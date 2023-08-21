// Multi-level combinational logic synthesis. For something more practical, see
// https://github.com/berkeley-abc/abc/
// https://people.eecs.berkeley.edu/~alanmi/publications/
//
// This code takes inspiration from the research of "Multilevel Logic Synthesis"
// (Brayton90), "SOCRATES: A System for AutomatiCally Synthesizing and
// Optimizing Combinational Logic" (Gregory88) by applying metarules. However,
// those papers are devoid of actual implementable details, so what we do is
// maintain a list of manual rules that run on the AST of the circuit.
//
// TODO Each rule is able to provide a weight of whether it thinks it would be
// able to help optimise the circuit or not (according to the objective
// function).
//
// TODO We explore the space of possible moves using a form of simulated
// annealing with a fixed limit of scouts. Rules may be combined in each step.
//
// Simple objective functions may be provided, such as reducing
//
// - TODO component count
// - TODO component cost
// - TODO power consumption
// - TODO critical path time
//
// For a limited set of logic families, such as
//
//   - TODO RTL https://en.wikipedia.org/wiki/Resistor-transistor_logic
//   - TODO DTL https://en.wikipedia.org/wiki/Diode-transistor_logic
//   - TODO TTL https://en.wikipedia.org/wiki/Transistor-transistor_logic
//   - TODO CMOS https://en.wikipedia.org/wiki/CMOS
//   - TODO Sky130 https://github.com/google/skywater-pdk
//
// See https://en.wikipedia.org/wiki/Logic_family for more.
//
// The objective functions are incredibly simple and do not fully simulate the
// circuits so there may be all kinds of power dissipation issues, especially
// around fan-in and fan-out and do not consider interference (sometimes for the
// better) such as power-up times of multi-gate components.
//
// TODO The output is a netlib using the JSON format described at
// https://github.com/nturley/netlistsvg which is really only appropriate for
// visualisation and manual inspection.
//
// TODO output formats that can be simulated with SPICE
// TODO output formats that can be used by other tools
package logic

import java.io.File
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

import scala.collection.immutable.BitSet

import fommil.util._
import mccluskey.SofP

import Logic._

trait LocalRule {
  // the List implies different choices that could be taken. Nil implies the
  // rule has no action.
  //
  // the rule should not apply itself recursively to the node's children (unless
  // it cannot be done from multiple indepentent calls) but may transform
  // multi-level structures.
  def perform(node: Logic): List[Logic]
}
object LocalRule {
  // unnest nodes of the same type
  //   A.(A.B.C) => A.B.C
  //   (A + B) + (A + C + D) = A + B + C + D
  object UnNest extends LocalRule {
    // TODO a variant that recurses

    override def perform(node: Logic): List[Logic] = node match {
      case And(entries) =>
        val (nested, other) = entries.partitionMap {
          case And(es) => Left(es)
          case es => Right(es)
        }
        List(And(nested.flatten ++ other))

      case Or(entries) =>
        val (nested, other) = entries.partitionMap {
          case Or(es) => Left(es)
          case es => Right(es)
        }
        List(Or(nested.flatten ++ other))

      case _ => Nil
    }
  }

  // Eliminate by absorption
  //
  // A.(A + B) = A
  // A + (A.B) = A
  //
  // with nesting...
  //
  // A.(A + B + (A + C)) = A
  // A + (A.B.(A.C)) = A
  object Eliminate extends LocalRule {
    // TODO fully recursive elimination for less frequent calling (note that it
    // cannot be constructed from multiple single calls because it needs the
    // great-grandparent common sets). Note that A.(B + ((A + D).C)) eliminates
    // to A.C, not A. We need to track AND / OR factors separately.

    // The core rule logic exposed for other rules to use directly when there is
    // an an expected immediate opportunity for elimination.
    def eliminate(node: Logic): Option[Logic] = node match {
      case And(entries) =>
        def rec(or: Or): Boolean = or.entries.exists {
          case nested: Or => rec(nested)
          case e => entries.contains(e)
        }
        val entries_ =  entries.filterNot {
          case nested: Or => rec(nested)
          case _ => false
        }
        if (entries_.size == entries.size) None else Some(And(entries_))

      case Or(entries) =>
        def rec(and: And): Boolean = and.entries.exists {
          case nested: And => rec(nested)
          case e => entries.contains(e)
        }
        val entries_ =  entries.filterNot {
          case nested: And => rec(nested)
          case _ => false
        }
        if (entries_.size == entries.size) None else Some(Or(entries_))

      case _ => None
    }

    def perform(node: Logic): List[Logic] = eliminate(node).toList
  }

  // factor common products by distribution:
  //
  //   (A + B)(A + C) = A + (B.C)
  //   (A.B) + (A.C) = A.(B + C)
  //
  // considers all possible factors for an expression.
  object Factor extends LocalRule {
    // TODO have a separate "Optimal Factors" that calculates all permutations
    // of a factorisation (including iterating over the common and uncommon
    // remainders) and returns the one factorisation with the minimal number of
    // terms. Although this can be reached by searching through the individual
    // factors, it is useful to have this as a single step choice which can
    // potentially be applied once, from the branches to the trunk, for a
    // comparison solution.

    def perform(node: Logic): List[Logic] = node match {
      case And(entries) =>
        def rec(or: Or): List[Logic] = or.entries.toList.flatMap {
          case nested: Or => rec(nested)
          case e => List(e)
        }
        entries.flatMap {
          case nested: Or => rec(nested)
          case _ => Nil
        }.counts
          .toList
          .flatMap {
            case (factor, c) =>
              if (c < 2) None
              else Eliminate.eliminate(And(entries + factor))
          }

      case Or(entries) =>
        def rec(and: And): List[Logic] = and.entries.toList.flatMap {
          case nested: And => rec(nested)
          case e => List(e)
        }
        entries.flatMap {
          case nested: And => rec(nested)
          case _ => Nil
        }.counts
          .toList
          .flatMap {
            case (factor, c) =>
              if (c < 2) None
              else Eliminate.eliminate(Or(entries + factor))
          }

      case _ => Nil
    }
  }

  // TODO deMorgan, minimise Inv in AND/OR nodes
  //      A'.B'.C = (A + B + C')' (outer Inv counts less than an inner one)
  //      A' + B' + C = (A.B.C')'

  // TODO detect and remove dontcares

  // TODO XOR / NAND expansions
}

trait GlobalRule {
  // there is the possibility of work duplication between the "trigger" and
  // "perform" steps. If that becomes a performance issue, we can make use of
  // type members to allow the trigger to pass state over to the perform step.
  def trigger(channels: List[Logic], fan_out: Map[Logic, Int]): List[Logic]
  def perform(nodes: List[Logic]): Map[Logic, Logic]
}
object GlobalRule {
  // TODO split AND / OR gates that have sub-sets that could be shared
  //      (note that this must be performed after local rules or it can be undone)
}

// combinatorial logic, cycles are not permitted (caller's responsibility).
sealed trait Logic { self =>
  final def render(top: Boolean)(show: Int => String): String = self match {
    case In(a) => show(a)
    case Inv(e) => e.render(false)(show) + "'"
    case And(entries) => entries.map(_.render(false)(show)).mkString("·")
    case Or(entries) =>
      val parts = entries.map(_.render(false)(show))
      if (top) parts.mkString(" + ")
      else parts.mkString("(", " + ", ")")
  }
  final def render(show: Int => String): String = render(true)(show)
  final def render: String = render(true)(_.toString)

  final def size: Int = self match {
    case In(_) => 1
    case Inv(e) => 1 + e.size
    case And(es) => 1 + es.map(_.size).sum
    case Or(es) => 1 + es.map(_.size).sum
  }

  // override final def toString: String = render(false)(_.toString)

  final def eval(input: BitSet): Boolean = self match {
    case In(a) => input(a)
    case Inv(e) => !e.eval(input)
    case And(as) => as.forall(_.eval(input))
    case Or(os) => os.exists(_.eval(input))
  }

  // Replace every node that is equal to the target, recursing into children.
  //
  // Does not recurse into the replacement Node
  final def replace(target: Logic, replacement: Logic): Logic =
    if (self == target) replacement
    else {
      def replace_(entries: Iterable[Logic])(cons: Iterable[Logic] => Logic): Logic = {
        val entries_ = entries.map { e =>
          val replaced = e.replace(target, replacement)
          (replaced ne e, replaced)
        }
        if (entries_.exists(_._1)) cons(entries_.map(_._2))
        else self
      }

      self match {
        case Inv(e) =>
          val replaced = e.replace(target, replacement)
          if (replaced ne e) Inv(replaced) else self

        case And(entries) =>
          replace_(entries)(es => And(es.toSet))

        case Or(entries) =>
          replace_(entries)(es => Or(es.toSet))

        case In(_) => self
      }
    }

  def nodes: List[Logic] = {
    def nodes_(es: Iterable[Logic]): List[Logic] = es.toList.flatMap(_.nodes)
    self match {
      case Inv(a) => self :: a.nodes
      case And(entries) => self :: nodes_(entries)
      case Or(entries) => self :: nodes_(entries)
      case In(_) => self :: Nil
    }
  }

}
object Logic {
  // TODO caching hashCode may be beneficial to all the Set usage

  // constructor enforces involution: (A')' = A
  case class Inv private(entry: Logic) extends Logic

  // structure enforces indempotency A . A = A
  // constructor enforces identity A . 1 = A
  case class And private(entries: Set[Logic]) extends Logic

  // structure enforces indempotency A + A = A
  // constructor enforces identity A + 0 = A
  case class Or  private(entries: Set[Logic]) extends Logic

  case class In  (channel: Int) extends Logic

  object Inv {
    def apply(e: Logic): Logic = e match {
      case Inv(ee) => ee
      case e => new Inv(e)
    }
  }

  object And {
    def apply(entries: Set[Logic]): Logic = {
      require(entries.nonEmpty)
      if (entries.size == 1) entries.head
      else new And(entries)
    }
  }

  object Or {
    def apply(entries: Set[Logic]): Logic = {
      require(entries.nonEmpty)
      if (entries.size == 1) entries.head
      else new Or(entries)
    }
  }

  object In {

  }
}

object Main {

  def main(args: Array[String]): Unit = {
    require(args.length >= 1, "an input file must be provided")
    val in = new File(args(0))
    require(in.isFile(), s"$in must exist")
    val input = Files.readString(in.toPath, UTF_8)

    val design = jzon.Decoder[SofP.Storage].decodeJson(input) match {
      case Left(err) => throw new IllegalArgumentException(err)
      case Right(as) => as
    }

    val _ = alpha_syms
      .take(design.input_width)
      .map(_.toLowerCase)
      .zipWithIndex
      .map(_.swap)
      .toMap

    ???
  }
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain logic.Main tests/fulladder.minsums.json\""
// End:
