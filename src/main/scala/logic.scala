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

import mccluskey.{ SofP, Util }

import Logic._

trait LocalRule {
  def transform(node: Logic): Logic
}
object LocalRule {

}

trait GlobalRule {
  // there is the possibility of work duplication between the "trigger" and
  // "perform" steps. If that becomes a performance issue, we can make use of
  // type members to allow the trigger to pass state over to the perform step.
  def trigger(channels: List[Logic], fan_out: Map[Logic, Int]): List[Logic]
  def perform(nodes: List[Logic]): Map[Logic, Logic]
}

// combinatorial logic, cycles are not permitted (caller's responsibility).
sealed trait Logic { self =>
  final def render(top: Boolean)(show: Int => String): String = self match {
    case In(a) => show(a)
    case Inv(e) => "~" + e.render(false)(show)
    case And(entries) => entries.map(_.render(false)(show)).mkString("·")
    case Or(entries) =>
      val parts = entries.map(_.render(false)(show))
      if (top) parts.mkString(" + ")
      else parts.mkString("(", " + ", ")")
  }
  final def render(show: Int => String): String = render(true)(show)
  final def render: String = render(true)(_.toString)

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
        val entries_ = entries.map { e: Logic =>
          val replaced = e.replace(target, replacement)
          (replaced eq e, replaced)
        }
        if (entries_.exists(_._1)) cons(entries_.map(_._2))
        else self
      }

      self match {
        case Inv(e) =>
          val replaced = e.replace(target, replacement)
          if (replaced eq e) self else Inv(replaced)

        case And(entries) =>
          replace_(entries)(es => And(es.toSet))

        case Or(entries) =>
          replace_(entries)(es => Or(es.toSet))

        case In(_) => self
      }
    }


}
object Logic {
  case class Inv private(entry: Logic) extends Logic
  case class And private(entries: Set[Logic]) extends Logic
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

    val _ = Util.alpha
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
