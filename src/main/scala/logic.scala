// Multi-level combinational logic synthesis. For something more practical, see
// https://github.com/berkeley-abc/abc/
// https://people.eecs.berkeley.edu/~alanmi/publications/
//
// This code takes inspiration from the research of "Multilevel Logic Synthesis"
// (Brayton90), "SOCRATES: A System for AutomatiCally Synthesizing and
// Optimizing Combinational Logic" (Gregory88) by applying metarules. However,
// those papers are devoid of actual implementable details, so what we do is
// maintain a list of manual rules that run on the AST of the circuit. Many of
// the techniques are also documented in "Switching Theory for Logic Synthesis"
// by Sasao99.
//
// We explore the space of possible moves using a form of simulated annealing
// with a fixed limit of scouts.
//
// Simple objective functions may be provided, such as reducing component count,
// component cost, power consumption or critical path time for various
// https://en.wikipedia.org/wiki/Logic_family
//
// The objective functions are incredibly simple and do not fully simulate the
// circuits so there may be all kinds of power dissipation issues, especially
// around fan-in and fan-out and do not consider interference (sometimes for the
// better) such as power-up times of multi-gate components.
//
// The output is a netlib in yosys (https://github.com/YosysHQ/) JSON format,
// which can be rendered by https://github.com/nturley/netlistsvg
package logic

import java.io.File
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

import scala.collection.immutable.BitSet

import fommil.util._
import mccluskey.McCluskey

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
    override def perform(node: Logic): List[Logic] = node match {
      case And(entries) =>
        val (nested, other) = entries.partitionMap {
          case And(es) => Left(es)
          case es => Right(es)
        }
        if (nested.isEmpty) Nil
        else List(And(nested.flatten ++ other))

      case Or(entries) =>
        val (nested, other) = entries.partitionMap {
          case Or(es) => Left(es)
          case es => Right(es)
        }
        if (nested.isEmpty) Nil
        else List(Or(nested.flatten ++ other))

      case _ => Nil
    }
  }

  // Eliminate by absorption
  //
  // A.(A + B) = A
  // A + (A.B) = A
  //
  // Although technically a LocalRule, it is always optimal to perform this on
  // the root nodes.
  object Eliminate extends LocalRule {
    // The core rule logic exposed for other rules to use directly when there is
    // an expected immediate opportunity for elimination.
    //
    // We have to recurse all the way to the branches since the common factors
    // cannot be obtained in the opposite direction. Note that we need to be
    // careful to track nested AND and ORs separately. For example, A.(B + ((A +
    // D).C)) (AND(OR(AND(...)))) only eliminates the D in the (A + D) term
    // to A.C, not A. To achieve this we keep a running record of what the
    // common sum and products are, so that they can eliminate independently of
    // each other.
    def eliminate(node: Logic): Logic = {
      // .get is safe because we can never get a None from the delegate when the
      // common factors are empty.
      val repl = eliminate_(node, Set.empty, Set.empty).get
      if (repl == node) node else repl // return same instance when possible
    }
    // Returns None if the node should be eliminated, otherwise a Some of a
    // (potentially) reduced tree.
    private def eliminate_(node: Logic, common_sums: Set[Logic], common_products: Set[Logic]): Option[Logic] = node match {
      case node: And =>
        def flatten_factors(outer: And): Set[Logic] = outer.entries.flatMap {
          case inner: And => flatten_factors(inner)
          case e => Set(e)
        }
        val flattened_factors = flatten_factors(node)

        if (flattened_factors.overlaps(common_sums)) None
        else {
          lazy val common_products_ = common_products ++ flatten_factors(node)
          val entries_ = node.entries.flatMap {
            case flip: Or => eliminate_(flip, common_sums - flip, common_products_)
            case e => Some(e)
          }
          if (entries_.isEmpty) None else Some(And(entries_))
        }

      case node: Or =>
        def flatten_factors(outer: Or): Set[Logic] = outer.entries.flatMap {
          case inner: Or => flatten_factors(inner)
          case e => Set(e)
        }
        val flattened_factors = flatten_factors(node)

        if (flattened_factors.overlaps(common_products)) None
        else {
          lazy val common_sums_ = common_sums ++ flattened_factors
          val entries_ = node.entries.flatMap {
            case flip: And => eliminate_(flip, common_sums_ - flip, common_products)
            case e => Some(e)
          }
          if (entries_.isEmpty) None else Some(Or(entries_))
        }

      case Inv(e) =>
        // flip and invert the factors
        eliminate_(e, common_products.map(Inv(_)), common_sums.map(Inv(_))).map(Inv(_))

      case _ => Some(node)
    }

    def perform(node: Logic): List[Logic] = {
      val node_ = eliminate(node)
      if (node_ eq node) Nil
      else List(node_)
    }
  }

  // factor common products by distribution:
  //
  //   (A + B)(A + C) = A + (B.C)
  //   (A.B) + (A.C) = A.(B + C)
  //
  // considers all possible factors for an expression.
  object Factor extends LocalRule {
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
              else Some(Eliminate.eliminate(And(entries + factor)))
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
              else Some(Eliminate.eliminate(Or(entries + factor)))
          }

      case _ => Nil
    }
  }

  // Apply deMorgan's rule
  //
  //   A'.B'.C = (A + B + C')'
  //   A' + B' + C = (A.B.C')'
  //
  // This rule always flips, so can lead to infinite cycles and is therefore
  // costly to search. Simple triggers such as counts of inverted contents don't
  // tend to reach the optimal circuits.
  object DeMorgan extends LocalRule {
    def perform(node: Logic): List[Logic] = node match {
      case And(nodes) =>
        val (norm, inv) = nodes.partitionMap {
          case Inv(e) => Right(e)
          case e => Left(e)
        }
        List(Inv(Or(norm.map(Inv(_)) ++ inv)))

      case Or(nodes) =>
        val (norm, inv) = nodes.partitionMap {
          case Inv(e) => Right(e)
          case e => Left(e)
        }
        List(Inv(And(norm.map(Inv(_)) ++ inv)))

      case _ => Nil
    }
  }

  // TODO it feels like there is further elimination possible here...
  // i1'·i2'·i0 + (i1' + i0 + i2)' + (i2' + i0 + i1)' + (i0' + i1' + i2')'

  // TODO hand-coded transduction rules (e.g. inverters replaced with NANDs)
  //      including the two standard test cases that seem to be used over and
  //      over in expand/reduce techniques like transduction.

  // TODO use simulated annealing to build a transduction database

}

trait GlobalRule {
  // there is the possibility of work duplication between the "trigger" and
  // "perform" steps. If that becomes a performance issue, we can make use of
  // type members to allow the trigger to pass state over to the perform step.
  def trigger(channels: List[Logic], fan_out: Map[Logic, Int]): List[Logic]
  def perform(nodes: List[Logic]): Map[Logic, Logic]
}
object GlobalRule {
  // TODO split AND / OR gates that have sub-sets that can be shared
}

trait Objective {
  def measure(fan_out: Map[Logic, Int]): Double
}
object Objective {
  // https://en.wikipedia.org/wiki/Diode_logic
  // https://en.wikipedia.org/wiki/Resistor-transistor_logic
  // https://en.wikipedia.org/wiki/Diode-transistor_logic
  //
  // Diode Logic only implements active-high AND / OR, RTL only implements INV /
  // NOR using npn transistors (and can build all other gates from there), and
  // DTL expands on both, using pnp in NOR gates.
  //
  // The relative weights of each component type are user provided.
  //
  // Negative voltage sinks and their associated resistors are not considered,
  // nor are capacitors, which may be used to speed up transistor switching.
  //
  // Old-school RTL NOR may be preferred for 2 or 3 input NOR, which uses a
  // voltage divider instead of diodes.
  case class DTL_Components(
    resistor: Double,
    npn: Double,
    diode: Double,
    rtl: Boolean
  ) extends Objective {
    // TODO add transistor+diode to boost weak fan-out signals.
    //
    // INV is implemented as a common emitter NPN transistor. Two and three
    // input NOR may be implemented as INV with a voltage divider.
    //
    override def measure(fan_out: Map[Logic, Int]): Double = fan_out.keys.map(calc).sum

    // TODO intermediate AST, reused for the schematic
    def calc(node: Logic): Double = node match {
      case True | In(_) => 0
      case Inv(or @ Or(es)) if rtl & es.size < 4 => (2 + es.size) * resistor + npn - calc(or)
      case Inv(_) => 2 * resistor + npn
      case Or(es) => resistor + es.size * diode
      case And(es) => resistor + es.size * diode
    }
  }

  //   - TODO TTL https://en.wikipedia.org/wiki/Transistor-transistor_logic
  //   - TODO CMOS https://en.wikipedia.org/wiki/CMOS
  //   - TODO Sky130 https://github.com/google/skywater-pdk

}

// combinatorial logic, cycles are not permitted (caller's responsibility).
sealed trait Logic { self =>
  private final def render(ands: Boolean, ors: Boolean): String = self match {
    case True => "1"
    case Inv(True) => "0"
    case In(i) => s"i$i"
    case Inv(e) => e.render(false, false) + "'"
    case And(entries) =>
      val parts = entries.map(_.render(true, false))
      if (ors) parts.mkString("·")
      else parts.mkString("(", "·", ")")
    case Or(entries) =>
      val parts = entries.map(_.render(false, true))
      if (ands) parts.mkString(" + ")
      else parts.mkString("(", " + ", ")")
  }
  final def render: String = render(true, true)
  override final def toString: String = render

  final def size: Int = self match {
    case True => 1
    case _: In => 1
    case Inv(e) => 1 + e.size
    case And(es) => 1 + es.map(_.size).sum
    case Or(es) => 1 + es.map(_.size).sum
  }

  final def eval(input: BitSet): Boolean = self match {
    case True => true
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
        case True => self

        case Inv(e) =>
          val replaced = e.replace(target, replacement)
          if (replaced ne e) Inv(replaced) else self

        case And(entries) =>
          replace_(entries)(es => And(es.toSet))

        case Or(entries) =>
          replace_(entries)(es => Or(es.toSet))

        case _: In => self
      }
    }

  // this gets called so much it's worth caching
  val nodes: List[Logic] = {
    def nodes_(es: Iterable[Logic]): List[Logic] = es.toList.flatMap(_.nodes)
    self match {
      case True => self :: Nil
      case Inv(a) => self :: a.nodes
      case And(entries) => self :: nodes_(entries)
      case Or(entries) => self :: nodes_(entries)
      case _: In => self :: Nil
    }
  }

}
object Logic {
  // constructor enforces involution: (A')' = A
  case class Inv private(entry: Logic) extends Logic {
    override val hashCode: Int = 17 * entry.hashCode
    override def equals(that: Any): Boolean = that match {
      case thon: Inv => hashCode == thon.hashCode && entry == thon.entry
      case _ => false
    }
  }

  // structure enforces indempotency A . A = A
  // constructor enforces identity A . 1 = A
  // constructor enforces complementation A . A' = 0
  case class And private(entries: Set[Logic]) extends Logic {
    override val hashCode: Int = entries.hashCode
    override def equals(that: Any): Boolean = that match {
      case thon: And => hashCode == thon.hashCode && entries.size == thon.entries.size && entries == thon.entries
      case _ => false
    }
  }

  // structure enforces indempotency A + A = A
  // constructor enforces identity A + 0 = A
  // constructor enforces complementation A + A' = 1
  case class Or  private(entries: Set[Logic]) extends Logic {
    override val hashCode: Int = entries.hashCode
    override def equals(that: Any): Boolean = that match {
      case thon: Or => hashCode == thon.hashCode && entries.size == thon.entries.size && entries == thon.entries
      case _ => false
    }
  }

  case class In  (channel: Int) extends Logic

  // a placemarker (along with Inv(True)) for nodes that can be collapsed
  case object True extends Logic

  object Inv {
    private val False = new Inv(True)
    def apply(e: Logic): Logic = e match {
      case True => False
      case Inv(ee) => ee
      case e => new Inv(e)
    }
  }

  object And {
    def apply(head: Logic, tail: Logic*): Logic =
      apply(tail.toSet + head)
    def apply(entries: Set[Logic]): Logic = {
      var entries_ = entries

      // this doesn't remove all dupes from nested AND gates, we could still
      // have AND(AND(a, b), AND(b, c)). The UnNest rule considers this, as we
      // want to preserve structure here.
      def rec(es: Set[Logic], top: Boolean): Unit = es.foreach { e =>
        if (entries_.contains(Inv(e)) || (top && e == Inv(True)))
          entries_ = Set(Inv(True))
        else if ((!top && entries_.contains(e)) || (top && e == True))
          entries_ = entries_ - e

        e match {
          case And(nested) => rec(nested, false)
          case _ => ()
        }
      }
      rec(entries_, true)

      if (entries_.isEmpty) True
      else if (entries_.size == 1) entries_.head
      else new And(entries_)
    }
  }

  object Or {
    def apply(head: Logic, tail: Logic*): Logic =
      apply(tail.toSet + head)
    def apply(entries: Set[Logic]): Logic = {
      var entries_ = entries

      def rec(es: Set[Logic], top: Boolean): Unit = es.foreach { e =>
        if (entries_.contains(Inv(e)))
          entries_ = Set(True)
        else if ((!top && entries_.contains(e)) || (top && e == Inv(True)))
          entries_ = entries_ - e

        e match {
          case Or(nested) => rec(nested, false)
          case _ => ()
        }
      }
      rec(entries_, true)

      if (entries_.isEmpty) True
      else if (entries_.size == 1) entries_.head
      else new Or(entries_)
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

    val minsums = {
      val (input_width, tables, user_in_names, user_out_names) = McCluskey.parse(input)
      McCluskey.solve(input_width, tables, user_in_names, user_out_names)
    }

    val local_rules = {
      import LocalRule._
      List(Factor, UnNest, Eliminate, DeMorgan)
    }
    val max_surface = 25
    val max_steps = 1000

    val obj: Objective = Objective.DTL_Components(
      resistor = 0,
      npn = 1,
      diode = 0.75,
      rtl = true
    )

    // would be nice to keep track of the rules that were applied
    var surface = minsums.asLogic.map { soln => soln -> obj.measure(fanout(soln)) }
    // TODO add variants with truth table inverted for outputs with more than half true

    surface.tail.foreach { needle =>
      assert(verify(minsums.input_width, surface.head._1, needle._1))
    }

    // TODO calculate the alternative msop using 2-bit input decoders which
    //      doubles the size of the inputs but typically reduces the size of the
    //      sop network (~25% according to the literature).

    System.out.println("baseline = " + surface.map(_._2).min)

    var step = 0
    var converged = false

    // note what has been done before (should probably cap this)
    var local_rejects = Set.empty[(Map[String, Logic], LocalRule, Logic)]

    while (step < max_steps && !converged) {
      val surface_ = surface
      // System.out.println(s"step $step surface ${surface.size}")

      surface.foreach { case (last_soln, _) =>
        val nodes = last_soln.values.toList.flatMap(_.nodes).distinct
        local_rules.foreach { rule =>
          nodes.foreach { node =>
            if (!local_rejects.contains((last_soln, rule, node))) {
              local_rejects += ((last_soln, rule, node))
              rule.perform(node).foreach { repl =>
                // System.out.println(s"replacing $node with $repl via $rule")
                val update = last_soln.map {
                  case (name, circuit) => name -> circuit.replace(node, repl)
                }
                assert(verify(minsums.input_width, surface.head._1, update))
                surface ::= (update -> obj.measure(fanout(update)))
              }
            }
          }
        }

        // TODO apply global rules
      }
      surface = surface.distinctBy(_._1).sortBy(_._2).take(max_surface)
      step += 1
      if (surface eq surface_) converged = true
    }

    System.out.println(surface.head)
  }

  def fanout(channels: Map[String, Logic]): Map[Logic, Int] =
    channels.values.toList.flatMap(_.nodes).counts

  def verify(input_width: Int, orig: Map[String, Logic], update: Map[String, Logic]): Boolean = {
    (0 until (1 << input_width)).foreach { i =>
      val in = BitSet.fromBitMask(Array(i))
      for {
        channel <- orig.keys
      } {
        if (orig(channel).eval(in) != update(channel).eval(in)) return false
      }
    }
    true
  }

}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain logic.Main tests/fulladder.truth\""
// End:
