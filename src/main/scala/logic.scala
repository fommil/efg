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

import fommil.cache._
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

  // This is too inefficient, so has been disabled, but the code remains for
  // reference. We hand-code for the known situations that it would have
  // detected such as maximising AND/OR or splitting something off that can be
  // represented as XOR/OH (c.f. Split). But obviously that doesn't catch
  // everything.
  object Nest extends LocalRule {
    private def subsets(entries: Set[Logic]): List[(Set[Logic], Set[Logic])] =
      (2 to (entries.size + 1) / 2).toList.flatMap { i =>
        entries.subsets(i).map { left => (left, entries.diff(left)) }
      }

    // using hand-crafted constructors to avoid optimisations that remove redundancy
    override def perform(node: Logic): List[Logic] = node match {
      case And(entries) if entries.size > 1 =>
        subsets(entries).map { case (left, right) => new And(left + new And(right)) }

      case Or(entries) if entries.size > 1 =>
        subsets(entries).map { case (left, right) => new Or(left + new Or(right))}

      case _ => Nil
    }
  }

  // a subset of Nest whereby we detect and split out subsets of nodes that can
  // be represented by dedicated logic gates.
  object Split extends LocalRule {
    // FIXME implement by iterating through all subsets and checking the is* methods
    override def perform(node: Logic): List[Logic] = ???
    // Set(node.asXOR, node.asXNOR, node.asOH, node.asNOH).flatten.toList
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
    def perform(node: Logic): List[Logic] = {
      val node_ = perform_(node)
      if (node_ == node) Nil else List(node_)
    }
    def perform_(node: Logic): Logic = node match {
      case And(nodes) =>
        val (norm, inv) = nodes.partitionMap {
          case Inv(e) => Right(e)
          case e => Left(Inv(e))
        }
        Inv(Or(norm ++ inv))

      case Or(nodes) =>
        val (norm, inv) = nodes.partitionMap {
          case Inv(e) => Right(e)
          case e => Left(Inv(e))
        }
        Inv(And(norm ++ inv))

      case _ => node
    }
  }

  class Cached(underlying: LocalRule, limit: Int) extends LocalRule {
    private[this] val cache = new LRA[Logic, List[Logic]](limit)
    final def perform(node: Logic): List[Logic] = {
      val cached = cache.synchronized { cache.get(node) }
      if (cached != null) cached
      else {
        val res = underlying.perform(node)
        cache.synchronized { cache.put(node, res) }
        res
      }
    }
  }

  // TODO hand-coded transduction rules (e.g. inverters replaced with NANDs)
  //      including the two standard test cases that seem to be used over and
  //      over in expand/reduce techniques like transduction.

  // TODO use simulated annealing to build a transduction database. A way to
  // find nodes that can be replaced would be to look 2+ levels deep and if the
  // number of inputs is smaller than the depth then construct the truth table
  // and perform a straight swap for the more efficient implementation. That might
  // be cheaper and more straightforward than finding dterms.

}

trait GlobalRule {
  // like LocalRule, implementations are encouraged to return each possible as
  // an entry in a list instead of being aggressive.
  def perform(circuits: Map[String, Logic]): List[Map[String, Logic]]
}

object GlobalRule {
  // finds all AND/OR gates that have subsets that could be utilised by other
  // overlapping parts of the circuit, and splits them out as nested entries.
  // Each "step" only performs one replacement action on the entire circuit even
  // if two steps are needed for sharing to occur (e.g. consider two overlapping
  // OR gates where both need to be unnested).
  object Shared extends GlobalRule {
    override def perform(circuits: Map[String, Logic]): List[Map[String, Logic]] = {
      ???
      // FIXME implement GlobalRule.Shared and wire it up
    }
  }
}

trait Objective {
  def measure(circuit: Map[String, Logic]): Double
}
object Objective {
  // The relative weights of each component type are user provided.
  //
  // Negative voltage sinks and their associated resistors are not considered,
  // nor are capacitors, which may be used to speed up transistor switching.
  case class DTL_Components(
    resistor: Double,
    npn: Double,
    pnp: Double,
    diode: Double
  ) extends Objective {
    import Hardware.DTL
    import Hardware.DTL._

    override def measure(circuit: Map[String, Logic]): Double =
      measureFanout(DTL.fanout(circuit.values.toSet.map(DTL.materialise(_))))

    // BUF should really be counted a bit more...
    def measureFanout(fanout: Map[DTL, Int]): Double =
      fanout.keySet.toList.map(calc(_)).sum

    private def calc(node: DTL): Double = node match {
      case REF(_)  => 0
      case AND(es) => resistor + es.size * diode
      case  OR(es) => resistor + es.size * diode
      case NOT(_)  => 2 * resistor + npn
      case BUF(_, _)  => ???
      case NOR(es) => (2 + es.size) * resistor + npn
      case NOH(es) => 2 * resistor + npn + es.size * diode
      case  OH(es) => 2 * resistor + pnp + es.size * diode
      case XOR(es) => (es.size - 1) * (3 * resistor + 2 * npn)
      case XNOR(es) => (es.size - 1) * (3 * resistor + 2 * pnp)
    }
  }

  //   - TODO CMOS https://en.wikipedia.org/wiki/CMOS
  //   - TODO Sky130 https://github.com/google/skywater-pdk

}

object Hardware {
  // https://en.wikipedia.org/wiki/Diode_logic
  // https://en.wikipedia.org/wiki/Resistor-transistor_logic
  // https://en.wikipedia.org/wiki/Diode-transistor_logic
  //
  // Diode Logic only implements active-high AND / OR, RTL only implements INV /
  // NOR using npn transistors (and can build all other gates from there), and
  // DTL expands on both, using pnp in NOR gates.
  //
  // We also consider One Hot (i.e. intuitive multi-bit exclusive OR) based on
  // the efficient Not One Hot (NOH) implementation using a rectifier network
  // with the transistor emitter feedback.
  //
  // Old-school RTL NOR is preferred for 2 or 3 input NOR, which uses a voltage
  // divider instead of diodes.
  sealed trait DTL
  object DTL {
    case class REF(channel: Int)      extends DTL
    case class AND(entries: Set[DTL]) extends DTL
    case class OR (entries: Set[DTL]) extends DTL
    case class NOT(entry: DTL)        extends DTL

    // amplifier(s) to address fan-out constraints. Number required depends on
    // the fanout of the node.
    //
    // TODO an extra pass after materialise to add BUF for large fan-out
    case class BUF(entry: DTL, id: Int) extends DTL

    // voltage divider (has fan-in constraints)
    // TODO calculate the fan-in constraint in Falstad and breadboard
    case class NOR(entries: Set[DTL]) extends DTL

    // rectifier and NPN "Not One Hot". Equivalent to XNOR for 2 inputs but not any other arity.
    //
    // https://www.edn.com/perform-the-xor-xnor-function-with-a-diode-bridge-and-a-transistor/
    // https://www.electricaltechnology.org/2018/12/exclusive-or-xor-gate.html#xor-gate-using-bjt-and-diodes
    // TODO calculate the fan-in constraint in Falstad and breadboard
    case class NOH(entries: Set[DTL]) extends DTL
    // "One Hot" uses PNP, equivalent to XOR for 2 inputs.
    case class OH (entries: Set[DTL]) extends DTL

    // There are situations where it is preferable to use a transistor XOR
    // encoding when diodes are expensive or take up too much space.
    // https://hackaday.io/project/8449-hackaday-ttlers/log/150147-bipolar-xor-gate-with-only-2-transistors
    // XOR / XNOR are probably best called PARITY when extended to higher arity.
    //
    // TODO find an efficent way to implement multi-input XOR/XNOR otherwise,
    // this should be viewed as nested XOR2 / XNOR2 at the hardware.
    case class XOR(a: Set[DTL])     extends DTL // ⊕
    case class XNOR(a: Set[DTL])    extends DTL // ⊙

    // TODO eval to verify that the desired Logic is retained

    def materialise(logic: Logic): DTL = logic match {
      case True => impossible
      case In(i) => REF(i)

      case Inv(e) => materialise(e) match {
        case OR(es) if es.size < 4 => NOR(es)
        case XOR(es) => XNOR(es)
        case XNOR(es) => XOR(es)
        case OH(es) => NOH(es)
        case NOH(es) => OH(es)
        case other => NOT(other)
      }

      case And(es) => es.toList match {
        // TODO n-arity one-hot
        // x ⊕ y = (x + y) · (x' + y')
        // x ⊙ y = (x + y') · (x' + y)
        case List(Or(as), Or(bs)) if as.size == 2 && bs == as.map(Inv(_)) =>
          XOR(materialise(as.head), materialise(as.tail.head))

        // TODO does this extend to n-arity nested XOR?
        // x ⊕ y = (x + y) · (x · y)'
        case List(Or(as), Inv(And(bs))) if as.size == 2 && as == bs =>
          XOR(materialise(as.head), materialise(as.tail.head))
        // TODO rewrite to not need a second re-ordered check
        case List(Inv(And(bs)), Or(as)) if as.size == 2 && as == bs =>
          XOR(materialise(as.head), materialise(as.tail.head))

        case _ =>
          AND(es.map(materialise(_)))
      }

      // might be more efficient to not convert into a List
      case Or(es) => es.toList match {
        // x ⊕ y = (x · y') + (x' · y)
        // x ⊙ y = (x · y) + (x' · y')
        case List(And(as), And(bs)) if as.size == 2 && bs == as.map(Inv(_)) =>
          XNOR(materialise(as.head), materialise(as.tail.head))

        case _ =>
          //  OH(a, b, c) = (a · b' · c') + (a' · b · c') + (a' · b' · c)
          // NOH(a, b, c) = (a' · b · c)  + (a · b' · c)  + (a · b · c')
          // XOR(a, b, c) = OH(a, b, c) + (a · b · c) (parity)
          // XNOR(a, b, c) = NOH(a, b, c) + (a' · b' · c') (negative parity)
          // finding them without context is equivalent, so prefer NOH
          val (others, ands) = es.partitionMap {
            case and: And => Right(and)
            case e => Left(e)
          }

          // this checks if everything is actually made out of the same stuff
          lazy val abcs = ands.map { e =>
            // we can leave this as a Set because we know that And will never
            // contain an element and its inverse.
            e.entries.map {
              case Inv(a) => a
              case a => a
            }
          }
          lazy val abc = abcs.head
          lazy val abc_ = abc.map(Inv(_))

          // there is probably a more efficient way to do this, but it's easy to
          // debug code that produces exactly what we are looking for, and makes
          // it easier to find subsets and their diff.
          def expect_notonehot = abc.map { not => (abc - not) + Inv(not) }
          def expect_onehot = abc_.map { hot => (abc_ - hot) + Inv(hot) }
          lazy val expect_xor = (1 to abc_.size by 2).toSet.flatMap { i: Int =>
            abc_.subsets(i).map { subs =>
              And(subs.map(Inv(_)) ++ (abc_.diff(subs)))
            }.toSet
          }
          def expect_xnor = expect_xor.map(Inv(_))

          val isSpecial = others.isEmpty && abcs.size == 1
          if (isSpecial && ands == expect_notonehot)
            NOH(abc.map(materialise(_)))
          else if (isSpecial && ands == expect_onehot)
            OH(abc.map(materialise(_)))
          else if (isSpecial && ands == expect_xor)
            XOR(abc.map(materialise(_)))
          else if (isSpecial && ands == expect_xnor)
            XNOR(abc.map(materialise(_)))
          else
            OR(es.map(materialise(_)))
      }
    }

    def fanout(circuits: Set[DTL]): Map[DTL, Int] = {
      def fanout_seq(acc: Map[DTL, Int], els: Set[DTL]) =
        els.foldLeft(acc) { case (acc_, e) => fanout_(acc_, e)}

      def fanout_(acc: Map[DTL, Int], c: DTL): Map[DTL, Int] = {
        val acc_ = acc.incr(c)
        if (acc.contains(c)) acc_
        else c match {
          case REF(_)  => acc_
          case AND(es) => fanout_seq(acc_, es)
          case  OR(es) => fanout_seq(acc_, es)
          case NOT(e)  => fanout_seq(acc_, Set(e))
          case BUF(e, _) => fanout_seq(acc_, Set(e))
          case NOR(es) => fanout_seq(acc_, es)
          case NOH(es) => fanout_seq(acc_, es)
          case  OH(es) => fanout_seq(acc_, es)
          case XOR(es) => fanout_seq(acc_, es)
          case XNOR(es) => fanout_seq(acc_, es)
        }
      }

      circuits.foldLeft(Map.empty[DTL, Int]) {
        case (acc, c) => fanout_(acc, c)
      }
    }

    object AND {
      def apply(el: DTL, els: DTL*): AND = AND(els.toSet + el)
    }
    object OR {
      def apply(el: DTL, els: DTL*): OR = OR(els.toSet + el)
    }
    object NOR {
      def apply(el: DTL, els: DTL*): NOR = NOR(els.toSet + el)
    }
    object NOH {
      def apply(el: DTL, els: DTL*): NOH = NOH(els.toSet + el)
    }
    object OH {
      def apply(el: DTL, els: DTL*): OH = OH(els.toSet + el)
    }
    object XOR {
      def apply(el: DTL, els: DTL*): XOR = XOR(els.toSet + el)
    }
    object XNOR {
      def apply(el: DTL, els: DTL*): XNOR = XNOR(els.toSet + el)
    }
  }

}

// combinatorial logic, cycles are not permitted (caller's responsibility).
sealed trait Logic { self =>
  private final def render(ands: Boolean, ors: Boolean): String = self match {
    case True => "1"
    case Inv(True) => "0"
    case In(i) => s"i$i"
    case Inv(e) => e.render(false, false) + "'"
    case And(entries) =>
      val nested = entries.exists(_.isInstanceOf[And])
      val parts = entries.map(_.render(false, !nested))
      if (ors) parts.mkString("·")
      else parts.mkString("(", "·", ")")
    case Or(entries) =>
      val nested = entries.exists(_.isInstanceOf[Or])
      val parts = entries.map(_.render(!nested, false))
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

  def nodes: List[Logic] = {
    def nodes_(es: Iterable[Logic]): List[Logic] = es.toList.flatMap(_.nodes)
    self match {
      case True => self :: Nil
      case Inv(a) => self :: a.nodes
      case And(entries) => self :: nodes_(entries)
      case Or(entries) => self :: nodes_(entries)
      case _: In => self :: Nil
    }
  }

  // the following as* methods return the parameters of the indicated gate if
  // this node can be represented by that gate. This is important for both rule
  // application and hardware dependent materialisation stages. A logic node may
  // be represented by multiple gates, e.g. XOR is the same as OH for 2 inputs.
  def asXOR: Set[Logic] = this match {
    case True => Set.empty
    case In(_) => Set.empty
    case Inv(e) => e.asXNOR
    case And(es) => if (es.size != 2) Set.empty else {
      // x ⊕ y = (x + y) · (x' + y')
      // TODO extend to n-arity
      //
      // by applying DeMorgans to And, it allows us to consider the form
      //
      // x ⊕ y = (x + y) · (x · y)'
      //
      // This is not strictly necessary since we should arrive there by
      // application of the local rules but it's easy to do so why not.
      val es_ = es.map {
        case a@ And(_) => LocalRule.DeMorgan.perform_(a)
        case e => e
      }
      val abc = level2(es_)
      if (abc.size != 2) Set.empty
      else {
        val x = abc.head
        val y = abc.tail.head
        if (es == Set(Or(x, y), Or(Inv(x), Inv(y)))) abc
        else Set.empty
      }
    }

    case Or(es) =>
      // x ⊕ y = (x' · y) + (x · y')
      // extending to n-arity matches all odd parities

      // FIXME implement

      ???
  }

  // x ⊙ y = (x + y') · (x' + y)
  def asXNOR: Set[Logic] = ???
  def asOH: Set[Logic] = ???
  def asNOH: Set[Logic] = ???

  // returns all elements at the next level with inversions removed
  private def level2(els: Set[Logic]): Set[Logic] = {
    def norm(e: Logic): Logic = e match {
      case Inv(e) => e
      case e => e
    }

    els.flatMap {
      case Or(es) => es.map(norm(_))
      case And(es) => es.map(norm(_))
      case Inv(And(es)) => es.map(norm(_))
      case Inv(Or(es)) => es.map(norm(_))
      case _ => Nil
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
  case class And private[logic](entries: Set[Logic]) extends Logic {
    override val hashCode: Int = entries.hashCode
    override def equals(that: Any): Boolean = that match {
      case thon: And => hashCode == thon.hashCode && entries.size == thon.entries.size && entries == thon.entries
      case _ => false
    }
  }

  // structure enforces indempotency A + A = A
  // constructor enforces identity A + 0 = A
  // constructor enforces complementation A + A' = 1
  case class Or  private[logic](entries: Set[Logic]) extends Logic {
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

  // TODO is auto-deduping nested things stopping us from finding optimal solutions?
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
      List(Factor, UnNest, Eliminate, DeMorgan, Split).map(new Cached(_, 1024 * 1024))
    }
    val max_steps = 1000

    val obj = Objective.DTL_Components(
      resistor = 0,
      npn = 1,
      pnp = 1,
      diode = 0.75
    )

    // Tracks which circuits have been fully explored to avoid repeating work.
    // We might want to limit since it is a designed-in leak.
    var all_my_circuits = minsums.asLogic.map { soln => soln -> obj.measure(soln) }.toMap
    // TODO add variants with truth table inverted for outputs with more than half true

    val ground_truth = all_my_circuits.head._1
    all_my_circuits.tail.foreach {
      case (needle, _) => assert(verify(minsums.input_width, ground_truth, needle))
    }

    // TODO calculate the alternative msop using 2-bit input decoders which
    //      doubles the size of the inputs but typically reduces the size of the
    //      sop network (~25% according to the literature).

    System.out.println("baseline = " + all_my_circuits.minBy(_._2))

    var step = 0

    // TODO parallelise

    // we repeat the same work for each output channel a lot of times so rule
    // application benefits from caching.
    //
    // it's unfortunate that only 1 step is allowed at a time, which may exclude
    // multi-step changes that only produce an improvement in the objective
    // function when all are applied, but individually increase costs.

    var surface = all_my_circuits.keySet
    while (step < max_steps && surface.nonEmpty) {
      val surface_ = surface
      surface = Set.empty
      surface_.foreach { last_soln =>
        val nodes = last_soln.values.toList.flatMap(_.nodes).distinct
        local_rules.foreach { rule =>
          nodes.foreach { node =>
            rule.perform(node).foreach { repl =>
              // System.out.println(s"replacing $node with $repl via $rule")
              val update = last_soln.map {
                case (name, circuit) => name -> circuit.replace(node, repl)
              }
              if (!all_my_circuits.contains(update) && !surface.contains(update)) {
                assert(verify(minsums.input_width, ground_truth, update))
                surface += update
                all_my_circuits += (update -> obj.measure(update))
              }
            }
          }
        }
      }
      step += 1
    }

    val soln = all_my_circuits.minBy(_._2)
    val impl = soln._1.map { case (n, c) => n -> Hardware.DTL.materialise(c) }
    val shared = Hardware.DTL.fanout(impl.values.toSet).filter {
      case (Hardware.DTL.REF(_), _) => false
      case (_, out) => out > 1
    }

    System.out.println(s"optimised = $soln")
    System.out.println(s"SHARED = $shared ")

    // TODO output the DTL circuit in yosys format
    System.out.println(s"IMPL = $impl")

    // FIXME fix the solver until it can be as efficient as the textbook soln

    val textbook = {
      import Hardware.DTL._

      val A = REF(0)
      val B = REF(1)
      val Cin = REF(2)
      val tmp = XOR(A, B)
      val Co = OR(AND(tmp, Cin), AND(A, B))
      val S = XOR(tmp, Cin)

      Map("S" -> S, "Co" -> Co)
    }
    System.out.println(textbook)
    val fanout_textbook = Hardware.DTL.fanout(textbook.values.toSet)
    System.out.println(s"text cost = ${obj.measureFanout(fanout_textbook)}")

  }

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
