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

import scala.annotation.unused
import scala.collection.immutable.BitSet

import fommil.cache._
import fommil.util._
import jzon.syntax._
import mccluskey.McCluskey
import yosys.Netlist

import Logic._

trait LocalRule {
  // the List implies different choices that could be taken. Nil implies the
  // rule has no action.
  //
  // the rule should not apply itself recursively to the node's children (unless
  // it cannot be done from multiple indepentent calls) but may transform
  // multi-level structures.
  def perform(node: Logic): List[Logic]

  def name: String
}
object LocalRule {
  // unnest nodes of the same type
  //   A.(A.B.C) => A.B.C
  //   (A + B) + (A + C + D) = A + B + C + D
  object UnNest extends LocalRule {
    override def name: String = "unnest"

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

      case Xor(entries) =>
        val (nested, other) = entries.partitionMap {
          case Xor(es) => Left(es)
          case es => Right(es)
        }
        if (nested.isEmpty) Nil
        else List(Xor(nested.flatten ++ other))

      case OneHot(entries) =>
        val (nested, other) = entries.partitionMap {
          case OneHot(es) => Left(es)
          case es => Right(es)
        }
        if (nested.isEmpty) Nil
        else List(OneHot(nested.flatten ++ other))

      case _ => Nil
    }
  }

  // This is too inefficient, so has been disabled, but the code remains for
  // reference. We hand-code for the known situations that it would have
  // detected such as maximising AND/OR or splitting something off that can be
  // represented as XOR/OH (c.f. Split). But obviously that doesn't catch
  // everything.
  object Nest extends LocalRule {
    override def name: String = "nest"

    def subsets(entries: Set[Logic]): List[(Set[Logic], Set[Logic])] =
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
  // be represented by dedicated logic gates. Note that this won't split a
  // multi-arity gate into smaller parts, as that is handled by Global.Shared
  //
  // This won't discover subsets if they require a common factor, e.g.
  //
  // a.b + a.c + b.c = a.b + c.(a'.b + a.b')
  //
  // where the XOR(a, b) is only visible if the common factor c is extracted.
  object Split extends LocalRule {
    override def name: String = "split"

    override def perform(node: Logic): List[Logic] = node match {
      case Or(es) =>
        (2 to es.size).toList.flatMap { i =>
          es.subsets(i).flatMap { sub =>
            val n = new Or(sub)
            Set(
              Xor.from(n),
              Xnor.from(n),
              OneHot.from(n),
              NotOneHot.from(n)
            ).flatten.map { gate =>
              Or(es.diff(sub) + gate)
            }
          }
        }

      case _ => Nil
    }
  }

  // TODO NAND (including flipping of inputs)
  // TODO NOR
  // TODO cycle the inversion of inputs (e.g. XOR, XNOR)

  // Eliminate by absorption
  //
  // A.(A + B) = A
  // A + (A.B) = A
  //
  // A nested AND inside an AND will not have any of its contents eliminated
  // (similar for nested OR inside OR), although their contents will be
  // considered common terms for the branches.
  //
  // Although this traverses the branches all the way to the leaves, it only
  // removes branches that are redundant with respect to the current node's
  // factors.
  object Eliminate extends LocalRule {
    override def name: String = "eliminate"

    // The core rule logic exposed for other rules to use directly when there is
    // an expected immediate opportunity for elimination.
    def eliminate(node: Logic): Logic = node match {
      case And(entries) => // A.(A + B) = A
        def flatten_factors(es: Set[Logic]): Set[Logic] = es.flatMap {
          case And(es_) => flatten_factors(es_)
          case e => Set(e)
        }
        val factors = flatten_factors(entries)
        val entries_ = entries.map {
          case e@ Or(es) =>
            val redundant = (factors - e).map { k => k -> True }.toMap
            val es_ = es.map { e => e.replace(redundant) }
            if (es_ == es) e else Or(es_)
          case e => e
        }
        if (entries_ == entries) node
        else And(entries_)

      case Or(entries) => // A + (A.B) = A
        def flatten_factors(es: Set[Logic]): Set[Logic] = es.flatMap {
          case Or(es_) => flatten_factors(es_)
          case e => Set(e)
        }
        val factors = flatten_factors(entries)
        val entries_ = entries.map {
          case e@ And(es) =>
            val redundant = (factors - e).map { k => k -> Inv(True) }.toMap
            val es_ = es.map { e => e.replace(redundant) }
            if (es_ == es) e else And(es_)
          case e => e
        }
        if (entries_ == entries) node
        else Or(entries_)

      case _ => node
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
  // considers all possible factors for an expression including factors that
  // only factor part of the expression, e.g.
  //
  // a.b + b.c + a.c = a.(b + c) + b.c
  //                 = b.(a + c) + a.c
  //                 = c.(a + b) + a.b
  //
  // Does not recurse into nested gates to find candidates.
  object Factor extends LocalRule {
    override def name: String = "factor"

    private def scope(@unused max: Int) = 2 // math.max(2, max - 1)

    def perform(node: Logic): List[Logic] = node match {
      case And(entries) =>
        val incommon = scope(entries.size)
        val candidates = entries.toList.flatMap {
          case Or(terms) => terms.toList
          case e => List(e)
        }.counts.filter(_._2 >= incommon).keySet
        candidates.map { factor =>
          val (uncommon, common) =  entries.partitionMap {
            case and@ Or(terms) =>
              if (terms.contains(factor)) Right(Or(terms - factor))
              else Left(and)

            case other =>
              if (factor == other) Right(Inv(True))
              else Left(other)
          }
          And(uncommon + Or(factor, And(common)))
        }.toList

      case Or(entries) =>
        val incommon = scope(entries.size)
        val candidates = entries.toList.flatMap {
          case And(terms) => terms.toList
          case e => List(e)
        }.counts.filter(_._2 >= incommon).keySet
        candidates.map { factor =>
          val (uncommon, common) =  entries.partitionMap {
            case and@ And(terms) =>
              if (terms.contains(factor)) Right(And(terms - factor))
              else Left(and)

            case other =>
              if (factor == other) Right(True)
              else Left(other)
          }
          Or(uncommon + And(factor, Or(common)))
        }.toList

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
    override def name: String = "demorgan"

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

  // when a gate has a complement, this is where we swap between them. could
  // arguably be included in DeMorgan but it's not technically the same thing.
  object Complement extends LocalRule {
    override def name: String = "complement"

    def perform(node: Logic): List[Logic] = {
      val node_ = perform_(node)
      if (node_ == node) Nil else List(node_)
    }

    def perform_(node: Logic): Logic = node match {
      case Xor(es) => Inv(Xnor(es))
      case Xnor(es) => Inv(Xor(es))
      case OneHot(es) => Inv(NotOneHot(es))
      case NotOneHot(es) => Inv(OneHot(es))
      case _ => node
    }
  }

  class Cached(underlying: LocalRule, limit: Int) extends LocalRule {
    override def name: String = underlying.name

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

}

trait GlobalRule {
  // like LocalRule, implementations are encouraged to return each possible move
  // as an entry in a list instead of being aggressive and applying everything.
  def perform(circuits: Set[Logic]): List[Map[Logic, Logic]]

  def name: String
}

object GlobalRule {
  // finds multi-input gates that have subsets that could be utilised by other
  // overlapping parts of the circuit, and splits them out as nested entries.
  object SharedAnd extends GlobalRule {
    override def name: String = "shared_and"

    override def perform(circuits: Set[Logic]): List[Map[Logic, Logic]] =
      ands(circuits).map { case (a, b) => Map(a -> b) }

    private def ands(circuits: Set[Logic]): List[(Logic, Logic)] = {
      val ands = circuits.flatMap { circuit =>
        circuit.nodes.collect { case e: And => e }
      }
      for {
        left <- ands
        left_ = left.entries
        right <- ands
        right_ = right.entries
        if left != right
        subset = left_.intersect(right_)
        if subset.size > 1 && left_.size > subset.size
      } yield {
        (left, new And(left_.diff(subset) + new And(subset)))
      }
    }.toList
  }

  object SharedOr extends GlobalRule {
    override def name: String = "shared_or"

    override def perform(circuits: Set[Logic]): List[Map[Logic, Logic]] =
      ors(circuits).map { case (a, b) => Map(a -> b) }

    private def ors(circuits: Set[Logic]): List[(Logic, Logic)] = {
      val ors = circuits.flatMap { circuit =>
        circuit.nodes.collect { case e: Or => e }
      }
      for {
        left <- ors
        left_ = left.entries
        right <- ors
        right_ = right.entries
        if left != right
        subset = left_.intersect(right_)
        if subset.size > 1 && left_.size > subset.size
      } yield {
        (left, new Or(left_.diff(subset) + new Or(subset)))
      }
    }.toList
  }

  object SharedXor extends GlobalRule {
    override def name: String = "shared_xor"

    override def perform(circuits: Set[Logic]): List[Map[Logic, Logic]] =
      xors(circuits).map { case (a, b) => Map(a -> b) }

    // these are not caught by the 'ors' rule because of the complex interaction
    // between the components.
    private def xors(circuits: Set[Logic]): List[(Logic, Logic)] = {
      val xors = circuits.flatMap { circuit =>
        circuit.nodes.collect { case e: Xor => e }
      }

      for {
        left <- xors
        right <- xors
        if left != right
        left_ = left.entries
        right_ = right.entries
        subset = left_.intersect(right_)
        if subset.size > 1 && left_.size > subset.size
      } yield {
        (left, Xor(left_.diff(subset) + Xor(subset)))
      }
    }.toList
  }

  // this detects when an OR can be expanded because it would allow its
  // XOR component to be shared with an existing XOR gate.
  //
  // a + b = a.b' + a'.b + a.b
  object SharedOrXor extends GlobalRule {
    override def name: String = "shared_or_xor"

    override def perform(circuits: Set[Logic]): List[Map[Logic, Logic]] =
      xors_ors(circuits).map { case (a, b) => Map(a -> b) }

    private def xors_ors(circuits: Set[Logic]): List[(Logic, Logic)] = {
      val ors = circuits.flatMap { circuit =>
        circuit.nodes.collect { case e: Or => e }
      }
      val xors = circuits.flatMap { circuit =>
        circuit.nodes.collect { case e: Xor => e }
      }
      for {
        left <- ors
        right <- xors
        left_ = left.entries
        right_ = right.entries
        subset = left_.intersect(right_)
        if subset.size >= 2
      } yield {
        val evens = (2 to subset.size by 2).flatMap { i =>
          subset.subsets(i).map(And(_))
        }.toSet

        (left, Or(left_.diff(subset) ++ evens + Xor(subset)))
      }
    }.toList

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
    case Xor(entries) =>
      entries.map(_.render(true, false)).mkString("(", " ⊕ ", ")")
    case Xnor(entries) =>
      entries.map(_.render(true, false)).mkString("(", " ⊙ ", ")")
    case OneHot(entries) =>
      entries.map(_.render(true, false)).mkString("(", " Δ ", ")")
    case NotOneHot(entries) =>
      entries.map(_.render(true, false)).mkString("(", " ∇ ", ")")
  }
  final def render: String = render(true, true)
  override final def toString: String = render

  final def eval(input: BitSet): Boolean = self match {
    case True => true
    case In(a) => input(a)
    case Inv(e) => !e.eval(input)
    case And(as) => as.forall(_.eval(input))
    case Or(os) => os.exists(_.eval(input))
    case Xor(es) => es.count(_.eval(input)) % 2 == 1
    case Xnor(es) => es.count(_.eval(input)) % 2 == 0
    case OneHot(es) => es.count(_.eval(input)) == 1
    case NotOneHot(es) => es.count(_.eval(input)) != 1
  }

  // Replace every node that is equal to the target, recursing into children.
  //
  // Does not recurse into the replacement Node(s).
  final def replace(target: Logic, replacement: Logic): Logic =
    replace(Map(target -> replacement))

  final def replace(lut: Map[Logic, Logic]): Logic = lut.get(self) match {
    case Some(replacement) => replacement
    case None =>
      def replace_(entries: Iterable[Logic])(cons: Iterable[Logic] => Logic): Logic = {
        val entries_ = entries.map { e =>
          val replaced = e.replace(lut)
          (replaced ne e, replaced)
        }
        if (entries_.exists(_._1)) cons(entries_.map(_._2))
        else self
      }

      self match {
        case True => self
        case Inv(e) =>
          val replaced = e.replace(lut)
          if (replaced ne e) Inv(replaced) else self
        case And(entries) =>
          replace_(entries)(es => And(es.toSet))
        case Or(entries) =>
          replace_(entries)(es => Or(es.toSet))
        case Xor(entries) =>
          replace_(entries)(es => Xor(es.toSet))
        case Xnor(entries) =>
          replace_(entries)(es => Xnor(es.toSet))
        case OneHot(entries) =>
          replace_(entries)(es => OneHot(es.toSet))
        case NotOneHot(entries) =>
          replace_(entries)(es => NotOneHot(es.toSet))
        case _: In => self
      }
  }

  def nodes: Set[Logic] = {
    self match {
      case True => Set(self)
      case In(_) => Set(self)
      case Inv(a) => a.nodes + self
      case And(es) => es.flatMap(_.nodes) + self
      case Or(es) => es.flatMap(_.nodes) + self
      case Xor(es) => es.flatMap(_.nodes) + self
      case Xnor(es) => es.flatMap(_.nodes) + self
      case OneHot(es) => es.flatMap(_.nodes) + self
      case NotOneHot(es) => es.flatMap(_.nodes) + self
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
    override val hashCode: Int = 19 * entries.hashCode
    override def equals(that: Any): Boolean = that match {
      case thon: And => hashCode == thon.hashCode && entries.size == thon.entries.size && entries == thon.entries
      case _ => false
    }
  }

  // structure enforces indempotency A + A = A
  // constructor enforces identity A + 0 = A
  // constructor enforces complementation A + A' = 1
  case class Or  private[logic](entries: Set[Logic]) extends Logic {
    override val hashCode: Int = 23 * entries.hashCode
    override def equals(that: Any): Boolean = that match {
      case thon: Or => hashCode == thon.hashCode && entries.size == thon.entries.size && entries == thon.entries
      case _ => false
    }
  }

  case class In  (channel: Int) extends Logic

  // a placemarker (along with Inv(True)) for nodes that can be collapsed
  case object True extends Logic

  // XOR/XNOR/OH/NOH/NAND/NOR may seem like unusual entries in the AST because
  // they are just special forms of AND/OR. However, it's necessary to encode
  // them to avoid carrying metadata, plus there is ambiguity in the inversion
  // of inputs when written in the OR form. Ideally we'd have a "core" AST and
  // an "extended" one, but since we have very little use for the core AST, we
  // only use this extended one.

  // x ⊕ y = (x' · y) + (x · y')
  //
  // extending to n-arity matches all odd parities
  case class Xor private[logic](entries: Set[Logic]) extends Logic {
    override val hashCode: Int = 29 * entries.hashCode
    override def equals(that: Any): Boolean = that match {
      case thon: Xor => hashCode == thon.hashCode && entries.size == thon.entries.size && entries == thon.entries
      case _ => false
    }

    def asCore: Logic = Or {
      (1 to entries.size by 2).flatMap { i: Int =>
        entries.subsets(i).map { odd =>
          And(odd ++ entries.diff(odd).map(Inv(_)))
        }
      }.toSet
    }
  }

  // x ⊙ y = (x · y) + (x' · y')
  //
  // higher arity counts even parity (in the sense that it is "not odd").
  case class Xnor private[logic](entries: Set[Logic]) extends Logic {
    override val hashCode: Int = 31 * entries.hashCode
    override def equals(that: Any): Boolean = that match {
      case thon: Xnor => hashCode == thon.hashCode && entries.size == thon.entries.size && entries == thon.entries
      case _ => false
    }
    def asCore: Logic = Or {
      (0 to entries.size by 2).flatMap { i: Int =>
        entries.subsets(i).map { even =>
          And(even ++ entries.diff(even).map(Inv(_)))
        }
      }.toSet
    }
  }

  // "one hot" means exactly one of the inputs is high, and the rest are low.
  case class OneHot private[logic](entries: Set[Logic]) extends Logic {
    override val hashCode: Int = 37 * entries.hashCode
    override def equals(that: Any): Boolean = that match {
      case thon: OneHot => hashCode == thon.hashCode && entries.size == thon.entries.size && entries == thon.entries
      case _ => false
    }

    def asCore: Logic = Or {
      entries.map { hot => And((entries - hot).map(Inv(_)) + hot) }
    }
  }

  // negation of "one hot"
  case class NotOneHot private[logic](entries: Set[Logic]) extends Logic {
    override val hashCode: Int = 41 * entries.hashCode
    override def equals(that: Any): Boolean = that match {
      case thon: NotOneHot => hashCode == thon.hashCode && entries.size == thon.entries.size && entries == thon.entries
      case _ => false
    }
    def asCore: Logic = Or {
      val entries_ = entries.map(Inv(_))

      (2 to entries_.size).toSet.flatMap { i: Int =>
        entries_.subsets(i).map { subs =>
          And(subs.map(Inv(_)) ++ entries_.diff(subs))
        }.toSet
      } + And(entries_)
    }
  }

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
        if (entries_.contains(Inv(e)) || (top && e == True))
          entries_ = Set(True)
        else if ((!top && entries_.contains(e)) || (top && e == Inv(True) && entries.size > 1))
          entries_ = entries_ - e // only remove FALSE if we have something that can be TRUE

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

  object Xor {
    def apply(head: Logic, tail: Logic*): Logic =
      apply(tail.toSet + head)

    def apply(entries: Set[Logic]): Logic = {
      require(entries.nonEmpty)
      if (entries.size == 1) entries.head
      else {
        require_normed(entries)
        new Xor(entries)
      }
    }

    // note that Xor(Xor(inputs).asCore) == Xor(inputs) is not true in general,
    // as inputs may be inverted in pairs.
    def from(node: Logic): Option[Logic] = node match {
      case Inv(Xnor(es)) => Some(new Xor(es))
      case Or(es) =>
        val (invalid, terms) = es.partitionMap {
          case And(es_) => Right(es_)
          case other => Left(other)
        }
        if (invalid.nonEmpty)
          return None

        val comps = terms.flatten
        val norms = comps.map {
          case Inv(e) => e
          case e => e
        }

        // - every term has the same number of components.
        // - every component, and its inverse, appears an equal number of times.
        // - the number of terms is the number of ways to get odd parity TODO (precalculated)
        if (norms.size < 2 || terms.map(_.size).size != 1 || comps.size != 2 * norms.size)
          return None

        // this search is redundant leading to bad performance for negatives,
        // but is still efficient for positives. We could prune all permutations
        // of inputs where an even number of inputs have been inverted, but
        // that's not free.
        (0 to norms.size).reverse.foreach { i =>
          // subsets(0) gives an empty set allowing for all flipped
          norms.subsets(i).foreach { ss =>
            val inputs = ss ++ (norms.diff(ss).map(Inv(_)))
            val xor = new Xor(inputs)
            if (xor.asCore == node) return Some(xor)
          }
        }
        None

      case _ => None
    }
  }

  object Xnor {
    def apply(head: Logic, tail: Logic*): Logic =
      apply(tail.toSet + head)

    def apply(entries: Set[Logic]): Logic = {
      require(entries.nonEmpty)
      if (entries.size == 1) entries.head
      else {
        require_normed(entries)
        new Xnor(entries)
      }
    }

    def from(node: Logic): Option[Logic] = node match {
      case Inv(Xor(es)) => Some(new Xnor(es))
      case Or(es) =>
        val (invalid, terms) = es.partitionMap {
          case And(es_) => Right(es_)
          case other => Left(other)
        }
        if (invalid.nonEmpty)
          return None
        val comps = terms.flatten
        val norms = comps.map {
          case Inv(e) => e
          case e => e
        }

        // XNOR has roughly the same properties as XOR
        if (norms.size < 2 || terms.map(_.size).size != 1 || comps.size != 2 * norms.size)
          return None

        (0 to norms.size).reverse.foreach { i =>
          // subsets(0) gives an empty set allowing for all flipped
          norms.subsets(i).foreach { ss =>
            val inputs = ss ++ (norms.diff(ss).map(Inv(_)))
            val xnor = new Xnor(inputs)
            if (xnor.asCore == node) return Some(xnor)
          }
        }
        None
      case _ => None
    }
  }

  object OneHot {
    def apply(head: Logic, tail: Logic*): Logic =
      apply(tail.toSet + head)

    def apply(entries: Set[Logic]): Logic = {
      if (entries.size < 3) Xor(entries)
      else {
        require_normed(entries)
        new OneHot(entries)
      }
    }

    def from(node: Logic): Option[Logic] = node match {
      case Inv(NotOneHot(es)) => Some(new OneHot(es))
      case Or(es) =>
        val (invalid, terms) = es.toList.partitionMap {
          case And(es_) => Right(es_.toList)
          case other => Left(other)
        }
        if (invalid.nonEmpty) return None

        val widths = terms.map(_.size).toSet
        if (widths.size != 1 || widths.head < 3) return None

        val counts = terms.flatten.counts
        if (counts.size != 2 * widths.head || counts.values.toSet.size != 2 )
          return None

        val inputs = counts.groupBy(_._2).minBy(_._1)._2.keySet
        val oh = new OneHot(inputs)

        if (oh.asCore == node) Some(oh)
        else None

      case _ => None
    }
  }

  object NotOneHot {
    def apply(head: Logic, tail: Logic*): Logic =
      apply(tail.toSet + head)

    def apply(entries: Set[Logic]): Logic = {
      require(entries.nonEmpty)
      if (entries.size < 3) Xnor(entries)
      else {
        require_normed(entries)
        new NotOneHot(entries)
      }
    }

    def from(node: Logic): Option[Logic] = node match {
      case Inv(OneHot(es)) => Some(new NotOneHot(es))
      case Or(es) =>
        val (invalid, terms) = es.toList.partitionMap {
          case And(es_) => Right(es_.toList)
          case other => Left(other)
        }
        if (invalid.nonEmpty) return None

        val widths = terms.map(_.size).toSet
        if (widths.size != 1 || widths.head < 3) return None

        val counts = terms.flatten.counts
        if (counts.size != 2 * widths.head || counts.values.toSet.size != 2 )
          return None

        // the opposite of OH...
        val inputs = counts.groupBy(_._2).maxBy(_._1)._2.keySet
        val noh = new NotOneHot(inputs)

        if (noh.asCore == node) Some(noh)
        else None

      case _ => None
    }
  }

  object In {

  }

  private def require_normed(entries: Set[Logic]): Unit = {
    val normed = entries.map {
      case Inv(e) => e
      case e => e
    }
    require(normed.size == entries.size)
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
      List(Factor, UnNest, Eliminate, DeMorgan, Split, Complement).map(new Cached(_, 1024 * 1024))
    }
    val global_rules = {
      import GlobalRule._
      List(SharedAnd, SharedOr, SharedXor, SharedOrXor)
    }

    val max_steps = 128
    val max_explored = 1024 * 1024
    val max_width = 128

    val obj = Objective.DTL_Components(
      resistor = 0,
      npn = 1,
      pnp = 1,
      diode = 0.75
    )

    type Circuit = Map[String, Logic]

    // Tracks which circuits have been fully explored to avoid repeating work.
    // We might want to limit since it is a designed-in leak.
    //
    // the list of rules and intermediate solutions is recorded to aid auditing.
    var all_my_circuits = minsums.asLogic.map { soln => soln -> (obj.measure(soln), List.empty[(Circuit, String, Double)]) }.toMap

    @unused def audit(circuit: Circuit): List[String] = {
      val history = all_my_circuits(circuit)
      val complete = (circuit, "final", history._1) :: history._2
      complete.reverse.map(_.toString)
    }

    val baseline = all_my_circuits.map(_._2._1).min

    // TODO add variants with truth table inverted for outputs with more than half true

    var step = 0

    // TODO parallelise

    // we repeat the same work for each output channel a lot of times so rule
    // application benefits from caching.

    var surface = all_my_circuits
    while (step < max_steps && all_my_circuits.size < max_explored && surface.nonEmpty) {
      var surface_ = surface
      surface = Map.empty

      def push(entry: Map[String, Logic], prev: Map[String, Logic], desc: String): Unit = {
        if (!all_my_circuits.contains(entry) && !surface.contains(entry)) {
          require(verify(minsums.input_width, prev, entry), desc)
          val cost = obj.measure(entry)
          val (last_cost, history) = all_my_circuits(prev)
          val trail = (cost, (prev, desc, last_cost) :: history)
          all_my_circuits += (entry -> trail)

          // only add to the surface if we are making progress...
          val progress = trail._2.map(_._3)
          if (cost < 2 * baseline && (progress.size < 4 || progress(0) <= progress(3))) {
            surface += (entry -> trail)
          }
        }
      }

      // this is where we prune the width of the search space. There are many
      // strategies that could be taken here (including random sampling, or
      // maximising hamming distance), but we do the very naive thing of only
      // considering the best performing circuits.
      surface_ = surface_.toList.sortBy(_._2._1).take(max_width).toMap

      surface_.foreach { case (last_soln, _) =>
        val nodes = last_soln.values.flatMap(_.nodes)
        local_rules.foreach { rule =>
          nodes.foreach { node =>
            rule.perform(node).foreach { repl =>
              // System.err.println(s"replacing $node with $repl via $rule")
              val update = last_soln.map {
                case (name, circuit) => name -> circuit.replace(node, repl)
              }
              push(update, last_soln, rule.name)
            }
          }
        }

        global_rules.foreach { rule =>
          rule.perform(last_soln.values.toSet).foreach { repl =>
            val update = last_soln.map {
              case (name, circuit) => name -> circuit.replace(repl)
            }
            push(update, last_soln, rule.name)
          }
        }

      }
      step += 1
      System.err.println(s"STEP=$step EXPLORED=${all_my_circuits.size}")
    }

    val soln = all_my_circuits.minBy(_._2._1)

    val cost = soln._2._1
    val names = minsums.input_names.zipWithIndex.map {
      case (n, i) => In(i) -> n
    }.toMap
    val netlist = Netlist.from(
      s"${in.getName} ($cost)",
      names,
      soln._1
    )
    System.out.println(netlist.toJsonPretty)

    // val impl = soln._1.map { case (n, c) => n -> Hardware.DTL.materialise(c) }
    // val shared = Hardware.DTL.fanout(impl.values.toSet).filter {
    //   case (Hardware.DTL.REF(_), _) => false
    //   case (_, out) => out > 1
    // }
    // System.err.println(s"SHARED = $shared ")
    // System.err.println(audit(soln._1).mkString("\n"))
    System.err.println(s"COST = ${cost}")
    // System.err.println(s"IMPL = $impl")
  }

  def verify(input_width: Int, orig: Map[String, Logic], update: Map[String, Logic]): Boolean = {
    (0 until (1 << input_width)).foreach { i =>
      val in = BitSet.fromBitMask(Array(i))
      for {
        channel <- orig.keys
      } {
        if (orig(channel).eval(in) != update(channel).eval(in))
          return false
      }
    }
    true
  }

}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain logic.Main tests/fulladder.truth\""
// End:
