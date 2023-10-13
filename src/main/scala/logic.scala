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
  object Split extends LocalRule {
    private def isGate(n: Logic): Boolean = n.asNOH.nonEmpty || n.asOH.nonEmpty || n.asXNOR.nonEmpty || n.asXOR.nonEmpty

    override def perform(node: Logic): List[Logic] = node match {
      case Or(es) if es.size == 2 & node.asXOR.isEmpty =>
        // allows XOR subgates to be extracted from plain OR gates
        //
        // a + b = a.b' + a'.b + a.b
        //
        // in the hope that a common factor will eliminate the a.b.
        //
        // It might make sense to only perform this rule if we can detect that
        // the XOR component can be reused by Global.Shared, to avoid needlessly
        // expanding the search space.
        //
        // (is it worth doing this for higher arity?)
        val a = es.head
        val b = es.tail.head
        Or(Or(And(a, Inv(b)), And(Inv(a), b)), And(a, b)) :: Nil

      case Or(es) if es.size > 2 =>
        (2 to (es.size + 1) / 2).toList.flatMap { i =>
          es.subsets(i).flatMap { sub =>
            val n = new Or(sub)
            if (isGate(n)) Some(new Or(es.diff(sub) + n)) else None
          }
        }

      case And(es) if es.size > 2 =>
        (2 to (es.size + 1) / 2).toList.flatMap { i =>
          es.subsets(i).flatMap { sub =>
            val n = new And(sub)
            if (isGate(n)) Some(new And(es.diff(sub) + n)) else None
          }
        }

      case _ => Nil
    }
  }

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

    override def toString = underlying.toString
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
  // like LocalRule, implementations are encouraged to return each possible move
  // as an entry in a list instead of being aggressive and applying everything.
  def perform(circuits: Set[Logic]): List[Map[Logic, Logic]]
}

object GlobalRule {
  // FIXME tests for the global rules

  // finds multi-input gates that have subsets that could be utilised by other
  // overlapping parts of the circuit, and splits them out as nested entries.
  object Shared extends GlobalRule {
    override def perform(circuits: Set[Logic]): List[Map[Logic, Logic]] =
      (ands(circuits) ++ ors(circuits) ++ xors(circuits)).map { case (a, b) => Map(a -> b) }

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

    // these are not caught by the 'ors' rule because of the complex interaction
    // between the components.
    private def xors(circuits: Set[Logic]): List[(Logic, Logic)] = {
      val xors = circuits.filter(_.asXOR.nonEmpty)

      // if (xors.nonEmpty) {
      //   System.out.println(s"SHARED XORS $xors")
      // }

      for {
        left <- xors
        right <- xors
        if left != right
        left_ = left.asXOR
        right_ = right.asXOR
        subset = left_.intersect(right_)
        if subset.size > 1 && left_.size > subset.size
      } yield {
        (left, Xor(left_.diff(subset) + Xor(subset)))
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

        case _: In => self
      }
  }

  lazy val nodes: Set[Logic] = {
    self match {
      case True => Set(self)
      case In(_) => Set(self)
      case Inv(a) => a.nodes + self
      case And(es) => es.flatMap(_.nodes) + self
      case Or(es) => es.flatMap(_.nodes) + self
    }
  }

  // the following as* methods return the parameters of the indicated gate if
  // this node can be represented by that gate. This is important for both rule
  // application and hardware dependent materialisation stages. A logic node may
  // be represented by multiple gates, e.g. XOR is the same as OH for 2 inputs.

  // x ⊕ y = (x' · y) + (x · y')
  //
  // extending to n-arity matches all odd parities.
  lazy val asXOR: Set[Logic] = this match {
    case True => Set.empty
    case In(_) => Set.empty
    case Inv(e) => e.asXNOR
    case And(_) => Set.empty // reachable by DeMorgan
    case Or(es) =>
      val abc = level2(es)
      val abc_ = abc.map(Inv(_))
      val expect_xor = (1 to abc_.size by 2).toSet.flatMap { i: Int =>
        abc_.subsets(i).map { subs =>
          And(subs.map(Inv(_)) ++ (abc_.diff(subs)))
        }.toSet
      }

      if (es == expect_xor) abc
      else Set.empty
  }

  // x ⊙ y = (x · y) + (x' · y')
  //
  // extending to n-arity is everything except odd parities.
  lazy val asXNOR: Set[Logic] =  this match {
    case True => Set.empty
    case In(_) => Set.empty
    case Inv(e) => e.asXOR
    case And(_) => Set.empty // reachable by DeMorgan
    case Or(es) =>
      val abc = level2(es)
      val abc_ = abc.map(Inv(_))
      val expect_xnor = (1 to abc_.size).filter(_ % 2 == 0).toSet.flatMap { i: Int =>
        abc_.subsets(i).map { subs =>
          And(subs.map(Inv(_)) ++ (abc_.diff(subs)))
        }.toSet
      } + And(abc_)

      if (es == expect_xnor) abc
      else Set.empty
  }

  lazy val asOH: Set[Logic] = this match {
    case True => Set.empty
    case In(_) => Set.empty
    case Inv(e) => e.asNOH
    case And(_) => Set.empty // reachable by DeMorgan
    case Or(es) =>
      val abc = level2(es)
      val abc_ = abc.map(Inv(_))
      val expect_oh = abc_.map { a =>
        And((abc_ - a) + Inv(a))
      }

      if (es == expect_oh) abc
      else Set.empty
  }

  lazy val asNOH: Set[Logic] =  this match {
    case True => Set.empty
    case In(_) => Set.empty
    case Inv(e) => e.asOH
    case And(_) => Set.empty // reachable by DeMorgan
    case Or(es) =>
      val abc = level2(es)
      val abc_ = abc.map(Inv(_))
      val expect_noh = (2 to abc_.size).toSet.flatMap { i: Int =>
        abc_.subsets(i).map { subs =>
          And(subs.map(Inv(_)) ++ (abc_.diff(subs)))
        }.toSet
      } + And(abc_)

      if (es == expect_noh) abc
      else Set.empty
  }

  // FIXME using level2 as the only seed is bad because it only considers gates
  // where the uninverted inputs are the dimensions of the gate. But it may be
  // the case, for example, that the "b" needs to be inverted. We should
  // consider all permutations (gate dependent!).

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

  // a constructor around Or
  object Xor {
    def apply(head: Logic, tail: Logic*): Logic =
      apply(tail.toSet + head)

    def apply(entries: Set[Logic]): Logic = {
      // TODO support all arities
      if (entries.size == 2) {
        val i0 = entries.head
        val i1 = entries.tail.head
        Or(
          And(Inv(i0), i1), // x' y
          And(i0, Inv(i1)), // x  y'
        )
      } else if (entries.size == 3) {
        val i0 = entries.head
        val i1 = entries.tail.head
        val i2 = entries.tail.tail.head
        Or(
          And(Inv(i0), Inv(i1), i2), // x' y' z
          And(Inv(i0), i1, Inv(i2)), // x' y  z'
          And(i0, Inv(i1), Inv(i2)), // x  y' z'
          And(i0, i1, i2),           // x  y  z
        )
      } else ???
    }
  }

  object In {

  }

  def fanout(circuits: Set[Logic]): Map[Logic, Int] = {
    def fanout_seq(acc: Map[Logic, Int], els: Set[Logic]) =
      els.foldLeft(acc) { case (acc_, e) => fanout_(acc_, e)}

    def fanout_(acc: Map[Logic, Int], c: Logic): Map[Logic, Int] = {
      val acc_ = acc.incr(c)
      if (acc.contains(c)) acc_
      else c match {
        case True => acc_
        case In(_)  => acc_
        case Inv(e)  => fanout_seq(acc_, Set(e))
        case And(es) => fanout_seq(acc_, es)
        case Or(es) => fanout_seq(acc_, es)
      }
    }

    circuits.foldLeft(Map.empty[Logic, Int]) {
      case (acc, c) => fanout_(acc, c)
    }
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
    val global_rules = {
      import GlobalRule._
      List(Shared)
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
      case (needle, _) => verify(minsums.input_width, ground_truth, needle, None, "sop")
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

      def push(entry: Map[String, Logic], prev: Map[String, Logic], desc: String): Unit = {
        if (!all_my_circuits.contains(entry) && !surface.contains(entry)) {
          verify(minsums.input_width, ground_truth, entry, Some(prev), desc)
          surface += entry
          all_my_circuits += (entry -> obj.measure(entry))
        }
      }

      surface_.foreach { last_soln =>
        val nodes = last_soln.values.flatMap(_.nodes)
        local_rules.foreach { rule =>
          nodes.foreach { node =>
            rule.perform(node).foreach { repl =>
              // System.out.println(s"replacing $node with $repl via $rule")
              val update = last_soln.map {
                case (name, circuit) => name -> circuit.replace(node, repl)
              }
              push(update, last_soln, s"[$rule on $node]")
            }
          }
        }

        global_rules.foreach { rule =>
          rule.perform(last_soln.values.toSet).foreach { repl =>
            val update = last_soln.map {
              case (name, circuit) => name -> circuit.replace(repl)
            }
            push(update, last_soln, rule.toString)
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

    // FIXME match the efficiency of the textbook solution

    // FIXME why are we getting into this situation?
    // (i0·i1) + (i0·i2) + (i1·i2) != ((i1'·i0) + (i1·i0'))' + (i0·i2) + (i1·i2) in Co
    // (((i0·i1)'·((i0·i1') + (i0'·i1))') + ((i1'·i0) + (i1·i0')))' + (i0·i2) + (i1·i2)

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
    System.out.println(s"textbook impl = $textbook")
    val fanout_textbook = Hardware.DTL.fanout(textbook.values.toSet)
    System.out.println(s"textbook cost = ${obj.measureFanout(fanout_textbook)}")

  }

  def verify(input_width: Int, orig: Map[String, Logic], update: Map[String, Logic], prev: Option[Map[String, Logic]], debug: String): Unit = {
    (0 until (1 << input_width)).foreach { i =>
      val in = BitSet.fromBitMask(Array(i))
      for {
        channel <- orig.keys
      } {
        if (orig(channel).eval(in) != update(channel).eval(in)) {
          val extra = prev match {
            case None => ""
            case Some(prev_) => s" (previously ${prev_(channel)})"
          }
          throw new AssertionError(s"verification failure $debug ${orig(channel)} != ${update(channel)} in $channel$extra")
        }
      }
    }
  }

}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain logic.Main tests/fulladder.truth\""
// End:
