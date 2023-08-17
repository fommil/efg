package logic

import java.io.File
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

import scala.collection.immutable.BitSet

import mccluskey.{ SofP, Util }

import Logic._

// TODO rule: ~A·~B + A·B => XNOR
//      rule: A.~B + ~A.B => XOR
// (check) A.B + A.C + B.C => ??? at least 2 trues

// TODO XOR expansion (c.f. Brayton90)
// TODO Triangles (c.f. Brayton90)
// TODO weak division (find common factors)
// TODO metarule replacement database
//      - https://github.com/berkeley-abc/abc
//      - https://people.eecs.berkeley.edu/~alanmi/publications/
// TODO visualisation format
//      - graphviz (won't look like a digital circuit though)
//      - https://tex.stackexchange.com/questions/32839 (big dependency)
//      - https://gojs.net/latest/samples/LogicCircuit.html (no positioning)
//      - https://github.com/nturley/netlistsvg
sealed trait Logic {
  // this is a bit rubbish because it doesn't show common nodes.
  final def render(top: Boolean)(show: Int => String): String = this match {
    case In(a) => show(a)
    case Inv(e) => "~" + e.render(false)(show)
    case And(entries) => entries.map(_.render(false)(show)).mkString("·")
    case Or(entries) =>
      val parts = entries.map(_.render(false)(show))
      if (top) parts.mkString(" + ")
      else parts.mkString("(", " + ", ")")
  }

  def render(show: Int => String): String = render(true)(show)
  def render: String = render(true)(_.toString)

  //  override final def toString: String = render(false)(_.toString)

  def eval(input: BitSet): Boolean = this match {
    case In(a) => input(a)
    case Inv(e) => !e.eval(input)
    case And(as) => as.forall(_.eval(input))
    case Or(os) => os.exists(_.eval(input))
  }

  private def deMorgan: Logic = this match {
    case And(entries) =>
      val (invs, regs) = entries.partitionMap {
        case Inv(e) => Left(e)
        case e => Right(e)
      }
      if (invs.size > regs.size) {
        // ~A.~B.C = ~(A + B + ~C)
        Inv(Or(invs ++ regs.map(Inv(_)))).factor
      } else this

    case Or(entries) =>
      val (invs, regs) = entries.partitionMap {
        case Inv(e) => Left(e)
        case e => Right(e)
      }
      if (invs.size > regs.size) {
        // ~(~A + ~B + C) = A.B.~C
        Inv(And(invs ++ regs.map(Inv(_)))).factor
      } else this

    case other => other
  }

  // NOTE: this is probably a really rubbish approach. What we really want to do
  // is to create the list of all the unique nodes, and then generate
  // substitutions that we then search through. This is just blindly applying
  // rules without any regard for where we are going. But it's useful for
  // testing.
  // extracts common factors using a greedy algorithm
  def factor: Logic = this match {
    case In(_) => this
    case Inv(a) =>
      // this should only flip if *everything* is inverted, to avoid infinite
      // loops with deMorgans.
      a.factor match {
        case Inv(e) => e
        case a@ And(entries) =>
          val (invs, regs) = entries.partitionMap {
            case Inv(e) => Left(e)
            case other => Right(other)
          }
          if (regs.isEmpty) And(invs)
          else Inv(a)
        case a@ Or(entries) =>
          val (invs, regs) = entries.partitionMap {
            case Inv(e) => Left(e)
            case other => Right(other)
          }
          if (regs.isEmpty) Or(invs)
          else Inv(a)

        case other => Inv(other)
      }

    case And(entries) =>
      // this is basically PofS in McCluskey, but for a more general AST.
      val (tops, other) = entries.map(_.factor).partitionMap {
        case And(subs) => Left(subs)
        case other => Right(other)
      }
      // should really find if there is anything common between the "other"s and
      // extract, but since we're focussing on applying this only to 2-level
      // logic, we don't care for now.
      val remain = other.filterNot {
        case Or(ors) => Util.overlaps(ors, tops)
        case _ => false
      }
      And(tops.flatten ++ remain).deMorgan

    case Or(entries) =>
      val parts = entries.map(_.factor)
      val (popular, many) = parts.toList.flatMap {
        case And(es) => es.toList
        case e => List(e)
      }.groupBy(identity).map {
        case (expr, occs) => expr -> occs.size
      }.maxBy(_._2) // this is the greedy selection

      {
        if (many < 2) {
          Or(parts)
        } else {
          val (factored, uncommon) = parts.partitionMap {
            case e @ And(es) =>
              if (es.contains(popular)) Left(And(es - popular)) else Right(e)
            case e =>
              if (e == popular) Left(e) else Right(e)
          }

          val and = And(Set(popular) + Or(factored))

          if (uncommon.isEmpty) and
          else {
            Or(uncommon).factor match {
              case Or(nested) => Or(nested + and)
              case other => Or(Set(and, other))
            }
          }
        }.deMorgan
      }

  }

  // maybe we should allow this to be mutated...
  def dedupe(nodes: Map[Logic, Logic]): (Logic, Map[Logic, Logic]) = {
    def withThis[A](res: (A, Map[Logic, Logic]))(cons: A => Logic): (Logic, Map[Logic, Logic]) = {
      val node = cons(res._1)
      (node, res._2 + (node -> node))
    }

    nodes.get(this) match {
      case Some(hit) => (hit, nodes)
      case None => this match {
        case Inv(e) =>
          withThis(e.dedupe(nodes))(Inv(_))
        case And(entries) =>
          val foo = entries.foldLeft((Set.empty[Logic], nodes)) {
            case ((es, acc), e) =>
              val (node, acc_) = e.dedupe(acc)
              (es + node, acc_ + (node -> node))
          }
          withThis(foo)(And(_))
        case Or(entries) =>
          val foo = entries.foldLeft((Set.empty[Logic], nodes)) {
            case ((es, acc), e) =>
              val (node, acc_) = e.dedupe(acc)
              (es + node, acc_ + (node -> node))
          }
          withThis(foo)(Or(_))
        case i @ In(_) =>
          withThis((i, nodes))(identity)
      }
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
      else {
        // this is a bit much, will backfire when we try to share gates. Maybe
        // all constructions should be followed by a choice to leave as-is or to
        // try to unnest.
        val (nested, not) = entries.partitionMap {
          case And(es) => Left(es)
          case other => Right(other)
        }
        if (not.isEmpty) new And(nested.flatten)
        else new And(entries)
      }
    }
  }

  object Or {
    def apply(entries: Set[Logic]): Logic = {
      require(entries.nonEmpty)
      if (entries.size == 1) entries.head
      else {
        val (nested, not) = entries.partitionMap {
          case Or(es) => Left(es)
          case other => Right(other)
        }
        if (not.isEmpty)
          new Or(nested.flatten)
        else
          new Or(entries)
      }
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

    val mins = jzon.Decoder[SofP.Storage].decodeJson(input) match {
      case Left(err) => throw new IllegalArgumentException(err)
      case Right(as) => as
    }

    val syms = Util.alpha.take(mins.input_width).map(_.toLowerCase).zipWithIndex.map(_.swap).toMap

    // output some really simple deduped gate counts (not really a cost)
    // this only works for 2 outputs, make it general
    val List(as, bs) = mins.asLogic.reverse // reverse to match the file format
    for {
      a <- as
      b <- bs
    } yield {
      val af = a.factor
      val bf = b.factor
      val (_, deduped) = af.dedupe(Map.empty[Logic, Logic])
      val (_, deduped_) = bf.dedupe(deduped)

      // simple gate counting metric
      val nodes = deduped_.keys.filter {
        case In(_) => false
        case _ => true
      }

      // FIXME the output is junk, one of the rules is clearly buggy
      System.out.println(s"nodes = ${nodes.size} { ${af.render(syms)} ; ${bf.render(syms)} }")
    }
  }
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain logic.Main tests/fulladder.minsums.json\""
// End:
