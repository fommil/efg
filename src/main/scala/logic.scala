package logic

import scala.collection.immutable.BitSet

// TODO XOR expansion (c.f. Brayton90)
// TODO Triangles (c.f. Brayton90)
// TODO weak division (find common factors)
// TODO metarule replacement database
// TODO visualisation format
//      - graphviz (won't look like a digital circuit though)
//      - https://tex.stackexchange.com/questions/32839 (big dependency)
//      - https://gojs.net/latest/samples/LogicCircuit.html (no positioning)
sealed trait Logic {
  import Logic._

  // this is a bit rubbish because it doesn't show common nodes.
  final def render(top: Boolean)(show: Int => String): String = this match {
    case In(a) => show(a)
    case Inv(e) => "~" + e.render(false)(show)
    case And(entries) => entries.map(_.render(false)(show)).mkString(".")
    case Or(entries) =>
      val parts = entries.map(_.render(false)(show))
      if (top) parts.mkString(" + ")
      else parts.mkString("(", " + ", ")")
  }

  override final def toString: String = render(false)(_.toString)

  def eval(input: BitSet): Boolean = this match {
    case In(a) => input(a)
    case Inv(e) => !e.eval(input)
    case And(as) => as.forall(_.eval(input))
    case Or(os) => os.exists(_.eval(input))
  }

  // TODO consider all possible factors

  // extracts common factors using a greedy algorithm. This is designed
  // primarily to work on 2-level OR(AND(...)) logic so it may not produce great
  // results for deeper logics.
  def factor: Logic = this match {
    case In(_) => this
    case Inv(a) => Inv(a.factor)
    case And(entries) =>
      val (tops, other) = entries.map(_.factor).partitionMap {
        case And(subs) => Left(subs)
        case other => Right(other)
      }
      // 
      And(tops.flatten.distinct ++ other)
    case Or(entries) =>
      //entries.
      ???

  }

  def dedupe(nodes: Map[Logic, Logic]): (Logic, Map[Logic, Logic]) = ???

}
object Logic {
  case class Inv(entry: Logic) extends Logic
  case class And(entries: List[Logic]) extends Logic
  case class Or(entries: List[Logic]) extends Logic
  case class In(channel: Int) extends Logic
}
