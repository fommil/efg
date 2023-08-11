package logic

import scala.collection.immutable.BitSet

// TODO XOR expansion (c.f. Brayton90)
// TODO Triangles (c.f. Brayton90)
sealed trait Logic {
  import Logic._

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

}
object Logic {
  case class Inv(entry: Logic) extends Logic
  case class And(entries: List[Logic]) extends Logic
  case class Or(entries: List[Logic]) extends Logic
  case class In(channel: Int) extends Logic
}
