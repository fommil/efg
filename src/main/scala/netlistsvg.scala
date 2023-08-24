// Reading and writing yosys netlists (a JSON format).
//
// https://github.com/yosyshq/yosys
// https://github.com/nturley/netlistsvg
//
// Prefer the git version, e.g.
// sudo npm install -g git@github.com:nturley/netlistsvg.git
//
// To find the list of standard cells, start `yosys` and type `help -cells`. e.g.
//
//    $_AND_           (A, B, Y)
//    $_NAND_          (A, B, Y)
//    $_NOR_           (A, B, Y)
//    $_NOT_           (A, Y)
//    $_OR_            (A, B, Y)
//    $_XNOR_          (A, B, Y)
//    $_XOR_           (A, B, Y)
//
// Which are understood by netlistsvg by the default.svg skin file.
//
// Note that yosys has uppercase (gate level) cells, and lowercase (high level /
// verilog syntax) variants, and is free to rewrite the latter into gate level
// cells. By using exclusively the gate level variants, we can ensure that the
// structures are preserved.
//
// We can also produce netlists that use non-standard cells by provide custom
// skins, but be aware that yosys will not be able to understand them. For
// example, netlistsvg provides an analog.svg that defines the visual
// description of basic components such as resistors, diodes, transistors and
// capacitors. The shape of the connections and required attributes may be
// inferred from reading the SVG.
package netlistsvg

import scala.annotation.switch

import jzon.Decoder.{ JsonError, UnsafeJson }
import jzon.internal.RetractReader

case class Netlist(
  modules: Map[Module.Name, Module]
)
case class Module(
  ports: Map[Port.Name, Port],
  cells: Map[Cell.Name, Cell]
)
case class Port(
  direction: Port.Direction,
  bits: List[Connection]
)
// port_directions are only required for non-standard cells
// attributes are cell-specific
case class Cell(
  `type`: Cell.Type,
  attributes: Map[String, String],
  port_directions: Map[Port.Name, Port.Direction],
  connections: Map[Port.Name, List[Connection]]
)

sealed trait Connection
object Connection {
  case class Literal(s: String) extends Connection
  case class Ref(i: Int) extends Connection

  implicit val encoder: jzon.Encoder[Connection] = new jzon.Encoder[Connection] {
    def unsafeEncode(a: Connection, indent: Option[Int], out: java.io.Writer): Unit = a match {
      case Literal(s) => jzon.Encoder[String].unsafeEncode(s, indent, out)
      case Ref(i) => jzon.Encoder[Int].unsafeEncode(i, indent, out)
    }
  }

  implicit val decoder: jzon.Decoder[Connection] = new jzon.Decoder[Connection] {
    def unsafeDecode(trace: List[JsonError], in: RetractReader): Connection = {
      val next = in.nextNonWhitespace()
      in.retract()
      (next: @switch) match {
        case '"' => Literal(jzon.Decoder[String].unsafeDecode(trace, in))
        case '0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9' => Ref(jzon.Decoder[Int].unsafeDecode(trace, in))
        case _ => throw UnsafeJson(JsonError.Message("expected string or number") :: trace)
      }
    }
  }
}

object Cell {
  type Name = String
  type Type = String // if it starts with $ it must be one of the yosys standard cells

  implicit val encoder: jzon.Encoder[Cell] = jzon.Encoder.derived
  implicit val decoder: jzon.Decoder[Cell] = jzon.Decoder.derived
}

object Port {
  type Name = String
  type Direction = String // input|output

  implicit val encoder: jzon.Encoder[Port] = jzon.Encoder.derived
  implicit val decoder: jzon.Decoder[Port] = jzon.Decoder.derived
}

object Module {
  type Name = String

  implicit val encoder: jzon.Encoder[Module] = jzon.Encoder.derived
  implicit val decoder: jzon.Decoder[Module] = jzon.Decoder.derived
}

object Netlist {

}
