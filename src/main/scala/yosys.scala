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
//    $reduce_and      (A, Y)
//    $reduce_bool     (A, Y)
//    $reduce_or       (A, Y)
//    $reduce_xnor     (A, Y)
//    $reduce_xor      (A, Y)
//
// Which are understood by netlistsvg by the default.svg skin file.
//
// Note that yosys has uppercase (gate level) cells, and lowercase (high level /
// verilog syntax) variants, and is free to rewrite the latter into gate level
// cells. The gate level cells are 1 bit binary operations, but the high level
// variants support multi-bit. $reduce_and and $reduce_or are roughly the
// multi-arity versions of AND and OR that we would care about (although the
// docs also say that the reduce_ variants are unary cells, so it's still all a
// bit unclear).
//
// Note that there is no "one hot" or "not one hot" in the standard cell
// library.
//
// We can also produce netlists that use non-standard cells by provide custom
// skins, but be aware that yosys will not be able to understand them. For
// example, netlistsvg provides an analog.svg that defines the visual
// description of basic components such as resistors, diodes, transistors and
// capacitors. The shape of the connections and required attributes may be
// inferred from reading the SVG.
package yosys

import scala.annotation.switch

import logic.Logic
import logic.Logic._

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
// attributes are cell-specific
case class Cell(
  `type`: Cell.Type,
  attributes: Map[String, String],
  port_directions: Map[Port.Name, Port.Direction],
  connections: Map[Port.Name, List[Connection]]
)

sealed trait Connection
object Connection {
  case class Literal(s: String) extends Connection {
    override def toString = s
  }
  case class Ref(i: Int) extends Connection {
    override def toString = i.toString
  }

  // in lieu of a shapely rule...
  implicit val ordering: Ordering[Connection] = new Ordering[Connection] {
    private val underlying_i = Ordering[Int]
    private val underlying_s = Ordering[String]
    def compare(x: Connection, y: Connection): Int = (x, y) match {
      case (Ref(_), Literal(_)) => -1
      case (Literal(_), Ref(_)) => 1
      case (Ref(a), Ref(b)) => underlying_i.compare(a, b)
      case (Literal(a), Literal(b)) => underlying_s.compare(a, b)
    }
  }

  implicit val encoder: jzon.Encoder[Connection] = new jzon.Encoder[Connection] {
    def unsafeEncode(a: Connection, indent: Option[Int], out: java.io.Writer): Unit = a match {
      case Literal(s) => jzon.Encoder[String].unsafeEncode(s, indent, out)
      case Ref(i) => jzon.Encoder[Int].unsafeEncode(i, indent, out)
    }
  }

  implicit val decoder: jzon.Decoder[Connection] = new jzon.Decoder[Connection] {
    def unsafeDecode(trace: List[jzon.Decoder.JsonError], in: jzon.internal.RetractReader): Connection = {
      val next = in.nextNonWhitespace()
      in.retract()

      (next: @switch) match {
        case '"' => Literal(jzon.Decoder[String].unsafeDecode(trace, in))
        case _ => Ref(jzon.Decoder[Int].unsafeDecode(trace, in))
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
  import Connection.{ Literal, Ref }

  implicit val encoder: jzon.Encoder[Netlist] = jzon.Encoder.derived
  implicit val decoder: jzon.Decoder[Netlist] = jzon.Decoder.derived

  def from(
    name: String,
    names: Map[In, String],
    outputs: Map[String, Logic]
  ): Netlist = {
    // all nodes are single output, so we can assign each node an index which
    // will be the connection identifier for its output.

    val lookup = outputs.values.flatMap(_.nodes).toSet.zipWithIndex.toMap
    def con(node: Logic): Connection = node match {
      case True => Literal("1")
      case Inv(True) => Literal("0")
      case _ => Ref(lookup(node))
    }

    // create the lookup from each node into a cell type, port dependencies
    val (ports, cells) = lookup.flatMap {
      case (node, _) => con(node) match {
        case Literal(_) => None
        case ref => Some(node -> ref)
      }
    }.partitionMap {
      case (True, y) => Right { s"True$$$y" ->
        // the "ref" doesn't seem to change the rendering
        Cell("$_constant_", Map("ref" -> "1"), Map("Y" -> "output"),
          Map("Y" -> List(y)))
      }
      case (n: OneHot, y) => Right { s"OneHot$$$y" ->
        // the "ref" doesn't seem to change the rendering
        Cell("generic", Map("ref" -> "OH"),
          Map("in0" -> "input", "out0" -> "output"),
          Map("in0" -> n.entries.map(con(_)).toList.sorted, "out0" -> List(y)))
      }
      case (n: NotOneHot, y) => Right { s"NotOneHot$$$y" ->
        // the "ref" doesn't seem to change the rendering
        Cell("generic", Map("ref" -> "NOH"),
          Map("in0" -> "input", "out0" -> "output"),
          Map("in0" -> n.entries.map(con(_)).toList.sorted, "out0" -> List(y)))
      }
      case (n: Inv, y) => Right { s"Inv$$$y" ->
        Cell("$_NOT_", Map.empty, Map("A" -> "input", "Y" -> "output"),
          Map("A" -> List(con(n.entry)), "Y" -> List(y)))
      }
      case (n: And, y) => Right { s"And$$$y" -> {
        if (n.entries.size == 2) {
          val es = n.entries.toList.map(con(_)).sorted
          Cell("$_AND_", Map.empty, Map("A" -> "input", "B" -> "input", "Y" -> "output"),
            Map("A" -> List(es(0)), "B" -> List(es(1)), "Y" -> List(y)))
        } else
            Cell("$reduce_and", Map.empty, Map("A" -> "input", "Y" -> "output"),
              Map("A" -> n.entries.map(con(_)).toList.sorted, "Y" -> List(y)))
      }}
      case (n: Or, y) => Right { s"Or$$$y" -> {
        if (n.entries.size == 2) {
          val es = n.entries.toList.map(con(_)).sorted
          Cell("$_OR_", Map.empty, Map("A" -> "input", "B" -> "input", "Y" -> "output"),
            Map("A" -> List(es(0)), "B" -> List(es(1)), "Y" -> List(y)))
        } else
            Cell("$reduce_or", Map.empty, Map("A" -> "input", "Y" -> "output"),
              Map("A" -> n.entries.map(con(_)).toList.sorted, "Y" -> List(y)))
      }}
      case (n: Xor, y) => Right { s"Xor$$$y" -> {
        if (n.entries.size == 2) {
          val es = n.entries.toList.map(con(_)).sorted
          Cell("$_XOR_", Map.empty, Map("A" -> "input", "B" -> "input", "Y" -> "output"),
            Map("A" -> List(es(0)), "B" -> List(es(1)), "Y" -> List(y)))
        } else
            Cell("$reduce_xor", Map.empty, Map("A" -> "input", "Y" -> "output"),
              Map("A" -> n.entries.map(con(_)).toList.sorted, "Y" -> List(y)))
      }}
      case (n: Xnor, y) => Right { s"Xnor$$$y" -> {
        if (n.entries.size == 2) {
          val es = n.entries.toList.map(con(_)).sorted
          Cell("$_XNOR_", Map.empty, Map("A" -> "input", "B" -> "input", "Y" -> "output"),
            Map("A" -> List(es(0)), "B" -> List(es(1)), "Y" -> List(y)))
        } else
            Cell("$reduce_xnor", Map.empty, Map("A" -> "input", "Y" -> "output"),
              Map("A" -> n.entries.map(con(_)).toList.sorted, "Y" -> List(y)))
      }}
      case (n: In, y) => Left { names(n) -> Port("input", List(y)) }
      case (n: Nand, y) => Right { s"Nand$$$y" -> {
        if (n.entries.size == 2) {
          val es = n.entries.toList.map(con(_)).sorted
          Cell("$_NAND_", Map.empty, Map("A" -> "input", "B" -> "input", "Y" -> "output"),
            Map("A" -> List(es(0)), "B" -> List(es(1)), "Y" -> List(y)))
        } else
            Cell("$reduce_nand", Map.empty, Map("A" -> "input", "Y" -> "output"),
              Map("A" -> n.entries.map(con(_)).toList.sorted, "Y" -> List(y)))
      }}
      case (n: Nor, y) => Right { s"Nor$$$y" -> {
        if (n.entries.size == 2) {
          val es = n.entries.toList.map(con(_)).sorted
          Cell("$_NOR_", Map.empty, Map("A" -> "input", "B" -> "input", "Y" -> "output"),
            Map("A" -> List(es(0)), "B" -> List(es(1)), "Y" -> List(y)))
        } else
            Cell("$reduce_nor", Map.empty, Map("A" -> "input", "Y" -> "output"),
              Map("A" -> n.entries.map(con(_)).toList.sorted, "Y" -> List(y)))
      }}
    }

    val signals = outputs.map {
      case (n, node) => n -> Port("output", List(con(node)))
    }

    Netlist(Map(name -> Module(ports.toMap ++ signals, cells.toMap)))
  }
}
