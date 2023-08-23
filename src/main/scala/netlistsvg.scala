// Reading and writing yosys netlists (a JSON format).
//
// https://github.com/yosyshq/yosys
// https://github.com/nturley/netlistsvg
package netlistsvg


// TL;DR of the schema is
/*
{
  "modules": {
    "<dont care>": {
      "ports": {
        "<port name>": {
          "direction": "<input|output>",
          "bits": [ 2, "1", ... ]
        },
        ...
      },
      "cells": {
        "<cell name>": {
          "type": "<type name>",
          "attributes": {
            "WIDTH": 3,
            ...
          },
          "port_directions": {
            "<port name>": "<input|output>",
            ...
          },
          "connections": {
            "<port name>": [ 3, "0", ... ],
            ...
          }
      },
      ...
    }
  }
}
*/

case class Top(
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
case class Cell(
  `type`: Cell.Type,
  attributes: Map[String, String],
  port_directions: Map[Port.Name, Port.Direction], // unidirectional ports omitted
  connections: Map[Port.Name, List[Connection]]
)

sealed trait Connection // Either[String, Int]
object Connection {
  case class ROM(symbol: String) extends Connection
  case class Ref(i: Int) extends Connection
}

object Module {
  type Name = String
}

object Port {
  type Name = String
  type Direction = String // input|output
}

object Cell {
  type Name = String
  type Type = String

  // some examples...
  //
  // type port/direction connections/sizes attributes
  //
  // $add A=input,B=input,Y=input A=0,B=2,Y=10
  // $and A=input,B=input,Y=output A=1,B=1,Y=1
  // $dff CLK=input,D=input,Q=output CLK=1,D=0,Q=9
  //
  // r_v <none> A=1,B=1 value=10k
  //
  // ...
}
