package logic

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

    override def measure(circuit: Map[String, Logic]): Double = try {
      measureFanout(DTL.fanout(circuit.values.toSet.map(DTL.materialise(_))))
    } catch {
      case e: IllegalStateException =>
        System.err.println(s"FAILED CIRCUIT $circuit")
        throw e
    }

    // BUF should really be counted a bit more...
    def measureFanout(fanout: Map[DTL, Int]): Double =
      fanout.keySet.toList.map(calc(_)).sum

    private def calc(node: DTL): Double = node match {
      case REF(_)  => 0
      case AND(es) => 1000
      case  OR(es) => 1000
      case NOT(_)  => 1
      // case BUF(_, _)  => ???
      case NOR(es) => if (es.size > 2) 1000 else 1
      case NOH(es) => 1000
      case  OH(es) => 1000
      case XOR(es) => 1000
      case XNOR(es) => 1000
      case NAND(es) => if (es.size > 2) 1000 else 1
    }
  }

  // could do the same for
  //  - CMOS https://en.wikipedia.org/wiki/CMOS
  //  - Sky130 https://github.com/google/skywater-pdk

}
