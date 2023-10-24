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
      case AND(es) => resistor + es.size * diode
      case  OR(es) => resistor + es.size * diode
      case NOT(_)  => 2 * resistor + npn
      case BUF(_, _)  => ???
      case NOR(es) => (2 + es.size) * resistor + npn
      case NOH(es) => 2 * resistor + npn + es.size * diode
      case  OH(es) => 2 * resistor + pnp + es.size * diode
      case XOR(es) => (es.size - 1) * (3 * resistor + 2 * npn)
      case XNOR(es) => (es.size - 1) * (3 * resistor + 2 * pnp)
      case NAND(es) => 2 * resistor + es.size * diode + npn // saves a resistor
    }
  }

  //   - TODO CMOS https://en.wikipedia.org/wiki/CMOS
  //   - TODO Sky130 https://github.com/google/skywater-pdk

}
