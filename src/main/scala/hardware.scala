package logic

import fommil.util._

import Logic._

object Hardware {
  // https://en.wikipedia.org/wiki/Diode_logic
  // https://en.wikipedia.org/wiki/Resistor-transistor_logic
  // https://en.wikipedia.org/wiki/Diode-transistor_logic
  //
  // Diode Logic only implements active-high AND / OR, RTL only implements INV /
  // NOR using npn transistors (and can build all other gates from there), and
  // DTL expands on both, using pnp in NOR gates.
  //
  // We also consider One Hot (i.e. intuitive multi-bit exclusive OR) based on
  // the efficient Not One Hot (NOH) implementation using a rectifier network
  // with the transistor emitter feedback.
  //
  // Old-school RTL NOR is preferred for 2 or 3 input NOR, which uses a voltage
  // divider instead of diodes.
  sealed trait DTL
  object DTL {
    case class REF(channel: Int)      extends DTL
    case class AND(entries: Set[DTL]) extends DTL { override def toString = s"""AND(${entries.mkString(", ")})"""}
    case class OR (entries: Set[DTL]) extends DTL { override def toString = s"""OR(${entries.mkString(", ")})"""}
    case class NOT(entry: DTL)        extends DTL

    // amplifier(s) to address fan-out constraints. Number required depends on
    // the fanout of the node.
    //
    // TODO an extra pass after materialise to add BUF for large fan-out
    case class BUF(entry: DTL, id: Int) extends DTL

    // voltage divider (has fan-in constraints)
    // TODO calculate the fan-in constraint in Falstad and breadboard
    case class NOR(entries: Set[DTL]) extends DTL

    // rectifier and NPN "Not One Hot". Equivalent to XNOR for 2 inputs but not any other arity.
    //
    // https://www.edn.com/perform-the-xor-xnor-function-with-a-diode-bridge-and-a-transistor/
    // https://www.electricaltechnology.org/2018/12/exclusive-or-xor-gate.html#xor-gate-using-bjt-and-diodes
    // TODO calculate the fan-in constraint in Falstad and breadboard
    case class NOH(entries: Set[DTL]) extends DTL
    // "One Hot" uses PNP, equivalent to XOR for 2 inputs.
    case class OH (entries: Set[DTL]) extends DTL

    // There are situations where it is preferable to use a transistor XOR
    // encoding when diodes are expensive or take up too much space.
    // https://hackaday.io/project/8449-hackaday-ttlers/log/150147-bipolar-xor-gate-with-only-2-transistors
    // XOR / XNOR are probably best called PARITY when extended to higher arity.
    //
    // TODO find an efficent way to implement multi-input XOR/XNOR otherwise,
    // this should be viewed as nested XOR2 / XNOR2 at the hardware.
    case class XOR(entries: Set[DTL]) extends DTL  { override def toString = s"""XOR(${entries.mkString(", ")})"""}
    case class XNOR(entries: Set[DTL]) extends DTL // ⊙

    // TODO eval to verify that the desired Logic is retained

    def materialise(logic: Logic): DTL = logic match {
      case True => impossible
      case In(i) => REF(i)

      case Inv(e) => materialise(e) match {
        case OR(es) if es.size < 4 => NOR(es)
        case XOR(es) => XNOR(es)
        case XNOR(es) => XOR(es)
        case OH(es) => NOH(es)
        case NOH(es) => OH(es)
        case other => NOT(other)
      }

      case And(es) => AND(es.map(materialise(_)))

      case e@ Or(es) =>
        val noh = e.asNOH
        lazy val oh = e.asOH
        lazy val xor = e.asXOR
        lazy val xnor = e.asXNOR
        if (noh.nonEmpty) NOH(noh.map(materialise(_)))
        else if (oh.nonEmpty) OH(oh.map(materialise(_)))
        else if (xor.nonEmpty) XOR(xor.map(materialise(_)))
        else if (xnor.nonEmpty) XNOR(xnor.map(materialise(_)))
        else OR(es.map(materialise(_)))
    }

    def fanout(circuits: Set[DTL]): Map[DTL, Int] = {
      def fanout_seq(acc: Map[DTL, Int], els: Set[DTL]) =
        els.foldLeft(acc) { case (acc_, e) => fanout_(acc_, e)}

      def fanout_(acc: Map[DTL, Int], c: DTL): Map[DTL, Int] = {
        val acc_ = acc.incr(c)
        if (acc.contains(c)) acc_
        else c match {
          case REF(_)  => acc_
          case AND(es) => fanout_seq(acc_, es)
          case  OR(es) => fanout_seq(acc_, es)
          case NOT(e)  => fanout_seq(acc_, Set(e))
          case BUF(e, _) => fanout_seq(acc_, Set(e))
          case NOR(es) => fanout_seq(acc_, es)
          case NOH(es) => fanout_seq(acc_, es)
          case  OH(es) => fanout_seq(acc_, es)
          case XOR(es) => fanout_seq(acc_, es)
          case XNOR(es) => fanout_seq(acc_, es)
        }
      }

      circuits.foldLeft(Map.empty[DTL, Int]) {
        case (acc, c) => fanout_(acc, c)
      }
    }

    object AND {
      def apply(el: DTL, els: DTL*): AND = AND(els.toSet + el)
    }
    object OR {
      def apply(el: DTL, els: DTL*): OR = OR(els.toSet + el)
    }
    object NOR {
      def apply(el: DTL, els: DTL*): NOR = NOR(els.toSet + el)
    }
    object NOH {
      def apply(el: DTL, els: DTL*): NOH = NOH(els.toSet + el)
    }
    object OH {
      def apply(el: DTL, els: DTL*): OH = OH(els.toSet + el)
    }
    object XOR {
      def apply(el: DTL, els: DTL*): XOR = XOR(els.toSet + el)
    }
    object XNOR {
      def apply(el: DTL, els: DTL*): XNOR = XNOR(els.toSet + el)
    }
  }

}
