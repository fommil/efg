package logic

import scala.collection.immutable.BitSet

import fommil.util._
import internal._

import LocalRule._
import Logic._

object LogicGen {
  // self-referenced must be in a Gen.delay
  private def impl(depth: Int): Gen[Logic] = {
    val max_depth = 5
    val max_width = 4

    lazy val in: Gen[Logic] = {
      // realistic mixture of inverted circuit inputs
      val raw: Gen[Logic] = Gen.choose(0, names.length - 1).map(i => In(i, names(i)))
      Gen.oneOf(raw, raw.map(Inv(_)))
    }

    lazy val value: Gen[Logic] = if (depth == max_depth) in else impl(depth + 1)
    lazy val inv: Gen[Logic] = Gen.delay(value).map(Inv(_))

    val set: Gen[Set[Logic]] = Gen.delay(Gen.nel(value, max_width)).map(_.toSet)
    val or: Gen[Logic] = set.map(Or(_))
    val and: Gen[Logic] = set.map(And(_))

    // TODO Gen.frequency(
    //   Gen.delay(genIn) -> 1,
    //   Gen.delay(genInv) -> 3,
    //   Gen.delay(genAnd) -> 4,
    //   Gen.delay(genOr) -> 4
    // )
    Gen.oneOf(or, and, in, inv)
  }
  private val names: Array[String] = alpha_syms.map(_.toLowerCase).take(8).toArray
  lazy val gen: Gen[Logic] = impl(0)
}

class LogicTest extends Test {

  def testUnnest: Unit = Gen.prop(LogicGen.gen) { ast =>
    UnNest.perform(ast).foreach { transformed =>
      assert(transformed != ast, "rule should only return new forms")

      (0 until 16).foreach { i =>
        val in = BitSet.fromBitMask(Array(i))
        assertEquals(ast.eval(in), transformed.eval(in))
      }
    }
  }

}
