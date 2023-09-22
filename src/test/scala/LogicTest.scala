package logic

import scala.collection.immutable.BitSet

import internal._

import LocalRule._
import Logic._

object LogicGen {
  // self-referenced must be in a Gen.delay
  private def impl(depth: Int): Gen[Logic] = {
    val max_inputs = 8
    val max_depth = 5
    val max_width = 4

    lazy val in: Gen[Logic] = {
      // realistic mixture of inverted circuit inputs
      val raw: Gen[Logic] = Gen.choose(0, max_inputs - 1).map(i => In(i))
      Gen.oneOf(raw, raw.map(Inv(_)))
    }

    lazy val value: Gen[Logic] = if (depth == max_depth) in else impl(depth + 1)
    lazy val inv: Gen[Logic] = Gen.delay(value).map(Inv(_))

    val set: Gen[Set[Logic]] = Gen.delay(Gen.nel(value, max_width)).map(_.toSet)
    val or: Gen[Logic] = set.map(Or(_))
    val and: Gen[Logic] = set.map(And(_))

    Gen.frequency(
      Gen.delay(in) -> 1,
      Gen.delay(inv) -> 3,
      Gen.delay(and) -> 4,
      Gen.delay(or) -> 4
    )
  }
  lazy val gen: Gen[Logic] = impl(0)

  lazy val shrinker: Shrink[Logic] = Shrink {
    case True => Nil
    case _: In => Nil
    case Inv(e) => e :: Nil
    case And(entries) => Shrink.set(shrinker.shrink)(entries).map(And(_))
    case Or(entries) => Shrink.set(shrinker.shrink)(entries).map(Or(_))
  }
}

class LogicTest extends Test {

  def assertLocalRule(rule: LocalRule, ast: Logic): Unit =
    rule.perform(ast).foreach { transformed =>
      assert(transformed != ast, "should only return new forms")

      (0 until 16).foreach { i =>
        val in = BitSet.fromBitMask(Array(i))
        assertEquals(ast.eval(in), transformed.eval(in))
      }
    }

  def propLocalRule(rule: LocalRule) = Gen.prop(LogicGen.gen, LogicGen.shrinker) {
    ast => assertLocalRule(rule, ast)
  }

  def testUnNest: Unit = propLocalRule(UnNest)
  def testNest: Unit = propLocalRule(Nest)
  def testSplit: Unit = propLocalRule(Split)
  def testEliminate: Unit = propLocalRule(Eliminate)
  def testFactor: Unit = propLocalRule(Factor)
  def testDeMorgan: Unit = propLocalRule(DeMorgan)

  // any property test that fails, no matter how simple, should be documented
  // below as a standalone test, committed along with the fix.

  // common entries...
  private val a = In(0)
  private val b = In(1)
  private val c = In(2)

  // a·(a + b)
  def testEliminate1: Unit = assertLocalRule(Eliminate, And(a, Or(a, b)))

  // (a·b + a)
  def testEliminate2: Unit = assertLocalRule(Eliminate, Or(And(a, b), a))

  // (a + b + c) should not try to nest
  def testNest1: Unit = assertLocalRule(Nest, Or(a, b, c))
}

// Local Variables:
// scala-compile-suggestion: "sbtn Test/testOnly -- *.LogicTest.testEliminate1"
// End:
