package logic

import scala.collection.immutable.BitSet

import internal._

import LocalRule._
import Logic._

object LogicGen {
  // self-referenced must be in a Gen.delay
  private def impl(depth: Int): Gen[Logic] = {
    val max_inputs = 4
    val max_depth = 4
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

  def testXOR: Unit = {
    val node2 = Or(
      And(Inv(In(0)), In(1)),
      And(In(0), Inv(In(1))),
    )
    assertEquals(Set(In(0), In(1)), node2.asXOR)

    val node3 = Or(
      And(Inv(In(0)), Inv(In(1)), In(2)),
      And(Inv(In(0)), In(1), Inv(In(2))),
      And(In(0), Inv(In(1)), Inv(In(2))),
      And(In(0), In(1), In(2)),
    )
    assertEquals(Set(In(0), In(1), In(2)), node3.asXOR)
  }

  def testXNOR: Unit = {
    val node2 = Or(
      And(Inv(In(0)), Inv(In(1))),
      And(In(0), In(1)),
    )
    assertEquals(Set(In(0), In(1)), node2.asXNOR)

    val node3 = Or(
      And(Inv(In(0)), Inv(In(1)), Inv(In(2))),
      And(In(0), In(1), Inv(In(2))),
      And(In(0), Inv(In(1)), In(2)),
      And(Inv(In(0)), In(1), In(2)),
    )
    assertEquals(Set(In(0), In(1), In(2)), node3.asXNOR)
  }

  def testOH: Unit = {
    val node2 = Or(
      And(Inv(In(0)), In(1)),
      And(In(0), Inv(In(1))),
    )
    assertEquals(Set(In(0), In(1)), node2.asOH)

    val node3 = Or(
      And(Inv(In(0)), Inv(In(1)), In(2)),
      And(Inv(In(0)), In(1), Inv(In(2))),
      And(In(0), Inv(In(1)), Inv(In(2))),
    )
    assertEquals(Set(In(0), In(1), In(2)), node3.asOH)
  }

  def testNOH: Unit = {
    val node2 = Or(
      And(Inv(In(0)), Inv(In(1))),
      And(In(0), In(1)),
    )
    assertEquals(Set(In(0), In(1)), node2.asNOH)

    val node3 = Or(
      And(Inv(In(0)), Inv(In(1)), Inv(In(2))),
      And(In(0), In(1), Inv(In(2))),
      And(In(0), Inv(In(1)), In(2)),
      And(Inv(In(0)), In(1), In(2)),
      And(In(0), In(1), In(2)),
    )
    assertEquals(Set(In(0), In(1), In(2)), node3.asNOH)
  }

  def assertLocalRule(rule: LocalRule, ast: Logic): Unit = {
    val high_ = ast.nodes.collect { case In(i) => i }.maxOption
    if (high_.isEmpty) return // no Inputs
    val high = high_.get

    rule.perform(ast).foreach { transformed =>
      assert(transformed != ast, "should only return new forms")
      (0 until 1 << high).foreach { i =>
        val in = BitSet.fromBitMask(Array(i))
        val expected = ast.eval(in)
        val got = transformed.eval(in)
        lazy val in_ = (0 to high).map(in(_)).mkString(",")
        assert(expected == got, s"\nORIG  = $ast\nTRANS = $transformed\nIN    = ${in_} ($expected, $got) ")
      }
    }
  }

  /////////////////
  // PROPERTY TESTS

  def propLocalRule(rule: LocalRule) = Gen.prop(LogicGen.gen, LogicGen.shrinker) {
    ast => assertLocalRule(rule, ast)
  }

  def testUnNest: Unit = propLocalRule(UnNest)
  // def testNest: Unit = propLocalRule(Nest)
  def testSplit: Unit = propLocalRule(Split)
  def testEliminate: Unit = propLocalRule(Eliminate)
  def testFactor: Unit = propLocalRule(Factor)
  def testDeMorgan: Unit = propLocalRule(DeMorgan)
  def testXclude: Unit = propLocalRule(Xclude)

  // any property test that fails, no matter how simple, should be documented
  // below as a standalone test, committed along with the fix.

  // common entries...
  private val a = In(0)
  private val b = In(1)
  private val c = In(2)
  // private val d = In(3)

  // a·(a + b)
  def testEliminate1: Unit = {
    val logic = And(a, Or(a, b))
    assertEquals(a, Eliminate.eliminate(logic))
    assertLocalRule(Eliminate, logic)
  }

  // (a·b + a)
  def testEliminate2: Unit = {
    val logic = Or(And(a, b), a)
    assertEquals(a, Eliminate.eliminate(logic))
    assertLocalRule(Eliminate, logic)
  }

  // a.(b + (a + b).(a + c))
  def testEliminate3: Unit = {
    val logic = And(a, Or(b, And(Or(a, b), Or(a, c))))
    assertEquals(a, Eliminate.eliminate(logic))
    assertLocalRule(Eliminate, logic)
  }

  // (a + b) . (a + c) is untouched (i.e. don't try to UnFactor)
  def testEliminate4: Unit = {
    val logic = And(Or(a, b), Or(a, c))
    assertEquals(logic, Eliminate.eliminate(logic))
    assertLocalRule(Eliminate, logic)
  }

  // (a·b)'·((a·b') + (a'·b))' + (a.b') + (a'.b)
  // checks to make sure that (false + false)' evaluates to true
  def testEliminate5: Unit = {
    val logic = Or(
      And(
        Inv(And(a, b)),
        Inv(Or(And(a, Inv(b)), And(Inv(a), b)))
      ),
      And(a, Inv(b)),
      And(Inv(a), b)
    )

    assertLocalRule(Eliminate, logic)
  }

  // (a + b + c) should not try to nest
  def testNest1: Unit = assertLocalRule(Nest, Or(a, b, c))

  // a + b = a.b' + a'.b + a.b
  def testXclude1: Unit = {
    val or = Or(a, b)
    val xor = Or(Xor(a, b), And(a, b))
    assertEquals(List(xor), Xclude.perform(or))
    assertLocalRule(Xclude, or)
  }

  // a.b + a.c + b.c should find partial factors
  def testFactor1: Unit = {
    val logic = Or(And(a, b), And(a, c), And(b, c))

    assertEquals(
      Set(
        Or(And(a, Or(b, c)), And(b, c)),
        Or(And(b, Or(a, c)), And(a, c)),
        Or(And(c, Or(a, b)), And(a, b))
      ),
      Factor.perform(logic).toSet
    )

    assertLocalRule(Factor, logic)
  }

  // b + (a.b')
  def testFactor2: Unit = {
    val logic = Or(b, And(a, Inv(b)))

    assertLocalRule(Factor, logic)
  }

  // (a·c) + (a + b)
  def testFactor3: Unit = {
    val logic = Or(And(a, c), Or(a, b))

    assertLocalRule(Factor, logic)
  }

}

// Local Variables:
// scala-compile-suggestion: "sbtn Test/testOnly -- *.LogicTest.testEliminate1"
// End:
