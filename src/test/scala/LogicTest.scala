package logic

import scala.collection.immutable.BitSet

import internal._

import LocalRule._
import GlobalRule._
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

    // note we don't generate any special forms here, but maybe we should! or at
    // least generate them but convert to their core form.

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
    case Xor(entries) => Shrink.set(shrinker.shrink)(entries).map(Xor(_))
    case Xnor(entries) => Shrink.set(shrinker.shrink)(entries).map(Xnor(_))
    case OneHot(entries) => Shrink.set(shrinker.shrink)(entries).map(OneHot(_))
    case NotOneHot(entries) => Shrink.set(shrinker.shrink)(entries).map(NotOneHot(_))
    case Nand(entries) => Shrink.set(shrinker.shrink)(entries).map(Nand(_))
    case Nor(entries) => Shrink.set(shrinker.shrink)(entries).map(Nor(_))
  }
}

class LogicTest extends Test {
  // common entries...
  private val a = In(0)
  private val b = In(1)
  private val c = In(2)
  // private val d = In(3)

  def testXOR: Unit = {
    val or2 = Or(
      And(Inv(a), b),
      And(a, Inv(b)),
    )
    val xor2 = new Xor(Set(a, b))
    assertEquals(or2, xor2.asCore)
    assertEquals(Some(xor2), Xor.from(or2))

    val or3 = Or(
      And(Inv(a), Inv(b), c),
      And(Inv(a), b, Inv(c)),
      And(a, Inv(b), Inv(c)),
      And(a, b, c),
    )
    val xor3 = new Xor(Set(a, b, c))

    assertEquals(or3, xor3.asCore)
    assertEquals(Some(xor3), Xor.from(or3))

    // show that inverting odd inputs leads to the same node (different to orig)
    val nodes_odd = Set(
      new Xor(Set(Inv(a), b, c)).asCore, // 1 inv
      new Xor(Set(a, Inv(b), c)).asCore,
      new Xor(Set(a, b, Inv(c))).asCore,
      new Xor(Set(Inv(a), Inv(b), Inv(c))).asCore // 3 invs
    )
    assert(1 == nodes_odd.size,
      s"ODD (${nodes_odd.size})\n${nodes_odd.mkString("\n")}")
    assert(new Xor(Set(a, b, c)).asCore != nodes_odd.head)

    // inverting even inputs leads to the same
    val nodes_even = Set(
      new Xor(Set(a, b, c)).asCore, // norm
      new Xor(Set(Inv(a), Inv(b), c)).asCore, // 2 invs
      new Xor(Set(Inv(a), b, Inv(c))).asCore,
      new Xor(Set(a, Inv(b), Inv(c))).asCore
    )
    assert(1 == nodes_even.size,
      s"EVEN (${nodes_even.size})\n${nodes_even.mkString("\n")}")
  }

  def testXNOR: Unit = {
    val or2 = Or(
      And(Inv(a), Inv(b)),
      And(a, b),
    )
    val xnor2 = new Xnor(Set(a, b))
    assertEquals(or2, xnor2.asCore)

    val or3 = Or(
      And(Inv(a), Inv(b), Inv(c)),
      And(a, b, Inv(c)),
      And(a, Inv(b), c),
      And(Inv(a), b, c),
    )
    val xnor3 = new Xnor(Set(a, b, c))
    assertEquals(or3, xnor3.asCore)
  }

  def testOH: Unit = {
    val or3 = Or(
      And(Inv(a), Inv(b), c),
      And(Inv(a), b, Inv(c)),
      And(a, Inv(b), Inv(c)),
    )
    val oh3 = new OneHot(Set(a, b, c))
    assertEquals(or3, oh3.asCore)
    assertEquals(Some(oh3), OneHot.from(or3))
  }

  def testNOH: Unit = {
    val or3 = Or(
      And(Inv(a), Inv(b), Inv(c)),
      And(a, b, Inv(c)),
      And(a, Inv(b), c),
      And(Inv(a), b, c),
      And(a, b, c),
    )
    val noh3 = new NotOneHot(Set(a, b, c))
    assertEquals(or3, noh3.asCore)
    assertEquals(Some(noh3), NotOneHot.from(or3))
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

  def assertGlobalRule(rule: GlobalRule, ast: Logic): Unit = {
    val high_ = ast.nodes.collect { case In(i) => i }.maxOption
    if (high_.isEmpty) return // no Inputs
    val high = high_.get

    rule.perform(Set(ast)).foreach { transform =>
      val transformed = ast.replace(transform)
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

  def propGlobalRule(rule: GlobalRule) = Gen.prop(LogicGen.gen, LogicGen.shrinker) {
    ast => assertGlobalRule(rule, ast)
  }

  def testUnNest: Unit = propLocalRule(UnNest)
  // def testNest: Unit = propLocalRule(Nest)
  def testSplit: Unit = propLocalRule(Split)
  def testEliminate: Unit = propLocalRule(Eliminate)
  def testFactor: Unit = propLocalRule(Factor)
  def testDeMorgan: Unit = propLocalRule(DeMorgan)
  def testComplement: Unit = propLocalRule(Complement)
  def testExclude: Unit = propLocalRule(Complement)

  def testShared: Unit = propGlobalRule(Shared)

  // any property test that fails, no matter how simple, should be documented
  // below as a standalone test, committed along with the fix.

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

  def testSplit1: Unit = {
    val logic = Or(
      And(Inv(a), b),
      And(a, Inv(b)),
      c
    )
    val rewrites = List(
      Or(c, Xor(a, b)),
      Or(c, Xnor(Inv(a), b))
    )

    assertEquals(rewrites, Split.perform(logic))
    assertLocalRule(Split, logic)
  }

}

// Local Variables:
// scala-compile-suggestion: "sbtn Test/testOnly -- *.LogicTest.testEliminate1"
// End:
