package logic

import internal._

import Logic._
import Hardware.DTL
import Hardware.DTL._

class DtlTest extends Test {

  val i0 = In(0)
  val i1 = In(1)
  val i2 = In(2)
  val I0 = REF(0)
  val I1 = REF(1)
  val I2 = REF(2)

  def testXOR: Unit = {
    val xor3 = Xor(i0, i1, i2)
    assertEquals(
      XOR(I0, I1, I2),
      DTL.materialise(xor3)
    )
  }

}

// Local Variables:
// scala-compile-suggestion: "sbtn Test/testOnly -- *.DtlTest.testXOR"
// End:
