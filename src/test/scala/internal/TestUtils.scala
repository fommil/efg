package internal

abstract class Test extends junit.framework.TestCase {
  final def assertEquals[A](expected: A, got: A): Unit = {
    def diff = {
      val e = expected.toString
      val g = got.toString

      if (e.size > 100 || g.size > 100) {
        var prefix = 0
        var suffix = 0
        val different = g
          .padTo(e.size, ' ')
          .zip(e.padTo(g.size, ' '))
          .dropWhile {
            case (x, y) =>
              prefix += 1
              x == y
          }
          .reverse
          .dropWhile {
            case (x, y) =>
              suffix += 1
              x == y
          }
          .reverse
        val (left, right) = different.unzip

        s"DIFF (prefix=$prefix, suffix=$suffix) '${left.mkString}' != '${right.mkString}'"
      } else s"$g != $e"
    }

    assert(expected == got, diff)
  }
}

object TestUtils {
  def getResourceAsString(res: String): String = {
    val is = getClass.getClassLoader.getResourceAsStream(res)
    try {
      val baos        = new java.io.ByteArrayOutputStream()
      val data        = Array.ofDim[Byte](2048)
      var len: Int    = 0
      def read(): Int = { len = is.read(data); len }
      while (read() != -1)
        baos.write(data, 0, len)
      baos.toString("UTF-8")
    } finally is.close()
  }
}
