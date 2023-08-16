// Recovers a truth table from sums of products (output of McCluskey). Useful to
// generate ground truth, e.g. missing data in the McCluskey paper, or if we
// have a digital circuit design and wish to reverse engineer it to see if there
// is a more optimal representation.
//
// This is not very scalable and will probably OOM not much beyond 8 bits.
package truthtable

import java.io.File
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

import scala.collection.immutable.BitSet

import mccluskey.{ Cube, SofP }

object Main {
  def main(args: Array[String]): Unit = {
    require(args.length >= 1, "an input file must be provided")
    val in = new File(args(0))
    require(in.isFile(), s"$in must exist")
    val input = Files.readString(in.toPath, UTF_8)

    val mins = jzon.Decoder[SofP.Storage].decodeJson(input) match {
      case Left(err) => throw new IllegalArgumentException(err)
      case Right(as) => as
    }

    val input_width = mins.symbols.head._2.length
    def all_inputs = Cube.bitsets(input_width)

    val output_size = mins.sums_of_products.length
    val trues = mins.asLogic.map { out =>
      val logic = out.head // only need to consider one
      all_inputs.filter(logic.eval(_)).toSet
    }

    all_inputs.foreach { row =>
      val truth = trues.zipWithIndex.foldLeft(BitSet()) {
        case (bits, (t, i)) => if (t.contains(row)) bits + i else bits
      }
      if (truth.nonEmpty) {
        val input = Cube.from(row, input_width)
        if (output_size == 1) {
          System.out.println(input.render)
        } else {
          val output = Cube.from(truth, output_size)
          System.out.println(input.render + " | " + output.render)
        }
      }
    }
  }
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain truthtable.Main tests/tableI.minsums.json\""
// End:
