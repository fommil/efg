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

import scala.collection.immutable.ArraySeq

import mccluskey.{ Cube, Storage }

object Main {
  def main(args: Array[String]): Unit = {
    require(args.length >= 1, "an input file must be provided")
    val in = new File(args(0))
    require(in.isFile(), s"$in must exist")
    val input = Files.readString(in.toPath, UTF_8)

    val mins = jzon.Decoder[Storage].decodeJson(input) match {
      case Left(err) => throw new IllegalArgumentException(err)
      case Right(as) => as
    }

    // only need to consider one of the solutions
    val logic = mins.asLogic.head.to(ArraySeq)

    val in_names = mins.input_names.mkString(" ")
    val out_names = logic.map(_._1).mkString(" ")
    System.out.println(s"@ ${in_names} | ${out_names}")

    Cube.bitsets(mins.input_width).foreach { input =>
      val outputs = logic.map {
        case (_, channel) => channel.eval(input)
      }
      if (outputs.exists(identity)) {
        val row_input = Cube.from(input, mins.input_width)
        val row_output = Cube(outputs.map(o => Cube.Bit(Option(o))))

        System.out.println(s"${row_input.render} | ${row_output.render}")
      }
    }
  }
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain truthtable.Main tests/tableI.minsums.json\""
// End:
