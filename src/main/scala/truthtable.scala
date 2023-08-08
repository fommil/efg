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

import mccluskey.{ Bits, MinSumsOfProducts }
import mccluskey.MinSum._

object Main {
  def main(args: Array[String]): Unit = {
    require(args.length >= 1, "an input file must be provided")
    val in = new File(args(0))
    require(in.isFile(), s"$in must exist")
    val input = Files.readString(in.toPath, UTF_8)

    val mins = jzon.Decoder[MinSumsOfProducts].decodeJson(input) match {
      case Left(err) => throw new IllegalArgumentException(err)
      case Right(as) => as
    }

    val input_size = mins.symbols.head._2.values.length
    val all_inputs = (0 until input_size).foldLeft(List(List.empty[Option[Boolean]])) {
      case (acc, _) => acc.map(Some(true) :: _) ++ acc.map(Some(false) :: _)
    }.map(bs => Bits(bs.to(ArraySeq))).reverse

    val trues = mins.sums_of_products.map { channel =>
      // any of the sums is fine, they all evaluate to the same. when
      // evaluating, we treat each product as a combination of ORs, the dual of
      // how the minsums are actually constructed.
      val logic = Or(channel.head.map(s => Leaf(mins.symbols(s))))

      all_inputs.filter(logic.eval(_)).toSet
    }

    all_inputs.foreach { row =>
      val truth = trues.map(_.contains(row))
      if (truth.exists(identity)) {
        val input = row.render.mkString(" ")
        if (truth.lengthCompare(1) == 0) {
          System.out.println(input)
        } else {
          val output = truth.map(t => if (t) '1' else '0').mkString(" ")
          System.out.println(input + " | " + output)
        }
      }
    }
  }
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain truthtable.Main tests/tableI.minsums.json\""
// End:
