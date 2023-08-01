// Implementation of "Minimization of Boolean Functions" by McCluskey, 1956
//
// Input is a file containing an ASCII truth table. Each bit is 0 or 1. Spaces
// and anything after a # are ignored. Non-empty rows must have the same number
// of columns.
//
// Input and output columns are separated by a pipe '|' character.
//
// Missing rows are treated as having 0 in the output column.
//
// TODO 'x' in input (careful about precedence, requires state)
//
// Outputs a human readable representation of the minimal sum of prime
// implicants and writes a machine readable version to disk.
package mccluskey

import java.io.File
import java.nio.charset.StandardCharsets.UTF_8
import scala.collection.immutable.BitSet
import java.nio.file.Files

object Main {
  def main(args: Array[String]): Unit = {
    require(args.length == 1, "one input file must be provided")
    val file = new File(args(0))
    require(file.isFile(), s"$file must exist")

    // construct the canonical representation
    val canon = Files.readString(file.toPath, UTF_8)
      .split("\n").toList
      .flatMap { line =>
        val row = line.split("#")(0).replace(" ", "")
        if (row.isEmpty) None
        else {
          require(row.matches("^[01]+\\|[01]+$"), s"only 0 and 1 separated by | are valid, got '$row'")
          val List(input, output) = row.split('|').toList.map(_.map { case '1' => true ; case '0' => false })
          Some((input, output))
        }
      }
      .filterNot(_._2.toList.distinct == List(false))

    require(canon.map(_._1.length).distinct.length == 1, "inputs must have the same length")
    require(canon.map(_._2.length).distinct.length == 1, "outputs must have the same length")
    require(canon.distinct.length == canon.length, "duplicates not allowed")

    require(canon.forall(_._2.length == 1), "only one output allowed") // TODO support multiple outputs

    // System.out.println(s"$canon")

    val terms = canon.zipWithIndex.map {
      case ((input, _), i) => Term(input.map(Some(_)).toArray, List(i))
    }

    System.out.println(s"${terms.mkString("  ", "\n  ", "\n")}")

    // FIXME apply boolean reduction rules, etc
  }
}

// a potential prime implicant, derived from one or more p-terms
case class Term(
  // None is McCluskey's hyphen
  bits: Array[Option[Boolean]],
  // the row indexes covered by this term
  ps: List[Int]
) {
  require(bits.nonEmpty)
  require(ps.nonEmpty)

  override def toString: String = {
    val input = new String(bits.map {
      case None => '-'
      case Some(true) => '1'
      case Some(false) => '0'
    })
    val indexes = ps.mkString("(", ", ", ")")
    s"$input $indexes"
  }
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain mccluskey.Main tests/basic.truth\""
// End:
