// Implementation of "Minimization of Boolean Functions" by McCluskey, 1956
//
// Input is a file containing an ASCII truth table. Each bit is 0 or 1. Spaces
// and anything after a # are ignored. Non-empty rows must have the same number
// of columns.
//
// Input and output columns are separated by a pipe '|' character. If there is
// no pipe on a row then it will be treated as input bits with a single output
// column having value '1'.
//
// Missing rows are treated as having 0 in the output column.
//
// Rows may start with @label (followed by whitespace) which will be used as the
// label instead of an automatically generated symbol based on the row number.
// The program will halt if a generated symbol clashes with a manually provided
// one.
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
  private val RowPattern = "^(@[_a-zA-Z0-9]+)?([ 01]+)([|][ 01]+)?$".r
  private def parseBits(s: String): Seq[Boolean] = s.replace(" ", "").map {
    case '1' => true
    case '0' => false
    // protected by regexps
  }

  def main(args: Array[String]): Unit = {
    require(args.length == 1, "one input file must be provided")
    val file = new File(args(0))
    require(file.isFile(), s"$file must exist")

    // construct the canonical representation
    val canon = Files.readString(file.toPath, UTF_8)
      .split("\n").toList
      .flatMap { line =>
        val row = line.split("#")(0)
        if (row.trim.isEmpty) None
        else row match {
          case RowPattern(label, input, null) => Some((parseBits(input), List(1), Option(label)))
          case RowPattern(label, input, output) => Some((parseBits(input), parseBits(output.tail), Option(label)))
        }
      }
      .filterNot(_._2.toList.distinct == List(false))

    require(canon.map(_._1.length).distinct.length == 1, "inputs must have the same length")
    require(canon.map(_._2.length).distinct.length == 1, "outputs must have the same length")
    require(canon.distinct.length == canon.length, "duplicates not allowed")

    require(canon.forall(_._2.length == 1), "only one output allowed") // TODO support multiple outputs

    // System.out.println(s"$canon")

    val terms = canon.zipWithIndex.map {
      case ((input, _, label_), i) =>
        val label = label_.map(_.tail).getOrElse(i.toString)
        Term(input.map(Some(_)).toArray, List(label))
    }
    require(terms.flatMap(_.ps).distinct.length == terms.length, "labels must be unique")

    System.out.println(s"${terms.mkString("  ", "\n  ", "\n")}")

    // FIXME apply boolean reduction rules, etc
  }
}

// a potential prime implicant, derived from one or more p-terms
case class Term(
  // None is McCluskey's hyphen
  bits: Array[Option[Boolean]],
  // the row labels included in this term
  ps: List[String]
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
// scala-compile-suggestion: "sbt \"runMain mccluskey.Main tests/tableI.truth\""
// End:
