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
import java.nio.file.Files

import scala.collection.immutable.ArraySeq

object Main {
  private val RowPattern = "^(@[_a-zA-Z0-9]+)?([ 01]+)([|][ 01]+)?$".r

  def main(args: Array[String]): Unit = {
    require(args.length == 1, "one input file must be provided")
    val file = new File(args(0))
    require(file.isFile(), s"$file must exist")
    val input = Files.readString(file.toPath, UTF_8)

    val canon = canonical_representation(input)
    val primes = prime_implicants(canon)

    System.out.println(s"${primes.mkString("  ", "\n  ", "\n")}")

    // FIXME calculate minimum sum of prime implicants
  }

  // construct the canonical representation from the user's .truth table
  def canonical_representation(s: String): List[Term] = {
    def parseBits(s: String): Seq[Boolean] = s.replace(" ", "").map {
      case '1' => true
      case '0' => false
    }

    val rows = s
      .split("\n").toList
      .flatMap { line =>
        val row = line.split("#")(0)
        if (row.trim.isEmpty) None
        else row match {
          case RowPattern(label, input, null) => Some((parseBits(input), List(true), Option(label)))
          case RowPattern(label, input, output) =>
            val out = parseBits(output.tail)
            if (out.isEmpty || out.forall(!_)) None
            else Some((parseBits(input), out, Option(label)))
        }
      }

    require(rows.map(_._1.length).distinct.length == 1, "inputs must have the same length")
    require(rows.map(_._2.length).distinct.length == 1, "outputs must have the same length")
    require(rows.distinct.length == rows.length, "duplicates not allowed")

    require(rows.forall(_._2.length == 1), "only one output allowed") // TODO support multiple outputs

    val terms = rows.zipWithIndex.map {
      case ((input, _, label_), i) =>
        val label = label_.map(_.tail).getOrElse(i.toString)
        Term(input.map(Some(_)).to(ArraySeq), List(label))
    }
    require(terms.flatMap(_.ps).distinct.length == terms.length, "labels must be unique")

    terms
  }

  // calculates the unique prime implicants from the canonical representation
  def prime_implicants(terms: List[Term]): List[Term] = {
    // performs a single sweep of the first list of terms against themselves and
    // the second list, returning newly merged terms followed by those that were
    // not affected by the merging.
    //
    // it is possible that it is more efficient to iterate based on column, rather
    // than term, but this seems conceptually easier to understand.
    def step(as: List[Term], bs: List[Term]): (List[Term], List[Term]) = {
      // assertions can be removed when we're confident that bugs have been found
      assert(as.intersect(bs).isEmpty, s"duplicate terms in intersect: $as $bs")
      assert(as.distinct.length == as.length, s"duplicate terms in a: $as")
      assert(bs.distinct.length == bs.length, s"duplicate terms in b: $bs")

      val combined = as ++ bs

      val mergeable = for {
        a <- as
        b <- combined.dropWhile(_ ne a)
        if a ne b
        if a canMerge b
      } yield (a, b)

      // we can arrive at merged results through multiple paths, but always at the
      // same step of the iteration, so we must distinct by the _.bits
      val eliminated = mergeable.flatMap { case (a, b) => List(a, b) }.distinct
      val merged = mergeable.map { case (a, b) => a merge b }.distinctBy(_.bits)

      // the diff here should be using .bits as the comparison, but since new
      // terms only enter from merging it is not strictly needed. Distinct here is
      // just to avoid duplicate checks.
      val unchanged = combined diff eliminated
      (merged, unchanged)
    }

    var surface = (terms, List.empty[Term])
    while (surface._1.nonEmpty) {
      // System.out.println(s"==== STEP ====")
      // System.out.println(s"${surface._1.mkString("  ", "\n  ", "\n")}")
      // System.out.println(s"${surface._2.mkString("  ", "\n  ", "\n")}")

      surface = step(surface._1, surface._2)
    }
    surface._1 ++ surface._2
  }

}

// a potential prime implicant, derived from one or more p-terms
case class Term(
  // input bits, None is McCluskey's hyphen
  bits: ArraySeq[Option[Boolean]],
  // the row labels included in this term
  ps: List[String]
) {
  require(bits.nonEmpty)
  require(ps.nonEmpty)

  // // if a sequence of bits matches this, then they also match that.
  // def subsetOf(that: Term): Boolean =
  //   bits.zip(that.bits).forall {
  //     case (Some(_), None) => true
  //     case (oa, ob) => oa == ob
  //   }

  def canMerge(that: Term): Boolean = {
    val alts = bits.zip(that.bits).filter {
      // case (Some(a), Some(b)) => a != b
      case (oa, ob) => oa != ob
    }
    alts.lengthCompare(1) == 0
  }

  // does not check for compatibility, always guard with canMerge
  def merge(that: Term): Term = {
    val bits_ = bits.zip(that.bits).map {
      case (Some(a), Some(b)) if a == b => Some(a)
      case _ => None
    }
    val ps_ = ps ++ that.ps
    Term(bits_, ps_)
  }

  override def toString: String = {
    val input = bits.map {
      case None => '-'
      case Some(true) => '1'
      case Some(false) => '0'
    }
    val indexes = ps.mkString("(", ", ", ")")
    s"${input.mkString} $indexes"
  }
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain mccluskey.Main tests/tableI.truth\""
// End:
