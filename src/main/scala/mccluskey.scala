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

import scala.collection.immutable.{ BitSet, ListSet }

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

    val cardinality = terms.head.bits.length

    System.out.println(s"${terms.mkString("  ", "\n  ", "\n")}")

    // calculate prime implicants by applying boolean reduction rules

    val step1 = reduce_step(terms, Nil)
    val probe = step1._1 ++ step1._2

    System.out.println(s"${probe.mkString("  ", "\n  ", "\n")}")


    // go through each column
    // find combinations of Terms that can be merged

    // iterate over the new combinations, until nothing new is discovered
    // (we only need to check the surface at each stage, anything that was consumed as part of an earlier merge will not produce new primes)

    // remove everything that is a subset (but only after it has been compared with everything)

    // it feels like there might be an n-queens style search trick that would
    // allow the invalid search to be excluded.

    // FIXME apply boolean reduction rules, etc
  }

  // performs a single sweep of the first list of terms against themselves and
  // the second list, returning newly merged terms and those that were not
  // affected by the merging, separately to facilitate additional iterations.
  //
  // it is possible that it is more efficient to iterate based on column, rather
  // than term, but this seems conceptually easier to understand.
  def reduce_step(as: List[Term], bs: List[Term]): (List[Term], List[Term]) = {
    // these should be removed for efficiency later on
    assert(as.intersect(bs).isEmpty, s"duplicate terms in intersect: $as $bs")
    assert(as.distinct.length == as.length, s"duplicate terms in a: $as")
    assert(bs.distinct.length == bs.length, s"duplicate terms in b: $bs")

    val combined = as ++ bs

    val mergeable = for {
      a <- as
      b <- combined
      if a ne b
      if a canMerge b
    } yield (a, b)

    val eliminated = mergeable.flatMap { case (a, b) => List(a, b) }.distinct
    val merged = mergeable.map { case (a, b) => a merge b }
    // TODO possible that mergeable is constructed through different paths,
    // leading to dupes that we need to handle here (only appearing in _1).

    ((combined diff eliminated), merged)
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

  // if a sequence of bits matches this, then they also match that.
  def subsetOf(that: Term): Boolean =
    bits.zip(that.bits).forall {
      case (Some(_), None) => true
      case (oa, ob) => oa == ob
    }

  def canMerge(that: Term): Boolean = {
    val alts = bits.zip(that.bits).filter {
      case (Some(oa), Some(ob)) => oa != ob
      case _ => false
    }
    alts.length == 1
  }

  // does not check for compatibility, always guard with canMerge
  def merge(that: Term): Term = {
    val bits_ = bits.zip(that.bits).map {
      case (Some(oa), Some(ob)) if oa == ob => Some(oa)
      case _ => None
    }
    val ps_ = ps ++ that.ps
    Term(bits_, ps_)
  }

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
