// Implementation of "Minimization of Boolean Functions" by McCluskey56.
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

import scala.collection.immutable.{ ArraySeq, TreeMap }

object Main {
  private val RowPattern = "^(@[_a-zA-Z0-9]+)?([ 01]+)([|][ 01]+)?$".r

  def main(args: Array[String]): Unit = {
    require(args.length == 1, "one input file must be provided")
    val file = new File(args(0))
    require(file.isFile(), s"$file must exist")
    val input = Files.readString(file.toPath, UTF_8)

    val canon = canonical_representation(input)
    val primes = prime_implicants(canon)

    // the "prime implicant table" would have columns of distinct labels; and
    // rows being the bitmask of each term (or a unique shorthand symbol). X
    // would appear in every cell where the term (row) contains the column's
    // label. But we don't need to construct the table explicitly.

    // System.out.println(s"${primes.map(_.render).mkString("  ", "\n  ", "\n")}")

    val symbols = primes.map(_.mask).zip(gen_symbols).to(TreeMap)
    System.out.println(MinSum.render(symbols))

    val logic = prime_sums(primes)
    // System.out.println(s"${logic.render(symbols)}")
    val minimal = logic.minimise
    // System.out.println(s"${minimal.render(symbols)}")
    val expanded = minimal.expand
    System.out.println(s"${expanded.render(symbols)}")
  }

  def gen_symbols: LazyList[String] = LazyList.from(1).map { i_ =>
    val buf = new java.lang.StringBuffer
    var i = i_
    while (i > 0) {
      val rem = (i - 1) % 26
      buf.append(('A' + rem).toChar)
      i = (i - rem) / 26
    }
    buf.reverse.toString
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
    require(terms.flatMap(_.labels).distinct.length == terms.length, "labels must be unique")

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
      surface = step(surface._1, surface._2)
    }
    surface._1 ++ surface._2
  }

  // this is the novel thing that McCluskey did in his paper that filled in gaps
  // in Quine52 and those that came before him (McColl, Blake, etc).
  def prime_sums(primes: List[Term]): MinSum = {
    val labels = primes.flatMap(_.labels).distinct.sorted

    val logic = MinSum.And(labels.map { label =>
      val rows = primes.filter(_ contains label).map(MinSum.Leaf(_))
      assert(rows.nonEmpty)
      MinSum.Or(rows)
    })

    logic
  }

}

// a potential prime implicant, derived from one or more p-terms
case class Term(
  // input bits, None is McCluskey's hyphen
  bits: ArraySeq[Option[Boolean]],
  // the row labels included in this term
  labels: List[String]
) {
  require(bits.nonEmpty)
  require(labels.nonEmpty)

  // is it worth optimising with a Set[String] lookup?
  def contains(label: String): Boolean = labels.contains(label)

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
    val labels_ = labels ++ that.labels
    Term(bits_, labels_)
  }

  val mask: String =  {
    val input = bits.map {
      case None => '-'
      case Some(true) => '1'
      case Some(false) => '0'
    }
    input.mkString
  }

  def render: String = {
    val indexes = labels.mkString("(", ", ", ")")
    s"$mask $indexes"
  }

  override def toString = render
}

sealed trait MinSum {
  import MinSum._

  final def render(symbols: Map[String, String], top: Boolean = true): String = this match {
    case Leaf(term) => symbols.getOrElse(term.mask, term.mask)
    case And(entries) => entries.map(_.render(symbols, false)).mkString(".")
    case Or(entries) =>
      val parts = entries.map(_.render(symbols, false))
      if (top) parts.mkString(" + ")
      else parts.mkString("(", " + ", ")")
  }

  // Reduces the boolean statement to a minimal form by applying boolean laws
  // without complements (i.e. DeMorgan's law is ignored).
  //
  // Iteration may be needed beyond 2-level logic.
  //
  // This is probably incredibly inefficient.
  final def minimise: MinSum = this match {
    case _: Leaf => this
    case And(entries) =>
      val (leafs, ors) = {
        // unnest, by associativity
        // A . (B . C) = A . B . C
        // and extract all the top-level terms, rearranging by commutativity
        // A . B = B . A
        var leafs: List[Leaf] = Nil
        var ors: List[Or] = Nil
        def extract(entry: MinSum): Unit = entry.minimise match {
          case t: Leaf => leafs ::= t
          case And(es) => es.foreach(extract)
          case or: Or => ors ::= or
        }
        entries.foreach(extract)
        // remove dupes by idempotency
        // A . A = A
        // A + A = A
        (leafs.distinct, ors.distinct)
      }

      // expand so that OR is on the top, and eliminate
      def expand(factors: List[MinSum], ors: List[Or]): List[MinSum] = ors match {
        case Nil => factors match {
          case List(factor) => List(factor)
          case _ => List(And(factors))
        }
        case head :: tail =>
          if (factors.intersect(head.entries).nonEmpty) {
            // absorption
            // A . (A + B) = A
            expand(factors, tail)
          } else {
            // distribution
            // A . (B + C) = (A . B) + (A . C)
            head.entries.flatMap { e =>
              expand(e :: factors, tail)
            }
          }
      }

      expand(leafs, ors) match {
        case List(entry) => entry
        case es => Or(es).minimise // inefficient, repeats a lot of work
      }

    case Or(entries) =>
      // unnest by associativity
      // A + (B + C) = (A + B) + C
      // and dedupe by idempotentcy
      // A + A = A
      val tops = entries.map(_.minimise).flatMap {
        case Or(es) => es
        case e => List(e)
      }.distinct // List[And | Leaf]

      // reduce with absorption
      // A + (A . B) = A
      val reduced = tops.filter { e =>
        !tops.exists { t =>
          e != t && t.products.subsetOf(e.products)
        }
      }

      reduced match {
        case List(entry) => entry
        case es => Or(es)
      }
  }

  // assumes this his been minimised, the AND equivalent products
  private[MinSum] lazy val products: Set[MinSum] = this match {
    case e: Leaf => Set(e)
    case And(es) => es.toSet
    case _ => Set.empty
  }

  // for human (qualitative) consumption of a call to minimise.
  def expand: MinSum = this match {
    case Or(entries) =>
      // pick the candidate with the most common counts and factor
      val candidate = entries.flatMap(_.products).distinct.map { c =>
        c -> entries.count(_.products.contains(c))
      }.maxBy(_._2)
      if (candidate._2 < 2) return this
      val factor = candidate._1

      val (common_, uncommon) = entries.partitionMap {
        case e@ And(es) if e != factor & e.products.contains(factor) =>
          Left(And(es.filter(_ != factor)))
        case e =>
          Right(e)
      }

      // in an ideal world we'd return Or(common ++ Or(uncommon).expand) but
      // there are edge cases that need to be simplified or the output is messy.
      val common = (factor, Or(common_).expand) match {
        case (And(as), And(bs)) => And(as ++ bs)
        case (a, b) => And(a :: b :: Nil)
      }
      if (uncommon.isEmpty) common
      else Or(uncommon).expand match {
        case Or(bs) => Or(common :: bs)
        case bs => Or(common :: bs :: Nil)
      }

    case _ => this
  }

}
object MinSum {
  case class And(entries: List[MinSum]) extends MinSum
  case class Or(entries: List[MinSum]) extends MinSum
  case class Leaf(term: Term) extends MinSum

  def render(symbols: Map[String, String]): String = {
    val pad = symbols.values.map(_.length).max
    symbols.toList.sortBy(_._2).map {
      case (bits, sym) => String.format("%-" + pad + "s", sym) + " = " + bits
    }.mkString("\n")
  }
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain mccluskey.Main tests/tableI.truth\""
// End:
