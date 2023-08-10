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
// label instead of an automatically generated symbol based on the input bits,
// useful for debugging against literature based examples.
//
// Outputs a human readable representation of the minimal sum of prime
// implicants to stdout, and a machine readable version to disk if requested.
//
// The interpretation of the output is such that each + (OR) represents a
// designer's choice that, when a decision has been made, the logic gates to be
// used are an OR over each of the parts. For example 'A.C.F.(D + E)' means that
// either A.C.F.D or A.C.F.E are valid circuits. When implementing A.C.F.D we
// should implement 'A OR C OR F OR D'.
//
// It is entirely possible, especially multi-output, that some gates are subsets
// of others. It is up downstream steps to discover such subsets when
// considering optimal layouts. For example, -100 may be split into (-1--
// AND --00) where either of the gates may be reused or simply because the
// hardware implementation is only possible with 1 or 2 input gates.
//
// The Quine-McCluskey algorithm is known to break down for problems that have a
// lot of inputs, due to the number of primes. For this reason, research has
// continued in the form of "Logic minimization algorithms for VLSI synthesis"
// Brayton84, aka ESPRESSO-II, and latterly ESPRESSO-SIGNATURE. These algorithms
// use heuristic approaches to find a smaller set of sum of products that are
// highly likely to contain the globally optimal minimum.
package mccluskey

import java.io.File
import java.lang.IllegalStateException
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

import scala.collection.immutable.{ ArraySeq, TreeMap, TreeSet }
import jzon.syntax._

object Main {
  private val RowPattern = "^(@[_a-zA-Z0-9]+)?([ 01xX]+)([|][ 01xX]+)?$".r

  def main(args: Array[String]): Unit = {
    require(args.length >= 1, "an input file must be provided")
    val in = new File(args(0))
    require(in.isFile(), s"$in must exist")

    var out: File = null
    if (args.length >= 2) {
      out = new File(args(1))
    }

    val input = Files.readString(in.toPath, UTF_8)

    // TODO output the inverted outputs as well, which can be more efficient.

    val canon = canonical_representation(input)
    // System.out.println(canon.map(_._1).mkString("\n"))

    val output_length = canon.head._2.values.length

    val mins = (0 until output_length).map { i =>
      val primes = prime_implicants(canon, i)
      // System.out.println(prime_implicant_table(primes))
      val minimal = prime_sums(primes).minimise
      (minimal, minimal.expand)
    }

    // shared across all the outputs
    val symbols = mins.flatMap(_._2.gates).distinct.zip(BitsSym.alpha).toMap
    System.out.println(BitsSym.render(symbols))
    System.out.println("")

    mins.foreach {
      case (_, human) =>
        System.out.println(s"${human.render(symbols)}")
    }

    if (out ne null) {
      if (out.isFile()) out.delete()
      out.getParentFile().mkdirs()

      val lookup = symbols.toList.map(_.swap).to(TreeMap)
      val outputs = mins.toList
        .map { case (machine, _) => machine.asMinSums.map(_.map(symbols(_))) }
      val machine = MinSumsOfProducts(lookup, outputs)

      Files.writeString(out.toPath, machine.toJsonPretty, UTF_8)
    }
  }

  // construct the canonical representation (including d-terms) from the user's
  // .truth table along with each row's output Bits. If the user provided rows
  // with zero output they will be included here.
  def canonical_representation(s: String): List[(Term, Bits)] = {
    val rows = s
      .split("\n").toList
      .flatMap { line =>
        val row = line.split("#").applyOrElse(0, (_: Int) => "")
        if (row.trim.isEmpty) None
        else row match {
          case RowPattern(label_, input, output) =>
            // successful parseBits are guaranteed non-empty by the regexp
            val in = Bits.parse(input).toOption.get
            val out: Bits = {
              if (output eq null) Bits.ONE
              else Bits.parse(output.tail) match {
                case Right(bits) => bits
                case Left(err) => throw new IllegalArgumentException(err)
              }
            }
            val label =
              if (label_ ne null) label_.tail
              else if (in.values.exists(_.isEmpty)) "" // will be replaced later
              else java.lang.Integer.parseInt(in.render, 2).toString
            Some(Term(in, TreeSet(label)) -> out)
        }
      }

    require(rows.map(_._1.inputs.values.length).distinct.length == 1, "inputs must have the same length")
    require(rows.map(_._2.values.length).distinct.length == 1, "outputs must have the same length")
    require(rows.map(_._1).distinct.length == rows.map(_._1).length, "inputs must be unique")

    // expand out input dontcares into explicit rows
    val terms = rows.foldLeft(List.empty[(Term, Bits)]) {
      case (seen, row@(term, outputs)) =>
        if (term.inputs.values.forall(_.isDefined)) row :: seen
        else {
          val excluded = seen.map(_._1.inputs).toSet.filter(_.isSubsetOf(term.inputs))
          val expanded = term.inputs.values.foldLeft(List(ArraySeq.empty[Boolean])) {
            case (acc, Some(t)) => acc.map(_ :+ t)
            case (acc, None) => acc.map(_ :+ true) ++ acc.map(_ :+ false)
          }.map(bools => Bits(bools.map(Option(_))))
          val label_base = term.labels.head

          val vrows = expanded.toSet.diff(excluded).toList.map {
            case vrow =>
              val num = Integer.parseInt(vrow.render, 2).toString
              val label = if (label_base.isEmpty) num else s"${label_base}.${num}"
              Term(vrow, TreeSet(label)) -> outputs
          }
          vrows.reverse ::: seen
        }
    }.reverse

    require(terms.flatMap(_._1.labels).distinct.length == terms.length, "labels must be unique")
    terms
  }

  // calculates the unique prime implicants from the canonical representation
  // note that p-terms and d-terms (don't cares) are treated the same to get to
  // the most minimal representation, but then d-terms are filtered out since
  // they are not needed in minimisation.
  def prime_implicants(terms_outputs: List[(Term, Bits)], index: Int): List[Term] = {
    val pterms = terms_outputs.filter(_._2.values(index) == Some(true)).map(_._1)
    val dterms = terms_outputs.filter(_._2.values(index) == None).map(_._1)

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
      val merged = mergeable.map { case (a, b) => a merge b }.distinctBy(_.inputs)

      // the diff here should be using .bits as the comparison, but since new
      // terms only enter from merging it is not strictly needed. Distinct here is
      // just to avoid duplicate checks.
      val unchanged = combined diff eliminated
      (merged, unchanged)
    }

    var surface = (pterms ++ dterms, List.empty[Term])
    while (surface._1.nonEmpty) {
      surface = step(surface._1, surface._2)
    }
    val repr = surface._1 ++ surface._2

    if (dterms.isEmpty) return repr

    val dontcares = dterms.flatMap(_.labels).to(TreeSet)
    repr.flatMap { t =>
      if (t.labels.intersect(dontcares).isEmpty) Some(t)
      else {
        val t_ = t.copy(labels = t.labels diff dontcares)
        if (t_.labels.isEmpty) None
        else Some(t_)
      }
    }
  }

  // for debugging
  def prime_implicant_table(primes: List[Term]): String = {
    val b = new java.lang.StringBuffer
    val labels = primes.flatMap(_.labels).to(TreeSet)
    primes.foreach { prime =>
      b.append(prime.inputs.render)
      b.append(" ")
      labels.foreach { label =>
        b.append(if (prime.labels.contains(label)) "x" else " ")
      }
      b.append("\n")
    }
    b.toString
  }

  // this is the novel thing that McCluskey did in his paper that filled in gaps
  // in Quine52 and those that came before him (McColl, Blake, etc).
  def prime_sums(primes: List[Term]): MinSum = {
    val labels = primes.flatMap(_.labels).to(TreeSet).toList

    val logic = MinSum.And(labels.map { label =>
      val rows = primes.filter(_.labels contains label).map(t => MinSum.Leaf(t.inputs))
      assert(rows.nonEmpty)
      MinSum.Or(rows)
    })

    logic
  }

}

// input bits, None is McCluskey's hyphen.
//
// This represents a logic gate of N bits where N is equal to the number of Some
// entries. e.g. -1-0 is a 2 input gate where index 1 is true and index 3 is
// false. These can be decomposed into smaller fixed-input gates and shared
// between each other, which is a circuit design optimisation step that is not
// considered by McCluskey.
final class Bits private(
  // Array doesn't have a sensible equals, so use ArraySeq
  val values: ArraySeq[Option[Boolean]]
    // could optimise memory usage with Array(Seq)[Char] holding -1,0,1 or at
    // least just having a custom ADT for Option[Boolean].
) extends AnyVal {
  def render: String =  {
    val input = values.map {
      case None => '-'
      case Some(true) => '1'
      case Some(false) => '0'
    }
    input.mkString
  }

  def isSubsetOf(that: Bits): Boolean =
    (this.values.length == that.values.length) && {
      values.zip(that.values).forall {
        case (Some(a), Some(b)) => a == b
        case (_, None) => true
        case _ => false
      }
    }

  override def toString = render
}
object Bits {
  val ONE = Bits(ArraySeq(Some(true)))

  def apply(values: ArraySeq[Option[Boolean]]) = {
    require(values.nonEmpty)
    new Bits(values)
  }
  def parse(s: String): Either[String, Bits] = {
    val bits = s.replace(" ", "").map {
      case '1' => Some(true)
      case '0' => Some(false)
      case 'x' | 'X' | '-' => None
      case c => return Left(s"unexpected character '$c'")
    }.to(ArraySeq)
    if (bits.isEmpty) Left("unexpected empty bits")
    else Right(Bits(bits))
  }

  implicit val encoder: jzon.Encoder[Bits] = jzon.Encoder[String].contramap(_.render)
  implicit val decoder: jzon.Decoder[Bits] = jzon.Decoder[String].emap(parse(_))
}

// a symbolic (usually alphanumeric) representation of Bits that is managed
// through a scoped lookup table.
final class BitsSym private (val value: String) extends AnyVal {
  override def toString = value
}
object BitsSym {
  def apply(value: String): BitsSym = new BitsSym(value)

  implicit val ordering: Ordering[BitsSym] = new Ordering[BitsSym] {
    override def compare(a: BitsSym, b: BitsSym): Int = a.value.compareTo(b.value)
  }

  implicit val encoder: jzon.FieldEncoder[BitsSym] = jzon.FieldEncoder[String].contramap(_.value)
  implicit val decoder: jzon.FieldDecoder[BitsSym] = jzon.FieldDecoder[String].map(BitsSym(_))

  def alpha: LazyList[BitsSym] = LazyList.from(1).map { i_ =>
    val buf = new java.lang.StringBuffer
    var i = i_
    while (i > 0) {
      val rem = (i - 1) % 26
      buf.append(('A' + rem).toChar)
      i = (i - rem) / 26
    }
    BitsSym(buf.reverse.toString)
  }

  def render(symbols: Map[Bits, BitsSym]): String = {
    val pad = symbols.values.map(_.value.length).max
    symbols.toList.sortBy(_._2.value).map {
      case (bits, sym) => String.format("%-" + pad + "s", sym.value) + " = " + bits.render
    }.mkString("\n")
  }
}

// a potential prime implicant, derived from one or more p-terms or d-terms
//
// String labels are useful for debugging but this could be swapped out to be
// the Integer value of the input bits to save memory and be a bit more
// efficient.
case class Term(
  inputs: Bits,
  labels: TreeSet[String]
) {
  require(labels.nonEmpty)

  def canMerge(that: Term): Boolean = {
    val alts = inputs.values.zip(that.inputs.values).filter {
      case (oa, ob) => oa != ob
    }
    alts.lengthCompare(1) == 0
  }

  // does not check for compatibility, always guard with canMerge
  def merge(that: Term): Term = {
    val input_ = inputs.values.zip(that.inputs.values).map {
      case (Some(a), Some(b)) if a == b => Some(a)
      case _ => None
    }
    val labels_ = labels ++ that.labels
    Term(Bits(input_), labels_)
  }

  def render: String = {
    val indexes = labels.mkString("(", ", ", ")")
    s"${inputs.render} $indexes"
  }

  override def toString = render
}

sealed trait MinSum {
  import MinSum._

  final def gates: List[Bits] = this match {
    case Leaf(bits) => List(bits)
    case And(as) => as.flatMap(_.gates)
    case Or(os) => os.flatMap(_.gates)
  }

  final def render(symbols: Map[Bits, BitsSym], top: Boolean = true): String = this match {
    case Leaf(bits) => symbols.get(bits).map(_.toString).getOrElse(bits.render)
    case And(entries) => entries.map(_.render(symbols, false)).mkString(".")
    case Or(entries) =>
      val parts = entries.map(_.render(symbols, false))
      if (top) parts.mkString(" + ")
      else parts.mkString("(", " + ", ")")
  }

  override final def toString: String = render(Map.empty, false)

  // when minimised, this should succeed.
  final def asMinSums: List[List[Bits]] = this match {
    case t: Leaf => Or(List(And(List(t)))).asMinSums
    case t: And => Or(List(t)).asMinSums
    case Or(sums) => sums.map {
      case And(products) => products.map {
        case Leaf(bits) => bits
        case other => throw new IllegalStateException(other.toString)
      }
      case other => throw new IllegalStateException(other.toString)
    }
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

  // should really only accept booleans, not optional booleans.
  def eval(input: Bits): Boolean = this match {
    case Leaf(bits) => input.isSubsetOf(bits)
    case And(as) => as.forall(_.eval(input))
    case Or(os) => os.exists(_.eval(input))
  }

}
object MinSum {
  case class And(entries: List[MinSum]) extends MinSum
  case class Or(entries: List[MinSum]) extends MinSum
  case class Leaf(bits: Bits) extends MinSum
}

// the nested lists are output channel, sums, products. we could have encoded
// List[MinSum] but this restricts each output to sums of products.
case class MinSumsOfProducts(
  symbols: Map[BitsSym, Bits],
  sums_of_products: List[List[List[BitsSym]]]
)
object MinSumsOfProducts {
  implicit val encoder: jzon.Encoder[MinSumsOfProducts] = jzon.Encoder.derived
  implicit val decoder: jzon.Decoder[MinSumsOfProducts] = jzon.Decoder.derived
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain mccluskey.Main tests/tableI.truth\""
// End:
