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
// Outputs the minimal sum of prime implicants to stdout in JSON format.
//
// The interpretation of the output is such that each sum of products is a
// complement of the circuit that recovers the truth table. For example 'A.B.C'
// means to implement 'A OR B OR C' over the cubes A, B and C, where cubes are
// multi-input AND gates that may require their input to be inverted.
//
// The Quine-McCluskey algorithm is known to break down for problems that have a
// lot of inputs, due to the number of primes. For this reason, research has
// continued in the form of "Logic minimization algorithms for VLSI synthesis"
// Brayton84, aka ESPRESSO-II, and latterly ESPRESSO-SIGNATURE. These algorithms
// use heuristic approaches to find a smaller set of sum of products that are
// highly likely to contain the globally optimal minimum.
//
// The 2-level logic form that is output here is usually has the shortest
// critical path, since it is maximally parallel, but is woefully inefficient in
// terms of number of gates. Therefore, the next step in practical circuit
// design is typically Multilevel Logic Synthesis.
package mccluskey

import java.io.File
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

import scala.collection.immutable.{ ArraySeq, BitSet, TreeMap, TreeSet }

import jzon.syntax._
import logic.Logic

object Main {
  private val RowPattern = "^(@[_a-zA-Z0-9]+)?([ 01xX]+)([|][ 01xX]+)?$".r

  def main(args: Array[String]): Unit = {
    require(args.length == 1, "an input file must be provided")
    val in = new File(args(0))
    require(in.isFile(), s"$in must exist")

    val input = Files.readString(in.toPath, UTF_8)

    // TODO output the inverted outputs as well, which can be more efficient.

    val canon = canonical_representation(input)
    // System.out.println(canon.map(_._1).mkString("\n"))

    val output_length = canon.head._2.length

    val mins = (0 until output_length).map { i =>
      val primes = prime_implicants(canon, i)
      // System.out.println(prime_implicant_table(primes))
      prime_sums(primes).minimise
    }.toList

    // shared across all the outputs
    val out = SofP.Storage.create(mins)
    System.out.println(out.toJsonPretty)
  }

  // construct the canonical representation (including d-terms) from the user's
  // .truth table along with each row's output Cube. If the user provided rows
  // with zero output they will be included here.
  def canonical_representation(s: String): List[(Term, Cube)] = {
    val rows = s
      .split("\n").toList
      .flatMap { line =>
        val row = line.split("#").applyOrElse(0, (_: Int) => "")
        if (row.trim.isEmpty) None
        else row match {
          case RowPattern(label_, input, output) =>
            // successful parseCube are guaranteed non-empty by the regexp
            val in = Cube.parse(input).toOption.get
            val out: Cube = {
              if (output eq null) Cube.ONE
              else Cube.parse(output.tail) match {
                case Right(bits) => bits
                case Left(err) => throw new IllegalArgumentException(err)
              }
            }
            val label =
              if (label_ ne null) label_.tail
              else if (in.dterms) "" // will be replaced later
              else java.lang.Integer.parseInt(in.render, 2).toString
            Some(Term(in, TreeSet(label)) -> out)
        }
      }

    require(rows.map(_._1.inputs.length).distinct.length == 1, "inputs must have the same length")
    require(rows.map(_._2.length).distinct.length == 1, "outputs must have the same length")
    require(rows.map(_._1).distinct.length == rows.map(_._1).length, "inputs must be unique")

    // expand out input dontcares into explicit rows
    val terms = rows.foldLeft(List.empty[(Term, Cube)]) {
      case (seen, row@(term, outputs)) =>
        if (!term.inputs.dterms) row :: seen
        else {
          val excluded = seen.map(_._1.inputs).filter(_.subsetOf(term.inputs))
          val expanded = term.inputs.fill
          val label_base = term.labels.head

          val vrows = expanded.diff(excluded).map {
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
  def prime_implicants(terms_outputs: List[(Term, Cube)], index: Int): List[Term] = {
    val pterms = terms_outputs.filter(_._2.pterm(index)).map(_._1)
    val dterms = terms_outputs.filter(_._2.dterm(index)).map(_._1)

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
  def prime_sums(primes: List[Term]): PofS = {
    val labels = primes.flatMap(_.labels).to(TreeSet).toList

    val logic = PofS(labels.map { label =>
      val rows = primes.filter(_.labels contains label).map(t => t.inputs)
      assert(rows.nonEmpty)
      rows
    })

    logic
  }

}

// This may be interpreted as a multi-input AND gate where a 1 indicates that
// the input channel must be true, 0 that it must be false (inverted), and -
// that it is ignored (dontcare). Most significant bit on the left.
//
// Many research papers use the verbose x_{1}x_{3}' notation.
final class Cube private(
  // Array doesn't have a sensible equals, so use ArraySeq
  // Memory could be optimised further by using Char instead of a sealed trait
  private val values: ArraySeq[Cube.Bit]
) extends AnyVal {
  import Cube.Bit

  def length: Int = values.length

  def pterm(i: Int): Boolean = values(i) == Bit.True
  def dterm(i: Int): Boolean = values(i) == Bit.DontCare
  def dterms: Boolean = values.exists(_ == Bit.DontCare)

  // fill all the dontcare holes of this to obtain fully populated instances
  def fill: List[Cube] = {
    values.foldLeft(List(ArraySeq.empty[Bit])) {
      case (acc, Bit.DontCare) => acc.map(_ :+ Bit.True) ++ acc.map(_ :+ Bit.False)
      case (acc, other) => acc.map(_ :+ other)
    }.map(Cube(_))
  }

  def render: String =  {
    val input = values.reverse.map {
      case Bit.DontCare => '-'
      case Bit.True => '1'
      case Bit.False => '0'
    }
    input.mkString
  }

  // aka fully covered by that
  def subsetOf(that: Cube): Boolean =
    (this.values.length == that.values.length) && {
      values.zip(that.values).forall {
        case (_, Bit.DontCare) => true
        case (a, b) => a == b
      }
    }

  def canMerge(that: Cube): Boolean = {
    val alts = values.zip(that.values).filter {
      case (oa, ob) => oa != ob
    }
    alts.lengthCompare(1) == 0
  }

  // does not check for compatibility, always guard with canMerge
  def merge(that: Cube): Cube = Cube {
    values.zip(that.values).map {
      case (Bit.True, Bit.True) => Bit.True
      case (Bit.False, Bit.False) => Bit.False
      case _ => Bit.DontCare
    }
  }

  def asLogic: Logic = {
    val and = Logic.And(values.zipWithIndex.toList.flatMap {
      case (Bit.DontCare, _) => None
      case (Bit.True, i) => Some(Logic.In(i))
      case (Bit.False, i) => Some(Logic.Inv(Logic.In(i)))
    })
    if (length == 1) and.entries.head
    else and
  }

  override def toString = render
}
object Cube {
  val ONE = Cube(ArraySeq(Bit.True))

  sealed trait Bit
  object Bit {
    def apply(o: Option[Boolean]): Bit = o match {
      case Some(true) => True
      case Some(false) => False
      case None => DontCare
    }

    case object True extends Bit
    case object False extends Bit
    case object DontCare extends Bit
  }

  def apply(values: ArraySeq[Bit]): Cube = {
    require(values.nonEmpty)
    new Cube(values)
  }
  def from(bs: BitSet, width: Int): Cube = apply {
    (0 until width).map(b => Bit(Some(bs.contains(b)))).to(ArraySeq)
  }

  def parse(s: String): Either[String, Cube] = {
    val bits = s.replace(" ", "").map {
      case '1' => Bit.True
      case '0' => Bit.False
      case 'x' | 'X' | '-' => Bit.DontCare
      case c => return Left(s"unexpected character '$c'")
    }.to(ArraySeq).reverse
    if (bits.isEmpty) Left("unexpected empty bits")
    else Right(Cube(bits))
  }

  implicit val encoder: jzon.Encoder[Cube] = jzon.Encoder[String].contramap(_.render)
  implicit val decoder: jzon.Decoder[Cube] = jzon.Decoder[String].emap(parse(_))
}

// a symbolic (usually alphanumeric) representation of Cube that is managed
// through a scoped lookup table.
final class CubeSym private (val value: String) extends AnyVal {
  override def toString = value
}
object CubeSym {
  def apply(value: String): CubeSym = new CubeSym(value)

  implicit val ordering: Ordering[CubeSym] = new Ordering[CubeSym] {
    override def compare(a: CubeSym, b: CubeSym): Int = a.value.compareTo(b.value)
  }

  implicit val encoder: jzon.FieldEncoder[CubeSym] = jzon.FieldEncoder[String].contramap(_.value)
  implicit val decoder: jzon.FieldDecoder[CubeSym] = jzon.FieldDecoder[String].map(CubeSym(_))

  def alpha: LazyList[CubeSym] = LazyList.from(1).map { i_ =>
    val buf = new java.lang.StringBuffer
    var i = i_
    while (i > 0) {
      val rem = (i - 1) % 26
      buf.append(('A' + rem).toChar)
      i = (i - rem) / 26
    }
    CubeSym(buf.reverse.toString)
  }

  def render(symbols: Map[Cube, CubeSym]): String = {
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
// efficient (could use bitset in that case instead of TreeSet).
case class Term(
  inputs: Cube,
  labels: TreeSet[String]
) {
  require(labels.nonEmpty)

  def canMerge(that: Term): Boolean = inputs.canMerge(that.inputs)
  def merge(that: Term): Term = Term(inputs.merge(that.inputs), labels ++ that.labels)

  def render: String = {
    val indexes = labels.mkString("(", ", ", ")")
    s"${inputs.render} $indexes"
  }

  override def toString = render
}

// Product of Sums, i.e. 2-level logic (AND (OR ...) ... ), that can be
// minimised to a Sum of Products (OR (AND ...) ...) of the same Cubes. Note
// that although the (DeMorgan) complement is a Sum of Products it may result in
// a separate set of Cubes and is not (usually) minimal, and therefore not of
// interest here.
case class PofS (ors: List[List[Cube]]) {
  require(ors.nonEmpty)

  // There isn't enough information to define what the true minimum is. For
  // example it may be the smallest number of cubes or the least number of bit
  // comparisons (with a higher, but shared, weight applied to inversions). We
  // aggressively eliminate as many cubes as possible, branching when there is a
  // choice to be made, and hope that we end up with a very small set of minimal
  // Sums of Products that contain the true minimum.
  //
  // 1. de-dupe aggressively by idempotency: A . A = A ; A + A = A.
  //
  // 2. factor out all the single-symbol (necessary) products by commutativity
  //    and eliminate from the remainder by absorption: A . (A + B) = A.
  //
  // 3. in the remainder, find the cube(s) that appear the most, and use as the
  //    next factor, branching when there are multiple choices. Eliminate and repeat,
  //    until the remainder is empty.
  def minimise: SofP = SofP {
    // FIXME update this algorithm to match the description
    val ors_ = ors.map(_.distinct).sortBy(_.length)
    ors_.tail.foldLeft(List(ors_.head)) {
      case (acc, or) =>
        // TODO intersect is inefficient
        val overlap = acc.filter(_.intersect(or).nonEmpty)
        if (overlap.nonEmpty) overlap
        else if (acc.isEmpty) List(or)
        else or.flatMap { c => acc.map(c :: _) }
    }
  }

}

// Sum of Products (OR (AND ...) ...)
case class SofP(values: List[List[Cube]])
object SofP {
  // disk format for multi-output SofP that uses a common dictionary for the bitsets
  // the nested lists are: channel -> sum -> product -> cube
  //
  // note that the least significant output bit is index 0 i.e. the reverse of
  // the truth table ordering.
  case class Storage(
    symbols: Map[CubeSym, Cube],
    sums_of_products: List[List[List[CubeSym]]]
  )
  object Storage {
    implicit val encoder: jzon.Encoder[Storage] = jzon.Encoder.derived
    implicit val decoder: jzon.Decoder[Storage] = jzon.Decoder.derived

    def create(mins: List[SofP]): Storage = {
      val symbols = mins.flatMap(_.values.flatten).distinct.zip(CubeSym.alpha).toMap
      val lookup = symbols.map(_.swap).to(TreeMap)
      val outputs = mins.map(_.values.map(_.map(symbols(_))))
      Storage(lookup, outputs)
    }
  }
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain mccluskey.Main tests/tableI.truth\""
// End:
