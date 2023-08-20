// Implementation of "Minimization of Boolean Functions" by McCluskey56.
//
// Input is a file containing an ASCII truth table. Each bit is 0 or 1. Spaces
// and anything after a # are ignored. Non-empty rows must have the same number
// of columns.
//
// In and out columns are separated by a pipe '|' character. If there is no pipe
// on a row then it will be treated as input bits with a single output column
// having value '1'.
//
// Missing rows are treated as having 0 in the output column.
//
// Outputs the minimal sum of prime implicants to stdout in JSON format, along
// with the mimimal sum of prime implicants for the inverted output (which can
// sometimes be more efficient).
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
// The 2-level logic form that is output usually has the shortest critical path
// (for the AND/OR logic step, not counting inversion), since it is maximally
// parallel, but is woefully inefficient in terms of number of gates. Therefore,
// the next step in practical circuit design is typically Multilevel Logic
// Synthesis.
//
// TODO characteristic functions for multi-output logic tables
package mccluskey

import java.io.File
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

import scala.collection.immutable.{ ArraySeq, BitSet, ListMap }

import fommil.util._
import jzon.syntax._
import logic.Logic

object Main {
  private val RowPattern = "^([ 01xX]+)([|][ 01xX]+)?$".r

  def main(args: Array[String]): Unit = {
    require(args.length == 1, "an input file must be provided")
    val in = new File(args(0))
    require(in.isFile(), s"$in must exist")

    val input = Files.readString(in.toPath, UTF_8)

    val (input_width, canon) = canonical_representation(input)
    // System.out.println(input_width)
    // System.out.println(canon.map(_._1).mkString("\n"))
    val output_width = canon.head._2.length

    val canon_lookup = canon.toMap
    val inverse = Cube.bitsets(input_width).flatMap { bs =>
      // invert all the outputs, don't include zeros, keep dterms
      canon_lookup.get(bs) match {
        case Some(output) =>
          val out = output.invert
          if (out.zero) None else Some(bs -> out)
        case None =>
          val out = Cube.ones(output_width)
          Some(bs -> out)
      }
    }.toList

    val (mins, mins_inv) = (0 until output_width).map { i =>
      val primes = prime_implicants(canon, i, input_width)
      val iprimes = prime_implicants(inverse, i, input_width)
      (prime_sums(primes).minimise, prime_sums(iprimes).minimise)
    }.toList.unzip

    // shared across all the outputs
    val out = SofP.Storage.create(input_width, mins, mins_inv)
    System.out.println(out.toJsonPretty)
  }

  // construct the canonical representation (including d-terms) from the user's
  // .truth table along with each row's output Cube. If the user provided rows
  // with zero output they will be included here.
  def canonical_representation(s: String): (Int, List[(BitSet, Cube)]) = {
    val rows = s
      .split("\n").toList
      .flatMap { line =>
        val row = line.split("#").applyOrElse(0, (_: Int) => "")
        if (row.trim.isEmpty) None
        else row match {
          case RowPattern(input, output) =>
            // successful parseCube are guaranteed non-empty by the regexp
            val in = Cube.parse(input).toOption.get
            val out: Cube = {
              if (output eq null) Cube.ones(1)
              else Cube.parse(output.tail) match {
                case Right(bits) => bits
                case Left(err) => throw new IllegalArgumentException(err)
              }
            }
            Some(in -> out)
        }
      }

    require(rows.map(_._1.length).distinct.length == 1, "inputs must have the same length")
    require(rows.map(_._2.length).distinct.length == 1, "outputs must have the same length")
    require(rows.map(_._1).distinct.length == rows.map(_._1).length, "inputs must be unique")

    // expand input dontcares into explicit bitsets, which is ordering dependent
    val terms = rows.foldLeft(List.empty[(BitSet, Cube)]) {
      case (acc, (input, output)) =>
        input.toBitSet match {
          case Some(bs) => (bs, output) :: acc
          case None =>
            val excluded = acc.map(_._1)
            val vrows = input.fill.diff(excluded).map(_ -> output)
            // zero values must be retained to restrict later dontcares
            vrows ::: acc
        }
    }
    assert(terms.map(_._1).distinct.length == terms.length, "labels must be unique")

    // bitsets don't hold their width, so we have to provide it explicitly.
    // we could return cubes for inputs, but that doesn't capture the density.
    (rows.head._1.length, terms)
  }

  // calculates the unique prime implicants from the canonical representation
  // note that p-terms and d-terms (don't cares) are treated the same to get to
  // the most minimal representation, but then d-terms are filtered out since
  // they are not needed in minimisation.
  def prime_implicants(rows: List[(BitSet, Cube)], index: Int, input_width: Int): List[Term] = {
    val rows_ = rows.map {
      case (row, out) => Term(Cube.from(row, input_width), Set(row)) -> out
    }

    val pterms = rows_.filter(_._2.pterm(index)).map(_._1)
    val dterms = rows_.filter(_._2.dterm(index)).map(_._1)

    // performs a single sweep of the first list of terms against themselves and
    // the second list, returning newly merged terms followed by those that were
    // not affected by the merging.
    //
    // it is possible that it is more efficient to iterate based on column, rather
    // than term, but this seems conceptually easier to understand.
    def step(as: List[Term], bs: List[Term]): (List[Term], List[Term]) = {
      // assertions can be removed when we're confident that bugs have been found
      assert(!as.overlaps(bs), s"duplicate terms in intersect: $as $bs")
      assert(as.distinct.length == as.length, s"duplicate terms in a: $as")
      assert(bs.distinct.length == bs.length, s"duplicate terms in b: $bs")

      val combined = as ++ bs

      val mergeable = for {
        a <- as
        b <- combined.dropWhile(_ ne a)
        if a ne b
        if a canMerge b
      } yield (a, b)

      // we can arrive at merged results through multiple paths, but always at
      // the same step of the iteration, so we must distinct by the input bits.
      val eliminated = mergeable.flatMap { case (a, b) => List(a, b) }.distinct
      val merged = mergeable.map { case (a, b) => a merge b }.distinctBy(_.inputs)

      // the diff here should be using .bits as the comparison, but since new
      // terms only enter from merging it is not strictly needed.
      val unchanged = combined diff eliminated
      (merged, unchanged)
    }

    var surface = (pterms ++ dterms, List.empty[Term])
    while (surface._1.nonEmpty) {
      surface = step(surface._1, surface._2)
    }
    val repr = surface._1 ++ surface._2

    if (dterms.isEmpty) return repr

    val dontcares = dterms.flatMap(_.labels).toSet
    repr.flatMap { t =>
      if (!t.labels.overlaps(dontcares)) Some(t)
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
    val labels = primes.flatMap(_.labels).toSet
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
    val labels = primes.flatMap(_.labels).toSet
    PofS(labels.map { label =>
      primes.filter(_.labels contains label).map(t => t.inputs).toSet
    })
  }

}

// This may be interpreted as a multi-input AND gate where a 1 indicates that
// the input channel must be true, 0 that it must be false (inverted), and -
// that it is ignored (dontcare). Most significant bit on the left.
//
// Many research papers use the verbose x_{1}x_{3}' notation.
final class Cube private(
  // Array doesn't have a sensible equals, so use ArraySeq. Memory could be
  // optimised further by using two BitSets (pterms, dterms) and a width (since
  // Scala's BitSet is unbounded).
  private val values: ArraySeq[Cube.Bit]
) extends AnyVal {
  import Cube.Bit

  def length: Int = values.length

  def pterm(i: Int): Boolean = values(i) == Bit.True
  def dterm(i: Int): Boolean = values(i) == Bit.DontCare

  def pterms: Int = values.count(_ != Bit.DontCare)
  def dterms: Boolean = values.exists(_ == Bit.DontCare)

  def zterms: Seq[Int] = values.zipWithIndex.filter(_._1 == Bit.False).map(_._2)

  // fill all the dontcare holes of this to obtain fully populated BitSets
  def fill: List[BitSet] = {
    values.foldLeft(List(ArraySeq.empty[Cube.Bit])) {
      case (acc, Bit.DontCare) => acc.map(_ :+ Bit.True) ++ acc.map(_ :+ Bit.False)
      case (acc, other) => acc.map(_ :+ other)
    }
  }.flatMap(Cube(_).toBitSet)

  def invert: Cube = Cube(values.map {
    case Bit.DontCare => Bit.DontCare
    case Bit.True => Bit.False
    case Bit.False => Bit.True
  })

  def zero: Boolean = values.forall(_ == Bit.False)

  def render: String =  {
    val input = values.reverse.map {
      case Bit.DontCare => '-'
      case Bit.True => '1'
      case Bit.False => '0'
    }
    input.mkString
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

  def toBitSet: Option[BitSet] = if (dterms) None else Some {
    values.zipWithIndex.foldLeft(BitSet.empty) {
      case (acc, (v, i)) => if (v == Bit.True) acc + i else acc
    }
  }

  def asLogic: Logic = Logic.And {
    values.zipWithIndex.flatMap {
      case (Bit.DontCare, _) => None
      case (Bit.True, i) => Some(Logic.In(i))
      case (Bit.False, i) => Some(Logic.Inv(Logic.In(i)))
    }.toSet
  }

  override def toString = render
}
object Cube {
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

  def ones(width: Int): Cube = Cube(ArraySeq.fill(width)(Bit.True))

  def all(width: Int): Seq[Cube] = bitsets(width).map(bs => from(bs, width))
  def bitsets(width: Int): Seq[BitSet] = (0 until (1 << width)).map(bits => BitSet.fromBitMaskNoCopy(Array(bits)))

  // very simple cost function roughly the BJT transistor count in a direct
  // implementation of this as 2-level logic with inverter sharing.
  def cost(cubes: Set[Cube]): Int = {
    val or = if (cubes.size == 1) 0 else cubes.size
    val ands = cubes.map(c => if (c.pterms == 1) 0 else c.pterms).sum
    val invs = cubes.flatMap(_.zterms).size
    or + ands + invs
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

  def alpha: LazyList[CubeSym] = alpha_syms.map(CubeSym(_))

  def render(symbols: Map[Cube, CubeSym]): String = {
    val pad = symbols.values.map(_.value.length).max
    symbols.toList.sortBy(_._2.value).map {
      case (bits, sym) => String.format("%-" + pad + "s", sym.value) + " = " + bits.render
    }.mkString("\n")
  }
}

// a potential prime implicant, derived from one or more p-terms or d-terms
case class Term(
  inputs: Cube,
  labels: Set[BitSet] // or a set of indexes, however you prefer
) {
  require(labels.nonEmpty)

  def canMerge(that: Term): Boolean = inputs.canMerge(that.inputs)
  def merge(that: Term): Term = Term(inputs.merge(that.inputs), labels ++ that.labels)

  def render: String = {
    val indexes = labels.map(_.toBitMask.head).mkString("(", ",", ")")
    s"${inputs.render} $indexes"
  }

  override def toString = render
}

// Product of Sums, i.e. 2-level logic (AND (OR ...) ... ), that can be
// minimised to a Sum of Products (OR (AND ...) ...) of the same Cubes. Note
// that although the (DeMorgan) complement is a Sum of Products it may result in
// a separate set of Cubes and is not (usually) minimal, and therefore not of
// interest here.
case class PofS(ors: Set[Set[Cube]]) {
  require(ors.nonEmpty)
  require(ors.forall(_.nonEmpty))

  def minimise: SofP = SofP {
    def rec(factors: Set[Cube], remain: Set[Set[Cube]]): Set[Set[Cube]] = {
      val others = remain.filter(ss => !ss.overlaps(factors))
      if (others.isEmpty) Set(factors)
      else others.head.flatMap { c =>
        // it is possible to apply a greedy heuristic to find the factor that
        // appears the most, but it is possible to miss the true minimum.
        rec(factors + c, others.tail)
      }
    }

    val (nfactors, nremain) = ors.partitionMap {
      cs: Set[Cube] => if (cs.size == 1) Left(cs.head) else Right(cs)
    }
    val results = rec(nfactors, nremain)
    results.filterNot(res => results.exists(t => (t ne res) && t.subsetOf(res)) )
  }

}

// Sum of Products (OR (AND ...) ...)
case class SofP(values: Set[Set[Cube]]) {
  // we also take the liberty of ordering the output by the minimal cost
  // function to increase the likelihood that downstream consumers can get
  // decent results by truncation.
  def symbolic(lookup: Map[Cube, CubeSym]): List[List[CubeSym]] =
    values.toList.sortBy(Cube.cost(_)).map(_.toList.sortBy(_.render).map(lookup(_)))
}
object SofP {
  // disk format for multi-output SofP that uses a common dictionary for the bitsets
  // the nested lists are: channel -> sum -> product -> cube
  //
  // note that the least significant output bit is index 0 i.e. the reverse of
  // the truth table ordering.
  case class Storage(
    input_width: Int,
    // input_names: List[String],
    output_width: Int,
    // output_names: List[String],
    symbols: Map[CubeSym, Cube],
    // dterms: List[List[Cube]],
    sums_of_products: List[List[List[CubeSym]]],
    sums_of_products_inv: List[List[List[CubeSym]]],
  ) {
    require(sums_of_products.length == sums_of_products_inv.length)

    // each channel provides a list of candidate logics
    def asLogic: List[List[Logic]] = (sums_of_products.zip(sums_of_products_inv)).map {
      case (out, iout) =>
        def conv(soln: List[CubeSym]): Logic = {
          Logic.Or(soln.map { c => symbols(c).asLogic }.toSet)
        }
        out.map(conv(_)) ++ iout.map(s => Logic.Inv(conv(s)))
    }
  }
  object Storage {
    implicit val encoder: jzon.Encoder[Storage] = jzon.Encoder.derived
    implicit val decoder: jzon.Decoder[Storage] = jzon.Decoder.derived

    def create(
      input_width: Int,
      mins: List[SofP],
      mins_inv: List[SofP]
    ): Storage = {
      val symbols_ = (mins ++ mins_inv)
        .flatMap(_.values.flatten)
        .distinct
        .sortBy(_.render)
        .zip(CubeSym.alpha)
      val symbols = symbols_.toMap
      val lookup = symbols_.map(_.swap).to(ListMap)

      Storage(
        input_width,
        mins.length,
        lookup,
        mins.map(_.symbolic(symbols)),
        mins_inv.map(_.symbolic(symbols))
      )
    }
  }
}

// Local Variables:
// scala-compile-suggestion: "sbt \"runMain mccluskey.Main tests/tableI.truth\""
// End:
