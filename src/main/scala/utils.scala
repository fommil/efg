package fommil

import java.lang.IllegalStateException

object util {
  implicit class SetOpz[A](private val as: Set[A]) extends AnyVal {
    // equivalent to a1.intersects(a2).nonEmpty
    def overlaps(that: Set[A]): Boolean = {
      as.foreach { as_ => if (that.contains(as_)) return true }
      false
    }
  }

  implicit class ListOpz[A](private val as: List[A]) extends AnyVal {
    // equivalent to a1.intersects(a2).nonEmpty
    def overlaps(a2: List[A]): Boolean = {
      as.foreach(as_ => a2.foreach(a2_ => if (as_ == a2_) return true))
      false
    }
  }

  implicit class IterableOpz[A](private val as: Iterable[A]) extends AnyVal {
    def counts: Map[A, Int] = as.foldLeft(Map.empty[A, Int]) {
      case (acc, a) => acc.updatedWith(a) {
        case Some(c) => Some(c + 1)
        case None => Some(1)
      }
    }

    // def flatUnzip3[A1, A2, A3](implicit asTriple: A => (Option[A1], Option[A2], Option[A3])): (List[A1], List[A2], List[A3]) = {
    //   as.foldRight((List.empty[A1], List.empty[A2], List.empty[A3])) {
    //     case (a, (acc1, acc2, acc3)) =>
    //       val (a1, a2, a3) = asTriple(a)
    //       val a1_ = a1 match {
    //         case None => acc1
    //         case Some(s) => s :: acc1
    //       }
    //       val a2_ = a2 match {
    //         case None => acc2
    //         case Some(s) => s :: acc2
    //       }
    //       val a3_ = a3 match {
    //         case None => acc3
    //         case Some(s) => s :: acc3
    //       }
    //       (a1_, a2_, a3_)
    //   }
    // }

    def funzip3[A1, A2, A3](f: A => (Option[A1], Option[A2], Option[A3])): (List[A1], List[A2], List[A3]) = {
      as.foldRight((List.empty[A1], List.empty[A2], List.empty[A3])) {
        case (a, (a1s, a2s, a3s)) =>
          val (oa1, oa2, oa3) = f(a)
          val a1s_ = oa1 match {
            case None => a1s
            case Some(a1) => a1 :: a1s
          }
          val a2s_ = oa2 match {
            case None => a2s
            case Some(a2) => a2 :: a2s
          }
          val a3s_ = oa3 match {
            case None => a3s
            case Some(a3) => a3 :: a3s
          }
          (a1s_, a2s_, a3s_)
      }
    }

  }

  def alpha_syms: LazyList[String] = LazyList.from(1).map { i_ =>
    val buf = new java.lang.StringBuffer
    var i = i_
    while (i > 0) {
      val rem = (i - 1) % 26
      buf.append(('A' + rem).toChar)
      i = (i - rem) / 26
    }
    buf.reverse.toString
  }

  def impossible: Nothing = throw new IllegalStateException("a dev made a mistake")
}
