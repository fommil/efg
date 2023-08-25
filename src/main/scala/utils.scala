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

    def funzip[A1, A2](implicit f: A => (IterableOnce[A1], IterableOnce[A2])): (List[A1], List[A2]) = {
      as.foldRight((List.empty[A1], List.empty[A2])) {
        case (a, (a1s, a2s)) =>
          val (oa1, oa2) = f(a)
          (oa1.iterator.toList ++ a1s, oa2.iterator.toList ++ a2s)
      }
    }

    def funzip3[A1, A2, A3](f: A => (IterableOnce[A1], IterableOnce[A2], IterableOnce[A3])): (List[A1], List[A2], List[A3]) = {
      as.foldRight((List.empty[A1], List.empty[A2], List.empty[A3])) {
        case (a, (a1s, a2s, a3s)) =>
          val (oa1, oa2, oa3) = f(a)
          (oa1.iterator.toList ++ a1s, oa2.iterator.toList ++ a2s, oa3.iterator.toList ++ a3s)
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
