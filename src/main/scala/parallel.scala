// YOLO to Effects and actors.
//
// The caller chooses the executor they want for parallel work. Be really
// careful about deadlocks, basically never use a pool that your caller is using
// to invoke you.
package fommil.parallel

import java.util.concurrent._

import scala.util.control.NonFatal

abstract class Loop(val name: String) extends Thread(name) {
  setDaemon(true)

  @volatile protected var cancelled = false
  @volatile protected var cancelling = false

  def isCancelled(): Boolean = cancelled
  def cancel(): Unit = { cancelling = true }

  def startup_hook(): Unit = ()

  override def run(): Unit = try {
    startup_hook()
    while (!cancelling) loop()
    cancelled = true
  } catch {
    case NonFatal(t) =>
      t.printStackTrace
      System.err.println(s"[ERROR] exception in thread: $t")
  }

  def loop(): Unit
}

case class Pool(name: String, block_caller: Boolean, executor: ExecutorService)
object Pool {
  // Good for work that does a lot of I/O but doesn't pressure the heap. Don't
  // forget to account for the current thread doing work when allocating.
  def unbounded(name: String): Pool = Pool(
    name,
    false,
    new ThreadPoolExecutor(0, Int.MaxValue, 60, TimeUnit.SECONDS, new SynchronousQueue[Runnable](true), new NamedThreadFactory(name))
  )

  // Good for anything that is resource constrained, since work will wait
  // instead of eating resources. We pay the cost of blocking the calling
  // thread instead of allowing the resources to be consumed.
  def constrained(name: String, threads_max: Int): Pool = Pool(
    name,
    true,
    new ThreadPoolExecutor(threads_max, threads_max, Int.MaxValue, TimeUnit.NANOSECONDS, new LinkedBlockingQueue[Runnable](), new NamedThreadFactory(name))
  )

  // Like constrained but allows some work on the calling thread.
  def bounded(name: String, threads_max: Int): Pool = constrained(name, threads_max).copy(block_caller = false)
}

final class NamedThreadFactory(name: String) extends ThreadFactory {
  private val group = Thread.currentThread().getThreadGroup()
  private val count = new atomic.AtomicInteger(1)

  def newThread(r: Runnable): Thread = {
    val t = new Thread(group, r, s"${name}-${count.getAndIncrement()}")
    t.setDaemon(true)
    t.setPriority(Thread.NORM_PRIORITY)
    t
  }
}

object `package` {

  // can't be a specific Seq because .grouped returns Iterable
  implicit class ParallelSeqOps[A](val as: Seq[A]) extends AnyVal {
    // these are Java Futures, not Scala Futures
    private[parallel] def background[B](executor: ExecutorService, f: A => B): Seq[Future[B]] =
      as.map { a => executor.submit(new Callable[B] { def call(): B = f(a) }) }

    // Performs f in parallel threads, order is not guaranteed. The work for
    // each element is assumed to be roughly the same, allowing us to evenly
    // distribute the load across this thread and an executor.
    //
    // A non-positive parallelism will create a job for each piece of work.
    def parmap[B](pool: Pool, parallelism: Int)(f: A => B): Seq[B] =
      if (as.isEmpty || (parallelism == 1 && !pool.block_caller)) as.map(f)
      else {
        val groupsize =
          if (parallelism <= 0) 1
          else math.max(1, as.length / parallelism)

        if (groupsize == 1) {
          if (pool.block_caller) {
            as.background(pool.executor, f).map(_.get) // blocks
          } else {
            // It would be good to have a fallback here, if a job fails to be
            // submitted to the pool immediately then do it on this thread. This
            // may be possible using ugly hacks involving ThreadLocal and
            // RejectedExecutionHandler.
            val jobs = as.tail.background(pool.executor, f)
            val here = f(as.head)
            val there = jobs.map(_.get) // blocks
            here +: there
          }
        } else {
          val grouped = as.grouped(groupsize).toSeq
          if (pool.block_caller) {
            grouped.background(pool.executor, _.map(f)).flatMap(_.get) // blocks
          } else {
            val jobs = grouped.tail.background(pool.executor, _.map(f))
            val here = grouped.head.map(f)
            val there = jobs.flatMap(_.get) // blocks
            here ++ there
          }
        }
      }

    def parforeach(pool: Pool, parallelism: Int)(f: A => Unit): Unit = parmap(pool, parallelism)(f): Unit
  }
}
