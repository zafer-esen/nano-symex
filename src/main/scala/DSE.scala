import scala.collection.mutable.ArrayBuffer
import scala.collection.{immutable, mutable}

/**
 * Extremely simple dynamic symbolic execution engine.
 */
class DSE(encoder : ExprEncoder, spawnSMT : => SMT,
          logCommands : Boolean = false) {

  val smt = spawnSMT

  import encoder._
  import Program._
  import PType.{PInt, PArray}
  import smt._
  import SMT._
  import scala.collection.mutable.Queue

  private val valQueue = Queue[(Valuation, Int)]()

  def shutdown = smt.shutdown

  smt.logCommands(logCommands)

  def exec(p : Prog, variables : Seq[Var], depth : Int = Integer.MAX_VALUE) = {

    def createSymbolicArray(name : String, len : Int) : Map[BigInt, String] = {
      (for (i <- 0 until len) yield
        (BigInt(i), name + "_" + i)).toMap
    }
    def createBigInitArray(len : Int, default : BigInt = 0) :
    Map[BigInt, BigInt] = {
      (for (i <- 0 until len) yield (BigInt(i) -> default)).toMap
    }

    val firsttest =
      new Valuation(
        (for (v@Var(name, PInt, _) <- variables) yield (v -> BigInt(0))).toMap,
        (for (v@Var(name, PArray, len) <- variables) yield (v ->
          createBigInitArray(len))).toMap // bigInt indices?
      )

    val initstore   : SymbStore =
      (for (v@Var(name, _, _) <- variables) yield v -> name).toMap
    val initstoreAr : ArSymbStore =
      (for (v@Var(name, PArray, arrayLen) <- variables) yield
        v -> createSymbolicArray(name, arrayLen)).toMap

    valQueue.clear

    valQueue.enqueue((firsttest,0))

    println("First test case\n" + firsttest)

    while (!valQueue.isEmpty) {
      val (test,bl) = valQueue.dequeue
      println("now starting\n" + test + "\nlevel" + bl)
      for (v@Var(name, PInt, _) <- variables)
        declareConst(name, IntType)
      for (v@Var(name, PArray, _) <- variables)
        declareConst(name, ArType)
      execHelp(p, variables, test, bl, 0)(initstore, initstoreAr)
      reset
    }

  }

  def execHelp(p : Prog, variables : Seq[Var],
               valuation : Valuation,
               bl : Int, curl: Int)
              (implicit store   : SymbStore,
                        arStore : ArSymbStore) : Unit = p match {

    case Skip => ()

    case Sequence(Skip, rest) =>
      execHelp(rest, variables, valuation, bl, curl)

    case Sequence(Sequence(p1, p2), p3) =>
      execHelp(Sequence(p1, Sequence(p2, p3)), variables, valuation, bl, curl)

    case Sequence(op@Assign(lhs : Var, rhs), rest) => {
      val newConst = freshConst(IntType)
      val newValuation = valuation + (lhs -> eval(rhs,valuation))
      addAssertion("(= " + newConst + " " + encode(rhs) + ")")
      val newStore = store + (lhs -> newConst)
      execHelp(rest, variables, newValuation, bl, curl)(newStore, arStore)
    }

    case Sequence(IfThenElse(cond, b1, b2), rest) => {
      println("level " + curl)
      if (eval(cond, valuation)) {
        if (bl <= curl) {
  	  push
          addAssertion(encode(Not(cond))) ;
          if (isSat) {
            val intValuation = (for (v@Var(name, PInt, _) <- variables)
              yield (v -> getSatValue(name))).toMap
            val arrayValuation = (for (v@Var(name, PArray, len) <- variables)
              yield (v -> getArrayValue(name))).toMap
            val newtest = new Valuation(intValuation, arrayValuation)
            println("new test case" + newtest)
            valQueue.enqueue((newtest,curl+1))
          }
          pop
	}
	addAssertion(encode(cond))
        execHelp(Sequence(b1, rest), variables, valuation, bl, curl+1)
      } else {
          println("level " + curl + " orig " + bl)
          if (bl <= curl) {
            push
            addAssertion(encode(cond))
            if (isSat) {
              val newtest = ??? // todo: create proper Valuation for arrays too
//                (for (v@Var(name, PInt, _) <- variables)
//                 yield (v -> getSatValue(name))).toMap
              println("new test case" + newtest)
              valQueue.enqueue((newtest,curl+1))
            }
	    pop
	  }
          addAssertion(encode(Not(cond)))
          execHelp(Sequence(b2, rest), variables, valuation, bl, curl+1)
      }
    }

    case Sequence(w@While(cond, body), rest) =>
      execHelp(Sequence(IfThenElse(!cond, Skip, Sequence(body, w)), rest),
               variables, valuation, bl, curl)

    case Sequence(a@Assert(cond), rest) => {    // Still to be fixed
      push
      addAssertion(encode(!cond))
      if (isSat) {
        println("Foun`d testcase leading to failing assertion:")
        val failtest =  ??? // todo: create proper Valuation for arrays too
//          (for (v@Var(name, PInt) <- variables)
//           yield (v -> getSatValue(name))).toMap
        println(failtest)
      }
      pop
      execHelp(rest, variables, valuation, bl, curl)
    }

    case p =>
      execHelp(Sequence(p, Skip), variables, valuation, bl, curl)

  }

}


object DSETest extends App {

  import ExampleProg._

  val dse = new DSE(new IntExprEncoder(useArrayTheory = true), new Z3SMT)

  dse.exec(p, List(a, b, x, y))

}

object DSETest2 extends App {

  import ExampleProg2._

  val dse = new DSE(new IntExprEncoder(useArrayTheory = true), new Z3SMT)

  dse.exec(p, List(a, x), 200)

}

object DSETest3 extends App {

  import ExampleProg3._

  val dse = new DSE(new IntExprEncoder(useArrayTheory = true), new Z3SMT)

  dse.exec(p, List(a, b))

}

object Step5_DSE_ArrayTheory {
  import Program._

  def main(args : Array[String]) {
    val timeoutSeconds = 60
    println("Running step 3 with a timeout of " + timeoutSeconds + " seconds")

    import scala.concurrent.ExecutionContext.Implicits.global
    import scala.concurrent._
    import scala.concurrent.duration._

    def task(len : Int) = {
      val A = Var("A", PType.PArray, len)
      val prog = new InsertionSortProg(A, IntConst(len))
      import prog._

      val solver = new Z3SMT
      val symex = new DSE(new IntExprEncoder(useArrayTheory = true),
        solver, logCommands = true)
      symex.exec(p, List(A, i, j, x), 200)
      println(solver.numCheckSatCalls + " check-sat calls")
    }

    var len = 1
    var stop = false
    val timer = new Util.Timer

    while(!stop) {
      len += 1
      println("-"*80)
      println("len = " + len)
      timer.start()
      try Await.result(Future(task(len)), timeoutSeconds seconds) catch {
        case _: TimeoutException =>
          println("timeout!")
          stop = true
      }
      timer.stop()
      println(timer.s + " seconds")
    }
  }
}

object Step5_DSE_NoArrayTheory {
  import Program._

  def main(args : Array[String]) {
    val timeoutSeconds = 60
    println("Running step 3 with a timeout of " + timeoutSeconds + " seconds")

    import scala.concurrent.ExecutionContext.Implicits.global
    import scala.concurrent._
    import scala.concurrent.duration._

    def task(len : Int) = {
      val A = Var("A", PType.PArray)
      val prog = new InsertionSortProg(A, IntConst(len))
      import prog._

      val solver = new Z3SMT
      val symex = new DSE(new IntExprEncoder(useArrayTheory = false),
        solver, logCommands = false)
      symex.exec(p, List(A, i, j, x), 200)
      println(solver.numCheckSatCalls + " check-sat calls")
    }

    var len = 1
    var stop = false
    val timer = new Util.Timer

    while(!stop) {
      len += 1
      println("-"*80)
      println("len = " + len)
      timer.start()
      try Await.result(Future(task(len)), timeoutSeconds seconds) catch {
        case _: TimeoutException =>
          println("timeout!")
          stop = true
      }
      timer.stop()
      println(timer.s + " seconds")
    }
  }
}