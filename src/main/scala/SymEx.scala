import java.util.concurrent.TimeoutException

/**
 * Extremely simple symbolic execution engine.
 */
class SymEx(encoder : ExprEncoder, spawnSMT : => SMT,
            logCommands : Boolean = false){

  val smt = spawnSMT

  import encoder._
  import Program._
  import PType._
  import smt._

  def shutdown = smt.shutdown

  smt.logCommands(logCommands)

  def exec(p : Prog, variables : Seq[Var], depth : Int = Integer.MAX_VALUE) = {
    for (v@Var(name, PInt, _) <- variables)
      declareConst(name, IntType)
    if (encoder.useArrayTheory) {
      for (v@Var(name, PArray, _) <- variables)
      declareConst(name, ArType)
    }
    val store = // also includes array variables
      (for (v@Var(name, _, _) <- variables) yield (v -> name)).toMap
    val arStore = // starts all arrays with empty maps
      (for (v@Var(name, PArray, _) <- variables) yield
        v -> Map.empty[BigInt, String]).toMap

    execHelp(p, List(), depth)(store, arStore)

    reset
  }

  def execHelp(p : Prog, ops : List[Prog], depth : Int)
              (implicit store   : SymbStore,
                        arStore : ArSymbStore) : Unit = p match {

    case _ if ops.size > depth => ()

    case Skip => ()

    case Sequence(Skip, rest) =>
      execHelp(rest, ops, depth)

    case Sequence(Sequence(p1, p2), p3) =>
      execHelp(Sequence(p1, Sequence(p2, p3)), ops, depth)

    case Sequence(op@Assign(lhs : ArElement, rhs), rest) if useArrayTheory => {
      val newConst = freshConst(ArType)
      addAssertion("(= " + newConst + " " + "(store " +
        store(lhs.a) + " " + encode(lhs.i) + " " + encode(rhs) + "))")
      val newStore = store + (lhs.a -> newConst)
      execHelp(rest, op :: ops, depth)(newStore, arStore)
    }

    case Sequence(op@Assign(lhs : ArElement, rhs), rest) if !useArrayTheory => {
      // the index of the accessed array needs to be determined
      val ind = encode(lhs.i)
      if (isSat) {
        val v = getSatValue(ind)

        // first branch
        push
        addAssertion("(= " + ind + " " + v + ")")
        val (newArStore, nonArrayLhs) = {
            val newVal: String = freshConst(IntType)
            (arStore + (lhs.a -> (arStore(lhs.a) ++ Map(v -> newVal))), newVal)
        }

        addAssertion("(= " + nonArrayLhs + " " + encode(rhs) + ")")
        execHelp(rest, op :: ops, depth)(store, newArStore)
        pop

        // second branch
        push
        addAssertion("(not (= " + ind + " " + v + "))")
        execHelp(Sequence(op, rest), ops, depth)(store, arStore)
        pop
      } else () // do nothing if no other ind values possible
    }

    case Sequence(op@Assign(lhs : Var, rhs : ArElement), rest) if !useArrayTheory => {
      // the index of the accessed array needs to be determined
      val ind : String = encode(rhs.i)
      if (isSat) {
        val v = getSatValue(ind)
        // first branch
        push
        addAssertion("(= " + ind + " " + v + ")")
        val (newArStore, nonArrayRhs: String) = arStore(rhs.a).get(v) match {
          case Some(e) => (arStore, e)
          case None =>
            val newVal: String = freshConst(IntType)
            (arStore + (rhs.a -> (arStore(rhs.a) ++ Map(v -> newVal))), newVal)
        }
        //val newConst = freshConst(IntType)
        //addAssertion("(= " + newConst + " " + nonArrayRhs + ")")
        val newStore = store + (lhs -> nonArrayRhs)
        execHelp(rest, op :: ops, depth)(newStore, newArStore)
        //execHelp(Sequence(Assign(lhs, nonArrayVar),
        //  rest), ops, depth)(newStore, newArStore)
        pop

        // second branch
        push
        addAssertion("(not (= " + ind + " " + v + "))")
        execHelp(Sequence(op, rest), ops, depth)(store, arStore)
        pop
      } else () // do nothing if no other ind values possible
    }

    case Sequence(op@Assign(lhs : Var, rhs), rest) => {
      val newConst = freshConst(IntType)
      addAssertion("(= " + newConst + " " + encode(rhs) + ")")
      val newStore = store + (lhs -> newConst)
      execHelp(rest, op :: ops, depth)(newStore, arStore)
    }

    case Sequence(IfThenElse(cond, b1, b2), rest) => {
      val condStr = encode(cond)
      push
      addAssertion(condStr)
      val trueBranchSat = isSat
      if (trueBranchSat)
        execHelp(Sequence(b1, rest), ops, depth)
      pop
      push
      addAssertion("(not " + condStr + ")")
      if (!trueBranchSat || isSat)
        execHelp(Sequence(b2, rest), ops, depth)
      pop
    }

    case Sequence(w@While(cond, body), rest) =>
      execHelp(Sequence(IfThenElse(!cond, Skip, Sequence(body, w)), rest),
               ops, depth)

    case Sequence(a@Assert(cond), rest) => {
      push
      addAssertion(encode(!cond))
      if (isSat) {
        println("Found path leading to failing assertion:")
        for (op <- (a :: ops).reverse)
          println("  " + op)
        smt.logCommands(false)
      } else {
        pop
        execHelp(rest, ops, depth)
      }
    }

    case p =>
      execHelp(Sequence(p, Skip), ops, depth)

  }

}


object SymExTest extends App {

  import ExampleProg._

  val symex = new SymEx(new IntExprEncoder(useArrayTheory = true),
                        new Z3SMT, logCommands = false)

  symex.exec(p, List(a, b, x, y))

}

object SymExTest2 extends App {

  import ExampleProg2._

  val symex = new SymEx(new IntExprEncoder(useArrayTheory = true),
                        new Z3SMT, logCommands = false)

  symex.exec(p, List(a, x), 200)

}

object Step3 {
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
      val symex = new SymEx(new IntExprEncoder(useArrayTheory = true),
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

object Step4 {
  import Program._

  def main(args : Array[String]) {
    val timeoutSeconds = 60
    println("Running step 4 with a timeout of " + timeoutSeconds + " seconds")

    import scala.concurrent.ExecutionContext.Implicits.global
    import scala.concurrent._
    import scala.concurrent.duration._

    def task(len : Int) = {
      val A = Var("A", PType.PArray)
      val prog = new InsertionSortProg(A, IntConst(len))
      import prog._
      val solver = new Z3SMT
      val symex = new SymEx(new IntExprEncoder(useArrayTheory = false),
        solver, logCommands = false)
      val pNormaliser = new ProgramNormaliser
      val (normalisedP, tempVars) = pNormaliser(p)
      symex.exec(normalisedP, List(A, i, j, x) ++ tempVars, 200)
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
      Thread.sleep(10)
    }
  }
}