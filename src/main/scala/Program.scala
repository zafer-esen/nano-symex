import Program.Expr

object Program {

  /**
   * Integer-valued expressions.
   */

  abstract sealed class Expr {
    def +(that : Expr)   = Plus(this, that)
    def -(that : Expr)   = Plus(this, that * (-1))
    def unary_-          = this * (-1)
    def *(that : Expr)   = Times(this, that)
    def <=(that : Expr)  = Leq(this, that)
    def >=(that : Expr)  = Leq(that, this)
    def <(that : Expr)   = Leq(this + 1, that)
    def >(that : Expr)   = Leq(that + 1, this)
    def ===(that : Expr) = Eq(that, this)
    def =/=(that : Expr) = !Eq(that, this)
  }

  case class Var     (name : String,
                      ptype : PType.Value = PType.PInt,
                      arrayLen : Int = 0) //optional size argument for arrays
                                                          extends Expr {
    override def toString: String = name
  }
  case class IntConst(value : BigInt)                     extends Expr {
    override def toString: String = value.toString
  }
  case class Plus    (left : Expr, right : Expr)          extends Expr {
    override def toString: String = left + " + " + right
  }
  case class Times   (left : Expr, right : Expr)          extends Expr {
    override def toString: String = left + " * " + right
  }
  case class ArElement(a : Var, i : Expr)                 extends Expr {
    override def toString: String = a + "[" + i + "]"
  }

  implicit def int2Expr(v : Int) : Expr = IntConst(v)

  object PType extends Enumeration {
    val PInt, PArray = Value
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Boolean expressions / predicates.
   */

  abstract sealed class BExpr {
    def &(that : BExpr) = And(this, that)
    def |(that : BExpr) = Or (this, that)
    def unary_!         = Not(this)
  }

  case class Eq  (left : Expr, right : Expr)     extends BExpr {
    override def toString: String = left + " = " + right
  }
  case class Leq (left : Expr, right : Expr)     extends BExpr {
    override def toString: String = left + " <= " + right
  }

  case class Not (sub : BExpr)                   extends BExpr {
    override def toString: String = "!" + sub
  }
  case class And (left : BExpr, right : BExpr)   extends BExpr {
    override def toString: String = left + " & " + right
  }
  case class Or  (left : BExpr, right : BExpr)   extends BExpr {
    override def toString: String = left + " | " + right
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * While-programs.
   */

  abstract sealed class Prog {
    override def toString: String = {
      this match {
        case Skip => ""
        case Assign(v, rhs) => v + " := " + rhs
        case Assert(cond) => "Assert(" + cond + ")"
        case Sequence(left, right) => left + "\n" + right
        case IfThenElse(cond, b1, b2) =>
          "If(" + cond + ") (\n" +
          b1 + "\n" +
          ") Else (\n" +
          b2 + "\n" +
          ")"
        case While(cond, body) =>
          "While(" + cond + ") (\n" +
          body + "\n" + ")"
      }
    }
  }

  case object Skip                                            extends Prog

  case class  Assign     (v : Expr, rhs : Expr)               extends Prog
  case class  Assert     (cond : BExpr)                       extends Prog

  case class  Sequence   (left  : Prog, right : Prog)         extends Prog
  case class  IfThenElse (cond : BExpr, b1 : Prog, b2 : Prog) extends Prog
  case class  While      (cond : BExpr, body : Prog)          extends Prog

  def Prog(stmts : Prog*) : Prog =
    if (stmts.isEmpty)
      Skip
    else
      stmts reduceRight (Sequence(_, _))

  def If(cond : BExpr)(branch : Prog*) =
    IfThenElse(cond, Prog(branch : _*), Skip)

  def While(cond : BExpr)(body : Prog*) : Prog =
    While(cond, Prog(body : _*))

  implicit def var2LHS(v : Var) = new AnyRef {
    def :=(that : Expr) = Assign(v, that)
  }

  implicit def arElement2LHS(e : ArElement) = new AnyRef {
    def :=(that : Expr) = Assign(e, that)
  }

  implicit def ite2RichIte(p : IfThenElse) = new AnyRef {
    def Else(branch : Prog*) =
      IfThenElse(p.cond, p.b1, Prog(branch : _*))
  }

  implicit def arSelect(a : Var) = new AnyRef {
    def apply(i : Expr) = ArElement(a, i)
  }

}

object ExampleExpr {

  import Program._

  val x = Var("x")
  val y = Var("y")

  val f = 0 <= x & x <= 10 & x + y === 42
  val g = y <= 20

}

object ExprTest extends App {

  import Program._
  val useArrayTheory = true
  val exprEncoder = new IntExprEncoder(useArrayTheory)
  import exprEncoder._
  import ExampleExpr._

  println("f: " + f)
  println("g: " + g)

  for (smt <- List(new Z3SMT, new PrincessSMT)) try {
    import smt._
    println("Testing SMT solver " + name + " ...")

    implicit val store   : SymbStore   = Map(x -> "x", y -> "y")
    implicit val arStore : ArSymbStore = Map.empty

    for (encoder <- List(exprEncoder,
                         new BVExprEncoder (32, useArrayTheory))) {
      import encoder._

      println("  sort " + IntType)

      push
      declareConst("x", IntType)
      declareConst("y", IntType)

      addAssertion(encode(f))
      println("    f is sat: " + isSat)

      addAssertion(encode(g))
      println("    f & g is sat: " + isSat)
      pop
    }
  } finally {
    smt.shutdown
  }

}

object ExampleProg {

  import Program._

  val a = Var("a")
  val b = Var("b")
  val x = Var("x")
  val y = Var("y")

  val p = Prog(
    x := 1,
    y := 0,
    If (a =/= 0) (
      y := 3+x,
      If (b === 0) (
        x := 2*(a+b)
      )
    ),
    Assert(x-y =/= 0)
  )

}

object ExampleProg2 {

  import Program._

  val a = Var("a")
  val x = Var("x")

  val p = Prog(
    x := 0,
    While (x =/= a) (
      x := x + 1
    ),
    Assert(x === a)
  )

}

object ExampleProg3 {

  import Program._

  val a = Var("a")
  val b = Var("b")

  val p = Prog(
    a := a + 1,
    b := (a + b) - 3, 
    If (a === b) (
        Assert(a =/= 0)
    )
  )
}

object ProgTest extends App {

  println(ExampleProg.p)

}

class InsertionSortProg (val A : Program.Var, val len : Program.IntConst) {
  import Program._
  val i = Var("i")
  val j = Var("j")
  val x = Var("x")

  val p = Prog(
    i := 1,
    While(i < len) (
      x := A(i),
      j := i - 1,
      While(j >= 0 & A(j) > x) (
        A(j+1) := A(j),
        j := j - 1
      ),
      A(j+1) := x,
      i := i + 1
    ),

    // assertion: the final array is sorted
    i := 0,
    While(i+1 < len) (
      Assert(A(i) <= A(i+1)),
      i := i + 1
    )
  )

  override def toString: String = p.toString
}

object Step2Test extends App {
  import Program._
  // inputs: array A, array length len
  val A = Var("A", PType.PArray)
  val prog = new InsertionSortProg(A, IntConst(10))
  println(prog)
}
