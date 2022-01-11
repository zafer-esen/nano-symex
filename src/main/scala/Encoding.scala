
/**
 * Translation from ASTs to SMT expressions.
 */
abstract class ExprEncoder {

  import Program._

  val useArrayTheory : Boolean

  val IntType : String
  val ArType  : String

  class Valuation(val intValuation : Map[Var, BigInt],
                  val arrayValuation : Map[Var, Map[BigInt, BigInt]]) {
    override def toString: String =
      intValuation.toString + "; " + (
        (for(v <- arrayValuation) yield {v._1  + " -> [" + v._2.mkString(", ") +
          "]"}).mkString(", "))

    def apply(v : Var) : BigInt = {
      assert(v.ptype == PType.PInt, "Trying to get integer value from " +
        "array var: " + v)
      intValuation(v)
    }
    def apply(v : Var, i : Int) : BigInt = {
      assert(v.ptype == PType.PArray, "Trying to get array value from " +
        "integer var: " + v)
      arrayValuation(v)(i)
    }
    def +(other : Valuation) : Valuation = {
      new Valuation(this.intValuation ++ other.intValuation,
                    this.arrayValuation ++ other.arrayValuation)
    }
    def +(appendedVar : (Var, BigInt)) : Valuation = {
      new Valuation(this.intValuation + appendedVar,
                    this.arrayValuation)
    }
  }

  type SymbStore   = Map[Var, String]
  type ArSymbStore = Map[Var, Map[BigInt, String]]

  def encode(expr : Expr)(implicit store    : SymbStore,
                                   arStore  : ArSymbStore) : String

  def encode(expr : BExpr)(implicit store   : SymbStore,
                                    arStore : ArSymbStore) : String

  def eval(expr : Expr, valuation: Valuation) : BigInt

  def eval(expr : BExpr, valuation: Valuation) : Boolean

}

/**
 * Translation from ASTs to SMT expressions, mapping the program integer
 * type to unbounded (mathematical) integers.
 */
class IntExprEncoder (override val useArrayTheory : Boolean)
  extends ExprEncoder {

  import Program._

  val IntType : String = "Int"
  val ArType  : String = "(Array Int Int)"

  def encode(expr : Expr)
            (implicit store   : SymbStore,
                      arStore : ArSymbStore) : String = expr match {
    case v : Var         => store(v)
    case ArElement(a, i) => "(select " + store(a) + " " + encode(i) + ")"
    case IntConst(v)     => if (v >= 0) v.toString else ("(- " + -v + ")")
    case Plus(l, r)      => "(+ " + encode(l) + " " + encode(r) + ")"
    case Times(l, r)     => "(* " + encode(l) + " " + encode(r) + ")"
  }

  def encode(expr : BExpr)
            (implicit store   : SymbStore,
                      arStore : ArSymbStore) : String = expr match {
    case Eq(l, r)    => "(= "   + encode(l) + " " + encode(r) + ")"
    case Leq(l, r)   => "(<= "  + encode(l) + " " + encode(r) + ")"
    case Not(s)      => "(not " + encode(s) + ")"
    case And(l, r)   => "(and " + encode(l) + " " + encode(r) + ")"
    case Or(l, r)    => "(or "  + encode(l) + " " + encode(r) + ")"
  }

  def eval(expr : Expr, valuation : Valuation) : BigInt = expr match {
    case v : Var     => valuation(v)
    case ArElement(a, i) => valuation(a, eval(i, valuation).toInt) // todo
    case IntConst(v) => v
    case Plus(l, r)  => (eval(l,valuation) + eval(r,valuation))
    case Times(l, r) => (eval(l,valuation) * eval(r,valuation))
  }
  
  def eval(expr : BExpr, valuation : Valuation) : Boolean = expr match {
    case Eq(l, r)    => (eval(l,valuation) == eval(r,valuation))
    case Leq(l, r)   => (eval(l,valuation) <= eval(r,valuation))
    case Not(s)      => (!eval(s,valuation))
    case And(l, r)   => (eval(l,valuation) && eval(r,valuation))
    case Or(l, r)    => (eval(l,valuation) || eval(r,valuation))
  }

}

/**
 * Translation from ASTs to SMT expressions, mapping the program integer
 * type to signed bit-vectors of width <code>width</code>.
 */
class BVExprEncoder(width : Int, override val useArrayTheory: Boolean)
  extends ExprEncoder {

  import Program._

  val IntType : String = "(_ BitVec " + width + ")"
  val ArType  : String = "(Array " + IntType + " " + IntType + ")"

  def encode(expr : Expr)
            (implicit store   : SymbStore,
                      arStore : ArSymbStore) : String = expr match {
    case v : Var     => store(v)
    case ArElement(a, i) => "(select " + store(a) + " " + encode(i) + ")"
    case IntConst(v) =>
      if (v >= 0)
        "(_ bv" + v.toString + " " + width + ")"
      else
        "(bvneg (_ bv" + (-v).toString + " " + width + "))"
    case Plus(l, r)  => "(bvadd " + encode(l) + " " + encode(r) + ")"
    case Times(l, r) => "(bvmul " + encode(l) + " " + encode(r) + ")"
  }

  def encode(expr : BExpr)
            (implicit store   : SymbStore,
                      arStore : ArSymbStore) : String = expr match {
    case Eq(l, r)    => "(= "     + encode(l) + " " + encode(r) + ")"
    case Leq(l, r)   => "(bvsle " + encode(l) + " " + encode(r) + ")"
    case Not(s)      => "(not "   + encode(s) + ")"
    case And(l, r)   => "(and "   + encode(l) + " " + encode(r) + ")"
    case Or(l, r)    => "(or "    + encode(l) + " " + encode(r) + ")"
  }

  def eval(expr : Expr, valuation: Valuation) : BigInt = ???

  def eval(expr : BExpr, valuation: Valuation) : Boolean = ???

}

