import scala.collection.mutable.ArrayBuffer

class ProgramNormaliser {
  import Program._

  def apply(p: Prog): (Prog, Seq[Var]) = { //return normalised prog + temp vars
    var nameCounter = 0
    val tempVars = new ArrayBuffer[Var]()
    def getTempVar(typ: Program.PType.Value) : Var = {
      nameCounter += 1
      val tempVar = Var("temp_" + nameCounter, typ)
      tempVars += tempVar
      tempVar
    }
    val newAssignments = new scala.collection.mutable.ArrayBuffer[Prog]
    def prependNewAssignments (p : Prog) = {
      if (newAssignments.isEmpty)
        p
      else
        Sequence(newAssignments reduce Sequence, p)
    }
    def appendNewAssignments (p : Prog) = {
      if (newAssignments.isEmpty)
        p
      else
        Sequence(p, newAssignments reduce Sequence)
    }
    def normaliseP (p : Prog) : Prog = {
      p match {
        case Assign(a1@ArElement(_,_), a2@ArElement(_,_)) =>
          // a1[i1] := a2[i2] --> t = a2[i2] ; a1[i1] := t
          val t = getTempVar(PType.PInt) // only Int elem types are considered
          Sequence(Assign(t, a2), Assign(a1, t))
        case Sequence(left, right) =>
          Sequence(normaliseP(left), normaliseP(right))
        case IfThenElse(cond, b1, b2) =>
          // prepends any array reads inside cond to directly before the if stmt
          assert(newAssignments.isEmpty)
          val newCond = normaliseBE(cond)
          val newP = prependNewAssignments(
            IfThenElse(newCond, normaliseP(b1), normaliseP(b2)))
          newAssignments.clear
          newP
        case While(cond, body) =>
          // prepends any array reads inside cond to directly before the While
          // stmt and also appends it to the body as the last statement
          assert(newAssignments.isEmpty)
          val newCond = normaliseBE(cond)
          val newP = prependNewAssignments(
            While(newCond, normaliseP(appendNewAssignments(body))))
          newAssignments.clear
          newP
        case Assert(cond) =>
          assert(newAssignments.isEmpty)
          val newCond = normaliseBE(cond)
          val newP = prependNewAssignments(Assert(newCond))
          newAssignments.clear
          newP
        case other => other
      }
    }
    def normaliseE (e: Expr) : Expr = {
      e match {
        case v: Var => v
        case c: IntConst => c
        case Plus(left, right) => Plus(normaliseE(left), normaliseE(right))
        case Times(left, right) => Times(normaliseE(left), normaliseE(right))
        case arElem: ArElement =>
          val t = getTempVar(PType.PInt)
          newAssignments += Assign(t, arElem)
          t
      }
    }
    def normaliseBE (e : BExpr) : BExpr = {
      e match {
        case Eq (left,right)  => Eq(normaliseE(left), normaliseE(right))
        case Leq(left, right) => Leq(normaliseE(left), normaliseE(right))
        case Not(be)          => Not(normaliseBE(be))
        case And(left, right) => And(normaliseBE(left), normaliseBE(right))
        case Or (left, right) => Or(normaliseBE(left), normaliseBE(right))
      }
    }
    (normaliseP(p), tempVars)
  }

}
