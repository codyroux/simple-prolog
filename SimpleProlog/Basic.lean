/-
Author: Cody Roux
-/
import Lean
import Batteries.Data.MLList

variable {vars : Type} {const : Type}

variable [DecidableEq vars] [DecidableEq const]

inductive PTerm (vars const : Type) where
| var : vars → PTerm vars const
| con : const → PTerm vars const
| app : PTerm vars const → PTerm vars const → PTerm vars const
deriving DecidableEq, Repr, Inhabited

instance instToStringTerm [ToString vars] [ToString const] : ToString (PTerm vars const) where
  toString t := aux t
  where
    aux : PTerm vars const → String
    | .var v => toString v
    | .con c => toString c
    | .app t1 t2 => "(" ++ aux t1 ++ " " ++ aux t2 ++ ")"

namespace PTerm

def getVars : PTerm vars const → List vars
  | var v => [v]
  | con _ => []
  | app t1 t2 => (getVars t1) ++ (getVars t2)

structure Renaming vars where
  domain : List vars
  map : vars → vars

structure Subst (vars const : Type) where
  domain : List vars
  map : vars → PTerm vars const
deriving Inhabited

instance instToStringSubst [ToString vars] [ToString const] : ToString (Subst vars const) where
  toString s :=
    let mappings := s.domain.map (fun v => toString v ++ " ↦ " ++ toString (s.map v))
    "{" ++ String.intercalate ", " mappings ++ "}"

def apply (t : PTerm vars const) (s : Subst vars const) : PTerm vars const :=
  match t with
  | var v =>
    if v ∈ s.domain then
      s.map v
    else
      var v
  | con c => con c
  | app t1 t2 => app (apply t1 s) (apply t2 s)

def applyAndMark (t : PTerm vars const) (s : Subst vars const) : Bool × PTerm vars const :=
  match t with
  | var v =>
    if v ∈ s.domain then
      (true, s.map v)
    else
      (false, var v)
  | con c => (false, con c)
  | app t1 t2 =>
    let (m1, t1') := applyAndMark t1 s
    let (m2, t2') := applyAndMark t2 s
    (m1 || m2, app t1' t2')

partial def applyFull (t : PTerm vars const) (s : Subst vars const) : PTerm vars const :=
  let (b, t') := applyAndMark t s
  if b then
    applyFull t' s
  else
    t'

#eval
let s : Subst String String := {
  domain := ["x", "y"],
  map := fun v =>
    if v = "x" then con "a"
    else if v = "y" then app (con "b") (var "z")
    else default
}
let t := app (var "x") (app (var "y") (var "w"))
t.apply s

def Subst.compose (s1 s2 : Subst vars const) : Subst vars const :=
  {
    domain := s1.domain ++ (s2.domain.filter (fun v => v ∉ s1.domain)),
    map := fun v =>
      if v ∈ s1.domain then
        s1.map v
      else
        (s2.map v).apply s1
  }

def Subst.empty : Subst vars const :=
  {
    domain := [],
    map := fun v => var v
  }

def Subst.add (σ : Subst vars const) (v : vars) (t : PTerm vars const) : Subst vars const :=
  {
    domain := σ.domain.insert v
    map := fun v' => if v = v' then t else σ.map v'
  }

partial def occurs (v : vars) (t : PTerm vars const) (σ : Subst vars const) : Bool :=
  match t with
  | var v' =>
    if v' ∈ σ.domain then
      occurs v (σ.map v') σ
    else if v = v' then true else false
  | con _ => false
  | app t1 t2 => occurs v t1 σ || occurs v t2 σ

def collectVars (t : PTerm vars const) (acc : List vars) : List vars :=
  match t with
  | var v => acc.insert v
  | con _ => acc
  | app t1 t2 =>
    let acc1 := collectVars t1 acc
    collectVars t2 acc1

def collectVarsList (ts : List (PTerm vars const)) : List vars :=
  ts.foldl (fun acc t => collectVars t acc) []

end PTerm

namespace Unification

structure EqConstr (vars const : Type) where
  lhs : PTerm vars const
  rhs : PTerm vars const
deriving Repr, Inhabited

open PTerm

inductive UnifyError (vars const : Type) where
  | occursCheckFailed : vars → PTerm vars const → UnifyError vars const
  | constructorMismatch : const → const → UnifyError vars const
  | shapeMismatch : PTerm vars const → PTerm vars const → UnifyError vars const
deriving Repr

instance [ToString vars] [ToString const]: ToString (UnifyError vars const) where
  toString
    | UnifyError.occursCheckFailed v t =>
      "Occurs check failed: variable " ++ toString v ++ " occurs in term " ++ toString t
    | UnifyError.constructorMismatch c1 c2 =>
      "Constructor mismatch: " ++ toString c1 ++ " vs " ++ toString c2
    | UnifyError.shapeMismatch t1 t2 =>
      "Shape mismatch between terms: " ++ toString t1 ++ " and " ++ toString t2


abbrev UnifyM vars const α := StateT (Subst vars const) (Except (UnifyError vars const)) α

instance : MonadExcept (UnifyError vars const) (UnifyM vars const) := inferInstance

instance : MonadState (Subst vars const) (UnifyM vars const) := inferInstance

partial def UnifyM.run {α} (m : UnifyM vars const α) (init : Subst vars const := Subst.empty)
 : Except (UnifyError vars const) (Subst vars const) :=
  StateT.run m init |> Except.map Prod.snd

-- TODO: maybe we can actually use `partial_fixpoint` here!
mutual

partial def unifyAux (eqs : List (EqConstr vars const)) : UnifyM vars const Unit :=
  match eqs with
  | [] => pure ()
  | e::es => do
    let l ← unifyStep e
    unifyAux <| l ++ es

partial def unifyStep (e : EqConstr vars const)
 : UnifyM vars const (List (EqConstr vars const)) := do
 match (e.lhs, e.rhs) with
 | (var v, _)
 | (_, var v) =>
    do let s ← get
    if v ∈ s.domain then
      let lhs := e.lhs.apply s
      let rhs := e.rhs.apply s
      unifyStepNorm { lhs := lhs, rhs := rhs }
    else
      unifyStepNorm e
  | _ => unifyStepNorm e

partial def unifyStepNorm (e : EqConstr vars const)
 : UnifyM vars const (List (EqConstr vars const)) := do
  match (e.lhs, e.rhs) with
  | (var v, t)
  | (t, var v) =>
    do
      if t = var v then
        pure []
      else
      let σ ← get
      -- occurs check
      if occurs v t σ then
        throw (UnifyError.occursCheckFailed v t)
      else
        do
          StateT.modifyGet (fun σ => ([], σ.add v t))
  | (con c1, con c2) =>
    if c1 = c2 then
      pure []
    else
      throw (UnifyError.constructorMismatch c1 c2)
  | (app l1 r1, app l2 r2) =>
    pure [{ lhs := l1, rhs := l2 }, { lhs := r1, rhs := r2 }]
  | _ =>
    throw (UnifyError.shapeMismatch e.lhs e.rhs)

end


def unify (eqs : List (EqConstr vars const)) (init : Subst vars const := Subst.empty)
 : Except (UnifyError vars const) (Subst vars const) :=
  (unifyAux eqs).run (init := init)

def unifyOne (e : EqConstr vars const) (init : Subst vars const := Subst.empty)
  : Except (UnifyError vars const) (Subst vars const) :=
  unify [e] (init := init)


end Unification

open PTerm Unification


section TermDSL

open Lean Elab Meta

-- We create a little elaborator for terms
declare_syntax_cat p_lit
syntax ident : p_lit

def elabPLit : Syntax → MetaM Expr
  | `(p_lit| $id:ident) =>
    let id := id.getId.toString
    if id.front.isUpper then
      mkAppOptM ``PTerm.var #[none, mkConst ``String, mkStrLit id]
    else
      mkAppOptM ``PTerm.con #[mkConst ``String, none, mkStrLit id]
  | _ => throwError "unexpected syntax"

elab "test_elabPLit " p:p_lit : term => do
  let t ← elabPLit p
  return t

#reduce test_elabPLit x

#reduce test_elabPLit X

declare_syntax_cat p_term
syntax p_lit : p_term
syntax p_lit "(" p_term,* ")" : p_term

partial def elabPTerm : Syntax → MetaM Expr
  | `(p_term| $lit:p_lit) =>
    elabPLit lit
  | `(p_term| $lit:p_lit ( $args:p_term,* )) =>
    do
      let func ← elabPLit lit
      let argExprs ← args.getElems.mapM elabPTerm
      let mut result := func
      for arg in argExprs do
        result ← mkAppM ``PTerm.app #[result, arg]
      return result
  | _ => throwError "unexpected syntax"

elab "test_elabPTerm " t:p_term : term => do
  let t ← elabPTerm t
  return t

#check `(p_term| f ( a, b, X ))

-- TODO: create a delaborator for Term to make the output prettier.

#reduce test_elabPTerm f(x, Y, g(a))

elab "test_unify " t:p_term u:p_term : term => do
  let t ← elabPTerm t
  let u ← elabPTerm u
  let eqConstr ← mkAppM ``EqConstr.mk #[t, u]
  let emptySubst ← mkAppOptM ``Subst.empty #[mkConst ``String, mkConst ``String]
  let unifyCall ← mkAppM ``Unification.unifyOne #[eqConstr, emptySubst]
  return unifyCall

#eval test_unify f(X, a) f(b, Y)

#eval test_unify f(X, a) f(b, X)

#eval test_unify f(X, a) f(X, Y)

end TermDSL

#eval ({ lhs := app (var "x") (con "a"), rhs := app (con "b") (var "y") } : EqConstr String String)
#eval Unification.unifyOne { lhs := app (var "x") (con "a"), rhs := app (con "b") (var "y") }

namespace Clause

structure Clause (vars const : Type) where
  head : PTerm vars const
  body : List (PTerm vars const)
deriving Repr, Inhabited

instance [ToString vars] [ToString const] : ToString (Clause vars const) where
  toString c := s!"{c.head} -: {c.body}"

class GenSym (α : Type) where
  genSym : List α → α → α

class LawfulGenSym (α : Type) [DecidableEq α] [GenSym α] where
  genSym_fresh : ∀ (used : List α) (base : α), GenSym.genSym used base ∉ used

-- TODO: prove termination.
partial instance instGenSymString : GenSym String where
  genSym used base :=
    aux used base 0
  where
  aux used base (n : Nat) :=
    let candidate := base ++ "_" ++ toString n
    if candidate ∈ used then
      aux used base (n + 1)
    else
      candidate

variable [Inhabited vars] [DecidableEq vars] [GenSym vars]
variable [Repr vars] [Repr const]
variable [ToString vars] [ToString const]

structure PState (vars const : Type) where
  usedVars : List vars
  subst : Subst vars const
  goals : List (PTerm vars const)
deriving Inhabited

abbrev PrologST vars const := StateM (PState vars const)

def mkRenaming (usedVars : List vars) (toFreshen : List vars) : List vars × Subst vars const :=
  toFreshen.foldl
  (fun (allVars, σ) v =>
    if v ∈ σ.domain then (allVars, σ) else
    let v' := GenSym.genSym allVars v
    (allVars.insert v', σ.add v (.var v')))
  (usedVars, Subst.empty)

def PTerm.freshen (t : PTerm vars const) (usedVars : List vars) : List vars × PTerm vars const :=
  let (allVars, σ) := mkRenaming usedVars (t.getVars)
  (allVars, t.apply σ)

def addAll [BEq α] (l₁ l₂ : List α) :=
  l₂.foldl (fun l a => l.insert a) l₁

def freshen (c : Clause vars const) (usedVars : List vars) : List vars × Clause vars const :=
  let allVars := c.head.getVars
  let allVars := c.body.foldl (fun all l => addAll all l.getVars) allVars
  let (allVars, σ) := mkRenaming usedVars allVars
  (allVars, { head := c.head.apply σ, body := c.body.map (apply · σ)})


def apply
  (c : Clause vars const)
  (g : PTerm vars const) :
  ExceptT (UnifyError vars const) (PrologST vars const) Unit := do
  let st ← get
  let (allVars, c) := freshen c st.usedVars
  let eq : EqConstr vars const := ⟨g, c.head⟩
  dbg_trace s!"applying {c} to {g}"
  let σ ← unifyOne eq st.subst
  dbg_trace s!"Got {σ}"
  let newGoals := c.body.map (fun t => t.applyFull σ)
  modify ({· with goals := newGoals, usedVars := allVars, subst := σ})
  return ()


declare_syntax_cat p_clause
syntax p_term "-:" p_term,* : p_clause

open Lean Elab Meta

partial def elabPClause : Syntax → MetaM Expr
  | `(p_clause| $t:p_term -: $args:p_term,* ) =>
    do
      let head ← elabPTerm t
      let argExprs ← args.getElems.mapM elabPTerm
      let termTy ← mkAppOptM ``PTerm #[mkConst ``String, mkConst ``String]
      let bodyList ←
        argExprs.foldrM (fun arg acc => do
          let accExpr ← acc
          return mkAppM ``List.cons #[arg, accExpr])
          (mkAppOptM ``List.nil #[termTy])
      mkAppM ``Clause.mk #[head, ← bodyList]
  | _ => throwError "unexpected syntax"

elab "test_elabPClause " c:p_clause : term => do
  let c ← elabPClause c
  return c


#reduce test_elabPClause f(X, Y) -: g(a, Y), h(X)


end Clause

section Program

open Clause


variable {vars const : Type}
  [DecidableEq vars]
  [DecidableEq const]
  [Inhabited vars]
  [GenSym vars]
  [ToString vars]
  [ToString const]

abbrev Res := Option

structure Program vars const where
  clauses : List (Clause vars const)
deriving Inhabited

def select (goals : List (PTerm vars const)) : Option (PTerm vars const × List (PTerm vars const)) :=
  match goals with
  | [] => none
  | g :: gs => some (g, gs)

#check tryCatch

partial def runBody
  (P : Program vars const)
  : PrologST vars const (Res (Subst vars const)) := do
  let st ← get
  match select st.goals with
  | none => return st.subst
  | some (g, gs) =>
    for c in P.clauses do
      let newGoals ← Clause.apply c g |> ExceptT.run
      match newGoals with
      | .ok () => do
        let st ← get
        dbg_trace s!"new goals {newGoals}"
        modify ({ · with goals := st.goals ++ gs})
        let sol ← runBody P
        return sol
      | .error _ =>
        dbg_trace "failed."
        continue
    return failure

def run (P : Program vars const) (goal : PTerm vars const) : Res (Subst vars const) :=
  (runBody P).run' ⟨goal.getVars, Subst.empty, [goal]⟩

-- Not quite what we want: we want to list the values for the vars in the goal.
def giveSolution (P : Program vars const) (goal : PTerm vars const) : Res (PTerm vars const) := do
  let σ ← run P goal
  return goal.applyFull σ

private def test_clause_1 : Clause String String :=
  test_elabPClause concat(nil, X, X) -:

private def test_clause_2 : Clause String String :=
  test_elabPClause concat(cons(X, Y), Z, cons(X, W)) -: concat(Y, Z, W)

private def test_prog : Program String String := ⟨[test_clause_1, test_clause_2]⟩

private def test_goal : PTerm String String :=
  test_elabPTerm concat(cons(a, cons(b, nil)), cons(c, nil), O)

#eval giveSolution test_prog test_goal

end Program
