/-
Author: Cody Roux
-/
import Lean


variable {vars : Type} {const : Type}

variable [DecidableEq vars] [DecidableEq const]

inductive Term (vars const : Type) where
| var : vars → Term vars const
| con : const → Term vars const
| app : Term vars const → Term vars const → Term vars const
deriving DecidableEq, Repr, Inhabited

instance instToStringTerm [ToString vars] [ToString const] : ToString (Term vars const) where
  toString t := aux t
  where
    aux : Term vars const → String
    | .var v => toString v
    | .con c => toString c
    | .app t1 t2 => "(" ++ aux t1 ++ " " ++ aux t2 ++ ")"

#print Term

#synth Inhabited <| Term String String

#print instInhabitedTerm

namespace Term

structure Subst (vars const : Type) where
  domain : List vars
  map : vars → Term vars const

instance instToStringSubst [ToString vars] [ToString const] : ToString (Subst vars const) where
  toString s :=
    let mappings := s.domain.map (fun v => toString v ++ " ↦ " ++ toString (s.map v))
    "{" ++ String.intercalate ", " mappings ++ "}"

def apply (t : Term vars const) (s : Subst vars const) : Term vars const :=
  match t with
  | var v =>
    if v ∈ s.domain then
      s.map v
    else
      var v
  | con c => con c
  | app t1 t2 => app (apply t1 s) (apply t2 s)


def applyAndMark (t : Term vars const) (s : Subst vars const) : Bool × Term vars const :=
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

partial def applyFull (t : Term vars const) (s : Subst vars const) : Term vars const :=
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

def Subst.single (v : vars) (t : Term vars const) : Subst vars const :=
  {
    domain := [v],
    map := fun _ => t
  }

partial def occurs (v : vars) (t : Term vars const) (σ : Subst vars const) : Bool :=
  match t with
  | var v' =>
    if v' ∈ σ.domain then
      occurs v (σ.map v') σ
    else if v = v' then true else false
  | con _ => false
  | app t1 t2 => occurs v t1 σ || occurs v t2 σ

def collectVars (t : Term vars const) (acc : List vars) : List vars :=
  match t with
  | var v =>
    if v ∈ acc then
      acc
    else
      v :: acc
  | con _ => acc
  | app t1 t2 =>
    let acc1 := collectVars t1 acc
    collectVars t2 acc1

def collectVarsList (ts : List (Term vars const)) : List vars :=
  ts.foldl (fun acc t => collectVars t acc) []

end Term

namespace Unification

structure EqConstr (vars const : Type) where
  lhs : Term vars const
  rhs : Term vars const
deriving Repr, Inhabited

open Term

abbrev UnifyM vars const α := StateT (Subst vars const) (Except Unit) α

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
      let σ ← get
      -- occurs check
      if occurs v t σ then
        throw ()
      else
        do
          let s ← get
          let newSubst := Subst.single v t
          StateT.set (s.compose newSubst)
          pure []
  | (con c1, con c2) =>
    if c1 = c2 then
      pure []
    else
      throw ()
  | (app l1 r1, app l2 r2) =>
    pure [{ lhs := l1, rhs := l2 }, { lhs := r1, rhs := r2 }]
  | _ =>
    throw ()

end


def unify (eqs : List (EqConstr vars const)) : Except Unit (Subst vars const) :=
  Prod.snd <$> (unifyAux eqs).run (Subst.empty)

def unifyOne (e : EqConstr vars const) : Except Unit (Subst vars const) :=
  unify [e]

end Unification

open Term Unification


section TermDSL

open Lean Elab Meta

-- We create a little elaborator for terms
declare_syntax_cat p_lit
syntax ident : p_lit

def elabPLit : Syntax → MetaM Expr
  | `(p_lit| $id:ident) =>
    let id := id.getId.toString
    if id.front.isUpper then
      mkAppOptM ``Term.var #[none, mkConst ``String, mkStrLit id]
    else
      mkAppOptM ``Term.con #[mkConst ``String, none, mkStrLit id]
  | _ => throwError "unexpected syntax"

elab "test_elabPLit " p:p_lit : term => do
  let t ← elabPLit p
  logInfo m!"elaborated term: {t}"
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
        result ← mkAppM ``Term.app #[result, arg]
      return result
  | _ => throwError "unexpected syntax"

elab "test_elabPTerm " t:p_term : term => do
  let t ← elabPTerm t
  logInfo m!"elaborated term: {t}"
  return t

#reduce test_elabPTerm f(x, Y, g(a))

elab "test_unify " t:p_term u:p_term : term => do
  let t ← elabPTerm t
  let u ← elabPTerm u
  let eqConstr ← mkAppM ``EqConstr.mk #[t, u]
  let unifyCall ← mkAppM ``Unification.unifyOne #[eqConstr]
  logInfo m!"unification result: {unifyCall}"
  return unifyCall

#reduce test_unify f(X, a) f(b, Y)

#eval test_unify f(X, a) f(b, Y)

end TermDSL

#eval ({ lhs := app (var "x") (con "a"), rhs := app (con "b") (var "y") } : EqConstr String String)
#eval Unification.unifyOne { lhs := app (var "x") (con "a"), rhs := app (con "b") (var "y") }

namespace Clause

structure Clause (vars const : Type) where
  head : Term vars const
  body : List (Term vars const)
deriving Repr, Inhabited

class GenSym (α : Type) where
  genSym : List α → α → α

class LawfulGenSym (α : Type) [DecidableEq α] [GenSym α] where
  genSym_fresh : ∀ (used : List α) (base : α), GenSym.genSym used base ∉ used

#print Nat.toDigits
#print instToStringNat
#print Nat.repr

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

variable [DecidableEq α] [GenSym α]

#check Array.indexOf?
#check List.toArray

def freshSubst [Inhabited α] (used : List α) : Subst α const :=
  let freshVars :=
    used.map (fun v => GenSym.genSym used v)
  let freshVars := freshVars.toArray
  let usedArray := used.toArray
  let s : Subst α const :=
    {
      domain := used,
      map := fun v =>
        let idx := usedArray.indexOf? v
        match idx with
        | some i => var (freshVars[i]!)
        | none => var v
    }
  s

def freshen [Inhabited α] (used : List α) (cl : Clause α const) : Clause α const :=
  let s := freshSubst used
  {
    head := cl.head.apply s,
    body := cl.body.map (fun t => t.apply s)
  }

-- Now we need to freshen the head of a clause, unify it against the goal, and return the updated
-- substitution and body constraints.

end Clause
