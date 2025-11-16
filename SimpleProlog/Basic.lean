/-
Author: Cody Roux
-/

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

def occurs (v : vars) (t : Term vars const) : Bool :=
  match t with
  | var v' => v = v'
  | con _ => false
  | app t1 t2 => occurs v t1 || occurs v t2

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
      -- occurs check
      if occurs v t then
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

#eval ({ lhs := app (var "x") (con "a"), rhs := app (con "b") (var "y") } : EqConstr String String)
#eval Unification.unifyOne { lhs := app (var "x") (con "a"), rhs := app (con "b") (var "y") }
