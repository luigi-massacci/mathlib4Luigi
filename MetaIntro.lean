import Lean
import Mathlib.Tactic.Polyrith
import Mathlib.Data.Real.Basic
open Lean Elab Command


syntax (name := xxx) "red" : command
syntax (name := yyy) "green" : command
syntax (name := zzz) "blue" : command

@[macro xxx] def redMacro : Macro := λ stx =>
  match stx with
  | _ => `(green)

@[macro yyy] def greenMacro : Macro := λ stx =>
  match stx with
  | _ => `(blue)

@[command_elab zzz] def blueElab : CommandElab := λ stx =>
  Lean.logInfo "finally, blue!"

red -- finally, blue!


elab "traces" : tactic => do
  let array := List.replicate 2 (List.range 3)
  Lean.logInfo m!"logInfo: {array}"
  dbg_trace f!"dbg_trace: {array}"

example : True := by -- `example` is underlined in blue, outputting:
                     -- dbg_trace: [[0, 1, 2], [0, 1, 2]]
  traces -- now `traces` is underlined in blue, outputting
  --        -- logInfo: [[0, 1, 2], [0, 1, 2]]
  trivial


def one_plus_one_mk : Expr := mkAppN (.const ``Nat.add []) #[mkNatLit 1, mkNatLit 1]

elab "one_plus_one_mk" : term => return one_plus_one_mk

#eval one_plus_one_mk

def fun_plus_one : Expr := .lam `x (.const ``Nat [])
  (mkAppN (.const ``Nat.add []) #[mkNatLit 1, .bvar 0]) BinderInfo.default

elab "fun_plus_one" : term => return fun_plus_one

#check fun_plus_one

def debrjuin : Expr := .lam `a (.const ``Nat [])
  (.lam `b  (.const ``Nat [])
    ( (.lam `c  (.const ``Nat [])
      (mkAppN (.const ``Nat.mul [])
        #[(mkAppN (.const ``Nat.add []) #[.bvar 1, .bvar 2]), .bvar 0])
       BinderInfo.default))
    BinderInfo.default)
  BinderInfo.default

elab "debrjuin" : term => return debrjuin

#check debrjuin
