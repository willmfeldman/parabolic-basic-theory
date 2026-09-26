/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
import Lean
open Lean

/-! Local, non-sandboxed pre-check for the comparator challenges (not a substitute for Comparator).

Usage, from inside a challenge workspace after `lake build Challenge Solution`:

    lake env lean --run ../../scripts/check-challenge-definitions.lean <theorem names from config.json>

Exit code 0 and `result: MATCH` mean every definition restated in the `Challenge` modules and used by
the listed theorems agrees with the library constant of the same name. -/

/-- Local stand-in for Comparator's statement check: for each challenge theorem, walk the
constants it depends on (through types, and through values of non-theorems) that come from
`Challenge*` modules, and compare each with the Solution environment's constant of the same
name (kind, universe params, type, and value for definitions). -/
def isChallengeMod (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (`Challenge).isPrefixOf env.header.moduleNames[i.toNat]!
  | none => true

partial def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let names := args.map String.toName
  let envC ← importModules #[{ module := `Challenge }] {}
  let envS ← importModules #[{ module := `Solution }] {}
  let mut ok := true
  let mut seen : NameSet := {}
  let mut todo : Array Name := names.toArray
  let mut checked := 0
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some cC := envC.find? n | IO.println s!"MISSING in challenge: {n}"; ok := false; continue
    let some cS := envS.find? n | IO.println s!"MISSING in solution: {n}"; ok := false; continue
    let fromChallenge := isChallengeMod envC n
    let isThm := cC matches .thmInfo _
    if cC.levelParams != cS.levelParams then
      IO.println s!"LEVEL PARAMS differ: {n}"; ok := false
    if cC.type != cS.type then
      IO.println s!"TYPE differs: {n}"; ok := false
    if !isThm && fromChallenge then
      if cC.value? != cS.value? then
        IO.println s!"VALUE differs: {n}"; ok := false
      match cC, cS with
      | .defnInfo a, .defnInfo b =>
        if a.hints != b.hints then IO.println s!"HINTS differ: {n}"; ok := false
        if a.safety != b.safety then IO.println s!"SAFETY differs: {n}"; ok := false
      | _, _ => pure ()
    if (cC matches .thmInfo _) != (cS matches .thmInfo _) ||
       (cC matches .defnInfo _) != (cS matches .defnInfo _) then
      IO.println s!"KIND differs: {n}"; ok := false
    checked := checked + 1
    if fromChallenge then
      if names.contains n then
        IO.println s!"challenge theorem {n}: sorry-free in solution? {!(cS.value?.map (·.hasSorry)).getD false}"
      else
        IO.println s!"  checked local constant {n}"
      let mut deps := cC.type.getUsedConstants
      if !isThm then
        deps := deps ++ (cC.value?.map (·.getUsedConstants)).getD #[]
      for c in deps do
        if isChallengeMod envC c then todo := todo.push c
        else if (envS.find? c).isNone then
          IO.println s!"MISSING in solution (external): {c}"; ok := false
        else if (envC.find? c).map (·.type) != (envS.find? c).map (·.type) then
          IO.println s!"TYPE differs (external): {c}"; ok := false
  IO.println s!"checked {checked} constants; result: {if ok then "MATCH" else "MISMATCH"}"
  return if ok then 0 else 1
