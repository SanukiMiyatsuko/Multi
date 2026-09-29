import Multi.term2
open T

def checkNF : T → Bool
  | Z => true
  | P a b c => checkNF a && checkNF b && checkNF c &&
      (T.G a b).all (fun x => decide (x < b)) && decide (T.head c ≤ P a b Z)

def showT : T → String
  | Z => "0"
  | P a b c => "P(" ++ showT a ++ "," ++ showT b ++ "," ++ showT c ++ ")"

def enumerateNF (n : Nat) : Array (List T) := Id.run do
  let mut levels := #[[Z]]
  for k in List.range n do
    let mut next := []
    for i in List.range (k + 1) do
      for j in List.range (k - i + 1) do
        for a in levels[i]! do
          for b in levels[j]! do
            for c in levels[k - i - j]! do
              if (T.G a b).all (fun x => decide (x < b)) && decide (T.head c ≤ P a b Z) then
                next := P a b c :: next
    levels := levels.push next
  return levels

def runNFProbe : IO Unit := do
  let levels := enumerateNF 9
  for i in List.range levels.size do
    IO.println s!"size {i}: {levels[i]!.length} normal forms"
    for s in levels[i]! do
      for n in List.range 4 do
        let t := T.fund s (T.ofNat n)
        if !(checkNF t) then
          IO.println s!"FAIL index {n}: {showT s} -> {showT t}"
          return
  IO.println "All finite checks passed."

#eval runNFProbe

def subterms : T → List T
  | Z => [Z]
  | s@(P a b c) => s :: (subterms a ++ subterms b ++ subterms c)

def runGapProbe : IO Unit := do
  let levels := enumerateNF 8
  for i in List.range levels.size do
    for s in levels[i]! do
      match T.dom s with
      | .Ω l =>
        let z := T.fund s Z
        for x in (T.G l s).flatMap subterms do
          if decide (z < x) && decide (x < s) then
            IO.println s!"GAP FAIL {showT s}, fund0 {showT z}, subterm {showT x}"
            return
      | _ => pure ()
  IO.println "Support-subterm gap checks passed."

#eval runGapProbe

def runSubtermGapProbe : IO Unit := do
  let levels := enumerateNF 8
  for i in List.range levels.size do
    for s in levels[i]! do
      match T.dom s with
      | .Ω _ =>
        let z := T.fund s Z
        for x in subterms s do
          if decide (z < x) && decide (x < s) then
            match x with
            | P _ Z Z => pure ()
            | _ =>
              IO.println s!"NONPRINCIPAL GAP {showT s}, fund0 {showT z}, subterm {showT x}"
              return
      | _ => pure ()
  IO.println "Nonprincipal subterm gap checks passed."

#eval runSubtermGapProbe
