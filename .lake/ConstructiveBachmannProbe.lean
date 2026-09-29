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

def anchor (s : T) : T :=
  match T.dom s with
  | .Ω l => P (T.fund l Z) Z Z
  | .ω => T.ofNat 1
  | _ => Z

def runAnchoredBachmannProbe : IO Unit := do
  let levels := enumerateNF 7
  let terms := levels.toList.flatten
  let inputs := (enumerateNF 4).toList.flatten
  IO.println s!"Checking {terms.length} terms and {inputs.length} inputs"
  for s in terms do
    let ts := match T.dom s with
      | .ω => (List.range 4).map T.ofNat
      | .Ω l => inputs.filter (fun t => decide (t < P l Z Z))
      | _ => []
    for t in ts do
      let lo := T.fund s t
      let hi := T.fund s (t + P Z Z Z)
      for r in terms do
        if decide (lo < r) && decide (r ≤ hi) then
          let bound := T.fund r (anchor r)
          if !(decide (lo ≤ bound)) then
            IO.println s!"FAIL s={showT s}; t={showT t}; r={showT r}"
            IO.println s!"lower={showT lo}; upper={showT hi}; anchor-result={showT bound}"
            return
  IO.println "Anchored Bachmann finite checks passed."

#eval runAnchoredBachmannProbe