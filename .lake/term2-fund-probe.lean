import Multi.term2
open T

def normalCheck : T → Bool
  | Z => true
  | P s0 s1 s2 => normalCheck s0 && normalCheck s1 && normalCheck s2 &&
      (T.G s0 s1).all (fun x => decide (x < s1)) && decide (T.head s2 ≤ P s0 s1 Z)

def printTerm : T → String
  | Z => "Z"
  | P s0 s1 s2 => "P(" ++ printTerm s0 ++ "," ++ printTerm s1 ++ "," ++ printTerm s2 ++ ")"

def probe (fuel : Nat) (terms : List T) : IO Unit := do
  match fuel with
  | 0 => IO.println "bounded exploration finished"
  | fuel + 1 =>
    IO.println s!"round {fuel}: {terms.length} terms"
    let next := (terms.flatMap fun s => (List.range 3).map fun n => (s, n, T.fund s (T.ofNat n)))
    match next.find? (fun p => !(normalCheck p.2.2)) with
    | some p =>
      IO.println s!"NONNORMAL: index {p.2.1}"
      IO.println (printTerm p.1)
      IO.println (printTerm p.2.2)
    | none =>
      let ts := (next.map fun p => p.2.2).filter fun s => s.size < 300
      probe fuel ts.eraseDups

#eval probe 7 ((List.range 5).map fun n => P Z (T.LF n) Z)
