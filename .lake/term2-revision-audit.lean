import Multi.term2

open T

theorem check_isNF_index (s0 s1 s2 : T) (h : T.isNF (P s0 s1 s2)) :
    T.isNF s0 := by
  cases h with
  | p _ _ _ h0 _ _ _ _ => exact h0

theorem check_G_index (u s0 s1 s2 x : T) (hu : u ≤ s0)
    (hx : x ∈ T.G u s0) : x ∈ T.G u (P s0 s1 s2) := by
  rw [T.G, if_pos hu]
  exact List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ hx))

#print axioms check_isNF_index
#print axioms check_G_index
