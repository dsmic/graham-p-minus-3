import GrahamPM.Basic

/-!
# Small cases `m ≤ 23` (Lemma L4)

The orderings from the table in Section 4 of `proof.md`, for `x = 1`, checked by the kernel via
`decide`.
-/

namespace GrahamPM

theorem s1 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 1)) [] := by unfold Valid; decide
theorem s3 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 3)) [] := by unfold Valid; decide
theorem s5 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 5)) [2, 3] := by unfold Valid; decide
theorem s7 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 7)) [2, 3, 5, 4] := by
  unfold Valid; decide
theorem s9 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 9)) [2, 3, 5, 7, 4, 6] := by
  unfold Valid; decide
theorem s11 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 11)) [2, 3, 4, 5, 9, 6, 8, 7] := by
  unfold Valid; decide
theorem s13 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 13))
    [2, 3, 4, 5, 6, 9, 8, 10, 11, 7] := by
  unfold Valid; decide
theorem s15 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 15))
    [2, 3, 4, 5, 7, 6, 10, 9, 12, 13, 8, 11] := by
  unfold Valid; decide
theorem s17 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 17))
    [2, 3, 4, 5, 6, 7, 8, 10, 12, 9, 15, 11, 14, 13] := by
  unfold Valid; decide
theorem s19 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 19))
    [2, 3, 4, 5, 6, 7, 8, 9, 11, 14, 10, 12, 17, 13, 16, 15] := by
  unfold Valid; decide
theorem s21 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 21))
    [2, 3, 4, 5, 6, 7, 9, 10, 8, 12, 13, 16, 11, 18, 19, 17, 15, 14] := by
  unfold Valid; decide
theorem s23 : Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod 23))
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 12, 16, 15, 19, 13, 20, 21, 18, 17] := by
  unfold Valid; decide

/-- **L4.** For odd `m ≤ 23`, `ℤ_m ∖ {0, 1, -1}` has a valid ordering. -/
theorem small_case (m : ℕ) [NeZero m] (hm : Odd m) (hle : m ≤ 23) :
    ∃ l : List (ZMod m), Valid (Finset.univ \ {0, 1, -1}) l := by
  have h1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  interval_cases m <;> first
    | exact absurd hm (by decide)
    | exact ⟨_, s1⟩ | exact ⟨_, s3⟩ | exact ⟨_, s5⟩ | exact ⟨_, s7⟩ | exact ⟨_, s9⟩
    | exact ⟨_, s11⟩ | exact ⟨_, s13⟩ | exact ⟨_, s15⟩ | exact ⟨_, s17⟩ | exact ⟨_, s19⟩
    | exact ⟨_, s21⟩ | exact ⟨_, s23⟩

end GrahamPM
