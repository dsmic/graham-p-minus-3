import GrahamPM.Challenge

/-!
# Sanity checks of the formal statement (not part of the proof)

Small examples in `ℤ_7` showing that the formulation means what is intended:
a valid ordering is accepted, an invalid one is rejected, and `k + 1` is computed in `ℕ`.
-/

namespace GrahamPM

/-- `2, 3, 5, 4` orders `ℤ_7 ∖ {0, 1, -1}` with partial sums `2, 5, 3, 0` (pairwise distinct). -/
example : ∃ l : List (ZMod 7), l.Nodup ∧ l.toFinset = Finset.univ \ {0, 1, -1} ∧
    Function.Injective fun k : Fin l.length => (l.take (k + 1)).sum :=
  ⟨[2, 3, 5, 4], by decide, by decide, by decide⟩

/-- `2, 5, 3, 4` has partial sums `2, 0, 3, 0`: the value `0` occurs twice, so it is invalid. -/
example : ¬ Function.Injective fun k : Fin ([2, 5, 3, 4] : List (ZMod 7)).length =>
    (([2, 5, 3, 4] : List (ZMod 7)).take (k + 1)).sum := by
  decide

/-- In `l.take (k + 1)` the addition `k + 1` is in `ℕ` (not modulo `l.length`):
the last partial sum of `[1, 2]` is `3`, not the empty sum `0`. -/
example (l : List ℕ) (k : Fin l.length) : l.take (k + 1) = l.take ((k : ℕ) + 1) := rfl

example : (fun k : Fin ([1, 2] : List ℕ).length => (([1, 2] : List ℕ).take (k + 1)).sum)
    ⟨1, by decide⟩ = 3 := by decide

end GrahamPM
