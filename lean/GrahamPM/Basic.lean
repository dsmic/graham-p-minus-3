import Mathlib

/-!
# Basic notions and dilation (Lemma L1)
-/

namespace GrahamPM

/-- `l` is a valid ordering of `S` (same wording as in `Challenge.lean`). -/
def Valid {G : Type*} [AddMonoid G] [DecidableEq G] (S : Finset G) (l : List G) : Prop :=
  l.Nodup ∧ l.toFinset = S ∧ Function.Injective fun k : Fin l.length => (l.take (k + 1)).sum

/-- Pairwise distinct partial sums, with natural-number indices. -/
def PSInj {G : Type*} [AddMonoid G] (l : List G) : Prop :=
  ∀ i j, i < l.length → j < l.length → (l.take (i + 1)).sum = (l.take (j + 1)).sum → i = j

lemma injective_iff_psinj {G : Type*} [AddMonoid G] (l : List G) :
    (Function.Injective fun k : Fin l.length => (l.take (k + 1)).sum) ↔ PSInj l := by
  constructor
  · intro h i j hi hj he
    exact congrArg Fin.val (@h ⟨i, hi⟩ ⟨j, hj⟩ he)
  · intro h a b he
    exact Fin.ext (h a b a.2 b.2 he)

/-- **L1 (dilation).** Multiplication by a unit preserves valid orderings. -/
lemma valid_map_mul {R : Type*} [Ring R] [DecidableEq R] {u : R} (hu : IsUnit u)
    {S : Finset R} {l : List R} (h : Valid S l) :
    Valid (S.image (u * ·)) (l.map (u * ·)) := by
  obtain ⟨hnd, hS, hinj⟩ := h
  have hfi : Function.Injective (u * · : R → R) := hu.mul_right_injective
  refine ⟨hnd.map hfi, by subst hS; ext y; simp, ?_⟩
  rw [injective_iff_psinj] at hinj ⊢
  intro i j hi hj he
  rw [List.length_map] at hi hj
  apply hinj i j hi hj
  have he' : u * (l.take (i + 1)).sum = u * (l.take (j + 1)).sum := by
    rw [← List.map_take, ← List.map_take, List.sum_map_mul_left, List.sum_map_mul_left] at he
    simpa using he
  exact hfi he'

/-- The image of `univ \ {0, 1, -1}` under multiplication by a unit `x`. -/
lemma image_mul_univ_sdiff {R : Type*} [Ring R] [Fintype R] [DecidableEq R] {x : R}
    (hx : IsUnit x) :
    (Finset.univ \ {0, 1, -1} : Finset R).image (x * ·) = Finset.univ \ {0, x, -x} := by
  have hfi : Function.Injective (x * · : R → R) := hx.mul_right_injective
  rw [Finset.image_sdiff _ _ hfi, Finset.image_univ_of_surjective
    (Finite.surjective_of_injective hfi)]
  simp [Finset.image_insert]

end GrahamPM
