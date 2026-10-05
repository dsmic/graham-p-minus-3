import GrahamPM.Basic
import GrahamPM.Small
import GrahamPM.Lift
import GrahamPM.CycleEvenGen
import GrahamPM.CycleOddGen

/-!
# Proof of the two theorems of `Challenge.lean`

Assembly: small `m ≤ 23` (L4), or the cycle `Z_r` (L3) + lifting (L2); then dilation (L1).
The statements are literally those of `Challenge.lean` (checked in `Check.lean`).
-/

namespace GrahamPM.Solution

open GrahamPM

/-- Even `r = 2h`, `h ≥ 6`, i.e. `m = 4h + 3`. -/
lemma big_even {m h : ℕ} [NeZero m] (hm : m = 4 * h + 3) (hh : 6 ≤ h) :
    ∃ l : List (ZMod m), Valid (Finset.univ \ {0, 1, -1}) l := by
  refine ⟨_, lift (r := 2 * h) (by omega) (by omega) (fe h) (de h) ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro p hp; have := fe_lt hh (show p < 4 * h by omega); omega
  · intro p q hp hq he; exact fe_inj hh (by omega) (by omega) he
  · intro p hp; have := de_range hh (show p < 4 * h by omega); push_cast; omega
  · intro p q hp hq he; exact de_inj hh (by omega) (by omega) he
  · intro p hp; exact fe_step hh (by omega)
  · have := fe_last hh; rw [show 2 * (2 * h) - 1 = 4 * h - 1 by omega]; exact this

/-- Odd `r = 2s + 1`, `s ≥ 5`, i.e. `m = 4s + 5`. -/
lemma big_odd {m s : ℕ} [NeZero m] (hm : m = 4 * s + 5) (hs : 5 ≤ s) :
    ∃ l : List (ZMod m), Valid (Finset.univ \ {0, 1, -1}) l := by
  refine ⟨_, lift (r := 2 * s + 1) (by omega) (by omega) (fo s) (dso s) ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro p hp; have := fo_lt hs (show p < 4 * s + 2 by omega); omega
  · intro p q hp hq he; exact fo_inj hs (by omega) (by omega) he
  · intro p hp; have := dso_range hs (show p < 4 * s + 2 by omega); push_cast; omega
  · intro p q hp hq he; exact dso_inj hs (by omega) (by omega) he
  · intro p hp; exact fo_step hs (by omega)
  · have := fo_last hs; rw [show 2 * (2 * s + 1) - 1 = 4 * s + 2 - 1 by omega]; exact this

/-- The case `x = 1`, for every odd `m`. -/
lemma case_one (m : ℕ) [NeZero m] (hm : Odd m) :
    ∃ l : List (ZMod m), Valid (Finset.univ \ {0, 1, -1}) l := by
  by_cases hle : m ≤ 23
  · exact small_case m hm hle
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨h, hk | hk⟩ := Nat.even_or_odd' k
  · -- k = 2h, so m = 4h + 1 = 2r + 3 with r = 2h - 1 odd: r = 2s + 1, s = h - 1
    subst hk
    exact big_odd (s := h - 1) (by omega) (by omega)
  · -- k = 2h + 1, so m = 4h + 3 with r = 2h even
    subst hk
    exact big_even (h := h) (by omega) (by omega)

theorem graham_punctured_pm {m : ℕ} [NeZero m] (hm : Odd m) (x : ZMod m) (hx : IsUnit x) :
    ∃ l : List (ZMod m), l.Nodup ∧ l.toFinset = Finset.univ \ {0, x, -x} ∧
      Function.Injective fun k : Fin l.length => (l.take (k + 1)).sum := by
  obtain ⟨l, hl⟩ := case_one m hm
  have := valid_map_mul hx hl
  rw [image_mul_univ_sdiff hx] at this
  exact ⟨_, this⟩

/-- The sum of all elements of `ℤ_p` is `0` for odd primes `p`. -/
lemma sum_univ_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : ∑ a : ZMod p, a = 0 := by
  have hneg : ∑ a : ZMod p, a = ∑ a : ZMod p, -a :=
    (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun a => rfl)).symm
  have h1 : ∑ a : ZMod p, -a = -∑ a : ZMod p, a := Finset.sum_neg_distrib (f := fun a => a)
  rw [h1] at hneg
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this
    exact hp2 this
  have : (2 : ZMod p) * ∑ a : ZMod p, a = 0 := by
    rw [two_mul]; nth_rewrite 2 [hneg]; exact add_neg_cancel _
  exact (mul_eq_zero.mp this).resolve_left h2

theorem graham_p_minus_three {p : ℕ} [Fact p.Prime] (S : Finset (ZMod p))
    (h0 : (0 : ZMod p) ∉ S) (hcard : S.card = p - 3) (hsum : ∑ s ∈ S, s = 0) :
    ∃ l : List (ZMod p), l.Nodup ∧ l.toFinset = S ∧
      Function.Injective fun k : Fin l.length => (l.take (k + 1)).sum := by
  have hp := (Fact.out : p.Prime)
  by_cases hsmall : p ≤ 3
  · have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hS
    exact ⟨[], by simp, by simp, fun a => a.elim0⟩
  have hp2 : p ≠ 2 := by omega
  -- the complement of S ∪ {0} has exactly two elements y, z
  have hT : (Finset.univ \ insert 0 S).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card,
      Finset.card_insert_of_notMem h0, hcard]
    omega
  obtain ⟨y, z, hyz, hT2⟩ := Finset.card_eq_two.mp hT
  have hy : y ∈ Finset.univ \ insert 0 S := by rw [hT2]; simp
  have hz : z ∈ Finset.univ \ insert 0 S := by rw [hT2]; simp
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, true_and, not_or] at hy hz
  -- partition of ℤ_p: {0} ∪ S ∪ {y, z}
  have hpart : ∀ a : ZMod p, a = 0 ∨ a ∈ S ∨ a = y ∨ a = z := by
    intro a
    by_cases ha : a ∈ insert 0 S
    · rw [Finset.mem_insert] at ha; tauto
    · have : a ∈ Finset.univ \ insert 0 S := by simp [ha]
      rw [hT2] at this; simp at this; tauto
  -- sum: 0 = Σ S + y + z
  have hall := sum_univ_zmod (p := p) hp2
  have hdecomp : (Finset.univ : Finset (ZMod p)) = insert 0 (insert y (insert z S)) := by
    ext a; simp only [Finset.mem_univ, Finset.mem_insert, true_iff]; rcases hpart a with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  rw [hdecomp, Finset.sum_insert (by simp only [Finset.mem_insert, not_or]; exact ⟨Ne.symm hy.1, Ne.symm hz.1, h0⟩),
    Finset.sum_insert (by simp [hyz, hy.2]), Finset.sum_insert hz.2, hsum] at hall
  have hzy : z = -y := by
    have : y + z = 0 := by simpa [add_comm, add_assoc] using hall
    exact (neg_eq_of_add_eq_zero_right this).symm
  -- S = univ \ {0, y, -y}
  have hSeq : S = Finset.univ \ {0, y, -y} := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or]
    constructor
    · intro ha
      refine ⟨fun h => h0 (h ▸ ha), fun h => hy.2 (h ▸ ha), fun h => hz.2 (hzy ▸ h ▸ ha)⟩
    · rintro ⟨ha0, hay, haz⟩
      rcases hpart a with h | h | h | h
      · exact absurd h ha0
      · exact h
      · exact absurd h hay
      · exact absurd (h.trans hzy) haz
  have hyu : IsUnit y := isUnit_iff_ne_zero.mpr hy.1
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [hSeq]
  exact graham_punctured_pm hodd y hyu

end GrahamPM.Solution
