import GrahamPM.Basic

/-!
# Lifting (Lemma L2)

A cycle on `{0, …, n-1}` (`n = 2r`) with vertices `f p` and jumps `d p`, in which every length
`2, …, r+1` occurs exactly once to the right and once to the left, gives a valid ordering of
`ℤ_m ∖ {0, 1, -1}` (`m = 2r + 3`): the jumps, read modulo `m`.
-/

namespace GrahamPM

lemma eq_of_intCast_eq {m : ℕ} {a b : ℤ} (h : (a : ZMod m) = (b : ZMod m))
    (hab : |a - b| < m) : a = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have := Int.eq_zero_of_abs_lt_dvd h (by rwa [abs_sub_comm])
  omega

lemma telescope (f : ℕ → ℕ) (d : ℕ → ℤ) (n : ℕ)
    (hstep : ∀ p, p + 1 < n → (f (p + 1) : ℤ) = f p + d p) :
    ∀ j, j < n → ((List.range j).map d).sum = (f j : ℤ) - f 0 := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hstep j hj]; ring

theorem lift {r m : ℕ} [NeZero m] (hm : m = 2 * r + 3) (hr : 1 ≤ r) (f : ℕ → ℕ) (d : ℕ → ℤ)
    (hf_lt : ∀ p, p < 2 * r → f p < 2 * r)
    (hf_inj : ∀ p q, p < 2 * r → q < 2 * r → f p = f q → p = q)
    (hd_rng : ∀ p, p < 2 * r →
      (2 ≤ d p ∧ d p ≤ (r : ℤ) + 1) ∨ (-((r : ℤ) + 1) ≤ d p ∧ d p ≤ -2))
    (hd_inj : ∀ p q, p < 2 * r → q < 2 * r → d p = d q → p = q)
    (hstep : ∀ p, p + 1 < 2 * r → (f (p + 1) : ℤ) = f p + d p)
    (hlast : (f 0 : ℤ) = f (2 * r - 1) + d (2 * r - 1)) :
    Valid (Finset.univ \ {0, 1, -1} : Finset (ZMod m))
      ((List.range (2 * r)).map fun p => ((d p : ℤ) : ZMod m)) := by
  set n := 2 * r with hn
  set l := (List.range n).map fun p => ((d p : ℤ) : ZMod m) with hl
  have hmn : (n : ℤ) + 3 = m := by omega
  -- no duplicates
  have hnd : l.Nodup := by
    apply List.Nodup.map_on _ (List.nodup_range)
    intro p hp q hq he
    rw [List.mem_range] at hp hq
    apply hd_inj p q hp hq
    apply eq_of_intCast_eq he
    rw [abs_lt]; constructor <;> rcases hd_rng p hp with h1 | h1 <;>
      rcases hd_rng q hq with h2 | h2 <;> omega
  -- all elements lie in univ \ {0, 1, -1}
  have hsub : l.toFinset ⊆ Finset.univ \ {0, 1, -1} := by
    intro y hy
    rw [List.mem_toFinset, hl, List.mem_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [List.mem_range] at hp
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or]
    have hb := hd_rng p hp
    refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
    · have := eq_of_intCast_eq (b := 0) (by simpa using h0)
        (by rw [abs_lt]; constructor <;> rcases hb with h | h <;> omega)
      rcases hb with h | h <;> omega
    · have := eq_of_intCast_eq (b := 1) (by simpa using h1)
        (by rw [abs_lt]; constructor <;> rcases hb with h | h <;> omega)
      rcases hb with h | h <;> omega
    · have := eq_of_intCast_eq (b := -1) (by simpa using h2)
        (by rw [abs_lt]; constructor <;> rcases hb with h | h <;> omega)
      rcases hb with h | h <;> omega
  -- cardinality
  have h01 : (0 : ZMod m) ≠ 1 := by
    intro h; have := eq_of_intCast_eq (a := 0) (b := 1) (by simpa using h)
      (by rw [abs_lt]; omega); omega
  have h0m : (0 : ZMod m) ≠ -1 := by
    intro h; have := eq_of_intCast_eq (a := 0) (b := -1) (by simpa using h)
      (by rw [abs_lt]; omega); omega
  have h1m : (1 : ZMod m) ≠ -1 := by
    intro h; have := eq_of_intCast_eq (a := 1) (b := -1) (by simpa using h)
      (by rw [abs_lt]; omega); omega
  have hcard3 : ({0, 1, -1} : Finset (ZMod m)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h01, h0m]),
      Finset.card_insert_of_notMem (by simp [h1m]), Finset.card_singleton]
  have hcardS : (Finset.univ \ {0, 1, -1} : Finset (ZMod m)).card = n := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card, hcard3]; omega
  have hcardl : l.toFinset.card = n := by
    rw [List.toFinset_card_of_nodup hnd, hl, List.length_map, List.length_range]
  have hS : l.toFinset = Finset.univ \ {0, 1, -1} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardS, hcardl])
  refine ⟨hnd, hS, ?_⟩
  -- partial sums
  rw [injective_iff_psinj]
  have hsum : ∀ k, k < n → (l.take (k + 1)).sum =
      ((if k + 1 < n then (f (k + 1) : ℤ) - f 0 else 0 : ℤ) : ZMod m) := by
    intro k hk
    rw [hl, ← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
    have hc : ((List.range (k + 1)).map fun p => ((d p : ℤ) : ZMod m)).sum =
        ((((List.range (k + 1)).map d).sum : ℤ) : ZMod m) := by
      rw [Int.cast_list_sum, List.map_map]; rfl
    rw [hc]
    split_ifs with hk1
    · rw [telescope f d n hstep (k + 1) hk1]
    · have hkn : k + 1 = n := by omega
      rw [hkn, show n = (n - 1) + 1 by omega, List.range_succ, List.map_append, List.sum_append,
        telescope f d n hstep (n - 1) (by omega)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [show (f (n - 1) : ℤ) - f 0 + d (n - 1) = 0 by rw [hn] at hlast ⊢; omega]
  intro i j hi hj he
  rw [List.length_map, List.length_range] at hi hj
  rw [hsum i hi, hsum j hj] at he
  have hfb : ∀ t, t < n → 0 ≤ (f t : ℤ) ∧ (f t : ℤ) < n := fun t ht => ⟨by omega, by
    have := hf_lt t ht; omega⟩
  have h0 := hfb 0 (by omega)
  split_ifs at he with hi1 hj1 hj1
  · have hi' := hfb (i + 1) hi1; have hj' := hfb (j + 1) hj1
    have := eq_of_intCast_eq he (by rw [abs_lt]; omega)
    have := hf_inj (i + 1) (j + 1) hi1 hj1 (by omega)
    omega
  · have hi' := hfb (i + 1) hi1
    have := eq_of_intCast_eq he (by rw [abs_lt]; omega)
    have := hf_inj (i + 1) 0 hi1 (by omega) (by omega)
    omega
  · have hj' := hfb (j + 1) hj1
    have := eq_of_intCast_eq he (by rw [abs_lt]; omega)
    have := hf_inj 0 (j + 1) (by omega) hj1 (by omega)
    omega
  · omega

end GrahamPM
