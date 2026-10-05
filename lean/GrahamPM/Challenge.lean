import Mathlib

/-!
# Graham's rearrangement conjecture for `ℤ_m ∖ {0, x, -x}` — the formal statements

This is the only file whose content has to be checked by a human: it says *what* is proved.
The proof is in `Solution.lean` and is checked completely by the Lean kernel;
`Check.lean` confirms that `Solution.lean` proves exactly these statements.

The vocabulary is the same as in the Lean formalization of Pham–Sauermann
(github.com/vltanh/lean4-graham-rearrangement-conjecture, `Challenge.lean`):

* An *ordering* of `S` is a list `l` containing every element of `S` exactly once:
  `l.Nodup ∧ l.toFinset = S`.
* Its partial sums are `s₁, s₁ + s₂, …, s₁ + ⋯ + s_{|S|}`;
  the `k`-th one is `(l.take k).sum`.
* The ordering is *valid* if these partial sums are pairwise distinct:
  `Function.Injective fun k : Fin l.length => (l.take (k + 1)).sum`.

**Theorem 1.** For every odd `m` and every unit `x` of `ℤ_m`, the set `ℤ_m ∖ {0, x, -x}`
has a valid ordering.

**Theorem 2 (Graham for |S| = p − 3 with sum 0).** For every prime `p`, every set
`S ⊆ ℤ_p ∖ {0}` with `|S| = p − 3` and sum `0` has a valid ordering.
(For `p = 2, 3`, `p - 3 = 0` in `ℕ`, so `S = ∅`.)
-/

namespace GrahamPM

theorem graham_punctured_pm {m : ℕ} [NeZero m] (hm : Odd m) (x : ZMod m) (hx : IsUnit x) :
    ∃ l : List (ZMod m), l.Nodup ∧ l.toFinset = Finset.univ \ {0, x, -x} ∧
      Function.Injective fun k : Fin l.length => (l.take (k + 1)).sum := by
  sorry

theorem graham_p_minus_three {p : ℕ} [Fact p.Prime] (S : Finset (ZMod p))
    (h0 : (0 : ZMod p) ∉ S) (hcard : S.card = p - 3) (hsum : ∑ s ∈ S, s = 0) :
    ∃ l : List (ZMod p), l.Nodup ∧ l.toFinset = S ∧
      Function.Injective fun k : Fin l.length => (l.take (k + 1)).sum := by
  sorry

end GrahamPM
