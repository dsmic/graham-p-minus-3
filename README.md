# Graham's rearrangement conjecture for sets of size p − 3 with sum zero

Graham's rearrangement conjecture (1971) states that for every prime p, the elements of any set
A ⊆ ℤ_p ∖ {0} can be ordered so that all partial sums a₁, a₁ + a₂, …, a₁ + ⋯ + a_|A| are pairwise
distinct.

For sets of size p − 3, the case of **sum ≠ 0** was settled by Hicks, Ollis and Schmitt (2019). The
case of **sum 0** remained open; it is listed as open by Kravitz (2024). This repository closes it:

> **Theorem.** Let m be odd and x ∈ ℤ_m coprime to m. Then ℤ_m ∖ {0, x, −x} has an ordering with
> pairwise distinct partial sums.
>
> **Corollary.** For every prime p, every S ⊆ ℤ_p ∖ {0} with |S| = p − 3 and ΣS = 0 has an ordering
> with pairwise distinct partial sums. Together with the known cases, Graham's conjecture therefore
> holds for **all** A ⊆ ℤ_p ∖ {0} with |A| ≥ p − 3.

The proof is an explicit construction. It is written up in [`proof.md`](proof.md) and **formalized in
Lean 4 with Mathlib** ([`lean/`](lean/)); the formal proof depends only on Lean's standard axioms.

## Contents

| path | content |
|---|---|
| [`proof.md`](proof.md) | the proof (about three pages) |
| [`example.md`](example.md) | two examples: p = 43 in full, and the 39-digit prime p = 2¹²⁷ − 1 |
| [`lean/`](lean/) | the formal proof (Lean 4 + Mathlib) |
| [`python/`](python/) | the construction and numerical cross-checks (not needed for the proof) |
| [`figures/`](figures/) | the figures |

## The idea in a nutshell

1. **Dilation.** Multiplying by x⁻¹ reduces everything to x = 1, i.e. to A = {2, 3, …, m − 2}.
2. **Lifting.** Write m = 2r + 3. It suffices to find a closed walk ("a frog") on the integers
   0, 1, …, 2r − 1 that visits every point once and uses every jump length 2, …, r + 1 exactly once to
   the right and once to the left. Read modulo m, its jumps are the required ordering, and its
   positions are the partial sums.
3. **Construction.** Such a walk is given explicitly: two zigzags plus 18 connecting arcs, with one
   formula for even and one for odd r (r ≥ 11). The small cases m ≤ 23 are listed in a table.

![The cycle Z_r](figures/cycle.svg)

## Checking the formal proof

**What has to be read by a human:** only [`lean/GrahamPM/Challenge.lean`](lean/GrahamPM/Challenge.lean).
It contains the two statements, with `sorry` in place of the proofs, so that they can be read on their
own. "Valid ordering" is phrased exactly as in the Lean formalization of Pham–Sauermann
([vltanh/lean4-graham-rearrangement-conjecture](https://github.com/vltanh/lean4-graham-rearrangement-conjecture)):

```lean
∃ l : List (ZMod m), l.Nodup ∧ l.toFinset = Finset.univ \ {0, x, -x} ∧
  Function.Injective fun k : Fin l.length => (l.take (k + 1)).sum
```

Everything else is checked by the Lean kernel:
- [`Check.lean`](lean/GrahamPM/Check.lean) confirms by `rfl` that the theorems proved in
  `Solution.lean` have exactly the types of the statements in `Challenge.lean`, and prints their axioms.
- [`Sanity.lean`](lean/GrahamPM/Sanity.lean) checks on small examples that the formal statement means
  what is intended, e.g. that `k + 1` is computed in ℕ, so the last partial sum is not silently
  replaced by the empty sum.

**How to build** (Linux/macOS; tested with Lean v4.35.0-rc3 and Mathlib v4.35.0-rc3, pinned in
`lean/lake-manifest.json`):

```bash
# 1. install the Lean toolchain manager elan (once)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# 2. download the precompiled Mathlib (several GB) and build
cd lean
lake exe cache get
lake build
```

The build takes one to two minutes. Expected result: `Build completed successfully`, the two
intended `declaration uses 'sorry'` warnings from `Challenge.lean`, and

```
'GrahamPM.Solution.graham_punctured_pm' depends on axioms: [propext, Classical.choice, Quot.sound]
'GrahamPM.Solution.graham_p_minus_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the standard axioms of Lean and Mathlib; in particular there is no `sorryAx`, and no
`native_decide` (`Lean.ofReduceBool`) is used.

**Structure of the formal proof** (it follows [`proof.md`](proof.md)):

| file | content | section of proof.md |
|---|---|---|
| `Basic.lean` | the notion `Valid`; dilation by a unit (L1) | 1 |
| `Lift.lean` | lifting a cycle on {0, …, 2r−1} to an ordering in ℤ_{2r+3} (L2) | 1, Lemma 1 |
| `CycleEvenGen.lean`, `CycleOddGen.lean` | the cycle Z_r: vertex and jump at each position, range, injectivity, step equation (L3) | 2, 3 |
| `Small.lean` | the cases m ≤ 23, checked by `decide` (L4) | 4 |
| `Solution.lean` | assembly of the theorem and of the corollary | 1, 5 |

The two `Cycle…Gen.lean` files are produced by [`lean/scripts/gen_cycle.py`](lean/scripts/gen_cycle.py):
- each piece of the piecewise-linear vertex and jump functions gets an evaluation lemma, proved only
  by `rw` with `if_pos`/`if_neg`, each condition by `omega`;
- the main lemmas are case analyses closed by `omega`.

The generator does not have to be trusted, since Lean checks the generated proofs. To regenerate:
`cd lean && python3 scripts/gen_cycle.py && lake build`.

## Numerical cross-checks (optional)

Plain Python 3, no extra packages (figures: matplotlib).

```bash
cd python
python3 construction.py 2000         # the cycle Z_r for r = 9..2000; orderings in Z_m for all units x
python3 check_proof_tables.py 2000   # the statements of proof.md, Section 3, literally for r = 11..2000
python3 small_cases.py               # the table of proof.md, Section 4
python3 example.py                   # the data of example.md
python3 figures.py                   # the figures
```

## Literature and novelty

- **Sum ≠ 0, size p − 3:** J. Hicks, M. A. Ollis, J. R. Schmitt, *Distinct partial sums in cyclic
  groups: polynomial method and constructive approaches*, J. Combin. Des. 27 (2019), arXiv:1809.02684,
  Theorem 4.6, proved for Alspach's version.
  - Their proof explicitly assumes x ≠ −y: "if x = −y then the sum of the elements in
    ℤ_p ∖ {0, x, y} is 0".
  - Their method removes two adjacent elements from a rotational sequencing. It cannot produce the
    pair x, −x, because two adjacent steps x, −x would revisit a point.
- **Status as of 2024:** N. Kravitz, *Rearranging small sets for distinct partial sums*, Integers 24
  (2024), arXiv:2407.01835: Graham's conjecture "holds when |A| ≤ 12 … and when A is a non-zero sum set
  of size p − 2 or p − 3". The surveys say the same:
  - Costa, Della Fiore, Ollis, Rovner-Frydman, EJC 29(3) (2022), Theorem 1.3;
  - Ollis, *Sequenceable groups and related topics*, EJC DS10v3 (2025), Theorem 39: "k = n − 3 when
    … ΣS ≠ 0".
- **Imprecise secondary summaries:** some summaries attribute "p − 3 ≤ |A| ≤ p − 1" to Hicks–Ollis–
  Schmitt without the restriction to sum ≠ 0, e.g. erdosproblems.com, problem 475, and Bucić et al.,
  arXiv:2503.01825.
- **Large p:** for all sufficiently large primes, without an explicit bound, the case follows from the
  asymptotic results:
  - Müyesser–Pokrovskiy, arXiv:2204.09666;
  - Bedert–Bucić–Kravitz–Montgomery–Müyesser, arXiv:2508.18254;
  - Pham–Sauermann, arXiv:2602.15797.

  The construction here is explicit and covers every prime, and every odd modulus m when x is a unit.
- **Small cases by computer:** all sets for n ≤ 25 (Archdeacon, Dinitz, Mattern, Stinson); zero-sum sets
  with |A| ≤ 22 (Costa, Della Fiore, Fontana, Vena, arXiv:2603.20961).

The literature search (October 2026) was careful but cannot be exhaustive.

## Remarks

- **A family of size p − 4 (Alspach's version).** The ordering is cyclic, so one may start anywhere.
  Putting any element a last and dropping it gives an ordering of ℤ_p ∖ {0, x, −x, a} whose partial
  sums are pairwise distinct and nonzero. This settles Alspach's conjecture for all sets of size p − 4
  whose complement contains a pair ±x. The general case p − 4 remains open.
- **Graceful digraphs.** In the sense of Bloom and Hsu, the construction gives a graceful labelling of
  the disjoint union of a directed cycle of length 2r and a directed 2-cycle, C_{2r} ∪ C₂ (modulo
  2r + 3), for every r ≥ 9; by computer search also for r = 1 and 3 ≤ r ≤ 8. For r = 2, C₄ ∪ C₂ is not
  graceful: all 5040 labellings were checked.
- **Not covered:** composite m with x not coprime to m.

## Notes

The construction was found by computer experiments, using exhaustive searches and CP-SAT. The Lean
formalization was written with the help of an AI assistant (Claude).

