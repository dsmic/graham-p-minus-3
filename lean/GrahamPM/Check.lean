import GrahamPM.Challenge
import GrahamPM.Solution

/-!
# Matching the statements, and the axiom check

* The theorems proved in `Solution.lean` have exactly the types of the statements in
  `Challenge.lean` (otherwise the equations below would not type-check; `rfl` then holds by proof
  irrelevance).
* `#print axioms` shows what the proofs rely on. Expected output: `[propext, Classical.choice,
  Quot.sound]` – the standard axioms of Lean/Mathlib, no `sorryAx`.
-/

example : @GrahamPM.graham_punctured_pm = @GrahamPM.Solution.graham_punctured_pm := rfl
example : @GrahamPM.graham_p_minus_three = @GrahamPM.Solution.graham_p_minus_three := rfl

#print axioms GrahamPM.Solution.graham_punctured_pm
#print axioms GrahamPM.Solution.graham_p_minus_three
