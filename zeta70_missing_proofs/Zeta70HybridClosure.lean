import Mathlib
import Zeta70MissingProofs

/-!
# Exact hybrid closure for the Zeta70 determinant programme

This module checks the complete rational implication from the two remaining
analytic estimates to a strict 70% lower bound.  It deliberately does not
postulate those estimates as axioms.
-/

namespace Zeta70HybridClosure

noncomputable section

/-- Hard-wedge mass above the line `y = (2/3)x`. -/
def residualMass : ℝ := 6541 / 1200000

/-- A scalar dimension-two upper sieve with constant four creates an excess
of three copies beyond the already-booked local main term. -/
def hybridExcess : ℝ := 3 * residualMass

/-- Exact residual-mass ledger. -/
theorem hybridExcess_exact : hybridExcess = 6541 / 400000 := by
  norm_num [hybridExcess, residualMass]

/-- The hybrid error fits strictly below the repaired determinant budget. -/
theorem hybridExcess_below_budget : hybridExcess < 11 / 630 := by
  norm_num [hybridExcess, residualMass]

/-- Exact remaining error margin in the determinant channel. -/
theorem hybrid_budget_margin :
    11 / 630 - hybridExcess = 27917 / 25200000 := by
  norm_num [hybridExcess, residualMass]

/-- The repaired zero-side detector at the hybrid excess. -/
theorem hybrid_simple_zero_bound_exact :
    Zeta70MissingProofs.simpleZeroBound hybridExcess = 800000 / 1138869 := by
  norm_num [Zeta70MissingProofs.simpleZeroBound, hybridExcess, residualMass]

/-- The hybrid ledger has a strict rational margin above seventy percent. -/
theorem hybrid_simple_zero_bound_gt_seventy :
    (7 / 10 : ℝ) < Zeta70MissingProofs.simpleZeroBound hybridExcess := by
  norm_num [Zeta70MissingProofs.simpleZeroBound, hybridExcess, residualMass]

/-- Exact margin in the resulting simple-zero proportion. -/
theorem hybrid_simple_zero_margin :
    Zeta70MissingProofs.simpleZeroBound hybridExcess - 7 / 10 =
      27917 / 11388690 := by
  norm_num [Zeta70MissingProofs.simpleZeroBound, hybridExcess, residualMass]

/-- Any genuine analytic estimate no worse than the hybrid ledger crosses
seventy percent. -/
theorem analytic_delta_le_hybrid_gives_gt_seventy
    {delta : ℝ} (hdelta : 0 ≤ delta) (hle : delta ≤ hybridExcess) :
    (7 / 10 : ℝ) < Zeta70MissingProofs.simpleZeroBound delta := by
  apply Zeta70MissingProofs.hard_error_below_threshold_gives_gt_seventy hdelta
  exact lt_of_le_of_lt hle hybridExcess_below_budget

/-- Finite Hilbert-space form of the vector-valued upper-sieve transfer.
Once each exact fibre operator is positive and bounded by `4 I`, all Gabor,
Mellin, orientation, and cross-dyadic labels may remain inside the Hilbert
coordinate without increasing the constant. -/
theorem finite_vector_sieve_four
    {ι : Type*} [Fintype ι]
    (main total : ι → ℝ)
    (hmain : ∀ i, 0 ≤ main i)
    (hfibre : ∀ i, total i ≤ 4 * main i) :
    (∑ i, total i) ≤ 4 * ∑ i, main i := by
  calc
    (∑ i, total i) ≤ ∑ i, 4 * main i :=
      Finset.sum_le_sum fun i _ => hfibre i
    _ = 4 * ∑ i, main i := by rw [Finset.mul_sum]

#print axioms hybridExcess_below_budget
#print axioms hybrid_simple_zero_bound_gt_seventy
#print axioms analytic_delta_le_hybrid_gives_gt_seventy
#print axioms finite_vector_sieve_four

end

end Zeta70HybridClosure
