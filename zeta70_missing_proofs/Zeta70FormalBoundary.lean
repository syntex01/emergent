import Mathlib
import Zeta70MissingProofs

/-!
# Zeta70 formal trust boundary

This module kernel-checks the finite aggregation step and the complete scalar
implication from a genuine hard-channel estimate to a strict seventy-percent
lower bound. It deliberately exposes the analytic strip estimate as data and
does not conceal it behind a new primitive assumption.
-/

namespace Zeta70FormalBoundary

open scoped BigOperators
open Filter

noncomputable section

/-! ## Finite weighted aggregation -/

/-- Weighted Cauchy--Schwarz in the exact squared form used after aggregating
all short-factor moduli before applying Cauchy--Schwarz. -/
theorem weighted_cauchy_schwarz_sq
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x y : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * x i * y i) ^ 2 ≤
      (∑ i ∈ s, w i * x i ^ 2) * (∑ i ∈ s, w i * y i ^ 2) := by
  let f : ι → ℝ := fun i => Real.sqrt (w i) * x i
  let g : ι → ℝ := fun i => Real.sqrt (w i) * y i
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) s f g
  have hfg : (∑ i ∈ s, f i * g i) = ∑ i ∈ s, w i * x i * y i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f, g]
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
    ring
  have hff : (∑ i ∈ s, f i ^ 2) = ∑ i ∈ s, w i * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hgg : (∑ i ∈ s, g i ^ 2) = ∑ i ∈ s, w i * y i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  simpa [hfg, hff, hgg] using hcs

/-- Abstract transfer lemma: once the two globally aggregated square sums have
bounds `A` and `B`, the cross term has the exact geometric-mean bound. -/
theorem aggregate_cross_term_sq_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x y : ι → ℝ) (A B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : (∑ i ∈ s, w i * x i ^ 2) ≤ A)
    (hB : (∑ i ∈ s, w i * y i ^ 2) ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    (∑ i ∈ s, w i * x i * y i) ^ 2 ≤ A * B := by
  calc
    (∑ i ∈ s, w i * x i * y i) ^ 2
        ≤ (∑ i ∈ s, w i * x i ^ 2) * (∑ i ∈ s, w i * y i ^ 2) :=
          weighted_cauchy_schwarz_sq s w x y hw
    _ ≤ A * B := mul_le_mul hA hB (Finset.sum_nonneg fun i hi =>
          mul_nonneg (hw i hi) (sq_nonneg (y i))) hA0

/-- The reciprocal scale ratios appearing in the two multiplicity estimates
cancel exactly before the square root is taken. -/
theorem reciprocal_scale_ratio_cancel
    {B₁ B₂ : ℝ} (hB₁ : B₁ ≠ 0) (hB₂ : B₂ ≠ 0) :
    (B₂ / B₁) * (B₁ / B₂) = 1 := by
  field_simp

/-! ## Explicit analytic certificate interface -/

/-- An eventual lower bound for a numerator relative to a nonnegative
normalizing count. This is the filter-level form of a liminf lower bound. -/
def EventuallyProportionAtLeast
    (p : ℝ) (num den : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop, (p - ε) * den n ≤ num n

/-- This structure is the entire remaining analytic trust boundary. Producing
it for the actual zeta/Gabor quantities requires the exact hard-channel strip
estimate; no constructor is supplied in this module. -/
structure AnalyticCertificate (num den : ℕ → ℝ) where
  delta : ℝ
  delta_nonneg : 0 ≤ delta
  delta_lt_threshold : delta < 11 / 630
  denominator_nonneg : ∀ᶠ n in atTop, 0 ≤ den n
  detector_output : EventuallyProportionAtLeast
    (Zeta70MissingProofs.simpleZeroBound delta) num den

/-- A genuine analytic certificate below the sharp threshold yields the
strict seventy-percent lower bound, with no additional mathematical
hypothesis. -/
theorem certificate_implies_seventy_percent
    {num den : ℕ → ℝ} (C : AnalyticCertificate num den) :
    EventuallyProportionAtLeast (7 / 10 : ℝ) num den := by
  have hgt : (7 / 10 : ℝ) < Zeta70MissingProofs.simpleZeroBound C.delta :=
    Zeta70MissingProofs.hard_error_below_threshold_gives_gt_seventy
      C.delta_nonneg C.delta_lt_threshold
  intro ε hε
  let η : ℝ := min (ε / 2)
    ((Zeta70MissingProofs.simpleZeroBound C.delta - 7 / 10) / 2)
  have hη : 0 < η := by
    apply lt_min
    · linarith
    · dsimp [η]
      linarith
  have hcoeff :
      (7 / 10 : ℝ) - ε ≤
        Zeta70MissingProofs.simpleZeroBound C.delta - η := by
    dsimp [η]
    have hηε : η ≤ ε / 2 := min_le_left _ _
    linarith
  filter_upwards [C.detector_output η hη, C.denominator_nonneg] with n hn hden
  exact (mul_le_mul_of_nonneg_right hcoeff hden).trans hn

/-- At zero hard excess the scalar detector gives the stronger constant
`20/27`. -/
theorem zero_excess_bound :
    Zeta70MissingProofs.simpleZeroBound 0 = 20 / 27 := by
  norm_num [Zeta70MissingProofs.simpleZeroBound]

/-- The stronger zero-excess constant is strictly above seventy percent. -/
theorem zero_excess_strictly_above_seventy :
    (7 / 10 : ℝ) < Zeta70MissingProofs.simpleZeroBound 0 := by
  norm_num [Zeta70MissingProofs.simpleZeroBound]

#print axioms weighted_cauchy_schwarz_sq
#print axioms aggregate_cross_term_sq_le
#print axioms reciprocal_scale_ratio_cancel
#print axioms certificate_implies_seventy_percent
#print axioms zero_excess_strictly_above_seventy

end

end Zeta70FormalBoundary
