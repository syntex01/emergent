import Mathlib

namespace Zeta70Barrier

noncomputable section

/-!
This file verifies two exact obstruction statements for the proposed
fourth-moment route to a strict 70% lower bound for simple critical-line
zeta zeros.

It deliberately does not state an unconditional theorem about zeta zeros.
The analytic determinant/thin-strip estimate is not present here.
-/

/-- A normalized spectral summary containing only the zero-side fractions and
first three moments used by the proposed low-moment route. -/
structure ThreeMomentSummary where
  simpleFraction : ℝ
  pairFraction : ℝ
  m1 : ℝ
  m2 : ℝ
  m3 : ℝ

/-- The exact three-point witness: mass `2/3` at `1`, mass `1/6` at `2`,
and mass `1/6` at `0`. -/
def threeMomentWitness : ThreeMomentSummary where
  simpleFraction := 2 / 3
  pairFraction := 1 / 6
  m1 := (2 / 3 : ℝ) * 1 + (1 / 6 : ℝ) * 2 + (1 / 6 : ℝ) * 0
  m2 := (2 / 3 : ℝ) * 1 ^ 2 + (1 / 6 : ℝ) * 2 ^ 2 + (1 / 6 : ℝ) * 0 ^ 2
  m3 := (2 / 3 : ℝ) * 1 ^ 3 + (1 / 6 : ℝ) * 2 ^ 3 + (1 / 6 : ℝ) * 0 ^ 3

/-- The witness satisfies the normalized zero-side ledger and the target first
three moments exactly. -/
theorem threeMomentWitness_exact :
    threeMomentWitness.simpleFraction = (2 / 3 : ℝ) ∧
    threeMomentWitness.pairFraction = (1 / 6 : ℝ) ∧
    threeMomentWitness.simpleFraction + 2 * threeMomentWitness.pairFraction = 1 ∧
    threeMomentWitness.m1 = 1 ∧
    threeMomentWitness.m2 = 4 / 3 ∧
    threeMomentWitness.m3 = 2 := by
  norm_num [threeMomentWitness]

/-- Any universal lower bound that uses only the abstract zero-side ledger and
these first three moment values can be no larger than `2/3`, because the
explicit witness is admissible. -/
theorem first_three_moments_ceiling
    {C : ℝ}
    (hUniversal :
      ∀ D : ThreeMomentSummary,
        0 ≤ D.simpleFraction →
        0 ≤ D.pairFraction →
        D.simpleFraction + 2 * D.pairFraction ≤ 1 →
        D.m1 = 1 → D.m2 = 4 / 3 → D.m3 = 2 →
        C ≤ D.simpleFraction) :
    C ≤ 2 / 3 := by
  have h := threeMomentWitness_exact
  exact hUniversal threeMomentWitness (by norm_num [threeMomentWitness])
    (by norm_num [threeMomentWitness]) (by norm_num [threeMomentWitness])
    h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

/-! ## Exact sharpness of the fourth-moment error budget -/

/-- First moment of the four-point sharpness distribution. -/
theorem sharp_first_moment (a : ℝ) :
    (7 / 20 : ℝ) * (1 - a) +
      (7 / 20 : ℝ) * (1 + a) +
      (3 / 20 : ℝ) * 2 +
      (3 / 20 : ℝ) * 0 = 1 := by
  ring

/-- Second moment of the four-point sharpness distribution. -/
theorem sharp_second_moment {a : ℝ} (ha : a ^ 2 = (1 / 21 : ℝ)) :
    (7 / 20 : ℝ) * (1 - a) ^ 2 +
      (7 / 20 : ℝ) * (1 + a) ^ 2 +
      (3 / 20 : ℝ) * 2 ^ 2 +
      (3 / 20 : ℝ) * 0 ^ 2 = 4 / 3 := by
  have hpair : (1 - a) ^ 2 + (1 + a) ^ 2 = 2 + 2 * a ^ 2 := by ring
  rw [← mul_add, hpair, ha]
  norm_num

/-- Third moment of the four-point sharpness distribution. -/
theorem sharp_third_moment {a : ℝ} (ha : a ^ 2 = (1 / 21 : ℝ)) :
    (7 / 20 : ℝ) * (1 - a) ^ 3 +
      (7 / 20 : ℝ) * (1 + a) ^ 3 +
      (3 / 20 : ℝ) * 2 ^ 3 +
      (3 / 20 : ℝ) * 0 ^ 3 = 2 := by
  have hpair : (1 - a) ^ 3 + (1 + a) ^ 3 = 2 + 6 * a ^ 2 := by ring
  rw [← mul_add, hpair, ha]
  norm_num

/-- Fourth moment of the four-point sharpness distribution. -/
theorem sharp_fourth_moment {a : ℝ} (ha : a ^ 2 = (1 / 21 : ℝ)) :
    (7 / 20 : ℝ) * (1 - a) ^ 4 +
      (7 / 20 : ℝ) * (1 + a) ^ 4 +
      (3 / 20 : ℝ) * 2 ^ 4 +
      (3 / 20 : ℝ) * 0 ^ 4 = 208 / 63 := by
  have ha4 : a ^ 4 = (1 / 21 : ℝ) ^ 2 := by
    calc
      a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = (1 / 21 : ℝ) ^ 2 := by rw [ha]
  have hpair :
      (1 - a) ^ 4 + (1 + a) ^ 4 = 2 + 12 * a ^ 2 + 2 * a ^ 4 := by
    ring
  rw [← mul_add, hpair, ha, ha4]
  norm_num

/-- The centered fourth moment of the sharpness distribution. -/
theorem sharp_centered_fourth {a : ℝ} (ha : a ^ 2 = (1 / 21 : ℝ)) :
    (7 / 20 : ℝ) * (-a) ^ 4 +
      (7 / 20 : ℝ) * a ^ 4 +
      (3 / 20 : ℝ) * 1 ^ 4 +
      (3 / 20 : ℝ) * (-1) ^ 4 = 19 / 63 := by
  have ha4 : a ^ 4 = (1 / 21 : ℝ) ^ 2 := by
    calc
      a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = (1 / 21 : ℝ) ^ 2 := by rw [ha]
  rw [show (-a) ^ 4 = a ^ 4 by ring, ha4]
  norm_num

/-- The sharp centered fourth moment corresponds exactly to the analytic error
budget `Δ = 11/630`. -/
theorem sharp_delta_identity :
    ((19 / 63 : ℝ) - 4 / 15) / 2 = 11 / 630 := by
  norm_num

/-- The repaired scalar endgame equals exactly 70% at the sharp threshold. -/
theorem endgame_at_sharp_threshold :
    ((1 - (1 / 3 : ℝ)) ^ 2) /
      (1 - 2 * (1 / 3 : ℝ) + 19 / 63) = 7 / 10 := by
  norm_num

/-- Therefore a strict 70% conclusion through this endgame requires a strict
improvement over `Δ = 11/630`. -/
theorem strict_seventy_requires_strict_delta
    {Δ : ℝ}
    (hformula :
      ((1 - (1 / 3 : ℝ)) ^ 2) /
        (1 - 2 * (1 / 3 : ℝ) + 4 / 15 + 2 * Δ) > 7 / 10)
    (hden : 0 < 1 - 2 * (1 / 3 : ℝ) + 4 / 15 + 2 * Δ) :
    Δ < 11 / 630 := by
  norm_num at hformula hden ⊢
  field_simp at hformula
  nlinarith

#print axioms first_three_moments_ceiling
#print axioms sharp_fourth_moment
#print axioms sharp_delta_identity
#print axioms endgame_at_sharp_threshold
#print axioms strict_seventy_requires_strict_delta

end

end Zeta70Barrier
