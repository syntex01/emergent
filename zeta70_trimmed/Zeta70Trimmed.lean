import Mathlib

namespace Zeta70Trimmed

noncomputable section

/-!
This file kernel-checks the exact scalar algebra behind a rank-trimmed
quartic detector.  It does not postulate the remaining analytic theorem.
-/

/--
Pure scalar rearrangement behind the rank-trimmed detector theorem.

`master` is `c² (n - s) ≤ n A + 4 c (r + n τ)`.
-/
theorem trimmed_detector_rearrangement
    {N n r s c A τ : ℝ}
    (hN : 0 < N)
    (hc : 0 < c)
    (master : c ^ 2 * (n - s) ≤ n * A + 4 * c * (r + n * τ)) :
    n / N * (1 - A / c ^ 2 - 4 * τ / c) - 4 * r / (c * N) ≤ s / N := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hdiv :
      n - s ≤ (n * A + 4 * c * (r + n * τ)) / c ^ 2 := by
    exact (le_div_iff₀ hc2).2 master
  have hs :
      n - (n * A + 4 * c * (r + n * τ)) / c ^ 2 ≤ s := by
    linarith
  have hid :
      n / N * (1 - A / c ^ 2 - 4 * τ / c) - 4 * r / (c * N)
        =
      (n - (n * A + 4 * c * (r + n * τ)) / c ^ 2) / N := by
    field_simp [ne_of_gt hN, ne_of_gt hc]
    ring
  rw [hid]
  exact (div_le_div_iff_of_pos_right hN).2 hs

/-- Optimizing parameter for variance `1/3` and fourth moment `4/15 + 2Δ`. -/
def sigmaOpt (Δ : ℝ) : ℝ := 1 / 10 - 3 * Δ

def cOpt (Δ : ℝ) : ℝ := 1 - sigmaOpt Δ

theorem cOpt_eq (Δ : ℝ) : cOpt Δ = 9 / 10 + 3 * Δ := by
  unfold cOpt sigmaOpt
  ring

/-- Exact optimized scalar identity. -/
theorem optimized_trimmed_identity
    {Δ : ℝ}
    (hc : cOpt Δ ≠ 0)
    (hden : 27 + 90 * Δ ≠ 0) :
    1 -
        ((sigmaOpt Δ) ^ 2
          - 2 * sigmaOpt Δ * (1 / 3 : ℝ)
          + (4 / 15 + 2 * Δ)) /
          (cOpt Δ) ^ 2
      =
    20 / (27 + 90 * Δ) := by
  unfold sigmaOpt cOpt at *
  field_simp [hc, hden]
  ring

/-- Exact threshold for a strict seventy-percent conclusion. -/
theorem optimized_trimmed_exceeds_seventy
    {Δ : ℝ}
    (hlo : -(3 : ℝ) / 10 < Δ)
    (hΔ : Δ < 11 / 630) :
    (7 : ℝ) / 10 < 20 / (27 + 90 * Δ) := by
  have hden : 0 < 27 + 90 * Δ := by
    nlinarith
  apply (lt_div_iff₀ hden).2
  nlinarith

/-- Equality at the sharp endpoint. -/
theorem optimized_trimmed_sharp_endpoint :
    20 / (27 + 90 * ((11 : ℝ) / 630)) = 7 / 10 := by
  norm_num

/-! ## A sharp four-point spectral witness -/

theorem witness_first_moment (a : ℝ) :
    (7 / 20 : ℝ) * (1 - a) +
      (7 / 20 : ℝ) * (1 + a) +
      (3 / 20 : ℝ) * 2 +
      (3 / 20 : ℝ) * 0 = 1 := by
  ring

theorem witness_second_moment {a : ℝ} (ha : a ^ 2 = (1 / 21 : ℝ)) :
    (7 / 20 : ℝ) * (1 - a) ^ 2 +
      (7 / 20 : ℝ) * (1 + a) ^ 2 +
      (3 / 20 : ℝ) * 2 ^ 2 +
      (3 / 20 : ℝ) * 0 ^ 2 = 4 / 3 := by
  nlinarith [sq_nonneg (1 - a), sq_nonneg (1 + a)]

theorem witness_third_moment {a : ℝ} (ha : a ^ 2 = (1 / 21 : ℝ)) :
    (7 / 20 : ℝ) * (1 - a) ^ 3 +
      (7 / 20 : ℝ) * (1 + a) ^ 3 +
      (3 / 20 : ℝ) * 2 ^ 3 +
      (3 / 20 : ℝ) * 0 ^ 3 = 2 := by
  nlinarith

theorem witness_fourth_moment {a : ℝ} (ha : a ^ 2 = (1 / 21 : ℝ)) :
    (7 / 20 : ℝ) * (1 - a) ^ 4 +
      (7 / 20 : ℝ) * (1 + a) ^ 4 +
      (3 / 20 : ℝ) * 2 ^ 4 +
      (3 / 20 : ℝ) * 0 ^ 4 = 208 / 63 := by
  have ha4 : a ^ 4 = (1 / 21 : ℝ) ^ 2 := by
    calc
      a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = (1 / 21 : ℝ) ^ 2 := by rw [ha]
  nlinarith

/-- The centered fourth moment of the witness is exactly the sharp value. -/
theorem witness_centered_fourth {a : ℝ} (ha : a ^ 2 = (1 / 21 : ℝ)) :
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

theorem witness_delta :
    ((19 / 63 : ℝ) - 4 / 15) / 2 = 11 / 630 := by
  norm_num

#print axioms trimmed_detector_rearrangement
#print axioms optimized_trimmed_identity
#print axioms optimized_trimmed_exceeds_seventy
#print axioms witness_centered_fourth

end

end Zeta70Trimmed
