import Mathlib

/-!
# Formal scalar core of the Zeta70 missing-proofs analysis

This file verifies the algebraic detector identities, the admissible repaired
zero-side endgame, the exact hard-channel error budget, and a scalar form of the
fixed-window normalization obstruction.

It deliberately does not assume the unresolved determinant estimate as an axiom.
There are no `sorry`, `admit`, or user-declared axioms.
-/

namespace Zeta70MissingProofs

noncomputable section

/-- The quartic detector used on the zero side. -/
def phi (sigma t : ℝ) : ℝ :=
  (1 - sigma) ^ 2 + 4 * (1 - sigma) * t - (((t - 1) ^ 2 - sigma) ^ 2)

/-- Detector factorization corresponding to manuscript equation (5.3). -/
lemma phi_factor (sigma t : ℝ) :
    phi sigma t =
      t * (8 * (1 - sigma) - 2 * (1 - sigma) * t - t * (t - 2) ^ 2) := by
  simp only [phi]
  ring

/-- Detector gap identity corresponding to manuscript equation (5.4). -/
lemma phi_gap (sigma t : ℝ) :
    8 * (1 - sigma) - phi sigma t =
      (t - 2) ^ 2 * (t ^ 2 + 2 * (1 - sigma)) := by
  simp only [phi]
  ring

/-- The detector is nonpositive on the nonpositive half-line. -/
lemma phi_nonpos_of_nonpos {sigma t : ℝ}
    (hsigma : sigma < 3 / 4) (ht : t ≤ 0) :
    phi sigma t ≤ 0 := by
  rw [phi_factor]
  have hone : 0 ≤ 1 - sigma := by nlinarith
  have hfirst : 0 ≤ 8 * (1 - sigma) := mul_nonneg (by norm_num) hone
  have hsecond : 0 ≤ -2 * (1 - sigma) * t := by
    have : 0 ≤ (2 * (1 - sigma)) * (-t) :=
      mul_nonneg (mul_nonneg (by norm_num) hone) (neg_nonneg.mpr ht)
    nlinarith
  have hthird : 0 ≤ -t * (t - 2) ^ 2 :=
    mul_nonneg (neg_nonneg.mpr ht) (sq_nonneg (t - 2))
  have hbracket :
      0 ≤ 8 * (1 - sigma) - 2 * (1 - sigma) * t - t * (t - 2) ^ 2 := by
    nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg ht hbracket

/-- The detector is bounded by `8 * (1 - sigma)`. -/
lemma phi_le_eight {sigma t : ℝ} (hsigma : sigma < 3 / 4) :
    phi sigma t ≤ 8 * (1 - sigma) := by
  have hone : 0 ≤ 1 - sigma := by nlinarith
  have hprod : 0 ≤ (t - 2) ^ 2 * (t ^ 2 + 2 * (1 - sigma)) :=
    mul_nonneg (sq_nonneg (t - 2)) (by nlinarith [sq_nonneg t])
  nlinarith [phi_gap sigma t]

/-- Dropping the final square gives the linear positive-side bound. -/
lemma phi_le_linear (sigma t : ℝ) :
    phi sigma t ≤ (1 - sigma) ^ 2 + 4 * (1 - sigma) * t := by
  simp only [phi]
  nlinarith [sq_nonneg ((t - 1) ^ 2 - sigma)]

/-- Formal optimizer of the rational detector quotient. -/
def sigmaStar (v k : ℝ) : ℝ := (v - k) / (1 - v)

/-- The fourth moment dominates the square of the second moment. -/
lemma sigmaStar_le_v {v k : ℝ} (hv : v < 1) (hk : v ^ 2 ≤ k) :
    sigmaStar v k ≤ v := by
  unfold sigmaStar
  apply (div_le_iff₀ (sub_pos.mpr hv)).2
  nlinarith

/-- Hence the optimizer is admissible whenever `v < 3/4`. -/
lemma sigmaStar_admissible {v k : ℝ}
    (hv : v < 3 / 4) (hk : v ^ 2 ≤ k) :
    sigmaStar v k < 3 / 4 := by
  exact lt_of_le_of_lt (sigmaStar_le_v (lt_trans hv (by norm_num)) hk) hv

/-- The exact target optimizer. -/
lemma target_sigma :
    sigmaStar (1 / 3 : ℝ) (139 / 480) = 21 / 320 := by
  norm_num [sigmaStar]

lemma target_sigma_admissible :
    sigmaStar (1 / 3 : ℝ) (139 / 480) < 3 / 4 := by
  norm_num [sigmaStar]

/-- Correct target-specific use of the master detector inequality. -/
theorem repaired_zero_side_target
    {r v k : ℝ}
    (hv : v = 1 / 3)
    (hk : k ≤ 139 / 480)
    (hmaster : ∀ sigma : ℝ, sigma < 3 / 4 →
      (1 - sigma) ^ 2 * (1 - r) ≤ sigma ^ 2 - 2 * v * sigma + k) :
    640 / 897 ≤ r := by
  have h := hmaster (21 / 320) (by norm_num)
  rw [hv] at h
  nlinarith

/-- Fourth-moment bound in terms of the unresolved hard excess `delta`. -/
def fourthMomentBudget (delta : ℝ) : ℝ := 4 / 15 + 2 * delta

/-- Resulting simple-zero lower bound. -/
def simpleZeroBound (delta : ℝ) : ℝ := 20 / (27 + 90 * delta)

/-- The optimizer corresponding to the fourth-moment budget. -/
def sigmaDelta (delta : ℝ) : ℝ := 1 / 10 - 3 * delta

lemma sigmaDelta_admissible {delta : ℝ} (hdelta : 0 ≤ delta) :
    sigmaDelta delta < 3 / 4 := by
  unfold sigmaDelta
  nlinarith

/-- Algebraic factorization behind the general hard-error budget. -/
lemma delta_detector_factor (delta r : ℝ) :
    sigmaDelta delta ^ 2
        - 2 * (1 / 3 : ℝ) * sigmaDelta delta
        + fourthMomentBudget delta
        - (1 - sigmaDelta delta) ^ 2 * (1 - r)
      = (10 * delta + 3) * ((90 * delta + 27) * r - 20) / 100 := by
  simp only [sigmaDelta, fourthMomentBudget]
  ring

/-- The repaired master inequality implies the exact lower bound
`20 / (27 + 90 * delta)`. -/
theorem repaired_zero_side_with_error_budget
    {r k delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hk : k ≤ fourthMomentBudget delta)
    (hmaster : ∀ sigma : ℝ, sigma < 3 / 4 →
      (1 - sigma) ^ 2 * (1 - r) ≤
        sigma ^ 2 - 2 * (1 / 3 : ℝ) * sigma + k) :
    simpleZeroBound delta ≤ r := by
  have hsigma : sigmaDelta delta < 3 / 4 := sigmaDelta_admissible hdelta
  have h := hmaster (sigmaDelta delta) hsigma
  have hbudget :
      0 ≤ sigmaDelta delta ^ 2
        - 2 * (1 / 3 : ℝ) * sigmaDelta delta
        + fourthMomentBudget delta
        - (1 - sigmaDelta delta) ^ 2 * (1 - r) := by
    nlinarith
  rw [delta_detector_factor] at hbudget
  have hfactor : 0 < 10 * delta + 3 := by nlinarith
  have hlinear : 0 ≤ (90 * delta + 27) * r - 20 := by
    by_contra hnot
    have hneg : (90 * delta + 27) * r - 20 < 0 := lt_of_not_ge hnot
    have hprodneg :
        (10 * delta + 3) * ((90 * delta + 27) * r - 20) < 0 :=
      mul_neg_of_pos_of_neg hfactor hneg
    nlinarith
  have hden : 0 < 27 + 90 * delta := by nlinarith
  unfold simpleZeroBound
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The claimed hard allowance gives exactly `640/897`. -/
lemma claimed_hard_allowance_value :
    simpleZeroBound (11 / 960 : ℝ) = 640 / 897 := by
  norm_num [simpleZeroBound]

/-- Exact strict-70-percent threshold. -/
theorem hard_error_below_threshold_gives_gt_seventy
    {delta : ℝ} (hdelta : 0 ≤ delta) (hsmall : delta < 11 / 630) :
    (7 / 10 : ℝ) < simpleZeroBound delta := by
  have hden : 0 < 27 + 90 * delta := by nlinarith
  unfold simpleZeroBound
  apply (lt_div_iff₀ hden).2
  nlinarith

/-- Conversely, the scalar budget exceeds 70 percent only below `11/630`. -/
theorem gt_seventy_forces_hard_error_below_threshold
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hgt : (7 / 10 : ℝ) < simpleZeroBound delta) :
    delta < 11 / 630 := by
  have hden : 0 < 27 + 90 * delta := by nlinarith
  unfold simpleZeroBound at hgt
  have hcross := (lt_div_iff₀ hden).mp hgt
  nlinarith

lemma threshold_ratio :
    ((11 / 630 : ℝ) / (11 / 960)) = 32 / 21 := by
  norm_num

lemma final_margin :
    (640 / 897 : ℝ) - 7 / 10 = 121 / 8970 := by
  norm_num

/-- Scalar single-mode version of the fixed-window normalization obstruction:
with a fixed window of measure `J < H`, a unit contraction and a prefactor
`1/H` cannot reproduce a positive unit diagonal using the same coefficient. -/
theorem single_mode_fixed_window_strict_loss
    {H J energy : ℝ}
    (hH : 0 < H) (hJH : J < H) (henergy : 0 < energy) :
    (J / H) * energy < energy := by
  have hratio : J / H < 1 := by
    exact (div_lt_one hH).2 hJH
  nlinarith [mul_lt_mul_of_pos_right hratio henergy]

/-- Therefore equality with the original positive diagonal energy is impossible. -/
theorem no_same_coefficient_unit_normalization
    {H J energy : ℝ}
    (hH : 0 < H) (hJH : J < H) (henergy : 0 < energy) :
    ¬ energy ≤ (J / H) * energy := by
  have hlt := single_mode_fixed_window_strict_loss hH hJH henergy
  linarith

/-- Rescaling coefficients by `sqrt(H)` restores the missing prefactor but
multiplies their squared energy by `H`. -/
lemma normalization_conservation {H energy : ℝ} (hH : H ≠ 0) :
    H * energy / H = energy := by
  field_simp

#print axioms phi_factor
#print axioms phi_gap
#print axioms repaired_zero_side_target
#print axioms repaired_zero_side_with_error_budget
#print axioms hard_error_below_threshold_gives_gt_seventy
#print axioms single_mode_fixed_window_strict_loss
#print axioms no_same_coefficient_unit_normalization

end

end Zeta70MissingProofs
