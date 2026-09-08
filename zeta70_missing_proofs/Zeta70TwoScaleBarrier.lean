import Mathlib

/-!
# The two-scale detector and the quadratic-information barrier

This file formalizes the exact scalar obstruction exposed by the bounded
completed-zeta scattering detector. It does not assume or state a new zeta
zero theorem.
-/

namespace Zeta70TwoScaleBarrier

noncomputable section

/-- The proposed prime-side target is already at least as strong as the desired
simple-zero proportion: if the detector sum is bounded above by `δ * S`, then
a lower bound `q * δ * N < L` immediately forces `q * N < S`. -/
theorem detector_target_implies_simple_proportion
    {L S N δ q : ℝ}
    (hδ : 0 < δ)
    (hupper : L ≤ δ * S)
    (htarget : q * δ * N < L) :
    q * N < S := by
  have h : q * δ * N < δ * S := htarget.trans_le hupper
  have h' : δ * (q * N) < δ * S := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  by_contra hnot
  have hrev : S ≤ q * N := le_of_not_gt hnot
  have hmul : δ * S ≤ δ * (q * N) :=
    mul_le_mul_of_nonneg_left hrev hδ.le
  exact (not_lt_of_ge hmul) h'

/-- Any lower bound for a simple-zero detector obtained only from a first
multiplicity moment and a quadratic collision moment has the ceiling `2-C`.

The hypotheses `h1` and `h2` are the constraints imposed at multiplicities
one and two on a quadratic minorant `α*m - γ*m^2`; a valid simple-zero detector
has value at most `δ` at `m=1` and at most zero at `m=2`. -/
theorem quadratic_information_ceiling
    {δ C α γ : ℝ}
    (hC1 : 1 ≤ C)
    (hC2 : C ≤ 2)
    (h1 : α - γ ≤ δ)
    (h2 : 2 * α - 4 * γ ≤ 0) :
    α - C * γ ≤ (2 - C) * δ := by
  by_cases hγδ : γ ≤ δ
  · have hα : α ≤ 2 * γ := by linarith
    have hprod : 0 ≤ (2 - C) * (δ - γ) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hδγ : δ < γ := lt_of_not_ge hγδ
    have hα : α ≤ δ + γ := by linarith
    have hprod : 0 ≤ (C - 1) * (γ - δ) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- In particular, once the normalized quadratic collision constant exceeds
`13/10`, the quadratic-information ceiling is strictly below seventy percent. -/
theorem quadratic_information_cannot_reach_seventy
    {δ C α γ : ℝ}
    (hδ : 0 < δ)
    (hC1 : 1 ≤ C)
    (hC2 : C ≤ 2)
    (hC70 : (13 : ℝ) / 10 < C)
    (h1 : α - γ ≤ δ)
    (h2 : 2 * α - 4 * γ ≤ 0) :
    α - C * γ < (7 / 10 : ℝ) * δ := by
  have hbase := quadratic_information_ceiling hC1 hC2 h1 h2
  have hcoef : 2 - C < (7 / 10 : ℝ) := by linarith
  exact hbase.trans_lt (mul_lt_mul_of_pos_right hcoef hδ)

/-- For the explicit scale `κ = 3 - 2*sqrt 2`, the two-scale detector has
`c₁ = δ` and `c₂ = -(2/3)δ`. These stronger two-point constraints force the
smaller exact ceiling `(7-4C)/3`. -/
theorem explicit_two_scale_quadratic_ceiling
    {δ C α γ : ℝ}
    (hC1 : 1 ≤ C)
    (hC2 : C ≤ 2)
    (h1 : α - γ ≤ δ)
    (h2 : 2 * α - 4 * γ ≤ -(2 / 3 : ℝ) * δ) :
    α - C * γ ≤ ((7 - 4 * C) / 3) * δ := by
  by_cases hγ : γ ≤ (4 / 3 : ℝ) * δ
  · have hα : α ≤ 2 * γ - δ / 3 := by linarith
    have hprod : 0 ≤ (2 - C) * ((4 / 3 : ℝ) * δ - γ) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hγ' : (4 / 3 : ℝ) * δ < γ := lt_of_not_ge hγ
    have hα : α ≤ δ + γ := by linarith
    have hprod : 0 ≤ (C - 1) * (γ - (4 / 3 : ℝ) * δ) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- The upper bound in the preceding theorem is attained by the quadratic
minorant with `γ = 4δ/3` and `α = 7δ/3`. -/
theorem explicit_ceiling_attained
    (δ C : ℝ) :
    (7 * δ / 3) - C * (4 * δ / 3) = ((7 - 4 * C) / 3) * δ := by
  ring

#print axioms detector_target_implies_simple_proportion
#print axioms quadratic_information_ceiling
#print axioms quadratic_information_cannot_reach_seventy
#print axioms explicit_two_scale_quadratic_ceiling
#print axioms explicit_ceiling_attained

end

end Zeta70TwoScaleBarrier
