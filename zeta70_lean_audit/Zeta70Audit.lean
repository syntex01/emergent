import Mathlib

namespace Zeta70Audit

noncomputable section

/-!
This file formally checks the self-contained algebraic and calculus core of
`Zeta70_70percent_Proof.md`. It deliberately does not postulate the Gabor/zero-side
analytic reductions as axioms, because doing so would not verify the advertised
unconditional zeta theorem.
-/

/-- The polynomial used in the zero-side argument. -/
def Phi (σ t : ℝ) : ℝ :=
  (1 - σ) ^ 2 + 4 * (1 - σ) * t - (((t - 1) ^ 2 - σ) ^ 2)

/-- Equation (5.3). -/
theorem phi_identity_one (σ t : ℝ) :
    Phi σ t = t * (8 * (1 - σ) - 2 * (1 - σ) * t - t * (t - 2) ^ 2) := by
  unfold Phi
  ring

/-- Equation (5.4). -/
theorem phi_identity_two (σ t : ℝ) :
    8 * (1 - σ) - Phi σ t = (t - 2) ^ 2 * (t ^ 2 + 2 * (1 - σ)) := by
  unfold Phi
  ring

/-- Equation (5.5), in the parameter range actually used in the proof. -/
theorem phi_nonpositive_of_nonpositive
    {σ t : ℝ} (hσ : σ < (3 : ℝ) / 4) (ht : t ≤ 0) : Phi σ t ≤ 0 := by
  rw [phi_identity_one]
  have hOne : 0 ≤ 1 - σ := by linarith
  have ha : 0 ≤ 8 * (1 - σ) := mul_nonneg (by norm_num) hOne
  have hb : 0 ≤ -(2 * (1 - σ) * t) := by
    apply neg_nonneg.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hOne) ht
  have hc : 0 ≤ -(t * (t - 2) ^ 2) := by
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg ht (sq_nonneg (t - 2)))
  have hbracket : 0 ≤ 8 * (1 - σ) - 2 * (1 - σ) * t - t * (t - 2) ^ 2 := by
    nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg ht hbracket

/-- Equation (5.6). -/
theorem phi_le_eight
    {σ t : ℝ} (hσ : σ < (3 : ℝ) / 4) : Phi σ t ≤ 8 * (1 - σ) := by
  have hq : 0 ≤ t ^ 2 + 2 * (1 - σ) := by
    nlinarith [sq_nonneg t]
  have hp : 0 ≤ (t - 2) ^ 2 * (t ^ 2 + 2 * (1 - σ)) :=
    mul_nonneg (sq_nonneg (t - 2)) hq
  nlinarith [phi_identity_two σ t]

/-- Equation (5.7); in fact this holds for every real `t`. -/
theorem phi_le_linear (σ t : ℝ) :
    Phi σ t ≤ (1 - σ) ^ 2 + 4 * (1 - σ) * t := by
  unfold Phi
  nlinarith [sq_nonneg ((t - 1) ^ 2 - σ)]

/-! ## Exact hard-wedge mass accounting -/

/-- Integrating `2*x*y*(1-x)` in `y` over `0 ≤ y ≤ x` gives this polynomial. -/
theorem total_mass_inner_reduction (x : ℝ) :
    x * (1 - x) * x ^ 2 = -x ^ 4 + x ^ 3 := by
  ring

/-- A primitive of the total-mass polynomial. -/
def totalPrimitive (x : ℝ) : ℝ := -x ^ 5 / 5 + x ^ 4 / 4

/-- Exact evaluation of the single-contraction total mass, equation (4.2). -/
theorem total_mass_exact : totalPrimitive 1 - totalPrimitive 0 = (1 : ℝ) / 20 := by
  norm_num [totalPrimitive]

/-- Integrating in `y` over `1-x ≤ y ≤ 1/2` gives this polynomial. -/
theorem hard_mass_inner_reduction (x : ℝ) :
    x * (1 - x) * (((1 : ℝ) / 2) ^ 2 - (1 - x) ^ 2) =
      x ^ 4 - 3 * x ^ 3 + ((11 : ℝ) / 4) * x ^ 2 - ((3 : ℝ) / 4) * x := by
  ring

/-- A primitive of the hard-wedge polynomial. -/
def hardPrimitive (x : ℝ) : ℝ :=
  x ^ 5 / 5 - 3 * x ^ 4 / 4 + 11 * x ^ 3 / 12 - 3 * x ^ 2 / 8

/-- Exact evaluation of the hard wedge, equation (4.3). -/
theorem hard_mass_exact :
    hardPrimitive 1 - hardPrimitive ((1 : ℝ) / 2) = (11 : ℝ) / 960 := by
  norm_num [hardPrimitive]

/-- Equation (4.5). -/
theorem alternating_channel_constant :
    (1 : ℝ) / 10 + 11 / 960 = 107 / 960 := by
  norm_num

/-- Equation (6.1). -/
theorem fourth_moment_constant :
    4 * ((1 : ℝ) / 60) + 2 * (1 / 10 + 11 / 960) = 139 / 480 := by
  norm_num

/-! ## The optimization in Lemma 5.1 -/

/-- The optimizer used in the manuscript. -/
def sigmaStar (v k : ℝ) : ℝ := (v - k) / (1 - v)

/-- The moment inequality `k ≥ v²` puts the optimizer below `v`. -/
theorem sigmaStar_le_v
    {v k : ℝ} (hv : v < 1) (hk : v ^ 2 ≤ k) : sigmaStar v k ≤ v := by
  unfold sigmaStar
  apply (div_le_iff₀ (sub_pos.mpr hv)).2
  nlinarith

/-- Hence the manuscript's restriction `σ < 3/4` is valid in its numerical application,
provided the standard fourth-moment inequality `k ≥ v²` is supplied. -/
theorem sigmaStar_lt_three_quarters
    {v k : ℝ} (hv : v < (3 : ℝ) / 4) (hk : v ^ 2 ≤ k) :
    sigmaStar v k < (3 : ℝ) / 4 := by
  exact lt_of_le_of_lt (sigmaStar_le_v (lt_trans hv (by norm_num)) hk) hv

/-- At the endpoint values used in the manuscript, the optimizer is `21/320`. -/
theorem application_sigmaStar :
    sigmaStar ((1 : ℝ) / 3) (139 / 480) = 21 / 320 := by
  norm_num [sigmaStar]

/-- The exact final ratio in equation (6.2). -/
theorem final_ratio_exact :
    ((1 - ((1 : ℝ) / 3)) ^ 2) /
        (1 - 2 * ((1 : ℝ) / 3) + 139 / 480) = 640 / 897 := by
  norm_num

/-- The claimed rational constant is strictly greater than 70 percent. -/
theorem final_ratio_exceeds_seventy_percent :
    (7 : ℝ) / 10 < 640 / 897 := by
  norm_num

/-- The difference displayed in the manuscript is exact. -/
theorem final_margin_exact :
    (640 : ℝ) / 897 - 7 / 10 = 121 / 8970 := by
  norm_num

/-! ## A defect in the statement of Lemma 5.1 -/

/-- The moment values of `G = diag(15,-13)` with `N=2` and `tr G=N` are `v=196`, `k=38416`. -/
theorem counterexample_moments :
    ((((15 : ℝ) - 1) ^ 2 + ((-13 : ℝ) - 1) ^ 2) / 2 = 196) ∧
    ((((15 : ℝ) - 1) ^ 4 + ((-13 : ℝ) - 1) ^ 4) / 2 = 38416) := by
  norm_num

/-- Therefore the displayed conclusion of Lemma 5.1 is false under only the
hypotheses explicitly stated there: its right side can equal one while `s/N=0`.
The omitted domain condition is material, even though it is repairable in the
specific application where `v=1/3`. -/
theorem lemma_five_one_unqualified_counterexample :
    ¬ ((0 : ℝ) ≥ ((1 - 196) ^ 2) / (1 - 2 * 196 + 38416)) := by
  norm_num

#print axioms hard_mass_exact
#print axioms final_ratio_exact
#print axioms lemma_five_one_unqualified_counterexample

end

end Zeta70Audit
