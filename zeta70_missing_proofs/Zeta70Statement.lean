import Mathlib
import Zeta70MissingProofs

/-!
# Trusted statement surface for the proposed 70% zeta theorem

The counting functions below are defined directly from Mathlib's
`riemannZeta` and `analyticOrderAt`.  The final theorem in this file proves the
headline statement from an explicit analytic certificate.  No constructor for
that certificate is supplied: the determinant-windowed balanced-strip bound
remains the mathematical trust boundary.
-/

namespace Zeta70Statement

open scoped BigOperators ComplexConjugate
open Complex Set Filter

noncomputable section

/-- A nontrivial zero of the Riemann zeta function. -/
def IsNontrivialZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- Multiplicity, defined by the analytic order of vanishing. -/
def zeroMult (ρ : ℂ) : ℕ :=
  (analyticOrderAt riemannZeta ρ).toNat

/-- Nontrivial zeros whose ordinates lie in `(T₁,T₂]`. -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- Total zero count, with multiplicity. -/
def Ncount (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- Simple critical-line zero count. -/
def N0simple (T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩
    {ρ | zeroMult ρ = 1}).ncard

/-- The literal dyadic-height strict-70% statement in epsilon form. -/
def SeventyPercent : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((7 / 10 : ℝ) - ε) * (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ)

/-- Eventual form of a proportion bound over real heights. -/
def EventuallyProportionAtLeast
    (p : ℝ) (num den : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ T in atTop, (p - ε) * den T ≤ num T

/-- The exact analytic certificate required by the repaired fourth-moment
argument.  Its `detector_output` field is where the cutoff-preserving Gabor
trace calculation and zero-side transfer must meet. -/
structure AnalyticCertificate where
  delta : ℝ
  delta_nonneg : 0 ≤ delta
  delta_lt_threshold : delta < 11 / 630
  detector_output : EventuallyProportionAtLeast
    (Zeta70MissingProofs.simpleZeroBound delta)
    (fun T => (N0simple T (2 * T) : ℝ))
    (fun T => (Ncount T (2 * T) : ℝ))

/-- A genuine analytic certificate below the sharp error threshold proves the
literal strict-70% theorem for Mathlib's Riemann zeta function. -/
theorem certificate_implies_seventy_percent
    (C : AnalyticCertificate) : SeventyPercent := by
  have hgt : (7 / 10 : ℝ) < Zeta70MissingProofs.simpleZeroBound C.delta :=
    Zeta70MissingProofs.hard_error_below_threshold_gives_gt_seventy
      C.delta_nonneg C.delta_lt_threshold
  intro ε hε
  let η : ℝ := min (ε / 2)
    ((Zeta70MissingProofs.simpleZeroBound C.delta - 7 / 10) / 2)
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηε : η ≤ ε / 2 := min_le_left _ _
  have hcoeff :
      (7 / 10 : ℝ) - ε ≤
        Zeta70MissingProofs.simpleZeroBound C.delta - η := by
    linarith
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (C.detector_output η hη)
  refine ⟨T₀, fun T hT => ?_⟩
  have hden : 0 ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  exact (mul_le_mul_of_nonneg_right hcoeff hden).trans (hT₀ T hT)

#print axioms certificate_implies_seventy_percent

end

end Zeta70Statement
