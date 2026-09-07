import Mathlib

/-!
# The determinant window survives the dispersion swap

This finite counterexample formalizes the structural obstruction in the newest
strip proposal. An unweighted fiber energy factors through autocorrelations.
With a nonconstant determinant/output window, the weight remains attached to
the base fiber. It cannot in general be replaced by a multiplier depending
only on the autocorrelation shift.
-/

namespace Zeta70WeightedDispersion

open scoped BigOperators

noncomputable section

abbrev I := Fin 2

def idx (i : I) : ℤ := i.val

def leftPoint (i : I) : ℤ := if i.val = 0 then 1 else 0

def rightPoint (i : I) : ℤ := if i.val = 1 then 1 else 0

def shifts : Finset ℤ := {-1, 0, 1}

/-- The correlation vector that appears after an unweighted dispersion swap. -/
def corr (u : I → ℤ) (k : ℤ) : ℤ :=
  ∑ i : I, ∑ j : I,
    if idx i - idx j = k then u i * u j else 0

/-- Fiber amplitude for the toy determinant/output coordinate `n - m`. -/
def fiberAmplitude (u v : I → ℤ) (j : ℤ) : ℤ :=
  ∑ m : I, ∑ n : I,
    if idx n - idx m = j then u m * v n else 0

/-- A nonconstant output window selecting the central determinant fiber. -/
def centralWindow (j : ℤ) : ℤ := if j = 0 then 1 else 0

def weightedEnergy (u v : I → ℤ) : ℤ :=
  ∑ j ∈ shifts, centralWindow j * fiberAmplitude u v j ^ 2

/-- The form claimed after discarding the base-fiber window: only a multiplier
of the autocorrelation shift `k` remains. -/
def shiftOnlyForm (omega : ℤ → ℤ) (u v : I → ℤ) : ℤ :=
  ∑ k ∈ shifts, omega k * corr u k * corr v k

/-- Translating one input leaves its entire autocorrelation vector unchanged. -/
theorem shiftOnlyForm_translation_invariant (omega : ℤ → ℤ) :
    shiftOnlyForm omega leftPoint leftPoint =
      shiftOnlyForm omega rightPoint leftPoint := by
  simp [shiftOnlyForm, shifts, corr, leftPoint, rightPoint, idx]

/-- The actual weighted fiber energy is not invariant under that translation. -/
theorem weightedEnergy_left :
    weightedEnergy leftPoint leftPoint = 1 := by
  native_decide

theorem weightedEnergy_right :
    weightedEnergy rightPoint leftPoint = 0 := by
  native_decide

/-- No multiplier depending only on the correlation shift can represent both
weighted determinant energies. Thus the determinant window may not be dropped
when passing to a product of prime-pair correlations. -/
theorem no_universal_shift_only_factorization :
    ¬ ∃ omega : ℤ → ℤ,
      weightedEnergy leftPoint leftPoint =
          shiftOnlyForm omega leftPoint leftPoint ∧
      weightedEnergy rightPoint leftPoint =
          shiftOnlyForm omega rightPoint leftPoint := by
  rintro ⟨omega, hleft, hright⟩
  have hs := shiftOnlyForm_translation_invariant omega
  have hbad : (1 : ℤ) = 0 := by
    calc
      (1 : ℤ) = weightedEnergy leftPoint leftPoint := weightedEnergy_left.symm
      _ = shiftOnlyForm omega leftPoint leftPoint := hleft
      _ = shiftOnlyForm omega rightPoint leftPoint := hs
      _ = weightedEnergy rightPoint leftPoint := hright.symm
      _ = 0 := weightedEnergy_right
  norm_num at hbad

#print axioms shiftOnlyForm_translation_invariant
#print axioms weightedEnergy_left
#print axioms weightedEnergy_right
#print axioms no_universal_shift_only_factorization

end

end Zeta70WeightedDispersion
