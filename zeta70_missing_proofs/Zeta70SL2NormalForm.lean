import Mathlib

/-!
# Exact `SL₂(ℤ)` normal form of the residual determinant strip

The analytic gap in the proposed Zeta70 argument is often written in the
coordinates

`d = x*n + b*t`,  `e = y*n + a*t`,  with `a*x - b*y = 1`.

This file kernel-checks that this change of variables is a genuine lattice
automorphism, gives its inverse, and gives the equivalent additive-Chowla
coordinates `(z,s) = (d,e-d)`. No analytic cancellation theorem is assumed.
-/

namespace Zeta70SL2NormalForm

noncomputable section

/-- The determinant-line parametrisation `(n,t) ↦ (d,e)`. -/
def determinantMap (a b x y : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (x * p.1 + b * p.2, y * p.1 + a * p.2)

/-- Its inverse `(d,e) ↦ (a*d-b*e,-y*d+x*e)`. -/
def determinantMapInv (a b x y : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (a * p.1 - b * p.2, -y * p.1 + x * p.2)

/-- Bézout's identity makes the displayed inverse a left inverse. -/
theorem determinantMapInv_determinantMap
    {a b x y : ℤ} (hdet : a * x - b * y = 1) (p : ℤ × ℤ) :
    determinantMapInv a b x y (determinantMap a b x y p) = p := by
  rcases p with ⟨n, t⟩
  apply Prod.ext
  · change a * (x * n + b * t) - b * (y * n + a * t) = n
    calc
      a * (x * n + b * t) - b * (y * n + a * t)
          = (a * x - b * y) * n := by ring
      _ = n := by rw [hdet]; ring
  · change -y * (x * n + b * t) + x * (y * n + a * t) = t
    calc
      -y * (x * n + b * t) + x * (y * n + a * t)
          = (a * x - b * y) * t := by ring
      _ = t := by rw [hdet]; ring

/-- Bézout's identity also makes it a right inverse. -/
theorem determinantMap_determinantMapInv
    {a b x y : ℤ} (hdet : a * x - b * y = 1) (p : ℤ × ℤ) :
    determinantMap a b x y (determinantMapInv a b x y p) = p := by
  rcases p with ⟨d, e⟩
  apply Prod.ext
  · change x * (a * d - b * e) + b * (-y * d + x * e) = d
    calc
      x * (a * d - b * e) + b * (-y * d + x * e)
          = (a * x - b * y) * d := by ring
      _ = d := by rw [hdet]; ring
  · change y * (a * d - b * e) + a * (-y * d + x * e) = e
    calc
      y * (a * d - b * e) + a * (-y * d + x * e)
          = (a * x - b * y) * e := by ring
      _ = e := by rw [hdet]; ring

/-- The determinant parametrisation is an equivalence of the integer lattice. -/
def determinantEquiv
    (a b x y : ℤ) (hdet : a * x - b * y = 1) :
    (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun := determinantMap a b x y
  invFun := determinantMapInv a b x y
  left_inv := determinantMapInv_determinantMap hdet
  right_inv := determinantMap_determinantMapInv hdet

/-- The defining determinant equation is recovered exactly. -/
theorem determinant_coordinate
    {a b x y n t : ℤ} (hdet : a * x - b * y = 1) :
    a * (x * n + b * t) - b * (y * n + a * t) = n := by
  calc
    a * (x * n + b * t) - b * (y * n + a * t)
        = (a * x - b * y) * n := by ring
    _ = n := by rw [hdet]; ring

/-- The second inverse coordinate is recovered exactly. -/
theorem line_coordinate
    {a b x y n t : ℤ} (hdet : a * x - b * y = 1) :
    -y * (x * n + b * t) + x * (y * n + a * t) = t := by
  calc
    -y * (x * n + b * t) + x * (y * n + a * t)
        = (a * x - b * y) * t := by ring
    _ = t := by rw [hdet]; ring

/-- Change from `(d,e)` to additive-correlation coordinates `(z,s)=(d,e-d)`. -/
def differenceMap (p : ℤ × ℤ) : ℤ × ℤ := (p.1, p.2 - p.1)

/-- The inverse change `(z,s) ↦ (z,z+s)`. -/
def differenceMapInv (p : ℤ × ℤ) : ℤ × ℤ := (p.1, p.1 + p.2)

theorem differenceMapInv_differenceMap (p : ℤ × ℤ) :
    differenceMapInv (differenceMap p) = p := by
  rcases p with ⟨d, e⟩
  simp [differenceMap, differenceMapInv]

theorem differenceMap_differenceMapInv (p : ℤ × ℤ) :
    differenceMap (differenceMapInv p) = p := by
  rcases p with ⟨z, s⟩
  simp [differenceMap, differenceMapInv]

def differenceEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun := differenceMap
  invFun := differenceMapInv
  left_inv := differenceMapInv_differenceMap
  right_inv := differenceMap_differenceMapInv

/-- The exact map from determinant coordinates `(n,t)` to additive Chowla
coordinates `(z,s)=(d,e-d)`. -/
def chowlaMap (a b x y : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (x * p.1 + b * p.2, (y - x) * p.1 + (a - b) * p.2)

/-- Its exact inverse. -/
def chowlaMapInv (a b x y : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  ((a - b) * p.1 - b * p.2, (x - y) * p.1 + x * p.2)

/-- The Chowla map is the determinant map followed by taking the difference. -/
theorem chowlaMap_eq
    (a b x y : ℤ) (p : ℤ × ℤ) :
    chowlaMap a b x y p = differenceMap (determinantMap a b x y p) := by
  rcases p with ⟨n, t⟩
  apply Prod.ext
  · rfl
  · change (y - x) * n + (a - b) * t =
      (y * n + a * t) - (x * n + b * t)
    ring

/-- The inverse displayed above is a left inverse. -/
theorem chowlaMapInv_chowlaMap
    {a b x y : ℤ} (hdet : a * x - b * y = 1) (p : ℤ × ℤ) :
    chowlaMapInv a b x y (chowlaMap a b x y p) = p := by
  rcases p with ⟨n, t⟩
  apply Prod.ext
  · change (a - b) * (x * n + b * t) -
      b * ((y - x) * n + (a - b) * t) = n
    calc
      (a - b) * (x * n + b * t) -
          b * ((y - x) * n + (a - b) * t)
          = (a * x - b * y) * n := by ring
      _ = n := by rw [hdet]; ring
  · change (x - y) * (x * n + b * t) +
      x * ((y - x) * n + (a - b) * t) = t
    calc
      (x - y) * (x * n + b * t) +
          x * ((y - x) * n + (a - b) * t)
          = (a * x - b * y) * t := by ring
      _ = t := by rw [hdet]; ring

/-- The inverse displayed above is a right inverse. -/
theorem chowlaMap_chowlaMapInv
    {a b x y : ℤ} (hdet : a * x - b * y = 1) (p : ℤ × ℤ) :
    chowlaMap a b x y (chowlaMapInv a b x y p) = p := by
  rcases p with ⟨z, s⟩
  apply Prod.ext
  · change x * ((a - b) * z - b * s) +
      b * ((x - y) * z + x * s) = z
    calc
      x * ((a - b) * z - b * s) +
          b * ((x - y) * z + x * s)
          = (a * x - b * y) * z := by ring
      _ = z := by rw [hdet]; ring
  · change (y - x) * ((a - b) * z - b * s) +
      (a - b) * ((x - y) * z + x * s) = s
    calc
      (y - x) * ((a - b) * z - b * s) +
          (a - b) * ((x - y) * z + x * s)
          = (a * x - b * y) * s := by ring
      _ = s := by rw [hdet]; ring

/-- Thus the residual strip is exactly an additive-correlation lattice. -/
def chowlaEquiv
    (a b x y : ℤ) (hdet : a * x - b * y = 1) :
    (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun := chowlaMap a b x y
  invFun := chowlaMapInv a b x y
  left_inv := chowlaMapInv_chowlaMap hdet
  right_inv := chowlaMap_chowlaMapInv hdet

/-- Pointwise form of the exact Möbius-product rewrite. -/
theorem product_rewrite
    {a b x y n t : ℤ} (μ : ℤ → ℂ) :
    μ (x * n + b * t) * μ (y * n + a * t) =
      μ (chowlaMap a b x y (n, t)).1 *
        μ ((chowlaMap a b x y (n, t)).1 +
          (chowlaMap a b x y (n, t)).2) := by
  change μ (x * n + b * t) * μ (y * n + a * t) =
    μ (x * n + b * t) *
      μ ((x * n + b * t) + ((y - x) * n + (a - b) * t))
  have harg :
      (x * n + b * t) + ((y - x) * n + (a - b) * t) =
        y * n + a * t := by ring
  rw [harg]

/-- Mapping a finite lattice region through the determinant equivalence loses
no lattice points. -/
theorem card_map_determinant
    {a b x y : ℤ} (hdet : a * x - b * y = 1)
    (S : Finset (ℤ × ℤ)) :
    (S.map (determinantEquiv a b x y hdet).toEmbedding).card = S.card := by
  exact Finset.card_map _

/-- The same exact cardinality preservation in additive Chowla coordinates. -/
theorem card_map_chowla
    {a b x y : ℤ} (hdet : a * x - b * y = 1)
    (S : Finset (ℤ × ℤ)) :
    (S.map (chowlaEquiv a b x y hdet).toEmbedding).card = S.card := by
  exact Finset.card_map _

#print axioms determinantMapInv_determinantMap
#print axioms determinantMap_determinantMapInv
#print axioms determinant_coordinate
#print axioms chowlaMapInv_chowlaMap
#print axioms chowlaMap_chowlaMapInv
#print axioms product_rewrite
#print axioms card_map_chowla

end

end Zeta70SL2NormalForm
