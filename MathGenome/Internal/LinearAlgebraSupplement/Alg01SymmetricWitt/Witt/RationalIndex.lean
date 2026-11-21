import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.Decomposition
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring

namespace Alg01SymmetricWitt.Witt.RationalIndex

open Coordinates (hyperbolicPlane hyperbolicSum)
open Decomposition (IsWittIndex)

/-- The binary plane with quadratic value `u² - 2v²`. -/
def binaryPlane : QuadraticForm ℚ (ℚ × ℚ) :=
  (QuadraticMap.sq (R := ℚ)).prod ((-2 : ℚ) • QuadraticMap.sq (R := ℚ))

/-- The form with quadratic value `xy + u² - 2v²` on `((x, y), (u, v))`. -/
def rationalForm : QuadraticForm ℚ ((ℚ × ℚ) × (ℚ × ℚ)) :=
  (hyperbolicPlane ℚ).prod binaryPlane

@[simp] theorem binaryPlane_apply (u v : ℚ) :
    binaryPlane (u, v) = u ^ 2 - 2 * v ^ 2 := by
  change u * u + (-2 : ℚ) * (v * v) = _
  ring

theorem rationalForm_eq_hyperbolic_prod :
    rationalForm = (hyperbolicPlane ℚ).prod binaryPlane :=
  rfl

@[simp] theorem rationalForm_apply (x y u v : ℚ) :
    rationalForm ((x, y), (u, v)) = x * y + u ^ 2 - 2 * v ^ 2 := by
  rw [rationalForm_eq_hyperbolic_prod, QuadraticMap.prod_apply,
    Coordinates.hyperbolicPlane_apply, binaryPlane_apply]
  ring

theorem two_not_isSquare : ¬ IsSquare (2 : ℚ) :=
  fun h => Nat.prime_two.not_isSquare (Rat.isSquare_ofNat_iff.mp h)

theorem binaryPlane_anisotropic : binaryPlane.Anisotropic := by
  rintro ⟨u, v⟩ h
  rw [binaryPlane_apply] at h
  have hsq : u ^ 2 = 2 * v ^ 2 := sub_eq_zero.mp h
  by_cases hv : v = 0
  · subst v
    have hu : u = 0 := by
      by_contra hu
      exact (pow_ne_zero 2 hu) (by simpa using hsq)
    exact Prod.ext hu rfl
  · exfalso
    apply two_not_isSquare
    refine ⟨u / v, ?_⟩
    rw [← sq, div_pow, eq_div_iff (pow_ne_zero 2 hv)]
    exact hsq.symm

theorem binaryPlane_nondegenerate : binaryPlane.Nondegenerate :=
  (Coordinates.nondegenerate_iff_associated_separatingLeft binaryPlane).2
    (QuadraticMap.separatingLeft_of_anisotropic binaryPlane binaryPlane_anisotropic)

theorem rationalForm_nondegenerate : rationalForm.Nondegenerate := by
  rw [rationalForm_eq_hyperbolic_prod]
  apply (Coordinates.nondegenerate_iff_associated_separatingLeft _).2
  intro z hz
  apply Prod.ext
  · apply (Coordinates.nondegenerate_iff_associated_separatingLeft _).1
      (Coordinates.hyperbolicNondegenerate ℚ).1
    intro x
    simpa using hz (x, 0)
  · apply (Coordinates.nondegenerate_iff_associated_separatingLeft _).1 binaryPlane_nondegenerate
    intro y
    simpa using hz (0, y)

private theorem rationalForm_equivalent_hyperbolicSum_one :
    rationalForm.Equivalent ((hyperbolicSum ℚ 1).prod binaryPlane) := by
  let e : (hyperbolicSum ℚ 1).IsometryEquiv (hyperbolicPlane ℚ) :=
    { toLinearEquiv := LinearEquiv.funUnique (Fin 1) ℚ (ℚ × ℚ)
      map_app' := by
        intro z
        simp [Coordinates.hyperbolicSum_apply] }
  exact ⟨e.symm.prod (QuadraticMap.IsometryEquiv.refl binaryPlane)⟩

theorem rationalForm_wittIndex : IsWittIndex rationalForm 1 :=
  (Decomposition.isWittIndex_iff rationalForm binaryPlane 1 1 rationalForm_nondegenerate
    binaryPlane_anisotropic rationalForm_equivalent_hyperbolicSum_one).2 rfl

end Alg01SymmetricWitt.Witt.RationalIndex
