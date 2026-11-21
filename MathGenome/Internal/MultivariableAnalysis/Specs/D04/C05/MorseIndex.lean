import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.Symmetry
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-! The index of the actual coordinate Hessian, and invariance under arbitrary
local C¹ signed-square coordinates. No coordinate construction is assumed. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C05.MorseIndex
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.Symmetry.Model
namespace Model
/-- The full Hessian quadratic form v ↦ vᵀ H_f(a) v (without a factor 1/2). -/
def hessianQuadraticForm {n : ℕ} (f : E n → ℝ) (a : E n) : QuadraticForm ℝ (E n) :=
  (hessian f a).toQuadraticForm'.comp (coordinates n).toLinearMap

/-- Negative inertia: maximal dimension of a subspace on which the Hessian is
negative definite. Mathlib's signature counts dimensions, not their difference. -/
def negativeMorseIndex {n : ℕ} (f : E n → ℝ) (a : E n) : ℕ :=
  sigNeg (hessianQuadraticForm f a)

def positiveMorseIndex {n : ℕ} (f : E n → ℝ) (a : E n) : ℕ :=
  sigPos (hessianQuadraticForm f a)
end Model
open Model
abbrev hessianQuadraticFormType := {n : ℕ} → (E n → ℝ) → E n → QuadraticForm ℝ (E n)
def hessianQuadraticFormValue : hessianQuadraticFormType := @hessianQuadraticForm
abbrev negativeMorseIndexType := {n : ℕ} → (E n → ℝ) → E n → ℕ
def negativeMorseIndexValue : negativeMorseIndexType := @negativeMorseIndex
abbrev positiveMorseIndexType := {n : ℕ} → (E n → ℝ) → E n → ℕ
def positiveMorseIndexValue : positiveMorseIndexType := @positiveMorseIndex

/-- Peano/congruence bridge using only the first derivative of χ. The normal
form need hold only in a neighborhood; its coefficients may be arbitrary. -/
def morse_hessian_congruenceType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    IsOpen U → a ∈ U → CrOn 2 U f → totalDerivative f a = 0 →
    ∀ (χ : E n → E n) (A : E n →L[ℝ] E n) (ε : Fin n → ℝ),
      HasFDerivAt χ A a → χ a = 0 →
      (∀ᶠ x in 𝓝 a, f x = f a + ∑ i, ε i * (χ x i)^2) →
      ∀ v, hessianQuadraticForm f a v = 2 * ∑ i, ε i * (A v i)^2

/-- Source d04:05:morse-index. Both coordinate maps have exactly C¹ regularity.
The function has only C² regularity near a, independently of any stronger Morse
coordinate construction. Every dimension n, including zero, is quantified. -/
def morse_indexType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    IsOpen U → a ∈ U → CrOn 2 U f → totalDerivative f a = 0 →
    (hessian f a).det ≠ 0 →
    ∀ (χ : OpenPartialHomeomorph (E n) (E n)),
      a ∈ χ.source → χ a = 0 → CrOn 1 χ.source (χ : E n → E n) →
      CrOn 1 χ.target (χ.symm : E n → E n) →
      ∀ (ε : Fin n → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) →
      (∀ x ∈ χ.source, f x = f a + ∑ i, ε i * (χ x i)^2) →
      negativeMorseIndex f a = {i | ε i < 0}.ncard ∧
      positiveMorseIndex f a = {i | 0 < ε i}.ncard

end Specs.D04.C05.MorseIndex
