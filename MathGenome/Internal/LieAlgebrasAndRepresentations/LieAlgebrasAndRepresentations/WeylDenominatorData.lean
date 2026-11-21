import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleRoots
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalCharacterDefinitions
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.Determinant

/-! The Weyl sign, alternant, and denominator in the integral group ring. -/

noncomputable section

namespace LieAlgebrasAndRepresentations.WeylDenominator

open AddMonoidAlgebra
open scoped BigOperators Classical

universe u v

/-- The Weyl sign determined by the real determinant. -/
def sign {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : Set E} (w : rootWeylGroup R) : ℤ :=
  if LinearMap.det w.val.toLinearMap = 1 then 1 else -1

/-- The sum of signed formal monomials indexed by the Weyl elements. -/
def alternant {P : Type u} [AddCommGroup P] {W : Type v}
    (ε : W → ℤ) (orbit : W → P) : AddMonoidAlgebra ℤ P :=
  ∑ᶠ w, single (orbit w) (ε w)

/-- The monomial at the half-sum times the product over positive roots. -/
def denominator {P : Type u} [AddCommGroup P] {I : Type v}
    (r : P) (S : Finset I) (α : I → P) : AddMonoidAlgebra ℤ P :=
  single r 1 * ∏ a ∈ S, (1 - single (-α a) 1)

section Cartan

open _root_.Specs.LieAlgebrasAndRepresentations
open FormalCharacters FiniteModuleWeights VermaModules SerreRelations

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- Half the sum of the positive roots in the complex Cartan dual. -/
def cartanRho (H : LieSubalgebra ℂ L) (φ : Direction H)
    (hS : (positive H φ).Finite) : Module.Dual ℂ H :=
  (1 / 2 : ℂ) • ∑ a ∈ hS.toFinset, a

variable [FiniteDimensional ℂ L]

/-- The Weyl sign determined by the determinant on the complex Cartan dual. -/
def cartanSign (H : LieSubalgebra ℂ L) (w : weightWeylGroup H) : ℤ :=
  if LinearMap.det w.val.toLinearMap = 1 then 1 else -1

/-- The alternant of an integral weight under the Cartan Weyl action. -/
def cartanAlternant (H : LieSubalgebra ℂ L) (φ : Direction H)
    (hW : ∀ w : weightWeylGroup H, ∀ x ∈ integralWeights H φ,
      w.val x ∈ integralWeights H φ) (ν : integralWeights H φ) : IntegralGroupRing H φ :=
  alternant (cartanSign H) (fun w => ⟨w.val ν.val, hW w ν.val ν.property⟩)

/-- The denominator with the half-sum and the positive roots in the integral lattice. -/
def cartanDenominator (H : LieSubalgebra ℂ L) (φ : Direction H)
    (hS : (positive H φ).Finite) (hρ : cartanRho H φ hS ∈ integralWeights H φ)
    (hP : ∀ a ∈ positive H φ, a ∈ integralWeights H φ) : IntegralGroupRing H φ :=
  denominator (⟨cartanRho H φ hS, hρ⟩ : integralWeights H φ) hS.toFinset
    (fun a => if ha : a ∈ positive H φ then ⟨a, hP a ha⟩ else 0)

end Cartan

end LieAlgebrasAndRepresentations.WeylDenominator
