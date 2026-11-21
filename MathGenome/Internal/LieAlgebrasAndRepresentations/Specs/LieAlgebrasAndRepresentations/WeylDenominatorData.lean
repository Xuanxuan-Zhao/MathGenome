import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleRoots
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalCharacterDefinitions
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.Determinant

/-! The Weyl denominator of LA-H02. All exponentials below are formal
basis elements of the integral group ring. -/
noncomputable section

namespace LieAlgebrasAndRepresentations.WeylDenominatorSpecs

open AddMonoidAlgebra
open scoped Classical

universe u v

/-- The integer sign corresponding to the determinant of a real Weyl element. -/
def sign {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : Set E} (w : rootWeylGroup R) : ℤ :=
  if LinearMap.det w.val.toLinearMap = 1 then 1 else -1

/-- The alternating sum, with the actual Weyl orbit as its exponents. -/
def alternant {P : Type u} [AddCommGroup P] {W : Type v}
    (ε : W → ℤ) (orbit : W → P) : AddMonoidAlgebra ℤ P :=
  ∑ᶠ w, single (orbit w) (ε w)

/-- The denominator product with the half-sum as its leading exponent. -/
def denominator {P : Type u} [AddCommGroup P] {I : Type v}
    (r : P) (S : Finset I) (α : I → P) : AddMonoidAlgebra ℤ P :=
  single r 1 * ∏ a ∈ S, (1 - single (-α a) 1)

def signType :=
  {E : Type u} → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] →
    {R : Set E} → rootWeylGroup R → ℤ

def alternantType :=
  {P : Type u} → [AddCommGroup P] → {W : Type v} →
    (W → ℤ) → (W → P) → AddMonoidAlgebra ℤ P

def denominatorType :=
  {P : Type u} → [AddCommGroup P] → {I : Type v} →
    P → Finset I → (I → P) → AddMonoidAlgebra ℤ P

section Cartan

open _root_.Specs.LieAlgebrasAndRepresentations
open FormalCharacters FiniteModuleWeights VermaModules SerreRelations RootDecomposition

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

/-- The half-sum in the complex Cartan dual. -/
def cartanRho (H : LieSubalgebra ℂ L) (φ : Direction H)
    (hS : (positive H φ).Finite) : Module.Dual ℂ H :=
  (1 / 2 : ℂ) • ∑ a ∈ hS.toFinset, a

/-- The integer sign of the Weyl group on the complex Cartan dual. -/
def cartanSign (H : LieSubalgebra ℂ L) (w : weightWeylGroup H) : ℤ :=
  if LinearMap.det w.val.toLinearMap = 1 then 1 else -1

/-- The alternating expression indexed by the actual Weyl group of the Cartan. -/
def cartanAlternant (H : LieSubalgebra ℂ L) (φ : Direction H)
    (hW : ∀ w : weightWeylGroup H, ∀ x ∈ integralWeights H φ,
      w.val x ∈ integralWeights H φ) (ν : integralWeights H φ) : IntegralGroupRing H φ :=
  alternant (cartanSign H) (fun w => ⟨w.val ν.val, hW w ν.val ν.property⟩)

/-- The product expression in the integral group ring of the Cartan weights. -/
def cartanDenominator (H : LieSubalgebra ℂ L) (φ : Direction H)
    (hS : (positive H φ).Finite) (hρ : cartanRho H φ hS ∈ integralWeights H φ)
    (hP : ∀ a ∈ positive H φ, a ∈ integralWeights H φ) : IntegralGroupRing H φ :=
  denominator (⟨cartanRho H φ hS, hρ⟩ : integralWeights H φ) hS.toFinset
    (fun a => if ha : a ∈ positive H φ then ⟨a, hP a ha⟩ else 0)

def cartanRhoType :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H),
    (positive H φ).Finite → Module.Dual ℂ H

def cartanSignType :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L), weightWeylGroup H → ℤ

def cartanAlternantType :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (φ : Direction H),
    (∀ w : weightWeylGroup H, ∀ x ∈ integralWeights H φ, w.val x ∈ integralWeights H φ) →
      integralWeights H φ → IntegralGroupRing H φ

def cartanDenominatorType :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (φ : Direction H) (hS : (positive H φ).Finite),
    cartanRho H φ hS ∈ integralWeights H φ →
    (∀ a ∈ positive H φ, a ∈ integralWeights H φ) → IntegralGroupRing H φ

end Cartan

end LieAlgebrasAndRepresentations.WeylDenominatorSpecs
