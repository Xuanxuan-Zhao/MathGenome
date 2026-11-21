import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.FrobeniusSchurIndicator
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Star.Module

/-! Real realization in paper.tex 1750–1754 and 1784–1805.
The complexification is the actual scalar-extension tensor product. -/
noncomputable section
universe u v
namespace P103.Ch08.RealFormSpecs

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Extend the real group action to ℂ ⊗[ℝ] U. -/
def complexification {U : Type v} [AddCommGroup U] [Module ℝ U]
    (σ : Representation ℝ G U) : Representation ℂ G (TensorProduct ℝ ℂ U) :=
  (Module.End.baseChangeHom ℝ ℂ U).toMonoidHom.comp σ

/-- An actual real representation and an equivariant complex-linear isomorphism.
No real-valued-character certificate is substituted for the real representation. -/
def HasRealForm (ρ : Representation ℂ G V) : Prop :=
  ∃ (U : Type v) (_ : AddCommGroup U) (_ : Module ℝ U)
    (σ : Representation ℝ G U) (e : TensorProduct ℝ ℂ U ≃ₗ[ℂ] V),
    ∀ g z, e (complexification σ g z) = ρ g (e z)

/-- Real-valuedness in the original complex character codomain. -/
def RealCharacter (ρ : Representation ℂ G V) : Prop :=
  ∀ g, star (CharacterSpecs.characterValue ρ g) = CharacterSpecs.characterValue ρ g

/-- A conjugate-linear equivariant map with the specified normalized square. -/
def HasConjugateStructure (ρ : Representation ℂ G V) (ε : ℂ) : Prop :=
  ∃ J : V →ₗ⋆[ℂ] V, (∀ g x, J (ρ g x) = ρ g (J x)) ∧
    ∀ x, J (J x) = ε • x

def realizationType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), Irreducible ℂ G V ρ →
    (FrobeniusSchurSpecs.indicatorValue ρ = 1 ↔ HasRealForm ρ)

def selfDualRealCharacterType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), FrobeniusSchurSpecs.SelfDual ρ → RealCharacter ρ

def negativeType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), Irreducible ℂ G V ρ →
    FrobeniusSchurSpecs.indicatorValue ρ = -1 → RealCharacter ρ ∧ ¬ HasRealForm ρ

def normalizedStructuresType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), Irreducible ℂ G V ρ →
    (FrobeniusSchurSpecs.indicatorValue ρ = 1 → HasConjugateStructure ρ 1) ∧
    (FrobeniusSchurSpecs.indicatorValue ρ = -1 → HasConjugateStructure ρ (-1))

end P103.Ch08.RealFormSpecs
