import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Conormal

/-! FL-07, paper.tex:608–639. All structural maps are those of the given
compatible tower A → P → B. The presenting algebra may be arbitrary;
neither finite presentation nor nontriviality is assumed. -/
namespace Specs.AdvCommAlg.FormalLifting.SplittingCriterion

universe u v w
noncomputable section

open Specs.AdvCommAlg.Differentials
open TensorProduct

variable (A : Type u) (P : Type v) (B : Type w)
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]

/-- An A-algebra section of the actual map P/I² → B, I = ker(P → B). -/
def HasInfinitesimalSection : Prop :=
  ∃ s : B →ₐ[A] P ⧸ (RingHom.ker (algebraMap P B)) ^ 2,
    (IsScalarTower.toAlgHom A P B).kerSquareLift.comp s = AlgHom.id A B

/-- The full conormal sequence is short exact, and its left arrow has a
B-linear retraction. Together these conditions mean split short exactness.
The shared Conormal is I/I², with its descended B-module structure. -/
def SplitConormal (h : Function.Surjective (algebraMap P B)) : Prop :=
  Function.Injective (conormalMapValue A P B h) ∧
  Function.Exact (conormalMapValue A P B h) (conormalProjectionValue A P B) ∧
  Function.Surjective (conormalProjectionValue A P B) ∧
  ∃ ρ : (B ⊗[P] KaehlerDifferential A P) →ₗ[B] Conormal A P B h,
    ρ.comp (conormalMapValue A P B h) = LinearMap.id

/-- The implication that does not require formal smoothness of P. -/
def sectionImpliesSplit : Prop := ∀ (A : Type u) (P : Type v) (B : Type w)
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
  (h : Function.Surjective (algebraMap P B)),
  HasInfinitesimalSection A P B → SplitConormal A P B h

/-- Both equivalences, for every formally smooth presenting algebra P. -/
def splittingCriterion : Prop := ∀ (A : Type u) (P : Type v) (B : Type w)
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
  (h : Function.Surjective (algebraMap P B)),
  formallySmoothValue A P →
    (formallySmoothValue A B ↔ HasInfinitesimalSection A P B) ∧
    (formallySmoothValue A B ↔ SplitConormal A P B h)

end
end Specs.AdvCommAlg.FormalLifting.SplittingCriterion
