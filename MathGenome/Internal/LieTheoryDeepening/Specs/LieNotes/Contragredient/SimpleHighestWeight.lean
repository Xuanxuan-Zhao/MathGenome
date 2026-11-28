import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.VermaModules
import Mathlib.RingTheory.SimpleModule.Basic

/-! The simple highest-weight quotient of a contragredient Verma module. -/

namespace Specs.LieNotes.Contragredient.SimpleHighestWeight

open CartanData CartanQuotient
open VermaModules (Verma IsWeightCharacter IsHighestVector cartanAction)
open WeightExtraction (weightSpace)
open _root_.RepTheorySurvey.CategoryO.BorelInduction (U)

noncomputable section

universe u v w
set_option linter.checkUnivs false

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]
  (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ)

/-- The sum of all proper enveloping-algebra submodules of the Verma module. -/
def radical : Submodule (U (Algebra R)) (Verma R Λ hχ) :=
  sSup {N | N ≠ ⊤}

/-- The canonical highest-weight quotient. -/
abbrev L := Verma R Λ hχ ⧸ radical R Λ hχ

/-- The canonical projection from the Verma module. -/
def quotientMap : Verma R Λ hχ →ₗ[U (Algebra R)] L R Λ hχ :=
  (radical R Λ hχ).mkQ

/-- The image of the highest-weight generator under the quotient projection. -/
def top : L R Λ hχ :=
  quotientMap R Λ hχ (VermaModules.top R Λ hχ)

/-- The full common eigenspace for the Cartan action on the quotient. -/
def weightSpaceAt (μ : Module.Dual ℂ H) : Submodule ℂ (L R Λ hχ) :=
  weightSpace (cartanAction R (L R Λ hχ)) μ

def RadicalType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ),
    Submodule (U (Algebra R)) (Verma R Λ hχ)

def LType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (Λ : Module.Dual ℂ H),
    (∃! χ, IsWeightCharacter R Λ χ) → Type (max u v)

def QuotientMapType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ),
    Verma R Λ hχ →ₗ[U (Algebra R)] L R Λ hχ

def TopType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ),
    L R Λ hχ

def WeightSpaceAtType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ),
    Module.Dual ℂ H → Submodule ℂ (L R Λ hχ)

/-- The radical is proper and contains every proper submodule. -/
def RadicalIsGreatest : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ),
    IsGreatest {N : Submodule (U (Algebra R)) (Verma R Λ hχ) | N ≠ ⊤} (radical R Λ hχ)

def SimpleModule : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ),
    IsSimpleModule (U (Algebra R)) (L R Λ hχ)

def TopHighest : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ),
    top R Λ hχ ≠ 0 ∧ IsHighestVector R Λ (top R Λ hχ)

/-- Every simple quotient is uniquely isomorphic to the canonical one over the Verma module. -/
def UniqueSimpleQuotient : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ)
    (V : Type w) [AddCommGroup V] [Module (U (Algebra R)) V] [IsSimpleModule (U (Algebra R)) V]
    (q : Verma R Λ hχ →ₗ[U (Algebra R)] V), Function.Surjective q →
    ∃! e : L R Λ hχ ≃ₗ[U (Algebra R)] V, e.toLinearMap.comp (quotientMap R Λ hχ) = q

/-- Each quotient weight space is the image of the corresponding Verma weight space. -/
def WeightSpaceImage : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ)
    (μ : Module.Dual ℂ H),
    weightSpaceAt R Λ hχ μ =
      (VermaModules.weightSpaceAt R Λ hχ μ).map ((quotientMap R Λ hχ).restrictScalars ℂ)

end

end Specs.LieNotes.Contragredient.SimpleHighestWeight
