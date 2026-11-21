import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Partitions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic

/-! Independent specification of K03.15.rs_sums, paper.tex:3670–3686.
The scalar action by the real increment is ordinary multiplication for real
values and multiplication by the real embedding for complex values. All tags
belong to closed cells. Functions on ℝ are used only on the indicated interval.
The auxiliary definitions work in any real normed vector space; existence in
the Cauchy criterion is asserted separately for precisely ℝ and ℂ. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsSums
open _root_.SingleVariableAnalysis.Riemann
open scoped BigOperators
universe u

abbrev boundedOnType := {E : Type u} → [NormedAddCommGroup E] → ℝ → ℝ → (ℝ → E) → Prop
def boundedOnValue : boundedOnType := fun a b f =>
  ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M

abbrev sumType := {E : Type u} → [AddCommGroup E] → [Module ℝ E] →
  {a b : ℝ} → (P : PartitionData a b) →
  Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P → (ℝ → E) → (ℝ → ℝ) → E
noncomputable def sumValue : sumType := fun P t f α =>
  ∑ i : Fin P.n, (α (P.point i.succ) - α (P.point i.castSucc)) • f (t i)

abbrev limitType := {E : Type u} → [NormedAddCommGroup E] → [Module ℝ E] →
  ℝ → ℝ → (ℝ → E) → (ℝ → ℝ) → E → Prop
def limitValue : limitType := fun a b f α I =>
  ∀ ε : ℝ, 0 < ε → ∃ P₀ : PartitionData a b,
    ∀ P : PartitionData a b,
      Specs.SingleVariableAnalysis.Ch08.Partitions.refinesValue P P₀ →
      ∀ t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P,
        ‖sumValue P t f α - I‖ < ε

abbrev cauchyForwardType := {E : Type u} → [NormedAddCommGroup E] → [Module ℝ E] →
  ℝ → ℝ → (ℝ → E) → (ℝ → ℝ) → Prop
def cauchyForwardValue : cauchyForwardType := fun a b f α =>
  ∀ ε : ℝ, 0 < ε → ∃ P₀ : PartitionData a b,
    ∀ P : PartitionData a b,
      Specs.SingleVariableAnalysis.Ch08.Partitions.refinesValue P P₀ →
      ∀ t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P,
      ∀ Q : PartitionData a b,
        Specs.SingleVariableAnalysis.Ch08.Partitions.refinesValue Q P₀ →
        ∀ u : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue Q,
          ‖sumValue P t f α - sumValue Q u f α‖ < ε

abbrev integralType := limitType
def integralValue : integralType := fun a b f α I =>
  boundedOnValue (min a b) (max a b) f ∧
  boundedOnValue (min a b) (max a b) α ∧
  if a ≤ b then limitValue a b f α I else limitValue b a f α (-I)

abbrev cauchyType := cauchyForwardType
def cauchyValue : cauchyType := fun a b f α =>
  boundedOnValue (min a b) (max a b) f ∧
  boundedOnValue (min a b) (max a b) α ∧
  if a ≤ b then cauchyForwardValue a b f α else cauchyForwardValue b a f α

def unique : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [Module ℝ E]
  (a b : ℝ) (f : ℝ → E) (α : ℝ → ℝ) (I J : E),
  integralValue a b f α I → integralValue a b f α J → I = J

def realCauchy : Prop := ∀ (a b : ℝ) (f α : ℝ → ℝ),
  (∃ I : ℝ, integralValue a b f α I) ↔ cauchyValue a b f α

def complexCauchy : Prop := ∀ (a b : ℝ) (f : ℝ → ℂ) (α : ℝ → ℝ),
  (∃ I : ℂ, integralValue a b f α I) ↔ cauchyValue a b f α

def degenerateSum : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [Module ℝ E]
  (a : ℝ) (P : PartitionData a a)
  (t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P)
  (f : ℝ → E) (α : ℝ → ℝ), sumValue P t f α = 0

def degenerateIntegral : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [Module ℝ E]
  (a : ℝ) (f : ℝ → E) (α : ℝ → ℝ) (I : E),
  integralValue a a f α I ↔ I = 0

def orientation : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [Module ℝ E]
  (a b : ℝ) (f : ℝ → E) (α : ℝ → ℝ) (I : E),
  integralValue a b f α I ↔ integralValue b a f α (-I)

def realSumFormula : Prop := ∀ {a b : ℝ} (P : PartitionData a b)
  (t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P)
  (f α : ℝ → ℝ),
  sumValue P t f α = ∑ i : Fin P.n,
    f (t i) * (α (P.point i.succ) - α (P.point i.castSucc))

def complexSumFormula : Prop := ∀ {a b : ℝ} (P : PartitionData a b)
  (t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P)
  (f : ℝ → ℂ) (α : ℝ → ℝ),
  sumValue P t f α = ∑ i : Fin P.n,
    f (t i) * ((α (P.point i.succ) - α (P.point i.castSucc) : ℝ) : ℂ)

def forwardIntegralIff : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [Module ℝ E]
  (a b : ℝ) (_hab : a ≤ b) (f : ℝ → E) (α : ℝ → ℝ) (I : E),
  integralValue a b f α I ↔
    boundedOnValue a b f ∧ boundedOnValue a b α ∧
    ∀ ε : ℝ, 0 < ε → ∃ P₀ : PartitionData a b,
      ∀ P : PartitionData a b,
        Specs.SingleVariableAnalysis.Ch08.Partitions.refinesValue P P₀ →
        ∀ t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P,
          ‖sumValue P t f α - I‖ < ε

end Specs.SingleVariableAnalysis.Ch15.RsSums
