import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Caratheodory

/-!
Independent specification of paper.tex:588–623. A premeasure evaluates only
members of its algebra. Countable additivity is required only when the union
is in that algebra. No extension, finiteness, or nonemptiness is assumed.
The covering outer measure reuses the shared covering construction.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch02.PremeasureAgreement

/-- The literal source data `p : A → [0,∞]` and its two premeasure axioms. -/
structure Premeasure {α : Type u} (A : Set (Set α)) (hA : IsSetAlgebra A) where
  value : A → ℝ≥0∞
  empty : value ⟨∅, hA.empty_mem⟩ = 0
  iUnion (E : ℕ → A) (hU : (⋃ n, (E n).1) ∈ A)
      (hd : Pairwise fun i j => Disjoint (E i).1 (E j).1) :
    value ⟨⋃ n, (E n).1, hU⟩ = ∑' n, value (E n)

end D11.Ch02.PremeasureAgreement

namespace Specs.D11.Ch02.PremeasureAgreement

open _root_.D11.Ch02.PremeasureAgreement

def premeasure_type : Type (u + 1) :=
  {α : Type u} → (A : Set (Set α)) → IsSetAlgebra A → Type u

def premeasure_value : premeasure_type.{u} := fun A hA => Premeasure A hA

def isSigmaFinite_type : Type (u + 1) :=
  {α : Type u} → {A : Set (Set α)} → {hA : IsSetAlgebra A} → Premeasure A hA → Prop

def isSigmaFinite_value : isSigmaFinite_type.{u} := fun p =>
  ∃ E : ℕ → _, (∀ n, p.value (E n) < ∞) ∧ (⋃ n, (E n).1) = univ

def coveringOuterMeasure_type : Type (u + 1) :=
  {α : Type u} → {A : Set (Set α)} → {hA : IsSetAlgebra A} →
    Premeasure A hA → OuterMeasure α

noncomputable def coveringOuterMeasure_value : coveringOuterMeasure_type.{u} :=
  fun {_α} {A} {hA} p =>
    _root_.Specs.D11.Ch02.OuterCover.coveringOuterMeasure_value
      A hA.empty_mem hA.univ_mem p.value p.empty

def coveringOuterMeasure_apply : Prop :=
  ∀ {α : Type u} {A : Set (Set α)} {hA : IsSetAlgebra A}
    (p : Premeasure A hA) (E : Set α),
    coveringOuterMeasure_value p E =
      ⨅ (F : ℕ → Set α) (hF : ∀ n, F n ∈ A)
        (_ : E ⊆ ⋃ n, F n), ∑' n, p.value ⟨F n, hF n⟩

def algebra_measurable : Prop :=
  ∀ {α : Type u} {A : Set (Set α)} {hA : IsSetAlgebra A}
    (p : Premeasure A hA),
    A ⊆ {s : Set α | ∀ E : Set α,
      coveringOuterMeasure_value p E =
        coveringOuterMeasure_value p (E ∩ s) + coveringOuterMeasure_value p (E \ s)}

def coveringOuterMeasure_agrees : Prop :=
  ∀ {α : Type u} {A : Set (Set α)} {hA : IsSetAlgebra A}
    (p : Premeasure A hA) (s : A), coveringOuterMeasure_value p s.1 = p.value s

end Specs.D11.Ch02.PremeasureAgreement
