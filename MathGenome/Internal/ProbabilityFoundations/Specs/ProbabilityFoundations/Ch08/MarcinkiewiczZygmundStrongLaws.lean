import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-! The full conclusion of paper.tex, Theorem `thm:mz-strong`, 2977–2990.
Index k represents the source's X_{k+1}; range n contains n summands.
The space is not completed. Integrability of the nonnegative real p-th
power expresses precisely finiteness of its extended expectation.
The converse allows any real-valued limit function, so in particular a
finite real random variable; no zero-limit or first-moment premise is used. -/
namespace Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundStrongLaws

universe u

def firstMomentType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (p : ℝ), Measurable X → 1 ≤ p →
    Integrable (fun ω => |X ω| ^ p) P → Integrable X P

def subunitType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p : ℝ),
    (∀ k, Measurable (X k)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    0 < p → p < 1 → Integrable (fun ω => |X 0 ω| ^ p) P →
    ∀ᵐ ω ∂P, Tendsto
      (fun n => (∑ k ∈ Finset.range n, X k ω) /
        MarcinkiewiczZygmundTruncation.weight p n) atTop (𝓝 0)

def centeredType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p : ℝ),
    (∀ k, Measurable (X k)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    1 ≤ p → p < 2 → Integrable (fun ω => |X 0 ω| ^ p) P →
    Integrable (X 0) P ∧ ∀ᵐ ω ∂P, Tendsto
      (fun n => ((∑ k ∈ Finset.range n, X k ω) -
          (n : ℝ) * ∫ t, X 0 t ∂P) /
        MarcinkiewiczZygmundTruncation.weight p n) atTop (𝓝 0)

def converseType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p c : ℝ) (Z : Ω → ℝ),
    (∀ k, Measurable (X k)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    0 < p → p < 2 →
    (∀ᵐ ω ∂P, Tendsto
      (fun n => ((∑ k ∈ Finset.range n, X k ω) - (n : ℝ) * c) /
        MarcinkiewiczZygmundTruncation.weight p n) atTop (𝓝 (Z ω))) →
    Integrable (fun ω => |X 0 ω| ^ p) P ∧
      (1 < p → c = ∫ t, X 0 t ∂P)

def exponentOneType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ),
    (∀ k, Measurable (X k)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    Integrable (fun ω => |X 0 ω| ^ (1 : ℝ)) P →
    ∀ᵐ ω ∂P, Tendsto
      (fun n => ((∑ k ∈ Finset.range n, X k ω) -
          (n : ℝ) * ∫ t, X 0 t ∂P) /
        MarcinkiewiczZygmundTruncation.weight 1 n) atTop (𝓝 0)

/-- The centering part, to be applied after the converse has supplied its moment. -/
def centeringAfterMomentType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p c : ℝ) (Z : Ω → ℝ),
    (∀ k, Measurable (X k)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ k, IdentDistrib (X k) (X 0) P P) → 1 < p →
    Integrable (fun ω => |X 0 ω| ^ p) P →
    (∀ᵐ ω ∂P, Tendsto
      (fun n => ((∑ k ∈ Finset.range n, X k ω) - (n : ℝ) * c) /
        MarcinkiewiczZygmundTruncation.weight p n) atTop (𝓝 (Z ω))) →
    c = ∫ t, X 0 t ∂P

end Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundStrongLaws
