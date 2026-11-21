import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Counting spaces on arbitrary types, paper.tex:3475–3489.
Every assertion explicitly uses the full power-set sigma-algebra. Exponents
are extended nonnegative reals; `1 ≤ p < q` includes every real exponent in
the source and the infinite endpoint. The raw spaces and norms are exactly
the shared ordinary measurable representative spaces and source norms.
The quotient embedding below preserves the underlying sequence. Its bound
is stated on representatives, whose norms are the quotient norms by the
upstream quotient construction. No countability of the index type is assumed.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch10.SequenceSpaceInclusion
open Specs.D11.Ch10.QuotientConstruction

def counting_integral : Prop := ∀ {I : Type u} (f : I → ℝ≥0∞),
  letI : MeasurableSpace I := ⊤
  Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value Measure.count f =
    ∑' i, f i

def counting_sum : Prop := ∀ {I : Type u} (f : I → ℝ≥0∞),
  (∑' i, f i) = ⨆ s : Finset I, ∑ i ∈ s, f i

def counting_relation : Prop := ∀ {I : Type u} {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI : MeasurableSpace I := ⊤
  ∀ (p : ℝ≥0∞) (f g : Raw (X := I) (𝕜 := 𝕜) Measure.count p),
    nullRelation Measure.count p f g ↔ f.val = g.val

def raw_inclusion : Prop := ∀ {I : Type u} {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI : MeasurableSpace I := ⊤
  ∀ (p q : ℝ≥0∞), 1 ≤ p → p < q → ∀ f : I → 𝕜,
    f ∈ rawSpace Measure.count p →
      f ∈ rawSpace Measure.count q ∧
      sourceNorm Measure.count q f ≤ sourceNorm Measure.count p f

def countable_support : Prop := ∀ {I : Type u} {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI : MeasurableSpace I := ⊤
  ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ → ∀ f : Raw (X := I) (𝕜 := 𝕜) Measure.count p,
    (Function.support f.val).Countable

def quotient_inclusion : Prop := ∀ {I : Type u} {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI : MeasurableSpace I := ⊤
  ∀ (p q : ℝ≥0∞), 1 ≤ p → p < q →
    ∃ F : QuotientLp (X := I) (𝕜 := 𝕜) Measure.count p ↪ QuotientLp (X := I) (𝕜 := 𝕜) Measure.count q,
      ∀ f : Raw (X := I) (𝕜 := 𝕜) Measure.count p,
        ∃ hq : f.val ∈ rawSpace Measure.count q,
          F (classOf f) = classOf ⟨f.val, hq⟩ ∧
          sourceNorm Measure.count q f.val ≤ sourceNorm Measure.count p f.val

end Specs.D11.Ch10.SequenceSpaceInclusion
