import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Corollary 3.6 (paper.tex 986–1002), on the specified arbitrary probability
space and arbitrary sub-sigma-algebra. The exponent ranges over ENNReal, so
it includes infinity. Both canonical Lp seminorms are specified; at infinity
these use the essential supremum. MemLp supplies integrability when p ≥ 1.
No completeness of either sigma-algebra is assumed. -/

open MeasureTheory
open scoped ENNReal
open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

namespace Specs.ProbabilityFoundations.Ch03.ConditionalLpContraction

universe u

def absoluteValueBoundType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), Integrable X P →
      ∀ᵐ ω ∂P, |realConditionalExpectationValue G P X ω| ≤
        realConditionalExpectationValue G P (fun ω => |X ω|) ω

def lpContractionType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (X : Ω → ℝ), MemLp X p P →
      Integrable X P ∧ MemLp (realConditionalExpectationValue G P X) p P ∧
        eLpNorm (realConditionalExpectationValue G P X) p P ≤ eLpNorm X p P ∧
        lpNorm (realConditionalExpectationValue G P X) p P ≤ lpNorm X p P

def essSupContractionType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), MemLp X ∞ P →
      essSup (fun ω => |realConditionalExpectationValue G P X ω|) P ≤
        essSup (fun ω => |X ω|) P

def lpDistanceContractionType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (X Y : Ω → ℝ),
      Integrable X P → Integrable Y P → MemLp X p P → MemLp Y p P →
      MemLp (fun ω => realConditionalExpectationValue G P X ω -
        realConditionalExpectationValue G P Y ω) p P ∧
      eLpNorm (fun ω => realConditionalExpectationValue G P X ω -
        realConditionalExpectationValue G P Y ω) p P ≤
        eLpNorm (fun ω => X ω - Y ω) p P ∧
      lpNorm (fun ω => realConditionalExpectationValue G P X ω -
        realConditionalExpectationValue G P Y ω) p P ≤
        lpNorm (fun ω => X ω - Y ω) p P

end Specs.ProbabilityFoundations.Ch03.ConditionalLpContraction
