import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Completion
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeCommonException
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
Independent statements for paper.tex:1377–1411, versions for a completion.
The completed domain is the canonical Chapter 2 completion. All witnesses are
measurable in the original sigma-algebra, and all a.e. equalities use original
measurable null envelopes. The ordered target is the two-sided extended real
line; its bounds hold everywhere. Real and complex versions are finite-valued
by their codomain. There are no mass, completeness, or nonemptiness assumptions.
-/

open MeasureTheory MeasurableSpace
universe u

namespace Specs.D11.Ch04.CompletionVersions

open Specs.D11.Ch02.Completion
open Specs.D11.Ch04.AeCommonException

def ereal_measurable_iff_bounds : Prop :=
  ∀ {X : Type u} [m : MeasurableSpace X] (μ : Measure X) (f : X → EReal),
    @Measurable X EReal (completedSpace_value μ) (borel EReal) f ↔
      ∃ f₀ f₁ : X → EReal,
        @Measurable X EReal m (borel EReal) f₀ ∧
        @Measurable X EReal m (borel EReal) f₁ ∧
        (∀ x, f₀ x ≤ f x) ∧ (∀ x, f x ≤ f₁ x) ∧ aeEq_value μ f₀ f₁

def ereal_version : Prop :=
  ∀ {X : Type u} [m : MeasurableSpace X] (μ : Measure X) (f : X → EReal),
    @Measurable X EReal (completedSpace_value μ) (borel EReal) f →
      ∃ h : X → EReal, @Measurable X EReal m (borel EReal) h ∧ aeEq_value μ h f

def real_version : Prop :=
  ∀ {X : Type u} [m : MeasurableSpace X] (μ : Measure X) (f : X → ℝ),
    @Measurable X ℝ (completedSpace_value μ) (borel ℝ) f →
      ∃ h : X → ℝ, @Measurable X ℝ m (borel ℝ) h ∧ aeEq_value μ h f

def complex_version : Prop :=
  ∀ {X : Type u} [m : MeasurableSpace X] (μ : Measure X) (f : X → ℂ),
    @Measurable X ℂ (completedSpace_value μ) (borel ℂ) f →
      ∃ h : X → ℂ, @Measurable X ℂ m (borel ℂ) h ∧ aeEq_value μ h f

end Specs.D11.Ch04.CompletionVersions
