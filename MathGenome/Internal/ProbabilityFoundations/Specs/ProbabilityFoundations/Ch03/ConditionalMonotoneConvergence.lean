import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions
import Mathlib.Topology.Order.MonotoneConvergence

/-! The monotone part of paper.tex, Theorem 3.7 (lines 1007–1024).
All inputs take values in the extended nonnegative reals, so no finiteness
or integrability is imposed. The common exceptional set belongs even to G.
The first statement permits arbitrary measurable versions; the second supplies
canonical versions and their defining test identities. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Specs.ProbabilityFoundations.Ch03.ConditionalMonotoneConvergence

open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

universe u

def versionsMonotoneConvergenceType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (Xn : ℕ → Ω → ℝ≥0∞) (X : Ω → ℝ≥0∞),
      (∀ n, Measurable[F] (Xn n)) → Measurable[F] X →
      (∀ᵐ ω ∂P, Monotone (fun n => Xn n ω)) →
      (∀ᵐ ω ∂P, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω))) →
      ∀ (Un : ℕ → Ω → ℝ≥0∞) (U : Ω → ℝ≥0∞),
        (∀ n, nonnegativeVersionValue G P (Xn n) (Un n)) →
        nonnegativeVersionValue G P X U →
        ∃ N : Set Ω, MeasurableSet[G] N ∧ P N = 0 ∧
          ∀ ω, ω ∉ N → Monotone (fun n => Un n ω) ∧
            Tendsto (fun n => Un n ω) atTop (𝓝 (U ω))

def canonicalMonotoneConvergenceType : Prop :=
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (Xn : ℕ → Ω → ℝ≥0∞) (X : Ω → ℝ≥0∞),
      (∀ n, Measurable[F] (Xn n)) → Measurable[F] X →
      (∀ᵐ ω ∂P, Monotone (fun n => Xn n ω)) →
      (∀ᵐ ω ∂P, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω))) →
      (∀ n, nonnegativeVersionValue G P (Xn n)
        (nonnegativeConditionalExpectationValue G P (Xn n))) ∧
      nonnegativeVersionValue G P X (nonnegativeConditionalExpectationValue G P X) ∧
      ∃ N : Set Ω, MeasurableSet[G] N ∧ P N = 0 ∧
        ∀ ω, ω ∉ N →
          Monotone (fun n => nonnegativeConditionalExpectationValue G P (Xn n) ω) ∧
          Tendsto (fun n => nonnegativeConditionalExpectationValue G P (Xn n) ω)
            atTop (𝓝 (nonnegativeConditionalExpectationValue G P X ω))

end Specs.ProbabilityFoundations.Ch03.ConditionalMonotoneConvergence
