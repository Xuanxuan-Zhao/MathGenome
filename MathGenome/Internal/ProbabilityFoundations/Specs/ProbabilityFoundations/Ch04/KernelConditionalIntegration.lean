import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-! Conditional integration in Theorem 4.8 (paper.tex:1192–1197).
Once a conditional kernel is given, no standard Borel assumption is needed.
The joint law has the given first marginal μ. A conditional kernel given G
is specified by exactly the rectangle test identities of Corollary 4.7.
All measurability refers to the original specified sigma algebras. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch04.KernelConditionalIntegration
open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions
universe u v w

/-- The nonnegative formula, allowing infinite integrals. -/
def nonnegativeJointType : Prop :=
  ∀ {Ω : Type u} {S : Type v} {T : Type w}
    [F : MeasurableSpace Ω] [mS : MeasurableSpace S] [MeasurableSpace T]
    (P : Measure[F] Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (Y : Ω → T), Measurable X → Measurable Y →
    ∀ (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S T) [IsMarkovKernel K],
    P.map (fun ω => (X ω, Y ω)) = μ.compProd K →
    ∀ (f : S × T → ℝ≥0∞), Measurable f →
    nonnegativeVersionValue (mS.comap X) P (fun ω => f (X ω, Y ω))
      (fun ω => ∫⁻ y, f (X ω, y) ∂K (X ω))

/-- The signed formula includes absolute fiber integrability, the canonical
integral, and every measurable extension across the infinite absolute fibers. -/
def realJointType : Prop :=
  ∀ {Ω : Type u} {S : Type v} {T : Type w}
    [F : MeasurableSpace Ω] [mS : MeasurableSpace S] [MeasurableSpace T]
    (P : Measure[F] Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (Y : Ω → T), Measurable X → Measurable Y →
    ∀ (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S T) [IsMarkovKernel K],
    P.map (fun ω => (X ω, Y ω)) = μ.compProd K →
    ∀ (f : S × T → ℝ), Measurable f → Integrable (fun ω => f (X ω, Y ω)) P →
    (∀ᵐ ω ∂P, Integrable (fun y => f (X ω, y)) (K (X ω)) ∧
      (∫⁻ y, ENNReal.ofReal |f (X ω, y)| ∂K (X ω)) < ∞) ∧
    realVersionValue (mS.comap X) P (fun ω => f (X ω, Y ω))
      (fun ω => ∫ y, f (X ω, y) ∂K (X ω)) ∧
    ∀ (g : S → ℝ), Measurable g →
      (∀ s, (∫⁻ y, ENNReal.ofReal |f (s, y)| ∂K s) < ∞ →
        g s = ∫ y, f (s, y) ∂K s) →
      realVersionValue (mS.comap X) P (fun ω => f (X ω, Y ω)) (fun ω => g (X ω))

/-- The defining test identities for the given conditional kernel are hypotheses,
not a conclusion assumed in advance for general product functions. -/
def nonnegativeConditionalType : Prop :=
  ∀ {Ω : Type u} {T : Type w} [F : MeasurableSpace Ω] [mT : MeasurableSpace T]
    (G : MeasurableSpace Ω) (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (Y : Ω → T), Measurable[F] Y →
    ∀ (K : @Kernel Ω T G mT) [IsMarkovKernel K],
    (∀ A, MeasurableSet[G] A → ∀ B, MeasurableSet B →
      (∫⁻ ω in A, K ω B ∂P) = P (A ∩ Y ⁻¹' B)) →
    ∀ (f : Ω × T → ℝ≥0∞), @Measurable _ _ (G.prod mT) _ f →
    @nonnegativeVersionValue Ω G F P (fun ω => f (ω, Y ω))
      (fun ω => ∫⁻ y, f (ω, y) ∂K ω)

/-- Full signed conditional formula on G, with every G-measurable choice on
exceptional fibers. -/
def realConditionalType : Prop :=
  ∀ {Ω : Type u} {T : Type w} [F : MeasurableSpace Ω] [mT : MeasurableSpace T]
    (G : MeasurableSpace Ω) (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (Y : Ω → T), Measurable[F] Y →
    ∀ (K : @Kernel Ω T G mT) [IsMarkovKernel K],
    (∀ A, MeasurableSet[G] A → ∀ B, MeasurableSet B →
      (∫⁻ ω in A, K ω B ∂P) = P (A ∩ Y ⁻¹' B)) →
    ∀ (f : Ω × T → ℝ), @Measurable _ _ (G.prod mT) _ f →
    Integrable (fun ω => f (ω, Y ω)) P →
    (∀ᵐ ω ∂P, Integrable (fun y => f (ω, y)) (K ω) ∧
      (∫⁻ y, ENNReal.ofReal |f (ω, y)| ∂K ω) < ∞) ∧
    @realVersionValue Ω G F P (fun ω => f (ω, Y ω)) (fun ω => ∫ y, f (ω, y) ∂K ω) ∧
    ∀ (g : Ω → ℝ), Measurable[G] g →
      (∀ ω, (∫⁻ y, ENNReal.ofReal |f (ω, y)| ∂K ω) < ∞ →
        g ω = ∫ y, f (ω, y) ∂K ω) →
      @realVersionValue Ω G F P (fun ω => f (ω, Y ω)) g

end Specs.ProbabilityFoundations.Ch04.KernelConditionalIntegration
