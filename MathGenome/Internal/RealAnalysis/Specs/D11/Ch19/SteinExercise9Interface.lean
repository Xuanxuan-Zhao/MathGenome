import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent statements of paper.tex:5619–5626.
The domain is the closed interval with its relative topology and exactly its
Borel sigma-algebra. Functionals are merely real-linear at input; boundedness
is a conclusion. The hypothesis a ≤ b includes the singleton interval.
Every integral identity carries actual scalar absolute integrability. -/
namespace Specs.D11.Ch19.SteinExercise9Interface

open Set MeasureTheory
open Specs.D11.Ch06.ScalarIntegral

local instance (priority := 2000) {X : Type} [TopologicalSpace X] : MeasurableSpace X := borel X

/-- Positivity gives representation, unique among all finite Borel measures. -/
def positive_representation : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ (I : C(Icc a b, ℝ) →ₗ[ℝ] ℝ),
    (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f) →
    ∃! μ : @Measure (Icc a b) (borel (Icc a b)),
      IsFiniteMeasure μ ∧ ∀ f : C(Icc a b, ℝ),
        ∃ hf : scalarIntegrable_value μ f, I f = scalarIntegral_value μ f hf

/-- Automatic boundedness and the exact operator norm, with no continuity assumption. -/
def bounded_norm : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ (I : C(Icc a b, ℝ) →ₗ[ℝ] ℝ),
    (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f) →
    ∃ L : C(Icc a b, ℝ) →L[ℝ] ℝ,
      L.toLinearMap = I ∧ ‖L‖ = I 1

/-- Every finite positive Borel measure defines a unique positive real-linear
integration functional. The preceding theorem gives its norm. -/
def measure_induces_functional : Prop :=
  ∀ (a b : ℝ), a ≤ b →
    ∀ (μ : @Measure (Icc a b) (borel (Icc a b))), IsFiniteMeasure μ →
    ∃! I : C(Icc a b, ℝ) →ₗ[ℝ] ℝ,
      (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f) ∧
      ∀ f : C(Icc a b, ℝ), ∃ hf : scalarIntegrable_value μ f,
        I f = scalarIntegral_value μ f hf

end Specs.D11.Ch19.SteinExercise9Interface
