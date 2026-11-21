import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureBoundsContinuity
import Mathlib.MeasureTheory.Measure.Regular

/-!
Independent statements for the finite-measure step in paper.tex:5382–5401.
`BorelSpace` says that the given measurable sets are exactly the Borel sets.
All error parameters are positive real numbers, compared with measure via
`ENNReal.ofReal`. No separation, countability, compactness, or metric assumption
is made. Closed approximating sets are not required to be compact.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch18.FiniteClosedOpenRegularClass

/-- The source's class of Borel sets with arbitrarily small closed/open sandwiches. -/
def closedOpenClass {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) : Set (Set X) :=
  {E | MeasurableSet E ∧ ∀ ε : ℝ, 0 < ε →
    ∃ F V : Set X, IsClosed F ∧ IsOpen V ∧ F ⊆ E ∧ E ⊆ V ∧
      μ (V \ F) < ENNReal.ofReal ε}

end D11.Ch18.FiniteClosedOpenRegularClass

namespace Specs.D11.Ch18.FiniteClosedOpenRegularClass

open _root_.D11.Ch18.FiniteClosedOpenRegularClass

/-- Open-set error approximation implies the native weak regularity predicate. -/
def weaklyRegular_of_open_inner : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ],
    (∀ U : Set X, IsOpen U → ∀ ε : ℝ, 0 < ε →
      ∃ F : Set X, F ⊆ U ∧ IsClosed F ∧ μ (U \ F) < ENNReal.ofReal ε) →
    μ.WeaklyRegular

/-- The full sandwich conclusion, with one bound on the whole difference. -/
def borel_closed_open_approximation : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ],
    (∀ U : Set X, IsOpen U → ∀ ε : ℝ, 0 < ε →
      ∃ F : Set X, F ⊆ U ∧ IsClosed F ∧ μ (U \ F) < ENNReal.ofReal ε) →
    ∀ E : Set X, MeasurableSet E → ∀ ε : ℝ, 0 < ε →
      ∃ F V : Set X, IsClosed F ∧ IsOpen V ∧ F ⊆ E ∧ E ⊆ V ∧
        μ (V \ F) < ENNReal.ofReal ε

/-- This is an actual sigma-algebra of subsets, containing every open set. -/
def closedOpenClass_sigmaAlgebra : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ],
    (∀ U : Set X, IsOpen U → ∀ ε : ℝ, 0 < ε →
      ∃ F : Set X, F ⊆ U ∧ IsClosed F ∧ μ (U \ F) < ENNReal.ofReal ε) →
    IsSetAlgebra (closedOpenClass μ) ∧
    (∀ E : ℕ → Set X, (∀ n, E n ∈ closedOpenClass μ) →
      (⋃ n, E n) ∈ closedOpenClass μ) ∧
    (∀ U : Set X, IsOpen U → U ∈ closedOpenClass μ)

/-- In fact its members are exactly all Borel sets. -/
def mem_closedOpenClass_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ],
    (∀ U : Set X, IsOpen U → ∀ ε : ℝ, 0 < ε →
      ∃ F : Set X, F ⊆ U ∧ IsClosed F ∧ μ (U \ F) < ENNReal.ofReal ε) →
    ∀ E : Set X, E ∈ closedOpenClass μ ↔ MeasurableSet E

/-- Both quantitative approximations for every Borel set, with common witnesses. -/
def borel_inner_outer_approximation : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ],
    (∀ U : Set X, IsOpen U → ∀ ε : ℝ, 0 < ε →
      ∃ F : Set X, F ⊆ U ∧ IsClosed F ∧ μ (U \ F) < ENNReal.ofReal ε) →
    ∀ E : Set X, MeasurableSet E → ∀ ε : ℝ, 0 < ε →
      ∃ F V : Set X, IsClosed F ∧ IsOpen V ∧ F ⊆ E ∧ E ⊆ V ∧
        μ (E \ F) < ENNReal.ofReal ε ∧ μ (V \ E) < ENNReal.ofReal ε

/-- Outer regularity and closed inner regularity on all Borel sets. -/
def borel_regularity : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ],
    (∀ U : Set X, IsOpen U → ∀ ε : ℝ, 0 < ε →
      ∃ F : Set X, F ⊆ U ∧ IsClosed F ∧ μ (U \ F) < ENNReal.ofReal ε) →
    μ.OuterRegular ∧ μ.InnerRegularWRT IsClosed MeasurableSet

/-- The corresponding infimum and supremum identities on each Borel set. -/
def borel_measure_formulas : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ],
    (∀ U : Set X, IsOpen U → ∀ ε : ℝ, 0 < ε →
      ∃ F : Set X, F ⊆ U ∧ IsClosed F ∧ μ (U \ F) < ENNReal.ofReal ε) →
    ∀ E : Set X, MeasurableSet E →
      (μ E = ⨆ (F : Set X) (_ : F ⊆ E) (_ : IsClosed F), μ F) ∧
      (μ E = ⨅ (V : Set X) (_ : E ⊆ V) (_ : IsOpen V), μ V)

end Specs.D11.Ch18.FiniteClosedOpenRegularClass
