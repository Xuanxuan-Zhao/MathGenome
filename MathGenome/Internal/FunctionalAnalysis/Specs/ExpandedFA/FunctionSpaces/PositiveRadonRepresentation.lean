import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Regular

/-! Independent statements for the positive part of `fa2:p4:riesz-markov`
(paper.tex, lines 16820–16828). The measurable structure is the Borel
structure, and no continuity or uniform boundedness of the functional is assumed. -/

namespace ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec

open Set MeasureTheory
open scoped ENNReal CompactlySupported

universe u

/-- The paper's convention for a positive Radon measure: compact finiteness,
Borel outer regularity, and compact inner regularity on open sets. -/
def PositiveRadon {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  (∀ K : Set X, IsCompact K → μ K < ∞) ∧
  (∀ A : Set X, MeasurableSet A →
    μ A = ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), μ U) ∧
  (∀ U : Set X, IsOpen U →
    μ U = ⨆ (K : Set X) (_ : K ⊆ U) (_ : IsCompact K), μ K)

/-- Every algebraic positive real-linear functional on `C_c` is represented
by exactly one positive Radon measure. Integrability is included explicitly. -/
def PositiveRepresentation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (I : C_c(X, ℝ) →ₗ[ℝ] ℝ),
    (∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ I f) →
    ∃! μ : Measure X, PositiveRadon μ ∧
      ∀ f : C_c(X, ℝ), Integrable f μ ∧ I f = ∫ x, f x ∂μ

/-- Finite positive Radon measures are compact-inner regular on every Borel set,
without any countability or metrizability hypothesis on the space. -/
def FiniteInnerRegularity : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X),
    PositiveRadon μ → μ univ < ∞ →
    ∀ A : Set X, MeasurableSet A →
      μ A = ⨆ (K : Set X) (_ : K ⊆ A) (_ : IsCompact K), μ K

end ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec
