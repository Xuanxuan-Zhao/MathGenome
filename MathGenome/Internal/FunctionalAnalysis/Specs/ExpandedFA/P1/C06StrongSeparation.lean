import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent statements for `fa2:p1:c06:strong-separation`, paper.tex:1122–1136.

The supremum is the real supremum of the functional image. Nonemptiness and
explicit boundedness make it a finite supremum, even when C is unbounded.
All complex duals consist of continuous complex-linear functionals and all
convexity is real convexity. No normed space is assumed complete. The locally
convex statements use the given Hausdorff topology and the native TVS/LCS
structures shared with `TvsDefinitions`; no norm or metrizability is required.
-/
namespace Specs.ExpandedFA.P1.C06StrongSeparation
universe u

def realQuantitativeType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (x₀ : E), C.Nonempty → IsClosed C → Convex ℝ C → x₀ ∉ C →
    ∀ r : ℝ, 0 < r → r < Metric.infDist x₀ C →
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ BddAbove (f '' C) ∧
      sSup (f '' C) < f x₀ ∧ r * ‖f‖ ≤ f x₀ - sSup (f '' C)

def complexQuantitativeType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C : Set E) (x₀ : E), C.Nonempty → IsClosed C → Convex ℝ C → x₀ ∉ C →
    ∀ r : ℝ, 0 < r → r < Metric.infDist x₀ C →
    ∃ f : E →L[ℂ] ℂ, f ≠ 0 ∧ BddAbove ((fun x => (f x).re) '' C) ∧
      sSup ((fun x => (f x).re) '' C) < (f x₀).re ∧
      r * ‖f‖ ≤ (f x₀).re - sSup ((fun x => (f x).re) '' C)

def realNormedType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (x₀ : E), C.Nonempty → IsClosed C → Convex ℝ C → x₀ ∉ C →
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ BddAbove (f '' C) ∧ sSup (f '' C) < f x₀

def complexNormedType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C : Set E) (x₀ : E), C.Nonempty → IsClosed C → Convex ℝ C → x₀ ∉ C →
    ∃ f : E →L[ℂ] ℂ, f ≠ 0 ∧ BddAbove ((fun x => (f x).re) '' C) ∧
      sSup ((fun x => (f x).re) '' C) < (f x₀).re

def realLocallyConvexType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    (C : Set E) (x₀ : E), C.Nonempty → IsClosed C → Convex ℝ C → x₀ ∉ C →
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ BddAbove (f '' C) ∧ sSup (f '' C) < f x₀

def complexLocallyConvexType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    (C : Set E) (x₀ : E), C.Nonempty → IsClosed C → Convex ℝ C → x₀ ∉ C →
    ∃ f : E →L[ℂ] ℂ, f ≠ 0 ∧ BddAbove ((fun x => (f x).re) '' C) ∧
      sSup ((fun x => (f x).re) '' C) < (f x₀).re


def realLocallyConvexCompactType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    (C D : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    D.Nonempty → IsCompact D → Convex ℝ D → Disjoint C D →
    ∃ (h : E →L[ℝ] ℝ) (δ : ℝ), h ≠ 0 ∧ 0 < δ ∧
      ∀ c ∈ C, ∀ d ∈ D, h c + δ ≤ h d

def complexLocallyConvexCompactType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    (C D : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    D.Nonempty → IsCompact D → Convex ℝ D → Disjoint C D →
    ∃ (h : E →L[ℝ] ℝ) (f : E →L[ℂ] ℂ) (δ : ℝ),
      h ≠ 0 ∧ f ≠ 0 ∧ (∀ x, h x = (f x).re) ∧ 0 < δ ∧
        ∀ c ∈ C, ∀ d ∈ D, h c + δ ≤ h d

def realNormedCompactType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C D : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    D.Nonempty → IsCompact D → Convex ℝ D → Disjoint C D →
    ∃ (h : E →L[ℝ] ℝ) (δ : ℝ), h ≠ 0 ∧ 0 < δ ∧
      ∀ c ∈ C, ∀ d ∈ D, h c + δ ≤ h d

def complexNormedCompactType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C D : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    D.Nonempty → IsCompact D → Convex ℝ D → Disjoint C D →
    ∃ (h : E →L[ℝ] ℝ) (f : E →L[ℂ] ℂ) (δ : ℝ),
      h ≠ 0 ∧ f ≠ 0 ∧ (∀ x, h x = (f x).re) ∧ 0 < δ ∧
        ∀ c ∈ C, ∀ d ∈ D, h c + δ ≤ h d

end Specs.ExpandedFA.P1.C06StrongSeparation
