import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CompactContentOuterMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates

/-!
Independent specification for the regularity and positivity part of
`paper.tex:5852–5863`, `D11.21.compact_content_radon_measure`.

All measures below have exactly the Borel sigma-algebra. The measure and
content are the shared constructions of the preceding goals, not newly
chosen or rescaled objects. No countability or sigma-finiteness is assumed.
The lower comparison on compact sets is an inequality, not an equality.
-/
noncomputable section
namespace Specs.D11.Ch21.CompactContentRadonMeasure

open Set TopologicalSpace MeasureTheory
open scoped ENNReal
open Specs.D11.Ch21.CompactContentOuterMeasure
open Specs.D11.Ch18
universe u

/-- Finiteness on every compact set, including the empty compact. -/
def compact_finite : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (c : Content X), RadonPredicates.compactFiniteValue (borelMeasure_value c)

/-- Outer approximation on all Borel sets, with extended-real values. -/
def outer_regular_borel : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] (c : Content X),
    RadonPredicates.outerRegularBorelValue (borelMeasure_value c)

/-- Compact inner approximation on opens; no all-Borel inner regularity is added. -/
def compact_inner_regular_open : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (c : Content X), RadonPredicates.compactInnerRegularOpenValue (borelMeasure_value c)

/-- The source comparison between compact content and the resulting measure. -/
def content_le_measure : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X]
    (c : Content X) (K : Compacts X), c K ≤ borelMeasure_value c (K : Set X)

/-- Left invariance of the Borel restriction, transported from content invariance. -/
def left_invariant : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (c : Content G)
    (_hc : ∀ (a : G) (K : Compacts G),
      c (K.map (fun x => a * x) (continuous_const_mul a)) = c K)
    (a : G) (E : Set G), MeasurableSet[borel G] E →
      borelMeasure_value c ((fun x => a * x) '' E) = borelMeasure_value c E

/-- The full remaining conclusion for every content supplied by the original
compact-product construction, with its original normalization compact `K₀`.
In particular its measure is nonzero; no assertion `μ K₀ = 1` is made. -/
def compact_content_radon_measure : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (K₀ : PositiveCompacts G) (h : Compacts G → ℝ)
    (hh : CompactContentCluster.ContentProperties G K₀ h),
    let μ := borelMeasure_value (sourceContent_value K₀ h hh)
    RadonPredicates.isRadonValue μ ∧
      (∀ (a : G) (E : Set G), MeasurableSet[borel G] E →
        μ ((fun x => a * x) '' E) = μ E) ∧
      (∀ K : Compacts G, ENNReal.ofReal (h K) ≤ μ (K : Set G)) ∧
      (1 ≤ μ (K₀ : Set G) ∧ μ (K₀ : Set G) < ∞) ∧ μ ≠ 0

end Specs.D11.Ch21.CompactContentRadonMeasure
