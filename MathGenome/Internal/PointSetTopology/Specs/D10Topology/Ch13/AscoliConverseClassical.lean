import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.RealAndEuclideanCompactness

/-! Independent statements of Ascoli necessity and the classical corollaries
(paper.tex, d10:13:ascoli(b), its final assertion, and d10:13:classical-ascoli).
Uniform closure and closedness refer to the source's bounded supremum metric
through its canonical topology. No completeness or nonemptiness is assumed.
Real vector spaces carry their Euclidean (L²) norm, for every natural dimension.
The interval is the subspace Icc a b, including a = b and a > b. -/

noncomputable section
open Set
universe u v
namespace Specs.D10Topology.Ch13.AscoliConverseClassical
open FunctionTopologies

def ascoli_converse : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y],
    Ch11.LocalCompactConventions.LCH X → ∀ A : Set (ContinuousMaps X Y),
    @IsCompact _ compactOpenContinuousTopology
      (@closure _ compactOpenContinuousTopology A) →
    Equicontinuous A ∧ PointwiseRelativelyCompact A

def compactDomain_ascoli_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MetricSpace Y] (A : Set (ContinuousMaps X Y)),
    @IsCompact _ uniformContinuousTopology (@closure _ uniformContinuousTopology A) ↔
      Equicontinuous A ∧ PointwiseRelativelyCompact A

def compactMetric_ascoli_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    (A : Set (ContinuousMaps X Y)),
    @IsCompact _ uniformContinuousTopology (@closure _ uniformContinuousTopology A) ↔
      Equicontinuous A ∧ PointwiseRelativelyCompact A

def euclidean_pointwiseRelativelyCompact_iff_bounded : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (m : ℕ)
    (A : Set (ContinuousMaps X (EuclideanSpace ℝ (Fin m)))),
    PointwiseRelativelyCompact A ↔
      ∀ x : X, ∃ R : ℝ, ∀ f ∈ A, ‖f x‖ ≤ R

def classical_ascoli_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ)
    (A : Set (ContinuousMaps X (EuclideanSpace ℝ (Fin m)))),
    @IsCompact _ uniformContinuousTopology (@closure _ uniformContinuousTopology A) ↔
      Equicontinuous A ∧ (∀ x : X, ∃ R : ℝ, ∀ f ∈ A, ‖f x‖ ≤ R)

def classical_compact_iff_closed : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] (m : ℕ)
    (A : Set (ContinuousMaps X (EuclideanSpace ℝ (Fin m)))),
    Equicontinuous A → (∀ x : X, ∃ R : ℝ, ∀ f ∈ A, ‖f x‖ ≤ R) →
    (@IsCompact _ uniformContinuousTopology A ↔ @IsClosed _ uniformContinuousTopology A)

def interval_lipschitz_compact_closure : Prop :=
  ∀ (a b : ℝ) (m : ℕ)
    (A : Set (ContinuousMaps (Icc a b) (EuclideanSpace ℝ (Fin m))))
    (R L : ℝ), 0 ≤ L →
    (∀ f ∈ A, ∀ x, ‖f x‖ ≤ R) →
    (∀ f ∈ A, ∀ x y, dist (f x) (f y) ≤ L * dist x y) →
    @IsCompact _ uniformContinuousTopology (@closure _ uniformContinuousTopology A)

end Specs.D10Topology.Ch13.AscoliConverseClassical
