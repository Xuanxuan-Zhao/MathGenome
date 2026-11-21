import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.TestFunctionLFTopology
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent specification of `paper.tex:20235–20279`,
`fa2:p4:hardy-whitney`. The standing hypothesis `d ≥ 1` is stated at
paper.tex:19997. The norm on `Fin d → ℝ` is the supremum norm, as used in
the source's cubical proof. Closed dyadic cubes include their boundaries.
All constants below are uniform over the open sets and the chosen cubes. -/

open Set TopologicalSpace MeasureTheory

namespace ExpandedFA.PartIV.HardyWhitney
open ExpandedFA.Distributions

/-- The standard dyadic cube with side `2 ^ level` and lower corner
`2 ^ level * corner`. Different cubes use the same dyadic grid. -/
structure DyadicCube (d : ℕ) where
  level : ℤ
  corner : Fin d → ℤ
  deriving DecidableEq

namespace DyadicCube

noncomputable def side {d : ℕ} (Q : DyadicCube d) : ℝ := (2 : ℝ) ^ Q.level

noncomputable def center {d : ℕ} (Q : DyadicCube d) : Domain d :=
  fun i => Q.side * ((Q.corner i : ℝ) + 1 / 2)

/-- Concentric dilation by a side-length factor; this is a closed cube in
supremum-norm coordinates. -/
noncomputable def dilate {d : ℕ} (Q : DyadicCube d) (t : ℝ) : Set (Domain d) :=
  Metric.closedBall Q.center (t * Q.side / 2)

noncomputable def carrier {d : ℕ} (Q : DyadicCube d) : Set (Domain d) := Q.dilate 1

noncomputable def star {d : ℕ} (Q : DyadicCube d) : Set (Domain d) := Q.dilate (9 / 8)

end DyadicCube

/-- Only the nonempty finite-measure open sets from the source lemma. -/
def EligibleOpen (d : ℕ) :=
  {Ω : Opens (Domain d) // (Ω : Set (Domain d)).Nonempty ∧ volume (Ω : Set (Domain d)) < ⊤}

/-- A family is indexed by a subset of the countable, standard dyadic grid.
The real test functions are globally smooth, with compact topological
support contained in the open domain. -/
structure Partition {d : ℕ} (Ω : Opens (Domain d)) where
  cubes : Set (DyadicCube d)
  weight : cubes → Tests ℝ Ω

/-- Full single-level geometric and analytic estimates. Coordinate words
list all multi-index derivatives (with repetitions); a constant for each
order is equivalent to constants for each multi-index in fixed dimension. -/
def PartitionEstimates {d : ℕ} {Ω : Opens (Domain d)}
    (c C : ℝ) (A : ℕ → ℝ) (N : ℕ) (W : Partition Ω) : Prop :=
  (⋃ Q : W.cubes, Q.val.carrier) = Ω ∧
  W.cubes.Pairwise (fun Q R => Disjoint (interior Q.carrier) (interior R.carrier)) ∧
  (∀ Q : W.cubes, IsCompact Q.val.star ∧ Q.val.star ⊆ Ω) ∧
  LocallyFinite (fun Q : W.cubes => (Subtype.val : Ω → Domain d) ⁻¹' Q.val.star) ∧
  (∀ x, {Q : W.cubes | x ∈ Q.val.star}.Finite ∧
    {Q : W.cubes | x ∈ Q.val.star}.ncard ≤ N) ∧
  (∀ Q : W.cubes, ∀ x, 0 ≤ W.weight Q x) ∧
  (∀ Q : W.cubes, tsupport (W.weight Q) ⊆ Q.val.star) ∧
  (∀ x ∈ Ω, ∑ᶠ Q : W.cubes, W.weight Q x = 1) ∧
  (∀ Q : W.cubes, Integrable (W.weight Q) ∧
    c * (volume Q.val.carrier).toReal ≤ ∫ x, W.weight Q x) ∧
  (∀ (Q : W.cubes) (k : ℕ) (a : Fin k → Fin d) (x : Domain d),
    ‖iteratedFDeriv ℝ k (W.weight Q) x (fun j => coordinateVector (a j))‖ ≤
      A k * Q.val.side ^ (-(k : ℤ))) ∧
  (∀ Q R : W.cubes, (Q.val.star ∩ R.val.star).Nonempty →
    Q.val.side ≤ C * R.val.side ∧ R.val.side ≤ C * Q.val.side)

/-- Fine and coarse enlargements have the nested-level containment and the
uniform bound on the number of coarse cubes meeting one fixed fine cube.
The explicit finiteness assertion prevents the infinite-set convention for
`Set.ncard` from weakening the required bound. -/
def NestedEstimates {d : ℕ} {Ω Ω' : Opens (Domain d)}
    (C : ℝ) (N : ℕ) (W : Partition Ω) (W' : Partition Ω') : Prop :=
  (∀ (R : W'.cubes) (Q : W.cubes), (R.val.star ∩ Q.val.star).Nonempty →
    R.val.side ≤ C * Q.val.side ∧ R.val.star ⊆ Q.val.dilate C) ∧
  (∀ R : W'.cubes,
    {Q : W.cubes | (R.val.star ∩ Q.val.star).Nonempty}.Finite ∧
    {Q : W.cubes | (R.val.star ∩ Q.val.star).Nonempty}.ncard ≤ N)

/-- Quantitative distance estimates used by the maximal-twentyfold-cube
construction. These are proof tools, not hypotheses of the existence theorem.
For every point of the 9/8 enlargement the boundary distance lies between
nine and twenty-two side lengths. -/
def DistanceBounds {d : ℕ} (Ω : Set (Domain d)) (S : Set (DyadicCube d)) : Prop :=
  ∀ Q ∈ S, ∀ x ∈ Q.star,
    9 * Q.side ≤ Metric.infDist x Ωᶜ ∧ Metric.infDist x Ωᶜ ≤ 22 * Q.side

/-- The geometric part of the construction, with explicit absolute
constants. The final existence theorem does not assume this predicate. -/
def CubeGeometry {d : ℕ} (Ω : Opens (Domain d)) (S : Set (DyadicCube d)) : Prop :=
  (⋃ Q : S, Q.val.carrier) = Ω ∧
  S.Pairwise (fun Q R => Disjoint (interior Q.carrier) (interior R.carrier)) ∧
  (∀ Q : S, IsCompact Q.val.star ∧ Q.val.star ⊆ Ω) ∧
  LocallyFinite (fun Q : S => (Subtype.val : Ω → Domain d) ⁻¹' Q.val.star) ∧
  (∀ x, {Q : S | x ∈ Q.val.star}.Finite ∧ {Q : S | x ∈ Q.val.star}.ncard ≤ 30 ^ d) ∧
  (∀ Q R : S, (Q.val.star ∩ R.val.star).Nonempty →
    Q.val.side ≤ 3 * R.val.side ∧ R.val.side ≤ 3 * Q.val.side) ∧
  DistanceBounds Ω S

end ExpandedFA.PartIV.HardyWhitney

namespace Specs.ExpandedFA.PartIV.HardyWhitney
open _root_.ExpandedFA.PartIV.HardyWhitney
open _root_.ExpandedFA.Distributions

/-- A separately checkable geometric subobligation of the full source
lemma. It retains all nonempty finite-measure open sets in positive dimension. -/
def geometricWhitneyType : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ Ω : EligibleOpen d,
    ∃ S : Set (DyadicCube d), CubeGeometry Ω.val S

/-- A simultaneous choice for all eligible open sets makes the nested-level
quantifiers explicit. Constants depend only on dimension (and derivative
order for `A`), not on either open set or any cube. -/
def smoothWhitneyType : Prop :=
  ∀ (d : ℕ), 0 < d →
    ∃ (c C : ℝ) (A : ℕ → ℝ) (N : ℕ),
      0 < c ∧ 1 ≤ C ∧ (∀ k, 0 < A k) ∧ 0 < N ∧
      ∃ W : ∀ Ω : EligibleOpen d, Partition Ω.val,
        (∀ Ω, PartitionEstimates c C A N (W Ω)) ∧
        (∀ Ω Ω' : EligibleOpen d,
          (Ω'.val : Set (Domain d)) ⊆ Ω.val → NestedEstimates C N (W Ω) (W Ω'))

end Specs.ExpandedFA.PartIV.HardyWhitney
