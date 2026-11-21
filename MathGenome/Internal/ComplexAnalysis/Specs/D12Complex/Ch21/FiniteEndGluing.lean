import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.PuncturedDiskLoops
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-! Independent data and statements for the finite attachment in paper.tex:3703–3710.
Only ordinary maps of the original spaces are input. The topology on the exact
carrier `E ⊕ J` is defined by its final-topology construction, not assumed. -/
noncomputable section
open Set Topology

namespace D12Complex.FiniteEndGluing
universe u v w

abbrev Parameter (r : ℝ) := D12Complex.Ch20.PuncturedDiskLoops.Disk r
abbrev FullDisk (r : ℝ) := Metric.ball (0 : ℂ) r

/-- Inclusion of the original punctured parameter domain into its full disk. -/
def punctureInclusion {r : ℝ} (t : Parameter r) : FullDisk r :=
  ⟨t, by simpa only [Metric.mem_ball, dist_zero_right] using t.property.2⟩

/-- All inputs are facts about ordinary maps on the old space and plane disks.
Coincident centers are allowed, with disjointness required only in that case. -/
structure Data (E : Type u) (J : Type v) (B : Type w)
    [TopologicalSpace E] [TopologicalSpace B] where
  radius : J → ℝ
  radius_pos : ∀ j, 0 < radius j
  theta : (j : J) → Parameter (radius j) → E
  theta_openEmbedding : ∀ j, IsOpenEmbedding (theta j)
  projection : E → B
  projection_continuous : Continuous projection
  diskProjection : (j : J) → FullDisk (radius j) → B
  diskProjection_continuous : ∀ j, Continuous (diskProjection j)
  agrees : ∀ j t, diskProjection j (punctureInclusion t) = projection (theta j t)
  avoids : ∀ x j, projection x ≠ diskProjection j
    ⟨0, by simpa only [Metric.mem_ball, dist_self] using radius_pos j⟩
  disjoint : ∀ j k, j ≠ k →
    diskProjection j ⟨0, by simpa only [Metric.mem_ball, dist_self] using radius_pos j⟩ =
      diskProjection k ⟨0, by simpa only [Metric.mem_ball, dist_self] using radius_pos k⟩ →
    Disjoint (range (theta j)) (range (theta k))

namespace Data
variable {E : Type u} {J : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace B] (d : Data E J B)

/-- The missing center in the full parameter disk. -/
def center (j : J) : FullDisk (d.radius j) :=
  ⟨0, by simpa only [Metric.mem_ball, dist_self] using d.radius_pos j⟩

/-- The exact full-disk attachment map. -/
def psi (j : J) (t : FullDisk (d.radius j)) : E ⊕ J := by
  classical
  exact if h : (t : ℂ) = 0 then Sum.inr j else
    Sum.inl (d.theta j ⟨t, norm_pos_iff.mpr h,
      by simpa only [Metric.mem_ball, dist_zero_right] using t.property⟩)

/-- The finest topology making the old inclusion and every full-disk map continuous.
Mathlib orders topologies by reverse inclusion of their open sets. -/
@[instance_reducible] def topology : TopologicalSpace (E ⊕ J) :=
  TopologicalSpace.coinduced (Sum.inl : E → E ⊕ J) inferInstance ⊔
    ⨆ j, TopologicalSpace.coinduced (d.psi j) inferInstance

/-- The actual extended projection with prescribed old and center values. -/
def extendedProjection : E ⊕ J → B
  | Sum.inl x => d.projection x
  | Sum.inr j => d.diskProjection j (d.center j)


/-- Literal closed parameter disk, included in the full open parameter disk. -/
def closedDiskMap (j : J) (s : ℝ) (hs : s < d.radius j)
    (t : Metric.closedBall (0 : ℂ) s) : E ⊕ J :=
  d.psi j ⟨t, lt_of_le_of_lt t.property hs⟩

end Data
end D12Complex.FiniteEndGluing

namespace Specs.D12Complex.Ch21.FiniteEndGluing
open _root_.D12Complex.FiniteEndGluing
universe u v w

/-- Full topological attachment conclusion. The only topology on the new carrier
is the explicitly constructed final topology, and each disk map and projection
is the prescribed set-theoretic function. The assertions apply also to empty J. -/
def finite_end_gluing_type : Prop :=
  ∀ {E : Type u} {J : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] [T2Space E] [SecondCountableTopology E]
    [Finite J] [T2Space B] (d : Data E J B),
    letI := d.topology
    (∀ U : Set (E ⊕ J), IsOpen U ↔
      IsOpen ((Sum.inl : E → E ⊕ J) ⁻¹' U) ∧
        ∀ j, IsOpen (d.psi j ⁻¹' U)) ∧
    IsOpenEmbedding (Sum.inl : E → E ⊕ J) ∧
    (∀ j, IsOpenEmbedding (d.psi j)) ∧
    (∀ j, range (d.psi j) = Sum.inl '' range (d.theta j) ∪ {Sum.inr j}) ∧
    DenseRange (Sum.inl : E → E ⊕ J) ∧
    ConnectedSpace (E ⊕ J) ∧ T2Space (E ⊕ J) ∧
    SecondCountableTopology (E ⊕ J) ∧
    Continuous d.extendedProjection ∧
    (∀ x, d.extendedProjection (Sum.inl x) = d.projection x) ∧
    (∀ j, d.extendedProjection (Sum.inr j) = d.diskProjection j (d.center j)) ∧
    (∀ j, d.extendedProjection ∘ d.psi j = d.diskProjection j) ∧
    (∀ j k, j ≠ k → d.diskProjection j (d.center j) =
      d.diskProjection k (d.center k) →
      Disjoint (range (d.psi j)) (range (d.psi k))) ∧
    (∀ j, ∃ e : OpenPartialHomeomorph (E ⊕ J) ℂ,
      e.source = range (d.psi j) ∧
      e.target = Metric.ball (0 : ℂ) (d.radius j) ∧
      e (Sum.inr j) = 0 ∧
      (∀ t, e (d.psi j t) = (t : ℂ)) ∧
      (∀ t : FullDisk (d.radius j), e.symm (t : ℂ) = d.psi j t)) ∧
    (∀ (j : J) (s : ℝ), 0 ≤ s → ∀ hs : s < d.radius j,
      Continuous (d.closedDiskMap j s hs) ∧
      range (d.closedDiskMap j s hs) =
        d.psi j '' ((Subtype.val : FullDisk (d.radius j) → ℂ) ⁻¹'
          Metric.closedBall (0 : ℂ) s) ∧
      IsCompact (d.psi j '' ((Subtype.val : FullDisk (d.radius j) → ℂ) ⁻¹'
        Metric.closedBall (0 : ℂ) s)) ∧
      IsCompact (range (d.closedDiskMap j s hs)))

end Specs.D12Complex.Ch21.FiniteEndGluing
