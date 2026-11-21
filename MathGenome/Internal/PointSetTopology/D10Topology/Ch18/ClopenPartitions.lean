import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.ClopenPartitions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.QuasiComponents
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith

open Set TopologicalSpace
universe u

namespace D10Topology.Ch18

abbrev ClopenPartitionOf {X : Type u} [TopologicalSpace X] (A : Set X)
    {n : ℕ} (P : Fin n → Set X) : Prop :=
  ClopenPartitionsData.ClopenPartitionOf A P

abbrev Refines {X : Type u} {n m : ℕ} (P : Fin n → Set X) (Q : Fin m → Set X) : Prop :=
  ClopenPartitionsData.Refines P Q

variable {X : Type u} [d : MetricSpace X] [hcompact : CompactSpace X]

/-- Refine a finite clopen cover, allowing empty cover members. This also
handles the empty space without assuming a nonempty whole-space part. -/
private theorem small_mesh_subordinate (hz : Ch06.ZeroDimensional X)
    (ε : ℝ) (hε : 0 < ε) (m : ℕ) (Q : Fin m → Set X)
    (hQ : ∀ j, IsClopen (Q j)) (hcover : (⋃ j, Q j) = univ) :
    ∃ (n : ℕ) (P : Fin n → Set X), ClopenPartitionOf univ P ∧ Refines P Q ∧
      ∀ i, Ch09.diameter d.toPseudoMetricSpace (P i) < ENNReal.ofReal ε := by
  let : ZeroDimensionalSpace X := (Ch06.zeroDimensional_iff_mathlib X).mp hz
  let U : X × Fin m → Opens X := fun p =>
    ⟨Metric.ball p.1 (ε / 3) ∩ Q p.2, Metric.isOpen_ball.inter (hQ p.2).isOpen⟩
  have hU : IsOpenCover U := by
    apply IsOpenCover.of_sets
    apply subset_antisymm (subset_univ _)
    intro x _
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨(x, j), Metric.mem_ball_self (by linarith), hj⟩
  obtain ⟨n, W, hW, hcoverW, hdisj⟩ := hU.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, fun i => (W i : Set X), ⟨fun i => (W i).isClopen, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    exact Set.nonempty_iff_ne_empty.mpr (fun h => (hW i).1 (SetLike.coe_injective h))
  · intro i j hij
    exact Clopens.coe_disjoint.mpr (hdisj hij)
  · exact subset_antisymm (subset_univ _) hcoverW
  · intro i
    obtain ⟨p, hp⟩ := (hW i).2
    exact ⟨p.2, hp.trans inter_subset_right⟩
  · intro i
    obtain ⟨p, hp⟩ := (hW i).2
    rw [Ch09.diameter_eq_mathlib]
    apply lt_of_le_of_lt (Metric.ediam_le_of_forall_dist_le (C := 2 * (ε / 3)) ?_)
      ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))
    intro x hx y hy
    have hx' : dist x p.1 < ε / 3 := (hp hx).1
    have hy' : dist p.1 y < ε / 3 := by simpa [dist_comm] using (hp hy).1
    exact (dist_triangle x p.1 y).trans (by linarith)

theorem small_mesh_partition (hz : Ch06.ZeroDimensional X) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (P : Fin n → Set X), ClopenPartitionOf univ P ∧
      ∀ i, Ch09.diameter d.toPseudoMetricSpace (P i) < ENNReal.ofReal ε := by
  obtain ⟨n, P, hP, _, hmesh⟩ := small_mesh_subordinate hz ε hε 1
    (fun _ : Fin 1 => (univ : Set X)) (fun _ => isClopen_univ)
    (by ext x; simp)
  exact ⟨n, P, hP, hmesh⟩

theorem small_mesh_refinement (hz : Ch06.ZeroDimensional X) (ε : ℝ) (hε : 0 < ε)
    (m : ℕ) (Q : Fin m → Set X) (hQ : ClopenPartitionOf univ Q) :
    ∃ (n : ℕ) (P : Fin n → Set X), ClopenPartitionOf univ P ∧ Refines P Q ∧
      ∀ i, Ch09.diameter d.toPseudoMetricSpace (P i) < ENNReal.ofReal ε :=
  small_mesh_subordinate hz ε hε m Q hQ.1 hQ.2.2.2

omit hcompact in
/-- A finite nonempty open subset of a T₁ space contains an isolated point. -/
private theorem infinite_of_open_no_isolated (hno : ∀ x : X, ¬ IsOpen ({x} : Set X))
    (H : Set X) (hH : IsOpen H) (hne : H.Nonempty) : H.Infinite := by
  intro hfin
  obtain ⟨x, hx⟩ := hne
  apply hno x
  have heq : H \ (H \ {x}) = {x} := by ext y; simp only [mem_sdiff, mem_singleton_iff]; grind
  rw [← heq]
  exact hH.sdiff (hfin.subset sdiff_subset).isClosed

include hcompact in
/-- Infinitely many singleton connected components supply a prescribed
positive number of nonempty clopen pieces in the clopen subtype. -/
theorem split_clopen_part (hz : Ch06.ZeroDimensional X)
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X))
    (H : Set X) (hH : IsClopen H) (hne : H.Nonempty) (k : ℕ) (hk : 0 < k) :
    ∃ P : Fin k → Set X, ClopenPartitionOf H P := by
  let : TotallyDisconnectedSpace X :=
    (Ch06.totallyDisconnected_iff_mathlib X).mp
      (Ch06.zeroDimensional_t1_totallyDisconnected X hz)
  let : Infinite H := Set.infinite_coe_iff.mpr
    (infinite_of_open_no_isolated hno H hH.isOpen hne)
  have hinj : Function.Injective (ConnectedComponents.mk : H → ConnectedComponents H) := by
    intro x y hxy
    have := ConnectedComponents.coe_eq_coe'.mp hxy
    simpa only [connectedComponent_eq_singleton, mem_singleton_iff] using this
  let : Infinite (ConnectedComponents H) := Infinite.of_injective _ hinj
  obtain ⟨V, hV, hVne, hVdisj, hVcover⟩ :=
    ConnectedComponents.exists_fun_isClopen_of_infinite H k hk
  refine ⟨fun i => Subtype.val '' V i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hH.isClosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp (hV i).isClosed,
      hH.isOpen.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mp (hV i).isOpen⟩
  · intro i
    exact (hVne i).image _
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba : b = a := Subtype.val_injective hab
    subst b
    exact Set.disjoint_left.mp (hVdisj hij) ha hb
  · rw [← image_iUnion, hVcover, image_univ, Subtype.range_val]

end D10Topology.Ch18
