import MathGenome.Internal.LinearPDE.P201Specs.Common.WeakLimit
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14WeakSubsequence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences

namespace P201.WeakLimit
open Filter
open scoped Topology
universe u

/-- Late Galerkin equations hold on each fixed test space; closed level sets
pass them to a weak cluster point. Norm density then gives all tests. -/
theorem clusterPoint_solves : Expected.ClusterPointSolves.{u} := by
  intro V _ _ Vm hmono hdense a ell s heq x hx
  have htests : ∀ v ∈ (⋃ m, (Vm m : Set V)), a x v = ell v := by
    intro v hv
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hv
    have hc := ExpandedFA.P1.C12BoundedSequences.weak_evaluation_continuous
      ℝ V (a.flip v)
    let : TopologicalSpace V := weakTopology V
    have hclosed : IsClosed {z : V | a z v = ell v} :=
      isClosed_eq hc continuous_const
    apply hclosed.mem_of_mapClusterPt hx
    exact (eventually_ge_atTop j).mono fun m hm => heq m v (hmono hm hj)
  have hclosed : IsClosed {v : V | a x v = ell v} :=
    isClosed_eq (a x).continuous ell.continuous
  intro v
  exact hclosed.closure_subset_iff.mpr htests (hdense v)

/-- Reflexive sequential compactness supplies an extraction. Its limit is a
cluster point of the original tails, to which the preceding theorem applies. -/
theorem weakLimit_existence : Expected.WeakLimitExistence.{u} := by
  intro V _ _ _ href Vm hmono _hfin hdense a ell s hbound heq
  obtain ⟨k, hk, x, hx⟩ :=
    ExpandedFA.P1.C14WeakSubsequence.reflexive_weak_subsequence ℝ V href s hbound
  refine ⟨k, hk, x, hx, ?_⟩
  apply clusterPoint_solves V Vm hmono hdense a ell s heq x
  let : TopologicalSpace V := weakTopology V
  exact hx.mapClusterPt.of_comp hk.tendsto_atTop

/-- Testing the difference of two solutions against itself forces equality. -/
theorem solution_unique {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : V →L[ℝ] V →L[ℝ] ℝ) (ell : V →L[ℝ] ℝ)
    (alpha : ℝ) (halpha : 0 < alpha) (hcoerc : ∀ v : V, alpha * ‖v‖ ^ 2 ≤ a v v)
    {x y : V} (hx : Solves V a ell x) (hy : Solves V a ell y) : y = x := by
  have hz : a (y - x) (y - x) = 0 := by
    rw [map_sub a]
    change a y (y - x) - a x (y - x) = 0
    rw [hy, hx, sub_self]
  have hb := hcoerc (y - x)
  rw [hz] at hb
  have hn : ‖y - x‖ = 0 :=
    (sq_eq_zero_iff.mp (le_antisymm (nonpos_of_mul_nonpos_right hb halpha)
      (sq_nonneg _)))
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Coercivity is used only for uniqueness, after weak-limit existence. -/
theorem coercive_weakLimit : Expected.CoerciveWeakLimit.{u} := by
  intro V _ _ _ href Vm hmono hfin hdense a ell s hbound heq alpha halpha hcoerc
  obtain ⟨k, hk, x, hx, hsol⟩ :=
    weakLimit_existence V href Vm hmono hfin hdense a ell s hbound heq
  refine ⟨k, hk, x, hx, hsol, ?_, ?_⟩
  · intro y hy
    exact solution_unique a ell alpha halpha hcoerc hsol hy
  · intro y
    constructor
    · intro hy
      exact solution_unique a ell alpha halpha hcoerc hsol
        (clusterPoint_solves V Vm hmono hdense a ell s heq y hy)
    · rintro rfl
      let : TopologicalSpace V := weakTopology V
      exact hx.mapClusterPt.of_comp hk.tendsto_atTop

end P201.WeakLimit
