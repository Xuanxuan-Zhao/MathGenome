import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.RieszRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection

/-!
Adjoints and reducing subspaces (`paper.tex` 7499–7512).

The native adjoint is constructed using inverse Riesz representation on the
scalar-linear dual. It is a bounded scalar-linear K → H map and satisfies the
paper's conjugate-first identity. Mathlib's rectangular adjoint norm theorem
requires exactly Hilbert completeness of H and K; its range theorems use norm
closure, without a closed-range hypothesis.

For invariance, PTP = TP means that TPx is fixed by P. For reduction, write
x = Px + (x-Px), with the two summands in M and Mᗮ. Invariance of both summands
is precisely commutation with P. The adjoint pairing identifies invariance of
M under T* with invariance of Mᗮ under T; closedness supplies Mᗮᗮ = M.

The Banach transpose acts on continuous linear functionals by precomposition.
It is distinguished from the Hilbert adjoint by the explicit Riesz bridge.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.Adjoint
universe u v w z

/-- Canonical Hilbert adjoint of every bounded operator between Hilbert spaces. -/
def hilbertAdjoint : Spec.AdjointType.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ _ T => ContinuousLinearMap.adjoint T

/-- Invariance under a bounded operator, with no closedness built into the predicate. -/
def IsInvariantSubspace : Spec.InvariantSubspaceType.{u, v} :=
  Spec.InvariantSubspaceValue

/-- Reduction means invariance of both orthogonal summands. -/
def IsReducingSubspace : Spec.ReducingSubspaceType.{u, v} :=
  Spec.ReducingSubspaceValue

theorem adjoint_inner : Spec.DefiningIdentity.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T x y
  exact (ContinuousLinearMap.adjoint_inner_right T x y).symm

theorem adjoint_exists_unique : Spec.ExistenceUniqueness.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T
  refine ⟨hilbertAdjoint 𝕜 H K T, adjoint_inner 𝕜 H K T, ?_⟩
  intro S hS
  ext y
  apply ext_inner_left 𝕜
  intro x
  exact (hS x y).symm.trans (adjoint_inner 𝕜 H K T x y)

theorem adjoint_norm : Spec.NormEquality.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T
  exact (ContinuousLinearMap.adjoint.norm_map T).symm

theorem adjoint_cstar_norm : Spec.CstarNorm.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T
  simpa only [Spec.AdjointValue, pow_two] using
    ContinuousLinearMap.norm_adjoint_comp_self T

theorem adjoint_involution : Spec.Involution.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T
  exact ContinuousLinearMap.adjoint_adjoint T

theorem adjoint_comp : Spec.Composition.{u, v, w, z} := by
  intro 𝕜 H K L _ _ _ _ _ _ _ _ _ _ S T
  exact ContinuousLinearMap.adjoint_comp S T

theorem range_closure_eq_orthogonal_adjoint_ker : Spec.RangeClosure.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T
  simpa only [Spec.AdjointValue, ContinuousLinearMap.adjoint_adjoint] using
    (ContinuousLinearMap.orthogonal_ker (ContinuousLinearMap.adjoint T)).symm

theorem adjoint_range_closure_eq_orthogonal_ker : Spec.AdjointRangeClosure.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T
  exact (ContinuousLinearMap.orthogonal_ker T).symm

theorem invariant_iff_projection_identity : Spec.InvarianceCriterion.{u, v} := by
  intro 𝕜 H _ _ _ _ M hM T
  let : CompleteSpace M := hM.completeSpace_coe
  change (∀ x ∈ M, T x ∈ M) ↔
    M.starProjection.comp (T.comp M.starProjection) = T.comp M.starProjection
  constructor
  · intro h
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr (h _ (M.starProjection_apply_mem x))
  · intro h x hx
    apply Submodule.starProjection_eq_self_iff.mp
    have hp := congrArg (fun A : H →L[𝕜] H => A x) h
    simpa only [ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.mpr hx] using hp

theorem reducing_iff_commutes_projection : Spec.ReductionCommutation.{u, v} := by
  intro 𝕜 H _ _ _ _ M hM T
  let : CompleteSpace M := hM.completeSpace_coe
  change ((∀ x ∈ M, T x ∈ M) ∧ (∀ x ∈ M.orthogonal, T x ∈ M.orthogonal)) ↔
    M.starProjection.comp T = T.comp M.starProjection
  rw [eq_comm]
  constructor
  · rintro ⟨hM_inv, hperp_inv⟩
    ext x
    apply Eq.symm
    apply Submodule.eq_starProjection_of_mem_orthogonal'
      (hM_inv _ (M.starProjection_apply_mem x))
      (hperp_inv _ (Submodule.sub_starProjection_mem_orthogonal x))
    rw [map_sub, add_sub_cancel]
    rfl
  · intro h
    have hp (x : H) : T (M.starProjection x) = M.starProjection (T x) :=
      congrArg (fun A : H →L[𝕜] H => A x) h
    constructor
    · intro x hx
      apply Submodule.starProjection_eq_self_iff.mp
      rw [← hp, Submodule.starProjection_eq_self_iff.mpr hx]
    · intro x hx
      have hzero : M.starProjection x = 0 := by
        have hk := Submodule.ker_starProjection M
        have : x ∈ M.starProjection.ker := by rw [hk]; exact hx
        exact this
      have hzeroT : M.starProjection (T x) = 0 := by rw [← hp, hzero, map_zero]
      rw [← Submodule.ker_starProjection M]
      exact hzeroT

theorem reducing_iff_invariant_adjoint : Spec.ReductionAdjoint.{u, v} := by
  intro 𝕜 H _ _ _ _ M hM T
  let : CompleteSpace M := hM.completeSpace_coe
  change ((∀ x ∈ M, T x ∈ M) ∧ (∀ x ∈ M.orthogonal, T x ∈ M.orthogonal)) ↔
    (∀ x ∈ M, T x ∈ M) ∧ (∀ x ∈ M, T.adjoint x ∈ M)
  apply and_congr_right
  intro _
  simpa only [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem,
    ContinuousLinearMap.coe_coe] using
    (ContinuousLinearMap.mem_invtSubmodule_adjoint_iff (T := T) (U := M)).symm

theorem reduction_equivalences : Spec.ReductionEquivalences.{u, v} := by
  intro 𝕜 H _ _ _ _ M hM T
  exact ⟨reducing_iff_commutes_projection 𝕜 H M hM T,
    (reducing_iff_commutes_projection 𝕜 H M hM T).symm.trans
      (reducing_iff_invariant_adjoint 𝕜 H M hM T)⟩

/-- Riesz intertwines precomposition on the linear dual with the Hilbert adjoint. -/
theorem adjoint_transpose_riesz : Spec.TransposeRieszBridge.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T y
  ext x
  exact (ContinuousLinearMap.adjoint_inner_left T x y).symm

end ExpandedFA.Hilbert.Adjoint
