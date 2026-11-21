import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.GantmacherAdjointIdeal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.GantmacherCriterion
import Mathlib.Analysis.Normed.Group.Quotient

set_option maxSynthPendingDepth 4

namespace ExpandedFA.Compactness.GantmacherAdjointIdeal
universe u v w z
open Set Topology
noncomputable section
variable {𝕜 : Type u} [RCLike 𝕜]
  {X : Type v} {Y : Type w} {Z : Type z}
  [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [NormedSpace 𝕜 Z]

private abbrev tr (T : X →L[𝕜] Y) :=
  P1.C04Annihilators.Spec.BanachTransposeValue 𝕜 X Y T
private abbrev J (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :=
  NormedSpace.inclusionInDoubleDual 𝕜 E

/-- The transpose, bundled also in its operator argument. -/
private def transposeOperator : (X →L[𝕜] Y) →L[𝕜] (Y →L[𝕜] 𝕜) →L[𝕜] (X →L[𝕜] 𝕜) :=
  (ContinuousLinearMap.compL 𝕜 X Y 𝕜).flip

private lemma canonical_range_closed [CompleteSpace Y] : IsClosed (range (J (𝕜 := 𝕜) Y)) := by
  have hJ : Isometry (J (𝕜 := 𝕜) Y) :=
    (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := Y)).isometry
  exact ((completeSpace_iff_isComplete_range hJ.isUniformInducing).mp inferInstance).isClosed

/-- A closed subspace is the common kernel of the continuous dual forms that
vanish on it. The quotient is a genuine normed space because the subspace is closed. -/
private lemma mem_of_annihilators {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)) (x : E)
    (hx : ∀ f : E →L[𝕜] 𝕜, (∀ y ∈ M, f y = 0) → f x = 0) : x ∈ M := by
  let : IsClosed (M : Set E) := hM
  apply (Submodule.Quotient.mk_eq_zero M).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜)
  intro f
  exact hx (f.comp M.mkQL) (by intro y hy; simp [(Submodule.Quotient.mk_eq_zero M).mpr hy])

theorem gantmacher_equivalences : Spec.GantmacherEquivalences.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T
  exact ⟨GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 X Y T,
    (GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 X Y T).trans
      (GantmacherCriterion.bidualRange_iff_adjoint_continuous 𝕜 X Y T)⟩

/-- The forward implication is the canonical triple-dual calculation. -/
private lemma adjoint_forward [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator T) : IsWeaklyCompactOperator (tr T) := by
  apply (GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 _ _ (tr T)).mpr
  intro η
  refine ⟨tr T (η.comp (J Y)), ?_⟩
  ext ξ
  obtain ⟨y, hy⟩ := (GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 X Y T).mp hT ξ
  change η (tr (tr T) ξ) = (tr (tr T) ξ) (η.comp (J Y))
  rw [hy]
  rfl

/-- The reverse implication uses separation of the closed canonical range in Y″. -/
theorem adjoint_equivalence : Spec.AdjointEquivalence.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T
  constructor
  · exact adjoint_forward T
  · intro hT'
    apply (GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 X Y T).mpr
    intro ξ
    let M : Submodule 𝕜 ((Y →L[𝕜] 𝕜) →L[𝕜] 𝕜) := (J Y).toLinearMap.range
    have hm : tr (tr T) ξ ∈ M := by
      apply mem_of_annihilators M (canonical_range_closed (𝕜 := 𝕜) (Y := Y)) (tr (tr T) ξ)
      intro η hη
      obtain ⟨f, hf⟩ :=
        (GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 _ _ (tr T)).mp hT' η
      have hf0 : f = 0 := by
        ext x
        have hh := congrArg (fun g => g ((J X) x)) hf
        change η ((J Y) (T x)) = f x at hh
        exact hh.symm.trans (hη _ ⟨T x, rfl⟩)
      have hh := congrArg (fun g => g ξ) hf
      change η (tr (tr T) ξ) = ξ f at hh
      simpa [hf0] using hh
    obtain ⟨y, hy⟩ := hm
    exact ⟨y, hy.symm⟩

theorem linear_space : Spec.LinearSpace.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _
  have crit := GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 X Y
  refine ⟨?_, ?_, ?_⟩
  · apply (crit 0).mpr
    intro ξ
    refine ⟨0, ?_⟩
    ext f
    change ξ (f.comp 0) = f 0
    simp
  · intro S T hS hT
    apply (crit (S + T)).mpr
    intro ξ
    obtain ⟨y, hy⟩ := (crit S).mp hS ξ
    obtain ⟨z, hz⟩ := (crit T).mp hT ξ
    refine ⟨y + z, ?_⟩
    ext f
    have ht : tr (S + T) f = tr S f + tr T f := by
      ext x
      exact f.map_add _ _
    change ξ (tr (S + T) f) = f (y + z)
    rw [ht, map_add, map_add]
    exact congrArg₂ (· + ·) (congrArg (fun g => g f) hy) (congrArg (fun g => g f) hz)
  · intro a T hT
    apply (crit (a • T)).mpr
    intro ξ
    obtain ⟨y, hy⟩ := (crit T).mp hT ξ
    refine ⟨a • y, ?_⟩
    ext f
    have ht : tr (a • T) f = a • tr T f := by
      ext x
      exact f.map_smul a (T x)
    change ξ (tr (a • T) f) = f (a • y)
    rw [ht, map_smul, map_smul]
    exact congrArg (a • ·) (congrArg (fun g => g f) hy)

theorem norm_closed : Spec.NormClosed.{u,v,w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _
  let D : (X →L[𝕜] Y) →L[𝕜] (((X →L[𝕜] 𝕜) →L[𝕜] 𝕜) →L[𝕜]
      ((Y →L[𝕜] 𝕜) →L[𝕜] 𝕜)) :=
    (transposeOperator (X := Y →L[𝕜] 𝕜) (Y := X →L[𝕜] 𝕜)).comp transposeOperator
  have heq : {T : X →L[𝕜] Y | Spec.WC T} =
      ⋂ ξ, (fun T => D T ξ) ⁻¹' range (J (𝕜 := 𝕜) Y) := by
    ext T
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_range]
    exact (GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 X Y T).trans
      (by constructor <;> intro h ξ <;> obtain ⟨y, hy⟩ := h ξ <;> exact ⟨y, hy.symm⟩)
  rw [heq]
  apply isClosed_iInter
  intro ξ
  exact (canonical_range_closed (𝕜 := 𝕜)).preimage
    (((ContinuousLinearMap.apply 𝕜 _ ξ).comp D).continuous)

theorem two_sided_ideal : Spec.TwoSidedIdeal.{u,v,w,z} := by
  intro 𝕜 X Y Z _ _ _ _ _ _ _ _ _ _ T hT
  have hr := (GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 X Y T).mp hT
  constructor
  · intro A
    apply (GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 X Z (A.comp T)).mpr
    intro ξ
    obtain ⟨y, hy⟩ := hr ξ
    refine ⟨A y, ?_⟩
    ext f
    exact congrArg (fun g => g (tr A f)) hy
  · intro B
    apply (GantmacherCriterion.weaklyCompact_iff_bidualRange 𝕜 Z Y (T.comp B)).mpr
    intro ξ
    obtain ⟨y, hy⟩ := hr (tr (tr B) ξ)
    refine ⟨y, ?_⟩
    ext f
    exact congrArg (fun g => g f) hy

end
end ExpandedFA.Compactness.GantmacherAdjointIdeal
