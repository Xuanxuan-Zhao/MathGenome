import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RightBanachParametrices
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.AtkinsonParametrices
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
namespace ExpandedFA.Fredholm
open scoped Topology
universe u v w
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- A closed-range map with complemented kernel has a bounded section on its range. -/
theorem range_section_of_complemented_kernel [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) (hc : IsClosed (T.range : Set F))
    (hk : T.ker.ClosedComplemented) :
    ∃ W : T.range →L[𝕜] E, ∀ y, T (W y) = y := by
  let : CompleteSpace T.range := hc.completeSpace_coe
  obtain ⟨N, hN⟩ := hk.exists_isTopCompl
  have hs : Topology.IsStrictMap T := by
    change Topology.IsStrictMap (Subtype.val ∘ T.rangeRestrict)
    rw [← Topology.IsEmbedding.subtypeVal.isStrictMap_iff]
    exact (T.rangeRestrict.isQuotientMap (fun y => by
      obtain ⟨x, hx⟩ := y.property
      exact ⟨x, Subtype.ext hx⟩)).isStrictMap
  let a := T.ker.quotientEquivOfIsTopCompl N hN
  let b : (E ⧸ T.ker) ≃L[𝕜] T.range := ContinuousLinearEquiv.quotKerEquivRange hs
  refine ⟨N.subtypeL.comp (a.toContinuousLinearMap.comp b.symm.toContinuousLinearMap), ?_⟩
  intro y
  change T (a (b.symm y)) = y
  have hq : T.ker.mkQ (a (b.symm y)) = b.symm y :=
    a.symm_apply_apply (b.symm y)
  have hb : (b (T.ker.mkQ (a (b.symm y))) : F) = T (a (b.symm y)) := rfl
  rw [hq, b.apply_symm_apply] at hb
  exact hb.symm

/-- Lift a finite-dimensional map into the range through an arbitrary operator.
The algebraic section need not be continuous on the whole range: only its
restriction to the finite-dimensional image is used. -/
theorem lift_finite_range_map (T : E →L[𝕜] F)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (f : G →L[𝕜] F) [FiniteDimensional 𝕜 f.range]
    (hf : f.range ≤ T.range) :
    ∃ L : G →L[𝕜] E, T.comp L = f := by
  obtain ⟨s, hs⟩ := T.toLinearMap.rangeRestrict.exists_rightInverse_of_surjective
    T.toLinearMap.range_rangeRestrict
  let j : f.range →ₗ[𝕜] T.range := Submodule.inclusion hf
  let l : f.range →L[𝕜] E := (s.comp j).toContinuousLinearMap
  refine ⟨l.comp f.rangeRestrict, ?_⟩
  ext x
  have h := LinearMap.congr_fun hs (j (f.rangeRestrict x))
  exact congrArg Subtype.val h

/-- A bounded right inverse up to a finite-rank defect supplies a bounded
right inverse on the entire actual range, and hence a complemented kernel. -/
theorem kernel_complemented_of_finite_right_defect
    (T : E →L[𝕜] F) (U : F →L[𝕜] E) (P : F →L[𝕜] F)
    [FiniteDimensional 𝕜 P.range]
    (hTU : T.comp U = ContinuousLinearMap.id 𝕜 F - P) :
    T.ker.ClosedComplemented := by
  let f := P.comp T.range.subtypeL
  have hfinite : FiniteDimensional 𝕜 f.range :=
    Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range _ _)
  let := hfinite
  have hf : f.range ≤ T.range := by
    rintro _ ⟨y, rfl⟩
    have hy : P y = (y : F) - T (U y) := by
      have h := congrArg (fun A : F →L[𝕜] F => A y) hTU
      change T (U y) = (y : F) - P y at h
      rw [h]
      abel
    change P y ∈ T.range
    rw [hy]
    exact T.range.sub_mem y.property ⟨U y, rfl⟩
  obtain ⟨L, hL⟩ := lift_finite_range_map T f hf
  let W : T.range →L[𝕜] E := U.comp T.range.subtypeL + L
  have hW : Function.RightInverse W T.rangeRestrict := by
    intro y
    apply Subtype.ext
    change T (U y + L y) = y
    rw [map_add]
    have h1 := congrArg (fun A : F →L[𝕜] F => A y) hTU
    have h2 := congrArg (fun A : T.range →L[𝕜] F => A y) hL
    change T (U y) = (y : F) - P y at h1
    change T (L y) = P y at h2
    rw [h1, h2, sub_add_cancel]
  have hker : T.rangeRestrict.ker = T.ker := by
    ext x
    change (⟨T x, T.mem_range_self x⟩ : T.range) = 0 ↔ T x = 0
    exact Subtype.ext_iff
  rw [← hker]
  exact T.rangeRestrict.closedComplemented_ker_of_rightInverse W hW

open RightBanachParametricesSpec in
/-- Finite-rank right defect forces closed finite-codimensional range as well
as the complement condition. Idempotence of the defect is unnecessary here. -/
theorem right_condition_of_finite_right_defect
    (T : E →L[𝕜] F) (U : F →L[𝕜] E) (P : F →L[𝕜] F)
    [FiniteDimensional 𝕜 P.range]
    (hTU : T.comp U = ContinuousLinearMap.id 𝕜 F - P) : RightCondition T := by
  have hD := identity_sub_compact_isFredholm P (compact_of_finiteDimensional_range P)
  have hle : (ContinuousLinearMap.id 𝕜 F - P).range ≤ T.range := by
    rw [← hTU]
    exact LinearMap.range_comp_le_range _ _
  let := hD.2.2
  have hfinite : FiniteDimensional 𝕜 (F ⧸ T.range) :=
    Submodule.CoFG.of_le hle inferInstance
  exact ⟨Submodule.isClosed_mono_of_finiteDimensional_quotient hD.1 hle,
    hfinite, kernel_complemented_of_finite_right_defect T U P hTU⟩

open RightBanachParametricesSpec in
/-- Invert on a complement of the kernel, then project onto the range.
The complementary range projection has exactly the cokernel dimension. -/
theorem exact_right_projection_of_condition [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : RightCondition T) : ExactProjectionRightInverse T := by
  let := hT.2.1
  obtain ⟨W, hW⟩ := range_section_of_complemented_kernel T hT.1 hT.2.2
  obtain ⟨B, hB⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient hT.1).exists_isTopCompl
  let e := T.range.quotientEquivOfIsTopCompl B hB
  let : FiniteDimensional 𝕜 B := e.finiteDimensional
  let P := B.projectionL T.range hB.symm
  let U := W.comp (T.range.projectionOntoL B hB)
  have hPrange : P.range = B := by simp [P]
  have hP : P.comp P = P := by
    ext y
    simp [P]
  have hTU : T.comp U = ContinuousLinearMap.id 𝕜 F - P := by
    ext y
    change T (W (T.range.projectionOntoL B hB y)) = y - P y
    rw [hW]
    exact eq_sub_iff_add_eq.mpr
      (Submodule.projection_add_projection_eq_self hB.isCompl y)
  refine ⟨U, P, hP, ?_, hTU, ?_⟩
  · rw [hPrange]
    infer_instance
  · rw [hPrange]
    exact e.toLinearEquiv.finrank_eq.symm

open RightBanachParametricesSpec in
/-- Riesz--Schauder regularizes the Fredholm product I+K; composing its
right regularizer with the original S gives the desired projection defect. -/
theorem projection_right_inverse_of_compact [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : CompactRightInverse T) : ProjectionRightInverse T := by
  obtain ⟨S, K, hK, hTS⟩ := hT
  have hneg : Compactness.IsCompactLinearMap (-K).toLinearMap := by
    simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_neg] using Compactness.compact_smul (-1 : 𝕜) K.toLinearMap hK
  have hD : IsFredholm (ContinuousLinearMap.id 𝕜 F + K) := by
    simpa only [sub_neg_eq_add] using identity_sub_compact_isFredholm (-K) hneg
  let := hD.2.1
  have hc : RightCondition (ContinuousLinearMap.id 𝕜 F + K) :=
    ⟨hD.1, hD.2.2, Submodule.ClosedComplemented.of_finiteDimensional _⟩
  obtain ⟨R, P, hP, hfinite, hR, _⟩ := exact_right_projection_of_condition _ hc
  refine ⟨S.comp R, P, hP, hfinite, ?_⟩
  rw [← ContinuousLinearMap.comp_assoc, hTS, hR]

open RightBanachParametricesSpec in
/-- A finite-rank projection is compact in its original codomain. -/
theorem compact_right_inverse_of_projection
    (T : E →L[𝕜] F) (hT : ProjectionRightInverse T) : CompactRightInverse T := by
  obtain ⟨U, P, _, hfinite, hTU⟩ := hT
  let := hfinite
  have hc : Compactness.IsCompactLinearMap (-P).toLinearMap := by
    simpa only [neg_one_smul, ContinuousLinearMap.toLinearMap_neg] using
      Compactness.compact_smul (-1 : 𝕜) P.toLinearMap (compact_of_finiteDimensional_range P)
  exact ⟨U, -P, hc, by simpa only [sub_eq_add_neg] using hTU⟩

/-- All three right-sided conditions, including the complement condition
in the reverse implication, for arbitrary real or complex Banach spaces. -/
theorem right_banach_parametrices : RightBanachParametricesSpec.RightEquivalences := by
  intro 𝕜 _ E F _ _ _ _ _ _ T
  have hforward (hT : RightBanachParametricesSpec.RightCondition T) :
      RightBanachParametricesSpec.ProjectionRightInverse T := by
    obtain ⟨U, P, hP, hfinite, hTU, _⟩ := exact_right_projection_of_condition T hT
    exact ⟨U, P, hP, hfinite, hTU⟩
  have hback (hT : RightBanachParametricesSpec.ProjectionRightInverse T) :
      RightBanachParametricesSpec.RightCondition T := by
    obtain ⟨U, P, _, hfinite, hTU⟩ := hT
    let := hfinite
    exact right_condition_of_finite_right_defect T U P hTU
  exact ⟨⟨fun h => compact_right_inverse_of_projection T (hforward h),
    fun h => hback (projection_right_inverse_of_compact T h)⟩, ⟨hforward, hback⟩⟩

/-- The projection can always be chosen to have rank equal to the actual
cokernel dimension, including when that dimension is zero. -/
theorem right_banach_parametrices_exact_defect : RightBanachParametricesSpec.ExactDefect := by
  intro 𝕜 _ E F _ _ _ _ _ _ T hT
  exact exact_right_projection_of_condition T hT

end ExpandedFA.Fredholm
