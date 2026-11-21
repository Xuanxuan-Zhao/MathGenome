import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.ReflexiveMinimax
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.CompactConvexMinimax
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14BallCharacterization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12NormLsc

namespace ExpandedFA.Geometry
open Set
open Specs.ExpandedFA.Geometry.CompactConvexMinimax
open Specs.ExpandedFA.Geometry.ReflexiveMinimax
universe u v
noncomputable section

/-- On a norm-closed convex domain, convex norm-lsc functions are weakly lsc.
The function is not assumed to have any regularity outside the domain. -/
lemma convex_norm_lsc_weak_lsc_on {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f : E → ℝ} (hK : IsClosed K)
    (cv : ConvexOn ℝ K f) (hf : LowerSemicontinuousOn f K) :
    @LowerSemicontinuousOn E ℝ
      (P1.C12DualPairSpec.DualPairTopologyValue ℝ E (E →L[ℝ] ℝ) (topDualPairing ℝ E))
      inferInstance f K := by
  apply (@lowerSemicontinuousOn_iff_preimage_Iic E
    (P1.C12DualPairSpec.DualPairTopologyValue ℝ E (E →L[ℝ] ℝ) (topDualPairing ℝ E))
    K ℝ _ f).mpr
  intro r
  obtain ⟨V, hV, heq⟩ := lowerSemicontinuousOn_iff_preimage_Iic.mp hf r
  have hc : IsClosed (K ∩ f ⁻¹' Iic r) := by rw [heq]; exact hK.inter hV
  have hw := P1.C12ConvexClosure.isWeaklyClosed_of_isClosed_convex ℝ E
    (K ∩ f ⁻¹' Iic r) (cv.convex_le r) hc
  exact ⟨K ∩ f ⁻¹' Iic r, hw, by ext x; simp⟩

/-- The upper semicontinuous, concave counterpart. -/
lemma concave_norm_usc_weak_usc_on {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f : E → ℝ} (hK : IsClosed K)
    (cv : ConcaveOn ℝ K f) (hf : UpperSemicontinuousOn f K) :
    @UpperSemicontinuousOn E ℝ
      (P1.C12DualPairSpec.DualPairTopologyValue ℝ E (E →L[ℝ] ℝ) (topDualPairing ℝ E))
      inferInstance f K := by
  apply (@upperSemicontinuousOn_iff_preimage_Ici E
    (P1.C12DualPairSpec.DualPairTopologyValue ℝ E (E →L[ℝ] ℝ) (topDualPairing ℝ E))
    ℝ f K _).mpr
  intro r
  obtain ⟨V, hV, heq⟩ := upperSemicontinuousOn_iff_preimage_Ici.mp hf r
  have hc : IsClosed (K ∩ f ⁻¹' Ici r) := by rw [heq]; exact hK.inter hV
  have hw := P1.C12ConvexClosure.isWeaklyClosed_of_isClosed_convex ℝ E
    (K ∩ f ⁻¹' Ici r) (cv.convex_ge r) hc
  exact ⟨K ∩ f ⁻¹' Ici r, hw, by ext x; simp⟩

/-- Reflexivity supplies weak compactness of closed bounded convex domains. -/
lemma closed_bounded_convex_weakCompact {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hE : P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ E)
    (hK : IsClosed K) (bK : Bornology.IsBounded K) (cK : Convex ℝ K) :
    @IsCompact E
      (P1.C12DualPairSpec.DualPairTopologyValue ℝ E (E →L[ℝ] ℝ) (topDualPairing ℝ E)) K :=
  (P1.C14BallCharacterization.weakCompact_unitBall_iff_closed_bounded ℝ E).mp
    ((P1.C14BallCharacterization.reflexive_iff_weakCompact_unitBall ℝ E).mp hE)
    K bK (P1.C12ConvexClosure.isWeaklyClosed_of_isClosed_convex ℝ E K cK hK)

/-- All extrema and all outer-optimizer saddle pairs in reflexive Banach spaces. -/
theorem reflexive_minimax : reflexiveMinimaxType.{u,v} := by
  intro E G _ _ _ _ _ _ K L F hE hG nK hK bK cK nL hL bL cL cv lsc cc usc
  have kK := closed_bounded_convex_weakCompact hE hK bK cK
  have kL := closed_bounded_convex_weakCompact hG hL bL cL
  have wlsc := fun y hy => convex_norm_lsc_weak_lsc_on hK (cv y hy) (lsc y hy)
  have wusc := fun x hx => concave_norm_usc_weak_usc_on hL (cc x hx) (usc x hx)
  have htE : P1.C12DualPairSpec.DualPairTopologyValue ℝ E (E →L[ℝ] ℝ)
      (topDualPairing ℝ E) = instTopologicalSpaceWeakSpace ℝ E := by
    exact @induced_id (WeakSpace ℝ E) _
  have htG : P1.C12DualPairSpec.DualPairTopologyValue ℝ G (G →L[ℝ] ℝ)
      (topDualPairing ℝ G) = instTopologicalSpaceWeakSpace ℝ G := by
    exact @induced_id (WeakSpace ℝ G) _
  rw [htE] at kK wlsc
  rw [htG] at kL wusc
  exact @compact_convex_minimax (WeakSpace ℝ E) (WeakSpace ℝ G)
    _ _ _ _ _ _ _ _ _ _ _ _ K L F nK kK cK nL kL cL cv wlsc cc wusc

/-- The same result for a payoff whose exact domain is K × L. -/
theorem restricted_reflexive_minimax : restrictedReflexiveMinimaxType.{u,v} := by
  intro E G _ _ _ _ _ _ K L F hE hG nK hK bK cK nL hL bL cL cv lsc cc usc
  apply reflexive_minimax K L (extendPayoff F) hE hG nK hK bK cK nL hL bL cL
  · intro y hy
    exact cv ⟨y, hy⟩
  · intro y hy
    rw [← lowerSemicontinuous_restrict_iff]
    convert lsc ⟨y, hy⟩ using 1
    ext x
    simp [extendPayoff, x.property, hy]
  · intro x hx
    exact cc ⟨x, hx⟩
  · intro x hx
    rw [← upperSemicontinuousOn_iff_restrict]
    convert usc ⟨x, hx⟩ using 1
    ext y
    simp [extendPayoff, hx, y.property]

/-- Continuous bilinear von Neumann minimax on compact convex sets. -/
theorem compact_bilinear_minimax : compactBilinearMinimaxType.{u,v} := by
  intro E G _ _ _ _ _ _ _ _ _ _ _ _ K L B nK kK cK nL kL cL hB
  apply compact_convex_minimax K L (fun x y => B x y) nK kK cK nL kL cL
  · intro y _
    exact (B.flip y).convexOn cK
  · intro y _
    exact (hB.comp (continuous_id.prodMk continuous_const)).continuousOn.lowerSemicontinuousOn
  · intro x _
    exact (B x).concaveOn cL
  · intro x _
    exact (hB.comp (continuous_const.prodMk continuous_id)).continuousOn.upperSemicontinuousOn

/-- Continuous bilinear von Neumann minimax in real reflexive Banach spaces. -/
theorem reflexive_bilinear_minimax : reflexiveBilinearMinimaxType.{u,v} := by
  intro E G _ _ _ _ _ _ K L B hE hG nK hK bK cK nL hL bL cL
  apply reflexive_minimax K L (fun x y => B x y) hE hG nK hK bK cK nL hL bL cL
  · intro y _
    exact (B.flip y).toLinearMap.convexOn cK
  · intro y _
    exact (B.flip y).continuous.continuousOn.lowerSemicontinuousOn
  · intro x _
    exact (B x).toLinearMap.concaveOn cL
  · intro x _
    exact (B x).continuous.continuousOn.upperSemicontinuousOn

end
end ExpandedFA.Geometry
