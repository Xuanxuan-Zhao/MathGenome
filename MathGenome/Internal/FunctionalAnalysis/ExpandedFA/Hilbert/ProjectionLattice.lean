import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.ProjectionLattice
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.ProjectionLattice
universe u v

abbrev OrthogonalProjection : Spec.OrthogonalProjectionType.{u, v} :=
  Spec.OrthogonalProjectionValue

theorem projection_identification : Spec.ProjectionIdentification.{u, v} := by
  intro 𝕜 H _ _ _ _ P
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.property.isSelfAdjoint, p.property.isIdempotentElem.eq⟩
  · rintro ⟨hs, hi⟩
    exact ⟨⟨P, ⟨hi, hs⟩⟩, rfl⟩

theorem range_correspondence : Spec.RangeCorrespondence.{u, v} := by
  intro 𝕜 H _ _ _ _
  constructor
  · intro P
    apply Subtype.ext
    obtain ⟨h, heq⟩ := isStarProjection_iff_eq_starProjection_range.mp P.property
    exact heq.symm
  · intro M
    apply ClosedSubmodule.toSubmodule_injective
    exact Submodule.range_starProjection M.toSubmodule

theorem order_iff_range : Spec.OrderRange.{u, v} := by
  intro 𝕜 H _ _ _ _ P Q
  exact ((ContinuousLinearMap.IsStarProjection.isSymmetricProjection P.property).le_iff_range_le_range
    (ContinuousLinearMap.IsStarProjection.isSymmetricProjection Q.property))

theorem order_iff_quadratic : Spec.QuadraticOrder.{u, v} := by
  intro 𝕜 H _ _ _ _ P Q
  change (Q.val - P.val).IsPositive ↔ _
  rw [ContinuousLinearMap.isPositive_def']
  have hs := Q.property.isSelfAdjoint.sub P.property.isSelfAdjoint
  simp only [hs, true_and, ContinuousLinearMap.reApplyInnerSelf_apply,
    sub_apply, inner_sub_left, map_sub, sub_nonneg, inner_re_symm]

theorem order_iff_product : Spec.OrderProduct.{u, v} := by
  intro 𝕜 H _ _ _ _ P Q
  rw [order_iff_range 𝕜 H]
  constructor
  · intro h
    have hqp : Q.val.comp P.val = P.val := by
      apply ContinuousLinearMap.coe_inj.mp
      exact LinearMap.IsIdempotentElem.comp_eq_right_iff
        (ContinuousLinearMap.IsIdempotentElem.toLinearMap Q.property.isIdempotentElem) P.val.toLinearMap |>.mpr h
    refine ⟨?_, hqp⟩
    have hs := congrArg star hqp
    simpa only [← ContinuousLinearMap.mul_def, star_mul,
      P.property.isSelfAdjoint.star_eq, Q.property.isSelfAdjoint.star_eq] using hs
  · rintro ⟨_, hqp⟩
    exact LinearMap.IsIdempotentElem.comp_eq_right_iff
        (ContinuousLinearMap.IsIdempotentElem.toLinearMap Q.property.isIdempotentElem) P.val.toLinearMap |>.mp
      (congrArg ContinuousLinearMap.toLinearMap hqp)

section Lattice
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Range realizes the operator order as inclusion of closed subspaces. -/
def rangeOrderIso : OrthogonalProjection 𝕜 H ≃o ClosedSubmodule 𝕜 H where
  toFun := Spec.closedRange
  invFun := Spec.ofClosedSubspace
  left_inv := (range_correspondence 𝕜 H).1
  right_inv := (range_correspondence 𝕜 H).2
  map_rel_iff' := (order_iff_range 𝕜 H _ _).symm
end Lattice

theorem projection_complete_lattice : Spec.CompleteLatticeLaws.{u, v} := by
  intro 𝕜 H _ _ _ _ S
  let e := rangeOrderIso (𝕜 := 𝕜) (H := H)
  constructor
  · change IsGLB S (e.symm (sInf (e '' S)))
    exact e.isGLB_image.mp (isGLB_sInf (e '' S))
  · change IsLUB S (e.symm (sSup (e '' S)))
    exact e.isLUB_image.mp (isLUB_sSup (e '' S))

theorem meet_range : Spec.MeetRange.{u, v} := by
  intro 𝕜 H _ _ _ _ S
  change (Spec.closedRange (Spec.meet S)).toSubmodule = _
  unfold Spec.meet
  rw [(range_correspondence 𝕜 H).2]
  simp only [ClosedSubmodule.toSubmodule_sInf]
  simp only [iInf_image]
  rfl

theorem join_range : Spec.JoinRange.{u, v} := by
  intro 𝕜 H _ _ _ _ S
  change (Spec.closedRange (Spec.join S)).toSubmodule = _
  unfold Spec.join
  rw [(range_correspondence 𝕜 H).2]
  simp only [ClosedSubmodule.toSubmodule_sSup]
  simp only [iSup_image]
  rfl

theorem commuting_product_eq_meet : Spec.CommutingProduct.{u, v} := by
  intro 𝕜 H _ _ _ _ P Q hc
  have hc' : Commute P.val Q.val := hc
  let R : OrthogonalProjection 𝕜 H := ⟨P.val * Q.val, P.property.mul Q.property hc'⟩
  apply ContinuousLinearMap.IsStarProjection.ext R.property (Spec.meet {P, Q}).property
  rw [meet_range 𝕜 H]
  simp only [iInf_insert, iInf_singleton]
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    constructor
    · exact ⟨Q.val y, rfl⟩
    · refine ⟨P.val y, ?_⟩
      exact congrArg (fun f : H →L[𝕜] H => f y) hc.symm
  · intro x hx
    refine ⟨x, ?_⟩
    have hp := LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap P.property.isIdempotentElem) |>.mp hx.1
    have hq := LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap Q.property.isIdempotentElem) |>.mp hx.2
    change P.val x = x at hp
    change Q.val x = x at hq
    change P.val (Q.val x) = x
    rw [hq, hp]

section CompleteLatticeInstance
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The complete lattice uses the original operator order. -/
instance projectionCompleteLattice : CompleteLattice (OrthogonalProjection 𝕜 H) :=
  letI : InfSet (OrthogonalProjection 𝕜 H) := ⟨Spec.meet⟩
  completeLatticeOfInf _ (fun S => (projection_complete_lattice 𝕜 H S).1)

@[simp] theorem sInf_eq_meet (S : Set (OrthogonalProjection 𝕜 H)) :
    sInf S = Spec.meet S := rfl

@[simp] theorem sSup_eq_join (S : Set (OrthogonalProjection 𝕜 H)) :
    sSup S = Spec.join S :=
  (projection_complete_lattice 𝕜 H S).2.sSup_eq

/-- The lattice infimum is the intersection-range projector. -/
theorem inf_eq_meet (P Q : OrthogonalProjection 𝕜 H) :
    P ⊓ Q = Spec.meet {P, Q} := rfl

/-- For commuting projections the lattice meet is their operator product. -/
theorem commuting_product_eq_inf (P Q : OrthogonalProjection 𝕜 H)
    (hc : P.val.comp Q.val = Q.val.comp P.val) :
    P.val.comp Q.val = (P ⊓ Q).val :=
  commuting_product_eq_meet 𝕜 H P Q hc
end CompleteLatticeInstance

end ExpandedFA.Hilbert.ProjectionLattice
