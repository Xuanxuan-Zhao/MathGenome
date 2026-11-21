import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C0NotDual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C0NotComplemented
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Annihilators
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals

/-! The bidual and nondual consequences of `fa2:p1:czero-uncomplemented`.
The sequence pairing identifies the canonical range with the actual null
sequences. Naturality transports canonical complementability, and restriction
along J_Y provides the retraction for every dual, including incomplete Y. -/

noncomputable section
namespace ExpandedFA.P1.C0NotDual
local notation "D" => Dual
open C01SequenceSpaces
open ExpandedFA.FunctionSpaces.SequenceDuals
universe u v w

/-- Pullback of scalar-linear functionals by a bounded linear isomorphism. -/
def dualEquiv {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E ≃L[𝕜] F) :
    (D 𝕜 (F)) ≃L[𝕜] (D 𝕜 (E)) :=
  T.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)

@[simp] theorem dualEquiv_apply {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E ≃L[𝕜] F)
    (f : F →L[𝕜] 𝕜) (x : E) : dualEquiv T f x = f (T x) := rfl

/-- The pullback is an isometry when the original isomorphism is one. -/
def dualIsometry {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E ≃ₗᵢ[𝕜] F) :
    (D 𝕜 (F)) ≃ₗᵢ[𝕜] (D 𝕜 (E)) where
  toLinearEquiv := (dualEquiv T.toContinuousLinearEquiv).toLinearEquiv
  norm_map' f := by
    change ‖f.comp T.toContinuousLinearEquiv.toContinuousLinearMap‖ = ‖f‖
    exact f.opNorm_comp_linearIsometryEquiv T

/-- The usual isometric identification c₀″ = ℓ∞, with the chosen pairings. -/
def c0BidualIsometry (𝕜 : Type u) [RCLike 𝕜] :
    (D 𝕜 (D 𝕜 (SequenceC0 𝕜))) ≃ₗᵢ[𝕜] SequenceLInfinity 𝕜 :=
  (dualIsometry (c0DualityEquiv (𝕜 := 𝕜))).trans l1Duality.symm

@[simp] theorem c0BidualIsometry_pairing (𝕜 : Type u) [RCLike 𝕜]
    (ξ : (D 𝕜 (SequenceC0 𝕜)) →L[𝕜] 𝕜) (a : SequenceLp 𝕜 1) :
    l1Duality (𝕜 := 𝕜) (c0BidualIsometry 𝕜 ξ) a = ξ (c0DualityEquiv (𝕜 := 𝕜) a) := by
  change l1Duality (𝕜 := 𝕜) ((l1Duality (𝕜 := 𝕜)).symm (dualIsometry (c0DualityEquiv (𝕜 := 𝕜)) ξ)) a = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

@[simp] theorem c0BidualIsometry_evaluation (𝕜 : Type u) [RCLike 𝕜]
    (x : SequenceC0 𝕜) :
    c0BidualIsometry 𝕜 (evaluation 𝕜 _ x) = x.val := by
  apply l1Duality.injective
  ext a
  rw [c0BidualIsometry_pairing]
  change (∑' n, a n * x.val n) = ∑' n, x.val n * a n
  exact tsum_congr fun n => mul_comm _ _

theorem sequence_bidual_identification : Spec.SequenceBidualIdentification.{u} := by
  intro 𝕜 _
  exact ⟨c0DualityEquiv, l1Duality, c0BidualIsometry 𝕜,
    (fun _ _ => rfl), (fun _ _ => rfl), c0BidualIsometry_pairing 𝕜,
    c0BidualIsometry_evaluation 𝕜⟩

/-- Restriction along J_Y is the canonical retraction of Y‴ onto Y′. -/
def dualRetraction (𝕜 : Type u) (Y : Type v) [RCLike 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] :
    (D 𝕜 (D 𝕜 (D 𝕜 (Y)))) →L[𝕜] (D 𝕜 (Y)) :=
  C04Annihilators.banachTranspose 𝕜 _ _ (evaluation 𝕜 Y)

@[simp] theorem dualRetraction_evaluation (𝕜 : Type u) (Y : Type v) [RCLike 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (f : Y →L[𝕜] 𝕜) :
    dualRetraction 𝕜 Y (evaluation 𝕜 _ f) = f := by
  ext y
  rfl

theorem dual_canonical_complement : Spec.DualCanonicalComplement.{u,v} := by
  intro 𝕜 Y _ _ _
  refine ⟨dualRetraction 𝕜 Y, fun _ _ => rfl, dualRetraction_evaluation 𝕜 Y, ?_⟩
  exact (evaluation 𝕜 (D 𝕜 (Y))).closedComplemented_range_of_leftInverse
    (dualRetraction 𝕜 Y) (dualRetraction_evaluation 𝕜 Y)

/-- Transport a topological complement along a continuous linear equivalence. -/
theorem complemented_of_equiv {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E ≃L[𝕜] F)
    (p : Submodule 𝕜 E) (q : Submodule 𝕜 F)
    (hpq : ∀ x, x ∈ p ↔ T x ∈ q) (hq : q.ClosedComplemented) :
    p.ClosedComplemented := by
  obtain ⟨P, hP⟩ := hq
  let Q : E →L[𝕜] E := T.symm.toContinuousLinearMap.comp
    (q.subtypeL.comp (P.comp T.toContinuousLinearMap))
  have hQ : ∀ x, Q x ∈ p := by
    intro x
    apply (hpq _).mpr
    change T (T.symm (P (T x))) ∈ q
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using (P (T x)).property
  refine ⟨Q.codRestrict p hQ, ?_⟩
  intro x
  apply Subtype.ext
  change T.symm (P (T x.val)) = x.val
  have hfix := congrArg Subtype.val (hP ⟨T x.val, (hpq _).mp x.property⟩)
  exact (congrArg T.symm hfix).trans (T.symm_apply_apply _)

/-- Naturality of canonical evaluation under a linear topological isomorphism. -/
theorem bidualEquiv_evaluation {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E ≃L[𝕜] F) (x : E) :
    dualEquiv (dualEquiv T) (evaluation 𝕜 E x) =
      evaluation 𝕜 F (T x) := by
  ext f
  rfl

lemma bidualEquiv_mem_range {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E ≃L[𝕜] F)
    (ξ : (D 𝕜 (E)) →L[𝕜] 𝕜) :
    ξ ∈ (evaluation 𝕜 E).range ↔
      dualEquiv (dualEquiv T) ξ ∈ (evaluation 𝕜 F).range := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨T x, (bidualEquiv_evaluation T x).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨T.symm y, (dualEquiv (dualEquiv T)).injective ?_⟩
    change dualEquiv (dualEquiv T) (evaluation 𝕜 E (T.symm y)) = _
    rw [bidualEquiv_evaluation, T.apply_symm_apply]
    exact hy

theorem canonical_complement_invariance : Spec.CanonicalComplementInvariance.{u,v,w} := by
  intro 𝕜 E F _ _ _ _ _ T
  constructor
  · intro h
    apply complemented_of_equiv (dualEquiv (dualEquiv T)).symm
      (evaluation 𝕜 F).range (evaluation 𝕜 E).range ?_ h
    intro ξ
    simpa using (bidualEquiv_mem_range T ((dualEquiv (dualEquiv T)).symm ξ)).symm
  · exact complemented_of_equiv (dualEquiv (dualEquiv T))
      (evaluation 𝕜 E).range (evaluation 𝕜 F).range
      (bidualEquiv_mem_range T)

lemma c0BidualIsometry_mem_range (𝕜 : Type u) [RCLike 𝕜]
    (ξ : (D 𝕜 (SequenceC0 𝕜)) →L[𝕜] 𝕜) :
    ξ ∈ (evaluation 𝕜 (SequenceC0 𝕜)).range ↔
      c0BidualIsometry 𝕜 ξ ∈ sequenceC0Submodule 𝕜 := by
  constructor
  · rintro ⟨x, rfl⟩
    change c0BidualIsometry 𝕜 (evaluation 𝕜 _ x) ∈ _
    rw [c0BidualIsometry_evaluation]
    exact x.property
  · intro h
    refine ⟨⟨c0BidualIsometry 𝕜 ξ, h⟩, (c0BidualIsometry 𝕜).injective ?_⟩
    exact c0BidualIsometry_evaluation 𝕜 _

theorem canonical_image_not_complemented : Spec.CanonicalImageNotComplemented.{u} := by
  intro 𝕜 _ h
  apply C0NotComplemented.not_complemented 𝕜
  apply complemented_of_equiv (c0BidualIsometry 𝕜).symm.toContinuousLinearEquiv
    (sequenceC0Submodule 𝕜) (evaluation 𝕜 (SequenceC0 𝕜)).range ?_ h
  intro x
  simpa using (c0BidualIsometry_mem_range 𝕜 ((c0BidualIsometry 𝕜).symm x)).symm

theorem not_isomorphic_to_dual : Spec.NotIsomorphicToDual.{u,v} := by
  intro 𝕜 Y _ _ _ ⟨T⟩
  apply canonical_image_not_complemented 𝕜
  exact (canonical_complement_invariance 𝕜 _ _ T).mpr
    (dual_canonical_complement 𝕜 Y).choose_spec.2.2

end ExpandedFA.P1.C0NotDual
