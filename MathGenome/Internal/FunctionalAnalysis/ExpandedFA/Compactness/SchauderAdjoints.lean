import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.SchauderAdjoints
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.CompactIdeal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.BanachAdjoints
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BidualClosedImage
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.Linarith

/-!
Schauder's theorem for the shared Banach transpose. For the forward
implication finite nets for the compact image and its finite tuples of
scalar values give finite discretizations of the transpose unit-ball
image. Completeness is used only in the dual. For the converse, use
T″ J_X = J_Y T and the closed isometric canonical image of the complete
target Y, so compactness is recovered in Y itself.
-/
namespace ExpandedFA.Compactness.SchauderAdjoints

open Set Metric

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
  {E : Type v} {F : Type w} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Compactness of the original image gives finite discretizations of the
transpose image in the dual operator norm. -/
theorem totallyBounded_banachTranspose_image (T : E →L[𝕜] F)
    (hT : IsCompactLinearMap T.toLinearMap) :
    TotallyBounded (P1.C04Annihilators.banachTranspose 𝕜 E F T '' closedBall (0 : StrongDual 𝕜 F) 1) := by
  classical
  let T' := P1.C04Annihilators.banachTranspose 𝕜 E F T
  let S := T' '' closedBall (0 : StrongDual 𝕜 F) 1
  have preimage (a : S) : ∃ f : StrongDual 𝕜 F, ‖f‖ ≤ 1 ∧ T' f = a := by
    obtain ⟨f, hf, heq⟩ := a.property
    exact ⟨f, mem_closedBall_zero_iff.mp hf, heq⟩
  choose f hf heq using preimage
  apply totallyBounded_of_finite_discretization
  intro ε hε
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨Y, _, hYfin, hY⟩ :=
    (show IsCompact (closure (T '' closedBall (0 : E) 1)) from hT).finite_cover_balls hδ
  let := hYfin.fintype
  let V : S → (Y → 𝕜) := fun a y => f a y
  let Q : Set (Y → 𝕜) := Set.pi Set.univ (fun y => closedBall (0 : 𝕜) ‖(y : F)‖)
  have hQ : IsCompact Q :=
    isCompact_univ_pi (fun y => isCompact_closedBall (0 : 𝕜) ‖(y : F)‖)
  have hV (a : S) : V a ∈ Q := by
    intro y _
    apply mem_closedBall_zero_iff.mpr
    exact (f a).le_opNorm y |>.trans (mul_le_of_le_one_left (norm_nonneg _) (hf a))
  obtain ⟨Z, _, hZfin, hZ⟩ := hQ.finite_cover_balls hδ
  let := hZfin.fintype
  have near (a : S) : ∃ z : Z, dist (V a) z < δ := by
    obtain ⟨z, hz, h⟩ := mem_iUnion₂.mp (hZ (hV a))
    exact ⟨⟨z, hz⟩, h⟩
  choose z hz using near
  -- Encode the finite set by a small finite type, independently of F's universe.
  let code : S → ULift.{max u v} (Fin (Fintype.card Z)) :=
    fun a => ⟨Fintype.equivFin Z (z a)⟩
  refine ⟨_, inferInstance, code, ?_⟩
  intro a b hab
  have hzab : z a = z b := (Fintype.equivFin Z).injective (congrArg ULift.down hab)
  have hcoord (y : Y) : ‖f a y - f b y‖ < 2 * δ := by
    have hd : dist (V a) (V b) < 2 * δ := by
      calc
        dist (V a) (V b) ≤ dist (V a) (z a) + dist (V b) (z a) :=
          dist_triangle_right _ _ _
        _ < δ + δ := add_lt_add (hz a) (hzab ▸ hz b)
        _ = 2 * δ := by ring
    exact lt_of_le_of_lt (norm_le_pi_norm (V a - V b) y) (by simpa [dist_eq_norm] using hd)
  have hnorm : ‖T' (f a) - T' (f b)‖ ≤ 4 * δ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    have hTx : T x ∈ closure (T '' closedBall (0 : E) 1) :=
      subset_closure ⟨x, mem_closedBall_zero_iff.mpr hx.le, rfl⟩
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hY hTx)
    have hdist : ‖T x - y‖ < δ := by simpa [dist_eq_norm] using hxy
    have hfa : ‖f a (T x - y)‖ ≤ ‖T x - y‖ :=
      ((f a).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hf a))
    have hfb : ‖f b (T x - y)‖ ≤ ‖T x - y‖ :=
      ((f b).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hf b))
    have hid : f a (T x) - f b (T x) =
        f a (T x - y) + (f a y - f b y) - f b (T x - y) := by
      simp only [map_sub]
      abel
    change ‖f a (T x) - f b (T x)‖ ≤ 4 * δ
    rw [hid]
    have h := norm_sub_le (f a (T x - y) + (f a y - f b y)) (f b (T x - y))
    have h' := norm_add_le (f a (T x - y)) (f a y - f b y)
    have hc := hcoord ⟨y, hy⟩
    dsimp at hc
    linarith
  rw [dist_eq_norm, ← heq a, ← heq b]
  apply lt_of_le_of_lt hnorm
  dsimp [δ]
  linarith

/-- Forward Schauder theorem on the continuous linear dual, with no
completeness assumption on E or F. -/
theorem compact_banachTranspose : Spec.Forward.{u, v, w} := by
  intro 𝕜 E F _ _ _ _ _ T hT
  change IsCompactLinearMap (P1.C04Annihilators.banachTranspose 𝕜 E F T).toLinearMap
  change IsCompact (closure (_ '' closedBall (0 : StrongDual 𝕜 F) 1))
  exact (totallyBounded_banachTranspose_image T hT).closure.isCompact_of_isClosed
    isClosed_closure


/-- Compactness of T′ implies compactness of T when its target is Banach. -/
theorem compact_of_compact_banachTranspose :
    Spec.Converse.{u, v, w} := by
  intro 𝕜 E F _ _ _ _ _ _ T hT'
  let T' := P1.C04Annihilators.banachTranspose 𝕜 E F T
  let T'' := P1.C04Annihilators.banachTranspose 𝕜 (StrongDual 𝕜 F) (StrongDual 𝕜 E) T'
  have hT'' : IsCompactLinearMap T''.toLinearMap :=
    compact_banachTranspose 𝕜 (StrongDual 𝕜 F) (StrongDual 𝕜 E) T' hT'
  have hcomp : IsCompactOperator (T''.comp (P1.C04CanonicalMap.canonicalEvaluation 𝕜 E)) :=
    ((compact_iff_isCompactOperator _).mp hT'').comp_clm _
  have hnat := BanachAdjoints.bidual_naturality 𝕜 E F T
  change T''.comp (P1.C04CanonicalMap.canonicalEvaluation 𝕜 E) =
    (P1.C04CanonicalMap.canonicalEvaluation 𝕜 F).comp T at hnat
  rw [hnat] at hcomp
  have hK := hcomp.isCompact_closure_image_closedBall (r := (1 : ℝ))
  have hJ : Isometry (P1.C04CanonicalMap.canonicalEvaluation 𝕜 F) :=
    P1.BidualClosedImage.canonicalEvaluation_isometry 𝕜 F
  have hclosed : IsClosed (Set.range (P1.C04CanonicalMap.canonicalEvaluation 𝕜 F)) :=
    (P1.BidualClosedImage.canonicalEvaluation_closed_range_iff_banach 𝕜 F).mpr
      ((P1.C01Banach.isBanachSpace_iff_completeSpace F).mpr inferInstance)
  have hpre := hJ.isEmbedding.isInducing.isCompact_preimage hclosed hK
  change IsCompact (closure (T '' Metric.closedBall (0 : E) 1))
  apply hpre.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro y ⟨x, hx, rfl⟩
    exact subset_closure ⟨x, hx, rfl⟩
  · exact isClosed_closure.preimage hJ.continuous

/-- The full equivalence requires no completeness assumption on the domain. -/
theorem compact_iff_compact_banachTranspose :
    Spec.Equivalence.{u, v, w} := by
  intro 𝕜 E F _ _ _ _ _ _ T
  exact ⟨compact_banachTranspose 𝕜 E F T,
    compact_of_compact_banachTranspose 𝕜 E F T⟩

end ExpandedFA.Compactness.SchauderAdjoints
