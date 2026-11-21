import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.ClosedSumsDuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.ClosedSumEstimates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.KreinSmulian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.LocallyConvex.Separation

/-! Closed sums and Banach annihilators, `fa2:p1:closed-sums`.
The four primal conditions use the accepted quantitative closed-sum theorem.
The forward dual implication uses an explicitly bounded Hahn–Banach extension
on G+L. For the converse, bounded decompositions and Alaoglu give weak-star
closedness of the unit slice, so Krein–Šmulian applies. Weak representation
and separation then identify the sum with the intersection annihilator.
Distance-norming functionals recover the ambient primal estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace ExpandedFA.Supplements.ClosedSumsDuality

open Spec
open ExpandedFA.P1
open Set Topology

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma annihilator_sum_le (G L : Submodule 𝕜 E) :
    annihilator G ⊔ annihilator L ≤ annihilator (G ⊓ L) := by
  apply sup_le
  · intro f hf x hx
    exact hf x hx.1
  · intro f hf x hx
    exact hf x hx.2

lemma annihilator_isClosed (M : Submodule 𝕜 E) :
    IsClosed (annihilator M : Set (E →L[𝕜] 𝕜)) := by
  have heq : (annihilator M : Set (E →L[𝕜] 𝕜)) =
      ⋂ x : M, {f : E →L[𝕜] 𝕜 | f x = 0} := by
    ext f
    simp only [mem_iInter, mem_ofPred_eq]
    exact ⟨fun hf x => hf x x.property, fun hf x hx => hf ⟨x, hx⟩⟩
  rw [heq]
  exact isClosed_iInter fun x => isClosed_eq (ContinuousLinearMap.apply 𝕜 𝕜 (x : E)).continuous
    continuous_const

/-- A functional killed on the overlap has a well-defined value f(l) on g+l.
Bounded primal decompositions bound this functional before Hahn–Banach. -/
lemma bounded_annihilator_decomposition_of_primal_bound (G L : Submodule 𝕜 E)
    (h : ClosedSumEstimates.Spec.DecompositionBound G L) :
    AnnihilatorDecompositionBound G L := by
  classical
  obtain ⟨C, hC, h⟩ := h
  refine ⟨2 * C + 1, by linarith, ?_⟩
  intro f hf
  let T : G × L →ₗ[𝕜] ↥(G ⊔ L) :=
    ((ClosedSumEstimates.additionMap G L).codRestrict (G ⊔ L)
      (fun p => Submodule.add_mem_sup p.1.property p.2.property)).toLinearMap
  have hT : Function.Surjective T := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, l, hl, heq⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨g, hg⟩, ⟨l, hl⟩), Subtype.ext heq⟩
  let q : G × L →ₗ[𝕜] 𝕜 := (f.toLinearMap.comp L.subtype).comp (LinearMap.snd 𝕜 G L)
  have hk : T.ker ≤ q.ker := by
    intro p hp
    have hp' : (p.1 : E) + (p.2 : E) = 0 := congrArg Subtype.val hp
    change f (p.2 : E) = 0
    apply hf
    exact ⟨by
      have he : (p.2 : E) = -(p.1 : E) := eq_neg_of_add_eq_zero_right hp'
      rw [he]
      exact G.neg_mem p.1.property, p.2.property⟩
  let a₀ : ↥(G ⊔ L) →ₗ[𝕜] 𝕜 := T.liftOfSurjective hT ⟨q, hk⟩
  have ha₀ (g : G) (l : L) : a₀ (T (g, l)) = f (l : E) :=
    LinearMap.equivOfSurjective_apply hT hk
  have habound : ∀ x : ↥(G ⊔ L), ‖a₀ x‖ ≤ (C * ‖f‖) * ‖x‖ := by
    intro x
    obtain ⟨g, hg, l, hl, heq, hn⟩ := h x x.property
    have hx : T (⟨g, hg⟩, ⟨l, hl⟩) = x := Subtype.ext heq
    rw [← hx, ha₀]
    change ‖f l‖ ≤ (C * ‖f‖) * ‖g + l‖
    have he := f.le_opNorm l
    have hln : ‖l‖ ≤ C * ‖g + l‖ := by rw [heq]; linarith [norm_nonneg g]
    nlinarith [norm_nonneg f]
  let a₁ : ↥(G ⊔ L) →L[𝕜] 𝕜 := a₀.mkContinuous (C * ‖f‖) habound
  obtain ⟨a, ha, han⟩ := exists_extension_norm_eq (G ⊔ L) a₁
  have han' : ‖a‖ ≤ C * ‖f‖ := by
    rw [han]
    exact a₁.opNorm_le_bound (mul_nonneg hC.le (norm_nonneg f)) habound
  have hag : a ∈ annihilator G := by
    intro g hg
    have hval := ha (T (⟨g, hg⟩, 0))
    have heq : (T (⟨g, hg⟩, 0) : E) = g := by change g + 0 = g; exact add_zero g
    rw [heq] at hval
    exact hval.trans ((ha₀ ⟨g, hg⟩ 0).trans (map_zero f))
  have hbl : f - a ∈ annihilator L := by
    intro l hl
    have hval := ha (T (0, ⟨l, hl⟩))
    have heq : (T (0, ⟨l, hl⟩) : E) = l := by change 0 + l = l; exact zero_add l
    rw [heq] at hval
    have hal : a l = f l := hval.trans (ha₀ 0 ⟨l, hl⟩)
    simp [hal]
  refine ⟨a, hag, f - a, hbl, by abel, ?_⟩
  have hsub := norm_sub_le f a
  nlinarith

/-- An annihilator functional is bounded by distance to its subspace. -/
lemma annihilator_eval_le_distance (M : Submodule 𝕜 E) (f : E →L[𝕜] 𝕜)
    (hf : f ∈ annihilator M) (x : E) :
    ‖f x‖ ≤ ‖f‖ * Metric.infDist x (M : Set E) := by
  by_cases hn : ‖f‖ = 0
  · have hf0 : f = 0 := norm_eq_zero.mp hn
    simp [hf0]
  have hn' : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hn)
  rw [mul_comm ‖f‖, ← div_le_iff₀ hn']
  apply (Metric.le_infDist ⟨0, M.zero_mem⟩).mpr
  intro m hm
  rw [div_le_iff₀ hn']
  have heq : f (x - m) = f x := by rw [map_sub, hf m hm, sub_zero]
  simpa only [heq, dist_eq_norm, mul_comm] using f.le_opNorm (x - m)

lemma mem_of_annihilators_vanish (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E))
    (x : E) (hx : ∀ f ∈ annihilator M, f x = 0) : x ∈ M := by
  by_contra hnot
  obtain ⟨f, hf, _, hfx, hd⟩ := C05Norming.distance_norming_functional 𝕜 E M x
    (by rw [hM.closure_eq]; exact hnot)
  have hz := hx f hf
  rw [hfx, RCLike.ofReal_eq_zero] at hz
  exact hd.ne' hz

lemma ambient_distance_of_annihilator_decomposition (G L : Submodule 𝕜 E)
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E))
    (h : AnnihilatorDecompositionBound G L) :
    ClosedSumEstimates.Spec.AmbientDistanceBound G L := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  intro x
  by_cases hx : x ∈ G ⊓ L
  · rw [Metric.infDist_zero_of_mem hx]
    exact mul_nonneg hC.le (add_nonneg Metric.infDist_nonneg Metric.infDist_nonneg)
  have hI : IsClosed (↑(G ⊓ L) : Set E) := hG.inter hL
  obtain ⟨f, hf, hfn, hfx, _⟩ := C05Norming.distance_norming_functional 𝕜 E (G ⊓ L) x
    (by rw [hI.closure_eq]; exact hx)
  obtain ⟨a, ha, b, hb, hab, hn⟩ := h f hf
  rw [hfn, mul_one] at hn
  have hax := annihilator_eval_le_distance G a ha x
  have hbx := annihilator_eval_le_distance L b hb x
  have hnorm : ‖f x‖ = Metric.infDist x (↑(G ⊓ L) : Set E) := by
    rw [hfx, RCLike.norm_ofReal, abs_of_nonneg Metric.infDist_nonneg]
  have hfbound : ‖f x‖ ≤ ‖a x‖ + ‖b x‖ := by
    rw [← hab]
    exact norm_add_le _ _
  nlinarith [norm_nonneg a, norm_nonneg b,
    Metric.infDist_nonneg (x := x) (s := (G : Set E)),
    Metric.infDist_nonneg (x := x) (s := (L : Set E))]

/-- The shared initial topology agrees with the native weak-dual topology
on the same underlying carrier. Norms below always belong to the strong dual. -/
lemma weakStarTopology_eq_native : C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E =
    instTopologicalSpaceWeakDual 𝕜 E := by
  change TopologicalSpace.induced id _ = _
  exact @induced_id (E →L[𝕜] 𝕜) (instTopologicalSpaceWeakDual 𝕜 E)

lemma weak_annihilator_isClosed (M : Submodule 𝕜 E) :
    @IsClosed (WeakDual 𝕜 E) (instTopologicalSpaceWeakDual 𝕜 E)
      (annihilator M : Set (E →L[𝕜] 𝕜)) := by
  have heq : ((annihilator M : Set (E →L[𝕜] 𝕜)) : Set (WeakDual 𝕜 E)) =
      ⋂ x : M, {f : WeakDual 𝕜 E | f x = 0} := by
    ext f
    simp only [mem_iInter]
    exact ⟨fun hf x => hf x x.property, fun hf x hx => hf ⟨x, hx⟩⟩
  rw [heq]
  exact isClosed_iInter fun x => isClosed_eq (WeakDual.eval_continuous (𝕜 := 𝕜) (x : E))
    continuous_const

/-- Openness supplies bounded decompositions; compactness of the two
bounded annihilator slices makes the unit slice of their sum weak-star closed. -/
lemma weakStar_closed_of_norm_closed [CompleteSpace E] (G L : Submodule 𝕜 E)
    (hs : IsClosed (↑(annihilator G ⊔ annihilator L) : Set (E →L[𝕜] 𝕜))) :
    @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (↑(annihilator G ⊔ annihilator L) : Set (E →L[𝕜] 𝕜)) := by
  obtain ⟨C, hC, h⟩ := ClosedSumEstimates.decomposition_of_closed
    (annihilator G) (annihilator L) (annihilator_isClosed G) (annihilator_isClosed L) hs
  apply (KreinSmulian.subspace_closed_criterion 𝕜 E (annihilator G ⊔ annihilator L)).mpr
  rw [weakStarTopology_eq_native]
  change @IsClosed (WeakDual 𝕜 E) (instTopologicalSpaceWeakDual 𝕜 E)
    ((↑(annihilator G ⊔ annihilator L) : Set (E →L[𝕜] 𝕜)) ∩
      {f : WeakDual 𝕜 E | ‖WeakDual.toStrongDual f‖ ≤ 1})
  let A : Set (WeakDual 𝕜 E) :=
    {f | f ∈ annihilator G ∧ ‖WeakDual.toStrongDual f‖ ≤ C}
  let B : Set (WeakDual 𝕜 E) :=
    {f | f ∈ annihilator L ∧ ‖WeakDual.toStrongDual f‖ ≤ C}
  have hball : IsCompact {f : WeakDual 𝕜 E | ‖WeakDual.toStrongDual f‖ ≤ C} := by
    have hc := C13Alaoglu.weakStar_closedBall_isCompact 𝕜 E (0 : E →L[𝕜] 𝕜) C hC.le
    rw [weakStarTopology_eq_native] at hc
    change @IsCompact (E →L[𝕜] 𝕜) (instTopologicalSpaceWeakDual 𝕜 E) {f | ‖f‖ ≤ C}
    simpa only [sub_zero] using hc
  have hA : IsCompact A := hball.inter_left (weak_annihilator_isClosed G)
  have hB : IsCompact B := by
    have hc := hball.inter_left (weak_annihilator_isClosed L)
    exact hc
  have hk : IsCompact ((fun p : WeakDual 𝕜 E × WeakDual 𝕜 E => p.1 + p.2) '' (A ×ˢ B)) :=
    (hA.prod hB).image (continuous_fst.add continuous_snd)
  have heq : (((↑(annihilator G ⊔ annihilator L) : Set (E →L[𝕜] 𝕜)) : Set (WeakDual 𝕜 E)) ∩
      {f : WeakDual 𝕜 E | ‖WeakDual.toStrongDual f‖ ≤ 1}) =
      ((fun p : WeakDual 𝕜 E × WeakDual 𝕜 E => p.1 + p.2) '' (A ×ˢ B)) ∩
      {f : WeakDual 𝕜 E | ‖WeakDual.toStrongDual f‖ ≤ 1} := by
    ext f
    constructor
    · rintro ⟨hf, hfn⟩
      obtain ⟨a, ha, b, hb, hab, hn⟩ := h (WeakDual.toStrongDual f) hf
      have hn' : ‖a‖ + ‖b‖ ≤ C := hn.trans (by simpa using mul_le_mul_of_nonneg_left hfn hC.le)
      refine ⟨⟨(StrongDual.toWeakDual a, StrongDual.toWeakDual b),
        ⟨⟨ha, ?_⟩, ⟨hb, ?_⟩⟩, ?_⟩, hfn⟩
      · change ‖a‖ ≤ C
        linarith [norm_nonneg b]
      · change ‖b‖ ≤ C
        linarith [norm_nonneg a]
      · exact hab
    · rintro ⟨⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, hn⟩
      exact ⟨Submodule.add_mem_sup ha.1 hb.1, hn⟩
  rw [heq]
  exact hk.isClosed.inter (by
    simpa only [Metric.closedBall, dist_zero_right, Set.preimage_ofPred_eq] using
      (WeakDual.isClosed_closedBall (𝕜 := 𝕜) (E := E) 0 1))

/-- Weak-star separation gives the annihilator identity once the algebraic
sum is weak-star closed. No norm-closure/weak-star-closure identification is
assumed. The separator is an evaluation by the weak representation theorem. -/
lemma annihilator_equality_of_weakStar_closed (G L : Submodule 𝕜 E)
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E))
    (hs : @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (↑(annihilator G ⊔ annihilator L) : Set (E →L[𝕜] 𝕜))) :
    annihilator (G ⊓ L) = annihilator G ⊔ annihilator L := by
  apply le_antisymm _ (annihilator_sum_le G L)
  intro f hf
  by_contra hnot
  let M : Submodule 𝕜 (WeakDual 𝕜 E) := annihilator G ⊔ annihilator L
  have hM : IsClosed (M : Set (WeakDual 𝕜 E)) := by
    rw [weakStarTopology_eq_native] at hs
    exact hs
  let : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing 𝕜 E)
  obtain ⟨F, r, hsep, hF⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := 𝕜) (M.restrictScalars ℝ).convex hM hnot
  obtain ⟨x, hx⟩ := (topDualPairing 𝕜 E).dualEmbedding_surjective F
  have hx' (g : WeakDual 𝕜 E) : F g = g x := by rw [← hx]; rfl
  have hall : ∀ g ∈ M, g x = 0 := by
    intro g hg
    by_contra hz
    have hh := hsep ((((r + 1 : ℝ) : 𝕜) / g x) • g) (M.smul_mem _ hg)
    rw [hx'] at hh
    change RCLike.re ((((r + 1 : ℝ) : 𝕜) / g x) * g x) < r at hh
    rw [div_mul_cancel₀ _ hz, RCLike.ofReal_re] at hh
    linarith
  have hxG : x ∈ G := mem_of_annihilators_vanish G hG x
    (fun g hg => hall g (Submodule.mem_sup_left hg))
  have hxL : x ∈ L := mem_of_annihilators_vanish L hL x
    (fun g hg => hall g (Submodule.mem_sup_right hg))
  have hfz : f x = 0 := hf x ⟨hxG, hxL⟩
  have hr : 0 < r := by simpa only [map_zero] using hsep 0 M.zero_mem
  rw [hx', hfz, map_zero] at hF
  linarith

lemma annihilator_equality_of_primal_closed [CompleteSpace E] (G L : Submodule 𝕜 E)
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E))
    (hs : IsClosed (↑(G ⊔ L) : Set E)) :
    annihilator (G ⊓ L) = annihilator G ⊔ annihilator L := by
  apply le_antisymm _ (annihilator_sum_le G L)
  obtain ⟨_, _, h⟩ := bounded_annihilator_decomposition_of_primal_bound G L
    (ClosedSumEstimates.decomposition_of_closed G L hG hL hs)
  intro f hf
  obtain ⟨a, ha, b, hb, hab, _⟩ := h f hf
  exact Submodule.mem_sup.mpr ⟨a, ha, b, hb, hab⟩

lemma annihilator_decomposition_of_dual_closed [CompleteSpace E] (G L : Submodule 𝕜 E)
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E))
    (hs : IsClosed (↑(annihilator G ⊔ annihilator L) : Set (E →L[𝕜] 𝕜))) :
    AnnihilatorDecompositionBound G L := by
  have heq := annihilator_equality_of_weakStar_closed G L hG hL
    (weakStar_closed_of_norm_closed G L hs)
  obtain ⟨C, hC, h⟩ := ClosedSumEstimates.decomposition_of_closed
    (annihilator G) (annihilator L) (annihilator_isClosed G) (annihilator_isClosed L) hs
  refine ⟨C, hC, ?_⟩
  intro f hf
  exact h f (heq ▸ hf)

/-- Closedness of the primal sum is equivalent to norm closedness of the
sum of its Banach annihilators. -/
theorem dual_closedness : Spec.DualClosedness := by
  intro 𝕜 E _ _ _ _ G L hG hL
  constructor
  · intro hs
    rw [← annihilator_equality_of_primal_closed G L hG hL hs]
    exact annihilator_isClosed (G ⊓ L)
  · intro hs
    have hb := ambient_distance_of_annihilator_decomposition G L hG hL
      (annihilator_decomposition_of_dual_closed G L hG hL hs)
    exact ClosedSumEstimates.closed_of_decomposition G L hG hL
      (ClosedSumEstimates.decomposition_of_subspace_distance G L
        (ClosedSumEstimates.subspace_distance_of_ambient_distance G L hb))

theorem closed_annihilator_equality : Spec.ClosedAnnihilatorEquality := by
  intro 𝕜 E _ _ _ _ G L hG hL hs
  exact annihilator_equality_of_primal_closed G L hG hL hs

/-- Both hypotheses give actual bounded decompositions of every functional
annihilating the intersection, uniformly in its norm. -/
theorem bounded_annihilator_decompositions : Spec.BoundedAnnihilatorDecompositions := by
  intro 𝕜 E _ _ _ _ G L hG hL hs
  rcases hs with hs | hs
  · exact bounded_annihilator_decomposition_of_primal_bound G L
      (ClosedSumEstimates.decomposition_of_closed G L hG hL hs)
  · exact annihilator_decomposition_of_dual_closed G L hG hL hs

/-- A direct wrapper around the accepted four primal equivalences. -/
theorem primal_equivalences : Spec.PrimalEquivalences :=
  ClosedSumEstimates.closed_sum_equivalences

end ExpandedFA.Supplements.ClosedSumsDuality
