import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.ClosedSumEstimates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08OpenMapping
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Tactic.Linarith

/-! Closed sums and quantitative decompositions, `fa2:p1:closed-sums`.
The converse to openness is proved using the complete quotient of the
product by the kernel of addition. No representative of minimal norm
and no continuous or linear choice of decompositions is assumed. -/

noncomputable section
universe u v w
namespace ExpandedFA.Supplements.ClosedSumEstimates

open Spec

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Addition on the product of the subspaces. The product has its native
maximum norm; multiplying constants by two recovers the displayed sum norm. -/
def additionMap (G L : Submodule 𝕜 E) : G × L →L[𝕜] E :=
  G.subtypeL.coprod L.subtypeL

@[simp] theorem additionMap_apply (G L : Submodule 𝕜 E) (p : G × L) :
    additionMap G L p = (p.1 : E) + (p.2 : E) := rfl

/-- Exact bounded preimages imply closed range. Completeness is only
needed for the domain: its quotient by the closed kernel is complete,
and the induced injection is bounded below. -/
theorem closed_range_of_controlled_preimages
    {X : Type w} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (T : X →L[𝕜] E) (C : ℝ) (hC : 0 < C)
    (h : ∀ y ∈ Set.range T, ∃ x : X, T x = y ∧ ‖x‖ ≤ C * ‖y‖) :
    IsClosed (Set.range T) := by
  have : IsClosed (T.ker : Set X) := T.isClosed_ker
  let F : (X ⧸ T.ker) →L[𝕜] E := T.ker.liftQL T le_rfl
  have hbound : ∀ q : X ⧸ T.ker, ‖q‖ ≤ C * ‖F q‖ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H a =>
      obtain ⟨x, hx, hxn⟩ := h (T a) ⟨a, rfl⟩
      have heq : (Submodule.Quotient.mk x : X ⧸ T.ker) = Submodule.Quotient.mk a := by
        apply (Submodule.Quotient.eq T.ker).mpr
        change T (x - a) = 0
        rw [map_sub, hx, sub_self]
      calc
        ‖(Submodule.Quotient.mk a : X ⧸ T.ker)‖ =
            ‖(Submodule.Quotient.mk x : X ⧸ T.ker)‖ := congrArg norm heq.symm
        _ ≤ ‖x‖ := Submodule.Quotient.norm_mk_le T.ker x
        _ ≤ C * ‖T a‖ := hxn
        _ = C * ‖F (Submodule.Quotient.mk a)‖ := rfl
  have hanti : AntilipschitzWith ⟨C, hC.le⟩ F := F.antilipschitz_of_bound hbound
  have hr : Set.range F = Set.range T := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Submodule.Quotient.induction_on with
      | H a => exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Submodule.Quotient.mk a, rfl⟩
  rw [← hr]
  exact hanti.isClosed_range F.uniformContinuous

/-- Closedness gives actual decompositions by the open mapping theorem. -/
theorem decomposition_of_closed [CompleteSpace E] (G L : Submodule 𝕜 E)
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E))
    (hs : IsClosed (↑(G ⊔ L) : Set E)) : DecompositionBound G L := by
  have : CompleteSpace G := hG.isComplete.completeSpace_coe
  have : CompleteSpace L := hL.isComplete.completeSpace_coe
  have : CompleteSpace ↥(G ⊔ L) := hs.isComplete.completeSpace_coe
  let T : G × L →L[𝕜] ↥(G ⊔ L) := (additionMap G L).codRestrict (G ⊔ L)
    (fun p => Submodule.add_mem_sup p.1.property p.2.property)
  have hT : Function.Surjective T := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, l, hl, hgl⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨g, hg⟩, ⟨l, hl⟩), Subtype.ext hgl⟩
  obtain ⟨C, hC, hpre⟩ :=
    ExpandedFA.P1.C08OpenMapping.open_mapping_controlled_preimages 𝕜 (G × L) ↥(G ⊔ L) T hT
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro x hx
  obtain ⟨p, hp, hpn⟩ := hpre ⟨x, hx⟩
  refine ⟨p.1, p.1.property, p.2, p.2.property, congrArg Subtype.val hp, ?_⟩
  have h1 : ‖(p.1 : E)‖ ≤ ‖p‖ := norm_fst_le p
  have h2 : ‖(p.2 : E)‖ ≤ ‖p‖ := norm_snd_le p
  change ‖p‖ ≤ C * ‖x‖ at hpn
  nlinarith

/-- A bounded decomposition of g-l leaves an intersection vector close to g. -/
theorem subspace_distance_of_decomposition (G L : Submodule 𝕜 E)
    (h : DecompositionBound G L) : SubspaceDistanceBound G L := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  intro g hg
  rw [mul_comm C]
  apply (div_le_iff₀ hC).mp
  apply (Metric.le_infDist ⟨0, L.zero_mem⟩).mpr
  intro l hl
  have hgl : g - l ∈ G ⊔ L :=
    (G ⊔ L).sub_mem (Submodule.mem_sup_left hg) (Submodule.mem_sup_right hl)
  obtain ⟨u, hu, v, hv, huv, hn⟩ := h (g - l) hgl
  have hmeet : g - u ∈ G ⊓ L := by
    refine ⟨G.sub_mem hg hu, ?_⟩
    have heq : g - u = l + v := by
      calc g - u = (g - l) - u + l := by abel
           _ = (u + v) - u + l := by rw [huv]
           _ = l + v := by abel
    rw [heq]
    exact L.add_mem hl hv
  have hd := Metric.infDist_le_dist_of_mem (x := g) hmeet
  have he : dist g (g - u) = ‖u‖ := by rw [dist_eq_norm]; congr 1; abel
  rw [he] at hd
  rw [div_le_iff₀ hC]
  have hnorm : ‖g - l‖ = dist g l := (dist_eq_norm g l).symm
  rw [hnorm] at hn
  nlinarith [norm_nonneg v]

/-- Approximate the distance to the intersection, with slack proportional
to ‖x‖, to obtain exact decompositions. The zero vector is handled separately. -/
theorem decomposition_of_subspace_distance (G L : Submodule 𝕜 E)
    (h : SubspaceDistanceBound G L) : DecompositionBound G L := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨2 * C + 3, by linarith, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0, G.zero_mem, 0, L.zero_mem, by simp, by simp⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨g, hg, l, hl, hgl⟩ := Submodule.mem_sup.mp hx
  have hdist : Metric.infDist g (↑(G ⊓ L) : Set E) ≤ C * ‖x‖ := by
    apply (h g hg).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hd := Metric.infDist_le_dist_of_mem (L.neg_mem hl) (x := g)
    simpa only [dist_eq_norm, sub_neg_eq_add, hgl] using hd
  obtain ⟨n, hn, hgn⟩ := (Metric.infDist_lt_iff
    (show (↑(G ⊓ L) : Set E).Nonempty from ⟨0, (G ⊓ L).zero_mem⟩)).mp
      (lt_of_le_of_lt hdist (by nlinarith : C * ‖x‖ < (C + 1) * ‖x‖))
  refine ⟨g - n, G.sub_mem hg hn.1, l + n, L.add_mem hl hn.2, ?_, ?_⟩
  · calc g - n + (l + n) = g + l := by abel
         _ = x := hgl
  · have heq : l + n = x - (g - n) := by rw [← hgl]; abel
    have hln : ‖l + n‖ ≤ ‖x‖ + ‖g - n‖ := by rw [heq]; exact norm_sub_le _ _
    rw [dist_eq_norm] at hgn
    nlinarith

/-- Infimizing twice yields the estimate for arbitrary ambient vectors. -/
theorem ambient_distance_of_subspace_distance (G L : Submodule 𝕜 E)
    (h : SubspaceDistanceBound G L) : AmbientDistanceBound G L := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C + 1, by linarith, ?_⟩
  intro x
  have haux : Metric.infDist x (↑(G ⊓ L) : Set E) ≤
      (C + 1) * Metric.infDist x (G : Set E) + C * Metric.infDist x (L : Set E) := by
    have hdiv : (Metric.infDist x (↑(G ⊓ L) : Set E) - C * Metric.infDist x (L : Set E)) /
        (C + 1) ≤ Metric.infDist x (G : Set E) := by
      apply (Metric.le_infDist ⟨0, G.zero_mem⟩).mpr
      intro g hg
      apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
      have h1 := Metric.infDist_le_infDist_add_dist (x := x) (y := g) (s := (↑(G ⊓ L) : Set E))
      have h2 := Metric.infDist_le_infDist_add_dist (x := g) (y := x) (s := (L : Set E))
      have h3 := h g hg
      rw [dist_comm g x] at h2
      nlinarith
    have := (div_le_iff₀ (by linarith : 0 < C + 1)).mp hdiv
    linarith
  nlinarith [Metric.infDist_nonneg (x := x) (s := (L : Set E))]

/-- Specializing the ambient estimate to G recovers the subspace estimate. -/
theorem subspace_distance_of_ambient_distance (G L : Submodule 𝕜 E)
    (h : AmbientDistanceBound G L) : SubspaceDistanceBound G L := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  intro g hg
  simpa only [Metric.infDist_zero_of_mem hg, zero_add] using h g

/-- The complete product and its kernel quotient turn bounded exact
preimages into closedness of the algebraic sum. -/
theorem closed_of_decomposition [CompleteSpace E] (G L : Submodule 𝕜 E)
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E))
    (h : DecompositionBound G L) : IsClosed (↑(G ⊔ L) : Set E) := by
  have : CompleteSpace G := hG.isComplete.completeSpace_coe
  have : CompleteSpace L := hL.isComplete.completeSpace_coe
  obtain ⟨C, hC, h⟩ := h
  have hr : Set.range (additionMap G L) = (↑(G ⊔ L) : Set E) := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact Submodule.add_mem_sup p.1.property p.2.property
    · intro hx
      obtain ⟨g, hg, l, hl, hgl⟩ := Submodule.mem_sup.mp hx
      exact ⟨(⟨g, hg⟩, ⟨l, hl⟩), hgl⟩
  rw [← hr]
  apply closed_range_of_controlled_preimages (additionMap G L) C hC
  intro y hy
  obtain ⟨g, hg, l, hl, hgl, hn⟩ := h y (by rwa [hr] at hy)
  refine ⟨(⟨g, hg⟩, ⟨l, hl⟩), hgl, ?_⟩
  change max ‖g‖ ‖l‖ ≤ C * ‖y‖
  exact (max_le (by linarith [norm_nonneg l]) (by linarith [norm_nonneg g]))

/-- The four primal conditions of the closed-sum theorem are equivalent. -/
theorem closed_sum_equivalences : Spec.ClosedSumEquivalences := by
  intro 𝕜 E _ _ _ _ G L hG hL
  exact ⟨⟨decomposition_of_closed G L hG hL, closed_of_decomposition G L hG hL⟩,
    ⟨subspace_distance_of_decomposition G L, decomposition_of_subspace_distance G L⟩,
    ⟨ambient_distance_of_subspace_distance G L, subspace_distance_of_ambient_distance G L⟩⟩

end ExpandedFA.Supplements.ClosedSumEstimates
