import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SmallCap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.MilmanConverse
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24KreinMilman
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section

open Set TopologicalSpace
open scoped Topology Pointwise

universe u v

namespace ExpandedFA.P1

namespace SmallCap

/-- A weakly compact set is bounded for every continuous seminorm. The dual
of the associated seminormed space is Banach, even when E is incomplete. -/
theorem seminorm_bounded_of_weakly_compact
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    (K : Set E) (hK : IsCompact (toWeakSpace 𝕜 E '' K))
    (p : Seminorm 𝕜 E) (hp : Continuous p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, p x ≤ B := by
  let Q := ULift.{0} E
  let e : Q ≃ₗ[𝕜] E := ULift.moduleEquiv
  let q : Seminorm 𝕜 Q := p.comp e.toLinearMap
  letI : SeminormedAddCommGroup Q := q.toAddGroupSeminorm.toSeminormedAddCommGroup
  letI : TopologicalSpace Q := (inferInstance : SeminormedAddCommGroup Q).toUniformSpace.toTopologicalSpace
  letI : NormedSpace 𝕜 Q := ⟨fun c x => (map_smul_eq_mul q c x).le⟩
  have he : Continuous e.symm := by
    rw [continuous_iff_continuousAt]
    intro x
    change Filter.Tendsto e.symm (𝓝 x) (𝓝 (e.symm x))
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h := (isOpen_lt (hp.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds
      (show p (x - x) < ε by simpa using hε)
    filter_upwards [h] with y hy
    rw [dist_eq_norm]
    change p (e (e.symm y - e.symm x)) < ε
    simpa only [map_sub, LinearEquiv.apply_symm_apply, Function.comp_apply, Pi.sub_apply, id_eq] using hy
  let j : E →L[𝕜] Q := ⟨e.symm.toLinearMap, he⟩
  have hb : ∀ f : StrongDual 𝕜 Q, ∃ C : ℝ, ∀ x : K, ‖f (j x)‖ ≤ C := by
    intro f
    let g : E →L[𝕜] 𝕜 := f.comp j
    have hg : Continuous (fun x : WeakSpace 𝕜 E => g ((toWeakSpace 𝕜 E).symm x)) :=
      WeakBilin.eval_continuous _ g
    obtain ⟨C, hC⟩ := (hK.image hg).isBounded.exists_norm_le
    exact ⟨C, fun x => hC _ ⟨toWeakSpace 𝕜 E x, ⟨x, x.property, rfl⟩, rfl⟩⟩
  obtain ⟨B, hB⟩ := banach_steinhaus
    (g := fun x : K => NormedSpace.inclusionInDoubleDual 𝕜 Q (j x)) hb
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hB ⟨x, hx⟩
  change ‖NormedSpace.inclusionInDoubleDualLi 𝕜 (j x)‖ ≤ B at h
  rw [(NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map] at h
  exact h.trans (le_max_left _ _)


section Geometry

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [LocallyConvexSpace ℝ E]

/-- Baire category supplies a small patch of the closure of the extreme
points. Milman's converse makes the hull of its complement proper. -/
theorem exists_small_cap_of_countable_cover
    (K : Set E) (hne : K.Nonempty) (hK : IsCompact K) (hconv : Convex ℝ K)
    (q : Seminorm ℝ E) (hclosed : ∀ a r, IsClosed (q.closedBall a r))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x ∈ K, q x ≤ B)
    (ε : ℝ) (hε : 0 < ε)
    (A : Set E) (hA : A.Countable)
    (hcover : ∀ x ∈ K, ∃ a ∈ A, q (x - a) ≤ ε / 8) :
    ∃ C : Set E, C ⊂ K ∧ IsClosed C ∧ Convex ℝ C ∧
      ∃ d : ℝ, 0 ≤ d ∧ d < ε ∧
        ∀ x ∈ K \ C, ∀ y ∈ K \ C, q (x - y) ≤ d := by
  classical
  let D := closure (K.extremePoints ℝ)
  have hDK : D ⊆ K := closure_minimal extremePoints_subset hK.isClosed
  have hDc : IsCompact D := hK.of_isClosed_subset isClosed_closure hDK
  have hDn : D.Nonempty := (hK.extremePoints_nonempty hne).closure
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hDc
  letI : Nonempty D := hDn.to_subtype
  letI : Countable A := hA.to_subtype
  let F (a : A) : Set D := Subtype.val ⁻¹' q.closedBall a (ε / 8)
  have hFc (a : A) : IsClosed (F a) := (hclosed a _).preimage continuous_subtype_val
  have hFcover : ⋃ a, F a = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨a, ha, hax⟩ := hcover x (hDK x.property)
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hax⟩
  obtain ⟨a, ha⟩ := nonempty_interior_of_iUnion_of_closed hFc hFcover
  obtain ⟨W, hWo, hW⟩ := isOpen_induced_iff.mp (isOpen_interior (s := F a))
  have hWD : (D ∩ W).Nonempty := by
    obtain ⟨x, hx⟩ := ha
    exact ⟨x, x.property, by have := hx; rw [← hW] at this; exact this⟩
  have hsmall : D ∩ W ⊆ q.closedBall a (ε / 8) := by
    intro x hx
    exact (interior_subset (s := F a)) (show (⟨x, hx.1⟩ : D) ∈ interior (F a) from hW ▸ hx.2)
  let K₁ := closure (convexHull ℝ (D \ W))
  let K₂ := closure (convexHull ℝ (D ∩ W))
  have h₁K : K₁ ⊆ K := closure_minimal
    (convexHull_min (sdiff_subset.trans hDK) hconv) hK.isClosed
  have h₂K : K₂ ⊆ K := closure_minimal
    (convexHull_min (inter_subset_left.trans hDK) hconv) hK.isClosed
  have hc₁ : IsCompact K₁ := hK.of_isClosed_subset isClosed_closure h₁K
  have hc₂ : IsCompact K₂ := hK.of_isClosed_subset isClosed_closure h₂K
  have hv₁ : Convex ℝ K₁ := (convex_convexHull ℝ _).closure
  have hv₂ : Convex ℝ K₂ := (convex_convexHull ℝ _).closure
  have hs₂ : K₂ ⊆ q.closedBall a (ε / 8) := closure_minimal
    (convexHull_min hsmall (q.convex_closedBall _ _)) (hclosed a _)
  have hn₂ : K₂.Nonempty := hWD.mono ((subset_convexHull ℝ _).trans subset_closure)
  have hdiam₂ : ∀ x ∈ K₂, ∀ y ∈ K₂, q (x - y) ≤ ε / 4 := by
    intro x hx y hy
    calc
      q (x - y) = q ((x - a) - (y - a)) := by congr 1; abel
      _ ≤ q (x - a) + q (y - a) := map_sub_le_add q _ _
      _ ≤ ε / 4 := by
        have hxx : q (x - a) ≤ ε / 8 := hs₂ hx
        have hyy : q (y - a) ≤ ε / 8 := hs₂ hy
        linarith
  have hKM : K = closure (convexHull ℝ D) := by
    apply Subset.antisymm
    · rw [← closure_convexHull_extremePoints hK hconv]
      exact closure_mono (convexHull_mono subset_closure)
    · exact closure_minimal (convexHull_min hDK hconv) hK.isClosed
  have hproper₁ : K₁ ≠ K := by
    intro heq
    have hm := real_milman_converse K (D \ W) heq.symm hK
    change extremePoints K ⊆ _ at hm
    rw [extremePoints_eq_native] at hm
    have hc : IsClosed (D \ W) := isClosed_closure.sdiff hWo
    rw [hc.closure_eq] at hm
    have hDsub : D ⊆ D \ W := closure_minimal hm hc
    obtain ⟨x, hxD, hxW⟩ := hWD
    exact (hDsub hxD).2 hxW
  obtain h₁empty | hn₁ := K₁.eq_empty_or_nonempty
  · have hK₂ : K = K₂ := by
      apply Subset.antisymm ?_ h₂K
      rw [hKM]
      apply closure_minimal _ isClosed_closure
      apply convexHull_min _ hv₂
      intro x hxD
      by_cases hxW : x ∈ W
      · exact subset_closure (subset_convexHull ℝ _ ⟨hxD, hxW⟩)
      · have : x ∈ K₁ := subset_closure (subset_convexHull ℝ _ ⟨hxD, hxW⟩)
        simpa [h₁empty] using this
    refine ⟨∅, empty_ssubset.mpr hne, isClosed_empty, convex_empty, ε / 4,
      by positivity, by linarith, ?_⟩
    intro x hx y hy
    exact hdiam₂ x (hK₂ ▸ hx.1) y (hK₂ ▸ hy.1)
  have hjoin : K = convexJoin ℝ K₁ K₂ := by
    apply Subset.antisymm
    · rw [hKM]
      apply closure_minimal _ (isCompact_convexJoin hc₁ hc₂).isClosed
      apply convexHull_min _ (hv₁.convexJoin hv₂)
      intro x hxD
      by_cases hxW : x ∈ W
      · exact subset_convexJoin_right hn₁
          (subset_closure (subset_convexHull ℝ _ ⟨hxD, hxW⟩))
      · exact subset_convexJoin_left hn₂
          (subset_closure (subset_convexHull ℝ _ ⟨hxD, hxW⟩))
    · exact convexJoin_subset h₁K h₂K hconv
  let r : ℝ := min (1 / 2) (ε / (16 * (B + 1)))
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hr₁ : r < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hrB : 4 * r * B ≤ ε / 4 := by
    have h := min_le_right (1 / 2 : ℝ) (ε / (16 * (B + 1)))
    change r ≤ ε / (16 * (B + 1)) at h
    have ht : 0 < 16 * (B + 1) := by positivity
    have := (le_div_iff₀ ht).mp h
    nlinarith
  let C : Set E := r • K₁ + (1 - r) • K
  have hCc : IsCompact C := (hc₁.smul r).add (hK.smul (1 - r))
  have hCv : Convex ℝ C := (hv₁.smul r).add (hconv.smul (1 - r))
  have hCK : C ⊆ K := by
    rintro x ⟨_, ⟨x₁, hx₁, rfl⟩, _, ⟨x₂, hx₂, rfl⟩, rfl⟩
    exact hconv (h₁K hx₁) hx₂ hr.le (by linarith) (by ring)
  have hCproper : C ⊂ K := by
    refine ssubset_iff_subset_ne.mpr ⟨hCK, ?_⟩
    intro heq
    have hExt : K.extremePoints ℝ ⊆ K₁ := by
      intro x hx
      have hxC : x ∈ C := heq ▸ extremePoints_subset hx
      obtain ⟨_, ⟨x₁, hx₁, rfl⟩, _, ⟨x₂, hx₂, rfl⟩, hxrep⟩ := hxC
      have hxpaper := hx
      rw [← extremePoints_eq_native] at hxpaper
      have hx₁eq := hxpaper.2 x₁ (h₁K hx₁) x₂ hx₂ r hr hr₁ hxrep.symm
      exact hx₁eq.1 ▸ hx₁
    apply hproper₁
    apply Subset.antisymm h₁K
    rw [← closure_convexHull_extremePoints hK hconv]
    exact closure_minimal (convexHull_min hExt hv₁) isClosed_closure
  have hnear : ∀ x ∈ K \ C, ∃ y ∈ K₂, q (x - y) ≤ 2 * r * B := by
    intro x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, hseg⟩ := mem_convexJoin.mp (hjoin ▸ hx.1)
    obtain ⟨t, ht, heq⟩ := (segment_eq_image ℝ x₂ x₁) ▸ (segment_symm ℝ x₁ x₂ ▸ hseg)
    have htrep : x = t • x₁ + (1 - t) • x₂ := by rw [← heq]; module
    have htr : t < r := by
      by_contra hn
      have hrt : r ≤ t := le_of_not_gt hn
      let z := ((t - r) / (1 - r)) • x₁ + ((1 - t) / (1 - r)) • x₂
      have hz : z ∈ K := hconv (h₁K hx₁) (h₂K hx₂)
        (div_nonneg (sub_nonneg.mpr hrt) (by linarith))
        (div_nonneg (sub_nonneg.mpr ht.2) (by linarith)) (by
          field_simp [ne_of_gt (sub_pos.mpr hr₁)]
          <;> ring)
      apply hx.2
      refine ⟨r • x₁, ⟨x₁, hx₁, rfl⟩, (1 - r) • z, ⟨z, hz, rfl⟩, ?_⟩
      rw [htrep]
      dsimp [z]
      match_scalars <;> field_simp [ne_of_gt (sub_pos.mpr hr₁)] <;> ring
    refine ⟨x₂, hx₂, ?_⟩
    calc
      q (x - x₂) = q (t • (x₁ - x₂)) := by rw [htrep]; congr 1; module
      _ = t * q (x₁ - x₂) := by rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ t * (2 * B) := mul_le_mul_of_nonneg_left
        ((map_sub_le_add q _ _).trans (by linarith [hb x₁ (h₁K hx₁), hb x₂ (h₂K hx₂)])) ht.1
      _ ≤ 2 * r * B := by nlinarith
  refine ⟨C, hCproper, hCc.isClosed, hCv, 4 * r * B + ε / 4,
    by positivity, by linarith, ?_⟩
  intro x hx y hy
  obtain ⟨x₂, hx₂, hxx₂⟩ := hnear x hx
  obtain ⟨y₂, hy₂, hyy₂⟩ := hnear y hy
  calc
    q (x - y) = q ((x - x₂) + (x₂ - y₂) - (y - y₂)) := by congr 1; abel
    _ ≤ q (x - x₂) + q (x₂ - y₂) + q (y - y₂) :=
      (map_sub_le_add q _ _).trans (add_le_add (map_add_le_add q _ _) le_rfl)
    _ ≤ 4 * r * B + ε / 4 := by linarith [hdiam₂ x₂ hx₂ y₂ hy₂]

end Geometry

end SmallCap

/-- Every nonempty originally separable weakly compact convex subset of a
Hausdorff LCS has a proper weakly closed convex subset whose complement has
arbitrarily small diameter for a given continuous seminorm. -/
theorem small_cap : SmallCapSpec.smallCapType.{u, v} := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ _ K hne hsep hK hconv p hp ε hε
  letI : SeparableSpace K := hsep
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  letI : ContinuousSMul ℝ (WeakSpace 𝕜 E) := IsScalarTower.continuousSMul 𝕜
  letI : SeparatingDual 𝕜 E := ⟨fun x hx => by
    obtain ⟨f, hf⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hx
    exact ⟨f, by intro h; simpa [h] using hf⟩⟩
  letI : LocallyConvexSpace ℝ (WeakSpace 𝕜 E) :=
    WeakBilin.locallyConvexSpace (B := (topDualPairing 𝕜 E).flip)
  let w := toWeakSpace 𝕜 E
  let q : Seminorm ℝ (WeakSpace 𝕜 E) :=
    (p.restrictScalars ℝ).comp (w.symm.restrictScalars ℝ).toLinearMap
  have hq (a : WeakSpace 𝕜 E) (r : ℝ) : IsClosed (q.closedBall a r) := by
    let S := p.closedBall (w.symm a) r
    have hSc : IsClosed S :=
      isClosed_le (hp.comp (continuous_id.sub continuous_const)) continuous_const
    have hcl := (p.convex_closedBall (w.symm a) r).toWeakSpace_closure 𝕜
    change w '' closure S = closure (w '' S) at hcl
    rw [hSc.closure_eq] at hcl
    have hweak : IsClosed (w '' S) := isClosed_of_closure_subset hcl.symm.subset
    have heq : w '' S = q.closedBall a r := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨w.symm x, hx, w.apply_symm_apply x⟩
    exact heq ▸ hweak
  obtain ⟨B, hB, hb⟩ := SmallCap.seminorm_bounded_of_weakly_compact K hK p hp
  obtain ⟨A, hAc, _hAK, hAcl⟩ := exists_countable_dense_subset K
  have hcover : ∀ x ∈ w '' K, ∃ a ∈ w '' A, q (x - a) ≤ ε / 8 := by
    rintro _ ⟨x, hx, rfl⟩
    let U : Set E := {a | p (x - a) < ε / 8}
    have hU : IsOpen U := isOpen_lt (hp.comp (continuous_const.sub continuous_id)) continuous_const
    have hxU : x ∈ U := by dsimp [U]; simpa using (show (0 : ℝ) < ε / 8 by positivity)
    obtain ⟨a, haU, haA⟩ := mem_closure_iff.mp (hAcl hx) U hU hxU
    exact ⟨w a, ⟨a, haA, rfl⟩, haU.le⟩
  have hwconv : Convex ℝ (w '' K) := hconv.linear_image (w.restrictScalars ℝ).toLinearMap
  have hwb : ∀ x ∈ w '' K, q x ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hb x hx
  obtain ⟨C, hCK, hCc, hCv, d, hd₀, hdε, hd⟩ :=
    SmallCap.exists_small_cap_of_countable_cover (w '' K) (hne.image w) hK hwconv q hq
      B hB hwb ε hε (w '' A) (hAc.image w) hcover
  refine ⟨w ⁻¹' C, ?_, ?_, hCv.linear_preimage (w.restrictScalars ℝ).toLinearMap,
    d, hd₀, hdε, ?_⟩
  · apply ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, heq⟩ := hCK.subset hx
      exact w.injective heq ▸ hy
    · intro heq
      apply hCK.ne
      rw [← heq, w.surjective.image_preimage]
  · change IsClosed (w '' (w ⁻¹' C))
    rwa [w.surjective.image_preimage]
  · intro x hx y hy
    exact hd (w x) ⟨⟨x, hx.1, rfl⟩, hx.2⟩ (w y) ⟨⟨y, hy.1, rfl⟩, hy.2⟩

end ExpandedFA.P1
