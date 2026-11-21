import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.KirkFixedPoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.NormalStructure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14MilmanPettis
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Order.Zorn

namespace ExpandedFA.Geometry.KirkFixedPoint
universe u v
noncomputable section
open Set Metric
open scoped Topology

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- A norm-closed real-convex set is weakly closed. -/
lemma weakImage_isClosed {D : Set E} (hc : Convex ℝ D) (hd : IsClosed D) :
    IsClosed (toWeakSpace 𝕜 E '' D) := by
  rw [← closure_eq_iff_isClosed, ← hc.toWeakSpace_closure 𝕜, hd.closure_eq]

/-- Weak compactness implies norm boundedness, by uniform boundedness on the dual. -/
lemma bounded_of_weaklyCompact {C : Set E}
    (hc : IsCompact (toWeakSpace 𝕜 E '' C)) : Bornology.IsBounded C := by
  have hb := (WeakDual.isBounded_iff_isVonNBounded (𝕜 := 𝕜)
    (E := StrongDual 𝕜 E)).mpr
      ((hc.image (NormedSpace.inclusionInDoubleDualWeak 𝕜 E).continuous).isVonNBounded 𝕜)
  have heq : NormedSpace.inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' C) =
      StrongDual.toWeakDual '' (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜 '' C) := by
    ext x
    simp only [mem_image]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  rw [heq] at hb
  have hb' := (WeakDual.isBounded_toWeakDual_preimage_iff_isBounded).mpr hb
  rw [preimage_image_eq _ StrongDual.toWeakDual.injective] at hb'
  rw [isBounded_iff_forall_norm_le] at hb' ⊢
  obtain ⟨R, hR⟩ := hb'
  exact ⟨R, fun x hx => by
    simpa only [LinearIsometry.norm_map] using hR _ (mem_image_of_mem _ hx)⟩

/-- A minimal nonempty weakly closed convex invariant subset. Compactness,
not weak continuity of the map, ensures nonempty chain intersections. -/
lemma exists_minimal_invariant {C : Set E} (hne : C.Nonempty)
    (hcompact : IsCompact (toWeakSpace 𝕜 E '' C)) (hconvex : Convex ℝ C)
    (f : E → E) (hf : MapsTo f C C) :
    ∃ M : Set E, M ⊆ C ∧ M.Nonempty ∧ IsClosed (toWeakSpace 𝕜 E '' M) ∧
      Convex ℝ M ∧ MapsTo f M M ∧
      ∀ D : Set E, D ⊆ M → D.Nonempty → IsClosed (toWeakSpace 𝕜 E '' D) →
        Convex ℝ D → MapsTo f D D → M ⊆ D := by
  let S : Set (Set E) := {D | D ⊆ C ∧ D.Nonempty ∧
    IsClosed (toWeakSpace 𝕜 E '' D) ∧ Convex ℝ D ∧ MapsTo f D D}
  have hC : C ∈ S := ⟨Subset.rfl, hne, hcompact.isClosed, hconvex, hf⟩
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ D ∈ S, ∀ A ∈ c, D ⊆ A := by
    intro c hcs hc hcn
    letI : Nonempty c := hcn.to_subtype
    let D : Set E := ⋂ i : c, (i : Set E)
    have hDC : D ⊆ C := by
      obtain ⟨A, hA⟩ := hcn
      exact (iInter_subset _ (⟨A, hA⟩ : c)).trans (hcs hA).1
    have hclosed : IsClosed (toWeakSpace 𝕜 E '' D) := by
      rw [show toWeakSpace 𝕜 E '' D = ⋂ i : c, toWeakSpace 𝕜 E '' (i : Set E) from
        image_iInter (toWeakSpace 𝕜 E).bijective _]
      exact isClosed_iInter fun i => (hcs i.property).2.2.1
    have hDn : D.Nonempty := by
      have hn := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        (fun i : c => toWeakSpace 𝕜 E '' (i : Set E)) ?_
        (fun i => (hcs i.property).2.1.image _) ?_
        (fun i => (hcs i.property).2.2.1)
      · rw [← image_iInter (toWeakSpace 𝕜 E).bijective] at hn
        exact hn.of_image
      · intro i j
        rcases hc.total i.property j.property with hij | hji
        · exact ⟨i, Subset.rfl, image_mono hij⟩
        · exact ⟨j, image_mono hji, Subset.rfl⟩
      · intro i
        exact hcompact.of_isClosed_subset (hcs i.property).2.2.1
          (image_mono (hcs i.property).1)
    refine ⟨D, ⟨hDC, hDn, hclosed, convex_iInter (fun i => (hcs i.property).2.2.2.1), ?_⟩, ?_⟩
    · intro x hx
      exact mem_iInter.mpr fun i => (hcs i.property).2.2.2.2 (mem_iInter.mp hx i)
    · intro A hA
      exact iInter_subset (fun i : c => (i : Set E)) (⟨A, hA⟩ : c)

  obtain ⟨M, _, hM⟩ := zorn_superset_nonempty S hchain C hC
  exact ⟨M, hM.prop.1, hM.prop.2.1, hM.prop.2.2.1, hM.prop.2.2.2.1,
    hM.prop.2.2.2.2, fun D hDM hn hd hv hi =>
      hM.le_of_le ⟨hDM.trans hM.prop.1, hn, hd, hv, hi⟩ hDM⟩

/-- The geometric argument on an ambient map, using only its restriction to C. -/
lemma fixedPoint_of_mapsTo {C : Set E} (hne : C.Nonempty)
    (hcompact : IsCompact (toWeakSpace 𝕜 E '' C)) (hconvex : Convex ℝ C)
    (hnormal : NormalStructure.HasNormalStructure C)
    (f : E → E) (hf : MapsTo f C C)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, dist (f x) (f y) ≤ dist x y) :
    ∃ x ∈ C, f x = x := by
  obtain ⟨M, hMC, hMn, hMw, hMv, hMi, hmin⟩ :=
    exists_minimal_invariant hne hcompact hconvex f hf
  have hMb : Bornology.IsBounded M := (bounded_of_weaklyCompact hcompact).subset hMC
  have hMclosed : IsClosed M := by
    have hpre := hMw.preimage (toWeakSpaceCLM 𝕜 E).continuous
    change IsClosed ((toWeakSpace 𝕜 E) ⁻¹' (toWeakSpace 𝕜 E '' M)) at hpre
    simpa only [preimage_image_eq _ (toWeakSpace 𝕜 E).injective] using hpre
  have hhsub : closedConvexHull ℝ (f '' M) ⊆ M :=
    closedConvexHull_min (image_subset_iff.mpr hMi) hMv hMclosed
  have hMh : M ⊆ closedConvexHull ℝ (f '' M) := by
    apply hmin _ hhsub
    · exact (hMn.image f).mono subset_closedConvexHull
    · exact weakImage_isClosed convex_closedConvexHull isClosed_closedConvexHull
    · exact convex_closedConvexHull
    · intro x hx
      exact subset_closedConvexHull (mem_image_of_mem f (hhsub hx))
  have hdiam : Metric.diam M = 0 := by
    by_contra hd
    have hdpos : 0 < Metric.diam M := lt_of_le_of_ne Metric.diam_nonneg (Ne.symm hd)
    obtain ⟨z, hz, hzsup⟩ := hnormal M hMC hMv hdpos
    let r := sSup ((fun y => ‖z - y‖) '' M)
    have hb : BddAbove ((fun y => ‖z - y‖) '' M) := by
      refine ⟨Metric.diam M, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hMb hz hy
    have hzbound : ∀ y ∈ M, dist z y ≤ r := by
      intro y hy
      rw [dist_eq_norm]
      exact le_csSup hb (mem_image_of_mem _ hy)
    have hr : 0 ≤ r := by simpa using hzbound z hz
    let A := M ∩ ⋂ y ∈ M, closedBall y r
    have hAv : Convex ℝ A :=
      hMv.inter (convex_iInter fun y => convex_iInter fun _ => convex_closedBall y r)
    have hAc : IsClosed A :=
      hMclosed.inter (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_closedBall)
    have hAn : A.Nonempty := by
      refine ⟨z, hz, ?_⟩
      simpa only [mem_iInter, mem_closedBall] using hzbound
    have hAi : MapsTo f A A := by
      intro x hx
      have hxM : x ∈ M := hx.1
      have hxbound : ∀ y ∈ M, dist x y ≤ r := by
        simpa only [mem_iInter, mem_closedBall] using hx.2
      have hball : f '' M ⊆ closedBall (f x) r := by
        rintro _ ⟨y, hy, rfl⟩
        rw [mem_closedBall, dist_comm]
        exact (hlip x (hMC hxM) y (hMC hy)).trans (hxbound y hy)
      have hall : M ⊆ closedBall (f x) r := hMh.trans
        (closedConvexHull_min hball (convex_closedBall _ _) isClosed_closedBall)
      refine ⟨hMi hxM, ?_⟩
      simp only [mem_iInter, mem_closedBall]
      intro y hy
      exact (dist_comm (f x) y) ▸ hall hy
    have hMA := hmin A inter_subset_left hAn (weakImage_isClosed hAv hAc) hAv hAi
    have hdle : Metric.diam M ≤ r := Metric.diam_le_of_forall_dist_le hr (by
      intro x hx y hy
      exact mem_iInter.mp (mem_iInter.mp (hMA hx).2 y) hy)
    exact (not_le_of_gt hzsup) hdle
  obtain ⟨x, hx⟩ := hMn
  refine ⟨x, hMC hx, dist_le_zero.mp ?_⟩
  exact hdiam ▸ Metric.dist_le_diam_of_mem hMb (hMi hx) hx

/-- Kirk's fixed point theorem, for either scalar field. -/
theorem kirk_fixed_point : Spec.KirkFixedPoint.{u,v} := by
  intro 𝕜 E _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  intro C hne hcompact hconvex hnormal T hT
  classical
  let f : E → E := fun x => if h : x ∈ C then T ⟨x, h⟩ else x
  have hf (x : E) (hx : x ∈ C) : f x = T ⟨x, hx⟩ := dif_pos hx
  obtain ⟨x, hx, hfix⟩ := fixedPoint_of_mapsTo hne hcompact hconvex hnormal f
    (fun x hx => by rw [hf x hx]; exact (T ⟨x, hx⟩).property)
    (fun x hx y hy => by
      rw [hf x hx, hf y hy]
      simpa only [one_mul, NNReal.coe_one, Subtype.dist_eq] using hT.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩)
  exact ⟨⟨x, hx⟩, Subtype.ext ((hf x hx).symm.trans hfix)⟩

/-- Surjective canonical evaluation transfers Banach–Alaoglu compactness to E. -/
lemma weaklyCompact_of_reflexive {C : Set E} (hc : IsClosed C)
    (hv : Convex ℝ C) (hb : Bornology.IsBounded C)
    (href : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E)) :
    IsCompact (toWeakSpace 𝕜 E '' C) := by
  have hrange : Function.Surjective (NormedSpace.inclusionInDoubleDualWeak 𝕜 E) := by
    intro ξ
    obtain ⟨x, hx⟩ := href (WeakDual.toStrongDual ξ)
    exact ⟨toWeakSpace 𝕜 E x, congrArg StrongDual.toWeakDual hx⟩
  have hw := weakImage_isClosed (𝕜 := 𝕜) hv hc
  rw [← hw.closure_eq]
  apply NormedSpace.isCompact_closure_of_isBounded
  · simpa only [preimage_image_eq _ (toWeakSpace 𝕜 E).injective] using hb
  · rw [hrange.range_eq]
    exact subset_univ _

/-- Browder–Göhde–Kirk, including complex spaces and the zero space. -/
theorem browder_gohde_kirk : Spec.BrowderGohdeKirk.{u,v} := by
  intro 𝕜 E _ _ _ _ huc
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  intro C hne hc hb hv T hT
  have href : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E) :=
    ExpandedFA.P1.C14MilmanPettis.milman_pettis 𝕜 E huc
  exact kirk_fixed_point 𝕜 E C hne (weaklyCompact_of_reflexive hc hv hb href) hv
    (NormalStructure.uniformlyConvex_normalStructure 𝕜 E huc C hb hv) T hT

end
end ExpandedFA.Geometry.KirkFixedPoint
