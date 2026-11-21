import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionCornerCollar
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionFoundation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Applications.JordanBrouwer
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Order.Monotone.Union
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.TangentCone.Real
import MathGenome.ODEDynamics.Topics.D13Unified.Ch21
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Analysis.Calculus.ContDiff.Operations
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Applications.InvarianceDomain
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Comp
/-! Corner projection and graph construction for paper.tex 4789–4809.
The surface charts and local contractibility are constructed. Smooth transverse
fields, a uniform genuine boundary collar, and coherent induced boundary signs
are constructed below from the original geometric data.
-/
noncomputable section
set_option maxHeartbeats 800000
open Set Topology Filter
open scoped ContDiff Manifold

namespace P202.PlanarRegionTopology
open P202Specs.PlanarRegionTopology

/-- Positive projection onto one direction for both directed tangents. -/
theorem common_projection_direction {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0)
    (hn : NormedSpace.normalize u ≠ -NormedSpace.normalize v) :
    ∃ a : Plane, a ≠ 0 ∧ 0 < inner ℝ a u ∧ 0 < inner ℝ a v := by
  obtain ⟨hl, hr⟩ := normalized_direction_sum_positive hu hv hn
  let a := NormedSpace.normalize u + NormedSpace.normalize v
  have hleft : 0 < inner ℝ a u := by
    have hp : 0 < inner ℝ a (‖u‖ • NormedSpace.normalize u) := by
      rw [inner_smul_right]
      exact mul_pos (norm_pos_iff.mpr hu) hl
    simpa only [NormedSpace.norm_smul_normalize] using hp
  have hright : 0 < inner ℝ a v := by
    have hp : 0 < inner ℝ a (‖v‖ • NormedSpace.normalize v) := by
      rw [inner_smul_right]
      exact mul_pos (norm_pos_iff.mpr hv) hr
    simpa only [NormedSpace.norm_smul_normalize] using hp
  exact ⟨a, by intro hz; simp [hz] at hleft, hleft, hright⟩

/-- Positivity of the projected derivative persists on a neighborhood of
a join for each smooth extension. -/
theorem eventually_positive_projection_deriv {f : ℝ → Plane} {t δ : ℝ}
    (hδ : 0 < δ) (hf : ContDiffOn ℝ ∞ f (Ioo (t - δ) (t + δ)))
    {a : Plane} (hp : 0 < inner ℝ a (deriv f t)) :
    ∀ᶠ s in 𝓝 t, 0 < inner ℝ a (deriv f s) := by
  have ht : t ∈ Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
  have hc : ContinuousAt (deriv f) t :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).continuousAt
      (isOpen_Ioo.mem_nhds ht)
  exact (continuousAt_const.inner hc).eventually (Ioi_mem_nhds hp)

/-- An increasing projection on both closed half-arcs is increasing across
the corner. No derivative of the corner itself is used. -/
theorem strictMonoOn_across_join {f l r : ℝ → Plane} {t ε : ℝ} {a : Plane}
    (hε : 0 < ε)
    (hl : StrictMonoOn (fun s => inner ℝ a (l s)) (Icc (t - ε) t))
    (hr : StrictMonoOn (fun s => inner ℝ a (r s)) (Icc t (t + ε)))
    (hel : EqOn l f (Icc (t - ε) t))
    (her : EqOn r f (Icc t (t + ε))) :
    StrictMonoOn (fun s => inner ℝ a (f s)) (Icc (t - ε) (t + ε)) := by
  have hl' : StrictMonoOn (fun s => inner ℝ a (f s)) (Icc (t - ε) t) := by
    intro x hx y hy hxy
    simpa only [← hel hx, ← hel hy] using hl hx hy hxy
  have hr' : StrictMonoOn (fun s => inner ℝ a (f s)) (Icc t (t + ε)) := by
    intro x hx y hy hxy
    simpa only [← her hx, ← her hy] using hr hx hy hxy
  have hh := hl'.union hr' (isGreatest_Icc (by linarith))
    (isLeast_Icc (by linarith))
  rwa [Icc_union_Icc_eq_Icc (by linarith) (by linarith)] at hh

theorem cornerProjection : Expected.cornerProjection := by
  intro c t
  obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hn⟩ := c.regular_joins t
  obtain ⟨a, ha, hpl, hpr⟩ := common_projection_direction hnl hnr hn
  have hpos := (eventually_positive_projection_deriv hδ hl hpl).and
    (eventually_positive_projection_deriv hδ hr hpr)
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp hpos
  let ε := min δ η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; have := min_le_left δ η; linarith
  have hεη : ε < η := by dsimp [ε]; have := min_le_right δ η; linarith
  have hsmall : ∀ s ∈ Icc (t - ε) (t + ε),
      s ∈ Ioo (t - δ) (t + δ) ∧
      0 < inner ℝ a (deriv l s) ∧ 0 < inner ℝ a (deriv r s) := by
    intro s hs
    refine ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    apply hηball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hsubL : Icc (t - ε) t ⊆ Ioo (t - δ) (t + δ) := by
    intro s hs
    apply (hsmall s ⟨hs.1, by linarith [hs.2]⟩).1
  have hsubR : Icc t (t + ε) ⊆ Ioo (t - δ) (t + δ) := by
    intro s hs
    apply (hsmall s ⟨by linarith [hs.1], hs.2⟩).1
  have hlmono : StrictMonoOn (fun s => inner ℝ a (l s)) (Icc (t - ε) t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuousOn_const.inner (hl.continuousOn.mono hsubL)))
    intro s hs
    have hs' := interior_subset hs
    have hds : DifferentiableAt ℝ l s :=
      ((hl s (hsubL hs')).contDiffAt (isOpen_Ioo.mem_nhds (hsubL hs'))).differentiableAt
        (by simp)
    rw [deriv_inner_apply ℝ (differentiableAt_const a) hds]
    simpa using (hsmall s ⟨hs'.1, by linarith [hs'.2]⟩).2.1
  have hrmono : StrictMonoOn (fun s => inner ℝ a (r s)) (Icc t (t + ε)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuousOn_const.inner (hr.continuousOn.mono hsubR)))
    intro s hs
    have hs' := interior_subset hs
    have hds : DifferentiableAt ℝ r s :=
      ((hr s (hsubR hs')).contDiffAt (isOpen_Ioo.mem_nhds (hsubR hs'))).differentiableAt
        (by simp)
    rw [deriv_inner_apply ℝ (differentiableAt_const a) hds]
    simpa using (hsmall s ⟨by linarith [hs'.1], hs'.2⟩).2.2
  refine ⟨ε, a, hε, ha, strictMonoOn_across_join hε hlmono hrmono ?_ ?_⟩
  · exact hel.mono (by intro s hs; exact ⟨by linarith [hs.1], hs.2⟩)
  · exact her.mono (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩)

/-- Compactness gives a continuous inverse to the strictly monotone scalar
projection. Its image is the whole interval by the intermediate value theorem. -/
theorem projectedArcGraph_of_strictMono (c : RegularJordanCurve) (t ε : ℝ)
    (a : Plane) (hε : 0 < ε)
    (hm : StrictMonoOn (fun s => inner ℝ a (realLift c.parametrization s))
      (Icc (t - ε) (t + ε))) : Nonempty (ProjectedArcGraph c t ε a) := by
  let f : ℝ → ℝ := fun s => inner ℝ a (realLift c.parametrization s)
  let I : Set ℝ := Icc (t - ε) (t + ε)
  let J : Set ℝ := Icc (f (t - ε)) (f (t + ε))
  have hab : t - ε ≤ t + ε := by linarith
  have hc : Continuous (realLift c.parametrization) := by
    unfold realLift
    fun_prop
  have hf : Continuous f := continuous_const.inner hc
  have himage : f '' I = J :=
    hf.continuousOn.image_Icc_of_monotoneOn hab hm.monotoneOn
  let p : I → J := fun s => ⟨f s.val, himage ▸ mem_image_of_mem f s.property⟩
  have hp : Continuous p := by
    apply Continuous.subtype_mk
    exact hf.comp continuous_subtype_val
  have hpinj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    exact hm.injOn x.property y.property (congrArg Subtype.val hxy)
  have hpsurj : Function.Surjective p := by
    intro y
    have hy : y.val ∈ f '' I := himage.symm ▸ y.property
    obtain ⟨s, hs, heq⟩ := hy
    exact ⟨⟨s, hs⟩, Subtype.ext heq⟩
  let e : I ≃ₜ J :=
    hp.isClosedEmbedding hpinj |>.isEmbedding.toHomeomorphOfSurjective hpsurj
  let g : C(J, Plane) := ⟨fun x => realLift c.parametrization (e.symm x).val,
    hc.comp (continuous_subtype_val.comp e.symm.continuous)⟩
  refine ⟨⟨g, ?_, ?_⟩⟩
  · intro x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  · apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨(e.symm x).val, (e.symm x).property, rfl⟩
    · rintro _ ⟨s, hs, rfl⟩
      refine ⟨e ⟨s, hs⟩, ?_⟩
      change realLift c.parametrization (e.symm (e ⟨s, hs⟩)).val = _
      rw [e.symm_apply_apply]

theorem cornerGraph : Expected.cornerGraph := by
  intro c t
  obtain ⟨ε, a, hε, ha, hm⟩ := cornerProjection c t
  refine ⟨ε, a, hε, ha, ?_, projectedArcGraph_of_strictMono c t ε a hε hm⟩
  exact hm ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)

/-- A sufficiently small ambient neighborhood sees only a prescribed
parameter subarc of the embedded circle, not remote pieces of the curve. -/
theorem curve_subarc_neighborhood (c : RegularJordanCurve) (t ε : ℝ) (hε : 0 < ε) :
    ∃ O : Set Plane, IsOpen O ∧ realLift c.parametrization t ∈ O ∧
      O ∩ c.trace = O ∩ (realLift c.parametrization '' Icc (t - ε) (t + ε)) := by
  let V : Set ParameterCircle := (fun s : ℝ => (s : ParameterCircle)) ''
    Ioo (t - ε) (t + ε)
  have hV : IsOpen V := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  obtain ⟨O, hO, heq⟩ := (jordanCurve_embedding c).isInducing.isOpen_iff.mp hV
  have hp : realLift c.parametrization t ∈ O := by
    change (t : ParameterCircle) ∈ c.parametrization ⁻¹' O
    rw [heq]
    exact ⟨t, ⟨by linarith, by linarith⟩, rfl⟩
  refine ⟨O, hO, hp, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hxO, u, hu⟩
    have huO : u ∈ c.parametrization ⁻¹' O := by simpa [hu] using hxO
    rw [heq] at huO
    obtain ⟨s, hs, hsu⟩ := huO
    exact ⟨hxO, s, ⟨hs.1.le, hs.2.le⟩, by simpa [realLift, hsu] using hu⟩
  · rintro x ⟨hxO, s, _, rfl⟩
    exact ⟨hxO, (s : ParameterCircle), rfl⟩

/-- Finite disjointness lets the curve neighborhood exclude every other
boundary component, without any local finiteness assumption on ambient space. -/
theorem boundary_subarc_neighborhood (R : PlanarRegion) (i : Fin R.boundaryCount)
    (t ε : ℝ) (hε : 0 < ε) :
    ∃ O : Set Plane, IsOpen O ∧ realLift (R.curve i).parametrization t ∈ O ∧
      O ∩ R.boundary =
        O ∩ (realLift (R.curve i).parametrization '' Icc (t - ε) (t + ε)) := by
  classical
  obtain ⟨N, hN, hpN, hNarc⟩ := curve_subarc_neighborhood (R.curve i) t ε hε
  let A : Set Plane := ⋃ j : {j : Fin R.boundaryCount // j ≠ i}, (R.curve j.val).trace
  have hA : IsClosed A := isClosed_iUnion_of_finite fun j => (compact_trace (R.curve j.val)).isClosed
  have hpA : realLift (R.curve i).parametrization t ∉ A := by
    intro hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    exact Set.disjoint_left.mp (R.disjoint_curves j.property.symm)
      (mem_range_self (t : ParameterCircle)) hj
  refine ⟨N \ A, hN.inter hA.isOpen_compl, ⟨hpN, hpA⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxb⟩
    have hxi : x ∈ (R.curve i).trace := by
      change x ∈ frontier R.domain at hxb
      rw [R.boundary_eq] at hxb
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxb
      by_cases hji : j = i
      · simpa [hji] using hj
      · exact (hx.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
    exact ⟨hx, (hNarc ▸ (show x ∈ N ∩ (R.curve i).trace from ⟨hx.1, hxi⟩)).2⟩
  · rintro ⟨hx, s, hs, hxs⟩
    refine ⟨hx, ?_⟩
    change x ∈ frontier R.domain
    rw [R.boundary_eq]
    exact mem_iUnion.mpr ⟨i, (s : ParameterCircle), hxs⟩

/-- This is a local graph of the entire actual frontier, rather than only
a graph of a selected parametrized subarc. -/
theorem boundaryLocalGraph : Expected.boundaryLocalGraph := by
  intro R i t
  obtain ⟨ε, a, hε, ha, hm⟩ := cornerProjection (R.curve i) t
  obtain ⟨G⟩ := projectedArcGraph_of_strictMono (R.curve i) t ε a hε hm
  obtain ⟨O, hO, hp, heq⟩ := boundary_subarc_neighborhood R i t ε hε
  refine ⟨ε, a, G, O, hε, ha, hO, hp, ?_, ?_, ?_⟩
  · exact hm ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  · exact hm ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  · rw [G.image_eq]
    exact heq

/-- A continuous graph admits an explicit ambient flattening. Extend its
transverse displacement by clamping the scalar coordinate to the graph interval,
then subtract that displacement. The projection is unchanged, so adding the
same displacement gives the continuous inverse. -/
theorem projectedArcGraph_flatten {c : RegularJordanCurve} {t ε : ℝ} {a : Plane}
    (ha : a ≠ 0) (G : ProjectedArcGraph c t ε a)
    (hends : inner ℝ a (realLift c.parametrization (t - ε)) ≤
      inner ℝ a (realLift c.parametrization (t + ε))) :
    ∃ e : Plane ≃ₜ Plane,
      (∀ x, inner ℝ a (e x) = inner ℝ a x) ∧
      ∀ x, e (G.map x) = (x.val / inner ℝ a a) • a := by
  let L := inner ℝ a (realLift c.parametrization (t - ε))
  let U := inner ℝ a (realLift c.parametrization (t + ε))
  let clamp : ℝ → Icc L U := projIcc L U hends
  let b : ℝ → Plane := fun s => G.map (clamp s) - ((clamp s).val / inner ℝ a a) • a
  have haa : inner ℝ a a ≠ 0 := (real_inner_self_pos.mpr ha).ne'
  have hclamp : Continuous clamp := continuous_projIcc
  have hb : Continuous b := by
    exact (G.map.continuous.comp hclamp).sub
      (((continuous_subtype_val.comp hclamp).div_const _).smul continuous_const)
  have hab : ∀ s, inner ℝ a (b s) = 0 := by
    intro s
    dsimp [b]
    rw [inner_sub_right, inner_smul_right, G.projection]
    field_simp [haa]
    ring
  let e : Plane ≃ₜ Plane :=
    { toFun := fun x => x - b (inner ℝ a x)
      invFun := fun x => x + b (inner ℝ a x)
      left_inv := by
        intro x
        simp only [inner_sub_right, hab, sub_zero]
        exact sub_add_cancel x _
      right_inv := by
        intro x
        simp only [inner_add_right, hab, add_zero]
        exact add_sub_cancel_right x _
      continuous_toFun := continuous_id.sub (hb.comp (continuous_const.inner continuous_id))
      continuous_invFun := continuous_id.add (hb.comp (continuous_const.inner continuous_id)) }
  refine ⟨e, ?_, ?_⟩
  · intro x
    change inner ℝ a (x - b (inner ℝ a x)) = inner ℝ a x
    rw [inner_sub_right, hab, sub_zero]
  · intro x
    change G.map x - b (inner ℝ a (G.map x)) = _
    rw [G.projection]
    have hx : clamp x.val = x := projIcc_of_mem hends x.property
    dsimp only [b]
    rw [hx]
    exact sub_sub_cancel _ _

/-- The standard half-plane has a basis of contractible convex neighborhoods. -/
theorem halfPlane_stronglyLocallyContractible : StronglyLocallyContractibleSpace HalfPlane := by
  apply P202.JordanBrouwer.convex_stronglyLocallyContractible
  intro x hx y hy u v hu hv huv
  change 0 ≤ (u • x + v • y) 1
  change 0 ≤ u * x 1 + v * y 1
  exact add_nonneg (mul_nonneg hu hx) (mul_nonneg hv hy)

/-- Local contractibility is deduced from the actual charts in the shared
surface interface; the implication does not assume any collar. -/
theorem surfaceLocallyContractible : Expected.surfaceLocallyContractible := by
  intro K B hcharts
  haveI : StronglyLocallyContractibleSpace HalfPlane := halfPlane_stronglyLocallyContractible
  haveI : StronglyLocallyContractibleSpace K := by
    apply P202.JordanBrouwer.local_stronglyLocallyContractible
    intro x
    obtain ⟨e, hx, _⟩ := hcharts x
    haveI : StronglyLocallyContractibleSpace e.target :=
      e.open_target.stronglyLocallyContractibleSpace
    have he : StronglyLocallyContractibleSpace e.source :=
      e.toHomeomorphSourceTarget.isOpenEmbedding.stronglyLocallyContractibleSpace
    exact ⟨e.source, e.open_source, hx, he⟩
  exact StronglyLocallyContractibleSpace.locallyContractible

/-- A connected set avoiding the frontier of an open set lies entirely
in that set or entirely outside its closure. -/
theorem connected_frontier_dichotomy {U A : Set Plane} (hU : IsOpen U)
    (hA : IsPreconnected A) (havoid : Disjoint A (frontier U)) :
    A ⊆ U ∨ A ⊆ (closure U)ᶜ := by
  apply IsPreconnected.subset_or_subset hU isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left subset_closure) ?_ hA
  intro x hx
  by_cases hxu : x ∈ U
  · exact Or.inl hxu
  · right
    intro hxcl
    exact disjoint_left.mp havoid hx (by rw [hU.frontier_eq]; exact ⟨hxcl, hxu⟩)

/-- Once a local graph divides a neighborhood into two connected sides,
the original one-sidedness hypothesis selects exactly one interior side.
The sides here are proof-stage inputs, not new region hypotheses. -/
theorem select_local_domain_side {U O A B : Set Plane} {p : Plane}
    (hU : IsOpen U) (hside : LocallyOneSided U) (hp : p ∈ frontier U)
    (hO : IsOpen O) (hpO : p ∈ O)
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hpartition : O \ frontier U = A ∪ B) :
    (A ⊆ U ∧ B ⊆ (closure U)ᶜ) ∨
      (B ⊆ U ∧ A ⊆ (closure U)ᶜ) := by
  have havoidA : Disjoint A (frontier U) := by
    rw [disjoint_left]
    intro x hx hxf
    exact ((hpartition.symm ▸ (show x ∈ A ∪ B from Or.inl hx)).2) hxf
  have havoidB : Disjoint B (frontier U) := by
    rw [disjoint_left]
    intro x hx hxf
    exact ((hpartition.symm ▸ (show x ∈ A ∪ B from Or.inr hx)).2) hxf
  have hAd := connected_frontier_dichotomy hU hA havoidA
  have hBd := connected_frontier_dichotomy hU hB havoidB
  obtain ⟨N, _, _, hNO, hinside, houtside⟩ := hside p hp O hO hpO
  obtain ⟨x, hxN, hxU⟩ := hinside.nonempty
  obtain ⟨y, hyN, hyout⟩ := houtside.nonempty
  have hxAB : x ∈ A ∪ B := by
    rw [← hpartition]
    exact ⟨hNO hxN, by rw [hU.frontier_eq]; exact fun hx => hx.2 hxU⟩
  have hyAB : y ∈ A ∪ B := by
    rw [← hpartition]
    exact ⟨hNO hyN, fun hy => hyout (frontier_subset_closure hy)⟩
  rcases hAd with hAi | hAo <;> rcases hBd with hBi | hBo
  · exfalso
    exact hyout (subset_closure (hyAB.elim (fun hy => hAi hy) (fun hy => hBi hy)))
  · exact Or.inl ⟨hAi, hBo⟩
  · exact Or.inr ⟨hBi, hAo⟩
  · exfalso
    exact (hxAB.elim (fun hx => hAo hx) (fun hx => hBo hx)) (subset_closure hxU)
theorem localSideSelection : Expected.localSideSelection := by
  intro U O A B p hU hside hp hO hpO hA hB hpartition
  exact select_local_domain_side hU hside hp hO hpO hA hB hpartition

/-- A local ambient flattening produces an actual half-plane chart, retaining
exactly the specified boundary. -/
theorem halfPlane_chart_of_ambient {K B V : Set Plane} (H : Plane ≃ₜ Plane)
    (hV : IsOpen V) (x : K) (hx : H x.val ∈ V)
    (hK : ∀ z ∈ V, H.symm z ∈ K ↔ 0 ≤ z 1)
    (hB : ∀ z ∈ V, H.symm z ∈ B ↔ z 1 = 0) :
    ∃ e : OpenPartialHomeomorph K HalfPlane,
      x ∈ e.source ∧ ∀ y ∈ e.source, (e y).val 1 = 0 ↔ y.val ∈ B := by
  classical
  let S : Set K := (H ∘ Subtype.val) ⁻¹' V
  let T : Set HalfPlane := Subtype.val ⁻¹' V
  have hS : IsOpen S := hV.preimage (H.continuous.comp continuous_subtype_val)
  have hT : IsOpen T := hV.preimage continuous_subtype_val
  have hSx : x ∈ S := hx
  have hpos : ∀ y : K, y ∈ S → 0 ≤ H y.val 1 := by
    intro y hy
    exact (hK (H y.val) hy).mp (by simpa using y.property)
  let F : K → HalfPlane := fun y => if hy : y ∈ S then ⟨H y.val, hpos y hy⟩ else ⟨0, by simp⟩
  let G : HalfPlane → K := fun z => if hz : z ∈ T then
    ⟨H.symm z.val, (hK z.val hz).mpr z.property⟩ else x
  have hF : ∀ y (hy : y ∈ S), (F y).val = H y.val := by
    intro y hy
    simp [F, hy]
  have hG : ∀ z (hz : z ∈ T), (G z).val = H.symm z.val := by
    intro z hz
    simp [G, hz]
  have hFT : ∀ y ∈ S, F y ∈ T := by
    intro y hy
    change (F y).val ∈ V
    rw [hF y hy]
    exact hy
  have hGS : ∀ z ∈ T, G z ∈ S := by
    intro z hz
    change H (G z).val ∈ V
    rw [hG z hz, H.apply_symm_apply]
    exact hz
  let e : OpenPartialHomeomorph K HalfPlane :=
    { toFun := F
      invFun := G
      source := S
      target := T
      map_source' := hFT
      map_target' := hGS
      left_inv' := by
        intro y hy
        apply Subtype.ext
        rw [hG (F y) (hFT y hy), hF y hy, H.symm_apply_apply]
      right_inv' := by
        intro z hz
        apply Subtype.ext
        rw [hF (G z) (hGS z hz), hG z hz, H.apply_symm_apply]
      open_source := hS
      open_target := hT
      continuousOn_toFun := by
        apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
        apply (H.continuous.comp continuous_subtype_val).continuousOn.congr
        intro y hy
        exact (hF y hy)
      continuousOn_invFun := by
        apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
        apply (H.symm.continuous.comp continuous_subtype_val).continuousOn.congr
        intro z hz
        exact (hG z hz) }
  refine ⟨e, hSx, ?_⟩
  intro y hy
  change (F y).val 1 = 0 ↔ y.val ∈ B
  rw [hF y hy]
  simpa using (hB (H y.val) hy).symm


/-- Projection and signed transverse coordinate in a nonzero direction. -/
def planeProjectionCoordinates (a : Plane) (ha : a ≠ 0) : Plane ≃ₜ Plane := by
  have hden : a 0 * a 0 + a 1 * a 1 ≠ 0 := by
    have hpos := real_inner_self_pos.mpr ha
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial] at hpos
    exact hpos.ne'
  have hden' : a 0 ^ 2 + a 1 ^ 2 ≠ 0 := by simpa only [pow_two] using hden
  let f : Plane → Plane := fun x => !₂[a 0 * x 0 + a 1 * x 1, a 0 * x 1 - a 1 * x 0]
  let g : Plane → Plane := fun y => !₂[(a 0 * y 0 - a 1 * y 1) / (a 0 * a 0 + a 1 * a 1),
    (a 1 * y 0 + a 0 * y 1) / (a 0 * a 0 + a 1 * a 1)]
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        ext i
        fin_cases i <;> dsimp [f, g] <;> field_simp [hden, hden'] <;> ring
      right_inv := by
        intro y
        ext i
        fin_cases i <;> dsimp [f, g] <;> field_simp [hden, hden'] <;> ring
      continuous_toFun := by
        apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
        apply continuous_pi
        intro i
        fin_cases i <;> fun_prop
      continuous_invFun := by
        apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
        apply continuous_pi
        intro i
        fin_cases i <;> fun_prop }

theorem planeProjectionCoordinates_apply (a : Plane) (ha : a ≠ 0) (x : Plane) :
    planeProjectionCoordinates a ha x =
      !₂[a 0 * x 0 + a 1 * x 1, a 0 * x 1 - a 1 * x 0] := rfl

@[simp] theorem planeProjectionCoordinates_first (a : Plane) (ha : a ≠ 0) (x : Plane) :
    planeProjectionCoordinates a ha x 0 = inner ℝ a x := by
  rw [planeProjectionCoordinates_apply, PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial]
  change a 0 * x 0 + a 1 * x 1 = x 0 * a 0 + x 1 * a 1
  ring

@[simp] theorem planeProjectionCoordinates_smul (a : Plane) (ha : a ≠ 0) (s : ℝ) :
    planeProjectionCoordinates a ha (s • a) = !₂[s * inner ℝ a a, 0] := by
  rw [planeProjectionCoordinates_apply, PiLp.inner_apply, Fin.sum_univ_two]
  ext i
  fin_cases i <;> simp [RCLike.inner_apply] <;> ring


/-- The local one-sidedness hypothesis and a flattened boundary yield the
actual closed half-plane chart, with either possible choice of the interior. -/
theorem boundary_chart_of_ambient {U V : Set Plane} (H : Plane ≃ₜ Plane)
    (hU : IsOpen U) (hside : LocallyOneSided U) (p : Plane)
    (hp : p ∈ frontier U) (hV : IsOpen V) (hpV : H p ∈ V)
    (hflat : ∀ z ∈ V, H.symm z ∈ frontier U ↔ z 1 = 0) :
    ∃ e : OpenPartialHomeomorph (closure U) HalfPlane,
      (⟨p, frontier_subset_closure hp⟩ : closure U) ∈ e.source ∧
      ∀ y ∈ e.source, (e y).val 1 = 0 ↔ y.val ∈ frontier U := by
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV (H p) hpV
  let W := Metric.ball (H p) r
  let A := H ⁻¹' (W ∩ {z : Plane | 0 < z 1})
  let B := H ⁻¹' (W ∩ {z : Plane | z 1 < 0})
  have hpW : H p ∈ W := Metric.mem_ball_self hr
  have hW : IsOpen W := Metric.isOpen_ball
  have hAp : IsPreconnected A := by
    apply H.isPreconnected_preimage.mpr
    exact ((convex_ball _ _).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage (EuclideanSpace.proj (1 : Fin 2)).toLinearMap)).isPreconnected
  have hBp : IsPreconnected B := by
    apply H.isPreconnected_preimage.mpr
    exact ((convex_ball _ _).inter
      ((convex_Iio (0 : ℝ)).linear_preimage (EuclideanSpace.proj (1 : Fin 2)).toLinearMap)).isPreconnected
  have hzero : ∀ z ∈ W, H.symm z ∈ frontier U ↔ z 1 = 0 :=
    fun z hz => hflat z (hrV hz)
  have hpartition : H ⁻¹' W \ frontier U = A ∪ B := by
    ext q
    constructor
    · rintro ⟨hqW, hqf⟩
      have hne : (H q) 1 ≠ 0 := by
        intro hz
        apply hqf
        simpa using (hzero (H q) hqW).mpr hz
      rcases lt_or_gt_of_ne hne with hn | hn
      · exact Or.inr ⟨hqW, hn⟩
      · exact Or.inl ⟨hqW, hn⟩
    · intro hq
      rcases hq with hq | hq
      · refine ⟨hq.1, ?_⟩
        intro hqf
        have hz : (H q) 1 = 0 := (hzero (H q) hq.1).mp (by simpa using hqf)
        exact (ne_of_gt hq.2) hz
      · refine ⟨hq.1, ?_⟩
        intro hqf
        have hz : (H q) 1 = 0 := (hzero (H q) hq.1).mp (by simpa using hqf)
        exact (ne_of_lt hq.2) hz
  obtain hsel | hsel := select_local_domain_side hU hside hp
    (hW.preimage H.continuous) hpW hAp hBp hpartition
  · have hK : ∀ z ∈ W, H.symm z ∈ closure U ↔ 0 ≤ z 1 := by
      intro z hz
      constructor
      · intro hzK
        by_contra hn
        exact hsel.2 (show H.symm z ∈ B by simpa [B] using And.intro hz (lt_of_not_ge hn)) hzK
      · intro hn
        rcases lt_or_eq_of_le hn with hpos | heq
        · apply subset_closure
          apply hsel.1
          simpa [A] using And.intro hz hpos
        · exact frontier_subset_closure ((hzero z hz).mpr heq.symm)
    exact halfPlane_chart_of_ambient H hW ⟨p, frontier_subset_closure hp⟩ hpW hK hzero
  · let J := Homeomorph.neg Plane
    let H' := H.trans J
    let W' := J ⁻¹' W
    have hW' : IsOpen W' := hW.preimage J.continuous
    have hpW' : H' p ∈ W' := by simpa [H', W', J] using hpW
    have hK : ∀ z ∈ W', H'.symm z ∈ closure U ↔ 0 ≤ z 1 := by
      intro z hz
      have hzW : -z ∈ W := hz
      change H.symm (-z) ∈ closure U ↔ 0 ≤ z 1
      constructor
      · intro hzK
        by_contra hn
        have hneg : 0 < (-z) 1 := by simpa using neg_pos.mpr (lt_of_not_ge hn)
        exact hsel.2 (show H.symm (-z) ∈ A by simpa [A] using And.intro hzW hneg) hzK
      · intro hn
        rcases lt_or_eq_of_le hn with hpos | heq
        · apply subset_closure
          apply hsel.1
          have hneg : (-z) 1 < 0 := by simpa using neg_neg_of_pos hpos
          simpa [B] using And.intro hzW hneg
        · apply frontier_subset_closure
          apply (hzero (-z) hzW).mpr
          simp [← heq]
    have hB : ∀ z ∈ W', H'.symm z ∈ frontier U ↔ z 1 = 0 := by
      intro z hz
      change H.symm (-z) ∈ frontier U ↔ z 1 = 0
      rw [hzero (-z) hz]
      simp
    exact halfPlane_chart_of_ambient H' hW' ⟨p, frontier_subset_closure hp⟩ hpW' hK hB

/-- Ordinary interior points have half-plane charts whose images stay
strictly above the chart boundary. -/
theorem interior_chart {U : Set Plane} (hU : IsOpen U) (p : Plane) (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph (closure U) HalfPlane,
      (⟨p, subset_closure hp⟩ : closure U) ∈ e.source ∧
      ∀ y ∈ e.source, (e y).val 1 = 0 ↔ y.val ∈ frontier U := by
  let q : Plane := !₂[0, 1]
  let H := Homeomorph.addRight (q - p)
  have hHp : H p = q := by change p + (q - p) = q; abel
  let V : Set Plane := H '' U ∩ {z : Plane | 0 < z 1}
  have hV : IsOpen V := (H.isOpenMap U hU).inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hpV : H p ∈ V := by
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    rw [hHp]
    change (0 : ℝ) < 1
    norm_num
  have hzU : ∀ z ∈ V, H.symm z ∈ U := by
    intro z hz
    rcases hz.1 with ⟨w, hw, rfl⟩
    simpa using hw
  have hK : ∀ z ∈ V, H.symm z ∈ closure U ↔ 0 ≤ z 1 := by
    intro z hz
    exact iff_of_true (subset_closure (hzU z hz)) (le_of_lt hz.2)
  have hB : ∀ z ∈ V, H.symm z ∈ frontier U ↔ z 1 = 0 := by
    intro z hz
    have hn : H.symm z ∉ frontier U := by
      rw [hU.frontier_eq]
      exact fun hw => hw.2 (hzU z hz)
    exact iff_of_false hn (ne_of_gt hz.2)
  exact halfPlane_chart_of_ambient H hV ⟨p, subset_closure hp⟩ hpV hK hB


/-- The actual region frontier admits ambient coordinates in which it is
exactly the horizontal axis. Both sides of a reflex corner are included. -/
theorem boundary_ambient_flattening (R : PlanarRegion) (i : Fin R.boundaryCount) (t : ℝ) :
    ∃ (H : Plane ≃ₜ Plane) (V : Set Plane),
      IsOpen V ∧ H (realLift (R.curve i).parametrization t) ∈ V ∧
      ∀ z ∈ V, H.symm z ∈ R.boundary ↔ z 1 = 0 := by
  obtain ⟨ε, a, G, O, hε, ha, hO, hpO, hLt, htU, hOG⟩ := boundaryLocalGraph R i t
  let p : Plane := realLift (R.curve i).parametrization t
  let L : ℝ := inner ℝ a (realLift (R.curve i).parametrization (t - ε))
  let U : ℝ := inner ℝ a (realLift (R.curve i).parametrization (t + ε))
  have hLU : L ≤ U := (hLt.trans htU).le
  obtain ⟨E, hEproj, hEgraph⟩ := projectedArcGraph_flatten ha G hLU
  let H : Plane ≃ₜ Plane := E.trans (planeProjectionCoordinates a ha)
  have hHproj : ∀ x, H x 0 = inner ℝ a x := by
    intro x
    exact (planeProjectionCoordinates_first a ha (E x)).trans (hEproj x)
  have hHgraph : ∀ x, H (G.map x) = !₂[x.val, 0] := by
    intro x
    change planeProjectionCoordinates a ha (E (G.map x)) = _
    rw [hEgraph, planeProjectionCoordinates_smul]
    have haa : inner ℝ a a ≠ 0 := (real_inner_self_pos.mpr ha).ne'
    rw [div_mul_cancel₀ _ haa]
  have hpG : p ∈ range G.map := by
    rw [G.image_eq]
    exact ⟨t, ⟨by linarith, by linarith⟩, rfl⟩
  have hHp : H p 1 = 0 := by
    obtain ⟨x, hx⟩ := hpG
    rw [← hx, hHgraph]
    rfl
  let V : Set Plane := H '' O ∩ {z | L < z 0 ∧ z 0 < U}
  have hV : IsOpen V := (H.isOpenMap O hO).inter
    ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const))
  have hpV : H p ∈ V := by
    refine ⟨⟨p, hpO, rfl⟩, ?_⟩
    change L < H p 0 ∧ H p 0 < U
    rw [hHproj]
    exact ⟨hLt, htU⟩
  refine ⟨H, V, hV, hpV, ?_⟩
  intro z hz
  have hzO : H.symm z ∈ O := by
    obtain ⟨x, hx, hxz⟩ := hz.1
    simpa only [← hxz, H.symm_apply_apply] using hx
  have hGiff : H.symm z ∈ R.boundary ↔ H.symm z ∈ range G.map := by
    have hh := congrArg (fun S : Set Plane => H.symm z ∈ S) hOG
    simpa only [mem_inter_iff, hzO, true_and] using (Iff.of_eq hh)
  rw [hGiff]
  constructor
  · rintro ⟨x, hx⟩
    have hh : H (G.map x) = z := by rw [hx, H.apply_symm_apply]
    rw [hHgraph] at hh
    simpa using (congrArg (fun v : Plane => v 1) hh).symm
  · intro hz0
    let x : Icc L U := ⟨z 0, hz.2.1.le, hz.2.2.le⟩
    refine ⟨x, H.injective ?_⟩
    rw [hHgraph, H.apply_symm_apply]
    ext j
    fin_cases j
    · rfl
    · exact hz0.symm

/-- The cone of strict transverse directions for a prescribed family of tangents. -/
theorem convex_strict_directions (T : Set Plane) :
    Convex ℝ {w : Plane | ∀ v ∈ T, 0 < inner ℝ w v} := by
  intro x hx y hy a b ha hb hab v hv
  simp only [inner_add_left, inner_smul_left]
  have hxp := hx v hv
  have hyp := hy v hv
  by_cases hapos : 0 < a
  · exact add_pos_of_pos_of_nonneg (mul_pos hapos hxp) (mul_nonneg hb hyp.le)
  · have haz : a = 0 := le_antisymm (not_lt.mp hapos) ha
    have hbpos : 0 < b := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha hxp.le) (mul_pos hbpos hyp)

/-- A smooth ambient transverse field is constructed by a partition of unity
from a cover of good constant directions. No field is assumed as region data. -/
theorem smooth_transverse_field_of_cover {ι : Type*} {B : Set Plane}
    (hB : IsClosed B) (U : ι → Set Plane) (hU : ∀ i, IsOpen (U i))
    (hcover : B ⊆ ⋃ i, U i) (w : ι → Plane) (T : Plane → Set Plane)
    (hgood : ∀ i x, x ∈ B → x ∈ U i → ∀ v ∈ T x, 0 < inner ℝ (w i) v) :
    ∃ F : Plane → Plane, ContDiff ℝ ∞ F ∧
      (∀ x ∈ B, ∀ v ∈ T x, 0 < inner ℝ (F x) v) ∧
      (∀ x ∈ B, ∀ v : Plane, (∀ i, x ∈ U i → w i = v) → F x = v) := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, Plane))
    hB U hU hcover
  let F : Plane → Plane := fun x => ∑ᶠ i, ρ i x • w i
  have hF : ContDiff ℝ ∞ F := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact ρ.contDiffAt_finsum (fun _ _ => contDiffAt_const)
  refine ⟨F, hF, ?_, ?_⟩
  · intro x hx
    apply ρ.finsum_smul_mem_convex hx (g := fun i _ => w i) _
      (convex_strict_directions (T x))
    intro i hi
    exact hgood i x hx (hρ i (subset_closure hi))
  · intro x hx v heq
    change (∑ᶠ i, ρ i x • w i) = v
    have hsum : (∑ᶠ i, ρ i x • w i) = ∑ᶠ i, ρ i x • v := by
      apply finsum_congr
      intro i
      by_cases hi : ρ i x = 0
      · simp [hi]
      · rw [heq i (hρ i (subset_closure hi))]
    rw [hsum, ← finsum_smul, ρ.sum_eq_one hx, one_smul]

/-- Agreement on a nondegenerate left interval determines the derivative at
its right endpoint whenever the two ambient derivatives exist. -/
theorem deriv_eq_of_eqOn_left {f g : ℝ → Plane} {t δ : ℝ}
    (hδ : 0 < δ) (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t)
    (he : EqOn f g (Icc (t - δ) t)) : deriv f t = deriv g t := by
  have ht : t ∈ Icc (t - δ) t := ⟨by linarith, le_rfl⟩
  have hu : UniqueDiffWithinAt ℝ (Icc (t - δ) t) t :=
    uniqueDiffOn_Icc (by linarith) t ht
  rw [← hf.derivWithin hu, ← hg.derivWithin hu]
  exact derivWithin_congr he (he ht)

/-- A smooth point of a canonical curve is regular. The nonzero derivative
comes from the actual one-sided extension; it is not an added hypothesis. -/
theorem regular_nonjoin_deriv_ne_zero (c : RegularJordanCurve) {t : ℝ}
    (ht : (t : ParameterCircle) ∉ c.joins) :
    deriv (realLift c.parametrization) t ≠ 0 := by
  obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hn⟩ := c.regular_joins t
  have hleft : DifferentiableAt ℝ l t :=
    ((hl.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).differentiableAt (by simp))
  have hcurve : DifferentiableAt ℝ (realLift c.parametrization) t :=
    (c.smooth_off_joins t ht).differentiableAt (by simp)
  rw [← deriv_eq_of_eqOn_left hδ hleft hcurve hel]
  exact hnl

/-- Every corner admits one fixed vector whose quarter-turn has strictly
positive scalar product with the true left normal on every nearby smooth arc.
This includes the center parameter when it is an extra smooth join. -/
theorem local_positive_projection_deriv (c : RegularJordanCurve) (t : ℝ) :
    ∃ (ε : ℝ) (a : Plane), 0 < ε ∧ a ≠ 0 ∧
      ∀ s ∈ Ioo (t - ε) (t + ε), (s : ParameterCircle) ∉ c.joins →
        0 < inner ℝ a (deriv (realLift c.parametrization) s) := by
  obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hn⟩ := c.regular_joins t
  obtain ⟨a, ha, hpl, hpr⟩ := common_projection_direction hnl hnr hn
  have hpos := (eventually_positive_projection_deriv hδ hl hpl).and
    (eventually_positive_projection_deriv hδ hr hpr)
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp hpos
  let ε := min δ η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; have := min_le_left δ η; linarith
  have hεη : ε < η := by dsimp [ε]; have := min_le_right δ η; linarith
  refine ⟨ε, a, hε, ha, ?_⟩
  intro s hs hsjoin
  have hsδ : s ∈ Ioo (t - δ) (t + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsp : 0 < inner ℝ a (deriv l s) ∧ 0 < inner ℝ a (deriv r s) := by
    apply hηball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  rcases lt_trichotomy s t with hst | rfl | hts
  · have he : deriv l s = deriv (realLift c.parametrization) s := by
      apply EqOn.deriv (s := Ioo (t - δ) t) _ isOpen_Ioo ⟨hsδ.1, hst⟩
      exact fun x hx => hel ⟨hx.1.le, hx.2.le⟩
    simpa only [he] using hsp.1
  · have hleft : DifferentiableAt ℝ l s :=
      ((hl.contDiffAt (isOpen_Ioo.mem_nhds hsδ)).differentiableAt (by simp))
    have hcurve : DifferentiableAt ℝ (realLift c.parametrization) s :=
      (c.smooth_off_joins s hsjoin).differentiableAt (by simp)
    simpa only [deriv_eq_of_eqOn_left hδ hleft hcurve hel] using hsp.1
  · have he : deriv r s = deriv (realLift c.parametrization) s := by
      apply EqOn.deriv (s := Ioo t (t + δ)) _ isOpen_Ioo ⟨hts, hsδ.2⟩
      exact fun x hx => her ⟨hx.1.le, hx.2.le⟩
    simpa only [he] using hsp.2

/-- Changing a real lift by a period does not change its derivative. -/
theorem realLift_deriv_eq_of_coe_eq (c : RegularJordanCurve) {s t : ℝ}
    (h : (s : ParameterCircle) = (t : ParameterCircle)) :
    deriv (realLift c.parametrization) s = deriv (realLift c.parametrization) t := by
  have he : (fun u : ℝ => realLift c.parametrization (s + u)) =
      (fun u : ℝ => realLift c.parametrization (t + u)) := by
    funext u
    simp only [realLift, AddCircle.coe_add, h]
  have hd := congrArg (fun f : ℝ → Plane => deriv f 0) he
  simpa only [deriv_comp_const_add, add_zero] using hd

/-- A fixed positive normal direction at every nearby smooth point of an
actual parametrized component, with an ambient open neighborhood as domain. -/
theorem ambient_positive_normal_direction (c : RegularJordanCurve) (t : ℝ) :
    ∃ (O : Set Plane) (w : Plane), IsOpen O ∧
      realLift c.parametrization t ∈ O ∧ w ≠ 0 ∧
      ∀ s : ℝ, realLift c.parametrization s ∈ O →
        (s : ParameterCircle) ∉ c.joins →
        0 < inner ℝ w (quarterTurn (deriv (realLift c.parametrization) s)) := by
  obtain ⟨ε, a, hε, ha, hpos⟩ := local_positive_projection_deriv c t
  let V : Set ParameterCircle := (fun s : ℝ => (s : ParameterCircle)) ''
    Ioo (t - ε) (t + ε)
  have hV : IsOpen V := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  obtain ⟨O, hO, heq⟩ := (jordanCurve_embedding c).isInducing.isOpen_iff.mp hV
  have hp : realLift c.parametrization t ∈ O := by
    change (t : ParameterCircle) ∈ c.parametrization ⁻¹' O
    rw [heq]
    exact ⟨t, ⟨by linarith, by linarith⟩, rfl⟩
  have hw : quarterTurn a ≠ 0 := by
    intro hzero
    have hself := quarterTurn_inner a a
    rw [hzero] at hself
    simp only [inner_zero_left] at hself
    exact ha (inner_self_eq_zero.mp hself.symm)
  refine ⟨O, quarterTurn a, hO, hp, hw, ?_⟩
  intro s hs hsjoin
  have hsv : (s : ParameterCircle) ∈ V := by
    rw [← heq]
    exact hs
  obtain ⟨u, hu, hus⟩ := hsv
  rw [quarterTurn_inner, ← realLift_deriv_eq_of_coe_eq c hus]
  apply hpos u hu
  simpa only [hus] using hsjoin

/-- The prescribed piecewise regular component admits a smooth ambient
vector field positively transverse to each of its given smooth arcs. -/
theorem curve_smooth_positive_transverse_field (c : RegularJordanCurve) :
    ∃ F : Plane → Plane, ContDiff ℝ ∞ F ∧
      ∀ s : ℝ, (s : ParameterCircle) ∉ c.joins →
        0 < inner ℝ (F (realLift c.parametrization s))
          (quarterTurn (deriv (realLift c.parametrization) s)) := by
  choose U w hU hpU hw hgood using ambient_positive_normal_direction c
  let T : Plane → Set Plane := fun x =>
    {v | ∃ s : ℝ, realLift c.parametrization s = x ∧
      (s : ParameterCircle) ∉ c.joins ∧
      v = quarterTurn (deriv (realLift c.parametrization) s)}
  have hcover : c.trace ⊆ ⋃ t : ℝ, U t := by
    rintro x ⟨u, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective u
    exact mem_iUnion.mpr ⟨s, hpU s⟩
  obtain ⟨F, hF, hFT, hconst⟩ := smooth_transverse_field_of_cover (compact_trace c).isClosed
    U hU hcover w T (by
      intro i x hx hxU v hv
      obtain ⟨s, hs, hsjoin, rfl⟩ := hv
      exact hgood i s (hs ▸ hxU) hsjoin)
  refine ⟨F, hF, ?_⟩
  intro s hsjoin
  exact hFT _ (mem_range_self (s : ParameterCircle)) _ ⟨s, rfl, hsjoin, rfl⟩

/-- Restriction of a two-sided boundary chart to a shorter closed positive
cylinder is a genuine collar, including openness of its lower image. -/
theorem boundaryCollar_of_bicollar {K B : Set Plane} (hB : IsCompact B)
    (hBK : B ⊆ K) {a : ℝ} (ha : 0 < a)
    (e : OpenPartialHomeomorph (B × ℝ) Plane)
    (hsource : e.source = univ ×ˢ Ioo (-a) a)
    (hzero : ∀ x : B, e (x, 0) = x.val)
    (hcarrier : ∀ z ∈ e.source, e z ∈ K ↔ 0 ≤ z.2)
    (hinterior : ∀ z ∈ e.source, 0 < z.2 → e z ∈ interior K) :
    Nonempty (BoundaryCollar K B) := by
  let b : ℝ := a / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [b]; linarith
  let f : B × unitInterval → B × ℝ := fun z => (z.1, b * (z.2 : ℝ))
  have hf : Continuous f := by fun_prop
  have hfs : ∀ z, f z ∈ e.source := by
    intro z
    rw [hsource]
    refine ⟨mem_univ _, ?_⟩
    have hz0 := z.2.property.1
    have hz1 := z.2.property.2
    change -a < b * (z.2 : ℝ) ∧ b * (z.2 : ℝ) < a
    constructor
    · exact (neg_lt_zero.mpr ha).trans_le (mul_nonneg hb.le hz0)
    · exact (mul_le_of_le_one_right hb.le hz1).trans_lt hba
  have hfk : ∀ z, e (f z) ∈ K := by
    intro z
    apply (hcarrier _ (hfs z)).2
    exact mul_nonneg hb.le z.2.property.1
  let g : C(B × unitInterval, K) :=
    ⟨fun z => ⟨e (f z), hfk z⟩,
      (e.continuousOn.comp_continuous hf hfs).subtype_mk _⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    have heq : f x = f y := e.injOn (hfs x) (hfs y) (congrArg Subtype.val hxy)
    refine Prod.ext (show x.1 = y.1 from congrArg (fun z : B × ℝ => z.1) heq) ?_
    apply Subtype.ext
    have htime := congrArg Prod.snd heq
    change b * (x.2 : ℝ) = b * (y.2 : ℝ) at htime
    exact mul_left_cancel₀ hb.ne' htime
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  refine ⟨{ boundary_subset := hBK
            map := g
            embedding := g.continuous.isClosedEmbedding hginj |>.isEmbedding
            at_zero := ?_
            positive_interior := ?_
            open_lower_image := ?_ }⟩
  · intro x
    change e (x, b * ((0 : unitInterval) : ℝ)) = x.val
    simpa using hzero x
  · intro x t ht
    exact hinterior _ (hfs (x, t)) (mul_pos hb ht)
  · let W : Set (B × ℝ) := univ ×ˢ Ioo (-a) b
    have hWopen : IsOpen W := isOpen_univ.prod isOpen_Ioo
    have hWsource : W ⊆ e.source := by
      intro z hz
      rw [hsource]
      exact ⟨mem_univ _, hz.2.1, hz.2.2.trans hba⟩
    have himage : g '' {z : B × unitInterval | (z.2 : ℝ) < 1} =
        Subtype.val ⁻¹' (e '' W) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨f z, ?_, rfl⟩
        refine ⟨mem_univ _, ?_, ?_⟩
        · have hs := hfs z
          rw [hsource] at hs
          exact hs.2.1
        · exact (mul_lt_of_lt_one_right hb hz)
      · rintro ⟨z, hzW, hzy⟩
        have hzs := hWsource hzW
        have hz0 : 0 ≤ z.2 := (hcarrier z hzs).1 (hzy ▸ y.property)
        let t : unitInterval := ⟨z.2 / b,
          div_nonneg hz0 hb.le, (div_le_one hb).2 hzW.2.2.le⟩
        refine ⟨(z.1, t), ?_, ?_⟩
        · exact (div_lt_one hb).2 hzW.2.2
        · apply Subtype.ext
          change e (z.1, b * (z.2 / b)) = y.val
          rw [mul_div_cancel₀ _ hb.ne']
          exact hzy
    rw [himage]
    exact (e.isOpen_image_of_subset_source hWopen hWsource).preimage continuous_subtype_val

/-- A continuous map that is locally a homeomorphism along its injective
compact zero section is a single open product chart for one uniform time. -/
theorem uniform_bicollarChart {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] [TopologicalSpace Y] [T2Space Y]
    (F : X × ℝ → Y) (hF : Continuous F)
    (hzero : Function.Injective (fun x => F (x, 0)))
    (hloc : ∀ x : X, ∃ e : OpenPartialHomeomorph (X × ℝ) Y,
      (x, 0) ∈ e.source ∧ ∀ z, e z = F z) :
    ∃ (a : ℝ) (e : OpenPartialHomeomorph (X × ℝ) Y), 0 < a ∧
      e.source = univ ×ˢ Ioo (-a) a ∧ ∀ z, e z = F z := by
  let S : Set (X × ℝ) := {p | ∃ e : OpenPartialHomeomorph (X × ℝ) Y,
    p ∈ e.source ∧ ∀ z, e z = F z}
  have hS : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro p ⟨e, hp, he⟩
    exact ⟨e.source, fun z hz => ⟨e, hz, he⟩, e.open_source, hp⟩
  have hSzero : univ ×ˢ ({0} : Set ℝ) ⊆ S := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    have ht' : t = 0 := ht
    subst t
    exact hloc x
  obtain ⟨U, V, _, hVopen, hU, hV, hUV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hS hSzero
  obtain ⟨b, hb, hball⟩ := Metric.isOpen_iff.mp hVopen 0 (hV (mem_singleton 0))
  have hl : IsLocalHomeomorphOn F (univ ×ˢ Ioo (-b) b) := by
    intro p hp
    have hpV : p.2 ∈ V := by
      apply hball
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hp.2
    obtain ⟨e, hpe, he⟩ := hUV ⟨hU (mem_univ _), hpV⟩
    exact ⟨e, hpe, (funext he).symm⟩
  have hlinj : ∀ x : X, ∃ U ∈ 𝓝 (x, (0 : ℝ)), Set.InjOn F U := by
    intro x
    obtain ⟨e, hx, he⟩ := hloc x
    refine ⟨e.source, e.open_source.mem_nhds hx, ?_⟩
    intro p hp q hq hpq
    apply e.injOn hp hq
    simpa only [he] using hpq
  obtain ⟨c, hc, hcinj⟩ :=
    D13Unified.Ch21.Collar.uniform_injective_near_zero F hF hzero hlinj
  let a := min b c
  have ha : 0 < a := lt_min hb hc
  have haB : univ ×ˢ Ioo (-a) a ⊆ (univ : Set X) ×ˢ Ioo (-b) b := by
    intro p hp
    exact ⟨mem_univ _, lt_of_le_of_lt (neg_le_neg (min_le_left b c)) hp.2.1,
      lt_of_lt_of_le hp.2.2 (min_le_left b c)⟩
  have haC : univ ×ˢ Ioo (-a) a ⊆ (univ : Set X) ×ˢ Ioo (-c) c := by
    intro p hp
    exact ⟨mem_univ _, lt_of_le_of_lt (neg_le_neg (min_le_right b c)) hp.2.1,
      lt_of_lt_of_le hp.2.2 (min_le_right b c)⟩
  obtain ⟨e, he, heF⟩ := D13Unified.Ch21.Collar.open_chart_of_injOn F
    (univ ×ˢ Ioo (-a) a) (isOpen_univ.prod isOpen_Ioo) (hl.mono haB) (hcinj.mono haC)
  exact ⟨a, e, ha, he, heF⟩

/-- Constant transverse translation of a projected graph is injective on its
entire vertical product, without differentiability of the graph. -/
theorem graph_translation_injOn {X : Type*} (γ : X → Plane) (S : Set X)
    (a w : Plane) (hprojection : Set.InjOn (fun x => inner ℝ a (γ x)) S)
    (haw : inner ℝ a w = 0) (hw : w ≠ 0) :
    Set.InjOn (fun z : X × ℝ => γ z.1 + z.2 • w) (S ×ˢ univ) := by
  intro x hx y hy hxy
  have hproj := congrArg (fun p : Plane => inner ℝ a p) hxy
  simp only [inner_add_right, inner_smul_right, haw, mul_zero, add_zero] at hproj
  have hbase : x.1 = y.1 := hprojection hx.1 hy.1 hproj
  apply Prod.ext hbase
  dsimp only at hxy
  rw [hbase] at hxy
  exact smul_left_injective ℝ hw (add_left_cancel hxy)

/-- At finitely many distinct points, smooth bumps can be chosen inside
prescribed open neighborhoods with mutually disjoint supports. Each bump is
identically one on a neighborhood of its own center. -/
theorem exists_disjoint_bumps {ι : Type*} [Finite ι] (p : ι → Plane)
    (hp : Function.Injective p) (O : ι → Set Plane) (hO : ∀ i, IsOpen (O i))
    (hcenter : ∀ i, p i ∈ O i) :
    ∃ f : ∀ i, ContDiffBump (p i),
      (∀ i, Function.support (f i) ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j))) := by
  classical
  obtain ⟨V, hV, hVdis⟩ := (Set.finite_range p).t2_separation
  have hneighborhood : ∀ i, ∃ r : ℝ, 0 < r ∧ Metric.ball (p i) r ⊆ O i ∩ V (p i) := by
    intro i
    exact Metric.isOpen_iff.mp ((hO i).inter (hV (p i)).2) (p i)
      ⟨hcenter i, (hV (p i)).1⟩
  choose r hr hball using hneighborhood
  let f : ∀ i, ContDiffBump (p i) := fun i =>
    ⟨r i / 2, r i, by linarith [hr i], by linarith [hr i]⟩
  refine ⟨f, ?_, ?_⟩
  · intro i x hx
    rw [(f i).support_eq] at hx
    exact (hball i hx).1
  · intro i j hij
    apply (hVdis (mem_range_self i) (mem_range_self j) (fun heq => hij (hp heq))).mono
    · intro x hx
      rw [(f i).support_eq] at hx
      exact (hball i hx).2
    · intro x hx
      rw [(f j).support_eq] at hx
      exact (hball j hx).2

/-- The actual compact region is a surface with its actual frontier as boundary,
including every noncuspidal corner and every ordinary interior point. -/
theorem regionSurface : ∀ R : PlanarRegion,
    IsSurfaceWithBoundary R.carrier R.boundary := by
  intro R x
  by_cases hxb : x.val ∈ R.boundary
  · have hxcurves : x.val ∈ ⋃ i, (R.curve i).trace := by
      rw [← R.boundary_eq]
      exact hxb
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxcurves
    obtain ⟨θ, hθ⟩ := hi
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective θ
    have hxt : realLift (R.curve i).parametrization t = x.val := by
      change (R.curve i).parametrization (t : ParameterCircle) = x.val
      rw [ht]
      exact hθ
    obtain ⟨H, V, hV, hpV, hflat⟩ := boundary_ambient_flattening R i t
    have hxV : H x.val ∈ V := by rw [← hxt]; exact hpV
    exact boundary_chart_of_ambient H R.open_domain R.one_sided x.val hxb hV hxV hflat
  · have hxU : x.val ∈ R.domain := by
      by_contra hn
      apply hxb
      rw [PlanarRegion.boundary, R.open_domain.frontier_eq]
      exact ⟨x.property, hn⟩
    exact interior_chart R.open_domain x.val hxU


/-- Local contractibility of the canonical region follows from its constructed charts. -/
theorem regionLocallyContractible (R : PlanarRegion) : LocallyContractibleSpace R.carrier :=
  surfaceLocallyContractible R.carrier R.boundary (regionSurface R)

/-- One-sided agreement also determines two existing ambient derivatives. -/
theorem deriv_eq_of_eventuallyEq_le {f g : ℝ → Plane} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t)
    (he : f =ᶠ[𝓝[≤] t] g) : deriv f t = deriv g t := by
  have hu := uniqueDiffWithinAt_Iic t
  rw [← hf.derivWithin hu, ← hg.derivWithin hu]
  exact he.derivWithin_eq (he.eq_of_nhdsWithin (by simp))

theorem deriv_eq_of_eventuallyEq_ge {f g : ℝ → Plane} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t)
    (he : f =ᶠ[𝓝[≥] t] g) : deriv f t = deriv g t := by
  have hu := uniqueDiffWithinAt_Ici t
  rw [← hf.derivWithin hu, ← hg.derivWithin hu]
  exact he.derivWithin_eq (he.eq_of_nhdsWithin (by simp))

/-- A fixed local projection is positive on every actual one-sided tangent,
including the two limiting tangents at corners. -/
theorem local_positive_oneSided_deriv (c : RegularJordanCurve) (t : ℝ) :
    ∃ (ε : ℝ) (a : Plane), 0 < ε ∧ a ≠ 0 ∧
      ∀ s ∈ Ioo (t - ε) (t + ε), ∀ (η : ℝ) (f : ℝ → Plane), 0 < η →
        DifferentiableAt ℝ f s →
        (EqOn f (realLift c.parametrization) (Icc (s - η) s) ∨
          EqOn f (realLift c.parametrization) (Icc s (s + η))) →
        0 < inner ℝ a (deriv f s) := by
  obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hn⟩ := c.regular_joins t
  obtain ⟨a, ha, hpl, hpr⟩ := common_projection_direction hnl hnr hn
  have hpos := (eventually_positive_projection_deriv hδ hl hpl).and
    (eventually_positive_projection_deriv hδ hr hpr)
  obtain ⟨ζ, hζ, hζball⟩ := Metric.mem_nhds_iff.mp hpos
  let ε := min δ ζ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; have := min_le_left δ ζ; linarith
  have hεζ : ε < ζ := by dsimp [ε]; have := min_le_right δ ζ; linarith
  refine ⟨ε, a, hε, ha, ?_⟩
  intro s hs η f hη hf he
  have hsδ : s ∈ Ioo (t - δ) (t + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsp : 0 < inner ℝ a (deriv l s) ∧ 0 < inner ℝ a (deriv r s) := by
    apply hζball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hls : DifferentiableAt ℝ l s :=
    (hl.contDiffAt (isOpen_Ioo.mem_nhds hsδ)).differentiableAt (by simp)
  have hrs : DifferentiableAt ℝ r s :=
    (hr.contDiffAt (isOpen_Ioo.mem_nhds hsδ)).differentiableAt (by simp)
  rcases he with he | he
  · have hef : f =ᶠ[𝓝[≤] s] realLift c.parametrization :=
      he.eventuallyEq_of_mem (Icc_mem_nhdsLE (by linarith))
    by_cases hst : s ≤ t
    · have heg : l =ᶠ[𝓝[≤] s] realLift c.parametrization :=
        hel.eventuallyEq_of_mem (Icc_mem_nhdsLE_of_mem ⟨hsδ.1, hst⟩)
      rw [deriv_eq_of_eventuallyEq_le hf hls (hef.trans heg.symm)]
      exact hsp.1
    · have heg : r =ᶠ[𝓝[≤] s] realLift c.parametrization :=
        (her.eventuallyEq_of_mem (Icc_mem_nhds (lt_of_not_ge hst) hsδ.2)).filter_mono nhdsWithin_le_nhds
      rw [deriv_eq_of_eventuallyEq_le hf hrs (hef.trans heg.symm)]
      exact hsp.2
  · have hef : f =ᶠ[𝓝[≥] s] realLift c.parametrization :=
      he.eventuallyEq_of_mem (Icc_mem_nhdsGE (by linarith))
    by_cases hst : t ≤ s
    · have heg : r =ᶠ[𝓝[≥] s] realLift c.parametrization :=
        her.eventuallyEq_of_mem (Icc_mem_nhdsGE_of_mem ⟨hst, hsδ.2⟩)
      rw [deriv_eq_of_eventuallyEq_ge hf hrs (hef.trans heg.symm)]
      exact hsp.2
    · have heg : l =ᶠ[𝓝[≥] s] realLift c.parametrization :=
        (hel.eventuallyEq_of_mem (Icc_mem_nhds hsδ.1 (lt_of_not_ge hst))).filter_mono nhdsWithin_le_nhds
      rw [deriv_eq_of_eventuallyEq_ge hf hls (hef.trans heg.symm)]
      exact hsp.1

theorem oneSidedCurveNormals_nonempty (c : RegularJordanCurve) (p : Plane)
    (hp : p ∈ c.trace) : (oneSidedCurveNormals c p).Nonempty := by
  obtain ⟨u, rfl⟩ := hp
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective u
  obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hn⟩ := c.regular_joins s
  refine ⟨quarterTurn (deriv l s), s, δ, l, hδ, rfl, ?_, Or.inl hel, rfl⟩
  exact (hl.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).differentiableAt (by simp)

/-- Each corner has a single ambient neighborhood and one constant direction
strictly transverse to every actual one-sided normal at every curve point there. -/
theorem ambient_positive_oneSided_direction (c : RegularJordanCurve) (t : ℝ) :
    ∃ (O : Set Plane) (w : Plane), IsOpen O ∧
      realLift c.parametrization t ∈ O ∧ w ≠ 0 ∧
      ∀ p ∈ O, ∀ v ∈ oneSidedCurveNormals c p, 0 < inner ℝ w v := by
  obtain ⟨ε, a, hε, ha, hpos⟩ := local_positive_oneSided_deriv c t
  let V : Set ParameterCircle := (fun s : ℝ => (s : ParameterCircle)) ''
    Ioo (t - ε) (t + ε)
  have hV : IsOpen V := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  obtain ⟨O, hO, heq⟩ := (jordanCurve_embedding c).isInducing.isOpen_iff.mp hV
  have hp : realLift c.parametrization t ∈ O := by
    change (t : ParameterCircle) ∈ c.parametrization ⁻¹' O
    rw [heq]
    exact ⟨t, ⟨by linarith, by linarith⟩, rfl⟩
  have hw : quarterTurn a ≠ 0 := by
    intro hzero
    have hself := quarterTurn_inner a a
    rw [hzero] at hself
    simp only [inner_zero_left] at hself
    exact ha (inner_self_eq_zero.mp hself.symm)
  refine ⟨O, quarterTurn a, hO, hp, hw, ?_⟩
  intro p hp v hv
  obtain ⟨s, η, f, hη, hsp, hf, he, rfl⟩ := hv
  have hsv : (s : ParameterCircle) ∈ V := by
    rw [← heq]
    change realLift c.parametrization s ∈ O
    rw [hsp]
    exact hp
  obtain ⟨u, hu, hus⟩ := hsv
  let g : ℝ → Plane := fun q => f (s - u + q)
  have hgs : DifferentiableAt ℝ g u := by
    have hc : DifferentiableAt ℝ (fun q : ℝ => s - u + q) u := by fun_prop
    apply DifferentiableAt.comp u _ hc
    simpa only [sub_add_cancel] using hf
  have hperiod : ∀ q : ℝ, realLift c.parametrization (s - u + q) =
      realLift c.parametrization q := by
    intro q
    simp only [realLift, AddCircle.coe_add, AddCircle.coe_sub, ← hus, sub_self, zero_add]
  have heg : EqOn g (realLift c.parametrization) (Icc (u - η) u) ∨
      EqOn g (realLift c.parametrization) (Icc u (u + η)) := by
    rcases he with he | he
    · left
      intro q hq
      change f (s - u + q) = _
      rw [he ⟨by linarith [hq.1], by linarith [hq.2]⟩, hperiod]
    · right
      intro q hq
      change f (s - u + q) = _
      rw [he ⟨by linarith [hq.1], by linarith [hq.2]⟩, hperiod]
  have hd : deriv g u = deriv f s := by
    dsimp only [g]
    rw [deriv_comp_const_add, sub_add_cancel]
  rw [quarterTurn_inner, ← hd]
  exact hpos u hu η g hη hgs heg

/-- A smooth ambient field is strictly transverse at all smooth arcs and at
both actual limiting tangents of every corner, and never vanishes on the curve. -/
theorem curve_smooth_oneSided_transverse_field (c : RegularJordanCurve) :
    ∃ F : Plane → Plane, ContDiff ℝ ∞ F ∧
      (∀ p ∈ c.trace, ∀ v ∈ oneSidedCurveNormals c p, 0 < inner ℝ (F p) v) ∧
      (∀ p ∈ c.trace, F p ≠ 0) := by
  choose U w hU hpU hw hgood using ambient_positive_oneSided_direction c
  have hcover : c.trace ⊆ ⋃ t : ℝ, U t := by
    rintro x ⟨u, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective u
    exact mem_iUnion.mpr ⟨s, hpU s⟩
  obtain ⟨F, hF, hFT, _⟩ := smooth_transverse_field_of_cover (compact_trace c).isClosed
    U hU hcover w (oneSidedCurveNormals c) (fun i x _ hxU => hgood i x hxU)
  refine ⟨F, hF, hFT, ?_⟩
  intro p hp hzero
  obtain ⟨v, hv⟩ := oneSidedCurveNormals_nonempty c p hp
  have hpositive := hFT p hp v hv
  exact (lt_irrefl (0 : ℝ)) (by simpa only [hzero, inner_zero_left] using hpositive)

/-- The independently parametrized, disjoint boundary components admit one
smooth ambient field transverse to all actual one-sided tangent normals. -/
theorem region_smooth_oneSided_transverse_field (R : PlanarRegion) :
    ∃ F : Plane → Plane, ContDiff ℝ ∞ F ∧
      (∀ (i : Fin R.boundaryCount) (p : Plane), p ∈ (R.curve i).trace →
        ∀ v ∈ oneSidedCurveNormals (R.curve i) p, 0 < inner ℝ (F p) v) ∧
      (∀ p ∈ R.boundary, F p ≠ 0) := by
  classical
  choose O w hO hpO hw hgood using fun (i : Fin R.boundaryCount) (t : ℝ) =>
    ambient_positive_oneSided_direction (R.curve i) t
  let A (i : Fin R.boundaryCount) : Set Plane :=
    ⋃ j : {j : Fin R.boundaryCount // j ≠ i}, (R.curve j.val).trace
  have hA : ∀ i, IsClosed (A i) := fun i => isClosed_iUnion_of_finite
    (fun j => (compact_trace (R.curve j.val)).isClosed)
  let U (z : Fin R.boundaryCount × ℝ) : Set Plane := O z.1 z.2 \ A z.1
  have hU : ∀ z, IsOpen (U z) := fun z => (hO z.1 z.2).inter (hA z.1).isOpen_compl
  have htrace_avoid : ∀ i p, p ∈ (R.curve i).trace → p ∉ A i := by
    intro i p hp hmem
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    exact disjoint_left.mp (R.disjoint_curves j.property.symm) hp hj
  have hcover : R.boundary ⊆ ⋃ z, U z := by
    intro p hp
    change p ∈ frontier R.domain at hp
    rw [R.boundary_eq] at hp
    obtain ⟨i, u, rfl⟩ := mem_iUnion.mp hp
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective u
    exact mem_iUnion.mpr ⟨(i, s), hpO i s,
      htrace_avoid i _ (mem_range_self (s : ParameterCircle))⟩
  let T : Plane → Set Plane := fun p => ⋃ i, oneSidedCurveNormals (R.curve i) p
  have hgoodU : ∀ z p, p ∈ R.boundary → p ∈ U z → ∀ v ∈ T p,
      0 < inner ℝ (w z.1 z.2) v := by
    intro z p hp hpU v hv
    obtain ⟨i, hvi⟩ := mem_iUnion.mp hv
    have hpi : p ∈ (R.curve i).trace := by
      obtain ⟨s, η, f, hη, hsp, hf, he, hv⟩ := hvi
      exact ⟨(s : ParameterCircle), hsp⟩
    have hi : i = z.1 := by
      by_contra hne
      exact hpU.2 (mem_iUnion.mpr ⟨⟨i, hne⟩, hpi⟩)
    subst i
    exact hgood z.1 z.2 p hpU.1 v hvi
  obtain ⟨F, hF, hFT, _⟩ := smooth_transverse_field_of_cover isClosed_frontier
    U hU hcover (fun z => w z.1 z.2) T hgoodU
  have hFi : ∀ i p, p ∈ (R.curve i).trace →
      ∀ v ∈ oneSidedCurveNormals (R.curve i) p, 0 < inner ℝ (F p) v := by
    intro i p hp v hv
    apply hFT p _ v (mem_iUnion.mpr ⟨i, hv⟩)
    change p ∈ frontier R.domain
    rw [R.boundary_eq]
    exact mem_iUnion.mpr ⟨i, hp⟩
  refine ⟨F, hF, hFi, ?_⟩
  intro p hp hzero
  change p ∈ frontier R.domain at hp
  rw [R.boundary_eq] at hp
  obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
  obtain ⟨v, hv⟩ := oneSidedCurveNormals_nonempty (R.curve i) p hpi
  have hpositive := hFi i p hpi v hv
  exact (lt_irrefl (0 : ℝ)) (by simpa only [hzero, inner_zero_left] using hpositive)

/-- The constructed field tests the actual derivatives of all prescribed
smooth arcs and is nonzero even at the finitely many joins. -/
theorem region_smooth_transverse_field (R : PlanarRegion) :
    ∃ F : Plane → Plane, ContDiff ℝ ∞ F ∧
      (∀ (i : Fin R.boundaryCount) (s : ℝ), (s : ParameterCircle) ∉ (R.curve i).joins →
        0 < inner ℝ (F (realLift (R.curve i).parametrization s))
          (quarterTurn (deriv (realLift (R.curve i).parametrization) s))) ∧
      (∀ p ∈ R.boundary, F p ≠ 0) := by
  obtain ⟨F, hF, hFi, hne⟩ := region_smooth_oneSided_transverse_field R
  refine ⟨F, hF, ?_, hne⟩
  intro i s hs
  apply hFi i _ (mem_range_self (s : ParameterCircle))
  refine ⟨s, 1, realLift (R.curve i).parametrization, zero_lt_one, rfl, ?_,
    Or.inl (fun _ _ => rfl), rfl⟩
  exact ((R.curve i).smooth_off_joins s hs).differentiableAt (by simp)

/-- Finite circle joins leave a smooth real parameter in every open interval. -/
theorem exists_nonjoin_in_Ioo (c : RegularJordanCurve) {a b : ℝ} (hab : a < b) :
    ∃ s ∈ Ioo a b, (s : ParameterCircle) ∉ c.joins := by
  classical
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let d := min b (a + 1)
  have had : a < d := lt_min hab (by linarith)
  by_contra h
  have hall : ∀ s ∈ Ioo a d, (s : ParameterCircle) ∈ c.joins := by
    intro s hs
    by_contra hsj
    exact h ⟨s, ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩, hsj⟩
  have hfinite : (Ioo a d).Finite := Set.Finite.of_injOn
    (f := fun s : ℝ => (s : ParameterCircle)) hall (by
      intro x hx y hy hxy
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        ⟨hx.1.le, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
        ⟨hy.1.le, lt_of_lt_of_le hy.2 (min_le_right _ _)⟩).mp hxy)
    c.joins.finite_toSet
  exact (Set.Ioo_infinite had) hfinite

theorem dense_nonjoin_parameters (c : RegularJordanCurve) :
    Dense {s : ℝ | (s : ParameterCircle) ∉ c.joins} := by
  rw [dense_iff_exists_between]
  intro a b hab
  obtain ⟨s, hs, hsj⟩ := exists_nonjoin_in_Ioo c hab
  exact ⟨s, hsj, hs.1, hs.2⟩

/-- A normal ray enters the specified actual set for all sufficiently small
positive distances. This is the pointwise test used in HasSideOnLeft. -/
def NormalRayInto (A : Set Plane) (c : RegularJordanCurve) (t σ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
    realLift c.parametrization t +
      r • (σ • quarterTurn (deriv (realLift c.parametrization) t)) ∈ A

theorem normalRayInto_disjoint {A B : Set Plane} {c : RegularJordanCurve} {t σ : ℝ}
    (hd : Disjoint A B) (hA : NormalRayInto A c t σ) (hB : NormalRayInto B c t σ) : False := by
  obtain ⟨ε, hε, hA⟩ := hA
  obtain ⟨η, hη, hB⟩ := hB
  have hsmall : 0 < min ε η / 2 := by positivity
  exact disjoint_left.mp hd
    (hA _ hsmall (by have := min_le_left ε η; linarith))
    (hB _ hsmall (by have := min_le_right ε η; linarith))

theorem normal_sign_unique_of_disjoint {A B : Set Plane} {c : RegularJordanCurve}
    {t σ τ : ℝ} (hd : Disjoint A B) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (hσA : NormalRayInto A c t σ) (hτB : NormalRayInto B c t (-τ)) : σ = τ := by
  rcases hσ with hσ | hσ <;> rcases hτ with hτ | hτ
  · exact hσ.trans hτ.symm
  · exfalso
    apply normalRayInto_disjoint hd hσA
    simpa only [hσ, hτ, neg_neg] using hτB
  · exfalso
    apply normalRayInto_disjoint hd hσA
    simpa only [hσ, hτ] using hτB
  · exact hσ.trans hτ.symm

/-- Locally consistent signs across every join determine one sign on the
entire prescribed component. No global orientation is assumed in this helper. -/
theorem orientation_of_local_normal_signs {A B : Set Plane} (c : RegularJordanCurve)
    (hd : Disjoint A B)
    (hlocal : ∀ t : ℝ, ∃ (U : Set ℝ) (σ : ℝ), IsOpen U ∧ t ∈ U ∧
      (σ = 1 ∨ σ = -1) ∧ ∀ s ∈ U, (s : ParameterCircle) ∉ c.joins →
        NormalRayInto A c s σ ∧ NormalRayInto B c s (-σ)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      HasSideOnLeft A c σ ∧ HasSideOnLeft B c (-σ) := by
  choose U σ hU htU hσ hside using hlocal
  have hloc : IsLocallyConstant σ := by
    apply (IsLocallyConstant.iff_exists_open σ).mpr
    intro t
    refine ⟨U t, hU t, htU t, ?_⟩
    intro u hut
    obtain ⟨s, hsU, hsjoin⟩ := (dense_nonjoin_parameters c).inter_open_nonempty
      (U u ∩ U t) ((hU u).inter (hU t)) ⟨u, htU u, hut⟩
    exact normal_sign_unique_of_disjoint hd (hσ u) (hσ t)
      (hside u s hsU.1 hsjoin).1 (hside t s hsU.2 hsjoin).2
  have hconst : ∀ t : ℝ, σ t = σ 0 := fun t =>
    hloc.apply_eq_of_preconnectedSpace t 0
  refine ⟨σ 0, hσ 0, ?_, ?_⟩
  · intro s hsjoin
    simpa only [hconst s, NormalRayInto] using (hside s s (htU s) hsjoin).1
  · intro s hsjoin
    simpa only [hconst s, NormalRayInto] using (hside s s (htU s) hsjoin).2

/-- The disjoint union of the prescribed parameter circles maps onto the
actual region frontier, in its ordinary subspace topology. -/
def boundaryParameterMap (R : PlanarRegion) :
    C((Σ _ : Fin R.boundaryCount, ParameterCircle), R.boundary) where
  toFun z := ⟨(R.curve z.1).parametrization z.2, by
    change (R.curve z.1).parametrization z.2 ∈ frontier R.domain
    rw [R.boundary_eq]
    exact mem_iUnion.mpr ⟨z.1, mem_range_self z.2⟩⟩
  continuous_toFun := by
    apply continuous_sigma
    intro i
    exact (R.curve i).parametrization.continuous.subtype_mk _

 theorem boundaryParameterMap_bijective (R : PlanarRegion) :
    Function.Bijective (boundaryParameterMap R) := by
  constructor
  · rintro ⟨i, s⟩ ⟨j, t⟩ heq
    have heqval : (R.curve i).parametrization s = (R.curve j).parametrization t :=
      congrArg Subtype.val heq
    by_cases hij : i = j
    · subst j
      have hst := (R.curve i).injective heqval
      subst t
      rfl
    · exfalso
      apply disjoint_left.mp (R.disjoint_curves hij) (mem_range_self s)
      rw [heqval]
      exact mem_range_self t
  · intro p
    have hp : p.val ∈ ⋃ i, (R.curve i).trace := by
      rw [← R.boundary_eq]
      exact p.property
    obtain ⟨i, q, hq⟩ := mem_iUnion.mp hp
    exact ⟨⟨i, q⟩, Subtype.ext hq⟩

/-- This is an actual homeomorphism with the full frontier; finite disjointness
and compactness supply the inverse continuity. -/
def boundaryParameterHomeomorph (R : PlanarRegion) :
    (Σ _ : Fin R.boundaryCount, ParameterCircle) ≃ₜ R.boundary := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact (boundaryParameterMap R).continuous.isClosedEmbedding
    (boundaryParameterMap_bijective R).injective |>.isEmbedding.toHomeomorphOfSurjective
      (boundaryParameterMap_bijective R).surjective

theorem curve_derivative_periodic (c : RegularJordanCurve) :
    Function.Periodic (deriv (realLift c.parametrization)) 1 := by
  have hf : Function.Periodic (realLift c.parametrization) 1 := by
    intro t
    simp [realLift, AddCircle.coe_add_period]
  intro t
  rw [← deriv_comp_add_const]
  exact congrArg (fun f : ℝ → Plane => deriv f t) (funext hf)

def curveTangent (c : RegularJordanCurve) : ParameterCircle → Plane :=
  (curve_derivative_periodic c).lift

@[simp] theorem curveTangent_coe (c : RegularJordanCurve) (t : ℝ) :
    curveTangent c (t : ParameterCircle) = deriv (realLift c.parametrization) t := rfl

theorem right_extension_deriv {f r : ℝ → Plane} {t δ : ℝ}
    (hδ : 0 < δ) (hf : DifferentiableAt ℝ f t)
    (hr : ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)))
    (heq : EqOn r f (Icc t (t + δ))) : deriv f t = deriv r t := by
  have ht : t ∈ Icc t (t + δ) := ⟨le_rfl, by linarith⟩
  have hu := (uniqueDiffOn_Icc (show t < t + δ by linarith)).uniqueDiffWithinAt ht
  have hrt : DifferentiableAt ℝ r t :=
    ((hr t ⟨by linarith, by linarith⟩).contDiffAt
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).differentiableAt (by simp)
  rw [← hf.derivWithin hu, ← hrt.derivWithin hu]
  exact (derivWithin_congr heq (heq ht)).symm

theorem curve_derivative_ne_zero (c : RegularJordanCurve) (t : ℝ)
    (ht : (t : ParameterCircle) ∉ c.joins) :
    deriv (realLift c.parametrization) t ≠ 0 := by
  obtain ⟨δ, l, r, hδ, _, hr, _, her, _, hnr, _⟩ := c.regular_joins t
  rw [right_extension_deriv hδ ((c.smooth_off_joins t ht).differentiableAt (by simp)) hr her]
  exact hnr

/-- Strict limiting transversality at one actual lifted join, retaining both
one-sided smooth extensions and their agreement with the original curve. -/
def HasStrictJoinTransversality (c : RegularJordanCurve) (q : ParameterCircle) (w : Plane) : Prop :=
  ∃ (t δ : ℝ) (l r : ℝ → Plane), (t : ParameterCircle) = q ∧ 0 < δ ∧
    ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)) ∧
    ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)) ∧
    EqOn l (realLift c.parametrization) (Icc (t - δ) t) ∧
    EqOn r (realLift c.parametrization) (Icc t (t + δ)) ∧
    0 < inner ℝ w (quarterTurn (deriv l t)) ∧
    0 < inner ℝ w (quarterTurn (deriv r t))

theorem local_curve_normal (c : RegularJordanCurve) (q : ParameterCircle) :
    ∃ (w : Plane) (O : Set Plane), w ≠ 0 ∧ IsOpen O ∧ c.parametrization q ∈ O ∧
      (∀ s : ℝ, c.parametrization (s : ParameterCircle) ∈ O →
        (s : ParameterCircle) ∉ c.joins →
        0 < inner ℝ w (quarterTurn (deriv (realLift c.parametrization) s))) ∧
      HasStrictJoinTransversality c q w := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨δ, l, r, hδ, hl, hr, hel, her, hnl, hnr, hn⟩ := c.regular_joins t
  obtain ⟨a, ha, hal, har⟩ := common_projection_direction hnl hnr hn
  have hnhds : ∀ᶠ s in 𝓝 t, s ∈ Ioo (t - δ) (t + δ) ∧
      0 < inner ℝ a (deriv l s) ∧ 0 < inner ℝ a (deriv r s) :=
    (show ∀ᶠ s in 𝓝 t, s ∈ Ioo (t - δ) (t + δ) from
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩).and
      ((eventually_positive_projection_deriv hδ hl hal).and
        (eventually_positive_projection_deriv hδ hr har))
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let ε := η / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgood : ∀ s ∈ Icc (t - ε) (t + ε), (s : ParameterCircle) ∉ c.joins →
      0 < inner ℝ a (deriv (realLift c.parametrization) s) := by
    intro s hs hsj
    have hsη : s ∈ Metric.ball t η := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      dsimp [ε] at hs
      constructor <;> linarith [hs.1, hs.2]
    obtain ⟨hsδ, hsl, hsr⟩ := hball hsη
    rcases lt_trichotomy s t with hst | rfl | hts
    · have heq : deriv l s = deriv (realLift c.parametrization) s :=
        (hel.mono (show Ioo (t - δ) t ⊆ Icc (t - δ) t from Ioo_subset_Icc_self)).deriv
          isOpen_Ioo ⟨hsδ.1, hst⟩
      rwa [heq] at hsl
    · have heq := right_extension_deriv hδ
        ((c.smooth_off_joins s hsj).differentiableAt (by simp)) hr her
      rwa [← heq] at hsr
    · have heq : deriv r s = deriv (realLift c.parametrization) s :=
        (her.mono (show Ioo t (t + δ) ⊆ Icc t (t + δ) from Ioo_subset_Icc_self)).deriv
          isOpen_Ioo ⟨hts, hsδ.2⟩
      rwa [heq] at hsr
  obtain ⟨O, hO, hpO, heq⟩ := curve_subarc_neighborhood c t ε hε
  refine ⟨quarterTurn a, O, ?_, hO, hpO, ?_, ?_⟩
  · intro hz
    have := quarterTurn_inner a a
    rw [hz, inner_zero_left] at this
    exact ha ((inner_self_eq_zero).mp this.symm)
  · intro s hsO hsj
    have hs : c.parametrization (s : ParameterCircle) ∈
        O ∩ (realLift c.parametrization '' Icc (t - ε) (t + ε)) := by
      rw [← heq]
      exact ⟨hsO, mem_range_self _⟩
    obtain ⟨u, hu, hus⟩ := hs.2
    have hcircle : (u : ParameterCircle) = (s : ParameterCircle) := c.injective hus
    have htangent : deriv (realLift c.parametrization) u =
        deriv (realLift c.parametrization) s := by
      change curveTangent c (u : ParameterCircle) = curveTangent c (s : ParameterCircle)
      rw [hcircle]
    rw [quarterTurn_inner, ← htangent]
    exact hgood u hu (hcircle ▸ hsj)
  · exact ⟨t, δ, l, r, rfl, hδ, hl, hr, hel, her,
      by simpa only [quarterTurn_inner] using hal,
      by simpa only [quarterTurn_inner] using har⟩

theorem disjoint_bump_zero {ι : Type*} {p : ι → Plane}
    (f : ∀ i, ContDiffBump (p i))
    (hdis : Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j))))
    {i j : ι} {x : Plane} (hi : f i x ≠ 0) (hij : j ≠ i) : f j x = 0 := by
  by_contra hj
  exact Set.disjoint_left.mp (hdis hij) hj hi

/-- The actual corner hypotheses yield a continuous transversal on the given
parameter circle, smooth away from the prescribed finite joins and locally
constant at each join. It is constructed from finite disjoint smooth bumps. -/
theorem curve_transverse_field (c : RegularJordanCurve) :
    ∃ W : C(ParameterCircle, Plane),
      (∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
        ContDiffAt ℝ ∞ (realLift W) t ∧
          0 < inner ℝ (W (t : ParameterCircle))
            (quarterTurn (deriv (realLift c.parametrization) t))) ∧
      ∀ q ∈ c.joins, ∃ w : Plane, w ≠ 0 ∧ W =ᶠ[𝓝 q] (fun _ => w) ∧
        HasStrictJoinTransversality c q w := by
  classical
  let J := ↥c.joins
  let p : J → Plane := fun j => c.parametrization j.val
  have hp : Function.Injective p := by
    intro i j hij
    exact Subtype.ext (c.injective hij)
  choose v O hv hO hpO hgood hstrict using fun j : J => local_curve_normal c j.val
  obtain ⟨f, hfO, hfdis⟩ := exists_disjoint_bumps p hp O hO hpO
  let W : ParameterCircle → Plane := fun q =>
    (∑ j : J, f j (c.parametrization q) • v j) +
      (1 - ∑ j : J, f j (c.parametrization q)) • quarterTurn (curveTangent c q)
  have hsingle : ∀ (i : J) (q : ParameterCircle), f i (c.parametrization q) ≠ 0 →
      W q = f i (c.parametrization q) • v i +
        (1 - f i (c.parametrization q)) • quarterTurn (curveTangent c q) := by
    intro i q hi
    have hother : ∀ j : J, j ≠ i → f j (c.parametrization q) = 0 :=
      fun j hji => disjoint_bump_zero f hfdis hi hji
    dsimp [W]
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · intro b _ hbi
      exact hother b hbi
    · simp
    · intro b _ hbi
      simp [hother b hbi]
    · simp
  have hat_join : ∀ q ∈ c.joins, ∃ w : Plane, w ≠ 0 ∧ W =ᶠ[𝓝 q] (fun _ => w) ∧
      HasStrictJoinTransversality c q w := by
    intro q hq
    let i : J := ⟨q, hq⟩
    have hfi : (fun q' : ParameterCircle => f i (c.parametrization q')) =ᶠ[𝓝 q] 1 :=
      (f i).eventuallyEq_one.comp_tendsto c.parametrization.continuous.continuousAt
    refine ⟨v i, hv i, ?_, hstrict i⟩
    filter_upwards [hfi] with q' hq'
    rw [hsingle i q' (by rw [hq']; exact one_ne_zero), hq']
    simp
  have hturn : ContDiff ℝ ∞ quarterTurn := by
    apply contDiff_euclidean.mpr
    intro i
    fin_cases i
    · simpa [quarterTurn] using
        ((contDiff_euclidean.mp (contDiff_id : ContDiff ℝ ∞ (fun v : Plane => v))) (1 : Fin 2)).neg
    · simpa [quarterTurn] using
        ((contDiff_euclidean.mp (contDiff_id : ContDiff ℝ ∞ (fun v : Plane => v))) (0 : Fin 2))
  have hsmooth : ∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
      ContDiffAt ℝ ∞ (fun s : ℝ => W (s : ParameterCircle)) t := by
    intro t ht
    have hcurve := c.smooth_off_joins t ht
    have htangent : ContDiffAt ℝ ∞ (deriv (realLift c.parametrization)) t :=
      hcurve.derivWithin (by simp)
    have hbump : ∀ j : J, ContDiffAt ℝ ∞
        (fun s : ℝ => f j (realLift c.parametrization s)) t :=
      fun j => (f j).contDiff.contDiffAt.comp t hcurve
    have hsum : ContDiffAt ℝ ∞
        (fun s : ℝ => ∑ j : J, f j (realLift c.parametrization s)) t :=
      ContDiffAt.sum (fun j _ => hbump j)
    exact (ContDiffAt.sum (fun j _ => (hbump j).smul contDiffAt_const)).add
      ((contDiffAt_const.sub hsum).smul (hturn.contDiffAt.comp t htangent))
  have hcontinuous : Continuous W := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases ht : (t : ParameterCircle) ∈ c.joins
    · obtain ⟨w, _, hw, _⟩ := hat_join (t : ParameterCircle) ht
      have hw' := hw.comp_tendsto (continuous_quotient_mk'.continuousAt (x := t))
      exact continuousAt_const.congr_of_eventuallyEq hw'
    · exact (hsmooth t ht).continuousAt
  refine ⟨⟨W, hcontinuous⟩, ?_, hat_join⟩
  intro t ht
  refine ⟨hsmooth t ht, ?_⟩
  by_cases hi : ∃ i : J, f i (realLift c.parametrization t) ≠ 0
  · obtain ⟨i, hi⟩ := hi
    have hfi : 0 < f i (realLift c.parametrization t) :=
      lt_of_le_of_ne (f i).nonneg hi.symm
    have hgoodi := hgood i t (hfO i hi) ht
    change 0 < inner ℝ (W (t : ParameterCircle)) _
    rw [hsingle i _ hi, inner_add_left, inner_smul_left, inner_smul_left,
      curveTangent_coe, quarterTurn_inner]
    exact add_pos_of_pos_of_nonneg (mul_pos hfi hgoodi)
      (mul_nonneg (sub_nonneg.mpr (f i).le_one) (real_inner_self_nonneg))
  · have hz : ∀ i : J, f i (realLift c.parametrization t) = 0 := by simpa using hi
    change 0 < inner ℝ (W (t : ParameterCircle)) _
    dsimp [W]
    simp only [show ∀ i : J, f i (c.parametrization (t : ParameterCircle)) = 0 from hz,
      zero_smul, Finset.sum_const_zero, sub_zero, one_smul, zero_add,
      curveTangent_coe, quarterTurn_inner]
    exact real_inner_self_pos.mpr (curve_derivative_ne_zero c t ht)

theorem strict_projection_from_extensions {c : RegularJordanCurve} {t δ : ℝ}
    {l r : ℝ → Plane} {a : Plane} (hδ : 0 < δ)
    (hl : ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)))
    (hr : ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)))
    (hel : EqOn l (realLift c.parametrization) (Icc (t - δ) t))
    (her : EqOn r (realLift c.parametrization) (Icc t (t + δ)))
    (hpl : 0 < inner ℝ a (deriv l t)) (hpr : 0 < inner ℝ a (deriv r t)) :
    ∃ ε : ℝ, 0 < ε ∧ StrictMonoOn
      (fun s => inner ℝ a (realLift c.parametrization s)) (Icc (t - ε) (t + ε)) := by
  have hpos := (eventually_positive_projection_deriv hδ hl hpl).and
    (eventually_positive_projection_deriv hδ hr hpr)
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp hpos
  let ε := min δ η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; have := min_le_left δ η; linarith
  have hεη : ε < η := by dsimp [ε]; have := min_le_right δ η; linarith
  have hsmall : ∀ s ∈ Icc (t - ε) (t + ε),
      s ∈ Ioo (t - δ) (t + δ) ∧
      0 < inner ℝ a (deriv l s) ∧ 0 < inner ℝ a (deriv r s) := by
    intro s hs
    refine ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    apply hηball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hsubL : Icc (t - ε) t ⊆ Ioo (t - δ) (t + δ) := by
    intro s hs
    apply (hsmall s ⟨hs.1, by linarith [hs.2]⟩).1
  have hsubR : Icc t (t + ε) ⊆ Ioo (t - δ) (t + δ) := by
    intro s hs
    apply (hsmall s ⟨by linarith [hs.1], hs.2⟩).1
  have hlmono : StrictMonoOn (fun s => inner ℝ a (l s)) (Icc (t - ε) t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuousOn_const.inner (hl.continuousOn.mono hsubL)))
    intro s hs
    have hs' := interior_subset hs
    have hds : DifferentiableAt ℝ l s :=
      ((hl s (hsubL hs')).contDiffAt (isOpen_Ioo.mem_nhds (hsubL hs'))).differentiableAt
        (by simp)
    rw [deriv_inner_apply ℝ (differentiableAt_const a) hds]
    simpa using (hsmall s ⟨hs'.1, by linarith [hs'.2]⟩).2.1
  have hrmono : StrictMonoOn (fun s => inner ℝ a (r s)) (Icc t (t + ε)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuousOn_const.inner (hr.continuousOn.mono hsubR)))
    intro s hs
    have hs' := interior_subset hs
    have hds : DifferentiableAt ℝ r s :=
      ((hr s (hsubR hs')).contDiffAt (isOpen_Ioo.mem_nhds (hsubR hs'))).differentiableAt
        (by simp)
    rw [deriv_inner_apply ℝ (differentiableAt_const a) hds]
    simpa using (hsmall s ⟨by linarith [hs'.1], hs'.2⟩).2.2
  refine ⟨ε, hε, strictMonoOn_across_join hε hlmono hrmono ?_ ?_⟩
  · exact hel.mono (by intro s hs; exact ⟨by linarith [hs.1], hs.2⟩)
  · exact her.mono (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩)

@[simp] theorem inner_neg_quarterTurn_left (w v : Plane) :
    inner ℝ (-quarterTurn w) v = inner ℝ w (quarterTurn v) := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two] <;> ring

@[simp] theorem inner_neg_quarterTurn_self (w : Plane) :
    inner ℝ (-quarterTurn w) w = 0 := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two] <;> ring

/-- At a join with a constant strict transversal, the actual affine cylinder
has an injective open real-coordinate neighborhood. -/
theorem affine_join_local_injective (c : RegularJordanCurve) (W : C(ParameterCircle, Plane))
    {q : ParameterCircle} {w : Plane} (hw : w ≠ 0)
    (hconst : W =ᶠ[𝓝 q] (fun _ => w)) (hstrict : HasStrictJoinTransversality c q w) :
    ∃ (t : ℝ) (U : Set (ℝ × ℝ)), (t : ParameterCircle) = q ∧ IsOpen U ∧ (t, 0) ∈ U ∧
      Set.InjOn (fun z : ℝ × ℝ => realLift c.parametrization z.1 + z.2 • W (z.1 : ParameterCircle)) U := by
  obtain ⟨t, δ, l, r, htq, hδ, hl, hr, hel, her, hpl, hpr⟩ := hstrict
  obtain ⟨ε, hε, hmono⟩ := strict_projection_from_extensions hδ hl hr hel her
    (a := -quarterTurn w) (by simpa only [inner_neg_quarterTurn_left] using hpl)
      (by simpa only [inner_neg_quarterTurn_left] using hpr)
  have hconst' : ∀ᶠ s : ℝ in 𝓝 t, W (s : ParameterCircle) = w := by
    have hc : ContinuousAt (fun s : ℝ => (s : ParameterCircle)) t := continuous_quotient_mk'.continuousAt
    rw [← htq] at hconst
    exact hconst.comp_tendsto hc
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hconst'
  let d := min ε η / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdε : d ≤ ε := by dsimp [d]; have := min_le_left ε η; linarith
  have hdη : d < η := by dsimp [d]; have := min_le_right ε η; linarith
  have hsub : Ioo (t - d) (t + d) ⊆ Icc (t - ε) (t + ε) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hW : ∀ s ∈ Ioo (t - d) (t + d), W (s : ParameterCircle) = w := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  refine ⟨t, Ioo (t - d) (t + d) ×ˢ univ, htq, isOpen_Ioo.prod isOpen_univ,
    ⟨⟨by linarith, by linarith⟩, mem_univ _⟩, ?_⟩
  have hlocal := graph_translation_injOn (realLift c.parametrization)
    (Ioo (t - d) (t + d)) (-quarterTurn w) w
    ((hmono.mono hsub).injOn) (inner_neg_quarterTurn_self w) hw
  intro x hx y hy hxy
  apply hlocal hx hy
  simpa only [hW x.1 hx.1, hW y.1 hy.1] using hxy

/-- The two real columns of the linear collar derivative. -/
def planeColumnMap (u v : Plane) : (ℝ × ℝ) →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v

@[simp] theorem planeColumnMap_apply (u v : Plane) (z : ℝ × ℝ) :
    planeColumnMap u v z = z.1 • u + z.2 • v := rfl

theorem planeColumnMap_injective {u v : Plane}
    (h : inner ℝ v (quarterTurn u) ≠ 0) : Function.Injective (planeColumnMap u v) := by
  apply (planeColumnMap u v).ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  change z.1 • u + z.2 • v = 0 at hz
  have h0 := congrArg (fun w : Plane => w 0) hz
  have h1 := congrArg (fun w : Plane => w 1) hz
  change z.1 * u 0 + z.2 * v 0 = 0 at h0
  change z.1 * u 1 + z.2 * v 1 = 0 at h1
  have hd : u 0 * v 1 - u 1 * v 0 ≠ 0 := by
    convert h using 1
    simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hz1 : (u 0 * v 1 - u 1 * v 0) * z.1 = 0 := by
    linear_combination v 1 * h0 - v 0 * h1
  have hz2 : (u 0 * v 1 - u 1 * v 0) * z.2 = 0 := by
    linear_combination u 0 * h1 - u 1 * h0
  exact Prod.ext ((mul_eq_zero.mp hz1).resolve_left hd) ((mul_eq_zero.mp hz2).resolve_left hd)

/-- The collar derivative is an equivalence whenever transversality is strict. -/
def planeColumnEquiv (u v : Plane) (h : inner ℝ v (quarterTurn u) ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] Plane :=
  ((planeColumnMap u v).toLinearMap.linearEquivOfInjective (planeColumnMap_injective h)
    (by simp [Module.finrank_prod, Plane])).toContinuousLinearEquiv

@[simp] theorem planeColumnEquiv_coe (u v : Plane)
    (h : inner ℝ v (quarterTurn u) ≠ 0) :
    (planeColumnEquiv u v h : (ℝ × ℝ) →L[ℝ] Plane) = planeColumnMap u v := by
  apply ContinuousLinearMap.ext
  intro z
  rfl

/-- At a smooth parameter, the actual linear transverse collar admits an
ambient open local inverse. -/
theorem smooth_linear_collar_local_inverse {f v : ℝ → Plane} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ f t) (hv : ContDiffAt ℝ ∞ v t)
    (htrans : inner ℝ (v t) (quarterTurn (deriv f t)) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) Plane,
      (t, (0 : ℝ)) ∈ e.source ∧
      (∀ z, e z = f z.1 + z.2 • v z.1) ∧
      ContDiffAt ℝ ∞ e.symm (f t) ∧
      HasFDerivAt e.symm
        ((planeColumnEquiv (deriv f t) (v t) htrans).symm : Plane →L[ℝ] (ℝ × ℝ)) (f t) := by
  let F : ℝ × ℝ → Plane := fun z => f z.1 + z.2 • v z.1
  let L := planeColumnEquiv (deriv f t) (v t) htrans
  have hfd : DifferentiableAt ℝ f t := hf.differentiableAt (by simp)
  have hvd : DifferentiableAt ℝ v t := hv.differentiableAt (by simp)
  have h₁ := (hfd.hasDerivAt.hasFDerivAt).comp (t, (0 : ℝ))
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (t, (0 : ℝ))))
  have h₂ := (hvd.hasDerivAt.hasFDerivAt).comp (t, (0 : ℝ))
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (t, (0 : ℝ))))
  have h₃ := (hasFDerivAt_snd (𝕜 := ℝ) (p := (t, (0 : ℝ)))).smul h₂
  have hDF : HasFDerivAt F (L : (ℝ × ℝ) →L[ℝ] Plane) (t, 0) := by
    rw [planeColumnEquiv_coe]
    apply (h₁.add h₃).congr_fderiv
    apply ContinuousLinearMap.ext
    intro z
    simp [planeColumnMap, ContinuousLinearMap.comp_apply]
  have hc : ContDiffAt ℝ ∞ F (t, (0 : ℝ)) := by
    exact (hf.comp (t, (0 : ℝ)) contDiffAt_fst).add
      (contDiffAt_snd.smul (hv.comp (t, (0 : ℝ)) contDiffAt_fst))
  let e := hc.toOpenPartialHomeomorph F hDF (by simp)
  refine ⟨e, hc.mem_toOpenPartialHomeomorph_source hDF (by simp), fun _ => rfl, ?_, ?_⟩
  · change ContDiffAt ℝ ∞ (hc.localInverse hDF (by simp)) (f t)
    have hh := hc.to_localInverse hDF (by simp)
    simpa only [F, zero_smul, add_zero] using hh
  · change HasFDerivAt
      ((hc.hasStrictFDerivAt' hDF (by simp)).localInverse F L (t, 0))
      (L.symm : Plane →L[ℝ] (ℝ × ℝ)) (f t)
    have hh := (hc.hasStrictFDerivAt' hDF (by simp)).to_localInverse.hasFDerivAt
    simpa only [F, zero_smul, add_zero] using hh


/-- The ordinary quotient cylinder has local product covering coordinates. -/
theorem parameterCylinder_localHomeomorph :
    IsLocalHomeomorph (fun z : ℝ × ℝ => ((z.1 : ParameterCircle), z.2)) := by
  intro p
  obtain ⟨e, he, hq⟩ := AddCircle.isLocalHomeomorph_coe (1 : ℝ) p.1
  refine ⟨e.prod (OpenPartialHomeomorph.refl ℝ), ⟨he, mem_univ _⟩, ?_⟩
  funext z
  exact Prod.ext (congrFun hq z.1) rfl

/-- Any actual real-coordinate chart descends through the local covering
coordinates to a chart of the ordinary circle cylinder. -/
theorem circleCylinder_chart_of_real_chart (F : ParameterCircle × ℝ → Plane)
    (t : ℝ) (e : OpenPartialHomeomorph (ℝ × ℝ) Plane)
    (he : (t, (0 : ℝ)) ∈ e.source)
    (heq : ∀ z, e z = F ((z.1 : ParameterCircle), z.2)) :
    ∃ g : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane,
      ((t : ParameterCircle), (0 : ℝ)) ∈ g.source ∧ ∀ z, g z = F z := by
  let Q : ℝ × ℝ → ParameterCircle × ℝ := fun z => ((z.1 : ParameterCircle), z.2)
  have hlift : IsLocalHomeomorphOn (F ∘ Q) ({(t, (0 : ℝ))} : Set (ℝ × ℝ)) := by
    intro p hp
    have hp' : p = (t, (0 : ℝ)) := hp
    subst p
    exact ⟨e, he, (funext heq).symm⟩
  have hQ : IsLocalHomeomorphOn Q ({(t, (0 : ℝ))} : Set (ℝ × ℝ)) :=
    parameterCylinder_localHomeomorph.isLocalHomeomorphOn
  have hcircle := hlift.of_comp_right hQ
  obtain ⟨g, hg, hgeq⟩ := hcircle ((t : ParameterCircle), (0 : ℝ))
    ⟨(t, 0), mem_singleton _, rfl⟩
  exact ⟨g, hg, fun z => congrFun hgeq.symm z⟩

/-- Strict transversality at a smooth parameter gives a genuine local chart
of the circle cylinder for the actual linear collar. -/
theorem smooth_circle_collar_local_inverse (c : RegularJordanCurve)
    (W : C(ParameterCircle, Plane)) {t : ℝ}
    (hc : ContDiffAt ℝ ∞ (realLift c.parametrization) t)
    (hW : ContDiffAt ℝ ∞ (realLift W) t)
    (htrans : inner ℝ (realLift W t)
      (quarterTurn (deriv (realLift c.parametrization) t)) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane,
      ((t : ParameterCircle), (0 : ℝ)) ∈ e.source ∧
      ∀ z, e z = c.parametrization z.1 + z.2 • W z.1 := by
  obtain ⟨e, he, heq, -, -⟩ := smooth_linear_collar_local_inverse hc hW htrans
  exact circleCylinder_chart_of_real_chart
    (fun z => c.parametrization z.1 + z.2 • W z.1) t e he heq

/-- Invariance of domain upgrades any continuous planar cylinder injection on
an open parameter neighborhood to an actual ambient open chart. -/
theorem real_chart_of_injOn (F : ℝ × ℝ → Plane) (hF : Continuous F)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hi : Set.InjOn F U) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) Plane,
      e.source = U ∧ ∀ z, e z = F z := by
  let C : (ℝ × ℝ) ≃ₜ Plane :=
    (planeColumnEquiv !₂[1, 0] !₂[0, 1] (by
      norm_num [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two])).toHomeomorph
  let V : Set Plane := C.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage C.symm.continuous
  let h : V ≃ₜ U := C.symm.sets rfl
  let g : U → Plane := fun z => F z.val
  let f : V → Plane := g ∘ h
  have hg : Continuous g := hF.comp continuous_subtype_val
  have hf : Continuous f := hg.comp h.continuous
  have hfi : Function.Injective f := by
    intro x y hxy
    apply h.injective
    apply Subtype.ext
    exact hi (h x).property (h y).property hxy
  obtain ⟨ho, -, -⟩ := P202.InvarianceDomain.invarianceDomain 2 (by norm_num) V hV f hf hfi
  have hgo : IsOpenMap g := by
    have hh := ho.comp h.symm.isOpenMap
    have heq : f ∘ h.symm = g := by
      funext z
      simp [f]
    rw [heq] at hh
    exact hh
  refine ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv F U)
    hF.continuousOn hgo hU, rfl, fun _ => rfl⟩

/-- Local constant corner transversals and smooth strict arc transversals
produce one genuine ambient product chart on a uniform circle cylinder. -/
theorem curve_bicollar_of_transverse_field (c : RegularJordanCurve)
    (W : C(ParameterCircle, Plane))
    (hWoff : ∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
      ContDiffAt ℝ ∞ (realLift W) t ∧
        0 < inner ℝ (W (t : ParameterCircle))
          (quarterTurn (deriv (realLift c.parametrization) t)))
    (hWjoin : ∀ q ∈ c.joins, ∃ w : Plane, w ≠ 0 ∧ W =ᶠ[𝓝 q] (fun _ => w) ∧
      HasStrictJoinTransversality c q w) :
    ∃ (a : ℝ) (e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane),
      0 < a ∧ e.source = univ ×ˢ Ioo (-a) a ∧
        ∀ z, e z = c.parametrization z.1 + z.2 • W z.1 := by
  let F : ParameterCircle × ℝ → Plane :=
    fun z => c.parametrization z.1 + z.2 • W z.1
  have hF : Continuous F :=
    (c.parametrization.continuous.comp continuous_fst).add
      (continuous_snd.smul (W.continuous.comp continuous_fst))
  have hzero : Function.Injective (fun q => F (q, 0)) := by
    intro q q' heq
    apply c.injective
    simpa [F] using heq
  have hloc : ∀ q : ParameterCircle,
      ∃ e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane,
        (q, 0) ∈ e.source ∧ ∀ z, e z = F z := by
    intro q
    by_cases hq : q ∈ c.joins
    · obtain ⟨w, hw, hconst, hstrict⟩ := hWjoin q hq
      obtain ⟨t, U, htq, hU, htU, hinj⟩ :=
        affine_join_local_injective c W hw hconst hstrict
      have hγ : Continuous (realLift c.parametrization) :=
        c.parametrization.continuous.comp continuous_quotient_mk'
      have hW : Continuous (realLift W) := W.continuous.comp continuous_quotient_mk'
      have hreal : Continuous (fun z : ℝ × ℝ =>
          realLift c.parametrization z.1 + z.2 • W (z.1 : ParameterCircle)) :=
        (hγ.comp continuous_fst).add (continuous_snd.smul (hW.comp continuous_fst))
      obtain ⟨E, hEU, hEF⟩ := real_chart_of_injOn _ hreal U hU hinj
      have htE : (t, (0 : ℝ)) ∈ E.source := by rw [hEU]; exact htU
      obtain ⟨e, he, heF⟩ := circleCylinder_chart_of_real_chart F t E htE hEF
      refine ⟨e, ?_, heF⟩
      simpa only [htq] using he
    · obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨hWs, htrans⟩ := hWoff t hq
      exact smooth_circle_collar_local_inverse c W (c.smooth_off_joins t hq)
        hWs htrans.ne'
  exact uniform_bicollarChart F hF hzero hloc

/-- The prescribed piecewise smooth noncuspidal Jordan curve admits a genuine
ambient bicollar, with an actual continuous linear transverse field. -/
theorem curve_bicollar (c : RegularJordanCurve) :
    ∃ (W : C(ParameterCircle, Plane)) (a : ℝ)
      (e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane),
      0 < a ∧ e.source = univ ×ˢ Ioo (-a) a ∧
        (∀ z, e z = c.parametrization z.1 + z.2 • W z.1) ∧
        (∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
          ContDiffAt ℝ ∞ (realLift W) t ∧
            0 < inner ℝ (W (t : ParameterCircle))
              (quarterTurn (deriv (realLift c.parametrization) t))) := by
  obtain ⟨W, hWoff, hWjoin⟩ := curve_transverse_field c
  obtain ⟨a, e, ha, hsource, he⟩ := curve_bicollar_of_transverse_field c W hWoff hWjoin
  exact ⟨W, a, e, ha, hsource, he, hWoff⟩

/-- The two connected sides of an actual component bicollar have opposite
roles as domain and exterior, by the original local one-sidedness hypothesis. -/
theorem bicollar_domain_side_selection (R : PlanarRegion) (i : Fin R.boundaryCount)
    {a : ℝ} (ha : 0 < a)
    (e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane)
    (hsource : e.source = univ ×ˢ Ioo (-a) a)
    (hzero : ∀ q : ParameterCircle, e (q, 0) = (R.curve i).parametrization q)
    (havoid : ∀ j : Fin R.boundaryCount, j ≠ i → Disjoint e.target (R.curve j).trace) :
    (e '' (univ ×ˢ Ioo 0 a) ⊆ R.domain ∧
      e '' (univ ×ˢ Ioo (-a) 0) ⊆ (closure R.domain)ᶜ) ∨
    (e '' (univ ×ˢ Ioo (-a) 0) ⊆ R.domain ∧
      e '' (univ ×ˢ Ioo 0 a) ⊆ (closure R.domain)ᶜ) := by
  have hzsource : ∀ q : ParameterCircle, (q, (0 : ℝ)) ∈ e.source := by
    intro q
    rw [hsource]
    exact ⟨mem_univ _, neg_lt_zero.mpr ha, ha⟩
  have htrace_boundary : (R.curve i).trace ⊆ R.boundary := by
    intro p hp
    change p ∈ frontier R.domain
    rw [R.boundary_eq]
    exact mem_iUnion.mpr ⟨i, hp⟩
  have hzero_boundary : ∀ q : ParameterCircle, e (q, 0) ∈ R.boundary := by
    intro q
    rw [hzero]
    exact htrace_boundary (mem_range_self _)
  have hboundary : ∀ z ∈ e.source, e z ∈ R.boundary ↔ z.2 = 0 := by
    intro z hz
    constructor
    · intro hzb
      have hzT : e z ∈ e.target := e.map_source hz
      change e z ∈ frontier R.domain at hzb
      rw [R.boundary_eq] at hzb
      obtain ⟨j, q, heq⟩ := mem_iUnion.mp hzb
      have hji : j = i := by
        by_contra hji
        exact Set.disjoint_left.mp (havoid j hji) hzT ⟨q, heq⟩
      subst j
      have heq' : e z = e (q, 0) := by rw [hzero]; exact heq.symm
      exact congrArg Prod.snd (e.injOn hz (hzsource q) heq')
    · intro hz0
      exact (congrArg e (show z = (z.1, 0) from Prod.ext rfl hz0)).symm ▸ hzero_boundary z.1
  have hpos : univ ×ˢ Ioo 0 a ⊆ e.source := by
    intro z hz
    rw [hsource]
    exact ⟨mem_univ _, (neg_lt_zero.mpr ha).trans hz.2.1, hz.2.2⟩
  have hneg : univ ×ˢ Ioo (-a) 0 ⊆ e.source := by
    intro z hz
    rw [hsource]
    exact ⟨mem_univ _, hz.2.1, hz.2.2.trans ha⟩
  have hpartition : e.target \ frontier R.domain =
      e '' (univ ×ˢ Ioo 0 a) ∪ e '' (univ ×ˢ Ioo (-a) 0) := by
    ext y
    constructor
    · intro hy
      let z := e.symm y
      have hzs : z ∈ e.source := e.map_target hy.1
      have hezy : e z = y := e.right_inv hy.1
      have hz0 : z.2 ≠ 0 := by
        intro hz0
        have hyb : y ∈ R.boundary := hezy ▸ (hboundary z hzs).2 hz0
        exact hy.2 hyb
      have hzinterval : z.2 ∈ Ioo (-a) a := by rw [hsource] at hzs; exact hzs.2
      rcases lt_or_gt_of_ne hz0 with hzneg | hzpos
      · exact Or.inr ⟨z, ⟨mem_univ _, hzinterval.1, hzneg⟩, hezy⟩
      · exact Or.inl ⟨z, ⟨mem_univ _, hzpos, hzinterval.2⟩, hezy⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · refine ⟨e.map_source (hpos hz), ?_⟩
        exact fun hzb => hz.2.1.ne' ((hboundary z (hpos hz)).1 hzb)
      · refine ⟨e.map_source (hneg hz), ?_⟩
        exact fun hzb => hz.2.2.ne ((hboundary z (hneg hz)).1 hzb)
  have hposconn : IsPreconnected (e '' (univ ×ˢ Ioo 0 a)) :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image e (e.continuousOn.mono hpos)
  have hnegconn : IsPreconnected (e '' (univ ×ˢ Ioo (-a) 0)) :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image e (e.continuousOn.mono hneg)
  exact select_local_domain_side R.open_domain R.one_sided (hzero_boundary 0)
    e.open_target (e.map_source (hzsource 0)) hposconn hnegconn hpartition

/-- The side selected by local one-sidedness gives a single inward sign
for the entire component bicollar, including its zero section. -/
theorem bicollar_inward_sign (R : PlanarRegion) (i : Fin R.boundaryCount)
    {a : ℝ} (ha : 0 < a)
    (e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane)
    (hsource : e.source = univ ×ˢ Ioo (-a) a)
    (hzero : ∀ q : ParameterCircle, e (q, 0) = (R.curve i).parametrization q)
    (havoid : ∀ j : Fin R.boundaryCount, j ≠ i → Disjoint e.target (R.curve j).trace) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ (q : ParameterCircle) (r : ℝ),
      r ∈ Ioo (-a) a →
      (e (q, s * r) ∈ R.carrier ↔ 0 ≤ r) ∧
        (0 < r → e (q, s * r) ∈ interior R.carrier) := by
  have hzeroK : ∀ q : ParameterCircle, e (q, 0) ∈ R.carrier := by
    intro q
    rw [hzero]
    apply frontier_subset_closure
    rw [R.boundary_eq]
    exact mem_iUnion.mpr ⟨i, mem_range_self q⟩
  have hinterior : interior R.carrier = R.domain := (basicProperties R).2.2.1
  have htest (f : ParameterCircle × ℝ → Plane)
      (h0 : ∀ q : ParameterCircle, f (q, 0) ∈ R.carrier)
      (hp : f '' (univ ×ˢ Ioo 0 a) ⊆ R.domain)
      (hn : f '' (univ ×ˢ Ioo (-a) 0) ⊆ (closure R.domain)ᶜ) :
      ∀ (q : ParameterCircle) (r : ℝ), r ∈ Ioo (-a) a →
        (f (q, r) ∈ R.carrier ↔ 0 ≤ r) ∧
          (0 < r → f (q, r) ∈ interior R.carrier) := by
    intro q r hr
    have hpos (hrpos : 0 < r) : f (q, r) ∈ R.domain :=
      hp ⟨(q, r), ⟨mem_univ _, hrpos, hr.2⟩, rfl⟩
    refine ⟨?_, fun hrpos => hinterior ▸ hpos hrpos⟩
    constructor
    · intro hk
      by_contra hnegative
      exact hn ⟨(q, r), ⟨mem_univ _, hr.1, lt_of_not_ge hnegative⟩, rfl⟩ hk
    · intro hr0
      rcases hr0.eq_or_lt with hrzero | hrpos
      · rw [← hrzero]
        exact h0 q
      · exact subset_closure (hpos hrpos)
  rcases bicollar_domain_side_selection R i ha e hsource hzero havoid with
    hforward | hreverse
  · refine ⟨1, Or.inl rfl, ?_⟩
    simpa only [one_mul] using htest e hzeroK hforward.1 hforward.2
  · let f : ParameterCircle × ℝ → Plane := fun z => e (z.1, -z.2)
    have h0 : ∀ q : ParameterCircle, f (q, 0) ∈ R.carrier := by
      intro q
      simpa only [f, neg_zero] using hzeroK q
    have hp : f '' (univ ×ˢ Ioo 0 a) ⊆ R.domain := by
      rintro _ ⟨z, hz, rfl⟩
      apply hreverse.1
      exact ⟨(z.1, -z.2), ⟨mem_univ _, neg_lt_neg hz.2.2, neg_lt_zero.mpr hz.2.1⟩, rfl⟩
    have hn : f '' (univ ×ˢ Ioo (-a) 0) ⊆ (closure R.domain)ᶜ := by
      rintro _ ⟨z, hz, rfl⟩
      apply hreverse.2
      exact ⟨(z.1, -z.2), ⟨mem_univ _, neg_pos.mpr hz.2.2, (by simpa only [neg_neg] using neg_lt_neg hz.2.1)⟩, rfl⟩
    refine ⟨-1, Or.inr rfl, ?_⟩
    simpa only [neg_one_mul, f] using htest f h0 hp hn

/-- Component affine charts assemble into a single uniform bicollar of the
actual full frontier, via its canonical finite-union parametrization. -/
theorem region_bicollar_of_component_charts (R : PlanarRegion)
    (W : ∀ i : Fin R.boundaryCount, C(ParameterCircle, Plane))
    (a : Fin R.boundaryCount → ℝ) (ha : ∀ i, 0 < a i)
    (e : ∀ i : Fin R.boundaryCount, OpenPartialHomeomorph (ParameterCircle × ℝ) Plane)
    (hesource : ∀ i, (e i).source = univ ×ˢ Ioo (-a i) (a i))
    (hemap : ∀ i z, e i z = (R.curve i).parametrization z.1 + z.2 • W i z.1) :
    ∃ (b : ℝ) (E : OpenPartialHomeomorph (R.boundary × ℝ) Plane),
      0 < b ∧ E.source = univ ×ˢ Ioo (-b) b ∧
      (∀ x : R.boundary, E (x, 0) = x.val) ∧
      ∀ (x : R.boundary) (t : ℝ), E (x, t) = x.val +
        t • W ((boundaryParameterHomeomorph R).symm x).1
          ((boundaryParameterHomeomorph R).symm x).2 := by
  let X := Σ _ : Fin R.boundaryCount, ParameterCircle
  let D : X × ℝ ≃ₜ Σ _ : Fin R.boundaryCount, ParameterCircle × ℝ :=
    Homeomorph.sigmaProdDistrib
  have hD : ∀ (z : X) (r : ℝ), D (z, r) = ⟨z.1, (z.2, r)⟩ := by
    intro z r
    exact Homeomorph.sigmaProdDistrib_apply (X := fun _ : Fin R.boundaryCount => ParameterCircle) (z, r)
  let G : (Σ _ : Fin R.boundaryCount, ParameterCircle × ℝ) → Plane :=
    fun z => (R.curve z.1).parametrization z.2.1 + z.2.2 • W z.1 z.2.1
  have hG : Continuous G := by
    apply continuous_sigma
    intro i
    exact ((R.curve i).parametrization.continuous.comp continuous_fst).add
      (continuous_snd.smul ((W i).continuous.comp continuous_fst))
  let F : X × ℝ → Plane := G ∘ D
  have hF : Continuous F := hG.comp D.continuous
  have hFzero : ∀ z : X, F (z, 0) = (boundaryParameterMap R z).val := by
    intro z
    simp only [F, Function.comp_apply, hD, G, boundaryParameterMap, ContinuousMap.coe_mk, zero_smul, add_zero]
  have hinj : Function.Injective (fun z : X => F (z, 0)) := by
    intro x y hxy
    apply (boundaryParameterMap_bijective R).1
    apply Subtype.ext
    simpa only [hFzero] using hxy
  have hlocal : ∀ z : X, ∃ H : OpenPartialHomeomorph (X × ℝ) Plane,
      (z, 0) ∈ H.source ∧ ∀ p, H p = F p := by
    rintro ⟨i, q⟩
    let S := (e i).source
    have hlocal_i : IsLocalHomeomorphOn (G ∘ Sigma.mk i) S := by
      simpa only [show G ∘ Sigma.mk i = (e i : (ParameterCircle × ℝ) → Plane) from
        funext (fun p => (hemap i p).symm)] using IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn (e i)
    have hlocal_G := hlocal_i.of_comp_right
      (Topology.IsOpenEmbedding.sigmaMk.isLocalHomeomorph.isLocalHomeomorphOn)
    have hqS : (q, (0 : ℝ)) ∈ S := by
      rw [show S = (e i).source from rfl, hesource]
      exact ⟨mem_univ _, neg_lt_zero.mpr (ha i), ha i⟩
    obtain ⟨H, hH, hHG⟩ := hlocal_G ⟨i, (q, 0)⟩ ⟨(q, 0), hqS, rfl⟩
    refine ⟨D.toOpenPartialHomeomorph.trans H, ?_, ?_⟩
    · exact ⟨mem_univ _, hH⟩
    · intro p
      change H (D p) = G (D p)
      exact congrFun hHG.symm (D p)
  letI : Nonempty X := ⟨⟨⟨0, R.boundaryCount_pos⟩, 0⟩⟩
  obtain ⟨b, H, hb, hHsource, hHF⟩ := uniform_bicollarChart F hF hinj hlocal
  let P := boundaryParameterHomeomorph R
  let Q : R.boundary × ℝ ≃ₜ X × ℝ := P.symm.prodCongr (Homeomorph.refl ℝ)
  let E := Q.toOpenPartialHomeomorph.trans H
  have hQzero : ∀ x : R.boundary, (boundaryParameterMap R (P.symm x)).val = x.val := by
    intro x
    exact congrArg Subtype.val (P.apply_symm_apply x)
  have hEzero : ∀ x : R.boundary, E (x, 0) = x.val := by
    intro x
    change H (P.symm x, 0) = x.val
    rw [hHF, hFzero, hQzero]
  refine ⟨b, E, hb, ?_, hEzero, ?_⟩
  · ext z
    change (z ∈ univ ∧ Q z ∈ H.source) ↔ _
    rw [hHsource]
    simp only [mem_univ, true_and, mem_prod, mem_Ioo]
    rfl
  · intro x t
    change H (P.symm x, t) = _
    rw [hHF]
    simp only [F, Function.comp_apply, hD, G]
    change (R.curve (P.symm x).1).parametrization (P.symm x).2 + t • W _ _ = _
    rw [show (R.curve (P.symm x).1).parametrization (P.symm x).2 = x.val from hQzero x]

/-- In the oriented plane a covector annihilating the directed tangent and
evaluating to one on a positive transverse vector is positive on the left normal. -/
theorem left_normal_covector_positive (D : Plane →L[ℝ] ℝ) (v W : Plane)
    (htrans : 0 < inner ℝ W (quarterTurn v)) (htan : D v = 0) (hW : D W = 1) :
    0 < D (quarterTurn v) := by
  have hv : v ≠ 0 := by
    intro hz
    simp [hz, quarterTurn, PiLp.inner_apply, Fin.sum_univ_two] at htrans
  have hdecomp : inner ℝ W (quarterTurn v) • quarterTurn v + inner ℝ W v • v =
      inner ℝ v v • W := by
    ext i
    fin_cases i <;>
      simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two, EuclideanSpace.real_norm_sq_eq] <;> ring
  have hD := congrArg D hdecomp
  simp only [map_add, map_smul, htan, hW, smul_eq_mul, mul_zero, add_zero, mul_one] at hD
  exact (mul_pos_iff_of_pos_left htrans).mp (hD ▸ (real_inner_self_pos.mpr hv))

/-- A defining function with positive derivative in a direction detects both
actual short rays, using only differentiability at the boundary point. -/
theorem defining_function_normal_rays (F : Plane → ℝ) (p n : Plane)
    (hF : DifferentiableAt ℝ F p) (hzero : F p = 0)
    (hpos : 0 < fderiv ℝ F p n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      0 < F (p + r • n) ∧ F (p - r • n) < 0 := by
  let f : ℝ → ℝ := fun r => F (p + r • n)
  have hline : HasDerivAt (fun r : ℝ => p + r • n) n 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const n).const_add p
  have hFp : HasFDerivAt F (fderiv ℝ F p) (p + (0 : ℝ) • n) := by
    simpa using hF.hasFDerivAt
  have hf : HasDerivAt f (fderiv ℝ F p n) 0 := hFp.comp_hasDerivAt 0 hline
  have hsl : ∀ᶠ r in 𝓝[≠] (0 : ℝ), 0 < r⁻¹ * f r := by
    simpa [f, hzero] using hf.tendsto_slope_zero.eventually (eventually_gt_nhds hpos)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hsl)
  refine ⟨ε, hε, ?_⟩
  intro r hr hre
  have hdist : dist r 0 < ε := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hre
  have hndist : dist (-r) 0 < ε := by
    simpa only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hr] using hre
  have hp := he hdist (show r ∈ ({0} : Set ℝ)ᶜ from hr.ne')
  have hn := he hndist (show -r ∈ ({0} : Set ℝ)ᶜ from neg_ne_zero.mpr hr.ne')
  refine ⟨(mul_pos_iff_of_pos_left (inv_pos.mpr hr)).mp hp, ?_⟩
  have hnegative : (-r)⁻¹ < 0 := inv_lt_zero.mpr (neg_neg_of_pos hr)
  have hval : f (-r) < 0 :=
    ((mul_pos_iff.mp hn).resolve_left (fun h => (not_lt_of_ge hnegative.le) h.1)).2
  simpa only [f, neg_smul, ← sub_eq_add_neg] using hval

/-- In a smooth defining-function chart a positive transverse vector fixes the
sign of the actual normal rays for the prescribed oriented tangent. -/
theorem defining_function_left_normal_rays (F : Plane → ℝ) (p v W : Plane)
    (hF : DifferentiableAt ℝ F p) (hzero : F p = 0)
    (htan : fderiv ℝ F p v = 0) (hW : fderiv ℝ F p W = 1)
    (htrans : 0 < inner ℝ W (quarterTurn v)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      0 < F (p + r • quarterTurn v) ∧ F (p - r • quarterTurn v) < 0 := by
  apply defining_function_normal_rays F p (quarterTurn v) hF hzero
  exact left_normal_covector_positive (fderiv ℝ F p) v W htrans htan hW

/-- Local signs of a defining function give actual membership on short rays. -/
theorem normal_rays_in_local_sides {A B O : Set Plane} (F : Plane → ℝ) (p n : Plane)
    (hO : IsOpen O) (hpO : p ∈ O) (hF : DifferentiableAt ℝ F p)
    (hzero : F p = 0) (hpos : 0 < fderiv ℝ F p n)
    (hA : ∀ x ∈ O, 0 < F x → x ∈ A) (hB : ∀ x ∈ O, F x < 0 → x ∈ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      p + r • n ∈ A ∧ p - r • n ∈ B := by
  obtain ⟨ε, hε, hrays⟩ := defining_function_normal_rays F p n hF hzero hpos
  have hcplus : Continuous (fun r : ℝ => p + r • n) := by fun_prop
  have hcminus : Continuous (fun r : ℝ => p - r • n) := by fun_prop
  have hplus : ∀ᶠ r in 𝓝 (0 : ℝ), p + r • n ∈ O := by
    apply hcplus.continuousAt.eventually
    simpa only [zero_smul, add_zero] using (show ∀ᶠ y in 𝓝 p, y ∈ O from hO.mem_nhds hpO)
  have hminus : ∀ᶠ r in 𝓝 (0 : ℝ), p - r • n ∈ O := by
    apply hcminus.continuousAt.eventually
    simpa only [zero_smul, sub_zero] using (show ∀ᶠ y in 𝓝 p, y ∈ O from hO.mem_nhds hpO)
  obtain ⟨η, hη, hηprop⟩ := Metric.eventually_nhds_iff.mp (hplus.and hminus)
  refine ⟨min ε η, lt_min hε hη, ?_⟩
  intro r hr hre
  have hdist : dist r 0 < η := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using
      hre.trans_le (min_le_right ε η)
  have hmem := hηprop hdist
  have hsign := hrays r hr (hre.trans_le (min_le_left ε η))
  exact ⟨hA _ hmem.1 hsign.1, hB _ hmem.2 hsign.2⟩

/-- A local defining function for the actual curve annihilates its genuine
smooth derivative. No globally smooth loop is needed. -/
theorem defining_function_tangent_zero (c : RegularJordanCurve) (t : ℝ)
    (ht : (t : ParameterCircle) ∉ c.joins) (F : Plane → ℝ)
    (hF : DifferentiableAt ℝ F (realLift c.parametrization t))
    (hvanish : ∀ᶠ s in 𝓝 t, F (realLift c.parametrization s) = 0) :
    fderiv ℝ F (realLift c.parametrization t) (deriv (realLift c.parametrization) t) = 0 := by
  have hcurve : DifferentiableAt ℝ (realLift c.parametrization) t :=
    (c.smooth_off_joins t ht).differentiableAt (by simp)
  have hcomp := hF.hasFDerivAt.comp_hasDerivAt t hcurve.hasDerivAt
  exact hcomp.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hvanish)

/-- A genuine scalar defining chart and a positive transverse vector give the
paper's exact smooth-arc left/right normal tests. -/
theorem boundary_normal_rays_of_defining_function {A B O : Set Plane}
    (c : RegularJordanCurve) (t : ℝ) (ht : (t : ParameterCircle) ∉ c.joins)
    (F : Plane → ℝ) (W : Plane) (hO : IsOpen O)
    (hpO : realLift c.parametrization t ∈ O)
    (hF : DifferentiableAt ℝ F (realLift c.parametrization t))
    (hvanish : ∀ᶠ s in 𝓝 t, F (realLift c.parametrization s) = 0)
    (hW : fderiv ℝ F (realLift c.parametrization t) W = 1)
    (htrans : 0 < inner ℝ W (quarterTurn (deriv (realLift c.parametrization) t)))
    (hA : ∀ x ∈ O, 0 < F x → x ∈ A) (hB : ∀ x ∈ O, F x < 0 → x ∈ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      realLift c.parametrization t +
        r • quarterTurn (deriv (realLift c.parametrization) t) ∈ A ∧
      realLift c.parametrization t -
        r • quarterTurn (deriv (realLift c.parametrization) t) ∈ B := by
  apply normal_rays_in_local_sides F _ _ hO hpO hF hvanish.self_of_nhds _ hA hB
  exact left_normal_covector_positive _ _ W htrans
    (defining_function_tangent_zero c t ht F hF hvanish) hW

/-- At every smooth parameter, actual tangent-normal rays enter the two
corresponding sides of the affine transverse cylinder. This uses the genuine
smooth local inverse, without a globally smooth-loop hypothesis. -/
theorem affine_bicollar_normal_rays (c : RegularJordanCurve)
    (W : C(ParameterCircle, Plane)) (t a : ℝ) (ha : 0 < a)
    (hc : ContDiffAt ℝ ∞ (realLift c.parametrization) t)
    (hW : ContDiffAt ℝ ∞ (realLift W) t)
    (htrans : 0 < inner ℝ (realLift W t)
      (quarterTurn (deriv (realLift c.parametrization) t))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      realLift c.parametrization t +
        r • quarterTurn (deriv (realLift c.parametrization) t) ∈
        (fun z : ParameterCircle × ℝ => c.parametrization z.1 + z.2 • W z.1) ''
          (univ ×ˢ Ioo 0 a) ∧
      realLift c.parametrization t -
        r • quarterTurn (deriv (realLift c.parametrization) t) ∈
        (fun z : ParameterCircle × ℝ => c.parametrization z.1 + z.2 • W z.1) ''
          (univ ×ˢ Ioo (-a) 0) := by
  obtain ⟨e, he, heq, hesmooth, heder⟩ := smooth_linear_collar_local_inverse hc hW htrans.ne'
  let p := realLift c.parametrization t
  let L := planeColumnEquiv (deriv (realLift c.parametrization) t) (realLift W t) htrans.ne'
  let F : Plane → ℝ := fun x => (e.symm x).2
  have hline : e (t, (0 : ℝ)) = p := by simp [heq, p]
  have hsymm : e.symm p = (t, (0 : ℝ)) := by
    rw [← hline]
    exact e.left_inv he
  have hpt : p ∈ e.target := hline ▸ e.map_source he
  have hzero : F p = 0 := by simp only [F, hsymm]
  have hDF : HasFDerivAt F
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (L.symm : Plane →L[ℝ] (ℝ × ℝ))) p := by
    exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp p heder
  have hLv : L ((1 : ℝ), 0) = deriv (realLift c.parametrization) t := by
    change planeColumnMap _ _ ((1 : ℝ), 0) = _
    simp
  have hLW : L ((0 : ℝ), 1) = realLift W t := by
    change planeColumnMap _ _ ((0 : ℝ), 1) = _
    simp
  have htan : fderiv ℝ F p (deriv (realLift c.parametrization) t) = 0 := by
    rw [hDF.fderiv, ContinuousLinearMap.comp_apply, ← hLv]
    change (L.symm (L ((1 : ℝ), 0))).2 = 0
    rw [L.symm_apply_apply]
  have hunit : fderiv ℝ F p (realLift W t) = 1 := by
    rw [hDF.fderiv, ContinuousLinearMap.comp_apply, ← hLW]
    change (L.symm (L ((0 : ℝ), 1))).2 = 1
    rw [L.symm_apply_apply]
  have hinterval : F ⁻¹' Ioo (-a) a ∈ 𝓝 p :=
    hDF.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds
      ⟨by rw [hzero]; linarith, by rwa [hzero]⟩)
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_target.mem_nhds hpt) hinterval)
  apply normal_rays_in_local_sides F p _ hO hpO hDF.differentiableAt hzero
    (left_normal_covector_positive _ _ _ htrans htan hunit)
  · intro x hx hsign
    refine ⟨(((e.symm x).1 : ParameterCircle), F x),
      ⟨mem_univ _, hsign, (hOsub hx).2.2⟩, ?_⟩
    simpa only [heq, F, realLift] using e.right_inv (hOsub hx).1
  · intro x hx hsign
    refine ⟨(((e.symm x).1 : ParameterCircle), F x),
      ⟨mem_univ _, (hOsub hx).2.1, hsign⟩, ?_⟩
    simpa only [heq, F, realLift] using e.right_inv (hOsub hx).1

/-- Restrict a genuine global frontier bicollar to any prescribed component.
Its target automatically avoids all other boundary traces. -/
theorem boundary_bicollar_component_chart (R : PlanarRegion) (i : Fin R.boundaryCount)
    {a : ℝ} (ha : 0 < a)
    (E : OpenPartialHomeomorph (R.boundary × ℝ) Plane)
    (hsource : E.source = univ ×ˢ Ioo (-a) a)
    (hzero : ∀ x : R.boundary, E (x, 0) = x.val) :
    ∃ e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane,
      e.source = univ ×ˢ Ioo (-a) a ∧
      (∀ q : ParameterCircle, e (q, 0) = (R.curve i).parametrization q) ∧
      (∀ j : Fin R.boundaryCount, j ≠ i → Disjoint e.target (R.curve j).trace) ∧
      ∀ (q : ParameterCircle) (t : ℝ), e (q, t) =
        E ((boundaryParameterHomeomorph R) ⟨i, q⟩, t) := by
  let P := boundaryParameterHomeomorph R
  let J : ParameterCircle × ℝ → R.boundary × ℝ :=
    fun z => (P ⟨i, z.1⟩, z.2)
  have hJ : Topology.IsOpenEmbedding J :=
    (P.isOpenEmbedding.comp (Topology.IsOpenEmbedding.sigmaMk (i := i))).prodMap
      (Homeomorph.refl ℝ).isOpenEmbedding
  let e := hJ.toOpenPartialHomeomorph.trans E
  have hemap : ∀ (q : ParameterCircle) (t : ℝ), e (q, t) = E (P ⟨i, q⟩, t) := by
    intro q t
    rfl
  have hesource : e.source = univ ×ˢ Ioo (-a) a := by
    ext z
    change (z ∈ univ ∧ J z ∈ E.source) ↔ _
    rw [hsource]
    simp only [mem_univ, true_and, mem_prod, mem_Ioo]
    rfl
  have hPval : ∀ (j : Fin R.boundaryCount) (q : ParameterCircle),
      (P ⟨j, q⟩).val = (R.curve j).parametrization q := by
    intro j q
    rfl
  refine ⟨e, hesource, ?_, ?_, hemap⟩
  · intro q
    rw [hemap, hzero, hPval]
  · intro j hji
    rw [Set.disjoint_left]
    intro p hpe hpj
    obtain ⟨q, hq⟩ := hpj
    let z := e.symm p
    have hz : z ∈ e.source := e.map_target hpe
    have hez : e z = p := e.right_inv hpe
    have hzE : J z ∈ E.source := by
      change z ∈ univ ∧ J z ∈ E.source at hz
      exact hz.2
    have hqE : (P ⟨j, q⟩, (0 : ℝ)) ∈ E.source := by
      rw [hsource]
      exact ⟨mem_univ _, neg_lt_zero.mpr ha, ha⟩
    have hEq : E (J z) = E (P ⟨j, q⟩, 0) := by
      rw [hzero, hPval, hq]
      exact hez
    have hbase : P ⟨i, z.1⟩ = P ⟨j, q⟩ := congrArg Prod.fst (E.injOn hzE hqE hEq)
    have hij : i = j := congrArg Sigma.fst (P.injective hbase)
    exact hji hij.symm

/-- One sign on each given component coherently selects the domain side
of a global frontier bicollar; the resulting sign function is continuous. -/
theorem boundary_bicollar_inward_signs (R : PlanarRegion)
    {a : ℝ} (ha : 0 < a)
    (E : OpenPartialHomeomorph (R.boundary × ℝ) Plane)
    (hsource : E.source = univ ×ˢ Ioo (-a) a)
    (hzero : ∀ x : R.boundary, E (x, 0) = x.val) :
    ∃ s : Fin R.boundaryCount → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      Continuous (fun x : R.boundary => s ((boundaryParameterHomeomorph R).symm x).1) ∧
      ∀ (x : R.boundary) (r : ℝ), r ∈ Ioo (-a) a →
        (E (x, s ((boundaryParameterHomeomorph R).symm x).1 * r) ∈ R.carrier ↔ 0 ≤ r) ∧
        (0 < r → E (x, s ((boundaryParameterHomeomorph R).symm x).1 * r) ∈ interior R.carrier) := by
  choose e hesource hezero heavoid hemap using
    fun i => boundary_bicollar_component_chart R i ha E hsource hzero
  choose s hs htest using fun i => bicollar_inward_sign R i ha (e i)
    (hesource i) (hezero i) (heavoid i)
  have hscont : Continuous (fun z : Σ _ : Fin R.boundaryCount, ParameterCircle => s z.1) := by
    exact continuous_sigma (fun i =>
      (continuous_const : Continuous (fun _ : ParameterCircle => s i)))
  refine ⟨s, hs, hscont.comp (boundaryParameterHomeomorph R).symm.continuous, ?_⟩
  intro x r hr
  let z := (boundaryParameterHomeomorph R).symm x
  have hPx : (boundaryParameterHomeomorph R) ⟨z.1, z.2⟩ = x :=
    (boundaryParameterHomeomorph R).apply_symm_apply x
  simpa only [hemap, hPx] using htest z.1 z.2 r hr

/-- Reflecting the time coordinate independently on the finitely many
parametrized components converts a bicollar into a genuine inward collar. -/
theorem boundaryCollar_of_signed_bicollar (R : PlanarRegion) {a : ℝ} (ha : 0 < a)
    (e : OpenPartialHomeomorph (R.boundary × ℝ) Plane)
    (hsource : e.source = univ ×ˢ Ioo (-a) a)
    (hzero : ∀ x : R.boundary, e (x, 0) = x.val)
    (s : Fin R.boundaryCount → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hsign : ∀ (x : R.boundary) (r : ℝ), r ∈ Ioo (-a) a →
      (e (x, s ((boundaryParameterHomeomorph R).symm x).1 * r) ∈ R.carrier ↔ 0 ≤ r) ∧
      (0 < r → e (x, s ((boundaryParameterHomeomorph R).symm x).1 * r) ∈ interior R.carrier)) :
    Nonempty (BoundaryCollar R.carrier R.boundary) := by
  let P := boundaryParameterHomeomorph R
  let σ : R.boundary → ℝ := fun x => s (P.symm x).1
  have hσ₀ : Continuous (fun z : (Σ _ : Fin R.boundaryCount, ParameterCircle) => s z.1) := by
    apply continuous_sigma
    intro i
    change Continuous (fun _ : ParameterCircle => s i)
    exact continuous_const
  have hσ : Continuous σ := hσ₀.comp P.symm.continuous
  let J : R.boundary × ℝ ≃ₜ R.boundary × ℝ :=
    { toFun := fun z => (z.1, σ z.1 * z.2)
      invFun := fun z => (z.1, σ z.1 * z.2)
      left_inv := by
        intro z
        apply Prod.ext
        · rfl
        · change σ z.1 * (σ z.1 * z.2) = z.2
          rcases hs (P.symm z.1).1 with h | h <;> simp [σ, h]
      right_inv := by
        intro z
        apply Prod.ext
        · rfl
        · change σ z.1 * (σ z.1 * z.2) = z.2
          rcases hs (P.symm z.1).1 with h | h <;> simp [σ, h]
      continuous_toFun := continuous_fst.prodMk ((hσ.comp continuous_fst).mul continuous_snd)
      continuous_invFun := continuous_fst.prodMk ((hσ.comp continuous_fst).mul continuous_snd) }
  let e' := J.toOpenPartialHomeomorph.trans e
  have he' : ∀ z, e' z = e (z.1, σ z.1 * z.2) := fun _ => rfl
  have hsource' : e'.source = univ ×ˢ Ioo (-a) a := by
    ext z
    change (z ∈ univ ∧ J z ∈ e.source) ↔ _
    rw [hsource]
    change (True ∧ True ∧ -a < σ z.1 * z.2 ∧ σ z.1 * z.2 < a) ↔
      True ∧ -a < z.2 ∧ z.2 < a
    rcases hs (P.symm z.1).1 with h | h
    · simp [σ, h]
    · simp only [σ, h, neg_one_mul, true_and]
      constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]
  apply boundaryCollar_of_bicollar (compact_boundary R) frontier_subset_closure ha e' hsource'
  · intro x
    simpa only [he', mul_zero] using hzero x
  · intro z hz
    rw [hsource'] at hz
    exact (hsign z.1 z.2 hz.2).1
  · intro z hz hp
    rw [hsource'] at hz
    exact (hsign z.1 z.2 hz.2).2 hp

/-- The actual component bicollar selects one induced sign, and the smooth
local inverse proves the required tangent-normal test for that sign. -/
theorem component_induced_sign_of_bicollar (R : PlanarRegion) (i : Fin R.boundaryCount)
    (W : C(ParameterCircle, Plane)) (a : ℝ) (ha : 0 < a)
    (e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane)
    (hsource : e.source = univ ×ˢ Ioo (-a) a)
    (hformula : ∀ z, e z = (R.curve i).parametrization z.1 + z.2 • W z.1)
    (havoid : ∀ j : Fin R.boundaryCount, j ≠ i → Disjoint e.target (R.curve j).trace)
    (hWoff : ∀ t : ℝ, (t : ParameterCircle) ∉ (R.curve i).joins →
      ContDiffAt ℝ ∞ (realLift W) t)
    (htrans : ∀ t : ℝ, (t : ParameterCircle) ∉ (R.curve i).joins →
      0 < inner ℝ (realLift W t)
        (quarterTurn (deriv (realLift (R.curve i).parametrization) t))) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ HasSideOnLeft R.domain (R.curve i) s := by
  have hzero : ∀ q : ParameterCircle, e (q, 0) = (R.curve i).parametrization q := by
    intro q
    simp only [hformula, zero_smul, add_zero]
  have hmap : (fun z : ParameterCircle × ℝ =>
      (R.curve i).parametrization z.1 + z.2 • W z.1) = e := by
    funext z
    exact (hformula z).symm
  have hray : ∀ t : ℝ, (t : ParameterCircle) ∉ (R.curve i).joins →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
        realLift (R.curve i).parametrization t +
          r • quarterTurn (deriv (realLift (R.curve i).parametrization) t) ∈
          e '' (univ ×ˢ Ioo 0 a) ∧
        realLift (R.curve i).parametrization t -
          r • quarterTurn (deriv (realLift (R.curve i).parametrization) t) ∈
          e '' (univ ×ˢ Ioo (-a) 0) := by
    intro t ht
    simpa only [hmap] using affine_bicollar_normal_rays (R.curve i) W t a ha
      ((R.curve i).smooth_off_joins t ht) (hWoff t ht) (htrans t ht)
  rcases bicollar_domain_side_selection R i ha e hsource hzero havoid with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro t ht
    obtain ⟨ε, hε, htest⟩ := hray t ht
    refine ⟨ε, hε, ?_⟩
    intro r hr hre
    simpa only [one_smul] using hpos.1 (htest r hr hre).1
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro t ht
    obtain ⟨ε, hε, htest⟩ := hray t ht
    refine ⟨ε, hε, ?_⟩
    intro r hr hre
    simpa only [neg_one_smul, smul_neg, sub_eq_add_neg] using hneg.1 (htest r hr hre).2

/-- A family of actual affine component bicollars gives the coherent induced
orientation on every supplied parametrized component. -/
theorem induced_orientation_of_affine_bicollars (R : PlanarRegion)
    (W : Fin R.boundaryCount → C(ParameterCircle, Plane))
    (a : Fin R.boundaryCount → ℝ) (ha : ∀ i, 0 < a i)
    (e : Fin R.boundaryCount → OpenPartialHomeomorph (ParameterCircle × ℝ) Plane)
    (hsource : ∀ i, (e i).source = univ ×ˢ Ioo (-a i) (a i))
    (hformula : ∀ i z, e i z = (R.curve i).parametrization z.1 + z.2 • W i z.1)
    (havoid : ∀ i j : Fin R.boundaryCount, j ≠ i → Disjoint (e i).target (R.curve j).trace)
    (hWoff : ∀ (i : Fin R.boundaryCount) (t : ℝ), (t : ParameterCircle) ∉ (R.curve i).joins →
      ContDiffAt ℝ ∞ (realLift (W i)) t)
    (htrans : ∀ (i : Fin R.boundaryCount) (t : ℝ), (t : ParameterCircle) ∉ (R.curve i).joins →
      0 < inner ℝ (realLift (W i) t)
        (quarterTurn (deriv (realLift (R.curve i).parametrization) t))) :
    ∃ s, IsInducedBoundaryOrientation R s := by
  have hsign : ∀ i : Fin R.boundaryCount, ∃ s : ℝ,
      (s = 1 ∨ s = -1) ∧ HasSideOnLeft R.domain (R.curve i) s := by
    intro i
    exact component_induced_sign_of_bicollar R i (W i) (a i) (ha i) (e i)
      (hsource i) (hformula i) (havoid i) (hWoff i) (htrans i)
  choose s hs hleft using hsign
  exact ⟨s, fun i => ⟨hs i, hleft i⟩⟩

/-- The original region data alone give its genuine boundary collar and the
coherent induced signs on its prescribed parametrized boundary components. -/
theorem regionCollarAndOrientation (R : PlanarRegion) :
    Nonempty (BoundaryCollar R.carrier R.boundary) ∧
      ∃ s, IsInducedBoundaryOrientation R s := by
  choose W a e ha hesource heformula hWoff using
    fun i : Fin R.boundaryCount => curve_bicollar (R.curve i)
  obtain ⟨b, E, hb, hEsource, hEzero, hEformula⟩ :=
    region_bicollar_of_component_charts R W a ha e hesource heformula
  obtain ⟨s, hs, _, hsign⟩ := boundary_bicollar_inward_signs R hb E hEsource hEzero
  have hcollar := boundaryCollar_of_signed_bicollar R hb E hEsource hEzero s hs hsign
  choose e' he'Source he'zero he'avoid he'map using
    fun i : Fin R.boundaryCount => boundary_bicollar_component_chart R i hb E hEsource hEzero
  have hformula : ∀ (i : Fin R.boundaryCount) (z : ParameterCircle × ℝ),
      e' i z = (R.curve i).parametrization z.1 + z.2 • W i z.1 := by
    intro i z
    rw [he'map, hEformula]
    rw [(boundaryParameterHomeomorph R).symm_apply_apply]
    rfl
  have horient : ∃ s, IsInducedBoundaryOrientation R s :=
    induced_orientation_of_affine_bicollars R W (fun _ => b) (fun _ => hb) e'
      he'Source hformula he'avoid (fun i t ht => (hWoff i t ht).1)
      (fun i t ht => (hWoff i t ht).2)
  exact ⟨hcollar, horient⟩

/-- Full local geometry of the given planar region, including reflex corners,
a genuine collar in the ordinary product topology, and the actual normal test. -/
theorem localGeometry : Expected.localGeometry := by
  intro R
  obtain ⟨hcollar, horient⟩ := regionCollarAndOrientation R
  exact ⟨regionSurface R, regionLocallyContractible R, hcollar, horient⟩

end P202.PlanarRegionTopology
