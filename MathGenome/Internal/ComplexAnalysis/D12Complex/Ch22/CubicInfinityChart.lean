import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.CubicInfinityChart
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.CubicFiniteCharts
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The missing chart at [0:0:1] of the literal cubic. The graph theorem is
applied to its polynomial equation. Factoring the resulting solution as u³A(u)
gives the seventh-order remainder without presuming a Taylor expansion.
Finite/infinity transitions are the coordinate ratios x/y, u/v, and 1/v.
Finally the compatible local charts are restricted to disk targets to form a
complex atlas; connectedness is not used.
-/
noncomputable section
open Set Filter Topology Asymptotics
open scoped Topology
namespace D12Complex.CubicInfinityChart
open ProjectivePlaneTopology CubicFiniteCharts

@[simp] theorem infinityU_infinityPoint (u v : ℂ) : infinityU (infinityPoint u v) = u := by
  change affineCoordinate 2 (affineParam 2 ![v,u]) 1 = u
  rw [affineCoordinate_param]
  rfl
@[simp] theorem infinityV_infinityPoint (u v : ℂ) : infinityV (infinityPoint u v) = v := by
  change affineCoordinate 2 (affineParam 2 ![v,u]) 0 = v
  rw [affineCoordinate_param]
  rfl

theorem infinityPoint_mem_patch (u v : ℂ) : infinityPoint u v ∈ coordinatePatch 2 :=
  affineParam_mem_patch 2 ![v,u]

theorem infinityPoint_coordinates {p : ComplexProjectivePlane}
    (hp : p ∈ coordinatePatch 2) : infinityPoint (infinityU p) (infinityV p) = p := by
  have h : ![infinityV p, infinityU p] = affineCoordinate 2 p := by
    ext i
    fin_cases i <;> rfl
  simpa only [infinityPoint, h] using affineParam_coordinate 2 hp

@[simp] theorem onCubic_infinityPoint_iff (G H u v : ℂ) :
    OnCubic G H (infinityPoint u v) ↔ v = 4*u^3-G*u*v^2-H*v^3 := by
  simp only [infinityPoint, affineParam, onCubic_projection_iff, homogeneousEquation]
  change 1^2*v-4*u^3+G*u*v^2+H*v^3 = 0 ↔ _
  constructor <;> intro h <;> linear_combination h

theorem infinity_equation (G H : ℂ) (p : ComplexProjectivePlane)
    (hp : p ∈ coordinatePatch 2) :
    OnCubic G H p ↔ infinityV p = 4*infinityU p^3-G*infinityU p*infinityV p^2-H*infinityV p^3 := by
  rw [← infinityPoint_coordinates hp, onCubic_infinityPoint_iff]
  simp

@[simp] theorem O_eq : infinityPoint 0 0 = O := rfl
@[simp] theorem infinityU_O : infinityU O = 0 := infinityU_infinityPoint 0 0
@[simp] theorem infinityV_O : infinityV O = 0 := infinityV_infinityPoint 0 0
@[simp] theorem O_onCubic (G H : ℂ) : OnCubic G H O := by
  exact (onCubic_infinityPoint_iff G H 0 0).mpr (by ring)

@[simp] theorem O_not_mem_finitePatch : O ∉ coordinatePatch 0 := by
  change projection _ ∉ coordinatePatch 0
  rw [projection_mem_patch_iff]
  change ¬ (0 : ℂ) ≠ 0
  simp

@[simp] theorem O_mem_infinityPatch : O ∈ coordinatePatch 2 := affineParam_mem_patch 2 _

theorem eq_O_of_not_finite (G H : ℂ) {p : ComplexProjectivePlane}
    (hp : OnCubic G H p) (hfin : p ∉ coordinatePatch 0) : p = O := by
  induction p using Projectivization.ind with | h v hv =>
  have hz : v 0 = 0 := by
    by_contra hn
    exact hfin ((projection_mem_patch_iff 0 ⟨v,hv⟩).mpr hn)
  have heq := (onCubic_projection_iff G H ⟨v,hv⟩).mp hp
  have hx : v 1 = 0 := by
    have hpow : v 1 ^ 3 = 0 := by
      simp only [homogeneousEquation, hz, mul_zero, zero_pow (by omega : 2 ≠ 0),
        zero_pow (by omega : 3 ≠ 0), add_zero, zero_sub] at heq
      exact (mul_eq_zero.mp (neg_eq_zero.mp heq)).resolve_left (by norm_num)
    exact (pow_eq_zero_iff (by omega : 3 ≠ 0)).mp hpow
  apply projection_eq_iff_minors ⟨v,hv⟩ _ |>.mpr
  intro i j
  have hw : (2 : Fin 3).insertNth (1 : ℂ) ![0,0] = ![0,0,1] := by
    ext k
    fin_cases k <;> rfl
  fin_cases i <;> fin_cases j <;> simp [hw, hz, hx]

theorem unique_infinity : Specs.D12Complex.Ch22.CubicInfinityChart.unique_infinity_type := by
  intro G H
  refine ⟨O_onCubic G H, O_not_mem_finitePatch, ?_⟩
  intro p hp
  constructor
  · exact eq_O_of_not_finite G H hp
  · rintro rfl
    exact O_not_mem_finitePatch

theorem continuous_infinityPoint : Continuous (fun z : ℂ × ℂ => infinityPoint z.1 z.2) := by
  apply (continuous_affineParam 2).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_snd
  · exact continuous_fst

theorem continuousOn_infinityU : ContinuousOn infinityU (coordinatePatch 2) := by
  change ContinuousOn (fun p => affineCoordinate 2 p 1) (coordinatePatch 2)
  exact (continuous_apply 1).comp_continuousOn (continuousOn_affineCoordinate 2)

theorem continuousOn_infinityV : ContinuousOn infinityV (coordinatePatch 2) := by
  change ContinuousOn (fun p => affineCoordinate 2 p 0) (coordinatePatch 2)
  exact (continuous_apply 0).comp_continuousOn (continuousOn_affineCoordinate 2)

theorem continuousOn_infinityU_cubic (G H : ℂ) :
    ContinuousOn (fun p : Cubic G H => infinityU p.val) (infinityPatch G H) :=
  continuousOn_infinityU.comp continuous_subtype_val.continuousOn (fun _ hp => hp)

theorem continuousOn_infinityV_cubic (G H : ℂ) :
    ContinuousOn (fun p : Cubic G H => infinityV p.val) (infinityPatch G H) :=
  continuousOn_infinityV.comp continuous_subtype_val.continuousOn (fun _ hp => hp)

theorem infinityPatch_isOpen (G H : ℂ) : IsOpen (infinityPatch G H) :=
  (coordinatePatch_isOpen 2).preimage continuous_subtype_val

@[simp] theorem finiteX_infinityPoint (u v : ℂ) : finiteX (infinityPoint u v) = u/v := by
  rfl
@[simp] theorem finiteY_infinityPoint (u v : ℂ) : finiteY (infinityPoint u v) = 1/v := by
  rfl
@[simp] theorem infinityU_affinePoint (x y : ℂ) : infinityU (affinePoint x y) = x/y := by
  rfl
@[simp] theorem infinityV_affinePoint (x y : ℂ) : infinityV (affinePoint x y) = 1/y := by
  rfl

@[simp] theorem infinityPoint_mem_finite_iff (u v : ℂ) : infinityPoint u v ∈ coordinatePatch 0 ↔ v ≠ 0 := by
  change projection _ ∈ coordinatePatch 0 ↔ v ≠ 0
  rw [projection_mem_patch_iff]
  rfl
@[simp] theorem affinePoint_mem_infinity_iff (x y : ℂ) : affinePoint x y ∈ coordinatePatch 2 ↔ y ≠ 0 := by
  simp [affinePoint, affineParam]

theorem finiteX_eq_infinityU_div_infinityV {p : ComplexProjectivePlane}
    (hp : p ∈ coordinatePatch 2) : finiteX p = infinityU p / infinityV p := by
  rw [← infinityPoint_coordinates hp, finiteX_infinityPoint]
  simp

theorem finiteY_eq_one_div_infinityV {p : ComplexProjectivePlane}
    (hp : p ∈ coordinatePatch 2) : finiteY p = 1 / infinityV p := by
  rw [← infinityPoint_coordinates hp, finiteY_infinityPoint]
  simp

theorem infinityU_eq_finiteX_div_finiteY {p : ComplexProjectivePlane}
    (hp : p ∈ coordinatePatch 0) : infinityU p = finiteX p / finiteY p := by
  rw [← affinePoint_coordinates hp, infinityU_affinePoint]
  simp

theorem infinityV_eq_one_div_finiteY {p : ComplexProjectivePlane}
    (hp : p ∈ coordinatePatch 0) : infinityV p = 1 / finiteY p := by
  rw [← affinePoint_coordinates hp, infinityV_affinePoint]
  simp

theorem infinityV_ne_zero {p : ComplexProjectivePlane}
    (hp₂ : p ∈ coordinatePatch 2) (hp₀ : p ∈ coordinatePatch 0) : infinityV p ≠ 0 := by
  have hm := hp₀
  rw [← infinityPoint_coordinates hp₂, infinityPoint_mem_finite_iff] at hm
  simpa only [infinityV_infinityPoint] using hm

theorem finiteY_ne_zero {p : ComplexProjectivePlane}
    (hp₀ : p ∈ coordinatePatch 0) (hp₂ : p ∈ coordinatePatch 2) : finiteY p ≠ 0 := by
  have hm := hp₂
  rw [← affinePoint_coordinates hp₀, affinePoint_mem_infinity_iff] at hm
  simpa only [finiteY_affinePoint] using hm


lemma local_infinity_graph (G H : ℂ) :
    ∃ (U W : Set ℂ) (f : ℂ → ℂ),
      IsOpen U ∧ IsOpen W ∧ 0 ∈ U ∧ 0 ∈ W ∧
      HolomorphicOn U f ∧ f 0 = 0 ∧ MapsTo f U W ∧
      ∀ z ∈ U, ∀ w ∈ W, w = 4*z^3-G*z*w^2-H*w^3 ↔ w = f z := by
  have hP : ContDiffAt ℂ 1
      (fun p : ℂ × ℂ => p.2 - 4*p.1^3 + G*p.1*p.2^2 + H*p.2^3) (0, 0) := by
    fun_prop
  have hzero : (0:ℂ) - 4*(0:ℂ)^3 + G*0*0^2 + H*0^3 = 0 := by ring
  have hD : HasDerivAt (fun w : ℂ => w - 4*(0:ℂ)^3 + G*0*w^2 + H*w^3) 1 0 := by
    convert (((hasDerivAt_id' (0:ℂ)).sub_const (4*(0:ℂ)^3)).add
      (((hasDerivAt_id' (0:ℂ)).pow 2).const_mul (G*0))).add
      (((hasDerivAt_id' (0:ℂ)).pow 3).const_mul H) using 1; norm_num
  obtain ⟨U, W, f, hU, hW, hU0, hW0, hf, hf0, hmap, hgraph⟩ :=
    SimpleRootBranches.local_simple_root_hasDerivAt hP hzero hD (by norm_num)
  refine ⟨U, W, f, hU, hW, hU0, hW0, ⟨hU, hf⟩, hf0, hmap, ?_⟩
  intro z hz w hw
  have heq : w - 4*z^3 + G*z*w^2 + H*w^3 = 0 ↔ w = 4*z^3-G*z*w^2-H*w^3 := by
    constructor <;> intro h <;> linear_combination h
  exact heq.symm.trans (hgraph z hz w hw)

/-- The cubic equation forces the full seventh-order remainder. -/
lemma infinity_expansion {G H : ℂ} {f : ℂ → ℂ}
    (hfc : ContinuousAt f 0) (hf0 : f 0 = 0)
    (heq : ∀ᶠ u in 𝓝 (0:ℂ), f u = 4*u^3-G*u*(f u)^2-H*(f u)^3) :
    (fun u => f u - 4*u^3) =O[𝓝 (0:ℂ)] (fun u => u^7) := by
  let d : ℂ → ℂ := fun u => 1 + G*u*f u + H*(f u)^2
  have hd : ContinuousAt d 0 := by dsimp [d]; fun_prop
  have hd0 : d 0 = 1 := by simp [d, hf0]
  let A : ℂ → ℂ := fun u => 4 / d u
  have hA : ContinuousAt A 0 := by
    dsimp [A]
    exact continuousAt_const.div hd (by rw [hd0]; norm_num)
  have hdnz : ∀ᶠ u in 𝓝 (0:ℂ), d u ≠ 0 := hd.eventually_ne (by rw [hd0]; norm_num)
  have hfactor : ∀ᶠ u in 𝓝 (0:ℂ), f u = u^3*A u := by
    filter_upwards [heq, hdnz] with u hu hdu
    dsimp [A]
    rw [← mul_div_assoc]
    apply (eq_div_iff hdu).2
    dsimp [d]
    linear_combination hu
  let B : ℂ → ℂ := fun u => -G*(A u)^2-H*u^2*(A u)^3
  have hB : ContinuousAt B 0 := by dsimp [B]; fun_prop
  have hbig : B =O[𝓝 (0:ℂ)] (fun _ => (1:ℂ)) :=
    isBigO_const_of_tendsto hB (by norm_num)
  have hmul := (isBigO_refl (fun u : ℂ => u^7) (𝓝 (0:ℂ))).mul hbig
  have hres : (fun u => f u - 4*u^3) =ᶠ[𝓝 (0:ℂ)] (fun u => u^7*B u) := by
    filter_upwards [heq, hfactor] with u hu hfu
    dsimp [B]
    rw [hfu] at hu ⊢
    linear_combination hu
  simpa only [mul_one] using hmul.congr' hres.symm Filter.EventuallyEq.rfl


theorem nonsingular_infinity : Specs.D12Complex.Ch22.CubicInfinityChart.nonsingular_infinity_type := by
  intro G H
  refine ⟨?_, by norm_num⟩
  convert (((hasDerivAt_id' (0:ℂ)).sub_const (4*(0:ℂ)^3)).add
    (((hasDerivAt_id' (0:ℂ)).pow 2).const_mul (G*0))).add
    (((hasDerivAt_id' (0:ℂ)).pow 3).const_mul H) using 1; norm_num

theorem infinity_graph : Specs.D12Complex.Ch22.CubicInfinityChart.infinity_graph_type := by
  intro G H
  obtain ⟨U, W, f, hU, hW, hU0, hW0, hf, hf0, hmap, hgraph⟩ :=
    local_infinity_graph G H
  refine ⟨U, W, f, hU, hU0, hW, hW0, hf, hf0, hmap, hgraph, ?_⟩
  apply infinity_expansion (hf.2 0 hU0).continuousAt hf0
  filter_upwards [hU.mem_nhds hU0] with u hu
  exact (hgraph u hu (f u) (hmap hu)).mpr rfl



private lemma holomorphic_congr {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : HolomorphicOn U f) (heq : EqOn g f U) : HolomorphicOn U g := by
  refine ⟨hf.1, fun z hz => ?_⟩
  apply (hf.2 z hz).congr_of_eventuallyEq
  filter_upwards [hf.1.mem_nhds hz] with w hw
  exact heq hw

theorem infinity_chart : Specs.D12Complex.Ch22.CubicInfinityChart.infinity_chart_type := by
  classical
  intro G H
  obtain ⟨U, W, V, hU, hU0, hW, hW0, hV, hV0, hmap, hgraph, hbig⟩ :=
    infinity_graph G H
  have hpoint (t : ℂ) (ht : t ∈ U) : OnCubic G H (infinityPoint t (V t)) :=
    (onCubic_infinityPoint_iff G H t (V t)).mpr ((hgraph t ht (V t) (hmap ht)).mpr rfl)
  let center : Cubic G H := ⟨O, O_onCubic G H⟩
  let g : ℂ → Cubic G H := fun t => if ht : t ∈ U then
    ⟨infinityPoint t (V t), hpoint t ht⟩ else center
  have hgval (t : ℂ) (ht : t ∈ U) : (g t).val = infinityPoint t (V t) := by
    simp [g, ht]
  have hgc (t : ℂ) (ht : t ∈ U) : infinityU (g t).val = t := by
    rw [hgval t ht, infinityU_infinityPoint]
  have hgv (t : ℂ) (ht : t ∈ U) : infinityV (g t).val = V t := by
    rw [hgval t ht, infinityV_infinityPoint]
  have hgd (t : ℂ) (ht : t ∈ U) : infinityV (g t).val ∈ W := by
    rw [hgv t ht]
    exact hmap ht
  have hgs : MapsTo g U (infinityPatch G H) := by
    intro t ht
    change (g t).val ∈ coordinatePatch 2
    rw [hgval t ht]
    exact infinityPoint_mem_patch t (V t)
  have hVcont : ContinuousOn V U := fun t ht => (hV.2 t ht).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g U := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (continuous_infinityPoint.comp_continuousOn (continuousOn_id.prodMk hVcont)).congr
      (fun t ht => hgval t ht)
  have hcg (p : Cubic G H) (hp : p ∈ infinityPatch G H)
      (hu : infinityU p.val ∈ U) (hv : infinityV p.val ∈ W) :
      g (infinityU p.val) = p := by
    apply Subtype.ext
    rw [hgval _ hu]
    have hcurve := (infinity_equation G H p.val hp).mp p.property
    have hvV := (hgraph _ hu _ hv).mp hcurve
    rw [← hvV]
    exact infinityPoint_coordinates hp
  let e := chartOfParametrization
    (fun p : Cubic G H => infinityU p.val) (fun p => infinityV p.val)
    (infinityPatch G H) U W g (infinityPatch_isOpen G H) hU hW
    (continuousOn_infinityU_cubic G H) (continuousOn_infinityV_cubic G H)
    hgcont hgc hgd hgs hcg
  have he : IsInfinityChart G H e := by
    refine ⟨fun p hp => hp.1, fun p hp => rfl, ?_, ?_⟩
    · exact holomorphic_congr ⟨hU, fun z hz => differentiableAt_id⟩ hgc
    · exact holomorphic_congr hV hgv
  refine ⟨U, W, V, e, hU, hU0, hW, hW0, hV, hV0, hmap, hgraph,
    hbig, he, rfl, rfl, hgval, ?_⟩
  intro p hp
  have hps : p ∈ e.source := by
    change p ∈ infinityPatch G H ∧ infinityU p.val ∈ U ∧ infinityV p.val ∈ W
    simpa only [infinityPatch, mem_ofPred_eq, hp, infinityU_O, infinityV_O] using
      (show O ∈ coordinatePatch 2 ∧ (0 : ℂ) ∈ U ∧ (0 : ℂ) ∈ W from
        ⟨O_mem_infinityPatch, hU0, hW0⟩)
  refine ⟨hps, ?_⟩
  change infinityU p.val = 0
  rw [hp, infinityU_O]

private theorem finite_to_infinity_holomorphic {G H : ℂ} {axis : Bool}
    {e f : OpenPartialHomeomorph (Cubic G H) ℂ}
    (he : IsFiniteChart G H axis e) (hf : IsInfinityChart G H f) :
    HolomorphicOn (e.symm.trans f).source (e.symm.trans f) := by
  refine ⟨(e.symm.trans f).open_source, ?_⟩
  intro z hz
  have hz' : z ∈ e.target ∧ e.symm z ∈ f.source := hz
  have hp0 : (e.symm z).val ∈ coordinatePatch 0 := he.1 (e.map_target hz'.1)
  have hp2 : (e.symm z).val ∈ coordinatePatch 2 := hf.1 hz'.2
  have hnonzero : finiteY (e.symm z).val ≠ 0 := by
    rw [← affinePoint_coordinates hp0, affinePoint_mem_infinity_iff] at hp2
    exact hp2
  apply ((he.2.2.1.2 z hz'.1).div (he.2.2.2.2 z hz'.1) hnonzero).congr_of_eventuallyEq
  filter_upwards [(e.symm.trans f).open_source.mem_nhds hz] with w hw
  have hw' : w ∈ e.target ∧ e.symm w ∈ f.source := hw
  change f (e.symm w) = finiteX (e.symm w).val / finiteY (e.symm w).val
  rw [hf.2.1 _ hw'.2]
  exact infinityU_eq_finiteX_div_finiteY (he.1 (e.map_target hw'.1))

private theorem infinity_to_finite_holomorphic {G H : ℂ} {axis : Bool}
    {e f : OpenPartialHomeomorph (Cubic G H) ℂ}
    (he : IsInfinityChart G H e) (hf : IsFiniteChart G H axis f) :
    HolomorphicOn (e.symm.trans f).source (e.symm.trans f) := by
  refine ⟨(e.symm.trans f).open_source, ?_⟩
  intro z hz
  have hz' : z ∈ e.target ∧ e.symm z ∈ f.source := hz
  have hp2 : (e.symm z).val ∈ coordinatePatch 2 := he.1 (e.map_target hz'.1)
  have hp0 : (e.symm z).val ∈ coordinatePatch 0 := hf.1 hz'.2
  have hnonzero : infinityV (e.symm z).val ≠ 0 := by
    rw [← infinityPoint_coordinates hp2, infinityPoint_mem_finite_iff] at hp0
    exact hp0
  cases axis
  · apply (differentiableAt_const (c := (1 : ℂ)) |>.div
      (he.2.2.2.2 z hz'.1) hnonzero).congr_of_eventuallyEq
    filter_upwards [(e.symm.trans f).open_source.mem_nhds hz] with w hw
    have hw' : w ∈ e.target ∧ e.symm w ∈ f.source := hw
    change f (e.symm w) = 1 / infinityV (e.symm w).val
    rw [hf.2.1 _ hw'.2]
    exact finiteY_eq_one_div_infinityV (he.1 (e.map_target hw'.1))
  · apply ((he.2.2.1.2 z hz'.1).div
      (he.2.2.2.2 z hz'.1) hnonzero).congr_of_eventuallyEq
    filter_upwards [(e.symm.trans f).open_source.mem_nhds hz] with w hw
    have hw' : w ∈ e.target ∧ e.symm w ∈ f.source := hw
    change f (e.symm w) = infinityU (e.symm w).val / infinityV (e.symm w).val
    rw [hf.2.1 _ hw'.2]
    exact finiteX_eq_infinityU_div_infinityV (he.1 (e.map_target hw'.1))

private theorem infinity_to_infinity_holomorphic {G H : ℂ}
    {e f : OpenPartialHomeomorph (Cubic G H) ℂ}
    (he : IsInfinityChart G H e) (hf : IsInfinityChart G H f) :
    HolomorphicOn (e.symm.trans f).source (e.symm.trans f) := by
  refine ⟨(e.symm.trans f).open_source, ?_⟩
  intro z hz
  have hz' : z ∈ e.target ∧ e.symm z ∈ f.source := hz
  apply (he.2.2.1.2 z hz'.1).congr_of_eventuallyEq
  filter_upwards [(e.symm.trans f).open_source.mem_nhds hz] with w hw
  have hw' : w ∈ e.target ∧ e.symm w ∈ f.source := hw
  exact hf.2.1 _ hw'.2

theorem finite_infinity_transitions :
    Specs.D12Complex.Ch22.CubicInfinityChart.finite_infinity_transitions_type := by
  intro G H axis e f he hf
  let t := e.symm.trans f
  have ht : HolomorphicOn t.source t := finite_to_infinity_holomorphic he hf
  have hti : HolomorphicOn t.target t.symm := infinity_to_finite_holomorphic hf he
  exact ⟨ht, hti, t.mapsTo, t.mapsTo_symm, t.leftInvOn, t.rightInvOn⟩

theorem infinity_transitions :
    Specs.D12Complex.Ch22.CubicInfinityChart.infinity_transitions_type := by
  intro G H e f he hf
  let t := e.symm.trans f
  have ht : HolomorphicOn t.source t := infinity_to_infinity_holomorphic he hf
  have hti : HolomorphicOn t.target t.symm := infinity_to_infinity_holomorphic hf he
  exact ⟨ht, hti, t.mapsTo, t.mapsTo_symm, t.leftInvOn, t.rightInvOn⟩

universe u
variable {X : Type u} [TopologicalSpace X]

private def Refines (c e : OpenPartialHomeomorph X ℂ) : Prop :=
  c.source ⊆ e.source ∧ c.target ⊆ e.target ∧
  (c : X → ℂ) = e ∧ (c.symm : ℂ → X) = e.symm

/-- Restriction to a coordinate disk preserves the actual coordinate functions. -/
private theorem exists_domain_subchart (e : OpenPartialHomeomorph X ℂ)
    (p : X) (hp : p ∈ e.source) :
    ∃ c : Surfaces.ComplexChart X, p ∈ c.val.source ∧ Refines c.val e := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e p) (e.map_source hp)
  let d := e.trans (OpenPartialHomeomorph.ofSet (Metric.ball (e p) r) Metric.isOpen_ball)
  have hdt : d.target = Metric.ball (e p) r := by
    change Metric.ball (e p) r ∩ id ⁻¹' e.target = Metric.ball (e p) r
    exact inter_eq_left.mpr hball
  have hdom : IsDomain d.target := by
    rw [hdt]
    exact ⟨⟨e p, Metric.mem_ball_self hr⟩, Metric.isOpen_ball,
      (convex_ball (e p) r).isPreconnected⟩
  refine ⟨⟨d, hdom⟩, ?_, ?_⟩
  · exact ⟨hp, Metric.mem_ball_self hr⟩
  · exact ⟨fun _ h => h.1, fun z hz => hball (hdt ▸ hz), rfl, rfl⟩

private theorem compatible_refinements
    {c d e f : OpenPartialHomeomorph X ℂ}
    (hce : Refines c e) (hdf : Refines d f)
    (h : BiholomorphicPair (e.symm.trans f).source (e.symm.trans f).target
      (e.symm.trans f) (e.symm.trans f).symm) :
    BiholomorphicPair (c.symm.trans d).source (c.symm.trans d).target
      (c.symm.trans d) (c.symm.trans d).symm := by
  have hc (z : ℂ) : c.symm z = e.symm z := congrFun hce.2.2.2 z
  have hd (x : X) : d x = f x := congrFun hdf.2.2.1 x
  have hct (x : X) : c x = e x := congrFun hce.2.2.1 x
  have hdi (z : ℂ) : d.symm z = f.symm z := congrFun hdf.2.2.2 z
  refine ⟨⟨(c.symm.trans d).open_source, ?_⟩,
    ⟨(c.symm.trans d).open_target, ?_⟩,
    (c.symm.trans d).mapsTo, (c.symm.trans d).mapsTo_symm,
    (c.symm.trans d).leftInvOn, (c.symm.trans d).rightInvOn⟩
  · intro z hz
    have hz' : z ∈ e.target ∧ e.symm z ∈ f.source :=
      ⟨hce.2.1 hz.1, hc z ▸ hdf.1 hz.2⟩
    exact (h.1.2 z hz').congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by
      change d (c.symm w) = f (e.symm w)
      rw [hc, hd])
  · intro z hz
    have hz' : z ∈ f.target ∧ f.symm z ∈ e.source :=
      ⟨hdf.2.1 hz.1, hdi z ▸ hce.1 hz.2⟩
    exact (h.2.1.2 z hz').congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by
      change c (d.symm w) = e (f.symm w)
      rw [hdi, hct])


private theorem regular_refinements {G H : ℂ}
    {c e : OpenPartialHomeomorph (Cubic G H) ℂ} (hce : Refines c e)
    (he : IsInfinityChart G H e ∨ ∃ axis, IsFiniteChart G H axis e) :
    IsInfinityChart G H c ∨ ∃ axis, IsFiniteChart G H axis c := by
  rcases he with he | ⟨axis, he⟩
  · left
    refine ⟨hce.1.trans he.1, ?_, ⟨c.open_target, ?_⟩, ⟨c.open_target, ?_⟩⟩
    · intro p hp
      exact (congrFun hce.2.2.1 p).trans (he.2.1 p (hce.1 hp))
    · intro z hz
      simpa only [hce.2.2.2] using he.2.2.1.2 z (hce.2.1 hz)
    · intro z hz
      simpa only [hce.2.2.2] using he.2.2.2.2 z (hce.2.1 hz)
  · right
    refine ⟨axis, hce.1.trans he.1, ?_, ⟨c.open_target, ?_⟩, ⟨c.open_target, ?_⟩⟩
    · intro p hp
      exact (congrFun hce.2.2.1 p).trans (he.2.1 p (hce.1 hp))
    · intro z hz
      simpa only [hce.2.2.2] using he.2.2.1.2 z (hce.2.1 hz)
    · intro z hz
      simpa only [hce.2.2.2] using he.2.2.2.2 z (hce.2.1 hz)

theorem complex_manifold :
    Specs.D12Complex.Ch22.CubicInfinityChart.complex_manifold_type := by
  classical
  intro ω₁ ω₂ h₁ h₂
  let G := Specs.D12Complex.Ch22.WeierstrassEquations.g₂ ω₁ ω₂
  let H := Specs.D12Complex.Ch22.WeierstrassEquations.g₃ ω₁ ω₂
  change Nonempty (Cubic G H) ∧ CompactSpace (Cubic G H) ∧ T2Space (Cubic G H) ∧
    SecondCountableTopology (Cubic G H) ∧
    ∃ A : Set (Surfaces.ComplexChart (Cubic G H)), Surfaces.IsAtlas A ∧
      ∀ e ∈ A, IsInfinityChart G H e.val ∨ ∃ axis, IsFiniteChart G H axis e.val
  let C : Set (OpenPartialHomeomorph (Cubic G H) ℂ) :=
    {e | IsInfinityChart G H e ∨ ∃ axis, IsFiniteChart G H axis e}
  have hcover : ∀ p : Cubic G H, ∃ e ∈ C, p ∈ e.source := by
    intro p
    by_cases hp : p ∈ finitePatch G H
    · obtain ⟨e, he, hc⟩ := CubicFiniteCharts.finite_charts ω₁ ω₂ h₁ h₂ p hp
      exact ⟨e, Or.inr ⟨_, hc⟩, he⟩
    · obtain ⟨U, W, V, e, hU, hU0, hW, hW0, hV, hV0, hmap, hgraph, hbig,
        he, ht, hs, hi, hO⟩ := infinity_chart G H
      have hpO : p.val = O := ((unique_infinity G H).2.2 p.val p.property).mp hp
      exact ⟨e, Or.inl he, (hO p hpO).1⟩
  have hcomp : ∀ e ∈ C, ∀ f ∈ C,
      BiholomorphicPair (e.symm.trans f).source (e.symm.trans f).target
        (e.symm.trans f) (e.symm.trans f).symm := by
    intro e he f hf
    rcases he with he | ⟨axis₁, he⟩ <;> rcases hf with hf | ⟨axis₂, hf⟩
    · exact infinity_transitions G H e f he hf
    · let t := e.symm.trans f
      have ht : HolomorphicOn t.source t := infinity_to_finite_holomorphic he hf
      have hti : HolomorphicOn t.target t.symm := finite_to_infinity_holomorphic hf he
      exact ⟨ht, hti, t.mapsTo, t.mapsTo_symm, t.leftInvOn, t.rightInvOn⟩
    · exact finite_infinity_transitions G H axis₁ e f he hf
    · exact CubicFiniteCharts.transitions G H axis₁ axis₂ e f he hf
  let A : Set (Surfaces.ComplexChart (Cubic G H)) :=
    {c | ∃ e ∈ C, Refines c.val e}
  refine ⟨⟨⟨O, O_onCubic G H⟩⟩, inferInstance, inferInstance, inferInstance, A,
    ⟨?_, ?_⟩, ?_⟩
  · intro p
    obtain ⟨e, he, hp⟩ := hcover p
    obtain ⟨c, hc, hce⟩ := exists_domain_subchart e p hp
    exact ⟨c, ⟨e, he, hce⟩, hc⟩
  · rintro c ⟨e, he, hce⟩ d ⟨f, hf, hdf⟩
    exact compatible_refinements hce hdf (hcomp e he f hf)
  · rintro c ⟨e, he, hce⟩
    exact regular_refinements hce he


end D12Complex.CubicInfinityChart

namespace D12Complex.CubicInfinityChart.Definitions
abbrev O : Specs.D12Complex.Ch22.CubicInfinityChart.O_type :=
  D12Complex.CubicInfinityChart.O
abbrev infinityU : Specs.D12Complex.Ch22.CubicInfinityChart.infinityU_type :=
  D12Complex.CubicInfinityChart.infinityU
abbrev infinityV : Specs.D12Complex.Ch22.CubicInfinityChart.infinityV_type :=
  D12Complex.CubicInfinityChart.infinityV
abbrev infinityPoint : Specs.D12Complex.Ch22.CubicInfinityChart.infinityPoint_type :=
  D12Complex.CubicInfinityChart.infinityPoint
abbrev infinityPatch : Specs.D12Complex.Ch22.CubicInfinityChart.infinityPatch_type :=
  D12Complex.CubicInfinityChart.infinityPatch
abbrev IsInfinityChart : Specs.D12Complex.Ch22.CubicInfinityChart.IsInfinityChart_type :=
  D12Complex.CubicInfinityChart.IsInfinityChart
end D12Complex.CubicInfinityChart.Definitions
