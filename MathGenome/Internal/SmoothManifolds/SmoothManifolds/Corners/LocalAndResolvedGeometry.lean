import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Real.Sign

/-! Corner models, intrinsic face germs, resolved smooth faces, and box/simplex
charts for M10.06. General products and outward-first orientations are separate goals. -/
namespace SmoothManifolds.Corners
open ModelData CornerData Set Filter
open scoped Topology
universe u

private theorem forwardVelocity_mem_cone {n : ℕ} {k : Fin (n + 1)}
    {s : Set (Orthant n k)} {x : Orthant n k} {v : Euclidean n}
    (h : IsForwardVelocity s x v) : v ∈ modelCone x := by
  rcases h with ⟨c, hc0, hc, hs⟩
  intro i hi hxi
  have hd := (hasDerivWithinAt_pi.mp hc i).mono Ioi_subset_Ici_self
  have hlim := (hasDerivWithinAt_iff_tendsto_slope'
    (by simp : (0 : ℝ) ∉ Ioi (0 : ℝ))).mp hd
  apply ge_of_tendsto hlim
  have hs' := hs.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  filter_upwards [hs', self_mem_nhdsWithin] with t ht htp
  rcases ht with ⟨y, hy, hcy⟩
  have hnonneg : 0 ≤ c t i := by
    rw [← hcy]
    exact y.property i hi
  simpa [slope_def_field, hc0, hxi] using div_nonneg hnonneg (le_of_lt htp)

private theorem ray_eventually_mem_model {n : ℕ} {k : Fin (n + 1)}
    (x : Orthant n k) {v : Euclidean n} (hv : v ∈ modelCone x) :
    ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, x.val + t • v ∈ orthantSet n k := by
  have heach : ∀ i : Fin n, ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0,
      i.val < k.val → 0 ≤ (x.val + t • v) i := by
    intro i
    by_cases hi : i.val < k.val
    · by_cases hx : x.val i = 0
      · filter_upwards [self_mem_nhdsWithin] with t ht _
        change 0 ≤ x.val i + t * v i
        rw [hx, zero_add]
        exact mul_nonneg ht (hv i hi hx)
      · have hpos : 0 < x.val i := lt_of_le_of_ne (x.property i hi) (Ne.symm hx)
        have hcont : Continuous (fun t : ℝ => x.val i + t * v i) := by fun_prop
        have he : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < x.val i + t * v i :=
          hcont.continuousAt.eventually (by simpa using lt_mem_nhds hpos)
        filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht _
        exact le_of_lt ht
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hi h))
  filter_upwards [Filter.eventually_all.mpr heach] with t ht
  exact ht

private theorem cone_has_smooth_velocity {n : ℕ} {k : Fin (n + 1)}
    {s : Set (Orthant n k)} (hs : IsOpen s) (x : Orthant n k) (hx : x ∈ s)
    {v : Euclidean n} (hv : v ∈ modelCone x) : IsSmoothForwardVelocity s x v := by
  rcases isOpen_induced_iff.mp hs with ⟨U, hU, hUs⟩
  have hxU : x.val ∈ U := by
    change x ∈ Subtype.val ⁻¹' U
    rw [hUs]
    exact hx
  have hray : Continuous (fun t : ℝ => x.val + t • v) := by fun_prop
  have heU : ∀ᶠ t in 𝓝 (0 : ℝ), x.val + t • v ∈ U :=
    hray.continuousAt.eventually (by simpa using hU.mem_nhds hxU)
  refine ⟨fun t => x.val + t • v, by simp, ?_, ?_, ?_⟩
  · exact (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt
  · simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add x.val
  · filter_upwards [ray_eventually_mem_model x hv,
      heU.filter_mono nhdsWithin_le_nhds] with t ht htU
    refine ⟨⟨x.val + t • v, ht⟩, ?_, rfl⟩
    rw [← hUs]
    exact htU

private theorem velocity_cone :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_velocity_coneType := by
  intro n k s hs x hx v
  have hforget : IsSmoothForwardVelocity s x v → IsForwardVelocity s x v := by
    rintro ⟨c, h0, _, hc, hs⟩
    exact ⟨c, h0, hc.hasDerivWithinAt, hs⟩
  exact ⟨⟨forwardVelocity_mem_cone, fun h => hforget (cone_has_smooth_velocity hs x hx h)⟩,
    ⟨fun h => forwardVelocity_mem_cone (hforget h), cone_has_smooth_velocity hs x hx⟩⟩

private theorem lineality :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_linealityType := by
  intro n k x
  have heq : ∀ v, v ∈ modelLineality x ↔ v ∈ modelCone x ∧ -v ∈ modelCone x := by
    intro v
    constructor
    · intro hv
      constructor
      · intro i hi hx
        rw [hv i hi hx]
      · intro i hi hx
        change 0 ≤ -(v i)
        rw [hv i hi hx, neg_zero]
    · intro hv i hi hx
      exact le_antisymm (neg_nonneg.mp (hv.2 i hi hx)) (hv.1 i hi hx)
  refine ⟨heq, ?_⟩
  intro L hL v hv
  exact (heq v).mpr ⟨hL hv, hL (L.neg_mem hv)⟩

private theorem lineality_codimension :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_lineality_codimensionType := by
  classical
  intro n k x
  let A := activeCoordinates x
  let r : Euclidean n →ₗ[ℝ] (A → ℝ) := {
    toFun := fun v i => v i.val
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hr : Function.Surjective r := by
    intro z
    refine ⟨fun i => if hi : i ∈ A then z ⟨i, hi⟩ else 0, ?_⟩
    funext i
    exact dite_eq_left i.property
  have hker : LinearMap.ker r = modelLineality x := by
    ext v
    constructor
    · intro hv i hi hx
      have hz := congrFun (LinearMap.mem_ker.mp hv) ⟨i, by simp [A, activeCoordinates, hi, hx]⟩
      exact hz
    · intro hv
      apply LinearMap.mem_ker.mpr
      funext i
      have hi := (Finset.mem_filter.mp i.property).2
      exact hv i.val hi.1 hi.2
  rw [← hker]
  calc
    Module.finrank ℝ (Euclidean n ⧸ LinearMap.ker r) =
        Module.finrank ℝ (A → ℝ) := (r.quotKerEquivOfSurjective hr).finrank_eq
    _ = modelDepth x := by simp [A, modelDepth]

private theorem uniqueDiffOn_orthant {n : ℕ} (k : Fin (n + 1)) :
    UniqueDiffOn ℝ (orthantSet n k) := by
  have heq : orthantSet n k = Set.pi {i : Fin n | i.val < k.val} (fun _ => Ici (0 : ℝ)) := rfl
  rw [heq]
  exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Ici 0)

private theorem uniqueDiffOn_orthantDomain {n : ℕ} {k : Fin (n + 1)}
    {s : Set (Orthant n k)} (hs : IsOpen s) :
    UniqueDiffOn ℝ (Subtype.val '' s : Set (Euclidean n)) := by
  obtain ⟨U, hU, hEq⟩ := hs.image_val
  rw [hEq, inter_comm]
  exact (uniqueDiffOn_orthant k).inter hU

private theorem extension_maps_cone {n : ℕ} {k l : Fin (n + 1)}
    (e : OpenPartialHomeomorph (Orthant n k) (Orthant n l))
    (x : Orthant n k) (hx : x ∈ e.source) (H : OrthantExtension e.source e x)
    {v : Euclidean n} (hv : v ∈ modelCone x) :
    fderiv ℝ H.map x.val v ∈ modelCone (e x) := by
  rcases cone_has_smooth_velocity e.open_source x hx hv with ⟨c, hc0, _, hc, hs⟩
  have hd : DifferentiableAt ℝ H.map x.val :=
    (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt (by simp)
  have hcU : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ H.domain :=
    hc.continuousAt.eventually (by simpa [hc0] using H.isOpen_domain.mem_nhds H.mem_domain)
  apply forwardVelocity_mem_cone (s := e.target)
  refine ⟨H.map ∘ c, ?_, ?_, ?_⟩
  · simpa [Function.comp_def, hc0] using H.agrees x hx H.mem_domain
  · have hd' : HasFDerivAt H.map (fderiv ℝ H.map x.val) (c 0) := by
      rw [hc0]
      exact hd.hasFDerivAt
    have hh := hd'.comp_hasDerivAt (0 : ℝ) hc
    exact hh.hasDerivWithinAt
  · filter_upwards [hs, hcU.filter_mono nhdsWithin_le_nhds] with t ht htU
    rcases ht with ⟨y, hy, hyc⟩
    refine ⟨e y, e.map_source hy, ?_⟩
    change (e y).val = H.map (c t)
    rw [← hyc]
    exact (H.agrees y hy (by rwa [hyc])).symm

private theorem extension_comp_derivative {n : ℕ} {k l : Fin (n + 1)}
    (e : OpenPartialHomeomorph (Orthant n k) (Orthant n l))
    (x : Orthant n k) (hx : x ∈ e.source)
    (H : OrthantExtension e.source e x)
    (G : OrthantExtension e.target e.symm (e x)) :
    (fderiv ℝ G.map (e x).val).comp (fderiv ℝ H.map x.val) =
      ContinuousLinearMap.id ℝ (Euclidean n) := by
  have hHx : H.map x.val = (e x).val := H.agrees x hx H.mem_domain
  have hH : DifferentiableAt ℝ H.map x.val :=
    (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ G.map (e x).val :=
    (G.smooth.contDiffAt (G.isOpen_domain.mem_nhds G.mem_domain)).differentiableAt (by simp)
  have heq : (G.map ∘ H.map) =ᶠ[𝓝[Subtype.val '' e.source] x.val] id := by
    have hHU : ∀ᶠ z in 𝓝 x.val, z ∈ H.domain := H.isOpen_domain.mem_nhds H.mem_domain
    have hGV : ∀ᶠ z in 𝓝 x.val, H.map z ∈ G.domain :=
      hH.continuousAt.eventually (by simpa [hHx] using G.isOpen_domain.mem_nhds G.mem_domain)
    filter_upwards [self_mem_nhdsWithin, hHU.filter_mono nhdsWithin_le_nhds,
      hGV.filter_mono nhdsWithin_le_nhds] with z hz hzU hzV
    rcases hz with ⟨y, hy, rfl⟩
    change G.map (H.map y.val) = y.val
    have hHy := H.agrees y hy hzU
    rw [hHy, G.agrees (e y) (e.map_source hy) (by rwa [← hHy]), e.left_inv hy]
  have hG' : DifferentiableAt ℝ G.map (H.map x.val) := hHx.symm ▸ hG
  have hd : HasFDerivWithinAt (G.map ∘ H.map)
      ((fderiv ℝ G.map (H.map x.val)).comp (fderiv ℝ H.map x.val))
      (Subtype.val '' e.source) x.val :=
    (hG'.hasFDerivAt.comp x.val hH.hasFDerivAt).hasFDerivWithinAt
  have hd' := hd.congr_of_eventuallyEq heq.symm (by
    change x.val = G.map (H.map x.val)
    rw [hHx, G.agrees (e x) (e.map_source hx) G.mem_domain, e.left_inv hx])
  have hu := uniqueDiffOn_orthantDomain e.open_source x.val ⟨x, hx, rfl⟩
  simpa only [hHx] using hu.eq hd' (hasFDerivAt_id x.val).hasFDerivWithinAt

private theorem cone_equiv_depth {n : ℕ} {k l : Fin (n + 1)}
    (x : Orthant n k) (y : Orthant n l) (E : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (hE : E '' modelCone x = modelCone y) : modelDepth x = modelDepth y := by
  have hiff (v : Euclidean n) : E v ∈ modelCone y ↔ v ∈ modelCone x := by
    rw [← hE]
    constructor
    · rintro ⟨w, hw, hEq⟩
      rwa [E.injective hEq] at hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  have hlin (v : Euclidean n) : E v ∈ modelLineality y ↔ v ∈ modelLineality x := by
    rw [(lineality y).1, (lineality x).1]
    simpa only [map_neg] using and_congr (hiff v) (hiff (-v))
  have hmap : (modelLineality x).map E.toLinearMap = modelLineality y := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hlin v).mpr hv
    · intro hw
      refine ⟨E.symm w, ?_, E.apply_symm_apply w⟩
      exact (hlin (E.symm w)).mp (by simpa using hw)
  rw [← lineality_codimension x, ← lineality_codimension y]
  exact (Submodule.Quotient.equiv (modelLineality x) (modelLineality y) E hmap).finrank_eq

private theorem transition_cone_proof :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.transition_coneType := by
  intro n k l e _he hge x hx H
  rcases hge ⟨e x, e.map_source hx⟩ with ⟨V, hV, hxV, g, hg, hgeq⟩
  let G : OrthantExtension e.target e.symm (e x) := {
    domain := V
    isOpen_domain := hV
    mem_domain := hxV
    map := g
    smooth := hg
    agrees := fun y hy hyV => hgeq ⟨y, hy⟩ hyV }
  have hGF := extension_comp_derivative e x hx H G
  have hFG : (fderiv ℝ H.map x.val).comp (fderiv ℝ G.map (e x).val) =
      ContinuousLinearMap.id ℝ (Euclidean n) := by
    let H' : OrthantExtension e.symm.target e.symm.symm (e.symm (e x)) := {
      domain := H.domain
      isOpen_domain := H.isOpen_domain
      mem_domain := by simpa only [e.left_inv hx] using H.mem_domain
      map := H.map
      smooth := H.smooth
      agrees := H.agrees }
    simpa only [e.left_inv hx] using
      extension_comp_derivative e.symm (e x) (e.map_source hx) G H'
  let E : Euclidean n ≃L[ℝ] Euclidean n := {
    toLinearEquiv := {
      toLinearMap := (fderiv ℝ H.map x.val).toLinearMap
      invFun := fderiv ℝ G.map (e x).val
      left_inv := fun v => DFunLike.congr_fun hGF v
      right_inv := fun v => DFunLike.congr_fun hFG v }
    continuous_toFun := (fderiv ℝ H.map x.val).continuous
    continuous_invFun := (fderiv ℝ G.map (e x).val).continuous }
  have hcone : E '' modelCone x = modelCone (e x) := by
    apply Set.Subset.antisymm
    · rintro w ⟨v, hv, rfl⟩
      exact extension_maps_cone e x hx H hv
    · intro w hw
      refine ⟨E.symm w, ?_, E.apply_symm_apply w⟩
      change (fderiv ℝ G.map (e x).val) w ∈ modelCone x
      have hh := extension_maps_cone e.symm (e x) (e.map_source hx) G hw
      simpa only [e.left_inv hx] using hh
  exact ⟨E, rfl, hcone, cone_equiv_depth x (e x) E.toLinearEquiv hcone⟩

private theorem chart_depth_proof :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.chart_depthType := by
  intro n M _ S c d hc hd p hp hq
  let e := c.2.symm.trans d.2
  have hcompat := S.maximal.1.2 c hc d hd
  have hxe : c.2 p ∈ e.source := by
    refine ⟨c.2.map_source hp, ?_⟩
    change c.2.symm (c.2 p) ∈ d.2.source
    rwa [c.2.left_inv hp]
  rcases hcompat.1 ⟨c.2 p, hxe⟩ with ⟨U, hU, hxU, f, hf, hfeq⟩
  let H : OrthantExtension e.source e (c.2 p) := {
    domain := U
    isOpen_domain := hU
    mem_domain := hxU
    map := f
    smooth := hf
    agrees := fun y hy hyU => hfeq ⟨y, hy⟩ hyU }
  obtain ⟨E, hE, hcone, hdepth⟩ := transition_cone_proof e hcompat.1 hcompat.2 (c.2 p) hxe H
  simpa only [e, OpenPartialHomeomorph.trans_apply, c.2.left_inv hp] using hdepth

private theorem coordinate_germs_injective_proof :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.coordinate_germs_injectiveType := by
  classical
  intro n k x i j hg
  apply Subtype.ext
  by_contra hij
  have hxi := (Finset.mem_filter.mp i.property).2.2
  have hxj := (Finset.mem_filter.mp j.property).2.2
  let q : ℝ → Orthant n k := fun t =>
    ⟨Function.update x.val j.val (x.val j.val + |t|), by
      intro r hr
      by_cases he : r = j.val
      · subst r
        simp only [Function.update_self]
        exact add_nonneg (x.property j.val hr) (abs_nonneg t)
      · rw [Function.update_of_ne he]
        exact x.property r hr⟩
  have hq0 : q 0 = x := by
    apply Subtype.ext
    simp [q]
  have hqcv : Continuous (fun t : ℝ => Function.update x.val j.val (x.val j.val + |t|)) :=
    (continuous_const : Continuous (fun _ : ℝ => x.val)).update j.val
      (continuous_const.add continuous_abs)
  have hqc : Continuous q := hqcv.subtype_mk _
  have hqt : Tendsto q (𝓝 (0 : ℝ)) (𝓝 x) := by
    simpa only [hq0] using hqc.tendsto (0 : ℝ)
  have heq := (Filter.Germ.coe_eq.mp hg).comp_tendsto hqt
  have heq' := heq.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  obtain ⟨t, ht, htp⟩ := (heq'.and self_mem_nhdsWithin).exists
  have hleft : (q t).val i.val = 0 := by
    simpa only [q, Function.update_of_ne hij] using hxi
  have hright : (q t).val j.val ≠ 0 := by
    simpa only [q, Function.update_self, hxj, zero_add, abs_of_pos htp] using ne_of_gt htp
  change ((q t).val i.val = 0) = ((q t).val j.val = 0) at ht
  exact hright (Eq.mp ht hleft)

private theorem model_face_projection_proper_proof :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_face_projection_properType := by
  intro n k
  have heq : {z : Orthant n k × Fin n | z.2.val < k.val ∧ z.1.val z.2 = 0} =
      ⋃ i : {i : Fin n // i.val < k.val},
        ({x : Orthant n k | x.val i.val = 0} ×ˢ ({i.val} : Set (Fin n))) := by
    ext ⟨x, j⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hj, hx⟩
      exact ⟨⟨j, hj⟩, hx, rfl⟩
    · rintro ⟨i, hx, rfl⟩
      exact ⟨i.property, hx⟩
  have hclosed : IsClosed {z : Orthant n k × Fin n | z.2.val < k.val ∧ z.1.val z.2 = 0} := by
    rw [heq]
    apply isClosed_iUnion_of_finite
    intro i
    exact (isClosed_eq ((continuous_apply i.val).comp continuous_subtype_val)
      continuous_const).prod isClosed_singleton
  exact isProperMap_fst_of_compactSpace.restrict hclosed

private theorem zero_faces_proof :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.zero_facesType := by
  intro M _ S
  refine ⟨?_⟩
  rintro ⟨p, g, c, hc, hp, i, _⟩
  exact Fin.elim0 i

private theorem succAbove_lt_constraint {n : ℕ} (k : Fin (n + 2))
    (i : Fin (n + 1)) (hi : i.val < k.val) (j : Fin n) :
    (i.succAbove j).val < k.val ↔ j.val < (faceConstraintCount k).val := by
  change (i.succAbove j).val < k.val ↔ j.val < k.val - 1
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ hji]
    have hj : j.val < i.val := hji
    simp only [Fin.val_castSucc]
    omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hji)]
    simp only [Fin.val_succ]
    omega

private theorem coordinate_face_chart_proof :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.coordinate_face_chartType := by
  intro n k i hi
  let Face := {x : Orthant (n + 1) k // x.val i = 0}
  let d : Face → Orthant n (faceConstraintCount k) := fun x =>
    ⟨i.removeNth x.val.val, fun j hj =>
      x.val.property (i.succAbove j) ((succAbove_lt_constraint k i hi j).mpr hj)⟩
  have hins_mem (y : Orthant n (faceConstraintCount k)) :
      i.insertNth (0 : ℝ) y.val ∈ orthantSet (n + 1) k := by
    intro r
    refine Fin.succAboveCases i ?_ ?_ r
    · intro _
      simp
    · intro j hj
      rw [Fin.insertNth_apply_succAbove]
      exact y.property j ((succAbove_lt_constraint k i hi j).mp hj)
  let a : Orthant n (faceConstraintCount k) → Face := fun y =>
    ⟨⟨i.insertNth (0 : ℝ) y.val, hins_mem y⟩, by simp⟩
  have hdcont : Continuous d := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun j => (continuous_apply (i.succAbove j)).comp
      (continuous_subtype_val.comp continuous_subtype_val))
  have hacont : Continuous a := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact Continuous.finInsertNth i continuous_const continuous_subtype_val
  let h : Face ≃ₜ Orthant n (faceConstraintCount k) := {
    toFun := d
    invFun := a
    left_inv := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact Fin.insertNth_eq_iff.mpr ⟨x.property.symm, rfl⟩
    right_inv := by
      intro y
      apply Subtype.ext
      exact Fin.removeNth_insertNth (α := fun _ : Fin (n + 1) => ℝ) i 0 y.val
    continuous_toFun := hdcont
    continuous_invFun := hacont }
  refine ⟨h, fun _ _ => rfl, fun _ => rfl, ?_, ?_⟩
  · apply contDiff_pi.mpr
    intro r
    refine Fin.succAboveCases i ?_ ?_ r
    · simpa only [Fin.insertNth_apply_same] using
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Euclidean n => (0 : ℝ)))
    · intro j
      simpa only [Fin.insertNth_apply_succAbove] using
        (contDiff_apply ℝ (fun _ : Fin n => ℝ) j :
          ContDiff ℝ (⊤ : ℕ∞) (fun y : Euclidean n => y j))
  · apply contDiff_pi.mpr
    intro j
    exact contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) (i.succAbove j)

private theorem model_face_compact_support_proof :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_face_compact_supportType := by
  intro n k F _ s hs
  have hp := model_face_projection_proper_proof n k
  have hsub : sectionSupport (fun q : ModelFaceSheets n k => s (modelFaceProjection q)) ⊆
      modelFaceProjection ⁻¹' sectionSupport s := by
    apply closure_minimal
    · intro q hq
      exact subset_closure hq
    · exact isClosed_closure.preimage hp.continuous
  exact (hp.isCompact_preimage hs).of_isClosed_subset isClosed_closure hsub

theorem cornerCompatible_symm {n : ℕ} {M : Type u} [TopologicalSpace M]
    {c d : CornerChart n M} (h : CornerCompatible c d) : CornerCompatible d c := by
  have he : d.2.symm.trans c.2 = (c.2.symm.trans d.2).symm := by
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  unfold CornerCompatible
  rw [he]
  exact h.symm

theorem cornerCompatible_refl {n : ℕ} {M : Type u} [TopologicalSpace M]
    (c : CornerChart n M) : CornerCompatible c c := by
  constructor
  · intro x
    refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
    intro y _
    change y.val.val = (c.2 (c.2.symm y.val)).val
    rw [c.2.right_inv y.property.1]
  · intro x
    refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
    intro y _
    change y.val.val = (c.2 (c.2.symm y.val)).val
    rw [c.2.right_inv y.property.1]

/-- Two charts compatible with every chart of a covering family are compatible. -/
theorem cornerCompatible_of_cover {n : ℕ} {M : Type u} [TopologicalSpace M]
    {A : Set (CornerChart n M)}
    (hcover : ∀ p : M, ∃ a ∈ A, p ∈ a.2.source)
    {c d : CornerChart n M}
    (hc : ∀ a ∈ A, CornerCompatible c a)
    (hd : ∀ a ∈ A, CornerCompatible d a) : CornerCompatible c d := by
  have forward : ∀ {c d : CornerChart n M},
      (∀ a ∈ A, CornerCompatible c a) →
      (∀ a ∈ A, CornerCompatible d a) →
      OrthantMapContDiffOn (⊤ : ℕ∞) (c.2.symm.trans d.2).source
        (fun x => (c.2.symm.trans d.2) x.val) := by
    intro c d hc hd x
    let p := c.2.symm x.val
    have hpc : p ∈ c.2.source := c.2.symm.map_source x.property.1
    have hpd : p ∈ d.2.source := x.property.2
    obtain ⟨a, ha, hpa⟩ := hcover p
    let f := c.2.symm.trans a.2
    let g := a.2.symm.trans d.2
    have hxf : x.val ∈ f.source := ⟨x.property.1, hpa⟩
    have hfg : f x.val ∈ g.source := by
      constructor
      · exact a.2.map_source hpa
      · change a.2.symm (a.2 p) ∈ d.2.source
        rwa [a.2.left_inv hpa]
    obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := (hc a ha).1 ⟨x.val, hxf⟩
    obtain ⟨V, hV, hxV, G, hG, hGeq⟩ := (cornerCompatible_symm (hd a ha)).1 ⟨f x.val, hfg⟩
    obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp f.open_source
    have hxW : x.val.val ∈ W := by rw [← hWeq] at hxf; exact hxf
    refine ⟨(U ∩ W) ∩ F ⁻¹' V,
      (hF.mono inter_subset_left).continuousOn.isOpen_inter_preimage (hU.inter hW) hV,
      ⟨⟨hxU, hxW⟩, ?_⟩, G ∘ F,
      hG.comp (hF.mono (inter_subset_left.trans inter_subset_left)) (fun _ hy => hy.2), ?_⟩
    · change F x.val.val ∈ V
      rwa [hFeq ⟨x.val, hxf⟩ hxU]
    · intro y hy
      have hyf : y.val ∈ f.source := by rw [← hWeq]; exact hy.1.2
      have hpy : c.2.symm y.val ∈ a.2.source := hyf.2
      have hfyg : f y.val ∈ g.source := by
        constructor
        · exact a.2.map_source hpy
        · change a.2.symm (a.2 (c.2.symm y.val)) ∈ d.2.source
          rw [a.2.left_inv hpy]
          exact y.property.2
      change G (F y.val.val) = (d.2 (c.2.symm y.val)).val
      rw [hFeq ⟨y.val, hyf⟩ hy.1.1]
      have hV' : (f y.val).val ∈ V := by
        have hyV := hy.2
        change F y.val.val ∈ V at hyV
        rwa [hFeq ⟨y.val, hyf⟩ hy.1.1] at hyV
      rw [hGeq ⟨f y.val, hfyg⟩ hV']
      change (d.2 (a.2.symm (a.2 (c.2.symm y.val)))).val = _
      rw [a.2.left_inv hpy]
  refine ⟨forward hc hd, ?_⟩
  have h := forward hd hc
  have he : d.2.symm.trans c.2 = (c.2.symm.trans d.2).symm := by
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  rw [he] at h
  exact h

theorem cornerAtlas_subset_maximalExtension {n : ℕ} {M : Type u} [TopologicalSpace M]
    {A : Set (CornerChart n M)} (hA : IsSmoothCornerAtlas A) :
    A ⊆ cornerMaximalExtension A := by
  intro c hc a ha
  exact hA.2 c hc a ha

theorem cornerMaximalExtension_isSmoothAtlas {n : ℕ} {M : Type u} [TopologicalSpace M]
    {A : Set (CornerChart n M)} (hA : IsSmoothCornerAtlas A) :
    IsSmoothCornerAtlas (cornerMaximalExtension A) := by
  constructor
  · intro p
    obtain ⟨c, hc, hpc⟩ := hA.1 p
    exact ⟨c, cornerAtlas_subset_maximalExtension hA hc, hpc⟩
  · intro c hc d hd
    exact cornerCompatible_of_cover hA.1 hc hd

theorem cornerMaximalExtension_isMaximal {n : ℕ} {M : Type u} [TopologicalSpace M]
    {A : Set (CornerChart n M)} (hA : IsSmoothCornerAtlas A) :
    IsMaximalSmoothCornerAtlas (cornerMaximalExtension A) := by
  refine ⟨cornerMaximalExtension_isSmoothAtlas hA, ?_⟩
  intro B hB hAB
  apply Set.Subset.antisymm _ hAB
  intro c hc a ha
  exact hB.2 c hc a (hAB (cornerAtlas_subset_maximalExtension hA ha))


/-- A linear isomorphism of positive orthants permutes the coordinate rays,
with strictly positive scale factors. No matrix sparsity is assumed. -/
theorem positive_linearEquiv_coordinates {α β : Type*} [Fintype α] [Fintype β]
    (E : (α → ℝ) ≃ₗ[ℝ] (β → ℝ))
    (hE : ∀ v, (∀ i, 0 ≤ v i) ↔ ∀ j, 0 ≤ E v j) :
    ∃ σ : β ≃ α, ∃ a : β → ℝ, (∀ j, 0 < a j) ∧
      ∀ v j, E v j = a j * v (σ j) := by
  classical
  let A : β → α → ℝ := fun j i => E (Pi.single i 1) j
  let B : α → β → ℝ := fun i j => E.symm (Pi.single j 1) i
  have hA : ∀ j i, 0 ≤ A j i := by
    intro j i
    exact (hE _).mp (by intro r; simp [Pi.single_apply]; split_ifs <;> norm_num) j
  have hB : ∀ i j, 0 ≤ B i j := by
    intro i j
    have hn : ∀ r : β, 0 ≤ (Pi.single j (1 : ℝ) : β → ℝ) r := by
      intro r
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    exact (hE (E.symm (Pi.single j 1))).mpr
      (by simpa only [E.apply_symm_apply] using hn) i
  have hexpand (v : α → ℝ) (j : β) : E v j = ∑ i, A j i * v i := by
    have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
      funext r
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, A]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hexpand' (v : β → ℝ) (i : α) : E.symm v i = ∑ j, B i j * v j := by
    have hv : v = ∑ j, v j • Pi.single j (1 : ℝ) := by
      funext r
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, B]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hrow (j : β) : ∃ i : α, 0 < A j i ∧ ∀ r, r ≠ i → A j r = 0 := by
    have hsum : ∑ i, A j i * B i j = 1 := by
      simpa [B] using (hexpand (E.symm (Pi.single j 1)) j).symm
    have hpos : 0 < ∑ i, A j i * B i j := by rw [hsum]; norm_num
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun i _ => mul_nonneg (hA j i) (hB i j))).mp hpos
    have hai : 0 < A j i := (mul_pos_iff.mp hi).elim And.left
      (fun h => False.elim ((not_lt_of_ge (hA j i)) h.1))
    have hbi : 0 < B i j := (mul_pos_iff.mp hi).elim And.right
      (fun h => False.elim ((not_lt_of_ge (hB i j)) h.2))
    refine ⟨i, hai, ?_⟩
    intro r hri
    have hz : ∑ k, B i k * A k r = 0 := by
      simpa [A, Pi.single_eq_of_ne (Ne.symm hri)] using
        (hexpand' (E (Pi.single r 1)) i).symm
    have hterm : B i j * A j r = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => mul_nonneg (hB i k) (hA k r))).mp hz j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hbi)
  choose f hf hfzero using hrow
  let a : β → ℝ := fun j => A j (f j)
  have heval (v : α → ℝ) (j : β) : E v j = a j * v (f j) := by
    rw [hexpand]
    exact Fintype.sum_eq_single (f j) (fun r hr => by rw [hfzero j r hr, zero_mul])
  have hfinj : Function.Injective f := by
    intro j k hjk
    by_contra hne
    let v := E.symm (Pi.single j (1 : ℝ))
    have hj : 1 = a j * v (f j) := by simpa [v] using heval v j
    have hk : 0 = a k * v (f j) := by
      simpa [v, hjk, Pi.single_eq_of_ne (Ne.symm hne)] using heval v k
    have hv : v (f j) = 0 := (mul_eq_zero.mp hk.symm).resolve_left (ne_of_gt (hf k))
    rw [hv, mul_zero] at hj
    exact one_ne_zero hj
  have hfsurj : Function.Surjective f := by
    intro i
    by_contra hi
    have hi' : ∀ j, f j ≠ i := by simpa only [not_exists] using hi
    have hz : E (Pi.single i (1 : ℝ)) = 0 := by
      funext j
      simp [heval, Pi.single_eq_of_ne (hi' j)]
    have hv : Pi.single i (1 : ℝ) = (0 : α → ℝ) := E.injective (by simpa using hz)
    have := congrFun hv i
    simpa using this
  exact ⟨Equiv.ofBijective f ⟨hfinj, hfsurj⟩, a, hf, heval⟩

/-- Cone isomorphisms preserve the largest linear subspaces. -/
theorem cone_equiv_lineality {n : ℕ} {k l : Fin (n + 1)}
    (x : Orthant n k) (y : Orthant n l) (E : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (hE : E '' modelCone x = modelCone y) (v : Euclidean n) :
    E v ∈ modelLineality y ↔ v ∈ modelLineality x := by
  have hiff (w : Euclidean n) : E w ∈ modelCone y ↔ w ∈ modelCone x := by
    rw [← hE]
    constructor
    · rintro ⟨z, hz, he⟩
      rwa [E.injective he] at hz
    · exact fun hw => ⟨w, hw, rfl⟩
  rw [(lineality y).1, (lineality x).1]
  simpa only [map_neg] using and_congr (hiff v) (hiff (-v))

/-- The action on active normal coordinates is an isomorphism of full positive
orthants. Applying the positive-orthant classification gives the facet bijection. -/
theorem cone_facets :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.cone_facetsType := by
  classical
  intro n k l x y E hE
  let r {m : Fin (n+1)} (z : Orthant n m) :
      Euclidean n →ₗ[ℝ] (activeCoordinates z → ℝ) := {
    toFun := fun v i => v i.val
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  let s {m : Fin (n+1)} (z : Orthant n m) :
      (activeCoordinates z → ℝ) →ₗ[ℝ] Euclidean n := {
    toFun := fun v i => if hi : i ∈ activeCoordinates z then v ⟨i, hi⟩ else 0
    map_add' := by intro v w; funext i; dsimp; split_ifs <;> simp
    map_smul' := by intro a v; funext i; dsimp; split_ifs <;> simp }
  have hrs {m : Fin (n+1)} (z : Orthant n m) (v : activeCoordinates z → ℝ) :
      r z (s z v) = v := by
    funext i
    exact dite_eq_left i.property
  have hrzero {m : Fin (n+1)} (z : Orthant n m) (v : Euclidean n) :
      r z v = 0 ↔ v ∈ modelLineality z := by
    constructor
    · intro hv i hi hz
      exact congrFun hv ⟨i, by simp [activeCoordinates, hi, hz]⟩
    · intro hv
      funext i
      have hi := (Finset.mem_filter.mp i.property).2
      exact hv i.val hi.1 hi.2
  have hrcone {m : Fin (n+1)} (z : Orthant n m) (v : Euclidean n) :
      (∀ i, 0 ≤ r z v i) ↔ v ∈ modelCone z := by
    constructor
    · intro hv i hi hz
      exact hv ⟨i, by simp [activeCoordinates, hi, hz]⟩
    · intro hv i
      have hi := (Finset.mem_filter.mp i.property).2
      exact hv i.val hi.1 hi.2
  have hresidual (v : Euclidean n) : v - s x (r x v) ∈ modelLineality x := by
    apply (hrzero x _).mp
    rw [map_sub, hrs, sub_self]
  have hfactor (v : Euclidean n) : r y (E (s x (r x v))) = r y (E v) := by
    have hh := (hrzero y _).mpr
      ((cone_equiv_lineality x y E hE _).mpr (hresidual v))
    rw [map_sub, map_sub] at hh
    exact (sub_eq_zero.mp hh).symm
  let L : (activeCoordinates x → ℝ) →ₗ[ℝ] (activeCoordinates y → ℝ) :=
    (r y).comp (E.toLinearMap.comp (s x))
  have hL : Function.Bijective L := by
    constructor
    · intro v w hvw
      have hz : L (v-w) = 0 := by rw [map_sub, hvw, sub_self]
      have hlin : s x (v-w) ∈ modelLineality x :=
        (cone_equiv_lineality x y E hE _).mp ((hrzero y _).mp hz)
      have hh := (hrzero x _).mpr hlin
      rw [hrs] at hh
      exact sub_eq_zero.mp hh
    · intro z
      refine ⟨r x (E.symm (s y z)), ?_⟩
      change r y (E (s x (r x (E.symm (s y z))))) = z
      rw [hfactor, E.apply_symm_apply, hrs]
  let F := LinearEquiv.ofBijective L hL
  have hpos (v : activeCoordinates x → ℝ) :
      (∀ i, 0 ≤ v i) ↔ ∀ j, 0 ≤ F v j := by
    have hv : (∀ i, 0 ≤ v i) ↔ s x v ∈ modelCone x := by
      simpa only [hrs] using hrcone x (s x v)
    have hiff : E (s x v) ∈ modelCone y ↔ s x v ∈ modelCone x := by
      rw [← hE]
      exact ⟨fun ⟨w, hw, he⟩ => E.injective he ▸ hw, fun hw => ⟨_, hw, rfl⟩⟩
    exact hv.trans (hiff.symm.trans (hrcone y _).symm)
  obtain ⟨σ, a, ha, hcoord⟩ := positive_linearEquiv_coordinates F hpos
  have hnormal (v : Euclidean n) (j : activeCoordinates y) :
      E v j.val = a j * v (σ j).val := by
    have hh := hcoord (r x v) j
    change r y (E (s x (r x v))) j = a j * v (σ j).val at hh
    rw [hfactor] at hh
    exact hh
  refine ⟨σ, a, ha, hnormal, ?_⟩
  intro j
  ext w
  constructor
  · rintro ⟨v, ⟨hv, hv0⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hE]
      exact ⟨v, hv, rfl⟩
    · rw [hnormal, hv0, mul_zero]
  · rintro ⟨hw, hw0⟩
    obtain ⟨v, hv, rfl⟩ := (show w ∈ E '' modelCone x by rwa [hE])
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    rw [hnormal] at hw0
    exact (mul_eq_zero.mp hw0).resolve_left (ne_of_gt (ha j))

theorem model_velocity_cone :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_velocity_coneType := velocity_cone

theorem model_lineality :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_linealityType := lineality

theorem model_lineality_codimension :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_lineality_codimensionType := lineality_codimension

theorem transition_cone :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.transition_coneType := transition_cone_proof

theorem chart_depth :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.chart_depthType.{u} := chart_depth_proof

theorem coordinate_germs_injective :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.coordinate_germs_injectiveType := coordinate_germs_injective_proof

theorem model_face_projection_proper :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_face_projection_properType := model_face_projection_proper_proof

theorem zero_faces :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.zero_facesType.{u} := zero_faces_proof

theorem coordinate_face_chart :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.coordinate_face_chartType := coordinate_face_chart_proof

theorem model_face_compact_support :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_face_compact_supportType.{u} := model_face_compact_support_proof

private theorem extension_entry_zero_of_coordinate_nonzero {n : ℕ} {k l : Fin (n + 1)}
    (e : OpenPartialHomeomorph (Orthant n k) (Orthant n l))
    (he : OrthantMapContDiffOn (⊤ : ℕ∞) e.source (fun z => e z.val))
    (hge : OrthantMapContDiffOn (⊤ : ℕ∞) e.target (fun z => e.symm z.val))
    (x : Orthant n k) (hx : x ∈ e.source) (H : OrthantExtension e.source e x)
    (i j : Fin n) (hj : j.val < l.val) (hjz : (e x).val j = 0)
    (hin : x.val i ≠ 0) : fderiv ℝ H.map x.val (Pi.single i 1) j = 0 := by
  obtain ⟨E, hE, hcone, _⟩ := transition_cone e he hge x hx H
  have hlin : (Pi.single i 1 : Euclidean n) ∈ modelLineality x := by
    intro r hr hrz
    have hri : r ≠ i := by
      intro hh
      exact hin (hh ▸ hrz)
    exact Pi.single_eq_of_ne hri 1
  have hh := (cone_equiv_lineality x (e x) E.toLinearEquiv hcone _).mpr hlin
  have hz := hh j hj hjz
  change E.toContinuousLinearMap (Pi.single i 1) j = 0 at hz
  rwa [hE] at hz

private theorem transition_coordinate_faces {n : ℕ} {k l : Fin (n + 1)}
    (e : OpenPartialHomeomorph (Orthant n k) (Orthant n l))
    (he : OrthantMapContDiffOn (⊤ : ℕ∞) e.source (fun z => e z.val))
    (hge : OrthantMapContDiffOn (⊤ : ℕ∞) e.target (fun z => e.symm z.val))
    (x : Orthant n k) (hx : x ∈ e.source) (H : OrthantExtension e.source e x) :
    ∃ σ : activeCoordinates (e x) ≃ activeCoordinates x,
      ∀ j, ∀ᶠ z in 𝓝 x, (e z).val j.val = 0 ↔ z.val (σ j).val = 0 := by
  classical
  obtain ⟨E, hE, hcone, _⟩ := transition_cone e he hge x hx H
  obtain ⟨σ, a, ha, hcoord, _⟩ := cone_facets x (e x) E.toLinearEquiv hcone
  refine ⟨σ, fun j => ?_⟩
  let i : Fin n := (σ j).val
  rcases hge ⟨e x, e.map_source hx⟩ with ⟨V, hV, hxV, g, hg, hgeq⟩
  let G : OrthantExtension e.target e.symm (e x) := {
    domain := V
    isOpen_domain := hV
    mem_domain := hxV
    map := g
    smooth := hg
    agrees := fun y hy hyV => hgeq ⟨y, hy⟩ hyV }
  let H' : OrthantExtension e.symm.target e.symm.symm (e.symm (e x)) := {
    domain := H.domain
    isOpen_domain := H.isOpen_domain
    mem_domain := by simpa only [e.left_inv hx] using H.mem_domain
    map := H.map
    smooth := H.smooth
    agrees := H.agrees }
  have hFG : (fderiv ℝ H.map x.val).comp (fderiv ℝ G.map (e x).val) =
      ContinuousLinearMap.id ℝ (Euclidean n) := by
    simpa only [e.left_inv hx] using
      extension_comp_derivative e.symm (e x) (e.map_source hx) G H'
  have hD : fderiv ℝ H.map x.val (Pi.single i 1) j.val ≠ 0 := by
    have hh := hcoord (Pi.single i 1) j
    change E.toContinuousLinearMap (Pi.single i 1) j.val = _ at hh
    rw [hE] at hh
    have hs : (Pi.single i (1 : ℝ) : Euclidean n) (σ j).val = 1 := by
      change Pi.single i 1 i = 1
      simp
    rw [hs, mul_one] at hh
    exact hh.trans_ne (ne_of_gt (ha j))
  have hDg : fderiv ℝ G.map (e x).val (Pi.single j.val 1) i ≠ 0 := by
    intro hz
    have hh := hcoord (fderiv ℝ G.map (e x).val (Pi.single j.val 1)) j
    change E.toContinuousLinearMap _ j.val = _ at hh
    rw [hE] at hh
    have hv := DFunLike.congr_fun hFG (Pi.single j.val (1 : ℝ))
    have hj := congrFun hv j.val
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, Pi.single_eq_same] at hj
    rw [hh, hz, mul_zero] at hj
    exact zero_ne_one hj
  have hcontD : ContinuousAt (fun z : Orthant n k =>
      fderiv ℝ H.map z.val (Pi.single i 1) j.val) x := by
    have hd := (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).continuousAt_fderiv (by simp)
    exact (continuous_apply j.val).continuousAt.comp
      (((hd.comp continuous_subtype_val.continuousAt).clm_apply continuousAt_const))
  have hcontDg : ContinuousAt (fun y : Orthant n l =>
      fderiv ℝ G.map y.val (Pi.single j.val 1) i) (e x) := by
    have hd := (G.smooth.contDiffAt (G.isOpen_domain.mem_nhds G.mem_domain)).continuousAt_fderiv (by simp)
    exact (continuous_apply i).continuousAt.comp
      (((hd.comp continuous_subtype_val.continuousAt).clm_apply continuousAt_const))
  have hec : ContinuousAt e x := e.continuousOn.continuousAt (e.open_source.mem_nhds hx)
  have hnearD : ∀ᶠ z in 𝓝 x, fderiv ℝ H.map z.val (Pi.single i 1) j.val ≠ 0 :=
    hcontD.eventually_ne hD
  have hnearDg : ∀ᶠ z in 𝓝 x, fderiv ℝ G.map (e z).val (Pi.single j.val 1) i ≠ 0 :=
    (hcontDg.comp hec).eventually_ne hDg
  have hnearH : ∀ᶠ z : Orthant n k in 𝓝 x, z.val ∈ H.domain :=
    continuous_subtype_val.continuousAt.eventually (H.isOpen_domain.mem_nhds H.mem_domain)
  have hnearG : ∀ᶠ z in 𝓝 x, (e z).val ∈ G.domain :=
    (continuous_subtype_val.continuousAt.comp hec).eventually (G.isOpen_domain.mem_nhds G.mem_domain)
  filter_upwards [hnearD, hnearDg, hnearH, hnearG, e.open_source.mem_nhds hx] with z hzD hzDg hzH hzG hz
  let Hz : OrthantExtension e.source e z := {
    domain := H.domain
    isOpen_domain := H.isOpen_domain
    mem_domain := hzH
    map := H.map
    smooth := H.smooth
    agrees := H.agrees }
  let Gz : OrthantExtension e.target e.symm (e z) := {
    domain := G.domain
    isOpen_domain := G.isOpen_domain
    mem_domain := hzG
    map := G.map
    smooth := G.smooth
    agrees := G.agrees }
  have hji := (Finset.mem_filter.mp j.property).2.1
  have hii := (Finset.mem_filter.mp (σ j).property).2.1
  constructor
  · intro hjz
    by_contra hiz
    exact hzD (extension_entry_zero_of_coordinate_nonzero e he hge z hz Hz i j.val hji hjz hiz)
  · intro hiz
    by_contra hjz
    have hh := extension_entry_zero_of_coordinate_nonzero e.symm hge he (e z) (e.map_source hz)
      Gz j.val i hii (by simpa only [e.left_inv hz] using hiz) hjz
    exact hzDg hh


theorem chart_face_germ_transition {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c d : CornerChart n M)
    (hc : c ∈ S.atlas) (hd : d ∈ S.atlas) (p : M)
    (hp : p ∈ c.2.source) (hq : p ∈ d.2.source) :
    ∃ σ : activeCoordinates (d.2 p) ≃ activeCoordinates (c.2 p),
      ∀ j, chartFaceGerm d p j.val = chartFaceGerm c p (σ j).val := by
  classical
  let e := c.2.symm.trans d.2
  have hcompat := S.maximal.1.2 c hc d hd
  have hxe : c.2 p ∈ e.source := by
    refine ⟨c.2.map_source hp, ?_⟩
    change c.2.symm (c.2 p) ∈ d.2.source
    rwa [c.2.left_inv hp]
  rcases hcompat.1 ⟨c.2 p, hxe⟩ with ⟨U, hU, hxU, f, hf, hfeq⟩
  let H : OrthantExtension e.source e (c.2 p) := {
    domain := U
    isOpen_domain := hU
    mem_domain := hxU
    map := f
    smooth := hf
    agrees := fun y hy hyU => hfeq ⟨y, hy⟩ hyU }
  have hresult := transition_coordinate_faces e hcompat.1 hcompat.2 (c.2 p) hxe H
  have hxeq : e (c.2 p) = d.2 p := by
    dsimp [e]
    rw [c.2.left_inv hp]
  rw [hxeq] at hresult
  obtain ⟨σ, hσ⟩ := hresult
  refine ⟨σ, fun j => ?_⟩
  apply Filter.Germ.coe_eq.mpr
  have hcc : ContinuousAt c.2 p := c.2.continuousOn.continuousAt (c.2.open_source.mem_nhds hp)
  have heq := hcc.eventually (hσ j)
  filter_upwards [heq, c.2.open_source.mem_nhds hp, d.2.open_source.mem_nhds hq] with q hqeq hqc hqd
  have hqe : e (c.2 q) = d.2 q := by
    dsimp [e]
    rw [c.2.left_inv hqc]
  change (q ∈ d.2.source ∧ (d.2 q).val j.val = 0) =
    (q ∈ c.2.source ∧ (c.2 q).val (σ j).val = 0)
  exact propext (by simpa only [hqe, hqc, hqd, true_and] using hqeq)

theorem localFaceGerm_chart_surjective {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (p : M) (hp : p ∈ c.2.source) (g : LocalFaceGerm S p) :
    ∃ i : activeCoordinates (c.2 p), g.val = chartFaceGerm c p i.val := by
  classical
  rcases g.property with ⟨d, hd, hdp, j, hj, hjz, hgj⟩
  obtain ⟨σ, hσ⟩ := chart_face_germ_transition S c d hc hd p hp hdp
  let j' : activeCoordinates (d.2 p) := ⟨j, by simp [activeCoordinates, hj, hjz]⟩
  exact ⟨σ j', hgj.trans (hσ j')⟩


theorem chart_coordinate_germs_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : CornerChart n M) (p : M) (hp : p ∈ c.2.source) :
    Function.Injective (fun i : activeCoordinates (c.2 p) => chartFaceGerm c p i.val) := by
  intro i j hij
  apply coordinate_germs_injective (c.2 p)
  apply Filter.Germ.coe_eq.mpr
  have ht := c.2.tendsto_symm hp
  have heq := (Filter.Germ.coe_eq.mp hij).comp_tendsto ht
  filter_upwards [heq, c.2.open_target.mem_nhds (c.2.map_source hp)] with y hy hyt
  change (c.2.symm y ∈ c.2.source ∧ (c.2 (c.2.symm y)).val i.val = 0) =
    (c.2.symm y ∈ c.2.source ∧ (c.2 (c.2.symm y)).val j.val = 0) at hy
  simpa only [c.2.right_inv hyt, c.2.map_target hyt, true_and] using hy

theorem corner_countable_chart_cover {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) :
    ∃ C : Set (CornerChart n M), C.Countable ∧ C ⊆ S.atlas ∧
      ∀ p : M, ∃ c ∈ C, p ∈ c.2.source := by
  classical
  let := S.secondCountable
  choose c hc hp using S.maximal.1.1
  obtain ⟨A, hA, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun p : M => (c p).2.source) (fun p => (c p).2.open_source)
    (by intro p _; exact mem_iUnion.mpr ⟨p, hp p⟩)
  refine ⟨c '' A, hA.image _, ?_, ?_⟩
  · rintro d ⟨p, _, rfl⟩
    exact hc p
  · intro p
    obtain ⟨q, hq, hqp⟩ := mem_iUnion₂.mp (hcover (mem_univ p))
    exact ⟨c q, mem_image_of_mem _ hq, hqp⟩


theorem isClosed_orthantSet (n : ℕ) (k : Fin (n + 1)) : IsClosed (orthantSet n k) := by
  simp only [orthantSet, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_apply i)


theorem corner_locallyCompactSpace {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) : LocallyCompactSpace M := by
  classical
  choose c hc hpc using S.maximal.1.1
  let (p : M) : LocallyCompactSpace (Orthant n (c p).1) :=
    (isClosed_orthantSet n (c p).1).locallyCompactSpace
  apply LocallyCompactSpace.of_hasBasis
    (s := fun p (s : Set (Orthant n (c p).1)) => (c p).2.symm '' s)
    (p := fun p s => s ∈ 𝓝 ((c p).2 p) ∧ IsCompact s ∧ s ⊆ (c p).2.target)
  · intro p
    rw [← (c p).2.symm_map_nhds_eq (hpc p)]
    exact ((compact_basis_nhds ((c p).2 p)).hasBasis_self_subset
      ((c p).2.open_target.mem_nhds ((c p).2.map_source (hpc p)))).map _
  · rintro p s ⟨_, hs, hst⟩
    exact hs.image_of_continuousOn ((c p).2.continuousOn_symm.mono hst)


theorem corner_atlas_extension :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.corner_atlas_extensionType := by
  intro n M _ A hA
  exact ⟨cornerMaximalExtension_isMaximal hA, cornerAtlas_subset_maximalExtension hA⟩

theorem model_corner_structure :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.model_corner_structureType := by
  intro n k
  let c : CornerChart n (Orthant n k) := ⟨k, OpenPartialHomeomorph.refl _⟩
  have hA : IsSmoothCornerAtlas {c} := by
    constructor
    · intro p
      exact ⟨c, mem_singleton c, mem_univ p⟩
    · intro a ha b hb
      rw [mem_singleton_iff.mp ha, mem_singleton_iff.mp hb]
      exact cornerCompatible_refl c
  refine ⟨⟨inferInstance, inferInstance, cornerMaximalExtension {c},
    cornerMaximalExtension_isMaximal hA⟩, ?_⟩
  exact cornerAtlas_subset_maximalExtension hA (mem_singleton c)

theorem empty_corner_structure :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.empty_corner_structureType := by
  intro n
  have hA : IsSmoothCornerAtlas (∅ : Set (CornerChart n Empty)) := by
    refine ⟨fun p => Empty.elim p, ?_⟩
    intro c hc
    exact False.elim hc
  exact ⟨⟨inferInstance, inferInstance, cornerMaximalExtension ∅,
    cornerMaximalExtension_isMaximal hA⟩⟩

theorem countable_chart_cover :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.countable_chart_coverType :=
  corner_countable_chart_cover

theorem locally_compact :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.locally_compactType :=
  corner_locallyCompactSpace

theorem chart_face_germs :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.chart_face_germsType := by
  intro n M _ S c hc p hp
  constructor
  · intro i j hij
    exact chart_coordinate_germs_injective c p hp (congrArg Subtype.val hij)
  · intro g
    obtain ⟨i, hi⟩ := localFaceGerm_chart_surjective S c hc p hp g
    exact ⟨i, Subtype.ext hi.symm⟩

theorem local_face_cardinality :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.local_face_cardinalityType := by
  classical
  intro n M _ S c hc p hp
  let E := Equiv.ofBijective (chartFaceAt S c hc p hp) (chart_face_germs S c hc p hp)
  refine ⟨Finite.of_equiv _ E, ?_⟩
  calc
    Nat.card (LocalFaceGerm S p) = Nat.card (activeCoordinates (c.2 p)) :=
      Nat.card_congr E.symm
    _ = modelDepth (c.2 p) := by simp [modelDepth]

theorem isOpen_germ_eq {M α : Type*} [TopologicalSpace M] (f g : M → α) :
    IsOpen {p : M | (Filter.Germ.ofFun f : Filter.Germ (𝓝 p) α) = Filter.Germ.ofFun g} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  rcases mem_nhds_iff.mp (Filter.Germ.coe_eq.mp hp) with ⟨U, hU, hUo, hpU⟩
  apply mem_of_superset (hUo.mem_nhds hpU)
  intro q hq
  exact Filter.Germ.coe_eq.mpr (mem_of_superset (hUo.mem_nhds hq) hU)


theorem isOpen_chartFaceGerm_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (i j : Fin n) :
    IsOpen {p : M | chartFaceGerm c p i = chartFaceGerm d p j} :=
  isOpen_germ_eq (fun q => q ∈ c.2.source ∧ (c.2 q).val i = 0)
    (fun q => q ∈ d.2.source ∧ (d.2 q).val j = 0)

theorem isOpen_faceSheet {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (i : Fin n) (hi : i.val < c.1.val) (U : Set M) (hU : IsOpen U) :
    IsOpen (faceSheet S c i U) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, hc, i, hi, U, hU, rfl⟩

theorem face_projection_continuous :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.face_projection_continuousType := by
  intro n M _ S
  rw [continuous_def]
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  rcases q.2.property with ⟨c, hc, hp, i, hi, hz, hg⟩
  have hmem : q ∈ faceSheet S c i U := ⟨hq, hp, hz, hg⟩
  exact mem_of_superset ((isOpen_faceSheet S c hc i hi U hU).mem_nhds hmem)
    (fun _ h => h.1)

theorem resolved_face_hausdorff :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.resolved_face_hausdorffType := by
  intro n M _ S
  let := S.hausdorff
  constructor
  intro q r hqr
  by_cases hbase : q.1 = r.1
  · rcases q with ⟨p, g⟩
    rcases r with ⟨p', g'⟩
    dsimp at hbase
    subst p'
    obtain ⟨c, hc, hp⟩ := S.maximal.1.1 p
    obtain ⟨i, hi⟩ := (chart_face_germs S c hc p hp).2 g
    obtain ⟨j, hj⟩ := (chart_face_germs S c hc p hp).2 g'
    have hij : i ≠ j := by
      intro heq
      apply hqr
      have hgg : g = g' := hi.symm.trans (heq ▸ hj)
      exact congrArg (Sigma.mk p) hgg
    have hia := (Finset.mem_filter.mp i.property).2
    have hja := (Finset.mem_filter.mp j.property).2
    refine ⟨faceSheet S c i.val univ, faceSheet S c j.val univ,
      isOpen_faceSheet S c hc i.val hia.1 univ isOpen_univ,
      isOpen_faceSheet S c hc j.val hja.1 univ isOpen_univ,
      ⟨mem_univ _, hp, hia.2, congrArg Subtype.val hi.symm⟩,
      ⟨mem_univ _, hp, hja.2, congrArg Subtype.val hj.symm⟩, ?_⟩
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    let iz : activeCoordinates (c.2 z.1) :=
      ⟨i.val, by simp [activeCoordinates, hia.1, hzi.2.2.1]⟩
    let jz : activeCoordinates (c.2 z.1) :=
      ⟨j.val, by simp [activeCoordinates, hja.1, hzj.2.2.1]⟩
    have heq : iz = jz := chart_coordinate_germs_injective c z.1 hzi.2.1
      (hzi.2.2.2.symm.trans hzj.2.2.2)
    exact hij (Subtype.ext (congrArg (fun a : activeCoordinates (c.2 z.1) => a.val) heq))
  · exact separated_by_continuous (face_projection_continuous S) hbase


theorem chartFaceLift_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (i : Fin n) (hi : i.val < c.1.val) :
    Function.Injective (chartFaceLift S c hc i hi) := by
  intro p q hpq
  exact Subtype.ext (congrArg Sigma.fst hpq)

theorem chartFaceLift_preimage_sheet {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (i : Fin n) (hi : i.val < c.1.val)
    (d : CornerChart n M) (j : Fin n) (U : Set M) :
    chartFaceLift S c hc i hi ⁻¹' faceSheet S d j U =
      Subtype.val ⁻¹' (U ∩ {p | chartFaceGerm c p i = chartFaceGerm d p j}) := by
  ext p
  constructor
  · rintro ⟨hpU, _, _, hpg⟩
    exact ⟨hpU, hpg⟩
  · rintro ⟨hpU, hpg⟩
    have heq := (Filter.Germ.coe_eq.mp hpg).eq_of_nhds
    have hpd : p.val ∈ d.2.source ∧ (d.2 p.val).val j = 0 := by
      change (p.val ∈ c.2.source ∧ (c.2 p.val).val i = 0) =
        (p.val ∈ d.2.source ∧ (d.2 p.val).val j = 0) at heq
      exact heq ▸ p.property
    exact ⟨hpU, hpd.1, hpd.2, hpg⟩

theorem chartFaceLift_continuous {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (i : Fin n) (hi : i.val < c.1.val) :
    Continuous (chartFaceLift S c hc i hi) := by
  apply continuous_generateFrom_iff.mpr
  rintro V ⟨d, hd, j, hj, U, hU, rfl⟩
  rw [chartFaceLift_preimage_sheet]
  exact (hU.inter (isOpen_chartFaceGerm_eq c d i j)).preimage continuous_subtype_val

theorem chartFaceLift_image_open {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (i : Fin n) (hi : i.val < c.1.val) (U : Set M) :
    chartFaceLift S c hc i hi '' (Subtype.val ⁻¹' U) = faceSheet S c i U := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, p.property.1, p.property.2, rfl⟩
  · rintro ⟨hpU, hpc, hpz, hpg⟩
    refine ⟨⟨q.1, hpc, hpz⟩, hpU, ?_⟩
    apply Sigma.ext (x := chartFaceLift S c hc i hi ⟨q.1, hpc, hpz⟩) (y := q) rfl
    apply heq_of_eq
    exact Subtype.ext hpg.symm

theorem chartFaceLift_isOpenMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (i : Fin n) (hi : i.val < c.1.val) :
    IsOpenMap (chartFaceLift S c hc i hi) := by
  intro V hV
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hV
  rw [chartFaceLift_image_open]
  exact isOpen_faceSheet S c hc i hi U hU

theorem chartFaceLift_isOpenEmbedding {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (i : Fin n) (hi : i.val < c.1.val) :
    Topology.IsOpenEmbedding (chartFaceLift S c hc i hi) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (chartFaceLift_continuous S c hc i hi) (chartFaceLift_injective S c hc i hi)
    (chartFaceLift_isOpenMap S c hc i hi)

def chartFacePatchHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : CornerChart n M) (i : Fin n) : ChartFacePatch c i ≃ₜ ModelChartFacePatch c i where
  toFun p := ⟨c.2 p.val, c.2.map_source p.property.1, p.property.2⟩
  invFun x := ⟨c.2.symm x.val, c.2.map_target x.property.1, by
    rw [c.2.right_inv x.property.1]
    exact x.property.2⟩
  left_inv p := Subtype.ext (c.2.left_inv p.property.1)
  right_inv x := Subtype.ext (c.2.right_inv x.property.1)
  continuous_toFun :=
    (c.2.continuousOn.comp_continuous continuous_subtype_val (fun p => p.property.1)).subtype_mk _
  continuous_invFun :=
    (c.2.continuousOn_symm.comp_continuous continuous_subtype_val (fun x => x.property.1)).subtype_mk _

noncomputable def chartFaceSheetHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (i : Fin n) (hi : i.val < c.1.val) :
    ChartFacePatch c i ≃ₜ faceSheet S c i univ :=
  (chartFaceLift_isOpenEmbedding S c hc i hi).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [← image_univ, ← preimage_univ]
      exact chartFaceLift_image_open S c hc i hi univ))

noncomputable def modelFaceSheetHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (i : Fin n) (hi : i.val < c.1.val) :
    faceSheet S c i univ ≃ₜ ModelChartFacePatch c i :=
  (chartFaceSheetHomeomorph S c hc i hi).symm.trans (chartFacePatchHomeomorph c i)


open TopologicalSpace

private theorem secondCountable_of_countable_generator_refinement {α : Type*}
    (G B : Set (Set α)) (hB : B.Countable) (hBG : B ⊆ G)
    (href : ∀ s ∈ G, ∀ x ∈ s, ∃ b ∈ B, x ∈ b ∧ b ⊆ s) :
    @SecondCountableTopology α (generateFrom G) := by
  let : TopologicalSpace α := generateFrom B
  have hg : ∀ s ∈ G, IsOpen s := by
    intro s hs
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨b, hb, hxb, hbs⟩ := href s hs x hx
    exact ⟨b, hbs, isOpen_generateFrom_of_mem hb, hxb⟩
  have heq : generateFrom G = generateFrom B :=
    le_antisymm (generateFrom_anti hBG) (le_generateFrom hg)
  rw [heq]
  exact SecondCountableTopology.mk' hB

theorem resolvedFaceSpace_secondCountable {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) : SecondCountableTopology (ResolvedFaceSpace S) := by
  classical
  let := S.secondCountable
  obtain ⟨C, hC, hCA, hcover⟩ := countable_chart_cover S
  let B : Set (Set (ResolvedFaceSpace S)) :=
    ⋃ c ∈ C, ⋃ i : {i : Fin n // i.val < c.1.val},
      (fun U => faceSheet S c i.val U) '' countableBasis M
  have hB : B.Countable :=
    hC.biUnion fun c _ => countable_iUnion fun i => (countable_countableBasis M).image _
  change @SecondCountableTopology _ (generateFrom _)
  apply secondCountable_of_countable_generator_refinement _ B hB
  · intro b hb
    obtain ⟨c, hc, i, U, hU, rfl⟩ := by simpa only [B, mem_iUnion, mem_image] using hb
    exact ⟨c, hCA hc, i.val, i.property, U, isOpen_of_mem_countableBasis hU, rfl⟩
  · intro a ha q hq
    rcases ha with ⟨d, hd, j, hj, V, hV, rfl⟩
    rcases hq with ⟨hqV, hqd, hqj, hqg⟩
    obtain ⟨c, hc, hqc⟩ := hcover q.1
    obtain ⟨i, hi⟩ := (chart_face_germs S c (hCA hc) q.1 hqc).2 q.2
    have hg : q.2.val = chartFaceGerm c q.1 i.val := congrArg Subtype.val hi.symm
    let W : Set M := V ∩ c.2.source ∩ d.2.source ∩
      {p | chartFaceGerm c p i.val = chartFaceGerm d p j}
    have hW : IsOpen W :=
      ((hV.inter c.2.open_source).inter d.2.open_source).inter (isOpen_chartFaceGerm_eq c d i.val j)
    have hqW : q.1 ∈ W := ⟨⟨⟨hqV, hqc⟩, hqd⟩, hg.symm.trans hqg⟩
    obtain ⟨U, hU, hqU, hUW⟩ := (isBasis_countableBasis M).mem_nhds_iff.mp (hW.mem_nhds hqW)
    refine ⟨faceSheet S c i.val U, ?_, ?_, ?_⟩
    · have hi' : i.val.val < c.1.val := (Finset.mem_filter.mp i.property).2.1
      exact mem_iUnion₂.mpr ⟨c, hc, mem_iUnion.mpr
        ⟨⟨i.val, hi'⟩, mem_image_of_mem _ hU⟩⟩
    · exact ⟨hqU, hqc, (Finset.mem_filter.mp i.property).2.2, hg⟩
    · intro r hr
      rcases hr with ⟨hrU, hrc, hri, hrg⟩
      rcases hUW hrU with ⟨⟨⟨hrV, _⟩, hrd⟩, heq⟩
      have heq' := (Filter.Germ.coe_eq.mp heq).eq_of_nhds
      change (r.1 ∈ c.2.source ∧ (c.2 r.1).val i.val = 0) =
        (r.1 ∈ d.2.source ∧ (d.2 r.1).val j = 0) at heq'
      exact ⟨hrV, hrd, (Eq.mp heq' ⟨hrc, hri⟩).2, hrg.trans heq⟩

theorem resolved_face_second_countable :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.resolved_face_second_countableType :=
  resolvedFaceSpace_secondCountable

theorem face_sheet_embedding :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.face_sheet_embeddingType :=
  chartFaceLift_isOpenEmbedding

theorem resolvedFaceProjection_isProperMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) : IsProperMap (faceProjection S) := by
  classical
  rw [isProperMap_iff_ultrafilter]
  refine ⟨face_projection_continuous S, ?_⟩
  intro 𝒰 p h𝒰
  obtain ⟨c, hc, hp⟩ := S.maximal.1.1 p
  have hbase : ∀ᶠ q : ResolvedFaceSpace S in 𝒰, q.1 ∈ c.2.source :=
    h𝒰.eventually (c.2.open_source.mem_nhds hp)
  have hcover : ∀ᶠ q : ResolvedFaceSpace S in 𝒰,
      ∃ i : Fin n, i.val < c.1.val ∧ q ∈ faceSheet S c i univ := by
    filter_upwards [hbase] with q hq
    obtain ⟨i, hi⟩ := localFaceGerm_chart_surjective S c hc q.1 hq q.2
    have hia := (Finset.mem_filter.mp i.property).2
    exact ⟨i.val, hia.1, mem_univ _, hq, hia.2, hi⟩
  obtain ⟨i, hiU⟩ := Ultrafilter.eventually_exists_iff.mp hcover
  have hi : i.val < c.1.val := (hiU.exists.choose_spec).1
  have hsheet : ∀ᶠ q : ResolvedFaceSpace S in 𝒰, q ∈ faceSheet S c i univ :=
    hiU.mono (fun _ h => h.2)
  have hcc : ContinuousAt (fun y : M => (c.2 y).val i) p :=
    (continuous_apply i).continuousAt.comp (continuous_subtype_val.continuousAt.comp
      (c.2.continuousOn.continuousAt (c.2.open_source.mem_nhds hp)))
  have hcoord : Tendsto (fun q : ResolvedFaceSpace S => (c.2 q.1).val i)
      (𝒰 : Filter _) (𝓝 ((c.2 p).val i)) := hcc.tendsto.comp h𝒰
  have hz : ∀ᶠ q : ResolvedFaceSpace S in 𝒰, (c.2 q.1).val i = 0 :=
    hsheet.mono (fun _ h => h.2.2.1)
  have hcoord0 : Tendsto (fun q : ResolvedFaceSpace S => (c.2 q.1).val i)
      (𝒰 : Filter _) (𝓝 (0 : ℝ)) := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hz)
  have hpi : (c.2 p).val i = 0 := tendsto_nhds_unique hcoord hcoord0
  let p' : ChartFacePatch c i := ⟨p, hp, hpi⟩
  let t : ResolvedFaceSpace S → ChartFacePatch c i := fun q =>
    if hq : q.1 ∈ c.2.source ∧ (c.2 q.1).val i = 0 then ⟨q.1, hq⟩ else p'
  have htbase : (fun q : ResolvedFaceSpace S => (t q).val) =ᶠ[𝒰] faceProjection S := by
    filter_upwards [hsheet] with q hq
    have hpq : q.1 ∈ c.2.source ∧ (c.2 q.1).val i = 0 := ⟨hq.2.1, hq.2.2.1⟩
    simp only [t, dite_eq_left hpq, faceProjection]
  have ht : Tendsto t (𝒰 : Filter _) (𝓝 p') := by
    apply tendsto_subtype_rng.mpr
    exact h𝒰.congr' htbase.symm
  have hlift : (fun q => chartFaceLift S c hc i hi (t q)) =ᶠ[𝒰] id := by
    filter_upwards [hsheet] with q hq
    have hpq : q.1 ∈ c.2.source ∧ (c.2 q.1).val i = 0 := ⟨hq.2.1, hq.2.2.1⟩
    simp only [t, dite_eq_left hpq, id_eq]
    apply Sigma.ext (x := chartFaceLift S c hc i hi ⟨q.1, hq.2.1, hq.2.2.1⟩) (y := q) rfl
    apply heq_of_eq
    exact Subtype.ext hq.2.2.2.symm
  refine ⟨chartFaceLift S c hc i hi p', rfl, ?_⟩
  change Tendsto id (𝒰 : Filter _) (𝓝 (chartFaceLift S c hc i hi p'))
  exact ((chartFaceLift_continuous S c hc i hi).tendsto p' |>.comp ht).congr' hlift


theorem resolvedFaceProjection_compact_support {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) {F : M → Type*} [∀ x, Zero (F x)]
    (s : ∀ x, F x) (hs : IsCompact (sectionSupport s)) :
    IsCompact (sectionSupport (fun q : ResolvedFaceSpace S => s (faceProjection S q))) := by
  have hp := resolvedFaceProjection_isProperMap S
  have hsub : sectionSupport (fun q : ResolvedFaceSpace S => s (faceProjection S q)) ⊆
      faceProjection S ⁻¹' sectionSupport s := by
    apply closure_minimal
    · intro q hq
      exact subset_closure hq
    · exact isClosed_closure.preimage hp.continuous
  exact (hp.isCompact_preimage hs).of_isClosed_subset isClosed_closure hsub


theorem face_projection_proper :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.face_projection_properType :=
  resolvedFaceProjection_isProperMap

theorem face_compact_support :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.face_compact_supportType := by
  intro n M _ S F _ s hs
  have hp := face_projection_proper S
  have hsub : sectionSupport (fun q : ResolvedFaceSpace S => s (faceProjection S q)) ⊆
      faceProjection S ⁻¹' sectionSupport s := by
    apply closure_minimal
    · intro q hq
      exact subset_closure hq
    · exact isClosed_closure.preimage hp.continuous
  exact (hp.isCompact_preimage hs).of_isClosed_subset isClosed_closure hsub

abbrev WholeModelFace {n : ℕ} (k : Fin (n + 1)) (i : Fin n) :=
  {x : Orthant n k // x.val i = 0}

def modelPatchToFace {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : CornerChart n M) (i : Fin n) : ModelChartFacePatch c i → WholeModelFace c.1 i :=
  fun x => ⟨x.val, x.property.2⟩

theorem modelPatchToFace_isOpenEmbedding {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : CornerChart n M) (i : Fin n) : Topology.IsOpenEmbedding (modelPatchToFace c i) := by
  refine ⟨Topology.IsEmbedding.subtypeVal.codRestrict _ (fun x => x.property.2), ?_⟩
  have hr : range (modelPatchToFace c i) = Subtype.val ⁻¹' c.2.target := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property.1
    · intro hx
      exact ⟨⟨x.val, hx, x.property⟩, rfl⟩
  rw [hr]
  exact c.2.open_target.preimage continuous_subtype_val

def faceCoordinateMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : CornerChart (n + 1) M) (i : Fin (n + 1))
    (h : WholeModelFace c.1 i ≃ₜ Orthant n (faceConstraintCount c.1)) :
    ChartFacePatch c i → Orthant n (faceConstraintCount c.1) :=
  h ∘ modelPatchToFace c i ∘ chartFacePatchHomeomorph c i

theorem faceCoordinateMap_isOpenEmbedding {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : CornerChart (n + 1) M) (i : Fin (n + 1))
    (h : WholeModelFace c.1 i ≃ₜ Orthant n (faceConstraintCount c.1)) :
    Topology.IsOpenEmbedding (faceCoordinateMap c i h) :=
  h.isOpenEmbedding.comp
    ((modelPatchToFace_isOpenEmbedding c i).comp (chartFacePatchHomeomorph c i).isOpenEmbedding)

noncomputable def resolvedFaceChart {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold (n + 1) M) (c : CornerChart (n + 1) M) (hc : c ∈ S.atlas)
    (i : Fin (n + 1)) (hi : i.val < c.1.val) (p : ChartFacePatch c i)
    (h : WholeModelFace c.1 i ≃ₜ Orthant n (faceConstraintCount c.1)) :
    OpenPartialHomeomorph (ResolvedFaceSpace S) (Orthant n (faceConstraintCount c.1)) := by
  letI : Nonempty (ChartFacePatch c i) := ⟨p⟩
  letI : Nonempty (Orthant n (faceConstraintCount c.1)) := ⟨faceCoordinateMap c i h p⟩
  exact ((faceCoordinateMap_isOpenEmbedding c i h).toOpenPartialHomeomorph
    (faceCoordinateMap c i h)).lift_openEmbedding (chartFaceLift_isOpenEmbedding S c hc i hi)

theorem resolvedFaceChart_source {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold (n + 1) M) (c : CornerChart (n + 1) M) (hc : c ∈ S.atlas)
    (i : Fin (n + 1)) (hi : i.val < c.1.val) (p : ChartFacePatch c i)
    (h : WholeModelFace c.1 i ≃ₜ Orthant n (faceConstraintCount c.1)) :
    (resolvedFaceChart S c hc i hi p h).source = faceSheet S c i univ := by
  simp only [resolvedFaceChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]
  rw [← preimage_univ]
  exact chartFaceLift_image_open S c hc i hi univ

theorem resolvedFaceChart_apply {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold (n + 1) M) (c : CornerChart (n + 1) M) (hc : c ∈ S.atlas)
    (i : Fin (n + 1)) (hi : i.val < c.1.val) (p q : ChartFacePatch c i)
    (h : WholeModelFace c.1 i ≃ₜ Orthant n (faceConstraintCount c.1)) :
    resolvedFaceChart S c hc i hi p h (chartFaceLift S c hc i hi q) =
      faceCoordinateMap c i h q := by
  simp only [resolvedFaceChart, OpenPartialHomeomorph.lift_openEmbedding_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]

theorem exists_resolvedFaceChart {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold (n + 1) M) (c : CornerChart (n + 1) M) (hc : c ∈ S.atlas)
    (i : Fin (n + 1)) (hi : i.val < c.1.val) (p : ChartFacePatch c i) :
    ∃ e : OpenPartialHomeomorph (ResolvedFaceSpace S) (Orthant n (faceConstraintCount c.1)),
      e.source = faceSheet S c i univ ∧
      ∀ q ∈ e.source, (e q).val = i.removeNth (c.2 q.1).val := by
  obtain ⟨h, hh, _, _, _⟩ := coordinate_face_chart n c.1 i hi
  refine ⟨resolvedFaceChart S c hc i hi p h, resolvedFaceChart_source S c hc i hi p h, ?_⟩
  intro q hq
  rw [resolvedFaceChart_source] at hq
  have hq' : q ∈ chartFaceLift S c hc i hi '' (Subtype.val ⁻¹' univ) := by
    rwa [chartFaceLift_image_open]
  obtain ⟨r, _, rfl⟩ := hq'
  rw [resolvedFaceChart_apply]
  funext j
  exact hh _ j

theorem resolved_face_charts_cover {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold (n + 1) M) (q : ResolvedFaceSpace S) :
    ∃ c ∈ S.atlas, ∃ i : Fin (n + 1), i.val < c.1.val ∧
      ∃ e : OpenPartialHomeomorph (ResolvedFaceSpace S) (Orthant n (faceConstraintCount c.1)),
        e.source = faceSheet S c i univ ∧ q ∈ e.source ∧
        ∀ r ∈ e.source, (e r).val = i.removeNth (c.2 r.1).val := by
  rcases q.2.property with ⟨c, hc, hqc, i, hi, hqz, hqg⟩
  obtain ⟨e, he, hmap⟩ := exists_resolvedFaceChart S c hc i hi ⟨q.1, hqc, hqz⟩
  exact ⟨c, hc, i, hi, e, he, by rw [he]; exact ⟨mem_univ _, hqc, hqz, hqg⟩, hmap⟩


theorem resolvedFaceTransition_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold (n+1) M)
    (c d : CornerChart (n+1) M) (hc : c ∈ S.atlas) (hd : d ∈ S.atlas)
    (i j : Fin (n+1)) (hi : i.val < c.1.val) (hj : j.val < d.1.val)
    (e f : CornerChart n (ResolvedFaceSpace S))
    (hes : e.2.source = faceSheet S c i univ)
    (hfs : f.2.source = faceSheet S d j univ)
    (hec : ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val))
    (hfc : ∀ q ∈ f.2.source, (f.2 q).val = j.removeNth ((d.2 q.1).val)) :
    OrthantMapContDiffOn (⊤ : ℕ∞) (e.2.symm.trans f.2).source
      (fun z => (e.2.symm.trans f.2) z.val) := by
  classical
  let t := e.2.symm.trans f.2
  let T := c.2.symm.trans d.2
  have hcompat := S.maximal.1.2 c hc d hd
  have hrestore (z : t.source) :
      i.insertNth (0 : ℝ) z.val.val = (c.2 (e.2.symm z.val).1).val := by
    have hqe : e.2.symm z.val ∈ e.2.source := e.2.map_target z.property.1
    have hqc : e.2.symm z.val ∈ faceSheet S c i univ := hes ▸ hqe
    apply Fin.insertNth_eq_iff.mpr
    refine ⟨hqc.2.2.1.symm, ?_⟩
    have hh := hec (e.2.symm z.val) hqe
    rw [e.2.right_inv z.property.1] at hh
    exact hh
  have hbase (z : t.source) : c.2 (e.2.symm z.val).1 ∈ T.source := by
    have hqe : e.2.symm z.val ∈ e.2.source := e.2.map_target z.property.1
    have hqc : e.2.symm z.val ∈ faceSheet S c i univ := hes ▸ hqe
    have hqd : e.2.symm z.val ∈ faceSheet S d j univ := hfs ▸ z.property.2
    refine ⟨c.2.map_source hqc.2.1, ?_⟩
    change c.2.symm (c.2 (e.2.symm z.val).1) ∈ d.2.source
    rw [c.2.left_inv hqc.2.1]
    exact hqd.2.1
  obtain ⟨_, _, _, hsi, _⟩ := coordinate_face_chart n c.1 i hi
  obtain ⟨_, _, _, _, hsd⟩ := coordinate_face_chart n d.1 j hj
  intro x
  rcases hcompat.1 ⟨c.2 (e.2.symm x.val).1, hbase x⟩ with
    ⟨U, hU, hxU, H, hH, hHeq⟩
  let V : Set (Euclidean n) := (fun z => i.insertNth (0 : ℝ) z) ⁻¹' U
  refine ⟨V, hU.preimage hsi.continuous, ?_,
    (fun z => j.removeNth (H (i.insertNth (0 : ℝ) z))), ?_, ?_⟩
  · change i.insertNth 0 x.val.val ∈ U
    rwa [hrestore x]
  · exact hsd.comp_contDiffOn (hH.comp hsi.contDiffOn (fun z hz => hz))
  · intro z hz
    have hqc : e.2.symm z.val ∈ faceSheet S c i univ :=
      hes ▸ e.2.map_target z.property.1
    have hqd : e.2.symm z.val ∈ faceSheet S d j univ := hfs ▸ z.property.2
    have hcz : (c.2 (e.2.symm z.val).1).val ∈ U := by
      rwa [← hrestore z]
    have hh := hHeq ⟨c.2 (e.2.symm z.val).1, hbase z⟩ hcz
    have hT : T (c.2 (e.2.symm z.val).1) = d.2 (e.2.symm z.val).1 := by
      dsimp [T]
      rw [c.2.left_inv hqc.2.1]
    change H (c.2 (e.2.symm z.val).1).val = (T (c.2 (e.2.symm z.val).1)).val at hh
    rw [hT] at hh
    change j.removeNth (H (i.insertNth 0 z.val.val)) = (f.2 (e.2.symm z.val)).val
    rw [hrestore z, hh, hfc (e.2.symm z.val) z.property.2]

theorem resolvedFaceCharts_compatible {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold (n+1) M)
    (c d : CornerChart (n+1) M) (hc : c ∈ S.atlas) (hd : d ∈ S.atlas)
    (i j : Fin (n+1)) (hi : i.val < c.1.val) (hj : j.val < d.1.val)
    (e f : CornerChart n (ResolvedFaceSpace S))
    (hes : e.2.source = faceSheet S c i univ)
    (hfs : f.2.source = faceSheet S d j univ)
    (hec : ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val))
    (hfc : ∀ q ∈ f.2.source, (f.2 q).val = j.removeNth ((d.2 q.1).val)) :
    CornerCompatible e f := by
  constructor
  · exact resolvedFaceTransition_smooth S c d hc hd i j hi hj e f hes hfs hec hfc
  · exact resolvedFaceTransition_smooth S d c hd hc j i hj hi f e hfs hes hfc hec


theorem resolved_face_atlas {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold (n + 1) M) :
    IsSmoothCornerAtlas {e | IsResolvedFaceChart S e} := by
  constructor
  · intro q
    obtain ⟨c, hc, i, hi, e, hes, hqe, hec⟩ := resolved_face_charts_cover S q
    refine ⟨⟨faceConstraintCount c.1, e⟩, ?_, hqe⟩
    exact ⟨c, hc, i, hi, rfl, hes, hec⟩
  · intro e he f hf
    rcases he with ⟨c, hc, i, hi, _, hes, hec⟩
    rcases hf with ⟨d, hd, j, hj, _, hfs, hfc⟩
    exact resolvedFaceCharts_compatible S c d hc hd i j hi hj e f hes hfs hec hfc

theorem resolved_corner_structure :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.resolved_corner_structureType := by
  intro n M _ S
  exact ⟨⟨resolved_face_hausdorff S, resolved_face_second_countable S,
    cornerMaximalExtension {e | IsResolvedFaceChart S e},
    cornerMaximalExtension_isMaximal (resolved_face_atlas S)⟩, rfl⟩

theorem resolvedFaceChart_projection_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold (n + 1) M) (e : CornerChart n (ResolvedFaceSpace S))
    (he : IsResolvedFaceChart S e) (d : CornerChart (n + 1) M) (hd : d ∈ S.atlas) :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      {x : Orthant n e.1 | x ∈ e.2.target ∧ (e.2.symm x).1 ∈ d.2.source}
      (fun x => d.2 (e.2.symm x.val).1) := by
  rcases he with ⟨c, hc, i, hi, hek, hes, hem⟩
  have hI : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Euclidean n => (i.insertNth (0 : ℝ) y : Euclidean (n + 1))) := by
    obtain ⟨_, _, _, hI, _⟩ := coordinate_face_chart n c.1 i hi
    exact hI
  have reconstruct : ∀ y : Orthant n e.1, y ∈ e.2.target →
      i.insertNth (0 : ℝ) y.val = (c.2 (e.2.symm y).1).val := by
    intro y hy
    have hq := e.2.map_target hy
    have hface : (c.2 (e.2.symm y).1).val i = 0 := by
      rw [hes] at hq
      exact hq.2.2.1
    have hdel : i.removeNth (c.2 (e.2.symm y).1).val = y.val := by
      rw [← hem (e.2.symm y) hq, e.2.right_inv hy]
    rw [← hdel, ← hface]
    exact Fin.insertNth_self_removeNth i _
  intro x
  have hqx := e.2.map_target x.property.1
  have hqcx : (e.2.symm x.val).1 ∈ c.2.source := by
    rw [hes] at hqx
    exact hqx.2.1
  have hbase : c.2 (e.2.symm x.val).1 ∈ (c.2.symm.trans d.2).source := by
    constructor
    · exact c.2.map_source hqcx
    · change c.2.symm (c.2 (e.2.symm x.val).1) ∈ d.2.source
      rw [c.2.left_inv hqcx]
      exact x.property.2
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ :=
    (S.maximal.1.2 c hc d hd).1 ⟨c.2 (e.2.symm x.val).1, hbase⟩
  let I : Euclidean n → Euclidean (n + 1) := fun y => i.insertNth (0 : ℝ) y
  have hFI : ContDiffOn ℝ (⊤ : ℕ∞) (F ∘ I) (I ⁻¹' U) :=
    hF.comp hI.contDiffOn (fun _ hy => hy)
  refine ⟨I ⁻¹' U, hU.preimage hI.continuous, ?_, F ∘ I, hFI, ?_⟩
  · change i.insertNth (0 : ℝ) x.val.val ∈ U
    rw [reconstruct x.val x.property.1]
    exact hxU
  · intro y hy
    have hqy := e.2.map_target y.property.1
    have hqcy : (e.2.symm y.val).1 ∈ c.2.source := by
      rw [hes] at hqy
      exact hqy.2.1
    have hb : c.2 (e.2.symm y.val).1 ∈ (c.2.symm.trans d.2).source := by
      constructor
      · exact c.2.map_source hqcy
      · change c.2.symm (c.2 (e.2.symm y.val).1) ∈ d.2.source
        rw [c.2.left_inv hqcy]
        exact y.property.2
    change F (i.insertNth (0 : ℝ) y.val.val) = (d.2 (e.2.symm y.val).1).val
    rw [reconstruct y.val y.property.1]
    have hyU : (c.2 (e.2.symm y.val).1).val ∈ U := by
      change i.insertNth (0 : ℝ) y.val.val ∈ U at hy
      rwa [reconstruct y.val y.property.1] at hy
    rw [hFeq ⟨c.2 (e.2.symm y.val).1, hb⟩ hyU]
    change (d.2 (c.2.symm (c.2 (e.2.symm y.val).1))).val = _
    rw [c.2.left_inv hqcy]

theorem cornerCoordinateSmooth_of_cover {n m : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set (CornerChart n X)} (hcover : ∀ p : X, ∃ a ∈ A, p ∈ a.2.source)
    (c : CornerChart n X) (hc : c ∈ cornerMaximalExtension A)
    (d : CornerChart m Y) (f : X → Y)
    (hf : ∀ a ∈ A, OrthantMapContDiffOn (⊤ : ℕ∞)
      {x : Orthant n a.1 | x ∈ a.2.target ∧ f (a.2.symm x) ∈ d.2.source}
      (fun x => d.2 (f (a.2.symm x.val)))) :
    OrthantMapContDiffOn (⊤ : ℕ∞)
      {x : Orthant n c.1 | x ∈ c.2.target ∧ f (c.2.symm x) ∈ d.2.source}
      (fun x => d.2 (f (c.2.symm x.val))) := by
  intro x
  let p := c.2.symm x.val
  have hpc : p ∈ c.2.source := c.2.map_target x.property.1
  obtain ⟨a, ha, hpa⟩ := hcover p
  let t := c.2.symm.trans a.2
  have hxt : x.val ∈ t.source := ⟨x.property.1, hpa⟩
  have htx : t x.val ∈ {y : Orthant n a.1 | y ∈ a.2.target ∧ f (a.2.symm y) ∈ d.2.source} := by
    constructor
    · exact a.2.map_source hpa
    · change f (a.2.symm (a.2 p)) ∈ d.2.source
      rw [a.2.left_inv hpa]
      exact x.property.2
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := (hc a ha).1 ⟨x.val, hxt⟩
  obtain ⟨V, hV, hxV, G, hG, hGeq⟩ := hf a ha ⟨t x.val, htx⟩
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp t.open_source
  have hxW : x.val.val ∈ W := by rw [← hWeq] at hxt; exact hxt
  refine ⟨(U ∩ W) ∩ F ⁻¹' V,
    (hF.mono inter_subset_left).continuousOn.isOpen_inter_preimage (hU.inter hW) hV,
    ⟨⟨hxU, hxW⟩, ?_⟩, G ∘ F,
    hG.comp (hF.mono (inter_subset_left.trans inter_subset_left)) (fun _ hy => hy.2), ?_⟩
  · change F x.val.val ∈ V
    rwa [hFeq ⟨x.val, hxt⟩ hxU]
  · intro y hy
    have hyt : y.val ∈ t.source := by rw [← hWeq]; exact hy.1.2
    have hypa : c.2.symm y.val ∈ a.2.source := hyt.2
    have hty : t y.val ∈ {z : Orthant n a.1 | z ∈ a.2.target ∧ f (a.2.symm z) ∈ d.2.source} := by
      constructor
      · exact a.2.map_source hypa
      · change f (a.2.symm (a.2 (c.2.symm y.val))) ∈ d.2.source
        rw [a.2.left_inv hypa]
        exact y.property.2
    change G (F y.val.val) = (d.2 (f (c.2.symm y.val))).val
    rw [hFeq ⟨y.val, hyt⟩ hy.1.1]
    have hyV : (t y.val).val ∈ V := by
      have hyV := hy.2
      change F y.val.val ∈ V at hyV
      rwa [hFeq ⟨y.val, hyt⟩ hy.1.1] at hyV
    rw [hGeq ⟨t y.val, hty⟩ hyV]
    change (d.2 (f (a.2.symm (a.2 (c.2.symm y.val))))).val = _
    rw [a.2.left_inv hypa]

theorem face_projection_smooth :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.face_projection_smoothType := by
  intro n M _ S T hT
  refine ⟨face_projection_continuous S, ?_⟩
  intro c hc d hd
  rw [hT] at hc
  exact cornerCoordinateSmooth_of_cover (resolved_face_atlas S).1 c hc d (faceProjection S)
    (fun e he => resolvedFaceChart_projection_smooth S e he d hd)


end SmoothManifolds.Corners

namespace SmoothManifolds.CornerExamples
open ModelData CornerData Set Finset
open scoped Topology

@[simp] theorem barycentric_zero {n : ℕ} (x : Euclidean n) :
    simplexBarycentric x 0 = 1 - ∑ i, x i := rfl
@[simp] theorem barycentric_succ {n : ℕ} (x : Euclidean n) (i : Fin n) :
    simplexBarycentric x i.succ = x i := by simp [simplexBarycentric]

@[simp] theorem sum_barycentric {n : ℕ} (x : Euclidean n) :
    ∑ i, simplexBarycentric x i = 1 := by simp [Fin.sum_univ_succ]

theorem barycentric_nonneg {n : ℕ} {x : Euclidean n} :
    x ∈ simplexSet n ↔ ∀ i, 0 ≤ simplexBarycentric x i := by
  constructor
  · rintro ⟨hx, hs⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using sub_nonneg.mpr hs
    · simpa using hx j
  · intro hx
    exact ⟨fun i => by simpa using hx i.succ, sub_nonneg.mp (hx 0)⟩

theorem exists_positive_barycentric {n : ℕ} (x : Simplex n) :
    ∃ j, 0 < simplexBarycentric x.val j := by
  by_contra h
  have hz : ∀ j, simplexBarycentric x.val j = 0 := by
    intro j
    exact le_antisymm (le_of_not_gt (fun hj => h ⟨j, hj⟩))
      (barycentric_nonneg.mp x.property j)
  have : (1 : ℝ) = 0 := by simpa only [hz, sum_const_zero] using (sum_barycentric x.val).symm
  norm_num at this

@[simp] theorem sum_insert_barycentric {n : ℕ} (j : Fin (n+1)) (y : Euclidean n) :
    ∑ i, j.insertNth (1 - ∑ i, y i) y i = 1 := by
  rw [Fin.sum_insertNth]; ring

theorem barycentric_tail_of_sum {n : ℕ} (b : Fin (n+1) → ℝ)
    (hb : ∑ i, b i = 1) : simplexBarycentric (Fin.tail b) = b := by
  calc
    simplexBarycentric (Fin.tail b) = Fin.cons (b 0) (Fin.tail b) := by
      have hh : b 0 + ∑ i : Fin n, b i.succ = 1 := by simpa [Fin.sum_univ_succ] using hb
      have hz : 1 - ∑ i, Fin.tail b i = b 0 := by dsimp [Fin.tail]; linarith
      simp only [simplexBarycentric, hz]
    _ = b := Fin.cons_self_tail b

@[simp] theorem barycentric_restore {n : ℕ} (j : Fin (n+1)) (y : Euclidean n) :
    simplexBarycentric (simplexRestoreBarycentric j y) = j.insertNth (1 - ∑ i, y i) y :=
  barycentric_tail_of_sum _ (sum_insert_barycentric j y)

@[simp] theorem omit_restore {n : ℕ} (j : Fin (n+1)) (y : Euclidean n) :
    simplexOmitBarycentric j (simplexRestoreBarycentric j y) = y := by
  simp [simplexOmitBarycentric]

@[simp] theorem restore_omit {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    simplexRestoreBarycentric j (simplexOmitBarycentric j x) = x := by
  have hsum := Fin.add_sum_removeNth j (simplexBarycentric x)
  rw [sum_barycentric] at hsum
  have hh : 1 - ∑ i, simplexOmitBarycentric j x i = simplexBarycentric x j := by
    dsimp [simplexOmitBarycentric]
    linarith
  change Fin.tail (j.insertNth (1 - ∑ i, simplexOmitBarycentric j x i) (simplexOmitBarycentric j x) : Euclidean (n+1)) = x
  rw [hh]
  change Fin.tail (j.insertNth (simplexBarycentric x j) (j.removeNth (simplexBarycentric x))) = x
  rw [Fin.insertNth_self_removeNth]
  simp [simplexBarycentric]

theorem contDiff_barycentric (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (@simplexBarycentric n) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [barycentric_zero]
    fun_prop
  · simpa only [barycentric_succ] using
      (contDiff_apply ℝ (fun _ : Fin n => ℝ) j)

theorem contDiff_omitBarycentric {n : ℕ} (j : Fin (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (simplexOmitBarycentric j) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_apply ℝ (fun _ : Fin (n+1) => ℝ) (j.succAbove i)).comp (contDiff_barycentric n)

theorem contDiff_insertBarycentric {n : ℕ} (j : Fin (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Euclidean n =>
      (j.insertNth (1 - ∑ i, y i) y : Euclidean (n+1))) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.succAboveCases j ?_ (fun r => ?_) i
  · simp only [Fin.insertNth_apply_same]
    fun_prop
  · simpa only [Fin.insertNth_apply_succAbove] using
      (contDiff_apply ℝ (fun _ : Fin n => ℝ) r)

theorem contDiff_restoreBarycentric {n : ℕ} (j : Fin (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (simplexRestoreBarycentric j) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_apply ℝ (fun _ : Fin (n+1) => ℝ) i.succ).comp (contDiff_insertBarycentric j)

/-- The ambient affine homeomorphism behind the j-th simplex corner chart. -/
def omitBarycentricHomeomorph {n : ℕ} (j : Fin (n+1)) : Euclidean n ≃ₜ Euclidean n where
  toFun := simplexOmitBarycentric j
  invFun := simplexRestoreBarycentric j
  left_inv := restore_omit j
  right_inv := omit_restore j
  continuous_toFun := (contDiff_omitBarycentric j).continuous
  continuous_invFun := (contDiff_restoreBarycentric j).continuous

theorem simplex_chart_mem_iff {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    (x ∈ simplexSet n ∧ 0 < simplexBarycentric x j) ↔
      (∀ i, 0 ≤ simplexOmitBarycentric j x i) ∧ ∑ i, simplexOmitBarycentric j x i < 1 := by
  have hsum := Fin.add_sum_removeNth j (simplexBarycentric x)
  rw [sum_barycentric] at hsum
  change simplexBarycentric x j + ∑ i, simplexOmitBarycentric j x i = 1 at hsum
  constructor
  · rintro ⟨hx, hj⟩
    exact ⟨fun i => barycentric_nonneg.mp hx (j.succAbove i), by linarith⟩
  · rintro ⟨hx, hs⟩
    have hj : 0 < simplexBarycentric x j := by linarith
    refine ⟨barycentric_nonneg.mpr ?_, hj⟩
    intro i
    refine Fin.succAboveCases j (le_of_lt hj) (fun r => hx r) i

def simplexChartDomain {n : ℕ} (j : Fin (n+1)) : Set (Simplex n) :=
  {x | 0 < simplexBarycentric x.val j}

def simplexChartTarget (n : ℕ) : Set (Orthant n (Fin.last n)) :=
  {y | ∑ i, y.val i < 1}

theorem isOpen_simplexChartDomain {n : ℕ} (j : Fin (n+1)) :
    IsOpen (simplexChartDomain j) :=
  isOpen_lt continuous_const
    (((continuous_apply j).comp (contDiff_barycentric n).continuous).comp continuous_subtype_val)

theorem isOpen_simplexChartTarget (n : ℕ) : IsOpen (simplexChartTarget n) := by
  apply isOpen_lt _ continuous_const
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_subtype_val

def simplexChartPatch {n : ℕ} (j : Fin (n+1)) :
    simplexChartDomain j ≃ₜ simplexChartTarget n where
  toFun := fun x => ⟨⟨simplexOmitBarycentric j x.val.val, by
    intro i _
    exact ((simplex_chart_mem_iff j x.val.val).mp ⟨x.val.property, x.property⟩).1 i⟩,
      ((simplex_chart_mem_iff j x.val.val).mp ⟨x.val.property, x.property⟩).2⟩
  invFun := fun y => by
    have h := (simplex_chart_mem_iff j (simplexRestoreBarycentric j y.val.val)).mpr
      ⟨fun i => by simpa only [omit_restore] using y.val.property i i.isLt,
        by simpa only [omit_restore] using (show ∑ i, y.val.val i < 1 from y.property)⟩
    exact ⟨⟨simplexRestoreBarycentric j y.val.val, h.1⟩, h.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact restore_omit j x.val.val
  right_inv := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact omit_restore j y.val.val
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (contDiff_omitBarycentric j).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (contDiff_restoreBarycentric j).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)

/-- The explicit affine corner chart, on the open set where λⱼ is positive. -/
noncomputable def simplexCornerChart {n : ℕ} (j : Fin (n+1)) :
    OpenPartialHomeomorph (Simplex n) (Orthant n (Fin.last n)) :=
  let U : TopologicalSpace.Opens (Simplex n) := ⟨simplexChartDomain j, isOpen_simplexChartDomain j⟩
  let V : TopologicalSpace.Opens (Orthant n (Fin.last n)) := ⟨simplexChartTarget n, isOpen_simplexChartTarget n⟩
  let y0 : V := ⟨⟨0, by simp [orthantSet]⟩, by simp [V, simplexChartTarget]⟩
  (U.openPartialHomeomorphSubtypeCoe ⟨(simplexChartPatch j).symm y0⟩).symm.trans
    ((simplexChartPatch j).toOpenPartialHomeomorph.trans
      (V.openPartialHomeomorphSubtypeCoe ⟨y0⟩))

@[simp] theorem simplexCornerChart_source {n : ℕ} (j : Fin (n+1)) :
    (simplexCornerChart j).source = simplexChartDomain j := by
  simp [simplexCornerChart]

@[simp] theorem simplexCornerChart_target {n : ℕ} (j : Fin (n+1)) :
    (simplexCornerChart j).target = simplexChartTarget n := by
  simp [simplexCornerChart]

theorem simplexCornerChart_cover {n : ℕ} (x : Simplex n) :
    ∃ j, x ∈ (simplexCornerChart j).source := by
  obtain ⟨j, hj⟩ := exists_positive_barycentric x
  exact ⟨j, by simpa [simplexChartDomain] using hj⟩

theorem simplexCornerChart_apply {n : ℕ} (j : Fin (n+1)) (x : Simplex n)
    (hx : x ∈ (simplexCornerChart j).source) :
    ((simplexCornerChart j) x).val = simplexOmitBarycentric j x.val := by
  let U : TopologicalSpace.Opens (Simplex n) := ⟨simplexChartDomain j, isOpen_simplexChartDomain j⟩
  have hne : Nonempty U := ⟨(simplexChartPatch j).symm
    ⟨⟨0, by simp [orthantSet]⟩, by simp [simplexChartTarget]⟩⟩
  let E := U.openPartialHomeomorphSubtypeCoe hne
  have hxE : x ∈ E.target := by simpa [E, U] using hx
  have hEq : (E.symm x).val = x := E.right_inv hxE
  change simplexOmitBarycentric j (E.symm x).val.val = simplexOmitBarycentric j x.val
  rw [hEq]

theorem simplexCornerChart_symm_apply {n : ℕ} (j : Fin (n+1)) (y : Orthant n (Fin.last n))
    (hy : y ∈ (simplexCornerChart j).target) :
    ((simplexCornerChart j).symm y).val = simplexRestoreBarycentric j y.val := by
  let V : TopologicalSpace.Opens (Orthant n (Fin.last n)) :=
    ⟨simplexChartTarget n, isOpen_simplexChartTarget n⟩
  have hne : Nonempty V := ⟨⟨⟨0, by simp [orthantSet]⟩, by simp [V, simplexChartTarget]⟩⟩
  let E := V.openPartialHomeomorphSubtypeCoe hne
  have hyE : y ∈ E.target := by simpa [E, V] using hy
  have hEq : (E.symm y).val = y := E.right_inv hyE
  change simplexRestoreBarycentric j (E.symm y).val.val = simplexRestoreBarycentric j y.val
  rw [hEq]

noncomputable def simplexChart {n : ℕ} (j : Fin (n+1)) : CornerChart n (Simplex n) :=
  ⟨Fin.last n, simplexCornerChart j⟩

noncomputable def simplexAtlas (n : ℕ) : Set (CornerChart n (Simplex n)) :=
  Set.range (@simplexChart n)

theorem simplexCompatible {n : ℕ} (i j : Fin (n+1)) :
    CornerCompatible (simplexChart i) (simplexChart j) := by
  let e := (simplexCornerChart i).symm.trans (simplexCornerChart j)
  have htrans : ∀ z ∈ e.source,
      (e z).val = simplexOmitBarycentric j (simplexRestoreBarycentric i z.val) := by
    intro z hz
    change z ∈ (simplexCornerChart i).target ∧
      (simplexCornerChart i).symm z ∈ (simplexCornerChart j).source at hz
    rw [OpenPartialHomeomorph.trans_apply, simplexCornerChart_apply j _ hz.2,
      simplexCornerChart_symm_apply i _ hz.1]
  have hback : ∀ z ∈ e.target,
      (e.symm z).val = simplexOmitBarycentric i (simplexRestoreBarycentric j z.val) := by
    intro z hz
    change z ∈ (simplexCornerChart j).target ∧
      (simplexCornerChart j).symm z ∈ (simplexCornerChart i).source at hz
    change ((simplexCornerChart i) ((simplexCornerChart j).symm z)).val = _
    rw [simplexCornerChart_apply i _ hz.2, simplexCornerChart_symm_apply j _ hz.1]
  constructor
  · intro x
    refine ⟨univ, isOpen_univ, mem_univ _, simplexOmitBarycentric j ∘ simplexRestoreBarycentric i,
      ((contDiff_omitBarycentric j).comp (contDiff_restoreBarycentric i)).contDiffOn, ?_⟩
    intro y _
    exact (htrans y.val y.property).symm
  · intro x
    refine ⟨univ, isOpen_univ, mem_univ _, simplexOmitBarycentric i ∘ simplexRestoreBarycentric j,
      ((contDiff_omitBarycentric i).comp (contDiff_restoreBarycentric j)).contDiffOn, ?_⟩
    intro y _
    exact (hback y.val y.property).symm

theorem simplexAtlas_isSmooth (n : ℕ) : IsSmoothCornerAtlas (simplexAtlas n) := by
  constructor
  · intro x
    obtain ⟨j, hj⟩ := simplexCornerChart_cover x
    exact ⟨simplexChart j, mem_range_self j, hj⟩
  · rintro c ⟨i, rfl⟩ d ⟨j, rfl⟩
    exact simplexCompatible i j

noncomputable def simplexCornerManifold (n : ℕ) : CornerManifold n (Simplex n) where
  hausdorff := inferInstance
  secondCountable := inferInstance
  atlas := cornerMaximalExtension (simplexAtlas n)
  maximal := SmoothManifolds.Corners.cornerMaximalExtension_isMaximal (simplexAtlas_isSmooth n)

theorem simplexChart_mem_atlas {n : ℕ} (j : Fin (n+1)) :
    simplexChart j ∈ (simplexCornerManifold n).atlas :=
  SmoothManifolds.Corners.cornerAtlas_subset_maximalExtension (simplexAtlas_isSmooth n)
    (mem_range_self j)

/-- Complete geometric interface: ordered affine charts, including dimension zero. -/
theorem simplex_corner_structure (n : ℕ) :
    ∃ S : CornerManifold n (Simplex n),
      ∃ c : Fin (n+1) → CornerChart n (Simplex n),
        (∀ j, c j ∈ S.atlas ∧ (c j).1 = Fin.last n ∧
          (c j).2.source = {x | 0 < simplexBarycentric x.val j} ∧
          (c j).2.target = {y | ∑ r, y.val r < 1} ∧
          (∀ x ∈ (c j).2.source, ((c j).2 x).val = simplexOmitBarycentric j x.val) ∧
          (∀ y ∈ (c j).2.target, ((c j).2.symm y).val = simplexRestoreBarycentric j y.val)) ∧
        (∀ x, ∃ j, x ∈ (c j).2.source) ∧
        (∀ j : Fin (n+1), ContDiff ℝ (⊤ : ℕ∞) (simplexOmitBarycentric j) ∧
          ContDiff ℝ (⊤ : ℕ∞) (simplexRestoreBarycentric j)) := by
  refine ⟨simplexCornerManifold n, simplexChart, ?_, simplexCornerChart_cover, ?_⟩
  · intro j
    exact ⟨simplexChart_mem_atlas j, rfl, simplexCornerChart_source j,
      simplexCornerChart_target j, simplexCornerChart_apply j, simplexCornerChart_symm_apply j⟩
  · intro j
    exact ⟨contDiff_omitBarycentric j, contDiff_restoreBarycentric j⟩

@[simp] theorem simplexSet_zero : simplexSet 0 = univ := by
  ext x
  simp [simplexSet]


def barycentricLinear (n : ℕ) : Euclidean n →ₗ[ℝ] Euclidean (n+1) where
  toFun := fun x => Fin.cons (-∑ i, x i) x
  map_add' := by
    intro x y
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.sum_add_distrib, add_comm]
    · simp
  map_smul' := by
    intro a x
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.mul_sum]
    · simp

def barycentricAffine (n : ℕ) : Euclidean n →ᵃ[ℝ] Euclidean (n+1) where
  toFun := simplexBarycentric
  linear := barycentricLinear n
  map_vadd' := by
    intro x v
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [simplexBarycentric, barycentricLinear, Finset.sum_add_distrib]
      ring
    · simp [simplexBarycentric, barycentricLinear]

def removeNthLinear {n : ℕ} (j : Fin (n+1)) :
    Euclidean (n+1) →ₗ[ℝ] Euclidean n where
  toFun := j.removeNth
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def omitBarycentricAffine {n : ℕ} (j : Fin (n+1)) : Euclidean n →ᵃ[ℝ] Euclidean n :=
  (removeNthLinear j).toAffineMap.comp (barycentricAffine n)

@[simp] theorem omitBarycentricAffine_apply {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    omitBarycentricAffine j x = simplexOmitBarycentric j x := rfl

noncomputable def omitBarycentricAffineEquiv {n : ℕ} (j : Fin (n+1)) :
    Euclidean n ≃ᵃ[ℝ] Euclidean n :=
  AffineEquiv.ofBijective (φ := omitBarycentricAffine j)
    ⟨Function.LeftInverse.injective (restore_omit j), Function.RightInverse.surjective (omit_restore j)⟩

@[simp] theorem omitBarycentricAffineEquiv_apply {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    omitBarycentricAffineEquiv j x = simplexOmitBarycentric j x := rfl

@[simp] theorem omitBarycentricAffineEquiv_symm_apply {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    (omitBarycentricAffineEquiv j).symm x = simplexRestoreBarycentric j x := by
  apply (omitBarycentricAffineEquiv j).injective
  simp


theorem simplex_charts_affine :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.simplex_charts_affineType := by
  intro n j
  exact ⟨omitBarycentricAffineEquiv j, omitBarycentricAffineEquiv_apply j,
    omitBarycentricAffineEquiv_symm_apply j⟩

end SmoothManifolds.CornerExamples

namespace SmoothManifolds.Corners
open Matrix

theorem determinant_of_single_row {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (i j : Fin (n+1)) (a : R)
    (hai : A j i = a) (hzero : ∀ r, r ≠ i → A j r = 0) :
    A.det = (-1 : R) ^ (j.val + i.val) * a *
      (A.submatrix j.succAbove i.succAbove).det := by
  rw [Matrix.det_succ_row A j]
  rw [Finset.sum_eq_single i]
  · rw [hai]
  · intro r _ hri
    rw [hzero r hri, mul_zero, zero_mul]
  · simp

theorem determinant_single_row_signed {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i j : Fin (n+1)) (a : ℝ)
    (hai : A j i = a) (hzero : ∀ r, r ≠ i → A j r = 0) :
    (-1 : ℝ)^j.val * A.det = a *
      ((-1 : ℝ)^i.val * (A.submatrix j.succAbove i.succAbove).det) := by
  rw [determinant_of_single_row A i j a hai hzero, pow_add]
  have hsq : (-1 : ℝ)^j.val * (-1 : ℝ)^j.val = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℝ)^j.val * ((-1)^j.val * (-1)^i.val * a *
        (A.submatrix j.succAbove i.succAbove).det) =
      ((-1 : ℝ)^j.val * (-1)^j.val) *
        (a * ((-1)^i.val * (A.submatrix j.succAbove i.succAbove).det)) := by ring
    _ = _ := by rw [hsq, one_mul]

theorem determinant_single_row_signed_pos_iff {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i j : Fin (n+1)) (a : ℝ)
    (hai : A j i = a) (hzero : ∀ r, r ≠ i → A j r = 0) (ha : 0 < a) :
    0 < (-1 : ℝ)^j.val * A.det ↔
      0 < (-1 : ℝ)^i.val * (A.submatrix j.succAbove i.succAbove).det := by
  rw [determinant_single_row_signed A i j a hai hzero]
  exact mul_pos_iff_of_pos_left ha

theorem real_sign_mul_of_pos {a b : ℝ} (ha : 0 < a) : Real.sign (a*b) = Real.sign b := by
  obtain hb | rfl | hb := lt_trichotomy b 0
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb), Real.sign_of_neg hb]
  · simp
  · rw [Real.sign_of_pos (mul_pos ha hb), Real.sign_of_pos hb]

theorem determinant_single_row_signed_sign {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i j : Fin (n+1)) (a : ℝ)
    (hai : A j i = a) (hzero : ∀ r, r ≠ i → A j r = 0) (ha : 0 < a) :
    Real.sign ((-1 : ℝ)^j.val * A.det) =
      Real.sign ((-1 : ℝ)^i.val * (A.submatrix j.succAbove i.succAbove).det) := by
  rw [determinant_single_row_signed A i j a hai hzero]
  exact real_sign_mul_of_pos ha

end SmoothManifolds.Corners

namespace SmoothManifolds.CornerExamples
open ModelData CornerData Corners Set
open scoped Topology

def boxChartTarget {n : ℕ} (a b : Euclidean n) : Set (Orthant n (Fin.last n)) :=
  {y | ∀ i, y.val i < b i - a i}

def boxInverseCoordinate {n : ℕ} (a b : Euclidean n) (ε : Fin n → Bool)
    (y : Euclidean n) : Euclidean n :=
  fun i => if ε i then b i - y i else a i + y i

def boxClamp {n : ℕ} (a b : Euclidean n) (x : Euclidean n) : Euclidean n :=
  fun i => max (a i) (min (b i) (x i))

theorem boxCoordinate_smooth {n : ℕ} (a b : Euclidean n) (ε : Fin n → Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (boxCoordinate a b ε) := by
  apply contDiff_pi.mpr
  intro i
  cases hε : ε i
  · simpa [boxCoordinate, hε] using
      (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).sub contDiff_const
  · simpa [boxCoordinate, hε] using
      contDiff_const.sub (contDiff_apply ℝ (fun _ : Fin n => ℝ) i)

theorem boxInverseCoordinate_smooth {n : ℕ} (a b : Euclidean n) (ε : Fin n → Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (boxInverseCoordinate a b ε) := by
  apply contDiff_pi.mpr
  intro i
  cases hε : ε i
  · simpa [boxInverseCoordinate, hε] using
      contDiff_const.add (contDiff_apply ℝ (fun _ : Fin n => ℝ) i)
  · simpa [boxInverseCoordinate, hε] using
      contDiff_const.sub (contDiff_apply ℝ (fun _ : Fin n => ℝ) i)

theorem boxClamp_mem {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i)
    (x : Euclidean n) : boxClamp a b x ∈ closedBoxSet a b := by
  intro i
  exact ⟨le_max_left _ _, max_le (hab i) (min_le_left _ _)⟩

theorem boxClamp_eq {n : ℕ} (a b x : Euclidean n) (hx : x ∈ closedBoxSet a b) :
    boxClamp a b x = x := by
  funext i
  simp only [boxClamp, min_eq_right (hx i).2, max_eq_right (hx i).1]

theorem boxClamp_continuous {n : ℕ} (a b : Euclidean n) : Continuous (boxClamp a b) := by
  apply continuous_pi
  intro i
  exact continuous_const.max (continuous_const.min (continuous_apply i))

theorem boxInverseCoordinate_boxCoordinate {n : ℕ} (a b x : Euclidean n) (ε : Fin n → Bool) :
    boxInverseCoordinate a b ε (boxCoordinate a b ε x) = x := by
  funext i
  cases hε : ε i <;> simp [boxInverseCoordinate, boxCoordinate, hε]

theorem boxCoordinate_boxInverseCoordinate {n : ℕ} (a b y : Euclidean n) (ε : Fin n → Bool) :
    boxCoordinate a b ε (boxInverseCoordinate a b ε y) = y := by
  funext i
  cases hε : ε i <;> simp [boxInverseCoordinate, boxCoordinate, hε]

def boxMap {n : ℕ} (a b : Euclidean n) (ε : Fin n → Bool) :
    ClosedBox a b → Orthant n (Fin.last n) :=
  fun x => ⟨boxCoordinate a b ε x.val, by
    intro i _
    cases hε : ε i
    · simpa [boxCoordinate, hε] using sub_nonneg.mpr (x.property i).1
    · simpa [boxCoordinate, hε] using sub_nonneg.mpr (x.property i).2⟩

def boxInv {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i) (ε : Fin n → Bool) :
    Orthant n (Fin.last n) → ClosedBox a b :=
  fun y => ⟨boxClamp a b (boxInverseCoordinate a b ε y.val), boxClamp_mem a b hab _⟩

theorem boxInverseCoordinate_mem {n : ℕ} (a b : Euclidean n) (ε : Fin n → Bool)
    (y : Orthant n (Fin.last n)) (hy : y ∈ boxChartTarget a b) :
    boxInverseCoordinate a b ε y.val ∈ closedBoxSet a b := by
  intro i
  have hnonneg := y.property i i.isLt
  have hlt := hy i
  cases hε : ε i <;> simp only [boxInverseCoordinate, hε, Bool.false_eq_true,
    ↓reduceIte] <;> constructor <;> linarith

theorem boxInv_eq {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i) (ε : Fin n → Bool)
    (y : Orthant n (Fin.last n)) (hy : y ∈ boxChartTarget a b) :
    (boxInv a b hab ε y).val = boxInverseCoordinate a b ε y.val :=
  boxClamp_eq a b _ (boxInverseCoordinate_mem a b ε y hy)

theorem boxChartSource_open {n : ℕ} (a b : Euclidean n) (ε : Fin n → Bool) :
    IsOpen (boxChartSource a b ε) := by
  simp only [boxChartSource, ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  cases hε : ε i
  · simpa only [hε, Bool.false_eq_true, ↓reduceIte, Function.comp_def] using
      isOpen_lt ((continuous_apply i).comp continuous_subtype_val) continuous_const
  · simpa only [hε, ↓reduceIte, Function.comp_def] using
      isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)

theorem boxChartTarget_open {n : ℕ} (a b : Euclidean n) :
    IsOpen (boxChartTarget a b) := by
  simp only [boxChartTarget, ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt ((continuous_apply i).comp continuous_subtype_val) continuous_const

def boxChart {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i) (ε : Fin n → Bool) :
    OpenPartialHomeomorph (ClosedBox a b) (Orthant n (Fin.last n)) where
  toFun := boxMap a b ε
  invFun := boxInv a b hab ε
  source := boxChartSource a b ε
  target := boxChartTarget a b
  map_source' := by
    intro x hx i
    have hxs := hx i
    have hbox := x.property i
    cases hε : ε i <;>
      simp only [boxCoordinate, boxMap, hε, Bool.false_eq_true, ↓reduceIte] at * <;> linarith
  map_target' := by
    intro y hy i
    have hys := hy i
    have hnonneg := y.property i i.isLt
    change if ε i then a i < (boxInv a b hab ε y).val i
      else (boxInv a b hab ε y).val i < b i
    rw [boxInv_eq a b hab ε y hy]
    cases hε : ε i <;>
      simp only [boxInverseCoordinate, hε, Bool.false_eq_true, ↓reduceIte] <;> linarith
  left_inv' := by
    intro x _
    apply Subtype.ext
    change boxClamp a b (boxInverseCoordinate a b ε (boxCoordinate a b ε x.val)) = x.val
    rw [boxInverseCoordinate_boxCoordinate, boxClamp_eq a b x.val x.property]
  right_inv' := by
    intro y hy
    apply Subtype.ext
    change boxCoordinate a b ε (boxInv a b hab ε y).val = y.val
    rw [boxInv_eq a b hab ε y hy, boxCoordinate_boxInverseCoordinate]
  open_source := boxChartSource_open a b ε
  open_target := boxChartTarget_open a b
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    exact (boxCoordinate_smooth a b ε).continuous.comp continuous_subtype_val
  continuousOn_invFun := by
    apply Continuous.continuousOn
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    exact (boxClamp_continuous a b).comp
      ((boxInverseCoordinate_smooth a b ε).continuous.comp continuous_subtype_val)

def boxAtlas {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i) :
    Set (CornerChart n (ClosedBox a b)) :=
  range (fun ε => (⟨Fin.last n, boxChart a b hab ε⟩ : CornerChart n (ClosedBox a b)))

theorem boxAtlas_cover {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i < b i) :
    ∀ p : ClosedBox a b, ∃ c ∈ boxAtlas a b (fun i => (hab i).le), p ∈ c.2.source := by
  classical
  intro p
  let ε : Fin n → Bool := fun i => decide (a i < p.val i)
  refine ⟨⟨Fin.last n, boxChart a b (fun i => (hab i).le) ε⟩, mem_range_self _, ?_⟩
  intro i
  by_cases h : a i < p.val i
  · simpa [ε, h] using h
  · have hbox := p.property i
    have habi := hab i
    change if ε i then a i < p.val i else p.val i < b i
    simp only [ε, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    linarith

theorem boxCharts_compatible {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i)
    (ε δ : Fin n → Bool) :
    CornerCompatible (⟨Fin.last n, boxChart a b hab ε⟩ : CornerChart n (ClosedBox a b))
      ⟨Fin.last n, boxChart a b hab δ⟩ := by
  have forward : ∀ ε δ : Fin n → Bool,
      OrthantMapContDiffOn (⊤ : ℕ∞)
        ((boxChart a b hab ε).symm.trans (boxChart a b hab δ)).source
        (fun x => ((boxChart a b hab ε).symm.trans (boxChart a b hab δ)) x.val) := by
    intro ε δ x
    refine ⟨univ, isOpen_univ, mem_univ _, boxCoordinate a b δ ∘ boxInverseCoordinate a b ε,
      ((boxCoordinate_smooth a b δ).comp (boxInverseCoordinate_smooth a b ε)).contDiffOn, ?_⟩
    intro y _
    change boxCoordinate a b δ (boxInverseCoordinate a b ε y.val.val) =
      boxCoordinate a b δ (boxInv a b hab ε y.val).val
    rw [boxInv_eq a b hab ε y.val y.property.1]
  refine ⟨forward ε δ, ?_⟩
  have h := forward δ ε
  have he : (boxChart a b hab δ).symm.trans (boxChart a b hab ε) =
      ((boxChart a b hab ε).symm.trans (boxChart a b hab δ)).symm := by
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  rw [he] at h
  exact h

theorem boxAtlas_isSmooth {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i < b i) :
    IsSmoothCornerAtlas (boxAtlas a b (fun i => (hab i).le)) := by
  refine ⟨boxAtlas_cover a b hab, ?_⟩
  rintro c ⟨ε, rfl⟩ d ⟨δ, rfl⟩
  exact boxCharts_compatible a b _ ε δ

theorem box_corner_structure (n : ℕ) (a b : Euclidean n) (hab : ∀ i, a i < b i) :
    ∃ S : CornerManifold n (ClosedBox a b), ∀ ε : Fin n → Bool,
      ∃ c ∈ S.atlas, c.1 = Fin.last n ∧ c.2.source = boxChartSource a b ε ∧
        ∀ p, (c.2 p).val = boxCoordinate a b ε p.val := by
  let hle : ∀ i, a i ≤ b i := fun i => (hab i).le
  refine ⟨⟨inferInstance, inferInstance, cornerMaximalExtension (boxAtlas a b hle),
    cornerMaximalExtension_isMaximal (boxAtlas_isSmooth a b hab)⟩, ?_⟩
  intro ε
  refine ⟨⟨Fin.last n, boxChart a b hle ε⟩,
    cornerAtlas_subset_maximalExtension (boxAtlas_isSmooth a b hab) (mem_range_self ε),
    rfl, rfl, ?_⟩
  intro p
  rfl


end SmoothManifolds.CornerExamples


namespace SmoothManifolds.CornerExamples
open ModelData CornerData Corners Set

theorem square_corner_two_faces :
    ∃ S : CornerManifold 2 (ClosedBox (0 : Euclidean 2) (fun _ => (1 : ℝ))),
      ∃ p : ClosedBox (0 : Euclidean 2) (fun _ => (1 : ℝ)),
        p.val = 0 ∧ Nat.card (LocalFaceGerm S p) = 2 := by
  obtain ⟨S, hS⟩ := box_corner_structure 2 (0 : Euclidean 2) (fun _ => (1 : ℝ)) (by intro i; norm_num)
  obtain ⟨c, hc, hck, hcs, hcm⟩ := hS (fun _ => false)
  let p : ClosedBox (0 : Euclidean 2) (fun _ => (1 : ℝ)) :=
    ⟨0, by intro i; norm_num⟩
  have hp : p ∈ c.2.source := by
    rw [hcs]
    intro i
    change (0 : ℝ) < 1
    norm_num
  have hcp : (c.2 p).val = 0 := by
    rw [hcm]
    funext i
    simp [boxCoordinate, p]
  refine ⟨S, p, rfl, ?_⟩
  rw [(local_face_cardinality S c hc p hp).2]
  simp [modelDepth, activeCoordinates, hcp, hck]
  decide

end SmoothManifolds.CornerExamples

namespace SmoothManifolds.CornerExamples
open ModelData CornerData Corners Set

/-- The signed diagonal linear part of an affine box chart. -/
def boxCoordinateLinear {n : ℕ} (ε : Fin n → Bool) :
    Euclidean n →ₗ[ℝ] Euclidean n where
  toFun := fun x i => if ε i then -x i else x i
  map_add' := by
    intro x y
    funext i
    cases h : ε i <;> simp [h, add_comm]
  map_smul' := by
    intro a x
    funext i
    cases h : ε i <;> simp [h]

def boxCoordinateAffine {n : ℕ} (a b : Euclidean n) (ε : Fin n → Bool) :
    Euclidean n →ᵃ[ℝ] Euclidean n where
  toFun := boxCoordinate a b ε
  linear := boxCoordinateLinear ε
  map_vadd' := by
    intro x v
    funext i
    cases h : ε i <;> simp [boxCoordinate, boxCoordinateLinear, h] <;> ring

noncomputable def boxCoordinateAffineEquiv {n : ℕ} (a b : Euclidean n)
    (ε : Fin n → Bool) : Euclidean n ≃ᵃ[ℝ] Euclidean n :=
  AffineEquiv.ofBijective (φ := boxCoordinateAffine a b ε)
    ⟨Function.LeftInverse.injective (fun x => boxInverseCoordinate_boxCoordinate a b x ε),
      Function.RightInverse.surjective (fun y => boxCoordinate_boxInverseCoordinate a b y ε)⟩

@[simp] theorem boxCoordinateAffineEquiv_apply {n : ℕ} (a b : Euclidean n)
    (ε : Fin n → Bool) (x : Euclidean n) :
    boxCoordinateAffineEquiv a b ε x = boxCoordinate a b ε x := rfl

@[simp] theorem boxCoordinateAffineEquiv_symm_apply {n : ℕ} (a b : Euclidean n)
    (ε : Fin n → Bool) (y : Euclidean n) :
    (boxCoordinateAffineEquiv a b ε).symm y = boxInverseCoordinate a b ε y := by
  apply (boxCoordinateAffineEquiv a b ε).injective
  rw [AffineEquiv.apply_symm_apply, boxCoordinateAffineEquiv_apply]
  exact (boxCoordinate_boxInverseCoordinate a b y ε).symm

/-- Full box chart interface, also valid for the one-point zero-dimensional box. -/
theorem box_corner_charts :
    Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry.box_corner_chartsType := by
  intro n a b hab
  let hle : ∀ i, a i ≤ b i := fun i => (hab i).le
  let c : (Fin n → Bool) → CornerChart n (ClosedBox a b) :=
    fun ε => ⟨Fin.last n, boxChart a b hle ε⟩
  refine ⟨⟨inferInstance, inferInstance, cornerMaximalExtension (boxAtlas a b hle),
    cornerMaximalExtension_isMaximal (boxAtlas_isSmooth a b hab)⟩, c, ?_, ?_, ?_⟩
  · intro ε
    refine ⟨cornerAtlas_subset_maximalExtension (boxAtlas_isSmooth a b hab)
      (mem_range_self ε), rfl, rfl, rfl, fun _ => rfl, ?_⟩
    intro y hy
    exact boxInv_eq a b hle ε y hy
  · intro x
    obtain ⟨d, ⟨ε, rfl⟩, hx⟩ := boxAtlas_cover a b hab x
    exact ⟨ε, hx⟩
  · intro ε
    refine ⟨boxCoordinateAffineEquiv a b ε,
      boxCoordinateAffineEquiv_apply a b ε,
      boxCoordinateAffineEquiv_symm_apply a b ε, ?_, ?_⟩
    · exact boxCoordinate_smooth a b ε
    · simpa only [boxCoordinateAffineEquiv_symm_apply] using
        boxInverseCoordinate_smooth a b ε

end SmoothManifolds.CornerExamples
