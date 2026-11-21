import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.RegularLevel
import MathGenome.Internal.MultivariableAnalysis.D04.C04.ImplicitFunction
import MathGenome.Internal.MultivariableAnalysis.D04.C14.EmbeddedManifoldCharts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04.RegularLevel
open Specs.D04.C04.RegularLevel.Model

theorem dimension_le {n q : ℕ} (L : E n →L[ℝ] E q)
    (hL : Function.Surjective L) : q ≤ n := by
  simpa using L.toLinearMap.finrank_le_finrank_of_surjective hL

theorem zero_constraints : Specs.D04.C04.RegularLevel.zero_constraintsType := by
  intro n U g c
  ext x
  exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩

theorem empty_level : Specs.D04.C04.RegularLevel.empty_levelType := by
  intro n q r U g c hr he
  refine ⟨hr, Nat.sub_le n q, ?_⟩
  simp only [he, mem_empty_iff_false, false_implies, implies_true]

/-- A surjection has an invertible block consisting of original coordinate columns. -/
theorem exists_coordinate_block {n q : ℕ} (L : E n →L[ℝ] E q)
    (hL : Function.Surjective L) :
    ∃ s : Fin (n-q) ⊕ Fin q ≃ Fin n,
      ((L.comp (coordinateEquiv s).toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (E (n-q)) (E q))).IsInvertible := by
  classical
  let v : Fin n → E q := fun i => L (standardBasis n i)
  have hv : Submodule.span ℝ (range v) = ⊤ := by
    have he : range v = L.toLinearMap '' range (standardBasis n) := by
      ext y
      simp [v, Set.mem_range, Set.mem_image]
    rw [he, ← LinearMap.map_span, (standardBasis n).span_eq, Submodule.map_top,
      LinearMap.range_eq_top.mpr hL]
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let b : Module.Basis κ ℝ (E q) := Module.Basis.mk hli (by rw [hspan,hv])
  have hcard : Fintype.card κ = q := by
    rw [← Module.finrank_eq_card_basis b, finrank_euclideanSpace_fin]
  let eκ : Fin q ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let j : Fin q → Fin n := a ∘ eκ
  have hj : Function.Injective j := ha.comp eκ.injective
  let t : Set (Fin n) := range j
  let ej : Fin q ≃ t := Equiv.ofInjective j hj
  have ht : Fintype.card t = q := by simpa using Fintype.card_congr ej.symm
  have htc : Fintype.card ↥tᶜ = n-q := by rw [Fintype.card_compl_set, ht, Fintype.card_fin]
  let ec : Fin (n-q) ≃ ↥tᶜ := (Fintype.equivFinOfCardEq htc).symm
  let s : Fin (n-q) ⊕ Fin q ≃ Fin n :=
    (ec.sumCongr ej).trans ((Equiv.sumComm _ _).trans (Equiv.Set.sumCompl t))
  have hs (i : Fin q) : s (.inr i) = j i := rfl
  let bq : Module.Basis (Fin q) ℝ (E q) := b.reindex eκ.symm
  let T : E q ≃ₗ[ℝ] E q := (standardBasis q).equiv bq (Equiv.refl _)
  have hb (i : Fin q) : T (standardBasis q i) = L (standardBasis n (j i)) := by
    simp [T, bq, Module.Basis.equiv_apply, Module.Basis.reindex_apply, b,
      Module.Basis.coe_mk, Function.comp_def, j, v]
  have hsingle (i : Fin q) : coordinateEquiv s (0,standardBasis q i) = standardBasis n (j i) := by
    apply PiLp.ext
    intro k
    have hk : k = s (s.symm k) := (s.apply_symm_apply k).symm
    rw [hk]
    cases hsk : s.symm k with
    | inl z =>
      change Sum.elim _ _ (s.symm (s (.inl z))) = _
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, PiLp.zero_apply, standardBasis_apply]
      have hne : s (.inl z) ≠ j i := by rw [← hs]; exact s.injective.ne (by simp)
      simp [hne]
    | inr z =>
      change Sum.elim _ _ (s.symm (s (.inr z))) = _
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, standardBasis_apply]
      rw [← hs i]
      simp only [s.injective.eq_iff, Sum.inr.injEq]
  have he : (L.comp (coordinateEquiv s).toContinuousLinearMap).comp
      (ContinuousLinearMap.inr ℝ (E (n-q)) (E q)) = T.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.coe_injective
    apply (standardBasis q).ext
    intro i
    change L (coordinateEquiv s (0,standardBasis q i)) = T (standardBasis q i)
    rw [hsingle,hb]
  exact ⟨s, he ▸ ContinuousLinearMap.isInvertible_equiv⟩

namespace LevelGraph
variable {r : ℕ∞ω} {n q : ℕ} {U : Set (E n)} {g : E n → E q} {c : E q}
variable (d : LevelGraph r U g c)

@[simp] theorem projection_theta (u : E (n-q)) : d.projection (d.θ u) = u := by
  change ((coordinateEquiv d.coordinates).symm (coordinateEquiv d.coordinates (u,d.φ u))).1 = u
  simp

theorem theta_injective : Function.Injective d.θ := by
  intro u v h
  simpa using congrArg d.projection h

theorem theta_regular : ContDiffOn ℝ r d.θ d.A :=
  (coordinateEquiv d.coordinates).contDiff.contDiffOn.comp
    (contDiffOn_id.prodMk d.regular_φ) (mapsTo_univ _ _)

theorem ambient_open : IsOpen d.ambient :=
  (coordinateEquiv d.coordinates).toHomeomorph.isOpenMap _ (d.open_A.prod d.open_B)

theorem ambient_subset : d.ambient ⊆ U := d.product_subset

theorem theta_mem (u : E (n-q)) (hu : u ∈ d.A) :
    d.θ u ∈ level U g c ∩ d.ambient := by
  have ht : d.θ u ∈ d.ambient := ⟨(u,d.φ u), ⟨hu,d.map_φ hu⟩, rfl⟩
  exact ⟨⟨(ambient_subset d) ht, (d.equation u hu (d.φ u) (d.map_φ hu)).mpr rfl⟩, ht⟩

theorem inverse_mem (x : E n) (hx : x ∈ level U g c ∩ d.ambient) :
    d.projection x ∈ d.A ∧ d.θ (d.projection x) = x := by
  obtain ⟨⟨u,y⟩, ⟨hu,hy⟩, rfl⟩ := hx.2
  have he : y = d.φ u := (d.equation u hu y hy).mp hx.1.2
  simp only [Specs.D04.C04.RegularLevel.Model.LevelGraph.projection, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  exact ⟨hu, by subst y; rfl⟩

theorem image_eq : d.θ '' d.A = level U g c ∩ d.ambient := by
  apply Subset.antisymm
  · rintro x ⟨u,hu,rfl⟩
    exact theta_mem d u hu
  · intro x hx
    exact ⟨d.projection x, (inverse_mem d x hx).1, (inverse_mem d x hx).2⟩

def homeomorph : d.A ≃ₜ ↥(level U g c ∩ d.ambient) where
  toFun u := ⟨d.θ u,theta_mem d u u.property⟩
  invFun x := ⟨d.projection x,(inverse_mem d x x.property).1⟩
  left_inv u := Subtype.ext (projection_theta d u)
  right_inv x := Subtype.ext (inverse_mem d x x.property).2
  continuous_toFun := (theta_regular d).continuousOn.mapsToRestrict (fun u hu => theta_mem d u hu)
  continuous_invFun := d.projection.continuous.continuousOn.mapsToRestrict
    (fun x hx => (inverse_mem d x hx).1)

theorem derivative_injective (hr : 1 ≤ r) (u : E (n-q)) (hu : u ∈ d.A) :
    Function.Injective (fderiv ℝ d.θ u) := by
  have ht := ((theta_regular d).differentiableOn (ne_of_gt (lt_of_lt_of_le zero_lt_one hr)) u hu).differentiableAt (d.open_A.mem_nhds hu)
  have hid : d.projection ∘ d.θ = id := funext (projection_theta d)
  have hd : d.projection.comp (fderiv ℝ d.θ u) = ContinuousLinearMap.id ℝ (E (n-q)) := by
    have h := d.projection.hasFDerivAt.comp u ht.hasFDerivAt
    rw [hid] at h
    exact h.unique (hasFDerivAt_id u)
  intro v w hvw
  have he := congrArg d.projection hvw
  simpa only [← ContinuousLinearMap.comp_apply, hd, ContinuousLinearMap.id_apply] using he

theorem kernel_eq (hr : 1 ≤ r) (hU : IsOpen U) (hg : ContDiffOn ℝ r g U)
    (u : E (n-q)) (hu : u ∈ d.A) :
    LinearMap.range (fderiv ℝ d.θ u).toLinearMap =
      LinearMap.ker (fderiv ℝ g (d.θ u)).toLinearMap := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have ht := ((theta_regular d).differentiableOn hr0 u hu).differentiableAt (d.open_A.mem_nhds hu)
  have hgu := (hg.differentiableOn hr0 (d.θ u) (theta_mem d u hu).1.1).differentiableAt
    (hU.mem_nhds (theta_mem d u hu).1.1)
  have hc : (g ∘ d.θ) =ᶠ[𝓝 u] (fun _ => c) := by
    filter_upwards [d.open_A.mem_nhds hu] with v hv
    exact (theta_mem d v hv).1.2
  have hz : (fderiv ℝ g (d.θ u)).comp (fderiv ℝ d.θ u) = 0 :=
    ((hgu.hasFDerivAt.comp u ht.hasFDerivAt).congr_of_eventuallyEq hc.symm).unique
      (hasFDerivAt_const c u)
  have hle : LinearMap.range (fderiv ℝ d.θ u).toLinearMap ≤
      LinearMap.ker (fderiv ℝ g (d.θ u)).toLinearMap := by
    rintro v ⟨w,rfl⟩
    change ((fderiv ℝ g (d.θ u)).comp (fderiv ℝ d.θ u)) w = 0
    rw [hz]
    rfl
  have hs : Function.Surjective (fderiv ℝ g (d.θ u)) := by
    have hcomp : fderiv ℝ (g ∘ coordinateEquiv d.coordinates) (u,d.φ u) =
        (fderiv ℝ g (d.θ u)).comp (coordinateEquiv d.coordinates).toContinuousLinearMap :=
      (hgu.hasFDerivAt.comp (u,d.φ u) (coordinateEquiv d.coordinates).hasFDerivAt).fderiv
    intro y
    obtain ⟨w,hw⟩ := (d.solved_invertible u hu).surjective y
    refine ⟨coordinateEquiv d.coordinates (0,w), ?_⟩
    simpa only [ContinuousLinearMap.comp_apply, hcomp, ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.coe_coe] using hw
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (derivative_injective d hr u hu), finrank_euclideanSpace_fin]
  have hd := (fderiv ℝ g (d.θ u)).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin] at hd
  exact Nat.sub_eq_of_eq_add (by simpa only [add_comm] using hd.symm)

/-- The chain-rule direction needs no regularity of the level itself. -/
theorem velocity_in_kernel (hU : IsOpen U) (hg : DifferentiableOn ℝ g U)
    {x v : E n} (hx : x ∈ U) (hv : CurveVelocity (level U g c) x v) :
    fderiv ℝ g x v = 0 := by
  obtain ⟨ε,γ,hε,hγ0,hγM,_,hγ⟩ := hv
  have hxg := (hg x hx).differentiableAt (hU.mem_nhds hx)
  have hcomp := (show HasFDerivAt g (fderiv ℝ g x) (γ 0) by simpa [hγ0] using hxg.hasFDerivAt).comp_hasDerivAt 0 hγ
  have he : (g ∘ γ) =ᶠ[𝓝 0] (fun _ => c) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0:ℝ) ∈ Ioo (-ε) ε by constructor <;> linarith)] with t ht
    exact (hγM ht).2
  exact (hcomp.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const 0 c)

/-- Every tangent image vector is the velocity of a short graph of a line. -/
theorem image_velocity (hr : 1 ≤ r) (u : E (n-q)) (hu : u ∈ d.A) (w : E (n-q)) :
    CurveVelocity (level U g c) (d.θ u) (fderiv ℝ d.θ u w) := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  let l : ℝ → E (n-q) := fun t => u + t • w
  have hl : Continuous l := continuous_const.add (continuous_id.smul continuous_const)
  have hl0 : l 0 = u := by simp [l]
  have hn : l ⁻¹' d.A ∈ 𝓝 0 := hl.continuousAt.preimage_mem_nhds (by simpa [hl0] using d.open_A.mem_nhds hu)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
  have hmap : MapsTo l (Ioo (-ε) ε) d.A := by
    intro t ht
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] using (show -ε < t ∧ t < ε from ht)
  refine ⟨ε, d.θ ∘ l, hε, by simp [hl0], ?_, ?_, ?_⟩
  · intro t ht
    exact (theta_mem d (l t) (hmap ht)).1
  · exact ((theta_regular d).of_le hr).comp
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn hmap
  · have hdθ := ((theta_regular d).differentiableOn hr0 u hu).differentiableAt (d.open_A.mem_nhds hu)
    have hdl : HasDerivAt l w 0 := by
      simpa [l] using (hasDerivAt_id (0:ℝ)).smul_const w |>.const_add u
    exact (show HasFDerivAt d.θ (fderiv ℝ d.θ u) (l 0) by simpa [hl0] using hdθ.hasFDerivAt).comp_hasDerivAt 0 hdl

/-- Graph data give actual charts for the shared embedded-manifold interface. -/
def embeddedChart (hr : 1 ≤ r) : EmbeddedChart r (n-q) n (level U g c) where
  half := false
  half_pos := by simp
  source := d.A
  source_open := ⟨d.A, d.open_A, by
    simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩
  ambient := d.ambient
  ambient_open := ambient_open d
  toFun := d.θ
  invFun := d.projection
  map_source := fun u hu => theta_mem d u hu
  map_target := fun x hx => (inverse_mem d x hx).1
  left_inv := fun u _ => projection_theta d u
  right_inv := fun x hx => (inverse_mem d x hx).2
  continuous_toFun := (theta_regular d).continuousOn
  continuous_invFun := d.projection.continuous.continuousOn
  regular := (open_fullRankLocalExtension_iff d.A d.θ d.open_A).mpr
    ⟨theta_regular d, derivative_injective d hr⟩

theorem transition (e : LevelGraph r U g c) :
    IsOpen (d.overlap e) ∧ ContDiffOn ℝ r (e.projection ∘ d.θ) (d.overlap e) ∧
    MapsTo (e.projection ∘ d.θ) (d.overlap e) (e.overlap d) ∧
    ∀ u ∈ d.overlap e, d.projection (e.θ (e.projection (d.θ u))) = u := by
  refine ⟨(theta_regular d).continuousOn.isOpen_inter_preimage d.open_A (ambient_open e),
    e.projection.contDiff.comp_contDiffOn ((theta_regular d).mono inter_subset_left), ?_, ?_⟩
  · intro u hu
    have hxe : d.θ u ∈ level U g c ∩ e.ambient := ⟨(theta_mem d u hu.1).1,hu.2⟩
    have hx := inverse_mem e (d.θ u) hxe
    refine ⟨hx.1, ?_⟩
    change e.θ (e.projection (d.θ u)) ∈ d.ambient
    rw [hx.2]
    exact (theta_mem d u hu.1).2
  · intro u hu
    have hx := inverse_mem e (d.θ u) ⟨(theta_mem d u hu.1).1,hu.2⟩
    rw [hx.2, projection_theta]

end LevelGraph

theorem graph_geometry : Specs.D04.C04.RegularLevel.graph_geometryType := by
  intro r n q U g c hr hU hg d
  refine ⟨LevelGraph.ambient_open d, LevelGraph.ambient_subset d, LevelGraph.image_eq d,
    LevelGraph.theta_injective d, LevelGraph.theta_regular d,
    ⟨LevelGraph.homeomorph d, fun _ => rfl⟩, ?_⟩
  intro u hu
  have hk := LevelGraph.kernel_eq d hr hU hg u hu
  refine ⟨LevelGraph.derivative_injective d hr u hu, hk, ?_⟩
  intro v
  constructor
  · exact LevelGraph.velocity_in_kernel hU
      (hg.differentiableOn (ne_of_gt (lt_of_lt_of_le zero_lt_one hr)))
      (LevelGraph.theta_mem d u hu).1.1
  · intro hv
    have hv' : v ∈ LinearMap.range (fderiv ℝ d.θ u).toLinearMap := by
      rw [hk]
      exact hv
    obtain ⟨w, rfl⟩ := hv'
    exact LevelGraph.image_velocity d hr u hu w

theorem graph_transitions : Specs.D04.C04.RegularLevel.graph_transitionsType := by
  intro r n q U g c d e
  obtain ⟨ho,hr,hm,hi⟩ := LevelGraph.transition d e
  obtain ⟨ho',hr',hm',hi'⟩ := LevelGraph.transition e d
  exact ⟨ho,hr,hm,ho',hr',hm',hi,hi'⟩

open private implicit_neighborhood from MathGenome.Internal.MultivariableAnalysis.D04.C04.ImplicitFunction

/-- Construct the graph from the coordinate block; no manifold theorem is used. -/
theorem regular_level_local : Specs.D04.C04.RegularLevel.regular_level_localType := by
  intro n q r U g c a hr hU hg ha hsurj
  have hq : q ≤ n := dimension_le _ hsurj
  obtain ⟨s,hs⟩ := exists_coordinate_block (fderiv ℝ g a) hsurj
  let e := coordinateEquiv s
  let z := e.symm a
  let W := e ⁻¹' U
  let G : E (n-q) × E q → E q := g ∘ e
  have hW : IsOpen W := hU.preimage e.continuous
  have hG : ContDiffOn ℝ r G W := hg.comp e.contDiff.contDiffOn (fun _ hz => hz)
  have hz : z ∈ W := by simpa [W,z] using ha.1
  have hcz : G z = c := by simpa [G,z] using ha.2
  have hga := (hg.differentiableOn (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1)) a ha.1).differentiableAt
    (hU.mem_nhds ha.1)
  have hcomp : fderiv ℝ G z = (fderiv ℝ g a).comp e.toContinuousLinearMap := by
    have h := (show HasFDerivAt g (fderiv ℝ g a) (e z) by simpa [z] using hga.hasFDerivAt).comp z e.hasFDerivAt
    exact h.fderiv
  have hblock : (Specs.D04.C04.ImplicitFunction.Model.solvedDerivative G z).IsInvertible := by
    change ((fderiv ℝ G z).comp (ContinuousLinearMap.inr ℝ (E (n-q)) (E q))).IsInvertible
    rw [hcomp]
    exact hs
  obtain ⟨A,B,φ,hgeom,hφ⟩ := implicit_neighborhood W G z.1 z.2 c hr.1 hW hG hz hcz hblock
  obtain ⟨hA,hB,haA,hbB,hAB,hmap,hφa,hiff,_,hderiv⟩ := hgeom
  let d : LevelGraph r U g c :=
    { coordinates := s
      A := A
      B := B
      open_A := hA
      open_B := hB
      φ := φ
      regular_φ := hφ
      map_φ := hmap
      product_subset := by rintro x ⟨w,hw,rfl⟩; exact hAB hw
      equation := hiff
      solved_invertible := fun u hu => (hderiv u hu).1 }
  refine ⟨hq,d,?_,graph_geometry hr.1 hU hg d⟩
  exact ⟨z,⟨haA,hbB⟩, e.apply_symm_apply a⟩

/-- All centers have the constructed full-space graph chart. Empty levels need
no dimension inequality q≤n: n-q≤n is the dimension condition of the predicate. -/
theorem regular_level_manifold : Specs.D04.C04.RegularLevel.regular_level_manifoldType := by
  intro n q r U g c hr hU hg hreg
  have hcharts (a : E n) (ha : a ∈ level U g c) :
      ∃ (d : LevelGraph r U g c) (h : EmbeddedChart r (n-q) n (level U g c)) (u : E (n-q)),
      h.half = false ∧ h.source = d.A ∧ h.ambient = d.ambient ∧
      h.toFun = d.θ ∧ h.invFun = d.projection ∧ CenteredAt h u ∧ h.toFun u = a := by
    obtain ⟨_,d,had,_⟩ := regular_level_local r U g c a hr hU hg ha (hreg a ha)
    have hinv := LevelGraph.inverse_mem d a ⟨ha,had⟩
    refine ⟨d, LevelGraph.embeddedChart d hr.1, d.projection a, rfl,rfl,rfl,rfl,rfl,?_,hinv.2⟩
    exact ⟨hinv.1, by simp [LevelGraph.embeddedChart]⟩
  refine ⟨⟨hr, Nat.sub_le n q, ?_⟩, hcharts⟩
  intro a ha
  obtain ⟨_,h,u,_,_,_,_,_,hu,hea⟩ := hcharts a ha
  exact ⟨h,u,hu,hea⟩

theorem full_codimension : Specs.D04.C04.RegularLevel.full_codimensionType := by
  intro n r U g c a hr hU hg ha hsurj
  obtain ⟨_,d,had,_⟩ := regular_level_local r U g c a hr hU hg ha hsurj
  have : Subsingleton (E (n-n)) := by rw [Nat.sub_self]; infer_instance
  have hinv := LevelGraph.inverse_mem d a ⟨ha,had⟩
  refine ⟨⟨d.ambient, LevelGraph.ambient_open d, had, ?_⟩, ?_⟩
  · ext x
    constructor
    · intro hx
      have hxi := LevelGraph.inverse_mem d x hx
      have he : d.projection x = d.projection a := Subsingleton.elim _ _
      rw [he,hinv.2] at hxi
      exact mem_singleton_iff.mpr hxi.2.symm
    · intro hx
      rw [mem_singleton_iff.mp hx]
      exact ⟨ha,had⟩
  · exact LinearMap.ker_eq_bot.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (show Module.finrank ℝ (E n) = Module.finrank ℝ (E n) from rfl)).mpr hsurj)

end D04.RegularLevel
