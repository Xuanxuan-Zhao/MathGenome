import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.Meridians
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.HilbertCharacterization.ProjectionRegularity
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue

/-! Meridian equivalence, paper.tex:9191–9235 (`fa2:p2:meridian`).

Write G for the gauge and f for the support at p, normalized by f p = 1.
For u ∈ ker f, the body projection onto span(p,u) fixes both f and dG(u).
It therefore kills every horizontal tangent w with dG(u) w = 0. The same
projection fixes dG(x) for nonzero x in that meridian, so dG(x) w = 0 too.

Consequently u ↦ G(a • (G(u)⁻¹ • u) + z • p) has derivative zero on the
punctured two-dimensional plane ker f. That domain is connected, so the
function is constant, for every a,z. Choosing gauge-one horizontal vectors
in two meridians now identifies their full gauges in the coordinates (a,z).
Closedness identifies K with {G ≤ 1}, including the endpoint heights ±1. -/
namespace ExpandedFA.HilbertCharacterization

universe u
open Set Metric Filter
open scoped Topology
open Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup
open Specs.ExpandedFA.HilbertCharacterization.ProjectionUniqueness
open Specs.ExpandedFA.HilbertCharacterization.Meridians

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Two independent vectors in radial and horizontal directions give a
coordinate injection. The normalized support extracts the second coordinate. -/
def meridianCoordinates (p u : V) : (ℝ × ℝ) →ₗ[ℝ] V :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight p

omit [FiniteDimensional ℝ V] in
@[simp] theorem meridianCoordinates_apply (p u : V) (t : ℝ × ℝ) :
    meridianCoordinates p u t = t.1 • u + t.2 • p := rfl

omit [FiniteDimensional ℝ V] in
theorem meridianCoordinates_injective {p u : V} {f : V →L[ℝ] ℝ}
    (hfp : f p = 1) (hfu : f u = 0) (hu : u ≠ 0) :
    Function.Injective (meridianCoordinates p u) := by
  apply (meridianCoordinates p u).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨a, b⟩ h
  have hb := congrArg f h
  simp [hfp, hfu] at hb
  have ha : a = 0 := by
    have : a • u = 0 := by simpa [hb] using h
    exact (smul_eq_zero.mp this).resolve_right hu
  simp [ha, hb]

omit [FiniteDimensional ℝ V] in
theorem meridianPlane_finrank {p u : V} {f : V →L[ℝ] ℝ}
    (hfp : f p = 1) (hfu : f u = 0) (hu : u ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ ({p, u} : Set V)) = 2 := by
  have hr : LinearMap.range (meridianCoordinates p u) =
      Submodule.span ℝ ({p, u} : Set V) := by
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_span_pair]
    constructor
    · rintro ⟨⟨a, b⟩, h⟩
      exact ⟨b, a, by simpa [add_comm] using h⟩
    · rintro ⟨a, b, h⟩
      exact ⟨(b, a), by simpa [add_comm] using h⟩
  rw [← hr, LinearMap.finrank_range_of_inj (meridianCoordinates_injective hfp hfu hu)]
  simp

omit [FiniteDimensional ℝ V] in
/-- A horizontal tangent annihilated by a contact support is killed by the
projection onto its meridian plane. -/
theorem meridianProjection_kills_tangent {p u w : V} {f g : V →L[ℝ] ℝ}
    (hfp : f p = 1) (hfu : f u = 0) (hgu : g u ≠ 0)
    (hfw : f w = 0) (hgw : g w = 0) (P : V →L[ℝ] V)
    (hPr : ∀ x, P x ∈ Submodule.span ℝ ({p, u} : Set V))
    (hfP : f.comp P = f) (hgP : g.comp P = g) : P w = 0 := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hPr w)
  have hfa : a = 0 := by
    have h := congrArg f hab
    have hfw' : f (P w) = 0 := by
      rw [← ContinuousLinearMap.comp_apply, hfP, hfw]
    simpa [map_add, map_smul, hfp, hfu, hfw'] using h
  have hgb : b = 0 := by
    have h := congrArg g hab
    have hgw' : g (P w) = 0 := by
      rw [← ContinuousLinearMap.comp_apply, hgP, hgw]
    simp [hfa, map_smul, hgw'] at h
    exact h.resolve_right hgu
  simpa [hfa, hgb] using hab.symm

/-- The gauge is differentiable at every nonzero vector, by the accepted
regularity theorem and the continuous support inequality. -/
theorem projection_gauge_hasFDerivAt {K : Set V} (hK : ProjectionBody K)
    {x : V} (hx : x ≠ 0) : HasFDerivAt (gauge K) (fderiv ℝ (gauge K) x) x := by
  have hc := contDiffOn_gauge_of_unique hK.2.1
    (projection_supporting_plane_unique K hK)
  exact ((hc x hx).contDiffAt
    ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hx)).differentiableAt
      (by norm_num) |>.hasFDerivAt

omit [FiniteDimensional ℝ V] in
/-- At a differentiability point, a contacting linear minorant is the derivative. -/
theorem contacting_minorant_eq_fderiv {G : V → ℝ} {x : V}
    (hd : DifferentiableAt ℝ G x) {g : V →L[ℝ] ℝ}
    (hg : ∀ y, g y ≤ G y) (hgx : g x = G x) : g = fderiv ℝ G x := by
  have hmin : IsLocalMin (fun y => G y - g y) x := by
    apply Filter.Eventually.of_forall
    intro y
    change G x - g x ≤ G y - g y
    rw [hgx, sub_self]
    exact sub_nonneg.mpr (hg y)
  exact (sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero
    (hd.hasFDerivAt.sub g.hasFDerivAt))).symm

/-- The inner and outer radii make the gauge positive away from zero. -/
theorem projection_gauge_pos {K : Set V} (hK : ProjectionBody K)
    {x : V} (hx : x ≠ 0) : 0 < gauge K x := by
  obtain ⟨r, R, hr, hR, hin, hout⟩ := symmetricConvexBody_radii K hK.2.1
  exact (div_pos (norm_pos_iff.mpr hx) hR).trans_le
    (le_gauge_of_subset_closedBall
      (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp hK.2.1.2.2.2)) hR.le hout)

/-- Euler's identity for the homogeneous gauge, using its contact support. -/
theorem projection_gauge_fderiv_self {K : Set V} (hK : ProjectionBody K)
    {x : V} (hx : x ≠ 0) : fderiv ℝ (gauge K) x x = gauge K x := by
  obtain ⟨g, hg, hgx⟩ := exists_gauge_support hK.2.1 hx
  rw [← contacting_minorant_eq_fderiv
    (projection_gauge_hasFDerivAt hK hx).differentiableAt hg hgx, hgx]

/-- A derivative of the gauge at any point of a meridian vanishes on the
horizontal tangent to its equatorial section. -/
theorem meridianGauge_tangent {K : Set V} (hK : ProjectionBody K)
    {p : V} (hp : p ∈ frontier K) {f : V →L[ℝ] ℝ}
    (hf : f ∈ NormalCone K p) (hfp : f p = 1)
    {u x w : V} (hu : u ≠ 0) (hfu : f u = 0)
    (hx : x ≠ 0) (hxL : x ∈ Submodule.span ℝ ({p, u} : Set V))
    (hfw : f w = 0) (hgw : fderiv ℝ (gauge K) u w = 0) :
    fderiv ℝ (gauge K) x w = 0 := by
  let L : CentralPlane V := ⟨Submodule.span ℝ {p, u}, meridianPlane_finrank hfp hfu hu⟩
  obtain ⟨P, hP⟩ := hK.2.2 L.subspace L.finrank_eq_two
  have hpL : p ∈ L.subspace := Submodule.subset_span (by simp)
  have huL : u ∈ L.subspace := Submodule.subset_span (by simp)
  have hfP : f.comp P = f := normalized_support_fixed_by_projection
    (projection_supporting_plane_unique K hK p hp) L.subspace P hP hpL hf hfp
  obtain ⟨g, hg, hgu⟩ := exists_gauge_support hK.2.1 hu
  obtain ⟨q, hq, hqx⟩ := exists_gauge_support hK.2.1 hx
  have hgd := contacting_minorant_eq_fderiv
    (projection_gauge_hasFDerivAt hK hu).differentiableAt hg hgu
  have hqd := contacting_minorant_eq_fderiv
    (projection_gauge_hasFDerivAt hK hx).differentiableAt hq hqx
  have hgP := gauge_support_fixed_of_differentiable hK hu
    (projection_gauge_hasFDerivAt hK hu).differentiableAt hg hgu L huL P hP
  have hqP := gauge_support_fixed_of_differentiable hK hx
    (projection_gauge_hasFDerivAt hK hx).differentiableAt hq hqx L hxL P hP
  have hgu0 : g u ≠ 0 := by
    rw [hgu]
    exact (projection_gauge_pos hK hu).ne'
  have hPw := meridianProjection_kills_tangent hfp hfu hgu0 hfw
    (hgd.symm ▸ hgw) P hP.1 hfP hgP
  rw [← hqd, ← hqP, ContinuousLinearMap.comp_apply, hPw, map_zero]

/-- Normalize a nonzero vector in the horizontal plane by its equatorial
radius. The gauge of every translated, scaled normalized direction has zero
derivative on the punctured horizontal plane. No endpoint height is excluded. -/
theorem meridianGauge_normalized_hasFDerivAt_zero {K : Set V} (hK : ProjectionBody K)
    {p : V} (hp : p ∈ frontier K) {f : V →L[ℝ] ℝ}
    (hf : f ∈ NormalCone K p) (hfp : f p = 1)
    (a z : ℝ) (ha : a ≠ 0) (u : f.ker) (hu : u ≠ 0) :
    HasFDerivAt (fun v : f.ker =>
      gauge K (a • ((gauge K (v : V))⁻¹ • (v : V)) + z • p)) (0 : f.ker →L[ℝ] ℝ) u := by
  have huV : (u : V) ≠ 0 := fun h => hu (Subtype.ext h)
  have hfu : f (u : V) = 0 := u.property
  let b := gauge K (u : V)
  have hb : b ≠ 0 := (projection_gauge_pos hK huV).ne'
  let g := fderiv ℝ (gauge K) (u : V)
  let J := f.ker.subtypeL
  let B := (ContinuousLinearMap.toSpanSingleton ℝ (-(b ^ 2)⁻¹)).comp (g.comp J)
  let D := b⁻¹ • J + B.smulRight (u : V)
  have hg := (projection_gauge_hasFDerivAt hK huV).comp u J.hasFDerivAt
  have hi : HasFDerivAt (fun v : f.ker => (gauge K (v : V))⁻¹) B u :=
    (hasFDerivAt_inv hb).comp u hg
  have hn : HasFDerivAt (fun v : f.ker => (gauge K (v : V))⁻¹ • (v : V)) D u :=
    hi.smul J.hasFDerivAt
  have hDf (w : f.ker) : f (D w) = 0 := by
    simp [D, B, J, map_add, map_smul, hfu, show f (w : V) = 0 from w.property]
  have hDg (w : f.ker) : g (D w) = 0 := by
    have hgu : g (u : V) = b := projection_gauge_fderiv_self hK huV
    simp only [D, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, B, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, map_add, map_smul, hgu]
    dsimp [J]
    field_simp
    ring
  let x := a • (b⁻¹ • (u : V)) + z • p
  have hx : x ≠ 0 := by
    intro hx
    have hz : z = 0 := by
      have h := congrArg f hx
      simpa [x, map_add, map_smul, hfu, hfp] using h
    have h : (a * b⁻¹) • (u : V) = 0 := by simpa [x, hz, smul_smul] using hx
    exact huV ((smul_eq_zero.mp h).resolve_left (mul_ne_zero ha (inv_ne_zero hb)))
  have hxL : x ∈ Submodule.span ℝ ({p, (u : V)} : Set V) := by
    exact Submodule.mem_span_pair.mpr ⟨z, a * b⁻¹, by simp [x, smul_smul, add_comm]⟩
  have hd := (projection_gauge_hasFDerivAt hK hx).comp u
    ((hn.const_smul a).add_const (z • p))
  convert hd using 1
  · rfl
  · ext w
    change 0 = fderiv ℝ (gauge K) x (a • D w)
    exact (meridianGauge_tangent hK hp hf hfp huV hfu hx hxL
      (by simp [hDf w]) (by simpa [g] using congrArg (a * ·) (hDg w))).symm

/-- The horizontal plane is two-dimensional, so deleting its origin leaves
it connected. -/
theorem supporting_ker_finrank {K : Set V} (hK : ProjectionBody K)
    {p : V} {f : V →L[ℝ] ℝ} (hfp : f p = 1) :
    Module.finrank ℝ f.ker = 2 := by
  have hfne : f.toLinearMap ≠ 0 := by
    intro h
    have hval := LinearMap.congr_fun h p
    simp [hfp] at hval
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hfne
  change Module.finrank ℝ f.ker + 1 = Module.finrank ℝ V at hd
  rw [hK.1] at hd
  omega

/-- All normalized equatorial directions give the same gauge at every height.
Constancy on the punctured plane replaces polar coordinates and integration. -/
theorem meridianGauge_normalized_eq {K : Set V} (hK : ProjectionBody K)
    {p : V} (hp : p ∈ frontier K) {f : V →L[ℝ] ℝ}
    (hf : f ∈ NormalCone K p) (hfp : f p = 1)
    (a z : ℝ) (u v : f.ker) (hu : u ≠ 0) (hv : v ≠ 0) :
    gauge K (a • ((gauge K (u : V))⁻¹ • (u : V)) + z • p) =
      gauge K (a • ((gauge K (v : V))⁻¹ • (v : V)) + z • p) := by
  by_cases ha : a = 0
  · simp [ha]
  let H : f.ker → ℝ := fun w =>
    gauge K (a • ((gauge K (w : V))⁻¹ • (w : V)) + z • p)
  have hd (w : f.ker) (hw : w ≠ 0) : HasFDerivAt H (0 : f.ker →L[ℝ] ℝ) w :=
    meridianGauge_normalized_hasFDerivAt_zero hK hp hf hfp a z ha w hw
  have hopen : IsOpen {w : f.ker | w ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hconn : IsPreconnected {w : f.ker | w ≠ 0} := by
    have hr : 1 < Module.rank ℝ f.ker := Module.one_lt_rank_of_one_lt_finrank (by
      rw [supporting_ker_finrank hK hfp]; norm_num)
    convert (isConnected_compl_singleton_of_one_lt_rank hr (0 : f.ker)).isPreconnected using 1
    ext w
    simp
  exact hopen.is_const_of_fderiv_eq_zero hconn
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).fderiv) hu hv

/-- In particular, choosing equatorial unit-gauge vectors identifies the
entire two-variable gauges of their meridian sections. -/
theorem meridianGauge_coordinates_eq {K : Set V} (hK : ProjectionBody K)
    {p : V} (hp : p ∈ frontier K) {f : V →L[ℝ] ℝ}
    (hf : f ∈ NormalCone K p) (hfp : f p = 1)
    {u v : V} (hfu : f u = 0) (hfv : f v = 0)
    (hgu : gauge K u = 1) (hgv : gauge K v = 1) (a z : ℝ) :
    gauge K (a • u + z • p) = gauge K (a • v + z • p) := by
  have hu : u ≠ 0 := by intro h; simp [h] at hgu
  have hv : v ≠ 0 := by intro h; simp [h] at hgv
  simpa [hgu, hgv] using meridianGauge_normalized_eq hK hp hf hfp a z
    (⟨u, hfu⟩ : f.ker) (⟨v, hfv⟩ : f.ker)
    (fun h => hu (congrArg Subtype.val h)) (fun h => hv (congrArg Subtype.val h))

/-- Every meridian plane has an equatorial direction normalized to gauge one. -/
theorem exists_meridian_horizontal_unit {K : Set V} (hK : ProjectionBody K)
    {p : V} {f : V →L[ℝ] ℝ} (hfp : f p = 1)
    (L : Submodule ℝ V) (hL : Module.finrank ℝ L = 2) (hpL : p ∈ L) :
    ∃ u : V, u ∈ L ∧ f u = 0 ∧ u ≠ 0 ∧ gauge K u = 1 := by
  let g : L →ₗ[ℝ] ℝ := f.toLinearMap.comp L.subtype
  have hgp : g ⟨p, hpL⟩ = 1 := hfp
  have hgn : g ≠ 0 := by
    intro h
    have hval := LinearMap.congr_fun h ⟨p, hpL⟩
    simp [hgp] at hval
  have hdim : Module.finrank ℝ g.ker = 1 := by
    have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hgn
    rw [hL] at hd
    omega
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by
    rw [hdim]; norm_num : 0 < Module.finrank ℝ g.ker)
  let u : V := ((w : L) : V)
  have huL : u ∈ L := (w : L).property
  have hfu : f u = 0 := w.property
  have hu : u ≠ 0 := fun h => hw (Subtype.ext (Subtype.ext h))
  have hb := projection_gauge_pos hK hu
  refine ⟨(gauge K u)⁻¹ • u, L.smul_mem _ huL, ?_, ?_, ?_⟩
  · simp [map_smul, hfu]
  · exact smul_ne_zero (inv_ne_zero hb.ne') hu
  · rw [gauge_smul_of_nonneg (inv_nonneg.mpr hb.le)]
    simp [hb.ne']

/-- Radial and equatorial coordinates give a linear isomorphism onto a meridian. -/
theorem exists_meridian_coordinate_equiv {p u : V} {f : V →L[ℝ] ℝ}
    (hfp : f p = 1) (hfu : f u = 0) (hu : u ≠ 0)
    (L : Submodule ℝ V) (hL : Module.finrank ℝ L = 2)
    (hpL : p ∈ L) (huL : u ∈ L) :
    ∃ e : (ℝ × ℝ) ≃ₗ[ℝ] L, ∀ t, (e t : V) = t.1 • u + t.2 • p := by
  let T : (ℝ × ℝ) →ₗ[ℝ] L := (meridianCoordinates p u).codRestrict L
    (fun t => L.add_mem (L.smul_mem t.1 huL) (L.smul_mem t.2 hpL))
  have hTi : Function.Injective T := by
    intro x y hxy
    exact meridianCoordinates_injective hfp hfu hu (congrArg Subtype.val hxy)
  have hTs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [hL] : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ L)).mp hTi
  exact ⟨LinearEquiv.ofBijective T ⟨hTi, hTs⟩, fun _ => rfl⟩

/-- Meridian equivalence for any normalized supporting functional. The equality
of gauges is global, and membership uses closedness of the original body. -/
theorem meridians_of_normalized_support {K : Set V} (hK : ProjectionBody K)
    {p : V} (hp : p ∈ frontier K) {f : V →L[ℝ] ℝ}
    (hf : f ∈ NormalCone K p) (hfp : f p = 1)
    (L M : Submodule ℝ V) (hL : Module.finrank ℝ L = 2)
    (hM : Module.finrank ℝ M = 2) (hpL : p ∈ L) (hpM : p ∈ M) :
    ∃ A : L ≃ₗ[ℝ] M, A ⟨p, hpL⟩ = ⟨p, hpM⟩ ∧
      (∀ x : L, f (A x : V) = f (x : V)) ∧
      (∀ x : L, (A x : V) ∈ K ↔ (x : V) ∈ K) := by
  obtain ⟨u, huL, hfu, hu, hgu⟩ := exists_meridian_horizontal_unit hK hfp L hL hpL
  obtain ⟨v, hvM, hfv, hv, hgv⟩ := exists_meridian_horizontal_unit hK hfp M hM hpM
  obtain ⟨eL, heL⟩ := exists_meridian_coordinate_equiv hfp hfu hu L hL hpL huL
  obtain ⟨eM, heM⟩ := exists_meridian_coordinate_equiv hfp hfv hv M hM hpM hvM
  let A : L ≃ₗ[ℝ] M := eL.symm.trans eM
  have hAe (t : ℝ × ℝ) : A (eL t) = eM t := by simp [A]
  have hpLe : eL (0, 1) = ⟨p, hpL⟩ := Subtype.ext (by simpa using heL (0, 1))
  have hpMe : eM (0, 1) = ⟨p, hpM⟩ := Subtype.ext (by simpa using heM (0, 1))
  refine ⟨A, ?_, ?_, ?_⟩
  · rw [← hpLe, hAe, hpMe]
  · intro x
    obtain ⟨t, rfl⟩ := eL.surjective x
    rw [hAe, heL, heM]
    simp [map_add, map_smul, hfu, hfv]
  · intro x
    obtain ⟨t, rfl⟩ := eL.surjective x
    rw [hAe, heL, heM]
    have hg := meridianGauge_coordinates_eq hK hp hf hfp hfu hfv hgu hgv t.1 t.2
    have hzero : K ∈ 𝓝 (0 : V) := mem_interior_iff_mem_nhds.mp hK.2.1.2.2.2
    have hmem (y : V) : y ∈ K ↔ gauge K y ≤ 1 := by
      rw [gauge_le_one_iff_mem_closure hK.2.1.2.1 hzero, hK.2.1.1.isClosed.closure_eq]
    rw [hmem, hmem, hg]

/-- `fa2:p2:meridian`: any two central sections through the chosen axis are
linearly equivalent, fixing that axis point and preserving support height. -/
theorem meridians_linearly_equivalent : meridiansType.{u} := by
  intro V _ _ _ K hK p hp
  obtain ⟨f, hf, hfp⟩ := exists_normalized_support hK.2.1 hp
  exact ⟨f, hf, hfp, fun L M hL hM hpL hpM =>
    meridians_of_normalized_support hK hp hf hfp L M hL hM hpL hpM⟩

end ExpandedFA.HilbertCharacterization
