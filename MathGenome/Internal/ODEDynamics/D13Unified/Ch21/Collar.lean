import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.Collar
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.CircleLift
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Covering.AddCircle
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace D13Unified.Ch21.Collar
noncomputable section
open Set Filter Function
open scoped Topology ContDiff
open Specs.D13Unified.Ch21.Collar

theorem lift_periodic (γ : Circle → ℂ) : Periodic (realLift γ) 1 := by
  intro t
  change γ ((t + 1 : ℝ) : AddCircle (1 : ℝ)) = γ (t : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add_period]

theorem lift_eq_iff (γ : Circle → ℂ) (hγ : Injective γ) (t u : ℝ) :
    realLift γ t = realLift γ u ↔ ∃ k : ℤ, t - u = (k : ℝ) := by
  change γ (q t) = γ (q u) ↔ _
  rw [hγ.eq_iff, Ch15.CircleLift.quotientMap_eq_iff]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by linarith⟩

theorem lift_trace (γ : Circle → ℂ) : range (realLift γ) = range γ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨q t, rfl⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨u, rfl⟩ := Ch15.CircleLift.quotientMap_surjective t
    exact ⟨u, rfl⟩

theorem regularity_bridge (γ : Circle → ℂ) : RegularEmbeddedLoop γ ↔
    ContDiff ℝ 1 (realLift γ) ∧
    (∀ t u : ℝ, realLift γ t = realLift γ u ↔ ∃ k : ℤ, t - u = (k : ℝ)) ∧
    ∀ t : ℝ, deriv (realLift γ) t ≠ 0 := by
  constructor
  · rintro ⟨hc, hi, hr⟩
    exact ⟨hc, lift_eq_iff γ hi, hr⟩
  · rintro ⟨hc, he, hr⟩
    refine ⟨hc, ?_, hr⟩
    intro x y hxy
    obtain ⟨t, rfl⟩ := Ch15.CircleLift.quotientMap_surjective x
    obtain ⟨u, rfl⟩ := Ch15.CircleLift.quotientMap_surjective y
    obtain ⟨k, hk⟩ := (he t u).mp hxy
    exact (Ch15.CircleLift.quotientMap_eq_iff t u).mpr ⟨k, by linarith⟩

theorem circleC1_continuous {γ : Circle → ℂ} (hγ : CircleC1 γ) : Continuous γ := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact hγ.continuous

/-- The regularity convention is exactly the one from local covering charts. -/
theorem coveringC1_bridge (γ : Circle → ℂ) : CircleC1 γ ↔ ∀ t : ℝ, ∃ U : Set ℝ,
    IsOpen U ∧ t ∈ U ∧ Topology.IsOpenEmbedding (U.domRestrict q) ∧
    ContDiffOn ℝ 1 (realLift γ) U := by
  constructor
  · intro hg t
    obtain ⟨e, ht, he⟩ := AddCircle.isLocalHomeomorph_coe (1 : ℝ) t
    refine ⟨e.source, e.open_source, ht, ?_, hg.contDiffOn⟩
    have he' : q = (e : ℝ → Circle) := he
    rw [he']
    exact e.isOpenEmbedding_restrict
  · intro h
    apply contDiff_iff_contDiffAt.mpr
    intro t
    obtain ⟨U, hU, ht, _, hc⟩ := h t
    exact (hc t ht).contDiffAt (hU.mem_nhds ht)

theorem derivative_periodic (γ : Circle → ℂ) : Periodic (deriv (realLift γ)) 1 := by
  intro t
  rw [← deriv_comp_add_const]
  exact congrArg (fun f : ℝ → ℂ => deriv f t) (funext (lift_periodic γ))

/-- The tangent descends to the same quotient as the curve. -/
def tangent (γ : Circle → ℂ) : Circle → ℂ := (derivative_periodic γ).lift

@[simp] theorem tangent_coe (γ : Circle → ℂ) (t : ℝ) :
    tangent γ (q t) = deriv (realLift γ) t := rfl

theorem tangent_continuous {γ : Circle → ℂ} (hγ : CircleC1 γ) :
    Continuous (tangent γ) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact hγ.continuous_deriv_one

theorem tangent_ne_zero {γ : Circle → ℂ} (hγ : RegularEmbeddedLoop γ) (t : Circle) :
    tangent γ t ≠ 0 := by
  obtain ⟨u, rfl⟩ := Ch15.CircleLift.quotientMap_surjective t
  exact hγ.2.2 u

theorem det_eq_im (u v : ℂ) : det u v = (star u * v).im := by
  simp only [det, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem det_left_normal (u : ℂ) : det u (Complex.I * u) = ‖u‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [det, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, zero_sub, Complex.normSq_apply]
  ring

/-- Transversality is preserved by a sufficiently close approximation to i*u. -/
theorem det_positive_of_close {u v : ℂ} (hu : u ≠ 0)
    (hv : dist v (Complex.I * u) < ‖u‖ / 2) : 0 < det u v := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hb : |det u (v - Complex.I * u)| ≤ ‖u‖ * ‖v - Complex.I * u‖ := by
    rw [det_eq_im]
    exact (Complex.abs_im_le_norm _).trans (by simp)
  have he : det u (v - Complex.I * u) = det u v - ‖u‖ ^ 2 := by
    rw [← det_left_normal u]
    simp only [det, Complex.sub_re, Complex.sub_im]
    ring
  rw [he] at hb
  rw [dist_eq_norm] at hv
  have hm := mul_lt_mul_of_pos_left hv hn
  have hl := (abs_le.mp hb).1
  nlinarith

/-- Build the field by extending from the compact embedded trace, smoothing in
 the ambient Euclidean plane, and restricting back to the curve. -/
theorem transverse_exists (γ : Circle → ℂ) (hγ : RegularEmbeddedLoop γ) :
    ∃ v : Circle → ℂ, CircleC1 v ∧
      ∀ t : ℝ, 0 < det (deriv (realLift γ) t) (v (q t)) := by
  let : TietzeExtension ℂ := TietzeExtension.of_homeo Complex.equivRealProdCLM.toHomeomorph
  have hgc : Continuous γ := circleC1_continuous hγ.1
  have htc : Continuous (tangent γ) := tangent_continuous hγ.1
  let n : C(Circle, ℂ) := ⟨fun t => Complex.I * tangent γ t, continuous_const.mul htc⟩
  obtain ⟨N, hN⟩ := n.exists_extension' (hgc.isClosedEmbedding hγ.2.1)
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set Circle).Nonempty)
    htc.norm.continuousOn
  have hm : 0 < ‖tangent γ t₀‖ := norm_pos_iff.mpr (tangent_ne_zero hγ t₀)
  obtain ⟨V, hV, hVN, -⟩ := N.continuous.exists_contDiff_approx (n := 1)
    (ε := fun _ => ‖tangent γ t₀‖ / 2) continuous_const (fun _ => half_pos hm)
  refine ⟨fun t => V (γ t), ?_, ?_⟩
  · exact hV.comp hγ.1
  · intro t
    apply det_positive_of_close (hγ.2.2 t)
    have he : N (γ (q t)) = Complex.I * tangent γ (q t) := congrFun hN (q t)
    rw [← tangent_coe γ t, ← he]
    exact (hVN (γ (q t))).trans_le (div_le_div_of_nonneg_right (ht₀ (mem_univ _)) (by norm_num))

/-- Compactness upgrades injectivity on the zero section and local injectivity
there to injectivity on one entire cylinder. No differential hypothesis is used. -/
theorem uniform_injective_near_zero {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    (F : X × ℝ → Y) (hc : Continuous F)
    (hi : Injective (fun x => F (x, 0)))
    (hloc : ∀ x : X, ∃ U ∈ 𝓝 (x, (0 : ℝ)), InjOn F U) :
    ∃ a : ℝ, 0 < a ∧ InjOn F (univ ×ˢ Ioo (-a) a) := by
  let P : (ℝ × ℝ) → (X × X) → Prop := fun r xy =>
    F (xy.1, r.1) = F (xy.2, r.2) → (xy.1, r.1) = (xy.2, r.2)
  have hP : ∀ xy : X × X, ∀ᶠ z : (ℝ × ℝ) × (X × X) in 𝓝 ((0, 0), xy),
      P z.1 z.2 := by
    intro xy
    have h₁ : Continuous (fun z : (ℝ × ℝ) × (X × X) => (z.2.1, z.1.1)) := by fun_prop
    have h₂ : Continuous (fun z : (ℝ × ℝ) × (X × X) => (z.2.2, z.1.2)) := by fun_prop
    by_cases he : xy.1 = xy.2
    · obtain ⟨U, hU, hUi⟩ := hloc xy.1
      have he' : (xy.2, (0 : ℝ)) = (xy.1, 0) := by rw [he]
      have hu₁ := (h₁.continuousAt (x := ((0, 0), xy))).eventually hU
      have hu₂ := (h₂.continuousAt (x := ((0, 0), xy))).eventually (he' ▸ hU)
      filter_upwards [hu₁, hu₂] with z hz₁ hz₂
      exact fun h => hUi hz₁ hz₂ h
    · have hne : F (xy.1, 0) ≠ F (xy.2, 0) := fun h => he (hi h)
      have hn := ((hc.comp h₁).continuousAt (x := ((0, 0), xy))).ne_iff_eventually_ne
        ((hc.comp h₂).continuousAt (x := ((0, 0), xy))) |>.mp hne
      filter_upwards [hn] with z hz
      exact fun h => (hz h).elim
  have hh : ∀ᶠ r in 𝓝 ((0, 0) : ℝ × ℝ), ∀ xy : X × X, P r xy := by
    have hh' := isCompact_univ.eventually_forall_of_forall_eventually
      (fun xy (_ : xy ∈ (univ : Set (X × X))) => hP xy)
    simpa only [mem_univ, forall_const] using hh'
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨a, ha, ?_⟩
  intro p hp s hs hps
  apply hball (show (p.2, s.2) ∈ Metric.ball ((0, 0) : ℝ × ℝ) a from ?_) (p.1, s.1) hps
  simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff,
    abs_lt, mem_Ioo] using And.intro hp.2 hs.2

/-- Derivative with columns u and v in standard real coordinates. -/
def columnMap (u v : ℂ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v

@[simp] theorem columnMap_apply (u v : ℂ) (z : ℝ × ℝ) :
    columnMap u v z = z.1 • u + z.2 • v := rfl

theorem columnMap_injective {u v : ℂ} (h : det u v ≠ 0) : Injective (columnMap u v) := by
  apply (columnMap u v).ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  change z.1 • u + z.2 • v = 0 at hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.zero_re, Complex.zero_im] at hr hi
  have h₁ : det u v * z.1 = 0 := by
    dsimp [det]
    linear_combination v.im * hr - v.re * hi
  have h₂ : det u v * z.2 = 0 := by
    dsimp [det]
    linear_combination u.re * hi - u.im * hr
  exact Prod.ext ((mul_eq_zero.mp h₁).resolve_left h) ((mul_eq_zero.mp h₂).resolve_left h)

def columnEquiv (u v : ℂ) (h : det u v ≠ 0) : (ℝ × ℝ) ≃L[ℝ] ℂ :=
  ((columnMap u v).toLinearMap.linearEquivOfInjective (columnMap_injective h)
    (by simp [Module.finrank_prod, Complex.finrank_real_complex])).toContinuousLinearEquiv

@[simp] theorem columnEquiv_coe (u v : ℂ) (h : det u v ≠ 0) :
    (columnEquiv u v h : (ℝ × ℝ) →L[ℝ] ℂ) = columnMap u v := by
  apply ContinuousLinearMap.ext
  intro z
  rfl

def realCollar (γ v : Circle → ℂ) : ℝ × ℝ → ℂ :=
  fun p => realLift γ p.1 + p.2 • realLift v p.1

theorem realCollar_contDiff {γ v : Circle → ℂ} (hg : CircleC1 γ) (hv : CircleC1 v) :
    ContDiff ℝ 1 (realCollar γ v) :=
  (hg.comp contDiff_fst).add (contDiff_snd.smul (hv.comp contDiff_fst))

theorem realCollar_hasFDerivAt {γ v : Circle → ℂ} (hg : CircleC1 γ) (hv : CircleC1 v)
    (p : ℝ × ℝ) : HasFDerivAt (realCollar γ v)
      (columnMap (deriv (realLift γ) p.1 + p.2 • deriv (realLift v) p.1) (realLift v p.1)) p := by
  have h₁ := ((hg.differentiable (by norm_num)).differentiableAt.hasDerivAt.hasFDerivAt).comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have h₂ := ((hv.differentiable (by norm_num)).differentiableAt.hasDerivAt.hasFDerivAt).comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have h₃ := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).smul h₂
  apply (h₁.add h₃).congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  simp [columnMap, ContinuousLinearMap.comp_apply, smul_add]
  ring

/-- The determinant remains positive on one uniform cylinder. -/
theorem uniform_positive_jacobian {γ v : Circle → ℂ} (hg : CircleC1 γ) (hv : CircleC1 v)
    (ht : ∀ t : ℝ, 0 < det (deriv (realLift γ) t) (v (q t))) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : Circle, ∀ r ∈ Ioo (-a) a,
      0 < det (tangent γ c + r • tangent v c) (v c) := by
  have hgc := tangent_continuous hg
  have hvc := tangent_continuous hv
  have hv' := circleC1_continuous hv
  let J : ℝ × Circle → ℝ := fun p => det (tangent γ p.2 + p.1 • tangent v p.2) (v p.2)
  have hJ : Continuous J := by unfold J det; fun_prop
  have hpos : ∀ c : Circle, 0 < J (0, c) := by
    intro c
    obtain ⟨t, rfl⟩ := Ch15.CircleLift.quotientMap_surjective c
    simpa [J] using ht t
  have hh : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ c : Circle, 0 < J (r, c) := by
    have hP : ∀ c ∈ (univ : Set Circle), ∀ᶠ z : ℝ × Circle in 𝓝 (0, c), 0 < J z := by
      intro c _
      exact (hJ.continuousAt (x := (0, c))).eventually (Ioi_mem_nhds (hpos c))
    have hh' := isCompact_univ.eventually_forall_of_forall_eventually
      (P := fun r c => 0 < J (r, c)) hP
    simpa only [mem_univ, forall_const, mem_Ioi] using hh'
  obtain ⟨a, ha, hb⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨a, ha, fun c r hr => hb ?_ c⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hr

/-- The product covering coordinates for the cylinder. -/
def quotientCylinder : ℝ × ℝ → Circle × ℝ := fun p => (q p.1, p.2)

theorem quotientCylinder_surjective : Surjective quotientCylinder := by
  rintro ⟨c, r⟩
  obtain ⟨t, rfl⟩ := Ch15.CircleLift.quotientMap_surjective c
  exact ⟨(t, r), rfl⟩

theorem quotientCylinder_localHomeomorph : IsLocalHomeomorph quotientCylinder := by
  intro p
  obtain ⟨e, he, hq⟩ := AddCircle.isLocalHomeomorph_coe (1 : ℝ) p.1
  refine ⟨e.prod (OpenPartialHomeomorph.refl ℝ), ⟨he, mem_univ _⟩, ?_⟩
  funext z
  exact Prod.ext (congrFun hq z.1) rfl

theorem collarMap_continuous {γ v : Circle → ℂ} (hg : CircleC1 γ) (hv : CircleC1 v) :
    Continuous (collarMap γ v) :=
  ((circleC1_continuous hg).comp continuous_fst).add
    (continuous_snd.smul ((circleC1_continuous hv).comp continuous_fst))

/-- Nonzero determinant gives an actual C¹ real local inverse. -/
theorem realCollar_local_inverse {γ v : Circle → ℂ} (hg : CircleC1 γ) (hv : CircleC1 v)
    (p : ℝ × ℝ)
    (hd : det (deriv (realLift γ) p.1 + p.2 • deriv (realLift v) p.1) (realLift v p.1) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      p ∈ e.source ∧ (∀ z, e z = realCollar γ v z) ∧
      ContDiffAt ℝ 1 e.symm (realCollar γ v p) := by
  let L := columnEquiv _ _ hd
  have hf : HasFDerivAt (realCollar γ v) (L : (ℝ × ℝ) →L[ℝ] ℂ) p := by
    rw [show (L : (ℝ × ℝ) →L[ℝ] ℂ) = columnMap _ _ from columnEquiv_coe _ _ hd]
    exact realCollar_hasFDerivAt hg hv p
  have hc := (realCollar_contDiff hg hv).contDiffAt (x := p)
  exact ⟨hc.toOpenPartialHomeomorph _ hf (by norm_num),
    hc.mem_toOpenPartialHomeomorph_source hf (by norm_num), fun _ => rfl,
    hc.to_localInverse hf (by norm_num)⟩

theorem collarMap_localHomeomorphOn {γ v : Circle → ℂ} (hg : CircleC1 γ) (hv : CircleC1 v)
    (a : ℝ) (hd : ∀ c : Circle, ∀ r ∈ Ioo (-a) a,
      det (tangent γ c + r • tangent v c) (v c) ≠ 0) :
    IsLocalHomeomorphOn (collarMap γ v) (cylinder a) := by
  have hf : IsLocalHomeomorphOn (collarMap γ v ∘ quotientCylinder)
      (quotientCylinder ⁻¹' cylinder a) := by
    intro p hp
    obtain ⟨e, he, heq, -⟩ := realCollar_local_inverse hg hv p (hd (q p.1) p.2 hp.2)
    exact ⟨e, he, funext fun z => (heq z).symm⟩
  have hh := hf.of_comp_right (quotientCylinder_localHomeomorph.isLocalHomeomorphOn)
  simpa only [image_preimage_eq _ quotientCylinder_surjective] using hh

/-- An injective local homeomorphism on an open set gives a single chart whose
source is that entire open set, without requiring global injectivity outside it. -/
theorem open_chart_of_injOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] (F : X → Y) (S : Set X) (hS : IsOpen S)
    (hl : IsLocalHomeomorphOn F S) (hi : InjOn F S) :
    ∃ e : OpenPartialHomeomorph X Y, e.source = S ∧ ∀ x, e x = F x := by
  have hl' : IsLocalHomeomorph (S.domRestrict F) := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    have hcomp := hl.comp (hS.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn)
      (show MapsTo (Subtype.val : S → X) univ S from fun x _ => x.2)
    exact hcomp
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv F S)
    hl.continuousOn hl'.isOpenMap hS, rfl, fun _ => rfl⟩

theorem inverseC1_of_chart {γ v : Circle → ℂ} (hg : CircleC1 γ) (hv : CircleC1 v)
    (a : ℝ) (e : OpenPartialHomeomorph (Circle × ℝ) ℂ)
    (hs : e.source = cylinder a) (he : ∀ p, e p = collarMap γ v p)
    (hd : ∀ c : Circle, ∀ r ∈ Ioo (-a) a,
      det (tangent γ c + r • tangent v c) (v c) ≠ 0) : InverseC1 e := by
  intro y hy
  have hp : e.symm y ∈ cylinder a := hs ▸ e.map_target hy
  obtain ⟨t, ht⟩ := Ch15.CircleLift.quotientMap_surjective (e.symm y).1
  let p : ℝ × ℝ := (t, (e.symm y).2)
  have hQp : quotientCylinder p = e.symm y := Prod.ext ht rfl
  have hp' : realCollar γ v p = y := by
    change collarMap γ v (quotientCylinder p) = y
    rw [hQp, ← he, e.right_inv hy]
  obtain ⟨g, hpg, hgq, hgs⟩ := realCollar_local_inverse hg hv p (by
    simpa only [p, realLift, ← tangent_coe, ht] using hd (e.symm y).1 (e.symm y).2 hp.2)
  have hgy : y ∈ g.target := by rw [← hp', ← hgq]; exact g.map_source hpg
  have hgp : g.symm y = p := by
    rw [← hp', ← hgq, g.left_inv hpg]
  refine ⟨g.symm, hp' ▸ hgs, ?_⟩
  have hcont : ContinuousAt (fun z => quotientCylinder (g.symm z)) y :=
    quotientCylinder_localHomeomorph.continuous.continuousAt.comp (g.continuousAt_symm hgy)
  have hQgy : quotientCylinder (g.symm y) = e.symm y := by rw [hgp, hQp]
  have hU : ∀ᶠ z in 𝓝 y, quotientCylinder (g.symm z) ∈ e.source :=
    hcont.eventually (by
      change e.source ∈ 𝓝 (quotientCylinder (g.symm y))
      rw [hQgy]
      exact e.open_source.mem_nhds (e.map_target hy))
  filter_upwards [hU, g.open_target.mem_nhds hgy, e.open_target.mem_nhds hy] with z hzU hzg hze
  apply e.injOn hzU (e.map_target hze)
  rw [he, e.right_inv hze]
  change realCollar γ v (g.symm z) = z
  rw [← hgq, g.right_inv hzg]

theorem sides_properties {γ v : Circle → ℂ} (hg : CircleC1 γ) (hv : CircleC1 v)
    {a : ℝ} (ha : 0 < a) (hi : InjOn (collarMap γ v) (cylinder a)) :
    Disjoint (positiveSide γ v a) (negativeSide γ v a) ∧
    IsPathConnected (positiveSide γ v a) ∧ IsPathConnected (negativeSide γ v a) ∧
    positiveSide γ v a ⊆ (range γ)ᶜ ∧ negativeSide γ v a ⊆ (range γ)ᶜ := by
  have hpos : univ ×ˢ Ioo 0 a ⊆ cylinder a := by
    rintro ⟨c,r⟩ ⟨_,hr⟩
    exact ⟨mem_univ _, lt_trans (neg_neg_of_pos ha) hr.1, hr.2⟩
  have hneg : univ ×ˢ Ioo (-a) 0 ⊆ cylinder a := by
    rintro ⟨c,r⟩ ⟨_,hr⟩
    exact ⟨mem_univ _, hr.1, lt_trans hr.2 ha⟩
  have hzero (c : Circle) : (c, (0 : ℝ)) ∈ cylinder a :=
    ⟨mem_univ _, neg_neg_of_pos ha, ha⟩
  have hcirc : IsPathConnected (univ : Set Circle) := by
    have hq : q '' (univ : Set ℝ) = univ :=
      image_univ.trans (range_eq_univ.mpr Ch15.CircleLift.quotientMap_surjective)
    rw [← hq]
    exact isPathConnected_univ.image (AddCircle.continuous_mk' (1 : ℝ))
  have hipos : IsPathConnected (Ioo (0 : ℝ) a) :=
    (convex_Ioo (0 : ℝ) a).isPathConnected ⟨a/2, by constructor <;> linarith⟩
  have hineg : IsPathConnected (Ioo (-a) (0 : ℝ)) :=
    (convex_Ioo (-a) (0 : ℝ)).isPathConnected ⟨-a/2, by constructor <;> linarith⟩
  refine ⟨?_, (hcirc.prod hipos).image (collarMap_continuous hg hv),
    (hcirc.prod hineg).image (collarMap_continuous hg hv), ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro z ⟨p,hp,hpz⟩ ⟨s,hs,hsz⟩
    have heq := hi (hpos hp) (hneg hs) (hpz.trans hsz.symm)
    have hr := congrArg Prod.snd heq
    linarith [hp.2.1, hs.2.2]
  · rintro z ⟨p,hp,rfl⟩ ⟨c,hc⟩
    have heq := hi (hpos hp) (hzero c) (by simpa [collarMap] using hc.symm)
    have hr := congrArg Prod.snd heq
    linarith [hp.2.1]
  · rintro z ⟨p,hp,rfl⟩ ⟨c,hc⟩
    have heq := hi (hneg hp) (hzero c) (by simpa [collarMap] using hc.symm)
    have hr := congrArg Prod.snd heq
    linarith [hp.2.2]

/-- A uniform embedded transverse C¹ collar for every regular C¹ embedded loop. -/
theorem collar_exists (γ : Circle → ℂ) (hγ : RegularEmbeddedLoop γ) :
    ∃ (v : Circle → ℂ) (a : ℝ), IsCollar γ v a := by
  obtain ⟨v, hv, ht⟩ := transverse_exists γ hγ
  obtain ⟨b, hb, hJ⟩ := uniform_positive_jacobian hγ.1 hv ht
  have hJne : ∀ c : Circle, ∀ r ∈ Ioo (-b) b,
      det (tangent γ c + r • tangent v c) (v c) ≠ 0 :=
    fun c r hr => ne_of_gt (hJ c r hr)
  have hl := collarMap_localHomeomorphOn hγ.1 hv b hJne
  have hloc : ∀ c : Circle, ∃ U ∈ 𝓝 (c, (0 : ℝ)), InjOn (collarMap γ v) U := by
    intro c
    obtain ⟨e, he, heq⟩ := hl (c, 0) ⟨mem_univ _, neg_neg_of_pos hb, hb⟩
    exact ⟨e.source, e.open_source.mem_nhds he, heq ▸ e.injOn⟩
  have hi₀ : Injective (fun c => collarMap γ v (c, 0)) := by
    simpa only [collarMap, zero_smul, add_zero] using hγ.2.1
  obtain ⟨a₀, ha₀, hi₀⟩ := uniform_injective_near_zero (collarMap γ v)
    (collarMap_continuous hγ.1 hv) hi₀ hloc
  let a : ℝ := min b a₀
  have ha : 0 < a := lt_min hb ha₀
  have hsub : cylinder a ⊆ cylinder b := by
    intro p hp
    exact ⟨hp.1, lt_of_le_of_lt (neg_le_neg (min_le_left b a₀)) hp.2.1,
      lt_of_lt_of_le hp.2.2 (min_le_left b a₀)⟩
  have hi : InjOn (collarMap γ v) (cylinder a) := hi₀.mono (by
    intro p hp
    exact ⟨hp.1, lt_of_le_of_lt (neg_le_neg (min_le_right b a₀)) hp.2.1,
      lt_of_lt_of_le hp.2.2 (min_le_right b a₀)⟩)
  have hJa : ∀ c : Circle, ∀ r ∈ Ioo (-a) a,
      det (tangent γ c + r • tangent v c) (v c) ≠ 0 :=
    fun c r hr => hJne c r (hsub (show (c, r) ∈ cylinder a from ⟨mem_univ c, hr⟩)).2
  obtain ⟨e, hs, he⟩ := open_chart_of_injOn (collarMap γ v) (cylinder a)
    (isOpen_univ.prod isOpen_Ioo) (hl.mono hsub) hi
  refine ⟨v, a, ha, hv, ht, e, hs, he, ?_, realCollar_contDiff hγ.1 hv,
    inverseC1_of_chart hγ.1 hv a e hs he hJa, sides_properties hγ.1 hv ha hi⟩
  rintro z ⟨c, rfl⟩
  have hc : (c, (0 : ℝ)) ∈ e.source := by rw [hs]; exact ⟨mem_univ _, neg_neg_of_pos ha, ha⟩
  simpa only [he, collarMap, zero_smul, add_zero] using e.map_source hc

end
end D13Unified.Ch21.Collar
