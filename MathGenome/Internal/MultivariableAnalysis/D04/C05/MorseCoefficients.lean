import MathGenome.Internal.MultivariableAnalysis.D04.C02.SegmentFTC
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.Integral
import MathGenome.Internal.MultivariableAnalysis.D04.C03.Symmetry
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.MorseCoefficients
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.ProjIcc
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Topology
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace D04
open SingleVariableAnalysis.Riemann
abbrev riemannValue := Specs.D04.C05.MorseCoefficients.Model.riemannValue
abbrev morseCoefficients := @Specs.D04.C05.MorseCoefficients.Model.morseCoefficients

/-- Continuous scalar interval functions have ordinary Riemann integrals. -/
theorem continuous_real_riemann_integrable (v : ℝ → ℝ)
    (hc : ContinuousOn v (Icc (0 : ℝ) 1)) : RealIntegrable v 0 1 := by
  apply real_continuous_integrable v (by norm_num)
  intro x hx
  exact (SingleVariableAnalysis.relativeContinuousAt_within_iff v (Icc (0 : ℝ) 1) x).mpr (hc x hx)

theorem riemannValue_eq {v : ℝ → ℝ} (hv : RealIntegrable v 0 1) :
    riemannValue v = realIntegral v hv := by
  simp [riemannValue, Specs.D04.C05.MorseCoefficients.Model.riemannValue, hv]

theorem riemannValue_congr {v w : ℝ → ℝ} (hv : RealIntegrable v 0 1)
    (hw : RealIntegrable w 0 1) (he : EqOn v w (Icc (0 : ℝ) 1)) :
    riemannValue v = riemannValue w := by
  rw [riemannValue_eq hv, riemannValue_eq hw]
  exact le_antisymm (realIntegral_mono _ _ hv hw (fun t ht => (he ht).le))
    (realIntegral_mono _ _ hw hv (fun t ht => (he ht).ge))

namespace MorseParameter
variable {X Y T : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace T] [CompactSpace T]

/-- Evaluation of a continuous family of operators, in the supremum norm. -/
def applyFamily (F : C(T, X →L[ℝ] Y)) : X →L[ℝ] C(T,Y) :=
  LinearMap.mkContinuous
    { toFun := fun v => (⟨fun t => F t v, by fun_prop⟩ : C(T,Y))
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    ‖F‖ (by
      intro v
      change ‖(⟨fun t => F t v, by fun_prop⟩ : C(T,Y))‖ ≤ ‖F‖ * ‖v‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg F) (norm_nonneg v))).mpr
      intro t
      exact (F t).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right
        (ContinuousMap.norm_coe_le_norm F t) (norm_nonneg v)))

/-- Reordering continuous and linear arguments is a bounded linear operation. -/
def flip : C(T, X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] C(T,Y)) :=
  LinearMap.mkContinuous
    { toFun := fun (F : C(T, X →L[ℝ] Y)) => applyFamily F
      map_add' := by intros; ext; simp [applyFamily]
      map_smul' := by intros; ext; simp [applyFamily] }
    1 (by
      intro F
      simp only [one_mul]
      change ‖applyFamily F‖ ≤ ‖F‖
      apply (applyFamily F).opNorm_le_bound (norm_nonneg F)
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro t
      exact (F t).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right
        (ContinuousMap.norm_coe_le_norm F t) (norm_nonneg v)))

@[simp] theorem flip_apply (F : C(T, X →L[ℝ] Y)) (v : X) (t : T) :
    flip F v t = F t v := rfl

/-- A continuous derivative on a compact parameter fiber gives a uniform
Fréchet remainder. No integral differentiation theorem is used. -/
theorem hasFDerivAt_curry (U : Set X) (hU : IsOpen U)
    (f : X → T → Y) (f' : X → T → X →L[ℝ] Y)
    (hc : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hc' : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hd : ∀ x ∈ U, ∀ t, HasFDerivAt (fun y => f y t) (f' x t) x)
    (x : X) (hx : x ∈ U) :
    HasFDerivAt (fun y => ContinuousMap.mkD (f y) 0)
      (flip (ContinuousMap.mkD (f' x) 0)) x := by
  have ht (y : X) (hy : y ∈ U) : Continuous (f y) :=
    hc.comp_continuous (Continuous.prodMk_right y) (fun _ => ⟨hy, trivial⟩)
  have ht' (y : X) (hy : y ∈ U) : Continuous (f' y) :=
    hc'.comp_continuous (Continuous.prodMk_right y) (fun _ => ⟨hy, trivial⟩)
  have hC := (ContinuousMap.continuousOn_mkD_of_uncurry f' 0 hc').continuousAt
    (hU.mem_nhds hx)
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hcpos
  obtain ⟨δ, hδ, hbound⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hx) (hC (Metric.ball_mem_nhds (ContinuousMap.mkD (f' x) 0) hcpos)))
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hyU := (hbound hy).1
  apply (ContinuousMap.norm_le _ (mul_nonneg hcpos.le (norm_nonneg _))).mpr
  intro t
  have hdiff (z : X) (hz : z ∈ Metric.ball x δ) : ‖f' z t - f' x t‖ ≤ c := by
    have hzU := (hbound hz).1
    have hn := (hbound hz).2
    change dist (ContinuousMap.mkD (f' z) 0) (ContinuousMap.mkD (f' x) 0) < c at hn
    rw [_root_.dist_eq_norm (ContinuousMap.mkD (f' z) 0) (ContinuousMap.mkD (f' x) 0)] at hn
    have he := ContinuousMap.norm_coe_le_norm
      (ContinuousMap.mkD (f' z) 0 - ContinuousMap.mkD (f' x) 0) t
    simpa only [ContinuousMap.sub_apply,
      ContinuousMap.mkD_apply_of_continuous (ht' z hzU),
      ContinuousMap.mkD_apply_of_continuous (ht' x hx)] using he.trans hn.le
  have he := (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hd z (hbound hz).1 t).hasFDerivWithinAt)
    hdiff (Metric.mem_ball_self hδ) hy
  simpa only [ContinuousMap.sub_apply, flip_apply,
    ContinuousMap.mkD_apply_of_continuous (ht y hyU),
    ContinuousMap.mkD_apply_of_continuous (ht x hx),
    ContinuousMap.mkD_apply_of_continuous (ht' x hx)] using he

/-- Repeated differentiation in the compact interval function space.  The
induction applies the uniform remainder lemma to each derivative field. -/
theorem contDiffOn_curry (r : ℕ) (W : Set (X × ℝ)) (hW : IsOpen W)
    (F : X × ℝ → Y) (hF : ContDiffOn ℝ r F W)
    (U : Set X) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (x,t) ∈ W) :
    ContDiffOn ℝ r
      (fun x => ContinuousMap.mkD (fun t : Icc (0 : ℝ) 1 => F (x,t)) 0) U := by
  have restrict_cont {Z : Type} [TopologicalSpace Z] (G : X × ℝ → Z)
      (hG : ContinuousOn G W) :
      ContinuousOn (fun p : X × Icc (0 : ℝ) 1 => G (p.1,p.2)) (U ×ˢ univ) :=
    hG.comp (by fun_prop) (fun p hp => hUW p.1 hp.1 p.2 p.2.property)
  induction r generalizing Y with
  | zero =>
    exact contDiffOn_zero.mpr (ContinuousMap.continuousOn_mkD_of_uncurry _ 0
      (restrict_cont F hF.continuousOn))
  | succ r ih =>
    have hF' := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := (r : ℕ∞ω)) (f := F) hW).mp (by simpa using hF)
    let D : X × ℝ → X →L[ℝ] Y := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ X ℝ)
    have hD : ContDiffOn ℝ r D W := hF'.2.2.clm_comp contDiffOn_const
    have hcD := ih D hD
    have hd (x : X) (hx : x ∈ U) (t : Icc (0 : ℝ) 1) :
        HasFDerivAt (fun y => F (y,t)) (D (x,t)) x := by
      have ha := (hF'.1 (x,t) (hUW x hx t t.property)).differentiableAt
        (hW.mem_nhds (hUW x hx t t.property))
      exact ha.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (t : ℝ) x))
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := (r : ℕ∞ω)) hU.uniqueDiffOn).mpr
    refine ⟨by simp, fun x => flip (ContinuousMap.mkD (fun t : Icc (0 : ℝ) 1 => D (x,t)) 0),
      ?_, ?_⟩
    · have hflip : ContDiff ℝ (r : ℕ∞ω)
          (flip (X := X) (Y := Y) (T := Icc (0 : ℝ) 1)) :=
        ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (r : ℕ∞ω)) (E := C(Icc (0 : ℝ) 1, X →L[ℝ] Y))
          (F := X →L[ℝ] C(Icc (0 : ℝ) 1,Y)) flip
      exact hflip.comp_contDiffOn hcD
    · intro x hx
      exact (hasFDerivAt_curry U hU (fun x (t : Icc (0 : ℝ) 1) => F (x,t))
        (fun x (t : Icc (0 : ℝ) 1) => D (x,t))
        (restrict_cont F hF.continuousOn) (restrict_cont D hD.continuousOn) hd x hx).hasFDerivWithinAt

/-- Continuous extension by clamping the interval argument. -/
def intervalExtend (F : C(Icc (0 : ℝ) 1, ℝ)) (t : ℝ) : ℝ :=
  F (projIcc 0 1 zero_le_one t)

theorem intervalExtend_continuous (F : C(Icc (0 : ℝ) 1, ℝ)) : Continuous (intervalExtend F) :=
  F.continuous.comp continuous_projIcc

theorem intervalExtend_integrable (F : C(Icc (0 : ℝ) 1, ℝ)) :
    RealIntegrable (intervalExtend F) 0 1 :=
  continuous_real_riemann_integrable _ (intervalExtend_continuous F).continuousOn

/-- The ordinary scalar Riemann integral is bounded linear for the supremum norm. -/
def integralCLM : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => riemannValue (intervalExtend F)
      map_add' := by
        intro F G
        obtain ⟨h, he⟩ := real_add_value (intervalExtend_integrable F) (intervalExtend_integrable G)
        change riemannValue (fun t => intervalExtend F t + intervalExtend G t) = _
        rw [riemannValue_eq h, riemannValue_eq (intervalExtend_integrable F),
          riemannValue_eq (intervalExtend_integrable G)]
        exact he
      map_smul' := by
        intro c F
        obtain ⟨h, he⟩ := real_mul_value (intervalExtend_integrable F) c
        change riemannValue (fun t => c * intervalExtend F t) = c * riemannValue (intervalExtend F)
        rw [riemannValue_eq h, riemannValue_eq (intervalExtend_integrable F)]
        exact he }
    1 (by
      intro F
      change ‖riemannValue (intervalExtend F)‖ ≤ 1 * ‖F‖
      rw [riemannValue_eq (intervalExtend_integrable F), one_mul]
      obtain ⟨hn, hnorm, _⟩ := real_norm_estimate (intervalExtend F) (intervalExtend_integrable F)
      apply hnorm.trans
      have hb := realIntegral_le_mul_bound hn
        (M := ‖F‖) (fun t _ => F.norm_coe_le_norm _)
      simpa using hb)

/-- Identifies the bounded linear functional with the original Darboux value. -/
theorem integralCLM_mkD (v : ℝ → ℝ) (hv : ContinuousOn v (Icc (0 : ℝ) 1)) :
    integralCLM (ContinuousMap.mkD (fun t : Icc (0 : ℝ) 1 => v t) 0) = riemannValue v := by
  apply riemannValue_congr (intervalExtend_integrable _) (continuous_real_riemann_integrable v hv)
  intro t ht
  simp only [intervalExtend, projIcc_of_mem zero_le_one ht]
  exact ContinuousMap.mkD_apply_of_continuous (show Continuous (fun t : Icc (0 : ℝ) 1 => v t) from hv.domRestrict)

/-- Parameter differentiation for the ordinary Riemann integral, assuming
only joint continuity of the integrand and its parameter derivative. -/
theorem riemann_hasFDerivAt (U : Set X) (hU : IsOpen U)
    (f : X → ℝ → ℝ) (f' : X → ℝ → X →L[ℝ] ℝ)
    (hc : ContinuousOn (Function.uncurry f) (U ×ˢ Icc (0 : ℝ) 1))
    (hc' : ContinuousOn (Function.uncurry f') (U ×ˢ Icc (0 : ℝ) 1))
    (hd : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt (fun y => f y t) (f' x t) x)
    (x : X) (hx : x ∈ U) :
    ∃ L : X →L[ℝ] ℝ, HasFDerivAt (fun y => riemannValue (f y)) L x ∧
      ∀ h, L h = riemannValue (fun t => f' x t h) := by
  have restrict_cont {Z : Type} [TopologicalSpace Z] (G : X → ℝ → Z)
      (hG : ContinuousOn (Function.uncurry G) (U ×ˢ Icc (0 : ℝ) 1)) :
      ContinuousOn (fun p : X × Icc (0 : ℝ) 1 => G p.1 p.2) (U ×ˢ univ) :=
    hG.comp (f := fun p : X × Icc (0 : ℝ) 1 => (p.1,(p.2 : ℝ)))
      (by fun_prop) (fun p hp => ⟨hp.1,p.2.property⟩)
  have ht (y : X) (hy : y ∈ U) : ContinuousOn (f y) (Icc (0 : ℝ) 1) :=
    hc.comp (f := fun t : ℝ => (y,t)) (by fun_prop) (fun t ht => ⟨hy,ht⟩)
  have ht' : ContinuousOn (f' x) (Icc (0 : ℝ) 1) :=
    hc'.comp (f := fun t : ℝ => (x,t)) (by fun_prop) (fun t ht => ⟨hx,ht⟩)
  let L := integralCLM.comp (flip (ContinuousMap.mkD (fun t : Icc (0 : ℝ) 1 => f' x t) 0))
  refine ⟨L, ?_, ?_⟩
  · have h := integralCLM.hasFDerivAt.comp x
      (hasFDerivAt_curry U hU (fun y (t : Icc (0 : ℝ) 1) => f y t)
        (fun y (t : Icc (0 : ℝ) 1) => f' y t)
        (restrict_cont f hc) (restrict_cont f' hc') (fun y hy t => hd y hy t t.property) x hx)
    apply h.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (integralCLM_mkD (f y) (ht y hy)).symm
  · intro h
    change integralCLM (flip (ContinuousMap.mkD (fun t : Icc (0 : ℝ) 1 => f' x t) 0) h) = _
    have he : flip (ContinuousMap.mkD (fun t : Icc (0 : ℝ) 1 => f' x t) 0) h =
        ContinuousMap.mkD (fun t : Icc (0 : ℝ) 1 => f' x t h) 0 := by
      ext t
      rw [flip_apply,
        ContinuousMap.mkD_of_continuous (show Continuous (fun t : Icc (0 : ℝ) 1 => f' x t) from ht'.domRestrict),
        ContinuousMap.mkD_of_continuous (show Continuous (fun t : Icc (0 : ℝ) 1 => f' x t h) from
          (ht'.clm_apply continuousOn_const).domRestrict)]
      rfl
    rw [he]
    exact integralCLM_mkD _ (ht'.clm_apply continuousOn_const)

/-- The same bounded Riemann functional preserves each finite derivative
order. Its proof differentiates in the compact function space, by induction. -/
theorem riemann_contDiffOn (r : ℕ) (W : Set (X × ℝ)) (hW : IsOpen W)
    (F : X × ℝ → ℝ) (hF : ContDiffOn ℝ r F W)
    (U : Set X) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (x,t) ∈ W) :
    ContDiffOn ℝ r (fun x => riemannValue (fun t => F (x,t))) U := by
  have h := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (r : ℕ∞ω)) integralCLM).comp_contDiffOn
    (contDiffOn_curry r W hW F hF U hU hUW)
  apply h.congr
  intro x hx
  apply (integralCLM_mkD _ ?_).symm
  exact hF.continuousOn.comp (by fun_prop) (fun t ht => hUW x hx t ht)

end MorseParameter
open private hessian_basis from MathGenome.Internal.MultivariableAnalysis.D04.C03.Symmetry

/-- Hessian entries lose precisely two derivatives on an open domain. -/
theorem morse_hessian_contDiffOn {n : ℕ} (r : ℕ) (U : Set (E n))
    (f : E n → ℝ) (hU : IsOpen U) (hf : CrOn (r+2) U f) (i j : Fin n) :
    ContDiffOn ℝ r (fun x => hessian f x i j) U := by
  have hc := (crOn_iff_contDiffOn (r+2) U f hU).mp hf
  have hc2 : CrOn 2 U f := (crOn_iff_contDiffOn 2 U f hU).mpr (hc.of_le (by norm_cast; omega))
  have hT : ContDiffOn ℝ r (higherDifferential 2 f) U := by
    intro x hx
    exact ((hc.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right
      (i := 2) (m := (r : ℕ∞ω)) (by norm_cast)).contDiffWithinAt
  have h := hT.continuousLinearMap_comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E n) ℝ
      ![standardBasis n i, standardBasis n j])
  exact h.congr (fun x hx => (hessian_basis U f x
    (crOn_timesDifferentiableAt 2 U f hU hc2 x hx) i j).symm)

/-- The weighted Hessian integrand is jointly C^r wherever tx is in U. -/
theorem morse_integrand_contDiffOn {n : ℕ} (r : ℕ) (U : Set (E n))
    (f : E n → ℝ) (hU : IsOpen U) (hf : CrOn (r+2) U f) (i j : Fin n) :
    ContDiffOn ℝ r (fun p : E n × ℝ => (1-p.2) * hessian f (p.2 • p.1) i j)
      {p : E n × ℝ | p.2 • p.1 ∈ U} := by
  have hH := morse_hessian_contDiffOn r U f hU hf i j
  exact (contDiffOn_const.sub contDiffOn_snd).mul
    (hH.comp (contDiff_snd.smul contDiff_fst).contDiffOn (fun _ hp => hp))

/-- Radial segments in a ball remain in that same ball. -/
theorem morse_radial_ball {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {x : E n} (hx : x ∈ Metric.ball 0 ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • x ∈ Metric.ball 0 ρ :=
  (convex_ball (0 : E n) ρ).smul_mem_of_zero_mem (by simpa using hρ) hx ht

/-- Regularity of the actual Riemann coefficients, on every admissible ball. -/
theorem morseCoefficients_crOn {n : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn (r+2) U f) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : Metric.ball (0 : E n) ρ ⊆ U) (i j : Fin n) :
    CrOn r (Metric.ball 0 ρ) (fun x => morseCoefficients f x i j) := by
  apply (crOn_iff_contDiffOn r _ _ Metric.isOpen_ball).mpr
  exact MorseParameter.riemann_contDiffOn r _ (hU.preimage (by fun_prop)) _
    (morse_integrand_contDiffOn r U f hU hf i j) _ Metric.isOpen_ball
    (fun x hx t ht => hball (morse_radial_ball hρ hx ht))

/-- Every defining scalar integrand is continuous and Riemann integrable. -/
theorem morseCoefficients_integrable {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 2 U f) (x : E n)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) (i j : Fin n) :
    RealIntegrable (fun t : ℝ => (1-t) * hessian f (t • x) i j) 0 1 := by
  apply continuous_real_riemann_integrable
  have hH := (morse_hessian_contDiffOn 0 U f hU hf i j).continuousOn
  exact (continuous_const.sub continuous_id).continuousOn.mul
    (hH.comp (by fun_prop) hseg)

/-- Symmetry is inherited pointwise under the scalar integral. -/
theorem morseCoefficients_symmetric {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 2 U f) (x : E n)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) : (morseCoefficients f x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  apply riemannValue_congr (morseCoefficients_integrable U f hU hf x hseg j i)
    (morseCoefficients_integrable U f hU hf x hseg i j)
  intro t ht
  have hs := hessian_symmetric U f (t • x)
    (crOn_timesDifferentiableAt 2 U f hU hf _ (hseg t ht))
  exact congrArg ((1-t) * ·) (hs.apply i j)

/-- Integration of the constant Hessian at the origin gives exactly one half. -/
theorem morseCoefficients_zero {n : ℕ} (f : E n → ℝ) :
    morseCoefficients f 0 = (1/2 : ℝ) • hessian f 0 := by
  ext i j
  let c := hessian f 0 i j
  have hi : RealIntegrable (fun t : ℝ => (1-t)*c) 0 1 :=
    continuous_real_riemann_integrable _ (by fun_prop)
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => c * (s-s^2/2)) ((1-t)*c) t := by
    convert ((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div_const 2)).const_mul c using 1 <;> simp [id_eq, mul_comm]
  have he := real_ftc_second (fun t : ℝ => c * (t-t^2/2)) (fun t => (1-t)*c)
    0 1 (by norm_num) (by fun_prop) (fun t _ => hd t) hi
  change riemannValue (fun t => (1-t) * hessian f (t • (0 : E n)) i j) = (1/2 : ℝ) * c
  simp only [smul_zero]
  rw [riemannValue_eq hi]
  calc
    _ = c * (1-1^2/2) - c * (0-0^2/2) := he
    _ = _ := by ring

/-- Scalar order-two Taylor on a radial segment, with ordinary Riemann remainder. -/
theorem morse_taylor_two {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 2 U f) (x : E n)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) :
    f x - (f 0 + totalDerivative f 0 x) =
      riemannValue (fun t => (1-t) * differentialDiagonal (higherDifferential 2 f (t • x)) x) := by
  have hc := (crOn_iff_contDiffOn 2 U f hU).mp hf
  let D : ℕ → ℝ → ℝ := fun j t => differentialDiagonal (higherDifferential j f (t • x)) x
  have hD : SingleVariableAnalysis.ClosedDerivativeFamily 2 (fun t : ℝ => f (t • x)) 0 1 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro t _; rfl
    · intro j hj t ht
      have hT : ContinuousAt (iteratedFDeriv ℝ j f) (t • x) :=
        ((hc.contDiffAt (hU.mem_nhds (hseg t ht))).iteratedFDeriv_right
          (i := j) (m := 0) (by norm_cast; simpa using hj)).continuousAt
      exact ((hT.comp (x := t) (by fun_prop)).eval_const (fun _ => x)).continuousWithinAt
    · intro j hj t ht
      have hT : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) (t • x) :=
        (hc.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt_iteratedFDeriv (by exact_mod_cast hj)
      have hl : HasDerivAt (fun s : ℝ => s • x) x t := by simpa using (hasDerivAt_id t).smul_const x
      have hh := (hT.hasFDerivAt.continuousMultilinear_apply_const (fun _ => x)).comp_hasDerivAt t hl
      exact hh.hasDerivWithinAt
  obtain ⟨hi, he⟩ := real_integral_remainder (fun t : ℝ => f (t • x)) 1 0 1 D hD
    0 (by constructor <;> norm_num) 1 (by constructor <;> norm_num)
  have hi' : RealIntegrable (fun t => (1-t) * differentialDiagonal (higherDifferential 2 f (t • x)) x) 0 1 := by
    simpa [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue, D] using hi
  rw [riemannValue_eq hi']
  change f x - (f 0 + fderiv ℝ f 0 x) = _
  simpa [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegralValue, D,
    Finset.sum_range_succ, differentialDiagonal, Specs.D04.C03.HigherInterfaces.Model.differentialDiagonal,
    higherDifferential, Specs.D04.C03.HigherInterfaces.Model.higherDifferential,
    iteratedFDeriv_one_apply] using he

theorem riemannValue_mul {v : ℝ → ℝ} (hv : RealIntegrable v 0 1) (c : ℝ) :
    riemannValue (fun t => c * v t) = c * riemannValue v := by
  obtain ⟨h, he⟩ := real_mul_value hv c
  rw [riemannValue_eq h, riemannValue_eq hv]
  exact he

/-- Finite sums commute with the proper Riemann integral. -/
theorem riemannValue_sum {ι : Type} (s : Finset ι) (v : ι → ℝ → ℝ)
    (hv : ∀ i ∈ s, RealIntegrable (v i) 0 1) :
    RealIntegrable (fun t => ∑ i ∈ s, v i t) 0 1 ∧
      riemannValue (fun t => ∑ i ∈ s, v i t) = ∑ i ∈ s, riemannValue (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h, he⟩ := real_zero_value (show (0 : ℝ) ≤ 1 by norm_num)
    refine ⟨by simpa using h, ?_⟩
    simpa only [Finset.sum_empty, riemannValue_eq h] using he
  | @insert i s hi ih =>
    obtain ⟨hs, he⟩ := ih (fun j hj => hv j (Finset.mem_insert_of_mem hj))
    obtain ⟨ha, hea⟩ := real_add_value (hv i (Finset.mem_insert_self i s)) hs
    refine ⟨by simpa only [Finset.sum_insert hi] using ha, ?_⟩
    simp only [Finset.sum_insert hi]
    rw [← riemannValue_eq ha, ← riemannValue_eq (hv i (Finset.mem_insert_self i s)),
      ← riemannValue_eq hs, he] at hea
    exact hea

/-- The coefficient matrix is the exact quadratic representation, without
any nondegeneracy hypothesis on the Hessian. -/
theorem morseCoefficients_identity {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 2 U f) (hcrit : totalDerivative f 0 = 0)
    (x : E n) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) :
    f x - f 0 = ∑ i : Fin n, ∑ j : Fin n, morseCoefficients f x i j * x i * x j := by
  classical
  let v : Fin n → Fin n → ℝ → ℝ := fun i j t =>
    (x i * x j) * ((1-t) * hessian f (t • x) i j)
  have hv (i j : Fin n) : RealIntegrable (v i j) 0 1 :=
    (real_mul_value (morseCoefficients_integrable U f hU hf x hseg i j) (x i * x j)).choose
  have hs (i : Fin n) := riemannValue_sum Finset.univ (v i) (fun j _ => hv i j)
  have hall := riemannValue_sum Finset.univ (fun i t => ∑ j, v i j t) (fun i _ => (hs i).1)
  have htay := morse_taylor_two U f hU hf x hseg
  rw [hcrit] at htay
  simp only [zero_apply, add_zero] at htay
  rw [htay]
  have hdiag : ContinuousOn
      (fun t : ℝ => (1-t) * differentialDiagonal (higherDifferential 2 f (t • x)) x) (Icc 0 1) := by
    intro t ht
    have hT := ((crOn_iff_contDiffOn 2 U f hU).mp hf).contDiffAt (hU.mem_nhds (hseg t ht))
    have hcont := (hT.iteratedFDeriv_right (i := 2) (m := 0) (by norm_num)).continuousAt
    exact ((continuous_const.sub continuous_id).continuousAt.mul
      ((hcont.comp (x := t) (by fun_prop)).eval_const (fun _ => x))).continuousWithinAt
  have hsum := riemannValue_congr (continuous_real_riemann_integrable _ hdiag) hall.1
    (fun t ht => by
      rw [higherDifferential_diagonal_hessian U f (t • x)
        (crOn_timesDifferentiableAt 2 U f hU hf _ (hseg t ht)) x]
      simp only [dotProduct, Matrix.mulVec, coordinates_apply, v, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring)
  rw [hsum, hall.2]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hs i).2]
  apply Finset.sum_congr rfl
  intro j _
  rw [show riemannValue (v i j) = (x i * x j) * morseCoefficients f x i j from
    riemannValue_mul (morseCoefficients_integrable U f hU hf x hseg i j) (x i * x j)]
  ring

/-- The entire coefficient matrix has the asserted finite regularity. -/
theorem morseCoefficients_matrix_crOn {n : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn (r+2) U f) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : Metric.ball (0 : E n) ρ ⊆ U) :
    CrOn r (Metric.ball 0 ρ) (morseCoefficients f) := by
  apply (crOn_iff_contDiffOn r _ _ Metric.isOpen_ball).mpr
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact (crOn_iff_contDiffOn r _ _ Metric.isOpen_ball).mp
    (morseCoefficients_crOn r U f hU hf ρ hρ hball i j)

/-- For smooth data every finite step applies to this same coefficient map. -/
theorem morseCoefficients_smoothOn {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : SmoothOn U f) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : Metric.ball (0 : E n) ρ ⊆ U) :
    SmoothOn (Metric.ball 0 ρ) (morseCoefficients f) := by
  intro r
  exact morseCoefficients_matrix_crOn r U f hU (hf (r+2)) ρ hρ hball

/-- The empty-dimensional quadratic identity has no extra hypothesis. -/
theorem morseCoefficients_dimension_zero (f : E 0 → ℝ) (x : E 0) :
    f x - f 0 = ∑ i : Fin 0, ∑ j : Fin 0, morseCoefficients f x i j * x i * x j := by
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

/-- Coefficient-integral stage of the bounded Morse lemma, with an admissible
closed ball, exact identity, symmetry, normalization, and finite regularity. -/
theorem morse_coefficients {n : ℕ} (r : ℕ) (_hr : 1 ≤ r) (U : Set (E n))
    (f : E n → ℝ) (hU : IsOpen U) (h0 : (0 : E n) ∈ U) (hf : CrOn (r+2) U f)
    (hcrit : totalDerivative f 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (0 : E n) ρ ⊆ U ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, ∀ i j : Fin n,
        RealIntegrable (fun t : ℝ => (1-t) * hessian f (t • x) i j) 0 1) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ,
        f x - f 0 = ∑ i : Fin n, ∑ j : Fin n, morseCoefficients f x i j * x i * x j) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, (morseCoefficients f x).IsSymm) ∧
      morseCoefficients f 0 = (1/2 : ℝ) • hessian f 0 ∧
      CrOn r (Metric.ball 0 ρ) (morseCoefficients f) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h0)
  have hseg (x : E n) (hx : x ∈ Metric.closedBall (0 : E n) ρ)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • x ∈ U :=
    hball ((convex_closedBall (0 : E n) ρ).smul_mem_of_zero_mem
      (by simpa using hρ.le) hx ht)
  have hf2 : CrOn 2 U f := (crOn_iff_contDiffOn 2 U f hU).mpr
    (((crOn_iff_contDiffOn (r+2) U f hU).mp hf).of_le (by norm_cast; omega))
  exact ⟨ρ, hρ, hball, hseg,
    fun x hx i j => morseCoefficients_integrable U f hU hf2 x (hseg x hx) i j,
    fun x hx => morseCoefficients_identity U f hU hf2 hcrit x (hseg x hx),
    fun x hx => morseCoefficients_symmetric U f hU hf2 x (hseg x hx),
    morseCoefficients_zero f,
    morseCoefficients_matrix_crOn r U f hU hf ρ hρ (fun x hx => hball (Metric.ball_subset_closedBall hx))⟩

/-- Smooth specialization on one fixed neighborhood, for the identical
integral coefficient map at every derivative order. -/
theorem morse_coefficients_smooth {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (h0 : (0 : E n) ∈ U) (hf : SmoothOn U f)
    (hcrit : totalDerivative f 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (0 : E n) ρ ⊆ U ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, ∀ i j : Fin n,
        RealIntegrable (fun t : ℝ => (1-t) * hessian f (t • x) i j) 0 1) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ,
        f x - f 0 = ∑ i : Fin n, ∑ j : Fin n, morseCoefficients f x i j * x i * x j) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, (morseCoefficients f x).IsSymm) ∧
      morseCoefficients f 0 = (1/2 : ℝ) • hessian f 0 ∧
      SmoothOn (Metric.ball 0 ρ) (morseCoefficients f) := by
  obtain ⟨ρ, hρ, hball, hseg, hi, he, hs, hz, _⟩ :=
    morse_coefficients 1 le_rfl U f hU h0 (hf 3) hcrit
  exact ⟨ρ, hρ, hball, hseg, hi, he, hs, hz,
    morseCoefficients_smoothOn U f hU hf ρ hρ
      (fun x hx => hball (Metric.ball_subset_closedBall hx))⟩

end D04
