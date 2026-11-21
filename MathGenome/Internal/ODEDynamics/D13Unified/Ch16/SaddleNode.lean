import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.SaddleNode
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.SimplePersistence
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace D13Unified.Ch16.SaddleNode
open D13Unified.Ch16.SimplePersistence

private lemma scalar_linear_apply (L : ℝ →L[ℝ] ℝ) (x : ℝ) :
    L x = x * L 1 := by
  simpa using L.map_smul x (1 : ℝ)

private lemma scalar_linear_invertible (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) :
    L.IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · ext
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [scalar_linear_apply]
    field_simp
  · ext
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [scalar_linear_apply]
    field_simp

/-- The parameter may be solved as a C³ graph over the state. The box is fixed
and lies in the original open domain. This uses the implicit function theorem
in the parameter direction, rather than presuming the fold's coordinate. -/
theorem parameter_graph
    (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hmem : (0, 0) ∈ U) (hf : ContDiffOn ℝ 3 f U)
    (hzero : f (0, 0) = 0) (hparam : parameterDerivative f (0, 0) ≠ 0) :
    ∃ ψ : ℝ → ℝ, ∃ r s : ℝ,
      0 < r ∧ 0 < s ∧ ψ 0 = 0 ∧
      ContDiffOn ℝ 3 ψ (Metric.ball 0 r) ∧
      Metric.ball 0 s ×ˢ Metric.ball 0 r ⊆ U ∧
      (∀ x ∈ Metric.ball 0 r, ψ x ∈ Metric.ball 0 s) ∧
      (∀ μ ∈ Metric.ball 0 s, ∀ x ∈ Metric.ball 0 r,
        f (μ, x) = 0 ↔ μ = ψ x) := by
  let g : ℝ × ℝ → ℝ := fun z => f z.swap
  have hfat : ContDiffAt ℝ 3 f (0, 0) := hf.contDiffAt (hU.mem_nhds hmem)
  have hgat : ContDiffAt ℝ 3 g (0, 0) :=
    hfat.comp (0, 0) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hswap : HasFDerivAt (fun z : ℝ × ℝ => z.swap)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ))
      (0, 0) := hasFDerivAt_snd.prodMk hasFDerivAt_fst
  have hgderiv := (hfat.differentiableAt (by norm_num)).hasFDerivAt.comp (0, 0) hswap
  have hgderiv' : HasFDerivAt g
      (fderiv ℝ f (0, 0) ∘L
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)))
      (0, 0) := hgderiv
  have hginv : (fderiv ℝ g (0, 0) ∘L .inr ℝ ℝ ℝ).IsInvertible := by
    apply scalar_linear_invertible
    change fderiv ℝ g (0, 0) (0, 1) ≠ 0
    rw [hgderiv'.fderiv]
    exact hparam
  let ψ := hgat.implicitFunction (by norm_num) hginv
  have hψzero : ψ 0 = 0 := hgat.implicitFunction_apply_self (by norm_num) hginv
  have hψsmooth : ContDiffAt ℝ 3 ψ 0 :=
    hgat.contDiffAt_implicitFunction (by norm_num) hginv
  have heq : ∀ᶠ z : ℝ × ℝ in 𝓝 (0, 0), g z = 0 ↔ ψ z.1 = z.2 := by
    simpa only [g, Prod.swap_prod_mk, hzero] using
      hgat.eventually_apply_eq_iff_implicitFunction (by norm_num) hginv
  obtain ⟨r₀, hr₀, hbox⟩ := Metric.eventually_nhds_iff.mp
    (heq.and ((hU.preimage continuous_swap).mem_nhds (by simpa using hmem)))
  have hψnear : ∀ᶠ x in 𝓝 (0 : ℝ), ψ x ∈ Metric.ball 0 r₀ := by
    apply hψsmooth.continuousAt.preimage_mem_nhds
    simpa [hψzero] using (Metric.ball_mem_nhds (0 : ℝ) hr₀)
  have hsmooth : ∀ᶠ x in 𝓝 (0 : ℝ), ContDiffAt ℝ 3 ψ x :=
    hψsmooth.eventually (by norm_num)
  obtain ⟨r, hr, hsmall⟩ := Metric.eventually_nhds_iff.mp
    ((hψnear.and hsmooth).and (Metric.ball_mem_nhds (0 : ℝ) hr₀))
  refine ⟨ψ, r, r₀, hr, hr₀, hψzero, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hsmall hx).1.2.contDiffWithinAt
  · rintro ⟨μ, x⟩ ⟨hμ, hx⟩
    have hz : dist (x, μ) (0, 0) < r₀ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨(hsmall hx).2, hμ⟩
    exact (hbox hz).2
  · intro x hx
    exact (hsmall hx).1.1
  · intro μ hμ x hx
    have hz : dist (x, μ) (0, 0) < r₀ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨(hsmall hx).2, hμ⟩
    exact (hbox hz).1.trans eq_comm

private lemma pair_linear_apply (L : ℝ × ℝ →L[ℝ] ℝ) (u v : ℝ) :
    L (u, v) = L (1, 0) * u + L (0, 1) * v := by
  have huv : (u, v) = u • (1, 0) + v • (0, 1) := by ext <;> simp
  rw [huv, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring_nf

/-- Differentiating the zero graph once gives the exact identity along it. -/
theorem parameter_graph_derivative
    {f : ℝ × ℝ → ℝ} {ψ : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f (ψ x, x)) (hψ : DifferentiableAt ℝ ψ x)
    (heq : ∀ᶠ t in 𝓝 x, f (ψ t, t) = 0) :
    parameterDerivative f (ψ x, x) * deriv ψ x + stateDerivative f (ψ x, x) = 0 := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt (f := fun t => (ψ t, t)) x
    (hψ.hasDerivAt.prodMk (hasDerivAt_id x))
  have hz : HasDerivAt (fun t => f (ψ t, t)) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  have h := hd.unique hz
  rw [pair_linear_apply] at h
  simpa only [mul_one, parameterDerivative, stateDerivative,
    Specs.D13Unified.Ch16.SimplePersistence.stateDerivative] using h

/-- The first two jets of the implicit parameter graph, including the factor
of two in the normalized coefficient. No Hessian is replaced by a formal symbol. -/
theorem parameter_graph_jets
    {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {ψ : ℝ → ℝ}
    (hU : IsOpen U) (hmem : (0, 0) ∈ U) (hf : ContDiffOn ℝ 3 f U)
    (hψ : ContDiffAt ℝ 3 ψ 0) (hψzero : ψ 0 = 0)
    (heq : ∀ᶠ x in 𝓝 (0 : ℝ), f (ψ x, x) = 0)
    (hstate : stateDerivative f (0, 0) = 0)
    (hparam : parameterDerivative f (0, 0) ≠ 0) :
    HasDerivAt ψ 0 0 ∧ HasDerivAt (deriv ψ) (2 * coefficient f) 0 := by
  have hfat := hf.contDiffAt (hU.mem_nhds hmem)
  have hψdiff := hψ.differentiableAt (by norm_num)
  have hfirst := parameter_graph_derivative
    (by simpa [hψzero] using hfat.differentiableAt (by norm_num)) hψdiff heq
  have hdψ : deriv ψ 0 = 0 := by
    rw [hψzero, hstate, add_zero, mul_eq_zero] at hfirst
    exact hfirst.resolve_left hparam
  have hderiv : HasDerivAt ψ 0 0 := by simpa [hdψ] using hψdiff.hasDerivAt
  refine ⟨hderiv, ?_⟩
  have hp : ContDiffAt ℝ 2 (parameterDerivative f) (0, 0) :=
    ((hf.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const).contDiffAt
      (hU.mem_nhds hmem)
  have hs : ContDiffAt ℝ 2 (stateDerivative f) (0, 0) :=
    ((hf.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const).contDiffAt
      (hU.mem_nhds hmem)
  have hg : HasDerivAt (fun x => (ψ x, x)) (0, 1) 0 :=
    hderiv.prodMk (hasDerivAt_id 0)
  have hpat : DifferentiableAt ℝ (parameterDerivative f) (ψ 0, 0) :=
    by simpa [hψzero] using hp.differentiableAt (by norm_num)
  have hpd : DifferentiableAt ℝ (fun x => parameterDerivative f (ψ x, x)) 0 :=
    hpat.comp (f := fun x => (ψ x, x)) 0 hg.differentiableAt
  have hsd : HasDerivAt (fun x => stateDerivative f (ψ x, x))
      (stateSecondDerivative f (0, 0)) 0 := by
    simpa only [hψzero, stateSecondDerivative, Function.comp_def] using
      (show DifferentiableAt ℝ (stateDerivative f) (ψ 0, 0) from
        by simpa [hψzero] using hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt (f := fun t => (ψ t, t)) 0 hg
  have hdderiv : DifferentiableAt ℝ (deriv ψ) 0 :=
    (hψ.derivWithin (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hid : ∀ᶠ x in 𝓝 (0 : ℝ),
      parameterDerivative f (ψ x, x) * deriv ψ x + stateDerivative f (ψ x, x) = 0 := by
    have hdiff : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (ψ x, x) := by
      have hnear : ∀ᶠ z in 𝓝 (0, 0), DifferentiableAt ℝ f z :=
        (hfat.eventually (by norm_num)).mono fun _ hz => hz.differentiableAt (by norm_num)
      have hgt : Tendsto (fun x => (ψ x, x)) (𝓝 0) (𝓝 (0, 0)) :=
        by simpa [hψzero] using hg.continuousAt.tendsto
      exact hgt.eventually hnear
    filter_upwards [hdiff, hψ.eventually (by norm_num), heq.eventually_nhds] with x hx hψx heqx
    exact parameter_graph_derivative hx (hψx.differentiableAt (by norm_num)) heqx
  have hsum := (hpd.hasDerivAt.mul hdderiv.hasDerivAt).add hsd
  have hz : HasDerivAt
      (fun x => parameterDerivative f (ψ x, x) * deriv ψ x + stateDerivative f (ψ x, x))
      0 0 := (hasDerivAt_const 0 (0 : ℝ)).congr_of_eventuallyEq hid
  have hrel := hsum.unique hz
  simp only [hψzero, hdψ, mul_zero, zero_add] at hrel
  have hval : deriv (deriv ψ) 0 = 2 * coefficient f := by
    unfold coefficient
    field_simp [hparam]
    nlinarith [hrel]
  exact hdderiv.hasDerivAt.congr_deriv hval

/-- The normalized quadratic quotient extends continuously with value one.
The proof only needs two derivatives; it does not assume a smooth quotient. -/
theorem quadratic_quotient_limit
    {ψ : ℝ → ℝ} {a : ℝ} (hψ : ContDiffAt ℝ 2 ψ 0)
    (hzero : ψ 0 = 0) (hd : HasDerivAt ψ 0 0)
    (hdd : HasDerivAt (deriv ψ) (2 * a) 0) :
    Tendsto (fun x => ψ x / x ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
  have hdlim : Tendsto (fun x => deriv ψ x / x) (𝓝[≠] (0 : ℝ)) (𝓝 (2 * a)) := by
    simpa only [slope_fun_def_field, hd.deriv, sub_zero] using hdd.tendsto_slope
  have hratio : Tendsto (fun x => deriv ψ x / (2 * x))
      (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
    convert hdlim.div_const 2 using 1
    · ext x
      simp [div_eq_mul_inv, mul_comm, mul_assoc]
    · ring_nf
  have hdiff : ∀ᶠ x in 𝓝[≠] (0 : ℝ), HasDerivAt ψ (deriv ψ x) x :=
    ((hψ.eventually (by norm_num)).mono fun x hx =>
      (hx.differentiableAt (by norm_num)).hasDerivAt).filter_mono nhdsWithin_le_nhds
  apply HasDerivAt.lhopital_zero_nhdsNE hdiff
    (Eventually.of_forall fun x => (hasDerivAt_id x).pow 2) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  · simpa only [hzero] using hψ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · simpa using (continuousAt_id.pow 2).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  · simpa using hratio

/-- A one-dimensional Morse coordinate with derivative normalized to one.
The continuous quadratic quotient is sufficient: differentiating away from
zero and taking limits proves C¹ regularity at zero. -/
theorem quadratic_coordinate_function
    {ψ : ℝ → ℝ} {a : ℝ} (ha : a ≠ 0) (hψ : ContDiffAt ℝ 2 ψ 0)
    (hzero : ψ 0 = 0) (hd : HasDerivAt ψ 0 0)
    (hdd : HasDerivAt (deriv ψ) (2 * a) 0) :
    ∃ y : ℝ → ℝ, ∃ r : ℝ, 0 < r ∧ y 0 = 0 ∧
      HasDerivAt y 1 0 ∧ ContDiffOn ℝ 1 y (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball 0 r, ψ x = a * y x ^ 2) ∧
      (∀ x ∈ Metric.ball 0 r, (0 < y x ↔ 0 < x) ∧ (y x < 0 ↔ x < 0)) := by
  classical
  let k : ℝ → ℝ := Function.update (fun x => ψ x / (a * x ^ 2)) 0 1
  have hkzero : k 0 = 1 := by simp [k]
  have hkval (x : ℝ) (hx : x ≠ 0) : k x = ψ x / (a * x ^ 2) := by
    simp [k, hx]
  have hklim : Tendsto (fun x => ψ x / (a * x ^ 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    convert (quadratic_quotient_limit hψ hzero hd hdd).div_const a using 1
    · ext x
      simp only [div_div, mul_comm]
    · field_simp
  have hkcont : ContinuousAt k 0 := continuousAt_update_same.mpr hklim
  let y : ℝ → ℝ := fun x => x * Real.sqrt (k x)
  have hyzero : y 0 = 0 := by simp [y]
  have hyderiv : HasDerivAt y 1 0 := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have hsqrt : Tendsto (fun x => Real.sqrt (k x)) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      simpa only [hkzero, Real.sqrt_one] using hkcont.sqrt.tendsto.mono_left nhdsWithin_le_nhds
    apply hsqrt.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : x ≠ 0 := hx
    simp only [slope_fun_def_field, hyzero, sub_zero, y]
    field_simp
  have hnear : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < k x ∧ ContDiffAt ℝ 2 ψ x := by
    have hkp : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < k x :=
      hkcont.preimage_mem_nhds (Ioi_mem_nhds (by simp [hkzero]))
    exact hkp.and (hψ.eventually (by norm_num))
  obtain ⟨r, hr, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  have hpos (x : ℝ) (hx : x ∈ Metric.ball 0 r) : 0 < k x := (hsmall hx).1
  have hidentity (x : ℝ) (hx : x ∈ Metric.ball 0 r) : ψ x = a * y x ^ 2 := by
    by_cases hxzero : x = 0
    · simp [hxzero, hzero, hyzero]
    · rw [show y x = x * Real.sqrt (k x) from rfl, mul_pow,
        Real.sq_sqrt (hpos x hx).le, hkval x hxzero]
      field_simp
  have hsmooth (x : ℝ) (hx : x ∈ Metric.ball 0 r) (hne : x ≠ 0) :
      ContDiffAt ℝ 1 y x := by
    have hkx : ContDiffAt ℝ 1 k x := by
      have hbase : ContDiffAt ℝ 1 (fun t => ψ t / (a * t ^ 2)) x :=
        ((hsmall hx).2.of_le (by norm_num)).div
          (contDiffAt_const.mul (contDiffAt_id.pow 2)) (mul_ne_zero ha (pow_ne_zero _ hne))
      apply hbase.congr_of_eventuallyEq
      filter_upwards [isOpen_ne.mem_nhds hne] with t ht
      exact hkval t ht
    exact contDiffAt_id.mul (hkx.sqrt (hpos x hx).ne')
  have hdiff (x : ℝ) (hx : x ∈ Metric.ball 0 r) : DifferentiableAt ℝ y x := by
    by_cases hne : x = 0
    · simpa [hne] using hyderiv.differentiableAt
    · exact (hsmooth x hx hne).differentiableAt (by norm_num)
  have hformula (x : ℝ) (hx : x ∈ Metric.ball 0 r) (hne : x ≠ 0) :
      deriv y x = deriv ψ x / (2 * a * y x) := by
    have hyeq : y x ≠ 0 := mul_ne_zero hne (Real.sqrt_pos.mpr (hpos x hx)).ne'
    have hlocal : (fun t => ψ t) =ᶠ[𝓝 x] (fun t => a * y t ^ 2) :=
      (Metric.isOpen_ball.eventually_mem hx).mono fun t ht => hidentity t ht
    have ht := (((hdiff x hx).hasDerivAt.pow 2).const_mul a).congr_of_eventuallyEq hlocal
    have hrel := ht.deriv
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hrel
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) ha) hyeq)).mpr
    nlinarith [hrel]
  have hyprimecont : ContinuousAt (deriv y) 0 := by
    rw [continuousAt_iff_punctured_nhds]
    have hdlim : Tendsto (fun x => deriv ψ x / x)
        (𝓝[≠] (0 : ℝ)) (𝓝 (2 * a)) := by
      simpa only [slope_fun_def_field, hd.deriv, sub_zero] using hdd.tendsto_slope
    have hylim : Tendsto (fun x => y x / x)
        (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      simpa only [slope_fun_def_field, hyzero, sub_zero] using hyderiv.tendsto_slope
    have hlim := hdlim.div ((tendsto_const_nhds.mul hylim).const_mul (2 : ℝ))
      (show 2 * (a * 1) ≠ 0 by simpa using ha)
    have hlim' : Tendsto (fun x => (deriv ψ x / x) / (2 * (a * (y x / x))))
        (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      convert hlim using 1
      field_simp
    rw [hyderiv.deriv]
    apply hlim'.congr'
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds (0 : ℝ) hr),
      self_mem_nhdsWithin] with x hx hne
    rw [hformula x hx hne]
    field_simp [show x ≠ 0 from hne]
  have hyC1 : ContDiffOn ℝ 1 y (Metric.ball 0 r) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 by rfl,
      contDiffOn_succ_iff_deriv_of_isOpen Metric.isOpen_ball]
    refine ⟨fun x hx => (hdiff x hx).differentiableWithinAt, ?_, ?_⟩
    · norm_num
    · rw [contDiffOn_zero]
      intro x hx
      by_cases hne : x = 0
      · simpa [hne] using hyprimecont.continuousWithinAt
      · exact ((hsmooth x hx hne).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨y, r, hr, hyzero, hyderiv, hyC1, hidentity, ?_⟩
  intro x hx
  have hsqrt := Real.sqrt_pos.mpr (hpos x hx)
  constructor
  · exact mul_pos_iff_of_pos_right hsqrt
  · change x * Real.sqrt (k x) < 0 ↔ x < 0
    constructor <;> intro ht <;> nlinarith

/-- The normalized coordinate is an actual local C¹ diffeomorphism. -/
theorem quadratic_coordinate
    {ψ : ℝ → ℝ} {a : ℝ} (ha : a ≠ 0) (hψ : ContDiffAt ℝ 2 ψ 0)
    (hzero : ψ 0 = 0) (hd : HasDerivAt ψ 0 0)
    (hdd : HasDerivAt (deriv ψ) (2 * a) 0) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (0 : ℝ) ∈ e.source ∧ e 0 = 0 ∧ HasDerivAt e 1 0 ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (∀ x ∈ e.source, ψ x = a * e x ^ 2) ∧
      (∀ x ∈ e.source, (0 < e x ↔ 0 < x) ∧ (e x < 0 ↔ x < 0)) := by
  obtain ⟨y, r, hr, hyzero, hyderiv, hyC1, hidentity, hsign⟩ :=
    quadratic_coordinate_function ha hψ hzero hd hdd
  have hyat := hyC1.contDiffAt (Metric.ball_mem_nhds (0 : ℝ) hr)
  let e₀ := hyat.toOpenPartialHomeomorph y
    (hyderiv.hasFDerivAt_equiv (by norm_num)) (by norm_num)
  have hmem : (0 : ℝ) ∈ e₀.source :=
    hyat.mem_toOpenPartialHomeomorph_source (hyderiv.hasFDerivAt_equiv (by norm_num)) (by norm_num)
  have hyprimecont : ContinuousAt (deriv y) 0 :=
    (hyC1.continuousOn_deriv_of_isOpen Metric.isOpen_ball le_rfl).continuousAt
      (Metric.ball_mem_nhds (0 : ℝ) hr)
  have hnear : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < deriv y x ∧ x ∈ Metric.ball 0 r := by
    have hp : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < deriv y x :=
      hyprimecont.preimage_mem_nhds (Ioi_mem_nhds (by rw [hyderiv.deriv]; norm_num))
    exact hp.and (Metric.ball_mem_nhds (0 : ℝ) hr)
  obtain ⟨s, hs, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  let e := e₀.restrOpen (Metric.ball 0 s) Metric.isOpen_ball
  have heval : (e : ℝ → ℝ) = y := rfl
  have hsource : e.source ⊆ Metric.ball 0 r := fun x hx => (hsmall hx.2).2
  have heC1 : ContDiffOn ℝ 1 e e.source := hyC1.mono hsource
  have he0 : (0 : ℝ) ∈ e.source := ⟨hmem, Metric.mem_ball_self hs⟩
  refine ⟨e, he0, hyzero, hyderiv, heC1, ?_, ?_, ?_⟩
  · intro z hz
    have hx := e.map_target hz
    have hsmooth : ContDiffAt ℝ 1 e (e.symm z) :=
      heC1.contDiffAt (e.open_source.mem_nhds hx)
    exact (e.contDiffAt_symm_deriv ((hsmall hx.2).1.ne') hz
      (hsmooth.differentiableAt (by norm_num)).hasDerivAt hsmooth).contDiffWithinAt
  · intro x hx
    exact hidentity x (hsource hx)
  · intro x hx
    exact hsign x (hsource hx)

/-- The derivative of the state partial along a graph tangent to the state
axis is the actual second state partial. -/
theorem state_derivative_on_graph
    {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {ψ : ℝ → ℝ}
    (hU : IsOpen U) (hmem : (0, 0) ∈ U) (hf : ContDiffOn ℝ 3 f U)
    (hψzero : ψ 0 = 0) (hd : HasDerivAt ψ 0 0) :
    HasDerivAt (fun x => stateDerivative f (ψ x, x)) (stateSecondDerivative f (0, 0)) 0 := by
  have hs : ContDiffAt ℝ 2 (stateDerivative f) (0, 0) :=
    ((hf.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const).contDiffAt
      (hU.mem_nhds hmem)
  have hg := hd.prodMk (hasDerivAt_id 0)
  simpa only [hψzero, stateSecondDerivative, Function.comp_def] using
    (show DifferentiableAt ℝ (stateDerivative f) (ψ 0, 0) from
      by simpa [hψzero] using hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
        (f := fun t => (ψ t, t)) 0 hg

/-- Local zero-set coordinates, together with the signs needed on its two
branches, obtained from the upstream scalar direction test. -/
theorem fold_coordinate
    (f : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hmem : (0, 0) ∈ U) (hf : ContDiffOn ℝ 3 f U)
    (hzero : f (0, 0) = 0) (hstate : stateDerivative f (0, 0) = 0)
    (hparam : parameterDerivative f (0, 0) ≠ 0)
    (hsecond : stateSecondDerivative f (0, 0) ≠ 0) :
    coefficient f ≠ 0 ∧ ∃ e : OpenPartialHomeomorph ℝ ℝ, ∃ s : ℝ,
      0 < s ∧ (0 : ℝ) ∈ e.source ∧ e 0 = 0 ∧ HasDerivAt e 1 0 ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      Metric.ball 0 s ×ˢ e.source ⊆ U ∧
      (∀ μ ∈ Metric.ball 0 s, ∀ x ∈ e.source,
        f (μ, x) = 0 ↔ μ = coefficient f * e x ^ 2) ∧
      (∀ x ∈ e.source, (0 < e x ↔ 0 < x) ∧ (e x < 0 ↔ x < 0)) ∧
      (∀ μ ∈ Metric.ball 0 s, ∀ x ∈ e.source, f (μ, x) = 0 → x ≠ 0 →
        (stateSecondDerivative f (0, 0) < 0 → stateDerivative f (μ, x) * x < 0) ∧
        (0 < stateSecondDerivative f (0, 0) → 0 < stateDerivative f (μ, x) * x)) := by
  have ha : coefficient f ≠ 0 := div_ne_zero (neg_ne_zero.mpr hsecond)
    (mul_ne_zero (by norm_num) hparam)
  obtain ⟨ψ, r, s, hr, hs, hψzero, hψC3, hbox, hψin, hgraph⟩ :=
    parameter_graph f U hU hmem hf hzero hparam
  have hψat := hψC3.contDiffAt (Metric.ball_mem_nhds (0 : ℝ) hr)
  have heq : ∀ᶠ x in 𝓝 (0 : ℝ), f (ψ x, x) = 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with x hx
    exact (hgraph (ψ x) (hψin x hx) x hx).mpr rfl
  obtain ⟨hd, hdd⟩ := parameter_graph_jets hU hmem hf hψat hψzero heq hstate hparam
  obtain ⟨e₀, he0, hezero, hederiv, heC1, heinv, heident, hesign⟩ :=
    quadratic_coordinate ha (hψat.of_le (by norm_num)) hψzero hd hdd
  obtain ⟨ρ, hρ, hdir⟩ := flow_directions
    (fun x => stateDerivative f (ψ x, x)) 0 (stateSecondDerivative f (0, 0))
    (by simpa [hψzero] using hstate)
    (state_derivative_on_graph hU hmem hf hψzero hd) hsecond
  let e := e₀.restrOpen (Metric.ball 0 r ∩ Metric.ball 0 ρ)
    (Metric.isOpen_ball.inter Metric.isOpen_ball)
  have hsource (x : ℝ) (hx : x ∈ e.source) : x ∈ e₀.source ∧ x ∈ Metric.ball 0 r ∧ x ∈ Metric.ball 0 ρ := hx
  have he0' : (0 : ℝ) ∈ e.source := ⟨he0, Metric.mem_ball_self hr, Metric.mem_ball_self hρ⟩
  refine ⟨ha, e, s, hs, he0', hezero, hederiv, heC1.mono (fun x hx => hx.1),
    heinv.mono (fun z hz => hz.1), ?_, ?_, ?_, ?_⟩
  · rintro ⟨μ, x⟩ ⟨hμ, hx⟩
    exact hbox ⟨hμ, (hsource x hx).2.1⟩
  · intro μ hμ x hx
    exact (hgraph μ hμ x (hsource x hx).2.1).trans
      (by rw [heident x (hsource x hx).1]; rfl)
  · intro x hx
    exact hesign x (hsource x hx).1
  · intro μ hμ x hx hz hne
    have hψx : μ = ψ x := (hgraph μ hμ x (hsource x hx).2.1).mp hz
    rw [hψx]
    have hbound : |x - 0| < ρ := by
      simpa only [sub_zero, Metric.mem_ball, Real.dist_eq] using (hsource x hx).2.2
    simpa only [sub_zero] using hdir x hbound hne

/-- Realize any equilibrium on the original open parameter slice, then apply
the scalar flow stability theorem to that same field. -/
theorem scalar_stability_at_equilibrium
    {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {μ p : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    (hmem : (μ, p) ∈ U) (hz : f (μ, p) = 0) :
    HasScalarStability f U μ p := by
  obtain ⟨F, hdom, heval, hF, h0, heq, hd⟩ :=
    realize_flow_slice f U hU (hf.of_le (by norm_num)) μ p hmem hz
  refine ⟨F, hdom, heval, hF, h0, heq, ?_⟩
  change deriv (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) 0 =
    stateDerivative f (μ, p) at hd
  simpa only [hd] using scalar_flow_stability F hF h0 heq

/-- The generic scalar saddle-node: an exact local coordinate for the zero
set, fixed-neighborhood root counts, and stability of the actual scalar flows. -/
theorem saddle_node :
    Specs.D13Unified.Ch16.SaddleNode.saddleNode := by
  intro f U hU hmem hf hzero hstate hparam hsecond
  obtain ⟨ha, e, s, hs, he0, hezero, hederiv, heC1, heinv, hbox, heq, hesign, hdir⟩ :=
    fold_coordinate f U hU hmem hf hzero hstate hparam hsecond
  have htarget0 : (0 : ℝ) ∈ e.target := by simpa only [hezero] using e.map_source he0
  obtain ⟨t, ht, htarget⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds htarget0)
  let ε := min s (|coefficient f| * t ^ 2)
  have hε : 0 < ε := lt_min hs (mul_pos (abs_pos.mpr ha) (sq_pos_of_pos ht))
  have hμs {μ : ℝ} (hμ : μ ∈ Metric.ball 0 ε) : μ ∈ Metric.ball 0 s := by
    exact lt_of_lt_of_le (show dist μ 0 < ε from hμ)
      (min_le_left s (|coefficient f| * t ^ 2))
  have hzeroroots : ∀ x ∈ e.source, f (0, x) = 0 ↔ x = 0 := by
    intro x hx
    constructor
    · intro hz
      have hfold := (heq 0 (Metric.mem_ball_self hs) x hx).mp hz
      have hsq : e x ^ 2 = 0 := (mul_eq_zero.mp hfold.symm).resolve_left ha
      have hex : e x = e 0 := by simpa only [sq_eq_zero_iff, hezero] using hsq
      exact e.injOn hx he0 hex
    · rintro rfl
      exact hzero
  refine ⟨ha, e, ε, hε, he0, hezero, heC1, heinv, hederiv,
    (fun z hz => hbox ⟨hμs hz.1, hz.2⟩),
    (fun μ hμ => heq μ (hμs hμ)), ?_, hzeroroots, hstate, hsecond⟩
  intro μ hμ
  refine ⟨?_, ?_, ?_⟩
  · intro hneg x hx hz
    have hfold := (heq μ (hμs hμ) x hx).mp hz
    have hsq : μ / coefficient f = e x ^ 2 :=
      (div_eq_iff ha).mpr (by rw [hfold]; ring_nf)
    rw [hsq] at hneg
    exact (sq_nonneg (e x)).not_gt hneg
  · rintro rfl
    exact hzeroroots
  · intro hpos
    have hμbound : |μ| < |coefficient f| * t ^ 2 :=
      lt_of_lt_of_le (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hμ)
        (min_le_right _ _)
    have hquot : μ / coefficient f < t ^ 2 := by
      have habs : |μ| / |coefficient f| < t ^ 2 :=
        (div_lt_iff₀ (abs_pos.mpr ha)).mpr (by nlinarith [hμbound])
      simpa only [← abs_div, abs_of_pos hpos] using habs
    have hsqrtpos := Real.sqrt_pos.mpr hpos
    have hsqrtlt := (Real.sqrt_lt' ht).mpr hquot
    have hypos : Real.sqrt (μ / coefficient f) ∈ e.target :=
      htarget (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hsqrtpos] using hsqrtlt)
    have hyneg : -Real.sqrt (μ / coefficient f) ∈ e.target :=
      htarget (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg,
        abs_of_pos hsqrtpos] using hsqrtlt)
    let xneg := e.symm (-Real.sqrt (μ / coefficient f))
    let xpos := e.symm (Real.sqrt (μ / coefficient f))
    have hxneg : xneg ∈ e.source := e.map_target hyneg
    have hxpos : xpos ∈ e.source := e.map_target hypos
    have hexneg : e xneg = -Real.sqrt (μ / coefficient f) := e.right_inv hyneg
    have hexpos : e xpos = Real.sqrt (μ / coefficient f) := e.right_inv hypos
    have hxneglt : xneg < 0 := (hesign xneg hxneg).2.mp (by rw [hexneg]; linarith)
    have hxposgt : 0 < xpos := (hesign xpos hxpos).1.mp (by rw [hexpos]; exact hsqrtpos)
    have hzneg : f (μ, xneg) = 0 := by
      apply (heq μ (hμs hμ) xneg hxneg).mpr
      rw [hexneg, neg_sq, Real.sq_sqrt hpos.le]
      field_simp
    have hzpos : f (μ, xpos) = 0 := by
      apply (heq μ (hμs hμ) xpos hxpos).mpr
      rw [hexpos, Real.sq_sqrt hpos.le]
      field_simp
    have hroots : ∀ x ∈ e.source, f (μ, x) = 0 ↔ x = xneg ∨ x = xpos := by
      intro x hx
      constructor
      · intro hz
        have hfold := (heq μ (hμs hμ) x hx).mp hz
        have hsq : e x ^ 2 = (Real.sqrt (μ / coefficient f)) ^ 2 := by
          rw [Real.sq_sqrt hpos.le]
          apply (eq_div_iff ha).mpr
          rw [hfold]
          ring_nf
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp | hn
        · exact Or.inr (e.injOn hx hxpos (hp.trans hexpos.symm))
        · exact Or.inl (e.injOn hx hxneg (hn.trans hexneg.symm))
      · rintro (rfl | rfl)
        · exact hzneg
        · exact hzpos
    have hopposite : stateDerivative f (μ, xneg) * stateDerivative f (μ, xpos) < 0 := by
      have hdn := hdir μ (hμs hμ) xneg hxneg hzneg hxneglt.ne
      have hdp := hdir μ (hμs hμ) xpos hxpos hzpos hxposgt.ne'
      rcases lt_or_gt_of_ne hsecond with hn | hp
      · have hnegprod := hdn.1 hn
        have hposprod := hdp.1 hn
        have hleft : 0 < stateDerivative f (μ, xneg) := by
          rcases mul_neg_iff.mp hnegprod with h | h
          · exact h.1
          · exact False.elim (hxneglt.not_gt h.2)
        have hright : stateDerivative f (μ, xpos) < 0 := by
          rcases mul_neg_iff.mp hposprod with h | h
          · exact False.elim (hxposgt.not_gt h.2)
          · exact h.1
        exact mul_neg_of_pos_of_neg hleft hright
      · have hleft := neg_of_mul_pos_left (hdn.2 hp) hxneglt.le
        have hright := pos_of_mul_pos_left (hdp.2 hp) hxposgt.le
        exact mul_neg_of_neg_of_pos hleft hright
    exact ⟨xneg, xpos, hxneg, hxpos, hxneglt, hxposgt, hexneg, hexpos, hroots, hopposite,
      scalar_stability_at_equilibrium hU hf (hbox ⟨hμs hμ, hxneg⟩) hzneg,
      scalar_stability_at_equilibrium hU hf (hbox ⟨hμs hμ, hxpos⟩) hzpos⟩

end D13Unified.Ch16.SaddleNode
