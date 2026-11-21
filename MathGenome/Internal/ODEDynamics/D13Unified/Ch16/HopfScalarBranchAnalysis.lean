import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfScalarBranchAnalysis
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.HopfReturnExpansion
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace D13Unified.Ch16.HopfScalarBranchAnalysis
open Set Filter
open Specs.D13Unified.Ch16.CubicHomologicalElimination
open Specs.D13Unified.Ch16.CubicNormalForm
open Specs.D13Unified.Ch16.HopfReturnExpansion
open Specs.D13Unified.Ch16.HopfScalarBranchAnalysis

lemma returnBox_isOpen (δ ε : ℝ) : IsOpen (returnBox δ ε) :=
  (isOpen_lt (continuous_fst.abs) continuous_const).inter
    (isOpen_lt (continuous_snd.abs) continuous_const)

lemma zero_mem_returnBox {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    (0 : ℝ × ℝ) ∈ returnBox δ ε := by
  exact ⟨by simpa using hδ, by simpa using hε⟩

/-- Package the supplied analytic data, without choosing or assuming a branch. -/
theorem sourceReturnData (F : ℝ × ℂ → ℂ) (ω : ℝ) (h : SourceHypotheses F ω) :
    ∃ ε > 0, ∃ ρ > 0, ∃ δ > 0, ∃ C > 0, ∃ P Q : ℝ × ℝ → ℝ,
      δ < ρ ∧ CoordinateValidity F ε ρ ∧ ReturnData F ω ε δ C P Q ∧
      (∀ μ r, |μ| < ε → 0 < r → r < δ →
        FullAngularTurn F ω μ r (P (r, μ)) ρ) := by
  obtain ⟨hK, ε, hε, ρ, hρ, δ, hδ, C, hC, P, Q, hdρ, hcoord,
    hP, hQ, hE, hzero, hbounds, hturn⟩ :=
    HopfReturnExpansion.returnExpansion F ω h.regularity h.frequency_pos h.eigenvalue h.equilibrium
  exact ⟨ε, hε, ρ, hρ, δ, hδ, C, hC, P, Q, hdρ, hcoord,
    ⟨hK, hP, hQ, hE, hzero, hbounds⟩, hturn⟩

/-- Actual derivative of the exponential linear displacement at criticality. -/
theorem linear_displacement_derivative (F : ℝ × ℂ → ℂ) (ω : ℝ)
    (ha : spectralReal F 0 = 0) (hb : spectralImag F 0 = ω) (hω : 0 < ω)
    (hda : DifferentiableAt ℝ (spectralReal F) 0)
    (hdb : DifferentiableAt ℝ (spectralImag F) 0) :
    HasDerivAt (fun μ => linearReturnFactor F μ - 1)
      (turnAngle * deriv (spectralReal F) 0 / ω) 0 := by
  have hd := ((hda.hasDerivAt.div hdb.hasDerivAt (by rw [hb]; exact hω.ne')).const_mul
    turnAngle).exp.sub_const 1
  convert hd using 1 <;> simp [linearReturnFactor, angularLinear, ha, hb]
  field_simp
  <;> ring

/-- Divide the genuine fourth-order error, including the signed-radius zero. -/
theorem quotient_error_bound {F : ℝ × ℂ → ℂ} {ω ε δ C : ℝ}
    {P Q : ℝ × ℝ → ℝ} (h : ReturnData F ω ε δ C P Q)
    (q : ℝ × ℝ) (hq : q ∈ returnBox δ ε) :
    |Q q - (linearReturnFactor F q.2 - 1) - cubicReturnCoefficient F q.2 * q.1 ^ 2|
      ≤ C * |q.1| ^ 3 := by
  by_cases hr : q.1 = 0
  · have hz := (h.at_zero q.2 hq.2).2
    have hqz : q = (0, q.2) := Prod.ext hr rfl
    rw [hqz]
    simp only [Prod.fst, Prod.snd, hz, zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 3 ≠ 0), mul_zero, sub_self, sub_zero, abs_zero, le_refl]
  have hab : 0 < |q.1| := abs_pos.mpr hr
  have hid :
      Q q - (linearReturnFactor F q.2 - 1) - cubicReturnCoefficient F q.2 * q.1 ^ 2 =
        returnError F P q / q.1 := by
    apply (eq_div_iff hr).mpr
    rw [returnError, (h.bounds q hq).1]
    ring
  rw [hid, abs_div]
  apply (div_le_iff₀ hab).mpr
  calc
    |returnError F P q| ≤ C * |q.1| ^ 4 := (h.bounds q hq).2.1
    _ = C * |q.1| ^ 3 * |q.1| := by ring

/-- Scalar C² implicit function theorem, with all nearby zeros characterized. -/
theorem implicitGraph (Q : ℝ × ℝ → ℝ) (hQ : ContDiffAt ℝ 2 Q 0)
    (hzero : Q 0 = 0)
    (hinv : (fderiv ℝ Q 0 ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = 0 ∧
      (∀ᶠ q in nhds (0 : ℝ × ℝ), Q q = 0 ↔ q.2 = ψ q.1) := by
  let ψ := hQ.implicitFunction (by decide) hinv
  refine ⟨ψ, hQ.contDiffAt_implicitFunction (by decide) hinv,
    hQ.implicitFunction_apply_self (by decide) hinv, ?_⟩
  filter_upwards [hQ.eventually_apply_eq_iff_implicitFunction (by decide) hinv] with q hq
  simpa only [hzero, eq_comm] using hq

/-- The canonical normal-form theorem supplies spectral regularity and the
critical values used in differentiating the actual quotient. -/
theorem quotient_parameter_derivative {F : ℝ × ℂ → ℂ} {ω ε δ C : ℝ}
    {P Q : ℝ × ℝ → ℝ} (hs : SourceHypotheses F ω)
    (hε : 0 < ε) (h : ReturnData F ω ε δ C P Q) :
    HasDerivAt (fun μ => Q (0, μ))
      (turnAngle * deriv (spectralReal F) 0 / ω) 0 := by
  obtain ⟨ha, hb, η, hη, ρ, hρ, D, hD, hc, hR, hreg⟩ :=
    CubicNormalForm.normalForm F ω hs.regularity hs.frequency_pos hs.eigenvalue hs.equilibrium
  have hreg0 := hreg 0 (by simpa using hη)
  have hd := linear_displacement_derivative F ω ha hb hs.frequency_pos
    (hreg0.2.1.differentiableAt (by norm_num))
    (hreg0.2.2.1.differentiableAt (by norm_num))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Metric.eventually_nhds_iff.mpr
    ⟨ε, hε, fun μ hμ => (h.at_zero μ (by simpa [Real.dist_eq] using hμ)).2⟩] with μ hμ
  exact hμ

/-- The O(r³) quotient residual forces its radial derivative at zero to
vanish. This argument uses signed radii and includes r=0. -/
theorem quotient_radial_derivative {F : ℝ × ℂ → ℂ} {ω ε δ C : ℝ}
    {P Q : ℝ × ℝ → ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (h : ReturnData F ω ε δ C P Q) :
    HasDerivAt (fun r => Q (r, 0)) 0 0 := by
  let L := linearReturnFactor F 0 - 1
  let K := cubicReturnCoefficient F 0
  let R : ℝ → ℝ := fun r => Q (r, 0) - L - K * r ^ 2
  have hO : R =O[nhds (0 : ℝ)] (fun r => r ^ 3) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [Metric.eventually_nhds_iff.mpr
      ⟨δ, hδ, fun r hr => show |r| < δ by simpa [Real.dist_eq] using hr⟩] with r hr
    simpa [R, L, K, Real.norm_eq_abs, abs_pow] using
      quotient_error_bound h (r, 0) ⟨hr, by simpa using hε⟩
  have hRo : R =o[nhds (0 : ℝ)] (fun r => r) :=
    hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (by decide : 1 < 3))
  have hR0 : R 0 = 0 := by simp [R, L, K, (h.at_zero 0 (by simpa using hε)).2]
  have hdR : HasDerivAt R 0 0 := by
    apply HasDerivAt.of_isLittleO
    simpa only [hR0, sub_zero, smul_zero] using hRo
  have hdpoly : HasDerivAt (fun r : ℝ => L + K * r ^ 2) 0 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).pow 2).const_mul K |>.const_add L using 1 <;> simp
  have hid : (fun r => Q (r, 0)) = fun r => R r + (L + K * r ^ 2) := by
    funext r; dsimp [R]; ring
  rw [hid]
  convert hdR.add hdpoly using 1 <;> simp

/-- The parameter partial is scalar multiplication by the computed nonzero
κ; invertibility is proved by an explicit continuous linear inverse. -/
theorem sourceImplicitGraph {F : ℝ × ℂ → ℂ} {ω ε δ C : ℝ}
    {P Q : ℝ × ℝ → ℝ} (hs : SourceHypotheses F ω)
    (hε : 0 < ε) (hδ : 0 < δ) (h : ReturnData F ω ε δ C P Q) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = 0 ∧
      (∀ᶠ q in nhds (0 : ℝ × ℝ), Q q = 0 ↔ q.2 = ψ q.1) := by
  have hQ : ContDiffAt ℝ 2 Q 0 := h.quotient_regular.contDiffAt
    ((returnBox_isOpen δ ε).mem_nhds (zero_mem_returnBox hδ hε))
  let κ := turnAngle * deriv (spectralReal F) 0 / ω
  have hκ : κ ≠ 0 := div_ne_zero
    (mul_ne_zero (by dsimp [turnAngle]; positivity) hs.crossing) hs.frequency_pos.ne'
  have hder := quotient_parameter_derivative hs hε h
  have hcomp := hQ.differentiableAt (by norm_num) |>.hasFDerivAt |>.comp_hasDerivAt
    (f := fun μ : ℝ => (0, μ)) (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))
  have hv : fderiv ℝ Q 0 (0, 1) = κ := hcomp.unique hder
  have hlin : fderiv ℝ Q 0 ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      κ • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro x
    change fderiv ℝ Q 0 (0, x) = κ * x
    have hx : (0, x) = x • ((0, 1) : ℝ × ℝ) := by simp
    rw [hx, map_smul, hv]; simp [mul_comm]
  have hinv : (fderiv ℝ Q 0 ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hlin]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := κ⁻¹ • ContinuousLinearMap.id ℝ ℝ) <;>
      apply ContinuousLinearMap.ext <;> intro x <;> simp [hκ, mul_assoc]
  have hzero : Q 0 = 0 := by
    change Q (0, 0) = 0
    obtain ⟨ha, hb, _⟩ := CubicNormalForm.normalForm F ω hs.regularity
      hs.frequency_pos hs.eigenvalue hs.equilibrium
    simpa [linearReturnFactor, angularLinear, ha] using
      (h.at_zero 0 (by simpa using hε)).2
  exact implicitGraph Q hQ hzero hinv

/-- Differentiate the genuine implicit identity, using both computed partials. -/
theorem flatImplicitGraph : FlatImplicitGraph := by
  intro F ω hs ε δ C P Q hε hδ hC h
  obtain ⟨ψ, hψ, hψ0, hgraph⟩ := sourceImplicitGraph hs hε hδ h
  refine ⟨ψ, hψ, hψ0, ?_, hgraph⟩
  have hQ : ContDiffAt ℝ 2 Q 0 := h.quotient_regular.contDiffAt
    ((returnBox_isOpen δ ε).mem_nhds (zero_mem_returnBox hδ hε))
  have hdQ := (hQ.differentiableAt (by norm_num)).hasFDerivAt
  have hdψ := (hψ.differentiableAt (by norm_num)).hasDerivAt
  have hQr := quotient_radial_derivative hε hδ h
  have hQμ := quotient_parameter_derivative hs hε h
  have hQr' := hdQ.comp_hasDerivAt (f := fun r : ℝ => (r, 0)) (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))
  have hQμ' := hdQ.comp_hasDerivAt (f := fun μ : ℝ => (0, μ)) (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))
  have hvr : fderiv ℝ Q 0 (1, 0) = 0 := hQr'.unique hQr
  have hvμ : fderiv ℝ Q 0 (0, 1) = turnAngle * deriv (spectralReal F) 0 / ω :=
    hQμ'.unique hQμ
  have hcurve : ContinuousAt (fun r => (r, ψ r)) 0 := continuousAt_id.prodMk hψ.continuousAt
  have hcurve0 : (0, ψ 0) = (0 : ℝ × ℝ) := by simp [hψ0]
  have hident : (fun r => Q (r, ψ r)) =ᶠ[nhds (0 : ℝ)] fun _ => 0 := by
    have hc : Tendsto (fun r => (r, ψ r)) (nhds 0) (nhds (0 : ℝ × ℝ)) := by
      convert hcurve.tendsto using 1 <;> simp [hψ0] <;> rfl
    filter_upwards [hc.eventually hgraph] with r hr
    exact hr.mpr rfl
  have hdcurve := hdQ.comp_hasDerivAt_of_eq (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).prodMk hdψ) hcurve0.symm
  have hz : fderiv ℝ Q 0 (1, deriv ψ 0) = 0 :=
    hdcurve.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hident)
  have hsplit : (1, deriv ψ 0) = ((1, 0) : ℝ × ℝ) + deriv ψ 0 • (0, 1) := by simp
  rw [hsplit, map_add, map_smul, hvr, hvμ] at hz
  have hκ : turnAngle * deriv (spectralReal F) 0 / ω ≠ 0 := div_ne_zero
    (mul_ne_zero (by dsimp [turnAngle]; positivity) hs.crossing) hs.frequency_pos.ne'
  simp only [zero_add, smul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_right hκ

/-- C² regularity gives a uniform second-order remainder near zero.
The estimate follows from the mean-value theorem on each signed segment. -/
theorem second_order_remainder_bigO (f : ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0) :
    (fun x => f x - f 0 - deriv f 0 * x) =O[nhds (0 : ℝ)] (fun x => x ^ 2) := by
  have hd : DifferentiableAt ℝ (deriv f) 0 :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  obtain ⟨C, hC⟩ := hd.isBigO_sub.bound
  have hdiff : ∀ᶠ x in nhds (0 : ℝ), DifferentiableAt ℝ f x :=
    (hf.eventually (by norm_num)).mono fun _ hx => hx.differentiableAt (by norm_num)
  obtain ⟨η, hη, hb⟩ := Metric.eventually_nhds_iff.mp (hC.and hdiff)
  apply Asymptotics.IsBigO.of_bound (max C 0)
  filter_upwards [Metric.eventually_nhds_iff.mpr
    ⟨η, hη, fun x hx => show |x| < η by simpa [Real.dist_eq] using hx⟩] with x hx
  let g : ℝ → ℝ := fun t => f t - f 0 - deriv f 0 * t
  have ht (t : ℝ) (ht : t ∈ segment ℝ 0 x) : |t| ≤ |x| := by
    simpa [Real.norm_eq_abs] using norm_sub_le_of_mem_segment ht
  have hb' (t : ℝ) (ht' : t ∈ segment ℝ 0 x) :=
    hb (show dist t 0 < η by simpa [Real.dist_eq] using (ht t ht').trans_lt hx)
  have hg : ∀ t ∈ segment ℝ 0 x,
      HasDerivWithinAt g (deriv f t - deriv f 0) (segment ℝ 0 x) t := by
    intro t ht'
    convert! (((hb' t ht').2.hasDerivAt.sub_const (f 0)).sub
      ((hasDerivAt_id t).const_mul (deriv f 0))).hasDerivWithinAt using 1 <;> simp [g]
  have hbound : ∀ t ∈ segment ℝ 0 x, ‖deriv f t - deriv f 0‖ ≤ max C 0 * |x| := by
    intro t ht'
    calc
      _ ≤ C * |t| := by simpa [Real.norm_eq_abs] using (hb' t ht').1
      _ ≤ max C 0 * |t| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg t)
      _ ≤ max C 0 * |x| := mul_le_mul_of_nonneg_left (ht t ht') (le_max_right _ _)
  have hmv := (convex_segment (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le
    hg hbound (left_mem_segment ℝ 0 x) (right_mem_segment ℝ 0 x)
  simpa [g, Real.norm_eq_abs, abs_pow, pow_two, mul_assoc] using hmv

/-- Differentiating the actual factorization controls the quotient radial
partial uniformly at every nonzero signed radius. -/
theorem quotient_radial_error_bound {F : ℝ × ℂ → ℂ} {ω ε δ C : ℝ}
    {P Q : ℝ × ℝ → ℝ} (h : ReturnData F ω ε δ C P Q)
    (r μ : ℝ) (hq : (r, μ) ∈ returnBox δ ε) (hr : r ≠ 0) :
    |deriv (fun s => Q (s, μ)) r - 2 * cubicReturnCoefficient F μ * r|
      ≤ 2 * C * |r| ^ 2 := by
  let L := linearReturnFactor F μ
  let K := cubicReturnCoefficient F μ
  have hQ : ContDiffAt ℝ 2 Q (r, μ) := h.quotient_regular.contDiffAt
    ((returnBox_isOpen δ ε).mem_nhds hq)
  have hdQ := (hQ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    (f := fun s : ℝ => (s, μ)) r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r μ))
  have hdQ' := hdQ.differentiableAt.hasDerivAt
  have hdP := (hasDerivAt_id r).mul ((hasDerivAt_const r (1 : ℝ)).add hdQ')
  have hEq : (fun s => P (s, μ)) =ᶠ[nhds r] (fun s => s * (1 + Q (s, μ))) := by
    have hc : ContinuousAt (fun s : ℝ => (s, μ)) r := continuousAt_id.prodMk continuousAt_const
    filter_upwards [hc.eventually ((returnBox_isOpen δ ε).mem_nhds hq)] with s hs
    exact (h.bounds (s, μ) hs).1
  have hdE := ((hdP.congr_of_eventuallyEq hEq).sub
    ((hasDerivAt_id r).const_mul L)).sub (((hasDerivAt_id r).pow 3).const_mul K)
  have heder : deriv (fun s => returnError F P (s, μ)) r =
      (1 + Q (r, μ)) + r * deriv (fun s => Q (s, μ)) r - L - 3 * K * r ^ 2 := by
    convert! hdE.deriv using 1 <;> dsimp [returnError, L, K, Function.comp_def] <;> ring
  have hid :
      (deriv (fun s => Q (s, μ)) r - 2 * K * r) * r ^ 2 =
      r * deriv (fun s => returnError F P (s, μ)) r - returnError F P (r, μ) := by
    rw [heder, returnError, (h.bounds (r, μ) hq).1]
    dsimp [L, K]; ring
  have he := (h.bounds (r, μ) hq).2.1
  have her := (h.bounds (r, μ) hq).2.2.1
  have hab : 0 < |r| := abs_pos.mpr hr
  have hb :
      |deriv (fun s => Q (s, μ)) r - 2 * K * r| * |r| ^ 2 ≤
        (2 * C * |r| ^ 2) * |r| ^ 2 := by
    calc
      _ = |r * deriv (fun s => returnError F P (s, μ)) r - returnError F P (r, μ)| := by
        rw [← hid, abs_mul, abs_pow]
      _ ≤ |r| * |deriv (fun s => returnError F P (s, μ)) r| + |returnError F P (r, μ)| := by
        simpa only [abs_mul] using abs_sub (r * deriv (fun s => returnError F P (s, μ)) r) (returnError F P (r, μ))
      _ ≤ |r| * (C * |r| ^ 3) + C * |r| ^ 4 :=
        add_le_add (mul_le_mul_of_nonneg_left her hab.le) he
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (pow_pos hab 2)).mp (by simpa [mul_comm] using hb)

/-- Parameter regularity of the actual two scalar coefficients. The integral
factor is smooth also at zero, so no division by a(μ) is used. -/
theorem source_coefficients_regular {F : ℝ × ℂ → ℂ} {ω : ℝ}
    (hs : SourceHypotheses F ω) :
    ContDiffAt ℝ 2 (linearReturnFactor F) 0 ∧
    ContDiffAt ℝ 2 (cubicReturnCoefficient F) 0 := by
  obtain ⟨ha0, hb0, η, hη, ρ, hρ, C, hC, hc, hR, hreg⟩ :=
    CubicNormalForm.normalForm F ω hs.regularity hs.frequency_pos hs.eigenvalue hs.equilibrium
  have hr := hreg 0 (by simpa using hη)
  obtain ⟨hA, hB⟩ := HopfPolarReduction.angular_coefficients_regular F 0
    hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.1.ne'
  have hL : ContDiffAt ℝ 2 (linearReturnFactor F) 0 := (contDiffAt_const.mul hA).exp
  refine ⟨hL, ?_⟩
  have h2A : ContDiffAt ℝ 2 (fun μ => 2 * angularLinear F μ) 0 := contDiffAt_const.mul hA
  have hi := (HopfAngularScalarEstimates.exponentialIntegral_c2 turnAngle).contDiffAt.comp
    (0 : ℝ) h2A
  convert! (hB.mul hL).mul hi using 1

/-- Quantitative value estimate along the actual local implicit graph. -/
theorem graph_value_bigO {F : ℝ × ℂ → ℂ} {ω ε δ C : ℝ}
    {P Q : ℝ × ℝ → ℝ} (hs : SourceHypotheses F ω)
    (hε : 0 < ε) (hδ : 0 < δ) (h : ReturnData F ω ε δ C P Q)
    (ψ : ℝ → ℝ) (hψ : ContDiffAt ℝ 2 ψ 0) (hψ0 : ψ 0 = 0)
    (hψflat : deriv ψ 0 = 0)
    (hgraph : ∀ᶠ q in nhds (0 : ℝ × ℝ), Q q = 0 ↔ q.2 = ψ q.1) :
    (fun r => ψ r - branchCoefficient F * r ^ 2) =O[nhds (0 : ℝ)] (fun r => r ^ 3) := by
  let κ := turnAngle * deriv (spectralReal F) 0 / ω
  let K₀ := cubicReturnCoefficient F 0
  have hκ : κ ≠ 0 := div_ne_zero
    (mul_ne_zero (by dsimp [turnAngle]; positivity) hs.crossing) hs.frequency_pos.ne'
  obtain ⟨ha0, hb0, η, hη, ρ, hρ, D, hD, hc, hR, hreg⟩ :=
    CubicNormalForm.normalForm F ω hs.regularity hs.frequency_pos hs.eigenvalue hs.equilibrium
  have hr := hreg 0 (by simpa using hη)
  have hdL := linear_displacement_derivative F ω ha0 hb0 hs.frequency_pos
    (hr.2.1.differentiableAt (by norm_num)) (hr.2.2.1.differentiableAt (by norm_num))
  have hL0 : linearReturnFactor F 0 = 1 := by simp [linearReturnFactor, angularLinear, ha0]
  have hLder : deriv (linearReturnFactor F) 0 = κ := by
    simpa using (hdL.add_const 1).deriv
  obtain ⟨hL, hK⟩ := source_coefficients_regular hs
  have hψO : ψ =O[nhds (0 : ℝ)] (fun r => r ^ 2) := by
    simpa only [hψ0, hψflat, zero_mul, sub_zero] using second_order_remainder_bigO ψ hψ
  have hψt : Tendsto ψ (nhds 0) (nhds 0) := by simpa only [hψ0] using hψ.continuousAt.tendsto
  have hcurve : Tendsto (fun r => (r, ψ r)) (nhds 0) (nhds (0 : ℝ × ℝ)) := by
    convert! tendsto_id.prodMk_nhds hψt using 1
  have hevent := hcurve.eventually ((returnBox_isOpen δ ε).mem_nhds (zero_mem_returnBox hδ hε))
  let R : ℝ → ℝ := fun r => Q (r, ψ r) - (linearReturnFactor F (ψ r) - 1) -
    cubicReturnCoefficient F (ψ r) * r ^ 2
  have hRO : R =O[nhds (0 : ℝ)] (fun r => r ^ 3) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hevent] with r hr
    simpa only [R, Real.norm_eq_abs, abs_pow] using quotient_error_bound h (r, ψ r) hr
  have hLO : (fun μ => linearReturnFactor F μ - 1 - κ * μ) =O[nhds (0 : ℝ)]
      (fun μ => μ ^ 2) := by
    simpa only [hL0, hLder] using second_order_remainder_bigO (linearReturnFactor F) hL
  have hKO : (fun μ => cubicReturnCoefficient F μ - K₀) =O[nhds (0 : ℝ)] (fun μ => μ) := by
    simpa only [sub_zero, K₀] using (hK.differentiableAt (by norm_num)).isBigO_sub
  have hp4 : (fun r : ℝ => (r ^ 2) ^ 2) =O[nhds (0 : ℝ)] (fun r => r ^ 3) := by
    convert! (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by decide : 3 < 4)).isBigO using 1
    funext r; ring
  have hLψ := (hLO.comp_tendsto hψt).trans ((hψO.pow 2).trans hp4)
  have hKψ := (hKO.comp_tendsto hψt).trans hψO
  have hKψr := (hKψ.mul (Asymptotics.isBigO_refl (fun r : ℝ => r ^ 2) (nhds 0))).trans
    (show (fun r : ℝ => r ^ 2 * r ^ 2) =O[nhds (0 : ℝ)] (fun r => r ^ 3) by
      convert! hp4 using 1 <;> funext r <;> ring)
  have hsum := ((hRO.add hLψ).add hKψr).neg_left
  have hleading : (fun r => κ * ψ r + K₀ * r ^ 2) =O[nhds (0 : ℝ)] (fun r => r ^ 3) := by
    apply hsum.congr' _ (Filter.EventuallyEq.rfl)
    filter_upwards [hcurve.eventually hgraph] with r hr
    have hz := hr.mpr rfl
    dsimp [R, K₀]
    rw [hz]; ring
  have hcoeff : κ * branchCoefficient F = -K₀ := by
    dsimp [κ, branchCoefficient, K₀]
    rw [h.coefficient_zero]
    field_simp [hs.crossing, hs.frequency_pos.ne']
    <;> ring
  apply (Asymptotics.isBigO_const_mul_left_iff hκ).mp
  convert! hleading using 1
  funext r
  rw [mul_sub, ← mul_assoc, hcoeff]
  ring

/-- The first derivative estimate uses the actual radial error bound and
C² regularity of Q. In particular, it is not inferred by differentiating
an unqualified O(r³) statement. -/
theorem graph_derivative_bigO {F : ℝ × ℂ → ℂ} {ω ε δ C : ℝ}
    {P Q : ℝ × ℝ → ℝ} (hs : SourceHypotheses F ω)
    (hε : 0 < ε) (hδ : 0 < δ) (h : ReturnData F ω ε δ C P Q)
    (ψ : ℝ → ℝ) (hψ : ContDiffAt ℝ 2 ψ 0) (hψ0 : ψ 0 = 0)
    (hψflat : deriv ψ 0 = 0)
    (hgraph : ∀ᶠ q in nhds (0 : ℝ × ℝ), Q q = 0 ↔ q.2 = ψ q.1) :
    (fun r => deriv ψ r - 2 * branchCoefficient F * r) =O[nhds (0 : ℝ)] (fun r => r ^ 2) := by
  let κ := turnAngle * deriv (spectralReal F) 0 / ω
  let K₀ := cubicReturnCoefficient F 0
  let U : ℝ → ℝ := fun r => fderiv ℝ Q (r, ψ r) (0, 1)
  let V : ℝ → ℝ := fun r => fderiv ℝ Q (r, ψ r) (1, 0)
  have hκ : κ ≠ 0 := div_ne_zero
    (mul_ne_zero (by dsimp [turnAngle]; positivity) hs.crossing) hs.frequency_pos.ne'
  have hQ : ContDiffAt ℝ 2 Q 0 := h.quotient_regular.contDiffAt
    ((returnBox_isOpen δ ε).mem_nhds (zero_mem_returnBox hδ hε))
  have hdQ := (hQ.differentiableAt (by norm_num)).hasFDerivAt
  have hvr := (hdQ.comp_hasDerivAt (f := fun r : ℝ => (r, 0)) (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))).unique
    (quotient_radial_derivative hε hδ h)
  have hvμ := (hdQ.comp_hasDerivAt (f := fun μ : ℝ => (0, μ)) (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))).unique
    (quotient_parameter_derivative hs hε h)
  have hV0 : V 0 = 0 := by convert! hvr using 1 <;> simp [V, hψ0] <;> rfl
  have hU0 : U 0 = κ := by convert! hvμ using 1 <;> simp [U, hψ0, κ] <;> rfl
  have hc : ContDiffAt ℝ 1 (fun r => (r, ψ r)) 0 :=
    contDiffAt_id.prodMk (hψ.of_le (by norm_num))
  have hc0 : (0, ψ 0) = (0 : ℝ × ℝ) := by simp [hψ0]
  have hU : ContDiffAt ℝ 1 U 0 := by
    have hd : ContDiffAt ℝ 1 (fderiv ℝ Q) (0, ψ 0) := by
      rw [hc0]; exact hQ.fderiv_right (m := 1) (by norm_num)
    exact (hd.comp 0 hc).clm_apply contDiffAt_const
  have hUO : (fun r => U r - κ) =O[nhds (0 : ℝ)] (fun r => r) := by
    simpa only [hU0, sub_zero] using (hU.differentiableAt (by norm_num)).isBigO_sub
  have hdψ : ContDiffAt ℝ 1 (deriv ψ) 0 := hψ.derivWithin (by norm_num)
  have hdψO : deriv ψ =O[nhds (0 : ℝ)] (fun r => r) := by
    simpa only [hψflat, sub_zero] using (hdψ.differentiableAt (by norm_num)).isBigO_sub
  have hcT : Tendsto (fun r => (r, ψ r)) (nhds 0) (nhds (0 : ℝ × ℝ)) := by
    convert! hc.continuousAt.tendsto using 1 <;> simp [hψ0] <;> rfl
  have hevent := hcT.eventually ((returnBox_isOpen δ ε).mem_nhds (zero_mem_returnBox hδ hε))
  have hVO : (fun r => V r - 2 * cubicReturnCoefficient F (ψ r) * r) =O[nhds (0 : ℝ)]
      (fun r => r ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (2 * C)
    filter_upwards [hevent] with r hr
    by_cases hz : r = 0
    · simp [hz, hV0]
    have hQr : ContDiffAt ℝ 2 Q (r, ψ r) := h.quotient_regular.contDiffAt
      ((returnBox_isOpen δ ε).mem_nhds hr)
    have hdd := (hQr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      (f := fun s : ℝ => (s, ψ r)) r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r (ψ r)))
    have hder : deriv (fun s => Q (s, ψ r)) r = V r := hdd.deriv
    simpa only [Real.norm_eq_abs, abs_pow, hder] using quotient_radial_error_bound h r (ψ r) hr hz
  have hK : ContDiffAt ℝ 2 (cubicReturnCoefficient F) 0 := (source_coefficients_regular hs).2
  have hKψ : DifferentiableAt ℝ (fun r => cubicReturnCoefficient F (ψ r)) 0 := by
    have hK' : ContDiffAt ℝ 2 (cubicReturnCoefficient F) (ψ 0) := by rwa [hψ0]
    exact (hK'.differentiableAt (by norm_num)).comp 0
      (hψ.differentiableAt (by norm_num))
  have hKO : (fun r => cubicReturnCoefficient F (ψ r) - K₀) =O[nhds (0 : ℝ)] (fun r => r) := by
    simpa only [hψ0, K₀, sub_zero] using hKψ.isBigO_sub
  have hKOr : (fun r => 2 * (cubicReturnCoefficient F (ψ r) - K₀) * r) =O[nhds (0 : ℝ)]
      (fun r => r ^ 2) := by
    convert! (hKO.const_mul_left 2).mul (Asymptotics.isBigO_refl (fun r : ℝ => r) (nhds 0)) using 1
    funext r; ring
  have hVO' : (fun r => V r - 2 * K₀ * r) =O[nhds (0 : ℝ)] (fun r => r ^ 2) := by
    convert! hVO.add hKOr using 1
    funext r; ring
  have hproduct : (fun r => (U r - κ) * deriv ψ r) =O[nhds (0 : ℝ)] (fun r => r ^ 2) := by
    convert! hUO.mul hdψO using 1
    funext r; ring
  have hident : ∀ᶠ r in nhds (0 : ℝ), V r + U r * deriv ψ r = 0 := by
    have hzero : (fun r => Q (r, ψ r)) =ᶠ[nhds (0 : ℝ)] fun _ => 0 := by
      filter_upwards [hcT.eventually hgraph] with r hr
      exact hr.mpr rfl
    have hdiffψ := (hψ.eventually (by norm_num)).mono
      fun r hr => hr.differentiableAt (by norm_num)
    have hloc : ∀ᶠ r in nhds (0 : ℝ), (fun s => Q (s, ψ s)) =ᶠ[nhds r] fun _ => 0 :=
      hzero.eventually_nhds
    filter_upwards [hevent, hdiffψ, hloc] with r hr hψr hzr
    have hQr : ContDiffAt ℝ 2 Q (r, ψ r) := h.quotient_regular.contDiffAt
      ((returnBox_isOpen δ ε).mem_nhds hr)
    have hd := (hQr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      r ((hasDerivAt_id r).prodMk hψr.hasDerivAt)
    have hz := hd.unique ((hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq hzr)
    have hv : (1, deriv ψ r) = ((1, 0) : ℝ × ℝ) + deriv ψ r • (0, 1) := by simp
    rw [hv, map_add, map_smul] at hz
    simpa only [U, V, smul_eq_mul, mul_comm] using hz
  have hcoeff : κ * branchCoefficient F = -K₀ := by
    dsimp [κ, branchCoefficient, K₀]
    rw [h.coefficient_zero]
    field_simp [hs.crossing, hs.frequency_pos.ne']
    <;> ring
  apply (Asymptotics.isBigO_const_mul_left_iff hκ).mp
  apply ((hVO'.add hproduct).neg_left).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hident] with r hr
  rw [mul_sub, show κ * (2 * branchCoefficient F * r) = -2 * K₀ * r by
    calc
      _ = 2 * (κ * branchCoefficient F) * r := by ring
      _ = _ := by rw [hcoeff]; ring]
  nlinarith

/-- Put the IFT graph, both estimates, and strict one-sided monotonicity
on one common signed interval, respecting any supplied radius cutoff. -/
theorem localBranchAnalysis : LocalBranchAnalysis := by
  intro F ω hs ε δ C P Q hε hδ hC h cutoff hcut hcutδ
  obtain ⟨ψ, hψ, hψ0, hflat, hgraph⟩ := flatImplicitGraph F ω hs ε δ C P Q hε hδ hC h
  have hv := graph_value_bigO hs hε hδ h ψ hψ hψ0 hflat hgraph
  have hd := graph_derivative_bigO hs hε hδ h ψ hψ hψ0 hflat hgraph
  obtain ⟨Mv, hMv, hbv⟩ := hv.exists_pos
  obtain ⟨Md, hMd, hbd⟩ := hd.exists_pos
  let c := branchCoefficient F
  have hc : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hs.cubic) hs.crossing
  have hsmall := (hd.trans_isLittleO
    (Asymptotics.isLittleO_pow_id (by decide : 1 < 2))).def (abs_pos.mpr hc)
  have hslope : ∀ᶠ r in nhds (0 : ℝ), 0 < r → 0 < c * deriv ψ r := by
    filter_upwards [hsmall] with r hr hrpos
    have he : |deriv ψ r - 2 * c * r| ≤ |c| * r := by
      simpa only [Real.norm_eq_abs, abs_of_pos hrpos, c] using hr
    rcases lt_or_gt_of_ne hc with hcn | hcp
    · rw [abs_of_neg hcn] at he
      have hu := (abs_le.mp he).2
      exact mul_pos_of_neg_of_neg hcn (by nlinarith)
    · rw [abs_of_pos hcp] at he
      have hl := (abs_le.mp he).1
      exact mul_pos hcp (by nlinarith)
  obtain ⟨η, hη, hg⟩ := Metric.eventually_nhds_iff.mp hgraph
  let ε₀ := min ε (η / 2)
  have hε₀ : 0 < ε₀ := lt_min hε (half_pos hη)
  have hε₀η : ε₀ < η := (min_le_right _ _).trans_lt (by linarith)
  have hψbound : ∀ᶠ r in nhds (0 : ℝ), |ψ r| < ε₀ := by
    have ht : Tendsto ψ (nhds 0) (nhds 0) := by simpa only [hψ0] using hψ.continuousAt.tendsto
    exact ht.eventually (Metric.eventually_nhds_iff.mpr
      ⟨ε₀, hε₀, fun μ hμ => by simpa [Real.dist_eq] using hμ⟩)
  have hreg := hψ.eventually (by norm_num)
  obtain ⟨ξ, hξ, hb⟩ := Metric.eventually_nhds_iff.mp
    (hbv.bound.and (hbd.bound.and (hslope.and (hψbound.and hreg))))
  let d := min cutoff (min δ (min η ξ))
  have hdpos : 0 < d := lt_min hcut (lt_min hδ (lt_min hη hξ))
  have hdcut : d ≤ cutoff := min_le_left _ _
  have hdδ : d ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hdη : d ≤ η := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdξ : d ≤ ξ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb' (r : ℝ) (hr : |r| < d) :=
    hb (show dist r 0 < ξ by simpa [Real.dist_eq] using hr.trans_le hdξ)
  have hreg' : ContDiffOn ℝ 2 ψ (Ioo (-d) d) := by
    intro r hr
    exact (hb' r (abs_lt.mpr hr)).2.2.2.2.contDiffWithinAt
  have hzeros : ∀ r μ, |r| < d → |μ| < ε₀ → (Q (r, μ) = 0 ↔ μ = ψ r) := by
    intro r μ hr hμ
    apply hg
    simpa [Prod.dist_eq, Real.dist_eq] using
      max_lt (hr.trans_le hdη) (hμ.trans hε₀η)
  have hsl : ∀ r ∈ Ioo 0 d, 0 < c * deriv ψ r := by
    intro r hr
    exact (hb' r (by simpa only [abs_of_pos hr.1] using hr.2)).2.2.1 hr.1
  refine ⟨d, hdpos, ε₀, hε₀, ψ, hdcut, min_le_left _ _, ?_⟩
  refine ⟨hreg', hψ0, hflat, fun r hr => (hb' r hr).2.2.2.1, hzeros, ?_, ?_, hsl, ?_⟩
  · intro r μ hr hrd hμ
    have hfac := (h.bounds (r, μ)
      ⟨by rw [abs_of_pos hr]; exact hrd.trans_le hdδ,
        hμ.trans_le (min_le_left _ _)⟩).1
    rw [← hzeros r μ (by rwa [abs_of_pos hr]) hμ]
    constructor
    · intro hp
      have hh : r * Q (r, μ) = 0 := by nlinarith
      exact (mul_eq_zero.mp hh).resolve_left hr.ne'
    · intro hq
      simpa [hq] using hfac
  · refine ⟨Mv + Md, add_pos hMv hMd, ?_⟩
    intro r hr
    have hv := (hb' r hr).1
    have hd := (hb' r hr).2.1
    simp only [Real.norm_eq_abs, abs_pow, sq_abs] at hv hd
    exact ⟨hv.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)),
      hd.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r))⟩
  · apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) d)
      (continuousOn_const.mul (hreg'.continuousOn.mono (by intro r hr; exact ⟨by linarith [hr.1], hr.2⟩)))
    intro r hr
    rw [interior_Ioo] at hr
    have hdr : DifferentiableAt ℝ ψ r :=
      (hreg'.contDiffAt (Ioo_mem_nhds (by linarith [hr.1]) hr.2)).differentiableAt (by norm_num)
    change 0 < deriv (fun s => c * ψ s) r
    rw [deriv_const_mul c hdr]
    exact hsl r hr

/-- Extend weighted monotonicity to radius zero by the mean-value theorem. -/
theorem weighted_monotone_zero {F : ℝ × ℂ → ℂ} {P Q : ℝ × ℝ → ℝ}
    {d ε₀ : ℝ} {ψ : ℝ → ℝ} (hd : 0 < d) (h : LocalBranch F P Q d ε₀ ψ) :
    StrictMonoOn (fun r => branchCoefficient F * ψ r) (Ico 0 d) := by
  have hsub : Ico 0 d ⊆ Ioo (-d) d := fun r hr => ⟨by linarith [hr.1], hr.2⟩
  apply strictMonoOn_of_deriv_pos (convex_Ico (0 : ℝ) d)
    (continuousOn_const.mul (h.regular.continuousOn.mono hsub))
  intro r hr
  rw [interior_Ico] at hr
  have hdr : DifferentiableAt ℝ ψ r :=
    (h.regular.contDiffAt (Ioo_mem_nhds (by linarith [hr.1]) hr.2)).differentiableAt (by norm_num)
  change 0 < deriv (fun s => branchCoefficient F * ψ s) r
  rw [deriv_const_mul _ hdr]
  exact h.slope r hr

theorem weighted_branch_positive {F : ℝ × ℂ → ℂ} {P Q : ℝ × ℝ → ℝ}
    {d ε₀ : ℝ} {ψ : ℝ → ℝ} (hd : 0 < d) (h : LocalBranch F P Q d ε₀ ψ)
    {r : ℝ} (hr : 0 < r) (hrd : r < d) :
    0 < branchCoefficient F * ψ r := by
  have hh := weighted_monotone_zero hd h ⟨le_rfl, hd⟩ ⟨hr.le, hrd⟩ hr
  simpa [h.zero] using hh

/-- Every still smaller positive radius cutoff contains all sufficiently
small-parameter roots. No inverse branch is assumed in this statement. -/
theorem local_branch_root_shrink {F : ℝ × ℂ → ℂ} {P Q : ℝ × ℝ → ℝ}
    {d ε₀ ε₁ : ℝ} {ψ : ℝ → ℝ} (hd : 0 < d) (hε₁ : 0 < ε₁) (he : ε₁ ≤ ε₀)
    (h : LocalBranch F P Q d ε₀ ψ) (τ : ℝ) (hτ : 0 < τ) (hτd : τ < d) :
    ∃ ν > 0, ν ≤ ε₁ ∧
      ∀ μ r, |μ| < ν → 0 < r → r < d → P (r, μ) = r → r < τ := by
  let c := branchCoefficient F
  have hτp : 0 < c * ψ τ := weighted_branch_positive hd h hτ hτd
  have hψτ : ψ τ ≠ 0 := by intro hz; simp [hz] at hτp
  have hc : c ≠ 0 := by intro hz; simp [hz] at hτp
  let ν := min ε₁ |ψ τ|
  refine ⟨ν, lt_min hε₁ (abs_pos.mpr hψτ), min_le_left _ _, ?_⟩
  intro μ r hμ hr hrd hp
  have hμ₀ : |μ| < ε₀ := (hμ.trans_le (min_le_left _ _)).trans_le he
  have hroot := (h.fixed_points r μ hr hrd hμ₀).mp hp
  have hrp : 0 < c * ψ r := weighted_branch_positive hd h hr hrd
  by_contra hn
  have hm : c * ψ τ ≤ c * ψ r :=
    (weighted_monotone_zero hd h).monotoneOn ⟨hτ.le, hτd⟩ ⟨hr.le, hrd⟩ (le_of_not_gt hn)
  have hτabs : |c| * |ψ τ| = c * ψ τ := by rw [← abs_mul, abs_of_pos hτp]
  have hrabs : |c| * |ψ r| = c * ψ r := by rw [← abs_mul, abs_of_pos hrp]
  have habs : |ψ τ| ≤ |ψ r| := by nlinarith [abs_pos.mpr hc]
  have hμτ : |μ| < |ψ τ| := hμ.trans_le (min_le_right _ _)
  rw [hroot] at hμτ
  exact (not_lt_of_ge habs) hμτ

/-- Intermediate-value and injectivity argument on the positive half branch.
The parameter side is first expressed by its leading scalar coefficient. -/
theorem local_branch_root_side {F : ℝ × ℂ → ℂ} {P Q : ℝ × ℝ → ℝ}
    {d ε₀ : ℝ} {ψ : ℝ → ℝ} (hd : 0 < d) (hε₀ : 0 < ε₀)
    (h : LocalBranch F P Q d ε₀ ψ) :
    ∃ ε₁ > 0, ε₁ ≤ ε₀ ∧ ∀ μ, |μ| < ε₁ →
      ((∃! r, 0 < r ∧ r < d ∧ P (r, μ) = r) ↔ 0 < branchCoefficient F * μ) ∧
      ((¬ 0 < branchCoefficient F * μ) →
        ∀ r, 0 < r → r < d → P (r, μ) ≠ r) := by
  let c := branchCoefficient F
  let t := d / 2
  have ht : 0 < t := half_pos hd
  have htd : t < d := by dsimp [t]; linarith
  have htp : 0 < c * ψ t := weighted_branch_positive hd h ht htd
  have hc : c ≠ 0 := by intro hz; simp [hz] at htp
  have hψt : ψ t ≠ 0 := by intro hz; simp [hz] at htp
  let ε₁ := min ε₀ |ψ t|
  refine ⟨ε₁, lt_min hε₀ (abs_pos.mpr hψt), min_le_left _ _, ?_⟩
  intro μ hμ
  have hμ₀ : |μ| < ε₀ := hμ.trans_le (min_le_left _ _)
  have hrootpos : ∀ r, 0 < r → r < d → P (r, μ) = r → 0 < c * μ := by
    intro r hr hrd hp
    rw [(h.fixed_points r μ hr hrd hμ₀).mp hp]
    exact weighted_branch_positive hd h hr hrd
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨r, hr, _⟩
    exact hrootpos r hr.1 hr.2.1 hr.2.2
  · intro hμpos
    have habs : |c * μ| < |c * ψ t| := by
      rw [abs_mul, abs_mul]
      exact mul_lt_mul_of_pos_left (hμ.trans_le (min_le_right _ _)) (abs_pos.mpr hc)
    rw [abs_of_pos hμpos, abs_of_pos htp] at habs
    have hg : ContinuousOn (fun r => c * ψ r) (Icc 0 t) :=
      continuousOn_const.mul (h.regular.continuousOn.mono
        (fun r hr => ⟨by linarith [hr.1], hr.2.trans_lt htd⟩))
    obtain ⟨r, hr, heq⟩ := intermediate_value_Icc ht.le hg
      (show c * μ ∈ Icc (c * ψ 0) (c * ψ t) by simpa [h.zero] using ⟨hμpos.le, habs.le⟩)
    change c * ψ r = c * μ at heq
    have hψr : ψ r = μ := (mul_left_cancel₀ hc) heq
    have hrpos : 0 < r := by
      by_contra hn
      have hz : r = 0 := le_antisymm (le_of_not_gt hn) hr.1
      rw [hz, h.zero, mul_zero] at heq
      linarith
    have hrd : r < d := hr.2.trans_lt htd
    refine ⟨r, ⟨hrpos, hrd, (h.fixed_points r μ hrpos hrd hμ₀).mpr hψr.symm⟩, ?_⟩
    intro s hs
    have hψs := (h.fixed_points s μ hs.1 hs.2.1 hμ₀).mp hs.2.2
    apply (weighted_monotone_zero hd h).injOn ⟨hs.1.le, hs.2.1⟩ ⟨hrpos.le, hrd⟩
    change c * ψ s = c * ψ r
    rw [← hψs, hψr]
  · intro hn r hr hrd hp
    exact hn (hrootpos r hr hrd hp)

/-- Transversality identifies the geometric parameter side with the scalar
branch side, including the distinguished parameter itself. -/
theorem parameter_side_eventually {F : ℝ × ℂ → ℂ} {ω : ℝ}
    (hs : SourceHypotheses F ω) :
    ∀ᶠ μ in nhds (0 : ℝ),
      (spectralReal F μ * firstLyapunovCoefficient F < 0 ↔
        0 < branchCoefficient F * μ) := by
  obtain ⟨ha0, hb0, η, hη, ρ, hρ, C, hC, hc, hR, hreg⟩ :=
    CubicNormalForm.normalForm F ω hs.regularity hs.frequency_pos hs.eigenvalue hs.equilibrium
  have hA := (hreg 0 (by simpa using hη)).2.1.differentiableAt (by norm_num)
  let D := deriv (spectralReal F) 0
  let s : ℝ → ℝ := Function.update (fun μ => spectralReal F μ / μ) 0 D
  have hD : D ≠ 0 := hs.crossing
  have hscont : ContinuousAt s 0 := by
    simpa only [ha0, sub_zero] using hA.hasDerivAt.continuousAt_div
  have hmcont : ContinuousAt (fun μ => s μ / D) 0 := hscont.div_const D
  have hm : ∀ᶠ μ in nhds (0 : ℝ), 0 < s μ / D :=
    hmcont.eventually (lt_mem_nhds (by simp [s, hD]))
  filter_upwards [hm] with μ hμ
  have hid : spectralReal F μ = (s μ / D * D) * μ := by
    rw [div_mul_cancel₀ _ hD]
    by_cases hz : μ = 0
    · simp [hz, ha0]
    · simp [s, Function.update_of_ne hz, div_mul_cancel₀ _ hz]
  have hfactor : spectralReal F μ * firstLyapunovCoefficient F =
      -(D ^ 2 * (s μ / D)) * (branchCoefficient F * μ) := by
    rw [hid]
    dsimp [branchCoefficient, D]
    field_simp [hs.crossing]
    <;> ring
  have hneg : -(D ^ 2 * (s μ / D)) < 0 := neg_neg_of_pos (mul_pos (sq_pos_of_ne_zero hD) hμ)
  rw [hfactor, mul_neg_iff]
  simp [hneg, not_lt_of_gt hneg]

/-- A scalar algebra estimate used in inverting the quadratic amplitude law. -/
theorem inverse_quadratic_error (c M ζ r μ : ℝ) (hc : c ≠ 0) (hM : 0 < M)
    (hζ : 0 < ζ) (hr : 0 < r)
    (herror : |μ - c * r ^ 2| ≤ M * r ^ 3)
    (hrsmall : M * r ≤ |c| / 2)
    (hrζ : M * r ≤ ζ * |c| ^ 2 / 2) :
    |r ^ 2 - μ / c| ≤ ζ * |μ| := by
  have hcn := abs_pos.mpr hc
  have htriangle : |c| * r ^ 2 - |μ| ≤ M * r ^ 3 := by
    calc
      _ = |c * r ^ 2| - |μ| := by rw [abs_mul, abs_pow, sq_abs]
      _ ≤ |c * r ^ 2 - μ| := abs_sub_abs_le_abs_sub _ _
      _ = |μ - c * r ^ 2| := abs_sub_comm _ _
      _ ≤ _ := herror
  have hlow : |c| / 2 * r ^ 2 ≤ |μ| := by
    nlinarith [mul_le_mul_of_nonneg_right hrsmall (sq_nonneg r)]
  have hscaled : |c| * |r ^ 2 - μ / c| = |μ - c * r ^ 2| := by
    rw [← abs_mul, abs_sub_comm μ (c * r ^ 2)]
    congr 1
    field_simp
    <;> ring
  have hgoal : |c| * |r ^ 2 - μ / c| ≤ |c| * (ζ * |μ|) := by
    rw [hscaled]
    apply herror.trans
    nlinarith [mul_le_mul_of_nonneg_right hrζ (sq_nonneg r),
      mul_le_mul_of_nonneg_left hlow (mul_nonneg hζ.le hcn.le)]
  exact (mul_le_mul_iff_right₀ hcn).mp hgoal

/-- Uniform inverse little-o along every local positive fixed radius. -/
theorem local_branch_inverse_amplitude {F : ℝ × ℂ → ℂ} {P Q : ℝ × ℝ → ℝ}
    {d ε₀ ε₁ : ℝ} {ψ : ℝ → ℝ} (hd : 0 < d) (hε₁ : 0 < ε₁) (he : ε₁ ≤ ε₀)
    (hc : branchCoefficient F ≠ 0) (h : LocalBranch F P Q d ε₀ ψ) :
    ∀ ζ > 0, ∃ ν > 0, ν ≤ ε₁ ∧
      ∀ μ r, |μ| < ν → 0 < r → r < d → P (r, μ) = r →
        |r ^ 2 - μ / branchCoefficient F| ≤ ζ * |μ| := by
  intro ζ hζ
  obtain ⟨M, hM, hest⟩ := h.estimates
  let c := branchCoefficient F
  let τ := min (d / 2) (min (|c| / (2 * M)) (ζ * |c| ^ 2 / (2 * M)))
  have hτ : 0 < τ := lt_min (half_pos hd) (lt_min (by positivity) (by positivity))
  have hτd : τ < d := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨ν, hν, hνε, hshrink⟩ := local_branch_root_shrink hd hε₁ he h τ hτ hτd
  refine ⟨ν, hν, hνε, ?_⟩
  intro μ r hμ hr hrd hp
  have hrτ := hshrink μ r hμ hr hrd hp
  have hroot := (h.fixed_points r μ hr hrd ((hμ.trans_le hνε).trans_le he)).mp hp
  have herr : |μ - c * r ^ 2| ≤ M * r ^ 3 := by
    rw [hroot]
    simpa only [abs_of_pos hr] using (hest r (by simpa only [abs_of_pos hr] using hrd)).1
  have hs : M * r ≤ |c| / 2 := by
    have hh := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hM)).mp
      (hrτ.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hz : M * r ≤ ζ * |c| ^ 2 / 2 := by
    have hh := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hM)).mp
      (hrτ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  exact inverse_quadratic_error c M ζ r μ hc hM hζ hr herr hs hz

/-- Complete scalar branch theorem for every actual upstream return map. -/
theorem scalarBranchAnalysis : ScalarBranchAnalysis := by
  intro F ω hs ε δ C P Q hε hδ hC h cutoff hcut hcutδ
  obtain ⟨d, hd, ε₀, hε₀, ψ, hdcut, he₀, hlocal⟩ :=
    localBranchAnalysis F ω hs ε δ C P Q hε hδ hC h cutoff hcut hcutδ
  obtain ⟨εb, hεb, heb, hroots⟩ := local_branch_root_side hd hε₀ hlocal
  obtain ⟨η, hη, hside⟩ := Metric.eventually_nhds_iff.mp (parameter_side_eventually hs)
  let ε₁ := min εb η
  have hε₁ : 0 < ε₁ := lt_min hεb hη
  have he₁ : ε₁ ≤ ε₀ := (min_le_left _ _).trans heb
  have hc : branchCoefficient F ≠ 0 := div_ne_zero (neg_ne_zero.mpr hs.cubic) hs.crossing
  refine ⟨d, hd, ε₀, hε₀, ε₁, hε₁, ψ, hdcut, he₀, he₁, hlocal, ?_, ?_, ?_⟩
  · intro μ hμ
    have hh := hroots μ (hμ.trans_le (min_le_left _ _))
    have hsμ := hside (show dist μ 0 < η by simpa [Real.dist_eq] using hμ.trans_le (min_le_right _ _))
    exact ⟨hh.1.trans hsμ.symm, fun hn => hh.2 (fun hp => hn (hsμ.mpr hp))⟩
  · intro ζ hζ
    obtain ⟨ν, hν, hνε, hamp⟩ := local_branch_inverse_amplitude hd hε₁ he₁ hc hlocal ζ hζ
    refine ⟨ν, hν, hνε, ?_⟩
    intro μ r hμ hr hrd hp
    have hh := hamp μ r hμ hr hrd hp
    have hid : r ^ 2 + deriv (spectralReal F) 0 / firstLyapunovCoefficient F * μ =
        r ^ 2 - μ / branchCoefficient F := by
      dsimp [branchCoefficient]
      field_simp [hs.cubic, hs.crossing]
      <;> ring
    rwa [hid]
  · exact local_branch_root_shrink hd hε₁ he₁ hlocal

end D13Unified.Ch16.HopfScalarBranchAnalysis
