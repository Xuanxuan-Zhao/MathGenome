import MathGenome.Internal.MultivariableAnalysis.D04.C03.LineRestrictions
import MathGenome.Internal.MultivariableAnalysis.D04.C02.SegmentFTC
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.TaylorIntegral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.Integral

noncomputable section
open Set
open scoped BigOperators
namespace D04
open SingleVariableAnalysis.Riemann

/-- Continuity of a fixed diagonal evaluation on the entire segment. -/
theorem higherDifferential_line_continuous {d m : ℕ} (k j : ℕ)
    (U : Set (E d)) (f : E d → E m) (a h : E d)
    (hU : IsOpen U) (hf : CrOn k U f)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) (hj : j ≤ k) :
    ContinuousOn (fun t : ℝ => differentialDiagonal (higherDifferential j f (a+t•h)) h)
      (Icc 0 1) := by
  have hc := (crOn_iff_contDiffOn k U f hU).mp hf
  intro t ht
  have hfAt := hc.contDiffAt (hU.mem_nhds (hseg t ht))
  have htensor : ContinuousAt (iteratedFDeriv ℝ j f) (a+t•h) :=
    ((hfAt.iteratedFDeriv_right (i := j) (m := 0) (by simpa using hj)).continuousAt)
  exact ((htensor.comp (x := t) (show ContinuousAt (fun s : ℝ => a+s•h) t from by fun_prop)).eval_const (fun _ => h)).continuousWithinAt

/-- The affine chain rule followed by fixed tensor evaluation. -/
theorem higherDifferential_line_derivative {d m : ℕ} (k j : ℕ)
    (U : Set (E d)) (f : E d → E m) (a h : E d)
    (hU : IsOpen U) (hf : CrOn k U f)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) (hj : j < k)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => differentialDiagonal (higherDifferential j f (a+s•h)) h)
      (differentialDiagonal (higherDifferential (j+1) f (a+t•h)) h) t := by
  have hc := (crOn_iff_contDiffOn k U f hU).mp hf
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) (a+t•h) :=
    (hc.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt_iteratedFDeriv (by exact_mod_cast hj)
  have hl : HasDerivAt (fun s : ℝ => a+s•h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add a
  have hh := (hd.hasFDerivAt.continuousMultilinear_apply_const (fun _ => h)).comp_hasDerivAt t hl
  convert hh using 1
  · rfl
  · rfl

/-- Coordinatewise scalar Taylor, with the actual higher differential as jet. -/
theorem taylor_integral : Specs.D04.C03.TaylorIntegral.taylor_integralType := by
  intro d m n U f a h hU hf hseg
  let v : ℝ → E m := fun t =>
    (1-t)^n • differentialDiagonal (higherDifferential (n+1) f (a+t•h)) h
  have hc : ContinuousOn v (Icc 0 1) :=
    ((continuous_const.sub continuous_id).pow n).continuousOn.smul
      (higherDifferential_line_continuous (n+1) (n+1) U f a h hU hf hseg le_rfl)
  have hv := continuous_vector_riemann_integrable v (by norm_num : (0 : ℝ) ≤ 1) hc
  refine ⟨hv, ?_⟩
  ext i
  let D : ℕ → ℝ → ℝ := fun j t => differentialDiagonal (higherDifferential j f (a+t•h)) h i
  have hD : SingleVariableAnalysis.ClosedDerivativeFamily (n+1)
      (fun t : ℝ => f (a+t•h) i) 0 1 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro t _
      rfl
    · intro j hj
      exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).continuous.comp_continuousOn
        (higherDifferential_line_continuous (n+1) j U f a h hU hf hseg hj)
    · intro j hj t ht
      exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).hasFDerivAt.comp_hasDerivAt t
        (higherDifferential_line_derivative (n+1) j U f a h hU hf hseg hj t ht)).hasDerivWithinAt
  obtain ⟨hi, he⟩ := real_integral_remainder (fun t : ℝ => f (a+t•h) i)
    n 0 1 D hD 0 (by constructor <;> norm_num) 1 (by constructor <;> norm_num)
  have hs : (∑ k ∈ Finset.range (n+1), D k 0 / (k.factorial : ℝ) * (1-0)^k) =
      taylorPolynomial n f a h i := by
    simp [D, taylorPolynomial, Specs.D04.C03.HigherInterfaces.Model.taylorPolynomial,
      differentialDiagonal, div_eq_mul_inv, mul_comm]
  rw [hs] at he
  change f (a+h) i = taylorPolynomial n f a h i + (n.factorial : ℝ)⁻¹ *
    realIntegral (fun t => v t i) (hv i)
  have he' : f (a+h) i - taylorPolynomial n f a h i =
      (n.factorial : ℝ)⁻¹ * realIntegral (fun t => v t i) (hv i) := by
    simpa [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegralValue, D, v] using he
  linarith


/-- The alternative remainder is the first identity with the polynomial subtracted. -/
theorem taylor_remainder_integral : Specs.D04.C03.TaylorIntegral.taylor_remainder_integralType := by
  intro d m n U f a h hU hf hseg
  obtain ⟨hv, he⟩ := taylor_integral n U f a h hU hf hseg
  refine ⟨hv, ?_⟩
  change f (a+h) - taylorPolynomial n f a h = _
  rw [he, add_sub_cancel_left]

private theorem riemann_weighted_constant (n : ℕ) (c : ℝ)
    (hv : RealIntegrable (fun t : ℝ => (1-t)^n*c) 0 1) :
    realIntegral _ hv = c / (n+1 : ℝ) := by
  let F : ℝ → ℝ := fun t => -(c / (n+1 : ℝ)) * (1-t)^(n+1)
  have hd (t : ℝ) : HasDerivAt F ((1-t)^n*c) t := by
    have hh := (((hasDerivAt_id t).const_sub 1).pow (n+1)).const_mul (-(c / (n+1 : ℝ)))
    simp only [id_eq, Nat.add_sub_cancel] at hh
    convert hh using 1
    have hn : (n+1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have he := real_ftc_second F (fun t : ℝ => (1-t)^n*c) 0 1 (by norm_num)
    (by dsimp [F]; fun_prop) (fun t _ => hd t) hv
  simpa [F] using he

private theorem real_integral_sub {v w : ℝ → ℝ}
    (hv : RealIntegrable v 0 1) (hw : RealIntegrable w 0 1)
    (hs : RealIntegrable (fun t => v t - w t) 0 1) :
    realIntegral _ hs = realIntegral _ hv - realIntegral _ hw := by
  obtain ⟨hn, hen⟩ := real_mul_value hw (-1)
  obtain ⟨ha, hea⟩ := real_add_value hv hn
  simpa only [neg_one_mul, sub_eq_add_neg] using hea.trans (congrArg (fun z => realIntegral _ hv + z) hen)

private theorem realIntegral_congr {v w : ℝ → ℝ} {a b : ℝ}
    (hv : RealIntegrable v a b) (hw : RealIntegrable w a b) (he : v = w) :
    realIntegral v hv = realIntegral w hw := by
  subst w
  rfl

/-- Removing the constant top differential gives the degree-(n+1) remainder. -/
theorem taylor_remainder_integral_sub :
    Specs.D04.C03.TaylorIntegral.taylor_remainder_integral_subType := by
  intro d m n U f a h hU hf hseg
  let v : ℝ → E m := fun t =>
    (1-t)^n • differentialDiagonal (higherDifferential (n+1) f (a+t•h)) h
  let w : ℝ → E m := fun t =>
    (1-t)^n • differentialDiagonal (higherDifferential (n+1) f a) h
  let z : ℝ → E m := fun t => (1-t)^n • differentialDiagonal
    (higherDifferential (n+1) f (a+t•h) - higherDifferential (n+1) f a) h
  have hdiag := higherDifferential_line_continuous (n+1) (n+1) U f a h hU hf hseg le_rfl
  have hwc : ContinuousOn w (Icc 0 1) := by dsimp [w]; fun_prop
  have hzc : ContinuousOn z (Icc 0 1) := by
    change ContinuousOn (fun t : ℝ => (1-t)^n •
      (differentialDiagonal (higherDifferential (n+1) f (a+t•h)) h -
        differentialDiagonal (higherDifferential (n+1) f a) h)) (Icc 0 1)
    exact ((continuous_const.sub continuous_id).pow n).continuousOn.smul (hdiag.sub continuousOn_const)
  obtain ⟨hv, he⟩ := taylor_integral n U f a h hU hf hseg
  have hw := continuous_vector_riemann_integrable w (by norm_num : (0 : ℝ) ≤ 1) hwc
  have hz := continuous_vector_riemann_integrable z (by norm_num : (0 : ℝ) ≤ 1) hzc
  refine ⟨hz, ?_⟩
  have hpoly : taylorPolynomial (n+1) f a h = taylorPolynomial n f a h +
      ((n+1).factorial : ℝ)⁻¹ • differentialDiagonal (higherDifferential (n+1) f a) h := by
    exact Finset.sum_range_succ _ _
  ext i
  have hs : realIntegral (fun t => z t i) (hz i) = realIntegral (fun t => v t i) (hv i) -
      differentialDiagonal (higherDifferential (n+1) f a) h i / (n+1 : ℝ) := by
    have hzi : (fun t => z t i) = (fun t => v t i - w t i) := by
      funext t
      change ((1-t)^n • (differentialDiagonal (higherDifferential (n+1) f (a+t•h)) h -
        differentialDiagonal (higherDifferential (n+1) f a) h)) i =
        ((1-t)^n • differentialDiagonal (higherDifferential (n+1) f (a+t•h)) h) i -
        ((1-t)^n • differentialDiagonal (higherDifferential (n+1) f a) h) i
      exact congrArg (fun x : E m => x i) (smul_sub ((1-t)^n) _ _)
    have hzs : RealIntegrable (fun t => v t i - w t i) 0 1 := by
      rw [← hzi]
      exact hz i
    have hh := real_integral_sub (hv i) (hw i) hzs
    have hwval := riemann_weighted_constant n
      (differentialDiagonal (higherDifferential (n+1) f a) h i) (hw i)
    change realIntegral (fun t => w t i) (hw i) = _ at hwval
    rw [hwval] at hh
    exact (realIntegral_congr (hz i) hzs hzi).trans hh
  change f (a+h) i - taylorPolynomial (n+1) f a h i =
    (n.factorial : ℝ)⁻¹ * realIntegral (fun t => z t i) (hz i)
  rw [hs]
  have hei := congrArg (fun x : E m => x i) he
  have hpi := congrArg (fun x : E m => x i) hpoly
  change f (a+h) i = taylorPolynomial n f a h i +
    (n.factorial : ℝ)⁻¹ * realIntegral (fun t => v t i) (hv i) at hei
  change taylorPolynomial (n+1) f a h i = taylorPolynomial n f a h i +
    ((n+1).factorial : ℝ)⁻¹ * differentialDiagonal (higherDifferential (n+1) f a) h i at hpi
  rw [hei, hpi, Nat.factorial_succ, Nat.cast_mul]
  simp only [Nat.cast_add, Nat.cast_one, mul_inv_rev]
  ring

end D04
