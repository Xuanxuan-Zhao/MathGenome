import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.CircleMultiplicity
import MathGenome.Internal.MultivariableAnalysis.D04.C09.GradientIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C02.QuotientRule
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The circle is differentiated componentwise. Its speed and angular work
integrands are constant on every smooth piece. The shared proper Riemann FTC
and polygonal length theorem then evaluate their integrals. A closed turn
contradicts the shared endpoint theorem for any proposed global potential. -/
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace D04.C09
open SingleVariableAnalysis.Riemann
namespace CircleMultiplicity
open Specs.D04.C09.CircleMultiplicity.Model

abbrev circle := Specs.D04.C09.CircleMultiplicity.Model.circle
abbrev circleVelocity := Specs.D04.C09.CircleMultiplicity.Model.circleVelocity
abbrev circlePath := Specs.D04.C09.CircleMultiplicity.Model.circlePath
abbrev puncturedPlane := Specs.D04.C09.CircleMultiplicity.Model.puncturedPlane
abbrev angularField := Specs.D04.C09.CircleMultiplicity.Model.angularField

@[simp] lemma circle_zero (m : ℤ) (t : ℝ) : circle m t 0 = Real.cos ((m : ℝ)*t) := rfl
@[simp] lemma circle_one (m : ℤ) (t : ℝ) : circle m t 1 = Real.sin ((m : ℝ)*t) := rfl
@[simp] lemma velocity_zero (m : ℤ) (t : ℝ) : circleVelocity m t 0 = -(m : ℝ)*Real.sin ((m : ℝ)*t) := rfl
@[simp] lemma velocity_one (m : ℤ) (t : ℝ) : circleVelocity m t 1 = (m : ℝ)*Real.cos ((m : ℝ)*t) := rfl

lemma circle_derivative (m : ℤ) (t : ℝ) :
    HasDerivAt (circle m) (circleVelocity m t) t := by
  have hc := ((hasDerivAt_id t).const_mul (m : ℝ)).cos
  have hs := ((hasDerivAt_id t).const_mul (m : ℝ)).sin
  have h : HasDerivAt
      (fun s : ℝ => ![Real.cos ((m : ℝ)*s), Real.sin ((m : ℝ)*s)])
      ![-(m : ℝ)*Real.sin ((m : ℝ)*t), (m : ℝ)*Real.cos ((m : ℝ)*t)] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [mul_comm, neg_mul] using hc
    · simpa [mul_comm] using hs
  exact (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t h

lemma circle_speed (m : ℤ) (t : ℝ) : ‖circleVelocity m t‖ = |(m : ℝ)| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, velocity_zero, velocity_one, Real.norm_eq_abs, sq_abs]
  have h := Real.sin_sq_add_cos_sq ((m : ℝ)*t)
  rw [show (-(m : ℝ)*Real.sin ((m : ℝ)*t))^2 +
    ((m : ℝ)*Real.cos ((m : ℝ)*t))^2 = (m : ℝ)^2 by nlinarith [sq_nonneg (m : ℝ)]]
  exact Real.sqrt_sq_eq_abs _

lemma circle_norm (m : ℤ) (t : ℝ) : ‖circle m t‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, circle_zero, circle_one, Real.norm_eq_abs, sq_abs]
  rw [Real.cos_sq_add_sin_sq, Real.sqrt_one]

lemma circle_closed (m : ℤ) : circle m 0 = circle m (2 * Real.pi) := by
  ext i
  fin_cases i
  · change Real.cos ((m : ℝ)*0) = Real.cos ((m : ℝ)*(2*Real.pi))
    simp only [mul_zero, Real.cos_zero, Real.cos_int_mul_two_pi]
  · change Real.sin ((m : ℝ)*0) = Real.sin ((m : ℝ)*(2*Real.pi))
    simp only [mul_zero, Real.sin_zero]
    have he : (m : ℝ)*(2*Real.pi) = ((2*m : ℤ) : ℝ)*Real.pi := by push_cast; ring
    rw [he, Real.sin_int_mul_pi]

lemma velocity_continuous (m : ℤ) : Continuous (circleVelocity m) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

lemma circle_piecewiseC1 (m : ℤ) : PiecewiseC1 (circlePath m) := by
  obtain ⟨P⟩ := partition_exists (circlePath m).ordered
  refine ⟨⟨P, fun _ => circleVelocity m, ?_⟩⟩
  intro i
  exact ⟨(velocity_continuous m).continuousOn,
    fun t _ => (circle_derivative m t).hasDerivWithinAt⟩

lemma velocity_agrees (m : ℤ) (d : PiecewiseC1Data (circlePath m))
    (i : Fin d.partition.n) {t : ℝ} (ht : t ∈ cell d.partition i) :
    d.velocity i t = circleVelocity m t := by
  have hu := uniqueDiffOn_Icc (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))) t ht
  exact ((d.smooth i).2 t ht).derivWithin hu |>.symm.trans
    ((circle_derivative m t).hasDerivWithinAt.derivWithin hu)

lemma constant_riemann_integral {a b : ℝ} (hab : a ≤ b) (c : ℝ)
    (h : RealIntegrable (fun _ => c) a b) :
    realIntegral (fun _ => c) h = (b-a)*c := by
  have he := real_ftc_second (fun t => c*t) (fun _ => c) a b hab
    (by fun_prop) (fun t _ => by simpa using (hasDerivAt_id t).const_mul c) h
  exact he.trans (by ring)

/-- Evaluate a proper line integral whose integrand is constant on every piece. -/
lemma pieceIntegral_constant {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (H : E n → E n → ℝ) (c : ℝ)
    (heq : ∀ i, ∀ t ∈ cell d.partition i, H (γ t) (d.velocity i t) = c) :
    ∃ h : PieceIntegrable d H, pieceIntegral d H h = (b-a)*c := by
  have hc (i : Fin d.partition.n) := riemann_integrable_of_continuousOn
    (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le
    (f := fun _ => c) continuousOn_const
  choose h hv using (fun i => riemann_congr (hc i) (fun t ht => (heq i t ht).symm))
  refine ⟨h, ?_⟩
  change (∑ i, realIntegral _ (h i)) = _
  simp_rw [hv, constant_riemann_integral
    (d.partition.strictMono (Fin.castSucc_lt_succ)).le]
  rw [← Finset.sum_mul]
  congr 1
  simpa only [d.partition.first, d.partition.last] using
    sum_cell_differences d.partition.point

lemma circle_scalar_integral (m : ℤ) (d : PiecewiseC1Data (circlePath m)) :
    ∃ h : ScalarIntegrable d (fun _ => 1),
      scalarLineIntegral d (fun _ => 1) h = 2*Real.pi*|(m : ℝ)| := by
  obtain ⟨h, he⟩ := pieceIntegral_constant d (fun _ v => 1 * ‖v‖) |(m : ℝ)|
    (fun i t ht => by rw [velocity_agrees m d i ht, circle_speed, one_mul])
  exact ⟨h, he.trans (by ring)⟩

lemma circle_length (m : ℤ) :
    length (circle m) 0 (2*Real.pi) = ENNReal.ofReal (2*Real.pi*|(m : ℝ)|) := by
  obtain ⟨d⟩ := circle_piecewiseC1 m
  obtain ⟨h, he⟩ := circle_scalar_integral m d
  have hs := (length_speed_integral d (speed_integrable d)).1
  have heq : piecewiseSpeedIntegral d (speed_integrable d) =
      scalarLineIntegral d (fun _ => 1) h := by
    change (∑ i, realIntegral (fun t => ‖d.velocity i t‖) _) =
      ∑ i, realIntegral (fun t => 1 * ‖d.velocity i t‖) _
    apply Finset.sum_congr rfl
    intro i _
    simp only [one_mul]
  rw [heq, he] at hs
  exact hs

lemma angularField_circle (m : ℤ) (t : ℝ) :
    circle m t ∈ puncturedPlane ∧
    inner ℝ (angularField (circle m t)) (circleVelocity m t) = (m : ℝ) := by
  constructor
  · intro hz
    have hn := circle_norm m t
    rw [hz, norm_zero] at hn
    norm_num at hn
  · rw [D04.inner_coordinates]
    simp only [Fin.sum_univ_two, angularField,
      Specs.D04.C09.CircleMultiplicity.Model.angularField, 
      Matrix.cons_val_zero, Matrix.cons_val_one, circle_zero, circle_one,
      velocity_zero, velocity_one, Real.cos_sq_add_sin_sq, div_one]
    calc
      _ = (m : ℝ)*(Real.sin ((m : ℝ)*t)^2 + Real.cos ((m : ℝ)*t)^2) := by ring
      _ = (m : ℝ) := by rw [Real.sin_sq_add_cos_sq, mul_one]

lemma circle_work_integral (m : ℤ) (d : PiecewiseC1Data (circlePath m)) :
    ∃ h : WorkIntegrable d angularField,
      workLineIntegral d angularField h = 2*Real.pi*(m : ℝ) := by
  obtain ⟨h, he⟩ := pieceIntegral_constant d (fun x v => inner ℝ (angularField x) v) (m : ℝ)
    (fun i t ht => by rw [velocity_agrees m d i ht]; exact (angularField_circle m t).2)
  exact ⟨h, he.trans (by ring)⟩


lemma puncturedPlane_open : IsOpen puncturedPlane := isOpen_ne

lemma denominator_ne_zero (x : E 2) (hx : x ∈ puncturedPlane) :
    (x 0)^2 + (x 1)^2 ≠ 0 := by
  intro h
  apply hx
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 1)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0)]
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma coordinate_contDiff (i : Fin 2) : ContDiff ℝ 1 (fun x : E 2 => x i) :=
  contDiff_piLp_apply 2

lemma angularField_C1 : CrOn 1 puncturedPlane angularField := by
  apply (crOn_iff_contDiffOn 1 puncturedPlane angularField puncturedPlane_open).mpr
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_euclidean.mpr
  have h0 := (coordinate_contDiff 0).contDiffAt (x := x)
  have h1 := (coordinate_contDiff 1).contDiffAt (x := x)
  have hq := (h0.pow 2).add (h1.pow 2)
  intro i
  fin_cases i
  · exact h1.neg.div hq (denominator_ne_zero x hx)
  · exact h0.div hq (denominator_ne_zero x hx)

lemma angularField_cross_partials (x : E 2) (hx : x ∈ puncturedPlane) :
    scalarPartialDerivative (fun y => angularField y 1) x 0 =
      scalarPartialDerivative (fun y => angularField y 0) x 1 := by
  let p0 : E 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  let p1 : E 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have h0 := p0.hasFDerivAt (x := x)
  have h1 := p1.hasFDerivAt (x := x)
  have hq := (h0.pow 2).add (h1.pow 2)
  have hi := (hasFDerivAt_inv (denominator_ne_zero x hx)).comp x hq
  have hF1 := hi.fun_smul h0
  have hF0 := hi.fun_smul h1.neg
  have hA1 := (hasTotalDerivative_iff_hasFDerivAt puncturedPlane
    (fun y => angularField y 1) _ x puncturedPlane_open hx).mpr (by simpa [angularField, Specs.D04.C09.CircleMultiplicity.Model.angularField,
      div_eq_mul_inv, smul_eq_mul, mul_comm, p0, p1] using hF1)
  have hA0 := (hasTotalDerivative_iff_hasFDerivAt puncturedPlane
    (fun y => angularField y 0) _ x puncturedPlane_open hx).mpr (by simpa [angularField, Specs.D04.C09.CircleMultiplicity.Model.angularField,
      div_eq_mul_inv, smul_eq_mul, mul_comm, p0, p1] using hF0)
  rw [scalarPartialDerivative_eq puncturedPlane _ x _ hA1,
    scalarPartialDerivative_eq puncturedPlane _ x _ hA0]
  simp [D04.standardBasis_apply, PiLp.proj_apply]
  field_simp
  ring


/-- Every unit vector has a representative angle in the closed full turn. -/
lemma unit_circle_angle (x : E 2) (hx : ‖x‖ = 1) :
    ∃ θ ∈ Icc (0 : ℝ) (2*Real.pi), Real.cos θ = x 0 ∧ Real.sin θ = x 1 := by
  have hsq : (x 0)^2 + (x 1)^2 = 1 := by
    simpa [Fin.sum_univ_two, hx] using (EuclideanSpace.real_norm_sq_eq x).symm
  have hx0 : -1 ≤ x 0 ∧ x 0 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (x 1)]
  have hc := Real.cos_arccos hx0.1 hx0.2
  have hs : Real.sin (Real.arccos (x 0)) = |x 1| := by
    rw [Real.sin_arccos, show 1 - (x 0)^2 = (x 1)^2 by linarith,
      Real.sqrt_sq_eq_abs]
  by_cases hy : 0 ≤ x 1
  · exact ⟨Real.arccos (x 0), ⟨Real.arccos_nonneg _,
      (Real.arccos_le_pi _).trans (by linarith [Real.pi_pos])⟩,
      hc, hs.trans (abs_of_nonneg hy)⟩
  · refine ⟨2*Real.pi - Real.arccos (x 0), ⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [Real.arccos_le_pi (x 0), Real.pi_pos]
    · linarith [Real.arccos_nonneg (x 0)]
    · simpa only [Real.cos_two_pi_sub] using hc
    · rw [Real.sin_two_pi_sub, hs, abs_of_neg (lt_of_not_ge hy), neg_neg]

lemma circle_trace (m : ℤ) (hm : m ≠ 0) :
    trace (circlePath m) = {x : E 2 | ‖x‖ = 1} := by
  ext x
  constructor
  · rintro ⟨t, _, rfl⟩
    exact circle_norm m t
  · intro hx
    obtain ⟨θ, hθ, hc, hs⟩ := unit_circle_angle x hx
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rcases lt_or_gt_of_ne hm0 with hmneg | hmpos
    · have hmle : (m : ℝ) ≤ -1 := by
        have hmz : m ≤ -1 := by
          have : m < 0 := by exact_mod_cast hmneg
          omega
        exact_mod_cast hmz
      refine ⟨(θ-2*Real.pi)/(m : ℝ), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg_of_nonpos (by linarith [hθ.2]) hmneg.le
      · apply (div_le_iff_of_neg hmneg).mpr
        nlinarith [Real.pi_pos, hθ.1]
      · apply PiLp.ext
        intro i
        fin_cases i
        · change Real.cos ((m : ℝ)*((θ-2*Real.pi)/(m : ℝ))) = x 0
          rw [mul_div_cancel₀ _ hm0, Real.cos_sub_two_pi, hc]
        · change Real.sin ((m : ℝ)*((θ-2*Real.pi)/(m : ℝ))) = x 1
          rw [mul_div_cancel₀ _ hm0, Real.sin_sub_two_pi, hs]
    · have hmge : 1 ≤ (m : ℝ) := by
        have hmz : (1 : ℤ) ≤ m := by
          have : 0 < m := by exact_mod_cast hmpos
          omega
        exact_mod_cast hmz
      refine ⟨θ/(m : ℝ), ⟨div_nonneg hθ.1 hmpos.le, ?_⟩, ?_⟩
      · apply (div_le_iff₀ hmpos).mpr
        nlinarith [Real.pi_pos, hθ.2]
      · apply PiLp.ext
        intro i
        fin_cases i
        · change Real.cos ((m : ℝ)*(θ/(m : ℝ))) = x 0
          rw [mul_div_cancel₀ _ hm0, hc]
        · change Real.sin ((m : ℝ)*(θ/(m : ℝ))) = x 1
          rw [mul_div_cancel₀ _ hm0, hs]

lemma angularField_no_potential : ¬ ∃ f : E 2 → ℝ,
    CrOn 1 puncturedPlane f ∧ ∀ x ∈ puncturedPlane, scalarGradient f x = angularField x := by
  rintro ⟨f, hf, hgrad⟩
  obtain ⟨d⟩ := circle_piecewiseC1 1
  have htrace : trace (circlePath 1) ⊆ puncturedPlane := by
    rintro x ⟨t, _, rfl⟩
    exact (angularField_circle 1 t).1
  obtain ⟨hc, hw, _, hval⟩ := gradient_integral d puncturedPlane f puncturedPlane_open hf htrace
  have hconst : ∀ i, ∀ t ∈ cell d.partition i,
      inner ℝ (scalarGradient f (circlePath 1 t)) (d.velocity i t) = (1 : ℝ) := by
    intro i t ht
    change inner ℝ (scalarGradient f (circle 1 t)) (d.velocity i t) = 1
    rw [hgrad _ ((angularField_circle 1 t).1), velocity_agrees 1 d i ht]
    simpa using (angularField_circle 1 t).2
  obtain ⟨hw', he⟩ := pieceIntegral_constant d
    (fun x v => inner ℝ (scalarGradient f x) v) 1 hconst
  have hz : f (circlePath 1 (2*Real.pi)) - f (circlePath 1 0) = 0 := by
    change f (circle 1 (2*Real.pi)) - f (circle 1 0) = 0
    rw [circle_closed, sub_self]
  have he' : workLineIntegral d (scalarGradient f) hw = 2*Real.pi := by
    exact he.trans (by ring)
  rw [hz, he'] at hval
  linarith [Real.pi_pos]

lemma trace_length_values_differ :
    trace (circlePath 1) = trace (circlePath 2) ∧
    trace (circlePath 1) = trace (circlePath (-1)) ∧
    length (circle 1) 0 (2*Real.pi) ≠ length (circle 2) 0 (2*Real.pi) ∧
    (2*Real.pi*(1 : ℝ)) ≠ (2*Real.pi*(-1 : ℝ)) := by
  refine ⟨(circle_trace 1 (by norm_num)).trans (circle_trace 2 (by norm_num)).symm,
    (circle_trace 1 (by norm_num)).trans (circle_trace (-1) (by norm_num)).symm, ?_, ?_⟩
  · rw [circle_length, circle_length]
    intro h
    have he := congrArg ENNReal.toReal h
    norm_num only [Int.cast_one, Int.cast_ofNat, abs_one, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at he
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at he
    norm_num at he
  · nlinarith [Real.pi_pos]


/-- Equal traces give neither an unsigned nor a directed integral value. -/
lemma trace_does_not_determine :
    ∃ (d₁ : PiecewiseC1Data (circlePath 1))
      (d₂ : PiecewiseC1Data (circlePath 2)) (dneg : PiecewiseC1Data (circlePath (-1))),
    ∃ (h₁ : ScalarIntegrable d₁ (fun _ => 1)) (h₂ : ScalarIntegrable d₂ (fun _ => 1)),
    ∃ (w₁ : WorkIntegrable d₁ angularField) (wneg : WorkIntegrable dneg angularField),
      trace (circlePath 1) = trace (circlePath 2) ∧
      trace (circlePath 1) = trace (circlePath (-1)) ∧
      scalarLineIntegral d₁ (fun _ => 1) h₁ ≠ scalarLineIntegral d₂ (fun _ => 1) h₂ ∧
      workLineIntegral d₁ angularField w₁ ≠ workLineIntegral dneg angularField wneg := by
  obtain ⟨d₁⟩ := circle_piecewiseC1 1
  obtain ⟨d₂⟩ := circle_piecewiseC1 2
  obtain ⟨dneg⟩ := circle_piecewiseC1 (-1)
  obtain ⟨h₁, hs₁⟩ := circle_scalar_integral 1 d₁
  obtain ⟨h₂, hs₂⟩ := circle_scalar_integral 2 d₂
  obtain ⟨w₁, hw₁⟩ := circle_work_integral 1 d₁
  obtain ⟨wneg, hwneg⟩ := circle_work_integral (-1) dneg
  refine ⟨d₁, d₂, dneg, h₁, h₂, w₁, wneg,
    trace_length_values_differ.1, trace_length_values_differ.2.1, ?_, ?_⟩
  · rw [hs₁, hs₂]
    norm_num
  · rw [hw₁, hwneg]
    norm_num
    linarith [Real.pi_pos]

end CircleMultiplicity
end D04.C09
