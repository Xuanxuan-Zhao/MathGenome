import Specs.ExpandedFA.PartV.VolterraFactorial
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.VolterraOperator
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Factorial bounds and the ordered simplex formula from
paper.tex:21872–21907, fa2:p5:volterra-resolvent.

We work on `[a,b]`, specializing to `[0,T]` by `a = 0`, `b = T`.
The pointwise induction integrates `(s-a)^n` and divides by `n+1`, giving
the factorial with no smallness assumption. The independent recursive integral
appends each kernel factor on the right of the accumulated operator. Commuting
that fixed bounded linear map with the Bochner integral proves the formula
without commuting any two kernel values. The zero-fold power is the identity,
and the zero-fold integral evaluates `u`, also on singleton intervals.
-/

noncomputable section
namespace ExpandedFA.PartV
open Set MeasureTheory

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
variable {a b : ℝ} (hab : a ≤ b)
  (k : C(volterraTriangle a b, E →L[𝕜] E))

/-- The selected upstream operator satisfies its actual integral formula. -/
theorem volterra_apply_integral (u : C(VolterraInterval a b, E))
    (t : VolterraInterval a b) :
    VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k u t =
      volterraIntegralValue hab k u t :=
  (volterra_operator_properties 𝕜 E a b hab k).1 u t

/-- The scalar simplex-volume recurrence, without any positive-length premise. -/
theorem integral_sub_pow (a t : ℝ) (n : ℕ) :
    (∫ s in a..t, (s - a) ^ n) = (t - a) ^ (n + 1) / (n + 1 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_right (fun s : ℝ => s ^ n) a]
  simp

/-- Integrating the inductive pointwise bound gives the factorial, rather than
merely the geometric operator-norm bound. -/
theorem volterra_pow_pointwise (n : ℕ) (u : C(VolterraInterval a b, E))
    (t : VolterraInterval a b) :
    ‖((VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n) u t‖ ≤
      ‖k‖ ^ n * ((t : ℝ) - a) ^ n / (n.factorial : ℝ) * ‖u‖ := by
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  change ‖(V ^ n) u t‖ ≤ _
  induction n generalizing t with
  | zero => simpa using u.norm_coe_le_norm t
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, volterra_apply_integral hab k]
    change ‖∫ s in a..(t : ℝ), volterraIntegrand hab k ((V ^ n) u) t s‖ ≤ _
    calc
      _ ≤ ∫ s in a..(t : ℝ),
          ‖k‖ * (‖k‖ ^ n * (s - a) ^ n / (n.factorial : ℝ) * ‖u‖) := by
        apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
        · apply Filter.Eventually.of_forall
          intro s hs
          rw [volterraIntegrand_eq hab k ((V ^ n) u) t s ⟨hs.1.le, hs.2⟩]
          exact ((k _).le_opNorm _).trans
            (mul_le_mul (k.norm_coe_le_norm _) (ih ⟨s, hs.1.le, hs.2.trans t.property.2⟩)
              (norm_nonneg _) (norm_nonneg k))
        · exact (by fun_prop : Continuous (fun s : ℝ =>
            ‖k‖ * (‖k‖ ^ n * (s - a) ^ n / (n.factorial : ℝ) * ‖u‖))).intervalIntegrable _ _
      _ = ‖k‖ ^ (n + 1) * ((t : ℝ) - a) ^ (n + 1) /
          ((n + 1).factorial : ℝ) * ‖u‖ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
          integral_sub_pow]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, div_eq_mul_inv, mul_inv_rev]
        ring

/-- Supremum in the interval variable and then the operator norm. -/
theorem volterra_pow_norm (n : ℕ) :
    ‖(VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n‖ ≤
      ‖k‖ ^ n * (b - a) ^ n / (n.factorial : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  exact (volterra_pow_pointwise hab k n u t).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (sub_nonneg.mpr t.property.1)
            (sub_le_sub_right t.property.2 a) n) (by positivity)) (by positivity))
      (norm_nonneg u))

/-- Pulling a fixed accumulated operator through the integrals identifies the
nested formula with the genuine operator power. -/
theorem volterra_orderedIntegral_eq (n : ℕ) (u : C(VolterraInterval a b, E))
    (A : E →L[𝕜] E) (t : VolterraInterval a b) :
    volterraOrderedIntegral hab k u n A t =
      A (((VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n) u t) := by
  induction n generalizing A t with
  | zero => rfl
  | succ n ih =>
    simp only [volterraOrderedIntegral, ih, ContinuousLinearMap.comp_apply]
    rw [pow_succ', mul_apply_eq_comp, volterra_apply_integral hab k]
    exact A.intervalIntegral_comp_comm
      (((continuous_volterraIntegrand hab k
        (((VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n) u)).comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)

/-- Each level of the nested integral is continuous and integrable. -/
theorem continuous_volterraOrderedIntegrand (n : ℕ)
    (u : C(VolterraInterval a b, E)) (A : E →L[𝕜] E)
    (t : VolterraInterval a b) :
    Continuous (fun s : ℝ => volterraOrderedIntegral hab k u n
      (A.comp (k (volterraRetraction t s))) (Set.projIcc a b hab s)) := by
  simp only [volterra_orderedIntegral_eq, ContinuousLinearMap.comp_apply]
  exact A.continuous.comp
    ((continuous_volterraIntegrand hab k
      (((VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n) u)).comp
        (continuous_const.prodMk continuous_id))

end

theorem volterra_factorial_pointwise : VolterraFactorialSpec.PointwiseEstimate := by
  intro 𝕜 E _ _ _ _ a b hab k n u t
  exact volterra_pow_pointwise hab k n u t

theorem volterra_factorial_operator_norm : VolterraFactorialSpec.OperatorEstimate := by
  intro 𝕜 E _ _ _ _ a b hab k n
  exact volterra_pow_norm hab k n

theorem volterra_factorial_uniform_operator_norm :
    VolterraFactorialSpec.UniformOperatorEstimate := by
  intro 𝕜 E _ _ _ _ a b hab k M hM n
  have hM0 : 0 ≤ M :=
    (norm_nonneg (k ⟨(a, a), le_rfl, le_rfl, hab⟩)).trans
      (hM ⟨(a, a), le_rfl, le_rfl, hab⟩)
  have hk : ‖k‖ ≤ M := (ContinuousMap.norm_le k hM0).mpr hM
  exact (volterra_pow_norm hab k n).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg k) hk n)
        (pow_nonneg (sub_nonneg.mpr hab) n)) (by positivity))

theorem volterra_factorial_uniform_pointwise :
    VolterraFactorialSpec.UniformPointwiseEstimate := by
  intro 𝕜 E _ _ _ _ a b hab k M hM n u t
  have hM0 : 0 ≤ M :=
    (norm_nonneg (k ⟨(a, a), le_rfl, le_rfl, hab⟩)).trans
      (hM ⟨(a, a), le_rfl, le_rfl, hab⟩)
  have hk : ‖k‖ ≤ M := (ContinuousMap.norm_le k hM0).mpr hM
  exact (volterra_pow_pointwise hab k n u t).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg k) hk n)
          (pow_nonneg (sub_nonneg.mpr t.property.1) n)) (by positivity))
      (norm_nonneg u))

theorem volterra_ordered_integral_formula : VolterraFactorialSpec.OrderedIntegralFormula := by
  intro 𝕜 E _ _ _ _ a b hab k n u t
  exact (volterra_orderedIntegral_eq hab k n u (ContinuousLinearMap.id 𝕜 E) t).symm

theorem volterra_ordered_integrals_exist : VolterraFactorialSpec.OrderedIntegralsExist := by
  intro 𝕜 E _ _ _ _ a b hab k n u A t
  have hc := continuous_volterraOrderedIntegrand hab k n u A t
  exact ⟨hc, hc.intervalIntegrable _ _⟩

theorem volterra_ordered_integrand_restriction :
    VolterraFactorialSpec.OrderedIntegrandRestriction := by
  intro 𝕜 E _ _ _ _ a b hab k n u A t s hs
  have hr : volterraRetraction t s = ⟨((t : ℝ), s), hs.1, hs.2, t.property.2⟩ := by
    apply Subtype.ext
    simp [volterraRetraction, min_eq_right hs.2, max_eq_right hs.1]
  rw [hr, Set.projIcc_of_mem hab ⟨hs.1, hs.2.trans t.property.2⟩]

end ExpandedFA.PartV
