import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinSolutions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

namespace ExpandedFA.PartIV.KreinSolutions

/-- The normalized even solution of `w'' = μ w`. -/
def C : ℝ → ℝ → ℝ := Specs.CValue
/-- The normalized odd solution of `w'' = μ w`. -/
def S : ℝ → ℝ → ℝ := Specs.SValue

def kernelPlus : (ℝ → ℝ) → ℝ → ℝ → ℝ := Specs.KernelPlusValue

def kernelMinus : (ℝ → ℝ) → ℝ → ℝ → ℝ := Specs.KernelMinusValue

/-- Scalar positive definiteness includes symmetry and all finite real quadratic tests. -/
def PositiveDefinite : (ℝ → ℝ → ℝ) → Prop := Specs.PositiveDefiniteValue

@[simp] theorem C_zero_parameter (t : ℝ) : C 0 t = 1 := by
  simp [C, Specs.CValue]

@[simp] theorem S_zero_parameter (t : ℝ) : S 0 t = t := by
  simp [S, Specs.SValue]

theorem parity : Specs.Parity := by
  intro μ
  constructor
  · intro t
    simp [Specs.CValue, mul_neg, Real.cos_neg, Real.cosh_neg]
  · intro t
    by_cases hn : μ < 0
    · simp [Specs.SValue, hn, mul_neg, Real.sin_neg, neg_div]
    · by_cases hz : μ = 0 <;>
        simp [Specs.SValue, hn, hz, mul_neg, Real.sinh_neg, neg_div]

/-- Both first derivatives, with the square-root denominators cancelled only away from zero. -/
theorem firstDerivatives : Specs.FirstDerivatives := by
  intro μ t
  by_cases hn : μ < 0
  · have hne : Real.sqrt (-μ) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hn)
    have hsq : Real.sqrt (-μ) ^ 2 = -μ := Real.sq_sqrt (le_of_lt (neg_pos.mpr hn))
    have hc : Specs.CValue μ = fun u => Real.cos (Real.sqrt (-μ) * u) := by
      funext u; simp [Specs.CValue, hn]
    have hs : Specs.SValue μ = fun u => Real.sin (Real.sqrt (-μ) * u) / Real.sqrt (-μ) := by
      funext u; simp [Specs.SValue, hn]
    rw [hc, hs]
    constructor
    · convert ((Real.hasDerivAt_cos (Real.sqrt (-μ) * t)).comp t
        ((hasDerivAt_id t).const_mul (Real.sqrt (-μ)))) using 1
      · rfl
      · field_simp [hne]
        ring_nf
        rw [hsq]
        ring
    · convert (((Real.hasDerivAt_sin (Real.sqrt (-μ) * t)).comp t
        ((hasDerivAt_id t).const_mul (Real.sqrt (-μ)))).div_const (Real.sqrt (-μ))) using 1 <;>
        simp [hne]
  · by_cases hz : μ = 0
    · subst μ
      have hc : Specs.CValue 0 = fun _ => (1 : ℝ) := by funext u; simp [Specs.CValue]
      have hs : Specs.SValue 0 = id := by funext u; simp [Specs.SValue]
      rw [hc, hs]
      simpa only [zero_mul] using
        And.intro (hasDerivAt_const t (1 : ℝ)) (hasDerivAt_id t)
    · have hp : 0 < μ := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      have hne : Real.sqrt μ ≠ 0 := Real.sqrt_ne_zero'.mpr hp
      have hsq : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hp.le
      have hc : Specs.CValue μ = fun u => Real.cosh (Real.sqrt μ * u) := by
        funext u; simp [Specs.CValue, hn, hz]
      have hs : Specs.SValue μ = fun u => Real.sinh (Real.sqrt μ * u) / Real.sqrt μ := by
        funext u; simp [Specs.SValue, hn, hz]
      rw [hc, hs]
      constructor
      · convert ((Real.hasDerivAt_cosh (Real.sqrt μ * t)).comp t
          ((hasDerivAt_id t).const_mul (Real.sqrt μ))) using 1
        · rfl
        · field_simp [hne]
          ring_nf
          rw [hsq]
      · convert (((Real.hasDerivAt_sinh (Real.sqrt μ * t)).comp t
          ((hasDerivAt_id t).const_mul (Real.sqrt μ))).div_const (Real.sqrt μ)) using 1 <;>
          simp [hne]

theorem secondDerivatives : Specs.SecondDerivatives := by
  intro μ t
  have hc : deriv (Specs.CValue μ) = fun u => μ * Specs.SValue μ u :=
    funext fun u => (firstDerivatives μ u).1.deriv
  have hs : deriv (Specs.SValue μ) = Specs.CValue μ :=
    funext fun u => (firstDerivatives μ u).2.deriv
  constructor
  · rw [hc]
    exact ((firstDerivatives μ t).2.const_mul μ)
  · rw [hs]
    exact (firstDerivatives μ t).1

theorem initialData : Specs.InitialData := by
  intro μ
  have hc : Specs.CValue μ 0 = 1 := by simp [Specs.CValue]
  have hs : Specs.SValue μ 0 = 0 := by simp [Specs.SValue]
  exact ⟨hc, by simpa [hs] using (firstDerivatives μ 0).1.deriv,
    hs, by simpa [hc] using (firstDerivatives μ 0).2.deriv⟩

theorem additionSum : Specs.AdditionSum := by
  intro μ s t
  by_cases hn : μ < 0
  · simp only [Specs.CValue, ite_eq_left hn, mul_sub, mul_add, Real.cos_sub, Real.cos_add]
    ring
  · by_cases hz : μ = 0
    · simp [Specs.CValue, hz]
      ring
    · simp only [Specs.CValue, ite_eq_right hn, ite_eq_right hz, mul_sub, mul_add,
        Real.cosh_sub, Real.cosh_add]
      ring

theorem additionDifference : Specs.AdditionDifference := by
  intro μ s t
  by_cases hn : μ < 0
  · have hne : Real.sqrt (-μ) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hn)
    have hsq : Real.sqrt (-μ) ^ 2 = -μ := Real.sq_sqrt (le_of_lt (neg_pos.mpr hn))
    simp only [Specs.CValue, Specs.SValue, ite_eq_left hn, mul_sub, mul_add,
      Real.cos_sub, Real.cos_add]
    field_simp [hne]
    rw [hsq]
    ring
  · by_cases hz : μ = 0
    · simp [Specs.CValue, Specs.SValue, hz]
    · have hp : 0 < μ := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      have hne : Real.sqrt μ ≠ 0 := Real.sqrt_ne_zero'.mpr hp
      have hsq : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hp.le
      simp only [Specs.CValue, Specs.SValue, ite_eq_right hn, ite_eq_right hz, mul_sub, mul_add,
        Real.cosh_sub, Real.cosh_add]
      field_simp [hne]
      rw [hsq]
      ring

theorem kernelRegularity : Specs.KernelRegularity := by
  intro F hF he
  have hsub : ∀ s t, F (s - t) = F (t - s) := by
    intro s t
    simpa only [neg_sub] using he (t - s)
  constructor
  · constructor
    · exact ((hF.comp (continuous_fst.sub continuous_snd)).add
        (hF.comp (continuous_fst.add continuous_snd))).div_const 2
    · intro s t
      simp only [Specs.KernelPlusValue, hsub s t, add_comm s t]
  · constructor
    · exact ((hF.comp (continuous_fst.sub continuous_snd)).sub
        (hF.comp (continuous_fst.add continuous_snd))).div_const 2
    · intro s t
      simp only [Specs.KernelMinusValue, hsub s t, add_comm s t]

end ExpandedFA.PartIV.KreinSolutions
