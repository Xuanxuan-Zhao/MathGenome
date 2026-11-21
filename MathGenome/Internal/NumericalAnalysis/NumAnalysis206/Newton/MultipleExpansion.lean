import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.MultipleExpansion
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.Definitions
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Filter Topology

namespace NumAnalysis206.Newton

/-- Differentiating the local multiplicity factorization, with a factored result. -/
lemma hasDerivAt_multiple_factor (g : ℝ → ℝ) (p x : ℝ) (m : ℕ)
    (hm : 1 ≤ m) (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun y => (y - p) ^ m * g y)
      ((x - p) ^ (m - 1) * ((m : ℝ) * g x + (x - p) * deriv g x)) x := by
  have hpow : (x - p) ^ m = (x - p) ^ (m - 1) * (x - p) := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  convert (((hasDerivAt_id x).sub_const p).pow m).mul hg.hasDerivAt using 1
  · rfl
  · dsimp
    rw [hpow]
    ring

/-- The complete local multiple-root expansion, including finite constants. -/
theorem multiple_root_expansion : Specs.NumAnalysis206.Newton.multipleRootExpansion := by
  intro f g p m hm hg hgp hf
  have hm1 : 1 ≤ m := le_trans (by decide) hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hg' : ContinuousAt (deriv g) p :=
    (hg.derivWithin (m := 0) (by norm_num)).continuousAt
  let A : ℝ → ℝ := fun x => (m : ℝ) * g x + (x - p) * deriv g x
  have hA : ContinuousAt A p :=
    (continuousAt_const.mul hg.continuousAt).add
      ((continuousAt_id.sub continuousAt_const).mul hg')
  have hA0 : A p ≠ 0 := by simpa [A] using mul_ne_zero hm0 hgp
  let c : ℝ := |A p| / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hAlower : ∀ᶠ x in 𝓝 p, c ≤ |A x| :=
    hA.abs.eventually_const_le (by dsimp [c]; linarith [abs_pos.mpr hA0])
  let B : ℝ → ℝ := fun x => deriv g x / ((m : ℝ) * A x)
  have hB : ContinuousAt B p :=
    hg'.div (continuousAt_const.mul hA) (mul_ne_zero hm0 hA0)
  let C : ℝ := |B p| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBbound : ∀ᶠ x in 𝓝 p, |B x| ≤ C :=
    hB.abs.eventually_le_const (by dsimp [C]; linarith)
  have hroot : f p = 0 := by
    rw [hf.eq_of_nhds]
    simp [Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hm)]
  have hevent : ∀ᶠ x in 𝓝 p,
      f =ᶠ[𝓝 x] (fun y => (y - p) ^ m * g y) ∧
      ContDiffAt ℝ 2 g x ∧ c ≤ |A x| ∧ |B x| ≤ C := by
    filter_upwards [hf.eventuallyEq_nhds, hg.eventually (by norm_num), hAlower, hBbound]
      with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨r, c, C, hr, hc, hC, hroot, ?_⟩
  intro x hx
  obtain ⟨hfx, hgx, hAx, hBx⟩ := hball (by simpa [Metric.mem_ball, Real.dist_eq] using hx)
  have hd := (hasDerivAt_multiple_factor g p x m hm1
    (hgx.differentiableAt (by norm_num))).congr_of_eventuallyEq hfx
  have hder : deriv f x = (x - p) ^ (m - 1) * A x := hd.deriv
  have hAx0 : A x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hAx
    linarith
  have hquot (hne : x ≠ p) :
      deriv f x ≠ 0 ∧ f x / deriv f x = (x - p) / (m : ℝ) -
        (x - p) ^ 2 * deriv g x / ((m : ℝ) * A x) := by
    have he : x - p ≠ 0 := sub_ne_zero.mpr hne
    have hep : (x - p) ^ (m - 1) ≠ 0 := pow_ne_zero _ he
    refine ⟨by rw [hder]; exact mul_ne_zero hep hAx0, ?_⟩
    rw [hfx.eq_of_nhds, hder]
    have hpow : (x - p) ^ m = (x - p) ^ (m - 1) * (x - p) := by
      rw [← pow_succ, Nat.sub_add_cancel hm1]
    rw [hpow]
    field_simp [hep, hm0, hAx0]
    dsimp [A]
    ring
  have herr : Specs.NumAnalysis206.Newton.scalarNewtonValue f x - p -
      (1 - 1 / (m : ℝ)) * (x - p) = (x - p) ^ 2 * B x := by
    by_cases hne : x = p
    · subst x
      simp [Specs.NumAnalysis206.Newton.scalarNewtonValue, hroot]
    · unfold Specs.NumAnalysis206.Newton.scalarNewtonValue
      rw [(hquot hne).2]
      dsimp [B]
      ring
  have hcorr : Specs.NumAnalysis206.Newton.correctedNewtonValue m f x - p =
      (m : ℝ) * ((x - p) ^ 2 * B x) := by
    by_cases hne : x = p
    · subst x
      simp [Specs.NumAnalysis206.Newton.correctedNewtonValue, hroot]
    · unfold Specs.NumAnalysis206.Newton.correctedNewtonValue
      rw [mul_div_assoc, (hquot hne).2]
      dsimp [B]
      field_simp
      ring
  refine ⟨hd.differentiableAt, hder, hAx, hquot, ?_, ?_⟩
  · rw [herr, abs_mul, abs_pow]
    calc
      |x - p| ^ 2 * |B x| ≤ |x - p| ^ 2 * C :=
        mul_le_mul_of_nonneg_left hBx (sq_nonneg _)
      _ = _ := by ring
  · rw [hcorr, abs_mul, abs_of_pos hmpos, abs_mul, abs_pow]
    calc
      (m : ℝ) * (|x - p| ^ 2 * |B x|) ≤ (m : ℝ) * (|x - p| ^ 2 * C) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hBx (sq_nonneg _)) (le_of_lt hmpos)
      _ = _ := by ring

end NumAnalysis206.Newton
