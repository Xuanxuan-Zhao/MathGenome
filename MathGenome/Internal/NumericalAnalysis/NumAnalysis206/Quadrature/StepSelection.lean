import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.StepSelection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter Topology
namespace NumAnalysis206.Quadrature

private lemma central_left {M η a b : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hab : a ≤ b) (hb : M * b ^ 3 ≤ 3 * η) :
    centralBound M η b ≤ centralBound M η a := by
  have hbp : 0 < b := lt_of_lt_of_le ha hab
  have hp : a * b * (a + b) ≤ 2 * b ^ 3 := by
    calc
      a * b * (a + b) ≤ b * b * (b + b) := by gcongr
      _ = 2 * b ^ 3 := by ring
  have hc : M * (a * b * (a + b)) ≤ 6 * η := by nlinarith [mul_le_mul_of_nonneg_left hp hM]
  have hd := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hc)
  dsimp [centralBound]
  field_simp
  nlinarith

private lemma central_root {M η r h : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hh : 0 < h) (heq : M * r ^ 3 = 3 * η) :
    centralBound M η r ≤ centralBound M η h := by
  have hp : 0 ≤ M * (h - r) ^ 2 * (h + 2 * r) := by positivity
  dsimp [centralBound]
  field_simp
  nlinarith

private lemma forward_left {M η a b : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hab : a ≤ b) (hb : M * b ^ 2 ≤ 4 * η) :
    forwardBound M η b ≤ forwardBound M η a := by
  have hbp : 0 < b := lt_of_lt_of_le ha hab
  have hp : a * b ≤ b ^ 2 := by nlinarith
  have hc : M * (a * b) ≤ 4 * η := by nlinarith [mul_le_mul_of_nonneg_left hp hM]
  have hd := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hc)
  dsimp [forwardBound]
  field_simp
  nlinarith

private lemma forward_root {M η r h : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hh : 0 < h) (heq : M * r ^ 2 = 4 * η) :
    forwardBound M η r ≤ forwardBound M η h := by
  have hp : 0 ≤ M * (h - r) ^ 2 := by positivity
  dsimp [forwardBound]
  field_simp
  nlinarith

/-- The central bound has its global constrained minimum at the capped cube root. -/
theorem central_min : StepSelectionSpec.centralMin := by
  intro H M η hH hM hη
  let r := (3 * η / M) ^ (1 / 3 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hpow : r ^ 3 = 3 * η / M := by
    simpa only [r, one_div, Nat.cast_ofNat] using
      (Real.rpow_inv_natCast_pow (x := 3 * η / M) (by positivity) (by norm_num : (3 : ℕ) ≠ 0))
  have heq : M * r ^ 3 = 3 * η := by rw [hpow]; field_simp
  change min H r ∈ Ioc 0 H ∧ IsMinOn (centralBound M η) (Ioc 0 H) (min H r)
  refine ⟨⟨lt_min hH hr, min_le_left _ _⟩, ?_⟩
  intro h hh
  rcases le_total H r with hHr | hrH
  · rw [min_eq_left hHr]
    apply central_left hM.le hh.1 hh.2
    calc
      M * H ^ 3 ≤ M * r ^ 3 := by gcongr
      _ = 3 * η := heq
  · rw [min_eq_right hrH]
    exact central_root hM.le hr hh.1 heq

/-- The forward bound has its global constrained minimum at the capped square root. -/
theorem forward_min : StepSelectionSpec.forwardMin := by
  intro H M η hH hM hη
  rw [← Real.sqrt_eq_rpow]
  let r := Real.sqrt (4 * η / M)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hpow : r ^ 2 = 4 * η / M := Real.sq_sqrt (by positivity)
  have heq : M * r ^ 2 = 4 * η := by rw [hpow]; field_simp
  change min H r ∈ Ioc 0 H ∧ IsMinOn (forwardBound M η) (Ioc 0 H) (min H r)
  refine ⟨⟨lt_min hH hr, min_le_left _ _⟩, ?_⟩
  intro h hh
  rcases le_total H r with hHr | hrH
  · rw [min_eq_left hHr]
    apply forward_left hM.le hh.1 hh.2
    calc
      M * H ^ 2 ≤ M * r ^ 2 := by gcongr
      _ = 4 * η := heq
  · rw [min_eq_right hrH]
    exact forward_root hM.le hr hh.1 heq

/-- With only sample error, the central bound strictly decreases to its minimum at H. -/
theorem central_noise : StepSelectionSpec.centralNoise := by
  intro H η hH hη
  have hanti : StrictAntiOn (centralBound 0 η) (Ioc 0 H) := by
    intro a ha b hb hab
    simpa [centralBound] using (div_lt_div_of_pos_left hη ha.1 hab)
  refine ⟨hanti, ?_⟩
  intro h hh
  exact hanti.antitoneOn hh ⟨hH, le_rfl⟩ hh.2

/-- With only sample error, the forward bound strictly decreases to its minimum at H. -/
theorem forward_noise : StepSelectionSpec.forwardNoise := by
  intro H η hH hη
  have hanti : StrictAntiOn (forwardBound 0 η) (Ioc 0 H) := by
    intro a ha b hb hab
    simpa [forwardBound] using (div_lt_div_of_pos_left (show 0 < 2 * η by positivity) ha.1 hab)
  refine ⟨hanti, ?_⟩
  intro h hh
  exact hanti.antitoneOn hh ⟨hH, le_rfl⟩ hh.2

/-- With exact samples the central bound approaches zero, with no positive minimizer. -/
theorem central_exact : StepSelectionSpec.centralExact := by
  intro H M hH hM
  have hc : Continuous (centralBound M 0) := by
    change Continuous (fun h : ℝ => M * h ^ 2 / 6 + 0 / h)
    simp only [zero_div, add_zero]
    fun_prop
  have ht : Tendsto (centralBound M 0) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [centralBound] using (hc.continuousAt (x := 0)).tendsto
  refine ⟨ht.mono_left nhdsWithin_le_nhds, ?_, ?_⟩
  · apply IsGLB.isGLB_of_tendsto (s := Ioc 0 H) (a := 0) ?_ (isGLB_Ioc hH)
      ⟨H, hH, le_rfl⟩ (ht.mono_left nhdsWithin_le_nhds)
    intro a ha b hb hab
    dsimp [centralBound]
    simp only [zero_div, add_zero]
    gcongr
    exact ha.1.le
  · intro h hh hmin
    have hhpos := hh.1
    have hhalf : h / 2 ∈ Ioc 0 H := ⟨by positivity, by linarith [hh.2]⟩
    have hle := hmin hhalf
    dsimp [centralBound] at hle
    simp only [zero_div, add_zero] at hle
    have hp : 0 < M * h ^ 2 := by positivity
    nlinarith

/-- With exact samples the forward bound approaches zero, with no positive minimizer. -/
theorem forward_exact : StepSelectionSpec.forwardExact := by
  intro H M hH hM
  have hc : Continuous (forwardBound M 0) := by
    change Continuous (fun h : ℝ => M * h / 2 + 2 * 0 / h)
    simp only [mul_zero, zero_div, add_zero]
    fun_prop
  have ht : Tendsto (forwardBound M 0) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [forwardBound] using (hc.continuousAt (x := 0)).tendsto
  refine ⟨ht.mono_left nhdsWithin_le_nhds, ?_, ?_⟩
  · apply IsGLB.isGLB_of_tendsto (s := Ioc 0 H) (a := 0) ?_ (isGLB_Ioc hH)
      ⟨H, hH, le_rfl⟩ (ht.mono_left nhdsWithin_le_nhds)
    intro a ha b hb hab
    dsimp [forwardBound]
    simp only [mul_zero, zero_div, add_zero]
    gcongr
  · intro h hh hmin
    have hhpos := hh.1
    have hhalf : h / 2 ∈ Ioc 0 H := ⟨by positivity, by linarith [hh.2]⟩
    have hle := hmin hhalf
    dsimp [forwardBound] at hle
    simp only [mul_zero, zero_div, add_zero] at hle
    have hp : 0 < M * h := mul_pos hM hh.1
    nlinarith

/-- Both zero budgets give identically zero bounds. -/
theorem zero_budgets : StepSelectionSpec.zeroBudgets := by
  intro h
  simp [centralBound, forwardBound]

end NumAnalysis206.Quadrature
