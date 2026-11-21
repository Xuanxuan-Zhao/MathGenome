import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UcSums
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.RotundDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.BanachSumDefinitions
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform convexity of finite and uniformly convex arbitrary normed sums.
We use a power-deficit estimate, rather than a scalar ℓᵖ convexity theorem.
A compact one-variable argument makes the coordinate estimate uniform. -/
noncomputable section
open scoped ENNReal
open Set
universe u v w
namespace ExpandedFA.P1.UcSums

/-- Convexity of the power function, in midpoint form. -/
lemma power_midpoint_le {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((a + b) / 2) ^ p ≤ (a ^ p + b ^ p) / 2 := by
  have h := (convexOn_rpow hp).2 ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  convert h using 1 <;> congr 1 <;> ring

lemma power_midpoint_lt {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≠ b) : ((a + b) / 2) ^ p < (a ^ p + b ^ p) / 2 := by
  have h := (strictConvexOn_rpow hp).2 ha hb hab
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  convert h using 1 <;> congr 1 <;> ring

/-- The scalar power deficit is uniformly positive when one normalized norm
is one and the midpoint is uniformly below one. -/
lemma scalar_deficit_gap {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      γ ≤ (1 + b ^ p) / 2 - (min ((1 + b) / 2) (1 - δ)) ^ p := by
  let f : ℝ → ℝ := fun b =>
    (1 + b ^ p) / 2 - (min ((1 + b) / 2) (1 - δ)) ^ p
  have hc : Continuous f := by
    dsimp [f]
    fun_prop (disch := positivity)
  have hpos : ∀ b ∈ Icc (0 : ℝ) 1, 0 < f b := by
    intro b hb
    dsimp [f]
    have hm : 0 ≤ min ((1 + b) / 2) (1 - δ) :=
      le_min (by linarith [hb.1]) (by linarith)
    by_cases hb₁ : b = 1
    · subst b
      simp only [Real.one_rpow, add_self_div_two]
      have heq : min (1 : ℝ) (1 - δ) = 1 - δ := min_eq_right (by linarith)
      rw [heq]
      have hlt := Real.rpow_lt_rpow (by linarith : 0 ≤ 1 - δ)
        (by linarith : 1 - δ < 1) (by linarith : 0 < p)
      simpa using sub_pos.mpr hlt
    · have hs := power_midpoint_lt hp (show (0 : ℝ) ≤ 1 by norm_num) hb.1
        (Ne.symm hb₁)
      have hle := Real.rpow_le_rpow hm (min_le_left ((1 + b) / 2) (1 - δ))
        (by linarith : 0 ≤ p)
      rw [Real.one_rpow] at hs
      linarith
  obtain ⟨b, hb, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hc.continuousOn
  exact ⟨f b, hpos b hb, fun a ha ha₁ => hmin ⟨ha, ha₁⟩⟩

/-- Homogeneous version of the compact scalar estimate. -/
lemma homogeneous_deficit_gap {p δ γ a b c : ℝ}
    (hp : 0 < p) (hγ : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      γ ≤ (1 + z ^ p) / 2 - (min ((1 + z) / 2) (1 - δ)) ^ p)
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) (hc : 0 ≤ c)
    (hcmean : c ≤ (a + b) / 2) (hcδ : c ≤ a * (1 - δ)) :
    γ * a ^ p ≤ (a ^ p + b ^ p) / 2 - c ^ p := by
  have hz₀ : 0 ≤ b / a := div_nonneg hb ha.le
  have hz₁ : b / a ≤ 1 := (div_le_one ha).mpr hba
  have hcm : c / a ≤ min ((1 + b / a) / 2) (1 - δ) := by
    apply le_min
    · apply (div_le_iff₀ ha).mpr
      calc
        c ≤ (a + b) / 2 := hcmean
        _ = ((1 + b / a) / 2) * a := by field_simp
    · exact (div_le_iff₀ ha).mpr (by linarith)
  have hcp := Real.rpow_le_rpow (div_nonneg hc ha.le) hcm hp.le
  have h := hγ (b / a) hz₀ hz₁
  have h' : γ ≤ (1 + (b / a) ^ p) / 2 - (c / a) ^ p := by linarith
  rw [Real.div_rpow hb ha.le, Real.div_rpow hc ha.le] at h'
  have hap : 0 < a ^ p := Real.rpow_pos_of_pos ha _
  apply (le_div_iff₀ hap).mp
  convert h' using 1; field_simp

/-- The power deficit is always nonnegative, solely by the triangle inequality. -/
lemma norm_power_deficit_nonneg {F : Type*} [SeminormedAddCommGroup F]
    {p : ℝ} (hp : 1 ≤ p) (x y : F) :
    0 ≤ (‖x‖ ^ p + ‖y‖ ^ p) / 2 - (‖x + y‖ / 2) ^ p := by
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ ‖x + y‖ / 2)
    (show ‖x + y‖ / 2 ≤ (‖x‖ + ‖y‖) / 2 by gcongr; exact norm_add_le x y)
    (by linarith : 0 ≤ p)
  have := power_midpoint_le hp (norm_nonneg x) (norm_nonneg y)
  linarith

/-- A common unit-ball gap gives a homogeneous power-deficit bound on
coordinates whose separation is a fixed fraction of their largest norm. -/
lemma separated_power_gap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p t δ γ : ℝ} (hp : 0 < p) (_ht : 0 < t)
    (hγ : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      γ ≤ (1 + z ^ p) / 2 - (min ((1 + z) / 2) (1 - δ)) ^ p)
    (huc : ∀ x y : F, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → t ≤ ‖x - y‖ →
      ‖x + y‖ / 2 ≤ 1 - δ)
    (x y : F) (hsep : t * max ‖x‖ ‖y‖ ≤ ‖x - y‖) :
    γ * (max ‖x‖ ‖y‖) ^ p ≤
      (‖x‖ ^ p + ‖y‖ ^ p) / 2 - (‖x + y‖ / 2) ^ p := by
  have aux : ∀ (x y : F), ‖y‖ ≤ ‖x‖ → t * ‖x‖ ≤ ‖x - y‖ →
      γ * ‖x‖ ^ p ≤ (‖x‖ ^ p + ‖y‖ ^ p) / 2 - (‖x + y‖ / 2) ^ p := by
    intro x y hyx hs
    by_cases hx : ‖x‖ = 0
    · have hy : ‖y‖ = 0 := le_antisymm (by simpa [hx] using hyx) (norm_nonneg y)
      have hxy : ‖x + y‖ = 0 := by
        apply le_antisymm _ (norm_nonneg _)
        simpa [hx, hy] using norm_add_le x y
      simp [hx, hy, hxy, Real.zero_rpow hp.ne']
    have hxpos : 0 < ‖x‖ := (norm_nonneg x).lt_of_ne' hx
    have hnx : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
        inv_mul_cancel₀ hx]
    have hny : ‖‖x‖⁻¹ • y‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
      exact (inv_mul_le_one₀ hxpos).mpr hyx
    have hns : t ≤ ‖‖x‖⁻¹ • x - ‖x‖⁻¹ • y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), ← div_eq_inv_mul]
      exact (le_div_iff₀ hxpos).mpr hs
    have h := huc _ _ hnx hny hns
    rw [← smul_add, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))] at h
    have hmid : ‖x + y‖ / 2 ≤ ‖x‖ * (1 - δ) := by
      have hh : (‖x + y‖ / 2) / ‖x‖ ≤ 1 - δ := by convert h using 1; ring
      exact (div_le_iff₀ hxpos).mp hh |>.trans_eq (mul_comm _ _)
    exact homogeneous_deficit_gap hp hγ hxpos (norm_nonneg y) hyx
      (by positivity) (by have := norm_add_le x y; linarith) hmid
  rcases le_total ‖y‖ ‖x‖ with hyx | hxy
  · rw [max_eq_left hyx] at hsep ⊢
    exact aux x y hyx hsep
  · rw [max_eq_right hxy] at hsep ⊢
    have h := aux y x hxy (by simpa [norm_sub_rev] using hsep)
    simpa [add_comm] using h

/-- The estimate that will be summed. Small coordinates are paid for by
`t^p` times their mass; the others are paid for by the convexity deficit. -/
lemma coordinate_power_estimate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p t δ γ : ℝ} (hp : 1 < p) (ht : 0 < t) (hγpos : 0 < γ)
    (hγ : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      γ ≤ (1 + z ^ p) / 2 - (min ((1 + z) / 2) (1 - δ)) ^ p)
    (huc : ∀ x y : F, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → t ≤ ‖x - y‖ →
      ‖x + y‖ / 2 ≤ 1 - δ) (x y : F) :
    ‖x - y‖ ^ p ≤ t ^ p * (‖x‖ ^ p + ‖y‖ ^ p) +
      (2 ^ p / γ) * ((‖x‖ ^ p + ‖y‖ ^ p) / 2 - (‖x + y‖ / 2) ^ p) := by
  have hp₀ : 0 < p := by linarith
  have hr₀ : 0 ≤ max ‖x‖ ‖y‖ := (norm_nonneg x).trans (le_max_left _ _)
  have hmass : (max ‖x‖ ‖y‖) ^ p ≤ ‖x‖ ^ p + ‖y‖ ^ p := by
    rcases le_total ‖x‖ ‖y‖ with h | h
    · rw [max_eq_right h]
      linarith [Real.rpow_nonneg (norm_nonneg x) p]
    · rw [max_eq_left h]
      linarith [Real.rpow_nonneg (norm_nonneg y) p]
  have hdef := norm_power_deficit_nonneg hp.le x y
  by_cases hs : t * max ‖x‖ ‖y‖ ≤ ‖x - y‖
  · have hgap := separated_power_gap hp₀ ht hγ huc x y hs
    have hnorm : ‖x - y‖ ≤ 2 * max ‖x‖ ‖y‖ := by
      have := norm_sub_le x y
      have := le_max_left ‖x‖ ‖y‖
      have := le_max_right ‖x‖ ‖y‖
      linarith
    have hpow := Real.rpow_le_rpow (norm_nonneg _) hnorm hp₀.le
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr₀] at hpow
    have hscaled := mul_le_mul_of_nonneg_left hgap
      (show 0 ≤ 2 ^ p / γ by positivity)
    have hcoef : (2 ^ p / γ) * γ = 2 ^ p := by field_simp
    rw [← mul_assoc, hcoef] at hscaled
    exact (hpow.trans hscaled).trans (le_add_of_nonneg_left (by positivity))
  · have hpow := Real.rpow_le_rpow (norm_nonneg _) (le_of_not_ge hs) hp₀.le
    rw [Real.mul_rpow ht.le hr₀] at hpow
    have hsmall := hpow.trans (mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ t ^ p))
    exact hsmall.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hdef))

/-- Extract the common midpoint implication from the canonical infimum modulus. -/
lemma common_ball_gap (𝕜 : Type w) {I : Type u} (E : I → Type v)
    [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (hmod : Spec.CommonModulus 𝕜 E) {t : ℝ} (ht : 0 < t) (ht₂ : t ≤ 2) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i (x y : E i),
      ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → t ≤ ‖x - y‖ → ‖x + y‖ / 2 ≤ 1 - δ := by
  obtain ⟨d, hd, hdi⟩ := hmod t ht ht₂
  refine ⟨min d 1, lt_min hd zero_lt_one, min_le_right _ _, ?_⟩
  intro i x y hx hy hsep
  have hmem : 1 - ‖(2 : 𝕜)⁻¹ • (x + y)‖ ∈
      RotundDefinitions.convexityDeficits 𝕜 (E i) t := ⟨x, y, hx, hy, hsep, rfl⟩
  have hne : (RotundDefinitions.convexityDeficits 𝕜 (E i) t).Nonempty := ⟨_, hmem⟩
  have hval : RotundDefinitions.Spec.ModulusValue 𝕜 (E i) t =
      sInf (RotundDefinitions.convexityDeficits 𝕜 (E i) t) := by
    simp only [RotundDefinitions.Spec.ModulusValue, ht.ne', ↓reduceIte]
    exact ite_eq_left hne
  have hle := csInf_le (RotundDefinitions.convexityDeficits_bddBelow 𝕜 (E i) t) hmem
  have hdi := hdi i
  rw [hval] at hdi
  rw [C14UniformConvexity.norm_midpoint_eq_half] at hle
  have := min_le_left d 1
  linarith

/-- Summing the coordinate estimate is valid on every index type.
All three power series have their canonical sums by `lp.hasSum_norm`. -/
lemma sum_power_estimate (𝕜 : Type w) {I : Type u} (E : I → Type v)
    [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    (hmod : Spec.CommonModulus 𝕜 E) {t : ℝ} (ht : 0 < t) (ht₂ : t ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : lp E p,
      ‖x - y‖ ^ p.toReal ≤ t ^ p.toReal * (‖x‖ ^ p.toReal + ‖y‖ ^ p.toReal) +
        C * ((‖x‖ ^ p.toReal + ‖y‖ ^ p.toReal) / 2 -
          ‖(2 : 𝕜)⁻¹ • (x + y)‖ ^ p.toReal) := by
  obtain ⟨δ, hδ, hδ₁, huc⟩ := common_ball_gap 𝕜 E hmod ht ht₂
  obtain ⟨γ, hγpos, hγ⟩ := scalar_deficit_gap hp hδ hδ₁
  refine ⟨2 ^ p.toReal / γ, by positivity, ?_⟩
  intro x y
  have hp₀ : 0 < p.toReal := by linarith
  have hx := lp.hasSum_norm hp₀ x
  have hy := lp.hasSum_norm hp₀ y
  have hm := lp.hasSum_norm hp₀ ((2 : 𝕜)⁻¹ • (x + y))
  have hd := lp.hasSum_norm hp₀ (x - y)
  have hr := ((hx.add hy).mul_left (t ^ p.toReal)).add
    ((((hx.add hy).div_const 2).sub hm).mul_left (2 ^ p.toReal / γ))
  apply hasSum_le _ hd hr
  intro i
  let : NormedSpace ℝ (E i) := NormedSpace.restrictScalars ℝ 𝕜 (E i)
  have h := coordinate_power_estimate hp ht hγpos hγ (huc i) (x i) (y i)
  change ‖x i - y i‖ ^ p.toReal ≤
    t ^ p.toReal * (‖x i‖ ^ p.toReal + ‖y i‖ ^ p.toReal) +
      (2 ^ p.toReal / γ) * ((‖x i‖ ^ p.toReal + ‖y i‖ ^ p.toReal) / 2 -
        ‖(2 : 𝕜)⁻¹ • (x i + y i)‖ ^ p.toReal)
  rw [C14UniformConvexity.norm_midpoint_eq_half]
  exact h

/-- Finite families, including the empty family, have a positive common
modulus whenever their individual norms are uniformly convex. -/
lemma finite_common_modulus (𝕜 : Type w) {I : Type u} [Finite I] (E : I → Type v)
    [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (huc : ∀ i, C14UniformConvexity.UniformlyConvex 𝕜 (E i)) :
    Spec.CommonModulus 𝕜 E := by
  intro ε hε hε₂
  have hpos : ∀ i, (0 : ℝ) < RotundDefinitions.modulusConvexity 𝕜 (E i) ε :=
    fun i => (RotundDefinitions.uniformlyConvex_iff_modulus_pos 𝕜 (E i)).mp
      (huc i) ε hε hε₂
  classical
  let := Fintype.ofFinite I
  have aux : ∀ A : Finset I, ∃ δ : ℝ, 0 < δ ∧
      ∀ i ∈ A, δ ≤ RotundDefinitions.modulusConvexity 𝕜 (E i) ε := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i A hi ih =>
      obtain ⟨d, hd, hdi⟩ := ih
      refine ⟨min d (RotundDefinitions.modulusConvexity 𝕜 (E i) ε),
        lt_min hd (hpos i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hdi j hj)
  obtain ⟨δ, hδ, hδi⟩ := aux Finset.univ
  exact ⟨δ, hδ, fun i => hδi i (Finset.mem_univ i)⟩

/-- Uniform convexity of an arbitrary ℓᵖ sum under a common modulus bound. -/
theorem arbitrary_sum_uniformlyConvex :
    ∀ (𝕜 : Type w) {I : Type u} (E : I → Type v)
      [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
      (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ → Spec.CommonModulus 𝕜 E →
      C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
        (ExpandedFA.Supplements.BanachSumDefinitions.Spec.Space E p) := by
  intro 𝕜 I E _ _ _ p _ hp hpt hmod
  have hp' : 1 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hpt).mpr hp
    simpa using this
  have hp₀ : 0 < p.toReal := by linarith
  intro ε hε hε₂
  let t : ℝ := ε / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₂ : t ≤ 2 := by dsimp [t]; linarith
  obtain ⟨C, hC, hest⟩ := sum_power_estimate 𝕜 E hp' hmod ht ht₂
  have htP : 0 < t ^ p.toReal := Real.rpow_pos_of_pos ht _
  have hfour : (4 : ℝ) ≤ 4 ^ p.toReal := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hp'.le
    simpa using h
  have hεP : ε ^ p.toReal = 4 ^ p.toReal * t ^ p.toReal := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) ht.le]
    congr 1
    dsimp [t]
    ring
  have hA : 0 < ε ^ p.toReal - 2 * t ^ p.toReal := by
    rw [hεP]
    nlinarith
  let B : ℝ := min ((ε ^ p.toReal - 2 * t ^ p.toReal) / C) (1 / 2)
  have hB : 0 < B := lt_min (div_pos hA hC) (by norm_num)
  have hB₁ : B ≤ 1 / 2 := min_le_right _ _
  have hBC : C * B ≤ ε ^ p.toReal - 2 * t ^ p.toReal := by
    have h := min_le_left ((ε ^ p.toReal - 2 * t ^ p.toReal) / C) (1 / 2)
    simpa only [mul_comm] using (le_div_iff₀ hC).mp h
  let R : ℝ := (1 - B) ^ (p.toReal)⁻¹
  have hR₀ : 0 ≤ R := Real.rpow_nonneg (by linarith) _
  have hR₁ : R < 1 := Real.rpow_lt_one (by linarith) (by linarith) (inv_pos.mpr hp₀)
  refine ⟨1 - R, by linarith, ?_⟩
  intro x y hx hy hsep
  have hxP : ‖x‖ ^ p.toReal ≤ 1 := by
    simpa using Real.rpow_le_rpow (norm_nonneg x) hx hp₀.le
  have hyP : ‖y‖ ^ p.toReal ≤ 1 := by
    simpa using Real.rpow_le_rpow (norm_nonneg y) hy hp₀.le
  have hsepP := Real.rpow_le_rpow hε.le hsep hp₀.le
  have he := hest x y
  have hsum : ‖x‖ ^ p.toReal + ‖y‖ ^ p.toReal ≤ 2 := by linarith
  have hbound : ε ^ p.toReal ≤ 2 * t ^ p.toReal +
      C * (1 - ‖(2 : 𝕜)⁻¹ • (x + y)‖ ^ p.toReal) := by
    calc
      ε ^ p.toReal ≤ ‖x - y‖ ^ p.toReal := hsepP
      _ ≤ _ := he
      _ ≤ _ := by
        have htbound := mul_le_mul_of_nonneg_left hsum htP.le
        have hCbound := mul_le_mul_of_nonneg_left (show
          (‖x‖ ^ p.toReal + ‖y‖ ^ p.toReal) / 2 ≤ 1 by linarith) hC.le
        nlinarith
  have hmidP : ‖(2 : 𝕜)⁻¹ • (x + y)‖ ^ p.toReal ≤ 1 - B := by
    nlinarith
  have hRP : R ^ p.toReal = 1 - B := Real.rpow_inv_rpow (by linarith) hp₀.ne'
  have hmid : ‖(2 : 𝕜)⁻¹ • (x + y)‖ ≤ R := by
    apply (Real.rpow_le_rpow_iff (norm_nonneg _) hR₀ hp₀).mp
    rwa [hRP]
  simpa only [sub_sub_cancel] using hmid

/-- Every finite ℓᵖ sum of uniformly convex spaces is uniformly convex. -/
theorem finite_sum_uniformlyConvex :
    ∀ (𝕜 : Type w) {I : Type u} [Finite I] (E : I → Type v)
      [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
      (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
      (∀ i, C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 (E i)) →
      C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
        (ExpandedFA.Supplements.BanachSumDefinitions.Spec.Space E p) := by
  intro 𝕜 I _ E _ _ _ p _ hp hpt huc
  exact arbitrary_sum_uniformlyConvex 𝕜 E p hp hpt (finite_common_modulus 𝕜 E huc)

end ExpandedFA.P1.UcSums
