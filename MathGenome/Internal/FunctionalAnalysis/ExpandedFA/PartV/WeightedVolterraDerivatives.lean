import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeightedVolterraDerivatives
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.WeakVolterraResolvent
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace VolterraSmoothness

lemma hasDerivWithinAt_integral_Icc {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure A} {F G : ℝ → A → E} {B C : A → ℝ} {a b : ℝ}
    (hab : a < b)
    (hFm : ∀ t ∈ Icc a b, AEStronglyMeasurable (F t) μ)
    (hGm : ∀ t ∈ Icc a b, AEStronglyMeasurable (G t) μ)
    (hFB : ∀ᵐ r ∂μ, ∀ t ∈ Icc a b, ‖F t r‖ ≤ B r)
    (hGB : ∀ᵐ r ∂μ, ∀ t ∈ Icc a b, ‖G t r‖ ≤ C r)
    (hB : Integrable B μ) (hC : Integrable C μ)
    (hFc : ∀ᵐ r ∂μ, ContinuousOn (fun t => F t r) (Icc a b))
    (hGc : ∀ᵐ r ∂μ, ContinuousOn (fun t => G t r) (Icc a b))
    (hd : ∀ᵐ r ∂μ, ∀ t ∈ Ioo a b, HasDerivAt (fun t => F t r) (G t r) t) :
    ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => ∫ r, F s r ∂μ)
      (∫ r, G t r ∂μ) (Icc a b) t := by
  have hcF : ContinuousOn (fun t => ∫ r, F t r ∂μ) (Icc a b) :=
    continuousOn_of_dominated hFm (fun t ht => hFB.mono (fun r hr => hr t ht)) hB hFc
  have hcG : ContinuousOn (fun t => ∫ r, G t r ∂μ) (Icc a b) :=
    continuousOn_of_dominated hGm (fun t ht => hGB.mono (fun r hr => hr t ht)) hC hGc
  have hdi (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun t => ∫ r, F t r ∂μ) (∫ r, G t r ∂μ) t := by
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Ioo_mem_nhds ht.1 ht.2)
      (by filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
          exact hFm s ⟨hs.1.le, hs.2.le⟩)
      (hB.mono' (hFm t ⟨ht.1.le, ht.2.le⟩)
        (hFB.mono (fun r hr => hr t ⟨ht.1.le, ht.2.le⟩)))
      (hGm t ⟨ht.1.le, ht.2.le⟩)
      (hGB.mono (fun r hr s hs => hr s ⟨hs.1.le, hs.2.le⟩)) hC hd).2
  intro t ht
  rcases eq_or_lt_of_le ht.1 with heq | hat
  · subst t
    apply (hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun s hs => (hdi s hs).differentiableAt.differentiableWithinAt)
      ((hcF a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT hab) ?_).mono Icc_subset_Ici_self
    apply ((hcG a ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT hab)).congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with s hs
    exact (hdi s hs).deriv.symm
  · rcases lt_or_eq_of_le ht.2 with htb | heq
    · exact (hdi t ⟨hat, htb⟩).hasDerivWithinAt
    · subst t
      apply (hasDerivWithinAt_Iic_of_tendsto_deriv
        (fun s hs => (hdi s hs).differentiableAt.differentiableWithinAt)
        ((hcF b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self)
        (Ioo_mem_nhdsLT hab) ?_).mono Icc_subset_Iic_self
      apply ((hcG b ⟨hab.le, le_rfl⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLT hab)).congr'
      filter_upwards [Ioo_mem_nhdsLT hab] with s hs
      exact (hdi s hs).deriv.symm

/-- Finite jets may be integrated term by term on a closed real interval. The
hypotheses refer only to values and derivatives on that interval; arbitrary
ambient values outside it impose no extra condition. -/
lemma contDiffOn_integral_of_jets {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure A} {H : ℕ → ℝ → A → E} {B : ℕ → A → ℝ} {a b : ℝ} {m : ℕ}
    (hab : a < b)
    (hHm : ∀ j ≤ m, ∀ t ∈ Icc a b, AEStronglyMeasurable (H j t) μ)
    (hHB : ∀ j ≤ m, ∀ᵐ r ∂μ, ∀ t ∈ Icc a b, ‖H j t r‖ ≤ B j r)
    (hB : ∀ j ≤ m, Integrable (B j) μ)
    (hHc : ∀ j ≤ m, ∀ᵐ r ∂μ, ContinuousOn (fun t => H j t r) (Icc a b))
    (hd : ∀ j < m, ∀ᵐ r ∂μ, ∀ t ∈ Ioo a b,
      HasDerivAt (fun t => H j t r) (H (j+1) t r) t) :
    ContDiffOn ℝ m (fun t => ∫ r, H 0 t r ∂μ) (Icc a b) ∧
      ∀ j ≤ m, ∀ t ∈ Icc a b,
        iteratedDerivWithin j (fun t => ∫ r, H 0 t r ∂μ) (Icc a b) t =
          ∫ r, H j t r ∂μ := by
  have hc (j : ℕ) (hj : j ≤ m) :
      ContinuousOn (fun t => ∫ r, H j t r ∂μ) (Icc a b) :=
    continuousOn_of_dominated (hHm j hj)
      (fun t ht => (hHB j hj).mono (fun r hr => hr t ht)) (hB j hj) (hHc j hj)
  have hdi (j : ℕ) (hj : j < m) : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s => ∫ r, H j s r ∂μ)
        (∫ r, H (j+1) t r ∂μ) (Icc a b) t :=
    hasDerivWithinAt_integral_Icc hab (hHm j hj.le) (hHm (j+1) hj)
      (hHB j hj.le) (hHB (j+1) hj) (hB j hj.le) (hB (j+1) hj)
      (hHc j hj.le) (hHc (j+1) hj) (hd j hj)
  have heq : ∀ j ≤ m, ∀ t ∈ Icc a b,
      iteratedDerivWithin j (fun t => ∫ r, H 0 t r ∂μ) (Icc a b) t =
        ∫ r, H j t r ∂μ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj t ht
      rw [iteratedDerivWithin_succ]
      rw [derivWithin_congr (ih (by omega)) (ih (by omega) t ht)]
      exact (hdi j (by omega) t ht).derivWithin (uniqueDiffOn_Icc hab t ht)
  refine ⟨(contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (uniqueDiffOn_Icc hab)).mpr ⟨?_, ?_⟩, heq⟩
  · intro j hj
    exact (hc j hj).congr (heq j hj)
  · intro j hj t ht
    exact ((hdi j hj t ht).congr (heq j hj.le) (heq j hj.le t ht)).differentiableWithinAt

/-- A fixed integrable weight preserves finite smoothness on a closed interval,
provided the derivatives of the varying factor are measurable in the parameter
and have a constant bound for each derivative order. -/
lemma contDiffOn_weighted_integral {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure A} {P : A → ℝ → E} {w : A → ℝ} {C : ℕ → ℝ} {a b : ℝ} {m : ℕ}
    (hab : a < b) (hw : Integrable w μ)
    (hPc : ∀ᵐ r ∂μ, ContDiffOn ℝ m (P r) (Icc a b))
    (hPm : ∀ j ≤ m, ∀ t ∈ Icc a b,
      AEStronglyMeasurable (fun r => iteratedDerivWithin j (P r) (Icc a b) t) μ)
    (hPB : ∀ j ≤ m, ∀ᵐ r ∂μ, ∀ t ∈ Icc a b,
      ‖iteratedDerivWithin j (P r) (Icc a b) t‖ ≤ C j) :
    ContDiffOn ℝ m (fun t => ∫ r, w r • P r t ∂μ) (Icc a b) ∧
      ∀ j ≤ m, ∀ t ∈ Icc a b,
        iteratedDerivWithin j (fun t => ∫ r, w r • P r t ∂μ) (Icc a b) t =
          ∫ r, w r • iteratedDerivWithin j (P r) (Icc a b) t ∂μ := by
  let H (j : ℕ) (t : ℝ) (r : A) := w r • iteratedDerivWithin j (P r) (Icc a b) t
  have h := contDiffOn_integral_of_jets (H := H) (m := m) (μ := μ)
    (B := fun j r => ‖w r‖ * C j) hab ?_ ?_ ?_ ?_ ?_
  · simpa only [H, iteratedDerivWithin_zero] using h
  · intro j hj t ht
    exact hw.aestronglyMeasurable.smul (hPm j hj t ht)
  · intro j hj
    filter_upwards [hPB j hj] with r hr t ht
    dsimp [H]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hr t ht) (norm_nonneg _)
  · intro j hj
    exact hw.norm.mul_const (C j)
  · intro j hj
    filter_upwards [hPc] with r hr
    exact (hr.continuousOn_iteratedDerivWithin (by exact_mod_cast hj)
      (uniqueDiffOn_Icc hab)).const_smul (w r)
  · intro j hj
    filter_upwards [hPc] with r hr t ht
    have hd : HasDerivWithinAt (iteratedDerivWithin j (P r) (Icc a b))
        (iteratedDerivWithin (j+1) (P r) (Icc a b) t) (Icc a b) t := by
      simpa only [iteratedDerivWithin_succ] using
        (hr.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj)
          (uniqueDiffOn_Icc hab) t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt
    exact (hd.const_smul (w r)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end VolterraSmoothness

namespace ExpandedFA.PartV.WeightedVolterraDerivatives
open ExpandedFA.PartV.FractionalIntegrals.Spec
open ExpandedFA.PartV.WeakVolterraBounds.Spec

/-- The Gamma denominator dominates arbitrary geometric numerators with
any fixed polynomial factor, as needed for all finite derivative orders. -/
theorem polynomial_gamma_summability : Spec.PolynomialGammaSummability := by
  intro α c hα hc d
  obtain ⟨R₀, hR₀⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop hα)) (c+1)
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hRc : c < R^α := lt_of_lt_of_le (by linarith : c < c+1)
    (hR₀ R (le_max_left _ _))
  have hq0 : 0 ≤ c/R^α := div_nonneg hc (Real.rpow_nonneg hR.le _)
  have hq : ‖c/R^α‖ < 1 := by
    rw [Real.norm_of_nonneg hq0]
    exact (div_lt_one (Real.rpow_pos_of_pos hR _)).mpr hRc
  have hs := (summable_pow_mul_geometric_of_norm_lt_one d hq).mul_left (Real.exp (R+1))
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) _) (pow_nonneg hc _))
      (Real.Gamma_pos_of_pos (by positivity)).le)
    (fun n => ?_) hs
  have hg := WeakVolterraBounds.gamma_lower_bound
    (mul_nonneg (Nat.cast_nonneg n) hα.le) hR
  calc
    (n : ℝ)^d * c^n / Real.Gamma ((n : ℝ)*α+1) ≤
        (n : ℝ)^d * c^n / (Real.exp (-(R+1)) * R^((n : ℝ)*α)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hg
    _ = Real.exp (R+1) * ((n : ℝ)^d * (c/R^α)^n) := by
      rw [mul_comm (n : ℝ) α, Real.rpow_mul_natCast hR.le, div_pow, Real.exp_neg]
      field_simp

/-- The correction series starts with the first iterate, rather than the
datum. This shifted polynomial majorant is still summable. -/
lemma summable_shifted_polynomial_gamma {α c : ℝ} (hα : 0 < α)
    (hc : 0 ≤ c) (d : ℕ) :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^d * c^(n+1) /
      Real.Gamma (((n+1 : ℕ) : ℝ)*α+1)) := by
  exact (summable_nat_add_iff 1).mpr (polynomial_gamma_summability hα hc d)

/-- Abstract weighted M-test, applicable to each differentiated correction
series once its finite-iterate estimates have been established. -/
lemma weighted_tsum_bound {𝕜 : Type} [RCLike 𝕜]
    {F : ℕ → ℝ → 𝕜} {b : ℕ → ℝ} {α β T : ℝ}
    (hb : Summable b) (_hb0 : ∀ n, 0 ≤ b n)
    (hF : ∀ n t, t ∈ Ioc (0 : ℝ) T → ‖F n t‖ ≤ b n * t^(α-β)) :
    (∀ t ∈ Ioc (0 : ℝ) T, Summable (fun n => F n t)) ∧
    (∀ t ∈ Ioc (0 : ℝ) T,
      ‖∑' n, F n t‖ ≤ (∑' n, b n) * t^(α-β)) ∧
    TendstoUniformlyOn
      (fun N t => ∑ n ∈ Finset.range N, t^(β-α) • F n t)
      (fun t => ∑' n, t^(β-α) • F n t) atTop (Ioc (0 : ℝ) T) := by
  have hs (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) :
      Summable (fun n => ‖F n t‖) := by
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hF n t ht)
      (hb.mul_right _)
  refine ⟨fun t ht => (hs t ht).of_norm, ?_, ?_⟩
  · intro t ht
    calc
      ‖∑' n, F n t‖ ≤ ∑' n, ‖F n t‖ := norm_tsum_le_tsum_norm (hs t ht)
      _ ≤ ∑' n, b n * t^(α-β) := (hs t ht).tsum_le_tsum
        (fun n => hF n t ht) (hb.mul_right _)
      _ = _ := tsum_mul_right
  · apply tendstoUniformlyOn_tsum_nat hb
    intro n t ht
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    calc
      t^(β-α) * ‖F n t‖ ≤ t^(β-α) * (b n * t^(α-β)) :=
        mul_le_mul_of_nonneg_left (hF n t ht) (Real.rpow_nonneg ht.1.le _)
      _ = b n := by
        calc
          _ = b n * (t^(β-α) * t^(α-β)) := by ring
          _ = b n := by rw [← Real.rpow_add ht.1]; simp

/-- On any interval bounded away from zero a weighted majorant is an
ordinary summable uniform majorant, for either sign of the exponent. -/
lemma weighted_majorant_on_interval {𝕜 : Type} [RCLike 𝕜]
    {F : ℕ → ℝ → 𝕜} {b : ℕ → ℝ} {p a T : ℝ}
    (ha : 0 < a) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hF : ∀ n t, t ∈ Ioc (0 : ℝ) T → ‖F n t‖ ≤ b n * t^p) :
    ∃ B : ℕ → ℝ, Summable B ∧
      ∀ n t, t ∈ Icc a T → ‖F n t‖ ≤ B n := by
  refine ⟨fun n => b n * max (a^p) (T^p), hb.mul_right _, ?_⟩
  intro n t ht
  have hp : t^p ≤ max (a^p) (T^p) := by
    rcases le_total 0 p with hp | hp
    · exact (Real.rpow_le_rpow (ha.trans_le ht.1).le ht.2 hp).trans
        (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos ha ht.1 hp).trans (le_max_left _ _)
  exact (hF n t ⟨ha.trans_le ht.1, ht.2⟩).trans
    (mul_le_mul_of_nonneg_left hp (hb0 n))

/-- Weighted normal convergence implies continuity on the entire positive
half-open interval, including its right endpoint. -/
lemma weighted_tsum_continuousOn {𝕜 : Type} [RCLike 𝕜]
    {F : ℕ → ℝ → 𝕜} {b : ℕ → ℝ} {p T : ℝ}
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hFc : ∀ n, ContinuousOn (F n) (Ioc 0 T))
    (hF : ∀ n t, t ∈ Ioc (0 : ℝ) T → ‖F n t‖ ≤ b n * t^p) :
    ContinuousOn (fun t => ∑' n, F n t) (Ioc 0 T) := by
  intro t ht
  obtain ⟨B, hB, hFB⟩ := weighted_majorant_on_interval (by linarith [ht.1] : 0 < t/2)
    hb hb0 hF
  have hsub : Icc (t/2) T ⊆ Ioc (0 : ℝ) T :=
    fun s hs => ⟨by linarith [hs.1, ht.1], hs.2⟩
  have hc := continuousOn_tsum (fun n => (hFc n).mono hsub) hB hFB
  apply (hc t ⟨by linarith [ht.1], ht.2⟩).mono_of_mem_nhdsWithin
  exact mem_of_superset
    (inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith [ht.1] : t/2 < t)))
      self_mem_nhdsWithin)
    (fun s hs => ⟨hs.1.le, hs.2.2⟩)

/-- Termwise differentiation under weighted normal convergence. The
right endpoint follows by continuity of the sum and of its derivative
and the mean value theorem, so no ambient extension beyond T is needed. -/
lemma hasDerivWithinAt_weighted_tsum {𝕜 : Type} [RCLike 𝕜]
    {F G : ℕ → ℝ → 𝕜} {b c : ℕ → ℝ} {p q T : ℝ}
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hc : Summable c) (hc0 : ∀ n, 0 ≤ c n)
    (hFc : ∀ n, ContinuousOn (F n) (Ioc 0 T))
    (hGc : ∀ n, ContinuousOn (G n) (Ioc 0 T))
    (hd : ∀ n t, t ∈ Ioc (0 : ℝ) T →
      HasDerivWithinAt (F n) (G n t) (Ioc 0 T) t)
    (hF : ∀ n t, t ∈ Ioc (0 : ℝ) T → ‖F n t‖ ≤ b n * t^p)
    (hG : ∀ n t, t ∈ Ioc (0 : ℝ) T → ‖G n t‖ ≤ c n * t^q) :
    ∀ t ∈ Ioc (0 : ℝ) T,
      HasDerivWithinAt (fun s => ∑' n, F n s) (∑' n, G n t) (Ioc 0 T) t := by
  have hs (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) : Summable (fun n => F n t) :=
    .of_norm_bounded (hb.mul_right (t^p)) (fun n => hF n t ht)
  have hdi (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
      HasDerivAt (fun s => ∑' n, F n s) (∑' n, G n t) t := by
    obtain ⟨B, hB, hGB⟩ := weighted_majorant_on_interval
      (by linarith [ht.1] : 0 < t/2) hc hc0 hG
    apply hasDerivAt_of_tendstoUniformlyOn (s := Ioo (t/2) T) isOpen_Ioo
      (tendstoUniformlyOn_tsum_nat hB (fun n s hs => hGB n s ⟨hs.1.le, hs.2.le⟩))
    · exact .of_forall fun N s hs => HasDerivAt.fun_sum fun n _ =>
        (hd n s ⟨by linarith [hs.1, ht.1], hs.2.le⟩).hasDerivAt
          (Ioc_mem_nhds (by linarith [hs.1, ht.1]) hs.2)
    · exact fun s hs' => (hs s ⟨by linarith [hs'.1, ht.1], hs'.2.le⟩).hasSum.tendsto_sum_nat
    · exact ⟨by linarith [ht.1], ht.2⟩
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact (hdi t ⟨ht.1, hlt⟩).hasDerivWithinAt
  · subst t
    have hFc' := weighted_tsum_continuousOn hb hb0 hFc hF
    have hGc' := weighted_tsum_continuousOn hc hc0 hGc hG
    apply (hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun s hs => (hdi s hs).differentiableAt.differentiableWithinAt)
      ((hFc' T ht).mono Ioo_subset_Ioc_self) (Ioo_mem_nhdsLT ht.1) ?_).mono
      Ioc_subset_Iic_self
    apply ((hGc' T ht).mono_of_mem_nhdsWithin (Ioc_mem_nhdsLT ht.1)).congr'
    filter_upwards [Ioo_mem_nhdsLT ht.1] with s hs
    exact (hdi s hs).deriv.symm

/-- Smooth series with summable weighted bounds on every derivative.
All identities are within (0,T], so they include the one-sided endpoint. -/
lemma contDiffOn_tsum_of_weighted_bounds {𝕜 : Type} [RCLike 𝕜]
    {F : ℕ → ℝ → 𝕜} {b : ℕ → ℕ → ℝ} {α T : ℝ} {m : ℕ}
    (hF : ∀ n, ContDiffOn ℝ m (F n) (Ioc 0 T))
    (hb : ∀ j ≤ m, Summable (b j))
    (hb0 : ∀ j ≤ m, ∀ n, 0 ≤ b j n)
    (hB : ∀ j ≤ m, ∀ n t, t ∈ Ioc (0 : ℝ) T →
      ‖iteratedDerivWithin j (F n) (Ioc 0 T) t‖ ≤ b j n * t^(α-(j : ℝ))) :
    ContDiffOn ℝ m (fun t => ∑' n, F n t) (Ioc 0 T) ∧
      ∀ j ≤ m, ∀ t ∈ Ioc (0 : ℝ) T,
        iteratedDerivWithin j (fun t => ∑' n, F n t) (Ioc 0 T) t =
          ∑' n, iteratedDerivWithin j (F n) (Ioc 0 T) t := by
  have hcont (j : ℕ) (hj : j ≤ m) (n : ℕ) :
      ContinuousOn (iteratedDerivWithin j (F n) (Ioc 0 T)) (Ioc 0 T) :=
    (hF n).continuousOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Ioc _ _)
  have hd (j : ℕ) (hj : j < m) : ∀ t ∈ Ioc (0 : ℝ) T,
      HasDerivWithinAt (fun t => ∑' n, iteratedDerivWithin j (F n) (Ioc 0 T) t)
        (∑' n, iteratedDerivWithin (j+1) (F n) (Ioc 0 T) t) (Ioc 0 T) t := by
    apply hasDerivWithinAt_weighted_tsum (hb j hj.le) (hb0 j hj.le)
      (hb (j+1) hj) (hb0 (j+1) hj) (hcont j hj.le) (hcont (j+1) hj)
      ?_ (hB j hj.le) (hB (j+1) hj)
    intro n t ht
    simpa only [iteratedDerivWithin_succ] using
      ((hF n).differentiableOn_iteratedDerivWithin
        (by exact_mod_cast hj) (uniqueDiffOn_Ioc _ _) t ht).hasDerivWithinAt
  have heq : ∀ j ≤ m, ∀ t ∈ Ioc (0 : ℝ) T,
      iteratedDerivWithin j (fun t => ∑' n, F n t) (Ioc 0 T) t =
        ∑' n, iteratedDerivWithin j (F n) (Ioc 0 T) t := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj t ht
      rw [iteratedDerivWithin_succ]
      rw [derivWithin_congr (ih (by omega)) (ih (by omega) t ht)]
      exact (hd j (by omega) t ht).derivWithin (uniqueDiffOn_Ioc _ _ t ht)
  refine ⟨(contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (uniqueDiffOn_Ioc _ _)).mpr ⟨?_, ?_⟩, heq⟩
  · intro j hj
    exact (weighted_tsum_continuousOn (hb j hj) (hb0 j hj) (hcont j hj) (hB j hj)).congr
      (heq j hj)
  · intro j hj t ht
    exact ((hd j hj t ht).congr (heq j hj.le) (heq j hj.le t ht)).differentiableWithinAt

/-- Transfer the smooth series and its estimates to the original solution
correction, preserving subtraction of the datum before differentiation. -/
lemma derivative_conclusion_of_series {𝕜 : Type} [RCLike 𝕜]
    {F : ℕ → ℝ → 𝕜} {b : ℕ → ℕ → ℝ} {α T : ℝ} {m : ℕ}
    {f u : ℝ → 𝕜} (hf : ContDiffOn ℝ m f (Icc 0 T))
    (hF : ∀ n, ContDiffOn ℝ m (F n) (Ioc 0 T))
    (hb : ∀ j ≤ m, Summable (b j))
    (hb0 : ∀ j ≤ m, ∀ n, 0 ≤ b j n)
    (hB : ∀ j ≤ m, ∀ n t, t ∈ Ioc (0 : ℝ) T →
      ‖iteratedDerivWithin j (F n) (Ioc 0 T) t‖ ≤ b j n * t^(α-(j : ℝ)))
    (hu : ∀ t ∈ Ioc (0 : ℝ) T, HasSum (fun n => F n t) (u t - f t)) :
    Spec.DerivativeConclusion m α T f u := by
  obtain ⟨hsm, hder⟩ := contDiffOn_tsum_of_weighted_bounds hF hb hb0 hB
  have heq : EqOn (fun t => u t - f t) (fun t => ∑' n, F n t) (Ioc 0 T) :=
    fun t ht => (hu t ht).tsum_eq.symm
  refine ⟨((hf.mono Ioc_subset_Icc_self).add hsm).congr
    (fun t ht => by simp [← heq ht]), ?_⟩
  intro j hj hjm
  refine ⟨∑' n, b j n, tsum_nonneg (hb0 j hjm), ?_⟩
  intro t ht
  rw [iteratedDerivWithin_congr heq ht, hder j hjm t ht]
  exact (weighted_tsum_bound (α := α) (β := (j : ℝ)) (hb j hjm) (hb0 j hjm)
    (hB j hjm)).2.1 t ht

/-- Absorb all higher iterate powers of t into a summable coefficient.
The resulting bound is uniform on the full half-open interval (0,T]. -/
lemma gamma_majorant_to_weighted {𝕜 : Type} [RCLike 𝕜]
    {F : ℕ → ℝ → 𝕜} {α c D β T : ℝ} (hα : 0 < α)
    (hc : 0 ≤ c) (hD : 0 ≤ D) (d : ℕ)
    (hF : ∀ n t, t ∈ Ioc (0 : ℝ) T →
      ‖F n t‖ ≤ D * ((n+1 : ℕ) : ℝ)^d * c^(n+1) /
        Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) *
        t^(((n+1 : ℕ) : ℝ)*α-β)) :
    ∃ b : ℕ → ℝ, Summable b ∧ (∀ n, 0 ≤ b n) ∧
      ∀ n t, t ∈ Ioc (0 : ℝ) T → ‖F n t‖ ≤ b n * t^(α-β) := by
  let R : ℝ := max 1 T
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let b : ℕ → ℝ := fun n =>
    (D / R^α) * (((n+1 : ℕ) : ℝ)^d * (c*R^α)^(n+1) /
      Real.Gamma (((n+1 : ℕ) : ℝ)*α+1))
  refine ⟨b, (summable_shifted_polynomial_gamma hα (by positivity) d).mul_left _,
    fun n => by dsimp [b]; positivity [Real.Gamma_pos_of_pos (by positivity :
      0 < ((n+1 : ℕ) : ℝ)*α+1)], ?_⟩
  intro n t ht
  have htR : t ≤ R := ht.2.trans (le_max_right _ _)
  have he : ((n+1 : ℕ) : ℝ)*α-β = (n : ℝ)*α+(α-β) := by
    push_cast
    ring
  have hp : t^((n : ℝ)*α) ≤ R^((n : ℝ)*α) :=
    Real.rpow_le_rpow ht.1.le htR (by positivity)
  calc
    ‖F n t‖ ≤ D * ((n+1 : ℕ) : ℝ)^d * c^(n+1) /
        Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) * t^(((n+1 : ℕ) : ℝ)*α-β) := hF n t ht
    _ = D * ((n+1 : ℕ) : ℝ)^d * c^(n+1) /
        Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) * (t^((n : ℝ)*α)*t^(α-β)) := by
      rw [he, Real.rpow_add ht.1]
    _ ≤ D * ((n+1 : ℕ) : ℝ)^d * c^(n+1) /
        Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) * (R^((n : ℝ)*α)*t^(α-β)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg ht.1.le _))
        (by positivity [Real.Gamma_pos_of_pos (by positivity :
          0 < ((n+1 : ℕ) : ℝ)*α+1)])
    _ = b n * t^(α-β) := by
      dsimp [b]
      rw [mul_pow, pow_succ (R^α), mul_comm (n : ℝ) α, Real.rpow_mul_natCast hR.le]
      field_simp

/-- The polynomial/Gamma estimates for the individual terms suffice for
the full correction estimate and regularity, with no smallness assumption. -/
lemma derivative_conclusion_of_gamma_series {𝕜 : Type} [RCLike 𝕜]
    {F : ℕ → ℝ → 𝕜} {α T : ℝ} {m : ℕ} {f u : ℝ → 𝕜}
    (hα : 0 < α) (hf : ContDiffOn ℝ m f (Icc 0 T))
    (hF : ∀ n, ContDiffOn ℝ m (F n) (Ioc 0 T))
    (hB : ∀ j ≤ m, ∃ (D c : ℝ) (d : ℕ), 0 ≤ D ∧ 0 ≤ c ∧
      ∀ n t, t ∈ Ioc (0 : ℝ) T →
        ‖iteratedDerivWithin j (F n) (Ioc 0 T) t‖ ≤
          D * ((n+1 : ℕ) : ℝ)^d * c^(n+1) /
            Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) *
            t^(((n+1 : ℕ) : ℝ)*α-(j : ℝ)))
    (hu : ∀ t ∈ Ioc (0 : ℝ) T, HasSum (fun n => F n t) (u t - f t)) :
    Spec.DerivativeConclusion m α T f u := by
  classical
  have hex (j : ℕ) (hj : j ≤ m) : ∃ b : ℕ → ℝ,
      Summable b ∧ (∀ n, 0 ≤ b n) ∧
      ∀ n t, t ∈ Ioc (0 : ℝ) T →
        ‖iteratedDerivWithin j (F n) (Ioc 0 T) t‖ ≤ b n * t^(α-(j : ℝ)) := by
    obtain ⟨D, c, d, hD, hc, h⟩ := hB j hj
    exact gamma_majorant_to_weighted hα hc hD d h
  let b (j : ℕ) : ℕ → ℝ := if hj : j ≤ m then (hex j hj).choose else 0
  have hb (j : ℕ) (hj : j ≤ m) := (hex j hj).choose_spec
  have hb' (j : ℕ) (hj : j ≤ m) :
      Summable (b j) ∧ (∀ n, 0 ≤ b j n) ∧
      ∀ n t, t ∈ Ioc (0 : ℝ) T →
        ‖iteratedDerivWithin j (F n) (Ioc 0 T) t‖ ≤ b j n * t^(α-(j : ℝ)) := by
    simpa only [b, dite_eq_left hj] using hb j hj
  exact derivative_conclusion_of_series hf hF (fun j hj => (hb' j hj).1)
    (fun j hj => (hb' j hj).2.1) (fun j hj => (hb' j hj).2.2) hu

/-- Normalize an iterate by its entire power of the output time. The
remaining integral is over a fixed interval. This definition uses the
original amplitude and datum, without clamping either smooth function. -/
def rescaledIterate {𝕜 : Type} [RCLike 𝕜] (α : ℝ)
    (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) : ℕ → ℝ → 𝕜
  | 0, t => f t
  | n+1, t => ∫ r in Ioc (0 : ℝ) 1,
      WeakVolterraResolvent.betaWeight α ((n : ℝ)*α+1) r •
        (k (t,t*r) * rescaledIterate α k f n (t*r))

/-- Dilation of one power-kernel integral. The identity holds before any
smoothness argument, and retains the exact unnormalized power of t. -/
lemma power_integral_rescale {𝕜 : Type} [RCLike 𝕜]
    {t α β : ℝ} (ht : 0 < t) (k : ℝ × ℝ → 𝕜) (h : ℝ → 𝕜) :
    (∫ s in Ioc 0 t, (t-s)^(α-1) • (k (t,s) * (s^β • h s))) =
      t^(α+β) • ∫ r in Ioc (0 : ℝ) 1,
        ((1-r)^(α-1) * r^β) • (k (t,t*r) * h (t*r)) := by
  let g : ℝ → 𝕜 := fun s => (t-s)^(α-1) • (k (t,s) * (s^β • h s))
  have he : ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) 1),
      g (t*r) = t^(α+β-1) •
        (((1-r)^(α-1) * r^β) • (k (t,t*r) * h (t*r))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp [g]
    rw [mul_smul_comm, show t-t*r = t*(1-r) by ring,
      Real.mul_rpow ht.le (sub_nonneg.mpr hr.2), Real.mul_rpow ht.le hr.1.le]
    simp only [smul_smul]
    rw [show α+β-1 = (α-1)+β by ring, Real.rpow_add ht]
    congr 1
    ring
  have hsub := intervalIntegral.smul_integral_comp_mul_add g t 0 (a := 0) (b := 1)
  simp only [mul_zero, add_zero, mul_one] at hsub
  rw [intervalIntegral.integral_of_le ht.le,
    intervalIntegral.integral_of_le zero_le_one, integral_congr_ae he,
    integral_smul, smul_smul] at hsub
  change (∫ s in Ioc 0 t, g s) = _
  rw [← hsub]
  have hp : t * t^(α+β-1) = t^(α+β) := by
    calc
      _ = t^(1 : ℝ) * t^(α+β-1) := by rw [Real.rpow_one]
      _ = t^(1+(α+β-1)) := (Real.rpow_add ht _ _).symm
      _ = _ := by congr 1; ring
  rw [hp]

/-- The recursively rescaled integrals represent the actual operator powers.
Only values on the original triangle and time interval enter this identity. -/
lemma continuous_iterate_rescaled {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hT : 0 ≤ T) (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜)
    (K : C(triangle T, 𝕜)) (hK : ∀ z, K z = k z.val)
    (F : C(Icc (0 : ℝ) T, 𝕜)) (hF : ∀ t, F t = f t)
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : WeakVolterraResolvent.Spec.ContinuousRealizes hT α K V) (n : ℕ) :
    ∀ t ∈ Ioc (0 : ℝ) T,
      continuousExtension hT ((V^n) F) t =
        t^((n : ℝ)*α) • rescaledIterate α k f n t := by
  induction n with
  | zero =>
    intro t ht
    simp [rescaledIterate, continuousExtension,
      projIcc_of_mem hT (Ioc_subset_Icc_self ht), hF]
  | succ n ih =>
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := Ioc_subset_Icc_self ht
    have he : (∫ s in Ioc 0 t,
        weakIntegrand α K (continuousExtension hT ((V^n) F)) t s) =
        ∫ s in Ioc 0 t, (t-s)^(α-1) •
          (k (t,s) * (s^((n : ℝ)*α) • rescaledIterate α k f n s)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      have hs' : s ∈ Ioc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      simp only [weakIntegrand, amplitudeValue,
        dite_eq_left (show (t,s) ∈ triangle T from ⟨hs.1.le, hs.2, ht.2⟩),
        hK, ih s hs']
    rw [pow_succ', mul_apply_eq_comp, continuousExtension, projIcc_of_mem hT ht',
      hV, weakValue, he, power_integral_rescale ht.1]
    congr 1
    · congr 1
      push_cast
      ring
    · simp only [rescaledIterate, WeakVolterraResolvent.betaWeight, add_sub_cancel_right]

lemma compact_finite_family_bound {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsCompact S) {b : ℕ → X → ℝ} (m : ℕ)
    (hb : ∀ j ≤ m, ContinuousOn (b j) S) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ j ≤ m, ∀ x ∈ S, b j x ≤ L := by
  induction m with
  | zero =>
    obtain ⟨C, hC⟩ := hS.bddAbove_image (hb 0 le_rfl)
    refine ⟨max 1 C, le_max_left _ _, ?_⟩
    intro j hj x hx
    have : j = 0 := by omega
    subst j
    exact (hC (mem_image_of_mem (b 0) hx)).trans (le_max_right _ _)
  | succ m ih =>
    obtain ⟨L, hL, hbL⟩ := ih (fun j hj => hb j (by omega))
    obtain ⟨C, hC⟩ := hS.bddAbove_image (hb (m+1) le_rfl)
    refine ⟨max L C, hL.trans (le_max_left _ _), ?_⟩
    intro j hj x hx
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact (hbL j (by omega) x hx).trans (le_max_left _ _)
    · exact (hC (mem_image_of_mem (b (m+1)) hx)).trans (le_max_right _ _)

lemma datum_derivatives_bound {𝕜 : Type} [RCLike 𝕜] {T : ℝ} {m : ℕ}
    (hT : 0 < T) {f : ℝ → 𝕜} (hf : ContDiffOn ℝ m f (Icc 0 T)) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin j f (Icc 0 T) t‖ ≤ L := by
  exact compact_finite_family_bound isCompact_Icc m
    (fun j hj => (hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj)
      (uniqueDiffOn_Icc hT)).norm)

lemma dilation_mapsTo_interval {T r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    MapsTo (r * ·) (Icc (0 : ℝ) T) (Icc (0 : ℝ) T) := by
  intro t ht
  exact ⟨mul_nonneg hr.1 ht.1,
    (mul_le_mul_of_nonneg_right hr.2 ht.1).trans (by simpa using ht.2)⟩

lemma datum_dilation_derivative_bound {𝕜 : Type} [RCLike 𝕜] {T : ℝ} {m : ℕ}
    (hT : 0 < T) {f : ℝ → 𝕜} (hf : ContDiffOn ℝ m f (Icc 0 T))
    {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin j f (Icc 0 T) t‖ ≤ L) :
    ∀ j ≤ m, ∀ r ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin j (fun t => f (t*r)) (Icc 0 T) t‖ ≤ L := by
  intro j hj r hr t ht
  have hmaps := dilation_mapsTo_interval hr (T := T)
  rw [show (fun t => f (t*r)) = (fun t => f (r*t)) by ext; rw [mul_comm],
    iteratedDerivWithin_comp_const_smul ht (uniqueDiffOn_Icc hT)
      (hf.of_le (by exact_mod_cast hj)) r hmaps,
    norm_smul, Real.norm_of_nonneg (pow_nonneg hr.1 _)]
  calc
    _ ≤ r^j * L := mul_le_mul_of_nonneg_left (hb j hj (r*t) (hmaps ht))
      (pow_nonneg hr.1 _)
    _ ≤ L := by
      simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hr.1 hr.2 (n := j)) hL


lemma kernel_derivatives_bound {𝕜 : Type} [RCLike 𝕜] {T : ℝ} {m : ℕ}
    {k : ℝ × ℝ → 𝕜} (hk : Spec.SmoothKernel m T k) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ j ≤ m, ∀ z ∈ triangle T,
      ‖iteratedFDeriv ℝ j k z‖ ≤ L := by
  obtain ⟨U, hU, htri, hk⟩ := hk
  have hcompact : IsCompact (triangle T) := isCompact_iff_compactSpace.mpr inferInstance
  exact compact_finite_family_bound hcompact m (fun j hj =>
    ((ContinuousOn.continuousOn_iteratedFDeriv hk hU (by exact_mod_cast hj)).mono htri).norm)






lemma kernel_dilation_contDiffOn {𝕜 : Type} [RCLike 𝕜] {T r : ℝ} {m : ℕ}
    {k : ℝ × ℝ → 𝕜} (hk : Spec.SmoothKernel m T k) (hr : r ∈ Icc (0 : ℝ) 1) :
    ContDiffOn ℝ m (fun t => k (t,t*r)) (Icc 0 T) := by
  obtain ⟨U, _, htri, hk⟩ := hk
  apply hk.comp (contDiffOn_id.prodMk (contDiffOn_id.mul contDiffOn_const))
  intro t ht
  exact htri ⟨mul_nonneg ht.1 hr.1,
    mul_le_of_le_one_right ht.1 hr.2, ht.2⟩

lemma kernel_dilation_derivative {𝕜 : Type} [RCLike 𝕜] {T r : ℝ} {m j : ℕ}
    (hT : 0 < T) {k : ℝ × ℝ → 𝕜} (hk : Spec.SmoothKernel m T k)
    (hr : r ∈ Icc (0 : ℝ) 1) (hj : j ≤ m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    iteratedDerivWithin j (fun t => k (t,t*r)) (Icc 0 T) t =
      (iteratedFDeriv ℝ j k (t,t*r)) (fun _ => (1,r)) := by
  obtain ⟨U, hU, htri, hk⟩ := hk
  let g : ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.id ℝ ℝ).prod
    (r • ContinuousLinearMap.id ℝ ℝ)
  have hg : ∀ t, g t = (t,t*r) := by intro t; simp [g, mul_comm]
  have hmaps : Icc (0 : ℝ) T ⊆ g ⁻¹' U := by
    intro s hs
    rw [mem_preimage, hg]
    exact htri ⟨mul_nonneg hs.1 hr.1,
      mul_le_of_le_one_right hs.1 hr.2, hs.2⟩
  have hp := ((hk.ftaylorSeriesWithin hU.uniqueDiffOn).compContinuousLinearMap g).mono hmaps
  have he := hp.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast hj) (uniqueDiffOn_Icc hT) ht
  have hc : ContDiffAt ℝ j k (g t) :=
    (hk.of_le (by exact_mod_cast hj)).contDiffAt (hU.mem_nhds (hmaps ht))
  have hwithin : iteratedFDerivWithin ℝ j k U (g t) = iteratedFDeriv ℝ j k (g t) :=
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hc (hmaps ht)
  simp only [ftaylorSeriesWithin] at he
  rw [hwithin] at he
  have he' := congrArg (fun p : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℝ) 𝕜 =>
    p (fun _ => 1)) he
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, hg, g,
    Function.comp_def, iteratedDerivWithin] using he'.symm






lemma kernel_dilation_derivatives_bound {𝕜 : Type} [RCLike 𝕜] {T : ℝ} {m : ℕ}
    (hT : 0 < T) {k : ℝ × ℝ → 𝕜} (hk : Spec.SmoothKernel m T k) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ∀ r ∈ Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin j (fun t => k (t,t*r)) (Icc 0 T) t‖ ≤ L := by
  obtain ⟨L, hL, hb⟩ := kernel_derivatives_bound hk
  refine ⟨L, hL, ?_⟩
  intro j hj t ht r hr
  rw [kernel_dilation_derivative hT hk hr hj ht]
  apply (ContinuousMultilinearMap.le_opNorm _ _).trans
  have hnorm : ‖((1 : ℝ),r)‖ = (1 : ℝ) := by
    rw [Prod.norm_def, norm_one, Real.norm_of_nonneg hr.1, max_eq_left hr.2]
  simpa [hnorm] using hb j hj (t,t*r)
    ⟨mul_nonneg ht.1 hr.1, mul_le_of_le_one_right ht.1 hr.2, ht.2⟩

lemma kernel_dilation_derivative_continuousOn {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {m j : ℕ} (hT : 0 < T) {k : ℝ × ℝ → 𝕜}
    (hk : Spec.SmoothKernel m T k) (hj : j ≤ m) :
    ContinuousOn (fun z : ℝ × ℝ =>
      iteratedDerivWithin j (fun t => k (t,t*z.2)) (Icc 0 T) z.1)
      (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  have hks := hk
  obtain ⟨U, hU, htri, hk'⟩ := hk
  have he : EqOn (fun z : ℝ × ℝ =>
      iteratedDerivWithin j (fun t => k (t,t*z.2)) (Icc 0 T) z.1)
      (fun z => (iteratedFDeriv ℝ j k (z.1,z.1*z.2)) (fun _ => (1,z.2)))
      (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz
    exact kernel_dilation_derivative hT hks hz.2 hj hz.1
  have hcoord : Continuous (fun z : ℝ × ℝ => (z.1,z.1*z.2)) := by fun_prop
  have hmem : MapsTo (fun z : ℝ × ℝ => (z.1,z.1*z.2))
      (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) U := by
    intro z hz
    exact htri ⟨mul_nonneg hz.1.1 hz.2.1,
      mul_le_of_le_one_right hz.1.1 hz.2.2, hz.1.2⟩
  have hd := (ContinuousOn.continuousOn_iteratedFDeriv hk' hU
    (by exact_mod_cast hj)).comp hcoord.continuousOn hmem
  have hv : Continuous (fun z : ℝ × ℝ => fun _ : Fin j => ((1 : ℝ),z.2)) := by fun_prop
  exact (hd.eval hv.continuousOn).congr he



open WeakVolterraResolvent (betaWeight betaWeight_integrable integral_betaWeight betaWeight_nonneg)



lemma norm_beta_integral_le_bound {𝕜 : Type} [RCLike 𝕜]
    {α β A : ℝ} (hα : 0 < α) (hβ : 0 < β) (g : ℝ → 𝕜)
    (hg : ∀ r ∈ Ioc (0 : ℝ) 1, ‖g r‖ ≤ A) :
    ‖∫ r in Ioc (0 : ℝ) 1, betaWeight α β r • g r‖ ≤
      A * (Real.Gamma α * Real.Gamma β / Real.Gamma (α+β)) := by
  calc
    _ ≤ ∫ r in Ioc (0 : ℝ) 1, betaWeight α β r * A := by
      apply norm_integral_le_of_norm_le ((betaWeight_integrable hα hβ).mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [norm_smul, Real.norm_of_nonneg (betaWeight_nonneg hr)]
      exact mul_le_mul_of_nonneg_left (hg r hr) (betaWeight_nonneg hr)
    _ = _ := by rw [integral_mul_const, integral_betaWeight hα hβ, mul_comm]

lemma gamma_mass_step {α : ℝ} (hα : 0 < α) (n : ℕ) :
    (Real.Gamma α ^ n / Real.Gamma ((n : ℝ)*α+1)) *
        (Real.Gamma α * Real.Gamma ((n : ℝ)*α+1) /
          Real.Gamma (α+((n : ℝ)*α+1))) =
      Real.Gamma α ^ (n+1) / Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) := by
  have hb : 0 < (n : ℝ)*α+1 := by positivity
  have he : α+((n : ℝ)*α+1) = ((n+1 : ℕ) : ℝ)*α+1 := by push_cast; ring
  rw [he, pow_succ]
  field_simp [(Real.Gamma_pos_of_pos hb).ne']

lemma rescaledIterate_norm_bound {𝕜 : Type} [RCLike 𝕜]
    {α T M A : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜)
    (hk : ∀ z ∈ WeakVolterraBounds.Spec.triangle T, ‖k z‖ ≤ M)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, ‖f t‖ ≤ A) (n : ℕ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖rescaledIterate α k f n t‖ ≤
        A * (M * Real.Gamma α)^n / Real.Gamma ((n : ℝ)*α+1) := by
  induction n with
  | zero =>
    intro t ht
    simpa [rescaledIterate] using hf t ht
  | succ n ih =>
    intro t ht
    have hb : 0 < (n : ℝ)*α+1 := by positivity
    have he : α+((n : ℝ)*α+1) = ((n+1 : ℕ) : ℝ)*α+1 := by push_cast; ring
    have htr (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) : t*r ∈ Icc (0 : ℝ) T :=
      ⟨mul_nonneg ht.1 hr.1.le,
        (mul_le_of_le_one_right ht.1 hr.2).trans ht.2⟩
    have hkt (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) :
        (t,t*r) ∈ WeakVolterraBounds.Spec.triangle T :=
      ⟨(htr r hr).1, mul_le_of_le_one_right ht.1 hr.2, ht.2⟩
    change ‖∫ r in Ioc (0 : ℝ) 1, betaWeight α ((n : ℝ)*α+1) r •
      (k (t,t*r) * rescaledIterate α k f n (t*r))‖ ≤ _
    calc
      _ ≤ (M * (A * (M * Real.Gamma α)^n / Real.Gamma ((n : ℝ)*α+1))) *
          (Real.Gamma α * Real.Gamma ((n : ℝ)*α+1) /
            Real.Gamma (α+((n : ℝ)*α+1))) := by
        apply norm_beta_integral_le_bound hα hb
        intro r hr
        rw [norm_mul]
        exact mul_le_mul (hk _ (hkt r hr)) (ih _ (htr r hr))
          (norm_nonneg _) hM
      _ = _ := by
        rw [he, pow_succ]
        field_simp [(Real.Gamma_pos_of_pos hb).ne']

lemma norm_binomial_product_sum_le {𝕜 : Type} [RCLike 𝕜]
    {L B : ℝ} (hL : 0 ≤ L) (_hB : 0 ≤ B) (j : ℕ)
    (a b : ℕ → 𝕜) (ha : ∀ i ≤ j, ‖a i‖ ≤ L) (hb : ∀ i ≤ j, ‖b i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (j+1), (j.choose i : 𝕜) * a i * b (j-i)‖ ≤
      (2 : ℝ)^j * L * B := by
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), ‖(j.choose i : 𝕜) * a i * b (j-i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * L * B := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [norm_mul, RCLike.norm_natCast]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (ha i (by simpa using hi)) (by positivity))
        (hb (j-i) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (by positivity) hL)
    _ = (2 : ℝ)^j * L * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum,
        Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

lemma norm_binomial_product_sum_le_uniform {𝕜 : Type} [RCLike 𝕜]
    {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) {j m : ℕ} (hj : j ≤ m)
    (a b : ℕ → 𝕜) (ha : ∀ i ≤ j, ‖a i‖ ≤ L) (hb : ∀ i ≤ j, ‖b i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (j+1), (j.choose i : 𝕜) * a i * b (j-i)‖ ≤
      (2 : ℝ)^m * L * B := by
  exact (norm_binomial_product_sum_le hL hB j a b ha hb).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hL) hB)

/-- An abstract derivative jet obeying the exact beta-rescaled product rule
has a uniform exponential/Gamma bound. The time interval is closed, so the
statement also controls the derivative values at its two endpoints. -/
lemma beta_jet_recursion_bound {𝕜 : Type} [RCLike 𝕜]
    {α T L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) (m : ℕ)
    (H : ℕ → ℕ → ℝ → 𝕜) (K : ℕ → ℝ → ℝ → 𝕜)
    (hzero : ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T, ‖H 0 j t‖ ≤ L)
    (hK : ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ∀ r ∈ Ioc (0 : ℝ) 1, ‖K j t r‖ ≤ L)
    (hrec : ∀ n j, j ≤ m → ∀ t ∈ Icc (0 : ℝ) T,
      H (n+1) j t = ∫ r in Ioc (0 : ℝ) 1,
        betaWeight α ((n : ℝ)*α+1) r •
          ∑ i ∈ Finset.range (j+1), (j.choose i : 𝕜) * K i t r *
            ((r^(j-i)) • H n (j-i) (t*r))) (n : ℕ) :
    ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ‖H n j t‖ ≤ L * ((2 : ℝ)^m * L * Real.Gamma α)^n /
        Real.Gamma ((n : ℝ)*α+1) := by
  induction n with
  | zero =>
    intro j hj t ht
    simpa using hzero j hj t ht
  | succ n ih =>
    intro j hj t ht
    have hb : 0 < (n : ℝ)*α+1 := by positivity
    have he : α+((n : ℝ)*α+1) = ((n+1 : ℕ) : ℝ)*α+1 := by push_cast; ring
    have hB : 0 ≤ L * ((2 : ℝ)^m * L * Real.Gamma α)^n /
        Real.Gamma ((n : ℝ)*α+1) := by
      positivity [Real.Gamma_pos_of_pos hb, Real.Gamma_pos_of_pos hα]
    rw [hrec n j hj t ht]
    calc
      _ ≤ ((2 : ℝ)^m * L *
          (L * ((2 : ℝ)^m * L * Real.Gamma α)^n /
            Real.Gamma ((n : ℝ)*α+1))) *
          (Real.Gamma α * Real.Gamma ((n : ℝ)*α+1) /
            Real.Gamma (α+((n : ℝ)*α+1))) := by
        apply norm_beta_integral_le_bound hα hb
        intro r hr
        apply norm_binomial_product_sum_le_uniform hL hB hj
          (fun i => K i t r) (fun i => (r^i) • H n i (t*r))
        · intro i hi
          exact hK i (hi.trans hj) t ht r hr
        · intro i hi
          have htr : t*r ∈ Icc (0 : ℝ) T :=
            ⟨mul_nonneg ht.1 hr.1.le,
              (mul_le_of_le_one_right ht.1 hr.2).trans ht.2⟩
          rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hr.1.le _)]
          exact (mul_le_mul_of_nonneg_left (ih i (hi.trans hj) _ htr)
            (pow_nonneg hr.1.le _)).trans
              (mul_le_of_le_one_left hB (pow_le_one₀ hr.1.le hr.2))
      _ = _ := by
        rw [he, pow_succ]
        field_simp [(Real.Gamma_pos_of_pos hb).ne']

lemma rescaled_dilation_mapsTo {T r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    MapsTo (fun t => t*r) (Icc (0 : ℝ) T) (Icc (0 : ℝ) T) := by
  intro t ht
  exact ⟨mul_nonneg ht.1 hr.1,
    (mul_le_of_le_one_right ht.1 hr.2).trans ht.2⟩

lemma iteratedDerivWithin_dilation {𝕜 : Type} [RCLike 𝕜] {T : ℝ} {j : ℕ}
    (hT : 0 < T) {H : ℝ → 𝕜} (hH : ContDiffOn ℝ j H (Icc 0 T))
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) T) :
    iteratedDerivWithin j (fun t => H (t*r)) (Icc 0 T) t =
      r^j • iteratedDerivWithin j H (Icc 0 T) (t*r) := by
  simpa only [mul_comm r] using
    iteratedDerivWithin_comp_const_smul ht (uniqueDiffOn_Icc hT) hH r
      (show MapsTo (r * ·) (Icc (0 : ℝ) T) (Icc (0 : ℝ) T) from
        fun t ht => by simpa only [mul_comm r] using rescaled_dilation_mapsTo hr ht)

lemma continuousOn_dilation_derivative {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {m : ℕ} (hT : 0 < T) {H : ℝ → 𝕜}
    (hH : ContDiffOn ℝ m H (Icc 0 T)) (j : ℕ) (hj : j ≤ m) :
    ContinuousOn (fun z : ℝ × ℝ =>
      iteratedDerivWithin j (fun t => H (t*z.2)) (Icc 0 T) z.1)
      ((Icc (0 : ℝ) T) ×ˢ Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn (fun z : ℝ × ℝ =>
      z.2^j • iteratedDerivWithin j H (Icc 0 T) (z.1*z.2))
      ((Icc (0 : ℝ) T) ×ˢ Icc (0 : ℝ) 1) :=
    (continuous_snd.pow j).continuousOn.smul
      ((hH.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Icc hT)).comp'
        (continuous_fst.mul continuous_snd).continuousOn
        (fun z hz => rescaled_dilation_mapsTo hz.2 hz.1))
  exact hc.congr (fun z hz =>
    iteratedDerivWithin_dilation hT (hH.of_le (by exact_mod_cast hj)) hz.2 hz.1)

lemma iteratedDerivWithin_rescaled_product {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {j : ℕ} (hT : 0 < T) (k : ℝ × ℝ → 𝕜) (H : ℝ → 𝕜)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) T)
    (hk : ContDiffOn ℝ j (fun t => k (t,t*r)) (Icc 0 T))
    (hH : ContDiffOn ℝ j H (Icc 0 T)) :
    iteratedDerivWithin j (fun t => k (t,t*r) * H (t*r)) (Icc 0 T) t =
      ∑ i ∈ Finset.range (j+1), (j.choose i : 𝕜) *
        iteratedDerivWithin i (fun t => k (t,t*r)) (Icc 0 T) t *
          (r^(j-i) • iteratedDerivWithin (j-i) H (Icc 0 T) (t*r)) := by
  have hcomp : ContDiffOn ℝ j (fun t => H (t*r)) (Icc 0 T) :=
    hH.comp (by fun_prop) (rescaled_dilation_mapsTo hr)
  change iteratedDerivWithin j ((fun t => k (t,t*r)) * (fun t => H (t*r))) (Icc 0 T) t = _
  rw [iteratedDerivWithin_mul ht (uniqueDiffOn_Icc hT) (hk t ht) (hcomp t ht)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDerivWithin_dilation hT
    (hH.of_le (by exact_mod_cast Nat.sub_le j i)) hr ht]

lemma continuousOn_rescaled_product_derivative {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {m : ℕ} (hT : 0 < T) (k : ℝ × ℝ → 𝕜) (H : ℝ → 𝕜)
    (hk : ∀ r ∈ Icc (0 : ℝ) 1,
      ContDiffOn ℝ m (fun t => k (t,t*r)) (Icc 0 T))
    (hK : ∀ j ≤ m, ContinuousOn (fun z : ℝ × ℝ =>
      iteratedDerivWithin j (fun t => k (t,t*z.2)) (Icc 0 T) z.1)
      ((Icc (0 : ℝ) T) ×ˢ Icc (0 : ℝ) 1))
    (hH : ContDiffOn ℝ m H (Icc 0 T)) (j : ℕ) (hj : j ≤ m) :
    ContinuousOn (fun z : ℝ × ℝ =>
      iteratedDerivWithin j (fun t => k (t,t*z.2) * H (t*z.2)) (Icc 0 T) z.1)
      ((Icc (0 : ℝ) T) ×ˢ Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn (fun z : ℝ × ℝ =>
      ∑ i ∈ Finset.range (j+1), (j.choose i : 𝕜) *
        iteratedDerivWithin i (fun t => k (t,t*z.2)) (Icc 0 T) z.1 *
          iteratedDerivWithin (j-i) (fun t => H (t*z.2)) (Icc 0 T) z.1)
      ((Icc (0 : ℝ) T) ×ˢ Icc (0 : ℝ) 1) := by
    apply continuousOn_finsetSum
    intro i hi
    exact (continuous_const.continuousOn.mul
      (hK i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj))).mul
        (continuousOn_dilation_derivative hT hH (j-i) ((Nat.sub_le _ _).trans hj))
  apply hc.congr
  intro z hz
  have hcomp : ContDiffOn ℝ j (fun t => H (t*z.2)) (Icc 0 T) :=
    (hH.of_le (by exact_mod_cast hj)).comp (by fun_prop) (rescaled_dilation_mapsTo hz.2)
  change iteratedDerivWithin j ((fun t => k (t,t*z.2)) * (fun t => H (t*z.2)))
    (Icc 0 T) z.1 = _
  exact iteratedDerivWithin_mul hz.1 (uniqueDiffOn_Icc hT)
    (((hk z.2 hz.2).of_le (by exact_mod_cast hj)) z.1 hz.1) (hcomp z.1 hz.1)

lemma norm_iteratedDerivWithin_rescaled_product_le {𝕜 : Type} [RCLike 𝕜]
    {T L B : ℝ} {m j : ℕ} (hT : 0 < T) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (k : ℝ × ℝ → 𝕜) (H : ℝ → 𝕜) (hj : j ≤ m)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) T)
    (hk : ContDiffOn ℝ m (fun t => k (t,t*r)) (Icc 0 T))
    (hH : ContDiffOn ℝ m H (Icc 0 T))
    (hkb : ∀ i ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin i (fun t => k (t,t*r)) (Icc 0 T) t‖ ≤ L)
    (hHb : ∀ i ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin i H (Icc 0 T) t‖ ≤ B) :
    ‖iteratedDerivWithin j (fun t => k (t,t*r) * H (t*r)) (Icc 0 T) t‖ ≤
      (2 : ℝ)^m * L * B := by
  rw [iteratedDerivWithin_rescaled_product hT k H hr ht
    (hk.of_le (by exact_mod_cast hj)) (hH.of_le (by exact_mod_cast hj))]
  apply norm_binomial_product_sum_le_uniform hL hB hj
    (fun i => iteratedDerivWithin i (fun t => k (t,t*r)) (Icc 0 T) t)
    (fun i => r^i • iteratedDerivWithin i H (Icc 0 T) (t*r))
  · intro i hi
    exact hkb i (hi.trans hj) t ht
  · intro i hi
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hr.1 _)]
    exact (mul_le_mul_of_nonneg_left
      (hHb i (hi.trans hj) _ (rescaled_dilation_mapsTo hr ht))
      (pow_nonneg hr.1 _)).trans
        (mul_le_of_le_one_left hB (pow_le_one₀ hr.1 hr.2))





set_option maxHeartbeats 1000000 in
lemma beta_rescaled_product_step {𝕜 : Type} [RCLike 𝕜]
    {α β T L B : ℝ} {m : ℕ} (hα : 0 < α) (hβ : 0 < β)
    (hT : 0 < T) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (k : ℝ × ℝ → 𝕜) (H : ℝ → 𝕜)
    (hk : ∀ r ∈ Icc (0 : ℝ) 1,
      ContDiffOn ℝ m (fun t => k (t,t*r)) (Icc 0 T))
    (hK : ∀ j ≤ m, ContinuousOn (fun z : ℝ × ℝ =>
      iteratedDerivWithin j (fun t => k (t,t*z.2)) (Icc 0 T) z.1)
      (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1))
    (hH : ContDiffOn ℝ m H (Icc 0 T))
    (hkb : ∀ j ≤ m, ∀ r ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin j (fun t => k (t,t*r)) (Icc 0 T) t‖ ≤ L)
    (hHb : ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin j H (Icc 0 T) t‖ ≤ B) :
    let Q : ℝ → 𝕜 := fun t => ∫ r in Ioc (0 : ℝ) 1,
      betaWeight α β r • (k (t,t*r) * H (t*r))
    ContDiffOn ℝ m Q (Icc 0 T) ∧
    (∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      iteratedDerivWithin j Q (Icc 0 T) t =
        ∫ r in Ioc (0 : ℝ) 1, betaWeight α β r •
          ∑ i ∈ Finset.range (j+1), (j.choose i : 𝕜) *
            iteratedDerivWithin i (fun t => k (t,t*r)) (Icc 0 T) t *
              (r^(j-i) • iteratedDerivWithin (j-i) H (Icc 0 T) (t*r))) ∧
    (∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin j Q (Icc 0 T) t‖ ≤
        ((2 : ℝ)^m * L * B) *
          (Real.Gamma α * Real.Gamma β / Real.Gamma (α+β))) := by
  dsimp only
  have hPb (j : ℕ) (hj : j ≤ m) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖iteratedDerivWithin j (fun t => k (t,t*r) * H (t*r)) (Icc 0 T) t‖ ≤
        (2 : ℝ)^m * L * B :=
    norm_iteratedDerivWithin_rescaled_product_le hT hL hB k H hj hr ht (hk r hr) hH
      (fun i hi t ht => hkb i hi r hr t ht) hHb
  have hPi := VolterraSmoothness.contDiffOn_weighted_integral
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (P := fun r t => k (t,t*r) * H (t*r)) (w := betaWeight α β)
    (C := fun _ => (2 : ℝ)^m * L * B) hT (betaWeight_integrable hα hβ)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact (hk r (Ioc_subset_Icc_self hr)).mul
        (hH.comp (by fun_prop) (rescaled_dilation_mapsTo (Ioc_subset_Icc_self hr))))
    (by
      intro j hj t ht
      have hc : ContinuousOn (fun r =>
          iteratedDerivWithin j (fun t => k (t,t*r) * H (t*r)) (Icc 0 T) t) (Icc 0 1) :=
        (continuousOn_rescaled_product_derivative hT k H hk hK hH j hj).comp
          (f := fun r : ℝ => (t,r))
          (continuous_const.continuousOn.prodMk continuousOn_id)
          (fun r hr => ⟨ht,hr⟩)
      exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (by
      intro j hj
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr t ht
      exact hPb j hj r (Ioc_subset_Icc_self hr) t ht)
  refine ⟨hPi.1, ?_, ?_⟩
  · intro j hj t ht
    rw [hPi.2 j hj t ht]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    rw [iteratedDerivWithin_rescaled_product hT k H (Ioc_subset_Icc_self hr) ht
      ((hk r (Ioc_subset_Icc_self hr)).of_le (by exact_mod_cast hj))
      (hH.of_le (by exact_mod_cast hj))]
  · intro j hj t ht
    rw [hPi.2 j hj t ht]
    exact norm_beta_integral_le_bound hα hβ _
      (fun r hr => hPb j hj r (Ioc_subset_Icc_self hr) t ht)





lemma rescaledIterate_contDiffOn_and_bound {𝕜 : Type} [RCLike 𝕜]
    {α T L : ℝ} {m : ℕ} (hα : 0 < α) (hT : 0 < T) (hL : 0 ≤ L)
    (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜)
    (hf : ContDiffOn ℝ m f (Icc 0 T))
    (hk : ∀ r ∈ Icc (0 : ℝ) 1,
      ContDiffOn ℝ m (fun t => k (t,t*r)) (Icc 0 T))
    (hK : ∀ j ≤ m, ContinuousOn (fun z : ℝ × ℝ =>
      iteratedDerivWithin j (fun t => k (t,t*z.2)) (Icc 0 T) z.1)
      ((Icc (0 : ℝ) T) ×ˢ Icc (0 : ℝ) 1))
    (hfb : ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin j f (Icc 0 T) t‖ ≤ L)
    (hkb : ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
      ∀ r ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin j (fun t => k (t,t*r)) (Icc 0 T) t‖ ≤ L) (n : ℕ) :
    ContDiffOn ℝ m (rescaledIterate α k f n) (Icc 0 T) ∧
      ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) T,
        ‖iteratedDerivWithin j (rescaledIterate α k f n) (Icc 0 T) t‖ ≤
          L * ((2 : ℝ)^m * L * Real.Gamma α)^n /
            Real.Gamma ((n : ℝ)*α+1) := by
  induction n with
  | zero =>
    refine ⟨hf, ?_⟩
    intro j hj t ht
    simpa [rescaledIterate] using hfb j hj t ht
  | succ n ih =>
    have hb : 0 < (n : ℝ)*α+1 := by positivity
    have hB : 0 ≤ L * ((2 : ℝ)^m * L * Real.Gamma α)^n /
        Real.Gamma ((n : ℝ)*α+1) := by
      positivity [Real.Gamma_pos_of_pos hb, Real.Gamma_pos_of_pos hα]
    obtain ⟨hs, hd, hbnd⟩ := beta_rescaled_product_step hα hb hT hL hB
      k (rescaledIterate α k f n) hk hK ih.1
      (fun j hj r hr t ht => hkb j hj t ht r hr) ih.2
    refine ⟨hs, ?_⟩
    intro j hj t ht
    have hh := hbnd j hj t ht
    have he : α+((n : ℝ)*α+1) = ((n+1 : ℕ) : ℝ)*α+1 := by push_cast; ring
    apply hh.trans_eq
    rw [he, pow_succ]
    field_simp [(Real.Gamma_pos_of_pos hb).ne']

lemma rescaledIterate_smooth_gamma_bounds {𝕜 : Type} [RCLike 𝕜]
    {α T : ℝ} {m : ℕ} (hα : 0 < α) (hT : 0 < T)
    (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜)
    (hk : Spec.SmoothKernel m T k) (hf : ContDiffOn ℝ m f (Icc 0 T)) :
    ∃ D c : ℝ, 0 ≤ D ∧ 0 ≤ c ∧
      (∀ n, ContDiffOn ℝ m (rescaledIterate α k f n) (Icc 0 T)) ∧
      ∀ j ≤ m, ∀ n, ∀ t ∈ Icc (0 : ℝ) T,
        ‖iteratedDerivWithin j (rescaledIterate α k f n) (Icc 0 T) t‖ ≤
          D * c^n / Real.Gamma ((n : ℝ)*α+1) := by
  obtain ⟨Lf, hLf, hfb⟩ := datum_derivatives_bound hT hf
  obtain ⟨Lk, hLk, hkb⟩ := kernel_dilation_derivatives_bound hT hk
  let L := max Lf Lk
  have hL : 0 ≤ L := zero_le_one.trans (hLf.trans (le_max_left _ _))
  have hh := rescaledIterate_contDiffOn_and_bound hα hT hL k f hf
    (fun r hr => kernel_dilation_contDiffOn hk hr)
    (fun j hj => kernel_dilation_derivative_continuousOn hT hk hj)
    (fun j hj t ht => (hfb j hj t ht).trans (le_max_left _ _))
    (fun j hj t ht r hr => (hkb j hj t ht r hr).trans (le_max_right _ _))
  refine ⟨L, (2 : ℝ)^m * L * Real.Gamma α, hL,
    by positivity [Real.Gamma_pos_of_pos hα], fun n => (hh n).1, ?_⟩
  intro j hj n t ht
  exact (hh n).2 j hj t ht


lemma norm_descPochhammer_eval_le (p : ℝ) (j : ℕ) :
    ‖(descPochhammer ℝ j).eval p‖ ≤ (‖p‖+(j : ℝ))^j := by
  rw [descPochhammer_eval_eq_prod_range, norm_prod]
  calc
    ∏ i ∈ Finset.range j, ‖p-(i : ℝ)‖ ≤
        ∏ i ∈ Finset.range j, (‖p‖+(j : ℝ)) := by
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => ?_)
      calc
        ‖p-(i : ℝ)‖ ≤ ‖p‖+‖(i : ℝ)‖ := norm_sub_le _ _
        _ ≤ ‖p‖+(j : ℝ) := by
          simp only [Real.norm_natCast]
          have hij : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_range.mp hi).le
          linarith
    _ = _ := by simp

lemma iteratedDerivWithin_rpow_pos {p T t : ℝ} (j : ℕ)
    (ht : t ∈ Ioc (0 : ℝ) T) :
    iteratedDerivWithin j (fun s : ℝ => s^p) (Ioc 0 T) t =
      (descPochhammer ℝ j).eval p * t^(p-(j : ℝ)) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioc _ _)
    (Real.contDiffAt_rpow_const_of_ne ht.1.ne') ht,
    iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

lemma norm_iteratedDerivWithin_rpow_le {p T t : ℝ} (j : ℕ)
    (ht : t ∈ Ioc (0 : ℝ) T) :
    ‖iteratedDerivWithin j (fun s : ℝ => s^p) (Ioc 0 T) t‖ ≤
      (‖p‖+(j : ℝ))^j * t^(p-(j : ℝ)) := by
  rw [iteratedDerivWithin_rpow_pos j ht, norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  exact mul_le_mul_of_nonneg_right (norm_descPochhammer_eval_le p j)
    (Real.rpow_nonneg ht.1.le _)

lemma norm_iteratedDerivWithin_rpow_smul_le_sum {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ → E} {p T t : ℝ}
    (j : ℕ) (ht : t ∈ Ioc (0 : ℝ) T)
    (hH : ContDiffWithinAt ℝ j H (Ioc 0 T) t) :
    ‖iteratedDerivWithin j (fun s : ℝ => s^p • H s) (Ioc 0 T) t‖ ≤
      ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) *
        ((‖p‖+(i : ℝ))^i * t^(p-(i : ℝ))) *
        ‖iteratedDerivWithin (j-i) H (Ioc 0 T) t‖ := by
  have hp : ContDiffWithinAt ℝ j (fun s : ℝ => s^p) (Ioc 0 T) t :=
    (Real.contDiffAt_rpow_const_of_ne ht.1.ne').contDiffWithinAt
  change ‖iteratedDerivWithin j ((fun s : ℝ => s^p) • H) (Ioc 0 T) t‖ ≤ _
  rw [iteratedDerivWithin_smul ht (uniqueDiffOn_Ioc _ _) hp hH]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  apply norm_nsmul_le.trans
  rw [norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_iteratedDerivWithin_rpow_le i ht)
      (Nat.cast_nonneg _)) (norm_nonneg _)

/-- A uniform bound on finitely many derivatives of the rescaled amplitude
turns into a weighted derivative bound for the original iterate. -/
lemma norm_iteratedDerivWithin_rpow_smul_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ → E} {p T t B : ℝ}
    (j : ℕ) (ht : t ∈ Ioc (0 : ℝ) T) (_hB : 0 ≤ B)
    (hH : ContDiffWithinAt ℝ j H (Ioc 0 T) t)
    (hHbound : ∀ i ≤ j, ‖iteratedDerivWithin i H (Ioc 0 T) t‖ ≤ B) :
    ‖iteratedDerivWithin j (fun s : ℝ => s^p • H s) (Ioc 0 T) t‖ ≤
      (2 : ℝ)^j * (‖p‖+(j : ℝ)+1)^j * (max 1 T)^j * B *
        t^(p-(j : ℝ)) := by
  let Q : ℝ := ‖p‖+(j : ℝ)+1
  let R : ℝ := max 1 T
  have hQ : 1 ≤ Q := by
    change 1 ≤ ‖p‖+(j : ℝ)+1
    have := norm_nonneg p
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hR : 1 ≤ R := le_max_left _ _
  have hq0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hr0 : 0 ≤ R := le_trans zero_le_one hR
  have hR' : t ≤ R := ht.2.trans (le_max_right _ _)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (j+1)) :
      ((‖p‖+(i : ℝ))^i * t^(p-(i : ℝ))) *
          ‖iteratedDerivWithin (j-i) H (Ioc 0 T) t‖ ≤
        Q^j * R^j * B * t^(p-(j : ℝ)) := by
    have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hp : (‖p‖+(i : ℝ))^i ≤ Q^j := by
      apply (pow_le_pow_left₀ (by positivity) (show ‖p‖+(i : ℝ) ≤ Q by
        dsimp [Q]
        have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
        linarith) i).trans
      exact pow_le_pow_right₀ hQ hij
    have ht1 : t^((j-i : ℕ) : ℝ) ≤ R^j := by
      rw [Real.rpow_natCast]
      exact (pow_le_pow_left₀ ht.1.le hR' (j-i)).trans
        (pow_le_pow_right₀ hR (Nat.sub_le _ _))
    have he : p-(i : ℝ) = (p-(j : ℝ))+((j-i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hij]; ring
    rw [he, Real.rpow_add ht.1]
    calc
      ((‖p‖+(i : ℝ))^i * (t^(p-(j : ℝ))*t^((j-i : ℕ) : ℝ))) *
          ‖iteratedDerivWithin (j-i) H (Ioc 0 T) t‖ ≤
        (Q^j * (t^(p-(j : ℝ))*R^j)) * B := by
          apply mul_le_mul
          · exact mul_le_mul hp
              (mul_le_mul_of_nonneg_left ht1 (Real.rpow_nonneg ht.1.le _))
              (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg ht.1.le _)) (pow_nonneg hq0 _)
          · exact hHbound _ (Nat.sub_le _ _)
          · exact norm_nonneg _
          · exact mul_nonneg (pow_nonneg hq0 _)
              (mul_nonneg (Real.rpow_nonneg ht.1.le _) (pow_nonneg hr0 _))
      _ = _ := by ring
  calc
    ‖iteratedDerivWithin j (fun s : ℝ => s^p • H s) (Ioc 0 T) t‖ ≤
      ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) *
        ((‖p‖+(i : ℝ))^i * t^(p-(i : ℝ))) *
        ‖iteratedDerivWithin (j-i) H (Ioc 0 T) t‖ :=
          norm_iteratedDerivWithin_rpow_smul_le_sum j ht hH
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) *
        (Q^j * R^j * B * t^(p-(j : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hterm i hi) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      dsimp [Q, R]
      ring

lemma norm_iteratedDerivWithin_rpow_nat_mul_smul_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ → E} {α T t B : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (n j : ℕ) (hn : 1 ≤ n)
    (ht : t ∈ Ioc (0 : ℝ) T) (hB : 0 ≤ B)
    (hH : ContDiffWithinAt ℝ j H (Ioc 0 T) t)
    (hHbound : ∀ i ≤ j, ‖iteratedDerivWithin i H (Ioc 0 T) t‖ ≤ B) :
    ‖iteratedDerivWithin j (fun s : ℝ => s^((n : ℝ)*α) • H s) (Ioc 0 T) t‖ ≤
      ((2 : ℝ)^j * ((j : ℝ)+2)^j * (max 1 T)^j) * (n : ℝ)^j * B *
        t^((n : ℝ)*α-(j : ℝ)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hj' : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hp : ‖(n : ℝ)*α‖+(j : ℝ)+1 ≤ (n : ℝ)*((j : ℝ)+2) := by
    rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hα)]
    have hna : (n : ℝ)*α ≤ n := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (by linarith : 0 ≤ (j : ℝ)+1)]
  apply (norm_iteratedDerivWithin_rpow_smul_le j ht hB hH hHbound).trans
  have hpow := pow_le_pow_left₀ (by positivity) hp j
  calc
    (2 : ℝ)^j * (‖(n : ℝ)*α‖+(j : ℝ)+1)^j * (max 1 T)^j * B *
        t^((n : ℝ)*α-(j : ℝ)) ≤
      (2 : ℝ)^j * ((n : ℝ)*((j : ℝ)+2))^j * (max 1 T)^j * B *
        t^((n : ℝ)*α-(j : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.1.le _)
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [mul_pow]; ring

lemma contDiffOn_rpow_smul_pos {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ → E} {p T : ℝ}
    {m : ℕ} (hH : ContDiffOn ℝ m H (Ioc 0 T)) :
    ContDiffOn ℝ m (fun t => t^p • H t) (Ioc 0 T) := by
  apply ContDiffOn.smul _ hH
  intro t ht
  exact (Real.contDiffAt_rpow_const_of_ne ht.1.ne').contDiffWithinAt

/-- Gamma bounds for uniformly bounded derivatives of the rescaled iterates
supply the polynomial/Gamma bounds required by the differentiated series. -/
lemma norm_neumann_rescaled_deriv_le {𝕜 : Type*} [RCLike 𝕜]
    {H : ℕ → ℝ → 𝕜} {α T D c : ℝ} {m : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hH : ∀ n, ContDiffOn ℝ m (H n) (Ioc 0 T))
    (hHbound : ∀ i ≤ m, ∀ n, 1 ≤ n → ∀ t ∈ Ioc (0 : ℝ) T,
      ‖iteratedDerivWithin i (H n) (Ioc 0 T) t‖ ≤
        D * c^n / Real.Gamma ((n : ℝ)*α+1))
    (ζ : 𝕜) (j : ℕ) (hj : j ≤ m) (n : ℕ) (hn : 1 ≤ n)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) :
    ‖iteratedDerivWithin j (fun s => ζ^n * (s^((n : ℝ)*α) • H n s))
        (Ioc 0 T) t‖ ≤
      (((2 : ℝ)^j * ((j : ℝ)+2)^j * (max 1 T)^j) * D) *
        (n : ℝ)^j * (‖ζ‖*c)^n / Real.Gamma ((n : ℝ)*α+1) *
          t^((n : ℝ)*α-(j : ℝ)) := by
  rw [iteratedDerivWithin_const_mul_field, norm_mul, norm_pow]
  have hB : 0 ≤ D * c^n / Real.Gamma ((n : ℝ)*α+1) :=
    div_nonneg (mul_nonneg hD (pow_nonneg hc _))
      (Real.Gamma_pos_of_pos (by positivity)).le
  have hd := norm_iteratedDerivWithin_rpow_nat_mul_smul_le hα.le hα1 n j hn ht hB
    ((hH n t ht).of_le (by exact_mod_cast hj))
    (fun i hi => hHbound i (hi.trans hj) n hn t ht)
  apply (mul_le_mul_of_nonneg_left hd (pow_nonneg (norm_nonneg ζ) _)).trans_eq
  simp only [div_eq_mul_inv, mul_pow]
  ring

lemma iteratedDerivWithin_Ioc_eq_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ → E} {T : ℝ}
    {m : ℕ} (hT : 0 < T) (hH : ContDiffOn ℝ m H (Icc 0 T))
    (j : ℕ) (hj : j ≤ m) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) :
    iteratedDerivWithin j H (Ioc 0 T) t = iteratedDerivWithin j H (Icc 0 T) t := by
  unfold iteratedDerivWithin
  rw [iteratedFDerivWithin_subset Ioc_subset_Icc_self
    (uniqueDiffOn_Ioc _ _) (uniqueDiffOn_Icc hT) (hH.of_le (by exact_mod_cast hj)) ht]

lemma finite_iterate_estimates_of_rescaled_bounds {𝕜 : Type*} [RCLike 𝕜]
    {H A : ℕ → ℝ → 𝕜} {α T D c : ℝ} {m : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hT : 0 < T) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (hH : ∀ n, ContDiffOn ℝ m (H n) (Icc 0 T))
    (hHbound : ∀ i ≤ m, ∀ n, 1 ≤ n → ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin i (H n) (Icc 0 T) t‖ ≤
        D * c^n / Real.Gamma ((n : ℝ)*α+1))
    (ζ : 𝕜)
    (hA : ∀ n t, t ∈ Ioc (0 : ℝ) T →
      A n t = ζ^(n+1) * (t^(((n+1 : ℕ) : ℝ)*α) • H (n+1) t)) :
    (∀ n, ContDiffOn ℝ m (A n) (Ioc 0 T)) ∧
      ∀ j ≤ m, ∃ (D' c' : ℝ) (d : ℕ), 0 ≤ D' ∧ 0 ≤ c' ∧
        ∀ n t, t ∈ Ioc (0 : ℝ) T →
          ‖iteratedDerivWithin j (A n) (Ioc 0 T) t‖ ≤
            D' * ((n+1 : ℕ) : ℝ)^d * c'^(n+1) /
              Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) *
                t^(((n+1 : ℕ) : ℝ)*α-(j : ℝ)) := by
  have hH' (n : ℕ) : ContDiffOn ℝ m (H n) (Ioc 0 T) :=
    (hH n).mono Ioc_subset_Icc_self
  have hHbound' : ∀ i ≤ m, ∀ n, 1 ≤ n → ∀ t ∈ Ioc (0 : ℝ) T,
      ‖iteratedDerivWithin i (H n) (Ioc 0 T) t‖ ≤
        D * c^n / Real.Gamma ((n : ℝ)*α+1) := by
    intro i hi n hn t ht
    rw [iteratedDerivWithin_Ioc_eq_Icc hT (hH n) i hi t ht]
    exact hHbound i hi n hn t (Ioc_subset_Icc_self ht)
  constructor
  · intro n
    exact (contDiffOn_const.mul (contDiffOn_rpow_smul_pos (hH' (n+1)))).congr
      (fun t ht => hA n t ht)
  · intro j hj
    refine ⟨((2 : ℝ)^j * ((j : ℝ)+2)^j * (max 1 T)^j) * D,
      ‖ζ‖*c, j, ?_, mul_nonneg (norm_nonneg _) hc, ?_⟩
    · have hmax : 0 ≤ max (1 : ℝ) T := le_trans zero_le_one (le_max_left _ _)
      positivity
    · intro n t ht
      rw [iteratedDerivWithin_congr (hA n) ht]
      exact norm_neumann_rescaled_deriv_le hα hα1 hD hc hH' hHbound' ζ j hj (n+1)
        (by omega) t ht

/-- Smooth rescaled iterates with a uniform Gamma bound give all finite
positive-time derivative estimates for the actual Neumann correction terms. -/
lemma neumann_estimates_of_rescaled_bounds {𝕜 : Type} [RCLike 𝕜]
    {α T D c : ℝ} {m : ℕ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hT : 0 < T) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜)
    (K : C(ExpandedFA.PartV.WeakVolterraBounds.Spec.triangle T, 𝕜))
    (hK : ∀ z, K z = k z.val)
    (F : C(Icc (0 : ℝ) T, 𝕜)) (hF : ∀ t, F t = f t)
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : WeakVolterraResolvent.Spec.ContinuousRealizes hT.le α K V)
    (hH : ∀ n, ContDiffOn ℝ m (rescaledIterate α k f n) (Icc 0 T))
    (hHbound : ∀ i ≤ m, ∀ n, 1 ≤ n → ∀ t ∈ Icc (0 : ℝ) T,
      ‖iteratedDerivWithin i (rescaledIterate α k f n) (Icc 0 T) t‖ ≤
        D * c^n / Real.Gamma ((n : ℝ)*α+1)) (ζ : 𝕜) :
    (∀ n, ContDiffOn ℝ m
      (fun t => ζ^(n+1) * ExpandedFA.PartV.FractionalIntegrals.Spec.continuousExtension
        hT.le ((V^(n+1)) F) t) (Ioc 0 T)) ∧
      ∀ j ≤ m, ∃ (D' c' : ℝ) (d : ℕ), 0 ≤ D' ∧ 0 ≤ c' ∧
        ∀ n t, t ∈ Ioc (0 : ℝ) T →
          ‖iteratedDerivWithin j
              (fun s => ζ^(n+1) * ExpandedFA.PartV.FractionalIntegrals.Spec.continuousExtension
                hT.le ((V^(n+1)) F) s) (Ioc 0 T) t‖ ≤
            D' * ((n+1 : ℕ) : ℝ)^d * c'^(n+1) /
              Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) *
                t^(((n+1 : ℕ) : ℝ)*α-(j : ℝ)) := by
  apply finite_iterate_estimates_of_rescaled_bounds hα hα1 hT hD hc hH hHbound ζ
  intro n t ht
  rw [continuous_iterate_rescaled hT.le k f K hK F hF V hV (n+1) t ht]


/-- Zeroth-order bound for the actual nonzero Neumann terms, with their
full time powers. This needs only continuity of the kernel and datum. -/
lemma norm_neumann_term_le {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(triangle T, 𝕜))
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : WeakVolterraResolvent.Spec.ContinuousRealizes hT α k V)
    (ζ : 𝕜) (f : C(Icc (0 : ℝ) T, 𝕜)) (n : ℕ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖ζ^(n+1) * continuousExtension hT ((V^(n+1)) f) t‖ ≤
      ‖f‖ * (‖ζ‖ * ‖k‖ * Real.Gamma α)^(n+1) /
        Real.Gamma (((n+1 : ℕ) : ℝ)*α+1) * t^(((n+1 : ℕ) : ℝ)*α) := by
  rw [norm_mul, norm_pow, continuousExtension, projIcc_of_mem hT ht]
  calc
    ‖ζ‖^(n+1) * ‖((V^(n+1)) f) ⟨t,ht⟩‖ ≤
        ‖ζ‖^(n+1) * (iterateBound α t ‖k‖ (n+1) * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        (WeakVolterraBounds.continuous_iterate_pointwise hα hT k (norm_nonneg _)
          (fun z => k.norm_coe_le_norm z) V hV (n+1) f ⟨t,ht⟩) (by positivity)
    _ = _ := by dsimp [iterateBound]; rw [mul_pow, mul_pow]; ring

set_option maxHeartbeats 1000000 in
/-- Identify the actual correction u-f with the nonzero Neumann iterates.
The equation here is an equality of continuous functions and the realization
hypothesis fixes V to the manuscript's integral operator. -/
lemma correction_hasSum {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : C(triangle T, 𝕜))
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : WeakVolterraResolvent.Spec.ContinuousRealizes hT α k V)
    (ζ : 𝕜) (f u : C(Icc (0 : ℝ) T, 𝕜))
    (hu : u = f + ζ • V u) (t : Icc (0 : ℝ) T) :
    HasSum (fun n : ℕ => ζ^(n+1) * ((V^(n+1)) f t)) (u t - f t) := by
  have hb := WeakVolterraResolvent.continuous_bounds_of_realizes
    hα hT (norm_nonneg k) k (fun z => k.norm_coe_le_norm z) V hV
  have hN := WeakVolterraBounds.neumann_of_iterate_bound
    hα hT (norm_nonneg k) V hb ζ
  let R := ∑' n : ℕ, ζ^n • V^n
  have heq : (1-ζ • V) u = f := by
    change u - ζ • V u = f
    exact sub_eq_iff_eq_add.mpr hu
  have hRu : R f = u := by
    rw [← heq, ← mul_apply_eq_comp, hN.2.2.1]
    rfl
  have hs : HasSum (fun n : ℕ => ((ζ^n • V^n) f) t) (u t) := by
    rw [← hRu]
    exact (ContinuousMap.evalCLM 𝕜 t).hasSum
      ((ContinuousLinearMap.apply 𝕜 C(Icc (0 : ℝ) T, 𝕜) f).hasSum hN.1.hasSum)
  simpa only [Finset.sum_range_one, pow_zero, one_smul, one_apply_eq_self,
    smul_apply, ContinuousMap.smul_apply, smul_eq_mul, one_mul] using
    (hasSum_nat_add_iff' 1).mpr hs

/-- The smooth kernel hypothesis supplies the actual continuous triangle
amplitude required by the accepted upstream theorem. -/
lemma smoothKernel_continuousOn {𝕜 : Type} [RCLike 𝕜]
    {m : ℕ} {T : ℝ} {k : ℝ × ℝ → 𝕜} (hk : Spec.SmoothKernel m T k) :
    ContinuousOn k (triangle T) := by
  obtain ⟨U, _, hU, hk⟩ := hk
  exact hk.continuousOn.mono hU

/-- Restricting the ambient source functions gives precisely the continuous
operator equation. The clamped extension is used only at s in [0,t]. -/
lemma continuous_equation_of_solution {𝕜 : Type} [RCLike 𝕜]
    {α T : ℝ} (hT : 0 ≤ T) {K : ℝ × ℝ → 𝕜} {f u : ℝ → 𝕜} {ζ : 𝕜}
    (hu : Spec.IsSolution α T K f ζ u)
    (k : C(triangle T, 𝕜)) (hk : ∀ z, k z = K z.val)
    (F U : C(Icc (0 : ℝ) T, 𝕜)) (hF : ∀ t, F t = f t) (hU : ∀ t, U t = u t)
    (V : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜))
    (hV : WeakVolterraResolvent.Spec.ContinuousRealizes hT α k V) :
    U = F + ζ • V U := by
  ext t
  change U t = F t + ζ * (V U t)
  have hint : weakValue α k (continuousExtension hT U) t =
      ∫ s in Ioc 0 (t : ℝ), ((t : ℝ)-s)^(α-1) • (K (t,s) * u s) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans t.property.2⟩
    have hts : ((t : ℝ),s) ∈ triangle T := ⟨hs.1.le, hs.2, t.property.2⟩
    simp only [weakIntegrand, amplitudeValue, dite_eq_left hts,
      continuousExtension, projIcc_of_mem hT hsT, hk, hU]
  rw [hU, hF, hV, hint]
  exact hu.2 t t.property

/-- At order zero, the source conclusion is exactly the continuity already
included in the continuous solution interface. -/
lemma derivative_conclusion_zero {𝕜 : Type} [RCLike 𝕜]
    {α T : ℝ} {f u : ℝ → 𝕜} (hu : ContinuousOn u (Icc 0 T)) :
    Spec.DerivativeConclusion 0 α T f u := by
  refine ⟨contDiffOn_zero.mpr (hu.mono Ioc_subset_Icc_self), ?_⟩
  intro j hj hj0
  omega

/-- No positive-time derivative is asserted on a zero-length interval. -/
lemma derivative_conclusion_zero_time {𝕜 : Type} [RCLike 𝕜]
    (m : ℕ) (α : ℝ) (f u : ℝ → 𝕜) :
    Spec.DerivativeConclusion m α 0 f u := by
  refine ⟨by simp, ?_⟩
  intro j hj hjm
  exact ⟨0, le_rfl, by simp⟩

/-- Finite rescaled iterates supply summable bounds for every derivative.
The resulting series is the correction to the original continuous solution. -/
theorem weighted_derivative_regularity : Spec.WeightedDerivativeRegularity := by
  intro 𝕜 _ α T m hα hα1 hT k f ζ u hk hf hu
  by_cases hT0 : T = 0
  · subst T
    exact derivative_conclusion_zero_time m α f u
  cases m with
  | zero => exact derivative_conclusion_zero hu.1
  | succ m =>
    let K : C(triangle T, 𝕜) :=
      ⟨fun z => k z, continuousOn_iff_continuous_domRestrict.mp
        (smoothKernel_continuousOn hk)⟩
    let F : C(Icc (0 : ℝ) T, 𝕜) :=
      ⟨fun t => f t, continuousOn_iff_continuous_domRestrict.mp hf.continuousOn⟩
    let U : C(Icc (0 : ℝ) T, 𝕜) :=
      ⟨fun t => u t, continuousOn_iff_continuous_domRestrict.mp hu.1⟩
    obtain ⟨V, hV, _⟩ := WeakVolterraBounds.continuous_construction
      α T hα hT K ‖K‖ (norm_nonneg _) (fun z => K.norm_coe_le_norm z)
    have hV' : WeakVolterraResolvent.Spec.ContinuousRealizes hT α K V :=
      fun f t => (hV f t).2
    have hU : U = F + ζ • V U := continuous_equation_of_solution
      hT hu K (fun _ => rfl) F U (fun _ => rfl) (fun _ => rfl) V hV'
    let A : ℕ → ℝ → 𝕜 := fun n t =>
      ζ^(n+1) * continuousExtension hT ((V^(n+1)) F) t
    have hsum : ∀ t ∈ Ioc (0 : ℝ) T,
        HasSum (fun n => A n t) (u t - f t) := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
      convert correction_hasSum hα hT K V hV' ζ F U hU ⟨t, ht'⟩ using 1
      · ext n
        simp only [A, continuousExtension, projIcc_of_mem hT ht']
    have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
    obtain ⟨D, c, hD, hc, hH, hHb⟩ := rescaledIterate_smooth_gamma_bounds
      hα hTpos k f hk hf
    have hiter := neumann_estimates_of_rescaled_bounds hα hα1.le hTpos hD hc
      k f K (fun _ => rfl) F (fun _ => rfl) V hV' hH
      (fun i hi n _ t ht => hHb i hi n t ht) ζ
    exact derivative_conclusion_of_gamma_series hα hf hiter.1 hiter.2 hsum

end ExpandedFA.PartV.WeightedVolterraDerivatives
