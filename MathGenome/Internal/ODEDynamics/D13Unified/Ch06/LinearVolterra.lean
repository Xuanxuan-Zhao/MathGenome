import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.LinearVolterra
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.Gronwall
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal Matrix.Norms.Elementwise

namespace D13Unified.Ch06.LinearVolterra
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma continuousOn_integrand {a b : ℝ} {A : ℝ → E →L[ℝ] E} {B Y : ℝ → E}
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hY : ContinuousOn Y (Icc a b)) :
    ContinuousOn (fun t => A t (Y t) + B t) (Icc a b) :=
  (hA.clm_apply hY).add hB

omit [CompleteSpace E] in
lemma IsIntegralSolution.initial {a b s : ℝ} {A : ℝ → E →L[ℝ] E}
    {B Y : ℝ → E} {ξ : E} (hY : IsIntegralSolution a b s A B ξ Y)
    (hs : s ∈ Icc a b) : Y s = ξ := by
  simpa only [intervalIntegral.integral_same, add_zero] using hY.2 s hs

theorem differential_equivalence :
    Specs.D13Unified.Ch06.LinearVolterra.DifferentialEquivalence.{u} := by
  intro E _ _ _ a b s A B ξ Y hs hA hB
  constructor
  · intro hY
    have hg := continuousOn_integrand hA hB hY.1
    refine ⟨hY.1, hY.initial hs, ?_⟩
    intro t ht
    exact ((D13Unified.hasDerivWithinAt_integral_on_interval ordConnected_Icc hg hs ht
      ).const_add ξ).congr_of_mem (fun r hr => hY.2 r hr) ht
  · rintro ⟨hY, hYs, hd⟩
    refine ⟨hY, ?_⟩
    intro t ht
    rw [D13Unified.integral_eq_sub_on_interval ordConnected_Icc hY
      (continuousOn_integrand hA hB hY) hd hs ht, hYs]
    exact (add_sub_cancel ξ (Y t)).symm

omit [CompleteSpace E] in
/-- An oriented integral equation plus a linear bound on its integrand. -/
lemma norm_bound_of_integral {a b s : ℝ} {Y g : ℝ → E} {ξ : E}
    {L M : ℝ} (hs : s ∈ Icc a b) (hY : ContinuousOn Y (Icc a b))
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (heq : ∀ t ∈ Icc a b, Y t = ξ + ∫ r in s..t, g r)
    (hg : ∀ r ∈ Icc a b, ‖g r‖ ≤ L * ‖Y r‖ + M) :
    ∀ t ∈ Icc a b,
      ‖Y t‖ ≤ ‖ξ‖ * Real.exp (L * |t-s|) + M * Specs.D13Unified.Ch05.Gronwall.EValue L |t-s| := by
  have hcont : ContinuousOn (fun r => L * ‖Y r‖ + M) (Icc a b) :=
    (continuousOn_const.mul hY.norm).add continuousOn_const
  intro t ht
  by_cases hst : s ≤ t
  · have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hineq : ∀ v ∈ Icc s t, ‖Y v‖ ≤ ‖ξ‖ + ∫ r in s..v, (L * ‖Y r‖ + M) := by
      intro v hv
      calc
        ‖Y v‖ = ‖ξ + ∫ r in s..v, g r‖ := congrArg norm (heq v (hsub hv))
        _ ≤ ‖ξ‖ + ‖∫ r in s..v, g r‖ := norm_add_le _ _
        _ ≤ ‖ξ‖ + ∫ r in s..v, (L * ‖Y r‖ + M) := by
          apply add_le_add (le_refl ‖ξ‖)
          apply intervalIntegral.norm_integral_le_of_norm_le hv.1
          · exact Eventually.of_forall (fun r hr => hg r (hsub ⟨hr.1.le, hr.2.trans hv.2⟩))
          · exact (hcont.mono (by
              rw [uIcc_of_le hv.1]
              exact (Icc_subset_Icc le_rfl hv.2).trans hsub)).intervalIntegrable
    have hb := Ch05.Gronwall.constant_forward s t ‖ξ‖ L M (fun r => ‖Y r‖)
      hst (norm_nonneg _) hL hM (hY.norm.mono hsub)
      (fun _ _ => norm_nonneg _) hineq t ⟨hst, le_rfl⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hb
  · have hts : t ≤ s := le_of_not_ge hst
    have hsub : Icc t s ⊆ Icc a b := Icc_subset_Icc ht.1 hs.2
    have hineq : ∀ v ∈ Icc t s, ‖Y v‖ ≤ ‖ξ‖ + ∫ r in v..s, (L * ‖Y r‖ + M) := by
      intro v hv
      calc
        ‖Y v‖ = ‖ξ + ∫ r in s..v, g r‖ := congrArg norm (heq v (hsub hv))
        _ ≤ ‖ξ‖ + ‖∫ r in s..v, g r‖ := norm_add_le _ _
        _ = ‖ξ‖ + ‖∫ r in v..s, g r‖ := by rw [intervalIntegral.integral_symm, norm_neg]
        _ ≤ ‖ξ‖ + ∫ r in v..s, (L * ‖Y r‖ + M) := by
          apply add_le_add (le_refl ‖ξ‖)
          apply intervalIntegral.norm_integral_le_of_norm_le hv.2
          · exact Eventually.of_forall (fun r hr => hg r (hsub ⟨hv.1.trans hr.1.le, hr.2⟩))
          · exact (hcont.mono (by
              rw [uIcc_of_le hv.2]
              exact (Icc_subset_Icc hv.1 le_rfl).trans hsub)).intervalIntegrable
    exact Ch05.Gronwall.constant_backward t s ‖ξ‖ L M (fun r => ‖Y r‖)
      hts (norm_nonneg _) hL hM (hY.norm.mono hsub)
      (fun _ _ => norm_nonneg _) hineq t ⟨le_rfl, hts⟩

theorem growth_bound : Specs.D13Unified.Ch06.LinearVolterra.GrowthBound.{u} := by
  intro E _ _ _ a b s A B ξ Y L M hs _ _ hL hM hA hB hY
  apply norm_bound_of_integral hs hY.1 hL hM hY.2
  intro r hr
  exact (norm_add_le _ _).trans (add_le_add
    ((A r).le_opNorm (Y r) |>.trans (mul_le_mul_of_nonneg_right (hA r hr) (norm_nonneg _)))
    (hB r hr))

/-- Subtract two Volterra equations without any assumptions outside [a,b]. -/
lemma IsIntegralSolution.sub {a b s : ℝ} {A C : ℝ → E →L[ℝ] E}
    {B D Y Z : ℝ → E} {ξ η : E} (hs : s ∈ Icc a b)
    (hA : ContinuousOn A (Icc a b)) (hC : ContinuousOn C (Icc a b))
    (hB : ContinuousOn B (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hY : IsIntegralSolution a b s A B ξ Y) (hZ : IsIntegralSolution a b s C D η Z) :
    IsIntegralSolution a b s A (fun t => (A t - C t) (Z t) + (B t - D t))
      (ξ - η) (fun t => Y t - Z t) := by
  refine ⟨hY.1.sub hZ.1, ?_⟩
  intro t ht
  have hsub := ordConnected_Icc.uIcc_subset hs ht
  have hgi : IntervalIntegrable (fun r => A r (Y r) + B r) volume s t := ((continuousOn_integrand hA hB hY.1).mono hsub).intervalIntegrable
  have hgj : IntervalIntegrable (fun r => C r (Z r) + D r) volume s t := ((continuousOn_integrand hC hD hZ.1).mono hsub).intervalIntegrable
  have hint : (∫ r in s..t, (A r (Y r) + B r)) - (∫ r in s..t, (C r (Z r) + D r)) =
      ∫ r in s..t, (A r (Y r - Z r) + ((A r - C r) (Z r) + (B r - D r))) := by
    rw [← intervalIntegral.integral_sub hgi hgj]
    apply intervalIntegral.integral_congr
    intro r _
    simp only [map_sub, sub_apply]
    abel
  dsimp only
  rw [hY.2 t ht, hZ.2 t ht]
  calc
    (ξ + ∫ r in s..t, (A r (Y r) + B r)) - (η + ∫ r in s..t, (C r (Z r) + D r)) =
      ξ - η + ((∫ r in s..t, (A r (Y r) + B r)) - (∫ r in s..t, (C r (Z r) + D r))) := by abel
    _ = _ := by rw [hint]

theorem perturbation_bound : Specs.D13Unified.Ch06.LinearVolterra.PerturbationBound.{u} := by
  intro E _ _ _ a b s A C B D ξ η Y Z L R δA δB hs hA hC hB hD
    hL hR hδA hδB hAL hZR hAC hBD hY hZ
  have hsub := hY.sub hs hA hC hB hD hZ
  apply growth_bound a b s A (fun t => (A t - C t) (Z t) + (B t - D t))
    (ξ - η) (fun t => Y t - Z t) L (δA * R + δB) hs hA
    (((hA.sub hC).clm_apply hZ.1).add (hB.sub hD))
    hL (add_nonneg (mul_nonneg hδA hR) hδB) hAL _ hsub
  intro t ht
  exact (norm_add_le _ _).trans (add_le_add
    (((A t - C t).le_opNorm (Z t)).trans
      (mul_le_mul (hAC t ht) (hZR t ht) (norm_nonneg _) hδA)) (hBD t ht))

/-- Uniqueness is relative to the interval, and allows s at either endpoint. -/
theorem unique {a b s : ℝ} {A : ℝ → E →L[ℝ] E} {B Y Z : ℝ → E} {ξ : E}
    (hs : s ∈ Icc a b) (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hY : IsIntegralSolution a b s A B ξ Y) (hZ : IsIntegralSolution a b s A B ξ Z) :
    EqOn Y Z (Icc a b) := by
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hL0 : 0 ≤ L := (norm_nonneg (A s)).trans (hL s hs)
  have hsub := hY.sub hs hA hA hB hB hZ
  have hb := growth_bound a b s A (fun t => (A t - A t) (Z t) + (B t - B t))
    (ξ - ξ) (fun t => Y t - Z t) L 0 hs hA
    (by simpa only [sub_self, zero_add, zero_apply] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : E)) (Icc a b)))
    hL0 le_rfl hL (by intro t ht; simp) hsub
  intro t ht
  have h := hb t ht
  simpa only [sub_self, norm_zero, zero_mul, add_zero, norm_le_zero_iff, sub_eq_zero] using h



lemma E_nonneg {L v : ℝ} (hv : 0 ≤ v) :
    0 ≤ Specs.D13Unified.Ch05.Gronwall.EValue L v := by
  have heq : (∫ r in 0..v, Real.exp (L*(v-r))) =
      Specs.D13Unified.Ch05.Gronwall.EValue L v := by
    simpa only [sub_zero, Ch05.Gronwall.E] using Ch05.Gronwall.integral_exp_kernel L 0 v
  rw [← heq]
  exact intervalIntegral.integral_nonneg_of_forall hv (fun _ => (Real.exp_pos _).le)

lemma E_le {L v T : ℝ} (hL : 0 ≤ L) (hv : 0 ≤ v) (hvT : v ≤ T) :
    Specs.D13Unified.Ch05.Gronwall.EValue L v ≤ T * Real.exp (L * T) := by
  have hi : IntervalIntegrable (fun r : ℝ => Real.exp (L * (v-r))) volume 0 v :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable 0 v
  have hj : IntervalIntegrable (fun _ : ℝ => Real.exp (L * T)) volume 0 v :=
    intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on hv hi hj (fun r hr =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hr.1]) hL))
  rw [Ch05.Gronwall.integral_exp_kernel] at h
  simp only [sub_zero, intervalIntegral.integral_const, smul_eq_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right hvT (Real.exp_pos _).le)

lemma time_length_le {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |t-s| ≤ b-a := by
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- A bound independent of the evaluation time. -/
lemma uniform_perturbation_bound {a b s : ℝ} {A C : ℝ → E →L[ℝ] E}
    {B D Y Z : ℝ → E} {ξ η : E} {L R δ : ℝ} (hs : s ∈ Icc a b)
    (hA : ContinuousOn A (Icc a b)) (hC : ContinuousOn C (Icc a b))
    (hB : ContinuousOn B (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hAL : ∀ t ∈ Icc a b, ‖A t‖ ≤ L) (hZR : ∀ t ∈ Icc a b, ‖Z t‖ ≤ R)
    (hAC : ∀ t ∈ Icc a b, ‖A t - C t‖ ≤ δ)
    (hBD : ∀ t ∈ Icc a b, ‖B t - D t‖ ≤ δ) (hξη : ‖ξ-η‖ ≤ δ)
    (hY : IsIntegralSolution a b s A B ξ Y) (hZ : IsIntegralSolution a b s C D η Z) :
    ∀ t ∈ Icc a b,
      ‖Y t - Z t‖ ≤ δ * (Real.exp (L * (b-a)) * (1 + (R+1)*(b-a))) := by
  intro t ht
  have hvT := time_length_le hs ht
  have hT : 0 ≤ b-a := sub_nonneg.mpr (hs.1.trans hs.2)
  have hb := perturbation_bound a b s A C B D ξ η Y Z L R δ δ hs hA hC hB hD
    hL hR hδ hδ hAL hZR hAC hBD hY hZ t ht
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvT hL)
  have hc : 0 ≤ δ*R+δ := add_nonneg (mul_nonneg hδ hR) hδ
  calc
    ‖Y t - Z t‖ ≤ ‖ξ-η‖ * Real.exp (L*|t-s|) +
        (δ*R+δ)*Specs.D13Unified.Ch05.Gronwall.EValue L |t-s| := hb
    _ ≤ δ * Real.exp (L*(b-a)) + (δ*R+δ)*((b-a)*Real.exp (L*(b-a))) :=
      add_le_add (mul_le_mul hξη he (Real.exp_pos _).le hδ)
        (mul_le_mul_of_nonneg_left (E_le hL (abs_nonneg _) hvT) hc)
    _ = _ := by ring

/-- Filter version of uniform dependence, also covering parameter limits. -/
theorem tendstoUniformlyOn_solutions {ι : Type*} {l : Filter ι}
    {a b s : ℝ} {A : ι → ℝ → E →L[ℝ] E} {B Y : ι → ℝ → E}
    {ξ : ι → E} {A₀ : ℝ → E →L[ℝ] E} {B₀ Y₀ : ℝ → E} {ξ₀ : E}
    (hs : s ∈ Icc a b) (hA : ∀ k, ContinuousOn (A k) (Icc a b))
    (hB : ∀ k, ContinuousOn (B k) (Icc a b))
    (hA₀ : ContinuousOn A₀ (Icc a b)) (hB₀ : ContinuousOn B₀ (Icc a b))
    (hY : ∀ k, IsIntegralSolution a b s (A k) (B k) (ξ k) (Y k))
    (hY₀ : IsIntegralSolution a b s A₀ B₀ ξ₀ Y₀)
    (hAc : TendstoUniformlyOn A A₀ l (Icc a b))
    (hBc : TendstoUniformlyOn B B₀ l (Icc a b)) (hξc : Tendsto ξ l (𝓝 ξ₀)) :
    TendstoUniformlyOn Y Y₀ l (Icc a b) := by
  obtain ⟨L₀, hL₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hA₀
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hY₀.1
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR s hs)
  have hL₀0 : 0 ≤ L₀ := (norm_nonneg _).trans (hL₀ s hs)
  let L := L₀ + 1
  have hL : 0 ≤ L := by dsimp [L]; linarith
  let K := Real.exp (L * (b-a)) * (1+(R+1)*(b-a))
  have hT : 0 ≤ b-a := sub_nonneg.mpr (hs.1.trans hs.2)
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (add_nonneg zero_le_one (mul_nonneg (by linarith) hT))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := min 1 (ε / (K+1))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by linarith))
  have hδε : δ * K < ε := by
    have hbound : δ ≤ ε / (K+1) := min_le_right _ _
    have hbound' := (le_div_iff₀ (by linarith : 0 < K+1)).mp hbound
    nlinarith
  have ha := (Metric.tendstoUniformlyOn_iff.mp hAc) δ hδ
  have hb := (Metric.tendstoUniformlyOn_iff.mp hBc) δ hδ
  have hx := (Metric.tendsto_nhds.mp hξc) δ hδ
  filter_upwards [ha, hb, hx] with k hkA hkB hkξ
  have hAk : ∀ t ∈ Icc a b, ‖A k t - A₀ t‖ ≤ δ := by
    intro t ht
    simpa only [dist_eq_norm, norm_sub_rev] using (hkA t ht).le
  have hBk : ∀ t ∈ Icc a b, ‖B k t - B₀ t‖ ≤ δ := by
    intro t ht
    simpa only [dist_eq_norm, norm_sub_rev] using (hkB t ht).le
  have hξk : ‖ξ k - ξ₀‖ ≤ δ := by simpa only [dist_eq_norm] using hkξ.le
  have hAL : ∀ t ∈ Icc a b, ‖A k t‖ ≤ L := by
    intro t ht
    calc
      ‖A k t‖ ≤ ‖A k t - A₀ t‖ + ‖A₀ t‖ := norm_le_norm_sub_add _ _
      _ ≤ δ + L₀ := add_le_add (hAk t ht) (hL₀ t ht)
      _ ≤ L := by dsimp [L, δ]; linarith [min_le_left (1 : ℝ) (ε/(K+1))]
  intro t ht
  have h := uniform_perturbation_bound hs (hA k) hA₀ (hB k) hB₀ hL hR0 hδ.le
    hAL hR hAk hBk hξk (hY k) hY₀ t ht
  simpa only [dist_eq_norm, norm_sub_rev] using h.trans_lt hδε

theorem uniform_dependence : Specs.D13Unified.Ch06.LinearVolterra.UniformDependence.{u} := by
  intro E _ _ _ a b s A B Y ξ A₀ B₀ Y₀ ξ₀
  exact tendstoUniformlyOn_solutions



/-- Picard's operator on the full Banach space C([a,b],E). There is no
small-interval or invariant-ball hypothesis. -/
def picardOperator {a b s : ℝ} (hs : s ∈ Icc a b)
    {A : ℝ → E →L[ℝ] E} {B : ℝ → E}
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b)) (ξ : E)
    (Y : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := ξ + ∫ r in s..t, (A r (IccExtend (hs.1.trans hs.2) Y r) + B r)
  continuous_toFun := by
    have hg : ContinuousOn (fun r => A r (IccExtend (hs.1.trans hs.2) Y r) + B r) (Icc a b) :=
      continuousOn_integrand hA hB (continuous_IccExtend_iff.mpr Y.continuous).continuousOn
    have hc : ContinuousOn (fun t => ξ + ∫ r in s..t,
        (A r (IccExtend (hs.1.trans hs.2) Y r) + B r)) (Icc a b) := by
      intro t ht
      exact ((hasDerivWithinAt_integral_on_interval ordConnected_Icc hg hs ht).const_add ξ).continuousWithinAt
    exact hc.domRestrict

lemma picard_integrable {a b s : ℝ} (hs : s ∈ Icc a b)
    {A : ℝ → E →L[ℝ] E} {B : ℝ → E}
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (Y : C(Icc a b, E)) (t : Icc a b) :
    IntervalIntegrable (fun r => A r (IccExtend (hs.1.trans hs.2) Y r) + B r) volume s t :=
  ((continuousOn_integrand hA hB
    (continuous_IccExtend_iff.mpr Y.continuous).continuousOn).mono
    (ordConnected_Icc.uIcc_subset hs t.property)).intervalIntegrable

/-- Factorial decay of differences of Picard iterates, valid simultaneously
on the two sides of s. -/
lemma dist_picard_iterate_apply_le {a b s : ℝ} (hs : s ∈ Icc a b)
    {A : ℝ → E →L[ℝ] E} {B : ℝ → E}
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b)) (ξ : E)
    (L : ℝ≥0) (hL : ∀ t ∈ Icc a b, ‖A t‖ ≤ L)
    (Y Z : C(Icc a b,E)) (n : ℕ) (t : Icc a b) :
    dist ((picardOperator hs hA hB ξ)^[n] Y t) ((picardOperator hs hA hB ξ)^[n] Z t) ≤
      (L * |t.val-s|)^n / n.factorial * dist Y Z := by
  let K := picardOperator hs hA hB ξ
  change dist (K^[n] Y t) (K^[n] Z t) ≤ _
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := Y) (g := Z) t
  | succ n hn =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dist_eq_norm]
    change ‖(ξ + ∫ r in s..t, (A r (IccExtend _ (K^[n] Y) r) + B r)) -
      (ξ + ∫ r in s..t, (A r (IccExtend _ (K^[n] Z) r) + B r))‖ ≤ _
    rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
      (picard_integrable hs hA hB _ t) (picard_integrable hs hA hB _ t)]
    calc
      _ ≤ ∫ r in uIoc s t.val, (L:ℝ)^(n+1) * |r-s|^n / n.factorial * dist Y Z := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le
          (Continuous.integrableOn_uIoc (by fun_prop))
        apply (ae_restrict_mem measurableSet_Ioc).mono
        intro r hr
        have hr' : r ∈ Icc a b := (ordConnected_Icc.uIcc_subset hs t.property) (uIoc_subset_uIcc hr)
        rw [IccExtend_of_mem _ _ hr', IccExtend_of_mem _ _ hr', add_sub_add_right_eq_sub,
          ← map_sub]
        calc
          ‖A r ((K^[n] Y) ⟨r, hr'⟩ - (K^[n] Z) ⟨r, hr'⟩)‖ ≤
              L * dist ((K^[n] Y) ⟨r,hr'⟩) ((K^[n] Z) ⟨r,hr'⟩) := by
            rw [dist_eq_norm]
            exact (A r).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hL r hr') (norm_nonneg _))
          _ ≤ (L:ℝ)^(n+1) * |r-s|^n / n.factorial * dist Y Z := by
            calc
              _ ≤ L * (((L:ℝ)*|r-s|)^n / n.factorial * dist Y Z) :=
                mul_le_mul_of_nonneg_left (hn ⟨r,hr'⟩) L.coe_nonneg
              _ = _ := by rw [mul_pow, pow_succ']; ring
      _ ≤ ((L:ℝ)*|t.val-s|)^(n+1) / (n+1).factorial * dist Y Z := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

/-- Existence on the whole compact interval by a contracting iterate. -/
theorem existence : Specs.D13Unified.Ch06.LinearVolterra.Existence.{u} := by
  intro E _ _ _ a b s A B ξ hs hA hB
  obtain ⟨L₀, hL₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let L : ℝ≥0 := ⟨L₀, (norm_nonneg _).trans (hL₀ s hs)⟩
  let K := picardOperator hs hA hB ξ
  have hT : 0 ≤ b-a := sub_nonneg.mpr (hs.1.trans hs.2)
  obtain ⟨n, hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop ((L:ℝ)*(b-a))).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  let c : ℝ≥0 := ⟨((L:ℝ)*(b-a))^n / n.factorial, by positivity⟩
  have hK : ContractingWith c (K^[n]) := by
    refine ⟨hn, LipschitzWith.of_dist_le_mul ?_⟩
    intro Y Z
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro t
    exact (dist_picard_iterate_apply_le hs hA hB ξ L hL₀ Y Z n t).trans (by
      change ((L:ℝ)*|t.val-s|)^n / n.factorial * dist Y Z ≤
        ((L:ℝ)*(b-a))^n / n.factorial * dist Y Z
      gcongr
      exact time_length_le hs t.property)
  have : Nonempty (Icc a b) := ⟨⟨s, hs⟩⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Function.IsFixedPt K Y :=
    ⟨_, hK.isFixedPt_fixedPoint_iterate⟩
  let Y' := IccExtend (hs.1.trans hs.2) Y
  have hsol : IsIntegralSolution a b s A B ξ Y' := by
    refine ⟨(continuous_IccExtend_iff.mpr Y.continuous).continuousOn, ?_⟩
    intro t ht
    rw [show Y' t = Y ⟨t,ht⟩ from IccExtend_of_mem _ _ ht]
    exact (congrArg (fun f : C(Icc a b,E) => f ⟨t,ht⟩) hY).symm
  exact ⟨Y', hsol, fun Z hZ => unique hs hA hB hZ hsol⟩



/-- Joint parameter continuity, obtained from uniform dependence on a compact
interval and continuity of evaluation. -/
theorem joint_dependence : Specs.D13Unified.Ch06.LinearVolterra.JointDependence.{u} := by
  intro E _ _ _ P _ a b s A B ξ hs hA hB hξ
  let AA (p : P) : C(Icc a b, E →L[ℝ] E) :=
    ⟨fun t => A p t, hA.comp (continuous_const.prodMk continuous_id)⟩
  let BB (p : P) : C(Icc a b, E) :=
    ⟨fun t => B p t, hB.comp (continuous_const.prodMk continuous_id)⟩
  have hAA : Continuous AA := ContinuousMap.continuous_of_continuous_uncurry AA hA
  have hBB : Continuous BB := ContinuousMap.continuous_of_continuous_uncurry BB hB
  have hAc (p : P) : ContinuousOn (A p) (Icc a b) :=
    continuousOn_iff_continuous_domRestrict.mpr (AA p).continuous
  have hBc (p : P) : ContinuousOn (B p) (Icc a b) :=
    continuousOn_iff_continuous_domRestrict.mpr (BB p).continuous
  choose Y hY huniq using fun p => existence a b s (A p) (B p) (ξ p) hs (hAc p) (hBc p)
  let YY (p : P) : C(Icc a b,E) := ⟨fun t => Y p t, (hY p).1.domRestrict⟩
  have hYY : Continuous YY := by
    rw [continuous_iff_continuousAt]
    intro p
    have ha : TendstoUniformlyOn A (A p) (𝓝 p) (Icc a b) :=
      tendstoUniformlyOn_iff_restrict.mpr
        (ContinuousMap.tendsto_iff_tendstoUniformly.mp hAA.continuousAt)
    have hb : TendstoUniformlyOn B (B p) (𝓝 p) (Icc a b) :=
      tendstoUniformlyOn_iff_restrict.mpr
        (ContinuousMap.tendsto_iff_tendstoUniformly.mp hBB.continuousAt)
    have hy := tendstoUniformlyOn_solutions hs hAc hBc (hAc p) (hBc p) hY (hY p) ha hb hξ.continuousAt
    exact ContinuousMap.tendsto_iff_tendstoUniformly.mpr
      (tendstoUniformlyOn_iff_restrict.mp hy)
  refine ⟨Y, hY, ?_⟩
  exact continuous_eval.comp ((hYY.comp continuous_fst).prodMk continuous_snd)

/-- Matrix multiplication is exactly the continuous linear action used above. -/
@[simp] theorem matrixAction_apply {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (Y : Matrix (Fin n) (Fin r) ℝ) :
    matrixAction A Y = A * Y := rfl

lemma continuous_matrixAction {n r : ℕ} :
    Continuous (matrixAction (n:=n) (r:=r)) := by
  let T : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      ((Fin n → Fin r → ℝ) →L[ℝ] (Fin n → Fin r → ℝ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (mulLinearMap ℝ)
  exact T.continuous_of_finiteDimensional

theorem matrix_existence : Specs.D13Unified.Ch06.LinearVolterra.MatrixExistence := by
  intro n r a b s A B ξ hs hA hB
  have hAc : ContinuousOn A (Icc a b) :=
    continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j => hA i j))
  have hAop := (continuous_matrixAction (n:=n) (r:=r)).comp_continuousOn hAc
  obtain ⟨Y, hY, huniq⟩ := existence a b s (fun t => matrixAction (A t)) B ξ hs hAop hB
  refine ⟨Y, ?_, ?_⟩
  · exact hY
  · intro Z hZ
    exact huniq Z hZ



omit [CompleteSpace E] in
lemma continuous_matrixActionIn {n r : ℕ}
    (e : Matrix (Fin n) (Fin r) ℝ ≃L[ℝ] E) :
    Continuous (matrixActionIn e) :=
  continuous_const.clm_comp (continuous_matrixAction.clm_comp continuous_const)

theorem matrix_integral_bridge :
    Specs.D13Unified.Ch06.LinearVolterra.MatrixIntegralBridge.{u} := by
  intro E _ _ _ n r e a b s A B Y ξ hs hA hB hY
  have hAc := (continuous_matrixAction (n:=n) (r:=r)).comp_continuousOn hA
  have hi : ContinuousOn (fun t i j => (A t * Y t + B t) i j) (Icc a b) :=
    continuousOn_integrand hAc hB hY
  have heq (t : ℝ) (ht : t ∈ Icc a b) :
      e (Y t) = e ξ + ∫ u in s..t,
        (matrixActionIn e (A u) (e (Y u)) + e (B u)) ↔
      Y t = ξ + ∫ u in s..t, (A u * Y u + B u) := by
    have hg : (fun u => matrixActionIn e (A u) (e (Y u)) + e (B u)) =
        (fun u => e (A u * Y u + B u)) := by
      funext u
      change e (matrixAction (A u) (e.symm (e (Y u)))) + e (B u) = _
      rw [e.symm_apply_apply, matrixAction_apply, map_add]
    have hInt : IntervalIntegrable (fun u i j => (A u * Y u + B u) i j) volume s t :=
      (hi.mono (ordConnected_Icc.uIcc_subset hs ht)).intervalIntegrable
    let ee : (Fin n → Fin r → ℝ) →L[ℝ] E := e.toContinuousLinearMap
    have hcomm := ee.intervalIntegral_comp_comm hInt
    change (∫ u in s..t, e (A u * Y u + B u)) = e (∫ u in s..t, (A u * Y u + B u)) at hcomm
    rw [hg, hcomm, ← map_add, e.injective.eq_iff]
  constructor
  · intro h t ht
    exact (heq t ht).mp (h.2 t ht)
  · intro h
    exact ⟨e.continuous.comp_continuousOn hY, fun t ht => (heq t ht).mpr (h t ht)⟩

theorem matrix_growth_bound : Specs.D13Unified.Ch06.LinearVolterra.MatrixGrowthBound.{u} := by
  intro E _ _ _ n r e a b s A B Y ξ L M hs hA hB hY heq hL hM hAL hBM
  exact growth_bound a b s (fun t => matrixActionIn e (A t)) (fun t => e (B t))
    (e ξ) (fun t => e (Y t)) L M hs
    ((continuous_matrixActionIn e).comp_continuousOn hA)
    (e.continuous.comp_continuousOn hB) hL hM hAL hBM
    ((matrix_integral_bridge n r e a b s A B Y ξ hs hA hB hY).mpr heq)

lemma uniformContinuous_matrixAction {n r : ℕ} :
    UniformContinuous (matrixAction (n:=n) (r:=r)) := by
  let T : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      ((Fin n → Fin r → ℝ) →L[ℝ] (Fin n → Fin r → ℝ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (mulLinearMap ℝ)
  exact T.toContinuousLinearMap.uniformContinuous

theorem matrix_uniform_dependence :
    Specs.D13Unified.Ch06.LinearVolterra.MatrixUniformDependence := by
  intro n r a b s A B Y ξ A₀ B₀ Y₀ ξ₀ hs hA hB hA₀ hB₀ hY hY₀ heq heq₀ hAc hBc hξc
  exact uniform_dependence a b s (fun k t => matrixAction (A k t)) B Y ξ
    (fun t => matrixAction (A₀ t)) B₀ Y₀ ξ₀ hs
    (fun k => continuous_matrixAction.comp_continuousOn (hA k)) hB
    (continuous_matrixAction.comp_continuousOn hA₀) hB₀
    (fun k => ⟨hY k, heq k⟩) ⟨hY₀, heq₀⟩
    (uniformContinuous_matrixAction.comp_tendstoUniformlyOn hAc) hBc hξc

theorem matrix_joint_dependence :
    Specs.D13Unified.Ch06.LinearVolterra.MatrixJointDependence := by
  intro P _ n r a b s A B ξ hs hA hB hξ
  exact joint_dependence a b s (fun p t => matrixAction (A p t)) B ξ hs
    (continuous_matrixAction.comp hA) hB hξ

theorem matrix_differential_equivalence :
    Specs.D13Unified.Ch06.LinearVolterra.MatrixDifferentialEquivalence := by
  intro n r a b s A B Y ξ hs hA hB
  exact differential_equivalence a b s (fun t => matrixAction (A t)) B ξ Y hs
    (continuous_matrixAction.comp_continuousOn hA) hB



universe v
theorem operator_growth_bound :
    Specs.D13Unified.Ch06.LinearVolterra.OperatorGrowthBound.{u,v} := by
  intro F G _ _ _ _ _ a b s A B Y ξ L M hs hA hB hY heq hL hM hAL hBM
  apply norm_bound_of_integral hs hY hL hM heq
  intro t ht
  exact (norm_add_le _ _).trans (add_le_add
    (((A t).opNorm_comp_le (Y t)).trans
      (mul_le_mul_of_nonneg_right (hAL t ht) (norm_nonneg _))) (hBM t ht))

end D13Unified.Ch06.LinearVolterra

/- Mathlib proof attribution
Adapted portion near line 344:
The factorial estimate for the iterated approximation, adapted to the linear
Volterra construction.

Upstream: Mathlib/Analysis/ODE/PicardLindelof.lean (around line 329)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Winston Yin

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
