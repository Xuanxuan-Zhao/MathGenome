import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.ContourCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.HolomorphicHomomorphism
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Algebraic properties of the manuscript's finite-cycle Riesz–Dunford integral. -/

noncomputable section
namespace ExpandedFA.BanachAlgebra.HolomorphicHomomorphism

open Set MeasureTheory Filter
open scoped Topology
open ContourCalculus
open Specs.ExpandedFA.BanachAlgebra.Conventions


universe u v

section Integrals
variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

lemma cycleIntegral_add (Γ : Cycle) {h k : ℂ → X}
    (hh : ContinuousOn h Γ.trace) (hk : ContinuousOn k Γ.trace) :
    cycleIntegral Γ (fun z => h z + k z) = cycleIntegral Γ h + cycleIntegral Γ k := by
  simp only [cycleIntegral, smul_add, intervalIntegral.integral_add
    (cycle_integrable Γ hh _) (cycle_integrable Γ hk _), Finset.sum_add_distrib]

lemma cycleIntegral_smul (Γ : Cycle) (c : ℂ) (h : ℂ → X) :
    cycleIntegral Γ (fun z => c • h z) = c • cycleIntegral Γ h := by
  simp only [cycleIntegral, smul_comm _ c, intervalIntegral.integral_smul,
    Finset.smul_sum]

lemma map_cycleIntegral (Γ : Cycle) (L : X →L[ℂ] Y) {h : ℂ → X}
    (hh : ContinuousOn h Γ.trace) :
    L (cycleIntegral Γ h) = cycleIntegral Γ (fun z => L (h z)) := by
  simp only [cycleIntegral, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← L.intervalIntegral_comp_comm (cycle_integrable Γ hh i)]
  simp only [map_smul]
end Integrals

section Algebra
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

lemma contourValue_add (Γ : Cycle) (a : A) {f g : ℂ → ℂ}
    (hΓ : Γ.trace ⊆ algebraResolventSet ℂ A a)
    (hf : ContinuousOn f Γ.trace) (hg : ContinuousOn g Γ.trace) :
    contourValue A Γ a (fun z => f z + g z) =
      contourValue A Γ a f + contourValue A Γ a g := by
  change _ • cycleIntegral Γ (fun z => (f z + g z) • algebraResolvent ℂ A a z) = _
  simp_rw [add_smul]
  rw [cycleIntegral_add Γ (contour_integrand_continuous Γ a hΓ hf)
    (contour_integrand_continuous Γ a hΓ hg), smul_add]
  rfl

lemma contourValue_smul (Γ : Cycle) (a : A) (c : ℂ) (f : ℂ → ℂ) :
    contourValue A Γ a (fun z => c * f z) = c • contourValue A Γ a f := by
  change _ • cycleIntegral Γ (fun z => (c * f z) • algebraResolvent ℂ A a z) = _
  simp_rw [mul_smul]
  rw [cycleIntegral_smul, smul_comm]
  rfl

/-- Commutation with the resolvent holds even at its zero extension on the spectrum. -/
lemma commute_resolvent {a b : A} (h : Commute b a) (z : ℂ) :
    Commute b (algebraResolvent ℂ A a z) := by
  have hc : Commute b (algebraMap ℂ A z - a) :=
    Commute.sub_right (Algebra.commutes z b).symm h
  by_cases hu : IsUnit (algebraMap ℂ A z - a)
  · obtain ⟨w, hw⟩ := hu
    change Commute b (Ring.inverse (algebraMap ℂ A z - a))
    rw [← hw, Ring.inverse_unit]
    exact (hw ▸ hc).units_inv_right
  · change Commute b (Ring.inverse (algebraMap ℂ A z - a))
    rw [Ring.inverse_non_unit _ hu]
    exact Commute.zero_right b

lemma commute_cycleIntegral (Γ : Cycle) {h : ℂ → A} (hh : ContinuousOn h Γ.trace)
    (b : A) (hc : ∀ z ∈ Γ.trace, Commute b (h z)) :
    Commute b (cycleIntegral Γ h) := by
  change (ContinuousLinearMap.mul ℂ A b) (cycleIntegral Γ h) =
    ((ContinuousLinearMap.mul ℂ A).flip b) (cycleIntegral Γ h)
  rw [map_cycleIntegral Γ _ hh, map_cycleIntegral Γ _ hh]
  apply cycleIntegral_congr Γ
  intro z hz
  exact (hc z hz).eq

lemma commute_contourValue (Γ : Cycle) {a b : A} {f : ℂ → ℂ}
    (hΓ : Γ.trace ⊆ algebraResolventSet ℂ A a)
    (hf : ContinuousOn f Γ.trace) (hc : Commute b a) :
    Commute b (contourValue A Γ a f) := by
  have hi := commute_cycleIntegral Γ (contour_integrand_continuous Γ a hΓ hf) b
    (fun z _ => (commute_resolvent hc z).smul_right (f z))
  exact hi.smul_right _
end Algebra

/-- Complex scalar linearity on every common holomorphy neighborhood. -/
theorem scalar_linearity : Spec.ScalarLinearity.{u} := by
  intro A _ _ hA a U f g α β hU hKU hf hg
  letI : CompleteSpace A := hA.1
  let Γ := selectedCycle (algebraSpectrum ℂ A a) U
  have hΓ := selected_cycle_admissible A hA a U hU hKU
  have hres : Γ.trace ⊆ algebraResolventSet ℂ A a := fun z hz =>
    not_not.mp (hΓ.1 hz).2
  change contourValue A Γ a _ = α • contourValue A Γ a f + β • contourValue A Γ a g
  calc
    _ = contourValue A Γ a (fun z => α * f z) +
        contourValue A Γ a (fun z => β * g z) :=
      contourValue_add Γ a hres
        (((continuousOn_const (c := α)).mul hf.continuousOn).mono
          (fun z hz => (hΓ.1 hz).1))
        (((continuousOn_const (c := β)).mul hg.continuousOn).mono
          (fun z hz => (hΓ.1 hz).1))
    _ = _ := congrArg₂ (· + ·) (contourValue_smul Γ a α f) (contourValue_smul Γ a β g)

/-- The same commutation result in an arbitrary complex Banach algebra. -/
theorem commutation : Spec.Commutation.{u} := by
  intro A _ _ hA a b U f hU hKU hf hc
  letI : CompleteSpace A := hA.1
  have hΓ := selected_cycle_admissible A hA a U hU hKU
  exact commute_contourValue _ (fun z hz => not_not.mp (hΓ.1 hz).2)
    (hf.continuousOn.mono (fun z hz => (hΓ.1 hz).1)) hc

/-- Bounded operators on the zero space are included. -/
theorem operator_commutation : Spec.OperatorCommutation.{u} := by
  intro X _ _ _ T S U f hU hKU hf hc
  classical
  by_cases hX : Subsingleton X
  · letI := hX
    exact Subsingleton.elim _ _
  letI : Nontrivial X := not_subsingleton_iff_nontrivial.mp hX
  exact (commutation (X →L[ℂ] X) ⟨inferInstance, inferInstance, inferInstance⟩
    T S U f hU hKU hf hc).eq


section Normalization

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Integration on a fixed finite C¹ cycle is continuous for uniform convergence. -/
lemma cycleIntegral_tendsto_uniform (Γ : Cycle) {h : ℂ → X} {F : ℕ → ℂ → X}
    (hh : ContinuousOn h Γ.trace) (hF : ∀ n, ContinuousOn (F n) Γ.trace)
    (hlim : TendstoUniformlyOn F h atTop Γ.trace) :
    Tendsto (fun n => cycleIntegral Γ (F n)) atTop (𝓝 (cycleIntegral Γ h)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε / (Γ.length + 1) := div_pos hε (by have := Γ.length_nonneg; positivity)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) _ hδ] with n hn
  rw [dist_eq_norm, ← cycleIntegral_sub Γ (hF n) hh]
  apply (norm_cycleIntegral_le Γ ((hF n).sub hh) hδ.le (fun z hz => ?_)).trans_lt
  · calc
      Γ.length * (ε / (Γ.length + 1)) < (Γ.length + 1) * (ε / (Γ.length + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) hδ
      _ = ε := mul_div_cancel₀ _ (by have := Γ.length_nonneg; positivity)
  · have h := hn z hz
    rw [dist_comm, dist_eq_norm] at h
    exact h.le

lemma cycleIntegral_sum (Γ : Cycle) {ι : Type*} (s : Finset ι) (h : ι → ℂ → X)
    (hh : ∀ i ∈ s, ContinuousOn (h i) Γ.trace) :
    cycleIntegral Γ (fun z => ∑ i ∈ s, h i z) = ∑ i ∈ s, cycleIntegral Γ (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cycleIntegral]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [cycleIntegral_add Γ (hh i (Finset.mem_insert_self _ _))
      (continuousOn_finsetSum _ (fun j hj => hh j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hh j (Finset.mem_insert_of_mem hj))]

lemma cycleIntegral_smul_const (Γ : Cycle) (h : ℂ → ℂ) (x : X) :
    cycleIntegral Γ (fun z => h z • x) = cycleIntegral Γ h • x := by
  simp only [cycleIntegral, smul_smul, smul_eq_mul,
    intervalIntegral.integral_smul_const, Finset.sum_smul]

lemma cycleIntegral_inverse_pow (Γ : Cycle) (hzero : ∀ z ∈ Γ.trace, z ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    cycleIntegral Γ (fun z => (z ^ (n + 1))⁻¹) = 0 := by
  let m : ℤ := -(n : ℤ)
  have hm : (m : ℂ) ≠ 0 := by
    dsimp [m]
    simpa only [Int.cast_neg, Int.cast_natCast] using
      (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne') : -(n : ℂ) ≠ 0)
  have he : m - 1 = -((n + 1 : ℕ) : ℤ) := by dsimp [m]; omega
  have hc : ContinuousOn (fun z : ℂ => z ^ (m - 1)) Γ.trace :=
    continuousOn_id.zpow₀ _ (fun z hz => Or.inl (hzero z hz))
  have hi := cycleIntegral_derivative_eq_zero Γ (continuousOn_const.mul hc)
    (fun z hz => hasDerivAt_zpow m z (Or.inl (hzero z hz)))
  change cycleIntegral Γ (fun z => (m : ℂ) * z ^ (m - 1)) = 0 at hi
  rw [cycleIntegral_const_mul] at hi
  have hz := (mul_eq_zero.mp hi).resolve_left hm
  simpa only [he, zpow_neg, zpow_natCast] using hz

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

/-- Uniform Neumann expansion on any compact contour separated from the norm ball. -/
lemma resolvent_series_uniform [CompleteSpace A] [NormOneClass A]
    (a : A) (Γ : Cycle) (r : ℝ) (hr : ‖a‖ < r)
    (hΓ : ∀ z ∈ Γ.trace, r ≤ ‖z‖) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, (z ^ (n + 1))⁻¹ • a ^ n)
      (algebraResolvent ℂ A a) atTop Γ.trace := by
  have hr0 : 0 < r := (norm_nonneg a).trans_lt hr
  have hq0 : 0 ≤ ‖a‖ / r := div_nonneg (norm_nonneg _) hr0.le
  have hq1 : ‖a‖ / r < 1 := (div_lt_one hr0).mpr hr
  have hsum : Summable (fun n : ℕ => r⁻¹ * (‖a‖ / r) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hbound (n : ℕ) (z : ℂ) (hz : z ∈ Γ.trace) :
      ‖(z ^ (n + 1))⁻¹ • a ^ n‖ ≤ r⁻¹ * (‖a‖ / r) ^ n := by
    have hz0 : 0 < ‖z‖ := hr0.trans_le (hΓ z hz)
    calc
      _ = ‖z‖⁻¹ ^ (n + 1) * ‖a ^ n‖ := by rw [norm_smul, norm_inv, norm_pow, inv_pow]
      _ ≤ r⁻¹ ^ (n + 1) * ‖a‖ ^ n :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) (inv_anti₀ hr0 (hΓ z hz)) _)
          (norm_pow_le ..) (norm_nonneg _) (by positivity)
      _ = _ := by rw [div_eq_mul_inv, mul_pow, pow_succ]; ring
  have hlim := tendstoUniformlyOn_tsum_nat hsum hbound
  apply hlim.congr_right
  intro z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hr0.trans_le (hΓ z hz))
  have hs := (hasSum_geom_series_inverse (z⁻¹ • a) (show ‖z⁻¹ • a‖ < 1 by
    rw [norm_smul, norm_inv, inv_mul_lt_iff₀ (hr0.trans_le (hΓ z hz)), mul_one]
    exact hr.trans_le (hΓ z hz))).const_smul z⁻¹
  have he : z⁻¹ • Ring.inverse (1 - z⁻¹ • a) = algebraResolvent ℂ A a z := by
    have h := spectrum.units_smul_resolvent_self (r := Units.mk0 z hz0) (a := a)
    have h' := congrArg (fun x : A => z⁻¹ • x) h
    simpa only [Units.smul_def, Units.val_mk0, Units.val_inv_eq_inv_val, resolvent,
      map_one, inv_smul_smul₀ hz0] using h'.symm
  rw [he] at hs
  exact (show HasSum (fun n : ℕ => (z ^ (n + 1))⁻¹ • a ^ n)
      (algebraResolvent ℂ A a z) by
    simpa only [smul_pow, smul_smul, pow_succ, mul_inv_rev, inv_pow] using hs).tsum_eq


lemma contourValue_one_exterior (hA : IsUnitalBanachAlgebra A) (a : A)
    (Γ : Cycle) (r : ℝ) (hr : ‖a‖ < r)
    (hΓ : ∀ z ∈ Γ.trace, r ≤ ‖z‖) (hw : Γ.winding 0 = 1) :
    contourValue A Γ a (fun _ => 1) = 1 := by
  letI : CompleteSpace A := hA.1
  letI : NormOneClass A := hA.2.2
  have hr0 : 0 < r := (norm_nonneg a).trans_lt hr
  have hz : ∀ z ∈ Γ.trace, z ≠ 0 := fun z h =>
    norm_pos_iff.mp (hr0.trans_le (hΓ z h))
  have hterm (n : ℕ) :
      ContinuousOn (fun z => (z ^ (n + 1))⁻¹ • a ^ n) Γ.trace :=
    ((continuousOn_id.pow _).inv₀ (fun z h => pow_ne_zero _ (hz z h))).smul continuousOn_const
  have hi (n : ℕ) (hn : 0 < n) :
      cycleIntegral Γ (fun z => (z ^ (n + 1))⁻¹ • a ^ n) = 0 := by
    rw [cycleIntegral_smul_const, cycleIntegral_inverse_pow Γ hz n hn, zero_smul]
  have hpartial (N : ℕ) (hN : 0 < N) :
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        cycleIntegral Γ (fun z => ∑ n ∈ Finset.range N, (z ^ (n + 1))⁻¹ • a ^ n) = 1 := by
    rw [cycleIntegral_sum Γ _ _ (fun n _ => hterm n)]
    rw [Finset.sum_eq_single 0]
    · simp only [zero_add, pow_one, pow_zero, cycleIntegral_smul_const, smul_smul]
      have hw' : (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          cycleIntegral Γ (fun z => z⁻¹) = 1 := by
        simpa only [Cycle.winding, sub_zero] using hw
      rw [hw', one_smul]
    · intro n hn hn0
      exact hi n (Nat.pos_of_ne_zero hn0)
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hN))
  have hres : ContinuousOn (algebraResolvent ℂ A a) Γ.trace :=
    continuousOn_resolvent_trace Γ a (fun z hz =>
      spectrum.mem_resolventSet_of_norm_lt (hr.trans_le (hΓ z hz)))
  have hl := (cycleIntegral_tendsto_uniform Γ hres
    (fun N => continuousOn_finsetSum _ (fun n _ => hterm n))
    (resolvent_series_uniform a Γ r hr hΓ)).const_smul (2 * Real.pi * Complex.I : ℂ)⁻¹
  have he : (fun N => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      cycleIntegral Γ (fun z => ∑ n ∈ Finset.range N, (z ^ (n + 1))⁻¹ • a ^ n))
      =ᶠ[atTop] (fun _ => (1 : A)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact hpartial N hN
  have hv := tendsto_nhds_unique hl (tendsto_const_nhds.congr' he.symm)
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    cycleIntegral Γ (fun z => (1 : ℂ) • algebraResolvent ℂ A a z) = 1
  simp only [one_smul]
  exact hv


lemma admissible_mono_compact {Γ : Cycle} {K L U : Set ℂ}
    (h : Γ.Admissible L U) (hKL : K ⊆ L) : Γ.Admissible K U := by
  refine ⟨fun z hz => ⟨(h.1 hz).1, fun hzK => (h.1 hz).2 (hKL hzK)⟩, h.2.1, ?_, h.2.2.2⟩
  obtain ⟨V, hV, hLV, hd, hw⟩ := h.2.2.1
  exact ⟨V, hV, hKL.trans hLV, hd, hw⟩

/-- The normalization is proved by the uniformly convergent Neumann expansion. -/
theorem unitality : Spec.Unitality.{u} := by
  intro A _ _ hA a U hU hKU
  letI : CompleteSpace A := hA.1
  letI : NormOneClass A := hA.2.2
  let r := ‖a‖ + 1
  have hr : ‖a‖ < r := lt_add_one _
  have hr0 : 0 < r := (norm_nonneg a).trans_lt hr
  obtain ⟨Γ, hΓ⟩ := admissible_cycles_exist (Metric.closedBall (0 : ℂ) r) univ
    (isCompact_closedBall _ _) isOpen_univ (subset_univ _)
  have hbound : ∀ z ∈ Γ.trace, r ≤ ‖z‖ := by
    intro z hz
    have h := (hΓ.1 hz).2
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at h
    exact h.le
  have hK : algebraSpectrum ℂ A a ⊆ Metric.closedBall (0 : ℂ) r := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (spectrum.norm_le_norm_of_mem hz).trans hr.le
  have had := admissible_mono_compact hΓ hK
  have hf : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) univ := differentiableOn_const 1
  have he := neighborhood_independence A hA a U univ U (fun _ => 1) (fun _ => 1)
    hU isOpen_univ hU hKU (fun z hz => ⟨hz, mem_univ z⟩)
    (differentiableOn_const 1) hf (fun _ _ => rfl)
    (selectedCycle (algebraSpectrum ℂ A a) U) Γ
    (selected_cycle_admissible A hA a U hU hKU) had
  exact he.trans (contourValue_one_exterior hA a Γ r hr hbound
    (hΓ.winding_eq_one (Metric.mem_closedBall.mpr (by simpa using hr0.le))))


lemma cycleIntegral_holomorphic_eq_zero (Γ : Cycle) {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hΓ : Γ.trace ⊆ U) (hw : ∀ z ∉ U, Γ.winding z = 0)
    (hf : DifferentiableOn ℂ f U) : cycleIntegral Γ f = 0 :=
  cycleIntegral_eq_zero_of_null_winding U Γ f hU hΓ hw hf

lemma holomorphicValue_congr (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} (hU : IsOpen U) (hKU : algebraSpectrum ℂ A a ⊆ U)
    {f g : ℂ → ℂ} (hfg : EqOn f g U) :
    holomorphicValue A a U f = holomorphicValue A a U g := by
  have hΓ := selected_cycle_admissible A hA a U hU hKU
  apply congrArg (fun x : A => (2 * Real.pi * Complex.I : ℂ)⁻¹ • x)
  apply cycleIntegral_congr
  intro z hz
  exact congrArg (fun c : ℂ => c • algebraResolvent ℂ A a z) (hfg ((hΓ.1 hz).1))

/-- Multiplication by the coordinate is obtained directly from (z-a)R(z)=1. -/
lemma holomorphicValue_coordinate_mul (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hKU : algebraSpectrum ℂ A a ⊆ U) (hf : DifferentiableOn ℂ f U) :
    holomorphicValue A a U (fun z => z * f z) = a * holomorphicValue A a U f := by
  letI : CompleteSpace A := hA.1
  let Γ := selectedCycle (algebraSpectrum ℂ A a) U
  have hΓ := selected_cycle_admissible A hA a U hU hKU
  have htr : Γ.trace ⊆ U := fun z hz => (hΓ.1 hz).1
  have hr : Γ.trace ⊆ algebraResolventSet ℂ A a := fun z hz => not_not.mp (hΓ.1 hz).2
  have hfc := hf.continuousOn.mono htr
  have hc := contour_integrand_continuous Γ a hr hfc
  have hm (z : ℂ) (hz : z ∈ Γ.trace) :
      z • algebraResolvent ℂ A a z = a * algebraResolvent ℂ A a z + 1 := by
    have hi := (algebraResolvent_inverse ℂ A a z (hr hz)).1
    rw [sub_mul, smul_mul_assoc, one_mul] at hi
    exact (sub_eq_iff_eq_add).mp hi |>.trans (add_comm _ _)
  have he : cycleIntegral Γ (fun z => (z * f z) • algebraResolvent ℂ A a z) =
      a * cycleIntegral Γ (fun z => f z • algebraResolvent ℂ A a z) := by
    calc
      _ = cycleIntegral Γ (fun z => a * (f z • algebraResolvent ℂ A a z) + f z • (1 : A)) := by
        apply cycleIntegral_congr Γ
        intro z hz
        change (z * f z) • resolvent a z = a * (f z • resolvent a z) + f z • (1 : A)
        have hm' : z • resolvent a z = a * resolvent a z + 1 := hm z hz
        rw [mul_comm z (f z), mul_smul, hm', smul_add, mul_smul_comm]
      _ = cycleIntegral Γ (fun z => a * (f z • algebraResolvent ℂ A a z)) +
          cycleIntegral Γ (fun z => f z • (1 : A)) :=
        cycleIntegral_add Γ (continuousOn_const.mul hc) (hfc.smul continuousOn_const)
      _ = _ := by
        rw [← show (ContinuousLinearMap.mul ℂ A a) (cycleIntegral Γ (fun z => f z • algebraResolvent ℂ A a z)) =
          cycleIntegral Γ (fun z => a * (f z • algebraResolvent ℂ A a z)) from
          map_cycleIntegral Γ (ContinuousLinearMap.mul ℂ A a) hc,
          cycleIntegral_smul_const, cycleIntegral_holomorphic_eq_zero Γ hU htr hΓ.2.2.2 hf,
          zero_smul, add_zero]
        rfl
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      cycleIntegral Γ (fun z => (z * f z) • algebraResolvent ℂ A a z) = _
  rw [he, ← mul_smul_comm]
  rfl

/-- The coordinate function is sent to the original algebra element. -/
theorem coordinate : Spec.Coordinate.{u} := by
  intro A _ _ hA a U hU hKU
  have h := holomorphicValue_coordinate_mul hA a hU hKU (differentiableOn_const 1)
  change holomorphicValue A a U id = a
  simp only [mul_one, unitality A hA a U hU hKU] at h
  exact h

lemma holomorphicValue_pow (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} (hU : IsOpen U) (hKU : algebraSpectrum ℂ A a ⊆ U) (n : ℕ) :
    holomorphicValue A a U (fun z => z ^ n) = a ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using unitality A hA a U hU hKU
  | succ n ih =>
    have h := holomorphicValue_coordinate_mul hA a hU hKU (differentiableOn_id.pow n)
    change holomorphicValue A a U (fun z => z * z ^ n) =
      a * holomorphicValue A a U (fun z => z ^ n) at h
    simpa only [← pow_succ', ih] using h

/-- Agreement with every complex polynomial, including constants and zero. -/
theorem polynomial_agreement : Spec.PolynomialAgreement.{u} := by
  intro A _ _ hA a U p hU hKU
  letI : CompleteSpace A := hA.1
  have hΓ := selected_cycle_admissible A hA a U hU hKU
  let Γ := selectedCycle (algebraSpectrum ℂ A a) U
  have hr : Γ.trace ⊆ algebraResolventSet ℂ A a := fun z hz => not_not.mp (hΓ.1 hz).2
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, map_add]
    calc
      _ = holomorphicValue A a U (fun z => p.eval z) +
          holomorphicValue A a U (fun z => q.eval z) :=
        contourValue_add Γ a hr
          (p.differentiableOn.continuousOn.mono (fun z hz => (hΓ.1 hz).1))
          (q.differentiableOn.continuousOn.mono (fun z hz => (hΓ.1 hz).1))
      _ = _ := congrArg₂ (· + ·) hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial, Polynomial.aeval_monomial]
    calc
      _ = c • holomorphicValue A a U (fun z => z ^ n) := contourValue_smul Γ a c _
      _ = (algebraMap ℂ A c) * a ^ n := by
        rw [holomorphicValue_pow hA a hU hKU, Algebra.smul_def]

/-- Resolvent agreement follows by applying the coordinate relation to (lam-z)⁻¹. -/
theorem resolvent_agreement : Spec.ResolventAgreement.{u} := by
  intro A _ _ hA a U lam hU hKU hlam hlamres
  letI : CompleteSpace A := hA.1
  let g : ℂ → ℂ := fun z => (lam - z)⁻¹
  have hg : DifferentiableOn ℂ g U :=
    (differentiableOn_const lam |>.sub differentiableOn_id).inv
      (fun z hz => sub_ne_zero.mpr (fun he => hlam ((show lam = z from he) ▸ hz)))
  have hlin := scalar_linearity A hA a U g (fun z => z * g z) lam (-1) hU hKU
    hg (differentiableOn_id.mul hg)
  have hfg : EqOn (fun z => lam * g z + (-1) * (z * g z)) (fun _ => 1) U := by
    intro z hz
    have hne : lam - z ≠ 0 := sub_ne_zero.mpr (fun he => hlam (he ▸ hz))
    dsimp [g]
    rw [neg_one_mul, ← sub_eq_add_neg, ← sub_mul, mul_inv_cancel₀ hne]
  have hi : (algebraMap ℂ A lam - a) * holomorphicValue A a U g = 1 := by
    calc
      _ = lam • holomorphicValue A a U g - a * holomorphicValue A a U g := by
        rw [sub_mul, ← Algebra.smul_def]
      _ = lam • holomorphicValue A a U g + (-1 : ℂ) •
          holomorphicValue A a U (fun z => z * g z) := by
        rw [holomorphicValue_coordinate_mul hA a hU hKU hg, neg_one_smul, sub_eq_add_neg]
      _ = holomorphicValue A a U (fun z => lam * g z + (-1) * (z * g z)) := hlin.symm
      _ = holomorphicValue A a U (fun _ => 1) := holomorphicValue_congr hA a hU hKU hfg
      _ = 1 := unitality A hA a U hU hKU
  have he := congrArg (fun x : A => algebraResolvent ℂ A a lam * x) hi
  have hinv : algebraResolvent ℂ A a lam * (algebraMap ℂ A lam - a) = 1 := by
    simpa only [← Algebra.algebraMap_eq_smul_one, AlgebraResolventValue, algebraResolvent, resolvent] using
      (algebraResolvent_inverse ℂ A a lam hlamres).2
  change holomorphicValue A a U g = algebraResolvent ℂ A a lam
  simpa only [← mul_assoc, hinv, one_mul, mul_one] using he


/-- Scalar Cauchy's formula for the finite cycles used by the calculus. -/
lemma scalar_cauchy_formula (Γ : Cycle) {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hΓ : Γ.trace ⊆ U) (hnull : ∀ z ∉ U, Γ.winding z = 0)
    (hf : DifferentiableOn ℂ f U) {w : ℂ} (hw : w ∈ U)
    (hwΓ : w ∉ Γ.trace) (hwind : Γ.winding w = 1) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      cycleIntegral Γ (fun z => f z * (z - w)⁻¹) = f w := by
  have hd : DifferentiableOn ℂ (dslope f w) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hw)).mpr hf
  have hz := cycleIntegral_holomorphic_eq_zero Γ hU hΓ hnull hd
  have hc := hf.continuousOn.mono hΓ
  have hk := continuousOn_cycle_kernel Γ hwΓ
  have he : cycleIntegral Γ (dslope f w) =
      cycleIntegral Γ (fun z => f z * (z - w)⁻¹) -
        f w * cycleIntegral Γ (fun z => (z - w)⁻¹) := by
    calc
      _ = cycleIntegral Γ (fun z => f z * (z - w)⁻¹ - f w * (z - w)⁻¹) := by
        apply cycleIntegral_congr Γ
        intro z hz
        have hzw : z ≠ w := fun he => hwΓ (he ▸ hz)
        rw [dslope_of_ne _ hzw, slope_def_field, div_eq_mul_inv, sub_mul]
      _ = _ := by
        have he := cycleIntegral_sub Γ (hc.mul hk) ((continuousOn_const (c := f w)).mul hk)
        change cycleIntegral Γ (fun z => f z * (z - w)⁻¹ - f w * (z - w)⁻¹) =
          cycleIntegral Γ (fun z => f z * (z - w)⁻¹) -
            cycleIntegral Γ (fun z => f w * (z - w)⁻¹) at he
        exact he.trans (congrArg (fun x => cycleIntegral Γ (fun z => f z * (z - w)⁻¹) - x)
          (cycleIntegral_const_mul Γ _ (f w)))
  have he' := sub_eq_zero.mp (he.symm.trans hz)
  rw [he']
  calc
    _ = f w * ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        cycleIntegral Γ (fun z => (z - w)⁻¹)) := by ring
    _ = f w := by rw [show (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        cycleIntegral Γ (fun z => (z - w)⁻¹) = 1 from hwind, mul_one]

/-- Multiplying the calculus by a resolvent, with an arbitrary holomorphic numerator. -/
lemma holomorphicValue_div_coordinate (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hKU : algebraSpectrum ℂ A a ⊆ U) (hf : DifferentiableOn ℂ f U)
    (z : ℂ) (hz : z ∉ U) (hzres : z ∈ algebraResolventSet ℂ A a) :
    holomorphicValue A a U (fun w => (z - w)⁻¹ * f w) =
      algebraResolvent ℂ A a z * holomorphicValue A a U f := by
  let h : ℂ → ℂ := fun w => (z - w)⁻¹ * f w
  have hh : DifferentiableOn ℂ h U :=
    ((differentiableOn_const z |>.sub differentiableOn_id).inv
      (fun w hw => sub_ne_zero.mpr (fun he => hz ((show z = w from he) ▸ hw)))).mul hf
  have hlin := scalar_linearity A hA a U h (fun w => w * h w) z (-1) hU hKU
    hh (differentiableOn_id.mul hh)
  have hfg : EqOn (fun w => z * h w + (-1) * (w * h w)) f U := by
    intro w hw
    have hne : z - w ≠ 0 := sub_ne_zero.mpr (fun he => hz (he ▸ hw))
    dsimp [h]
    rw [neg_one_mul, ← sub_eq_add_neg, ← sub_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hi : (algebraMap ℂ A z - a) * holomorphicValue A a U h =
      holomorphicValue A a U f := by
    calc
      _ = z • holomorphicValue A a U h - a * holomorphicValue A a U h := by
        rw [sub_mul, ← Algebra.smul_def]
      _ = z • holomorphicValue A a U h + (-1 : ℂ) •
          holomorphicValue A a U (fun w => w * h w) := by
        rw [holomorphicValue_coordinate_mul hA a hU hKU hh, neg_one_smul, sub_eq_add_neg]
      _ = holomorphicValue A a U (fun w => z * h w + (-1) * (w * h w)) := hlin.symm
      _ = _ := holomorphicValue_congr hA a hU hKU hfg
  have he := congrArg (fun x : A => algebraResolvent ℂ A a z * x) hi
  have hinv : algebraResolvent ℂ A a z * (algebraMap ℂ A z - a) = 1 := by
    simpa only [← Algebra.algebraMap_eq_smul_one, AlgebraResolventValue, algebraResolvent, resolvent] using
      (algebraResolvent_inverse ℂ A a z hzres).2
  simpa only [← mul_assoc, hinv, one_mul] using he

end Normalization


section Fubini
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma continuousOn_vector_intervalIntegral {Z : Type*} [TopologicalSpace Z]
    [FirstCountableTopology Z] {F : Z → ℝ → X} {U : Set Z}
    (hF : ContinuousOn F.uncurry (U ×ˢ Icc 0 1)) :
    ContinuousOn (fun z => ∫ t in (0 : ℝ)..1, F z t) U := by
  intro z hz
  have hc : ∀ᶠ w in 𝓝[U] z, ContinuousOn (F w) (Set.uIcc 0 1) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [Set.uIcc_of_le zero_le_one]
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hw, ht⟩)
  have hu : TendstoUniformlyOn F (F z) (𝓝[U] z) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨V, hV, hv⟩ := isCompact_Icc.mem_uniformity_of_prod hF hz (Metric.dist_mem_uniformity hε)
    filter_upwards [hV] with w hw t ht
    simpa only [Set.mem_ofPred_eq, dist_comm] using hv w hw t ht
  exact hu.tendsto_intervalIntegral_of_continuousOn hc

lemma continuousOn_vector_cycleIntegral (Γ : Cycle) {F : ℂ → ℂ → X} {U : Set ℂ}
    (hF : ContinuousOn F.uncurry (U ×ˢ Γ.trace)) :
    ContinuousOn (fun z => cycleIntegral Γ (F z)) U := by
  unfold cycleIntegral
  apply continuousOn_finsetSum
  intro i hi
  apply continuousOn_vector_intervalIntegral
  have hp : ContinuousOn (fun p : ℂ × ℝ => (Γ.arc i).path p.2) (U ×ˢ Icc 0 1) :=
    (Γ.arc i).continuousOn_path.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hv : ContinuousOn (fun p : ℂ × ℝ => (Γ.arc i).velocity p.2) (U ×ˢ Icc 0 1) :=
    (Γ.arc i).continuousOn_velocity.comp continuous_snd.continuousOn (fun p hp => hp.2)
  exact hv.smul (hF.comp (continuous_fst.continuousOn.prodMk hp)
    (fun p hp => ⟨hp.1, Γ.path_mem_trace i hp.2⟩))

lemma cycleIntegral_intervalIntegral (Γ : Cycle) {F : ℂ → ℝ → X}
    (hF : ContinuousOn F.uncurry (Γ.trace ×ˢ Icc 0 1)) :
    cycleIntegral Γ (fun z => ∫ t in (0 : ℝ)..1, F z t) =
      ∫ t in (0 : ℝ)..1, cycleIntegral Γ (fun z => F z t) := by
  have hG (i : Fin Γ.count) : ContinuousOn
      (fun p : ℝ × ℝ => (Γ.arc i).velocity p.1 • F ((Γ.arc i).path p.1) p.2)
      (Icc 0 1 ×ˢ Icc 0 1) := by
    exact ((Γ.arc i).continuousOn_velocity.comp continuous_fst.continuousOn (fun p hp => hp.1)).smul
      (hF.comp (((Γ.arc i).continuousOn_path.comp continuous_fst.continuousOn (fun p hp => hp.1)).prodMk
        continuous_snd.continuousOn) (fun p hp => ⟨Γ.path_mem_trace i hp.1, hp.2⟩))
  have hswap (i : Fin Γ.count) :
      (∫ s in (0 : ℝ)..1, (Γ.arc i).velocity s • ∫ t in (0 : ℝ)..1, F ((Γ.arc i).path s) t) =
      ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, (Γ.arc i).velocity s • F ((Γ.arc i).path s) t := by
    simp_rw [← intervalIntegral.integral_smul]
    apply intervalIntegral_intervalIntegral_swap
    apply ((hG i).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    simpa only [uIoc_of_le zero_le_one] using
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self :
        Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 ⊆ Icc 0 1 ×ˢ Icc 0 1)
  have hint (i : Fin Γ.count) : IntervalIntegrable
      (fun t => ∫ s in (0 : ℝ)..1, (Γ.arc i).velocity s • F ((Γ.arc i).path s) t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    apply continuousOn_vector_intervalIntegral
    exact (hG i).comp (continuous_swap.continuousOn) (fun p hp => ⟨hp.2, hp.1⟩)
  simp only [cycleIntegral, hswap]
  exact (intervalIntegral.integral_finsetSum (fun i _ => hint i)).symm

/-- Fubini for two arbitrary finite C¹ cycles and a continuous Banach-valued kernel. -/
lemma cycleIntegral_swap (Γ Δ : Cycle) {F : ℂ → ℂ → X}
    (hF : ContinuousOn F.uncurry (Γ.trace ×ˢ Δ.trace)) :
    cycleIntegral Γ (fun z => cycleIntegral Δ (F z)) =
      cycleIntegral Δ (fun w => cycleIntegral Γ (fun z => F z w)) := by
  have hc (j : Fin Δ.count) : ContinuousOn
      (fun p : ℂ × ℝ => (Δ.arc j).velocity p.2 • F p.1 ((Δ.arc j).path p.2))
      (Γ.trace ×ˢ Icc 0 1) := by
    exact ((Δ.arc j).continuousOn_velocity.comp continuous_snd.continuousOn (fun p hp => hp.2)).smul
      (hF.comp (continuous_fst.continuousOn.prodMk
        ((Δ.arc j).continuousOn_path.comp continuous_snd.continuousOn (fun p hp => hp.2)))
        (fun p hp => ⟨hp.1, Δ.path_mem_trace j hp.2⟩))
  change cycleIntegral Γ (fun z => ∑ j, ∫ t in (0 : ℝ)..1,
      (Δ.arc j).velocity t • F z ((Δ.arc j).path t)) = _
  rw [cycleIntegral_sum Γ Finset.univ
    (fun j z => ∫ t in (0 : ℝ)..1, (Δ.arc j).velocity t • F z ((Δ.arc j).path t))
    (fun j _ => continuousOn_vector_intervalIntegral
      (F := fun z t => (Δ.arc j).velocity t • F z ((Δ.arc j).path t)) (hc j))]
  unfold cycleIntegral
  apply Finset.sum_congr rfl
  intro j hj
  change cycleIntegral Γ (fun z => ∫ t in (0 : ℝ)..1,
      (Δ.arc j).velocity t • F z ((Δ.arc j).path t)) =
    ∫ t in (0 : ℝ)..1, (Δ.arc j).velocity t • cycleIntegral Γ (fun z => F z ((Δ.arc j).path t))
  rw [cycleIntegral_intervalIntegral Γ
    (F := fun z t => (Δ.arc j).velocity t • F z ((Δ.arc j).path t)) (hc j)]
  simp only [cycleIntegral_smul]
end Fubini


/-- Multiplicativity follows from Cauchy's formula and Fubini on nested cycles. -/
theorem multiplicativity : Spec.Multiplicativity.{u} := by
  intro A _ _ hA a U f g hU hKU hf hg
  letI : CompleteSpace A := hA.1
  let Γ := selectedCycle (algebraSpectrum ℂ A a) U
  have hΓ := selected_cycle_admissible A hA a U hU hKU
  obtain ⟨V, hV, hKV, hd, hwind⟩ := hΓ.2.2.1
  let W := V ∩ U
  have hW : IsOpen W := hV.inter hU
  have hKW : algebraSpectrum ℂ A a ⊆ W := fun z hz => ⟨hKV hz, hKU hz⟩
  let Δ := selectedCycle (algebraSpectrum ℂ A a) W
  have hΔ := selected_cycle_admissible A hA a W hW hKW
  have hΔU : Δ.Admissible (algebraSpectrum ℂ A a) U :=
    hΔ.mono_domain inter_subset_right
  have htrΓ : Γ.trace ⊆ U := fun z hz => (hΓ.1 hz).1
  have htrΔ : Δ.trace ⊆ W := fun w hw => (hΔ.1 hw).1
  have hrΓ : Γ.trace ⊆ algebraResolventSet ℂ A a := fun z hz => not_not.mp (hΓ.1 hz).2
  have hrΔ : Δ.trace ⊆ algebraResolventSet ℂ A a := fun w hw => not_not.mp (hΔ.1 hw).2
  have hdisj (z : ℂ) (hz : z ∈ Γ.trace) : z ∉ W :=
    fun h => Set.disjoint_left.mp hd h.1 hz
  have hne (z : ℂ) (hz : z ∈ Γ.trace) (w : ℂ) (hw : w ∈ Δ.trace) : z - w ≠ 0 :=
    sub_ne_zero.mpr (fun he => hdisj z hz (he ▸ htrΔ hw))
  let c : ℂ := (2 * Real.pi * Complex.I)⁻¹
  let G : A := holomorphicValue A a W g
  let H : ℂ → ℂ → A := fun z w => (f z * ((z - w)⁻¹ * g w)) • resolvent a w
  have hcont : ContinuousOn H.uncurry (Γ.trace ×ˢ Δ.trace) := by
    have hf' := hf.continuousOn.mono htrΓ
    have hg' := hg.continuousOn.mono (htrΔ.trans inter_subset_right)
    have hr' : ContinuousOn (fun w => resolvent a w) Δ.trace :=
      continuousOn_resolvent_trace Δ a hrΔ
    exact ((hf'.comp continuous_fst.continuousOn (fun p hp => hp.1)).mul
      (((continuous_fst.continuousOn.sub continuous_snd.continuousOn).inv₀
        (fun p hp => hne p.1 hp.1 p.2 hp.2)).mul
          (hg'.comp continuous_snd.continuousOn (fun p hp => hp.2)))).smul
      (hr'.comp continuous_snd.continuousOn (fun p hp => hp.2))
  have hinner (z : ℂ) (hz : z ∈ Γ.trace) :
      c • cycleIntegral Δ (H z) = (f z • resolvent a z) * G := by
    have hdiv := holomorphicValue_div_coordinate hA a hW hKW
      (hg.mono inter_subset_right) z (hdisj z hz) (hrΓ hz)
    calc
      _ = contourValue A Δ a (fun w => f z * ((z - w)⁻¹ * g w)) := rfl
      _ = f z • holomorphicValue A a W (fun w => (z - w)⁻¹ * g w) :=
        contourValue_smul Δ a (f z) _
      _ = f z • (resolvent a z * G) := congrArg (fun x : A => f z • x) hdiv
      _ = _ := (smul_mul_assoc ..).symm
  have houter (w : ℂ) (hw : w ∈ Δ.trace) :
      c • cycleIntegral Γ (fun z => H z w) = (f w * g w) • resolvent a w := by
    have hwV : w ∈ V := (htrΔ hw).1
    have hcauchy := scalar_cauchy_formula Γ hU htrΓ hΓ.2.2.2 hf
      (htrΔ hw).2 (fun hwΓ => Set.disjoint_left.mp hd hwV hwΓ) (hwind w hwV)
    calc
      _ = c • cycleIntegral Γ (fun z => (f z * (z - w)⁻¹) • (g w • resolvent a w)) := by
        apply congrArg (fun x : A => c • x)
        apply cycleIntegral_congr Γ
        intro z hz
        dsimp [H]
        rw [smul_smul, mul_assoc]
      _ = c • (cycleIntegral Γ (fun z => f z * (z - w)⁻¹) • (g w • resolvent a w)) := by
        rw [cycleIntegral_smul_const]
      _ = (f w * g w) • resolvent a w := by
        rw [smul_smul, show c * cycleIntegral Γ (fun z => f z * (z - w)⁻¹) = f w from hcauchy,
          smul_smul]
  have hfg : holomorphicValue A a U (fun z => f z * g z) =
      c • cycleIntegral Δ (fun w => (f w * g w) • resolvent a w) :=
    holomorphic_formula A hA a U _ hU hKU (hf.mul hg) Δ hΔU
  have hgchange : G = holomorphicValue A a U g :=
    (holomorphic_formula A hA a U g hU hKU hg Δ hΔU).symm
  calc
    _ = c • cycleIntegral Δ (fun w => (f w * g w) • resolvent a w) := hfg
    _ = c • cycleIntegral Δ (fun w => c • cycleIntegral Γ (fun z => H z w)) := by
      apply congrArg (fun x : A => c • x)
      exact cycleIntegral_congr Δ (fun w hw => (houter w hw).symm)
    _ = c • (c • cycleIntegral Δ (fun w => cycleIntegral Γ (fun z => H z w))) := by
      rw [cycleIntegral_smul]
    _ = c • (c • cycleIntegral Γ (fun z => cycleIntegral Δ (H z))) := by
      rw [cycleIntegral_swap Γ Δ hcont]
    _ = c • cycleIntegral Γ (fun z => c • cycleIntegral Δ (H z)) := by
      rw [cycleIntegral_smul]
    _ = c • cycleIntegral Γ (fun z => (f z • resolvent a z) * G) := by
      apply congrArg (fun x : A => c • x)
      exact cycleIntegral_congr Γ hinner
    _ = (c • cycleIntegral Γ (fun z => f z • resolvent a z)) * G := by
      have hc : ContinuousOn (fun z => f z • resolvent a z) Γ.trace :=
        contour_integrand_continuous Γ a hrΓ (hf.continuousOn.mono htrΓ)
      have hm := map_cycleIntegral Γ ((ContinuousLinearMap.mul ℂ A).flip G) hc
      change (cycleIntegral Γ (fun z => f z • resolvent a z)) * G =
        cycleIntegral Γ (fun z => (f z • resolvent a z) * G) at hm
      rw [← hm, smul_mul_assoc]
    _ = holomorphicValue A a U f * holomorphicValue A a U g :=
      congrArg (fun x : A => holomorphicValue A a U f * x) hgchange

end ExpandedFA.BanachAlgebra.HolomorphicHomomorphism
