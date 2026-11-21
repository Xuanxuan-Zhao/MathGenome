import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.WatsonTail
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Absolute
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Comparison
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaDefinition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Products

noncomputable section
namespace SingleVariableAnalysis.WatsonTail
open Set Filter MeasureTheory
open scoped Topology BigOperators
open Riemann Riemann.Improper
open Specs.SingleVariableAnalysis.Ch17.WatsonTail
abbrev Value := Specs.SingleVariableAnalysis.Ch17.WatsonTail.Scalar

/-- Damping preserves proper Riemann integrability; no continuity of q is required. -/
theorem damped_local (k : ScalarKind) (q : ℝ → Value k)
    (hq : LocallyIntegrable k q (0 : WithBot ℝ) ⊤) (lam : ℝ) :
    LocallyIntegrable k (damped k q lam) (0 : WithBot ℝ) ⊤ := by
  intro u v hu huv hv
  have hq' := hq u v hu huv hv
  have he : RealIntegrable (fun t => Real.exp (-lam * t)) u v :=
    (positive_continuous_darboux
      (fun t _ => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt)
      (WithBot.coe_lt_coe.mp hu) huv).choose
  cases k with
  | real => exact real_product he hq'
  | complex =>
    let qc : ℝ → ℂ := q
    have hqc : ComplexIntegrable qc u v := hq'
    change ComplexIntegrable (fun t => (Real.exp (-lam*t) : ℂ) * qc t) u v
    constructor
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using real_product he hqc.1
    · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_zero] using real_product he hqc.2

theorem norm_local (k : ScalarKind) (q : ℝ → Value k)
    (hq : LocallyIntegrable k q (0 : WithBot ℝ) ⊤) :
    LocallyIntegrable .real (fun t => ‖q t‖) (0 : WithBot ℝ) ⊤ := by
  intro u v hu huv hv
  exact (scalar_integral_norm_le k q (hq u v hu huv hv)).choose

@[simp] theorem norm_damped (k : ScalarKind) (q : ℝ → Value k) (lam t : ℝ) :
    ‖damped k q lam t‖ = Real.exp (-lam * t) * ‖q t‖ := by
  simp [damped, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem gamma_local (s : ℝ) :
    LocallyIntegrable .real (gammaKernel s) (0 : WithBot ℝ) ⊤ := by
  intro u v hu huv _
  exact (gamma_proper_truncations s u v (WithBot.coe_lt_coe.mp hu) huv).choose

theorem gamma_right_converges (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) :
    RightConverges .real (gammaKernel s) δ ⊤ := by
  exact ⟨_, right_change_split .real (gammaKernel s) (gamma_local s)
    ⟨1, WithBot.coe_lt_coe.mpr zero_lt_one, WithTop.coe_lt_top _⟩
    ⟨δ, WithBot.coe_lt_coe.mpr hδ, WithTop.coe_lt_top _⟩ _
    (gamma_independent_limits s hs).2⟩

/-- Comparison passes to the finite endpoint values, including nonunit constants. -/
theorem right_integral_scaled_bound (f g : ℝ → ℝ) (δ A G C : ℝ)
    (hA : RightHasIntegral .real f δ ⊤ A)
    (hG : RightHasIntegral .real g δ ⊤ G) (hC : 0 ≤ C)
    (hfg : ∀ t : ℝ, δ ≤ t → 0 ≤ f t ∧ f t ≤ C * g t) : A ≤ C * G := by
  rcases hA with ⟨hf, hA⟩
  rcases hG with ⟨hg, hG⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  let e := ε / (2 * (C + 1))
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨r, hr⟩ := hA e he
  obtain ⟨s, hs⟩ := hG e he
  obtain ⟨t, hrt, hst⟩ := right_later r s
  have ha := hr t hrt
  have hg' := hs t hst
  have hi := (realIntegral_scaled_comparison (hf.2 t) (hg.2 t)
    (fun x hx => hfg x hx.1)).2
  change |realIntegral f (hf.2 t) - A| < e at ha
  change |realIntegral g (hg.2 t) - G| < e at hg'
  have heq : e * (2 * (C + 1)) = ε := by
    dsimp [e]
    exact div_mul_cancel₀ _ (by positivity)
  have hprod := mul_le_mul_of_nonneg_left (abs_lt.mp hg').2.le hC
  nlinarith [(abs_lt.mp ha).1]

/-- A baseline damping converts absolute convergence into an exponential tail. -/
theorem tail_from_baseline (k : ScalarKind) (q : ℝ → Value k)
    (hq : LocallyIntegrable k q (0 : WithBot ℝ) ⊤) (δ : ℝ) (hδ : 0 < δ)
    (lam0 : ℝ) (h0 : 0 < lam0)
    (hbase : RightConverges .real (fun t => ‖damped k q lam0 t‖) δ ⊤) :
    exponentialTail k q δ := by
  obtain ⟨G, hG⟩ := hbase
  change ℝ at G
  refine ⟨|G|, abs_nonneg _, max 1 (2 * lam0), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun lam hlam => ?_⟩
  have hl2 : 2 * lam0 ≤ lam := (le_max_right _ _).trans hlam
  have hl0 : lam0 ≤ lam := by linarith
  let C := Real.exp (-(lam - lam0) * δ)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hpoint (t : ℝ) (ht : δ ≤ t) :
      0 ≤ ‖damped k q lam t‖ ∧
      ‖damped k q lam t‖ ≤ C * ‖damped k q lam0 t‖ := by
    refine ⟨norm_nonneg _, ?_⟩
    rw [norm_damped, norm_damped, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have he : Real.exp (-lam * t) =
        Real.exp (-(lam - lam0) * t) * Real.exp (-lam0 * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hl0) (sub_nonneg.mpr ht)]))
      (Real.exp_pos _).le
  let hloc := damped_local k q hq lam
  let hnloc := norm_local k _ hloc
  let c : RegularPoint (0 : WithBot ℝ) ⊤ :=
    ⟨δ, WithBot.coe_lt_coe.mpr hδ, WithTop.coe_lt_top _⟩
  have hn : RightConverges .real (fun t => ‖damped k q lam t‖) δ ⊤ := by
    apply right_scaled_comparison _ _ δ ⊤ (local_right_regular .real _ hnloc c) hG.choose
      C hC _ ⟨G, hG⟩
    exact ⟨⟨δ + 1, by linarith, WithTop.coe_lt_top _⟩,
      fun t _ => hpoint t.val t.property.1.le⟩
  obtain ⟨A, hA⟩ := hn
  change ℝ at A
  obtain ⟨T, hT⟩ := right_absolute_converges k _ δ ⊤
    (local_right_regular k _ hloc c) ⟨A, hA⟩
  refine ⟨T, A, hT, hA, right_norm_bound k _ δ ⊤ T A hT hA, ?_⟩
  calc
    A ≤ C * G := right_integral_scaled_bound _ _ δ A G C hA hG hC hpoint
    _ ≤ C * |G| := mul_le_mul_of_nonneg_left (le_abs_self G) hC
    _ = |G| * C := mul_comm _ _
    _ ≤ |G| * Real.exp (-lam * δ / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
        (abs_nonneg _)

/-- The finite local expansion implies the integrable leading power bound. -/
theorem expansion_power_bound (k : ScalarKind) (N : ℕ) (α : ℝ)
    (a : Fin N → Value k) (q : ℝ → Value k)
    (hexp : localExpansion k N α a q) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t ≤ η →
      ‖q t‖ ≤ D * t ^ (α - 1) := by
  obtain ⟨D, hD, η, hη, hrem⟩ := hexp
  refine ⟨D + ∑ j, ‖a j‖, add_nonneg hD (Finset.sum_nonneg (fun _ _ => norm_nonneg _)),
    min η 1, lt_min hη zero_lt_one, fun t ht htη => ?_⟩
  have ht1 : t ≤ 1 := htη.trans (min_le_right _ _)
  have hp (n : ℕ) : t ^ (α + (n : ℝ) - 1) ≤ t ^ (α - 1) := by
    rw [show α + (n : ℝ) - 1 = (α - 1) + (n : ℝ) by ring,
      Real.rpow_add ht, Real.rpow_natCast]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht.le _) (pow_le_one₀ ht.le ht1)
  have hs : ‖∑ j : Fin N, (t ^ (α + (j : ℕ) - 1)) • a j‖ ≤
      (∑ j : Fin N, ‖a j‖) * t ^ (α - 1) := by
    calc
      _ ≤ ∑ j : Fin N, ‖(t ^ (α + (j : ℕ) - 1)) • a j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin N, ‖a j‖ * t ^ (α - 1) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
        exact (mul_le_mul_of_nonneg_right (hp j.val) (norm_nonneg _)).trans_eq (mul_comm _ _)
      _ = _ := (Finset.sum_mul ..).symm
  have htri := norm_add_le
    (q t - ∑ j : Fin N, (t ^ (α + (j : ℕ) - 1)) • a j)
    (∑ j : Fin N, (t ^ (α + (j : ℕ) - 1)) • a j)
  rw [sub_add_cancel] at htri
  have hr := (hrem t ht (htη.trans (min_le_left _ _))).trans
    (mul_le_mul_of_nonneg_left (hp N) hD)
  calc
    _ ≤ _ := htri
    _ ≤ D * t ^ (α - 1) + (∑ j : Fin N, ‖a j‖) * t ^ (α - 1) := add_le_add hr hs
    _ = _ := by ring

/-- The Gamma kernel supplies a positive, convergent comparator at 0+. -/
theorem left_norm_of_power_bound (k : ScalarKind) (q : ℝ → Value k)
    (hq : LocallyIntegrable k q (0 : WithBot ℝ) ⊤)
    (α D η : ℝ) (hα : 0 < α) (hD : 0 ≤ D) (hη : 0 < η)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ η → ‖q t‖ ≤ D * t ^ (α - 1))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    LeftConverges .real (fun t => ‖damped k q lam t‖) (0 : WithBot ℝ) 1 := by
  let hnloc := norm_local k _ (damped_local k q hq lam)
  apply left_scaled_comparison _ (gammaKernel α) (0 : WithBot ℝ) 1
    (local_left_regular .real _ hnloc
      ⟨1, WithBot.coe_lt_coe.mpr zero_lt_one, WithTop.coe_lt_top _⟩)
    (gamma_left_regular α) (D * Real.exp 1) (mul_nonneg hD (Real.exp_pos _).le) _
    ⟨_, (gamma_independent_limits α hα).1⟩
  have hm : 0 < min η 1 := lt_min hη zero_lt_one
  refine ⟨⟨min η 1 / 2, WithBot.coe_lt_coe.mpr (half_pos hm), by
    linarith [min_le_right η 1]⟩, fun t htr => ?_⟩
  have ht : 0 < t.val := WithBot.coe_lt_coe.mp t.property.1
  have htη : t.val ≤ η := by linarith [min_le_left η 1]
  have ht1 : t.val ≤ 1 := t.property.2.le
  have hg : 0 ≤ gammaKernel α t.val := (gammaKernel_pos α t.val ht).le
  have hcancel : t.val ^ (α - 1) = Real.exp t.val * gammaKernel α t.val := by
    dsimp [gammaKernel, GSpec.gammaKernelValue]
    rw [mul_left_comm, ← Real.exp_add]
    simp
  refine ⟨norm_nonneg _, ?_⟩
  calc
    ‖damped k q lam t.val‖ ≤ ‖q t.val‖ := by
      rw [norm_damped]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (by nlinarith))
    _ ≤ D * t.val ^ (α - 1) := hbound t.val ht htη
    _ ≤ D * (Real.exp 1 * gammaKernel α t.val) := by
      rw [hcancel]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht1) hg) hD
    _ = _ := by ring

/-- Eventual exponential growth controls the infinite endpoint for large damping. -/
theorem right_norm_of_growth (k : ScalarKind) (q : ℝ → Value k)
    (hq : LocallyIntegrable k q (0 : WithBot ℝ) ⊤)
    (C c A : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, A ≤ t → ‖q t‖ ≤ C * Real.exp (c * t))
    (δ : ℝ) (hδ : 0 < δ) (lam : ℝ) (hlam : c + 1 ≤ lam) :
    RightConverges .real (fun t => ‖damped k q lam t‖) δ ⊤ := by
  let hnloc := norm_local k _ (damped_local k q hq lam)
  have hg := gamma_right_converges 1 δ zero_lt_one hδ
  apply right_scaled_comparison _ (gammaKernel 1) δ ⊤
    (local_right_regular .real _ hnloc
      ⟨δ, WithBot.coe_lt_coe.mpr hδ, WithTop.coe_lt_top _⟩)
    hg.choose_spec.choose C hC _ hg
  let r := max δ (max A 0) + 1
  have hrδ : δ < r := (le_max_left _ _).trans_lt (lt_add_one _)
  refine ⟨⟨r, hrδ, WithTop.coe_lt_top _⟩, fun t hrt => ?_⟩
  have htA : A ≤ t.val := le_trans (le_max_left A 0)
    ((le_max_right δ (max A 0)).trans (by dsimp [r] at hrt; linarith))
  have ht0 : 0 ≤ t.val := (hδ.trans t.property.1).le
  refine ⟨norm_nonneg _, ?_⟩
  calc
    ‖damped k q lam t.val‖ ≤ Real.exp (-lam * t.val) * (C * Real.exp (c * t.val)) := by
      rw [norm_damped]
      exact mul_le_mul_of_nonneg_left (hbound t.val htA) (Real.exp_pos _).le
    _ = C * Real.exp ((c - lam) * t.val) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ C * Real.exp (-t.val) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) hC
    _ = C * gammaKernel 1 t.val := by simp [gammaKernel, GSpec.gammaKernelValue]

theorem absolute_convergence :
    Specs.SingleVariableAnalysis.Ch17.WatsonTail.absoluteConvergence := by
  intro k N α a q _hN hα hq hexp hgrowth
  obtain ⟨D, hD, η, hη, hbound⟩ := expansion_power_bound k N α a q hexp
  obtain ⟨C, hC, c, A, hgrowth⟩ := hgrowth
  refine ⟨max c 0 + 1, by linarith [le_max_right c 0], fun lam hlam => ?_⟩
  have hlam0 : 0 ≤ lam := by linarith [le_max_right c 0]
  have hlamc : c + 1 ≤ lam := by linarith [le_max_left c 0]
  have hl := left_norm_of_power_bound k q hq α D η hα hD hη hbound lam hlam0
  have hr := right_norm_of_growth k q hq C c A hC hgrowth 1 zero_lt_one lam hlamc
  have hloc := damped_local k q hq lam
  have hnloc := norm_local k _ hloc
  have habs : AbsoluteConverges k (damped k q lam) (0 : WithBot ℝ) ⊤ := by
    obtain ⟨l, hl⟩ := hl
    obtain ⟨r, hr⟩ := hr
    exact ⟨l + r, hnloc,
      ⟨1, WithBot.coe_lt_coe.mpr zero_lt_one, WithTop.coe_lt_top _⟩, l, r, hl, hr, rfl⟩
  exact ⟨habs, absolute_converges k _ _ _ hloc habs⟩

theorem tail_control : Specs.SingleVariableAnalysis.Ch17.WatsonTail.tailControl := by
  intro k q hq hgrowth δ hδ
  obtain ⟨C, hC, c, A, hgrowth⟩ := hgrowth
  apply tail_from_baseline k q hq δ hδ (max c 0 + 1)
    (by linarith [le_max_right c 0])
  exact right_norm_of_growth k q hq C c A hC hgrowth δ hδ _
    (by linarith [le_max_left c 0])

theorem continuous_local (k : ScalarKind) (f : ℝ → Value k)
    (hf : ∀ t : ℝ, 0 < t → ContinuousAt f t) :
    LocallyIntegrable k f (0 : WithBot ℝ) ⊤ := by
  intro u v hu huv _
  cases k with
  | real => exact (positive_continuous_darboux hf (WithBot.coe_lt_coe.mp hu) huv).choose
  | complex =>
    exact ⟨(positive_continuous_darboux
      (fun t ht => Complex.continuous_re.continuousAt.comp (hf t ht))
      (WithBot.coe_lt_coe.mp hu) huv).choose,
      (positive_continuous_darboux
      (fun t ht => Complex.continuous_im.continuousAt.comp (hf t ht))
      (WithBot.coe_lt_coe.mp hu) huv).choose⟩

theorem monomial_local (k : ScalarKind) (a : Value k) (β : ℝ) :
    LocallyIntegrable k (monomial k a β) (0 : WithBot ℝ) ⊤ := by
  apply continuous_local
  intro t ht
  exact (Real.continuousAt_rpow_const t (β - 1) (Or.inl ht.ne')).smul continuousAt_const

theorem monomial_tail (k : ScalarKind) (a : Value k) (β δ : ℝ)
    (hβ : 0 < β) (hδ : 0 < δ) : exponentialTail k (monomial k a β) δ := by
  apply tail_from_baseline k _ (monomial_local k a β) δ hδ 1 zero_lt_one
  have hg := gamma_right_converges β δ hβ hδ
  let hnloc := norm_local k _ (damped_local k _ (monomial_local k a β) 1)
  apply right_scaled_comparison _ (gammaKernel β) δ ⊤
    (local_right_regular .real _ hnloc
      ⟨δ, WithBot.coe_lt_coe.mpr hδ, WithTop.coe_lt_top _⟩)
    hg.choose_spec.choose ‖a‖ (norm_nonneg _) _ hg
  refine ⟨⟨δ + 1, by linarith, WithTop.coe_lt_top _⟩, fun t _ => ⟨norm_nonneg _, ?_⟩⟩
  have ht : 0 ≤ t.val := (hδ.trans t.property.1).le
  apply le_of_eq
  simp only [norm_damped, monomial, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg ht _), neg_one_mul]
  dsimp [gammaKernel, GSpec.gammaKernelValue]
  ring

theorem retained_monomial_tails :
    Specs.SingleVariableAnalysis.Ch17.WatsonTail.retainedMonomialTails := by
  intro k N α a _hN hα δ hδ j
  exact monomial_tail k (a j) (α + (j : ℕ)) δ (by positivity) hδ

end SingleVariableAnalysis.WatsonTail
