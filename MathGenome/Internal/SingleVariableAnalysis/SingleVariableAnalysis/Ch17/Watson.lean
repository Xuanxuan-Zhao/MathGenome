import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.Watson
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.WatsonTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SingleVariableAnalysis.Watson
open Set Filter MeasureTheory
open scoped Topology BigOperators
open Riemann Riemann.Improper
open Specs.SingleVariableAnalysis.Ch17.WatsonTail
abbrev Value := Specs.SingleVariableAnalysis.Ch17.WatsonTail.Scalar
namespace D
export Specs.SingleVariableAnalysis.Ch08.Integral (scalarIntegrableValue scalarIntegralValue)
end D

theorem scalar_add_value (k : ScalarKind) {f g : ℝ → Value k} {u v : ℝ}
    (hf : D.scalarIntegrableValue k f u v) (hg : D.scalarIntegrableValue k g u v) :
    ∃ h : D.scalarIntegrableValue k (fun t => f t + g t) u v,
      D.scalarIntegralValue k _ h = D.scalarIntegralValue k f hf + D.scalarIntegralValue k g hg := by
  cases k with
  | real => exact real_add_value hf hg
  | complex => exact complex_add_value hf hg

theorem scalar_smul_value (k : ScalarKind) {f : ℝ → Value k} {u v : ℝ}
    (hf : D.scalarIntegrableValue k f u v) (c : ℝ) :
    ∃ h : D.scalarIntegrableValue k (fun t => c • f t) u v,
      D.scalarIntegralValue k _ h = c • D.scalarIntegralValue k f hf := by
  cases k with
  | real => exact real_mul_value hf c
  | complex =>
    change (ℝ → ℂ) at f
    change ∃ h : ComplexIntegrable (fun t => (c : ℂ) * f t) u v,
      complexIntegral _ h = (c : ℂ) * complexIntegral f hf
    exact complex_mul_value hf (c : ℂ)

theorem real_smul_value (k : ScalarKind) {f : ℝ → ℝ} {u v : ℝ}
    (hf : RealIntegrable f u v) (a : Value k) :
    ∃ h : D.scalarIntegrableValue k (fun t => f t • a) u v,
      D.scalarIntegralValue k _ h = realIntegral f hf • a := by
  cases k with
  | real =>
    change ℝ at a
    change ∃ h : RealIntegrable (fun t => f t * a) u v,
      realIntegral _ h = realIntegral f hf * a
    simpa only [mul_comm] using real_mul_value hf a
  | complex =>
    change ℂ at a
    change ∃ h : ComplexIntegrable (fun t => (f t : ℂ) * a) u v,
      complexIntegral _ h = (realIntegral f hf : ℂ) * a
    obtain ⟨hr, hvr⟩ := real_mul_value hf a.re
    obtain ⟨hi, hvi⟩ := real_mul_value hf a.im
    have hfr : (fun t => ((f t : ℂ) * a).re) = (fun t => a.re * f t) := by
      funext t; simp [mul_comm]
    have hfi : (fun t => ((f t : ℂ) * a).im) = (fun t => a.im * f t) := by
      funext t; simp [mul_comm]
    refine ⟨⟨hfr.symm ▸ hr, hfi.symm ▸ hi⟩, ?_⟩
    apply Complex.ext
    · rw [(complexIntegral_components _ _).1]
      simpa only [hfr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero, mul_comm] using hvr
    · rw [(complexIntegral_components _ _).2]
      simpa only [hfi, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, add_zero, zero_add, mul_comm] using hvi

noncomputable local instance (a : WithBot ℝ) (b : ℝ) : LinearOrder (LeftIndex a b) := by
  change LinearOrder {t : ℝ // a < (t : WithBot ℝ) ∧ t < b}
  infer_instance
noncomputable local instance (a : ℝ) (b : WithTop ℝ) : LinearOrder (RightIndex a b) := by
  change LinearOrder {t : ℝ // a < t ∧ (t : WithTop ℝ) < b}
  infer_instance

theorem left_tendsto_iff (k : ScalarKind) (f : ℝ → Value k) (a : WithBot ℝ) (b : ℝ)
    (h : LeftRegular k f a b) (L : Value k) :
    LeftHasIntegral k f a b L ↔ Tendsto (LeftTruncation k f a b h) atBot (𝓝 L) := by
  have hn : Nonempty (LeftIndex a b) := by
    cases a using WithBot.recBotCoe with
    | bot => exact ⟨⟨b - 1, WithBot.bot_lt_coe _, sub_one_lt _⟩⟩
    | coe a =>
      obtain ⟨t, hat, htb⟩ := exists_between (WithBot.coe_lt_coe.mp h.1)
      exact ⟨⟨t, WithBot.coe_lt_coe.mpr hat, htb⟩⟩
  let := hn
  constructor
  · rintro ⟨_, hL⟩
    apply (Metric.tendsto_atTop (β := OrderDual (LeftIndex a b))
      (u := LeftTruncation k f a b h) (a := L)).mpr
    intro ε hε
    obtain ⟨r, hr⟩ := hL ε hε
    obtain ⟨s, hsr, _⟩ := left_earlier r r
    exact ⟨s, fun t ht => hr t ((show t.val ≤ s.val from ht).trans_lt hsr)⟩
  · intro hL
    have ht := (Metric.tendsto_atTop (β := OrderDual (LeftIndex a b))
      (u := LeftTruncation k f a b h) (a := L)).mp hL
    exact ⟨h, fun ε hε => by
      obtain ⟨r, hr⟩ := ht ε hε
      exact ⟨r, fun t ht => hr t ht.le⟩⟩

theorem right_tendsto_iff (k : ScalarKind) (f : ℝ → Value k) (a : ℝ) (b : WithTop ℝ)
    (h : RightRegular k f a b) (L : Value k) :
    RightHasIntegral k f a b L ↔ Tendsto (RightTruncation k f a b h) atTop (𝓝 L) := by
  have hn : Nonempty (RightIndex a b) := by
    cases b using WithTop.recTopCoe with
    | top => exact ⟨⟨a + 1, lt_add_one _, WithTop.coe_lt_top _⟩⟩
    | coe b =>
      obtain ⟨t, hat, htb⟩ := exists_between (WithTop.coe_lt_coe.mp h.1)
      exact ⟨⟨t, hat, WithTop.coe_lt_coe.mpr htb⟩⟩
  let := hn
  rw [Metric.tendsto_atTop]
  constructor
  · rintro ⟨_, hL⟩ ε hε
    obtain ⟨r, hr⟩ := hL ε hε
    obtain ⟨s, hrs, _⟩ := right_later r r
    exact ⟨s, fun t ht => hr t (hrs.trans_le ht)⟩
  · intro hL
    exact ⟨h, fun ε hε => by
      obtain ⟨r, hr⟩ := hL ε hε
      exact ⟨r, fun t ht => hr t ht.le⟩⟩

theorem left_add (k : ScalarKind) {f g : ℝ → Value k} {a : WithBot ℝ} {b : ℝ}
    {F G : Value k} (hf : LeftHasIntegral k f a b F) (hg : LeftHasIntegral k g a b G) :
    LeftHasIntegral k (fun t => f t + g t) a b (F + G) := by
  let hrf := hf.choose
  let hrg := hg.choose
  let hr : LeftRegular k (fun t => f t + g t) a b :=
    ⟨hrf.1, fun t => (scalar_add_value k (hrf.2 t) (hrg.2 t)).choose⟩
  apply (left_tendsto_iff k _ a b hr _).mpr
  have ht := ((left_tendsto_iff k f a b hrf F).mp hf).add
    ((left_tendsto_iff k g a b hrg G).mp hg)
  apply ht.congr'
  exact Eventually.of_forall fun t => (scalar_add_value k (hrf.2 t) (hrg.2 t)).choose_spec.symm

theorem right_add (k : ScalarKind) {f g : ℝ → Value k} {a : ℝ} {b : WithTop ℝ}
    {F G : Value k} (hf : RightHasIntegral k f a b F) (hg : RightHasIntegral k g a b G) :
    RightHasIntegral k (fun t => f t + g t) a b (F + G) := by
  let hrf := hf.choose
  let hrg := hg.choose
  let hr : RightRegular k (fun t => f t + g t) a b :=
    ⟨hrf.1, fun t => (scalar_add_value k (hrf.2 t) (hrg.2 t)).choose⟩
  apply (right_tendsto_iff k _ a b hr _).mpr
  have ht := ((right_tendsto_iff k f a b hrf F).mp hf).add
    ((right_tendsto_iff k g a b hrg G).mp hg)
  apply ht.congr'
  exact Eventually.of_forall fun t => (scalar_add_value k (hrf.2 t) (hrg.2 t)).choose_spec.symm

theorem left_smul (k : ScalarKind) {f : ℝ → Value k} {a : WithBot ℝ} {b : ℝ}
    {F : Value k} (hf : LeftHasIntegral k f a b F) (c : ℝ) :
    LeftHasIntegral k (fun t => c • f t) a b (c • F) := by
  let hrf := hf.choose
  let hr : LeftRegular k (fun t => c • f t) a b :=
    ⟨hrf.1, fun t => (scalar_smul_value k (hrf.2 t) c).choose⟩
  apply (left_tendsto_iff k _ a b hr _).mpr
  apply (tendsto_const_nhds.smul ((left_tendsto_iff k f a b hrf F).mp hf)).congr'
  exact Eventually.of_forall fun t => (scalar_smul_value k (hrf.2 t) c).choose_spec.symm

theorem right_smul (k : ScalarKind) {f : ℝ → Value k} {a : ℝ} {b : WithTop ℝ}
    {F : Value k} (hf : RightHasIntegral k f a b F) (c : ℝ) :
    RightHasIntegral k (fun t => c • f t) a b (c • F) := by
  let hrf := hf.choose
  let hr : RightRegular k (fun t => c • f t) a b :=
    ⟨hrf.1, fun t => (scalar_smul_value k (hrf.2 t) c).choose⟩
  apply (right_tendsto_iff k _ a b hr _).mpr
  apply (tendsto_const_nhds.smul ((right_tendsto_iff k f a b hrf F).mp hf)).congr'
  exact Eventually.of_forall fun t => (scalar_smul_value k (hrf.2 t) c).choose_spec.symm

theorem left_real_smul (k : ScalarKind) {f : ℝ → ℝ} {a : WithBot ℝ} {b F : ℝ}
    (hf : LeftHasIntegral .real f a b F) (c : Value k) :
    LeftHasIntegral k (fun t => f t • c) a b (F • c) := by
  let hrf := hf.choose
  let hr : LeftRegular k (fun t => f t • c) a b :=
    ⟨hrf.1, fun t => (real_smul_value k (hrf.2 t) c).choose⟩
  apply (left_tendsto_iff k _ a b hr _).mpr
  have ht : Tendsto (fun t => (LeftTruncation .real f a b hrf t : ℝ)) atBot (𝓝 F) :=
    (left_tendsto_iff .real f a b hrf F).mp hf
  have hc : Continuous (fun x : ℝ => x • c) := continuous_id.smul continuous_const
  apply ((hc.tendsto F).comp ht).congr' 
  exact Eventually.of_forall fun t => (real_smul_value k (hrf.2 t) c).choose_spec.symm

theorem right_real_smul (k : ScalarKind) {f : ℝ → ℝ} {a F : ℝ} {b : WithTop ℝ}
    (hf : RightHasIntegral .real f a b F) (c : Value k) :
    RightHasIntegral k (fun t => f t • c) a b (F • c) := by
  let hrf := hf.choose
  let hr : RightRegular k (fun t => f t • c) a b :=
    ⟨hrf.1, fun t => (real_smul_value k (hrf.2 t) c).choose⟩
  apply (right_tendsto_iff k _ a b hr _).mpr
  have ht : Tendsto (fun t => (RightTruncation .real f a b hrf t : ℝ)) atTop (𝓝 F) :=
    (right_tendsto_iff .real f a b hrf F).mp hf
  have hc : Continuous (fun x : ℝ => x • c) := continuous_id.smul continuous_const
  apply ((hc.tendsto F).comp ht).congr' 
  exact Eventually.of_forall fun t => (real_smul_value k (hrf.2 t) c).choose_spec.symm

/-- A fixed positive split used only to combine independent endpoint limits. -/
def unitSplit : RegularPoint (0 : WithBot ℝ) ⊤ :=
  ⟨1, WithBot.coe_lt_coe.mpr zero_lt_one, WithTop.coe_lt_top _⟩

theorem has_add (k : ScalarKind) {f g : ℝ → Value k} {F G : Value k}
    (hf : HasIntegral k f (0 : WithBot ℝ) ⊤ F)
    (hg : HasIntegral k g (0 : WithBot ℝ) ⊤ G) :
    HasIntegral k (fun t => f t + g t) (0 : WithBot ℝ) ⊤ (F + G) := by
  obtain ⟨hlf, lf, rf, hlf', hrf', rfl⟩ :=
    (hasIntegral_at_every_split k f (0 : WithBot ℝ) ⊤ unitSplit F).mp hf
  obtain ⟨hlg, lg, rg, hlg', hrg', rfl⟩ :=
    (hasIntegral_at_every_split k g (0 : WithBot ℝ) ⊤ unitSplit G).mp hg
  exact ⟨(fun u v hu huv hv => (scalar_add_value k (hlf u v hu huv hv)
    (hlg u v hu huv hv)).choose), unitSplit, lf + lg, rf + rg,
    left_add k hlf' hlg', right_add k hrf' hrg', by abel⟩

theorem has_smul (k : ScalarKind) {f : ℝ → Value k} {F : Value k}
    (hf : HasIntegral k f (0 : WithBot ℝ) ⊤ F) (c : ℝ) :
    HasIntegral k (fun t => c • f t) (0 : WithBot ℝ) ⊤ (c • F) := by
  obtain ⟨hlf, split, lf, rf, hlf', hrf', rfl⟩ := hf
  exact ⟨(fun u v hu huv hv => (scalar_smul_value k (hlf u v hu huv hv) c).choose),
    split, c • lf, c • rf, left_smul k hlf' c, right_smul k hrf' c, smul_add ..⟩

theorem has_sub (k : ScalarKind) {f g : ℝ → Value k} {F G : Value k}
    (hf : HasIntegral k f (0 : WithBot ℝ) ⊤ F)
    (hg : HasIntegral k g (0 : WithBot ℝ) ⊤ G) :
    HasIntegral k (fun t => f t - g t) (0 : WithBot ℝ) ⊤ (F - G) := by
  simpa only [neg_one_smul, ← sub_eq_add_neg] using has_add k hf (has_smul k hg (-1))

theorem has_real_smul (k : ScalarKind) {f : ℝ → ℝ} {F : ℝ}
    (hf : HasIntegral .real f (0 : WithBot ℝ) ⊤ F) (c : Value k) :
    HasIntegral k (fun t => f t • c) (0 : WithBot ℝ) ⊤ (F • c) := by
  obtain ⟨hlf, split, lf, rf, hlf', hrf', rfl⟩ := hf
  exact ⟨(fun u v hu huv hv => (real_smul_value k (hlf u v hu huv hv) c).choose),
    split, (show ℝ from lf) • c, (show ℝ from rf) • c, left_real_smul k hlf' c, right_real_smul k hrf' c, add_smul ..⟩

/-- The real Gamma moment, before multiplication by a scalar coefficient. -/
def moment (β lam : ℝ) (t : ℝ) : ℝ := Real.exp (-lam * t) * t ^ (β - 1)

theorem moment_continuous (β lam t : ℝ) (ht : 0 < t) :
    ContinuousAt (moment β lam) t :=
  (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id)).mul
    (Real.continuousAt_rpow_const t (β - 1) (Or.inl ht.ne'))

theorem moment_integrable (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    IntegrableOn (moment β lam) (Ioi 0) := by
  have hi : IntegrableOn (fun t => gammaKernel β (lam * t)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (gammaKernel β) 0 hlam).mpr
      (by simpa using gammaKernel_integrable hβ)
  have he (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      (lam ^ (β - 1))⁻¹ * gammaKernel β (lam * t) = moment β lam t := by
    dsimp [gammaKernel, GSpec.gammaKernelValue, moment]
    rw [Real.mul_rpow hlam.le ht.le]
    have hn : lam ^ (β - 1) ≠ 0 := (Real.rpow_pos_of_pos hlam _).ne'
    field_simp
  exact IntegrableOn.congr_fun (hi.const_mul ((lam ^ (β - 1))⁻¹)) he measurableSet_Ioi

theorem moment_value (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    (∫ t in Ioi (0 : ℝ), moment β lam t) = Real.Gamma β / lam ^ β := by
  have he := Real.integral_rpow_mul_exp_neg_mul_Ioi hβ hlam
  have hf : (fun t : ℝ => t ^ (β - 1) * Real.exp (-(lam * t))) = moment β lam := by
    funext t
    simp only [moment, mul_neg, mul_comm]
  rw [hf] at he
  rw [he, one_div, Real.inv_rpow hlam.le, div_eq_mul_inv, mul_comm]

theorem moment_hasIntegral (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    HasIntegral .real (moment β lam) (0 : WithBot ℝ) ⊤ (Real.Gamma β / lam ^ β) := by
  let hi := moment_integrable β lam hβ hlam
  obtain ⟨hl, hr⟩ := positive_integrable_independent (moment_continuous β lam) hi
  refine ⟨WatsonTail.continuous_local .real _ (moment_continuous β lam), unitSplit,
    _, _, hl, hr, ?_⟩
  change Real.Gamma β / lam ^ β = (∫ t in (0 : ℝ)..1, moment β lam t) +
    ∫ t in Ioi (1 : ℝ), moment β lam t
  rw [intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi zero_le_one)), moment_value β lam hβ hlam]

theorem monomial_hasIntegral (k : ScalarKind) (a : Value k) (β lam : ℝ)
    (hβ : 0 < β) (hlam : 0 < lam) :
    HasIntegral k (damped k (monomial k a β) lam) (0 : WithBot ℝ) ⊤
      ((Real.Gamma β / lam ^ β) • a) := by
  change HasIntegral k (fun t => Real.exp (-lam * t) • (t ^ (β - 1)) • a)
    (0 : WithBot ℝ) ⊤ ((Real.Gamma β / lam ^ β) • a)
  simpa only [moment, mul_smul] using
    has_real_smul k (moment_hasIntegral β lam hβ hlam) a

/-- Every positive proper truncation of a Gamma moment is bounded by its
full integral, after establishing integrability of that full moment. -/
theorem moment_truncation_le (β lam u v : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (hu : 0 < u) (huv : u ≤ v) (h : RealIntegrable (moment β lam) u v) :
    realIntegral _ h ≤ Real.Gamma β / lam ^ β := by
  have hd := (positive_continuous_darboux (moment_continuous β lam) hu huv).choose_spec
  rw [hd, intervalIntegral.integral_of_le huv, ← moment_value β lam hβ hlam]
  apply setIntegral_mono_set (moment_integrable β lam hβ hlam)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
  · exact Filter.Eventually.of_forall (fun t ht => hu.trans ht.1)

theorem scalar_zero_value (k : ScalarKind) {u v : ℝ} (huv : u ≤ v) :
    ∃ h : D.scalarIntegrableValue k (fun _ => 0) u v, D.scalarIntegralValue k _ h = 0 := by
  cases k with
  | real => exact real_zero_value huv
  | complex => exact complex_zero_value huv

theorem has_zero (k : ScalarKind) :
    HasIntegral k (fun _ => 0) (0 : WithBot ℝ) ⊤ 0 := by
  let hl : LeftRegular k (fun _ => 0) (0 : WithBot ℝ) 1 :=
    ⟨unitSplit.property.1, fun t => (scalar_zero_value k t.property.2.le).choose⟩
  let hr : RightRegular k (fun _ => 0) 1 ⊤ :=
    ⟨unitSplit.property.2, fun t => (scalar_zero_value k t.property.1.le).choose⟩
  refine ⟨(fun u v _ huv _ => (scalar_zero_value k huv).choose), unitSplit, 0, 0, ?_, ?_, by simp⟩
  · apply (left_tendsto_iff k _ _ _ hl _).mpr
    convert (tendsto_const_nhds : Tendsto (fun _ : LeftIndex (0 : WithBot ℝ) 1 => (0 : Value k)) atBot (𝓝 0)) using 1
    funext t
    exact (scalar_zero_value k t.property.2.le).choose_spec
  · apply (right_tendsto_iff k _ _ _ hr _).mpr
    convert (tendsto_const_nhds : Tendsto (fun _ : RightIndex 1 ⊤ => (0 : Value k)) atTop (𝓝 0)) using 1
    funext t
    exact (scalar_zero_value k t.property.1.le).choose_spec

theorem has_sum (k : ScalarKind) {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → Value k) (F : ι → Value k)
    (hf : ∀ i ∈ s, HasIntegral k (f i) (0 : WithBot ℝ) ⊤ (F i)) :
    HasIntegral k (fun t => ∑ i ∈ s, f i t) (0 : WithBot ℝ) ⊤ (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using has_zero k
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using has_add k (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

def polynomial (k : ScalarKind) (N : ℕ) (α : ℝ) (a : Fin N → Value k) (t : ℝ) : Value k :=
  ∑ j : Fin N, (t ^ (α + (j : ℕ) - 1)) • a j

theorem polynomial_hasIntegral (k : ScalarKind) (N : ℕ) (α : ℝ) (a : Fin N → Value k)
    (lam : ℝ) (hα : 0 < α) (hlam : 0 < lam) :
    HasIntegral k (damped k (polynomial k N α a) lam) (0 : WithBot ℝ) ⊤
      (∑ j : Fin N, (Real.Gamma (α + (j : ℕ)) / lam ^ (α + (j : ℕ))) • a j) := by
  change HasIntegral k (fun t => Real.exp (-lam * t) • ∑ j : Fin N,
    (t ^ (α + (j : ℕ) - 1)) • a j) (0 : WithBot ℝ) ⊤ _
  simpa only [damped, Finset.smul_sum, monomial] using
    has_sum k Finset.univ (fun j => damped k (monomial k (a j) (α + (j : ℕ))) lam)
      (fun j => (Real.Gamma (α + (j : ℕ)) / lam ^ (α + (j : ℕ))) • a j)
      (fun j _ => monomial_hasIntegral k (a j) _ lam (by positivity) hlam)

theorem polynomial_local (k : ScalarKind) (N : ℕ) (α : ℝ) (a : Fin N → Value k) :
    LocallyIntegrable k (polynomial k N α a) (0 : WithBot ℝ) ⊤ := by
  apply WatsonTail.continuous_local
  intro t ht
  change Tendsto (fun y => ∑ j : Fin N, (y ^ (α + (j : ℕ) - 1)) • a j)
    (𝓝 t) (𝓝 (∑ j : Fin N, (t ^ (α + (j : ℕ) - 1)) • a j))
  apply tendsto_finsetSum
  intro j _
  exact (Real.continuousAt_rpow_const t _ (Or.inl ht.ne')).smul continuousAt_const

/-- Fixed powers have at most exponential growth; the bound is simultaneous
for the finitely many retained powers. -/
theorem polynomial_growth (k : ScalarKind) (N : ℕ) (α : ℝ) (a : Fin N → Value k) :
    exponentialGrowth k (polynomial k N α a) := by
  have hp : ∀ᶠ t : ℝ in atTop, ∀ j : Fin N,
      ‖t ^ (α + (j : ℕ) - 1)‖ ≤ Real.exp t := by
    apply Filter.eventually_all.mpr
    intro j
    simpa only [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le] using
      (isLittleO_rpow_exp_atTop (α + (j : ℕ) - 1)).def zero_lt_one
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hp
  refine ⟨∑ j, ‖a j‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), 1, A, fun t ht => ?_⟩
  calc
    ‖polynomial k N α a t‖ ≤ ∑ j : Fin N, ‖(t ^ (α + (j : ℕ) - 1)) • a j‖ := norm_sum_le _ _
    _ ≤ ∑ j, Real.exp t * ‖a j‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hA t ht j) (norm_nonneg _)
    _ = (∑ j, ‖a j‖) * Real.exp (1 * t) := by rw [one_mul, Finset.sum_mul]; simp_rw [mul_comm]

theorem growth_sub (k : ScalarKind) {q p : ℝ → Value k}
    (hq : exponentialGrowth k q) (hp : exponentialGrowth k p) :
    exponentialGrowth k (fun t => q t - p t) := by
  obtain ⟨C, hC, c, A, hq⟩ := hq
  obtain ⟨D, hD, d, B, hp⟩ := hp
  refine ⟨C + D, add_nonneg hC hD, max c d, max 0 (max A B), fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have htA : A ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htB : B ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  calc
    ‖q t - p t‖ ≤ ‖q t‖ + ‖p t‖ := norm_sub_le _ _
    _ ≤ C * Real.exp (c * t) + D * Real.exp (d * t) := add_le_add (hq t htA) (hp t htB)
    _ ≤ C * Real.exp (max c d * t) + D * Real.exp (max c d * t) :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) ht0)) hC)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) ht0)) hD)
    _ = _ := by ring

/-- A bound on all proper left truncations passes to the independent limit. -/
theorem left_bound (k : ScalarKind) {f : ℝ → Value k} {a : WithBot ℝ} {b : ℝ}
    {F : Value k} (hf : LeftHasIntegral k f a b F) (K : ℝ)
    (hb : ∀ (h : LeftRegular k f a b) (t : LeftIndex a b),
      ‖LeftTruncation k f a b h t‖ ≤ K) : ‖F‖ ≤ K := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨hr, hlim⟩ := hf
  obtain ⟨r, hr'⟩ := hlim ε hε
  obtain ⟨t, htr, _⟩ := left_earlier r r
  have ht := hr' t htr
  have hn := norm_sub_norm_le F (LeftTruncation k f a b hr t)
  rw [norm_sub_rev] at hn
  rw [dist_eq_norm] at ht
  linarith [hb hr t]

/-- The local remainder is bounded using the full positive Gamma moment,
without any continuity assumption on the remainder. -/
theorem left_remainder_bound (k : ScalarKind) (r : ℝ → Value k)
    (s lam D δ : ℝ) (hs : 0 < s) (hlam : 0 < lam) (hD : 0 ≤ D)
    (hlocal : ∀ t : ℝ, 0 < t → t ≤ δ → ‖r t‖ ≤ D * t ^ (s - 1))
    (R : Value k) (hR : LeftHasIntegral k (damped k r lam) (0 : WithBot ℝ) δ R) :
    ‖R‖ ≤ D * (Real.Gamma s / lam ^ s) := by
  apply left_bound k hR
  intro hr t
  obtain ⟨hn, hnorm⟩ := scalar_integral_norm_le k _ (hr.2 t)
  have ht0 : 0 < t.val := WithBot.coe_lt_coe.mp t.property.1
  obtain ⟨hm, _⟩ := positive_continuous_darboux (moment_continuous s lam) ht0 t.property.2.le
  have hc := (realIntegral_scaled_comparison hn hm (C := D) (fun x hx => by
    refine ⟨norm_nonneg _, ?_⟩
    rw [WatsonTail.norm_damped]
    calc
      Real.exp (-lam * x) * ‖r x‖ ≤ Real.exp (-lam * x) * (D * x ^ (s - 1)) :=
        mul_le_mul_of_nonneg_left (hlocal x (ht0.trans_le hx.1) hx.2) (Real.exp_pos _).le
      _ = D * moment s lam x := by dsimp [moment]; ring)).2
  exact hnorm.trans (hc.trans (mul_le_mul_of_nonneg_left
    (moment_truncation_le s lam t.val δ hs hlam ht0 t.property.2.le hm) hD))

/-- Finite-order Laplace error estimate for a locally power-bounded remainder.
The full integral is an independent-endpoint value, supplied separately. -/
theorem remainder_estimate (k : ScalarKind) (r : ℝ → Value k)
    (hq : LocallyIntegrable k r (0 : WithBot ℝ) ⊤)
    (hg : exponentialGrowth k r) (s D δ : ℝ) (hs : 0 < s) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hlocal : ∀ t : ℝ, 0 < t → t ≤ δ → ‖r t‖ ≤ D * t ^ (s - 1)) :
    ∃ L : ℝ, 0 < L ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ lam : ℝ, L ≤ lam →
      ∀ R : Value k, HasIntegral k (damped k r lam) (0 : WithBot ℝ) ⊤ R →
        ‖R‖ ≤ B * lam ^ (-s) := by
  obtain ⟨B, hB, L, hL, htail⟩ := WatsonTail.tail_control k r hq hg δ hδ
  have he : ∀ᶠ lam : ℝ in atTop,
      Real.exp (-lam * δ / 2) ≤ lam ^ (-s) := by
    have he := (isLittleO_exp_neg_mul_rpow_atTop (show 0 < δ / 2 by positivity) (-s)).def zero_lt_one
    filter_upwards [he, eventually_ge_atTop (0 : ℝ)] with lam he hlam
    have hexp : -(δ / 2) * lam = -lam * δ / 2 := by ring
    simpa only [hexp, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.rpow_nonneg hlam _)] using he
  obtain ⟨A, hA⟩ := eventually_atTop.mp he
  refine ⟨max L A, hL.trans_le (le_max_left _ _), D * Real.Gamma s + B,
    add_nonneg (mul_nonneg hD (Real.Gamma_pos_of_pos hs).le) hB, fun lam hlam R hR => ?_⟩
  have hlamL : L ≤ lam := (le_max_left _ _).trans hlam
  have hlam0 : 0 < lam := hL.trans_le hlamL
  let c : RegularPoint (0 : WithBot ℝ) ⊤ :=
    ⟨δ, WithBot.coe_lt_coe.mpr hδ, WithTop.coe_lt_top _⟩
  obtain ⟨_, l, u, hl, hu, rfl⟩ := (hasIntegral_at_every_split k _ _ _ c R).mp hR
  obtain ⟨T, V, hT, _, hTV, hVB⟩ := htail lam hlamL
  have heq := right_unique k _ δ ⊤ u T hu hT
  have hut : ‖u‖ ≤ B * lam ^ (-s) := by
    rw [heq]
    exact hTV.trans (hVB.trans (mul_le_mul_of_nonneg_left
      (hA lam ((le_max_right _ _).trans hlam)) hB))
  have hlt := left_remainder_bound k r s lam D δ hs hlam0 hD hlocal l hl
  calc
    ‖l + u‖ ≤ ‖l‖ + ‖u‖ := norm_add_le _ _
    _ ≤ D * (Real.Gamma s / lam ^ s) + B * lam ^ (-s) := add_le_add hlt hut
    _ = (D * Real.Gamma s + B) * lam ^ (-s) := by
      rw [Real.rpow_neg hlam0.le]
      ring

theorem expansion : Specs.SingleVariableAnalysis.Ch17.Watson.expansion := by
  intro k N α a q hN hα hq hexp hg
  obtain ⟨L0, hL0, hconv⟩ := WatsonTail.absolute_convergence k N α a q hN hα hq hexp hg
  let p := polynomial k N α a
  let r : ℝ → Value k := fun t => q t - p t
  have hp : LocallyIntegrable k p (0 : WithBot ℝ) ⊤ := polynomial_local k N α a
  have hr : LocallyIntegrable k r (0 : WithBot ℝ) ⊤ := by
    intro u v hu huv hv
    simpa only [r, neg_one_smul, ← sub_eq_add_neg] using
      (scalar_add_value k (hq u v hu huv hv)
        (scalar_smul_value k (hp u v hu huv hv) (-1)).choose).choose
  have hrg : exponentialGrowth k r := growth_sub k hg (polynomial_growth k N α a)
  obtain ⟨D, hD, δ, hδ, hlocal⟩ := hexp
  obtain ⟨L1, hL1, B, hB, hbound⟩ := remainder_estimate k r hr hrg
    (α + (N : ℝ)) D δ (by positivity) hD hδ hlocal
  refine ⟨max L0 L1, hL0.trans_le (le_max_left _ _), B, hB, fun lam hlam => ?_⟩
  obtain ⟨habs, I, hI⟩ := hconv lam ((le_max_left _ _).trans hlam)
  have hlam0 : 0 < lam := hL0.trans_le ((le_max_left _ _).trans hlam)
  have hP := polynomial_hasIntegral k N α a lam hα hlam0
  have hR : HasIntegral k (damped k r lam) (0 : WithBot ℝ) ⊤
      (I - ∑ j : Fin N, (Real.Gamma (α + (j : ℕ)) / lam ^ (α + (j : ℕ))) • a j) := by
    change HasIntegral k (fun t => Real.exp (-lam * t) • (q t - polynomial k N α a t))
      (0 : WithBot ℝ) ⊤ _
    simpa only [damped, smul_sub] using has_sub k hI hP
  refine ⟨I, habs, hI, ?_⟩
  change ‖I - ∑ j : Fin N,
    (gammaIntegral (α + (j : ℕ)) (by positivity) / lam ^ (α + (j : ℕ))) • a j‖ ≤ _
  have hgamma : ∀ (s : ℝ) (hs : 0 < s), gammaIntegral s hs = Real.Gamma s := gamma_eq_realGamma
  simp_rw [hgamma]
  convert hbound lam ((le_max_right _ _).trans hlam) _ hR using 1
  congr 2
  ring

end SingleVariableAnalysis.Watson
