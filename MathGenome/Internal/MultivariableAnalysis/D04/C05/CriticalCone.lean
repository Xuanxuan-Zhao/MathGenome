import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.CriticalCone
import MathGenome.Internal.MultivariableAnalysis.D04.C05.CriticalConeNecessity
import MathGenome.Internal.MultivariableAnalysis.D04.C01.BoundedSubsequence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04
open Specs.D04.C05.ActiveConstraintCoordinates
open Specs.D04.C05.ActiveConstraints

/-- The complete necessary condition, including all critical directions. -/
theorem critical_cone_necessary :
    Specs.D04.C05.CriticalCone.critical_cone_necessaryType :=
  critical_cone_necessity

namespace CriticalCone

/-- Differentiability along convergent normalized increments. -/
theorem normalized_first_order {n : ℕ} {F : E n → ℝ} {A : E n →L[ℝ] ℝ}
    {a v : E n} {d : ℕ → E n} (hF : HasFDerivAt F A a)
    (hd : Tendsto d atTop (𝓝 0))
    (hv : Tendsto (fun k => ‖d k‖⁻¹ • d k) atTop (𝓝 v)) :
    Tendsto (fun k => (F (a + d k) - F a) / ‖d k‖) atTop (𝓝 (A v)) := by
  have hr := ((hasFDerivAt_iff_isLittleO_nhds_zero.mp hF).norm_right.comp_tendsto hd).tendsto_div_nhds_zero
  have hA := A.continuous.continuousAt.tendsto.comp hv
  have H := hr.add hA
  simp only [zero_add] at H
  convert H using 1
  funext k
  simp only [Function.comp_apply, map_smul, smul_eq_mul]
  ring

/-- The second-order polynomial with the source's normalization. -/
theorem taylorPolynomial_two {n : ℕ} (F : E n → ℝ) (a d : E n) :
    taylorPolynomial 2 F a d = F a + fderiv ℝ F a d +
      (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 F a (fun _ => d) := by
  change (∑ j ∈ Finset.range (2+1), _) = _
  rw [Finset.sum_range_succ]
  change taylorPolynomial 1 F a d + _ = _
  rw [taylorPolynomial_one]
  norm_num [Specs.D04.C03.HigherInterfaces.Model.differentialDiagonal,
    Specs.D04.C03.HigherInterfaces.Model.higherDifferential]

/-- Stationary second-order expansion along normalized increments. -/
theorem normalized_second_order {n : ℕ} {F : E n → ℝ} {a v : E n}
    {d : ℕ → E n} (hF : ContDiffAt ℝ 2 F a) (hz : fderiv ℝ F a = 0)
    (hd : Tendsto d atTop (𝓝 0))
    (hv : Tendsto (fun k => ‖d k‖⁻¹ • d k) atTop (𝓝 v)) :
    Tendsto (fun k => (F (a + d k) - F a) / ‖d k‖ ^ 2) atTop
      (𝓝 ((1 / 2 : ℝ) * iteratedFDeriv ℝ 2 F a (fun _ => v))) := by
  obtain ⟨V, hV⟩ := twice_at hF
  have hr := ((taylorPeano_succ 1 V F a hV).comp_tendsto hd).tendsto_div_nhds_zero
  let T := iteratedFDeriv ℝ 2 F a
  have hT : Tendsto (fun k => T (fun _ => ‖d k‖⁻¹ • d k)) atTop
      (𝓝 (T (fun _ => v))) := T.cont.continuousAt.tendsto.comp
        (tendsto_pi_nhds.mpr (fun _ => hv))
  have H := (hT.const_mul (1 / 2 : ℝ)).add hr
  simp only [add_zero] at H
  apply H.congr
  intro k
  have hscale := T.map_smul_univ (fun _ => ‖d k‖⁻¹) (fun _ => d k)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hscale
  rw [hscale]
  change _ = (F (a + d k) - F a) / ‖d k‖ ^ 2
  change (1 / 2 : ℝ) * (‖d k‖⁻¹ ^ 2 * T (fun _ => d k)) +
    (F (a + d k) - taylorPolynomial 2 F a (d k)) / ‖d k‖ ^ 2 = _
  rw [taylorPolynomial_two, hz, zero_apply]
  simp only [T, div_eq_mul_inv, inv_pow]
  ring

end CriticalCone

/-- Positive second variation on every nonzero critical direction gives
strict relative minimality and growth in the ambient Euclidean distance. -/
theorem critical_cone_sufficient :
    Specs.D04.C05.CriticalCone.critical_cone_sufficientType := by
  classical
  intro n q s U f g h c a lam μ hU hf hg hh ha _hli hμ hinactive hmult hpos
  have hfc := (crOn_iff_contDiffOn 2 U f hU).mp hf
  have hgc := (crOn_iff_contDiffOn 2 U g hU).mp hg
  have hhc := (crOn_iff_contDiffOn 2 U h hU).mp hh
  have hgsc (j : Fin q) : ContDiffOn ℝ 2 (fun x => g x j) U :=
    (contDiffOn_piLp 2).mp hgc j
  have hhsc (i : Fin s) : ContDiffOn ℝ 2 (fun x => h x i) U :=
    (contDiffOn_piLp 2).mp hhc i
  have hdf := (hfc.contDiffAt (hU.mem_nhds ha.1)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hdg (j : Fin q) := ((hgsc j).contDiffAt (hU.mem_nhds ha.1)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hdh (i : Fin s) := ((hhsc i).contDiffAt (hU.mem_nhds ha.1)).differentiableAt (by norm_num) |>.hasFDerivAt
  let L := lagrangian f g h lam μ
  have hL : ContDiffAt ℝ 2 L a :=
    ((hfc.sub (ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) =>
      (hgsc j).const_smul (lam j)))).sub
      (ContDiffOn.sum (fun i (_ : i ∈ Finset.univ) =>
        (hhsc i).const_smul (μ i)))).contDiffAt (hU.mem_nhds ha.1)
  have hdL : fderiv ℝ L a = 0 := by
    have H := (hdf.sub (HasFDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => (hdg j).const_mul (lam j)))).sub
      (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hdh i).const_mul (μ i)))
    change HasFDerivAt L _ a at H
    rw [H.fderiv]
    ext z
    simp only [sub_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply]
    change Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative f a z -
      (∑ j, lam j * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => g x j) a z) -
      (∑ i, μ i * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun x => h x i) a z) = 0
    rw [hmult]
    ring
  have hμa : (∑ i, μ i * h a i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : h a i = 0
    · rw [hi, mul_zero]
    · rw [hinactive i hi, zero_mul]
  have hLle (x : E n) (hx : x ∈ Feasible U g h c) : L x - L a ≤ f x - f a := by
    have hn : 0 ≤ ∑ i, μ i * h x i := Finset.sum_nonneg (fun i _ => mul_nonneg (hμ i) (hx.2.2 i))
    dsimp [L, lagrangian]
    rw [hx.2.1, ha.2.1, hμa]
    linarith
  have hgrowth : ∃ b > 0, ∃ r > 0, ∀ x ∈ Feasible U g h c,
      ‖x - a‖ < r → f a + b * ‖x - a‖ ^ 2 ≤ f x := by
    by_contra H
    push Not at H
    let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
    have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hbad (k : ℕ) := H (ε k) (hεpos k) (ε k) (hεpos k)
    choose x hx hb hbad using hbad
    have hne (k : ℕ) : x k ≠ a := by
      intro he
      have H := hbad k
      simp [he] at H
    let d₀ : ℕ → E n := fun k => x k - a
    have hd₀ne (k : ℕ) : d₀ k ≠ 0 := sub_ne_zero.mpr (hne k)
    have hd₀ : Tendsto d₀ atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      exact squeeze_zero (fun _ => norm_nonneg _) (fun k => (hb k).le) hε
    obtain ⟨σ, v, hσ, hv⟩ := bounded_subsequence (fun k => ‖d₀ k‖⁻¹ • d₀ k)
      ⟨1, fun k => le_of_eq (norm_smul_inv_norm (hd₀ne k))⟩
    let d : ℕ → E n := d₀ ∘ σ
    have hd : Tendsto d atTop (𝓝 0) := hd₀.comp hσ.tendsto_atTop
    have hv' : Tendsto (fun k => ‖d k‖⁻¹ • d k) atTop (𝓝 v) := hv
    have hu (k : ℕ) : ‖‖d₀ k‖⁻¹ • d₀ k‖ = 1 := norm_smul_inv_norm (hd₀ne k)
    have hvnorm : ‖v‖ = 1 := by
      have hn : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 ‖v‖) := by
        simpa only [Function.comp_apply, hu] using hv.norm
      exact tendsto_nhds_unique hn tendsto_const_nhds
    have hvne : v ≠ 0 := by intro he; simp [he] at hvnorm
    have hadd (k : ℕ) : a + d k = x (σ k) := by dsimp [d, d₀]; abel
    have hgs (j : Fin q) : fderiv ℝ (fun z => g z j) a v = 0 := by
      have ht := CriticalCone.normalized_first_order (hdg j) hd hv'
      have ht' : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
          (𝓝 (fderiv ℝ (fun z => g z j) a v)) := by
        convert ht using 1
        funext k
        rw [hadd, (hx (σ k)).2.1, ha.2.1, sub_self, zero_div]
      exact tendsto_nhds_unique ht' tendsto_const_nhds
    have hgv : totalDerivative g a v = 0 := by
      have hdga := (hgc.contDiffAt (hU.mem_nhds ha.1)).differentiableAt (by norm_num) |>.hasFDerivAt
      ext j
      have he := ((PiLp.hasFDerivAt_apply 2 (g a) j).comp a hdga).fderiv
      change (fderiv ℝ g a v) j = 0
      have he' : fderiv ℝ (fun z => g z j) a = _ := he
      have H := hgs j
      rw [he'] at H
      exact H
    have hhv (i : Active h a) : 0 ≤ totalDerivative (fun z => h z i.val) a v := by
      have ht := CriticalCone.normalized_first_order (hdh i.val) hd hv'
      apply ge_of_tendsto ht
      exact Eventually.of_forall (fun k => by
        rw [hadd, i.property, sub_zero]
        exact div_nonneg ((hx (σ k)).2.2 i.val) (norm_nonneg _))
    have hfv : totalDerivative f a v ≤ 0 := by
      have ht := CriticalCone.normalized_first_order hdf hd hv'
      have hbound : Tendsto (fun k => ε (σ k) * ‖d k‖) atTop (𝓝 (0 : ℝ)) := by
        simpa using (hε.comp hσ.tendsto_atTop).mul hd.norm
      apply le_of_tendsto_of_tendsto' ht hbound
      intro k
      have hn : 0 < ‖d k‖ := norm_pos_iff.mpr (hd₀ne (σ k))
      apply (div_le_iff₀ hn).mpr
      have H := hbad (σ k)
      change f (x (σ k)) < f a + ε (σ k) * ‖d k‖ ^ 2 at H
      rw [hadd]
      nlinarith
    have hfge : 0 ≤ totalDerivative f a v := by
      change 0 ≤ Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative f a v
      rw [hmult]
      have hz : (∑ j, lam j * Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative (fun z => g z j) a v) = 0 := by
        change (∑ j, lam j * fderiv ℝ (fun z => g z j) a v) = 0
        simp only [hgs, mul_zero, Finset.sum_const_zero]
      rw [hz, zero_add]
      apply Finset.sum_nonneg
      intro i _
      by_cases hi : h a i = 0
      · exact mul_nonneg (hμ i) (hhv ⟨i, hi⟩)
      · rw [hinactive i hi, zero_mul]
    have hvc : v ∈ criticalCone f g h a := ⟨hgv, hhv, le_antisymm hfv hfge⟩
    have hpositive := hpos v hvc hvne
    have ht := CriticalCone.normalized_second_order hL hdL hd hv'
    have hle : (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 L a (fun _ => v) ≤ 0 := by
      apply le_of_tendsto_of_tendsto' ht (hε.comp hσ.tendsto_atTop)
      intro k
      have hn : 0 < ‖d k‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (hd₀ne (σ k)))
      apply (div_le_iff₀ hn).mpr
      rw [hadd]
      change L (x (σ k)) - L a ≤ ε (σ k) * ‖d k‖ ^ 2
      have H := hbad (σ k)
      have HL := hLle (x (σ k)) (hx (σ k))
      change f (x (σ k)) < f a + ε (σ k) * ‖d k‖ ^ 2 at H
      linarith
    change 0 < iteratedFDeriv ℝ 2 L a (fun _ => v) at hpositive
    linarith
  obtain ⟨b, hb, r, hr, hgrowth⟩ := hgrowth
  refine ⟨⟨ha, r, hr, ?_⟩, b, hb, r, hr, hgrowth⟩
  intro x hx hxr hxa
  have H := hgrowth x hx hxr
  have hn : 0 < b * ‖x - a‖ ^ 2 :=
    mul_pos hb (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxa)))
  linarith

end D04
