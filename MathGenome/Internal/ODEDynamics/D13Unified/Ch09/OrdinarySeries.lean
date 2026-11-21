import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.OrdinarySeries
import MathGenome.Internal.ODEDynamics.D13Unified.Ch09.HolomorphicDiscLinearIVP
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace D13Unified.Ch09.OrdinarySeries
open HolomorphicDiscLinearIVP Set Metric Filter
open scoped ENNReal BigOperators Topology Matrix.Norms.Elementwise

lemma zero_mem_disc {R : ℝ≥0∞} (hR : 0 < R) : (0 : ℂ) ∈ disc R := by
  simpa [disc] using hR

lemma disc_isOpen (R : ℝ≥0∞) : IsOpen (disc R) := isOpen_eball

lemma hasSeries_taylor {R : ℝ≥0∞} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (disc R)) : HasSeriesOnDisc R f (taylorCoeff f) := by
  intro z hz
  convert Complex.hasSum_taylorSeries_on_eball hf hz using 1
  funext n
  simp [taylorCoeff, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma series_coeff_unique {R : ℝ≥0∞} (hR : 0 < R) {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : DifferentiableOn ℂ f (disc R)) (ha : HasSeriesOnDisc R f a) :
    a = taylorCoeff f := by
  have h : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [eball_mem_nhds (0 : ℂ) hR] with z hz
    simpa [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using ha z hz
  have ht := (hf.analyticAt ((disc_isOpen R).mem_nhds (zero_mem_disc hR))).hasFPowerSeriesAt
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (h.eq_formalMultilinearSeries ht)

noncomputable def companion (p q : ℂ → ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; -q z, -p z]

@[simp] lemma companion_mulVec (p q : ℂ → ℂ) (z : ℂ) (v : Fin 2 → ℂ) :
    (companion p q z).mulVec v = ![v 1, -q z * v 0 - p z * v 1] := by
  ext i
  fin_cases i <;> simp [companion, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

lemma companion_differentiable {R : ℝ≥0∞} {p q : ℂ → ℂ}
    (hp : DifferentiableOn ℂ p (disc R)) (hq : DifferentiableOn ℂ q (disc R)) :
    DifferentiableOn ℂ (companion p q) (disc R) := by
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact differentiableOn_const _
  · exact differentiableOn_const _
  · exact hq.neg
  · exact hp.neg

lemma solution_lift {R : ℝ≥0∞} {p q v : ℂ → ℂ} {a₀ a₁ : ℂ}
    (hv : IsOrdinarySolution R p q a₀ a₁ v) :
    (fun z => ![v z, deriv v z]) 0 = ![a₀, a₁] ∧
    ∀ z ∈ disc R, HasDerivAt (fun z => ![v z, deriv v z])
      ((companion p q z).mulVec ![v z, deriv v z]) z := by
  refine ⟨by simp [hv.2.2.1, hv.2.2.2.1], ?_⟩
  intro z hz
  rw [companion_mulVec]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (hv.1.differentiableAt (disc_isOpen R |>.mem_nhds hz)).hasDerivAt
  · have h := (hv.2.1.differentiableAt (disc_isOpen R |>.mem_nhds hz)).hasDerivAt
    convert h using 1 <;> dsimp
    linear_combination -hv.2.2.2.2 z hz

theorem ordinary_ivp : Specs.D13Unified.Ch09.OrdinarySeries.ordinary_ivp_type := by
  intro R hR p q hp hq a₀ a₁
  obtain ⟨Y, hY, hu⟩ := holomorphic_disc_matrix_ivp 2 R hR (companion p q)
    (companion_differentiable hp hq) ![a₀, a₁]
  let y : ℂ → ℂ := fun z => Y z 0
  have hd (z : ℂ) (hz : z ∈ disc R) : HasDerivAt y (Y z 1) z := by
    simpa [y] using (hasDerivAt_pi.mp (hY.2.2 z hz) 0)
  have he : EqOn (deriv y) (fun z => Y z 1) (disc R) := fun z hz => (hd z hz).deriv
  have hd' (z : ℂ) (hz : z ∈ disc R) :
      HasDerivAt (deriv y) (-q z * y z - p z * deriv y z) z := by
    have h := hasDerivAt_pi.mp (hY.2.2 z hz) 1
    simp only [companion_mulVec, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
    have hez : deriv y z = Y z 1 := he hz
    rw [← hez] at h
    exact h.congr_of_eventuallyEq (he.eventuallyEq_of_mem (disc_isOpen R |>.mem_nhds hz))
  have hy : IsOrdinarySolution R p q a₀ a₁ y := by
    refine ⟨fun z hz => (hd z hz).differentiableAt.differentiableWithinAt,
      fun z hz => (hd' z hz).differentiableAt.differentiableWithinAt, ?_, ?_, ?_⟩
    · exact congrFun hY.1 0
    · rw [he (zero_mem_disc hR)]
      exact congrFun hY.1 1
    · intro z hz
      rw [(hd' z hz).deriv]
      ring
  refine ⟨y, hy, ?_⟩
  intro v hv z hz
  have h := solution_lift hv
  exact congrFun (hu _ h.1 h.2 hz) 0

@[simp] lemma taylorCoeff_zero (f : ℂ → ℂ) : taylorCoeff f 0 = f 0 := by
  simp [taylorCoeff]

@[simp] lemma taylorCoeff_one (f : ℂ → ℂ) : taylorCoeff f 1 = deriv f 0 := by
  simp [taylorCoeff, iteratedDeriv_succ']

lemma taylorCoeff_deriv (f : ℂ → ℂ) (n : ℕ) :
    taylorCoeff (deriv f) n = ((n : ℂ) + 1) * taylorCoeff f (n+1) := by
  simp only [taylorCoeff, iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

lemma taylorCoeff_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    taylorCoeff (f + g) n = taylorCoeff f n + taylorCoeff g n := by
  simp only [taylorCoeff, iteratedDeriv_add hf.contDiffAt hg.contDiffAt, add_div]

lemma taylorCoeff_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    taylorCoeff (f * g) n =
      ∑ k ∈ Finset.range (n+1), taylorCoeff f k * taylorCoeff g (n-k) := by
  simp only [taylorCoeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have he : (n.choose k : ℂ) * (k.factorial : ℂ) * ((n-k).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hk' : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk : ((n-k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-k)
  field_simp
  linear_combination he * iteratedDeriv k f 0 * iteratedDeriv (n-k) g 0

lemma taylorCoeff_congr {f g : ℂ → ℂ} (he : f =ᶠ[𝓝 0] g) (n : ℕ) :
    taylorCoeff f n = taylorCoeff g n := by
  unfold taylorCoeff
  rw [he.iteratedDeriv_eq n]

lemma recurrence_of_solution {R : ℝ≥0∞} (hR : 0 < R) {p q y : ℂ → ℂ}
    (hp : DifferentiableOn ℂ p (disc R)) (hq : DifferentiableOn ℂ q (disc R))
    {a₀ a₁ : ℂ} (hy : IsOrdinarySolution R p q a₀ a₁ y) :
    OrdinaryRecurrence (taylorCoeff p) (taylorCoeff q) (taylorCoeff y) := by
  have hp₀ : AnalyticAt ℂ p 0 := hp.analyticAt ((disc_isOpen R).mem_nhds (zero_mem_disc hR))
  have hq₀ : AnalyticAt ℂ q 0 := hq.analyticAt ((disc_isOpen R).mem_nhds (zero_mem_disc hR))
  have hy₀ : AnalyticAt ℂ y 0 := hy.1.analyticAt ((disc_isOpen R).mem_nhds (zero_mem_disc hR))
  have hd₀ : AnalyticAt ℂ (deriv y) 0 := hy₀.deriv
  have he : deriv (deriv y) + p * deriv y + q * y =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [(disc_isOpen R).mem_nhds (zero_mem_disc hR)] with z hz
    exact hy.2.2.2.2 z hz
  intro n
  have ht : taylorCoeff (fun _ : ℂ => (0 : ℂ)) n = 0 := by simp [taylorCoeff]
  -- Use the normalized Leibniz formulas before simplifying coefficients.
  have h' := taylorCoeff_congr he n
  rw [taylorCoeff_add (hd₀.deriv.add (hp₀.mul hd₀)) (hq₀.mul hy₀),
    taylorCoeff_add hd₀.deriv (hp₀.mul hd₀),
    taylorCoeff_mul hp₀ hd₀, taylorCoeff_mul hq₀ hy₀, ht,
    taylorCoeff_deriv, taylorCoeff_deriv] at h'
  simp_rw [taylorCoeff_deriv] at h'
  have hs : (∑ k ∈ Finset.range (n+1),
      (taylorCoeff p k * ((((n-k : ℕ) : ℂ) + 1) * taylorCoeff y (n-k+1)) +
        taylorCoeff q k * taylorCoeff y (n-k))) =
      (∑ k ∈ Finset.range (n+1),
      ((((n-k : ℕ) : ℂ) + 1) * taylorCoeff p k * taylorCoeff y (n-k+1) +
        taylorCoeff q k * taylorCoeff y (n-k))) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [← hs, Finset.sum_add_distrib]
  push_cast at h'
  linear_combination h'

/-- The recurrence determines every coefficient from the prescribed first two. -/
lemma recurrence_unique {p q a b : ℕ → ℂ} (ha : OrdinaryRecurrence p q a)
    (hb : OrdinaryRecurrence p q b) (h₀ : a 0 = b 0) (h₁ : a 1 = b 1) : a = b := by
  funext m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm₀ : m = 0
    · simpa [hm₀] using h₀
    by_cases hm₁ : m = 1
    · simpa [hm₁] using h₁
    obtain ⟨n, rfl⟩ : ∃ n, m = n+2 := ⟨m-2, by omega⟩
    have hs : (∑ k ∈ Finset.range (n+1),
        ((((n-k : ℕ) : ℂ) + 1) * p k * a (n-k+1) + q k * a (n-k))) =
        (∑ k ∈ Finset.range (n+1),
        ((((n-k : ℕ) : ℂ) + 1) * p k * b (n-k+1) + q k * b (n-k))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih (n-k+1) (by omega), ih (n-k) (by omega)]
    have he := ha n
    rw [hs] at he
    have hn₂ : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
    have hn₁ : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
    exact mul_left_cancel₀ (mul_ne_zero hn₂ hn₁) (he.trans (hb n).symm)

theorem ordinary_series : Specs.D13Unified.Ch09.OrdinarySeries.ordinary_series_type := by
  intro R hR p q pₖ qₖ hp hq hps hqs a₀ a₁ y hy
  refine ⟨?_, ?_, hasSeries_taylor hy.1, ?_⟩
  · simpa only [taylorCoeff_zero] using hy.2.2.1
  · simpa only [taylorCoeff_one] using hy.2.2.2.1
  · have hpₖ := series_coeff_unique hR hp hps
    have hqₖ := series_coeff_unique hR hq hqs
    rw [hpₖ, hqₖ]
    exact recurrence_of_solution hR hp hq hy

theorem recursive_series : Specs.D13Unified.Ch09.OrdinarySeries.recursive_series_type := by
  intro R hR p q pₖ qₖ hp hq hps hqs a₀ a₁ a ha₀ ha₁ ha
  obtain ⟨y, hy, hu⟩ := ordinary_ivp R hR p q hp hq a₀ a₁
  obtain ⟨hy₀, hy₁, hs, hr⟩ := ordinary_series R hR p q pₖ qₖ hp hq hps hqs a₀ a₁ y hy
  have he : a = taylorCoeff y := recurrence_unique ha hr (ha₀.trans hy₀.symm) (ha₁.trans hy₁.symm)
  exact ⟨y, hy, he, he.symm ▸ hs, hu⟩

end D13Unified.Ch09.OrdinarySeries
