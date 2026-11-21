import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.OrderDivisorDefinitions
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.DiscreteCountableZeros
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.CanonicalFactors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Filter Set
open scoped Topology ENNReal
namespace D12Complex.OrderDivisorDefinitions

def maximumModulus : Specs.D12Complex.Ch17.OrderDivisorDefinitions.maximumModulus_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.maximumModulus_value

def growthQuotient : Specs.D12Complex.Ch17.OrderDivisorDefinitions.growthQuotient_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.growthQuotient_value

def order : Specs.D12Complex.Ch17.OrderDivisorDefinitions.order_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.order_value

def zeroLocation : Specs.D12Complex.Ch17.OrderDivisorDefinitions.zeroLocation_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.zeroLocation_value

def AdmissibleExponent : Specs.D12Complex.Ch17.OrderDivisorDefinitions.AdmissibleExponent_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.AdmissibleExponent_value

def divisorExponent : Specs.D12Complex.Ch17.OrderDivisorDefinitions.divisorExponent_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.divisorExponent_value

def RankSummable : Specs.D12Complex.Ch17.OrderDivisorDefinitions.RankSummable_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.RankSummable_value

def canonicalRank : Specs.D12Complex.Ch17.OrderDivisorDefinitions.canonicalRank_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.canonicalRank_value

def genus : Specs.D12Complex.Ch17.OrderDivisorDefinitions.genus_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.genus_value

def IsCanonicalFactorization : Specs.D12Complex.Ch17.OrderDivisorDefinitions.IsCanonicalFactorization_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.IsCanonicalFactorization_value

def factorizationGenus : Specs.D12Complex.Ch17.OrderDivisorDefinitions.factorizationGenus_type :=
  Specs.D12Complex.Ch17.OrderDivisorDefinitions.factorizationGenus_value

theorem polynomial_function_exists :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.polynomial_function_exists_type := by
  intro P hP
  have hn : ∃ z : ℂ, P.eval z ≠ 0 := by
    by_contra! h
    exact hP (Polynomial.funext (by simpa using h))
  exact ⟨⟨P.eval, ⟨isOpen_univ, fun _ _ => P.differentiableAt⟩, hn⟩, rfl⟩

theorem zeroLocation_nonzero :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.zeroLocation_nonzero_type := by
  intro f i
  exact i.1.property.1

theorem zeroLocation_is_zero :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.zeroLocation_is_zero_type := by
  intro f i
  exact i.1.property.2

theorem maximumModulus_attained :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.maximumModulus_attained_type := by
  intro f hf r hr
  have hs : (Metric.sphere (0 : ℂ) r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn hs hf.norm.continuousOn
  have heq : maximumModulus f r = ‖f z‖ := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact hs.image _
    · rintro _ ⟨w, hw, rfl⟩
      exact hmax hw
    · intro b hb
      exact ⟨‖f z‖, ⟨z, hz, rfl⟩, hb⟩
  exact ⟨z, hz, heq.symm, fun w hw => (hmax hw).trans_eq heq.symm⟩

theorem growthQuotient_nonneg :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.growthQuotient_nonneg_type := by
  intro f r hr
  apply div_nonneg _ (Real.log_nonneg hr.le)
  apply Real.log_nonneg
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (max (Real.exp 1) (maximumModulus f r)) :=
      Real.log_le_log (Real.exp_pos _) (le_max_left _ _)

/-- A coefficient bound uniform over every circle of radius at least one. -/
lemma polynomial_bound (P : Polynomial ℂ) :
    ∃ C : ℝ, Real.exp 1 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      max (Real.exp 1) (maximumModulus P.eval r) ≤ C * r ^ P.natDegree := by
  let C : ℝ := Real.exp 1 + ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖
  have hC : Real.exp 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hC0 : 0 ≤ C := (Real.exp_pos 1).le.trans hC
  refine ⟨C, hC, fun r hr => max_le ?_ ?_⟩
  · exact hC.trans (le_mul_of_one_le_right hC0 (one_le_pow₀ hr))
  · have hne : ((fun z => ‖P.eval z‖) '' Metric.sphere (0 : ℂ) r).Nonempty :=
      (NormedSpace.sphere_nonempty.mpr (zero_le_one.trans hr)).image _
    apply csSup_le hne
    rintro _ ⟨z, hz, rfl⟩
    have hz' : ‖z‖ = r := by simpa using hz
    calc
      ‖P.eval z‖ = ‖∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * z ^ i‖ := by
        rw [Polynomial.eval_eq_sum_range]
      _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i * z ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * r ^ P.natDegree := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_pow, hz']
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hr (by have := Finset.mem_range.mp hi; omega)) (norm_nonneg _)
      _ = (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * r ^ P.natDegree :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ C * r ^ P.natDegree := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hr) _)
        dsimp [C]
        exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- The elementary real-analysis estimate behind polynomial order zero. -/
lemma growthQuotient_tendsto_zero_of_bound (f : ℂ → ℂ) (C : ℝ) (n : ℕ)
    (hC : Real.exp 1 ≤ C)
    (hbound : ∀ r : ℝ, 1 ≤ r →
      max (Real.exp 1) (maximumModulus f r) ≤ C * r ^ n) :
    Tendsto (growthQuotient f) atTop (𝓝 0) := by
  have hCpos : 0 < C := (Real.exp_pos 1).trans_le hC
  have hlogC : 1 ≤ Real.log C := by
    simpa using Real.log_le_log (Real.exp_pos 1) hC
  let A : ℝ := Real.log C + n
  have hA : 0 < A := by dsimp [A]; positivity
  have hlim1 : Tendsto (fun r : ℝ => Real.log A / Real.log r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hlim2 : Tendsto (fun r : ℝ => Real.log (Real.log r) / Real.log r) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hlim : Tendsto (fun r : ℝ =>
      (Real.log A + Real.log (Real.log r)) / Real.log r) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using hlim1.add hlim2
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    exact growthQuotient_nonneg f r hr
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with r hr
    have hr1 : 1 < r := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hr
    have hlr : 1 ≤ Real.log r := by
      simpa using Real.log_le_log (Real.exp_pos 1) hr
    have hlmax : Real.log (max (Real.exp 1) (maximumModulus f r)) ≤ A * Real.log r := by
      calc
        _ ≤ Real.log (C * r ^ n) :=
          Real.log_le_log ((Real.exp_pos 1).trans_le (le_max_left _ _)) (hbound r hr1.le)
        _ = Real.log C + (n : ℝ) * Real.log r := by
          rw [Real.log_mul hCpos.ne' (pow_pos (zero_lt_one.trans hr1) n).ne', Real.log_pow]
        _ ≤ A * Real.log r := by
          dsimp [A]
          nlinarith
    change Real.log (Real.log (max (Real.exp 1) (maximumModulus f r))) / Real.log r ≤ _
    apply div_le_div_of_nonneg_right _ (by linarith)
    calc
      _ ≤ Real.log (A * Real.log r) := Real.log_le_log (by
        have := Real.log_le_log (Real.exp_pos 1)
          (le_max_left (Real.exp 1) (maximumModulus f r))
        rw [Real.log_exp] at this
        linarith) hlmax
      _ = Real.log A + Real.log (Real.log r) := Real.log_mul hA.ne' (by linarith)

theorem order_polynomial :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.order_polynomial_type := by
  intro P f _ heq
  obtain ⟨C, hC, hbound⟩ := polynomial_bound P
  have ht : Tendsto (growthQuotient f.toFun) atTop (𝓝 0) := by
    rw [heq]
    exact growthQuotient_tendsto_zero_of_bound P.eval C P.natDegree hC hbound
  simpa [order, Specs.D12Complex.Ch17.OrderDivisorDefinitions.order_value, growthQuotient]
    using (ENNReal.tendsto_ofReal ht).limsup_eq

theorem order_constant :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.order_constant_type := by
  intro c f hc heq
  exact order_polynomial (Polynomial.C c) f (by simpa using hc) (by simpa using heq)

theorem zero_multiplicity_finite :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.zero_multiplicity_finite_type := by
  intro f z htop
  have ha : AnalyticOnNhd ℂ f.toFun Set.univ := fun a _ =>
    (D12Complex.LocalZeroFactorization.holomorphicNear_iff_analyticAt f.toFun a).mp
      ⟨Set.univ, Set.mem_univ _, f.holomorphic⟩
  have hzero := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) (analyticOrderAt_eq_top.mp htop)
  obtain ⟨w, hw⟩ := f.nonzero
  exact hw (hzero (Set.mem_univ w))

theorem repeatedZero_fiber :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.repeatedZero_fiber_type := by
  classical
  intro f z hz
  by_cases hfz : f.toFun z = 0
  · refine ⟨{
      toFun := fun i => by
        obtain ⟨⟨⟨w, hw⟩, j⟩, hi⟩ := i
        change w = z at hi
        subst w
        exact j
      invFun := fun j => ⟨⟨⟨z, hz, hfz⟩, j⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }⟩
    · rintro ⟨⟨⟨w, hw⟩, j⟩, hi⟩
      change w = z at hi
      subst w
      rfl
    · intro j
      rfl
  · have horder : (analyticOrderAt f.toFun z).toNat = 0 := by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hfz)]
      rfl
    have : IsEmpty (Fin (analyticOrderAt f.toFun z).toNat) := by
      rw [horder]
      infer_instance
    have : IsEmpty {i : RepeatedZero f //
        Specs.D12Complex.Ch17.OrderDivisorDefinitions.zeroLocation_value f i = z} :=
      ⟨fun i => hfz (by
        rw [← i.property]
        exact i.val.1.property.2)⟩
    exact ⟨Equiv.equivOfIsEmpty _ _⟩

theorem divisorExponent_eq_top_of_no_exponent :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.divisorExponent_eq_top_of_no_exponent_type := by
  intro ι a ha
  change sInf _ = ⊤
  apply le_antisymm le_top
  apply le_sInf
  rintro x ⟨s, hs, _⟩
  exact (ha ⟨s, hs⟩).elim

theorem divisorExponent_finite :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.divisorExponent_finite_type := by
  intro ι hι a
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hm : ENNReal.ofReal ε ∈ {x | ∃ s : ℝ,
      Specs.D12Complex.Ch17.OrderDivisorDefinitions.AdmissibleExponent_value a s ∧
        x = ENNReal.ofReal s} := ⟨ε, ⟨hε, Summable.of_finite⟩, rfl⟩
  exact (sInf_le hm).trans (by simp)

theorem canonicalRank_eq_top_iff :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.canonicalRank_eq_top_iff_type := by
  classical
  intro ι a
  unfold Specs.D12Complex.Ch17.OrderDivisorDefinitions.canonicalRank_value
  split_ifs with h <;> simp [h]

theorem canonicalRank_eq_nat_iff :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.canonicalRank_eq_nat_iff_type := by
  classical
  intro ι a q
  unfold Specs.D12Complex.Ch17.OrderDivisorDefinitions.canonicalRank_value
  split_ifs with h
  · rw [ENat.natCast_inj, Nat.find_eq_iff]
  · simp only [ENat.top_ne_natCast, false_iff, not_and]
    exact fun hq => (h ⟨q, hq⟩).elim

theorem canonicalRank_finite :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.canonicalRank_finite_type := by
  intro ι hι a
  apply (canonicalRank_eq_nat_iff a 0).mpr
  exact ⟨Summable.of_finite, fun p hp => (Nat.not_lt_zero p hp).elim⟩

theorem genus_constant :
    Specs.D12Complex.Ch17.OrderDivisorDefinitions.genus_constant_type := by
  intro q c
  simp [Specs.D12Complex.Ch17.OrderDivisorDefinitions.genus_value]

end D12Complex.OrderDivisorDefinitions
