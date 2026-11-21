import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Integration
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Differentiation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Integration part of K03.13.termwise (paper.tex:1387–1404).
The coefficient primitive has zero constant coefficient and successor
coefficient a n / (n+1). The accepted differentiation-radius theorem applied
to this sequence proves exact radius equality without restricting the radius.
Ordinary ordered sums are shifted explicitly, so no unconditional-sum
convention is used to stand for convergence.

For the definite integral we use the project's proper Darboux integral.
Compact uniform continuity proves integrability of continuous real functions.
Mean-value tags telescope for each partition, identifying the integral of a
primitive's derivative with its endpoint difference. Complex functions use
this argument on their two real components. The result on the ordered hull
is then given its proper orientation, including x < c and x = c.
This is a direct C¹ proof of the required integration step, with no assumed
Riemann/measure-integral bridge or unaccepted fundamental-theorem import.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped BigOperators Topology ENNReal

def realPrimitiveCoefficients (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => a n / (n+1 : ℝ)
def complexPrimitiveCoefficients (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n+1 => a n / (n+1 : ℂ)

theorem real_powerSeries_primitive_radius (a : ℕ → ℝ) :
    realPowerSeriesRadius (realPrimitiveCoefficients a) = realPowerSeriesRadius a := by
  have h := real_powerSeries_derivative_radius (realPrimitiveCoefficients a)
  have he : (fun n : ℕ => (n+1 : ℝ) * realPrimitiveCoefficients a (n+1)) = a := by
    funext n
    dsimp [realPrimitiveCoefficients]
    exact mul_div_cancel₀ _ (by positivity)
  change realPowerSeriesRadius (realPrimitiveCoefficients a) = realPowerSeriesRadius a
  rw [he] at h
  exact h.symm

theorem complex_powerSeries_primitive_radius (a : ℕ → ℂ) :
    complexPowerSeriesRadius (complexPrimitiveCoefficients a) = complexPowerSeriesRadius a := by
  have h := complex_powerSeries_derivative_radius (complexPrimitiveCoefficients a)
  have he : (fun n : ℕ => (n+1 : ℂ) * complexPrimitiveCoefficients a (n+1)) = a := by
    funext n
    dsimp [complexPrimitiveCoefficients]
    exact mul_div_cancel₀ _ (by exact_mod_cast (show (n+1 : ℝ) ≠ 0 by positivity))
  change complexPowerSeriesRadius (complexPrimitiveCoefficients a) = complexPowerSeriesRadius a
  rw [he] at h
  exact h.symm

theorem real_powerSeries_primitive_center :
    Specs.SingleVariableAnalysis.Ch13.Integration.realPrimitiveCenter := by
  intro a c ε hε
  refine ⟨0, fun N _ => ?_⟩
  simpa [Specs.SingleVariableAnalysis.Ch11.PartialSums.realPartialSumValue] using hε

theorem complex_powerSeries_primitive_center :
    Specs.SingleVariableAnalysis.Ch13.Integration.complexPrimitiveCenter := by
  intro a c ε hε
  refine ⟨0, fun N _ => ?_⟩
  simpa [Specs.SingleVariableAnalysis.Ch11.PartialSums.complexPartialSumValue] using hε


namespace PowerSeriesIntegration
open Riemann

/-- Continuous functions on the compact interval have small Darboux gaps.
This is a local bridge to the project's proper integral, not a measure integral. -/
theorem continuous_real_integrable {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) : RealIntegrable f a b := by
  have hb : BoundedOnInterval f a b :=
    ⟨isCompact_Icc.bddBelow_image hc, isCompact_Icc.bddAbove_image hc⟩
  rcases lt_or_eq_of_le hab with hab | rfl
  · apply (darboux_criterion f hab hb).mpr
    intro ε hε
    let e := ε / (2 * (b-a))
    have he : 0 < e := by dsimp [e]; positivity
    obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hc) e he
    obtain ⟨P, hP⟩ := exists_fine_partition hab.le δ hδ
    have ho (i : Fin P.n) :
        cellSupremum f P hb i - cellInfimum f P hb i ≤ e := by
      apply cell_oscillation_le_of_sub_le
      intro x hx y hy
      apply (le_abs_self _).trans
      apply le_of_lt
      apply hu x (cell_subset_interval P i hx) y (cell_subset_interval P i hy)
      rw [Real.dist_eq]
      have hl : cellLength P i < δ := (cellLength_le_mesh P i).trans_lt hP
      change x ∈ Icc _ _ at hx
      change y ∈ Icc _ _ at hy
      exact (abs_le.mpr ⟨by dsimp [cellLength, Specs.SingleVariableAnalysis.Ch08.Partitions.lengthValue]; linarith [hx.1, hy.2], by dsimp [cellLength, Specs.SingleVariableAnalysis.Ch08.Partitions.lengthValue]; linarith [hx.2, hy.1]⟩).trans_lt hl
    refine ⟨P, ?_⟩
    calc
      upperSum f P hb - lowerSum f P hb =
          ∑ i : Fin P.n, (cellSupremum f P hb i - cellInfimum f P hb i) * cellLength P i := by
        simp only [sub_mul, Finset.sum_sub_distrib]; rfl
      _ ≤ ∑ i : Fin P.n, e * cellLength P i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ho i) (cell_positive P i).le
      _ = ε / 2 := by
        rw [← Finset.mul_sum, sum_cellLength]
        dsimp [e]
        field_simp [ne_of_gt (sub_pos.mpr hab)]
      _ < ε := half_lt_self hε
  · exact realIntegrable_degenerate f a

/-- Mean-value tags telescope to the endpoint difference; the all-tagged
limit identifies that difference with the proper Darboux integral. -/
theorem real_integral_of_primitive {f F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hd : ∀ y ∈ Ioo a b, HasDerivAt F (f y) y) :
    ∃ hi : RealIntegrable f a b, realIntegral f hi = F b - F a := by
  have hi := continuous_real_integrable hab hf
  refine ⟨hi, ?_⟩
  rcases lt_or_eq_of_le hab with hab | rfl
  · apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨δ, hδ, hlim⟩ := tagged_forward f hab hi.bounded hi (realIntegral f hi) rfl ε hε
    obtain ⟨P, hP⟩ := exists_fine_partition hab.le δ hδ
    have ht (i : Fin P.n) : ∃ z ∈ Ioo (P.point i.castSucc) (P.point i.succ),
        f z = (F (P.point i.succ) - F (P.point i.castSucc)) / cellLength P i := by
      apply exists_hasDerivAt_eq_slope F f (P.strictMono (Fin.castSucc_lt_succ (i := i)))
      · exact hF.mono (cell_subset_interval P i)
      · intro z hz
        apply hd z
        have hz' := cell_subset_interval P i ⟨hz.1.le, hz.2.le⟩
        have hl := P.strictMono.monotone (Fin.zero_le i.castSucc)
        have hr := P.strictMono.monotone (Fin.le_last i.succ)
        rw [P.first] at hl
        rw [P.last] at hr
        exact ⟨hl.trans_lt hz.1, hz.2.trans_le hr⟩
    choose z hz heq using ht
    let ξ : Tagging P := fun i => ⟨z i, (hz i).1.le, (hz i).2.le⟩
    have hs : taggedSum P ξ f = F b - F a := by
      change (∑ i : Fin P.n, cellLength P i • f (z i)) = _
      simp_rw [smul_eq_mul, heq, mul_div_cancel₀ _ (ne_of_gt (cell_positive P _))]
      have hh := sum_cell_differences (fun i => F (P.point i))
      simpa only [P.first, P.last] using hh
    have hh := hlim P ξ hP
    change |taggedSum P ξ f - realIntegral f hi| < ε at hh
    rw [hs] at hh
    simpa only [Real.dist_eq, abs_sub_comm] using hh.le
  · simp [realIntegral_degenerate]

/-- Complex values are integrated componentwise; the two real mean-value
arguments may choose different tags. -/
theorem complex_integral_of_primitive {f F : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hd : ∀ y ∈ Ioo a b, HasDerivAt F (f y) y) :
    ∃ hi : ComplexIntegrable f a b, complexIntegral f hi = F b - F a := by
  obtain ⟨hr, hIr⟩ := real_integral_of_primitive hab
    (Complex.continuous_re.comp_continuousOn hf) (Complex.continuous_re.comp_continuousOn hF)
    (fun y hy => Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hd y hy))
  obtain ⟨him, hIi⟩ := real_integral_of_primitive hab
    (Complex.continuous_im.comp_continuousOn hf) (Complex.continuous_im.comp_continuousOn hF)
    (fun y hy => Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hd y hy))
  refine ⟨⟨hr, him⟩, ?_⟩
  apply Complex.ext
  · exact (complexIntegral_components f ⟨hr, him⟩).1.trans hIr
  · exact (complexIntegral_components f ⟨hr, him⟩).2.trans hIi


/-- Dropping degree zero in an ordinary series, including conditional sums. -/
theorem sum_range_tail {A : Type*} [AddCommGroup A] (b : ℕ → A) (N : ℕ) :
    (∑ n ∈ Finset.range (N+1), b (n+1)) =
      (∑ n ∈ Finset.range (N+1+1), b n) - b 0 := by
  rw [Finset.sum_range_succ' b (N+1), add_sub_cancel_right]

theorem real_tail_hasSum {b : ℕ → ℝ} {S : ℝ} (h : RealSeriesHasSum b S) :
    RealSeriesHasSum (fun n => b (n+1)) (S - b 0) := by
  apply (realSequenceConverges_iff _ _).mpr
  have ht := (((realSequenceConverges_iff _ _).mp h).comp
    (tendsto_add_atTop_nat 1)).sub_const (b 0)
  apply ht.congr
  intro N
  exact (sum_range_tail b N).symm

theorem complex_tail_hasSum {b : ℕ → ℂ} {S : ℂ} (h : ComplexSeriesHasSum b S) :
    ComplexSeriesHasSum (fun n => b (n+1)) (S - b 0) := by
  apply (complexSequenceConverges_iff _ _).mpr
  have ht := (((complexSequenceConverges_iff _ _).mp h).comp
    (tendsto_add_atTop_nat 1)).sub_const (b 0)
  apply ht.congr
  intro N
  exact (sum_range_tail b N).symm

end PowerSeriesIntegration
open PowerSeriesIntegration

theorem real_powerSeries_primitive_derivative :
    Specs.SingleVariableAnalysis.Ch13.Integration.realPrimitiveDerivative := by
  intro a c f g hf hg x hx
  change (∀ y : ℝ, ENNReal.ofReal |y-c| < realPowerSeriesRadius a →
    RealPowerSeriesHasSum a c y (f y)) at hf
  change (∀ y : ℝ, ENNReal.ofReal |y-c| < realPowerSeriesRadius a →
    RealPowerSeriesHasSum (realPrimitiveCoefficients a) c y (g y)) at hg
  change ENNReal.ofReal |x-c| < realPowerSeriesRadius a at hx
  have hg' : ∀ y : ℝ, ENNReal.ofReal |y-c| < realPowerSeriesRadius (realPrimitiveCoefficients a) →
      RealPowerSeriesHasSum (realPrimitiveCoefficients a) c y (g y) := by
    intro y hy
    exact hg y (by rwa [real_powerSeries_primitive_radius] at hy)
  have hx' : ENNReal.ofReal |x-c| < realPowerSeriesRadius (realPrimitiveCoefficients a) := by
    rwa [real_powerSeries_primitive_radius]
  have hsum := (real_powerSeries_all_derivatives (realPrimitiveCoefficients a) c g hg' 1 x hx').1
  change RealSeriesHasSum (realFormalDerivativeTerm (realPrimitiveCoefficients a) c 1 x)
    (iteratedDeriv 1 g x) at hsum
  have htail := real_tail_hasSum hsum
  have hz : realFormalDerivativeTerm (realPrimitiveCoefficients a) c 1 x 0 = 0 := by
    simp [realFormalDerivativeTerm, realPrimitiveCoefficients]
  have he : (fun n => realFormalDerivativeTerm (realPrimitiveCoefficients a) c 1 x (n+1)) =
      realPowerSeriesTerm a c x := by
    funext n
    simp only [realFormalDerivativeTerm, Nat.descFactorial_one, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one, realPrimitiveCoefficients, realPowerSeriesTerm]
    rw [mul_div_cancel₀ _ (by positivity)]
  rw [hz, sub_zero, he] at htail
  have hv : iteratedDeriv 1 g x = f x :=
    real_series_sum_unique _ _ _ htail (hf x hx)
  have hd := (real_powerSeries_all_derivatives (realPrimitiveCoefficients a) c g hg' 0 x hx').2
  simpa only [iteratedDeriv_zero, zero_add, hv] using hd

theorem complex_powerSeries_primitive_derivative :
    Specs.SingleVariableAnalysis.Ch13.Integration.complexPrimitiveDerivative := by
  intro a c f g hf hg x hx
  change (∀ y : ℝ, ENNReal.ofReal |y-c| < complexPowerSeriesRadius a →
    ComplexPowerSeriesHasSum a c (y : ℂ) (f y)) at hf
  change (∀ y : ℝ, ENNReal.ofReal |y-c| < complexPowerSeriesRadius a →
    ComplexPowerSeriesHasSum (complexPrimitiveCoefficients a) c (y : ℂ) (g y)) at hg
  change ENNReal.ofReal |x-c| < complexPowerSeriesRadius a at hx
  have hg' : ∀ y : ℝ, ENNReal.ofReal |y-c| < complexPowerSeriesRadius (complexPrimitiveCoefficients a) →
      ComplexPowerSeriesHasSum (complexPrimitiveCoefficients a) c (y : ℂ) (g y) := by
    intro y hy
    exact hg y (by rwa [complex_powerSeries_primitive_radius] at hy)
  have hx' : ENNReal.ofReal |x-c| < complexPowerSeriesRadius (complexPrimitiveCoefficients a) := by
    rwa [complex_powerSeries_primitive_radius]
  have hsum := (complex_powerSeries_all_derivatives (complexPrimitiveCoefficients a) c g hg' 1 x hx').1
  change ComplexSeriesHasSum (complexFormalDerivativeTerm (complexPrimitiveCoefficients a) c 1 (x : ℂ))
    (iteratedDeriv 1 g x) at hsum
  have htail := complex_tail_hasSum hsum
  have hz : complexFormalDerivativeTerm (complexPrimitiveCoefficients a) c 1 (x : ℂ) 0 = 0 := by
    simp [complexFormalDerivativeTerm, complexPrimitiveCoefficients]
  have he : (fun n => complexFormalDerivativeTerm (complexPrimitiveCoefficients a) c 1 (x : ℂ) (n+1)) =
      complexPowerSeriesTerm a c (x : ℂ) := by
    funext n
    simp only [complexFormalDerivativeTerm, Nat.descFactorial_one, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one, complexPrimitiveCoefficients, complexPowerSeriesTerm]
    rw [mul_div_cancel₀ _ (by exact_mod_cast (show (n+1 : ℝ) ≠ 0 by positivity))]
  rw [hz, sub_zero, he] at htail
  have hv : iteratedDeriv 1 g x = f x :=
    complex_series_sum_unique _ _ _ htail (hf x hx)
  have hd := (complex_powerSeries_all_derivatives (complexPrimitiveCoefficients a) c g hg' 0 x hx').2
  simpa only [iteratedDeriv_zero, zero_add, hv] using hd

namespace PowerSeriesIntegration
/-- Every point of the integration segment remains in the same smaller disk. -/
theorem distance_le_of_mem_hull (c x y : ℝ) (hy : y ∈ Icc (min c x) (max c x)) :
    |y-c| ≤ |x-c| := by
  rcases le_total c x with h | h
  · rw [min_eq_left h, max_eq_right h] at hy
    rw [abs_of_nonneg (sub_nonneg.mpr hy.1), abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [hy.2]
  · rw [min_eq_right h, max_eq_left h] at hy
    rw [abs_of_nonpos (sub_nonpos.mpr hy.2), abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [hy.1]
end PowerSeriesIntegration

theorem real_powerSeries_termwise_integration :
    Specs.SingleVariableAnalysis.Ch13.Integration.realTermwiseIntegration := by
  intro a c f hf x hx
  change (∀ y : ℝ, ENNReal.ofReal |y-c| < realPowerSeriesRadius a →
    RealPowerSeriesHasSum a c y (f y)) at hf
  change ENNReal.ofReal |x-c| < realPowerSeriesRadius a at hx
  obtain ⟨g, hg⟩ := real_powerSeries_sum_exists (realPrimitiveCoefficients a) c
  change (∀ y : ℝ, ENNReal.ofReal |y-c| < realPowerSeriesRadius (realPrimitiveCoefficients a) →
    RealPowerSeriesHasSum (realPrimitiveCoefficients a) c y (g y)) at hg
  have hg' : ∀ y : ℝ, ENNReal.ofReal |y-c| < realPowerSeriesRadius a →
      RealPowerSeriesHasSum (realPrimitiveCoefficients a) c y (g y) := by
    intro y hy
    exact hg y (by rwa [real_powerSeries_primitive_radius])
  have h0 : ENNReal.ofReal |c-c| < realPowerSeriesRadius a :=
    (ENNReal.ofReal_le_ofReal (show |c-c| ≤ |x-c| by simp)).trans_lt hx
  have hgc : g c = 0 := by
    have hh := real_powerSeries_sum_unique (realPrimitiveCoefficients a) c c (g c)
      ((realPrimitiveCoefficients a) 0) (hg' c h0)
      (real_powerSeries_center_hasSum (realPrimitiveCoefficients a) c).1
    simpa [realPrimitiveCoefficients] using hh
  have hsum := real_tail_hasSum (hg' x hx)
  change RealSeriesHasSum
    (fun n => realPowerSeriesTerm (realPrimitiveCoefficients a) c x (n+1))
    (g x - realPowerSeriesTerm (realPrimitiveCoefficients a) c x 0) at hsum
  have hsum' : RealSeriesHasSum (fun n => a n / (n+1 : ℝ) * (x-c)^(n+1)) (g x) := by
    simpa [realPowerSeriesTerm, realPrimitiveCoefficients] using hsum
  have hd : ∀ y : ℝ, ENNReal.ofReal |y-c| < realPowerSeriesRadius a → HasDerivAt g (f y) y :=
    real_powerSeries_primitive_derivative a c f g hf hg'
  have hinside (y : ℝ) (hy : y ∈ Icc (min c x) (max c x)) :
      ENNReal.ofReal |y-c| < realPowerSeriesRadius a :=
    (ENNReal.ofReal_le_ofReal (distance_le_of_mem_hull c x y hy)).trans_lt hx
  have hfc : ContinuousOn f (Icc (min c x) (max c x)) := by
    intro y hy
    have hh := (real_powerSeries_all_derivatives a c f hf 0 y (hinside y hy)).2
    simpa only [iteratedDeriv_zero] using hh.continuousAt.continuousWithinAt
  have hgg : ContinuousOn g (Icc (min c x) (max c x)) :=
    fun y hy => (hd y (hinside y hy)).continuousAt.continuousWithinAt
  obtain ⟨hi, hI⟩ := real_integral_of_primitive (min_le_max (a := c) (b := x)) hfc hgg
    (fun y hy => hd y (hinside y ⟨hy.1.le, hy.2.le⟩))
  change ∃ hi : Riemann.RealIntegrable f (min c x) (max c x),
    RealSeriesHasSum (fun n => a n / (n+1 : ℝ) * (x-c)^(n+1))
      (if c ≤ x then Riemann.realIntegral f hi else -Riemann.realIntegral f hi)
  refine ⟨hi, ?_⟩
  have hval : (if c ≤ x then Riemann.realIntegral f hi else -Riemann.realIntegral f hi) = g x := by
    by_cases hcx : c ≤ x
    · simpa only [ite_eq_left hcx, min_eq_left hcx, max_eq_right hcx, hgc, sub_zero] using hI
    · have hxc : x ≤ c := le_of_not_ge hcx
      rw [ite_eq_right hcx, hI, min_eq_right hxc, max_eq_left hxc, hgc, zero_sub, neg_neg]
  rwa [hval]

theorem complex_powerSeries_termwise_integration :
    Specs.SingleVariableAnalysis.Ch13.Integration.complexTermwiseIntegration := by
  intro a c f hf x hx
  change (∀ y : ℝ, ENNReal.ofReal |y-c| < complexPowerSeriesRadius a →
    ComplexPowerSeriesHasSum a c (y : ℂ) (f y)) at hf
  change ENNReal.ofReal |x-c| < complexPowerSeriesRadius a at hx
  obtain ⟨g, hg⟩ := complex_powerSeries_sum_exists (complexPrimitiveCoefficients a) c
  change (∀ y : ℝ, ENNReal.ofReal |y-c| < complexPowerSeriesRadius (complexPrimitiveCoefficients a) →
    ComplexPowerSeriesHasSum (complexPrimitiveCoefficients a) c (y : ℂ) (g y)) at hg
  have hg' : ∀ y : ℝ, ENNReal.ofReal |y-c| < complexPowerSeriesRadius a →
      ComplexPowerSeriesHasSum (complexPrimitiveCoefficients a) c (y : ℂ) (g y) := by
    intro y hy
    exact hg y (by rwa [complex_powerSeries_primitive_radius])
  have h0 : ENNReal.ofReal |c-c| < complexPowerSeriesRadius a :=
    (ENNReal.ofReal_le_ofReal (show |c-c| ≤ |x-c| by simp)).trans_lt hx
  have hgc : g c = 0 := by
    have hh := complex_powerSeries_sum_unique (complexPrimitiveCoefficients a) c (c : ℂ) (g c)
      ((complexPrimitiveCoefficients a) 0) (hg' c h0)
      (complex_powerSeries_center_hasSum (complexPrimitiveCoefficients a) c).1
    simpa [complexPrimitiveCoefficients] using hh
  have hsum := complex_tail_hasSum (hg' x hx)
  change ComplexSeriesHasSum
    (fun n => complexPowerSeriesTerm (complexPrimitiveCoefficients a) c (x : ℂ) (n+1))
    (g x - complexPowerSeriesTerm (complexPrimitiveCoefficients a) c (x : ℂ) 0) at hsum
  have hsum' : ComplexSeriesHasSum (fun n => a n / (n+1 : ℂ) * ((x : ℂ)-(c : ℂ))^(n+1)) (g x) := by
    simpa [complexPowerSeriesTerm, complexPrimitiveCoefficients] using hsum
  have hd : ∀ y : ℝ, ENNReal.ofReal |y-c| < complexPowerSeriesRadius a → HasDerivAt g (f y) y :=
    complex_powerSeries_primitive_derivative a c f g hf hg'
  have hinside (y : ℝ) (hy : y ∈ Icc (min c x) (max c x)) :
      ENNReal.ofReal |y-c| < complexPowerSeriesRadius a :=
    (ENNReal.ofReal_le_ofReal (distance_le_of_mem_hull c x y hy)).trans_lt hx
  have hfc : ContinuousOn f (Icc (min c x) (max c x)) := by
    intro y hy
    have hh := (complex_powerSeries_all_derivatives a c f hf 0 y (hinside y hy)).2
    simpa only [iteratedDeriv_zero] using hh.continuousAt.continuousWithinAt
  have hgg : ContinuousOn g (Icc (min c x) (max c x)) :=
    fun y hy => (hd y (hinside y hy)).continuousAt.continuousWithinAt
  obtain ⟨hi, hI⟩ := complex_integral_of_primitive (min_le_max (a := c) (b := x)) hfc hgg
    (fun y hy => hd y (hinside y ⟨hy.1.le, hy.2.le⟩))
  change ∃ hi : Riemann.ComplexIntegrable f (min c x) (max c x),
    ComplexSeriesHasSum (fun n => a n / (n+1 : ℂ) * ((x : ℂ)-(c : ℂ))^(n+1))
      (if c ≤ x then Riemann.complexIntegral f hi else -Riemann.complexIntegral f hi)
  refine ⟨hi, ?_⟩
  have hval : (if c ≤ x then Riemann.complexIntegral f hi else -Riemann.complexIntegral f hi) = g x := by
    by_cases hcx : c ≤ x
    · simpa only [ite_eq_left hcx, min_eq_left hcx, max_eq_right hcx, hgc, sub_zero] using hI
    · have hxc : x ≤ c := le_of_not_ge hcx
      rw [ite_eq_right hcx, hI, min_eq_right hxc, max_eq_left hxc, hgc, zero_sub, neg_neg]
  rwa [hval]

end SingleVariableAnalysis
