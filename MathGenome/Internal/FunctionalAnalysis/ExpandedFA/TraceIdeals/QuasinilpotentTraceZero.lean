import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.QuasinilpotentTraceZero
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceBasisCyclicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.WeylSumsProducts
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
universe u
namespace ExpandedFA.TraceIdeals.QuasinilpotentTraceZero
open Filter Finset
open scoped Topology

/-- An exponential cannot be bounded by a polynomial times a strictly slower
exponential on the positive half-line. -/
lemma exponential_rate_le (a b C : ℝ) (n : ℕ)
    (h : ∀ r : ℝ, 1 ≤ r → Real.exp (a * r) ≤ C * r ^ n * Real.exp (b * r)) :
    a ≤ b := by
  by_contra hab
  have hd : 0 < a - b := sub_pos.mpr (lt_of_not_ge hab)
  have ht : Tendsto (fun r : ℝ => Real.exp ((a-b)*r) / r^n) atTop atTop := by
    simpa only [Real.rpow_natCast] using
      tendsto_exp_mul_div_rpow_atTop (n : ℝ) (a-b) hd
  obtain ⟨r, hr, hlarge⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (ht.eventually (eventually_gt_atTop C))).exists
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsmall : Real.exp ((a-b)*r) / r^n ≤ C := by
    rw [div_le_iff₀ (pow_pos hrpos n)]
    rw [sub_mul, Real.exp_sub]
    apply (div_le_iff₀ (Real.exp_pos (b*r))).mpr
    exact h r hr
  exact (not_lt_of_ge hsmall) hlarge

/-- The fixed finite head of a singular-value product has polynomial growth. -/
lemma finite_product_le_monomial (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (n : ℕ) (r : ℝ) (hr : 1 ≤ r) :
    (∏ i ∈ range n, (1+r*s i)) ≤ (∏ i ∈ range n, (1+s i)) * r^n := by
  calc
    _ ≤ ∏ i ∈ range n, ((1+s i)*r) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact add_nonneg zero_le_one (mul_nonneg (zero_le_one.trans hr) (hs i))
      · intro i _; nlinarith [hs i]
    _ = _ := by rw [prod_mul_distrib]; simp

/-- This is the last real-variable argument in the manuscript proof: a
summable singular sequence leaves arbitrarily small exponential tails. -/
lemma nonpositive_of_product_exp_bounds (a : ℝ) (s : ℕ → ℝ)
    (hs : ∀ i, 0 ≤ s i) (_hsum : Summable s)
    (h : ∀ (r : ℝ), 0 ≤ r → ∀ n : ℕ,
      Real.exp (a*r) ≤ (∏ i ∈ range n, (1+r*s i)) *
        Real.exp ((∑' k, s (k+n))*r)) : a ≤ 0 := by
  have htail (n : ℕ) : a ≤ ∑' k, s (k+n) := by
    apply exponential_rate_le a _ (∏ i ∈ range n, (1+s i)) n
    intro r hr
    exact (h r (zero_le_one.trans hr) n).trans
      (mul_le_mul_of_nonneg_right (finite_product_le_monomial s hs n r hr)
        (Real.exp_pos _).le)
  exact ge_of_tendsto' (tendsto_sum_nat_add s) htail

/-- Spectral collapse follows from upper hemicontinuity, without assuming
separability, normality, or a nonzero-dimensional space. -/
lemma spectrum_eventually_small {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {Q : H →L[ℂ] H} (hQ : spectrum ℂ Q ⊆ {0})
    {F : ℕ → H →L[ℂ] H} (hF : Tendsto F atTop (𝓝 Q))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z ∈ spectrum ℂ (F n), ‖z‖ < ε := by
  have hsubset : spectrum ℂ Q ⊆ Metric.ball 0 ε := by
    intro z hz
    have hz0 : z = 0 := Set.mem_singleton_iff.mp (hQ hz)
    simpa [hz0] using hε
  have h := (upperHemicontinuous_spectrum ℂ (H →L[ℂ] H)).forall_isOpen
    Q (Metric.ball 0 ε) Metric.isOpen_ball hsubset
  filter_upwards [hF.eventually h] with n hn z hz
  simpa only [Metric.mem_ball, dist_zero_right] using hn hz

/-- A dimension-independent error estimate for a finite product. In particular,
no logarithm or choice of a branch is needed for the determinant limit. -/
lemma finite_product_exp_error {ι : Type*} (s : Finset ι) (x : ι → ℂ)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ 1) :
    ‖(∏ i ∈ s, (1+x i)) - Complex.exp (∑ i ∈ s, x i)‖ ≤
      (∑ i ∈ s, ‖x i‖^2) * Real.exp (∑ i ∈ s, ‖x i‖) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have ih' := ih (fun i hi => hx i (mem_insert_of_mem hi))
    have hj' := hx j (mem_insert_self j s)
    have hnorm : ‖1+x j‖ ≤ Real.exp ‖x j‖ := by
      calc
        _ ≤ 1 + ‖x j‖ := by simpa using norm_add_le (1 : ℂ) (x j)
        _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp ‖x j‖
    have herr : ‖1+x j-Complex.exp (x j)‖ ≤ ‖x j‖^2 := by
      rw [show 1+x j-Complex.exp (x j) = -(Complex.exp (x j)-1-x j) by ring,
        norm_neg]
      exact Complex.norm_exp_sub_one_sub_id_le hj'
    have hexp : ‖Complex.exp (∑ i ∈ s, x i)‖ ≤
        Real.exp (∑ i ∈ s, ‖x i‖) :=
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (norm_sum_le _ _))
    rw [prod_insert hj, sum_insert hj, sum_insert hj, sum_insert hj, Complex.exp_add]
    calc
      _ = ‖(1+x j)*((∏ i ∈ s, (1+x i)) - Complex.exp (∑ i ∈ s, x i)) +
          (1+x j-Complex.exp (x j))*Complex.exp (∑ i ∈ s, x i)‖ := by congr 1; ring
      _ ≤ ‖1+x j‖ * ‖(∏ i ∈ s, (1+x i)) - Complex.exp (∑ i ∈ s, x i)‖ +
          ‖1+x j-Complex.exp (x j)‖ * ‖Complex.exp (∑ i ∈ s, x i)‖ := by
        simpa only [norm_mul] using norm_add_le
          ((1+x j)*((∏ i ∈ s, (1+x i)) - Complex.exp (∑ i ∈ s, x i)))
          ((1+x j-Complex.exp (x j))*Complex.exp (∑ i ∈ s, x i))
      _ ≤ Real.exp ‖x j‖ * ((∑ i ∈ s, ‖x i‖^2) *
          Real.exp (∑ i ∈ s, ‖x i‖)) + ‖x j‖^2 *
          Real.exp (∑ i ∈ s, ‖x i‖) := by gcongr
      _ ≤ Real.exp ‖x j‖ * ((∑ i ∈ s, ‖x i‖^2) *
          Real.exp (∑ i ∈ s, ‖x i‖)) + ‖x j‖^2 *
          (Real.exp ‖x j‖ * Real.exp (∑ i ∈ s, ‖x i‖)) := by
        gcongr
        exact le_mul_of_one_le_left (Real.exp_pos _).le
          (Real.one_le_exp (norm_nonneg _))
      _ = _ := by rw [Real.exp_add]; ring

/-- A bounded first absolute moment and a vanishing largest entry force the
second moment of finite lists to vanish, even when their lengths vary. -/
lemma finite_squares_tendsto_zero (d : ℕ → ℕ) (x : ∀ n, Fin (d n) → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ∑ i, ‖x n i‖ ≤ C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i, ‖x n i‖ ≤ ε) :
    Tendsto (fun n => ∑ i, ‖x n i‖^2) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsmall (ε/(C+1)) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  have he : (∑ i, ‖x n i‖^2) ≤ (ε/(C+1))*C := by
    calc
      _ ≤ ∑ i, (ε/(C+1))*‖x n i‖ := by
        apply sum_le_sum
        intro i _
        nlinarith [mul_le_mul_of_nonneg_right (hN n hn i) (norm_nonneg (x n i))]
      _ = (ε/(C+1))*(∑ i, ‖x n i‖) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound n) (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sum_nonneg (fun _ _ => sq_nonneg _))]
  apply he.trans_lt
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < C+1)]
  nlinarith

/-- The elementary triangular-array determinant limit. Its only hypotheses
are bounded absolute sums, uniformly small entries, and convergence of sums. -/
lemma finite_product_one_add_tendsto_exp (d : ℕ → ℕ) (x : ∀ n, Fin (d n) → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ∑ i, ‖x n i‖ ≤ C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i, ‖x n i‖ ≤ ε)
    {a : ℂ} (hsum : Tendsto (fun n => ∑ i, x n i) atTop (𝓝 a)) :
    Tendsto (fun n => ∏ i, (1+x n i)) atTop (𝓝 (Complex.exp a)) := by
  have hsq := finite_squares_tendsto_zero d x C hC hbound hsmall
  have herr : Tendsto (fun n => ‖(∏ i, (1+x n i)) - Complex.exp (∑ i, x n i)‖)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (by simpa using hsq.mul_const (Real.exp C))
    filter_upwards [hsmall 1 zero_lt_one] with n hn
    exact (finite_product_exp_error univ (x n) (fun i _ => hn i)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hbound n))
        (sum_nonneg (fun _ _ => sq_nonneg _)))
  have hdiff : Tendsto (fun n => (∏ i, (1+x n i)) - Complex.exp (∑ i, x n i))
      atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr herr
  have hexp := Complex.continuous_exp.continuousAt.tendsto.comp hsum
  simpa using hdiff.add hexp

/-- The complex exponential limit and the singular head/tail bounds already
force its linear exponent to vanish. This is independent of operator theory. -/
lemma zero_of_exp_product_bounds (a : ℂ) (s : ℕ → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hsum : Summable s)
    (h : ∀ (z : ℂ) (n : ℕ),
      ‖Complex.exp (-z*a)‖ ≤ (∏ i ∈ range n, (1+‖z‖*s i)) *
        Real.exp (‖z‖*(∑' k, s (k+n)))) : a = 0 := by
  have hsq : ‖a‖^2 ≤ 0 := by
    apply nonpositive_of_product_exp_bounds (‖a‖^2) (fun i => ‖a‖*s i)
      (fun i => mul_nonneg (norm_nonneg _) (hs i)) (hsum.mul_left ‖a‖)
    intro r hr n
    let z : ℂ := -(r : ℂ) * star a
    have hconj : star a*a = ((‖a‖^2 : ℝ) : ℂ) := by
      simpa only [RCLike.star_def, Complex.ofReal_pow] using Complex.conj_mul' a
    have hza : -z*a = ((r*‖a‖^2 : ℝ) : ℂ) := by
      calc
        -z*a = (r : ℂ)*(star a*a) := by dsimp [z]; ring
        _ = _ := by rw [hconj, Complex.ofReal_mul]
    have hz : ‖z‖ = r*‖a‖ := by
      simp only [z, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr, norm_star]
    have hb := h z n
    rw [hza, Complex.norm_exp_ofReal, hz] at hb
    rw [tsum_mul_left]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  have hz : ‖a‖ = 0 := by nlinarith [sq_nonneg ‖a‖]
  exact norm_eq_zero.mp hz

/-- Uniform head/tail bound for all finite initial products. This bypasses
the construction of an infinite product. -/
lemma finite_product_head_tail_bound (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hsum : Summable s) (r : ℝ) (hr : 0 ≤ r) (n m : ℕ) :
    (∏ i ∈ range n, (1+r*s i)) ≤ (∏ i ∈ range m, (1+r*s i)) *
      Real.exp (r*(∑' k, s (k+m))) := by
  have hp : Monotone (fun n => ∏ i ∈ range n, (1+r*s i)) := by
    apply monotone_nat_of_le_succ
    intro k
    rw [prod_range_succ]
    have hnonneg : 0 ≤ ∏ i ∈ range k, (1+r*s i) :=
      prod_nonneg (fun i _ => add_nonneg zero_le_one (mul_nonneg hr (hs i)))
    nlinarith [mul_nonneg hr (hs k)]
  have hhead : 0 ≤ ∏ i ∈ range m, (1+r*s i) :=
    prod_nonneg (fun i _ => add_nonneg zero_le_one (mul_nonneg hr (hs i)))
  rcases le_total n m with hnm | hmn
  · exact (hp hnm).trans (le_mul_of_one_le_right hhead
      (Real.one_le_exp (mul_nonneg hr (tsum_nonneg (fun k => hs (k+m))))))
  · have hn : n = m+(n-m) := by omega
    rw [hn, prod_range_add]
    apply mul_le_mul_of_nonneg_left _ hhead
    apply (Real.prod_one_add_le_exp_sum (range (n-m))
      (fun i => mul_nonneg hr (hs (m+i)))).trans
    apply Real.exp_le_exp.mpr
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ hr
    have ht : Summable (fun k => s (k+m)) := (summable_nat_add_iff m).mpr hsum
    simpa only [Nat.add_comm m] using
      ht.sum_le_tsum (range (n-m)) (fun k _ => hs (k+m))

/-- Scalar assembly: bounded finite spectral lists, collapsing entries,
convergent traces, and Weyl's shifted-product bound force the limiting trace
to be zero. The lengths of the lists are allowed to grow arbitrarily. -/
lemma zero_of_finite_spectral_lists (d : ℕ → ℕ) (ev : ∀ n, Fin (d n) → ℂ)
    (a : ℂ) (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) (hsum : Summable s)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ∑ i, ‖ev n i‖ ≤ C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i, ‖ev n i‖ ≤ ε)
    (htrace : Tendsto (fun n => ∑ i, ev n i) atTop (𝓝 a))
    (hprod : ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
      (∏ i, (1+r*‖ev n i‖)) ≤ ∏ i ∈ range (d n), (1+r*s i)) : a = 0 := by
  apply zero_of_exp_product_bounds a s hs hsum
  intro z m
  have hscaled (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∀ i, ‖-z*ev n i‖ ≤ ε := by
    filter_upwards [hsmall (ε/(‖z‖+1)) (by positivity)] with n hn i
    rw [norm_mul, norm_neg]
    have hi := (le_div_iff₀ (by positivity : 0 < ‖z‖+1)).mp (hn i)
    nlinarith [norm_nonneg (ev n i)]
  have hbscaled (n : ℕ) : (∑ i, ‖-z*ev n i‖) ≤ ‖z‖*C := by
    simpa only [norm_mul, norm_neg, ← mul_sum] using
      mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg z)
  have htscaled : Tendsto (fun n => ∑ i, -z*ev n i) atTop (𝓝 (-z*a)) := by
    simpa only [mul_sum] using htrace.const_mul (-z)
  have hlim := finite_product_one_add_tendsto_exp d (fun n i => -z*ev n i)
    (‖z‖*C) (mul_nonneg (norm_nonneg z) hC) hbscaled hscaled htscaled
  apply le_of_tendsto' hlim.norm
  intro n
  calc
    _ ≤ ∏ i, (1+‖z‖*‖ev n i‖) := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      simpa only [norm_one, norm_mul, norm_neg] using norm_add_le (1 : ℂ) (-z*ev n i)
    _ ≤ ∏ i ∈ range (d n), (1+‖z‖*s i) := hprod n ‖z‖ (norm_nonneg z)
    _ ≤ _ := finite_product_head_tail_bound s hs hsum ‖z‖ (norm_nonneg z) (d n) m

open TraceClassDefinitions

/-- Trace subtraction is justified by the absolute diagonal sums. -/
lemma trace_sub (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S T : H →L[ℂ] H) (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace (S-T) = trace S - trace T := by
  have hSsum := (diagonal_trace ℂ H S hS _ TraceClassDefinitions.Spec.chosenBasis).1.of_norm
  have hTsum := (diagonal_trace ℂ H T hT _ TraceClassDefinitions.Spec.chosenBasis).1.of_norm
  change (∑' i, inner ℂ (TraceClassDefinitions.Spec.chosenBasis i)
    ((S-T) (TraceClassDefinitions.Spec.chosenBasis i))) = _
  simp only [sub_apply, inner_sub_right]
  exact hSsum.tsum_sub hTsum

/-- Convergence in the shared trace norm implies convergence of traces. -/
lemma trace_tendsto_of_traceNorm {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {Q : H →L[ℂ] H}
    (hQ : IsTraceClass Q) {F : ℕ → H →L[ℂ] H} (hF : ∀ n, IsTraceClass (F n))
    (h : Tendsto (fun n => traceNorm (F n-Q)) atTop (𝓝 0)) :
    Tendsto (fun n => trace (F n)) atTop (𝓝 (trace Q)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ h
  intro n
  rw [← trace_sub H (F n) Q (hF n) hQ]
  exact trace_bound ℂ H (F n-Q) (TraceNormIdeal.traceClass_sub _ _ (hF n) hQ)

/-- Convergence in the shared trace norm also implies operator-norm convergence. -/
lemma tendsto_of_traceNorm {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {Q : H →L[ℂ] H}
    (hQ : IsTraceClass Q) {F : ℕ → H →L[ℂ] H} (hF : ∀ n, IsTraceClass (F n))
    (h : Tendsto (fun n => traceNorm (F n-Q)) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 Q) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => TraceNormIdeal.opNorm_le_traceNorm _
      (TraceNormIdeal.traceClass_sub _ _ (hF n) hQ)) h

/-- A contraction on the left contracts the shared trace norm, including on
the zero space (where the identity has norm zero). -/
lemma traceNorm_comp_contraction {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T A : H →L[ℂ] H)
    (hT : IsTraceClass T) (hA : ‖A‖ ≤ 1) :
    IsTraceClass (A.comp T) ∧ traceNorm (A.comp T) ≤ traceNorm T := by
  obtain ⟨hm, hb⟩ := TraceNormIdeal.two_sided_ideal ℂ H H H H T A
    (ContinuousLinearMap.id ℂ H) hT
  simp only [ContinuousLinearMap.comp_id] at hm hb
  refine ⟨hm, hb.trans ?_⟩
  have ht := TraceNormIdeal.traceNorm_nonneg T hT
  calc
    _ ≤ 1 * traceNorm T * 1 := by
      gcongr
      exact ContinuousLinearMap.norm_id_le
    _ = _ := by ring

/-- Projecting the range of an arbitrary finite-rank trace-norm approximation
gives a finite-rank left compression with singular values dominated by those
of the original operator. No countability of the ambient Hilbert space is used. -/
lemma exists_finite_rank_singular_approximants {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Q : H →L[ℂ] H) (hQ : IsTraceClass Q) :
    ∃ F : ℕ → H →L[ℂ] H,
      (∀ n, FiniteDimensional ℂ (F n).range) ∧
      (∀ n, IsTraceClass (F n)) ∧
      Tendsto (fun n => traceNorm (F n-Q)) atTop (𝓝 0) ∧
      (∀ n, traceNorm (F n) ≤ traceNorm Q) ∧
      (∀ n k, TraceClassDefinitions.Spec.singularSequence (F n) k ≤
        TraceClassDefinitions.Spec.singularSequence Q k) := by
  classical
  have hg (n : ℕ) := TraceNormIdeal.finite_rank_dense ℂ H H Q hQ
    (1/((n : ℝ)+1)) (by positivity)
  choose G hGrank hG hdiff herror using hg
  let M (n : ℕ) : Submodule ℂ H := (G n).range
  letI (n : ℕ) : FiniteDimensional ℂ (M n) := hGrank n
  let P (n : ℕ) : H →L[ℂ] H := (M n).starProjection
  let F (n : ℕ) : H →L[ℂ] H := (P n).comp Q
  have hp (n : ℕ) : ‖P n‖ ≤ 1 := (M n).starProjection_norm_le
  have hF (n : ℕ) := traceNorm_comp_contraction Q (P n) hQ (hp n)
  have herr (n : ℕ) : traceNorm (Q-F n) ≤ traceNorm (Q-G n) := by
    have hh := traceNorm_comp_contraction (Q-G n) (M n)ᗮ.starProjection
      (hdiff n) (M n)ᗮ.starProjection_norm_le
    have heq : (M n)ᗮ.starProjection.comp (Q-G n) = Q-F n := by
      ext x
      have hgx : (M n).starProjection (G n x) = G n x :=
        (M n).starProjection_eq_self_iff.mpr ⟨x, rfl⟩
      simp only [Submodule.starProjection_orthogonal, ContinuousLinearMap.comp_apply,
        sub_apply, ContinuousLinearMap.id_apply, map_sub, hgx, F, P]
      abel
    rw [heq] at hh
    exact hh.2
  refine ⟨F, ?_, fun n => (hF n).1, ?_, fun n => (hF n).2, ?_⟩
  · intro n
    apply Submodule.finiteDimensional_of_le (S₂ := M n)
    rintro x ⟨y, rfl⟩
    exact ((M n).orthogonalProjectionOnto (Q y)).property
  · apply squeeze_zero (fun n => TraceNormIdeal.traceNorm_nonneg _
      (TraceNormIdeal.traceClass_sub _ _ (hF n).1 hQ)) _
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    intro n
    have hneg := (TraceNormIdeal.traceClass_neg (Q-F n)
      (TraceNormIdeal.traceClass_sub _ _ hQ (hF n).1)).2
    rw [neg_sub] at hneg
    rw [hneg]
    exact (herr n).trans (herror n).le
  · intro n k
    have h := CompactSpectral.SingularApproximation.singularValue_ideal ℂ H H H H
      Q (P n) (ContinuousLinearMap.id ℂ H) hQ.1 (k+1) (Nat.succ_pos k)
    simp only [ContinuousLinearMap.comp_id] at h
    apply h.trans
    have hs := TraceNormIdeal.singular_nonneg Q hQ.1 k
    have hpi : ‖P n‖ * ‖ContinuousLinearMap.id ℂ H‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (hp n)
        (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := H))
        (norm_nonneg _) zero_le_one
    calc
      _ ≤ 1 * TraceClassDefinitions.Spec.singularSequence Q k :=
        mul_le_mul_of_nonneg_right hpi hs
      _ = _ := one_mul _

/-- All infinite-dimensional and analytic steps are discharged here. The
remaining input is a generic finite-rank trace/eigenvalue theorem, with no
quasinilpotence assumption. This is an explicit conditional assembly lemma,
not the final quasinilpotent trace theorem. -/
lemma trace_zero_of_finite_rank_spectral_data
    (hfinite : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (F : H →L[ℂ] H), IsTraceClass F →
      FiniteDimensional ℂ F.range →
      ∃ (d : ℕ) (ev : Fin d → ℂ),
        (∀ i, ev i = 0 ∨ ev i ∈ spectrum ℂ F) ∧
        (∑ i, ev i) = trace F ∧ (∑ i, ‖ev i‖) ≤ traceNorm F ∧
        ∀ (r : ℝ), 0 ≤ r → (∏ i, (1+r*‖ev i‖)) ≤
          ∏ i ∈ range d, (1+r*TraceClassDefinitions.Spec.singularSequence F i)) :
    Spec.TraceVanishes.{u} := by
  intro H _ _ _ Q hQ hspec
  obtain ⟨F, hfr, hF, hconv, htr, hsv⟩ := exists_finite_rank_singular_approximants Q hQ
  choose d ev hev htrace hnorm hprod using fun n => hfinite H (F n) (hF n) (hfr n)
  apply zero_of_finite_spectral_lists d ev (trace Q)
    (TraceClassDefinitions.Spec.singularSequence Q)
    (TraceNormIdeal.singular_nonneg Q hQ.1) hQ.2
    (traceNorm Q) (TraceNormIdeal.traceNorm_nonneg Q hQ)
    (fun n => (hnorm n).trans (htr n))
  · intro ε hε
    filter_upwards [spectrum_eventually_small hspec (tendsto_of_traceNorm hQ hF hconv) hε]
      with n hn i
    rcases hev n i with hz | hz
    · simpa only [hz, norm_zero] using hε.le
    · exact (hn (ev n i) hz).le
  · simpa only [htrace] using trace_tendsto_of_traceNorm hQ hF hconv
  · intro n r hr
    apply (hprod n r hr).trans
    exact Finset.prod_le_prod₀
      (fun i _ => add_nonneg zero_le_one
        (mul_nonneg hr (TraceNormIdeal.singular_nonneg (F n) (hF n).1 i)))
      (fun i _ => add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left (hsv n i) hr))

/-- Enumerate the characteristic-root multiset without discarding repeated or zero roots. -/

lemma exists_list_enumeration (m : Multiset ℂ) :
    ∃ (d : ℕ) (ev : Fin d → ℂ),
      (∀ i, ev i ∈ m) ∧ (∑ i, ev i) = m.sum ∧
      ∀ z, (Finset.univ.filter (fun i => ev i = z)).card = m.count z := by
  classical
  let l := m.toList
  refine ⟨l.length, l.get, ?_, ?_, ?_⟩
  · intro i
    have hi : l.get i ∈ l := List.get_mem l i
    simpa only [l, Multiset.mem_toList] using hi
  · have heq : (∑ i : Fin l.length, l.get i) = l.sum := by
      rw [← List.sum_ofFn, List.ofFn_get]
    simpa only [l, Multiset.sum_toList] using heq
  · intro z
    have heq := Fin.card_filter_univ_eq_vector_get_eq_count z (⟨l, rfl⟩ : List.Vector ℂ l.length)
    change (Finset.univ.filter (fun i => l.get i = z)).card = l.count z at heq
    simpa only [l, ← Multiset.coe_count, Multiset.coe_toList] using heq



lemma roots_count_restrict_le {V : Type u} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (M : Submodule ℂ V) [FiniteDimensional ℂ M]
    (hM : ∀ x ∈ M, f x ∈ M) (z : ℂ)
    [FiniteDimensional ℂ (f.maxGenEigenspace z)] :
    ((f.restrict hM).charpoly.roots.count z) ≤
      Module.finrank ℂ (f.maxGenEigenspace z) := by
  classical
  rw [Polynomial.count_roots, ← LinearMap.finrank_maxGenEigenspace_eq]
  let G := Module.End.maxGenEigenspace (f.restrict hM) z
  have hle : G.map M.subtype ≤ f.maxGenEigenspace z := by
    exact Module.End.map_genEigenspace_le M.subtype (by ext x; rfl) z ⊤
  rw [← Submodule.finrank_map_subtype_eq M G]
  exact Submodule.finrank_mono hle

lemma roots_restrict_hasEigenvalue {V : Type u} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (M : Submodule ℂ V) [FiniteDimensional ℂ M]
    (hM : ∀ x ∈ M, f x ∈ M) (z : ℂ)
    (hz : z ∈ (f.restrict hM).charpoly.roots) : f.HasEigenvalue z := by
  have hz' : Module.End.HasEigenvalue (f.restrict hM) z :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      (Polynomial.isRoot_of_mem_roots hz)
  obtain ⟨x, hx, hne⟩ := hz'.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector
  change f.HasEigenvector z (x : V)
  refine ⟨?_, ?_⟩
  · apply Module.End.mem_eigenspace_iff.mpr
    exact congrArg (fun a : M => (a : V)) (Module.End.mem_eigenspace_iff.mp hx)
  · exact fun hx0 => hne (Subtype.ext hx0)



lemma trace_eq_linearMap_trace {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (A : V →L[ℂ] V) :
    trace A = A.toLinearMap.trace ℂ V := by
  let b := stdOrthonormalBasis ℂ V
  have hA : IsTraceClass A := ExpandedFA.TraceIdeals.TraceNormIdeal.finite_rank_traceClass A
  have hb := (ExpandedFA.TraceIdeals.TraceBasisCyclicity.diagonal_trace
    ℂ V A hA _ b.toHilbertBasis).2.tsum_eq
  calc
    trace A = ∑' j, inner ℂ (b.toHilbertBasis j) (A (b.toHilbertBasis j)) := hb.symm
    _ = A.toLinearMap.trace ℂ V := by
      rw [tsum_fintype, LinearMap.trace_eq_sum_inner A.toLinearMap b]
      simp only [OrthonormalBasis.coe_toHilbertBasis]
      rfl

lemma finite_rank_trace_eq_roots {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (F : H →L[ℂ] H) [FiniteDimensional ℂ F.range] :
    trace F = (F.toLinearMap.rangeRestrict.domRestrict F.range).charpoly.roots.sum := by
  let R := F.range
  let g : H →L[ℂ] R := F.rangeRestrict
  let i : R →L[ℂ] H := R.subtypeL
  have hg : IsTraceClass g := ExpandedFA.TraceIdeals.TraceNormIdeal.finite_rank_traceClass g
  have htrace := ExpandedFA.TraceIdeals.TraceBasisCyclicity.trace_comp_comm g i hg
  have hleft : i.comp g = F := rfl
  calc
    trace F = trace (g.comp i) := by simpa only [hleft] using htrace
    _ = (g.comp i).toLinearMap.trace ℂ R := trace_eq_linearMap_trace _
    _ = _ := Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)

section FiniteWeylBridge
open Finset

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma padded_selection_perm (F : H →L[ℂ] H) {d : ℕ} (ev : Fin d → ℂ)
    (hev : WeylProducts.Spec.PaddedEigenvalueSelection F ev) (σ : Equiv.Perm (Fin d)) :
    WeylProducts.Spec.PaddedEigenvalueSelection F (fun i => ev (σ i)) := by
  classical
  refine ⟨fun i hi => hev.1 (σ i) hi, ?_⟩
  intro z hz
  apply le_trans _ (hev.2 z hz)
  apply Finset.card_le_card_of_injOn σ
  · intro i hi
    simpa only [Finset.mem_coe, mem_filter, mem_univ, true_and] using hi
  · exact σ.injective.injOn

/-- Extending a finite algebraic selection by zeros preserves all prefix
multiplicity bounds, including when the requested prefix exceeds its length. -/
lemma padded_selection_zero_extend (F : H →L[ℂ] H) {d : ℕ} (ev : Fin d → ℂ)
    (hev : WeylProducts.Spec.PaddedEigenvalueSelection F ev) (n : ℕ) :
    WeylProducts.Spec.PaddedEigenvalueSelection F
      (fun i : Fin n => if h : i.val < d then ev ⟨i.val, h⟩ else 0) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i hi
    dsimp only at hi ⊢
    split_ifs at hi ⊢ with hi'
    · exact hev.1 _ hi
    · exact (hi rfl).elim
  · intro z hz
    apply le_trans _ (hev.2 z hz)
    let s : Finset (Fin n) := univ.filter
      (fun i => (if h : i.val < d then ev ⟨i.val,h⟩ else 0) = z)
    let t : Finset (Fin d) := univ.filter (fun i => ev i = z)
    have hlt (i : s) : i.val.val < d := by
      have hi := (mem_filter.mp i.property).2
      by_contra hn
      simp only [dite_eq_right hn] at hi
      exact hz hi.symm
    let f : s → t := fun i => ⟨⟨i.val.val, hlt i⟩, by
      have hi := (mem_filter.mp i.property).2
      change _ ∈ univ.filter (fun i => ev i = z)
      exact mem_filter.mpr ⟨mem_univ _, by simpa only [dite_eq_left (hlt i)] using hi⟩⟩
    apply Finset.card_le_card_of_injective (f := f)
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun k : t => k.val.val) hij

lemma admissible_zero_extend (F : H →L[ℂ] H) {d : ℕ} (ev : Fin d → ℂ)
    (hev : WeylProducts.Spec.PaddedEigenvalueSelection F ev)
    (hsort : Antitone (fun i => ‖ev i‖)) :
    WeylSumsProducts.Spec.AdmissibleEigenvalueSequence F
      (fun j => if h : j < d then ev ⟨j,h⟩ else 0) := by
  classical
  refine ⟨?_, fun n => padded_selection_zero_extend F ev hev n⟩
  intro i j hij
  by_cases hj : j < d
  · have hi : i < d := lt_of_le_of_lt hij hj
    simpa only [dite_eq_left hi, dite_eq_left hj] using hsort (show (⟨i,hi⟩ : Fin d) ≤ ⟨j,hj⟩ from hij)
  · simp only [dite_eq_right hj, norm_zero]
    exact norm_nonneg _

lemma exists_sorted_selection (F : H →L[ℂ] H) {d : ℕ} (ev : Fin d → ℂ)
    (hev : WeylProducts.Spec.PaddedEigenvalueSelection F ev) :
    ∃ σ : Equiv.Perm (Fin d),
      WeylSumsProducts.Spec.AdmissibleEigenvalueSequence F
        (fun j => if h : j < d then ev (σ ⟨j,h⟩) else 0) := by
  let σ := Tuple.sort (fun i => -‖ev i‖)
  refine ⟨σ, admissible_zero_extend F (fun i => ev (σ i))
    (padded_selection_perm F ev hev σ) ?_⟩
  intro i j hij
  have h := Tuple.monotone_sort (fun i => -‖ev i‖) hij
  dsimp only [Function.comp_apply] at h
  linarith


/-- The finite Weyl estimates do not require an eigenvalue ordering in the
input; sorting and zero padding are internal to this bridge. -/
lemma finite_selection_weyl_bounds [CompleteSpace H] (F : H →L[ℂ] H)
    (hF : TraceClassDefinitions.IsTraceClass F) {d : ℕ} (ev : Fin d → ℂ)
    (hev : WeylProducts.Spec.PaddedEigenvalueSelection F ev) :
    (∑ i, ‖ev i‖) ≤ TraceClassDefinitions.traceNorm F ∧
      ∀ (r : ℝ), 0 ≤ r → (∏ i, (1+r*‖ev i‖)) ≤
        ∏ i ∈ range d, (1+r*TraceClassDefinitions.Spec.singularSequence F i) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_sorted_selection F ev hev
  let e : ℕ → ℂ := fun j => if h : j < d then ev (σ ⟨j,h⟩) else 0
  have hsum : (∑ j ∈ range d, ‖e j‖) = ∑ i, ‖ev i‖ := by
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      _ = ∑ i : Fin d, ‖ev (σ i)‖ := by
        apply sum_congr rfl
        intro i _
        simp only [e, dite_eq_left i.isLt]
      _ = _ := Equiv.sum_comp σ (fun i => ‖ev i‖)
  have hprod (r : ℝ) : (∏ j ∈ range d, (1+r*‖e j‖)) =
      ∏ i, (1+r*‖ev i‖) := by
    rw [← Fin.prod_univ_eq_prod_range]
    calc
      _ = ∏ i : Fin d, (1+r*‖ev (σ i)‖) := by
        apply prod_congr rfl
        intro i _
        simp only [e, dite_eq_left i.isLt]
      _ = _ := Equiv.prod_comp σ (fun i => 1+r*‖ev i‖)
  refine ⟨?_, ?_⟩
  · have hb := WeylSumsProducts.weyl_power_sums H F hF.1 e hσ 1 zero_lt_one d
    simp only [pow_one, hsum] at hb
    exact hb.trans (hF.2.sum_le_tsum (range d)
      (fun i _ => TraceNormIdeal.singular_nonneg F hF.1 i))
  · intro r hr
    have hb := WeylSumsProducts.weyl_finite_shifted_products H F hF.1 e hσ r hr d
    simpa only [hprod] using hb

end FiniteWeylBridge

/-- Finite rank operators have finite characteristic-root lists with exactly
 the trace and Weyl bounds required by the approximation argument. -/
lemma finite_rank_spectral_data {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (F : H →L[ℂ] H)
    (hF : IsTraceClass F) (hfr : FiniteDimensional ℂ F.range) :
    ∃ (d : ℕ) (ev : Fin d → ℂ),
      (∀ i, ev i = 0 ∨ ev i ∈ spectrum ℂ F) ∧
      (∑ i, ev i) = trace F ∧ (∑ i, ‖ev i‖) ≤ traceNorm F ∧
      ∀ (r : ℝ), 0 ≤ r → (∏ i, (1+r*‖ev i‖)) ≤
        ∏ i ∈ range d, (1+r*TraceClassDefinitions.Spec.singularSequence F i) := by
  classical
  letI : FiniteDimensional ℂ F.range := hfr
  let hM : ∀ x ∈ F.range, F.toLinearMap x ∈ F.range := fun x _ => ⟨x, rfl⟩
  let A := F.toLinearMap.restrict hM
  obtain ⟨d, ev, hev, hsum, hcount⟩ := exists_list_enumeration A.charpoly.roots
  have hselect : WeylProducts.Spec.PaddedEigenvalueSelection F ev := by
    refine ⟨?_, ?_⟩
    · intro i _
      exact roots_restrict_hasEigenvalue F.toLinearMap F.range hM (ev i) (hev i)
    · intro z hz
      letI := WeylProducts.compact_maxGenEigenspace_finiteDimensional F hF.1 hz
      rw [hcount]
      exact roots_count_restrict_le F.toLinearMap F.range hM z
  obtain ⟨hnorm, hprod⟩ := finite_selection_weyl_bounds F hF ev hselect
  refine ⟨d, ev, ?_, ?_, hnorm, hprod⟩
  · intro i
    right
    rw [ContinuousLinearMap.spectrum_eq]
    exact (roots_restrict_hasEigenvalue F.toLinearMap F.range hM (ev i) (hev i)).mem_spectrum
  · exact hsum.trans (finite_rank_trace_eq_roots F).symm

/-- The quasinilpotent stage of Lidskii's theorem, for every complex Hilbert
space, including zero and nonseparable spaces. -/
theorem quasinilpotent_trace_zero : Spec.TraceVanishes.{u} := by
  apply trace_zero_of_finite_rank_spectral_data
  intro H _ _ _ F hF hfr
  exact finite_rank_spectral_data F hF hfr

end ExpandedFA.TraceIdeals.QuasinilpotentTraceZero
