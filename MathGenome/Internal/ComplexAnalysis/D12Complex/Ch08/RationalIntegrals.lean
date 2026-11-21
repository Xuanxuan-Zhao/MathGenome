import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.RationalIntegrals
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Topology.Algebra.Polynomial
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexComputations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.ResidueCycle
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
open Set Filter MeasureTheory Asymptotics Bornology
open scoped Topology BigOperators

namespace D12Complex.RationalIntegrals

theorem cauchy_kernel_integrable :
    Specs.D12Complex.Ch08.RationalIntegrals.cauchy_kernel_integrable_type :=
  integrable_inv_one_add_sq

theorem cauchy_kernel_integral :
    Specs.D12Complex.Ch08.RationalIntegrals.cauchy_kernel_integral_type :=
  integral_univ_inv_one_add_sq

/-- The degree gap gives a comparison with the real Cauchy kernel. -/
theorem rational_isBigO_cauchy_kernel (P Q : Polynomial ℂ)
    (hgap : P.degree + 2 ≤ Q.degree) :
    (fun x : ℝ => P.eval (x : ℂ) / Q.eval (x : ℂ))
      =O[cocompact ℝ] (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  have hdeg : (P * (1 + Polynomial.X ^ 2)).degree ≤ Q.degree := by
    apply (Polynomial.degree_mul_le _ _).trans
    apply le_trans _ hgap
    gcongr
    exact (Polynomial.degree_add_le _ _).trans (by simp)
  have hpoly := Polynomial.isBigO_cobounded_of_degree_le hdeg
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (cocompact ℝ) (cobounded ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Complex.isometry_ofReal.antilipschitzWith.tendsto_cobounded
  have hb := hpoly.comp_tendsto ht
  obtain ⟨C, hC, hbound⟩ := hb.exists_pos
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [hbound.bound] with x hx
  have hkernel : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hn : ‖(1 : ℂ) + (x : ℂ)^2‖ = 1 + x^2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkernel]
  simp only [Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, norm_mul, hn] at hx
  rw [norm_div, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hkernel)]
  by_cases hq : Q.eval (x : ℂ) = 0
  · simp only [hq, norm_zero, div_zero]
    positivity
  · have hqnorm := norm_pos_iff.mpr hq
    apply (div_le_iff₀ hqnorm).mpr
    calc
      _ ≤ C * ‖Q.eval (x : ℂ)‖ / (1 + x^2) := (le_div_iff₀ hkernel).mpr hx
      _ = _ := by ring

theorem rational_integrable_of_degree_gap (P Q : Polynomial ℂ)
    (hreal : ∀ x : ℝ, Q.eval (x : ℂ) ≠ 0)
    (hgap : P.degree + 2 ≤ Q.degree) :
    Integrable (fun x : ℝ => P.eval (x : ℂ) / Q.eval (x : ℂ)) := by
  have hcont : Continuous (fun x : ℝ => P.eval (x : ℂ) / Q.eval (x : ℂ)) :=
    (P.continuous.comp Complex.continuous_ofReal).div
      (Q.continuous.comp Complex.continuous_ofReal) hreal
  exact hcont.locallyIntegrable.integrable_of_isBigO_cocompact
    (rational_isBigO_cauchy_kernel P Q hgap)
    (integrable_inv_one_add_sq.integrableAtFilter _)

theorem rational_integrable :
    Specs.D12Complex.Ch08.RationalIntegrals.rational_integrable_type := by
  intro P Q _ hreal hgap
  exact rational_integrable_of_degree_gap P Q hreal hgap

theorem rational_improper_tails :
    Specs.D12Complex.Ch08.RationalIntegrals.rational_improper_tails_type := by
  intro P Q hcoprime hreal hgap c
  have hi := rational_integrable P Q hcoprime hreal hgap
  exact ⟨intervalIntegral_tendsto_integral_Iic c hi.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi c hi.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Iic c hi.norm.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi c hi.norm.integrableOn tendsto_id,
    (intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn).symm⟩

/-- Uniform quadratic decay in every complex direction, not merely on ℝ. -/
theorem rational_quadratic_decay (P Q : Polynomial ℂ)
    (hgap : P.degree + 2 ≤ Q.degree) :
    ∃ C > 0, ∃ R > 0, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖P.eval z / Q.eval z‖ ≤ C / ‖z‖^2 := by
  have hdeg : (P * Polynomial.X^2).degree ≤ Q.degree := by
    apply (Polynomial.degree_mul_le _ _).trans
    simpa using hgap
  obtain ⟨C, hC, hb⟩ := (Polynomial.isBigO_cobounded_of_degree_le hdeg).exists_pos
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hb.bound
  refine ⟨C, hC, max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  have hn : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one ((le_max_right R 1).trans hz)
  have h := hR ((le_max_left R 1).trans hz)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul,
    norm_pow] at h
  rw [norm_div]
  by_cases hq : Q.eval z = 0
  · simp only [hq, norm_zero, div_zero]
    positivity
  · apply (div_le_iff₀ (norm_pos_iff.mpr hq)).mpr
    calc
      _ ≤ C * ‖Q.eval z‖ / ‖z‖^2 := (le_div_iff₀ (sq_pos_of_pos hn)).mpr h
      _ = _ := by ring

open Specs.D12Complex.Ch04.IndexComputations (half_disk_traversal)

/-- The finite-radius residue identity for the actual half-disk contour. -/
theorem half_disk_integral_residues (A : Finset ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn (Set.univ \ (A : Set ℂ)) f)
    (hreal : ∀ a ∈ A, a.im ≠ 0)
    (r : ℝ) (hr : 0 < r) (hlarge : ∀ a ∈ A, ‖a‖ < r)
    (γ : PiecewiseC1Path) (ht : half_disk_traversal γ 0 1 r) :
    γ.integral f = (2 * Real.pi * Complex.I : ℂ) *
      ∑ a ∈ A.filter (fun a => 0 < a.im), Residue.residue f a := by
  classical
  let Γ : IntegralCycle := ⟨Finsupp.single γ 1, by
    intro δ hδ
    have hδγ : δ = γ := by simpa using hδ
    subst δ
    exact IndexComputations.half_disk_closed γ ht⟩
  have htrace : Γ.trace = γ.trace := by
    exact IndexOperationsHomotopy.single_trace γ
  have havoid : Disjoint Γ.trace (A : Set ℂ) := by
    apply Set.disjoint_left.mpr
    intro a ha haA
    rw [htrace] at ha
    have h := (IndexComputations.half_disk_trace_coordinates γ
      (by simp) hr ht a ha).2
    simp only [sub_zero, div_one] at h
    rcases h with h | h
    · exact (ne_of_lt (hlarge a haA)) h
    · exact hreal a haA h
  have hindex (a : ℂ) (ha : a ∈ A) :
      Γ.index a = if 0 < a.im then 1 else 0 := by
    change γ.index a = _
    split_ifs with h
    · exact (IndexComputations.half_disk_index γ 0 1 a r (by simp) hr ht).1
        (by simpa using And.intro (hlarge a ha) h)
    · exact (IndexComputations.half_disk_index γ 0 1 a r (by simp) hr ht).2
        (Or.inr (by simpa using lt_of_le_of_ne (le_of_not_gt h) (hreal a ha)))
  obtain ⟨s, hs, he⟩ := ResidueCycle.residue_theorem Set.univ (A : Set ℂ) f Γ
    isOpen_univ (subset_univ _) (A.finite_toSet.isClosed.preimage continuous_subtype_val)
    A.finite_toSet.isDiscrete hf (subset_univ _) havoid (by simp)
  have heq : s = A.filter (fun a => 0 < a.im) := by
    ext a
    rw [hs a, Finset.mem_filter]
    constructor
    · rintro ⟨ha, hi⟩
      exact ⟨ha, by simpa [hindex a ha] using hi⟩
    · rintro ⟨ha, hi⟩
      exact ⟨ha, by simp [hindex a ha, hi]⟩
  have hΓint : Γ.integral f = γ.integral f := by
    simp [Γ, IntegralCycle.integral, IntegralCycle.chain, IntegralChain.integral]
  rw [hΓint, heq] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have ham := Finset.mem_filter.mp ha
  rw [hindex a ham.1, ite_eq_left ham.2, one_mul]

/-- Standard parametrization of the upper arc, with parameter interval [1,2]. -/
def upperArc (r t : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (((Real.pi * (t - 1) : ℝ) : ℂ) * Complex.I)

lemma upperArc_hasDerivAt (r t : ℝ) :
    HasDerivAt (upperArc r) (upperArc r t * ((Real.pi : ℂ) * Complex.I)) t := by
  convert (((((hasDerivAt_id t).sub_const 1).const_mul Real.pi).ofReal_comp.mul_const
    Complex.I).cexp.const_mul (r : ℂ)) using 1 <;>
    first | (funext y; simp [upperArc, mul_assoc]) | simp [upperArc, mul_assoc]

lemma norm_upperArc (r t : ℝ) (hr : 0 ≤ r) : ‖upperArc r t‖ = r := by
  simp [upperArc, Complex.norm_exp, abs_of_nonneg hr]

/-- Subdivision and the real affine substitution identify the straight piece
with the ordinary real-axis integral. -/
theorem half_disk_integral_decomposition (f : ℂ → ℂ) (r : ℝ)
    (γ : PiecewiseC1Path) (ht : half_disk_traversal γ 0 1 r)
    (hf : ContinuousOn f γ.trace) :
    γ.integral f = (∫ x in -r..r, f (x : ℂ)) +
      ∫ t in (1 : ℝ)..2, f (upperArc r t) *
        (upperArc r t * ((Real.pi : ℂ) * Complex.I)) := by
  obtain ⟨γ₁, γ₂, ha₁, hb₁, ha₂, hb₂, h₁, h₂, he⟩ :=
    PiecewiseC1Path.subdivision γ 1 f (by rw [ht.1, ht.2.1]; norm_num) hf
  have hf₁ := PiecewiseC1Path.continuousOn_trace_of_restriction γ γ₁ f hf
    (by rw [ha₁]) (by rw [hb₁, ht.2.1]; norm_num)
    (by simpa [ha₁, hb₁] using h₁)
  have hf₂ := PiecewiseC1Path.continuousOn_trace_of_restriction γ γ₂ f hf
    (by rw [ha₂, ht.1]; norm_num) (by rw [hb₂])
    (by simpa [ha₂, hb₂] using h₂)
  have hl : EqOn γ₁ (fun t : ℝ => ((r * (2*t-1) : ℝ) : ℂ))
      (Icc γ₁.path.a γ₁.path.b) := by
    intro t hti
    rw [ha₁, ht.1, hb₁] at hti
    rw [h₁ (by simpa [ht.1] using hti), ht.2.2.1 t hti]
    simp
  have hu : EqOn γ₂ (upperArc r) (Icc γ₂.path.a γ₂.path.b) := by
    intro t hti
    rw [ha₂, hb₂, ht.2.1] at hti
    rw [h₂ (by simpa [ht.2.1] using hti), ht.2.2.2 t hti]
    simp [upperArc]
  have hd (t : ℝ) : deriv (fun t : ℝ => ((r*(2*t-1) : ℝ) : ℂ)) t = (2*r : ℝ) := by
    convert ((((hasDerivAt_id t).const_mul 2).sub_const 1).const_mul r).ofReal_comp.deriv
      using 1 <;> simp [mul_comm]
  rw [he, PiecewiseC1Path.integral_congr_representative γ₁ _ f hf₁ hl,
    PiecewiseC1Path.integral_congr_representative γ₂ _ f hf₂ hu,
    ha₁, ht.1, hb₁, ha₂, hb₂, ht.2.1]
  simp_rw [hd, (upperArc_hasDerivAt r _).deriv]
  congr 1
  have hg : (fun t : ℝ => f ((r*(2*t-1) : ℝ) : ℂ) * (2*r : ℝ)) =
      fun t : ℝ => (2*r) • f (((2*r)*t + (-r) : ℝ) : ℂ) := by
    funext t
    rw [show r * (2*t-1) = (2*r)*t + (-r) from by ring,
      Complex.real_smul, mul_comm]
  rw [hg, intervalIntegral.integral_smul]
  have hs := intervalIntegral.smul_integral_comp_mul_add
    (fun x : ℝ => f (x : ℂ)) (a := 0) (b := 1) (2*r) (-r)
  simpa only [mul_zero, zero_add, mul_one, show 2*r + -r = r from by ring] using hs

/-- The ML estimate on the explicit arc gives a vanishing O(1/r) bound. -/
theorem upperArc_integral_bound (f : ℂ → ℂ) (C R r : ℝ)
    (hr : 0 < r) (hR : R ≤ r)
    (hdecay : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C / ‖z‖^2) :
    ‖∫ t in (1 : ℝ)..2, f (upperArc r t) *
      (upperArc r t * ((Real.pi : ℂ) * Complex.I))‖ ≤ C * Real.pi / r := by
  have hb : ∀ t : ℝ, t ∈ Set.uIoc 1 2 →
      ‖f (upperArc r t) * (upperArc r t * ((Real.pi : ℂ) * Complex.I))‖ ≤
        C * Real.pi / r := by
    intro t _
    rw [norm_mul, norm_mul, norm_mul, norm_upperArc r t hr.le, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
    have hdec : ‖f (upperArc r t)‖ ≤ C / r^2 := by
      simpa only [norm_upperArc r t hr.le] using
        (hdecay (upperArc r t) (by simpa only [norm_upperArc r t hr.le] using hR))
    calc
      _ ≤ (C / r^2) * (r * Real.pi) := mul_le_mul_of_nonneg_right hdec (by positivity)
      _ = _ := by field_simp [hr.ne']
  simpa only [show |(2 : ℝ) - 1| = 1 from by norm_num, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

/-- Rational integration over the real axis. The contour identity is used at
large radii only; both ordinary tails were established independently above. -/
theorem rational_integral_residues :
    Specs.D12Complex.Ch08.RationalIntegrals.rational_integral_residues_type := by
  classical
  intro P Q hcoprime hreal hgap
  let f : ℂ → ℂ := fun z => P.eval z / Q.eval z
  let A : Finset ℂ := Q.roots.toFinset
  have hQ : Q ≠ 0 := by
    intro h
    simpa [h] using hreal 0
  have hroot (a : ℂ) : a ∈ A ↔ Q.eval a = 0 := by
    simp [A, Polynomial.mem_roots hQ, Polynomial.IsRoot]
  have hnonreal : ∀ a ∈ A, a.im ≠ 0 := by
    intro a ha him
    have he : (a.re : ℂ) = a := by
      apply Complex.ext <;> simp [him]
    exact hreal a.re (he.symm ▸ (hroot a).mp ha)
  have hf : HolomorphicOn (Set.univ \ (A : Set ℂ)) f := by
    refine ⟨isOpen_univ.sdiff A.finite_toSet.isClosed, ?_⟩
    intro z hz
    have hqz : Q.eval z ≠ 0 := fun h => hz.2 ((hroot z).mpr h)
    exact P.differentiableAt.div Q.differentiableAt hqz
  have hlarge : ∀ᶠ r : ℝ in atTop, 0 < r ∧ ∀ a ∈ A, ‖a‖ < r := by
    filter_upwards [eventually_gt_atTop (∑ a ∈ A, ‖a‖)] with r hr
    refine ⟨(Finset.sum_nonneg (fun a _ => norm_nonneg a)).trans_lt hr, ?_⟩
    intro a ha
    exact (Finset.single_le_sum (fun b _ => norm_nonneg b) ha).trans_lt hr
  have heq : ∀ᶠ r : ℝ in atTop,
      (∫ x in -r..r, f (x : ℂ)) +
        (∫ t in (1 : ℝ)..2, f (upperArc r t) *
          (upperArc r t * ((Real.pi : ℂ) * Complex.I))) =
        (2 * Real.pi * Complex.I : ℂ) *
          ∑ a ∈ A.filter (fun a => 0 < a.im), Residue.residue f a := by
    filter_upwards [hlarge] with r hr
    obtain ⟨γ, ht⟩ := IndexComputations.half_disk_boundary_exists 0 1 r (by simp) hr.1
    have havoid : ∀ z ∈ γ.trace, z ∉ (A : Set ℂ) := by
      intro z hz hzA
      have hb := (IndexComputations.half_disk_trace_coordinates γ
        (by simp) hr.1 ht z hz).2
      simp only [sub_zero, div_one] at hb
      rcases hb with hb | hb
      · exact (ne_of_lt (hr.2 z hzA)) hb
      · exact hnonreal z hzA hb
    have hc : ContinuousOn f γ.trace := fun z hz =>
      (hf.2 z ⟨mem_univ z, havoid z hz⟩).continuousAt.continuousWithinAt
    exact (half_disk_integral_decomposition f r γ ht hc).symm.trans
      (half_disk_integral_residues A f hf hnonreal r hr.1 hr.2 γ ht)
  obtain ⟨C, _, R, _, hdecay⟩ := rational_quadratic_decay P Q hgap
  have harc : Tendsto (fun r : ℝ =>
      ∫ t in (1 : ℝ)..2, f (upperArc r t) *
        (upperArc r t * ((Real.pi : ℂ) * Complex.I))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun r : ℝ => C * Real.pi / r) ?_
      (tendsto_const_nhds.div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop R, eventually_gt_atTop 0] with r hR hr
    exact upperArc_integral_bound f C R r hr hR hdecay
  have hseg := intervalIntegral_tendsto_integral
    (rational_integrable P Q hcoprime hreal hgap) tendsto_neg_atTop_atBot tendsto_id
  have hconst := tendsto_const_nhds.congr' (EventuallyEq.symm heq)
  simpa only [add_zero] using tendsto_nhds_unique (hseg.add harc) hconst

end D12Complex.RationalIntegrals
