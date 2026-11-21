import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.OscillatoryIntegrals
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.RationalIntegrals
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.JordanEstimate
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.ResidueComputation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
open Set Filter MeasureTheory Asymptotics Bornology
open scoped Topology BigOperators

namespace D12Complex.OscillatoryIntegrals

lemma norm_exp_real_frequency (c x : ℝ) :
    ‖Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))‖ = 1 := by
  simp [Complex.norm_exp]

lemma integrable_exp_mul {g : ℝ → ℂ} (hg : Integrable g) (c : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * g x) := by
  apply hg.bdd_mul (c := 1)
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)))).aestronglyMeasurable
  · exact ae_of_all _ (fun x => (norm_exp_real_frequency c x).le)

theorem oscillatory_integrable :
    Specs.D12Complex.Ch08.OscillatoryIntegrals.oscillatory_integrable_type := by
  intro P Q _ hreal hgap c
  exact integrable_exp_mul (RationalIntegrals.rational_integrable_of_degree_gap P Q hreal hgap) c

theorem oscillatory_absolute_tails :
    Specs.D12Complex.Ch08.OscillatoryIntegrals.oscillatory_absolute_tails_type := by
  intro P Q hcoprime hreal hgap c d
  simp_rw [norm_mul, norm_exp_real_frequency, one_mul]
  have hi := (RationalIntegrals.rational_integrable P Q hcoprime hreal hgap).norm
  exact ⟨intervalIntegral_tendsto_integral_Iic d hi.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi d hi.integrableOn tendsto_id⟩

lemma degree_add_one_le_of_lt {a b : WithBot ℕ} (h : a < b) : a + 1 ≤ b := by
  by_cases ha : a = ⊥
  · simp [ha]
  · lift a to ℕ using ha
    lift b to ℕ using ne_bot_of_gt h
    change ((a + 1 : ℕ) : WithBot ℕ) ≤ (b : WithBot ℕ)
    exact WithBot.coe_le_coe.mpr (Nat.add_one_le_iff.mpr (WithBot.coe_lt_coe.mp h))

lemma rational_derivative_degree_gap (P Q : Polynomial ℂ) (hpq : P.degree < Q.degree) :
    (P.derivative * Q - P * Q.derivative).degree + 2 ≤ (Q^2).degree := by
  have hp : P.derivative.degree + 1 ≤ P.degree := by
    by_cases hP : P = 0
    · simp [hP]
    · exact degree_add_one_le_of_lt (Polynomial.degree_derivative_lt hP)
  have hq : Q.derivative.degree + 1 ≤ Q.degree := by
    by_cases hQ : Q = 0
    · simp [hQ]
    · exact degree_add_one_le_of_lt (Polynomial.degree_derivative_lt hQ)
  have hgap := degree_add_one_le_of_lt hpq
  calc
    _ ≤ max (P.derivative * Q).degree (P * Q.derivative).degree + 2 :=
      (by gcongr; exact Polynomial.degree_sub_le _ _)
    _ ≤ Q.degree + Q.degree := by
      rw [← max_add_add_right, max_le_iff]
      constructor
      · calc
          _ ≤ (P.derivative.degree + Q.degree) + 2 :=
            (by gcongr; exact Polynomial.degree_mul_le _ _)
          _ = (P.derivative.degree + 1) + 1 + Q.degree := by change _ + (1 + 1 : WithBot ℕ) = _; ac_rfl
          _ ≤ (P.degree + 1) + Q.degree := by gcongr
          _ ≤ Q.degree + Q.degree := by gcongr
      · calc
          _ ≤ (P.degree + Q.derivative.degree) + 2 :=
            (by gcongr; exact Polynomial.degree_mul_le _ _)
          _ = (P.degree + 1) + (Q.derivative.degree + 1) := by change _ + (1 + 1 : WithBot ℕ) = _; ac_rfl
          _ ≤ Q.degree + Q.degree := add_le_add hgap hq
    _ = _ := by rw [Polynomial.degree_pow]; simp [two_mul]

/-- The derivative quotient is globally integrable on the real axis, even
when the original proper quotient has only linear decay. -/
lemma rational_derivative_integrable (P Q : Polynomial ℂ)
    (hreal : ∀ x : ℝ, Q.eval (x : ℂ) ≠ 0) (hproper : P.degree < Q.degree) :
    Integrable (fun x : ℝ =>
      (P.derivative.eval (x : ℂ) * Q.eval (x : ℂ) -
        P.eval (x : ℂ) * Q.derivative.eval (x : ℂ)) / Q.eval (x : ℂ)^2) := by
  simpa only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow] using
    RationalIntegrals.rational_integrable_of_degree_gap
      (P.derivative * Q - P * Q.derivative) (Q^2)
      (by simpa using fun x => pow_ne_zero 2 (hreal x))
      (rational_derivative_degree_gap P Q hproper)

lemma rational_tendsto_zero (P Q : Polynomial ℂ) (hproper : P.degree < Q.degree) :
    Tendsto (fun x : ℝ => P.eval (x : ℂ) / Q.eval (x : ℂ))
      (cocompact ℝ) (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (cocompact ℝ) (cobounded ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Complex.isometry_ofReal.antilipschitzWith.tendsto_cobounded
  exact (Polynomial.isLittleO_cobounded_of_degree_lt hproper).tendsto_div_nhds_zero.comp ht

lemma exp_mul_tendsto_zero {l : Filter ℝ} {g : ℝ → ℂ}
    (hg : Tendsto g l (𝓝 0)) (c : ℝ) :
    Tendsto (fun x : ℝ => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * g x)
      l (𝓝 0) := by
  apply squeeze_zero_norm (a := fun x => ‖g x‖)
  · intro x
    simp only [norm_mul, norm_exp_real_frequency, one_mul, le_refl]
  · simpa using hg.norm

lemma exp_real_frequency_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (c : ℂ) * (y : ℂ)))
      (Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * (Complex.I * (c : ℂ))) x := by
  convert (((hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * (c : ℂ))).cexp)
    using 1 <;> simp

/-- Integration by parts on an arbitrary finite real interval. -/
lemma oscillatory_integration_by_parts (g g' : ℝ → ℂ)
    (hderiv : ∀ x, HasDerivAt g (g' x) x) (hcont : Continuous g')
    (c a b : ℝ) (hc : c ≠ 0) :
    (∫ x in a..b, Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * g x) =
      (Complex.exp (Complex.I * (c : ℂ) * (b : ℂ)) * g b -
        Complex.exp (Complex.I * (c : ℂ) * (a : ℂ)) * g a -
          ∫ x in a..b, Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * g' x) /
        (Complex.I * (c : ℂ)) := by
  let E : ℝ → ℂ := fun x => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun x => (hderiv x).continuousAt
  have he : Continuous E := by dsimp [E]; fun_prop
  have hprod := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x (_ : x ∈ uIcc a b) => exp_real_frequency_hasDerivAt c x)
    (fun x (_ : x ∈ uIcc a b) => hderiv x)
    ((he.mul_const (Complex.I * (c : ℂ))).intervalIntegrable a b)
    (hcont.intervalIntegrable a b)
  have hint : (∫ x in a..b, E x * (Complex.I * (c : ℂ)) * g x + E x * g' x) =
      (Complex.I * (c : ℂ)) * (∫ x in a..b, E x * g x) +
        (∫ x in a..b, E x * g' x) := by
    rw [intervalIntegral.integral_add
      (f := fun x => E x * (Complex.I * (c : ℂ)) * g x)
      (g := fun x => E x * g' x)
      (((he.mul_const _).mul hg).intervalIntegrable a b)
      ((he.mul hcont).intervalIntegrable a b)]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hint] at hprod
  apply (eq_div_iff (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hc))).mpr
  change (∫ x in a..b, E x * g x) * (Complex.I * (c : ℂ)) = _
  linear_combination hprod

/-- An integrable derivative and vanishing endpoint values give ordinary
oscillatory tails. The two cutoffs have unrelated filters. -/
lemma oscillatory_tails_of_integrable_derivative (g g' : ℝ → ℂ)
    (hderiv : ∀ x, HasDerivAt g (g' x) x) (hcont : Continuous g')
    (hi : Integrable g') (hzero : Tendsto g (cocompact ℝ) (𝓝 0))
    (c : ℝ) (hc : c ≠ 0) (d : ℝ) :
    ∃ Lminus Lplus : ℂ,
      Tendsto (fun a : ℝ => ∫ x in a..d,
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * g x) atBot (𝓝 Lminus) ∧
      Tendsto (fun b : ℝ => ∫ x in d..b,
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * g x) atTop (𝓝 Lplus) := by
  let E : ℝ → ℂ := fun x => Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))
  have hiE := integrable_exp_mul hi c
  have hminus := intervalIntegral_tendsto_integral_Iic d hiE.integrableOn tendsto_id
  have hplus := intervalIntegral_tendsto_integral_Ioi d hiE.integrableOn tendsto_id
  have hzminus := exp_mul_tendsto_zero (hzero.mono_left atBot_le_cocompact) c
  have hzplus := exp_mul_tendsto_zero (hzero.mono_left atTop_le_cocompact) c
  refine ⟨(E d * g d - ∫ x in Iic d, E x * g' x) / (Complex.I * (c : ℂ)),
    (- E d * g d - ∫ x in Ioi d, E x * g' x) / (Complex.I * (c : ℂ)), ?_, ?_⟩
  · have ht := (((tendsto_const_nhds (x := E d * g d)).sub hzminus).sub hminus).div_const
      (Complex.I * (c : ℂ))
    simpa only [E, id_eq, sub_zero, oscillatory_integration_by_parts g g' hderiv hcont c _ _ hc] using ht
  · have ht := ((hzplus.sub (tendsto_const_nhds (x := E d * g d))).sub hplus).div_const
      (Complex.I * (c : ℂ))
    simpa only [E, id_eq, zero_sub, neg_mul,
      oscillatory_integration_by_parts g g' hderiv hcont c _ _ hc] using ht

theorem oscillatory_tails_exist :
    Specs.D12Complex.Ch08.OscillatoryIntegrals.oscillatory_tails_exist_type := by
  intro P Q _ hreal hproper c hc d
  let g : ℝ → ℂ := fun x => P.eval (x : ℂ) / Q.eval (x : ℂ)
  let g' : ℝ → ℂ := fun x =>
    (P.derivative.eval (x : ℂ) * Q.eval (x : ℂ) -
      P.eval (x : ℂ) * Q.derivative.eval (x : ℂ)) / Q.eval (x : ℂ)^2
  have hd : ∀ x, HasDerivAt g (g' x) x := by
    intro x
    exact (((P.hasDerivAt (x : ℂ)).div (Q.hasDerivAt (x : ℂ)) (hreal x)).comp_ofReal)
  have hcont : Continuous g' := by
    apply Continuous.div
    · exact ((P.derivative.continuous.comp Complex.continuous_ofReal).mul
        (Q.continuous.comp Complex.continuous_ofReal)).sub
        ((P.continuous.comp Complex.continuous_ofReal).mul
          (Q.derivative.continuous.comp Complex.continuous_ofReal))
    · exact (Q.continuous.comp Complex.continuous_ofReal).pow 2
    · exact fun x => pow_ne_zero 2 (hreal x)
  exact oscillatory_tails_of_integrable_derivative g g' hd hcont
    (rational_derivative_integrable P Q hreal hproper)
    (rational_tendsto_zero P Q hproper) c hc d

/-- The half-disk arc uses the same oriented curve as Jordan's angular
semicircle; this is the real affine substitution, including its speed. -/
lemma upperArc_integral_eq_semicircle (f : ℂ → ℂ) (r : ℝ)
    (hf : ContinuousOn f (JordanEstimate.upperSemicircle r).trace) :
    (∫ t in (1 : ℝ)..2, f (RationalIntegrals.upperArc r t) *
      (RationalIntegrals.upperArc r t * ((Real.pi : ℂ) * Complex.I))) =
      (JordanEstimate.upperSemicircle r).integral f := by
  let H : ℝ → ℂ := fun t => f (circleMap 0 r t) * (circleMap 0 r t * Complex.I)
  have hpath : (JordanEstimate.upperSemicircle r).integral f = ∫ t in 0..Real.pi, H t := by
    rw [PiecewiseC1Path.integral_congr_representative
      (JordanEstimate.upperSemicircle r) (circleMap 0 r) f hf (by intro t _; rfl)]
    simp only [JordanEstimate.upperSemicircle, H, deriv_circleMap]
    rfl
  have hArc (t : ℝ) : RationalIntegrals.upperArc r t = circleMap 0 r (Real.pi*t - Real.pi) := by
    simp only [RationalIntegrals.upperArc, circleMap, zero_add]
    congr 2
    push_cast
    ring
  have hsub := intervalIntegral.smul_integral_comp_mul_add H (a := 1) (b := 2)
    Real.pi (-Real.pi)
  rw [hpath]
  calc
    _ = Real.pi • (∫ t in (1 : ℝ)..2, H (Real.pi*t + -Real.pi)) := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [hArc]
      simp only [H, Complex.real_smul, sub_eq_add_neg]
      ring
    _ = _ := by simpa only [mul_one, add_neg_cancel, show Real.pi*2 + -Real.pi = Real.pi by ring]
        using hsub

lemma rational_linear_decay (P Q : Polynomial ℂ) (hproper : P.degree < Q.degree) :
    ∃ C > 0, ∃ R > 0, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖P.eval z / Q.eval z‖ ≤ C / ‖z‖ := by
  have hdeg : (P * Polynomial.X).degree ≤ Q.degree :=
    (Polynomial.degree_mul_le _ _).trans (by simpa using degree_add_one_le_of_lt hproper)
  obtain ⟨C, hC, hb⟩ := (Polynomial.isBigO_cobounded_of_degree_le hdeg).exists_pos
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hb.bound
  refine ⟨C, hC, max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  have hn : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one ((le_max_right R 1).trans hz)
  have h := hR ((le_max_left R 1).trans hz)
  simp only [Polynomial.eval_mul, Polynomial.eval_X, norm_mul] at h
  rw [norm_div]
  by_cases hq : Q.eval z = 0
  · simp only [hq, norm_zero, div_zero]
    positivity
  · apply (div_le_iff₀ (norm_pos_iff.mpr hq)).mpr
    calc
      _ ≤ C * ‖Q.eval z‖ / ‖z‖ := (le_div_iff₀ hn).mpr h
      _ = _ := by ring

lemma semicircle_traceSupNorm_le (q : ℂ → ℂ) (C R r : ℝ) (hr : 0 < r) (hR : R ≤ r)
    (hdecay : ∀ z : ℂ, R ≤ ‖z‖ → ‖q z‖ ≤ C / ‖z‖) :
    (JordanEstimate.upperSemicircle r).traceSupNorm q ≤ C / r := by
  apply csSup_le
  · exact ⟨‖q (circleMap 0 r 0)‖, circleMap 0 r 0,
      ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, rfl⟩, rfl⟩
  · rintro y ⟨z, ⟨t, _, rfl⟩, rfl⟩
    have hn : ‖JordanEstimate.upperSemicircle r t‖ = r := by
      change ‖circleMap 0 r t‖ = r
      simp [norm_circleMap_zero, abs_of_pos hr]
    simpa only [hn] using hdecay (JordanEstimate.upperSemicircle r t) (hn.symm ▸ hR)

/-- Symmetric truncations tend to the sum only after both ordinary limits
have been supplied. The splitting point is arbitrary. -/
lemma symmetric_integral_tendsto_of_tails (g : ℝ → ℂ) (hg : Continuous g)
    (d : ℝ) (Lminus Lplus : ℂ)
    (hm : Tendsto (fun a : ℝ => ∫ x in a..d, g x) atBot (𝓝 Lminus))
    (hp : Tendsto (fun b : ℝ => ∫ x in d..b, g x) atTop (𝓝 Lplus)) :
    Tendsto (fun r : ℝ => ∫ x in -r..r, g x) atTop (𝓝 (Lminus + Lplus)) := by
  convert (hm.comp tendsto_neg_atTop_atBot).add hp using 1
  funext r
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (-r) d) (hg.intervalIntegrable d r)).symm

theorem oscillatory_upper_residues :
    Specs.D12Complex.Ch08.OscillatoryIntegrals.oscillatory_upper_residues_type := by
  classical
  intro P Q _ hreal hproper c hc d Lminus Lplus hminus hplus
  let q : ℂ → ℂ := fun z => P.eval z / Q.eval z
  let f : ℂ → ℂ := fun z => Complex.exp (Complex.I * (c : ℂ) * z) * q z
  let A : Finset ℂ := Q.roots.toFinset
  have hQ : Q ≠ 0 := by
    intro h
    simpa [h] using hreal 0
  have hroot (z : ℂ) : z ∈ A ↔ Q.eval z = 0 := by
    simp [A, Polynomial.mem_roots hQ, Polynomial.IsRoot]
  have hnonreal : ∀ z ∈ A, z.im ≠ 0 := by
    intro z hz him
    have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
    exact hreal z.re (he.symm ▸ (hroot z).mp hz)
  have hq (z : ℂ) (hz : z ∉ A) : DifferentiableAt ℂ q z :=
    P.differentiableAt.div Q.differentiableAt (fun h => hz ((hroot z).mpr h))
  have hf : HolomorphicOn (univ \ (A : Set ℂ)) f := by
    refine ⟨isOpen_univ.sdiff A.finite_toSet.isClosed, ?_⟩
    intro z hz
    exact (by fun_prop : DifferentiableAt ℂ
      (fun z : ℂ => Complex.exp (Complex.I * (c : ℂ) * z)) z).mul (hq z hz.2)
  have hlarge : ∀ᶠ r : ℝ in atTop, 0 < r ∧ ∀ a ∈ A, ‖a‖ < r := by
    filter_upwards [eventually_gt_atTop (∑ a ∈ A, ‖a‖)] with r hr
    exact ⟨(Finset.sum_nonneg (fun a _ => norm_nonneg a)).trans_lt hr,
      fun a ha => (Finset.single_le_sum (fun b _ => norm_nonneg b) ha).trans_lt hr⟩
  have heq : ∀ᶠ r : ℝ in atTop,
      (∫ x in -r..r, f (x : ℂ)) +
        (∫ t in (1 : ℝ)..2, f (RationalIntegrals.upperArc r t) *
          (RationalIntegrals.upperArc r t * ((Real.pi : ℂ) * Complex.I))) =
        (2 * Real.pi * Complex.I : ℂ) *
          ∑ a ∈ A.filter (fun a => 0 < a.im), Residue.residue f a := by
    filter_upwards [hlarge] with r hr
    obtain ⟨γ, ht⟩ := IndexComputations.half_disk_boundary_exists 0 1 r (by simp) hr.1
    have havoid : ∀ z ∈ γ.trace, z ∉ A := by
      intro z hz hzA
      have hb := (IndexComputations.half_disk_trace_coordinates γ
        (by simp) hr.1 ht z hz).2
      simp only [sub_zero, div_one] at hb
      rcases hb with hb | hb
      · exact (ne_of_lt (hr.2 z hzA)) hb
      · exact hnonreal z hzA hb
    have hcont : ContinuousOn f γ.trace := fun z hz =>
      (hf.2 z ⟨mem_univ z, havoid z hz⟩).continuousAt.continuousWithinAt
    exact (RationalIntegrals.half_disk_integral_decomposition f r γ ht hcont).symm.trans
      (RationalIntegrals.half_disk_integral_residues A f hf hnonreal r hr.1 hr.2 γ ht)
  obtain ⟨C, _, R, _, hdecay⟩ := rational_linear_decay P Q hproper
  have harc : Tendsto (fun r : ℝ => ∫ t in (1 : ℝ)..2,
      f (RationalIntegrals.upperArc r t) *
        (RationalIntegrals.upperArc r t * ((Real.pi : ℂ) * Complex.I))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun r : ℝ => (Real.pi / c) * (C / r)) ?_ ?_
    · filter_upwards [hlarge, eventually_ge_atTop R] with r hr hR
      have hn (z : ℂ) (hz : z ∈ (JordanEstimate.upperSemicircle r).trace) : ‖z‖ = r := by
        obtain ⟨t, _, rfl⟩ := hz
        change ‖circleMap 0 r t‖ = r
        simp [norm_circleMap_zero, abs_of_pos hr.1]
      have hqarc : ContinuousOn q (JordanEstimate.upperSemicircle r).trace := by
        intro z hz
        apply (hq z ?_).continuousAt.continuousWithinAt
        intro hzA
        exact (ne_of_lt (hr.2 z hzA)) (hn z hz)
      have hfarc : ContinuousOn f (JordanEstimate.upperSemicircle r).trace :=
        (by fun_prop : Continuous (fun z : ℂ =>
          Complex.exp (Complex.I * (c : ℂ) * z))).continuousOn.mul hqarc
      rw [upperArc_integral_eq_semicircle f r hfarc]
      exact (JordanEstimate.jordan_estimate r c hr.1 hc q hqarc).trans
        (mul_le_mul_of_nonneg_left (semicircle_traceSupNorm_le q C R r hr.1 hR hdecay)
          (div_nonneg Real.pi_pos.le hc.le))
    · simpa only [mul_zero] using
        (tendsto_const_nhds (x := Real.pi / c)).mul
          (tendsto_const_nhds.div_atTop tendsto_id :
            Tendsto (fun r : ℝ => C / r) atTop (𝓝 0))
  have hcont : Continuous (fun x : ℝ => f (x : ℂ)) := by
    exact (by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)))).mul
        ((P.continuous.comp Complex.continuous_ofReal).div
          (Q.continuous.comp Complex.continuous_ofReal) hreal)
  have hseg := symmetric_integral_tendsto_of_tails (fun x : ℝ => f (x : ℂ))
    hcont d Lminus Lplus hminus hplus
  have hconst := tendsto_const_nhds.congr' (EventuallyEq.symm heq)
  simpa only [add_zero] using tendsto_nhds_unique (hseg.add harc) hconst

/-- Adding the zero-index terms back into the finite residue theorem. -/
lemma cycle_integral_residues_finite (A : Finset ℂ) (f : ℂ → ℂ) (Γ : IntegralCycle)
    (hf : HolomorphicOn (univ \ (A : Set ℂ)) f) (havoid : Disjoint Γ.trace (A : Set ℂ)) :
    Γ.integral f = (2 * Real.pi * Complex.I : ℂ) *
      ∑ a ∈ A, Γ.index a * Residue.residue f a := by
  classical
  obtain ⟨s, hs, he⟩ := ResidueCycle.residue_theorem univ (A : Set ℂ) f Γ
    isOpen_univ (subset_univ _) (A.finite_toSet.isClosed.preimage continuous_subtype_val)
    A.finite_toSet.isDiscrete hf (subset_univ _) havoid (by simp)
  rw [he]
  congr 1
  apply Finset.sum_subset
  · intro a ha
    exact ((hs a).mp ha).1
  · intro a ha hnot
    have hzero : Γ.index a = 0 := by
      by_contra h
      exact hnot ((hs a).mpr ⟨ha, h⟩)
    simp [hzero]

/-- The lower half-disk is positively oriented by the rotation η = -1.
Its straight diameter therefore runs from r to -r. -/
lemma lower_half_disk_integral_residues (A : Finset ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn (univ \ (A : Set ℂ)) f)
    (hreal : ∀ a ∈ A, a.im ≠ 0) (r : ℝ) (hr : 0 < r)
    (hlarge : ∀ a ∈ A, ‖a‖ < r) (γ : PiecewiseC1Path)
    (ht : Specs.D12Complex.Ch04.IndexComputations.half_disk_traversal γ 0 (-1) r) :
    γ.integral f = (2 * Real.pi * Complex.I : ℂ) *
      ∑ a ∈ A.filter (fun a => a.im < 0), Residue.residue f a := by
  classical
  let Γ : IntegralCycle := ⟨Finsupp.single γ 1, by
    intro δ hδ
    have he : δ = γ := by simpa using hδ
    simpa only [he] using IndexComputations.half_disk_closed γ ht⟩
  have htrace : Γ.trace = γ.trace := IndexOperationsHomotopy.single_trace γ
  have havoid : Disjoint Γ.trace (A : Set ℂ) := by
    rw [htrace]
    apply disjoint_left.mpr
    intro z hz hA
    have hb := (IndexComputations.half_disk_trace_coordinates γ (by simp) hr ht z hz).2
    simp only [sub_zero, div_neg, div_one, Complex.neg_im, neg_eq_zero] at hb
    exact hb.elim (fun h => (ne_of_lt (hlarge z hA)) h) (hreal z hA)
  have hi (z : ℂ) (hz : z ∈ A) : Γ.index z = if z.im < 0 then 1 else 0 := by
    change γ.index z = _
    have hx := IndexComputations.half_disk_index γ 0 (-1) z r (by simp) hr ht
    simp only [sub_zero, div_neg, div_one, Complex.neg_im, neg_pos, neg_lt_zero] at hx
    split_ifs with h
    · exact hx.1 ⟨hlarge z hz, h⟩
    · exact hx.2 (Or.inr (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (hreal z hz))))
  have hΓ : Γ.integral f = γ.integral f := by
    simp [Γ, IntegralCycle.integral, IntegralCycle.chain, IntegralChain.integral]
  rw [← hΓ, cycle_integral_residues_finite A f Γ hf havoid]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hi a ha]
  split_ifs <;> simp

lemma lower_half_disk_integral_decomposition (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (γ : PiecewiseC1Path)
    (ht : Specs.D12Complex.Ch04.IndexComputations.half_disk_traversal γ 0 (-1) r)
    (hf : ContinuousOn f γ.trace) :
    γ.integral f = -((∫ x in -r..r, f (x : ℂ)) +
      ∫ t in (1 : ℝ)..2, f (-RationalIntegrals.upperArc r t) *
        (RationalIntegrals.upperArc r t * ((Real.pi : ℂ) * Complex.I))) := by
  obtain ⟨δ, hd⟩ := IndexComputations.half_disk_boundary_exists 0 1 r (by simp) hr
  have hneg : EqOn γ (fun t => -δ t) (Icc 0 2) := by
    intro t ht'
    dsimp only
    by_cases h : t ≤ 1
    · rw [ht.2.2.1 t ⟨ht'.1, h⟩, hd.2.2.1 t ⟨ht'.1, h⟩]
      simp
    · rw [ht.2.2.2 t ⟨(lt_of_not_ge h).le, ht'.2⟩,
        hd.2.2.2 t ⟨(lt_of_not_ge h).le, ht'.2⟩]
      simp
  have hc : ContinuousOn (fun z => f (-z)) δ.trace := by
    apply hf.comp continuous_neg.continuousOn
    rintro z ⟨t, hti, rfl⟩
    refine ⟨t, ?_, ?_⟩
    · simpa only [ht.1, ht.2.1, hd.1, hd.2.1] using hti
    · exact hneg (by simpa only [hd.1, hd.2.1] using hti)
  have hI : γ.integral f = -δ.integral (fun z => f (-z)) := by
    rw [PiecewiseC1Path.integral_congr_representative γ (fun t => -δ t) f hf
      (by simpa only [ht.1, ht.2.1] using hneg),
      PiecewiseC1Path.integral_congr_representative δ δ (fun z => f (-z)) hc (by intro t _; rfl)]
    simp only [ht.1, ht.2.1, hd.1, hd.2.1]
    have hderiv (t : ℝ) : deriv (fun t => -δ t) t = -deriv (δ : ℝ → ℂ) t :=
      deriv.neg
    simp_rw [hderiv, mul_neg,
      intervalIntegral.integral_neg]
  rw [hI, RationalIntegrals.half_disk_integral_decomposition (fun z => f (-z)) r δ hd hc]
  congr 2
  have hi := intervalIntegral.integral_comp_neg (f := fun x : ℝ => f (x : ℂ))
    (a := -r) (b := r)
  simpa only [Complex.ofReal_neg, neg_neg] using hi

theorem oscillatory_lower_residues :
    Specs.D12Complex.Ch08.OscillatoryIntegrals.oscillatory_lower_residues_type := by
  classical
  intro P Q _ hreal hproper c hc d Lminus Lplus hminus hplus
  let q : ℂ → ℂ := fun z => P.eval z / Q.eval z
  let f : ℂ → ℂ := fun z => Complex.exp (Complex.I * (c : ℂ) * z) * q z
  let A : Finset ℂ := Q.roots.toFinset
  have hQ : Q ≠ 0 := by
    intro h
    simpa [h] using hreal 0
  have hroot (z : ℂ) : z ∈ A ↔ Q.eval z = 0 := by
    simp [A, Polynomial.mem_roots hQ, Polynomial.IsRoot]
  have hnonreal : ∀ z ∈ A, z.im ≠ 0 := by
    intro z hz him
    have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
    exact hreal z.re (he.symm ▸ (hroot z).mp hz)
  have hq (z : ℂ) (hz : z ∉ A) : DifferentiableAt ℂ q z :=
    P.differentiableAt.div Q.differentiableAt (fun h => hz ((hroot z).mpr h))
  have hf : HolomorphicOn (univ \ (A : Set ℂ)) f := by
    refine ⟨isOpen_univ.sdiff A.finite_toSet.isClosed, ?_⟩
    intro z hz
    exact (by fun_prop : DifferentiableAt ℂ
      (fun z : ℂ => Complex.exp (Complex.I * (c : ℂ) * z)) z).mul (hq z hz.2)
  have hlarge : ∀ᶠ r : ℝ in atTop, 0 < r ∧ ∀ a ∈ A, ‖a‖ < r := by
    filter_upwards [eventually_gt_atTop (∑ a ∈ A, ‖a‖)] with r hr
    exact ⟨(Finset.sum_nonneg (fun a _ => norm_nonneg a)).trans_lt hr,
      fun a ha => (Finset.single_le_sum (fun b _ => norm_nonneg b) ha).trans_lt hr⟩
  have heq : ∀ᶠ r : ℝ in atTop,
      (∫ x in -r..r, f (x : ℂ)) +
        (∫ t in (1 : ℝ)..2, f (-RationalIntegrals.upperArc r t) *
          (RationalIntegrals.upperArc r t * ((Real.pi : ℂ) * Complex.I))) =
        -(2 * Real.pi * Complex.I : ℂ) *
          ∑ a ∈ A.filter (fun a => a.im < 0), Residue.residue f a := by
    filter_upwards [hlarge] with r hr
    obtain ⟨γ, ht⟩ := IndexComputations.half_disk_boundary_exists 0 (-1) r (by simp) hr.1
    have havoid (z : ℂ) (hz : z ∈ γ.trace) : z ∉ A := by
      intro hzA
      have hb := (IndexComputations.half_disk_trace_coordinates γ
        (by simp) hr.1 ht z hz).2
      simp only [sub_zero, div_neg, div_one, Complex.neg_im, neg_eq_zero] at hb
      exact hb.elim (fun h => (ne_of_lt (hr.2 z hzA)) h) (hnonreal z hzA)
    have hcont : ContinuousOn f γ.trace := fun z hz =>
      (hf.2 z ⟨mem_univ z, havoid z hz⟩).continuousAt.continuousWithinAt
    have h1 := lower_half_disk_integral_decomposition f r hr.1 γ ht hcont
    have h2 := lower_half_disk_integral_residues A f hf hnonreal r hr.1 hr.2 γ ht
    linear_combination h1 - h2
  obtain ⟨C, _, R, _, hdecay⟩ := rational_linear_decay P Q hproper
  have harc : Tendsto (fun r : ℝ => ∫ t in (1 : ℝ)..2,
      f (-RationalIntegrals.upperArc r t) *
        (RationalIntegrals.upperArc r t * ((Real.pi : ℂ) * Complex.I))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun r : ℝ => (Real.pi / (-c)) * (C / r)) ?_ ?_
    · filter_upwards [hlarge, eventually_ge_atTop R] with r hr hR
      let qn : ℂ → ℂ := fun z => q (-z)
      have hn (z : ℂ) (hz : z ∈ (JordanEstimate.upperSemicircle r).trace) : ‖z‖ = r := by
        obtain ⟨t, _, rfl⟩ := hz
        change ‖circleMap 0 r t‖ = r
        simp [norm_circleMap_zero, abs_of_pos hr.1]
      have hqnarc : ContinuousOn qn (JordanEstimate.upperSemicircle r).trace := by
        intro z hz
        apply ((hq (-z) ?_).continuousAt.comp continuous_neg.continuousAt).continuousWithinAt
        intro hzA
        exact (ne_of_lt (hr.2 (-z) hzA)) (by simpa only [norm_neg] using hn z hz)
      have hfnarc : ContinuousOn (fun z => f (-z)) (JordanEstimate.upperSemicircle r).trace :=
        (by fun_prop : Continuous (fun z : ℂ =>
          Complex.exp (Complex.I * (c : ℂ) * -z))).continuousOn.mul hqnarc
      rw [upperArc_integral_eq_semicircle (fun z => f (-z)) r hfnarc]
      have he : (fun z => f (-z)) =
          (fun z => Complex.exp (Complex.I * ((-c : ℝ) : ℂ) * z) * qn z) := by
        funext z
        dsimp [f, qn]
        congr 2
        push_cast
        ring
      rw [he]
      apply (JordanEstimate.jordan_estimate r (-c) hr.1 (neg_pos.mpr hc) qn hqnarc).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg Real.pi_pos.le (neg_pos.mpr hc).le)
      apply semicircle_traceSupNorm_le qn C R r hr.1 hR
      intro z hz
      simpa only [norm_neg] using hdecay (-z) (by simpa only [norm_neg] using hz)
    · simpa only [mul_zero] using
        (tendsto_const_nhds (x := Real.pi / (-c))).mul
          (tendsto_const_nhds.div_atTop tendsto_id :
            Tendsto (fun r : ℝ => C / r) atTop (𝓝 0))
  have hcont : Continuous (fun x : ℝ => f (x : ℂ)) := by
    exact (by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)))).mul
        ((P.continuous.comp Complex.continuous_ofReal).div
          (Q.continuous.comp Complex.continuous_ofReal) hreal)
  have hseg := symmetric_integral_tendsto_of_tails (fun x : ℝ => f (x : ℂ))
    hcont d Lminus Lplus hminus hplus
  have hconst := tendsto_const_nhds.congr' (EventuallyEq.symm heq)
  simpa only [add_zero] using tendsto_nhds_unique (hseg.add harc) hconst

/-- The exponential Cauchy kernel, first for a nonnegative frequency.
The zero frequency uses the absolutely convergent rational formula. -/
lemma exponential_quadratic_kernel (b : ℝ) (hb : 0 < b) (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun x : ℝ =>
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) / ((x : ℂ)^2 + (b : ℂ)^2)) ∧
    (∫ x : ℝ, Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) /
      ((x : ℂ)^2 + (b : ℂ)^2)) =
        ((Real.pi / b) * Real.exp (-b*c) : ℝ) := by
  classical
  let Q : Polynomial ℂ := Polynomial.X^2 + Polynomial.C ((b : ℂ)^2)
  let f : ℂ → ℂ := fun z => Complex.exp (Complex.I * (c : ℂ) * z) / Q.eval z
  have hdeg : Q.degree = 2 := Polynomial.degree_X_pow_add_C (by norm_num) _
  have hQ : Q ≠ 0 := by
    intro h
    simp [h] at hdeg
  have hreal (x : ℝ) : Q.eval (x : ℂ) ≠ 0 := by
    have hx : (0 : ℝ) < x^2 + b^2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos hb)
    simpa only [Q, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, ← Complex.ofReal_pow, ← Complex.ofReal_add, ne_eq,
      Complex.ofReal_eq_zero] using hx.ne'
  have hgap : (1 : Polynomial ℂ).degree + 2 ≤ Q.degree := by rw [hdeg]; norm_num
  have hproper : (1 : Polynomial ℂ).degree < Q.degree := by rw [hdeg]; norm_num
  have hi : Integrable (fun x : ℝ => f (x : ℂ)) := by
    simpa only [f, Polynomial.eval_one, one_div, div_eq_mul_inv, one_mul, id_eq] using
      oscillatory_integrable 1 Q (isCoprime_one_left) hreal hgap c
  have hformula : (∫ x : ℝ, f (x : ℂ)) =
      (2 * Real.pi * Complex.I : ℂ) *
        ∑ a ∈ Q.roots.toFinset.filter (fun a => 0 < a.im), Residue.residue f a := by
    by_cases hc0 : c = 0
    · simpa only [f, hc0, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
        Polynomial.eval_one] using
        RationalIntegrals.rational_integral_residues 1 Q isCoprime_one_left hreal hgap
    · have hpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have hsum := oscillatory_upper_residues 1 Q isCoprime_one_left hreal hproper c hpos 0
        (∫ x in Iic (0 : ℝ), f (x : ℂ)) (∫ x in Ioi (0 : ℝ), f (x : ℂ))
        (by simpa only [f, Polynomial.eval_one, one_div, div_eq_mul_inv, one_mul, id_eq] using
          intervalIntegral_tendsto_integral_Iic (0 : ℝ) hi.integrableOn tendsto_id)
        (by simpa only [f, Polynomial.eval_one, one_div, div_eq_mul_inv, one_mul, id_eq] using
          intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi.integrableOn tendsto_id)
      rw [intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn] at hsum
      simpa only [f, Polynomial.eval_one, one_div, div_eq_mul_inv, one_mul, id_eq] using hsum
  let a : ℂ := Complex.I * (b : ℂ)
  have haim : a.im = b := by simp [a]
  have hfactor (z : ℂ) : Q.eval z = (z-a)*(z+a) := by
    simp only [Q, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, a]
    ring_nf
    simp [Complex.I_sq]
  have hfilter : Q.roots.toFinset.filter (fun z => 0 < z.im) = {a} := by
    ext z
    simp only [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hQ,
      Polynomial.IsRoot, hfactor, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h | h, hz⟩
      · exact h
      · subst z
        simp only [Complex.neg_im, haim] at hz
        linarith
    · rintro rfl
      exact ⟨Or.inl rfl, by simpa only [haim] using hb⟩
  have hderiv : deriv (fun z : ℂ => Q.eval z) a = 2*a := by
    rw [(Q.hasDerivAt a).deriv]
    simp [Q, Polynomial.derivative_pow]
  have ha : a ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne')
  have hres : Residue.residue f a = Complex.exp (-(b*c : ℝ)) / (2*a) := by
    have heval : Q.eval a = 0 := by simp [hfactor]
    have hnz : deriv (fun z : ℂ => Q.eval z) a ≠ 0 := by
      rw [hderiv]
      exact mul_ne_zero (by norm_num) ha
    have h := ResidueComputation.residue_simple_quotient f
      (fun z => Complex.exp (Complex.I * (c : ℂ) * z)) (fun z => Q.eval z) a univ
      (mem_univ a) ⟨isOpen_univ, by intro z _; fun_prop⟩
      ⟨isOpen_univ, by intro z _; exact Q.differentiableAt⟩ heval hnz (by exact Eventually.of_forall fun z => rfl)
    rw [h, hderiv]
    congr 2
    dsimp [a]
    push_cast
    calc
      _ = Complex.I^2 * ((b : ℂ)*(c : ℂ)) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have he := hformula
  rw [hfilter, Finset.sum_singleton, hres] at he
  have hs : (2 * Real.pi * Complex.I : ℂ) *
      (Complex.exp (-(b*c : ℝ)) / (2*a)) = ((Real.pi / b) * Real.exp (-b*c) : ℝ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    dsimp [a]
    push_cast
    field_simp [hb.ne']
  rw [hs] at he
  simpa only [f, Q, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] using And.intro hi he

theorem cosine_kernel : Specs.D12Complex.Ch08.OscillatoryIntegrals.cosine_kernel_type := by
  intro b hb c
  obtain ⟨hi, he⟩ := exponential_quadratic_kernel b hb |c| (abs_nonneg c)
  have hre (x : ℝ) :
      (Complex.exp (Complex.I * ((|c| : ℝ) : ℂ) * (x : ℂ)) /
        ((x : ℂ)^2 + (b : ℂ)^2)).re = Real.cos (c*x) / (x^2+b^2) := by
    have hcos : Real.cos (|c| * x) = Real.cos (c*x) := by
      rcases le_total 0 c with hc | hc
      · rw [abs_of_nonneg hc]
      · rw [abs_of_nonpos hc, neg_mul, Real.cos_neg]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add]
    simp only [Complex.div_ofReal_re, Complex.exp_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, mul_zero, sub_zero, zero_add, Real.exp_zero]
    simpa only [one_mul] using congrArg (fun y => y / (x^2+b^2)) hcos
  refine ⟨?_, ?_⟩
  · have hri : Integrable (fun x : ℝ =>
        (Complex.exp (Complex.I * ((|c| : ℝ) : ℂ) * (x : ℂ)) /
          ((x : ℂ)^2 + (b : ℂ)^2)).re) := hi.re
    simpa only [hre] using hri
  · have h := integral_re hi
    change (∫ x : ℝ, (Complex.exp (Complex.I * ((|c| : ℝ) : ℂ) * (x : ℂ)) /
      ((x : ℂ)^2 + (b : ℂ)^2)).re) =
        (∫ x : ℝ, Complex.exp (Complex.I * ((|c| : ℝ) : ℂ) * (x : ℂ)) /
          ((x : ℂ)^2 + (b : ℂ)^2)).re at h
    rw [he, Complex.ofReal_re] at h
    simpa only [hre] using h

end D12Complex.OscillatoryIntegrals
