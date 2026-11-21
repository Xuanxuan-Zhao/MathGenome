import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.Failure
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.UniformImproper
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpProperties
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace SingleVariableAnalysis.ParameterFailure
open Set Filter
open scoped Topology BigOperators
open SingleVariableAnalysis.Riemann
open Specs.SingleVariableAnalysis.Ch14.Failure
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint

abbrev integrand := integrandValue
abbrev limitFunction := limitValue

/-- The elementary continuous-derivative FTC, proved with the project's tagged
sums. On each cell MVT supplies a tag with exactly the primitive increment;
uniform continuity compares arbitrary tags with these tags. -/
theorem fineTaggedLimit_of_primitive {a b : ℝ} (hab : a < b)
    (F f : ℝ → ℝ) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) :
    FineTaggedLimit f a b (F b - F a) := by
  intro ε hε
  have hη : 0 < ε / (2 * (b - a)) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) _ hη
  refine ⟨δ, hδ, fun P ξ hP => ?_⟩
  have hm (i : Fin P.n) : ∃ c ∈ Ioo (P.point i.castSucc) (P.point i.succ),
      f c * cellLength P i = F (P.point i.succ) - F (P.point i.castSucc) := by
    have hs : Icc (P.point i.castSucc) (P.point i.succ) ⊆ Icc a b :=
      cell_subset_interval P i
    obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope F f
      (P.strictMono (Fin.castSucc_lt_succ (i := i)))
      (fun x hx => (hd x (hs hx)).continuousAt.continuousWithinAt)
      (fun x hx => hd x (hs (Ioo_subset_Icc_self hx)))
    exact ⟨c, hc, (eq_div_iff (ne_of_gt (cell_positive P i))).mp he⟩
  choose c hc he using hm
  have htel : (∑ i : Fin P.n, f (c i) * cellLength P i) = F b - F a := by
    simp_rw [he]
    simpa only [P.first, P.last] using sum_cell_differences (fun i => F (P.point i))
  have heq : taggedSum P ξ f - (F b - F a) =
      ∑ i : Fin P.n, (f (ξ i) - f (c i)) * cellLength P i := by
    rw [← htel]
    simp only [taggedSum, S.sumValue, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, Real.norm_eq_abs]
  calc
    _ ≤ ∑ i : Fin P.n, |(f (ξ i) - f (c i)) * cellLength P i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin P.n, (ε / (2 * (b - a))) * cellLength P i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_pos (cell_positive P i)]
      apply mul_le_mul_of_nonneg_right _ (cell_positive P i).le
      apply (hu (ξ i) (cell_subset_interval P i (ξ i).property)
        (c i) (cell_subset_interval P i (Ioo_subset_Icc_self (hc i))) ?_).le
      rw [Real.dist_eq]
      have ht := (ξ i).property
      have hi := hc i
      have hdist : |(ξ i : ℝ) - c i| ≤ cellLength P i := by
        apply abs_le.mpr
        dsimp [cellLength, S.lengthValue]
        constructor <;> linarith [ht.1, ht.2, hi.1, hi.2]
      exact hdist.trans_lt ((cellLength_le_mesh P i).trans_lt hP)
    _ = ε / 2 := by rw [← Finset.mul_sum, sum_cellLength]; field_simp
    _ < ε := half_lt_self hε

private theorem exponential_eq (x : ℝ) :
    Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue x = Real.exp x :=
  expSeries_eq_realExp x

private theorem continuous_integrand : Continuous (fun p : ℝ × ℝ => integrand p.1 p.2) := by
  simp only [integrand, integrandValue, exponential_eq]
  fun_prop

theorem joint_continuity : jointContinuity := by
  intro X T _ _
  exact continuous_integrand.continuousOn

theorem finite_formula : finiteFormula := by
  intro R t hR _
  let F : ℝ → ℝ := fun x => 1 - Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue (-t * x)
  have hd (x : ℝ) : HasDerivAt F (integrand x t) x := by
    have h := ((real_expSeries_derivative (-t * x)).comp x
      ((hasDerivAt_id x).const_mul (-t))).const_sub 1
    convert h using 1 <;> first | rfl | dsimp [integrand, integrandValue]; ring
  have hc : ContinuousOn (fun x => integrand x t) (Icc 0 R) :=
    (continuous_integrand.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hb : BoundedOnInterval (fun x => integrand x t) 0 R := by
    exact ⟨(isCompact_Icc.image_of_continuousOn hc).bddBelow, (isCompact_Icc.image_of_continuousOn hc).bddAbove⟩
  rcases hR.eq_or_lt with rfl | hR
  · refine ⟨realIntegrable_degenerate _ _, ?_⟩
    calc
      _ = 0 := realIntegral_degenerate _ _ _
      _ = _ := by simp [exponential_eq]
  · obtain ⟨h, he⟩ := (real_tagged_equivalence _ hR.le hb _).mpr
      (fineTaggedLimit_of_primitive hR F _ hc (fun x _ => hd x))
    refine ⟨h, ?_⟩
    simpa [F, exponential_eq] using he


theorem zero_values : zeroValues := by
  refine ⟨fun x => by simp [integrandValue], ?_, by simp [limitValue], ?_⟩
  · intro R h
    have hR := (show RealIntegrable _ 0 R from h).ordered
    obtain ⟨h', he⟩ := finite_formula R 0 hR le_rfl
    simpa [exponential_eq] using he
  · intro t ht
    simp [limitValue, ne_of_gt ht]

theorem truncation_continuity : truncationContinuity := by
  intro R _
  simp only [exponential_eq]
  fun_prop

private theorem finite_value (R t : ℝ) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (h : RealIntegrable (fun x => integrand x t) 0 R) :
    realIntegral _ h = 1 - Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue (-t * R) := by
  obtain ⟨h', he⟩ := finite_formula R t hR ht
  exact he

theorem improper_formula : improperFormula := by
  intro t ht
  have hreg : rightRegularValue .real (fun x => integrand x t) 0 ⊤ := by
    refine ⟨WithTop.coe_lt_top _, fun R => ?_⟩
    exact (finite_formula R.val t R.property.1.le ht).choose
  refine ⟨hreg, fun ε hε => ?_⟩
  by_cases hz : t = 0
  · subst t
    refine ⟨⟨1, zero_lt_one, WithTop.coe_lt_top _⟩, fun R _ => ?_⟩
    change dist (realIntegral _ (hreg.2 R)) (limitValue 0) < ε
    have hv := finite_value R.val 0 R.property.1.le le_rfl (hreg.2 R)
    simpa [hv, limitValue, exponential_eq] using hε
  · have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hlin : Tendsto (fun R : ℝ => -t * R) atTop atBot := by
      simpa only [id_eq, mul_comm] using
        (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop).atTop_mul_const_of_neg' (neg_neg_of_pos ht')
    have hexp : Tendsto (fun R : ℝ => Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue (-t * R)) atTop (𝓝 0) :=
      real_expSeries_tendsto_atBot.comp hlin
    obtain ⟨B, hB⟩ := Metric.tendsto_atTop.mp hexp ε hε
    refine ⟨⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), WithTop.coe_lt_top _⟩,
      fun R hR => ?_⟩
    change dist (realIntegral _ (hreg.2 R)) (limitValue t) < ε
    have hv := finite_value R.val t R.property.1.le ht (hreg.2 R)
    have hclose := hB R.val ((le_max_left B 1).trans hR.le)
    calc
      _ = dist (1 - Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue (-t * R.val)) 1 :=
        congrArg₂ dist hv (by simp [limitValue, hz])
      _ = dist (Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue (-t * R.val)) 0 := by
        simp
      _ < ε := hclose

theorem limit_discontinuous : discontinuity := by
  intro hc
  obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.mp hc (1 / 2) (by norm_num)
  have hd : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  have hh := h (show δ / 2 ∈ Ici (0 : ℝ) from (half_pos hδ).le) hd
  norm_num [limitValue, ne_of_gt (half_pos hδ)] at hh

theorem tail_formula : tailFormula := by
  intro R t hR ht h
  calc
    _ = limitValue t - (1 - Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue (-t * R)) :=
      congrArg (fun y : ℝ => limitValue t - y) (finite_value R t hR ht.le h)
    _ = _ := by simp [limitValue, ne_of_gt ht]

theorem tail_hasIntegral : tailHasIntegral := by
  intro R t hR ht
  rcases hR.eq_or_lt with rfl | hR
  · simpa [limitValue, ne_of_gt ht, exponential_eq] using improper_formula t ht.le
  obtain ⟨h0, hlim⟩ := improper_formula t ht.le
  let u : rightIndexValue 0 ⊤ := ⟨R, hR, WithTop.coe_lt_top _⟩
  let lift (v : rightIndexValue R ⊤) : rightIndexValue 0 ⊤ :=
    ⟨v.val, hR.trans v.property.1, WithTop.coe_lt_top _⟩
  have hd (v : rightIndexValue R ⊤) :=
    SingleVariableAnalysis.Riemann.Improper.right_tail_difference .real
      (fun x => integrand x t) 0 ⊤ h0 u (lift v) v.property.1
  have hreg : rightRegularValue .real (fun x => integrand x t) R ⊤ :=
    ⟨WithTop.coe_lt_top _, fun v => (hd v).choose⟩
  refine ⟨hreg, fun ε hε => ?_⟩
  obtain ⟨r, hr⟩ := hlim ε hε
  refine ⟨⟨max r.val R + 1, by linarith [le_max_right r.val R], WithTop.coe_lt_top _⟩,
    fun v hv => ?_⟩
  have hlate : r.val < (lift v).val := by
    dsimp [lift]
    have hv' : max r.val R + 1 < v.val := hv
    linarith [le_max_left r.val R]
  change dist (realIntegral _ (hreg.2 v))
    (Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue (-t * R)) < ε
  have hdiff : realIntegral _ (hreg.2 v) =
      realIntegral _ (h0.2 (lift v)) - realIntegral _ (h0.2 u) := (hd v).choose_spec
  calc
    _ = dist (realIntegral _ (h0.2 (lift v)) - realIntegral _ (h0.2 u))
        (limitValue t - realIntegral _ (h0.2 u)) :=
      congrArg₂ dist hdiff (tail_formula R t hR.le ht (h0.2 u)).symm
    _ = dist (realIntegral _ (h0.2 (lift v))) (limitValue t) := dist_sub_right _ _ _
    _ < ε := hr (lift v) hlate

theorem tail_supremum : Specs.SingleVariableAnalysis.Ch14.Failure.tailSupremum := by
  intro R δ hR hδ
  have hc : Tendsto (fun t : ℝ =>
      Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue (-t * R))
      (𝓝[>] 0) (𝓝 1) := by
    simp only [exponential_eq]
    have he : ContinuousAt (fun t : ℝ => Real.exp (-t * R)) 0 := by fun_prop
    simpa using he.tendsto.mono_left nhdsWithin_le_nhds
  have hlub : IsLUB ((fun t =>
      Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue (-t * R)) '' Ioc 0 δ) 1 := by
    constructor
    · rintro _ ⟨t, ht, rfl⟩
      have hn : -t * R ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.1.le) hR.le
      simpa only [exponential_eq] using Real.exp_le_one_iff.mpr hn
    · intro u hu
      apply le_of_tendsto hc
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with t ht htδ
      exact hu (mem_image_of_mem _ ⟨ht, htδ.le⟩)
  exact ⟨hlub, hlub.csSup_eq ⟨_, mem_image_of_mem _ ⟨hδ, le_rfl⟩⟩⟩

/-- Any parameter set containing all sufficiently small positive parameters
fails uniform convergence. The proof rules out arbitrary proposed limits by
uniqueness of the improper integral, then uses the exact tail supremum. -/
theorem not_uniform_on (δ : ℝ) (hδ : 0 < δ) (T : Set ℝ)
    (hsub : Ioc 0 δ ⊆ T) (hpos : T ⊆ Ici 0) :
    ¬ Specs.SingleVariableAnalysis.Ch14.UniformImproper.rightUniformConvergesValue
      .real T (fun x t => integrand x t.val) 0 ⊤ := by
  rintro ⟨G, hG⟩
  have heq (t : T) : G t = limitValue t.val :=
    SingleVariableAnalysis.Riemann.Improper.right_unique .real _ 0 ⊤ _ _
      (SingleVariableAnalysis.Riemann.Improper.right_uniform_pointwise .real T _ 0 ⊤ G hG t)
      (improper_formula t.val (hpos t.property))
  obtain ⟨hreg, hlim⟩ := hG
  obtain ⟨r, hr⟩ := hlim (1 / 2) (by norm_num)
  let R : rightIndexValue 0 ⊤ :=
    ⟨r.val + 1, by linarith [r.property.1], WithTop.coe_lt_top _⟩
  have hR : r.val < R.val := by dsimp [R]; linarith
  obtain ⟨y, ⟨t, ht, rfl⟩, hy, _⟩ := (tail_supremum R.val δ R.property.1 hδ).1.exists_between
    (show (1 : ℝ) / 2 < 1 by norm_num)
  have he := hr R hR ⟨t, hsub ht⟩
  rw [heq] at he
  change dist (realIntegral _ ((hreg.2 ⟨t, hsub ht⟩).2 R)) (limitValue t) < (1 : ℝ) / 2 at he
  rw [Real.dist_eq, abs_sub_comm] at he
  have htail := tail_formula R.val t R.property.1.le ht.1
    ((hreg.2 ⟨t, hsub ht⟩).2 R)
  have he' : |Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesExpValue (-t * R.val)| < (1 : ℝ) / 2 := by
    calc
      _ = |limitValue t - realIntegral _ ((hreg.2 ⟨t, hsub ht⟩).2 R)| :=
        congrArg abs htail.symm
      _ < _ := he
  have he'' := (abs_lt.mp he').2
  exact (not_lt_of_ge he''.le) hy

theorem nonuniform_convergence : nonuniform := by
  intro δ hδ
  exact ⟨not_uniform_on δ hδ (Icc 0 δ) Ioc_subset_Icc_self (fun _ ht => ht.1),
    not_uniform_on δ hδ (Ioc 0 δ) Subset.rfl (fun _ ht => ht.1.le)⟩

end SingleVariableAnalysis.ParameterFailure
