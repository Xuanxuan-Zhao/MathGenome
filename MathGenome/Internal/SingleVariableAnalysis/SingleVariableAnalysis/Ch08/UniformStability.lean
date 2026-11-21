import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.UniformStability
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Uniform

/-! Uniform stability for the proper Darboux integral. -/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators Topology

/-- One uniformly close bounded function bounds the limit. -/
theorem bounded_uniform_limit {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → ℝ → E} {f : ℝ → E} {a b : ℝ}
    (hF : ∀ n, ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖F n x‖ ≤ M)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ x ∈ Set.Icc a b, ‖F n x - f x‖ < ε) :
    ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M := by
  obtain ⟨N, hN⟩ := hu 1 zero_lt_one
  obtain ⟨M, hM⟩ := hF N
  refine ⟨M + 1, fun x hx => ?_⟩
  have ht := norm_add_le (F N x) (f x - F N x)
  rw [add_sub_cancel] at ht
  have he : ‖f x - F N x‖ < 1 := by simpa only [norm_sub_rev] using hN N le_rfl x hx
  linarith [hM x hx]

/-- A uniform error increases the Darboux gap by at most twice length times error. -/
theorem darboux_gap_le_of_uniform_error {f g : ℝ → ℝ} {a b e : ℝ}
    (P : Partition a b) (hf : BoundedOnInterval f a b)
    (hg : BoundedOnInterval g a b)
    (he : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ e) :
    upperSum f P hf - lowerSum f P hf ≤
      upperSum g P hg - lowerSum g P hg + 2 * e * (b - a) := by
  have hc (i : Fin P.n) :
      cellSupremum f P hf i - cellInfimum f P hf i ≤
        (cellSupremum g P hg i - cellInfimum g P hg i) + 2 * e := by
    apply cell_oscillation_le_of_sub_le
    intro x hx y hy
    have hxy := abs_sub_le_cell_oscillation g P hg i hx hy
    have hex := abs_le.mp (he x (cell_subset_interval P i hx))
    have hey := abs_le.mp (he y (cell_subset_interval P i hy))
    linarith [(le_abs_self (g x - g y)).trans hxy]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_right (hc i) (cell_positive P i).le
  have hsum (u : ℝ → ℝ) (hu : BoundedOnInterval u a b) :
      (∑ i : Fin P.n, (cellSupremum u P hu i - cellInfimum u P hu i) *
        cellLength P i) = upperSum u P hu - lowerSum u P hu := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rfl
  simp only [add_mul, Finset.sum_add_distrib, hsum,
    ← Finset.mul_sum, sum_cellLength] at hs
  exact hs

theorem realIntegrable_uniform_limit {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ n, RealIntegrable (F n) a b)
    (hu : RealUniformConverges (fun n (x : Set.Icc a b) => F n x) (fun x => f x)) :
    RealIntegrable f a b := by
  have hb := bounded_uniform_limit (F := F) (f := f) (a := a) (b := b)
    (fun n => by simpa only [Real.norm_eq_abs] using (hF n).bounded.abs_bound)
    (by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      exact ⟨N, fun n hn x hx => by
        simpa only [Real.norm_eq_abs] using hN n hn ⟨x, hx⟩⟩)
  obtain ⟨M, hM⟩ := hb
  have hf : BoundedOnInterval f a b :=
    boundedOnInterval_of_abs (by simpa only [Real.norm_eq_abs] using hM)
  rcases lt_or_eq_of_le hab with hab | rfl
  · apply (darboux_criterion f hab hf).mpr
    intro ε hε
    have hlen : 0 < b - a := sub_pos.mpr hab
    obtain ⟨N, hN⟩ := hu (ε / (4 * (b - a))) (by positivity)
    obtain ⟨P, hP⟩ := (darboux_criterion (F N) hab (hF N).bounded).mp
      (hF N) (ε / 2) (half_pos hε)
    refine ⟨P, ?_⟩
    have hg := darboux_gap_le_of_uniform_error P hf (hF N).bounded
      (fun x hx => by simpa only [abs_sub_comm] using (hN N le_rfl ⟨x, hx⟩).le)
    have he : 2 * (ε / (4 * (b - a))) * (b - a) = ε / 2 := by
      field_simp [ne_of_gt hlen]
      norm_num
    rw [he] at hg
    linarith
  · exact realIntegrable_degenerate f a

/-- Linearity applied to a difference, with its actual Darboux value. -/
theorem real_sub_value {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b) :
    ∃ hd : RealIntegrable (fun x => f x - g x) a b,
      realIntegral _ hd = realIntegral f hf - realIntegral g hg := by
  obtain ⟨hn, hIn⟩ := real_mul_value hg (-1)
  obtain ⟨hd, hId⟩ := real_add_value hf hn
  rw [hIn] at hId
  refine ⟨by simpa only [neg_one_mul, sub_eq_add_neg] using hd, ?_⟩
  simpa only [neg_one_mul, sub_eq_add_neg] using hId

theorem complex_sub_value {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b) :
    ∃ hd : ComplexIntegrable (fun x => f x - g x) a b,
      complexIntegral _ hd = complexIntegral f hf - complexIntegral g hg := by
  obtain ⟨hn, hIn⟩ := complex_mul_value hg (-1)
  obtain ⟨hd, hId⟩ := complex_add_value hf hn
  rw [hIn] at hId
  refine ⟨by simpa only [neg_one_mul, sub_eq_add_neg] using hd, ?_⟩
  simpa only [neg_one_mul, sub_eq_add_neg] using hId

/-- The real supremum of the errors tends to zero. Boundedness of every
difference ensures these are genuine finite suprema at every index. -/
theorem norm_error_sup_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → ℝ → E} {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ n, ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖F n x‖ ≤ M)
    (hf : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ x ∈ Set.Icc a b, ‖F n x - f x‖ < ε) :
    Filter.Tendsto (fun n => sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b))
      Filter.atTop (𝓝 0) := by
  have hb (n : ℕ) : BddAbove ((fun x => ‖f x - F n x‖) '' Set.Icc a b) := by
    obtain ⟨M, hM⟩ := hf
    obtain ⟨L, hL⟩ := hF n
    refine ⟨M + L, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add (hM x hx) (hL x hx))
  have hne (n : ℕ) : ((fun x => ‖f x - F n x‖) '' Set.Icc a b).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)⟩
  have hzero (n : ℕ) : 0 ≤ sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b) :=
    (norm_nonneg _).trans (le_csSup (hb n)
      (Set.mem_image_of_mem _ (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hzero n)]
  apply lt_of_le_of_lt (csSup_le (hne n) ?_) (half_lt_self hε)
  rintro _ ⟨x, hx, rfl⟩
  simpa only [norm_sub_rev] using (hN n hn x hx).le

theorem real_integral_sub_le_sup {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b) :
    ‖realIntegral f hf - realIntegral g hg‖ ≤
      (b - a) * sSup ((fun x => ‖f x - g x‖) '' Set.Icc a b) := by
  obtain ⟨hd, hId⟩ := real_sub_value hf hg
  obtain ⟨_, ht, hu⟩ := real_norm_estimate _ hd
  have h := ht.trans hu
  change ‖realIntegral _ hd‖ ≤ _ at h
  rw [hId] at h
  exact h

theorem complex_integral_sub_le_sup {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b) :
    ‖complexIntegral f hf - complexIntegral g hg‖ ≤
      (b - a) * sSup ((fun x => ‖f x - g x‖) '' Set.Icc a b) := by
  obtain ⟨hd, hId⟩ := complex_sub_value hf hg
  obtain ⟨_, ht, hu⟩ := complex_norm_estimate _ hd
  have h := ht.trans hu
  change ‖complexIntegral _ hd‖ ≤ _ at h
  rw [hId] at h
  exact h

/-- A vanishing error bound gives scalar convergence, with either scalar target. -/
theorem tendsto_of_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    {u : ℕ → E} {v : E} {e : ℕ → ℝ}
    (he : Filter.Tendsto e Filter.atTop (𝓝 0)) (hu : ∀ n, ‖v - u n‖ ≤ e n) :
    Filter.Tendsto u Filter.atTop (𝓝 v) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg)
    (fun n => by simpa only [dist_eq_norm, norm_sub_rev] using hu n) he

theorem real_uniform_stability :
    Specs.SingleVariableAnalysis.Ch08.UniformStability.realUniformStability := by
  intro F f a b hab hF hu
  have hu' : RealUniformConverges (fun n (x : Set.Icc a b) => F n x) (fun x => f x) := hu
  have hf := realIntegrable_uniform_limit hab hF hu'
  have hb : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hf.bounded.abs_bound
  have hs := norm_error_sup_tendsto_zero hab
    (F := F) (f := f)
    (fun n => by simpa only [Real.norm_eq_abs] using
      BoundedOnInterval.abs_bound (RealIntegrable.bounded (hF n))) hb
    (by
      intro ε hε
      obtain ⟨N, hN⟩ := hu' ε hε
      exact ⟨N, fun n hn x hx => by
        simpa only [Real.norm_eq_abs] using hN n hn ⟨x, hx⟩⟩)
  have hs' : Filter.Tendsto
      (fun n => (b - a) * sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b))
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul (b - a) hs
  refine ⟨hf, hb, fun n => real_integral_sub_le_sup hf (hF n), hs', ?_⟩
  exact tendsto_of_norm_sub_le hs' (fun n => real_integral_sub_le_sup hf (hF n))

theorem complex_uniform_stability :
    Specs.SingleVariableAnalysis.Ch08.UniformStability.complexUniformStability := by
  intro F f a b hab hF hu
  have hr : RealUniformConverges (fun n (x : Set.Icc a b) => (F n x).re)
      (fun x => (f x).re) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun n hn x => ?_⟩
    simpa only [Complex.sub_re] using
      (Complex.abs_re_le_norm (F n x - f x)).trans_lt (hN n hn x)
  have hi : RealUniformConverges (fun n (x : Set.Icc a b) => (F n x).im)
      (fun x => (f x).im) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun n hn x => ?_⟩
    simpa only [Complex.sub_im] using
      (Complex.abs_im_le_norm (F n x - f x)).trans_lt (hN n hn x)
  have hf : ComplexIntegrable f a b :=
    ⟨realIntegrable_uniform_limit hab (fun n => (hF n).1) hr,
      realIntegrable_uniform_limit hab (fun n => (hF n).2) hi⟩
  have hs := norm_error_sup_tendsto_zero hab (F := F) (f := f)
    (fun n => ComplexIntegrable.norm_bound (hF n)) hf.norm_bound
    (by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      exact ⟨N, fun n hn x hx => hN n hn ⟨x, hx⟩⟩)
  have hs' : Filter.Tendsto
      (fun n => (b - a) * sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b))
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul (b - a) hs
  refine ⟨hf, hf.norm_bound, fun n => complex_integral_sub_le_sup hf (hF n), hs', ?_⟩
  exact tendsto_of_norm_sub_le hs' (fun n => complex_integral_sub_le_sup hf (hF n))

end SingleVariableAnalysis.Riemann
