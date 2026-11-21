import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.DenseCoboundaries
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.CompositionIsometry
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace D13Unified.Ch19.DenseCoboundaries
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
universe u
abbrev truncate := @Specs.D13Unified.Ch19.DenseCoboundaries.truncate
abbrev boundedCoboundaries := @Specs.D13Unified.Ch19.DenseCoboundaries.boundedCoboundaries

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

lemma truncate_bound (f : X → ℝ) (n : ℕ) (x : X) : ‖truncate f n x‖ ≤ n := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩

lemma truncate_error_bound (f : X → ℝ) (n : ℕ) (x : X) :
    ‖truncate f n x - f x‖ ≤ ‖f x‖ := by
  unfold truncate Specs.D13Unified.Ch19.DenseCoboundaries.truncate
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_total (f x) (-(n : ℝ)) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h, abs_of_nonneg (by linarith),
      abs_of_nonpos (by linarith)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · rcases le_total (f x) (n : ℝ) with h' | h'
    · rw [min_eq_right h', max_eq_right h, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [min_eq_left h', max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) n]), abs_of_nonpos (by linarith),
        abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])]
      linarith [Nat.cast_nonneg (α := ℝ) n]

lemma truncate_measurable (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    AEStronglyMeasurable (truncate f n) μ :=
  ((continuous_const.max (continuous_const.min continuous_id)).comp_aestronglyMeasurable hf)

lemma truncate_memLp [IsFiniteMeasure μ] (f : X → ℝ) (hf : AEStronglyMeasurable f μ)
    (n : ℕ) : MemLp (truncate f n) ∞ μ :=
  MemLp.of_bound (truncate_measurable f hf n) n (.of_forall (truncate_bound f n))

lemma truncate_fixed (f : X → ℝ) (T : X → X) (hf : f ∘ T =ᵐ[μ] f) (n : ℕ) :
    truncate f n ∘ T =ᵐ[μ] truncate f n := by
  filter_upwards [hf] with x hx
  change max _ (min _ (f (T x))) = max _ (min _ (f x))
  rw [show f (T x) = f x from hx]

/-- Truncations converge for every finite positive exponent. -/
lemma truncate_tendsto {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞)
    (f : X → ℝ) (hf : MemLp f p μ) :
    Tendsto (fun n => eLpNorm (truncate f n - f) p μ) atTop (𝓝 0) := by
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have hmeas n := (truncate_measurable f hf.aestronglyMeasurable n).sub hf.aestronglyMeasurable
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' (hmeas _)]
  have ht : Tendsto (fun n => ∫⁻ x, ‖truncate f n x - f x‖ₑ ^ p.toReal ∂μ)
      atTop (𝓝 0) := by
    have hz : (∫⁻ _ : X, (0 : ℝ≥0∞) ∂μ) = 0 := by simp
    rw [← hz]
    apply tendsto_lintegral_of_dominated_convergence' (fun x => ‖f x‖ₑ ^ p.toReal)
    · intro n
      exact (hmeas n).enorm.pow_const _
    · intro n
      exact .of_forall fun x => ENNReal.rpow_le_rpow
        (enorm_le_iff_norm_le.mpr (truncate_error_bound f n x)) hpos.le
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp hp' hf.eLpNorm_lt_top).ne
    · apply ae_of_all
      intro x
      have heq : ∀ᶠ n : ℕ in atTop, truncate f n x = f x := by
        filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖f x‖)] with n hn
        change max (-(n : ℝ)) (min (n : ℝ) (f x)) = f x
        rw [min_eq_right ((le_abs_self _).trans hn),
          max_eq_right (by have := neg_abs_le (f x); rw [← Real.norm_eq_abs] at this; linarith)]
      apply tendsto_const_nhds.congr'
      filter_upwards [heq] with n hn
      simp [hn, ENNReal.zero_rpow_of_pos hpos]
  simpa only [Pi.sub_apply, one_div, Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.mpr hpos)] using
    (ENNReal.continuous_rpow_const (y := p.toReal⁻¹)).continuousAt.tendsto.comp ht

theorem truncation : Specs.D13Unified.Ch19.DenseCoboundaries.truncationStatement := by
  intro X _ T μ _ f hf
  exact ⟨truncate_memLp f hf.aestronglyMeasurable, truncate_tendsto (by norm_num) (by norm_num) f hf,
    fun h n => truncate_fixed f T h n⟩


section Approximation
variable [IsProbabilityMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Bounded truncations converge in Lᵖ; invariance survives on representatives. -/
lemma bounded_approximation (hp : p ≠ ∞) (f : Lp ℝ p μ) :
    ∃ b : ℕ → Lp ℝ p μ, (∀ n, MemLp (b n) ∞ μ) ∧
      Tendsto b atTop (𝓝 f) ∧
      ∀ (T : X → X), MeasurePreserving T μ μ → (f : X → ℝ) ∘ T =ᵐ[μ] f →
        ∀ n, (b n : X → ℝ) ∘ T =ᵐ[μ] b n := by
  have hb n := truncate_memLp f (Lp.aestronglyMeasurable f) n
  have hbp n : MemLp (truncate f n) p μ := (hb n).mono_exponent le_top
  let b n := (hbp n).toLp (truncate f n)
  refine ⟨b, fun n => (memLp_congr_ae (hbp n).coeFn_toLp).mpr (hb n), ?_, ?_⟩
  · have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (truncate f) hbp f (Lp.memLp f)).mpr
      (truncate_tendsto (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp f
        (Lp.memLp f))
    simpa only [Lp.toLp_coeFn] using ht
  · intro T hT h n
    exact (hT.quasiMeasurePreserving.ae_eq_comp (hbp n).coeFn_toLp).trans
      ((truncate_fixed f T h n).trans (hbp n).coeFn_toLp.symm)

end Approximation


section Density
variable [IsProbabilityMeasure μ] (T : X → X) (hT : MeasurePreserving T μ μ)

private def boundedSubmodule (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (Lp ℝ p μ) where
  carrier := boundedCoboundaries p T μ hT
  zero_mem' := by
    refine ⟨0, 0, ?_, ?_, ?_, by simp⟩
    · exact (memLp_congr_ae (Lp.coeFn_zero ℝ p μ)).mpr MemLp.zero
    · exact (memLp_congr_ae (Lp.coeFn_zero ℝ p μ)).mpr MemLp.zero
    · exact (hT.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_zero ℝ p μ)).trans
        (Lp.coeFn_zero ℝ p μ).symm
  add_mem' := by
    rintro d e ⟨v, g, hv, hg, hvi, rfl⟩ ⟨w, k, hw, hk, hwi, rfl⟩
    refine ⟨v + w, g + k, ?_, ?_, ?_, ?_⟩
    · exact (memLp_congr_ae (Lp.coeFn_add v w)).mpr (hv.add hw)
    · exact (memLp_congr_ae (Lp.coeFn_add g k)).mpr (hg.add hk)
    · exact (hT.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_add v w)).trans
        ((hvi.add hwi).trans (Lp.coeFn_add v w).symm)
    · simp only [map_add]; abel
  smul_mem' := by
    rintro c d ⟨v, g, hv, hg, hvi, rfl⟩
    refine ⟨c • v, c • g, ?_, ?_, ?_, ?_⟩
    · exact (memLp_congr_ae (Lp.coeFn_smul c v)).mpr (hv.const_smul c)
    · exact (memLp_congr_ae (Lp.coeFn_smul c g)).mpr (hg.const_smul c)
    · exact (hT.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c v)).trans
        ((hvi.const_smul c).trans (Lp.coeFn_smul c v).symm)
    · simp [smul_add, smul_sub]

lemma dense_l2 : Dense (boundedCoboundaries 2 T μ hT) := by
  let U := CompositionIsometry.composition ℝ 2 T μ hT
  let B := boundedSubmodule T hT 2
  have hfixed : Specs.D13Unified.Ch19.MeanErgodic.fixedSpace U ≤ B.topologicalClosure := by
    intro v hv
    have hvi : (v : X → ℝ) ∘ T =ᵐ[μ] v :=
      (CompositionIsometry.l2_mean_ergodic ℝ T μ hT).1 v |>.mp hv
    obtain ⟨b, hb, ht, hi⟩ := bounded_approximation (by norm_num : (2 : ℝ≥0∞) ≠ ∞) v
    apply B.isClosed_topologicalClosure.mem_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro n
    apply subset_closure
    refine ⟨b n, 0, hb n, ?_, hi T hT hvi n, by simp⟩
    exact (memLp_congr_ae (Lp.coeFn_zero ℝ 2 μ)).mpr MemLp.zero
  have hrange : LinearMap.range (LinearMap.id - U.toLinearMap) ≤ B.topologicalClosure := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨b, hb, ht, _⟩ := bounded_approximation (by norm_num : (2 : ℝ≥0∞) ≠ ∞) g
    have hlim := ht.sub (U.continuous.tendsto g |>.comp ht)
    change g - U g ∈ B.topologicalClosure
    apply B.isClosed_topologicalClosure.mem_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    apply subset_closure
    refine ⟨0, b n, ?_, hb n, ?_, by simp [U]⟩
    · exact (memLp_congr_ae (Lp.coeFn_zero ℝ 2 μ)).mpr MemLp.zero
    · exact (hT.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_zero ℝ 2 μ)).trans
        (Lp.coeFn_zero ℝ 2 μ).symm
  have hcob : Specs.D13Unified.Ch19.MeanErgodic.coboundarySpace U ≤ B.topologicalClosure := by
    exact Submodule.topologicalClosure_minimal _ hrange B.isClosed_topologicalClosure
  have htop : (⊤ : Submodule ℝ (Lp ℝ 2 μ)) ≤ B.topologicalClosure := by
    rw [← (MeanErgodic.fixed_coboundary_complement U).sup_eq_top]
    exact sup_le hfixed hcob
  intro f
  exact htop (Submodule.mem_top)

/-- The canonical inclusion on a probability space is a contraction. -/
private def lower (p : ℝ≥0∞) [Fact (1 ≤ p)] : Lp ℝ p μ →L[ℝ] Lp ℝ 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (Lp.memLp f |>.mono_exponent (Fact.out : 1 ≤ p)).toLp f
      map_add' := by
        intro f g
        apply Lp.ext
        exact (MemLp.coeFn_toLp _).trans
          ((Lp.coeFn_add f g).trans ((Lp.coeFn_add _ _).trans
            ((MemLp.coeFn_toLp _).add (MemLp.coeFn_toLp _))).symm)
      map_smul' := by
        intro c f
        apply Lp.ext
        exact (MemLp.coeFn_toLp _).trans
          ((Lp.coeFn_smul c f).trans ((Lp.coeFn_smul c _).trans
            ((MemLp.coeFn_toLp _).const_smul c)).symm) }
    1 (by
      intro f
      simp only [one_mul]
      change ‖(Lp.memLp f |>.mono_exponent (Fact.out : 1 ≤ p)).toLp f‖ ≤ ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_le_eLpNorm_of_exponent_le (Fact.out : 1 ≤ p)))


private lemma lower_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp ℝ p μ) :
    (lower (μ := μ) p f : X → ℝ) =ᵐ[μ] f :=
  (Lp.memLp f |>.mono_exponent (Fact.out : 1 ≤ p)).coeFn_toLp

private lemma lower_composition (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp ℝ p μ) :
    lower (μ := μ) p (CompositionIsometry.composition ℝ p T μ hT f) =
      CompositionIsometry.composition ℝ 1 T μ hT (lower (μ := μ) p f) := by
  apply Lp.ext
  exact (lower_ae p _).trans ((CompositionIsometry.composition_ae ℝ p T μ hT f).trans
    ((CompositionIsometry.composition_ae ℝ 1 T μ hT _).trans
      (hT.quasiMeasurePreserving.ae_eq_comp (lower_ae p f))).symm)

private lemma lower_mem (d : Lp ℝ 2 μ) (hd : d ∈ boundedCoboundaries 2 T μ hT) :
    lower (μ := μ) 2 d ∈ boundedCoboundaries 1 T μ hT := by
  obtain ⟨v, g, hv, hg, hi, rfl⟩ := hd
  refine ⟨lower 2 v, lower 2 g, (memLp_congr_ae (lower_ae 2 v)).mpr hv,
    (memLp_congr_ae (lower_ae 2 g)).mpr hg, ?_, ?_⟩
  · exact (hT.quasiMeasurePreserving.ae_eq_comp (lower_ae 2 v)).trans
      (hi.trans (lower_ae 2 v).symm)
  · rw [map_add, map_sub, lower_composition T hT]

lemma dense_l1 : Dense (boundedCoboundaries 1 T μ hT) := by
  have hrange (f : Lp ℝ 2 μ) : lower (μ := μ) 2 f ∈
      closure (boundedCoboundaries 1 T μ hT) := by
    exact closure_minimal (t := (lower (μ := μ) 2) ⁻¹' closure (boundedCoboundaries 1 T μ hT))
      (fun d hd => subset_closure (lower_mem T hT d hd))
      (isClosed_closure.preimage (lower (μ := μ) 2).continuous) (dense_l2 T hT f)
  intro f
  obtain ⟨b, hb, ht, _⟩ := bounded_approximation (by norm_num : (1 : ℝ≥0∞) ≠ ∞) f
  apply isClosed_closure.mem_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro n
  let c : Lp ℝ 2 μ := ((hb n).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)).toLp (b n)
  have hc : lower (μ := μ) 2 c = b n :=
    Lp.ext ((lower_ae 2 c).trans (MemLp.coeFn_toLp _))
  rw [← hc]
  exact hrange c

theorem density : Specs.D13Unified.Ch19.DenseCoboundaries.densityStatement := by
  intro X _ T μ _ hT
  exact ⟨dense_l2 T hT, dense_l1 T hT⟩

end Density


section Convergence
variable [IsProbabilityMeasure μ] (T : X → X) (hT : MeasurePreserving T μ μ)

lemma essentially_bounded_norm (g : X → ℝ) (hg : MemLp g ∞ μ) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ (eLpNorm g ∞ μ).toReal := by
  have he : eLpNormEssSup g μ ≠ ∞ := by
    rw [← eLpNorm_exponent_top hg.aestronglyMeasurable]
    exact hg.ne
  filter_upwards [enorm_ae_le_eLpNormEssSup g μ] with x hx
  have hh := ENNReal.toReal_mono he hx
  simpa only [eLpNorm_exponent_top hg.aestronglyMeasurable, enorm, ENNReal.coe_toReal,
    coe_nnnorm] using hh

/-- The a.e. algebraic identities and the essential bound hold simultaneously
on the whole forward orbit; no choice of inverse of T is involved. -/
lemma pointwise_coboundary (v g : Lp ℝ 1 μ) (hg : MemLp g ∞ μ)
    (hi : (v : X → ℝ) ∘ T =ᵐ[μ] v) :
    let d := v + (g - CompositionIsometry.composition ℝ 1 T μ hT g)
    ∀ᵐ x ∂μ, (∀ n : ℕ, 0 < n →
      MeasureDefinitions.ergodicAverage T (d : X → ℝ) n x =
        v x + (g x - g (T^[n] x)) / (n : ℝ)) ∧
      (∀ n : ℕ, 0 < n →
        |MeasureDefinitions.ergodicAverage T (d : X → ℝ) n x - v x| ≤
          2 * (eLpNorm g ∞ μ).toReal / (n : ℝ)) ∧
      Tendsto (fun n => MeasureDefinitions.ergodicAverage T (d : X → ℝ) n x)
        atTop (𝓝 (v x)) := by
  let U := CompositionIsometry.composition ℝ 1 T μ hT
  let d := v + (g - U g)
  have hd : (d : X → ℝ) =ᵐ[μ] fun x => v x + (g x - g (T x)) := by
    filter_upwards [Lp.coeFn_add v (g - U g), Lp.coeFn_sub g (U g),
      CompositionIsometry.composition_ae ℝ 1 T μ hT g] with x ha hs hu
    change (v + (g - U g)) x = _
    rw [ha, Pi.add_apply, hs, Pi.sub_apply, hu]
    rfl
  have hda : ∀ᵐ x ∂μ, ∀ n : ℕ, d (T^[n] x) =
      v (T^[n] x) + (g (T^[n] x) - g (T (T^[n] x))) :=
    ae_all_iff.mpr (fun n => (hT.iterate n).quasiMeasurePreserving.ae hd)
  have hia : ∀ᵐ x ∂μ, ∀ n : ℕ, v (T (T^[n] x)) = v (T^[n] x) :=
    ae_all_iff.mpr (fun n => (hT.iterate n).quasiMeasurePreserving.ae hi)
  have hga : ∀ᵐ x ∂μ, ∀ n : ℕ, ‖g (T^[n] x)‖ ≤ (eLpNorm g ∞ μ).toReal :=
    ae_all_iff.mpr (fun n => (hT.iterate n).quasiMeasurePreserving.ae
      (essentially_bounded_norm g hg))
  filter_upwards [hda, hia, hga] with x hdx hix hgx
  have hvx (n : ℕ) : v (T^[n] x) = v x := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', hix n, ih]
  have hsum (n : ℕ) : (∑ j ∈ Finset.range n, d (T^[j] x)) =
      (n : ℝ) * v x + g x - g (T^[n] x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hdx n, hvx n, Function.iterate_succ_apply']
      push_cast
      ring
  have heq (n : ℕ) (hn : 0 < n) :
      MeasureDefinitions.ergodicAverage T (d : X → ℝ) n x =
        v x + (g x - g (T^[n] x)) / (n : ℝ) := by
    rw [MeasureDefinitions.ergodicAverage_real_eq T d n hn, hsum]
    field_simp
    ring
  have hbound (n : ℕ) (hn : 0 < n) :
      |MeasureDefinitions.ergodicAverage T (d : X → ℝ) n x - v x| ≤
        2 * (eLpNorm g ∞ μ).toReal / (n : ℝ) := by
    rw [heq n hn, add_sub_cancel_left, abs_div, abs_of_pos (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    calc
      |g x - g (T^[n] x)| ≤ |g x| + |g (T^[n] x)| := abs_sub _ _
      _ ≤ 2 * (eLpNorm g ∞ μ).toReal := by
        have h0 := hgx 0
        simpa only [Function.iterate_zero_apply, Real.norm_eq_abs] using
          (add_le_add h0 (hgx n)).trans_eq (two_mul _).symm
  refine ⟨heq, hbound, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  exact squeeze_zero' (.of_forall fun n => norm_nonneg _)
    ((eventually_gt_atTop 0).mono fun n hn => by simpa only [Real.norm_eq_abs] using hbound n hn)
    (tendsto_const_div_atTop_nhds_zero_nat (2 * (eLpNorm g ∞ μ).toReal))

theorem convergence : Specs.D13Unified.Ch19.DenseCoboundaries.convergenceStatement := by
  intro X _ T μ _ hT v g _ hg hi
  let d := v + (g - CompositionIsometry.composition ℝ 1 T μ hT g)
  have hp := pointwise_coboundary T hT v g hg hi
  refine ⟨hp, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  apply squeeze_zero' (g := fun n : ℕ => 2 * (eLpNorm g ∞ μ).toReal / (n : ℝ))
    (.of_forall fun n => norm_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hb : ∀ᵐ x ∂μ, ‖(CompositionIsometry.average ℝ 1 T μ hT n d - v) x‖ ≤
        2 * (eLpNorm g ∞ μ).toReal / (n : ℝ) := by
      filter_upwards [hp, CompositionIsometry.average_ae ℝ 1 T μ hT n d,
        Lp.coeFn_sub (CompositionIsometry.average ℝ 1 T μ hT n d) v] with x hx ha hs
      rw [hs, Pi.sub_apply, ha, Real.norm_eq_abs]
      exact hx.2.1 n hn
    change ‖CompositionIsometry.average ℝ 1 T μ hT n d - v‖ ≤ _
    simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one,
      Real.one_rpow, one_mul] using
      Lp.norm_le_of_ae_bound (by positivity) hb
  · exact tendsto_const_div_atTop_nhds_zero_nat (2 * (eLpNorm g ∞ μ).toReal)

end Convergence

end
end D13Unified.Ch19.DenseCoboundaries
