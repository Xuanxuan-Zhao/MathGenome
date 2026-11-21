import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.AffineEnvelopeLowerLimit
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.CaratheodoryIntegrands
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.WeakLpPairings
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Convert

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace VariationalNotes.Sobolev

variable {S : Type*} [MeasurableSpace S] {μ : Measure S}

/-- Comparing an integrable signed test with a possibly infinite upper energy. -/
theorem integral_coe_le_lintegral_ofReal {f g : S → ℝ}
    (hf : Integrable f μ) (hfg : f ≤ᵐ[μ] g) :
    ((∫ x, f x ∂μ : ℝ) : EReal) ≤ ((∫⁻ x, ENNReal.ofReal (g x) ∂μ) : EReal) := by
  have hp : Integrable (fun x ↦ max (f x) 0) μ := hf.pos_part
  have hpos : 0 ≤ ∫ x, max (f x) 0 ∂μ := integral_nonneg (fun _ ↦ le_max_right _ _)
  calc
    ((∫ x, f x ∂μ : ℝ) : EReal) ≤ ((∫ x, max (f x) 0 ∂μ : ℝ) : EReal) := by
      exact_mod_cast integral_mono hf hp (fun _ ↦ le_max_left _ _)
    _ = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ) : EReal) := by
      have heq : (fun x ↦ ENNReal.ofReal (max (f x) 0)) =
          (fun x ↦ ENNReal.ofReal (f x)) := by
        ext x
        simp [ENNReal.ofReal, Real.toNNReal]
      rw [← heq, ← ofReal_integral_eq_lintegral_ofReal hp
        (ae_of_all _ (fun _ ↦ le_max_right _ _)), EReal.coe_ennreal_ofReal,
        max_eq_left hpos]
    _ ≤ _ := by
      exact_mod_cast lintegral_mono_ae (hfg.mono fun _ h ↦ ENNReal.ofReal_le_ofReal h)

/-- A convergent sequence admits increasing simultaneous bounds on a conull
union of null-measurable sets. Null measurability is enough for indicators and
avoids imposing completeness on the measure. -/
theorem exists_bounded_localizations {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {fₙ : ℕ → S → E} {f : S → E}
    (hfₙ : ∀ n, AEMeasurable (fₙ n) μ) (hf : AEMeasurable f μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ fₙ n x) atTop (𝓝 (f x))) :
    ∃ T : ℕ → Set S, (∀ M, NullMeasurableSet (T M) μ) ∧ Monotone T ∧
      (∀ᵐ x ∂μ, ∃ M, x ∈ T M) ∧
      (∀ M x, x ∈ T M → (∀ n, ‖fₙ n x‖ ≤ (M : ℝ)) ∧ ‖f x‖ ≤ (M : ℝ)) := by
  let T : ℕ → Set S := fun M ↦ {x | (∀ n, ‖fₙ n x‖ ≤ (M : ℝ)) ∧ ‖f x‖ ≤ (M : ℝ)}
  refine ⟨T, ?_, ?_, ?_, fun _ _ h ↦ h⟩
  · intro M
    have h := (NullMeasurableSet.iInter (fun n ↦
      nullMeasurableSet_le (hfₙ n).norm (aemeasurable_const (b := (M : ℝ))))).inter
        (nullMeasurableSet_le hf.norm (aemeasurable_const (b := (M : ℝ))))
    convert h using 1
    ext x
    simp [T]
  · intro M N hMN x hx
    exact ⟨fun n ↦ (hx.1 n).trans (by exact_mod_cast hMN),
      hx.2.trans (by exact_mod_cast hMN)⟩
  · filter_upwards [hconv] with x hx
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hx).exists_norm_le
    obtain ⟨M, hM⟩ := exists_nat_ge (max C ‖f x‖)
    exact ⟨M, fun n ↦ (hC _ ⟨n, rfl⟩).trans ((le_max_left _ _).trans hM),
      (le_max_right _ _).trans hM⟩

/-- Real integrals of uniformly bounded intercepts converge alongside all the
mixed-exponent weak pairings. -/
theorem bounded_affine_integral_tendsto [IsFiniteMeasure μ]
    {k : ℕ} {d : Fin k → ℕ} {r : Fin k → ℝ≥0∞}
    (hr : ∀ i, 1 < r i) (hrt : ∀ i, r i < ∞)
    [∀ i, Fact (1 ≤ r i)]
    (zₙ : (i : Fin k) → ℕ → Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ)
    (z : (i : Fin k) → Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ)
    (hz : ∀ i, Tendsto (fun n ↦ toWeakSpace ℝ _ (zₙ i n)) atTop
      (𝓝 (toWeakSpace ℝ _ (z i))))
    {cₙ : ℕ → S → ℝ} {c : S → ℝ}
    {bₙ : ℕ → (i : Fin k) → S → EuclideanSpace ℝ (Fin (d i))}
    {b : (i : Fin k) → S → EuclideanSpace ℝ (Fin (d i))}
    (hcₙ : ∀ n, AEMeasurable (cₙ n) μ) (hc : AEMeasurable c μ)
    (hbₙ : ∀ n i, AEMeasurable (bₙ n i) μ) (hb : ∀ i, AEMeasurable (b i) μ)
    (hcconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ cₙ n x) atTop (𝓝 (c x)))
    (hbconv : ∀ i, ∀ᵐ x ∂μ, Tendsto (fun n ↦ bₙ n i x) atTop (𝓝 (b i x)))
    {M : ℝ} (hM : 0 ≤ M)
    (hcbd : ∀ᵐ x ∂μ, (∀ n, ‖cₙ n x‖ ≤ M) ∧ ‖c x‖ ≤ M)
    (hbbd : ∀ i, ∀ᵐ x ∂μ, (∀ n, ‖bₙ n i x‖ ≤ M) ∧ ‖b i x‖ ≤ M) :
    (∀ n, Integrable (fun x ↦ cₙ n x + ∑ i, inner ℝ (bₙ n i x) (zₙ i n x)) μ) ∧
    Integrable (fun x ↦ c x + ∑ i, inner ℝ (b i x) (z i x)) μ ∧
    Tendsto (fun n ↦ ∫ x, cₙ n x + ∑ i, inner ℝ (bₙ n i x) (zₙ i n x) ∂μ)
      atTop (𝓝 (∫ x, c x + ∑ i, inner ℝ (b i x) (z i x) ∂μ)) := by
  have hcintₙ (n : ℕ) : Integrable (cₙ n) μ :=
    Integrable.of_bound (hcₙ n).aestronglyMeasurable M (hcbd.mono fun _ h ↦ h.1 n)
  have hcint : Integrable c μ :=
    Integrable.of_bound hc.aestronglyMeasurable M (hcbd.mono fun _ h ↦ h.2)
  have hpair (i : Fin k) := VariationalNotes.bounded_weakLp_pairing S μ (d i) (r i)
    (hr i) (hrt i) (zₙ i) (z i) (fun n ↦ bₙ n i) (b i) (hz i)
    (fun n ↦ hbₙ n i) (hb i) (hbconv i) ⟨M, hM, hbbd i⟩
  have hintₙ (n : ℕ) : Integrable
      (fun x ↦ cₙ n x + ∑ i, inner ℝ (bₙ n i x) (zₙ i n x)) μ :=
    (hcintₙ n).add (integrable_finsetSum _ (fun i _ ↦ (hpair i).1 n))
  have hint : Integrable (fun x ↦ c x + ∑ i, inner ℝ (b i x) (z i x)) μ :=
    hcint.add (integrable_finsetSum _ (fun i _ ↦ (hpair i).2.1))
  refine ⟨hintₙ, hint, ?_⟩
  have hct := tendsto_integral_of_dominated_convergence (fun _ ↦ M)
    (fun n ↦ (hcₙ n).aestronglyMeasurable) (integrable_const M)
    (fun n ↦ hcbd.mono fun _ h ↦ h.1 n) hcconv
  have hbt := tendsto_finsetSum Finset.univ (fun i _ ↦ (hpair i).2.2)
  have hsum := hct.add hbt
  simpa only [integral_add (hcintₙ _) (integrable_finsetSum _ (fun i _ ↦ (hpair i).1 _)),
    integral_add hcint (integrable_finsetSum _ (fun i _ ↦ (hpair i).2.1)),
    integral_finsetSum _ (fun i _ ↦ (hpair i).1 _),
    integral_finsetSum _ (fun i _ ↦ (hpair i).2.1)] using hsum

/-- The affine-test lower-limit estimate with no global coefficient bounds.
The test at the limit is nonnegative. All sequence tests may be signed. -/
theorem affine_test_lowerLimit [IsFiniteMeasure μ]
    {k : ℕ} {d : Fin k → ℕ} {r : Fin k → ℝ≥0∞}
    (hr : ∀ i, 1 < r i) (hrt : ∀ i, r i < ∞)
    [∀ i, Fact (1 ≤ r i)]
    (zₙ : (i : Fin k) → ℕ → Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ)
    (z : (i : Fin k) → Lp (EuclideanSpace ℝ (Fin (d i))) (r i) μ)
    (hz : ∀ i, Tendsto (fun n ↦ toWeakSpace ℝ _ (zₙ i n)) atTop
      (𝓝 (toWeakSpace ℝ _ (z i))))
    {cₙ : ℕ → S → ℝ} {c : S → ℝ}
    {bₙ : ℕ → (i : Fin k) → S → EuclideanSpace ℝ (Fin (d i))}
    {b : (i : Fin k) → S → EuclideanSpace ℝ (Fin (d i))}
    (hcₙ : ∀ n, AEMeasurable (cₙ n) μ) (hc : AEMeasurable c μ)
    (hbₙ : ∀ n i, AEMeasurable (bₙ n i) μ) (hb : ∀ i, AEMeasurable (b i) μ)
    (hcconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ cₙ n x) atTop (𝓝 (c x)))
    (hbconv : ∀ i, ∀ᵐ x ∂μ, Tendsto (fun n ↦ bₙ n i x) atTop (𝓝 (b i x)))
    {Fₙ : ℕ → S → ℝ}
    (hF0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ Fₙ n x)
    (hFtest : ∀ n, ∀ᵐ x ∂μ,
      cₙ n x + ∑ i, inner ℝ (bₙ n i x) (zₙ i n x) ≤ Fₙ n x)
    (h0 : ∀ᵐ x ∂μ, 0 ≤ c x + ∑ i, inner ℝ (b i x) (z i x)) :
    ((∫⁻ x, ENNReal.ofReal (c x + ∑ i, inner ℝ (b i x) (z i x)) ∂μ) : EReal) ≤
      liminf (fun n ↦ ((∫⁻ x, ENNReal.ofReal (Fₙ n x) ∂μ) : EReal)) atTop := by
  classical
  let fₙ : ℕ → S → ℝ × (∀ i, EuclideanSpace ℝ (Fin (d i))) :=
    fun n x ↦ (cₙ n x, fun i ↦ bₙ n i x)
  let f : S → ℝ × (∀ i, EuclideanSpace ℝ (Fin (d i))) :=
    fun x ↦ (c x, fun i ↦ b i x)
  have hfₙ (n : ℕ) : AEMeasurable (fₙ n) μ :=
    (hcₙ n).prodMk (aemeasurable_pi_iff.mpr (hbₙ n))
  have hf : AEMeasurable f μ := hc.prodMk (aemeasurable_pi_iff.mpr hb)
  have hfconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ fₙ n x) atTop (𝓝 (f x)) := by
    filter_upwards [hcconv, ae_all_iff.mpr hbconv] with x hc hb
    exact hc.prodMk_nhds (tendsto_pi_nhds.mpr hb)
  obtain ⟨T, hTm, hTmono, hTcover, hTbd⟩ := exists_bounded_localizations hfₙ hf hfconv
  let a : S → ℝ := fun x ↦ c x + ∑ i, inner ℝ (b i x) (z i x)
  have ha : AEMeasurable a μ := hc.add (Finset.aemeasurable_fun_sum _ (fun i _ ↦
    (hb i).inner ((Lp.aestronglyMeasurable (z i)).aemeasurable)))
  have hloc (M : ℕ) :
      ((∫⁻ x, ENNReal.ofReal ((T M).indicator a x) ∂μ) : EReal) ≤
        liminf (fun n ↦ ((∫⁻ x, ENNReal.ofReal (Fₙ n x) ∂μ) : EReal)) atTop := by
    let Cₙ : ℕ → S → ℝ := fun n ↦ (T M).indicator (cₙ n)
    let C : S → ℝ := (T M).indicator c
    let Bₙ : ℕ → (i : Fin k) → S → EuclideanSpace ℝ (Fin (d i)) :=
      fun n i ↦ (T M).indicator (bₙ n i)
    let B : (i : Fin k) → S → EuclideanSpace ℝ (Fin (d i)) :=
      fun i ↦ (T M).indicator (b i)
    have hCconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ Cₙ n x) atTop (𝓝 (C x)) := by
      filter_upwards [hcconv] with x hx
      by_cases hxT : x ∈ T M
      · simpa [Cₙ, C, hxT] using hx
      · simp [Cₙ, C, hxT]
    have hBconv (i) : ∀ᵐ x ∂μ, Tendsto (fun n ↦ Bₙ n i x) atTop (𝓝 (B i x)) := by
      filter_upwards [hbconv i] with x hx
      by_cases hxT : x ∈ T M
      · simpa [Bₙ, B, hxT] using hx
      · simp [Bₙ, B, hxT]
    have hCbd : ∀ᵐ x ∂μ, (∀ n, ‖Cₙ n x‖ ≤ (M : ℝ)) ∧ ‖C x‖ ≤ (M : ℝ) := by
      apply ae_of_all
      intro x
      by_cases hx : x ∈ T M
      · exact ⟨fun n ↦ by simpa [Cₙ, hx] using
          (norm_fst_le (fₙ n x)).trans ((hTbd M x hx).1 n),
          by simpa [C, hx] using (norm_fst_le (f x)).trans ((hTbd M x hx).2)⟩
      · simp [Cₙ, C, hx]
    have hBbd (i) : ∀ᵐ x ∂μ, (∀ n, ‖Bₙ n i x‖ ≤ (M : ℝ)) ∧ ‖B i x‖ ≤ (M : ℝ) := by
      apply ae_of_all
      intro x
      by_cases hx : x ∈ T M
      · constructor
        · intro n
          simpa [Bₙ, hx] using (norm_le_pi_norm (fun i ↦ bₙ n i x) i).trans
            ((norm_snd_le (fₙ n x)).trans ((hTbd M x hx).1 n))
        · simpa [B, hx] using (norm_le_pi_norm (fun i ↦ b i x) i).trans
            ((norm_snd_le (f x)).trans ((hTbd M x hx).2))
      · simp [Bₙ, B, hx]
    obtain ⟨hintₙ, hint, hconv⟩ := bounded_affine_integral_tendsto hr hrt zₙ z hz
      (fun n ↦ (hcₙ n).indicator₀ (hTm M)) (hc.indicator₀ (hTm M))
      (fun n i ↦ (hbₙ n i).indicator₀ (hTm M)) (fun i ↦ (hb i).indicator₀ (hTm M))
      hCconv hBconv (Nat.cast_nonneg M) hCbd hBbd
    have heq : (fun x ↦ C x + ∑ i, inner ℝ (B i x) (z i x)) = (T M).indicator a := by
      ext x
      by_cases hx : x ∈ T M <;> simp [C, B, a, hx]
    rw [heq] at hint hconv
    have hapos : 0 ≤ᵐ[μ] (T M).indicator a := by
      filter_upwards [h0] with x hx
      by_cases hxT : x ∈ T M <;> simp [hxT, a, hx]
    have hcompare (n : ℕ) :
        ((∫ x, Cₙ n x + ∑ i, inner ℝ (Bₙ n i x) (zₙ i n x) ∂μ : ℝ) : EReal) ≤
          ((∫⁻ x, ENNReal.ofReal (Fₙ n x) ∂μ) : EReal) := by
      apply integral_coe_le_lintegral_ofReal (hintₙ n)
      filter_upwards [hFtest n, hF0 n] with x hx h0x
      by_cases hxT : x ∈ T M
      · simpa [Cₙ, Bₙ, hxT] using hx
      · simpa [Cₙ, Bₙ, hxT] using h0x
    have heconv : Tendsto (fun n ↦
        ((∫ x, Cₙ n x + ∑ i, inner ℝ (Bₙ n i x) (zₙ i n x) ∂μ : ℝ) : EReal))
        atTop (𝓝 ((∫ x, (T M).indicator a x ∂μ : ℝ) : EReal)) :=
      continuous_coe_real_ereal.continuousAt.tendsto.comp hconv
    have hle := liminf_le_liminf (f := atTop) (Filter.Eventually.of_forall hcompare)
    rw [heconv.liminf_eq] at hle
    convert hle using 1
    rw [← ofReal_integral_eq_lintegral_ofReal hint hapos, EReal.coe_ennreal_ofReal,
      max_eq_left (integral_nonneg_of_ae hapos)]
  have hmon : ∀ᵐ x ∂μ, Monotone (fun M ↦ ENNReal.ofReal ((T M).indicator a x)) := by
    filter_upwards [h0] with x hx
    intro M N hMN
    by_cases hxM : x ∈ T M
    · have hxN := hTmono hMN hxM
      simp [hxM, hxN]
    · simp only [indicator_of_notMem hxM, ENNReal.ofReal_zero]
      positivity
  have hconv : ∀ᵐ x ∂μ, Tendsto
      (fun M ↦ ENNReal.ofReal ((T M).indicator a x)) atTop (𝓝 (ENNReal.ofReal (a x))) := by
    filter_upwards [hTcover] with x hx
    obtain ⟨M, hxM⟩ := hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop M] with N hMN
    simp [hTmono hMN hxM]
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (fun M ↦ ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (ha.indicator₀ (hTm M))) hmon hconv
  exact le_of_tendsto (continuous_coe_ennreal_ereal.continuousAt.tendsto.comp hlim)
    (Filter.Eventually.of_forall hloc)

/-- The first `N` affine values together with zero, expressed recursively. -/
def finiteAffineMax (v : ℕ → S → ℝ) : ℕ → S → ℝ
  | 0 => fun _ ↦ 0
  | N + 1 => fun x ↦ max (finiteAffineMax v N x) (v N x)

omit [MeasurableSpace S] in
lemma finiteAffineMax_nonneg (v : ℕ → S → ℝ) (N : ℕ) (x : S) :
    0 ≤ finiteAffineMax v N x := by
  induction N with
  | zero => exact le_rfl
  | succ N hN => exact hN.trans (le_max_left _ _)

omit [MeasurableSpace S] in
lemma finiteAffineMax_monotone (v : ℕ → S → ℝ) (x : S) :
    Monotone (fun N ↦ finiteAffineMax v N x) := by
  apply monotone_nat_of_le_succ
  intro N
  exact le_max_left _ _

lemma finiteAffineMax_aemeasurable {v : ℕ → S → ℝ}
    (hv : ∀ j, AEMeasurable (v j) μ) (N : ℕ) :
    AEMeasurable (finiteAffineMax v N) μ := by
  induction N with
  | zero => exact aemeasurable_const
  | succ N hN => exact hN.max (hv N)

omit [MeasurableSpace S] in
lemma finiteAffineMax_le {v : ℕ → S → ℝ} {x : S} {g : ℝ}
    (h0 : 0 ≤ g) (hv : ∀ j, v j x ≤ g) (N : ℕ) : finiteAffineMax v N x ≤ g := by
  induction N with
  | zero => exact h0
  | succ N hN => exact max_le hN (hv N)

omit [MeasurableSpace S] in
lemma finiteAffineMax_tendsto {v : ℕ → S → ℝ} {x : S} {g : ℝ}
    (hv : IsLUB ({0} ∪ Set.range (fun j ↦ v j x)) g) :
    Tendsto (fun N ↦ finiteAffineMax v N x) atTop (𝓝 g) := by
  apply tendsto_atTop_isLUB (finiteAffineMax_monotone v x)
  constructor
  · rintro _ ⟨N, rfl⟩
    exact finiteAffineMax_le (hv.1 (Or.inl (by simp)))
      (fun j ↦ hv.1 (Or.inr ⟨j, rfl⟩)) N
  · intro q hq
    apply hv.2
    rintro a (ha | ⟨j, rfl⟩)
    · have ha0 : a = 0 := by simpa using ha
      subst a
      exact hq ⟨0, rfl⟩
    · exact (le_max_right _ _).trans (hq ⟨j + 1, rfl⟩)

private theorem aemeasurable_ite_null {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {T : Set S} [DecidablePred (· ∈ T)] (hT : NullMeasurableSet T μ) {f g : S → E}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x ↦ if x ∈ T then f x else g x) μ := by
  classical
  convert (hf.indicator₀ hT).add (hg.indicator₀ hT.compl) using 1
  ext x
  by_cases hx : x ∈ T <;> simp [hx]

/-- Measurably choose a maximizing test from each finite initial list, including
zero. The comparison is made at the LIMIT, so each choice is held fixed while
`n` varies. This gives a.e. converging coefficients even though the fibers only
converge weakly. -/
theorem exists_finite_max_tests {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (eval : S → E → ℝ) (evalₙ : ℕ → S → E → ℝ)
    (heval : ∀ q : S → E, AEMeasurable q μ → AEMeasurable (fun x ↦ eval x (q x)) μ)
    (heval0 : ∀ x, eval x 0 = 0) (hevalₙ0 : ∀ n x, evalₙ n x 0 = 0)
    (fₙ : ℕ → ℕ → S → E) (f : ℕ → S → E)
    (hfₙ : ∀ j n, AEMeasurable (fₙ j n) μ) (hf : ∀ j, AEMeasurable (f j) μ)
    (hconv : ∀ j, ∀ᵐ x ∂μ, Tendsto (fun n ↦ fₙ j n x) atTop (𝓝 (f j x)))
    {Fₙ : ℕ → S → ℝ} (hF0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ Fₙ n x)
    (hF : ∀ j n, ∀ᵐ x ∂μ, evalₙ n x (fₙ j n x) ≤ Fₙ n x) (N : ℕ) :
    ∃ (qₙ : ℕ → S → E) (q : S → E),
      (∀ n, AEMeasurable (qₙ n) μ) ∧ AEMeasurable q μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n ↦ qₙ n x) atTop (𝓝 (q x))) ∧
      (∀ n, ∀ᵐ x ∂μ, evalₙ n x (qₙ n x) ≤ Fₙ n x) ∧
      (∀ x, eval x (q x) = finiteAffineMax (fun j x ↦ eval x (f j x)) N x) := by
  classical
  induction N with
  | zero =>
    refine ⟨fun _ _ ↦ 0, fun _ ↦ 0, fun _ ↦ aemeasurable_const, aemeasurable_const,
      ae_of_all _ (fun _ ↦ tendsto_const_nhds), ?_, ?_⟩
    · intro n
      simpa only [hevalₙ0] using hF0 n
    · intro x
      exact heval0 x
  | succ N hN =>
    obtain ⟨qₙ, q, hqₙ, hq, hqconv, hqF, hqeq⟩ := hN
    let T : Set S := {x | eval x (q x) ≤ eval x (f N x)}
    have hT : NullMeasurableSet T μ := nullMeasurableSet_le (heval q hq) (heval (f N) (hf N))
    let Qₙ : ℕ → S → E := fun n x ↦ if x ∈ T then fₙ N n x else qₙ n x
    let Q : S → E := fun x ↦ if x ∈ T then f N x else q x
    refine ⟨Qₙ, Q, fun n ↦ aemeasurable_ite_null hT (hfₙ N n) (hqₙ n),
      aemeasurable_ite_null hT (hf N) hq, ?_, ?_, ?_⟩
    · filter_upwards [hconv N, hqconv] with x hx hqx
      by_cases hxT : x ∈ T
      · simpa [Qₙ, Q, hxT] using hx
      · simpa [Qₙ, Q, hxT] using hqx
    · intro n
      filter_upwards [hF N n, hqF n] with x hx hqx
      by_cases hxT : x ∈ T
      · simpa [Qₙ, hxT] using hx
      · simpa [Qₙ, hxT] using hqx
    · intro x
      by_cases hxT : x ∈ T
      · have hx : eval x (q x) ≤ eval x (f N x) := hxT
        simpa [Q, hxT, finiteAffineMax, ← hqeq x] using (max_eq_right hx).symm
      · have hx : eval x (f N x) ≤ eval x (q x) := le_of_not_ge hxT
        simpa [Q, hxT, finiteAffineMax, ← hqeq x] using (max_eq_left hx).symm

/-- The countable affine envelope gives integral lower semicontinuity under a.e.
state convergence and native weak convergence in each independent fiber. -/
theorem affineEnvelope_lowerLimit : AffineEnvelopeSpecs.AffineEnvelopeLowerLimit := by
  intro S _ μ _ m k d r hr hrt
  let : ∀ i, Fact (1 ≤ r i) := fun i ↦ ⟨(hr i).le⟩
  intro G c b sₙ s zₙ z hG hG0 henv hsₙ hs hsconv hz
  classical
  obtain ⟨hccont, hbcont, hcmeas, hbmeas, hrep⟩ := henv
  let E := ℝ × (∀ i, EuclideanSpace ℝ (Fin (d i)))
  let eval : S → E → ℝ := fun x q ↦ q.1 + ∑ i, inner ℝ (q.2 i) (z i x)
  let evalₙ : ℕ → S → E → ℝ := fun n x q ↦ q.1 + ∑ i, inner ℝ (q.2 i) (zₙ i n x)
  let fₙ : ℕ → ℕ → S → E := fun j n x ↦
    (c j x (sₙ n x), fun i ↦ b j i x (sₙ n x))
  let f : ℕ → S → E := fun j x ↦ (c j x (s x), fun i ↦ b j i x (s x))
  let Fₙ : ℕ → S → ℝ := fun n x ↦ G x (sₙ n x) (fun i ↦ zₙ i n x)
  let F : S → ℝ := fun x ↦ G x (s x) (fun i ↦ z i x)
  let v : ℕ → S → ℝ := fun j x ↦ eval x (f j x)
  have heval (q : S → E) (hq : AEMeasurable q μ) :
      AEMeasurable (fun x ↦ eval x (q x)) μ := by
    exact hq.fst.add (Finset.aemeasurable_fun_sum _ (fun i _ ↦
      (aemeasurable_pi_iff.mp hq.snd i).inner
        (Lp.aestronglyMeasurable (z i)).aemeasurable))
  have heval0 (x) : eval x 0 = 0 := by simp [eval]
  have hevalₙ0 (n x) : evalₙ n x 0 = 0 := by simp [evalₙ]
  have hfₙ (j n) : AEMeasurable (fₙ j n) μ :=
    (hcmeas j (sₙ n) (hsₙ n)).prodMk
      (aemeasurable_pi_iff.mpr (fun i ↦ hbmeas j i (sₙ n) (hsₙ n)))
  have hf (j) : AEMeasurable (f j) μ :=
    (hcmeas j s hs).prodMk (aemeasurable_pi_iff.mpr (fun i ↦ hbmeas j i s hs))
  have hfconv (j) : ∀ᵐ x ∂μ, Tendsto (fun n ↦ fₙ j n x) atTop (𝓝 (f j x)) := by
    filter_upwards [hsconv] with x hx
    exact ((hccont j x).tendsto (s x) |>.comp hx).prodMk_nhds
      (tendsto_pi_nhds.mpr (fun i ↦ (hbcont j i x).tendsto (s x) |>.comp hx))
  have hF0 (n) : ∀ᵐ x ∂μ, 0 ≤ Fₙ n x := hG0.mono fun x hx ↦ hx _ _
  have hFtest (j n) : ∀ᵐ x ∂μ, evalₙ n x (fₙ j n x) ≤ Fₙ n x := by
    filter_upwards [hrep] with x hx
    exact (hx (sₙ n x) (fun i ↦ zₙ i n x)).1 j
  have hv (j) : AEMeasurable (v j) μ := heval (f j) (hf j)
  have hN (N : ℕ) :
      ((∫⁻ x, ENNReal.ofReal (finiteAffineMax v N x) ∂μ) : EReal) ≤
        liminf (fun n ↦ ((∫⁻ x, ENNReal.ofReal (Fₙ n x) ∂μ) : EReal)) atTop := by
    obtain ⟨qₙ, q, hqₙ, hq, hqconv, hqF, hqeq⟩ := exists_finite_max_tests
      eval evalₙ heval heval0 hevalₙ0 fₙ f hfₙ hf hfconv hF0 hFtest N
    have hq0 : ∀ᵐ x ∂μ, 0 ≤ (q x).1 + ∑ i, inner ℝ ((q x).2 i) (z i x) := by
      apply ae_of_all
      intro x
      change 0 ≤ eval x (q x)
      rw [hqeq x]
      exact finiteAffineMax_nonneg v N x
    have hbound := affine_test_lowerLimit hr hrt zₙ z hz
      (fun n ↦ (hqₙ n).fst) hq.fst
      (fun n i ↦ aemeasurable_pi_iff.mp (hqₙ n).snd i)
      (fun i ↦ aemeasurable_pi_iff.mp hq.snd i)
      (hqconv.mono fun x hx ↦ hx.fst_nhds)
      (fun i ↦ hqconv.mono fun x hx ↦
        tendsto_pi_nhds.mp hx.snd_nhds i)
      hF0 hqF hq0
    have heq : (fun x ↦ (q x).1 + ∑ i, inner ℝ ((q x).2 i) (z i x)) =
        finiteAffineMax v N := funext hqeq
    rw [← heq]
    exact hbound
  have hmaxconv : ∀ᵐ x ∂μ, Tendsto (fun N ↦ ENNReal.ofReal (finiteAffineMax v N x))
      atTop (𝓝 (ENNReal.ofReal (F x))) := by
    filter_upwards [hrep] with x hx
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    exact finiteAffineMax_tendsto (hx (s x) (fun i ↦ z i x)).2
  have hmaxmono : ∀ᵐ x ∂μ, Monotone (fun N ↦ ENNReal.ofReal (finiteAffineMax v N x)) :=
    ae_of_all _ (fun x ↦ ENNReal.ofReal_mono.comp (finiteAffineMax_monotone v x))
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (fun N ↦ ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (finiteAffineMax_aemeasurable hv N)) hmaxmono hmaxconv
  have hfinal := le_of_tendsto
    (continuous_coe_ennreal_ereal.continuousAt.tendsto.comp hlim)
    (Filter.Eventually.of_forall hN)
  have hFnonneg : ∀ᵐ x ∂μ, 0 ≤ F x := hG0.mono fun x hx ↦ hx _ _
  change extendedIntegral μ F ≤ liminf (fun n ↦ extendedIntegral μ (Fₙ n)) atTop
  rw [extendedIntegral_of_nonneg hFnonneg]
  have heq (n) := extendedIntegral_of_nonneg (hF0 n)
  simpa only [heq] using hfinal

end VariationalNotes.Sobolev
