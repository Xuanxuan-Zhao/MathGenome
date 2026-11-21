import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.AtomicHardySpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.CalderonZygmundDecomposition
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyPAtoms
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe v

namespace ExpandedFA.Hardy.HardyPAtoms
open HardyPAtomsSpec

/-- The elementary finite-p estimate for an infinity-atom. -/
lemma ball_bound_pnorm {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : AEStronglyMeasurable f volume)
    (c : Point d) (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hb : ∀ᵐ x ∂volume, (x ∉ Metric.ball c r → f x = 0) ∧
      ‖f x‖ ≤ (volume.real (Metric.ball c r))⁻¹) :
    MemLp f (ENNReal.ofReal p) volume ∧
    (eLpNorm f (ENNReal.ofReal p) volume).toReal ≤
      (volume.real (Metric.ball c r)) ^ (1 / p - 1) := by
  let B := Metric.ball c r
  let M : ℝ := (volume.real B)⁻¹
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hpos : 0 < volume.real B := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  have hM : 0 ≤ M := inv_nonneg.mpr hpos.le
  let g := B.indicator (fun _ : Point d => M)
  have hg : MemLp g (ENNReal.ofReal p) volume :=
    memLp_indicator_const _ hB.nullMeasurableSet M (Or.inr measure_ball_ne_top)
  have hfg : ∀ᵐ x ∂volume, ‖f x‖ ≤ ‖g x‖ := by
    filter_upwards [hb] with x hx
    by_cases hxB : x ∈ B
    · simpa [g, Set.indicator_of_mem hxB, abs_of_nonneg hM] using hx.2
    · simp [g, Set.indicator_of_notMem hxB, hx.1 hxB]
  refine ⟨hg.mono hf hfg, ?_⟩
  calc
    (eLpNorm f (ENNReal.ofReal p) volume).toReal ≤
        (eLpNorm g (ENNReal.ofReal p) volume).toReal :=
      ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_ae hf hfg)
    _ = M * (volume.real B) ^ (1 / p) := by
      rw [eLpNorm_indicator_const hB.nullMeasurableSet (ENNReal.ofReal_pos.mpr hp).ne'
        ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
      simp [ENNReal.toReal_ofReal hp.le, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg hM, ENNReal.toReal_ofReal hM, Measure.real]
    _ = (volume.real B) ^ (1 / p - 1) := by
      rw [Real.rpow_sub_one hpos.ne']
      simp only [M, div_eq_mul_inv, mul_comm]

/-- Every source infinity-atom satisfies the finite-p atom conditions. -/
theorem infinityAtoms_are_pAtoms : InfinityAtomsArePAtoms.{v} := by
  intro d p hp 𝕜 _ a
  obtain ⟨c, r, hr, hμ0, hμtop, hb⟩ := a.property.2
  obtain ⟨hm, hn⟩ := ball_bound_pnorm a.val (Lp.aestronglyMeasurable a.val)
    c r p hr (zero_lt_one.trans hp) hb
  exact ⟨hm, a.property.1, c, r, hr, hb.mono (fun _ hx => hx.1), hn⟩

/-- Actual summation in the accepted Hardy quotient gives the uniform bound. -/
theorem expansion_to_bound : ExpansionToBound.{v} := by
  intro hex d p hp
  obtain ⟨C, hC, h⟩ := hex d p hp
  refine ⟨C, hC, fun {𝕜} _ a => ?_⟩
  obtain ⟨b, c, hc, hs, hn⟩ := h a
  obtain ⟨u, hu, hnu⟩ := AtomicHardySpace.sequence_series volume b c hc
  exact ⟨u, hu.unique hs, hnu.trans hn⟩

section Transport
variable {d : ℕ} {p : ℝ} {𝕜 : Type v} [RCLike 𝕜]

lemma pAtomicNorm_bddBelow {f : L1 d 𝕜} :
    BddBelow {r : ℝ | ∃ a : ℕ → PAtom d p 𝕜, ∃ c : ℕ → 𝕜,
      Summable (fun j => ‖c j‖) ∧ HasSum (fun j => c j • (a j).val) f ∧
      (∑' j, ‖c j‖) = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, c, hc, hs, rfl⟩
  exact tsum_nonneg (fun _ => norm_nonneg _)

/-- Summation takes place in the complete Hardy space; its continuous L¹ map
identifies the sum with the supplied p-atomic series. -/
lemma lift_p_series {C : ℝ} (_hC : 0 ≤ C)
    (ha : ∀ a : PAtom d p 𝕜, ∃ u : H1 d 𝕜,
      AtomicHardySpaceSpec.EmbeddingValue volume u = a.val ∧ ‖u‖ ≤ C)
    (a : ℕ → PAtom d p 𝕜) (c : ℕ → 𝕜)
    (hc : Summable (fun j => ‖c j‖)) {f : L1 d 𝕜}
    (hs : HasSum (fun j => c j • (a j).val) f) :
    ∃ u : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume u = f ∧
      ‖u‖ ≤ C * ∑' j, ‖c j‖ := by
  classical
  choose u hu hn using ha
  have hnc : Summable (fun j => C * ‖c j‖) := hc.mul_left C
  have hv : Summable (fun j => c j • u (a j)) := by
    apply hnc.of_norm_bounded
    intro j
    rw [norm_smul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hn (a j)) (norm_nonneg (c j))
  refine ⟨∑' j, c j • u (a j), ?_, ?_⟩
  · have hm := hv.hasSum.mapL (AtomicHardySpaceSpec.EmbeddingValue volume)
    simp only [map_smul, hu] at hm
    exact hm.unique hs
  · rw [← tsum_mul_left]
    apply hv.hasSum.norm_le_of_bounded hnc.hasSum
    intro j
    rw [norm_smul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hn (a j)) (norm_nonneg (c j))

/-- Hölder on the essential supporting ball, with the original global Lp
norm on the right. This is the quantitative L¹ bridge for normalized p-atoms. -/
lemma ball_holder (hp : 1 < p) (f : L1 d 𝕜)
    (hf : MemLp f (ENNReal.ofReal p) volume) (c : Point d) (r : ℝ) (hr : 0 < r)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) :
    ‖f‖ ≤ (eLpNorm f (ENNReal.ofReal p) volume).toReal *
      (volume.real (Metric.ball c r)) ^ (1 - 1 / p) := by
  let B := Metric.ball c r
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have he : B.indicator (⇑f) =ᵐ[volume] ⇑f := by
    filter_upwards [hs] with x hx
    by_cases hxB : x ∈ B
    · exact Set.indicator_of_mem hxB _
    · simpa only [Set.indicator_of_notMem hxB] using (hx hxB).symm
  have hple : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hcmp : eLpNorm f 1 volume ≤
      eLpNorm f (ENNReal.ofReal p) volume * volume B ^ (1 - 1 / p) := by
    calc
      eLpNorm f 1 volume = eLpNorm f 1 (volume.restrict B) := by
        rw [← eLpNorm_congr_ae he, eLpNorm_indicator_eq_eLpNorm_restrict hB.nullMeasurableSet]
      _ ≤ eLpNorm f (ENNReal.ofReal p) (volume.restrict B) *
          volume B ^ (1 - 1 / p) := by
        simpa only [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one,
          ENNReal.toReal_ofReal (zero_lt_one.trans hp).le] using
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hple hf.aestronglyMeasurable.restrict
      _ ≤ eLpNorm f (ENNReal.ofReal p) volume * volume B ^ (1 - 1 / p) :=
        mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self) le_rfl
  rw [Lp.norm_def]
  have hfin : eLpNorm f (ENNReal.ofReal p) volume * volume B ^ (1 - 1 / p) ≠ ∞ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (Metric.measure_ball_pos volume c hr).ne'
        measure_ball_ne_top)
  convert ENNReal.toReal_mono hfin hcmp using 1
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  rfl

lemma pAtom_norm_le_one (hp : 1 < p) (a : PAtom d p 𝕜) : ‖a.val‖ ≤ 1 := by
  obtain ⟨hf, hz, c, r, hr, hs, hn⟩ := a.property
  have hb : 0 < volume.real (Metric.ball c r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  calc
    ‖a.val‖ ≤ (eLpNorm a.val (ENNReal.ofReal p) volume).toReal *
        (volume.real (Metric.ball c r)) ^ (1 - 1 / p) :=
      ball_holder hp a.val hf c r hr hs
    _ ≤ (volume.real (Metric.ball c r)) ^ (1 / p - 1) *
        (volume.real (Metric.ball c r)) ^ (1 - 1 / p) :=
      mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hb.le _)
    _ = 1 := by rw [← Real.rpow_add hb, sub_add_sub_cancel, sub_self, Real.rpow_zero]

/-- The L¹ hypothesis in the quotient atom type follows from the source's
raw finite-p and finite-ball hypotheses, even for merely essential support. -/
lemma raw_pAtom_realization (hp : 1 < p) (f : Point d → 𝕜)
    (hf : MemLp f (ENNReal.ofReal p) volume) (hz : (∫ x, f x) = 0)
    (hb : ∃ c : Point d, ∃ r : ℝ, 0 < r ∧
      (∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) ∧
      (eLpNorm f (ENNReal.ofReal p) volume).toReal ≤
        (volume.real (Metric.ball c r)) ^ (1 / p - 1)) :
    ∃ a : PAtom d p 𝕜, a.val =ᵐ[volume] f := by
  obtain ⟨c, r, hr, hs, hn⟩ := hb
  let B := Metric.ball c r
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have he : B.indicator f =ᵐ[volume] f := by
    filter_upwards [hs] with x hx
    by_cases hxB : x ∈ B
    · exact Set.indicator_of_mem hxB _
    · simpa only [Set.indicator_of_notMem hxB] using (hx hxB).symm
  let : IsFiniteMeasure (volume.restrict B) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume B < ∞)⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hfi : Integrable f volume :=
    ((integrable_indicator_iff hB).mpr
      (MemLp.integrable hp1 (hf.mono_measure Measure.restrict_le_self))).congr he
  let F : L1 d 𝕜 := hfi.toL1 f
  have hF : ⇑F =ᵐ[volume] f := hfi.coeFn_toL1
  refine ⟨⟨F, hf.ae_eq hF.symm, (integral_congr_ae hF).trans hz,
    c, r, hr, ?_, ?_⟩, hF⟩
  · filter_upwards [hF, hs] with x hx hxB
    simpa only [hx] using hxB
  · rwa [eLpNorm_congr_ae hF]

/-- Any ball-supported mean-zero Lp class is a scalar multiple of a p-atom.
The strictly positive normalization also handles the zero function. -/
lemma normalize_ball (f : L1 d 𝕜) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hz : (∫ x, f x) = 0) (c : Point d) (r : ℝ) (hr : 0 < r)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) :
    ∃ k : 𝕜, ∃ a : PAtom d p 𝕜, k • a.val = f := by
  let B := Metric.ball c r
  let b : ℝ := (volume.real B) ^ (1 / p - 1)
  have hb : 0 < b := Real.rpow_pos_of_pos
    (ENNReal.toReal_pos (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top) _
  let N : ℝ := (eLpNorm f (ENNReal.ofReal p) volume).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  let A : ℝ := N / b + 1
  have hA : 0 < A := add_pos_of_nonneg_of_pos (div_nonneg hN hb.le) zero_lt_one
  let k : 𝕜 := algebraMap ℝ 𝕜 A
  have hk : k ≠ 0 := by
    change algebraMap ℝ 𝕜 A ≠ 0
    exact (map_ne_zero (algebraMap ℝ 𝕜)).mpr hA.ne'
  have hkn : ‖k‖ = A := by
    change ‖(A : 𝕜)‖ = A
    rw [RCLike.norm_ofReal, abs_of_pos hA]
  have hsm : ⇑(k⁻¹ • f) =ᵐ[volume] k⁻¹ • ⇑f := Lp.coeFn_smul _ _
  have hm : MemLp (⇑(k⁻¹ • f)) (ENNReal.ofReal p) volume :=
    (hf.const_smul k⁻¹).ae_eq hsm.symm
  have hi : N ≤ A * b := by
    rw [← div_le_iff₀ hb]
    exact le_add_of_nonneg_right zero_le_one
  have hn : (eLpNorm (⇑(k⁻¹ • f)) (ENNReal.ofReal p) volume).toReal ≤ b := by
    rw [eLpNorm_congr_ae hsm, eLpNorm_const_smul, ENNReal.toReal_mul]
    rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), norm_inv, hkn]
    exact (inv_mul_le_iff₀ hA).mpr hi
  have hzero : (∫ x, (k⁻¹ • f) x) = 0 := by
    rw [integral_congr_ae hsm]
    change (∫ x, k⁻¹ • f x) = 0
    rw [integral_smul, hz, smul_zero]
  have hsup : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → (k⁻¹ • f) x = 0 := by
    filter_upwards [hsm, hs] with x hx hxs
    intro hxB
    simp [hx, hxs hxB]
  refine ⟨k, ⟨k⁻¹ • f, hm, hzero, c, r, hr, hsup, hn⟩, ?_⟩
  exact smul_inv_smul₀ hk f

/-- Absolute Hardy estimates on telescoping increments, together with an L¹
limit of the good approximations, give an actual Hardy element at that limit. -/
lemma hardy_of_telescope (g : ℕ → L1 d 𝕜) (f : L1 d 𝕜)
    (hg : Tendsto g atTop (𝓝 f)) (A : ℕ → ℝ) (hA : Summable A)
    (hinit : ∃ u : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume u = g 0 ∧
      ‖u‖ ≤ A 0)
    (hstep : ∀ n, ∃ u : H1 d 𝕜,
      AtomicHardySpaceSpec.EmbeddingValue volume u = g (n + 1) - g n ∧
      ‖u‖ ≤ A (n + 1)) :
    ∃ u : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume u = f ∧
      ‖u‖ ≤ ∑' n, A n := by
  classical
  obtain ⟨u₀, hu₀, hn₀⟩ := hinit
  choose v hv hn using hstep
  have htail : Summable (fun n => A (n + 1)) := hA.comp_injective
    (fun n m h => Nat.add_right_cancel h)
  have hvs : Summable v := htail.of_norm_bounded hn
  have him : HasSum (fun n => g (n + 1) - g n)
      (AtomicHardySpaceSpec.EmbeddingValue volume (∑' n, v n)) := by
    simpa only [hv] using hvs.hasSum.mapL (AtomicHardySpaceSpec.EmbeddingValue volume)
  have hlim : AtomicHardySpaceSpec.EmbeddingValue volume (∑' n, v n) = f - g 0 := by
    apply tendsto_nhds_unique him.tendsto_sum_nat
    simpa only [Finset.sum_range_sub] using hg.sub_const (g 0)
  refine ⟨u₀ + ∑' n, v n, ?_, ?_⟩
  · rw [map_add, hu₀, hlim, add_sub_cancel]
  · calc
      ‖u₀ + ∑' n, v n‖ ≤ ‖u₀‖ + ‖∑' n, v n‖ := norm_add_le _ _
      _ ≤ A 0 + ∑' n, A (n + 1) := add_le_add hn₀
        (hvs.hasSum.norm_le_of_bounded htail.hasSum hn)
      _ = ∑' n, A n := by simpa using hA.sum_add_tsum_nat_add 1

/-- The zero-dimensional case is retained: mean-zero L¹ is the zero class. -/
lemma zero_dim_mean_zero (f : L1 0 𝕜) (hz : (∫ x, f x) = 0) : f = 0 := by
  have hzero : f 0 = 0 := by
    simpa only [volume_euclideanSpace_eq_dirac, integral_dirac] using hz
  apply Lp.ext
  filter_upwards [Lp.coeFn_zero 𝕜 1 (volume : Measure (Point 0))] with x hx
  have he : x = 0 := Subsingleton.elim _ _
  simpa only [he, hzero, Pi.zero_apply] using hx.symm

end Transport

/-- The accepted quotient norm and countable reindexing produce an actual
infinity-atomic sequence from a Hardy lift, with arbitrarily small norm slack. -/
lemma expansion_of_hardy_bound {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (u : H1 d 𝕜) (C : ℝ) (hC : ‖u‖ ≤ C) :
    ∃ b : ℕ → InfinityAtom d 𝕜, ∃ c : ℕ → 𝕜,
      Summable (fun j => ‖c j‖) ∧
      HasSum (fun j => c j • (b j).val)
        (AtomicHardySpaceSpec.EmbeddingValue volume u) ∧ (∑' j, ‖c j‖) ≤ C + 1 := by
  classical
  let μ : Measure (Point d) := volume
  let := AtomicHardySpace.euclidean_atoms_nonempty d 𝕜
  obtain ⟨c, hc, hn⟩ := Submodule.Quotient.norm_mk_lt u zero_lt_one
  obtain ⟨b, a, ha, hs⟩ := AtomicHardySpace.coefficient_sequence μ c
  have he : AtomicHardySpaceSpec.SynthesisValue μ c =
      AtomicHardySpaceSpec.EmbeddingValue μ u :=
    congrArg (AtomicHardySpaceSpec.EmbeddingValue μ) hc
  exact ⟨b, a, ha.summable, he ▸ hs, ha.tsum_eq.trans_le (hn.le.trans (add_le_add hC (le_refl 1)))⟩

theorem bound_to_expansion : BoundToExpansion.{v} := by
  intro hb d p hp
  obtain ⟨C, hC, hA⟩ := hb d p hp
  refine ⟨C + 1, by linarith, fun {𝕜} _ a => ?_⟩
  obtain ⟨u, hu, hn⟩ := hA a
  obtain ⟨b, c, hc, hs, hnc⟩ := expansion_of_hardy_bound u C hn
  exact ⟨b, c, hc, hu ▸ hs, hnc⟩

theorem pAtom_l1_bound : PAtomL1Bound.{v} := by
  intro d p hp 𝕜 _ a
  exact pAtom_norm_le_one hp a

theorem pAtomic_synthesis : PAtomicSynthesis.{v} := by
  intro d p hp 𝕜 _ a c hc
  have hs : Summable (fun j => c j • (a j).val) := by
    apply hc.of_norm_bounded
    intro j
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (pAtom_norm_le_one hp (a j))
  refine ⟨_, hs.hasSum, ?_⟩
  apply hs.hasSum.norm_le_of_bounded hc.hasSum
  intro j
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (pAtom_norm_le_one hp (a j))

theorem bound_to_rawAtomBound : BoundToRawAtomBound.{v} := by
  intro hb d p hp
  obtain ⟨C, hC, hA⟩ := hb d p hp
  refine ⟨C, hC, fun {𝕜} _ f hf hz hs => ?_⟩
  obtain ⟨a, ha⟩ := raw_pAtom_realization hp f hf hz hs
  obtain ⟨u, hu, hn⟩ := hA a
  exact ⟨u, hu ▸ ha, hn⟩

/-- Equality of spaces and norm equivalence follow by complete-space summation
and the exact coefficient-infimum formulas; no flattening of formal sums is used. -/
theorem bound_to_equivalentNorm : BoundToEquivalentNorm.{v} := by
  classical
  intro hinf hbound d p hp
  obtain ⟨C, hC, hA⟩ := hbound d p hp
  refine ⟨C, hC, fun {𝕜} _ f => ?_⟩
  have hforward : (∃ h : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume h = f) →
      HasPAtomicSeries d p f := by
    intro hf
    obtain ⟨a, c, hc, hs⟩ := (AtomicHardySpace.euclidean_sequence_range d f).mp hf
    exact ⟨fun j => ⟨a j, hinf d p hp (a j)⟩, c, hc, hs⟩
  refine ⟨⟨hforward, ?_⟩, ?_⟩
  · rintro ⟨a, c, hc, hs⟩
    obtain ⟨u, hu, hn⟩ := lift_p_series hC.le hA a c hc hs
    exact ⟨u, hu⟩
  · intro u hu
    have hP : HasPAtomicSeries d p f := hforward ⟨u, hu⟩
    have hR : {r : ℝ | ∃ a : ℕ → PAtom d p 𝕜, ∃ c : ℕ → 𝕜,
      Summable (fun j => ‖c j‖) ∧ HasSum (fun j => c j • (a j).val) f ∧
      (∑' j, ‖c j‖) = r}.Nonempty := by
      obtain ⟨a, c, hc, hs⟩ := hP
      exact ⟨_, a, c, hc, hs, rfl⟩
    constructor
    · rw [AtomicHardySpace.euclidean_sequence_norm d u]
      apply le_csInf
      · obtain ⟨a, c, hc, hs⟩ := (AtomicHardySpace.euclidean_sequence_range d f).mp ⟨u, hu⟩
        exact ⟨_, a, c, hc, hu ▸ hs, rfl⟩
      · rintro r ⟨a, c, hc, hs, rfl⟩
        apply csInf_le (pAtomicNorm_bddBelow (f := f))
        exact ⟨fun j => ⟨a j, hinf d p hp (a j)⟩, c, hc, hu ▸ hs, rfl⟩
    · have hle : ‖u‖ / C ≤ pAtomicNorm d p f := by
        apply le_csInf hR
        rintro r ⟨a, c, hc, hs, rfl⟩
        obtain ⟨w, hw, hn⟩ := lift_p_series hC.le hA a c hc hs
        have he : w = u := (AtomicHardySpace.embedding_properties volume).1 (hw.trans hu.symm)
        rw [he] at hn
        exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hn)
      exact (div_le_iff₀ hC).mp hle |>.trans_eq (mul_comm _ _)

/-- Compact support supplies the L¹ class and a containing ball; normalization
then reduces the corollary to the uniform p-atom theorem. -/
theorem bound_to_compactMembership : BoundToCompactMembership.{v} := by
  intro hbound d p hp 𝕜 _ f hf hs hz
  obtain ⟨C, hC, hA⟩ := hbound d p hp
  have hple : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp.le
  let : IsFiniteMeasure (volume.restrict (tsupport f)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hs.measure_lt_top (μ := volume)⟩
  have hfi : Integrable f volume :=
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
      (MemLp.integrable hple (hf.mono_measure Measure.restrict_le_self))
  let F : L1 d 𝕜 := hfi.toL1 f
  have he : ⇑F =ᵐ[volume] f := hfi.coeFn_toL1
  obtain ⟨r, hr, hball⟩ := hs.isBounded.subset_ball_lt 0 (0 : Point d)
  have hsup : ∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Point d) r → F x = 0 := by
    filter_upwards [he] with x hx
    intro hxB
    rw [hx]
    by_contra hx0
    exact hxB (hball (subset_tsupport f (by simpa only [Function.mem_support] using hx0)))
  obtain ⟨k, a, hka⟩ := normalize_ball F (hf.ae_eq he.symm)
    ((integral_congr_ae he).trans hz) 0 r hr hsup
  obtain ⟨u, hu, hn⟩ := hA a
  refine ⟨k • u, ?_⟩
  have heq : AtomicHardySpaceSpec.EmbeddingValue volume (k • u) = F := by
    rw [map_smul, hu, hka]
  rw [heq]
  exact he

theorem zero_dimension_expansion : ZeroDimensionExpansion.{v} := by
  classical
  intro p 𝕜 _ a
  have ha : a.val = 0 := zero_dim_mean_zero a.val a.property.2.1
  let b : InfinityAtom 0 𝕜 := Classical.choice
    (AtomicHardySpace.euclidean_atoms_nonempty 0 𝕜)
  refine ⟨fun _ => b, fun _ => 0, ?_, ?_, ?_⟩
  · simpa only [norm_zero] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  · simpa only [zero_smul, ha] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : L1 0 𝕜)) 0)
  · simp

/-- A bounded mean-zero function on a ball has a Hardy lift with the
expected size `M * |B|`. The bound is also valid when `M = 0`. -/
lemma bounded_ball_hardy {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 d 𝕜) (hz : (∫ x, f x) = 0)
    (c : Point d) (r : ℝ) (hr : 0 < r) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0)
    (hn : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) :
    ∃ u : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume u = f ∧
      ‖u‖ ≤ M * volume.real (Metric.ball c r) := by
  by_cases hzero : M = 0
  · have hfzero : f = 0 := by
      apply Lp.ext
      filter_upwards [hn, Lp.coeFn_zero 𝕜 1 (volume : Measure (Point d))] with x hx hx0
      have hx' : f x = 0 := norm_le_zero_iff.mp (hzero ▸ hx)
      exact hx'.trans hx0.symm
    exact ⟨0, by simp [hfzero], by simp [hzero]⟩
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
  let V := volume.real (Metric.ball c r)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  let K : ℝ := M * V
  have hK : 0 < K := mul_pos hMpos hV
  let k : 𝕜 := algebraMap ℝ 𝕜 K
  have hk : k ≠ 0 := (map_ne_zero (algebraMap ℝ 𝕜)).mpr hK.ne'
  have hkn : ‖k‖ = K := by
    change ‖(K : 𝕜)‖ = K
    rw [RCLike.norm_ofReal, abs_of_pos hK]
  have he : ⇑(k⁻¹ • f) =ᵐ[volume] k⁻¹ • ⇑f := Lp.coeFn_smul _ _
  have hzi : (∫ x, (k⁻¹ • f) x) = 0 := by
    rw [integral_congr_ae he]
    change (∫ x, k⁻¹ • f x) = 0
    rw [integral_smul, hz, smul_zero]
  have ha : AtomicHardySpaceSpec.IsAtomValue volume (k⁻¹ • f) := by
    refine ⟨hzi, c, r, hr, (Metric.measure_ball_pos volume c hr).ne',
      measure_ball_ne_top, ?_⟩
    filter_upwards [he, hs, hn] with x hx hxs hxn
    refine ⟨fun hxB => by simp [hx, hxs hxB], ?_⟩
    rw [hx, Pi.smul_apply, norm_smul, norm_inv, hkn]
    calc
      K⁻¹ * ‖f x‖ ≤ K⁻¹ * M := mul_le_mul_of_nonneg_left hxn (inv_nonneg.mpr hK.le)
      _ = V⁻¹ := by dsimp [K]; field_simp
  let a : InfinityAtom d 𝕜 := ⟨k⁻¹ • f, ha⟩
  refine ⟨k • AtomicHardySpace.atomElement volume a, ?_, ?_⟩
  · rw [map_smul, AtomicHardySpace.embedding_atomElement]
    exact smul_inv_smul₀ hk f
  · rw [norm_smul, hkn]
    exact mul_le_of_le_one_right hK.le (AtomicHardySpace.atomElement_norm volume a)

namespace Dyadic
open ExpandedFA.SingularIntegrals.CZ

/-- A corner and an enclosing Euclidean ball for a half-open dyadic cube.
The enlargement is dimensional and works also in dimension zero. -/
def corner {d : ℕ} (q : DyadicCube d) : HardyPAtomsSpec.Point d :=
  WithLp.toLp 2 (fun i => side q * (q.2 i : ℝ))

lemma cube_subset_ball {d : ℕ} (q : DyadicCube d) :
    cube q ⊆ Metric.ball (corner q) (((d : ℝ) + 1) * side q) := by
  intro x hx
  have hside := side_pos q
  have hn : ‖x - corner q‖ ^ 2 ≤ (d : ℝ) * side q ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i : Fin d, ‖(x - corner q) i‖ ^ 2 ≤ ∑ _i : Fin d, side q ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hxi := hx i
        have hcoord : ‖(x - corner q) i‖ ≤ side q := by
          change |x i - side q * (q.2 i : ℝ)| ≤ side q
          rw [abs_of_nonneg (sub_nonneg.mpr hxi.1)]
          nlinarith [hxi.2]
        exact pow_le_pow_left₀ (norm_nonneg _) hcoord 2
      _ = (d : ℝ) * side q ^ 2 := by simp
  rw [Metric.mem_ball, dist_eq_norm]
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  apply (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp
  apply hn.trans_lt
  rw [mul_pow]
  apply mul_lt_mul_of_pos_right _ (sq_pos_of_pos hside)
  nlinarith [sq_nonneg (d : ℝ)]

lemma cube_ball_volume {d : ℕ} (q : DyadicCube d) :
    volume.real (Metric.ball (corner q) (((d : ℝ) + 1) * side q)) =
      volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) ((d : ℝ) + 1)) * volume.real (cube q) := by
  rw [mul_comm ((d : ℝ) + 1), Measure.real,
    Measure.addHaar_ball_mul_of_pos volume (corner q) (side_pos q),
    ENNReal.toReal_mul, finrank_euclideanSpace, Fintype.card_fin,
    ENNReal.toReal_ofReal (pow_nonneg (side_pos q).le d)]
  simp only [Measure.real, cube_volume, ENNReal.toReal_ofReal (pow_nonneg (side_pos q).le d)]
  exact mul_comm _ _

/-- Every bounded mean-zero piece on a dyadic cube has a Hardy lift, with
one constant depending only on the dimension. -/
lemma bounded_cube_hardy {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 d 𝕜) (hz : (∫ x, f x) = 0) (q : DyadicCube d)
    (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ᵐ x ∂volume, x ∉ cube q → f x = 0)
    (hn : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) :
    ∃ u : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume u = f ∧
      ‖u‖ ≤ volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) ((d : ℝ) + 1)) * M *
        volume.real (cube q) := by
  obtain ⟨u, hu, hnu⟩ := bounded_ball_hardy f hz (corner q)
    (((d : ℝ) + 1) * side q) (mul_pos (by positivity) (side_pos q)) M hM
    (hs.mono (fun x hx hxb => hx (fun hxc => hxb (cube_subset_ball q hxc)))) hn
  refine ⟨u, hu, ?_⟩
  rw [cube_ball_volume] at hnu
  convert hnu using 1 <;> ring

/-- Maximal bad cubes at a higher threshold lie in maximal bad cubes at
a lower threshold. The selections are the actual accepted canonical ones. -/
lemma maximal_bad_nested {d : ℕ} (hd : 0 < d) {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (q : DyadicCube d) (hq : q ∈ maximalBadCubes f t) :
    ∃ r ∈ maximalBadCubes f s, cube q ⊆ cube r := by
  apply bad_cube_covered_by_maximal hd f hf s hs q
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hst ENNReal.toReal_nonneg) hq.1

lemma bad_region_antitone {d : ℕ} (hd : 0 < d) {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    badRegion (maximalBadCubes f t) ⊆ badRegion (maximalBadCubes f s) := by
  intro x hx
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  obtain ⟨r, hr, hqr⟩ := maximal_bad_nested hd f hf hs hst q q.property
  exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hqr hxq⟩

/-- Averaging on pairwise disjoint cubes preserves the total integral. -/
lemma goodPart_integral {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube) :
    (∫ x, goodPart f Q x) = ∫ x, f x := by
  have hg := goodPart_integrable f hf Q hd
  have hm := badRegion_measurable Q
  have hcube (q : Q) :
      (∫ x in cube q.val, goodPart f Q x) = ∫ x in cube q.val, f x := by
    rw [setIntegral_congr_fun (cube_measurable q.val)
      (fun x hx => goodPart_inside f Q hd q x hx), integral_const,
      MeasureTheory.measureReal_restrict_apply_univ]
    exact measure_smul_setAverage f (cube_volume_lt_top q.val).ne
  rw [← integral_add_compl hm hg, ← integral_add_compl hm hf]
  congr 1
  · rw [show badRegion Q = ⋃ q : Q, cube q.val from rfl,
      integral_iUnion (fun q : Q => cube_measurable q.val) (hd.subtype _) hg.integrableOn,
      integral_iUnion (fun q : Q => cube_measurable q.val) (hd.subtype _) hf.integrableOn]
    exact tsum_congr hcube
  · exact setIntegral_congr_fun hm.compl (fun x hx => goodPart_outside f Q x hx)

/-- The error in a dyadic good approximation is controlled by the original
L¹ mass on its bad region, which tends to zero with that region's measure. -/
lemma goodPart_error_integral {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube) :
    (∫ x, ‖goodPart f Q x - f x‖) ≤ 2 * ∫ x in badRegion Q, ‖f x‖ := by
  have hg := goodPart_integrable f hf Q hd
  have hm := badRegion_measurable Q
  have hzero : ∀ x, x ∉ badRegion Q → ‖goodPart f Q x - f x‖ = 0 :=
    fun x hx => by rw [goodPart_outside f Q x hx, sub_self, norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    (∫ x in badRegion Q, ‖goodPart f Q x - f x‖) ≤
        ∫ x in badRegion Q, (‖goodPart f Q x‖ + ‖f x‖) :=
      integral_mono (hg.sub hf).norm.integrableOn
        (hg.norm.add hf.norm).integrableOn (fun x => norm_sub_le _ _)
    _ = (∫ x in badRegion Q, ‖goodPart f Q x‖) + ∫ x in badRegion Q, ‖f x‖ :=
      integral_add hg.norm.integrableOn hf.norm.integrableOn
    _ ≤ 2 * ∫ x in badRegion Q, ‖f x‖ := by
      have hmass : (∫ x in badRegion Q, ‖goodPart f Q x‖) ≤
          ∫ x in badRegion Q, ‖f x‖ := by
        rw [show badRegion Q = ⋃ q : Q, cube q.val from rfl,
          integral_iUnion (fun q : Q => cube_measurable q.val) (hd.subtype _) hg.norm.integrableOn,
          integral_iUnion (fun q : Q => cube_measurable q.val) (hd.subtype _) hf.norm.integrableOn]
        exact Summable.tsum_le_tsum (fun q => goodPart_integral_norm_cube_le f Q hd q)
          (hasSum_integral_iUnion (fun q : Q => cube_measurable q.val)
            (hd.subtype _) hg.norm.integrableOn).summable
          (hasSum_integral_iUnion (fun q : Q => cube_measurable q.val)
            (hd.subtype _) hf.norm.integrableOn).summable
      linarith

/-- The measure estimate is for the actual bad region, not just a formal
sum of cube volumes. -/
lemma bad_region_measure_le {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) (Q : Set (DyadicCube d)) (hQ : Selection f t Q) :
    volume (badRegion Q) ≤ eLpNorm f 1 volume / ENNReal.ofReal t := by
  rw [badRegion, measure_iUnion (hQ.disjoint.subtype _)
    (fun q : Q => cube_measurable q.val)]
  exact selection_measure_bound f hf t ht Q hQ

lemma bad_region_measure_tendsto_zero {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (hlim : Tendsto t atTop atTop)
    (Q : ℕ → Set (DyadicCube d)) (hQ : ∀ n, Selection f (t n) (Q n)) :
    Tendsto (fun n => volume (badRegion (Q n))) atTop (𝓝 0) := by
  have hdiv := ENNReal.Tendsto.const_div (ENNReal.tendsto_ofReal_atTop.comp hlim)
    (a := eLpNorm f 1 volume) (Or.inr (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top)
  simp only [ENNReal.div_top] at hdiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
    (fun _ => bot_le) (fun n => bad_region_measure_le f hf (t n) (ht n) (Q n) (hQ n))

/-- Arbitrarily high selected levels converge in the actual L¹ norm, for
every integrable function. No maximal-function integrability is assumed. -/
lemma goodPart_error_tendsto_zero {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (hlim : Tendsto t atTop atTop)
    (Q : ℕ → Set (DyadicCube d)) (hQ : ∀ n, Selection f (t n) (Q n)) :
    Tendsto (fun n => ∫ x, ‖goodPart f (Q n) x - f x‖) atTop (𝓝 0) := by
  have hmass := hf.norm.tendsto_setIntegral_nhds_zero
    (bad_region_measure_tendsto_zero f hf t ht hlim Q hQ)
  have hmass' := hmass.const_mul 2
  simp only [mul_zero] at hmass'
  exact squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (fun n => goodPart_error_integral f hf (Q n) (hQ n).disjoint) hmass'

lemma goodPart_L1_tendsto {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 d 𝕜) (t : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (hlim : Tendsto t atTop atTop) (Q : ℕ → Set (DyadicCube d))
    (hQ : ∀ n, Selection (⇑f) (t n) (Q n)) :
    Tendsto (fun n => (goodPart_integrable (⇑f) (MeasureTheory.L1.integrable_coeFn f)
      (Q n) (hQ n).disjoint).toL1 (goodPart (⇑f) (Q n))) atTop (𝓝 f) := by
  let g (n : ℕ) : L1 d 𝕜 := (goodPart_integrable (⇑f) (MeasureTheory.L1.integrable_coeFn f)
    (Q n) (hQ n).disjoint).toL1 (goodPart (⇑f) (Q n))
  have he (n : ℕ) :
      ‖g n - f‖ = ∫ x, ‖goodPart (⇑f) (Q n) x - f x‖ := by
    rw [MeasureTheory.L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (g n) f,
      (goodPart_integrable (⇑f) (MeasureTheory.L1.integrable_coeFn f)
        (Q n) (hQ n).disjoint).coeFn_toL1] with x hx hy
    simpa only [hx, Pi.sub_apply] using congrArg (fun z => ‖z - f x‖) hy
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun n => ‖g n - f‖) atTop (𝓝 0)
  simp_rw [he]
  exact goodPart_error_tendsto_zero (⇑f) (MeasureTheory.L1.integrable_coeFn f)
    t ht hlim Q hQ

/-- Integration over a measurable or arbitrary set, as a continuous linear
map on L¹. This lets cancellation pass through the accepted bad-piece sum. -/
def setIntegralMap {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (S : Set (HardyPAtomsSpec.Point d)) : L1 d 𝕜 →L[𝕜] 𝕜 :=
  (MeasureTheory.L1.integralCLM' 𝕜).comp
    (LpToLpRestrictCLM (HardyPAtomsSpec.Point d) 𝕜 𝕜 volume 1 S)

lemma setIntegralMap_apply {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (S : Set (HardyPAtomsSpec.Point d)) (f : L1 d 𝕜) :
    setIntegralMap S f = ∫ x in S, f x := by
  change MeasureTheory.L1.integralCLM' 𝕜 _ = _
  rw [← MeasureTheory.L1.integral_eq', MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn 𝕜 S f)

lemma badPiece_setIntegral_zero {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    (q : DyadicCube d) (S : Set (HardyPAtomsSpec.Point d))
    (hq : cube q ⊆ S ∨ Disjoint (cube q) S) :
    (∫ x in S, badPiece f q x) = 0 := by
  rcases hq with hq | hq
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact badPiece_integral f q (cube_volume_lt_top q)
    · intro x hx
      exact Set.indicator_of_notMem (fun hxc => hx (hq hxc)) _
  · apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact Set.indicator_of_notMem (fun hxc => Set.disjoint_left.mp hq hxc hx) _

/-- Averaging on cubes contained in or disjoint from a set preserves the
integral over that set, by the actual L¹ bad-piece series. -/
lemma goodPart_setIntegral {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube)
    (S : Set (HardyPAtomsSpec.Point d))
    (hS : ∀ q ∈ Q, cube q ⊆ S ∨ Disjoint (cube q) S) :
    (∫ x in S, goodPart f Q x) = ∫ x in S, f x := by
  have hg := goodPart_integrable f hf Q hd
  obtain ⟨_, hb, hh, hsum⟩ := badSeries_of_memLp f Q hd
    (by norm_num : (1 : ℝ≥0∞) ≠ 0) (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    (memLp_one_iff_integrable.mpr hf) (memLp_one_iff_integrable.mpr hg)
  have hmap := hsum.mapL (setIntegralMap S)
  have hterm (q : Q) : setIntegralMap S ((hb q).toLp (badPiece f q.val)) = 0 := by
    rw [setIntegralMap_apply]
    rw [integral_congr_ae ((hb q).coeFn_toLp.restrict)]
    exact badPiece_setIntegral_zero f hf q.val S (hS q.val q.property)
  have hz : setIntegralMap S (hh.toLp (f - goodPart f Q)) = 0 := by
    apply hmap.unique
    simpa only [hterm] using (hasSum_zero : HasSum (fun _ : Q => (0 : 𝕜)) 0)
  rw [setIntegralMap_apply, integral_congr_ae (hh.coeFn_toLp.restrict)] at hz
  change (∫ x in S, f x - goodPart f Q x) = 0 at hz
  rw [integral_sub hf.integrableOn hg.integrableOn] at hz
  exact (sub_eq_zero.mp hz).symm

/-- Higher-level good approximations preserve the original integral on
every lower-level bad cube. -/
lemma goodPart_integral_on_lower_cube {d : ℕ} (hd : 0 < d)
    {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (q : DyadicCube d) (hq : q ∈ maximalBadCubes f s) :
    (∫ x in cube q, goodPart f (maximalBadCubes f t) x) = ∫ x in cube q, f x := by
  apply goodPart_setIntegral f hf _ (maximalBadCubes_disjoint f t)
  intro r hr
  obtain ⟨u, hu, hru⟩ := maximal_bad_nested hd f hf hs hst r hr
  by_cases he : u = q
  · exact Or.inl (he ▸ hru)
  · exact Or.inr ((maximalBadCubes_disjoint f s hu hq he).mono_left hru)

lemma goodPart_increment_mean_zero {d : ℕ} (hd : 0 < d)
    {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (q : DyadicCube d) (hq : q ∈ maximalBadCubes f s) :
    (∫ x in cube q, goodPart f (maximalBadCubes f t) x -
      goodPart f (maximalBadCubes f s) x) = 0 := by
  have hgS := goodPart_integrable f hf _ (maximalBadCubes_disjoint f s)
  have hgT := goodPart_integrable f hf _ (maximalBadCubes_disjoint f t)
  rw [integral_sub hgT.integrableOn hgS.integrableOn,
    goodPart_integral_on_lower_cube hd f hf hs hst q hq]
  have hval := goodPart_inside f _ (maximalBadCubes_disjoint f s) ⟨q, hq⟩
  rw [setIntegral_congr_fun (cube_measurable q) (fun x hx => hval x hx),
    integral_const, measureReal_restrict_apply_univ, cubeAverage,
    measure_smul_setAverage f (cube_volume_lt_top q).ne, sub_self]

/-- Hölder on an arbitrary finite-measure set, with the original global
finite-p norm on the right. -/
lemma set_holder {d : ℕ} {𝕜 : Type v} [RCLike 𝕜] {p : ℝ}
    (hp : 1 < p) (f : HardyPAtomsSpec.Point d → 𝕜)
    (hf : Integrable f volume) (hfp : MemLp f (ENNReal.ofReal p) volume)
    (S : Set (HardyPAtomsSpec.Point d)) (hS : volume S < ∞) :
    (∫ x in S, ‖f x‖) ≤ (eLpNorm f (ENNReal.ofReal p) volume).toReal *
      (volume.real S) ^ (1 - 1 / p) := by
  by_cases hzero : volume S = 0
  · rw [setIntegral_measure_zero _ hzero]
    positivity
  have hple : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hcomp : eLpNorm f 1 (volume.restrict S) ≤
      eLpNorm f (ENNReal.ofReal p) volume * volume S ^ (1 - 1 / p) := by
    calc
      _ ≤ eLpNorm f (ENNReal.ofReal p) (volume.restrict S) * volume S ^ (1 - 1 / p) := by
        simpa only [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one,
          ENNReal.toReal_ofReal (zero_lt_one.trans hp).le] using
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hple hfp.aestronglyMeasurable.restrict
      _ ≤ _ := mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self) le_rfl
  have heq : eLpNorm f 1 (volume.restrict S) = ENNReal.ofReal (∫ x in S, ‖f x‖) := by
    rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable.restrict,
      ← ofReal_integral_norm_eq_lintegral_enorm hf.integrableOn]
  have hfin : eLpNorm f (ENNReal.ofReal p) volume * volume S ^ (1 - 1 / p) ≠ ∞ :=
    ENNReal.mul_ne_top hfp.eLpNorm_ne_top (ENNReal.rpow_ne_top_of_ne_zero hzero hS.ne)
  have hle := ENNReal.toReal_mono hfin hcomp
  rwa [heq, ENNReal.toReal_ofReal (integral_nonneg (fun x => norm_nonneg _)),
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hle

lemma selection_real_volume_summable {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) (Q : Set (DyadicCube d)) (hQ : Selection f t Q) :
    Summable (fun q : Q => volume.real (cube q.val)) := by
  apply ENNReal.summable_toReal
  exact (lt_of_le_of_lt (selection_measure_bound f hf t ht Q hQ)
    (ENNReal.div_lt_top (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top
      (ENNReal.ofReal_pos.mpr ht).ne')).ne

lemma selection_volume_real {d : ℕ} (Q : Set (DyadicCube d))
    (hQ : Q.PairwiseDisjoint cube) :
    volume.real (badRegion Q) = ∑' q : Q, volume.real (cube q.val) := by
  rw [Measure.real, badRegion, measure_iUnion (hQ.subtype _)
    (fun q : Q => cube_measurable q.val),
    ENNReal.tsum_toReal_eq (fun q : Q => (cube_volume_lt_top q.val).ne)]
  rfl

/-- The lower average bound summed over the actual selected cubes. -/
lemma selection_lower_integral {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) (Q : Set (DyadicCube d)) (hQ : Selection f t Q) :
    t * volume.real (badRegion Q) ≤ ∫ x in badRegion Q, ‖f x‖ := by
  rw [selection_volume_real Q hQ.disjoint, ← tsum_mul_left,
    show badRegion Q = ⋃ q : Q, cube q.val from rfl,
    integral_iUnion (fun q : Q => cube_measurable q.val) (hQ.disjoint.subtype _) hf.norm.integrableOn]
  exact Summable.tsum_le_tsum (fun q => (hQ.lower q.val q.property).le)
    ((selection_real_volume_summable f hf t ht Q hQ).mul_left t)
    (hasSum_integral_iUnion (fun q : Q => cube_measurable q.val)
      (hQ.disjoint.subtype _) hf.norm.integrableOn).summable

/-- The weak-p estimate follows directly from Hölder on the bad region.
No unproved dyadic maximal bound or Jensen estimate is used. -/
lemma selection_p_volume_bound {d : ℕ} {𝕜 : Type v} [RCLike 𝕜] {p : ℝ}
    (hp : 1 < p) (f : HardyPAtomsSpec.Point d → 𝕜)
    (hf : Integrable f volume) (hfp : MemLp f (ENNReal.ofReal p) volume)
    (t : ℝ) (ht : 0 < t) (Q : Set (DyadicCube d)) (hQ : Selection f t Q) :
    volume.real (badRegion Q) ≤
      ((eLpNorm f (ENNReal.ofReal p) volume).toReal / t) ^ p := by
  let V := volume.real (badRegion Q)
  let N := (eLpNorm f (ENNReal.ofReal p) volume).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hfin : volume (badRegion Q) < ∞ :=
    (bad_region_measure_le f hf t ht Q hQ).trans_lt
      (ENNReal.div_lt_top (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top
        (ENNReal.ofReal_pos.mpr ht).ne')
  have hi : t * V ≤ N * V ^ (1 - 1 / p) :=
    (selection_lower_integral f hf t ht Q hQ).trans (set_holder hp f hf hfp _ hfin)
  by_cases hz : V = 0
  · change V ≤ (N / t) ^ p
    rw [hz]
    positivity
  have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hz)
  have hpowpos : 0 < V ^ (1 - 1 / p) := Real.rpow_pos_of_pos hVpos _
  have hdecomp : V = V ^ (1 / p) * V ^ (1 - 1 / p) := by
    rw [← Real.rpow_add hVpos]
    simp
  have hroot : V ^ (1 / p) ≤ N / t := by
    apply (le_div_iff₀ ht).mpr
    apply (mul_le_mul_iff_left₀ hpowpos).mp
    nlinarith [hi, hdecomp]
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hV _) hroot (zero_lt_one.trans hp).le
  rw [← Real.rpow_mul hV, one_div_mul_cancel (zero_lt_one.trans hp).ne', Real.rpow_one] at h
  exact h

/-- Summability of the dyadic level budget from any weak-p volume bounds.
The geometric ratio is strictly below one precisely because `p > 1`. -/
lemma geometric_level_budget {p : ℝ} (hp : 1 < p) (t N : ℝ) (ht : 0 < t) (hN : 0 ≤ N)
    (V : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n)
    (hbound : ∀ n, V n ≤ (N / ((2 : ℝ) ^ n * t)) ^ p) :
    Summable (fun n => ((2 : ℝ) ^ n * t) * V n) ∧
    (∑' n, ((2 : ℝ) ^ n * t) * V n) ≤
      N ^ p * t ^ (1 - p) / (1 - (2 : ℝ) ^ (1 - p)) := by
  let q : ℝ := (2 : ℝ) ^ (1 - p)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo := (summable_geometric_of_lt_one hq0 hq1).mul_left (N ^ p * t ^ (1 - p))
  have hle (n : ℕ) : ((2 : ℝ) ^ n * t) * V n ≤ (N ^ p * t ^ (1 - p)) * q ^ n := by
    have hlevel : 0 < (2 : ℝ) ^ n * t := mul_pos (by positivity) ht
    calc
      _ ≤ ((2 : ℝ) ^ n * t) * (N / ((2 : ℝ) ^ n * t)) ^ p :=
        mul_le_mul_of_nonneg_left (hbound n) hlevel.le
      _ = (N ^ p * t ^ (1 - p)) * q ^ n := by
        rw [Real.div_rpow hN hlevel.le]
        calc
          (2 ^ n * t) * (N ^ p / (2 ^ n * t) ^ p) =
              N ^ p * ((2 ^ n * t) ^ (1 : ℝ) * (2 ^ n * t) ^ (-p)) := by
            rw [Real.rpow_one, Real.rpow_neg hlevel.le]
            ring
          _ = N ^ p * (2 ^ n * t) ^ (1 - p) := by
            rw [← Real.rpow_add hlevel]
            rfl
          _ = (N ^ p * t ^ (1 - p)) * q ^ n := by
            rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ) ^ n) ht.le,
              ← Real.rpow_pow_comm (by norm_num : 0 ≤ (2 : ℝ))]
            dsimp [q]
            ring
  have hs : Summable (fun n => ((2 : ℝ) ^ n * t) * V n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (hV n)) hle hgeo
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, (N ^ p * t ^ (1 - p)) * q ^ n := hs.tsum_le_tsum hle hgeo
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]; rfl

end Dyadic

/-- An atomic expansion yields all original clauses through the proved
transport results in this module. -/
theorem assemble_from_expansion : Assembly.{v} := by
  intro hex
  have hb := expansion_to_bound hex
  exact ⟨hex, hb, bound_to_rawAtomBound hb,
    bound_to_equivalentNorm infinityAtoms_are_pAtoms hb,
    bound_to_compactMembership hb⟩

end ExpandedFA.Hardy.HardyPAtoms

namespace ExpandedFA.Hardy.HardyPAtoms
open HardyPAtomsSpec

lemma hardy_of_summable_increments {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (g : ℕ → L1 d 𝕜) (f : L1 d 𝕜)
    (hg : Tendsto g atTop (𝓝 f)) (A₀ : ℝ) (A : ℕ → ℝ) (hA : Summable A)
    (hinit : ∃ u : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume u = g 0 ∧
      ‖u‖ ≤ A₀)
    (hstep : ∀ n, ∃ u : H1 d 𝕜,
      AtomicHardySpaceSpec.EmbeddingValue volume u = g (n + 1) - g n ∧
      ‖u‖ ≤ A n) :
    ∃ u : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume u = f ∧
      ‖u‖ ≤ A₀ + ∑' n, A n := by
  classical
  obtain ⟨u₀, hu₀, hn₀⟩ := hinit
  choose v hv hn using hstep
  have hvs : Summable v := hA.of_norm_bounded hn
  have him : HasSum (fun n => g (n + 1) - g n)
      (AtomicHardySpaceSpec.EmbeddingValue volume (∑' n, v n)) := by
    simpa only [hv] using hvs.hasSum.mapL (AtomicHardySpaceSpec.EmbeddingValue volume)
  have hlim : AtomicHardySpaceSpec.EmbeddingValue volume (∑' n, v n) = f - g 0 := by
    apply tendsto_nhds_unique him.tendsto_sum_nat
    simpa only [Finset.sum_range_sub] using hg.sub_const (g 0)
  refine ⟨u₀ + ∑' n, v n, ?_, ?_⟩
  · rw [map_add, hu₀, hlim, add_sub_cancel]
  · exact (norm_add_le _ _).trans (add_le_add hn₀
      (hvs.hasSum.norm_le_of_bounded hA.hasSum hn))

end ExpandedFA.Hardy.HardyPAtoms

namespace ExpandedFA.Hardy.HardyPAtoms.Dyadic
open ExpandedFA.SingularIntegrals.CZ
open ExpandedFA.Hardy.HardyPAtomsSpec

/-- The actual L¹ good approximation associated to the canonical bad cubes. -/
def goodApprox {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 d 𝕜) (t : ℝ) : L1 d 𝕜 :=
  (goodPart_integrable (⇑f) (MeasureTheory.L1.integrable_coeFn f)
    (maximalBadCubes (⇑f) t) (maximalBadCubes_disjoint (⇑f) t)).toL1
      (goodPart (⇑f) (maximalBadCubes (⇑f) t))

lemma goodApprox_tendsto {d : ℕ} (hd : 0 < d) {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 d 𝕜) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => goodApprox f ((2 : ℝ)^n * t)) atTop (𝓝 f) := by
  apply goodPart_L1_tendsto f (fun n : ℕ => (2 : ℝ)^n * t)
    (fun n => mul_pos (pow_pos (by norm_num) n) ht)
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const ht)
  intro n
  exact maximalBadCubes_selection hd (⇑f) (MeasureTheory.L1.integrable_coeFn f)
    _ (mul_pos (pow_pos (by norm_num) n) ht)

end ExpandedFA.Hardy.HardyPAtoms.Dyadic


namespace ExpandedFA.Hardy.HardyPAtoms.Dyadic
open ExpandedFA.SingularIntegrals.CZ
open HardyPAtomsSpec

/-- Bounded cancellative restrictions to disjoint cubes sum in Hardy space. -/
lemma bounded_disjoint_cube_hardy {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (h : HardyPAtomsSpec.Point d → 𝕜) (hh : Integrable h volume)
    (Q : Set (DyadicCube d)) (hQ : Q.PairwiseDisjoint cube)
    (hV : Summable (fun q : Q => volume.real (cube q.val)))
    (M : ℝ) (hM : 0 ≤ M)
    (hz : ∀ q : Q, (∫ x in cube q.val, h x) = 0)
    (hout : ∀ x, x ∉ badRegion Q → h x = 0)
    (hn : ∀ᵐ x ∂volume, ‖h x‖ ≤ M) :
    ∃ u : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume u = hh.toL1 h ∧
      ‖u‖ ≤ volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) ((d : ℝ) + 1)) * M *
        ∑' q : Q, volume.real (cube q.val) := by
  classical
  let V := volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) ((d : ℝ) + 1))
  let hp := memLp_one_iff_integrable.mpr hh
  let b (q : Q) : L1 d 𝕜 :=
    (hp.indicator (cube_measurable q.val).nullMeasurableSet).toLp ((cube q.val).indicator h)
  have hb (q : Q) : ⇑(b q) =ᵐ[volume] (cube q.val).indicator h :=
    (hp.indicator (cube_measurable q.val).nullMeasurableSet).coeFn_toLp
  have hlift (q : Q) : ∃ u : H1 d 𝕜,
      AtomicHardySpaceSpec.EmbeddingValue volume u = b q ∧
      ‖u‖ ≤ V * M * volume.real (cube q.val) := by
    refine bounded_cube_hardy (b q) ?_ q.val M hM ?_ ?_
    · rw [integral_congr_ae (hb q), integral_indicator (cube_measurable q.val)]
      exact hz q
    · filter_upwards [hb q] with x hx hxc
      rw [hx, Set.indicator_of_notMem hxc]
    · filter_upwards [hb q, hn] with x hx hxn
      rw [hx]
      by_cases hxc : x ∈ cube q.val
      · simpa only [Set.indicator_of_mem hxc] using hxn
      · simp only [Set.indicator_of_notMem hxc, norm_zero]
        exact hM
  choose u hu hnu using hlift
  have hbudget : Summable (fun q : Q => V * M * volume.real (cube q.val)) :=
    hV.mul_left (V * M)
  have hus : Summable u := hbudget.of_norm_bounded hnu
  have hbs : HasSum b (hh.toL1 h) :=
    hasSum_indicator_disjoint Q hQ h (by norm_num) (by norm_num) hp hout
  refine ⟨∑' q, u q, ?_, ?_⟩
  · have him : HasSum b (AtomicHardySpaceSpec.EmbeddingValue volume (∑' q, u q)) := by
      simpa only [hu] using hus.hasSum.mapL (AtomicHardySpaceSpec.EmbeddingValue volume)
    exact him.unique hbs
  · rw [← tsum_mul_left]
    exact hus.hasSum.norm_le_of_bounded hbudget.hasSum hnu

/-- One dyadic increment has an actual Hardy lift with its cube-volume budget. -/
lemma goodPart_increment_hardy {d : ℕ} (hd : 0 < d)
    {𝕜 : Type v} [RCLike 𝕜]
    (f : HardyPAtomsSpec.Point d → 𝕜) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) :
    ∃ u : H1 d 𝕜,
      AtomicHardySpaceSpec.EmbeddingValue volume u =
        (goodPart_integrable f hf _ (maximalBadCubes_disjoint f (2 * t))).toL1
          (goodPart f (maximalBadCubes f (2 * t))) -
        (goodPart_integrable f hf _ (maximalBadCubes_disjoint f t)).toL1
          (goodPart f (maximalBadCubes f t)) ∧
      ‖u‖ ≤ volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) ((d : ℝ) + 1)) *
        (3 * (2 : ℝ) ^ d) * t *
        ∑' q : maximalBadCubes f t, volume.real (cube q.val) := by
  have ht2 : 0 < 2 * t := by positivity
  have htt : t ≤ 2 * t := by linarith
  let Q := maximalBadCubes f t
  let R := maximalBadCubes f (2 * t)
  have hQ := maximalBadCubes_selection hd f hf t ht
  have hR := maximalBadCubes_selection hd f hf (2 * t) ht2
  have hgQ := goodPart_integrable f hf Q hQ.disjoint
  have hgR := goodPart_integrable f hf R hR.disjoint
  let h := goodPart f R - goodPart f Q
  have hh : Integrable h volume := hgR.sub hgQ
  obtain ⟨u, hu, hnu⟩ := bounded_disjoint_cube_hardy h hh Q hQ.disjoint
    (selection_real_volume_summable f hf t ht Q hQ)
    (3 * (2 : ℝ) ^ d * t) (by positivity)
    (fun q => goodPart_increment_mean_zero hd f hf ht htt q.val q.property)
    (fun x hx => by
      dsimp [h]
      rw [goodPart_outside f Q x hx,
        goodPart_outside f R x (fun hxr => hx (bad_region_antitone hd f hf ht htt hxr)), sub_self])
    (by
      filter_upwards [goodPart_ae_norm_le f t ht Q hQ,
        goodPart_ae_norm_le f (2 * t) ht2 R hR] with x hxQ hxR
      exact (norm_sub_le _ _).trans (by nlinarith))
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    change hh.toL1 h = hgR.toL1 (goodPart f R) - hgQ.toL1 (goodPart f Q)
    apply Lp.ext
    filter_upwards [hh.coeFn_toL1,
      Lp.coeFn_sub (hgR.toL1 (goodPart f R)) (hgQ.toL1 (goodPart f Q)),
      hgR.coeFn_toL1, hgQ.coeFn_toL1] with x hx hs hxR hxQ
    simp only [hs, hxR, hxQ, hx, h, Pi.sub_apply]
  · convert hnu using 1; ring

end ExpandedFA.Hardy.HardyPAtoms.Dyadic

namespace ExpandedFA.Hardy.HardyPAtoms.Dyadic
open ExpandedFA.SingularIntegrals.CZ

lemma normalized_budget_factor {p V N : ℝ} (hp : 1 < p) (hV : 0 < V)
    (hN : 0 ≤ N) (hsize : N ≤ V ^ (1 / p - 1)) :
    N ^ p * (V⁻¹) ^ (1 - p) ≤ 1 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  calc
    N ^ p * (V⁻¹) ^ (1 - p) ≤
        (V ^ (1 / p - 1)) ^ p * (V⁻¹) ^ (1 - p) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hN hsize hp0.le)
        (Real.rpow_nonneg (inv_nonneg.mpr hV.le) _)
    _ = V ^ ((1 / p - 1) * p + -(1 - p)) := by
      rw [← Real.rpow_mul hV.le, Real.inv_rpow hV.le, ← Real.rpow_neg hV.le,
        ← Real.rpow_add hV]
    _ = 1 := by
      have hexp : (1 / p - 1) * p + -(1 - p) = 0 := by
        field_simp
        ring
      rw [hexp, Real.rpow_zero]

/-- Summable budget on any selections at successive dyadic levels. -/
lemma selection_level_budget {d : ℕ} {𝕜 : Type v} [RCLike 𝕜] {p : ℝ}
    (hp : 1 < p) (f : HardyPAtomsSpec.Point d → 𝕜)
    (hf : Integrable f volume) (hfp : MemLp f (ENNReal.ofReal p) volume)
    (t : ℝ) (ht : 0 < t) (Q : ℕ → Set (DyadicCube d))
    (hQ : ∀ n, Selection f ((2 : ℝ) ^ n * t) (Q n)) :
    Summable (fun n => ((2 : ℝ) ^ n * t) * ∑' q : Q n, volume.real (cube q.val)) ∧
    (∑' n, ((2 : ℝ) ^ n * t) * ∑' q : Q n, volume.real (cube q.val)) ≤
      (eLpNorm f (ENNReal.ofReal p) volume).toReal ^ p *
        t ^ (1 - p) / (1 - (2 : ℝ) ^ (1 - p)) := by
  apply geometric_level_budget hp t _ ht ENNReal.toReal_nonneg
  · exact fun n => tsum_nonneg (fun q => ENNReal.toReal_nonneg)
  · intro n
    rw [← selection_volume_real (Q n) (hQ n).disjoint]
    exact selection_p_volume_bound hp f hf hfp _ (mul_pos (by positivity) ht) _ (hQ n)

/-- Canonical maximal-cube form used by the telescoping construction. -/
lemma maximal_level_budget {d : ℕ} (hd : 0 < d) {𝕜 : Type v} [RCLike 𝕜] {p : ℝ}
    (hp : 1 < p) (f : HardyPAtomsSpec.Point d → 𝕜)
    (hf : Integrable f volume) (hfp : MemLp f (ENNReal.ofReal p) volume)
    (t : ℝ) (ht : 0 < t) :
    Summable (fun n => ((2 : ℝ) ^ n * t) *
      ∑' q : maximalBadCubes f ((2 : ℝ) ^ n * t), volume.real (cube q.val)) ∧
    (∑' n, ((2 : ℝ) ^ n * t) *
      ∑' q : maximalBadCubes f ((2 : ℝ) ^ n * t), volume.real (cube q.val)) ≤
      (eLpNorm f (ENNReal.ofReal p) volume).toReal ^ p *
        t ^ (1 - p) / (1 - (2 : ℝ) ^ (1 - p)) := by
  exact selection_level_budget hp f hf hfp t ht _
    (fun n => maximalBadCubes_selection hd f hf _ (mul_pos (by positivity) ht))

end ExpandedFA.Hardy.HardyPAtoms.Dyadic

namespace ExpandedFA.Hardy.HardyPAtoms.Dyadic
open ExpandedFA.SingularIntegrals.CZ
open HardyPAtomsSpec

/-- Summing the actual Hardy lifts of the good-part increments recovers f. -/
lemma hardy_of_goodApprox {d : ℕ} (hd : 0 < d) {𝕜 : Type v} [RCLike 𝕜]
    {p : ℝ} (hp : 1 < p) (f : L1 d 𝕜)
    (hfp : MemLp f (ENNReal.ofReal p) volume) (t : ℝ) (ht : 0 < t)
    (A₀ : ℝ) (hinit : ∃ u : H1 d 𝕜,
      AtomicHardySpaceSpec.EmbeddingValue volume u = goodApprox f t ∧ ‖u‖ ≤ A₀) :
    ∃ u : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume u = f ∧
      ‖u‖ ≤ A₀ +
        (volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) ((d : ℝ) + 1)) *
          (3 * (2 : ℝ)^d)) *
        ((eLpNorm f (ENNReal.ofReal p) volume).toReal ^ p *
          t ^ (1-p) / (1 - (2 : ℝ) ^ (1-p))) := by
  let K := volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) ((d : ℝ) + 1)) *
    (3 * (2 : ℝ)^d)
  have hK : 0 ≤ K := mul_nonneg ENNReal.toReal_nonneg (by positivity)
  let level := fun n : ℕ => (2 : ℝ)^n * t
  let V := fun n : ℕ => ∑' q : maximalBadCubes (⇑f) (level n), volume.real (cube q.val)
  have hf := MeasureTheory.L1.integrable_coeFn f
  have hbudget := maximal_level_budget hd hp (⇑f) hf hfp t ht
  obtain ⟨u, hu, hnu⟩ := hardy_of_summable_increments
    (fun n => goodApprox f (level n)) f (goodApprox_tendsto hd f t ht)
    A₀ (fun n => K * (level n * V n)) (hbudget.1.mul_left K)
    (by simpa only [level, pow_zero, one_mul] using hinit) (fun n => by
      obtain ⟨u, hu, hn⟩ := goodPart_increment_hardy hd (⇑f) hf (level n)
        (mul_pos (by positivity) ht)
      refine ⟨u, ?_, ?_⟩
      · have hlevel : level (n+1) = 2 * level n := by dsimp [level]; rw [pow_succ]; ring
        simpa only [goodApprox, hlevel] using hu
      · simpa only [K, V, mul_assoc] using hn)
  refine ⟨u, hu, hnu.trans ?_⟩
  apply add_le_add le_rfl
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hbudget.2 hK

end ExpandedFA.Hardy.HardyPAtoms.Dyadic

namespace ExpandedFA.Hardy.HardyPAtoms.Dyadic
open ExpandedFA.Hardy.HardyPAtomsSpec
open ExpandedFA.SingularIntegrals.CZ

/-- A harmless dimension-dependent bound for the radius of initial bad cubes. -/
def initialSideFactor (d : ℕ) : ℝ :=
  volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) 1) + 1

def initialRadiusFactor (d : ℕ) : ℝ :=
  2 * ((d : ℝ) + 1) * initialSideFactor d + 1

lemma initialSideFactor_one_le (d : ℕ) : 1 ≤ initialSideFactor d := by
  dsimp [initialSideFactor]
  exact le_add_of_nonneg_left ENNReal.toReal_nonneg

lemma initialRadiusFactor_pos (d : ℕ) : 0 < initialRadiusFactor d := by
  have := initialSideFactor_one_le d
  dsimp [initialRadiusFactor]
  positivity

lemma ball_volume_scaling {d : ℕ} (c : HardyPAtomsSpec.Point d) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball c r) = r ^ d *
      volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) 1) := by
  rw [show r = r * 1 from (mul_one r).symm, Measure.real,
    Measure.addHaar_ball_mul_of_pos volume c hr,
    ENNReal.toReal_mul, finrank_euclideanSpace, Fintype.card_fin,
    ENNReal.toReal_ofReal (pow_nonneg hr.le d)]
  simp only [mul_one, Measure.real]

lemma bad_cube_side_lt {d : ℕ} (hd : 0 < d) {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 d 𝕜) (c : HardyPAtomsSpec.Point d) (r : ℝ) (hr : 0 < r)
    (hL1 : ‖f‖ ≤ 1) (q : DyadicCube d)
    (hq : isBad (⇑f) ((volume.real (Metric.ball c r))⁻¹) q) :
    side q < initialSideFactor d * r := by
  have hV : 0 < volume.real (Metric.ball c r) := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  have hmass : (∫ x in cube q, ‖f x‖) ≤ 1 := by
    apply (setIntegral_le_integral (MeasureTheory.L1.integrable_coeFn f).norm
      (Eventually.of_forall (fun x => norm_nonneg _))).trans
    simpa only [← MeasureTheory.L1.norm_eq_integral_norm] using hL1
  have hvol : volume.real (cube q) < volume.real (Metric.ball c r) := by
    have hh : (volume.real (Metric.ball c r))⁻¹ * volume.real (cube q) < 1 :=
      hq.trans_le hmass
    simpa only [mul_one] using (inv_mul_lt_iff₀ hV).mp hh
  have hpow : side q ^ d < (initialSideFactor d * r) ^ d := by
    simp only [measureReal_def, cube_volume,
      ENNReal.toReal_ofReal (pow_nonneg (side_pos q).le d)] at hvol
    change side q ^ d < volume.real (Metric.ball c r) at hvol
    rw [ball_volume_scaling c hr] at hvol
    apply hvol.trans_le
    rw [mul_pow, mul_comm (initialSideFactor d ^ d)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr.le d)
    exact (show volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) 1) ≤
      initialSideFactor d from by dsimp [initialSideFactor]; linarith).trans
        (le_self_pow₀ (initialSideFactor_one_le d) hd.ne')
  exact lt_of_not_ge (fun h => (not_lt_of_ge
    (pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans (initialSideFactor_one_le d)) hr.le) h d)) hpow)

lemma bad_cube_meets_support_ball {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 d 𝕜) (c : HardyPAtomsSpec.Point d) (r : ℝ) (hr : 0 < r)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0)
    (q : DyadicCube d) (hq : isBad (⇑f) ((volume.real (Metric.ball c r))⁻¹) q) :
    ∃ y ∈ cube q, y ∈ Metric.ball c r := by
  classical
  by_contra hn
  have hzero : (∫ x in cube q, ‖f x‖) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hs, ae_restrict_mem (cube_measurable q)] with x hxs hxq
    simp only [hxs (fun hxB => hn ⟨x, hxq, hxB⟩), norm_zero, Pi.zero_apply]
  have hV : 0 < volume.real (Metric.ball c r) := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  have hcube : 0 < volume.real (cube q) :=
    ENNReal.toReal_pos (cube_volume_pos q).ne' (cube_volume_lt_top q).ne
  have hh := hq
  rw [isBad, hzero] at hh
  exact (not_lt_of_ge (mul_pos (inv_pos.mpr hV) hcube).le) hh

lemma initial_bad_region_subset_ball {d : ℕ} (hd : 0 < d) {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 d 𝕜) (c : HardyPAtomsSpec.Point d) (r : ℝ) (hr : 0 < r)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) (hL1 : ‖f‖ ≤ 1) :
    badRegion (maximalBadCubes (⇑f) ((volume.real (Metric.ball c r))⁻¹)) ⊆
      Metric.ball c (initialRadiusFactor d * r) := by
  intro x hx
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hyq, hyB⟩ := bad_cube_meets_support_ball f c r hr hs q.val q.property.1
  have hslt := bad_cube_side_lt hd f c r hr hL1 q.val q.property.1
  have hxcorner := cube_subset_ball q.val hxq
  have hycorner := cube_subset_ball q.val hyq
  rw [Metric.mem_ball] at hxcorner hycorner hyB ⊢
  have hxy : dist x y < 2 * ((d : ℝ) + 1) * side q.val := by
    calc
      dist x y ≤ dist x (corner q.val) + dist (corner q.val) y := dist_triangle _ _ _
      _ < ((d : ℝ) + 1) * side q.val + ((d : ℝ) + 1) * side q.val := by
        rw [dist_comm (corner q.val)]
        exact add_lt_add hxcorner hycorner
      _ = 2 * ((d : ℝ) + 1) * side q.val := by ring
  have hxy' : dist x y < 2 * ((d : ℝ) + 1) * (initialSideFactor d * r) :=
    hxy.trans (mul_lt_mul_of_pos_left hslt (by positivity))
  calc
    dist x c ≤ dist x y + dist y c := dist_triangle _ _ _
    _ < 2 * ((d : ℝ) + 1) * (initialSideFactor d * r) + r := add_lt_add hxy' hyB
    _ = initialRadiusFactor d * r := by dsimp [initialRadiusFactor]; ring


lemma initial_goodPart_hardy {d : ℕ} (hd : 0 < d) {𝕜 : Type v} [RCLike 𝕜]
    (f : L1 d 𝕜) (hz : (∫ x, f x) = 0)
    (c : HardyPAtomsSpec.Point d) (r : ℝ) (hr : 0 < r)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) (hL1 : ‖f‖ ≤ 1) :
    ∃ u : H1 d 𝕜,
      AtomicHardySpaceSpec.EmbeddingValue volume u =
        (goodPart_integrable (⇑f) (MeasureTheory.L1.integrable_coeFn f)
          (maximalBadCubes (⇑f) ((volume.real (Metric.ball c r))⁻¹))
          (maximalBadCubes_disjoint (⇑f) _)).toL1
          (goodPart (⇑f) (maximalBadCubes (⇑f) ((volume.real (Metric.ball c r))⁻¹))) ∧
      ‖u‖ ≤ (2 : ℝ) ^ d * initialRadiusFactor d ^ d := by
  let V := volume.real (Metric.ball c r)
  let t := V⁻¹
  let Q := maximalBadCubes (⇑f) t
  let g := goodPart (⇑f) Q
  have hf := MeasureTheory.L1.integrable_coeFn f
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  have ht : 0 < t := inv_pos.mpr hV
  have hQ := maximalBadCubes_selection hd (⇑f) hf t ht
  have hg : Integrable g volume := goodPart_integrable (⇑f) hf Q hQ.disjoint
  let G : L1 d 𝕜 := hg.toL1 g
  have he : ⇑G =ᵐ[volume] g := hg.coeFn_toL1
  have hR := initialRadiusFactor_pos d
  have hR1 : 1 ≤ initialRadiusFactor d := by
    have := initialSideFactor_one_le d
    dsimp [initialRadiusFactor]
    exact le_add_of_nonneg_left (by positivity)
  have hball : Metric.ball c r ⊆ Metric.ball c (initialRadiusFactor d * r) :=
    Metric.ball_subset_ball (by nlinarith)
  have hbad : badRegion Q ⊆ Metric.ball c (initialRadiusFactor d * r) :=
    initial_bad_region_subset_ball hd f c r hr hs hL1
  have hgs : ∀ᵐ x ∂volume, x ∉ Metric.ball c (initialRadiusFactor d * r) → G x = 0 := by
    filter_upwards [he, hs] with x hx hxs
    intro hxn
    rw [hx, show g x = f x from goodPart_outside (⇑f) Q x (fun hxB => hxn (hbad hxB))]
    exact hxs (fun hxB => hxn (hball hxB))
  have hgn : ∀ᵐ x ∂volume, ‖G x‖ ≤ (2 : ℝ) ^ d * t := by
    filter_upwards [he, goodPart_ae_norm_le (⇑f) t ht Q hQ] with x hx hxn
    simpa only [hx] using hxn
  have hgz : (∫ x, G x) = 0 := by
    rw [integral_congr_ae he]
    exact (goodPart_integral (⇑f) hf Q hQ.disjoint).trans hz
  obtain ⟨u, hu, hnu⟩ := bounded_ball_hardy G hgz c (initialRadiusFactor d * r)
    (mul_pos hR hr) ((2 : ℝ) ^ d * t) (by positivity) hgs hgn
  refine ⟨u, hu, hnu.trans_eq ?_⟩
  have hvol : volume.real (Metric.ball c (initialRadiusFactor d * r)) =
      initialRadiusFactor d ^ d * V := by
    dsimp only [V]
    rw [ball_volume_scaling c (mul_pos hR hr), ball_volume_scaling c hr, mul_pow]
    ring
  rw [hvol]
  dsimp only [t]
  field_simp

end ExpandedFA.Hardy.HardyPAtoms.Dyadic


namespace ExpandedFA.Hardy.HardyPAtoms
open HardyPAtomsSpec ExpandedFA.Hardy.HardyPAtoms.Dyadic

/-- The uniform bound, including the singleton Euclidean space. -/
theorem pAtom_hardy_bound : AtomBound.{v} := by
  intro d p hp
  by_cases hd0 : d = 0
  · subst d
    refine ⟨1, zero_lt_one, fun {𝕜} _ a => ?_⟩
    have ha : a.val = 0 := zero_dim_mean_zero a.val a.property.2.1
    exact ⟨0, by simp [ha], by simp⟩
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  let I : ℝ := (2 : ℝ)^d * initialRadiusFactor d ^ d
  let K : ℝ := volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) ((d : ℝ)+1)) *
    (3 * (2 : ℝ)^d)
  let den : ℝ := 1 - (2 : ℝ) ^ (1-p)
  have hI : 0 ≤ I := mul_nonneg (by positivity)
    (pow_nonneg (initialRadiusFactor_pos d).le d)
  have hK : 0 ≤ K := mul_nonneg ENNReal.toReal_nonneg (by positivity)
  have hden : 0 < den := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  refine ⟨I + K / den + 1, by positivity, fun {𝕜} _ a => ?_⟩
  obtain ⟨c, r, hr, hs, hsize⟩ := a.property.2.2
  have hV : 0 < volume.real (Metric.ball c r) := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  have hinit := initial_goodPart_hardy hd a.val a.property.2.1 c r hr hs
    (pAtom_norm_le_one hp a)
  obtain ⟨u, hu, hn⟩ := hardy_of_goodApprox hd hp a.val a.property.1
    ((volume.real (Metric.ball c r))⁻¹) (inv_pos.mpr hV) I hinit
  refine ⟨u, hu, ?_⟩
  have hfactor := normalized_budget_factor hp hV ENNReal.toReal_nonneg hsize
  have hdiv : (eLpNorm a.val (ENNReal.ofReal p) volume).toReal ^ p *
      (volume.real (Metric.ball c r))⁻¹ ^ (1-p) / den ≤ 1 / den :=
    (div_le_div_iff_of_pos_right hden).mpr hfactor
  have hmul := mul_le_mul_of_nonneg_left hdiv hK
  change ‖u‖ ≤ I + K / den + 1
  change ‖u‖ ≤ I + K * _ at hn
  have heq : K * (1 / den) = K / den := by ring
  rw [heq] at hmul
  linarith

/-- Quantitative atomic expansions converge in L¹. -/
theorem pAtom_expansion : ExpansionBound.{v} := bound_to_expansion pAtom_hardy_bound

/-- All clauses of the source theorem. -/
theorem pAtoms_main : MainResult.{v} := assemble_from_expansion pAtom_expansion

end ExpandedFA.Hardy.HardyPAtoms
