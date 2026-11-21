import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.BorelNormSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.NormalPVM

/-!
The norm and spectral mapping clauses of `fa2:p2:normal-spectral`.
We first prove the result for any PVM. Cutting off reciprocal functions gives
norm and invertibility estimates on spectral subspaces, so no scalar control
measure, nonzero Hilbert space, or separability assumption is needed.
-/

noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set
open Classical
namespace ExpandedFA.SpectralMeasure.BorelNormSpectrum
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (E : ProjectionValuedMeasure S H)

abbrev BM (f : S → ℂ) := SpectralMeasure.Spec.IsBoundedMeasurable f

lemma bounded_const (c : ℂ) : BM (fun _ : S => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

lemma bounded_indicator (B : Set S) (hB : MeasurableSet B) {f : S → ℂ} (hf : BM f) :
    BM (B.indicator f) := by
  obtain ⟨C, hC, hbound⟩ := hf.nonneg_bound
  exact ⟨hf.1.indicator hB, C, fun s => by
    by_cases hs : s ∈ B <;> simp [hs, hC, hbound s]⟩

lemma integral_const (c : ℂ) : E.spectralIntegral (fun _ => c) = c • 1 := by
  have h := E.spectralIntegral_smul c (fun _ => 1) (bounded_const 1)
  have hc : c • (fun _ : S => (1 : ℂ)) = (fun _ => c) := by
    ext s
    simp
  rw [hc, E.spectralIntegral_one] at h
  exact h

lemma integral_neg {f : S → ℂ} (hf : BM f) :
    E.spectralIntegral (-f) = -E.spectralIntegral f := by
  simpa using E.spectralIntegral_smul (-1) f hf

lemma bounded_sub {f g : S → ℂ} (hf : BM f) (hg : BM g) : BM (f - g) := by
  simpa [sub_eq_add_neg] using hf.add (hg.smul (-1))

lemma integral_sub {f g : S → ℂ} (hf : BM f) (hg : BM g) :
    E.spectralIntegral (f - g) = E.spectralIntegral f - E.spectralIntegral g := by
  rw [sub_eq_add_neg, E.spectralIntegral_add f (-g) hf (by simpa using hg.smul (-1)),
    integral_neg E hg, sub_eq_add_neg]

lemma integral_indicator_one (B : Set S) (hB : MeasurableSet B) :
    E.spectralIntegral (B.indicator (fun _ => 1)) = E B := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [E.spectralIntegral_coefficient _ (bounded_indicator B hB (bounded_const 1)),
    VectorMeasure.integral_eq_setToFun,
    setToFun_indicator_const _ hB (measure_ne_top _ _)]
  simpa [VectorMeasure.transpose, ContinuousLinearMap.mul_apply',
    ProjectionValuedMeasure.coefficientMeasure_apply, coefficient, SpectralMeasure.Spec.CoefficientValue]
    using E.coefficientMeasure_apply x y B hB

lemma integral_indicator (B : Set S) (hB : MeasurableSet B)
    {f : S → ℂ} (hf : BM f) :
    E.spectralIntegral (B.indicator f) = E.spectralIntegral f * E B := by
  have heq : B.indicator f = f * B.indicator (fun _ => 1) := by
    ext s
    by_cases hs : s ∈ B <;> simp [hs]
  rw [heq, E.spectralIntegral_mul _ _ hf (bounded_indicator B hB (bounded_const 1)),
    integral_indicator_one E B hB]

lemma integral_congr_of_null {B : Set S} (hB : MeasurableSet B) (hnull : E B = 0)
    {f g : S → ℂ} (hf : BM f) (hg : BM g) (heq : ∀ s ∉ B, f s = g s) :
    E.spectralIntegral f = E.spectralIntegral g := by
  have hfg : B.indicator (f - g) = f - g := by
    ext s
    by_cases hs : s ∈ B
    · simp [hs]
    · simp [hs, heq s hs]
  have hz := integral_indicator E B hB (bounded_sub hf hg)
  rw [hfg, integral_sub E hf hg, hnull, mul_zero] at hz
  exact sub_eq_zero.mp hz

lemma norm_le_of_null_bound {f : S → ℂ} (hf : BM f) {C : ℝ} (hC : 0 ≤ C)
    (hnull : E {s | C < ‖f s‖} = 0) : ‖E.spectralIntegral f‖ ≤ C := by
  let B := {s | C < ‖f s‖}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hf.1.norm
  let g := Bᶜ.indicator f
  have hg := bounded_indicator Bᶜ hB.compl hf
  have heq : E.spectralIntegral f = E.spectralIntegral g :=
    integral_congr_of_null E hB hnull hf hg (fun s hs => by simp [g, hs])
  rw [heq]
  apply E.spectralIntegral_norm_le g hg C hC
  intro s
  by_cases hs : s ∈ B
  · simp [g, hs, hC]
  · simpa [g, hs] using le_of_not_gt hs

lemma projection_norm_eq_one {B : Set S} (hB : MeasurableSet B) (hne : E B ≠ 0) :
    ‖E B‖ = 1 := by
  have hp : 0 < ‖E B‖ := norm_pos_iff.mpr hne
  have h := norm_mul_le (E B) (E B)
  rw [E.idempotent B hB] at h
  exact le_antisymm (E.norm_le_one B hB) (by nlinarith)

/-- Local reciprocal, bounded after cutting away a neighbourhood of zero. -/
lemma bounded_reciprocal (f : S → ℂ) (hf : BM f) (r : ℝ) (hr : 0 < r) :
    BM ({s | r ≤ ‖f s‖}.indicator (fun s => (f s)⁻¹)) := by
  have hB : MeasurableSet {s | r ≤ ‖f s‖} := measurableSet_le measurable_const hf.1.norm
  refine ⟨hf.1.inv.indicator hB, r⁻¹, ?_⟩
  intro s
  by_cases hs : r ≤ ‖f s‖
  · simpa only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hs, norm_inv] using
      inv_anti₀ hr hs
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hs, norm_zero]
    exact le_of_lt (inv_pos.mpr hr)

/-- Any level strictly above the operator norm is E-null. -/
lemma null_above_norm {f : S → ℂ} (hf : BM f) {r : ℝ}
    (hr : ‖E.spectralIntegral f‖ < r) : E {s | r < ‖f s‖} = 0 := by
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr
  let B := {s | r < ‖f s‖}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hf.1.norm
  let g := B.indicator (fun s => (f s)⁻¹)
  have hg : BM g := by
    have heq : g = B.indicator ({s | r ≤ ‖f s‖}.indicator (fun s => (f s)⁻¹)) := by
      ext s
      by_cases hs : s ∈ B
      · have hs' : r ≤ ‖f s‖ := le_of_lt hs
        simp [g, hs, hs']
      · simp [g, hs]
    rw [heq]
    exact bounded_indicator B hB (bounded_reciprocal f hf r hr0)
  have hgBound : ∀ s, ‖g s‖ ≤ r⁻¹ := by
    intro s
    by_cases hs : s ∈ B
    · simpa [g, hs, norm_inv] using inv_anti₀ hr0 (le_of_lt hs)
    · simp [g, hs, le_of_lt (inv_pos.mpr hr0)]
  have heq : f * g = B.indicator (fun _ => 1) := by
    ext s
    by_cases hs : s ∈ B
    · have hn : f s ≠ 0 := norm_pos_iff.mp (hr0.trans hs)
      simp [g, hs, hn]
    · simp [g, hs]
  have hprod : E.spectralIntegral f * E.spectralIntegral g = E B := by
    rw [← E.spectralIntegral_mul f g hf hg, heq, integral_indicator_one E B hB]
  by_contra hne
  have hnorm := norm_mul_le (E.spectralIntegral f) (E.spectralIntegral g)
  rw [hprod, projection_norm_eq_one E hB hne] at hnorm
  have hgb := E.spectralIntegral_norm_le g hg r⁻¹ (by positivity) hgBound
  have hlt : ‖E.spectralIntegral f‖ * r⁻¹ < 1 := (mul_inv_lt_iff₀ hr0).mpr (by simpa using hr)
  have := mul_le_mul_of_nonneg_left hgb (norm_nonneg (E.spectralIntegral f))
  linarith

lemma norm_eq_essentialSup {f : S → ℂ} (hf : BM f) :
    ‖E.spectralIntegral f‖ = Spec.essentialSup E f := by
  let A := {C : ℝ | 0 ≤ C ∧ E {s | C < ‖f s‖} = 0}
  have hne : A.Nonempty := ⟨‖E.spectralIntegral f‖ + 1, by
    constructor
    · positivity
    · exact null_above_norm E hf (by linarith)⟩
  have hbd : BddBelow A := ⟨0, fun _ h => h.1⟩
  apply le_antisymm
  · exact le_csInf hne (fun C hC => norm_le_of_null_bound E hf hC.1 hC.2)
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact csInf_le hbd ⟨by positivity, null_above_norm E hf (by linarith)⟩


/-- Invertibility is equivalent to an E-essential gap around zero. The
reciprocal is cut off on the null set, hence is bounded everywhere. -/
lemma integral_isUnit_iff {f : S → ℂ} (hf : BM f) :
    IsUnit (E.spectralIntegral f) ↔
      ∃ r : ℝ, 0 < r ∧ E {s | ‖f s‖ < r} = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    let r : ℝ := (‖(↑u⁻¹ : H →L[ℂ] H)‖ + 1)⁻¹
    have hr : 0 < r := by dsimp [r]; positivity
    refine ⟨r, hr, ?_⟩
    let B := {s | ‖f s‖ < r}
    have hB : MeasurableSet B := measurableSet_lt hf.1.norm measurable_const
    let g := B.indicator f
    have hg : BM g := bounded_indicator B hB hf
    have hgb : ‖E.spectralIntegral g‖ ≤ r := by
      apply E.spectralIntegral_norm_le g hg r hr.le
      intro s
      by_cases hs : s ∈ B
      · simpa [g, hs] using le_of_lt hs
      · simp [g, hs, hr.le]
    have hid : E B = (↑u⁻¹ : H →L[ℂ] H) * E.spectralIntegral g := by
      rw [integral_indicator E B hB hf, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    by_contra hne
    have hp := norm_mul_le (↑u⁻¹ : H →L[ℂ] H) (E.spectralIntegral g)
    rw [← hid, projection_norm_eq_one E hB hne] at hp
    have hle := mul_le_mul_of_nonneg_left hgb (norm_nonneg (↑u⁻¹ : H →L[ℂ] H))
    have hlt : ‖(↑u⁻¹ : H →L[ℂ] H)‖ * r < 1 := by
      dsimp [r]
      apply (mul_inv_lt_iff₀ (by positivity)).mpr
      linarith
    linarith
  · rintro ⟨r, hr, hnull⟩
    let B := {s | ‖f s‖ < r}
    have hB : MeasurableSet B := measurableSet_lt hf.1.norm measurable_const
    let g := {s | r ≤ ‖f s‖}.indicator (fun s => (f s)⁻¹)
    have hg : BM g := bounded_reciprocal f hf r hr
    have hfg : E.spectralIntegral (f * g) = 1 := by
      rw [← E.spectralIntegral_one]
      apply integral_congr_of_null E hB hnull (hf.mul hg) (bounded_const 1)
      intro s hs
      have hs' : r ≤ ‖f s‖ := le_of_not_gt hs
      have hn : f s ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hr hs')
      simp [g, hs', hn]
    have hgf : E.spectralIntegral (g * f) = 1 := by
      simpa only [mul_comm] using hfg
    exact isUnit_iff_exists.mpr ⟨E.spectralIntegral g,
      by rw [← E.spectralIntegral_mul f g hf hg]; exact hfg,
      by rw [← E.spectralIntegral_mul g f hg hf]; exact hgf⟩

lemma spectrum_eq_essentialRange {f : S → ℂ} (hf : BM f) :
    spectrum ℂ (E.spectralIntegral f) = Spec.essentialRange E f := by
  ext z
  have hshift : E.spectralIntegral ((fun _ : S => z) - f) =
      algebraMap ℂ (H →L[ℂ] H) z - E.spectralIntegral f := by
    rw [integral_sub E (bounded_const z) hf, integral_const E z,
      Algebra.algebraMap_eq_smul_one]
  rw [spectrum.mem_iff, ← hshift, integral_isUnit_iff E (bounded_sub (bounded_const z) hf)]
  simp only [Spec.essentialRange, Set.mem_ofPred_eq, not_exists, not_and,
    Pi.sub_apply, norm_sub_rev]

lemma borel_calculus : Spec.BorelCalculus E E.spectralIntegral := by
  refine ⟨E.spectralIntegral_one, E.spectralIntegral_add, E.spectralIntegral_smul,
    E.spectralIntegral_mul, E.spectralIntegral_star, E.coefficientMeasure, ?_, ?_⟩
  · intro x y B hB
    exact E.coefficientMeasure_apply x y B hB
  · exact E.spectralIntegral_coefficient

theorem pvm_norm_spectrum : Spec.PVMNormSpectrum.{u, v} := by
  intro S H _ _ _ _ E
  exact ⟨E.spectralIntegral, borel_calculus E, fun f hf =>
    ⟨norm_eq_essentialSup E hf, spectrum_eq_essentialRange E hf⟩⟩

theorem normal_norm_spectrum : Spec.NormalNormSpectrum.{v} := by
  intro H _ _ _ N hN
  obtain ⟨E, hE, _⟩ := NormalPVM.normal_spectral_theorem H N hN
  refine ⟨E, E.spectralIntegral, hE, borel_calculus E, ?_, ?_⟩
  · have h := NormalPVM.continuousIntegral_coordinate E hE
    exact h
  · intro f hf
    exact ⟨norm_eq_essentialSup E hf, spectrum_eq_essentialRange E hf⟩

theorem zero_space : Spec.ZeroSpace.{u, v} := by
  intro S H _ _ _ _ _ E f hf
  constructor
  · rw [← norm_eq_essentialSup E hf]
    have hz : E.spectralIntegral f = 0 := Subsingleton.elim _ _
    simp [hz]
  · rw [← spectrum_eq_essentialRange E hf]
    exact spectrum.of_subsingleton (R := ℂ) _

end ExpandedFA.SpectralMeasure.BorelNormSpectrum
