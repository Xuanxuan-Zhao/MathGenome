import MathGenome.Internal.RealAnalysis.D11.Ch13.MeasureDifferentiation
import MathGenome.Internal.RealAnalysis.D11.Ch15.LebesgueRNSigmaFiniteSigned
import MathGenome.Internal.RealAnalysis.D11.Ch15.LebesgueDecompositionSigmaFinite
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.RegularMeasureDifferentiation

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace D11.Ch13.RegularMeasureDifferentiation
open D11.Ch03 D11.Ch03.LebesgueMeasures
open D11.Ch13.MeasureDifferentiation D11.Ch13.AveragesMaximalDefinition
open D11.Ch13.RegularShrinking
variable {n : ℕ} [NeZero n]

/-- The Vitali singular theorem requires local finiteness only. In particular,
no finite-total-mass assumption is used in this extension. -/
lemma singular_balls_borel (σ : Measure (Point n)) [IsFiniteMeasureOnCompacts σ]
    (hs : σ ⟂ₘ (volume : Measure (Point n))) :
    ∀ᵐ x ∂(volume : Measure (Point n)),
      Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let v := IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure (Point n)) 0
  filter_upwards [v.ae_eventually_measure_zero_of_singular hs] with x hx
  have hclosed : Tendsto
      (fun r => σ (closedBall x r) / (volume : Measure (Point n)) (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hx.comp
    apply IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt _
      (fun _ : ℝ => x) id tendsto_id
    exact Eventually.of_forall (fun r => by simp)
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hclosed
  simp only [ENNReal.toReal_zero] at hreal
  apply squeeze_zero (fun r => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) _ hreal
  intro r
  change (σ (ball x r)).toReal / (lebesgue n (ball x r)).toReal ≤
    (σ (closedBall x r) / (volume : Measure (Point n)) (closedBall x r)).toReal
  rw [ENNReal.toReal_div, completed_eq_native _ (ball_measurable x r),
    Measure.addHaar_closedBall_eq_addHaar_ball (volume : Measure (Point n)) x r]
  exact div_le_div_of_nonneg_right
    (ENNReal.toReal_mono (measure_closedBall_lt_top (μ := σ)).ne (measure_mono ball_subset_closedBall))
    ENNReal.toReal_nonneg

theorem singular_centered_balls :
    Specs.D11.Ch13.RegularMeasureDifferentiation.singular_centered_balls := by
  intro n _ σ _ hs
  have h := singular_balls_borel σ hs
  change ∀ᵐ x ∂Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value n,
    Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) at h
  rw [← borel_restriction n (native_borel_le n)] at h
  exact ae_of_ae_trim (native_borel_le n) h

/-- A positive fraction guarantees a finite nonzero denominator. -/
lemma nice_volume {x : Point n} {c : ℝ} {E : ℝ → Set (Point n)}
    (h : NiceFamily x c E) (r : ℝ) (hr : 0 < r) :
    0 < lebesgue n (E r) ∧ lebesgue n (E r) < ∞ := by
  have hb := ball_measure x r hr
  exact ⟨(ENNReal.mul_pos (ENNReal.ofReal_pos.mpr h.1).ne' hb.1.ne').trans_le
      (h.2 r hr).2.2,
    (measure_mono (h.2 r hr).2.1).trans_lt hb.2.1⟩

/-- This comparison uses only finiteness on the enclosing ball. -/
lemma nice_ratio_bound (σ : Measure (Point n)) [IsFiniteMeasureOnCompacts σ]
    {x : Point n} {c : ℝ} {E : ℝ → Set (Point n)}
    (h : NiceFamily x c E) (r : ℝ) (hr : 0 < r) :
    measureRatio σ (E r) ≤ c⁻¹ * measureRatio σ (ball x r) := by
  have hv := nice_volume h r hr
  have hb := ball_measure x r hr
  have hfrac : ENNReal.ofReal c * lebesgue n (ball x r) ≤ lebesgue n (E r) :=
    (h.2 r hr).2.2
  have hd : c * (lebesgue n (ball x r)).toReal ≤ (lebesgue n (E r)).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal h.1.le] using
      ENNReal.toReal_mono hv.2.ne hfrac
  have hm := ENNReal.toReal_mono (measure_ball_ne_top (μ := σ))
    (measure_mono (h.2 r hr).2.1 : σ (E r) ≤ σ (ball x r))
  have hE : 0 < (lebesgue n (E r)).toReal := ENNReal.toReal_pos hv.1.ne' hv.2.ne
  change (σ (E r)).toReal / (lebesgue n (E r)).toReal ≤
    c⁻¹ * ((σ (ball x r)).toReal / (lebesgue n (ball x r)).toReal)
  apply (div_le_iff₀ hE).mpr
  apply (le_trans hm)
  rw [inv_mul_eq_div, div_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hb.2.2 h.1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hd (ENNReal.toReal_nonneg (a := σ (ball x r)))]

/-- The same centered limit controls every nice family, independently of c. -/
theorem singular_nice_of_balls (σ : Measure (Point n)) [IsFiniteMeasureOnCompacts σ]
    {x : Point n}
    (hx : Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ScalarNiceLimit (fun E => (σ E).toReal) 0 x := by
  intro c E hE
  refine ⟨fun r hr => nice_volume hE r hr, ?_⟩
  have hu := hx.const_mul c⁻¹
  simp only [mul_zero] at hu
  have ht : Tendsto (fun r => measureRatio σ (E r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun r => div_nonneg
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg) _ hu
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact nice_ratio_bound σ hE r hr
  simpa only [measureRatio, smul_eq_mul, div_eq_inv_mul] using ht

/-- A scalar singular set function dominated by σ has all the same nice
limits. Only sets inside a ball are evaluated by this assertion. -/
lemma dominated_nice_of_balls {𝕜 : Type} [RCLike 𝕜]
    (S : Set (Point n) → 𝕜) (σ : Measure (Point n)) [IsFiniteMeasureOnCompacts σ]
    (hS : ∀ (x : Point n) (r : ℝ) (E : Set (Point n)), MeasurableSet E →
      E ⊆ ball x r → ‖S E‖ ≤ (σ E).toReal)
    {x : Point n}
    (hx : Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ScalarNiceLimit S 0 x := by
  intro c E hE
  have hσ := singular_nice_of_balls σ hx c E hE
  refine ⟨hσ.1, ?_⟩
  apply squeeze_zero_norm' _ hσ.2
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  exact mul_le_mul_of_nonneg_left (hS x r (E r) (hE.2 r hr).1 (hE.2 r hr).2.1)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- The density comparison at one Lebesgue point is uniform in the family. -/
lemma density_nice_at_lebesguePoint {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point n → 𝕜) (hf : locallyIntegrable f) {x : Point n}
    (hx : lebesguePoint f hf x) :
    ScalarNiceLimit (fun E => ∫ y in E, f y ∂lebesgue n) (f x) x := by
  intro c E hE
  refine ⟨fun r hr => nice_volume hE r hr, ?_⟩
  let g : Point n → ℝ := fun y => ‖f y - f x‖
  have hg : locallyIntegrable g := locallyIntegrable_norm _
    (locallyIntegrable_sub_const f hf (f x))
  have hu : Tendsto (fun r => c⁻¹ * setMean g (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun r => setMean g (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := hx
    simpa only [mul_zero] using h.const_mul c⁻¹
  have hdiff : Tendsto (fun r => setMean f (E r) - f x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm' _ hu
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hv := nice_volume hE r hr
    have hb := ball_measure x r hr
    have hi := integrableOn_subset_ball f hf (hE.2 r hr).2.1
    rw [← mean_sub_const f (f x) (E r) hi hv.1.ne' hv.2.ne]
    apply (norm_mean_le _ _).trans
    have hfrac : ENNReal.ofReal c * lebesgue n (ball x r) ≤ lebesgue n (E r) :=
      (hE.2 r hr).2.2
    have hd : c * (lebesgue n (ball x r)).toReal ≤ (lebesgue n (E r)).toReal := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hE.1.le] using
        ENNReal.toReal_mono hv.2.ne hfrac
    apply mean_comparison (hE.2 r hr).2.1
      (integrableOn_subset_ball g hg Subset.rfl) (fun _ => norm_nonneg _)
      (ENNReal.toReal_pos hv.1.ne' hv.2.ne) hb.2.2
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hE.1).mpr (by nlinarith [hd])
  change Tendsto (fun r => setMean f (E r)) (𝓝[>] (0 : ℝ)) (𝓝 (f x))
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const (f x)

/-- Intersect the singular-variation conull set with the density Lebesgue
points before quantifying over c and over E. -/
theorem scalar_local_differentiation {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (V S : Set (Point n) → 𝕜) (σ : Measure (Point n)) [IsFiniteMeasureOnCompacts σ]
    (hs : σ ⟂ₘ (volume : Measure (Point n)))
    (f : Point n → 𝕜) (hf : locallyIntegrable f)
    (hS : ∀ (x : Point n) (r : ℝ) (E : Set (Point n)), MeasurableSet E →
      E ⊆ ball x r → ‖S E‖ ≤ (σ E).toReal)
    (hV : ∀ (x : Point n) (r : ℝ) (E : Set (Point n)), MeasurableSet E →
      E ⊆ ball x r → V E = (∫ y in E, f y ∂lebesgue n) + S E) :
    ∃ N : Set (Point n), MeasurableSet[lebesgueSpace n] N ∧ lebesgue n N = 0 ∧
      ∀ x ∉ N,
        DensityLebesguePoint f x ∧
        Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        ScalarNiceLimit V (f x) x ∧ ScalarNiceLimit S 0 x := by
  have hg := (singular_centered_balls σ hs).and
    (D11.Ch13.LebesgueDifferentiation.ae_lebesguePoint f hf)
  obtain ⟨N, hsub, hNm, hN0⟩ := @exists_measurable_superset_of_null (Point n)
    (lebesgueSpace n) (lebesgue n) _ (ae_iff.mp hg)
  refine ⟨N, hNm, hN0, ?_⟩
  intro x hx
  have hp : Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      lebesguePoint f hf x := by
    by_contra hn
    exact hx (hsub hn)
  have hSx := dominated_nice_of_balls S σ hS hp.1
  have hfx := density_nice_at_lebesguePoint f hf hp.2
  refine ⟨⟨hf, hp.2⟩, hp.1, ?_, hSx⟩
  intro c E hE
  refine ⟨(hSx c E hE).1, ?_⟩
  have ht := (hfx c E hE).2.add (hSx c E hE).2
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [hV x r (E r) (hE.2 r hr).1 (hE.2 r hr).2.1, smul_add]

/-- A singular positive part is compact-finite whenever the whole measure is. -/
lemma positive_singular_compact_finite (ν σ : Measure (Point n))
    [IsFiniteMeasureOnCompacts ν] (f : Point n → ℝ)
    (h : DensityDecomposition ν σ f) : IsFiniteMeasureOnCompacts σ := by
  constructor
  intro K hK
  exact (le_add_left le_rfl |>.trans_eq (h.2.2.2 K hK.measurableSet).symm).trans_lt
    (hK.measure_lt_top (μ := ν))

/-- Compact finiteness forces local absolute integrability of every selected
real representative, including representatives only measurable in the completion. -/
lemma positive_density_locallyIntegrable (ν σ : Measure (Point n))
    [IsFiniteMeasureOnCompacts ν] (f : Point n → ℝ)
    (h : DensityDecomposition ν σ f) : locallyIntegrable f := by
  apply (locallyIntegrable_iff f).mpr
  refine ⟨h.1, fun K hK => ?_⟩
  refine ⟨h.1.aestronglyMeasurable.restrict, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_restrict_of_ae h.2.1)).mpr
  exact (le_add_right le_rfl |>.trans_eq
    (h.2.2.2 K hK.measurableSet).symm).trans_lt (hK.measure_lt_top (μ := ν))

lemma positive_local_identity (ν σ : Measure (Point n))
    [IsFiniteMeasureOnCompacts ν] (f : Point n → ℝ)
    (h : DensityDecomposition ν σ f) (x : Point n) (r : ℝ)
    (E : Set (Point n)) (hE : MeasurableSet E) (hEB : E ⊆ ball x r) :
    (ν E).toReal = (∫ y in E, f y ∂lebesgue n) + (σ E).toReal := by
  have : IsFiniteMeasureOnCompacts σ := positive_singular_compact_finite ν σ f h
  have hf := positive_density_locallyIntegrable ν σ f h
  have hi := integrableOn_subset_ball f hf hEB
  have hn : ∀ᵐ y ∂(lebesgue n).restrict E, 0 ≤ f y := ae_restrict_of_ae h.2.1
  have hI : (∫⁻ y in E, ENNReal.ofReal (f y) ∂lebesgue n) ≠ ∞ :=
    (hasFiniteIntegral_iff_ofReal hn).mp hi.2 |>.ne
  have hσ : σ E ≠ ∞ := ne_top_of_le_ne_top (measure_ball_ne_top (μ := σ))
    (measure_mono hEB)
  have heq : ν E = (∫⁻ y in E, ENNReal.ofReal (f y) ∂lebesgue n) + σ E :=
    h.2.2.2 E hE
  rw [heq, ENNReal.toReal_add hI hσ,
    ← integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable]

/-- Sigma-finite Borel RN gives a finite real representative. Its total
integral is allowed to be infinite. -/
lemma exists_positive_decomposition (ν : Measure (Point n))
    [IsFiniteMeasureOnCompacts ν] :
    ∃ (f : Point n → ℝ) (σ : Measure (Point n)), DensityDecomposition ν σ f := by
  let m : Measure (Point n) := volume
  let g : Point n → ℝ := fun x => (ν.rnDeriv m x).toReal
  let σ := ν.singularPart m
  have hm : Measurable (ν.rnDeriv m) := Measure.measurable_rnDeriv ν m
  have hgm : Measurable g := hm.ennreal_toReal
  have hfinite : ∀ᵐ x ∂m, ν.rnDeriv m x ≠ ∞ :=
    (Measure.rnDeriv_lt_top ν m).mono (fun _ hx => hx.ne)
  refine ⟨g, σ, hgm.mono (native_borel_le n) le_rfl,
    ae_of_all _ (fun _ => ENNReal.toReal_nonneg),
    Measure.mutuallySingular_singularPart ν m, ?_⟩
  intro E hE
  have heq : ν E = σ E + (m.withDensity (ν.rnDeriv m)) E := by
    have ht := congrArg (fun ρ : Measure (Point n) => ρ E)
      (Measure.haveLebesgueDecomposition_add ν m)
    simpa only [Measure.add_apply] using ht
  change ν E = (∫⁻ y in E, ENNReal.ofReal (g y) ∂lebesgue n) + σ E
  rw [heq, setLIntegral_completed_eq (fun y => ENNReal.ofReal (g y))
      (ENNReal.measurable_ofReal.comp hgm) E hE, withDensity_apply _ hE, add_comm]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hfinite] with y hy
  exact (ENNReal.ofReal_toReal hy).symm

/-- Full positive case, including existence and every fixed measurable density. -/
theorem positive_differentiation :
    Specs.D11.Ch13.RegularMeasureDifferentiation.positive_differentiation := by
  intro n _ ν _ _
  refine ⟨exists_positive_decomposition ν, ?_⟩
  intro f σ h
  have : IsFiniteMeasureOnCompacts σ := positive_singular_compact_finite ν σ f h
  have hf := positive_density_locallyIntegrable ν σ f h
  refine ⟨hf, fun x r => ⟨measure_ball_lt_top, measure_ball_lt_top⟩, ?_⟩
  apply scalar_local_differentiation (fun E => (ν E).toReal)
    (fun E => (σ E).toReal) σ h.2.2.1 f hf _ (positive_local_identity ν σ f h)
  intro x r E _ _
  exact le_of_eq (Real.norm_of_nonneg ENNReal.toReal_nonneg)

/-- Completion preserves Borel scalar integrals, also after restriction. -/
lemma setIntegral_completed_eq {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point n → 𝕜) (hf : Measurable f)
    (E : Set (Point n)) (hE : MeasurableSet E) :
    (∫ y in E, f y ∂lebesgue n) = ∫ y in E, f y ∂(volume : Measure (Point n)) := by
  calc
    _ = ∫ y, f y ∂((lebesgue n).restrict E).trim (native_borel_le n) :=
      integral_trim (native_borel_le n) hf.stronglyMeasurable
    _ = _ := by
      rw [← restrict_trim (native_borel_le n) (lebesgue n) hE]
      have ht : (lebesgue n).trim (native_borel_le n) = (volume : Measure (Point n)) :=
        borel_restriction n _
      rw [ht]

lemma integrableOn_completed {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point n → 𝕜) (E : Set (Point n)) (hE : MeasurableSet E)
    (hi : IntegrableOn f E (volume : Measure (Point n))) :
    IntegrableOn f E (lebesgue n) := by
  apply integrable_of_integrable_trim (native_borel_le n)
  rw [← restrict_trim (native_borel_le n) (lebesgue n) hE]
  have ht : (lebesgue n).trim (native_borel_le n) = (volume : Measure (Point n)) :=
    borel_restriction n _
  rw [ht]
  exact hi

/-- All extended signed values of finite variation are actual real values;
this is proved before using their real-valued ratios. -/
lemma signed_finite_value
    (ν : D11.Ch14.ScalarInterfaces.ExtendedSignedMeasure (Point n))
    (E : Set (Point n)) (hE : MeasurableSet E)
    (hv : D11.Ch14.ExtendedSignedVariant.variation ν E < ∞) :
    (ν.value ⟨E,hE⟩ ≠ ⊤ ∧ ν.value ⟨E,hE⟩ ≠ ⊥) ∧
      ‖signedValue ν E‖ ≤ (D11.Ch14.ExtendedSignedVariant.variation ν E).toReal := by
  classical
  have hj := (D11.Ch14.ExtendedSignedVariant.jordan_decomposition ν).2.2 E hE
  have hparts : D11.Ch14.ExtendedSignedVariant.positivePart ν E +
      D11.Ch14.ExtendedSignedVariant.negativePart ν E < ∞ := hv
  obtain ⟨hp, hq⟩ := ENNReal.add_lt_top.mp hparts
  have heq : ν.value ⟨E,hE⟩ =
      (((D11.Ch14.ExtendedSignedVariant.positivePart ν E).toReal -
        (D11.Ch14.ExtendedSignedVariant.negativePart ν E).toReal : ℝ) : EReal) := by
    rw [hj, EReal.coe_sub, EReal.coe_ennreal_toReal hp.ne, EReal.coe_ennreal_toReal hq.ne]
  refine ⟨by rw [heq]; exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩, ?_⟩
  rw [signedValue, dite_eq_left hE, heq, EReal.toReal_coe]
  change ‖(D11.Ch14.ExtendedSignedVariant.positivePart ν E).toReal -
    (D11.Ch14.ExtendedSignedVariant.negativePart ν E).toReal‖ ≤
    (D11.Ch14.ExtendedSignedVariant.positivePart ν E +
      D11.Ch14.ExtendedSignedVariant.negativePart ν E).toReal
  rw [ENNReal.toReal_add hp.ne hq.ne, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a :=
    D11.Ch14.ExtendedSignedVariant.positivePart ν E)], by
      linarith [ENNReal.toReal_nonneg (a := D11.Ch14.ExtendedSignedVariant.negativePart ν E)]⟩

/-- The finite complex case uses scalar RN and the variation of the singular
restriction, then the same common-null-set argument as for positive measures. -/
theorem complex_differentiation :
    Specs.D11.Ch13.RegularMeasureDifferentiation.complex_differentiation := by
  intro n _ ν _ _
  obtain ⟨Z, hZ, hZ0, hdec, f, hf⟩ :=
    D11.Ch15.LebesgueDecompositionSigmaFinite.complex_decomposition
      (volume : Measure (Point n)) ν
  let a := ν.restrict Zᶜ
  let s := ν.restrict Z
  let σ := D11.Ch14.TotalVariation.totalVariation s
  have : IsFiniteMeasure σ := hdec.2.1
  have hsing : σ ⟂ₘ (volume : Measure (Point n)) := by
    obtain ⟨A, hA, hsA, hmA⟩ := hdec.2.2.2.2.1
    refine ⟨Aᶜ, hA.compl, ?_, by simpa only [compl_compl] using hmA⟩
    exact (D11.Ch14.TotalVariation.totalVariation_apply s Aᶜ hA.compl).trans hsA
  have hi : Integrable f (lebesgue n) := by
    apply integrable_of_integrable_trim (native_borel_le n)
    have ht : (lebesgue n).trim (native_borel_le n) = (volume : Measure (Point n)) :=
      borel_restriction n _
    rw [ht]
    exact hf.2.1
  have hfloc := D11.Ch13.MaximalWeak11.locallyIntegrable_of_integrable f
    (hf.1.mono (native_borel_le n) le_rfl) hi
  refine ⟨a, s, f, hdec, hf, hfloc, ?_⟩
  apply scalar_local_differentiation (fun E => ν E) (fun E => s E) σ hsing f hfloc
  · intro x r E hE hEB
    have hb : ENNReal.ofReal ‖s E‖ ≤ σ E :=
      D11.Ch14.TotalVariation.norm_le_totalVariation s E
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using
      ENNReal.toReal_mono (measure_ne_top σ E) hb
  · intro x r E hE hEB
    have heq : ν = a + s := hdec.2.2.1
    rw [heq, VectorMeasure.add_apply]
    have ha : a E = ∫ y in E, f y ∂(volume : Measure (Point n)) := hf.2.2.1 E hE
    rw [ha, setIntegral_completed_eq f hf.1 E hE]

open D11.Ch14.ScalarInterfaces D11.Ch14.ExtendedSignedVariant

lemma signed_locally_finite (ν : ExtendedSignedMeasure (Point n))
    [IsFiniteMeasureOnCompacts (variation ν)] : SignedLocallyFinite ν := by
  intro x r E hE hEB
  apply (signed_finite_value ν E hE _).1
  exact (measure_mono hEB).trans_lt (measure_ball_lt_top (μ := variation ν))

lemma signed_density_locallyIntegrable (a : ExtendedSignedMeasure (Point n))
    [IsFiniteMeasureOnCompacts (variation a)] (f : Point n → ℝ)
    (hf : Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.Density
      (volume : Measure (Point n)) a f) : locallyIntegrable f := by
  apply (locallyIntegrable_iff f).mpr
  refine ⟨hf.1.mono (native_borel_le n) le_rfl, fun K hK => ?_⟩
  apply integrableOn_completed f K hK.measurableSet
  apply (integrable_indicator_iff hK.measurableSet).mp
  exact D11.Ch15.LebesgueRNSigmaFiniteSigned.density_local_integrable
    (volume : Measure (Point n)) a f hf K hK.measurableSet (hK.measure_lt_top (μ := variation a))

/-- On finite-variation Borel sets the extended RN identity equals the honest
Bochner integral, whose integrability is established first. -/
lemma signed_density_value (a : ExtendedSignedMeasure (Point n))
    [IsFiniteMeasureOnCompacts (variation a)] (f : Point n → ℝ)
    (hf : Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned.Density
      (volume : Measure (Point n)) a f)
    (x : Point n) (r : ℝ) (E : Set (Point n))
    (hE : MeasurableSet E) (hEB : E ⊆ ball x r) :
    signedValue a E = ∫ y in E, f y ∂lebesgue n := by
  classical
  have hv : variation a E < ∞ := (measure_mono hEB).trans_lt measure_ball_lt_top
  have hi : IntegrableOn f E (volume : Measure (Point n)) :=
    (integrable_indicator_iff hE).mp
      (D11.Ch15.LebesgueRNSigmaFiniteSigned.density_local_integrable
        (volume : Measure (Point n)) a f hf E hE hv)
  have hp : (∫⁻ y in E, ENNReal.ofReal (f y) ∂(volume : Measure (Point n))) < ∞ :=
    (lintegral_ofReal_le_lintegral_enorm _).trans_lt hi.2
  have hn : (∫⁻ y in E, ENNReal.ofReal (-f y) ∂(volume : Measure (Point n))) < ∞ :=
    (lintegral_ofReal_le_lintegral_enorm _).trans_lt hi.neg.2
  calc
    signedValue a E =
        (∫⁻ y in E, ENNReal.ofReal (f y) ∂(volume : Measure (Point n))).toReal -
        (∫⁻ y in E, ENNReal.ofReal (-f y) ∂(volume : Measure (Point n))).toReal := by
      rw [signedValue, dite_eq_left hE, hf.2.2 E hE,
        EReal.toReal_sub (by simpa using hp.ne) (EReal.coe_ennreal_ne_bot _)
          (by simpa using hn.ne) (EReal.coe_ennreal_ne_bot _),
        EReal.toReal_coe_ennreal, EReal.toReal_coe_ennreal]
    _ = ∫ y in E, f y ∂(volume : Measure (Point n)) :=
      (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi).symm
    _ = _ := (setIntegral_completed_eq f hf.1 E hE).symm

/-- Full extended signed case. Restrictions retain the globally omitted
infinity, while compact finiteness excludes both infinities on every averaging set. -/
theorem signed_differentiation :
    Specs.D11.Ch13.RegularMeasureDifferentiation.signed_differentiation := by
  intro n _ ν hν _
  have : IsFiniteMeasureOnCompacts (variation ν) := hν
  obtain ⟨Z, hZ, hZ0, hdec⟩ :=
    D11.Ch15.LebesgueRNSigmaFiniteSigned.decomposition_exists
      (volume : Measure (Point n)) ν
  let a := D11.Ch15.LebesgueRNSigmaFiniteSigned.restrict ν Zᶜ hZ.compl
  let s := D11.Ch15.LebesgueRNSigmaFiniteSigned.restrict ν Z hZ
  have ha_var : variation a = (variation ν).restrict Zᶜ :=
    D11.Ch15.LebesgueRNSigmaFiniteSigned.restrict_variation ν Zᶜ hZ.compl
  have hs_var : variation s = (variation ν).restrict Z :=
    D11.Ch15.LebesgueRNSigmaFiniteSigned.restrict_variation ν Z hZ
  have : IsFiniteMeasureOnCompacts (variation a) := by rw [ha_var]; infer_instance
  have : IsFiniteMeasureOnCompacts (variation s) := by rw [hs_var]; infer_instance
  have : SigmaFinite (Specs.D11.Ch14.ExtendedSignedVariant.variation_value a) := hdec.1
  obtain ⟨f, hf⟩ := D11.Ch15.LebesgueRNSigmaFiniteSigned.density_exists
    (volume : Measure (Point n)) a hdec.2.2.2.2.1
  have hfloc := signed_density_locallyIntegrable a f hf
  have hsing : variation s ⟂ₘ (volume : Measure (Point n)) := by
    obtain ⟨A, hA, hsA, hmA⟩ := hdec.2.2.2.2.2
    exact ⟨Aᶜ, hA.compl, hsA, by simpa only [compl_compl] using hmA⟩
  refine ⟨a, s, f, hdec, hf, hfloc, signed_locally_finite ν, signed_locally_finite s, ?_⟩
  apply scalar_local_differentiation (signedValue ν) (signedValue s) (variation s)
    hsing f hfloc
  · intro x r E hE hEB
    exact (signed_finite_value s E hE
      ((measure_mono hEB).trans_lt measure_ball_lt_top)).2
  · intro x r E hE hEB
    classical
    have hfa := signed_locally_finite a x r E hE hEB
    have hfs := signed_locally_finite s x r E hE hEB
    have heq : signedValue ν E = signedValue a E + signedValue s E := by
      simp only [signedValue, dite_eq_left hE]
      rw [hdec.2.2.2.1 ⟨E,hE⟩, EReal.toReal_add hfa.1 hfa.2 hfs.1 hfs.2]
    rw [heq, signed_density_value a f hf x r E hE hEB]

/-- Uniformity also holds for any supplied signed decomposition and any
completed density representative, not just the Borel witness selected by RN. -/
theorem signed_given_decomposition :
    Specs.D11.Ch13.RegularMeasureDifferentiation.signed_given_decomposition := by
  intro n _ ν a s hν _ hd f hf ha
  have : IsFiniteMeasureOnCompacts (variation ν) := hν
  obtain ⟨Z, hZ, hsZ, hmZ⟩ := hd.2.2.2.2.2
  have hp := D11.Ch15.LebesgueRNSigmaFiniteSigned.parts_from_null_support
    (volume : Measure (Point n)) ν a s Z hZ hmZ hsZ hd.2.2.2.1 hd.2.2.2.2.1
  have : IsFiniteMeasureOnCompacts (variation a) := by
    rw [hp.1, D11.Ch15.LebesgueRNSigmaFiniteSigned.restrict_variation]
    infer_instance
  have : IsFiniteMeasureOnCompacts (variation s) := by
    rw [hp.2, D11.Ch15.LebesgueRNSigmaFiniteSigned.restrict_variation]
    infer_instance
  have hs : variation s ⟂ₘ (volume : Measure (Point n)) :=
    ⟨Zᶜ, hZ.compl, hsZ, by rw [compl_compl]; exact hmZ⟩
  refine ⟨signed_locally_finite ν, signed_locally_finite s, ?_⟩
  apply scalar_local_differentiation (signedValue ν) (signedValue s) (variation s) hs f hf
  · intro x r E hE hEB
    exact (signed_finite_value s E hE ((measure_mono hEB).trans_lt measure_ball_lt_top)).2
  · intro x r E hE hEB
    classical
    have hfa := signed_locally_finite a x r E hE hEB
    have hfs := signed_locally_finite s x r E hE hEB
    have heq : signedValue ν E = signedValue a E + signedValue s E := by
      simp only [signedValue, dite_eq_left hE]
      rw [hd.2.2.2.1 ⟨E,hE⟩, EReal.toReal_add hfa.1 hfa.2 hfs.1 hfs.2]
    have ha' : signedValue a E = ∫ y in E, f y ∂lebesgue n := ha x r E hE hEB
    rw [heq, ha']

/-- Arbitrary completed representatives in the finite complex case. -/
theorem complex_given_decomposition :
    Specs.D11.Ch13.RegularMeasureDifferentiation.complex_given_decomposition := by
  intro n _ ν a s _ _ hd f hf ha
  let σ := D11.Ch14.TotalVariation.totalVariation s
  have : IsFiniteMeasure σ := hd.2.1
  have hs : σ ⟂ₘ (volume : Measure (Point n)) := by
    obtain ⟨Z, hZ, hsZ, hmZ⟩ := hd.2.2.2.2.1
    refine ⟨Zᶜ, hZ.compl, ?_, by rw [compl_compl]; exact hmZ⟩
    exact (D11.Ch14.TotalVariation.totalVariation_apply s Zᶜ hZ.compl).trans hsZ
  apply scalar_local_differentiation (fun E => ν E) (fun E => s E) σ hs f hf
  · intro x r E hE hEB
    have hb : ENNReal.ofReal ‖s E‖ ≤ σ E :=
      D11.Ch14.TotalVariation.norm_le_totalVariation s E
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using
      ENNReal.toReal_mono (measure_ne_top σ E) hb
  · intro x r E hE hEB
    have heq : ν = a + s := hd.2.2.1
    have ha' : a E = ∫ y in E, f y ∂lebesgue n := ha x r E hE hEB
    rw [heq, VectorMeasure.add_apply, ha']

end D11.Ch13.RegularMeasureDifferentiation
