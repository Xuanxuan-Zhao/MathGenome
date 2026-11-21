import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.RoydenLebesgueVitali
import MathGenome.Internal.RealAnalysis.D11.Ch17.VitaliLpConvergence
import MathGenome.Internal.RealAnalysis.D11.Ch07.FiniteAeToMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch05.Fatou

/-! Pointwise Vitali convergence, paper.tex:5282–5290. The proof passes from
pointwise convergence and spatial tails to global convergence in measure.
Fatou transfers the tails to the candidate limit before its integrability is
known. The existing Vitali criterion then proves L1 membership and convergence.
No uniform norm bound is assumed or needed in this route. -/
open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u
noncomputable section
namespace D11.Ch17.RoydenLebesgueVitali
open D11.Ch17.UniformControls D11.Ch06.ScalarIntegral
open D11.Ch07.ConvergenceDefinitions D11.Ch05.NonnegativeIntegral
open D11.Ch10.LpDefinition

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Fatou transfers a uniform set-integral bound to the pointwise limit.
The integral on the left may initially be infinite. -/
theorem absoluteIntegral_limit_le (μ : Measure X) (F : ℕ → X → 𝕜)
    (f : X → 𝕜) (hF : ∀ n, Measurable (F n))
    (hlim : pointwiseConverges F f) (A : Set X) :
    absoluteIntegral μ f A ≤ integralSup μ F A := by
  rw [absoluteIntegral_formula]
  have heq : (fun x => ENNReal.ofReal ‖f x‖) =
      (fun x => liminf (fun n => ENNReal.ofReal ‖F n x‖) atTop) := by
    funext x
    exact ((ENNReal.continuous_ofReal.tendsto _).comp (hlim x).norm).liminf_eq.symm
  rw [heq]
  refine (lintegral_liminf_le (fun n => (hF n).norm.ennreal_ofReal)).trans ?_
  apply liminf_le_of_frequently_le'
  apply Frequently.of_forall
  intro n
  rw [← absoluteIntegral_formula]
  exact le_iSup (fun n => absoluteIntegral μ (F n) A) n

/-- Pointwise convergence plus uniform spatial tails implies global convergence
in measure. Only finite truncations use the finite-space a.e. theorem. -/
theorem inMeasure_of_pointwise_spatial (μ : Measure X) (F : ℕ → X → 𝕜)
    (f : X → 𝕜) (ht : spatialTails μ F) (hf : Measurable f)
    (hlim : pointwiseConverges F f) : inMeasureConverges μ F f := by
  have hF : ∀ n, Measurable (F n) := fun n => (ht.1 n).1
  intro ε hε
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  by_cases hηtop : η = ∞
  · simp [hηtop]
  let δ : ℝ := η.toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hη.ne' hηtop
  let r : ℝ := ε * δ / 8
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨A, hA, hAfin, hb⟩ := ht.2 r hr
  have hfl : absoluteIntegral μ f Aᶜ ≤ integralSup μ F Aᶜ :=
    absoluteIntegral_limit_le μ F f hF hlim Aᶜ
  have hout (n : ℕ) :
      (μ.restrict Aᶜ) (deviationSet (F n) f ε) < ENNReal.ofReal (δ / 2) := by
    have hcheb := D11.Ch10.Chebyshev.chebyshev (μ.restrict Aᶜ)
      (F n - f) 1 ε ((hF n).sub hf) zero_lt_one hε
    change ENNReal.ofReal (ε ^ (1 : ℝ)) *
      (μ.restrict Aᶜ) (deviationSet (F n) f ε) ≤
      nonnegativeIntegral (μ.restrict Aᶜ)
        (fun x => ENNReal.ofReal (‖F n x - f x‖ ^ (1 : ℝ))) at hcheb
    simp only [Real.rpow_one, integral_eq_lintegral] at hcheb
    have hdiff : (∫⁻ x in Aᶜ, ENNReal.ofReal ‖F n x - f x‖ ∂μ) ≤
        integralSup μ F Aᶜ + integralSup μ F Aᶜ := by
      calc
        _ ≤ ∫⁻ x in Aᶜ, ENNReal.ofReal ‖F n x‖ + ENNReal.ofReal ‖f x‖ ∂μ := by
          apply lintegral_mono
          intro x
          dsimp only
          rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
        _ = absoluteIntegral μ (F n) Aᶜ + absoluteIntegral μ f Aᶜ := by
          rw [lintegral_add_left (hF n).norm.ennreal_ofReal]
          rw [absoluteIntegral_formula, absoluteIntegral_formula]
        _ ≤ _ := add_le_add (le_iSup (fun n => absoluteIntegral μ (F n) Aᶜ) n) hfl
    have hm : ENNReal.ofReal ε * (μ.restrict Aᶜ) (deviationSet (F n) f ε) <
        ENNReal.ofReal ε * ENNReal.ofReal (δ / 2) := by
      calc
        _ ≤ _ := hcheb
        _ ≤ _ := hdiff
        _ < ENNReal.ofReal r + ENNReal.ofReal r := ENNReal.add_lt_add hb hb
        _ ≤ _ := by
          rw [← ENNReal.ofReal_add hr.le hr.le, ← ENNReal.ofReal_mul hε.le]
          apply ENNReal.ofReal_le_ofReal
          dsimp [r]
          nlinarith [mul_pos hε hδ]
    exact lt_of_mul_lt_mul_left hm bot_le
  have hlocal := D11.Ch07.FiniteAeToMeasure.ae_to_measure_restrict
    μ F f A hA hAfin hF hf
    ((D11.Ch04.AeCommonException.almostEverywhere_iff_native μ _).mpr
      (Eventually.of_forall hlim))
  have hev := (hlocal ε hε).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hδ)))
  filter_upwards [hev] with n hn
  have hsplit : μ (deviationSet (F n) f ε) =
      (μ.restrict A) (deviationSet (F n) f ε) +
      (μ.restrict Aᶜ) (deviationSet (F n) f ε) := by
    rw [← Measure.add_apply, Measure.restrict_add_restrict_compl hA]
  rw [hsplit]
  apply le_of_lt
  calc
    _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
      ENNReal.add_lt_add hn (hout n)
    _ = η := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      have hsum : δ / 2 + δ / 2 = δ := by ring
      rw [hsum, ENNReal.ofReal_toReal hηtop]



/-- The p=1 power controls are exactly the original controls, since taking
another absolute value does not change the absolute integral. -/
theorem one_power_controls (μ : Measure X) (F : ℕ → X → 𝕜)
    (hs : uiSmall μ F) (ht : spatialTails μ F) :
    lpUiSmall μ 1 F ∧ lpSpatialTails μ 1 F := by
  have hfamily : lpFamily μ 1 F := by
    refine ⟨le_rfl, fun n => (rawLp_iff_finite_integral μ 1 (F n) le_rfl).mpr ?_⟩
    change Measurable (F n) ∧
      nonnegativeIntegral μ (fun x => ENNReal.ofReal (‖F n x‖ ^ (1 : ℝ))) < ∞
    exact ⟨(hs.1 n).1, by simpa only [Real.rpow_one] using (hs.1 n).2⟩
  have hnorms : integrableFamily μ (powerFamily 1 F) := by
    intro n
    change Measurable (fun x => ‖F n x‖ ^ (1 : ℝ)) ∧
      nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖‖F n x‖ ^ (1 : ℝ)‖) < ∞
    simp only [Real.rpow_one, norm_norm]
    exact ⟨(hs.1 n).1.norm, (hs.1 n).2⟩
  have hsup (A : Set X) : integralSup μ (powerFamily 1 F) A = integralSup μ F A := by
    simp only [integralSup, absoluteIntegral, powerFamily, Real.rpow_one, norm_norm]
  constructor
  · refine ⟨hfamily, hnorms, ?_⟩
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hs.2 ε hε
    exact ⟨δ, hδ, fun A hA hμA => (hsup A).trans_lt (hbound A hA hμA)⟩
  · refine ⟨hfamily, hnorms, ?_⟩
    intro ε hε
    obtain ⟨A, hA, hμA, hbound⟩ := ht.2 ε hε
    exact ⟨A, hA, hμA, (hsup Aᶜ).trans_lt hbound⟩

theorem pointwise_vitali_spatial :
    Specs.D11.Ch17.RoydenLebesgueVitali.pointwise_vitali_spatial.{u} := by
  intro X 𝕜 _ _ _ _ μ F f hs ht hf hlim
  change uiSmall μ F at hs
  change spatialTails μ F at ht
  have hcontrols := one_power_controls μ F hs ht
  have hmeasure := inMeasure_of_pointwise_spatial μ F f ht hf hlim
  have hconv := (D11.Ch17.VitaliLpConvergence.vitali_lp_convergence_on_representatives
    μ 1 le_rfl F f hcontrols.1.1.2 hf).mpr ⟨hmeasure, hcontrols.1, hcontrols.2⟩
  change lpConverges μ 1 F f at hconv
  have hfi : scalarIntegrable μ f := by
    simpa only [finitePowerIntegral, powerIntegral, Real.rpow_one, scalarIntegrable]
      using hconv.2.1
  refine ⟨hfi, hconv, ?_⟩
  change Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ))
  apply tendsto_integral_of_L1 f hf.aestronglyMeasurable
    (Eventually.of_forall (fun n => (scalarIntegrable_iff μ (F n)).mp (hs.1 n) |>.2))
  simpa only [powerIntegral_eq_lintegral, Real.rpow_one, ofReal_norm]
    using hconv.2.2.2

theorem pointwise_vitali_finite :
    Specs.D11.Ch17.RoydenLebesgueVitali.pointwise_vitali_finite.{u} := by
  intro X 𝕜 _ _ _ _ μ F f hs hμ hf hlim
  have ht : spatialTails μ F := by
    refine ⟨hs.1, fun ε hε => ⟨univ, MeasurableSet.univ, hμ, ?_⟩⟩
    simp only [compl_univ, integralSup, absoluteIntegral_formula, Measure.restrict_empty,
      lintegral_zero_measure, iSup_const]
    exact ENNReal.ofReal_pos.mpr hε
  exact pointwise_vitali_spatial μ F f hs ht hf hlim

theorem lebesgue_vitali_spatial :
    Specs.D11.Ch17.RoydenLebesgueVitali.lebesgue_vitali_spatial := by
  intro 𝕜 _ _ _ E _hE μ F f hs ht hf hlim
  exact pointwise_vitali_spatial _ F f hs ht hf hlim

theorem lebesgue_vitali_finite :
    Specs.D11.Ch17.RoydenLebesgueVitali.lebesgue_vitali_finite := by
  intro 𝕜 _ _ _ E hE hEfin μ F f hs hf hlim
  have hmass := (D11.Ch01.ExhaustionRestriction.restriction_mass
    (volume : Measure ℝ).completion E hE).2
  exact pointwise_vitali_finite _ F f hs (hmass.trans_lt hEfin) hf hlim

end D11.Ch17.RoydenLebesgueVitali
