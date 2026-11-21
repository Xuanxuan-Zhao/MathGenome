import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch06.DominationInvariance
import MathGenome.Internal.RealAnalysis.D11.Ch10.LpDefinition

open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace D11.Ch17.UniformControls
open D11.Ch05.NonnegativeIntegral D11.Ch06.ScalarIntegral D11.Ch10.LpDefinition

def absoluteIntegral : ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (X → 𝕜) → Set X → ℝ≥0∞ := fun μ f A =>
  nonnegativeIntegral (μ.restrict A)
    (fun x => ENNReal.ofReal ‖f x‖)

def integralSup : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Set X → ℝ≥0∞ := fun μ F A => ⨆ i, absoluteIntegral μ (F i) A

def amplitudeSup : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → ℝ → ℝ≥0∞ := fun μ F R =>
  ⨆ i, absoluteIntegral μ (F i) {x | R < ‖F i x‖}

def integrableFamily : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Prop := fun μ F =>
  ∀ i, scalarIntegrable μ (F i)

def uiSmall : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Prop := fun μ F =>
  integrableFamily μ F ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ A : Set _, MeasurableSet A → μ A < ENNReal.ofReal δ →
      integralSup μ F A < ENNReal.ofReal ε

def spatialTails : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Prop := fun μ F =>
  integrableFamily μ F ∧ ∀ ε : ℝ, 0 < ε →
    ∃ E : Set _, MeasurableSet E ∧ μ E < ∞ ∧
      integralSup μ F Eᶜ < ENNReal.ofReal ε

def uiTail : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Prop := fun μ F =>
  integrableFamily μ F ∧
    Tendsto (amplitudeSup μ F) atTop (𝓝 0)

def uniformL1Bound : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Prop := fun μ F =>
  integrableFamily μ F ∧ integralSup μ F univ < ∞

def powerFamily : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ℝ → (ι → X → 𝕜) → (ι → X → ℝ) := fun p F i x => ‖F i x‖ ^ p

def lpFamily : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ → (ι → X → 𝕜) → Prop := fun μ p F =>
  1 ≤ p ∧ ∀ i, F i ∈ rawLp μ p

def lpUiSmall : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ → (ι → X → 𝕜) → Prop := fun μ p F =>
  lpFamily μ p F ∧ uiSmall μ (powerFamily p F)

def lpSpatialTails : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ → (ι → X → 𝕜) → Prop := fun μ p F =>
  lpFamily μ p F ∧ spatialTails μ (powerFamily p F)

def lpUiTail : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ → (ι → X → 𝕜) → Prop := fun μ p F =>
  lpFamily μ p F ∧ uiTail μ (powerFamily p F)

def lpUniformL1Bound : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ → (ι → X → 𝕜) → Prop := fun μ p F =>
  lpFamily μ p F ∧ uniformL1Bound μ (powerFamily p F)

/-- The source integral over a set, without totalizing a scalar integral. -/
theorem absoluteIntegral_formula : ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜) (A : Set X),
  absoluteIntegral μ f A = ∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ := by
  intro X 𝕜 _ _ _ _ μ f A
  exact integral_eq_lintegral (μ.restrict A) _

theorem absoluteIntegral_eq_L1Norm : ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
  absoluteIntegral μ f univ = powerNorm μ 1 f := by
  intro X 𝕜 _ _ _ _ μ f
  simp only [absoluteIntegral, Measure.restrict_univ, powerNorm, Real.rpow_one,
    one_div_one, ENNReal.rpow_one]

theorem absoluteIntegral_congr_ae : ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f g : X → 𝕜) (A : Set X),
  f =ᵐ[μ] g → absoluteIntegral μ f A = absoluteIntegral μ g A := by
  intro X 𝕜 _ _ _ _ μ f g A hfg
  rw [absoluteIntegral_formula, absoluteIntegral_formula]
  exact lintegral_congr_ae ((ae_restrict_of_ae hfg).mono
    fun x hx => congrArg (fun z => ENNReal.ofReal ‖z‖) hx)

theorem integralSup_congr_ae : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F G : ι → X → 𝕜),
  (∀ i, F i =ᵐ[μ] G i) → ∀ A : Set X,
  integralSup μ F A = integralSup μ G A := by
  intro X ι 𝕜 _ _ _ _ μ F G hfg A
  change (⨆ i, absoluteIntegral μ (F i) A) = ⨆ i, absoluteIntegral μ (G i) A
  exact iSup_congr fun i => absoluteIntegral_congr_ae μ (F i) (G i) A (hfg i)

/-- Both the integrand and the large-value set change a.e. with a member.
No measurability of an arbitrary modification is inferred. -/
theorem amplitudeSup_congr_ae : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F G : ι → X → 𝕜),
  (∀ i, F i =ᵐ[μ] G i) → ∀ R : ℝ,
  amplitudeSup μ F R = amplitudeSup μ G R := by
  intro X ι 𝕜 _ _ _ _ μ F G hfg R
  change (⨆ i, absoluteIntegral μ (F i) {x | R < ‖F i x‖}) =
    ⨆ i, absoluteIntegral μ (G i) {x | R < ‖G i x‖}
  apply iSup_congr
  intro i
  calc
    absoluteIntegral μ (F i) {x | R < ‖F i x‖} =
        absoluteIntegral μ (G i) {x | R < ‖F i x‖} :=
      absoluteIntegral_congr_ae μ (F i) (G i) _ (hfg i)
    _ = absoluteIntegral μ (G i) {x | R < ‖G i x‖} := by
      unfold absoluteIntegral
      congr 1
      apply Measure.restrict_congr_set
      filter_upwards [hfg i] with x hx
      simp only [hx]

theorem integrableFamily_congr_ae : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F G : ι → X → 𝕜),
  (∀ i, Measurable (F i)) → (∀ i, Measurable (G i)) →
  (∀ i, F i =ᵐ[μ] G i) →
  (integrableFamily μ F ↔ integrableFamily μ G) := by
  intro X ι 𝕜 _ _ _ _ μ F G hF hG hfg
  change (∀ i, scalarIntegrable μ (F i)) ↔ ∀ i, scalarIntegrable μ (G i)
  apply forall_congr'
  intro i
  rw [native_integrable_iff μ (F i) (hF i), native_integrable_iff μ (G i) (hG i)]
  exact integrable_congr (hfg i)

theorem controls_congr_ae : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F G : ι → X → 𝕜),
  (∀ i, Measurable (F i)) → (∀ i, Measurable (G i)) →
  (∀ i, F i =ᵐ[μ] G i) →
  (uiSmall μ F ↔ uiSmall μ G) ∧
  (spatialTails μ F ↔ spatialTails μ G) ∧
  (uiTail μ F ↔ uiTail μ G) ∧
  (uniformL1Bound μ F ↔ uniformL1Bound μ G) := by
  intro X ι 𝕜 _ _ _ _ μ F G hF hG hfg
  have hi : integrableFamily μ F ↔ integrableFamily μ G :=
    integrableFamily_congr_ae μ F G hF hG hfg
  have hs : integralSup μ F = integralSup μ G :=
    funext (integralSup_congr_ae μ F G hfg)
  have ht : amplitudeSup μ F = amplitudeSup μ G :=
    funext (amplitudeSup_congr_ae μ F G hfg)
  simp only [uiSmall, spatialTails, uiTail, uniformL1Bound, hi, hs, ht, iff_self, and_self]

theorem powerFamily_measurable : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (_μ : Measure X) (p : ℝ) (F : ι → X → 𝕜),
  (∀ i, Measurable (F i)) → ∀ i, Measurable (powerFamily p F i) := by
  intro X ι 𝕜 _ _ _ _ _μ p F hF i
  exact (hF i).norm.pow_const p

theorem absoluteIntegral_powerFamily :
    Specs.D11.Ch17.UniformControls.absoluteIntegral_powerFamily := by
  intro X ι 𝕜 _ _ _ _ μ p F i A
  change nonnegativeIntegral (μ.restrict A) (fun x => ENNReal.ofReal ‖‖F i x‖ ^ p‖) = _
  congr 1
  funext x
  rw [Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm]

/-- Finite-p membership is the original measurable-representative condition,
with exactly the integrability of the pth-power density. -/
theorem lpFamily_iff : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (F : ι → X → 𝕜),
  lpFamily μ p F ↔
    1 ≤ p ∧ (∀ i, Measurable (F i)) ∧
      integrableFamily μ (powerFamily p F) := by
  intro X ι 𝕜 _ _ _ _ μ p F
  change (1 ≤ p ∧ ∀ i, F i ∈ rawLp μ p) ↔
    1 ≤ p ∧ (∀ i, Measurable (F i)) ∧ integrableFamily μ (powerFamily p F)
  constructor
  · rintro ⟨hp, hF⟩
    have hm : ∀ i, Measurable (F i) := fun i => (hF i).1
    refine ⟨hp, hm, fun i => ⟨powerFamily_measurable μ p F hm i, ?_⟩⟩
    have hi := ((rawLp_iff_finite_integral μ p (F i) hp).mp (hF i)).2
    change nonnegativeIntegral μ (fun x => ENNReal.ofReal (‖F i x‖ ^ p)) < ∞ at hi
    change nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖‖F i x‖ ^ p‖) < ∞
    simpa only [Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm] using hi
  · rintro ⟨hp, hm, hi⟩
    refine ⟨hp, fun i => (rawLp_iff_finite_integral μ p (F i) hp).mpr ⟨hm i, ?_⟩⟩
    change nonnegativeIntegral μ (fun x => ENNReal.ofReal (‖F i x‖ ^ p)) < ∞
    have h := (hi i).2
    change nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖‖F i x‖ ^ p‖) < ∞ at h
    simpa only [Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm] using h

theorem lpFamily_congr_ae : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (F G : ι → X → 𝕜),
  (∀ i, Measurable (F i)) → (∀ i, Measurable (G i)) →
  (∀ i, F i =ᵐ[μ] G i) → (lpFamily μ p F ↔ lpFamily μ p G) := by
  intro X ι 𝕜 _ _ _ _ μ p F G hF hG hfg
  have heq : ∀ i, powerFamily p F i =ᵐ[μ] powerFamily p G i := by
    intro i
    exact (hfg i).mono fun x hx => congrArg (fun z => ‖z‖ ^ p) hx
  rw [lpFamily_iff, lpFamily_iff]
  have hi : integrableFamily μ (powerFamily p F) ↔ integrableFamily μ (powerFamily p G) :=
    integrableFamily_congr_ae μ _ _ (powerFamily_measurable μ p F hF)
      (powerFamily_measurable μ p G hG) heq
  exact and_congr Iff.rfl (and_congr (iff_of_true hF hG) hi)

theorem lpControls_congr_ae : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (F G : ι → X → 𝕜),
  (∀ i, Measurable (F i)) → (∀ i, Measurable (G i)) →
  (∀ i, F i =ᵐ[μ] G i) →
  (lpUiSmall μ p F ↔ lpUiSmall μ p G) ∧
  (lpSpatialTails μ p F ↔ lpSpatialTails μ p G) ∧
  (lpUiTail μ p F ↔ lpUiTail μ p G) ∧
  (lpUniformL1Bound μ p F ↔ lpUniformL1Bound μ p G) := by
  intro X ι 𝕜 _ _ _ _ μ p F G hF hG hfg
  have hpow : ∀ i, powerFamily p F i =ᵐ[μ] powerFamily p G i := by
    intro i
    exact (hfg i).mono fun x hx => congrArg (fun z => ‖z‖ ^ p) hx
  have hc := controls_congr_ae μ (powerFamily p F) (powerFamily p G)
    (powerFamily_measurable μ p F hF) (powerFamily_measurable μ p G hG) hpow
  have hl : lpFamily μ p F ↔ lpFamily μ p G := lpFamily_congr_ae μ p F G hF hG hfg
  exact ⟨and_congr hl hc.1, and_congr hl hc.2.1,
    and_congr hl hc.2.2.1, and_congr hl hc.2.2.2⟩

theorem empty_suprema : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) [IsEmpty ι] (F : ι → X → 𝕜),
  (∀ A : Set X, integralSup μ F A = 0) ∧
  (∀ R : ℝ, amplitudeSup μ F R = 0) := by
  intro X ι 𝕜 _ _ _ _ μ _ F
  constructor
  · intro A
    change (⨆ i, absoluteIntegral μ (F i) A) = 0
    simp
  · intro R
    change (⨆ i, absoluteIntegral μ (F i) {x | R < ‖F i x‖}) = 0
    simp

theorem empty_controls : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) [IsEmpty ι] (F : ι → X → 𝕜),
  uiSmall μ F ∧ spatialTails μ F ∧ uiTail μ F ∧
    uniformL1Bound μ F := by
  intro X ι 𝕜 _ _ _ _ μ _ F
  have hi : integrableFamily μ F := fun i => isEmptyElim i
  obtain ⟨hs, ht⟩ := empty_suprema μ F
  refine ⟨⟨hi, ?_⟩, ⟨hi, ?_⟩, ⟨hi, ?_⟩, ⟨hi, ?_⟩⟩
  · intro ε hε
    refine ⟨1, zero_lt_one, fun A _ _ => ?_⟩
    rw [hs A]
    exact ENNReal.ofReal_pos.mpr hε
  · intro ε hε
    refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
    rw [hs]
    exact ENNReal.ofReal_pos.mpr hε
  · have hz : amplitudeSup μ F = fun _ => 0 := funext ht
    rw [hz]
    exact tendsto_const_nhds
  · rw [hs]
    exact ENNReal.zero_lt_top

theorem empty_lpControls : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) [IsEmpty ι] (p : ℝ) (F : ι → X → 𝕜), 1 ≤ p →
  lpUiSmall μ p F ∧ lpSpatialTails μ p F ∧
    lpUiTail μ p F ∧ lpUniformL1Bound μ p F
 := by
  intro X ι 𝕜 _ _ _ _ μ _ p F hp
  have hl : lpFamily μ p F := ⟨hp, fun i => isEmptyElim i⟩
  have hc := empty_controls μ (powerFamily p F)
  exact ⟨⟨hl, hc.1⟩, ⟨hl, hc.2.1⟩, ⟨hl, hc.2.2.1⟩, ⟨hl, hc.2.2.2⟩⟩

theorem uniformL1Bound_iff_normBound : ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ι → X → 𝕜),
  uniformL1Bound μ F ↔ integrableFamily μ F ∧
    (⨆ i, powerNorm μ 1 (F i)) < ∞ := by
  intro X ι 𝕜 _ _ _ _ μ F
  have h : integralSup μ F univ = ⨆ i, powerNorm μ 1 (F i) :=
    iSup_congr fun i => absoluteIntegral_eq_L1Norm μ (F i)
  simp only [uniformL1Bound, h]

end D11.Ch17.UniformControls
