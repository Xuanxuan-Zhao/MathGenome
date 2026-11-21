import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.VitaliLpCauchy
import MathGenome.Internal.RealAnalysis.D11.Ch17.NormConvergenceControls
import MathGenome.Internal.RealAnalysis.D11.Ch10.Completeness
import MathGenome.Internal.RealAnalysis.D11.Ch10.Chebyshev
import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions

open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u
noncomputable section
namespace D11.Ch17.VitaliLpCauchy
open D11.Ch17.UniformControls D11.Ch17.NormConvergenceControls
open D11.Ch07.ConvergenceDefinitions

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The representative power integral is the pth power of quotient distance. -/
theorem difference_integral_eq_dist_rpow (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (a b : Lp 𝕜 (ENNReal.ofReal p) μ) (f g : X → 𝕜)
    (hf : Measurable f) (hg : Measurable g)
    (hfa : f =ᵐ[μ] a) (hgb : g =ᵐ[μ] b) :
    (∫⁻ x, ENNReal.ofReal (‖f x - g x‖ ^ p) ∂μ) =
      ENNReal.ofReal (dist a b) ^ p := by
  have heq := power_integral_eq μ p hp (f - g) (hf.sub hg) univ
  rw [absoluteIntegral_formula] at heq
  simp only [Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm,
    Measure.restrict_univ, Pi.sub_apply] at heq
  rw [heq, eLpNorm_congr_ae (hfa.sub hgb), ← Lp.edist_def, Lp.edist_dist]

/-- For p ≥ 1, Cauchyness is equivalently uniform smallness of the pth-power
integrals of all sufficiently late pairwise differences. -/
theorem cauchySeq_iff_power_integrals (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (F : ℕ → Lp 𝕜 (ENNReal.ofReal p) μ) (G : ℕ → X → 𝕜)
    (hG : ∀ n, Measurable (G n)) (hGF : ∀ n, G n =ᵐ[μ] F n) :
    CauchySeq F ↔ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, ∀ m ≥ N,
        (∫⁻ x, ENNReal.ofReal (‖G n x - G m x‖ ^ p) ∂μ) < ENNReal.ofReal ε := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  simp_rw [difference_integral_eq_dist_rpow μ p hp _ _ _ _ (hG _) (hG _) (hGF _) (hGF _)]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp h (min ε 1) (lt_min hε zero_lt_one)
    refine ⟨N, fun n hn m hm => ?_⟩
    have hd := hN n hn m hm
    have hd1 : ENNReal.ofReal (dist (F n) (F m)) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((lt_of_lt_of_le hd (min_le_right _ _)).le)
    exact (ENNReal.rpow_le_self_of_le_one hd1 hp).trans_lt
      (ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (lt_of_lt_of_le hd (min_le_left _ _)))
  · intro h
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε ^ p) (Real.rpow_pos_of_pos hε _)
    refine ⟨N, fun n hn m hm => ?_⟩
    have ht := hN n hn m hm
    rw [← ENNReal.ofReal_rpow_of_nonneg hε.le hp0.le] at ht
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp ((ENNReal.rpow_lt_rpow_iff hp0).mp ht)

/-- The power inequality integrated on any set, without a finite-measure
assumption on that set. -/
theorem difference_integral_le (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    (f g : X → 𝕜) (hf : Measurable f) (A : Set X) :
    (∫⁻ x in A, ENNReal.ofReal (‖f x - g x‖ ^ p) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (p - 1)) *
        (absoluteIntegral μ (fun x => ‖f x‖ ^ p) A +
         absoluteIntegral μ (fun x => ‖g x‖ ^ p) A) := by
  simp only [absoluteIntegral_formula,
    Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm]
  calc
    _ ≤ ∫⁻ x in A, ENNReal.ofReal ((2 : ℝ) ^ (p - 1)) *
        (ENNReal.ofReal (‖f x‖ ^ p) + ENNReal.ofReal (‖g x‖ ^ p)) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_add (Real.rpow_nonneg (norm_nonneg _) _)
          (Real.rpow_nonneg (norm_nonneg _) _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [sub_neg_eq_add, sub_add_cancel, norm_neg] using
        norm_rpow_le p hp (f x - g x) (-g x)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left (hf.norm.pow_const p).ennreal_ofReal]

/-- Chebyshev gives global Cauchyness in measure from the power-integral
Cauchy condition. The measure here is never restricted to a finite set. -/
theorem cauchyInMeasure_of_power_integrals (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    (G : ℕ → X → 𝕜) (hG : ∀ n, Measurable (G n))
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ x, ENNReal.ofReal (‖G n x - G m x‖ ^ p) ∂μ) < ENNReal.ofReal ε) :
    cauchyInMeasure μ G := by
  intro η hη δ hδ
  obtain ⟨N, hN⟩ := h ((η ^ p) * δ) (mul_pos (Real.rpow_pos_of_pos hη _) hδ)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hcheb := D11.Ch10.Chebyshev.chebyshev μ (G n - G m) p η
    ((hG n).sub (hG m)) (lt_of_lt_of_le zero_lt_one hp) hη
  change ENNReal.ofReal (η ^ p) * μ {x | η < ‖G n x - G m x‖} ≤
    D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ
      (fun x => ENNReal.ofReal (‖G n x - G m x‖ ^ p)) at hcheb
  rw [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral] at hcheb
  have ht := hcheb.trans_lt (hN n hn m hm)
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hη.le _)] at ht
  exact lt_of_mul_lt_mul_left ht (bot_le : (0 : ℝ≥0∞) ≤ _)

/-- On a finite-measure set there is a positive threshold whose constant
power integral is small. Using M+1 also covers zero-mass sets. -/
theorem exists_small_threshold (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    (E : Set X) (hE : μ E < ∞) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal (η ^ p) * μ E ≤ ENNReal.ofReal (ε / 4) := by
  let M : ℝ := (μ E).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hden : 0 < 4 * (M + 1) := by positivity
  let η : ℝ := min 1 (ε / (4 * (M + 1)))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε hden)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηq : η ≤ ε / (4 * (M + 1)) := min_le_right _ _
  have hb : η * (4 * (M + 1)) ≤ ε := (le_div_iff₀ hden).mp hηq
  have hpow : η ^ p ≤ η := Real.rpow_le_self_of_le_one hη.le hη1 hp
  refine ⟨η, hη, ?_⟩
  rw [← ENNReal.ofReal_toReal hE.ne,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hη.le _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    η ^ p * M ≤ η * M := mul_le_mul_of_nonneg_right hpow hM
    _ ≤ ε / 4 := by nlinarith

/-- The three-region estimate proves uniform smallness of all late difference
power integrals. All sets used for small-set control are ordinarily measurable. -/
theorem power_integrals_of_controls (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    (G : ℕ → X → 𝕜) (hG : ∀ n, Measurable (G n))
    (hmeasure : cauchyInMeasure μ G)
    (hsmall : uiSmall μ (powerFamily p G))
    (htails : spatialTails μ (powerFamily p G)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫⁻ x, ENNReal.ofReal (‖G n x - G m x‖ ^ p) ∂μ) < ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := (2 : ℝ) ^ (p - 1)
  have hC : 0 < C := Real.rpow_pos_of_pos (by norm_num) _
  let a : ℝ := ε / (8 * C)
  have ha : 0 < a := div_pos hε (by positivity)
  obtain ⟨E, hE, hEmass, hEtail⟩ := htails.2 a ha
  obtain ⟨δ, hδ, hδsmall⟩ := hsmall.2 a ha
  obtain ⟨η, hη, hηmass⟩ := exists_small_threshold μ p hp E hEmass ε hε
  obtain ⟨N, hN⟩ := hmeasure η hη δ hδ
  have hbudget : ENNReal.ofReal C * (ENNReal.ofReal a + ENNReal.ofReal a) =
      ENNReal.ofReal (ε / 4) := by
    rw [← ENNReal.ofReal_add ha.le ha.le, ← ENNReal.ofReal_mul hC.le]
    congr 1
    dsimp [a]
    field_simp
    ring
  refine ⟨N, fun n hn m hm => ?_⟩
  let q : X → ℝ≥0∞ := fun x => ENNReal.ofReal (‖G n x - G m x‖ ^ p)
  let A : Set X := E ∩ deviationSet (G n) (G m) η
  have hA : MeasurableSet A := hE.inter (measurable_deviationSet _ _ _ (hG n) (hG m))
  have hAmass : μ A < ENNReal.ofReal δ :=
    (measure_mono inter_subset_right).trans_lt (hN m hm n hn)
  have hApart : integralSup μ (powerFamily p G) A < ENNReal.ofReal a :=
    hδsmall A hA hAmass
  have hpiece (B : Set X)
      (hB : integralSup μ (powerFamily p G) B < ENNReal.ofReal a) :
      (∫⁻ x in B, q x ∂μ) ≤ ENNReal.ofReal (ε / 4) := by
    calc
      _ ≤ ENNReal.ofReal C *
          (absoluteIntegral μ (powerFamily p G n) B +
           absoluteIntegral μ (powerFamily p G m) B) :=
        difference_integral_le μ p hp (G n) (G m) (hG n) B
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal a + ENNReal.ofReal a) := by
        apply mul_le_mul_right
        exact add_le_add ((le_iSup (fun i => absoluteIntegral μ (powerFamily p G i) B) n).trans hB.le)
          ((le_iSup (fun i => absoluteIntegral μ (powerFamily p G i) B) m).trans hB.le)
      _ = _ := hbudget
  have hgood : (∫⁻ x in E \ A, q x ∂μ) ≤ ENNReal.ofReal (ε / 4) := by
    calc
      _ ≤ ∫⁻ _ in E \ A, ENNReal.ofReal (η ^ p) ∂μ := by
        apply setLIntegral_mono' (hE.diff hA)
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        have hnorm : ‖G n x - G m x‖ ≤ η := by
          by_contra h
          exact hx.2 ⟨hx.1, lt_of_not_ge h⟩
        exact Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith)
      _ = ENNReal.ofReal (η ^ p) * μ (E \ A) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (η ^ p) * μ E := mul_le_mul_right (measure_mono sdiff_subset) _
      _ ≤ _ := hηmass
  have hsplit : (∫⁻ x, q x ∂μ) =
      ((∫⁻ x in A, q x ∂μ) + ∫⁻ x in E \ A, q x ∂μ) + ∫⁻ x in Eᶜ, q x ∂μ := by
    rw [← lintegral_add_compl q hE, ← lintegral_inter_add_sdiff q E hA,
      inter_eq_right.mpr (inter_subset_left : A ⊆ E)]
  calc
    _ = _ := hsplit
    _ ≤ (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) + ENNReal.ofReal (ε / 4) :=
      add_le_add (add_le_add (hpiece A hApart) hgood) (hpiece Eᶜ hEtail)
    _ < ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

/-- The complete global finite-p Cauchy criterion, for every ordinary
measurable choice of representatives. -/
theorem vitali_lp_cauchy : Specs.D11.Ch17.VitaliLpCauchy.vitali_lp_cauchy.{u} := by
  intro X 𝕜 _ _ _ _ μ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  intro F G hG hGF
  constructor
  · intro hc
    obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hc
    have hcontrols := lp_norm_convergence_controls μ p hp F f G hG hGF hf
    refine ⟨?_, hcontrols.1, hcontrols.2.1⟩
    exact cauchyInMeasure_of_power_integrals μ p hp G hG
      ((cauchySeq_iff_power_integrals μ p hp F G hG hGF).mp hc)
  · rintro ⟨hmeasure, hsmall, htail⟩
    exact (cauchySeq_iff_power_integrals μ p hp F G hG hGF).mpr
      (power_integrals_of_controls μ p hp G hG hmeasure hsmall.2 htail.2)

end D11.Ch17.VitaliLpCauchy
