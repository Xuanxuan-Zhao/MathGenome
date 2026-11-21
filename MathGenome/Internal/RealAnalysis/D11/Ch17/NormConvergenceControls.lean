import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.NormConvergenceControls
import MathGenome.Internal.RealAnalysis.D11.Ch17.DominatedAndFiniteFamilies
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Bounded

open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u
noncomputable section
namespace D11.Ch17.NormConvergenceControls
open D11.Ch17.UniformControls D11.Ch17.DominatedAndFiniteFamilies
open D11.Ch06.ScalarIntegral D11.Ch10.LpDefinition

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Finite families approximate all set integrals up to an arbitrarily small
uniform additive error. This gives both controls, and a separate norm bound. -/
theorem controls_of_finite_approximation (μ : Measure X) (F : ℕ → X → 𝕜)
    (hF : integrableFamily μ F)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ B : Option (Fin N) → X → 𝕜,
      integrableFamily μ B ∧ ∀ n A, absoluteIntegral μ (F n) A ≤
        ENNReal.ofReal ε + integralSup μ B A) :
    uiSmall μ F ∧ spatialTails μ F ∧ uniformL1Bound μ F := by
  constructor
  · refine ⟨hF, ?_⟩
    intro ε hε
    obtain ⟨N, B, hB, happrox⟩ := happrox (ε / 3) (by positivity)
    obtain ⟨δ, hδ, hsmall⟩ := (finite_controls μ B hB).1.2 (ε / 3) (by positivity)
    refine ⟨δ, hδ, fun A hA hmass => ?_⟩
    have hle : integralSup μ F A ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
      iSup_le fun n => (happrox n A).trans (add_le_add le_rfl (hsmall A hA hmass).le)
    refine hle.trans_lt ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (by linarith)
  constructor
  · refine ⟨hF, ?_⟩
    intro ε hε
    obtain ⟨N, B, hB, happrox⟩ := happrox (ε / 3) (by positivity)
    obtain ⟨E, hE, hmass, htail⟩ :=
      (finite_controls μ B hB).2.2 (ε / 3) (by positivity)
    refine ⟨E, hE, hmass, ?_⟩
    have hle : integralSup μ F Eᶜ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
      iSup_le fun n => (happrox n Eᶜ).trans (add_le_add le_rfl htail.le)
    refine hle.trans_lt ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (by linarith)
  · refine ⟨hF, ?_⟩
    obtain ⟨N, B, hB, happrox⟩ := happrox 1 zero_lt_one
    have hfin : integralSup μ B univ < ∞ := by
      apply lt_top_iff_ne_top.mpr
      apply iSup_ne_top
      intro i
      rw [absoluteIntegral_eq_L1Norm]
      simpa only [powerNorm, Real.rpow_one, one_div_one, ENNReal.rpow_one] using (hB i).2.ne
    exact (iSup_le fun n => happrox n univ).trans_lt
      (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hfin⟩)

/-- The pth-power integral is the pth power of the extended Lp norm. -/
theorem power_integral_eq (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    (f : X → 𝕜) (hf : Measurable f) (A : Set X) :
    absoluteIntegral μ (fun x => ‖f x‖ ^ p) A =
      eLpNorm f (ENNReal.ofReal p) (μ.restrict A) ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [absoluteIntegral_formula]
  simp only [Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm]
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hp0)
    ENNReal.ofReal_ne_top hf.stronglyMeasurable.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  simp

/-- Scalar multiplication of an absolute set integral. -/
theorem absoluteIntegral_const_mul (μ : Measure X) (c : ℝ) (f : X → ℝ) (A : Set X) :
    absoluteIntegral μ (fun x => c * f x) A =
      ENNReal.ofReal |c| * absoluteIntegral μ f A := by
  simp only [absoluteIntegral_formula, norm_mul, Real.norm_eq_abs,
    ENNReal.ofReal_mul (abs_nonneg c)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The elementary real power estimate, valid also for complex scalars. -/
theorem norm_rpow_le (p : ℝ) (hp : 1 ≤ p) (a b : 𝕜) :
    ‖a‖ ^ p ≤ (2 : ℝ) ^ (p - 1) * (‖a - b‖ ^ p + ‖b‖ ^ p) := by
  calc
    ‖a‖ ^ p ≤ (‖a - b‖ + ‖b‖) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) (by simpa only [add_comm] using norm_le_norm_add_norm_sub' a b) (by linarith)
    _ ≤ _ := by
      exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ‖a - b‖₊ ‖b‖₊ hp

/-- The triangle inequality for absolute set integrals. -/
theorem absoluteIntegral_add_le (μ : Measure X) (f g : X → 𝕜)
    (hf : Measurable f) (A : Set X) :
    absoluteIntegral μ (fun x => f x + g x) A ≤
      absoluteIntegral μ f A + absoluteIntegral μ g A := by
  rw [absoluteIntegral_formula, absoluteIntegral_formula, absoluteIntegral_formula]
  calc
    _ ≤ ∫⁻ x in A, ENNReal.ofReal ‖f x‖ + ENNReal.ofReal ‖g x‖ ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = _ := lintegral_add_left hf.norm.ennreal_ofReal _

/-- A set integral is at most the full-space integral. -/
theorem absoluteIntegral_le_univ (μ : Measure X) (f : X → 𝕜) (A : Set X) :
    absoluteIntegral μ f A ≤ absoluteIntegral μ f univ := by
  rw [absoluteIntegral_formula, absoluteIntegral_formula, Measure.restrict_univ]
  exact lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)

/-- The power density of a measurable Lp member is an ordinary integrable
function, on the original sigma-algebra. -/
theorem scalarIntegrable_power (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    (f : X → 𝕜) (hf : f ∈ rawLp μ p) :
    scalarIntegrable μ (fun x => ‖f x‖ ^ p) := by
  have hfam : lpFamily μ p (fun _ : Unit => f) := ⟨hp, fun _ => hf⟩
  exact (lpFamily_iff μ p (fun _ : Unit => f)).mp hfam |>.2.2 ()

/-- Norm convergence supplies finite approximations to every restricted power
integral. The approximating family contains the finite prefix and one scaled
power density of the limit. -/
theorem power_controls_of_tendsto_eLpNorm (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    (F : ℕ → X → 𝕜) (f : X → 𝕜)
    (hF : ∀ n, F n ∈ rawLp μ p) (hf : f ∈ rawLp μ p)
    (hlim : Tendsto (fun n => eLpNorm (F n - f) (ENNReal.ofReal p) μ)
      atTop (𝓝 0)) :
    uiSmall μ (powerFamily p F) ∧ spatialTails μ (powerFamily p F) ∧
      uniformL1Bound μ (powerFamily p F) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let C : ℝ := (2 : ℝ) ^ (p - 1)
  have hC : 0 < C := Real.rpow_pos_of_pos (by norm_num) _
  let D : ℕ → X → ℝ := fun n x => C * ‖F n x - f x‖ ^ p
  let b : X → ℝ := fun x => C * ‖f x‖ ^ p
  have hb : scalarIntegrable μ b := by
    have hi := (scalarIntegrable_iff μ _).mp (scalarIntegrable_power μ p hp f hf)
    exact (scalarIntegrable_iff μ b).mpr
      ⟨measurable_const.mul hi.1, hi.2.const_mul C⟩
  have hDm : ∀ n, Measurable (D n) := fun n =>
    measurable_const.mul (((hF n).1.sub hf.1).norm.pow_const p)
  have hDformula : ∀ n, absoluteIntegral μ (D n) univ =
      ENNReal.ofReal C * eLpNorm (F n - f) (ENNReal.ofReal p) μ ^ p := by
    intro n
    rw [absoluteIntegral_const_mul, abs_of_pos hC]
    congr 1
    simpa only [Pi.sub_apply, Measure.restrict_univ] using
      power_integral_eq μ p hp (F n - f) ((hF n).1.sub hf.1) univ
  have hDlim : Tendsto (fun n => absoluteIntegral μ (D n) univ) atTop (𝓝 0) := by
    simp_rw [hDformula]
    have h := ENNReal.Tendsto.const_mul (hlim.ennrpow_const p)
      (a := ENNReal.ofReal C) (Or.inr ENNReal.ofReal_ne_top)
    simpa only [ENNReal.zero_rpow_of_pos hp0, mul_zero] using h
  apply controls_of_finite_approximation
  · exact fun n => scalarIntegrable_power μ p hp (F n) (hF n)
  · intro ε hε
    obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hDlim
      (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
    let B : Option (Fin N) → X → ℝ := fun i =>
      match i with
      | none => b
      | some i => powerFamily p F i
    have hB : integrableFamily μ B := by
      intro i
      cases i with
      | none => exact hb
      | some i => exact scalarIntegrable_power μ p hp (F i) (hF i)
    refine ⟨N, B, hB, fun n A => ?_⟩
    by_cases hn : n < N
    · have hle : absoluteIntegral μ (powerFamily p F n) A ≤ integralSup μ B A :=
        le_iSup (fun i => absoluteIntegral μ (B i) A) (some ⟨n, hn⟩)
      exact hle.trans (le_add_left le_rfl)
    · have hpoint : ∀ᵐ x ∂μ, ‖powerFamily p F n x‖ ≤ D n x + b x := by
        apply Eventually.of_forall
        intro x
        change ‖‖F n x‖ ^ p‖ ≤ C * ‖F n x - f x‖ ^ p + C * ‖f x‖ ^ p
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← mul_add]
        exact norm_rpow_le p hp _ _
      calc
        absoluteIntegral μ (powerFamily p F n) A ≤
            absoluteIntegral μ (fun x => D n x + b x) A :=
          absoluteIntegral_le_of_ae_norm_le μ _ _ A hpoint
        _ ≤ absoluteIntegral μ (D n) A + absoluteIntegral μ b A :=
          absoluteIntegral_add_le μ _ _ (hDm n) A
        _ ≤ ENNReal.ofReal ε + integralSup μ B A :=
          add_le_add ((absoluteIntegral_le_univ μ (D n) A).trans (hN n (by omega)))
            (le_iSup (fun i => absoluteIntegral μ (B i) A) none)

/-- The general finite-p assertion, using the genuine ordinary-a.e. quotient
norm. The representatives may be chosen independently for every member. -/
theorem lp_norm_convergence_controls :
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (hp : 1 ≤ p),
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    ∀ (F : ℕ → Lp 𝕜 (ENNReal.ofReal p) μ) (f : Lp 𝕜 (ENNReal.ofReal p) μ)
      (G : ℕ → X → 𝕜),
      (∀ n, Measurable (G n)) → (∀ n, G n =ᵐ[μ] (F n)) →
      Tendsto F atTop (𝓝 f) →
      lpUiSmall μ p G ∧ lpSpatialTails μ p G ∧
        lpUniformL1Bound μ p G ∧ ∃ C : ℝ, ∀ n, ‖F n‖ ≤ C := by
  intro X 𝕜 _ _ _ _ μ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  intro F f G hG hGF hconv
  have hraw : ∀ n, G n ∈ rawLp μ p := by
    intro n
    exact (rawLp_iff_memLp μ p (G n) hp).mpr
      ⟨hG n, (memLp_congr_ae (hGF n)).mpr (Lp.memLp (F n))⟩
  have hf : (fun x => f x) ∈ rawLp μ p := by
    exact (rawLp_iff_memLp μ p _ hp).mpr
      ⟨(Lp.stronglyMeasurable f).measurable, Lp.memLp f⟩
  have hlim : Tendsto (fun n => eLpNorm (G n - ⇑f) (ENNReal.ofReal p) μ)
      atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm (G n - ⇑f) (ENNReal.ofReal p) μ) =
        (fun n => eLpNorm (⇑(F n) - ⇑f) (ENNReal.ofReal p) μ) := by
      funext n
      exact eLpNorm_congr_ae ((hGF n).sub EventuallyEq.rfl)
    rw [heq]
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F f).mp hconv
  have hc := power_controls_of_tendsto_eLpNorm μ p hp G (fun x => f x) hraw hf hlim
  have hl : lpFamily μ p G := ⟨hp, hraw⟩
  refine ⟨⟨hl, hc.1⟩, ⟨hl, hc.2.1⟩, ⟨hl, hc.2.2⟩, ?_⟩
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto F hconv).exists_norm_le
  exact ⟨C, fun n => hC (F n) (mem_range_self n)⟩

/-- Absolute-value densities have exactly the same absolute set integrals. -/
theorem absoluteIntegral_norm (μ : Measure X) (f : X → 𝕜) (A : Set X) :
    absoluteIntegral μ (fun x => ‖f x‖) A = absoluteIntegral μ f A := by
  simp only [absoluteIntegral_formula, norm_norm]

/-- The endpoint one, stated for the scalar representatives themselves. -/
theorem l1_norm_convergence_controls :
    Specs.D11.Ch17.NormConvergenceControls.l1_norm_convergence_controls.{u} := by
  intro X 𝕜 _ _ _ _ μ F f G hG hGF hconv
  have hraw : ∀ n, G n ∈ rawLp μ 1 := by
    intro n
    apply (rawLp_iff_memLp μ 1 (G n) le_rfl).mpr
    refine ⟨hG n, ?_⟩
    simpa only [ENNReal.ofReal_one] using
      (memLp_congr_ae (hGF n)).mpr (Lp.memLp (F n))
  have hf : (fun x => f x) ∈ rawLp μ 1 := by
    apply (rawLp_iff_memLp μ 1 _ le_rfl).mpr
    refine ⟨(Lp.stronglyMeasurable f).measurable, ?_⟩
    simpa only [ENNReal.ofReal_one] using Lp.memLp f
  have hlim : Tendsto (fun n => eLpNorm (G n - ⇑f) (ENNReal.ofReal 1) μ)
      atTop (𝓝 0) := by
    simp only [ENNReal.ofReal_one]
    have heq : (fun n => eLpNorm (G n - ⇑f) 1 μ) =
        (fun n => eLpNorm (⇑(F n) - ⇑f) 1 μ) := by
      funext n
      exact eLpNorm_congr_ae ((hGF n).sub EventuallyEq.rfl)
    rw [heq]
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F f).mp hconv
  have hc := power_controls_of_tendsto_eLpNorm μ 1 le_rfl G (fun x => f x) hraw hf hlim
  have hnorm : integralSup μ (powerFamily 1 G) = integralSup μ G := by
    funext A
    apply iSup_congr
    intro n
    change absoluteIntegral μ (fun x => ‖G n x‖ ^ (1 : ℝ)) A = absoluteIntegral μ (G n) A
    simp only [Real.rpow_one]
    exact absoluteIntegral_norm μ (G n) A
  have hi : integrableFamily μ G := by
    intro n
    apply (scalarIntegrable_iff μ (G n)).mpr
    refine ⟨hG n, memLp_one_iff_integrable.mp ?_⟩
    have h := (rawLp_iff_memLp μ 1 (G n) le_rfl).mp (hraw n)
    simpa using h.2
  refine ⟨⟨hi, ?_⟩, ⟨hi, ?_⟩, ⟨hi, ?_⟩, ?_⟩
  · have h := hc.1.2
    change ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ A : Set X, MeasurableSet A → μ A < ENNReal.ofReal δ →
        integralSup μ G A < ENNReal.ofReal ε
    simpa only [← hnorm] using h
  · have h := hc.2.1.2
    change ∀ ε : ℝ, 0 < ε → ∃ E : Set X, MeasurableSet E ∧ μ E < ∞ ∧
      integralSup μ G Eᶜ < ENNReal.ofReal ε
    simpa only [← hnorm] using h
  · have h := hc.2.2.2
    change integralSup μ G univ < ∞
    simpa only [← hnorm] using h

  · obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto F hconv).exists_norm_le
    exact ⟨C, fun n => hC (F n) (mem_range_self n)⟩

end D11.Ch17.NormConvergenceControls
