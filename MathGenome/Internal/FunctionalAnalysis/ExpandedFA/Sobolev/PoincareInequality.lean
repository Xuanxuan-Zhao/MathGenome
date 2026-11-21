import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.WeakDerivativeSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.PoincareInequality
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal

namespace ExpandedFA.Sobolev
open ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Evaluating any derivative component is continuous in the original sum norm. -/
theorem continuous_sobolev_component (α : DerivativeIndex d 1) :
    Continuous (fun u : SobolevSpace 𝕜 d Ω 1 p => u.val α) :=
  (PiLp.continuous_apply 1 _ α).comp continuous_subtype_val

/-- An estimate with a fixed constant passes from tests to their full-norm closure. -/
theorem poincare_of_test_estimate (hp : p ≠ ∞) (i : Fin d) (C : ℝ)
    (h : ∀ φ : Tests 𝕜 Ω,
      ‖(testToSobolev (p := p) 1 φ).val (zeroIndex d 1)‖ ≤
        C * ‖(testToSobolev (p := p) 1 φ).val (coordinateIndex i)‖)
    (u : SobolevZero 𝕜 d Ω 1 p hp) :
    ‖u.val.val (zeroIndex d 1)‖ ≤ C * ‖u.val.val (coordinateIndex i)‖ := by
  have hc : IsClosed {v : SobolevSpace 𝕜 d Ω 1 p |
      ‖v.val (zeroIndex d 1)‖ ≤ C * ‖v.val (coordinateIndex i)‖} :=
    isClosed_le (continuous_sobolev_component _).norm
      (continuous_const.mul (continuous_sobolev_component _).norm)
  apply closure_minimal (t := {v : SobolevSpace 𝕜 d Ω 1 p |
      ‖v.val (zeroIndex d 1)‖ ≤ C * ‖v.val (coordinateIndex i)‖}) ?_ hc
      (show u.val ∈ closure
        (Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SmoothMembers 𝕜 d Ω 1 p) from
          u.property)
  rintro v ⟨φ, hφ⟩
  have he : v = testToSobolev (p := p) 1 φ := by
    apply sobolev_underlying_injective 𝕜 d Ω 1 p
    change v.val (zeroIndex d 1) = (testToSobolev (p := p) 1 φ).val (zeroIndex d 1)
    rw [testToSobolev_underlying]
    exact Lp.ext (hφ.trans (testToDomainLp_coe φ).symm)
  change ‖v.val (zeroIndex d 1)‖ ≤ C * ‖v.val (coordinateIndex i)‖
  rw [he]
  exact h φ

theorem poincare_empty : Specs.ExpandedFA.Sobolev.PoincareInequality.EmptyDomain := by
  intro 𝕜 _ d Ω hΩ p _ hp u
  have hm : volume.restrict (Ω : Set (Domain d)) = 0 := by simp [hΩ]
  have hz (f : Domain d → 𝕜) : eLpNorm f p (volume.restrict (Ω : Set (Domain d))) = 0 := by
    rw [hm]
    simp
  rw [Lp.norm_def, hz]
  rfl

/-- The vector gradient belongs to Lp because it has finitely many Lp coordinates. -/
theorem gradientFunction_memLp (u : SobolevSpace 𝕜 d Ω 1 p) :
    MemLp (gradientFunction u) p (volume.restrict (Ω : Set (Domain d))) :=
  MemLp.of_eval_piLp (fun i => Lp.memLp (u.val (coordinateIndex i)))

theorem coordinate_norm_le_gradient (u : SobolevSpace 𝕜 d Ω 1 p) (i : Fin d) :
    ‖u.val (coordinateIndex i)‖ ≤ gradientLpNorm u := by
  apply ENNReal.toReal_mono (gradientFunction_memLp u).eLpNorm_ne_top
  exact eLpNorm_mono (Lp.aestronglyMeasurable _) (fun x => PiLp.norm_apply_le (gradientFunction u x) i)

/-- The fundamental theorem on a coordinate line, followed by finite-measure
Hölder, gives Poincaré on a fixed enclosing interval. -/
theorem eLpNorm_le_length_mul_deriv {f : ℝ → 𝕜} {a b : ℝ}
    (hab : a < b) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfs : Function.support f ⊆ Icc a b) (_hp : p ≠ ∞) :
    eLpNorm f p volume ≤ ENNReal.ofReal (b - a) * eLpNorm (deriv f) p volume := by
  let ν := volume.restrict (Icc a b)
  have hfmeas := hf.continuous.aestronglyMeasurable (μ := volume)
  have hgmeas := (hf.continuous_deriv le_rfl).aestronglyMeasurable (μ := volume)
  have hgs : Function.support (deriv f) ⊆ Icc a b :=
    support_deriv_subset.trans (closure_minimal hfs isClosed_Icc)
  have h1 : eLpNorm (deriv f) 1 ν ≤
      eLpNorm (deriv f) p ν * (ν univ) ^ (1 - 1 / p.toReal) := by
    simpa only [ENNReal.toReal_one, div_one] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (show (1 : ℝ≥0∞) ≤ p from Fact.out) hgmeas.restrict
  have hpoint (x : ℝ) : ‖f x‖ₑ ≤
      eLpNorm (deriv f) p ν * (ν univ) ^ (1 - 1 / p.toReal) := by
    apply le_trans (b := eLpNorm (deriv f) 1 ν) ?_ h1
    rw [eLpNorm_restrict_eq_of_support_subset hgmeas hgs]
    exact (hfc.enorm_le_lintegral_Ici_deriv hf x).trans
      ((lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans
        lintegral_enorm_le_eLpNorm_one)
  have hbound := eLpNorm_le_of_ae_enorm_bound (p := p) hfmeas.restrict
    (Eventually.of_forall hpoint : ∀ᵐ x ∂ν, ‖f x‖ₑ ≤
      eLpNorm (deriv f) p ν * (ν univ) ^ (1 - 1 / p.toReal))
  change eLpNorm f p ν ≤
    (eLpNorm (deriv f) p ν * (ν univ) ^ (1 - 1 / p.toReal)) * (ν univ) ^ p.toReal⁻¹
    at hbound
  rw [eLpNorm_restrict_eq_of_support_subset hfmeas hfs,
    mul_assoc, ← ENNReal.rpow_add _ _
      (by simp [ν, Real.volume_Icc, hab]) (by simp [ν])] at hbound
  have hexp : (1 - 1 / p.toReal) + p.toReal⁻¹ = 1 := by ring
  rw [hexp, ENNReal.rpow_one, eLpNorm_restrict_eq_of_support_subset hgmeas hgs]
    at hbound
  simpa [ν, Real.volume_Icc, mul_comm] using hbound

omit [Fact (1 ≤ p)] in
/-- A finite Lp norm raised to the exponent is the integral of the norm power. -/
theorem eLpNorm_rpow_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    (eLpNorm f p μ) ^ p.toReal = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
  have hpr : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp0, hp⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf,
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpr, ENNReal.rpow_one]

/-- Tonelli transfers a uniform one-coordinate Lp estimate to the full
Euclidean product measure. -/
theorem eLpNorm_le_of_coordinate_estimate {f g : Domain d → 𝕜}
    (hf : Continuous f) (hg : Continuous g) (i : Fin d) (L : ℝ≥0∞)
    (hp : p ≠ ∞)
    (h : ∀ x, eLpNorm (f ∘ Function.update x i) p volume ≤
      L * eLpNorm (g ∘ Function.update x i) p volume) :
    eLpNorm f p volume ≤ L * eLpNorm g p volume := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  apply (ENNReal.rpow_le_rpow_iff hpr).mp
  rw [eLpNorm_rpow_integral hf.aestronglyMeasurable hp0 hp,
    ENNReal.mul_rpow_of_nonneg _ _ hpr.le,
    eLpNorm_rpow_integral hg.aestronglyMeasurable hp0 hp,
    ← lintegral_const_mul _ (by fun_prop), volume_pi]
  apply lintegral_le_of_lmarginal_le {i} (by fun_prop) (by fun_prop)
  rw [lmarginal_singleton, lmarginal_singleton]
  intro x
  have hx := ENNReal.rpow_le_rpow (h x) hpr.le
  have hfx : Continuous (f ∘ Function.update x i) :=
    hf.comp (continuous_const.update i continuous_id)
  have hgx : Continuous (g ∘ Function.update x i) :=
    hg.comp (continuous_const.update i continuous_id)
  rw [eLpNorm_rpow_integral hfx.aestronglyMeasurable hp0 hp,
    ENNReal.mul_rpow_of_nonneg _ _ hpr.le,
    eLpNorm_rpow_integral hgx.aestronglyMeasurable hp0 hp]
    at hx
  change (∫⁻ t, ‖f (Function.update x i t)‖ₑ ^ p.toReal) ≤
    ∫⁻ t, L ^ p.toReal * ‖g (Function.update x i t)‖ₑ ^ p.toReal
  rw [lintegral_const_mul _ (show Measurable
    (fun t => ‖g (Function.update x i t)‖ₑ ^ p.toReal) from
      hgx.enorm.measurable.pow_const _)]
  exact hx

@[simp] theorem natIndex_coordinateIndex (i : Fin d) :
    natIndex (coordinateIndex i) = Pi.single i 1 := by
  funext j
  simp [natIndex, coordinateIndex, Pi.single_apply, apply_ite]

@[simp] theorem multiIndexWord_coordinateIndex (i : Fin d) :
    multiIndexWord (natIndex (coordinateIndex i)) = [i] := by
  have hlen : (multiIndexWord (natIndex (coordinateIndex i))).length = 1 := by
    rw [multiIndexWord_length, natIndex_coordinateIndex]
    simp
  obtain ⟨j, hj⟩ := List.length_eq_one_iff.mp hlen
  have hi : i ∈ multiIndexWord (natIndex (coordinateIndex i)) := by
    apply List.count_pos_iff.mp
    rw [multiIndexWord_count, natIndex_coordinateIndex]
    simp
  rw [hj] at hi ⊢
  simp only [List.mem_singleton] at hi
  subst j
  rfl

@[simp] theorem testToSobolev_coordinate (φ : Tests 𝕜 Ω) (i : Fin d) :
    (testToSobolev (p := p) 1 φ).val (coordinateIndex i) =
      testToDomainLp (p := p) (testPartialCLM [i] φ) := by
  change testToDomainLp (p := p)
    (testPartialCLM (multiIndexWord (natIndex (coordinateIndex i))).reverse φ) = _
  rw [multiIndexWord_coordinateIndex]
  rfl

/-- The ordinary derivative along a coordinate line is the accepted test partial. -/
theorem deriv_coordinate_line (φ : Tests 𝕜 Ω) (i : Fin d) (x : Domain d) :
    deriv (φ ∘ Function.update x i) =
      (testPartialCLM [i] φ) ∘ Function.update x i := by
  funext t
  rw [fderiv_comp_deriv _ (φ.contDiff.differentiable (by simp)).differentiableAt
    (hasDerivAt_update x i t).differentiableAt, deriv_update]
  exact (testPartial_single_apply i φ _).symm

/-- The test-function estimate uses only the width of one coordinate strip. -/
theorem test_eLpNorm_le_strip (i : Fin d) {a b : ℝ} (hab : a < b)
    (hΩ : ∀ x ∈ Ω, a < x i ∧ x i < b) (hp : p ≠ ∞) (φ : Tests 𝕜 Ω) :
    eLpNorm φ p volume ≤ ENNReal.ofReal (b - a) *
      eLpNorm (testPartialCLM [i] φ) p volume := by
  apply eLpNorm_le_of_coordinate_estimate φ.continuous
    (testPartialCLM [i] φ).continuous i _ hp
  intro x
  have hfl : ContDiff ℝ 1 (φ ∘ Function.update x i) :=
    (φ.contDiff.of_le (by simp)).comp (by convert contDiff_update 1 x i)
  have hs : Function.support (φ ∘ Function.update x i) ⊆ Icc a b := by
    intro t ht
    have hx : Function.update x i t ∈ Ω :=
      φ.tsupport_subset (subset_tsupport φ ht)
    have hh := hΩ _ hx
    simp only [Function.update_self] at hh
    exact ⟨hh.1.le, hh.2.le⟩
  have he := eLpNorm_le_length_mul_deriv hab hfl
    (φ.hasCompactSupport.comp_isClosedEmbedding (isClosedEmbedding_update x i)) hs hp
  rw [deriv_coordinate_line] at he
  exact he

/-- Restricted-volume norms agree with full-volume norms for tests supported
in Ω. This includes the coordinate derivatives used in the Sobolev graph. -/
theorem norm_testToDomainLp (φ : Tests 𝕜 Ω) :
    ‖testToDomainLp (p := p) φ‖ = (eLpNorm φ p volume).toReal := by
  rw [testToDomainLp, Lp.norm_toLp,
    eLpNorm_restrict_eq_of_support_subset φ.continuous.aestronglyMeasurable
      ((subset_tsupport φ).trans φ.tsupport_subset)]

theorem poincare_coordinate_strip :
    Specs.ExpandedFA.Sobolev.PoincareInequality.CoordinateStrip := by
  intro 𝕜 _ d Ω i a b hab hΩ p _ hp u
  apply poincare_of_test_estimate hp i (b - a) ?_ u
  intro φ
  rw [testToSobolev_underlying, testToSobolev_coordinate,
    norm_testToDomainLp, norm_testToDomainLp]
  have he := test_eLpNorm_le_strip i hab hΩ hp φ
  have hn : ENNReal.ofReal (b - a) * eLpNorm (testPartialCLM [i] φ) p volume ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ((testPartialCLM [i] φ).continuous.memLp_of_hasCompactSupport
        (testPartialCLM [i] φ).hasCompactSupport).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono hn he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_pos.mpr hab).le] using hr

/-- Every bounded coordinate projection fits strictly inside some finite strip. -/
theorem exists_coordinate_strip (i : Fin d)
    (hΩ : Bornology.IsBounded ((fun x : Domain d => x i) '' (Ω : Set (Domain d)))) :
    ∃ a b : ℝ, a < b ∧ ∀ x ∈ Ω, a < x i ∧ x i < b := by
  obtain ⟨a, ha⟩ := hΩ.bddBelow
  obtain ⟨b, hb⟩ := hΩ.bddAbove
  refine ⟨a - 1, max a b + 1, ?_, ?_⟩
  · have := le_max_left a b
    linarith
  · intro x hx
    have hl := ha (show x i ∈ (fun x : Domain d => x i) '' (Ω : Set (Domain d)) from
      ⟨x, hx, rfl⟩)
    have hu := hb (show x i ∈ (fun x : Domain d => x i) '' (Ω : Set (Domain d)) from
      ⟨x, hx, rfl⟩)
    have := le_max_right a b
    constructor <;> linarith

theorem poincare_bounded_projection :
    Specs.ExpandedFA.Sobolev.PoincareInequality.BoundedProjection := by
  intro 𝕜 _ d Ω i hΩ
  obtain ⟨a, b, hab, hstrip⟩ := exists_coordinate_strip i hΩ
  refine ⟨b - a, sub_pos.mpr hab, ?_⟩
  intro p _ hp u
  exact (poincare_coordinate_strip 𝕜 d Ω i a b hab hstrip p hp u).trans
    (mul_le_mul_of_nonneg_left (coordinate_norm_le_gradient u.val i) (sub_pos.mpr hab).le)

theorem poincare_bounded_domain :
    Specs.ExpandedFA.Sobolev.PoincareInequality.BoundedDomain := by
  intro 𝕜 _ d Ω hΩ hdim
  rcases hdim with hd | he
  · let i : Fin d := ⟨0, hd⟩
    exact poincare_bounded_projection 𝕜 d Ω i
      (Bornology.IsBounded.image (ContinuousLinearMap.proj i : Domain d →L[ℝ] ℝ) hΩ)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro p _ hp u
    rw [poincare_empty 𝕜 d Ω he p hp u]
    exact mul_nonneg zero_le_one ENNReal.toReal_nonneg

end ExpandedFA.Sobolev
