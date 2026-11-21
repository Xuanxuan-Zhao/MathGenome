import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealRepresentationBorelExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.RieszRepresentation
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace ZeroAtInfty ENNReal Classical

namespace ExpandedFA.SpectralMeasure.RealRepresentationBorelExtension
open ExpandedFA.FunctionSpaces
open ScalarRieszMarkovSpec
universe u v

variable {S : Type u} [TopologicalSpace S] [CompactSpace S]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma representation_selfAdjoint (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (f : C(S, ℝ)) :
    star (π f) = π f := by
  rw [← map_star]
  congr 1

lemma representation_inner_swap (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (f : C(S, ℝ)) (x y : H) : ⟪π f x, y⟫_ℝ = ⟪x, π f y⟫_ℝ := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  exact congrArg (fun T : H →L[ℝ] H => ⟪x, T y⟫_ℝ) (representation_selfAdjoint π f)

lemma representation_positive (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (f : C(S, ℝ)) (hf : ∀ s, 0 ≤ f s) (x : H) : 0 ≤ ⟪x, π f x⟫_ℝ := by
  let r : C(S, ℝ) := ⟨fun s => Real.sqrt (f s), Real.continuous_sqrt.comp f.continuous⟩
  have hr : r * r = f := by
    ext s
    exact Real.mul_self_sqrt (hf s)
  rw [← hr, map_mul]
  change 0 ≤ ⟪x, π r (π r x)⟫_ℝ
  rw [← representation_inner_swap]
  exact real_inner_self_nonneg

lemma representation_apply_bound (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (f : C(S, ℝ)) (y : H) : ‖π f y‖ ≤ ‖f‖ * ‖y‖ := by
  let q : C(S, ℝ) := (‖f‖ ^ 2) • 1 - f * f
  have hq : ∀ s, 0 ≤ q s := by
    intro s
    have hf := f.norm_coe_le_norm s
    change 0 ≤ ‖f‖ ^ 2 * 1 - f s * f s
    have hf2 := pow_le_pow_left₀ (norm_nonneg (f s)) hf 2
    simp only [Real.norm_eq_abs, sq_abs] at hf2
    nlinarith
  have hp := representation_positive π q hq y
  have heq : ⟪y, π q y⟫_ℝ = ‖f‖ ^ 2 * ‖y‖ ^ 2 - ‖π f y‖ ^ 2 := by
    simp only [q, map_sub, map_smul, map_one, map_mul]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply, inner_sub_right,
      inner_smul_right]
    rw [← representation_inner_swap, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]
  rw [heq] at hp
  nlinarith [norm_nonneg (π f y), mul_nonneg (norm_nonneg f) (norm_nonneg y)]

theorem automatic_contractivity : Spec.AutomaticContractivity.{u, v} := by
  intro S _ _ _ H _ _ _ π f
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (representation_apply_bound π f)



variable [T2Space S] [MeasurableSpace S] [BorelSpace S]

/-- The compact continuous/C₀ identification does not require nonemptiness. -/
def compactEquiv : C(S, ℝ) ≃ₗᵢ[ℝ] C₀(S, ℝ) :=
  (ScalarRieszMarkov.compact_identification S ℝ).choose

@[simp] lemma compactEquiv_apply (f : C(S, ℝ)) (s : S) : compactEquiv f s = f s :=
  (ScalarRieszMarkov.compact_identification S ℝ).choose_spec.1 f s

@[simp] lemma compactEquiv_symm_apply (f : C₀(S, ℝ)) (s : S) :
    compactEquiv.symm f s = f s :=
  (ScalarRieszMarkov.compact_identification S ℝ).choose_spec.2 f s

/-- Contractivity supplies continuity of the coefficient functional, rather
than requiring any continuity premise on the algebraic representation. -/
def coefficientFunctional (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x y : H) :
    C₀(S, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟪x, π (compactEquiv.symm f) y⟫_ℝ
      map_add' := by intros; simp [map_add, inner_add_right]
      map_smul' := by intros; simp [map_smul, inner_smul_right] }
    (‖x‖ * ‖y‖) (fun f => by
      calc
        ‖⟪x, π (compactEquiv.symm f) y⟫_ℝ‖ ≤ ‖x‖ * ‖π (compactEquiv.symm f) y‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖compactEquiv.symm f‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left (representation_apply_bound _ _ _) (norm_nonneg _)
        _ = (‖x‖ * ‖y‖) * ‖f‖ := by rw [compactEquiv.symm.norm_map]; ring)

@[simp] lemma coefficientFunctional_apply (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (x y : H) (f : C₀(S, ℝ)) :
    coefficientFunctional π x y f = ⟪x, π (compactEquiv.symm f) y⟫_ℝ := rfl

lemma coefficientFunctional_norm_le (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x y : H) :
    ‖coefficientFunctional π x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply LinearMap.mkContinuous_norm_le
  positivity

lemma coefficient_unique (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x y : H)
    {ν η : VectorMeasure S ℝ} (hν : Spec.RepresentsCoefficient π x y ν)
    (hη : Spec.RepresentsCoefficient π x y η) : ν = η := by
  apply ScalarRieszMarkov.scalarIntegral_injective ν η hν.1 hη.1
  intro f
  have hn := (hν.2 (compactEquiv.symm f)).2
  have he := (hη.2 (compactEquiv.symm f)).2
  have hf : (compactEquiv.symm f : S → ℝ) = f := funext (compactEquiv_symm_apply f)
  rw [hf] at hn he
  exact hn.symm.trans he

lemma exists_coefficient (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x y : H) :
    ∃ ν : VectorMeasure S ℝ, Spec.RepresentsCoefficient π x y ν ∧
      ν.variation.real univ ≤ ‖x‖ * ‖y‖ := by
  obtain ⟨ν, hν, hrep, hnorm, _⟩ :=
    ScalarRieszMarkov.real_representation S (coefficientFunctional π x y)
  refine ⟨ν, ⟨hν, ?_⟩, ?_⟩
  · intro f
    have h := hrep (compactEquiv f)
    have hf : (compactEquiv f : S → ℝ) = f := funext (compactEquiv_apply f)
    rw [hf] at h
    simpa only [coefficientFunctional_apply, LinearIsometryEquiv.symm_apply_apply] using h
  · rw [← hnorm]
    exact coefficientFunctional_norm_le π x y

def coefficientMeasure (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x y : H) :
    VectorMeasure S ℝ := (exists_coefficient π x y).choose

lemma coefficientMeasure_represents (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x y : H) :
    Spec.RepresentsCoefficient π x y (coefficientMeasure π x y) :=
  (exists_coefficient π x y).choose_spec.1

lemma coefficientMeasure_mass_le (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x y : H) :
    (coefficientMeasure π x y).variation.real univ ≤ ‖x‖ * ‖y‖ :=
  (exists_coefficient π x y).choose_spec.2

lemma finiteScalarRadon_add {ν η : VectorMeasure S ℝ}
    (hν : FiniteScalarRadon ν) (hη : FiniteScalarRadon η) : FiniteScalarRadon (ν + η) := by
  letI : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  letI : IsFiniteMeasure η.variation := ⟨hη.1⟩
  letI : ν.variation.Regular :=
    (PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  letI : η.variation.Regular :=
    (PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hη.2
  letI : (ν.variation + η.variation).Regular := ScalarRieszMarkov.regular_add _ _
  letI : IsFiniteMeasure (ν + η).variation :=
    isFiniteMeasure_of_le (ν.variation + η.variation) VectorMeasure.variation_add_le
  exact ⟨measure_lt_top _ _, (PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
    (ScalarRieszMarkov.regular_of_le VectorMeasure.variation_add_le)⟩

lemma finiteScalarRadon_smul (a : ℝ) {ν : VectorMeasure S ℝ}
    (hν : FiniteScalarRadon ν) : FiniteScalarRadon (a • ν) := by
  letI : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  letI : ν.variation.Regular :=
    (PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  rw [FiniteScalarRadon, VectorMeasure.variation_smul]
  exact ⟨measure_lt_top _ _, (PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
    inferInstance⟩

lemma coefficientMeasure_add_left (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x z y : H) :
    coefficientMeasure π (x + z) y = coefficientMeasure π x y + coefficientMeasure π z y := by
  apply coefficient_unique π (x + z) y (coefficientMeasure_represents _ _ _)
  have hx := coefficientMeasure_represents π x y
  have hz := coefficientMeasure_represents π z y
  refine ⟨finiteScalarRadon_add hx.1 hz.1, ?_⟩
  intro f
  refine ⟨VectorMeasure.Integrable.add_vectorMeasure (hx.2 f).1 (hz.2 f).1, ?_⟩
  rw [scalarIntegral, VectorMeasure.integral_add_vectorMeasure (hx.2 f).1 (hz.2 f).1]
  exact (inner_add_left _ _ _).trans (congrArg₂ (· + ·) (hx.2 f).2 (hz.2 f).2)

lemma coefficientMeasure_smul_left (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (a : ℝ) (x y : H) : coefficientMeasure π (a • x) y = a • coefficientMeasure π x y := by
  apply coefficient_unique π (a • x) y (coefficientMeasure_represents _ _ _)
  have hx := coefficientMeasure_represents π x y
  refine ⟨finiteScalarRadon_smul a hx.1, ?_⟩
  intro f
  refine ⟨VectorMeasure.Integrable.smul_vectorMeasure (hx.2 f).1 a, ?_⟩
  rw [scalarIntegral, VectorMeasure.integral_smul_vectorMeasure]
  simpa only [real_inner_smul_left, smul_eq_mul, scalarIntegral] using congrArg (a * ·) (hx.2 f).2

lemma coefficientMeasure_symm (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x y : H) :
    coefficientMeasure π x y = coefficientMeasure π y x := by
  apply coefficient_unique π x y (coefficientMeasure_represents _ _ _)
  have hy := coefficientMeasure_represents π y x
  refine ⟨hy.1, fun f => ⟨(hy.2 f).1, ?_⟩⟩
  rw [← representation_inner_swap, real_inner_comm]
  exact (hy.2 f).2

lemma coefficientMeasure_add_right (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x y z : H) :
    coefficientMeasure π x (y + z) = coefficientMeasure π x y + coefficientMeasure π x z := by
  rw [coefficientMeasure_symm π x (y + z), coefficientMeasure_add_left,
    coefficientMeasure_symm π y x, coefficientMeasure_symm π z x]

lemma coefficientMeasure_smul_right (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (a : ℝ) (x y : H) : coefficientMeasure π x (a • y) = a • coefficientMeasure π x y := by
  rw [coefficientMeasure_symm π x (a • y), coefficientMeasure_smul_left,
    coefficientMeasure_symm π y x]



lemma coefficientMeasure_diagonal_nonneg (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (x : H) (B : Set S) (hB : MeasurableSet B) : 0 ≤ coefficientMeasure π x x B := by
  obtain ⟨ρ, hρ, hfin, hrep, _⟩ := ScalarRieszMarkov.positive_representation S
    (coefficientFunctional π x x) (fun f hf =>
      representation_positive π (compactEquiv.symm f) (by simpa using hf) x)
  letI : IsFiniteMeasure ρ := ⟨hfin⟩
  have hr : Spec.RepresentsCoefficient π x x ρ.toSignedMeasure := by
    refine ⟨⟨by simpa using hfin, by simpa using hρ⟩, ?_⟩
    intro f
    have h := hrep (compactEquiv f)
    have hf : (compactEquiv f : S → ℝ) = f := funext (compactEquiv_apply f)
    rw [hf] at h
    simpa only [Measure.variation_toSignedMeasure, coefficientFunctional_apply,
      LinearIsometryEquiv.symm_apply_apply, ScalarRieszMarkov.scalarIntegral_toSignedMeasure] using h
  rw [coefficient_unique π x x (coefficientMeasure_represents _ _ _) hr,
    Measure.toSignedMeasure_apply_measurable hB]
  exact ENNReal.toReal_nonneg

lemma coefficientMeasure_system (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) :
    Spec.CoefficientSystem π (coefficientMeasure π) := by
  refine ⟨?_, coefficientMeasure_add_left π, coefficientMeasure_smul_left π,
    coefficientMeasure_add_right π, coefficientMeasure_smul_right π,
    coefficientMeasure_symm π, coefficientMeasure_diagonal_nonneg π⟩
  intro x y
  exact ⟨coefficientMeasure_represents π x y, coefficientMeasure_mass_le π x y,
    fun _ h => coefficient_unique π x y h (coefficientMeasure_represents _ _ _)⟩

theorem coefficient_existence : Spec.CoefficientExistence.{u, v} := by
  intro S _ _ _ _ _ H _ _ _ π
  exact ⟨coefficientMeasure π, coefficientMeasure_system π⟩

lemma boundedBorel_continuous (f : C(S, ℝ)) : Spec.IsBoundedBorel (f : S → ℝ) :=
  ⟨f.continuous.measurable, ‖f‖, norm_nonneg _, f.norm_coe_le_norm⟩

lemma boundedBorel_const (a : ℝ) : Spec.IsBoundedBorel (fun _ : S => a) :=
  ⟨measurable_const, |a|, abs_nonneg _, fun _ => le_rfl⟩

lemma boundedBorel_add {g h : S → ℝ} (hg : Spec.IsBoundedBorel g)
    (hh : Spec.IsBoundedBorel h) : Spec.IsBoundedBorel (fun s => g s + h s) := by
  obtain ⟨Cg, hCg, hgb⟩ := hg.2
  obtain ⟨Ch, hCh, hhb⟩ := hh.2
  exact ⟨hg.1.add hh.1, Cg + Ch, add_nonneg hCg hCh,
    fun s => (abs_add_le _ _).trans (add_le_add (hgb s) (hhb s))⟩

lemma boundedBorel_mul {g h : S → ℝ} (hg : Spec.IsBoundedBorel g)
    (hh : Spec.IsBoundedBorel h) : Spec.IsBoundedBorel (fun s => g s * h s) := by
  obtain ⟨Cg, hCg, hgb⟩ := hg.2
  obtain ⟨Ch, hCh, hhb⟩ := hh.2
  refine ⟨hg.1.mul hh.1, Cg * Ch, mul_nonneg hCg hCh, fun s => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hgb s) (hhb s) (abs_nonneg _) hCg

lemma boundedBorel_integrable {g : S → ℝ} (hg : Spec.IsBoundedBorel g)
    (ρ : Measure S) [IsFiniteMeasure ρ] : Integrable g ρ := by
  obtain ⟨C, _, hC⟩ := hg.2
  exact (integrable_const C).mono' hg.1.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- The density is the native countably additive vector measure defined from
set integrals, not a representing-measure certificate. -/
def density (ν : VectorMeasure S ℝ) (g : S → ℝ) : VectorMeasure S ℝ :=
  ν.withDensity g (ContinuousLinearMap.mul ℝ ℝ)

lemma density_variation {ν : VectorMeasure S ℝ} [IsFiniteMeasure ν.variation]
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g) :
    (density ν g).variation = ν.variation.withDensity (fun s => ‖g s‖ₑ) := by
  rw [density, VectorMeasure.variation_withDensity (boundedBorel_integrable hg _) (by simp),
    VectorMeasure.variation_transpose_eq _ _ (by simp)]

lemma density_variation_le {ν : VectorMeasure S ℝ} [IsFiniteMeasure ν.variation]
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g) {C : ℝ} (hC : 0 ≤ C)
    (hgb : ∀ s, |g s| ≤ C) : (density ν g).variation ≤ ENNReal.ofReal C • ν.variation := by
  rw [density_variation hg]
  calc
    ν.variation.withDensity (fun s => ‖g s‖ₑ) ≤
        ν.variation.withDensity (fun _ => ENNReal.ofReal C) :=
      withDensity_mono (Filter.Eventually.of_forall (fun s => by
        simpa only [← ofReal_norm, Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal (hgb s)))
    _ = ENNReal.ofReal C • ν.variation := by rw [withDensity_const]

/-- Bounded Borel densities preserve finite regularity under exactly the
arbitrary compact Hausdorff hypotheses of the source. -/
lemma finiteScalarRadon_density {ν : VectorMeasure S ℝ} (hν : FiniteScalarRadon ν)
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g) : FiniteScalarRadon (density ν g) := by
  letI : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  letI : ν.variation.Regular :=
    (PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  obtain ⟨C, hC, hgb⟩ := hg.2
  have hb := density_variation_le (ν := ν) hg hC hgb
  letI : IsFiniteMeasure (ENNReal.ofReal C • ν.variation) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (density ν g).variation :=
    isFiniteMeasure_of_le (ENNReal.ofReal C • ν.variation) hb
  refine ⟨measure_lt_top _ _, (PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr ?_⟩
  exact ScalarRieszMarkov.regular_of_le hb



lemma boundedBorel_simple (f : SimpleFunc S ℝ) : Spec.IsBoundedBorel (f : S → ℝ) := by
  obtain ⟨C, hC⟩ := (f.map (fun a : ℝ => |a|)).exists_forall_le
  refine ⟨f.measurable, max C 0, le_max_right _ _, fun s => ?_⟩
  exact (hC s).trans (le_max_left _ _)

/-- Change of density first on simple functions. -/
lemma scalarIntegral_density_simple {ν : VectorMeasure S ℝ} [IsFiniteMeasure ν.variation]
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g)
    [IsFiniteMeasure (density ν g).variation] (f : SimpleFunc S ℝ) :
    scalarIntegral (density ν g) f = scalarIntegral ν (fun s => f s * g s) := by
  induction f using SimpleFunc.induction with
  | @const a B hB =>
    have hi : (SimpleFunc.piecewise B hB (SimpleFunc.const S a) (SimpleFunc.const S 0) :
        S → ℝ) = B.indicator (fun _ => a) := by ext s; simp [Set.indicator, hB]
    rw [hi]
    have hm : (fun s => B.indicator (fun _ => a) s * g s) =
        (fun s => a • B.indicator g s) := by
      ext s
      by_cases hs : s ∈ B <;> simp [hs, smul_eq_mul]
    rw [hm, scalarIntegral, VectorMeasure.integral_indicator_const _ hB,
      density, VectorMeasure.withDensity_apply (boundedBorel_integrable hg _)]
    rw [scalarIntegral, VectorMeasure.integral_fun_smul, VectorMeasure.integral_indicator hB]
    rfl
  | @add f h _ hf hh =>
    have hfint := boundedBorel_integrable (boundedBorel_simple f) (density ν g).variation
    have hhint := boundedBorel_integrable (boundedBorel_simple h) (density ν g).variation
    have hfgint := boundedBorel_integrable (boundedBorel_mul (boundedBorel_simple f) hg) ν.variation
    have hhgint := boundedBorel_integrable (boundedBorel_mul (boundedBorel_simple h) hg) ν.variation
    have hm : (fun s => (f + h) s * g s) = (fun s => f s * g s + h s * g s) := by
      ext s
      exact add_mul _ _ _
    change scalarIntegral (density ν g) (fun s => f s + h s) = _
    rw [hm]
    simp only [scalarIntegral] at hf hh ⊢
    rw [VectorMeasure.integral_fun_add hfint hhint,
      VectorMeasure.integral_fun_add hfgint hhgint, hf, hh]

/-- The substitution law for two arbitrary bounded Borel functions follows
from pointwise bounded simple approximation and vector-measure dominated
convergence. It does not rely on Baire=Borel or a countable topology. -/
lemma scalarIntegral_density {ν : VectorMeasure S ℝ} [IsFiniteMeasure ν.variation]
    {g f : S → ℝ} (hg : Spec.IsBoundedBorel g) (hf : Spec.IsBoundedBorel f)
    [IsFiniteMeasure (density ν g).variation] :
    scalarIntegral (density ν g) f = scalarIntegral ν (fun s => f s * g s) := by
  obtain ⟨C, hC, hfb⟩ := hf.2
  obtain ⟨D, hD, hgb⟩ := hg.2
  let F := hf.1.stronglyMeasurable.approxBounded C
  have hF (n : ℕ) (s : S) : ‖F n s‖ ≤ C :=
    hf.1.stronglyMeasurable.norm_approxBounded_le hC n s
  have hlim (s : S) : Filter.Tendsto (fun n => F n s) Filter.atTop (nhds (f s)) :=
    hf.1.stronglyMeasurable.tendsto_approxBounded_of_norm_le (hfb s)
  have hleft : Filter.Tendsto (fun n => scalarIntegral (density ν g) (F n)) Filter.atTop
      (nhds (scalarIntegral (density ν g) f)) :=
    VectorMeasure.tendsto_integral_filter_of_norm_le_const (μ := density ν g)
      (B := ContinuousLinearMap.mul ℝ ℝ)
      (Filter.Eventually.of_forall (fun n => (F n).measurable.aestronglyMeasurable))
      ⟨C, Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall (hF n))⟩
      (Filter.Eventually.of_forall hlim)
  have hright : Filter.Tendsto (fun n => scalarIntegral ν (fun s => F n s * g s)) Filter.atTop
      (nhds (scalarIntegral ν (fun s => f s * g s))) :=
    VectorMeasure.tendsto_integral_filter_of_norm_le_const (μ := ν)
      (B := ContinuousLinearMap.mul ℝ ℝ)
      (Filter.Eventually.of_forall (fun n => ((F n).measurable.mul hg.1).aestronglyMeasurable))
      ⟨C * D, Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall (fun s => by
        rw [norm_mul]
        exact mul_le_mul (hF n s) (hgb s) (norm_nonneg _) hC))⟩
      (Filter.Eventually.of_forall (fun s => (hlim s).mul tendsto_const_nhds))
  have heq : (fun n => scalarIntegral (density ν g) (F n)) =
      (fun n => scalarIntegral ν (fun s => F n s * g s)) :=
    funext (fun n => scalarIntegral_density_simple hg (F n))
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright



instance coefficientMeasure_finite (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (x y : H) :
    IsFiniteMeasure (coefficientMeasure π x y).variation :=
  ⟨(coefficientMeasure_represents π x y).1.1⟩

lemma coefficientIntegral_bound (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g) {C : ℝ} (hC : 0 ≤ C)
    (hgb : ∀ s, |g s| ≤ C) (x y : H) :
    ‖scalarIntegral (coefficientMeasure π x y) g‖ ≤ C * ‖x‖ * ‖y‖ := by
  calc
    _ ≤ ∫ s, ‖g s‖ ∂(coefficientMeasure π x y).variation :=
      ScalarRieszMarkov.scalarIntegral_l1_bound _ _
    _ ≤ ∫ _ : S, C ∂(coefficientMeasure π x y).variation :=
      integral_mono_ae (boundedBorel_integrable hg _).norm (integrable_const C)
        (Filter.Eventually.of_forall hgb)
    _ = C * (coefficientMeasure π x y).variation.real univ := by simp [mul_comm]
    _ ≤ C * (‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left (coefficientMeasure_mass_le π x y) hC
    _ = _ := (mul_assoc _ _ _).symm

/-- Actual real bilinearity of the integral follows from the proved
bilinearity of the countably additive coefficient measures. -/
def integralBilin (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (g : S → ℝ) (hg : Spec.IsBoundedBorel g) : H →ₗ[ℝ] H →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => scalarIntegral (coefficientMeasure π x y) g
      map_add' := fun y z => by
        rw [coefficientMeasure_add_right, scalarIntegral,
          VectorMeasure.integral_add_vectorMeasure
            (boundedBorel_integrable hg _) (boundedBorel_integrable hg _)]
        rfl
      map_smul' := fun a y => by
        simp only [coefficientMeasure_smul_right, scalarIntegral,
          VectorMeasure.integral_smul_vectorMeasure, RingHom.id_apply] }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change scalarIntegral (coefficientMeasure π (x + z) y) g =
      scalarIntegral (coefficientMeasure π x y) g + scalarIntegral (coefficientMeasure π z y) g
    rw [coefficientMeasure_add_left, scalarIntegral,
      VectorMeasure.integral_add_vectorMeasure
        (boundedBorel_integrable hg _) (boundedBorel_integrable hg _)]
    rfl
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change scalarIntegral (coefficientMeasure π (a • x) y) g =
      a • scalarIntegral (coefficientMeasure π x y) g
    simp only [coefficientMeasure_smul_left, scalarIntegral,
      VectorMeasure.integral_smul_vectorMeasure, RingHom.id_apply, LinearMap.smul_apply]

/-- This form uses original real vectors in both slots. -/
def integralForm (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (g : S → ℝ) (hg : Spec.IsBoundedBorel g) : H →L⋆[ℝ] H →L[ℝ] ℝ :=
  (integralBilin π g hg).mkContinuous₂ hg.2.choose
    (coefficientIntegral_bound π hg hg.2.choose_spec.1 hg.2.choose_spec.2)

/-- Only values on actual bounded Borel functions are mathematically specified. -/
def borelOperator (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (g : S → ℝ) : H →L[ℝ] H :=
  if hg : Spec.IsBoundedBorel g then
    (ExpandedFA.Hilbert.RieszRepresentation.form_representation ℝ H (integralForm π g hg)).choose
  else 0

lemma borelOperator_inner (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g) (x y : H) :
    ⟪x, borelOperator π g y⟫_ℝ = scalarIntegral (coefficientMeasure π x y) g := by
  rw [borelOperator, dif_pos hg]
  exact ((ExpandedFA.Hilbert.RieszRepresentation.form_representation ℝ H
    (integralForm π g hg)).choose_spec.1 x y).symm

lemma borelOperator_represents (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g) :
    Spec.OperatorRepresents (coefficientMeasure π) g (borelOperator π g) :=
  fun x y => ⟨boundedBorel_integrable hg _, borelOperator_inner π hg x y⟩

lemma borelOperator_unique (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g) (A : H →L[ℝ] H)
    (hA : Spec.OperatorRepresents (coefficientMeasure π) g A) : A = borelOperator π g := by
  ext y
  apply ext_inner_left ℝ
  intro x
  exact (hA x y).2.trans (borelOperator_inner π hg x y).symm

lemma borelOperator_norm_le (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g) {C : ℝ} (hC : 0 ≤ C)
    (hgb : ∀ s, |g s| ≤ C) : ‖borelOperator π g‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro y
  have h := coefficientIntegral_bound π hg hC hgb (borelOperator π g y) y
  rw [← borelOperator_inner π hg, real_inner_self_eq_norm_sq,
    Real.norm_of_nonneg (sq_nonneg _)] at h
  by_cases hz : ‖borelOperator π g y‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖borelOperator π g y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

lemma borelOperator_continuous (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) (f : C(S, ℝ)) :
    borelOperator π f = π f := by
  symm
  apply borelOperator_unique π (boundedBorel_continuous f)
  exact fun x y => (coefficientMeasure_represents π x y).2 f

lemma borelOperator_selfAdjoint (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g) : star (borelOperator π g) = borelOperator π g := by
  apply borelOperator_unique π hg
  intro x y
  refine ⟨boundedBorel_integrable hg _, ?_⟩
  change ⟪x, (borelOperator π g).adjoint y⟫_ℝ = _
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm,
    borelOperator_inner π hg, coefficientMeasure_symm π y x]



lemma coefficientMeasure_continuous_right (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (f : C(S, ℝ)) (x y : H) :
    coefficientMeasure π x (π f y) = density (coefficientMeasure π x y) f := by
  have hd := finiteScalarRadon_density (coefficientMeasure_represents π x y).1
    (boundedBorel_continuous f)
  letI : IsFiniteMeasure (density (coefficientMeasure π x y) f).variation := ⟨hd.1⟩
  apply coefficient_unique π x (π f y) (coefficientMeasure_represents _ _ _)
  refine ⟨hd, fun h => ⟨boundedBorel_integrable (boundedBorel_continuous h) _, ?_⟩⟩
  rw [scalarIntegral_density (boundedBorel_continuous f) (boundedBorel_continuous h)]
  have hrep := ((coefficientMeasure_represents π x y).2 (h * f)).2
  simpa only [map_mul, ContinuousMap.coe_mul, Pi.mul_def, mul_apply_eq_comp] using hrep

lemma coefficientMeasure_continuous_left (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (f : C(S, ℝ)) (x y : H) :
    coefficientMeasure π (π f x) y = density (coefficientMeasure π x y) f := by
  rw [coefficientMeasure_symm, coefficientMeasure_continuous_right,
    coefficientMeasure_symm π y x]

/-- Continuous-test uniqueness identifies the actual signed measures after
applying any bounded Borel operator to the second vector. -/
lemma coefficientMeasure_borel_right (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    {g : S → ℝ} (hg : Spec.IsBoundedBorel g) (x y : H) :
    coefficientMeasure π x (borelOperator π g y) = density (coefficientMeasure π x y) g := by
  have hd := finiteScalarRadon_density (coefficientMeasure_represents π x y).1 hg
  letI : IsFiniteMeasure (density (coefficientMeasure π x y) g).variation := ⟨hd.1⟩
  apply coefficient_unique π x (borelOperator π g y) (coefficientMeasure_represents _ _ _)
  refine ⟨hd, fun f => ⟨boundedBorel_integrable (boundedBorel_continuous f) _, ?_⟩⟩
  have hdf := finiteScalarRadon_density (coefficientMeasure_represents π x y).1
    (boundedBorel_continuous f)
  letI : IsFiniteMeasure (density (coefficientMeasure π x y) f).variation := ⟨hdf.1⟩
  rw [← representation_inner_swap, borelOperator_inner π hg,
    coefficientMeasure_continuous_left,
    scalarIntegral_density (boundedBorel_continuous f) hg,
    scalarIntegral_density hg (boundedBorel_continuous f)]
  congr 1
  ext s
  exact mul_comm _ _

lemma borelOperator_mul (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    {g h : S → ℝ} (hg : Spec.IsBoundedBorel g) (hh : Spec.IsBoundedBorel h) :
    borelOperator π (fun s => g s * h s) = borelOperator π g * borelOperator π h := by
  symm
  apply borelOperator_unique π (boundedBorel_mul hg hh)
  intro x y
  refine ⟨boundedBorel_integrable (boundedBorel_mul hg hh) _, ?_⟩
  have hd := finiteScalarRadon_density (coefficientMeasure_represents π x y).1 hh
  letI : IsFiniteMeasure (density (coefficientMeasure π x y) h).variation := ⟨hd.1⟩
  change ⟪x, borelOperator π g (borelOperator π h y)⟫_ℝ = _
  rw [borelOperator_inner π hg, coefficientMeasure_borel_right π hh,
    scalarIntegral_density hh hg]

lemma borelOperator_add (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    {g h : S → ℝ} (hg : Spec.IsBoundedBorel g) (hh : Spec.IsBoundedBorel h) :
    borelOperator π (fun s => g s + h s) = borelOperator π g + borelOperator π h := by
  symm
  apply borelOperator_unique π (boundedBorel_add hg hh)
  intro x y
  refine ⟨boundedBorel_integrable (boundedBorel_add hg hh) _, ?_⟩
  change ⟪x, borelOperator π g y + borelOperator π h y⟫_ℝ = _
  rw [inner_add_right, borelOperator_inner π hg, borelOperator_inner π hh]
  exact (VectorMeasure.integral_fun_add (boundedBorel_integrable hg _)
    (boundedBorel_integrable hh _)).symm

lemma borelOperator_smul (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H))
    (a : ℝ) {g : S → ℝ} (hg : Spec.IsBoundedBorel g) :
    borelOperator π (fun s => a * g s) = a • borelOperator π g := by
  symm
  apply borelOperator_unique π (boundedBorel_mul (boundedBorel_const a) hg)
  intro x y
  refine ⟨boundedBorel_integrable (boundedBorel_mul (boundedBorel_const a) hg) _, ?_⟩
  change ⟪x, a • borelOperator π g y⟫_ℝ = _
  rw [inner_smul_right, borelOperator_inner π hg]
  exact (VectorMeasure.integral_fun_smul _ _ a g).symm

lemma borelOperator_one (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) :
    borelOperator π (fun _ => 1) = 1 := by
  change borelOperator π (1 : C(S, ℝ)) = 1
  rw [borelOperator_continuous, map_one]

lemma borelOperator_extension (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) :
    Spec.BorelExtension π (coefficientMeasure π) (borelOperator π) := by
  refine ⟨?_, borelOperator_continuous π, borelOperator_one π, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact ⟨borelOperator_represents π hg, borelOperator_unique π hg⟩
  · intro g h hg hh
    exact borelOperator_add π hg hh
  · intro a g hg
    exact borelOperator_smul π a hg
  · intro g h hg hh
    exact borelOperator_mul π hg hh
  · intro g hg
    simpa only [star_trivial] using (borelOperator_selfAdjoint π hg).symm
  · intro g hg C hC hgb
    exact borelOperator_norm_le π hg hC hgb
  · intro Ψ hΨ g hg
    exact borelOperator_unique π hg (Ψ g) (hΨ g hg)

/-- The full real bounded-Borel extension, including zero Hilbert spaces and
empty compact spaces, obtained without assuming a PVM or a control measure. -/
theorem real_representation_extension : Spec.RealRepresentationExtension.{u, v} := by
  intro S _ _ _ _ _ H _ _ _ π
  refine ⟨fun f => automatic_contractivity S H π f,
    coefficientMeasure π, borelOperator π, coefficientMeasure_system π,
    borelOperator_extension π⟩

end ExpandedFA.SpectralMeasure.RealRepresentationBorelExtension
