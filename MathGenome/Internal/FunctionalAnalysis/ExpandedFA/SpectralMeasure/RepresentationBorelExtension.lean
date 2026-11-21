import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RepresentationBorelExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.Definitions
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.MeasureTheory.Function.ContinuousMapDense

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped InnerProductSpace ZeroAtInfty ComplexConjugate
open MeasureTheory Set

namespace ExpandedFA.SpectralMeasure.RepresentationBorelExtension
universe u v

variable {S : Type u} {H : Type v} [TopologicalSpace S] [CompactSpace S]
  [T2Space S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The continuous scalar-linear coefficient functional, with the source's
conjugate-first inner product convention. -/
def coefficientFunctional (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (x y : H) :
    C(S, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟪x, π f y⟫_ℂ
      map_add' := fun f g => by simp [inner_add_right]
      map_smul' := fun c f => by simp [inner_smul_right] }
    (‖x‖ * ‖y‖) (by
      intro f
      calc
        ‖⟪x, π f y⟫_ℂ‖ ≤ ‖x‖ * ‖π f y‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖π f‖ * ‖y‖) := mul_le_mul_of_nonneg_left
          ((π f).le_opNorm y) (norm_nonneg x)
        _ ≤ ‖x‖ * (‖f‖ * ‖y‖) := by
          gcongr
          exact NonUnitalStarAlgHom.norm_apply_le π f
        _ = (‖x‖ * ‖y‖) * ‖f‖ := by ring)

@[simp] theorem coefficientFunctional_apply
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (x y : H) (f : C(S, ℂ)) :
    coefficientFunctional π x y f = ⟪x, π f y⟫_ℂ := rfl

theorem coefficientFunctional_norm_le
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (x y : H) :
    ‖coefficientFunctional π x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply (coefficientFunctional π x y).opNorm_le_bound (by positivity)
  intro f
  calc
    ‖coefficientFunctional π x y f‖ ≤ ‖x‖ * ‖π f y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖π f‖ * ‖y‖) := mul_le_mul_of_nonneg_left
      ((π f).le_opNorm y) (norm_nonneg x)
    _ ≤ ‖x‖ * (‖f‖ * ‖y‖) := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le π f
    _ = _ := by ring

/-- Riesz--Markov on C(S), transported through the isometric compact
identification with C₀(S). No point of S is chosen. -/
theorem coefficient_measure_exists
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (x y : H) :
    ∃ μ : ComplexMeasure S,
      FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon μ ∧
      (∀ f : C(S, ℂ), Integrable f μ.variation ∧
        ⟪x, π f y⟫_ℂ = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral μ f) ∧
      μ.variation univ ≤ ENNReal.ofReal (‖x‖ * ‖y‖) ∧
      (∀ η : ComplexMeasure S,
        FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon η →
        (∀ f : C(S, ℂ), Integrable f η.variation ∧
          ⟪x, π f y⟫_ℂ = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral η f) → η = μ) := by
  obtain ⟨e, he, he'⟩ := FunctionSpaces.ScalarRieszMarkov.compact_identification S ℂ
  let L : C₀(S, ℂ) →L[ℂ] ℂ :=
    (coefficientFunctional π x y).comp e.symm.toLinearIsometry.toContinuousLinearMap
  have hL : ‖L‖ ≤ ‖x‖ * ‖y‖ := by
    apply L.opNorm_le_bound (by positivity)
    intro f
    calc
      ‖L f‖ ≤ ‖coefficientFunctional π x y‖ * ‖e.symm f‖ :=
        (coefficientFunctional π x y).le_opNorm _
      _ ≤ (‖x‖ * ‖y‖) * ‖f‖ := by
        rw [e.symm.norm_map]
        exact mul_le_mul_of_nonneg_right (coefficientFunctional_norm_le π x y) (norm_nonneg _)
  obtain ⟨μ, hμ, hrep, hnorm, huniq⟩ :=
    FunctionSpaces.ScalarRieszMarkov.complex_representation S L
  refine ⟨μ, hμ, ?_, ?_, ?_⟩
  · intro f
    have hf := hrep (e f)
    have heq : (e f : S → ℂ) = f := funext (he f)
    rw [heq] at hf
    change Integrable f μ.variation ∧
      ⟪x, π (e.symm (e f)) y⟫_ℂ = _ at hf
    simpa only [e.symm_apply_apply] using hf
  · have hreal : μ.variation.real univ ≤ ‖x‖ * ‖y‖ := hnorm ▸ hL
    rw [← ENNReal.ofReal_toReal hμ.1.ne]
    exact ENNReal.ofReal_le_ofReal hreal
  · intro η hη hηrep
    apply huniq η hη
    intro f
    have hf := hηrep (e.symm f)
    have heq : (e.symm f : S → ℂ) = f := funext (he' f)
    rw [heq] at hf
    exact hf

theorem scalar_measures : Spec.ScalarMeasures.{u, v} := by
  intro S H _ _ _ _ _ _ _ _ π
  choose μ hμ hrep hbound huniq using coefficient_measure_exists π
  exact ⟨μ, hμ, hrep, hbound, huniq⟩

open FunctionSpaces.ScalarRieszMarkovSpec

theorem bounded_borel_integrable (μ : ComplexMeasure S) (hμ : FiniteScalarRadon μ)
    (g : S → ℂ) (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    Integrable g μ.variation := by
  letI : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  obtain ⟨C, hC⟩ := hg.2
  exact Integrable.of_bound hg.1.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem coefficient_integral_bound
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hgC : ∀ s, ‖g s‖ ≤ C) (x y : H) :
    ‖scalarIntegral (μ x y) g‖ ≤ C * ‖x‖ * ‖y‖ := by
  letI : IsFiniteMeasure (μ x y).variation := ⟨(hμ.1 x y).1⟩
  have hmass : (μ x y).variation.real univ ≤ ‖x‖ * ‖y‖ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hμ.2.2.1 x y)
  calc
    ‖scalarIntegral (μ x y) g‖ ≤ C * ‖ContinuousLinearMap.mul ℝ ℂ‖ *
        (μ x y).variation.real univ :=
      VectorMeasure.norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hgC)
    _ ≤ C * 1 * (μ x y).variation.real univ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℝ ℂ
    _ ≤ C * 1 * (‖x‖ * ‖y‖) := by gcongr
    _ = _ := by ring

/-- Finite simultaneous L¹ approximation. Taking the sum of the variations
retains regularity on arbitrary compact Hausdorff spaces. No scalar control
measure for the whole representation is introduced. -/
theorem continuous_integral_approximation {ι : Type*} [Fintype ι]
    (μ : ι → ComplexMeasure S) (hμ : ∀ i, FiniteScalarRadon (μ i))
    (g : S → ℂ) (hg : SpectralMeasure.Spec.IsBoundedMeasurable g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : C(S, ℂ), ∀ i, (∫ s, ‖g s - f s‖ ∂(μ i).variation) ≤ ε := by
  classical
  letI (i : ι) : IsFiniteMeasure (μ i).variation := ⟨(hμ i).1⟩
  letI (i : ι) : (μ i).variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp (hμ i).2
  have hreg : ∀ t : Finset ι, (∑ i ∈ t, (μ i).variation).Regular := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (inferInstance : (0 : Measure S).Regular)
    | @insert a t ha ih =>
      letI := ih
      simpa only [Finset.sum_insert ha] using
        FunctionSpaces.ScalarRieszMarkov.regular_add (μ a).variation (∑ i ∈ t, (μ i).variation)
  let ρ : Measure S := ∑ i, (μ i).variation
  letI : ρ.Regular := hreg Finset.univ
  have hgρ : Integrable g ρ := by
    obtain ⟨C, hC⟩ := hg.2
    exact Integrable.of_bound hg.1.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  obtain ⟨f, hf, _⟩ := hgρ.exists_boundedContinuous_integral_sub_le hε
  refine ⟨f.toContinuousMap, fun i => ?_⟩
  have hle : (μ i).variation ≤ ρ :=
    Finset.single_le_sum (fun j _ => (show 0 ≤ (μ j).variation from bot_le)) (Finset.mem_univ i)
  exact (integral_mono_measure hle (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (hgρ.sub (f.integrable ρ)).norm).trans hf

/-- Continuous tests transfer every finite continuous relation between scalar
integrals to bounded Borel tests. This avoids assuming algebraic identities
of the representing measures. -/
theorem integral_relation_extension {ι : Type*} [Fintype ι]
    (μ : ι → ComplexMeasure S) (hμ : ∀ i, FiniteScalarRadon (μ i))
    (F : (ι → ℂ) → ℂ) (hF : Continuous F)
    (hzero : ∀ f : C(S, ℂ), F (fun i => scalarIntegral (μ i) f) = 0)
    (g : S → ℂ) (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    F (fun i => scalarIntegral (μ i) g) = 0 := by
  have hmem : (fun i => scalarIntegral (μ i) g) ∈
      closure (Set.range (fun f : C(S, ℂ) => fun i => scalarIntegral (μ i) f)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨f, hf⟩ := continuous_integral_approximation μ hμ g hg (half_pos hε)
    refine ⟨(fun i => scalarIntegral (μ i) f), ⟨f, rfl⟩, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
    apply (dist_pi_le_iff (half_pos hε).le).mpr
    intro i
    have hi := VectorMeasure.integral_fun_sub
      (bounded_borel_integrable (μ i) (hμ i) g hg) (bounded_borel_integrable (μ i) (hμ i) f
        ⟨f.continuous.measurable, ⟨‖f‖, f.norm_coe_le_norm⟩⟩)
        (B := ContinuousLinearMap.mul ℝ ℂ)
    rw [dist_eq_norm]
    change ‖(μ i).integral g (ContinuousLinearMap.mul ℝ ℂ) -
      (μ i).integral f (ContinuousLinearMap.mul ℝ ℂ)‖ ≤ _
    rw [← hi]
    exact (FunctionSpaces.ScalarRieszMarkov.scalarIntegral_l1_bound (μ i) _).trans (hf i)
  exact closure_minimal (Set.range_subset_iff.mpr hzero)
    (isClosed_eq hF continuous_const) hmem

theorem coefficient_integral_add_left
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) (x z y : H) :
    scalarIntegral (μ (x + z) y) g =
      scalarIntegral (μ x y) g + scalarIntegral (μ z y) g := by
  let ν : Fin 3 → ComplexMeasure S := ![μ (x + z) y, μ x y, μ z y]
  have hν : ∀ i, FiniteScalarRadon (ν i) := by
    intro i; fin_cases i <;> exact hμ.1 _ _
  apply sub_eq_zero.mp
  apply integral_relation_extension ν hν (fun a => a 0 - (a 1 + a 2)) (by fun_prop) ?_ g hg
  intro f
  change scalarIntegral (μ (x + z) y) f -
    (scalarIntegral (μ x y) f + scalarIntegral (μ z y) f) = 0
  simp only [← (hμ.2.1 (x + z) y f).2, ← (hμ.2.1 x y f).2, ← (hμ.2.1 z y f).2,
    inner_add_left, sub_self]

theorem coefficient_integral_add_right
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) (x y z : H) :
    scalarIntegral (μ x (y + z)) g =
      scalarIntegral (μ x y) g + scalarIntegral (μ x z) g := by
  let ν : Fin 3 → ComplexMeasure S := ![μ x (y + z), μ x y, μ x z]
  have hν : ∀ i, FiniteScalarRadon (ν i) := by
    intro i; fin_cases i <;> exact hμ.1 _ _
  apply sub_eq_zero.mp
  apply integral_relation_extension ν hν (fun a => a 0 - (a 1 + a 2)) (by fun_prop) ?_ g hg
  intro f
  change scalarIntegral (μ x (y + z)) f -
    (scalarIntegral (μ x y) f + scalarIntegral (μ x z) f) = 0
  simp only [← (hμ.2.1 x (y + z) f).2, ← (hμ.2.1 x y f).2, ← (hμ.2.1 x z f).2,
    map_add, inner_add_right, sub_self]

theorem coefficient_integral_smul_left
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) (c : ℂ) (x y : H) :
    scalarIntegral (μ (c • x) y) g = conj c * scalarIntegral (μ x y) g := by
  let ν : Fin 2 → ComplexMeasure S := ![μ (c • x) y, μ x y]
  have hν : ∀ i, FiniteScalarRadon (ν i) := by
    intro i; fin_cases i <;> exact hμ.1 _ _
  apply sub_eq_zero.mp
  apply integral_relation_extension ν hν (fun a => a 0 - conj c * a 1) (by fun_prop) ?_ g hg
  intro f
  simp only [ν, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← (hμ.2.1 (c • x) y f).2, ← (hμ.2.1 x y f).2, inner_smul_left, sub_self]

theorem coefficient_integral_smul_right
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) (c : ℂ) (x y : H) :
    scalarIntegral (μ x (c • y)) g = c * scalarIntegral (μ x y) g := by
  let ν : Fin 2 → ComplexMeasure S := ![μ x (c • y), μ x y]
  have hν : ∀ i, FiniteScalarRadon (ν i) := by
    intro i; fin_cases i <;> exact hμ.1 _ _
  apply sub_eq_zero.mp
  apply integral_relation_extension ν hν (fun a => a 0 - c * a 1) (by fun_prop) ?_ g hg
  intro f
  simp only [ν, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← (hμ.2.1 x (c • y) f).2, ← (hμ.2.1 x y f).2,
    map_smul, inner_smul_right, sub_self]

/-- The Borel coefficient form, with its two semilinearity laws proved by
finite simultaneous approximation, rather than included as hypotheses. -/
def coefficientFormLinear
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := fun y => scalarIntegral (μ x y) g
      map_add' := coefficient_integral_add_right π μ hμ g hg x
      map_smul' := fun c y => by
        simpa only [smul_eq_mul, RingHom.id_apply] using
          coefficient_integral_smul_right π μ hμ g hg c x y }
  map_add' x z := by
    ext y
    exact coefficient_integral_add_left π μ hμ g hg x z y
  map_smul' c x := by
    ext y
    change scalarIntegral (μ (c • x) y) g = conj c * scalarIntegral (μ x y) g
    exact coefficient_integral_smul_left π μ hμ g hg c x y

theorem borel_operator_exists
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    ∃ A : H →L[ℂ] H, ∀ x y, ⟪x, A y⟫_ℂ = scalarIntegral (μ x y) g := by
  obtain ⟨C, hC, hgC⟩ := hg.nonneg_bound
  let a : H →L⋆[ℂ] H →L[ℂ] ℂ :=
    (coefficientFormLinear π μ hμ g hg).mkContinuous₂ C
      (coefficient_integral_bound π μ hμ g C hC hgC)
  let A := ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin a)
  refine ⟨A, fun x y => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- The same density argument allows bounded multipliers and conjugation in
the tests. Only a common Lipschitz bound on the pointwise transformations is
needed; neither weighted measures nor a countable approximation of the
compact space is assumed. -/
theorem transformed_integral_relation_extension {ι : Type*} [Fintype ι]
    (μ : ι → ComplexMeasure S) (hμ : ∀ i, FiniteScalarRadon (μ i))
    (T : ι → (S → ℂ) → (S → ℂ))
    (hT : ∀ i f, SpectralMeasure.Spec.IsBoundedMeasurable f →
      SpectralMeasure.Spec.IsBoundedMeasurable (T i f))
    (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ i f g s, ‖T i f s - T i g s‖ ≤ K * ‖f s - g s‖)
    (F : (ι → ℂ) → ℂ) (hF : Continuous F)
    (hzero : ∀ f : C(S, ℂ), F (fun i => scalarIntegral (μ i) (T i f)) = 0)
    (g : S → ℂ) (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    F (fun i => scalarIntegral (μ i) (T i g)) = 0 := by
  have hmem : (fun i => scalarIntegral (μ i) (T i g)) ∈
      closure (Set.range (fun f : C(S, ℂ) => fun i => scalarIntegral (μ i) (T i f))) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hK1 : 0 < K + 1 := by linarith
    obtain ⟨f, hf⟩ := continuous_integral_approximation μ hμ g hg
      (div_pos (half_pos hε) hK1)
    have hfb : SpectralMeasure.Spec.IsBoundedMeasurable (f : S → ℂ) :=
      ⟨f.continuous.measurable, ⟨‖f‖, f.norm_coe_le_norm⟩⟩
    refine ⟨(fun i => scalarIntegral (μ i) (T i f)), ⟨f, rfl⟩,
      lt_of_le_of_lt ?_ (half_lt_self hε)⟩
    apply (dist_pi_le_iff (half_pos hε).le).mpr
    intro i
    have hgi := bounded_borel_integrable (μ i) (hμ i) g hg
    have hfi := bounded_borel_integrable (μ i) (hμ i) f hfb
    have hTg := bounded_borel_integrable (μ i) (hμ i) (T i g) (hT i g hg)
    have hTf := bounded_borel_integrable (μ i) (hμ i) (T i f) (hT i f hfb)
    have hi : scalarIntegral (μ i) (T i g) - scalarIntegral (μ i) (T i f) =
        scalarIntegral (μ i) (fun s => T i g s - T i f s) :=
      (VectorMeasure.integral_fun_sub hTg hTf (B := ContinuousLinearMap.mul ℝ ℂ)).symm
    rw [dist_eq_norm, hi]
    calc
      _ ≤ ∫ s, ‖T i g s - T i f s‖ ∂(μ i).variation :=
        FunctionSpaces.ScalarRieszMarkov.scalarIntegral_l1_bound _ _
      _ ≤ ∫ s, K * ‖g s - f s‖ ∂(μ i).variation :=
        integral_mono (hTg.sub hTf).norm ((hgi.sub hfi).norm.const_mul K) (hLip i g f)
      _ = K * ∫ s, ‖g s - f s‖ ∂(μ i).variation := integral_const_mul _ _
      _ ≤ K * ((ε / 2) / (K + 1)) := mul_le_mul_of_nonneg_left (hf i) hK
      _ ≤ (K + 1) * ((ε / 2) / (K + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = ε / 2 := mul_div_cancel₀ _ hK1.ne'
  exact closure_minimal (Set.range_subset_iff.mpr hzero)
    (isClosed_eq hF continuous_const) hmem

def borelOperator
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ) : H →L[ℂ] H := by
  classical
  exact if hg : SpectralMeasure.Spec.IsBoundedMeasurable g then
    (borel_operator_exists π μ hμ g hg).choose else 0

theorem borelOperator_coefficient
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) (x y : H) :
    ⟪x, borelOperator π μ hμ g y⟫_ℂ = scalarIntegral (μ x y) g := by
  simpa only [borelOperator, dite_eq_left hg] using
    (borel_operator_exists π μ hμ g hg).choose_spec x y

theorem borelOperator_continuous
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (f : C(S, ℂ)) :
    borelOperator π μ hμ f = π f := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [borelOperator_coefficient π μ hμ f
    ⟨f.continuous.measurable, ⟨‖f‖, f.norm_coe_le_norm⟩⟩]
  exact (hμ.2.1 x y f).2.symm

theorem borelOperator_add
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (f g : S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    borelOperator π μ hμ (f + g) = borelOperator π μ hμ f + borelOperator π μ hμ g := by
  ext y
  apply ext_inner_left ℂ
  intro x
  simp only [add_apply, inner_add_right]
  rw [borelOperator_coefficient π μ hμ (f + g) (hf.add hg),
    borelOperator_coefficient π μ hμ f hf, borelOperator_coefficient π μ hμ g hg]
  exact VectorMeasure.integral_add (bounded_borel_integrable _ (hμ.1 x y) f hf)
    (bounded_borel_integrable _ (hμ.1 x y) g hg)

theorem borelOperator_smul
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (c : ℂ) (f : S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    borelOperator π μ hμ (c • f) = c • borelOperator π μ hμ f := by
  ext y
  apply ext_inner_left ℂ
  intro x
  simp only [smul_apply, inner_smul_right]
  rw [borelOperator_coefficient π μ hμ (c • f) (hf.smul c),
    borelOperator_coefficient π μ hμ f hf]
  exact FunctionSpaces.ScalarRieszMarkov.scalarIntegral_smul _ c f

theorem borelOperator_norm_le
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (f : S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (C : ℝ)
    (hC : 0 ≤ C) (hCf : ∀ s, ‖f s‖ ≤ C) : ‖borelOperator π μ hμ f‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro y
  let A := borelOperator π μ hμ f
  have hh := coefficient_integral_bound π μ hμ f C hC hCf (A y) y
  rw [← borelOperator_coefficient π μ hμ f hf] at hh
  change ‖⟪A y, A y⟫_ℂ‖ ≤ C * ‖A y‖ * ‖y‖ at hh
  have hsq : ‖A y‖ ^ 2 ≤ C * ‖A y‖ * ‖y‖ := by
    simpa only [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] using hh
  by_cases hz : ‖A y‖ = 0
  · change ‖A y‖ ≤ _
    rw [hz]
    positivity
  · have hzpos : 0 < ‖A y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact (mul_le_mul_iff_right₀ hzpos).mp (by nlinarith [hsq])

theorem coefficient_integral_star
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) (x y : H) :
    scalarIntegral (μ x y) (star g) = conj (scalarIntegral (μ y x) g) := by
  let ν : Fin 2 → ComplexMeasure S := ![μ x y, μ y x]
  let T : Fin 2 → (S → ℂ) → (S → ℂ) := ![(fun a => star a), id]
  have hν : ∀ i, FiniteScalarRadon (ν i) := by
    intro i; fin_cases i <;> exact hμ.1 _ _
  have hT : ∀ i a, SpectralMeasure.Spec.IsBoundedMeasurable a →
      SpectralMeasure.Spec.IsBoundedMeasurable (T i a) := by
    intro i a ha
    fin_cases i
    · exact ha.star
    · exact ha
  have hLip : ∀ i a b s, ‖T i a s - T i b s‖ ≤ 1 * ‖a s - b s‖ := by
    intro i a b s
    fin_cases i
    · change ‖star (a s) - star (b s)‖ ≤ 1 * ‖a s - b s‖
      rw [← star_sub, norm_star, one_mul]
    · change ‖a s - b s‖ ≤ 1 * ‖a s - b s‖
      rw [one_mul]
  apply sub_eq_zero.mp
  apply transformed_integral_relation_extension ν hν T hT 1 zero_le_one hLip
    (fun a => a 0 - conj (a 1)) (by fun_prop) ?_ g hg
  intro f
  change scalarIntegral (μ x y) (star (f : S → ℂ)) -
    conj (scalarIntegral (μ y x) f) = 0
  have hs : star (f : S → ℂ) = (star f : C(S, ℂ)) := rfl
  rw [hs, ← (hμ.2.1 x y (star f)).2, ← (hμ.2.1 y x f).2, map_star]
  change ⟪x, ContinuousLinearMap.adjoint (π f) y⟫_ℂ - conj ⟪y, π f x⟫_ℂ = 0
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm, sub_self]

theorem borelOperator_star
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    borelOperator π μ hμ (star g) = star (borelOperator π μ hμ g) := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [borelOperator_coefficient π μ hμ (star g) hg.star,
    coefficient_integral_star π μ hμ g hg x y,
    ← borelOperator_coefficient π μ hμ g hg y x]
  change conj ⟪y, borelOperator π μ hμ g x⟫_ℂ =
    ⟪x, ContinuousLinearMap.adjoint (borelOperator π μ hμ g) y⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

/-- An identity with a bounded Borel multiplier, first known on continuous
tests, extends to every bounded Borel test. Finite L¹ approximation supplies
all limits, including the product integral. -/
theorem weighted_integral_identity_extension
    (ν η : ComplexMeasure S) (hν : FiniteScalarRadon ν) (hη : FiniteScalarRadon η)
    (b : S → ℂ) (hb : SpectralMeasure.Spec.IsBoundedMeasurable b)
    (heq : ∀ f : C(S, ℂ), scalarIntegral ν f = scalarIntegral η ((f : S → ℂ) * b))
    (g : S → ℂ) (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    scalarIntegral ν g = scalarIntegral η (g * b) := by
  obtain ⟨C, hC, hbC⟩ := hb.nonneg_bound
  let ρ : Fin 2 → ComplexMeasure S := ![ν, η]
  let T : Fin 2 → (S → ℂ) → (S → ℂ) := ![id, (fun a => a * b)]
  have hρ : ∀ i, FiniteScalarRadon (ρ i) := by
    intro i; fin_cases i
    · exact hν
    · exact hη
  have hT : ∀ i a, SpectralMeasure.Spec.IsBoundedMeasurable a →
      SpectralMeasure.Spec.IsBoundedMeasurable (T i a) := by
    intro i a ha
    fin_cases i
    · exact ha
    · exact ha.mul hb
  have hLip : ∀ i a d s, ‖T i a s - T i d s‖ ≤ max 1 C * ‖a s - d s‖ := by
    intro i a d s
    fin_cases i
    · change ‖a s - d s‖ ≤ max 1 C * ‖a s - d s‖
      exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
    · change ‖a s * b s - d s * b s‖ ≤ max 1 C * ‖a s - d s‖
      rw [← sub_mul, norm_mul, mul_comm ‖a s - d s‖]
      exact mul_le_mul_of_nonneg_right ((hbC s).trans (le_max_right _ _)) (norm_nonneg _)
  apply sub_eq_zero.mp
  apply transformed_integral_relation_extension ρ hρ T hT (max 1 C)
    (zero_le_one.trans (le_max_left _ _)) hLip (fun a => a 0 - a 1) (by fun_prop) ?_ g hg
  intro f
  exact sub_eq_zero.mpr (heq f)

theorem coefficient_integral_mul_continuous
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) (f : C(S, ℂ)) (x y : H) :
    scalarIntegral (μ x (π f y)) g = scalarIntegral (μ x y) (g * f) := by
  apply weighted_integral_identity_extension _ _ (hμ.1 x (π f y)) (hμ.1 x y)
    f ⟨f.continuous.measurable, ⟨‖f‖, f.norm_coe_le_norm⟩⟩ ?_ g hg
  intro a
  change scalarIntegral (μ x (π f y)) a = scalarIntegral (μ x y) (a * f : C(S, ℂ))
  rw [← (hμ.2.1 x (π f y) a).2, ← (hμ.2.1 x y (a * f)).2, map_mul]
  rfl

theorem borelOperator_mul_continuous
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (g : S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) (f : C(S, ℂ)) :
    borelOperator π μ hμ (g * f) = borelOperator π μ hμ g * π f := by
  ext y
  apply ext_inner_left ℂ
  intro x
  change ⟪x, borelOperator π μ hμ (g * f) y⟫_ℂ =
    ⟪x, borelOperator π μ hμ g (π f y)⟫_ℂ
  rw [borelOperator_coefficient π μ hμ (g * f)
    (hg.mul ⟨f.continuous.measurable, ⟨‖f‖, f.norm_coe_le_norm⟩⟩),
    borelOperator_coefficient π μ hμ g hg]
  exact (coefficient_integral_mul_continuous π μ hμ g hg f x y).symm

/-- The second density step: both factors are arbitrary bounded Borel
functions. Only finitely many coefficient measures are needed in each test. -/
theorem borelOperator_mul
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (μ : H → H → ComplexMeasure S)
    (hμ : Spec.RepresentsCoefficients π μ) (f g : S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    borelOperator π μ hμ (f * g) = borelOperator π μ hμ f * borelOperator π μ hμ g := by
  ext y
  apply ext_inner_left ℂ
  intro x
  let A := borelOperator π μ hμ f
  have heq : ∀ a : C(S, ℂ),
      scalarIntegral (μ (ContinuousLinearMap.adjoint A x) y) a =
        scalarIntegral (μ x y) ((a : S → ℂ) * f) := by
    intro a
    rw [← (hμ.2.1 (ContinuousLinearMap.adjoint A x) y a).2]
    rw [ContinuousLinearMap.adjoint_inner_left]
    have hright := borelOperator_mul_continuous π μ hμ f hf a
    have hcoef := borelOperator_coefficient π μ hμ (f * a)
      (hf.mul ⟨a.continuous.measurable, ⟨‖a‖, a.norm_coe_le_norm⟩⟩) x y
    rw [hright] at hcoef
    exact hcoef.trans (congrArg (scalarIntegral (μ x y)) (mul_comm f (a : S → ℂ)))
  have hprod := weighted_integral_identity_extension _ _
    (hμ.1 (ContinuousLinearMap.adjoint A x) y) (hμ.1 x y) f hf heq g hg
  change ⟪x, borelOperator π μ hμ (f * g) y⟫_ℂ =
    ⟪x, A (borelOperator π μ hμ g y)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left A (borelOperator π μ hμ g y) x,
    borelOperator_coefficient π μ hμ (f * g) (hf.mul hg),
    borelOperator_coefficient π μ hμ g hg, hprod, mul_comm f g]

/-- The complete bounded Borel extension stage, including both arbitrary
Borel factors in the product law. -/
theorem borel_extension : Spec.BorelExtension.{u, v} := by
  intro S H _ _ _ _ _ _ _ _ π
  obtain ⟨μ, hμ⟩ := scalar_measures S H π
  refine ⟨μ, borelOperator π μ hμ, hμ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg x y
    exact ⟨bounded_borel_integrable _ (hμ.1 x y) g hg,
      borelOperator_coefficient π μ hμ g hg x y⟩
  · exact borelOperator_continuous π μ hμ
  · change borelOperator π μ hμ ((1 : C(S, ℂ)) : S → ℂ) = 1
    rw [borelOperator_continuous, map_one]
  · exact borelOperator_add π μ hμ
  · exact borelOperator_smul π μ hμ
  · exact borelOperator_mul π μ hμ
  · exact borelOperator_star π μ hμ
  · intro f C hf hC hbound
    exact borelOperator_norm_le π μ hμ f hf C hC hbound
  · intro Ψ hΨ g hg
    ext y
    apply ext_inner_left ℂ
    intro x
    rw [hΨ g hg x y, borelOperator_coefficient π μ hμ g hg]

end ExpandedFA.SpectralMeasure.RepresentationBorelExtension
