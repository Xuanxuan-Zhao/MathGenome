import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.GaussianLaws
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.GaussianProjectionCriterion

/-!
The projection characterization of Gaussian vectors (Theorem 7.7).
The Riesz representation theorem identifies every linear form with an inner
product projection. The resulting Gaussian law has finite second moment;
expanding its covariance bilinear form gives the actual coordinate covariance
matrix. Characteristic function uniqueness identifies N(EX,Cov X).
Neither the dimension nor the projected variances need be positive.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace NNReal

namespace ProbabilityFoundations.Ch07

open Specs.ProbabilityFoundations.Ch07.GaussianProjectionCriterion

/-- A vector is Gaussian when its Borel law is Gaussian. -/
def IsGaussianVector : gaussianVectorType := gaussianVectorValue

/-- Every real linear projection has a normal law, allowing variance zero. -/
def HasGaussianProjections : gaussianProjectionsType := gaussianProjectionsValue

noncomputable def vectorMean : vectorMeanType := vectorMeanValue

noncomputable def vectorCovariance : vectorCovarianceType := vectorCovarianceValue

theorem isGaussianVector_iff_projections {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Euclidean d) (hX : Measurable X) :
    IsGaussianVector P X ↔ HasGaussianProjections P X := by
  change IsGaussian (P.map X) ↔ ∀ t : Euclidean d,
    ∃ (a : ℝ) (v : ℝ≥0), P.map (fun ω => inner ℝ t (X ω)) = gaussianReal a v
  constructor
  · intro h t
    have := h
    refine ⟨∫ x, inner ℝ t x ∂P.map X, (Var[fun x => inner ℝ t x; P.map X]).toNNReal, ?_⟩
    change P.map ((fun x : Euclidean d => inner ℝ t x) ∘ X) = _
    rw [← Measure.map_map (μ := P)
      (by fun_prop : Measurable (fun x : Euclidean d => inner ℝ t x)) hX]
    exact IsGaussian.map_eq_gaussianReal (innerSL ℝ t)
  · intro h
    apply isGaussian_of_map_eq_gaussianReal
    intro L
    obtain ⟨t, ht⟩ := (InnerProductSpace.toDual ℝ (Euclidean d)).surjective L
    obtain ⟨a, v, hv⟩ := h t
    refine ⟨a, v, ?_⟩
    rw [← ht, Measure.map_map (by fun_prop) hX]
    exact hv

theorem gaussian_projection_moments {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Euclidean d) (hX : Measurable X)
    (h : HasGaussianProjections P X) :
    Integrable X P ∧ MemLp X 2 P ∧ Integrable (fun ω => ‖X ω‖ ^ 2) P := by
  have : IsGaussian (P.map X) := (isGaussianVector_iff_projections P X hX).mpr h
  have h₂ : MemLp X 2 P :=
    (memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable).mp
      IsGaussian.memLp_two_id
  exact ⟨h₂.integrable (by simp), h₂,
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp h₂⟩

/-- Expansion of the actual covariance bilinear form in the coordinate basis. -/
theorem covarianceBilin_eq_vectorCovariance {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Euclidean d)
    (h₂ : MemLp X 2 P) (x y : Euclidean d) :
    covarianceBilin (P.map X) x y = x ⬝ᵥ vectorCovariance P X *ᵥ y := by
  have hc (i : Fin d) : MemLp (fun ω => X ω i) 2 P :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' h₂
  have he : (fun ω => WithLp.toLp 2 (fun i => X ω i)) = X := rfl
  rw [← he]
  rw [covarianceBilin_apply_pi hc]
  simp only [vectorCovariance, vectorCovarianceValue, dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vectorCovariance_posSemidef {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Euclidean d)
    (h₂ : MemLp X 2 P) : (vectorCovariance P X).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa [vectorCovariance, vectorCovarianceValue, Matrix.conjTranspose_apply] using
      (covariance_comm (fun ω => X ω j) (fun ω => X ω i) (μ := P))
  · intro x
    have h := covarianceBilin_self_nonneg (μ := P.map X) (WithLp.toLp 2 x)
    rw [covarianceBilin_eq_vectorCovariance P X h₂] at h
    simpa using h

/-- The projection hypothesis determines the law with its actual moments. -/
theorem gaussian_projection_parameters {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Euclidean d) (hX : Measurable X)
    (h : HasGaussianProjections P X) :
    (vectorCovariance P X).PosSemidef ∧
      P.map X = gaussianLaw (vectorMean P X) (vectorCovariance P X) := by
  have : IsGaussian (P.map X) := (isGaussianVector_iff_projections P X hX).mpr h
  obtain ⟨h₁, h₂, _⟩ := gaussian_projection_moments P X hX h
  have hS := vectorCovariance_posSemidef P X h₂
  refine ⟨hS, ?_⟩
  apply measure_eq_gaussianLaw_of_characteristicFunction _ _ hS _ inferInstance
  intro t
  have hm : (∫ x, id x ∂P.map X) = vectorMean P X :=
    integral_map hX.aemeasurable aestronglyMeasurable_id
  rw [characteristicFunction, IsGaussian.charFun_eq', hm,
    covarianceBilin_eq_vectorCovariance P X h₂]
  rw [mul_comm Complex.I]

/-- This Gaussian predicate is exactly membership in the family N(m,S). -/
theorem isGaussianVector_iff_gaussianLaw {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Euclidean d) (hX : Measurable X) :
    IsGaussianVector P X ↔ ∃ (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
      S.PosSemidef ∧ P.map X = gaussianLaw m S := by
  constructor
  · intro h
    obtain ⟨hS, he⟩ := gaussian_projection_parameters P X hX
      ((isGaussianVector_iff_projections P X hX).mp h)
    exact ⟨vectorMean P X, vectorCovariance P X, hS, he⟩
  · rintro ⟨m, S, _, he⟩
    change IsGaussian (P.map X)
    rw [he]
    infer_instance

/-- Every linear projection of N(m,S) has the stipulated mean and variance. -/
theorem gaussianLaw_map_projection {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (t : Euclidean d) :
    (gaussianLaw m S).map (fun x => inner ℝ t x) =
      gaussianReal (inner ℝ t m) (t ⬝ᵥ S *ᵥ t).toNNReal := by
  have hm : (∫ x, inner ℝ t x ∂gaussianLaw m S) = inner ℝ t m := by
    rw [integral_inner (integrable_id_gaussianLaw m S), integral_id_gaussianLaw]
  have hv : Var[fun x => inner ℝ t x; gaussianLaw m S] = t ⬝ᵥ S *ᵥ t := by
    rw [← covarianceBilin_self (memLp_two_id_gaussianLaw m S)]
    exact covarianceBilin_multivariateGaussian hS t t
  change (gaussianLaw m S).map (innerSL ℝ t) = _
  rw [IsGaussian.map_eq_gaussianReal]
  change gaussianReal (∫ x, inner ℝ t x ∂gaussianLaw m S)
    (Var[fun x => inner ℝ t x; gaussianLaw m S]).toNNReal = _
  rw [hm, hv]

theorem projection_law_of_gaussianLaw {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Euclidean d) (hX : Measurable X)
    (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : P.map X = gaussianLaw m S) (t : Euclidean d) :
    P.map (fun ω => inner ℝ t (X ω)) =
      gaussianReal (inner ℝ t m) (t ⬝ᵥ S *ᵥ t).toNNReal := by
  change P.map ((fun x : Euclidean d => inner ℝ t x) ∘ X) = _
  rw [← Measure.map_map (μ := P)
    (by fun_prop : Measurable (fun x : Euclidean d => inner ℝ t x)) hX,
    hLaw, gaussianLaw_map_projection m S hS t]

theorem projection_law_actual_parameters {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Euclidean d) (hX : Measurable X)
    (h : HasGaussianProjections P X) (t : Euclidean d) :
    P.map (fun ω => inner ℝ t (X ω)) =
      gaussianReal (inner ℝ t (vectorMean P X))
        (t ⬝ᵥ vectorCovariance P X *ᵥ t).toNNReal := by
  obtain ⟨hS, hLaw⟩ := gaussian_projection_parameters P X hX h
  exact projection_law_of_gaussianLaw P X hX _ _ hS hLaw t

/-- In particular zero projected variance means a point mass, without exclusions. -/
theorem projection_law_zero_variance {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Euclidean d) (hX : Measurable X)
    (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : P.map X = gaussianLaw m S) (t : Euclidean d) (ht : t ⬝ᵥ S *ᵥ t = 0) :
    P.map (fun ω => inner ℝ t (X ω)) = Measure.dirac (inner ℝ t m) := by
  rw [projection_law_of_gaussianLaw P X hX m S hS hLaw t, ht,
    Real.toNNReal_zero, gaussianReal_zero_var]

end ProbabilityFoundations.Ch07
