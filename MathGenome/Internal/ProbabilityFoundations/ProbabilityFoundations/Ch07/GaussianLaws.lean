import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.CharacteristicUniqueness
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.GaussianLaws

/-!
The Gaussian law of paper.tex, Theorem 7.7 (existence and transform).
Mathlib constructs this law as the image of independent standard normals
under x ↦ m + √S x. Its positive semidefinite square root construction works
also for singular S. No restriction on the natural dimension is imposed.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace NNReal

namespace ProbabilityFoundations.Ch07

/-- N(m,S), using the canonical Gaussian construction on Euclidean space.
The asserted covariance and transform require only positive semidefiniteness. -/
noncomputable def gaussianLaw {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) : Measure (Euclidean d) :=
  multivariateGaussian m S

instance isGaussian_gaussianLaw {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) : IsGaussian (gaussianLaw m S) := by
  unfold gaussianLaw
  infer_instance

instance isProbabilityMeasure_gaussianLaw {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) : IsProbabilityMeasure (gaussianLaw m S) :=
  inferInstance

/-- The transform has the manuscript's plus sign and variance normalization. -/
theorem characteristicFunction_gaussianLaw {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (t : Euclidean d) :
    characteristicFunction (gaussianLaw m S) t =
      Complex.exp (Complex.I * (inner ℝ t m : ℂ) - ((t ⬝ᵥ S *ᵥ t : ℝ) : ℂ) / 2) := by
  simpa only [characteristicFunction, gaussianLaw, mul_comm Complex.I] using
    (charFun_multivariateGaussian (μ := m) hS t)

/-- The transform uniquely specifies the full law, even without moment assumptions. -/
theorem measure_eq_gaussianLaw_of_characteristicFunction {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (μ : Measure (Euclidean d)) (hμ : IsProbabilityMeasure μ)
    (h : ∀ t : Euclidean d, characteristicFunction μ t =
      Complex.exp (Complex.I * (inner ℝ t m : ℂ) - ((t ⬝ᵥ S *ᵥ t : ℝ) : ℂ) / 2)) :
    μ = gaussianLaw m S := by
  apply measure_eq_of_characteristicFunction_eq μ (gaussianLaw m S) hμ inferInstance
  intro t
  rw [h t, characteristicFunction_gaussianLaw m S hS t]

/-- The actual vector expectation is well-defined. -/
theorem integrable_id_gaussianLaw {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) : Integrable (fun x => x) (gaussianLaw m S) :=
  IsGaussian.integrable_fun_id

/-- The actual vector expectation equals m. -/
theorem integral_id_gaussianLaw {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) : (∫ x, x ∂gaussianLaw m S) = m :=
  integral_id_multivariateGaussian

/-- Covariances are actual centered-coordinate integrals. -/
theorem covariance_gaussianLaw {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (i j : Fin d) :
    covariance (fun x => x i) (fun x => x j) (gaussianLaw m S) = S i j :=
  covariance_eval_multivariateGaussian hS i j

theorem memLp_two_id_gaussianLaw {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) : MemLp (fun x => x) 2 (gaussianLaw m S) :=
  IsGaussian.memLp_two_fun_id

/-- Finiteness of E‖X‖², including every degenerate covariance. -/
theorem integrable_norm_sq_gaussianLaw {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) :
    Integrable (fun x => ‖x‖ ^ 2) (gaussianLaw m S) := by
  exact (memLp_two_iff_integrable_sq_norm (by fun_prop)).mp (memLp_two_id_gaussianLaw m S)

/-- Zero covariance gives precisely the point mass at the mean. -/
theorem gaussianLaw_zero_covariance {d : ℕ} (m : Euclidean d) :
    gaussianLaw m 0 = Measure.dirac m := by
  apply measure_eq_of_characteristicFunction_eq _ _ inferInstance inferInstance
  intro t
  rw [characteristicFunction_gaussianLaw m 0 Matrix.PosSemidef.zero t]
  simp [characteristicFunction, charFun_dirac, real_inner_comm, mul_comm]

/-- Compatibility with the existing univariate Gaussian, coordinate by coordinate. -/
theorem gaussianLaw_map_coordinate {d : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (i : Fin d) :
    (gaussianLaw m S).map (fun x => x i) = gaussianReal (m i) (S i i).toNNReal :=
  (measurePreserving_eval_multivariateGaussian (μ := m) hS (i := i)).map_eq

/-- Under the usual coordinate identification ℝ¹ → ℝ, N(m,v) is `gaussianReal m v`. -/
theorem gaussianLaw_univariate (m : ℝ) (v : ℝ≥0) :
    (gaussianLaw (WithLp.toLp 2 (fun _ : Fin 1 => m))
      (Matrix.diagonal (fun _ : Fin 1 => (v : ℝ)))).map (fun x => x 0) = gaussianReal m v := by
  have hS : (Matrix.diagonal (fun _ : Fin 1 => (v : ℝ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun _ => v.coe_nonneg)
  simpa using gaussianLaw_map_coordinate (WithLp.toLp 2 (fun _ : Fin 1 => m)) _ hS 0

end ProbabilityFoundations.Ch07
