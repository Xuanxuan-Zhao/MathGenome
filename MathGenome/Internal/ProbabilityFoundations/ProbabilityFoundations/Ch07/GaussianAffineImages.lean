import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.GaussianLaws
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.GaussianAffineImages

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

namespace ProbabilityFoundations.Ch07

/-- Congruence by an arbitrary rectangular matrix preserves positive semidefiniteness. -/
theorem affineCovariance_posSemidef {d r : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) (A : Matrix (Fin r) (Fin d) ℝ) :
    (A * S * Aᵀ).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using hS.mul_mul_conjTranspose_same A

private theorem continuous_matrix_mulVec {d r : ℕ} (A : Matrix (Fin r) (Fin d) ℝ) :
    Continuous (fun x : Euclidean d => WithLp.toLp 2 (A *ᵥ x)) := by
  exact (Matrix.toEuclideanLin A).continuous_of_finiteDimensional

private theorem inner_matrix_mulVec {d r : ℕ} (A : Matrix (Fin r) (Fin d) ℝ)
    (t : Euclidean r) (x : Euclidean d) :
    inner ℝ t (WithLp.toLp 2 (A *ᵥ x)) =
      inner ℝ (WithLp.toLp 2 (Aᵀ *ᵥ t)) x := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (A *ᵥ x) ⬝ᵥ t = x ⬝ᵥ (Aᵀ *ᵥ t)
  rw [dotProduct_comm, dotProduct_transpose_mulVec]

private theorem charFun_map_matrix {d r : ℕ} (μ : Measure (Euclidean d))
    (A : Matrix (Fin r) (Fin d) ℝ) (t : Euclidean r) :
    characteristicFunction (μ.map (fun x : Euclidean d => WithLp.toLp 2 (A *ᵥ x))) t =
      characteristicFunction μ (WithLp.toLp 2 (Aᵀ *ᵥ t)) := by
  rw [characteristicFunction_eq_integral, integral_map
    (continuous_matrix_mulVec A).measurable.aemeasurable (by fun_prop),
    characteristicFunction_eq_integral]
  congr 1
  funext x
  rw [inner_matrix_mulVec]

/-- The image measure under an arbitrary affine map is the Gaussian with the
transformed mean and covariance. No invertibility or positive rank is required. -/
theorem gaussianLaw_map_affine {d r : ℕ} (m : Euclidean d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (A : Matrix (Fin r) (Fin d) ℝ) (b : Euclidean r) :
    (gaussianLaw m S).map (fun x : Euclidean d => WithLp.toLp 2 (A *ᵥ x) + b) =
      gaussianLaw (WithLp.toLp 2 (A *ᵥ m) + b) (A * S * Aᵀ) := by
  have hA := (continuous_matrix_mulVec A).measurable
  apply measure_eq_gaussianLaw_of_characteristicFunction _ _
    (affineCovariance_posSemidef S hS A) _ inferInstance
  intro t
  have hq : t ⬝ᵥ (A * S * Aᵀ) *ᵥ t =
      (Aᵀ *ᵥ t) ⬝ᵥ S *ᵥ (Aᵀ *ᵥ t) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  rw [show (fun x : Euclidean d => WithLp.toLp 2 (A *ᵥ x) + b) =
    (fun y : Euclidean r => y + b) ∘
      (fun x : Euclidean d => WithLp.toLp 2 (A *ᵥ x)) from rfl,
    ← Measure.map_map (show Measurable (fun y : Euclidean r => y + b) from by fun_prop) hA]
  change charFun _ t = _
  rw [charFun_map_add_const]
  change characteristicFunction _ t * _ = _
  rw [charFun_map_matrix, characteristicFunction_gaussianLaw m S hS,
    ← Complex.exp_add]
  congr 1
  rw [← inner_matrix_mulVec A t m, hq]
  simp only [inner_add_right, Complex.ofReal_add, real_inner_comm b t]
  ring

/-- Any measurable random vector with law N(m,S) has the asserted affine image law. -/
theorem gaussianRandomVector_affine_law {d r : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Euclidean d) (hX : Measurable X)
    (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : P.map X = gaussianLaw m S)
    (A : Matrix (Fin r) (Fin d) ℝ) (b : Euclidean r) :
    P.map (fun ω => WithLp.toLp 2 (A *ᵥ X ω) + b) =
      gaussianLaw (WithLp.toLp 2 (A *ᵥ m) + b) (A * S * Aᵀ) := by
  have hAffine : Measurable (fun x : Euclidean d => WithLp.toLp 2 (A *ᵥ x) + b) :=
    (continuous_matrix_mulVec A).measurable.add_const b
  rw [show (fun ω => WithLp.toLp 2 (A *ᵥ X ω) + b) =
    (fun x : Euclidean d => WithLp.toLp 2 (A *ᵥ x) + b) ∘ X from rfl,
    ← Measure.map_map hAffine hX, hLaw, gaussianLaw_map_affine m S hS A b]

end ProbabilityFoundations.Ch07
