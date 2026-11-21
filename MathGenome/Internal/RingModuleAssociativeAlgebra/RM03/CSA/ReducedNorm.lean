import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedCharpoly
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedNorm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Flat.Basic

/-! Construction and properties of the reduced norm. -/

namespace RM03.CSA

open scoped TensorProduct
open Algebra.TensorProduct
open Specs.RM03.CSA (genericMatrix)

universe u v w z

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {ι : Type z} [Fintype ι] {L : Type w} [Field L] [Algebra k L]

/-- The signed constant term of the reduced characteristic polynomial of an element. -/
noncomputable def reducedNorm (hA : IsCentralSimple k A) (a : A) : k :=
  (-1) ^ degree k A * (reducedCharpoly hA a).eval 0

/-- The signed constant term of the generic reduced characteristic polynomial. -/
noncomputable def genericReducedNorm (hA : IsCentralSimple k A) (a : ι → A) :
    MvPolynomial ι k :=
  (-1) ^ degree k A * (genericReducedCharpoly hA a).eval 0

/-- In any matrix splitting, the reduced norm becomes the determinant. -/
theorem reducedNorm_map (hA : IsCentralSimple k A) (a : A)
    (e : BaseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L) :
    algebraMap k L (reducedNorm hA a) = (e (1 ⊗ₜ[k] a)).det := by
  rw [reducedNorm, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin,
    ← reducedCharpoly_map hA a e, ← Polynomial.coeff_zero_eq_eval_zero]
  simp

theorem reducedNorm_eq_det (hA : IsCentralSimple k A) (a : A)
    (e : A ≃ₐ[k] Matrix (Fin (degree k A)) (Fin (degree k A)) k) :
    reducedNorm hA a = (e a).det := by
  simpa using reducedNorm_map hA a ((Algebra.TensorProduct.lid k A).trans e)

/-- The identity with the determinant holds coefficientwise in the coordinate variables. -/
theorem genericReducedNorm_map (hA : IsCentralSimple k A) (a : ι → A)
    (e : BaseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L) :
    MvPolynomial.map (algebraMap k L) (genericReducedNorm hA a) =
      (genericMatrix fun i => e (1 ⊗ₜ[k] a i)).det := by
  rw [genericReducedNorm, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin,
    ← genericReducedCharpoly_map hA a e, ← Polynomial.coeff_zero_eq_eval_zero]
  simp

/-- Each term in the determinant uses one linear entry per column. -/
private theorem genericMatrix_det_homogeneous {R : Type*} [CommRing R] {n : ℕ}
    (M : ι → Matrix (Fin n) (Fin n) R) :
    (genericMatrix M).det.IsHomogeneous n := by
  classical
  have hentry (j l : Fin n) : ((genericMatrix M) j l).IsHomogeneous 1 := by
    simp only [genericMatrix, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => ?_)
    rw [mul_comm]
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun σ _ => ?_)
  have hprod : (∏ i, (genericMatrix M) (σ i) i).IsHomogeneous n := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i => (genericMatrix M) (σ i) i) (fun _ => 1) (fun i _ => hentry _ _)
  have hsign : ((Equiv.Perm.sign σ : ℤˣ) : MvPolynomial ι R) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤˣ) : R) := by
    simp
  rw [hsign]
  exact hprod.C_mul _

theorem genericReducedNorm_homogeneous (hA : IsCentralSimple k A) (a : ι → A) :
    (genericReducedNorm hA a).IsHomogeneous (degree k A) := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
  apply MvPolynomial.IsHomogeneous.of_map (algebraMap k (AlgebraicClosure k)).injective
  rw [genericReducedNorm_map hA a e]
  exact genericMatrix_det_homogeneous _

theorem genericReducedNorm_eval (hA : IsCentralSimple k A) (a : ι → A) (x : ι → k) :
    MvPolynomial.eval x (genericReducedNorm hA a) = reducedNorm hA (∑ i, x i • a i) := by
  rw [genericReducedNorm, reducedNorm, ← Polynomial.coeff_zero_eq_eval_zero,
    ← Polynomial.coeff_zero_eq_eval_zero, ← genericReducedCharpoly_eval hA a x]
  simp

theorem reducedNorm_basis_eval (hA : IsCentralSimple k A) (b : Module.Basis ι k A) (a : A) :
    MvPolynomial.eval (fun i => b.repr a i) (genericReducedNorm hA b) = reducedNorm hA a := by
  rw [genericReducedNorm_eval, b.sum_repr]

theorem reducedNorm_one (hA : IsCentralSimple k A) : reducedNorm hA 1 = 1 := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
  apply (algebraMap k (AlgebraicClosure k)).injective
  rw [reducedNorm_map hA 1 e, ← Algebra.TensorProduct.one_def]
  simp

theorem reducedNorm_basis_totalDegree (hA : IsCentralSimple k A) (b : Module.Basis ι k A) :
    (genericReducedNorm hA b).totalDegree = degree k A := by
  refine (genericReducedNorm_homogeneous hA b).totalDegree (fun h => ?_)
  simpa [h, reducedNorm_one] using reducedNorm_basis_eval hA b 1

private theorem degree_baseChange_eq (hA : IsCentralSimple k A) :
    degree L (BaseChange k L A) = degree k A := by
  unfold degree
  rw [finrank_baseChange hA]

/-- Arbitrary field extension acts on the coefficients of the norm polynomial. -/
theorem genericReducedNorm_baseChange (hA : IsCentralSimple k A) (a : ι → A)
    (hL : IsCentralSimple L (BaseChange k L A) := isCentralSimple_baseChange hA) :
    genericReducedNorm hL (fun i => 1 ⊗ₜ[k] a i) =
      MvPolynomial.map (algebraMap k L) (genericReducedNorm hA a) := by
  rw [genericReducedNorm, genericReducedCharpoly_baseChange hA a hL, degree_baseChange_eq hA,
    genericReducedNorm, ← Polynomial.coeff_zero_eq_eval_zero,
    ← Polynomial.coeff_zero_eq_eval_zero]
  simp [Specs.RM03.CSA.mapGeneric]

theorem reducedNorm_basis_baseChange (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (hL : IsCentralSimple L (BaseChange k L A) := isCentralSimple_baseChange hA) :
    genericReducedNorm hL (b.baseChange L) =
      MvPolynomial.map (algebraMap k L) (genericReducedNorm hA b) := by
  rw [show (⇑(b.baseChange L)) = fun i => 1 ⊗ₜ[k] b i from
    funext (Module.Basis.baseChange_apply L b)]
  exact genericReducedNorm_baseChange hA b hL

theorem genericReducedNorm_eval₂ (hA : IsCentralSimple k A) (a : ι → A) (x : ι → L)
    (hL : IsCentralSimple L (BaseChange k L A) := isCentralSimple_baseChange hA) :
    MvPolynomial.eval₂ (algebraMap k L) x (genericReducedNorm hA a) =
      reducedNorm hL (∑ i, x i • (1 ⊗ₜ[k] a i)) := by
  rw [MvPolynomial.eval₂_eq_eval_map, ← genericReducedNorm_baseChange hA a hL,
    genericReducedNorm_eval]

theorem reducedNorm_baseChange (hA : IsCentralSimple k A) (a : A)
    (hL : IsCentralSimple L (BaseChange k L A) := isCentralSimple_baseChange hA) :
    reducedNorm hL (1 ⊗ₜ[k] a) = algebraMap k L (reducedNorm hA a) := by
  rw [reducedNorm, reducedCharpoly_baseChange hA a hL, degree_baseChange_eq hA, reducedNorm,
    ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]
  simp

theorem reducedNorm_mul (hA : IsCentralSimple k A) (a b : A) :
    reducedNorm hA (a * b) = reducedNorm hA a * reducedNorm hA b := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
  apply (algebraMap k (AlgebraicClosure k)).injective
  rw [map_mul, reducedNorm_map hA (a * b) e, reducedNorm_map hA a e, reducedNorm_map hA b e,
    ← Matrix.det_mul, ← map_mul, tmul_mul_tmul, one_mul]

theorem reducedNorm_ne_zero_iff_isUnit (hA : IsCentralSimple k A) (a : A) :
    reducedNorm hA a ≠ 0 ↔ IsUnit a := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
  let f : A →ₐ[k] Matrix (Fin (degree k A)) (Fin (degree k A)) (AlgebraicClosure k) :=
    (e.toAlgHom.restrictScalars k).comp includeRight
  have hdet : algebraMap k (AlgebraicClosure k) (reducedNorm hA a) = (f a).det :=
    reducedNorm_map hA a e
  rw [← (algebraMap k (AlgebraicClosure k)).injective.ne_iff, map_zero, hdet,
    ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
  refine ⟨fun ha => ?_, fun ha => ha.map f⟩
  have hf : Function.Injective f :=
    e.injective.comp (includeRight_injective (algebraMap k (AlgebraicClosure k)).injective)
  have hinj : Function.Injective (LinearMap.mulLeft k a) := by
    intro x y h
    change a * x = a * y at h
    apply hf
    apply ha.mul_right_injective
    simpa only [← map_mul] using congrArg f h
  let : FiniteDimensional k A := hA.2.2
  exact IsUnit.isUnit_iff_mulLeft_bijective.mpr
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

end RM03.CSA
