import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.MatrixDivision
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SeparableSubfield
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SubfieldSplitting
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.MatrixAlgebra

/-! Finite Galois splitting of central simple algebras. -/

namespace RM03.CSA

universe u v w

/-- Extending scalars on a matrix algebra extends the coefficients entrywise. -/
private def baseChangeMatrix (k K B ι : Type*) [Field k] [Field K] [Algebra k K]
    [Ring B] [Algebra k B] [Fintype ι] [DecidableEq ι] :
    BaseChange k K (Matrix ι ι B) ≃ₐ[K] Matrix ι ι (BaseChange k K B) :=
  Algebra.TensorProduct.congr
    (Matrix.uniqueAlgEquiv (m := PUnit.{1}) (R := K) (A := K)).symm
    (AlgEquiv.refl : Matrix ι ι B ≃ₐ[k] Matrix ι ι B)
  |>.trans (Matrix.kroneckerTMulAlgEquiv PUnit.{1} ι k K K B)
  |>.trans (Matrix.reindexAlgEquiv K _ (Equiv.uniqueProd ι PUnit.{1}))

/-- An algebra equivalence to matrices over one field extends to any larger field. -/
private def extendMatrixSplitting {k E K B : Type*} [Field k] [Field E] [Field K]
    [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
    [Ring B] [Algebra k B] {n : ℕ}
    (e : BaseChange k E B ≃ₐ[E] Matrix (Fin n) (Fin n) E) :
    BaseChange k K B ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
  Algebra.TensorProduct.congr (Algebra.TensorProduct.rid E K K).symm
    (AlgEquiv.refl : B ≃ₐ[k] B)
  |>.trans (Algebra.TensorProduct.assoc k E K K E B)
  |>.trans (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e)
  |>.trans (baseChangeMatrix E K E (Fin n))
  |>.trans (Algebra.TensorProduct.rid E K K).mapMatrix

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

/-- The degree-sized separable subfield of a division factor splits that factor,
and its finite normal closure splits both the factor and the original algebra. -/
theorem galois_splitting_of_presentation {D : Type w} [DivisionRing D] [Algebra k D] {r : ℕ}
    (hA : IsCentralSimple k A) (hD : IsCentralDivision k D) (hr : 0 < r)
    (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) :
    degree k A = r * degree k D ∧
      ∃ (E : Subalgebra k D) (hE : IsField E),
        letI := hE.toField
        Algebra.IsSeparable k E ∧ Module.finrank k E = degree k D ∧
          Nonempty (BaseChange k E D ≃ₐ[E] Matrix (Fin (degree k D)) (Fin (degree k D)) E) ∧
            ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Algebra E K)
                (_ : IsScalarTower k E K),
              FiniteDimensional k K ∧ IsGalois k K ∧ IsNormalClosure k E K ∧
                Nonempty (BaseChange k K D ≃ₐ[K] Matrix (Fin (degree k D)) (Fin (degree k D)) K) ∧
                Nonempty (BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K) := by
  have hd := degree_matrix_division hA hD hr e
  obtain ⟨E, hField, hSep, hDim⟩ := exists_separable_subfield hD
  let : Field E := hField.toField
  let : FiniteDimensional k D := hD.2
  let : FiniteDimensional k E := FiniteDimensional.of_injective E.val.toLinearMap E.val.injective
  let : Algebra.IsSeparable k E := hSep
  obtain ⟨eE⟩ := subfield_splits E.val hD hDim
  let f : E →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let : Algebra E (AlgebraicClosure k) := f.toRingHom.toAlgebra
  let : IsScalarTower k E (AlgebraicClosure k) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let K := IntermediateField.normalClosure k E (AlgebraicClosure k)
  have : Nonempty (E →ₐ[k] AlgebraicClosure k) := ⟨f⟩
  have hClosure : IsNormalClosure k E K :=
    isNormalClosure_normalClosure k E (AlgebraicClosure k)
  let eD : BaseChange k K D ≃ₐ[K] Matrix (Fin (degree k D)) (Fin (degree k D)) K :=
    extendMatrixSplitting eE
  have hSplitA :
      Nonempty (BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K) := by
    rw [hd]
    exact ⟨Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
      |>.trans (baseChangeMatrix k K D (Fin r))
      |>.trans eD.mapMatrix
      |>.trans (Matrix.compAlgEquiv (Fin r) (Fin (degree k D)) K K)
      |>.trans (Matrix.reindexAlgEquiv K K finProdFinEquiv)⟩
  exact ⟨hd, E, hField, hSep, hDim, ⟨eE⟩, K, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hClosure, ⟨eD⟩, hSplitA⟩

/-- A central simple algebra has positive degree, square dimension, and a finite
Galois splitting field. -/
theorem galois_splitting (hA : IsCentralSimple k A) :
    0 < degree k A ∧ Module.finrank k A = (degree k A) ^ 2 ∧
      ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
        FiniteDimensional k K ∧ IsGalois k K ∧
          Nonempty (BaseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K) := by
  obtain ⟨r, D, _, _, hD, hr, ⟨e⟩⟩ := MatrixDivision.exists_presentation k A hA
  obtain ⟨_, _, _, _, _, _, K, hK, hAlg, _, _, hFin, hGal, _, _, hSplit⟩ :=
    galois_splitting_of_presentation hA hD hr e
  exact ⟨degree_pos hA, finrank_eq_degree_sq hA, K, hK, hAlg, hFin, hGal, hSplit⟩

end RM03.CSA
