import MathGenome.Internal.Specs.D05.M06.SumDimension
import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.D05.M02.Dimension
import MathGenome.Internal.D05.M06.ExternalSum
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! K05.06.sum_dimension: concatenated bases and dimensions of finite direct sums. -/

namespace D05.M06.SumDimension

/-- The direct-sum basis consists of the injected chosen basis vectors. -/
theorem external_basis : Specs.D05.M06.SumDimension.external_basis := by
  intro K ι M κ _ _ _ b
  classical
  refine ⟨DFinsupp.basis b, ?_⟩
  intro i j
  apply Module.Basis.apply_eq_iff.mpr
  change sigmaFinsuppEquivDFinsupp.symm
    (DFinsupp.mapRange (fun i x => (b i).repr x) (fun i => map_zero _)
      (DFinsupp.single i (b i j))) = Finsupp.single ⟨i, j⟩ 1
  apply sigmaFinsuppEquivDFinsupp.injective
  simp

/-- Use the proved bridge to the canonical internal-sum predicate. Its collected
basis has exactly the inclusion values; no dimension assumption is needed. -/
theorem internal_basis : Specs.D05.M06.SumDimension.internal_basis := by
  intro K V ι κ _ _ _ _ U h b
  classical
  have hi := (D05.M06.DirectSum.internal_iff_mathlib U).mp h
  exact ⟨hi.collectedBasis b, fun i j => by simp⟩

theorem external_finiteDimensional :
    Specs.D05.M06.SumDimension.external_finiteDimensional := by
  intro K ι M _ _ _ _ _
  exact (Specs.D05.M06.ExternalSum.finiteProductMap K ι M).symm.finiteDimensional

/-- The forward map of this isomorphism is the actual summation map, as supplied
by the upstream external/internal comparison. -/
theorem internal_finiteDimensional :
    Specs.D05.M06.SumDimension.internal_finiteDimensional := by
  intro K V ι _ _ _ _ U _ h
  obtain ⟨e, _⟩ := (D05.M06.ExternalSum.isomorphism_iff_internal U).mpr h
  let _ := external_finiteDimensional (K := K) (M := fun i => U i)
  exact e.finiteDimensional

theorem external_dimension : Specs.D05.M06.SumDimension.external_dimension := by
  intro K ι M _ _ _ _ _
  exact Module.finrank_directSum K M

theorem internal_dimension : Specs.D05.M06.SumDimension.internal_dimension := by
  intro K V ι _ _ _ _ U _ h
  obtain ⟨e, _⟩ := (D05.M06.ExternalSum.isomorphism_iff_internal U).mpr h
  exact e.finrank_eq.symm.trans (external_dimension (K := K) (M := fun i => U i))

theorem empty_external_dimension :
    Specs.D05.M06.SumDimension.empty_external_dimension := by
  intro K ι M _ _ _ _ _
  let _ : ∀ i, FiniteDimensional K (M i) := fun i => isEmptyElim i
  exact ⟨by simp, by simp⟩

theorem empty_internal_dimension :
    Specs.D05.M06.SumDimension.empty_internal_dimension := by
  intro K V ι _ _ _ _ _ U h
  let _ : ∀ i, FiniteDimensional K (U i) := fun i => isEmptyElim i
  exact ⟨by simpa using (internal_dimension U h), by simp⟩

end D05.M06.SumDimension
