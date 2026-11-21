import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree
import Mathlib.FieldTheory.Galois.Basic

/-! The degree and finite Galois splitting assertions of RM03-C04.05. -/

namespace Specs.RM03.CSA

universe u v w

/-- The degree is positive, its square is the dimension, and a finite Galois
extension splits the algebra into matrices of that size. -/
def GaloisSplitting : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A →
    0 < degree k A ∧ Module.finrank k A = (degree k A) ^ 2 ∧
      ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
        FiniteDimensional k K ∧ IsGalois k K ∧
          Nonempty (baseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K)

/-- For each positive-size matrix presentation, the division algebra contains a
separable splitting subfield of degree `degree k D`. Its normal closure
splits both algebras, with matrix sizes given by their degrees. -/
def GaloisSplittingOfPresentation : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {D : Type w} [DivisionRing D] [Algebra k D] {r : ℕ},
    isCentralSimple k A → isCentralDivision k D → 0 < r →
      (A ≃ₐ[k] Matrix (Fin r) (Fin r) D) →
      degree k A = r * degree k D ∧
        ∃ (E : Subalgebra k D) (hE : IsField E),
          letI := hE.toField
          Algebra.IsSeparable k E ∧ Module.finrank k E = degree k D ∧
            Nonempty (baseChange k E D ≃ₐ[E] Matrix (Fin (degree k D)) (Fin (degree k D)) E) ∧
              ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Algebra E K)
                  (_ : IsScalarTower k E K),
                FiniteDimensional k K ∧ IsGalois k K ∧ IsNormalClosure k E K ∧
                  Nonempty (baseChange k K D ≃ₐ[K] Matrix (Fin (degree k D)) (Fin (degree k D)) K) ∧
                  Nonempty (baseChange k K A ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K)

end Specs.RM03.CSA
