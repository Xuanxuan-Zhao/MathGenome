import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! The linear algebra used in A14, over the original perfect field. -/

open scoped TensorProduct

namespace LinearAlgebraicGroups.Affine

open Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A multiplicative Jordan decomposition into commuting invertible endomorphisms. -/
structure IsMultiplicativeJordanDecomposition (f s u : End k V) : Prop where
  eq_mul : f = s * u
  commute : Commute s u
  semisimple : s.IsSemisimple
  unipotent : IsNilpotent (u - 1)
  isUnit_semisimple : IsUnit s
  isUnit_unipotent : IsUnit u

/-- The scalar extension to the algebraic closure has a basis of eigenvectors. -/
def GeometricallyDiagonalizable [FiniteDimensional k V] (f : End k V) : Prop :=
  let K := AlgebraicClosure k
  let Vₖ := K ⊗[k] V
  ∃ (b : Basis (Fin (finrank K Vₖ)) K Vₖ) (eigenvalue : Fin (finrank K Vₖ) → K),
    ∀ i, f.baseChange K (b i) = eigenvalue i • b i

namespace JordanFactorsSpec

def existenceAndUniqueness : Prop :=
  ∀ {k V : Type*} [Field k] [PerfectField k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : End k V), IsUnit f →
    ∃! p : End k V × End k V, IsMultiplicativeJordanDecomposition f p.1 p.2

def intertwining : Prop :=
  ∀ {k V W : Type*} [Field k] [PerfectField k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {f s u : End k V} {g t v : End k W} (h : V →ₗ[k] W),
    IsMultiplicativeJordanDecomposition f s u →
    IsMultiplicativeJordanDecomposition g t v →
    h.comp f = g.comp h →
    h.comp s = t.comp h ∧ h.comp u = v.comp h

def tensorCompatibility : Prop :=
  ∀ {k V W : Type*} [Field k] [PerfectField k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {f s u : End k V} {g t v : End k W},
    IsMultiplicativeJordanDecomposition f s u →
    IsMultiplicativeJordanDecomposition g t v →
    IsMultiplicativeJordanDecomposition (TensorProduct.map f g)
      (TensorProduct.map s t) (TensorProduct.map u v)

def semisimpleGeometric : Prop :=
  ∀ {k V : Type*} [Field k] [PerfectField k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : End k V), f.IsSemisimple ↔ GeometricallyDiagonalizable f

open Polynomial in
/-- Over the algebraic closure the characteristic polynomial is a pure power of X - 1. -/
def unipotentGeometric : Prop :=
  ∀ {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : End k V),
    IsNilpotent (f - 1) ↔
      (f.baseChange (AlgebraicClosure k)).charpoly =
        (X - 1) ^ finrank (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] V)

end JordanFactorsSpec
end LinearAlgebraicGroups.Affine
