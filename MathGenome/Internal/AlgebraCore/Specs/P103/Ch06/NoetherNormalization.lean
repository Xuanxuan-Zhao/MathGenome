import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
Independent statements of Noether normalization, Theorem 6.5
(`paper.tex:1082–1086`). The field is arbitrary and the algebra is only
assumed commutative, nonzero, and of finite type. In particular it need
not be reduced or a domain. The natural number of variables may be zero.
`ringKrullDim` uses the source's supremum of strict prime-chain lengths.
`AlgHom.Finite` means finite as a module via the displayed map.
-/
namespace P103.Specs.Ch06.NoetherNormalization

universe u v

def normalization_mapType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A],
    ∃ (d : ℕ) (g : MvPolynomial (Fin d) k →ₐ[k] A),
      Function.Injective g ∧ g.Finite ∧ ringKrullDim A = (d : WithBot ℕ∞)

/-- The original formulation using elements and their generated subalgebra. -/
def normalization_elementsType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A],
    ∃ (d : ℕ) (y : Fin d → A),
      AlgebraicIndependent k y ∧
      Module.Finite (Algebra.adjoin k (Set.range y)) A ∧
      ringKrullDim A = (d : WithBot ℕ∞)

end P103.Specs.Ch06.NoetherNormalization
