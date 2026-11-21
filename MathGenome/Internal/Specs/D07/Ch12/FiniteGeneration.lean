import MathGenome.Internal.Specs.D07.Ch12.SimpleDegree
import Mathlib.Algebra.BigOperators.Fin

/-!
Independent specification for K07.12.finite_generation, paper.tex:3639–3646.
All fields carry their specified structure map through `Algebra K L`.
Finite degree means that cardinal vector-space dimension is a natural number.
A finite list is represented by `Fin r → L`; repetitions and r = 0 are allowed.
The degree of each algebraic generator is its minimal polynomial's degree over K.
No hypothesis of algebraicity or finite dimension is imposed on the ambient L
in the bound for its generated intermediate field.
-/

universe u v

namespace Specs.D07.Ch12.FiniteGeneration

/-- Both directions of finite extension iff finite algebraic field generation. -/
def FiniteIffFiniteAlgebraicGeneration : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (∃ n : ℕ, Module.rank K L = (n : Cardinal.{v})) ↔
      ∃ (r : ℕ) (α : Fin r → L),
        (∀ i, IsAlgebraic K (α i)) ∧
        IntermediateField.adjoin K (Set.range α) = ⊤

/-- The generated extension has a finite degree bounded by the product of the
individual degrees over K. This also covers generation inside an infinite L/K. -/
def AdjoinDegreeBound : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (r : ℕ) (α : Fin r → L),
    (∀ i, IsAlgebraic K (α i)) →
      ∃ n : ℕ,
        Module.rank K (IntermediateField.adjoin K (Set.range α)) = (n : Cardinal.{v}) ∧
        n ≤ ∏ i, (minpoly K (α i)).natDegree

/-- The source's degree bound when the generators generate all of L. The
existential cardinal equality supplies finiteness before any natural formula. -/
def GeneratedExtensionDegreeBound : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (r : ℕ) (α : Fin r → L),
    (∀ i, IsAlgebraic K (α i)) →
    IntermediateField.adjoin K (Set.range α) = ⊤ →
      ∃ n : ℕ, Module.rank K L = (n : Cardinal.{v}) ∧
        n ≤ ∏ i, (minpoly K (α i)).natDegree

/-- The empty list generates the image of K, of degree one. -/
def EmptyAdjoinDegree : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Module.rank K (IntermediateField.adjoin K (∅ : Set L)) = 1

end Specs.D07.Ch12.FiniteGeneration
