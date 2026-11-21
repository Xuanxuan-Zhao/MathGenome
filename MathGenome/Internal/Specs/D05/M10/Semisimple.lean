import MathGenome.Internal.Specs.D05.M06.Invariant
import MathGenome.Internal.Specs.D05.M08.Minpoly
import MathGenome.Internal.Specs.D05.M09.MinpolyCriterion
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.Algebra.Polynomial.Splits

/-!
Independent statements for K05.10.semisimple, paper.tex:1567–1577.
Semisimplicity means invariant complements over the original field. Neither
splitting, perfection nor characteristic zero is required for the main criterion.
The minimal polynomial and eigenbasis predicate are the upstream objects.
The scalar-extension and characteristic-zero separability statements of line
1577 are specified separately in `Specs.D05.M10.Semisimple.ScalarExtension`.
-/

namespace Specs.D05.M10.Semisimple

universe u v

def semisimple_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → Module.End K V → Prop

/-- Every invariant subspace has an invariant internal direct-sum complement.
`IsCompl` asserts both trivial intersection and sum equal to the whole space. -/
def semisimple_value : semisimple_type.{u, v} :=
  fun K V _ _ _ T => ∀ U : Submodule K V,
    M06.Invariant.invariant_value K V U T →
    ∃ W : Submodule K V, M06.Invariant.invariant_value K V W T ∧ IsCompl U W

/-- Invariance under `T` is precisely stability under polynomial evaluation. -/
def invariant_iff_polynomial_stable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (U : Submodule K V),
    M06.Invariant.invariant_value K V U T ↔
      ∀ (p : Polynomial K) (v : V), v ∈ U → Polynomial.aeval T p v ∈ U

/-- The module action here is `p • v = p(T)v`, not an arbitrary module action. -/
def semisimple_iff_module : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V),
    semisimple_value K V T ↔ IsSemisimpleModule (Polynomial K) (Module.AEval' T)

/-- The main theorem, with squarefree in the factorization sense. -/
def semisimple_iff_squarefree : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    semisimple_value K V T ↔ Squarefree (M08.Minpoly.minimalPolynomial_value K V T)

/-- Explicitly exclude repeated irreducible factors; this does not assert
separability or splitting of those factors in any extension field. -/
def semisimple_iff_no_repeated_irreducible : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    semisimple_value K V T ↔
      ∀ p : Polynomial K, Irreducible p →
        ¬ p * p ∣ M08.Minpoly.minimalPolynomial_value K V T

/-- A finite set of monic irreducibles expresses distinctness literally.
The empty product is allowed and is the minimal polynomial of the zero space. -/
def semisimple_iff_distinct_irreducible_factors : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    semisimple_value K V T ↔
      ∃ s : Finset (Polynomial K), (∀ p ∈ s, p.Monic ∧ Irreducible p) ∧
        M08.Minpoly.minimalPolynomial_value K V T = ∏ p ∈ s, p

/-- Diagonalizability also requires splitting over the named base field. -/
def diagonalizable_iff_semisimple_and_splits : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    M09.Diagonalizable.diagonalizable_value K V T ↔
      semisimple_value K V T ∧ (M08.Minpoly.minimalPolynomial_value K V T).Splits

/-- No positive-dimensional hypothesis is hidden in the main criterion. -/
def zero_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Subsingleton V] (T : Module.End K V),
    semisimple_value K V T ∧ M08.Minpoly.minimalPolynomial_value K V T = 1

end Specs.D05.M10.Semisimple
