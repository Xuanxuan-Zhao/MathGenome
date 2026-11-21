import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra
import Mathlib.RingTheory.GradedAlgebra.TensorProduct

namespace Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree

open scoped DirectSum TensorProduct
open Specs.Alg01SymmetricWitt.Symmetric.Algebra (degree pureProduct)
open Specs.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra (comparisonHom)

universe u v w

section

variable (R : Type u) (S : Type v) (M : Type w)
  [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]

/-- The scalar extension of a symmetric degree, inside the scalar-extended algebra. -/
abbrev baseChangedDegree (n : ℕ) : Submodule S (S ⊗[R] SymmetricAlgebra R M) :=
  (degree R M n).baseChange S

end

set_option linter.checkUnivs false in
def baseChangedDegreeType :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] (_ : ℕ),
    Submodule S (S ⊗[R] SymmetricAlgebra R M)

/-- Tensoring the inclusion identifies the scalar extension of each degree with its image. -/
def summandIdentification : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] (n : ℕ),
    ∃ e : S ⊗[R] degree R M n ≃ₗ[S] baseChangedDegree R S M n,
      e.toLinearMap = (degree R M n).toBaseChange S

/-- The extended degrees form an internal graded algebra. Their decomposition agrees with
the direct sum of the tensor products of the original degrees. -/
def scalarExtensionGrading : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    ∃ g : GradedAlgebra (baseChangedDegree R S M),
      letI := g
      ∃ d : S ⊗[R] SymmetricAlgebra R M ≃ₗ[S] (⨁ n, S ⊗[R] degree R M n),
        (∀ z, DirectSum.lmap (fun n ↦ (degree R M n).toBaseChange S) (d z) =
          DirectSum.decompose (baseChangedDegree R S M) z) ∧
        ∀ (n : ℕ) (s : S) (x : degree R M n),
          d (s ⊗ₜ[R] (x : SymmetricAlgebra R M)) =
            DirectSum.of (fun n ↦ S ⊗[R] degree R M n) n (s ⊗ₜ[R] x)

/-- The canonical comparison and its inverse carry each homogeneous degree into that degree. -/
def gradedComparison : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M],
    ∃ e : S ⊗[R] SymmetricAlgebra R M ≃ₐ[S] SymmetricAlgebra S (S ⊗[R] M),
      e.toAlgHom = comparisonHom R S M ∧
      ∀ n : ℕ,
        Set.MapsTo e (baseChangedDegree R S M n) (degree S (S ⊗[R] M) n) ∧
        Set.MapsTo e.symm (degree S (S ⊗[R] M) n) (baseChangedDegree R S M n)

/-- Each degreewise comparison commutes with the canonical inclusions into the two
algebras. Its values on the pure classes determine it as a linear map. -/
def degreeComparison : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] (n : ℕ),
    ∃ e : S ⊗[R] degree R M n ≃ₗ[S] degree S (S ⊗[R] M) n,
      (∀ z, (e z : SymmetricAlgebra S (S ⊗[R] M)) =
        comparisonHom R S M ((degree R M n).subtype.baseChange S z)) ∧
      (∀ (s : S) (x : Fin n → M),
        e (s ⊗ₜ[R] pureProduct R M n x) =
          s • pureProduct S (S ⊗[R] M) n (fun i ↦ 1 ⊗ₜ[R] x i)) ∧
      ∀ f : (S ⊗[R] degree R M n) →ₗ[S] degree S (S ⊗[R] M) n,
        (∀ (s : S) (x : Fin n → M),
          f (s ⊗ₜ[R] pureProduct R M n x) =
            s • pureProduct S (S ⊗[R] M) n (fun i ↦ 1 ⊗ₜ[R] x i)) →
        f = e.toLinearMap

end Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree
