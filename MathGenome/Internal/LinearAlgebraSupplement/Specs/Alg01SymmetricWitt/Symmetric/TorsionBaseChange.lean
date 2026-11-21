import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Polynomial
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Flat.Basic

namespace Specs.Alg01SymmetricWitt.Symmetric.TorsionBaseChange

open scoped _root_.Polynomial TensorProduct
open Module
open Specs.Alg01SymmetricWitt.Symmetric.Algebra (degree)
open Specs.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra (comparisonHom)
open Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree (baseChangedDegree)
open Specs.Alg01SymmetricWitt.Symmetric.Polynomial (equivMvPolynomial)
open Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation
  (PolynomialQuotient quotientMap quotientDegree)

abbrev ResidueField := ZMod 2
abbrev ExtendedModule := ResidueField ⊗[ℤ] ZMod 2
abbrev ExtendedAlgebra := ResidueField ⊗[ℤ] SymmetricAlgebra ℤ (ZMod 2)

/-- The usual degree-`n` component of the univariate polynomial ring over the residue field. -/
noncomputable def residuePolynomialDegree (n : ℕ) : Submodule ResidueField ResidueField[X] :=
  LinearMap.range (Polynomial.monomial n : ResidueField →ₗ[ResidueField] ResidueField[X])

/-- The integral presentation, with its grading and the coefficient modules of every degree. -/
def integralPresentation : Prop :=
  TorsionPresentation.presentation ∧ TorsionPresentation.quotientGrading ∧
    TorsionPresentation.degreeZero ∧ TorsionPresentation.degreePositive

/-- The extended integral presentation commutes with the polynomial equivalence,
and the map from the quotient is coefficient reduction modulo two. -/
def quotientScalarExtension (e : ExtendedAlgebra ≃ₐ[ResidueField] ResidueField[X]) : Prop :=
  ∃ (p : SymmetricAlgebra ℤ (ZMod 2) ≃ₐ[ℤ] PolynomialQuotient)
    (q : (ResidueField ⊗[ℤ] PolynomialQuotient) ≃ₐ[ResidueField] ResidueField[X]),
    p (SymmetricAlgebra.ι ℤ (ZMod 2) 1) = quotientMap Polynomial.X ∧
    (∀ n : ℕ, (degree ℤ (ZMod 2) n).map p.toLinearMap = quotientDegree n) ∧
    (∀ (s : ResidueField) (x : SymmetricAlgebra ℤ (ZMod 2)),
      q (s ⊗ₜ[ℤ] p x) = e (s ⊗ₜ[ℤ] x)) ∧
    (∀ (s : ResidueField) (f : ℤ[X]),
      q (s ⊗ₜ[ℤ] quotientMap f) = s • f.map (Int.castRingHom ResidueField)) ∧
    ∀ n : ℕ,
      ((quotientDegree n).baseChange ResidueField).map q.toLinearMap =
        residuePolynomialDegree n

/-- The extended algebra is a graded polynomial algebra in the basis generator
`1 ⊗ 1` of the extended cyclic module. The identification uses the canonical comparison. -/
def scalarExtension : Prop :=
  ∃ (b : Basis (Fin 1) ResidueField ExtendedModule)
    (e : ExtendedAlgebra ≃ₐ[ResidueField] ResidueField[X]),
    b 0 = 1 ⊗ₜ[ℤ] (1 : ZMod 2) ∧
    e (1 ⊗ₜ[ℤ] SymmetricAlgebra.ι ℤ (ZMod 2) 1) = Polynomial.X ∧
    e.toAlgHom =
      ((MvPolynomial.uniqueAlgEquiv ResidueField (Fin 1)).toAlgHom.comp
        (equivMvPolynomial b).toAlgHom).comp (comparisonHom ℤ ResidueField (ZMod 2)) ∧
    (∀ n : ℕ,
      (baseChangedDegree ℤ ResidueField (ZMod 2) n).map e.toLinearMap =
        residuePolynomialDegree n) ∧
    quotientScalarExtension e

/-- Tensoring multiplication by two with the residue field sends an injection to zero
on a nonzero module. -/
def nonflatness : Prop :=
  let mulTwo : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id
  Function.Injective mulTwo ∧
    mulTwo.baseChange ResidueField = 0 ∧
    (1 ⊗ₜ[ℤ] (1 : ℤ) : ResidueField ⊗[ℤ] ℤ) ≠ 0 ∧
    ¬ Module.Flat ℤ ResidueField

end Specs.Alg01SymmetricWitt.Symmetric.TorsionBaseChange
