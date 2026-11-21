import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Resolution
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Polynomial calculation in RK-13, paper.tex:2495–2502.
The variables are ordered by `Fin r`, and coefficients use evaluation at zero.
No domain, field, or Noetherian hypothesis is imposed on A. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
namespace AdvCommAlg.Koszul.PolynomialExample

abbrev PolynomialRing (A : Type u) [CommRing A] (r : ℕ) := MvPolynomial (Fin r) A

def variableList (A : Type u) [CommRing A] (r : ℕ) : List (PolynomialRing A r) :=
  List.ofFn MvPolynomial.X

@[simp] theorem variableList_length (A : Type u) [CommRing A] (r : ℕ) :
    (variableList A r).length = r := List.length_ofFn

def prefixIdeal (A : Type u) [CommRing A] (r j : ℕ) : Ideal (PolynomialRing A r) :=
  Ideal.ofList ((variableList A r).take j)

/-- Restrict scalars to the polynomial ring by setting every variable to zero. -/
abbrev evaluationAlgebra (A : Type u) [CommRing A] (r : ℕ) : Algebra (PolynomialRing A r) A :=
  (MvPolynomial.eval (fun _ => (0 : A))).toAlgebra

end AdvCommAlg.Koszul.PolynomialExample

namespace Specs.AdvCommAlg.Koszul.PolynomialExample
open _root_.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul.PolynomialExample

def variableListRegular : Prop :=
  ∀ (A : Type u) [CommRing A] [Nontrivial A] (r : ℕ),
    RingTheory.Sequence.IsRegular (PolynomialRing A r) (variableList A r)

def successiveQuotients : Prop :=
  ∀ (A : Type u) [CommRing A] [Nontrivial A] (r j : ℕ), j ≤ r →
    Nonempty ((PolynomialRing A r ⧸ prefixIdeal A r j) ≃ₐ[A]
      MvPolynomial {i : Fin r // j ≤ i.val} A)

/-- The target is A with the specified evaluation action; the augmentation is evaluation. -/
def resolvesCoefficients : Prop :=
  ∀ (A : Type u) [CommRing A] [Nontrivial A] (r : ℕ),
    letI := evaluationAlgebra A r
    ∃ π : listComplex (variableList A r) ⟶
        (ChainComplex.single₀ (ModuleCat (PolynomialRing A r))).obj (ModuleCat.of _ A),
      (∀ z, π.f 0 z = MvPolynomial.eval (fun _ => 0)
        (exteriorPower.zeroEquiv (PolynomialRing A r) _ z)) ∧
      QuasiIso π ∧
      (∀ q : ℕ, Module.Free (PolynomialRing A r) ((listComplex (variableList A r)).X q) ∧
        Module.Finite (PolynomialRing A r) ((listComplex (variableList A r)).X q)) ∧
      (∀ q : ℕ, r < q → IsZero ((listComplex (variableList A r)).X q))

/-- A acts on Koszul homology by restriction along the constant-polynomial map. -/
def coefficientHomology : Prop :=
  ∀ (A : Type u) [CommRing A] [Nontrivial A] (r q : ℕ),
    letI := evaluationAlgebra A r
    letI : Module A (homology A (variableList A r) q) :=
      Module.compHom _ (MvPolynomial.C : A →+* PolynomialRing A r)
    Nonempty (homology A (variableList A r) q ≃ₗ[A] (⋀[A]^q (Fin r → A)))

end Specs.AdvCommAlg.Koszul.PolynomialExample
