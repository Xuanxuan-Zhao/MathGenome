import MathGenome.Internal.Specs.D07.Ch19.SymmetricPolynomialTheorem
import Mathlib.Algebra.Polynomial.Splits

/-!
Independent specifications for K07.19.symmetric_root_expressions,
paper.tex:5305–5317. An extension is a chosen `Algebra F K` between fields.
The equality of multisets specifies all roots with their multiplicities, in
that one extension. No distinctness, separability, characteristic, or finite
extension hypothesis is imposed. `Fin f.natDegree` includes the empty case.
Membership in the base field means membership in the image of its embedding.
-/

universe u v

noncomputable section

namespace Specs.D07.Ch19.SymmetricRootExpressions

open MvPolynomial

/-- A split monic polynomial admits an enumeration of all its roots, including
repeated roots, of length its degree. -/
def RootEnumerationExists : Prop :=
  ∀ (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (f : Polynomial F), f.Monic → (f.map (algebraMap F K)).Splits →
    ∃ α : Fin f.natDegree → K,
      Finset.univ.val.map α = (f.map (algebraMap F K)).roots

/-- Vieta identifies every elementary symmetric value, including e₀, with
the corresponding signed coefficient of the original polynomial. -/
def ElementaryRootValues : Prop :=
  ∀ (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (f : Polynomial F), f.Monic → (f.map (algebraMap F K)).Splits →
    ∀ α : Fin f.natDegree → K,
      Finset.univ.val.map α = (f.map (algebraMap F K)).roots →
      ∀ j : ℕ, j ≤ f.natDegree →
        aeval α (esymm (Fin f.natDegree) F j) =
          algebraMap F K ((-1) ^ j * f.coeff (f.natDegree - j))

/-- The formal expression G in elementary symmetric polynomials evaluates at
the roots to G evaluated at the signed coefficients, embedded into K. -/
def SymmetricValueFromCoefficients : Prop :=
  ∀ (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (f : Polynomial F), f.Monic → (f.map (algebraMap F K)).Splits →
    ∀ α : Fin f.natDegree → K,
      Finset.univ.val.map α = (f.map (algebraMap F K)).roots →
      ∀ p : MvPolynomial (Fin f.natDegree) F, p.IsSymmetric →
        ∃ G : MvPolynomial (Fin f.natDegree) F,
          aeval (fun i : Fin f.natDegree => esymm (Fin f.natDegree) F (i.val + 1)) G = p ∧
          aeval α p = algebraMap F K
            (eval (fun i : Fin f.natDegree =>
              (-1) ^ (i.val + 1) * f.coeff (f.natDegree - (i.val + 1))) G)

/-- Every symmetric polynomial over F in the entire enumerated root multiset
has its value in the embedded base field. -/
def SymmetricRootValueInBaseField : Prop :=
  ∀ (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (f : Polynomial F), f.Monic → (f.map (algebraMap F K)).Splits →
    ∀ α : Fin f.natDegree → K,
      Finset.univ.val.map α = (f.map (algebraMap F K)).roots →
      ∀ p : MvPolynomial (Fin f.natDegree) F, p.IsSymmetric →
        ∃ c : F, algebraMap F K c = aeval α p

end Specs.D07.Ch19.SymmetricRootExpressions
