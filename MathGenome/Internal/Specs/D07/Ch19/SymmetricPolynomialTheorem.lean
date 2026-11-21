import MathGenome.Internal.Specs.D07.Ch19.SymmetricFunctions
import MathGenome.Internal.Specs.D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity

/-!
Specifications for K07.19.symmetric_polynomial_theorem, paper.tex:5254–5305.
Both polynomial rings have `n` formal variables; index `i : Fin n` denotes
the source's variable T_{i+1} or X_{i+1}. Substitution sends T_{i+1} to e_{i+1}.
The coefficient ring may be the zero ring and `n` may be zero. Symmetry is
invariance under variable permutations, using the canonical symmetric subalgebra.
The grading conclusions use the independently specified upstream grading result.
-/

universe u

namespace Specs.D07.Ch19.SymmetricPolynomialTheorem

open MvPolynomial

/-- Existence and uniqueness among all formal expressions in the n generators. -/
def UniqueExpression : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (f : MvPolynomial (Fin n) R),
    f.IsSymmetric →
      ∃! G : MvPolynomial (Fin n) R,
        aeval (fun i : Fin n => esymm (Fin n) R (i.val + 1)) G = f

/-- The isomorphism onto the fixed subring is specifically elementary-symmetric
substitution, not merely an abstract isomorphism of the two rings. -/
def SubstitutionIsomorphism : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    ∃ e : MvPolynomial (Fin n) R ≃ₐ[R] symmetricSubalgebra (Fin n) R,
      ∀ G : MvPolynomial (Fin n) R,
        (e G).val = aeval (fun i : Fin n => esymm (Fin n) R (i.val + 1)) G

/-- The degree-d weighted component substitutes to the total-degree-d component. -/
def ComponentCompatibility : Prop :=
  Specs.D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity.ComponentCompatibility.{u}

/-- Substitution preserves and reflects homogeneity, with weight(T_j) = j. -/
def HomogeneityEquivalence : Prop :=
  Specs.D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity.HomogeneityEquivalence.{u}

/-- The unique expression of a homogeneous symmetric polynomial has its weighted
degree. Uniqueness here is still among all formal expressions. -/
def UniqueWeightedExpression : Prop :=
  Specs.D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity.UniqueWeightedExpression.{u}

end Specs.D07.Ch19.SymmetricPolynomialTheorem
