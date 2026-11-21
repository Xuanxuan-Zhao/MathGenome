import MathGenome.Internal.Specs.D07.Ch19.SymmetricFunctions
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
The grading assertion following the fundamental symmetric-polynomial theorem,
paper.tex:5297–5300. Index `i : Fin n` denotes the generator T_{i+1},
so its weight is `i.val + 1`. All assertions concern formal polynomials.
Neither positive n nor a nontrivial coefficient ring is assumed.
-/

universe u

namespace Specs.D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity

open MvPolynomial

/-- Substitution carries the weight-d component to the total-degree-d component. -/
def ComponentCompatibility : Prop :=
  ∀ (R : Type u) [CommRing R] (n d : ℕ) (G : MvPolynomial (Fin n) R),
    aeval (fun i : Fin n => esymm (Fin n) R (i.val + 1))
        (weightedHomogeneousComponent (fun i : Fin n => i.val + 1) d G) =
      homogeneousComponent d
        (aeval (fun i : Fin n => esymm (Fin n) R (i.val + 1)) G)

/-- The substitution preserves and reflects homogeneity with the indicated weights. -/
def HomogeneityEquivalence : Prop :=
  ∀ (R : Type u) [CommRing R] (n d : ℕ) (G : MvPolynomial (Fin n) R),
    (aeval (fun i : Fin n => esymm (Fin n) R (i.val + 1)) G).IsHomogeneous d ↔
      G.IsWeightedHomogeneous (fun i : Fin n => i.val + 1) d

/-- The unique elementary-symmetric expression of a homogeneous symmetric
polynomial is weighted homogeneous. Uniqueness is among all expressions. -/
def UniqueWeightedExpression : Prop :=
  ∀ (R : Type u) [CommRing R] (n d : ℕ) (f : MvPolynomial (Fin n) R),
    f.IsSymmetric → f.IsHomogeneous d →
      ∃ G : MvPolynomial (Fin n) R,
        aeval (fun i : Fin n => esymm (Fin n) R (i.val + 1)) G = f ∧
        G.IsWeightedHomogeneous (fun i : Fin n => i.val + 1) d ∧
        ∀ H : MvPolynomial (Fin n) R,
          aeval (fun i : Fin n => esymm (Fin n) R (i.val + 1)) H = f → H = G

end Specs.D07.Ch19.SymmetricPolynomialTheoremWeightedHomogeneity
