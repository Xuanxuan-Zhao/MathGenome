import MathGenome.Internal.Specs.D07.Ch11.QuotientNormalForm

/-!
Independent statements for K07.13.coordinates_arithmetic (paper.tex:4025–4038).
The base is an arbitrary finite field of cardinality q; thus no particular
model of the q-element field or unchosen identification with a closure is used.
`AdjoinRoot f` is the canonical ideal quotient K[X]/(f), with its canonical
ring and K-algebra structures. Bottom-valued degree includes the zero normal
form. Inversion is specified by the two inverse equations and uniqueness,
without choosing an additional field structure on the quotient.
-/

universe u
namespace Specs.D07.Ch13.CoordinatesArithmetic
open Polynomial

/-- The quotient is a field with q^n elements (and is actually finite). -/
def FieldCardinality : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (q n : ℕ) (f : K[X]),
    Nat.card K = q → f.natDegree = n → f.Monic → Irreducible f →
    IsField (AdjoinRoot f) ∧ Finite (AdjoinRoot f) ∧ Nat.card (AdjoinRoot f) = q ^ n

/-- Coordinates are arbitrary n-tuples of base elements, interpreted as the
class of the polynomial with those coefficients. -/
def CoordinateBijection : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (f : K[X]),
    f.natDegree = n → f.Monic → Irreducible f →
    ∃ e : (Fin n → K) ≃ AdjoinRoot f,
      ∀ a, e a = AdjoinRoot.mk f (∑ i : Fin n, C (a i) * X ^ (i : ℕ))

/-- Every residue has exactly one representative of degree less than n. -/
def UniqueNormalForm : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (f : K[X]),
    f.natDegree = n → f.Monic → Irreducible f → ∀ x : AdjoinRoot f,
    ∃! g : K[X], g.degree < (n : WithBot ℕ) ∧ AdjoinRoot.mk f g = x

/-- Addition and multiplication are the polynomial operations followed by
Euclidean remainder; the resulting representatives have the required degree. -/
def RemainderArithmetic : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (f : K[X]),
    f.natDegree = n → f.Monic → Irreducible f → ∀ g h : K[X],
      (((g + h) % f).degree < (n : WithBot ℕ) ∧
        AdjoinRoot.mk f ((g + h) % f) = AdjoinRoot.mk f g + AdjoinRoot.mk f h) ∧
      (((g * h) % f).degree < (n : WithBot ℕ) ∧
        AdjoinRoot.mk f ((g * h) % f) = AdjoinRoot.mk f g * AdjoinRoot.mk f h)

/-- Different representatives of the same inputs give identical reduced outputs. -/
def RepresentativeIndependence : Prop :=
  ∀ (K : Type u) [Field K] (f : K[X]), f.Monic → Irreducible f →
    ∀ g g' h h' : K[X],
      AdjoinRoot.mk f g = AdjoinRoot.mk f g' →
      AdjoinRoot.mk f h = AdjoinRoot.mk f h' →
      (g + h) % f = (g' + h') % f ∧ (g * h) % f = (g' * h') % f

/-- Nonzero refers to the residue, rather than merely to its representative.
The coefficients in a Bézout equation exist for every such residue. -/
def NonzeroResidueBezout : Prop :=
  ∀ (K : Type u) [Field K] (f : K[X]), f.Monic → Irreducible f →
    ∀ g : K[X], AdjoinRoot.mk f g ≠ 0 →
      ∃ u v : K[X], u * f + v * g = 1

/-- Any Bézout equation computes the unique two-sided inverse as the class of v. -/
def InverseFromBezout : Prop :=
  ∀ (K : Type u) [Field K] (f g u v : K[X]), u * f + v * g = 1 →
    AdjoinRoot.mk f v * AdjoinRoot.mk f g = 1 ∧
    AdjoinRoot.mk f g * AdjoinRoot.mk f v = 1 ∧
    ∀ w : AdjoinRoot f, AdjoinRoot.mk f g * w = 1 ↔ w = AdjoinRoot.mk f v

end Specs.D07.Ch13.CoordinatesArithmetic
