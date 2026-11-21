import MathGenome.Internal.Specs.D07.Ch19.ResultantDefinition

/-!
Independent specification of K07.19.resultant_bezout,
paper.tex:5399–5423, with the commutative-ring adjugate support supplied
by the separately allocated `support.commutative_ring_adjugate`.

The resultant is the fixed-bound, descending-row determinant from the
upstream specification. `degree : WithBot ℕ` gives degree zero equal to
bottom. In particular, a strict bound of zero forces the multiplier to
be the zero polynomial. No nontriviality, domain, or characteristic
assumption is imposed, and no degree is recomputed after specialization.
-/

universe u v

namespace Specs.D07.Ch19.ResultantBezout

open Polynomial
open Specs.D07.Ch19.ResultantDefinition

/-- The bounded polynomial certificate over any commutative unital ring. -/
def BezoutCertificate : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]) (n m : ℕ),
    f.degree ≤ (n : WithBot ℕ) → g.degree ≤ (m : WithBot ℕ) → 0 < n + m →
    ∃ U V : R[X], U.degree < (m : WithBot ℕ) ∧ V.degree < (n : WithBot ℕ) ∧
      C (fixedResultant f g n m) = U * f + V * g

/-- The exceptional empty matrix has determinant one; no certificate is asserted. -/
def EmptyDeterminant : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]), fixedResultant f g 0 0 = 1

/-- Applying a coefficient homomorphism to an existing certificate preserves
its strict bounds and gives a certificate for the same fixed bounds. -/
def CertificateUnderHomomorphism : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S)
    (f g : R[X]) (n m : ℕ) (U V : R[X]),
    f.degree ≤ (n : WithBot ℕ) → g.degree ≤ (m : WithBot ℕ) →
    U.degree < (m : WithBot ℕ) → V.degree < (n : WithBot ℕ) →
    C (fixedResultant f g n m) = U * f + V * g →
    (U.map φ).degree < (m : WithBot ℕ) ∧ (V.map φ).degree < (n : WithBot ℕ) ∧
      C (fixedResultant (f.map φ) (g.map φ) n m) =
        U.map φ * f.map φ + V.map φ * g.map φ

/-- A common root after any coefficient homomorphism annihilates the image
of the fixed-bound resultant, even if one or both polynomial degrees drop. -/
def NecessaryElimination : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S)
    (f g : R[X]) (n m : ℕ) (x : S),
    f.degree ≤ (n : WithBot ℕ) → g.degree ≤ (m : WithBot ℕ) → 0 < n + m →
    (f.map φ).eval x = 0 → (g.map φ).eval x = 0 →
    φ (fixedResultant f g n m) = 0

end Specs.D07.Ch19.ResultantBezout
