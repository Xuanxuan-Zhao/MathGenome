import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
Statements for K07.11.content_primitive, paper.tex:2498–2521.
Contents are gcds in the divisibility sense, with arbitrary associates allowed.
A normalization is chosen internally solely to give one content function; it is
not an extra hypothesis on the UFD. `Polynomial.IsPrimitive` means that every
common coefficient divisor is a unit. Its nonvanishing is proved below.
`emultiplicity` takes values in ℕ∞, so zero coefficients have exponent infinity.
-/

universe u
namespace Specs.D07.Ch11.ContentPrimitive

open Polynomial

/-- The universal property of a gcd of all coefficients (only finitely many
are nonzero). This definition does not choose a normalization. -/
def IsContent {R : Type u} [CommRing R] (f : R[X]) (c : R) : Prop :=
  (∀ n : ℕ, c ∣ f.coeff n) ∧
    ∀ d : R, (∀ n : ℕ, d ∣ f.coeff n) → d ∣ c

/-- An internal choice, available for every UFD, not an additional instance
required of the coefficient ring. -/
@[instance_reducible]
noncomputable def contentStructure (R : Type u) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] : NormalizedGCDMonoid R :=
  Classical.choice inferInstance

/-- One representative of content. All theorems about arbitrary choices use
`IsContent`, rather than imposing this representative. -/
noncomputable def content {R : Type u} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (f : R[X]) : R :=
  letI := contentStructure R
  f.content

def ContentIsGcd : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : R[X]), IsContent f (content f)

def ContentZero : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R],
    content (0 : R[X]) = 0

def ContentEqZero : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : R[X]) (c : R), IsContent f c → (c = 0 ↔ f = 0)

def ContentUnique : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : R[X]) (c d : R), IsContent f c → IsContent f d → Associated c d

def ContentAssociateChoice : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : R[X]) (c : R), IsContent f c ↔ Associated c (content f)

def PrimitiveIffUnitContent : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : R[X]) (c : R), IsContent f c →
      (f.IsPrimitive ↔ f ≠ 0 ∧ IsUnit c)

/-- The nonzero hypothesis is essential: over a field there are no prime
elements, but the zero polynomial is still not primitive. -/
def PrimitiveIffNoCommonPrime : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : R[X]), f ≠ 0 →
      (f.IsPrimitive ↔ ∀ p : R, Prime p → ¬∀ n : ℕ, p ∣ f.coeff n)

def ZeroNotPrimitive : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R],
    ¬(0 : R[X]).IsPrimitive

/-- Existence works for every associate chosen as content; a fixed nonzero
content gives a unique quotient. No primitive part of zero is specified. -/
def PrimitivePartExists : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : R[X]) (c : R), f ≠ 0 → IsContent f c →
      ∃! g : R[X], f = C c * g ∧ g.IsPrimitive

def PrimitivePartCoefficients : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f g : R[X]) (c : R), f = C c * g →
      ∀ n : ℕ, f.coeff n = c * g.coeff n

/-- Exact change under replacing the content c by c*u. -/
def PrimitivePartUnitChange : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f g h : R[X]) (c : R) (v : Rˣ), f ≠ 0 →
      f = C c * g → f = C (c * (v : R)) * h → g = C (v : R) * h

def MonicPrimitive : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : R[X]), f.Monic → f.IsPrimitive

/-- For nonzero elements, the exponent is a finite natural number, counting
prime factors. Zero has exponent infinity. -/
def ValuationBoundary : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (p : R), Prime p → emultiplicity p (0 : R) = ⊤ ∧
      ∀ a : R, a ≠ 0 → ∃ k : ℕ, emultiplicity p a = k ∧
        p ^ k ∣ a ∧ ¬p ^ (k + 1) ∣ a

/-- The minimum is over the finite support; outside it the exponents are
infinity, so omitting those coefficients does not change the minimum. -/
def ContentValuation : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : R[X]) (c p : R), IsContent f c → Prime p →
      emultiplicity p c = f.support.inf (fun n => emultiplicity p (f.coeff n))

/-- Dividing by content subtracts its exponent from every coefficient;
for each prime the remaining finite minimum is zero. -/
def PrimitivePartValuations : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f g : R[X]) (c p : R), f ≠ 0 → IsContent f c → Prime p →
      f = C c * g →
      (∀ n : ℕ, emultiplicity p (g.coeff n) =
        emultiplicity p (f.coeff n) - emultiplicity p c) ∧
      g.support.inf (fun n => emultiplicity p (g.coeff n)) = 0

end Specs.D07.Ch11.ContentPrimitive
