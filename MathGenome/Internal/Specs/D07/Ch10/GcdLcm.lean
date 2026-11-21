import MathGenome.Internal.Specs.D07.Ch10.Associates

/-!
Independent specifications for K07.10.gcd_lcm, paper.tex:1833–1841.
All general statements concern a commutative nontrivial domain. The predicates
use only divisibility, with no numerical ordering, chosen gcd operation, or
assumption that gcds exist. The zero cases are included. The final proposition
records the source's warning that universal gcd existence fails for domains.
-/

universe u

namespace Specs.D07.Ch10.GcdLcm

/-- Type of the source's three-place predicate (inputs first, candidate last). -/
def DivisorPredicateType : Type (u + 1) :=
  ∀ (R : Type u) [CommRing R] [IsDomain R], R → R → R → Prop

/-- A greatest common divisor, where "greatest" means divisibility. -/
def IsGcd : DivisorPredicateType.{u} :=
  fun R _ _ a b d => d ∣ a ∧ d ∣ b ∧ ∀ c : R, c ∣ a → c ∣ b → c ∣ d

/-- A least common multiple, where "least" means divisibility. -/
def IsLcm : DivisorPredicateType.{u} :=
  fun R _ _ a b m => a ∣ m ∧ b ∣ m ∧ ∀ c : R, a ∣ c → b ∣ c → m ∣ c

def GcdCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b d : R),
    IsGcd R a b d ↔ d ∣ a ∧ d ∣ b ∧ ∀ c : R, c ∣ a → c ∣ b → c ∣ d

def LcmCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b m : R),
    IsLcm R a b m ↔ a ∣ m ∧ b ∣ m ∧ ∀ c : R, a ∣ c → b ∣ c → m ∣ c

def GcdUniqueUpToAssociates : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b d e : R),
    IsGcd R a b d → IsGcd R a b e → Associated d e

def LcmUniqueUpToAssociates : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b m n : R),
    IsLcm R a b m → IsLcm R a b n → Associated m n

/-- Multiplication by units preserves the gcd property. -/
def GcdAssociated : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b d e : R),
    Associated d e → (IsGcd R a b d ↔ IsGcd R a b e)

def LcmAssociated : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b m n : R),
    Associated m n → (IsLcm R a b m ↔ IsLcm R a b n)

/-- The all-zero gcd convention is forced, even without normalization. -/
def GcdZeroZero : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (d : R),
    IsGcd R 0 0 d ↔ d = 0

/-- In particular, for nonzero a a gcd of a and zero is a up to a unit.
The stronger statement at a = 0 is also true and preserves the boundary. -/
def GcdZeroRight : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a d : R),
    IsGcd R a 0 d ↔ Associated d a

def GcdZeroLeft : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a d : R),
    IsGcd R 0 a d ↔ Associated d a

/-- These are actual witnesses, not merely conditional uniqueness statements. -/
def ZeroConventions : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a : R),
    IsGcd R 0 0 0 ∧ IsGcd R a 0 a ∧ IsGcd R 0 a a ∧
      IsLcm R a 0 0 ∧ IsLcm R 0 a 0

def LcmZeroRight : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a m : R),
    IsLcm R a 0 m ↔ m = 0

def LcmZeroLeft : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a m : R),
    IsLcm R 0 a m ↔ m = 0

/-- The source does not supply any gcd-existence axiom for a general domain. -/
def NotEveryDomainHasGcds : Prop :=
  ¬ ∀ (R : Type) [CommRing R] [IsDomain R] (a b : R), ∃ d : R, IsGcd R a b d

end Specs.D07.Ch10.GcdLcm
