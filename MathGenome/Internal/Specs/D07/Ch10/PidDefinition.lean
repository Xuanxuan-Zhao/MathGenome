import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.ZMod.Basic

/-!
Independent specifications for K07.10.pid_definition, paper.tex:1912–1917.
The ambient ring is commutative and unital. A PID additionally requires
the nontrivial domain property; a principal ideal ring does not.
The residue-class model of ℤ/4ℤ is `ZMod 4`.
-/

universe u

namespace Specs.D07.Ch10.PidDefinition

def PIDPredicateType : Type (u + 1) :=
  (R : Type u) → [CommRing R] → Prop

/-- The domain condition includes nontriviality; the ideal quantifier includes
the zero ideal and the whole ring. -/
def pidPredicateValue : PIDPredicateType.{u} :=
  fun R _ => IsDomain R ∧ ∀ I : Ideal R, ∃ a : R, I = Ideal.span {a}

/-- Mathlib's principal ideal ring class requires exactly one generator
for each ideal, with no domain assumption. -/
def PrincipalIdealRingIff : Prop :=
  ∀ (R : Type u) [CommRing R],
    IsPrincipalIdealRing R ↔ ∀ I : Ideal R, ∃ a : R, I = Ideal.span {a}

def PIDIff : Prop :=
  ∀ (R : Type u) [CommRing R],
    pidPredicateValue R ↔ IsDomain R ∧ IsPrincipalIdealRing R

/-- The integer ideals containing (4) are precisely the ideals with a
nonnegative generator dividing 4. -/
def IntegerIdealsAboveFour : Prop :=
  ∀ J : Ideal ℤ, Ideal.span {(4 : ℤ)} ≤ J ↔
    ∃ n : ℕ, n ∣ 4 ∧ J = Ideal.span {(n : ℤ)}

def DivisorsFour : Prop :=
  ∀ n : ℕ, n ∣ 4 ↔ n = 1 ∨ n = 2 ∨ n = 4

/-- Inverse image under the actual integer projection gives the ordered
ideal correspondence. Its inverse is identified by its actual set image. -/
def ZModFourIdealCorrespondence : Prop :=
  ∃ e : Ideal (ZMod 4) ≃o {J : Ideal ℤ // Ideal.span {(4 : ℤ)} ≤ J},
    (∀ I, (e I).val = I.comap (Int.castRingHom (ZMod 4))) ∧
    (∀ J, (e.symm J : Set (ZMod 4)) =
      (Int.castRingHom (ZMod 4)) '' (J.val : Set ℤ))

/-- The same nonnegative generator describes the preimage and its image. -/
def ZModFourIdealGenerators : Prop :=
  ∀ I : Ideal (ZMod 4), ∃ n : ℕ, n ∣ 4 ∧
    I.comap (Int.castRingHom (ZMod 4)) = Ideal.span {(n : ℤ)} ∧
    I = Ideal.span {(n : ZMod 4)}

/-- Exhaustiveness and distinctness of the three listed ideals. -/
def ZModFourIdeals : Prop :=
  (∀ I : Ideal (ZMod 4),
    I = ⊥ ∨ I = Ideal.span {(2 : ZMod 4)} ∨ I = ⊤) ∧
  (⊥ : Ideal (ZMod 4)) ≠ Ideal.span {(2 : ZMod 4)} ∧
  Ideal.span {(2 : ZMod 4)} ≠ ⊤ ∧ (⊥ : Ideal (ZMod 4)) ≠ ⊤

def ZModFourZeroDivisor : Prop :=
  (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) * 2 = 0

def ZModFourPrincipalNotDomain : Prop :=
  IsPrincipalIdealRing (ZMod 4) ∧ ¬ IsDomain (ZMod 4) ∧
    ¬ pidPredicateValue (ZMod 4)

end Specs.D07.Ch10.PidDefinition
