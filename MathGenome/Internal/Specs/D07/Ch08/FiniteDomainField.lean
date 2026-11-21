import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Basic.Finite.Defs

/-!
Independent specifications for K07.08.finite_domain_field,
paper.tex:1430–1435. A domain here is a commutative, nontrivial unital
ring without zero divisors, expressed by `CommRing` and `IsDomain`.
`Finite R` means finiteness of the underlying set, not finite dimension.
The field structure must retain all the given commutative ring operations.
The integer example records why the finiteness hypothesis is necessary.
-/

universe u

namespace Specs.D07.Ch08.FiniteDomainField

def NonzeroMultiplicationBijective : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [Finite R] (a : R), a ≠ 0 →
    Function.Bijective (fun x : R => a * x)

def FiniteDomainInverse : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [Finite R] (a : R), a ≠ 0 →
    ∃ b : R, a * b = 1 ∧ b * a = 1

def FiniteDomainIsField : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [Finite R], IsField R

/-- Existence of a field structure extending the original operations. -/
def FieldStructure : Prop :=
  ∀ (R : Type u) (s : CommRing R) [IsDomain R] [Finite R],
    ∃ f : Field R, f.toCommRing = s

def IntegerCounterexample : Prop :=
  IsDomain ℤ ∧ Infinite ℤ ∧ ¬ IsField ℤ

end Specs.D07.Ch08.FiniteDomainField
