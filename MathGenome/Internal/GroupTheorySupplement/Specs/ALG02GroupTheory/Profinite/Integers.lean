import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.Cofinal
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.ProfiniteIntegers.ResidueModel
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.QuotientGroup

/-! The integer part of GR02-C05.05, with the residue model used in FT-E06. -/

namespace Specs.ALG02GroupTheory.Profinite

open AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem

abbrev IntegerGroup := Multiplicative ℤ

abbrev IntegerIndexType := ℕ+ → FiniteIndexNormalSubgroup IntegerGroup

/-- The subgroup of integer multiples of the positive modulus. -/
def integerIndexValue : IntegerIndexType := fun n =>
  { toSubgroup := (AddSubgroup.zmultiples ((n : ℕ) : ℤ)).toSubgroup
    isFiniteIndex' := ⟨by simp⟩ }

def IntegerIndexBijective : Prop := Function.Bijective integerIndexValue

def IntegerFiniteIndex : Prop :=
  ∀ H : AddSubgroup ℤ, H.FiniteIndex ↔ ∃! n : ℕ+, H = AddSubgroup.zmultiples ((n : ℕ) : ℤ)

def IntegerIndexLe : Prop :=
  ∀ m n : ℕ+, integerIndexValue m ≤ integerIndexValue n ↔ (n : ℕ) ∣ (m : ℕ)

abbrev IntegerQuotientEquivType :=
  ∀ n : ℕ+, finiteQuotient (integerIndexValue n) ≃* Multiplicative (ZMod (n : ℕ))

def integerQuotientEquivValue : IntegerQuotientEquivType :=
  fun n => (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative

def IntegerQuotientMk : Prop :=
  ∀ (n : ℕ+) (a : ℤ), integerQuotientEquivValue n (QuotientGroup.mk (Multiplicative.ofAdd a)) =
    Multiplicative.ofAdd (a : ZMod (n : ℕ))

def IntegerTransition : Prop :=
  ∀ (m n : ℕ+) (h : integerIndexValue m ≤ integerIndexValue n)
    (h' : (n : ℕ) ∣ (m : ℕ)) (x : finiteQuotient (integerIndexValue m)),
    (integerQuotientEquivValue n (transitionValue h x)).toAdd =
      reduction n m h' (integerQuotientEquivValue m x).toAdd

def IntegerCompletion : Prop :=
  ∃ e : completionValue IntegerGroup ≃ₜ* Multiplicative ResidueFamily,
    (∀ (x : completionValue IntegerGroup) (n : ℕ+),
      coordinate n (e x).toAdd =
        (integerQuotientEquivValue n (projectionValue (integerIndexValue n) x)).toAdd) ∧
    (∀ a : ℤ, e (etaValue IntegerGroup (Multiplicative.ofAdd a)) =
      Multiplicative.ofAdd (integerResidues a))

abbrev FactorialModulusType := ℕ → ℕ+

def factorialModulusValue : FactorialModulusType :=
  fun j => ⟨j.factorial, Nat.factorial_pos j⟩

abbrev FactorialIndicesType := Set (FiniteIndexNormalSubgroup IntegerGroup)

def factorialIndicesValue : FactorialIndicesType :=
  Set.range fun j => integerIndexValue (factorialModulusValue j)

def FactorialCofinal : Prop :=
  ∀ N : FiniteIndexNormalSubgroup IntegerGroup, ∃ d : factorialIndicesValue, d.1 ≤ N

def FactorialCompletion : Prop :=
  ∃ e : completionValue IntegerGroup ≃ₜ* RestrictedCompletion factorialIndicesValue,
    (e : completionValue IntegerGroup → RestrictedCompletion factorialIndicesValue) =
      restrictCoordinatesValue factorialIndicesValue ∧
    ∀ (x : RestrictedCompletion factorialIndicesValue) (N : FiniteIndexNormalSubgroup IntegerGroup)
      (d : factorialIndicesValue) (h : d.1 ≤ N),
      projectionValue N (e.symm x) = transitionValue h (x.1 d)

def FactorialResidueRestriction : Prop :=
  ∃ e : Multiplicative ResidueFamily ≃ₜ* RestrictedCompletion factorialIndicesValue,
    ∀ (x : Multiplicative ResidueFamily) (j : ℕ),
      (integerQuotientEquivValue (factorialModulusValue j)
        ((e x).1 ⟨integerIndexValue (factorialModulusValue j), ⟨j, rfl⟩⟩)).toAdd =
          coordinate (factorialModulusValue j) x.toAdd

end Specs.ALG02GroupTheory.Profinite
