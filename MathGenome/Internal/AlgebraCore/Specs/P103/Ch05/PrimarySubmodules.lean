import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedPrimesInterface
import Mathlib.RingTheory.Ideal.Operations

/-! Primary submodules and the assertions in paper.tex:995.
No finite generation is assumed, including in the Noetherian-ring assertion. -/
namespace P103.Specs.Ch05.PrimarySubmodules
universe u v
open P103.Specs.Ch05.AssociatedPrimesInterface

def PrimaryType := ∀ (R : Type u) [CommRing R] (M : Type v)
  [AddCommGroup M] [Module R M], Submodule R M → Prop

def primaryValue : PrimaryType.{u,v} := fun R _ M _ _ N =>
  N ≠ ⊤ ∧ ∀ (r : R) (m : M), r • m ∈ N → m ∉ N →
    ∃ n : ℕ, 1 ≤ n ∧ ∀ y : M, r ^ n • y ∈ N

def RadicalType := ∀ (R : Type u) [CommRing R] (M : Type v)
  [AddCommGroup M] [Module R M], Submodule R M → Ideal R

def radicalValue : RadicalType.{u,v} := fun R _ M _ _ N =>
  (Module.annihilator R (M ⧸ N)).radical

def ZeroDivisorsType := ∀ (R : Type u) [CommRing R] (M : Type v)
  [AddCommGroup M] [Module R M], Submodule R M → Set R

def zeroDivisorsValue : ZeroDivisorsType.{u,v} := fun _ _ M _ _ N =>
  {r | ∃ x : M ⧸ N, x ≠ 0 ∧ r • x = 0}

def quotient_nontrivialType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M), primaryValue R M N → Nontrivial (M ⧸ N)

def primary_iff_quotientType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M), primaryValue R M N ↔
    N ≠ ⊤ ∧ ∀ (r : R) (x : M ⧸ N), r • x = 0 → x ≠ 0 →
      ∃ n : ℕ, 1 ≤ n ∧ ∀ y : M ⧸ N, r ^ n • y = 0

def radical_isPrimeType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M), primaryValue R M N → (radicalValue R M N).IsPrime

def radical_eq_zeroDivisorsType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M), primaryValue R M N →
      (radicalValue R M N : Set R) = zeroDivisorsValue R M N

def injective_of_not_mem_radicalType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M), primaryValue R M N → ∀ r : R,
      r ∉ radicalValue R M N → Function.Injective (fun x : M ⧸ N => r • x)

def mem_radical_iff_nilpotentType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M) (r : R), r ∈ radicalValue R M N ↔
      ∃ n : ℕ, 1 ≤ n ∧ ∀ y : M ⧸ N, r ^ n • y = 0

def associatedPrimes_singletonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M), primaryValue R M N →
      associatedPrimesValue R (M ⧸ N) = {radicalValue R M N}

end P103.Specs.Ch05.PrimarySubmodules
