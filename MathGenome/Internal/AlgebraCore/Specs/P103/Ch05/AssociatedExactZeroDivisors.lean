import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedPrimesInterface
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Prod

/-!
The remaining assertions of Theorem 5.3, paper.tex:970–981.
`associatedPrimesValue` uses exact element annihilators; `supportValue`
uses `LocalizedModule` at the complement of each prime. A binary direct
sum is represented by the product module with its canonical inclusions.
No nonzero hypothesis is imposed on the ring or on any module.
-/
namespace P103.Specs.Ch05.AssociatedExactZeroDivisors

open P103.Specs.Ch05.AssociatedPrimesInterface
universe u v w x

def zero_divisorsType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    {r : R | ∃ m : M, m ≠ 0 ∧ r • m = 0} =
      ⋃ p ∈ associatedPrimesValue R M, (p : Set R)

def associatedPrimes_exactType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (L : Type v) (M : Type w) (N : Type x)
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    [Module.Finite R L] [Module.Finite R M] [Module.Finite R N]
    (i : L →ₗ[R] M) (q : M →ₗ[R] N),
    Function.Injective i → Function.Exact i q → Function.Surjective q →
    associatedPrimesValue R L ⊆ associatedPrimesValue R M ∧
      associatedPrimesValue R M ⊆ associatedPrimesValue R L ∪ associatedPrimesValue R N

def support_exactType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (L : Type v) (M : Type w) (N : Type x)
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    [Module.Finite R L] [Module.Finite R M] [Module.Finite R N]
    (i : L →ₗ[R] M) (q : M →ₗ[R] N),
    Function.Injective i → Function.Exact i q → Function.Surjective q →
    supportValue R M = supportValue R L ∪ supportValue R N

def associatedPrimes_prodType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (L : Type v) (N : Type w) [AddCommGroup L] [AddCommGroup N]
    [Module R L] [Module R N] [Module.Finite R L] [Module.Finite R N],
    associatedPrimesValue R (L × N) = associatedPrimesValue R L ∪ associatedPrimesValue R N

end P103.Specs.Ch05.AssociatedExactZeroDivisors
