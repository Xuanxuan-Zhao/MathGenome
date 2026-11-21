import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
Independent specification for K07.20.purely_inseparable (paper.tex:5807–5824).
Extensions are specified algebra maps, so “L = K” means that the base map is
surjective. `IsPurelyInseparable` is the canonical Mathlib predicate; its
agreement with the source's power definition and its algebraicity are explicit
obligations below. No finiteness is imposed except in `FiniteDegree`.
The root count uses the finite set of roots, discarding multiplicities, in any
specified algebraically closed overfield. The least exponent includes zero.
-/

universe u v w

namespace Specs.D07.Ch20.PurelyInseparable

open Polynomial
open scoped Classical

/-- Positive-characteristic definition, including algebraicity in the RHS. -/
def PositiveCharacteristic : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [CharP K p], p.Prime →
      (IsPurelyInseparable K L ↔
        Algebra.IsAlgebraic K L ∧
        ∀ a : L, ∃ r : ℕ, a ^ (p ^ r) ∈ (algebraMap K L).range)

/-- Equality with the base is expressed relative to the chosen embedding. -/
def CharacteristicZero : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [CharZero K],
    IsPurelyInseparable K L ↔ Function.Surjective (algebraMap K L)

def Algebraicity : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    IsPurelyInseparable K L → Algebra.IsAlgebraic K L

/-- The closure is allowed a different universe and independent embedding. -/
def OneRootIffPower : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω] [IsAlgClosed Ω]
    (p : ℕ) [CharP K p], p.Prime → ∀ a : L, IsAlgebraic K a →
      (((minpoly K a).aroots Ω).toFinset.card = 1 ↔
        ∃ r : ℕ, a ^ (p ^ r) ∈ (algebraMap K L).range)

/-- The binomial is over K; b is the unique base scalar representing a^(p^t).
The nonmembership condition says t is the least possible exponent. -/
def PowerIffLeastBinomial : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [CharP K p], p.Prime → ∀ a : L, IsAlgebraic K a →
      ((∃ r : ℕ, a ^ (p ^ r) ∈ (algebraMap K L).range) ↔
        ∃ (t : ℕ) (b : K), algebraMap K L b = a ^ (p ^ t) ∧
          (∀ r : ℕ, r < t → a ^ (p ^ r) ∉ (algebraMap K L).range) ∧
          minpoly K a = X ^ (p ^ t) - C b)

def FiniteDegree : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [CharP K p], p.Prime → IsPurelyInseparable K L →
      [FiniteDimensional K L] → ∃ n : ℕ, Module.finrank K L = p ^ n

/-- An element can be purely inseparable even when the whole extension is not. -/
def SeparablePureElement : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [CharP K p], p.Prime → ∀ a : L,
      (∃ r : ℕ, a ^ (p ^ r) ∈ (algebraMap K L).range) →
      IsSeparable K a → a ∈ (algebraMap K L).range

/-- Also covers the source's characteristic-zero convention. -/
def SeparableElementInPureExtension : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    IsPurelyInseparable K L → ∀ a : L,
      IsSeparable K a → a ∈ (algebraMap K L).range

/-- Exactly one extension of an arbitrary prescribed base embedding.
No pre-existing K-algebra structure on Ω and no finite-degree premise. -/
def UniqueEmbedding : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω] [Algebra K L] [IsAlgClosed Ω],
    IsPurelyInseparable K L → ∀ σ : K →+* Ω,
      ∃! τ : L →+* Ω, τ.comp (algebraMap K L) = σ

/-- Roots t^(1/p) exist in an algebraic closure (indeed in any closed overfield). -/
def ExampleRootExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type w) [Field Ω]
    [Algebra (RatFunc (ZMod p)) Ω] [IsAlgClosed Ω],
    ∃ a : Ω, a ^ p = algebraMap (RatFunc (ZMod p)) Ω RatFunc.X

/-- Any chosen p-th root of t gives a genuinely nontrivial purely inseparable
extension of degree p and exactly one base embedding into a closed overfield. -/
def RationalFunctionExample : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Type v) (Ω : Type w) [Field L] [Field Ω]
    [Algebra (RatFunc (ZMod p)) L] [Algebra (RatFunc (ZMod p)) Ω] [IsAlgClosed Ω]
    (a : L), a ^ p = algebraMap (RatFunc (ZMod p)) L RatFunc.X →
      IsPurelyInseparable (RatFunc (ZMod p))
        (IntermediateField.adjoin (RatFunc (ZMod p)) {a}) ∧
      Module.finrank (RatFunc (ZMod p))
        (IntermediateField.adjoin (RatFunc (ZMod p)) {a}) = p ∧
      1 < Module.finrank (RatFunc (ZMod p))
        (IntermediateField.adjoin (RatFunc (ZMod p)) {a}) ∧
      ∃! _f : IntermediateField.adjoin (RatFunc (ZMod p)) {a} →ₐ[RatFunc (ZMod p)] Ω,
        True

/-- With a specified inclusion of the ambient field into Ω, the unique map
is precisely the restriction of that inclusion. -/
def ExampleEmbeddingIsInclusion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Type v) (Ω : Type w) [Field L] [Field Ω]
    [Algebra (RatFunc (ZMod p)) L] [Algebra (RatFunc (ZMod p)) Ω]
    (a : L), a ^ p = algebraMap (RatFunc (ZMod p)) L RatFunc.X →
    ∀ (i : L →ₐ[RatFunc (ZMod p)] Ω)
      (f : IntermediateField.adjoin (RatFunc (ZMod p)) {a} →ₐ[RatFunc (ZMod p)] Ω),
      f = i.comp (IntermediateField.adjoin (RatFunc (ZMod p)) {a}).val

end Specs.D07.Ch20.PurelyInseparable
