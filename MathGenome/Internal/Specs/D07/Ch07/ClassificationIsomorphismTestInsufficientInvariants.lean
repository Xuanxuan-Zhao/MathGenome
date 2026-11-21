import MathGenome.Internal.Specs.D07.Ch07.TorsionCountInvariants
import MathGenome.Internal.Specs.D07.Ch06.CompositionSeriesDefinition
import Mathlib.GroupTheory.Exponent

/-! Independent statements of the counterexamples in paper.tex:1150 and 3482.
The additive cyclic groups are the actual residue groups `ZMod n`. -/
namespace Specs.D07.Ch07.ClassificationIsomorphismTestInsufficientInvariants

open Specs.D07.Ch07.TorsionCountInvariants
open Specs.D07.Ch06.CompositionSeriesDefinition

abbrev SquarePair (p : ℕ) := ZMod (p ^ 2) × ZMod (p ^ 2)
abbrev MixedTriple (p : ℕ) := ZMod (p ^ 2) × (ZMod p × ZMod p)
abbrev Klein := ZMod 2 × ZMod 2

def OrderFourCardinality : Prop :=
  Nat.card (ZMod 4) = 4 ∧ Nat.card Klein = 4

def OrderFourNotIsomorphic : Prop := ¬ Nonempty (ZMod 4 ≃+ Klein)

def OrderFourElementOrders : Prop :=
  addOrderOf (1 : ZMod 4) = 4 ∧ ∀ x : Klein, addOrderOf x ≠ 4

def PrimeExampleCardinality : Prop :=
  ∀ p : ℕ, p.Prime →
    Nat.card (SquarePair p) = p ^ 4 ∧ Nat.card (MixedTriple p) = p ^ 4

def PrimeExampleExponent : Prop :=
  ∀ p : ℕ, p.Prime →
    AddMonoid.exponent (SquarePair p) = p ^ 2 ∧
    AddMonoid.exponent (MixedTriple p) = p ^ 2

def PrimeExampleTorsionCounts : Prop :=
  ∀ p : ℕ, p.Prime →
    Nat.card (torsionSubgroup (SquarePair p) p 1) = p ^ 2 ∧
    Nat.card (torsionSubgroup (MixedTriple p) p 1) = p ^ 3

def PrimeExampleNotIsomorphic : Prop :=
  ∀ p : ℕ, p.Prime → ¬ Nonempty (SquarePair p ≃+ MixedTriple p)

/-- There are exactly two steps and each actual adjacent quotient is C₂.
`Multiplicative` changes notation only, to reuse the canonical shared series. -/
def HasTwoC2Factors (A : Type) [AddCommGroup A] : Prop :=
  ∃ s : Series (Multiplicative A), s.length = 2 ∧
    ∀ i : Fin s.length,
      Nonempty (factorValue s i ≃* Multiplicative (ZMod 2))

def OrderFourCompositionFactors : Prop :=
  HasTwoC2Factors (ZMod 4) ∧ HasTwoC2Factors Klein

end Specs.D07.Ch07.ClassificationIsomorphismTestInsufficientInvariants
