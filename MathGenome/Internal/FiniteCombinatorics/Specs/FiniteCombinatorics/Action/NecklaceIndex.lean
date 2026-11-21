import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.RotationCycles
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.Polya
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.WeightedPolya
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.NumberTheory.Divisors

/-! W34, necklace part. For n > 0 the positions are ZMod n, and the group
is its additive group written multiplicatively. Length zero is represented
separately by Fin 0, never by the infinite type ZMod 0. -/
namespace FiniteCombinatorics.NecklaceIndexSpec
open scoped BigOperators
universe u v

@[instance_reducible] def rotationAction (n : ℕ) :
    MulAction (Multiplicative (ZMod n)) (ZMod n) where
  smul a x := a.toAdd + x
  one_smul x := zero_add x
  mul_smul a b x := add_assoc a.toAdd b.toAdd x
attribute [local instance] rotationAction FixedColoringsSpec.coloringAction

/-- A necklace is precisely a coloring modulo rotations, with inverse
precomposition as the coloring action. -/
def Necklaces (n : ℕ) [NeZero n] (C : Type u) :=
  MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (ZMod n → C)

noncomputable local instance necklacesFintype (n : ℕ) [NeZero n] (C : Type u) [Fintype C] :
    Fintype (Necklaces n C) := by
  unfold Necklaces
  exact Fintype.ofFinite _

noncomputable def cycleIndex (n : ℕ) [NeZero n] :
    MvPolynomial (Fin (Fintype.card (ZMod n))) ℚ :=
  CycleIndexSpec.cycleIndex (Multiplicative (ZMod n)) (ZMod n)

noncomputable def inventory (n : ℕ) [NeZero n] (C : Type u) [Fintype C] :
    MvPolynomial C ℕ :=
  WeightedPolyaSpec.orbitEnumerator (Multiplicative (ZMod n)) (ZMod n) C

/-- The permutation group of the empty set is the trivial empty-position action. -/
def EmptyNecklaces (C : Type u) :=
  MulAction.orbitRel.Quotient (Equiv.Perm (Fin 0)) (Fin 0 → C)

def rotationActionType := (n : ℕ) → MulAction (Multiplicative (ZMod n)) (ZMod n)
def NecklacesType := ∀ (n : ℕ) [NeZero n], Type u → Type u
def cycleIndexType := ∀ (n : ℕ) [NeZero n], MvPolynomial (Fin (Fintype.card (ZMod n))) ℚ
def inventoryType := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C], MvPolynomial C ℕ
def EmptyNecklacesType := Type u → Type u

def RotationApply : Prop := ∀ (n : ℕ) (a : ZMod n) (x : ZMod n),
  (Multiplicative.ofAdd a) • x = x + a

def NecklaceEquality : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) (f h : ZMod n → C),
  Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod n)) (ZMod n → C)) f =
    Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod n)) (ZMod n → C)) h ↔
    ∃ a : ZMod n, ∀ x, f (x + a) = h x

def CycleIndexFormula : Prop := ∀ (n : ℕ) [NeZero n],
  cycleIndex n = (n : ℚ)⁻¹ • ∑ d ∈ n.divisors,
    (Nat.totient d : ℚ) • RotationCyclesSpec.lengthVariable n d ^ (n / d)

def Count : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C],
  (Nat.card (Necklaces n C) : ℚ) =
    (n : ℚ)⁻¹ * ∑ d ∈ n.divisors, (Nat.totient d : ℚ) * (Fintype.card C : ℚ) ^ (n / d)

def WeightedFormula : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C],
  MvPolynomial.map (Nat.castRingHom ℚ) (inventory n C) =
    (n : ℚ)⁻¹ • ∑ d ∈ n.divisors, (Nat.totient d : ℚ) •
      (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ d) ^ (n / d)

def CoefficientCounts : Prop := by
  classical
  exact ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C] (m : C →₀ ℕ),
    (inventory n C).coeff m =
      (Finset.univ.filter (fun O : Necklaces n C =>
        WeightedPolyaSpec.orbitMultiplicity (Multiplicative (ZMod n)) (ZMod n) C O = m)).card

def Specialization : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C]
    (R : Type v) [CommSemiring R] (w : C → R),
  MvPolynomial.eval₂ (Nat.castRingHom R) w (inventory n C) =
    ∑ O : Necklaces n C, ∏ x : ZMod n, w (O.out x)

def EmptyColorsCount : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C] [IsEmpty C],
  Nat.card (Necklaces n C) = 0

def EmptyColorsInventory : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C] [IsEmpty C],
  inventory n C = 0

def EmptyCount : Prop := ∀ (C : Type u), Nat.card (EmptyNecklaces C) = 1

def EmptyIndex : Prop :=
  CycleIndexSpec.cycleIndex (Equiv.Perm (Fin 0)) (Fin 0) = 1

def EmptyInventory : Prop := ∀ (C : Type u) [Fintype C],
  WeightedPolyaSpec.orbitEnumerator (Equiv.Perm (Fin 0)) (Fin 0) C = 1

end FiniteCombinatorics.NecklaceIndexSpec
