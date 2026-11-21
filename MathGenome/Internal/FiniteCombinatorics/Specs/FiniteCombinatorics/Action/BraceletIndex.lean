import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.ReflectionCycles
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.NecklaceIndex

/-! W34, bracelets. Positive lengths use the abstract group DihedralGroup n
acting on ZMod n. We embed the finite cycle-index variables into ℕ, with
s_k = X k. This is an injective renaming; no out-of-range variable occurs
with positive exponent. Length zero uses Fin 0, not ZMod 0. -/
namespace FiniteCombinatorics.BraceletIndexSpec
open scoped BigOperators
universe u v
attribute [local instance] FixedColoringsSpec.coloringAction Classical.propDecidable

def Bracelets (n : ℕ) [NeZero n] (C : Type u) :=
  MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n → C)

noncomputable local instance braceletsFintype (n : ℕ) [NeZero n]
    (C : Type u) [Fintype C] : Fintype (Bracelets n C) := by
  unfold Bracelets
  exact Fintype.ofFinite _

noncomputable def cycleIndex (n : ℕ) [NeZero n] : MvPolynomial ℕ ℚ :=
  MvPolynomial.rename (fun i : Fin (Fintype.card (ZMod n)) => i.val + 1)
    (CycleIndexSpec.cycleIndex (DihedralGroup n) (ZMod n))

noncomputable def rotationIndex (n : ℕ) [NeZero n] : MvPolynomial ℕ ℚ :=
  MvPolynomial.rename (fun i : Fin (Fintype.card (ZMod n)) => i.val + 1)
    (NecklaceIndexSpec.cycleIndex n)

noncomputable def inventory (n : ℕ) [NeZero n] (C : Type u) [Fintype C] :
    MvPolynomial C ℕ := WeightedPolyaSpec.orbitEnumerator (DihedralGroup n) (ZMod n) C

def EmptyBracelets (C : Type u) :=
  MulAction.orbitRel.Quotient (Equiv.Perm (Fin 0)) (Fin 0 → C)

def BraceletsType := ∀ (n : ℕ) [NeZero n], Type u → Type u
def cycleIndexType := ∀ (n : ℕ) [NeZero n], MvPolynomial ℕ ℚ
def rotationIndexType := ∀ (n : ℕ) [NeZero n], MvPolynomial ℕ ℚ
def inventoryType := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C], MvPolynomial C ℕ
def EmptyBraceletsType := Type u → Type u

def BraceletEquality : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) (f h : ZMod n → C),
  Quotient.mk (MulAction.orbitRel (DihedralGroup n) (ZMod n → C)) f =
    Quotient.mk (MulAction.orbitRel (DihedralGroup n) (ZMod n → C)) h ↔
    ∃ (a : ZMod n) (e : Bool), ∀ x, f (a + if e then -x else x) = h x

def OddIndex : Prop := ∀ (n : ℕ) [NeZero n], Odd n →
  cycleIndex n = (1 / 2 : ℚ) • rotationIndex n +
    (1 / 2 : ℚ) • (MvPolynomial.X 1 * MvPolynomial.X 2 ^ ((n - 1) / 2))

def EvenIndex : Prop := ∀ (n : ℕ) [NeZero n], Even n →
  cycleIndex n = (1 / 2 : ℚ) • rotationIndex n +
    (1 / 4 : ℚ) • (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ ((n - 2) / 2) +
      MvPolynomial.X 2 ^ (n / 2))

def OddCount : Prop := ∀ (n : ℕ) [NeZero n], Odd n → ∀ (C : Type u) [Fintype C],
  (Nat.card (Bracelets n C) : ℚ) =
    (1 / 2 : ℚ) * (Nat.card (NecklaceIndexSpec.Necklaces n C) : ℚ) +
      (1 / 2 : ℚ) * ((Fintype.card C : ℚ) * (Fintype.card C : ℚ) ^ ((n - 1) / 2))

def EvenCount : Prop := ∀ (n : ℕ) [NeZero n], Even n → ∀ (C : Type u) [Fintype C],
  (Nat.card (Bracelets n C) : ℚ) =
    (1 / 2 : ℚ) * (Nat.card (NecklaceIndexSpec.Necklaces n C) : ℚ) +
      (1 / 4 : ℚ) * ((Fintype.card C : ℚ) ^ 2 * (Fintype.card C : ℚ) ^ ((n - 2) / 2) +
        (Fintype.card C : ℚ) ^ (n / 2))

def OddWeighted : Prop := ∀ (n : ℕ) [NeZero n], Odd n → ∀ (C : Type u) [Fintype C],
  MvPolynomial.map (Nat.castRingHom ℚ) (inventory n C) =
    (1 / 2 : ℚ) • MvPolynomial.map (Nat.castRingHom ℚ) (NecklaceIndexSpec.inventory n C) +
      (1 / 2 : ℚ) • ((∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ)) *
        (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ 2) ^ ((n - 1) / 2))

def EvenWeighted : Prop := ∀ (n : ℕ) [NeZero n], Even n → ∀ (C : Type u) [Fintype C],
  MvPolynomial.map (Nat.castRingHom ℚ) (inventory n C) =
    (1 / 2 : ℚ) • MvPolynomial.map (Nat.castRingHom ℚ) (NecklaceIndexSpec.inventory n C) +
      (1 / 4 : ℚ) • ((∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ)) ^ 2 *
        (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ 2) ^ ((n - 2) / 2) +
        (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ 2) ^ (n / 2))

def CoefficientCounts : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C] (m : C →₀ ℕ),
  (inventory n C).coeff m = (Finset.univ.filter (fun O : Bracelets n C =>
    WeightedPolyaSpec.orbitMultiplicity (DihedralGroup n) (ZMod n) C O = m)).card

def Specialization : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C]
    (R : Type v) [CommSemiring R] (w : C → R),
  MvPolynomial.eval₂ (Nat.castRingHom R) w (inventory n C) =
    ∑ O : Bracelets n C, ∏ x : ZMod n, w (O.out x)

def EmptyColorsCount : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C] [IsEmpty C],
  Nat.card (Bracelets n C) = 0

def EmptyColorsInventory : Prop := ∀ (n : ℕ) [NeZero n] (C : Type u) [Fintype C] [IsEmpty C],
  inventory n C = 0

def EmptyCount : Prop := ∀ (C : Type u), Nat.card (EmptyBracelets C) = 1

def EmptyIndex : Prop := CycleIndexSpec.cycleIndex (Equiv.Perm (Fin 0)) (Fin 0) = 1

def EmptyInventory : Prop := ∀ (C : Type u) [Fintype C],
  WeightedPolyaSpec.orbitEnumerator (Equiv.Perm (Fin 0)) (Fin 0) C = 1

-- Explicit low-length checks retain the abstract 2n-element averaging action.
def OneIndex : Prop := cycleIndex 1 = MvPolynomial.X 1
def TwoIndex : Prop := cycleIndex 2 =
  (1 / 2 : ℚ) • (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2)
end FiniteCombinatorics.BraceletIndexSpec
