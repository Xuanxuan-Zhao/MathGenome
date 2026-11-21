import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.FlatLattice
import Mathlib.Order.RelSeries
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Preorder.Chain

/-! The lattice-rank argument in W72. A maximal chain in the finite
interval [x,y] is represented by a saturated series with head x and last y;
its length counts edges, so a singleton interval has length zero.
No atom-generation hypothesis occurs in these statements.
`IsUpperModularLattice` has exactly the covering axiom used by
`GeometricLattice` in FlatLattice. -/
namespace FiniteCombinatorics.Matroid
universe u

abbrev SaturatedChain (L : Type u) [PartialOrder L] :=
  RelSeries {(x, y) : L × L | x ⋖ y}

namespace Expected

/-- The common interval length, expressed independently as the supremum of
lengths of saturated chains. All such lengths will be proved equal and
at least one such chain will be proved to exist when x ≤ y. -/
noncomputable def latticeIntervalLength {L : Type u} [PartialOrder L] (x y : L) : ℕ :=
  sSup {n | ∃ s : SaturatedChain L, s.head = x ∧ s.last = y ∧ s.length = n}

noncomputable def latticeHeight {L : Type u} [PartialOrder L] [OrderBot L] (x : L) : ℕ :=
  latticeIntervalLength (⊥ : L) x

def latticeIntervalLengthType := ∀ {L : Type u}, [PartialOrder L] → L → L → ℕ
def latticeHeightType := ∀ {L : Type u}, [PartialOrder L] → [OrderBot L] → L → ℕ

def latticeJoinCover : Prop :=
  ∀ {L : Type u} [Lattice L] [IsUpperModularLattice L] {x y : L},
    x ⋖ y → ∀ b : L, x ⊔ b = y ⊔ b ∨ (x ⊔ b) ⋖ (y ⊔ b)

def latticeChainExists : Prop :=
  ∀ {L : Type u} [Lattice L] [Finite L] (x y : L), x ≤ y →
    ∃ s : SaturatedChain L, s.head = x ∧ s.last = y

def latticeChainsEqualLength : Prop :=
  ∀ {L : Type u} [Lattice L] [IsUpperModularLattice L]
    (s t : SaturatedChain L), s.head = t.head → s.last = t.last → s.length = t.length

def latticeIntervalLengthOfChain : Prop :=
  ∀ {L : Type u} [Lattice L] [IsUpperModularLattice L] (s : SaturatedChain L),
    latticeIntervalLength s.head s.last = s.length

/-- A chain maximal by inclusion in an interval, with no saturation
assumption: its length is the interval length defined above. -/
def latticeMaximalChainLength : Prop :=
  ∀ {L : Type u} [Lattice L] [Finite L] [IsUpperModularLattice L]
    (x y : L) [Fact (x ≤ y)] (s : LTSeries (Set.Icc x y)),
    IsMaxChain (· ≤ ·) (Set.range s) → s.length = latticeIntervalLength x y

def latticeIntervalLengthSelf : Prop :=
  ∀ {L : Type u} [Lattice L] [IsUpperModularLattice L] (x : L),
    latticeIntervalLength x x = 0

def latticeHeightBot : Prop :=
  ∀ {L : Type u} [Lattice L] [OrderBot L] [IsUpperModularLattice L],
    latticeHeight (⊥ : L) = 0

def latticeChainHeight : Prop :=
  ∀ {L : Type u} [Lattice L] [OrderBot L] [IsUpperModularLattice L] [Finite L]
    (s : SaturatedChain L), latticeHeight s.last = latticeHeight s.head + s.length

def latticeIntervalHeight : Prop :=
  ∀ {L : Type u} [Lattice L] [OrderBot L] [IsUpperModularLattice L] [Finite L]
    (x y : L), x ≤ y →
      latticeIntervalLength x y = latticeHeight y - latticeHeight x ∧
      (latticeIntervalLength x y : ℤ) = (latticeHeight y : ℤ) - (latticeHeight x : ℤ)

def latticeHeightMonotone : Prop :=
  ∀ {L : Type u} [Lattice L] [OrderBot L] [IsUpperModularLattice L] [Finite L],
    Monotone (latticeHeight (L := L))

def latticeHeightStrictMono : Prop :=
  ∀ {L : Type u} [Lattice L] [OrderBot L] [IsUpperModularLattice L] [Finite L],
    StrictMono (latticeHeight (L := L))

def latticeHeightCover : Prop :=
  ∀ {L : Type u} [Lattice L] [OrderBot L] [IsUpperModularLattice L] [Finite L]
    {x y : L}, x ⋖ y → latticeHeight y = latticeHeight x + 1

def latticeHeightSubmodular : Prop :=
  ∀ {L : Type u} [Lattice L] [OrderBot L] [IsUpperModularLattice L] [Finite L]
    (x y : L), latticeHeight (x ⊔ y) + latticeHeight (x ⊓ y) ≤
      latticeHeight x + latticeHeight y

def latticeAtomIncrement : Prop :=
  ∀ {L : Type u} [Lattice L] [OrderBot L] [IsUpperModularLattice L] [Finite L]
    (x a : L), IsAtom a →
      0 ≤ (latticeHeight (x ⊔ a) : ℤ) - (latticeHeight x : ℤ) ∧
      (latticeHeight (x ⊔ a) : ℤ) - (latticeHeight x : ℤ) ≤ 1

end Expected
end FiniteCombinatorics.Matroid
