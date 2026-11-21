import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CharacteristicIsometry
import Mathlib.Logic.Relation

/-! FR-C08, source lines 1162–1202. Coordinates are the canonical zero-based
Young-diagram coordinates. Connectivity is by paths of actual grid edges
inside the skew shape, and height counts all occupied rows minus one. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The skew diagram λ/μ; containment is required separately below. -/
def skewCells {n k : ℕ} (lam : Partition n) (mu : Partition k) : Finset (ℕ × ℕ) :=
  cells lam \ cells mu

/-- Two cells share an edge, rather than merely a vertex. -/
def CellAdjacent (a b : ℕ × ℕ) : Prop :=
  (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
  (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1))

/-- Every two cells are joined by an edge path wholly inside the given set. -/
def EdgeConnected (s : Finset (ℕ × ℕ)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s,
    Relation.ReflTransGen (fun a b => a ∈ s ∧ b ∈ s ∧ CellAdjacent a b) a b

/-- No four cells form an axis-aligned unit square. -/
def NoSquare (s : Finset (ℕ × ℕ)) : Prop :=
  ∀ i j : ℕ, ¬ ((i, j) ∈ s ∧ (i + 1, j) ∈ s ∧
    (i, j + 1) ∈ s ∧ (i + 1, j + 1) ∈ s)

def IsBorderStrip {n k : ℕ} (lam : Partition n) (mu : Partition k) : Prop :=
  cells mu ⊆ cells lam ∧ (skewCells lam mu).Nonempty ∧
    EdgeConnected (skewCells lam mu) ∧ NoSquare (skewCells lam mu)

def borderStripHeight {n k : ℕ} (lam : Partition n) (mu : Partition k) : ℕ :=
  ((skewCells lam mu).image Prod.fst).card - 1

/-- The ordinary Specht trace on the conjugacy class of a partition.
The chosen action is required to be the restriction of the tabloid action.
The implementation proves existence and identifies this with every inherited
realization; no character formula is used as the definition of a character. -/
def spechtCharacterAtCycle {n : ℕ} (lam nu : Partition n) : ℂ :=
  representationClassFunction
    (Classical.epsilon (fun rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam) =>
      InheritedSpechtAction lam rho)) (cycleClass nu)

/-- Adjoin one positive part to a cycle partition. This definition uses the
canonical multiset of parts, so the new cycle may appear anywhere in sorted order. -/
def adjoinCycle {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (tau : Partition (n - m)) : Partition n where
  parts := m ::ₘ tau.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.mp hi with h | h
    · simpa only [h] using hm
    · exact tau.parts_pos h
  parts_sum := by
    rw [Multiset.sum_cons, tau.parts_sum, Nat.add_sub_of_le hmn]

def skewCellsType := {n k : ℕ} → Partition n → Partition k → Finset (ℕ × ℕ)
def CellAdjacentType := (ℕ × ℕ) → (ℕ × ℕ) → Prop
def EdgeConnectedType := Finset (ℕ × ℕ) → Prop
def NoSquareType := Finset (ℕ × ℕ) → Prop
def IsBorderStripType := {n k : ℕ} → Partition n → Partition k → Prop
def borderStripHeightType := {n k : ℕ} → Partition n → Partition k → ℕ
def spechtCharacterAtCycleType := {n : ℕ} → Partition n → Partition n → ℂ
def adjoinCycleType := {n m : ℕ} → (hm : 0 < m) → (hmn : m ≤ n) →
  Partition (n - m) → Partition n

/-- Full deletion rule, including m=n and the empty remaining partition. -/
def murnaghan_nakayamaType : Prop :=
  ∀ {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (lam : Partition n) (tau : Partition (n - m)),
    spechtCharacterAtCycle lam (adjoinCycle hm hmn tau) =
      ∑ mu : Partition (n - m),
        if IsBorderStrip lam mu ∧ (skewCells lam mu).card = m then
          (-1 : ℂ) ^ borderStripHeight lam mu * spechtCharacterAtCycle mu tau else 0

def spechtCharacterAtCycle_traceType : Prop :=
  ∀ {n : ℕ} (lam nu : Partition n)
    (rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam)),
    InheritedSpechtAction lam rho → ∀ g : SymmetricGroup n,
      cyclePartition g = nu → spechtCharacterAtCycle lam nu = rho.character g

def spechtCharacterAtCycle_emptyType : Prop :=
  spechtCharacterAtCycle emptyPartition emptyPartition = 1

/-- Intermediate algebraic recurrence, with literal polynomial coefficients.
This is not the border-strip identification required by the main theorem. -/
def spechtCharacterAtCycle_adjoinCycleType : Prop :=
  ∀ {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (lam : Partition n) (tau : Partition (n-m))
    (r : ℕ), 1 ≤ r → n ≤ r →
    spechtCharacterAtCycle lam (adjoinCycle hm hmn tau) =
      ∑ mu : Partition (n-m),
        naturalCoefficient (shiftedPartition r lam)
          (powerSum r m * partitionAlternant r mu) * spechtCharacterAtCycle mu tau

end Specs.AdvancedFiniteGroupRepresentations
