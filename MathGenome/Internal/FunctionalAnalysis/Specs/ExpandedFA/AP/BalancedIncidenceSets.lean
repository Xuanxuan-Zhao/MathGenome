import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.WalshBlocks
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! Independent statement of paper.tex:12734–12786, including the summability
used at paper.tex:12894. Indices `m ≥ 1` are represented by natural numbers
with an explicit lower bound. All quotients in the estimates are real. -/
noncomputable section

namespace ExpandedFA.AP.Incidence
open scoped BigOperators

/-- The fixed growth factor in the source. -/
def growthFactor : ℝ := 6 / 5

/-- A single offset is used for the whole sequence. -/
def dimension (offset m : ℕ) : ℕ := ⌊growthFactor ^ (m + offset)⌋₊

def levelSize (offset m : ℕ) : ℕ :=
  ExpandedFA.AP.Walsh.levelSize (dimension offset m)

def rowCount (offset m : ℕ) : ℕ := levelSize offset m ^ 2

/-- Symbols retain their row and their position in that row. -/
abbrev Symbol (offset m : ℕ) := Fin (rowCount offset m) × Fin (levelSize offset m)

/-- The actual number of sets incident with a symbol, counting the set indices. -/
def incidenceCount {k t q : ℕ} (N : Fin q → Finset (Fin k × Fin t))
    (e : Fin k × Fin t) : ℕ :=
  (Finset.univ.filter (fun j => e ∈ N j)).card

/-- The three source requirements, together with the exact set sizes.
The ambient set is all `k*t` symbols, so the balance sum includes unused rows. -/
def FamilyProperties (k t s q n : ℕ) (N : Fin q → Finset (Fin k × Fin t)) : Prop :=
  (∀ j, (N j).card = s) ∧
  (∀ i j, i ≠ j → ((N i ∩ N j).card : ℝ) ≤ (s : ℝ) / (2 * n)) ∧
  (∀ j (r : Fin k), ((N j).filter (fun e => e.1 = r)).card ≤ 1) ∧
  (∑ e : Fin k × Fin t,
    |1 / ((k : ℝ) * t) - (incidenceCount N e : ℝ) / ((q : ℝ) * s)|) ≤
      1 / (n : ℝ)

end ExpandedFA.AP.Incidence

namespace Specs.ExpandedFA.AP.BalancedIncidenceSets
open ExpandedFA.AP.Incidence

/-- Full simultaneous conclusion: one offset and one family at every index,
with the reciprocal dimensions summable over the positive indices. -/
def incidenceSetsExist : Prop :=
  ∃ offset : ℕ,
    ∃ N : ∀ m, Fin (rowCount offset (m + 1)) → Finset (Symbol offset m),
      (∀ m, 1 ≤ m → 2 ≤ dimension offset m) ∧
      (∀ m, 1 ≤ m → FamilyProperties
        (rowCount offset m) (levelSize offset m)
        (levelSize offset (m + 1)) (rowCount offset (m + 1))
        (dimension offset (m + 1)) (N m)) ∧
      Summable (fun m : ℕ => 1 / (dimension offset (m + 1) : ℝ))

/-- This stronger summability assertion holds even before discarding an
initial segment, and hence for any final choice of offset. -/
def reciprocalDimensionsSummable : Prop :=
  ∀ offset : ℕ, Summable (fun m : ℕ => 1 / (dimension offset m : ℝ))

/-- A reusable elementary bound for the actual Walsh level size. -/
def walshSizeBounds : Prop := ∀ n : ℕ, 1 ≤ n →
  4 ^ n ≤ 4 * n * ExpandedFA.AP.Walsh.levelSize n ∧
    ExpandedFA.AP.Walsh.levelSize n ≤ 4 ^ n

/-- The completed portion of the finite construction, before the balance count. -/
def intersectionsAndRows : Prop := ∀ k t s q : ℕ,
  0 < t → 0 < s → s ≤ k →
  ∃ N : Fin q → Finset (Fin k × Fin t),
    (∀ j, (N j).card = s) ∧
    (∀ i j, i ≠ j → ((N i ∩ N j).card : ℝ) ≤
      1 + (s : ℝ) * (q / ((k / s) * t) + 1 : ℕ) / t) ∧
    (∀ j (r : Fin k), ((N j).filter (fun e => e.1 = r)).card ≤ 1)

/-- A sufficient finite balance estimate for the same cyclic family.
The factor two is harmless when removing a finite initial segment. -/
def finiteIncidenceFamily : Prop := ∀ k t s q : ℕ,
  0 < t → 0 < s → 0 < q → s ≤ k →
  ∃ N : Fin q → Finset (Fin k × Fin t),
    (∀ j, (N j).card = s) ∧
    (∀ i j, i ≠ j → ((N i ∩ N j).card : ℝ) ≤
      1 + (s : ℝ) * (q / ((k / s) * t) + 1 : ℕ) / t) ∧
    (∀ j (r : Fin k), ((N j).filter (fun e => e.1 = r)).card ≤ 1) ∧
    (∑ e : Fin k × Fin t,
      |1 / ((k : ℝ) * t) - (incidenceCount N e : ℝ) / ((q : ℝ) * s)|) ≤
        2 * (s : ℝ) / k + 2 * ((k / s : ℕ) : ℝ) * t / q

end Specs.ExpandedFA.AP.BalancedIncidenceSets
