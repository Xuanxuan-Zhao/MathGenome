import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions

/-!
Independent statements for paper.tex:468–484.
`ThreePoint` is the subtype of the actual source set `{1, 2, 3} ⊆ ℕ`.
The two families below are exactly the displayed families on that set.
The charge is defined on sets for convenience; its measure interface below
restricts evaluation to the finite/cofinite algebra.
-/

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch01.AxiomCounterexamples

abbrev ThreePoint := ↥({1, 2, 3} : Set ℕ)

def pointOne : ThreePoint := ⟨1, by simp⟩
def pointTwo : ThreePoint := ⟨2, by simp⟩
def pointThree : ThreePoint := ⟨3, by simp⟩

def firstFamily : Set (Set ThreePoint) := {∅, univ, {pointOne}, {pointTwo, pointThree}}

def secondFamily : Set (Set ThreePoint) := {∅, univ, {pointTwo}, {pointOne, pointThree}}

def finiteCofinite : Set (Set ℕ) := {s | s.Finite ∨ sᶜ.Finite}

noncomputable def cofiniteCharge (s : Set ℕ) : ℝ≥0∞ := by
  classical
  exact if s.Finite then 0 else 1

end D11.Ch01.AxiomCounterexamples

namespace Specs.D11.Ch01.AxiomCounterexamples

open _root_.D11.Ch01.AxiomCounterexamples
open _root_.D11.Ch01.MeasureDefinitions

def union_sigma_failure : Prop :=
  (∃ m₁ m₂ : MeasurableSpace ThreePoint,
    (∀ s, MeasurableSet[m₁] s ↔ s ∈ firstFamily) ∧
    (∀ s, MeasurableSet[m₂] s ↔ s ∈ secondFamily)) ∧
  {pointOne} ∈ firstFamily ∪ secondFamily ∧
  {pointTwo} ∈ firstFamily ∪ secondFamily ∧
  ({pointOne} ∪ {pointTwo}) ∉ firstFamily ∪ secondFamily ∧
  ¬ IsSetAlgebra (firstFamily ∪ secondFamily) ∧
  ¬ ∃ m : MeasurableSpace ThreePoint,
    ∀ s, MeasurableSet[m] s ↔ s ∈ firstFamily ∪ secondFamily

def finiteCofinite_isAlgebra : Prop := IsSetAlgebra finiteCofinite

def charge_values : Prop :=
  (∀ s : Set ℕ, s.Finite → cofiniteCharge s = 0) ∧
  (∀ s : Set ℕ, sᶜ.Finite → cofiniteCharge s = 1)

/-- A charge on the exact source algebra, using the shared finite-additivity
interface. The quantifier over `hA` makes the type independent of a candidate
proof of algebra closure. -/
def finite_additive_charge : Prop :=
  ∀ hA : IsSetAlgebra finiteCofinite,
    ∃ p : AlgebraMeasure finiteCofinite hA,
      ∀ s : {s : Set ℕ // s ∈ finiteCofinite}, p.value s = cofiniteCharge s.1

/-- Includes the empty finite family (`n = 0`). -/
def charge_finite_additivity : Prop :=
  ∀ (n : ℕ) (E : Fin n → Set ℕ),
    (∀ i, E i ∈ finiteCofinite) →
    Pairwise (fun i j => Disjoint (E i) (E j)) →
    cofiniteCharge (⋃ i, E i) = ∑ i, cofiniteCharge (E i)

def countable_additivity_failure : Prop :=
  (∀ n : ℕ, ({n} : Set ℕ) ∈ finiteCofinite) ∧
  Pairwise (fun i j : ℕ => Disjoint ({i} : Set ℕ) {j}) ∧
  (⋃ n : ℕ, ({n} : Set ℕ)) = univ ∧
  cofiniteCharge univ = 1 ∧
  (∑' n : ℕ, cofiniteCharge {n}) = 0 ∧
  cofiniteCharge (⋃ n : ℕ, ({n} : Set ℕ)) ≠ ∑' n : ℕ, cofiniteCharge {n}

/-- `⊤` is the full power-set sigma-algebra, not an unstated measurable
structure on the naturals. -/
def no_countably_additive_extension : Prop :=
  ¬ ∃ μ : @Measure ℕ ⊤,
    ∀ s : Set ℕ, s ∈ finiteCofinite → μ s = cofiniteCharge s

end Specs.D11.Ch01.AxiomCounterexamples
