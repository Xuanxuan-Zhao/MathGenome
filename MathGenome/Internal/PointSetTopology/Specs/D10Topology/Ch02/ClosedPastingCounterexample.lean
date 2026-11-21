import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions
import Mathlib.Topology.LocallyFinite
import Mathlib.Data.Set.Countable

/-! Independent specification for the countable closed-pasting example in
`paper.tex`, d10:02:cautions. All topologies below are the usual real topology
and its induced subspace topologies. -/

open Set
open scoped Topology

namespace Specs.D10Topology.Ch02.ClosedPastingCounterexample

/-- The original subset `{0} ∪ {1/n : n ≥ 1}` of the usual real line. -/
def carrier : Set ℝ := {x | x = 0 ∨ ∃ n : ℕ, 1 ≤ n ∧ x = 1 / (n : ℝ)}
abbrev Space : Type := carrier

def origin : Space := ⟨0, Or.inl rfl⟩

/-- Index `n` parametrizes the positive denominator `n+1`. -/
noncomputable def term (n : ℕ) : Space :=
  ⟨1 / ((n : ℝ) + 1), Or.inr ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), by simp⟩⟩

noncomputable def stepMap (x : Space) : ℝ := if x.val = 0 then 0 else 1

def pieces (x : Space) : Set Space := {x}

-- Canonical definitions may be shared with the implementation. Definition
-- bindings below check their values as well as their types.
def carrierType := Set ℝ
def carrierValue : carrierType :=
  {x | x = 0 ∨ ∃ n : ℕ, 1 ≤ n ∧ x = 1 / (n : ℝ)}
def originType : Type := Space
def originValue : originType := origin
def termType := ℕ → Space
noncomputable def termValue : termType := term
def mapType := Space → ℝ
noncomputable def mapValue : mapType := stepMap
def piecesType := Space → Set Space
def piecesValue : piecesType := fun x => {x}

def countable_space : Prop := Countable Space

def singleton_closed_cover : Prop :=
  (∀ x : Space, IsClosed (pieces x)) ∧ (⋃ x : Space, pieces x) = univ

def restrictions_continuous : Prop :=
  ∀ x : Space, Continuous (fun a : pieces x => stepMap a.val)

def map_values : Prop :=
  stepMap origin = 0 ∧ ∀ (n : ℕ) (hn : 1 ≤ n),
    stepMap ⟨1 / (n : ℝ), Or.inr ⟨n, hn, rfl⟩⟩ = 1

def interval_preimage : Prop :=
  stepMap ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2) = {origin}

def origin_not_open : Prop := ¬ IsOpen ({origin} : Set Space)

def map_not_continuous_at_origin : Prop := ¬ ContinuousAt stepMap origin

def map_not_continuous : Prop := ¬ Continuous stepMap

/-- Explicit pointwise failure, stronger than merely denying global local finiteness. -/
def not_locally_finite_at_origin : Prop :=
  ∀ N ∈ 𝓝 origin, {x : Space | (pieces x ∩ N).Nonempty}.Infinite

def cover_not_locally_finite : Prop := ¬ LocallyFinite pieces

end Specs.D10Topology.Ch02.ClosedPastingCounterexample
