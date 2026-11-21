import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountableFan
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import Mathlib.Topology.Separation.GDelta

/-! The countable fan, paper.tex d10:08:fan. -/

open Set

namespace D10Topology.Ch08.CountableFan

abbrev Fan := Specs.D10Topology.Ch08.CountableFan.Fan
def apex : Fan := none
def point (n k : ℕ+) : Fan := some (n,k)
abbrev topology : TopologicalSpace Fan := Specs.D10Topology.Ch08.CountableFan.topology

instance : TopologicalSpace Fan := topology

theorem open_iff (U : Set Fan) : IsOpen U ↔
    (none ∈ U → ∀ n : ℕ+, ∃ K : ℕ+, ∀ k : ℕ+, K ≤ k → some (n,k) ∈ U) := Iff.rfl

theorem isolated_pairs (n k : ℕ+) : IsOpen ({some (n,k)} : Set Fan) := by
  intro h
  simp at h

theorem neighborhood_apex_iff (N : Set Fan) : Ch01.Neighborhood topology none N ↔
    none ∈ N ∧ ∀ n : ℕ+, ∃ K : ℕ+, ∀ k : ℕ+, K ≤ k → some (n,k) ∈ N := by
  constructor
  · rintro ⟨U, ho, hp, hUN⟩
    refine ⟨hUN hp, fun n => ?_⟩
    obtain ⟨K, hK⟩ := ho hp n
    exact ⟨K, fun k hk => hUN (hK k hk)⟩
  · rintro ⟨hp, hN⟩
    exact ⟨N, (fun _ => hN), hp, Subset.rfl⟩

theorem countable : Countable Fan := inferInstance

theorem t1 : T1Space Fan := by
  constructor
  intro x
  rw [← isOpen_compl_iff]
  cases x with
  | none =>
    intro h
    simp at h
  | some a =>
    intro _ n
    refine ⟨a.2 + 1, fun k hk => ?_⟩
    simp only [mem_compl_iff, mem_singleton_iff, Option.some.injEq]
    intro he
    have : a.2 + 1 ≤ a.2 := (congrArg Prod.snd he) ▸ hk
    exact (lt_irrefl _) (PNat.add_one_le_iff.mp this)

theorem singleton_gdelta (x : Fan) : IsGδ ({x} : Set Fan) := by
  let := t1
  have h := (Set.to_countable (({x} : Set Fan)ᶜ)).isGδ_compl
  simpa only [compl_compl] using h

/-- A proposed countable local base loses one point on its own branch. -/
theorem not_firstCountableAt_apex : ¬ Ch04.FirstCountableAt topology (none : Fan) := by
  classical
  rintro ⟨L, hc, hL⟩
  obtain ⟨U, hUL⟩ := Ch04.countable_localBase_enumeration (none : Fan) L hc hL
  have hU : ∀ i, Ch01.Neighborhood topology none (U i) := by
    intro i
    apply hL.1
    rw [← hUL]
    exact mem_range_self i
  have htail : ∀ n : ℕ+, ∃ k : ℕ+, some (n,k) ∈ U n.natPred := by
    intro n
    obtain ⟨K, hK⟩ := ((neighborhood_apex_iff _).mp (hU n.natPred)).2 n
    exact ⟨K, hK K le_rfl⟩
  choose k hk using htail
  let V : Set Fan := {x | ∀ n : ℕ+, x ≠ some (n, k n)}
  have hpV : (none : Fan) ∈ V := by simp [V]
  have hoV : IsOpen V := by
    intro _ n
    refine ⟨k n + 1, fun m hm => ?_⟩
    intro j he
    have he' : n = j ∧ m = k j := by simpa using he
    have hm' : k n + 1 ≤ k n := by simpa [← he'.1, he'.2] using hm
    exact (lt_irrefl _) (PNat.add_one_le_iff.mp hm')
  obtain ⟨W, hWL, hWV⟩ := hL.2 V ⟨V, hoV, hpV, Subset.rfl⟩
  obtain ⟨i, rfl⟩ := hUL.symm ▸ hWL
  let n : ℕ+ := ⟨i+1, Nat.succ_pos i⟩
  have hn : n.natPred = i := by simp [n, PNat.natPred]
  have hmem : some (n, k n) ∈ U i := hn ▸ hk n
  exact hWV hmem n rfl

theorem not_firstCountable : ¬ FirstCountable topology := by
  intro h
  exact not_firstCountableAt_apex (h none)

end D10Topology.Ch08.CountableFan
