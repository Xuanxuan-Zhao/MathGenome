import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ShiftCompactness
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ShiftSpaces

/-! Compactness, absence of isolated points, and total disconnectedness of
both binary symbolic spaces (paper.tex, Lemma `d13:17:shift-compactness`). -/
namespace D13Unified.Ch17.ShiftCompactness

open Set Topology
open D13Unified.Ch17.ShiftSpaces

theorem compactPlus : Specs.D13Unified.Ch17.ShiftCompactness.compactPlusStatement := by
  change CompactSpace OneSided
  exact inferInstance

theorem compact : Specs.D13Unified.Ch17.ShiftCompactness.compactStatement := by
  change CompactSpace TwoSided
  exact inferInstance

/-- A cylinder fixes only finitely many coordinates, leaving one coordinate
free in either of the infinite index sets used in the paper. -/
theorem exists_ne_mem_nhds (I : Type) [Infinite I] (s : I → Binary)
    (U : Set (I → Binary)) (hU : U ∈ 𝓝 s) : ∃ t ∈ U, t ≠ s := by
  classical
  obtain ⟨V, ⟨r, F, rfl⟩, hsV, hVU⟩ :=
    (cylinders_basis I).mem_nhds_iff.mp hU
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset F
  obtain ⟨b, hb⟩ := exists_ne (s j)
  refine ⟨Function.update s j b, hVU ?_, ?_⟩
  · intro k hk
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)]
    exact hsV k hk
  · intro h
    have hh := congrFun h j
    exact hb (by simpa using hh)

theorem noIsolatedPointsPlus :
    Specs.D13Unified.Ch17.ShiftCompactness.noIsolatedPointsPlusStatement := by
  intro s U hU
  exact exists_ne_mem_nhds ℕ s U hU

theorem noIsolatedPoints :
    Specs.D13Unified.Ch17.ShiftCompactness.noIsolatedPointsStatement := by
  intro s U hU
  exact exists_ne_mem_nhds ℤ s U hU

theorem totallyDisconnectedPlus :
    Specs.D13Unified.Ch17.ShiftCompactness.totallyDisconnectedPlusStatement := by
  change TotallyDisconnectedSpace OneSided
  exact inferInstance

theorem totallyDisconnected :
    Specs.D13Unified.Ch17.ShiftCompactness.totallyDisconnectedStatement := by
  change TotallyDisconnectedSpace TwoSided
  exact inferInstance

theorem connected_subsingletonPlus :
    Specs.D13Unified.Ch17.ShiftCompactness.connected_subsingletonPlusStatement := by
  intro C hC
  exact hC.isPreconnected.subsingleton

theorem connected_subsingleton :
    Specs.D13Unified.Ch17.ShiftCompactness.connected_subsingletonStatement := by
  intro C hC
  exact hC.isPreconnected.subsingleton

end D13Unified.Ch17.ShiftCompactness
