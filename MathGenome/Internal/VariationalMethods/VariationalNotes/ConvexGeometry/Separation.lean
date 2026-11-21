import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Separation

open Set

universe u

namespace VariationalNotes.ConvexGeometry

/-- The open case of the manuscript's geometric separation theorem. -/
theorem open_separation : Specs.open_separation.{u} := by
  intro E _ _ _ _ _ _ _ A B hA hB hAc hBc hdis hAo
  obtain ⟨l, α, hlA, hlB⟩ :=
    geometric_hahn_banach_open hAc hAo hBc hdis
  refine ⟨l, α, ?_, hlA, hlB⟩
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  intro hl
  have hlt := lt_of_lt_of_le (hlA a ha) (hlB b hb)
  simp [hl] at hlt

/-- The compact–closed case, expressed using finite real suprema and infima. -/
theorem compact_closed_separation : Specs.compact_closed_separation.{u} := by
  intro E _ _ _ _ _ _ _ A B hA hB hAc hBc hdis hAk hBcl
  obtain ⟨l, α, β, hlA, hαβ, hlB⟩ :=
    geometric_hahn_banach_compact_closed hAc hAk hBc hBcl hdis
  have hupper : ∀ x ∈ l '' A, x ≤ α := by
    rintro x ⟨a, ha, rfl⟩
    exact (hlA a ha).le
  have hlower : ∀ x ∈ l '' B, β ≤ x := by
    rintro x ⟨b, hb, rfl⟩
    exact (hlB b hb).le
  refine ⟨l, ?_, ⟨α, hupper⟩, ⟨β, hlower⟩, ?_⟩
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    intro hl
    have hlt := (hlA a ha).trans (hαβ.trans (hlB b hb))
    simp [hl] at hlt
  · exact (csSup_le (hA.image l) hupper).trans_lt
      (hαβ.trans_le (le_csInf (hB.image l) hlower))

end VariationalNotes.ConvexGeometry
