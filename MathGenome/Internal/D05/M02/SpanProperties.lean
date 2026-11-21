import MathGenome.Internal.D05.M02.Span
import MathGenome.Internal.Specs.D05.M02.SpanProperties

/-! K05.02.span_properties: the universal property of span and its consequences. -/

namespace D05.M02.SpanProperties

theorem subset_span : Specs.D05.M02.SpanProperties.subset_span := by
  intro K V _ _ _ S
  exact Submodule.subset_span

theorem span_le_iff : Specs.D05.M02.SpanProperties.span_le_iff := by
  intro K V _ _ _ S U
  exact Submodule.span_le

theorem span_mono : Specs.D05.M02.SpanProperties.span_mono := by
  intro K V _ _ _ S T hST
  exact (span_le_iff S (Submodule.span K T)).mpr
    (Set.Subset.trans hST (subset_span T))

theorem span_idempotent : Specs.D05.M02.SpanProperties.span_idempotent := by
  intro K V _ _ _ S
  apply le_antisymm
  · exact (span_le_iff (Submodule.span K S : Set V) (Submodule.span K S)).mpr
      (Set.Subset.refl _)
  · exact subset_span (Submodule.span K S : Set V)

theorem span_empty : Specs.D05.M02.SpanProperties.span_empty := by
  intro K V _ _ _
  ext x
  change x ∈ Submodule.span K (∅ : Set V) ↔ x = 0
  rw [Submodule.span_empty]
  exact Submodule.mem_bot K

end D05.M02.SpanProperties
