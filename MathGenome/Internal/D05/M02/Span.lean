import MathGenome.Internal.Specs.D05.M02.Span
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! K05.02.span: finite linear combinations and their canonical subspace. -/

namespace D05.M02.Span

/-- The paper's span, represented by the canonical Mathlib submodule. -/
abbrev span (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (S : Set V) : Submodule K V := Submodule.span K S

/-- Forget the zero extension of the finitely supported coefficient function
in Mathlib's characterization; conversely every finite sum lies in the span. -/
theorem mem_span_iff_finite_sum : Specs.D05.M02.Span.mem_span_iff_finite_sum := by
  intro K V _ _ _ S x
  constructor
  · intro hx
    obtain ⟨a, F, hFS, _, hsum⟩ :=
      Submodule.mem_span_iff_exists_finset_subset.mp hx
    exact ⟨F, a, hFS, hsum⟩
  · rintro ⟨F, a, hFS, rfl⟩
    exact Submodule.sum_mem _ fun s hs =>
      (Submodule.span K S).smul_mem (a s) (Submodule.subset_span (hFS hs))

theorem empty_sum : Specs.D05.M02.Span.empty_sum := by
  intro K V _ _ _ a
  exact Finset.sum_empty

theorem zero_mem_span : Specs.D05.M02.Span.zero_mem_span := by
  intro K V _ _ _ S
  exact (Submodule.span K S).zero_mem

theorem add_mem_span : Specs.D05.M02.Span.add_mem_span := by
  intro K V _ _ _ S x y hx hy
  exact (Submodule.span K S).add_mem hx hy

theorem smul_mem_span : Specs.D05.M02.Span.smul_mem_span := by
  intro K V _ _ _ S a x hx
  exact (Submodule.span K S).smul_mem a hx

theorem smul_finite_sum : Specs.D05.M02.Span.smul_finite_sum := by
  intro K V _ _ _ F a b
  simp only [Finset.smul_sum, smul_smul]

theorem finite_combinations_subspace : Specs.D05.M02.Span.finite_combinations_subspace := by
  intro K V _ _ _ S
  refine ⟨Submodule.span K S, ?_⟩
  ext x
  exact mem_span_iff_finite_sum S x

end D05.M02.Span
