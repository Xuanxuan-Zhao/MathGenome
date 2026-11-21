import MathGenome.Internal.Specs.D05.M02.Basis
import Mathlib.LinearAlgebra.Basis.Basic
import MathGenome.Internal.D05.M02.Independence

/-! K05.02.basis: independent spanning families and unique finite-support coordinates. -/

namespace D05.M02.Basis

/-- A basis is the canonical Mathlib basis over the stated scalar field. -/
abbrev basis (K V I : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  Module.Basis I K V

theorem basis_iff_independent_span : Specs.D05.M02.Basis.basis_iff_independent_span := by
  intro K V I _ _ _ v
  constructor
  · rintro ⟨b, hb⟩
    have hfamily : (b : I → V) = v := funext hb
    exact ⟨hfamily ▸ b.linearIndependent, hfamily ▸ b.span_eq⟩
  · rintro ⟨hli, hspan⟩
    exact ⟨Module.Basis.mk hli hspan.ge, Module.Basis.mk_apply hli hspan.ge⟩

/-- Spanning gives a preimage under linear combination. Subtracting two such
preimages gives a zero relation, so independence gives uniqueness. Conversely,
uniqueness for the zero vector forces every zero relation to have zero coefficients. -/
theorem independent_span_iff_unique_expansion :
    Specs.D05.M02.Basis.independent_span_iff_unique_expansion := by
  intro K V I _ _ _ v
  change (LinearIndependent K v ∧ Submodule.span K (Set.range v) = ⊤) ↔
    ∀ x : V, ∃! a : I →₀ K, Finsupp.linearCombination K v a = x
  constructor
  · rintro ⟨hli, hspan⟩ x
    obtain ⟨a, ha⟩ :=
      ((span_range_eq_top_iff_surjective_finsuppLinearCombination K (v := v)).mp hspan) x
    refine ⟨a, ha, ?_⟩
    intro c hc
    have hzero : Finsupp.linearCombination K v (c - a) = 0 := by
      rw [map_sub, hc, ha, sub_self]
    have hcoeff : ∀ i, (c - a) i = 0 :=
      (D05.M02.Independence.independent_iff_finsupp_relation v).mp hli (c - a) hzero
    exact sub_eq_zero.mp (Finsupp.ext hcoeff)
  · intro h
    constructor
    · rw [linearIndependent_iff]
      intro a ha
      obtain ⟨c, _, huniq⟩ := h 0
      exact (huniq a ha).trans (huniq 0 (map_zero _)).symm
    · apply (span_range_eq_top_iff_surjective_finsuppLinearCombination K (v := v)).mpr
      intro x
      obtain ⟨a, ha, _⟩ := h x
      exact ⟨a, ha⟩

theorem basis_iff_unique_expansion : Specs.D05.M02.Basis.basis_iff_unique_expansion := by
  intro K V I _ _ _ v
  exact (basis_iff_independent_span v).trans (independent_span_iff_unique_expansion v)

theorem repr_unique_expansion : Specs.D05.M02.Basis.repr_unique_expansion := by
  intro K V I _ _ _ b x
  change Finsupp.linearCombination K b (b.repr x) = x ∧
    ∀ a : I →₀ K, Finsupp.linearCombination K b a = x → a = b.repr x
  refine ⟨b.linearCombination_repr x, ?_⟩
  intro a ha
  calc
    a = b.repr (Finsupp.linearCombination K b a) := (b.repr_linearCombination a).symm
    _ = b.repr x := congrArg b.repr ha

end D05.M02.Basis
