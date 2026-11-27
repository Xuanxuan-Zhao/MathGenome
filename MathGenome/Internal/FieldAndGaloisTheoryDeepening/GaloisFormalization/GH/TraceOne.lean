import Mathlib.RingTheory.Trace.Basic

open scoped BigOperators

universe u v

namespace GaloisFormalization.GH

/-- The sum of all Galois conjugates of some element of a finite Galois extension is one. -/
theorem exists_trace_one (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] :
    ∃ t : E, (∑ σ : Gal(E/k), σ t) = (1 : E) := by
  obtain ⟨t, ht⟩ := Algebra.trace_surjective k E (1 : k)
  refine ⟨t, ?_⟩
  rw [← trace_eq_sum_automorphisms (K := k) t, ht, map_one]

end GaloisFormalization.GH
