import Mathlib.FieldTheory.Galois.Basic

open scoped BigOperators

universe u v

namespace Specs.GaloisFormalization.GH

/-- GH02. Every finite Galois extension has an element whose conjugates sum to one. -/
def TraceOne : Prop :=
  ∀ (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E],
    ∃ t : E, (∑ σ : Gal(E/k), σ t) = (1 : E)

end Specs.GaloisFormalization.GH
