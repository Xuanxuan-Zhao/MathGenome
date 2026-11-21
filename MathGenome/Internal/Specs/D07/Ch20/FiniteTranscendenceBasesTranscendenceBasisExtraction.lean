import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
Independent specification for the extraction step of
K07.20.finite_transcendence_bases (paper.tex:6119–6127).

A finite tuple generates as a FIELD: its intermediate-field adjoin is top.
An embedding of index sets selects a subtuple without repetitions of indices.
`IsTranscendenceBasis` asserts algebraic independence and maximality (in L).
`Module.Finite` is finite vector-space degree over the generated intermediate
field, and algebraicity is also stated explicitly. Neither finite generation
as a K-algebra nor algebraicity over K is assumed. The tuple may be empty.
-/

universe u v

namespace Specs.D07.Ch20.FiniteTranscendenceBasesTranscendenceBasisExtraction

/-- Extract a maximal independent subtuple from ANY finite field-generating tuple,
with finite algebraic degree above its rational function field. -/
def TranscendenceBasisExtraction : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (m : ℕ) (b : Fin m → L),
    IntermediateField.adjoin K (Set.range b) = ⊤ →
      ∃ (r : ℕ) (j : Fin r ↪ Fin m),
        IsTranscendenceBasis K (fun i => b (j i)) ∧
        Algebra.IsAlgebraic
          (IntermediateField.adjoin K (Set.range fun i => b (j i))) L ∧
        Module.Finite
          (IntermediateField.adjoin K (Set.range fun i => b (j i))) L

end Specs.D07.Ch20.FiniteTranscendenceBasesTranscendenceBasisExtraction
