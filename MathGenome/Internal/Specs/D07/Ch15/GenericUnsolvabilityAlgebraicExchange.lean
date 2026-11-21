import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.Algebraic.Defs

/-!
Independent statements for the exchange argument in paper.tex:4459–4463
and paper.tex:6125–6129 (K07.15.generic_unsolvability and
K07.20.finite_transcendence_bases).

`Algebra B M` specifies an embedding of fields; `IntermediateField.adjoin`
is the generated field, rather than merely the generated subring. Algebraicity
is elementwise and imposes no finite-degree assumption on the ambient field.
The finite generating tuple may have repetitions and algebraic dependencies.
The natural-number indices include zero, so the empty generating tuple is allowed.
-/

universe u v

namespace Specs.D07.Ch15.GenericUnsolvabilityAlgebraicExchange

/-- One-element exchange, with no characteristic restriction. -/
def AlgebraicExchange : Prop :=
  ∀ (B : Type u) (M : Type v) [Field B] [Field M] [Algebra B M] (x y : M),
    Transcendental B x →
    IsAlgebraic (IntermediateField.adjoin B {y}) x →
    IsAlgebraic (IntermediateField.adjoin B {x}) y

/-- Any finite independent tuple has length at most the length of a field
 generating tuple over which the entire ambient extension is algebraic. -/
def IndependentCardinalityBound : Prop :=
  ∀ (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M]
    (s t : ℕ) (c : Fin s → M) (a : Fin t → M),
    Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range c)) M →
    AlgebraicIndependent K a → t ≤ s

/-- In particular there are no `s + 1` independent elements, including when `s = 0`. -/
def NoIndependentSuccessor : Prop :=
  ∀ (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M]
    (s : ℕ) (c : Fin s → M),
    Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range c)) M →
    ∀ a : Fin (s + 1) → M, ¬ AlgebraicIndependent K a

end Specs.D07.Ch15.GenericUnsolvabilityAlgebraicExchange
