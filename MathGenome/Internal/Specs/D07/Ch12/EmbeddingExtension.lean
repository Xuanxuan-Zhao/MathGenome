import MathGenome.Internal.Specs.D07.Ch12.MinpolyDivisibility
import MathGenome.Internal.Specs.D07.Ch12.SimpleEmbeddings
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
Independent specification for K07.12.embedding_extension
(paper.tex:3687–3697; chapters/M07.12.tex:146–156).

The given extension L/E has its specified `Algebra E L`. The embedding σ
is an arbitrary unital field homomorphism, and its actual coefficient map
is used in the splitting hypothesis. No previously chosen E-action on Ω
is required. The resulting injective field map agrees with σ on every
element of E. Both statements allow infinite algebraic extensions and
arbitrary characteristic, with the three fields in independent universes.
-/

universe u v w

namespace Specs.D07.Ch12.EmbeddingExtension

/-- Splitting of the images of all minimal polynomials suffices to extend
the prescribed embedding, without assuming the target algebraically closed. -/
def ExtensionOfSplitting : Prop :=
  ∀ (E : Type u) (L : Type v) (Ω : Type w)
    [Field E] [Field L] [Field Ω] [Algebra E L] [Algebra.IsAlgebraic E L]
    (σ : E →+* Ω),
    (∀ a : L, ((minpoly E a).map σ).Splits) →
      ∃ τ : L →+* Ω, Function.Injective τ ∧
        ∀ x : E, τ (algebraMap E L x) = σ x

/-- Every embedding of the base into an algebraically closed field extends
to the entire algebraic extension, with the prescribed restriction. -/
def ExtensionIntoAlgebraicallyClosed : Prop :=
  ∀ (E : Type u) (L : Type v) (Ω : Type w)
    [Field E] [Field L] [Field Ω] [Algebra E L] [Algebra.IsAlgebraic E L]
    [IsAlgClosed Ω] (σ : E →+* Ω),
      ∃ τ : L →+* Ω, Function.Injective τ ∧
        ∀ x : E, τ (algebraMap E L x) = σ x

end Specs.D07.Ch12.EmbeddingExtension
