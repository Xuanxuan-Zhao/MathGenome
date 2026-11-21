import MathGenome.Internal.Specs.D07.Ch06.CompositionSeriesDefinition

/-!
Existence and Jordan–Hölder uniqueness, paper.tex:1137–1160.
The canonical `Series` requires only adjacent normality. The equivalence
of the finite index types pairs every quotient factor exactly once, so
repeated isomorphism classes keep their multiplicities. No choice of
representatives for isomorphism classes is part of the statement.
-/
namespace Specs.D07.Ch06.JordanHolderExtension

open Specs.D07.Ch06.CompositionSeriesDefinition
universe u

def CompositionSeriesExists : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Nonempty (Series G)

def JordanHolder : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (s t : Series G),
    s.length = t.length ∧
      ∃ e : Fin s.length ≃ Fin t.length,
        ∀ i, Nonempty (factorValue s i ≃* factorValue t (e i))

end Specs.D07.Ch06.JordanHolderExtension
