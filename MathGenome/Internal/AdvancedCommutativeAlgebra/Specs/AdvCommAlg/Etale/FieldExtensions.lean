import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-! Independent specification of ET-10, paper.tex, lines 1749–1775.
`Algebra.IsSeparable K L` means that every element has a separable minimal
polynomial; it implies algebraicity, including for infinite extensions.
Finite generation below is generation by a finite set as a *field*.
-/
namespace Specs.AdvCommAlg.Etale.FieldExtensions

universe u v

/-- No finite degree or finite generation hypothesis is imposed. -/
def separableFormallyEtale : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Algebra.IsSeparable K L → FormalLifting.formallyEtaleValue K L

/-- Finite degree is finiteness as a vector space, rather than cardinal finiteness. -/
def finiteEtaleIffSeparable : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], etaleValue K L ↔ Algebra.IsSeparable K L

/-- The bridge needed to apply the essentially finite type field criterion. -/
def finitelyGeneratedEssFiniteType : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (⊤ : IntermediateField K L).FG → Algebra.EssFiniteType K L

/-- Formal unramifiedness detects finite separable extensions among extensions
finitely generated as fields. -/
def finitelyGeneratedUnramifiedIff : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (⊤ : IntermediateField K L).FG →
      (FormalLifting.formallyUnramifiedValue K L ↔
        FiniteDimensional K L ∧ Algebra.IsSeparable K L)

end Specs.AdvCommAlg.Etale.FieldExtensions
