import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal
import Mathlib.RingTheory.FinitePresentation
import Mathlib.Algebra.Module.FinitePresentation

/-! Independent specifications for paper.tex, KD-13 (lines 304–311).
Algebra finite type and algebra finite presentation are the hypotheses;
the conclusions concern the canonical module of relative differentials over B.
Both rings may be zero, and no Noetherian hypothesis is imposed.
-/

namespace Specs.AdvCommAlg.Differentials

universe u v

def finiteOfFiniteType : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B], Module.Finite B (KaehlerDifferential A B)

def finitePresentationOfFinitePresentation : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B],
    Module.FinitePresentation B (KaehlerDifferential A B)

end Specs.AdvCommAlg.Differentials
