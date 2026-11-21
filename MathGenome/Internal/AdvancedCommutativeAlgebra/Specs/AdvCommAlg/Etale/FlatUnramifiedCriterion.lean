import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal
import Mathlib.RingTheory.Flat.Basic

/-! Independent specification of ET-12, paper.tex:1821–1881.
Finite presentation is required over the specified base. No Noetherian,
nontriviality, or finiteness hypothesis on the base ring is imposed.
-/
namespace Specs.AdvCommAlg.Etale

universe u v

/-- An algebra is étale exactly when it is finitely presented, flat as a
module over its base, and has zero relative Kähler differentials.
Subsingleton expresses vanishing of the entire differential module.
Both rings may be zero rings. -/
def etaleIffFinitePresentationFlatOmega : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    etaleValue A B ↔
      Algebra.FinitePresentation A B ∧ Module.Flat A B ∧
        Subsingleton (Differentials.omegaValue A B)

end Specs.AdvCommAlg.Etale
