import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! SN-13 (paper.tex:4354–4378). Normality is tested at every prime,
including for nondomain rings and the zero ring. Noetherianity of the
étale algebra is a conclusion rather than an added hypothesis. -/
universe u
namespace AdvCommAlg.Normality.Specs

/-- Ascent of normality, including Noetherianity from finite presentation. -/
def etaleNormalAscentType : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.Etale A B],
    IsNormalValue A → ∃ hB : IsNoetherianRing B, @IsNormalValue B _ hB

/-- Descent for faithful flatness of the specified étale structural map. -/
def etaleNormalDescentType : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.Etale A B] [Module.FaithfullyFlat A B],
    (∃ hB : IsNoetherianRing B, @IsNormalValue B _ hB) → IsNormalValue A

end AdvCommAlg.Normality.Specs
