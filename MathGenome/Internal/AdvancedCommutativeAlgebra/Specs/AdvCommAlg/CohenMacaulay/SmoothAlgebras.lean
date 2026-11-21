import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions

/-! CM-17, paper.tex:3888–3909. Smooth means finitely presented and formally
smooth. All commutative rings, including the zero ring, are admitted. The
Noetherian target instance is part of the conclusion. -/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def smoothNoetherianType : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A],
    _root_.Specs.AdvCommAlg.Smooth.smoothValue A B → IsNoetherianRing B

noncomputable def smoothCohenMacaulayType : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A],
    CohenMacaulayRingValue A →
    _root_.Specs.AdvCommAlg.Smooth.smoothValue A B →
    ∃ hB : IsNoetherianRing B, @CohenMacaulayRingValue B _ hB

end AdvCommAlg.CohenMacaulay.Specs
