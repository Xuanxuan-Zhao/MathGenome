import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorRing
import Mathlib.RingTheory.Noetherian.Defs

namespace GaloisFormalization.PV.Specs

universe u

/-- The differential domain assertion of Lemma 1.3. -/
def simpleDifferentialDomain : Prop :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
    (D : operator .differential R), isSimple D → IsDomain R

end GaloisFormalization.PV.Specs
