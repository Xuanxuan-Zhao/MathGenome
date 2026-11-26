import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianCliffordInvariants
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRank

namespace LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianAlbertApplication

open _root_.LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
  (DiagramPresentation)
open TrialitarianCliffordInvariants (CubicVectorModel)

universe u

/-- The given trialitarian group, identified with the pointwise stabilizer of
its diagram cubic field in the Albert model, contains a noncentral
ground-field cocharacter. -/
def AlbertIsotropy : Prop :=
  ∀ (F E S : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field E] [Field S]
    [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
    [Module.Finite F E] [Algebra.IsSeparable F E] [IsSepClosure F S],
    Module.finrank F E = 3 →
    ∀ (G : AffineAlgebraicGroup F) (D : DiagramPresentation G E S),
      GeometricRadicals.IsSemisimple G →
      SimplyConnectedLattice.GeometricallySimplyConnected G →
      CubicVectorModel G D →
      ∃ c : CharacterDescent.Cocharacter G.val, ¬ RelativeRank.IsCentralCocharacter c

end LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianAlbertApplication
