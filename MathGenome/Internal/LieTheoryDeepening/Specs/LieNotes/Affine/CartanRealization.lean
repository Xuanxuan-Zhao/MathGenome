import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanData
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.AffineSimpleTriples

/-! The realization in KM09 uses the Cartan submodule and the simple roots
of the LO09–LO10 affine Lie algebra. -/

namespace Specs.LieNotes.Affine.CartanRealization

open _root_.RepTheorySurvey.Affine
open _root_.LieAlgebrasAndRepresentations.HighestRoot (simpleRoots)
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open _root_.Specs.LieAlgebrasAndRepresentations.TraceCriterion (killingForm_value)
open _root_.Specs.RepTheorySurvey.Affine.TriangularRootSpaces (affineCartan_value)
open _root_.LieAlgebrasAndRepresentations (rootSet rootForm)
open _root_.Specs.LieNotes.Contragredient.CartanData
open scoped Classical

universe u

/-- The integer matrix of the actual affine simple roots and coroots is
symmetrizable and is minimally realized on the affine Cartan. -/
def AffineCartanRealization : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    [H.IsCartanSubalgebra] (φ : Direction H), B.IsNormalized H → Regular H φ →
    ∀ (θ : Module.Dual ℂ H), IsHighestFiniteRoot H φ θ →
    ∃ indexFintype : Fintype (simpleRoots H φ),
      letI := indexFintype
      ∃ (A : Matrix (AffineSimpleIndex H φ) (AffineSimpleIndex H φ) ℤ)
        (R : Realization A (affineCartan_value B H)),
        (∀ i, (R.h i : AffineAlgebra B) = affineSimpleH B H θ i) ∧
        (∀ i, R.α i = affineSimpleRoot B H θ i) ∧
        IsGeneralizedCartanMatrix A ∧ IsSymmetrizable A ∧ R.IsMinimal ∧
        (A.map fun z : ℤ => (z : ℂ)).rank = Fintype.card (simpleRoots H φ)

/-- Scaling the Killing form by half the Killing-dual squared length of a long
root produces the normalization used in the loop bracket. -/
def ExistsNormalizedForm : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra],
    ∃ (B : InvariantForm G) (γ : rootSet H),
      IsLongRoot γ ∧ B.form = (rootForm H γ.val γ.val / 2) • killingForm_value ℂ G ∧
        B.IsNormalized H

end Specs.LieNotes.Affine.CartanRealization
