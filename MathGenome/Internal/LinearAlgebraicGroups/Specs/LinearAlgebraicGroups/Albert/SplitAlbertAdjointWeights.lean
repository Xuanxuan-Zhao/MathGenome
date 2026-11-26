import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitFrameTorus
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.CharacterPairing

namespace LinearAlgebraicGroups.Albert.SplitAlbertAdjointWeightsSpecification

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs.SpinWeights
open LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open LinearAlgebraicGroups.Specs.CharacterPairing (absoluteRoots characterValue)
open LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus)
open LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal)
open SplitFrameTorusSpecification
open IntegralSmoothnessSpecification
open ShortDirectionSpecification (IntegralPresentation)

noncomputable section

/-- The short roots from the vector block and the two half-spin blocks. The two
parities of exterior indices together give all sixteen half-sums. -/
def shortRoots : Set CharacterExponents :=
  Set.range vectorWeight ∪ Set.range exteriorWeight

/-- The adjoint roots in the free diagonal Clifford coordinates. -/
def roots : Set CharacterExponents :=
  rootCharacters ∪ shortRoots

/-- The three families are individually distinct and together give 48 roots. -/
def RootCardinalities : Prop :=
  rootCharacters.ncard = 24 ∧ (Set.range vectorWeight).ncard = 8 ∧
    (Set.range exteriorWeight).ncard = 16 ∧ roots.ncard = 48

def RootsSpan : Prop := Submodule.span ℤ roots = ⊤

/-- Centrality and triviality are tested on all scheme-valued points and their pullbacks. -/
def HasTrivialCentre {R : Type} [CommRing R] (G : SpinSpecification.GroupScheme R) : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) (z : X ⟶ G.X),
    (∀ (Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X) (g : Y ⟶ G.X),
      (f ≫ z) * g = g * (f ≫ z)) → z = 1

/-- This assertion covers the split group over every commutative ring,
with arbitrary test schemes over that ring. -/
def UniversallyTrivialCentre {P : IntegralPresentation} (G : SplitGroup P) : Prop :=
  ∀ (R : Type) [CommRing R], HasTrivialCentre
    (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).mapGrp).obj G.group)

def IntegralCentre : Prop :=
  ∀ (P : IntegralPresentation) (G : SplitGroup P), UniversallyTrivialCentre G

/-- The fibre character coordinates are pulled back from the same integral
torus with its calibrated Laurent coordinates. -/
structure FibreCalibration {P : IntegralPresentation} {G : SplitGroup P} (T : FrameTorus G)
    (k : Type) [Field k] where
  points : ∀ R : TestAlgebra k, Points (T.fibre k).group.X R ≃* DiagonalPoints R
  characters : Additive (Character (T.fibre k).group) ≃ₗ[ℤ] CharacterExponents
  projection : ∀ (R : TestAlgebra k) (t : Points (T.fibre k).group.X R),
    ∃ z : ScalarPoints diagonalTorus (CommAlgCat.of ℤ R),
      z.left = t.left ≫ pullback.fst diagonalTorus.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ∧
      points R t = T.points _ z
  evaluation : ∀ (R : TestAlgebra k) (t : Points (T.fibre k).group.X R)
    (χ : Character (T.fibre k).group),
    characterValue χ R t =
      (Additive.toMul (evaluate (points R t) (characters (Additive.ofMul χ))) : Rˣ).val

def FibreCharacters : Prop :=
  ∀ {P : IntegralPresentation} {G : SplitGroup P} (T : FrameTorus G) (k : Type) [Field k],
    IsSplitTorus (T.fibre k).group ∧ Nonempty (FibreCalibration T k)

/-- The scheme-theoretic root set in the calibrated character coordinates. -/
def FibreWeights {P : IntegralPresentation} {G : SplitGroup P} (T : FrameTorus G)
    (k : Type) [Field k] : Prop :=
  IsSplitTorus (T.fibre k).group ∧ IsGeometricallyMaximal (T.fibre k) ∧
  ∃ C : FibreCalibration T k,
    Set.BijOn (fun χ : Character (T.fibre k).group => C.characters (Additive.ofMul χ))
      (absoluteRoots (T.fibre k)) roots

/-- The fibre assertions use the same integral presentation and the same
frame torus throughout. -/
def Statement : Prop :=
  ∀ (P : IntegralPresentation) (G : SplitGroup P),
    (∀ (k : Type) [Field k] [IsAlgClosed k], IsReductive (algebraicFiber G k)) →
    ∃ T : FrameTorus G, T.InOrderedStabilizer ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k],
        FibreWeights T k ∧ IsSemisimple (algebraicFiber G k) ∧
          HasTrivialCentre (geometricFiber G k)) ∧
      UniversallyTrivialCentre G

end

end LinearAlgebraicGroups.Albert.SplitAlbertAdjointWeightsSpecification
