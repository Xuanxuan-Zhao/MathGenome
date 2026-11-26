import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingSingletonRootSL2

open CharacterDescent (Character)
open CharacterPairing (absoluteRoots)
open GeometricRadicals (IsSplitReductive IsSplitTorus IsTorus baseChangedSubgroup)
open QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open RankOneFlag (IsGeometricallyMaximal)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Relative.RelativeChambers (relativeRoots)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open RootGroups (HasScalarAction IsRootSubgroup)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open TrialitarianFixedRootSL2 (RankOne)
open Unipotent (baseChangedAlgebraicGroup)

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

/-- The fibre of restriction above the base-changed character consists of a single
absolute root for a maximal torus through the given split torus. -/
def HasSingleAbsoluteRoot (S : ClosedSubgroup G.val) (a : Character S.group) : Prop :=
  ∃ (T : ClosedSubgroup G.val) (i : S.group ⟶ T.group),
    IsTorus T.group ∧ IsGeometricallyMaximal T ∧ i ≫ T.inclusion = S.inclusion ∧
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
      (_ : IsGalois F K)
      (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
      (e : MultiplicativeComparison F K),
      IsSplitReductive (baseChangedAlgebraicGroup K G) ∧
      IsSplitTorus ((groupBaseChange F K).obj T.group) ∧
      PreservesUnits e ∧
      ∃! b : Character ((groupBaseChange F K).obj T.group),
        b ∈ absoluteRoots (baseChangedSubgroup K T hT) ∧
          (groupBaseChange F K).map i ≫ b = (groupBaseChange F K).map a ≫ e.inv

/-- The two transvections have the specified opposite weights on the original
split torus. The marked diagonal gives the two opposite contracting radicals. -/
def IsRankOneAt (S : ClosedSubgroup G.val) (a : relativeRoots S) (L : RankOne S) : Prop :=
  HasScalarAction S a.val (L.upper.hom ≫ L.positive.inclusion) ∧
  HasScalarAction S a.val⁻¹ (L.lower.hom ≫ L.negative.inclusion) ∧
  TrialitarianRelativeRoots.RankOne.HasOppositeRadicals L

/-- An actual relative root with a singleton absolute fibre has a marked
split rank-one subgroup. -/
def SingletonRootSL2 : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ (S : ClosedSubgroup G.val), IsMaximalSplitTorus S →
      ∀ a : relativeRoots S, HasSingleAbsoluteRoot S a.val →
        ∃ L : RankOne S, IsRankOneAt S a L

/-- In a split group the given maximal split torus is geometrically maximal
and each root has a singleton fibre. The two marked subgroups are the
absolute root subgroups at that torus. -/
def SplitCase : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → IsSplitReductive G →
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      IsGeometricallyMaximal S ∧
      ∀ a : relativeRoots S, HasSingleAbsoluteRoot S a.val ∧
        ∃ L : RankOne S, IsRankOneAt S a L ∧
          IsRootSubgroup S L.positive a.val ∧ IsRootSubgroup S L.negative a.val⁻¹

/-- Rational conjugation transports the actual relative root by pullback
along the inverse of the induced torus isomorphism and preserves its
finite singleton fibre condition. -/
def ConjugationInvariance : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ S S' : ClosedSubgroup G.val, IsMaximalSplitTorus S → IsMaximalSplitTorus S' →
      ∀ (g : 𝟙_ (SchemeOver F) ⟶ G.val.X) (e : S.group ≅ S'.group),
        (let c := toUnit S.group.X ≫ g
         (e.hom ≫ S'.inclusion).hom.hom = c * S.inclusion.hom.hom * c⁻¹) →
        ∀ a : relativeRoots S,
          let b : Character S'.group := e.inv ≫ a.val
          b ∈ relativeRoots S' ∧ (HasSingleAbsoluteRoot S a.val ↔ HasSingleAbsoluteRoot S' b)

end

end LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingSingletonRootSL2
