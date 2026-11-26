import Specs.LinearAlgebraicGroups.Arithmetic.StrongApproximation
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import LinearAlgebraicGroups.Arithmetic.AnisotropicSufficiency
import LinearAlgebraicGroups.Arithmetic.IsotropicSufficiency
import LinearAlgebraicGroups.Arithmetic.NoncompactnessNecessary
import LinearAlgebraicGroups.Arithmetic.SimpleConnectednessNecessary
import Mathlib.AlgebraicGeometry.Artinian
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.Specs
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Arithmetic.StrongApproximation

open Specs.Arithmetic.AnisotropicClassicalApproximation (GloballyAnisotropic)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsSemisimple identitySubgroup)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)

open private isReduced_of_smooth_over_field from
  LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private isIso_of_schemeIso from
  LinearAlgebraicGroups.Reductive.GeometricRadicals

open private arithmetic_absolute_simplicity from
  LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo

private theorem baseChangeZero {K L : Type u} [Field K] [Field L] [Algebra K L]
    {G : GroupScheme K} (hG : IsZero G) : IsZero ((groupBaseChange K L).obj G) := by
  let e := Functor.Monoidal.εIso (baseChange K L)
  let f : (groupBaseChange K L).obj (Grp.trivial (SchemeOver K)) ⟶
      Grp.trivial (SchemeOver L) := default
  have hf : f.hom.hom = e.inv := toUnit_unique _ _
  have : IsIso f.hom.hom := hf ▸ inferInstanceAs (IsIso e.inv)
  let ef := Grp.mkIso (asIso f.hom.hom) (IsMonHom.one_hom (f := f.hom.hom))
    (IsMonHom.mul_hom (f := f.hom.hom))
  exact (Grp.isZero_trivial _).of_iso
    ((groupBaseChange K L).mapIso (hG.iso (Grp.isZero_trivial _)) ≪≫ ef)

private theorem positiveDimension {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (hG : AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G) :
    0 < topologicalKrullDim G.val.X.left := by
  by_contra! hd
  let : Smooth G.val.X.hom := hG.1.1
  let : GeometricallyConnected G.val.X.hom := hG.1.2.1
  let : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  let : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  let : IsLocallyArtinian G.val.X.left := IsLocallyArtinian.of_topologicalKrullDim_le_zero hd
  let : DiscreteTopology G.val.X.left := IsLocallyArtinian.discreteTopology
  let : Subsingleton G.val.X.left := subsingleton_of_preconnected_totallyDisconnected
  let : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  let e := identitySubgroup G
  let : IsClosedImmersion e.inclusion.hom.hom.left := e.isClosedImmersion
  let : Surjective e.inclusion.hom.hom.left :=
    ⟨fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ x⟩⟩
  let : IsIso e.inclusion.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso e.inclusion := isIso_of_schemeIso _
  exact hG.2.1 (baseChangeZero ((Grp.isZero_trivial _).of_iso (asIso e.inclusion).symm))

/-- Strong approximation over global fields is equivalent to algebraic simple
connectedness and noncompactness of the product at the omitted places. -/
theorem criterion :
    Specs.Arithmetic.StrongApproximation.Criterion.{u, v} := by
  classical
  intro K _ D G i S hG hS
  have hss : IsSemisimple G := hG.1
  constructor
  · intro hDense
    constructor
    · by_contra hsc
      obtain ⟨B, hB, hBne, havoid⟩ :=
        SimpleConnectednessNecessary.simplyConnectednessNecessary D G hss hsc i S hS
      have hOpen := (AdelicGroups.adelicBasis D i S).isOpen hB
      obtain ⟨x, ⟨g, hg⟩, hx⟩ := hDense.exists_mem_open hOpen hBne
      exact havoid g ⟨x, hx, hg⟩
    · intro hCompact
      have hConnected := @GeometricallyConnected.connectedSpace_of_subsingleton _ _ G.val.X.hom
        hss.2.1
      exact (NoncompactnessNecessary.compactInsidePrecludesStrongApproximation D i S hS
        hss.1 hConnected (positiveDimension hG) hCompact).2.2 hDense
  · rintro ⟨hsc, hNoncompact⟩
    by_cases hIso : ∃ c : Cocharacter G.val, IsNoncentral c
    · exact IsotropicSufficiency.strongApproximation D G i
        (arithmetic_absolute_simplicity hG) hsc hIso S hS
    · exact AnisotropicSufficiency.strongApproximation D G hG hsc
        (show GloballyAnisotropic G from hIso) i S hS hNoncompact

end LinearAlgebraicGroups.Arithmetic.StrongApproximation
