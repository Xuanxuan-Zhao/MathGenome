import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

variable {k : Type u} [Field k]

/-- The underlying scheme morphism of the identity section. -/
abbrev groupIdentitySection (G : Specs.GroupScheme k) :
    Spec (CommRingCat.of k) ⟶ G.X.left :=
  (η[G.X]).left

/-- The underlying point of the identity section. -/
abbrev groupIdentityPoint (G : Specs.GroupScheme k) : G.X.left :=
  groupIdentitySection G (IsLocalRing.closedPoint k)

/-- Smoothness over the base field at the identity. -/
def SmoothAtIdentity (G : Specs.GroupScheme k) : Prop :=
  (G.X.hom.stalkMap (groupIdentityPoint G)).hom.FormallySmooth

abbrev IdentityLocalRing (G : Specs.GroupScheme k) :=
  G.X.left.presheaf.stalk (groupIdentityPoint G)

abbrev IdentityResidueField (G : Specs.GroupScheme k) :=
  IsLocalRing.ResidueField (IdentityLocalRing G)

/-- The map from the base field to the residue field at the identity. -/
abbrev identityResidueMap (G : Specs.GroupScheme k) :
    CommRingCat.of k ⟶ G.X.left.residueField (groupIdentityPoint G) :=
  (Scheme.Spec.residueFieldIsoOfField (G.X.hom (groupIdentityPoint G))).inv ≫
    G.X.hom.residueFieldMap (groupIdentityPoint G)

abbrev identityResidueRingHom (G : Specs.GroupScheme k) : k →+* IdentityResidueField G :=
  (identityResidueMap G).hom

/-- The Zariski tangent space at a point, over its residue field. -/
abbrev ZariskiTangentSpace (X : Scheme.{u}) (x : X) :=
  Module.Dual (IsLocalRing.ResidueField (X.presheaf.stalk x))
    (IsLocalRing.CotangentSpace (X.presheaf.stalk x))

abbrev IdentityTangentSpace (G : Specs.GroupScheme k) :=
  ZariskiTangentSpace G.X.left (groupIdentityPoint G)

namespace Specs

def GroupSmoothnessCriteria : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme k) [LocallyOfFiniteType G.X.hom],
    (Smooth G.X.hom ↔ GeometricallyReduced G.X.hom) ∧
    (Smooth G.X.hom ↔ SmoothAtIdentity G)

def AffineGroupSmoothnessCriteria : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k),
    (Smooth G.1.X.hom ↔ GeometricallyReduced G.1.X.hom) ∧
    (Smooth G.1.X.hom ↔ SmoothAtIdentity G.1)

def SmoothOfReducedOverPerfectField : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (G : GroupScheme k)
    [LocallyOfFiniteType G.X.hom], IsReduced G.X.left → Smooth G.X.hom

def SmoothAtIdentityBaseChange : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme k) [LocallyOfFiniteType G.X.hom],
    SmoothAtIdentity ((groupBaseChange k K).obj G) ↔ SmoothAtIdentity G

def SmoothAtRationalPoint : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme k) [LocallyOfFiniteType G.X.hom]
    (p : 𝟙_ (SchemeOver k) ⟶ G.X),
    (G.X.hom.stalkMap (p.left (IsLocalRing.closedPoint k))).hom.FormallySmooth ↔
      SmoothAtIdentity G

def SmoothAtGeometricPoint : Prop :=
  ∀ (k Ω : Type u) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (G : GroupScheme k) [LocallyOfFiniteType G.X.hom]
    (p : 𝟙_ (SchemeOver Ω) ⟶ ((groupBaseChange k Ω).obj G).X),
    (((groupBaseChange k Ω).obj G).X.hom.stalkMap
      (p.left (IsLocalRing.closedPoint Ω))).hom.FormallySmooth ↔ SmoothAtIdentity G

def IdentityResidueFieldOverBase : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme k), IsIso (identityResidueMap G)

def ZariskiTangentDimension : Prop :=
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X),
    let A := X.presheaf.stalk x
    let n := Module.finrank (IsLocalRing.ResidueField A) (ZariskiTangentSpace X x)
    n = (IsLocalRing.maximalIdeal A).spanFinrank ∧
      ringKrullDim A ≤ (n : WithBot ℕ∞)

def IdentityTangentDimension : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme k) [LocallyOfFiniteType G.X.hom],
    letI : Module k (IdentityTangentSpace G) :=
      Module.compHom (IdentityTangentSpace G) (identityResidueRingHom G)
    let n := Module.finrank k (IdentityTangentSpace G)
    n = (IsLocalRing.maximalIdeal (IdentityLocalRing G)).spanFinrank ∧
      ringKrullDim (IdentityLocalRing G) ≤ (n : WithBot ℕ∞)

end Specs

end

end LinearAlgebraicGroups
