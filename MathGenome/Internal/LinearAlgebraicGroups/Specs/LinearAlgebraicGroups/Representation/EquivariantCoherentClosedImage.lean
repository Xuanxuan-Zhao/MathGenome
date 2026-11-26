import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory Opposite
open CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.EquivariantCoherentClosedImage

open EquivariantAffineModules
noncomputable section

variable {k : Type u} [Field k] {T : GroupScheme k} {X Z : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Z}

/-- Equivariance of a sheaf map, evaluated over every scheme over the field. -/
def IsEquivariantOnTests {F H : X.left.Modules}
    (L : Linearization a F) (K : Linearization a H) (m : F ⟶ H) : Prop :=
  ∀ (S : SchemeOver k) (t : S ⟶ T.X) (x : S ⟶ X),
    (transport a L.iso t x).hom ≫ (Scheme.Modules.pullback (actOn a t x).left).map m =
      (Scheme.Modules.pullback x.left).map m ≫ (transport a K.iso t x).hom

/-- Data with underlying sheaves given by the two actual adjoint functors. -/
structure ClosedImageData (i : Z ⟶ X) (a : ModObj T.X X) (b : ModObj T.X Z) where
  pushCoherent (H : EquivariantCoherent b) :
    ((Scheme.Modules.pushforward i.left).obj H.sheaf).IsFinitePresentation
  pushLinearization (H : EquivariantCoherent b) :
    Linearization a ((Scheme.Modules.pushforward i.left).obj H.sheaf)
  pullCoherent (F : EquivariantCoherent a) : (Pull i F.sheaf).IsFinitePresentation
  pullLinearization (F : EquivariantCoherent a) : Linearization b (Pull i F.sheaf)
  pushClasses : GZero b →ₗ[CharacterRing T] GZero a

def ClosedImageData.push {i : Z ⟶ X} (D : ClosedImageData i a b)
    (H : EquivariantCoherent b) : EquivariantCoherent a :=
  ⟨_, D.pushCoherent H, D.pushLinearization H⟩

def ClosedImageData.pull {i : Z ⟶ X} (D : ClosedImageData i a b)
    (F : EquivariantCoherent a) : EquivariantCoherent b :=
  ⟨_, D.pullCoherent F, D.pullLinearization F⟩

/-- Closed direct image and inverse image with their adjunction on linearized
coherent sheaves, and the map induced by direct image on the class module. -/
def HasClosedImage (i : Z ⟶ X) (a : ModObj T.X X) (b : ModObj T.X Z) : Prop :=
  ∃ D : ClosedImageData i a b,
    (∀ F, IsEquivariantPullback i F (D.pull F) (Iso.refl _)) ∧
    (∀ H, IsEquivariantPushforward i H (D.push H) (Iso.refl _)) ∧
    (∀ F, IsEquivariantOnTests F.lin (D.push (D.pull F)).lin
      ((Scheme.Modules.pullbackPushforwardAdjunction i.left).unit.app F.sheaf)) ∧
    (∀ {H K : EquivariantCoherent b} (m : H.sheaf ⟶ K.sheaf),
      EquivariantHom m →
        EquivariantHom (F := D.push H) (H := D.push K) ((Scheme.Modules.pushforward i.left).map m)) ∧
    (∀ {H K L : EquivariantCoherent b} (f : H.sheaf ⟶ K.sheaf) (g : K.sheaf ⟶ L.sheaf)
      (w : f ≫ g = 0), EquivariantHom f → EquivariantHom g →
        (ShortComplex.mk f g w).ShortExact →
        ((ShortComplex.mk f g w).map (Scheme.Modules.pushforward i.left)).ShortExact) ∧
    (∀ χ H K, IsTwist χ H K → IsTwist χ (D.push H) (D.push K)) ∧
    (∀ H, D.pushClasses (classOf H) = classOf (D.push H))

/-- Equivariant closed direct image in the setting of the E10 localization sequence. -/
def ClosedImage : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X Z : SchemeOver k}
    (a : ModObj T.X X) (b : ModObj T.X Z) (i : Z ⟶ X),
    IsSplitTorus T →
    LocallyOfFiniteType X.hom → IsSeparated X.hom → CompactSpace X.left →
    (∀ x : X.left, ∃ U : X.left.Opens,
      x ∈ U ∧ IsAffineOpen U ∧ a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U) →
    IsClosedImmersion i.left → IsEquivariantMap a b i →
    HasClosedImage i a b

end

end LinearAlgebraicGroups.Specs.EquivariantCoherentClosedImage
