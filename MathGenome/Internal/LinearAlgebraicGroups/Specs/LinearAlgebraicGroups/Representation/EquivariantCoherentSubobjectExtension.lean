import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.EquivariantCoherentSubobjectExtension

open EquivariantAffineModules

noncomputable section

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
variable {a : ModObj T.X X} {b : ModObj T.X Y}

/-- The hypotheses on the ambient scheme and the equivariant open immersion. -/
structure IsExtensionSetting (a : ModObj T.X X) (b : ModObj T.X Y) (j : Y ⟶ X) : Prop where
  split : IsSplitTorus T
  finiteType : LocallyOfFiniteType X.hom
  separated : IsSeparated X.hom
  compact : CompactSpace X.left
  invariantAffines : ∀ x : X.left, ∃ U : X.left.Opens,
    x ∈ U ∧ IsAffineOpen U ∧ a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U
  equivariant : IsEquivariantMap a b j

/-- The transport comparison for the actual pullback, also for quasi-coherent
sheaves that need not be coherent. -/
def PullbackLinearizationComparison (j : Y ⟶ X) {M : X.left.Modules} {N : Y.left.Modules}
    (L : Linearization a M) (K : Linearization b N) (e : Pull j M ≅ N) : Prop :=
  ∀ (S : SchemeOver k) (t : S ⟶ T.X) (y : S ⟶ Y),
    ∃ h : actOn a t (y ≫ j) = actOn b t y ≫ j,
      (Scheme.Modules.pullback y.left).map e.inv ≫ (pullComp M y j).hom ≫
        (transport a L.iso t (y ≫ j)).hom ≫ (pullCongr M h).hom ≫
        (pullComp M (actOn b t y) j).inv ≫
        (Scheme.Modules.pullback (actOn b t y).left).map e.hom =
      (transport b K.iso t y).hom

def SubobjectExtension : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
    {a : ModObj T.X X} {b : ModObj T.X Y} (j : Y ⟶ X) [IsOpenImmersion j.left],
    IsExtensionSetting a b j →
    ∀ (M : EquivariantQuasicoherent a) (N : EquivariantQuasicoherent b)
      (e : Pull j M.sheaf ≅ N.sheaf), PullbackLinearizationComparison j M.lin N.lin e →
    ∀ (H : EquivariantCoherent b) (ι : H.sheaf ⟶ N.sheaf),
      Mono ι → IsLinearizedMap H.lin N.lin ι →
      ∃ (F : EquivariantCoherent a) (i : F.sheaf ⟶ M.sheaf) (d : Pull j F.sheaf ≅ H.sheaf),
        Mono i ∧ IsLinearizedMap F.lin M.lin i ∧ IsEquivariantPullback j F H d ∧
        (Scheme.Modules.pullback j.left).map i ≫ e.hom = d.hom ≫ ι

/-- The actual open adjunction has an equivariant counit and takes equivariant
maps out of the pullback to equivariant maps into the direct image. -/
def OpenDirectImageAdjunction : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
    {a : ModObj T.X X} {b : ModObj T.X Y} (j : Y ⟶ X)
    [IsOpenImmersion j.left] [QuasiCompact j.left] [IsLocallyNoetherian X.left],
    IsEquivariantMap a b j →
    ∀ H : EquivariantQuasicoherent b,
      ∃ (J : Linearization a ((Scheme.Modules.pushforward j.left).obj H.sheaf))
        (e : Pull j ((Scheme.Modules.pushforward j.left).obj H.sheaf) ≅ H.sheaf),
        e.hom = (Scheme.Modules.pullbackPushforwardAdjunction j.left).counit.app H.sheaf ∧
        PullbackLinearizationComparison j J H.lin e ∧
        ∀ {F : X.left.Modules} (L : Linearization a F) (K : Linearization b (Pull j F)),
          PullbackLinearizationComparison j L K (Iso.refl _) →
          ∀ f : Pull j F ⟶ H.sheaf, IsLinearizedMap K H.lin f →
            IsLinearizedMap L J
              ((Scheme.Modules.pullbackPushforwardAdjunction j.left).homEquiv F H.sheaf f)

def SubobjectExtensionFromAdjunction : Prop :=
  OpenDirectImageAdjunction.{u} → SubobjectExtension.{u}

end

end LinearAlgebraicGroups.Specs.EquivariantCoherentSubobjectExtension
