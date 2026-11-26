import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.EquivariantOpenFlatBaseChange

open EquivariantAffineModules

noncomputable section

/-- The comparison for a square over the field, adjoint to the pullback
of the direct-image counit along the map of open subschemes. -/
def openBaseChange {k : Type u} [Field k] {X Y U V : SchemeOver k}
    (j : Y ⟶ X) (l : V ⟶ U) (g : U ⟶ X) (r : V ⟶ Y)
    (h : l ≫ g = r ≫ j) (H : Y.left.Modules) :
    Pull g ((Scheme.Modules.pushforward j.left).obj H) ⟶
      (Scheme.Modules.pushforward l.left).obj (Pull r H) :=
  let F := (Scheme.Modules.pushforward j.left).obj H
  let c := (Scheme.Modules.pullbackPushforwardAdjunction j.left).counit.app H
  ((Scheme.Modules.pullbackPushforwardAdjunction l.left).homEquiv _ _)
    ((pullComp F l g).hom ≫ (pullCongr F h).hom ≫ (pullComp F r j).inv ≫
      (Scheme.Modules.pullback r.left).map c)

/-- Formation of the direct image of a quasi-coherent module under a
quasi-compact open immersion commutes with flat base change. -/
def FlatOpenBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {X Y U V : SchemeOver k}
    (j : Y ⟶ X) (l : V ⟶ U) (g : U ⟶ X) (r : V ⟶ Y)
    (h : l ≫ g = r ≫ j), IsPullback l.left r.left g.left j.left →
    IsOpenImmersion j.left → QuasiCompact j.left → Flat g.left →
    ∀ H : Y.left.Modules, H.IsQuasicoherent → IsIso (openBaseChange j l g r h H)

end

end LinearAlgebraicGroups.Specs.EquivariantOpenFlatBaseChange
