import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FppfTorsors
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.QuotientEmbedding

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u v w

namespace LinearAlgebraicGroups.Specs.TorsorObstruction

open Fppf

noncomputable section

section Fibre

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A B : Sheaf J (Type w)} {T : C} (hT : IsTerminal T)
  (q : A.obj ⟶ B.obj) (x : B.obj.obj (op T))

/-- Sections of the sheaf fibre of a morphism over a point of its target. -/
def fibrePresheaf : Cᵒᵖ ⥤ Type w where
  obj U := {g : A.obj.obj U // q.app U g = B.obj.map (hT.from U.unop).op x}
  map {U V} f := ↾fun g ↦ ⟨A.obj.map f g.val, by
    rw [q.naturality_apply, g.property, ← Functor.map_comp_apply]
    have he : (hT.from U.unop).op ≫ f = (hT.from V.unop).op := by
      apply Quiver.Hom.unop_inj
      exact hT.hom_ext _ _
    rw [he]⟩
  map_id U := by ext g; change A.obj.map (𝟙 U) g.val = g.val; simp
  map_comp f g := by
    ext p
    change A.obj.map (f ≫ g) p.val = A.obj.map g (A.obj.map f p.val)
    rw [Functor.map_comp_apply]

def fibreSheaf : Sheaf J (Type w) := ⟨fibrePresheaf hT q x, by
  apply (isSheaf_iff_isSheaf_of_type J _).2
  intro U R hR s hs
  have hA := A.property.isSheafFor R hR
  have hB := B.property.isSheafFor R hR
  let t : Presieve.FamilyOfElements A.obj R.arrows := fun _ f hf ↦ (s f hf).val
  have ht : t.Compatible := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ e
    exact congrArg Subtype.val (hs g₁ g₂ hf₁ hf₂ e)
  obtain ⟨a, ha, hu⟩ := hA t ht
  have pa : q.app (op U) a = B.obj.map (hT.from U).op x := by
    apply hB.isSeparatedFor.ext
    intro V f hf
    rw [← q.naturality_apply, ha f hf, ← Functor.map_comp_apply, ← op_comp]
    change q.app (op V) (s f hf).val = _
    rw [(s f hf).2]
    rw [hT.hom_ext (hT.from V) (f ≫ hT.from U)]
  refine ⟨⟨a, pa⟩, fun _ f hf ↦ Subtype.ext (ha f hf), fun b hb ↦ Subtype.ext ?_⟩
  exact hu b.val (fun _ f hf ↦ congrArg Subtype.val (hb f hf))⟩

end Fibre

section Field

variable {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G)

/-- Rational points of the fppf sheaf quotient, evaluated at Spec k. -/
abbrev RationalPoints := (rightQuotientSheaf H).obj.obj (op (fieldBase k))

/-- The canonical map from ordinary right cosets to rational quotient points. -/
def rationalCosetMap (a : RightCosets H (fieldBase k)) : RationalPoints H :=
  (toSheafify (fppfOver k) (rightCosetPresheaf H)).app _ (ULift.up a)

abbrev fieldQuotient := (fppfOver k).overPullback (Type (u + 1)) (fieldBase k)

/-- The group of sections on the field slice is the restriction of a representable sheaf. -/
theorem fieldGroupSectionsAreSheaf (K : GroupScheme k) :
    Presieve.IsSheaf (torsorTopology (fieldBase k))
      (groupSections (fieldBase k) K ⋙ forget GrpCat) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    (((fieldQuotient (k := k)).obj (schemeFppfSheaf K.X)).property)

/-- The neutral class is the regular right torsor of the group over the field. -/
def fieldNeutralClass (K : GroupScheme k) : H1fppf k K :=
  neutralClass (fieldGroupSectionsAreSheaf K)

abbrev fibreProjection :=
  ((fieldQuotient (k := k)).map (rightQuotientProjection H)).hom

theorem projectSection_mul_inclusion {U : SchemeOver k} (a : U ⟶ G.X) (h : U ⟶ H.group.X) :
    projectSection H (a * (h ≫ H.inclusion.hom.hom)) = projectSection H a := by
  apply congrArg (fun c : RightCosets H U ↦
    (toSheafify (fppfOver k) (rightCosetPresheaf H)).app (op U) (ULift.up c))
  symm
  apply QuotientGroup.eq.mpr
  refine ⟨h, ?_⟩
  change h ≫ H.inclusion.hom.hom = a⁻¹ * (a * (h ≫ H.inclusion.hom.hom))
  simp

abbrev FibreSection (x : RationalPoints H) (U : Over (fieldBase k)) :=
  {g : ULift.{u+1} (U.left ⟶ G.X) //
    projectSection H g.down = (rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from U).left.op x}

/-- The right action on the fibre of the canonical sheaf projection over x. -/
def quotientFibreAction (x : RationalPoints H) : SchemeAction (fieldBase k) H.group where
  sheaf := fibreSheaf Over.mkIdTerminal (fibreProjection H) x
  act {U} a h := by
    change FibreSection H x U at a ⊢
    let b : U.left ⟶ H.group.X := h.down
    exact ⟨⟨a.val.down * (b ≫ H.inclusion.hom.hom)⟩,
      (projectSection_mul_inclusion H _ _).trans a.property⟩
  act_one {U} a := by
    change FibreSection H x U at a
    apply Subtype.ext
    apply ULift.ext
    change a.val.down * ((1 : U.left ⟶ H.group.X) ≫ H.inclusion.hom.hom) = a.val.down
    simp
  act_mul {U} a g h := by
    change FibreSection H x U at a
    apply Subtype.ext
    apply ULift.ext
    let b : U.left ⟶ H.group.X := g.down
    let c : U.left ⟶ H.group.X := h.down
    change (a.val.down * (b ≫ H.inclusion.hom.hom)) * (c ≫ H.inclusion.hom.hom) =
      a.val.down * ((b * c) ≫ H.inclusion.hom.hom)
    rw [MonObj.mul_comp, mul_assoc]
  map_act {U V} f a g := by
    change FibreSection H x U at a
    apply Subtype.ext
    apply ULift.ext
    let b : U.left ⟶ H.group.X := g.down
    change f.left ≫ (a.val.down * (b ≫ H.inclusion.hom.hom)) =
      (f.left ≫ a.val.down) * ((f.left ≫ b) ≫ H.inclusion.hom.hom)
    rw [MonObj.comp_mul, Category.assoc]

/-- An extension map on classes induced by the contracted product. This condition
specifies its value for every torsor and every realization of its extension. -/
def IsExtensionMap (f : Fppf.H1fppf k H.group → Fppf.H1fppf k G) : Prop :=
  ∀ (P : FppfTorsor (fieldBase k) H.group) (Q : FppfTorsor (fieldBase k) G),
    IsStructureGroupExtension (fieldBase k) H.inclusion P Q →
      f (Quotient.mk _ P) = Quotient.mk _ Q

/-- A cohomology class is the class of the fibre with its given action. -/
def IsFibreClass (x : RationalPoints H) (c : Fppf.H1fppf k H.group) : Prop :=
  ∃ h : IsTorsor (quotientFibreAction H x),
    c = Quotient.mk _ (⟨quotientFibreAction H x, h⟩ : FppfTorsor (fieldBase k) H.group)

end Field

/-- Pointed-set exactness and the rational orbit criterion for the right fppf quotient. -/
def PointedExactness : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G),
    ∃ (δ : RationalPoints H → H1fppf k H.group) (e : H1fppf k H.group → H1fppf k G),
      (∀ x, IsFibreClass H x (δ x)) ∧ IsExtensionMap H e ∧
      Function.Injective (rationalCosetMap H) ∧
      δ (rationalCosetMap H (QuotientGroup.mk 1)) = fieldNeutralClass H.group ∧
      e (fieldNeutralClass H.group) = fieldNeutralClass G ∧
      Set.range (rationalCosetMap H) = {x | δ x = fieldNeutralClass H.group} ∧
      Set.range δ = {c | e c = fieldNeutralClass G} ∧
      ∀ x y, δ x = δ y ↔ ∃ g : fieldBase k ⟶ G.X, actOnSection H g x = y

open QuotientEmbedding (Presentation)

/-- A quotient presentation identifies rational points and the rational coset map
with their scheme counterparts. On every test scheme, the sections of the
fibre are precisely the maps to the scheme-theoretic fibre of the projection. -/
def RationalPointsOfPresentation : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} {H : ClosedSubgroup G}
    (Q : Presentation H), ∃ e : RationalPoints H ≃ (fieldBase k ⟶ Q.scheme),
      (∀ g : fieldBase k ⟶ G.X, e (rationalCosetMap H (QuotientGroup.mk g)) = g ≫ Q.projection) ∧
      ∀ (x : RationalPoints H) (U : Over (fieldBase k)) (g : U.left ⟶ G.X),
        projectSection H g =
          (rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from U).left.op x ↔
        g ≫ Q.projection = U.hom ≫ e x

end

end LinearAlgebraicGroups.Specs.TorsorObstruction
