import Specs.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import LinearAlgebraicGroups.Cohomology.FlatPullback
import LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
import LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Basis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidAlgebra BigOperators TensorProduct DirectSum

universe u v

namespace LinearAlgebraicGroups.Representation.EquivariantAffineModules

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.EquivariantAffineModules
open Specs.CharacterDescent (Character)

noncomputable section

variable {k : Type u} [Field k]

section PullbackLinearization

variable {T : GroupScheme k} {W X Y Z : SchemeOver k}

set_option maxHeartbeats 250000

@[simp]
private theorem pullCongr_refl (F : X.left.Modules) (f : Y ⟶ X) :
    (pullCongr F (rfl : f = f)).hom = 𝟙 _ := rfl

@[reassoc]
private theorem pullCongr_trans (F : X.left.Modules) {f g h : Y ⟶ X}
    (e : f = g) (e' : g = h) :
    (pullCongr F e).hom ≫ (pullCongr F e').hom = (pullCongr F (e.trans e')).hom := by
  subst g h
  simp only [pullCongr_refl, Category.comp_id]

@[reassoc]
private theorem pullComp_congr_left (F : X.left.Modules) {f f' : Z ⟶ Y} (g : Y ⟶ X)
    (e : f = f') :
    (pullCongr (Pull g F) e).hom ≫ (pullComp F f' g).hom =
      (pullComp F f g).hom ≫ (pullCongr F (congrArg (· ≫ g) e)).hom := by
  subst f'
  simp only [pullCongr_refl, Category.id_comp, Category.comp_id]

private theorem pullComp_assoc (F : X.left.Modules) (f : W ⟶ Z) (g : Z ⟶ Y) (h : Y ⟶ X) :
    (Scheme.Modules.pullback f.left).map (pullComp F g h).hom ≫
      (pullComp F f (g ≫ h)).hom =
    (pullComp (Pull h F) f g).hom ≫ (pullComp F (f ≫ g) h).hom ≫
      (pullCongr F (Category.assoc f g h)).hom := by
  have H := congrArg (fun e => NatTrans.app e F)
    (Scheme.Modules.pseudofunctor_associativity f.left g.left h.left)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at H
  have H' :
      (pullComp F f (g ≫ h)).inv ≫
        (Scheme.Modules.pullback f.left).map (pullComp F g h).inv ≫
        (pullComp (Pull h F) f g).hom ≫ (pullComp F (f ≫ g) h).hom =
      (pullCongr F (Category.assoc f g h)).inv := H
  apply (cancel_mono (pullCongr F (Category.assoc f g h)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have E := congrArg (fun r =>
    ((Scheme.Modules.pullback f.left).map (pullComp F g h).hom ≫
      (pullComp F f (g ≫ h)).hom) ≫ r) H'
  have hcancel :
      (Scheme.Modules.pullback f.left).map (pullComp F g h).hom ≫
        (Scheme.Modules.pullback f.left).map (pullComp F g h).inv = 𝟙 _ :=
    ((Scheme.Modules.pullback f.left).mapIso (pullComp F g h)).hom_inv_id
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hcancel,
    Category.id_comp] using E.symm

/-- A choice of factorization of a morphism gives a comparison of the
successive inverse images with the inverse image of the morphism. -/
private def comparePull (F : X.left.Modules) (f : Z ⟶ Y) (g : Y ⟶ X) {h : Z ⟶ X}
    (e : f ≫ g = h) : Pull f (Pull g F) ≅ Pull h F :=
  pullComp F f g ≪≫ pullCongr F e

@[reassoc]
private theorem comparePull_map {B : SchemeOver k} (F : X.left.Modules)
    (f : W ⟶ Z) (l : Z ⟶ B) (g : B ⟶ X) {x : Z ⟶ X} (hx : l ≫ g = x)
    {l' : W ⟶ B} (hl : f ≫ l = l') (hx' : l' ≫ g = f ≫ x) :
    (Scheme.Modules.pullback f.left).map (comparePull F l g hx).hom ≫
      (pullComp F f x).hom =
    (pullComp (Pull g F) f l).hom ≫ (pullCongr (Pull g F) hl).hom ≫
      (comparePull F l' g hx').hom := by
  subst l' x
  simp only [comparePull, Iso.trans_hom, pullCongr_refl, Category.comp_id, Category.id_comp]
  exact pullComp_assoc F f l g

@[reassoc]
private theorem pullCongr_naturality {F H : X.left.Modules} {f f' : Y ⟶ X}
    (h : f = f') (g : F ⟶ H) :
    (pullCongr F h).hom ≫ (Scheme.Modules.pullback f'.left).map g =
      (Scheme.Modules.pullback f.left).map g ≫ (pullCongr H h).hom := by
  subst f'
  simp only [pullCongr_refl, Category.id_comp, Category.comp_id]

/-- Evaluate an inverse-image isomorphism along a morphism, with specified
names for the two composite morphisms. -/
private def evalPullIso {F : X.left.Modules} {g₁ g₂ : Z ⟶ X}
    (θ : Pull g₁ F ≅ Pull g₂ F) (l : Y ⟶ Z) {x y : Y ⟶ X}
    (hx : l ≫ g₁ = x) (hy : l ≫ g₂ = y) : Pull x F ≅ Pull y F :=
  (comparePull F l g₁ hx).symm ≪≫ (Scheme.Modules.pullback l.left).mapIso θ ≪≫
    comparePull F l g₂ hy

@[reassoc]
private theorem pullback_map_evalPullIso {F : X.left.Modules} {g₁ g₂ : Z ⟶ X}
    (θ : Pull g₁ F ≅ Pull g₂ F) (l : Y ⟶ Z) {x y : Y ⟶ X}
    (hx : l ≫ g₁ = x) (hy : l ≫ g₂ = y) (f : W ⟶ Y)
    {l' : W ⟶ Z} (hl : f ≫ l = l')
    (hx' : l' ≫ g₁ = f ≫ x) (hy' : l' ≫ g₂ = f ≫ y) :
    (Scheme.Modules.pullback f.left).map (evalPullIso θ l hx hy).hom ≫
      (pullComp F f y).hom = (pullComp F f x).hom ≫ (evalPullIso θ l' hx' hy').hom := by
  let C := Scheme.Modules.pullback f.left
  let e₁ := comparePull F l g₁ hx
  let e₂ := comparePull F l g₂ hy
  let e₁' := comparePull F l' g₁ hx'
  let e₂' := comparePull F l' g₂ hy'
  let θ₁ := (Scheme.Modules.pullback l.left).mapIso θ
  let θ₂ := (Scheme.Modules.pullback l'.left).mapIso θ
  have hL : C.map (e₁.symm ≪≫ θ₁ ≪≫ e₂).hom =
      C.map e₁.inv ≫ C.map θ₁.hom ≫ C.map e₂.hom := by simp
  change C.map (e₁.symm ≪≫ θ₁ ≪≫ e₂).hom ≫ (pullComp F f y).hom =
    (pullComp F f x).hom ≫ (e₁'.symm ≪≫ θ₂ ≪≫ e₂').hom
  have hcan : C.map e₁.hom ≫ C.map e₁.inv = 𝟙 _ := (C.mapIso e₁).hom_inv_id
  apply (cancel_epi (C.map e₁.hom)).mp
  simp only [hL, Category.assoc, reassoc_of% hcan]
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc (C.map e₁.hom)]
  have hcmp₁ := comparePull_map F f l g₁ hx hl hx'
  have hcmp₂ := comparePull_map F f l g₂ hy hl hy'
  change C.map e₁.hom ≫ _ = _ ≫ _ ≫ e₁'.hom at hcmp₁
  change C.map e₂.hom ≫ _ = _ ≫ _ ≫ e₂'.hom at hcmp₂
  rw [hcmp₁, hcmp₂]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hnat : C.map θ₁.hom ≫ (pullComp (Pull g₂ F) f l).hom =
      (pullComp (Pull g₁ F) f l).hom ≫ (Scheme.Modules.pullback (f ≫ l).left).map θ.hom :=
    ((Scheme.Modules.pullbackComp f.left l.left).hom.naturality θ.hom)
  rw [reassoc_of% hnat, ← pullCongr_naturality_assoc]
  rfl

private theorem transport_eq_evalPullIso (a : ModObj T.X X) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Y ⟶ T.X) (x : Y ⟶ X) :
    transport a θ t x = evalPullIso θ (lift t x) (lift_snd t x) rfl := by
  apply Iso.ext
  simp only [transport, evalPullIso, comparePull, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    pullCongr_refl, Category.comp_id, Category.assoc]

@[reassoc]
private theorem evalPullIso_comp_congr {F : X.left.Modules} {g₁ g₂ : Z ⟶ X}
    (θ : Pull g₁ F ≅ Pull g₂ F) (l : Y ⟶ Z)
    {x y y' : Y ⟶ X} (hx : l ≫ g₁ = x) (hy : l ≫ g₂ = y) (h : y = y') :
    (evalPullIso θ l hx hy).hom ≫ (pullCongr F h).hom =
      (evalPullIso θ l hx (hy.trans h)).hom := by
  subst y'
  rw [pullCongr_refl, Category.comp_id]

@[reassoc]
private theorem comparePull_outer (F : X.left.Modules) (f : Y ⟶ X) (g : Z ⟶ Y) (r : W ⟶ Z)
    {x : W ⟶ Y} (e : r ≫ g = x)
    (e' : r ≫ (g ≫ f) = x ≫ f) :
    (Scheme.Modules.pullback r.left).map (pullComp F g f).hom ≫
        (comparePull F r (g ≫ f) e').hom =
      (comparePull (Pull f F) r g e).hom ≫ (pullComp F x f).hom := by
  subst x
  simp only [comparePull, Iso.trans_hom, pullCongr_refl, Category.comp_id]
  rw [← Category.assoc, pullComp_assoc]
  simp only [Category.assoc, pullCongr_trans, pullCongr_refl, Category.comp_id]

private theorem equivariant_actOn {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {t : Z ⟶ T.X} {y : Z ⟶ Y} :
    actOn a t (y ≫ f) = actOn b t y ≫ f := by
  calc
    actOn a t (y ≫ f) = lift t y ≫ (𝟙 T.X ⊗ₘ f) ≫ a.smul := by simp [actOn]
    _ = actOn b t y ≫ f := by rw [← hf, ← Category.assoc]

/-- The universal linearization isomorphism pulled back along an
equivariant map. -/
def pullbackLinearizationIso {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) :
    Pull (snd T.X Y) (Pull f F) ≅ Pull b.smul (Pull f F) :=
  pullComp F (snd T.X Y) f ≪≫
    evalPullIso θ (𝟙 T.X ⊗ₘ f) (by simp) hf.symm ≪≫ (pullComp F b.smul f).symm

private theorem pullback_map_evalPullIso_to {F : X.left.Modules} {g₁ g₂ : Z ⟶ X}
    (θ : Pull g₁ F ≅ Pull g₂ F) (l : Y ⟶ Z) {x y : Y ⟶ X}
    (hx : l ≫ g₁ = x) (hy : l ≫ g₂ = y) (f : W ⟶ Y)
    {l' : W ⟶ Z} (hl : f ≫ l = l') {x' y' : W ⟶ X}
    (hfx : f ≫ x = x') (hfy : f ≫ y = y')
    (hx' : l' ≫ g₁ = x') (hy' : l' ≫ g₂ = y') :
    (Scheme.Modules.pullback f.left).map (evalPullIso θ l hx hy).hom ≫
        (comparePull F f y hfy).hom =
      (comparePull F f x hfx).hom ≫ (evalPullIso θ l' hx' hy').hom := by
  subst x' y'
  simp only [comparePull, Iso.trans_hom, pullCongr_refl, Category.comp_id]
  exact pullback_map_evalPullIso θ l hx hy f hl hx' hy'

/-- The pulled-back isomorphism agrees with transport over every test scheme. -/
@[reassoc]
theorem pullbackLinearization_transport {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Z ⟶ T.X) (y : Z ⟶ Y) :
    (transport b (pullbackLinearizationIso hf θ) t y).hom ≫
        (pullComp F (actOn b t y) f).hom =
      (pullComp F y f).hom ≫ (transport a θ t (y ≫ f)).hom ≫
        (pullCongr F (equivariant_actOn hf)).hom := by
  let r := lift t y
  let r' := lift t (y ≫ f)
  let p := snd T.X Y
  let q := 𝟙 T.X ⊗ₘ f
  let j : r ≫ q = r' := by simp [r, r', q]
  let ep : r ≫ p = y := lift_snd _ _
  let hp : q ≫ snd T.X X = p ≫ f := by simp [p, q]
  let hfx : r ≫ (p ≫ f) = y ≫ f := by rw [← Category.assoc, ep]
  let hfy : r ≫ (b.smul ≫ f) = actOn b t y ≫ f := (Category.assoc r b.smul f).symm
  let θq := evalPullIso θ q hp hf.symm
  let cl := comparePull (Pull f F) r p ep
  let cr := comparePull (Pull f F) r b.smul (rfl : r ≫ b.smul = actOn b t y)
  let θr := evalPullIso θ r' (lift_snd t (y ≫ f))
    (equivariant_actOn hf (t := t) (y := y))
  let P := Scheme.Modules.pullback r.left
  have hL := comparePull_outer F f p r ep hfx
  have hR := comparePull_outer F f b.smul r rfl hfy
  have hm := pullback_map_evalPullIso_to θ q hp hf.symm r j hfx hfy
    (lift_snd t (y ≫ f)) (equivariant_actOn hf (t := t) (y := y))
  have he :
      (transport a θ t (y ≫ f)).hom ≫ (pullCongr F (equivariant_actOn hf)).hom = θr.hom := by
    rw [transport_eq_evalPullIso, evalPullIso_comp_congr]
  rw [he, transport_eq_evalPullIso]
  change (cl.symm ≪≫ P.mapIso (pullComp F p f ≪≫ θq ≪≫ (pullComp F b.smul f).symm) ≪≫ cr).hom ≫
    (pullComp F (actOn b t y) f).hom = (pullComp F y f).hom ≫ θr.hom
  apply (cancel_epi cl.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]
  change P.map (pullComp F p f).hom ≫ P.map θq.hom ≫ P.map (pullComp F b.smul f).inv ≫
      cr.hom ≫ (pullComp F (actOn b t y) f).hom =
    cl.hom ≫ (pullComp F y f).hom ≫ θr.hom
  change _ = cl.hom ≫ (pullComp F y f).hom at hL
  change _ = cr.hom ≫ (pullComp F (actOn b t y) f).hom at hR
  rw [← hR, ← reassoc_of% hL]
  let A := P.map (pullComp F p f).hom
  let B := P.mapIso (pullComp F b.smul f)
  let M := P.map θq.hom
  let C₁ := (comparePull F r (p ≫ f) hfx).hom
  let C₂ := (comparePull F r (b.smul ≫ f) hfy).hom
  have hM : M ≫ C₂ = C₁ ≫ θr.hom := hm
  change A ≫ M ≫ B.inv ≫ (B.hom ≫ C₂) = A ≫ C₁ ≫ θr.hom
  exact (congrArg (fun d => A ≫ M ≫ d) (B.inv_hom_id_assoc C₂)).trans
    (congrArg (fun d => A ≫ d) hM)


/-- The pulled-back linearization isomorphism satisfies the identity law. -/
theorem pullbackLinearization_unit
    {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules} (L : Linearization a F)
    (Z : SchemeOver k) (y : Z ⟶ Y) :
    ∃ h : actOn b (1 : Z ⟶ T.X) y = y,
      (transport b (pullbackLinearizationIso hf L.iso) 1 y).hom ≫
        (pullCongr (Pull f F) h).hom = 𝟙 _ := by
  let := b
  let h : actOn b (1 : Z ⟶ T.X) y = y := one_smul (Z ⟶ T.X) y
  obtain ⟨hA, hunit⟩ := L.unit Z (y ≫ f)
  refine ⟨h, (cancel_mono (pullComp F y f).hom).mp ?_⟩
  rw [Category.assoc, pullComp_congr_left, pullbackLinearization_transport_assoc,
    pullCongr_trans, Category.id_comp]
  have heq : (equivariant_actOn hf (t := 1) (y := y)).trans (congrArg (· ≫ f) h) = hA :=
    Subsingleton.elim _ _
  rw [heq, hunit, Category.comp_id]


section PullbackComposition

set_option backward.isDefEq.respectTransparency false

@[reassoc]
private theorem transport_congr_point {a : ModObj T.X X} {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Z ⟶ T.X)
    {x x' : Z ⟶ X} (e : x = x') :
    (pullCongr F e).hom ≫ (transport a θ t x').hom =
      (transport a θ t x).hom ≫ (pullCongr F (congrArg (actOn a t) e)).hom := by
  subst x'
  simp only [pullCongr_refl, Category.id_comp, Category.comp_id]

private theorem equivariant_iterated_actOn {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) (s t : Z ⟶ T.X) (y : Z ⟶ Y) :
    actOn a s (actOn a t (y ≫ f)) = actOn b s (actOn b t y) ≫ f :=
  (congrArg (actOn a s) (equivariant_actOn hf (t := t) (y := y))).trans
    (equivariant_actOn hf (t := s) (y := actOn b t y))

@[reassoc]
private theorem pullbackLinearization_transport_two
    {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (s t : Z ⟶ T.X) (y : Z ⟶ Y) :
    (transport b (pullbackLinearizationIso hf θ) t y).hom ≫
      (transport b (pullbackLinearizationIso hf θ) s (actOn b t y)).hom ≫
      (pullComp F (actOn b s (actOn b t y)) f).hom =
    (pullComp F y f).hom ≫ (transport a θ t (y ≫ f)).hom ≫
      (transport a θ s (actOn a t (y ≫ f))).hom ≫ (pullCongr F (equivariant_iterated_actOn hf s t y)).hom := by
  rw [pullbackLinearization_transport, pullbackLinearization_transport_assoc,
    transport_congr_point_assoc, pullCongr_trans]

private theorem composition_cancel_square {C : Type*} [Category C]
    {A B D E P Q R S : C} (e₀ : A ≅ P) (e₁ : D ≅ R) (e₂ : E ≅ S)
    (f₁ : A ⟶ B) (f₂ : B ⟶ D) (f₃ : D ⟶ E) (f₄ : A ⟶ E)
    (g₁ : P ⟶ Q) (g₂ : Q ⟶ R) (g₃ : R ⟶ S) (g₄ : P ⟶ S)
    (h₁ : f₁ ≫ f₂ ≫ e₁.hom = e₀.hom ≫ g₁ ≫ g₂)
    (h₂ : f₃ ≫ e₂.hom = e₁.hom ≫ g₃) (h₃ : f₄ ≫ e₂.hom = e₀.hom ≫ g₄)
    (h : ComposesTo g₁ g₂ g₃ g₄) : ComposesTo f₁ f₂ f₃ f₄ := by
  unfold ComposesTo at *
  apply (cancel_mono e₂.hom).1
  simp only [Category.assoc, h₂, reassoc_of% h₁, h, h₃]

-- Complete the transport square with the equivariant identification of the target.
private theorem pullback_transport_compare
    {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Z ⟶ T.X) (y : Z ⟶ Y) :
    (transport b (pullbackLinearizationIso hf θ) t y).hom ≫
      (comparePull F (actOn b t y) f (equivariant_actOn hf).symm).hom =
    (pullComp F y f).hom ≫ (transport a θ t (y ≫ f)).hom := by
  simp only [comparePull, Iso.trans_hom, pullbackLinearization_transport_assoc,
    pullCongr_trans, pullCongr_refl, Category.comp_id]

private theorem pullback_transport_two_compare
    {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (s t : Z ⟶ T.X) (y : Z ⟶ Y) :
    (transport b (pullbackLinearizationIso hf θ) t y).hom ≫
      (transport b (pullbackLinearizationIso hf θ) s (actOn b t y)).hom ≫
      (comparePull F (actOn b s (actOn b t y)) f (equivariant_iterated_actOn hf s t y).symm).hom =
    (pullComp F y f).hom ≫ (transport a θ t (y ≫ f)).hom ≫
      (transport a θ s (actOn a t (y ≫ f))).hom := by
  simp only [comparePull, Iso.trans_hom, pullbackLinearization_transport_two_assoc,
    pullCongr_trans, pullCongr_refl, Category.comp_id]

private theorem comparePull_congr (F : X.left.Modules) (f : Y ⟶ X)
    {y y' : Z ⟶ Y} {x x' : Z ⟶ X} (e : y = y') (e' : x = x')
    (h : y ≫ f = x) (h' : y' ≫ f = x') :
    (pullCongr (Pull f F) e).hom ≫ (comparePull F y' f h').hom =
      (comparePull F y f h).hom ≫ (pullCongr F e').hom := by
  subst y' x x'
  simp only [comparePull, Iso.trans_hom, pullCongr_refl, Category.id_comp, Category.comp_id]

private theorem pullbackLinearization_mul_of
    {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F)
    (s t r : Z ⟶ T.X) (y : Z ⟶ Y)
    (hY : actOn b s (actOn b t y) = actOn b r y)
    (hX : actOn a s (actOn a t (y ≫ f)) = actOn a r (y ≫ f))
    (hL : ComposesTo (transport a θ t (y ≫ f)).hom (transport a θ s (actOn a t (y ≫ f))).hom
      (pullCongr F hX).hom (transport a θ r (y ≫ f)).hom) :
    ComposesTo (transport b (pullbackLinearizationIso hf θ) t y).hom
      (transport b (pullbackLinearizationIso hf θ) s (actOn b t y)).hom
      (pullCongr (Pull f F) hY).hom (transport b (pullbackLinearizationIso hf θ) r y).hom := by
  exact composition_cancel_square (pullComp F y f)
    (comparePull F (actOn b s (actOn b t y)) f (equivariant_iterated_actOn hf s t y).symm)
    (comparePull F (actOn b r y) f (equivariant_actOn hf).symm)
    _ _ _ _ _ _ _ _
    (pullback_transport_two_compare hf θ s t y)
    (comparePull_congr F f hY hX _ _) (pullback_transport_compare hf θ r y) hL

private theorem pullbackLinearization_mul
    {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules} (L : Linearization a F)
    (Z : SchemeOver k) (s t : Z ⟶ T.X) (y : Z ⟶ Y) :
    ∃ h : actOn b s (actOn b t y) = actOn b (s * t) y,
      TransportComposition (pullbackLinearizationIso hf L.iso) s t y h := by
  let := b
  let hY : actOn b s (actOn b t y) = actOn b (s * t) y := (mul_smul s t y).symm
  let hX := (L.mul Z s t (y ≫ f)).choose
  have hL : TransportComposition L.iso s t (y ≫ f) hX := (L.mul Z s t (y ≫ f)).choose_spec
  exact ⟨hY, pullbackLinearization_mul_of hf L.iso s t (s * t) y hY hX hL⟩

/-- An equivariant map pulls back the full linearization, with its
transport compatible with composition of scheme pullbacks. -/
def pullbackLinearization
    {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules} (L : Linearization a F) :
    Linearization b (Pull f F) where
  iso := pullbackLinearizationIso hf L.iso
  unit := pullbackLinearization_unit hf L
  mul := pullbackLinearization_mul hf L

end PullbackComposition

end PullbackLinearization

section AffineModules

open Scheme.Modules
open _root_.LinearAlgebraicGroups.ProjectiveFiniteness (finite_sections_of_isAffineOpen)
open private finite_restrictScalars_of_surjective
  from LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

set_option backward.isDefEq.respectTransparency false in
theorem finitePresentation_tilde {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : (tilde M).IsFinitePresentation := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R M).FG)
  let l := Finsupp.linearCombination R (fun a : (s : Set M) => a.val)
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (LinearMap.ker l)
  let P := presentationTilde M (s : Set M) hs (t : Set ((s : Set M) →₀ R)) ht
  refine { exists_quasicoherentData := ⟨P.quasicoherentData, ?_⟩ }
  constructor
  intro U
  constructor
  · constructor
    change Finite (↥(s : Set M))
    infer_instance
  · constructor
    change Finite (↥(t : Set ((s : Set M) →₀ R)))
    infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem finitePresentationSections (R : CommRingCat.{u})
    (F : (Spec R).Modules) [F.IsFinitePresentation] :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj F) := by
  let φ := (Scheme.ΓSpecIso R).inv
  let N : ModuleCat.{u} Γ(Spec R, ⊤) := F.val.obj (op ⊤)
  let : Module.Finite Γ(Spec R, ⊤) N := finite_sections_of_isAffineOpen F (isAffineOpen_top (Spec R))
  exact finite_restrictScalars_of_surjective φ.hom
    (ConcreteCategory.bijective_of_isIso φ).2 N

set_option backward.isDefEq.respectTransparency false in
theorem finitePresentation_iff_finite_sections (R : CommRingCat.{u}) [IsNoetherianRing R]
    (F : (Spec R).Modules) [F.IsQuasicoherent] :
    F.IsFinitePresentation ↔ Module.Finite R ((moduleSpecΓFunctor (R := R)).obj F) := by
  constructor
  · intro h
    exact finitePresentationSections R F
  · intro h
    let M := (moduleSpecΓFunctor (R := R)).obj F
    let : IsIso F.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ (R := R) F).mp ‹_›
    have e : tilde M ≅ F := asIso F.fromTildeΓ
    exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso e
      (finitePresentation_tilde M)

theorem affineFinitePresentation : AffineFinitePresentation.{u} := by
  intro R _ F _
  rw [finitePresentation_iff_finite_sections]
  constructor
  · intro h
    exact Module.finitePresentation_of_finite R _
  · intro h
    infer_instance

end AffineModules

section Grading

variable {Λ V W U : Type u} [CommGroup Λ]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

open WeightDecomposition (weightSpace mem_weightSpace)
open Specs.DiagonalizableGroups (groupAlgebra)

attribute [local instance] Classical.decEq

/-- A linear identity on an internally graded space can be tested on
homogeneous vectors. -/
theorem WeightGrading.linearMap_ext (G : WeightGrading k Λ V) {f g : V →ₗ[k] W}
    (h : ∀ i (v : G.piece i), f v = g v) : f = g := by
  have hcomp : f.comp (DirectSum.coeLinearMap G.piece) =
      g.comp (DirectSum.coeLinearMap G.piece) := by
    apply DirectSum.linearMap_ext
    intro i
    ext v
    simpa only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof] using h i v
  ext v
  obtain ⟨a, rfl⟩ := G.internal.surjective v
  exact DFunLike.congr_fun hcomp a

private def gradingDecomposition (G : WeightGrading k Λ V) :
    V ≃ₗ[k] ⨁ i, G.piece i :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap G.piece) G.internal).symm

private theorem gradingDecomposition_apply_of_mem (G : WeightGrading k Λ V)
    (i : Λ) (v : G.piece i) :
    gradingDecomposition G v = DirectSum.lof k Λ (G.piece ·) i v := by
  apply (gradingDecomposition G).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (DirectSum.coeLinearMap_lof G.piece i v).symm

local notation "B" => MonoidAlgebra k Λ
local notation "e" => MonoidAlgebra.of k Λ

private def gradedCoactionMap (G : WeightGrading k Λ V) : V →ₗ[k] V ⊗[k] B :=
  (DirectSum.toModule k Λ (V ⊗[k] B) (fun i =>
    ((TensorProduct.mk k V B).flip (e i)).comp (G.piece i).subtype)).comp
    (gradingDecomposition G).toLinearMap

@[simp]
private theorem gradedCoactionMap_apply_of_mem (G : WeightGrading k Λ V)
    (i : Λ) (v : G.piece i) : gradedCoactionMap G v = (v : V) ⊗ₜ[k] e i := by
  simp only [gradedCoactionMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    gradingDecomposition_apply_of_mem, DirectSum.toModule_lof, TensorProduct.mk_apply,
    LinearMap.flip_apply, Submodule.subtype_apply]

private def gradingToCoaction (G : WeightGrading k Λ V) :
    RightComodule k (groupAlgebra k Λ) V where
  coaction := gradedCoactionMap G
  coassoc v := by
    let f := (TensorProduct.assoc k V B B).toLinearMap ∘ₗ
      (gradedCoactionMap G).rTensor B ∘ₗ gradedCoactionMap G
    let g := (Coalgebra.comul (R := k) (A := B)).lTensor V ∘ₗ gradedCoactionMap G
    change f v = g v
    suffices f = g from DFunLike.congr_fun this v
    apply WeightGrading.linearMap_ext G
    intro i v
    have h : Coalgebra.comul (R := k) (e i) = e i ⊗ₜ[k] e i :=
      (MonoidAlgebra.isGroupLikeElem_of (R := k) i).comul_eq_tmul_self
    simp only [f, g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      gradedCoactionMap_apply_of_mem, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.assoc_tmul, h]
  counit v := by
    let f := (TensorProduct.rid k V).toLinearMap ∘ₗ
      (Coalgebra.counit (R := k) (A := B)).lTensor V ∘ₗ gradedCoactionMap G
    change f v = LinearMap.id (R := k) v
    suffices f = LinearMap.id from DFunLike.congr_fun this v
    apply WeightGrading.linearMap_ext G
    intro i v
    have h : Coalgebra.counit (R := k) (e i) = 1 :=
      (MonoidAlgebra.isGroupLikeElem_of (R := k) i).counit_eq_one
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, gradedCoactionMap_apply_of_mem,
      LinearMap.lTensor_tmul, TensorProduct.rid_tmul, h, one_smul, LinearMap.id_coe, id_eq]

private def coactionToGrading (ρ : RightComodule k (groupAlgebra k Λ) V) :
    WeightGrading k Λ V :=
  ⟨weightSpace ρ, WeightDecomposition.weightDecomposition ρ⟩

private theorem gradingToCoaction_rightInverse
    (ρ : RightComodule k (groupAlgebra k Λ) V) :
    gradingToCoaction (coactionToGrading ρ) = ρ := by
  have h : gradedCoactionMap (coactionToGrading ρ) = ρ.coaction := by
    apply WeightGrading.linearMap_ext (coactionToGrading ρ)
    intro i v
    rw [gradedCoactionMap_apply_of_mem]
    exact (mem_weightSpace.mp v.property).symm
  suffices ∀ p q : RightComodule k (groupAlgebra k Λ) V, p.coaction = q.coaction → p = q from
    this _ _ h
  rintro ⟨p, _, _⟩ ⟨q, _, _⟩ h
  dsimp at h
  subst q
  rfl

open private tensorCoefficients tensorCoefficients_tmul
  from LinearAlgebraicGroups.Multiplicative.WeightDecomposition

private theorem gradingToCoaction_leftInverse (G : WeightGrading k Λ V) :
    coactionToGrading (gradingToCoaction G) = G := by
  let p : ∀ i : Λ, V →ₗ[k] V := fun i =>
    Finsupp.lapply i ∘ₗ tensorCoefficients.toLinearMap ∘ₗ gradedCoactionMap G
  have hp (i : Λ) : p i = (G.piece i).subtype ∘ₗ
      DirectSum.component k Λ (G.piece ·) i ∘ₗ (gradingDecomposition G).toLinearMap := by
    apply WeightGrading.linearMap_ext G
    intro j x
    simp only [p, LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
      gradedCoactionMap_apply_of_mem, tensorCoefficients_tmul, Finsupp.single_apply,
      gradingDecomposition_apply_of_mem]
    by_cases h : j = i
    · subst j
      simp
    · simp [DirectSum.component.of, h]
  have he : (coactionToGrading (gradingToCoaction G)).piece = G.piece := by
    funext i
    ext v
    change v ∈ weightSpace (gradingToCoaction G) i ↔ v ∈ G.piece i
    rw [mem_weightSpace]
    constructor
    · intro h
      have hv : p i v = v := by
        change tensorCoefficients (gradedCoactionMap G v) i = v
        change gradedCoactionMap G v = _ at h
        rw [h, tensorCoefficients_tmul, Finsupp.single_eq_same]
      rw [← hv, hp]
      exact (DirectSum.component k Λ (G.piece ·) i (gradingDecomposition G v)).property
    · intro h
      exact gradedCoactionMap_apply_of_mem G i ⟨v, h⟩
  suffices ∀ G H : WeightGrading k Λ V, G.piece = H.piece → G = H from this _ _ he
  rintro ⟨p, _⟩ ⟨q, _⟩ h
  dsimp at h
  subst q
  rfl

theorem gradingCoactionComparison : GradingCoactionComparison.{u} := by
  intro k Λ V _ _ _ _
  refine ⟨⟨gradingToCoaction, coactionToGrading, gradingToCoaction_leftInverse,
    gradingToCoaction_rightInverse⟩, ?_⟩
  intro G i
  exact congrArg (fun H : WeightGrading k Λ V => H.piece i) (gradingToCoaction_leftInverse G)

section CompatibleCoactions

open WeightDecomposition (tensorCoactionMap)

variable {A : Type u} [CommRing A] [Algebra k A]
  [Module A V] [IsScalarTower k A V]

private theorem gradingToCoaction_smul (G : RingGrading k Λ A) (H : ModuleGrading G V) :
    IsModuleCoaction (gradingToCoaction G.toWeightGrading) (gradingToCoaction H.toWeightGrading) := by
  unfold IsModuleCoaction
  apply TensorProduct.ext
  apply WeightGrading.linearMap_ext G.toWeightGrading
  intro i r
  apply WeightGrading.linearMap_ext H.toWeightGrading
  intro j v
  let w : H.toWeightGrading.piece (i * j) := ⟨(r : A) • (v : V), H.smul_mem r.property v.property⟩
  change gradedCoactionMap H.toWeightGrading (scalarTensor ((r : A) ⊗ₜ[k] (v : V))) =
    scalarTensor.rTensor B
      (tensorCoactionMap (gradingToCoaction G.toWeightGrading)
        (gradingToCoaction H.toWeightGrading) ((r : A) ⊗ₜ[k] (v : V)))
  change gradedCoactionMap H.toWeightGrading (w : V) = _
  simp only [tensorCoactionMap, LinearMap.comp_apply, TensorProduct.map_tmul]
  change _ = scalarTensor.rTensor B
    ((LinearMap.mul' k B).lTensor (A ⊗[k] V)
      ((TensorProduct.tensorTensorTensorComm k A B V B)
        (gradedCoactionMap G.toWeightGrading (r : A) ⊗ₜ[k]
          gradedCoactionMap H.toWeightGrading (v : V))))
  rw [gradedCoactionMap_apply_of_mem _ _ w, gradedCoactionMap_apply_of_mem _ _ r,
    gradedCoactionMap_apply_of_mem _ _ v, TensorProduct.tensorTensorTensorComm_tmul,
    LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply, ← map_mul]
  rfl

private theorem smul_mem_of_coaction (ρ : RightComodule k (groupAlgebra k Λ) A)
    (δ : RightComodule k (groupAlgebra k Λ) V) (h : IsModuleCoaction ρ δ)
    {i j : Λ} {r : A} {v : V}
    (hr : r ∈ weightSpace ρ i) (hv : v ∈ weightSpace δ j) :
    r • v ∈ weightSpace δ (i * j) := by
  apply mem_weightSpace.mpr
  have h' := DFunLike.congr_fun h (r ⊗ₜ[k] v)
  change δ.coaction (r • v) = _ at h'
  simpa only [tensorCoactionMap, LinearMap.comp_apply, TensorProduct.map_tmul,
    mem_weightSpace.mp hr, mem_weightSpace.mp hv, LinearEquiv.coe_coe,
    TensorProduct.tensorTensorTensorComm_tmul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    LinearMap.mul'_apply, ← map_mul, scalarTensor, TensorProduct.lift.tmul, AlgHom.toLinearMap_apply,
    Algebra.lsmul_apply] using h'

private def ringGradingToCoaction (G : RingGrading k Λ A) :
    {ρ : RightComodule k (groupAlgebra k Λ) A // IsRingCoaction ρ} := by
  let H : ModuleGrading G A := { G.toWeightGrading with smul_mem := G.mul_mem }
  refine ⟨gradingToCoaction G.toWeightGrading, ?_, gradingToCoaction_smul G H⟩
  have h := gradedCoactionMap_apply_of_mem G.toWeightGrading (1 : Λ) ⟨1, G.one_mem⟩
  exact h.trans (by rw [map_one])

private def coactionToRingGrading
    (ρ : {ρ : RightComodule k (groupAlgebra k Λ) A // IsRingCoaction ρ}) : RingGrading k Λ A :=
  { coactionToGrading ρ.val with
    one_mem := mem_weightSpace.mpr <| ρ.property.1.trans (by rw [map_one])
    mul_mem := smul_mem_of_coaction ρ.val ρ.val ρ.property.2 }

private def ringGradingEquiv :
    RingGrading k Λ A ≃ {ρ : RightComodule k (groupAlgebra k Λ) A // IsRingCoaction ρ} where
  toFun := ringGradingToCoaction
  invFun := coactionToRingGrading
  left_inv G := by
    have h : (coactionToRingGrading (ringGradingToCoaction G)).toWeightGrading =
        G.toWeightGrading := gradingToCoaction_leftInverse _
    suffices ∀ G H : RingGrading k Λ A, G.toWeightGrading = H.toWeightGrading → G = H from
      this _ _ h
    rintro ⟨G, _, _⟩ ⟨H, _, _⟩ h
    dsimp at h
    subst H
    rfl
  right_inv ρ := Subtype.ext (gradingToCoaction_rightInverse ρ.val)

private def moduleGradingEquiv (G : RingGrading k Λ A) :
    ModuleGrading G V ≃
      {δ : RightComodule k (groupAlgebra k Λ) V // IsModuleCoaction (ringGradingEquiv G).val δ} where
  toFun H := ⟨gradingToCoaction H.toWeightGrading, gradingToCoaction_smul G H⟩
  invFun δ := { coactionToGrading δ.val with
    smul_mem := fun {i j r v} hr hv =>
      smul_mem_of_coaction _ δ.val δ.property (by
        have h := congrArg (fun H : WeightGrading k Λ A => H.piece i)
          (gradingToCoaction_leftInverse G.toWeightGrading)
        change weightSpace (gradingToCoaction G.toWeightGrading) i = G.piece i at h
        change r ∈ weightSpace (gradingToCoaction G.toWeightGrading) i
        rw [h]
        exact hr) hv }
  left_inv H := by
    have ext (G₁ G₂ : ModuleGrading G V)
        (h : G₁.toWeightGrading = G₂.toWeightGrading) : G₁ = G₂ := by
      obtain ⟨G₁, _⟩ := G₁
      obtain ⟨G₂, _⟩ := G₂
      dsimp at h
      subst G₂
      rfl
    exact ext _ _ (gradingToCoaction_leftInverse H.toWeightGrading)
  right_inv δ := Subtype.ext (gradingToCoaction_rightInverse δ.val)

theorem algebraComoduleComparison : AlgebraComoduleComparison.{u} := by
  intro k Λ A _ _ _ _
  refine ⟨ringGradingEquiv, ?_, ?_⟩
  · intro G i
    exact congrArg (fun H : WeightGrading k Λ A => H.piece i)
      (gradingToCoaction_leftInverse G.toWeightGrading)
  · intro G V _ _ _ _
    refine ⟨moduleGradingEquiv G, fun H i => ?_⟩
    exact congrArg (fun J : WeightGrading k Λ V => J.piece i)
      (gradingToCoaction_leftInverse H.toWeightGrading)

end CompatibleCoactions

private def weightProject (G : WeightGrading k Λ V) (i : Λ) : V →ₗ[k] G.piece i :=
  (DirectSum.component k Λ (G.piece ·) i).comp (gradingDecomposition G).toLinearMap

private theorem weightProject_of_mem (G : WeightGrading k Λ V) (i : Λ) (x : G.piece i) :
    weightProject G i x = x := by
  simp [weightProject, gradingDecomposition_apply_of_mem]

private theorem weightProject_natural (G : WeightGrading k Λ V) (H : WeightGrading k Λ W)
    (f : V →ₗ[k] W) (hf : PreservesWeight G H f) (i : Λ) (v : V) :
    f.restrict (hf i) (weightProject G i v) = weightProject H i (f v) := by
  let p := (f.restrict (hf i)).comp (weightProject G i)
  let q := (weightProject H i).comp f
  change p v = q v
  suffices p = q from DFunLike.congr_fun this v
  apply WeightGrading.linearMap_ext G
  intro j x
  change f.restrict (hf i) (weightProject G i x) = weightProject H i (f x)
  have h := gradingDecomposition_apply_of_mem H j ⟨f x, hf j x.property⟩
  by_cases hji : j = i
  · subst j
    rw [weightProject_of_mem]
    exact (weightProject_of_mem H i ⟨f x, hf i x.property⟩).symm
  · simp [weightProject, gradingDecomposition_apply_of_mem, h, DirectSum.component.of, hji]

theorem exactOnWeights : ExactOnWeights.{u} := by
  intro k Λ V W U _ _ _ _ _ _ _ _ G H J f g hf hg hinj hex hsurj i
  refine ⟨fun x y h => Subtype.ext (hinj (congrArg Subtype.val h)), ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      have hy' : g y = 0 := congrArg Subtype.val hy
      obtain ⟨x, hx⟩ := (hex y).mp hy'
      exact ⟨weightProject G i x, (weightProject_natural G H f hf i x).trans
        (by rw [hx, weightProject_of_mem])⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext ((hex (f x)).mpr ⟨x, rfl⟩)
  · intro z
    obtain ⟨y, hy⟩ := hsurj z
    exact ⟨weightProject H i y, (weightProject_natural H J g hg i y).trans
      (by rw [hy, weightProject_of_mem])⟩

private theorem nonzeroWeights_finite [Module.Finite k V] (G : WeightGrading k Λ V) :
    {i | G.piece i ≠ ⊥}.Finite := by
  have h (i : Λ) : weightSpace (gradingToCoaction G) i = G.piece i :=
    congrArg (fun H : WeightGrading k Λ V => H.piece i) (gradingToCoaction_leftInverse G)
  simpa only [h] using WeightDecomposition.finiteWeights (gradingToCoaction G)

private def gradedCharacter [Module.Finite k V] (G : WeightGrading k Λ V) :
    MonoidAlgebra ℤ Λ :=
  MonoidAlgebra.ofCoeff (Finsupp.onFinset (nonzeroWeights_finite G).toFinset
    (fun i => (Module.finrank k (G.piece i) : ℤ))
    (fun i hi => by
      by_contra hn
      have hz : G.piece i = ⊥ := by
        simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hn
      exact hi (by rw [hz, finrank_bot]; rfl)))

@[simp]
private theorem gradedCharacter_coeff [Module.Finite k V] (G : WeightGrading k Λ V) (i : Λ) :
    (gradedCharacter G).coeff i = (Module.finrank k (G.piece i) : ℤ) := rfl

private theorem gradedCharacter_add [Module.Finite k V] [Module.Finite k W] [Module.Finite k U]
    (G : WeightGrading k Λ V) (H : WeightGrading k Λ W) (J : WeightGrading k Λ U)
    (f : V →ₗ[k] W) (g : W →ₗ[k] U)
    (hf : PreservesWeight G H f) (hg : PreservesWeight H J g)
    (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g) :
    gradedCharacter H = gradedCharacter G + gradedCharacter J := by
  ext i
  simp only [gradedCharacter_coeff, MonoidAlgebra.coeff_add, Finsupp.add_apply]
  have ⟨hi, he, hs⟩ := exactOnWeights G H J f g hf hg hinj hex hsurj i
  let f' := f.restrict (hf i)
  let g' := g.restrict (hg i)
  have h := g'.finrank_range_add_finrank_ker
  change Function.Exact f' g' at he
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, LinearMap.exact_iff.mp he,
    LinearMap.finrank_range_of_inj hi, add_comm] at h
  exact_mod_cast h.symm

private theorem gradedCharacter_shift [Module.Finite k V]
    (G H : WeightGrading k Λ V) (χ : Λ)
    (h : ∀ ψ, H.piece (χ * ψ) = G.piece ψ) :
    gradedCharacter H = MonoidAlgebra.of ℤ Λ χ * gradedCharacter G := by
  ext ψ
  change (gradedCharacter H).coeff ψ = (MonoidAlgebra.single χ 1 * gradedCharacter G).coeff ψ
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul, gradedCharacter_coeff, gradedCharacter_coeff]
  have he : H.piece ψ = G.piece (χ⁻¹ * ψ) := by simpa only [mul_inv_cancel_left] using h (χ⁻¹ * ψ)
  rw [he]

theorem gradedCharacterLaws : GradedCharacterLaws.{u} := by
  intro k Λ _ _
  refine ⟨fun _ _ _ _ G => gradedCharacter G, ?_, ?_, ?_⟩
  · intro V _ _ _
    exact gradedCharacter_coeff
  · intro V W U _ _ _ _ _ _ _ _ _
    exact gradedCharacter_add
  · intro V _ _ _
    exact gradedCharacter_shift

end Grading

section WeightsOfSections

variable {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y}

/-- A character pulls the invertible coordinate on the multiplicative group
back to an invertible global function. -/
theorem isUnit_characterFunction (χ : Character T) : IsUnit (characterFunction χ) := by
  unfold characterFunction
  apply IsUnit.map (χ.hom.hom.left.appTop.hom)
  apply IsUnit.map (Scheme.ΓSpecIso _).inv.hom
  exact ⟨Units.map (MonoidAlgebra.of k _) (toUnits Specs.DiagonalizableGroups.integerGenerator), rfl⟩

/-- The nonvanishing locus of a homogeneous function is invariant. -/
theorem basicOpen_invariant_of_weight (f : Γ(X.left, ⊤)) (χ : Character T)
    (hf : HasFunctionWeight a f χ) :
    a.smul.left ⁻¹ᵁ (X.left.basicOpen f) = (snd T.X X).left ⁻¹ᵁ (X.left.basicOpen f) := by
  change a.smul.left.appTop f = _ at hf
  rw [Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top, hf, Scheme.basicOpen_mul]
  let c := (fst T.X X).left.appTop (characterFunction χ⁻¹)
  let d := (snd T.X X).left.appTop f
  have hc : IsUnit c := (isUnit_characterFunction χ⁻¹).map (fst T.X X).left.appTop.hom
  change (T.X ⊗ X).left.basicOpen c ⊓ (T.X ⊗ X).left.basicOpen d = (T.X ⊗ X).left.basicOpen d
  rw [Scheme.basicOpen_of_isUnit _ hc, top_inf_eq]

private theorem comp_appTop_apply {V W U : SchemeOver k} (i : V ⟶ W) (j : W ⟶ U)
    (r : Γ(U.left, ⊤)) :
    (i ≫ j).left.appTop r = i.left.appTop (j.left.appTop r) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

/-- Pulling a global function back along an equivariant morphism preserves
its weight. -/
theorem functionWeight_pullback (j : Y ⟶ X) (hj : IsEquivariantMap a b j)
    (f : Γ(X.left, ⊤)) (χ : Character T) (hf : HasFunctionWeight a f χ) :
    HasFunctionWeight b (j.left.appTop f) χ := by
  let q := 𝟙 T.X ⊗ₘ j
  have hfst : q ≫ fst T.X X = fst T.X Y := by simp [q]
  have hsnd : q ≫ snd T.X X = snd T.X Y ≫ j := by simp [q]
  let r := characterFunction χ⁻¹
  change a.smul.left.appTop f = (fst T.X X).left.appTop r * (snd T.X X).left.appTop f at hf
  change b.smul.left.appTop (j.left.appTop f) =
    (fst T.X Y).left.appTop r * (snd T.X Y).left.appTop (j.left.appTop f)
  calc
    _ = (b.smul ≫ j).left.appTop f := (comp_appTop_apply b.smul j f).symm
    _ = (q ≫ a.smul).left.appTop f := by rw [hj]
    _ = q.left.appTop ((fst T.X X).left.appTop r * (snd T.X X).left.appTop f) := by
      rw [comp_appTop_apply, hf]
    _ = (q ≫ fst T.X X).left.appTop r * (q ≫ snd T.X X).left.appTop f := by
      rw [map_mul, comp_appTop_apply, comp_appTop_apply]
    _ = _ := by rw [hfst, hsnd, comp_appTop_apply]


theorem homogeneousBasicOpenInvariant : HomogeneousBasicOpenInvariant.{u} :=
  fun a r χ hr => basicOpen_invariant_of_weight (a := a) r χ hr

theorem pullSection_naturality {U V : Scheme.{u}} (f : V ⟶ U)
    {F G : U.Modules} (g : F ⟶ G) (s : Γ(F, ⊤)) :
    pullSection f G (g.val.app (op ⊤) s) =
      ((Scheme.Modules.pullback f).map g).val.app (op ⊤) (pullSection f F s) := by
  let u := (Scheme.Modules.pullbackPushforwardAdjunction f).unit
  have h := u.naturality g
  exact congrArg (fun h : F ⟶ ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).obj G) =>
    h.val.app (op ⊤) s) h

theorem pullSection_smul {U V : Scheme.{u}} (f : V ⟶ U) (F : U.Modules)
    (r : Γ(U, ⊤)) (s : Γ(F, ⊤)) :
    pullSection f F (r • s) = f.appTop r • pullSection f F s := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op ⊤)
    |>.hom.map_smul r s

set_option backward.isDefEq.respectTransparency false in
theorem pullSection_comp {U V W : Scheme.{u}} (f : W ⟶ V) (g : V ⟶ U)
    (F : U.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app F).val.app (op ⊤)
      (pullSection f ((Scheme.Modules.pullback g).obj F) (pullSection g F s)) =
        pullSection (f ≫ g) F s := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction g
  let B := Scheme.Modules.pullbackPushforwardAdjunction f
  let C := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let h := Scheme.Modules.pullbackComp f g
  let R := Scheme.Modules.pushforward (f ≫ g)
  have e := unit_conjugateEquiv (A.comp B) C h.inv F
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at e
  have e' := congrArg (· ≫ R.map (h.hom.app F)) e
  have ei : R.map (h.inv.app F) ≫ R.map (h.hom.app F) = 𝟙 _ :=
    (R.mapIso (h.app F)).inv_hom_id
  have e'' : (A.comp B).unit.app F ≫
      (Scheme.Modules.pushforwardComp f g).hom.app _ ≫ R.map (h.hom.app F) = C.unit.app F := by
    change ((A.comp B).unit.app F ≫ _) ≫ _ = (C.unit.app F ≫ R.map (h.inv.app F)) ≫ _ at e'
    rw [Category.assoc, Category.assoc, ei] at e'
    exact e'.trans (Category.comp_id _)
  rw [Adjunction.comp_unit_app] at e''
  exact congrArg (fun z => z.val.app (op ⊤) s) e''

theorem pullSection_congr {U V : Scheme.{u}} {f g : V ⟶ U} (w : f = g)
    (F : U.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackCongr w).hom.app F).val.app (op ⊤) (pullSection f F s) =
      pullSection g F s := by
  subst g
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem linearizedMap_preserves_sectionWeight {F G : X.left.Modules}
    {L : Linearization a F} {K : Linearization a G} {g : F ⟶ G}
    (h : IsLinearizedMap L K g) {χ : Character T} {s : Γ(F, ⊤)}
    (hs : HasSectionWeight L s χ) :
    HasSectionWeight K (g.val.app (op ⊤) s) χ := by
  let P := snd T.X X
  let A := a.smul
  let gh := ((Scheme.Modules.pullback A.left).map g).val.app (op ⊤)
  let gp := ((Scheme.Modules.pullback P.left).map g).val.app (op ⊤)
  let t := pullSection P.left F s
  have he := congrArg (fun f : Pull P F ⟶ Pull A G => f.val.app (op ⊤) t) h
  change gh (L.iso.hom.val.app (op ⊤) t) = K.iso.hom.val.app (op ⊤) (gp t) at he
  unfold HasSectionWeight
  rw [pullSection_naturality, pullSection_naturality]
  change K.iso.hom.val.app (op ⊤) (gp t) =
    (fst T.X X).left.appTop (characterFunction χ) • gh (pullSection A.left F s)
  rw [← he]
  change L.iso.hom.val.app (op ⊤) t = _ at hs
  rw [hs]
  exact gh.hom.map_smul _ _

end WeightsOfSections

section AffineSectionComparison

open FlatCohomology (affinePullback affinePushforwardSections)

variable {R S : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
private theorem normalizedTildePullback (φ : R ⟶ S) (M : ModuleCat.{u} R) :
    ∃ e : (moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M)) ≅
        (ModuleCat.extendScalars.{u,u,u} φ.hom).obj M,
      ∀ s : M, e.hom (pullSection (Spec.map φ) (tilde M) ((tilde.isoTop M).hom s)) =
        (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M s := by
  obtain ⟨e₀, h₀⟩ := affinePullback φ
  let N := (ModuleCat.extendScalars.{u,u,u} φ.hom).obj M
  let Γ' := moduleSpecΓFunctor (R := S)
  let e := Γ'.mapIso (e₀.app M) ≪≫ (tilde.isoTop N).symm
  refine ⟨e, fun s => ?_⟩
  have h := h₀ M
  simp only [Adjunction.homEquiv_unit] at h
  have hs := congrArg (fun g => g s) h
  have hs' : (Γ'.map (e₀.hom.app M))
      (pullSection (Spec.map φ) (tilde M) ((tilde.isoTop M).hom s)) =
      (tilde.isoTop N).hom ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M s) := hs
  change (tilde.isoTop N).inv
    ((Γ'.map (e₀.hom.app M)) (pullSection (Spec.map φ) (tilde M) ((tilde.isoTop M).hom s))) = _
  rw [hs']
  exact congrArg (fun (f : N ⟶ N) => f ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M s))
    (tilde.isoTop N).hom_inv_id

set_option backward.isDefEq.respectTransparency false in
theorem affineSectionBaseChange : AffineSectionBaseChange.{u} := by
  intro R S φ F hF
  let M := (moduleSpecΓFunctor (R := R)).obj F
  let q : tilde M ≅ F := asIso F.fromTildeΓ
  let Γ' := moduleSpecΓFunctor (R := S)
  let P := Scheme.Modules.pullback (Spec.map φ)
  obtain ⟨e, he⟩ := normalizedTildePullback φ M
  refine ⟨(Γ'.mapIso (P.mapIso q)).symm ≪≫ e, ?_⟩
  intro s
  have hn := pullSection_naturality (Spec.map φ) q.inv s
  change e.hom (((P.map q.inv).val.app (op ⊤)) (pullSection (Spec.map φ) F s)) = _
  rw [← hn]
  let D := tilde.adjunction (R := R)
  let G := moduleSpecΓFunctor (R := R)
  have htw : G.map q.inv = D.unit.app M := by
    apply (cancel_mono (G.map q.hom)).mp
    calc
      _ = G.map (q.inv ≫ q.hom) := (G.map_comp _ _).symm
      _ = G.map (𝟙 F) := congrArg G.map q.inv_hom_id
      _ = 𝟙 M := G.map_id _
      _ = _ := (D.right_triangle_components F).symm
  change e.hom (pullSection (Spec.map φ) (tilde M) ((G.map q.inv) s)) = _
  rw [htw]
  exact he s

set_option backward.isDefEq.respectTransparency false in
theorem affineSectionsExact : AffineSectionsExact.{u} := by
  intro R K h1 h2 h3 hK
  let G := moduleSpecΓFunctor (R := R)
  let D := tilde.functor R
  let adj := tilde.adjunction (R := R)
  let e₂ := asIso K.X₂.fromTildeΓ
  let e₃ := asIso K.X₃.fromTildeΓ
  let : G.IsRightAdjoint := adj.isRightAdjoint
  let : Mono K.f := hK.mono_f
  let : Epi K.g := hK.epi_g
  have hn : D.map (G.map K.g) ≫ e₃.hom = e₂.hom ≫ K.g :=
    adj.counit.naturality K.g
  have epi_tilde : Epi (D.map (G.map K.g)) := by
    rw [← epi_comp_iff_of_isIso _ e₃.hom, hn]
    infer_instance
  let : Epi (D.map (G.map K.g)) := epi_tilde
  let : Epi (G.map K.g) := by
    constructor
    intro P f g h
    apply D.map_injective
    apply (cancel_epi (D.map (G.map K.g))).mp
    rw [← D.map_comp, h, D.map_comp]
  let K' := K.map G
  have lim : IsLimit (KernelFork.ofι K'.f K'.zero) := by
    exact isLimitForkMapOfIsLimit' G K.zero hK.fIsKernel
  have hdoc : K'.ShortExact := ShortComplex.ShortExact.mk'
    (K'.exact_of_f_is_kernel lim) (inferInstanceAs (Mono (G.map K.f)))
    (inferInstanceAs (Epi (G.map K.g)))
  exact ⟨(ModuleCat.mono_iff_injective _).mp hdoc.mono_f,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact K').mp hdoc.exact,
    (ModuleCat.epi_iff_surjective _).mp hdoc.epi_g⟩

end AffineSectionComparison

section CoordinateCharacters

open _root_.LinearAlgebraicGroups.CharacterDescent
open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)

private def characterPrecomp {T U : GroupScheme k} (j : T ≅ U) :
    Character U ≃* Character T where
  toFun χ := j.hom ≫ χ
  invFun χ := j.inv ≫ χ
  left_inv χ := by simp
  right_inv χ := by simp
  map_mul' χ ψ := by
    apply Grp.hom_ext
    exact MonObj.comp_mul j.hom.hom.hom χ.hom.hom ψ.hom.hom

private theorem characterFunction_comp {T U : GroupScheme k} (f : T ⟶ U) (χ : Character U) :
    characterFunction (f ≫ χ) = f.hom.hom.left.appTop (characterFunction χ) :=
  comp_appTop_apply f.hom.hom χ.hom.hom _

private def ringIsoEquiv {R S : CommRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem characterFunction_of_splitExponent (r : ℕ) :
    ∃ e : StandardLattice.{u} r ≃* Character (specGroup (groupAlgebra k (StandardLattice.{u} r))),
      ∀ m, characterFunction (e m) =
        (Scheme.ΓSpecIso (CommRingCat.of (MonoidAlgebra k (StandardLattice.{u} r)))).inv
          (MonoidAlgebra.of k _ m) := by
  obtain ⟨e, _, he, _, _⟩ := splitCompositionPairing (k := k) r
  refine ⟨e, fun m => ?_⟩
  rw [he]
  let R := CommRingCat.of (MonoidAlgebra k (StandardLattice.{u} r))
  let B := CommRingCat.of (MonoidAlgebra k IntegerCharacters)
  let φ : B ⟶ R := CommRingCat.ofHom
    (MonoidAlgebra.mapDomainBialgHom k
      ((zpowersHom (StandardLattice.{u} r) m).comp MulEquiv.ulift.toMonoidHom)).toAlgHom.toRingHom
  let g := MonoidAlgebra.of k IntegerCharacters integerGenerator
  change ((Scheme.ΓSpecIso B).inv ≫ (Spec.map φ).appTop) g =
    (Scheme.ΓSpecIso R).inv (MonoidAlgebra.of k _ m)
  rw [← Scheme.ΓSpecIso_inv_naturality]
  change (Scheme.ΓSpecIso R).inv (φ g) = _
  congr 1
  show MonoidAlgebra.mapDomainBialgHom k _ (MonoidAlgebra.single integerGenerator 1) = _
  rw [MonoidAlgebra.mapDomainBialgHom_single]
  change MonoidAlgebra.single (m ^ (1 : ℤ)) (1 : k) = MonoidAlgebra.single m 1
  rw [zpow_one]

theorem coordinateCharacters : CoordinateCharacters.{u} := by
  intro k _ T hT
  obtain ⟨r, ⟨j⟩⟩ := hT
  obtain ⟨d⟩ := standardSplitTorus (k := k) r
  let a := j ≪≫ d.symm
  obtain ⟨e, h⟩ := characterFunction_of_splitExponent (k := k) r
  let E := e.trans (characterPrecomp a)
  let b := (Spec (CommRingCat.of (MonoidAlgebra k (StandardLattice.{u} r))))
  let d' : T.X.left ≅ b := ⟨a.hom.hom.hom.left, a.inv.hom.hom.left,
    by
      have h := congrArg (fun g : T ⟶ T => g.hom.hom.left) a.hom_inv_id
      exact h,
    by
      have h := congrArg (fun g : specGroup (groupAlgebra k (StandardLattice.{u} r)) ⟶
          specGroup (groupAlgebra k (StandardLattice.{u} r)) => g.hom.hom.left) a.inv_hom_id
      exact h⟩
  let Γd : Γ(b, ⊤) ≅ Γ(T.X.left, ⊤) := Scheme.Γ.mapIso d'.op
  let e' := (MonoidAlgebra.domCongr k k E.symm).toRingEquiv.trans
    ((ringIsoEquiv (Scheme.ΓSpecIso (CommRingCat.of (MonoidAlgebra k (StandardLattice.{u} r)))).symm).trans
      (ringIsoEquiv Γd))
  refine ⟨e', fun χ => ?_⟩
  obtain ⟨m, rfl⟩ := E.surjective χ
  change a.hom.hom.hom.left.appTop ((Scheme.ΓSpecIso _).inv
    (MonoidAlgebra.domCongr k k E.symm (MonoidAlgebra.single (E m) 1))) = _
  rw [MonoidAlgebra.domCongr_single, MulEquiv.symm_apply_apply]
  exact (congrArg (fun c => a.hom.hom.hom.left.appTop c) (h m)).symm.trans
    (characterFunction_comp a.hom (e m)).symm

end CoordinateCharacters

section WeightArithmetic

variable {T : GroupScheme k} {X : SchemeOver k} {a : ModObj T.X X}

theorem characterFunction_mul (hT : IsSplitTorus T) (χ ψ : Character T) :
    characterFunction (χ * ψ) = characterFunction χ * characterFunction ψ := by
  obtain ⟨e, h⟩ := coordinateCharacters T hT
  rw [← h, ← h χ, ← h ψ, map_mul, map_mul]

theorem characterFunction_one (hT : IsSplitTorus T) :
    characterFunction (1 : Character T) = 1 := by
  obtain ⟨e, h⟩ := coordinateCharacters T hT
  rw [← h, map_one, map_one]

set_option backward.isDefEq.respectTransparency false in
theorem sectionWeight_smul (hT : IsSplitTorus T) {F : X.left.Modules}
    (L : Linearization a F) {r : Γ(X.left, ⊤)} {s : Γ(F, ⊤)}
    {χ δ : Character T} (hr : HasFunctionWeight a r δ) (hs : HasSectionWeight L s χ) :
    HasSectionWeight L (r • s) (δ * χ) := by
  let P := (snd T.X X).left
  let A := a.smul.left
  let c : Γ((T.X ⊗ X).left, ⊤) := (fst T.X X).left.appTop (characterFunction χ)
  let d : Γ((T.X ⊗ X).left, ⊤) := (fst T.X X).left.appTop (characterFunction δ)
  let b : Γ((T.X ⊗ X).left, ⊤) := (fst T.X X).left.appTop (characterFunction δ⁻¹)
  have he : d * b = 1 := by
    rw [← map_mul, ← characterFunction_mul hT, mul_inv_cancel, characterFunction_one hT, map_one]
  unfold HasSectionWeight
  rw [pullSection_smul, pullSection_smul, characterFunction_mul hT, map_mul]
  change L.iso.hom.val.app (op ⊤) (P.appTop r • pullSection P F s) =
    (d * c) • (A.appTop r • pullSection A F s)
  rw [(L.iso.hom.val.app (op ⊤)).hom.map_smul]
  change L.iso.hom.val.app (op ⊤) (pullSection P F s) = c • pullSection A F s at hs
  change A.appTop r = b * P.appTop r at hr
  rw [hs, hr, ← mul_smul, ← mul_smul]
  congr 1
  calc
    _ = 1 * (P.appTop r * c) := (one_mul _).symm
    _ = (d * b) * (P.appTop r * c) := by rw [he]
    _ = _ := by ac_rfl

set_option backward.isDefEq.respectTransparency false in
theorem multiply_app_top (F : X.left.Modules) (c : Γ(X.left, ⊤)) (s : Γ(F, ⊤)) :
    (multiply F c).val.app (op ⊤) s = c • s := by
  have h : (⊤ : X.left.Opens).leTop.op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  change (X.left.presheaf.map (⊤ : X.left.Opens).leTop.op).hom c • s = _
  rw [h]
  have hm : X.left.presheaf.map (𝟙 (op (⊤ : X.left.Opens))) =
      𝟙 (X.left.presheaf.obj (op ⊤)) := X.left.presheaf.map_id _
  exact congrArg (fun g : Γ(X.left, ⊤) ⟶ Γ(X.left, ⊤) => g c • s) hm

set_option backward.isDefEq.respectTransparency false in
theorem sectionWeight_twist (hT : IsSplitTorus T) {F : X.left.Modules}
    (L K : Linearization a F) (δ χ : Character T) (s : Γ(F, ⊤))
    (h : K.iso.hom = L.iso.hom ≫ multiply _
      ((fst T.X X).left.appTop (characterFunction δ))) :
    HasSectionWeight K s (δ * χ) ↔ HasSectionWeight L s χ := by
  unfold HasSectionWeight
  rw [h, SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    multiply_app_top, characterFunction_mul hT, map_mul, mul_smul]
  obtain ⟨u, hu⟩ := (isUnit_characterFunction δ).map (fst T.X X).left.appTop.hom
  rw [← hu]
  exact (MulAction.injective (β := Γ(Pull a.smul F, ⊤)) u).eq_iff

end WeightArithmetic

section InvariantOpen
@[instance_reducible]
private def actionOfMono {C : Type*} [Category C] [MonoidalCategory C]
    {M X Y : C} [MonObj M] (a : ModObj M X) (i : Y ⟶ X) [Mono i]
    (r : M ⊗ Y ⟶ Y) (hr : r ≫ i = M ◁ i ≫ a.smul) : ModObj M Y where
  smul := r
  one_smul := by
    change (η[M] ▷ Y) ≫ r = (λ_ Y).hom
    apply (cancel_mono i).mp
    rw [Category.assoc, hr, ← whisker_exchange_assoc,
      ModObj.one_smul_self, leftUnitor_naturality]
  mul_smul := by
    change (μ[M] ▷ Y) ≫ r = (α_ M M Y).hom ≫ M ◁ r ≫ r
    apply (cancel_mono i).mp
    simp only [Category.assoc, hr]
    have H := congrArg (M ◁ ·) hr
    simp only [whiskerLeft_comp] at H
    rw [← whisker_exchange_assoc, ModObj.mul_smul_self,
      associator_naturality_right_assoc, reassoc_of% H]

variable {T : GroupScheme k} {X : SchemeOver k}
  (a : ModObj T.X X) (U : X.left.Opens)
  (hU : a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U)

private instance openInclusion_isOpenImmersion (V : X.left.Opens) :
    IsOpenImmersion (openEmbedding X V).left :=
  inferInstanceAs (IsOpenImmersion V.ι)

include hU in
private theorem invariantOpen_range :
    Set.range ((T.X ◁ openEmbedding X U) ≫ a.smul).left ⊆
      Set.range (openEmbedding X U).left := by
  let j := openEmbedding X U
  rw [show Set.range j.left = (U : Set X.left) from Scheme.Opens.range_ι U]
  rintro _ ⟨z, rfl⟩
  have hz : a.smul.left ((T.X ◁ j).left z) ∈ U := by
    change (T.X ◁ j).left z ∈ a.smul.left ⁻¹ᵁ U
    rw [hU]
    change (snd T.X X).left ((T.X ◁ j).left z) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left]
    have h : (T.X ◁ j) ≫ snd T.X X = snd T.X _ ≫ j := by simp
    rw [h, Over.comp_left, Scheme.Hom.comp_apply]
    exact (Scheme.Opens.range_ι U).le ⟨(snd T.X _).left z, rfl⟩
  exact hz

private def invariantOpen_smul :
    T.X ⊗ openSubscheme X U ⟶ openSubscheme X U :=
  let j := openEmbedding X U
  let g := (T.X ◁ j) ≫ a.smul
  Over.homMk (IsOpenImmersion.lift j.left g.left (invariantOpen_range a U hU))
    (by
      change (IsOpenImmersion.lift j.left g.left _ ≫ j.left) ≫ X.hom = _
      rw [IsOpenImmersion.lift_fac]
      exact Over.w g)

@[reassoc]
private theorem invariantOpen_smul_comp :
    invariantOpen_smul a U hU ≫ openEmbedding X U =
      (T.X ◁ openEmbedding X U) ≫ a.smul :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

/-- An invariant open subscheme inherits the action of the ambient scheme. -/
@[instance_reducible]
def invariantOpenAction : ModObj T.X (openSubscheme X U) :=
  letI : Mono (openEmbedding X U) := Over.mono_of_mono_left _
  actionOfMono a (openEmbedding X U) (invariantOpen_smul a U hU)
    (invariantOpen_smul_comp a U hU)

theorem invariantOpenInclusion_equivariant :
    IsEquivariantMap a (invariantOpenAction a U hU) (openEmbedding X U) := by
  exact (invariantOpen_smul_comp a U hU).trans (by rw [id_tensorHom])

theorem invariantOpenAction_exists : InvariantOpenAction.{u} :=
  fun a U h => ⟨invariantOpenAction a U h, invariantOpenInclusion_equivariant a U h⟩

end InvariantOpen
section PullSectionEvaluation

variable {T : GroupScheme k} {X Y Z W : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y}

set_option backward.isDefEq.respectTransparency false in
private theorem comparePull_section (F : X.left.Modules) (f : Z ⟶ Y) (g : Y ⟶ X)
    {h : Z ⟶ X} (e : f ≫ g = h) (s : Γ(F, ⊤)) :
    (comparePull F f g e).hom.app ⊤
      (pullSection f.left (Pull g F) (pullSection g.left F s)) =
    pullSection h.left F s := by
  subst h
  exact pullSection_comp f.left g.left F s

private theorem hom_apply_inv_apply {P : Scheme.{u}} {F G : P.Modules}
    (e : F ≅ G) (s : Γ(F, ⊤)) :
    e.inv.app ⊤ (e.hom.app ⊤ s) = s := by
  calc
    _ = (e.hom ≫ e.inv).app ⊤ s := rfl
    _ = s := by rw [e.hom_inv_id]; rfl

set_option backward.isDefEq.respectTransparency false in
private theorem evalPullIso_section {F : X.left.Modules} {g₁ g₂ : Z ⟶ X}
    (θ : Pull g₁ F ≅ Pull g₂ F) (l : Y ⟶ Z) {x y : Y ⟶ X} (hx : l ≫ g₁ = x)
    (hy : l ≫ g₂ = y) (s : Γ(F, ⊤)) :
    (evalPullIso θ l hx hy).hom.app ⊤ (pullSection x.left F s) =
      (comparePull F l g₂ hy).hom.app ⊤
        (pullSection l.left (Pull g₂ F) (θ.hom.app ⊤ (pullSection g₁.left F s))) := by
  rw [← comparePull_section F l g₁ hx s]
  change (comparePull F l g₂ hy).hom.app ⊤
    (((Scheme.Modules.pullback l.left).map θ.hom).app ⊤
      ((comparePull F l g₁ hx).inv.app ⊤ ((comparePull F l g₁ hx).hom.app ⊤
        (pullSection l.left (Pull g₁ F) (pullSection g₁.left F s))))) = _
  rw [hom_apply_inv_apply]
  exact congrArg ((comparePull F l g₂ hy).hom.app ⊤)
    (pullSection_naturality l.left θ.hom (pullSection g₁.left F s)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a weight section at arbitrary scheme-valued points. -/
theorem transport_sectionWeight {F : X.left.Modules}
    (L : Linearization a F) {s : Γ(F, ⊤)} {χ : Character T}
    (hs : HasSectionWeight L s χ) (t : Z ⟶ T.X) (x : Z ⟶ X) :
    (transport a L.iso t x).hom.app ⊤ (pullSection x.left F s) =
      t.left.appTop (characterFunction χ) • pullSection (actOn a t x).left F s := by
  rw [transport_eq_evalPullIso, evalPullIso_section]
  change L.iso.hom.app ⊤ (pullSection (snd T.X X).left F s) = _ at hs
  rw [hs, pullSection_smul, Scheme.Modules.Hom.app_smul]
  rw [comparePull_section]
  rw [← comp_appTop_apply, lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical pullback of the universal isomorphism preserves the
weight equation on sections. -/
theorem sectionWeight_pullback_iso {f : Y ⟶ X} (hf : IsEquivariantMap a b f)
    {F : X.left.Modules} (L : Linearization a F) {s : Γ(F, ⊤)} {χ : Character T}
    (hs : HasSectionWeight L s χ) :
    (pullbackLinearizationIso hf L.iso).hom.app ⊤
        (pullSection (snd T.X Y).left (Pull f F) (pullSection f.left F s)) =
      (fst T.X Y).left.appTop (characterFunction χ) •
        pullSection b.smul.left (Pull f F) (pullSection f.left F s) := by
  let p := snd T.X Y
  let q := 𝟙 T.X ⊗ₘ f
  let F' := Pull f F
  let v := pullSection p.left F' (pullSection f.left F s)
  let j := pullComp F b.smul f
  let e₁ : q ≫ snd T.X X = p ≫ f := by simp [q, p]
  let e₂ : q ≫ a.smul = b.smul ≫ f := hf.symm
  let θ := evalPullIso L.iso q e₁ e₂
  let c := (fst T.X Y).left.appTop (characterFunction χ)
  let d := (fst T.X X).left.appTop (characterFunction χ)
  have hθ : θ.hom.app ⊤ (pullSection (p ≫ f).left F s) =
      c • pullSection (b.smul ≫ f).left F s := by
    change L.iso.hom.app ⊤ (pullSection (snd T.X X).left F s) =
      d • pullSection a.smul.left F s at hs
    dsimp only [θ]
    rw [evalPullIso_section, hs, pullSection_smul, Scheme.Modules.Hom.app_smul,
      comparePull_section]
    have hq : q ≫ fst T.X X = fst T.X Y := by simp [q]
    rw [← comp_appTop_apply, hq]
  have H₁ : (pullComp F p f).hom.app ⊤ v = pullSection (p ≫ f).left F s :=
    pullSection_comp p.left f.left F s
  have H₂ : j.hom.app ⊤
      (pullSection b.smul.left F' (pullSection f.left F s)) =
      pullSection (b.smul ≫ f).left F s := pullSection_comp b.smul.left f.left F s
  change j.inv.app ⊤ (θ.hom.app ⊤
    ((pullComp F p f).hom.app ⊤ v)) =
    c • pullSection b.smul.left F' (pullSection f.left F s)
  rw [H₁, hθ, ← H₂, ← Scheme.Modules.Hom.app_smul, hom_apply_inv_apply]

end PullSectionEvaluation
section RestrictionToAffines

variable {T : GroupScheme k}

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_spec_isQuasicoherent {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (F : (Spec R).Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback (Spec.map φ)).obj F).IsQuasicoherent := by
  let M := (moduleSpecΓFunctor (R := R)).obj F
  let q : tilde M ≅ F := asIso F.fromTildeΓ
  obtain ⟨e, _⟩ := FlatCohomology.affinePullback φ
  let N := (ModuleCat.extendScalars.{u,u,u} φ.hom).obj M
  let e' : tilde N ≅ ((Scheme.Modules.pullback (Spec.map φ)).obj F) :=
    (e.app M).symm ≪≫ (Scheme.Modules.pullback (Spec.map φ)).mapIso q
  exact (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso e' inferInstance

variable {X : SchemeOver k} {a : ModObj T.X X}

theorem functionWeight_one (hT : IsSplitTorus T) : HasFunctionWeight a 1 1 := by
  simp [HasFunctionWeight, characterFunction_one hT]

theorem functionWeight_mul (hT : IsSplitTorus T) {r s : Γ(X.left, ⊤)}
    {χ ψ : Character T} (hr : HasFunctionWeight a r χ) (hs : HasFunctionWeight a s ψ) :
    HasFunctionWeight a (r * s) (χ * ψ) := by
  unfold HasFunctionWeight at *
  rw [map_mul, hr, hs, mul_inv, characterFunction_mul hT, map_mul, map_mul]
  ac_rfl

theorem functionWeight_pow (hT : IsSplitTorus T) {r : Γ(X.left, ⊤)} {χ : Character T}
    (hr : HasFunctionWeight a r χ) (n : ℕ) : HasFunctionWeight a (r ^ n) (χ ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using functionWeight_one (a := a) hT
  | succ n ih => simpa only [pow_succ] using functionWeight_mul hT ih hr

set_option backward.isDefEq.respectTransparency false in
theorem functionWeight_inv_of_mul_eq_one (hT : IsSplitTorus T) {r s : Γ(X.left, ⊤)}
    {χ : Character T} (hr : HasFunctionWeight a r χ) (hrs : r * s = 1) :
    HasFunctionWeight a s χ⁻¹ := by
  let P := (snd T.X X).left.appTop
  let A := a.smul.left.appTop
  let c := (fst T.X X).left.appTop (characterFunction χ)
  let d := (fst T.X X).left.appTop (characterFunction χ⁻¹)
  have hcd : c * d = 1 := by
    rw [← map_mul, ← characterFunction_mul hT, mul_inv_cancel, characterFunction_one hT, map_one]
  have hA : A r * A s = 1 := by rw [← map_mul, hrs, map_one]
  have hP : P r * P s = 1 := by rw [← map_mul, hrs, map_one]
  change A r = d * P r at hr
  change A s = (fst T.X X).left.appTop (characterFunction (χ⁻¹)⁻¹) * P s
  rw [inv_inv]
  calc
    A s = (c * P s) * (A r * A s) := by
      rw [hr]
      rw [show (c * P s) * ((d * P r) * A s) = (c * d) * (P r * P s) * A s by ac_rfl,
        hcd, hP, one_mul, one_mul]
    _ = c * P s := by rw [hA, mul_one]

end RestrictionToAffines

section ProductCoordinates

open Specs.CharacterDescent (StandardLattice)

set_option backward.isDefEq.respectTransparency false in
private theorem appTop_Spec_map {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) =
      (Scheme.ΓSpecIso S).inv (φ r) := by
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop) r = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

private abbrev groupRingAlgebra (R : TestAlgebra k) (Λ : Type u) [CommGroup Λ] : TestAlgebra k :=
  CommAlgCat.of k (MonoidAlgebra R Λ)

private def groupRingConstants (R : TestAlgebra k) (Λ : Type u) [CommGroup Λ] :
    R ⟶ groupRingAlgebra R Λ :=
  CommAlgCat.ofHom MonoidAlgebra.singleOneAlgHom

set_option backward.isDefEq.respectTransparency false in
/-- A product with a split torus has the monoid algebra over the original
affine chart as its coordinate ring. -/
private theorem torusProductChart (T : GroupScheme k) (hT : IsSplitTorus T)
    (R : TestAlgebra k) :
    let S := groupRingAlgebra R (Character T)
    ∃ e : affineScheme S ≅ T.X ⊗ affineScheme R,
      e.hom ≫ snd T.X (affineScheme R) = (testSpec k).map (groupRingConstants R (Character T)).op ∧
      ∀ χ, (e.hom ≫ fst T.X (affineScheme R)).left.appTop (characterFunction χ) =
        (Scheme.ΓSpecIso (affineRing S)).inv (MonoidAlgebra.of R _ χ) := by
  classical
  obtain ⟨r, ⟨j⟩⟩ := hT
  obtain ⟨d⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  let a := j ≪≫ d.symm
  let Λ := StandardLattice.{u} r
  let C := groupRingAlgebra (CommAlgCat.of k k) Λ
  obtain ⟨e₀, he₀⟩ := characterFunction_of_splitExponent (k := k) r
  let E := e₀.trans (characterPrecomp a)
  let D := specGroup (Specs.DiagonalizableGroups.groupAlgebra k Λ)
  let overIso : T.X ≅ affineScheme C :=
    ⟨a.hom.hom.hom, a.inv.hom.hom,
      congrArg (fun f : T ⟶ T => f.hom.hom) a.hom_inv_id,
      congrArg (fun f : D ⟶ D => f.hom.hom) a.inv_hom_id⟩
  let P := R ⊗ C
  let S := groupRingAlgebra R (Character T)
  let ringEquiv : (R ⊗[k] MonoidAlgebra k Λ) ≃ₐ[k] MonoidAlgebra R (Character T) :=
    ((MonoidAlgebra.scalarTensorEquiv k R (M := Λ)).restrictScalars k).trans
      (MonoidAlgebra.domCongr k R E)
  let z : op S ≅ op P := (CommAlgCat.isoMk ringEquiv).op
  let cp : affineScheme P ≅ affineScheme R ⊗ affineScheme C :=
    Over.isoMk (pullbackSpecIso k R C).symm (by
      change (pullbackSpecIso k R C).inv ≫
        (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) = _
      rw [← pullbackSpecIso_hom_base, Iso.inv_hom_id_assoc]
      rfl)
  have cp_fst : cp.hom ≫ fst (affineScheme R) (affineScheme C) =
      (testSpec k).map (fst (op R) (op C)) :=
    Over.OverMorphism.ext (pullbackSpecIso_inv_fst k R C)
  have cp_snd : cp.hom ≫ snd (affineScheme R) (affineScheme C) =
      (testSpec k).map (snd (op R) (op C)) :=
    Over.OverMorphism.ext (pullbackSpecIso_inv_snd k R C)
  let e := (testSpec k).mapIso z ≪≫ cp ≪≫ (β_ (affineScheme R) (affineScheme C)) ≪≫
    (overIso.symm ⊗ᵢ Iso.refl (affineScheme R))
  refine ⟨e, ?_, ?_⟩
  · have h : e.hom ≫ snd T.X (affineScheme R) =
        (testSpec k).map (z.hom ≫ fst (op R) (op C)) := by
      simp [e]
      rw [cp_fst]
    rw [h]
    congr 1
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change ringEquiv (x ⊗ₜ[k] (1 : MonoidAlgebra k Λ)) = MonoidAlgebra.single 1 x
    simp only [ringEquiv, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
      MonoidAlgebra.scalarTensorEquiv_tmul, map_one]
    change (MonoidAlgebra.domCongr k R E) (x • MonoidAlgebra.single (1 : Λ) 1) = _
    rw [MonoidAlgebra.smul_single', mul_one, MonoidAlgebra.domCongr_single, map_one]
  · intro χ
    obtain ⟨m, rfl⟩ := E.surjective χ
    have h : e.hom ≫ fst T.X (affineScheme R) =
        (testSpec k).map (z.hom ≫ snd (op R) (op C)) ≫ overIso.inv := by
      simp [e]
      rw [reassoc_of% cp_snd]
    rw [h, comp_appTop_apply]
    have hc : overIso.inv.left.appTop (characterFunction (E m)) =
        (Scheme.ΓSpecIso (affineRing C)).inv (MonoidAlgebra.of k _ m) := by
      have hh : E m = a.hom ≫ e₀ m := rfl
      rw [hh, characterFunction_comp]
      change ((overIso.inv ≫ overIso.hom).left.appTop (characterFunction (e₀ m))) = _
      rw [overIso.inv_hom_id]
      exact he₀ m
    rw [hc]
    change (Spec.map (CommRingCat.ofHom (z.hom ≫ snd (op R) (op C)).unop.hom.toRingHom)).appTop
      ((Scheme.ΓSpecIso (affineRing C)).inv (MonoidAlgebra.of k _ m)) = _
    rw [appTop_Spec_map]
    apply congrArg (fun x => (Scheme.ΓSpecIso (affineRing S)).inv x)
    change ringEquiv ((1 : R) ⊗ₜ[k] MonoidAlgebra.single m 1) = MonoidAlgebra.single (E m) 1
    simp [ringEquiv, MonoidAlgebra.scalarTensorEquiv_tmul, MonoidAlgebra.domCongr_single]
    rfl

end ProductCoordinates

section CharacterLaw

open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open scoped TensorProduct CategoryTheory.MonObj

variable {T : GroupScheme k} {Z : SchemeOver k}

private theorem appTop_comp_apply {Y X U : Scheme.{u}} (f : Y ⟶ X) (g : X ⟶ U)
    (r : Γ(U, ⊤)) :
    (f ≫ g).appTop r = f.appTop (g.appTop r) := by
  rw [Scheme.Hom.comp_appTop]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem standardCoordinate_identity :
    let H := specGroup (groupAlgebra k IntegerCharacters)
    η[H.X].left.appTop ((Scheme.ΓSpecIso _).inv
      (MonoidAlgebra.of k _ integerGenerator)) = (1 : Γ(Spec (CommRingCat.of k), ⊤)) := by
  let w := MonoidAlgebra.of k IntegerCharacters integerGenerator
  let h := MonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k) integerGenerator
  change (Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom k _).toRingHom)).appTop
    ((Scheme.ΓSpecIso _).inv w) = _
  rw [appTop_Spec_map]
  change (Scheme.ΓSpecIso (CommRingCat.of k)).inv (Coalgebra.counit (R := k) w) = 1
  have hw : Coalgebra.counit (R := k) w = 1 := h.counit_eq_one
  rw [hw, map_one]

set_option backward.isDefEq.respectTransparency false in
private theorem standardCoordinate_mul :
    let H := specGroup (groupAlgebra k IntegerCharacters)
    let w : Γ(H.X.left, ⊤) := (Scheme.ΓSpecIso _).inv (MonoidAlgebra.of k _ integerGenerator)
    μ[H.X].left.appTop w = (fst H.X H.X).left.appTop w * (snd H.X H.X).left.appTop w := by
  let H := specGroup (groupAlgebra k IntegerCharacters)
  let B := MonoidAlgebra k IntegerCharacters
  let w : B := MonoidAlgebra.of k _ integerGenerator
  let w' : Γ(H.X.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B)).inv w
  let j := pullbackSpecIso k B B
  let d := (MonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k) integerGenerator)
  apply (ConcreteCategory.bijective_of_isIso j.inv.appTop).1
  change j.inv.appTop (μ[H.X].left.appTop w') =
    j.inv.appTop ((fst H.X H.X).left.appTop w' * (snd H.X H.X).left.appTop w')
  rw [map_mul]
  change (j.inv ≫ μ[H.X].left).appTop w' =
    (j.inv ≫ (fst H.X H.X).left).appTop w' * (j.inv ≫ (snd H.X H.X).left).appTop w'
  have hm : j.inv ≫ μ[H.X].left =
      Spec.map (CommRingCat.ofHom ((Bialgebra.comulAlgHom k B).toRingHom)) := by
    change j.inv ≫ j.hom ≫ _ = _
    rw [j.inv_hom_id_assoc]
    rfl
  have hfst : j.inv ≫ (fst H.X H.X).left =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) :=
    pullbackSpecIso_inv_fst k B B
  have hsnd : j.inv ≫ (snd H.X H.X).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k) (A := B) (B := B)).toRingHom) :=
    pullbackSpecIso_inv_snd k B B
  rw [hm, hfst, hsnd]
  let B' := CommRingCat.of B
  let J := CommRingCat.of (B ⊗[k] B)
  let δ : B' ⟶ J := CommRingCat.ofHom (Bialgebra.comulAlgHom k B).toRingHom
  let l : B' ⟶ J := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let r : B' ⟶ J := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := k) (A := B) (B := B)).toRingHom
  have fδ := appTop_Spec_map δ w
  have fl := appTop_Spec_map l w
  have fr := appTop_Spec_map r w
  calc
    _ = (Scheme.ΓSpecIso J).inv (δ w) := fδ
    _ = (Scheme.ΓSpecIso J).inv (l w) * (Scheme.ΓSpecIso J).inv (r w) := by
      rw [← map_mul]
      apply congrArg (fun x => (Scheme.ΓSpecIso J).inv x)
      change Coalgebra.comul (R := k) w = (w ⊗ₜ[k] (1 : B)) * ((1 : B) ⊗ₜ[k] w)
      have hw : Coalgebra.comul (R := k) w = w ⊗ₜ[k] w := d.comul_eq_tmul_self
      rw [hw, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = _ := congrArg₂ (· * ·) fl.symm fr.symm

set_option backward.isDefEq.respectTransparency false in
theorem characterFunction_at_one (χ : Character T) :
    (1 : Z ⟶ T.X).left.appTop (characterFunction χ) = 1 := by
  let H := specGroup (groupAlgebra k IntegerCharacters)
  let f : T.X ⟶ H.X := χ.hom.hom
  change (1 : Z ⟶ T.X).left.appTop (f.left.appTop _) = _
  rw [← comp_appTop_apply, MonObj.one_comp f]
  change ((toUnit Z ≫ η[H.X]).left.appTop _) = _
  rw [comp_appTop_apply, standardCoordinate_identity, map_one]

set_option backward.isDefEq.respectTransparency false in
theorem characterFunction_at_mul (χ : Character T) (s t : Z ⟶ T.X) :
    (s * t).left.appTop (characterFunction χ) =
      s.left.appTop (characterFunction χ) * t.left.appTop (characterFunction χ) := by
  let H := specGroup (groupAlgebra k IntegerCharacters)
  let f : T.X ⟶ H.X := χ.hom.hom
  let w : Γ(H.X.left, ⊤) := (Scheme.ΓSpecIso _).inv (MonoidAlgebra.of k _ integerGenerator)
  change (s * t).left.appTop (f.left.appTop w) =
    s.left.appTop (f.left.appTop w) * t.left.appTop (f.left.appTop w)
  rw [← comp_appTop_apply, MonObj.mul_comp, ← comp_appTop_apply, ← comp_appTop_apply]
  change (lift (s ≫ f) (t ≫ f) ≫ μ[H.X]).left.appTop w = _
  rw [comp_appTop_apply, standardCoordinate_mul, map_mul, ← comp_appTop_apply,
    ← comp_appTop_apply, lift_fst, lift_snd]

end CharacterLaw
section AffineHom

open Scheme.Modules

variable {R : CommRingCat.{u}} {Y : Scheme.{u}} {F : (Spec R).Modules}
    [F.IsQuasicoherent] {H : Y.Modules} (f : Y ⟶ Spec R)

/-- A morphism from the inverse image of an associated sheaf corresponds to
a semilinear map on the original module. The target sheaf may live on any scheme. -/
private def affinePullHomEquiv :
    ((Scheme.Modules.pullback f).obj F ⟶ H) ≃
      ((moduleSpecΓFunctor (R := R)).obj F ⟶
        (moduleSpecΓFunctor (R := R)).obj ((pushforward f).obj H)) :=
  ((pullbackPushforwardAdjunction f).homEquiv F H).trans
    ((Iso.homCongr (asIso F.fromTildeΓ).symm (Iso.refl _)).trans
      ((tilde.adjunction (R := R)).homEquiv _ _))

set_option backward.isDefEq.respectTransparency false in
private theorem affinePullHomEquiv_apply (g : (Scheme.Modules.pullback f).obj F ⟶ H)
    (s : (moduleSpecΓFunctor (R := R)).obj F) :
    affinePullHomEquiv f g s = g.val.app (op ⊤) (pullSection f F s) := by
  let A := pullbackPushforwardAdjunction f
  let B := tilde.adjunction (R := R)
  let G := moduleSpecΓFunctor (R := R)
  let d := A.homEquiv _ _ g
  change B.homEquiv _ _ (F.fromTildeΓ ≫ d) s = _
  have hb : B.homEquiv _ _ (F.fromTildeΓ ≫ d) = G.map d := by
    have hc : B.homEquiv (G.obj F) F (B.counit.app F) = 𝟙 _ := by
      rw [← B.homEquiv_symm_id]
      exact (B.homEquiv _ _).apply_symm_apply _
    change B.homEquiv _ _ (B.counit.app F ≫ d) = _
    rw [Adjunction.homEquiv_naturality_right]
    change (B.homEquiv (G.obj F) F (B.counit.app F)) ≫ G.map d = G.map d
    rw [hc, Category.id_comp]
  rw [hb]
  change (A.homEquiv F H g).val.app (op ⊤) s = _
  rw [Adjunction.homEquiv_unit]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem affinePullHom_ext {g h : (Scheme.Modules.pullback f).obj F ⟶ H}
    (e : ∀ (s : Γ(F, ⊤)),
      g.val.app (op ⊤) (pullSection f F s) =
        h.val.app (op ⊤) (pullSection f F s)) :
    g = h := by
  apply (affinePullHomEquiv f).injective
  ext s
  exact (affinePullHomEquiv_apply f g s).trans ((e s).trans
    (affinePullHomEquiv_apply f h s).symm)

set_option backward.isDefEq.respectTransparency false in
private def affinePullHom (g : Γ(F, ⊤) → Γ(H, ⊤))
    (hadd : ∀ x y, g (x + y) = g x + g y)
    (hsmul : ∀ (r : Γ(Spec R, ⊤)) (x : Γ(F, ⊤)),
      g (r • x) = f.appTop r • g x) : (Scheme.Modules.pullback f).obj F ⟶ H := by
  let M : ModuleCat R := (moduleSpecΓFunctor (R := R)).obj F
  let N : ModuleCat R := (moduleSpecΓFunctor (R := R)).obj ((pushforward f).obj H)
  let h : M →ₗ[R] N :=
    { toFun := fun s => g s
      map_add' := hadd
      map_smul' := by
        intro r s
        change g (((Scheme.ΓSpecIso R).inv r) • (show Γ(F, ⊤) from s)) =
          f.appTop ((Scheme.ΓSpecIso R).inv r) • g s
        exact hsmul ((Scheme.ΓSpecIso R).inv r) s }
  exact (affinePullHomEquiv f).symm (ConcreteCategory.ofHom (C := ModuleCat R) (X := M) (Y := N) h)

set_option backward.isDefEq.respectTransparency false in
private theorem affinePullHom_apply
    (g : Γ(F, ⊤) → Γ(H, ⊤)) (hadd : ∀ x y, g (x + y) = g x + g y)
    (hsmul : ∀ (r : Γ(Spec R, ⊤)) (x : Γ(F, ⊤)), g (r • x) = f.appTop r • g x)
    (s : Γ(F, ⊤)) :
    (affinePullHom f g hadd hsmul).val.app (op ⊤) (pullSection f F s) = g s := by
  rw [← affinePullHomEquiv_apply f]
  unfold affinePullHom
  rw [(affinePullHomEquiv f).apply_symm_apply]
  rfl

end AffineHom
private def pullSectionAdd {P Y : Scheme.{u}} (f : Y ⟶ P) (F : P.Modules) :
    Γ(F, ⊤) →+ Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app ⊤ |> AddCommGrpCat.Hom.hom

section WeightMaps

variable {Λ V W : Type u} [CommGroup Λ] [AddCommGroup V] [Module k V]
    [AddCommGroup W]

/-- Additive maps out of an internal direct sum are determined by their
values on its homogeneous summands. -/
private theorem WeightGrading.addHom_ext (G : WeightGrading k Λ V) {f g : V →+ W}
    (h : ∀ i (v : G.piece i), f v = g v) : f = g := by
  classical
  let j : (⨁ i, G.piece i) →+ V := (DirectSum.coeLinearMap G.piece).toAddMonoidHom
  have H : f.comp j = g.comp j := by
    apply DirectSum.addHom_ext
    intro i v
    have hv : j (DirectSum.of (fun i => ↥(G.piece i)) i v) = v := by
      exact DirectSum.coeLinearMap_lof G.piece i v
    change f (j (DirectSum.of _ i v)) = g (j (DirectSum.of _ i v))
    rw [hv]
    exact h i v
  ext v
  obtain ⟨w, rfl⟩ := G.internal.surjective v
  exact DFunLike.congr_fun H w

variable {T : GroupScheme k} {R : TestAlgebra k} {a : ModObj T.X (affineScheme R)}
  {F H : (affineScheme R).left.Modules}

set_option backward.isDefEq.respectTransparency false in
theorem isLinearizedMap_iff_preserves_weight_of_internal [F.IsQuasicoherent]
    (L : Linearization a F) (K : Linearization a H)
    (G : WeightGrading k (Character T) ((affineSections R).obj F))
    (hG : ∀ χ s, s ∈ G.piece χ ↔ HasSectionWeight L s χ)
    (f : F ⟶ H) :
    IsLinearizedMap L K f ↔ ∀ χ s, HasSectionWeight L s χ →
      HasSectionWeight K (f.app ⊤ s) χ := by
  constructor
  · intro h χ s hs
    exact linearizedMap_preserves_sectionWeight h hs
  · intro h
    let p := snd T.X (affineScheme R)
    let q := a.smul
    let F₁ := L.iso.hom ≫ (Scheme.Modules.pullback q.left).map f
    let F₂ := (Scheme.Modules.pullback p.left).map f ≫ K.iso.hom
    change F₁ = F₂
    apply affinePullHom_ext p.left
    let f₁ := (F₁.app ⊤).hom.comp (pullSectionAdd p.left F)
    let f₂ := (F₂.app ⊤).hom.comp (pullSectionAdd p.left F)
    have hm : f₁ = f₂ := by
      apply WeightGrading.addHom_ext G
      intro χ v
      let s : Γ(F, ⊤) := v.val
      let c := (fst T.X (affineScheme R)).left.appTop (characterFunction χ)
      let A := (Scheme.Modules.pullback q.left).map f
      let B := (Scheme.Modules.pullback p.left).map f
      have h₁ : L.iso.hom.app ⊤ (pullSection p.left F s) =
          c • pullSection q.left F s := (hG χ s).mp v.property
      have h₂ : K.iso.hom.app ⊤ (pullSection p.left H (f.app ⊤ s)) =
          c • pullSection q.left H (f.app ⊤ s) := h χ s ((hG χ s).mp v.property)
      change A.app ⊤ (L.iso.hom.app ⊤ (pullSection p.left F s)) =
        K.iso.hom.app ⊤ (B.app ⊤ (pullSection p.left F s))
      calc
        _ = c • A.app ⊤ (pullSection q.left F s) := by rw [h₁, Scheme.Modules.Hom.app_smul]
        _ = c • pullSection q.left H (f.app ⊤ s) := by
          exact congrArg (c • ·) (pullSection_naturality q.left f s).symm
        _ = K.iso.hom.app ⊤ (pullSection p.left H (f.app ⊤ s)) := h₂.symm
        _ = _ := congrArg (K.iso.hom.app ⊤) (pullSection_naturality p.left f s)
    exact fun s => DFunLike.congr_fun hm s

end WeightMaps

@[reassoc]
theorem multiply_natural {X : SchemeOver k} {F H : X.left.Modules}
    (g : F ⟶ H) (r : Γ(X.left, ⊤)) :
    multiply F r ≫ g = g ≫ multiply H r := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  exact g.app_smul ((X.left.presheaf.map U.leTop.op) r) x

theorem multiply_comp {X : SchemeOver k} (F : X.left.Modules)
    (r s : Γ(X.left, ⊤)) :
    multiply F r ≫ multiply F s = multiply F (s * r) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (X.left.presheaf.map U.leTop.op) s • ((X.left.presheaf.map U.leTop.op) r • x) =
    (X.left.presheaf.map U.leTop.op) (s * r) • x
  rw [smul_smul, map_mul]

theorem multiply_one {X : SchemeOver k} (F : X.left.Modules) :
    multiply F 1 = 𝟙 F := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (X.left.presheaf.map U.leTop.op) (1 : Γ(X.left, ⊤)) • x = x
  rw [map_one, one_smul]

def multiplyUnit {X : SchemeOver k} (F : X.left.Modules)
    (r : Γ(X.left, ⊤)ˣ) : F ≅ F where
  hom := multiply F r
  inv := multiply F ↑r⁻¹
  hom_inv_id := by rw [multiply_comp, Units.inv_mul, multiply_one]
  inv_hom_id := by rw [multiply_comp, Units.mul_inv, multiply_one]

theorem pushforward_multiply {X Y : SchemeOver k} (f : X ⟶ Y)
    (F : X.left.Modules) (r : Γ(Y.left, ⊤)) :
    (Scheme.Modules.pushforward f.left).map (multiply F (f.left.appTop r)) =
      multiply ((Scheme.Modules.pushforward f.left).obj F) r := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  let y : Γ(F, f.left ⁻¹ᵁ U) := x
  change (X.left.presheaf.map (f.left ⁻¹ᵁ U).leTop.op) (f.left.appTop r) • y =
    f.left.app U ((Y.left.presheaf.map U.leTop.op) r) • y
  have h := f.left.naturality U.leTop.op
  exact congrArg (fun s : Γ(X.left, f.left ⁻¹ᵁ U) => s • y)
    (congrArg (fun g : Γ(Y.left, ⊤) ⟶ Γ(X.left, f.left ⁻¹ᵁ U) => g r) h.symm)

theorem pullback_multiply {X Y : SchemeOver k} (f : X ⟶ Y)
    (F : Y.left.Modules) (r : Γ(Y.left, ⊤)) :
    (Scheme.Modules.pullback f.left).map (multiply F r) =
      multiply (Pull f F) (f.left.appTop r) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f.left
  apply (adj.homEquiv F (Pull f F)).injective
  have hl := adj.homEquiv_naturality_left (multiply F r) (𝟙 (Pull f F))
  have hr := adj.homEquiv_naturality_right (𝟙 (Pull f F))
    (multiply (Pull f F) (f.left.appTop r))
  rw [Category.comp_id] at hl
  rw [Category.id_comp, pushforward_multiply] at hr
  rw [hl, hr]
  exact multiply_natural _ r

section Twist

variable {T : GroupScheme k} {X Z : SchemeOver k} {a : ModObj T.X X}

private def characterUnit (χ : Character T) : Γ(T.X.left, ⊤)ˣ :=
  (isUnit_characterFunction χ).unit

private theorem characterUnit_val (χ : Character T) :
    (characterUnit χ : Γ(T.X.left, ⊤)) = characterFunction χ :=
  (isUnit_characterFunction χ).unit_spec

private def twistLinearizationIso {F : X.left.Modules}
    (χ : Character T) (θ : Pull (snd T.X X) F ≅ Pull a.smul F) :
    Pull (snd T.X X) F ≅ Pull a.smul F :=
  θ ≪≫ multiplyUnit _ (Units.map (fst T.X X).left.appTop.hom (characterUnit χ))

set_option backward.isDefEq.respectTransparency false in
private theorem twistLinearizationIso_hom {F : X.left.Modules}
    (χ : Character T) (θ : Pull (snd T.X X) F ≅ Pull a.smul F) :
    (twistLinearizationIso (a := a) χ θ).hom =
      θ.hom ≫ multiply _ ((fst T.X X).left.appTop (characterFunction χ)) := by
  change θ.hom ≫ multiply _ ((fst T.X X).left.appTop (characterUnit χ)) = _
  rw [characterUnit_val]

set_option backward.isDefEq.respectTransparency false in
private theorem transport_twist_hom {F : X.left.Modules}
    (χ : Character T) (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Z ⟶ T.X) (y : Z ⟶ X) :
    (transport a (twistLinearizationIso (a := a) χ θ) t y).hom =
      (transport a θ t y).hom ≫ multiply _ (t.left.appTop (characterFunction χ)) := by
  let j := lift t y
  let p := snd T.X X
  let q := a.smul
  let c := (fst T.X X).left.appTop (characterFunction χ)
  let d := t.left.appTop (characterFunction χ)
  let l := (comparePull F j p (lift_snd t y)).inv
  let r := (comparePull F j q (rfl : j ≫ q = actOn a t y)).hom
  let P := Scheme.Modules.pullback j.left
  rw [transport_eq_evalPullIso, transport_eq_evalPullIso]
  change l ≫ P.map (twistLinearizationIso (a := a) χ θ).hom ≫ r =
    (l ≫ P.map θ.hom ≫ r) ≫ multiply _ d
  rw [twistLinearizationIso_hom, P.map_comp, Category.assoc, Category.assoc, Category.assoc]
  change l ≫ P.map θ.hom ≫ P.map (multiply _ c) ≫ r =
    l ≫ P.map θ.hom ≫ r ≫ multiply _ d
  have hc : j.left.appTop c = d := by
    change j.left.appTop ((fst T.X X).left.appTop (characterFunction χ)) = _
    rw [← comp_appTop_apply, lift_fst]
  rw [pullback_multiply, hc, multiply_natural]

set_option backward.isDefEq.respectTransparency false in
private theorem twistUnitLaw {F : X.left.Modules} (L : Linearization a F) (χ : Character T)
    (y : Z ⟶ X) :
    ∃ h : actOn a (1 : Z ⟶ T.X) y = y,
      (transport a (twistLinearizationIso (a := a) χ L.iso) 1 y).hom ≫
        (pullCongr F h).hom = 𝟙 _ := by
  obtain ⟨h, hL⟩ := L.unit Z y
  refine ⟨h, ?_⟩
  rw [transport_twist_hom, characterFunction_at_one, multiply_one, Category.comp_id, hL]

private theorem composition_mul_scalar {Y : SchemeOver k}
    {F₀ F₁ F₂ F₃ : Y.left.Modules} (b₀ : F₀ ⟶ F₁) (b₁ : F₁ ⟶ F₂)
    (b₂ : F₂ ⟶ F₃) (b₃ : F₀ ⟶ F₃) (h : b₀ ≫ b₁ ≫ b₂ = b₃)
    (c d : Γ(Y.left, ⊤)) :
    (b₀ ≫ multiply F₁ d) ≫ (b₁ ≫ multiply F₂ c) ≫ b₂ =
      b₃ ≫ multiply F₃ (c * d) := by
  simp only [Category.assoc]
  rw [multiply_natural_assoc b₁ d, ← Category.assoc (multiply F₂ d), multiply_comp,
    multiply_natural, ← reassoc_of% h]

set_option backward.isDefEq.respectTransparency false in
private theorem twistMulLaw {F : X.left.Modules} (L : Linearization a F) (χ : Character T)
    (s t : Z ⟶ T.X) (y : Z ⟶ X) :
    ∃ h : actOn a s (actOn a t y) = actOn a (s * t) y,
      (transport a (twistLinearizationIso (a := a) χ L.iso) t y).hom ≫
        (transport a (twistLinearizationIso (a := a) χ L.iso) s (actOn a t y)).hom ≫
        (pullCongr F h).hom = (transport a (twistLinearizationIso (a := a) χ L.iso) (s * t) y).hom := by
  obtain ⟨h, hL⟩ := L.mul Z s t y
  refine ⟨h, ?_⟩
  unfold TransportComposition ComposesTo at hL
  rw [transport_twist_hom, transport_twist_hom, transport_twist_hom, characterFunction_at_mul]
  exact composition_mul_scalar _ _ _ _ hL _ _

/-- Twisting a linearization multiplies its transport by the given character. -/
def twistLinearization {F : X.left.Modules}
    (L : Linearization a F) (χ : Character T) : Linearization a F where
  iso := twistLinearizationIso χ L.iso
  unit _ := twistUnitLaw L χ
  mul _ := twistMulLaw L χ

def twistCoherent (F : EquivariantCoherent a) (χ : Character T) : EquivariantCoherent a :=
  ⟨F.sheaf, F.coherent, twistLinearization F.lin χ⟩

theorem twistCoherent_isTwist (F : EquivariantCoherent a) (χ : Character T) :
    IsTwist χ F (twistCoherent F χ) := by
  refine ⟨Iso.refl _, ?_⟩
  change (twistLinearizationIso (a := a) χ F.lin.iso).hom =
    (Scheme.Modules.pullback (snd T.X X).left).map (𝟙 _) ≫ F.lin.iso.hom ≫
      multiply _ ((fst T.X X).left.appTop (characterFunction χ)) ≫
      (Scheme.Modules.pullback a.smul.left).map (𝟙 _)
  rw [twistLinearizationIso_hom,
    (Scheme.Modules.pullback (snd T.X X).left).map_id F.sheaf,
    (Scheme.Modules.pullback a.smul.left).map_id F.sheaf,
    Category.id_comp, Category.comp_id]

end Twist

section Classes

variable {T : GroupScheme k} {X Y Z : SchemeOver k} {a : ModObj T.X X}

/-- Short exact sequences give the additive relation on coherent classes. -/
theorem classOf_exact {F H K : EquivariantCoherent a}
    {f : F.sheaf ⟶ H.sheaf} {g : H.sheaf ⟶ K.sheaf} (w : f ≫ g = 0)
    (hf : EquivariantHom f) (hg : EquivariantHom g)
    (hex : (ShortComplex.mk f g w).ShortExact) :
    classOf H = classOf F + classOf K := by
  have hm : Finsupp.single H 1 - Finsupp.single F 1 - Finsupp.single K 1 ∈
      relationSubmodule a :=
    Submodule.subset_span (Or.inl ⟨F, H, K, f, g, w, hf, hg, hex, rfl⟩)
  have h := LinearMap.mem_ker.mp (show _ ∈ LinearMap.ker (relationSubmodule a).mkQ by
    rw [Submodule.ker_mkQ]
    exact hm)
  simpa only [map_sub, map_add, classOf, sub_sub, sub_eq_zero] using h

/-- An equivariant sheaf whose underlying module is zero represents the zero class. -/
theorem classOf_isZero (F : EquivariantCoherent a) (hF : IsZero F.sheaf) :
    classOf F = 0 := by
  have hId : EquivariantHom (F := F) (H := F) (𝟙 F.sheaf) := by
    unfold EquivariantHom
    rw [(Scheme.Modules.pullback a.smul.left).map_id F.sheaf,
      (Scheme.Modules.pullback (snd T.X X).left).map_id F.sheaf,
      Category.comp_id, Category.id_comp]
  let S := ShortComplex.mk (𝟙 F.sheaf) (𝟙 F.sheaf) (hF.eq_of_src _ _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_isZero_X₂ hF)
      (inferInstanceAs (Mono (𝟙 F.sheaf))) (inferInstanceAs (Epi (𝟙 F.sheaf)))
  have h := classOf_exact S.zero hId hId hS
  exact add_left_cancel (show classOf F + classOf F = classOf F + 0 by rw [← h, add_zero])

variable {M : Type v} [AddCommGroup M] [Module (CharacterRing T) M]

/-- A rule on coherent sheaves respecting the two kinds of relations descends
to a character-ring linear map on the presented Grothendieck group. -/
def liftClassMap (value : EquivariantCoherent a → M)
    (exactRelation : ∀ {F H K : EquivariantCoherent a}
      (f : F.sheaf ⟶ H.sheaf) (g : H.sheaf ⟶ K.sheaf) (w : f ≫ g = 0),
      EquivariantHom f → EquivariantHom g → (ShortComplex.mk f g w).ShortExact →
      value H = value F + value K)
    (twistRelation : ∀ {χ : Character T} {F H : EquivariantCoherent a},
      IsTwist χ F H → value H = eChar χ • value F) :
    GZero a →ₗ[CharacterRing T] M :=
  (relationSubmodule a).liftQ (Finsupp.linearCombination _ value) (by
    apply Submodule.span_le.mpr
    intro r hr
    apply LinearMap.mem_ker.mpr
    rcases hr with ⟨F, H, K, f, g, w, hf, hg, hex, rfl⟩ | ⟨χ, F, H, h, rfl⟩
    · simp only [map_sub, sub_sub, map_add, Finsupp.linearCombination_single, one_smul, sub_sub, sub_eq_zero]
      exact exactRelation f g w hf hg hex
    · simp only [map_sub, map_smul, Finsupp.linearCombination_single, one_smul, sub_eq_zero]
      exact twistRelation h)

@[simp]
theorem liftClassMap_classOf (value : EquivariantCoherent a → M) (hex htw)
    (F : EquivariantCoherent a) : liftClassMap value hex htw (classOf F) = value F := by
  simp [liftClassMap, classOf]

/-- A linear map out of the class group is determined by the sheaf classes. -/
theorem classMap_ext {L L' : GZero a →ₗ[CharacterRing T] M}
    (h : ∀ F, L (classOf F) = L' (classOf F)) : L = L' := by
  apply LinearMap.ext
  intro c
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective (relationSubmodule a) c
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | single F r =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul]
    exact congrArg (r • ·) (h F)

end Classes
section ProjectionSections

private def moduleSectionsIso {Y : Scheme.{u}} {F G : Y.Modules} (e : F ≅ G) :
    Γ(F, ⊤) ≃+ Γ(G, ⊤) :=
  AddEquiv.ofBijective (e.hom.app ⊤).hom (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤))

set_option backward.isDefEq.respectTransparency false in
private theorem pullSection_bijective_of_isIso {P Y : Scheme.{u}} (f : Y ⟶ P) [IsIso f]
    (F : P.Modules) : Function.Bijective (pullSection f F) := by
  let L := Scheme.Modules.pullback f
  let L' := Scheme.Modules.pullback (inv f)
  let c₁ : L ⋙ L' ≅ 𝟭 _ := Scheme.Modules.pullbackComp (inv f) f ≪≫
    Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f) ≪≫ Scheme.Modules.pullbackId P
  let c₂ : L' ⋙ L ≅ 𝟭 _ := Scheme.Modules.pullbackComp f (inv f) ≪≫
    Scheme.Modules.pullbackCongr (IsIso.hom_inv_id f) ≪≫ Scheme.Modules.pullbackId Y
  let e := CategoryTheory.Equivalence.mk L L' c₁.symm c₂
  let : L.IsEquivalence := e.isEquivalence_functor
  let adj : L ⊣ _ := Scheme.Modules.pullbackPushforwardAdjunction f
  have : IsIso adj.unit := inferInstance
  let g := (adj.unit.app F).app ⊤
  exact ConcreteCategory.bijective_of_isIso g

set_option backward.isDefEq.respectTransparency false in
private theorem extendGroupRingFinsupp {R Λ : Type u} [CommRing R] [CommGroup Λ]
    (M : ModuleCat.{u} R) :
    let S := MonoidAlgebra R Λ
    let φ : R →+* S := algebraMap R S
    let N := (ModuleCat.extendScalars.{u,u,u} φ).obj M
    ∃ e : N ≃+ (Λ →₀ M),
      ∀ χ s, e ((MonoidAlgebra.of R Λ χ) • (show N from
        (ModuleCat.extendRestrictScalarsAdj φ).unit.app M s)) = Finsupp.single χ s := by
  classical
  intro S φ N
  let : Module R S := Module.compHom S φ
  let b : Module.Basis Λ R S := Module.Basis.ofRepr
    { (MonoidAlgebra.coeffAddEquiv : MonoidAlgebra R Λ ≃+ (Λ →₀ R)) with
      map_smul' := by
        intro r x
        ext i
        change (MonoidAlgebra.single 1 r * x : MonoidAlgebra R Λ).coeff i =
          r * x.coeff i
        rw [MonoidAlgebra.coeff_single_one_mul] }
  have hb (χ : Λ) : b.repr (MonoidAlgebra.of R Λ χ) = Finsupp.single χ 1 := by
    ext i
    change (MonoidAlgebra.single χ (1 : R)).coeff i = _
    rw [MonoidAlgebra.coeff_single]
  let e := (TensorProduct.equivFinsuppOfBasisLeft (N := M) b).toAddEquiv
  refine ⟨e, ?_⟩
  intro χ s
  let c := MonoidAlgebra.of R Λ χ
  let v : N := (ModuleCat.extendRestrictScalarsAdj φ).unit.app M s
  change e (c • v) = _
  have h : (c • v : N) = (c ⊗ₜ[R] s : S ⊗[R] M) := by
    change ((c * 1) ⊗ₜ[R] s : S ⊗[R] M) = _
    rw [mul_one]
  rw [h]
  change (TensorProduct.equivFinsuppOfBasisLeft (N := M) b) (c ⊗ₜ[R] s) = _
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, hb]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem comparePull_section_smul {X Y Z : SchemeOver k} (F : X.left.Modules)
    (f : Z ⟶ Y) (g : Y ⟶ X) {h : Z ⟶ X} (e : f ≫ g = h)
    (r : Γ(Y.left, ⊤)) (s : Γ(F, ⊤)) :
    (comparePull F f g e).hom.app ⊤
      (pullSection f.left (Pull g F) (r • pullSection g.left F s)) =
      f.left.appTop r • pullSection h.left F s := by
  rw [pullSection_smul, Scheme.Modules.Hom.app_smul, comparePull_section F f g e s]

set_option maxHeartbeats 380000 in
set_option backward.isDefEq.respectTransparency false in
private theorem affineProjectionExpansion {Λ : Type u} [CommGroup Λ]
    (R : TestAlgebra k) {Y : SchemeOver k} (p : Y ⟶ affineScheme R)
    (F : (affineScheme R).left.Modules) [F.IsQuasicoherent]
    (j : affineScheme (groupRingAlgebra R Λ) ≅ Y)
    (hp : j.hom ≫ p = (testSpec k).map (groupRingConstants R Λ).op)
    (c : Λ → Γ(Y.left, ⊤))
    (hc : ∀ χ, j.hom.left.appTop (c χ) =
      (Scheme.ΓSpecIso (affineRing (groupRingAlgebra R Λ))).inv (MonoidAlgebra.of R _ χ)) :
    ∃ E : Γ(Pull p F, ⊤) ≃+ (Λ →₀ Γ(F, ⊤)), ∀ χ s,
      E (c χ • pullSection p.left F s) = Finsupp.single χ s := by
  let S := groupRingAlgebra R Λ
  let φ : affineRing R ⟶ affineRing S := CommRingCat.ofHom (algebraMap R (MonoidAlgebra R Λ))
  let φ₁ := (testSpec k).map (groupRingConstants R Λ).op
  let j' : (affineScheme S).left ⟶ Y.left := j.hom.left
  have : IsIso j' := inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of k))).map j.hom))
  let P := Pull p F
  let C := comparePull F j.hom p (show j.hom ≫ p = φ₁ from hp)
  let M := (affineSections R).obj F
  obtain ⟨e, he⟩ := affineSectionBaseChange φ F
  obtain ⟨d, hd⟩ := extendGroupRingFinsupp (Λ := Λ) M
  let a := AddEquiv.ofBijective (pullSectionAdd j' P) (pullSection_bijective_of_isIso j' P)
  let b := moduleSectionsIso C
  let e' := AddEquiv.ofBijective e.hom.hom.toAddMonoidHom
    (ConcreteCategory.bijective_of_isIso e.hom)
  let E := (a.trans b).trans (e'.trans d)
  refine ⟨E, ?_⟩
  intro χ s
  let M' := (affineSections S).obj (Pull φ₁ F)
  let N := (ModuleCat.extendScalars.{u,u,u} φ.hom).obj M
  let J : M' ≅ N := e
  let s' : M' := pullSection φ₁.left F s
  let r' := MonoidAlgebra.of R _ χ
  let v : N := (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M s
  have hsem : J.hom (r' • s') = r' • v := by
    rw [J.hom.hom.map_smul]
    exact congrArg (fun w : N => r' • w) (he s)
  let x : M' := C.hom.app ⊤ (pullSection j' P (c χ • pullSection p.left F s))
  have h : x = j'.appTop (c χ) • pullSection φ₁.left F s :=
    comparePull_section_smul F j.hom p hp (c χ) s
  have harg : x = r' • s' := by
    have h₀ : j'.appTop (c χ) = (Scheme.ΓSpecIso (affineRing S)).inv r' := hc χ
    exact h.trans (congrArg (fun q : Γ((affineScheme S).left, ⊤) => q • pullSection φ₁.left F s) h₀)
  change d (J.hom x) = Finsupp.single χ s
  rw [harg, hsem]
  exact hd χ s

set_option backward.isDefEq.respectTransparency false in
private theorem projectionSectionExpansion {T : GroupScheme k} (hT : IsSplitTorus T)
    (R : TestAlgebra k) (F : (affineScheme R).left.Modules) [F.IsQuasicoherent] :
    let X := affineScheme R
    let p := snd T.X X
    ∃ E : Γ(Pull p F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤)),
      ∀ χ s,
        E ((fst T.X X).left.appTop (characterFunction χ) • pullSection p.left F s) =
          Finsupp.single χ s := by
  intro X p
  obtain ⟨j, hj, hχ⟩ := torusProductChart T hT R
  let c := fun χ => (fst T.X X).left.appTop (characterFunction χ)
  refine affineProjectionExpansion R p F j hj c (fun χ => ?_)
  exact (comp_appTop_apply j.hom (fst T.X X) _).symm.trans (hχ χ)

end ProjectionSections

section AffineWeightSpaces

variable {T : GroupScheme k} {R : TestAlgebra k} {a : ModObj T.X (affineScheme R)}

private abbrev topFunction (R : TestAlgebra k) (r : R) : Γ((affineScheme R).left, ⊤) :=
  (Scheme.ΓSpecIso (affineRing R)).inv r

set_option backward.isDefEq.respectTransparency false in
private theorem baseScalar_functionWeight (hT : IsSplitTorus T) (c : k) :
    HasFunctionWeight a (topFunction R (algebraMap k R c)) 1 := by
  let X := affineScheme R
  let p := snd T.X X
  let w := (Scheme.ΓSpecIso (CommRingCat.of k)).inv c
  have hΓ : X.hom.appTop w = topFunction R (algebraMap k R c) :=
    appTop_Spec_map (CommRingCat.ofHom (algebraMap k R)) c
  rw [← hΓ]
  change a.smul.left.appTop (X.hom.appTop w) =
    (fst T.X X).left.appTop (characterFunction ((1 : Character T)⁻¹)) *
      p.left.appTop (X.hom.appTop w)
  rw [inv_one, characterFunction_one hT, map_one, one_mul]
  exact (appTop_comp_apply a.smul.left X.hom w).symm.trans
    ((congrArg (fun v : (T.X ⊗ X).left ⟶ Spec (CommRingCat.of k) => v.appTop w)
      ((Over.w a.smul).trans (Over.w p).symm)).trans (appTop_comp_apply p.left X.hom w))

set_option backward.isDefEq.respectTransparency false in
/-- The homogeneous submodule of the affine coordinate algebra for a character. -/
def functionWeightSpace (hT : IsSplitTorus T) (χ : Character T) : Submodule k R where
  carrier := {r | HasFunctionWeight a (topFunction R r) χ}
  zero_mem' := by
    change HasFunctionWeight a (topFunction R 0) χ
    rw [show topFunction R 0 = 0 from map_zero _]
    unfold HasFunctionWeight
    rw [map_zero, map_zero, mul_zero]
  add_mem' := by
    intro r s hr hs
    change HasFunctionWeight a (topFunction R (r + s)) χ
    rw [show topFunction R (r + s) = topFunction R r + topFunction R s from map_add _ _ _]
    change a.smul.left.appTop (topFunction R r) = _ at hr
    change a.smul.left.appTop (topFunction R s) = _ at hs
    unfold HasFunctionWeight
    rw [map_add, map_add, hr, hs, mul_add]
  smul_mem' := by
    intro c r hr
    have H := functionWeight_mul hT (baseScalar_functionWeight (a := a) hT c) hr
    rw [one_mul] at H
    change HasFunctionWeight a (topFunction R (c • r)) χ
    rw [Algebra.smul_def,
      show topFunction R ((algebraMap k R c) * r) =
        topFunction R (algebraMap k R c) * topFunction R r from map_mul _ _ _]
    exact H

set_option backward.isDefEq.respectTransparency false in
/-- The weight submodule of the section module of a linearized sheaf. -/
def sectionWeightSpace (hT : IsSplitTorus T) {F : (affineScheme R).left.Modules}
    (L : Linearization a F) (χ : Character T) :
    Submodule k ((affineSections R).obj F) where
  carrier := {s | HasSectionWeight L s χ}
  zero_mem' := by
    change L.iso.hom.app ⊤ (pullSectionAdd (snd T.X (affineScheme R)).left F 0) =
      _ • pullSectionAdd a.smul.left F 0
    simp only [map_zero, smul_zero]
  add_mem' := by
    intro s t hs ht
    let p := pullSectionAdd (snd T.X (affineScheme R)).left F
    let q := pullSectionAdd a.smul.left F
    let c := (fst T.X (affineScheme R)).left.appTop (characterFunction χ)
    let l := L.iso.hom.app ⊤
    let s' : Γ(F, ⊤) := s
    let t' : Γ(F, ⊤) := t
    change l (p (s' + t')) = c • q (s' + t')
    have h₀ : l (p s') = c • q s' := hs
    have h₁ : l (p t') = c • q t' := ht
    rw [map_add, map_add, map_add, h₀, h₁, smul_add]
  smul_mem' := by
    intro c s hs
    change HasSectionWeight L ((topFunction R (algebraMap k R c)) • (show Γ(F, ⊤) from s)) χ
    simpa only [one_mul] using
      sectionWeight_smul hT L (baseScalar_functionWeight (a := a) hT c) hs

attribute [local instance] Classical.decEq

set_option backward.isDefEq.respectTransparency false in
/-- An internal direct sum of coordinate weights is the coordinate ring grading. -/
def affineGradingOfWeights (hT : IsSplitTorus T)
    (h : DirectSum.IsInternal (functionWeightSpace (a := a) hT)) : AffineGrading R a := by
  refine ⟨⟨⟨functionWeightSpace hT, h⟩, ?_, ?_⟩, ?_⟩
  · change HasFunctionWeight a (topFunction R 1) 1
    rw [show topFunction R 1 = 1 from map_one _]
    exact functionWeight_one hT
  · intro i j r s hr hs
    change HasFunctionWeight a (topFunction R (r * s)) (i * j)
    rw [show topFunction R (r * s) = topFunction R r * topFunction R s from map_mul _ _ _]
    exact functionWeight_mul hT hr hs
  · intro χ r
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- An internal direct sum of section weights is the compatible module grading. -/
def moduleGradingOfWeights (hT : IsSplitTorus T)
    {F : (affineScheme R).left.Modules} (L : Linearization a F) (G : AffineGrading R a)
    (h : DirectSum.IsInternal (sectionWeightSpace hT L)) :
    ModuleGrading G.val ((affineSections R).obj F) := by
  refine ⟨⟨sectionWeightSpace hT L, h⟩, ?_⟩
  intro i j r s hr hs
  change HasSectionWeight L (topFunction R r • (show Γ(F, ⊤) from s)) (i * j)
  exact sectionWeight_smul hT L ((G.property i r).mp hr) hs

end AffineWeightSpaces

section TwistWeights

variable {T : GroupScheme k} {X : SchemeOver k} {a : ModObj T.X X}

set_option backward.isDefEq.respectTransparency false in
theorem sectionWeight_isTwist (hT : IsSplitTorus T)
    {F H : EquivariantCoherent a} {δ : Character T} (h : IsTwist δ F H) :
    ∃ e : F.sheaf ≅ H.sheaf, ∀ (χ : Character T) (s : Γ(F.sheaf, ⊤)),
      HasSectionWeight H.lin (e.hom.app ⊤ s) (δ * χ) ↔ HasSectionWeight F.lin s χ := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun χ s => ?_⟩
  let p := snd T.X X
  let q := a.smul
  let A := (Scheme.Modules.pullback q.left).mapIso e
  let B := (Scheme.Modules.pullback p.left).mapIso e
  let d := (fst T.X X).left.appTop (characterFunction δ)
  let c := (fst T.X X).left.appTop (characterFunction χ)
  let r := (fst T.X X).left.appTop (characterFunction (δ * χ))
  have hr : r = d * c := by
    change (fst T.X X).left.appTop (characterFunction (δ * χ)) = _
    rw [characterFunction_mul hT, map_mul]
  let u := pullSection p.left F.sheaf s
  let v := pullSection q.left F.sheaf s
  let m := F.lin.iso.hom.app ⊤ u
  change H.lin.iso.hom.app ⊤ (pullSection p.left H.sheaf (e.hom.app ⊤ s)) =
    r • pullSection q.left H.sheaf (e.hom.app ⊤ s) ↔ m = c • v
  have hP : pullSection p.left H.sheaf (e.hom.app ⊤ s) = B.hom.app ⊤ u :=
    pullSection_naturality p.left e.hom s
  have hQ : pullSection q.left H.sheaf (e.hom.app ⊤ s) = A.hom.app ⊤ v :=
    pullSection_naturality q.left e.hom s
  rw [hP, hQ, he]
  change A.hom.app ⊤ ((multiply (Pull q F.sheaf) d).app ⊤
    (F.lin.iso.hom.app ⊤ (B.inv.app ⊤ (B.hom.app ⊤ u)))) =
      r • A.hom.app ⊤ v ↔ m = c • v
  rw [hom_apply_inv_apply, ← Scheme.Modules.Hom.app_smul A.hom, hr, mul_smul]
  have hm : (multiply (Pull q F.sheaf) d).app ⊤ m = d • m := multiply_app_top _ d m
  change A.hom.app ⊤ ((multiply (Pull q F.sheaf) d).app ⊤ m) =
    A.hom.app ⊤ (d • c • v) ↔ m = c • v
  rw [hm, (ConcreteCategory.bijective_of_isIso (A.hom.app ⊤)).1.eq_iff]
  obtain ⟨z, hz⟩ := (isUnit_characterFunction δ).map (fst T.X X).left.appTop.hom
  have hd : (z : Γ((T.X ⊗ X).left, ⊤)) = d := hz
  rw [← hd]
  exact (MulAction.injective (β := Γ(Pull q F.sheaf, ⊤)) z).eq_iff

end TwistWeights

section TrivialLinearization

variable {T : GroupScheme k} {X Y Z : SchemeOver k}

set_option backward.isDefEq.respectTransparency false in
private theorem evalPullIso_refl_hom {F : X.left.Modules}
    (l : Z ⟶ Y) (p : Y ⟶ X) {x : Z ⟶ X} (h : l ≫ p = x) :
    (evalPullIso (Iso.refl (Pull p F)) l h rfl).hom = (pullCongr F h.symm).hom := by
  subst x
  simp only [evalPullIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.refl_hom,
    (Scheme.Modules.pullback l.left).map_id, Category.id_comp,
    Iso.inv_hom_id, pullCongr_refl]

private theorem trivial_actOn_eq {t : Z ⟶ T.X} {x : Z ⟶ X} :
    actOn (ModObj.trivialAction T.X X) t x = x := lift_snd _ _

set_option backward.isDefEq.respectTransparency false in
private theorem trivial_transport_hom (F : X.left.Modules) (t : Z ⟶ T.X) (x : Z ⟶ X) :
    (transport (ModObj.trivialAction T.X X) (Iso.refl (Pull (snd T.X X) F)) t x).hom =
      (pullCongr F (trivial_actOn_eq (t := t) (x := x)).symm).hom := by
  rw [transport_eq_evalPullIso]
  exact evalPullIso_refl_hom (lift t x) (snd T.X X) (lift_snd _ _)

private theorem trivial_transport_unit (F : X.left.Modules) (x : Z ⟶ X) :
    ∃ h : actOn (ModObj.trivialAction T.X X) (1 : Z ⟶ T.X) x = x,
      (transport (ModObj.trivialAction T.X X) (Iso.refl (Pull (snd T.X X) F)) 1 x).hom ≫
        (pullCongr F h).hom = 𝟙 _ := by
  refine ⟨trivial_actOn_eq, ?_⟩
  rw [trivial_transport_hom, pullCongr_trans, pullCongr_refl]

@[reassoc]
private theorem pullCongr_eq (F : X.left.Modules) {x y x' y' : Z ⟶ X}
    (h : x = y) (g : y = x') (w : x' = y') (v : x = y') :
    (pullCongr F h).hom ≫ (pullCongr F g).hom ≫ (pullCongr F w).hom = (pullCongr F v).hom := by
  rw [pullCongr_trans, pullCongr_trans]

set_option backward.isDefEq.respectTransparency false in
private theorem trivial_transport_comp (F : X.left.Modules) (s t r : Z ⟶ T.X) (x : Z ⟶ X)
    (h : actOn (ModObj.trivialAction T.X X) s (actOn (ModObj.trivialAction T.X X) t x) =
        actOn (ModObj.trivialAction T.X X) r x) :
      (transport (ModObj.trivialAction T.X X) (Iso.refl (Pull (snd T.X X) F)) t x).hom ≫
        (transport (ModObj.trivialAction T.X X) (Iso.refl (Pull (snd T.X X) F)) s
          (actOn (ModObj.trivialAction T.X X) t x)).hom ≫ (pullCongr F h).hom =
        (transport (ModObj.trivialAction T.X X) (Iso.refl (Pull (snd T.X X) F)) r x).hom := by
  rw [trivial_transport_hom F t x, trivial_transport_hom F s, trivial_transport_hom F r x]
  exact pullCongr_eq F _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem trivial_transport_mul (F : X.left.Modules) (s t : Z ⟶ T.X) (x : Z ⟶ X) :
    ∃ h : actOn (ModObj.trivialAction T.X X) s (actOn (ModObj.trivialAction T.X X) t x) =
        actOn (ModObj.trivialAction T.X X) (s * t) x,
      (transport (ModObj.trivialAction T.X X) (Iso.refl (Pull (snd T.X X) F)) t x).hom ≫
        (transport (ModObj.trivialAction T.X X) (Iso.refl (Pull (snd T.X X) F)) s
          (actOn (ModObj.trivialAction T.X X) t x)).hom ≫ (pullCongr F h).hom =
        (transport (ModObj.trivialAction T.X X) (Iso.refl (Pull (snd T.X X) F)) (s * t) x).hom := by
  let a := ModObj.trivialAction T.X X
  have ht : actOn a t x = x := trivial_actOn_eq
  have hs : actOn a s (actOn a t x) = actOn a t x := trivial_actOn_eq
  have hm : actOn a (s * t) x = x := trivial_actOn_eq
  exact ⟨hs.trans (ht.trans hm.symm), trivial_transport_comp F s t (s * t) x _⟩

/-- A module sheaf on a scheme with the trivial action has the trivial linearization. -/
def trivialLinearization (T : GroupScheme k) (F : X.left.Modules) :
    Linearization (ModObj.trivialAction T.X X) F where
  iso := Iso.refl _
  unit _ := trivial_transport_unit F
  mul _ := trivial_transport_mul F

set_option backward.isDefEq.respectTransparency false in
/-- The structure line on the rational point with its trivial action. -/
def trivialPointLine (T : GroupScheme k) : EquivariantCoherent (pointAction T) where
  sheaf := tilde (ModuleCat.of k k)
  coherent := by
    change (tilde (R := CommRingCat.of k) (ModuleCat.of k k)).IsFinitePresentation
    exact finitePresentation_tilde (R := CommRingCat.of k) (ModuleCat.of k k)
  lin := trivialLinearization T _

end TrivialLinearization

section PointCharacters

variable {T : GroupScheme k}

private abbrev pointRing (k : Type u) [Field k] : TestAlgebra k := CommAlgCat.of k k

private abbrev PointWeights (F : EquivariantCoherent (pointAction T)) :=
  WeightGrading k (Character T) ((affineSections (pointRing k)).obj F.sheaf)

private theorem finite_sections_at_point (F : EquivariantCoherent (pointAction T)) :
    Module.Finite k ((affineSections (pointRing k)).obj F.sheaf) := by
  let R := affineRing (pointRing k)
  let H : (Spec R).Modules := F.sheaf
  let : H.IsFinitePresentation := F.coherent
  exact finitePresentationSections R H

/-- The character of a coherent linearized sheaf over the ground-field
point from its section weights. -/
def pointSheafCharacter (F : EquivariantCoherent (pointAction T)) (H : PointWeights F) :
    CharacterRing T :=
  letI := finite_sections_at_point F
  gradedCharacter H

theorem pointSheafCharacter_coeff (F : EquivariantCoherent (pointAction T)) (H : PointWeights F)
    (χ : Character T) :
    (pointSheafCharacter F H).coeff χ = (Module.finrank k (H.piece χ) : ℤ) := by
  let := finite_sections_at_point F
  exact gradedCharacter_coeff H χ

set_option backward.isDefEq.respectTransparency false in
theorem pointSheafCharacter_exact {F H K : EquivariantCoherent (pointAction T)}
    (G₀ : PointWeights F) (G₁ : PointWeights H) (G₂ : PointWeights K)
    (h₀ : ∀ χ s, s ∈ G₀.piece χ ↔ HasSectionWeight F.lin s χ)
    (h₁ : ∀ χ s, s ∈ G₁.piece χ ↔ HasSectionWeight H.lin s χ)
    (h₂ : ∀ χ s, s ∈ G₂.piece χ ↔ HasSectionWeight K.lin s χ)
    {f : F.sheaf ⟶ H.sheaf} {g : H.sheaf ⟶ K.sheaf} (w : f ≫ g = 0)
    (hf : EquivariantHom f) (hg : EquivariantHom g)
    (hex : (ShortComplex.mk f g w).ShortExact) :
    pointSheafCharacter H G₁ = pointSheafCharacter F G₀ + pointSheafCharacter K G₂ := by
  let := finite_sections_at_point F
  let := finite_sections_at_point H
  let := finite_sections_at_point K
  let := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let := K.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let S := affineSections (pointRing k)
  let f' := (S.map f).hom
  let g' := (S.map g).hom
  have hf' : PreservesWeight G₀ G₁ f' := by
    intro χ s hs
    apply (h₁ χ _).mpr
    exact linearizedMap_preserves_sectionWeight (show IsLinearizedMap F.lin H.lin f from hf)
      ((h₀ χ s).mp hs)
  have hg' : PreservesWeight G₁ G₂ g' := by
    intro χ s hs
    apply (h₂ χ _).mpr
    exact linearizedMap_preserves_sectionWeight (show IsLinearizedMap H.lin K.lin g from hg)
      ((h₁ χ s).mp hs)
  obtain ⟨hi, he, hs⟩ := affineSectionsExact (ShortComplex.mk f g w) hex
  exact gradedCharacter_add G₀ G₁ G₂ f' g' hf' hg' hi he hs

end PointCharacters

section FromGrading

variable {T : GroupScheme k} {R : TestAlgebra k} {Z : SchemeOver k}
  {a : ModObj T.X (affineScheme R)} {F : (affineScheme R).left.Modules}

attribute [local instance] Classical.decEq

private abbrev sectionsModule (F : (affineScheme R).left.Modules) := (affineSections R).obj F

private def pullWeightedSection (G : WeightGrading k (Character T) (sectionsModule F))
    (f : Z ⟶ affineScheme R) (c : Character T → Γ(Z.left, ⊤)) :
    sectionsModule F →+ Γ(Pull f F, ⊤) :=
  (DirectSum.toAddMonoid fun χ => ({
    toFun := fun v : G.piece χ => c χ • pullSection f.left F v.val
    map_zero' := by
      change c χ • (pullSectionAdd f.left F) 0 = _
      rw [map_zero, smul_zero]
    map_add' := by
      intro v w
      change c χ • (pullSectionAdd f.left F) (v.val + w.val) = _
      let A := pullSectionAdd f.left F
      let v' : Γ(F, ⊤) := v.val
      let w' : Γ(F, ⊤) := w.val
      change c χ • A (v' + w') = c χ • A v' + c χ • A w'
      rw [A.map_add, smul_add] } : G.piece χ →+ Γ(Pull f F, ⊤))).comp
      (gradingDecomposition G).toAddEquiv.toAddMonoidHom

private theorem pullWeightedSection_apply (G : WeightGrading k (Character T) (sectionsModule F))
    (f : Z ⟶ affineScheme R) (c : Character T → Γ(Z.left, ⊤))
    (χ : Character T) (v : sectionsModule F) (hv : v ∈ G.piece χ) :
    pullWeightedSection G f c v = c χ • pullSection f.left F v := by
  unfold pullWeightedSection
  rw [AddMonoidHom.comp_apply]
  change DirectSum.toAddMonoid _ (gradingDecomposition G v) = _
  rw [gradingDecomposition_apply_of_mem G χ ⟨v, hv⟩]
  exact DirectSum.toAddMonoid_of _ _ _

private def additiveScalar {A V : Type*} [AddCommMonoid V] [DistribSMul A V] (r : A) :
    V →+ V where
  toFun v := r • v
  map_zero' := smul_zero _
  map_add' := smul_add _

set_option backward.isDefEq.respectTransparency false in
private theorem pullWeightedSection_smul (G : AffineGrading R a)
    (H : ModuleGrading G.val (sectionsModule F))
    (f g : Z ⟶ affineScheme R) (c : Character T → Γ(Z.left, ⊤))
    (hc : ∀ (δ χ : Character T) (r : R), r ∈ G.val.piece δ →
      c (δ * χ) * g.left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) =
        f.left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) * c χ)
    (r : Γ((affineScheme R).left, ⊤)) (s : Γ(F, ⊤)) :
    pullWeightedSection H.toWeightGrading g c (r • s) =
      f.left.appTop r • pullWeightedSection H.toWeightGrading g c s := by
  let σ := (Scheme.ΓSpecIso (affineRing R)).inv
  obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso σ).2 r
  let M : ModuleCat.{u} R := sectionsModule F
  let U := Γ(Pull g F, ⊤)
  let w := pullWeightedSection H.toWeightGrading g c
  let A : R →+ (M →+ U) :=
    { toFun := fun r => w.comp (additiveScalar (V := ↥M) r)
      map_zero' := by ext v; change w ((0 : R) • v) = 0; simp
      map_add' := by
        intro x y
        ext v
        change w ((x + y) • v) = w (x • v) + w (y • v)
        rw [add_smul, map_add] }
  let B : R →+ (M →+ U) :=
    { toFun := fun r => (additiveScalar (V := ↥U) (f.left.appTop (σ r))).comp w
      map_zero' := by ext v; simp [additiveScalar, map_zero]
      map_add' := by intro x y; ext v; simp [additiveScalar, map_add, add_smul] }
  have E : A = B := by
    apply WeightGrading.addHom_ext G.val.toWeightGrading
    intro δ x
    apply WeightGrading.addHom_ext H.toWeightGrading
    intro χ v
    let y : M := v.val
    let r : R := x.val
    have hv : r • y ∈ H.piece (δ * χ) := H.smul_mem x.property v.property
    change w (r • y) = f.left.appTop (σ r) • w y
    rw [pullWeightedSection_apply _ _ _ _ _ hv,
      pullWeightedSection_apply _ _ _ _ _ v.property]
    change c (δ * χ) • pullSection g.left F ((σ r) • (show Γ(F, ⊤) from y)) =
      f.left.appTop (σ r) • c χ • pullSection g.left F y
    rw [pullSection_smul, ← mul_smul, ← mul_smul, hc δ χ r x.property]
  exact DFunLike.congr_fun (DFunLike.congr_fun E r) s

set_option backward.isDefEq.respectTransparency false in
private def pullWeightedHom [F.IsQuasicoherent] (G : AffineGrading R a)
    (H : ModuleGrading G.val (sectionsModule F))
    (f g : Z ⟶ affineScheme R) (c : Character T → Γ(Z.left, ⊤))
    (hc : ∀ (δ χ : Character T) (r : R), r ∈ G.val.piece δ →
      c (δ * χ) * g.left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) =
        f.left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) * c χ) :
    Pull f F ⟶ Pull g F :=
  affinePullHom f.left (pullWeightedSection H.toWeightGrading g c)
    (map_add _) (pullWeightedSection_smul G H f g c hc)

set_option backward.isDefEq.respectTransparency false in
private theorem pullWeightedHom_apply [F.IsQuasicoherent] (G : AffineGrading R a)
    (H : ModuleGrading G.val (sectionsModule F))
    (f g : Z ⟶ affineScheme R) (c : Character T → Γ(Z.left, ⊤)) (hc)
    (χ : Character T) (v : sectionsModule F) (hv : v ∈ H.piece χ) :
    (pullWeightedHom G H f g c hc).app ⊤ (pullSection f.left F v) =
      c χ • pullSection g.left F v := by
  let s := pullWeightedSection H.toWeightGrading g c
  let hs (r : Γ((affineScheme R).left, ⊤)) (x : Γ(F, ⊤)) :=
    pullWeightedSection_smul G H f g c hc r x
  exact (affinePullHom_apply f.left s (map_add s) hs v).trans
    (pullWeightedSection_apply H.toWeightGrading g c χ v hv)

set_option backward.isDefEq.respectTransparency false in
private theorem affinePullHom_ext_of_homogeneous [F.IsQuasicoherent] {M : Z.left.Modules}
    (G : WeightGrading k (Character T) (sectionsModule F))
    (f : Z ⟶ affineScheme R) (p q : Pull f F ⟶ M)
    (h : ∀ χ (v : sectionsModule F), v ∈ G.piece χ →
      p.app ⊤ (pullSection f.left F v) = q.app ⊤ (pullSection f.left F v)) : p = q := by
  apply affinePullHom_ext f.left
  let p' := (p.app ⊤).hom.comp (pullSectionAdd f.left F)
  let q' := (q.app ⊤).hom.comp (pullSectionAdd f.left F)
  have E : p' = q' := WeightGrading.addHom_ext G fun χ v => h χ v.val v.property
  exact fun v => DFunLike.congr_fun E v

private abbrev actionProjection (T : GroupScheme k) (R : TestAlgebra k) :=
  snd T.X (affineScheme R)

private def projectedCharacter (T : GroupScheme k) (R : TestAlgebra k) (χ : Character T) :
    Γ((T.X ⊗ affineScheme R).left, ⊤) :=
  (fst T.X (affineScheme R)).left.appTop (characterFunction χ)

set_option backward.isDefEq.respectTransparency false in
private theorem projectedCharacter_mul (hT : IsSplitTorus T) (χ ψ : Character T) :
    projectedCharacter T R (χ * ψ) = projectedCharacter T R χ * projectedCharacter T R ψ := by
  unfold projectedCharacter
  rw [characterFunction_mul hT, map_mul]

set_option backward.isDefEq.respectTransparency false in
private theorem projectedCharacter_inv_mul (hT : IsSplitTorus T) (χ : Character T) :
    projectedCharacter T R χ⁻¹ * projectedCharacter T R χ = 1 := by
  rw [← projectedCharacter_mul hT, inv_mul_cancel]
  unfold projectedCharacter
  rw [characterFunction_one hT, map_one]

set_option backward.isDefEq.respectTransparency false in
private theorem gradedForward_scalar (G : AffineGrading R a) (hT : IsSplitTorus T)
    (δ χ : Character T) (r : R) (hr : r ∈ G.val.piece δ) :
    projectedCharacter T R (δ * χ) * a.smul.left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) =
      (actionProjection T R).left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) *
        projectedCharacter T R χ := by
  have h := (G.property δ r).mp hr
  change a.smul.left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) =
    projectedCharacter T R δ⁻¹ * (actionProjection T R).left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r)
    at h
  rw [h, projectedCharacter_mul hT]
  calc
    _ = (projectedCharacter T R δ⁻¹ * projectedCharacter T R δ) *
      ((actionProjection T R).left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) *
        projectedCharacter T R χ) := by ac_rfl
    _ = _ := by rw [projectedCharacter_inv_mul hT, one_mul]

set_option backward.isDefEq.respectTransparency false in
private theorem gradedInverse_scalar (G : AffineGrading R a) (hT : IsSplitTorus T)
    (δ χ : Character T) (r : R) (hr : r ∈ G.val.piece δ) :
    projectedCharacter T R (δ * χ)⁻¹ * (actionProjection T R).left.appTop
        ((Scheme.ΓSpecIso (affineRing R)).inv r) =
      a.smul.left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) *
        projectedCharacter T R χ⁻¹ := by
  have h := (G.property δ r).mp hr
  change a.smul.left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) =
    projectedCharacter T R δ⁻¹ * (actionProjection T R).left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r)
    at h
  rw [h, mul_inv, projectedCharacter_mul hT]
  ac_rfl

set_option backward.isDefEq.respectTransparency false in
/-- The universal sheaf isomorphism associated to a compatible affine module grading. -/
def gradedLinearizationIso [F.IsQuasicoherent] (G : AffineGrading R a)
    (H : ModuleGrading G.val (sectionsModule F)) (hT : IsSplitTorus T) :
    Pull (actionProjection T R) F ≅ Pull a.smul F := by
  let p := actionProjection T R
  let h := pullWeightedHom G H p a.smul (projectedCharacter T R) (gradedForward_scalar G hT)
  let g := pullWeightedHom G H a.smul p (fun χ => projectedCharacter T R χ⁻¹) (gradedInverse_scalar G hT)
  refine ⟨h, g, ?_, ?_⟩
  · apply affinePullHom_ext_of_homogeneous H.toWeightGrading
    intro χ v hv
    change g.app ⊤ (h.app ⊤ (pullSection p.left F v)) = pullSection p.left F v
    have h₁ : h.app ⊤ (pullSection p.left F v) = projectedCharacter T R χ • pullSection a.smul.left F v :=
      pullWeightedHom_apply G H p a.smul _ _ χ v hv
    have h₂ : g.app ⊤ (pullSection a.smul.left F v) = projectedCharacter T R χ⁻¹ • pullSection p.left F v :=
      pullWeightedHom_apply G H a.smul p _ _ χ v hv
    rw [h₁, Scheme.Modules.Hom.app_smul, h₂, ← mul_smul, mul_comm, projectedCharacter_inv_mul hT, one_smul]
  · apply affinePullHom_ext_of_homogeneous H.toWeightGrading
    intro χ v hv
    change h.app ⊤ (g.app ⊤ (pullSection a.smul.left F v)) = pullSection a.smul.left F v
    have h₁ : h.app ⊤ (pullSection p.left F v) = projectedCharacter T R χ • pullSection a.smul.left F v :=
      pullWeightedHom_apply G H p a.smul _ _ χ v hv
    have h₂ : g.app ⊤ (pullSection a.smul.left F v) = projectedCharacter T R χ⁻¹ • pullSection p.left F v :=
      pullWeightedHom_apply G H a.smul p _ _ χ v hv
    rw [h₂, Scheme.Modules.Hom.app_smul, h₁, ← mul_smul, projectedCharacter_inv_mul hT, one_smul]

set_option backward.isDefEq.respectTransparency false in
theorem gradedLinearizationIso_apply [F.IsQuasicoherent] (G : AffineGrading R a)
    (H : ModuleGrading G.val (sectionsModule F)) (hT : IsSplitTorus T)
    (χ : Character T) (v : sectionsModule F) (hv : v ∈ H.piece χ) :
    (gradedLinearizationIso G H hT).hom.app ⊤ (pullSection (snd T.X (affineScheme R)).left F v) =
      (fst T.X (affineScheme R)).left.appTop (characterFunction χ) • pullSection a.smul.left F v :=
  pullWeightedHom_apply G H (actionProjection T R) a.smul
    (projectedCharacter T R) (gradedForward_scalar G hT) χ v hv

end FromGrading

section GradingLinearizationLaws

variable {T : GroupScheme k} {R : TestAlgebra k} {Z : SchemeOver k}
  {a : ModObj T.X (affineScheme R)} {F : (affineScheme R).left.Modules}


set_option backward.isDefEq.respectTransparency false in
private theorem transport_apply_of_weight
    (θ : Pull (actionProjection T R) F ≅ Pull a.smul F)
    (t : Z ⟶ T.X) (y : Z ⟶ affineScheme R) (χ : Character T) (v : Γ(F, ⊤))
    (hθ : θ.hom.app ⊤ (pullSection (actionProjection T R).left F v) =
      projectedCharacter T R χ • pullSection a.smul.left F v) :
    (transport a θ t y).hom.app ⊤ (pullSection y.left F v) =
      t.left.appTop (characterFunction χ) • pullSection (actOn a t y).left F v := by
  rw [transport_eq_evalPullIso, evalPullIso_section]
  rw [hθ, pullSection_smul, Scheme.Modules.Hom.app_smul, comparePull_section]
  unfold projectedCharacter
  rw [← comp_appTop_apply, lift_fst]

private theorem pullCongr_section_app {x y : Z ⟶ affineScheme R} (h : x = y) (v : Γ(F, ⊤)) :
    (pullCongr F h).hom.app ⊤ (pullSection x.left F v) = pullSection y.left F v :=
  pullSection_congr (congrArg Over.Hom.left h) F v

section HomogeneousComposition

set_option backward.isDefEq.respectTransparency false

/-- A morphism sends the given section to the indicated scalar multiple. -/
private def ActsByScalar {S : Scheme.{u}} {P Q : S.Modules} (f : P ⟶ Q)
    (c : Γ(S, ⊤)) (v : Γ(P, ⊤)) (w : Γ(Q, ⊤)) : Prop :=
  f.app ⊤ v = c • w

private def CompositionOnSection {S : Scheme.{u}} {A B C D : S.Modules}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (q : A ⟶ D) (w : Γ(A, ⊤)) : Prop :=
  (f ≫ g ≫ h).app ⊤ w = q.app ⊤ w

private theorem composition_of_scaled_sections {S : Scheme.{u}} {A B C D : S.Modules}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (q : A ⟶ D)
    (w : Γ(A, ⊤)) (x : Γ(B, ⊤)) (y : Γ(C, ⊤)) (z : Γ(D, ⊤))
    (s t r : Γ(S, ⊤)) (hr : r = t * s)
    (hf : ActsByScalar f t w x) (hg : ActsByScalar g s x y)
    (hh : h.app ⊤ y = z) (hq : ActsByScalar q r w z) :
    CompositionOnSection f g h q w := by
  unfold ActsByScalar at *
  change h.app ⊤ (g.app ⊤ (f.app ⊤ w)) = q.app ⊤ w
  rw [hf, Scheme.Modules.Hom.app_smul, hg, ← mul_smul, Scheme.Modules.Hom.app_smul, hh, hq, hr]

private theorem transport_scales_section (θ : Pull (actionProjection T R) F ≅ Pull a.smul F)
    (t : Z ⟶ T.X) (y : Z ⟶ affineScheme R) (χ : Character T) (v : Γ(F, ⊤))
    (hθ : ActsByScalar θ.hom (projectedCharacter T R χ)
      (pullSection (actionProjection T R).left F v) (pullSection a.smul.left F v)) :
    ActsByScalar (transport a θ t y).hom (t.left.appTop (characterFunction χ))
      (pullSection y.left F v) (pullSection (actOn a t y).left F v) :=
  @transport_apply_of_weight k _ T R Z a F θ t y χ v hθ

private theorem gradedLinearization_comp_on_section
    (θ : Pull (actionProjection T R) F ≅ Pull a.smul F)
    (s t r : Z ⟶ T.X) (y : Z ⟶ affineScheme R)
    (h : actOn a s (actOn a t y) = actOn a r y)
    (χ : Character T) (v : Γ(F, ⊤))
    (hc : r.left.appTop (characterFunction χ) =
      t.left.appTop (characterFunction χ) * s.left.appTop (characterFunction χ))
    (hθ : ActsByScalar θ.hom (projectedCharacter T R χ)
      (pullSection (actionProjection T R).left F v) (pullSection a.smul.left F v)) :
    CompositionOnSection (transport a θ t y).hom (transport a θ s (actOn a t y)).hom
      (pullCongr F h).hom (transport a θ r y).hom (pullSection y.left F v) :=
  composition_of_scaled_sections _ _ _ _ _ _ _ _ _ _ _ hc
    (transport_scales_section θ t y χ v hθ)
    (transport_scales_section θ s (actOn a t y) χ v hθ)
    (pullCongr_section_app h v)
    (transport_scales_section θ r y χ v hθ)

end HomogeneousComposition

variable [F.IsQuasicoherent]

set_option backward.isDefEq.respectTransparency false in
private theorem gradedLinearizationUnit (H : WeightGrading k (Character T) (sectionsModule F))
    (θ : Pull (actionProjection T R) F ≅ Pull a.smul F)
    (hθ : ∀ χ (v : sectionsModule F), v ∈ H.piece χ →
      θ.hom.app ⊤ (pullSection (actionProjection T R).left F v) =
        projectedCharacter T R χ • pullSection a.smul.left F v)
    (y : Z ⟶ affineScheme R) :
    ∃ h : actOn a (1 : Z ⟶ T.X) y = y,
      (transport a θ 1 y).hom ≫ (pullCongr F h).hom = 𝟙 _ := by
  let := a
  let h : actOn a (1 : Z ⟶ T.X) y = y := one_smul (Z ⟶ T.X) y
  refine ⟨h, affinePullHom_ext_of_homogeneous H y _ _ ?_⟩
  intro χ v hv
  change (pullCongr F h).hom.app ⊤
    ((transport a θ 1 y).hom.app ⊤ (pullSection y.left F v)) = pullSection y.left F v
  rw [transport_apply_of_weight θ 1 y χ v (hθ χ v hv), characterFunction_at_one, one_smul]
  exact pullCongr_section_app h v

section GradedComposition

set_option backward.isDefEq.respectTransparency false

private theorem composition_of_homogeneous_sections
    (H : WeightGrading k (Character T) (sectionsModule F)) (y : Z ⟶ affineScheme R)
    {B C D : Z.left.Modules} (f : Pull y F ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (q : Pull y F ⟶ D)
    (hh : ∀ χ (v : sectionsModule F), v ∈ H.piece χ →
      CompositionOnSection f g h q (pullSection y.left F v)) :
    ComposesTo f g h q :=
  affinePullHom_ext_of_homogeneous H y (f ≫ g ≫ h) q hh

private theorem gradedLinearization_mul (H : WeightGrading k (Character T) (sectionsModule F))
    (θ : Pull (actionProjection T R) F ≅ Pull a.smul F)
    (hθ : ∀ χ (v : sectionsModule F), v ∈ H.piece χ →
      θ.hom.app ⊤ (pullSection (actionProjection T R).left F v) =
        projectedCharacter T R χ • pullSection a.smul.left F v)
    (s t : Z ⟶ T.X) (y : Z ⟶ affineScheme R) :
    ∃ h : actOn a s (actOn a t y) = actOn a (s * t) y, TransportComposition θ s t y h := by
  let := a
  let r := s * t
  let h : actOn a s (actOn a t y) = actOn a r y := (mul_smul s t y).symm
  refine ⟨h, ?_⟩
  exact composition_of_homogeneous_sections H y
    (transport a θ t y).hom (transport a θ s (actOn a t y)).hom (pullCongr F h).hom
    (transport a θ r y).hom
    (fun χ v hv => gradedLinearization_comp_on_section θ s t r y h χ v
      ((characterFunction_at_mul χ s t).trans (mul_comm _ _)) (hθ χ v hv))

/-- The linearization reconstructed from the compatible module grading. -/
def gradedLinearization (G : AffineGrading R a)
    (H : ModuleGrading G.val (sectionsModule F)) (hT : IsSplitTorus T) : Linearization a F where
  iso := gradedLinearizationIso G H hT
  unit := fun _ y => gradedLinearizationUnit H.toWeightGrading _ (gradedLinearizationIso_apply G H hT) y
  mul := fun _ s t y =>
    gradedLinearization_mul H.toWeightGrading _ (gradedLinearizationIso_apply G H hT) s t y

end GradedComposition

end GradingLinearizationLaws
section PointCharacterMap

variable {T : GroupScheme k}

set_option backward.isDefEq.respectTransparency false in
theorem pointSheafCharacter_twist (hT : IsSplitTorus T)
    {F H : EquivariantCoherent (pointAction T)} {δ : Character T}
    (G₀ : PointWeights F) (G₁ : PointWeights H)
    (h₀ : ∀ χ s, s ∈ G₀.piece χ ↔ HasSectionWeight F.lin s χ)
    (h₁ : ∀ χ s, s ∈ G₁.piece χ ↔ HasSectionWeight H.lin s χ)
    (ht : IsTwist δ F H) :
    pointSheafCharacter H G₁ = eChar δ • pointSheafCharacter F G₀ := by
  obtain ⟨i, hi⟩ := sectionWeight_isTwist hT ht
  let S := affineSections (pointRing k)
  let j := S.mapIso i
  let e : S.obj F.sheaf ≃ₗ[k] S.obj H.sheaf := j.toLinearEquiv
  have hmem (ψ : Character T) (s : S.obj F.sheaf) :
      e s ∈ G₁.piece (δ * ψ) ↔ s ∈ G₀.piece ψ := by
    rw [h₁, h₀]
    exact hi ψ s
  have hdim (ψ : Character T) :
      Module.finrank k (G₁.piece (δ * ψ)) = Module.finrank k (G₀.piece ψ) := by
    have hm : (G₀.piece ψ).map e.toLinearMap = G₁.piece (δ * ψ) := by
      ext s
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact (hmem ψ v).mpr hv
      · intro hs
        obtain ⟨v, rfl⟩ := e.surjective s
        exact ⟨v, (hmem ψ v).mp hs, rfl⟩
    exact (LinearEquiv.finrank_eq (e.ofSubmodules _ _ hm)).symm
  ext ψ
  change (pointSheafCharacter H G₁).coeff ψ =
    (MonoidAlgebra.single δ 1 * pointSheafCharacter F G₀).coeff ψ
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul, pointSheafCharacter_coeff, pointSheafCharacter_coeff]
  have hh : δ * (δ⁻¹ * ψ) = ψ := mul_inv_cancel_left (G := Character T) δ ψ
  have hd := hdim (δ⁻¹ * ψ)
  have hdim' := (congrArg (fun z : Character T => Module.finrank k (G₁.piece z)) hh).symm.trans hd
  exact congrArg (fun n : ℕ => (n : ℤ)) hdim'

/-- The character of coherent sheaves over the rational point descends to the
class module once the homogeneous submodules have been identified. -/
def pointCharacterMap (hT : IsSplitTorus T)
    (G : ∀ F : EquivariantCoherent (pointAction T), PointWeights F)
    (hG : ∀ F χ s, s ∈ (G F).piece χ ↔ HasSectionWeight F.lin s χ) :
    GZero (pointAction T) →ₗ[CharacterRing T] CharacterRing T :=
  liftClassMap (fun F => pointSheafCharacter F (G F))
    (fun {F H K} _ _ w hf hg hex =>
      pointSheafCharacter_exact (G F) (G H) (G K) (hG F) (hG H) (hG K) w hf hg hex)
    (fun {_ F H} ht => pointSheafCharacter_twist hT (G F) (G H) (hG F) (hG H) ht)

theorem pointCharacterMap_classOf (hT : IsSplitTorus T)
    (G : ∀ F : EquivariantCoherent (pointAction T), PointWeights F)
    (hG : ∀ F χ s, s ∈ (G F).piece χ ↔ HasSectionWeight F.lin s χ)
    (F : EquivariantCoherent (pointAction T)) (χ : Character T) :
    (pointCharacterMap hT G hG (classOf F)).coeff χ = (Module.finrank k ((G F).piece χ) : ℤ) := by
  unfold pointCharacterMap
  rw [liftClassMap_classOf, pointSheafCharacter_coeff]

end PointCharacterMap

section PointNormalization

variable {T : GroupScheme k}

set_option backward.isDefEq.respectTransparency false in
theorem pointSheafCharacter_of_trivial_line (hT : IsSplitTorus T)
    (F : EquivariantCoherent (pointAction T)) (G : PointWeights F)
    (hG : ∀ χ s, s ∈ G.piece χ ↔ HasSectionWeight F.lin s χ)
    (i : tilde (ModuleCat.of k k) ≅ F.sheaf)
    (hF : F.lin.iso.hom = 𝟙 _) :
    pointSheafCharacter F G = 1 := by
  classical
  let R := pointRing k
  let M := (affineSections R).obj F.sheaf
  have htop : G.piece 1 = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro s
    apply (hG 1 s).mpr
    unfold HasSectionWeight
    rw [hF, characterFunction_one hT, map_one, one_smul]
    rfl
  let B : ModuleCat.{u} k := ModuleCat.of k k
  let j : B ≅ M := (tilde.isoTop (R := CommRingCat.of k) B) ≪≫
    (affineSections R).mapIso i
  have hc : Module.finrank k M = 1 :=
    j.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self k)
  ext χ
  rw [pointSheafCharacter_coeff]
  by_cases h : χ = 1
  · subst χ
    rw [htop, finrank_top, hc, MonoidAlgebra.coeff_one_one]
    rfl
  · have hd := G.internal.submodule_iSupIndep.pairwiseDisjoint h
    change Disjoint (G.piece χ) (G.piece 1) at hd
    rw [htop, disjoint_top] at hd
    rw [hd, finrank_bot, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single]
    simp [Ne.symm h]

theorem pointCharacterMap_trivial (hT : IsSplitTorus T)
    (G : ∀ F : EquivariantCoherent (pointAction T), PointWeights F)
    (hG : ∀ F χ s, s ∈ (G F).piece χ ↔ HasSectionWeight F.lin s χ) :
    pointCharacterMap hT G hG (classOf (trivialPointLine T)) = 1 := by
  unfold pointCharacterMap
  rw [liftClassMap_classOf]
  exact pointSheafCharacter_of_trivial_line hT _ (G _) (hG _) (Iso.refl _) rfl

theorem pointCharacterMap_surjective (hT : IsSplitTorus T)
    (G : ∀ F : EquivariantCoherent (pointAction T), PointWeights F)
    (hG : ∀ F χ s, s ∈ (G F).piece χ ↔ HasSectionWeight F.lin s χ) :
    Function.Surjective (pointCharacterMap hT G hG) := by
  intro r
  refine ⟨r • classOf (trivialPointLine T), ?_⟩
  rw [map_smul, pointCharacterMap_trivial, smul_eq_mul, mul_one]

end PointNormalization

section InverseTransport

variable {T : GroupScheme k} {X Z : SchemeOver k} {a : ModObj T.X X}
    {F : X.left.Modules}

set_option backward.isDefEq.respectTransparency false in
private theorem transport_symm_eq_eval
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Z ⟶ T.X) (x : Z ⟶ X) :
    (transport a θ t x).symm =
      evalPullIso θ.symm (lift t x) rfl (lift_snd t x) := by
  rw [transport_eq_evalPullIso]
  apply Iso.ext
  simp only [evalPullIso, Iso.symm_hom, Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]

set_option maxHeartbeats 370000 in
set_option backward.isDefEq.respectTransparency false in
private theorem projectionExpansion_evaluate
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤)))
    (hE : ∀ χ s, E ((fst T.X X).left.appTop (characterFunction χ) •
      pullSection (snd T.X X).left F s) = Finsupp.single χ s)
    (t : Z ⟶ T.X) (x : Z ⟶ X) (z : Character T →₀ Γ(F, ⊤)) :
    (comparePull F (lift t x) (snd T.X X) (lift_snd t x)).hom.app ⊤
      (pullSection (lift t x).left (Pull (snd T.X X) F) (E.symm z)) =
      z.sum (fun χ s => t.left.appTop (characterFunction χ) • pullSection x.left F s) := by
  let p := snd T.X X
  let l := lift t x
  let C := comparePull F l p (lift_snd t x)
  let τ := pullSectionAdd l.left (Pull p F)
  let u := pullSectionAdd x.left F
  let f := ((C.hom.app ⊤).hom.comp τ).comp E.symm.toAddMonoidHom
  let q (χ : Character T) : Γ(F, ⊤) →+ Γ(Pull x F, ⊤) :=
    (additiveScalar (t.left.appTop (characterFunction χ))).comp u
  let g := Finsupp.liftAddHom q
  have h : f = g := by
    apply Finsupp.addHom_ext
    intro χ s
    let c := (fst T.X X).left.appTop (characterFunction χ)
    have h₀ : E.symm (Finsupp.single χ s) = c • pullSection p.left F s :=
      E.symm_apply_eq.mpr ((hE χ s).symm)
    calc
      f (Finsupp.single χ s) =
        C.hom.app ⊤ (pullSection l.left (Pull p F) (c • pullSection p.left F s)) :=
        by
          change C.hom.app ⊤ (pullSection l.left (Pull p F) (E.symm (Finsupp.single χ s))) = _
          rw [h₀]
      _ = l.left.appTop c • pullSection x.left F s :=
        comparePull_section_smul F l p (lift_snd t x) c s
      _ = t.left.appTop (characterFunction χ) • pullSection x.left F s := by
        have hl : l.left.appTop c = t.left.appTop (characterFunction χ) := by
          change l.left.appTop ((fst T.X X).left.appTop (characterFunction χ)) = _
          rw [← comp_appTop_apply, lift_fst]
        rw [hl]
      _ = g (Finsupp.single χ s) := (Finsupp.liftAddHom_apply_single q χ s).symm
  exact (DFunLike.congr_fun h z).trans (Finsupp.liftAddHom_apply q z)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse linearization can be evaluated at any pair of scheme-valued
points by substituting into the universal character expansion. -/
theorem inverseTransport_expansion (L : Linearization a F)
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤)))
    (hE : ∀ χ s, E ((fst T.X X).left.appTop (characterFunction χ) •
      pullSection (snd T.X X).left F s) = Finsupp.single χ s)
    (t : Z ⟶ T.X) (x : Z ⟶ X) (s : Γ(F, ⊤)) :
    (transport a L.iso t x).inv.app ⊤ (pullSection (actOn a t x).left F s) =
      (E (L.iso.inv.app ⊤ (pullSection a.smul.left F s))).sum
        (fun χ v => t.left.appTop (characterFunction χ) • pullSection x.left F v) := by
  let z := E (L.iso.inv.app ⊤ (pullSection a.smul.left F s))
  have h : E.symm z = L.iso.inv.app ⊤ (pullSection a.smul.left F s) := E.symm_apply_apply _
  change (transport a L.iso t x).symm.hom.app ⊤ (pullSection (actOn a t x).left F s) = _
  rw [transport_symm_eq_eval, evalPullIso_section]
  have H := projectionExpansion_evaluate E hE t x z
  rw [h] at H
  exact H

end InverseTransport

section InverseUnit

variable {T : GroupScheme k} {X Z : SchemeOver k} {a : ModObj T.X X}
    {F : X.left.Modules}

set_option backward.isDefEq.respectTransparency false in
private theorem inverseTransport_unit (L : Linearization a F) (x : Z ⟶ X) (s : Γ(F, ⊤)) :
    (transport a L.iso 1 x).inv.app ⊤ (pullSection (actOn a 1 x).left F s) =
      pullSection x.left F s := by
  obtain ⟨h, hl⟩ := L.unit Z x
  let e := transport a L.iso 1 x
  have he : e.inv = (pullCongr F h).hom := by
    apply (cancel_epi e.hom).mp
    exact e.hom_inv_id.trans hl.symm
  change e.inv.app ⊤ (pullSection (actOn a 1 x).left F s) = _
  rw [he]
  exact pullSection_congr (congrArg Over.Hom.left h) F s

set_option backward.isDefEq.respectTransparency false in
/-- The identity law of a linearization gives the sum of the character
coefficients of each section. -/
theorem inverseTransport_coefficients_sum (L : Linearization a F)
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤)))
    (hE : ∀ χ s, E ((fst T.X X).left.appTop (characterFunction χ) •
      pullSection (snd T.X X).left F s) = Finsupp.single χ s)
    (s : Γ(F, ⊤)) :
    (E (L.iso.inv.app ⊤ (pullSection a.smul.left F s))).sum (fun _ v => v) = s := by
  let f := pullSectionAdd (𝟙 X.left) F
  let z := E (L.iso.inv.app ⊤ (pullSection a.smul.left F s))
  have h := inverseTransport_expansion L E hE (1 : X ⟶ T.X) (𝟙 X) s
  rw [inverseTransport_unit L (𝟙 X) s] at h
  change f s = z.sum (fun χ v => (1 : X ⟶ T.X).left.appTop (characterFunction χ) • f v) at h
  simp only [characterFunction_at_one, one_smul] at h
  refine (pullSection_bijective_of_isIso (𝟙 X.left) F).1 ?_
  change f (z.sum fun _ v => v) = f s
  rw [h]
  exact map_sum f _ _

end InverseUnit

section CoefficientExtraction

private theorem coefficient_sum {Λ M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (E : N ≃+ (Λ →₀ M)) (d : Λ → M → N)
    (hE : ∀ i w, E (d i w) = Finsupp.single i w)
    (I : Finset Λ) (v : Λ → M) (hv : ∀ i, i ∉ I → v i = 0) (i : Λ) :
    E (∑ j ∈ I, d j (v j)) i = v i := by
  classical
  change ((Finsupp.applyAddHom i).comp E.toAddMonoidHom) (∑ j ∈ I, d j (v j)) = v i
  rw [map_sum, Finset.sum_eq_single i]
  · exact (congrArg (fun z : Λ →₀ M => z i) (hE i (v i))).trans (Finsupp.single_eq_same)
  · intro j _ h
    change E (d j (v j)) i = 0
    rw [hE, Finsupp.single_eq_of_ne h.symm]
  · intro hi
    change E (d i (v i)) i = 0
    rw [hE, hv i hi, Finsupp.single_zero, Finsupp.zero_apply]

private theorem eq_of_weighted_sums {Λ M N V : Type*} [Zero V] [AddCommMonoid M]
    [AddCommMonoid N] (E : N ≃+ (Λ →₀ M)) (d : Λ → M → N)
    (hE : ∀ i w, E (d i w) = Finsupp.single i w)
    (z : Λ →₀ V) (l r : Λ → V → M) (hl : ∀ i, l i 0 = 0) (hr : ∀ i, r i 0 = 0)
    (h : z.sum (fun i v => d i (l i v)) = z.sum (fun i v => d i (r i v))) (i : Λ) :
    l i (z i) = r i (z i) := by
  have H₁ := coefficient_sum E d hE z.support (fun j => l j (z j))
    (fun j hj => (congrArg (l j) (Finsupp.notMem_support_iff.mp hj)).trans (hl j)) i
  have H₂ := coefficient_sum E d hE z.support (fun j => r j (z j))
    (fun j hj => (congrArg (r j) (Finsupp.notMem_support_iff.mp hj)).trans (hr j)) i
  exact H₁.symm.trans ((congrArg (fun w => E w i) h).trans H₂)

variable {T : GroupScheme k} {X Y Z : SchemeOver k} {a : ModObj T.X X}
    {F : X.left.Modules}

set_option backward.isDefEq.respectTransparency false in
private theorem sectionWeight_iff_inverse (hT : IsSplitTorus T) (L : Linearization a F)
    (χ : Character T) (v : Γ(F, ⊤)) :
    HasSectionWeight L v χ⁻¹ ↔ L.iso.inv.app ⊤ (pullSection a.smul.left F v) =
      (fst T.X X).left.appTop (characterFunction χ) • pullSection (snd T.X X).left F v := by
  let c := (fst T.X X).left.appTop (characterFunction χ)
  let d := (fst T.X X).left.appTop (characterFunction χ⁻¹)
  let x := pullSection (snd T.X X).left F v
  let y := pullSection a.smul.left F v
  have hu : c * d = 1 := by
    rw [← map_mul, ← characterFunction_mul hT, mul_inv_cancel, characterFunction_one hT, map_one]
  have hv : d * c = 1 := (mul_comm d c).trans hu
  change L.iso.hom.app ⊤ x = d • y ↔ L.iso.inv.app ⊤ y = c • x
  constructor
  · intro h
    calc
      L.iso.inv.app ⊤ y = L.iso.inv.app ⊤ (c • (d • y)) := by rw [← mul_smul, hu, one_smul]
      _ = c • x := by rw [← h, Scheme.Modules.Hom.app_smul, hom_apply_inv_apply]
  · intro h
    calc
      L.iso.hom.app ⊤ x = L.iso.hom.app ⊤ (d • (c • x)) := by rw [← mul_smul, hv, one_smul]
      _ = d • y := by rw [← h, Scheme.Modules.Hom.app_smul]; exact congrArg (d • ·) (hom_apply_inv_apply L.iso.symm y)

set_option backward.isDefEq.respectTransparency false in
private theorem sectionWeight_of_inverse_at_chart (hT : IsSplitTorus T) (L : Linearization a F)
    (j : Y ≅ T.X ⊗ X) (χ : Character T) (v : Γ(F, ⊤))
    (h : let t := j.hom ≫ fst T.X X
         let x := j.hom ≫ snd T.X X
         (transport a L.iso t x).inv.app ⊤ (pullSection (actOn a t x).left F v) =
           t.left.appTop (characterFunction χ) • pullSection x.left F v) :
    HasSectionWeight L v χ⁻¹ := by
  let t := j.hom ≫ fst T.X X
  let x := j.hom ≫ snd T.X X
  let l := lift t x
  let p := snd T.X X
  have hl : l = j.hom := by simp [l, t, x]
  have : IsIso l.left := by
    have : IsIso l := by rw [hl]; infer_instance
    exact inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of k))).map l))
  apply (sectionWeight_iff_inverse hT L χ v).mpr
  let c := (fst T.X X).left.appTop (characterFunction χ)
  let C := comparePull F l p (lift_snd t x)
  have H : C.hom.app ⊤
        (pullSection l.left (Pull p F) (L.iso.inv.app ⊤ (pullSection a.smul.left F v))) =
      t.left.appTop (characterFunction χ) • pullSection x.left F v := by
    change (transport a L.iso t x).symm.hom.app ⊤ (pullSection (actOn a t x).left F v) = _ at h
    rw [transport_symm_eq_eval, evalPullIso_section] at h
    exact h
  have H' : C.hom.app ⊤ (pullSection l.left (Pull p F) (c • pullSection p.left F v)) =
      t.left.appTop (characterFunction χ) • pullSection x.left F v := by
    rw [comparePull_section_smul]
    have hc : l.left.appTop c = t.left.appTop (characterFunction χ) := by
      rw [show l.left.appTop c = (l ≫ fst T.X X).left.appTop (characterFunction χ) from
        (comp_appTop_apply l (fst T.X X) _).symm, lift_fst]
    rw [hc]
  exact (pullSection_bijective_of_isIso l.left (Pull p F)).1
    ((moduleSectionsIso C).injective (H.trans H'.symm))


end CoefficientExtraction

section InternalFromCoefficients

variable {Λ M : Type u} [CommGroup Λ] [AddCommGroup M] [Module k M]

attribute [local instance] Classical.decEq

/-- In an expansion indexed by inverse weights, the coefficients are the
components of an internal direct sum. -/
private theorem internal_of_inverse_coefficients (G : Λ → Submodule k M)
    (C : M →+ (Λ →₀ M))
    (hmem : ∀ i v, C v i ∈ G i⁻¹)
    (hsum : ∀ v, (C v).sum (fun _ w => w) = v)
    (hsingle : ∀ i (v : G i), C v.val = Finsupp.single i⁻¹ v.val) :
    DirectSum.IsInternal G := by
  classical
  constructor
  · let I₀ := DFinsupp.mapRange.addMonoidHom (fun i => (G i).subtype.toAddMonoidHom)
    let I₁ := (finsuppAddEquivDFinsupp : (Λ →₀ M) ≃+ (Π₀ _ : Λ, M)).symm
    let I := I₁.toAddMonoidHom.comp I₀
    let D := DirectSum.coeLinearMap G
    let J : (Λ →₀ M) ≃+ (Λ →₀ M) := Finsupp.domCongr (Equiv.inv Λ)
    have e : J.toAddMonoidHom.comp (C.comp D.toAddMonoidHom) = I := by
      apply DirectSum.addHom_ext
      intro i v
      change J (C (D (DirectSum.of (fun j => G j) i v))) =
        (I₀ (DirectSum.of (fun j => G j) i v)).toFinsupp
      rw [DirectSum.coeLinearMap_of, hsingle]
      change Finsupp.equivMapDomain _ (Finsupp.single i⁻¹ v.val) = _
      rw [Finsupp.equivMapDomain_single]
      change Finsupp.single i⁻¹⁻¹ v.val =
        (DFinsupp.mapRange (fun j (w : G j) => w.val) (fun _ => rfl) (DFinsupp.single i v)).toFinsupp
      rw [inv_inv, DFinsupp.mapRange_single, DFinsupp.toFinsupp_single]
    have hi : Function.Injective I := by
      apply I₁.injective.comp
      exact (DFinsupp.mapRange_injective (fun i (w : G i) => w.val) (fun _ => rfl)).2
        (fun _ => Subtype.val_injective)
    intro x y h
    apply hi
    rw [← e]
    change J (C (D x)) = J (C (D y))
    exact congrArg (fun w => J (C w)) h
  · intro v
    let w := C v
    let x (i : Λ) := DirectSum.of (fun j => G j) i⁻¹ ⟨w i, hmem i v⟩
    refine ⟨∑ i ∈ w.support, x i, ?_⟩
    change (DirectSum.coeLinearMap G) (∑ i ∈ w.support, x i) = v
    rw [map_sum, ← hsum v]
    exact Finset.sum_congr rfl (fun i _ => DirectSum.coeLinearMap_of G i⁻¹ ⟨w i, hmem i v⟩)

end InternalFromCoefficients

section CoordinateWeightDecomposition

variable {T : GroupScheme k} {X Z : SchemeOver k}

attribute [local instance] Classical.decEq

private theorem ringIsoEquiv_symm_apply {R S : CommRingCat.{u}} (e : R ≅ S) (w : S) :
    (ringIsoEquiv e).symm w = e.inv w := by
  apply (ringIsoEquiv e).injective
  rw [RingEquiv.apply_symm_apply]
  exact (congrArg (fun g : S ⟶ S => g w) e.inv_hom_id).symm

set_option backward.isDefEq.respectTransparency false in
private theorem projectionFunctionExpansion (hT : IsSplitTorus T) (R : TestAlgebra k) :
    let X := affineScheme R
    ∃ E : Γ((T.X ⊗ X).left, ⊤) ≃+ (Character T →₀ Γ(X.left, ⊤)),
      ∀ χ f, E ((fst T.X X).left.appTop (characterFunction χ) * (snd T.X X).left.appTop f) =
        Finsupp.single χ f := by
  intro X
  let S := groupRingAlgebra R (Character T)
  obtain ⟨j, hp, hc⟩ := torusProductChart T hT R
  let : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of k))).map j.hom))
  let e₀ := (ringIsoEquiv (asIso j.hom.left.appTop)).toAddEquiv
  let j₁ : Γ((affineScheme S).left, ⊤) ≅ affineRing S := Scheme.ΓSpecIso (affineRing S)
  let j₂ : Γ(X.left, ⊤) ≅ affineRing R := Scheme.ΓSpecIso (affineRing R)
  let e₁ := ringIsoEquiv j₁
  let e₂ := ringIsoEquiv j₂
  let e := (e₀.trans e₁.toAddEquiv).trans (MonoidAlgebra.coeffAddEquiv.trans
    (Finsupp.mapRange.addEquiv e₂.symm.toAddEquiv))
  refine ⟨e, ?_⟩
  intro χ f
  let p := snd T.X X
  let q := fst T.X X
  let b := groupRingConstants R (Character T)
  let c := characterFunction χ
  have hf : j.hom.left.appTop (p.left.appTop f) =
      (Scheme.ΓSpecIso (affineRing S)).inv (b (e₂ f)) := by
    rw [← comp_appTop_apply, hp]
    have h : f = j₂.inv (e₂ f) := (e₂.symm_apply_apply f).symm.trans
      (ringIsoEquiv_symm_apply j₂ (e₂ f))
    calc
      _ = (Spec.map (CommRingCat.ofHom b.hom.toRingHom)).appTop
          ((Scheme.ΓSpecIso (affineRing R)).inv (e₂ f)) :=
        congrArg ((Spec.map (CommRingCat.ofHom b.hom.toRingHom)).appTop) h
      _ = _ := appTop_Spec_map _ _
  have ht : j.hom.left.appTop (q.left.appTop c) =
      (Scheme.ΓSpecIso (affineRing S)).inv (MonoidAlgebra.of R _ χ) :=
    (comp_appTop_apply j.hom q c).symm.trans (hc χ)
  change (Finsupp.mapRange.addEquiv e₂.symm.toAddEquiv)
    (MonoidAlgebra.coeffAddEquiv (e₁ (j.hom.left.appTop (q.left.appTop c * p.left.appTop f)))) = _
  rw [map_mul, ht, hf]
  have he (w : S) : e₁ (j₁.inv w) = w := by
    rw [← ringIsoEquiv_symm_apply, e₁.apply_symm_apply]
  have hmul (v w : S) : e₁ (j₁.inv v * j₁.inv w) = v * w :=
    (e₁.map_mul _ _).trans (congrArg₂ (· * ·) (he v) (he w))
  change (Finsupp.mapRange.addEquiv e₂.symm.toAddEquiv)
    (MonoidAlgebra.coeffAddEquiv (e₁ (j₁.inv (MonoidAlgebra.of R _ χ) * j₁.inv (b (e₂ f))))) = _
  rw [hmul]
  have hs : (MonoidAlgebra.of R _ χ * b (e₂ f) : S) = MonoidAlgebra.single χ (e₂ f) := by
    change MonoidAlgebra.single χ (1 : R) * MonoidAlgebra.single 1 (e₂ f) = _
    rw [MonoidAlgebra.single_mul_single, mul_one, one_mul]
  rw [hs]
  ext i
  change e₂.symm (Finsupp.single χ (e₂ f) i) = Finsupp.single χ f i
  by_cases h : i = χ
  · subst i
    simp
  · simp [Finsupp.single_eq_of_ne h]

set_option backward.isDefEq.respectTransparency false in
private theorem functionExpansion_evaluate
    (E : Γ((T.X ⊗ X).left, ⊤) ≃+ (Character T →₀ Γ(X.left, ⊤)))
    (hE : ∀ χ f, E ((fst T.X X).left.appTop (characterFunction χ) * (snd T.X X).left.appTop f) =
      Finsupp.single χ f)
    (t : Z ⟶ T.X) (x : Z ⟶ X) (f : Γ((T.X ⊗ X).left, ⊤)) :
    (lift t x).left.appTop f =
      (E f).sum (fun χ r => t.left.appTop (characterFunction χ) * x.left.appTop r) := by
  let l := lift t x
  let B := l.left.appTop.hom.toAddMonoidHom
  let q (χ : Character T) := (AddMonoidHom.mulLeft (t.left.appTop (characterFunction χ))).comp
    x.left.appTop.hom.toAddMonoidHom
  have h : B.comp E.symm.toAddMonoidHom = Finsupp.liftAddHom q := by
    apply Finsupp.addHom_ext
    intro χ r
    let c := characterFunction χ
    let w := (fst T.X X).left.appTop c * (snd T.X X).left.appTop r
    have hw : E.symm (Finsupp.single χ r) = w := E.symm_apply_eq.mpr (hE χ r).symm
    rw [Finsupp.liftAddHom_apply_single]
    change l.left.appTop (E.symm (Finsupp.single χ r)) = t.left.appTop c * x.left.appTop r
    rw [hw, show w = (fst T.X X).left.appTop c * (snd T.X X).left.appTop r from rfl, map_mul]
    exact congrArg₂ (· * ·)
      ((comp_appTop_apply l (fst T.X X) c).symm.trans (congrArg (fun g => g.left.appTop c) (lift_fst t x)))
      ((comp_appTop_apply l (snd T.X X) r).symm.trans (congrArg (fun g => g.left.appTop r) (lift_snd t x)))
  have hh := DFunLike.congr_fun h (E f)
  change B (E.symm (E f)) = _ at hh
  rw [E.symm_apply_apply, Finsupp.liftAddHom_apply] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
private theorem functionExpansion_action {a : ModObj T.X X}
    (E : Γ((T.X ⊗ X).left, ⊤) ≃+ (Character T →₀ Γ(X.left, ⊤)))
    (hE : ∀ χ f, E ((fst T.X X).left.appTop (characterFunction χ) * (snd T.X X).left.appTop f) =
      Finsupp.single χ f)
    (t : Z ⟶ T.X) (x : Z ⟶ X) (f : Γ(X.left, ⊤)) :
    (actOn a t x).left.appTop f =
      (E (a.smul.left.appTop f)).sum (fun χ r =>
        t.left.appTop (characterFunction χ) * x.left.appTop r) :=
  (comp_appTop_apply (lift t x) a.smul f).trans (functionExpansion_evaluate E hE t x _)

set_option backward.isDefEq.respectTransparency false in
private theorem functionExpansion_coefficients_weight {R : TestAlgebra k}
    {a : ModObj T.X (affineScheme R)} (hT : IsSplitTorus T)
    (E : Γ((T.X ⊗ affineScheme R).left, ⊤) ≃+ (Character T →₀ Γ((affineScheme R).left, ⊤)))
    (hE : ∀ χ f, E ((fst T.X (affineScheme R)).left.appTop (characterFunction χ) *
      (snd T.X (affineScheme R)).left.appTop f) = Finsupp.single χ f)
    (f : Γ((affineScheme R).left, ⊤)) (χ : Character T) :
    HasFunctionWeight a (E (a.smul.left.appTop f) χ) χ⁻¹ := by
  let := a
  let X := affineScheme R
  let S := groupRingAlgebra R (Character T)
  let Y := affineScheme S
  obtain ⟨j, _, _⟩ := torusProductChart T hT R
  let t := j.hom ≫ fst T.X X
  let x := j.hom ≫ snd T.X X
  let p := snd T.X Y
  let s := fst T.X Y
  let u := p ≫ t
  let y := p ≫ x
  let z := E (a.smul.left.appTop f)
  let l (_ : Character T) (r : Γ(X.left, ⊤)) := (actOn a t x).left.appTop r
  let r (i : Character T) (r : Γ(X.left, ⊤)) :=
    t.left.appTop (characterFunction i) * x.left.appTop r
  let d (i : Character T) (v : Γ(Y.left, ⊤)) :=
    s.left.appTop (characterFunction i) * p.left.appTop v
  have h : actOn a s (actOn a u y) = actOn a (s * u) y := (mul_smul s u y).symm
  have H := (functionExpansion_action E hE s (actOn a u y) f).symm.trans
    ((congrArg (fun g : T.X ⊗ Y ⟶ X => g.left.appTop f) h).trans
      (functionExpansion_action E hE (s * u) y f))
  have hu : actOn a u y = p ≫ actOn a t x := by
    change lift (p ≫ t) (p ≫ x) ≫ a.smul = p ≫ lift t x ≫ a.smul
    rw [comp_lift_assoc]
  obtain ⟨D, hD⟩ := projectionFunctionExpansion hT S
  have hc : l χ (z χ) = r χ (z χ) := by
    apply eq_of_weighted_sums D d hD z l r (fun _ => map_zero _) (fun _ => by simp [r]) _ χ
    change z.sum (fun i v => _ * p.left.appTop ((actOn a t x).left.appTop v)) =
      z.sum (fun i v => _ * p.left.appTop (t.left.appTop (characterFunction i) * x.left.appTop v))
    rw [hu] at H
    simp only [comp_appTop_apply, characterFunction_at_mul, map_mul, mul_assoc] at H ⊢
    exact H
  have hjx : lift t x = j.hom := by simp [t, x]
  have : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of k))).map j.hom))
  have J := (ConcreteCategory.bijective_of_isIso j.hom.left.appTop).injective
  change (actOn a t x).left.appTop (z χ) =
    t.left.appTop (characterFunction χ) * x.left.appTop (z χ) at hc
  change HasFunctionWeight a (z χ) χ⁻¹
  unfold HasFunctionWeight
  rw [inv_inv]
  apply J
  simp only [map_mul, ← comp_appTop_apply]
  have hj' : actOn a t x = j.hom ≫ a.smul := by rw [actOn, hjx]
  exact (congrArg (fun g : Y ⟶ X => g.left.appTop (z χ)) hj').symm.trans hc

set_option backward.isDefEq.respectTransparency false in
private theorem functionWeightSpace_internal {R : TestAlgebra k}
    {a : ModObj T.X (affineScheme R)} (hT : IsSplitTorus T) :
    DirectSum.IsInternal (functionWeightSpace (a := a) hT) := by
  classical
  let X := affineScheme R
  obtain ⟨E, hE⟩ := projectionFunctionExpansion hT R
  let j : Γ(X.left, ⊤) ≅ affineRing R := Scheme.ΓSpecIso (affineRing R)
  let e := (ringIsoEquiv j).toAddEquiv
  have he (w : R) : e.symm w = j.inv w := ringIsoEquiv_symm_apply j w
  let f := a.smul.left.appTop.hom.toAddMonoidHom.comp e.symm.toAddMonoidHom
  let C := (Finsupp.mapRange.addEquiv e).toAddMonoidHom.comp (E.toAddMonoidHom.comp f)
  apply internal_of_inverse_coefficients _ C
  · intro i v
    change HasFunctionWeight a (j.inv (e (E (a.smul.left.appTop (e.symm v)) i))) i⁻¹
    rw [← he, e.symm_apply_apply]
    exact functionExpansion_coefficients_weight hT E hE (e.symm v) i
  · intro v
    let z := E (a.smul.left.appTop (e.symm v))
    have H := functionExpansion_action (a := a) E hE (1 : X ⟶ T.X) (𝟙 X) (e.symm v)
    let := a
    have h : actOn a (1 : X ⟶ T.X) (𝟙 X) = 𝟙 X := one_smul (X ⟶ T.X) _
    rw [h] at H
    simp only [Over.id_left, Scheme.Hom.id_appTop, characterFunction_at_one, one_mul] at H
    have hh : z.sum (fun _ w => w) = e.symm v := H.symm
    change (Finsupp.mapRange e (map_zero e) z).sum (fun _ w => w) = v
    rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
    change (∑ i ∈ z.support, e (z i)) = v
    rw [← map_sum, show (∑ i ∈ z.support, z i) = e.symm v from hh, e.apply_symm_apply]
  · intro i v
    have hv : a.smul.left.appTop (e.symm v.val) =
        (fst T.X X).left.appTop (characterFunction i⁻¹) * (snd T.X X).left.appTop (e.symm v.val) :=
      by
        have h : HasFunctionWeight a (j.inv v.val) i := v.property
        rw [← he] at h
        exact h
    change Finsupp.mapRange e (map_zero e) (E (a.smul.left.appTop (e.symm v.val))) = _
    rw [hv, hE, Finsupp.mapRange_single, e.apply_symm_apply]

end CoordinateWeightDecomposition

section PointLinearAlgebra

attribute [local instance] Classical.decEq

variable {Λ M N : Type u} [CommGroup Λ] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N]

private def WeightGrading.mapLinearEquiv (H : WeightGrading k Λ M) (e : M ≃ₗ[k] N) :
    WeightGrading k Λ N := by
  classical
  refine ⟨fun i => (H.piece i).map e.toLinearMap, ?_⟩
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact e.toLinearMap.iSupIndep_map e.injective H.internal.submodule_iSupIndep
  · rw [← Submodule.map_iSup, H.internal.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective

private theorem weightProjection_ne (H : WeightGrading k Λ M) {i j : Λ}
    (h : i ≠ j) (v : H.piece i) : weightProject H j v = 0 := by
  change DirectSum.component k Λ (fun l => ↥(H.piece l)) j (gradingDecomposition H v) = _
  rw [gradingDecomposition_apply_of_mem H i v]
  simp [DirectSum.component.of, h]

private theorem weight_exists_nonzero [Nontrivial M] (H : WeightGrading k Λ M) :
    ∃ (χ : Λ) (v : H.piece χ), (v : M) ≠ 0 := by
  by_contra! h
  have hbot : ∀ i, H.piece i = ⊥ := by
    intro i
    rw [Submodule.eq_bot_iff]
    exact fun v hv => h i ⟨v, hv⟩
  have ht := H.internal.submodule_iSup_eq_top
  rw [show H.piece = fun _ => ⊥ from funext hbot, iSup_bot] at ht
  exact bot_ne_top ht

private theorem internal_of_graded_retract (H : WeightGrading k Λ M) (S : Submodule k M)
    (p : M →ₗ[k] S) (hp : Function.Surjective p)
    (hw : ∀ i (v : M), v ∈ H.piece i → (p v : M) ∈ H.piece i) :
    DirectSum.IsInternal (fun i => (H.piece i).comap S.subtype) := by
  classical
  let A := fun i => (H.piece i).comap S.subtype
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · intro i
    rw [Submodule.disjoint_def]
    intro x hxi hx
    apply Subtype.val_injective
    apply Submodule.disjoint_def.mp (H.internal.submodule_iSupIndep i) x.val hxi
    have hmap : (⨆ j, ⨆ (_ : j ≠ i), A j).map S.subtype ≤ ⨆ j, ⨆ (_ : j ≠ i), H.piece j := by
      simp only [Submodule.map_iSup, iSup_le_iff]
      intro j h v hv
      rcases hv with ⟨w, hw, rfl⟩
      exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem h hw)
    exact hmap (Submodule.mem_map_of_mem hx)
  · apply top_unique
    calc
      ⊤ = (⊤ : Submodule k M).map p := (Submodule.map_top p).trans
        (LinearMap.range_eq_top.mpr hp) |>.symm
      _ = ⨆ i, (H.piece i).map p := by rw [← H.internal.submodule_iSup_eq_top, Submodule.map_iSup]
      _ ≤ ⨆ i, A i := by
        apply iSup_mono
        intro i v hv
        rcases hv with ⟨w, hw', rfl⟩
        exact hw i w hw'

private def removeLine (H : WeightGrading k Λ M) (χ : Λ) (v : H.piece χ)
    (l : H.piece χ →ₗ[k] k) :
    M →ₗ[k] M :=
  LinearMap.id - (LinearMap.toSpanSingleton k M v.val).comp (l.comp (weightProject H χ))

private theorem removeLine_preserves (H : WeightGrading k Λ M) (χ : Λ) (v : H.piece χ)
    (l : H.piece χ →ₗ[k] k) (i : Λ) (x : M) (hx : x ∈ H.piece i) :
    removeLine H χ v l x ∈ H.piece i := by
  by_cases hi : i = χ
  · subst i
    exact (H.piece χ).sub_mem hx ((H.piece χ).smul_mem _ v.property)
  · have h := weightProjection_ne H hi (⟨x, hx⟩ : H.piece i)
    change x - l (weightProject H χ x) • v.val ∈ H.piece i
    rwa [show weightProject H χ x = 0 from h, map_zero, zero_smul, sub_zero]

end PointLinearAlgebra

section InvariantOpenImmersions

variable {T : GroupScheme k} {X Y : SchemeOver k}

set_option backward.isDefEq.respectTransparency false in
/-- An invariant open immersion presents the restricted action on its source. -/
theorem invariantOpenImmersionAction (a : ModObj T.X X) (f : Y ⟶ X)
    [IsOpenImmersion f.left]
    (h : a.smul.left ⁻¹ᵁ f.left.opensRange = (snd T.X X).left ⁻¹ᵁ f.left.opensRange) :
    ∃ b : ModObj T.X Y, IsEquivariantMap a b f := by
  let g := (T.X ◁ f) ≫ a.smul
  have hr : Set.range g.left ⊆ Set.range f.left := by
    rintro _ ⟨z, rfl⟩
    change (T.X ◁ f).left z ∈ a.smul.left ⁻¹ᵁ f.left.opensRange
    rw [h]
    change (snd T.X X).left ((T.X ◁ f).left z) ∈ Set.range f.left
    have h' : (T.X ◁ f) ≫ snd T.X X = snd T.X Y ≫ f := by simp
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h', Over.comp_left, Scheme.Hom.comp_apply]
    exact ⟨(snd T.X Y).left z, rfl⟩
  let m : T.X ⊗ Y ⟶ Y := Over.homMk (IsOpenImmersion.lift f.left g.left hr) (by
    rw [← Over.w f, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w g)
  have hm : m ≫ f = (T.X ◁ f) ≫ a.smul :=
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have : Mono f := Over.mono_of_mono_left _
  exact ⟨actionOfMono a f m hm, hm.trans (by rw [id_tensorHom])⟩

set_option backward.isDefEq.respectTransparency false in
/-- The spectrum of the localization at a homogeneous function has the
restricted action and its map to the original affine scheme is equivariant. -/
theorem homogeneousLocalizationAction {R : TestAlgebra k} (r : R)
    (a : ModObj T.X (affineScheme R)) {χ : Character T}
    (h : HasFunctionWeight a ((Scheme.ΓSpecIso (affineRing R)).inv r) χ) :
    let S : TestAlgebra k := .of k (Localization.Away r)
    let φ : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Localization.Away r))
    let f := (testSpec k).map φ.op
    ∃ b : ModObj T.X (affineScheme S), IsEquivariantMap a b f := by
  intro S φ f
  let j : Spec (affineRing S) ⟶ Spec (affineRing R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  have hj : f.left = j := rfl
  have : IsOpenImmersion f.left := by rw [hj]; infer_instance
  apply invariantOpenImmersionAction a f
  have hU : f.left.opensRange = (affineScheme R).left.basicOpen
      ((Scheme.ΓSpecIso (affineRing R)).inv r) := by
    change j.opensRange = (Spec (affineRing R)).basicOpen ((Scheme.ΓSpecIso (affineRing R)).inv r)
    rw [basicOpen_eq_of_affine]
    exact Scheme.Hom.opensRange_localizationAway (R := affineRing R) r
  rw [hU]
  exact basicOpen_invariant_of_weight _ _ h

end InvariantOpenImmersions

section PointSheafClasses

attribute [local instance] Classical.decEq

variable {T : GroupScheme k}

section

variable {R : CommRingCat.{u}} {F H : (Spec R).Modules}

local notation "Sect" => moduleSpecΓFunctor (R := R)

private theorem sections_homEquiv (f : F ⟶ H) :
    (tilde.adjunction (R := R)).homEquiv ((Sect).obj F) H (F.fromTildeΓ ≫ f) = (Sect).map f := by
  let D := tilde.adjunction (R := R)
  have h : D.homEquiv ((Sect).obj F) F (D.counit.app F) = 𝟙 _ := by
    rw [← D.homEquiv_symm_id, Equiv.apply_symm_apply]
  change D.homEquiv _ _ (D.counit.app F ≫ f) = _
  rw [Adjunction.homEquiv_naturality_right]
  exact (congrArg (fun j => j ≫ (Sect).map f) h).trans (Category.id_comp _)

private def mapFromSections [F.IsQuasicoherent]
    (f : (Sect).obj F ⟶ (Sect).obj H) : F ⟶ H :=
  (asIso F.fromTildeΓ).inv ≫ ((tilde.adjunction (R := R)).homEquiv _ _).symm f

private theorem mapFromSections_app [F.IsQuasicoherent]
    (f : (Sect).obj F ⟶ (Sect).obj H) :
    (Sect).map (mapFromSections f) = f := by
  let D := tilde.adjunction (R := R)
  let e := asIso F.fromTildeΓ
  have h : F.fromTildeΓ ≫ mapFromSections f = (D.homEquiv ((Sect).obj F) H).symm f :=
    e.hom_inv_id_assoc _
  let e' := D.homEquiv ((Sect).obj F) H
  exact (sections_homEquiv (mapFromSections f)).symm.trans
    ((congrArg e' h).trans (e'.apply_symm_apply f))

private theorem sections_faithful [F.IsQuasicoherent] {f g : F ⟶ H}
    (h : (Sect).map f = (Sect).map g) : f = g := by
  rw [← sections_homEquiv f, ← sections_homEquiv g] at h
  exact (cancel_epi F.fromTildeΓ).mp (((tilde.adjunction (R := R)).homEquiv _ _).injective h)

end

private theorem classOf_twist {R : TestAlgebra k} {a : ModObj T.X (affineScheme R)}
    {F H : EquivariantCoherent a} {χ : Character T}
    (h : IsTwist χ F H) : classOf H = eChar χ • classOf F := by
  have hr : Finsupp.single H 1 - eChar χ • Finsupp.single F 1 ∈ relationSubmodule a :=
    Submodule.subset_span (Or.inr ⟨χ, F, H, h, rfl⟩)
  have he := (Submodule.Quotient.mk_eq_zero (p := relationSubmodule a)).mpr hr
  change (relationSubmodule a).mkQ _ = 0 at he
  simpa only [map_sub, map_smul, classOf, sub_eq_zero] using he

set_option backward.isDefEq.respectTransparency false in
private theorem trivialWeight_one {X : SchemeOver k} (hT : IsSplitTorus T)
    (F : X.left.Modules) (v : Γ(F, ⊤)) :
    HasSectionWeight (trivialLinearization T F) v 1 := by
  let p := snd T.X X
  let I : Pull p F ⟶ Pull p F := 𝟙 _
  change I.app ⊤ (pullSection p.left F v) =
    (fst T.X X).left.appTop (characterFunction (1 : Character T)) •
      pullSection (snd T.X X).left F v
  rw [characterFunction_one hT, map_one, one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pointLine_hasWeight (hT : IsSplitTorus T) (χ : Character T)
    (v : Γ((trivialPointLine T).sheaf, ⊤)) :
    HasSectionWeight (twistCoherent (trivialPointLine T) χ).lin v χ := by
  let F := trivialPointLine T
  have h₁ : HasSectionWeight F.lin v 1 := trivialWeight_one hT F.sheaf v
  have h₂ := (sectionWeight_twist hT F.lin (twistCoherent F χ).lin χ 1 v
    (twistLinearizationIso_hom χ F.lin.iso)).mpr h₁
  change HasSectionWeight (twistLinearization F.lin χ) v χ
  change HasSectionWeight (twistLinearization F.lin χ) v (χ * 1) at h₂
  simpa only [mul_one] using h₂

private def pointModuleGrading {G : AffineGrading (pointRing k) (pointAction T)}
    (hT : IsSplitTorus T) {F : (affineScheme (pointRing k)).left.Modules}
    (H : WeightGrading k (Character T) (sectionsModule F)) : ModuleGrading G.val (sectionsModule F) where
  toWeightGrading := H
  smul_mem := by
    intro i j r v hr hv
    by_cases hi : i = 1
    · subst i
      rw [one_mul]
      exact (H.piece j).smul_mem r hv
    · have hm : G.val.piece 1 = ⊤ := by
        apply Submodule.eq_top_iff'.mpr
        intro w
        exact (G.property 1 w).mpr (baseScalar_functionWeight hT w)
      have hd := G.val.internal.submodule_iSupIndep.pairwiseDisjoint hi
      change Disjoint (G.val.piece i) (G.val.piece 1) at hd
      rw [hm, disjoint_top] at hd
      have hz : r = 0 := by rwa [hd, Submodule.mem_bot] at hr
      rw [hz, zero_smul]
      exact (H.piece (i * j)).zero_mem

set_option maxHeartbeats 350000 in
set_option backward.isDefEq.respectTransparency false in
private theorem splitPointSheaf (hT : IsSplitTorus T)
    (G : AffineGrading (pointRing k) (pointAction T))
    (E : AffineModuleComparison (pointRing k) (pointAction T) G)
    (hE : ∀ (F : (affineScheme (pointRing k)).left.Modules) (hF : F.IsQuasicoherent)
      (L : Linearization (pointAction T) F) χ v, v ∈ (E F hF L).piece χ ↔ HasSectionWeight L v χ)
    (F : EquivariantCoherent (pointAction T))
    (hn : Module.finrank k (sectionsModule F.sheaf) ≠ 0) :
    ∃ (K : EquivariantCoherent (pointAction T)) (χ : Character T)
      (i : K.sheaf ⟶ F.sheaf) (q : F.sheaf ⟶ (twistCoherent (trivialPointLine T) χ).sheaf)
      (w : i ≫ q = 0),
      EquivariantHom i ∧ EquivariantHom q ∧ (ShortComplex.mk i q w).ShortExact ∧
        Module.finrank k (sectionsModule K.sheaf) < Module.finrank k (sectionsModule F.sheaf) := by
  classical
  let R := pointRing k
  let M := sectionsModule F.sheaf
  let : Module.Finite k M := finite_sections_at_point F
  have : Nontrivial M := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
  let hF := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let := hF
  let H := (E F.sheaf hF F.lin).toWeightGrading
  obtain ⟨χ, v, hv⟩ := weight_exists_nonzero H
  have hv' : v ≠ 0 := fun h => hv (congrArg Subtype.val h)
  obtain ⟨l, hl₀⟩ := (LinearMap.toSpanSingleton k (H.piece χ) v).exists_leftInverse_of_injective
    (LinearMap.ker_toSpanSingleton k hv')
  have hl : l v = 1 := by
    have h := LinearMap.congr_fun hl₀ 1
    simpa only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply_one, LinearMap.id_apply] using h
  let j : k →ₗ[k] M := LinearMap.toSpanSingleton k M v.val
  let q₀ : M →ₗ[k] k := l.comp (weightProject H χ)
  have hqj : q₀.comp j = LinearMap.id := by
    ext
    change l (weightProject H χ (j 1)) = 1
    rw [LinearMap.toSpanSingleton_apply_one, weightProject_of_mem, hl]
  have hqj' (c : k) : q₀ (j c) = c := LinearMap.congr_fun hqj c
  let S := LinearMap.ker q₀
  let p₀ : M →ₗ[k] S := (removeLine H χ v l).codRestrict S fun x => by
    show q₀ (x - j (q₀ x)) = 0
    rw [map_sub, hqj', sub_self]
  have hp₀ (x : S) : p₀ x.val = x := by
    apply Subtype.val_injective
    change x.val - j (q₀ x.val) = x.val
    rw [show q₀ x.val = 0 from x.property, map_zero, sub_zero]
  let H₀ : WeightGrading k (Character T) S :=
    ⟨fun i => (H.piece i).comap S.subtype,
      internal_of_graded_retract H S p₀ (fun x => ⟨x.val, hp₀ x⟩) (removeLine_preserves H χ v l)⟩
  let B : ModuleCat.{u} k := ModuleCat.of k S
  let L := twistCoherent (trivialPointLine T) χ
  let F₀ := tilde (R := affineRing R) B
  let hF₀ : F₀.IsQuasicoherent := inferInstance
  let e := (tilde.isoTop (R := affineRing R) B).toLinearEquiv
  let g := pointModuleGrading (G := G) hT (WeightGrading.mapLinearEquiv H₀ e)
  let K : EquivariantCoherent (pointAction T) :=
    ⟨F₀, finitePresentation_tilde (R := affineRing R) B, (E F₀ hF₀).symm g⟩
  let b := (tilde.isoTop (R := affineRing R) (ModuleCat.of k k)).toLinearEquiv
  let i' := S.subtype.comp e.symm.toLinearMap
  let p' := e.toLinearMap.comp p₀
  let q' := b.toLinearMap.comp q₀
  let j' := j.comp b.symm.toLinearMap
  let hL := L.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let := hL
  let : K.sheaf.IsQuasicoherent := hF₀
  let A := affineSections R
  let : A.Additive := ⟨fun {_ _} _ _ => rfl⟩
  let i₀ : A.obj K.sheaf ⟶ A.obj F.sheaf :=
    ConcreteCategory.ofHom (C := ModuleCat k) (X := A.obj K.sheaf) (Y := A.obj F.sheaf) i'
  let p₁ : A.obj F.sheaf ⟶ A.obj K.sheaf :=
    ConcreteCategory.ofHom (C := ModuleCat k) (X := A.obj F.sheaf) (Y := A.obj K.sheaf) p'
  let q₁ : A.obj F.sheaf ⟶ A.obj L.sheaf :=
    ConcreteCategory.ofHom (C := ModuleCat k) (X := A.obj F.sheaf) (Y := A.obj L.sheaf) q'
  let j₂ : A.obj L.sheaf ⟶ A.obj F.sheaf :=
    ConcreteCategory.ofHom (C := ModuleCat k) (X := A.obj L.sheaf) (Y := A.obj F.sheaf) j'
  let i : K.sheaf ⟶ F.sheaf := @mapFromSections (affineRing R) K.sheaf F.sheaf hF₀ i₀
  let p : F.sheaf ⟶ K.sheaf := @mapFromSections (affineRing R) F.sheaf K.sheaf hF p₁
  let q : F.sheaf ⟶ L.sheaf := @mapFromSections (affineRing R) F.sheaf L.sheaf hF q₁
  let j₁ : L.sheaf ⟶ F.sheaf := @mapFromSections (affineRing R) L.sheaf F.sheaf hL j₂
  have hi : A.map i = i₀ := @mapFromSections_app (affineRing R) K.sheaf F.sheaf hF₀ i₀
  have hp : A.map p = p₁ := @mapFromSections_app (affineRing R) F.sheaf K.sheaf hF p₁
  have hq : A.map q = q₁ := @mapFromSections_app (affineRing R) F.sheaf L.sheaf hF q₁
  have hj : A.map j₁ = j₂ := @mapFromSections_app (affineRing R) L.sheaf F.sheaf hL j₂
  have hz : i ≫ q = 0 := by
    apply sections_faithful (R := affineRing R)
    change A.map (i ≫ q) = A.map 0
    rw [A.map_comp, A.map_zero, hi, hq]
    ext x
    change b (q₀ (e.symm x).val) = 0
    rw [show q₀ (e.symm x).val = 0 from (e.symm x).property, map_zero]
  let C := ShortComplex.mk i q hz
  have hC : C.ShortExact := ShortComplex.Splitting.shortExact
    { r := p
      s := j₁
      f_r := by
        change i ≫ p = 𝟙 _
        apply sections_faithful (R := affineRing R)
        change A.map (i ≫ p) = A.map (𝟙 _)
        rw [A.map_comp, A.map_id, hi, hp]
        ext x
        change e (p₀ (e.symm x).val) = x
        rw [hp₀, e.apply_symm_apply]
      s_g := by
        change j₁ ≫ q = 𝟙 _
        apply sections_faithful (R := affineRing R)
        change A.map (j₁ ≫ q) = A.map (𝟙 _)
        rw [A.map_comp, A.map_id, hj, hq]
        ext x
        change b (q₀ (j (b.symm x))) = x
        rw [hqj', b.apply_symm_apply]
      id := by
        change p ≫ i + q ≫ j₁ = 𝟙 _
        apply sections_faithful (R := affineRing R)
        change A.map (p ≫ i + q ≫ j₁) = A.map (𝟙 _)
        rw [A.map_add, A.map_comp, A.map_comp, A.map_id, hi, hp, hq, hj]
        ext x
        change (e.symm (e (p₀ x))).val + j (b.symm (b (q₀ x))) = x
        rw [e.symm_apply_apply, b.symm_apply_apply]
        exact sub_add_cancel _ _ }
  refine ⟨K, χ, i, q, hz, ?_, ?_, hC, ?_⟩
  · have he : E F₀ hF₀ K.lin = g := (E F₀ hF₀).apply_symm_apply g
    have hK (d : Character T) (x : sectionsModule K.sheaf) :
        x ∈ g.piece d ↔ HasSectionWeight K.lin x d := by
      rw [← he]
      exact hE F₀ hF₀ K.lin d x
    apply (isLinearizedMap_iff_preserves_weight_of_internal K.lin F.lin g.toWeightGrading hK i).mpr
    intro d x hx
    apply (hE F.sheaf hF F.lin d _).mp
    change A.map i x ∈ H.piece d
    rw [hi]
    obtain ⟨y, hy, rfl⟩ := (show x ∈ (H₀.piece d).map e.toLinearMap from (hK d x).mpr hx)
    change (e.symm (e y)).val ∈ H.piece d
    rwa [e.symm_apply_apply]
  · apply (isLinearizedMap_iff_preserves_weight_of_internal F.lin L.lin H (hE F.sheaf hF F.lin) q).mpr
    intro d x hx
    by_cases hd : d = χ
    · subst d
      exact pointLine_hasWeight hT χ _
    · change HasSectionWeight L.lin (A.map q x) d
      rw [hq]
      have h₀ := weightProjection_ne H hd ⟨x, (hE F.sheaf hF F.lin d x).mpr hx⟩
      have hq₀ : q₀ x = 0 := by
        change l (weightProject H χ x) = 0
        rw [show weightProject H χ x = 0 from h₀, map_zero]
      change HasSectionWeight L.lin (b (q₀ x)) d
      rw [hq₀, map_zero]
      exact (sectionWeightSpace hT L.lin d).zero_mem
  · change Module.finrank k (sectionsModule F₀) < Module.finrank k M
    have hh : Module.finrank k S = Module.finrank k (sectionsModule F₀) := e.finrank_eq
    have hdim := LinearMap.finrank_range_add_finrank_ker q₀
    rw [LinearMap.range_eq_top.mpr (fun y => ⟨j y, hqj' y⟩), finrank_top, Module.finrank_self] at hdim
    change 1 + Module.finrank k S = Module.finrank k M at hdim
    exact hh.symm.trans_lt (by omega)

end PointSheafClasses

section PointCharacterIsomorphism

variable {T : GroupScheme k}

private theorem pointCharacterMap_injective (hT : IsSplitTorus T)
    (G : AffineGrading (pointRing k) (pointAction T))
    (E : AffineModuleComparison (pointRing k) (pointAction T) G)
    (hE : ∀ (F : (affineScheme (pointRing k)).left.Modules) (hF : F.IsQuasicoherent)
      (L : Linearization (pointAction T) F) χ v, v ∈ (E F hF L).piece χ ↔ HasSectionWeight L v χ) :
    let A (F : EquivariantCoherent (pointAction T)) := (E F.sheaf
      F.coherent.exists_quasicoherentData.choose.isQuasicoherent F.lin).toWeightGrading
    Function.Injective (pointCharacterMap hT A (fun F => hE F.sheaf _ F.lin)) := by
  intro A
  let hA : ∀ F χ v, v ∈ (A F).piece χ ↔ HasSectionWeight F.lin v χ :=
    fun F => hE F.sheaf _ F.lin
  let C := pointCharacterMap hT A hA
  let e₀ := classOf (trivialPointLine T)
  let j := LinearMap.toSpanSingleton (CharacterRing T) (GZero (pointAction T)) e₀
  have he (F : EquivariantCoherent (pointAction T)) : C (classOf F) • e₀ = classOf F := by
    generalize hn : Module.finrank k (sectionsModule F.sheaf) = n
    induction n using Nat.strong_induction_on generalizing F with
    | h n ih =>
      by_cases hz : n = 0
      · let := finite_sections_at_point F
        let := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
        have hM : Subsingleton (sectionsModule F.sheaf) :=
          Module.finrank_zero_iff.mp (hn.trans hz)
        have hF : IsZero F.sheaf := by
          let R := pointRing k
          let S := affineSections R
          let hq := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
          let : S.Additive := ⟨fun {_ _} _ _ => rfl⟩
          apply (IsZero.iff_id_eq_zero _).mpr
          apply @sections_faithful (affineRing R) F.sheaf F.sheaf hq
          change S.map (𝟙 F.sheaf) = S.map 0
          rw [S.map_id, S.map_zero]
          exact (IsZero.iff_id_eq_zero _).mp (ModuleCat.isZero_iff_subsingleton.mpr hM)
        rw [classOf_isZero F hF, map_zero, zero_smul]
      · obtain ⟨K, χ, i, q, w, hi, hq, hex, hdim⟩ := splitPointSheaf hT G E hE F ((fun h => hz (hn.symm.trans h)))
        let L := twistCoherent (trivialPointLine T) χ
        have hclass : classOf F = classOf K + classOf L := classOf_exact w hi hq hex
        have hL : classOf L = eChar χ • e₀ := classOf_twist (twistCoherent_isTwist _ χ)
        have hcL : C (classOf L) • e₀ = classOf L := by
          rw [hL, map_smul]
          change (eChar χ • pointCharacterMap hT A hA (classOf (trivialPointLine T))) • e₀ = _
          rw [pointCharacterMap_trivial, smul_eq_mul, mul_one]
        have hK := ih _ (hdim.trans_le (le_of_eq hn)) K rfl
        rw [hclass, map_add, add_smul, hK, hcL]
  have h : j.comp C = LinearMap.id := by
    apply classMap_ext
    exact he
  have hleft : Function.LeftInverse j C := fun x => DFunLike.congr_fun h x
  exact hleft.injective

set_option backward.isDefEq.respectTransparency false in
theorem pointCharacterComparison_of_affineComparison
    (ha : EquivariantAffineComparison.{u}) : PointCharacterComparison.{u} := by
  intro k _ T hT R a
  obtain ⟨G, E, hE, _, _⟩ := ha hT R a
  let A (F : EquivariantCoherent a) :=
    (E F.sheaf F.coherent.exists_quasicoherentData.choose.isQuasicoherent F.lin).toWeightGrading
  have hA (F : EquivariantCoherent a) : ∀ χ v, v ∈ (A F).piece χ ↔ HasSectionWeight F.lin v χ :=
    (hE F.sheaf _).2 F.lin
  let C := pointCharacterMap hT A hA
  let e := LinearEquiv.ofBijective C
    ⟨pointCharacterMap_injective hT G E (fun F hF => (hE F hF).2),
      pointCharacterMap_surjective hT A hA⟩
  refine ⟨G, E, e, hA, ?_, ?_, ?_⟩
  · exact pointCharacterMap_classOf hT A hA
  · intro F i hF
    change pointCharacterMap hT A hA (classOf F) = 1
    unfold pointCharacterMap
    rw [liftClassMap_classOf]
    exact pointSheafCharacter_of_trivial_line hT F (A F) (hA F) i hF
  · intro F H K f g w hf hg hex
    rw [classOf_exact w hf hg hex, map_add]

end PointCharacterIsomorphism

section InverseTransportBaseChange

variable {T : GroupScheme k} {X Y Z : SchemeOver k} {a : ModObj T.X X}
    {F : X.left.Modules}
set_option backward.isDefEq.respectTransparency false in
private theorem inverseTransport_baseChange (L : Linearization a F)
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤)))
    (hE : ∀ χ v, E ((fst T.X X).left.appTop (characterFunction χ) •
      pullSection (snd T.X X).left F v) = Finsupp.single χ v)
    (p : Z ⟶ Y) (t : Y ⟶ T.X) (x : Y ⟶ X) (v : Γ(F, ⊤)) :
    (transport a L.iso (p ≫ t) (p ≫ x)).inv.app ⊤
      (pullSection (actOn a (p ≫ t) (p ≫ x)).left F v) =
    (pullComp F p x).hom.app ⊤
      (pullSection p.left (Pull x F) ((transport a L.iso t x).inv.app ⊤
        (pullSection (actOn a t x).left F v))) := by
  rw [inverseTransport_expansion L E hE (p ≫ t) (p ≫ x) v,
    inverseTransport_expansion L E hE t x v]
  let C := ((pullComp F p x).hom.app ⊤).hom.comp (pullSectionAdd p.left (Pull x F))
  let z := E (L.iso.inv.app ⊤ (pullSection a.smul.left F v))
  change (∑ χ ∈ z.support, (p ≫ t).left.appTop (characterFunction χ) •
      pullSection (p ≫ x).left F (z χ)) =
    C (∑ χ ∈ z.support, t.left.appTop (characterFunction χ) • pullSection x.left F (z χ))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [comp_appTop_apply]
  exact (comparePull_section_smul F p x rfl _ _).symm


end InverseTransportBaseChange

section SectionCoefficientExtraction

variable {T : GroupScheme k} {X Z : SchemeOver k} {a : ModObj T.X X} {F : X.left.Modules}

private def InverseCoefficientMultiplication (L : Linearization a F)
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤))) : Prop :=
  ∀ (Z : SchemeOver k) (s t : Z ⟶ T.X) (x : Z ⟶ X) (v : Γ(F, ⊤)),
    let z := E (L.iso.inv.app ⊤ (pullSection a.smul.left F v))
    z.sum (fun χ w => s.left.appTop (characterFunction χ) •
      (transport a L.iso t x).inv.app ⊤ (pullSection (actOn a t x).left F w)) =
    z.sum (fun χ w => s.left.appTop (characterFunction χ) •
      (t.left.appTop (characterFunction χ) • pullSection x.left F w))

section InverseComposition

private theorem inverse_of_comp_iso {C : Type*} [Category C] {A B D E : C}
    (e₁ : A ≅ B) (e₂ : B ≅ D) (e₃ : D ≅ E) (e₄ : A ≅ E)
    (h : ComposesTo e₁.hom e₂.hom e₃.hom e₄.hom) :
    ComposesTo e₃.inv e₂.inv e₁.inv e₄.inv := by
  have H : e₁ ≪≫ e₂ ≪≫ e₃ = e₄ := Iso.ext h
  simpa only [ComposesTo, Iso.trans_inv, Category.assoc] using congrArg Iso.inv H

private theorem inverseTransport_cocycle (L : Linearization a F)
    (s t : Z ⟶ T.X) (x : Z ⟶ X)
    (h : actOn a s (actOn a t x) = actOn a (s * t) x) :
    ComposesTo (pullCongr F h).inv (transport a L.iso s (actOn a t x)).inv
      (transport a L.iso t x).inv (transport a L.iso (s * t) x).inv := by
  have hL : TransportComposition L.iso s t x h := (L.mul Z s t x).choose_spec
  exact @inverse_of_comp_iso Z.left.Modules _ (Pull x F) (Pull (actOn a t x) F)
    (Pull (actOn a s (actOn a t x)) F) (Pull (actOn a (s * t) x) F)
    (transport a L.iso t x) (transport a L.iso s (actOn a t x)) (pullCongr F h)
    (transport a L.iso (s * t) x) hL

/-- Evaluation of a module sheaf on the whole scheme. -/
private def topModuleFunctor (Z : Scheme.{u}) : Z.Modules ⥤ ModuleCat Γ(Z, ⊤) where
  obj F := F.val.obj (op ⊤)
  map f := f.val.app (op ⊤)
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem comp_three_apply {C : Type*} [Category C] {R : Type u} [Ring R]
    (S : C ⥤ ModuleCat.{u} R)
    {A B D E : C} {f : A ⟶ B} {g : B ⟶ D} {h : D ⟶ E} {j : A ⟶ E}
    (p : ComposesTo f g h j) (v : S.obj A) (w : S.obj B) (hfw : S.map f v = w) :
    S.map h (S.map g w) = S.map j v := by
  have e := congrArg S.map (show f ≫ g ≫ h = j from p)
  rw [S.map_comp, S.map_comp] at e
  simpa only [ModuleCat.comp_apply, hfw] using ConcreteCategory.congr_hom e v

private def inverseTransportOnTop (L : Linearization a F) (t : Z ⟶ T.X) (x : Z ⟶ X) :
    (topModuleFunctor Z.left).obj (Pull (actOn a t x) F) ⟶
      (topModuleFunctor Z.left).obj (Pull x F) :=
  (topModuleFunctor Z.left).map (transport a L.iso t x).inv

private def pulledTopSection (F : X.left.Modules) (x : Z ⟶ X) :
    Γ(F, ⊤) → (topModuleFunctor Z.left).obj (Pull x F) :=
  pullSection x.left F

private theorem inverseSectionCongr (F : X.left.Modules) {x y : Z ⟶ X} (p : x = y)
    (v : Γ(F, ⊤)) :
    (topModuleFunctor Z.left).map (pullCongr F p).inv (pulledTopSection F y v) =
      pulledTopSection F x v := by
  subst y
  rfl

private theorem inverseTransport_comp_top (L : Linearization a F)
    (s t : Z ⟶ T.X) (x : Z ⟶ X) (v : Γ(F, ⊤)) :
    inverseTransportOnTop L t x (inverseTransportOnTop L s (actOn a t x)
      (pulledTopSection F (actOn a s (actOn a t x)) v)) =
      inverseTransportOnTop L (s * t) x (pulledTopSection F (actOn a (s * t) x) v) := by
  let p := (L.mul Z s t x).choose
  exact comp_three_apply (topModuleFunctor Z.left)
    (inverseTransport_cocycle L s t x p) _ _ (inverseSectionCongr F p v)

private def weightedSum {Λ A V : Type u} [Ring A] [Zero V] {M : ModuleCat.{u} A}
    (z : Λ →₀ V) (c : Λ → A) (w : Λ → V → M) : M :=
  z.sum fun i v => c i • w i v

private theorem weightedSum_of_composition {Λ A V : Type u} [Ring A] [Zero V]
    {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (z : Λ →₀ V) (c d e : Λ → A) (w : V → M) (q : V → N) (l : M) (r : N)
    (hl : l = weightedSum z c (fun _ => w))
    (hr : r = weightedSum z e (fun _ => q))
    (h : f l = r) (he : ∀ i, e i = c i * d i) :
    weightedSum z c (fun _ v => f (w v)) = weightedSum z c (fun i v => d i • q v) := by
  rw [hl, hr] at h
  simpa only [weightedSum, Finsupp.sum, he, map_sum, map_smul, mul_smul] using h

private def sectionCoefficients (L : Linearization a F)
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤))) (v : Γ(F, ⊤)) :
    Character T →₀ Γ(F, ⊤) :=
  E (L.iso.inv.app ⊤ (pullSection a.smul.left F v))

private def characterValue (t : Z ⟶ T.X) (χ : Character T) : Γ(Z.left, ⊤) :=
  t.left.appTop (characterFunction χ)

private def ProjectionExpansion (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤))) :
    Prop :=
  ∀ χ v, E ((fst T.X X).left.appTop (characterFunction χ) •
    pullSection (snd T.X X).left F v) = Finsupp.single χ v

set_option backward.isDefEq.respectTransparency false in
private theorem inverseTop_weightedSum (L : Linearization a F)
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤)))
    (hE : ProjectionExpansion E)
    (t : Z ⟶ T.X) (x : Z ⟶ X) (v : Γ(F, ⊤)) :
    inverseTransportOnTop L t x (pulledTopSection F (actOn a t x) v) =
      weightedSum (sectionCoefficients L E v) (characterValue t) (fun _ => pulledTopSection F x) :=
  inverseTransport_expansion L E hE t x v

private def InverseTransportWeightedSums (L : Linearization a F)
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤))) : Prop :=
  ∀ (Z : SchemeOver k) (s t : Z ⟶ T.X) (x : Z ⟶ X) (v : Γ(F, ⊤)),
    weightedSum (sectionCoefficients L E v) (characterValue s)
      (fun _ w => inverseTransportOnTop L t x (pulledTopSection F (actOn a t x) w)) =
    weightedSum (sectionCoefficients L E v) (characterValue s)
      (fun χ w => characterValue t χ • pulledTopSection F x w)

set_option maxHeartbeats 150000 in
set_option backward.isDefEq.respectTransparency false in
/-- Expand the two sides of the inverse cocycle and use the character
multiplication law in the resulting finite sums. -/
private theorem inverseTransport_weightedSums (L : Linearization a F)
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤)))
    (hE : ProjectionExpansion E) : InverseTransportWeightedSums L E := by
  intro Z s t x v
  exact weightedSum_of_composition (inverseTransportOnTop L t x)
    (sectionCoefficients L E v) (characterValue s) (characterValue t) (characterValue (s * t))
    (pulledTopSection F (actOn a t x)) (pulledTopSection F x) _ _
    (inverseTop_weightedSum L E hE s (actOn a t x) v) (inverseTop_weightedSum L E hE (s * t) x v)
    (inverseTransport_comp_top L s t x v) (fun i => characterFunction_at_mul i s t)

private theorem sum_equal_of_weightedSum_equal {Λ V : Type u} [Zero V]
    {S : Scheme.{u}} {P Q : S.Modules} (f : P ⟶ Q)
    (z : Λ →₀ V) (c d : Λ → Γ(S, ⊤)) (w : V → Γ(P, ⊤)) (q : V → Γ(Q, ⊤))
    (h : weightedSum (M := (topModuleFunctor S).obj Q) z c
          (fun _ v => (topModuleFunctor S).map f (w v)) =
        weightedSum (M := (topModuleFunctor S).obj Q) z c (fun i v => d i • q v)) :
    z.sum (fun i v => c i • f.app ⊤ (w v)) = z.sum (fun i v => c i • (d i • q v)) :=
  h

set_option maxHeartbeats 115000 in
set_option backward.isDefEq.respectTransparency false in
private theorem inverseCoefficientComposition (L : Linearization a F)
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤)))
    (hE : ProjectionExpansion E) : InverseCoefficientMultiplication L E := by
  intro Z s t x v z
  exact @sum_equal_of_weightedSum_equal (Character T) Γ(F, ⊤) _ Z.left
    (Pull (actOn a t x) F) (Pull x F) (transport a L.iso t x).inv
    z (characterValue s) (characterValue t)
    (pullSection (actOn a t x).left F) (pullSection x.left F)
    (inverseTransport_weightedSums L E hE Z s t x v)

end InverseComposition

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem inverseTransport_coefficients_weight
    {R : TestAlgebra k} {a : ModObj T.X (affineScheme R)} {F : (affineScheme R).left.Modules}
    [F.IsQuasicoherent] (hT : IsSplitTorus T) (L : Linearization a F)
    (E : Γ(Pull (snd T.X (affineScheme R)) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤)))
    (hE : ∀ χ v, E ((fst T.X (affineScheme R)).left.appTop (characterFunction χ) •
      pullSection (snd T.X (affineScheme R)).left F v) = Finsupp.single χ v)
    (hmul : InverseCoefficientMultiplication L E)
    (v : Γ(F, ⊤)) (χ : Character T) :
    HasSectionWeight L (E (L.iso.inv.app ⊤ (pullSection a.smul.left F v)) χ) χ⁻¹ := by
  let X := affineScheme R
  let S := groupRingAlgebra R (Character T)
  let Y := affineScheme S
  obtain ⟨j, hj, _⟩ := torusProductChart T hT R
  let t := j.hom ≫ fst T.X X
  let x := j.hom ≫ snd T.X X
  let P := Pull x F
  have : P.IsQuasicoherent := by
    change (Pull (j.hom ≫ snd T.X X) F).IsQuasicoherent
    rw [hj]
    exact pullback_spec_isQuasicoherent (CommRingCat.ofHom (groupRingConstants R (Character T)).hom.toRingHom) F
  obtain ⟨D, hD⟩ := projectionSectionExpansion hT S P
  let p := snd T.X Y
  let s := fst T.X Y
  let c (i : Character T) := s.left.appTop (characterFunction i)
  let d (i : Character T) (w : Γ(P, ⊤)) := c i • pullSection p.left P w
  let l (_ : Character T) (w : Γ(F, ⊤)) : Γ(P, ⊤) :=
    (transport a L.iso t x).inv.app ⊤ (pullSection (actOn a t x).left F w)
  let r (i : Character T) (w : Γ(F, ⊤)) : Γ(P, ⊤) :=
    t.left.appTop (characterFunction i) • pullSection x.left F w
  let B := (pullComp F p x).hom.app ⊤
  let z := E (L.iso.inv.app ⊤ (pullSection a.smul.left F v))
  have hl (i : Character T) (w : Γ(F, ⊤)) :
      B (d i (l i w)) = c i • (transport a L.iso (p ≫ t) (p ≫ x)).inv.app ⊤
        (pullSection (actOn a (p ≫ t) (p ≫ x)).left F w) := by
    change (pullComp F p x).hom.app ⊤ (c i • pullSection p.left P (l i w)) = _
    rw [Scheme.Modules.Hom.app_smul]
    exact congrArg (c i • ·) (inverseTransport_baseChange L E hE p t x w).symm
  have hr (i : Character T) (w : Γ(F, ⊤)) :
      B (d i (r i w)) = c i • ((p ≫ t).left.appTop (characterFunction i) •
        pullSection (p ≫ x).left F w) := by
    change (pullComp F p x).hom.app ⊤ (c i • pullSection p.left P (r i w)) = _
    rw [Scheme.Modules.Hom.app_smul, comp_appTop_apply]
    exact congrArg (c i • ·) (comparePull_section_smul F p x rfl _ w)
  have hm := hmul (T.X ⊗ Y) s (p ≫ t) (p ≫ x) v
  have H : B (z.sum (fun i w => d i (l i w))) = B (z.sum (fun i w => d i (r i w))) := by
    dsimp only [Finsupp.sum] at hm ⊢
    rw [map_sum, map_sum]
    simp only [hl, hr]
    exact hm
  have H' := (moduleSectionsIso (pullComp F p x)).injective H
  have hcoeff : l χ (z χ) = r χ (z χ) := by
    apply eq_of_weighted_sums D d hD z l r _ _ H'
    · intro i
      change (transport a L.iso t x).inv.app ⊤ (pullSectionAdd (actOn a t x).left F 0) = 0
      rw [map_zero, map_zero]
    · intro i
      change t.left.appTop (characterFunction i) • (pullSectionAdd x.left F 0) = 0
      rw [map_zero, smul_zero]
  exact sectionWeight_of_inverse_at_chart hT L j χ (z χ) hcoeff

end SectionCoefficientExtraction

section AffineEquivalence

variable {T : GroupScheme k} {R : TestAlgebra k}
  {a : ModObj T.X (affineScheme R)} {F : (affineScheme R).left.Modules}

attribute [local instance] Classical.decEq

private def InverseExpansionsCompose : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k} {a : ModObj T.X X}
    {F : X.left.Modules} (L : Linearization a F)
    (E : Γ(Pull (snd T.X X) F, ⊤) ≃+ (Character T →₀ Γ(F, ⊤))),
    (∀ χ v, E ((fst T.X X).left.appTop (characterFunction χ) •
      pullSection (snd T.X X).left F v) = Finsupp.single χ v) →
    InverseCoefficientMultiplication L E

private theorem inverseExpansionsCompose : InverseExpansionsCompose.{u} := by
  intro k _ T X a F L E hE
  exact inverseCoefficientComposition L E hE

private def GradedIsomorphismsLinearized : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {R : TestAlgebra k}
    {a : ModObj T.X (affineScheme R)} {F : (affineScheme R).left.Modules} [F.IsQuasicoherent]
    (hT : IsSplitTorus T) (G : AffineGrading R a) (H : ModuleGrading G.val (sectionsModule F)),
    ∃ L : Linearization a F, L.iso = gradedLinearizationIso G H hT

private theorem gradedIsomorphismsLinearized : GradedIsomorphismsLinearized.{u} := by
  intro k _ T R a F hF hT G H
  exact ⟨gradedLinearization G H hT, rfl⟩

/-- The multiplicative law for the inverse expansions gives every section
as a finite sum of its scheme-theoretic weights. -/
private theorem sectionWeightSpace_internal [F.IsQuasicoherent]
    (hc : InverseExpansionsCompose.{u}) (hT : IsSplitTorus T) (L : Linearization a F) :
    DirectSum.IsInternal (sectionWeightSpace hT L) := by
  let X := affineScheme R
  obtain ⟨E, hE⟩ := projectionSectionExpansion hT R F
  let B := (L.iso.inv.app ⊤).hom
  let C := E.toAddMonoidHom.comp (B.comp (pullSectionAdd a.smul.left F))
  refine internal_of_inverse_coefficients (sectionWeightSpace hT L) C ?_ ?_ ?_
  · exact fun i v => inverseTransport_coefficients_weight hT L E hE (hc L E hE) v i
  · exact inverseTransport_coefficients_sum L E hE
  · intro i v
    have hv : HasSectionWeight L (show Γ(F, ⊤) from v.val) i := v.property
    have hv' : HasSectionWeight L (show Γ(F, ⊤) from v.val) i⁻¹⁻¹ := by simpa only [inv_inv] using hv
    have hw := (sectionWeight_iff_inverse hT L i⁻¹ v.val).mp hv'
    change E (L.iso.inv.app ⊤ (pullSection a.smul.left F v.val)) = _
    rw [hw]
    exact hE i⁻¹ v.val

private theorem linearization_eq_of_hom {L K : Linearization a F}
    (h : L.iso.hom = K.iso.hom) : L = K := by
  have he : L.iso = K.iso := Iso.ext h
  cases L
  cases K
  cases he
  rfl

private theorem moduleGrading_eq_of_piece {G : AffineGrading R a}
    {H K : ModuleGrading G.val (sectionsModule F)} (h : H.piece = K.piece) : H = K := by
  rcases H with ⟨⟨p, hp⟩, hm⟩
  rcases K with ⟨⟨q, hq⟩, hn⟩
  change p = q at h
  subst q
  rfl

/-- The equivalence on linearizations of a particular affine module sheaf. -/
private def affineModuleEquiv (hc : InverseExpansionsCompose.{u})
    (hd : GradedIsomorphismsLinearized.{u}) (hT : IsSplitTorus T) (G : AffineGrading R a)
    (F : (affineScheme R).left.Modules) [F.IsQuasicoherent] :
    Linearization a F ≃ ModuleGrading G.val (sectionsModule F) where
  toFun L := moduleGradingOfWeights hT L G (sectionWeightSpace_internal hc hT L)
  invFun H := (hd hT G H).choose
  left_inv L := by
    let H := moduleGradingOfWeights hT L G (sectionWeightSpace_internal hc hT L)
    apply linearization_eq_of_hom
    have hIso : (hd hT G H).choose.iso = gradedLinearizationIso G H hT := (hd hT G H).choose_spec
    change (hd hT G H).choose.iso.hom = L.iso.hom
    rw [hIso]
    apply affinePullHom_ext_of_homogeneous H.toWeightGrading (actionProjection T R)
    intro χ v hv
    exact (gradedLinearizationIso_apply G H hT χ v hv).trans
      ((show HasSectionWeight L v χ from hv).symm)
  right_inv H := by
    let L := (hd hT G H).choose
    let K := moduleGradingOfWeights hT L G (sectionWeightSpace_internal hc hT L)
    apply moduleGrading_eq_of_piece
    change K.piece = H.piece
    apply Eq.symm
    apply (K.internal.submodule_iSupIndep.le_iff_eq_of_iSup_eq_top H.internal.submodule_iSup_eq_top).mp
    intro χ v hv
    change HasSectionWeight L v χ
    unfold HasSectionWeight
    rw [show L.iso = gradedLinearizationIso G H hT from (hd hT G H).choose_spec]
    exact gradedLinearizationIso_apply G H hT χ v hv

set_option backward.isDefEq.respectTransparency false in
/-- The two directions of the affine comparison after the transport
composition equations have been established. -/
private theorem equivariantAffineComparison_of_cocycles
    (hc : InverseExpansionsCompose.{u}) (hd : GradedIsomorphismsLinearized.{u}) :
    EquivariantAffineComparison.{u} := by
  intro k _ T hT R a
  let G := affineGradingOfWeights hT (functionWeightSpace_internal (a := a) hT)
  let E : AffineModuleComparison R a G := fun F hF => affineModuleEquiv hc hd hT G F
  refine ⟨G, E, ?_, ?_, ?_⟩
  · intro F hF
    exact ⟨⟨asIso F.fromTildeΓ⟩, fun _ _ _ => Iff.rfl⟩
  · intro F H hF hH L K f
    exact isLinearizedMap_iff_preserves_weight_of_internal L K (E F hF L).toWeightGrading
      (fun _ _ => Iff.rfl) f
  · intro F hF L K χ h ψ
    ext s
    exact sectionWeight_twist hT L K χ ψ s h

theorem equivariantAffineComparison : EquivariantAffineComparison.{u} :=
  equivariantAffineComparison_of_cocycles inverseExpansionsCompose gradedIsomorphismsLinearized

theorem pointCharacterComparison : PointCharacterComparison.{u} :=
  pointCharacterComparison_of_affineComparison equivariantAffineComparison

end AffineEquivalence

section AffineRestriction

private def HasCanonicalPullbackLinearizations : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
    {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules} (L : Linearization a F),
    ∃ K : Linearization b (Pull f F), K.iso = pullbackLinearizationIso hf L.iso

private theorem linearizationPullback_of_canonical
    (h : HasCanonicalPullbackLinearizations.{u}) : LinearizationPullback.{u} := by
  intro k _ T X Y a b f hf F L
  obtain ⟨K, hK⟩ := h hf L
  refine ⟨K, fun Z t y => ⟨equivariant_actOn hf, ?_⟩⟩
  rw [hK]
  exact pullbackLinearization_transport hf L.iso t y

set_option backward.isDefEq.respectTransparency false in
private theorem sectionWeight_pullback_of_iso {T : GroupScheme k} {X Y : SchemeOver k}
    {a : ModObj T.X X} {b : ModObj T.X Y} {f : Y ⟶ X}
    (hf : IsEquivariantMap a b f) {F : X.left.Modules} (L : Linearization a F)
    (K : Linearization b (Pull f F)) (hK : K.iso = pullbackLinearizationIso hf L.iso)
    {s : Γ(F, ⊤)} {χ : Character T} (hs : HasSectionWeight L s χ) :
    HasSectionWeight K (pullSection f.left F s) χ := by
  rcases K with ⟨θ, hunit, hmul⟩
  change θ = pullbackLinearizationIso hf L.iso at hK
  subst θ
  exact @sectionWeight_pullback_iso k _ T X Y a b f hf F L s χ hs


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 340000 in
private theorem affineGradingRestriction_of_canonical
    (h : HasCanonicalPullbackLinearizations.{u}) : AffineGradingRestriction.{u} := by
  intro k _ T hT R S φ f a b _ hf F hF L
  let φ₀ : affineRing R ⟶ affineRing S := CommRingCat.ofHom φ.hom.toRingHom
  obtain ⟨K, hK⟩ := h hf L
  obtain ⟨e, he⟩ := @affineSectionBaseChange (affineRing R) (affineRing S) φ₀ F hF
  have hw (χ : Character T) (s : Γ(F, ⊤)) (hs : HasSectionWeight L s χ) :
      HasSectionWeight K (pullSection f.left F s) χ :=
    sectionWeight_pullback_of_iso hf L K hK hs
  refine ⟨K, e, @pullback_spec_isQuasicoherent (affineRing R) (affineRing S) φ₀ F hF, ?_, he, hw, ?_⟩
  · intro Z t y
    refine ⟨equivariant_actOn hf, ?_⟩
    rw [hK]
    exact pullbackLinearization_transport hf L.iso t y
  · intro χ δ r s hr hs
    exact sectionWeight_smul hT K hr (hw χ s hs)

set_option backward.isDefEq.respectTransparency false in
private theorem affineGradingPrincipalOpen_of_canonical
    (h : HasCanonicalPullbackLinearizations.{u}) : AffineGradingPrincipalOpen.{u} := by
  intro k _ T hT R r a S φ f b hf δ hr F hF L
  obtain ⟨K, hK⟩ := h hf L
  let u : S := IsLocalization.Away.invSelf (S := Localization.Away r) r
  let g := (Scheme.ΓSpecIso (affineRing S)).inv u
  have hr' := functionWeight_pullback f hf _ δ hr
  have hφ : f.left.appTop ((Scheme.ΓSpecIso (affineRing R)).inv r) =
      (Scheme.ΓSpecIso (affineRing S)).inv (φ r) :=
    appTop_Spec_map (CommRingCat.ofHom φ.hom.toRingHom) r
  rw [hφ] at hr'
  have hu' : φ r * u = 1 := IsLocalization.Away.mul_invSelf (S := Localization.Away r) r
  have hu : (Scheme.ΓSpecIso (affineRing S)).inv (φ r) * g = 1 := by
    rw [← map_mul, hu', map_one]
  have hg := functionWeight_inv_of_mul_eq_one hT hr' hu
  refine ⟨K, ?_, ?_⟩
  · intro Z t y
    refine ⟨equivariant_actOn hf, ?_⟩
    rw [hK]
    exact pullbackLinearization_transport hf L.iso t y
  · intro χ s n hs
    have hw : HasSectionWeight K (pullSection f.left F s) χ :=
      sectionWeight_pullback_of_iso hf L K hK hs
    have hh := sectionWeight_smul hT K (functionWeight_pow hT hg n) hw
    rw [map_pow]
    exact hh

private theorem canonicalPullbackLinearizations : HasCanonicalPullbackLinearizations.{u} := by
  intro k _ T X Y a b f hf F L
  exact ⟨pullbackLinearization hf L, rfl⟩

theorem linearizationPullback : LinearizationPullback.{u} :=
  linearizationPullback_of_canonical canonicalPullbackLinearizations

theorem affineGradingRestriction : AffineGradingRestriction.{u} :=
  affineGradingRestriction_of_canonical canonicalPullbackLinearizations

theorem affineGradingPrincipalOpen : AffineGradingPrincipalOpen.{u} :=
  affineGradingPrincipalOpen_of_canonical canonicalPullbackLinearizations

end AffineRestriction

end

end LinearAlgebraicGroups.Representation.EquivariantAffineModules
