import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyPretriangulated
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ConeOctahedronAxiom
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG.HomComplex (homotopyCategory)
open Specs.DerivedFormalization.DG.ConeOctahedronAxiom (StrictConeOctahedra OctahedronAxiom)

noncomputable section

private theorem signedProjectionComp {D : Type*} [Category* D] [Preadditive D]
    {X Y Y' Z Z' : D} (p : X ⟶ Y) (a : Y ⟶ Z) (hY : Y' = Y) (hZ : Z' = Z) :
    ((-p) ≫ eqToHom hY.symm) ≫ (eqToHom hY ≫ a ≫ eqToHom hZ.symm) =
      (-(p ≫ a)) ≫ eqToHom hZ.symm := by
  subst Y' Z'
  simp only [eqToHom_refl, id_comp, comp_id, Preadditive.neg_comp]

private theorem signedProjectionPrecomp {D : Type*} [Category* D] [Preadditive D]
    {X Y Z Z' : D} (b : X ⟶ Y) (p : Y ⟶ Z) (hZ : Z' = Z) :
    b ≫ ((-p) ≫ eqToHom hZ.symm) = (-(b ≫ p)) ≫ eqToHom hZ.symm := by
  rw [← Category.assoc b (-p) (eqToHom hZ.symm), Preadditive.comp_neg]

section StrictCones

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable [Category.{max v w} (homotopyCategory A)] [Preadditive (homotopyCategory A)]
  [HasShift (homotopyCategory A) ℤ]
variable (Q : RightDGModule A ⥤ (homotopyCategory A))
variable (hQT : ∀ X n, (shiftFunctor (homotopyCategory A) n).obj (Q.obj X) = Q.obj (shift X n))
variable {M N P : RightDGModule A}

local notation "row" => Specs.DerivedFormalization.DG.ConeRotation.coneTriangle Q hQT

private theorem coneTriangle_mor₃_eq_signedProjection (f : M ⟶ N) :
    (row f).mor₃ = (-(Q.map (coneProjection f))) ≫ eqToHom (hQT M 1).symm := by
  change -(Q.map (coneProjection f) ≫ eqToHom (hQT M 1).symm) = _
  exact (Preadditive.neg_comp _ _).symm

private theorem coneProjection_shift_comp
    (hMap : ∀ {X Y : RightDGModule A} (n : ℤ) (f : X ⟶ Y),
      HEq ((shiftFunctor (homotopyCategory A) n).map (Q.map f)) (Q.map (shiftMap n f)))
    (f : M ⟶ N) (a : M ⟶ P) :
    (row f).mor₃ ≫ (shiftFunctor (homotopyCategory A) (1 : ℤ)).map (Q.map a) =
      (-(Q.map (coneProjection f ≫ shiftMap 1 a))) ≫ eqToHom (hQT P 1).symm := by
  have ha := (conj_eqToHom_iff_heq _ _ (hQT M 1) (hQT P 1)).2 (hMap 1 a)
  rw [ha, coneTriangle_mor₃_eq_signedProjection Q hQT f]
  rw [signedProjectionComp _ _ (hQT M 1) (hQT P 1), ← Q.map_comp]

private theorem comp_coneProjection (f : M ⟶ N) {X : RightDGModule A} (b : X ⟶ cone f) :
    Q.map b ≫ (row f).mor₃ =
      (-(Q.map (b ≫ coneProjection f))) ≫ eqToHom (hQT M 1).symm := by
  rw [coneTriangle_mor₃_eq_signedProjection Q hQT f]
  rw [signedProjectionPrecomp _ _ (hQT M 1), ← Q.map_comp]

section FourthTriangle

variable (f : M ⟶ N) (g : N ⟶ P)

private def iteratedConeIso
    (hClass : ∀ {X Y : RightDGModule A} (h : X ⟶ Y), HEq (Q.map h) (homotopyClass h)) :
    Q.obj (cone g) ≅ Q.obj (cone (firstConeMap f g)) where
  hom := Q.map (octahedronSection f g)
  inv := Q.map (octahedronReadout f g)
  hom_inv_id := by rw [← Q.map_comp, octahedron_id_left, Q.map_id]
  inv_hom_id := by
    rw [← Q.map_comp, ← Q.map_id]
    have h := (homotopyCriterion _ _).2 ⟨_, octahedron_homotopy f g⟩
    exact eq_of_heq ((hClass _).trans ((heq_of_eq h).trans (hClass _).symm))

local notation "α" => firstConeMap f g
local notation "β" => secondConeMap f g

private abbrev fourthArrow :
    Q.obj (cone g) ⟶ (shiftFunctor (homotopyCategory A) (1 : ℤ)).obj (Q.obj (cone f)) :=
  (row g).mor₃ ≫ (shiftFunctor (homotopyCategory A) (1 : ℤ)).map (Q.map (coneInclusion f))

private def fourthTriangleIso
    (hClass : ∀ {X Y : RightDGModule A} (h : X ⟶ Y), HEq (Q.map h) (homotopyClass h))
    (hMap : ∀ {X Y : RightDGModule A} (n : ℤ) (h : X ⟶ Y),
      HEq ((shiftFunctor (homotopyCategory A) n).map (Q.map h)) (Q.map (shiftMap n h))) :
    Triangle.mk (Q.map α) (Q.map β) (fourthArrow Q hQT f g) ≅ row α := by
  let e := iteratedConeIso Q f g hClass
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
  · change Q.map α ≫ 𝟙 _ = 𝟙 _ ≫ Q.map α
    rw [comp_id, id_comp]
  · change Q.map β ≫ e.hom = 𝟙 _ ≫ Q.map (coneInclusion α)
    have hβ : Q.map β = Q.map (coneInclusion α) ≫ e.inv := by
      change Q.map β = Q.map (coneInclusion α) ≫ Q.map (octahedronReadout f g)
      rw [← Q.map_comp, octahedron_inclusion]
    rw [hβ, assoc, e.inv_hom_id, comp_id, id_comp]
  · change fourthArrow Q hQT f g ≫
      (shiftFunctor (homotopyCategory A) (1 : ℤ)).map (𝟙 (Q.obj (cone f))) =
      Q.map (octahedronSection f g) ≫ (row α).mor₃
    rw [fourthArrow, CategoryTheory.Functor.map_id, comp_id,
      coneProjection_shift_comp Q hQT hMap, comp_coneProjection Q hQT, octahedron_projection]

end FourthTriangle

private theorem strictConeOctahedra [HasZeroObject (homotopyCategory A)]
    [∀ n : ℤ, Functor.Additive (shiftFunctor (homotopyCategory A) n)]
    [Pretriangulated (homotopyCategory A)]
    (hClass : ∀ {X Y : RightDGModule A} (h : X ⟶ Y), HEq (Q.map h) (homotopyClass h))
    (hMap : ∀ {X Y : RightDGModule A} (n : ℤ) (h : X ⟶ Y),
      HEq ((shiftFunctor (homotopyCategory A) n).map (Q.map h)) (Q.map (shiftMap n h)))
    (hCone : ∀ {X Y : RightDGModule A} (h : X ⟶ Y), row h ∈ distTriang (homotopyCategory A)) :
    StrictConeOctahedra Q hQT hCone := by
  intro M N P f g
  let α := firstConeMap f g
  let β := secondConeMap f g
  let e := fourthTriangleIso Q hQT f g hClass hMap
  let O : Triangulated.Octahedron (Q.map_comp f g).symm (hCone f) (hCone g) (hCone (f ≫ g)) :=
    { m₁ := Q.map α
      m₃ := Q.map β
      comm₁ := by
        change Q.map (coneInclusion f) ≫ Q.map α = Q.map g ≫ Q.map (coneInclusion (f ≫ g))
        rw [← Q.map_comp, ← Q.map_comp, firstConeMap_inclusion]
      comm₂ := by
        change Q.map α ≫ (row (f ≫ g)).mor₃ = (row f).mor₃
        rw [comp_coneProjection Q hQT, firstConeMap_projection]
        exact (coneTriangle_mor₃_eq_signedProjection Q hQT f).symm
      comm₃ := by
        change Q.map (coneInclusion (f ≫ g)) ≫ Q.map β = Q.map (coneInclusion g)
        rw [← Q.map_comp, secondConeMap_inclusion]
      comm₄ := by
        change (row (f ≫ g)).mor₃ ≫ (shiftFunctor (homotopyCategory A) (1 : ℤ)).map (Q.map f) =
          Q.map β ≫ (row g).mor₃
        rw [coneProjection_shift_comp Q hQT hMap, comp_coneProjection Q hQT,
          secondConeMap_projection]
      mem := isomorphic_distinguished _ (hCone α) _ e }
  exact ⟨α, β, octahedronSection f g, firstConeMap_apply f g, secondConeMap_apply f g,
    octahedronSection_apply f g, O, rfl, rfl, e, rfl, rfl, rfl⟩

end StrictCones

private theorem octahedronWithComposite {D : Type*} [Category* D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
    [Pretriangulated D] {X Y Z U V W : D}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z} (e : a ≫ b = c)
    {i : Y ⟶ U} {p : U ⟶ X⟦(1 : ℤ)⟧} (ha : Triangle.mk a i p ∈ distTriang D)
    {j : Z ⟶ V} {q : V ⟶ Y⟦(1 : ℤ)⟧} (hb : Triangle.mk b j q ∈ distTriang D)
    {k : Z ⟶ W} {r : W ⟶ X⟦(1 : ℤ)⟧} (hc : Triangle.mk c k r ∈ distTriang D)
    (O : Triangulated.Octahedron e ha hb hc) :
    ∃ h : Triangle.mk (a ≫ b) k r ∈ distTriang D,
      Nonempty (Triangulated.Octahedron rfl ha hb h) := by
  subst c
  exact ⟨hc, ⟨O⟩⟩

section ArbitraryRows

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable [Category.{max v w} (homotopyCategory A)] [Preadditive (homotopyCategory A)]
  [HasShift (homotopyCategory A) ℤ] [HasZeroObject (homotopyCategory A)]
  [∀ n : ℤ, Functor.Additive (shiftFunctor (homotopyCategory A) n)]
  [Pretriangulated (homotopyCategory A)]
variable (Q : RightDGModule A ⥤ homotopyCategory A)
variable (hQT : ∀ X n, (shiftFunctor (homotopyCategory A) n).obj (Q.obj X) = Q.obj (shift X n))

local notation "row" => Specs.DerivedFormalization.DG.ConeRotation.coneTriangle Q hQT

private theorem isTriangulatedOfStrictConeOctahedra
    (hObj : ∀ X, Q.obj X = X)
    (hSurj : ∀ X Y, Function.Surjective (Q.map (X := X) (Y := Y)))
    (hCone : ∀ {X Y : RightDGModule A} (h : X ⟶ Y), row h ∈ distTriang (homotopyCategory A))
    (hStrict : StrictConeOctahedra Q hQT hCone) : IsTriangulated (homotopyCategory A) := by
  apply IsTriangulated.mk'
  intro X Y Z f g
  let eX : X ≅ Q.obj X := eqToIso (hObj X).symm
  let eY : Y ≅ Q.obj Y := eqToIso (hObj Y).symm
  let eZ : Z ≅ Q.obj Z := eqToIso (hObj Z).symm
  obtain ⟨f₀, hf⟩ := hSurj X Y (eX.inv ≫ f ≫ eY.hom)
  obtain ⟨g₀, hg⟩ := hSurj Y Z (eY.inv ≫ g ≫ eZ.hom)
  have hf' : f ≫ eY.hom = eX.hom ≫ Q.map f₀ := by
    rw [hf, Iso.hom_inv_id_assoc]
  have hg' : g ≫ eZ.hom = eY.hom ≫ Q.map g₀ := by
    rw [hg, Iso.hom_inv_id_assoc]
  obtain ⟨_, _, _, _, _, _, O, _⟩ := hStrict f₀ g₀
  obtain ⟨hComposite, hOct⟩ := octahedronWithComposite (Q.map_comp f₀ g₀).symm
    (hCone f₀) (hCone g₀) (hCone (f₀ ≫ g₀)) O
  exact ⟨Q.obj X, Q.obj Y, Q.obj Z,
    (row f₀).obj₃, (row g₀).obj₃, (row (f₀ ≫ g₀)).obj₃,
    Q.map f₀, Q.map g₀, eX, eY, eZ, hf', hg',
    (row f₀).mor₂, (row f₀).mor₃, hCone f₀,
    (row g₀).mor₂, (row g₀).mor₃, hCone g₀,
    (row (f₀ ≫ g₀)).mor₂, (row (f₀ ≫ g₀)).mor₃, hComposite, hOct⟩

end ArbitraryRows

/-- The signed cone pretriangulation of the right dg module homotopy category satisfies TR4. -/
theorem homotopyOctahedronAxiom : OctahedronAxiom.{u,v,w} := by
  intro k _ A C _
  let := C
  intro P S Z
  let := P
  let := S
  let := Z
  intro L hShift Q hObj
  let := L
  intro _ hClass hSurj hMap T
  let := T
  intro hQT hDist
  let hCone : ∀ {X Y : RightDGModule A} (f : X ⟶ Y),
      Specs.DerivedFormalization.DG.ConeRotation.coneTriangle Q hQT f ∈
        distTriang (homotopyCategory A) := fun {X Y} f =>
    (hDist _).2 ⟨X, Y, f, ⟨Iso.refl _⟩⟩
  have hStrict : StrictConeOctahedra Q hQT hCone := strictConeOctahedra Q hQT hClass hMap hCone
  exact ⟨hStrict, isTriangulatedOfStrictConeOctahedra Q hQT hObj hSurj hCone hStrict⟩

open private quotientShiftObj_eq quotientShift_map_heq
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyPretriangulated

/-- The canonical pretriangulation on `K A` is triangulated. -/
instance homotopyIsTriangulated {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k} :
    IsTriangulated (K A) :=
  (homotopyOctahedronAxiom A (instCategoryK A) rfl
    (homotopyPreadditive (A := A)) (homotopyHasShift (A := A)) (homotopyHasZeroObject (A := A))
    (homotopyShiftAdditive (A := A)) (quotientShiftObj_eq (A := A))
    (toHomotopyCategory A) (fun _ => rfl) (fun _ _ => HEq.rfl) (fun _ => HEq.rfl)
    (fun _ _ f => toHomotopyCategory_map_surjective f)
    (fun n f => quotientShift_map_heq n f) (homotopyPretriangulated (A := A))
    distinguished_iff_cone_triangle).2

end

end DerivedFormalization.RightDGModule
