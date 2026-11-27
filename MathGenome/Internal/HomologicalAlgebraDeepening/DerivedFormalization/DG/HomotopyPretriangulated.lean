import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeRotation
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomotopyPretriangulated
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v w

namespace DerivedFormalization.RightDGModule

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N : RightDGModule A}

noncomputable section

local notation "Q" => (toHomotopyCategory A)

open private identityConeContractible strictNeg homotopyClass_neg forwardRotation inverseRotation
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeRotation
open private map_heq_of_eq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyShift

private theorem quotientShiftObj_eq (X : RightDGModule A) (n : ℤ) :
    (shiftFunctor (K A) n).obj ((Q).obj X) = (Q).obj (shift X n) :=
  congrArg (fun F : K A ⥤ K A => F.obj ((Q).obj X)) (homotopyShiftFunctor_eq n)

private theorem quotientShift_map_heq (n : ℤ) (f : M ⟶ N) :
    HEq ((shiftFunctor (K A) n).map ((Q).map f)) ((Q).map (shiftMap n f)) :=
  (map_heq_of_eq (homotopyShiftFunctor_eq (A := A) n) ((Q).map f)).trans
    (heq_of_eq (@homotopyShift_map k _ A M N n f))

private theorem quotient_map_neg_eq (f : M ⟶ N) : (Q).map (strictNeg f) = -(Q).map f :=
  homotopyClass_neg f

/-- The canonical triangle of a strict right dg module map, with third arrow
given by the negative of the quotient projection. -/
abbrev coneTriangle (f : M ⟶ N) : Triangle (K A) :=
  @Specs.DerivedFormalization.DG.ConeRotation.coneTriangle k _ A M N
    (instCategoryK A) (homotopyHasShift (A := A)) (homotopyPreadditive (A := A))
    Q quotientShiftObj_eq f

/-- The third arrow is the negative projection with its target identified with the shift. -/
theorem coneTriangle_mor₃_heq (f : M ⟶ N) :
    HEq (coneTriangle f).mor₃ (-(Q).map (coneProjection f)) := by
  let p := (Q).map (coneProjection f)
  let e := (quotientShiftObj_eq M 1).symm
  change HEq (-(p ≫ eqToHom e)) (-p)
  exact (heq_of_eq (Preadditive.neg_comp p (eqToHom e)).symm).trans (comp_eqToHom_heq (-p) e)

/-- The isomorphism closure of the canonical cone triangles. -/
def coneTriangles (A : DGCategory.{u,v,w} k) : Set (Triangle (K A)) :=
  {T | ∃ (M N : RightDGModule A) (f : M ⟶ N), Nonempty (T ≅ coneTriangle f)}

private theorem coneTriangles_of_iso {T U : Triangle (K A)}
    (hU : U ∈ coneTriangles A) (e : T ≅ U) : T ∈ coneTriangles A := by
  obtain ⟨M, N, f, ⟨e'⟩⟩ := hU
  exact ⟨M, N, f, ⟨e ≪≫ e'⟩⟩

private theorem coneTriangles_rotate {T : Triangle (K A)}
    (hT : T ∈ coneTriangles A) : T.rotate ∈ coneTriangles A := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  obtain ⟨r, _⟩ := @forwardRotation k _ A M N
    (instCategoryK A) (homotopyPreadditive (A := A)) Q (fun _ => HEq.rfl)
    (homotopyHasShift (A := A)) quotientShiftObj_eq
    (fun n f => quotientShift_map_heq n f) (fun f => quotient_map_neg_eq f) f
  exact ⟨N, cone f, coneInclusion f, ⟨(Pretriangulated.rotate (K A)).mapIso e ≪≫ r⟩⟩

set_option maxHeartbeats 700000 in
private theorem coneTriangles_invRotate {T : Triangle (K A)}
    (hT : T ∈ coneTriangles A) : T.invRotate ∈ coneTriangles A := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  obtain ⟨r, _⟩ := @inverseRotation k _ A M N
    (instCategoryK A) (homotopyPreadditive (A := A)) Q (fun _ => HEq.rfl)
    (homotopyHasShift (A := A)) quotientShiftObj_eq (fun n f => quotientShift_map_heq n f)
    (strictHasShift (A := A)) (fun _ _ => rfl) (fun _ _ => HEq.rfl)
    (fun X n m h => ⟨heq_of_eq (quotient_shiftFunctorCompIsoId_hom X n m h),
      heq_of_eq (quotient_shiftFunctorCompIsoId_inv X n m h)⟩)
    (homotopyShiftAdditive (A := A)) (fun f => quotient_map_neg_eq f) f
  exact ⟨_, _, _, ⟨(Pretriangulated.invRotate (K A)).mapIso e ≪≫ r⟩⟩

private theorem coneTriangles_rotate_iff (T : Triangle (K A)) :
    T ∈ coneTriangles A ↔ T.rotate ∈ coneTriangles A :=
  ⟨coneTriangles_rotate, fun h =>
    coneTriangles_of_iso (coneTriangles_invRotate h) ((triangleRotation (K A)).unitIso.app T)⟩

private theorem identityConeIsZero (M : RightDGModule A) :
    IsZero ((Q).obj (cone (𝟙 M))) := by
  apply (IsZero.iff_id_eq_zero _).2
  have e := (homotopyCriterion _ _).2 (identityConeContractible M)
  change (Q).map (𝟙 (cone (𝟙 M))) = (Q).map 0 at e
  simpa only [(Q).map_id, (Q).map_zero] using e

private theorem contractible_is_cone (X : K A) :
    contractibleTriangle X ∈ coneTriangles A := by
  let M : RightDGModule A := X
  let f : M ⟶ M := 𝟙 M
  let h := identityConeIsZero M
  refine ⟨M, M, f, ⟨Triangle.isoMk _ _ (Iso.refl X) (Iso.refl X) h.isoZero.symm ?_ ?_ ?_⟩⟩
  · change (𝟙 X) ≫ (𝟙 X) = (𝟙 X) ≫ (Q).map (𝟙 M)
    exact congrArg (fun t => 𝟙 X ≫ t) ((Q).map_id M).symm
  · exact h.eq_of_tgt _ _
  · exact (isZero_zero (K A)).eq_of_src _ _

private theorem signedProjectionSquare {C : Type*} [Category* C] [Preadditive C]
    {X Y S T S' T' : C} {p : X ⟶ S} {q : Y ⟶ T} {c : X ⟶ Y} {a : S ⟶ T}
    (hS : S' = S) (hT : T' = T) (h : p ≫ a = c ≫ q) :
    (-p ≫ eqToHom hS.symm) ≫ (eqToHom hS ≫ a ≫ eqToHom hT.symm) =
      c ≫ (-q ≫ eqToHom hT.symm) := by
  subst S' T'
  simpa only [eqToHom_refl, id_comp, comp_id, Preadditive.neg_comp, Preadditive.comp_neg]
    using congrArg Neg.neg h

/-- A commuting square of homotopy classes between strict maps extends to their cone triangles. -/
theorem coneTriangle_fill {M' N' : RightDGModule A} (f : M ⟶ N) (g : M' ⟶ N')
    (a : (coneTriangle f).obj₁ ⟶ (coneTriangle g).obj₁)
    (b : (coneTriangle f).obj₂ ⟶ (coneTriangle g).obj₂)
    (comm : (coneTriangle f).mor₁ ≫ b = a ≫ (coneTriangle g).mor₁) :
    ∃ c : (coneTriangle f).obj₃ ⟶ (coneTriangle g).obj₃,
      (coneTriangle f).mor₂ ≫ c = b ≫ (coneTriangle g).mor₂ ∧
      (coneTriangle f).mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ (coneTriangle g).mor₃ := by
  obtain ⟨a₀, rfl⟩ := toHomotopyCategory_map_surjective (M := M) (N := M') a
  obtain ⟨b₀, rfl⟩ := toHomotopyCategory_map_surjective (M := N) (N := N') b
  change (Q).map f ≫ (Q).map b₀ = (Q).map a₀ ≫ (Q).map g at comm
  rw [← (Q).map_comp, ← (Q).map_comp] at comm
  obtain ⟨h, H⟩ := (homotopyCriterion _ _).mp comm
  let c := coneMapOfHomotopy f g a₀ b₀ h H
  refine ⟨(Q).map c, ?_, ?_⟩
  · change (Q).map (coneInclusion f) ≫ (Q).map c = (Q).map b₀ ≫ (Q).map (coneInclusion g)
    rw [← (Q).map_comp, ← (Q).map_comp]
    exact congrArg (fun t => (Q).map t) (coneMap_in f g a₀ b₀ h H)
  · have eShift : (shiftFunctor (K A) (1 : ℤ)).map ((Q).map a₀) =
        eqToHom (quotientShiftObj_eq M 1) ≫ (Q).map (shiftMap 1 a₀) ≫
          eqToHom (quotientShiftObj_eq M' 1).symm :=
      (conj_eqToHom_iff_heq _ _ (quotientShiftObj_eq M 1) (quotientShiftObj_eq M' 1)).2
        (quotientShift_map_heq 1 a₀)
    change (-((Q).map (coneProjection f)) ≫ eqToHom (quotientShiftObj_eq M 1).symm) ≫
      (shiftFunctor (K A) (1 : ℤ)).map ((Q).map a₀) =
        (Q).map c ≫ (-((Q).map (coneProjection g)) ≫ eqToHom (quotientShiftObj_eq M' 1).symm)
    have eCone : (Q).map (coneProjection f) ≫ (Q).map (shiftMap 1 a₀) =
        (Q).map c ≫ (Q).map (coneProjection g) := by
      rw [← (Q).map_comp, ← (Q).map_comp]
      exact congrArg (fun t => (Q).map t) (coneMap_out f g a₀ b₀ h H).symm
    rw [eShift]
    exact signedProjectionSquare (quotientShiftObj_eq M 1) (quotientShiftObj_eq M' 1) eCone

private theorem coneTriangles_fill (T U : Triangle (K A)) (hT : T ∈ coneTriangles A)
    (hU : U ∈ coneTriangles A) (a : T.obj₁ ⟶ U.obj₁) (b : T.obj₂ ⟶ U.obj₂)
    (e : T.mor₁ ≫ b = a ≫ U.mor₁) :
    ∃ c : T.obj₃ ⟶ U.obj₃, T.mor₂ ≫ c = b ≫ U.mor₂ ∧
      T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ U.mor₃ := by
  obtain ⟨M, N, f, ⟨eT⟩⟩ := hT
  obtain ⟨M', N', g, ⟨eU⟩⟩ := hU
  let a' := eT.inv.hom₁ ≫ a ≫ eU.hom.hom₁
  let b' := eT.inv.hom₂ ≫ b ≫ eU.hom.hom₂
  have comm : (coneTriangle f).mor₁ ≫ b' = a' ≫ (coneTriangle g).mor₁ := calc
    _ = eT.inv.hom₁ ≫ (T.mor₁ ≫ b) ≫ eU.hom.hom₂ := by
      simp only [b', assoc, eT.inv.comm₁_assoc]
    _ = _ := by simp only [a', e, assoc, eU.hom.comm₁]
  obtain ⟨c', e₂, e₃⟩ := coneTriangle_fill f g a' b' comm
  let h : coneTriangle f ⟶ coneTriangle g := ⟨a', b', c', comm, e₂, e₃⟩
  let h' := eT.hom ≫ h ≫ eU.inv
  have h₁ : h'.hom₁ = a := by
    change eT.hom.hom₁ ≫ (eT.inv.hom₁ ≫ a ≫ eU.hom.hom₁) ≫ eU.inv.hom₁ = a
    simp only [assoc, Iso.hom_inv_id_triangle_hom₁_assoc,
      Iso.hom_inv_id_triangle_hom₁, comp_id]
  have h₂ : h'.hom₂ = b := by
    change eT.hom.hom₂ ≫ (eT.inv.hom₂ ≫ b ≫ eU.hom.hom₂) ≫ eU.inv.hom₂ = b
    simp only [assoc, Iso.hom_inv_id_triangle_hom₂_assoc,
      Iso.hom_inv_id_triangle_hom₂, comp_id]
  exact ⟨h'.hom₃, by simpa only [h₂] using h'.comm₂, by simpa only [h₁] using h'.comm₃⟩

/-- The pretriangulated structure on the homotopy category of right dg modules. -/
instance homotopyPretriangulated : Pretriangulated (K A) where
  distinguishedTriangles := coneTriangles A
  isomorphic_distinguished _ h _ e := coneTriangles_of_iso h e
  contractible_distinguished := contractible_is_cone
  distinguished_cocone_triangle f := by
    obtain ⟨g, rfl⟩ := toHomotopyCategory_map_surjective f
    exact ⟨(coneTriangle g).obj₃, (coneTriangle g).mor₂, (coneTriangle g).mor₃,
      ⟨_, _, g, ⟨Iso.refl _⟩⟩⟩
  rotate_distinguished_triangle := coneTriangles_rotate_iff
  complete_distinguished_triangle_morphism := coneTriangles_fill

/-- The distinguished triangles are the triangles isomorphic to strict cone triangles. -/
theorem distinguished_iff_cone_triangle (T : Triangle (K A)) :
    T ∈ distTriang (K A) ↔ ∃ (M N : RightDGModule A) (f : M ⟶ N),
      Nonempty (T ≅ coneTriangle f) :=
  Iff.rfl

@[simp] theorem coneTriangle_distinguished (f : M ⟶ N) :
    coneTriangle f ∈ distTriang (K A) :=
  ⟨M, N, f, ⟨Iso.refl _⟩⟩

private def triangleIsoOfEqualFirstArrow {C : Type*} [Category* C] [HasShift C ℤ]
    [Preadditive C] [HasZeroObject C] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
    [Pretriangulated C] {X Y Z W : C} {f g : X ⟶ Y}
    {j : Y ⟶ Z} {j' : Y ⟶ W} {p : Z ⟶ X⟦(1 : ℤ)⟧} {p' : W ⟶ X⟦(1 : ℤ)⟧}
    (hf : Triangle.mk f j p ∈ distTriang C) (hg : Triangle.mk g j' p' ∈ distTriang C)
    (h : f = g) : Triangle.mk f j p ≅ Triangle.mk g j' p' :=
  isoTriangleOfIso₁₂ _ _ hf hg (Iso.refl X) (Iso.refl Y) (by
    change f ≫ 𝟙 Y = 𝟙 X ≫ g
    rw [comp_id, id_comp, h])

/-- Strict maps in the same homotopy class have isomorphic cone triangles. -/
def coneTriangleIsoOfHomotopic (f g : M ⟶ N) (h : homotopyClass f = homotopyClass g) :
    coneTriangle f ≅ coneTriangle g :=
  triangleIsoOfEqualFirstArrow (C := K A) (f := (Q).map f) (g := (Q).map g)
    (j := (coneTriangle f).mor₂) (j' := (coneTriangle g).mor₂)
    (p := (coneTriangle f).mor₃) (p' := (coneTriangle g).mor₃)
    (coneTriangle_distinguished f) (coneTriangle_distinguished g) (show (Q).map f = (Q).map g from h)

@[simp] theorem coneTriangleIsoOfHomotopic_hom₁ (f g : M ⟶ N)
    (h : homotopyClass f = homotopyClass g) :
    (coneTriangleIsoOfHomotopic f g h).hom.hom₁ = 𝟙 ((Q).obj M) :=
  rfl

@[simp] theorem coneTriangleIsoOfHomotopic_hom₂ (f g : M ⟶ N)
    (h : homotopyClass f = homotopyClass g) :
    (coneTriangleIsoOfHomotopic f g h).hom.hom₂ = 𝟙 ((Q).obj N) :=
  rfl

theorem homotopyPretriangulation :
    Specs.DerivedFormalization.DG.HomotopyPretriangulated.Pretriangulation.{u,v,w} := by
  intro k _ A
  refine ⟨instCategoryK A, rfl, homotopyPreadditive (A := A), homotopyHasShift (A := A),
    homotopyHasZeroObject (A := A), homotopyShiftAdditive (A := A), quotientShiftObj_eq (A := A),
    toHomotopyCategory A, fun _ => rfl, fun _ _ => HEq.rfl, fun _ => HEq.rfl,
    ?_, ?_, homotopyPretriangulated (A := A), ?_, ?_⟩
  · intro X Y f
    exact toHomotopyCategory_map_surjective f
  · intro X Y n f
    exact quotientShift_map_heq n f
  · exact distinguished_iff_cone_triangle
  · intro M N f g h
    exact ⟨coneTriangleIsoOfHomotopic f g h, coneTriangleIsoOfHomotopic_hom₁ f g h,
      coneTriangleIsoOfHomotopic_hom₂ f g h⟩

end

end DerivedFormalization.RightDGModule
