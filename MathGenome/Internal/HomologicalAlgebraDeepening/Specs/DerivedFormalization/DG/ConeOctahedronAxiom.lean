import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomotopyPretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace Specs.DerivedFormalization.DG.ConeOctahedronAxiom

open _root_.DerivedFormalization
open Basic (h0CategoryStruct h0Hom)
open HomComplex (dgModuleCategory homComplex homotopyCategory homotopyClass)
open ShiftCone (shift shiftMap cone coneTerm)
open ConeRotation (coneTriangle quotientShiftObj)

section StrictCones

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable [Category.{max v w} (homotopyCategory A)] [Preadditive (homotopyCategory A)]
  [HasShift (homotopyCategory A) ℤ] [HasZeroObject (homotopyCategory A)]
  [∀ n : ℤ, Functor.Additive (shiftFunctor (homotopyCategory A) n)]
  [Pretriangulated (homotopyCategory A)]

/-- The strict cone octahedron with its two right-linear comparison maps.
Its fourth triangle has last arrow `(coneTriangle Q hQT g).mor₃ ≫ [j_f]⟦1⟧'`.
The fourth triangle is identified with the cone triangle of the first comparison. -/
def StrictConeOctahedra (Q : RightDGModuleModel A ⥤ homotopyCategory A)
    (hQT : ∀ X n, (shiftFunctor (homotopyCategory A) n).obj (Q.obj X) = Q.obj (shift X n))
    (hCone : ∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
      coneTriangle Q hQT f ∈ distTriang (homotopyCategory A)) : Prop :=
  ∀ {M N P : RightDGModuleModel A} (f : M ⟶ N) (g : N ⟶ P),
    ∃ (α : cone f ⟶ cone (f ≫ g)) (β : cone (f ≫ g) ⟶ cone g)
      (s : cone g ⟶ cone α),
      (∀ (a : A.Obj) (i : ℤ) (p : coneTerm M N a i),
        (α.app a).f i p = ((g.app a).f i p.1, p.2)) ∧
      (∀ (a : A.Obj) (i : ℤ) (p : coneTerm M P a i),
        (β.app a).f i p = (p.1, (f.app a).f (i+1) p.2)) ∧
      (∀ (a : A.Obj) (i : ℤ) (p : coneTerm N P a i),
        (s.app a).f i p = ((p.1, 0), (p.2, 0))) ∧
      ∃ O : Triangulated.Octahedron (Q.map_comp f g).symm
          (hCone f) (hCone g) (hCone (f ≫ g)),
        O.m₁ = Q.map α ∧ O.m₃ = Q.map β ∧
        ∃ e : O.triangle ≅ coneTriangle Q hQT α,
          e.hom.hom₁ = 𝟙 (Q.obj (cone f)) ∧
          e.hom.hom₂ = 𝟙 (Q.obj (cone (f ≫ g))) ∧
          e.hom.hom₃ = Q.map s

end StrictCones

/-- The structure on the degree-zero cohomology category with the signed shifts and
the distinguished triangles of G04HomotopyPretriangulated satisfies TR4. The
`IsTriangulated` conclusion uses the supplied pretriangulated structure, so it
applies to arbitrary prescribed distinguished triangles in that structure. -/
def OctahedronAxiom : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (C : Category.{max v w} (homotopyCategory A)),
    C.toCategoryStruct = h0CategoryStruct (dgModuleCategory A) →
    letI := C
    ∀ (P : Preadditive (homotopyCategory A)) (S : HasShift (homotopyCategory A) ℤ)
      (Z : HasZeroObject (homotopyCategory A)),
      letI := P
      letI := S
      letI := Z
      ∀ (L : ∀ n : ℤ, Functor.Additive (shiftFunctor (homotopyCategory A) n))
        (hShift : ∀ (X : homotopyCategory A) (n : ℤ),
          (shiftFunctor (homotopyCategory A) n).obj X = shift X n)
        (Q : RightDGModuleModel A ⥤ homotopyCategory A) (hObj : ∀ X, Q.obj X = X),
        letI := L
        (∀ X Y : homotopyCategory A,
          HEq (P.homGroup X Y) (inferInstance : AddCommGroup (h0Hom (homComplex X Y)))) →
        (∀ {M N : RightDGModuleModel A} (f : M ⟶ N), HEq (Q.map f) (homotopyClass f)) →
        (∀ M N, Function.Surjective (Q.map (X := M) (Y := N))) →
        (∀ {M N : RightDGModuleModel A} (n : ℤ) (f : M ⟶ N),
          HEq ((shiftFunctor (homotopyCategory A) n).map (Q.map f)) (Q.map (shiftMap n f))) →
        ∀ T : Pretriangulated (homotopyCategory A),
          letI := T
          let hQT := quotientShiftObj Q hObj hShift
          ∀ hDist : ∀ X : Triangle (homotopyCategory A),
            X ∈ distTriang (homotopyCategory A) ↔
              ∃ (M N : RightDGModuleModel A) (f : M ⟶ N), Nonempty (X ≅ coneTriangle Q hQT f),
          StrictConeOctahedra Q hQT
            (fun {M N} f => (hDist (coneTriangle Q hQT f)).2 ⟨M, N, f, ⟨Iso.refl _⟩⟩) ∧
          IsTriangulated (homotopyCategory A)

end Specs.DerivedFormalization.DG.ConeOctahedronAxiom
