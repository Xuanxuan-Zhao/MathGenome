import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedKProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomotopyTriangulation
import Mathlib.CategoryTheory.Triangulated.Subcategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w t

namespace Specs.DerivedFormalization.DG.DerivedTriangles

open _root_.DerivedFormalization
open Derived (HomotopyCategoryLaws)
open DerivedKProjective (derivedCategoryInstance kProjectiveObjects)
open HomComplex (homotopyCategory homotopyClass gradedHom component HomotopyEquation)
open ShiftCone (shift shiftMap cone coneTerm coneInclusion coneProjection)

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

/-- The matrix determined by a specified right-linear homotopy, with the two
commuting squares for the strict inclusions and quotient projections. -/
def IsConeComparison {M N M' N' : RightDGModuleModel A}
    {f : M ⟶ N} {g : M' ⟶ N'} (a : M ⟶ M') (b : N ⟶ N')
    (H : gradedHom M N' (-1)) (c : cone f ⟶ cone g) : Prop :=
  coneInclusion f ≫ c = b ≫ coneInclusion g ∧
  c ≫ coneProjection g = coneProjection f ≫ shiftMap 1 a ∧
  ∀ (o : A.Obj) (i : ℤ) (x : coneTerm M N o i),
    (c.app o).f i x =
      ((b.app o).f i x.1 + component H o (i + 1) i (by omega) x.2,
        (a.app o).f (i + 1) x.2)

/-- The comparison of cones of a homotopy-commutative square with objectwise
quasi-isomorphisms on its vertical sides is an objectwise quasi-isomorphism. -/
def ConeSquareQuasiIso : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N M' N' : RightDGModuleModel A} (f : M ⟶ N) (g : M' ⟶ N')
    (a : M ⟶ M') (b : N ⟶ N') (H : gradedHom M N' (-1)),
    HomotopyEquation (f ≫ b) (a ≫ g) H →
    Module.quasiIsomorphism a → Module.quasiIsomorphism b →
    ∃ c : cone f ⟶ cone g, IsConeComparison a b H c ∧ Module.quasiIsomorphism c

/-- Any two K-projective replacements of the endpoints admit a strict lift of
the map and a right-linear homotopy of the square with the augmentations. -/
def ReplacementConeComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P P' M N : RightDGModuleModel A} (p : P ⟶ M) (q : P' ⟶ N) (f : M ⟶ N),
    KProjective.isKProjective P → KProjective.isKProjective P' →
    Module.quasiIsomorphism p → Module.quasiIsomorphism q →
    ∃ (g : P ⟶ P') (H : gradedHom P N (-1)) (c : cone g ⟶ cone f),
      HomotopyEquation (g ≫ q) (p ≫ f) H ∧
      IsConeComparison p q H c ∧ Module.quasiIsomorphism c

/-- The last arrow uses the negative of the specified strict projection.
The equality identifies the categorical shift with the signed strict shift. -/
abbrev triangleOfMaps (h : HomotopyCategoryLaws A)
    (S : letI := Derived.homotopyCategory A h; HasShift (homotopyCategory A) ℤ)
    {M N C : RightDGModuleModel A}
    (e : letI := Derived.homotopyCategory A h; letI := S
         (shiftFunctor (homotopyCategory A) (1 : ℤ)).obj M = shift M 1)
    (f : M ⟶ N) (j : N ⟶ C) (p : C ⟶ shift M 1) :
    letI := Derived.homotopyCategory A h; letI := S; Triangle (homotopyCategory A) := by
  letI := Derived.homotopyCategory A h
  letI := S
  let last : Basic.h0Hom
      (HomComplex.homComplex C ((shiftFunctor (homotopyCategory A) (1 : ℤ)).obj M)) :=
    (show @Quiver.Hom (homotopyCategory A) _ C (shift M 1) from homotopyClass p) ≫ eqToHom e.symm
  exact Triangle.mk (homotopyClass f) (homotopyClass j) (-last)

/-- The signed strict cone triangle in the fixed degree-zero cohomology category. -/
abbrev coneTriangle (h : HomotopyCategoryLaws A)
    (S : letI := Derived.homotopyCategory A h; HasShift (homotopyCategory A) ℤ)
    {M N : RightDGModuleModel A}
    (e : letI := Derived.homotopyCategory A h; letI := S
         (shiftFunctor (homotopyCategory A) (1 : ℤ)).obj M = shift M 1)
    (f : M ⟶ N) :=
  triangleOfMaps h S e f (coneInclusion f) (coneProjection f)

/-- The inherited triangulation on the full K-projective subcategory and its
transfer to the specified localization. The comparisons use the same shifts
and the same localization functor throughout. -/
def TriangulationAt (A : DGCategoryModel.{u,v,w} k) (h : HomotopyCategoryLaws A) : Prop :=
  let K := homotopyCategory A
  let D := Derived.derivedCategory A h
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  let Q : K ⥤ D := Derived.quotient A h
  let P := kProjectiveObjects A
  let R : P.FullSubcategory ⥤ D := P.ι ⋙ Q
  ∃ (SK : HasShift K ℤ) (AK : Preadditive K) (ZK : HasZeroObject K),
    letI := SK
    letI := AK
    letI := ZK
    ∃ (LK : ∀ n : ℤ, (shiftFunctor K n).Additive)
      (hS : ∀ (M : K) (n : ℤ), (shiftFunctor K n).obj M = shift M n),
      letI := LK
      ∃ TK : Pretriangulated K,
        letI := TK
        IsTriangulated K ∧
        (∀ {M N : RightDGModuleModel A} (n : ℤ) (f : M ⟶ N),
          HEq ((shiftFunctor K n).map (show @Quiver.Hom K _ M N from homotopyClass f))
            (homotopyClass (shiftMap n f))) ∧
        (∀ T : Triangle K, T ∈ distTriang K ↔
          ∃ (M N : RightDGModuleModel A) (f : M ⟶ N),
            Nonempty (T ≅ coneTriangle h SK (hS M 1) f)) ∧
        ∃ HP : P.IsTriangulated,
          letI := HP
          IsTriangulated P.FullSubcategory ∧
          ∃ (SD : HasShift D ℤ) (AD : Preadditive D) (ZD : HasZeroObject D),
            letI := SD
            letI := AD
            letI := ZD
            ∃ (LD : ∀ n : ℤ, (shiftFunctor D n).Additive) (qS : Q.CommShift ℤ),
              letI := LD
              letI := qS
              ∃ TD : Pretriangulated D,
                letI := TD
                IsTriangulated D ∧ Q.IsTriangulated ∧ R.IsEquivalence ∧
                R.IsTriangulated ∧
                (∀ T : Triangle D, T ∈ distTriang D ↔
                  ∃ (M N : RightDGModuleModel A) (_ : P M) (_ : P N) (f : M ⟶ N),
                    Nonempty (T ≅ Q.mapTriangle.obj (coneTriangle h SK (hS M 1) f))) ∧
                (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
                  Q.mapTriangle.obj (coneTriangle h SK (hS M 1) f) ∈ distTriang D) ∧
                (∀ {M N M' N' : RightDGModuleModel A}
                  (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
                  (H : gradedHom M N' (-1)) (c : cone f ⟶ cone g),
                  HomotopyEquation (f ≫ b) (a ≫ g) H →
                  IsConeComparison a b H c →
                  Module.quasiIsomorphism a → Module.quasiIsomorphism b →
                  ∃ e : Q.mapTriangle.obj (coneTriangle h SK (hS M 1) f) ≅
                        Q.mapTriangle.obj (coneTriangle h SK (hS M' 1) g),
                    e.hom.hom₁ = Q.map (homotopyClass a) ∧
                    e.hom.hom₂ = Q.map (homotopyClass b) ∧
                    e.hom.hom₃ = Q.map (homotopyClass c))

/-- At a native coefficient level containing the object universe. -/
def NativeTriangulation : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w,w} k)
    (h : HomotopyCategoryLaws A), TriangulationAt A h

open AmbientDerived (category strictInput)

/-- In the common adequate localization for an arbitrary original dg category. -/
def AmbientTriangulation : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : HomotopyCategoryLaws (category.{u,v,w,t} A)),
    TriangulationAt (category.{u,v,w,t} A) h

/-- The image of the cone of an original strict map can use the lifted original
cone as its third object. The strict comparisons commute with the inclusion and
the projection, and the triangle comparison localizes the coordinate isomorphism. -/
def LiftedConeTriangleComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    let B := category.{u,v,w,t} A
    let F := strictInput.{u,v,w,t} A
    ∀ (h : HomotopyCategoryLaws B),
      let K := homotopyCategory B
      let D := AmbientDerived.derivedCategory.{u,v,w,t} A h
      letI := Derived.homotopyCategory B h
      letI := derivedCategoryInstance B h
      let Q : K ⥤ D := AmbientDerived.quotient.{u,v,w,t} A h
      ∀ (SK : HasShift K ℤ),
        letI := SK
        ∀ (hS : ∀ (M : K) (n : ℤ), (shiftFunctor K n).obj M = shift M n)
          (SD : HasShift D ℤ),
          letI := SD
          ∀ qS : Q.CommShift ℤ,
            letI := qS
            ∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
              ∃ (s : F.obj (shift M 1) ≅ shift (F.obj M) 1)
                (c : F.obj (cone f) ≅ cone (F.map f)),
                (∀ (o : A.Obj) (i : ℤ) (x : ((F.obj (cone f)).complex o).X i),
                  (c.hom.app o).f i x = (ULift.up x.down.1, ULift.up x.down.2)) ∧
                F.map (coneInclusion f) ≫ c.hom = coneInclusion (F.map f) ∧
                F.map (coneProjection f) ≫ s.hom = c.hom ≫ coneProjection (F.map f) ∧
                ∃ e : Q.mapTriangle.obj
                    (triangleOfMaps h SK (hS (F.obj M) 1) (F.map f)
                      (F.map (coneInclusion f)) (F.map (coneProjection f) ≫ s.hom)) ≅
                    Q.mapTriangle.obj (coneTriangle h SK (hS (F.obj M) 1) (F.map f)),
                  e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ ∧
                  e.hom.hom₃ = Q.map (homotopyClass c.hom)

end

end Specs.DerivedFormalization.DG.DerivedTriangles
