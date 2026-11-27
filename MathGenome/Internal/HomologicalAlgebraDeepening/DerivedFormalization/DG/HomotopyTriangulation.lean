import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeOctahedronAxiom
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomotopyTriangulation
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG.HomotopyTriangulation (IsConeTriangle Triangulation)
open private quotientShift_map_heq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyPretriangulated

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N : RightDGModule A}

/-- A specified right-linear homotopy gives the strict comparison of cones. -/
theorem coneSquareComparison :
    Specs.DerivedFormalization.DG.HomotopyTriangulation.ConeSquareComparison.{u,v,w} :=
  exists_coneMapOfHomotopy

private theorem coneTriangle_has_components (f : M ⟶ N) :
    @IsConeTriangle k _ A (instCategoryK A) (homotopyHasShift (A := A)) M N f
      (coneTriangle f) :=
  ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl, coneTriangle_mor₃_heq f⟩

private theorem triangle_eq_of_components {C : Type*} [Category C] [HasShift C ℤ]
    {T U : Triangle C}
    (h₁ : T.obj₁ = U.obj₁) (h₂ : T.obj₂ = U.obj₂) (h₃ : T.obj₃ = U.obj₃)
    (e₁ : HEq T.mor₁ U.mor₁) (e₂ : HEq T.mor₂ U.mor₂) (e₃ : HEq T.mor₃ U.mor₃) :
    T = U := by
  cases T
  cases U
  cases h₁
  cases h₂
  cases h₃
  cases e₁
  cases e₂
  cases e₃
  rfl

private theorem eq_coneTriangle_of_components (f : M ⟶ N) (T : Triangle (K A))
    (h : @IsConeTriangle k _ A (instCategoryK A) (homotopyHasShift (A := A)) M N f T) :
    T = coneTriangle f := by
  obtain ⟨h₁, h₂, h₃, e₁, e₂, e₃⟩ := h
  exact triangle_eq_of_components h₁ h₂ h₃ e₁ e₂ (e₃.trans (coneTriangle_mor₃_heq f).symm)

/-- The signed shifts and cones give the triangulated structure on the fixed H⁰ category. -/
theorem homotopyTriangulation : Triangulation.{u,v,w} := by
  refine ⟨coneGradedSplit, ?_, ?_, ?_, ?_⟩
  · intro k _ A M N f a
    exact coneShortExact f a
  · intro k _ A M N f a h i
    exact coneConnectingMap f a h i
  · intro k _ A M N f
    exact quasiIso_iff_cone_acyclic f
  · intro k _ A
    refine ⟨instCategoryK A, rfl, homotopyHasShift (A := A), homotopyPreadditive (A := A),
      homotopyHasZeroObject (A := A), homotopyShiftAdditive (A := A),
      homotopyPretriangulated (A := A), homotopyIsTriangulated (A := A), ?_, ?_, ?_, ?_⟩
    · intro M s
      exact congrArg (fun F : K A ⥤ K A => F.obj M) (homotopyShiftFunctor_eq s)
    · intro M N s f
      exact ⟨(toHomotopyCategory A).map f, HEq.rfl, quotientShift_map_heq s f⟩
    · intro M N f g h
      exact ⟨coneTriangle f, coneTriangle g, coneTriangle_has_components f,
        coneTriangle_has_components g, coneTriangleIsoOfHomotopic f g h,
        heq_of_eq (coneTriangleIsoOfHomotopic_hom₁ f g h),
        heq_of_eq (coneTriangleIsoOfHomotopic_hom₂ f g h)⟩
    · intro T
      rw [distinguished_iff_cone_triangle]
      constructor
      · rintro ⟨M, N, f, h⟩
        exact ⟨M, N, f, coneTriangle f, coneTriangle_has_components f, h⟩
      · rintro ⟨M, N, f, U, hU, ⟨e⟩⟩
        exact ⟨M, N, f, ⟨e ≪≫ eqToIso (eq_coneTriangle_of_components f U hU)⟩⟩

end DerivedFormalization.RightDGModule
