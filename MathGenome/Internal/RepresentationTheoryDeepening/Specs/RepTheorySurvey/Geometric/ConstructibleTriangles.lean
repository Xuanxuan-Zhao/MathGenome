import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedLocalSheaves
import Mathlib.Topology.Connected.LocallyConnected

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace RepTheorySurvey.Geometric.ConstructibleTriangles.Expected

open Analytic

set_option linter.checkUnivs false in
def IsConstructibleAlongType :=
  ∀ {X : TopCat.{u}} {I : Type v} {Z : I → TopCat.{u}},
    (∀ i, Z i ⟶ X) → BoundedBelow X → Prop

/-- Finite cohomological support and locally constant finite-rank cohomology
after inverse image along each map in the family. -/
def IsConstructibleAlong : IsConstructibleAlongType.{u, v} :=
  fun {X} {I} {_Z} e F =>
    Set.Finite {q : ℤ | ¬ IsZero ((cohomology X q).obj F.obj)} ∧
      ∀ (i : I) (q : ℤ), LocallyConstantFiniteRank
        ((inverseImage (e i)).obj ((cohomology X q).obj F.obj))

def LocallyConstantFiniteRankKernel : Prop :=
  ∀ {X : TopCat.{u}} [LocallyConnectedSpace X] {A B : Sheaves X} (f : A ⟶ B),
    LocallyConstantFiniteRank A → LocallyConstantFiniteRank B →
      LocallyConstantFiniteRank (kernel f)

def LocallyConstantFiniteRankCokernel : Prop :=
  ∀ {X : TopCat.{u}} [LocallyConnectedSpace X] {A B : Sheaves X} (f : A ⟶ B),
    LocallyConstantFiniteRank A → LocallyConstantFiniteRank B →
      LocallyConstantFiniteRank (cokernel f)

def LocallyConstantFiniteRankExtension : Prop :=
  ∀ {X : TopCat.{u}} [LocallyConnectedSpace X] (S : ShortComplex (Sheaves X)),
    S.ShortExact → LocallyConstantFiniteRank S.X₁ → LocallyConstantFiniteRank S.X₃ →
      LocallyConstantFiniteRank S.X₂

def ConstructibleZero : Prop :=
  ∀ {X : TopCat.{u}} {I : Type v} {Z : I → TopCat.{u}} (e : ∀ i, Z i ⟶ X),
    IsConstructibleAlong e (0 : BoundedBelow X)

def ConstructibleOfIso : Prop :=
  ∀ {X : TopCat.{u}} {I : Type v} {Z : I → TopCat.{u}} (e : ∀ i, Z i ⟶ X)
    {F G : BoundedBelow X}, (F ≅ G) → IsConstructibleAlong e F → IsConstructibleAlong e G

def ConstructibleShift : Prop :=
  ∀ {X : TopCat.{u}} {I : Type v} {Z : I → TopCat.{u}} (e : ∀ i, Z i ⟶ X)
    {F : BoundedBelow X} (n : ℤ), IsConstructibleAlong e F → IsConstructibleAlong e (F⟦n⟧)

/-- Constructibility at any two vertices of a distinguished triangle implies it
at the third. -/
def ConstructibleTriangle : Prop :=
  ∀ {X : TopCat.{u}} {I : Type v} {Z : I → TopCat.{u}} [∀ i, LocallyConnectedSpace (Z i)]
    (e : ∀ i, Z i ⟶ X) (T : Triangle (BoundedBelow X)),
    T ∈ distTriang (BoundedBelow X) →
      ((IsConstructibleAlong e T.obj₁ → IsConstructibleAlong e T.obj₃ →
        IsConstructibleAlong e T.obj₂) ∧
      (IsConstructibleAlong e T.obj₁ → IsConstructibleAlong e T.obj₂ →
        IsConstructibleAlong e T.obj₃) ∧
      (IsConstructibleAlong e T.obj₂ → IsConstructibleAlong e T.obj₃ →
        IsConstructibleAlong e T.obj₁))

/-- Induction via ordinary cohomological truncations, starting with sheaves
placed in degree zero. -/
def ConstructibleTruncationInduction : Prop :=
  ∀ {X : TopCat.{u}} {I : Type v} {Z : I → TopCat.{u}} (e : ∀ i, Z i ⟶ X)
    (P : BoundedBelow X → Prop),
    P 0 →
    (∀ {F G : BoundedBelow X}, (F ≅ G) → P F → P G) →
    (∀ (F : BoundedBelow X) (n : ℤ), P F → P (F⟦n⟧)) →
    (∀ (T : Triangle (BoundedBelow X)), T ∈ distTriang (BoundedBelow X) →
      P T.obj₁ → P T.obj₃ → P T.obj₂) →
    (∀ M : Sheaves X, (∀ i, LocallyConstantFiniteRank ((inverseImage (e i)).obj M)) →
      P (LocalSheaf.sheafInDegreeZero M)) →
    ∀ F : BoundedBelow X, IsConstructibleAlong e F → P F

end RepTheorySurvey.Geometric.ConstructibleTriangles.Expected
