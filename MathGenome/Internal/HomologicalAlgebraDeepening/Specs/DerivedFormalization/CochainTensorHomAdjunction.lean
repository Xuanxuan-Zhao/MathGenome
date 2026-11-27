import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import Mathlib.CategoryTheory.Adjunction.Basic

/-! Specifications for currying and the two ordinary tensor–Hom adjunctions. -/

namespace Specs.DerivedFormalization.CochainTensorHomAdjunction

open CategoryTheory MonoidalCategory
open scoped TensorProduct
open CochainComplex.HomComplex
open HomologicalComplex (ιTensorObj)
open Specs.DerivedFormalization.Cochains (compValue homotopyValue quotientValue)
open Specs.DerivedFormalization.CochainModels
  (tensorComplexValue tensorMapValue internalHomValue internalHomMapValue)

universe u

variable {R : Type u} [CommRing R]

/-- Tensoring with the fixed complex on the right. -/
noncomputable abbrev tensorWithValue (Y : compValue.{u} R) : compValue.{u} R ⥤ compValue.{u} R :=
  ((curriedTensor (ModuleCat R)).map₂CochainComplex).flip.obj Y

/-- Postcomposition on the product internal Hom with fixed source. -/
@[implicit_reducible]
def homFromValue (Y : compValue.{u} R) : compValue.{u} R ⥤ compValue.{u} R where
  obj Z := internalHomValue Y Z
  map f := internalHomMapValue (𝟙 Y) f
  map_id Z := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext z : 1
    apply Cochain.ext
    intro i j hij
    simp [internalHomMapValue]
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext z : 1
    apply Cochain.ext
    intro i j hij
    simp [internalHomMapValue, Cochain.comp_zero_cochain_v]

/-- The differential, evaluated after currying, acts on the target and the
two source factors with the respective Koszul coefficients. -/
def curryingDifferential (X Y Z : compValue.{u} R)
    (e : internalHomValue (tensorComplexValue X Y) Z ≅ internalHomValue X (internalHomValue Y Z)) :
    Prop :=
  ∀ {n i j l m : ℤ} (hi : i + (n + 1) = l) (hj : j + l = m)
      (f : Cochain (tensorComplexValue X Y) Z n) (x : X.X i) (y : Y.X j),
    ((((internalHomValue X (internalHomValue Y Z)).d n (n + 1)
        (e.hom.f n f)).v i l hi x).v j m hj) y =
      Z.d (i + j + n) m
        (f.v (i + j) (i + j + n) rfl (ιTensorObj X Y i j (i + j) rfl (x ⊗ₜ[R] y))) -
      n.negOnePow • f.v (i + j + 1) m (by omega)
        (ιTensorObj X Y (i + 1) j (i + j + 1) (by omega) (X.d i (i + 1) x ⊗ₜ[R] y)) -
      (n + i).negOnePow • f.v (i + j + 1) m (by omega)
        (ιTensorObj X Y i (j + 1) (i + j + 1) (by omega) (x ⊗ₜ[R] Y.d j (j + 1) y))

def signedCurryingType : Prop :=
  ∀ {R : Type u} [CommRing R],
    ∃ e : ∀ X Y Z : compValue.{u} R,
        internalHomValue (tensorComplexValue X Y) Z ≅ internalHomValue X (internalHomValue Y Z),
      (∀ (X Y Z : compValue.{u} R) {n i j l m : ℤ} (hi : i + n = l) (hj : j + l = m)
          (f : Cochain (tensorComplexValue X Y) Z n) (x : X.X i) (y : Y.X j),
        (((e X Y Z).hom.f n f).v i l hi x).v j m hj y =
          f.v (i + j) m (by omega) (ιTensorObj X Y i j (i + j) rfl (x ⊗ₜ[R] y))) ∧
      (∀ {X X' Y Y' Z Z' : compValue.{u} R} (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z ⟶ Z'),
        internalHomMapValue (tensorMapValue a b) c ≫ (e X' Y' Z').hom =
          (e X Y Z).hom ≫ internalHomMapValue a (internalHomMapValue b c)) ∧
      ∀ X Y Z, curryingDifferential X Y Z (e X Y Z)

def closedAdjunctionsType : Prop :=
  ∀ {R : Type u} [CommRing R] (Y : compValue.{u} R),
    let q := quotientValue.{u} R
    ∃ (adj : tensorWithValue Y ⊣ homFromValue Y)
      (F G : homotopyValue.{u} R ⥤ homotopyValue.{u} R) (adjK : F ⊣ G)
      (left : q ⋙ F ≅ tensorWithValue Y ⋙ q) (right : q ⋙ G ≅ homFromValue Y ⋙ q),
      (∀ (X Z : compValue.{u} R) (f : tensorComplexValue X Y ⟶ Z) (i j : ℤ)
          (x : X.X i) (y : Y.X j),
        ((adj.homEquiv X Z f).f i x).v j (i + j) (add_comm j i) y =
          f.f (i + j) (ιTensorObj X Y i j (i + j) rfl (x ⊗ₜ[R] y))) ∧
      (∀ (Z : compValue.{u} R) (i j : ℤ) (f : (internalHomValue Y Z).X i) (y : Y.X j),
        (adj.counit.app Z).f (i + j)
          (ιTensorObj (internalHomValue Y Z) Y i j (i + j) rfl (f ⊗ₜ[R] y)) =
          f.v j (i + j) (add_comm j i) y) ∧
      ∀ (X Z : compValue.{u} R) (f : tensorComplexValue X Y ⟶ Z),
        adjK.homEquiv (q.obj X) (q.obj Z) (left.hom.app X ≫ q.map f) ≫ right.hom.app Z =
          q.map (adj.homEquiv X Z f)

end Specs.DerivedFormalization.CochainTensorHomAdjunction
