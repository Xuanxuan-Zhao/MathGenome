import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurAlgebras
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Strict descent data for an ordinary commutative algebra. -/

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace StrictModuleDataSpec

universe u v w u₁ u₂ u₃

noncomputable section

/-- Comparison of two successive scalar extensions with scalar extension along their
composite. The rings may have different universes. -/
def extendComp {R : Type u₁} {S : Type u₂} {T : Type u₃}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    ModuleCat.extendScalars.{u₁, u₃, max u₂ u₃ w} (g.comp f) ≅
      ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g :=
  (conjugateIsoEquiv ((ModuleCat.extendRestrictScalarsAdj.{max u₂ u₃ w, u₁, u₂} f).comp
    (ModuleCat.extendRestrictScalarsAdj.{max u₂ u₃ w, u₂, u₃} g))
    (ModuleCat.extendRestrictScalarsAdj.{max u₂ u₃ w, u₁, u₃} (g.comp f))).symm
      (ModuleCat.restrictScalarsComp f g).symm

/-- Scalar extension along equal maps, with the source and target fixed. -/
def extendCongr {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    {f g : R →+* S} (h : f = g) :
    ModuleCat.extendScalars.{u₁, u₂, w} f ≅ ModuleCat.extendScalars g := by
  subst h
  exact Iso.refl _

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

abbrev Power (n : ℕ) := AmitsurAlgebrasSpec.tensorPower A B n

abbrev factor {n : ℕ} (i : Fin n) := AmitsurAlgebrasSpec.factor A B i

/-- Scalar extension of a module from the factor at position `i`. -/
def atPosition {n : ℕ} (i : Fin n) :
    ModuleCat.{max u v w} B ⥤ ModuleCat.{max u v w} (Power A B n) :=
  ModuleCat.extendScalars (factor A B i).toRingHom

/-- Multiplication, induced by identifying both positions with the unique factor of `B`. -/
def diagonal : Power A B 2 →ₐ[A] B :=
  AmitsurAlgebrasSpec.liftFactors fun _ ↦ AlgHom.id A B

/-- Extension to the ordered factor positions prescribed by `f`. -/
def along {m n : ℕ} (f : Fin m → Fin n) :
    ModuleCat.{max u v w} (Power A B m) ⥤ ModuleCat.{max u v w} (Power A B n) :=
  ModuleCat.extendScalars (AmitsurAlgebrasSpec.map (A := A) (B := B) f).toRingHom

private theorem lift_on_factor {n : ℕ} {D : Type*} [CommRing D] [Algebra A D]
    (f : Fin n → B →ₐ[A] D) (i : Fin n) :
    (AmitsurAlgebrasSpec.liftFactors f).comp (factor A B i) = f i := by
  ext b
  change PiTensorProduct.lift _ (PiTensorProduct.tprod A (Pi.mulSingle (M := fun _ : Fin n ↦ B) i b)) = _
  rw [PiTensorProduct.lift.tprod]
  change (∏ j, f j (Pi.mulSingle (M := fun _ : Fin n ↦ B) i b j)) = _
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ h
    simp [Pi.mulSingle_eq_of_ne h]
  · simp

/-- Extending a positioned module along a map of positions moves it to the image position. -/
def alongPosition {m n : ℕ} (f : Fin m → Fin n) (i : Fin m) :
    atPosition.{u, v, w} A B (f i) ≅ atPosition A B i ⋙ along A B f :=
  extendCongr (congrArg AlgHom.toRingHom
    (lift_on_factor A B (fun j ↦ factor A B (f j)) i).symm) ≪≫
    extendComp _ _

/-- The diagonal pullback at either position is canonically the original module. -/
def diagonalPosition (i : Fin 2) :
    atPosition.{u, v, w} A B i ⋙ ModuleCat.extendScalars (diagonal A B).toRingHom ≅
      𝟭 (ModuleCat.{max u v w} B) :=
  (extendComp _ _).symm ≪≫
    extendCongr (congrArg AlgHom.toRingHom (lift_on_factor A B _ i)) ≪≫
    ModuleCat.extendScalarsId.{v, max u v w} B

abbrev Theta (N : ModuleCat.{max u v w} B) :=
  (atPosition A B (0 : Fin 2)).obj N ≅ (atPosition A B (1 : Fin 2)).obj N

variable {A B}

/-- The transported diagonal of the comparison isomorphism. -/
def diagonalTheta {N : ModuleCat.{max u v w} B} (θ : Theta A B N) : N ≅ N :=
  (diagonalPosition A B 0).symm.app N ≪≫
    (ModuleCat.extendScalars (diagonal A B).toRingHom).mapIso θ ≪≫
    (diagonalPosition A B 1).app N

/-- Extend the comparison isomorphism along the ordered pair `(f 0, f 1)`. -/
def alongTheta {n : ℕ} {N : ModuleCat.{max u v w} B}
    (f : Fin 2 → Fin n) (θ : Theta A B N) :
    (atPosition A B (f 0)).obj N ≅ (atPosition A B (f 1)).obj N :=
  (alongPosition A B f 0).app N ≪≫ (along A B f).mapIso θ ≪≫
    (alongPosition A B f 1).symm.app N

/-- The pair of positions increasingly enumerated by skipping `i`. -/
abbrev pair (i : Fin 3) : Fin 2 → Fin 3 := i.succAbove

variable (A B)

/-- A module with an isomorphism from position 0 to position 1, normalized on the
diagonal and satisfying the cocycle on positions `(0,1,2)`. -/
structure Datum where
  module : ModuleCat.{max u v w} B
  theta : Theta A B module
  normalized : (diagonalTheta theta).hom = 𝟙 module
  cocycle : (alongTheta (pair 2) theta).hom ≫ (alongTheta (pair 0) theta).hom =
    (alongTheta (pair 1) theta).hom

variable {A B}

/-- A map of the underlying modules whose two scalar extensions commute with `theta`. -/
@[ext]
structure Hom (X Y : Datum.{u, v, w} A B) where
  hom : X.module ⟶ Y.module
  comm : (atPosition A B (0 : Fin 2)).map hom ≫ Y.theta.hom =
    X.theta.hom ≫ (atPosition A B (1 : Fin 2)).map hom

/-- Identity and composition are those on the underlying modules. -/
@[instance_reducible]
def category : Category (Datum.{u, v, w} A B) where
  Hom := Hom
  id X := ⟨𝟙 X.module, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    simp only [Functor.map_comp, Category.assoc]
    rw [g.comm, ← Category.assoc, f.comm, Category.assoc]⟩
  id_comp f := Hom.ext (by simp)
  comp_id f := Hom.ext (by simp)
  assoc f g h := Hom.ext (by simp [Category.assoc])

attribute [local instance] category

/-- The functor forgetting the comparison isomorphism. -/
def forget : Datum.{u, v, w} A B ⥤ ModuleCat.{max u v w} B where
  obj X := X.module
  map f := f.hom

/-- The ordered binary and ternary algebra identifications. The three ternary insertions and
the binary multiplication consequently have the expected pure-tensor formulas. -/
def OrderedPowers : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∃ (e₂ : B ⊗[A] B ≃ₐ[A] Power A B 2)
      (e₃ : (B ⊗[A] B) ⊗[A] B ≃ₐ[A] Power A B 3),
      (∀ a b, e₂ (a ⊗ₜ[A] b) = factor A B 0 a * factor A B 1 b) ∧
      (∀ a b c, e₃ ((a ⊗ₜ[A] b) ⊗ₜ[A] c) =
        factor A B 0 a * factor A B 1 b * factor A B 2 c) ∧
      (∀ a b, diagonal A B (e₂ (a ⊗ₜ[A] b)) = a * b) ∧
      (∀ a b,
        AmitsurAlgebrasSpec.map (pair 2) (e₂ (a ⊗ₜ[A] b)) =
          e₃ ((a ⊗ₜ[A] b) ⊗ₜ[A] 1) ∧
        AmitsurAlgebrasSpec.map (pair 1) (e₂ (a ⊗ₜ[A] b)) =
          e₃ ((a ⊗ₜ[A] 1) ⊗ₜ[A] b) ∧
        AmitsurAlgebrasSpec.map (pair 0) (e₂ (a ⊗ₜ[A] b)) =
          e₃ ((1 ⊗ₜ[A] a) ⊗ₜ[A] b))

variable (A B)

/-- The underlying base-ring module used in ordinary tensor products. -/
abbrev restrict (N : ModuleCat.{max u v w} B) :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj N

/-- The two binary pullbacks are the ordinary tensors with their respective
factor actions. The displayed scalar-action formulas determine the actions
on the entire tensor products by additivity. -/
def BinaryModuleModels : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∀ N : ModuleCat.{max u v w} B,
      ∃ (e₀ : ↑((atPosition A B (0 : Fin 2)).obj N) ≃+ (restrict A B N ⊗[A] B))
        (e₁ : ↑((atPosition A B (1 : Fin 2)).obj N) ≃+ (B ⊗[A] restrict A B N)),
        (∀ b (x : N),
          e₀.symm ((show restrict A B N from x) ⊗ₜ[A] b) =
            factor A B (1 : Fin 2) b ⊗ₜ[B, (factor A B (0 : Fin 2)).toRingHom] x) ∧
        (∀ b (x : N),
          e₁.symm (b ⊗ₜ[A] (show restrict A B N from x)) =
            factor A B (0 : Fin 2) b ⊗ₜ[B, (factor A B (1 : Fin 2)).toRingHom] x) ∧
        (∀ a b c (x : N),
          e₀ ((factor A B 0 a * factor A B 1 b : Power A B 2) • e₀.symm ((show restrict A B N from x) ⊗ₜ[A] c)) =
            ((show restrict A B N from a • x) ⊗ₜ[A] (b * c))) ∧
        (∀ a b c (x : N),
          e₁ ((factor A B 0 a * factor A B 1 b : Power A B 2) • e₁.symm (c ⊗ₜ[A] (show restrict A B N from x))) =
            ((a * c) ⊗ₜ[A] (show restrict A B N from b • x)))

set_option linter.checkUnivs false in
private def declarationType {T : Sort*} (_ : T) := T

section

set_option linter.checkUnivs false

def AtPositionType := declarationType (@atPosition.{u, v, w})
def DiagonalType := declarationType (@diagonal.{u, v})
def AlongType := declarationType (@along.{u, v, w})
def AlongPositionType := declarationType (@alongPosition.{u, v, w})
def DiagonalPositionType := declarationType (@diagonalPosition.{u, v, w})
def ThetaType := declarationType (@Theta.{u, v, w})
def DiagonalThetaType := declarationType (@diagonalTheta.{u, v, w})
def AlongThetaType := declarationType (@alongTheta.{u, v, w})
abbrev datum := @Datum.{u, v, w}
abbrev hom := @Hom.{u, v, w}

def DatumType := declarationType (@Datum.{u, v, w})
def HomType := declarationType (@Hom.{u, v, w})
def CategoryType := declarationType (@category.{u, v, w})
def ForgetType := declarationType (@forget.{u, v, w})
def RestrictType := declarationType (@restrict.{u, v, w})

end

end

end StrictModuleDataSpec
