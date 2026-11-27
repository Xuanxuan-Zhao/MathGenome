import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedHom
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.PerfectHomBaseChange

/-! Signed Hom on the ordinary and dg models of the affine Amitsur columns. -/

namespace Specs.DerivedFormalization.Affine.OrdinaryDGHomComparison

open CategoryTheory Opposite CochainComplex.HomComplex
open scoped TensorProduct
open _root_.DerivedFormalization _root_.DerivedFormalization.Affine
open Cochains (compValue derivedValue homotopyValue qValue qhValue quotientValue)
open CochainModels (internalHomValue internalHomMapValue isKProjectiveValue)
open DG.HomComplex (gradedHom component homotopyClass)
open DG.KProjective (isKProjective)
open DG.Derived (HomotopyCategoryLaws)
open DG.DerivedKProjective (derivedCategoryInstance)
open CotangentComplex (liftCDGA cdgaLift oneObject)
open Descent.PerfectHomBaseChange (extend extendCochain comparison changeCoefficients
  changeHomCoefficients)

noncomputable section

universe u v t
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

abbrev ordinary (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] :=
  NonpositiveCDGA.ordinary (CommAlgCat.of k R)

/-- The stalk uses the coefficient lift of the original algebra in A08. -/
abbrev transported (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] :=
  liftCDGA.{u,v,t} (ordinary k R)

variable {k : Type u} [Field k] [CharZero k]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

abbrev transportedMap (f : R →ₐ[k] S) :
    transported.{u,v,t} k R ⟶ transported.{u,v,t} k S :=
  (cdgaLift.{u,v,t} k).map (NonpositiveCDGA.ordinaryMap (CommAlgCat.ofHom f))

abbrev restrictComplex (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R] :=
  (ModuleCat.restrictScalars.{max v t} (algebraMap k R)).mapHomologicalComplex (.up ℤ)

local instance : CommRing (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instCommRingDegreeZero _
local instance : Algebra k (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instAlgebraDegreeZero _

/-- Input from the strict degree-zero comparison at the common bound. -/
structure StrictComparison (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] where
  scalar : R ≃ₐ[k] (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero
  scalar_apply (r : R) : scalar r = ULift.up r
  strict : compValue.{max v t} R ≌ (transported.{u,v,t} k R).Module
  terms (X : compValue.{max v t} R) :
    (restrictComplex.{u,v,t} k R).obj X ≅ (strict.functor.obj X).complex ()
  terms_natural {X Y : compValue.{max v t} R} (f : X ⟶ Y) :
    (restrictComplex.{u,v,t} k R).map f ≫ (terms Y).hom =
      (terms X).hom ≫ (strict.functor.map f).app ()
  action (X : compValue.{max v t} R) (i : ℤ) (r : R) (x : X.X i) :
    Tensor.act (strict.functor.obj X) i 0 i (add_zero i) ((terms X).hom.f i x) (scalar r) =
      (terms X).hom.f i (r • x)

/-- The strict isomorphism conjugates every homogeneous map, with its
evaluation, and intertwines the actual pre- and postcomposition maps. -/
structure StrictHom (E : StrictComparison.{u,v,t} k R) where
  iso (X Y : compValue.{max v t} R) :
    E.strict.functor.obj (internalHomValue X Y) ≅
      DerivedHom.internalHom (E.strict.functor.obj X) (E.strict.functor.obj Y)
  evaluation (X Y : compValue.{max v t} R) (n i j : ℤ) (h : i + n = j)
      (f : Cochain X Y n) (x : X.X i) :
    component (((iso X Y).hom.app ()).f n ((E.terms (internalHomValue X Y)).hom.f n f))
        () i j h ((E.terms X).hom.f i x) =
      (E.terms Y).hom.f j (f.v i j h x)
  naturality
      (S : DerivedHom.HomActions (transported.{u,v,t} k R).toCommDGAlgebra)
      (_hS : DerivedHom.HomActionLaws (transported.{u,v,t} k R).toCommDGAlgebra S)
      {X X' Y Y' : compValue.{max v t} R} (f : X' ⟶ X) (g : Y ⟶ Y') :
    E.strict.functor.map (internalHomMapValue f g) ≫ (iso X' Y').hom =
      (iso X Y).hom ≫ S.pre (E.strict.functor.obj Y) (E.strict.functor.map f) ≫
        S.post (E.strict.functor.obj X') (E.strict.functor.map g)

abbrev StrictHom.chain {E : StrictComparison.{u,v,t} k R} (I : StrictHom E)
    (X Y : compValue.{max v t} R) :=
  (E.terms (internalHomValue X Y)).hom ≫ (I.iso X Y).hom.app ()

def StrictHomComparison : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {R : Type v} [CommRing R] [Algebra k R]
    (E : StrictComparison.{u,v,t} k R), Nonempty (StrictHom E)

abbrev dgHomotopy (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] :=
  DG.AmbientDerived.homotopyCategory.{u,v,0,t} (oneObject (ordinary k R))

abbrev dgDerived (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R]
    (h : HomotopyCategoryLaws (oneObject (transported.{u,v,t} k R))) :=
  DG.AmbientDerived.derivedCategory.{u,v,0,t} (oneObject (ordinary k R)) h

/-- Compare U08a with ADerivedHom on the supplied homotopy and derived
equivalences. The component equation uses the specified quotient square
and the factorization of the dg bifunctor on K-projective models. -/
def LocalizedHomComparison : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {R : Type v} [CommRing R] [Algebra k R]
    (E : StrictComparison.{u,v,t} k R) (I : StrictHom E)
    (h : HomotopyCategoryLaws (oneObject (transported.{u,v,t} k R))),
    let A := (transported.{u,v,t} k R).toCommDGAlgebra
    let G := oneObject (transported.{u,v,t} k R)
    letI := DG.Derived.homotopyCategory G h
    letI := derivedCategoryInstance G h
    let Kd := dgHomotopy.{u,v,t} k R
    let Dd := dgDerived.{u,v,t} k R h
    let Q := DG.AmbientDerived.quotient.{u,v,0,t} (oneObject (ordinary k R)) h
    let J : DerivedHom.Kp A h ⥤ Kd := (DG.DerivedKProjective.kProjectiveObjects G).ι
    let Qp := DG.DerivedKProjective.restrictedLocalization G h
    ∀ (K : homotopyValue.{max v t} R ≌ Kd)
      (D : derivedValue.{max v t} R ≌ Dd)
      (a : ∀ X : compValue.{max v t} R, K.functor.obj ((quotientValue R).obj X) ≅
        (E.strict.functor.obj X : Kd))
      (τ : qhValue R ⋙ D.functor ≅ K.functor ⋙ Q),
      (∀ {X Y : compValue.{max v t} R} (f : X ⟶ Y),
        K.functor.map ((quotientValue R).map f) ≫ (a Y).hom =
          (a X).hom ≫ homotopyClass (E.strict.functor.map f)) →
      ∀ (projective : ∀ (X : compValue.{max v t} R),
        isKProjectiveValue X → isKProjective (E.strict.functor.obj X))
        (O : DerivedHomModels.Models.{v,max v t} R)
        (S : DerivedHom.HomActions A) (H : Kdᵒᵖ × Kd ⥤ Kd) (F : Ddᵒᵖ × Dd ⥤ Dd),
        DerivedHom.HomActionLaws A S →
        ∀ (objH : ∀ (X Y : A.Module), H.obj (op X, Y) = DerivedHom.internalHom X Y),
        (∀ {X X' Y Y' : A.Module} (f : X' ⟶ X) (g : Y ⟶ Y'),
          let f₀ : @Quiver.Hom Kd (DG.Derived.homotopyCategory G h).toQuiver X' X :=
            homotopyClass f
          let g₀ : @Quiver.Hom Kd (DG.Derived.homotopyCategory G h).toQuiver Y Y' :=
            homotopyClass g
          HEq (H.map (Prod.mkHom f₀.op g₀)) (homotopyClass (S.pre Y f ≫ S.post X' g))) →
        ∀ (σ : Qp.op.prod Q ⋙ F ≅ J.op.prod (𝟭 Kd) ⋙ H ⋙ Q),
          ∃ β : DerivedHomModels.rHomValue O ⋙ D.functor ≅ D.functor.op.prod D.functor ⋙ F,
            ∀ (X Y : compValue.{max v t} R) (hX : isKProjectiveValue X),
              let X₀ : DerivedHomModels.Representative ((qValue R).obj X) :=
                ⟨(quotientValue R).obj X, Iso.refl _⟩
              let Y₀ : DerivedHomModels.Representative ((qValue R).obj Y) :=
                ⟨(quotientValue R).obj Y, Iso.refl _⟩
              let ρ (V : compValue.{max v t} R) :=
                τ.app ((quotientValue R).obj V) ≪≫ Q.mapIso (a V)
              let U : DerivedHom.Kp A h := ⟨E.strict.functor.obj X, projective X hX⟩
              let V : Kd := E.strict.functor.obj Y
              let pair := ((ρ X).symm.op).prod (ρ Y)
              D.functor.map (eqToHom (O.hom.obj_eq X₀.obj Y₀.obj).symm ≫
                  DerivedHomModels.modelMap O X₀ Y₀) ≫
                β.hom.app (op ((qValue R).obj X), (qValue R).obj Y) ≫
                F.map pair.hom ≫ (σ.app (op U, V)).hom ≫
                Q.map (eqToHom (objH (E.strict.functor.obj X) (E.strict.functor.obj Y))) =
              (ρ (internalHomValue X Y)).hom ≫ Q.map (homotopyClass (I.iso X Y).hom)

section Amitsur

variable {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
variable [IsScalarTower k A B] [IsScalarTower k A C]

/-- The original rings of the A12 columns, before any coefficient lift. -/
abbrev ColumnRing (A B C : Type v) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (p : ℕ) :=
  B ⊗[A] AmitsurAlgebrasSpec.degree A C p

local notation "Bₚ" => ColumnRing A B C

abbrev columnMap {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) : Bₚ p →ₐ[B] Bₚ q :=
  Algebra.TensorProduct.map (AlgHom.id B B) (AmitsurAlgebrasSpec.map f)

abbrev column (X : compValue.{max v t} B) (p : ℕ) : compValue.{max v t} (Bₚ p) :=
  (extend.{v,v,max v t} B (Bₚ p)).obj X

abbrev columnCochainMap (X : compValue.{max v t} B) {p q : ℕ}
    (f : Fin (p + 1) → Fin (q + 1)) :=
  let φ : Bₚ p →ₐ[B] Bₚ q := columnMap f
  letI : Algebra (Bₚ p) (Bₚ q) := φ.toRingHom.toAlgebra
  letI : IsScalarTower B (Bₚ p) (Bₚ q) := IsScalarTower.of_algHom φ
  changeCoefficients.{v,v,max v t} B (Bₚ p) (Bₚ q) X

abbrev columnHomMap (P X : compValue.{max v t} B) {p q : ℕ}
    (f : Fin (p + 1) → Fin (q + 1)) :=
  let φ : Bₚ p →ₐ[B] Bₚ q := columnMap f
  letI : Algebra (Bₚ p) (Bₚ q) := φ.toRingHom.toAlgebra
  letI : IsScalarTower B (Bₚ p) (Bₚ q) := IsScalarTower.of_algHom φ
  changeHomCoefficients.{v,v,max v t} B (Bₚ p) (Bₚ q) P X

def BoundedFiniteProjective (P : compValue.{max v t} B) : Prop :=
  (∃ L U : ℤ, ∀ i : ℤ, (i < L ∨ U < i) → Subsingleton (P.X i)) ∧
  (∀ i : ℤ, Module.Finite B (P.X i)) ∧ ∀ i : ℤ, Module.Projective B (P.X i)

abbrev dgHomColumn (F : ∀ p : ℕ, StrictComparison.{u,v,t} k (Bₚ p))
    (p : ℕ) (P X : compValue.{max v t} B) : (transported.{u,v,t} k (Bₚ p)).Module :=
  DerivedHom.internalHom ((F p).strict.functor.obj (column (A := A) (C := C) P p))
    ((F p).strict.functor.obj (column (A := A) (C := C) X p))

/-- The original Hom and every strict column are joined by dg maps over the
transported ring maps. Their underlying chain maps are the conjugates of
the F08a maps in every degree. -/
structure HomColumns (E : StrictComparison.{u,v,t} k B) (I : StrictHom E)
    (F : ∀ p : ℕ, StrictComparison.{u,v,t} k (Bₚ p)) (J : ∀ p : ℕ, StrictHom (F p)) where
  augmentation (p : ℕ) (P X : compValue.{max v t} B) :
    DerivedHom.internalHom (E.strict.functor.obj P) (E.strict.functor.obj X) ⟶
      Tensor.restrict (transportedMap (IsScalarTower.toAlgHom k B (Bₚ p)) :
        (transported.{u,v,t} k B).toCommDGAlgebra ⟶
          (transported.{u,v,t} k (Bₚ p)).toCommDGAlgebra)
        (dgHomColumn F p P X)
  augmentation_ordinary (p : ℕ) (P X : compValue.{max v t} B)
      (n : ℤ) (z : Cochain P X n) :
    ((augmentation p P X).app ()).f n ((I.chain P X).f n z) =
      ((J p).chain (column (A := A) (C := C) P p) (column (A := A) (C := C) X p)).f n (extendCochain (Bₚ p) n z)
  augmentation_evaluation (p : ℕ) (P X : compValue.{max v t} B)
      (n i j : ℤ) (h : i + n = j) (z : Cochain P X n) (s : Bₚ p) (x : P.X i) :
    component (((augmentation p P X).app ()).f n ((I.chain P X).f n z)) () i j h
      (((F p).terms (column (A := A) (C := C) P p)).hom.f i (s ⊗ₜ[B] x)) =
      ((F p).terms (column (A := A) (C := C) X p)).hom.f j (s ⊗ₜ[B] z.v i j h x)
  map {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max v t} B) :
    dgHomColumn F p P X ⟶
      Tensor.restrict (transportedMap ((columnMap f : Bₚ p →ₐ[B] Bₚ q).restrictScalars k) :
        (transported.{u,v,t} k (Bₚ p)).toCommDGAlgebra ⟶
          (transported.{u,v,t} k (Bₚ q)).toCommDGAlgebra)
        (dgHomColumn F q P X)
  map_ordinary {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max v t} B)
      (n : ℤ) (z : Cochain (column (A := A) (C := C) P p) (column (A := A) (C := C) X p) n) :
    ((map f P X).app ()).f n (((J p).chain (column (A := A) (C := C) P p) (column (A := A) (C := C) X p)).f n z) =
      ((J q).chain (column (A := A) (C := C) P q) (column (A := A) (C := C) X q)).f n
        ((columnHomMap (A := A) (C := C) P X f).f n z)
  map_evaluation {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max v t} B)
      (n i j : ℤ) (h : i + n = j) (z : Cochain (column (A := A) (C := C) P p) (column (A := A) (C := C) X p) n)
      (x : (column (A := A) (C := C) P p).X i) :
    component
      (((map f P X).app ()).f n (((J p).chain (column (A := A) (C := C) P p) (column (A := A) (C := C) X p)).f n z)) () i j h
      (((F q).terms (column (A := A) (C := C) P q)).hom.f i ((columnCochainMap (A := A) (C := C) P f).f i x)) =
      ((F q).terms (column (A := A) (C := C) X q)).hom.f j
        ((columnCochainMap (A := A) (C := C) X f).f j (z.v i j h x))
  map_id (p : ℕ) (P X : compValue.{max v t} B) :
    (map (id : Fin (p + 1) → Fin (p + 1)) P X).app () = 𝟙 _
  map_comp {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (g : Fin (q + 1) → Fin (r + 1))
      (P X : compValue.{max v t} B) :
    (map (g ∘ f) P X).app () = (map f P X).app () ≫ (map g P X).app ()
  augmentation_comp {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max v t} B) :
    (augmentation p P X).app () ≫ (map f P X).app () = (augmentation q P X).app ()
  baseChangeIso (P X : compValue.{max v t} B) (_hP : BoundedFiniteProjective P) (p : ℕ) :
    (F p).strict.functor.obj (column (A := A) (C := C) (internalHomValue P X) p) ≅ dgHomColumn F p P X
  baseChange_hom (P X : compValue.{max v t} B) (hP : BoundedFiniteProjective P) (p : ℕ) :
    (baseChangeIso P X hP p).hom =
      (F p).strict.functor.map (comparison (Bₚ p) P X) ≫
        ((J p).iso (column (A := A) (C := C) P p) (column (A := A) (C := C) X p)).hom
  baseChange_evaluation (P X : compValue.{max v t} B) (hP : BoundedFiniteProjective P) (p : ℕ)
      (n i j : ℤ) (h : i + n = j) (s s' : Bₚ p) (z : Cochain P X n) (x : P.X i) :
    component
      (((baseChangeIso P X hP p).hom.app ()).f n
        (((F p).terms (column (A := A) (C := C) (internalHomValue P X) p)).hom.f n (s ⊗ₜ[B] z)))
      () i j h (((F p).terms (column (A := A) (C := C) P p)).hom.f i (s' ⊗ₜ[B] x)) =
      ((F p).terms (column (A := A) (C := C) X p)).hom.f j ((s * s') ⊗ₜ[B] z.v i j h x)
  baseChange_coface {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max v t} B)
      (hP : BoundedFiniteProjective P) (n : ℤ) (z : (column (A := A) (C := C) (internalHomValue P X) p).X n) :
    ((map f P X).app ()).f n
      (((baseChangeIso P X hP p).hom.app ()).f n
        (((F p).terms (column (A := A) (C := C) (internalHomValue P X) p)).hom.f n z)) =
      (((baseChangeIso P X hP q).hom.app ()).f n
        (((F q).terms (column (A := A) (C := C) (internalHomValue P X) q)).hom.f n
          ((columnCochainMap (A := A) (C := C) (internalHomValue P X) f).f n z)))

def AmitsurHomComparison : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
    [IsScalarTower k A B] [IsScalarTower k A C]
    (E : StrictComparison.{u,v,t} k B) (I : StrictHom E)
    (F : ∀ p : ℕ, StrictComparison.{u,v,t} k (ColumnRing A B C p))
    (J : ∀ p : ℕ, StrictHom (F p)),
    Nonempty (HomColumns (A := A) (C := C) E I F J)

end Amitsur

end

end Specs.DerivedFormalization.Affine.OrdinaryDGHomComparison
