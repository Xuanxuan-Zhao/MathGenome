import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainRingTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.PerfectHomBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! The ordinary Amitsur diagram and its cochain models under change of ring representatives. -/

open CategoryTheory
open scoped TensorProduct

namespace Specs.DerivedFormalization.Descent.AmitsurRingTransport

noncomputable section

universe u v w t x y i j
set_option linter.checkUnivs false

open Cochains (compValue derivedValue qValue)
open CochainModels (internalHomValue internalHomMapValue)
open CochainComplex.HomComplex (Cochain)
open PerfectHomBaseChange (extend extendCochain changeCoefficients changeHomCoefficients comparison)

attribute [local instance] HasDerivedCategory.standard

abbrev CP (A : Type u) (C : Type v) [CommRing A] [CommRing C] [Algebra A C] (p : ℕ) :=
  AmitsurAlgebrasSpec.degree A C p

abbrev BP (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (p : ℕ) :=
  B ⊗[A] CP A C p

abbrev baseMap {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (p : ℕ) :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[B] BP A B C p)

abbrev columnMap {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) : BP A B C p →ₐ[B] BP A B C q :=
  Algebra.TensorProduct.map (AlgHom.id B B) (AmitsurAlgebrasSpec.map f)

section RingEquivalence

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (e : R ≃+* S)

/-- Exact restriction along the inverse ring equivalence at an independent term level. -/
abbrev moduleChange : ModuleCat.{t} R ≌ ModuleCat.{t} S :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm

abbrev changeRepresentative : compValue.{t} R ⥤ compValue.{t} S :=
  (moduleChange.{u,v,t} e).functor.mapHomologicalComplex (.up ℤ)

abbrev changeDerivedRepresentative : derivedValue.{t} R ⥤ derivedValue.{t} S :=
  (moduleChange.{u,v,t} e).functor.mapDerivedCategory

/-- The quotient square for this very restriction functor on cochains. -/
def quotientSquare : qValue.{t} R ⋙ changeDerivedRepresentative.{u,v,t} e ≅
    changeRepresentative.{u,v,t} e ⋙ qValue.{t} S :=
  (moduleChange.{u,v,t} e).functor.mapDerivedCategoryFactors

end RingEquivalence

section OriginalRings

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
variable {S : ℕ → Type w} {S' : ℕ → Type v}
variable [∀ p, CommRing (S p)] [∀ p, CommRing (S' p)]
variable [∀ p, Algebra R (S p)] [∀ p, Algebra R' (S' p)]

abbrev scalarColumnMap {p q : ℕ} (f : S p →ₐ[R] S q) (X : compValue.{t} R) :=
  letI : Algebra (S p) (S q) := f.toRingHom.toAlgebra
  letI : IsScalarTower R (S p) (S q) := IsScalarTower.of_algHom f
  changeCoefficients.{u,w,t} R (S p) (S q) X

abbrev homColumnMap {p q : ℕ} (f : S p →ₐ[R] S q)
    (P X : compValue.{t} R) :=
  letI : Algebra (S p) (S q) := f.toRingHom.toAlgebra
  letI : IsScalarTower R (S p) (S q) := IsScalarTower.of_algHom f
  changeHomCoefficients.{u,w,t} R (S p) (S q) P X

/-- An identification of the original-ring complexes with the ones computed
over representatives. The original localization and both Hom diagrams use
the same chain equivalences. -/
structure OriginalRingDiagramComparison
    (e : R ≃+* R') (eS : ∀ p, S p ≃+* S' p)
    (f : ∀ {p q : ℕ}, (Fin (p + 1) → Fin (q + 1)) → S p →ₐ[R] S q)
    (g : ∀ {p q : ℕ}, (Fin (p + 1) → Fin (q + 1)) → S' p →ₐ[R'] S' q) where
  localizationEquivalence : (changeDerivedRepresentative.{u,v,max u v w t} e).IsEquivalence
  originalModel (L' : compValue.{max u v w t} R') :
    ∃ (L : compValue.{max u v w t} R)
      (c : (changeRepresentative.{u,v,max u v w t} e).obj L ≅ L')
      (a : (changeDerivedRepresentative.{u,v,max u v w t} e).obj ((qValue R).obj L) ≅ (qValue R').obj L'),
      a.hom = ((quotientSquare e).app L).hom ≫ (qValue R').map c.hom
  extendIso (p : ℕ) :
    extend.{u,w,max u v w t} R (S p) ⋙ changeRepresentative.{w,v,max u v w t} (eS p) ≅
      changeRepresentative.{u,v,max u v w t} e ⋙ extend.{v,v,max u v w t} R' (S' p)
  extend_tmul (p : ℕ) (X : compValue.{max u v w t} R) (i : ℤ) (s : S p) (x : X.X i) :
    ((extendIso p).hom.app X).f i (s ⊗ₜ[R] x) =
      eS p s ⊗ₜ[R'] (show ((changeRepresentative.{u,v,max u v w t} e).obj X).X i from x)
  extend_map {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) (X : compValue.{max u v w t} R)
      (n : ℤ) (z : ((extend.{u,w,max u v w t} R (S p)).obj X).X n) :
    let F := changeRepresentative.{u,v,max u v w t} e
    ((extendIso q).hom.app X).f n ((scalarColumnMap (f a) X).f n z) =
      (scalarColumnMap (g a) (F.obj X)).f n (((extendIso p).hom.app X).f n z)
  homIso (P X : compValue.{max u v w t} R) :
    (changeRepresentative.{u,v,max u v w t} e).obj (internalHomValue P X) ≅
      internalHomValue ((changeRepresentative.{u,v,max u v w t} e).obj P)
        ((changeRepresentative.{u,v,max u v w t} e).obj X)
  hom_evaluation (P X : compValue.{max u v w t} R) (n i j : ℤ) (h : i + n = j)
      (z : Cochain P X n) (x : P.X i) :
    (((homIso P X).hom.f n z).v i j h) x = z.v i j h x
  hom_natural {P P' X X' : compValue.{max u v w t} R} (a : P' ⟶ P) (b : X ⟶ X') :
    let F := changeRepresentative.{u,v,max u v w t} e
    F.map (internalHomMapValue a b) ≫ (homIso P' X').hom =
      (homIso P X).hom ≫ internalHomMapValue (F.map a) (F.map b)
  homColumnIso (p : ℕ) (P X : compValue.{max u v w t} R) :
    let E := extend.{u,w,max u v w t} R (S p)
    let E' := extend.{v,v,max u v w t} R' (S' p)
    let C := changeRepresentative.{u,v,max u v w t} e
    (changeRepresentative.{w,v,max u v w t} (eS p)).obj (internalHomValue (E.obj P) (E.obj X)) ≅
      internalHomValue (E'.obj (C.obj P)) (E'.obj (C.obj X))
  homColumn_evaluation (p : ℕ) (P X : compValue.{max u v w t} R) (n i j : ℤ) (h : i + n = j)
      (z : Cochain ((extend.{u,w,max u v w t} R (S p)).obj P)
        ((extend.{u,w,max u v w t} R (S p)).obj X) n)
      (x : ((extend.{u,w,max u v w t} R (S p)).obj P).X i) :
    (((homColumnIso p P X).hom.f n z).v i j h) (((extendIso p).hom.app P).f i x) =
      ((extendIso p).hom.app X).f j (z.v i j h x)
  homColumn_natural (p : ℕ) {P P' X X' : compValue.{max u v w t} R}
      (a : P' ⟶ P) (b : X ⟶ X') :
    let E := extend.{u,w,max u v w t} R (S p)
    let E' := extend.{v,v,max u v w t} R' (S' p)
    let F := changeRepresentative.{u,v,max u v w t} e
    (changeRepresentative.{w,v,max u v w t} (eS p)).map
        (internalHomMapValue (E.map a) (E.map b)) ≫ (homColumnIso p P' X').hom =
      (homColumnIso p P X).hom ≫ internalHomMapValue (E'.map (F.map a)) (E'.map (F.map b))
  baseChangeComparison (p : ℕ) (P X : compValue.{max u v w t} R) :
    let E' := extend.{v,v,max u v w t} R' (S' p)
    let F := changeRepresentative.{u,v,max u v w t} e
    (changeRepresentative.{w,v,max u v w t} (eS p)).map (comparison (S p) P X) ≫
        (homColumnIso p P X).hom =
      (extendIso p).hom.app (internalHomValue P X) ≫ E'.map (homIso P X).hom ≫
        comparison (S' p) (F.obj P) (F.obj X)
  augmentation (p : ℕ) (P X : compValue.{max u v w t} R) (n : ℤ) (z : Cochain P X n) :
    (homColumnIso p P X).hom.f n (extendCochain (S p) n z) =
      extendCochain (S' p) n ((homIso P X).hom.f n z)
  cofaces {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) (P X : compValue.{max u v w t} R)
      (n : ℤ) (z : Cochain ((extend.{u,w,max u v w t} R (S p)).obj P)
        ((extend.{u,w,max u v w t} R (S p)).obj X) n) :
    let F := changeRepresentative.{u,v,max u v w t} e
    (homColumnIso q P X).hom.f n ((homColumnMap.{u,w,max u v w t} (f a) P X).f n z) =
      (homColumnMap.{v,v,max u v w t} (g a) (F.obj P) (F.obj X)).f n
        ((homColumnIso p P X).hom.f n z)

end OriginalRings

/-- Lift each original input over its own ring to the bound containing both
original term universes and the common ring universe. -/
abbrev liftInput {R : Type u} [CommRing R] (X : compValue.{i} R) : compValue.{max i t} R :=
  (CochainCoefficientLift.lift.{t,i} R).obj X

/-- Rings starting at independent levels admit common representatives of the
whole Amitsur diagram. The term universe contains the ring universes, both
original term universes `i` and `j`, and the enlargement parameter `t`.
The model and naturality comparisons apply to every pair of cochains at
that bound, including the same-ring lifts of the original inputs via `liftInput`. -/
def RingDiagramTransport : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (A : Type v) (B : Type x) (C : Type y) [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A B] [Algebra A C]
    [IsScalarTower k A B] [IsScalarTower k A C] [Module.FaithfullyFlat A C],
    ∃ (A' B' C' : CommAlgCat.{max u v x y} k)
      (eA : A ≃ₐ[k] A') (eB : B ≃ₐ[k] B') (eC : C ≃ₐ[k] C')
      (f : A' →ₐ[k] B') (g : A' →ₐ[k] C'),
      (∀ a : A, f (eA a) = eB (algebraMap A B a)) ∧
      (∀ a : A, g (eA a) = eC (algebraMap A C a)) ∧
      letI : Algebra A' B' := f.toRingHom.toAlgebra
      letI : Algebra A' C' := g.toRingHom.toAlgebra
      letI : IsScalarTower k A' B' := IsScalarTower.of_algHom f
      letI : IsScalarTower k A' C' := IsScalarTower.of_algHom g
      Module.FaithfullyFlat A' C' ∧
      ∃ (eCP : ∀ p : ℕ, CP A C p ≃ₐ[k] CP A' C' p)
        (eBP : ∀ p : ℕ, BP A B C p ≃ₐ[k] BP A' B' C' p),
        (∀ (p : ℕ) (i : Fin (p + 1)) (c : C),
          eCP p (AmitsurAlgebrasSpec.factor A C i c) = AmitsurAlgebrasSpec.factor A' C' i (eC c)) ∧
        (∀ (p : ℕ) (z : Fin (p + 1) → C),
          eCP p (PiTensorProduct.tprod A z) =
            PiTensorProduct.tprod A' (fun a => eC (z a))) ∧
        (∀ (p : ℕ) (a : A), eCP p (algebraMap A (CP A C p) a) =
          algebraMap A' (CP A' C' p) (eA a)) ∧
        (∀ (p : ℕ) (b : B) (z : CP A C p), eBP p (b ⊗ₜ[A] z) = eB b ⊗ₜ[A'] eCP p z) ∧
        (∀ (p : ℕ) (b : B), eBP p (baseMap p b) = baseMap p (eB b)) ∧
        (∀ (p : ℕ) (z : CP A C p),
          eBP p ((Algebra.TensorProduct.includeRight : CP A C p →ₐ[A] BP A B C p) z) =
            (Algebra.TensorProduct.includeRight : CP A' C' p →ₐ[A'] BP A' B' C' p) (eCP p z)) ∧
        (∀ {p q : ℕ} (d : Fin (p + 1) → Fin (q + 1))
          (z : CP A C p) (b : BP A B C p),
          eCP q (AmitsurAlgebrasSpec.map d z) = AmitsurAlgebrasSpec.map d (eCP p z) ∧
          eBP q (columnMap (A := A) (B := B) (C := C) d b) =
            columnMap (A := A') (B := B') (C := C') d (eBP p b)) ∧
        Nonempty (OriginalRingDiagramComparison.{x,max u v x y,max v x y,max i j t}
          eB.toRingEquiv (fun p => (eBP p).toRingEquiv)
          (fun d => columnMap (A := A) (B := B) (C := C) d)
          (fun d => columnMap (A := A') (B := B') (C := C') d))

end
end Specs.DerivedFormalization.Descent.AmitsurRingTransport
