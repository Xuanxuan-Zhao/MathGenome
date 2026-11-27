import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.FlatFiltration
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedBimoduleAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.SemiFreeResolution
import Mathlib.CategoryTheory.Products.Basic

open CategoryTheory CategoryTheory.Prod
open _root_.DerivedFormalization _root_.DerivedFormalization.Affine
open Specs.DerivedFormalization.DG

universe u v t

namespace Specs.DerivedFormalization.Affine.DerivedTensor

open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor dgCat regular signedBimodule term)
open HomComplex (homotopyCategory homotopyClass)
open Derived (HomotopyCategoryLaws derivedCategory quotient)
open DerivedKProjective (derivedCategoryInstance kProjectiveObjects restrictedLocalization)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B : CommDGAlgebra.{u,v} k}

def SemifreeIsFlat : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A : CommDGAlgebra.{u,v} k}, (∀ N : A.Module, T.Formulas (𝟙 A) N) →
    ∀ {M : A.Module}, IndexedSemiFree.semiFree M → T.KFlat M

def ProjectiveIsFlat : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A : CommDGAlgebra.{u,v} k}, (∀ N : A.Module, T.Formulas (𝟙 A) N) →
    ∀ {M : A.Module}, KProjective.isKProjective M → T.KFlat M

/-- Tensor on homotopy classes, together with its map on homogeneous generators. -/
structure HomotopyTensor (T : ModuleTensor.{u,v} k) (f : A ⟶ B)
    (hA : HomotopyCategoryLaws (dgCat A)) (hB : HomotopyCategoryLaws (dgCat B)) where
  functor :
    letI := Derived.homotopyCategory (dgCat A) hA
    letI := Derived.homotopyCategory (dgCat B) hB
    homotopyCategory (dgCat A) × homotopyCategory (dgCat B) ⥤ homotopyCategory (dgCat B)
  obj (M : A.Module) (N : B.Module) :
    letI := Derived.homotopyCategory (dgCat A) hA
    letI := Derived.homotopyCategory (dgCat B) hB
    functor.obj (M, N) = T.obj f M N
  map_tmul {M M' : A.Module} {N N' : B.Module} (g : M ⟶ M') (h : N ⟶ N') :
    letI := Derived.homotopyCategory (dgCat A) hA
    letI := Derived.homotopyCategory (dgCat B) hB
    ∃ a : T.obj f M N ⟶ T.obj f M' N',
      HEq (functor.map (Prod.mkHom (homotopyClass g) (homotopyClass h))) (homotopyClass a) ∧
      ∀ (i j n : ℤ) (e : i+j=n) (x : term M i) (y : term N j),
        ((a.app ()).f n) (T.tmul f i j n e x y) =
          T.tmul f i j n e ((g.app ()).f i x) ((h.app ()).f j y)

/-- The two-variable derived tensor uses the inverse of the localization
equivalence on the full homotopy subcategory of K-projectives. -/
def derivedTensorValue (T : ModuleTensor.{u,v} k) (h : HomotopyCategoryLaws (dgCat A))
    (H : HomotopyTensor T (𝟙 A) h h)
    (E : letI := Derived.homotopyCategory (dgCat A) h
         letI := derivedCategoryInstance (dgCat A) h
         (restrictedLocalization (dgCat A) h).IsEquivalence) :
    letI := derivedCategoryInstance (dgCat A) h
    derivedCategory (dgCat A) h × derivedCategory (dgCat A) h ⥤ derivedCategory (dgCat A) h := by
  letI := Derived.homotopyCategory (dgCat A) h
  letI := derivedCategoryInstance (dgCat A) h
  letI := E
  let R := (restrictedLocalization (dgCat A) h).asEquivalence.inverse ⋙
    (kProjectiveObjects (dgCat A)).ι
  exact R.prod R ⋙ H.functor ⋙ quotient (dgCat A) h

set_option linter.checkUnivs false in
def DerivedTensorType :=
  ∀ {k : Type u} [Field k] [CharZero k] {A : CommDGAlgebra.{u,v} k}
    (T : ModuleTensor.{u,v} k) (h : HomotopyCategoryLaws (dgCat A))
    (_ : HomotopyTensor T (𝟙 A) h h)
    (_ : letI := Derived.homotopyCategory (dgCat A) h
         letI := derivedCategoryInstance (dgCat A) h
         (restrictedLocalization (dgCat A) h).IsEquivalence),
    letI := derivedCategoryInstance (dgCat A) h
    derivedCategory (dgCat A) h × derivedCategory (dgCat A) h ⥤ derivedCategory (dgCat A) h

/-- The model on any pair of K-projective or one- or two-sided K-flat inputs. -/
def TensorComputations (T : ModuleTensor.{u,v} k) (h : HomotopyCategoryLaws (dgCat A))
    (H : HomotopyTensor T (𝟙 A) h h)
    (E : letI := Derived.homotopyCategory (dgCat A) h
         letI := derivedCategoryInstance (dgCat A) h
         (restrictedLocalization (dgCat A) h).IsEquivalence) : Prop :=
  letI := Derived.homotopyCategory (dgCat A) h
  letI := derivedCategoryInstance (dgCat A) h
  let Q := quotient (dgCat A) h
  let F := derivedTensorValue T h H E
  (∀ {P R M N : A.Module} (p : P ⟶ M) (r : R ⟶ N),
    KProjective.isKProjective P → KProjective.isKProjective R →
    Module.quasiIsomorphism p → Module.quasiIsomorphism r →
    Nonempty (F.obj (Q.obj M, Q.obj N) ≅ Q.obj (T.obj (𝟙 A) P R))) ∧
  (∀ {P R M N : A.Module} (p : P ⟶ M) (r : R ⟶ N),
    T.KFlat P → T.KFlat R → Module.quasiIsomorphism p → Module.quasiIsomorphism r →
    Nonempty (F.obj (Q.obj M, Q.obj N) ≅ Q.obj (T.obj (𝟙 A) P R))) ∧
  ∀ (M N : A.Module), T.KFlat M ∨ T.KFlat N →
    Nonempty (F.obj (Q.obj M, Q.obj N) ≅ Q.obj (T.obj (𝟙 A) M N))

def NativeTensor : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∃ T : ModuleTensor.{u,v} k,
      (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module), T.Formulas f N) ∧
      ∀ (A : CommDGAlgebra.{u,v} k) (h : HomotopyCategoryLaws (dgCat A)),
        ∃ (H : HomotopyTensor T (𝟙 A) h h)
          (E : letI := Derived.homotopyCategory (dgCat A) h
               letI := derivedCategoryInstance (dgCat A) h
               (restrictedLocalization (dgCat A) h).IsEquivalence),
          TensorComputations T h H E

open DerivedBimoduleAdjunction (SignedModels DerivedAdjunctionData)
open BimoduleAdjunction (ordinaryTensor)

/-- Extension by the regular target bimodule is exact and uses the signed
scalar extension on any K-projective replacement or K-flat model. -/
def NativeExtension : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∃ T : ModuleTensor.{u,v} k,
      (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module), T.Formulas f N) ∧
      ∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B)
        (hA : HomotopyCategoryLaws (dgCat A)) (hB : HomotopyCategoryLaws (dgCat B)),
        letI := Derived.homotopyCategory (dgCat A) hA
        letI := Derived.homotopyCategory (dgCat B) hB
        letI := derivedCategoryInstance (dgCat A) hA
        letI := derivedCategoryInstance (dgCat B) hB
        let QA := quotient (dgCat A) hA
        let QB := quotient (dgCat B) hB
        ∃ (m : SignedModels.{u,v,0,0} (signedBimodule f (regular B)))
          (d : DerivedAdjunctionData.{u,v,0,0} m.tensor m.hom hA hB),
          ordinaryTensor.{u,v,0,0} m.tensor = T.baseChange f ∧
          d.Realizes m.adjunction ∧ d.ComputesRepresentatives ∧ d.IsExact ∧
          ∀ {P M : A.Module} (p : P ⟶ M), T.KFlat P → Module.quasiIsomorphism p →
            Nonempty (d.tensor.obj (QA.obj M) ≅ QB.obj ((T.baseChange f).obj P))

/-- A realization of the exact left-derived scalar extension of the signed
strict functor. -/
structure ScalarExtension (T : ModuleTensor.{u,v} k) (f : A ⟶ B)
    (hA : HomotopyCategoryLaws (dgCat A)) (hB : HomotopyCategoryLaws (dgCat B)) where
  models : SignedModels.{u,v,0,0} (signedBimodule f (regular B))
  data : DerivedAdjunctionData.{u,v,0,0} models.tensor models.hom hA hB
  strict : ordinaryTensor.{u,v,0,0} models.tensor = T.baseChange f
  realizes : data.Realizes models.adjunction
  exactness : data.IsExact

abbrev ScalarExtension.functor {T : ModuleTensor.{u,v} k} {f : A ⟶ B}
    {hA : HomotopyCategoryLaws (dgCat A)} {hB : HomotopyCategoryLaws (dgCat B)}
    (S : ScalarExtension T f hA hB) := S.data.tensor

def ScalarExtension.onProjective {T : ModuleTensor.{u,v} k} {f : A ⟶ B}
    {hA : HomotopyCategoryLaws (dgCat A)} {hB : HomotopyCategoryLaws (dgCat B)}
    (S : ScalarExtension T f hA hB) (P : A.Module) (hP : KProjective.isKProjective P) :
    letI := Derived.homotopyCategory (dgCat A) hA
    letI := Derived.homotopyCategory (dgCat B) hB
    letI := derivedCategoryInstance (dgCat A) hA
    letI := derivedCategoryInstance (dgCat B) hB
    let QA := quotient (dgCat A) hA
    let QB := quotient (dgCat B) hB
    S.functor.obj (QA.obj P) ≅ QB.obj ((T.baseChange f).obj P) := by
  letI := Derived.homotopyCategory (dgCat A) hA
  letI := Derived.homotopyCategory (dgCat B) hB
  letI := derivedCategoryInstance (dgCat A) hA
  letI := derivedCategoryInstance (dgCat B) hB
  exact S.data.onProjective P hP ≪≫ eqToIso
    (congrArg (fun G : A.Module ⥤ B.Module => (quotient (dgCat B) hB).obj (G.obj P)) S.strict)

variable {C : CommDGAlgebra.{u,v} k}

def ExtensionCompositionLaws (T : ModuleTensor.{u,v} k)
    (f : A ⟶ B) (g : B ⟶ C)
    (hA : HomotopyCategoryLaws (dgCat A)) (hB : HomotopyCategoryLaws (dgCat B))
    (hC : HomotopyCategoryLaws (dgCat C))
    (F : ScalarExtension T f hA hB) (G : ScalarExtension T g hB hC)
    (J : ScalarExtension T (f ≫ g) hA hC) : Prop :=
  letI := Derived.homotopyCategory (dgCat A) hA
  letI := Derived.homotopyCategory (dgCat B) hB
  letI := Derived.homotopyCategory (dgCat C) hC
  letI := derivedCategoryInstance (dgCat A) hA
  letI := derivedCategoryInstance (dgCat B) hB
  letI := derivedCategoryInstance (dgCat C) hC
  let QA := quotient (dgCat A) hA
  let QC := quotient (dgCat C) hC
  ∃ (a : T.baseChange f ⋙ T.baseChange g ≅ T.baseChange (f ≫ g))
    (e : F.functor ⋙ G.functor ≅ J.functor),
    (∀ (M : A.Module) (i j l m n : ℤ) (hm : i+j=m) (hn : m+l=n)
      (x : term M i) (b : B.complex.X j) (c : C.complex.X l),
      ((a.hom.app M).app ()).f n
        (T.tmul g (N := regular C) m l n hn (T.tmul f (N := regular B) i j m hm x b) c) =
      T.tmul (f ≫ g) (N := regular C) i (j+l) n (by omega) x
        (C.mul j l (j+l) rfl (g.chainMap.f j b) c)) ∧
    ∀ (P : A.Module) (hP : KProjective.isKProjective P),
      ∃ hb : KProjective.isKProjective ((T.baseChange f).obj P),
        e.hom.app (QA.obj P) ≫ (J.onProjective P hP).hom =
          G.functor.map (F.onProjective P hP).hom ≫
          (G.onProjective ((T.baseChange f).obj P) hb).hom ≫
          QC.map (homotopyClass (a.hom.app P))

def NativeExtensionComposition : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∃ T : ModuleTensor.{u,v} k,
      (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module), T.Formulas f N) ∧
      ∀ (h : ∀ A : CommDGAlgebra.{u,v} k, HomotopyCategoryLaws (dgCat A)),
        ∃ F : ∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B), ScalarExtension T f (h A) (h B),
          ∀ {A B C : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (g : B ⟶ C),
            ExtensionCompositionLaws T f g (h A) (h B) (h C) (F f) (F g) (F (f ≫ g))

/-- The original cdga with its arrow complexes transported to a common bound.
The ground field and the algebra action are retained. -/
@[reducible] def liftAlgebra (A : CommDGAlgebra.{u,v} k) : CommDGAlgebra.{u,max v t} k where
  toDGAlgebra := (AmbientDerived.category.{u,v,0,max v t} (dgCat A)).toData
  graded_comm i j n h x y := ULift.ext (A.graded_comm i j n h x.down y.down)

@[reducible] def liftAlgebraMap (f : A ⟶ B) : liftAlgebra.{u,v,t} A ⟶ liftAlgebra.{u,v,t} B where
  chainMap := (CoefficientLiftComparison.complexLift.{u,v,max v t} k).map f.chainMap
  map_one := ULift.ext f.map_one
  map_mul i j n h x y := ULift.ext (f.map_mul i j n h x.down y.down)

/-- Original objects and maps are sent to the ambient category by the fixed
coefficient lift. Its derived version is the localization square of GDerivedAmbient. -/
abbrev liftInput (A : CommDGAlgebra.{u,v} k) : A.Module ⥤ (liftAlgebra.{u,v,t} A).Module :=
  AmbientDerived.strictInput.{u,v,0,max v t} (dgCat A)

/-- Lift every algebra and algebra map of a diagram using the same bound. -/
def liftAlgebraFunctor (k : Type u) [Field k] [CharZero k] :
    CommDGAlgebra.{u,v} k ⥤ CommDGAlgebra.{u,max v t} k where
  obj := liftAlgebra.{u,v,t}
  map := liftAlgebraMap.{u,v,t}
  map_id A := CommDGAlgebra.Hom.ext_chainMap
    ((CoefficientLiftComparison.complexLift.{u,v,max v t} k).map_id A.complex)
  map_comp f g := CommDGAlgebra.Hom.ext_chainMap
    ((CoefficientLiftComparison.complexLift.{u,v,max v t} k).map_comp f.chainMap g.chainMap)

/-- The original algebra is nonpositive at the common bound. -/
def LiftNonpositive : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CommDGAlgebra.{u,v} k),
    A.IsNonpositive → (liftAlgebra.{u,v,t} A).IsNonpositive

/-- With native adequate coefficients, the fixed localization comparison
identifies the ambient localization with the original native one. -/
def AdequateNativeLocalization : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CommDGAlgebra.{u,v} k)
    (h : HomotopyCategoryLaws (dgCat A)) (h' : HomotopyCategoryLaws (dgCat (liftAlgebra.{u,v,0} A))),
    letI := Derived.homotopyCategory (dgCat A) h
    letI := Derived.homotopyCategory (dgCat (liftAlgebra.{u,v,0} A)) h'
    letI := derivedCategoryInstance (dgCat A) h
    letI := derivedCategoryInstance (dgCat (liftAlgebra.{u,v,0} A)) h'
    ∃ (H : homotopyCategory (dgCat A) ≌ homotopyCategory (dgCat (liftAlgebra.{u,v,0} A)))
      (E : derivedCategory (dgCat A) h ≌ derivedCategory (dgCat (liftAlgebra.{u,v,0} A)) h'),
      Nonempty (quotient (dgCat A) h ⋙ E.functor ≅ H.functor ⋙
        quotient (dgCat (liftAlgebra.{u,v,0} A)) h')

def CoefficientTensor : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∃ (T : ModuleTensor.{u,v} k) (U : ModuleTensor.{u,max v t} k),
      (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module), T.Formulas f N) ∧
      (∀ {A B : CommDGAlgebra.{u,max v t} k} (f : A ⟶ B) (N : B.Module), U.Formulas f N) ∧
      ∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module),
        let I := liftInput.{u,v,t} A
        let J := liftInput.{u,v,t} B
        let f' := liftAlgebraMap.{u,v,t} f
        ∃ e : T.extension f N ⋙ J ≅ I ⋙ U.extension f' (J.obj N),
          ∀ (M : A.Module) (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j),
            (((e.hom.app M).app ()).f n) (ULift.up (T.tmul f i j n h x y)) =
              U.tmul f' i j n h (ULift.up x) (ULift.up y)

/-- A tensor on the derived category obtained from the named native
K-projective equivalence. -/
structure TensorResolution (T : ModuleTensor.{u,v} k) (A : CommDGAlgebra.{u,v} k)
    (h : HomotopyCategoryLaws (dgCat A)) where
  homotopy : HomotopyTensor T (𝟙 A) h h
  equivalence :
    letI := Derived.homotopyCategory (dgCat A) h
    letI := derivedCategoryInstance (dgCat A) h
    (restrictedLocalization (dgCat A) h).IsEquivalence

abbrev TensorResolution.functor {T : ModuleTensor.{u,v} k} {A : CommDGAlgebra.{u,v} k}
    {h : HomotopyCategoryLaws (dgCat A)} (R : TensorResolution T A h) :=
  derivedTensorValue T h R.homotopy R.equivalence

open DerivedCoefficientLift (Descent)

def TensorTransport {T : ModuleTensor.{u,v} k} {U : ModuleTensor.{u,max v t} k}
    (h : HomotopyCategoryLaws (dgCat A))
    (h' : HomotopyCategoryLaws (dgCat (liftAlgebra.{u,v,t} A)))
    (F : TensorResolution T A h) (G : TensorResolution U (liftAlgebra.{u,v,t} A) h')
    (d : Descent h h' (liftInput.{u,v,t} A)) : Prop :=
  letI := derivedCategoryInstance (dgCat A) h
  letI := derivedCategoryInstance (dgCat (liftAlgebra.{u,v,t} A)) h'
  Nonempty (F.functor ⋙ d.D ≅ d.D.prod d.D ⋙ G.functor)

def ExtensionTransport {T : ModuleTensor.{u,v} k} {U : ModuleTensor.{u,max v t} k}
    {f : A ⟶ B} (hA : HomotopyCategoryLaws (dgCat A)) (hB : HomotopyCategoryLaws (dgCat B))
    (hA' : HomotopyCategoryLaws (dgCat (liftAlgebra.{u,v,t} A)))
    (hB' : HomotopyCategoryLaws (dgCat (liftAlgebra.{u,v,t} B)))
    (F : ScalarExtension T f hA hB) (G : ScalarExtension U (liftAlgebraMap.{u,v,t} f) hA' hB')
    (dA : Descent hA hA' (liftInput.{u,v,t} A)) (dB : Descent hB hB' (liftInput.{u,v,t} B)) : Prop :=
  letI := derivedCategoryInstance (dgCat A) hA
  letI := derivedCategoryInstance (dgCat B) hB
  letI := derivedCategoryInstance (dgCat (liftAlgebra.{u,v,t} A)) hA'
  letI := derivedCategoryInstance (dgCat (liftAlgebra.{u,v,t} B)) hB'
  Nonempty (F.functor ⋙ dB.D ≅ dA.D ⋙ G.functor)

def CoefficientDerived : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∃ (T : ModuleTensor.{u,v} k) (U : ModuleTensor.{u,max v t} k),
      (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module), T.Formulas f N) ∧
      (∀ {A B : CommDGAlgebra.{u,max v t} k} (f : A ⟶ B) (N : B.Module), U.Formulas f N) ∧
      ∀ (h : ∀ A : CommDGAlgebra.{u,v} k, HomotopyCategoryLaws (dgCat A))
        (h' : ∀ A : CommDGAlgebra.{u,max v t} k, HomotopyCategoryLaws (dgCat A)),
        ∃ (F : ∀ A : CommDGAlgebra.{u,v} k, TensorResolution T A (h A))
          (G : ∀ A : CommDGAlgebra.{u,max v t} k, TensorResolution U A (h' A))
          (S : ∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B), ScalarExtension T f (h A) (h B))
          (S' : ∀ {A B : CommDGAlgebra.{u,max v t} k} (f : A ⟶ B), ScalarExtension U f (h' A) (h' B))
          (d : ∀ A : CommDGAlgebra.{u,v} k, Descent (h A) (h' (liftAlgebra.{u,v,t} A))
            (liftInput.{u,v,t} A)),
          (∀ A, TensorTransport (h A) (h' (liftAlgebra.{u,v,t} A))
            (F A) (G (liftAlgebra.{u,v,t} A)) (d A)) ∧
          ∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B),
            ExtensionTransport (h A) (h B) (h' (liftAlgebra.{u,v,t} A)) (h' (liftAlgebra.{u,v,t} B))
              (S f) (S' (liftAlgebraMap.{u,v,t} f)) (d A) (d B)

set_option linter.checkUnivs false in
abbrev LiftAlgebraType :=
  ∀ {k : Type u} [Field k] [CharZero k], CommDGAlgebra.{u,v} k → CommDGAlgebra.{u,max v t} k

set_option linter.checkUnivs false in
abbrev LiftAlgebraMapType :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : CommDGAlgebra.{u,v} k},
    (A ⟶ B) → (liftAlgebra.{u,v,t} A ⟶ liftAlgebra.{u,v,t} B)

end
end Specs.DerivedFormalization.Affine.DerivedTensor
