import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.NonpositiveAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.BalancedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ShiftCone
import Mathlib.Tactic.Ring

open CategoryTheory
open CochainComplex.HomComplex (Cochain)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component dgModuleCategory ofStrict)
open Specs.DerivedFormalization.DG.BalancedTensor (bimodule Degree tmul)

universe u v

namespace Specs.DerivedFormalization.Affine.Tensor

open _root_.DerivedFormalization
open _root_.DerivedFormalization.Affine

variable {k : Type u} [Field k] [CharZero k]
variable {A B C : CommDGAlgebra.{u,v} k}

abbrev dgCat (A : CommDGAlgebra.{u,v} k) :=
  Specs.DerivedFormalization.DG.Basic.toDGCategory A.toDGAlgebra

abbrev term {A : CommDGAlgebra.{u,v} k} (M : A.Module) (i : ℤ) :=
  (M.complex ()).X i

abbrev act {A : CommDGAlgebra.{u,v} k} (M : A.Module) (i j n : ℤ) (h : i+j=n) :=
  M.act (a := ()) (b := ()) i j n h

/-- Restriction of scalars on a dg module. -/
@[reducible] def restrict (f : A ⟶ B) (M : B.Module) : A.Module where
  complex := M.complex
  act {a b} i j n h := (LinearMap.lcomp k _ (f.chainMap.f j).hom).comp (M.act (a := a) (b := b) i j n h)
  act_id a i x := by
    cases a
    change act M i 0 i _ x (f.chainMap.f 0 A.one) = x
    rw [f.map_one]
    exact M.act_id () i x
  act_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ i j l x y z
    change act M (i+j) l _ _ (act M i j _ _ x (f.chainMap.f j y)) (f.chainMap.f l z) =
      act M i (j+l) _ _ x (f.chainMap.f (j+l) (A.mul j l _ rfl y z))
    rw [f.map_mul, M.act_assoc]
  leibniz := by
    rintro ⟨⟩ ⟨⟩ i j n h x y
    change (M.complex ()).d n (n+1) (act M i j n h x (f.chainMap.f j y)) = _
    rw [M.leibniz]
    have e := CategoryTheory.congr_fun (f.chainMap.comm j (j+1)) y
    simp only [ModuleCat.comp_apply] at e
    change _ = act M (i+1) j (n+1) _ ((M.complex ()).d i (i+1) x) (f.chainMap.f j y) +
      i.negOnePow • act M i (j+1) (n+1) _ x (f.chainMap.f (j+1) (A.complex.d j (j+1) y))
    rw [e]

/-- The restriction functor has the original chain maps as its components. -/
@[reducible] def restrictFunctor (f : A ⟶ B) : B.Module ⥤ A.Module where
  obj := restrict f
  map h := ⟨h.app, fun i j n e x a => h.comm_act i j n e x (f.chainMap.f j a)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

set_option linter.checkUnivs false in
def RestrictFunctorType :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : CommDGAlgebra.{u,v} k},
    (A ⟶ B) → (B.Module ⥤ A.Module)

/-- The right regular dg module. -/
@[reducible] def regular (A : CommDGAlgebra.{u,v} k) : A.Module where
  complex _ := A.complex
  act := A.mul
  act_id _ := A.toDGAlgebra.comp_id (a := ()) (b := ())
  act_assoc := fun {_ _ _} => A.toDGAlgebra.assoc (a := ()) (b := ()) (c := ()) (e := ())
  leibniz := fun {_ _} => A.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ())

theorem act_assoc_at (M : B.Module) (i j l ij jl n : ℤ)
    (hij : i+j=ij) (hjl : j+l=jl) (hn : ij+l=n)
    (x : term M i) (y : B.complex.X j) (z : B.complex.X l) :
    act M ij l n hn (act M i j ij hij x y) z =
      act M i jl n (by omega) x (B.mul j l jl hjl y z) := by
  subst ij jl n
  exact M.act_assoc (a := ()) (b := ()) (c := ()) i j l x y z

/-- A right action gives a left action by the Koszul sign. -/
def signedLeft (M : B.Module) (i j n : ℤ) (h : i+j=n) :
    B.complex.X i →ₗ[k] term M j →ₗ[k] term M n :=
  (i*j).negOnePow • (act M j i n (by omega)).flip

@[simp] theorem signedLeft_apply (M : B.Module) (i j n : ℤ) (h : i+j=n)
    (a : B.complex.X i) (x : term M j) :
    signedLeft M i j n h a x = (i*j).negOnePow • act M j i n (by omega) x a := rfl

-- Convert all module signs to integer scalars for bilinear rewriting.
private theorem signs {i j : ℤ} (h : i = j) : i.negOnePow = j.negOnePow := congrArg _ h

theorem signedLeft_right (M : B.Module) (i j l ij jl n : ℤ)
    (hij : i+j=ij) (hjl : j+l=jl) (hn : ij+l=n)
    (a : B.complex.X i) (x : term M j) (b : B.complex.X l) :
    signedLeft M i jl n (by omega) a (act M j l jl hjl x b) =
      act M ij l n hn (signedLeft M i j ij hij a x) b := by
  subst ij jl n
  simp only [signedLeft_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply]
  rw [act_assoc_at M j l i (j+l) (i+l) _ rfl (by omega) (by omega),
    act_assoc_at M j i l (i+j) (i+l) _ (by omega) rfl rfl,
    B.graded_comm l i (i+l) (by omega) b a]
  simp only [Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  rw [signs (show i*(j+l)+l*i = i*j + 2*(i*l) by ring),
    Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

theorem signedLeft_assoc (M : B.Module) (i j l n : ℤ) (h : i+j+l=n)
    (a : B.complex.X i) (b : B.complex.X j) (x : term M l) :
    signedLeft M (i+j) l n h (B.mul i j (i+j) rfl a b) x =
      signedLeft M i (j+l) n (by omega) a (signedLeft M j l (j+l) rfl b x) := by
  rw [signedLeft_apply, signedLeft_apply, signedLeft_apply,
    B.graded_comm i j (i+j) rfl a b]
  simp only [Units.smul_def, map_zsmul, LinearMap.smul_apply,
    smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  rw [act_assoc_at M l j i (j+l) (i+j) n (by omega) (by omega) (by omega),
    signs (show (i+j)*l+i*j = i*(j+l)+j*l by ring)]

theorem signedLeft_d (M : B.Module) (i j n : ℤ) (h : i+j=n)
    (a : B.complex.X i) (x : term M j) :
    (M.complex ()).d n (n+1) (signedLeft M i j n h a x) =
      signedLeft M (i+1) j (n+1) (by omega) (B.complex.d i (i+1) a) x +
      i.negOnePow • signedLeft M i (j+1) (n+1) (by omega) a ((M.complex ()).d j (j+1) x) := by
  simp only [signedLeft_apply, Units.smul_def, map_zsmul]
  rw [M.leibniz j i n (by omega)]
  simp only [Units.smul_def, smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  rw [signs (show i*j+j=(i+1)*j by ring),
    signs (show i+i*(j+1) = i*j+2*i by ring), Int.negOnePow_add,
    Int.negOnePow_two_mul, mul_one]
  ac_rfl

private def leftHom (M : B.Module) (i : ℤ) : B.complex.X i →ₗ[k] gradedHom M M i where
  toFun a := ⟨fun _ => Cochain.mk fun j n h =>
    ModuleCat.ofHom (signedLeft M i j n (by omega) a), by
      rintro ⟨⟩ ⟨⟩ j l n ji ni h hj hn x z
      exact signedLeft_right M i j l ji n ni (by omega) h (by omega) a x z⟩
  map_add' a b := by
    apply Subtype.ext
    funext c
    apply Cochain.ext
    intro j n h
    apply ModuleCat.hom_ext
    change signedLeft M i j n (by omega) (a+b) = signedLeft M i j n (by omega) a + signedLeft M i j n (by omega) b
    exact map_add _ _ _
  map_smul' t a := by
    apply Subtype.ext
    funext c
    apply Cochain.ext
    intro j n h
    apply ModuleCat.hom_ext
    change signedLeft M i j n (by omega) (t • a) = t • signedLeft M i j n (by omega) a
    exact map_smul _ _ _

private theorem leftHom_d (M : B.Module) (i : ℤ) (a : B.complex.X i) :
    (Specs.DerivedFormalization.DG.HomComplex.homComplex M M).d i (i+1) (leftHom M i a) =
      leftHom M (i+1) (B.complex.d i (i+1) a) := by
  apply Subtype.ext
  funext c
  cases c
  apply Cochain.ext
  intro j n h
  obtain rfl : i+j+1=n := by omega
  change (CochainComplex.HomComplex.δ i (i+1) ((leftHom M i a).val ())).v j (i+j+1) (by omega) = _
  rw [CochainComplex.HomComplex.δ_v i (i+1) rfl _ j (i+j+1) (by omega) (i+j) (j+1) (by omega) rfl]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (M.complex ()).d (i+j) (i+j+1) (signedLeft M i j (i+j) rfl a x) +
    (i+1).negOnePow • signedLeft M i (j+1) (i+j+1) (by omega) a ((M.complex ()).d j (j+1) x) =
    signedLeft M (i+1) j (i+j+1) (by omega) (B.complex.d i (i+1) a) x
  rw [signedLeft_d, Int.negOnePow_succ, Units.neg_smul]
  exact add_neg_cancel_right _ _

/-- A dg module over a commutative dg B-algebra is an A–B bimodule. -/
@[reducible] def signedBimodule (f : A ⟶ B) (M : B.Module) : bimodule (dgCat A) (dgCat B) where
  obj _ := M
  map _ _ := {
    f := fun i => (leftHom M i).comp (f.chainMap.f i).hom
    comm := by
      intro i a
      change leftHom M (i+1) (f.chainMap.f (i+1) (A.complex.d i (i+1) a)) =
        (Specs.DerivedFormalization.DG.HomComplex.homComplex M M).d i (i+1)
          (leftHom M i (f.chainMap.f i a))
      rw [leftHom_d]
      congr 1
      exact (CategoryTheory.congr_fun (f.chainMap.comm i (i+1)) a).symm }
  map_id := by
    rintro ⟨⟩
    change leftHom M 0 (f.chainMap.f 0 A.one) = ofStrict (𝟙 M)
    rw [f.map_one]
    apply Subtype.ext
    funext c
    cases c
    apply Cochain.ext
    intro i j h
    obtain rfl : i=j := by omega
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change signedLeft M 0 i i (zero_add i) B.one x = x
    rw [signedLeft_apply, zero_mul, Int.negOnePow_zero, one_smul]
    exact M.act_id () i x
  map_comp := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ i j n h a b
    subst n
    change leftHom M (i+j) (f.chainMap.f (i+j) (A.mul i j (i+j) rfl a b)) =
      (dgModuleCategory (dgCat B)).comp i j (i+j) rfl
        (leftHom M i (f.chainMap.f i a)) (leftHom M j (f.chainMap.f j b))
    rw [f.map_mul]
    apply Subtype.ext
    funext c
    cases c
    apply Cochain.ext
    intro l q e
    change ModuleCat.ofHom (signedLeft M (i+j) l q (by omega) _) =
      (((leftHom M j (f.chainMap.f j b)).val ()).comp
        ((leftHom M i (f.chainMap.f i a)).val ()) (by omega)).v l q e
    rw [Cochain.comp_v _ _ _ l (j+l) q (by omega) (by omega)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact signedLeft_assoc M i j l q (by omega) _ _ x

abbrev tensorDegree (f : A ⟶ B) (M : A.Module) (N : B.Module) (n : ℤ) :=
  Degree (signedBimodule f N) M () n

set_option linter.checkUnivs false in
def TensorDegreeType :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : CommDGAlgebra.{u,v} k},
    (A ⟶ B) → A.Module → B.Module → ℤ → Type v

noncomputable abbrev pure (f : A ⟶ B) {M : A.Module} {N : B.Module} (i j n : ℤ)
    (h : i+j=n) (x : term M i) (y : term N j) : tensorDegree f M N n :=
  tmul (signedBimodule f N) M () () i j n h x y

section ModuleTensor

open Specs.DerivedFormalization.DG.HomComplex (HomotopyEquation)
open Specs.DerivedFormalization.DG.ShiftCone (cone)
open Specs.DerivedFormalization.DG.Module (acyclic quasiIsomorphism)

/-- A functorial balanced tensor with its identification in each homogeneous degree. -/
structure ModuleTensor (k : Type u) [Field k] [CharZero k] where
  extension {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module) : A.Module ⥤ B.Module
  degree {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (M : A.Module) (N : B.Module) (n : ℤ) :
    tensorDegree f M N n ≃ₗ[k] term ((extension f N).obj M) n

variable {A B : CommDGAlgebra.{u,v} k}

abbrev ModuleTensor.obj (T : ModuleTensor.{u,v} k) (f : A ⟶ B) (M : A.Module) (N : B.Module) :=
  (T.extension f N).obj M

noncomputable abbrev ModuleTensor.tmul (T : ModuleTensor.{u,v} k) (f : A ⟶ B) {M : A.Module} {N : B.Module}
    (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :=
  T.degree f M N n (pure f i j n h x y)

/-- Acyclicity is tested on every degree of every acyclic dg module. -/
def ModuleTensor.KFlat (T : ModuleTensor.{u,v} k) (N : A.Module) : Prop :=
  ∀ E : A.Module, acyclic E → acyclic (T.obj (𝟙 A) E N)

structure ModuleTensor.Formulas (T : ModuleTensor.{u,v} k)
    (f : A ⟶ B) (N : B.Module) : Prop where
  differential (M : A.Module) (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j) :
    ((T.obj f M N).complex ()).d n (n+1) (T.tmul f i j n h x y) =
      T.tmul f (i+1) j (n+1) (by omega) ((M.complex ()).d i (i+1) x) y +
        i.negOnePow • T.tmul f i (j+1) (n+1) (by omega) x ((N.complex ()).d j (j+1) y)
  action (M : A.Module) (i j n l q : ℤ) (h : i+j=n) (e : n+l=q)
      (x : term M i) (y : term N j) (a : B.complex.X l) :
    act (T.obj f M N) n l q e (T.tmul f i j n h x y) a =
      T.tmul f i (j+l) q (by omega) x (act N j l (j+l) rfl y a)
  first {M M' : A.Module} (g : M ⟶ M') (i j n : ℤ) (h : i+j=n)
      (x : term M i) (y : term N j) :
    (((T.extension f N).map g).app ()).f n (T.tmul f i j n h x y) =
      T.tmul f i j n h ((g.app ()).f i x) y
  firstHomotopy {M M' : A.Module} (g g' : M ⟶ M') (w : gradedHom M M' (-1))
      (h : HomotopyEquation g g' w) :
    ∃ W : gradedHom (T.obj f M N) (T.obj f M' N) (-1),
      HomotopyEquation ((T.extension f N).map g) ((T.extension f N).map g') W ∧
      ∀ (i j n p q : ℤ) (e : i+j=n) (ep : i+(-1)=p) (eq : n+(-1)=q) (x : term M i) (y : term N j),
        component W () n q eq (T.tmul f i j n e x y) =
          T.tmul f p j q (by omega) (component w () i p ep x) y
  coneComparison {M M' : A.Module} (g : M ⟶ M') :
    Nonempty (T.obj f (cone g) N ≅ cone ((T.extension f N).map g))

def ModuleTensor.SecondVariable (T : ModuleTensor.{u,v} k) (f : A ⟶ B) (M : A.Module) : Prop :=
  ∃ (G : B.Module ⥤ B.Module) (e : ∀ N, G.obj N ≅ T.obj f M N),
    (∀ {N N' : B.Module} (g : N ⟶ N') (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j),
      ((e N').hom.app ()).f n (((G.map g).app ()).f n (((e N).inv.app ()).f n (T.tmul f i j n h x y))) =
        T.tmul f i j n h x ((g.app ()).f j y)) ∧
    ∀ {N N' : B.Module} (g g' : N ⟶ N') (w : gradedHom N N' (-1)),
      HomotopyEquation g g' w →
      ∃ W : gradedHom (T.obj f M N) (T.obj f M N') (-1),
        HomotopyEquation ((e N).inv ≫ G.map g ≫ (e N').hom)
          ((e N).inv ≫ G.map g' ≫ (e N').hom) W ∧
        ∀ (i j n p q : ℤ) (h : i+j=n) (ep : j+(-1)=p) (eq : n+(-1)=q)
          (x : term M i) (y : term N j),
          component W () n q eq (T.tmul f i j n h x y) =
            i.negOnePow • T.tmul f i p q (by omega) x (component w () j p ep y)

def ModuleTensor.PreservesQuasiIsomorphisms (T : ModuleTensor.{u,v} k)
    (N : A.Module) : Prop :=
  T.KFlat N → ∀ {M M' : A.Module} (g : M ⟶ M'),
    quasiIsomorphism g → quasiIsomorphism ((T.extension (𝟙 A) N).map g)

def ModuleTensorConstruction : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k], ∃ T : ModuleTensor.{u,v} k,
    (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module), T.Formulas f N) ∧
    (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (M : A.Module), T.SecondVariable f M) ∧
    (∀ {A : CommDGAlgebra.{u,v} k} (N : A.Module), T.PreservesQuasiIsomorphisms N)

end ModuleTensor


section Comparisons

open Specs.DerivedFormalization.DG.Module (quasiIsomorphism)

variable (T : ModuleTensor.{u,v} k)

/-- Scalar extension is tensoring with the regular module of the target algebra. -/
abbrev ModuleTensor.baseChange (f : A ⟶ B) : A.Module ⥤ B.Module :=
  T.extension f (regular B)

structure ModuleTensor.Comparisons : Prop where
  associate {A B C : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (g : B ⟶ C)
      (M : A.Module) (N : B.Module) (P : C.Module) :
    ∃ e : T.obj g (T.obj f M N) P ≅ T.obj (f ≫ g) M (T.obj g N P),
      ∀ (i j l m n : ℤ) (hm : i+j=m) (hn : m+l=n)
        (x : term M i) (y : term N j) (z : term P l),
        (e.hom.app ()).f n (T.tmul g m l n hn (T.tmul f i j m hm x y) z) =
          T.tmul (f ≫ g) i (j+l) n (by omega) x (T.tmul g j l (j+l) rfl y z)
  symmetry {A : CommDGAlgebra.{u,v} k} (M N : A.Module) :
    ∃ e : T.obj (𝟙 A) M N ≅ T.obj (𝟙 A) N M,
      ∀ (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j),
        (e.hom.app ()).f n (T.tmul (𝟙 A) i j n h x y) =
          (i*j).negOnePow • T.tmul (𝟙 A) j i n (by omega) y x
  leftUnit {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module) :
    ∃ e : T.obj f (regular A) N ≅ N,
      ∀ (i j n : ℤ) (h : i+j=n) (a : A.complex.X i) (y : term N j),
        (e.hom.app ()).f n (T.tmul f i j n h a y) = signedLeft N i j n h (f.chainMap.f i a) y
  compose {A B C : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (g : B ⟶ C) (M : A.Module) :
    ∃ e : (T.baseChange g).obj ((T.baseChange f).obj M) ≅ (T.baseChange (f ≫ g)).obj M,
      ∀ (i j l m n : ℤ) (hm : i+j=m) (hn : m+l=n)
        (x : term M i) (b : B.complex.X j) (c : C.complex.X l),
        (e.hom.app ()).f n (T.tmul g m l n hn (T.tmul f i j m hm x b) c) =
          T.tmul (f ≫ g) i (j+l) n (by omega) x (C.mul j l (j+l) rfl (g.chainMap.f j b) c)
  identity {A : CommDGAlgebra.{u,v} k} (M : A.Module) :
    ∃ e : (T.baseChange (𝟙 A)).obj M ≅ M,
      ∀ (i j n : ℤ) (h : i+j=n) (x : term M i) (a : A.complex.X j),
        (e.hom.app ()).f n (T.tmul (𝟙 A) i j n h x a) = act M i j n h x a
  regularFlat {A : CommDGAlgebra.{u,v} k} : T.KFlat (regular A)
  secondQuasiIso {A : CommDGAlgebra.{u,v} k} {M N N' : A.Module} (a : N ⟶ N') :
    T.KFlat M → quasiIsomorphism a →
    ∃ b : T.obj (𝟙 A) M N ⟶ T.obj (𝟙 A) M N',
      quasiIsomorphism b ∧
      ∀ (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term N j),
        (b.app ()).f n (T.tmul (𝟙 A) i j n h x y) = T.tmul (𝟙 A) i j n h x ((a.app ()).f j y)
  restrict {A B C : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (g : B ⟶ C)
      (M : A.Module) (P : C.Module) :
    ∃ e : restrict g (T.obj (f ≫ g) M P) ≅ T.obj f M (restrict g P),
      ∀ (i j n : ℤ) (h : i+j=n) (x : term M i) (y : term P j),
        (e.hom.app ()).f n (T.tmul (f ≫ g) (N := P) i j n h x y) =
          T.tmul f (N := restrict g P) i j n h x y

end Comparisons

section AlgebraCoproduct

variable (T : ModuleTensor.{u,v} k)
variable (f : A ⟶ B) (g : A ⟶ C)

/-- A tensor of cdgas over A, with its identification as the tensor of the
underlying modules and its right action from the second factor. -/
structure ModuleTensor.AlgebraCoproduct where
  obj : CommDGAlgebra.{u,v} k
  inl : B ⟶ obj
  inr : C ⟶ obj
  comparison : T.obj g (restrict f (regular B)) (regular C) ≅ restrict inr (regular obj)

variable {T f g} (Q : T.AlgebraCoproduct f g)

noncomputable abbrev ModuleTensor.AlgebraCoproduct.tmul (i j n : ℤ) (h : i+j=n)
    (x : B.complex.X i) (y : C.complex.X j) : Q.obj.complex.X n :=
  (Q.comparison.hom.app ()).f n (T.tmul g (M := restrict f (regular B)) (N := regular C) i j n h x y)

/-- Multiplication and the two inclusions are the signed tensor formulas.
The cocone is universal among compatible algebra maps. -/
structure ModuleTensor.AlgebraCoproduct.Formulas : Prop where
  unit : Q.obj.one = Q.tmul 0 0 0 rfl B.one C.one
  mul (i j p q m m' n : ℤ) (h : i+j=m) (h' : p+q=m') (hn : m+m'=n)
      (x : B.complex.X i) (y : C.complex.X j) (z : B.complex.X p) (w : C.complex.X q) :
    Q.obj.mul m m' n hn (Q.tmul i j m h x y) (Q.tmul p q m' h' z w) =
      (j*p).negOnePow • Q.tmul (i+p) (j+q) n (by omega)
        (B.mul i p (i+p) rfl x z) (C.mul j q (j+q) rfl y w)
  inl (i : ℤ) (x : B.complex.X i) :
    Q.inl.chainMap.f i x = Q.tmul i 0 i (add_zero i) x C.one
  inr (j : ℤ) (y : C.complex.X j) :
    Q.inr.chainMap.f j y = Q.tmul 0 j j (zero_add j) B.one y
  base : f ≫ Q.inl = g ≫ Q.inr
  coproduct {D : CommDGAlgebra.{u,v} k} (r : B ⟶ D) (s : C ⟶ D) :
    f ≫ r = g ≫ s → ∃! t : Q.obj ⟶ D, Q.inl ≫ t = r ∧ Q.inr ≫ t = s
  nonpositive : B.IsNonpositive → C.IsNonpositive → Q.obj.IsNonpositive
  underlying :
    ∃ e : T.obj (𝟙 A) (restrict f (regular B)) (restrict g (regular C)) ≅
        restrict (g ≫ Q.inr) (regular Q.obj),
      ∀ (i j n : ℤ) (h : i+j=n) (x : B.complex.X i) (y : C.complex.X j),
        (e.hom.app ()).f n (T.tmul (𝟙 A) (M := restrict f (regular B))
          (N := restrict g (regular C)) i j n h x y) = Q.tmul i j n h x y
  scalarExtension :
    ∃ e : T.baseChange Q.inl ⋙ restrictFunctor Q.inr ≅ restrictFunctor f ⋙ T.baseChange g,
      ∀ (M : B.Module) (i p q m n : ℤ) (hm : p+q=m) (hn : i+m=n)
        (x : term M i) (b : B.complex.X p) (c : C.complex.X q),
        ((e.hom.app M).app ()).f n (T.tmul Q.inl (N := regular Q.obj) i m n hn x (Q.tmul p q m hm b c)) =
          T.tmul g (M := restrict f M) (N := regular C) (i+p) q n (by omega) (act M i p (i+p) rfl x b) c

def ModuleTensor.AlgebraCoproducts (T : ModuleTensor.{u,v} k) : Prop :=
  ∃ S : ∀ {A B C : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (g : A ⟶ C),
      T.AlgebraCoproduct f g,
    (∀ {A B C : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (g : A ⟶ C), (S f g).Formulas) ∧
    ∀ {A B C A' B' C' : CommDGAlgebra.{u,v} k} {f : A ⟶ B} {g : A ⟶ C}
      {f' : A' ⟶ B'} {g' : A' ⟶ C'} (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C'),
      f ≫ b = a ≫ f' → g ≫ c = a ≫ g' →
      ∃ t : (S f g).obj ⟶ (S f' g').obj,
        (S f g).inl ≫ t = b ≫ (S f' g').inl ∧ (S f g).inr ≫ t = c ≫ (S f' g').inr ∧
        ∀ (i j n : ℤ) (h : i+j=n) (x : B.complex.X i) (y : C.complex.X j),
          t.chainMap.f n ((S f g).tmul i j n h x y) =
            (S f' g').tmul i j n h (b.chainMap.f i x) (c.chainMap.f j y)

end AlgebraCoproduct

/-- The module and algebra constructions use one and the same balanced tensor model. -/
def SignedTensorConstruction : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k], ∃ T : ModuleTensor.{u,v} k,
    (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (N : B.Module), T.Formulas f N) ∧
    (∀ {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) (M : A.Module), T.SecondVariable f M) ∧
    (∀ {A : CommDGAlgebra.{u,v} k} (N : A.Module), T.PreservesQuasiIsomorphisms N) ∧
    T.Comparisons ∧ T.AlgebraCoproducts

end Specs.DerivedFormalization.Affine.Tensor
