import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.NonpositiveAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedKProjective
import Mathlib.CategoryTheory.Localization.Prod

open CategoryTheory CochainComplex.HomComplex
open _root_.DerivedFormalization

universe u v t

set_option linter.checkUnivs false

namespace Specs.DerivedFormalization.Affine.DerivedHom

open _root_.DerivedFormalization.Affine (CommDGAlgebra)
open _root_.Specs.DerivedFormalization.DG
open HomComplex (gradedHom homComplex component compose ofStrict)

variable {k : Type u} [Field k] [CharZero k]

/-- All the module categories here use the shared one-object construction. -/
abbrev algebraCategory (A : CommDGAlgebra.{u,v} k) := Basic.toDGCategory A.toDGAlgebra
abbrev Mod (A : CommDGAlgebra.{u,v} k) := RightDGModuleModel (algebraCategory A)

/-- Coefficient enlargement keeps the same base field and the original algebra
operations, conjugated by the coefficient equivalences. -/
def liftAlgebra (A : CommDGAlgebra.{u,v} k) : CommDGAlgebra.{u,max v t} k where
  toDGAlgebra := (AmbientDerived.category.{u,v,0,t} (algebraCategory A)).toData
  graded_comm i j n e x y := ULift.ext (A.graded_comm i j n e x.down y.down)

variable {A : CommDGAlgebra.{u,v} k} {M N P : Mod A}

private theorem ext_component {r : ℤ} {f g : gradedHom M N r}
    (e : ∀ i q (h : i+r = q) (x : (M.complex ()).X i),
      component f () i q h x = component g () i q h x) : f = g := by
  apply Subtype.ext
  funext a
  cases a
  apply Cochain.ext
  intro i q h
  exact ModuleCat.hom_ext (LinearMap.ext (e i q h))

private theorem act_assoc_at (M : Mod A) (i j l ij jl n : ℤ)
    (eij : i+j = ij) (ejl : j+l = jl) (en : i+j+l = n)
    (x : (M.complex ()).X i) (y : A.complex.X j) (z : A.complex.X l) :
    M.act ij l n (by omega) (M.act i j ij eij x y) z =
      M.act i jl n (by omega) x (A.mul j l jl ejl y z) := by
  subst ij jl n
  exact M.act_assoc i j l x y z

/-- Left action on a right module, by graded commutativity. Viewed as a
homogeneous map it is right-linear. -/
def scalarOperator (M : Mod A) (j : ℤ) (z : A.complex.X j) : gradedHom M M j :=
  ⟨fun _ => Cochain.mk fun i q h =>
    ModuleCat.ofHom ((i*j).negOnePow • (M.act i j q h).flip z), by
    intro a b i l n ir nr h hi hn x y
    cases a
    cases b
    have e₂ : i+j = ir := hi
    have e₃ : i+l+j = nr := h ▸ hn
    subst n ir nr
    change ((i+l)*j).negOnePow • M.act (i+l) j (i+l+j) rfl
      (M.act i l (i+l) rfl x y) z =
      M.act (i+j) l (i+l+j) (by omega) ((i*j).negOnePow • M.act i j (i+j) rfl x z) y
    rw [show M.act (i+j) l (i+l+j) (by omega)
        ((i*j).negOnePow • M.act i j (i+j) rfl x z) y =
        (i*j).negOnePow • M.act (i+j) l (i+l+j) (by omega)
          (M.act i j (i+j) rfl x z) y from
      map_zsmul_unit ((M.act (i+j) l (i+l+j) (by omega)).flip y) _ _,
      act_assoc_at M i l j (i+l) (l+j) (i+l+j) rfl rfl rfl,
      act_assoc_at M i j l (i+j) (l+j) (i+l+j) rfl (by omega) (by omega)]
    rw [A.graded_comm l j (l+j) rfl y z, map_zsmul_unit, smul_smul]
    have hs : ((i+l)*j).negOnePow * (l*j).negOnePow = (i*j).negOnePow := by
      rw [add_mul, Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]
    rw [hs]⟩

@[simp] theorem scalarOperator_apply (j : ℤ) (z : A.complex.X j)
    (i q : ℤ) (h : i+j = q) (x : (M.complex ()).X i) :
    component (scalarOperator M j z) () i q h x =
      (i*j).negOnePow • M.act i j q h x z := rfl

private def scalarLinear (M : Mod A) (j : ℤ) :
    A.complex.X j →ₗ[k] gradedHom M M j where
  toFun := scalarOperator M j
  map_add' z y := by
    apply ext_component
    intro i q h x
    change _ = ((scalarOperator M j z).val () + (scalarOperator M j y).val ()).v i q h x
    simp only [scalarOperator_apply, Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply,
      map_add, smul_add]
  map_smul' c z := by
    apply ext_component
    intro i q h x
    change _ = (c • (scalarOperator M j z).val ()).v i q h x
    simp only [scalarOperator_apply, Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply,
      map_smul, smul_comm ((i*j).negOnePow) c]

/-- The left scalar action as a dg representation on the module. -/
def scalarRepresentation (M : Mod A) :
    DGFunctorModel (algebraCategory A) (HomComplex.dgModuleCategory (algebraCategory A)) where
  obj _ := M
  map a b := by
    cases a
    cases b
    exact CochainComplex.ofHom (fun j => ModuleCat.ofHom (scalarLinear M j)) (by
      intro j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change (homComplex M M).d j (j+1) (scalarOperator M j z) =
        scalarOperator M (j+1) (A.complex.d j (j+1) z)
      apply ext_component
      intro i q h x
      have hq : i+j+1 = q := by omega
      subst hq
      change (δ j (j+1) ((scalarOperator M j z).val ())).v i (i+j+1) (by omega) x = _
      rw [δ_v j (j+1) rfl _ i (i+j+1) (by omega) (i+j) (i+1) (by omega) rfl]
      simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
        ModuleCat.hom_smul, LinearMap.smul_apply]
      change (M.complex ()).d (i+j) (i+j+1) ((i*j).negOnePow • _) +
        (j+1).negOnePow • (((i+1)*j).negOnePow • _) = (i*(j+1)).negOnePow • _
      simp only [LinearMap.flip_apply]
      rw [map_zsmul_unit, M.leibniz]
      simp only [smul_add, smul_smul, add_mul, mul_add, one_mul, mul_one, Int.negOnePow_add,
        Int.negOnePow_one, mul_neg, mul_one, neg_mul, Units.neg_smul]
      have hs : j.negOnePow * ((i*j).negOnePow * j.negOnePow) = (i*j).negOnePow := by
        rw [← mul_assoc, mul_comm j.negOnePow (i*j).negOnePow, mul_assoc, Int.units_mul_self, mul_one]
      rw [hs]
      abel)
  map_id a := by
    cases a
    apply ext_component
    intro i q h x
    rw [add_zero] at h
    subst h
    change (i*0).negOnePow • M.act i 0 i (add_zero i) x A.one =
      (Cochain.ofHom ((𝟙 M : M ⟶ M).app ())).v i i (add_zero i) x
    rw [Cochain.ofHom_v, mul_zero, Int.negOnePow_zero, one_smul, M.act_id]
    rfl
  map_comp {a b c} i j n h z y := by
    cases a
    cases b
    cases c
    subst n
    apply ext_component
    intro l q e x
    change component (scalarOperator M (i+j) (A.mul i j (i+j) rfl z y)) () l q e x =
      (Cochain.comp ((scalarOperator M j y).val ()) ((scalarOperator M i z).val ())
        (add_comm j i)).v l q e x
    rw [Cochain.comp_v _ _ _ l (l+j) q rfl (by omega)]
    simp only [scalarOperator_apply, ModuleCat.comp_apply]
    rw [show M.act (l+j) i q (by omega)
        ((l*j).negOnePow • M.act l j (l+j) rfl x y) z =
        (l*j).negOnePow • M.act (l+j) i q (by omega) (M.act l j (l+j) rfl x y) z from
      map_zsmul_unit ((M.act (l+j) i q (by omega)).flip z) _ _, smul_smul]
    have hs : (l*i+l*j).negOnePow * (j*i).negOnePow =
        ((l+j)*i).negOnePow * (l*j).negOnePow := by
      rw [add_mul, Int.negOnePow_add, Int.negOnePow_add]
      ac_rfl
    rw [mul_add, ← hs, mul_smul]
    rw [act_assoc_at M l j i (l+j) (j+i) q rfl rfl (by omega),
      A.graded_comm j i (j+i) rfl y z, map_zsmul_unit]
    simp only [smul_smul, Int.units_mul_self, mul_one]
    have same (p : ℤ) (hp : i+j = p) :
        M.act l (i+j) q e x (A.mul i j (i+j) rfl z y) =
          M.act l p q (by omega) x (A.mul i j p hp z y) := by
      subst p
      rfl
    rw [same (j+i) (add_comm i j)]

/-- The internal Hom uses the G03 complex, with the right action induced by
precomposition with the left scalar operator of the source. -/
@[reducible] def internalHom (M N : Mod A) : Mod A where
  complex _ := homComplex M N
  act {a b} i j n h :=
    (LinearMap.lcomp k _ ((scalarRepresentation M).map a b |>.f j |>.hom)).comp
      (compose M M N i j n h)
  act_id a i x := by
    change compose M M N i 0 i _ x (((scalarRepresentation M).map a a).f 0
      ((algebraCategory A).id a)) = x
    rw [(scalarRepresentation M).map_id]
    exact (HomComplex.dgModuleCategory (algebraCategory A)).toData.comp_id i x
  act_assoc {a b c} i j l f z y := by
    change compose M M N (i+j) l (i+j+l) _
        (compose M M N i j (i+j) _ f (((scalarRepresentation M).map b c).f j z))
        (((scalarRepresentation M).map a b).f l y) =
      compose M M N i (j+l) (i+j+l) _ f
        (((scalarRepresentation M).map a c).f (j+l) ((algebraCategory A).comp j l (j+l) rfl z y))
    rw [(scalarRepresentation M).map_comp]
    exact (HomComplex.dgModuleCategory (algebraCategory A)).toData.assoc i j l f _ _
  leibniz {a b} i j n h f z := by
    let F := scalarRepresentation M
    change (homComplex M N).d n (n+1) (compose M M N i j n h f ((F.map a b).f j z)) =
      compose M M N (i+1) j (n+1) _ ((homComplex M N).d i (i+1) f) ((F.map a b).f j z) +
        i.negOnePow • compose M M N i (j+1) (n+1) _ f
          ((F.map a b).f (j+1) (((algebraCategory A).hom a b).d j (j+1) z))
    rw [show (F.map a b).f (j+1) (((algebraCategory A).hom a b).d j (j+1) z) =
        (homComplex M M).d j (j+1) ((F.map a b).f j z) from
      (CategoryTheory.congr_fun ((F.map a b).comm j (j+1)) z).symm]
    exact (HomComplex.dgModuleCategory (algebraCategory A)).toData.leibniz i j n h f _


def InternalHomType := ∀ {k : Type u} [Field k] [CharZero k]
    {A : CommDGAlgebra.{u,v} k}, Mod A → Mod A → Mod A

/-- The right scalar action contributes a sign on a homogeneous input.
The extra sign converting the right action to the left action is
the sign from passing the scalar past the degree of the map. -/
def ScalarFormula : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A : CommDGAlgebra.{u,v} k}
    (M N : Mod A) (r j n : ℤ) (h : r+j = n) (f : gradedHom M N r)
    (z : A.complex.X j) (i q ir : ℤ) (e : i+n = q) (er : i+r = ir)
    (x : (M.complex ()).X i),
    component ((internalHom M N).act (a := ()) (b := ()) r j n h f z) () i q e x =
      (i*j).negOnePow • N.act ir j q (by omega) (component f () i ir er x) z

/-- Compatibility of the right-module convention with the pointwise left action,
including graded left-linearity of every homogeneous map. -/
def LeftScalarFormula : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A : CommDGAlgebra.{u,v} k}
    (M N : Mod A) (r j n : ℤ) (h : r+j = n) (f : gradedHom M N r)
    (z : A.complex.X j) (i q ir : ℤ) (e : i+n = q) (er : i+r = ir)
    (x : (M.complex ()).X i),
    component (scalarOperator (internalHom M N) j z |> fun g =>
      component g () r n h f) () i q e x =
      component (scalarOperator N j z) () ir q (by omega) (component f () i ir er x) ∧
    component f () (i+j) q (by omega) (component (scalarOperator M j z) () i (i+j) rfl x) =
      (r*j).negOnePow • component (scalarOperator N j z) () ir q (by omega) (component f () i ir er x)

/-- The maps on the internal Hom, including the two maps on right-linear homotopies. -/
structure HomActions (A : CommDGAlgebra.{u,v} k) where
  pre {L M : Mod A} (N : Mod A) (f : L ⟶ M) : internalHom M N ⟶ internalHom L N
  post {N P : Mod A} (M : Mod A) (g : N ⟶ P) : internalHom M N ⟶ internalHom M P
  preGraded {L M : Mod A} (N : Mod A) {s : ℤ} (f : gradedHom L M s) :
    gradedHom (internalHom M N) (internalHom L N) s
  postGraded {N P : Mod A} (M : Mod A) {s : ℤ} (g : gradedHom N P s) :
    gradedHom (internalHom M N) (internalHom M P) s

structure HomActionLaws (A : CommDGAlgebra.{u,v} k) (F : HomActions A) : Prop where
  pre {L M N : Mod A} (f : L ⟶ M) (r : ℤ) (g : gradedHom M N r)
    (i q : ℤ) (e : i+r = q) (x : (L.complex ()).X i) :
    component ((F.pre N f).app () |>.f r |>.hom g) () i q e x =
      component g () i q e ((f.app ()).f i x)
  post {M N P : Mod A} (g : N ⟶ P) (r : ℤ) (f : gradedHom M N r)
    (i q : ℤ) (e : i+r = q) (x : (M.complex ()).X i) :
    component ((F.post M g).app () |>.f r |>.hom f) () i q e x =
      (g.app ()).f q (component f () i q e x)
  preGraded {L M N : Mod A} (r s q : ℤ) (e : r+s = q)
    (g : gradedHom L M s) (f : gradedHom M N r) :
    component (F.preGraded N g) () r q e f =
      (r*s).negOnePow • compose L M N r s q e f g
  postGraded {M N P : Mod A} (r s q : ℤ) (e : r+s = q)
    (g : gradedHom N P s) (f : gradedHom M N r) :
    component (F.postGraded M g) () r q e f = compose M N P s r q (by omega) g f
  preHomotopy {L M N : Mod A} {f g : L ⟶ M} {h : gradedHom L M (-1)} :
    HomComplex.HomotopyEquation f g h →
      HomComplex.HomotopyEquation (F.pre N f) (F.pre N g) (F.preGraded N h)
  postHomotopy {M N P : Mod A} {f g : N ⟶ P} {h : gradedHom N P (-1)} :
    HomComplex.HomotopyEquation f g h →
      HomComplex.HomotopyEquation (F.post M f) (F.post M g) (F.postGraded M h)

def HomActionsExist : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CommDGAlgebra.{u,v} k),
    ∃ F : HomActions A, HomActionLaws A F

open Opposite
open DerivedKProjective
open HomComplex (homotopyCategory homotopyClass)

abbrev K (A : CommDGAlgebra.{u,v} k) := homotopyCategory (algebraCategory A)

abbrev Kp (A : CommDGAlgebra.{u,v} k) (h : Derived.HomotopyCategoryLaws (algebraCategory A)) :=
  @ObjectProperty.FullSubcategory (K A) (Derived.homotopyCategory (algebraCategory A) h)
    (kProjectiveObjects (algebraCategory A))

section Descent

variable (A : CommDGAlgebra.{u,v} k)
variable [h : Fact (Derived.HomotopyCategoryLaws (algebraCategory A))]

noncomputable local instance : Category (K A) := Derived.homotopyCategory (algebraCategory A) h.out
noncomputable local instance : Category (Derived.derivedCategory (algebraCategory A) h.out) :=
  derivedCategoryInstance (algebraCategory A) h.out

noncomputable abbrev derivedInputs :
    (Kp A h.out)ᵒᵖ × K A ⥤ (Derived.derivedCategory (algebraCategory A) h.out)ᵒᵖ ×
      Derived.derivedCategory (algebraCategory A) h.out :=
  (restrictedLocalization (algebraCategory A) h.out).op.prod (Derived.quotient (algebraCategory A) h.out)

noncomputable abbrev modelInputs :
    (Kp A h.out)ᵒᵖ × K A ⥤ (K A)ᵒᵖ × K A :=
  ((kProjectiveObjects (algebraCategory A)).ι).op.prod (𝟭 (K A))

abbrev modelDenominators : MorphismProperty ((Kp A h.out)ᵒᵖ × K A) :=
  (MorphismProperty.isomorphisms _).prod (Derived.quasiIsomorphisms (algebraCategory A))

noncomputable abbrev localizedModels (H : (K A)ᵒᵖ × K A ⥤ K A) :
    (Kp A h.out)ᵒᵖ × K A ⥤ Derived.derivedCategory (algebraCategory A) h.out :=
  modelInputs A ⋙ H ⋙ Derived.quotient (algebraCategory A) h.out

/-- Given the homotopy functor and its proved inversion property, the
canonical derived value is the localization lift on the product. -/
noncomputable def deriveFromModels (H : (K A)ᵒᵖ × K A ⥤ K A)
    [ (derivedInputs A).IsLocalization (modelDenominators A) ]
    (inv : (modelDenominators A).IsInvertedBy (localizedModels A H)) :
    (Derived.derivedCategory (algebraCategory A) h.out)ᵒᵖ × Derived.derivedCategory (algebraCategory A) h.out
      ⥤ Derived.derivedCategory (algebraCategory A) h.out :=
  Localization.lift (localizedModels A H) inv (derivedInputs A)

def DeriveFromModelsType :=
  ∀ (H : (K A)ᵒᵖ × K A ⥤ K A)
    [(derivedInputs A).IsLocalization (modelDenominators A)],
    (modelDenominators A).IsInvertedBy (localizedModels A H) →
    (Derived.derivedCategory (algebraCategory A) h.out)ᵒᵖ × Derived.derivedCategory (algebraCategory A) h.out
      ⥤ Derived.derivedCategory (algebraCategory A) h.out

end Descent

def DeriveFromModelsFamilyType :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CommDGAlgebra.{u,v} k)
    [Fact (Derived.HomotopyCategoryLaws (algebraCategory A))], DeriveFromModelsType A

/-- The internal derived Hom is a bifunctor on the specified localization.
On the K-projective first variable it naturally factors the actual dg Hom,
and the comparison holds for every strict K-projective replacement. -/
def DerivedHomRealization : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CommDGAlgebra.{u,v} k)
    (h : Derived.HomotopyCategoryLaws (algebraCategory A)),
    let B := algebraCategory A
    letI := Derived.homotopyCategory B h
    let D := Derived.derivedCategory B h
    letI := derivedCategoryInstance B h
    let Q := Derived.quotient B h
    let Qp := restrictedLocalization B h
    let J : Kp A h ⥤ K A := (kProjectiveObjects B).ι
    ∃ (S : HomActions A) (H : (K A)ᵒᵖ × K A ⥤ K A) (F : Dᵒᵖ × D ⥤ D),
      HomActionLaws A S ∧
      (∀ (M N : Mod A), H.obj (op M, N) = internalHom M N) ∧
      (∀ {L M N P : Mod A} (f : L ⟶ M) (g : N ⟶ P),
        let f₀ : @Quiver.Hom (K A) _ L M := homotopyClass f
        let g₀ : @Quiver.Hom (K A) _ N P := homotopyClass g
        HEq (H.map (CategoryTheory.Prod.mkHom f₀.op g₀))
          (homotopyClass (S.pre N f ≫ S.post L g))) ∧
      ∃ σ : Qp.op.prod Q ⋙ F ≅ J.op.prod (𝟭 (K A)) ⋙ H ⋙ Q,
      (∀ {X X' : Dᵒᵖ × D} {Y Y' : (Kp A h)ᵒᵖ × K A}
        (e : X ≅ (Qp.op.prod Q).obj Y) (e' : X' ≅ (Qp.op.prod Q).obj Y')
        (f : X ⟶ X') (g : Y ⟶ Y'),
        f ≫ e'.hom = e.hom ≫ (Qp.op.prod Q).map g →
        F.map f ≫ ((F.mapIso e') ≪≫ σ.app Y').hom =
          ((F.mapIso e) ≪≫ σ.app Y).hom ≫ (J.op.prod (𝟭 (K A)) ⋙ H ⋙ Q).map g) ∧
      ∀ {P M : Mod A} (p : P ⟶ M),
        Module.quasiIsomorphism p → KProjective.isKProjective P → ∀ N : Mod A,
        Nonempty (F.obj (op (Q.obj M), Q.obj N) ≅ Q.obj (internalHom P N))


def LiftAlgebraType :=
  ∀ {k : Type u} [Field k] [CharZero k], CommDGAlgebra.{u,v} k → CommDGAlgebra.{u,max v t} k

open CoefficientLiftComparison (GradedComparisonFamily)
open HomComplex (HomotopyEquation)

abbrev liftedModule (M : Mod A) : Mod (liftAlgebra.{u,v,t} A) :=
  (AmbientDerived.strictInput.{u,v,0,t} (algebraCategory A)).obj M

/-- Original homogeneous Hom elements are conjugated by the degreewise
linear equivalences, before taking cohomology or localization. -/
structure CoefficientConjugationLaws (A : CommDGAlgebra.{u,v} k)
    (E : ∀ M N : Mod A, GradedComparisonFamily.{u,v,0,t} M N) : Prop where
  component (M N : Mod A) (r : ℤ) (f : gradedHom M N r)
      (i q : ℤ) (h : i+r = q) (x : (M.complex ()).X i) :
    (HomComplex.component (E M N r f) () i q h (ULift.up x)).down =
      HomComplex.component f () i q h x
  action (M N : Mod A) (r j n : ℤ) (h : r+j = n) (f : gradedHom M N r) (z : A.complex.X j) :
    E M N n ((internalHom M N).act (a := ()) (b := ()) r j n h f z) =
      (internalHom (liftedModule.{u,v,t} M) (liftedModule.{u,v,t} N)).act (a := ()) (b := ()) r j n h
        (E M N r f) (ULift.up z)
  differential (M N : Mod A) (r q : ℤ) (f : gradedHom M N r) :
    E M N q ((homComplex M N).d r q f) =
      (homComplex (liftedModule.{u,v,t} M) (liftedModule.{u,v,t} N)).d r q (E M N r f)
  composition (M N P : Mod A) (s r q : ℤ) (h : s+r = q)
      (g : gradedHom N P s) (f : gradedHom M N r) :
    E M P q (compose M N P s r q h g f) =
      compose (liftedModule.{u,v,t} M) (liftedModule.{u,v,t} N) (liftedModule.{u,v,t} P)
        s r q h (E N P s g) (E M N r f)
  strictMap {M N : Mod A} (f : M ⟶ N) :
    E M N 0 (ofStrict f) = ofStrict ((AmbientDerived.strictInput.{u,v,0,t} (algebraCategory A)).map f)
  homotopy {M N : Mod A} (f g : M ⟶ N) (h : gradedHom M N (-1)) :
    let U := AmbientDerived.strictInput.{u,v,0,t} (algebraCategory A)
    HomotopyEquation (U.map f) (U.map g) (E M N (-1) h) ↔ HomotopyEquation f g h
  moduleIso (M N : Mod A) :
    ∃ α : liftedModule.{u,v,t} (internalHom M N) ≅
        internalHom (liftedModule.{u,v,t} M) (liftedModule.{u,v,t} N),
      ∀ r (f : ((liftedModule.{u,v,t} (internalHom M N)).complex ()).X r),
        (α.hom.app ()).f r f = E M N r f.down

def CoefficientConjugation : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CommDGAlgebra.{u,v} k),
    ∃ E : ∀ M N : Mod A, GradedComparisonFamily.{u,v,0,t} M N,
      CoefficientConjugationLaws.{u,v,t} A E

/-- The same model calculation holds on the common ambient localization
for all coefficient bounds and all original dg modules. -/
def AmbientModels : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CommDGAlgebra.{u,v} k)
    (h : Derived.HomotopyCategoryLaws (AmbientDerived.category.{u,v,0,t} (algebraCategory A))),
    let B := AmbientDerived.category.{u,v,0,t} (algebraCategory A)
    letI := Derived.homotopyCategory B h
    let D := AmbientDerived.derivedCategory.{u,v,0,t} (algebraCategory A) h
    letI := derivedCategoryInstance B h
    let Q := AmbientDerived.quotient.{u,v,0,t} (algebraCategory A) h
    ∃ F : Dᵒᵖ × D ⥤ D,
      (∀ {P M : Mod (liftAlgebra.{u,v,t} A)} (p : P ⟶ M),
        Module.quasiIsomorphism p → KProjective.isKProjective P → ∀ N : Mod (liftAlgebra.{u,v,t} A),
        Nonempty (F.obj (op (Q.obj M), Q.obj N) ≅ Q.obj (internalHom P N))) ∧
      ∀ M N : Mod A,
        ∃ (P : Mod (liftAlgebra.{u,v,t} A)) (p : P ⟶ liftedModule.{u,v,t} M),
          KProjective.isKProjective P ∧ Module.quasiIsomorphism p ∧
          Nonempty (F.obj (op (Q.obj (liftedModule.{u,v,t} M)), Q.obj (liftedModule.{u,v,t} N)) ≅
            Q.obj (internalHom P (liftedModule.{u,v,t} N)))

end Specs.DerivedFormalization.Affine.DerivedHom
