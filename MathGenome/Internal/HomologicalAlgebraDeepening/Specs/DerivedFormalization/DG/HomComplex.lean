import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Module
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

open CategoryTheory
open CochainComplex.HomComplex

universe u v w

namespace Specs.DerivedFormalization.DG.HomComplex

open _root_.DerivedFormalization

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}

abbrev Family (M N : RightDGModuleModel A) (r : ℤ) :=
  ∀ a, Cochain (M.complex a) (N.complex a) r

/-- Right-linearity of a homogeneous family, with the same action on each side. -/
def RightLinear {M N : RightDGModuleModel A} {r : ℤ} (f : Family M N r) : Prop :=
  ∀ {a b : A.Obj} (i j n ir nr : ℤ) (h : i+j = n) (hi : i+r = ir) (hn : n+r = nr)
      (x : (M.complex b).X i) (z : (A.hom a b).X j),
    (f a).v n nr hn (M.act i j n h x z) =
      N.act ir j nr (by omega) ((f b).v i ir hi x) z

/-- All homogeneous right-linear families form a submodule of the product. -/
def gradedHomSubmodule (M N : RightDGModuleModel A) (r : ℤ) :
    Submodule k (Family M N r) where
  carrier := {f | RightLinear f}
  zero_mem' := by
    intro a b i j n ir nr h hi hn x z
    simp
  add_mem' := by
    intro f g hf hg a b i j n ir nr h hi hn x z
    have hf' := hf (a := a) (b := b) i j n ir nr h hi hn x z
    have hg' := hg (a := a) (b := b) i j n ir nr h hi hn x z
    simp only [Pi.add_apply, Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply, map_add, hf', hg']
  smul_mem' := by
    intro c f hf a b i j n ir nr h hi hn x z
    have hf' := hf (a := a) (b := b) i j n ir nr h hi hn x z
    simp only [Pi.smul_apply, Cochain.smul_v, ModuleCat.hom_smul, map_smul,
      LinearMap.smul_apply, hf']

abbrev gradedHom (M N : RightDGModuleModel A) (r : ℤ) :=
  ↥(gradedHomSubmodule M N r)

variable {M N P Q : RightDGModuleModel A} {r s t : ℤ}

/-- A coefficient of the homogeneous map, with a specified target index. -/
abbrev component (f : gradedHom M N r) (a : A.Obj) (i q : ℤ) (h : i+r = q) :
    (M.complex a).X i ⟶ (N.complex a).X q :=
  (f.val a).v i q h

/-- The differential before restricting to right-linear families. -/
abbrev differential (r s : ℤ) (f : Family M N r) : Family M N s :=
  fun a => δ r s (f a)

theorem differential_rightLinear {f : Family M N r} (hf : RightLinear f) :
    RightLinear (differential r (r+1) f) := by
  intro a b i j n ir nr h hi hn x z
  have en : n + (r+1) = nr := hn
  have ei : i + (r+1) = ir := hi
  rw [δ_v r (r+1) rfl (f a) n nr en (n+r) (n+1) (by omega) rfl,
    δ_v r (r+1) rfl (f b) i ir ei (i+r) (i+1) (by omega) rfl]
  have hn' : (n+r)+1 = nr := by omega
  have hi' : (i+r)+1 = ir := by omega
  subst hn' hi'
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul,
    Units.smul_def, LinearMap.smul_apply]
  rw [hf (a := a) (b := b) i j n (i+r) (n+r) h rfl rfl x z,
    N.leibniz (i+r) j (n+r) (by omega),
    M.leibniz i j n h]
  simp only [map_add, LinearMap.add_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply]
  rw [hf (a := a) (b := b) (i+1) j (n+1) ((i+r)+1) ((n+r)+1)
      (by omega) (by omega) (by omega) ((M.complex b).d i (i+1) x) z,
    hf (a := a) (b := b) i (j+1) (n+1) (i+r) ((n+r)+1)
      (by omega) rfl (by omega) x ((A.hom a b).d j (j+1) z)]
  rw [Int.negOnePow_succ]
  simp only [smul_add, smul_smul, Int.negOnePow_add,
    Units.val_neg, Units.val_mul, neg_mul, mul_comm (r.negOnePow : ℤ) (i.negOnePow : ℤ),
    neg_smul]
  abel

/-- The differential restricted to the submodule of right-linear families. -/
def restrictedDifferential (M N : RightDGModuleModel A) (r s : ℤ) :
    gradedHom M N r →ₗ[k] gradedHom M N s where
  toFun f := ⟨differential r s f.val, by
    by_cases h : r+1 = s
    · subst s
      exact differential_rightLinear f.property
    · have e : differential r s f.val = 0 := funext fun a => δ_shape r s h (f.val a)
      rw [e]
      exact (gradedHomSubmodule M N s).zero_mem⟩
  map_add' f g := Subtype.ext (funext fun a => δ_add r s (f.val a) (g.val a))
  map_smul' c f := Subtype.ext (funext fun a => δ_smul r s c (f.val a))

/-- The Hom complex of dg modules, with the restricted commutator differential. -/
@[reducible] def homComplex (M N : RightDGModuleModel A) : ModuleCochain.{u,max v w} k where
  X r := ModuleCat.of k (gradedHom M N r)
  d r s := ModuleCat.ofHom (restrictedDifferential M N r s)
  shape r s h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact funext fun a => δ_shape r s h (f.val a)
  d_comp_d' r s t _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact funext fun a => δ_δ r s t (f.val a)

/-- Ordinary composition applied to homogeneous families, in the order `g ∘ f`. -/
abbrev composition (e : s+r = t) (g : Family N P s) (f : Family M N r) :
    Family M P t :=
  fun a => (f a).comp (g a) ((add_comm r s).trans e)

theorem composition_rightLinear (e : s+r = t) {g : Family N P s} {f : Family M N r}
    (hg : RightLinear g) (hf : RightLinear f) :
    RightLinear (composition e g f) := by
  intro a b i j n it nt h hi hn x z
  change ((f a).comp (g a) _).v n nt hn _ = P.act it j nt _ (((f b).comp (g b) _).v i it hi x) z
  rw [Cochain.comp_v (f a) (g a) _ n (n+r) nt rfl (by omega),
    Cochain.comp_v (f b) (g b) _ i (i+r) it rfl (by omega)]
  simp only [ModuleCat.comp_apply]
  rw [hf (a := a) (b := b) i j n (i+r) (n+r) h rfl rfl x z,
    hg (a := a) (b := b) (i+r) j (n+r) it nt (by omega) (by omega) (by omega)]

/-- The bilinear composition of graded right-linear maps. -/
def compose (M N P : RightDGModuleModel A) (s r t : ℤ) (e : s+r = t) :
    gradedHom N P s →ₗ[k] gradedHom M N r →ₗ[k] gradedHom M P t where
  toFun g :=
    { toFun := fun f => ⟨composition e g.val f.val, composition_rightLinear e g.property f.property⟩
      map_add' := fun f f' => Subtype.ext (funext fun a => Cochain.add_comp (f.val a) (f'.val a) (g.val a) ((add_comm r s).trans e))
      map_smul' := fun c f => Subtype.ext (funext fun a => Cochain.smul_comp c (f.val a) (g.val a) ((add_comm r s).trans e)) }
  map_add' g g' := LinearMap.ext fun f =>
    Subtype.ext (funext fun a => Cochain.comp_add (f.val a) (g.val a) (g'.val a) ((add_comm r s).trans e))
  map_smul' c g := LinearMap.ext fun f =>
    Subtype.ext (funext fun a => Cochain.comp_smul (f.val a) c (g.val a) ((add_comm r s).trans e))

/-- A strict module map as a homogeneous map of degree zero. -/
def ofStrict (f : RightDGModuleHomModel M N) : gradedHom M N 0 :=
  ⟨fun a => Cochain.ofHom (f.app a), by
    intro a b i j n ir nr h hi hn x z
    rw [add_zero] at hi hn
    subst hi hn
    simp only [Cochain.ofHom_v]
    exact f.comm_act i j n h x z⟩

/-- The right dg modules form a dg category over the same base ring. -/
@[reducible] def dgModuleCategory (A : DGCategoryModel.{u,v,w} k) :
    DGCategoryModel.{u,max v w,max u w (v+1)} k where
  Obj := RightDGModuleModel A
  toData :=
    { hom := homComplex
      comp := fun {M N P} s r t e => compose M N P s r t e
      id := fun M => ofStrict (𝟙 M)
      d_id := by
        intro M
        apply Subtype.ext
        exact funext fun a => δ_ofHom _
      id_comp := by
        intro M N r f
        apply Subtype.ext
        exact funext fun a => (f.val a).comp_id
      comp_id := by
        intro M N r f
        apply Subtype.ext
        exact funext fun a => Cochain.id_comp (f.val a)
      assoc := by
        intro M N P Q i j l f g h
        apply Subtype.ext
        exact funext fun a => (Cochain.comp_assoc (h.val a) (g.val a) (f.val a)
          (show l+j = j+l by omega) (show j+i = i+j by omega) (by omega)).symm
      leibniz := by
        intro M N P s r t e g f
        apply Subtype.ext
        exact funext fun a => δ_comp (f.val a) (g.val a) (show r+s = t by omega)
          (r+1) (s+1) (t+1) rfl rfl rfl }

open Basic (classOf cyclesZero h0Hom h0Objects)

/-- The degree-zero cocycle representing a strict module map. -/
def strictCycle (f : RightDGModuleHomModel M N) : cyclesZero (homComplex M N) :=
  ⟨ofStrict f, Subtype.ext (funext fun a => δ_ofHom (f.app a))⟩

/-- The homotopy category of right dg modules. -/
@[implicit_reducible] def homotopyCategory (A : DGCategoryModel.{u,v,w} k) :=
  h0Objects (dgModuleCategory A)

/-- The morphism class of a strict map in the homotopy category. -/
noncomputable def homotopyClass (f : RightDGModuleHomModel M N) : h0Hom (homComplex M N) :=
  classOf (strictCycle f)

/-- A right-linear degree `-1` homotopy satisfies the usual component equation. -/
def HomotopyEquation (f g : RightDGModuleHomModel M N) (h : gradedHom M N (-1)) : Prop :=
  ∀ (a : A.Obj) (i : ℤ) (x : (M.complex a).X i),
    (f.app a).f i x - (g.app a).f i x =
      (N.complex a).d (i-1) i (component h a i (i-1) (by omega) x) +
        component h a (i+1) i (by omega) ((M.complex a).d i (i+1) x)

def HomotopyCriterion : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f g : RightDGModuleHomModel M N),
    homotopyClass f = homotopyClass g ↔ ∃ h : gradedHom M N (-1), HomotopyEquation f g h

def ClosedMapIdentification : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (z : cyclesZero (homComplex M N)),
    ∃! f : RightDGModuleHomModel M N, strictCycle f = z

/-- Computing the differential on any homogeneous component. -/
def DifferentialFormula : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (r : ℤ) (f : gradedHom M N r)
    (a : A.Obj) (i q : ℤ) (e : i+(r+1) = q) (x : (M.complex a).X i),
    component ((homComplex M N).d r (r+1) f) a i q e x =
      (N.complex a).d (i+r) q (component f a i (i+r) rfl x) -
        r.negOnePow • component f a (i+1) q (by omega) ((M.complex a).d i (i+1) x)

/-- Computing the composition at any choices of homogeneous indices. -/
def CompositionFormula : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N P : RightDGModuleModel A} (s r t : ℤ) (e : s+r = t)
    (g : gradedHom N P s) (f : gradedHom M N r)
    (a : A.Obj) (i j n : ℤ) (hij : i+r = j) (hjn : j+s = n)
    (x : (M.complex a).X i),
    component ((dgModuleCategory A).comp s r t e g f) a i n (by omega) x =
      component g a j n hjn (component f a i j hij x)

set_option linter.checkUnivs false
def GradedHomType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    RightDGModuleModel A → RightDGModuleModel A → ℤ → Type (max v w)

def HomComplexType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    RightDGModuleModel A → RightDGModuleModel A → ModuleCochain.{u,max v w} k

def DGModuleCategoryType :=
  ∀ {k : Type u} [CommRing k], DGCategoryModel.{u,v,w} k →
    DGCategoryModel.{u,max v w,max u w (v+1)} k

def HomotopyCategoryType :=
  ∀ {k : Type u} [CommRing k], DGCategoryModel.{u,v,w} k → Type (max u w (v+1))

def HomotopyCategoryStructure : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    ∃ C : Category.{max v w} (homotopyCategory A),
      C.toCategoryStruct = Basic.h0CategoryStruct (dgModuleCategory A)

def HomotopyClassType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A}, RightDGModuleHomModel M N → h0Hom (homComplex M N)

end Specs.DerivedFormalization.DG.HomComplex
