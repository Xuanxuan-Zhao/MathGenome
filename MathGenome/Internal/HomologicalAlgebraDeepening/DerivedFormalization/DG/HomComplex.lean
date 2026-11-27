import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Module
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomComplex

open CategoryTheory CochainComplex.HomComplex

universe u v w

namespace DerivedFormalization

open Specs.DerivedFormalization.DG.Basic (boundariesZero classOf cyclesZero h0Hom)
open Specs.DerivedFormalization.DG.HomComplex (HomotopyEquation)

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

namespace RightDGModule

/-- Degree-`r` homogeneous right-linear maps. -/
abbrev GradedHom (M N : RightDGModule A) (r : ℤ) :=
  Specs.DerivedFormalization.DG.HomComplex.gradedHom M N r

namespace GradedHom

variable {M N : RightDGModule A} {r : ℤ}

abbrev app (f : GradedHom M N r) (a : A.Obj) (i q : ℤ) (h : i+r = q) :=
  Specs.DerivedFormalization.DG.HomComplex.component f a i q h

/-- Construct a homogeneous map from a family of maps and its right-linearity. -/
def mk (f : ∀ (a : A.Obj) (i q : ℤ) (_ : i+r = q),
    (M.complex a).X i ⟶ (N.complex a).X q)
    (comm : ∀ {a b : A.Obj} (i j n ir nr : ℤ)
      (h : i+j = n) (hi : i+r = ir) (hn : n+r = nr)
      (x : (M.complex b).X i) (z : (A.hom a b).X j),
      f a n nr hn (M.act i j n h x z) =
        N.act ir j nr (by omega) (f b i ir hi x) z) :
    GradedHom M N r :=
  ⟨fun a => Cochain.mk (f a), comm⟩

@[simp] theorem mk_app (f) (comm) (a : A.Obj) (i q : ℤ) (e : i+r = q) :
    (mk (M := M) (N := N) f comm).app a i q e = f a i q e := rfl

theorem comm_act (f : GradedHom M N r) {a b : A.Obj} (i j n ir nr : ℤ)
    (h : i+j = n) (hi : i+r = ir) (hn : n+r = nr)
    (x : (M.complex b).X i) (z : (A.hom a b).X j) :
    f.app a n nr hn (M.act i j n h x z) =
      N.act ir j nr (by omega) (f.app b i ir hi x) z :=
  f.property i j n ir nr h hi hn x z

@[ext] theorem ext {f g : GradedHom M N r}
    (h : ∀ (a : A.Obj) (i q : ℤ) (e : i+r = q), f.app a i q e = g.app a i q e) :
    f = g :=
  Subtype.ext (funext fun a => Cochain.ext _ _ (h a))

end GradedHom

/-- The cochain complex of homogeneous right-linear maps. -/
abbrev homComplex (M N : RightDGModule A) : ModuleCochain.{u,max v w} k :=
  Specs.DerivedFormalization.DG.HomComplex.homComplex M N

/-- Right dg modules, with Hom complexes and graded composition. -/
abbrev dgCategory (A : DGCategory.{u,v,w} k) :
    DGCategory.{u,max v w,max u w (v+1)} k :=
  Specs.DerivedFormalization.DG.HomComplex.dgModuleCategory A

/-- The homotopy category `K(A)`, obtained by taking degree-zero cohomology. -/
@[implicit_reducible] def K (A : DGCategory.{u,v,w} k) :=
  (dgCategory A).H0

noncomputable instance (A : DGCategory.{u,v,w} k) : Category.{max v w} (K A) :=
  inferInstanceAs (Category ((dgCategory A).H0))

variable {M N P : RightDGModule A}

/-- The degree-zero cycle of a strict map. -/
abbrev strictCycle (f : M ⟶ N) : cyclesZero (homComplex M N) :=
  Specs.DerivedFormalization.DG.HomComplex.strictCycle f

/-- The strict map represented by a degree-zero cocycle. -/
def strictMap (z : cyclesZero (homComplex M N)) : M ⟶ N where
  app a := CochainComplex.ofHom (fun i => GradedHom.app z.val a i i (add_zero i)) (by
    intro i
    have hz : (homComplex M N).d 0 1 z.val = 0 := z.property
    have e := Cochain.congr_v (congrArg (fun f : GradedHom M N 1 => f.val a) hz)
      i (i+1) rfl
    change (δ 0 1 (z.val.val a)).v i (i+1) rfl = 0 at e
    exact sub_eq_zero.mp (by simpa only [δ_zero_cochain_v] using e))
  comm_act := by
    intro a b i j n h x y
    exact GradedHom.comm_act z.val i j n i n h (add_zero i) (add_zero n) x y

@[simp] theorem strictMap_strictCycle (f : M ⟶ N) : strictMap (strictCycle f) = f := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  exact Cochain.ofHom_v (f.app a) i

@[simp] theorem strictCycle_strictMap (z : cyclesZero (homComplex M N)) :
    strictCycle (strictMap z) = z := by
  apply Subtype.ext
  apply GradedHom.ext (M := M) (N := N)
  intro a i q e
  rw [add_zero] at e
  subst e
  exact Cochain.ofHom_v (strictMap z |>.app a) i

/-- The degree-zero cycles are precisely the strict module maps. -/
theorem closedMapIdentification (z : cyclesZero (homComplex M N)) :
    ∃! f : M ⟶ N, strictCycle f = z := by
  refine ⟨strictMap z, strictCycle_strictMap z, ?_⟩
  intro f hf
  rw [← hf, strictMap_strictCycle]

/-- the morphism of `K(A)` determined by a closed degree-zero map. -/
noncomputable abbrev homotopyClass (f : M ⟶ N) : h0Hom (homComplex M N) :=
  Specs.DerivedFormalization.DG.HomComplex.homotopyClass f

/-- The identity-on-objects functor sending strict module maps to homotopy classes. -/
noncomputable def toHomotopyCategory (A : DGCategory.{u,v,w} k) :
    RightDGModule A ⥤ K A where
  obj M := M
  map f := homotopyClass f
  map_id _ := rfl
  map_comp {M N P} f g := by
    change classOf (strictCycle (f ≫ g)) =
      Specs.DerivedFormalization.DG.Basic.h0Comp (dgCategory A)
        (classOf (strictCycle g)) (classOf (strictCycle f))
    rw [DGCategory.h0Comp_mk (dgCategory A) (a := M) (b := N) (c := P)]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact funext fun a => Cochain.ofHom_comp (f.app a) (g.app a)

/-- The boundary of a degree-`-1` cochain, on homogeneous elements. -/
theorem boundary_component (h : GradedHom M N (-1)) (a : A.Obj) (i : ℤ)
    (x : (M.complex a).X i) :
    GradedHom.app ((homComplex M N).d (-1) 0 h) a i i (add_zero i) x =
      (N.complex a).d (i-1) i (h.app a i (i-1) (by omega) x) +
        h.app a (i+1) i (by omega) ((M.complex a).d i (i+1) x) := by
  change (δ (-1) 0 (h.val a)).v i i (add_zero i) x = _
  rw [δ_v (-1) 0 (by decide) _ i i (add_zero i) (i-1) (i+1) rfl rfl]
  simp only [Int.negOnePow_zero, one_smul, ModuleCat.hom_add, LinearMap.add_apply,
    ModuleCat.comp_apply]

private theorem strictCycle_sub_component (f g : M ⟶ N) (a : A.Obj) (i : ℤ)
    (x : (M.complex a).X i) :
    GradedHom.app (strictCycle f - strictCycle g).val a i i (add_zero i) x =
      (f.app a).f i x - (g.app a).f i x := by
  change (Cochain.ofHom (f.app a) - Cochain.ofHom (g.app a)).v i i (add_zero i) x = _
  simp only [Cochain.sub_v, Cochain.ofHom_v, ModuleCat.hom_sub, LinearMap.sub_apply]

/-- Equality in the homotopy category is chain homotopy through right-linear maps. -/
theorem homotopyCriterion (f g : M ⟶ N) :
    homotopyClass f = homotopyClass g ↔ ∃ h : GradedHom M N (-1), HomotopyEquation f g h := by
  change classOf (strictCycle f) = classOf (strictCycle g) ↔ _
  rw [Submodule.Quotient.eq]
  change _ ∈ boundariesZero (homComplex M N) ↔ _
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, fun a i x => ?_⟩
    have e := congrArg (fun z : cyclesZero (homComplex M N) =>
      GradedHom.app z.val a i i (add_zero i) x) hh
    change GradedHom.app ((homComplex M N).d (-1) 0 h) a i i (add_zero i) x =
      GradedHom.app (strictCycle f - strictCycle g).val a i i (add_zero i) x at e
    rw [boundary_component] at e
    simpa only [strictCycle_sub_component] using e.symm
  · rintro ⟨h, hh⟩
    refine ⟨h, Subtype.ext (GradedHom.ext ?_)⟩
    intro a i q e
    rw [add_zero] at e
    subst e
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change GradedHom.app ((homComplex M N).d (-1) 0 h) a i i (add_zero i) x =
      GradedHom.app (strictCycle f - strictCycle g).val a i i (add_zero i) x
    rw [boundary_component]
    simpa only [strictCycle_sub_component] using (hh a i x).symm

/-- The differential is the signed commutator with the module differentials. -/
theorem differentialFormula (r : ℤ) (f : GradedHom M N r)
    (a : A.Obj) (i q : ℤ) (e : i+(r+1) = q) (x : (M.complex a).X i) :
    GradedHom.app ((homComplex M N).d r (r+1) f) a i q e x =
      (N.complex a).d (i+r) q (f.app a i (i+r) rfl x) -
        r.negOnePow • f.app a (i+1) q (by omega) ((M.complex a).d i (i+1) x) := by
  change (δ r (r+1) (f.val a)).v i q e x = _
  rw [δ_v r (r+1) rfl _ i q e (i+r) (i+1) (by omega) rfl]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
    Int.negOnePow_succ, Units.neg_smul, sub_eq_add_neg]
  rfl

/-- Graded composition is the ordinary composition of homogeneous components. -/
theorem compositionFormula (s r t : ℤ) (e : s+r = t)
    (g : GradedHom N P s) (f : GradedHom M N r)
    (a : A.Obj) (i j n : ℤ) (hij : i+r = j) (hjn : j+s = n)
    (x : (M.complex a).X i) :
    GradedHom.app ((dgCategory A).comp s r t e g f) a i n (by omega) x =
      g.app a j n hjn (f.app a i j hij x) := by
  change ((f.val a).comp (g.val a) ((add_comm r s).trans e)).v i n (by omega) x = _
  rw [Cochain.comp_v (f.val a) (g.val a) ((add_comm r s).trans e) i j n hij hjn]
  rfl

/-- The category structure on `K(A)` is the degree-zero cohomology structure. -/
theorem homotopyCategoryStructure :
    Specs.DerivedFormalization.DG.HomComplex.HomotopyCategoryStructure.{u,v,w} := by
  intro k _ A
  exact ⟨instCategoryK A, rfl⟩

end RightDGModule

end DerivedFormalization
