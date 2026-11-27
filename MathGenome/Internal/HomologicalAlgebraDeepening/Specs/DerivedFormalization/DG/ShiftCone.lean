import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomologySequence

open CategoryTheory HomologicalComplex CochainComplex.HomComplex

universe u v w

namespace Specs.DerivedFormalization.DG.ShiftCone

open _root_.DerivedFormalization

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {M N P : RightDGModuleModel A}

private theorem act_assoc_at (M : RightDGModuleModel A) {a b c : A.Obj}
    (i j l p q n : ℤ) (hp : i+j = p) (hq : j+l = q) (hn : p+l = n)
    (x : (M.complex c).X i) (f : (A.hom b c).X j) (g : (A.hom a b).X l) :
    M.act p l n hn (M.act i j p hp x f) g =
      M.act i q n (by omega) x (A.comp j l q hq f g) := by
  subst p q n
  exact M.act_assoc i j l x f g

private theorem shift_leibniz (M : RightDGModuleModel A) (s : ℤ) {a b : A.Obj}
    (i j n p q : ℤ) (h : i+j = n) (hp : i+s+1 = p) (hq : n+s+1 = q)
    (x : (M.complex b).X (i+s)) (f : (A.hom a b).X j) :
    (s.negOnePow • (M.complex a).d (n+s) q) (M.act (i+s) j (n+s) (by omega) x f) =
      M.act p j q (by omega) ((s.negOnePow • (M.complex b).d (i+s) p) x) f +
        i.negOnePow • M.act (i+s) (j+1) q (by omega) x ((A.hom a b).d j (j+1) f) := by
  subst p q
  have hs : s.negOnePow * (i+s).negOnePow = i.negOnePow := by
    rw [Int.negOnePow_add, mul_left_comm, Int.units_mul_self, mul_one]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [M.leibniz, smul_add, smul_smul, hs]
  simp only [Units.smul_def, map_zsmul, LinearMap.smul_apply]

/-- Cohomological shift, with the original right action on the reindexed degrees. -/
@[reducible] def shift (M : RightDGModuleModel A) (s : ℤ) : RightDGModuleModel A where
  complex a := (CochainComplex.shiftFunctor (ModuleCat k) s).obj (M.complex a)
  act i j n h := M.act (i+s) j (n+s) (by omega)
  act_id a i x := M.act_id a (i+s) x
  act_assoc {a b c} i j l x f g :=
    act_assoc_at M (i+s) j l (i+j+s) (j+l) (i+j+l+s) (by omega) rfl (by omega) x f g
  leibniz i j n h x f :=
    shift_leibniz M s i j n (i+1+s) (n+1+s) h (by omega) (by omega) x f

open HomComplex (gradedHom homComplex dgModuleCategory component)

/-- Reindex a homogeneous family and multiply by the dg shift sign. -/
@[reducible] def shiftGraded (s : ℤ) (r : ℤ) :
    gradedHom M N r →ₗ[k] gradedHom (shift M s) (shift N s) r where
  toFun f := ⟨fun a => Cochain.mk fun i q h =>
    (s*r).negOnePow • component f a (i+s) (q+s) (by omega), by
      intro a b i j n ir nr h hi hn x z
      change ((s*r).negOnePow • component f a (n+s) (nr+s) _) (M.act (i+s) j (n+s) _ x z) =
        N.act (ir+s) j (nr+s) _ (((s*r).negOnePow • component f b (i+s) (ir+s) _) x) z
      simp only [ModuleCat.hom_smul, LinearMap.smul_apply, Units.smul_def, map_zsmul,
        LinearMap.smul_apply]
      rw [f.property (a := a) (b := b) (i+s) j (n+s) (ir+s) (nr+s)
        (by omega) (by omega) (by omega) x z]⟩
  map_add' f g := by
    apply Subtype.ext
    funext a
    apply Cochain.ext
    intro i q h
    simp only [Submodule.coe_add, Pi.add_apply, Cochain.add_v, Cochain.mk_v]
    change (s*r).negOnePow • ((f.val a + g.val a).v (i+s) (q+s) _) =
      (s*r).negOnePow • (f.val a).v (i+s) (q+s) _ + (s*r).negOnePow • (g.val a).v (i+s) (q+s) _
    rw [Cochain.add_v, smul_add]
  map_smul' c f := by
    apply Subtype.ext
    funext a
    apply Cochain.ext
    intro i q h
    simp only [RingHom.id_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, Cochain.smul_v,
      Cochain.mk_v]
    change (s*r).negOnePow • (c • (f.val a).v (i+s) (q+s) _) =
      c • ((s*r).negOnePow • (f.val a).v (i+s) (q+s) _)
    simp only [Units.smul_def, smul_comm ((s*r).negOnePow : ℤ) c]

@[simp] theorem shiftGraded_component (s r : ℤ) (f : gradedHom M N r)
    (a : A.Obj) (i q : ℤ) (h : i+r = q) :
    component (shiftGraded s r f) a i q h =
      (s*r).negOnePow • component f a (i+s) (q+s) (by omega) := rfl

private theorem shiftGraded_comm (s r : ℤ) (f : gradedHom M N r) :
    shiftGraded s (r+1) ((homComplex M N).d r (r+1) f) =
      (homComplex (shift M s) (shift N s)).d r (r+1) (shiftGraded s r f) := by
  apply Subtype.ext
  funext a
  apply Cochain.ext
  intro i q h
  change (s*(r+1)).negOnePow • (δ r (r+1) (f.val a)).v (i+s) (q+s) (by omega) =
    (δ r (r+1) ((shiftGraded s r f).val a)).v i q h
  rw [δ_v r (r+1) rfl _ (i+s) (q+s) _ (i+r+s) (i+1+s) (by omega) (by omega),
    δ_v r (r+1) rfl _ i q h (i+r) (i+1) (by omega) rfl]
  change (s*(r+1)).negOnePow •
      ((f.val a).v (i+s) (i+r+s) _ ≫ (N.complex a).d (i+r+s) (q+s) +
        (r+1).negOnePow • (M.complex a).d (i+s) (i+1+s) ≫ (f.val a).v (i+1+s) (q+s) _) =
    ((s*r).negOnePow • (f.val a).v (i+s) (i+r+s) _) ≫
        (s.negOnePow • (N.complex a).d (i+r+s) (q+s)) +
      (r+1).negOnePow • (s.negOnePow • (M.complex a).d (i+s) (i+1+s)) ≫
        ((s*r).negOnePow • (f.val a).v (i+1+s) (q+s) _)
  simp only [mul_add, mul_one, Int.negOnePow_add, smul_add, Linear.units_smul_comp,
    Linear.comp_units_smul, smul_smul, mul_assoc]
  congr 1
  · rw [mul_comm s.negOnePow]
  · congr 1
    ac_rfl

/-- The shift is a dg endofunctor of right dg modules. -/
@[reducible] def shiftDGFunctor (A : DGCategoryModel.{u,v,w} k) (s : ℤ) :
    DGFunctorModel (dgModuleCategory A) (dgModuleCategory A) where
  obj M := shift M s
  map M N := { f := fun r => ModuleCat.ofHom (shiftGraded (M := M) (N := N) s r)
               comm' := fun r t h => by
                 obtain rfl : r+1 = t := h
                 apply ModuleCat.hom_ext
                 apply LinearMap.ext
                 intro f
                 exact (shiftGraded_comm s r f).symm }
  map_id M := by
    apply Subtype.ext
    funext a
    apply Cochain.ext
    intro i q h
    obtain rfl : i = q := by omega
    change (s*0).negOnePow • (Cochain.ofHom (𝟙 (M.complex a))).v (i+s) (i+s) _ =
      (Cochain.ofHom (𝟙 ((shift M s).complex a))).v i i _
    simp only [mul_zero, Int.negOnePow_zero, one_smul, Cochain.ofHom_v,
      HomologicalComplex.id_f]
    rfl
  map_comp {M N P} r t n h g f := by
    apply Subtype.ext
    funext a
    apply Cochain.ext
    intro i j e
    change (s*n).negOnePow • ((f.val a).comp (g.val a) (by omega)).v (i+s) (j+s) _ =
      (((shiftGraded s t f).val a).comp ((shiftGraded s r g).val a) (by omega)).v i j e
    rw [Cochain.comp_v _ _ _ (i+s) (i+t+s) (j+s) (by omega) (by omega),
      Cochain.comp_v _ _ _ i (i+t) j rfl (by omega)]
    change (s*n).negOnePow • ((f.val a).v (i+s) (i+t+s) _ ≫ (g.val a).v (i+t+s) (j+s) _) =
      ((s*t).negOnePow • (f.val a).v (i+s) (i+t+s) _) ≫
        ((s*r).negOnePow • (g.val a).v (i+t+s) (j+s) _)
    have hs : (s*n).negOnePow = (s*t).negOnePow * (s*r).negOnePow := by
      rw [← h, mul_add, Int.negOnePow_add, mul_comm]
    rw [hs, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]

/-- A closed degree-zero map shifts by reindexing its components. -/
@[reducible] def shiftMap (s : ℤ) (f : M ⟶ N) : shift M s ⟶ shift N s where
  app a := (CochainComplex.shiftFunctor (ModuleCat k) s).map (f.app a)
  comm_act := by
    intro a b i j n h x z
    exact f.comm_act (i+s) j (n+s) (by omega) x z

/-- In degree `i` the cone is the direct sum in the order `(y,x)`. -/
abbrev coneTerm (M N : RightDGModuleModel A) (a : A.Obj) (i : ℤ) :=
  ModuleCat.of k ((N.complex a).X i × (M.complex a).X (i+1))

/-- The matrix differential in consecutive degrees. -/
def coneStep (f : M ⟶ N) (a : A.Obj) (i : ℤ) :
    coneTerm M N a i ⟶ coneTerm M N a (i+1) :=
  ModuleCat.ofHom
    ((((N.complex a).d i (i+1)).hom.comp (LinearMap.fst _ _ _) +
      ((f.app a).f (i+1)).hom.comp (LinearMap.snd _ _ _)).prod
        (-(((M.complex a).d (i+1) (i+1+1)).hom.comp (LinearMap.snd _ _ _))))

/-- The differential vanishes off consecutive degrees. -/
def coneDiff (f : M ⟶ N) (a : A.Obj) (i j : ℤ) :
    coneTerm M N a i ⟶ coneTerm M N a j :=
  if h : i+1 = j then coneStep f a i ≫ eqToHom (congrArg (coneTerm M N a) h)
  else 0

@[simp] theorem coneDiff_succ (f : M ⟶ N) (a : A.Obj) (i : ℤ) (p : coneTerm M N a i) :
    coneDiff f a i (i+1) p =
      ((N.complex a).d i (i+1) p.1 + (f.app a).f (i+1) p.2,
        -(M.complex a).d (i+1) (i+1+1) p.2) := by
  rw [coneDiff, dite_eq_left rfl, eqToHom_refl, Category.comp_id]
  rfl

private theorem d_d_apply (C : ModuleCochain.{u,v} k) (i j l : ℤ) (x : C.X i) :
    C.d j l (C.d i j x) = 0 := by
  rw [← ModuleCat.comp_apply, d_comp_d]
  rfl

/-- The objectwise cone complex. -/
@[reducible] def coneComplex (f : M ⟶ N) (a : A.Obj) : ModuleCochain.{u,v} k where
  X := coneTerm M N a
  d := coneDiff f a
  shape i j h := dite_eq_right (show i+1 ≠ j from h)
  d_comp_d' i j l hij hjl := by
    obtain rfl : i+1 = j := hij
    obtain rfl : i+1+1 = l := hjl
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    change coneDiff f a (i+1) (i+1+1) (coneDiff f a i (i+1) p) = 0
    rw [coneDiff_succ, coneDiff_succ]
    have hf := CategoryTheory.congr_fun ((f.app a).comm (i+1) (i+1+1)) p.2
    simp only [ModuleCat.comp_apply] at hf
    apply Prod.ext
    · change (N.complex a).d (i+1) (i+1+1) (_ + _) + (f.app a).f (i+1+1) (-_) = 0
      rw [map_add, d_d_apply, zero_add, map_neg, ← hf, add_neg_cancel]
    · change -((M.complex a).d (i+1+1) (i+1+1+1) (-_)) = 0
      rw [map_neg, neg_neg, d_d_apply]

/-- The usual componentwise right action on the cone. -/
@[reducible] def cone (f : M ⟶ N) : RightDGModuleModel A where
  complex := coneComplex f
  act {a b} i j n h :=
    { toFun := fun p => (N.act i j n h p.1).prod (M.act (i+1) j (n+1) (by omega) p.2)
      map_add' := by
        intro p q
        ext z <;> simp [LinearMap.add_apply]
      map_smul' := by
        intro c p
        ext z <;> simp [LinearMap.smul_apply] }
  act_id a i p := Prod.ext (N.act_id a i p.1) (M.act_id a (i+1) p.2)
  act_assoc {a b c} i j l p f g := Prod.ext (N.act_assoc i j l p.1 f g)
    (act_assoc_at M (i+1) j l (i+j+1) (j+l) (i+j+l+1) (by omega) rfl (by omega) p.2 f g)
  leibniz {a b} i j n h p z := by
    change coneDiff f a n (n+1) (N.act i j n h p.1 z, M.act (i+1) j (n+1) _ p.2 z) = _
    rw [coneDiff_succ]
    apply Prod.ext
    · change (N.complex a).d n (n+1) (N.act i j n _ p.1 z) +
        (f.app a).f (n+1) (M.act (i+1) j (n+1) _ p.2 z) =
        N.act (i+1) j (n+1) _ ((coneDiff f b i (i+1) p).1) z +
          i.negOnePow • N.act i (j+1) (n+1) _ p.1 ((A.hom a b).d j (j+1) z)
      rw [coneDiff_succ, N.leibniz, f.comm_act]
      simp only [map_add, LinearMap.add_apply]
      abel
    · change -(M.complex a).d (n+1) (n+1+1) (M.act (i+1) j (n+1) _ p.2 z) =
        M.act (i+1+1) j (n+1+1) _ (coneDiff f b i (i+1) p).2 z +
          i.negOnePow • M.act (i+1) (j+1) (n+1+1) _ p.2 ((A.hom a b).d j (j+1) z)
      rw [coneDiff_succ, M.leibniz]
      simp only [map_neg, LinearMap.neg_apply, neg_add, Int.negOnePow_succ, Units.neg_smul,
        neg_neg]

/-- The target inclusion in the cone. -/
@[reducible] def coneInclusion (f : M ⟶ N) : N ⟶ cone f where
  app a := CochainComplex.ofHom (fun i => ModuleCat.ofHom (LinearMap.inl _ _ _)) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change coneDiff f a i (i+1) (y, 0) = ((N.complex a).d i (i+1) y, 0)
    rw [coneDiff_succ]
    simp)
  comm_act := by
    intro a b i j n h y z
    change (N.act i j n h y z, 0) = (_, M.act (i+1) j (n+1) _ 0 z)
    simp

/-- The positive quotient projection of the cone onto the shifted source. -/
@[reducible] def coneProjection (f : M ⟶ N) : cone f ⟶ shift M 1 where
  app a := CochainComplex.ofHom (fun i => ModuleCat.ofHom (LinearMap.snd _ _ _)) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    change (1 : ℤ).negOnePow • (M.complex a).d (i+1) (i+1+1) p.2 =
      (coneDiff f a i (i+1) p).2
    rw [coneDiff_succ, Int.negOnePow_one, Units.neg_smul, one_smul])
  comm_act := by intros; rfl

/-- The cone sequence as a short complex of strict right dg module maps. -/
@[reducible] def coneSequence (f : M ⟶ N) : ShortComplex (RightDGModuleModel A) :=
  ShortComplex.mk (coneInclusion f) (coneProjection f) (by
    apply RightDGModuleModel.hom_ext
    intro a
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

abbrev objectConeSequence (f : M ⟶ N) (a : A.Obj) :=
  (coneSequence f).map (RightDGModuleModel.eval a)

/-- The graded splitting uses the second inclusion and first projection, both right-linear. -/
def GradedSplit : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : M ⟶ N),
    ∃ (s : gradedHom (shift M 1) (cone f) 0) (r : gradedHom (cone f) N 0),
      ∀ (a : A.Obj) (i : ℤ) (x : (M.complex a).X (i+1)) (p : coneTerm M N a i),
        component s a i i (add_zero i) x = (0, x) ∧
        component r a i i (add_zero i) p = p.1

def ObjectwiseShortExact : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : M ⟶ N) (a : A.Obj),
    (objectConeSequence f a).ShortExact

/-- The canonical cohomology reindexing for the signed shift. -/
noncomputable abbrev shiftHomologyIso (M : RightDGModuleModel A) (s : ℤ)
    (a : A.Obj) (i : ℤ) : ((shift M s).complex a).homology i ≅ (M.complex a).homology (i+s) :=
  (CochainComplex.ShiftSequence.shiftIso (ModuleCat k) s i (i+s) (add_comm s i)).app (M.complex a)

def ConnectingMap : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : M ⟶ N) (a : A.Obj)
    (hS : (objectConeSequence f a).ShortExact) (i : ℤ),
    hS.δ i (i+1) rfl =
      (shiftHomologyIso M 1 a i).hom ≫ homologyMap (f.app a) (i+1)

def ConeAcyclicCriterion : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : M ⟶ N),
    Module.quasiIsomorphism f ↔ Module.acyclic (cone f)

set_option linter.checkUnivs false

def ShiftType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k},
    RightDGModuleModel A → ℤ → RightDGModuleModel A

def ShiftGradedType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (s r : ℤ),
    gradedHom M N r →ₗ[k] gradedHom (shift M s) (shift N s) r

def ShiftMapType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (s : ℤ), (M ⟶ N) → (shift M s ⟶ shift N s)

def ShiftDGFunctorType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k), ℤ →
    DGFunctorModel (dgModuleCategory A) (dgModuleCategory A)

def ConeType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A}, (M ⟶ N) → RightDGModuleModel A

def ConeInclusionType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : M ⟶ N), N ⟶ cone f

def ConeProjectionType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : M ⟶ N), cone f ⟶ shift M 1

def ConeSequenceType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A}, (M ⟶ N) → ShortComplex (RightDGModuleModel A)

def ShiftHomologyIsoType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (M : RightDGModuleModel A) (s : ℤ) (a : A.Obj) (i : ℤ),
    ((shift M s).complex a).homology i ≅ (M.complex a).homology (i+s)

end Specs.DerivedFormalization.DG.ShiftCone
