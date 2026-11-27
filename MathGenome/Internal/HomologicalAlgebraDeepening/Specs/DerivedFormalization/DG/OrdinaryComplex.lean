import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.AmbientDerived
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CellReindex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainRingTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.KProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.SemiFree
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
open scoped DirectSum

universe u v r j t

set_option linter.checkUnivs false

namespace Specs.DerivedFormalization.DG.OrdinaryComplex

open _root_.DerivedFormalization

noncomputable section

variable (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]

/-- A degree of the stalk algebra, realized inside the ordinary algebra. -/
def stalkTerm (i : ℤ) : Submodule k R where
  carrier := {x | i ≠ 0 → x = 0}
  zero_mem' := fun _ => rfl
  add_mem' hx hy h := by rw [hx h, hy h, add_zero]
  smul_mem' c x hx h := by rw [hx h, smul_zero]

/-- The copy of an ordinary algebra element in degree zero. -/
def scalar (a : R) : stalkTerm k R 0 :=
  ⟨a, fun h => (h rfl).elim⟩

private theorem stalkTerm_zero {i : ℤ} (hi : i ≠ 0) (a : stalkTerm k R i) : a = 0 :=
  Subtype.ext (a.property hi)

@[reducible] def stalkComplex : ModuleCochain.{u,v} k where
  X i := ModuleCat.of k (stalkTerm k R i)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

private def stalkMul (i j n : ℤ) (h : i + j = n) :
    stalkTerm k R i →ₗ[k] stalkTerm k R j →ₗ[k] stalkTerm k R n where
  toFun a :=
    { toFun := fun b => ⟨a.val * b.val, by
        intro hn
        by_cases hi : i = 0
        · have hj : j ≠ 0 := by omega
          rw [b.property hj, mul_zero]
        · rw [a.property hi, zero_mul]⟩
      map_add' b c := Subtype.ext (mul_add a.val b.val c.val)
      map_smul' c b := Subtype.ext (by simp [Algebra.smul_def, mul_left_comm]) }
  map_add' a b := LinearMap.ext fun c => Subtype.ext (add_mul a.val b.val c.val)
  map_smul' c a := LinearMap.ext fun b => Subtype.ext (smul_mul_assoc c a.val b.val)

@[reducible] def degreeZeroAlgebra : DGAlgebraModel.{u,v} k where
  hom _ _ := stalkComplex k R
  comp := stalkMul k R
  id _ := scalar k R 1
  d_id _ := rfl
  id_comp _ a := Subtype.ext (one_mul a.val)
  comp_id _ a := Subtype.ext (mul_one a.val)
  assoc _ _ _ a b c := Subtype.ext (mul_assoc a.val b.val c.val)
  leibniz i j n h a b := by
    change (0 : stalkTerm k R (n + 1)) =
      stalkMul k R (i + 1) j (n + 1) _ 0 b +
        i.negOnePow • stalkMul k R i (j + 1) (n + 1) _ a 0
    simp

abbrev degreeZeroCategory := Basic.toDGCategory (degreeZeroAlgebra k R)

abbrev DGMod := RightDGModuleModel (degreeZeroCategory k R)

abbrev restrictScalars := ModuleCat.restrictScalars.{v} (algebraMap k R)

abbrev restrictComplex := (restrictScalars k R).mapHomologicalComplex (ComplexShape.up ℤ)

variable {k R}

private def scalarAction (M : ModuleCat.{v} R) :
    (restrictScalars k R).obj M →ₗ[k] stalkTerm k R 0 →ₗ[k] (restrictScalars k R).obj M where
  toFun x :=
    { toFun := fun a => a.val • (show M from x)
      map_add' a b := add_smul a.val b.val (show M from x)
      map_smul' c a := by
        change (c • a.val) • (show M from x) = (algebraMap k R c) • (show M from a.val • (show M from x))
        rw [Algebra.smul_def, mul_smul] }
  map_add' x y := LinearMap.ext fun a => smul_add a.val (show M from x) (show M from y)
  map_smul' c x := LinearMap.ext fun a => by
    change a.val • ((algebraMap k R c) • (show M from x)) =
      (algebraMap k R c) • (a.val • (show M from x))
    exact smul_comm _ _ _

private def act (X : ModuleCochain.{v,v} R) (i j n : ℤ) (h : i+j=n) :
    ((restrictComplex k R).obj X).X i →ₗ[k] stalkTerm k R j →ₗ[k]
      ((restrictComplex k R).obj X).X n := by
  by_cases hj : j = 0
  · subst j
    rw [add_zero] at h
    subst n
    exact scalarAction (X.X i)
  · exact 0

@[simp] private theorem act_zero_degree (X : ModuleCochain.{v,v} R) (i : ℤ)
    (x : ((restrictComplex k R).obj X).X i) (a : stalkTerm k R 0) :
    act X i 0 i (add_zero i) x a = a.val • (show X.X i from x) := by
  simp only [act, ↓reduceDIte]
  rfl

private theorem act_assoc_at (X : ModuleCochain.{v,v} R) (i j l p q n : ℤ)
    (hp : i+j=p) (hq : j+l=q) (hn : p+l=n)
    (x : ((restrictComplex k R).obj X).X i) (a : stalkTerm k R j) (b : stalkTerm k R l) :
    act X p l n hn (act X i j p hp x a) b =
      act X i q n (by omega) x (stalkMul k R j l q hq a b) := by
  by_cases hj : j = 0
  · by_cases hl : l = 0
    · subst j l
      have hp' : i = p := by omega
      have hq' : 0 = q := by omega
      have hn' : p = n := by omega
      cases hq'
      cases hn'
      cases hp'
      rw [act_zero_degree, act_zero_degree, act_zero_degree]
      change b.val • (a.val • (show X.X i from x)) = (a.val * b.val) • (show X.X i from x)
      rw [← mul_smul, mul_comm]
    · rw [stalkTerm_zero k R hl b]
      simp
  · rw [stalkTerm_zero k R hj a]
    simp

/-- An ordinary cochain complex with its canonical right action. -/
@[reducible] def fromComplex (X : ModuleCochain.{v,v} R) : DGMod k R where
  complex _ := (restrictComplex k R).obj X
  act := act X
  act_id _ i x := by
    change act X i 0 i _ x (scalar k R 1) = x
    rw [act_zero_degree]
    exact one_smul R (show X.X i from x)
  act_assoc i j l x a b :=
    act_assoc_at X i j l (i+j) (j+l) (i+j+l) rfl rfl rfl x a b
  leibniz i j n h x a := by
    change ((restrictComplex k R).obj X).d n (n+1) (act X i j n h x a) =
      act X (i+1) j (n+1) _ (((restrictComplex k R).obj X).d i (i+1) x) a +
        i.negOnePow • act X i (j+1) (n+1) _ x (0 : stalkTerm k R (j+1))
    simp only [map_zero, smul_zero, add_zero]
    by_cases hj : j = 0
    · subst j
      simp only [add_zero] at h
      cases h
      rw [act_zero_degree, act_zero_degree]
      change X.d i (i+1) (a.val • (show X.X i from x)) =
        a.val • X.d i (i+1) (show X.X i from x)
      exact (X.d i (i+1)).hom.map_smul a.val (show X.X i from x)
    · rw [stalkTerm_zero k R hj a]
      simp [map_zero]

/-- Restriction on the terms of a chain map retains its underlying functions. -/
@[reducible] def fromComplexFunctor : ModuleCochain.{v,v} R ⥤ DGMod k R where
  obj := fromComplex
  map {X Y} f :=
    { app := fun _ => (restrictComplex k R).map f
      comm_act := by
        intro a b i j n h x z
        change ((restrictComplex k R).map f).f n (act X i j n h x z) =
          act Y i j n h (((restrictComplex k R).map f).f i x) z
        by_cases hj : j = 0
        · subst j
          simp only [add_zero] at h
          cases h
          rw [act_zero_degree, act_zero_degree]
          exact (f.f i).hom.map_smul z.val (show X.X i from x)
        · rw [stalkTerm_zero k R hj z]
          simp [map_zero] }
  map_id X := RightDGModuleModel.hom_ext fun _ => (restrictComplex k R).map_id X
  map_comp f g := RightDGModuleModel.hom_ext fun _ => (restrictComplex k R).map_comp f g

variable (k R)

def DegreeZeroAlgebraType :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R], DGAlgebraModel.{u,v} k

def FromComplexType :=
  ∀ {k : Type u} [CommRing k] {R : Type v} [CommRing R] [Algebra k R],
    ModuleCochain.{v,v} R → DGMod k R

def FromComplexFunctorType :=
  ∀ {k : Type u} [CommRing k] {R : Type v} [CommRing R] [Algebra k R],
    ModuleCochain.{v,v} R ⥤ DGMod k R

/-- Multiplication by the image of a base scalar recovers the given action of the base ring. -/
def RestrictionOfScalars : Prop :=
  ∀ {k : Type u} [CommRing k] {R : Type v} [CommRing R] [Algebra k R]
    (M : DGMod k R) (i : ℤ) (c : k) (x : (M.complex ()).X i),
    M.act (a := ()) (b := ()) i 0 i (add_zero i) x (scalar k R (algebraMap k R c)) = c • x

/-- The canonical functor is an equivalence, for an arbitrary commutative base ring. -/
def StrictEquivalence : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R],
    (fromComplexFunctor (k := k) (R := R)).IsEquivalence

/-- The underlying Hom comparison is by restriction on each homogeneous component.
The cochain isomorphisms preserve identities and graded composition. -/
def HomComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R],
    ∃ E : ∀ X Y : ModuleCochain.{v,v} R,
        (restrictComplex k R).obj (CochainModels.internalHomValue X Y) ≅
          HomComplex.homComplex (fromComplex (k := k) X) (fromComplex Y),
      (∀ (X Y : ModuleCochain.{v,v} R) (r i t : ℤ) (h : i+r=t)
        (f : Cochain X Y r) (x : X.X i),
        HomComplex.component ((E X Y).hom.f r f) () i t h x = (f.v i t h) x) ∧
      (∀ (X Y : ModuleCochain.{v,v} R) (f : X ⟶ Y),
        (E X Y).hom.f 0 (Cochain.ofHom f) =
          HomComplex.ofStrict ((fromComplexFunctor (k := k)).map f)) ∧
      (∀ (X Y Z : ModuleCochain.{v,v} R) (r s t : ℤ) (h : s+r=t)
        (f : Cochain X Y r) (g : Cochain Y Z s),
        (E X Z).hom.f t (f.comp g ((add_comm r s).trans h)) =
          HomComplex.compose _ _ _ s r t h ((E Y Z).hom.f s g) ((E X Y).hom.f r f))

/-- The null-homotopy equation is compared on the actual strict maps. -/
def StrictHomotopyComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    {X Y : ModuleCochain.{v,v} R} (f g : X ⟶ Y),
    let F := fromComplexFunctor (k := k) (R := R)
    Nonempty (Homotopy f g) ↔
      ∃ h : HomComplex.gradedHom (F.obj X) (F.obj Y) (-1),
        HomComplex.HomotopyEquation (F.map f) (F.map g) h

def AcyclicityComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    (X : ModuleCochain.{v,v} R),
    X.Acyclic ↔ Module.acyclic (fromComplex (k := k) X)

def QuasiIsoComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y),
    QuasiIso f ↔ Module.quasiIsomorphism ((fromComplexFunctor (k := k)).map f)

/-- Restriction takes the actual ordinary cohomology maps to the objectwise
dg cohomology maps, in every degree. -/
def CohomologyComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R] (i : ℤ),
    Nonempty (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i ⋙
      restrictScalars k R ≅
      fromComplexFunctor (k := k) (R := R) ⋙ RightDGModuleModel.eval () ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{v} k) (ComplexShape.up ℤ) i)

def SurjectivityComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y),
    (∀ i, Function.Surjective (f.f i)) ↔
      Module.degreewiseSurjective ((fromComplexFunctor (k := k)).map f)

def KProjectivityComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    (X : ModuleCochain.{v,v} R),
    CochainModels.isKProjectiveValue X ↔ KProjective.isKProjective (fromComplex (k := k) X)

/-- The canonical signed shift is transported by termwise identity maps. -/
def ShiftComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R] (s : ℤ),
    let F := fromComplexFunctor (k := k) (R := R)
    ∃ e : ∀ X : ModuleCochain.{v,v} R,
        F.obj ((CochainComplex.shiftFunctor (ModuleCat R) s).obj X) ≅
          ShiftCone.shift (F.obj X) s,
      (∀ (X : ModuleCochain.{v,v} R) (i : ℤ) (x : X.X (i+s)),
        ((e X).hom.app ()).f i x = x) ∧
      (∀ (X Y : ModuleCochain.{v,v} R) (f : X ⟶ Y),
        F.map ((CochainComplex.shiftFunctor (ModuleCat R) s).map f) ≫ (e Y).hom =
          (e X).hom ≫ ShiftCone.shiftMap s (F.map f))

/-- The comparison respects the cone inclusion and the projection onto the shifted source. -/
def ConeComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y),
    let F := fromComplexFunctor (k := k) (R := R)
    ∃ e : F.obj (CochainComplex.mappingCone f) ≅ ShiftCone.cone (F.map f),
      F.map (CochainComplex.mappingCone.inr f) ≫ e.hom = ShiftCone.coneInclusion (F.map f) ∧
      ∀ (i : ℤ) (x : (CochainComplex.mappingCone f).X i),
        ((ShiftCone.coneProjection (F.map f)).app ()).f i ((e.hom.app ()).f i x) =
          (CochainComplex.mappingCone.fst f).1.v i (i+1) rfl x

/-- The complex with one generator in degree `n` and zero differential. -/
abbrev ordinaryCell {R : Type v} [CommRing R] (n : ℤ) : ModuleCochain.{v,v} R :=
  (CochainComplex.shiftFunctor (ModuleCat R) (-n)).obj
    ((Cochains.stalkValue R).obj (ModuleCat.of R R))

def FreeCellComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R] (n : ℤ),
    Nonempty (fromComplex (k := k) (ordinaryCell (R := R) n) ≅
      (SemiFree.cell (A := degreeZeroCategory k R) () n))

/-- A graded-split filtration, with its chosen cell degrees and quotient maps. -/
structure CellPresentation {R : Type v} [CommRing R] (X : ModuleCochain.{v,v} R)
    (I : ℕ → Type v) (degree : ∀ j, I j → ℤ) where
  stage : ℕ → ModuleCochain.{v,v} R
  bottom (i : ℤ) (x : (stage 0).X i) : x = 0
  incl (j : ℕ) : stage j ⟶ stage (j+1)
  into (j : ℕ) : stage j ⟶ X
  compatible (j : ℕ) : incl j ≫ into (j+1) = into j
  injective (j : ℕ) (i : ℤ) : Function.Injective ((into j).f i)
  exhaustive (i : ℤ) (x : X.X i) : ∃ j y, (into j).f i y = x
  quotient (j : ℕ) : stage (j+1) ⟶ ∐ (fun s : I j => ordinaryCell (R := R) (degree j s))
  zero (j : ℕ) : incl j ≫ quotient j = 0
  shortExact (j : ℕ) : (ShortComplex.mk (incl j) (quotient j) (zero j)).ShortExact
  split (j : ℕ) (i : ℤ) :
    ∃ r : (stage (j+1)).X i ⟶ (stage j).X i, (incl j).f i ≫ r = 𝟙 _

/-- The ordinary generator is the image of one under the degree identification
for the shifted free stalk. -/
def ordinaryGenerator {R : Type v} [CommRing R] (n : ℤ) :
    (ordinaryCell (R := R) n).X n :=
  (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (ModuleCat.of R R)
    (n + -n) (add_neg_cancel n)).inv (1 : R)

/-- The free-cell comparison takes one to the named dg generator. -/
def FreeCellGeneratorComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R] (n : ℤ),
    ∃ e : fromComplex (k := k) (ordinaryCell (R := R) n) ≅
        SemiFree.cell (A := degreeZeroCategory k R) () n,
      (e.hom.app ()).f n (ordinaryGenerator n) =
        SemiFree.generator (A := degreeZeroCategory k R) () n

variable {k R} in
/-- Identifies the chosen ordinary stage maps with the actual attachment and its quotient. -/
structure CellPresentationMatch {X : ModuleCochain.{v,v} R}
    {I : ℕ → Type v} {d : ∀ l, I l → ℤ} (C : CellPresentation X I d)
    (P : SemiFree.Presentation (fromComplex (k := k) X)) where
  index (l : ℕ) : I l ≃ P.index l
  degree (l : ℕ) (s : I l) : (P.family l).degree (index l s) = d l s
  stage (l : ℕ) : fromComplex (k := k) (C.stage l) ≅ P.stage l
  sum (l : ℕ) : fromComplex (k := k) (∐ fun s : I l => ordinaryCell (R := R) (d l s)) ≅
    SemiFree.cellSum (P.family l)
  cell (l : ℕ) (s : I l) : fromComplex (k := k) (ordinaryCell (R := R) (d l s)) ≅
    SemiFree.cells (P.family l) (index l s)
  sum_inclusion (l : ℕ) (s : I l) :
    fromComplexFunctor.map (Sigma.ι (fun s : I l => ordinaryCell (R := R) (d l s)) s) ≫
      (sum l).hom = (cell l s).hom ≫
        SemiFree.sumInclusion (SemiFree.cells (P.family l)) (index l s)
  cell_generator (l : ℕ) (s : I l) :
    HEq (((cell l s).hom.app ()).f (d l s) (ordinaryGenerator (d l s)))
      (SemiFree.generator ((P.family l).object (index l s)) ((P.family l).degree (index l s)))
  into (l : ℕ) : (stage l).hom ≫ P.into l = fromComplexFunctor.map (C.into l)
  inclusion (l : ℕ) : fromComplexFunctor.map (C.incl l) ≫ (stage (l+1)).hom =
    (stage l).hom ≫ SemiFree.inclusion (P.family l) ≫ (P.successor l).hom
  quotient (l : ℕ) : fromComplexFunctor.map (C.quotient l) ≫ (sum l).hom =
    (stage (l+1)).hom ≫ (P.successor l).inv ≫ SemiFree.projection (P.family l)
  attaching_cycle (l : ℕ) (s : I l) :
    let t := index l s
    let a := (P.family l).object t
    let n := (P.family l).degree t
    let dgGen := ((P.successor l).hom.app a).f n (SemiFree.attachedGenerator (P.family l) t)
    let y := ((stage (l+1)).inv.app a).f n dgGen
    let z := ((stage l).inv.app a).f (n+1) ((P.family l).boundary t)
    (C.stage (l+1)).d n (n+1) y = (C.incl l).f (n+1) z

/-- Both directions transport chosen filtrations, including their embeddings,
the quotient summands and the differentials of the lifted generators. -/
def CellPresentationTransport : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    (X : ModuleCochain.{v,v} R),
    (∀ {I : ℕ → Type v} {d : ∀ l, I l → ℤ} (C : CellPresentation X I d),
      ∃ P : SemiFree.Presentation (fromComplex (k := k) X), Nonempty (CellPresentationMatch C P)) ∧
    (∀ P : SemiFree.Presentation (fromComplex (k := k) X),
      ∃ (I : ℕ → Type v) (d : ∀ l, I l → ℤ) (C : CellPresentation X I d),
        Nonempty (CellPresentationMatch C P))

/-- The ordinary and dg presentations can use the same sets of cells in each degree. -/
def CellFiltrationComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    (X : ModuleCochain.{v,v} R) (I : ℕ → Type v) (degree : ∀ j, I j → ℤ),
    Nonempty (CellPresentation X I degree) ↔
      ∃ P : SemiFree.Presentation (fromComplex (k := k) X),
        ∃ e : ∀ j, I j ≃ P.index j, ∀ j s, (P.family j).degree (e j s) = degree j s

abbrev OrdinaryK (R : Type v) [CommRing R] := Cochains.homotopyValue.{v} R
abbrev DGK := HomComplex.homotopyCategory (degreeZeroCategory k R)

variable {k R}

/-- On strict representatives, a comparison of homotopy categories agrees
with the strict comparison and takes precisely the quasi-isomorphisms to
the class inverted on the dg side. -/
def IsHomotopyComparison (h : Derived.HomotopyCategoryLaws (degreeZeroCategory k R))
    (E : letI := Derived.homotopyCategory _ h; OrdinaryK R ≌ DGK k R) : Prop :=
  letI := Derived.homotopyCategory _ h
  ∃ e : ∀ X : ModuleCochain.{v,v} R,
      E.functor.obj ((Cochains.quotientValue R).obj X) ≅ (fromComplex X : DGK k R),
    (∀ {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y),
      E.functor.map ((Cochains.quotientValue R).map f) ≫ (e Y).hom =
        (e X).hom ≫ HomComplex.homotopyClass ((fromComplexFunctor (k := k)).map f)) ∧
    (∀ {X Y : OrdinaryK R} (f : X ⟶ Y),
      HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ) f ↔
        Derived.quasiIsomorphisms (degreeZeroCategory k R) (E.functor.map f))

def HomotopyCategoryComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    (h : Derived.HomotopyCategoryLaws (degreeZeroCategory k R)),
    letI := Derived.homotopyCategory _ h
    ∃ E : OrdinaryK R ≌ DGK k R, IsHomotopyComparison h E

attribute [local instance] HasDerivedCategory.standard

/-- The comparison of localized categories commutes with their localization functors. -/
def DerivedCategoryComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    (h : Derived.HomotopyCategoryLaws (degreeZeroCategory k R)),
    letI := Derived.homotopyCategory _ h
    ∃ (E : OrdinaryK R ≌ DGK k R)
      (E' : Cochains.derivedValue.{v} R ≌ (Derived.quasiIsomorphisms (degreeZeroCategory k R)).Localization),
      IsHomotopyComparison h E ∧
        Nonempty (Cochains.qhValue R ⋙ E'.functor ≅
          E.functor ⋙ Derived.quotient (degreeZeroCategory k R) h)

/-- An indexed presentation at any index level is normalized on its actual stages. -/
def IndexedFiltrationComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    (X : ModuleCochain.{v,v} R)
    (P : IndexedSemiFree.Presentation.{u,v,0,j} (fromComplex (k := k) X)),
    ∃ T : CellReindex.Reindexing.{u,v,0,j,v} P,
      ∃ B : CellReindex.SmallRealization T.toPresentation,
        ∃ (C : CellPresentation X B.toPresentation.index
          (fun l => (B.toPresentation.family l).degree)),
          Nonempty (CellPresentationMatch C B.toPresentation)

/-- The ordinary equivalence uses the common ambient dg localization.
Its quotient square and strict representatives use the very same homotopy equivalence. -/
def AmbientLocalizationComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
    (h : Derived.HomotopyCategoryLaws (degreeZeroCategory k R))
    (h' : Derived.HomotopyCategoryLaws (AmbientDerived.category.{u,v,0,v} (degreeZeroCategory k R))),
    let A := degreeZeroCategory k R
    let B := AmbientDerived.category.{u,v,0,v} A
    letI := Derived.homotopyCategory A h
    letI := Derived.homotopyCategory B h'
    letI : Category (AmbientDerived.derivedCategory.{u,v,0,v} A h') :=
      inferInstanceAs (Category (@MorphismProperty.Localization _ (Derived.homotopyCategory B h')
        (Derived.quasiIsomorphisms B)))
    let T := AmbientDerived.transportToAmbient.{u,v,0,v} A
    let F := fromComplexFunctor (k := k) (R := R) ⋙ T
    ∃ (H : OrdinaryK R ≌ AmbientDerived.homotopyCategory.{u,v,0,v} A)
      (D : Cochains.derivedValue.{v} R ≌ AmbientDerived.derivedCategory.{u,v,0,v} A h')
      (e : ∀ X : ModuleCochain.{v,v} R,
        H.functor.obj ((Cochains.quotientValue R).obj X) ≅
          (F.obj X : AmbientDerived.homotopyCategory.{u,v,0,v} A)),
      (∀ {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y),
        H.functor.map ((Cochains.quotientValue R).map f) ≫ (e Y).hom =
          (e X).hom ≫ HomComplex.homotopyClass (F.map f)) ∧
      Nonempty (Cochains.qhValue R ⋙ D.functor ≅ H.functor ⋙ AmbientDerived.quotient A h')

section Represented

variable {S : Type v} [CommRing S]
variable {R₀ : Type r} [CommRing R₀] [Algebra k R₀]

/-- The base-ring structure on the representative uses the given algebra map. -/
abbrev representedAlgebra (e : R₀ ≃+* S) : Algebra k S :=
  (e.toRingHom.comp (algebraMap k R₀)).toAlgebra

/-- The strict comparison after changing the ring representative in a fixed universe. -/
def representedFunctor (e : R₀ ≃+* S) :
    letI := representedAlgebra (k := k) e
    Cochains.compValue.{v} R₀ ⥤ DGMod k S :=
  letI := representedAlgebra (k := k) e
  CochainRingTransport.complexFunctorValue e ⋙ fromComplexFunctor

/-- At every level supporting a ring representative, the comparison has the
original carrier functions and recovers the action of the original ring. -/
def RepresentedRingComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R₀ : Type r) [CommRing R₀] [Algebra k R₀]
    (S : Type v) [CommRing S] (e : R₀ ≃+* S),
    letI := representedAlgebra (k := k) e
    let F := representedFunctor (k := k) e
    F.IsEquivalence ∧
    (∀ (X : Cochains.compValue.{v} R₀) (i : ℤ) (a : R₀) (x : X.X i),
      (F.obj X).act (a := ()) (b := ()) i 0 i (add_zero i) x (scalar k S (e a)) = a • x) ∧
    (∀ (X : Cochains.compValue.{v} R₀) (i j : ℤ) (x : X.X i),
      ((F.obj X).complex ()).d i j x = X.d i j x) ∧
    (∀ {X Y : Cochains.compValue.{v} R₀} (f : X ⟶ Y) (i : ℤ) (x : X.X i),
      ((F.map f).app ()).f i x = f.f i x) ∧
    (∀ X : Cochains.compValue.{v} R₀, X.Acyclic ↔ Module.acyclic (F.obj X)) ∧
    (∀ {X Y : Cochains.compValue.{v} R₀} (f : X ⟶ Y),
      (QuasiIso f ↔ Module.quasiIsomorphism (F.map f)) ∧
      ((∀ i, Function.Surjective (f.f i)) ↔ Module.degreewiseSurjective (F.map f)))

/-- Changing the representative leaves the original homogeneous maps and
their composition unchanged on the underlying carrier functions. -/
def RepresentedHomComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R₀ : Type r) [CommRing R₀] [Algebra k R₀]
    (S : Type v) [CommRing S] (e : R₀ ≃+* S),
    letI := representedAlgebra (k := k) e
    let F := representedFunctor (k := k) e
    let res := (ModuleCat.restrictScalars.{v} (algebraMap k R₀)).mapHomologicalComplex (.up ℤ)
    ∃ E : ∀ X Y : Cochains.compValue.{v} R₀,
        res.obj (CochainModels.internalHomValue X Y) ≅ HomComplex.homComplex (F.obj X) (F.obj Y),
      (∀ (X Y : Cochains.compValue.{v} R₀) (q i t : ℤ) (h : i+q=t)
        (f : Cochain X Y q) (x : X.X i),
        HomComplex.component ((E X Y).hom.f q f) () i t h x = (f.v i t h) x) ∧
      (∀ (X Y : Cochains.compValue.{v} R₀) (f : X ⟶ Y),
        (E X Y).hom.f 0 (Cochain.ofHom f) = HomComplex.ofStrict (F.map f)) ∧
      (∀ (X Y Z : Cochains.compValue.{v} R₀) (q s t : ℤ) (h : s+q=t)
        (f : Cochain X Y q) (g : Cochain Y Z s),
        (E X Z).hom.f t (f.comp g ((add_comm q s).trans h)) =
          HomComplex.compose _ _ _ s q t h ((E Y Z).hom.f s g) ((E X Y).hom.f q f)) ∧
      (∀ X : Cochains.compValue.{v} R₀,
        CochainModels.isKProjectiveValue X ↔ KProjective.isKProjective (F.obj X))

/-- The comparison for a ring representative preserves the actual ordinary homotopies. -/
def RepresentedHomotopyComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R₀ : Type r) [CommRing R₀] [Algebra k R₀]
    (S : Type v) [CommRing S] (e : R₀ ≃+* S),
    letI := representedAlgebra (k := k) e
    let F := representedFunctor (k := k) e
    ∀ {X Y : Cochains.compValue.{v} R₀} (f g : X ⟶ Y),
      Nonempty (Homotopy f g) ↔
        ∃ h : HomComplex.gradedHom (F.obj X) (F.obj Y) (-1),
          HomComplex.HomotopyEquation (F.map f) (F.map g) h

/-- At a fixed term universe the ring representative gives the same shift comparison. -/
def RepresentedShiftComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R₀ : Type r) [CommRing R₀] [Algebra k R₀]
    (S : Type v) [CommRing S] (e : R₀ ≃+* S) (s : ℤ),
    letI := representedAlgebra (k := k) e
    let F := representedFunctor (k := k) e
    let T := CochainComplex.shiftFunctor (ModuleCat.{v} R₀) s
    ∃ a : ∀ X : Cochains.compValue.{v} R₀, F.obj (T.obj X) ≅ ShiftCone.shift (F.obj X) s,
      (∀ (X : Cochains.compValue.{v} R₀) (i : ℤ) (x : X.X (i+s)),
        ((a X).hom.app ()).f i x = x) ∧
      ∀ {X Y : Cochains.compValue.{v} R₀} (f : X ⟶ Y),
        F.map (T.map f) ≫ (a Y).hom = (a X).hom ≫ ShiftCone.shiftMap s (F.map f)

/-- The ring-representative comparison preserves the ordinary cone inclusion and projection. -/
def RepresentedConeComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R₀ : Type r) [CommRing R₀] [Algebra k R₀]
    (S : Type v) [CommRing S] (e : R₀ ≃+* S),
    letI := representedAlgebra (k := k) e
    let F := representedFunctor (k := k) e
    ∀ {X Y : Cochains.compValue.{v} R₀} (f : X ⟶ Y),
      ∃ a : F.obj (CochainComplex.mappingCone f) ≅ ShiftCone.cone (F.map f),
        F.map (CochainComplex.mappingCone.inr f) ≫ a.hom = ShiftCone.coneInclusion (F.map f) ∧
        ∀ (i : ℤ) (x : (CochainComplex.mappingCone f).X i),
          ((ShiftCone.coneProjection (F.map f)).app ()).f i ((a.hom.app ()).f i x) =
            (CochainComplex.mappingCone.fst f).1.v i (i+1) rfl x

/-- The original ring need only be small in the chosen term universe. -/
def SmallRingComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R₀ : Type r) [CommRing R₀] [Algebra k R₀] [Small.{v} R₀],
    let e := CochainRingTransport.shrinkRingEquivValue.{v} R₀
    (representedFunctor (k := k) e).IsEquivalence

/-- The representative's ambient comparison agrees with localization over the original ring. -/
def RepresentedLocalizationComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R₀ : Type r) [CommRing R₀] [Algebra k R₀]
    (S : Type v) [CommRing S] (e : R₀ ≃+* S),
    letI := representedAlgebra (k := k) e
    let A := degreeZeroCategory k S
    let B := AmbientDerived.category.{u,v,0,v} A
    ∀ (h' : Derived.HomotopyCategoryLaws B),
    letI := Derived.homotopyCategory B h'
    letI : Category (AmbientDerived.derivedCategory.{u,v,0,v} A h') :=
      inferInstanceAs (Category (@MorphismProperty.Localization _ (Derived.homotopyCategory B h')
        (Derived.quasiIsomorphisms B)))
    let F := representedFunctor (k := k) e ⋙ AmbientDerived.transportToAmbient.{u,v,0,v} A
    ∃ (H : Cochains.homotopyValue.{v} R₀ ≌ AmbientDerived.homotopyCategory.{u,v,0,v} A)
      (D : Cochains.derivedValue.{v} R₀ ≌ AmbientDerived.derivedCategory.{u,v,0,v} A h')
      (a : ∀ X : Cochains.compValue.{v} R₀,
        H.functor.obj ((Cochains.quotientValue R₀).obj X) ≅
          (F.obj X : AmbientDerived.homotopyCategory.{u,v,0,v} A)),
      (∀ {X Y : Cochains.compValue.{v} R₀} (f : X ⟶ Y),
        H.functor.map ((Cochains.quotientValue R₀).map f) ≫ (a Y).hom =
          (a X).hom ≫ HomComplex.homotopyClass (F.map f)) ∧
      Nonempty (Cochains.qhValue R₀ ⋙ D.functor ≅ H.functor ⋙ AmbientDerived.quotient A h')

/-- The input for independent original ring and complex universes uses the
same-ring term lift, followed by the comparison for the lifted ring. -/
abbrev adequateInput (k : Type u) [CommRing k] (R₀ : Type r) [CommRing R₀] [Algebra k R₀] :=
  CochainCoefficientLift.lift.{r,v} R₀ ⋙
    representedFunctor (k := k) (CochainRingTransport.uliftRingEquivValue.{max r v} R₀)

/-- The same-ring lift and the comparison for any representative at the new coefficient level. -/
def LiftedInputComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R₀ : Type r) [CommRing R₀] [Algebra k R₀]
    (S : Type (max v t)) [CommRing S] (e : R₀ ≃+* S),
    letI := representedAlgebra (k := k) e
    let F := CochainCoefficientLift.lift.{t,v} R₀ ⋙ representedFunctor (k := k) e
    (∀ (X : Cochains.compValue.{v} R₀) (i : ℤ) (a : R₀) (x : X.X i),
      let U := (CochainCoefficientLift.lift.{t,v} R₀).obj X
      let z := CochainCoefficientLift.termEquiv.{t,v} X i x
      (F.obj X).act (a := ()) (b := ()) i 0 i (add_zero i) (show U.X i from z)
        (scalar k S (e a)) =
          CochainCoefficientLift.termEquiv.{t,v} X i (a • x)) ∧
    (∀ (X : Cochains.compValue.{v} R₀) (i j : ℤ) (x : X.X i),
      ((F.obj X).complex ()).d i j (CochainCoefficientLift.termEquiv.{t,v} X i x) =
        CochainCoefficientLift.termEquiv.{t,v} X j (X.d i j x)) ∧
    (∀ {X Y : Cochains.compValue.{v} R₀} (f : X ⟶ Y) (i : ℤ) (x : X.X i),
      ((F.map f).app ()).f i (CochainCoefficientLift.termEquiv.{t,v} X i x) =
        CochainCoefficientLift.termEquiv.{t,v} Y i (f.f i x)) ∧
    (∀ X : Cochains.compValue.{v} R₀, X.Acyclic ↔ Module.acyclic (F.obj X)) ∧
    (∀ {X Y : Cochains.compValue.{v} R₀} (f : X ⟶ Y),
      (QuasiIso f ↔ Module.quasiIsomorphism (F.map f)) ∧
      ((∀ i, Function.Surjective (f.f i)) ↔ Module.degreewiseSurjective (F.map f)))

def AdequateInputComparison : Prop :=
  ∀ (k : Type u) [CommRing k] (R₀ : Type r) [CommRing R₀] [Algebra k R₀],
    let e := CochainRingTransport.uliftRingEquivValue.{max r v} R₀
    letI := representedAlgebra (k := k) e
    let F := adequateInput.{u,v,r} k R₀
    (∀ (X : Cochains.compValue.{v} R₀) (i : ℤ) (a : R₀) (x : X.X i),
      let U := (CochainCoefficientLift.lift.{r,v} R₀).obj X
      let z := CochainCoefficientLift.termEquiv.{r,v} X i x
      (F.obj X).act (a := ()) (b := ()) i 0 i (add_zero i) (show U.X i from z)
        (scalar k (ULift.{max r v} R₀) (e a)) =
          CochainCoefficientLift.termEquiv.{r,v} X i (a • x)) ∧
    (∀ (X : Cochains.compValue.{v} R₀) (i j : ℤ) (x : X.X i),
      ((F.obj X).complex ()).d i j (CochainCoefficientLift.termEquiv.{r,v} X i x) =
        CochainCoefficientLift.termEquiv.{r,v} X j (X.d i j x)) ∧
    (∀ {X Y : Cochains.compValue.{v} R₀} (f : X ⟶ Y) (i : ℤ) (x : X.X i),
      ((F.map f).app ()).f i (CochainCoefficientLift.termEquiv.{r,v} X i x) =
        CochainCoefficientLift.termEquiv.{r,v} Y i (f.f i x)) ∧
    (∀ X : Cochains.compValue.{v} R₀, X.Acyclic ↔ Module.acyclic (F.obj X)) ∧
    (∀ {X Y : Cochains.compValue.{v} R₀} (f : X ⟶ Y),
      (QuasiIso f ↔ Module.quasiIsomorphism (F.map f)) ∧
      ((∀ i, Function.Surjective (f.f i)) ↔ Module.degreewiseSurjective (F.map f)))

end Represented

end

end Specs.DerivedFormalization.DG.OrdinaryComplex
