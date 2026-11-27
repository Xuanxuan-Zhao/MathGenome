import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.OrdinaryComplex
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Derived
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFree
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.AmbientDerived
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellReindex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainRingTransport
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.Algebra.Category.ModuleCat.Biproducts

open CategoryTheory
open CochainComplex.HomComplex

universe u v r j t

namespace DerivedFormalization.OrdinaryComplex

open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.OrdinaryComplex

/-- An ordinary commutative algebra, considered as a dg algebra in degree zero. -/
noncomputable abbrev degreeZeroAlgebra := @Specs.DerivedFormalization.DG.OrdinaryComplex.degreeZeroAlgebra

/-- The associated right dg module of an ordinary cochain complex. -/
noncomputable abbrev fromComplex := @Specs.DerivedFormalization.DG.OrdinaryComplex.fromComplex

/-- Restriction of scalars on complexes with the canonical right action. -/
noncomputable abbrev fromComplexFunctor :=
  @Specs.DerivedFormalization.DG.OrdinaryComplex.fromComplexFunctor

theorem restrictionOfScalars : RestrictionOfScalars := by
  intro k _ R _ _ M i c x
  have h : scalar k R (algebraMap k R c) = c • scalar k R 1 := by
    apply Subtype.ext
    change algebraMap k R c = c • (1 : R)
    rw [Algebra.smul_def, mul_one]
  rw [h, map_smul]
  change c • M.act i 0 i (add_zero i) x ((degreeZeroCategory k R).id ()) = c • x
  rw [M.act_id]

theorem surjectivityComparison : SurjectivityComparison := by
  intro k _ R _ _ X Y f
  change (∀ i, Function.Surjective (f.f i)) ↔ ∀ (_ : Unit) i, Function.Surjective (f.f i)
  exact ⟨fun h _ => h, fun h => h ()⟩

theorem acyclicityComparison : AcyclicityComparison := by
  intro k _ R _ _ X
  change X.Acyclic ↔ ∀ (_ : Unit), ((restrictComplex k R).obj X).Acyclic
  have he (i : ℤ) : ((restrictComplex k R).obj X).ExactAt i ↔ X.ExactAt i :=
    (X.sc i).exact_map_iff_of_faithful (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R)
  exact ⟨fun h _ i => (he i).2 (h i), fun h i => (he i).1 (h () i)⟩

theorem quasiIsoComparison : QuasiIsoComparison := by
  intro k _ R _ _ X Y f
  change QuasiIso f ↔ ∀ (_ : Unit), QuasiIso ((restrictComplex k R).map f)
  exact ⟨fun h _ => (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f
    (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R)).2 h, fun h =>
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R)).1 (h ())⟩


theorem cohomologyComparison : CohomologyComparison := by
  intro k _ R _ _ i
  exact ⟨(Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ _ i)
    (ShortComplex.homologyFunctorIso (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R))).symm⟩

noncomputable section

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R] [Algebra k R]

open private act_zero_degree stalkTerm_zero from MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.OrdinaryComplex

private abbrev rAct (M : DGMod k R) (i : ℤ) (a : R) (x : (M.complex ()).X i) :=
  M.act (a := ()) (b := ()) i 0 i (add_zero i) x (scalar k R a)

private theorem actAssocAt (M : DGMod k R) (i j l p q n : ℤ)
    (hp : i+j=p) (hq : j+l=q) (hn : p+l=n)
    (x : (M.complex ()).X i) (a : stalkTerm k R j) (b : stalkTerm k R l) :
    M.act (a := ()) (b := ()) p l n hn (M.act i j p hp x a) b =
      M.act (a := ()) (b := ()) i q n (by omega) x
        ((degreeZeroCategory k R).comp (a := ()) (b := ()) (c := ()) j l q hq a b) := by
  subst p q n
  exact M.act_assoc (a := ()) (b := ()) (c := ()) i j l x a b

@[instance_reducible] private def termModule (M : DGMod k R) (i : ℤ) : Module R ((M.complex ()).X i) where
  smul := rAct M i
  one_smul := M.act_id () i
  mul_smul a b x := by
    have h := actAssocAt M i 0 0 i 0 i (add_zero i) rfl (add_zero i) x
      (scalar k R b) (scalar k R a)
    rw [mul_comm a b]
    exact h.symm
  smul_zero a := by
    change M.act i 0 i _ 0 (scalar k R a) = 0
    rw [map_zero, LinearMap.zero_apply]
  smul_add a x y := by
    change M.act i 0 i _ (x+y) (scalar k R a) = _
    rw [map_add]
    rfl
  add_smul a b x := by
    change M.act i 0 i _ x (scalar k R (a+b)) = _
    rw [show scalar k R (a+b) = scalar k R a + scalar k R b from rfl, map_add]
    rfl
  zero_smul x := by
    change M.act i 0 i _ x (0 : stalkTerm k R 0) = 0
    rw [map_zero]

private abbrev ordinaryTerm (M : DGMod k R) (i : ℤ) : ModuleCat.{v} R :=
  letI := termModule M i
  ModuleCat.of R ((M.complex ()).X i)

private def ordinaryD (M : DGMod k R) (i j : ℤ) :
    ordinaryTerm M i ⟶ ordinaryTerm M j :=
  ModuleCat.ofHom (X := ordinaryTerm M i) (Y := ordinaryTerm M j)
    { toFun := (M.complex ()).d i j
      map_add' := map_add ((M.complex ()).d i j).hom
      map_smul' := by
        intro r x
        change (M.complex ()).d i j (rAct M i r x) = rAct M j r ((M.complex ()).d i j x)
        by_cases h : i+1 = j
        · subst j
          have hh := M.leibniz (a := ()) (b := ()) i 0 i (add_zero i) x (scalar k R r)
          change _ = _ + i.negOnePow • M.act i 1 (i+1) _ x (0 : stalkTerm k R 1) at hh
          simpa only [map_zero, smul_zero, add_zero] using hh
        · rw [(M.complex ()).shape i j h]
          change 0 = rAct M j r 0
          exact ((termModule M j).smul_zero r).symm }

private abbrev toComplex (M : DGMod k R) : ModuleCochain.{v,v} R where
  X := ordinaryTerm M
  d := ordinaryD M
  shape i j h := by
    apply ModuleCat.hom_ext
    ext x
    change (M.complex ()).d i j x = 0
    rw [(M.complex ()).shape i j h]
    rfl
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    ext x
    change (M.complex ()).d j l ((M.complex ()).d i j x) = 0
    rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
    rfl

private def equivTerm (M : DGMod k R) (i : ℤ) :
    ((fromComplex (k := k) (toComplex M)).complex ()).X i ≃ₗ[k] (M.complex ()).X i where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := restrictionOfScalars M i c x

private def complexCounit (M : DGMod k R) :
    (fromComplex (k := k) (toComplex M)).complex () ≅ M.complex () :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (equivTerm M i).toModuleIso) (by
      intro i j h
      apply ModuleCat.hom_ext
      ext x
      rfl)

private theorem ordinaryAction (X : ModuleCochain.{v,v} R) (i : ℤ)
    (x : X.X i) (z : stalkTerm k R 0) :
    (fromComplex (k := k) X).act (a := ()) (b := ()) i 0 i (add_zero i) x z =
      z.val • x :=
  act_zero_degree X i x z

private def counit (M : DGMod k R) : fromComplex (k := k) (toComplex M) ≅ M where
  hom :=
    { app := fun a => by cases a; exact (complexCounit M).hom
      comm_act := by
        rintro ⟨⟩ ⟨⟩ i j n h x z
        change (fromComplex (k := k) (toComplex M)).act i j n h x z = M.act i j n h x z
        by_cases hj : j = 0
        · subst j
          simp only [add_zero] at h
          cases h
          exact ordinaryAction (k := k) (toComplex M) i x z
        · rw [stalkTerm_zero k R hj z, map_zero, map_zero]
          rfl }
  inv :=
    { app := fun a => by cases a; exact (complexCounit M).inv
      comm_act := by
        rintro ⟨⟩ ⟨⟩ i j n h x z
        change M.act i j n h x z = (fromComplex (k := k) (toComplex M)).act i j n h x z
        by_cases hj : j = 0
        · subst j
          simp only [add_zero] at h
          cases h
          exact (ordinaryAction (k := k) (toComplex M) i x z).symm
        · rw [stalkTerm_zero k R hj z, map_zero, map_zero]
          rfl }
  hom_inv_id := RightDGModuleModel.hom_ext fun a => by cases a; exact (complexCounit M).hom_inv_id
  inv_hom_id := RightDGModuleModel.hom_ext fun a => by cases a; exact (complexCounit M).inv_hom_id

private abbrev F : ModuleCochain.{v,v} R ⥤ DGMod k R := fromComplexFunctor

private def strictPreimage {X Y : ModuleCochain.{v,v} R} (f : (F (k := k)).obj X ⟶ (F (k := k)).obj Y) :
    X ⟶ Y where
  f i := ModuleCat.ofHom
    { toFun := (f.app ()).f i
      map_add' := map_add ((f.app ()).f i).hom
      map_smul' := by
        intro r x
        have e := f.comm_act (a := ()) (b := ()) i 0 i (add_zero i) x (scalar k R r)
        have h₁ := ordinaryAction (k := k) X i x (scalar k R r)
        have h₂ := ordinaryAction (k := k) Y i ((f.app ()).f i x) (scalar k R r)
        exact (congrArg (fun y => (f.app ()).f i y) h₁).symm.trans (e.trans h₂) }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    change (Y.d i j) ((f.app ()).f i x) = (f.app ()).f j (X.d i j x)
    have e := congrArg (fun g => g x) ((f.app ()).comm i j)
    exact e

private theorem map_strictPreimage {X Y : ModuleCochain.{v,v} R}
    (f : (F (k := k)).obj X ⟶ (F (k := k)).obj Y) :
    (F (k := k)).map (strictPreimage f) = f :=
  RightDGModuleModel.hom_ext fun a => by
    cases a
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    ext x
    rfl

private theorem strict_map_injective {X Y : ModuleCochain.{v,v} R} {f g : X ⟶ Y}
    (e : (F (k := k)).map f = (F (k := k)).map g) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext x
  exact congrArg (fun (h : (F (k := k)).obj X ⟶ (F (k := k)).obj Y) => (h.app ()).f i x) e

theorem strictEquivalence : StrictEquivalence := by
  intro k _ R _ _
  let F' := F (k := k) (R := R)
  have : F'.Full := ⟨fun f => ⟨strictPreimage f, map_strictPreimage f⟩⟩
  have : F'.Faithful := ⟨strict_map_injective⟩
  have : F'.EssSurj := ⟨fun M => ⟨toComplex M, ⟨counit M⟩⟩⟩
  exact ({} : F'.IsEquivalence)

private abbrev FG (X Y : ModuleCochain.{v,v} R) (r : ℤ) :=
  HomComplex.gradedHom (F (k := k) |>.obj X) (F (k := k) |>.obj Y) r

private def cochainToGraded {X Y : ModuleCochain.{v,v} R} {r : ℤ}
    (f : Cochain X Y r) : FG (k := k) X Y r :=
  ⟨fun _ => f.map (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R), by
    rintro ⟨⟩ ⟨⟩ i j n ir nr h hi hn x z
    by_cases hj : j = 0
    · subst j
      simp only [add_zero] at h
      cases h
      obtain rfl : ir = nr := hi.symm.trans hn
      change (f.v i ir hi)
          ((fromComplex (k := k) X).act (a := ()) (b := ()) i 0 i h x z) =
        (fromComplex (k := k) Y).act (a := ()) (b := ()) ir 0 ir _ ((f.v i ir hi) x) z
      have e₁ := congrArg (fun y => (f.v i ir hi) y) (ordinaryAction (k := k) X i x z)
      have e₂ := (f.v i ir hi).hom.map_smul z.val (show X.X i from x)
      have e₃ := ordinaryAction (k := k) Y ir ((f.v i ir hi) x) z
      exact e₁.trans (e₂.trans e₃.symm)
    · rw [stalkTerm_zero k R hj z]
      simp [map_zero]⟩

private def gradedToCochain {X Y : ModuleCochain.{v,v} R} {r : ℤ}
    (f : FG (k := k) X Y r) : Cochain X Y r :=
  Cochain.mk fun i j h =>
    ModuleCat.ofHom (X := X.X i) (Y := Y.X j)
      { toFun := HomComplex.component f () i j h
        map_add' := map_add (HomComplex.component f () i j h).hom
        map_smul' := by
          intro a x
          have e := f.property (a := ()) (b := ()) i 0 i j j (add_zero i) h h x (scalar k R a)
          have h₁ := ordinaryAction (k := k) X i x (scalar k R a)
          have h₂ := ordinaryAction (k := k) Y j (HomComplex.component f () i j h x) (scalar k R a)
          exact (congrArg (fun y => HomComplex.component f () i j h y) h₁).symm.trans (e.trans h₂) }

private theorem gradedExt {X Y : ModuleCochain.{v,v} R} {r : ℤ}
    {f g : FG (k := k) X Y r}
    (h : ∀ (i j : ℤ) (e : i+r=j) (x : X.X i),
        HomComplex.component f () i j e x = HomComplex.component g () i j e x) : f = g := by
  apply Subtype.ext
  funext a
  cases a
  apply Cochain.ext
  intro i j e
  apply ModuleCat.hom_ext
  exact LinearMap.ext (h i j e)

private theorem gradedToCochain_apply {X Y : ModuleCochain.{v,v} R} {r : ℤ}
    (f : FG (k := k) X Y r) (i j : ℤ) (h : i+r=j) (x : X.X i) :
    (gradedToCochain f).v i j h x = HomComplex.component f () i j h x := by
  simp only [gradedToCochain, Cochain.mk_v]
  rfl

private def homTermEquiv (X Y : ModuleCochain.{v,v} R) (r : ℤ) :
    (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R).obj ((CochainComplex.linearHomComplex R X Y).X r) ≃ₗ[k]
      (HomComplex.homComplex (F (k := k) |>.obj X) (F (k := k) |>.obj Y)).X r where
  toFun := cochainToGraded
  invFun := gradedToCochain
  left_inv f := by
    apply Cochain.ext
    intro i j e
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [gradedToCochain_apply]
    rfl
  right_inv f := gradedExt fun i j e x => gradedToCochain_apply f i j e x
  map_add' f g := by
    apply Subtype.ext
    funext a
    exact Cochain.map_add f g (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R)
  map_smul' c f := by
    apply gradedExt
    intro i j e x
    change (c • (f.map (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R)).v i j e) x =
       (c • (f.map (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R)).v i j e) x
    rfl

private def homIso (X Y : ModuleCochain.{v,v} R) :
    (restrictComplex k R).obj (CochainComplex.linearHomComplex R X Y) ≅
      HomComplex.homComplex (F (k := k) |>.obj X) (F (k := k) |>.obj Y) :=
  HomologicalComplex.Hom.isoOfComponents (fun r => (homTermEquiv (k := k) X Y r).toModuleIso)
    (by
      intro i j h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext a
      exact δ_map i j f (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R))

theorem homComparison : HomComparison := by
  intro k _ R _ _
  refine ⟨homIso (k := k), ?_, ?_, ?_⟩
  · intros
    rfl
  · intro X Y f
    apply Subtype.ext
    funext a
    exact Cochain.map_ofHom X Y f (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R)
  · intro X Y Z r s t h f g
    apply Subtype.ext
    funext a
    exact Cochain.map_comp Z f g _ (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R)

private theorem homotopyEquation_iff {X Y : ModuleCochain.{v,v} R} (f g : X ⟶ Y)
    (h : FG (k := k) X Y (-1)) :
    HomComplex.HomotopyEquation ((F (k := k)).map f) ((F (k := k)).map g) h ↔
      Cochain.ofHom f = δ (-1) 0 (gradedToCochain h) + Cochain.ofHom g := by
  have rhs (i : ℤ) (x : X.X i) :
      ((δ (-1) 0 (gradedToCochain h) + Cochain.ofHom g).v i i (add_zero i)) x =
        (Y.d (i-1) i (HomComplex.component h () i (i-1) (by omega) x) +
          (show Y.X i from HomComplex.component h () (i+1) i (by omega)
            (X.d i (i+1) x))) + g.f i x := by
    rw [Cochain.add_v, Cochain.ofHom_v,
      δ_v (-1) 0 (by decide) _ i i (add_zero i) (i-1) (i+1) rfl rfl]
    simp only [Int.negOnePow_zero, one_smul, ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.comp_apply, gradedToCochain_apply]
  constructor
  · intro hh
    apply Cochain.ext
    intro i j hij
    simp only [add_zero] at hij
    cases hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [Cochain.ofHom_v, rhs]
    exact sub_eq_iff_eq_add.mp (hh () i x)
  · intro hh a i x
    cases a
    let y : X.X i := x
    have he := congrArg (fun z : Cochain X Y 0 => z.v i i (add_zero i) y) hh
    rw [Cochain.ofHom_v] at he
    exact sub_eq_iff_eq_add.mpr (he.trans (rhs i y))

theorem strictHomotopyComparison : StrictHomotopyComparison := by
  intro k _ R _ _ X Y f g
  constructor
  · rintro ⟨h⟩
    let p := Cochain.equivHomotopy f g h
    refine ⟨(homTermEquiv (k := k) X Y (-1)) p.val, (homotopyEquation_iff f g _).2 ?_⟩
    change Cochain.ofHom f = δ (-1) 0 ((homTermEquiv (k := k) X Y (-1)).symm
      ((homTermEquiv (k := k) X Y (-1)) p.val)) + Cochain.ofHom g
    have he : gradedToCochain ((homTermEquiv (k := k) X Y (-1)) p.val) = p.val :=
      (homTermEquiv (k := k) X Y (-1)).left_inv p.val
    exact p.property.trans (congrArg (fun z : Cochain X Y (-1) =>
      δ (-1) 0 z + Cochain.ofHom g) he.symm)
  · rintro ⟨h, hh⟩
    exact ⟨(Cochain.equivHomotopy f g).symm ⟨gradedToCochain h, (homotopyEquation_iff f g h).1 hh⟩⟩

private def homPostcomp {P M N : DGMod k R} (f : M ⟶ N) :
    HomComplex.homComplex P M ⟶ HomComplex.homComplex P N where
  f i := ModuleCat.ofHom (HomComplex.compose P M N 0 i i (zero_add i) (HomComplex.ofStrict f))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    funext a
    exact δ_comp_ofHom (g.val a) (f.app a) j

private def homTargetIso (P : DGMod k R) {M N : DGMod k R} (e : M ≅ N) :
    HomComplex.homComplex P M ≅ HomComplex.homComplex P N where
  hom := homPostcomp e.hom
  inv := homPostcomp e.inv
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    funext a
    change ((g.val a).comp (Cochain.ofHom (e.hom.app a)) (add_zero r)).comp
      (Cochain.ofHom (e.inv.app a)) (add_zero r) = g.val a
    rw [Cochain.comp_assoc _ _ _ (add_zero r) (add_zero 0) (by omega),
      ← Cochain.ofHom_comp]
    have h := congrArg (fun f : M ⟶ M => f.app a) e.hom_inv_id
    change e.hom.app a ≫ e.inv.app a = 𝟙 _ at h
    rw [h]
    exact (g.val a).comp_id
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    funext a
    change ((g.val a).comp (Cochain.ofHom (e.inv.app a)) (add_zero r)).comp
      (Cochain.ofHom (e.hom.app a)) (add_zero r) = g.val a
    rw [Cochain.comp_assoc _ _ _ (add_zero r) (add_zero 0) (by omega),
      ← Cochain.ofHom_comp]
    have h := congrArg (fun f : N ⟶ N => f.app a) e.inv_hom_id
    change e.inv.app a ≫ e.hom.app a = 𝟙 _ at h
    rw [h]
    exact (g.val a).comp_id

theorem kProjectivityComparison : KProjectivityComparison := by
  intro k _ R _ _ X
  change CochainComplex.IsKProjective X ↔ KProjective.isKProjective (fromComplex (k := k) X)
  refine (DerivedFormalization.isKProjective_iff_internalHom_acyclic X).trans ?_
  constructor
  · intro h N hN
    have hn : (toComplex N).Acyclic :=
      (acyclicityComparison k R (toComplex N)).2 fun a => by
        cases a
        intro i
        exact (hN () i).of_iso (complexCounit N).symm
    have hh := (acyclicityComparison k R (CochainComplex.linearHomComplex R X (toComplex N))).1
      (h _ hn) ()
    exact fun i => (hh i).of_iso
      (homIso (k := k) X (toComplex N) ≪≫ homTargetIso (fromComplex X) (counit N))
  · intro h Y hy
    apply (acyclicityComparison k R (CochainComplex.linearHomComplex R X Y)).2
    intro a i
    exact ((h (fromComplex Y) ((acyclicityComparison k R Y).1 hy)) i).of_iso (homIso X Y).symm

private abbrev ordinaryQuotient : ModuleCochain.{v,v} R ⥤ OrdinaryK R :=
  HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

private abbrev dgQuotient : DGMod k R ⥤ RightDGModule.K (degreeZeroCategory k R) :=
  RightDGModule.toHomotopyCategory (degreeZeroCategory k R)

private def homotopyFunctor :
    OrdinaryK R ⥤ RightDGModule.K (degreeZeroCategory k R) :=
  CategoryTheory.Quotient.lift (homotopic (ModuleCat R) (ComplexShape.up ℤ))
    ((F (k := k)) ⋙ dgQuotient) fun _ _ f g h =>
      (RightDGModule.homotopyCriterion _ _).2 ((strictHomotopyComparison k R f g).1 h)

private theorem homotopyFunctor_map {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y) :
    (homotopyFunctor (k := k)).map (ordinaryQuotient.map f) =
      RightDGModule.homotopyClass ((F (k := k)).map f) :=
  rfl

private theorem homotopyFunctor_equivalence : (homotopyFunctor (k := k) (R := R)).IsEquivalence where
  faithful := ⟨by
    rintro ⟨X⟩ ⟨Y⟩ f g e
    obtain ⟨f', rfl⟩ := ordinaryQuotient.map_surjective f
    obtain ⟨g', rfl⟩ := ordinaryQuotient.map_surjective g
    have hh := (RightDGModule.homotopyCriterion _ _).1 e
    obtain ⟨h⟩ := (strictHomotopyComparison k R f' g').2 hh
    exact HomotopyCategory.eq_of_homotopy f' g' h⟩
  full := ⟨by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨g, rfl⟩ := RightDGModule.homotopyClass_surjective f
    let g' : (F (k := k)).obj X ⟶ (F (k := k)).obj Y := g
    refine ⟨ordinaryQuotient.map (strictPreimage g'), (homotopyFunctor_map _).trans ?_⟩
    exact congrArg RightDGModule.homotopyClass (map_strictPreimage g')⟩
  essSurj := ⟨fun M =>
    ⟨ordinaryQuotient.obj (toComplex M), ⟨dgQuotient.mapIso (counit M)⟩⟩⟩

private theorem homotopyFunctor_quasiIso {X Y : OrdinaryK R} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ) f ↔
      RightDGModule.quasiIsomorphisms (degreeZeroCategory k R) ((homotopyFunctor (k := k)).map f) := by
  cases X with | mk X =>
    cases Y with | mk Y =>
      obtain ⟨g, rfl⟩ := ordinaryQuotient.map_surjective f
      calc
        _ ↔ QuasiIso g := HomotopyCategory.quotient_map_mem_quasiIso_iff g
        _ ↔ Module.quasiIsomorphism ((F (k := k)).map g) := quasiIsoComparison k R g
        _ ↔ _ := (RightDGModule.quasiIsomorphisms_homotopyClass ((F (k := k)).map g)).symm

theorem homotopyCategoryComparison : HomotopyCategoryComparison := by
  intro k _ R _ _ h
  let := Derived.homotopyCategory (degreeZeroCategory k R) h
  let H : OrdinaryK R ⥤ DGK k R := homotopyFunctor
  have : H.IsEquivalence := homotopyFunctor_equivalence
  refine ⟨H.asEquivalence, fun _ => Iso.refl _, ?_, ?_⟩
  · intro X Y f
    let t := H.map (ordinaryQuotient.map f)
    change t ≫ 𝟙 _ = 𝟙 _ ≫ t
    exact (Category.comp_id t).trans (Category.id_comp t).symm
  · exact fun f => homotopyFunctor_quasiIso f


private abbrev ordinaryShift (s : ℤ) :=
  CochainComplex.shiftFunctor (ModuleCat.{v} R) s

private abbrev dgShift (s : ℤ) (X : ModuleCochain.{v,v} R) :=
  ShiftCone.shift (fromComplex (k := k) X) s

private def shiftComplexIso (s : ℤ) (X : ModuleCochain.{v,v} R) :
    (fromComplex (k := k) ((ordinaryShift (R := R) s).obj X)).complex () ≅
      (dgShift (k := k) s X).complex () :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j h
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k R).map_units_smul s.negOnePow (X.d (i+s) (j+s)))

private theorem shiftAction (s : ℤ) (X : ModuleCochain.{v,v} R)
    {i j n : ℤ} (h : i+j=n) (x : X.X (i+s)) (z : stalkTerm k R j) :
    (fromComplex (k := k) ((ordinaryShift (R := R) s).obj X)).act (a := ()) (b := ()) i j n h x z =
        (dgShift (k := k) s X).act (a := ()) (b := ()) i j n h x z := by
  by_cases hj : j = 0
  · subst j
    simp only [add_zero] at h
    cases h
    exact (ordinaryAction (k := k) ((ordinaryShift (R := R) s).obj X) i x z).trans
      (ordinaryAction (k := k) X (i+s) x z).symm
  · rw [stalkTerm_zero k R hj z, map_zero, map_zero]

private def shiftIso (s : ℤ) (X : ModuleCochain.{v,v} R) :
    fromComplex (k := k) ((ordinaryShift (R := R) s).obj X) ≅ dgShift (k := k) s X where
  hom :=
    { app := fun a => by cases a; exact (shiftComplexIso (k := k) s X).hom
      comm_act := by
        rintro ⟨⟩ ⟨⟩ i j n h x z
        exact shiftAction (k := k) s X h x z }
  inv :=
    { app := fun a => by cases a; exact (shiftComplexIso (k := k) s X).inv
      comm_act := by
        rintro ⟨⟩ ⟨⟩ i j n h x z
        exact (shiftAction (k := k) s X h x z).symm }
  hom_inv_id := RightDGModuleModel.hom_ext fun a => by
    cases a
    exact (shiftComplexIso (k := k) s X).hom_inv_id
  inv_hom_id := RightDGModuleModel.hom_ext fun a => by
    cases a
    exact (shiftComplexIso (k := k) s X).inv_hom_id

theorem shiftComparison : ShiftComparison := by
  intro k _ R _ _ s
  refine ⟨shiftIso (k := k) s, fun X i x => rfl, ?_⟩
  intro X Y f
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro i
  rfl

private theorem quasiIso_map_homotopyFunctor :
    RightDGModule.quasiIsomorphisms (degreeZeroCategory k R) ≤
      (HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).map (homotopyFunctor (k := k)) := by
  intro M N f hf
  obtain ⟨g, rfl, hg⟩ := hf
  let eM := counit M
  let eN := counit N
  let f' : fromComplex (k := k) (toComplex M) ⟶ fromComplex (k := k) (toComplex N) :=
    eM.hom ≫ g ≫ eN.inv
  let g' := strictPreimage f'
  have e' := map_strictPreimage f'
  refine ⟨ordinaryQuotient.obj (toComplex M), ordinaryQuotient.obj (toComplex N),
    ordinaryQuotient.map g', ?_, ?_⟩
  · apply (HomotopyCategory.quotient_map_mem_quasiIso_iff g').2
    apply (quasiIsoComparison k R g').2
    change Module.quasiIsomorphism ((F (k := k)).map g')
    suffices hq : Module.quasiIsomorphism f' from e'.symm ▸ hq
    intro a
    let V := RightDGModuleModel.eval (A := degreeZeroCategory k R) a
    have : QuasiIso (V.map g) := hg a
    change QuasiIso (V.map (eM.hom ≫ g ≫ eN.inv))
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  · refine ⟨Arrow.isoMk (dgQuotient.mapIso eM) (dgQuotient.mapIso eN) ?_⟩
    change dgQuotient.map eM.hom ≫ dgQuotient.map g =
      (homotopyFunctor (k := k)).map (ordinaryQuotient.map g') ≫ dgQuotient.map eN.hom
    have hmap : (homotopyFunctor (k := k)).map (ordinaryQuotient.map g') = dgQuotient.map f' :=
      (homotopyFunctor_map g').trans (congrArg dgQuotient.map e')
    have hcomp : eM.hom ≫ g = f' ≫ eN.hom := by simp [f']
    exact (dgQuotient.map_comp _ _).symm.trans
      ((congrArg dgQuotient.map hcomp).trans ((dgQuotient.map_comp _ _).trans
        (congrArg (fun l => l ≫ dgQuotient.map eN.hom) hmap.symm)))

attribute [local instance] HasDerivedCategory.standard

theorem derivedCategoryComparison : DerivedCategoryComparison := by
  intro k _ R _ _ h
  let := Derived.homotopyCategory (degreeZeroCategory k R) h
  let H : OrdinaryK R ⥤ DGK k R := homotopyFunctor
  have : H.IsEquivalence := homotopyFunctor_equivalence
  let W₁ : MorphismProperty (OrdinaryK R) :=
    HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ)
  let W₂ := Derived.quasiIsomorphisms (degreeZeroCategory k R)
  let L₁ : OrdinaryK R ⥤ Specs.DerivedFormalization.Cochains.derivedValue R := DerivedCategory.Qh
  let L₂ := W₂.Q
  have : L₁.IsLocalization W₁ := by
    dsimp only [L₁, W₁]
    infer_instance
  have : L₂.IsLocalization W₂ := by
    dsimp only [L₂]
    infer_instance
  let Φ : LocalizerMorphism W₁ W₂ := ⟨H, fun _ _ f hf => (homotopyFunctor_quasiIso f).1 hf⟩
  have : Φ.functor.IsEquivalence := ‹H.IsEquivalence›
  have : Φ.IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ quasiIso_map_homotopyFunctor
  let G := Φ.localizedFunctor L₁ L₂
  refine ⟨H.asEquivalence, G.asEquivalence, ⟨fun _ => Iso.refl _, ?_, ?_⟩,
    ⟨(Φ.catCommSq L₁ L₂).iso.symm⟩⟩
  · intro X Y f
    let t := H.map (ordinaryQuotient.map f)
    change t ≫ 𝟙 _ = 𝟙 _ ≫ t
    exact (Category.comp_id t).trans (Category.id_comp t).symm
  · exact fun f => homotopyFunctor_quasiIso f

open CategoryTheory.Limits
open HomologicalComplex (homotopyCofiber)

private abbrev dgCone {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y) :=
  ShiftCone.cone ((F (k := k)).map f)

private def coneCoords {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y) (i : ℤ) :
    (CochainComplex.mappingCone f).X i ≃ₗ[R] (Y.X i × X.X (i+1)) where
  toFun x := (homotopyCofiber.sndX f i x, homotopyCofiber.fstX f i (i+1) rfl x)
  invFun p := homotopyCofiber.inrX f i p.1 + homotopyCofiber.inlX f (i+1) i rfl p.2
  left_inv x := by
    let C := CochainComplex.mappingCone f
    let m : C.X i ⟶ C.X i := ModuleCat.ofHom
      (((homotopyCofiber.inrX f i).hom.comp (homotopyCofiber.sndX f i).hom) +
        ((homotopyCofiber.inlX f (i+1) i rfl).hom.comp (homotopyCofiber.fstX f i (i+1) rfl).hom))
    have h : m = 𝟙 _ := by
      apply homotopyCofiber.ext_to_X f i (i+1) rfl
      · apply ModuleCat.hom_ext
        ext y
        have h₁ := congrArg (fun g => g (homotopyCofiber.sndX f i y))
          (homotopyCofiber.inrX_fstX f i (i+1) rfl)
        have h₂ := congrArg (fun g => g (homotopyCofiber.fstX f i (i+1) rfl y))
          (homotopyCofiber.inlX_fstX f (i+1) i rfl)
        change homotopyCofiber.fstX f i (i+1) rfl
          (homotopyCofiber.inrX f i (homotopyCofiber.sndX f i y) +
            homotopyCofiber.inlX f (i+1) i rfl (homotopyCofiber.fstX f i (i+1) rfl y)) = _
        rw [map_add]
        exact congrArg₂ (· + ·) h₁ h₂ |>.trans (zero_add _)
      · apply ModuleCat.hom_ext
        ext y
        have h₁ := congrArg (fun g => g (homotopyCofiber.sndX f i y))
          (homotopyCofiber.inrX_sndX f i)
        have h₂ := congrArg (fun g => g (homotopyCofiber.fstX f i (i+1) rfl y))
          (homotopyCofiber.inlX_sndX f (i+1) i rfl)
        change homotopyCofiber.sndX f i
          (homotopyCofiber.inrX f i (homotopyCofiber.sndX f i y) +
            homotopyCofiber.inlX f (i+1) i rfl (homotopyCofiber.fstX f i (i+1) rfl y)) = _
        rw [map_add]
        exact congrArg₂ (· + ·) h₁ h₂ |>.trans (add_zero _)
    exact congrArg (fun g : C.X i ⟶ C.X i => g x) h
  right_inv p := by
    apply Prod.ext
    · change homotopyCofiber.sndX f i
        (homotopyCofiber.inrX f i p.1 + homotopyCofiber.inlX f (i+1) i rfl p.2) = p.1
      rw [map_add]
      have h₁ := congrArg (fun g => g p.1) (homotopyCofiber.inrX_sndX f i)
      have h₂ := congrArg (fun g => g p.2) (homotopyCofiber.inlX_sndX f (i+1) i rfl)
      exact congrArg₂ (· + ·) h₁ h₂ |>.trans (add_zero _)
    · change homotopyCofiber.fstX f i (i+1) rfl
        (homotopyCofiber.inrX f i p.1 + homotopyCofiber.inlX f (i+1) i rfl p.2) = p.2
      rw [map_add]
      have h₁ := congrArg (fun g => g p.1) (homotopyCofiber.inrX_fstX f i (i+1) rfl)
      have h₂ := congrArg (fun g => g p.2) (homotopyCofiber.inlX_fstX f (i+1) i rfl)
      exact congrArg₂ (· + ·) h₁ h₂ |>.trans (zero_add _)
  map_add' x y := Prod.ext (map_add _ x y) (map_add _ x y)
  map_smul' a x := Prod.ext ((homotopyCofiber.sndX f i).hom.map_smul a x)
    ((homotopyCofiber.fstX f i (i+1) rfl).hom.map_smul a x)

private def fromComplexIso {X : ModuleCochain.{v,v} R} {M : DGMod k R}
    (e : X ≅ toComplex M) : fromComplex (k := k) X ≅ M :=
  (F (k := k)).mapIso e ≪≫ counit M

private theorem rAct_cone {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y) (i : ℤ)
    (a : R) (p : Y.X i × X.X (i+1)) :
    rAct (dgCone (k := k) f) i a p = a • p :=
  Prod.ext (ordinaryAction (k := k) Y i p.1 (scalar k R a))
    (ordinaryAction (k := k) X (i+1) p.2 (scalar k R a))

private def coneTermIso {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y) (i : ℤ) :
    (CochainComplex.mappingCone f).X i ≅ ordinaryTerm (dgCone (k := k) f) i := by
  letI := termModule (dgCone (k := k) f) i
  exact (show (CochainComplex.mappingCone f).X i ≃ₗ[R] ordinaryTerm (dgCone (k := k) f) i from
    { toFun := coneCoords f i
      invFun := (coneCoords f i).symm
      left_inv := (coneCoords f i).left_inv
      right_inv := (coneCoords f i).right_inv
      map_add' := (coneCoords f i).map_add
      map_smul' a x := ((coneCoords f i).map_smul a x).trans (rAct_cone (k := k) f i a _).symm }).toModuleIso

private def coneIso {X Y : ModuleCochain.{v,v} R} (f : X ⟶ Y) :
    fromComplex (k := k) (CochainComplex.mappingCone f) ≅ dgCone (k := k) f :=
  fromComplexIso (HomologicalComplex.Hom.isoOfComponents (coneTermIso (k := k) f) (by
    intro i j h
    obtain rfl : i+1=j := h
    let := termModule (dgCone (k := k) f) (i+1)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ShiftCone.coneDiff ((F (k := k)).map f) () i (i+1)
      (coneCoords f i x) = coneCoords f (i+1) ((CochainComplex.mappingCone f).d i (i+1) x)
    let p : ShiftCone.coneTerm ((F (k := k)).obj X) ((F (k := k)).obj Y) () i :=
      coneCoords f i x
    refine (ShiftCone.coneDiff_succ ((F (k := k)).map f) () i p).trans ?_
    apply Prod.ext
    · have h' := congrArg (fun g => g x) (homotopyCofiber.d_sndX f i (i+1) rfl)
      exact (add_comm _ _).trans h'.symm
    · have h' := congrArg (fun g => g x) (homotopyCofiber.d_fstX f i (i+1) (i+1+1) rfl rfl)
      exact h'.symm))

theorem coneComparison : ConeComparison := by
  intro k _ R _ _ X Y f
  refine ⟨coneIso (k := k) f, ?_, ?_⟩
  · apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change coneCoords f i (homotopyCofiber.inrX f i y) = (y, 0)
    exact Prod.ext (congrArg (fun g => g y) (homotopyCofiber.inrX_sndX f i))
      (congrArg (fun g => g y) (homotopyCofiber.inrX_fstX f i (i+1) rfl))
  · intro i x
    change homotopyCofiber.fstX f i (i+1) rfl x = (CochainComplex.mappingCone.fst f).1.v i (i+1) rfl x
    simp only [CochainComplex.mappingCone.fst]
    rfl

private abbrev regularModule :=
  Yoneda.representable (A := degreeZeroCategory k R) ()

private def regularTermIso :
    ModuleCat.of R R ≅ ordinaryTerm (regularModule (k := k) (R := R)) 0 := by
  letI := termModule (regularModule (k := k) (R := R)) 0
  exact (show R ≃ₗ[R] ordinaryTerm (regularModule (k := k) (R := R)) 0 from
    { toFun := scalar k R
      invFun := Subtype.val
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' a b := Subtype.ext (mul_comm a b) }).toModuleIso

private abbrev regularStalk := (Specs.DerivedFormalization.Cochains.stalkValue R).obj (ModuleCat.of R R)

private def regularStalkTermIso (i : ℤ) :
    (regularStalk (R := R)).X i ≅ (toComplex (regularModule (k := k) (R := R))).X i := by
  by_cases hi : i = 0
  · subst i
    exact HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R) ≪≫
      regularTermIso (k := k)
  · have hs := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of R R) i hi
    have : Subsingleton (ordinaryTerm (regularModule (k := k) (R := R)) i) :=
      ⟨fun x y => (stalkTerm_zero k R hi x).trans (stalkTerm_zero k R hi y).symm⟩
    exact hs.iso (ModuleCat.isZero_of_subsingleton _)

private def regularStalkIso : fromComplex (k := k) (regularStalk (R := R)) ≅ regularModule :=
  fromComplexIso (HomologicalComplex.Hom.isoOfComponents (regularStalkTermIso (k := k)) (by
    intro i j _
    have h₁ := HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 (ModuleCat.of R R) i j
    have h₂ : (toComplex (regularModule (k := k) (R := R))).d i j = 0 := rfl
    erw [h₁, h₂, Limits.comp_zero, Limits.zero_comp]))

private def freeCellIso (n : ℤ) :
    fromComplex (k := k) (ordinaryCell (R := R) n) ≅
      SemiFree.cell (A := degreeZeroCategory k R) () n :=
  shiftIso (k := k) (-n) (regularStalk (R := R)) ≪≫
    { hom := ShiftCone.shiftMap (-n) (regularStalkIso (k := k) (R := R)).hom
      inv := ShiftCone.shiftMap (-n) (regularStalkIso (k := k) (R := R)).inv
      hom_inv_id := RightDGModuleModel.hom_ext fun a => by
        exact (CochainComplex.shiftFunctor (ModuleCat k) (-n)).mapIso
          ((RightDGModuleModel.eval a).mapIso regularStalkIso) |>.hom_inv_id
      inv_hom_id := RightDGModuleModel.hom_ext fun a => by
        exact (CochainComplex.shiftFunctor (ModuleCat k) (-n)).mapIso
          ((RightDGModuleModel.eval a).mapIso regularStalkIso) |>.inv_hom_id }

private theorem regularStalkIso_generator (p : ℤ) (hp : p = 0) :
    ((regularStalkIso (k := k) (R := R)).hom.app ()).f p
        ((HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0
          (ModuleCat.of R R) p hp).inv (1 : R)) =
      ((stalkComplex k R).XIsoOfEq hp.symm).hom (scalar k R 1) := by
  subst p
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)
  change scalar k R (e.hom (e.inv (1 : R))) = scalar k R 1
  exact congrArg (scalar k R) (congrArg (fun f : ModuleCat.of R R ⟶ _ => f (1 : R)) e.inv_hom_id)

private theorem freeCellIso_generator (n : ℤ) :
    ((freeCellIso (k := k) (R := R) n).hom.app ()).f n (ordinaryGenerator n) =
      SemiFree.generator (A := degreeZeroCategory k R) () n :=
  regularStalkIso_generator (n + -n) (add_neg_cancel n)

theorem freeCellGeneratorComparison : FreeCellGeneratorComparison := by
  intro k _ R _ _ n
  exact ⟨freeCellIso n, freeCellIso_generator n⟩

theorem freeCellComparison : FreeCellComparison := by
  intro k _ R _ _ n
  exact ⟨freeCellIso (k := k) (R := R) n⟩

private def ordinaryMap {M N : DGMod k R} (f : M ⟶ N) : toComplex M ⟶ toComplex N :=
  strictPreimage ((counit M).hom ≫ f ≫ (counit N).inv)

private def cellDegreeIso (a : (degreeZeroCategory k R).Obj) (m n : ℤ) (h : m = n) :
    (F (k := k)).obj (ordinaryCell (R := R) n) ≅ SemiFree.cell (A := degreeZeroCategory k R) a m :=
  freeCellIso n ≪≫ eqToIso (by cases a; subst m; rfl)

private theorem cellDegreeIso_generator (a : (degreeZeroCategory k R).Obj) (m n : ℤ) (h : m = n) :
    HEq ((((cellDegreeIso a m n h).hom.app ()).f n) (ordinaryGenerator n))
      (SemiFree.generator (A := degreeZeroCategory k R) a m) := by
  cases a
  subst m
  apply heq_of_eq
  change _ = SemiFree.generator (A := degreeZeroCategory k R) () n
  have f := freeCellIso_generator (k := k) (R := R) n
  simpa only [cellDegreeIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id] using f

private def cellFamilySumData {J I : Type v} {M : DGMod k R}
    (C : SemiFree.CellFamily M J) (d : I → ℤ) (e : I ≃ J)
    (he : ∀ i, C.degree (e i) = d i) :
    { q : (F (k := k)).obj (∐ fun i => ordinaryCell (R := R) (d i)) ≅ SemiFree.cellSum C //
      ∀ i, (F (k := k)).map (Sigma.ι (fun i => ordinaryCell (R := R) (d i)) i) ≫ q.hom =
        (cellDegreeIso (C.object (e i)) (C.degree (e i)) (d i) (he i)).hom ≫
          SemiFree.sumInclusion (SemiFree.cells C) (e i) } := by
  have : (F (k := k) (R := R)).IsEquivalence := strictEquivalence k R
  let G : I → ModuleCochain.{v,v} R := fun i => ordinaryCell (R := R) (d i)
  let B : J → DGMod k R := SemiFree.cells C
  let z : ∀ i, (F (k := k)).obj (G i) ≅ B (e i) := fun i =>
    cellDegreeIso (C.object (e i)) (C.degree (e i)) (d i) (he i)
  have t₁ := isColimitOfHasCoproductOfPreservesColimit (F (k := k)) G
  have t₂ := (Cofan.isColimitEquivOfEquiv e _).1 (RightDGModule.directSumIsColimit B)
  let E : Discrete.functor ((F (k := k)).obj ∘ G) ≅ Discrete.functor (B ∘ e) :=
    Discrete.natIso fun i : Discrete I => z i.as
  let C' : Cofan (B ∘ e) := Cofan.mk (SemiFree.cellSum C)
    (fun i : I => SemiFree.sumInclusion B (e i))
  have t₃ := (IsColimit.precomposeHomEquiv E C').2 t₂
  exact ⟨t₁.coconePointUniqueUpToIso t₃, fun i =>
    t₁.comp_coconePointUniqueUpToIso_hom t₃ ⟨i⟩⟩

private abbrev cellFamilySumIso {J I : Type v} {M : DGMod k R}
    (C : SemiFree.CellFamily M J) (d : I → ℤ) (e : I ≃ J)
    (he : ∀ i, C.degree (e i) = d i) :=
  (cellFamilySumData C d e he).val


private def presentationInclusion {X : ModuleCochain.{v,v} R}
    (P : SemiFree.Presentation (fromComplex (k := k) X)) (j : ℕ) :
    toComplex (P.stage j) ⟶ toComplex (P.stage (j+1)) :=
  ordinaryMap (SemiFree.inclusion (P.family j) ≫ (P.successor j).hom)

private def presentationInto {X : ModuleCochain.{v,v} R}
    (P : SemiFree.Presentation (fromComplex (k := k) X)) (j : ℕ) : toComplex (P.stage j) ⟶ X :=
  strictPreimage ((counit (P.stage j)).hom ≫ P.into j)

private def presentationQuotient {X : ModuleCochain.{v,v} R}
    (P : SemiFree.Presentation (fromComplex (k := k) X))
    {I : ℕ → Type v} {degree : ∀ j, I j → ℤ} (j : ℕ) (e : I j ≃ P.index j)
    (he : ∀ i, (P.family j).degree (e i) = degree j i) :
    toComplex (P.stage (j+1)) ⟶ ∐ fun i => ordinaryCell (R := R) (degree j i) :=
  strictPreimage ((counit _).hom ≫ (P.successor j).inv ≫
    SemiFree.projection (P.family j) ≫ (cellFamilySumIso (P.family j) (degree j) e he).inv)

private theorem presentationShortExact {X : ModuleCochain.{v,v} R}
    (P : SemiFree.Presentation (fromComplex (k := k) X))
    {I : ℕ → Type v} {degree : ∀ j, I j → ℤ} (j : ℕ) (e : I j ≃ P.index j)
    (he : ∀ i, (P.family j).degree (e i) = degree j i)
    (hz : presentationInclusion P j ≫ presentationQuotient P j e he = 0) :
    (ShortComplex.mk _ _ hz).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let C := P.family j
  let E := ((RightDGModuleModel.degree () i).mapIso (P.successor j)).toLinearEquiv
  let T := ((RightDGModuleModel.degree () i).mapIso (cellFamilySumIso C (degree j) e he)).toLinearEquiv
  have hh := (RightDGModule.attachmentQuotient C).1 () i
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change T.symm (E.symm x).2 = 0 ↔ ∃ y, E (y, 0) = x
    constructor
    · intro h
      have h' : (E.symm x).2 = 0 := T.symm.injective (h.trans (map_zero _).symm)
      refine ⟨(E.symm x).1, ?_⟩
      have hp : (((E.symm x).1, 0) : SemiFree.AttachTerm C () i) = E.symm x :=
        Prod.ext rfl h'.symm
      exact (congrArg E hp).trans (E.apply_symm_apply x)
    · rintro ⟨y, rfl⟩
      exact (congrArg (fun z : SemiFree.AttachTerm C () i => T.symm z.2)
        (E.symm_apply_apply (y, 0))).trans (map_zero _)
  · exact E.injective.comp hh.1
  · exact T.symm.surjective.comp (hh.2.1.comp E.symm.surjective)

private def attachRetraction {M : DGMod k R} {I : Type v}
    (C : SemiFree.CellFamily M I) (i : ℤ) :
    ordinaryTerm (SemiFree.attach C) i ⟶ ordinaryTerm M i := by
  letI := termModule (SemiFree.attach C) i
  letI := termModule M i
  exact ModuleCat.ofHom (X := ordinaryTerm (SemiFree.attach C) i) (Y := ordinaryTerm M i)
    { toFun := Prod.fst
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private def ordinaryPresentation {X : ModuleCochain.{v,v} R}
    (P : SemiFree.Presentation (fromComplex (k := k) X))
    {I : ℕ → Type v} {degree : ∀ j, I j → ℤ} (e : ∀ j, I j ≃ P.index j)
    (he : ∀ j i, (P.family j).degree (e j i) = degree j i) :
    CellPresentation X I degree := by
  let incl := presentationInclusion P
  let into := presentationInto P
  let quot j := presentationQuotient P j (e j) (he j)
  have hz (j : ℕ) : incl j ≫ quot j = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    let := termModule (P.stage j) i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let C := P.family j
    let E := ((RightDGModuleModel.degree () i).mapIso (P.successor j)).toLinearEquiv
    let T := ((RightDGModuleModel.degree () i).mapIso (cellFamilySumIso C (degree j) (e j) (he j))).toLinearEquiv
    change T.symm (E.symm (E (x, 0))).2 = 0
    exact (congrArg (fun z : SemiFree.AttachTerm C () i => T.symm z.2)
      (E.symm_apply_apply (x, 0))).trans (map_zero _)
  refine
    { stage := fun j => toComplex (P.stage j)
      bottom := fun i x => P.bottom () i x
      incl := incl
      into := into
      compatible := ?_
      injective := fun j i => P.injective j () i
      exhaustive := fun i x => P.exhaustive () i x
      quotient := quot
      zero := hz
      shortExact := fun j => presentationShortExact P j (e j) (he j) (hz j)
      split := ?_ }
  · intro j
    apply HomologicalComplex.hom_ext
    intro i
    let := termModule (P.stage j) i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : P.stage j ⟶ fromComplex (k := k) X => (f.app ()).f i x) (P.compatible j)
  · intro j i
    let C := P.family j
    let E := ((RightDGModuleModel.degree () i).mapIso (P.successor j)).toLinearEquiv
    refine ⟨(ordinaryMap (P.successor j).inv).f i ≫ attachRetraction C i, ?_⟩
    let := termModule (P.stage j) i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (E.symm (E (x, 0))).1 = x
    exact congrArg (fun z : SemiFree.AttachTerm C () i => z.1) (E.symm_apply_apply (x, 0))

theorem ordinaryPresentationOfDG {X : ModuleCochain.{v,v} R}
    (P : SemiFree.Presentation (fromComplex (k := k) X))
    {I : ℕ → Type v} {degree : ∀ j, I j → ℤ} (e : ∀ j, I j ≃ P.index j)
    (he : ∀ j i, (P.family j).degree (e j i) = degree j i) :
    Nonempty (CellPresentation X I degree) :=
  ⟨ordinaryPresentation P e he⟩

private theorem attachingCycle {X : ModuleCochain.{v,v} R} {I : ℕ → Type v}
    {d : ∀ l, I l → ℤ} (C : CellPresentation X I d)
    (P : SemiFree.Presentation (fromComplex (k := k) X))
    (stage : ∀ l, fromComplex (k := k) (C.stage l) ≅ P.stage l)
    (incl : ∀ l, (F (k := k)).map (C.incl l) ≫ (stage (l+1)).hom =
      (stage l).hom ≫ SemiFree.inclusion (P.family l) ≫ (P.successor l).hom)
    (l : ℕ) (t : P.index l) :
    let a := (P.family l).object t
    let n := (P.family l).degree t
    let g := ((P.successor l).hom.app a).f n (SemiFree.attachedGenerator (P.family l) t)
    let y := ((stage (l+1)).inv.app a).f n g
    let z := ((stage l).inv.app a).f (n+1) ((P.family l).boundary t)
    (C.stage (l+1)).d n (n+1) y = (C.incl l).f (n+1) z := by
  let a := (P.family l).object t
  let n := (P.family l).degree t
  let gen := SemiFree.attachedGenerator (P.family l) t
  let b := (P.family l).boundary t
  let J := SemiFree.inclusion (P.family l) ≫ (P.successor l).hom
  have he : J ≫ (stage (l+1)).inv = (stage l).inv ≫ (F (k := k)).map (C.incl l) := by
    apply (cancel_mono (stage (l+1)).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, incl]
    simp [J]
  have h₁ := CategoryTheory.congr_fun (((stage (l+1)).inv.app a).comm n (n+1))
    (((P.successor l).hom.app a).f n gen)
  have h₂ := CategoryTheory.congr_fun (((P.successor l).hom.app a).comm n (n+1)) gen
  have hg := (RightDGModule.attachmentFormula (P.family l) t).1
  have hd : ((P.stage (l+1)).complex a).d n (n+1) (((P.successor l).hom.app a).f n gen) =
      (J.app a).f (n+1) b := h₂.trans (congrArg ((P.successor l).hom.app a |>.f (n+1)) hg)
  exact h₁.trans ((congrArg ((stage (l+1)).inv.app a |>.f (n+1)) hd).trans
    (congrArg (fun f => (f.app a).f (n+1) b) he))

set_option backward.isDefEq.respectTransparency false in
private def ordinaryPresentationMatch {X : ModuleCochain.{v,v} R}
    (P : SemiFree.Presentation (fromComplex (k := k) X))
    {I : ℕ → Type v} {d : ∀ j, I j → ℤ} (e : ∀ j, I j ≃ P.index j)
    (he : ∀ j i, (P.family j).degree (e j i) = d j i) :
    CellPresentationMatch (ordinaryPresentation P e he) P := by
  let C := ordinaryPresentation P e he
  let stage l := counit (P.stage l)
  have incl (l : ℕ) : (F (k := k)).map (C.incl l) ≫ (stage (l+1)).hom =
      (stage l).hom ≫ SemiFree.inclusion (P.family l) ≫ (P.successor l).hom := by
    change (F (k := k)).map (strictPreimage _) ≫ _ = _
    rw [map_strictPreimage]
    simp [stage]
  refine { index := e
           degree := he
           stage := stage
           sum := fun l => cellFamilySumIso (P.family l) (d l) (e l) (he l)
           cell := fun l s => cellDegreeIso _ _ _ (he l s)
           sum_inclusion := fun l => (cellFamilySumData (P.family l) (d l) (e l) (he l)).property
           cell_generator := fun l s => cellDegreeIso_generator _ _ _ (he l s)
           into := fun l => (map_strictPreimage _).symm
           inclusion := incl
           quotient := ?_
           attaching_cycle := fun l s => attachingCycle C P stage incl l (e l s) }
  intro l
  change (F (k := k)).map (strictPreimage _) ≫ _ = _
  rw [map_strictPreimage]
  simp [stage]

open scoped DirectSum

private abbrev cellsInDegrees {I : Type v} (d : I → ℤ) (s : I) : DGMod k R :=
  SemiFree.cell (A := degreeZeroCategory k R) () (d s)

private abbrev sumOfCells {I : Type v} (d : I → ℤ) :=
  SemiFree.directSum (cellsInDegrees (k := k) (R := R) d)

private abbrev cellFamily {I : Type v} (d : I → ℤ) {P : DGMod k R}
    (z : ∀ s, (P.complex ()).X (d s+1))
    (hz : ∀ s, (P.complex ()).d (d s+1) (d s+1+1) (z s) = 0) :
    SemiFree.CellFamily P I :=
  ⟨fun _ => (), d, z, hz⟩

private theorem sumOfCells_d {I : Type v} (d : I → ℤ) (i : ℤ)
    (x : ((sumOfCells (k := k) (R := R) d).complex ()).X i) :
    ((sumOfCells (k := k) (R := R) d).complex ()).d i (i+1) x = 0 := by
  apply DFinsupp.ext
  intro s
  change ((SemiFree.directSum (cellsInDegrees (k := k) (R := R) d)).complex ()).d i (i+1) x s = 0
  rw [SemiFree.directSum_d]
  change (((-d s).negOnePow • (0 : (stalkComplex k R).X (i + -d s) ⟶
    (stalkComplex k R).X (i+1 + -d s)))) (x s) = 0
  rw [smul_zero]
  rfl

private def strictIsoOfBijective {M N : DGMod k R} (f : M ⟶ N)
    (hf : ∀ i, Function.Bijective ((f.app ()).f i)) : M ≅ N := by
  let b := HomologicalComplex.Hom.isoOfComponents (fun i => (LinearEquiv.ofBijective
    ((f.app ()).f i).hom (hf i)).toModuleIso) (fun i j _ => by
      change (f.app ()).f i ≫ (N.complex ()).d i j = (M.complex ()).d i j ≫ (f.app ()).f j
      exact (f.app ()).comm i j)
  refine ⟨f, ⟨fun a => by cases a; exact b.inv, ?_⟩, ?_, ?_⟩
  · rintro ⟨⟩ ⟨⟩ i j n h x z
    apply (hf n).1
    have hb (q : ℤ) (y : (N.complex ()).X q) : (f.app ()).f q (b.inv.f q y) = y :=
      (LinearEquiv.ofBijective ((f.app ()).f q).hom (hf q)).apply_symm_apply y
    exact (hb n _).trans (((f.comm_act (a := ()) (b := ()) i j n h (b.inv.f i x) z)).trans
      (congrArg (fun y => N.act (a := ()) (b := ()) i j n h y z) (hb i x))).symm
  · apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    exact b.hom_inv_id
  · apply RightDGModuleModel.hom_ext
    rintro ⟨⟩
    exact b.inv_hom_id

private theorem cellGenerator_mulAt (m j i : ℤ) (h : m+j=i)
    (x : (stalkComplex k R).X j) :
    (SemiFree.cell (A := degreeZeroCategory k R) () m).act (a := ()) (b := ()) m j i h
      (SemiFree.generator (A := degreeZeroCategory k R) () m) x = ((stalkComplex k R).XIsoOfEq (by omega : j = i + -m)).hom x := by
  subst i
  exact RightDGModule.cellGenerator_mul (A := degreeZeroCategory k R) () m () j x

section Extension

variable {I : Type v} (d : I → ℤ) {P Q : DGMod k R}
variable (ι : P ⟶ Q) (π : Q ⟶ sumOfCells d)

private abbrev componentAt {M N : DGMod k R} (f : M ⟶ N) (i : ℤ) := (f.app ()).f i

variable (hi : ∀ i, Function.Injective (componentAt ι i))
variable (hp : ∀ i, Function.Surjective (componentAt π i))
variable (hx : ∀ i, Function.Exact (componentAt ι i) (componentAt π i))

private def generatorLift (s : I) : (Q.complex ()).X (d s) :=
  (hp (d s) (SemiFree.summand (cellsInDegrees (k := k) (R := R) d) () (d s) s
    (SemiFree.generator (A := degreeZeroCategory k R) () (d s)))).choose

include hp in
private theorem generatorLift_spec (s : I) :
    componentAt π (d s) (generatorLift d π hp s) =
      SemiFree.summand (cellsInDegrees (k := k) (R := R) d) () (d s) s
        (SemiFree.generator (A := degreeZeroCategory k R) () (d s)) :=
  (hp (d s) _).choose_spec

include hp in
private theorem differential_generatorLift (s : I) :
    componentAt π (d s+1) ((Q.complex ()).d (d s) (d s+1) (generatorLift d π hp s)) = 0 := by
  have h := congrArg (fun f => f (generatorLift d π hp s)) ((π.app ()).comm (d s) (d s+1))
  exact h.symm.trans (sumOfCells_d d (d s) _)

private def chosenBoundary (s : I) : (P.complex ()).X (d s+1) :=
  ((hx (d s+1) _).1 (differential_generatorLift d π hp s)).choose

include hp hx in
private theorem chosenBoundary_spec (s : I) :
    componentAt ι (d s+1) (chosenBoundary d ι π hp hx s) =
      (Q.complex ()).d (d s) (d s+1) (generatorLift d π hp s) :=
  ((hx (d s+1) _).1 (differential_generatorLift d π hp s)).choose_spec

include hi in
private abbrev chosenFamily : SemiFree.CellFamily P I :=
  cellFamily d (chosenBoundary d ι π hp hx) (by
    intro s
    apply hi (d s+1+1)
    have h := congrArg (fun f => f (chosenBoundary d ι π hp hx s))
      ((ι.app ()).comm (d s+1) (d s+1+1))
    refine h.symm.trans ?_
    have he := congrArg (fun x => (Q.complex ()).d (d s+1) (d s+1+1) x)
      (chosenBoundary_spec d ι π hp hx s)
    refine he.trans ?_
    rw [map_zero]
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using
      congrArg (fun f => f (generatorLift d π hp s))
        (HomologicalComplex.d_comp_d (Q.complex ()) (d s) (d s+1) (d s+1+1)))

private def liftCellAt (i : ℤ) (s : I) :
    ((cellsInDegrees (k := k) (R := R) d s).complex ()).X i →ₗ[k] (Q.complex ()).X i :=
  Q.act (a := ()) (b := ()) (d s) (i + -d s) i (by omega) (generatorLift d π hp s)

private def liftSumAt (i : ℤ) :
    ((sumOfCells (k := k) (R := R) d).complex ()).X i →ₗ[k] (Q.complex ()).X i := by
  classical
  exact DirectSum.toModule k I _ (fun s => liftCellAt d π hp i s)

include hp in
private theorem liftSumAt_summand (i : ℤ) (s : I)
    (x : ((cellsInDegrees (k := k) (R := R) d s).complex ()).X i) :
    liftSumAt d π hp i (SemiFree.summand (cellsInDegrees d) () i s x) = liftCellAt d π hp i s x := by
  classical
  exact DirectSum.toModule_lof (R := k) (φ := fun s => liftCellAt d π hp i s) s x

include hp in
private theorem liftSumAt_section (i : ℤ)
    (x : ((sumOfCells (k := k) (R := R) d).complex ()).X i) :
    componentAt π i (liftSumAt d π hp i x) = x := by
  induction x using SemiFree.sum_induction (cellsInDegrees (k := k) (R := R) d) with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | single s x =>
    rw [liftSumAt_summand]
    change componentAt π i (Q.act (d s) (i + -d s) i _ (generatorLift d π hp s) x) = _
    rw [π.comm_act (a := ()) (b := ()), generatorLift_spec]
    change SemiFree.sumAct (cellsInDegrees (k := k) (R := R) d) (a := ()) (b := ())
      (d s) (i + -d s) i _ _ x = _
    rw [SemiFree.sumAct_summand]
    exact congrArg (SemiFree.summand (cellsInDegrees (k := k) (R := R) d) () i s)
      ((cellGenerator_mulAt (k := k) (R := R) (d s) (i + -d s) i (by omega) x).trans rfl)

include hp in
private theorem liftSumAt_act (i j n : ℤ) (h : i+j=n)
    (x : ((sumOfCells (k := k) (R := R) d).complex ()).X i) (a : stalkTerm k R j) :
    liftSumAt d π hp n ((sumOfCells d).act (a := ()) (b := ()) i j n h x a) =
      Q.act (a := ()) (b := ()) i j n h (liftSumAt d π hp i x) a := by
  induction x using SemiFree.sum_induction (cellsInDegrees (k := k) (R := R) d) with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]
  | single s x =>
    change liftSumAt d π hp n (SemiFree.sumAct (cellsInDegrees d) (a := ()) (b := ())
      i j n h (SemiFree.summand (cellsInDegrees d) () i s x) a) = _
    rw [SemiFree.sumAct_summand, liftSumAt_summand, liftSumAt_summand]
    change Q.act (a := ()) (b := ()) (d s) (n + -d s) n _
        (generatorLift d π hp s)
        ((cellsInDegrees d s).act (a := ()) (b := ()) i j n h x a) =
      Q.act (a := ()) (b := ()) i j n h
        (Q.act (a := ()) (b := ()) (d s) (i + -d s) i _ (generatorLift d π hp s) x) a
    exact (actAssocAt Q (d s) (i + -d s) j i (n + -d s) n
      (by omega) (by omega) h (generatorLift d π hp s) x a).symm

include hi hp hx in
private theorem liftSumAt_d (i : ℤ)
    (x : ((sumOfCells (k := k) (R := R) d).complex ()).X i) :
    (Q.complex ()).d i (i+1) (liftSumAt d π hp i x) =
      componentAt ι (i+1) (SemiFree.attachingMap (chosenFamily d ι π hi hp hx) () i x) := by
  induction x using SemiFree.sum_induction (cellsInDegrees (k := k) (R := R) d) with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single s x =>
    rw [liftSumAt_summand]
    have h := Q.leibniz (a := ()) (b := ()) (d s) (i + -d s) i
      (by omega) (generatorLift d π hp s) x
    change (Q.complex ()).d i (i+1) (liftCellAt d π hp i s x) =
      Q.act (a := ()) (b := ()) (d s+1) (i + -d s) (i+1) _
        ((Q.complex ()).d (d s) (d s+1) (generatorLift d π hp s)) x + _ at h
    rw [show ((degreeZeroCategory k R).hom () ()).d (i + -d s) (i + -d s + 1) x = 0 from rfl,
      map_zero, smul_zero, add_zero, ← chosenBoundary_spec d ι π hp hx] at h
    refine h.trans ?_
    change _ = componentAt ι (i+1) (SemiFree.attachingMap (chosenFamily d ι π hi hp hx) () i
      (SemiFree.summand (SemiFree.cells (chosenFamily d ι π hi hp hx)) () i s x))
    rw [SemiFree.attachingMap_summand]
    exact (ι.comm_act (a := ()) (b := ()) (d s+1) (i + -d s) (i+1) (by omega)
      (chosenBoundary d ι π hp hx s) x).symm

include hi hp hx in
private def attachmentHom : SemiFree.attach (chosenFamily d ι π hi hp hx) ⟶ Q where
  app a := by
    cases a
    refine CochainComplex.ofHom (fun i => ModuleCat.ofHom
      (((componentAt ι i).hom.comp (LinearMap.fst k _ _)) +
        (liftSumAt d π hp i).comp (LinearMap.snd k _ _))) ?_
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := congrArg (fun f => f x.1) ((ι.app ()).comm i (i+1))
    change (Q.complex ()).d i (i+1) (componentAt ι i x.1) =
      componentAt ι (i+1) ((P.complex ()).d i (i+1) x.1) at h
    let C := chosenFamily d ι π hi hp hx
    let y := (SemiFree.attachComplex C ()).d i (i+1) x
    change (Q.complex ()).d i (i+1) (componentAt ι i x.1 + liftSumAt d π hp i x.2) =
      componentAt ι (i+1) y.1 + liftSumAt d π hp (i+1) y.2
    rw [map_add, h, liftSumAt_d d ι π hi hp hx]
    have hy : y = ((P.complex ()).d i (i+1) x.1 + SemiFree.attachingMap C () i x.2, 0) := by
      exact (SemiFree.attachComplex_d C () i x).trans (Prod.ext rfl (sumOfCells_d d i x.2))
    rw [hy]
    simp only [map_zero, add_zero, map_add]
    rfl
  comm_act := by
    rintro ⟨⟩ ⟨⟩ i j n h x a
    change componentAt ι n (P.act (a := ()) (b := ()) i j n h x.1 a) +
      liftSumAt d π hp n ((sumOfCells d).act (a := ()) (b := ()) i j n h x.2 a) =
      Q.act (a := ()) (b := ()) i j n h (componentAt ι i x.1 + liftSumAt d π hp i x.2) a
    rw [liftSumAt_act d π hp, ι.comm_act (a := ()) (b := ()), map_add, LinearMap.add_apply]

include hi hp hx in
private theorem attachmentHom_inclusion :
    SemiFree.inclusion (chosenFamily d ι π hi hp hx) ≫ attachmentHom d ι π hi hp hx = ι := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change componentAt ι i x + liftSumAt d π hp i 0 = _
  rw [map_zero, add_zero]

include hi hp hx in
private theorem attachmentHom_projection :
    attachmentHom d ι π hi hp hx ≫ π = SemiFree.projection (chosenFamily d ι π hi hp hx) := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change componentAt π i (componentAt ι i x.1 + liftSumAt d π hp i x.2) = x.2
  rw [map_add, liftSumAt_section, (hx i _).2 ⟨x.1, rfl⟩, zero_add]

include hi hp hx in
private def attachmentIso : SemiFree.attach (chosenFamily d ι π hi hp hx) ≅ Q := by
  refine strictIsoOfBijective (attachmentHom d ι π hi hp hx) (fun i => ⟨?_, ?_⟩)
  · intro x y h
    have hxy (z : SemiFree.AttachTerm (chosenFamily d ι π hi hp hx) () i) :=
      congrArg (fun f => componentAt f i z) (attachmentHom_projection d ι π hi hp hx)
    have h₂ : x.2 = y.2 := (hxy x).symm.trans ((congrArg (componentAt π i) h).trans (hxy y))
    change componentAt ι i x.1 + liftSumAt d π hp i x.2 =
      componentAt ι i y.1 + liftSumAt d π hp i y.2 at h
    rw [h₂] at h
    exact Prod.ext (hi i (add_right_cancel h)) h₂
  · intro y
    let x₂ := componentAt π i y
    have hzero : componentAt π i (y - liftSumAt d π hp i x₂) = 0 := by
      rw [map_sub, liftSumAt_section, sub_self]
    obtain ⟨x₁, h₁⟩ := (hx i _).1 hzero
    refine ⟨(x₁, x₂), ?_⟩
    change componentAt ι i x₁ + liftSumAt d π hp i x₂ = y
    rw [h₁, sub_add_cancel]

end Extension

section Presentation

variable {X : ModuleCochain.{v,v} R} {I : ℕ → Type v} {d : ∀ l, I l → ℤ}
variable (C : CellPresentation X I d)

private abbrev stageInclusion (l : ℕ) := (F (k := k)).map (C.incl l)

private def stageSumIso (l : ℕ) :
    (F (k := k)).obj (∐ fun s : I l => ordinaryCell (R := R) (d l s)) ≅
      sumOfCells (k := k) (R := R) (d l) :=
  cellFamilySumIso (cellFamily (d l) (P := fromComplex (k := k) (C.stage l))
    (fun _ => 0) (fun _ => map_zero _)) (d l) (.refl _) (fun _ => rfl)

private abbrev stageProjection (l : ℕ) := (F (k := k)).map (C.quotient l) ≫ (stageSumIso C l).hom

private theorem ordinaryStageExact (l : ℕ) (i : ℤ) :
    (ShortComplex.mk ((C.incl l).f i) ((C.quotient l).f i)
      (by
        have h := congrArg (fun f : C.stage l ⟶ _ => f.f i) (C.zero l)
        exact h)).ShortExact := by
  exact (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 (C.shortExact l) i

private theorem stageInclusion_injective (l : ℕ) (i : ℤ) :
    Function.Injective (componentAt (stageInclusion (k := k) C l) i) :=
  (ModuleCat.mono_iff_injective ((C.incl l).f i)).1 (ordinaryStageExact C l i).mono_f

private theorem stageProjection_surjective (l : ℕ) (i : ℤ) :
    Function.Surjective (componentAt (stageProjection (k := k) C l) i) :=
  by
    let T := ((RightDGModuleModel.degree () i).mapIso (stageSumIso (k := k) C l)).toLinearEquiv
    change Function.Surjective (T ∘ (C.quotient l).f i)
    exact T.surjective.comp
      ((ModuleCat.epi_iff_surjective ((C.quotient l).f i)).1 (ordinaryStageExact C l i).epi_g)

private theorem stage_exact (l : ℕ) (i : ℤ) :
    Function.Exact (componentAt (stageInclusion (k := k) C l) i)
      (componentAt (stageProjection (k := k) C l) i) := by
  let T := ((RightDGModuleModel.degree () i).mapIso (stageSumIso (k := k) C l)).toLinearEquiv
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (ordinaryStageExact C l i).exact
  intro x
  change T ((C.quotient l).f i x) = 0 ↔ _
  have hT : T ((C.quotient l).f i x) = 0 ↔ (C.quotient l).f i x = 0 :=
    ⟨fun hz => T.injective (hz.trans (map_zero T).symm), fun hz => (congrArg T hz).trans (map_zero T)⟩
  exact hT.trans (h x)

variable (k) in
private abbrev dgPresentation : SemiFree.Presentation (fromComplex (k := k) X) where
  stage l := fromComplex (C.stage l)
  bottom a i x := C.bottom i x
  index := I
  family l := chosenFamily (d l) (stageInclusion C l) (stageProjection C l)
    (stageInclusion_injective C l) (stageProjection_surjective C l) (stage_exact C l)
  successor l := attachmentIso (d l) (stageInclusion C l) (stageProjection C l)
    (stageInclusion_injective C l) (stageProjection_surjective C l) (stage_exact C l)
  into l := (F (k := k)).map (C.into l)
  compatible l := by
    rw [← Category.assoc]
    have h := attachmentHom_inclusion (d l) (stageInclusion (k := k) C l) (stageProjection C l)
      (stageInclusion_injective C l) (stageProjection_surjective C l) (stage_exact C l)
    change (SemiFree.inclusion _ ≫ attachmentHom (d l) (stageInclusion C l) (stageProjection C l) _ _ _) ≫
      (F (k := k)).map (C.into (l+1)) = _
    rw [h, ← Functor.map_comp, C.compatible]
  injective l _ i := C.injective l i
  exhaustive _ i x := C.exhaustive i x

private def dgPresentationMatch : CellPresentationMatch C (dgPresentation k C) := by
  let P := dgPresentation k C
  have hi (l : ℕ) : (F (k := k)).map (C.incl l) =
      SemiFree.inclusion (P.family l) ≫ (P.successor l).hom :=
    (attachmentHom_inclusion (d l) (stageInclusion (k := k) C l) (stageProjection C l)
      (stageInclusion_injective C l) (stageProjection_surjective C l) (stage_exact C l)).symm
  have hq (l : ℕ) : stageProjection (k := k) C l =
      (P.successor l).inv ≫ SemiFree.projection (P.family l) := by
    apply (cancel_epi (P.successor l).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact attachmentHom_projection (d l) (stageInclusion (k := k) C l) (stageProjection C l)
      (stageInclusion_injective C l) (stageProjection_surjective C l) (stage_exact C l)
  let stage l : (F (k := k)).obj (C.stage l) ≅ P.stage l := Iso.refl _
  have hinc (l : ℕ) : (F (k := k)).map (C.incl l) ≫ (stage (l+1)).hom =
      (stage l).hom ≫ SemiFree.inclusion (P.family l) ≫ (P.successor l).hom := by
    simpa only [stage, Iso.refl_hom, Category.comp_id, Category.id_comp] using hi l
  refine { index := fun _ => .refl _
           degree := fun _ _ => rfl
           stage := stage
           sum := stageSumIso C
           cell := fun l s => cellDegreeIso () (d l s) (d l s) rfl
           sum_inclusion := ?_
           cell_generator := fun l s => cellDegreeIso_generator () (d l s) (d l s) rfl
           into := fun l => Category.id_comp _
           inclusion := hinc
           quotient := fun l => (hq l).trans (Category.id_comp _).symm
           attaching_cycle := fun l s => attachingCycle C P stage hinc l s }
  intro l
  exact (cellFamilySumData (cellFamily (d l) (P := fromComplex (k := k) (C.stage l))
    (fun _ => 0) (fun _ => map_zero _)) (d l) (.refl _) (fun _ => rfl)).property

end Presentation

theorem cellFiltrationComparison : CellFiltrationComparison := by
  intro k _ R _ _ X I d
  constructor
  · rintro ⟨C⟩
    exact ⟨dgPresentation k C, fun _ => .refl _, fun _ _ => rfl⟩
  · rintro ⟨P, e, he⟩
    exact ordinaryPresentationOfDG P e he

theorem cellPresentationTransport : CellPresentationTransport := by
  intro k _ R _ _ X
  constructor
  · intro I d C
    exact ⟨dgPresentation k C, ⟨dgPresentationMatch C⟩⟩
  · intro P
    let e (l : ℕ) := Equiv.refl (P.index l)
    let h (l : ℕ) (s : P.index l) : (P.family l).degree (e l s) = (P.family l).degree s := rfl
    exact ⟨P.index, fun l => (P.family l).degree, ordinaryPresentation P e h,
      ⟨ordinaryPresentationMatch P e h⟩⟩

theorem indexedFiltrationComparison : IndexedFiltrationComparison.{u,v,j} := by
  intro k _ R _ _ X P
  have hs (l : ℕ) : Small.{v} (Specs.DerivedFormalization.DG.CellReindex.NonzeroIndex (P.family l)) := by
    let g := fun s : Specs.DerivedFormalization.DG.CellReindex.NonzeroIndex (P.family l) =>
      (⟨(P.family l).degree s.val, (P.extension l).generator s.val⟩ :
        Σ n : ℤ, ((P.stage (l+1)).complex ()).X n)
    apply small_of_injective (f := g)
    intro a b h
    apply (DG.CellReindex.generatorSeparation (P.extension l)).2
    exact congrArg (fun x => (⟨(), x⟩ :
      Σ t : (degreeZeroCategory k R).Obj, Σ n : ℤ, ((P.stage (l+1)).complex t).X n)) h
  obtain ⟨T, ⟨B⟩, _⟩ := DG.CellReindex.toSmall P hs
  let Q := B.toPresentation
  let e (l : ℕ) := Equiv.refl (Q.index l)
  let h (l : ℕ) (s : Q.index l) : (Q.family l).degree (e l s) = (Q.family l).degree s := rfl
  exact ⟨T, B, ordinaryPresentation Q e h, ⟨ordinaryPresentationMatch Q e h⟩⟩


set_option backward.isDefEq.respectTransparency false in
theorem ambientLocalizationComparison : AmbientLocalizationComparison.{u,v} := by
  intro k _ R _ _ h h'
  let A := degreeZeroCategory k R
  let B := DG.AmbientDerived.category.{u,v,0,v} A
  let := Derived.homotopyCategory A h
  let := Derived.homotopyCategory B h'
  let : Category (Specs.DerivedFormalization.DG.AmbientDerived.derivedCategory.{u,v,0,v} A h') :=
    inferInstanceAs (Category (DG.AmbientDerived.derivedCategory.{u,v,0,v} A h'))
  obtain ⟨H, D, ⟨e, he, _⟩, ⟨hD⟩⟩ := derivedCategoryComparison k R h
  let H' := DG.AmbientDerived.homotopyEquivalence.{u,v,0,v} A
  let D' := DG.AmbientDerived.derivedEquivalence.{u,v,0,v} A
  refine ⟨H.trans H', D.trans D', fun X => H'.functor.mapIso (e X), ?_, ?_⟩
  · intro X Y f
    change H'.functor.map (H.functor.map (ordinaryQuotient.map f)) ≫ H'.functor.map (e Y).hom =
      H'.functor.map (e X).hom ≫ HomComplex.homotopyClass
        ((DG.AmbientDerived.transportToAmbient.{u,v,0,v} A).map ((F (k := k)).map f))
    have hmap := congrArg (fun f => H'.functor.map f) (he f)
    exact (H'.functor.map_comp _ _).symm.trans (hmap.trans
      ((H'.functor.map_comp _ _).trans (congrArg (fun g => H'.functor.map (e X).hom ≫ g)
        (DG.AmbientDerived.homotopyTransport_map_class.{u,v,0,v} ((F (k := k)).map f)))))
  · exact ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hD _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft H.functor (DG.AmbientDerived.transportSquare.{u,v,0,v} A) ≪≫
      (Functor.associator _ _ _).symm⟩


section Represented

open Specs.DerivedFormalization.Cochains (compValue)

private abbrev ringComplexFunctor {R₀ : Type r} [CommRing R₀] {S : Type v} [CommRing S]
    (e : R₀ ≃+* S) := CochainRingTransport.complexFunctor e

theorem representedRingComparison : RepresentedRingComparison.{u,v,r} := by
  intro k _ R₀ _ _ S _ e
  let := representedAlgebra (k := k) e
  let E := CochainRingTransport.complexEquivalence e
  let T := ringComplexFunctor e
  have hT : T.IsEquivalence := inferInstanceAs E.functor.IsEquivalence
  have hF : (fromComplexFunctor (k := k) (R := S)).IsEquivalence := strictEquivalence k S
  refine ⟨inferInstanceAs ((T ⋙ fromComplexFunctor (k := k)).IsEquivalence), ?_,
    fun _ _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_⟩
  · intro X i a x
    exact (ordinaryAction (k := k) (T.obj X) i x (scalar k S (e a))).trans
      (by change e.symm (e a) • x = a • x; rw [RingEquiv.symm_apply_apply])
  · intro X
    exact ((CochainRingTransport.complexProperties e X X (𝟙 X)).1).symm.trans
      (acyclicityComparison k S (T.obj X))
  · intro X Y f
    let h := CochainRingTransport.complexProperties e X Y f
    exact ⟨h.2.1.symm.trans (quasiIsoComparison k S (T.map f)),
      surjectivityComparison k S (T.map f)⟩

theorem smallRingComparison : SmallRingComparison.{u,v,r} := by
  intro k _ R₀ _ _ _
  exact (representedRingComparison k R₀ _ (CochainRingTransport.shrinkRingEquiv.{v} R₀)).1

theorem liftedInputComparison : LiftedInputComparison.{u,v,r,t} := by
  intro k _ R₀ _ _ S _ e
  let := representedAlgebra (k := k) e
  let L := CochainCoefficientLift.lift.{t,v} R₀
  have h := representedRingComparison.{u,max v t,r} k R₀ _ e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X i a x
    exact (h.2.1 (L.obj X) i a _).trans (CochainCoefficientLift.lift_smul.{t,v} X i a x)
  · intro X i j x
    exact (h.2.2.1 (L.obj X) i j _).trans (CochainCoefficientLift.lift_d.{t,v} X i j x)
  · intro X Y f i x
    exact (h.2.2.2.1 (L.map f) i _).trans (CochainCoefficientLift.lift_f.{t,v} f i x)
  · intro X
    exact (CochainCoefficientLift.acyclic_iff.{t,v} X).symm.trans (h.2.2.2.2.1 (L.obj X))
  · intro X Y f
    exact ⟨(CochainCoefficientLift.quasiIso_iff.{t,v} f).symm.trans (h.2.2.2.2.2 (L.map f)).1,
      (forall_congr' (fun i => (CochainCoefficientLift.surjective_iff.{t,v} f i).symm)).trans
        (h.2.2.2.2.2 (L.map f)).2⟩

theorem adequateInputComparison : AdequateInputComparison.{u,v,r} := by
  intro k _ R₀ _ _
  exact liftedInputComparison.{u,v,r,r} k R₀ _ (CochainRingTransport.uliftRingEquiv.{max v r} R₀)

private abbrev ringModuleFunctor {R₀ : Type r} [CommRing R₀] {S : Type v} [CommRing S]
    (e : R₀ ≃+* S) := (CochainRingTransport.moduleEquivalence e).functor

section HomTransport

variable {R₀ : Type r} [CommRing R₀] [Algebra k R₀] {S : Type v} [CommRing S]
variable (e : R₀ ≃+* S)

private def cochainBack {X Y : compValue.{v} R₀} {q : ℤ}
    (f : Cochain ((ringComplexFunctor e).obj X) ((ringComplexFunctor e).obj Y) q) :
    Cochain X Y q :=
  Cochain.mk fun i j h =>
    ModuleCat.ofHom (X := X.X i) (Y := Y.X j)
      { toFun := f.v i j h
        map_add' := map_add (f.v i j h).hom
        map_smul' := fun a x => by
          have hh : (show Y.X j from f.v i j h (e.symm (e a) • x)) =
              e.symm (e a) • (show Y.X j from f.v i j h x) :=
            (f.v i j h).hom.map_smul (e a) x
          rw [RingEquiv.symm_apply_apply] at hh
          exact hh }

private def cochainTransportTerm (X Y : compValue.{v} R₀) (q : ℤ) :
    letI := representedAlgebra (k := k) e
    (ModuleCat.restrictScalars.{v} (algebraMap k R₀)).obj ((CochainComplex.linearHomComplex R₀ X Y).X q) ≃ₗ[k]
      (ModuleCat.restrictScalars.{v} (algebraMap k S)).obj
        ((CochainComplex.linearHomComplex S ((ringComplexFunctor e).obj X) ((ringComplexFunctor e).obj Y)).X q) := by
  letI := representedAlgebra (k := k) e
  refine
    { toFun := fun f => f.map (ringModuleFunctor e)
      invFun := cochainBack e
      left_inv := ?_
      right_inv := ?_
      map_add' := fun f g => Cochain.map_add f g _
      map_smul' := ?_ }
  · intro c f
    apply Cochain.ext
    intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (algebraMap k R₀ c) • f.v i j h x =
      e.symm (e (algebraMap k R₀ c)) • f.v i j h x
    rw [RingEquiv.symm_apply_apply]
  · intro f
    apply Cochain.ext
    intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [cochainBack, Cochain.mk_v]
    rfl
  · intro f
    apply Cochain.ext
    intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [cochainBack]
    rfl

private def cochainTransportIso (X Y : compValue.{v} R₀) :
    letI := representedAlgebra (k := k) e
    ((ModuleCat.restrictScalars.{v} (algebraMap k R₀)).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.linearHomComplex R₀ X Y) ≅
    (restrictComplex k S).obj
      (CochainComplex.linearHomComplex S ((ringComplexFunctor e).obj X) ((ringComplexFunctor e).obj Y)) := by
  letI := representedAlgebra (k := k) e
  refine HomologicalComplex.Hom.isoOfComponents (fun q => (cochainTransportTerm (k := k) e X Y q).toModuleIso)
    (fun i j _ => ?_)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact δ_map i j f (ringModuleFunctor e)

private def representedHomIso (X Y : compValue.{v} R₀) :
    letI := representedAlgebra (k := k) e
    ((ModuleCat.restrictScalars.{v} (algebraMap k R₀)).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.linearHomComplex R₀ X Y) ≅
      HomComplex.homComplex ((representedFunctor (k := k) e).obj X) ((representedFunctor (k := k) e).obj Y) :=
  letI := representedAlgebra (k := k) e
  cochainTransportIso (k := k) e X Y ≪≫ homIso ((ringComplexFunctor e).obj X) ((ringComplexFunctor e).obj Y)

private theorem restrictAcyclic (X : compValue.{v} R₀) :
    (((ModuleCat.restrictScalars.{v} (algebraMap k R₀)).mapHomologicalComplex (.up ℤ)).obj X).Acyclic ↔
      X.Acyclic := by
  apply forall_congr'
  intro i
  exact (X.sc i).exact_map_iff_of_faithful (ModuleCat.restrictScalars (algebraMap k R₀))

end HomTransport

theorem representedHomComparison : RepresentedHomComparison.{u,v,r} := by
  intro k _ R₀ _ _ S _ e
  let := representedAlgebra (k := k) e
  let G := representedFunctor (k := k) e
  let T := ringModuleFunctor e
  refine ⟨representedHomIso (k := k) e, fun _ _ _ _ _ _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro X Y f
    change cochainToGraded ((Cochain.ofHom f).map T) = _
    rw [Cochain.map_ofHom]
    apply Subtype.ext
    funext a
    exact Cochain.map_ofHom _ _ ((ringComplexFunctor e).map f)
      (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k S)
  · intro X Y Z q s t h f g
    change cochainToGraded ((f.comp g ((add_comm q s).trans h)).map T) =
      HomComplex.compose _ _ _ s q t h (cochainToGraded (g.map T)) (cochainToGraded (f.map T))
    rw [Cochain.map_comp]
    apply Subtype.ext
    funext a
    exact Cochain.map_comp _ (f.map T) (g.map T) _
      (Specs.DerivedFormalization.DG.OrdinaryComplex.restrictScalars k S)
  · intro X
    have h := representedRingComparison k R₀ S e
    have : G.IsEquivalence := h.1
    change CochainComplex.IsKProjective X ↔ KProjective.isKProjective (G.obj X)
    refine (DerivedFormalization.isKProjective_iff_internalHom_acyclic X).trans ?_
    constructor
    · intro hP N hN
      let Y := G.objPreimage N
      let a := G.objObjPreimageIso N
      have hY : Y.Acyclic := (h.2.2.2.2.1 Y).2 fun b i =>
        (hN b i).of_iso ((RightDGModuleModel.eval b).mapIso a).symm
      have hn := (restrictAcyclic (k := k) _).2 (hP Y hY)
      exact fun i => (hn i).of_iso (representedHomIso (k := k) e X Y ≪≫ homTargetIso (G.obj X) a)
    · intro hP Y hY
      apply (restrictAcyclic (k := k) _).1
      exact fun i => (hP (G.obj Y) ((h.2.2.2.2.1 Y).1 hY) i).of_iso
        (representedHomIso (k := k) e X Y).symm

set_option backward.isDefEq.respectTransparency false in
theorem representedLocalizationComparison : RepresentedLocalizationComparison.{u,v,r} := by
  intro k _ R₀ _ _ S _ e A B h'
  let := representedAlgebra (k := k) e
  let h : Derived.HomotopyCategoryLaws A := ⟨RightDGModule.instCategoryK A, rfl⟩
  let := Derived.homotopyCategory B h'
  let : Category (Specs.DerivedFormalization.DG.AmbientDerived.derivedCategory.{u,v,0,v} A h') :=
    inferInstanceAs (Category (DG.AmbientDerived.derivedCategory.{u,v,0,v} A h'))
  obtain ⟨H, D, a, ha, ⟨hD⟩⟩ := ambientLocalizationComparison k S h h'
  let H₀ := CochainRingTransport.homotopyEquivalence e
  let D₀ := CochainRingTransport.derivedEquivalence e
  let T := ringComplexFunctor e
  let F' := fromComplexFunctor (k := k) (R := S) ⋙ DG.AmbientDerived.transportToAmbient.{u,v,0,v} A
  let J := RightDGModule.toHomotopyCategory B
  let α : ordinaryQuotient ⋙ H.functor ≅ F' ⋙ J := NatIso.ofComponents a ha
  let β : (Specs.DerivedFormalization.Cochains.quotientValue R₀) ⋙ (H₀.trans H).functor ≅
      ((representedFunctor (k := k) e) ⋙ DG.AmbientDerived.transportToAmbient.{u,v,0,v} A) ⋙ J :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CochainRingTransport.homotopyFactors e) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T α ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _).symm _
  refine ⟨H₀.trans H, D₀.trans D, fun X => β.app X, fun f => β.hom.naturality f, ?_⟩
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CochainRingTransport.derivedFactorsh e) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H₀.functor hD ≪≫
    (Functor.associator _ _ _).symm⟩


theorem representedHomotopyComparison : RepresentedHomotopyComparison.{u,v,r} := by
  intro k _ R₀ _ _ S _ e _ X Y f g
  let := representedAlgebra (k := k) e
  let T := ringComplexFunctor e
  let U := ringModuleFunctor e
  refine Iff.trans ?_ (strictHomotopyComparison k S (T.map f) (T.map g))
  exact ⟨fun ⟨h⟩ => ⟨U.mapHomotopy h⟩, fun ⟨h⟩ => ⟨U.preimageHomotopy h⟩⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem representedShiftComparison : RepresentedShiftComparison.{u,v,r} := by
  intro k _ R₀ _ _ S _ e s
  let := representedAlgebra (k := k) e
  let T := ringComplexFunctor e
  let G := fromComplexFunctor (k := k) (R := S)
  let a := T.commShiftIso s
  obtain ⟨b, hb, hn⟩ := shiftComparison k S s
  refine ⟨fun X => G.mapIso (a.app X) ≪≫ b (T.obj X), ?_, ?_⟩
  · intro X i x
    have h := (CochainRingTransport.shiftCompatibility e).1 X s i
    change (((b (T.obj X)).hom.app ()).f i) (((a.app X).hom.f i) x) = x
    exact (congrArg ((b (T.obj X)).hom.app () |>.f i) (CategoryTheory.congr_fun h x)).trans
      (hb (T.obj X) i x)
  · intro X Y f
    change G.map (T.map ((CochainComplex.shiftFunctor (ModuleCat.{v} R₀) s).map f)) ≫
        G.map (a.hom.app Y) ≫ (b (T.obj Y)).hom =
      (G.map (a.hom.app X) ≫ (b (T.obj X)).hom) ≫ ShiftCone.shiftMap s (G.map (T.map f))
    rw [← Category.assoc, ← Functor.map_comp]
    have h := a.hom.naturality f
    change T.map ((CochainComplex.shiftFunctor (ModuleCat.{v} R₀) s).map f) ≫ a.hom.app Y =
      a.hom.app X ≫ (ordinaryShift (R := S) s).map (T.map f) at h
    rw [h, Functor.map_comp, Category.assoc, hn, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem representedConeComparison : RepresentedConeComparison.{u,v,r} := by
  intro k _ R₀ _ _ S _ e _ X Y f
  let := representedAlgebra (k := k) e
  let T := ringComplexFunctor e
  let U := ringModuleFunctor e
  let G := fromComplexFunctor (k := k) (R := S)
  let g := (U.mapHomologicalComplex (ComplexShape.up ℤ)).map f
  let c := CochainComplex.mappingCone.mapHomologicalComplexIso f U
  obtain ⟨b, hb, hp⟩ := coneComparison k S g
  refine ⟨G.mapIso c ≪≫ b, ?_, ?_⟩
  · change G.map (T.map (CochainComplex.mappingCone.inr f)) ≫ G.map c.hom ≫ b.hom = _
    rw [← Category.assoc, ← Functor.map_comp,
      CochainComplex.mappingCone.map_inr f U]
    exact hb
  · intro i x
    let p := CochainComplex.mappingCone.fst g
    let q := CochainComplex.mappingCone.fst f
    have h : c.hom.f i ≫ p.1.v i (i+1) rfl = U.map (q.1.v i (i+1) rfl) := by
      open CochainComplex.mappingCone in
      change (mapHomologicalComplexXIso f U i).hom ≫ p.1.v i (i+1) rfl = _
      simp only [mapHomologicalComplexXIso, mapHomologicalComplexXIso'_hom, Preadditive.add_comp, Category.assoc,
        p, q, g, inl_v_fst_v, inr_f_fst_v, Limits.comp_zero, add_zero]
      exact Category.comp_id _
    change ((ShiftCone.coneProjection (G.map g)).app ()).f i
      (((b.hom.app ()).f i) (c.hom.f i x)) = _
    exact (hp i (c.hom.f i x)).trans (CategoryTheory.congr_fun h x)

end Represented

end

end DerivedFormalization.OrdinaryComplex
