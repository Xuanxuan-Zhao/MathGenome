import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentModelProperties
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeResolution
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift
import Batteries.Tactic.OpenPrivate

open CategoryTheory
open CochainComplex.HomComplex (Cochain)

universe u v t

set_option linter.style.haveILetI false

namespace DerivedFormalization.Affine.CotangentComplex

open Specs.DerivedFormalization.Affine.CotangentComplex
open Specs.DerivedFormalization.Affine.Tensor
  (ModuleTensor regular term act signedLeft restrict restrictFunctor)
open Specs.DerivedFormalization.DG.HomComplex
  (component gradedHom ofStrict HomotopyEquation)
open Kahler (DifferentialModel value)

open private unit_tensor_action signedLeft_regular tensor_ext
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison
open private classMap_strict represented_naturality
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift

noncomputable section

section Native

variable {k : Type u} [Field k] [CharZero k]
variable {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}
variable {T : ModuleTensor.{u,v} k}

private def unitTensor {P Q : CommDGAlgebra.{u,v} k} (p : P ⟶ Q) (M : P.Module)
    (h : T.Formulas p (regular Q)) : M ⟶ restrict p ((T.baseChange p).obj M) :=
  Tensor.homOfDegrees
    (fun i => (T.degree p M (regular Q) i).toLinearMap.comp
      ((Tensor.pair p (N := regular Q) i 0 i (add_zero i)).flip Q.one))
    (by
      intro i x
      simp only [Tensor.differential, LinearMap.comp_apply, LinearMap.flip_apply,
        LinearEquiv.coe_coe]
      change (((T.baseChange p).obj M).complex ()).d i (i+1)
          (T.tmul p (N := regular Q) i 0 i (add_zero i) x Q.one) = _
      rw [h.differential, show ((regular Q).complex ()).d 0 (0+1) Q.one = 0 from
        Q.toDGAlgebra.d_id ()]
      simp only [ModuleTensor.tmul, ← Tensor.pair_apply, map_zero, smul_zero, add_zero])
    (by
      intro i j n e x a
      change T.tmul p (N := regular Q) n 0 n (add_zero n) (act M i j n e x a) Q.one =
        act ((T.baseChange p).obj M) i j n e
          (T.tmul p (N := regular Q) i 0 i (add_zero i) x Q.one) (p.chainMap.f j a)
      rw [unit_tensor_action T h]
      apply congrArg (T.degree p M (regular Q) n)
      have he := Tensor.pure_balance p (N := regular Q) i j 0 n j n
        e (add_zero j) (add_zero n) x a Q.one
      rw [signedLeft_regular, Q.toDGAlgebra.comp_id] at he
      exact he)

private theorem unitTensor_apply {P Q : CommDGAlgebra.{u,v} k}
    (p : P ⟶ Q) (M : P.Module) (h : T.Formulas p (regular Q)) (i : ℤ) (x : term M i) :
    ((unitTensor p M h).app ()).f i x =
      T.tmul p (N := regular Q) i 0 i (add_zero i) x Q.one :=
  rfl

private theorem differentialMap_ext {P Q : CommDGAlgebra.{u,v} k} {f : P ⟶ Q}
    (O : DifferentialModel f) {N : Q.Module} {c d : O.module ⟶ N}
    (h : ∀ i x, (c.app ()).f i (value O.symbol i i (add_zero i) x) =
      (d.app ()).f i (value O.symbol i i (add_zero i) x)) : c = d := by
  let D : Kahler.Derivation f N 0 :=
    ⟨Cochain.mk (fun i p e => value O.symbol i p e ≫ (c.app ()).f p), by
      constructor
      · intro i p e a
        cases (show i = p by omega)
        simp only [Cochain.mk_v, ModuleCat.comp_apply]
        rw [O.symbol.property.relative i i (add_zero i) a, map_zero]
      · intro i j n ir jr nr e hi hj hn x y
        cases (show i = ir by omega)
        cases (show j = jr by omega)
        cases (show n = nr by omega)
        simp only [Cochain.mk_v, ModuleCat.comp_apply]
        rw [O.symbol.property.leibniz i j n i j n e (add_zero i) (add_zero j) (add_zero n)]
        simp only [map_add, Units.smul_def, map_zsmul, c.comm_act]⟩
  obtain ⟨F, _, hF⟩ := O.represents N 0 D
  have hc : ofStrict c = F := hF _ (by
    intro i p e x
    cases (show i = p by omega)
    simp only [component, ofStrict, Cochain.ofHom_v, value, D, Cochain.mk_v, ModuleCat.comp_apply])
  have hd : ofStrict d = F := hF _ (by
    intro i p e x
    cases (show i = p by omega)
    simp only [component, ofStrict, Cochain.ofHom_v, value, D, Cochain.mk_v, ModuleCat.comp_apply]
    exact (h i x).symm)
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  ext i x
  have eq := congrArg (fun g : gradedHom O.module N 0 => component g () i i (add_zero i) x)
    (hc.trans hd.symm)
  simpa only [component, ofStrict, Cochain.ofHom_v] using eq

private theorem induced_unique {R S : Model b} (f : Lift R S)
    (hp : T.Formulas (R.augmentation : R.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
      (regular B.toCommDGAlgebra))
    {c d : R.module T ⟶ S.module T} (hc : Induced T f c) (hd : Induced T f d) : c = d := by
  let p : R.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra := R.augmentation
  let U := unitTensor p R.differentials.module hp
  have he : U ≫ (restrictFunctor p).map c = U ≫ (restrictFunctor p).map d := by
    apply differentialMap_ext R.differentials
    intro i x
    change (c.app ()).f i ((U.app ()).f i _) = (d.app ()).f i ((U.app ()).f i _)
    rw [unitTensor_apply]
    exact (hc i 0 i (add_zero i) x B.one).trans (hd i 0 i (add_zero i) x B.one).symm
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply tensor_ext T
  intro i j e x a
  rw [← unit_tensor_action T hp i j n e x a, c.comm_act, d.comm_act]
  have hh := CategoryTheory.congr_fun
    (congrArg (fun F : R.differentials.module ⟶ restrict p (S.module T) => (F.app ()).f i) he) x
  change (c.app ()).f i ((U.app ()).f i x) = (d.app ()).f i ((U.app ()).f i x) at hh
  rw [unitTensor_apply] at hh
  exact congrArg (fun z => act (S.module T) i j n e z a) hh

private theorem induced_homotopic {R S : Model b} (f g : Lift R S)
    (hp : T.Formulas (R.augmentation : R.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
      (regular B.toCommDGAlgebra))
    (hq : T.Formulas (S.augmentation : S.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
      (regular B.toCommDGAlgebra)) :
    ∃ c d, Induced T f c ∧ Induced T g d ∧
      ∃ h : gradedHom (R.module T) (S.module T) (-1), HomotopyEquation c d h := by
  let J := PolynomialPath.relativePathModel S.augmentation
  obtain ⟨H, hbase, hfirst, hsecond, haug⟩ :=
    RelativePathComparison.relativePathLifting R.base S.base R.augmentation S.augmentation
      J g.hom f.hom R.semifree S.surjective S.quasiIso g.base_comm f.base_comm
      g.augmentation_comm f.augmentation_comm
  let W := PolynomialPath.modulePathModel (S.module T)
  obtain ⟨F, _, hends, h, hhom, _⟩ :=
    RelativePathComparison.pathToCotangentHomotopy (𝟙 A) R.base S.base
      R.augmentation S.augmentation J H
      (by simpa only [Category.id_comp] using hbase) haug T
      R.differentials S.differentials hp hq W
  exact ⟨F ≫ W.evaluation 1, F ≫ W.evaluation 0,
    hends f.hom 1 (Or.inr ⟨hsecond.symm, rfl⟩),
    hends g.hom 0 (Or.inl ⟨hfirst.symm, rfl⟩), h, hhom⟩

private theorem induced_id (R : Model b) : Induced T (Lift.id R) (𝟙 (R.module T)) := by
  intro i j n e x a
  rfl

private theorem induced_comp {R S U : Model b} {f : Lift R S} {g : Lift S U}
    {c : R.module T ⟶ S.module T} {d : S.module T ⟶ U.module T}
    (hc : Induced T f c) (hd : Induced T g d) : Induced T (f.comp g) (c ≫ d) := by
  intro i j n e x a
  change (d.app ()).f n ((c.app ()).f n _) = _
  rw [hc i j n e x a, hd i j n e (f.hom.chainMap.f i x) a]
  rfl

private theorem moduleClass_comp (h : Specs.DerivedFormalization.DG.Derived.HomotopyCategoryLaws
    (oneObject B)) {M N L : B.Module} (c : M ⟶ N) (d : N ⟶ L) :
    letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory (oneObject B) h
    moduleClass h (c ≫ d) = moduleClass h c ≫ moduleClass h d :=
  (RightDGModule.toHomotopyCategory (oneObject B)).map_comp c d

theorem nativeComparison : NativeComparison.{u,v} := by
  classical
  intro k _ _ A B b T h forms
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory (oneObject B) h
  obtain ⟨P, a, p, htriangle, hfree, hsurj, hqi⟩ := semifreeResolution b
  let R₀ : Model b := ⟨⟨P, a, p, htriangle, hfree, hsurj, hqi⟩, Kahler.model a⟩
  have hlift (R S : Model b) : Nonempty (Lift R S) := by
    obtain ⟨g, hbase, haug⟩ := Semifree.exists_lift_of_surjective_quasiIso R.base S.base b
      R.augmentation S.augmentation R.semifree R.triangle S.triangle S.surjective S.quasiIso
    exact ⟨g, hbase, haug⟩
  let chooseLift (R S : Model b) := Classical.choice (hlift R S)
  have hforms (R : Model b) : T.Formulas
      (R.augmentation : R.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
      (regular B.toCommDGAlgebra) := forms _ _
  have hm {R S : Model b} (f : Lift R S) : ∃ c, Induced T f c := by
    obtain ⟨c, _, hc, _, _⟩ := induced_homotopic f f (hforms R) (hforms S)
    exact ⟨c, hc⟩
  let map {R S : Model b} (f : Lift R S) := Classical.choose (hm f)
  have hmap {R S : Model b} (f : Lift R S) : Induced T f (map f) :=
    Classical.choose_spec (hm f)
  have huniq {R S : Model b} (f : Lift R S) (c : R.module T ⟶ S.module T)
      (hc : Induced T f c) : c = map f := induced_unique f (hforms R) hc (hmap f)
  have hh {R S : Model b} (f g : Lift R S) :
      ∃ s : gradedHom (R.module T) (S.module T) (-1), HomotopyEquation (map f) (map g) s := by
    obtain ⟨c, d, hc, hd, w, hw⟩ := induced_homotopic f g (hforms R) (hforms S)
    exact ⟨w, huniq f c hc ▸ huniq g d hd ▸ hw⟩
  have hind {R S : Model b} (f g : Lift R S) :
      comparisonClass h (map f) = comparisonClass h (map g) :=
    (RightDGModule.homotopyCriterion _ _).mpr (hh f g)
  have hid (R : Model b) : map (Lift.id R) = 𝟙 (R.module T) :=
    (huniq (Lift.id R) _ (induced_id R)).symm
  have hmul {R S U : Model b} (f : Lift R S) (g : Lift S U) :
      map f ≫ map g = map (f.comp g) := huniq _ _ (induced_comp (hmap f) (hmap g))
  have hidClass (R : Model b) (f : Lift R R) :
      comparisonClass h (map f) =
        @CategoryStruct.id _ (Specs.DerivedFormalization.DG.Derived.homotopyCategory
          (oneObject B) h).toCategoryStruct (R.module T) := by
    rw [hind f (Lift.id R), hid R]
    rfl
  refine ⟨{
    chosen := R₀
    lift := chooseLift
    map := map
    induced := hmap
    unique := huniq
    homotopy := hh
    independence := hind
    properties := ?_
    identity := fun R => hidClass R _
    cocycle := ?_
    iso := ?_ }⟩
  · intro R
    exact CotangentModelProperties.cotangentModelProperties T b R.base R.augmentation
      R.differentials R.triangle R.semifree R.surjective R.quasiIso (hforms R) (forms _)
  · intro R S U
    rw [← moduleClass_comp, hmul]
    exact hind _ _
  · intro R S f
    let g := chooseLift S R
    refine ⟨⟨comparisonClass h (map g), ?_, ?_⟩⟩
    · rw [← moduleClass_comp, hmul]
      exact hidClass R _
    · rw [← moduleClass_comp, hmul]
      exact hidClass S _

theorem cotangentExists : CotangentExists.{u,v} := by
  intro k _ _ A B b
  let T := Tensor.moduleTensorModel.{u,v} k
  have h := RightDGModule.homotopyCategoryStructure (oneObject B)
  exact ⟨T, h, Tensor.moduleTensor_formulas, nativeComparison b T h Tensor.moduleTensor_formulas⟩

end Native


section Coefficients

open Specs.DerivedFormalization.DG.CoefficientLift (liftMap liftModule)
open Specs.DerivedFormalization.DG.AmbientDerived (strictInput)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws homotopyCategory quotient)
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)

variable {k : Type u} [Field k] [CharZero k]
variable {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}
variable {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}

private def prePostHomotopy {C : CommDGAlgebra.{u,v} k} {L M N K : C.Module}
    (a : L ⟶ M) (w : gradedHom M N (-1)) (b : N ⟶ K) : gradedHom L K (-1) :=
  ⟨fun x => Cochain.mk (fun i j e => (a.app x).f i ≫ component w x i j e ≫ (b.app x).f j), by
    rintro ⟨⟩ ⟨⟩ i j n ir nr e ei en x y
    simp only [Cochain.mk_v, ModuleCat.comp_apply, a.comm_act]
    rw [w.property (a := ()) (b := ()) i j n ir nr e ei en, b.comm_act]⟩

private theorem prePostHomotopy_equation {C : CommDGAlgebra.{u,v} k} {L M N K : C.Module}
    (a : L ⟶ M) {c d : M ⟶ N} (w : gradedHom M N (-1)) (b : N ⟶ K)
    (h : HomotopyEquation c d w) :
    HomotopyEquation (a ≫ c ≫ b) (a ≫ d ≫ b) (prePostHomotopy a w b) := by
  intro x i z
  change (b.app x).f i ((c.app x).f i ((a.app x).f i z)) -
      (b.app x).f i ((d.app x).f i ((a.app x).f i z)) =
    (K.complex x).d (i-1) i
      ((b.app x).f (i-1) (component w x i (i-1) (by omega) ((a.app x).f i z))) +
    (b.app x).f i (component w x (i+1) i (by omega)
      ((a.app x).f (i+1) ((L.complex x).d i (i+1) z)))
  rw [← map_sub, h x i, map_add]
  have hb := CategoryTheory.congr_fun ((b.app x).comm (i-1) i)
    (component w x i (i-1) (by omega) ((a.app x).f i z))
  have ha := CategoryTheory.congr_fun ((a.app x).comm i (i+1)) z
  simp only [ModuleCat.comp_apply] at hb ha
  rw [hb, ha]

private theorem upHomotopy_equation {M N : B.Module} {c d : M ⟶ N}
    (w : gradedHom M N (-1)) (h : HomotopyEquation c d w) :
    HomotopyEquation (liftMap.{u,v,0,t} c) (liftMap.{u,v,0,t} d)
      (DG.CoefficientLift.gradedEquiv.{u,v,0,t} M N (-1) w) := by
  intro x i z
  apply ULift.ext
  exact h x i z.down

private theorem iso_inv_at {C : CommDGAlgebra.{u,v} k} {L M : C.Module} (e : L ≅ M)
    (n : ℤ) (x : term L n) :
    (e.inv.app ()).f n ((e.hom.app ()).f n x) = x :=
  CategoryTheory.congr_fun
    (congrArg (fun f : L ⟶ L => (f.app ()).f n) e.hom_inv_id) x

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem comparisonEnlargement : ComparisonEnlargement.{u,v,t} := by
  intro k _ _ A B b R S T T' U V
  constructor
  · intro f c h i j n e x a
    change (V.cotangentIso.hom.app ()).f n
      ((((liftMap.{u,v,0,t} c).app ()).f n)
        ((U.cotangentIso.inv.app ()).f n
          (T'.tmul U.model.augmentation (N := regular (liftCDGA.{u,v,t} B).toCommDGAlgebra)
            i j n e (value U.differentials.symbol i i (add_zero i) x) a))) = _
    change ULift.{t} (R.algebra.complex.X i) at x
    change ULift.{t} (B.complex.X j) at a
    obtain ⟨x⟩ := x
    obtain ⟨a⟩ := a
    rw [← U.symbol i x, ← U.tensor i j n e, iso_inv_at]
    change (V.cotangentIso.hom.app ()).f n
      (ULift.up ((c.app ()).f n
        (T.tmul R.augmentation (N := regular B.toCommDGAlgebra) i j n e
          (value R.differentials.symbol i i (add_zero i) x) a))) = _
    rw [h i j n e x a, V.tensor i j n e, V.symbol]
    rfl
  · intro c d w h
    let B' := (liftCDGA.{u,v,t} B).toCommDGAlgebra
    let w' := DG.CoefficientLift.gradedEquiv.{u,v,0,t} (R.module T) (S.module T) (-1) w
    let H := prePostHomotopy (C := B') U.cotangentIso.inv w' V.cotangentIso.hom
    refine ⟨H, ?_, fun _ _ _ _ => rfl⟩
    have hw' := upHomotopy_equation.{u,v,t} (B := B) w h
    exact prePostHomotopy_equation (C := B') U.cotangentIso.inv w'
      V.cotangentIso.hom hw'

set_option backward.isDefEq.respectTransparency false in
theorem localizedEnlargement : LocalizedEnlargement.{u,v,t} := by
  intro k _ _ A B b T T' h h'
  letI := homotopyCategory (oneObject B) h
  letI := homotopyCategory (oneObject (liftCDGA.{u,v,t} B)) h'
  letI := derivedCategoryInstance (oneObject B) h
  letI := derivedCategoryInstance (oneObject (liftCDGA.{u,v,t} B)) h'
  obtain ⟨⟨D, hD, _, _⟩, _⟩ :=
    DG.DerivedCoefficientLift.nativeDerivedCoefficientTransition.{u,v,0,t} (oneObject B) h h'
  refine ⟨D, hD, ?_⟩
  intro U
  let Q' := quotient (oneObject (liftCDGA.{u,v,t} B)) h'
  let K' := RightDGModule.toHomotopyCategory (oneObject (liftCDGA.{u,v,t} B))
  let I (R : Model b) : D.D.obj (localizedModel h R T) ≅ localizedModel h' (U R).model T' :=
    D.representedIso (R.module T) ≪≫ Q'.mapIso (K'.mapIso (U R).cotangentIso)
  refine ⟨I, fun _ => rfl, ?_⟩
  intro R S c
  have hnat := represented_naturality D (moduleClass h c)
  rw [classMap_strict] at hnat
  change D.D.map (localizedComparison h c) ≫ (D.representedIso (S.module T)).hom =
    (D.representedIso (R.module T)).hom ≫ Q'.map (moduleClass h' (liftMap.{u,v,0,t} c)) at hnat
  change D.D.map (localizedComparison h c) ≫
      ((D.representedIso (S.module T)).hom ≫ Q'.map (moduleClass h' (U S).cotangentIso.hom)) =
    ((D.representedIso (R.module T)).hom ≫ Q'.map (moduleClass h' (U R).cotangentIso.hom)) ≫
      Q'.map (moduleClass h' ((U R).map (U S) c))
  rw [← Category.assoc, hnat, Category.assoc, Category.assoc,
    ← Q'.map_comp, ← Q'.map_comp]
  have hc₁ := moduleClass_comp (B := liftCDGA.{u,v,t} B) h'
    (liftMap.{u,v,0,t} c) (U S).cotangentIso.hom
  have hc₂ := moduleClass_comp (B := liftCDGA.{u,v,t} B) h'
    (U R).cotangentIso.hom ((U R).map (U S) c)
  rw [← hc₁, ← hc₂]
  have he : (U R).cotangentIso.hom ≫ (U R).map (U S) c =
      liftMap.{u,v,0,t} c ≫ (U S).cotangentIso.hom :=
    Iso.hom_inv_id_assoc _ _
  rw [he]

end Coefficients

section Presentations

open Semifree
open scoped DirectSum

variable {k : Type u} [Field k] [CharZero k]

private abbrev liftedIndex (V : Variables.{v}) : V.Index ≃ (liftVariables.{v,t} V).Index :=
  Equiv.ulift.symm

private def liftedExponent (V : Variables.{v}) : V.Exponent ≃+ (liftVariables.{v,t} V).Exponent :=
  Finsupp.domCongr (liftedIndex V)

omit [CharZero k] in
private theorem liftedWeight (V : Variables.{v}) (m : V.Exponent) :
    (liftVariables.{v,t} V).weight (liftedExponent V m) = V.weight m := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | single x n =>
    change (liftVariables.{v,t} V).weight
      (Finsupp.equivMapDomain (liftedIndex V) (Finsupp.single x n)) =
        V.weight (Finsupp.single x n)
    rw [Finsupp.equivMapDomain_single, Variables.weight, Variables.weight,
      Finsupp.weight_single, Finsupp.weight_single]
    rfl

private def liftedMonomial (V : Variables.{v}) : V.Monomial ≃ (liftVariables.{v,t} V).Monomial :=
  (liftedExponent V).toEquiv.subtypeEquiv (by
    intro m
    constructor
    · intro h z hz
      exact h z.down hz
    · intro h z hz
      exact h (ULift.up z) hz)

private def polynomialCoordinates (A : NonpositiveCDGA.{u,v} k) (V : Variables.{v}) (i : ℤ) :
    Polynomial A V i ≃ₗ[k] Polynomial (liftCDGA.{u,v,t} A) (liftVariables.{v,t} V) i := by
  classical
  refine (DirectSum.lequivCongrLeft k (liftedMonomial V)).trans
    (DirectSum.congrLinearEquiv fun m => ?_)
  let n := (liftedMonomial V).symm m
  have hm : (liftedMonomial V) n = m := (liftedMonomial V).apply_symm_apply m
  have e : i - V.weight n.val = i - (liftVariables.{v,t} V).weight m.val :=
    congrArg (i - ·) (by rw [← hm]; exact (liftedWeight V n.val).symm)
  change A.complex.X (i - V.weight n.val) ≃ₗ[k]
    ULift.{t} (A.complex.X (i - (liftVariables.{v,t} V).weight m.val))
  exact (eqToIso (congrArg A.complex.X e)).toLinearEquiv.trans ULift.moduleEquiv.symm

/-- Transport the operations of a graded algebra to an equivalent family of
coefficient modules, with the zero cochain differential. -/
private def gradedAlgebraOn {C : CommDGAlgebra.{u,max v t} k}
    (X : ℤ → ModuleCat.{v} k) (E : ∀ i, X i ≃ₗ[k] C.complex.X i) :
    CommDGAlgebra.{u,v} k where
  toDGAlgebra :=
    { hom := fun _ _ => { X := X, d := fun _ _ => 0 }
      comp := fun i j n e =>
        ((C.mul i j n e).compl₁₂ (E i).toLinearMap (E j).toLinearMap).compr₂
          (E n).symm.toLinearMap
      id := fun _ => (E 0).symm C.one
      d_id := by intros; rfl
      id_comp := by
        intros
        simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply, C.toDGAlgebra.id_comp, LinearEquiv.symm_apply_apply]
      comp_id := by
        intros
        simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply, C.toDGAlgebra.comp_id, LinearEquiv.symm_apply_apply]
      assoc := by
        intros
        simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply, C.toDGAlgebra.assoc]
      leibniz := by
        intros
        simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero] }
  graded_comm := by
    intro i j n e x y
    change (E n).symm (C.mul i j n e (E i x) (E j y)) =
      (i*j).negOnePow • (E n).symm (C.mul j i n _ (E j y) (E i x))
    rw [C.graded_comm, Units.smul_def, map_zsmul]
    rfl

private theorem gradedAlgebraOn_mul {C : CommDGAlgebra.{u,max v t} k}
    (X : ℤ → ModuleCat.{v} k) (E : ∀ i, X i ≃ₗ[k] C.complex.X i)
    (i j n : ℤ) (e : i+j=n) (x : X i) (y : X j) :
    E n ((gradedAlgebraOn X E).mul i j n e x y) = C.mul i j n e (E i x) (E j y) :=
  (E n).apply_symm_apply _

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
/-- Use the polynomial universal property in both coefficient universes.
The initial reindexing isomorphism supplies a small carrier for the
enlarged polynomial algebra. The resulting multiplicative comparison
preserves the variables and their support. -/
theorem presentationEnlargement : PresentationEnlargement.{u,v,t} := by
  classical
  intro k _ _ A P f V E
  let A' := liftCDGA.{u,v,t} A
  let P' := liftCDGA.{u,v,t} P
  let W := liftVariables.{v,t} V
  let F := cdgaLift.{u,v,t} k
  change ∃ E' : StagedPresentation A' W (F.map f), _
  let C := (polynomialGradedAlgebra A' W).toCommDGAlgebra
  let X (i : ℤ) := ModuleCat.of k (Polynomial A V i)
  let J (i : ℤ) : X i ≃ₗ[k] C.complex.X i := polynomialCoordinates A V i
  let C₀ := gradedAlgebraOn X J
  let b₀ (i : ℤ) : A.complex.X i →ₗ[k] C₀.complex.X i :=
    (J i).symm.toLinearMap.comp
      ((coefficient A' W i).comp ULift.moduleEquiv.symm.toLinearMap)
  let x₀ (x : V.Index) : C₀.complex.X (V.degree x) :=
    (J (V.degree x)).symm (variableTerm A' W (ULift.up x))
  have hb₀ : b₀ 0 A.one = C₀.one := rfl
  have hm₀ (i j n : ℤ) (h : i+j=n) (a : A.complex.X i) (b : A.complex.X j) :
      b₀ n (A.mul i j n h a b) = C₀.mul i j n h (b₀ i a) (b₀ j b) := by
    apply (J n).injective
    rw [show J n (C₀.mul i j n h (b₀ i a) (b₀ j b)) = _ from gradedAlgebraOn_mul X J
      i j n h (b₀ i a) (b₀ j b)]
    change J n ((J n).symm (coefficient A' W n (ULift.up (A.mul i j n h a b)))) =
      polynomialMul A' W i j n h (J i ((J i).symm (coefficient A' W i (ULift.up a))))
        (J j ((J j).symm (coefficient A' W j (ULift.up b))))
    simp only [LinearEquiv.apply_symm_apply, polynomialMul_coefficient]
    rfl
  obtain ⟨G₀⟩ := gradedUniversalProperty A V C₀ b₀ hb₀ hm₀ x₀
  let g (i : ℤ) : Polynomial A V i →ₗ[k] Polynomial A' W i :=
    (J i).toLinearMap.comp (G₀.default.component i)
  have gb (i : ℤ) (a : A.complex.X i) :
      g i (coefficient A V i a) = coefficient A' W i (ULift.up a) := by
    change J i (G₀.default.component i (coefficient A V i a)) = _
    rw [G₀.default.map_base]
    exact (J i).apply_symm_apply _
  have gx (x : V.Index) :
      g (V.degree x) (variableTerm A V x) = variableTerm A' W (ULift.up x) := by
    change J _ (G₀.default.component _ (variableTerm A V x)) = _
    rw [G₀.default.map_var]
    exact (J _).apply_symm_apply _
  have gm (i j n : ℤ) (h : i+j=n) (a : Polynomial A V i) (b : Polynomial A V j) :
      g n (polynomialMul A V i j n h a b) = polynomialMul A' W i j n h (g i a) (g j b) := by
    change J n (G₀.default.component n (polynomialMul A V i j n h a b)) = _
    rw [G₀.default.map_mul]
    exact gradedAlgebraOn_mul X J i j n h _ _
  let f' (i : ℤ) : A'.complex.X i →ₗ[k] P'.complex.X i :=
    ((F.map f).chainMap.f i).hom
  let x' (x : W.Index) : P'.complex.X (W.degree x) :=
    ULift.up (E.component _ (variableTerm A V x.down))
  obtain ⟨G'⟩ := gradedUniversalProperty A' W P'.toCommDGAlgebra f' (F.map f).map_one
    (F.map f).map_mul x'
  let G := G'.default
  let l (i : ℤ) : Polynomial A' W i →ₗ[k] P'.complex.X i := G.component i
  let r (i : ℤ) : P'.complex.X i →ₗ[k] Polynomial A' W i :=
    (g i).comp ((E.component i).symm.toLinearMap.comp ULift.moduleEquiv.toLinearMap)
  have forward (i : ℤ) (a : Polynomial A V i) :
      l i (g i a) = ULift.up (E.component i a) := by
    induction i, a using polynomial_generated A V with
    | zero => simp only [map_zero]; rfl
    | add i a b ha hb => rw [map_add, map_add, ha, hb, map_add]; rfl
    | sign i z a ha =>
      simp only [Units.smul_def, map_zsmul, ha]
      rfl
    | base i a =>
      rw [gb]
      exact (G.map_base i (ULift.up a)).trans (congrArg ULift.up (E.map_base i a).symm)
    | var x =>
      rw [gx]
      exact G.map_var (ULift.up x)
    | mul i j n h a b ha hb =>
      rw [gm, show l n (polynomialMul A' W i j n h (g i a) (g j b)) = _ from
        G.map_mul i j n h (g i a) (g j b), ha, hb, E.map_mul]
      rfl
  have hrb (i : ℤ) (a : A.complex.X i) :
      r i (ULift.up (f.chainMap.f i a)) = coefficient A' W i (ULift.up a) := by
    change g i ((E.component i).symm (f.chainMap.f i a)) = _
    rw [← E.map_base, LinearEquiv.symm_apply_apply, gb]
  have hrx (x : V.Index) :
      r (V.degree x) (x' (ULift.up x)) = variableTerm A' W (ULift.up x) := by
    change g _ ((E.component _).symm (E.component _ (variableTerm A V x))) = _
    rw [LinearEquiv.symm_apply_apply, gx]
  have hrm (i j n : ℤ) (h : i+j=n) (a : P'.complex.X i) (b : P'.complex.X j) :
      r n (P'.mul i j n h a b) = polynomialMul A' W i j n h (r i a) (r j b) := by
    obtain ⟨a₀, ha₀⟩ := (E.component i).surjective a.down
    obtain ⟨b₀, hb₀⟩ := (E.component j).surjective b.down
    change g n ((E.component n).symm (P.mul i j n h a.down b.down)) =
      polynomialMul A' W i j n h (g i ((E.component i).symm a.down))
        (g j ((E.component j).symm b.down))
    rw [← ha₀, ← hb₀, ← E.map_mul, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, gm]
  have backward (i : ℤ) (a : Polynomial A' W i) : r i (l i a) = a := by
    induction i, a using polynomial_generated A' W with
    | zero => simp
    | add i a b ha hb => rw [map_add, map_add, ha, hb]
    | sign i z a ha => simp only [Units.smul_def, map_zsmul, ha]
    | base i a =>
      obtain ⟨a⟩ := a
      rw [show l i (coefficient A' W i (ULift.up a)) = f' i (ULift.up a) from G.map_base _ _]
      exact hrb i a
    | var x =>
      obtain ⟨x⟩ := x
      rw [show l _ (variableTerm A' W (ULift.up x)) = x' (ULift.up x) from G.map_var _]
      exact hrx x
    | mul i j n h a b ha hb =>
      rw [show l n (polynomialMul A' W i j n h a b) = _ from G.map_mul i j n h a b,
        hrm, ha, hb]
  let E₁ (i : ℤ) : Polynomial A' W i ≃ₗ[k] P'.complex.X i :=
    LinearEquiv.ofLinearMap (l i) (r i)
      (LinearMap.ext fun z => by
        change l i (g i ((E.component i).symm z.down)) = z
        rw [forward, LinearEquiv.apply_symm_apply]
        exact ULift.ext rfl)
      (LinearMap.ext (backward i))
  let S : Stages W :=
    { Stage := ULift.{t} E.stages.Stage
      order := LinearOrder.lift' ULift.down (fun _ _ => ULift.ext)
      wellFounded := InvImage.wf ULift.down E.stages.wellFounded
      stage := fun x => ULift.up (E.stages.stage x.down) }
  have preserveSupport (D : Set V.Index) (i : ℤ) (a : Polynomial A V i)
      (ha : UsesOnly A V D a) : UsesOnly A' W {x | x.down ∈ D} (g i a) := by
    refine polynomial_generated_on A V D (fun i a => UsesOnly A' W {x | x.down ∈ D} (g i a))
      ?_ ?_ ?_ ?_ ?_ ?_ i a ha
    · intro i
      rw [map_zero]
      exact UsesOnly.zero _
    · intro i p q hp hq
      rw [map_add]
      exact hp.add hq
    · intro i s p hp
      simp only [Units.smul_def, map_zsmul]
      exact hp.sign s
    · intro i a
      rw [gb]
      exact coefficient_usesOnly (A := A') (V := W) i _
    · intro x hx
      rw [gx]
      exact variable_usesOnly (A := A') (V := W) _ hx
    · intro i j n h p q hp hq
      rw [gm]
      exact hp.mul h hq
  let E' : StagedPresentation A' W (F.map f) :=
    { component := E₁
      map_one := (G.map_base 0 A'.one).trans (F.map f).map_one
      map_mul := G.map_mul
      map_base := G.map_base
      stages := S
      earlier := by
        rintro ⟨x⟩
        change UsesOnly A' W {y | y.down ∈ E.stages.before (E.stages.stage x)}
          (r (V.degree x+1) (P'.complex.d (V.degree x) (V.degree x+1)
            (l (V.degree x) (variableTerm A' W (ULift.up x)))))
        rw [show l (V.degree x) (variableTerm A' W (ULift.up x)) = x' (ULift.up x) from
          G.map_var (ULift.up x)]
        exact preserveSupport _ _ _ (E.earlier x) }
  exact ⟨E', fun x => G.map_var (ULift.up x), Equiv.ulift, fun _ => rfl, fun _ _ => Iff.rfl⟩

end Presentations

section LiftedBasis

open Semifree (Variables StagedPresentation variableTerm)
open SemifreeDifferentials
  (Coefficients IsGradedBasis multiples generator graded_basis differential_symbol semifreeAfterBaseChange)
open Specs.DerivedFormalization.DG.CoefficientLift (liftModule liftMap)
open private single freeModule freeGenerator multiples_act multiples_single multiples_freeGenerator
  gradedOfDegrees gradedOfDegrees_apply postDerivation postDerivation_apply derivation_eq_on_polynomials
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeDifferentials
open private isoOfDegreewiseBijective isoOfDegreewiseBijective_hom from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellLift
open private scalarExtend scalarExtend_pure from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

variable {k : Type u} [Field k] [CharZero k]

private def upBasisCoefficients (P : NonpositiveCDGA.{u,v} k) (V : Variables.{v}) (n : ℤ) :
    Coefficients P.toCommDGAlgebra V n ≃ₗ[k]
      Coefficients (liftCDGA.{u,v,t} P).toCommDGAlgebra (liftVariables.{v,t} V) n := by
  classical
  exact (DirectSum.lequivCongrLeft k (liftedIndex V)).trans
    (DirectSum.congrLinearEquiv fun _ => ULift.moduleEquiv.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem upBasisCoefficients_single (P : NonpositiveCDGA.{u,v} k) (V : Variables.{v})
    (n : ℤ) (x : V.Index) (z : P.complex.X (n + -V.degree x)) :
    upBasisCoefficients.{u,v,t} P V n (single P.toCommDGAlgebra V n x z) =
      single (liftCDGA.{u,v,t} P).toCommDGAlgebra (liftVariables.{v,t} V) n (ULift.up x)
        (ULift.up z) := by
  classical
  let W := liftVariables.{v,t} V
  let Q := liftCDGA.{u,v,t} P
  letI : DecidableEq W.Index := Classical.decEq _
  let U (y : W.Index) :
      P.complex.X (n + -V.degree y.down) ≃ₗ[k] Q.complex.X (n + -W.degree y) :=
    ULift.moduleEquiv.symm
  have h₁ :
      (DirectSum.lequivCongrLeft k (liftedIndex.{v,t} V))
          (single P.toCommDGAlgebra V n x z) =
        DirectSum.lof k W.Index (fun y => P.complex.X (n + -V.degree y.down)) (ULift.up x) z :=
    DirectSum.lequivCongrLeft_lof k (M := fun y : V.Index => (P.complex.X (n + -V.degree y) : Type v))
      (e := liftedIndex.{v,t} V) (i := x) (k := ULift.up x) rfl z z rfl
  have h₂ : (DirectSum.congrLinearEquiv U)
      (DirectSum.lof k W.Index (fun y => P.complex.X (n + -V.degree y.down)) (ULift.up x) z) =
      single Q.toCommDGAlgebra W n (ULift.up x) (ULift.up z) := by
    change (DirectSum.congrLinearEquiv U).toLinearMap _ = _
    rw [DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_lof]
    rfl
  exact (congrArg (DirectSum.congrLinearEquiv U) h₁).trans h₂

set_option backward.isDefEq.respectTransparency false in
private theorem isGradedBasis_up {P : NonpositiveCDGA.{u,v} k} {V : Variables.{v}}
    {M : P.Module} {g : ∀ x, term M (V.degree x)} (h : IsGradedBasis g) :
    IsGradedBasis (B := (liftCDGA.{u,v,t} P).toCommDGAlgebra) (V := liftVariables.{v,t} V)
      (M := liftModule.{u,v,0,t} M) (fun x => ULift.up (g x.down)) := by
  classical
  intro n
  let E := upBasisCoefficients.{u,v,t} P V n
  let M' : (liftCDGA.{u,v,t} P).Module := liftModule.{u,v,0,t} M
  let g' : ∀ x : (liftVariables.{v,t} V).Index, term (A := (liftCDGA.{u,v,t} P).toCommDGAlgebra) M' ((liftVariables.{v,t} V).degree x) :=
    fun x => ULift.up (g x.down)
  let U : term M n ≃ₗ[k] term M' n := ULift.moduleEquiv.symm
  have he : (multiples g' n).comp E.toLinearMap = U.toLinearMap.comp (multiples g n) := by
    apply DirectSum.linearMap_ext
    intro x
    apply LinearMap.ext
    intro z
    change multiples g' n (E (single P.toCommDGAlgebra V n x z)) =
      U (multiples g n (single P.toCommDGAlgebra V n x z))
    rw [show E (single P.toCommDGAlgebra V n x z) = _ from upBasisCoefficients_single P V n x z,
      multiples_single, multiples_single]
    rfl
  apply (Function.Bijective.of_comp_iff _ E.bijective).mp
  change Function.Bijective (multiples g' n ∘ E)
  rw [show multiples g' n ∘ E = U ∘ multiples g n from funext (LinearMap.congr_fun he)]
  exact U.bijective.comp (h n)

section CompareBasis

variable {P : CommDGAlgebra.{u,v} k} {V : Variables.{v}} {M N : P.Module}
  {g : ∀ x, term M (V.degree x)} {g' : ∀ x, term N (V.degree x)}

private def basisTermIso (h : IsGradedBasis g) (h' : IsGradedBasis g') (n : ℤ) :
    term M n ≃ₗ[k] term N n :=
  (LinearEquiv.ofBijective (multiples g n) (h n)).symm.trans
    (LinearEquiv.ofBijective (multiples g' n) (h' n))

private theorem basisTermIso_multiples (h : IsGradedBasis g) (h' : IsGradedBasis g')
    (n : ℤ) (z : Coefficients P V n) :
    basisTermIso h h' n (multiples g n z) = multiples g' n z := by
  simp [basisTermIso]

private theorem basisTermIso_gen (h : IsGradedBasis g) (h' : IsGradedBasis g') (x : V.Index) :
    basisTermIso h h' (V.degree x) (g x) = g' x := by
  rw [← multiples_freeGenerator g x, basisTermIso_multiples, multiples_freeGenerator]

private theorem basisTermIso_action (h : IsGradedBasis g) (h' : IsGradedBasis g')
    (i j n : ℤ) (e : i+j=n) (z : term M i) (a : P.complex.X j) :
    basisTermIso h h' n (act M i j n e z a) =
      act N i j n e (basisTermIso h h' i z) a := by
  obtain ⟨w, rfl⟩ := (h i).surjective z
  rw [← multiples_act, basisTermIso_multiples, multiples_act, basisTermIso_multiples]

private theorem commutes_on_basis (h : IsGradedBasis g)
    (L : ∀ n, term M n →ₗ[k] term N n)
    (hact : ∀ (i j n : ℤ) (e : i+j=n) (z : term M i) (a : P.complex.X j),
      L n (act M i j n e z a) = act N i j n e (L i z) a)
    (hgen : ∀ x : V.Index, L (V.degree x+1) ((M.complex ()).d (V.degree x) (V.degree x+1) (g x)) =
      (N.complex ()).d (V.degree x) (V.degree x+1) (L (V.degree x) (g x)))
    (n : ℤ) (z : term M n) :
    L (n+1) ((M.complex ()).d n (n+1) z) = (N.complex ()).d n (n+1) (L n z) := by
  classical
  obtain ⟨w, rfl⟩ := (h n).surjective z
  suffices he : ((L (n+1)).comp ((M.complex ()).d n (n+1)).hom).comp (multiples g n) =
    (((N.complex ()).d n (n+1)).hom.comp (L n)).comp (multiples g n) from
    LinearMap.congr_fun he w
  apply DirectSum.linearMap_ext
  intro x
  apply LinearMap.ext
  intro a
  change L (n+1) ((M.complex ()).d n (n+1) (multiples g n (single P V n x a))) =
    (N.complex ()).d n (n+1) (L n (multiples g n (single P V n x a)))
  rw [multiples_single, M.leibniz (a := ()) (b := ()), hact, N.leibniz (a := ()) (b := ())]
  simp only [map_add, Units.smul_def, map_zsmul, hact, hgen]

private theorem bijective_of_basis (h : IsGradedBasis g) (h' : IsGradedBasis g')
    (c : M ⟶ N) (hc : ∀ x : V.Index, (c.app ()).f (V.degree x) (g x) = g' x)
    (n : ℤ) : Function.Bijective ((c.app ()).f n) := by
  classical
  have he : ((c.app ()).f n).hom.comp (multiples g n) = multiples g' n := by
    apply DirectSum.linearMap_ext
    intro x
    apply LinearMap.ext
    intro a
    change (c.app ()).f n (multiples g n (single P V n x a)) =
      multiples g' n (single P V n x a)
    rw [multiples_single, multiples_single, c.comm_act, hc]
  apply (Function.Bijective.of_comp_iff _ (h n)).mp
  change Function.Bijective (((c.app ()).f n).hom ∘ multiples g n)
  rw [show ((c.app ()).f n).hom ∘ multiples g n = multiples g' n from
    funext (LinearMap.congr_fun he)]
  exact h' n

end CompareBasis

section LiftDifferentials

variable {A P : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} {V : Variables.{v}}

private abbrev enlargedMap (f : A ⟶ P) :
    (liftCDGA.{u,v,t} A).toCommDGAlgebra ⟶ (liftCDGA.{u,v,t} P).toCommDGAlgebra :=
  (cdgaLift.{u,v,t} k).map f

set_option backward.isDefEq.respectTransparency false in
private def liftDifferentialSymbol
    (O : DifferentialModel (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)) :
    Kahler.Derivation (enlargedMap.{u,v,t} f) (liftModule.{u,v,0,t} O.module) 0 :=
  ⟨Cochain.mk (fun i j h => (ModuleCat.uliftFunctor.{t,v} k).map (value O.symbol i j h)), by
    constructor
    · intro i j h a
      cases (show i = j by omega)
      rw [Cochain.mk_v]
      apply ULift.ext
      exact O.symbol.property.relative i i (add_zero i) a.down
    · intro i j n ir jr nr e hi hj hn x y
      cases (show i = ir by omega)
      cases (show j = jr by omega)
      cases (show n = nr by omega)
      simp only [Cochain.mk_v]
      apply ULift.ext
      exact O.symbol.property.leibniz i j n i j n e (add_zero i) (add_zero j)
        (add_zero n) x.down y.down⟩

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem differentialEnlargement (E : StagedPresentation A V f)
    (E' : StagedPresentation (liftCDGA.{u,v,t} A) (liftVariables.{v,t} V) (enlargedMap f))
    (hvar : ∀ x : V.Index,
      E'.component (V.degree x)
          (variableTerm (liftCDGA.{u,v,t} A) (liftVariables.{v,t} V) (ULift.up x)) =
        ULift.up (E.component (V.degree x) (variableTerm A V x)))
    (O : DifferentialModel (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra))
    (O' : DifferentialModel (enlargedMap.{u,v,t} f)) :
    ∃ I : liftModule.{u,v,0,t} O.module ≅ O'.module, ∀ (i : ℤ) (x : P.complex.X i),
      (I.hom.app ()).f i (ULift.up (value O.symbol i i (add_zero i) x)) =
        value O'.symbol i i (add_zero i) (ULift.up x) := by
  let W := liftVariables.{v,t} V
  let P' := liftCDGA.{u,v,t} P
  let M : P'.Module := liftModule.{u,v,0,t} O.module
  let N : P'.Module := O'.module
  let g : ∀ x : W.Index, term (A := P'.toCommDGAlgebra) M (W.degree x) := fun x => ULift.up (generator E O x.down)
  let g' := generator E' O'
  have h : IsGradedBasis g := isGradedBasis_up (graded_basis E O)
  have h' : IsGradedBasis g' := graded_basis E' O'
  let e := basisTermIso h h'
  let L (i : ℤ) := (e i).toLinearMap
  have ha (i j n : ℤ) (p : i + j = n)
      (z : term (A := P'.toCommDGAlgebra) M i) (a : P'.complex.X j) :
      L n (act (A := P'.toCommDGAlgebra) M i j n p z a) =
        act (A := P'.toCommDGAlgebra) N i j n p (L i z) a :=
    basisTermIso_action h h' i j n p z a
  let F := gradedOfDegrees (B := P'.toCommDGAlgebra) (M := M) (N := N) L ha
  let U := liftDifferentialSymbol.{u,v,t} O
  let D := postDerivation F U
  have eqGen (x : W.Index) :
      value D (W.degree x) (W.degree x) (add_zero _)
        (E'.component _ (variableTerm (liftCDGA.{u,v,t} A) W x)) = g' x := by
    obtain ⟨x⟩ := x
    rw [postDerivation_apply, gradedOfDegrees_apply, hvar]
    change e (V.degree x) (g (ULift.up x)) = g' (ULift.up x)
    exact basisTermIso_gen h h' _
  have hsymbol (i : ℤ) (x : P.complex.X i) :
      L i (ULift.up (value O.symbol i i (add_zero i) x)) =
        value O'.symbol i i (add_zero i) (ULift.up x) := by
    have eq := derivation_eq_on_polynomials E' (D := D) (D' := O'.symbol) eqGen i
      (ULift.up x)
    rw [postDerivation_apply, gradedOfDegrees_apply] at eq
    simp only [U, liftDifferentialSymbol, value, Cochain.mk_v] at eq
    exact eq
  have hdGen (x : W.Index) :
      L (W.degree x+1) ((M.complex ()).d (W.degree x) (W.degree x+1) (g x)) =
        (N.complex ()).d (W.degree x) (W.degree x+1) (L (W.degree x) (g x)) := by
    obtain ⟨x⟩ := x
    have eg : L (V.degree x) (g (ULift.up x)) = g' (ULift.up x) := basisTermIso_gen h h' _
    rw [eg]
    change L (V.degree x+1) (ULift.up (((O.module.complex ()).d (V.degree x) (V.degree x+1))
        (value O.symbol (V.degree x) (V.degree x) (add_zero _)
          (E.component _ (variableTerm A V x))))) =
      (O'.module.complex ()).d (V.degree x) (V.degree x+1)
        (value O'.symbol (V.degree x) (V.degree x) (add_zero _)
          (E'.component _ (variableTerm (liftCDGA.{u,v,t} A) W (ULift.up x))))
    rw [differential_symbol O, differential_symbol O', hvar]
    exact hsymbol _ _
  let I : M ≅ N := DG.CoefficientLift.isoOfComponents
    (fun _ i => e i)
    (by rintro ⟨⟩ i z; exact commutes_on_basis h L ha hdGen i z)
    (by rintro ⟨⟩ ⟨⟩ i j n h₀ z a; exact ha i j n h₀ z a)
  exact ⟨I, hsymbol⟩

end LiftDifferentials

section LiftCotangent

variable {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}

set_option backward.isDefEq.respectTransparency false in
private def liftIntoRestriction {P : NonpositiveCDGA.{u,v} k} (p : P ⟶ B)
    {M : P.Module} {N : B.Module} (f : M ⟶ restrict p N) :
    liftModule.{u,v,0,t} M ⟶ restrict (enlargedMap.{u,v,t} p) (liftModule.{u,v,0,t} N) :=
  Tensor.homOfDegrees (A := (liftCDGA.{u,v,t} P).toCommDGAlgebra)
    (M := liftModule.{u,v,0,t} M)
    (N := restrict (enlargedMap.{u,v,t} p) (liftModule.{u,v,0,t} N))
    (fun n => ULift.moduleEquiv.symm.toLinearMap.comp (((f.app ()).f n).hom.comp
      ULift.moduleEquiv.toLinearMap))
    (by
      intro n z
      apply ULift.ext
      change (N.complex ()).d n (n+1) ((f.app ()).f n z.down) =
        (f.app ()).f (n+1) ((M.complex ()).d n (n+1) z.down)
      simpa only [ModuleCat.comp_apply] using
        CategoryTheory.congr_fun ((f.app ()).comm n (n+1)) z.down)
    (by
      intro i j n e z a
      apply ULift.ext
      exact f.comm_act i j n e z.down a.down)

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Identify the two modules of differentials by their variable bases.
The upper scalar-extension map to the lifted model is an isomorphism
because it sends the scalar-extended basis to the lifted basis. -/
theorem modelEnlargement : ModelEnlargement.{u,v,t} := by
  intro k _ _ A B b R T T' Tform T'form
  let A' := liftCDGA.{u,v,t} A
  let B' := liftCDGA.{u,v,t} B
  let P' := liftCDGA.{u,v,t} R.algebra
  let a' := enlargedMap.{u,v,t} R.base
  let p : R.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra := R.augmentation
  let p' := enlargedMap.{u,v,t} R.augmentation
  let hp := Tform p (regular B.toCommDGAlgebra)
  let hp' := T'form p' (regular B'.toCommDGAlgebra)
  obtain ⟨V, ⟨E⟩⟩ := R.semifree
  obtain ⟨E', hvar, _⟩ := presentationEnlargement.{u,v,t} R.base V E
  let W := liftVariables.{v,t} V
  let O := R.differentials
  let O' := Kahler.model a'
  obtain ⟨I, hI⟩ := differentialEnlargement E E' hvar O O'
  let M := R.module T
  let M' := (T'.baseChange p').obj O'.module
  let L : O'.module ⟶ restrict p' (liftModule.{u,v,0,t} M) :=
    I.inv ≫ liftIntoRestriction R.augmentation (unitTensor p O.module hp)
  let c : M' ⟶ liftModule.{u,v,0,t} M := scalarExtend T' hp' L
  have hc (i j n : ℤ) (e : i+j=n) (x : term O.module i) (a : B.complex.X j) :
      (c.app ()).f n
        (T'.tmul p' (N := regular B'.toCommDGAlgebra) i j n e
          ((I.hom.app ()).f i (ULift.up x)) (ULift.up a)) =
      ULift.up (T.tmul p (N := regular B.toCommDGAlgebra) i j n e x a) := by
    rw [show (c.app ()).f n _ = _ from scalarExtend_pure T' hp' L i j n e _ _]
    change act (A := B'.toCommDGAlgebra) (liftModule.{u,v,0,t} M) i j n e
      (((liftIntoRestriction R.augmentation (unitTensor p O.module hp)).app ()).f i
        ((I.inv.app ()).f i ((I.hom.app ()).f i (ULift.up x)))) (ULift.up a) = _
    rw [iso_inv_at (C := P'.toCommDGAlgebra) I]
    apply ULift.ext
    exact unit_tensor_action T hp i j n e x a
  obtain ⟨_, hM, _, _, _⟩ := semifreeAfterBaseChange T E O p hp
  obtain ⟨_, hM', _, _, _⟩ := semifreeAfterBaseChange T' E' O' p' hp'
  let g (x : V.Index) : term M (V.degree x) :=
    T.tmul p (N := regular B.toCommDGAlgebra) (V.degree x) 0 (V.degree x) (add_zero _)
      (generator E O x) B.one
  let g' (x : W.Index) : term (A := B'.toCommDGAlgebra) M' (W.degree x) :=
    T'.tmul p' (N := regular B'.toCommDGAlgebra) (W.degree x) 0 (W.degree x) (add_zero _)
      (generator E' O' x) B'.one
  have hUp : IsGradedBasis (B := B'.toCommDGAlgebra) (V := W) (M := liftModule.{u,v,0,t} M)
    (fun x => ULift.up (g x.down)) := isGradedBasis_up (P := B) (g := g) hM
  have hcgen (x : W.Index) : (c.app ()).f (W.degree x) (g' x) = ULift.up (g x.down) := by
    obtain ⟨x⟩ := x
    have e : (I.hom.app ()).f (V.degree x) (ULift.up (generator E O x)) =
        generator E' O' (ULift.up x) := by
      unfold generator
      rw [hI]
      exact congrArg (fun z => value O'.symbol (V.degree x) (V.degree x) (add_zero _) z)
        (hvar x).symm
    have he := hc (V.degree x) 0 (V.degree x) (add_zero _) (generator E O x) B.one
    rw [e] at he
    exact he
  have hBij : ∀ (x : (oneObject B').Obj) n, Function.Bijective ((c.app x).f n) := by
    rintro ⟨⟩ n
    exact bijective_of_basis (P := B'.toCommDGAlgebra) (V := W) (g := g') hM' hUp c hcgen n
  let J : M' ≅ liftModule.{u,v,0,t} M := isoOfDegreewiseBijective c hBij
  have hJ : J.hom = c := isoOfDegreewiseBijective_hom c hBij
  refine ⟨{
    semifree := ⟨W, ⟨E'⟩⟩
    surjective := ?_
    quasiIso := ?_
    differentials := O'
    differentialIso := I
    symbol := hI
    cotangentIso := J.symm
    tensor := ?_ }⟩
  · intro i z
    obtain ⟨x, hx⟩ := R.surjective i z.down
    exact ⟨ULift.up x, ULift.ext hx⟩
  · letI : QuasiIso R.augmentation.chainMap := R.quasiIso
    change QuasiIso
      (((ModuleCat.uliftFunctor.{t,v} k).mapHomologicalComplex (ComplexShape.up ℤ)).map
        R.augmentation.chainMap)
    infer_instance
  · intro i j n e x a
    change (J.inv.app ()).f n (ULift.up (T.tmul p (N := regular B.toCommDGAlgebra) i j n e x a)) = _
    rw [← hc i j n e x a, ← hJ]
    exact iso_inv_at (C := B'.toCommDGAlgebra) J n _

end LiftCotangent

end LiftedBasis

end

end DerivedFormalization.Affine.CotangentComplex
