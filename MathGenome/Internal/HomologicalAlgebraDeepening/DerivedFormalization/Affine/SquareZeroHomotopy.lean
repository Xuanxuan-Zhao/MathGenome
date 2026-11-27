import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SquareZeroHomotopy
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SquareZeroMaps
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentModelProperties
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedHom
import Batteries.Tactic.OpenPrivate

open CategoryTheory Opposite

universe u v

namespace DerivedFormalization.Affine.SquareZeroHomotopy

open Specs.DerivedFormalization.Affine.SquareZeroHomotopy
open Specs.DerivedFormalization.Affine.CotangentComplex (Model)
open Specs.DerivedFormalization.Affine.SquareZeroMaps (Cycles IsNonpositive Maps)
open Specs.DerivedFormalization.Affine.PolynomialPath
  (ModulePathModel mapCoefficients derivative transport differential endpoint term)
open PolynomialPath (mapCoefficients_single derivative_single_zero derivative_single_succ
  differential_coordinates transport_refl evaluate_single)
open Specs.DerivedFormalization.Affine.Tensor (act)
open Specs.DerivedFormalization.DG.Basic (classOf boundariesZero cyclesZero)
open Specs.DerivedFormalization.DG.HomComplex (HomotopyEquation)
open RightDGModule
  (GradedHom homComplex strictMap strictCycle homotopyClass strictCycle_strictMap)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}

omit [CharZero k] in
private theorem chain_comm {C E : ModuleCochain.{u,v} k} (f : C ⟶ E)
    (i : ℤ) (x : C.X i) :
    E.d i (i+1) (f.f i x) = f.f (i+1) (C.d i (i+1) x) :=
  by simpa only [ModuleCat.comp_apply] using CategoryTheory.congr_fun (f.comm i (i+1)) x

omit [CharZero k] in
private theorem map_sign {V Y : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup Y] [Module k Y] (f : V →ₗ[k] Y) (s : ℤˣ) (x : V) :
    f (s • x) = s • f x := by
  simp only [Units.smul_def, map_zsmul]

section Interpolation

variable {L M : B.Module} (W : ModulePathModel M)
variable (f₀ f₁ : L ⟶ M) (h : GradedHom L M (-1))

/-- The signed polynomial interpolation in the two path coordinates. -/
private def interpolation (i : ℤ) :
    (L.complex ()).X i →ₗ[k] term (M.complex ()) i :=
  (((Finsupp.lsingle 0).comp (f₀.app () |>.f i |>.hom)) +
    ((Finsupp.lsingle 1).comp ((f₁.app () |>.f i |>.hom) - (f₀.app () |>.f i |>.hom)))).prod
    (-(i.negOnePow • (Finsupp.lsingle 0).comp (h.app () i (i-1) (by omega)).hom))

private theorem interpolation_apply (i : ℤ) (x : (L.complex ()).X i) :
    interpolation f₀ f₁ h i x =
      (Finsupp.single 0 ((f₀.app ()).f i x) +
        Finsupp.single 1 ((f₁.app ()).f i x - (f₀.app ()).f i x),
        -(i.negOnePow • Finsupp.single 0 (h.app () i (i-1) (by omega) x))) :=
  rfl

private theorem interpolation_form (hh : HomotopyEquation f₁ f₀ h)
    (i q : ℤ) (e : i = q) (x : (L.complex ()).X i) :
    mapCoefficients ((M.complex ()).d (i-1) q).hom
        (-(i.negOnePow • Finsupp.single 0 (h.app () i (i-1) (by omega) x))) +
      i.negOnePow • mapCoefficients (transport (M.complex ()) i q e)
        (Finsupp.single 0 ((f₁.app ()).f i x - (f₀.app ()).f i x)) =
    -((i+1).negOnePow • Finsupp.single 0
        (h.app () (i+1) q (by omega) ((L.complex ()).d i (i+1) x))) := by
  subst q
  rw [map_neg, map_sign, mapCoefficients_single, transport_refl,
    PolynomialPath.mapCoefficients_id_apply, hh () i x, Finsupp.single_add,
    smul_add, Int.negOnePow_succ, Units.neg_smul, neg_neg, neg_add_cancel_left]

set_option maxHeartbeats 500000 in
private theorem interpolation_comm (hh : HomotopyEquation f₁ f₀ h)
    (i : ℤ) (x : (L.complex ()).X i) :
    differential (M.complex ()) i (i+1) rfl (interpolation f₀ f₁ h i x) =
      interpolation f₀ f₁ h (i+1) ((L.complex ()).d i (i+1) x) := by
  rw [interpolation_apply, differential_coordinates, interpolation_apply]
  apply Prod.ext
  · simp only [map_add, mapCoefficients_single, map_sub]
    rw [chain_comm (f₀.app ()) i x, chain_comm (f₁.app ()) i x]
  · simp only [map_add, derivative_single_zero, derivative_single_succ, Nat.cast_one, one_smul,
      zero_add]
    exact interpolation_form f₀ f₁ h hh i (i+1-1) (by omega) x

/-- Interpolate closed maps whose difference is the differential of the given homotopy. -/
private def interpolate (hh : HomotopyEquation f₁ f₀ h) : L ⟶ W.obj where
  app a := by
    cases a
    exact CochainComplex.ofHom
      (fun i => ModuleCat.ofHom ((W.coordinates i).symm.toLinearMap.comp (interpolation f₀ f₁ h i)))
      (by
        intro i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply (W.coordinates (i+1)).injective
        change W.coordinates (i+1) ((W.obj.complex ()).d i (i+1)
            ((W.coordinates i).symm (interpolation f₀ f₁ h i x))) =
          W.coordinates (i+1) ((W.coordinates (i+1)).symm
            (interpolation f₀ f₁ h (i+1) ((L.complex ()).d i (i+1) x)))
        rw [W.d_coordinates i (i+1) rfl, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact interpolation_comm f₀ f₁ h hh i x)
  comm_act := by
    intro a b i j n hij x scalar
    cases a
    cases b
    apply (W.coordinates n).injective
    change W.coordinates n ((W.coordinates n).symm
        (interpolation f₀ f₁ h n (act L i j n hij x scalar))) =
      W.coordinates n (act W.obj i j n hij
        ((W.coordinates i).symm (interpolation f₀ f₁ h i x)) scalar)
    rw [W.action_coordinates, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      interpolation_apply, interpolation_apply]
    apply Prod.ext
    · simp only [map_add, mapCoefficients_single, LinearMap.flip_apply, map_sub]
      rw [← f₀.comm_act i j n hij x scalar, ← f₁.comm_act i j n hij x scalar]
    · simp only [map_neg, smul_neg]
      rw [map_sign, mapCoefficients_single, LinearMap.flip_apply, smul_smul,
        ← Int.negOnePow_add, add_comm j i, hij]
      exact congrArg (fun t => -(n.negOnePow • Finsupp.single 0 t))
        (h.comm_act i j n (i-1) (n-1) hij (by omega) (by omega) x scalar)

private theorem interpolate_zero (hh : HomotopyEquation f₁ f₀ h) :
    interpolate W f₀ f₁ h hh ≫ W.evaluation 0 = f₀ := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((W.evaluation 0).app ()).f i
      ((W.coordinates i).symm (interpolation f₀ f₁ h i x)) = _
  rw [W.evaluation_coordinates, LinearEquiv.apply_symm_apply, interpolation_apply]
  simp [endpoint]

private theorem interpolate_one (hh : HomotopyEquation f₁ f₀ h) :
    interpolate W f₀ f₁ h hh ≫ W.evaluation 1 = f₁ := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((W.evaluation 1).app ()).f i
      ((W.coordinates i).symm (interpolation f₀ f₁ h i x)) = _
  rw [W.evaluation_coordinates, LinearEquiv.apply_symm_apply, interpolation_apply]
  simp [endpoint]

end Interpolation

section Integration

variable {L M : B.Module} (W : ModulePathModel M) (f : L ⟶ W.obj)

private def integrate : GradedHom L M (-1) :=
  RightDGModule.GradedHom.mk (fun a i q e => (f.app a).f i ≫ RightDGModule.GradedHom.app W.homotopy a i q e)
    (by
      intro a b i j n ir nr h hi hn x z
      simp only [ModuleCat.comp_apply, f.comm_act, RightDGModule.GradedHom.comm_act W.homotopy i j n ir nr h hi hn])

private theorem integrate_equation :
    HomotopyEquation (f ≫ W.evaluation 1) (f ≫ W.evaluation 0) (integrate W f) := by
  intro a i x
  have hh := W.endpoints_homotopic a i ((f.app a).f i x)
  change ((W.evaluation 1).app a).f i ((f.app a).f i x) -
      ((W.evaluation 0).app a).f i ((f.app a).f i x) = _
  simpa only [integrate, RightDGModule.GradedHom.mk_app, ModuleCat.comp_apply,
    chain_comm (f.app a)] using hh

end Integration

private theorem boundary_iff_class_eq {L M : B.Module} {x y : cyclesZero (homComplex L M)} :
    (∃ h : GradedHom L M (-1), (homComplex L M).d (-1) 0 h = x.val - y.val) ↔
      classOf x = classOf y := by
  rw [Submodule.Quotient.eq]
  change (∃ h : GradedHom L M (-1), (homComplex L M).d (-1) 0 h = (x-y).val) ↔
    x - y ∈ boundariesZero (homComplex L M)
  rw [LinearMap.mem_range]
  exact exists_congr (fun h => ⟨fun he => Subtype.ext he, congrArg Subtype.val⟩)

private theorem boundary_iff_homotopy {L M : B.Module} {x y : cyclesZero (homComplex L M)} :
    (∃ h : GradedHom L M (-1), (homComplex L M).d (-1) 0 h = x.val - y.val) ↔
      ∃ h : GradedHom L M (-1), HomotopyEquation (strictMap x) (strictMap y) h := by
  rw [boundary_iff_class_eq, ← RightDGModule.homotopyCriterion]
  change classOf x = classOf y ↔ classOf (strictCycle (strictMap x)) =
    classOf (strictCycle (strictMap y))
  rw [strictCycle_strictMap, strictCycle_strictMap]

omit [CharZero k] in
private theorem cohomologyClass_eq_iff {C : ModuleCochain.{u,v} k}
    (x y : cyclesZero C) :
    cohomologyClass x = cohomologyClass y ↔ classOf x = classOf y := by
  change C.h0HomologyIso.hom (classOf x) = C.h0HomologyIso.hom (classOf y) ↔ _
  exact (ModuleCat.mono_iff_injective _).mp inferInstance |>.eq_iff

omit [CharZero k] in
private theorem cohomologyClass_surjective (C : ModuleCochain.{u,v} k) :
    Function.Surjective (cohomologyClass (C := C)) :=
  ((ModuleCat.epi_iff_surjective C.h0HomologyIso.hom).mp inferInstance).comp
    (Submodule.Quotient.mk_surjective _)

theorem pathQuotient : PathQuotient.{u,v} := by
  intro k _ _ A B b R T ht M hm S W U
  obtain ⟨P, E, e, _, he⟩ :=
    SquareZeroMaps.polynomialPathsAreCycles R T ht hm S W U
  have endpoints (p : Maps R P.augmentation P.zeroSection) (c : k) :
      strictMap (e p) ≫ W.evaluation c = strictMap (E.equiv (P.evalMap p c)) := by
    have hcyc : strictCycle (strictMap (e p) ≫ W.evaluation c) =
        E.equiv (P.evalMap p c) := E.cycle_ext (by
      intro i x
      exact (he p c i x).symm)
    rw [← hcyc, RightDGModule.strictMap_strictCycle]
  have criterion (f₀ f₁ : Maps R S.projection S.zeroSection) :
      PolynomiallyHomotopic P f₀ f₁ ↔
        ∃ h : GradedHom (R.module T) M (-1),
          (homComplex (R.module T) M).d (-1) 0 h = (E.equiv f₁).val - (E.equiv f₀).val := by
    rw [boundary_iff_homotopy (x := E.equiv f₁) (y := E.equiv f₀)]
    constructor
    · rintro ⟨p, hp₀, hp₁⟩
      have hh := integrate_equation W (strictMap (e p))
      rw [endpoints p 0, endpoints p 1, hp₀, hp₁] at hh
      exact ⟨_, hh⟩
    · rintro ⟨h, hh⟩
      let z := strictCycle (interpolate W (strictMap (E.equiv f₀)) (strictMap (E.equiv f₁)) h hh)
      let p := e.symm z
      have hp : strictMap (e p) =
          interpolate W (strictMap (E.equiv f₀)) (strictMap (E.equiv f₁)) h hh := by
        dsimp only [p]
        rw [e.apply_symm_apply]
        exact RightDGModule.strictMap_strictCycle _
      refine ⟨p, ?_, ?_⟩
      · apply E.equiv.injective
        rw [← strictCycle_strictMap (E.equiv (P.evalMap p 0)), ← endpoints p 0, hp,
          interpolate_zero, strictCycle_strictMap]
      · apply E.equiv.injective
        rw [← strictCycle_strictMap (E.equiv (P.evalMap p 1)), ← endpoints p 1, hp,
          interpolate_one, strictCycle_strictMap]
  refine ⟨P, E, criterion, ?_⟩
  have classes f₀ f₁ : PolynomiallyHomotopic P f₀ f₁ ↔
      cohomologyClass (E.equiv f₀) = cohomologyClass (E.equiv f₁) := by
    rw [criterion, boundary_iff_class_eq, cohomologyClass_eq_iff, eq_comm]
  let descend := Quot.lift (fun f => cohomologyClass (E.equiv f))
    (fun f₀ f₁ hp => (classes f₀ f₁).mp hp)
  have injective : Function.Injective descend := by
    intro x y
    induction x using Quot.ind with
    | mk x =>
      induction y using Quot.ind with
      | mk y =>
        intro hxy
        exact Quot.sound ((classes x y).mpr hxy)
  have surjective : Function.Surjective descend := by
    intro c
    obtain ⟨x, hx⟩ := (cohomologyClass_surjective _).comp E.equiv.surjective c
    exact ⟨Quot.mk _ x, hx⟩
  exact ⟨Equiv.ofBijective descend ⟨injective, surjective⟩, fun _ => rfl⟩

section ClassNaturality

omit [CharZero k]

private def cyclesIso (C : ModuleCochain.{u,v} k) :
    C.cycles 0 ≅ ModuleCat.of k (cyclesZero C) :=
  C.cyclesIsoSc' (-1) 0 1
    (ComplexShape.prev_eq' _ (show (-1 : ℤ) + 1 = 0 from rfl))
    (ComplexShape.next_eq' _ (show (0 : ℤ) + 1 = 1 from rfl)) ≪≫
    (C.sc' (-1) 0 1).moduleCatCyclesIso

private theorem cyclesIso_val (C : ModuleCochain.{u,v} k) (x : cyclesZero C) :
    C.iCycles 0 ((cyclesIso C).inv x) = x.val := by
  let e := C.cyclesIsoSc' (-1) 0 1
    (ComplexShape.prev_eq' _ (show (-1 : ℤ) + 1 = 0 from rfl))
    (ComplexShape.next_eq' _ (show (0 : ℤ) + 1 = 1 from rfl))
  have he : (cyclesIso C).inv ≫ C.iCycles 0 = (C.sc' (-1) 0 1).moduleCatLeftHomologyData.i := by
    change ((C.sc' (-1) 0 1).moduleCatCyclesIso.inv ≫ e.inv) ≫ C.iCycles 0 = _
    rw [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
      ShortComplex.moduleCatCyclesIso_inv_iCycles]
  exact CategoryTheory.congr_fun he x

private theorem cyclesIso_class (C : ModuleCochain.{u,v} k) (x : cyclesZero C) :
    C.homologyπ 0 ((cyclesIso C).inv x) = cohomologyClass x := by
  let S := C.sc' (-1) 0 1
  let ep : (ComplexShape.up ℤ).prev 0 = -1 :=
    ComplexShape.prev_eq' _ (show (-1 : ℤ) + 1 = 0 from rfl)
  let en : (ComplexShape.up ℤ).next 0 = 1 :=
    ComplexShape.next_eq' _ (show (0 : ℤ) + 1 = 1 from rfl)
  have he : (cyclesIso C).inv ≫ C.homologyπ 0 =
      S.moduleCatLeftHomologyData.π ≫ C.h0HomologyIso.hom := by
    change (S.moduleCatCyclesIso.inv ≫ (C.cyclesIsoSc' (-1) 0 1 ep en).inv) ≫
        C.homologyπ 0 =
      S.moduleCatLeftHomologyData.π ≫
        S.moduleCatHomologyIso.inv ≫ (C.homologyIsoSc' (-1) 0 1 ep en).inv
    rw [Category.assoc, ← HomologicalComplex.π_homologyIsoSc'_inv, ← Category.assoc,
      ShortComplex.moduleCatCyclesIso_inv_π, Category.assoc]
  exact CategoryTheory.congr_fun he x

private theorem cohomologyClass_map {C E : ModuleCochain.{u,v} k}
    (g : C ⟶ E) {x : cyclesZero C} {y : cyclesZero E} (h : g.f 0 x.val = y.val) :
    HomologicalComplex.homologyMap g 0 (cohomologyClass x) = cohomologyClass y := by
  have hcyc : HomologicalComplex.cyclesMap g 0 ((cyclesIso C).inv x) = (cyclesIso E).inv y := by
    apply (ModuleCat.mono_iff_injective (E.iCycles 0)).mp inferInstance
    have he := CategoryTheory.congr_fun (HomologicalComplex.cyclesMap_i g 0) ((cyclesIso C).inv x)
    rw [cyclesIso_val]
    have he' : E.iCycles 0 (HomologicalComplex.cyclesMap g 0 ((cyclesIso C).inv x)) =
        g.f 0 (C.iCycles 0 ((cyclesIso C).inv x)) := he
    rw [he', cyclesIso_val, h]
  have he := CategoryTheory.congr_fun (HomologicalComplex.homologyπ_naturality g 0)
    ((cyclesIso C).inv x)
  have he' : HomologicalComplex.homologyMap g 0 (C.homologyπ 0 ((cyclesIso C).inv x)) =
      E.homologyπ 0 (HomologicalComplex.cyclesMap g 0 ((cyclesIso C).inv x)) := he
  rw [hcyc, cyclesIso_class, cyclesIso_class] at he'
  exact he'

end ClassNaturality

theorem classNaturality : ClassNaturality.{u,v} := by
  intro k _ _ A B b R T M N S U E E' J hJ g
  obtain ⟨G, hG⟩ := SquareZeroMaps.coefficientNaturality R T S U E E' g
  refine ⟨G, fun f => cohomologyClass_map ((J.post (R.module T) g).app ()) ?_⟩
  let F : homComplex (R.module T) M ⟶ homComplex (R.module T) N :=
    (J.post (R.module T) g).app ()
  let z₀ := E.equiv f
  let z : Cycles R T N := ⟨F.f 0 z₀.val, by
    change (homComplex (R.module T) N).d 0 1 (F.f 0 z₀.val) = 0
    have hz₀ : (homComplex (R.module T) M).d 0 1 z₀.val = 0 := z₀.property
    rw [chain_comm F 0, hz₀, map_zero]⟩
  have hz : z = E'.equiv (G.postcompose f) := E'.cycle_ext (by
    intro i x
    rw [hG f i x]
    exact hJ.post g 0 z₀.val i i (add_zero i) _)
  exact congrArg Subtype.val hz

private theorem compose_squares {C : Type*} [Category C] {X X' Y Y' Z Z' : C}
    {f : X ⟶ X'} {g : Y ⟶ Y'} {h : Z ⟶ Z'}
    {a : X ⟶ Y} {a' : X' ⟶ Y'} {b : Y ⟶ Z} {b' : Y' ⟶ Z'}
    (ha : f ≫ a' = a ≫ g) (hb : g ≫ b' = b ≫ h) :
    f ≫ (a' ≫ b') = (a ≫ b) ≫ h := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

section Derived

open Specs.DerivedFormalization.Affine.CotangentComplex (oneObject)
open Specs.DerivedFormalization.Affine.DerivedHom (internalHom K)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws quasiIsomorphisms)
open Specs.DerivedFormalization.DG.DerivedKProjective
  (derivedCategoryInstance kProjectiveObjects restrictedLocalization)
open Specs.DerivedFormalization.DG.KProjective (isKProjective)

variable (B : NonpositiveCDGA.{u,v} k)
variable (h : HomotopyCategoryLaws (oneObject B))
variable [hLaw : Fact (HomotopyCategoryLaws (oneObject B))]

local instance : Category (K B.toCommDGAlgebra) :=
  Specs.DerivedFormalization.DG.Derived.homotopyCategory _ hLaw.out
local instance : Category (D B h) := derivedCategoryInstance _ h

open private representative representative_class from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedHom

/-- Ordinary cohomology is invariant under homotopy of dg module morphisms. -/
private def homotopyCohomology (i : ℤ) :
    RightDGModule.K (oneObject B) ⥤ ModuleCat.{v} k where
  obj M := (M.complex ()).homology i
  map g := HomologicalComplex.homologyMap ((representative (A := B.toCommDGAlgebra) g).app ()) i
  map_id M := by
    rw [RightDGModule.homologyMap_eq_of_homotopyClass_eq
      (g := 𝟙 (show B.Module from M)) (representative_class (A := B.toCommDGAlgebra) (𝟙 M)) () i]
    exact HomologicalComplex.homologyMap_id _ i
  map_comp {X Y Z} f g := by
    let T := RightDGModule.toHomotopyCategory (oneObject B)
    have hf : T.map (representative (A := B.toCommDGAlgebra) f) = f := representative_class (A := B.toCommDGAlgebra) f
    have hg : T.map (representative (A := B.toCommDGAlgebra) g) = g := representative_class (A := B.toCommDGAlgebra) g
    have hc : homotopyClass (representative (A := B.toCommDGAlgebra) (f ≫ g)) =
        homotopyClass (representative (A := B.toCommDGAlgebra) f ≫ representative (A := B.toCommDGAlgebra) g) := by
      change _ = T.map (representative (A := B.toCommDGAlgebra) f ≫ representative (A := B.toCommDGAlgebra) g)
      rw [T.map_comp, hf, hg, representative_class]
      rfl
    rw [RightDGModule.homologyMap_eq_of_homotopyClass_eq hc () i]
    exact HomologicalComplex.homologyMap_comp _ _ _

omit hLaw in
private theorem homotopyCohomology_map (i : ℤ) {M N : B.Module} (g : M ⟶ N) :
    (homotopyCohomology B i).map (homotopyClass g) = HomologicalComplex.homologyMap (g.app ()) i :=
  RightDGModule.homologyMap_eq_of_homotopyClass_eq
    (representative_class (A := B.toCommDGAlgebra) (homotopyClass g)) () i

private theorem homotopyCohomology_inverts (i : ℤ) :
    (quasiIsomorphisms (oneObject B)).IsInvertedBy (homotopyCohomology B i) := by
  rintro M N _ ⟨g, rfl, hg⟩
  rw [homotopyCohomology_map B i g]
  have : QuasiIso (g.app ()) := hg ()
  exact (quasiIsoAt_iff_isIso_homologyMap (g.app ()) i).mp inferInstance

private def localizedCohomology (i : ℤ) : CohomologyRealization B h i := by
  let J := homotopyCohomology B i
  let inv := homotopyCohomology_inverts B i
  letI : (Q B h).IsLocalization (quasiIsomorphisms (oneObject B)) :=
    inferInstanceAs ((RightDGModule.Q (oneObject B) h).IsLocalization
      (RightDGModule.quasiIsomorphisms (oneObject B)))
  let F := Localization.lift J inv (Q B h)
  let e := Localization.fac J inv (Q B h)
  refine ⟨F, fun M => e.app M, ?_⟩
  intro M N g
  let g₀ : @Quiver.Hom (RightDGModule.K (oneObject B)) _ M N := homotopyClass g
  have he := e.hom.naturality g₀
  change F.map ((Q B h).map (homotopyClass g)) ≫ (e.app N).hom =
    (e.app M).hom ≫ J.map (homotopyClass g) at he
  rw [homotopyCohomology_map] at he
  exact he

private theorem homRealization_nonempty :
    Nonempty (HomRealization B h) := by
  obtain ⟨J, H, F, hJ, hObj, hMap, e, _, _⟩ :=
    DerivedHom.derivedHomRealization B.toCommDGAlgebra h
  exact ⟨⟨J, hJ, H, F, hObj, hMap, e⟩⟩

variable {B h}

private theorem pre_id (F : HomRealization B h) (L M : B.Module) :
    F.actions.pre M (𝟙 L) = 𝟙 (internalHom L M) := by
  apply RightDGModuleModel.hom_ext
  rintro ⟨⟩
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply RightDGModule.GradedHom.ext (M := L) (N := M)
  rintro ⟨⟩ i q e
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact F.laws.pre (𝟙 L) r f i q e x

private def derivedModelIso (F : HomRealization B h) (L : B.Module) (hp : isKProjective L)
    (M : B.Module) :
    F.onDerived.obj (op ((Q B h).obj L), (Q B h).obj M) ≅
      (Q B h).obj (internalHom L M) :=
  F.factorization.app (op ⟨L, hp⟩, M) ≪≫ eqToIso (congrArg (Q B h).obj (F.model_obj L M))

private theorem derivedModelIso_natural (F : HomRealization B h)
    (L : B.Module) (hp : isKProjective L) {M N : B.Module} (g : M ⟶ N) :
    derivedPost F L g ≫ (derivedModelIso F L hp N).hom =
      (derivedModelIso F L hp M).hom ≫ (Q B h).map (homotopyClass (F.actions.post L g)) := by
  let Kp := (kProjectiveObjects (oneObject B)).FullSubcategory
  let L' : Kp := ⟨L, hp⟩
  let f₀ : @Quiver.Hom (K B.toCommDGAlgebra) _ L L := homotopyClass (𝟙 L)
  let g₀ : @Quiver.Hom (K B.toCommDGAlgebra) _ M N := homotopyClass g
  let a : ((op L', M) : Kpᵒᵖ × K B.toCommDGAlgebra) ⟶ (op L', N) :=
    CategoryTheory.Prod.mkHom (𝟙 (op L')) g₀
  let μ := F.onHomotopy.map (CategoryTheory.Prod.mkHom f₀.op g₀)
  let ν : @Quiver.Hom (K B.toCommDGAlgebra) _ (internalHom L M) (internalHom L N) :=
    homotopyClass (F.actions.post L g)
  have hμ : HEq μ ν := by
    have he := F.model_map (𝟙 L) g
    dsimp only at he
    rw [pre_id F L M, Category.id_comp] at he
    exact he
  have hc : μ ≫ eqToHom (F.model_obj L N) = eqToHom (F.model_obj L M) ≫ ν :=
    eq_of_heq ((comp_eqToHom_heq μ _).trans (hμ.trans (eqToHom_comp_heq ν _).symm))
  have hQ : (Q B h).map μ ≫ eqToHom (congrArg (Q B h).obj (F.model_obj L N)) =
      eqToHom (congrArg (Q B h).obj (F.model_obj L M)) ≫ (Q B h).map ν := by
    have eq := congrArg (Q B h).map hc
    simpa only [Functor.map_comp, eqToHom_map] using eq
  let I := (restrictedLocalization (oneObject B) h).op
  let J := (kProjectiveObjects (oneObject B)).ι.op
  have ha₁ : (I.prod (Q B h)).map a =
      CategoryTheory.Prod.mkHom (𝟙 (op ((Q B h).obj L))) ((Q B h).map g₀) := by
    change CategoryTheory.Prod.mkHom (I.map (𝟙 (op L'))) ((Q B h).map g₀) = _
    rw [I.map_id]
    rfl
  have ha₂ : (J.prod (𝟭 (K B.toCommDGAlgebra))).map a =
      CategoryTheory.Prod.mkHom f₀.op g₀ := by
    change CategoryTheory.Prod.mkHom (J.map (𝟙 (op L'))) g₀ = _
    rw [J.map_id]
    rfl
  have hs := F.factorization.hom.naturality a
  change F.onDerived.map ((I.prod (Q B h)).map a) ≫ (F.factorization.app (op L', N)).hom =
    (F.factorization.app (op L', M)).hom ≫ (Q B h).map
      (F.onHomotopy.map ((J.prod (𝟭 (K B.toCommDGAlgebra))).map a)) at hs
  rw [ha₁, ha₂] at hs
  change derivedPost F L g ≫ ((F.factorization.app (op L', N)).hom ≫
      eqToHom (congrArg (Q B h).obj (F.model_obj L N))) =
    ((F.factorization.app (op L', M)).hom ≫
      eqToHom (congrArg (Q B h).obj (F.model_obj L M))) ≫ (Q B h).map ν
  exact compose_squares hs hQ

theorem derivedCalculation : DerivedCalculation.{u,v} := by
  intro k _ _ B h
  let _ : Fact (HomotopyCategoryLaws (oneObject B)) := ⟨h⟩
  let _ := Specs.DerivedFormalization.DG.Derived.homotopyCategory (oneObject B) h
  let _ := derivedCategoryInstance (oneObject B) h
  refine ⟨homRealization_nonempty B h, ⟨localizedCohomology B h, ?_⟩⟩
  intro F A b R T ht hB
  let L := R.module T
  have hp : isKProjective L :=
    (CotangentModelProperties.cotangentModelProperties T b R.base R.augmentation
      R.differentials R.triangle R.semifree R.surjective R.quasiIso ht hB).1
  let C := localizedCohomology B h
  refine ⟨hp, ⟨fun i M => (C i).functor.mapIso (derivedModelIso F L hp M) ≪≫
    (C i).onStrict (internalHom L M), ?_⟩⟩
  intro i M N g
  let P := (C i).functor
  have he : P.map (derivedPost F L g) ≫ P.map (derivedModelIso F L hp N).hom =
      P.map (derivedModelIso F L hp M).hom ≫
        P.map ((Q B h).map (homotopyClass (F.actions.post L g))) := by
    exact (P.map_comp _ _).symm.trans
      ((congrArg P.map (derivedModelIso_natural F L hp g)).trans (P.map_comp _ _))
  change P.map (derivedPost F L g) ≫
      (P.map (derivedModelIso F L hp N).hom ≫ ((C i).onStrict (internalHom L N)).hom) =
    (P.map (derivedModelIso F L hp M).hom ≫ ((C i).onStrict (internalHom L M)).hom) ≫
      HomologicalComplex.homologyMap ((F.actions.post L g).app ()) i
  exact compose_squares he ((C i).onStrict_natural (F.actions.post L g))

theorem tangentCalculation : TangentCalculation.{u,v} := by
  intro k _ _ A B b R T ht hB h
  let _ : Fact (HomotopyCategoryLaws (oneObject B)) := ⟨h⟩
  let _ := Specs.DerivedFormalization.DG.Derived.homotopyCategory (oneObject B) h
  let _ := derivedCategoryInstance (oneObject B) h
  let L := R.module T
  obtain ⟨⟨F⟩, C, hC⟩ := derivedCalculation B h
  obtain ⟨_, e, he⟩ := hC F R T ht hB
  refine ⟨F, C 0, ?_⟩
  dsimp only
  intro S W U
  choose P E _ q hq using
    (fun (M : B.Module) (hm : IsNonpositive M) =>
      pathQuotient R T ht hm (S M) (W M) (U M))
  let intoDerived (M : B.Module) := ((forget (ModuleCat.{v} k)).mapIso (e 0 M).symm).toEquiv
  let comp M hm := (q M hm).trans (intoDerived M)
  have onClass M hm f : (e 0 M).hom (comp M hm (Quot.mk _ f)) =
      cohomologyClass ((E M hm).equiv f) := by
    have hi := (intoDerived M).left_inv (q M hm (Quot.mk _ f))
    exact hi.trans (hq M hm f)
  refine ⟨P, E, e 0, comp, onClass, ?_⟩
  intro M N hm hn g
  obtain ⟨G, hG⟩ :=
    classNaturality R T (S M) (S N) (E M hm) (E N hn) F.actions F.laws g
  refine ⟨G, fun f => ?_⟩
  apply (ModuleCat.mono_iff_injective (e 0 N).hom).mp inferInstance
  change (e 0 N).hom ((C 0).functor.map (derivedPost F L g) (comp M hm (Quot.mk _ f))) =
    (e 0 N).hom (comp N hn (Quot.mk _ (G.postcompose f)))
  calc
    _ = HomologicalComplex.homologyMap ((F.actions.post L g).app ()) 0
          ((e 0 M).hom (comp M hm (Quot.mk _ f))) :=
      CategoryTheory.congr_fun (he 0 g) (comp M hm (Quot.mk _ f))
    _ = _ := by rw [onClass M hm f, hG f, onClass N hn (G.postcompose f)]

end Derived

end
end DerivedFormalization.Affine.SquareZeroHomotopy
