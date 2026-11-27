import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.PerfectDuals
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.PerfectChainEvaluation
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorInvariance
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Adjunction.Unique

namespace DerivedFormalization.PerfectDuals

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Specs.DerivedFormalization
open Specs.DerivedFormalization.PerfectDuals
open Specs.DerivedFormalization.PerfectComplex (isBoundedFiniteProjectiveValue isPerfectValue)
open Specs.DerivedFormalization.Cochains
open Specs.DerivedFormalization.CochainModels (internalHomValue internalHomMapValue)
open Specs.DerivedFormalization.CochainTensorTransport
  (AdequateModel representedUnit representedUnitZero)
open Specs.DerivedFormalization.CochainTensor (tensor isKFlat)
open Specs.DerivedFormalization.DerivedHomAdjunction
  (Closed Presentation homComparison tensorComparison)
open Specs.DerivedFormalization.DerivedHomModels (Models rHomValue)
open HomologicalComplex CochainComplex.HomComplex
open scoped TensorProduct

universe u a v t

attribute [local instance] HasDerivedCategory.standard

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.checkUnivs false

def dual : DualType := @dualValue

variable {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}

private theorem projective_model (P : compValue.{a} R)
    (h : isBoundedFiniteProjectiveValue P) : P.IsKProjective := by
  obtain ⟨hp, b, c, _, hz⟩ := h
  letI (i : ℤ) : Module.Projective R (P.X i) := (hp i).2
  letI : P.IsStrictlyLE c := (CochainComplex.isStrictlyLE_iff P c).2
    (fun i hi => hz i (Or.inr hi))
  exact CochainComplex.isKProjective_of_projective P c

private theorem flat_model (P : compValue.{a} R)
    (h : isBoundedFiniteProjectiveValue P) : isKFlat P := by
  obtain ⟨hp, b, c, _, hz⟩ := h
  letI (i : ℤ) : Module.Projective R (P.X i) := (hp i).2
  exact CochainTensorInvariance.boundedAboveFlatIsKFlat R P
    (fun i => inferInstance) ⟨c, fun i hi => hz i (Or.inr hi)⟩

theorem perfectLift : PerfectLift.{u,v,t} := by
  intro R _ P hp
  obtain ⟨C, ⟨hterm, b, c, hbc, hz⟩, ⟨i⟩⟩ := hp
  let L := CochainCoefficientLift.lift.{max u t,v} R
  let F := CochainCoefficientLift.liftD.{max u t,v} R
  refine ⟨L.obj C, ⟨?_, b, c, hbc, ?_⟩,
    ⟨(F).mapIso i ≪≫ (CochainCoefficientLift.liftDFactors.{max u t,v} R).app C⟩⟩
  · intro n
    let f := CochainCoefficientLift.termEquiv.{max u t} C n
    letI : Module.Finite R (C.X n) := (hterm n).1
    letI : Module.Projective R (C.X n) := (hterm n).2
    exact ⟨Module.Finite.of_surjective f.toLinearMap f.surjective, Module.Projective.of_equiv' f⟩
  · intro n hn
    letI := ModuleCat.subsingleton_of_isZero (hz n hn)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (CochainCoefficientLift.termEquiv.{max u t} C n).symm.injective.subsingleton

section Chain

variable (M : AdequateModel e)

local notation "U" => representedUnit e
local notation "B" => Specs.DerivedFormalization.PerfectDuals.chainDual e

private theorem stalk_zero {n : ℤ} (hn : n ≠ 0) : IsZero ((representedUnit e).X n) :=
  isZero_single_obj_X (.up ℤ) 0 _ n hn

private theorem chainEvaluation_apply (P : compValue.{a} R) {i j n : ℤ}
    (h : j + i = n) (f : (B P).X j) (x : P.X i) :
    (Specs.DerivedFormalization.PerfectDuals.chainEvaluation M P).f n (Specs.DerivedFormalization.CochainTensor.pure (B P) P h f x) = f.v i n (by omega) x := by
  subst n
  exact (M.rawClosed P).counit_on_pure U j i f x

set_option maxHeartbeats 800000 in
private theorem chainComparison_apply_raw (P Y : compValue.{a} R) {i j k n l s : ℤ}
    (h : j + k = n) (hl : i + n = l) (hs : k + i = s)
    (y : Y.X j) (f : (B P).X k) (x : P.X i) :
    letI := M.chainMonoidal
    ((chainComparison M P Y).f n (Specs.DerivedFormalization.CochainTensor.pure Y (B P) h y f)).v i l hl x =
      ((M.tensorModel Y U ≪≫ tensorIso (Iso.refl Y) M.unitModel ≪≫ ρ_ Y).hom).f l
        (Specs.DerivedFormalization.CochainTensor.pure Y U (by omega : j + s = l) y (f.v i s (by omega) x)) := by
  letI := M.chainMonoidal
  dsimp only
  obtain rfl : l = n + i := by omega
  unfold chainComparison
  erw [(M.rawClosed P).on_pure]
  let a := M.tensorModel (tensor Y (B P)) P ≪≫
    tensorIso (M.tensorModel Y (B P)) (Iso.refl P)
  let b := M.tensorModel Y (tensor (B P) P) ≪≫
    tensorIso (Iso.refl Y) (M.tensorModel (B P) P)
  let m := M.tensorModel Y U ≪≫ tensorIso (Iso.refl Y) M.unitModel ≪≫ ρ_ Y
  let r := a ≪≫ α_ Y (B P) P ≪≫ b.symm
  have he :
      (M.tensorModel (tensor Y (B P)) P).hom ≫ (M.tensorModel Y (B P)).hom ▷ P ≫
        (α_ Y (B P) P).hom ≫
        Y ◁ ((M.tensorModel (B P) P).inv ≫ Specs.DerivedFormalization.PerfectDuals.chainEvaluation M P ≫ M.unitModel.hom) ≫
        (ρ_ Y).hom =
      r.hom ≫ CochainTensor.map (𝟙 Y) (Specs.DerivedFormalization.PerfectDuals.chainEvaluation M P) ≫ m.hom := by
    dsimp [r, a, b, m]
    simp only [Category.assoc, id_tensorHom, tensorHom_id]
    rw [reassoc_of% (M.tensorModel_natural (𝟙 Y) (Specs.DerivedFormalization.PerfectDuals.chainEvaluation M P))]
    simp [whiskerLeft_comp]
  rw [he]
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  have ha : r.hom.f (n + i) (Specs.DerivedFormalization.CochainTensor.pure (tensor Y (B P)) P rfl (Specs.DerivedFormalization.CochainTensor.pure Y (B P) h y f) x) =
      Specs.DerivedFormalization.CochainTensor.pure Y (tensor (B P) P) (by omega : j + s = n + i) y (Specs.DerivedFormalization.CochainTensor.pure (B P) P hs f x) :=
    M.associator_on_pure Y (B P) P j k i h rfl hs (by omega) y f x
  rw [ha, CochainTensor.map_on_pure, chainEvaluation_apply]
  rfl

set_option maxHeartbeats 500000 in
theorem chainFormulas : ChainFormulas.{u,a} := by
  intro R _ A _ e M P Y
  refine ⟨fun h f x => chainEvaluation_apply M P h f x, ?_, ?_, ?_⟩
  · intro i j k n h hk y f x
    rw [chainComparison_apply_raw M P Y h (by omega : i + n = j) (by omega : k + i = 0)]
    have hr := M.rightUnitor_on_pure Y j y ((representedUnitZero e).hom (f.v i 0 hk x))
    simpa only [Iso.hom_inv_id_apply] using hr
  · intro i j k n l h hl hk y f x
    rw [chainComparison_apply_raw M P Y h hl (rfl : k + i = _)]
    letI := ModuleCat.subsingleton_of_isZero (stalk_zero (e := e) (n := k + i) (by omega))
    rw [Subsingleton.elim (f.v i (k + i) (by omega) x) 0]
    simp [Specs.DerivedFormalization.CochainTensor.pure]
  · intro i j n h x f
    obtain rfl : n = i + j := by omega
    letI := M.chainMonoidal
    letI := M.chainSymmetric
    unfold chainBiduality
    erw [(M.rawClosed (Specs.DerivedFormalization.PerfectDuals.chainDual e P)).on_pure]
    let b := M.tensorModel P (Specs.DerivedFormalization.PerfectDuals.chainDual e P) ≪≫ β_ P (Specs.DerivedFormalization.PerfectDuals.chainDual e P) ≪≫ (M.tensorModel (Specs.DerivedFormalization.PerfectDuals.chainDual e P) P).symm
    change (b.hom ≫ Specs.DerivedFormalization.PerfectDuals.chainEvaluation M P).f (i + j) (Specs.DerivedFormalization.CochainTensor.pure P (Specs.DerivedFormalization.PerfectDuals.chainDual e P) rfl x f) = _
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    rw [show b.hom.f (i + j) (Specs.DerivedFormalization.CochainTensor.pure P (Specs.DerivedFormalization.PerfectDuals.chainDual e P) rfl x f) =
      (i * j).negOnePow • Specs.DerivedFormalization.CochainTensor.pure (Specs.DerivedFormalization.PerfectDuals.chainDual e P) P h f x from M.braiding_on_pure P (Specs.DerivedFormalization.PerfectDuals.chainDual e P) rfl x f]
    change (Specs.DerivedFormalization.PerfectDuals.chainEvaluation M P).f (i + j) ((i * j).negOnePow • Specs.DerivedFormalization.CochainTensor.pure (Specs.DerivedFormalization.PerfectDuals.chainDual e P) P h f x) = _
    simp only [Units.smul_def, map_zsmul, chainEvaluation_apply]

open Specs.DerivedFormalization.CochainRingTransport
  (complexFunctorValue rankOneComparisonValue moduleEquivalenceValue)
open Specs.DerivedFormalization.CochainTensorTransport (homFrom)

local notation "F" => complexFunctorValue e
local notation "nativeDual" => DerivedFormalization.chainDual
local notation "chainCmp" => Specs.DerivedFormalization.PerfectDuals.chainComparison

private def nativeDualIso (P : compValue.{a} R) :
    (F).obj (B P) ≅ nativeDual ((F).obj P) :=
  M.homIso P U ≪≫ (homFrom ((F).obj P)).mapIso (rankOneComparisonValue e)

private theorem nativeDualIso_apply (P : compValue.{a} R) {i j n : ℤ} (h : i + n = j)
    (f : (B P).X n) (x : P.X i) :
    ((nativeDualIso M P).hom.f n f).v i j h x = (rankOneComparisonValue e).hom.f j (f.v i j h x) := by
  change ((internalHomMapValue (𝟙 ((F).obj P)) (rankOneComparisonValue e).hom).f n
    ((M.homIso P U).hom.f n f)).v i j h x = _
  erw [DerivedFormalization.internalHomMap_apply]
  change (rankOneComparisonValue e).hom.f j (((M.homIso P U).hom.f n f).v i j h x) = _
  rw [M.hom_on_eval]

private theorem nativeDualIso_at_zero (P : compValue.{a} R) {i n : ℤ} (h : i + n = 0)
    (f : (B P).X n) (x : P.X i) :
    DerivedFormalization.chainDualTerm ((F).obj P) h ((nativeDualIso M P).hom.f n f) x =
      (representedUnitZero e).hom (f.v i 0 h x) := by
  rw [DerivedFormalization.chainDualTerm_apply, nativeDualIso_apply]
  rfl

private theorem transport_bounded (P : compValue.{a} R) :
    isBoundedFiniteProjectiveValue ((F).obj P) ↔ isBoundedFiniteProjectiveValue P := by
  letI : Small.{a} R := small_of_injective e.injective
  have hterm (i : ℤ) :
      (Module.Finite A (((F).obj P).X i) ∧ Module.Projective A (((F).obj P).X i)) ↔
      (Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) := by
    obtain ⟨hp, _, hf⟩ := CochainRingTransport.moduleProperties e (P.X i)
    rw [IsProjective.iff_projective, IsProjective.iff_projective]
    exact and_congr hf hp
  have hz (i : ℤ) : IsZero (((F).obj P).X i) ↔ IsZero (P.X i) := by
    rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
    rfl
  constructor <;> rintro ⟨h, b, c, hbc, hzero⟩
  · exact ⟨fun i => (hterm i).1 (h i), b, c, hbc, fun i hi => (hz i).1 (hzero i hi)⟩
  · exact ⟨fun i => (hterm i).2 (h i), b, c, hbc, fun i hi => (hz i).2 (hzero i hi)⟩

private theorem bounded_of_iso {S P : compValue.{a} R} (i : S ≅ P)
    (h : isBoundedFiniteProjectiveValue P) : isBoundedFiniteProjectiveValue S := by
  obtain ⟨h, b, c, hbc, hz⟩ := h
  refine ⟨fun n => ?_, b, c, hbc, fun n hn => (hz n hn).of_iso (Hom.isoApp i n)⟩
  letI : Module.Finite R (P.X n) := (h n).1
  letI : Module.Projective R (P.X n) := (h n).2
  let f := (Hom.isoApp i n).toLinearEquiv.symm
  exact ⟨Module.Finite.of_surjective f.toLinearMap f.surjective, Module.Projective.of_equiv' f⟩

private theorem native_bounded {S : Type a} [CommRing S] {P : compValue.{a} S}
    (h : isBoundedFiniteProjectiveValue P) :
    Specs.DerivedFormalization.PerfectChainEvaluation.boundedFiniteProjectiveValue P := by
  obtain ⟨h, b, c, _, hz⟩ := h
  exact ⟨⟨b, c, hz⟩, fun n => (h n).1, fun n => (h n).2⟩

include M in
private theorem bounded_dual (P : compValue.{a} R) (h : isBoundedFiniteProjectiveValue P) :
    isBoundedFiniteProjectiveValue (B P) := by
  have hP := native_bounded (P := (F).obj P) ((transport_bounded (e := e) P).2 h)
  obtain ⟨⟨b, c, hz⟩, hf, hp⟩ := DerivedFormalization.chainDual_boundedFiniteProjective hP
  have hb : isBoundedFiniteProjectiveValue (nativeDual ((F).obj P)) :=
    ⟨fun i => ⟨hf i, hp i⟩, min b c, c, min_le_right _ _,
      fun i hi => hz i (hi.imp (fun hj => lt_of_lt_of_le hj (min_le_left _ _)) id)⟩
  exact (transport_bounded (e := e) (B P)).1 (bounded_of_iso (nativeDualIso M P) hb)

set_option maxHeartbeats 1200000 in
private theorem native_comparison (P Y : compValue.{a} R) :
    (M.tensorIso Y (B P)).hom ≫ (F).map (chainCmp M P Y) ≫ (M.homIso P Y).hom =
      CochainTensor.map (𝟙 ((F).obj Y)) (nativeDualIso M P).hom ≫
        DerivedFormalization.chainEvaluationComparison ((F).obj P) ((F).obj Y) := by
  apply CochainTensor.hom_ext
  intro j k n h y f
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [M.tensor_on_pure, CochainTensor.map_on_pure]
  change ((M.homIso P Y).hom.f n ((chainCmp M P Y).f n
      (Specs.DerivedFormalization.CochainTensor.pure Y (B P) h y f))) = _
  apply Cochain.ext
  intro i l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [M.hom_on_eval]
  let d := (nativeDualIso M P).hom.f k f
  by_cases hk : i + k = 0
  · have hj : j = i + n := by omega
    subst j
    subst l
    erw [(chainFormulas M P Y).2.1 h hk y f x]
    change _ = ((DerivedFormalization.chainEvaluationComparison ((F).obj P) ((F).obj Y)).f n
      (ιTensorObj ((F).obj Y) (nativeDual ((F).obj P)) (i + n) k n h (y ⊗ₜ[A] d))).v i (i + n) rfl x
    erw [DerivedFormalization.chainEvaluationComparison_apply _ _ h hk y d x]
    erw [nativeDualIso_at_zero M P hk f x]
    rfl
  · erw [(chainFormulas M P Y).2.2.1 h hl hk y f x]
    change _ = ((DerivedFormalization.chainEvaluationComparison ((F).obj P) ((F).obj Y)).f n
      (ιTensorObj ((F).obj Y) (nativeDual ((F).obj P)) j k n h (y ⊗ₜ[A] d))).v i l hl x
    rw [DerivedFormalization.chainEvaluationComparison_apply_off _ _ h hl hk y d x]

private theorem chainComparison_isIso (P Y : compValue.{a} R)
    (h : isBoundedFiniteProjectiveValue P) : IsIso (chainCmp M P Y) := by
  haveI : IsIso (DerivedFormalization.chainEvaluationComparison ((F).obj P) ((F).obj Y)) :=
    (DerivedFormalization.chainEvaluationIso ((F).obj P)
      (native_bounded ((transport_bounded (e := e) P).2 h)) ((F).obj Y)).isIso_hom
  haveI : IsIso (CochainTensor.map (𝟙 ((F).obj Y)) (nativeDualIso M P).hom) := by
    change IsIso (((Specs.DerivedFormalization.DG.Basic.moduleTensor.{a,a} A).map₂CochainComplex.obj
      ((F).obj Y)).map (nativeDualIso M P).hom)
    infer_instance
  letI : IsIso ((M.tensorIso Y (B P)).hom ≫ (F).map (chainCmp M P Y) ≫
      (M.homIso P Y).hom) := by
    rw [native_comparison M P Y]
    infer_instance
  letI : IsIso ((F).map (chainCmp M P Y) ≫ (M.homIso P Y).hom) :=
    IsIso.of_isIso_comp_left (M.tensorIso Y (B P)).hom _
  letI : IsIso ((F).map (chainCmp M P Y)) :=
    IsIso.of_isIso_comp_right _ (M.homIso P Y).hom
  exact isIso_of_reflects_iso (chainCmp M P Y) F

set_option maxHeartbeats 1000000 in
private theorem chainComparison_natural (P : compValue.{a} R) {Y Y' : compValue.{a} R}
    (g : Y ⟶ Y') :
    CochainTensor.map g (𝟙 (B P)) ≫ chainCmp M P Y' =
      chainCmp M P Y ≫ internalHomMapValue (𝟙 P) g := by
  apply CochainTensor.hom_ext
  intro j k n h y f
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [CochainTensor.map_on_pure]
  apply Cochain.ext
  intro i l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have he := DerivedFormalization.internalHomMap_apply (𝟙 P) g hl
    ((chainCmp M P Y).f n (Specs.DerivedFormalization.CochainTensor.pure Y (B P) h y f)) x
  erw [he]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  by_cases hk : i + k = 0
  · have hj : j = i + n := by omega
    subst j
    subst l
    erw [(chainFormulas M P Y').2.1 h hk (g.f _ y) f x, (chainFormulas M P Y).2.1 h hk y f x]
    exact ((g.f (i + n)).hom.map_smul _ _).symm
  · erw [(chainFormulas M P Y').2.2.1 h hl hk (g.f _ y) f x,
      (chainFormulas M P Y).2.2.1 h hl hk y f x, map_zero]

end Chain

section FlatLocalization

open Specs.DerivedFormalization.DerivedTensor (kFlatHomotopy flatQh flatObject)
open private kFlat_iff_monoidal from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedTensor

variable {M : AdequateModel e} (T : Specs.DerivedFormalization.DerivedTensor.Model M)

private def flatChain (R : Type u) [CommRing R] : ObjectProperty (compValue.{a} R) :=
  isKFlat

private theorem flatChainMonoidal (M : AdequateModel e) :
    letI := M.chainMonoidal
    (flatChain.{u,a} R).IsMonoidal := by
  letI := M.chainMonoidal
  refine { prop_unit := ?_, prop_tensor := ?_ }
  · change isKFlat (𝟙_ (compValue.{a} R))
    rw [kFlat_iff_monoidal M]
    intro E hE n
    exact (hE n).of_iso (ρ_ E).symm
  · intro P S hP hS
    change isKFlat P at hP
    change isKFlat S at hS
    change isKFlat (P ⊗ S)
    rw [kFlat_iff_monoidal M] at hP hS ⊢
    intro E hE n
    exact (hS _ (hP _ hE) n).of_iso (α_ E P S)

private def flatQuotient (R : Type u) [CommRing R] :
    (flatChain.{u,a} R).FullSubcategory ⥤ (kFlatHomotopy.{u,a} R).FullSubcategory :=
  (kFlatHomotopy.{u,a} R).lift ((flatChain.{u,a} R).ι ⋙ quotientValue.{a} R)
    (fun X => X.property)

@[instance_reducible]
private def flatQuotientMonoidal :
    letI := M.chainMonoidal
    letI := M.homotopyMonoidal
    letI := flatChainMonoidal M
    letI := T.flatMonoidal
    letI := M.chainSymmetric
    letI := M.homotopySymmetric
    letI := M.quotientBraided
    (flatQuotient.{u,a} R).Monoidal := by
  letI := M.chainMonoidal
  letI := M.homotopyMonoidal
  letI := flatChainMonoidal M
  letI := T.flatMonoidal
  letI := M.chainSymmetric
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  let q := quotientValue.{a} R
  apply Functor.CoreMonoidal.toMonoidal
  refine ⟨(kFlatHomotopy.{u,a} R).isoMk (Functor.Monoidal.εIso q),
    fun X Y => (kFlatHomotopy.{u,a} R).isoMk (Functor.Monoidal.μIso q X.obj Y.obj),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y f Z
    apply (kFlatHomotopy.{u,a} R).ι.map_injective
    exact Functor.LaxMonoidal.μ_natural_left q f.hom Z.obj
  · intro X Y Z f
    apply (kFlatHomotopy.{u,a} R).ι.map_injective
    exact Functor.LaxMonoidal.μ_natural_right q Z.obj f.hom
  · intro X Y Z
    apply (kFlatHomotopy.{u,a} R).ι.map_injective
    exact Functor.LaxMonoidal.associativity q X.obj Y.obj Z.obj
  · intro X
    apply (kFlatHomotopy.{u,a} R).ι.map_injective
    exact Functor.LaxMonoidal.left_unitality q X.obj
  · intro X
    apply (kFlatHomotopy.{u,a} R).ι.map_injective
    exact Functor.LaxMonoidal.right_unitality q X.obj

private abbrev flatDerived (R : Type u) [CommRing R] :
    (flatChain.{u,a} R).FullSubcategory ⥤ derivedValue.{a} R :=
  (flatChain.{u,a} R).ι ⋙ qValue.{a} R

@[instance_reducible]
private def flatDerivedMonoidal :
    letI := M.chainMonoidal
    letI := flatChainMonoidal M
    letI := T.monoidal
    (flatDerived.{u,a} R).Monoidal := by
  letI := M.chainMonoidal
  letI := M.homotopyMonoidal
  letI := flatChainMonoidal M
  letI := T.flatMonoidal
  letI := M.chainSymmetric
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := T.monoidal
  letI := T.symmetric
  letI := T.braided
  letI := flatQuotientMonoidal T
  let i : flatQuotient.{u,a} R ⋙ flatQh.{u,a} R ≅ flatDerived.{u,a} R :=
    Functor.isoWhiskerLeft (flatChain.{u,a} R).ι (quotientCompQhIsoValue.{a} R)
  exact (Functor.Monoidal.coreMonoidalTransport i).toMonoidal

private theorem flat_tensor_comparison :
    letI := M.chainMonoidal
    letI := flatChainMonoidal M
    letI := T.monoidal
    letI := flatDerivedMonoidal T
    ∀ X Y : (flatChain.{u,a} R).FullSubcategory,
      (T.compare X.obj Y.obj (Or.inl X.property)).hom =
        Functor.LaxMonoidal.μ (flatDerived.{u,a} R) X Y ≫
          (qValue.{a} R).map (M.tensorModel X.obj Y.obj).inv := by
  letI := M.chainMonoidal
  letI := M.homotopyMonoidal
  letI := flatChainMonoidal M
  letI := T.flatMonoidal
  letI := M.chainSymmetric
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := T.monoidal
  letI := T.symmetric
  letI := T.braided
  letI := flatQuotientMonoidal T
  letI := flatDerivedMonoidal T
  intro X Y
  let q := quotientCompQhIsoValue.{a} R
  rw [T.compare_flat X.obj Y.obj X.property Y.property]
  have hμ : Functor.LaxMonoidal.μ (flatDerived.{u,a} R) X Y =
      (q.inv.app X.obj ⊗ₘ q.inv.app Y.obj) ≫
      (Functor.LaxMonoidal.μ (flatQh.{u,a} R) (flatObject R _ X.property) (flatObject R _ Y.property) ≫
        (qhValue.{a} R).map (Functor.LaxMonoidal.μ (quotientValue.{a} R) X.obj Y.obj)) ≫
      q.hom.app (X.obj ⊗ Y.obj) := rfl
  rw [hμ]
  simp only [Category.assoc]
  rw [← q.hom.naturality]
  simp only [Specs.DerivedFormalization.DerivedTensor.Descent.flatComparison, Iso.trans_hom,
    tensorIso_hom, Iso.symm_hom, Iso.app_inv, Functor.Monoidal.μIso_hom, Functor.mapIso_hom,
    Functor.comp_map]
  rfl

private theorem flat_unit_comparison :
    letI := M.chainMonoidal
    letI := flatChainMonoidal M
    letI := T.monoidal
    letI := flatDerivedMonoidal T
    T.toDescent.unitComparison.hom = Functor.LaxMonoidal.ε (flatDerived.{u,a} R) ≫
      (qValue.{a} R).map M.unitModel.inv := by
  letI := M.chainMonoidal
  letI := M.homotopyMonoidal
  letI := flatChainMonoidal M
  letI := T.flatMonoidal
  letI := M.chainSymmetric
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := T.monoidal
  letI := T.symmetric
  letI := T.braided
  letI := flatQuotientMonoidal T
  letI := flatDerivedMonoidal T
  let q := quotientCompQhIsoValue.{a} R
  have hε : Functor.LaxMonoidal.ε (flatDerived.{u,a} R) =
      (Functor.LaxMonoidal.ε (flatQh.{u,a} R) ≫
        (qhValue.{a} R).map (Functor.LaxMonoidal.ε (quotientValue.{a} R))) ≫
      q.hom.app (𝟙_ (compValue.{a} R)) := rfl
  rw [hε]
  simp only [Category.assoc]
  rw [← q.hom.naturality]
  simp only [Specs.DerivedFormalization.DerivedTensor.Descent.unitComparison, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Functor.Monoidal.εIso_hom, Functor.mapIso_hom,
    Functor.comp_map]
  rfl

private theorem raw_tensor_flat (M : AdequateModel e) {X Y : compValue.{a} R}
    (hX : isKFlat X) (hY : isKFlat Y) : isKFlat (tensor X Y) := by
  letI := M.chainMonoidal
  letI := flatChainMonoidal M
  have h : isKFlat (X ⊗ Y) := ObjectProperty.prop_tensor
    (P₁ := flatChain.{u,a} R) (P₂ := flatChain.{u,a} R) (Q := flatChain.{u,a} R)
    (X₁ := X) (X₂ := Y) hX hY
  exact fun E hE n => ((h E hE) n).of_iso (M.tensorModel E _ ≪≫
    tensorIso (Iso.refl E) (M.tensorModel X Y).symm ≪≫ (M.tensorModel E _).symm)

private theorem localization_preserves_contraction {C K : Type*} [Category* C] [Category* K]
    [MonoidalCategory C] [MonoidalCategory K] (F : C ⥤ K) [F.Monoidal]
    (Y B P : C) (f : B ⊗ P ⟶ 𝟙_ C) :
    let μ := Functor.LaxMonoidal.μ F
    let η := Functor.OplaxMonoidal.η F
    (μ Y B ▷ F.obj P) ≫ μ (Y ⊗ B) P ≫ F.map ((α_ Y B P).hom ≫ Y ◁ f ≫ (ρ_ Y).hom) =
      (α_ (F.obj Y) (F.obj B) (F.obj P)).hom ≫
        F.obj Y ◁ (μ B P ≫ F.map f ≫ η) ≫ (ρ_ (F.obj Y)).hom := by
  dsimp only
  simp only [Functor.map_comp, Category.assoc, Functor.LaxMonoidal.associativity_assoc,
    Functor.Monoidal.map_whiskerLeft_assoc, Functor.Monoidal.map_rightUnitor,
    Functor.Monoidal.μ_δ_assoc, whiskerLeft_comp]

set_option hygiene false in
local notation "Q" => (qValue.{a} R)

set_option maxHeartbeats 1500000 in
private theorem contraction_on_flat (Y B P : compValue.{a} R)
    (hY : isKFlat Y) (hB : isKFlat B) (hP : isKFlat P)
    (f : tensor B P ⟶ representedUnit e) :
    letI := M.chainMonoidal
    letI := T.monoidal
    let V := tensor Y B
    let hV := raw_tensor_flat M hY hB
    let f' := (M.tensorModel B P).inv ≫ f ≫ M.unitModel.hom
    let g := (M.tensorModel V P).hom ≫ (M.tensorModel Y B).hom ▷ P ≫
      (α_ Y B P).hom ≫ Y ◁ f' ≫ (ρ_ Y).hom
    (T.compare Y B (Or.inl hY)).hom ▷ (Q).obj P ≫
        (T.compare V P (Or.inl hV)).hom ≫ (Q).map g =
      (α_ ((Q).obj Y) ((Q).obj B) ((Q).obj P)).hom ≫
        (Q).obj Y ◁ ((T.compare B P (Or.inl hB)).hom ≫ (Q).map f ≫ T.unitComparison.inv) ≫
        (ρ_ ((Q).obj Y)).hom := by
  letI := M.chainMonoidal
  letI := T.monoidal
  letI := flatChainMonoidal M
  letI := flatDerivedMonoidal T
  let V := tensor Y B
  let hV := raw_tensor_flat M hY hB
  let y : (flatChain.{u,a} R).FullSubcategory := ⟨Y, hY⟩
  let b : (flatChain.{u,a} R).FullSubcategory := ⟨B, hB⟩
  let p : (flatChain.{u,a} R).FullSubcategory := ⟨P, hP⟩
  let v : (flatChain.{u,a} R).FullSubcategory := ⟨V, hV⟩
  let F := flatDerived.{u,a} R
  let f' : b ⊗ p ⟶ 𝟙_ (flatChain.{u,a} R).FullSubcategory :=
    ObjectProperty.homMk ((M.tensorModel B P).inv ≫ f ≫ M.unitModel.hom)
  let r : y ⊗ b ⟶ v := ObjectProperty.homMk (M.tensorModel Y B).inv
  have ε := flat_unit_comparison T
  have η : T.unitComparison.inv = (Q).map M.unitModel.hom ≫ Functor.OplaxMonoidal.η F := by
    apply (cancel_epi T.unitComparison.hom).1
    rw [Iso.hom_inv_id, ε]
    simp only [Category.assoc, ← (Q).map_comp_assoc, Iso.inv_hom_id, (Q).map_id,
      Category.id_comp]
    exact (Functor.Monoidal.ε_η F).symm
  have n := Functor.LaxMonoidal.μ_natural_left F r p
  dsimp only
  rw [flat_tensor_comparison T y b, flat_tensor_comparison T v p, flat_tensor_comparison T b p, η]
  simp only [Category.assoc, comp_whiskerRight]
  have n' : (Q).map (M.tensorModel Y B).inv ▷ (Q).obj P ≫ Functor.LaxMonoidal.μ F v p =
      Functor.LaxMonoidal.μ F (y ⊗ b) p ≫ (Q).map ((M.tensorModel Y B).inv ▷ P) := n
  rw [reassoc_of% n']
  repeat rw [← (Q).map_comp_assoc]
  rw [← (Q).map_comp]
  simp only [v, p, V]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, Category.id_comp]
  exact localization_preserves_contraction F y b p f' 

private theorem contraction_natural_iso {K : Type*} [Category* K] [MonoidalCategory K]
    {Y B P Y' B' P' : K} (y : Y ⟶ Y') (b : B ⟶ B') (p : P ⟶ P')
    (f : B' ⊗ P' ⟶ 𝟙_ K) :
    ((y ⊗ₘ b) ⊗ₘ p) ≫ (α_ Y' B' P').hom ≫ Y' ◁ f ≫ (ρ_ Y').hom =
      (α_ Y B P).hom ≫ Y ◁ ((b ⊗ₘ p) ≫ f) ≫ (ρ_ Y).hom ≫ y := by
  rw [associator_naturality_assoc, ← rightUnitor_naturality, ← id_tensorHom Y',
    ← id_tensorHom Y, ← tensorHom_id]
  simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]


set_option maxHeartbeats 900000 in
private theorem unitor_on_flat (P : compValue.{a} R) (hP : isKFlat P) :
    letI := M.chainMonoidal
    letI := T.monoidal
    let U := representedUnit e
    let g := (M.tensorModel U P).hom ≫ M.unitModel.hom ▷ P ≫ (λ_ P).hom
    T.unitComparison.hom ▷ (Q).obj P ≫ (T.compare U P (Or.inr hP)).hom ≫ (Q).map g =
      (λ_ ((Q).obj P)).hom := by
  letI := M.chainMonoidal
  letI := T.monoidal
  letI := flatChainMonoidal M
  letI := flatDerivedMonoidal T
  let U := representedUnit e
  have hU : isKFlat U := (kFlat_iff_monoidal M U).2
    (fun E hE n => (hE n).of_iso ((ρ_ E).symm ≪≫ tensorIso (Iso.refl E) M.unitModel.symm))
  let p : (flatChain.{u,a} R).FullSubcategory := ⟨P, hP⟩
  let u : (flatChain.{u,a} R).FullSubcategory := ⟨U, hU⟩
  let F := flatDerived.{u,a} R
  let f : 𝟙_ (flatChain.{u,a} R).FullSubcategory ⟶ u := ObjectProperty.homMk M.unitModel.inv
  have n := Functor.LaxMonoidal.μ_natural_left F f p
  dsimp only
  erw [flat_unit_comparison T, flat_tensor_comparison T u p]
  simp only [comp_whiskerRight, Category.assoc]
  have n' : (Q).map M.unitModel.inv ▷ (Q).obj P ≫ Functor.LaxMonoidal.μ F u p =
      Functor.LaxMonoidal.μ F (𝟙_ (flatChain.{u,a} R).FullSubcategory) p ≫ (Q).map (M.unitModel.inv ▷ P) := n
  rw [reassoc_of% n']
  repeat rw [← (Q).map_comp_assoc]
  rw [← (Q).map_comp]
  simp only [u, p, U]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
    Category.id_comp]
  exact (Functor.LaxMonoidal.left_unitality F p).symm

end FlatLocalization

/-- The second triangle follows from the first when evaluation is the counit at the unit. -/
@[instance_reducible]
private def exactPairingOfCounit {C : Type*} [Category* C] [MonoidalCategory C] {P B : C}
    (ev : B ⊗ P ⟶ 𝟙_ C) (coev : 𝟙_ C ⟶ P ⊗ B)
    (hP : coev ▷ P ≫ (α_ P B P).hom ≫ P ◁ ev ≫ (ρ_ P).hom = (λ_ P).hom)
    (inj : Function.Injective (fun f : B ⟶ B => f ▷ P ≫ ev)) : ExactPairing P B where
  evaluation' := ev
  coevaluation' := coev
  evaluation_coevaluation' := by
    apply (Iso.eq_comp_inv (ρ_ P)).2
    simpa only [Category.assoc] using hP
  coevaluation_evaluation' := by
    let f := B ◁ coev ≫ (α_ B P B).inv ≫ ev ▷ B
    have h : (ρ_ B).inv ≫ f ≫ (λ_ B).hom = 𝟙 B := by
      apply inj
      simp only [id_whiskerRight, Category.id_comp]
      let u : B ⊗ P ⟶ (B ⊗ P) ⊗ (B ⊗ P) :=
        (ρ_ B).inv ▷ P ≫ (B ◁ coev) ▷ P ≫ (α_ B P B).inv ▷ P ≫
          (α_ (B ⊗ P) B P).hom
      calc
        ((ρ_ B).inv ≫ f ≫ (λ_ B).hom) ▷ P ≫ ev =
            u ≫ ev ▷ (B ⊗ P) ≫ 𝟙_ C ◁ ev ≫ (λ_ (𝟙_ C)).hom := by
          dsimp only [u, f]
          monoidal
        _ = u ≫ (B ⊗ P) ◁ ev ≫ ev ▷ (𝟙_ C) ≫ (λ_ (𝟙_ C)).hom := by
          rw [whisker_exchange_assoc]
        _ = B ◁ (λ_ P).inv ≫
            B ◁ (coev ▷ P ≫ (α_ P B P).hom ≫ P ◁ ev ≫ (ρ_ P).hom) ≫ ev := by
          dsimp only [u]
          monoidal
        _ = ev := by rw [hP, ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
    change f = (ρ_ B).hom ≫ (λ_ B).inv
    apply (cancel_epi (ρ_ B).inv).1
    apply (cancel_mono (λ_ B).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id] using h


section Derived

open private presentationOf overIntoInjective homComparison_natural tensorComparison_natural
  existsProjectiveFlat from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomAdjunction

variable {M : AdequateModel e} {T : Specs.DerivedFormalization.DerivedTensor.Model M}
  {H : Models.{u,a} R} (c : Closed T H)

set_option hygiene false in
local notation "D" => (derivedValue.{a} R)
set_option hygiene false in
local notation "Q" => (qValue.{a} R)
local notation "DH" => rHomValue H

private theorem homComparison_projective {X Y : D} (P : Presentation X) (S : Presentation Y)
    (hP : P.complex.IsKProjective) : IsIso (homComparison H P S) :=
  (DerivedHomModels.modelIso H P.representative S.representative (Or.inl hP)).isIso_hom

set_option maxHeartbeats 1000000 in
private theorem closed_on_presentations {Z X Y : D}
    (S : Presentation Z) (P : Presentation X) (I : Presentation Y)
    (hP : isKFlat P.complex) (kP : P.complex.IsKProjective)
    (f : tensor S.complex P.complex ⟶ I.complex) :
    c.equiv Z X Y ((tensorComparison T S P hP).hom ≫ (Q).map f ≫ I.iso.hom) =
      S.iso.inv ≫ (Q).map ((M.rawClosed P.complex).adj.homEquiv _ _ f) ≫ homComparison H P I := by
  let J := presentationOf (H.injective Y)
  have hJ : J.complex.IsKInjective := H.isInjective Y
  obtain ⟨g, hg⟩ := overIntoInjective I J hJ (𝟙 Y)
  have hg' : (Q).map g ≫ J.iso.hom = I.iso.hom := by simpa [Presentation.Over] using hg
  have hi : P.Over P (𝟙 X) (𝟙 P.complex) := by simp [Presentation.Over]
  have hn := homComparison_natural H P P I J (Or.inl kP) (Or.inr hJ)
    (𝟙 P.complex) g hi hg
  change (Q).map (internalHomMapValue (𝟙 P.complex) g) ≫ homComparison H P J =
    homComparison H P I ≫ (DH).map (𝟙 _) at hn
  rw [(DH).map_id, Category.comp_id] at hn
  have h := c.on_models S P J hP hJ (f ≫ g)
  rw [(Q).map_comp, Category.assoc, hg'] at h
  rw [h]
  rw [Adjunction.homEquiv_naturality_right, (Q).map_comp]
  simp only [Category.assoc]
  erw [hn]

private theorem presentedTensor_eq {X Y : D} (P : Presentation X) (S : Presentation Y)
    (h : isKFlat S.complex) :
    presentedTensor T P S (Or.inr h) = tensorComparison T P S h := by
  rfl

private theorem computed_evaluation {X : D} (P : Presentation X)
    (hP : isKFlat P.complex) (kP : P.complex.IsKProjective) (hB : isKFlat (Specs.DerivedFormalization.PerfectDuals.chainDual e P.complex))
    (h : IsIso (homComparison H P (unitPresentation T))) :
    let L := dualPresentation T H P h
    evaluation c X =
      (presentedTensor T L P (Or.inl hB)).hom ≫
        (Q).map (Specs.DerivedFormalization.PerfectDuals.chainEvaluation M P.complex) ≫
        (unitPresentation T).iso.hom := by
  letI := T.monoidal
  let L := dualPresentation T H P h
  let I := unitPresentation T
  apply (c.equiv (dualValue T H X) X (𝟙_ D)).injective
  change c.equiv _ _ _ ((c.equiv _ _ _).symm (𝟙 _)) =
    c.equiv _ _ _ ((presentedTensor T L P (Or.inl hB)).hom ≫ _)
  rw [LinearEquiv.apply_symm_apply]
  rw [show (Or.inl hB : isKFlat L.complex ∨ isKFlat P.complex) = Or.inr hP from Subsingleton.elim _ _,
    presentedTensor_eq L P hP]
  erw [closed_on_presentations c L P I hP kP]
  unfold Specs.DerivedFormalization.PerfectDuals.chainEvaluation
  let adj := (M.rawClosed P.complex).adj
  have hc : adj.homEquiv L.complex I.complex (adj.counit.app I.complex) = 𝟙 L.complex := by
    rw [← adj.homEquiv_symm_id I.complex]
    exact (adj.homEquiv L.complex I.complex).apply_symm_apply (𝟙 _)
  erw [hc, (Q).map_id, Category.id_comp]
  exact L.iso.inv_hom_id.symm

private theorem evaluation_natural {P P' : D} (f : P' ⟶ P) :
    letI := T.monoidal
    let b := (DH).map (Prod.mkHom f.op (𝟙 (𝟙_ D)))
    (b ▷ P') ≫ evaluation c P' = (dualValue T H P ◁ f) ≫ evaluation c P := by
  letI := T.monoidal
  let b := (DH).map (Prod.mkHom f.op (𝟙 (𝟙_ D)))
  apply (c.equiv (dualValue T H P) P' (𝟙_ D)).injective
  have h1 := c.natural b (𝟙 P') (𝟙 (𝟙_ D)) (evaluation c P')
  have h2 := c.natural (𝟙 (dualValue T H P)) f (𝟙 (𝟙_ D)) (evaluation c P)
  change c.equiv _ _ _ ((b ⊗ₘ 𝟙 P') ≫ evaluation c P' ≫ 𝟙 _) =
    b ≫ c.equiv _ _ _ (evaluation c P') ≫ (DH).map (𝟙 _) at h1
  change c.equiv _ _ _ ((𝟙 _ ⊗ₘ f) ≫ evaluation c P ≫ 𝟙 _) =
    𝟙 _ ≫ c.equiv _ _ _ (evaluation c P) ≫ b at h2
  simp only [tensorHom_id, id_tensorHom, Category.comp_id, Category.id_comp, (rHomValue H).map_id] at h1 h2
  have he (W : D) : c.equiv (dualValue T H W) W (𝟙_ D) (evaluation c W) = 𝟙 _ :=
    (c.equiv (dualValue T H W) W (𝟙_ D)).apply_symm_apply (𝟙 _)
  erw [he P', Category.comp_id] at h1
  erw [he P, Category.id_comp] at h2
  exact h1.trans h2.symm

set_option maxHeartbeats 850000 in
private theorem comparison_natural {P P' Y Y' : D} (f : P' ⟶ P) (g : Y ⟶ Y') :
    letI := T.monoidal
    (g ⊗ₘ (DH).map (Prod.mkHom f.op (𝟙 (𝟙_ D)))) ≫ evaluationComparison c P' Y' =
      evaluationComparison c P Y ≫ (DH).map (Prod.mkHom f.op g) := by
  letI := T.monoidal
  let B := dualValue T H P
  let B' := dualValue T H P'
  let b : B ⟶ B' := (DH).map (Prod.mkHom f.op (𝟙 (𝟙_ D)))
  let w := (α_ Y B P).hom ≫ Y ◁ evaluation c P ≫ (ρ_ Y).hom
  let w' := (α_ Y' B' P').hom ≫ Y' ◁ evaluation c P' ≫ (ρ_ Y').hom
  have h1 := c.natural (g ⊗ₘ b) (𝟙 P') (𝟙 Y') w'
  have h2 := c.natural (𝟙 (Y ⊗ B)) f g w
  change c.equiv _ _ _ (((g ⊗ₘ b) ⊗ₘ 𝟙 P') ≫ w' ≫ 𝟙 Y') =
    (g ⊗ₘ b) ≫ evaluationComparison c P' Y' ≫ (DH).map (𝟙 _) at h1
  change c.equiv _ _ _ ((𝟙 (Y ⊗ B) ⊗ₘ f) ≫ w ≫ g) =
    𝟙 (Y ⊗ B) ≫ evaluationComparison c P Y ≫ (DH).map (Prod.mkHom f.op g) at h2
  simp only [(rHomValue H).map_id, Category.comp_id, Category.id_comp] at h1 h2
  erw [← h1, ← h2]
  congr 1
  dsimp only [w, w']
  have ha := associator_naturality g b (𝟙 P')
  have ha' := associator_naturality (𝟙 Y) (𝟙 B) f
  rw [id_tensorHom_id] at ha'
  simp only [Category.assoc]
  rw [reassoc_of% ha, reassoc_of% ha',
    ← rightUnitor_naturality]
  rw [← id_tensorHom Y', ← id_tensorHom Y, ← tensorHom_id g]
  simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  rw [tensorHom_id b, id_tensorHom B, evaluation_natural c f]

private theorem computed_biduality {X : D} (P : Presentation X)
    (hP : isKFlat P.complex) (kP : P.complex.IsKProjective)
    (hB : isKFlat (Specs.DerivedFormalization.PerfectDuals.chainDual e P.complex))
    (kB : (Specs.DerivedFormalization.PerfectDuals.chainDual e P.complex).IsKProjective)
    (h : IsIso (homComparison H P (unitPresentation T))) :
    let L := dualPresentation T H P h
    biduality c X = P.iso.inv ≫ (Q).map (chainBiduality M P.complex) ≫
      homComparison H L (unitPresentation T) := by
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := T.monoidal
  letI := T.symmetric
  let L := dualPresentation T H P h
  let I := unitPresentation T
  let b := M.tensorModel P.complex L.complex ≪≫ β_ P.complex L.complex ≪≫
    (M.tensorModel L.complex P.complex).symm
  have hb := (DerivedTensor.braidingOnModels T.toDescent P.complex L.complex hP hB).1
  have hb' : (β_ X (dualValue T H X)).hom ≫
          (presentedTensor T L P (Or.inl hB)).hom =
        (tensorComparison T P L hB).hom ≫ (Q).map b.hom := by
    rw [← presentedTensor_eq P L hB]
    unfold presentedTensor
    simp only [Iso.trans_hom, Iso.symm_hom]
    have h1 : T.compare P.complex L.complex (Or.inr hB) =
        T.toDescent.flatComparison P.complex L.complex hP hB :=
      T.compare_flat P.complex L.complex hP hB
    erw [h1, T.compare_flat L.complex P.complex hB hP]
    have hn := BraidedCategory.braiding_naturality P.iso.inv L.iso.inv
    simp only [tensorIso_inv, Category.assoc]
    change (β_ X (dualValue T H X)).hom ≫ (L.iso.inv ⊗ₘ P.iso.inv) ≫ _ = _
    rw [← reassoc_of% hn, hb]
  unfold biduality
  rw [computed_evaluation c P hP kP hB h]
  change c.equiv X (dualValue T H X) (𝟙_ D)
    ((β_ X (dualValue T H X)).hom ≫ (presentedTensor T L P (Or.inl hB)).hom ≫
      (Q).map (Specs.DerivedFormalization.PerfectDuals.chainEvaluation M P.complex) ≫ I.iso.hom) = _
  rw [reassoc_of% hb', ← (Q).map_comp_assoc]
  erw [closed_on_presentations c P L I hB kB]
  rfl

set_option maxHeartbeats 1500000 in
private theorem computed_comparison_of_flat {X Y : D} (P : Presentation X) (S : Presentation Y)
    (hP : isKFlat P.complex) (kP : P.complex.IsKProjective)
    (hB : isKFlat (Specs.DerivedFormalization.PerfectDuals.chainDual e P.complex))
    (hS : isKFlat S.complex) (h : IsIso (homComparison H P (unitPresentation T))) :
    let L := dualPresentation T H P h
    evaluationComparison c X Y =
      (presentedTensor T S L (Or.inr hB)).hom ≫
        (Q).map (chainComparison M P.complex S.complex) ≫ homComparison H P S := by
  letI := M.chainMonoidal
  letI := T.monoidal
  let L := dualPresentation T H P h
  let f := Specs.DerivedFormalization.PerfectDuals.chainEvaluation M P.complex
  let V := tensor S.complex L.complex
  let τ := presentedTensor T S L (Or.inr hB)
  let K : Presentation (Y ⊗ dualValue T H X) := ⟨V, τ.symm⟩
  let hV := raw_tensor_flat M hS hB
  let g : tensor V P.complex ⟶ S.complex :=
    (M.tensorModel V P.complex).hom ≫ (M.tensorModel S.complex L.complex).hom ▷ P.complex ≫
      (α_ S.complex L.complex P.complex).hom ≫
      S.complex ◁ ((M.tensorModel L.complex P.complex).inv ≫ f ≫ M.unitModel.hom) ≫
      (ρ_ S.complex).hom
  have hg :
      (tensorComparison T K P hP).hom ≫ (Q).map g ≫ S.iso.hom =
        (α_ Y (dualValue T H X) X).hom ≫ Y ◁ evaluation c X ≫ (ρ_ Y).hom := by
    have h₁ : (tensorComparison T K P hP).hom =
        ((S.iso.inv ⊗ₘ L.iso.inv) ⊗ₘ P.iso.inv) ≫
          (T.compare S.complex L.complex (Or.inl hS)).hom ▷ (Q).obj P.complex ≫
          (T.compare V P.complex (Or.inl hV)).hom := by
      rw [← presentedTensor_eq K P hP]
      simp only [presentedTensor, Iso.trans_hom, Iso.symm_hom, tensorIso_inv]
      change ((τ.hom ⊗ₘ P.iso.inv)) ≫ _ = _
      simp only [τ, presentedTensor, Iso.trans_hom, Iso.symm_hom, tensorIso_inv]
      let a := S.iso.inv ⊗ₘ L.iso.inv
      let b := (T.compare S.complex L.complex (Or.inl hS)).hom
      have hab : ((a ≫ b) ⊗ₘ P.iso.inv) =
          (a ⊗ₘ P.iso.inv) ≫ b ▷ (Q).obj P.complex := by
        rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
      erw [hab]
      simp only [Category.assoc]
      rfl
    have h₂ := contraction_on_flat T S.complex L.complex P.complex hS hB hP f
    dsimp only at h₂
    have h₃ :
        (L.iso.inv ⊗ₘ P.iso.inv) ≫ (T.compare L.complex P.complex (Or.inl hB)).hom ≫
          (Q).map f ≫ T.unitComparison.inv = evaluation c X := by
      rw [computed_evaluation c P hP kP hB h]
      simp only [presentedTensor, Iso.trans_hom, Iso.symm_hom, tensorIso_inv, Category.assoc]
      rfl
    rw [h₁]
    simp only [Category.assoc]
    rw [reassoc_of% h₂, reassoc_of% (contraction_natural_iso S.iso.inv L.iso.inv P.iso.inv _), h₃,
      Iso.inv_hom_id, Category.comp_id]
  unfold evaluationComparison
  erw [← hg, closed_on_presentations c K P S hP kP]
  rfl

open private overOfProjective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomAdjunction

set_option maxHeartbeats 1000000 in
private theorem computed_comparison {X Y : D} (P : Presentation X) (S : Presentation Y)
    (hP : isKFlat P.complex) (kP : P.complex.IsKProjective)
    (hB : isKFlat (Specs.DerivedFormalization.PerfectDuals.chainDual e P.complex))
    (h : IsIso (homComparison H P (unitPresentation T))) :
    let L := dualPresentation T H P h
    evaluationComparison c X Y =
      (presentedTensor T S L (Or.inr hB)).hom ≫
        (Q).map (chainComparison M P.complex S.complex) ≫ homComparison H P S := by
  letI : Small.{a} R := small_of_injective e.injective
  let L := dualPresentation T H P h
  obtain ⟨S', kS', hS'⟩ := existsProjectiveFlat Y
  obtain ⟨g, hg⟩ := overOfProjective S' S kS' (𝟙 Y)
  have hL : L.Over L (𝟙 _) (𝟙 _) := by simp [Presentation.Over]
  have hP' : P.Over P (𝟙 _) (𝟙 _) := by simp [Presentation.Over]
  have ht := tensorComparison_natural T S S' L L hB hB g (𝟙 L.complex) hg hL
  have hh := homComparison_natural H P P S' S (Or.inl kP) (Or.inl kP)
    (𝟙 P.complex) g hP' hg
  change T.tensorFunctor.map (𝟙 _) ≫ _ = _ at ht
  change _ = homComparison H P S' ≫ (DH).map (𝟙 _) at hh
  rw [T.tensorFunctor.map_id, Category.id_comp] at ht
  rw [(DH).map_id, Category.comp_id] at hh
  dsimp only
  erw [computed_comparison_of_flat c P S' hP kP hB hS' h, presentedTensor_eq S' L hB,
    presentedTensor_eq S L hB, ht]
  simp only [Category.assoc]
  erw [← (Q).map_comp_assoc, chainComparison_natural M P.complex g]
  have hmap := (Q).map_comp (chainComparison M P.complex S'.complex) (internalHomMapValue (𝟙 P.complex) g)
  erw [reassoc_of% hmap, hh]

private theorem comparison_isIso {X Y : D} (P : Presentation X) (S : Presentation Y)
    (h : isBoundedFiniteProjectiveValue P.complex) :
    IsIso (evaluationComparison c X Y) := by
  have kP := projective_model P.complex h
  have hb := bounded_dual M P.complex h
  have hP := flat_model P.complex h
  have hB := flat_model _ hb
  have hH := homComparison_projective P (unitPresentation T) kP (H := H)
  haveI := homComparison_projective P S kP (H := H)
  haveI := chainComparison_isIso M P.complex S.complex h
  rw [computed_comparison c P S hP kP hB hH]
  infer_instance

set_option maxHeartbeats 1500000 in
private theorem computed_coevaluation {X : D} (P : Presentation X)
    (hP : isKFlat P.complex) (kP : P.complex.IsKProjective)
    (hB : isKFlat (Specs.DerivedFormalization.PerfectDuals.chainDual e P.complex))
    (h : IsIso (homComparison H P (unitPresentation T)))
    (hC : IsIso (chainComparison M P.complex P.complex))
    (hD : IsIso (evaluationComparison c X X)) :
    let L := dualPresentation T H P h
    coevaluation c X hD =
      (unitPresentation T).iso.inv ≫ (Q).map (Specs.DerivedFormalization.PerfectDuals.chainCoevaluation M P.complex hC) ≫
        (presentedTensor T P L (Or.inl hP)).inv := by
  letI := M.chainMonoidal
  letI := T.monoidal
  letI := hC
  letI := hD
  let I := unitPresentation T
  let L := dualPresentation T H P h
  let g : tensor I.complex P.complex ⟶ P.complex :=
    (M.tensorModel I.complex P.complex).hom ≫ M.unitModel.hom ▷ P.complex ≫ (λ_ P.complex).hom
  let k := (M.rawClosed P.complex).adj.homEquiv _ _ g
  have hg :
      (tensorComparison T I P hP).hom ≫ (Q).map g ≫ P.iso.hom = (λ_ X).hom := by
    rw [← presentedTensor_eq I P hP]
    simp only [presentedTensor, Iso.trans_hom, Iso.symm_hom, tensorIso_inv, Category.assoc]
    change (T.unitComparison.hom ⊗ₘ P.iso.inv) ≫ _ = _
    rw [tensorHom_def']
    simp only [Category.assoc]
    erw [reassoc_of% (unitor_on_flat T P.complex hP),
      leftUnitor_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have hk :
      c.equiv (𝟙_ D) X X (λ_ X).hom = I.iso.inv ≫ (Q).map k ≫ homComparison H P P := by
    rw [← hg]
    exact closed_on_presentations c I P P hP kP g
  let τ := presentedTensor T P L (Or.inl hP)
  have hcmp : evaluationComparison c X X =
      τ.hom ≫ (Q).map (chainComparison M P.complex P.complex) ≫ homComparison H P P :=
    computed_comparison c P P hP kP hB h
  dsimp only
  apply (cancel_mono (evaluationComparison c X X)).1
  unfold coevaluation
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, hk]
  rw [hcmp]
  simp only [Category.assoc]
  change _ = I.iso.inv ≫ (Q).map (Specs.DerivedFormalization.PerfectDuals.chainCoevaluation M P.complex hC) ≫
    τ.inv ≫ τ.hom ≫ (Q).map (chainComparison M P.complex P.complex) ≫ homComparison H P P
  rw [Iso.inv_hom_id_assoc, ← (Q).map_comp_assoc]
  unfold Specs.DerivedFormalization.PerfectDuals.chainCoevaluation
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rfl

set_option maxHeartbeats 900000 in
private theorem derived_pairing {P : D} (h : IsIso (evaluationComparison c P P)) :
    letI := T.monoidal
    ∃ a : ExactPairing P (dualValue T H P),
      a.evaluation' = evaluation c P ∧ a.coevaluation' = coevaluation c P h := by
  letI := T.monoidal
  letI := h
  let B := dualValue T H P
  let v := evaluation c P
  let u := coevaluation c P h
  let w := (α_ P B P).hom ≫ P ◁ v ≫ (ρ_ P).hom
  have h₁ : u ▷ P ≫ (α_ P B P).hom ≫ P ◁ v ≫ (ρ_ P).hom = (λ_ P).hom := by
    apply (c.equiv (𝟙_ D) P P).injective
    have hw := c.natural u (𝟙 P) (𝟙 P) w
    change c.equiv _ _ _ ((u ⊗ₘ 𝟙 P) ≫ w ≫ 𝟙 P) =
      u ≫ evaluationComparison c P P ≫ (DH).map (𝟙 _) at hw
    simp only [tensorHom_id, (DH).map_id, Category.comp_id] at hw
    change c.equiv _ _ _ (u ▷ P ≫ w) = _
    erw [hw]
    unfold u coevaluation
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have inj : Function.Injective (fun f : B ⟶ B => f ▷ P ≫ v) := by
    intro f g hfg
    have ident (f : B ⟶ B) : c.equiv B P (𝟙_ D) (f ▷ P ≫ v) = f := by
      have hf := c.natural f (𝟙 P) (𝟙 (𝟙_ D)) v
      change c.equiv _ _ _ ((f ⊗ₘ 𝟙 P) ≫ v ≫ 𝟙 _) =
        f ≫ c.equiv B P (𝟙_ D) v ≫ (DH).map (𝟙 _) at hf
      simp only [tensorHom_id, (DH).map_id, Category.comp_id] at hf
      have hv : c.equiv B P (𝟙_ D) v = 𝟙 _ :=
        (c.equiv B P (𝟙_ D)).apply_symm_apply (𝟙 _)
      erw [hf, hv, Category.comp_id]
    exact (ident f).symm.trans ((congrArg (c.equiv B P (𝟙_ D)) hfg).trans (ident g))
  exact ⟨exactPairingOfCounit v u h₁ inj, rfl, rfl⟩

set_option maxHeartbeats 1200000 in
private theorem biduality_isIso_of_pairing {P : D} :
    letI := T.monoidal
    ∀ a : ExactPairing P (dualValue T H P),
      a.evaluation' = evaluation c P → IsIso (biduality c P) := by
  letI := T.monoidal
  letI := T.symmetric
  intro a ha
  let B := dualValue T H P
  letI : ExactPairing P B := a
  letI : ExactPairing B P := BraidedCategory.exactPairing_swap P B
  let adj₀ := CategoryTheory.tensorRightAdjunction B P
  let j : MonoidalCategory.tensorRight B ≅ Specs.DerivedFormalization.DerivedHomAdjunction.tensorRight T B :=
    NatIso.ofComponents (fun Z => Iso.refl (Z ⊗ B)) (by
      intro Z Z' g
      change g ▷ B ≫ 𝟙 _ = 𝟙 _ ≫ (g ⊗ₘ 𝟙 B)
      simp only [Category.comp_id, Category.id_comp, tensorHom_id])
  let adj := adj₀.ofNatIsoLeft j
  let i : 𝟙_ D ⊗ P ≅ dualValue T H B := (Adjunction.rightAdjointUniq adj (c.adjunction B)).app (𝟙_ D)
  have he : biduality c P = (λ_ P).inv ≫ i.hom := by
    apply ((c.adjunction B).homEquiv P (𝟙_ D)).symm.injective
    have h := (c.adjunction B).homEquiv_naturality_left_symm (λ_ P).inv i.hom
    rw [h]
    unfold i
    have hu := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adj (c.adjunction B) (𝟙_ D)
    erw [hu]
    have hb : ((c.adjunction B).homEquiv P (𝟙_ D)).symm (biduality c P) =
        (β_ P B).hom ≫ evaluation c P := by
      erw [Specs.DerivedFormalization.DerivedHomAdjunction.Closed.adjunction_homEquiv]
      exact (c.equiv P B (𝟙_ D)).symm_apply_apply _
    have hcounit : adj.counit.app (𝟙_ D) = adj₀.counit.app (𝟙_ D) := by
      change (𝟙 _) ≫ adj₀.counit.app (𝟙_ D) = _
      exact Category.id_comp _
    erw [hb, hcounit, ← adj₀.homEquiv_symm_id]
    simp only [adj₀, CategoryTheory.tensorRightAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
      CategoryTheory.tensorRightHomEquiv, Equiv.coe_fn_symm_mk, id_whiskerRight, Category.id_comp]
    have hv : ExactPairing.evaluation B P = (β_ P B).hom ≫ evaluation c P :=
      congrArg ((β_ P B).hom ≫ ·) ha
    rw [hv]
    have hmap :
        (Specs.DerivedFormalization.DerivedHomAdjunction.tensorRight T B).map (λ_ P).inv =
          (λ_ P).inv ▷ B := tensorHom_id (λ_ P).inv B
    rw [hmap]
    monoidal
  rw [he]
  infer_instance

theorem modelComputation : ModelComputation.{u,a} := by
  intro R _ A _ e M T H c X Y P S hp
  have hb := bounded_dual M P.complex hp
  have kP := projective_model P.complex hp
  have kB := projective_model _ hb
  have hP := flat_model P.complex hp
  have hB := flat_model _ hb
  have hH := homComparison_projective P (unitPresentation T) kP (H := H)
  have hC := chainComparison_isIso M P.complex P.complex hp
  have hD := comparison_isIso c P P hp
  refine ⟨hb, kP, kB, hP, hB, hH, hC, hD, ?_, ?_, ?_, ?_⟩
  · exact computed_evaluation c P hP kP hB hH
  · exact computed_comparison c P S hP kP hB hH
  · exact computed_coevaluation c P hP kP hB hH hC hD
  · exact computed_biduality c P hP kP hB kB hH

theorem perfectDuality : PerfectDuality.{u,a} := by
  intro R _ A _ e M T H c
  letI := T.monoidal
  refine ⟨fun f g => comparison_natural c f g, ?_⟩
  intro X hp
  obtain ⟨P, hP, ⟨i⟩⟩ := hp
  let P' : Presentation X := ⟨P, i.symm⟩
  have h := homComparison_projective P' (unitPresentation T) (projective_model P hP) (H := H)
  let L := dualPresentation T H P' h
  have hCmp (Y : derivedValue.{a} R) : IsIso (evaluationComparison c X Y) := by
    let S : Presentation Y := ⟨(qValue R).objPreimage Y, (qValue R).objObjPreimageIso Y⟩
    exact comparison_isIso c P' S hP
  obtain ⟨pairing, he, hc⟩ := derived_pairing c (hCmp X)
  exact ⟨⟨L.complex, bounded_dual M P hP, ⟨L.iso.symm⟩⟩, hCmp,
    ⟨pairing, he, hCmp X, hc⟩, biduality_isIso_of_pairing c pairing he⟩

end Derived

end

end DerivedFormalization.PerfectDuals
