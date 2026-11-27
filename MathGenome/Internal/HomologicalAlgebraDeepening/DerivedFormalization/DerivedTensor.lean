import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorInvariance
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.SemifreeReplacement
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Localization.Adjunction

/-! The unbounded derived tensor on the derived category of the original ring. -/

namespace DerivedFormalization.DerivedTensor

open CategoryTheory Category MonoidalCategory
open Specs.DerivedFormalization.DerivedTensor
open Specs.DerivedFormalization.Cochains
  (compValue homotopyValue derivedValue quotientValue qValue qhValue quotientCompQhIsoValue)
open Specs.DerivedFormalization.CochainTensor (isKFlat)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel representedUnit)

universe u a v

attribute [local instance] HasDerivedCategory.standard

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

abbrev tensorFunctor : TensorFunctorType :=
  @Specs.DerivedFormalization.DerivedTensor.Descent.tensorFunctor

private theorem inv_natural {C : Type*} [Category* C] {X Y X' Y' : C}
    (i : X ≅ Y) (i' : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ i'.hom = i.hom ≫ g) : g ≫ i'.inv = i.inv ≫ f := by
  rw [← cancel_mono i'.hom, assoc, Iso.inv_hom_id, comp_id, assoc, h, Iso.inv_hom_id_assoc]

private theorem map_natural {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y X' Y' : C} {f : X ⟶ X'} {g : Y ⟶ Y'} {p : X ⟶ Y} {q : X' ⟶ Y'}
    (h : f ≫ q = p ≫ g) : F.map f ≫ F.map q = F.map p ≫ F.map g := by
  simpa only [Functor.map_comp] using F.congr_map h

private theorem tensor_natural {C : Type*} [Category* C] [MonoidalCategory C]
    {X Y Z W X' Y' Z' W' : C}
    {f : X ⟶ X'} {g : Z ⟶ Z'} {f' : Y ⟶ Y'} {g' : W ⟶ W'}
    {p : X ⟶ Y} {q : Z ⟶ W} {p' : X' ⟶ Y'} {q' : Z' ⟶ W'}
    (hf : f ≫ p' = p ≫ f') (hg : g ≫ q' = q ≫ g') :
    (f ⊗ₘ g) ≫ (p' ⊗ₘ q') = (p ⊗ₘ q) ≫ (f' ⊗ₘ g') := by
  rw [tensorHom_comp_tensorHom, hf, hg, ← tensorHom_comp_tensorHom]

variable {R : Type u} [CommRing R]

private theorem qMapBijectiveFromKProjective {P Q : compValue.{a} R} [P.IsKProjective] :
    Function.Bijective ((qhValue R).map :
      ((quotientValue R).obj P ⟶ (quotientValue R).obj Q) → _) :=
  CochainComplex.IsKProjective.Qh_map_bijective P ((quotientValue R).obj Q)

private theorem homotopy_of_q_map_eq {P Q : compValue.{a} R} [P.IsKProjective]
    {f g : P ⟶ Q} (h : (qValue R).map f = (qValue R).map g) :
    Nonempty (Homotopy f g) := by
  let q := quotientCompQhIsoValue.{a} R
  refine ⟨HomotopyCategory.homotopyOfEq _ _ (qMapBijectiveFromKProjective.injective ?_)⟩
  apply (cancel_mono (q.hom.app Q)).1
  simpa only [Functor.comp_map, q.hom.naturality, h]

private theorem exists_chain_map {P Q : compValue.{a} R} [P.IsKProjective]
    (f : (qValue R).obj P ⟶ (qValue R).obj Q) :
    ∃ f₀ : P ⟶ Q, (qValue R).map f₀ = f := by
  let q := quotientCompQhIsoValue.{a} R
  obtain ⟨g, hg⟩ := qMapBijectiveFromKProjective.surjective (q.hom.app P ≫ f ≫ q.inv.app Q)
  let f₀ : P ⟶ Q := g.out
  refine ⟨f₀, (cancel_epi (q.hom.app P)).1 ?_⟩
  rw [← q.hom.naturality f₀]
  change (qhValue R).map ((quotientValue R).map f₀) ≫ q.hom.app Q = _
  have hf₀ : (quotientValue R).map f₀ = g := HomotopyCategory.quotient_map_out g
  rw [hf₀, hg]
  simp only [assoc, Iso.inv_hom_id_app, comp_id]

theorem kProjectiveMapLifting : KProjectiveMapLifting.{u,a} := by
  intro R _ X Y P Q _ p q f
  obtain ⟨f₀, hf₀⟩ := exists_chain_map (p.hom ≫ f ≫ q.inv)
  refine ⟨⟨f₀, by simp [hf₀]⟩, ?_⟩
  intro g₀ g₁ h₀ h₁
  exact homotopy_of_q_map_eq ((cancel_mono q.hom).1 (h₀.trans h₁.symm))

theorem coefficientLiftComparison : CoefficientLiftComparison.{u,a,v} := by
  intro R A _ _ e M T
  dsimp only
  obtain ⟨c, hp, hn⟩ := CochainTensor.liftTensor.{u,v,max u a} (R := R)
  refine ⟨c, hp, hn, ?_⟩
  intro X X' Y Y' f g h h'
  dsimp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_inv, Iso.symm_inv, Iso.symm_hom,
    Functor.mapIso_hom]
  let L := Specs.DerivedFormalization.CochainCoefficientLift.lift.{max u a,v} R
  have hc := T.compare_natural (L.map f) (L.map g) h h'
  rw [← assoc, hc, assoc, map_natural (qValue R) (inv_natural _ _ _ _ (hn f g)), ← assoc]

section Localization

private theorem isLocalization_of_projective_presentations
    {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
    (W_eq : ∀ {X Y : C} (f : X ⟶ Y), W f ↔ IsIso (L.map f))
    (h : ∀ X : D, ∃ P : C, Nonempty (L.obj P ≅ X) ∧
      ∀ Y : C, Function.Bijective (L.map : (P ⟶ Y) → _)) :
    L.IsLocalization W := by
  classical
  choose P hP hj using h
  let i (X : D) := (hP X).some
  let E (X : D) (Y : C) : (P X ⟶ Y) ≃ (X ⟶ L.obj Y) :=
    (Equiv.ofBijective L.map (hj X Y)).trans (Iso.homCongr (i X) (Iso.refl _))
  have E_apply (X : D) (Y : C) (f : P X ⟶ Y) :
      E X Y f = (i X).inv ≫ L.map f := by simp [E, Iso.homCongr]
  have hn : ∀ (X : D) (Y Y' : C) (g : Y ⟶ Y') (f : P X ⟶ Y),
      E X Y' (f ≫ g) = E X Y f ≫ L.map g := by
    intros
    simp only [E_apply, Functor.map_comp, assoc]
  let adj := Adjunction.adjunctionOfEquivLeft E hn
  have : IsIso adj.unit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
    intro X
    change IsIso (E X (P X) (𝟙 _))
    rw [E_apply, L.map_id, comp_id]
    infer_instance
  let F := adj.fullyFaithfulLOfIsIsoUnit
  letI := F.full
  letI := F.faithful
  have hW : W = (MorphismProperty.isomorphisms D).inverseImage L := by
    ext X Y f
    exact W_eq f
  rw [hW]
  exact adj.isLocalization'

variable {A : Type a} [CommRing A] {e : R ≃+* A}

private theorem exists_kProjective_kFlat [Small.{a} R] (X : compValue.{a} R) :
    ∃ (P : compValue.{a} R) (p : P ⟶ X), QuasiIso p ∧ P.IsKProjective ∧ isKFlat P := by
  obtain ⟨P, p, hq, _, _, hp, hF⟩ := SemifreeReplacement.nativeReplacement R X
  exact ⟨P, p, hq, hp, hF⟩

private theorem flatQh_isLocalization (e : R ≃+* A) :
    (flatQh.{u,a} R).IsLocalization (flatQuasiIso.{u,a} R) := by
  let C := ModuleCat.{a} R
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let L := qhValue.{a} R
  letI : L.IsLocalization W :=
    inferInstanceAs (DerivedCategory.Qh.IsLocalization (HomotopyCategory.quasiIso C (.up ℤ)))
  letI : L.EssSurj := Localization.essSurj L W
  letI : Small.{a} R := small_map e.toEquiv
  apply isLocalization_of_projective_presentations
  · intro X Y f
    exact (DerivedCategory.isIso_Qh_map_iff f.hom).symm
  · intro X
    obtain ⟨K, hK⟩ := HomotopyCategory.quotient_obj_surjective (L.objPreimage X)
    obtain ⟨P, p, hq, hp, hFlat⟩ := exists_kProjective_kFlat K
    letI := hp
    have hq' : W ((quotientValue R).map p) :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hq
    let i : L.obj ((quotientValue R).obj P) ≅ X :=
      Localization.isoOfHom L W ((quotientValue R).map p) hq' ≪≫
        L.mapIso (eqToIso hK) ≪≫ L.objObjPreimageIso X
    refine ⟨flatObject R P hFlat, ⟨i⟩, ?_⟩
    intro Y
    exact (CochainComplex.IsKProjective.Qh_map_bijective P Y.obj).comp
      ((kFlatHomotopy.{u,a} R).fullyFaithfulι.homEquiv).bijective

end Localization

section Monoidal

variable {A : Type a} [CommRing A] {e : R ≃+* A} (M : AdequateModel e)

set_option quotPrecheck false
set_option hygiene false

local notation "C" => (compValue.{a} R)
local notation "K" => (homotopyValue.{a} R)
local notation "π" => (quotientValue.{a} R)
local notation "Q" => (qValue.{a} R)
local notation "Qh" => (qhValue.{a} R)
local notation "W" => (HomotopyCategory.quasiIso (ModuleCat.{a} R) (.up ℤ))
local notation "HAc" => (HomotopyCategory.subcategoryAcyclic (ModuleCat.{a} R))
local notation "rawMap" => Specs.DerivedFormalization.CochainTensor.map

private theorem kFlat_iff_monoidal (P : C) :
    letI := M.chainMonoidal
    isKFlat P ↔ ∀ E : C, E.Acyclic → (E ⊗ P).Acyclic :=
  letI := M.chainMonoidal
  ⟨fun h E hE n => (h E hE n).of_iso (M.tensorModel E P),
    fun h E hE n => (h E hE n).of_iso (M.tensorModel E P).symm⟩

private theorem kFlat_iff_homotopy (P : K) :
    letI := M.homotopyMonoidal
    kFlatHomotopy R P ↔ ∀ E : K, HAc E → HAc (E ⊗ P) := by
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change isKFlat P ↔ _
  rw [kFlat_iff_monoidal M]
  have cmp (E : C) :
      HAc ((π).obj E ⊗ (π).obj P) ↔ (E ⊗ P).Acyclic :=
    ((HAc).prop_iff_of_iso (Functor.Monoidal.μIso π E P)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)
  constructor
  · intro h E hE
    obtain ⟨E, rfl⟩ := HomotopyCategory.quotient_obj_surjective E
    exact (cmp E).mpr (h E ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp hE))
  · intro h E hE
    exact (cmp E).mp (h ((π).obj E)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mpr hE))

private theorem kFlat_monoidal :
    letI := M.homotopyMonoidal
    (kFlatHomotopy.{u,a} R).IsMonoidal := by
  letI := M.homotopyMonoidal
  refine { prop_unit := ?_, prop_tensor := ?_ }
  · rw [kFlat_iff_homotopy M]
    exact fun E hE => (HAc).prop_of_iso (ρ_ E).symm hE
  · intro P S hP hS
    rw [kFlat_iff_homotopy M] at hP hS ⊢
    intro E hE
    exact (HAc).prop_of_iso (α_ E P S) (hS _ (hP _ hE))

private theorem quasiIso_iff_of_square {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (i : X ≅ X') (j : Y ≅ Y') (h : f ≫ j.hom = i.hom ≫ g) :
    QuasiIso f ↔ QuasiIso g := by
  rw [← quasiIso_iff_comp_right f j.hom, h, quasiIso_iff_comp_left]

private theorem tensor_left_quasiIso (P : C) (hP : isKFlat P) {X Y : C} (f : X ⟶ Y)
    (hf : QuasiIso f) :
    letI := M.chainMonoidal
    QuasiIso ((𝟙 P) ⊗ₘ f) :=
  letI := M.chainMonoidal
  (quasiIso_iff_of_square _ _ _ _ (M.tensorModel_natural (𝟙 P) f)).mp
    (CochainTensorInvariance.tensorMapQuasiIso P hP f hf)

private theorem tensor_right_quasiIso (P : C) (hP : isKFlat P) {X Y : C} (f : X ⟶ Y)
    (hf : QuasiIso f) :
    letI := M.chainMonoidal
    QuasiIso (f ⊗ₘ (𝟙 P)) :=
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  (quasiIso_iff_of_square _ _ (β_ X P) (β_ Y P)
    (BraidedCategory.braiding_naturality f (𝟙 P))).mpr (tensor_left_quasiIso M P hP f hf)

private theorem tensor_quasiIso {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : QuasiIso f) (hg : QuasiIso g) (hX : isKFlat X) (hY : isKFlat Y)
    (h : isKFlat X' ∨ isKFlat Y') :
    letI := M.chainMonoidal
    QuasiIso (f ⊗ₘ g) := by
  letI := M.chainMonoidal
  rcases h with hX' | hY'
  · letI := tensor_right_quasiIso M Y hY f hf
    letI := tensor_left_quasiIso M X' hX' g hg
    rw [tensorHom_def]
    simpa only [tensorHom_id, id_tensorHom] using
      (quasiIso_comp (f ⊗ₘ 𝟙 Y) (𝟙 X' ⊗ₘ g))
  · letI := tensor_left_quasiIso M X hX g hg
    letI := tensor_right_quasiIso M Y' hY' f hf
    rw [tensorHom_def']
    simpa only [tensorHom_id, id_tensorHom] using
      (quasiIso_comp (𝟙 X ⊗ₘ g) (f ⊗ₘ 𝟙 Y'))

include M in
private theorem rawMap_quasiIso {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : QuasiIso f) (hg : QuasiIso g) (hX : isKFlat X) (hY : isKFlat Y)
    (h : isKFlat X' ∨ isKFlat Y') : QuasiIso (rawMap f g) := by
  letI := M.chainMonoidal
  exact (quasiIso_iff_of_square _ _ _ _ (M.tensorModel_natural f g)).2
    (tensor_quasiIso M f g hf hg hX hY h)

private theorem flatQuasiIso_monoidal :
    letI := M.homotopyMonoidal
    letI := kFlat_monoidal M
    (flatQuasiIso.{u,a} R).IsMonoidal := by
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := kFlat_monoidal M
  apply MorphismProperty.IsMonoidal.mk'
  rintro ⟨S, hS⟩ ⟨S', hS'⟩ ⟨T, hT⟩ ⟨T', hT'⟩ f g hf hg
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective S
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective S'
  obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective T
  obtain ⟨Y', rfl⟩ := HomotopyCategory.quotient_obj_surjective T'
  let f₀ : X ⟶ X' := f.hom.out
  let g₀ : Y ⟶ Y' := g.hom.out
  have hf₀ : (π).map f₀ = f.hom := HomotopyCategory.quotient_map_out _
  have hg₀ : (π).map g₀ = g.hom := HomotopyCategory.quotient_map_out _
  change W (f.hom ⊗ₘ g.hom)
  change W f.hom at hf
  change W g.hom at hg
  rw [← hf₀] at hf ⊢
  rw [← hg₀] at hg ⊢
  have hfg := tensor_quasiIso M f₀ g₀
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff f₀).1 hf)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff g₀).1 hg) hS hT (Or.inl hS')
  have hπ := (HomotopyCategory.quotient_map_mem_quasiIso_iff (f₀ ⊗ₘ g₀)).2 hfg
  exact ((W).arrow_mk_iso_iff (Arrow.isoMk (Functor.Monoidal.μIso π X Y)
    (Functor.Monoidal.μIso π X' Y') (Functor.LaxMonoidal.μ_natural π f₀ g₀).symm)).2 hπ

private def descent : Descent M := by
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := kFlat_monoidal M
  letI := flatQuasiIso_monoidal M
  let L := flatQh.{u,a} R
  let W' := flatQuasiIso.{u,a} R
  letI : L.IsLocalization W' := flatQh_isLocalization e
  let ε : L.obj (𝟙_ (kFlatHomotopy.{u,a} R).FullSubcategory) ≅ (Q).obj (representedUnit e) :=
    (Qh).mapIso (Functor.Monoidal.εIso π) ≪≫
      (π ⋙ Qh).mapIso M.unitModel.symm ≪≫ (quotientCompQhIsoValue R).app _
  let D := LocalizedMonoidal L W' ε
  exact {
    flatMonoidal := kFlat_monoidal M
    monoidal := inferInstanceAs (MonoidalCategory D)
    symmetric := inferInstanceAs (SymmetricCategory D)
    localization := inferInstanceAs (L.IsLocalization W')
    braided := inferInstanceAs ((Localization.Monoidal.toMonoidalCategory L W' ε).Braided) }

variable {M} (T : Descent M)

private theorem flatComparison_natural {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (hX : isKFlat X) (hX' : isKFlat X')
    (hY : isKFlat Y) (hY' : isKFlat Y') :
    T.tensorFunctor.map ((Q).map f, (Q).map g) ≫ (T.flatComparison X' Y' hX' hY').hom =
      (T.flatComparison X Y hX hY).hom ≫ (Q).map (rawMap f g) := by
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := T.flatMonoidal
  letI := T.monoidal
  letI := T.symmetric
  letI := T.braided
  let q := quotientCompQhIsoValue.{a} R
  let F := π ⋙ Qh
  let L := flatQh.{u,a} R
  let fH : flatObject R X hX ⟶ flatObject R X' hX' := ObjectProperty.homMk ((π).map f)
  let gH : flatObject R Y hY ⟶ flatObject R Y' hY' := ObjectProperty.homMk ((π).map g)
  let μ₁ U V := Functor.LaxMonoidal.μ π U V
  let μ₂ U V := Functor.LaxMonoidal.μ L U V
  let fX := flatObject R X hX
  let fX' := flatObject R X' hX'
  let fY := flatObject R Y hY
  let fY' := flatObject R Y' hY'
  have h₁ := tensor_natural (q.inv.naturality f) (q.inv.naturality g)
  have h₂ : (F.map f ⊗ₘ F.map g) ≫ μ₂ fX' fY' =
      μ₂ fX fY ≫ (Qh).map ((π).map f ⊗ₘ (π).map g) :=
    Functor.LaxMonoidal.μ_natural L fH gH
  have h₃ : (Qh).map ((π).map f ⊗ₘ (π).map g) ≫ (Qh).map (μ₁ X' Y') =
      (Qh).map (μ₁ X Y) ≫ F.map (f ⊗ₘ g) :=
    map_natural Qh (Functor.LaxMonoidal.μ_natural π f g)
  have h₄ : F.map (f ⊗ₘ g) ≫ F.map (M.tensorModel X' Y').inv =
      F.map (M.tensorModel X Y).inv ≫ F.map (rawMap f g) :=
    map_natural F (inv_natural _ _ _ _ (M.tensorModel_natural f g))
  simp only [Descent.flatComparison, Descent.tensorFunctor, MonoidalCategory.tensor_map,
    Iso.trans_hom, Iso.app_hom, tensorIso_hom, Iso.symm_hom, Iso.app_inv,
    Functor.Monoidal.μIso_hom, Functor.mapIso_hom, assoc]
  erw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄,
    q.hom.naturality (rawMap f g)]

theorem braidingOnModels : BraidingOnModels.{u,a} := by
  intro R A _ _ e M T X Y hX hY
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := T.flatMonoidal
  letI := T.monoidal
  letI := T.symmetric
  letI := T.braided
  refine ⟨?_, fun i j n h x y => M.braiding_on_pure X Y h x y⟩
  let q := quotientCompQhIsoValue.{a} R
  let F := π ⋙ Qh
  let L := flatQh.{u,a} R
  let x := flatObject R X hX
  let y := flatObject R Y hY
  let b := M.tensorModel X Y ≪≫ β_ X Y ≪≫ (M.tensorModel Y X).symm
  let μ₁ U V := Functor.LaxMonoidal.μ π U V
  let μ₂ U V := Functor.LaxMonoidal.μ L U V
  have h₁ := (BraidedCategory.braiding_naturality (q.inv.app X) (q.inv.app Y)).symm
  have h₂ : (β_ (F.obj X) (F.obj Y)).hom ≫ μ₂ y x =
      μ₂ x y ≫ (Qh).map (β_ ((π).obj X) ((π).obj Y)).hom :=
    (Functor.LaxBraided.braided (F := L) x y).symm
  have h₃ : (Qh).map (β_ ((π).obj X) ((π).obj Y)).hom ≫ (Qh).map (μ₁ Y X) =
      (Qh).map (μ₁ X Y) ≫ F.map (β_ X Y).hom :=
    map_natural Qh (Functor.LaxBraided.braided (F := π) X Y).symm
  have h₄ : F.map (β_ X Y).hom ≫ F.map (M.tensorModel Y X).inv =
      F.map (M.tensorModel X Y).inv ≫ F.map b.hom := by
    apply map_natural F
    simp [b]
  change (β_ ((Q).obj X) ((Q).obj Y)).hom ≫ (T.flatComparison Y X hY hX).hom =
    (T.flatComparison X Y hX hY).hom ≫ (Q).map b.hom
  simp only [Descent.flatComparison, Iso.trans_hom, Iso.app_hom, tensorIso_hom, Iso.symm_hom,
    Iso.app_inv, Functor.Monoidal.μIso_hom, Functor.mapIso_hom, assoc]
  erw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, q.hom.naturality b.hom]

private theorem presentation_natural {X X' Y Y' : derivedValue.{a} R}
    {P P' S S' : C} (hP : isKFlat P) (hP' : isKFlat P') (hS : isKFlat S) (hS' : isKFlat S')
    (p : (Q).obj P ≅ X) (p' : (Q).obj P' ≅ X') (q : (Q).obj S ≅ Y) (q' : (Q).obj S' ≅ Y')
    (f : X ⟶ X') (g : Y ⟶ Y') (f₀ : P ⟶ P') (g₀ : S ⟶ S')
    (hf : (Q).map f₀ ≫ p'.hom = p.hom ≫ f) (hg : (Q).map g₀ ≫ q'.hom = q.hom ≫ g) :
    T.tensorFunctor.map (f, g) ≫ (T.presentationComparison hP' hS' p' q').hom =
      (T.presentationComparison hP hS p q).hom ≫ (Q).map (rawMap f₀ g₀) := by
  letI := T.monoidal
  change (f ⊗ₘ g) ≫ ((p'.inv ⊗ₘ q'.inv) ≫ (T.flatComparison P' S' hP' hS').hom) =
    ((p.inv ⊗ₘ q.inv) ≫ (T.flatComparison P S hP hS).hom) ≫ (Q).map (rawMap f₀ g₀)
  have hn := flatComparison_natural T f₀ g₀ hP hP' hS hS'
  change ((Q).map f₀ ⊗ₘ (Q).map g₀) ≫ _ = _ at hn
  rw [reassoc_of% (tensor_natural (inv_natural _ _ _ _ hf) (inv_natural _ _ _ _ hg)), hn, assoc]

theorem presentationNaturality : PresentationNaturality.{u,a} := by
  intro R A _ _ e M T X X' Y Y' P P' S S' hP hP' hS hS' p p' q q' f g f₀ g₀ hf hg
  exact presentation_natural T hP hP' hS hS' p p' q q' f g f₀ g₀ hf hg

private theorem augmentation_eq {X Y P S : C} (hP : isKFlat P) (hS : isKFlat S)
    (p : P ⟶ X) (q : S ⟶ Y) [QuasiIso p] [QuasiIso q]
    (c : T.tensorFunctor.obj ((Q).obj X, (Q).obj Y) ⟶ (Q).obj (Specs.DerivedFormalization.CochainTensor.tensor X Y))
    (hc : T.tensorFunctor.map ((Q).map p, (Q).map q) ≫ c =
      (T.flatComparison P S hP hS).hom ≫ (Q).map (rawMap p q)) :
    (T.augmentationComparison hP hS p q).hom ≫ (Q).map (rawMap p q) = c := by
  letI := T.monoidal
  letI : IsIso ((Q).map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 inferInstance
  letI : IsIso ((Q).map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance
  let l := tensorIso (asIso ((Q).map p)) (asIso ((Q).map q))
  change (l.inv ≫ (T.flatComparison P S hP hS).hom) ≫ (Q).map (rawMap p q) = c
  change l.hom ≫ c = _ at hc
  rw [assoc, ← hc, Iso.inv_hom_id_assoc]

theorem augmentationCompatibility : AugmentationCompatibility.{u,a} := by
  intro R A _ _ e M T X Y P S h hP hS p q _ _
  apply augmentation_eq
  rw [← T.compare_flat P S hP hS]
  exact T.compare_natural p q (Or.inl hP) h

include M in
private theorem rawMap_comp {X X' X'' Y Y' Y'' : C}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    rawMap f g ≫ rawMap f' g' = rawMap (f ≫ f') (g ≫ g') := by
  letI := M.chainMonoidal
  apply (cancel_mono (M.tensorModel X'' Y'').hom).1
  rw [assoc, M.tensorModel_natural f' g', ← assoc, M.tensorModel_natural f g, assoc,
    tensorHom_comp_tensorHom, M.tensorModel_natural]

private structure Replacement (X : C) where
  complex : C
  augmentation : complex ⟶ X
  quasiIso : QuasiIso augmentation
  projective : complex.IsKProjective
  flat : isKFlat complex

private def replacement (e : R ≃+* A) (X : C) : Replacement X := by
  letI : Small.{a} R := small_map e.toEquiv
  refine Classical.choice ?_
  obtain ⟨P, p, hp, hproj, hflat⟩ := exists_kProjective_kFlat X
  exact ⟨⟨P, p, hp, hproj, hflat⟩⟩

private def qIso {X Y : C} (f : X ⟶ Y) (hf : QuasiIso f) : (Q).obj X ≅ (Q).obj Y :=
  letI : IsIso ((Q).map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  asIso ((Q).map f)

private def compareReplacements {X Y : C} (r : Replacement X) (s : Replacement Y)
    (h : isKFlat X ∨ isKFlat Y) :
    T.tensorFunctor.obj ((Q).obj X, (Q).obj Y) ≅ (Q).obj (Specs.DerivedFormalization.CochainTensor.tensor X Y) :=
  letI := r.quasiIso
  letI := s.quasiIso
  T.augmentationComparison r.flat s.flat r.augmentation s.augmentation ≪≫
    qIso _ (rawMap_quasiIso M r.augmentation s.augmentation r.quasiIso s.quasiIso r.flat s.flat h)

private theorem compareReplacements_flat {X Y : C} (r : Replacement X) (s : Replacement Y)
    (hX : isKFlat X) (hY : isKFlat Y) :
    compareReplacements T r s (Or.inl hX) = T.flatComparison X Y hX hY := by
  letI := r.quasiIso
  letI := s.quasiIso
  apply Iso.ext
  exact augmentation_eq T r.flat s.flat r.augmentation s.augmentation _
    (flatComparison_natural T r.augmentation s.augmentation r.flat hX s.flat hY)

private theorem compareReplacements_natural {X X' Y Y' : C}
    (r : Replacement X) (r' : Replacement X') (s : Replacement Y) (s' : Replacement Y')
    (f : X ⟶ X') (g : Y ⟶ Y')
    (h : isKFlat X ∨ isKFlat Y) (h' : isKFlat X' ∨ isKFlat Y') :
    T.tensorFunctor.map ((Q).map f, (Q).map g) ≫ (compareReplacements T r' s' h').hom =
      (compareReplacements T r s h).hom ≫ (Q).map (rawMap f g) := by
  letI := r.projective
  letI := s.projective
  let p := qIso r.augmentation r.quasiIso
  let p' := qIso r'.augmentation r'.quasiIso
  let q := qIso s.augmentation s.quasiIso
  let q' := qIso s'.augmentation s'.quasiIso
  obtain ⟨f₀, hf⟩ := (kProjectiveMapLifting p p' ((Q).map f)).1
  obtain ⟨g₀, hg⟩ := (kProjectiveMapLifting q q' ((Q).map g)).1
  have hf' : (Q).map (f₀ ≫ r'.augmentation) = (Q).map (r.augmentation ≫ f) := by
    rw [(Q).map_comp, (Q).map_comp]
    exact hf
  have hg' : (Q).map (g₀ ≫ s'.augmentation) = (Q).map (s.augmentation ≫ g) := by
    rw [(Q).map_comp, (Q).map_comp]
    exact hg
  obtain ⟨hf₁⟩ := homotopy_of_q_map_eq hf'
  obtain ⟨hg₁⟩ := homotopy_of_q_map_eq hg'
  have hfg : (Q).map (rawMap (f₀ ≫ r'.augmentation) (g₀ ≫ s'.augmentation)) =
      (Q).map (rawMap (r.augmentation ≫ f) (s.augmentation ≫ g)) :=
    DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{a} R) (CochainTensor.mapHomotopy hf₁ hg₁)
  have hn := presentation_natural T r.flat r'.flat s.flat s'.flat p p' q q'
    ((Q).map f) ((Q).map g) f₀ g₀ hf hg
  change T.tensorFunctor.map ((Q).map f, (Q).map g) ≫
      ((T.presentationComparison r'.flat s'.flat p' q').hom ≫
        (Q).map (rawMap r'.augmentation s'.augmentation)) =
    ((T.presentationComparison r.flat s.flat p q).hom ≫ (Q).map (rawMap r.augmentation s.augmentation)) ≫
      (Q).map (rawMap f g)
  rw [← assoc, hn, assoc, ← (Q).map_comp]
  erw [rawMap_comp (M := M) f₀ r'.augmentation g₀ s'.augmentation, hfg,
    ← rawMap_comp (M := M) r.augmentation f s.augmentation g, (Q).map_comp]
  simp only [Descent.presentationComparison, Iso.trans_hom, assoc]

/-- The derived symmetric monoidal structure and its comparison to the signed
chain tensor, assembled from the ordinary adequate model. -/
def model (M : AdequateModel e) : Model M where
  toDescent := descent M
  compare X Y h := compareReplacements (descent M) (replacement e X) (replacement e Y) h
  compare_flat X Y := compareReplacements_flat (descent M) (replacement e X) (replacement e Y)
  compare_natural f g := compareReplacements_natural (descent M)
    (replacement e _) (replacement e _) (replacement e _) (replacement e _) f g

theorem existsModel : ExistsModel.{u,a} := by
  intro R A _ _ e M
  exact ⟨model M⟩

end Monoidal

end

end DerivedFormalization.DerivedTensor
