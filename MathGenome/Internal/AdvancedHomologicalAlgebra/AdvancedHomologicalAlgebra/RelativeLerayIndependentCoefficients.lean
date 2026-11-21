import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.RelativeLerayIndependentCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.RelativeLeray
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GrothendieckEdges
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2500000
set_option maxRecDepth 3000

universe a m u v w r s t

namespace AdvancedHomologicalAlgebra.RelativeLerayIndependentCoefficients

open SheafUniverseTransport HigherDirectImagesOriginalTheory OriginalDerivedSectionsTheory
open GrothendieckSpectralSequence GrothendieckEdges HypercohomologyDerivedNaturality
open LerayIndependentCoefficients (changeCoefficientsObj changeGradedIso stalkCoordinates)
open FiniteFiltrationConvergence
open Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.RightDerivedComposition (comparisonValue)
open Specs.AdvancedHomologicalAlgebra.RelativeLerayIndependentCoefficients

open private exactDescent derivedUnitTransport composeUnitTransport transport_commutes
  composition_unit from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients
open private unit_isIso_of_injective from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomology

attribute [local instance] HasDerivedCategory.standard

section GradedDiagrams

variable {C₀ : Type*} [Category* C₀] [Abelian C₀]

private def GradedSquare (k : ℕ) (p n : ℤ) {X Y : RowDiagram C₀} (f : X ⟶ Y)
    (e : X.page k p n ≅ cokernel (X.down p n))
    (e' : Y.page k p n ≅ cokernel (Y.down p n)) : Prop :=
  (pageEval k p n).map f ≫ e'.hom = e.hom ≫ (gradedEval p n).map f

private theorem GradedSquare.comp {k : ℕ} {p n : ℤ} {X Y Z : RowDiagram C₀}
    {f : X ⟶ Y} {g : Y ⟶ Z} {e e' e''}
    (hf : GradedSquare k p n f e e') (hg : GradedSquare k p n g e' e'') :
    GradedSquare k p n (f ≫ g) e e'' := by
  dsimp only [GradedSquare] at *
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg,
    ← Category.assoc, hf, Category.assoc]

private theorem GradedSquare.inv {k : ℕ} {p n : ℤ} {X Y : RowDiagram C₀}
    {f : X ⟶ Y} [IsIso f] {e e'} (hf : GradedSquare k p n f e e') :
    GradedSquare k p n (inv f) e' e := by
  dsimp only [GradedSquare] at *
  rw [Functor.map_inv, Functor.map_inv]
  apply (cancel_mono ((gradedEval p n).map f)).mp
  rw [Category.assoc, ← hf, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private def transportGraded {k : ℕ} {p n : ℤ} {X Y : RowDiagram C₀} (i : X ≅ Y)
    (e : Y.page k p n ≅ cokernel (Y.down p n)) :
    X.page k p n ≅ cokernel (X.down p n) :=
  (pageEval k p n).mapIso i ≪≫ e ≪≫ ((gradedEval p n).mapIso i).symm

private theorem gradedSquare_transport {k : ℕ} {p n : ℤ} {X Y X' Y' : RowDiagram C₀}
    (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : f ≫ j.hom = i.hom ≫ g)
    {e : X'.page k p n ≅ cokernel (X'.down p n)}
    {e' : Y'.page k p n ≅ cokernel (Y'.down p n)}
    (square : GradedSquare k p n g e e') :
    GradedSquare k p n f (transportGraded i e) (transportGraded j e') := by
  let P := pageEval (C := C₀) k p n
  let Q := gradedEval (C₀ := C₀) p n
  have cancel {A B : RowDiagram C₀} (a : A ≅ B) (z : B.page k p n ≅ cokernel (B.down p n)) :
      GradedSquare k p n a.hom (transportGraded a z) z := by
    let ζ : P.obj B ⟶ Q.obj B := z.hom
    change P.map a.hom ≫ ζ = (P.map a.hom ≫ ζ ≫ Q.map a.inv) ≫ Q.map a.hom
    have c : Q.map a.inv ≫ Q.map a.hom = 𝟙 (Q.obj B) := by
      rw [← Q.map_comp, Iso.inv_hom_id, Q.map_id]
    rw [Category.assoc, Category.assoc, c, Category.comp_id]
  have hj : GradedSquare k p n j.inv e' (transportGraded j e') := by
    have hinv : inv j.hom = j.inv := by
      apply (cancel_mono j.hom).1
      rw [IsIso.inv_hom_id, Iso.inv_hom_id]
    simpa only [hinv] using (cancel j e').inv
  have res := (cancel i e).comp (square.comp hj)
  have hf : i.hom ≫ g ≫ j.inv = f := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rwa [hf] at res

variable {C₁ : Type*} [Category* C₁] [Abelian C₁]
  (E : C₀ ⥤ C₁) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

private theorem cokernel_change_natural {X Y : RowDiagram C₀} (f : X ⟶ Y) (p n : ℤ) :
    E.map ((gradedEval p n).map f) ≫ (PreservesCokernel.iso E (Y.down p n)).hom =
    (PreservesCokernel.iso E (X.down p n)).hom ≫
      (gradedEval p n).map ((LerayIndependentCoefficients.changeCoefficients E).map f) := by
  apply (cancel_epi (E.map (cokernel.π (X.down p n)))).mp
  rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, PreservesCokernel.π_iso_hom]
  simp only [gradedEval, cokernel.map, cokernel.π_desc, Functor.map_comp, Category.assoc,
    PreservesCokernel.π_iso_hom]
  change _ = cokernel.π (E.map (X.down p n)) ≫
    cokernel.desc (E.map (X.down p n)) (E.map (f.step p n) ≫ cokernel.π (E.map (Y.down p n))) _
  rw [cokernel.π_desc]

private theorem gradedSquare_change {k : ℕ} {p n : ℤ} {X Y : RowDiagram C₀}
    {f : X ⟶ Y} {e e'} (h : GradedSquare k p n f e e') :
    GradedSquare k p n ((LerayIndependentCoefficients.changeCoefficients E).map f)
      (changeGradedIso E X k p n e) (changeGradedIso E Y k p n e') := by
  change E.map ((pageEval k p n).map f) ≫
      (E.map e'.hom ≫ (PreservesCokernel.iso E (Y.down p n)).hom) =
    (E.map e.hom ≫ (PreservesCokernel.iso E (X.down p n)).hom) ≫ _
  rw [← E.map_comp_assoc, h, E.map_comp, Category.assoc, cokernel_change_natural E,
    Category.assoc]

end GradedDiagrams

section LocalizedRow

variable {B₀ C₀ : Type*} [Category* B₀] [Category* C₀] [Abelian B₀] [Abelian C₀]
  [EnoughInjectives B₀] (H : B₀ ⥤ C₀) [H.Additive] (U : DerivedRow H)

private abbrev complexModel (K : CochainComplex.Plus B₀) :=
  U.system.data K (U.resolution K)

private abbrev ComplexLimit (K : CochainComplex.Plus B₀) (k : ℕ) (p n : ℤ) :=
  LimitIso (complexModel H U K).filtration (complexModel H U K).pages ((k : ℤ) + 2) p n

private theorem row_representative (W : DerivedCategory.Plus B₀) (k : ℕ) (p n : ℤ)
    (e : ComplexLimit H U (modelComplex W) k p n) :
    let M := modelData H U W
    let i := modelIso H U W
    closedToPage M.filtration M.pages ((k : ℤ) + 2) p n ≫ i.inv.page k p n ≫
        (rowGradedIso H U W k p n e).hom =
      closedClass M.filtration p n ≫ i.inv.step p n ≫ cokernel.π ((U.derived.obj W).down p n) := by
  let M := modelData H U W
  let i := modelIso H U W
  let P := pageEval (C := C₀) k p n
  let Q := gradedEval (C₀ := C₀) p n
  change closedToPage M.filtration M.pages ((k : ℤ) + 2) p n ≫ P.map i.inv ≫
      (P.map i.hom ≫ e.iso.hom ≫ Q.map i.inv) =
    closedClass M.filtration p n ≫ i.inv.step p n ≫ cokernel.π ((U.derived.obj W).down p n)
  have hi : P.map i.inv ≫ P.map i.hom = 𝟙 _ := by
    rw [← P.map_comp, Iso.inv_hom_id, P.map_id]
  have hr : closedToPage M.filtration M.pages ((k : ℤ) + 2) p n ≫ e.iso.hom =
      gradedClass M.filtration p n := e.representative_formula
  rw [← Category.assoc (P.map i.inv), hi, Category.id_comp, ← Category.assoc,
    hr]
  have hq : cokernel.π ((HypercohomologyDerivedNaturality.diagram H (modelData H U W)).down p n) ≫
        Q.map i.inv = i.inv.step p n ≫ cokernel.π ((U.derived.obj W).down p n) := by
    simp only [Q, gradedEval, cokernel.map, cokernel.π_desc]
  calc
    _ = closedClass M.filtration p n ≫
        (cokernel.π ((HypercohomologyDerivedNaturality.diagram H (modelData H U W)).down p n) ≫
          Q.map i.inv) := by
      exact Category.assoc (closedClass M.filtration p n) _ _
    _ = _ := congrArg (closedClass M.filtration p n ≫ ·) hq

private theorem complex_limit_square {K L : CochainComplex.Plus B₀} (f : K ⟶ L)
    (k : ℕ) (p n : ℤ) (e : ComplexLimit H U K k p n) (e' : ComplexLimit H U L k p n) :
    GradedSquare k p n (U.derived.map (DerivedCategory.Plus.Q.map f))
      (transportGraded (U.complexIso H K) e.iso)
      (transportGraded (U.complexIso H L) e'.iso) := by
  obtain ⟨a, ha, heq⟩ := U.map_eq f
  let g := diagramMap H U.system f a ha
  have hc := G05FilteredEdges.conjugate_eq_of_heq (U.obj_eq K) (U.obj_eq L)
    (U.complexes.map f) g heq
  have hnat := U.factors.hom.naturality f
  change U.derived.map (DerivedCategory.Plus.Q.map f) ≫ (U.factors.app L).hom =
    (U.factors.app K).hom ≫ U.complexes.map f at hnat
  have h : U.derived.map (DerivedCategory.Plus.Q.map f) ≫ (U.complexIso H L).hom =
      (U.complexIso H K).hom ≫ g := by
    simp only [DerivedRow.complexIso, Iso.trans_hom, Category.assoc]
    rw [← Category.assoc (U.derived.map _), hnat, Category.assoc]
    have hh := congrArg ((eqToIso (U.obj_eq K)).hom ≫ ·) hc
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using congrArg
      ((U.factors.app K).hom ≫ ·) hh
  apply gradedSquare_transport _ _ _ _ h
  change (U.system.lift _ _ a).maps.map ((k : ℤ) + 2) p n ≫ e'.iso.hom =
    e.iso.hom ≫ gradedCohomologyMap (U.system.lift _ _ a).filtered p n
  let t := U.system.lift _ _ a
  let M := complexModel H U K
  let N := complexModel H U L
  letI : Epi (closedToPage M.filtration M.pages ((k : ℤ) + 2) p n) := by
    have he : closedToPage M.filtration M.pages ((k : ℤ) + 2) p n =
        gradedClass M.filtration p n ≫ e.iso.inv := by
      rw [← e.representative_formula, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [he]
    infer_instance
  apply (cancel_epi (closedToPage M.filtration M.pages ((k : ℤ) + 2) p n)).mp
  rw [← Category.assoc, closedToPage_naturality t.filtered M.pages N.pages t.maps
    ((k : ℤ) + 2) p n, Category.assoc, e'.representative_formula,
    ← Category.assoc, e.representative_formula, gradedClass_naturality t.filtered p n]

private theorem localized_limit_square {Y Z : DerivedCategory.Plus B₀} (f : Y ⟶ Z) (n : ℤ) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∀ (p : ℤ)
      (e : ComplexLimit H U (modelComplex Y) k p n)
      (e' : ComplexLimit H U (modelComplex Z) k p n),
      GradedSquare k p n (U.derived.map f)
        (rowGradedIso H U Y k p n e) (rowGradedIso H U Z k p n e') := by
  letI : (DerivedCategory.Plus.Q (C := B₀)).EssSurj :=
    Localization.essSurj _ (CochainComplex.Plus.quasiIso B₀)
  let Q := DerivedCategory.Plus.Q (C := B₀)
  let i := Q.objObjPreimageIso Y
  let j := Q.objObjPreimageIso Z
  let f₀ := i.hom ≫ f ≫ j.inv
  obtain ⟨T, g, s, hs, hf⟩ := G05FilteredEdges.plus_left_fac f₀
  letI := hs
  let M := complexModel H U T
  obtain ⟨b, _, hb⟩ := M.convergence.stabilization n
  refine ⟨b.toNat, fun k hk p e e' ↦ ?_⟩
  obtain ⟨eT⟩ := M.convergence.limit M.pages ((k : ℤ) + 2) p n (by omega)
    (hb _ (by omega) p)
  have square := (complex_limit_square H U g k p n e eT).comp
    (complex_limit_square H U s k p n e' eT).inv
  have square₀ : GradedSquare k p n (U.derived.map f₀)
      (transportGraded (U.complexIso H (modelComplex Y)) e.iso)
      (transportGraded (U.complexIso H (modelComplex Z)) e'.iso) := by
    rw [hf, Functor.map_comp, Functor.map_inv]
    exact square
  have h : U.derived.map f ≫ (U.derived.mapIso j.symm).hom =
      (U.derived.mapIso i.symm).hom ≫ U.derived.map f₀ := by
    simp only [f₀, Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp,
      Iso.inv_hom_id_assoc]
  have hh := gradedSquare_transport (U.derived.mapIso i.symm) (U.derived.mapIso j.symm)
    _ _ h square₀
  simpa only [GradedSquare, transportGraded, rowGradedIso, modelIso, DerivedRow.complexIso,
    Functor.mapIso_trans, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc] using hh

end LocalizedRow

set_option hygiene false in
local notation "A" => AmbientSheaves.{max a m v w s t} R
set_option hygiene false in
local notation "B" => AmbientSheaves.{max a m u w r t} S
set_option hygiene false in
local notation "C" => AmbientSheaves.{max a m u v r s} T
set_option hygiene false in
local notation "F" => ambientDirectImage.{max a m w t} f
set_option hygiene false in
local notation "G" => ambientDirectImage.{max a m u r} g
set_option hygiene false in
local notation "R'" => liftedRing.{max a m v w s t} R
set_option hygiene false in
local notation "S'" => liftedRing.{max a m u w r t} S
set_option hygiene false in
local notation "T'" => liftedRing.{max a m u v r s} T
set_option hygiene false in
local notation "F'" => transportedDirectImage.{max a m w t} f
set_option hygiene false in
local notation "G'" => transportedDirectImage.{max a m u r} g
set_option hygiene false in
local notation "JX" => transport.{max a m v w s t} R
set_option hygiene false in
local notation "JY" => transport.{max a m u w r t} S
set_option hygiene false in
local notation "JZ" => transport.{max a m u v r s} T
set_option hygiene false in
local notation "f'" => transportedMap.{max a m w t} f
set_option hygiene false in
local notation "g'" => transportedMap.{max a m u r} g
set_option hygiene false in
local notation "φ'" => transportedScalars.{max a m w t} f
set_option hygiene false in
local notation "ψ'" => transportedScalars.{max a m u r} g
set_option hygiene false in
local notation "Lifts" => liftSheafCoefficients.{max a u v w r s t,u,r,m} R

private theorem lowerIso_naturality {M N P : Type*} [Category* M] [Category* N]
    [Category* P] {J : N ⥤ P} [J.IsEquivalence] {U U' : M ⥤ N} {V V' : M ⥤ P}
    (e : U ⋙ J ≅ V) (e' : U' ⋙ J ≅ V') (α : U ⟶ U') (β : V ⟶ V')
    (h : whiskerRight α J ≫ e'.hom = e.hom ≫ β) :
    (lowerIso e).hom ≫ α = whiskerRight β J.asEquivalence.inverse ≫ (lowerIso e').hom := by
  ext K : 2
  have hk := NatTrans.congr_app h K
  change J.map (α.app K) ≫ e'.hom.app K = e.hom.app K ≫ β.app K at hk
  have hc : e.inv.app K ≫ J.map (α.app K) = β.app K ≫ e'.inv.app K := by
    apply ((e'.app K).eq_comp_inv).2
    rw [Category.assoc]
    change e.inv.app K ≫ (J.map (α.app K) ≫ e'.hom.app K) = β.app K
    rw [hk, Iso.inv_hom_id_app_assoc]
  have hn := J.asEquivalence.unitIso.inv.naturality (α.app K)
  simp only [Functor.comp_map, Functor.id_map] at hn
  let Q := J.asEquivalence.inverse
  let η := J.asEquivalence.unitIso.inv
  change Q.map (J.map (α.app K)) ≫ η.app (U'.obj K) = η.app (U.obj K) ≫ α.app K at hn
  change (Q.map (e.inv.app K) ≫ 𝟙 _ ≫ η.app (U.obj K) ≫ 𝟙 _) ≫ α.app K =
      Q.map (β.app K) ≫ Q.map (e'.inv.app K) ≫ 𝟙 _ ≫ η.app (U'.obj K) ≫ 𝟙 _
  simp only [Category.assoc, Category.id_comp, Category.comp_id]
  rw [← hn, ← Q.map_comp_assoc, hc, Q.map_comp_assoc]

section

variable {X : TopCat.{u}} {Y : TopCat.{v}} {Z : TopCat.{w}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} {T : Z.Sheaf RingCat.{t}}
  (f : RingedMap R S) (g : RingedMap S T)

variable
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a m u v w r s t}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a m u v w r s t}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a m u v w r s t}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a m u v w r s t}]
  [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{max a m u v w r s t}]
  [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{max a m u v w r s t}]
  [EnoughInjectives A] [EnoughInjectives B]
  [(JX).IsEquivalence] [(JY).IsEquivalence] [(JZ).IsEquivalence]

private theorem underived_square :
    isoWhiskerRight (originalUnderived.{a,m} f g) JZ ≪≫ compositeSquare.{a,m} f g =
    composeFunctorSquares (firstSquare.{a,m} f g) (secondSquare.{a,m} f g) ≪≫
      isoWhiskerLeft JX (RelativeLeray.underivedCompositionIso R' S' T' f' g' φ' ψ') := by
  apply Iso.ext
  ext M V x
  rfl

private def siteComparison (L : RaisedLeray.{a,m} f g)
    (h : IsIso (comparisonValue F G)) : SiteComparison.{a,m} f g := by
  let j := exactDescent JX
  let k := exactDescent JY
  let l := exactDescent JZ
  have hx (M : A) (hM : Injective M) : Injective ((JX).obj M) :=
    ((JX).asEquivalence.map_injective_iff M).2 hM
  have hy (M : B) (hM : Injective M) : Injective ((JY).obj M) :=
    ((JY).asEquivalence.map_injective_iff M).2 hM
  let p := derivedUnitTransport F F' JX JY (firstSquare.{a,m} f g) (fun M hM ↦ by
    letI := hx M hM
    exact AcyclicTermComparison.rightAcyclic_of_injective F' _)
  let q := derivedUnitTransport G G' JY JZ (secondSquare.{a,m} f g) (fun M hM ↦ by
    letI := hy M hM
    exact AcyclicTermComparison.rightAcyclic_of_injective G' _)
  let c := derivedUnitTransport (F ⋙ G) (F' ⋙ G') JX JZ
    (composeFunctorSquares (firstSquare.{a,m} f g) (secondSquare.{a,m} f g))
    (fun M hM ↦ by
      letI := hx M hM
      exact AcyclicTermComparison.rightAcyclic_of_injective (F' ⋙ G') _)
  refine ⟨j, k, l, p, q, c, underived_square.{a,m} f g, ?_⟩
  intro K
  letI := h
  letI := L.package.comparison_isIso
  letI : IsIso (comparisonValue F' G') := NatIso.isIso_of_isIso_app _
  exact transport_commutes c (composeUnitTransport p q)
    (asIso (comparisonValue F G)) (asIso (comparisonValue F' G'))
    (composition_unit F G) (composition_unit F' G')
    (unit_isIso_of_injective (F ⋙ G)) K

variable (L : RaisedLeray.{a,m} f g) (d : SiteComparison.{a,m} f g)

local notation "Lower" => (JZ).asEquivalence.inverse
attribute [local instance] lowerAdditive
set_option hygiene false in
local notation "Raised" => GrothendieckSpectralSequence.sequence F' G' L.package.row
set_option hygiene false in
local notation "Diag" => diagram.{a,m} f g L d
set_option hygiene false in
local notation "Fil" => filtration.{a,m} f g L d

private theorem negative_columns (K : DerivedCategory.Plus A) (k : ℕ) (p n : ℤ)
    (hp : p < 0) : IsZero ((Diag K).page k p n) := by
  induction k generalizing p n with
  | zero =>
    have h := L.package.negative (d.source.functor.obj K) p (n - p) hp
    rw [show p + (n - p) = n by omega] at h
    exact (Lower).map_isZero h
  | succ k ih =>
    let p' := p - ((k : ℤ) + 2)
    have hp' : p' + ((k : ℤ) + 2) = p := by dsimp [p']; omega
    have hn' : n - 1 + 1 = n := by omega
    have hX₂ : IsZero (((Diag K).pageComplex k p' (n - 1)).X₂) := by
      change IsZero ((Diag K).page k (p' + ((k : ℤ) + 2)) (n - 1 + 1))
      rw [hp', hn']
      exact ih p n hp
    have h := (ShortComplex.isZero_homology_of_isZero_X₂ _ hX₂).of_iso
      ((Diag K).nextIso k p' (n - 1))
    rwa [hp', hn'] at h

private theorem inclusion_mono (K : DerivedCategory.Plus A) (p n : ℤ) :
    Mono ((Diag K).inclusion p n) := by
  letI := L.package.inclusion_mono (d.source.functor.obj K) p n
  exact inferInstanceAs (Mono ((Lower).map (((Raised).obj (d.source.functor.obj K)).inclusion p n)))

private theorem down_inclusion (K : DerivedCategory.Plus A) (p n : ℤ) :
    (Diag K).down p n ≫ (Diag K).inclusion p n = (Diag K).inclusion (p + 1) n := by
  change (Lower).map _ ≫ (Lower).map _ = (Lower).map _
  rw [← Functor.map_comp, L.package.down_inclusion]

private theorem decreasing (K : DerivedCategory.Plus A) (p n : ℤ) :
    Fil K (p + 1) n ≤ Fil K p n := by
  letI := inclusion_mono.{a,m} f g L d K p n
  letI := inclusion_mono.{a,m} f g L d K (p + 1) n
  dsimp only [filtration]
  exact Subobject.mk_le_mk_of_comm ((Diag K).down p n)
    (by rw [← Category.assoc, down_inclusion.{a,m} f g L d])

private theorem finite (K : DerivedCategory.Plus A) (n : ℤ) :
    letI : OrderBot (Subobject ((targetValue.{a,m} f g n).obj K)) := Subobject.orderBot
    ∃ lo hi : ℤ, (∀ p, p ≤ lo → Fil K p n = ⊤) ∧ (∀ p, hi ≤ p → Fil K p n = ⊥) := by
  obtain ⟨lo, hi, hlo, hhi⟩ := L.package.finite (d.source.functor.obj K) n
  refine ⟨lo, hi, ?_, ?_⟩
  · intro p hp
    letI := inclusion_mono.{a,m} f g L d K p n
    letI := hlo p hp
    letI : IsIso ((Diag K).inclusion p n) :=
      inferInstanceAs (IsIso ((Lower).map (((Raised).obj (d.source.functor.obj K)).inclusion p n)))
    dsimp only [filtration]
    exact Subobject.mk_eq_top_of_isIso _
  · intro p hp
    letI := inclusion_mono.{a,m} f g L d K p n
    dsimp only [filtration]
    apply Subobject.mk_eq_bot_iff_zero.mpr
    exact ((Lower).map_isZero (hhi p hp)).eq_of_src _ _

private theorem filtered_natural {K K' : DerivedCategory.Plus A} (h : K ⟶ K') (p n : ℤ) :
    (Fil K' p n).Factors ((Fil K p n).arrow ≫ (targetValue.{a,m} f g n).map h) := by
  letI := inclusion_mono.{a,m} f g L d K p n
  letI := inclusion_mono.{a,m} f g L d K' p n
  let U := derivedSequence.{a,m} f g L d
  dsimp only [filtration]
  refine ⟨(Subobject.underlyingIso _).hom ≫ (U.map h).step p n, ?_⟩
  change _ ≫ (U.obj K').inclusion p n ≫ (targetIso.{a,m} f g L d n).hom.app K' = _
  simp only [Category.assoc]
  rw [← Category.assoc ((U.map h).step p n), (U.map h).inclusion_comm]
  have hn :
      (U.map h).target n ≫ (targetIso.{a,m} f g L d n).hom.app K' =
        (targetIso.{a,m} f g L d n).hom.app K ≫ (targetValue.{a,m} f g n).map h :=
    (targetIso.{a,m} f g L d n).hom.naturality h
  rw [Category.assoc ((U.obj K).inclusion p n), hn, ← Category.assoc ((U.obj K).inclusion p n)]
  exact Subobject.underlyingIso_hom_comp_eq_mk_assoc _ _

private theorem graded (K : DerivedCategory.Plus A) (n : ℤ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ p : ℤ, (Diag K).differential k p n = 0 ∧
      Nonempty (RowLimit.{a,m} f g L d K k p n) := by
  let W := rowInput.{a,m} f g d K
  let M := relativeRowModel.{a,m} f g L d K
  obtain ⟨N, hN⟩ := L.package.convergence (d.source.functor.obj K) n
  obtain ⟨s₀, _, hs⟩ := M.convergence.stabilization n
  refine ⟨max N s₀.toNat, fun k hk p ↦ ?_⟩
  have hNk : N ≤ k := (le_max_left _ _).trans hk
  obtain ⟨hd, _⟩ := hN k hNk p
  refine ⟨?_, M.convergence.limit M.pages ((k : ℤ) + 2) p n (by omega)
    (hs _ (by omega) p)⟩
  change (Lower).map _ = 0
  rw [hd, Functor.map_zero]

private theorem graded_representatives (K : DerivedCategory.Plus A) (k : ℕ) (p n : ℤ)
    (h : Fil K (p + 1) n ≤ Fil K p n) (e : RowLimit.{a,m} f g L d K k p n) :
    let M := relativeRowModel.{a,m} f g L d K
    let i := modelIso G' L.package.row (rowInput.{a,m} f g d K)
    (Lower).map (closedToPage M.filtration M.pages ((k : ℤ) + 2) p n) ≫
        (Lower).map (i.inv.page k p n) ≫
        (gradedComparison.{a,m} f g L d K k p n h e).hom =
      (Lower).map (closedClass M.filtration p n) ≫ (Lower).map (i.inv.step p n) ≫
        (filtrationStepIso.{a,m} f g L d K p n).hom ≫ cokernel.π (Subobject.ofLE _ _ h) := by
  let W := rowInput.{a,m} f g d K
  let M := relativeRowModel.{a,m} f g L d K
  let i := modelIso G' L.package.row W
  let D := (Raised).obj (d.source.functor.obj K)
  let q := filtrationQuotientIso.{a,m} f g L d K p n h
  let π := cokernel.π (Subobject.ofLE _ _ h)
  have hp : cokernel.π ((Diag K).down p n) ≫ q.hom =
      (filtrationStepIso.{a,m} f g L d K p n).hom ≫ π := by
    simp only [q, π, filtrationQuotientIso, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
  have tail : (Lower).map (cokernel.π (D.down p n)) ≫
        (PreservesCokernel.iso Lower (D.down p n)).hom ≫ q.hom =
      (filtrationStepIso.{a,m} f g L d K p n).hom ≫ π := by
    rw [← Category.assoc]
    exact (congrArg (· ≫ q.hom) (PreservesCokernel.π_iso_hom Lower (D.down p n))).trans hp
  calc
    _ = (Lower).map (closedToPage M.filtration M.pages ((k : ℤ) + 2) p n ≫
        i.inv.page k p n ≫ (rowGradedIso G' L.package.row W k p n e).hom) ≫
          (PreservesCokernel.iso Lower (D.down p n)).hom ≫ q.hom := by
      simp only [gradedComparison, changeGradedIso, Iso.trans_hom, Functor.mapIso_hom,
        Functor.map_comp, Category.assoc, W, M, i, D, q]
    _ = _ := by
      rw [row_representative]
      change (Lower).map (closedClass M.filtration p n ≫ i.inv.step p n ≫
        cokernel.π (D.down p n)) ≫ (PreservesCokernel.iso Lower (D.down p n)).hom ≫ q.hom =
        (Lower).map (closedClass M.filtration p n) ≫ (Lower).map (i.inv.step p n) ≫
          (filtrationStepIso.{a,m} f g L d K p n).hom ≫ π
      simp only [Functor.map_comp, Category.assoc, tail]

private theorem filtrationQuotientIso_natural {K K' : DerivedCategory.Plus A} (h : K ⟶ K')
    (p n : ℤ) (leK : Fil K (p + 1) n ≤ Fil K p n)
    (leK' : Fil K' (p + 1) n ≤ Fil K' p n) :
    (gradedEval p n).map ((derivedSequence.{a,m} f g L d).map h) ≫
      (filtrationQuotientIso.{a,m} f g L d K' p n leK').hom =
    (filtrationQuotientIso.{a,m} f g L d K p n leK).hom ≫
      filtrationQuotientMap.{a,m} f g L d h p n leK leK' := by
  apply (cancel_epi (cokernel.π ((Diag K).down p n))).1
  simp only [gradedEval, filtrationQuotientIso, filtrationQuotientMap, cokernel.mapIso_hom,
    cokernel.map, cokernel.π_desc_assoc, cokernel.π_desc, filtrationStepMap,
    Category.assoc, Iso.hom_inv_id_assoc]

private theorem graded_natural {K K' : DerivedCategory.Plus A} (h : K ⟶ K') (n : ℤ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ (p : ℤ)
      (e : RowLimit.{a,m} f g L d K k p n) (e' : RowLimit.{a,m} f g L d K' k p n),
    ((derivedSequence.{a,m} f g L d).map h).page k p n ≫
        (gradedComparison.{a,m} f g L d K' k p n
          (decreasing.{a,m} f g L d K' p n) e').hom =
      (gradedComparison.{a,m} f g L d K k p n
        (decreasing.{a,m} f g L d K p n) e).hom ≫
      filtrationQuotientMap.{a,m} f g L d h p n (decreasing.{a,m} f g L d K p n)
        (decreasing.{a,m} f g L d K' p n) := by
  let h' : rowInput.{a,m} f g d K ⟶ rowInput.{a,m} f g d K' :=
    (F').rightDerivedFunctorPlus.map (d.source.functor.map h)
  obtain ⟨N, hN⟩ := localized_limit_square G' L.package.row h' n
  refine ⟨N, fun k hk p e e' ↦ ?_⟩
  let U := derivedSequence.{a,m} f g L d
  let i := changeGradedIso Lower ((Raised).obj (d.source.functor.obj K)) k p n
    (rowGradedIso G' L.package.row (rowInput.{a,m} f g d K) k p n e)
  let j := changeGradedIso Lower ((Raised).obj (d.source.functor.obj K')) k p n
    (rowGradedIso G' L.package.row (rowInput.{a,m} f g d K') k p n e')
  let leK := decreasing.{a,m} f g L d K p n
  let leK' := decreasing.{a,m} f g L d K' p n
  let q := filtrationQuotientIso.{a,m} f g L d K p n leK
  let q' := filtrationQuotientIso.{a,m} f g L d K' p n leK'
  let qmap := filtrationQuotientMap.{a,m} f g L d h p n leK leK'
  have sq : (U.map h).page k p n ≫ j.hom = i.hom ≫ (gradedEval p n).map (U.map h) :=
    gradedSquare_change Lower (hN k hk p e e')
  have qu : (gradedEval p n).map (U.map h) ≫ q'.hom = q.hom ≫ qmap :=
    filtrationQuotientIso_natural.{a,m} f g L d h p n leK leK'
  change (U.map h).page k p n ≫ (j.hom ≫ q'.hom) = (i.hom ≫ q.hom) ≫ qmap
  rw [← Category.assoc ((U.map h).page k p n), sq, Category.assoc, qu, Category.assoc]


private theorem row_comparison (M : SheafOfModules.{m} R) (n : ℕ) :
    (rowPage.{a,m} f g L d n).hom.app M ≫ (rowEdge.{a,m} f g L d n).app M =
      (Lower).map ((L.edges.filtered ((raisedSheafInput.{a,m} f g).obj M)).row n) ≫
        (sheafTargetIso.{a,m} f g L d n).hom.app M := by
  simp only [rowPage, rowEdge, sheafTargetIso, Iso.trans_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, L.row_comparison, Functor.map_comp_assoc]

private theorem column_comparison (M : SheafOfModules.{m} R) (n : ℕ) :
    (sheafTargetIso.{a,m} f g L d n).hom.app M ≫ (columnEdge.{a,m} f g L d n).app M =
      (Lower).map ((L.edges.filtered ((raisedSheafInput.{a,m} f g).obj M)).column n) ≫
        (columnPage.{a,m} f g L d n).hom.app M := by
  simp only [columnPage, columnEdge, sheafTargetIso, Iso.trans_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, L.column_comparison, Functor.map_comp_assoc]

private theorem derived_square (K : DerivedCategory.Plus A) :
    d.target.functor.map ((originalCompositionMap.{a,m} f g).app K) ≫
        (composeFunctorSquares d.first.iso d.second.iso).hom.app K =
      (d.compositeIso f g).hom.app K ≫
        (RelativeLeray.compositionMap R' S' T' f' g' φ' ψ').app (d.source.functor.obj K) := by
  simp only [originalCompositionMap, SiteComparison.compositeIso, RelativeLeray.compositionMap,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [d.derived]

private theorem target_canonical [IsIso (originalCompositionMap.{a,m} f g)] (n : ℤ) :
    targetIso.{a,m} f g L d n = iteratedTargetIso.{a,m} f g L d n ≪≫
      isoWhiskerRight (asIso (originalCompositionMap.{a,m} f g)).symm
        (DerivedCategory.Plus.homologyFunctor C n) := by
  let H := DerivedCategory.Plus.homologyFunctor C n
  let H' := DerivedCategory.Plus.homologyFunctor (SheafTheory.Modules T') n
  let c := originalCompositionMap.{a,m} f g
  let c' := RelativeLeray.compositionMap R' S' T' f' g' φ' ψ'
  let i := composeFunctorSquares d.first.iso d.second.iso
  let h := (d.target.cohomology n).symm
  let e := composeFunctorSquares (d.compositeIso f g) h
  let e' := composeFunctorSquares i h
  have hc : whiskerRight (whiskerRight c H) JZ ≫ e'.hom =
      e.hom ≫ whiskerLeft d.source.functor (whiskerRight c' H') := by
    ext K : 2
    have hn := h.hom.naturality (c.app K)
    change (JZ).map (H.map (c.app K)) ≫ h.hom.app _ =
      h.hom.app _ ≫ H'.map (d.target.functor.map (c.app K)) at hn
    change (JZ).map (H.map (c.app K)) ≫ (𝟙 _ ≫ h.hom.app _ ≫ 𝟙 _ ≫ H'.map (i.hom.app K) ≫ 𝟙 _) =
      (𝟙 _ ≫ h.hom.app _ ≫ 𝟙 _ ≫ H'.map ((d.compositeIso f g).hom.app K) ≫ 𝟙 _) ≫
        H'.map (c'.app (d.source.functor.obj K))
    simp only [Category.assoc, Category.id_comp, Category.comp_id]
    erw [reassoc_of% hn, ← H'.map_comp, ← H'.map_comp]
    exact congrArg (fun k ↦ h.hom.app _ ≫ H'.map k) (derived_square.{a,m} f g d K)
  have hLower := lowerIso_naturality e e' (whiskerRight c H)
    (whiskerLeft d.source.functor (whiskerRight c' H')) hc
  have hUpper : (L.targetIso n).hom ≫ whiskerRight c' H' = (L.package.iteratedIso n).hom := by
    letI : IsIso c' := L.composition_isIso
    rw [L.targetIso_canonical n]
    change ((L.package.iteratedIso n).hom ≫ whiskerRight (asIso c').inv H') ≫
      whiskerRight (asIso c').hom H' = _
    rw [Category.assoc, ← whiskerRight_comp, Iso.inv_hom_id, whiskerRight_id', Category.comp_id]
  apply Iso.ext
  apply ((isoWhiskerRight (asIso c) H).eq_comp_inv).2
  change (_ ≫ (lowerIso e).hom) ≫ whiskerRight c H =
    _ ≫ (lowerIso e').hom
  rw [Category.assoc, hLower]
  change whiskerRight (whiskerLeft d.source.functor (L.targetIso n).hom) Lower ≫
      whiskerRight (whiskerLeft d.source.functor (whiskerRight c' H')) Lower ≫ (lowerIso e').hom =
    whiskerRight (whiskerLeft d.source.functor (L.package.iteratedIso n).hom) Lower ≫ (lowerIso e').hom
  rw [← Category.assoc, ← whiskerRight_comp, ← whiskerLeft_comp, hUpper]

private theorem sheaf_target (n : ℕ) :
    sheafTargetIso.{a,m} f g L d n =
      isoWhiskerRight (sheafSequenceComparison.{a,m} f g L d) (targetEval (n : ℤ)) ≪≫
      isoWhiskerLeft (sheafPlacement.{a,m} f g) (targetIso.{a,m} f g L d n) := by
  apply Iso.ext
  ext M : 2
  simp only [sheafTargetIso, L.sheafTargetIso_eq, sheafTargetCoordinate,
    sheafSequenceComparison, sheafInputComparison, targetIso, targetCoordinates,
    lowerIso, composeFunctorSquares, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    isoWhiskerLeft_hom, isoWhiskerLeft_inv, isoWhiskerRight_hom, isoWhiskerRight_inv,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
    associator_inv_app, rightUnitor_hom_app, Functor.comp_obj, Functor.comp_map,
    targetEval, LerayIndependentCoefficients.changeCoefficients,
    Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  have h := congrArg (fun k ↦ (Lower).map k)
    ((L.targetIso (n : ℤ)).hom.naturality
      ((stalkCoordinates JX d.source).hom.app ((Lifts).obj M)))
  simp only [Functor.comp_map, Functor.map_comp, targetEval] at h
  erw [← reassoc_of% h]

end

/-- Relative Leray in the original ringed-space data, including the two
edge comparisons for sheaves. -/
theorem relativeLeray : relativeLerayType.{a,m,u,v,w,r,s,t} := by
  intro X Y Z R S T f g
  letI := sectionHasSheafify.{max a m v w r s t,u} X
  letI := sectionWEqualsLocallyBijective.{max a m v w r s t,u} X
  letI := sectionHasSheafify.{max a m u w r s t,v} Y
  letI := sectionWEqualsLocallyBijective.{max a m u w r s t,v} Y
  letI := sectionHasSheafify.{max a m u v r s t,w} Z
  letI := sectionWEqualsLocallyBijective.{max a m u v r s t,w} Z
  letI := ambient_enough_injectives.{max a m v w s t,u,r} X R
  letI := ambient_enough_injectives.{max a m u w r t,v,s} Y S
  letI := transportIsEquivalence.{max a m v w s t,u,r} R
  letI := transportIsEquivalence.{max a m u w r t,v,s} S
  letI := transportIsEquivalence.{max a m u v r s,w,t} T
  have hAcyclic := HigherDirectImagesIndependentCoefficients.relativeUnitIso.{max a m,u,v,r,s,w,t} f g
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hAcyclic, ?_⟩
  letI : PreservesFiniteLimits F :=
    HigherDirectImagesIndependentCoefficients.leftExact.{max a m u v w r s t,u,v,r,s} f
  letI : PreservesFiniteLimits G :=
    HigherDirectImagesIndependentCoefficients.leftExact.{max a m u v w r s t,v,w,s,t} g
  letI := (RightDerivedComposition.comparisonIsoIff A B C F G).mpr hAcyclic
  letI : IsIso (comparisonValue F G) := NatIso.isIso_of_isIso_app _
  letI : IsIso (originalCompositionMap.{a,m} f g) := by
    unfold originalCompositionMap
    infer_instance
  obtain ⟨L, _, _⟩ := RelativeLeray.relativeLeray.{max a m u v w r s t} R' S' T' f' g' φ' ψ'
  let d := siteComparison.{a,m} f g L (inferInstance : IsIso (comparisonValue F G))
  refine ⟨L, d, {
    composition_isIso := inferInstance
    composition_transport := derived_square.{a,m} f g d
    target_canonical := fun n ↦ target_canonical.{a,m} f g L d n
    sheaf_target := sheaf_target.{a,m} f g L d
    negative_columns := negative_columns.{a,m} f g L d
    decreasing := decreasing.{a,m} f g L d
    finite := finite.{a,m} f g L d
    filtered_natural := fun h => filtered_natural.{a,m} f g L d h
    graded := graded.{a,m} f g L d
    graded_representatives := fun K k p n e =>
      graded_representatives.{a,m} f g L d K k p n _ e
    graded_natural := fun h => graded_natural.{a,m} f g L d h
    sheaf_quadrant := fun M k p n h => ((JZ).asEquivalence.inverse).map_isZero
      (L.sheaf_quadrant ((raisedSheafInput.{a,m} f g).obj M) k p n h)
    row_comparison := row_comparison.{a,m} f g L d
    column_comparison := column_comparison.{a,m} f g L d }⟩

end AdvancedHomologicalAlgebra.RelativeLerayIndependentCoefficients
