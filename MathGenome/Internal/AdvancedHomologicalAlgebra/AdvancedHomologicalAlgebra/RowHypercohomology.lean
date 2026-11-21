import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.RowHypercohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SplitRowExtension
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleComplexFirstPages
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CartanEilenbergTotalization
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CartanEilenbergExistence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleComplexConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TotalRightDerivedFunctor
import Batteries.Tactic.OpenPrivate

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex
universe v u v' u'
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvancedHomologicalAlgebra.RowHypercohomology
open CartanEilenbergData CartanEilenbergTotalization
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]

/-- An additive functor preserves the cokernel of a morphism with a
generalized inverse. The proof uses an explicit retraction of its cokernel. -/
lemma preservesCokernel_of_generalizedInverse (F : A ⥤ B) [F.Additive]
    {X Y : A} (f : X ⟶ Y) (s : Y ⟶ X) (hs : f ≫ s ≫ f = f) :
    PreservesColimit (parallelPair f 0) F := by
  let π := cokernel.π f
  let t : cokernel f ⟶ Y := cokernel.desc f (𝟙 Y - s ≫ f) (by
    simp only [Preadditive.comp_sub, comp_id, ← Category.assoc]
    exact sub_eq_zero.mpr (by simpa only [Category.assoc] using hs.symm))
  have hπt : π ≫ t = 𝟙 Y - s ≫ f := cokernel.π_desc _ _ _
  have htπ : t ≫ π = 𝟙 _ := by
    apply (cancel_epi π).1
    rw [← Category.assoc, hπt]
    simp [π, Preadditive.sub_comp, Category.assoc]
  have hmap : F.map π ≫ F.map t = 𝟙 _ - F.map s ≫ F.map f := by
    rw [← F.map_comp, hπt, F.map_sub, F.map_id, F.map_comp]
  have hsplit : F.map t ≫ F.map π = 𝟙 _ := by
    rw [← F.map_comp, htπ, F.map_id]
  letI : Epi (F.map π) := ⟨fun a b hab => by
    simpa only [← Category.assoc, hsplit, id_comp] using congrArg (F.map t ≫ ·) hab⟩
  have hcolim := CokernelCofork.IsColimit.ofπ' (F.map π)
    (show F.map f ≫ F.map π = 0 by simp [π, ← F.map_comp]) (fun k hk =>
      ⟨F.map t ≫ k, by
        rw [← Category.assoc, hmap]
        simp [Preadditive.sub_comp, Category.assoc, hk]⟩)
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  exact (isColimitMapCoconeCoforkEquiv' F (cokernel.condition f)).symm hcolim

/-- Split incoming differential implies preservation of its cokernel inside
the cycles. Left exactness supplies preservation of the outgoing kernel. -/
lemma preservesLeftHomology_of_generalizedInverse (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (S : ShortComplex A)
    (s : S.X₂ ⟶ S.X₁) (hs : S.f ≫ s ≫ S.f = S.f) :
    F.PreservesLeftHomologyOf S := by
  let h := S.homologyData.left
  have hinv : h.f' ≫ (h.i ≫ s) ≫ h.f' = h.f' := by
    apply (cancel_mono h.i).1
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    rw [← Category.assoc h.f' h.i, ShortComplex.LeftHomologyData.f'_i]
    exact hs
  letI : h.IsPreservedBy F :=
    ⟨inferInstance, preservesCokernel_of_generalizedInverse F h.f' (h.i ≫ s) hinv⟩
  exact Functor.PreservesLeftHomologyOf.mk' F h

/-- Every horizontal row has generalized inverses, also at negative vertical
degree where every term is a zero object. -/
lemma row_generalizedInverse {K : CochainComplex A ℤ} (R : ResolutionData K)
    (p i j : ℤ) : ∃ s : (R.bicomplex.flip.X p).X j ⟶
      (R.bicomplex.flip.X p).X i,
      (R.bicomplex.flip.X p).d i j ≫ s ≫ (R.bicomplex.flip.X p).d i j =
        (R.bicomplex.flip.X p).d i j := by
  by_cases hp : 0 ≤ p
  · letI : ∀ q, Injective ((R.bicomplex.flip.X p).X q) :=
      fun q => (R.terms q).injective p hp
    letI : ∀ q, Injective ((R.bicomplex.flip.X p).cycles q) :=
      fun q => (R.cycles q).injective p hp
    exact SplitRowExtension.differential_has_generalized_inverse _ i j
  · refine ⟨0, ?_⟩
    exact (R.nonnegative i p (by omega)).eq_of_src _ _

lemma preservesRowHomology (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {K : CochainComplex A ℤ} (R : ResolutionData K) (p q : ℤ) :
    F.PreservesLeftHomologyOf ((R.bicomplex.flip.X p).sc q) := by
  obtain ⟨s, hs⟩ := row_generalizedInverse R p ((ComplexShape.up ℤ).prev q) q
  exact preservesLeftHomology_of_generalizedInverse F _ s hs

/-- The canonical kernel/cokernel homology comparison, with no chosen splitting
in its value. Generalized inverses prove only its invertibility. -/
def splitRowIso (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {K : CochainComplex A ℤ} (R : ResolutionData K) (p q : ℤ) :
    (((mapDouble F).obj R.bicomplex).flip.X p).homology q ≅
      F.obj ((R.bicomplex.flip.X p).homology q) := by
  letI := preservesRowHomology F R p q
  exact ((R.bicomplex.flip.X p).sc q).mapHomologyIso F

theorem splitRowIso_naturality_rows (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {K L : CochainComplex A ℤ} (R : ResolutionData K) (S : ResolutionData L)
    (p p' q : ℤ) (a : R.bicomplex.flip.X p ⟶ S.bicomplex.flip.X p') :
    homologyMap ((F.mapHomologicalComplex (.up ℤ)).map a) q ≫
        (splitRowIso F S p' q).hom =
      (splitRowIso F R p q).hom ≫ F.map (homologyMap a q) := by
  letI := preservesRowHomology F R p q
  letI := preservesRowHomology F S p' q
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor A (.up ℤ) q).map a) F

theorem splitRowIso_naturality (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {K L : CochainComplex A ℤ} (R : ResolutionData K) (S : ResolutionData L)
    (p q : ℤ) (a : R.bicomplex.flip.X p ⟶ S.bicomplex.flip.X p) :
    homologyMap ((F.mapHomologicalComplex (.up ℤ)).map a) q ≫
        (splitRowIso F S p q).hom =
      (splitRowIso F R p q).hom ≫ F.map (homologyMap a q) :=
  splitRowIso_naturality_rows F R S p p q a

def splitRowComparison (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] :
    SplitRowComparison F where
  iso := splitRowIso F
  naturality := splitRowIso_naturality F
  on_cycles := by
    intro K R p q
    let J := R.bicomplex.flip.X p
    let FJ := ((mapDouble F).obj R.bicomplex).flip.X p
    let S := J.sc q
    letI := preservesRowHomology F R p q
    let h := S.leftHomologyData
    let hF := h.map F
    have hl : FJ.liftCycles (F.map (J.iCycles q)) (q + 1) (by simp) (by
        change F.map (J.iCycles q) ≫ F.map (J.d q (q + 1)) = 0
        rw [← F.map_comp, J.iCycles_d, F.map_zero]) = hF.cyclesIso.inv := by
      apply (cancel_mono (FJ.iCycles q)).1
      rw [HomologicalComplex.liftCycles_i]
      change _ = hF.cyclesIso.inv ≫ (S.map F).iCycles
      rw [hF.cyclesIso_inv_comp_iCycles]
      rfl
    change FJ.liftCycles (F.map (J.iCycles q)) (q + 1) _ _ ≫
      FJ.homologyπ q ≫ (splitRowIso F R p q).hom = _
    rw [hl]
    change hF.cyclesIso.inv ≫ (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      F.map S.homologyπ
    rw [h.mapHomologyIso_eq F, Iso.trans_hom]
    simp only [Functor.mapIso_hom, Iso.symm_hom]
    rw [hF.homologyπ_comp_homologyIso_hom_assoc, Iso.inv_hom_id_assoc]
    change F.map h.π ≫ F.map h.homologyIso.inv = _
    rw [← F.map_comp, h.π_comp_homologyIso_inv]
    congr 1
    have he : h.cyclesIso.inv = 𝟙 S.cycles := by
      apply (cancel_mono S.iCycles).1
      rw [h.cyclesIso_inv_comp_iCycles]
      change S.iCycles = 𝟙 S.cycles ≫ S.iCycles
      exact (Category.id_comp _).symm
    rw [he]
    change 𝟙 S.cycles ≫ S.homologyπ = S.homologyπ
    exact Category.id_comp _

theorem splitRows : Specs.SplitRows.{v,u,v',u'} := by
  intro A _ _ B _ _ F _ _
  exact ⟨splitRowComparison F⟩

/-- Horizontal cohomology and F commute as vertical complexes, not just
degree by degree. This is the bridge to the simultaneous H-resolution. -/
def rowInvariantIso (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {K : CochainComplex A ℤ} (R : ResolutionData K) (q : ℤ) :
    mappedCohomologyColumn F R q ≅
      (F.mapHomologicalComplex (.up ℤ)).obj (cohomologyColumn R q) :=
  Hom.isoOfComponents (fun p => splitRowIso F R p q) (fun p p' _ =>
    (splitRowIso_naturality_rows F R R p p' q (R.bicomplex.flip.d p p')).symm)

theorem rowInvariantIso_naturality (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {K L : CochainComplex A ℤ} (R : ResolutionData K) (S : ResolutionData L)
    (a : R.bicomplex ⟶ S.bicomplex) (q : ℤ) :
    cohomologyColumnMap ((mapDouble F).map a) q ≫ (rowInvariantIso F S q).hom =
      (rowInvariantIso F R q).hom ≫
        (F.mapHomologicalComplex (.up ℤ)).map (cohomologyColumnMap a q) := by
  ext p
  exact splitRowIso_naturality F R S p q ((CartanEilenbergComparison.rowMap a).f p)

theorem invariantColumns : Specs.InvariantColumns.{v,u,v',u'} := by
  intro A _ _ B _ _ F _ _
  exact ⟨rowInvariantIso F, rowInvariantIso_naturality F⟩

section Pages
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  {K : CochainComplex A ℤ} (R : ResolutionData K)
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
  (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
  (D : F03Specs.PageData Fr)
  (P : DoubleComplexFirstPages.RowData ((mapDouble F).obj R.bicomplex) Fr hFr D)

def rowFirstIso (p q : ℤ) : DoubleComplexFirstPages.page Fr D 1 p q ≅
    F.obj ((R.bicomplex.flip.X p).homology q) :=
  P.firstIso p q ≪≫ splitRowIso F R p q

theorem rowFirstIso_d (p q : ℤ) :
    DoubleComplexFirstPages.firstDifferential Fr D p q ≫
        (rowFirstIso F R Fr hFr D P (p+1) q).hom =
      (rowFirstIso F R Fr hFr D P p q).hom ≫ ((ComplexShape.up ℤ).ε q •
        F.map (homologyMap (R.bicomplex.flip.d p (p+1)) q)) := by
  dsimp only [rowFirstIso, Iso.trans_hom]
  rw [← Category.assoc, P.first_d]
  have hd : (((mapDouble F).obj R.bicomplex).flip.d p (p+1)) =
      (F.mapHomologicalComplex (.up ℤ)).map (R.bicomplex.flip.d p (p+1)) := by
    ext i
    rfl
  rw [hd]
  simpa only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul] using
    congrArg (fun z => (P.firstIso p q).hom ≫ ((ComplexShape.up ℤ).ε q • z))
      (splitRowIso_naturality_rows F R R p (p+1) q (R.bicomplex.flip.d p (p+1)))

def rowSecondIso (p q : ℤ) : DoubleComplexFirstPages.page Fr D 2 p q ≅
    ((F.mapHomologicalComplex (.up ℤ)).obj (cohomologyColumn R q)).homology p :=
  P.secondIso p q ≪≫ (homologyFunctor B (.up ℤ) p).mapIso (rowInvariantIso F R q)

/-- The factor prescribed by signed interchange removes the raw first-page
sign. It is an actual isomorphism, since (-1)^(pq) is a unit. -/
def rowSignedFirstIso (p q : ℤ) : DoubleComplexFirstPages.page Fr D 1 p q ≅
    F.obj ((R.bicomplex.flip.X p).homology q) :=
  (p*q).negOnePow • rowFirstIso F R Fr hFr D P p q

theorem rowSignedFirstIso_d (p q : ℤ) :
    DoubleComplexFirstPages.firstDifferential Fr D p q ≫
        (rowSignedFirstIso F R Fr hFr D P (p+1) q).hom =
      (rowSignedFirstIso F R Fr hFr D P p q).hom ≫
        F.map (homologyMap (R.bicomplex.flip.d p (p+1)) q) := by
  dsimp only [rowSignedFirstIso]
  simp only [Preadditive.smul_iso_hom, Linear.comp_units_smul, rowFirstIso_d,
    Linear.units_smul_comp, smul_smul]
  change (((p+1)*q).negOnePow * q.negOnePow) • _ = (p*q).negOnePow • _
  congr 1
  rw [add_mul, one_mul, Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]

def firstPageComputation : FirstPageComputation F R Fr hFr D where
  row := P
  split := splitRowComparison F
  raw_d := rowFirstIso_d F R Fr hFr D P
  signed_d p q := by
    change D.differential 1 (by omega) p (p+q) ≫ _ ≫
      (rowSignedFirstIso F R Fr hFr D P (p+1) q).hom =
      (rowSignedFirstIso F R Fr hFr D P p q).hom ≫
        F.map (homologyMap (R.bicomplex.flip.d p (p+1)) q)
    simpa only [DoubleComplexFirstPages.firstDifferential, Category.assoc] using
      rowSignedFirstIso_d F R Fr hFr D P p q
  signedShortComplex a q := DoubleComplexFirstPages.firstPageShortIso Fr D
    (mappedOriginalColumn F R q) q (fun p => rowSignedFirstIso F R Fr hFr D P p q)
    (fun p => rowSignedFirstIso_d F R Fr hFr D P p q) a
  signedShortComplex_left _ _ := rfl
  signedShortComplex_middle _ _ := rfl
  signedShortComplex_right _ _ := rfl

omit [PreservesFiniteLimits F] in
private lemma nextIso_unique (N N' : PageCohomology.Data Fr D)
    (r : ℤ) (hr : 0 ≤ r) (a n : ℤ) :
    N.nextIso r hr a n = N'.nextIso r hr a n := by
  apply Iso.ext
  apply (cancel_epi (FilteredPage.toPage Fr (r+1) (a+r) (n+1)
    (D.containment (r+1) (a+r) (n+1)))).1
  rw [N.nextIso_formula, N'.nextIso_formula]

private lemma homologyIsoSc'_naturality {J L : CochainComplex B ℤ}
    (e : J ≅ L) (a : ℤ) :
    (J.homologyIsoSc' a (a+1) (a+1+1) (by simp) (by simp)).symm ≪≫
        (homologyFunctor B (.up ℤ) (a+1)).mapIso e =
      ShortComplex.homologyMapIso ((shortComplexFunctor' B (.up ℤ)
        a (a+1) (a+1+1)).mapIso e) ≪≫
        (L.homologyIsoSc' a (a+1) (a+1+1) (by simp) (by simp)).symm := by
  apply Iso.ext
  simpa [homologyFunctorIso', homologyFunctorIso, homologyIsoSc', ShortComplex.homologyMapIso] using
    ((homologyFunctorIso' B (.up ℤ) a (a+1) (a+1+1) (by simp) (by simp)).inv.naturality
      e.hom).symm

/-- The HA-B03 comparison followed by the map on column cohomology is the
homology of the signed first-page maps, with the same next-page comparison. -/
lemma rowSecondIso_eq (N : PageCohomology.Data Fr D) (p q : ℤ) :
    rowSecondIso F R Fr hFr D P p q =
      (firstPageComputation F R Fr hFr D P).secondPageIso F R Fr hFr D N p q := by
  suffices hn : ∀ a : ℤ,
      rowSecondIso F R Fr hFr D P (a+1) q =
        (firstPageComputation F R Fr hFr D P).secondPageIso F R Fr hFr D N (a+1) q by
    exact Eq.mp (congrArg (fun t => rowSecondIso F R Fr hFr D P t q =
      (firstPageComputation F R Fr hFr D P).secondPageIso F R Fr hFr D N t q)
      (show p-1+1 = p by omega)) (hn (p-1))
  intro a
  let J := DoubleComplexFirstPages.verticalHomology ((mapDouble F).obj R.bicomplex).flip q
  let L := mappedOriginalColumn F R q
  let e : J ≅ L := rowInvariantIso F R q
  let U := DoubleComplexFirstPages.firstPageShortIso Fr D J q
    (fun p => (p*q).negOnePow • P.firstIso p q) (fun p => P.signed_first_d p q) a
  let V := (shortComplexFunctor' B (.up ℤ) a (a+1) (a+1+1)).mapIso e
  let W := (firstPageComputation F R Fr hFr D P).signedShortComplex a q
  have hw : U ≪≫ V = W := by
    apply Iso.ext
    ext
    · simp only [U, V, W, DoubleComplexFirstPages.firstPageShortIso, firstPageComputation,
        Iso.trans_hom, ShortComplex.comp_τ₁, ShortComplex.isoMk_hom_τ₁, Functor.mapIso_hom,
        shortComplexFunctor'_map_τ₁, rowSignedFirstIso, rowFirstIso,
        Preadditive.smul_iso_hom, Linear.units_smul_comp]
      rfl
    · simp only [U, V, W, DoubleComplexFirstPages.firstPageShortIso, firstPageComputation,
        Iso.trans_hom, ShortComplex.comp_τ₂, ShortComplex.isoMk_hom_τ₂, Functor.mapIso_hom,
        shortComplexFunctor'_map_τ₂, rowSignedFirstIso, rowFirstIso,
        Preadditive.smul_iso_hom, Linear.units_smul_comp, Category.assoc]
      rfl
    · simp only [U, V, W, DoubleComplexFirstPages.firstPageShortIso, firstPageComputation,
        Iso.trans_hom, ShortComplex.comp_τ₃, ShortComplex.isoMk_hom_τ₃, Functor.mapIso_hom,
        shortComplexFunctor'_map_τ₃, rowSignedFirstIso, rowFirstIso,
        Preadditive.smul_iso_hom, Linear.units_smul_comp, Category.assoc]
      rfl
  obtain ⟨N', hN'⟩ := P.second_formula q
  have hNa := hN' a
  dsimp only at hNa
  change P.secondIso (a+1) q ≪≫ (homologyFunctor B (.up ℤ) (a+1)).mapIso e = _
  rw [← hNa, nextIso_unique F R Fr D N' N]
  have hs := homologyIsoSc'_naturality e a
  change (_ ≪≫ _ ≪≫ ShortComplex.homologyMapIso U ≪≫
      (J.homologyIsoSc' a (a+1) (a+1+1) (by simp) (by simp)).symm) ≪≫
      (homologyFunctor B (.up ℤ) (a+1)).mapIso e = _
  have hcenter (b : ℤ) (hb : b+1 = a+1) (hn : b+q+1 = a+1+q) :
      eqToIso (congrArg₂ (PageCohomology.object Fr D 2) hb.symm hn.symm) ≪≫
        N.nextIso 1 (by omega) b (b+q) ≪≫
        ShortComplex.homologyMapIso
          ((firstPageComputation F R Fr hFr D P).signedShortComplex b q) ≪≫
        (L.homologyIsoSc' b (b+1) (b+1+1) (by simp) (by simp)).symm ≪≫
        eqToIso (congrArg (fun i : ℤ => L.homology i) hb) =
      eqToIso (congrArg (PageCohomology.object Fr D 2 (a+1))
        (show a+1+q = a+q+1 by omega)) ≪≫ N.nextIso 1 (by omega) a (a+q) ≪≫
        ShortComplex.homologyMapIso W ≪≫
        (L.homologyIsoSc' a (a+1) (a+1+1) (by simp) (by simp)).symm := by
    have hba : b = a := by omega
    subst b
    apply Iso.ext
    simp only [Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
    rfl
  have hM := hcenter (a+1-1) (by omega) (by omega)
  change (firstPageComputation F R Fr hFr D P).secondPageIso F R Fr hFr D N (a+1) q = _ at hM
  rw [hM]
  apply Iso.ext
  have hcomp : (ShortComplex.homologyMapIso U).hom ≫
      (ShortComplex.homologyMapIso V).hom = (ShortComplex.homologyMapIso W).hom := by
    rw [← hw]
    simp only [ShortComplex.homologyMapIso_hom, Iso.trans_hom, ShortComplex.homologyMap_comp]
  have h := congrArg Iso.hom hs
  change (J.homologyIsoSc' a (a+1) (a+1+1) (by simp) (by simp)).symm.hom ≫
      ((homologyFunctor B (.up ℤ) (a+1)).mapIso e).hom =
    (ShortComplex.homologyMapIso V).hom ≫
      (L.homologyIsoSc' a (a+1) (a+1+1) (by simp) (by simp)).symm.hom at h
  simp only [Iso.trans_hom, Category.assoc, h, reassoc_of% hcomp]

/-- The signed coordinate change above is precisely the one induced by
the total interchange map on the actual page quotients. -/
theorem rowSignedFirstIso_interchange
    [((mapDouble F).obj R.bicomplex).flip.HasTotal (.up ℤ)]
    (G : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex).flip))
    (hG : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex).flip Prod.fst G)
    (Dt : F03Specs.PageData G) (p q : ℤ) :
    (DoubleComplexFirstPages.interchangePageIso ((mapDouble F).obj R.bicomplex)
      Fr G hFr hG D Dt 1 p (p+q)).hom ≫
        (DoubleComplexFirstPages.columnFirstIso ((mapDouble F).obj R.bicomplex).flip
          G hG Dt p q).hom ≫ (splitRowIso F R p q).hom =
      (rowSignedFirstIso F R Fr hFr D P p q).hom := by
  rw [← Category.assoc, DoubleComplexFirstPages.interchange_firstIso
    ((mapDouble F).obj R.bicomplex) Fr G hFr hG D Dt P p q,
    Linear.units_smul_comp]
  rfl
end Pages

theorem rowPages : Specs.RowPages.{v,u,v',u'} := by
  intro A _ _ B _ _ F _ _ K R _ Fr hFr D
  let P := (DoubleComplexFirstPages.system B).row _
    (CartanEilenbergTotalization.map_finite F R.bicomplex
      (CartanEilenbergTotalization.resolution_finite R)) Fr hFr D
  let M := firstPageComputation F R Fr hFr D P
  let N := PageCohomology.data Fr D
  exact ⟨M, N, M.secondPageIso F R Fr hFr D N, fun _ _ => rfl⟩

/-- Equality on one page propagates to all subsequent actual page quotients.
No filtered homotopy, convergence, or projective representatives are needed. -/
lemma pageMaps_eq_of_eq {X Y : FilteredComplex B} {f g : FilteredMap X Y}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    (M : FilteredPageFunctoriality.MapData f D E)
    (N : FilteredPageFunctoriality.MapData g D E)
    (r₀ : ℤ) (hr₀ : 0 ≤ r₀) (h : ∀ p n, M.map r₀ p n = N.map r₀ p n)
    (r : ℤ) (hr : r₀ ≤ r) : ∀ p n, M.map r p n = N.map r p n := by
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hr
  clear hr
  induction k with
  | zero =>
    rw [Int.natCast_zero, add_zero]
    exact h
  | succ k ih =>
    intro p n
    let s : ℤ := r₀ + (k : ℤ)
    have hs : 0 ≤ s := by dsimp [s]; omega
    have hc : FilteredPageFunctoriality.shortComplexMap M s hs (p-s) (n-1) =
        FilteredPageFunctoriality.shortComplexMap N s hs (p-s) (n-1) := by
      ext <;> apply ih
    have hm := FilteredPageFunctoriality.next_naturality M
      (PageCohomology.data X.filtration D) (PageCohomology.data Y.filtration E)
      s hs (p-s) (n-1)
    have hn := FilteredPageFunctoriality.next_naturality N
      (PageCohomology.data X.filtration D) (PageCohomology.data Y.filtration E)
      s hs (p-s) (n-1)
    rw [hc] at hm
    have hh := (cancel_mono
      ((PageCohomology.data Y.filtration E).nextIso s hs (p-s) (n-1)).hom).1
      (hm.trans hn.symm)
    rw [sub_add_cancel, sub_add_cancel] at hh
    rw [show r₀ + ((k+1 : ℕ) : ℤ) = s+1 by dsimp [s]; omega]
    exact hh

section TransportMaps
variable {H H' : A}

lemma transportStepMap_arrow {J J' : A} (e : H ≅ H') (e' : J ≅ J')
    (P : Subobject H) (Q : Subobject J)
    (f : H ⟶ J) (f' : H' ⟶ J') (hf : e.hom ≫ f' = f ≫ e'.hom)
    (m : (P : A) ⟶ (Q : A)) (hm : m ≫ Q.arrow = P.arrow ≫ f) :
    ((transportStepIso e P).inv ≫ m ≫ (transportStepIso e' Q).hom) ≫
      (transportPiece e' Q).arrow = (transportPiece e P).arrow ≫ f' := by
  rw [Category.assoc, Category.assoc, transportStepIso_arrow, ← Category.assoc m, hm]
  rw [Category.assoc, ← hf, ← Category.assoc]
  apply (cancel_epi (transportStepIso e P).hom).1
  simp [Category.assoc]
lemma transportStepMap_eq {J J' : A} (e : H ≅ H') (e' : J ≅ J')
    (P : Subobject H) (Q : Subobject J)
    (m m' : (P : A) ⟶ (Q : A)) (hm : m ≫ Q.arrow = m' ≫ Q.arrow) :
    (transportStepIso e P).inv ≫ m ≫ (transportStepIso e' Q).hom =
    (transportStepIso e P).inv ≫ m' ≫ (transportStepIso e' Q).hom := by
  rw [(cancel_mono Q.arrow).1 hm]

lemma transportGradedIso_naturality {H H' J J' : A} (e : H ≅ H') (e' : J ≅ J')
    {P₁ P₀ : Subobject H} {Q₁ Q₀ : Subobject J} (hP : P₁ ≤ P₀) (hQ : Q₁ ≤ Q₀)
    (m₁ : (P₁ : A) ⟶ (Q₁ : A)) (m₀ : (P₀ : A) ⟶ (Q₀ : A))
    (hm : Subobject.ofLE _ _ hP ≫ m₀ = m₁ ≫ Subobject.ofLE _ _ hQ)
    (t₁ : (transportPiece e P₁ : A) ⟶ (transportPiece e' Q₁ : A))
    (t₀ : (transportPiece e P₀ : A) ⟶ (transportPiece e' Q₀ : A))
    (ht : Subobject.ofLE _ _ (transportPiece_mono e hP) ≫ t₀ =
      t₁ ≫ Subobject.ofLE _ _ (transportPiece_mono e' hQ))
    (hn₀ : m₀ ≫ (transportStepIso e' Q₀).hom = (transportStepIso e P₀).hom ≫ t₀) :
    cokernel.map _ _ m₁ m₀ hm ≫ (transportGradedIso e' hQ).hom =
      (transportGradedIso e hP).hom ≫ cokernel.map _ _ t₁ t₀ ht := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE P₁ P₀ hP))).1
  simp only [cokernel.map, cokernel.π_desc_assoc, transportGradedIso_π_assoc]
  rw [Category.assoc, transportGradedIso_π, ← Category.assoc, hn₀]
  simp only [Category.assoc, cokernel.π_desc]

end TransportMaps

section DerivedComputation
universe w w'
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A]

open private TotalRightDerivedFunctor.complex_model_comparison from
  MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TotalRightDerivedFunctor

/-- A commutative square of replacements induces the model comparison square. -/
lemma replacementComparison_naturality (F : A ⥤ B) [F.Additive]
    {X I Y J : CochainComplex.Plus A} {i : X ⟶ I} {j : Y ⟶ J}
    (M : ReplacementComparison F X I i) (N : ReplacementComparison F Y J j)
    (f : X ⟶ Y) (a : I ⟶ J) (ha : i ≫ a = f ≫ j) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        N.iso.hom =
      M.iso.hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map a) := by
  letI := TotalRightDerivedFunctor.complex_model_comparison F J N.injective
  apply (cancel_mono (F.rightDerivedFunctorPlusUnit.app J)).1
  simp only [Category.assoc, N.unit_eq]
  have hn := F.rightDerivedFunctorPlusUnit.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc, M.unit_eq]
  simp only [← Functor.map_comp, ha]

/-- The augmentation of a simultaneous H-column, viewed as a map of complexes. -/
def cohomologyAugmentation {K : CochainComplex A ℤ} (R : ResolutionData K) (q : ℤ) :
    (CochainComplex.singleFunctor A 0).obj (K.homology q) ⟶ cohomologyColumn R q :=
  HomologicalComplex.mkHomFromSingle (j := 0) (homologyMap R.augmentation q) (by
    intro j hj
    have : j = 1 := by simpa using hj.symm
    subst j
    exact (R.cohomology q).augmentation_d)

lemma cohomologyColumn_strictlyGE {K : CochainComplex A ℤ} (R : ResolutionData K) (q : ℤ) :
    (cohomologyColumn R q).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact (R.cohomology q).zero_neg

lemma cohomologyColumn_injective {K : CochainComplex A ℤ} (R : ResolutionData K) (q p : ℤ) :
    Injective ((cohomologyColumn R q).X p) := by
  by_cases hp : 0 ≤ p
  · exact (R.cohomology q).injective p hp
  · exact ((R.cohomology q).zero_neg p (by omega)).injective

lemma cohomologyAugmentation_quasiIso {K : CochainComplex A ℤ}
    (R : ResolutionData K) (q : ℤ) : QuasiIso (cohomologyAugmentation R q) := by
  rw [quasiIso_iff]
  intro p
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hp : p = 0
  · subst p
    exact resolution_homology_zero_iso (R.cohomology q) _
  · exact (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 _ p hp).isIso
      (resolution_homology_zero (R.cohomology q) p hp) _

lemma cohomologyAugmentation_naturality {K L : CochainComplex A ℤ}
    (R : ResolutionData K) (S : ResolutionData L) (f : K ⟶ L)
    (a : R.bicomplex ⟶ S.bicomplex) (ha : CartanEilenbergComparison.IsLift R S f a)
    (q : ℤ) :
    cohomologyAugmentation R q ≫ cohomologyColumnMap a q =
      (CochainComplex.singleFunctor A 0).map (homologyMap f q) ≫
        cohomologyAugmentation S q := by
  apply HomologicalComplex.from_single_hom_ext
  dsimp only [HomologicalComplex.comp_f, cohomologyAugmentation]
  rw [HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change _ ≫ homologyMap R.augmentation q ≫
      homologyMap ((CartanEilenbergComparison.rowMap a).f 0) q = _
  rw [← homologyMap_comp, ha, homologyMap_comp]

def cohomologyColumnComputation (F : A ⥤ B) [F.Additive]
    {K : CochainComplex A ℤ} (R : ResolutionData K) (q : ℤ) :
    CohomologyColumnComputation F R q where
  bounded := ⟨0, cohomologyColumn_strictlyGE R q⟩
  augmentation := (CochainComplex.plus A).homMk (cohomologyAugmentation R q)
  augmentation_eq := by
    change (cohomologyAugmentation R q).f 0 = _
    simp only [cohomologyAugmentation, HomologicalComplex.mkHomFromSingle_f]
  model := CartanEilenbergTotalization.replacementComparison F _
    (cohomologyAugmentation_quasiIso R q) (cohomologyColumn_injective R q)

def cohomologyComputationIso (F : A ⥤ B) [F.Additive]
    {K : CochainComplex A ℤ} (R : ResolutionData K) (p q : ℤ) :
    (rightValueInt F p).obj (K.homology q) ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj (cohomologyColumn R q)).homology p :=
  (cohomologyColumnComputation F R q).homologyIso F R p

lemma cohomologyComputationIso_naturality (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex A ℤ} (R : ResolutionData K) (S : ResolutionData L)
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f a) (p q : ℤ) :
    (rightValueInt F p).map (homologyMap f q) ≫
        (cohomologyComputationIso F S p q).hom =
      (cohomologyComputationIso F R p q).hom ≫
        homologyMap ((F.mapHomologicalComplex (.up ℤ)).map
          (cohomologyColumnMap a q)) p := by
  let f' : cohomologyStalk (K.homology q) ⟶ cohomologyStalk (L.homology q) :=
    (CochainComplex.plus A).homMk
      ((CochainComplex.singleFunctor A 0).map (homologyMap f q))
  let a' : (⟨cohomologyColumn R q, (cohomologyColumnComputation F R q).bounded⟩ :
        CochainComplex.Plus A) ⟶
      (⟨cohomologyColumn S q, (cohomologyColumnComputation F S q).bounded⟩ :
        CochainComplex.Plus A) :=
    (CochainComplex.plus A).homMk (cohomologyColumnMap a q)
  have hn := replacementComparison_naturality F
    (cohomologyColumnComputation F R q).model (cohomologyColumnComputation F S q).model f' a'
    (ObjectProperty.hom_ext _ (cohomologyAugmentation_naturality R S f a ha q))
  have hh := congrArg ((DerivedCategory.Plus.homologyFunctor B p).map) hn
  simp only [Functor.map_comp] at hh
  dsimp only [cohomologyComputationIso, CohomologyColumnComputation.homologyIso,
    ReplacementComparison.homologyIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc]
  erw [hh]
  simp only [Category.assoc]
  exact congrArg (fun z => _ ≫ z)
    ((DerivedCategory.homologyFunctorFactors B p).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map (cohomologyColumnMap a q)))

section SecondPage
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  {K : CochainComplex A ℤ} (R : ResolutionData K)
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
  (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
  (D : F03Specs.PageData Fr)

abbrev actualRowData := (DoubleComplexFirstPages.system B).row _
  (map_finite F R.bicomplex (resolution_finite R)) Fr hFr D

/-- The actual E₂ quotient computes the canonical integer-indexed RᵖF(HᑫK). -/
def computedRowSecondIso (p q : ℤ) : DoubleComplexFirstPages.page Fr D 2 p q ≅
    (rightValueInt F p).obj (K.homology q) :=
  rowSecondIso F R Fr hFr D (actualRowData F R Fr hFr D) p q ≪≫
    (cohomologyComputationIso F R p q).symm

/-- The normalized E₂ computation on the actual simultaneous cohomology column. -/
def secondPageComputation (N : PageCohomology.Data Fr D) :
    SecondPageComputation F R Fr hFr D N where
  first := firstPageComputation F R Fr hFr D (actualRowData F R Fr hFr D)
  column := cohomologyColumnComputation F R

lemma computedRowSecondIso_eq (N : PageCohomology.Data Fr D) (p q : ℤ) :
    computedRowSecondIso F R Fr hFr D p q =
      (secondPageComputation F R Fr hFr D N).iso F R Fr hFr D p q := by
  unfold computedRowSecondIso SecondPageComputation.iso
  rw [rowSecondIso_eq F R Fr hFr D (actualRowData F R Fr hFr D) N p q]
  rfl

include hFr in
lemma rowSecond_negative (p q : ℤ) (hp : p < 0) :
    IsZero (DoubleComplexFirstPages.page Fr D 2 p q) := by
  apply (rowSecondIso F R Fr hFr D (actualRowData F R Fr hFr D) p q).isZero_iff.mpr
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero ((R.cohomology q).zero_neg p hp))

end SecondPage

section SecondNaturality
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  {K L : CochainComplex A ℤ} (R : ResolutionData K) (S : ResolutionData L)
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
  (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
  (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
  (hGr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj S.bicomplex) Prod.snd Gr)
  (D : F03Specs.PageData Fr) (E : F03Specs.PageData Gr)
  (a : R.bicomplex ⟶ S.bicomplex)
  (g : FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex), Fr⟩
    ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex), Gr⟩)
  (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ))
  (M : FilteredPageFunctoriality.MapData g D E)

include hg hFr hGr

lemma rowSecondIso_naturality (p q : ℤ) :
    M.map 2 p (p+q) ≫
        (rowSecondIso F S Gr hGr E (actualRowData F S Gr hGr E) p q).hom =
      (rowSecondIso F R Fr hFr D (actualRowData F R Fr hFr D) p q).hom ≫
        homologyMap ((F.mapHomologicalComplex (.up ℤ)).map (cohomologyColumnMap a q)) p := by
  have hn := ((DoubleComplexFirstPages.system B).row_naturality _ _
    (map_finite F R.bicomplex (resolution_finite R))
    (map_finite F S.bicomplex (resolution_finite S)) Fr Gr hFr hGr D E
    ((mapDouble F).map a) g hg M p q).2.2
  dsimp only [rowSecondIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hn, Category.assoc]
  have hv : DoubleComplexFirstPages.verticalHomologyMap
      ((mapDouble F).obj R.bicomplex).flip
      (CartanEilenbergComparison.rowMap ((mapDouble F).map a)) q =
        cohomologyColumnMap ((mapDouble F).map a) q := rfl
  rw [hv]
  have hh := congrArg (fun z => homologyMap z p) (rowInvariantIso_naturality F R S a q)
  rw [homologyMap_comp, homologyMap_comp] at hh
  simpa only [Category.assoc, HomologicalComplex.homologyFunctor_map, actualRowData] using
    congrArg (fun z => ((actualRowData F R Fr hFr D).secondIso p q).hom ≫ z) hh

lemma computedRowSecondIso_naturality (f : K ⟶ L)
    (ha : CartanEilenbergComparison.IsLift R S f a) (p q : ℤ) :
    M.map 2 p (p+q) ≫ (computedRowSecondIso F S Gr hGr E p q).hom =
      (computedRowSecondIso F R Fr hFr D p q).hom ≫
        (rightValueInt F p).map (homologyMap f q) := by
  dsimp only [computedRowSecondIso, Iso.trans_hom, Iso.symm_hom]
  apply (cancel_mono (cohomologyComputationIso F S p q).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, comp_id]
  rw [cohomologyComputationIso_naturality F R S f a ha,
    Iso.inv_hom_id_assoc, rowSecondIso_naturality F R S Fr Gr hFr hGr D E a g hg M]

lemma rowPage_isIso_of_quasiIso (f : K ⟶ L) (hf : QuasiIso f)
    (ha : CartanEilenbergComparison.IsLift R S f a) (r : ℤ) (hr : 2 ≤ r) :
    ∀ p n, IsIso (M.map r p n) := by
  apply FilteredPageFunctoriality.comparison M 2 (by omega) _ r hr
  intro p n
  let q := n-p
  letI := hf
  letI : IsIso (homologyMap f q) := (quasiIsoAt_iff_isIso_homologyMap f q).1 inferInstance
  have hn := computedRowSecondIso_naturality F R S Fr Gr hFr hGr D E a g hg M f ha p q
  have heq : M.map 2 p (p+q) = (computedRowSecondIso F R Fr hFr D p q).hom ≫
      (rightValueInt F p).map (homologyMap f q) ≫
        (computedRowSecondIso F S Gr hGr E p q).inv := by
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, comp_id]
  have h : IsIso (M.map 2 p (p+q)) := by rw [heq]; infer_instance
  dsimp only [q] at h
  rw [show p+(n-p)=n by omega] at h
  exact h

end SecondNaturality

lemma rowPage_lift_independent (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {K L : CochainComplex A ℤ} (R : ResolutionData K) (S : ResolutionData L)
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
    (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
    (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
    (hGr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj S.bicomplex) Prod.snd Gr)
    (D : F03Specs.PageData Fr) (E : F03Specs.PageData Gr)
    (f : K ⟶ L) (a b : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f a)
    (hb : CartanEilenbergComparison.IsLift R S f b)
    (g h : FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex), Fr⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex), Gr⟩)
    (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ))
    (hh : h.hom = HomologicalComplex₂.total.map ((mapDouble F).map b) (.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E)
    (N : FilteredPageFunctoriality.MapData h D E) (r : ℤ) (hr : 2 ≤ r) :
    ∀ p n, M.map r p n = N.map r p n := by
  apply pageMaps_eq_of_eq M N 2 (by omega) _ r hr
  intro p n
  have hm := computedRowSecondIso_naturality F R S Fr Gr hFr hGr D E a g hg M f ha p (n-p)
  have hn := computedRowSecondIso_naturality F R S Fr Gr hFr hGr D E b h hh N f hb p (n-p)
  have heq := (cancel_mono (computedRowSecondIso F S Gr hGr E p (n-p)).hom).1
    (hm.trans hn.symm)
  have transport : ∀ t t' : ℤ, t = t' →
      M.map 2 p t = N.map 2 p t → M.map 2 p t' = N.map 2 p t' := by
    intro t t' ht
    subst t'
    exact id
  exact transport _ _ (by omega) heq

theorem computedRows : Specs.ComputedRows.{v,u,v',u',w,w'} := by
  intro A _ _ B _ _ _ _ _ F _ _
  refine ⟨{
    secondIso := ?_
    canonical := ?_
    negative := ?_
    naturality := ?_
    lift_independent := ?_
    quasiIso_comparison := ?_ }⟩
  · intro K R _ Fr hFr D p q
    exact computedRowSecondIso F R Fr hFr D p q
  · intro K R _ Fr hFr D N
    exact ⟨secondPageComputation F R Fr hFr D N, computedRowSecondIso_eq F R Fr hFr D N⟩
  · intro K R _ Fr hFr D p q hp
    exact rowSecond_negative F R Fr hFr D p q hp
  · intro K L R S _ _ Fr Gr hFr hGr D E f a ha g hg M p q
    exact computedRowSecondIso_naturality F R S Fr Gr hFr hGr D E a g hg M f ha p q
  · intro K L R S _ _ Fr Gr hFr hGr D E f a b ha hb g h hg hh M N r hr p n
    exact rowPage_lift_independent F R S Fr Gr hFr hGr D E f a b ha hb
      g h hg hh M N r hr p n
  · intro K L R S _ _ Fr Gr hFr hGr D E f hf a ha g hg M r hr p n
    exact rowPage_isIso_of_quasiIso F R S Fr Gr hFr hGr D E a g hg M f hf ha r hr p n

section RowPageFunctoriality
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  {K L T : CochainComplex A ℤ}
  (R : ResolutionData K) (S : ResolutionData L) (U : ResolutionData T)
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
  [((mapDouble F).obj U.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
  (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
  (Hr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj U.bicomplex)))
  (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
  (hGr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj S.bicomplex) Prod.snd Gr)
  (hHr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj U.bicomplex) Prod.snd Hr)
  (D : F03Specs.PageData Fr) (E : F03Specs.PageData Gr) (G : F03Specs.PageData Hr)

/-- The total map of a double-complex comparison, restricted to the actual
row filtration. Uniqueness of filtered maps makes the existence choice immaterial. -/
def rowFilteredMap (a : R.bicomplex ⟶ S.bicomplex) :
    FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex), Fr⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex), Gr⟩ :=
  Classical.choose (FiniteDiagonalFiltrations.formula_filteredMap _ _ Prod.snd
    Fr Gr hFr hGr ((mapDouble F).map a))

lemma rowFilteredMap_hom (a : R.bicomplex ⟶ S.bicomplex) :
    (rowFilteredMap F R S Fr Gr hFr hGr a).hom =
      HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ) :=
  Classical.choose_spec (FiniteDiagonalFiltrations.formula_filteredMap _ _ Prod.snd
    Fr Gr hFr hGr ((mapDouble F).map a))

lemma rowFilteredMap_id :
    rowFilteredMap F R R Fr Fr hFr hFr (𝟙 R.bicomplex) =
      FilteredMap.id ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex), Fr⟩ := by
  apply FilteredMap.ext
  rw [rowFilteredMap_hom]
  change HomologicalComplex₂.total.map ((mapDouble F).map (𝟙 R.bicomplex)) (.up ℤ) = 𝟙 _
  erw [(mapDouble F).map_id, HomologicalComplex₂.total.map_id]

lemma rowFilteredMap_comp (a : R.bicomplex ⟶ S.bicomplex)
    (b : S.bicomplex ⟶ U.bicomplex) :
    rowFilteredMap F R U Fr Hr hFr hHr (a ≫ b) =
      (rowFilteredMap F R S Fr Gr hFr hGr a).comp
        (rowFilteredMap F S U Gr Hr hGr hHr b) := by
  apply FilteredMap.ext
  change _ = (rowFilteredMap F R S Fr Gr hFr hGr a).hom ≫
    (rowFilteredMap F S U Gr Hr hGr hHr b).hom
  simp only [rowFilteredMap_hom, Functor.map_comp, HomologicalComplex₂.total.map_comp]

/-- The induced morphism of actual row page quotients, including all their
canonical representative and differential formulas. -/
abbrev rowLiftPageData (a : R.bicomplex ⟶ S.bicomplex) :=
  FilteredPageFunctoriality.mapData (rowFilteredMap F R S Fr Gr hFr hGr a) D E

abbrev rowLiftPageMap (a : R.bicomplex ⟶ S.bicomplex) (r p n : ℤ) :=
  (rowLiftPageData F R S Fr Gr hFr hGr D E a).map r p n

lemma rowLiftPageMap_id (r p n : ℤ) :
    rowLiftPageMap F R R Fr Fr hFr hFr D D (𝟙 R.bicomplex) r p n = 𝟙 _ := by
  change FilteredPageFunctoriality.pageMap _ _ _ _ _ _ = _
  rw [rowFilteredMap_id]
  exact FilteredPageFunctoriality.pageMap_id _ _ _ _ _

lemma rowLiftPageMap_comp (a : R.bicomplex ⟶ S.bicomplex)
    (b : S.bicomplex ⟶ U.bicomplex) (r p n : ℤ) :
    rowLiftPageMap F R U Fr Hr hFr hHr D G (a ≫ b) r p n =
      rowLiftPageMap F R S Fr Gr hFr hGr D E a r p n ≫
        rowLiftPageMap F S U Gr Hr hGr hHr E G b r p n := by
  change FilteredPageFunctoriality.pageMap _ _ _ _ _ _ = _
  rw [rowFilteredMap_comp F R S U Fr Gr Hr hFr hGr hHr]
  exact FilteredPageFunctoriality.pageMap_comp _ _ _ _ _ _ _ _

lemma rowLiftPageMap_independent (f : K ⟶ L) (a b : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f a)
    (hb : CartanEilenbergComparison.IsLift R S f b) (r : ℤ) (hr : 2 ≤ r)
    (p n : ℤ) :
    rowLiftPageMap F R S Fr Gr hFr hGr D E a r p n =
      rowLiftPageMap F R S Fr Gr hFr hGr D E b r p n :=
  rowPage_lift_independent F R S Fr Gr hFr hGr D E f a b ha hb
    _ _ (rowFilteredMap_hom F R S Fr Gr hFr hGr a)
    (rowFilteredMap_hom F R S Fr Gr hFr hGr b) _ _ r hr p n

/-- A chain map acts on every row page by any comparison lift. From E₂
onward this map is independent of the comparison chosen here. -/
abbrev rowChainPageData (f : K ⟶ L) :=
  rowLiftPageData F R S Fr Gr hFr hGr D E
    (CartanEilenbergComparison.comparison R S f)

abbrev rowChainPageMap (f : K ⟶ L) (r p n : ℤ) :=
  (rowChainPageData F R S Fr Gr hFr hGr D E f).map r p n

lemma rowChainPageMap_eq (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f a) (r : ℤ) (hr : 2 ≤ r)
    (p n : ℤ) :
    rowChainPageMap F R S Fr Gr hFr hGr D E f r p n =
      rowLiftPageMap F R S Fr Gr hFr hGr D E a r p n :=
  rowLiftPageMap_independent F R S Fr Gr hFr hGr D E f _ a
    (CartanEilenbergComparison.comparison_augmentation R S f) ha r hr p n

lemma rowChainPageMap_id (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    rowChainPageMap F R R Fr Fr hFr hFr D D (𝟙 K) r p n = 𝟙 _ := by
  rw [rowChainPageMap_eq F R R Fr Fr hFr hFr D D (𝟙 K) (𝟙 R.bicomplex)
    (CartanEilenbergComparison.isLift_id R) r hr]
  exact rowLiftPageMap_id F R Fr hFr D r p n

lemma rowChainPageMap_comp (f : K ⟶ L) (g : L ⟶ T)
    (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    rowChainPageMap F R U Fr Hr hFr hHr D G (f ≫ g) r p n =
      rowChainPageMap F R S Fr Gr hFr hGr D E f r p n ≫
        rowChainPageMap F S U Gr Hr hGr hHr E G g r p n := by
  rw [rowChainPageMap_eq F R U Fr Hr hFr hHr D G (f ≫ g)
    (CartanEilenbergComparison.comparison R S f ≫
      CartanEilenbergComparison.comparison S U g)
    (CartanEilenbergComparison.isLift_comp R S U
      (CartanEilenbergComparison.comparison_augmentation R S f)
      (CartanEilenbergComparison.comparison_augmentation S U g)) r hr]
  exact rowLiftPageMap_comp F R S U Fr Gr Hr hFr hGr hHr D E G _ _ r p n

/-- Quasi-isomorphisms induce isomorphisms from E₂ onward. -/
lemma rowChainPageMap_isIso (f : K ⟶ L) (hf : QuasiIso f)
    (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    IsIso (rowChainPageMap F R S Fr Gr hFr hGr D E f r p n) :=
  rowPage_isIso_of_quasiIso F R S Fr Gr hFr hGr D E _ _
    (rowFilteredMap_hom F R S Fr Gr hFr hGr _)
    (rowChainPageData F R S Fr Gr hFr hGr D E f) f hf
    (CartanEilenbergComparison.comparison_augmentation R S f) r hr p n

/-- Equality on the horizontal cohomology maps determines the induced maps on
all row pages from E₂ onward. In particular homotopic chain maps act equally. -/
lemma rowChainPageMap_eq_of_homology (f g : K ⟶ L)
    (hfg : ∀ q, homologyMap f q = homologyMap g q)
    (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    rowChainPageMap F R S Fr Gr hFr hGr D E f r p n =
      rowChainPageMap F R S Fr Gr hFr hGr D E g r p n := by
  apply pageMaps_eq_of_eq
    (rowChainPageData F R S Fr Gr hFr hGr D E f)
    (rowChainPageData F R S Fr Gr hFr hGr D E g) 2 (by omega) _ r hr p n
  intro a b
  have hf := computedRowSecondIso_naturality F R S Fr Gr hFr hGr D E
    (CartanEilenbergComparison.comparison R S f) _
    (rowFilteredMap_hom F R S Fr Gr hFr hGr _)
    (rowChainPageData F R S Fr Gr hFr hGr D E f) f
    (CartanEilenbergComparison.comparison_augmentation R S f) a (b-a)
  have hg := computedRowSecondIso_naturality F R S Fr Gr hFr hGr D E
    (CartanEilenbergComparison.comparison R S g) _
    (rowFilteredMap_hom F R S Fr Gr hFr hGr _)
    (rowChainPageData F R S Fr Gr hFr hGr D E g) g
    (CartanEilenbergComparison.comparison_augmentation R S g) a (b-a)
  rw [hfg] at hf
  have hh := (cancel_mono (computedRowSecondIso F S Gr hGr E a (b-a)).hom).1
    (hf.trans hg.symm)
  have transport : ∀ t t' : ℤ, t = t' →
      (rowChainPageData F R S Fr Gr hFr hGr D E f).map 2 a t =
        (rowChainPageData F R S Fr Gr hFr hGr D E g).map 2 a t →
      (rowChainPageData F R S Fr Gr hFr hGr D E f).map 2 a t' =
        (rowChainPageData F R S Fr Gr hFr hGr D E g).map 2 a t' := by
    intro t t' ht
    subst t'
    exact id
  exact transport _ _ (by omega) hh

lemma rowChainPageMap_homotopy {f g : K ⟶ L} (h : Homotopy f g)
    (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    rowChainPageMap F R S Fr Gr hFr hGr D E f r p n =
      rowChainPageMap F R S Fr Gr hFr hGr D E g r p n :=
  rowChainPageMap_eq_of_homology F R S Fr Gr hFr hGr D E f g (fun q => h.homologyMap_eq q) r hr p n

end RowPageFunctoriality

section ResolutionIndependence
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  {K : CochainComplex A ℤ} (R S : ResolutionData K)
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
  (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
  (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
  (hGr : FiniteDiagonalFiltrations.HasFiltrationFormula
    ((mapDouble F).obj S.bicomplex) Prod.snd Gr)
  (D : F03Specs.PageData Fr) (E : F03Specs.PageData Gr)

/-- The identity comparison between any two resolutions is an isomorphism
of actual row pages. Its inverse is the comparison in the opposite direction. -/
def rowResolutionPageIso (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    PageCohomology.object Fr D r p n ≅ PageCohomology.object Gr E r p n where
  hom := rowChainPageMap F R S Fr Gr hFr hGr D E (𝟙 K) r p n
  inv := rowChainPageMap F S R Gr Fr hGr hFr E D (𝟙 K) r p n
  hom_inv_id := by
    rw [← rowChainPageMap_comp F R S R Fr Gr Fr hFr hGr hFr D E D (𝟙 K) (𝟙 K) r hr p n]
    simp only [Category.id_comp]
    exact rowChainPageMap_id F R Fr hFr D r hr p n
  inv_hom_id := by
    rw [← rowChainPageMap_comp F S R S Gr Fr Gr hGr hFr hGr E D E (𝟙 K) (𝟙 K) r hr p n]
    simp only [Category.id_comp]
    exact rowChainPageMap_id F S Gr hGr E r hr p n

end ResolutionIndependence

theorem rowRealizationsExist : Specs.RowRealizationsExist.{v,u,v',u',w,w'} := by
  intro A _ _ B _ _ _ _ _ F _ _ K hK
  obtain ⟨R⟩ := CartanEilenbergExistence.existsResolution K hK
  letI : R.bicomplex.HasTotal (.up ℤ) := (CartanEilenbergTotalization.finiteSupport R).2
  have hFR := CartanEilenbergTotalization.additiveSupport F R
  letI : ((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ) := hFR.2
  obtain ⟨Fc, Fr, hFc, hFr, hfinitec, hfiniter⟩ :=
    FiniteDiagonalFiltrations.filtrations ((mapDouble F).obj R.bicomplex) hFR.1
  let D := FilteredPage.pageData Fr
  let N := PageCohomology.data Fr D
  exact ⟨{
    resolution := R
    hasTotal := inferInstance
    hasMappedTotal := inferInstance
    filtration := Fr
    formula := hFr
    pages := D
    pageCohomology := N
    convergence := DoubleComplexConvergence.converges_of_finite Fr
      (DoubleComplexConvergence.formula_finite ((mapDouble F).obj R.bicomplex)
        hFR.1 Prod.snd (Or.inr rfl) Fr hFr)
    secondComparison := secondPageComputation F R Fr hFr D N
    secondIso := computedRowSecondIso F R Fr hFr D
    secondIso_eq := computedRowSecondIso_eq F R Fr hFr D N }⟩

/-- Actual row page maps, simultaneous in all complexes, resolutions and pages. -/
def rowPageFunctorialSystem (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] :
    RowPageFunctorialSystem F where
  map R S f := rowChainPageMap F R.resolution S.resolution
    R.filtration S.filtration R.formula S.formula R.pages S.pages f
  induced R S f a ha := ⟨rowFilteredMap F R.resolution S.resolution
    R.filtration S.filtration R.formula S.formula a,
    rowFilteredMap_hom F R.resolution S.resolution R.filtration S.filtration R.formula S.formula a,
    rowLiftPageData F R.resolution S.resolution R.filtration S.filtration
      R.formula S.formula R.pages S.pages a,
    rowChainPageMap_eq F R.resolution S.resolution R.filtration S.filtration
      R.formula S.formula R.pages S.pages f a ha⟩
  map_id R := rowChainPageMap_id F R.resolution R.filtration R.formula R.pages
  map_comp R S U := rowChainPageMap_comp F R.resolution S.resolution U.resolution
    R.filtration S.filtration U.filtration R.formula S.formula U.formula R.pages S.pages U.pages
  differential_comm R S f r hr p n :=
    (rowChainPageData F R.resolution S.resolution R.filtration S.filtration
      R.formula S.formula R.pages S.pages f).differential_comm r (by omega) p n
  second_naturality := by
    intro C K L R S f p q
    exact C.naturality R.resolution S.resolution
      R.filtration S.filtration R.formula S.formula R.pages S.pages f
      (CartanEilenbergComparison.comparison R.resolution S.resolution f)
      (CartanEilenbergComparison.comparison_augmentation R.resolution S.resolution f)
      _ (rowFilteredMap_hom F R.resolution S.resolution R.filtration S.filtration
        R.formula S.formula _) _ p q
  resolution_naturality R R' S S' f r hr p n := by
    rw [← rowChainPageMap_comp F R.resolution R'.resolution S'.resolution
      R.filtration R'.filtration S'.filtration R.formula R'.formula S'.formula
      R.pages R'.pages S'.pages (𝟙 _) f r hr p n,
      ← rowChainPageMap_comp F R.resolution S.resolution S'.resolution
      R.filtration S.filtration S'.filtration R.formula S.formula S'.formula
      R.pages S.pages S'.pages f (𝟙 _) r hr p n]
    simp only [Category.id_comp, Category.comp_id]
  homotopy_invariant R S f g h := rowChainPageMap_homotopy F R.resolution S.resolution
    R.filtration S.filtration R.formula S.formula R.pages S.pages h
  inverts_quasiIso R S f hf := rowChainPageMap_isIso F R.resolution S.resolution
    R.filtration S.filtration R.formula S.formula R.pages S.pages f hf
  inverse_comparisons R S r hr p n := ⟨rowResolutionPageIso F R.resolution S.resolution
    R.filtration S.filtration R.formula S.formula R.pages S.pages r hr p n, rfl, rfl⟩

theorem pageFunctoriality : Specs.PageFunctoriality.{v,u,v',u',w,w'} := by
  intro A _ _ B _ _ _ _ _ F _ _
  exact ⟨rowPageFunctorialSystem F⟩

/-- The common derived-cohomology comparison from the given augmented total
model and the canonical additive comparison on the diagonal summands. -/
def totalComputationIso (F : A ⥤ B) [F.Additive]
    (X : CochainComplex.Plus A) (R : ResolutionData X.obj)
    [R.bicomplex.HasTotal (.up ℤ)]
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)] (n : ℤ) :
    derivedCohomology F X n ≅
      (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)).homology n :=
  (derivedTotalComparison F X R).homologyIso n

lemma totalComputationIso_naturality (F : A ⥤ B) [F.Additive]
    (X Y : CochainComplex.Plus A) (R : ResolutionData X.obj) (S : ResolutionData Y.obj)
    [R.bicomplex.HasTotal (.up ℤ)] [S.bicomplex.HasTotal (.up ℤ)]
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
    (f : X ⟶ Y) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a) (n : ℤ) :
    derivedCohomologyMap F f n ≫ (totalComputationIso F Y S n).hom =
      (totalComputationIso F X R n).hom ≫
        homologyMap (HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)) n := by
  let M := derivedTotalComparison F X R
  let N := derivedTotalComparison F Y S
  let I : CochainComplex.Plus A := ⟨DoubleTotalization.sumTotal R.bicomplex, M.totalBound⟩
  let J : CochainComplex.Plus A := ⟨DoubleTotalization.sumTotal S.bicomplex, N.totalBound⟩
  let a' : I ⟶ J :=
    (CochainComplex.plus A).homMk (HomologicalComplex₂.total.map a (.up ℤ))
  have haug := augmentationComparison R S f.hom a ha
    M.augmentation.hom N.augmentation.hom M.augmentation_eq N.augmentation_eq
  have hn := replacementComparison_naturality F M.model N.model f a'
    (by ext n; exact congrArg (fun z => z.f n) haug)
  have hh := congrArg ((DerivedCategory.Plus.homologyFunctor B n).map) hn
  simp only [Functor.map_comp] at hh
  change derivedCohomologyMap F f n ≫ (N.homologyIso n).hom =
    (M.homologyIso n).hom ≫
      homologyMap (HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)) n
  dsimp only [derivedCohomologyMap, DerivedTotalComparison.homologyIso,
    ReplacementComparison.homologyIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [← Category.assoc]
  erw [hh]
  simp only [Category.assoc]
  have hfac :=
    (DerivedCategory.homologyFunctorFactors B n).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex₂.total.map a (.up ℤ)))
  have hfac' :
      (DerivedCategory.Plus.homologyFunctor B n).map
          (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map a')) ≫
        ((DerivedCategory.homologyFunctorFactors B n).app
          ((F.mapCochainComplexPlus.obj J).obj)).hom =
      ((DerivedCategory.homologyFunctorFactors B n).app ((F.mapCochainComplexPlus.obj I).obj)).hom ≫
        homologyMap ((F.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex₂.total.map a (.up ℤ))) n := hfac
  erw [← Category.assoc
    ((DerivedCategory.Plus.homologyFunctor B n).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map a')))
    (((DerivedCategory.homologyFunctorFactors B n).app _).hom)
    ((homologyFunctor B (.up ℤ) n).map N.additivity.hom)]
  erw [hfac']
  have htot := additiveNaturality F R S M.additivity N.additivity M.summands N.summands a
  have hhom := congrArg (fun z => homologyMap z n) htot
  simp only [homologyMap_comp] at hhom
  simp only [Category.assoc, homologyFunctor_map]
  rw [hhom]

lemma totalCohomology_lift_independent (F : A ⥤ B) [F.Additive]
    (X Y : CochainComplex.Plus A) (R : ResolutionData X.obj) (S : ResolutionData Y.obj)
    [R.bicomplex.HasTotal (.up ℤ)] [S.bicomplex.HasTotal (.up ℤ)]
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
    (f : X ⟶ Y) (a b : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a)
    (hb : CartanEilenbergComparison.IsLift R S f.hom b) (n : ℤ) :
    homologyMap (HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)) n =
      homologyMap (HomologicalComplex₂.total.map ((mapDouble F).map b) (.up ℤ)) n := by
  apply (cancel_epi (totalComputationIso F X R n).hom).1
  exact (totalComputationIso_naturality F X Y R S f a ha n).symm.trans
    (totalComputationIso_naturality F X Y R S f b hb n)

lemma cohomologyStepMap_eq_of_homologyMap_eq
    {X Y : FilteredComplex B} (f g : FilteredMap X Y) (n : ℤ)
    (h : homologyMap f.hom n = homologyMap g.hom n) (p : ℤ) :
    FiniteFiltrationConvergence.cohomologyStepMap f p n =
      FiniteFiltrationConvergence.cohomologyStepMap g p n := by
  apply (cancel_mono (FiniteFiltrationConvergence.cohomologyPiece Y.filtration p n).arrow).1
  simp only [FiniteFiltrationConvergence.cohomologyStepMap_arrow, h]

lemma rowConverges (F : A ⥤ B) [F.Additive]
    {K : CochainComplex A ℤ} (R : ResolutionData K)
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr) :
    DoubleComplexConvergence.Converges Fr :=
  DoubleComplexConvergence.converges_of_finite Fr
    (DoubleComplexConvergence.formula_finite _
      (map_finite F R.bicomplex (resolution_finite R)) _ (Or.inr rfl) Fr hFr)


section DerivedFiltration
open FiniteFiltrationConvergence
variable (F : A ⥤ B) [F.Additive]
  (X : CochainComplex.Plus A) (R : ResolutionData X.obj)
  [R.bicomplex.HasTotal (.up ℤ)]
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))

def derivedRowPiece (p n : ℤ) : Subobject
    ((DerivedCategory.Plus.homologyFunctor B n).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj X))) :=
  transportPiece (totalComputationIso F X R n).symm (cohomologyPiece Fr p n)

lemma derivedRowPiece_decreasing (p n : ℤ) :
    derivedRowPiece F X R Fr (p+1) n ≤ derivedRowPiece F X R Fr p n :=
  transportPiece_mono _ (cohomologyPiece_decreasing Fr p n)

lemma derivedRowPiece_finite
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr) (n : ℤ) :
    ∃ a b : ℤ,
      (∀ p, p ≤ a → derivedRowPiece F X R Fr p n = ⊤) ∧
      (∀ p, b ≤ p → derivedRowPiece F X R Fr p n = ⊥) := by
  obtain ⟨a,b,ha,hb⟩ := (rowConverges F R Fr hFr).target.finite n
  exact ⟨a,b,fun p hp => by simp [derivedRowPiece, ha p hp],
    fun p hp => by simp [derivedRowPiece, hb p hp]⟩

abbrev derivedRowGraded (p n : ℤ) : B :=
  cokernel (Subobject.ofLE _ _ (derivedRowPiece_decreasing F X R Fr p n))

/-- The actual stable-page limit, transported to the graded filtration on H(RF X). -/
def derivedRowLimitIso (D : F03Specs.PageData Fr) (r p n : ℤ)
    (h : Stabilized Fr r p n) : PageCohomology.object Fr D r p n ≅
      derivedRowGraded F X R Fr p n :=
  (limitIso Fr D r p n h).iso ≪≫
    transportGradedIso (totalComputationIso F X R n).symm
      (cohomologyPiece_decreasing Fr p n)

lemma derivedRowLimitIso_representative (D : F03Specs.PageData Fr) (r p n : ℤ)
    (h : Stabilized Fr r p n) :
    closedToPage Fr D r p n ≫ (derivedRowLimitIso F X R Fr D r p n h).hom =
      closedClass Fr p n ≫
        (transportStepIso (totalComputationIso F X R n).symm
          (cohomologyPiece Fr p n)).hom ≫
            cokernel.π (Subobject.ofLE _ _ (derivedRowPiece_decreasing F X R Fr p n)) := by
  dsimp only [derivedRowLimitIso, Iso.trans_hom]
  rw [← Category.assoc, (limitIso Fr D r p n h).representative_formula]
  dsimp only [gradedClass]
  rw [Category.assoc, transportGradedIso_π]
  rfl

end DerivedFiltration

section DerivedTargetMaps
open FiniteFiltrationConvergence
variable (F : A ⥤ B) [F.Additive]
  (X Y : CochainComplex.Plus A) (R : ResolutionData X.obj) (S : ResolutionData Y.obj)
  [R.bicomplex.HasTotal (.up ℤ)] [S.bicomplex.HasTotal (.up ℤ)]
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
  (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))

lemma totalComputationIso_inv_naturality (f : X ⟶ Y) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a) (n : ℤ) :
    homologyMap (HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)) n ≫
        (totalComputationIso F Y S n).inv =
      (totalComputationIso F X R n).inv ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) := by
  apply (cancel_epi (totalComputationIso F X R n).hom).1
  rw [← Category.assoc, ← totalComputationIso_naturality F X Y R S f a ha n]
  simp only [Category.assoc, Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

def derivedRowStepMap
    (g : FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex),Fr⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex),Gr⟩) (p n : ℤ) :
    (derivedRowPiece F X R Fr p n : B) ⟶ (derivedRowPiece F Y S Gr p n : B) :=
  (transportStepIso (totalComputationIso F X R n).symm (cohomologyPiece Fr p n)).inv ≫
    cohomologyStepMap g p n ≫
      (transportStepIso (totalComputationIso F Y S n).symm (cohomologyPiece Gr p n)).hom

lemma derivedRowStepMap_arrow
    (f : X ⟶ Y) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a)
    (g : FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex),Fr⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex),Gr⟩)
    (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)) (p n : ℤ) :
    derivedRowStepMap F X Y R S Fr Gr g p n ≫ (derivedRowPiece F Y S Gr p n).arrow =
      (derivedRowPiece F X R Fr p n).arrow ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) := by
  dsimp only [derivedRowStepMap, derivedRowPiece]
  exact transportStepMap_arrow _ _ _ _ (homologyMap g.hom n)
    ((DerivedCategory.Plus.homologyFunctor B n).map
      (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)))
    (by rw [hg]; exact (totalComputationIso_inv_naturality F X Y R S f a ha n).symm)
    (cohomologyStepMap g p n) (cohomologyStepMap_arrow g p n)

lemma derivedRowStepMap_independent
    (f : X ⟶ Y) (a b : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a)
    (hb : CartanEilenbergComparison.IsLift R S f.hom b)
    (g h : FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex),Fr⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex),Gr⟩)
    (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ))
    (hh : h.hom = HomologicalComplex₂.total.map ((mapDouble F).map b) (.up ℤ)) (p n : ℤ) :
    derivedRowStepMap F X Y R S Fr Gr g p n = derivedRowStepMap F X Y R S Fr Gr h p n := by
  apply (cancel_mono (derivedRowPiece F Y S Gr p n).arrow).1
  rw [derivedRowStepMap_arrow F X Y R S Fr Gr f a ha g hg,
    derivedRowStepMap_arrow F X Y R S Fr Gr f b hb h hh]

end DerivedTargetMaps


lemma derivedRowPiece_resolution_independent (F : A ⥤ B) [F.Additive]
    (X : CochainComplex.Plus A) (R S : ResolutionData X.obj)
    [R.bicomplex.HasTotal (.up ℤ)] [S.bicomplex.HasTotal (.up ℤ)]
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
    (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
    (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
    (hGr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj S.bicomplex) Prod.snd Gr) (p n : ℤ) :
    derivedRowPiece F X R Fr p n = derivedRowPiece F X S Gr p n := by
  have hle (R S : ResolutionData X.obj)
      [R.bicomplex.HasTotal (.up ℤ)] [S.bicomplex.HasTotal (.up ℤ)]
      [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
      [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
      (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
      (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
      (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
        ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
      (hGr : FiniteDiagonalFiltrations.HasFiltrationFormula
        ((mapDouble F).obj S.bicomplex) Prod.snd Gr) :
      derivedRowPiece F X R Fr p n ≤ derivedRowPiece F X S Gr p n := by
    obtain ⟨a,ha⟩ := CartanEilenbergComparison.liftExists R S (𝟙 X.obj)
    obtain ⟨g,hg⟩ := FiniteDiagonalFiltrations.formula_filteredMap _ _ Prod.snd
      Fr Gr hFr hGr ((mapDouble F).map a)
    exact Subobject.le_of_comm (derivedRowStepMap F X X R S Fr Gr g p n)
      (by simpa using derivedRowStepMap_arrow F X X R S Fr Gr (𝟙 X) a ha g hg p n)
  exact le_antisymm (hle R S Fr Gr hFr hGr) (hle S R Gr Fr hGr hFr)

lemma derivedRowStepMap_isIso_of_quasiIso (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (X Y : CochainComplex.Plus A) (R : ResolutionData X.obj) (S : ResolutionData Y.obj)
    [R.bicomplex.HasTotal (.up ℤ)] [S.bicomplex.HasTotal (.up ℤ)]
    [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
    [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
    (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
    (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
    (hFr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj R.bicomplex) Prod.snd Fr)
    (hGr : FiniteDiagonalFiltrations.HasFiltrationFormula
      ((mapDouble F).obj S.bicomplex) Prod.snd Gr)
    (D : F03Specs.PageData Fr) (E : F03Specs.PageData Gr)
    (f : X ⟶ Y) (hf : QuasiIso f.hom) (a : R.bicomplex ⟶ S.bicomplex)
    (ha : CartanEilenbergComparison.IsLift R S f.hom a)
    (g : FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex),Fr⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex),Gr⟩)
    (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ))
    (M : FilteredPageFunctoriality.MapData g D E) (p n : ℤ) :
    IsIso (derivedRowStepMap F X Y R S Fr Gr g p n) := by
  have hs := FiniteTargetComparison.steps_isIso g
    (rowConverges F R Fr hFr).finite (rowConverges F S Gr hGr).finite
    (FiniteTargetComparison.graded_isIso g
      (rowConverges F R Fr hFr).finite (rowConverges F S Gr hGr).finite D E M 2 (by omega)
      (rowPage_isIso_of_quasiIso F R S Fr Gr hFr hGr D E a g hg M f.hom hf ha 2 (by omega))) p n
  dsimp only [derivedRowStepMap]
  infer_instance



section DerivedGradedMaps
open FiniteFiltrationConvergence
variable (F : A ⥤ B) [F.Additive]
  (X Y : CochainComplex.Plus A) (R : ResolutionData X.obj) (S : ResolutionData Y.obj)
  [R.bicomplex.HasTotal (.up ℤ)] [S.bicomplex.HasTotal (.up ℤ)]
  [((mapDouble F).obj R.bicomplex).HasTotal (.up ℤ)]
  [((mapDouble F).obj S.bicomplex).HasTotal (.up ℤ)]
  (Fr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex)))
  (Gr : Filtration (DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex)))
  (g : FilteredMap ⟨DoubleTotalization.sumTotal ((mapDouble F).obj R.bicomplex),Fr⟩
    ⟨DoubleTotalization.sumTotal ((mapDouble F).obj S.bicomplex),Gr⟩)

lemma derivedRowStepMap_comm (p n : ℤ) :
    Subobject.ofLE _ _ (derivedRowPiece_decreasing F X R Fr p n) ≫
        derivedRowStepMap F X Y R S Fr Gr g p n =
      derivedRowStepMap F X Y R S Fr Gr g (p+1) n ≫
        Subobject.ofLE _ _ (derivedRowPiece_decreasing F Y S Gr p n) := by
  dsimp only [derivedRowStepMap, derivedRowPiece]
  apply (cancel_epi (transportStepIso (totalComputationIso F X R n).symm
    (cohomologyPiece Fr (p+1) n)).hom).1
  rw [← Category.assoc, ← transportStepIso_comm]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, cohomologyStepMap_comm g p n, Category.assoc,
    transportStepIso_comm]
  exact cohomologyPiece_decreasing Fr p n

/-- The quotient map induced by the actual transported filtration steps. -/
def derivedRowGradedMap (p n : ℤ) : derivedRowGraded F X R Fr p n ⟶
    derivedRowGraded F Y S Gr p n :=
  cokernel.map _ _ (derivedRowStepMap F X Y R S Fr Gr g (p+1) n)
    (derivedRowStepMap F X Y R S Fr Gr g p n)
    (derivedRowStepMap_comm F X Y R S Fr Gr g p n)

lemma derivedRowGradedMap_transport (p n : ℤ) :
    gradedCohomologyMap g p n ≫
        (transportGradedIso (totalComputationIso F Y S n).symm
          (cohomologyPiece_decreasing Gr p n)).hom =
      (transportGradedIso (totalComputationIso F X R n).symm
          (cohomologyPiece_decreasing Fr p n)).hom ≫
        derivedRowGradedMap F X Y R S Fr Gr g p n := by
  exact transportGradedIso_naturality _ _ _ _ _ _ (cohomologyStepMap_comm g p n)
    _ _ (derivedRowStepMap_comm F X Y R S Fr Gr g p n)
    (by simp only [derivedRowStepMap, Category.assoc, Iso.hom_inv_id_assoc])

lemma derivedRowLimitIso_naturality
    (D : F03Specs.PageData Fr) (E : F03Specs.PageData Gr)
    (M : FilteredPageFunctoriality.MapData g D E) (r p n : ℤ)
    (hFr : Stabilized Fr r p n) (hGr : Stabilized Gr r p n) :
    M.map r p n ≫ (derivedRowLimitIso F Y S Gr E r p n hGr).hom =
      (derivedRowLimitIso F X R Fr D r p n hFr).hom ≫
        derivedRowGradedMap F X Y R S Fr Gr g p n := by
  dsimp only [derivedRowLimitIso, Iso.trans_hom]
  rw [← Category.assoc, limitIso_naturality g D E M r p n
    (limitIso Fr D r p n hFr) (limitIso Gr E r p n hGr) hFr]
  rw [Category.assoc, derivedRowGradedMap_transport F X Y R S Fr Gr g p n]
  simp only [Category.assoc]
end DerivedGradedMaps



def actualDerivedRowTarget (F : A ⥤ B) [F.Additive]
    (X : CochainComplex.Plus A) (W : RowRealization F X.obj) : DerivedRowTarget F X W where
  targetComparison := derivedTotalComparison F X W.resolution
  comparison := totalComputationIso F X W.resolution
  comparison_eq _ := rfl

def actualDerivedRowStepMap (F : A ⥤ B) [F.Additive]
    {X Y : CochainComplex.Plus A} (W : RowRealization F X.obj)
    (V : RowRealization F Y.obj) (f : X ⟶ Y) (p n : ℤ) :
    ((actualDerivedRowTarget F X W).piece p n : B) ⟶
      ((actualDerivedRowTarget F Y V).piece p n : B) :=
  derivedRowStepMap F X Y W.resolution V.resolution W.filtration V.filtration
    (rowFilteredMap F W.resolution V.resolution W.filtration V.filtration W.formula V.formula
      (CartanEilenbergComparison.comparison W.resolution V.resolution f.hom)) p n

lemma actualDerivedRowStepMap_arrow (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {X Y : CochainComplex.Plus A} (W : RowRealization F X.obj)
    (V : RowRealization F Y.obj) (f : X ⟶ Y) (p n : ℤ) :
    actualDerivedRowStepMap F W V f p n ≫ ((actualDerivedRowTarget F Y V).piece p n).arrow =
      ((actualDerivedRowTarget F X W).piece p n).arrow ≫ derivedCohomologyMap F f n := by
  exact derivedRowStepMap_arrow F X Y W.resolution V.resolution W.filtration V.filtration
    f (CartanEilenbergComparison.comparison W.resolution V.resolution f.hom)
    (CartanEilenbergComparison.comparison_augmentation W.resolution V.resolution f.hom)
    _ (rowFilteredMap_hom F W.resolution V.resolution W.filtration V.filtration W.formula V.formula _) p n

lemma actualDerivedRowStepMap_lift_formula (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {X Y : CochainComplex.Plus A} (W : RowRealization F X.obj)
    (V : RowRealization F Y.obj) (f : X ⟶ Y)
    (a : W.resolution.bicomplex ⟶ V.resolution.bicomplex)
    (ha : CartanEilenbergComparison.IsLift W.resolution V.resolution f.hom a)
    (g : FilteredMap
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj W.resolution.bicomplex),W.filtration⟩
      ⟨DoubleTotalization.sumTotal ((mapDouble F).obj V.resolution.bicomplex),V.filtration⟩)
    (hg : g.hom = HomologicalComplex₂.total.map ((mapDouble F).map a) (.up ℤ)) (p n : ℤ) :
    actualDerivedRowStepMap F W V f p n =
      derivedRowStepMap F X Y W.resolution V.resolution W.filtration V.filtration g p n := by
  apply (cancel_mono ((actualDerivedRowTarget F Y V).piece p n).arrow).1
  rw [actualDerivedRowStepMap_arrow]
  exact (derivedRowStepMap_arrow F X Y W.resolution V.resolution W.filtration V.filtration f a ha g hg p n).symm

/-- The finite row filtration on the actual total derived cohomology object. -/
def actualDerivedTargetSystem (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] : DerivedTargetSystem F where
  target := actualDerivedRowTarget F
  finite X W n := derivedRowPiece_finite F X W.resolution W.filtration W.formula n
  limitIso X W r p n h := derivedRowLimitIso F X W.resolution W.filtration W.pages r p n h
  representative X W r p n h :=
    derivedRowLimitIso_representative F X W.resolution W.filtration W.pages r p n h
  stepMap W V f p n := actualDerivedRowStepMap F W V f p n
  step_arrow W V f p n := actualDerivedRowStepMap_arrow F W V f p n
  step_id X W p n := by
    apply (cancel_mono ((actualDerivedRowTarget F X W).piece p n).arrow).1
    rw [actualDerivedRowStepMap_arrow]
    dsimp only [derivedCohomologyMap]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    simp
  step_comp W V U f g p n := by
    apply (cancel_mono ((actualDerivedRowTarget F _ U).piece p n).arrow).1
    rw [actualDerivedRowStepMap_arrow]
    rw [Category.assoc, actualDerivedRowStepMap_arrow,
      ← Category.assoc, actualDerivedRowStepMap_arrow]
    simp only [Category.assoc, derivedCohomologyMap, CategoryTheory.Functor.map_comp]
  step_comm W V f p n := by
    exact derivedRowStepMap_comm F _ _ W.resolution V.resolution W.filtration V.filtration _ p n
  inverts_quasiIso W V f hf p n := by
    let g := rowFilteredMap F W.resolution V.resolution W.filtration V.filtration W.formula V.formula
      (CartanEilenbergComparison.comparison W.resolution V.resolution f.hom)
    exact derivedRowStepMap_isIso_of_quasiIso F _ _ W.resolution V.resolution
      W.filtration V.filtration W.formula V.formula W.pages V.pages f hf
      (CartanEilenbergComparison.comparison W.resolution V.resolution f.hom)
      (CartanEilenbergComparison.comparison_augmentation W.resolution V.resolution f.hom)
      g (rowFilteredMap_hom F W.resolution V.resolution W.filtration V.filtration W.formula V.formula _)
      (FilteredPageFunctoriality.mapData g W.pages V.pages) p n
  resolution_independent X W V p n :=
    derivedRowPiece_resolution_independent F X W.resolution V.resolution
      W.filtration V.filtration W.formula V.formula p n
  lift_step_formula W V f a ha g hg p n :=
    actualDerivedRowStepMap_lift_formula F W V f a ha g hg p n
  limit_naturality W V f a ha g hg M r p n hW hV := by
    have hn := derivedRowLimitIso_naturality F _ _ W.resolution V.resolution
      W.filtration V.filtration g W.pages V.pages M r p n hW hV
    simpa only [actualDerivedRowTarget, DerivedRowTarget.graded, DerivedRowTarget.piece,
      DerivedRowTarget.decreasing, derivedRowGraded, derivedRowPiece, derivedRowGradedMap,
      ← actualDerivedRowStepMap_lift_formula F W V f a ha g hg] using hn

theorem derivedTargets : Specs.DerivedTargets.{v,u,v',u',w,w'} := by
  intro A _ _ B _ _ _ _ _ F _ _
  exact ⟨actualDerivedTargetSystem F⟩

end DerivedComputation

/-- The complete row hypercohomology construction in HA-G03. -/
theorem rowHypercohomology : Specs.FullStatement.{v,u,v',u',w,w'} :=
  ⟨splitRows, invariantColumns, rowPages, computedRows, rowRealizationsExist,
    pageFunctoriality, derivedTargets⟩


end AdvancedHomologicalAlgebra.RowHypercohomology
