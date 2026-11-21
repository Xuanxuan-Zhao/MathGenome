import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.AcyclicCoverComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CechToCohomology

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory AdvancedHomologicalAlgebra.Cech
open AdvancedHomologicalAlgebra.CechToCohomology
open AdvancedHomologicalAlgebra.DoubleTotalization
open HomologicalComplex
universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace AdvancedHomologicalAlgebra.AcyclicCoverComparison

section RowEdge
open DoubleTotalization FiniteDiagonalFiltrations
open DoubleComplexFirstPages FilteredPage
universe w z
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {B : Type w} [Category.{z} B] [Abelian B]
variable {K : Bicomplex B} [K.HasTotal (.up ℤ)]
variable {F : Filtration (sumTotal K)} {hF : HasFiltrationFormula K Prod.fst F}
variable {D : F03Specs.PageData F} (C : ColumnData K F hF D)

/-- The second-page isomorphism sends a representative to its class in
the complex of vertical cohomology. -/
private lemma row_second_representative_step (p : ℤ) {T : B}
    (a : T ⟶ (almost F (1 + 1) (p + 1) (p + 1) : B))
    (x : T ⟶ (verticalHomology K 0).X (p + 1))
    (h : a ≫ Subobject.ofLE _ _ (PageCohomology.almost_succ_le F 1 (p + 1) (p + 1)) ≫
        toPage F 1 (p + 1) (p + 1) (D.containment 1 (p + 1) (p + 1)) ≫
        eqToHom (congrArg (PageCohomology.object F D 1 (p + 1)) (add_zero (p + 1)).symm) ≫
        (C.firstIso (p + 1) 0).hom = x)
    (hx : x ≫ (verticalHomology K 0).d (p + 1) (p + 1 + 1) = 0) :
    a ≫ toPage F (1+1) (p + 1) (p + 1) (D.containment 2 (p + 1) (p + 1)) ≫
      eqToHom (congrArg (PageCohomology.object F D 2 (p + 1)) (add_zero (p + 1)).symm) ≫
      (C.secondIso (p + 1) 0).hom =
    (verticalHomology K 0).liftCycles x (p + 1 + 1) (by simp) hx ≫
      (verticalHomology K 0).homologyπ (p + 1) := by
  obtain ⟨P, hP⟩ := C.second_formula 0
  let L := verticalHomology K 0
  let F₁ := firstPageShortIso F D L 0 (fun r => C.firstIso r 0) (fun r => C.first_d r 0) p
  let W := L.homologyIsoSc' p (p+1) (p+1+1) (by simp) (by simp)
  let S₁ := PageCohomology.shortComplex F D 1 (by omega) p (p+0)
  let z : T ⟶ (almost F (1 + 1) (p + 1) (p + 0 + 1) : B) :=
    a ≫ eqToHom (congrArg (fun n => (almost F (1 + 1) (p+1) n : B)) (by omega))
  have transp (r : ℤ) (n n' : ℤ) (e : n = n') :
      toPage F r (p + 1) n (D.containment r (p + 1) n) ≫
        eqToHom (congrArg (PageCohomology.object F D r (p+1)) e) =
      eqToHom (congrArg (fun i => (almost F r (p+1) i : B)) e) ≫
        toPage F r (p + 1) n' (D.containment r (p + 1) n') := by
    subst n'
    simp
  have transp₁ (n n' : ℤ) (e : n = n') :
      eqToHom (congrArg (fun i => (almost F (1 + 1) (p+1) i : B)) e) ≫
        Subobject.ofLE _ _ (PageCohomology.almost_succ_le F 1 (p+1) n') ≫
        toPage F 1 (p+1) n' (D.containment 1 (p+1) n') =
      Subobject.ofLE _ _ (PageCohomology.almost_succ_le F 1 (p+1) n) ≫
        toPage F 1 (p+1) n (D.containment 1 (p+1) n) ≫
        eqToHom (congrArg (PageCohomology.object F D 1 (p+1)) e) := by
    subst n'
    simp
  have middle : F₁.hom.τ₂ =
      eqToHom (congrArg (PageCohomology.object F D 1 (p+1))
        (show p+0+1 = p+1+0 by omega)) ≫ (C.firstIso (p+1) 0).hom := rfl
  have hz : z ≫ PageCohomology.nextRepresentative F D 1 (p+1) (p+0+1) ≫ F₁.hom.τ₂ = x := by
    rw [middle]
    have tr := transp₁ (p+1) (p+0+1) (by omega)
    simp only [z, PageCohomology.nextRepresentative, Category.assoc]
    erw [reassoc_of% tr]
    simp only [eqToHom_trans_assoc]
    change _ = x
    simpa only [toPage, Category.assoc] using h
  have hz_cycle : (z ≫ PageCohomology.nextRepresentative F D 1 (p+1) (p+0+1)) ≫ S₁.g = 0 := by
    rw [Category.assoc]
    change z ≫ PageCohomology.nextRepresentative F D 1 (p+1) (p+0+1) ≫
      D.differential 1 _ (p+1) (p+0+1) = 0
    rw [P.next_cycle 1 (by omega) p (p+0), comp_zero]
  have hz_lift :
      S₁.liftCycles (z ≫ PageCohomology.nextRepresentative F D 1 (p+1) (p+0+1)) hz_cycle ≫
        ShortComplex.cyclesMap F₁.hom =
      L.liftCycles x (p+1+1) (by simp) hx ≫ (L.cyclesIsoSc' p (p+1) (p+1+1)
        (by simp) (by simp)).hom := by
    apply (cancel_mono (L.sc' p (p+1) (p+1+1)).iCycles).1
    simpa only [Category.assoc, ShortComplex.cyclesMap_i, ShortComplex.liftCycles_i_assoc,
      cyclesIsoSc'_hom_iCycles, liftCycles_i] using hz
  have hz_next :
      z ≫ toPage F (1+1) (p+1) (p+0+1) (D.containment 2 (p+1) (p+0+1)) ≫
        (P.nextIso 1 (by omega) p (p+0)).hom =
      S₁.liftCycles (z ≫ PageCohomology.nextRepresentative F D 1 (p+1) (p+0+1)) hz_cycle ≫
        S₁.homologyπ := by
    erw [P.nextIso_formula]
    simp only [← Category.assoc]
    congr 1
    apply (cancel_mono S₁.iCycles).1
    change (z ≫ S₁.liftCycles _ _) ≫ S₁.iCycles = _
    simp only [Category.assoc, ShortComplex.liftCycles_i]
  have hP₀ := hP p
  dsimp only at hP₀
  rw [← hP₀]
  simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, ShortComplex.homologyMapIso_hom]
  change a ≫ toPage F (1+1) (p+1) (p+1) _ ≫ _ ≫ _ ≫ _ ≫ ShortComplex.homologyMap F₁.hom ≫
    W.inv = _
  have tr := transp 2 (p+1) (p+0+1) (by omega)
  rw [eqToHom_trans_assoc]
  simp only [toPage, Category.assoc] at tr ⊢
  erw [reassoc_of% tr]
  rw [← Category.assoc a]
  change z ≫ _ = _
  have hz_next' := hz_next
  simp only [toPage, Category.assoc] at hz_next'
  erw [reassoc_of% hz_next', ShortComplex.homologyπ_naturality_assoc,
    reassoc_of% hz_lift]
  change _ ≫ _ ≫ _ ≫ (L.homologyIsoSc' p (p+1) (p+1+1) (by simp) (by simp)).inv = _
  simp only [π_homologyIsoSc'_inv,
    Iso.hom_inv_id_assoc]
  rfl

open FiniteFiltrationConvergence EdgesAndFiveTerms

private lemma row_second_representative (n : ℤ) {T : B}
    (a : T ⟶ (almost F 2 n n : B))
    (x : T ⟶ (verticalHomology K 0).X n)
    (h : a ≫ Subobject.ofLE _ _ (PageCohomology.almost_succ_le F 1 n n) ≫
        toPage F 1 n n (D.containment 1 n n) ≫
        eqToHom (congrArg (PageCohomology.object F D 1 n) (add_zero n).symm) ≫
        (C.firstIso n 0).hom = x)
    (hx : x ≫ (verticalHomology K 0).d n (n+1) = 0) :
    a ≫ toPage F 2 n n (D.containment 2 n n) ≫
      eqToHom (congrArg (PageCohomology.object F D 2 n) (add_zero n).symm) ≫
      (C.secondIso n 0).hom =
    (verticalHomology K 0).liftCycles x (n+1) (by simp) hx ≫
      (verticalHomology K 0).homologyπ n := by
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, p+1 = n := ⟨n-1, by omega⟩
  exact row_second_representative_step C p a x h hx

private lemma row_first_representative (n m : ℤ) (hm : n+0=m) {T : B}
    (x : T ⟶ (K.X n).X 0)
    (hx : x ≫ (K.X n).d 0 1 = 0)
    (a : T ⟶ (almost F 1 n m : B))
    (ha : a ≫ (almost F 1 n m).arrow = x ≫ sumInjection K n 0 m hm) :
    a ≫ toPage F 1 n m (D.containment 1 n m) ≫
      eqToHom (congrArg (PageCohomology.object F D 1 n) hm.symm) ≫
      (C.firstIso n 0).hom = (K.X n).liftCycles x 1 (by simp) hx ≫ (K.X n).homologyπ 0 := by
  subst m
  simpa only [eqToHom_refl, Category.id_comp, zero_add] using C.first_formula n 0 x hx a ha

/-- The bottom edge sends the vertical classes of a row-zero augmentation
to the total cohomology classes of that augmentation. -/
private theorem row_edge_augmentation (E : EdgeData F D) {L : CochainComplex B ℤ}
    (v : L ⟶ sumTotal K) (vertical : L ⟶ verticalHomology K 0)
    (g : ∀ n : ℤ, L.X n ⟶ (K.X n).X 0)
    (hg : ∀ n, g n ≫ (K.X n).d 0 1 = 0)
    (hv : ∀ n, v.f n = g n ≫ sumInjection K n 0 n (add_zero n))
    (hvertical : ∀ n, vertical.f n = (K.X n).liftCycles (g n) 1 (by simp) (hg n) ≫ (K.X n).homologyπ 0)
    (n : ℤ) (hn : 0 ≤ n) :
    homologyMap vertical n ≫ (C.secondIso n 0).inv ≫
      eqToHom (congrArg (PageCohomology.object F D 2 n) (add_zero n)) ≫
      E.row n hn = homologyMap v n := by
  let i := L.iCycles n
  let σ : L.cycles n ⟶ (F.step n).X n :=
    i ≫ g n ≫ summandToStep K Prod.fst F hF n n 0 n (add_zero n) le_rfl
  have hσ : σ ≫ (F.piece n n).arrow = i ≫ v.f n := by
    simp [σ, hv n, Category.assoc]
  have hσ_d : σ ≫ (F.step n).d n (n+1) = 0 := by
    apply (cancel_mono (F.piece n (n+1)).arrow).1
    simp only [Category.assoc, Filtration.step, Filtration.differential_arrow, zero_comp]
    rw [← Category.assoc, hσ, Category.assoc, v.comm, ← Category.assoc]
    simp [i]
  let z := liftClosed F n n σ hσ_d
  let a := z ≫ Subobject.ofLE _ _ (closed_le_almost F 2 n n)
  let b := a ≫ Subobject.ofLE _ _ (PageCohomology.almost_succ_le F 1 n n)
  have hba : b ≫ (almost F 1 n n).arrow = (i ≫ g n) ≫ sumInjection K n 0 n (add_zero n) := by
    simp only [b, a, Category.assoc, Subobject.ofLE_arrow]
    rw [liftClosed_arrow, hσ, hv n]
  have h1 := row_first_representative C n n (add_zero n) (i ≫ g n)
    (by simp [Category.assoc, hg]) b hba
  have h1' : b ≫ toPage F 1 n n (D.containment 1 n n) ≫
      eqToHom (congrArg (PageCohomology.object F D 1 n) (add_zero n).symm) ≫
      (C.firstIso n 0).hom = i ≫ vertical.f n := by
    refine h1.trans ?_
    rw [hvertical n]
    have hcomp := comp_liftCycles (K := K.X n) (g n) 1 (by simp) (hg n) i
    simpa only [Category.assoc] using congrArg (fun f => f ≫ (K.X n).homologyπ 0) hcomp.symm
  have h1'' : a ≫ Subobject.ofLE _ _ (PageCohomology.almost_succ_le F 1 n n) ≫
      toPage F 1 n n (D.containment 1 n n) ≫
      eqToHom (congrArg (PageCohomology.object F D 1 n) (add_zero n).symm) ≫
      (C.firstIso n 0).hom = i ≫ vertical.f n := by
    simpa only [b, Category.assoc] using h1'
  have h₂ := row_second_representative C n a (i ≫ vertical.f n) h1''
    (by rw [Category.assoc, vertical.comm, ← Category.assoc, iCycles_d, zero_comp])
  apply (cancel_epi (L.homologyπ n)).1
  simp only [homologyπ_naturality_assoc, homologyπ_naturality]
  have hcyc : (verticalHomology K 0).liftCycles (i ≫ vertical.f n) (n+1) (by simp)
        (by rw [Category.assoc, vertical.comm, ← Category.assoc, iCycles_d, zero_comp]) =
      cyclesMap vertical n := by
    apply (cancel_mono ((verticalHomology K 0).iCycles n)).1
    rw [liftCycles_i, cyclesMap_i]
  rw [hcyc] at h₂
  erw [← Category.assoc (cyclesMap vertical n), ← h₂]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hz : a ≫ toPage F 2 n n (D.containment 2 n n) ≫ E.row n hn =
      z ≫ closedToPage F D 2 n n ≫ E.row n hn := by
    simp only [a, closedToPage, Category.assoc]
  simp only [toPage, Category.assoc] at hz
  erw [hz]
  rw [E.row_formula]
  change z ≫ (closedClass F n n ≫ (cohomologyPiece F n n).arrow) = _
  rw [closedClass_arrow]
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono ((sumTotal K).iCycles n)).1
  simp only [Category.assoc, liftCycles_i, cyclesMap_i]
  rw [show z ≫ (closed F n n).arrow = σ ≫ (F.piece n n).arrow from liftClosed_arrow F n n σ hσ_d]
  exact hσ

end RowEdge

variable {X : TopCat.{u}} (R : RingSheaf X) {U : Opens X} {A : Type v} (c : Cover U A)

private lemma embed_nat (n : ℕ) : natEmbedding.f n = (n : ℤ) := by simp [natEmbedding]

private lemma not_mem_of_neg {k : ℤ} (hk : k < 0) (n : ℕ) : natEmbedding.f n ≠ k := by
  rw [embed_nat]
  omega

private lemma negative_entry {M : Modules R} (I : InjectiveResolution M)
    (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero (((resolutionDoubleComplexInt R c M I).X p).X q) :=
  natToIntDoubleComplex_inQuadrant (resolutionDoubleComplex R c M I) p q (by omega)

private lemma isZero_homology_of_X {B : Type*} [Category* B] [Abelian B]
    (K : CochainComplex B ℤ) (n : ℤ) (h : IsZero (K.X n)) :
    IsZero (K.homology n) :=
  (HomologicalComplex.ExactAt.of_isZero h).isZero_homology

private abbrev cechComplexIntMap {M N : Modules R} (f : M ⟶ N) :=
  extendMap ((cochainFunctor R c).map ((SheafOfModules.forget R).map f)) natEmbedding

private def verticalAxis {M : Modules R} (I : InjectiveResolution M) :
    cechComplexInt R c M ⟶ (resolutionDoubleComplexInt R c M I).flip.X 0 :=
  cechComplexIntMap R c (I.ι.f 0) ≫
    (natToIntDoubleComplexRowIso (resolutionDoubleComplex R c M I) 0).inv

private lemma verticalAxis_f {M : Modules R} (I : InjectiveResolution M) (p : ℕ) :
    (verticalAxis R c I).f (p : ℤ) =
      ((cechComplex R c M.val).extendXIso natEmbedding (embed_nat p)).hom ≫
        ((cochainFunctor R c).map ((SheafOfModules.forget R).map (I.ι.f 0))).f p ≫
        (entryIso R c M I p 0).inv := by
  let t := natToIntDoubleComplexRowIso (resolutionDoubleComplex R c M I) 0
  let K := (resolutionDoubleComplex R c M I).flip.X 0
  have ht : t.hom.f (p : ℤ) ≫ (K.extendXIso natEmbedding (embed_nat p)).hom =
      (entryIso R c M I p 0).hom :=
    natToIntDoubleComplexRowIso_hom_f (resolutionDoubleComplex R c M I) p 0
  apply (cancel_mono (entryIso R c M I p 0).hom).1
  rw [assoc, assoc, Iso.inv_hom_id, comp_id, ← ht]
  simp only [verticalAxis, comp_f, assoc]
  change (cechComplexIntMap R c (I.ι.f 0)).f (p : ℤ) ≫ t.inv.f (p : ℤ) ≫ t.hom.f (p : ℤ) ≫ _ = _
  have hinv := congrArg (fun f => f.f (p : ℤ)) t.inv_hom_id
  simp only [comp_f, id_f] at hinv
  erw [reassoc_of% hinv, extendMap_f _ natEmbedding (embed_nat p)]
  change _ ≫ _ ≫ (K.extendXIso natEmbedding (embed_nat p)).inv ≫
    (K.extendXIso natEmbedding (embed_nat p)).hom = _
  rw [Iso.inv_hom_id, comp_id]
  rfl

private abbrev termInDegree (p : ℕ) :=
  SheafOfModules.forget R ⋙ cochainFunctor R c ⋙ eval (SectionModule (U := U) R) (.up ℕ) p

/-- The resolution augmentation, extended using the embedding of HA-H03. -/
private def stalkToResolution {M : Modules R} (I : InjectiveResolution M) :
    (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I.cocomplex.extend natEmbedding :=
  (extendSingleIso natEmbedding M 0 0 (embed_nat 0)).inv ≫ extendMap I.ι natEmbedding

private lemma stalkToResolution_f {M : Modules R} (I : InjectiveResolution M) :
    (stalkToResolution R I).f 0 = (singleObjXSelf (.up ℤ) 0 M).hom ≫ I.ι.f 0 ≫
      (I.cocomplex.extendXIso natEmbedding (embed_nat 0)).inv := by
  rw [stalkToResolution, comp_f, extendSingleIso_inv_f natEmbedding M 0 0 (embed_nat 0)]
  erw [extendMap_f I.ι natEmbedding (embed_nat 0)]
  simp

private def resolvedColumnMap {M : Modules R} (I : InjectiveResolution M) (p : ℕ) :
    (single (SectionModule (U := U) R) (.up ℤ) 0).obj ((cechComplexInt R c M).X (p : ℤ)) ⟶
      (resolutionDoubleComplexInt R c M I).X (p : ℤ) :=
  let F := termInDegree R c p
  (single _ (.up ℤ) 0).map ((cechComplex R c M.val).extendXIso natEmbedding (embed_nat p)).hom ≫
    ((singleMapHomologicalComplex F (.up ℤ) 0).app M).inv ≫
    (F.mapHomologicalComplex (.up ℤ)).map (stalkToResolution R I) ≫
    (mapExtendIso F I.cocomplex natEmbedding).hom ≫ (columnIso R c M I p).inv

private lemma resolvedColumnMap_f {M : Modules R} (I : InjectiveResolution M) (p : ℕ) :
    (resolvedColumnMap R c I p).f 0 =
      (singleObjXSelf (.up ℤ) 0 ((cechComplexInt R c M).X (p : ℤ))).hom ≫
        (verticalAxis R c I).f (p : ℤ) := by
  let F := termInDegree R c p
  let E := I.cocomplex.extendXIso natEmbedding (embed_nat 0)
  let e := ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendXIso natEmbedding (embed_nat 0)
  have hf : (mapExtendIso F I.cocomplex natEmbedding).hom.f (0 : ℤ) ≫ e.hom =
      F.map E.hom :=
    mapExtendIso_hom_f F I.cocomplex natEmbedding (embed_nat 0)
  have h : F.map E.inv ≫ (mapExtendIso F I.cocomplex natEmbedding).hom.f 0 = e.inv := by
    apply (cancel_mono e.hom).1
    rw [Category.assoc, hf, ← F.map_comp, Iso.inv_hom_id, F.map_id, Iso.inv_hom_id]
  rw [verticalAxis_f]
  simp only [resolvedColumnMap, comp_f, single_map_f_self, Functor.mapHomologicalComplex_map_f,
    stalkToResolution_f, assoc, Iso.trans_inv, Functor.mapIso_inv, eval_map]
  change _ ≫ _ ≫ F.map (singleObjXSelf (.up ℤ) 0 M).inv ≫
    F.map ((singleObjXSelf (.up ℤ) 0 M).hom ≫ I.ι.f 0 ≫ E.inv) ≫ _ ≫ _ = _
  rw [← F.map_comp_assoc, Iso.inv_hom_id_assoc, F.map_comp, assoc, reassoc_of% h]
  rfl

private lemma vertical_cycle {M : Modules R} (I : InjectiveResolution M)
    (p q : ℤ) (_hq : (ComplexShape.up ℤ).Rel 0 q) :
    (verticalAxis R c I).f p ≫ ((resolutionDoubleComplexInt R c M I).X p).d 0 q = 0 := by
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    apply (cancel_epi (singleObjXSelf (.up ℤ) 0 ((cechComplexInt R c M).X (p : ℤ))).hom).1
    rw [← assoc, ← resolvedColumnMap_f, (resolvedColumnMap R c I p).comm,
      single_obj_d, zero_comp, comp_zero]
  · exact ((cechComplex R c M.val).isZero_extend_X natEmbedding p
      (not_mem_of_neg (lt_of_not_ge hp))).eq_of_src _ _

private lemma transportAugmentationClass {B : Type*} [Category* B] [Abelian B] {C : CochainComplex B ℤ}
    {K : CochainComplex B ℕ} (i : C ≅ K.extend natEmbedding)
    {P Q : B} (x : P ≅ Q) (a : P ⟶ C.cycles 0) (b : Q ⟶ K.cycles 0)
    (hab : a ≫ C.iCycles 0 ≫ i.hom.f 0 ≫
      (K.extendXIso natEmbedding (by simp [natEmbedding] : natEmbedding.f 0 = (0 : ℤ))).hom =
      x.hom ≫ b ≫ K.iCycles 0) :
    a ≫ C.homologyπ 0 ≫ (homologyMapIso i 0).hom ≫
      (K.extendHomologyIso natEmbedding (by simp [natEmbedding] : natEmbedding.f 0 = (0 : ℤ))).hom =
      x.hom ≫ b ≫ K.homologyπ 0 := by
  have h : a ≫ cyclesMap i.hom 0 ≫
      (K.extendCyclesIso natEmbedding (by simp [natEmbedding] : natEmbedding.f 0 = (0 : ℤ))).hom = x.hom ≫ b := by
    apply (cancel_mono (K.iCycles 0)).1
    simpa only [assoc, extendCyclesIso_hom_iCycles, cyclesMap_i_assoc] using hab
  simp only [homologyMapIso_hom, homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom]
  simpa only [assoc] using congrArg (fun k => k ≫ K.homologyπ 0) h

@[reassoc] private lemma mapHomologyIso_homologyπ
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (S : ShortComplex C) (G : C ⥤ D) [G.Additive] [G.PreservesHomology] :
    (S.map G).homologyπ ≫ (S.mapHomologyIso G).hom =
      (S.mapCyclesIso G).hom ≫ G.map S.homologyπ := by
  let H := S.homologyData.left
  rw [H.mapCyclesIso_eq G, H.mapHomologyIso_eq G]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
    ShortComplex.LeftHomologyData.map_π, assoc, ← G.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]

private lemma mappedAugmentation_homology
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C]
    {M : C} (I : InjectiveResolution M) (F : C ⥤ D) [F.Additive]
    (G : D ⥤ E) [G.Additive] [G.PreservesHomology]
    (k : G.obj (F.obj M) ⟶
      ((I.cocomplex |> (F.mapHomologicalComplex (.up ℕ)).obj) |>
        (G.mapHomologicalComplex (.up ℕ)).obj).cycles 0)
    (hk : k ≫
      (((G.mapHomologicalComplex (.up ℕ)).obj ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)).iCycles 0) =
        G.map (F.map (I.ι.f 0))) :
    k ≫
      (((G.mapHomologicalComplex (.up ℕ)).obj ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)).homologyπ 0) ≫
      ((((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc 0).mapHomologyIso G).hom ≫
      G.map (I.isoRightDerivedObj F 0).inv =
      G.map (F.toRightDerivedZero.app M) := by
  let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let S := K.sc 0
  have hh : k ≫ (S.mapCyclesIso G).hom = G.map (I.toRightDerivedZero' F) := by
    apply (cancel_mono (G.map S.iCycles)).1
    rw [assoc, ShortComplex.mapCyclesIso_hom_iCycles, ← G.map_comp]
    exact hk.trans (G.congr_map (I.toRightDerivedZero'_comp_iCycles F)).symm
  change k ≫ (S.map G).homologyπ ≫ (S.mapHomologyIso G).hom ≫ _ = _
  rw [mapHomologyIso_homologyπ_assoc, ← assoc, hh, ← G.map_comp, ← G.map_comp,
    I.toRightDerivedZero_eq F]
  rfl

private lemma verticalCoefficientComponent
    {M : Modules R} (I : InjectiveResolution M) (D : ResolutionVerticalComparison R c M I)
    (p : ℕ)
    (a : (cechComplexInt R c M).X (p : ℤ) ⟶
      ((resolutionDoubleComplexInt R c M I).X (p : ℤ)).cycles 0)
    (ha : a ≫ ((resolutionDoubleComplexInt R c M I).X (p : ℤ)).iCycles 0 =
      (verticalAxis R c I).f (p : ℤ)) :
    (a ≫ ((resolutionDoubleComplexInt R c M I).X (p : ℤ)).homologyπ 0) ≫
      (D.iso 0).hom.f (p : ℤ) =
      (extendMap ((cochainFunctor R c).map
        ((SheafOfModules.forget R).toRightDerivedZero.app M)) natEmbedding).f (p : ℤ) := by
  let F := SheafOfModules.forget R
  let G := cechTerm R c p
  let K := (resolutionDoubleComplex R c M I).X p
  let C := (resolutionDoubleComplexInt R c M I).X (p : ℤ)
  let i := columnIso R c M I p
  let x := (cechComplex R c M.val).extendXIso natEmbedding (embed_nat p)
  let y := K.extendXIso natEmbedding (embed_nat 0)
  have hb : G.map (F.map (I.ι.f 0)) ≫ K.d 0 1 = 0 := by
    change G.map (F.map (I.ι.f 0)) ≫ G.map (F.map (I.cocomplex.d 0 1)) = 0
    rw [← G.map_comp, ← F.map_comp, I.ι.comm, single_obj_d, zero_comp, F.map_zero, G.map_zero]
  let b := K.liftCycles (G.map (F.map (I.ι.f 0))) 1 (by simp) hb
  have hb' : b ≫ K.iCycles 0 = G.map (F.map (I.ι.f 0)) := by
    simp only [b, liftCycles_i]
  have hab : a ≫ C.iCycles 0 ≫ i.hom.f 0 ≫ y.hom = x.hom ≫ b ≫ K.iCycles 0 := by
    rw [← assoc a, ha, verticalAxis_f, hb']
    change (x.hom ≫ G.map (F.map (I.ι.f 0)) ≫ y.inv ≫ i.inv.f 0) ≫
      i.hom.f 0 ≫ y.hom = _
    have h := congrArg (fun f => f.f (0 : ℤ)) i.inv_hom_id
    simp only [comp_f, id_f] at h
    simp only [assoc, reassoc_of% h, Iso.inv_hom_id, comp_id]
  have hclass := transportAugmentationClass i x a b hab
  let L := cechComplex R c ((localCohomology R 0).obj M)
  let z := L.extendXIso natEmbedding (embed_nat p)
  apply (cancel_mono z.hom).1
  rw [assoc, D.component p 0, extendMap_f _ _ (embed_nat p)]
  let := D.exactTerm p
  change _ = (x.hom ≫ G.map (F.toRightDerivedZero.app M) ≫ z.inv) ≫ z.hom
  simp only [assoc, Iso.inv_hom_id, comp_id, resolutionVerticalComponent, Iso.trans_hom]
  change a ≫ C.homologyπ 0 ≫ (homologyMapIso i 0).hom ≫
    (K.extendHomologyIso natEmbedding (embed_nat 0)).hom ≫
    (((underlyingComplex R I.cocomplex).sc 0).mapHomologyIso G).hom ≫
    G.map (I.isoRightDerivedObj F 0).inv =
      x.hom ≫ G.map (F.toRightDerivedZero.app M)
  rw [reassoc_of% hclass]
  exact congrArg (fun f => x.hom ≫ f) (mappedAugmentation_homology I F G b hb')

private def verticalAxisCycles {M : Modules R} (I : InjectiveResolution M) (p : ℤ) :
    (cechComplexInt R c M).X p ⟶ ((resolutionDoubleComplexInt R c M I).X p).cycles 0 :=
  ((resolutionDoubleComplexInt R c M I).X p).liftCycles
    ((verticalAxis R c I).f p) 1 (by simp) (vertical_cycle R c I p 1 (by simp))

private def verticalLocalMap {M : Modules R} (I : InjectiveResolution M)
    (D : ResolutionVerticalComparison R c M I) :
    cechComplexInt R c M ⟶
      DoubleComplexFirstPages.verticalHomology (resolutionDoubleComplexInt R c M I) 0 :=
  extendMap ((cochainFunctor R c).map
    ((SheafOfModules.forget R).toRightDerivedZero.app M)) natEmbedding ≫ (D.iso 0).inv

private lemma verticalLocalMap_f {M : Modules R} (I : InjectiveResolution M)
    (D : ResolutionVerticalComparison R c M I) (p : ℤ) :
    (verticalLocalMap R c I D).f p =
      verticalAxisCycles R c I p ≫ ((resolutionDoubleComplexInt R c M I).X p).homologyπ 0 := by
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    have : IsIso ((D.iso 0).hom.f (p : ℤ)) :=
      inferInstanceAs (IsIso ((eval _ _ (p : ℤ)).map (D.iso 0).hom))
    apply (cancel_mono ((D.iso 0).hom.f (p : ℤ))).1
    rw [verticalCoefficientComponent R c I D p _ (by simp only [verticalAxisCycles, liftCycles_i])]
    simp only [verticalLocalMap, assoc, ← comp_f, Iso.inv_hom_id, comp_id]
  · exact ((cechComplex R c M.val).isZero_extend_X natEmbedding p
      (not_mem_of_neg (lt_of_not_ge hp))).eq_of_src _ _

section
universe w z
private lemma singleAugmentation_homology {C : Type w} [Category.{z} C] [Abelian C]
    (K : CochainComplex C ℤ) (X : C) (a : X ⟶ K.X 0)
    (h : ∀ q, (ComplexShape.up ℤ).Rel 0 q → a ≫ K.d 0 q = 0) :
    (singleObjHomologySelfIso (.up ℤ) 0 X).inv ≫
      homologyMap (mkHomFromSingle (K := K) (j := 0) a h) 0 =
    K.liftCycles a 1 (by simp) (h 1 (by simp)) ≫ K.homologyπ 0 := by
  let f := mkHomFromSingle (K := K) (j := 0) a h
  change (singleObjHomologySelfIso (.up ℤ) 0 X).inv ≫ homologyMap f 0 = _
  rw [← singleObjCyclesSelfIso_inv_homologyπ, assoc, homologyπ_naturality]
  rw [← assoc]
  congr 1
  apply (cancel_mono (K.iCycles 0)).1
  simp only [cyclesMap_i, assoc, liftCycles_i, singleObjCyclesSelfIso_inv_iCycles_assoc,
    f, mkHomFromSingle_f, Iso.inv_hom_id_assoc]
end

private lemma vertical_degree_zero {M : Modules R} (I : InjectiveResolution M) (p : ℤ) :
    IsIso (homologyMap (mkHomFromSingle (K := (resolutionDoubleComplexInt R c M I).X p)
      (j := 0) ((verticalAxis R c I).f p) (vertical_cycle R c I p)) 0) := by
  let K := (resolutionDoubleComplexInt R c M I).X p
  let X := (cechComplexInt R c M).X p
  let Z := (single (SectionModule (U := U) R) (.up ℤ) 0).obj X
  let f : Z ⟶ K := mkHomFromSingle ((verticalAxis R c I).f p) (vertical_cycle R c I p)
  let D := resolutionVerticalComparison R c M I
  let g := verticalLocalMap R c I D
  let toLocal := (cochainFunctor R c).map ((SheafOfModules.forget R).toRightDerivedZero.app M)
  have : IsIso toLocal := inferInstance
  have : IsIso (extendMap toLocal natEmbedding) :=
    inferInstanceAs (IsIso ((natEmbedding.extendFunctor _).map toLocal))
  have : IsIso g := by
    change IsIso (extendMap toLocal natEmbedding ≫ (D.iso 0).inv)
    infer_instance
  have hg₀ : IsIso (g.f p) := inferInstanceAs (IsIso ((eval _ _ p).map g))
  have hh : (singleObjHomologySelfIso (.up ℤ) 0 X).inv ≫ homologyMap f 0 = g.f p := by
    rw [verticalLocalMap_f R c I D p]
    exact singleAugmentation_homology K X ((verticalAxis R c I).f p) (vertical_cycle R c I p)
  have : IsIso ((singleObjHomologySelfIso (.up ℤ) 0 X).inv ≫ homologyMap f 0) := by
    rw [hh]
    exact hg₀
  exact IsIso.of_isIso_comp_left ((singleObjHomologySelfIso (.up ℤ) 0 X).inv) (homologyMap f 0)

private lemma vertical_other {M : Modules R} (I : InjectiveResolution M)
    (hM : AcyclicOnIntersections R c M) (p q : ℤ) (hq : q ≠ 0) :
    IsZero (((resolutionDoubleComplexInt R c M I).X p).homology q) := by
  by_cases hp : 0 ≤ p
  · by_cases hq' : 0 ≤ q
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq'
      let F := eval (SectionModule (U := U) R) (.up ℤ) (p : ℤ)
      let K := cechComplex R c ((localCohomology R q).obj M)
      let e := F.mapIso (resolutionVerticalIntIso R c M I q) ≪≫
        K.extendXIso natEmbedding (embed_nat p)
      apply e.isZero_iff.2
      apply ModuleCat.isZero_iff_subsingleton.2
      have component (t : Fin (p + 1) → A) :
          Subsingleton (((localCohomology R q).obj M).obj (op (tupleOpen c t))) :=
        ModuleCat.isZero_iff_subsingleton.1
          (((localH01SectionsIso R (tupleOpen c t) q).app M).isZero_iff.2 (hM p t q (by omega)))
      change Subsingleton ((t : Fin (p + 1) → A) →
        ((localCohomology R q).obj M).obj (op (tupleOpen c t)))
      exact ⟨fun a b => funext fun t => (component t).elim (a t) (b t)⟩
    · exact isZero_homology_of_X _ _ (negative_entry R c I p q (Or.inr (lt_of_not_ge hq')))
  · exact isZero_homology_of_X _ _ (negative_entry R c I p q (Or.inl (lt_of_not_ge hp)))

private theorem vertical_assembly {M : Modules R} (I : InjectiveResolution M)
    (hM : AcyclicOnIntersections R c M) :
    ∃ v : cechComplexInt R c M ⟶ sumTotal (resolutionDoubleComplexInt R c M I),
      QuasiIso v ∧ ∀ n : ℤ, v.f n = (verticalAxis R c I).f n ≫
        sumInjection (resolutionDoubleComplexInt R c M I) n 0 n (add_zero n) :=
  AugmentedDoubleComplexComparison.cochain_column_assembly (resolutionDoubleComplexInt R c M I)
    (natToIntDoubleComplex_finiteDiagonals (resolutionDoubleComplex R c M I))
    (fun p q h => negative_entry R c I p q (Or.inr h))
    _ (verticalAxis R c I) (vertical_cycle R c I)
    (vertical_degree_zero R c I) (vertical_other R c I hM)

private def verticalMap {M : Modules R} (I : InjectiveResolution M) :
    cechComplexInt R c M ⟶ sumTotal (resolutionDoubleComplexInt R c M I) :=
  AugmentedDoubleComplexComparison.axisInclusion (cechComplexInt R c M) ≫
    HomologicalComplex₂.total.map
      (AugmentedDoubleComplexComparison.columnLift (resolutionDoubleComplexInt R c M I) _
        (verticalAxis R c I) (vertical_cycle R c I)) (.up ℤ)

private lemma verticalMap_f {M : Modules R} (I : InjectiveResolution M) (n : ℤ) :
    (verticalMap R c I).f n = (verticalAxis R c I).f n ≫
      sumInjection (resolutionDoubleComplexInt R c M I) n 0 n (add_zero n) := by
  simp [verticalMap, AugmentedDoubleComplexComparison.axisInclusion,
    AugmentedDoubleComplexComparison.columnLift, HomologicalComplex₂.ιTotal_map, assoc,
    mkHomFromSingle_f, sumInjection]

private abbrev totalMap {M N : Modules R} {I : InjectiveResolution M} {J : InjectiveResolution N}
    (φ : I.cocomplex ⟶ J.cocomplex) :=
  HomologicalComplex₂.total.map (resolutionDoubleComplexIntMap R c I J φ) (.up ℤ)

private lemma rowIso_naturality {B : Type*} [Category* B] [Abelian B]
    {K L : HomologicalComplex₂ B (.up ℕ) (.up ℕ)} (f : K ⟶ L) :
    ((HomologicalComplex₂.flipFunctor _ _ _).map (natToIntDoubleComplexMap f)).f 0 ≫
        (natToIntDoubleComplexRowIso L 0).hom =
      (natToIntDoubleComplexRowIso K 0).hom ≫
        extendMap (((HomologicalComplex₂.flipFunctor _ _ _).map f).f 0) natEmbedding := by
  let E := natEmbedding.extendFunctor B
  let F := eval B (.up ℤ) (0 : ℤ)
  let α := NatIso.mapHomologicalComplex (natEmbedding.extendFunctorCompEvalIso B (embed_nat 0)) (.up ℕ)
  simp only [natToIntDoubleComplexRowIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← assoc]
  change ((F.mapHomologicalComplex (.up ℤ)).map
    (extendMap ((E.mapHomologicalComplex (.up ℕ)).map f) natEmbedding) ≫ _) ≫ _ = _
  erw [mapExtendIso_naturality F ((E.mapHomologicalComplex (.up ℕ)).map f) natEmbedding,
    assoc]
  have h := congrArg E.map (α.hom.naturality f)
  simp only [Functor.map_comp] at h
  have hh := congrArg (fun g =>
    (mapExtendIso F ((E.mapHomologicalComplex (.up ℕ)).obj K) natEmbedding).hom ≫ g) h
  simp only [assoc] at hh ⊢
  convert hh using 1 <;> rfl

private lemma verticalAxis_naturality
    {M N : Modules R} (f : M ⟶ N) {I : InjectiveResolution M} {J : InjectiveResolution N}
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    cechComplexIntMap R c f ≫ verticalAxis R c J =
      verticalAxis R c I ≫
        ((HomologicalComplex₂.flipFunctor _ _ _).map (resolutionDoubleComplexIntMap R c I J φ)).f 0 := by
  apply (cancel_mono (natToIntDoubleComplexRowIso (resolutionDoubleComplex R c N J) 0).hom).1
  simp only [verticalAxis, assoc, Iso.inv_hom_id, comp_id]
  erw [rowIso_naturality (resolutionDoubleComplexMap R c I J φ), Iso.inv_hom_id_assoc,
    ← extendMap_comp, ← extendMap_comp]
  congr 1
  let F := SheafOfModules.forget R ⋙ cochainFunctor R c
  change F.map f ≫ F.map (J.ι.f 0) = F.map (I.ι.f 0) ≫ F.map (φ.f 0)
  rw [← F.map_comp, ← F.map_comp, comm]

private lemma verticalMap_naturality
    {M N : Modules R} (f : M ⟶ N) {I : InjectiveResolution M} {J : InjectiveResolution N}
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    cechComplexIntMap R c f ≫ verticalMap R c J =
      verticalMap R c I ≫ totalMap R c φ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [comp_f, verticalMap_f, assoc, totalMap, sumInjection, HomologicalComplex₂.ιTotal_map]
  simpa only [comp_f, assoc, HomologicalComplex₂.flipFunctor] using congrArg
    (fun g => g.f n ≫ (resolutionDoubleComplexInt R c N J).ιTotal (.up ℤ) n 0 n (add_zero n))
    (verticalAxis_naturality R c f φ comm)

private lemma sectionResolutionIso_eq (M : Modules R) (I : InjectiveResolution M) (n : ℕ) :
    sectionResolutionIso R c M I n = sectionComputationIso R c M I n := by
  simp only [sectionResolutionIso, sectionComputationIso, sectionCohomologyResolutionIso_eq]

private abbrev cechHomologyExtendIso (M : Modules R) (n : ℕ) :=
  (cechComplex R c M.val).extendHomologyIso natEmbedding
    (j := n) (j' := (n : ℤ)) (embed_nat n)

private def comparisonAt {M : Modules R} (I : InjectiveResolution M) (n : ℕ) :
    (cechCohomology R c n).obj M ⟶ (liftedSectionCohomology R c n).obj M :=
  (cechHomologyExtendIso R c M n).inv ≫ homologyMap (verticalMap R c I) (n : ℤ) ≫
    inv (homologyMap (resolutionTotalAugmentation R c M I) (n : ℤ)) ≫
    (sectionResolutionIso R c M I n).inv

private lemma comparisonAt_comm {M : Modules R} (I : InjectiveResolution M) (n : ℕ) :
    comparisonAt R c I n ≫ (sectionResolutionIso R c M I n).hom ≫
      homologyMap (resolutionTotalAugmentation R c M I) (n : ℤ) =
    (cechHomologyExtendIso R c M n).inv ≫ homologyMap (verticalMap R c I) (n : ℤ) := by
  simp [comparisonAt]

private lemma cechHomologyExtendIso_naturality {M N : Modules R} (f : M ⟶ N) (n : ℕ) :
    (cechCohomology R c n).map f ≫ (cechHomologyExtendIso R c N n).inv =
      (cechHomologyExtendIso R c M n).inv ≫ homologyMap
        (cechComplexIntMap R c f) (n : ℤ) := by
  apply (cancel_mono (cechHomologyExtendIso R c N n).hom).1
  simp only [assoc, Iso.inv_hom_id, comp_id]
  let g := (cochainFunctor R c).map ((SheafOfModules.forget R).map f)
  change homologyMap g n = (cechHomologyExtendIso R c M n).inv ≫
    homologyMap (extendMap g natEmbedding) (n : ℤ) ≫ (cechHomologyExtendIso R c N n).hom
  have h : homologyMap (extendMap g natEmbedding) (n : ℤ) ≫
      (cechHomologyExtendIso R c N n).hom =
      (cechHomologyExtendIso R c M n).hom ≫ homologyMap g n :=
    extendHomologyIso_hom_naturality g natEmbedding (embed_nat n)
  rw [h, Iso.inv_hom_id_assoc]


private lemma comparisonAt_naturality
    {M N : Modules R} (f : M ⟶ N) {I : InjectiveResolution M} {J : InjectiveResolution N}
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    (cechCohomology R c n).map f ≫ comparisonAt R c J n =
      comparisonAt R c I n ≫ (liftedSectionCohomology R c n).map f := by
  have hh : homologyMap (sectionComplexIntMap R c I J φ) (n : ℤ) ≫
      homologyMap (resolutionTotalAugmentation R c N J) (n : ℤ) =
      homologyMap (resolutionTotalAugmentation R c M I) (n : ℤ) ≫ homologyMap (totalMap R c φ) (n : ℤ) := by
    simpa only [homologyMap_comp] using
      congrArg (fun k => homologyMap k (n : ℤ)) (resolutionTotalAugmentation_naturality R c I J φ)
  have hv : homologyMap (cechComplexIntMap R c f) (n : ℤ) ≫
      homologyMap (verticalMap R c J) (n : ℤ) =
      homologyMap (verticalMap R c I) (n : ℤ) ≫ homologyMap (totalMap R c φ) (n : ℤ) := by
    simpa only [homologyMap_comp] using
      congrArg (fun k => homologyMap k (n : ℤ)) (verticalMap_naturality R c f φ comm)
  apply (cancel_mono ((sectionResolutionIso R c N J n).hom ≫
    homologyMap (resolutionTotalAugmentation R c N J) (n : ℤ))).1
  simp only [assoc, comparisonAt_comm]
  erw [reassoc_of% (cechHomologyExtendIso_naturality R c f n), hv,
    sectionResolutionIso_eq,
    reassoc_of% (sectionComputationIso_naturality R c M N f I J φ comm n), hh]
  simpa only [assoc, sectionResolutionIso_eq] using congrArg
    (fun k => k ≫ homologyMap (totalMap R c φ) (n : ℤ))
    (comparisonAt_comm R c I n).symm

private lemma comparisonAt_independent {M : Modules R} (I J : InjectiveResolution M) (n : ℕ) :
    comparisonAt R c I n = comparisonAt R c J n := by
  simpa using (comparisonAt_naturality R c (𝟙 M) (InjectiveResolution.desc (𝟙 M) J I)
    (InjectiveResolution.desc_commutes_zero (𝟙 M) J I) n).symm

private lemma comparisonAt_isIso
    {M : Modules R} (I : InjectiveResolution M) (hM : AcyclicOnIntersections R c M) (n : ℕ) :
    IsIso (comparisonAt R c I n) := by
  obtain ⟨v, hv, hf⟩ := vertical_assembly R c I hM
  have hEq : verticalMap R c I = v :=
    HomologicalComplex.hom_ext _ _ fun i => (verticalMap_f R c I i).trans (hf i).symm
  have : QuasiIso (verticalMap R c I) := hEq ▸ hv
  have : IsIso (homologyMap (verticalMap R c I) (n : ℤ)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  unfold comparisonAt
  infer_instance

private lemma spectralAbutment_hom
    (S : CechSpectralSequence R c) (M : Modules R) (I : InjectiveResolution M) (n : ℕ) :
    (S.abutment M I n).hom =
      inv (homologyMap (resolutionTotalAugmentation R c M I) (n : ℤ)) ≫
        (sectionResolutionIso R c M I n).inv := by
  have h : S.totalAugmentation M I = resolutionTotalAugmentation R c M I := by
    apply HomologicalComplex.hom_ext
    intro i
    rw [S.totalAugmentation_f, resolutionTotalAugmentation_f]
  apply (cancel_epi (homologyMap (resolutionTotalAugmentation R c M I) (n : ℤ))).1
  rw [IsIso.hom_inv_id_assoc]
  rw [← h, S.abutment_agrees, S.sectionResolution_eq]
  simp only [sectionResolutionIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]

private lemma edge_comparisonAt
    (S : CechSpectralSequence R c) {M : Modules R} (I : InjectiveResolution M)
    (E : EdgesAndFiveTerms.EdgeData (S.data M I).filtration (S.data M I).pages) (n : ℕ)
    (verticalClassMap : cechComplexInt R c M ⟶
      DoubleComplexFirstPages.verticalHomology (resolutionDoubleComplexInt R c M I) 0)
    (hLocal : verticalClassMap ≫ ((S.vertical M I).iso 0).hom = extendMap
      ((cochainFunctor R c).map ((SheafOfModules.forget R).toRightDerivedZero.app M))
        natEmbedding)
    (hedge : let D := S.data M I
      homologyMap verticalClassMap (n : ℤ) ≫ (D.firstPages.secondIso (n : ℤ) 0).inv ≫
        eqToHom (congrArg (PageCohomology.object D.filtration D.pages 2 (n : ℤ)) (add_zero _)) ≫
        E.row (n : ℤ) (by omega) = homologyMap (verticalMap R c I) (n : ℤ)) :
    let D := S.data M I
    let toLocal := (cochainFunctor R c).map ((SheafOfModules.forget R).toRightDerivedZero.app M)
    homologyMap toLocal n ≫ (S.second M I n 0).inv ≫
      eqToHom (congrArg (PageCohomology.object D.filtration D.pages 2 (n : ℤ)) (add_zero _)) ≫
      E.row (n : ℤ) (by omega) ≫ (S.abutment M I n).hom = comparisonAt R c I n := by
  let g := (cochainFunctor R c).map ((SheafOfModules.forget R).toRightDerivedZero.app M)
  let e := (cechComplex R c ((localCohomology R 0).obj M)).extendHomologyIso
    natEmbedding (j := n) (j' := (n : ℤ)) (embed_nat n)
  have hg : homologyMap g n ≫ e.inv =
      (cechHomologyExtendIso R c M n).inv ≫ homologyMap (extendMap g natEmbedding) (n : ℤ) := by
    apply (cancel_mono e.hom).1
    have h : homologyMap (extendMap g natEmbedding) (n : ℤ) ≫ e.hom =
        (cechHomologyExtendIso R c M n).hom ≫ homologyMap g n :=
      extendHomologyIso_hom_naturality g natEmbedding (embed_nat n)
    rw [assoc, Iso.inv_hom_id, comp_id, assoc, h, Iso.inv_hom_id_assoc]
  have hLocal' : homologyMap (extendMap g natEmbedding) (n : ℤ) =
      homologyMap verticalClassMap (n : ℤ) ≫
        (homologyMapIso ((S.vertical M I).iso 0) (n : ℤ)).hom := by
    rw [← hLocal, homologyMap_comp, homologyMapIso_hom]
  dsimp only
  rw [S.second_eq, Iso.trans_inv, Iso.trans_inv]
  simp only [assoc]
  change homologyMap g n ≫ e.inv ≫ _ = comparisonAt R c I n
  rw [← assoc, hg, hLocal']
  simp only [assoc, Iso.hom_inv_id_assoc]
  have hpost := congrArg (fun k => (cechHomologyExtendIso R c M n).inv ≫ k ≫
    (S.abutment M I n).hom) hedge
  simp only [assoc] at hpost
  simp only [Int.natCast_zero]
  erw [hpost, spectralAbutment_hom, comparisonAt]

/-- HA-H04, via the two augmentations of the Čech-resolution double complex. -/
theorem acyclic_cover_comparison :
    Specs.AdvancedHomologicalAlgebra.AcyclicCoverComparison.acyclicCoverComparison.{u, v} := by
  intro X R U A c
  let η (n : ℕ) : cechCohomology R c n ⟶ liftedSectionCohomology R c n :=
    { app M := comparisonAt R c (injectiveResolution M) n
      naturality {M N} f := comparisonAt_naturality R c f
        (InjectiveResolution.desc f (injectiveResolution N) (injectiveResolution M))
        (InjectiveResolution.desc_commutes_zero f (injectiveResolution N) (injectiveResolution M)) n }
  refine ⟨η, ?_, ?_, ?_⟩
  · intro M n hM
    exact comparisonAt_isIso R c (injectiveResolution M) hM n
  · intro S M I E n
    change _ = comparisonAt R c (injectiveResolution M) n
    rw [comparisonAt_independent R c (injectiveResolution M) I n]
    let V := S.vertical M I
    refine edge_comparisonAt R c S I E n (verticalLocalMap R c I V) ?_ ?_
    · simp only [verticalLocalMap, V, assoc, Iso.inv_hom_id, comp_id]
    · exact row_edge_augmentation (S.data M I).firstPages E (verticalMap R c I)
        (verticalLocalMap R c I V) (verticalAxis R c I).f
        (fun p => vertical_cycle R c I p 1 (by simp)) (verticalMap_f R c I)
        (verticalLocalMap_f R c I V) (n : ℤ) (by omega)
  · intro M I
    refine ⟨verticalMap R c I, resolutionTotalAugmentation R c M I, ?_,
      resolutionTotalAugmentation_f R c M I, inferInstance, ?_⟩
    · intro p
      rw [verticalMap_f, verticalAxis_f, assoc, assoc]
    · intro n
      change comparisonAt R c (injectiveResolution M) n ≫ _ = _
      rw [comparisonAt_independent R c (injectiveResolution M) I n]
      exact comparisonAt_comm R c I n

end AdvancedHomologicalAlgebra.AcyclicCoverComparison
