import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.IntervalProjectionPullback
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.ShrinkingLemma
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Set Topology Filter
open TopCat.Presheaf
open scoped ZeroObject

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 900000

namespace RepTheorySurvey.Geometric.IntervalProjectionPullback

open Analytic LocalSheaf
open private sectionGerms from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage

/-- The restriction obtained by evaluating the inverse-image unit on an open set. -/
private def pullSection {Y K : TopCat.{0}} (f : K ⟶ Y) (F : Sheaves Y) (W : Opens Y) :
    F.obj.obj (op W) ⟶ ((inverseImage f).obj F).obj.obj (op ((Opens.map f).obj W)) :=
  ((inverseDirectAdjunction f).unit.app F).hom.app (op W)

private theorem pullSection_germ {Y K : TopCat.{0}} (f : K ⟶ Y) (F : Sheaves Y)
    (W : Opens Y) (s : F.obj.obj (op W)) (k : K) (hk : f k ∈ W) :
    germ ((inverseImage f).obj F).obj ((Opens.map f).obj W) k hk (pullSection f F W s) =
      inverseImageStalkMap f F k (germ F.obj W (f k) hk s) := by
  unfold inverseImageStalkMap
  rw [ConcreteCategory.comp_apply]
  change _ = (stalkPushforward Coeff f ((inverseImage f).obj F).obj k)
    (((stalkFunctor Coeff (f k)).map ((inverseDirectAdjunction f).unit.app F).hom)
      (germ F.obj W (f k) hk s))
  erw [stalkFunctor_map_germ_apply, stalkPushforward_germ_apply]
  rfl

private theorem etale_eq_germ {Y : TopCat.{0}} {F : Sheaves Y} (p : EtaleSpace F.obj)
    {V : Opens Y} (s : F.obj.obj (op V)) {y : Y} (e : p.base = y)
    (h : p.base ∈ V) (ht : p.germ = germ F.obj V p.base h s) :
    p = sectionGerms F V s ⟨y, e ▸ h⟩ := by
  cases p with
  | mk b t =>
    dsimp at e ht
    subst y
    exact congrArg (EtaleSpace.mk b) ht

/-- A continuous family of germs based at points of an open set is represented by a section. -/
private theorem section_of_continuous_germs {Y : TopCat.{0}} (F : Sheaves Y) (W : Opens Y)
    (g : C(W, EtaleSpace F.obj)) (hg : ∀ y, (g y).base = y.val) :
    ∃ s : F.obj.obj (op W), ∀ y : W, g y = sectionGerms F W s y := by
  classical
  have localRep (y : W) : ∃ (V : Opens Y), y.val ∈ V ∧ ∃ hVW : V ≤ W,
      ∃ s : F.obj.obj (op V), ∀ (z : V),
        g ⟨z.val, hVW z.property⟩ = sectionGerms F V s z := by
    obtain ⟨V, _, s, hs⟩ := EtaleSpace.exists_section_of_tendsto
      g.continuous.continuousAt (g₀ := g y)
    obtain ⟨N, hN, hNo, hyN⟩ := mem_nhds_iff.mp hs
    have hm := W.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hNo
    let V' : Opens Y := ⟨Subtype.val '' N, hm⟩
    have hVW : V' ≤ W := fun _ ⟨z, _, hz⟩ => hz ▸ z.property
    have hVV : V' ≤ V := fun _ ⟨z, hz, e⟩ => e ▸ hg z ▸ (hN hz).1
    let i : V' ⟶ V := homOfLE hVV
    refine ⟨V', ⟨y, hyN, rfl⟩, hVW, F.obj.map i.op s, ?_⟩
    rintro ⟨z, a, ha, rfl⟩
    obtain ⟨h, ht⟩ := hN ha
    have e := etale_eq_germ (g a) s (hg a) h ht
    rw [e]
    exact congrArg (EtaleSpace.mk a.val) (germ_res_apply _ i _ _ _).symm
  choose V hyV hVW s hs using localRep
  let i (y : W) : V y ⟶ W := homOfLE (hVW y)
  have hc : W ≤ iSup V := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩
  have comp : TopCat.Presheaf.IsCompatible F.obj V s := by
    intro x y
    apply section_ext
    intro z hz
    have hx : z ∈ V x := (show V x ⊓ V y ≤ V x from inf_le_left) hz
    have hy : z ∈ V y := (show V x ⊓ V y ≤ V y from inf_le_right) hz
    have e := (hs x ⟨z, hx⟩).symm.trans (hs y ⟨z, hy⟩)
    change EtaleSpace.mk z (germ F.obj (V x) z hx (s x)) =
      EtaleSpace.mk z (germ F.obj (V y) z hy (s y)) at e
    rw [germ_res_apply, germ_res_apply]
    injection e
  obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' V W i hc s comp
  refine ⟨t, fun y => (hs y ⟨y.val, hyV y⟩).trans ?_⟩
  change EtaleSpace.mk y.val (germ F.obj (V y) y.val (hyV y) (s y)) =
    EtaleSpace.mk y.val (germ F.obj W y.val y.property t)
  rw [← ht, germ_res_apply]

/-- A locally finite closed cover can be used to extend sections defined near a
subset, after deleting the closed loci where the local representatives fail to glue. -/
private theorem glue_near_closed_cover {Z E ι : Type} [TopologicalSpace Z]
    [TopologicalSpace E] (C : ι → Set Z) (hC : LocallyFinite C)
    (hclosed : ∀ i, IsClosed (C i)) (hcover : ∀ z, ∃ i, z ∈ C i)
    (D : ι → Opens Z) (g : ∀ i, C(D i, E))
    (A : ι → ι → Opens Z)
    (hA₁ : ∀ i j, A i j ≤ D i) (hA₂ : ∀ i j, A i j ≤ D j)
    (hAgree : ∀ i j z (hz : z ∈ A i j),
      g i ⟨z, hA₁ i j hz⟩ = g j ⟨z, hA₂ i j hz⟩) :
    ∃ W : Opens Z, (∀ z, (∀ i, z ∈ C i → z ∈ D i) →
      (∀ i j, z ∈ C i → z ∈ C j → z ∈ A i j) → z ∈ W) ∧
      ∃ t : C(W, E), ∀ (z : W) i, z.val ∈ C i →
        ∃ h : z.val ∈ D i, t z = g i ⟨z.val, h⟩ := by
  classical
  let B₁ (i : ι) : Set Z := C i \ D i
  let B₂ (a : ι × ι) : Set Z := (C a.1 ∩ C a.2) \ A a.1 a.2
  have hB₁ : IsClosed (⋃ i, B₁ i) :=
    (hC.subset fun _ => sdiff_subset).isClosed_iUnion fun i =>
      (hclosed i).sdiff (D i).isOpen
  have hB₂' : LocallyFinite B₂ := by
    intro z
    obtain ⟨N, hzN, hN⟩ := hC z
    refine ⟨N, hzN, (hN.prod hN).subset ?_⟩
    rintro ⟨i, j⟩ ⟨w, hw, hwN⟩
    exact ⟨⟨w, hw.1.1, hwN⟩, ⟨w, hw.1.2, hwN⟩⟩
  have hB₂ : IsClosed (⋃ a, B₂ a) := hB₂'.isClosed_iUnion fun ⟨i, j⟩ =>
    ((hclosed i).inter (hclosed j)).sdiff (A i j).isOpen
  let W : Opens Z := ⟨((⋃ i, B₁ i) ∪ (⋃ a, B₂ a))ᶜ,
    (hB₁.union hB₂).isOpen_compl⟩
  have hD (z : W) (i : ι) (hz : z.val ∈ C i) : z.val ∈ D i := by
    by_contra hn
    exact z.property (Or.inl (mem_iUnion.mpr ⟨i, hz, hn⟩))
  have hEq (z : W) (i j : ι) (hi : z.val ∈ C i) (hj : z.val ∈ C j) :
      g i ⟨z.val, hD z i hi⟩ = g j ⟨z.val, hD z j hj⟩ := by
    have hz : z.val ∈ A i j := by
      by_contra hn
      exact z.property (Or.inr (mem_iUnion.mpr ⟨(i, j), ⟨hi, hj⟩, hn⟩))
    exact hAgree i j z.val hz
  let idx (z : W) := (hcover z.val).choose
  let ht (z : W) : z.val ∈ C (idx z) := (hcover z.val).choose_spec
  let t (z : W) := g (idx z) ⟨z.val, hD z (idx z) (ht z)⟩
  have eq (z : W) (i : ι) (hz : z.val ∈ C i) :
      t z = g i ⟨z.val, hD z i hz⟩ := hEq z (idx z) i (ht z) hz
  let C' (i : ι) : Set W := Subtype.val ⁻¹' C i
  have hc' : (⋃ i, C' i) = univ :=
    iUnion_eq_univ_iff.mpr fun z => hcover z.val
  refine ⟨W, ?_, ⟨t, ?_⟩, fun z i hz => ⟨hD z i hz, eq z i hz⟩⟩
  · intro z hd ha hz
    rcases hz with hz | hz
    · obtain ⟨i, hi, hni⟩ := mem_iUnion.mp hz
      exact hni (hd i hi)
    · obtain ⟨⟨i, j⟩, hij, hnij⟩ := mem_iUnion.mp hz
      exact hnij (ha i j hij.1 hij.2)
  · apply (hC.preimage_continuous continuous_subtype_val).continuous hc'
      (fun i => (hclosed i).preimage continuous_subtype_val)
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    let f : C' i → D i := fun z => ⟨z.val.val, hD z.val i z.property⟩
    have hf : Continuous f :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (g i).continuous.comp hf |>.congr fun z => (eq z.val i z.property).symm

private def firstProjection (K X : TopCat.{0}) : TopCat.of (K × X) ⟶ K :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

private def secondProjection (K X : TopCat.{0}) : TopCat.of (K × X) ⟶ X :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

private def fiberInclusion (K : TopCat.{0}) {X : TopCat.{0}} (x : X) :
    K ⟶ TopCat.of (K × X) :=
  TopCat.ofHom ⟨fun k => (k, x), continuous_id.prodMk continuous_const⟩

/-- The locus where the germs of two local sections agree is open. -/
private def agreementOpen {Y : TopCat.{0}} (F : Sheaves Y) {U V : Opens Y}
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V)) : Opens Y :=
  ⟨{y | ∃ (hu : y ∈ U) (hv : y ∈ V), germ F.obj U y hu s = germ F.obj V y hv t}, by
    apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨hu, hv, he⟩
    obtain ⟨O, hyO, iu, iv, hO⟩ := germ_eq F.obj y hu hv s t he
    filter_upwards [O.isOpen.mem_nhds hyO] with z hz
    exact ⟨iu.le hz, iv.le hz, germ_ext F.obj O hz iu iv hO⟩⟩

/-- Every section on a paracompact normal open part of a fiber lifts to a
section on an ambient open neighborhood of that part of the fiber. -/
private theorem lift_fiber_section {K X : TopCat.{0}}
    (x : X) (F : Sheaves (TopCat.of (K × X))) (U : Opens K)
    [ParacompactSpace U] [NormalSpace U]
    (s : ((inverseImage (fiberInclusion K x)).obj F).obj.obj (op U)) :
    ∃ (W : Opens (TopCat.of (K × X))) (t : F.obj.obj (op W)),
      ∀ k (hk : k ∈ U), ∃ hw : (k, x) ∈ W,
        germ ((inverseImage (fiberInclusion K x)).obj F).obj U k hk s =
          inverseImageStalkMap (fiberInclusion K x) F k
            (germ F.obj W (k, x) hw t) := by
  classical
  let f := fiberInclusion K x
  let G := (inverseImage f).obj F
  let A := TopCat.of (K × X)
  let D : Opens A := (Opens.map (firstProjection K X)).obj U
  let r : D → U := fun z => ⟨z.val.1, z.property⟩
  have hr : Continuous r := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have rep (a : U) : ∃ (V : Opens (TopCat.of U)), a ∈ V ∧
      ∃ (W : Opens A) (t : F.obj.obj (op W)), ∀ b : U, b ∈ V →
        ∃ h : f b.val ∈ W, germ G.obj U b.val b.property s =
          inverseImageStalkMap f F b.val (germ F.obj W (f b.val) h t) := by
    let e := inverseImageStalkIso f F a.val
    obtain ⟨W, hw, t, ht⟩ := exists_germ_eq F.obj
      (e.inv (germ G.obj U a.val a.property s))
    have he : germ G.obj U a.val a.property s =
        germ G.obj ((Opens.map f).obj W) a.val hw (pullSection f F W t) := by
      rw [pullSection_germ, ht]
      exact (ConcreteCategory.congr_hom e.inv_hom_id _).symm
    obtain ⟨V, ha, i, j, hV⟩ := germ_eq G.obj a.val a.property hw s
      (pullSection f F W t) he
    refine ⟨⟨Subtype.val ⁻¹' V, V.isOpen.preimage continuous_subtype_val⟩,
      ha, W, t, fun b hb => ⟨j.le hb, ?_⟩⟩
    rw [← pullSection_germ]
    exact germ_ext G.obj V hb i j hV
  choose V hv W t hrep using rep
  have hcov : (⋃ a, (V a : Set U)) = univ := iUnion_eq_univ_iff.mpr fun a => ⟨a, hv a⟩
  obtain ⟨V', hVo, hcov', hVf, hVsub⟩ :=
    precise_refinement (fun a => (V a : Set U)) (fun a => (V a).isOpen) hcov
  obtain ⟨O, hOc, _, hOs⟩ := exists_iUnion_eq_closure_subset hVo
    (fun b => hVf.point_finite b) hcov'
  let C (i : U) : Set D := r ⁻¹' closure (O i)
  have hCf : LocallyFinite C :=
    (hVf.subset fun i => subset_closure.trans (hOs i)).closure.preimage_continuous hr
  have hCc : ∀ i, IsClosed (C i) := fun _ => isClosed_closure.preimage hr
  have hCc' (z : D) : ∃ i, z ∈ C i := by
    have h : r z ∈ ⋃ i, O i := hOc.symm ▸ mem_univ _
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    exact ⟨i, subset_closure hi⟩
  let D' (i : U) : Opens (TopCat.of D) :=
    ⟨Subtype.val ⁻¹' W i, (W i).isOpen.preimage continuous_subtype_val⟩
  let g (i : U) : C(D' i, EtaleSpace F.obj) :=
    (sectionGerms F (W i) (t i)).comp
      ⟨fun z => ⟨z.val.val, z.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let B (i j : U) := agreementOpen F (t i) (t j)
  let B' (i j : U) : Opens (TopCat.of D) :=
    ⟨Subtype.val ⁻¹' B i j, (B i j).isOpen.preimage continuous_subtype_val⟩
  have hB₁ (i j : U) : B' i j ≤ D' i := fun _ h => h.1
  have hB₂ (i j : U) : B' i j ≤ D' j := fun _ h => h.2.1
  have hAgree (i j : U) (z : D) (hz : z ∈ B' i j) :
      g i ⟨z, hB₁ i j hz⟩ = g j ⟨z, hB₂ i j hz⟩ :=
    congrArg (EtaleSpace.mk z.val) hz.2.2
  obtain ⟨N, hN, v, hvN⟩ := glue_near_closed_cover C hCf hCc hCc' D' g B' hB₁ hB₂ hAgree
  have hfN (b : U) : (⟨f b.val, b.property⟩ : D) ∈ N := by
    let z : D := ⟨f b.val, b.property⟩
    have hrep' (i : U) (hi : z ∈ C i) :
        ∃ hw : f b.val ∈ W i, germ G.obj U b.val b.property s =
          inverseImageStalkMap f F b.val (germ F.obj (W i) (f b.val) hw (t i)) :=
      hrep i b (hVsub i (hOs i hi))
    apply hN
    · exact fun i hi => (hrep' i hi).choose
    · intro i j hi hj
      obtain ⟨hi', ei⟩ := hrep' i hi
      obtain ⟨hj', ej⟩ := hrep' j hj
      exact ⟨hi', hj', (((ConcreteCategory.isIso_iff_bijective (inverseImageStalkMap f F b.val)).mp inferInstance).injective)
        (ei.symm.trans ej)⟩
  let P : Opens A := ⟨Subtype.val '' (N : Set D),
    D.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ N.isOpen⟩
  have hPD : P ≤ D := fun _ ⟨z, _, hz⟩ => hz ▸ z.property
  let kN : P → N := fun p => ⟨⟨p.val, hPD p.property⟩, by
    obtain ⟨z, hz, e⟩ := p.property
    have he : (⟨p.val, hPD p.property⟩ : D) = z := Subtype.ext e.symm
    exact he.symm ▸ hz⟩
  have hkN : Continuous kN := (continuous_subtype_val.subtype_mk _).subtype_mk _
  let v' := v.comp ⟨kN, hkN⟩
  have hbase (p : P) : (v' p).base = p.val := by
    obtain ⟨i, hi⟩ := hCc' (kN p).val
    obtain ⟨_, e⟩ := hvN (kN p) i hi
    exact congrArg EtaleSpace.base e
  obtain ⟨a, ha⟩ := section_of_continuous_germs F P v' hbase
  refine ⟨P, a, fun k hk => ⟨⟨⟨f k, hk⟩, hfN ⟨k, hk⟩, rfl⟩, ?_⟩⟩
  let q : P := ⟨f k, ⟨⟨f k, hk⟩, hfN ⟨k, hk⟩, rfl⟩⟩
  obtain ⟨i, hi⟩ := hCc' (kN q).val
  obtain ⟨hw, hg⟩ := hvN (kN q) i hi
  obtain ⟨hw', hs⟩ := hrep i ⟨k, hk⟩ (hVsub i (hOs i hi))
  rw [hs]
  have hg' := hg.symm.trans (ha q)
  change EtaleSpace.mk (f k) (germ F.obj (W i) (f k) hw (t i)) =
    EtaleSpace.mk (f k) (germ F.obj P (f k) q.property a) at hg'
  congr 1
  injection hg'

/-- Restriction to a fiber preserves flasqueness when its open sets are paracompact
and normal. The base is arbitrary. -/
private theorem fiber_flasque {K X : TopCat.{0}} (x : X)
    (hK : ∀ U : Opens K, ParacompactSpace U ∧ NormalSpace U)
    (F : Sheaves (TopCat.of (K × X))) [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque ((inverseImage (fiberInclusion K x)).obj F) := by
  let f := fiberInclusion K x
  let G := (inverseImage f).obj F
  have htop (U : Opens K) : Function.Surjective (G.obj.map (homOfLE (le_top : U ≤ ⊤)).op) := by
    intro s
    haveI := (hK U).1
    haveI := (hK U).2
    obtain ⟨W, t, ht⟩ := lift_fiber_section x F U s
    obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective
      (F.obj.map (homOfLE (le_top : W ≤ ⊤)).op)).mp inferInstance t
    let b := pullSection f F ⊤ a
    have htop' : (⊤ : Opens K) ≤ (Opens.map f).obj ⊤ := fun _ _ => trivial
    refine ⟨G.obj.map (homOfLE htop').op b, ?_⟩
    apply section_ext G U
    intro k hk
    obtain ⟨hw, h⟩ := ht k hk
    rw [germ_res_apply, germ_res_apply]
    change germ G.obj ((Opens.map f).obj ⊤) k trivial (pullSection f F ⊤ a) = _
    rw [pullSection_germ, h, ← ha, germ_res_apply]
    rfl
  constructor
  intro U V j
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro s
  obtain ⟨a, ha⟩ := htop V.unop s
  refine ⟨G.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op a, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp]
  exact ha

private def fiberRestriction {K X : TopCat.{0}} (x : X)
    (F : Sheaves (TopCat.of (K × X))) (U : Opens X) (hx : x ∈ U) :
    ((directImage (secondProjection K X)).obj F).obj.obj (op U) ⟶
      (globalSections K).obj ((inverseImage (fiberInclusion K x)).obj F) :=
  let W := (Opens.map (secondProjection K X)).obj U
  let f := fiberInclusion K x
  pullSection f F W ≫ ((inverseImage f).obj F).obj.map
    (homOfLE (show (⊤ : Opens K) ≤ (Opens.map f).obj W from fun _ _ => hx)).op

private theorem fiberRestriction_germ {K X : TopCat.{0}} (x : X)
    (F : Sheaves (TopCat.of (K × X))) (U : Opens X) (hx : x ∈ U)
    (s : ((directImage (secondProjection K X)).obj F).obj.obj (op U)) (k : K) :
    germ ((inverseImage (fiberInclusion K x)).obj F).obj ⊤ k trivial
        (fiberRestriction x F U hx s) =
      inverseImageStalkMap (fiberInclusion K x) F k
        (germ F.obj ((Opens.map (secondProjection K X)).obj U) (k, x) hx s) := by
  unfold fiberRestriction
  rw [ConcreteCategory.comp_apply]
  erw [germ_res_apply, pullSection_germ]
  rfl

private theorem fiberRestriction_compatible {K X : TopCat.{0}} (x : X)
    (F : Sheaves (TopCat.of (K × X))) (U V : OpenNhds x) (i : U ⟶ V) :
    ((directImage (secondProjection K X)).obj F).obj.map
      ((OpenNhds.inclusion x).map i).op ≫ fiberRestriction x F U.1 U.2 =
      fiberRestriction x F V.1 V.2 := by
  apply ConcreteCategory.hom_ext
  intro s
  apply section_ext
  intro k _
  rw [ConcreteCategory.comp_apply]
  erw [fiberRestriction_germ, fiberRestriction_germ]
  congr 1
  exact germ_res_apply F.obj ((Opens.map (secondProjection K X)).map
    ((OpenNhds.inclusion x).map i)) (k, x) U.2 s

private def fiberCocone {K X : TopCat.{0}} (x : X)
    (F : Sheaves (TopCat.of (K × X))) :
    Cocone ((OpenNhds.inclusion x).op ⋙ ((directImage (secondProjection K X)).obj F).obj) :=
  ⟨_, {
    app := fun U => fiberRestriction x F U.unop.1 U.unop.2
    naturality := fun U V i => by
      have h := fiberRestriction_compatible x F V.unop U.unop i.unop
      exact h.trans (Category.comp_id _).symm }⟩

@[reassoc]
private theorem fiberDesc_germ {K X : TopCat.{0}} (x : X)
    (F : Sheaves (TopCat.of (K × X))) (U : Opens X) (hx : x ∈ U) :
    germ ((directImage (secondProjection K X)).obj F).obj U x hx ≫
      colimit.desc _ (fiberCocone x F) = fiberRestriction x F U hx :=
  colimit.ι_desc (fiberCocone x F) (op ⟨U, hx⟩)

/-- The degree-zero base-change map from a direct-image stalk to sections on the fiber. -/
private def fiberComparison {K X : TopCat.{0}} (x : X) :
    directImage (secondProjection K X) ⋙ stalk x ⟶
      inverseImage (fiberInclusion K x) ⋙ globalSections K where
  app F := colimit.desc _ (fiberCocone x F)
  naturality {F G} f := by
    let p := secondProjection K X
    let i := fiberInclusion K x
    apply stalk_hom_ext ((directImage p).obj F).obj
    intro U hx
    change _ ≫ ((stalkFunctor Coeff x).map ((directImage p).map f).hom ≫ _) = _
    rw [stalkFunctor_map_germ_assoc]
    erw [fiberDesc_germ, fiberDesc_germ_assoc]
    let W := (Opens.map p).obj U
    let j : (⊤ : Opens K) ⟶ (Opens.map i).obj W := homOfLE fun _ _ => hx
    let a := inverseDirectAdjunction i
    have h₁ := congrArg (fun v => v.hom.app (op W)) (a.unit.naturality f)
    have h₂ := ((inverseImage i).map f).hom.naturality j.op
    change f.hom.app (op W) ≫ (pullSection i G W ≫ ((inverseImage i).obj G).obj.map j.op) =
      (pullSection i F W ≫ ((inverseImage i).obj F).obj.map j.op) ≫
        ((inverseImage i).map f).hom.app (op ⊤)
    rw [Category.assoc, h₂, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun t => t ≫ ((inverseImage i).obj G).obj.map j.op) h₁

private theorem fiberComparison_germ {K X : TopCat.{0}} (x : X)
    (F : Sheaves (TopCat.of (K × X))) (U : Opens X) (hx : x ∈ U) :
    germ ((directImage (secondProjection K X)).obj F).obj U x hx ≫
      (fiberComparison (K := K) x).app F = fiberRestriction x F U hx :=
  fiberDesc_germ x F U hx

/-- Compactness supplies one base neighborhood for the entire fiber. -/
private theorem exists_tube {K X : TopCat.{0}} [CompactSpace K] (x : X)
    (W : Opens (TopCat.of (K × X))) (hW : ∀ k : K, (k, x) ∈ W) :
    ∃ V : Opens X, x ∈ V ∧ (Opens.map (secondProjection K X)).obj V ≤ W := by
  obtain ⟨_, V, _, hV, h₁, h₂, h₃⟩ :=
    generalized_tube_lemma (isCompact_univ (X := K)) (isCompact_singleton (x := x))
      W.isOpen (by
        rintro ⟨k, y⟩ ⟨_, hy⟩
        change y ∈ ({x} : Set X) at hy
        exact (mem_singleton_iff.mp hy).symm ▸ hW k)
  exact ⟨⟨V, hV⟩, h₂ rfl, fun z hz => h₃ ⟨h₁ trivial, hz⟩⟩

private theorem fiberComparison_isIso {K X : TopCat.{0}} [CompactSpace K] [Nonempty K]
    [ParacompactSpace (↥(⊤ : Opens K))] [NormalSpace (↥(⊤ : Opens K))]
    (x : X) (F : Sheaves (TopCat.of (K × X))) :
    IsIso ((fiberComparison (K := K) x).app F) := by
  let p := secondProjection K X
  let i := fiberInclusion K x
  let P := ((directImage p).obj F).obj
  let G := (inverseImage i).obj F
  let a := (fiberComparison (K := K) x).app F
  have hres (U : Opens X) (hx : x ∈ U) (s : P.obj (op U)) :
      a (germ P U x hx s) = fiberRestriction x F U hx s :=
    ConcreteCategory.congr_hom (fiberComparison_germ x F U hx) s
  apply (ConcreteCategory.isIso_iff_bijective a).mpr
  constructor
  · intro a₁ a₂ he
    obtain ⟨U, hU, s, rfl⟩ := exists_germ_eq P a₁
    obtain ⟨V, hV, t, rfl⟩ := exists_germ_eq P a₂
    change a (germ P U x hU s) = a (germ P V x hV t) at he
    rw [hres, hres] at he
    let W := agreementOpen F (U := (Opens.map p).obj U) (V := (Opens.map p).obj V) s t
    have hW (k : K) : (k, x) ∈ W := by
      have e := congrArg (fun a => germ G.obj ⊤ k trivial a) he
      rw [fiberRestriction_germ, fiberRestriction_germ] at e
      exact ⟨hU, hV, ((ConcreteCategory.isIso_iff_bijective
        (inverseImageStalkMap i F k)).mp inferInstance).injective e⟩
    obtain ⟨B, hB, hBW⟩ := exists_tube x W hW
    let k₀ : K := Classical.choice inferInstance
    let bU : B ⟶ U := homOfLE fun y hy => (hBW (show (k₀, y) ∈
      (Opens.map p).obj B from hy)).1
    let bV : B ⟶ V := homOfLE fun y hy => (hBW (show (k₀, y) ∈
      (Opens.map p).obj B from hy)).2.1
    apply germ_ext P B hB bU bV
    apply section_ext F
    intro z hz
    change germ F.obj ((Opens.map p).obj B) z hz
        (F.obj.map ((Opens.map p).map bU).op s) =
      germ F.obj ((Opens.map p).obj B) z hz (F.obj.map ((Opens.map p).map bV).op t)
    rw [germ_res_apply, germ_res_apply]
    exact (hBW hz).2.2
  · intro s
    obtain ⟨W, t, hW⟩ := lift_fiber_section x F ⊤ s
    obtain ⟨B, hB, hBW⟩ := exists_tube x W (fun k => (hW k trivial).choose)
    let j : (Opens.map p).obj B ⟶ W := homOfLE hBW
    let b := F.obj.map j.op t
    refine ⟨germ P B x hB b, ?_⟩
    change a (germ P B x hB b) = s
    rw [hres]
    apply section_ext G
    intro k _
    rw [fiberRestriction_germ]
    obtain ⟨_, e⟩ := hW k trivial
    rw [e, germ_res_apply]

open private constantPresheaf constSection constantGermIso constSection_germ from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage

/-- The unit followed by fiber restriction sends a germ to its canonical
pullback at every point of the fiber. -/
private def fiberUnit {K X : TopCat.{0}} (x : X) (F : Sheaves X) :
    (stalk x).obj F ⟶ (globalSections K).obj
      ((inverseImage (fiberInclusion K x)).obj ((inverseImage (secondProjection K X)).obj F)) :=
  (stalk x).map ((inverseDirectAdjunction (secondProjection K X)).unit.app F) ≫
    (fiberComparison x).app _

private theorem fiberUnit_germ {K X : TopCat.{0}} (x : X) (F : Sheaves X) (k : K) :
    let p := secondProjection K X
    let i := fiberInclusion K x
    let P := (inverseImage p).obj F
    fiberUnit (K := K) x F ≫ germ ((inverseImage i).obj P).obj ⊤ k trivial =
      inverseImageStalkMap p F (k, x) ≫ inverseImageStalkMap i P k := by
  dsimp only
  let p := secondProjection K X
  let i := fiberInclusion K x
  let P := (inverseImage p).obj F
  let η := (inverseDirectAdjunction p).unit.app F
  let G := (inverseImage i).obj P
  apply stalk_hom_ext F.obj
  intro U hx
  apply ConcreteCategory.hom_ext
  intro s
  have e₁ := stalkFunctor_map_germ_apply U x hx η.hom s
  change (stalk x).map η (germ F.obj U x hx s) =
    germ ((directImage p).obj P).obj U x hx (pullSection p F U s) at e₁
  have e₂ := ConcreteCategory.congr_hom (fiberComparison_germ x P U hx)
    (pullSection p F U s)
  change (fiberComparison x).app P (germ ((directImage p).obj P).obj U x hx
    (pullSection p F U s)) = _ at e₂
  change germ G.obj ⊤ k trivial (fiberUnit x F (germ F.obj U x hx s)) =
    inverseImageStalkMap i P k (inverseImageStalkMap p F (k, x) (germ F.obj U x hx s))
  unfold fiberUnit
  rw [ConcreteCategory.comp_apply]
  erw [e₁, e₂, fiberRestriction_germ, pullSection_germ]
  rfl

/-- The pullback over the fiber is the constant sheaf with value the stalk on the base. -/
private def fiberConstantMap {K X : TopCat.{0}} (x : X) (F : Sheaves X) :
    constant K ((stalk x).obj F) ⟶
      (inverseImage (fiberInclusion K x)).obj ((inverseImage (secondProjection K X)).obj F) := by
  let G := (inverseImage (fiberInclusion K x)).obj ((inverseImage (secondProjection K X)).obj F)
  let j (U : Opens K) : U ⟶ (⊤ : Opens K) := homOfLE le_top
  let α : constantPresheaf K ((stalk x).obj F) ⟶ G.obj :=
    { app := fun U => fiberUnit x F ≫ G.obj.map (j U.unop).op
      naturality := by
        intro U V v
        change 𝟙 _ ≫ _ = _
        simp only [Category.id_comp, Category.assoc, ← Functor.map_comp]
        rfl }
  exact ⟨sheafifyLift _ α G.property⟩

private theorem fiberConstantMap_global {K X : TopCat.{0}} (x : X) (F : Sheaves X) :
    constSection K ((stalk x).obj F) ⊤ ≫ (fiberConstantMap (K := K) x F).hom.app (op ⊤) =
      fiberUnit x F := by
  let G := (inverseImage (fiberInclusion K x)).obj ((inverseImage (secondProjection K X)).obj F)
  let j : (⊤ : Opens K) ⟶ ⊤ := homOfLE le_top
  trans fiberUnit (K := K) x F ≫ G.obj.map j.op
  · unfold fiberConstantMap
    exact congrArg (fun η : constantPresheaf K ((stalk x).obj F) ⟶ G.obj =>
      η.app (op (⊤ : Opens K))) (toSheafify_sheafifyLift _ _ _)
  · rw [show j = 𝟙 _ from Subsingleton.elim _ _]
    simp
    exact Category.comp_id (fiberUnit (K := K) x F)

private theorem fiberConstantMap_isIso {K X : TopCat.{0}} (x : X) (F : Sheaves X) :
    IsIso (fiberConstantMap (K := K) x F) := by
  apply (isIso_iff_stalkFunctor_map_iso _).mpr
  intro k
  let V := (stalk x).obj F
  let c := fiberConstantMap (K := K) x F
  let C := stalkFunctor Coeff k
  have hη : IsIso (constSection K V ⊤ ≫ germ (constant K V).obj ⊤ k trivial) := by
    rw [← isIso_comp_right_iff _ (constantGermIso K V k).hom, Category.assoc,
      constSection_germ]
    infer_instance
  rw [← isIso_comp_left_iff (constSection K V ⊤ ≫ germ (constant K V).obj ⊤ k trivial)]
  erw [Category.assoc, stalkFunctor_map_germ, ← Category.assoc, fiberConstantMap_global,
    fiberUnit_germ]
  infer_instance

private theorem ordinaryUnit_isIso {K X : TopCat.{0}} [CompactSpace K] [ConnectedSpace K]
    [ParacompactSpace (↥(⊤ : Opens K))] [NormalSpace (↥(⊤ : Opens K))]
    (F : Sheaves X) : IsIso ((inverseDirectAdjunction (secondProjection K X)).unit.app F) := by
  apply (isIso_iff_stalkFunctor_map_iso _).mpr
  intro x
  let V := (stalk x).obj F
  let a := (fiberComparison (K := K) x).app ((inverseImage (secondProjection K X)).obj F)
  haveI : IsIso a := fiberComparison_isIso _ _
  haveI : IsIso (constSection K V ⊤) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (SimplicialConstructibleDirectImage.constSection_bijective V ⊤
      (by simpa only [Opens.coe_top] using (isConnected_univ (α := K))))
  haveI := fiberConstantMap_isIso (K := K) x F
  haveI : IsIso ((globalSections K).map (fiberConstantMap (K := K) x F)) := inferInstance
  haveI : IsIso (fiberUnit (K := K) x F) := by
    rw [← fiberConstantMap_global]
    exact IsIso.comp_isIso
  haveI : IsIso ((stalk x).map ((inverseDirectAdjunction (secondProjection K X)).unit.app F) ≫ a) :=
    inferInstanceAs (IsIso (fiberUnit (K := K) x F))
  exact IsIso.of_isIso_comp_right
    ((stalk x).map ((inverseDirectAdjunction (secondProjection K X)).unit.app F)) a

private abbrev interval := TopCat.of unitInterval

private theorem interval_open_topology (U : Opens interval) :
    ParacompactSpace U ∧ NormalSpace U := ⟨inferInstance, inferInstance⟩

private instance : CompactSpace interval := isCompact_iff_compactSpace.mp isCompact_Icc
private instance : ConnectedSpace interval :=
  isConnected_iff_connectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isConnected ⟨0, by simp⟩)

private theorem interval_contractibleBasis (x : interval) (U : Opens interval) (hx : x ∈ U) :
    ∃ W : Opens interval, W ≤ U ∧ x ∈ W ∧ ContractibleSpace (TopCat.of W) := by
  obtain ⟨r, hr, hU⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let W : Opens interval :=
    ⟨Subtype.val ⁻¹' Metric.ball x.val r, Metric.isOpen_ball.preimage continuous_subtype_val⟩
  let A := Metric.ball x.val r ∩ unitInterval
  let e : W ≃ₜ A :=
    { toFun := fun y => ⟨y.val.val, y.property, y.val.property⟩
      invFun := fun y => ⟨⟨y.val, y.property.2⟩, y.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have : ContractibleSpace A :=
    ((convex_ball x.val r).inter (convex_Icc _ _)).contractibleSpace
      ⟨x.val, Metric.mem_ball_self hr, x.property⟩
  exact ⟨W, hU, Metric.mem_ball_self hr, e.contractibleSpace⟩

private instance : ContractibleSpace (TopCat.of (↥(⊤ : Opens interval))) := by
  have : ContractibleSpace interval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let e : (↥(⊤ : Opens interval)) ≃ₜ interval :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  exact e.contractibleSpace

open private existsInjectiveRepresentative derivedCohomologyIso plusHomologyFactors
  exactPlusFactors isIsoDerivedSectionsOfFlasque from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves

/-- Proper base change on the stalk cohomology of the interval projection. The map
on the representing complexes is the termwise fiber restriction. -/
private def derivedFiberCohomology {X : TopCat.{0}} (x : X)
    (E : BoundedBelow (TopCat.of (unitInterval × X))) (q : ℤ) :
    (stalk x).obj ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedDirectImage (secondProjection interval X)).obj E)) ≅
    (DerivedCategory.Plus.homologyFunctor Coeff q).obj
      ((globalSections interval).rightDerivedFunctorPlus.obj
        ((boundedBelowInverseImage (fiberInclusion interval x)).obj E)) := by
  let T := directImage (secondProjection interval X)
  let L := inverseImage (fiberInclusion interval x)
  let S := stalk x
  let Γ := globalSections interval
  let H := DerivedCategory.Plus.homologyFunctor Coeff q
  let h := HomologicalComplex.homologyFunctor Coeff (ComplexShape.up ℤ) q
  let I := (existsInjectiveRepresentative E).choose
  let e := (existsInjectiveRepresentative E).choose_spec.some
  let J := injectiveComplex I
  let K := L.mapCochainComplexPlus.obj J
  have hK (n : ℤ) : TopCat.Sheaf.IsFlasque (K.obj.X n) := by
    let F := J.obj.X n
    haveI : Injective F := (I.obj.X n).property
    haveI := DerivedLocalSheaves.injectiveFlasque F
    exact fiber_flasque x interval_open_topology F
  haveI : IsIso (Γ.rightDerivedFunctorPlusUnit.app K) := isIsoDerivedSectionsOfFlasque ⊤ K hK
  let eL : DerivedCategory.Plus.Q.obj K ≅ (exactDerivedPlus L).obj E :=
    ((exactPlusFactors L).app J).symm ≪≫ (exactDerivedPlus L).mapIso e
  let eR := asIso (Γ.rightDerivedFunctorPlusUnit.app K) ≪≫
    Γ.rightDerivedFunctorPlus.mapIso eL
  haveI := (interval_open_topology ⊤).1
  haveI := (interval_open_topology ⊤).2
  let b : T ⋙ S ≅ L ⋙ Γ := NatIso.ofComponents
    (fun F => by have := fiberComparison_isIso (K := interval) x F
                 exact asIso ((fiberComparison x).app F))
    (fun f => (fiberComparison (K := interval) x).naturality f)
  let e₀ := S.mapIso (derivedCohomologyIso T I q E e)
  let e₁ := (((T.mapCochainComplexPlus.obj J).obj.sc q).mapHomologyIso S).symm
  let e₂ := h.mapIso ((NatIso.mapHomologicalComplex b (.up ℤ)).app J.obj)
  let e₃ := ((plusHomologyFactors Coeff q).app (Γ.mapCochainComplexPlus.obj K)).symm
  exact e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ H.mapIso eR

private def pullbackSingleIso {A B : TopCat.{0}} (f : A ⟶ B) (F : Sheaves B) :
    (boundedBelowInverseImage f).obj (sheafInDegreeZero F) ≅
      sheafInDegreeZero ((inverseImage f).obj F) :=
  DerivedCategory.Plus.ι.preimageIso (((inverseImage f).mapDerivedCategorySingleFunctor 0).app F)

/-- Pullbacks of sheaves in degree zero have no positive higher direct images along the
interval projection. The coefficients on the fiber are the full rational stalk. -/
private theorem projection_positive_vanishing {X : TopCat.{0}} (F : Sheaves X) (n : ℕ) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (Sheaves X) (n + 1 : ℕ)).obj
      ((derivedDirectImage (secondProjection interval X)).obj
        (sheafInDegreeZero ((inverseImage (secondProjection interval X)).obj F)))) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  let i := fiberInclusion interval x
  let P := (inverseImage (secondProjection interval X)).obj F
  let E := sheafInDegreeZero P
  let Γ := (globalSections interval).rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor Coeff ((n + 1 : ℕ) : ℤ)
  let a := derivedFiberCohomology x E (n + 1 : ℕ)
  haveI := fiberConstantMap_isIso (K := interval) x F
  let b := pullbackSingleIso i P ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso (asIso (fiberConstantMap x F)).symm
  exact (SimplicialConstructibleDirectImage.derivedSectionsConstant_isZero_pos
    unitInterval ((stalk x).obj F) interval_contractibleBasis ⊤ n).of_iso
      (a ≪≫ H.mapIso (Γ.mapIso b))

open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
open private exactRightDerivedAdjunction from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves

private theorem projection_acyclic {X : TopCat.{0}} (F : Sheaves X) :
    rightAcyclicValue (directImage (secondProjection interval X))
      ((inverseImage (secondProjection interval X)).obj F) := by
  let p := secondProjection interval X
  let T := directImage p
  let P := (inverseImage p).obj F
  apply (AdvancedHomologicalAlgebra.AcyclicTermComparison.rightVanishing _ _ T P).mpr
  intro n
  let h := DerivedCategory.Plus.homologyFunctor (Sheaves X) ((n + 1 : ℕ) : ℤ)
  let e : DerivedCategory.Plus.Qh.obj (plusStalkValue P) ≅ sheafInDegreeZero P :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.singleFunctorIsoCompQh (Sheaves (TopCat.of (unitInterval × X))) 0).symm.app P)
  exact (projection_positive_vanishing F n).of_iso
    (h.mapIso (T.rightDerivedFunctorPlus.mapIso e))

/-- The canonical derived adjunction unit on a cochain representative. -/
private theorem derivedUnit_factorization {Y X : TopCat.{0}} (p : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaves X)) :
    (DerivedLocalSheaves.derivedInverseDirectAdjunctionData p).unit.app (DerivedCategory.Plus.Q.obj K) ≫
      (derivedDirectImage p).map ((exactPlusFactors (inverseImage p)).hom.app K) =
    DerivedCategory.Plus.Q.map ((inverseDirectAdjunction p).unit.mapCochainComplexPlus.app K) ≫
      (directImage p).rightDerivedFunctorPlusUnit.app ((inverseImage p).mapCochainComplexPlus.obj K) := by
  unfold DerivedLocalSheaves.derivedInverseDirectAdjunctionData exactRightDerivedAdjunction
  simp only [Adjunction.derived_unit, Adjunction.derivedη_fac_app]
  rfl

private theorem projection_derivedUnit_isIso (X : TopCat.{0}) :
    IsIso (DerivedLocalSheaves.derivedInverseDirectAdjunctionData (secondProjection interval X)).unit := by
  let p := secondProjection interval X
  let a := inverseDirectAdjunction p
  let b := DerivedLocalSheaves.derivedInverseDirectAdjunctionData p
  let L := inverseImage p
  let T := directImage p
  let Q := DerivedCategory.Plus.Q (C := Sheaves X)
  haveI := (interval_open_topology ⊤).1
  haveI := (interval_open_topology ⊤).2
  haveI (F : BoundedBelow X) : IsIso (b.unit.app F) := by
    obtain ⟨I, ⟨e⟩⟩ := existsInjectiveRepresentative F
    rw [← NatTrans.isIso_app_iff_of_iso b.unit e]
    let K := injectiveComplex I
    let J := L.mapCochainComplexPlus.obj K
    let u := a.unit.mapCochainComplexPlus.app K
    haveI (n : ℤ) : IsIso (u.hom.f n) := ordinaryUnit_isIso (K := interval) (K.obj.X n)
    haveI : IsIso ((CochainComplex.Plus.ι (Sheaves X)).map u) :=
      HomologicalComplex.Hom.isIso_of_components u.hom
    haveI : IsIso u := (CochainComplex.Plus.fullyFaithfulι _).isIso_of_isIso_map u
    let J' := (HomotopyCategory.Plus.quotient _).obj J
    have hJ (n : ℤ) : rightAcyclicValue T (J'.obj.as.X n) :=
      projection_acyclic (K.obj.X n)
    haveI : IsIso (T.rightDerivedFunctorPlusUnith.app J') :=
      AdvancedHomologicalAlgebra.AcyclicTermComparison.rightComparison _ _ T J' hJ
    haveI : IsIso (T.rightDerivedFunctorPlusUnit.app J) := by
      simp only [Functor.rightDerivedFunctorPlusUnit_app]
      infer_instance
    let c := T.rightDerivedFunctorPlus.map ((exactPlusFactors L).hom.app K)
    haveI : IsIso c :=
      Functor.map_isIso T.rightDerivedFunctorPlus ((exactPlusFactors L).hom.app K)
    haveI : IsIso (b.unit.app (Q.obj K) ≫ c) := by
      change IsIso (_ ≫ (derivedDirectImage p).map ((exactPlusFactors (inverseImage p)).hom.app K))
      rw [derivedUnit_factorization]
      change IsIso (Q.map u ≫ T.rightDerivedFunctorPlusUnit.app J)
      infer_instance
    exact IsIso.of_isIso_comp_right (b.unit.app (Q.obj K)) c
  exact NatIso.isIso_of_isIso_app b.unit

theorem intervalProjectionFullyFaithful : Expected.IntervalProjectionFullyFaithful := by
  intro X
  let b := DerivedLocalSheaves.derivedInverseDirectAdjunctionData (secondProjection interval X)
  haveI : IsIso b.unit := projection_derivedUnit_isIso X
  exact ⟨b.fullyFaithfulLOfIsIsoUnit⟩

end RepTheorySurvey.Geometric.IntervalProjectionPullback
