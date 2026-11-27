import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.FiniteCellApproximation
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellReindex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Telescope
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoproducts
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeMaps
import Mathlib.CategoryTheory.Triangulated.Yoneda

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor (whiskerLeft whiskerRight)
open scoped DirectSum

universe u v w j t z

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.FiniteCellApproximation
open IndexedSemiFree
open Specs.DerivedFormalization.DG.CellReindex (GradedDecomposition cellToModule)
open private moduleDecoding moduleDecoding_summand moduleDecoding_stageEncoding stageEncoding
  stageEncoding_old stageEncoding_new stageEncoding_bounded stageInclusion_into
  restrictSum restrictSum_apply extendSum extendSum_apply extendSum_off_range extendSum_lof
  stageDecoding restrictStage extendStage_restrictStage moduleDecoding_extendStage
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellReindex
open private boundaryMap_summand from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedCellAttachment
open private term_hom_ext from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedSums
open private strictConeMap strictConeMap_apply from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeMaps

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {M : RightDGModuleModel A} {F : Presentation.{u,v,w,j} M}

private theorem differentialSupport_finite (D : GradedDecomposition F) (s : CellIndex F) :
    (differentialSupport D s).Finite :=
  DFinsupp.finite_support (D.coordinates _ _ (attachmentValue F s))

private theorem differentialSupport_earlier (D : GradedDecomposition F)
    {s r : CellIndex F} (hr : r ∈ differentialSupport D s) : r.1 < s.1 := by
  by_contra h
  apply hr
  unfold attachmentValue
  rw [D.into, dite_eq_right h]

private theorem closed_empty (D : GradedDecomposition F) :
    IsClosed D ∅ := by simp [IsClosed]

private theorem closed_union [DecidableEq (CellIndex F)] (D : GradedDecomposition F) {E G : Finset (CellIndex F)}
    (hE : IsClosed D E) (hG : IsClosed D G) :
    IsClosed D (E ∪ G) := by
  classical
  intro s hs r hr
  rcases Finset.mem_union.mp hs with hs | hs
  · exact Finset.mem_union_left _ (hE s hs r hr)
  · exact Finset.mem_union_right _ (hG s hs r hr)

private theorem bounded_union [DecidableEq (CellIndex F)] (N : ℕ) {E G : Finset (CellIndex F)}
    (hE : ∀ s ∈ E, s.1 < N) (hG : ∀ s ∈ G, s.1 < N) :
    ∀ s ∈ E ∪ G, s.1 < N := by
  classical
  intro s hs
  exact (Finset.mem_union.mp hs).elim (hE s) (hG s)

private theorem exists_closed_superset (D : GradedDecomposition F) (N : ℕ)
    (E : Finset (CellIndex F)) (hE : ∀ s ∈ E, s.1 < N) :
    ∃ U : ClosedCells D N, E ⊆ U.val := by
  classical
  induction N generalizing E with
  | zero =>
      have he : E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun s hs => Nat.not_lt_zero _ (hE s hs))
      subst E
      exact ⟨⟨∅, closed_empty D, by simp⟩, Finset.Subset.refl _⟩
  | succ N ih =>
      induction E using Finset.induction_on with
      | empty =>
          exact ⟨⟨∅, closed_empty D, by simp⟩, Finset.Subset.refl _⟩
      | insert s E hs ihE =>
          obtain ⟨U, hU⟩ := ihE (fun r hr => hE r (Finset.mem_insert_of_mem hr))
          have htop := hE s (Finset.mem_insert_self s E)
          let V₀ := (differentialSupport_finite D s).toFinset
          have hV₀ : ∀ r ∈ V₀, r.1 < N := by
            intro r hr
            have h := differentialSupport_earlier D
              ((Set.Finite.mem_toFinset _).mp hr)
            omega
          obtain ⟨V, hV⟩ := ih V₀ hV₀
          have hclosed : IsClosed D (insert s V.val) := by
            intro r hr q hq
            rcases Finset.mem_insert.mp hr with rfl | hr
            · exact Finset.mem_insert_of_mem (hV ((Set.Finite.mem_toFinset _).mpr hq))
            · exact Finset.mem_insert_of_mem (V.property.1 r hr q hq)
          have hbounded : ∀ r ∈ insert s V.val, r.1 < N + 1 := by
            intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hr
            · exact htop
            · exact Nat.lt_succ_of_lt (V.property.2 r hr)
          refine ⟨⟨insert s V.val ∪ U.val, closed_union D hclosed U.property.1,
            bounded_union _ hbounded U.property.2⟩, ?_⟩
          intro r hr
          rcases Finset.mem_insert.mp hr with rfl | hr
          · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
          · exact Finset.mem_union_right _ (hU hr)

theorem closedCellsDirected : ClosedCellsDirected.{u,v,w,j} := by
  classical
  intro k _ A M F D N
  refine ⟨exists_closed_superset D N, ⟨⟨∅, closed_empty D, by simp⟩⟩, ?_⟩
  intro E G
  exact ⟨⟨E.val ∪ G.val, closed_union D E.property.1 G.property.1,
    bounded_union N E.property.2 G.property.2⟩, Finset.subset_union_left, Finset.subset_union_right⟩

private def supportedTerm (D : GradedDecomposition F) (E : Finset (CellIndex F))
    (a : A.Obj) (n : ℤ) : Submodule k ((M.complex a).X n) where
  carrier := {x | IsSupported D E a n x}
  zero_mem' := by
    intro s hs
    rw [map_zero]
    rfl
  add_mem' {x y} hx hy := by
    intro s hs
    rw [map_add, DFinsupp.add_apply, hx s hs, hy s hs, add_zero]
  smul_mem' c x hx := by
    intro s hs
    rw [map_smul, DFinsupp.smul_apply, hx s hs, smul_zero]

private theorem supported_act (D : GradedDecomposition F) (E : Finset (CellIndex F))
    {a b : A.Obj} {m n q : ℤ} (h : m + n = q)
    {x : (M.complex b).X m} (hx : IsSupported D E b m x) (f : (A.hom a b).X n) :
    IsSupported D E a q (M.act m n q h x f) := by
  intro s hs
  rw [D.coordinate_act, hx s hs, map_zero, LinearMap.zero_apply]

private theorem supported_cell (D : GradedDecomposition F) (E : Finset (CellIndex F))
    {s : CellIndex F} (hs : s ∈ E) (a : A.Obj) (n : ℤ)
    (x : ((CellReindex.allCells F s).complex a).X n) :
    IsSupported D E a n (cellToModule F s a n x) := by
  classical
  let : DecidableEq (CellIndex F) := Classical.decEq _
  intro r hr
  rw [D.cell]
  unfold summand
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_of_ne (β := fun s => ((CellReindex.allCells F s).complex a).X n) s r x (fun e => hr (e.symm ▸ hs))

private abbrev namedGenerator (F : Presentation.{u,v,w,j} M) (s : CellIndex F) :=
  ((F.into (s.1+1)).app ((F.family s.1).object s.2)).f ((F.family s.1).degree s.2)
    ((F.extension s.1).generator s.2)

private theorem supported_generator (D : GradedDecomposition F) (E : Finset (CellIndex F))
    {s : CellIndex F} (hs : s ∈ E) :
    IsSupported D E _ _ (namedGenerator F s) :=
  supported_cell D E hs _ _ (SemiFree.generator _ _)

private theorem namedGenerator_d (s : CellIndex F) :
    (M.complex ((F.family s.1).object s.2)).d ((F.family s.1).degree s.2)
      ((F.family s.1).degree s.2 + 1) (namedGenerator F s) = attachmentValue F s := by
  let a := (F.family s.1).object s.2
  let n := (F.family s.1).degree s.2
  let x := (F.extension s.1).generator s.2
  have h := CategoryTheory.congr_fun (((F.into (s.1+1)).app a).comm n (n+1)) x
  change (M.complex a).d n (n+1) (((F.into (s.1+1)).app a).f n x) =
    ((F.into (s.1+1)).app a).f (n+1) (((F.stage (s.1+1)).complex a).d n (n+1) x) at h
  change (M.complex a).d n (n+1) (((F.into (s.1+1)).app a).f n x) = _
  rw [h]
  dsimp only [x]
  rw [DerivedFormalization.DG.IndexedCellAttachment.generator_d]
  exact congrArg (fun g : F.stage s.1 ⟶ M =>
    (g.app a).f (n+1) ((F.family s.1).boundary s.2)) (F.compatible s.1)

private theorem cellToModule_apply (s : CellIndex F) (a : A.Obj) (n : ℤ)
    (x : ((CellReindex.allCells F s).complex a).X n) :
    cellToModule F s a n x =
      M.act ((F.family s.1).degree s.2) (n + -(F.family s.1).degree s.2) n
        (by omega) (namedGenerator F s) x := by
  have h := DerivedFormalization.DG.CellReindex.cellMapFormula F s.1 s.2 a
    (n + -(F.family s.1).degree s.2) n (by omega) x
  rw [HomologicalComplex.XIsoOfEq_rfl] at h
  change CellReindex.cellToSuccessor F s.1 s.2 a n x = _ at h
  change ((F.into (s.1+1)).app a).f n (CellReindex.cellToSuccessor F s.1 s.2 a n x) = _
  rw [h, (F.into (s.1+1)).comm_act]

private theorem supported_d_cell (D : GradedDecomposition F) (E : Finset (CellIndex F))
    (hE : IsClosed D E) {s : CellIndex F} (hs : s ∈ E) (a : A.Obj) (n : ℤ)
    (x : ((CellReindex.allCells F s).complex a).X n) :
    IsSupported D E a (n+1) ((M.complex a).d n (n+1) (cellToModule F s a n x)) := by
  have hz : IsSupported D E _ _ (attachmentValue F s) := by
    intro r hr
    by_contra hn
    exact hr (hE s hs r hn)
  rw [cellToModule_apply, M.leibniz, namedGenerator_d]
  exact (supportedTerm D E a (n+1)).add_mem (supported_act D E _ hz x)
    (by
      have hs' := supported_act D E
        (a := a) (b := (F.family s.1).object s.2)
        (q := n+1) (n := n + -(F.family s.1).degree s.2 + 1)
        (by omega) (supported_generator D E hs)
        ((A.hom a ((F.family s.1).object s.2)).d _ _ x)
      intro r hr
      rw [Units.smul_def, map_zsmul, DFinsupp.smul_apply, hs' r hr, smul_zero])

private theorem supported_d (D : GradedDecomposition F) (E : Finset (CellIndex F))
    (hE : IsClosed D E) (a : A.Obj) (n : ℤ) (x : (M.complex a).X n)
    (hx : IsSupported D E a n x) :
    IsSupported D E a (n+1) ((M.complex a).d n (n+1) x) := by
  classical
  let : DecidableEq (CellIndex F) := Classical.decEq _
  let e := D.coordinates a n
  suffices h : ∀ z : SumTerm (CellReindex.allCells F) a n,
      (∀ s, s ∉ E → z s = 0) →
        IsSupported D E a (n+1) ((M.complex a).d n (n+1) (e.symm z)) by
    simpa only [e.symm_apply_apply] using h (e x) hx
  intro z
  induction z using DirectSum.induction_on' with
  | h0 =>
      intro _
      rw [map_zero, map_zero]
      exact (supportedTerm D E a (n+1)).zero_mem
  | hadd s y z hz hy ih =>
      intro h
      have hs : s ∈ E := by
        by_contra hs
        apply hy
        have ht := h s hs
        change DirectSum.of (fun s => ((CellReindex.allCells F s).complex a).X n) s y s + z s = 0 at ht
        rwa [DirectSum.of_eq_same, hz, add_zero] at ht
      have hrest (r : CellIndex F) (hr : r ∉ E) : z r = 0 := by
        have hne : r ≠ s := fun e => hr (e.symm ▸ hs)
        have ht := h r hr
        change DirectSum.of (fun s => ((CellReindex.allCells F s).complex a).X n) s y r + z r = 0 at ht
        rwa [DirectSum.of_eq_of_ne _ _ _ hne, zero_add] at ht
      have hsingle : e.symm (DirectSum.of _ s y) = cellToModule F s a n y := by
        apply e.injective
        rw [e.apply_symm_apply]
        simpa only [summand, DirectSum.lof_eq_of] using (D.cell s a n y).symm
      rw [map_add, hsingle, map_add]
      exact (supportedTerm D E a (n+1)).add_mem (supported_d_cell D E hE hs a n y) (ih hrest)

private abbrev ClosedSelection (D : GradedDecomposition F) :=
  {E : Finset (CellIndex F) // IsClosed D E}

private abbrev stageSupported (D : GradedDecomposition F) (N : ℕ) (E : ClosedSelection D)
    (a : A.Obj) (n : ℤ) : Submodule k (((F.stage N).complex a).X n) :=
  (supportedTerm D E.val a n).comap (((F.into N).app a).f n).hom

private theorem stageSupported_d (D : GradedDecomposition F) (N : ℕ) (E : ClosedSelection D)
    (a : A.Obj) (i l : ℤ) (x : ((F.stage N).complex a).X i)
    (hx : x ∈ stageSupported D N E a i) :
    ((F.stage N).complex a).d i l x ∈ stageSupported D N E a l := by
  by_cases h : i + 1 = l
  · subst l
    change ((F.into N).app a).f (i+1) _ ∈ supportedTerm D E.val a (i+1)
    have hc := CategoryTheory.congr_fun (((F.into N).app a).comm i (i+1)) x
    change (M.complex a).d i (i+1) (((F.into N).app a).f i x) =
      ((F.into N).app a).f (i+1) (((F.stage N).complex a).d i (i+1) x) at hc
    rw [← hc]
    exact supported_d D E.val E.property a i _ hx
  · rw [((F.stage N).complex a).shape i l h]
    exact (stageSupported D N E a l).zero_mem

private def supportedComplex (D : GradedDecomposition F) (N : ℕ) (E : ClosedSelection D)
    (a : A.Obj) : ModuleCochain.{u,v} k where
  X i := ModuleCat.of k (stageSupported D N E a i)
  d i l := ModuleCat.ofHom ((((F.stage N).complex a).d i l).hom.restrict
    (stageSupported_d D N E a i l))
  shape i l h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((F.stage N).complex a).d i l x.val = 0
    rw [((F.stage N).complex a).shape i l h]
    rfl
  d_comp_d' i l p _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((F.stage N).complex a).d l p (((F.stage N).complex a).d i l x.val) = 0
    exact CategoryTheory.congr_fun (((F.stage N).complex a).d_comp_d i l p) x.val

private def supportedModule (D : GradedDecomposition F) (N : ℕ) (E : ClosedSelection D) :
    RightDGModuleModel A where
  complex := supportedComplex D N E
  act {a b} i l p h :=
    LinearMap.mk₂ k
      (fun x f => ⟨(F.stage N).act i l p h x.val f, by
        change ((F.into N).app a).f p _ ∈ supportedTerm D E.val a p
        rw [(F.into N).comm_act]
        exact supported_act D E.val h x.property f⟩)
      (by intro x y f; apply Subtype.ext; exact LinearMap.congr_fun (map_add _ _ _) _)
      (by intro c x f; apply Subtype.ext; exact LinearMap.congr_fun (map_smul _ _ _) _)
      (by intro x f g; apply Subtype.ext; exact map_add _ _ _)
      (by intro c x f; apply Subtype.ext; exact map_smul _ _ _)
  act_id a i x := Subtype.ext ((F.stage N).act_id a i x.val)
  act_assoc i l p x f g := Subtype.ext ((F.stage N).act_assoc i l p x.val f g)
  leibniz i l p h x f := Subtype.ext ((F.stage N).leibniz i l p h x.val f)

private def supportedInclusion (D : GradedDecomposition F) (N : ℕ) (E : ClosedSelection D) :
    supportedModule D N E ⟶ F.stage N where
  app a :=
    { f := fun i => ModuleCat.ofHom (stageSupported D N E a i).subtype
      comm' := fun _ _ _ => rfl }
  comm_act := fun _ _ _ _ _ _ => rfl

private def supportedTransition (D : GradedDecomposition F) (N : ℕ)
    {E G : ClosedSelection D} (h : E ≤ G) :
    supportedModule D N E ⟶ supportedModule D N G where
  app _a :=
    { f := fun _i => ModuleCat.ofHom (Submodule.inclusion (fun _x hx s hs => hx s (fun hm => hs (h hm))))
      comm' := fun _ _ _ => rfl }
  comm_act := fun _ _ _ _ _ _ => rfl

private def supportedDiagram (D : GradedDecomposition F) (N l : ℕ) :
    ClosedCells D N ⥤ RightDGModuleModel A where
  obj E := supportedModule D l ⟨E.val, E.property.1⟩
  map f := supportedTransition D l f.le
  map_id := by intro E; rfl
  map_comp := by intro E G H f g; rfl

private def supportedCocone (D : GradedDecomposition F) (N l : ℕ) :
    Cocone (supportedDiagram D N l) where
  pt := F.stage l
  ι :=
    { app := fun E => supportedInclusion D l ⟨E.val, E.property.1⟩
      naturality := by intro E G f; rfl }

private def stageSubmodules (D : GradedDecomposition F) (N : ℕ) : StageSubmodules D N where
  diagram := supportedDiagram D N N
  inclusion := (supportedCocone D N N).ι
  injective := fun E a n => Subtype.val_injective
  image := by
    intro E a n x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩

private theorem coordinates_into (D : GradedDecomposition F) (l : ℕ) (a : A.Obj) (n : ℤ)
    (x : ((F.stage l).complex a).X n) :
    D.coordinates a n (((F.into l).app a).f n x) = stageEncoding F a n l x := by
  let : DecidableEq (CellIndex F) := Classical.decEq _
  have h : (D.coordinates a n).symm.toLinearMap = moduleDecoding F a n := by
    apply DirectSum.linearMap_ext
    intro s
    apply LinearMap.ext
    intro y
    change (D.coordinates a n).symm (summand (CellReindex.allCells F) a n s y) =
      moduleDecoding F a n (summand (CellReindex.allCells F) a n s y)
    rw [moduleDecoding_summand, ← D.cell, LinearEquiv.symm_apply_apply]
  apply (D.coordinates a n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (moduleDecoding_stageEncoding F l a n x).symm.trans
    (congrArg (fun f : SumTerm (CellReindex.allCells F) a n →ₗ[k] _ =>
      f (stageEncoding F a n l x)) h.symm)

private abbrev Selected {D : GradedDecomposition F} (E : ClosedSelection (F := F) D) (l : ℕ) :=
  {i : F.index l // Sigma.mk l i ∈ E.val}

private theorem coordinates_old_supported_iff (D : GradedDecomposition F)
    (E : ClosedSelection D) (l : ℕ) (a : A.Obj) (n : ℤ) (x : ((F.stage (l+1)).complex a).X n) :
    x ∈ stageSupported D (l+1) E a n ↔
      ((F.extension l).coordinates a n x).1 ∈ stageSupported D l E a n ∧
      ∀ i : F.index l, Sigma.mk l i ∉ E.val → ((F.extension l).coordinates a n x).2 i = 0 := by
  change IsSupported D E.val a n (((F.into (l+1)).app a).f n x) ↔
    IsSupported D E.val a n (((F.into l).app a).f n ((F.extension l).coordinates a n x).1) ∧ _
  unfold IsSupported
  rw [coordinates_into, coordinates_into]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro s hs
      by_cases hs' : s.1 = l
      · exact stageEncoding_bounded F a n l _ s (Nat.le_of_eq hs'.symm)
      · rw [← stageEncoding_old F a n l x s hs']
        exact h s hs
    · intro i hi
      rw [← stageEncoding_new F a n l x i]
      exact h ⟨l,i⟩ hi
  · rintro ⟨h, h'⟩ ⟨m,i⟩ hi
    by_cases hm : m = l
    · subst m
      rw [stageEncoding_new]
      exact h' i hi
    · rw [stageEncoding_old _ _ _ _ _ _ hm]
      exact h ⟨m,i⟩ hi

private abbrev selectedFamily (D : GradedDecomposition F) (E : ClosedSelection D) (l : ℕ) :
    IndexedSemiFree.CellFamily (supportedModule D l E) (Selected (F := F) E l) where
  object i := (F.family l).object i.val
  degree i := (F.family l).degree i.val
  boundary i := ⟨(F.family l).boundary i.val, by
    intro r hr
    by_contra h
    exact hr (E.property ⟨l,i.val⟩ i.property r h)⟩
  closed i := by
    apply Subtype.ext
    exact (F.family l).closed i.val

private def selectedCoordinatesMap (D : GradedDecomposition F) (E : ClosedSelection D)
    (l : ℕ) (a : A.Obj) (n : ℤ) :
    (stageSupported D (l+1) E a n) →ₗ[k]
      (stageSupported D l E a n × CellTerm (selectedFamily D E l) a n) :=
  let J := Selected E l
  let b := (F.extension l).coordinates a n
  let f := Subtype.val (p := fun i : F.index l => Sigma.mk l i ∈ E.val)
  let p := stageSupported D (l+1) E a n
  (((LinearMap.fst k _ _).comp b.toLinearMap).restrict
    (fun x hx => ((coordinates_old_supported_iff D E l a n x).mp hx).1)).prod
    ((restrictSum (k := k) (J := J)
      (V := fun i => ((cells (F.family l) i).complex a).X n) f Subtype.val_injective).comp
      ((LinearMap.snd k _ _).comp (b.toLinearMap.comp p.subtype)))

private theorem selectedCoordinatesMap_bijective (D : GradedDecomposition F)
    (E : ClosedSelection D) (l : ℕ) (a : A.Obj) (n : ℤ) :
    Function.Bijective (selectedCoordinatesMap D E l a n) := by
  let b := (F.extension l).coordinates a n
  constructor
  · intro x y h
    apply Subtype.ext
    apply b.injective
    have hf : (b x.val).1 = (b y.val).1 :=
      congrArg (fun z : _ × CellTerm (selectedFamily D E l) a n => z.1.val) h
    apply Prod.ext hf
    apply DFinsupp.ext
    intro i
    by_cases hi : Sigma.mk l i ∈ E.val
    · exact congrArg (fun z : _ × CellTerm (selectedFamily D E l) a n => z.2 ⟨i,hi⟩) h
    · rw [((coordinates_old_supported_iff D E l a n x.val).mp x.property).2 i hi,
        ((coordinates_old_supported_iff D E l a n y.val).mp y.property).2 i hi]
  · rintro ⟨p,z⟩
    let y :=
      extendSum (k := k) (J := Selected E l)
        (V := fun i => ((cells (F.family l) i).complex a).X n) Subtype.val z
    let x := b.symm (p.val, y)
    have hx : b x = (p.val, y) := b.apply_symm_apply _
    have hmem : x ∈ stageSupported D (l+1) E a n := by
      apply (coordinates_old_supported_iff D E l a n x).mpr
      change (b x).1 ∈ stageSupported D l E a n ∧ _
      rw [hx]
      refine ⟨p.property, ?_⟩
      intro i hi
      exact extendSum_off_range (V := fun i => ((cells (F.family l) i).complex a).X n)
        Subtype.val z (fun ⟨j,hj⟩ => hi (hj ▸ j.property))
    refine ⟨⟨x,hmem⟩, Prod.ext ?_ ?_⟩
    · apply Subtype.ext
      exact congrArg Prod.fst hx
    · apply DFinsupp.ext
      intro i
      change (b x).2 i.val = z i
      rw [hx]
      exact extendSum_apply (V := fun i => ((cells (F.family l) i).complex a).X n)
        Subtype.val Subtype.val_injective z i

private def selectedCoordinates (D : GradedDecomposition F)
    (E : ClosedSelection D) (l : ℕ) (a : A.Obj) (n : ℤ) :
    (stageSupported D (l+1) E a n) ≃ₗ[k]
      (stageSupported D l E a n × CellTerm (selectedFamily D E l) a n) :=
  LinearEquiv.ofBijective (selectedCoordinatesMap D E l a n)
    (selectedCoordinatesMap_bijective D E l a n)

private def supportedStageInclusion (D : GradedDecomposition F)
    (E : ClosedSelection D) {l L : ℕ} (h : l ≤ L) :
    supportedModule D l E ⟶ supportedModule D L E := by
  let i := CellReindex.stageInclusion F h
  have hc := stageInclusion_into F h
  have hi (a : A.Obj) (n : ℤ) (x : ((F.stage l).complex a).X n)
      (hx : x ∈ stageSupported D l E a n) :
      (i.app a).f n x ∈ stageSupported D L E a n := by
    change IsSupported D E.val a n (((i ≫ F.into L).app a).f n x)
    rw [show i ≫ F.into L = F.into l from hc]
    exact hx
  refine
    { app := fun a =>
        { f := fun n => ModuleCat.ofHom (((i.app a).f n).hom.restrict (hi a n))
          comm' := ?_ }
      comm_act := ?_ }
  · rename_i a
    intro n n' _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact CategoryTheory.congr_fun ((i.app a).comm n n') x.val
  · intro a b m n q h x f
    apply Subtype.ext
    exact i.comm_act m n q h x.val f

private theorem boundaryMap_selected_extend (D : GradedDecomposition F)
    (E : ClosedSelection D) (l : ℕ) (a : A.Obj) (n : ℤ)
    (z : CellTerm (selectedFamily D E l) a n) :
    boundaryMap (F.family l) a n
        (extendSum (k := k) (J := Selected E l)
          (V := fun i => ((cells (F.family l) i).complex a).X n) Subtype.val z) =
      (boundaryMap (selectedFamily D E l) a n z).val := by
  let J := Selected E l
  let V (i : F.index l) : Type v := ((cells (F.family l) i).complex a).X n
  let : DecidableEq J := Classical.decEq _
  let : DecidableEq (F.index l) := Classical.decEq _
  let L : CellTerm (selectedFamily D E l) a n →ₗ[k] CellTerm (F.family l) a n :=
    extendSum (k := k) (J := J) (V := fun i => ((cells (F.family l) i).complex a).X n) Subtype.val
  have h : (boundaryMap (F.family l) a n).comp L =
      (stageSupported D l E a (n+1)).subtype.comp (boundaryMap (selectedFamily D E l) a n) := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change boundaryMap (F.family l) a n
        (L (summand (cells (selectedFamily D E l)) a n i x)) =
      (boundaryMap (selectedFamily D E l) a n
        (summand (cells (selectedFamily D E l)) a n i x)).val
    have he : L (summand (cells (selectedFamily D E l)) a n i x) =
        summand (cells (F.family l)) a n i.val x :=
      extendSum_lof (V := V) Subtype.val i x
    exact (congrArg (boundaryMap (F.family l) a n) he).trans
      ((boundaryMap_summand (F.family l) a n i.val x).trans
        (congrArg Subtype.val (boundaryMap_summand (selectedFamily D E l) a n i x)).symm)
  exact DFunLike.congr_fun h z

set_option backward.isDefEq.respectTransparency false in
private theorem boundaryMap_selected (D : GradedDecomposition F)
    (E : ClosedSelection D) (l : ℕ) (a : A.Obj) (n : ℤ)
    (x : stageSupported D (l+1) E a n) :
    boundaryMap (F.family l) a n ((F.extension l).coordinates a n x.val).2 =
      (boundaryMap (selectedFamily D E l) a n (selectedCoordinates D E l a n x).2).val := by
  let f : Selected E l → F.index l := Subtype.val
  let V (i : F.index l) : Type v := ((cells (F.family l) i).complex a).X n
  let z := (selectedCoordinates D E l a n x).2
  suffices he : extendSum (k := k) (V := fun i => ((cells (F.family l) i).complex a).X n)
      f z = ((F.extension l).coordinates a n x.val).2 by
    exact (congrArg (boundaryMap (F.family l) a n) he.symm).trans
      (boundaryMap_selected_extend D E l a n z)
  apply DFinsupp.ext
  intro i
  by_cases hi : Sigma.mk l i ∈ E.val
  · exact extendSum_apply (V := V) f Subtype.val_injective z ⟨i,hi⟩
  · have hr : i ∉ Set.range f := by
      rintro ⟨j,hj⟩
      exact hi (hj ▸ j.property)
    exact (extendSum_off_range (V := V) f z hr).trans
      (((coordinates_old_supported_iff D E l a n x.val).mp x.property).2 i hi).symm

set_option backward.isDefEq.respectTransparency false in
private def selectedAttachment (D : GradedDecomposition F) (E : ClosedSelection D) (l : ℕ) :
    Attachment (selectedFamily D E l) (supportedModule D (l+1) E) where
  inclusion := supportedStageInclusion D E (Nat.le_succ l)
  coordinates := selectedCoordinates D E l
  coordinate_inclusion a n x := by
    have hs : CellReindex.stageInclusion F (Nat.le_succ l) = (F.extension l).inclusion :=
      Functor.OfSequence.map_le_succ _ l
    have hc :
        ((F.extension l).coordinates a n
          (((supportedStageInclusion D E (Nat.le_succ l)).app a).f n x).val) = (x.val, 0) := by
      change (F.extension l).coordinates a n
        (((CellReindex.stageInclusion F (Nat.le_succ l)).app a).f n x.val) = _
      rw [hs, (F.extension l).coordinate_inclusion]
    refine Prod.ext (Subtype.ext (congrArg Prod.fst hc)) ?_
    apply DFinsupp.ext
    intro i
    exact congrArg (fun y : _ × CellTerm (F.family l) a n => y.2 i.val) hc
  coordinate_d a n x := by
    have hc := (F.extension l).coordinate_d a n x.val
    dsimp only at hc ⊢
    constructor
    · apply Subtype.ext
      exact hc.1.trans (congrArg (fun z =>
          ((F.stage l).complex a).d n (n+1) ((F.extension l).coordinates a n x.val).1 + z)
        (boundaryMap_selected D E l a n x))
    · intro i
      exact hc.2 i.val
  coordinate_act m n q h x f := by
    have hc := (F.extension l).coordinate_act m n q h x.val f
    dsimp only at hc ⊢
    exact ⟨Subtype.ext hc.1, fun i => hc.2 i.val⟩

private def decodeAt (D : GradedDecomposition F) (N : ℕ) (a : A.Obj) (n : ℤ) :
    (M.complex a).X n →ₗ[k] ((F.stage N).complex a).X n :=
  (stageDecoding F N a n).comp ((restrictStage F N a n).comp (D.coordinates a n).toLinearMap)

private theorem decodeAt_correct (D : GradedDecomposition F) (N : ℕ) (E : ClosedCells D N)
    (a : A.Obj) (n : ℤ) (x : (M.complex a).X n) (hx : IsSupported D E.val a n x) :
    ((F.into N).app a).f n (decodeAt D N a n x) = x := by
  have hz : ∀ s : CellIndex F, N ≤ s.1 → D.coordinates a n x s = 0 :=
    fun s hs => hx s (fun he => Nat.not_lt_of_ge hs (E.property.2 s he))
  rw [show decodeAt D N a n x = stageDecoding F N a n (restrictStage F N a n
      (D.coordinates a n x)) from rfl, ← moduleDecoding_extendStage,
    extendStage_restrictStage F N a n _ hz]
  obtain ⟨l,y,hy⟩ := F.exhaustive a n x
  rw [← hy, coordinates_into, moduleDecoding_stageEncoding]

private def supportedInto (D : GradedDecomposition F) (N : ℕ) (E : ClosedSelection D) :
    supportedModule D N E ⟶ M :=
  supportedInclusion D N E ≫ F.into N

private theorem supportedInto_injective (D : GradedDecomposition F) (N : ℕ)
    (E : ClosedSelection D) (a : A.Obj) (n : ℤ) :
    Function.Injective (((supportedInto D N E).app a).f n) :=
  (F.injective N a n).comp Subtype.val_injective

private theorem strict_hom_ext {P Q : RightDGModuleModel A} {f g : P ⟶ Q}
    (h : ∀ a n x, (f.app a).f n x = (g.app a).f n x) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact LinearMap.ext (h a n)

private theorem supportedStageInclusion_into (D : GradedDecomposition F)
    (E : ClosedSelection D) {l L : ℕ} (h : l ≤ L) :
    supportedStageInclusion D E h ≫ supportedInto D L E = supportedInto D l E := by
  apply strict_hom_ext
  intro a n x
  exact congrArg (fun g : F.stage l ⟶ M => (g.app a).f n x.val) (stageInclusion_into F h)

private def mapToSupported {P : RightDGModuleModel A} (D : GradedDecomposition F)
    (N : ℕ) (E : ClosedCells D N) (g : P ⟶ M)
    (hg : ∀ a n x, IsSupported D E.val a n ((g.app a).f n x)) :
    P ⟶ supportedModule D N ⟨E.val, E.property.1⟩ := by
  let i := supportedInto D N ⟨E.val, E.property.1⟩
  let q (a : A.Obj) (n : ℤ) :
      (P.complex a).X n →ₗ[k] stageSupported D N ⟨E.val, E.property.1⟩ a n :=
    LinearMap.codRestrict _ ((decodeAt D N a n).comp ((g.app a).f n).hom) (fun x => by
      change IsSupported D E.val a n (((F.into N).app a).f n
        (decodeAt D N a n ((g.app a).f n x)))
      rw [decodeAt_correct D N E a n _ (hg a n x)]
      exact hg a n x)
  have hq (a : A.Obj) (n : ℤ) (x : (P.complex a).X n) :
      (i.app a).f n (q a n x) = (g.app a).f n x :=
    decodeAt_correct D N E a n _ (hg a n x)
  have hi := supportedInto_injective D N ⟨E.val, E.property.1⟩
  refine
    { app := fun a =>
        { f := fun n => ModuleCat.ofHom (q a n)
          comm' := ?_ }
      comm_act := ?_ }
  · rename_i a
    intro n n' _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply hi a n'
    have h₁ := CategoryTheory.congr_fun ((i.app a).comm n n') (q a n x)
    have h₂ := CategoryTheory.congr_fun ((g.app a).comm n n') x
    change (M.complex a).d n n' ((i.app a).f n (q a n x)) =
      (i.app a).f n' (((supportedModule D N ⟨E.val, E.property.1⟩).complex a).d n n'
        (q a n x)) at h₁
    change (M.complex a).d n n' ((g.app a).f n x) =
      (g.app a).f n' ((P.complex a).d n n' x) at h₂
    change (i.app a).f n' (((supportedModule D N ⟨E.val, E.property.1⟩).complex a).d n n'
      (q a n x)) = (i.app a).f n' (q a n' ((P.complex a).d n n' x))
    rw [← h₁, hq, hq, h₂]
  · intro a b m n q' h x f
    apply hi a q'
    change (i.app a).f q' (q a q' (P.act m n q' h x f)) =
      (i.app a).f q' ((supportedModule D N ⟨E.val, E.property.1⟩).act
        m n q' h (q b m x) f)
    have hact := i.comm_act m n q' h (q b m x) f
    rw [hq] at hact
    exact (hq a q' _).trans ((g.comm_act m n q' h x f).trans hact.symm)

private theorem mapToSupported_into {P : RightDGModuleModel A} (D : GradedDecomposition F)
    (N : ℕ) (E : ClosedCells D N) (g : P ⟶ M)
    (hg : ∀ a n x, IsSupported D E.val a n ((g.app a).f n x)) :
    mapToSupported D N E g hg ≫ supportedInto D N ⟨E.val, E.property.1⟩ = g := by
  apply strict_hom_ext
  intro a n x
  exact decodeAt_correct D N E a n _ (hg a n x)

private def finitePresentation (D : GradedDecomposition F) (N : ℕ) (E : ClosedCells D N) :
    Presentation.{u,v,w,j} (supportedModule D N ⟨E.val, E.property.1⟩) := by
  let S : ClosedSelection D := ⟨E.val, E.property.1⟩
  let g := supportedInto D N S
  let i (l : ℕ) := mapToSupported D N E (supportedInto D l S) (fun _ _ x => x.property)
  have hi (l : ℕ) : i l ≫ g = supportedInto D l S :=
    mapToSupported_into D N E _ _
  refine
    { stage := fun l => supportedModule D l S
      bottom := fun a n x => Subtype.ext (F.bottom a n x.val)
      index := Selected S
      family := selectedFamily D S
      extension := selectedAttachment D S
      into := i
      compatible := ?_
      injective := ?_
      exhaustive := ?_ }
  · intro l
    have hc : ((selectedAttachment D S l).inclusion ≫ i (l+1)) ≫ g = i l ≫ g := by
      rw [Category.assoc, hi, hi]
      exact supportedStageInclusion_into D S (Nat.le_succ l)
    apply strict_hom_ext
    intro a n x
    apply supportedInto_injective D N S a n
    exact congrArg (fun m : supportedModule D l S ⟶ M => (m.app a).f n x) hc
  · intro l a n x y h
    apply supportedInto_injective D l S a n
    rw [← hi l]
    exact congrArg ((g.app a).f n) h
  · intro a n x
    refine ⟨N,x,?_⟩
    apply supportedInto_injective D N S a n
    exact congrArg (fun m : supportedModule D N S ⟶ M => (m.app a).f n x) (hi N)

private theorem finitePresentation_finite (D : GradedDecomposition F) (N : ℕ)
    (E : ClosedCells D N) : Finite (Σ l, (finitePresentation D N E).index l) := by
  let S : ClosedSelection D := ⟨E.val, E.property.1⟩
  change Finite (Σ l, Selected S l)
  let f (s : Σ l, Selected S l) : ↥E.val := ⟨⟨s.1,s.2.val⟩, s.2.property⟩
  apply Finite.of_injective f
  rintro ⟨l,i⟩ ⟨l',i'⟩ h
  have h' := congrArg Subtype.val h
  have hlevel : l = l' := congrArg Sigma.fst h'
  subst l'
  exact congrArg (Sigma.mk l) (Subtype.ext (Sigma.mk.inj_iff.mp h').2.eq)

private theorem supportedModule_finiteCell (D : GradedDecomposition F) (N : ℕ)
    (E : ClosedCells D N) : IndexedSemiFree.finiteCell (supportedModule D N ⟨E.val, E.property.1⟩) := by
  obtain ⟨R,hR⟩ := DerivedFormalization.DG.CellReindex.normalize (finitePresentation D N E)
  exact ⟨R.toPresentation, hR (finitePresentation_finite D N E)⟩

theorem stageSubmodulesExist : StageSubmodulesExist.{u,v,w,j} := by
  intro k _ A M F D N
  exact ⟨stageSubmodules D N, supportedModule_finiteCell D N⟩


section FilteredHom

universe i d

variable {J : Type i} [Preorder J]

private abbrev coconeMap {G : J ⥤ AddCommGrpCat.{d}} (c : Cocone G) (j : J) :
    G.obj j ⟶ c.pt := c.ι.app j

private def HasRepresentatives {G : J ⥤ AddCommGrpCat.{d}} (c : Cocone G) : Prop :=
  (∀ x : c.pt, ∃ j y, coconeMap c j y = x) ∧
    ∀ (j : J) (y : G.obj j), coconeMap c j y = 0 → ∃ (k : J) (p : j ⟶ k), G.map p y = 0

private theorem cocone_apply {G : J ⥤ AddCommGrpCat.{d}} (c : Cocone G)
    {j k : J} (p : j ⟶ k) (y : G.obj j) :
    coconeMap c k (G.map p y) = coconeMap c j y := by
  have h := c.ι.naturality p
  change G.map p ≫ coconeMap c k = coconeMap c j ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  exact CategoryTheory.congr_fun h y

private theorem natTrans_apply {G H : J ⥤ AddCommGrpCat.{d}} (a : G ⟶ H)
    {j k : J} (p : j ⟶ k) (y : G.obj j) :
    a.app k (G.map p y) = H.map p (a.app j y) :=
  CategoryTheory.congr_fun (a.naturality p) y

private def isColimitOfRepresentatives {G : J ⥤ AddCommGrpCat.{d}} (c : Cocone G)
    (hJ : Directed (· ≤ ·) (fun j : J => j)) (hc : HasRepresentatives c) :
    IsColimit c := by
  classical
  let j (x : c.pt) := (hc.1 x).choose
  let b (x : c.pt) : G.obj (j x) := (hc.1 x).choose_spec.choose
  have hb (x : c.pt) : coconeMap c (j x) (b x) = x := (hc.1 x).choose_spec.choose_spec
  let lift (s : Cocone G) (x : c.pt) := coconeMap s (j x) (b x)
  have lift_ι (s : Cocone G) (l : J) (y : G.obj l) :
      lift s (coconeMap c l y) = coconeMap s l y := by
    let x := coconeMap c l y
    obtain ⟨m,hm₁,hm₂⟩ := hJ (j x) l
    let z := G.map (homOfLE hm₁) (b x) - G.map (homOfLE hm₂) y
    have hz : coconeMap c m z = 0 := by
      change coconeMap c m (G.map (homOfLE hm₁) (b x) - G.map (homOfLE hm₂) y) = 0
      rw [map_sub, cocone_apply, cocone_apply, hb, sub_self]
    obtain ⟨q,p,hp⟩ := hc.2 m z hz
    have he : G.map p (G.map (homOfLE hm₁) (b x)) =
        G.map p (G.map (homOfLE hm₂) y) := by
      change G.map p (G.map (homOfLE hm₁) (b x) - G.map (homOfLE hm₂) y) = 0 at hp
      rwa [map_sub, sub_eq_zero] at hp
    change coconeMap s (j x) (b x) = coconeMap s l y
    rw [← cocone_apply s (homOfLE hm₁) (b x), ← cocone_apply s (homOfLE hm₂) y,
      ← cocone_apply s p, ← cocone_apply s p, he]
  let desc (s : Cocone G) : c.pt →+ s.pt :=
    { toFun := lift s
      map_zero' := by
        have h := lift_ι s (j 0) (0 : G.obj (j 0))
        simpa only [map_zero] using h
      map_add' x y := by
        obtain ⟨l,hx,hy⟩ := hJ (j x) (j y)
        let x' := G.map (homOfLE hx) (b x)
        let y' := G.map (homOfLE hy) (b y)
        have hx' : coconeMap c l x' = x := (cocone_apply c (homOfLE hx) (b x)).trans (hb x)
        have hy' : coconeMap c l y' = y := (cocone_apply c (homOfLE hy) (b y)).trans (hb y)
        have hxy : coconeMap c l (x' + y') = x + y := by rw [map_add, hx', hy']
        rw [← hxy, lift_ι, map_add, ← hx', ← hy', lift_ι, lift_ι] }
  exact
    { desc := fun s => AddCommGrpCat.ofHom (desc s)
      fac := fun s l => by
        apply ConcreteCategory.hom_ext
        intro y
        exact lift_ι s l y
      uniq := fun s m hm => by
        apply ConcreteCategory.hom_ext
        intro x
        change m x = lift s x
        exact (congrArg m (hb x).symm).trans (CategoryTheory.congr_fun (hm (j x)) (b x)) }

/-- The elementwise five-term argument for a directed colimit of additive Hom
groups. Surjectivity and eventual vanishing pass to the middle term. -/
private theorem representatives_of_exact_five
    {G₀ G₁ G₂ G₃ G₄ : J ⥤ AddCommGrpCat.{d}}
    (c₀ : Cocone G₀) (c₁ : Cocone G₁) (c₂ : Cocone G₂)
    (c₃ : Cocone G₃) (c₄ : Cocone G₄)
    (a : G₀ ⟶ G₁) (b : G₁ ⟶ G₂) (c : G₂ ⟶ G₃) (e : G₃ ⟶ G₄)
    (a' : c₀.pt ⟶ c₁.pt) (b' : c₁.pt ⟶ c₂.pt)
    (c' : c₂.pt ⟶ c₃.pt) (e' : c₃.pt ⟶ c₄.pt)
    (ha : ∀ j y, coconeMap c₁ j (a.app j y) = a' (coconeMap c₀ j y))
    (hb : ∀ j y, coconeMap c₂ j (b.app j y) = b' (coconeMap c₁ j y))
    (hc : ∀ j y, coconeMap c₃ j (c.app j y) = c' (coconeMap c₂ j y))
    (he : ∀ j y, coconeMap c₄ j (e.app j y) = e' (coconeMap c₃ j y))
    (ex₁ : ∀ j, Function.Exact (a.app j) (b.app j))
    (ex₂ : ∀ j, Function.Exact (b.app j) (c.app j))
    (ex₃ : ∀ j, Function.Exact (c.app j) (e.app j))
    (ex₁' : Function.Exact a' b') (ex₂' : Function.Exact b' c')
    (ex₃' : Function.Exact c' e')
    (hJ : Directed (· ≤ ·) (fun j : J => j))
    (h₀ : HasRepresentatives c₀) (h₁ : HasRepresentatives c₁)
    (h₃ : HasRepresentatives c₃) (h₄ : HasRepresentatives c₄) :
    HasRepresentatives c₂ := by
  constructor
  · intro x
    obtain ⟨j,y,hy⟩ := h₃.1 (c' x)
    have hy₀ : coconeMap c₄ j (e.app j y) = 0 := by
      rw [he, hy]
      exact (ex₃' (c' x)).mpr ⟨x,rfl⟩
    obtain ⟨k,p,hp⟩ := h₄.2 j (e.app j y) hy₀
    have hk : e.app k (G₃.map p y) = 0 := (natTrans_apply e p y).trans hp
    obtain ⟨z,hz⟩ := (ex₃ k (G₃.map p y)).mp hk
    have hdiff : c' (x - coconeMap c₂ k z) = 0 := by
      rw [map_sub, ← hc, hz, cocone_apply, hy, sub_self]
    obtain ⟨w,hw⟩ := (ex₂' _).mp hdiff
    obtain ⟨l,v,hv⟩ := h₁.1 w
    obtain ⟨m,hm₁,hm₂⟩ := hJ k l
    refine ⟨m, G₂.map (homOfLE hm₁) z + G₂.map (homOfLE hm₂) (b.app l v), ?_⟩
    rw [map_add, cocone_apply, cocone_apply, hb, hv, hw]
    abel
  · intro j y hy
    have hy₀ : coconeMap c₃ j (c.app j y) = 0 := by rw [hc, hy, map_zero]
    obtain ⟨k,p,hp⟩ := h₃.2 j (c.app j y) hy₀
    have hk : c.app k (G₂.map p y) = 0 := (natTrans_apply c p y).trans hp
    obtain ⟨z,hz⟩ := (ex₂ k (G₂.map p y)).mp hk
    have hz₀ : b' (coconeMap c₁ k z) = 0 := by
      rw [← hb, hz, cocone_apply, hy]
    obtain ⟨w,hw⟩ := (ex₁' _).mp hz₀
    obtain ⟨l,v,hv⟩ := h₀.1 w
    obtain ⟨m,hm₁,hm₂⟩ := hJ k l
    let z' := G₁.map (homOfLE hm₁) z - G₁.map (homOfLE hm₂) (a.app l v)
    have hz' : coconeMap c₁ m z' = 0 := by
      change coconeMap c₁ m (G₁.map (homOfLE hm₁) z - G₁.map (homOfLE hm₂) (a.app l v)) = 0
      rw [map_sub, cocone_apply, cocone_apply, ha, hv, hw, sub_self]
    obtain ⟨q,r,hr⟩ := h₁.2 m z' hz'
    have ha₀ : b.app l (a.app l v) = 0 := (ex₁ l _).mpr ⟨v,rfl⟩
    have hmid : b.app m z' = G₂.map (homOfLE hm₁) (G₂.map p y) := by
      change b.app m (G₁.map (homOfLE hm₁) z - G₁.map (homOfLE hm₂) (a.app l v)) = _
      rw [map_sub, natTrans_apply, natTrans_apply, hz, ha₀, map_zero, sub_zero]
    refine ⟨q, p ≫ homOfLE hm₁ ≫ r, ?_⟩
    rw [← Category.assoc, G₂.map_comp, G₂.map_comp]
    change G₂.map r (G₂.map (homOfLE hm₁) (G₂.map p y)) = 0
    rw [← hmid, ← natTrans_apply, hr, map_zero]

end FilteredHom

section Quotients

variable {P Q : RightDGModuleModel A} {I : Type j}

private abbrev attachmentSum {C : IndexedSemiFree.CellFamily P I} (E : Attachment C Q) :=
  _root_.DerivedFormalization.DG.IndexedSums.sum (cells C) (_root_.DerivedFormalization.DG.IndexedCellAttachment.termsSmall E)

private def attachmentSumRealization {C : IndexedSemiFree.CellFamily P I} (E : Attachment C Q) :
    StrictSum (cells C) (attachmentSum E) :=
  _root_.DerivedFormalization.DG.IndexedSums.sumRealization (cells C) (_root_.DerivedFormalization.DG.IndexedCellAttachment.termsSmall E)

private abbrev attachmentProjection {C : IndexedSemiFree.CellFamily P I} (E : Attachment C Q) :=
  _root_.DerivedFormalization.DG.IndexedCellAttachment.projection E (attachmentSumRealization E)

private theorem attachmentInclusion_injective {C : IndexedSemiFree.CellFamily P I}
    (E : Attachment C Q) (a : A.Obj) (n : ℤ) :
    Function.Injective ((E.inclusion.app a).f n) := by
  intro x y h
  have hc := congrArg (E.coordinates a n) h
  rw [E.coordinate_inclusion, E.coordinate_inclusion] at hc
  exact congrArg Prod.fst hc

private def mapSum {J : Type*} {W : I → RightDGModuleModel A}
    {S T : RightDGModuleModel A} (f : J → I)
    (a : StrictSum (fun i => W (f i)) S) (b : StrictSum W T) : S ⟶ T :=
  _root_.DerivedFormalization.DG.IndexedSums.desc a (fun i => b.inclusion (f i))

private theorem mapSum_inclusion {J : Type*} {W : I → RightDGModuleModel A}
    {S T : RightDGModuleModel A} (f : J → I)
    (a : StrictSum (fun i => W (f i)) S) (b : StrictSum W T) (i : J) :
    a.inclusion i ≫ mapSum f a b = b.inclusion (f i) :=
  _root_.DerivedFormalization.DG.IndexedSums.inclusion_desc a _ i

private theorem mapSum_coordinates {J : Type*} {W : I → RightDGModuleModel A}
    {S T : RightDGModuleModel A} (f : J → I)
    (a : StrictSum (fun i => W (f i)) S) (b : StrictSum W T)
    (o : A.Obj) (n : ℤ) (x : (S.complex o).X n) :
    b.coordinates o n (((mapSum f a b).app o).f n x) =
      extendSum (k := k) (V := fun i => ((W i).complex o).X n) f (a.coordinates o n x) := by
  let V (i : I) : Type v := ((W i).complex o).X n
  let z := mapSum f a b
  have h : (b.coordinates o n).toLinearMap.comp ((z.app o).f n).hom =
      (extendSum (k := k) (V := V) f).comp (a.coordinates o n).toLinearMap := by
    apply term_hom_ext a o n
    intro i y
    change b.coordinates o n ((z.app o).f n (((a.inclusion i).app o).f n y)) =
      extendSum f (a.coordinates o n (((a.inclusion i).app o).f n y))
    have hi := congrArg (fun c : W (f i) ⟶ T => (c.app o).f n y) (mapSum_inclusion f a b i)
    change (z.app o).f n (((a.inclusion i).app o).f n y) = ((b.inclusion (f i)).app o).f n y at hi
    rw [hi, b.coordinate_inclusion, a.coordinate_inclusion]
    exact (extendSum_lof (V := V) f i y).symm
  exact DFunLike.congr_fun h x

private def selectedQuotientInclusion (D : GradedDecomposition F) (E : ClosedSelection D) (l : ℕ) :
    attachmentSum (selectedAttachment D E l) ⟶ attachmentSum (F.extension l) :=
  mapSum (fun i : Selected E l => i.val)
    (attachmentSumRealization (selectedAttachment D E l)) (attachmentSumRealization (F.extension l))

private theorem selectedQuotientInclusion_projection (D : GradedDecomposition F)
    (E : ClosedSelection D) (l : ℕ) :
    attachmentProjection (selectedAttachment D E l) ≫ selectedQuotientInclusion D E l =
      supportedInclusion D (l+1) E ≫ attachmentProjection (F.extension l) := by
  let s := attachmentSumRealization (F.extension l)
  apply strict_hom_ext
  intro a n x
  apply (s.coordinates a n).injective
  change s.coordinates a n (((selectedQuotientInclusion D E l).app a).f n
      (((attachmentProjection (selectedAttachment D E l)).app a).f n x)) =
    s.coordinates a n (((attachmentProjection (F.extension l)).app a).f n x.val)
  unfold selectedQuotientInclusion
  rw [mapSum_coordinates, _root_.DerivedFormalization.DG.IndexedCellAttachment.projection_coordinates,
    _root_.DerivedFormalization.DG.IndexedCellAttachment.projection_coordinates]
  let V (i : F.index l) : Type v := ((cells (F.family l) i).complex a).X n
  let z := (selectedCoordinates D E l a n x).2
  change extendSum (k := k) (V := V) (fun i : Selected E l => i.val) z =
    ((F.extension l).coordinates a n x.val).2
  apply DFinsupp.ext
  intro i
  by_cases hi : Sigma.mk l i ∈ E.val
  · exact extendSum_apply (V := V) Subtype.val Subtype.val_injective z ⟨i,hi⟩
  · have hr : i ∉ Set.range (Subtype.val : Selected E l → F.index l) := by
      rintro ⟨j,hj⟩
      exact hi (hj ▸ j.property)
    exact (extendSum_off_range (V := V) Subtype.val z hr).trans
      (((coordinates_old_supported_iff D E l a n x.val).mp x.property).2 i hi).symm

private theorem selectedQuotientInclusion_injective (D : GradedDecomposition F)
    (E : ClosedSelection D) (l : ℕ) (a : A.Obj) (n : ℤ) :
    Function.Injective (((selectedQuotientInclusion D E l).app a).f n) := by
  intro x y h
  let s := attachmentSumRealization (selectedAttachment D E l)
  let t := attachmentSumRealization (F.extension l)
  have hc := congrArg (t.coordinates a n) h
  change t.coordinates a n (((selectedQuotientInclusion D E l).app a).f n x) =
    t.coordinates a n (((selectedQuotientInclusion D E l).app a).f n y) at hc
  unfold selectedQuotientInclusion at hc
  rw [mapSum_coordinates, mapSum_coordinates] at hc
  apply (s.coordinates a n).injective
  apply DFinsupp.ext
  intro i
  let V (i : F.index l) : Type v := ((cells (F.family l) i).complex a).X n
  exact (extendSum_apply (V := V) Subtype.val Subtype.val_injective (s.coordinates a n x) i).symm.trans
    ((congrArg (fun z : CellTerm (F.family l) a n => z i.val) hc).trans
      (extendSum_apply (V := V) Subtype.val Subtype.val_injective (s.coordinates a n y) i))

private def selectedQuotientTransition (D : GradedDecomposition F)
    {E G : ClosedSelection D} (h : E.val ⊆ G.val) (l : ℕ) :
    attachmentSum (selectedAttachment D E l) ⟶ attachmentSum (selectedAttachment D G l) :=
  mapSum (fun i : Selected E l => (⟨i.val, h i.property⟩ : Selected G l))
    (attachmentSumRealization (selectedAttachment D E l))
    (attachmentSumRealization (selectedAttachment D G l))

private theorem selectedQuotientInclusion_onSummand (D : GradedDecomposition F)
    (E : ClosedSelection D) (l : ℕ) (i : Selected E l) :
    (attachmentSumRealization (selectedAttachment D E l)).inclusion i ≫
        selectedQuotientInclusion D E l =
      (attachmentSumRealization (F.extension l)).inclusion i.val :=
  _root_.DerivedFormalization.DG.IndexedSums.inclusion_desc
    (attachmentSumRealization (selectedAttachment D E l))
    (fun i => (attachmentSumRealization (F.extension l)).inclusion i.val) i

private theorem selectedQuotientTransition_onSummand (D : GradedDecomposition F)
    {E G : ClosedSelection D} (h : E.val ⊆ G.val) (l : ℕ) (i : Selected E l) :
    (attachmentSumRealization (selectedAttachment D E l)).inclusion i ≫
        selectedQuotientTransition D h l =
      (attachmentSumRealization (selectedAttachment D G l)).inclusion ⟨i.val, h i.property⟩ :=
  _root_.DerivedFormalization.DG.IndexedSums.inclusion_desc
    (attachmentSumRealization (selectedAttachment D E l))
    (fun i => (attachmentSumRealization (selectedAttachment D G l)).inclusion ⟨i.val, h i.property⟩) i

private theorem selectedQuotientTransition_comp (D : GradedDecomposition F)
    {E G : ClosedSelection D} (h : E.val ⊆ G.val) (l : ℕ) :
    selectedQuotientTransition D h l ≫ selectedQuotientInclusion D G l =
      selectedQuotientInclusion D E l := by
  apply _root_.DerivedFormalization.DG.IndexedSums.hom_ext (attachmentSumRealization (selectedAttachment D E l))
  intro i
  rw [← Category.assoc, selectedQuotientTransition_onSummand,
    selectedQuotientInclusion_onSummand, selectedQuotientInclusion_onSummand]

private theorem selectedQuotientTransition_natural (D : GradedDecomposition F)
    {E G : ClosedSelection D} (h : E ≤ G) (l : ℕ) :
    supportedTransition D (l+1) h ≫ attachmentProjection (selectedAttachment D G l) =
      attachmentProjection (selectedAttachment D E l) ≫ selectedQuotientTransition D h l := by
  have hs : supportedTransition D (l+1) h ≫ supportedInclusion D (l+1) G =
      supportedInclusion D (l+1) E := by
    apply strict_hom_ext
    intro a n x
    rfl
  have hc :
      (supportedTransition D (l+1) h ≫ attachmentProjection (selectedAttachment D G l)) ≫
        selectedQuotientInclusion D G l =
      (attachmentProjection (selectedAttachment D E l) ≫ selectedQuotientTransition D h l) ≫
        selectedQuotientInclusion D G l := by
    rw [Category.assoc, Category.assoc, selectedQuotientTransition_comp,
      selectedQuotientInclusion_projection, selectedQuotientInclusion_projection, ← Category.assoc, hs]
  apply strict_hom_ext
  intro a n x
  apply selectedQuotientInclusion_injective D G l a n
  exact congrArg (fun f : supportedModule D (l+1) E ⟶ attachmentSum (F.extension l) =>
    (f.app a).f n x) hc

private def quotientDiagram (D : GradedDecomposition F) (N l : ℕ) :
    ClosedCells D N ⥤ RightDGModuleModel A where
  obj E := attachmentSum (selectedAttachment D ⟨E.val, E.property.1⟩ l)
  map f := selectedQuotientTransition D f.le l
  map_id E := by
    apply _root_.DerivedFormalization.DG.IndexedSums.hom_ext (attachmentSumRealization (selectedAttachment D ⟨E.val, E.property.1⟩ l))
    intro i
    rw [selectedQuotientTransition_onSummand, Category.comp_id]
  map_comp {E G H} f g := by
    apply _root_.DerivedFormalization.DG.IndexedSums.hom_ext (attachmentSumRealization (selectedAttachment D ⟨E.val, E.property.1⟩ l))
    intro i
    rw [← Category.assoc, selectedQuotientTransition_onSummand,
      selectedQuotientTransition_onSummand, selectedQuotientTransition_onSummand]

private def quotientCocone (D : GradedDecomposition F) (N l : ℕ) :
    Cocone (quotientDiagram D N l) where
  pt := attachmentSum (F.extension l)
  ι :=
    { app := fun E => selectedQuotientInclusion D ⟨E.val, E.property.1⟩ l
      naturality := by
        intro E G f
        change selectedQuotientTransition D f.le l ≫ selectedQuotientInclusion D ⟨G.val, G.property.1⟩ l =
          selectedQuotientInclusion D ⟨E.val, E.property.1⟩ l ≫ 𝟙 _
        rw [Category.comp_id]
        exact selectedQuotientTransition_comp D f.le l }

end Quotients

section CompactCoproduct

universe o m i

variable {R : Type o} [Category.{m} R] [Preadditive R]
variable {J : Type i} [Preorder J] {I : Type j}

private theorem compactCoproduct_representatives {W : I → R} (P : R)
    (hP : CompactRepresentables.IsCompact.{j,_,_} P)
    {G : J ⥤ R} (c : Cocone G)
    (S : J → Set I) (hcover : ∀ U : Finset I, ∃ a, ∀ s ∈ U, s ∈ S a)
    (inj : ∀ i, W i ⟶ c.pt) (hc : IsColimit (Cofan.mk c.pt inj))
    (inj' : ∀ (a : J) (i : S a), W i.val ⟶ G.obj a)
    (hc' : ∀ a, IsColimit (Cofan.mk (G.obj a) (inj' a)))
    (fac : ∀ (a : J) (i : S a), inj' a i ≫ c.ι.app a = inj i.val) :
    HasRepresentatives ((preadditiveCoyoneda.obj ⟨P⟩).mapCocone c) := by
  classical
  constructor
  · intro x
    obtain ⟨y, hy⟩ := (hP (Cofan.mk c.pt inj) hc).surjective x
    obtain ⟨a,ha⟩ := hcover y.support
    let z : P ⟶ G.obj a := ∑ i ∈ y.support.attach, y i.val ≫ inj' a ⟨i.val,ha i i.property⟩
    refine ⟨a,z,?_⟩
    change z ≫ c.ι.app a = x
    rw [← hy]
    have he := congrArg (CompactRepresentables.coproductHomMap P (Cofan.mk c.pt inj))
      (DirectSum.sum_support_of y)
    rw [← he, map_sum]
    unfold z
    rw [Preadditive.sum_comp]
    conv_rhs => rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Category.assoc, fac]
    exact (DirectSum.toAddMonoid_of (fun s => Preadditive.rightComp P (inj s)) i.val
      (y i.val)).symm
  · intro a y hy
    change P ⟶ G.obj a at y
    change y ≫ c.ι.app a = 0 at hy
    let ρ : c.pt ⟶ G.obj a := Cofan.IsColimit.desc hc
      (fun i => if h : i ∈ S a then inj' a ⟨i,h⟩ else 0)
    have hρ : c.ι.app a ≫ ρ = 𝟙 _ := by
      apply Cofan.IsColimit.hom_ext (hc' a)
      intro i
      change inj' a i ≫ c.ι.app a ≫ ρ = inj' a i ≫ 𝟙 _
      rw [← Category.assoc, fac, Category.comp_id]
      have hfac := Cofan.IsColimit.fac hc
        (fun i => if h : i ∈ S a then inj' a ⟨i,h⟩ else 0) i.val
      change inj i.val ≫ ρ = _ at hfac
      rw [hfac, dite_eq_left i.property]
    refine ⟨a,𝟙 _,?_⟩
    have h : y = 0 := calc
      y = y ≫ (c.ι.app a ≫ ρ) := by rw [hρ, Category.comp_id]
      _ = 0 := by rw [← Category.assoc, hy, zero_comp]
    subst y
    exact map_zero _

end CompactCoproduct

local instance homotopyCat : Category (HomComplex.homotopyCategory A) :=
  inferInstanceAs (Category (K A))

local instance derivedCat (h : Derived.HomotopyCategoryLaws A) :
    Category (Derived.derivedCategory A h) := DerivedKProjective.derivedCategoryInstance A h

section ConeQuotient

open CategoryTheory.Pretriangulated
open Specs.DerivedFormalization.DG.Telescope (coneComparison)

private structure IsStrictCokernel {P Q S : RightDGModuleModel A}
    (f : P ⟶ Q) (p : Q ⟶ S) : Prop where
  zero : f ≫ p = 0
  injective : ∀ a n, Function.Injective ((f.app a).f n)
  cokernel : Nonempty (IsColimit (CokernelCofork.ofπ p zero))

private theorem attachmentCokernel {P Q : RightDGModuleModel A} {I : Type j}
    {C : IndexedSemiFree.CellFamily P I} (E : Attachment C Q) :
    IsStrictCokernel E.inclusion (attachmentProjection E) :=
  ⟨_root_.DerivedFormalization.DG.IndexedCellAttachment.inclusion_projection E _,
    attachmentInclusion_injective E,
    ⟨_root_.DerivedFormalization.DG.IndexedCellAttachment.projectionIsCokernel E _⟩⟩

private theorem liftedCokernel {P Q : RightDGModuleModel A} {I : Type j}
    {C : IndexedSemiFree.CellFamily P I} (E : Attachment C Q) :
    let L := AmbientDerived.strictInput.{u,v,w,t} A
    IsStrictCokernel (L.map E.inclusion) (L.map (attachmentProjection E)) := by
  let L := AmbientDerived.strictInput.{u,v,w,t} A
  let H := _root_.DerivedFormalization.DG.IndexedCellAttachment.liftAttachment.{u,v,w,j,max w t} E
  let b := _root_.DerivedFormalization.DG.IndexedSums.liftStrictSum.{u,v,w,j,max w t}
    (attachmentSumRealization E)
  let p := _root_.DerivedFormalization.DG.IndexedCellAttachment.projection H b
  have hp : p = L.map (attachmentProjection E) := by
    apply strict_hom_ext
    intro a n x
    apply (b.coordinates a n).injective
    refine (_root_.DerivedFormalization.DG.IndexedCellAttachment.projection_coordinates H b a n x).trans ?_
    exact (congrArg (_root_.DerivedFormalization.DG.IndexedSums.liftTerm.{u,v,w,j,max w t}
      (cells C) a n) (_root_.DerivedFormalization.DG.IndexedCellAttachment.projection_coordinates
        E (attachmentSumRealization E) a n x.down)).symm
  change IsStrictCokernel H.inclusion (L.map (attachmentProjection E))
  rw [← hp]
  exact ⟨_root_.DerivedFormalization.DG.IndexedCellAttachment.inclusion_projection H b,
    attachmentInclusion_injective H,
    ⟨_root_.DerivedFormalization.DG.IndexedCellAttachment.projectionIsCokernel H b⟩⟩

variable (h : Derived.HomotopyCategoryLaws A)

private abbrev localizationQ (h : Derived.HomotopyCategoryLaws A) :
    HomComplex.homotopyCategory A ⥤ Derived.derivedCategory A h := Derived.quotient A h

private abbrev strictLocalization (h : Derived.HomotopyCategoryLaws A) :
    RightDGModuleModel A ⥤ (Derived.derivedCategory A h) :=
  toHomotopyCategory A ⋙ localizationQ h

variable [SK : HasShift (HomComplex.homotopyCategory A) ℤ] [SD : HasShift (Derived.derivedCategory A h) ℤ]
variable (hS : ∀ (P : (HomComplex.homotopyCategory A)) (n : ℤ), (shiftFunctor (HomComplex.homotopyCategory A) n).obj P = ShiftCone.shift P n)
variable [(localizationQ h).CommShift ℤ]

private abbrev localizationCone {P Q : RightDGModuleModel A} (f : P ⟶ Q) :
    Triangle (Derived.derivedCategory A h) :=
  (localizationQ h).mapTriangle.obj (DerivedTriangles.coneTriangle h SK (hS P 1) f)

private def coneQuotientIso {P Q S : RightDGModuleModel A}
    {f : P ⟶ Q} {p : Q ⟶ S} (hp : IsStrictCokernel f p) :
    (strictLocalization h).obj (ShiftCone.cone f) ≅ (strictLocalization h).obj S :=
  DerivedKProjective.replacementIso h (coneComparison f p hp.zero)
    (coneToCokernel f hp.injective p hp.zero hp.cokernel.some).2

private def cokernelTriangle {P Q S : RightDGModuleModel A}
    {f : P ⟶ Q} {p : Q ⟶ S} (hp : IsStrictCokernel f p) : Triangle (Derived.derivedCategory A h) :=
  Triangle.mk ((strictLocalization h).map f) ((strictLocalization h).map p)
    ((coneQuotientIso h hp).inv ≫ (localizationCone h hS f).mor₃)

set_option backward.isDefEq.respectTransparency false in
private def cokernelTriangleIso {P Q S : RightDGModuleModel A}
    {f : P ⟶ Q} {p : Q ⟶ S} (hp : IsStrictCokernel f p) :
    localizationCone h hS f ≅ cokernelTriangle h hS hp := by
  let e := coneQuotientIso h hp
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
  · change (strictLocalization h).map f ≫ 𝟙 _ = 𝟙 _ ≫ (strictLocalization h).map f
    simp
  · change (strictLocalization h).map (ShiftCone.coneInclusion f) ≫
      (strictLocalization h).map (coneComparison f p hp.zero) = 𝟙 _ ≫ (strictLocalization h).map p
    rw [← Functor.map_comp, Category.id_comp]
    rfl
  · change (localizationCone h hS f).mor₃ ≫ (shiftFunctor (Derived.derivedCategory A h) (1 : ℤ)).map (𝟙 _) =
      e.hom ≫ e.inv ≫ (localizationCone h hS f).mor₃
    have hm := (shiftFunctor (Derived.derivedCategory A h) (1 : ℤ)).map_id
      (localizationCone h hS f).obj₁
    exact (congrArg (fun g => (localizationCone h hS f).mor₃ ≫ g) hm).trans
      ((Category.comp_id _).trans (e.hom_inv_id_assoc _).symm)

variable [Preadditive (Derived.derivedCategory A h)] [HasZeroObject (Derived.derivedCategory A h)]
variable [∀ n : ℤ, (shiftFunctor (Derived.derivedCategory A h) n).Additive] [Pretriangulated (Derived.derivedCategory A h)]

private theorem cokernelTriangle_distinguished {P Q S : RightDGModuleModel A}
    {f : P ⟶ Q} {p : Q ⟶ S} (hp : IsStrictCokernel f p)
    (hf : localizationCone h hS f ∈ distTriang (Derived.derivedCategory A h)) :
    cokernelTriangle h hS hp ∈ distTriang (Derived.derivedCategory A h) :=
  isomorphic_distinguished _ hf _ (cokernelTriangleIso h hS hp).symm

local instance homotopyAdditive : Preadditive (HomComplex.homotopyCategory A) :=
  inferInstanceAs (Preadditive ((dgCategory A).H0))
variable (hMap : ∀ {M N : RightDGModuleModel A} (n : ℤ) (f : M ⟶ N),
  HEq ((shiftFunctor (HomComplex.homotopyCategory A) n).map (show @Quiver.Hom (HomComplex.homotopyCategory A) _ M N from HomComplex.homotopyClass f))
    (HomComplex.homotopyClass (ShiftCone.shiftMap n f)))

include hMap in
private theorem homotopyShift_natural {P P' : RightDGModuleModel A} (a : P ⟶ P') :
    (show @Quiver.Hom (HomComplex.homotopyCategory A) _ (ShiftCone.shift P 1) (ShiftCone.shift P' 1)
      from HomComplex.homotopyClass
      (ShiftCone.shiftMap 1 a)) ≫ eqToHom (hS P' 1).symm =
      eqToHom (hS P 1).symm ≫ (shiftFunctor (HomComplex.homotopyCategory A) (1 : ℤ)).map (HomComplex.homotopyClass a) := by
  let s := shiftFunctor (HomComplex.homotopyCategory A) (1 : ℤ)
  let f : @Quiver.Hom (HomComplex.homotopyCategory A) _ P P' := HomComplex.homotopyClass a
  let g : @Quiver.Hom (HomComplex.homotopyCategory A) _ (ShiftCone.shift P 1) (ShiftCone.shift P' 1) :=
    HomComplex.homotopyClass (ShiftCone.shiftMap 1 a)
  have e := (conj_eqToHom_iff_heq (s.map f) g (hS P 1) (hS P' 1)).mpr (hMap 1 a)
  change g ≫ eqToHom (hS P' 1).symm = eqToHom (hS P 1).symm ≫ s.map f
  rw [e, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

include hMap in
set_option backward.isDefEq.respectTransparency false in
private def strictConeTriangleMap {P Q P' Q' : RightDGModuleModel A}
    {f : P ⟶ Q} {g : P' ⟶ Q'}
    (a : P ⟶ P') (b : Q ⟶ Q') (e : f ≫ b = a ≫ g) :
    DerivedTriangles.coneTriangle h SK (hS P 1) f ⟶
      DerivedTriangles.coneTriangle h SK (hS P' 1) g := by
  let T : RightDGModuleModel A ⥤ (HomComplex.homotopyCategory A) := toHomotopyCategory A
  let z := strictConeMap f g a b e
  refine Triangle.homMk _ _ (T.map a) (T.map b) (T.map z) ?_ ?_ ?_
  · change T.map f ≫ T.map b = T.map a ≫ T.map g
    rw [← T.map_comp, ← T.map_comp, e]
  · change T.map (ShiftCone.coneInclusion f) ≫ T.map z =
      T.map b ≫ T.map (ShiftCone.coneInclusion g)
    rw [← T.map_comp, ← T.map_comp]
    congr 1
    apply strict_hom_ext
    intro o n x
    change (z.app o).f n (x,0) = ((b.app o).f n x, 0)
    rw [strictConeMap_apply, map_zero]
  · have hp : z ≫ ShiftCone.coneProjection g =
        ShiftCone.coneProjection f ≫ ShiftCone.shiftMap 1 a := by
      apply strict_hom_ext
      intro o n x
      change ((z.app o).f n x).2 = _
      rw [strictConeMap_apply]
      rfl
    have hs : T.map (ShiftCone.shiftMap 1 a) ≫ eqToHom (hS P' 1).symm =
        eqToHom (hS P 1).symm ≫ (shiftFunctor (HomComplex.homotopyCategory A) (1 : ℤ)).map (T.map a) :=
      homotopyShift_natural hS hMap a
    change (-(T.map (ShiftCone.coneProjection f) ≫ eqToHom (hS P 1).symm)) ≫
      (shiftFunctor (HomComplex.homotopyCategory A) (1 : ℤ)).map (T.map a) =
      T.map z ≫ (-(T.map (ShiftCone.coneProjection g) ≫ eqToHom (hS P' 1).symm))
    rw [Preadditive.neg_comp, Preadditive.comp_neg]
    congr 1
    rw [Category.assoc, ← hs, ← Category.assoc, ← Category.assoc, ← T.map_comp, ← T.map_comp, hp]

include hMap in
private def cokernelTriangleMap {P Q S P' Q' S' : RightDGModuleModel A}
    {f : P ⟶ Q} {p : Q ⟶ S} {g : P' ⟶ Q'} {q : Q' ⟶ S'}
    (hp : IsStrictCokernel f p) (hq : IsStrictCokernel g q)
    (a : P ⟶ P') (b : Q ⟶ Q') (c : S ⟶ S')
    (ef : f ≫ b = a ≫ g) (ep : p ≫ c = b ≫ q) :
    cokernelTriangle h hS hp ⟶ cokernelTriangle h hS hq := by
  let V := strictLocalization h
  let z := strictConeMap f g a b ef
  let e₁ := coneQuotientIso h hp
  let e₂ := coneQuotientIso h hq
  let m := (cokernelTriangleIso h hS hp).inv ≫
    (localizationQ h).mapTriangle.map (strictConeTriangleMap h hS hMap a b ef) ≫
    (cokernelTriangleIso h hS hq).hom
  have hm₁ : m.hom₁ = V.map a := by
    change 𝟙 _ ≫ V.map a ≫ 𝟙 _ = _
    simp
  have hm₂ : m.hom₂ = V.map b := by
    change 𝟙 _ ≫ V.map b ≫ 𝟙 _ = _
    simp
  have hm₃ : m.hom₃ = V.map c := by
    change e₁.inv ≫ V.map z ≫ e₂.hom = V.map c
    have hc : z ≫ coneComparison g q hq.zero = coneComparison f p hp.zero ≫ c := by
      apply strict_hom_ext
      intro o n x
      have he := congrArg (fun r : Q ⟶ S' => (r.app o).f n x.1) ep
      change (q.app o).f n ((z.app o).f n x).1 = (c.app o).f n ((p.app o).f n x.1)
      rw [strictConeMap_apply]
      exact he.symm
    have hc' : V.map z ≫ e₂.hom = e₁.hom ≫ V.map c := by
      change V.map z ≫ V.map (coneComparison g q hq.zero) =
        V.map (coneComparison f p hp.zero) ≫ V.map c
      exact (V.map_comp z (coneComparison g q hq.zero)).symm.trans
        ((congrArg V.map hc).trans (V.map_comp (coneComparison f p hp.zero) c))
    rw [hc', Iso.inv_hom_id_assoc]
  exact Triangle.homMk _ _ (V.map a) (V.map b) (V.map c)
    (by simpa only [hm₁, hm₂] using m.comm₁)
    (by simpa only [hm₂, hm₃] using m.comm₂)
    (by simpa only [hm₁, hm₃] using m.comm₃)

end ConeQuotient

section StageTriangles

open CategoryTheory.Pretriangulated

variable {B : DGCategoryModel.{u,z,w} k}

private theorem selectedAttachment_transition (D : GradedDecomposition F)
    {E G : ClosedSelection D} (e : E ≤ G) (l : ℕ) :
    (selectedAttachment D E l).inclusion ≫ supportedTransition D (l + 1) e =
      supportedTransition D l e ≫ (selectedAttachment D G l).inclusion := by
  apply strict_hom_ext
  intro a n x
  rfl

private theorem selectedAttachment_cocone (D : GradedDecomposition F)
    (E : ClosedSelection D) (l : ℕ) :
    (selectedAttachment D E l).inclusion ≫ supportedInclusion D (l + 1) E =
      supportedInclusion D l E ≫ (F.extension l).inclusion := by
  have hs : CellReindex.stageInclusion F (Nat.le_succ l) = (F.extension l).inclusion :=
    Functor.OfSequence.map_le_succ _ l
  apply strict_hom_ext
  intro a n x
  exact congrArg (fun f : F.stage l ⟶ F.stage (l+1) => (f.app a).f n x.val) hs

private abbrev PreservesAttachmentCokernels (L : RightDGModuleModel A ⥤ RightDGModuleModel B) : Prop :=
  ∀ {P Q : RightDGModuleModel A} {I : Type j} {C : IndexedSemiFree.CellFamily P I}
    (E : Attachment C Q),
    IsStrictCokernel (L.map E.inclusion) (L.map (attachmentProjection E))

variable (h : Derived.HomotopyCategoryLaws B)
variable [SK : HasShift (HomComplex.homotopyCategory B) ℤ]
variable [HasShift (Derived.derivedCategory B h) ℤ] [(localizationQ h).CommShift ℤ]
variable (hS : ∀ (P : HomComplex.homotopyCategory B) (n : ℤ),
  (shiftFunctor (HomComplex.homotopyCategory B) n).obj P = ShiftCone.shift P n)
variable (hMap : ∀ {P Q : RightDGModuleModel B} (n : ℤ) (f : P ⟶ Q),
  HEq ((shiftFunctor (HomComplex.homotopyCategory B) n).map
    (show @Quiver.Hom (HomComplex.homotopyCategory B) _ P Q from HomComplex.homotopyClass f))
    (HomComplex.homotopyClass (ShiftCone.shiftMap n f)))
variable (L : RightDGModuleModel A ⥤ RightDGModuleModel B)
variable (hCok : PreservesAttachmentCokernels.{u,v,w,j,z} L)

private def stageTriangleDiagram (D : GradedDecomposition F) (N l : ℕ) :
    ClosedCells D N ⥤ Triangle (Derived.derivedCategory B h) := by
  let c (E : ClosedCells D N) : ClosedSelection D := ⟨E.val, E.property.1⟩
  let W := L ⋙ strictLocalization h
  refine {
    obj := fun E => cokernelTriangle h hS (hCok (selectedAttachment D (c E) l))
    map := fun {E G} e => cokernelTriangleMap h hS hMap
      (hCok (selectedAttachment D (c E) l)) (hCok (selectedAttachment D (c G) l))
      (L.map (supportedTransition D l (E := c E) (G := c G) e.le))
      (L.map (supportedTransition D (l + 1) (E := c E) (G := c G) e.le))
      (L.map (selectedQuotientTransition D (E := c E) (G := c G) e.le l))
      (by simpa only [Functor.map_comp] using
        congrArg L.map (selectedAttachment_transition D (E := c E) (G := c G) e.le l))
      (by simpa only [Functor.map_comp] using
        congrArg L.map (selectedQuotientTransition_natural D (E := c E) (G := c G) e.le l).symm)
    map_id := ?_
    map_comp := ?_ }
  · intro E
    apply Triangle.hom_ext
    · exact ((supportedDiagram D N l) ⋙ W).map_id E
    · exact ((supportedDiagram D N (l + 1)) ⋙ W).map_id E
    · exact ((quotientDiagram D N l) ⋙ W).map_id E
  · intro E G H e f
    apply Triangle.hom_ext
    · exact ((supportedDiagram D N l) ⋙ W).map_comp e f
    · exact ((supportedDiagram D N (l + 1)) ⋙ W).map_comp e f
    · exact ((quotientDiagram D N l) ⋙ W).map_comp e f

private def stageTriangleCocone (D : GradedDecomposition F) (N l : ℕ) :
    Cocone (stageTriangleDiagram h hS hMap L hCok D N l) := by
  let c (E : ClosedCells D N) : ClosedSelection D := ⟨E.val, E.property.1⟩
  let W := L ⋙ strictLocalization h
  refine {
    pt := cokernelTriangle h hS (hCok (F.extension l))
    ι := {
      app := fun E => cokernelTriangleMap h hS hMap
        (hCok (selectedAttachment D (c E) l)) (hCok (F.extension l))
        (L.map (supportedInclusion D l (c E)))
        (L.map (supportedInclusion D (l + 1) (c E)))
        (L.map (selectedQuotientInclusion D (c E) l))
        (by simpa only [Functor.map_comp] using congrArg L.map (selectedAttachment_cocone D (c E) l))
        (by simpa only [Functor.map_comp] using
          (congrArg L.map (selectedQuotientInclusion_projection D (c E) l)))
      naturality := ?_ } }
  intro E G e
  simp only [Functor.const_obj_map]
  apply Triangle.hom_ext
  · exact (W.mapCocone (supportedCocone D N l)).w e
  · exact (W.mapCocone (supportedCocone D N (l + 1))).w e
  · exact (W.mapCocone (quotientCocone D N l)).w e

end StageTriangles

section TriangleChase

open CategoryTheory.Pretriangulated

universe o m i
variable {R : Type o} [Category.{m} R] [Preadditive R] [HasZeroObject R]
variable [HasShift R ℤ] [∀ n : ℤ, (shiftFunctor R n).Additive] [Pretriangulated R]
variable {J : Type i} [Preorder J]

private theorem functionExact_of_ab_exact {C : ShortComplex AddCommGrpCat.{m}} (h : C.Exact) :
    Function.Exact C.f C.g := by
  intro x
  constructor
  · exact (ShortComplex.ab_exact_iff C).mp h x
  · rintro ⟨y,rfl⟩
    change (C.f ≫ C.g) y = 0
    rw [C.zero]
    rfl

private theorem representatives_middle_triangle (P : R)
    {T : J ⥤ Triangle R} (c : Cocone T)
    (hT : ∀ j, T.obj j ∈ distTriang R) (hc : c.pt ∈ distTriang R)
    (hJ : Directed (· ≤ ·) (fun j : J => j)) (n : ℤ)
    (h₀ : HasRepresentatives
      ((Triangle.π₃ ⋙ shiftFunctor R (n-1) ⋙ preadditiveCoyoneda.obj ⟨P⟩).mapCocone c))
    (h₁ : HasRepresentatives
      ((Triangle.π₁ ⋙ shiftFunctor R n ⋙ preadditiveCoyoneda.obj ⟨P⟩).mapCocone c))
    (h₃ : HasRepresentatives
      ((Triangle.π₃ ⋙ shiftFunctor R n ⋙ preadditiveCoyoneda.obj ⟨P⟩).mapCocone c))
    (h₄ : HasRepresentatives
      ((Triangle.π₁ ⋙ shiftFunctor R (n+1) ⋙ preadditiveCoyoneda.obj ⟨P⟩).mapCocone c)) :
    HasRepresentatives
      ((Triangle.π₂ ⋙ shiftFunctor R n ⋙ preadditiveCoyoneda.obj ⟨P⟩).mapCocone c) := by
  let H := preadditiveCoyoneda.obj ⟨P⟩
  let e : n-1+1 = n := by omega
  let δ (a b : ℤ) (h : a + 1 = b) :
      Triangle.π₃ ⋙ H.shift a ⟶ Triangle.π₁ ⋙ H.shift b :=
    { app := fun U => H.homologySequenceδ U a b h
      naturality := fun {_ _} f => H.homologySequenceδ_naturality f a b h }
  let φ := whiskerRight (Triangle.π₁Toπ₂ : _ ⟶ Triangle.π₂) (H.shift n)
  let ψ := whiskerRight (Triangle.π₂Toπ₃ : _ ⟶ Triangle.π₃) (H.shift n)
  let α := δ (n-1) n e
  let β := δ n (n+1) rfl
  let c₀ := (Triangle.π₃ ⋙ H.shift (n-1)).mapCocone c
  let c₁ := (Triangle.π₁ ⋙ H.shift n).mapCocone c
  let c₂ := (Triangle.π₂ ⋙ H.shift n).mapCocone c
  let c₃ := (Triangle.π₃ ⋙ H.shift n).mapCocone c
  let c₄ := (Triangle.π₁ ⋙ H.shift (n+1)).mapCocone c
  have app_natural {F G : Triangle R ⥤ AddCommGrpCat.{m}} (η : F ⟶ G)
      (j : J) (x : F.obj (T.obj j)) :
      coconeMap (G.mapCocone c) j (η.app (T.obj j) x) =
        η.app c.pt (coconeMap (F.mapCocone c) j x) :=
    (CategoryTheory.congr_fun (η.naturality (c.ι.app j)) x).symm
  exact representatives_of_exact_five c₀ c₁ c₂ c₃ c₄
    (whiskerLeft T α) (whiskerLeft T φ) (whiskerLeft T ψ) (whiskerLeft T β)
    (α.app c.pt) (φ.app c.pt) (ψ.app c.pt) (β.app c.pt)
    (app_natural α) (app_natural φ) (app_natural ψ) (app_natural β)
    (fun j => functionExact_of_ab_exact (H.homologySequence_exact₁ _ (hT j) _ _ e))
    (fun j => functionExact_of_ab_exact (H.homologySequence_exact₂ _ (hT j) n))
    (fun j => functionExact_of_ab_exact (H.homologySequence_exact₃ _ (hT j) _ _ rfl))
    (functionExact_of_ab_exact (H.homologySequence_exact₁ _ hc _ _ e))
    (functionExact_of_ab_exact (H.homologySequence_exact₂ _ hc n))
    (functionExact_of_ab_exact (H.homologySequence_exact₃ _ hc _ _ rfl))
    hJ h₀ h₁ h₃ h₄

end TriangleChase

section ShiftedHom

universe o m i

variable {R : Type o} [Category.{m} R] [Preadditive R] [HasShift R ℤ]
variable {J : Type i} [Preorder J]

private abbrev shiftedHomCocone {G : J ⥤ RightDGModuleModel A} (c : Cocone G)
    (W : RightDGModuleModel A ⥤ R) (X : R) (n : ℤ) :=
  (W ⋙ shiftFunctor R n ⋙ preadditiveCoyoneda.obj ⟨X⟩).mapCocone c

private abbrev MapsStrictSumsToCoproducts (W : RightDGModuleModel A ⥤ R) : Prop :=
  ∀ {I : Type j} {V : I → RightDGModuleModel A} {S : RightDGModuleModel A} (b : StrictSum V S),
    Nonempty (IsColimit (Cofan.mk (W.obj S) (fun i => W.map (b.inclusion i))))

private theorem quotientHasRepresentatives (W : RightDGModuleModel A ⥤ R)
    (hSum : MapsStrictSumsToCoproducts.{u,v,w,j,o,m} W)
    (X : R) (hX : CompactRepresentables.IsCompact.{j,_,_} X)
    (D : GradedDecomposition F) (N l : ℕ) (hl : l < N) (n : ℤ) :
    HasRepresentatives (shiftedHomCocone (quotientCocone D N l) W X n) := by
  classical
  let U := shiftFunctor R n
  let V := W ⋙ U
  let c := V.mapCocone (quotientCocone D N l)
  let b := attachmentSumRealization (F.extension l)
  let b' (E : ClosedCells D N) := attachmentSumRealization (selectedAttachment D ⟨E.val,E.property.1⟩ l)
  let I (E : ClosedCells D N) : Set (F.index l) := {i | Sigma.mk l i ∈ E.val}
  have hcover (s : Finset (F.index l)) : ∃ E, ∀ i ∈ s, i ∈ I E := by
    have hb : ∀ x ∈ s.image (Sigma.mk l), x.1 < N := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hl
    obtain ⟨E,hE⟩ := exists_closed_superset D N (s.image (Sigma.mk l)) hb
    exact ⟨E, fun i hi => hE (Finset.mem_image_of_mem _ hi)⟩
  let inj (i : F.index l) := V.map (b.inclusion i)
  let inj' (E : ClosedCells D N) (i : I E) := V.map ((b' E).inclusion i)
  have hc : IsColimit (Cofan.mk c.pt inj) :=
    isColimitCofanMkObjOfIsColimit U _ _ (hSum b).some
  have hc' (E : ClosedCells D N) : IsColimit (Cofan.mk ((quotientDiagram D N l ⋙ V).obj E) (inj' E)) :=
    isColimitCofanMkObjOfIsColimit U _ _ (hSum (b' E)).some
  have hfac (E : ClosedCells D N) (i : I E) : inj' E i ≫ c.ι.app E = inj i.val := by
    let e := selectedQuotientInclusion D (⟨E.val,E.property.1⟩ : ClosedSelection D) l
    change V.map ((b' E).inclusion i) ≫ V.map e = V.map (b.inclusion i.val)
    exact (V.map_comp ((b' E).inclusion i) e).symm.trans
      (congrArg V.map (selectedQuotientInclusion_onSummand D ⟨E.val,E.property.1⟩ l i))
  exact compactCoproduct_representatives X hX c I hcover inj hc inj' hc' hfac

private theorem strictIsZero_of_terms {S : RightDGModuleModel A}
    (hS : ∀ a n (x : (S.complex a).X n), x = 0) : IsZero S := by
  apply (IsZero.iff_id_eq_zero S).mpr
  exact strict_hom_ext hS

private theorem bottomHasRepresentatives [∀ n : ℤ, (shiftFunctor R n).Additive]
    (W : RightDGModuleModel A ⥤ R) [W.PreservesZeroMorphisms]
    (X : R) (D : GradedDecomposition F) (N : ℕ) (n : ℤ) :
    HasRepresentatives (shiftedHomCocone (supportedCocone D N 0) W X n) := by
  let V := W ⋙ shiftFunctor R n
  have hz : IsZero (V.obj (F.stage 0)) := V.map_isZero (strictIsZero_of_terms F.bottom)
  have hEz (E : ClosedCells D N) : IsZero (V.obj (supportedModule D 0 ⟨E.val,E.property.1⟩)) :=
    V.map_isZero (strictIsZero_of_terms (fun a n x => Subtype.ext (F.bottom a n x.val)))
  constructor
  · intro x
    exact ⟨⟨∅, closed_empty D, by simp⟩, 0, hz.eq_of_tgt _ x⟩
  · intro E y _
    exact ⟨E, 𝟙 _, (hEz E).eq_of_tgt _ _⟩

end ShiftedHom

section ComparisonOfSubmodules

open private isoOfDegreewiseBijective isoOfDegreewiseBijective_hom from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellLift

variable (D : GradedDecomposition F) {N : ℕ} (S : StageSubmodules D N)

private def inclusionToSupported (E : ClosedCells D N) :
    S.diagram.obj E ⟶ supportedModule D N ⟨E.val,E.property.1⟩ :=
  mapToSupported D N E (S.inclusion.app E ≫ F.into N)
    (fun a n x => (S.image E a n _).mp ⟨x,rfl⟩)

private theorem inclusionToSupported_fac (E : ClosedCells D N) :
    inclusionToSupported D S E ≫ supportedInclusion D N ⟨E.val,E.property.1⟩ = S.inclusion.app E := by
  apply strict_hom_ext
  intro a n x
  apply F.injective N a n
  have hg : inclusionToSupported D S E ≫ supportedInto D N ⟨E.val,E.property.1⟩ =
      S.inclusion.app E ≫ F.into N :=
    mapToSupported_into D N E (S.inclusion.app E ≫ F.into N)
      (fun a n x => (S.image E a n _).mp ⟨x,rfl⟩)
  exact congrArg (fun f : S.diagram.obj E ⟶ M => (f.app a).f n x)
    hg

private theorem inclusionToSupported_bijective (E : ClosedCells D N) (a : A.Obj) (n : ℤ) :
    Function.Bijective (((inclusionToSupported D S E).app a).f n) := by
  have he (x : ((S.diagram.obj E).complex a).X n) :
      (((inclusionToSupported D S E).app a).f n x).val = ((S.inclusion.app E).app a).f n x :=
    congrArg (fun f : S.diagram.obj E ⟶ F.stage N => (f.app a).f n x)
      (inclusionToSupported_fac D S E)
  constructor
  · intro x y h
    exact S.injective E a n ((he x).symm.trans ((congrArg Subtype.val h).trans (he y)))
  · intro y
    obtain ⟨x,hx⟩ := (S.image E a n y.val).mpr y.property
    exact ⟨x,Subtype.ext ((he x).trans hx)⟩

private abbrev submoduleIso (E : ClosedCells D N) :
    S.diagram.obj E ≅ (supportedDiagram D N N).obj E :=
  isoOfDegreewiseBijective (inclusionToSupported D S E) (inclusionToSupported_bijective D S E)

private theorem submoduleIso_fac (E : ClosedCells D N) :
    (submoduleIso D S E).hom ≫ (supportedCocone D N N).ι.app E = S.inclusion.app E := by
  let i := supportedInclusion D N ⟨E.val,E.property.1⟩
  have he : (submoduleIso D S E).hom = inclusionToSupported D S E :=
    isoOfDegreewiseBijective_hom _ _
  exact (congrArg (fun f => f ≫ i) he).trans (inclusionToSupported_fac D S E)

private def submoduleDiagramIso : S.diagram ≅ supportedDiagram D N N := by
  refine NatIso.ofComponents (submoduleIso D S) ?_
  intro E G f
  let c := supportedCocone D N N
  let d : Cocone S.diagram := ⟨F.stage N, S.inclusion⟩
  have he : (submoduleIso D S E).hom ≫ c.ι.app E = d.ι.app E := submoduleIso_fac D S E
  have hg : (submoduleIso D S G).hom ≫ c.ι.app G = d.ι.app G := submoduleIso_fac D S G
  have h : (S.diagram.map f ≫ (submoduleIso D S G).hom) ≫ c.ι.app G =
      ((submoduleIso D S E).hom ≫ (supportedDiagram D N N).map f) ≫ c.ι.app G := by
    rw [Category.assoc, hg, Category.assoc, c.w f, he]
    exact d.w f
  apply strict_hom_ext
  intro a n x
  apply Subtype.val_injective
  exact congrArg (fun f : S.diagram.obj E ⟶ F.stage N => (f.app a).f n x) h

private def isColimit_homCocone_of_supported {R : Type*} [Category R] [Preadditive R] [HasShift R ℤ]
    (W : RightDGModuleModel A ⥤ R) (X : R) (n : ℤ)
    (hc : IsColimit (shiftedHomCocone (supportedCocone D N N) W X n)) :
    IsColimit (homCocone D S W X n) := by
  let V := W ⋙ shiftFunctor R n ⋙ preadditiveCoyoneda.obj ⟨X⟩
  let α := Functor.isoWhiskerRight (submoduleDiagramIso D S) V
  let c := shiftedHomCocone (supportedCocone D N N) W X n
  have ec : (Cocone.precompose α.hom).obj c ≅ homCocone D S W X n := by
    refine Cocone.ext (Iso.refl _) (fun E => ?_)
    change (V.map (submoduleIso D S E).hom ≫ V.map ((supportedCocone D N N).ι.app E)) ≫ 𝟙 _ =
      V.map (S.inclusion.app E)
    rw [Category.comp_id]
    exact (V.map_comp _ _).symm.trans (congrArg V.map (submoduleIso_fac D S E))
  exact IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv α c).symm hc) ec

end ComparisonOfSubmodules

section StageComparison

open CategoryTheory.Pretriangulated

variable {B : DGCategoryModel.{u,z,w} k} (h : Derived.HomotopyCategoryLaws B)
variable [SK : HasShift (HomComplex.homotopyCategory B) ℤ]
variable [HasShift (Derived.derivedCategory B h) ℤ] [(localizationQ h).CommShift ℤ]
variable [PR : Preadditive (Derived.derivedCategory B h)] [HasZeroObject (Derived.derivedCategory B h)]
variable [∀ n : ℤ, (shiftFunctor (Derived.derivedCategory B h) n).Additive]
variable [Pretriangulated (Derived.derivedCategory B h)]
variable (hS : ∀ (P : HomComplex.homotopyCategory B) (n : ℤ),
  (shiftFunctor (HomComplex.homotopyCategory B) n).obj P = ShiftCone.shift P n)
variable (hMap : ∀ {P Q : RightDGModuleModel B} (n : ℤ) (f : P ⟶ Q),
  HEq ((shiftFunctor (HomComplex.homotopyCategory B) n).map
    (show @Quiver.Hom (HomComplex.homotopyCategory B) _ P Q from HomComplex.homotopyClass f))
    (HomComplex.homotopyClass (ShiftCone.shiftMap n f)))
variable (hdist : ∀ {P Q : RightDGModuleModel B} (f : P ⟶ Q),
  localizationCone h hS f ∈ distTriang (Derived.derivedCategory B h))
variable (L : RightDGModuleModel A ⥤ RightDGModuleModel B)
variable [(L ⋙ strictLocalization h).PreservesZeroMorphisms]
variable (hCok : PreservesAttachmentCokernels.{u,v,w,j,z} L)
variable (hSum : MapsStrictSumsToCoproducts.{u,v,w,j,_,_} (L ⋙ strictLocalization h))

include hMap hdist hCok hSum in
set_option backward.isDefEq.respectTransparency false in
private theorem stageHasRepresentatives (X : Derived.derivedCategory B h)
    (hX : CompactRepresentables.IsCompact.{j,_,_} X) (D : GradedDecomposition F) (N : ℕ) :
    ∀ l, l ≤ N → ∀ n : ℤ,
      HasRepresentatives (shiftedHomCocone (supportedCocone D N l) (L ⋙ strictLocalization h) X n) := by
  let W := L ⋙ strictLocalization h
  have hdir := (closedCellsDirected F D N).2.2
  intro l
  induction l with
  | zero =>
      intro _ n
      exact bottomHasRepresentatives W X D N n
  | succ l ih =>
      intro hl n
      have hlt : l < N := hl
      let c := stageTriangleCocone h hS hMap L hCok D N l
      have ht (E : ClosedCells D N) :
          (stageTriangleDiagram h hS hMap L hCok D N l).obj E ∈ distTriang (Derived.derivedCategory B h) :=
        cokernelTriangle_distinguished h hS (hCok (selectedAttachment D ⟨E.val,E.property.1⟩ l)) (hdist _)
      have hc : c.pt ∈ distTriang (Derived.derivedCategory B h) :=
        cokernelTriangle_distinguished h hS (hCok (F.extension l)) (hdist _)
      exact representatives_middle_triangle X c ht hc hdir n
        (quotientHasRepresentatives W hSum X hX D N l hlt (n-1))
        (ih hlt.le n)
        (quotientHasRepresentatives W hSum X hX D N l hlt n)
        (ih hlt.le (n+1))

include hMap hdist hCok hSum in
private theorem stageHomComparisonAt (hAdd : CompactRepresentables.LocalizationMapAdditive h PR) :
    StageHomComparisonAt.{u,v,w,j,z} L h := by
  refine ⟨toHomotopyCategory B, inferInstance, PR, fun _ => rfl, fun _ => HEq.rfl,
    hAdd, ⟨SK, hS, hMap, ⟨inferInstance⟩⟩, ?_⟩
  intro X hX M F D N S n
  let W := L ⋙ strictLocalization h
  have hdir := (closedCellsDirected F D N).2.2
  have hr := stageHasRepresentatives h hS hMap hdist L hCok hSum X hX D N N (le_refl _) n
  exact ⟨isColimit_homCocone_of_supported D S W X n (isColimitOfRepresentatives _ hdir hr)⟩

end StageComparison

section AdequateLocalization

open CategoryTheory.Pretriangulated
open private quasiIsomorphisms_hasLeftCalculusOfFractions
  quasiIsomorphisms_isStableUnderFiniteProducts quasiIsomorphisms_isCompatibleWithTriangulation
  specConeTriangle_eq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles
open private quotientShift_map_heq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyPretriangulated

set_option backward.isDefEq.respectTransparency false in
private theorem stageHomComparisonAt_adequate {B : DGCategoryModel.{u,max z w,w} k}
    (h : Derived.HomotopyCategoryLaws B) (L : RightDGModuleModel A ⥤ RightDGModuleModel B)
    [L.PreservesZeroMorphisms] (hCok : PreservesAttachmentCokernels.{u,v,w,j,max z w} L)
    (hSum : MapsStrictSumsToCoproducts.{u,v,w,j,_,_} (L ⋙ strictLocalization h)) :
    StageHomComparisonAt.{u,v,w,j,max z w} L h := by
  let W := quasiIsomorphisms B
  let R := Derived.derivedCategory B h
  let _ : W.HasLeftCalculusOfFractions := quasiIsomorphisms_hasLeftCalculusOfFractions
  let _ : W.IsStableUnderFiniteProducts := quasiIsomorphisms_isStableUnderFiniteProducts
  let _ : W.IsCompatibleWithTriangulation := quasiIsomorphisms_isCompatibleWithTriangulation
  let SR : HasShift W.Localization ℤ := inferInstance
  let CS : W.Q.CommShift ℤ := inferInstance
  let AR : Preadditive W.Localization := inferInstance
  let ZR : HasZeroObject W.Localization := inferInstance
  let LR (n : ℤ) : (shiftFunctor W.Localization n).Additive := inferInstance
  let TR : Pretriangulated W.Localization := inferInstance
  let AQ : W.Q.Additive := inferInstance
  let _ : HasShift (HomComplex.homotopyCategory B) ℤ := homotopyHasShift
  let _ : Preadditive (HomComplex.homotopyCategory B) := homotopyPreadditive
  let _ : HasShift R ℤ := SR
  let _ : (localizationQ h).CommShift ℤ := CS
  let _ : Preadditive R := AR
  let _ : HasZeroObject R := ZR
  let _ : ∀ n : ℤ, (shiftFunctor R n).Additive := LR
  let _ : Pretriangulated R := TR
  let _ : (localizationQ h).Additive := AQ
  let _ : (strictLocalization h).PreservesZeroMorphisms :=
    inferInstanceAs (toHomotopyCategory B ⋙ localizationQ h).PreservesZeroMorphisms
  let _ : (L ⋙ strictLocalization h).PreservesZeroMorphisms := inferInstance
  have hS (P : HomComplex.homotopyCategory B) (n : ℤ) :
      (shiftFunctor (HomComplex.homotopyCategory B) n).obj P = ShiftCone.shift P n := rfl
  have hMap {P Q : RightDGModuleModel B} (n : ℤ) (f : P ⟶ Q) :
      HEq ((shiftFunctor (HomComplex.homotopyCategory B) n).map
        (show @Quiver.Hom (HomComplex.homotopyCategory B) _ P Q from HomComplex.homotopyClass f))
        (HomComplex.homotopyClass (ShiftCone.shiftMap n f)) :=
    quotientShift_map_heq n f
  let _ : W.Q.IsTriangulated := Triangulated.Localization.isTriangulated_functor W.Q W
  have hdist {P Q : RightDGModuleModel B} (f : P ⟶ Q) :
      localizationCone h hS f ∈ distTriang R := by
    change W.Q.mapTriangle.obj (DerivedTriangles.coneTriangle h homotopyHasShift rfl f) ∈
      distTriang W.Localization
    rw [specConeTriangle_eq]
    exact W.Q.map_distinguished _ (coneTriangle_distinguished f)
  have hAdd : CompactRepresentables.LocalizationMapAdditive h (inferInstance : Preadditive R) := by
    intro P Q f g
    let f₀ : @Quiver.Hom (HomComplex.homotopyCategory B) _ P Q := f
    let g₀ : @Quiver.Hom (HomComplex.homotopyCategory B) _ P Q := g
    exact (localizationQ h).map_add (f := f₀) (g := g₀)
  exact stageHomComparisonAt h hS hMap hdist L hCok hSum hAdd

end AdequateLocalization

/-- At either adequate localization, the finite closed cell submodules compute
all shifted Hom groups out of compact objects by a directed colimit. -/
theorem stageHomComparison : StageHomComparison.{u,v,w,j,t} := by
  constructor
  · intro k _ A h
    apply stageHomComparisonAt_adequate h (𝟭 (RightDGModuleModel A))
    · intro P Q I C E
      exact attachmentCokernel E
    · intro I V S b
      exact nativeExistingDerivedCoproduct.{u,v,w,j} h b
  · intro k _ A h
    let L := AmbientDerived.strictInput.{u,v,w,t} A
    let _ : L.PreservesZeroMorphisms := ⟨fun _ _ => strict_hom_ext (fun _ _ _ => rfl)⟩
    apply stageHomComparisonAt_adequate h L
    · intro P Q I C E
      exact liftedCokernel.{u,v,w,j,t} E
    · intro I V S b
      obtain ⟨c, hi, _, ⟨hc⟩⟩ := originalExistingDerivedCoproduct.{u,v,w,j,t} A h b
      let W := strictLocalization h
      change IsColimit (Cofan.mk (W.obj (L.obj S)) (fun i => W.map (c.inclusion i))) at hc
      have he : (fun i => W.map (c.inclusion i)) = (fun i => W.map (L.map (b.inclusion i))) :=
        funext fun i => congrArg W.map (hi i)
      rw [he] at hc
      exact ⟨hc⟩

end

end DerivedFormalization.RightDGModule
