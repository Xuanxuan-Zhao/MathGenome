import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.Sperner
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.FacetIncidence
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace D10Topology.Ch17
namespace SpernerCounting

/-- The facets of a cell with a prescribed complete set of labels. -/
def labeledFacets {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (A : Finset β) (C : Finset α) : Finset (Finset α) :=
  (C.powersetCard A.card).filter (fun F => F.image f = A)

lemma mem_labeledFacets {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} {A : Finset β} {C F : Finset α} :
    F ∈ labeledFacets f A C ↔ F ⊆ C ∧ F.card = A.card ∧ F.image f = A := by
  simp [labeledFacets, and_assoc]

lemma labeledFacets_erase {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} {A : Finset β} {C : Finset α}
    (hcard : C.card = A.card + 1) {F : Finset α} (hF : F ∈ labeledFacets f A C) :
    ∃ a ∈ C, F = C.erase a := by
  obtain ⟨hFC, hFcard, _⟩ := mem_labeledFacets.mp hF
  have hdiff : (C \ F).card = 1 := by rw [Finset.card_sdiff_of_subset hFC, hcard, hFcard]; omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hdiff
  have haC : a ∈ C := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).1
  refine ⟨a, haC, ?_⟩
  ext x
  have hx : x ∈ C \ F ↔ x = a := by rw [ha]; simp
  simp only [Finset.mem_sdiff] at hx
  simp only [Finset.mem_erase]
  constructor
  · intro hxF
    exact ⟨fun h => (hx.mpr h).2 hxF, hFC hxF⟩
  · rintro ⟨hxa, hxC⟩
    by_contra hxF
    exact hxa (hx.mp ⟨hxC, hxF⟩)

lemma image_erase_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} {C : Finset α} (hf : Set.InjOn f C) {a : α} (ha : a ∈ C) :
    (C.erase a).image f = (C.image f).erase (f a) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨b, ⟨hba, hb⟩, rfl⟩
    exact ⟨fun h => hba (hf hb ha h), b, hb, rfl⟩
  · rintro ⟨hya, b, hb, rfl⟩
    exact ⟨b, ⟨fun h => hya (congrArg f h), hb⟩, rfl⟩

lemma erase_image_eq_of_duplicate {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} {C : Finset α} {a b : α}
    (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) (heq : f a = f b) :
    (C.erase a).image f = (C.erase b).image f := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hxa, hx⟩, rfl⟩
    by_cases hxb : x = b
    · exact ⟨a, ⟨hab, ha⟩, heq.trans (congrArg f hxb.symm)⟩
    · exact ⟨x, ⟨hxb, hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxb, hx⟩, rfl⟩
    by_cases hxa : x = a
    · exact ⟨b, ⟨hab.symm, hb⟩, heq.symm.trans (congrArg f hxa.symm)⟩
    · exact ⟨x, ⟨hxa, hx⟩, rfl⟩

/-- Local degree parity: a fully labeled cell has one special facet;
noninjective labelings contribute either two special facets or none. -/
theorem labeledFacets_parity {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype β] (f : α → β) (j : β) (C : Finset α)
    (hcard : C.card = Fintype.card β) :
    ((labeledFacets f (Finset.univ.erase j) C).card : ZMod 2) =
      if C.image f = Finset.univ then 1 else 0 := by
  let A := Finset.univ.erase j
  have hc : C.card = A.card + 1 := by
    dsimp [A]
    simp only [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
    have hp : 0 < Fintype.card β := Fintype.card_pos_iff.mpr ⟨j⟩
    omega
  by_cases hi : Set.InjOn f C
  · have hfull : C.image f = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_image_of_injOn hi, Finset.card_univ, hcard]
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp (hfull ▸ Finset.mem_univ j)
    have he : (C.erase a).image f = A := by
      rw [image_erase_of_injOn hi ha, hfull, hfa]
    have hspecial : labeledFacets f A C = {C.erase a} := by
      ext F
      rw [Finset.mem_singleton]
      constructor
      · intro hF
        obtain ⟨b, hb, rfl⟩ := labeledFacets_erase hc hF
        have heq := (mem_labeledFacets.mp hF).2.2
        have hb' : f b = j := by
          by_contra hbj
          have hmem : f b ∈ A := Finset.mem_erase.mpr ⟨hbj, Finset.mem_univ _⟩
          have herase : f b ∉ (C.erase b).image f := by
            rw [image_erase_of_injOn hi hb]
            exact Finset.notMem_erase _ _
          exact herase (heq ▸ hmem)
        have hba : b = a := hi hb ha (hb'.trans hfa.symm)
        rw [hba]
      · rintro rfl
        exact mem_labeledFacets.mpr ⟨Finset.erase_subset _ _, by
          rw [Finset.card_erase_of_mem ha, hc]; omega, he⟩
    rw [ite_eq_left hfull]
    change ((labeledFacets f A C).card : ZMod 2) = 1
    rw [hspecial]; simp
  · have hnotfull : C.image f ≠ Finset.univ := by
      intro h
      apply hi
      apply Finset.injOn_of_card_image_eq
      rw [h, Finset.card_univ, hcard]
    rw [ite_eq_right hnotfull]
    simp only [Set.InjOn] at hi
    push Not at hi
    obtain ⟨a, ha, b, hb, heq, hab⟩ := hi
    have hdup : (C.erase a).image f = (C.erase b).image f :=
      erase_image_eq_of_duplicate ha hb hab heq
    have hbound : ∀ F ∈ labeledFacets f A C, F = C.erase a ∨ F = C.erase b := by
      intro F hF
      obtain ⟨hFC, hFcard, hlabels⟩ := mem_labeledFacets.mp hF
      have hinj : Set.InjOn f F := Finset.injOn_of_card_image_eq (by rw [hlabels, hFcard])
      obtain ⟨c, hcC, hFc⟩ := labeledFacets_erase hc hF
      by_cases hca : c = a
      · exact Or.inl (hFc.trans (congrArg C.erase hca))
      by_cases hcb : c = b
      · exact Or.inr (hFc.trans (congrArg C.erase hcb))
      have haF : a ∈ F := by rw [hFc]; exact Finset.mem_erase.mpr ⟨Ne.symm hca, ha⟩
      have hbF : b ∈ F := by rw [hFc]; exact Finset.mem_erase.mpr ⟨Ne.symm hcb, hb⟩
      exact False.elim (hab (hinj haF hbF heq))
    by_cases hA : (C.erase a).image f = A
    · have hspecial : labeledFacets f A C = {C.erase a, C.erase b} := by
        ext F
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact hbound F
        · intro h
          rcases h with rfl | rfl
          · exact mem_labeledFacets.mpr ⟨Finset.erase_subset _ _, by
              rw [Finset.card_erase_of_mem ha, hc]; omega, hA⟩
          · exact mem_labeledFacets.mpr ⟨Finset.erase_subset _ _, by
              rw [Finset.card_erase_of_mem hb, hc]; omega, hdup.symm.trans hA⟩
      change ((labeledFacets f A C).card : ZMod 2) = 0
      rw [hspecial]
      have hne : C.erase a ≠ C.erase b := fun h => hab ((Finset.erase_inj C ha).mp h)
      norm_num [hne]
      decide
    · have hspecial : labeledFacets f A C = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro F hF
        have hlabels := (mem_labeledFacets.mp hF).2.2
        rcases hbound F hF with rfl | rfl
        · exact hA hlabels
        · exact hA (hdup.trans hlabels)
      change ((labeledFacets f A C).card : ZMod 2) = 0
      rw [hspecial]; simp

/-- A total labeling is convenient for finite-set counting. Only values at
vertices of the triangulation are used. -/
def fullCells {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
    (f : Euclidean m → Fin (n + 1)) : Finset (Finset (Euclidean m)) :=
  (topCells T).filter (fun C => C.image f = Finset.univ)

def specialBoundary {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
    (f : Euclidean m → Fin (n + 1)) (j : Fin (n + 1)) : Finset (Finset (Euclidean m)) :=
  (boundaryFacets T).filter (fun F => F.image f = Finset.univ.erase j)

lemma local_facets_eq_filter {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
    (hn : 0 < n) (f : Euclidean m → Fin (n + 1)) (j : Fin (n + 1))
    {C : Finset (Euclidean m)} (hC : C ∈ topCells T) :
    labeledFacets f (Finset.univ.erase j) C =
      (facets T).filter (fun F => F ⊆ C ∧ F.image f = Finset.univ.erase j) := by
  have hA : (Finset.univ.erase j).card = n := by simp
  ext F
  rw [mem_labeledFacets, Finset.mem_filter]
  simp only [facets, Specs.D10Topology.Ch17.SimplexTriangulation.facetsValue,
    Finset.mem_filter]
  rw [hA]
  constructor
  · rintro ⟨hFC, hcard, hl⟩
    exact ⟨⟨T.complex.face_closed C (Finset.mem_filter.mp hC).1 F hFC, hn, hcard⟩, hFC, hl⟩
  · rintro ⟨⟨_, _, hcard⟩, hFC, hl⟩
    exact ⟨hFC, hcard, hl⟩

/-- Double counting the actual facet/cell incidences, over the field of two elements. -/
theorem incidence_parity {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
    (hn : 0 < n) (f : Euclidean m → Fin (n + 1)) (j : Fin (n + 1)) :
    ((fullCells T f).card : ZMod 2) = ((specialBoundary T f j).card : ZMod 2) := by
  have hlocal : ∀ C ∈ topCells T,
      ((labeledFacets f (Finset.univ.erase j) C).card : ZMod 2) =
        if C.image f = Finset.univ then 1 else 0 := by
    intro C hC
    apply labeledFacets_parity
    simpa using (Finset.mem_filter.mp hC).2
  calc
    ((fullCells T f).card : ZMod 2) =
        ∑ C ∈ topCells T, ((labeledFacets f (Finset.univ.erase j) C).card : ZMod 2) := by
      rw [fullCells, Finset.natCast_card_filter]
      exact Finset.sum_congr rfl (fun C hC => (hlocal C hC).symm)
    _ = ∑ C ∈ topCells T, ∑ F ∈ facets T,
        (if F ⊆ C ∧ F.image f = Finset.univ.erase j then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [local_facets_eq_filter T hn f j hC, Finset.natCast_card_filter]
    _ = ∑ F ∈ facets T, ∑ C ∈ topCells T,
        (if F ⊆ C ∧ F.image f = Finset.univ.erase j then (1 : ZMod 2) else 0) :=
      Finset.sum_comm
    _ = ∑ F ∈ facets T,
        if F.image f = Finset.univ.erase j then ((incidentTopCells T F).card : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro F _
      by_cases hl : F.image f = Finset.univ.erase j
      · simp only [hl, and_true, ite_true]
        have he : incidentTopCells T F = (topCells T).filter (fun C => F ⊆ C) := by
          ext C
          simp only [incidentTopCells,
            Specs.D10Topology.Ch17.FacetIncidence.incidentTopCellsValue, Finset.mem_filter]
          rfl
        rw [he, Finset.natCast_card_filter]
      · simp [hl]
    _ = ∑ F ∈ facets T,
        if F ∈ boundaryFacets T ∧ F.image f = Finset.univ.erase j then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro F hF
      by_cases hb : F ∈ boundaryFacets T
      · rw [boundary_facet_incidence T hn F hb]
        simp [hb]
      · have hi : F ∈ internalFacets T := Finset.mem_sdiff.mpr ⟨hF, hb⟩
        rw [internal_facet_incidence T hn F hi]
        have htwo : (2 : ZMod 2) = 0 := by decide
        simp [hb, htwo]
    _ = ((specialBoundary T f j).card : ZMod 2) := by
      rw [specialBoundary]
      change _ = ((((facets T).filter (fun F => cellHull F ⊆ simplexBoundary S)).filter
        (fun F => F.image f = Finset.univ.erase j)).card : ZMod 2)
      rw [Finset.filter_filter, Finset.natCast_card_filter]
      apply Finset.sum_congr rfl
      intro F hF
      simp only [boundaryFacets,
        Specs.D10Topology.Ch17.SimplexTriangulation.boundaryFacetsValue,
        Finset.mem_filter, hF, true_and]
      rfl

/-- The same original-face condition, expressed for a total labeling. -/
def RespectsFaces {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
    (f : Euclidean m → Fin (n + 1)) : Prop :=
  ∀ I : Finset (Fin (n + 1)), ∀ v ∈ vertices T.complex,
    v ∈ simplexFace S I → f v ∈ I

lemma vertex_of_cell {m : ℕ} (K : GeometricComplex m) {C : Finset (Euclidean m)}
    (hC : C ∈ K.cells) {v : Euclidean m} (hv : v ∈ C) : v ∈ vertices K := by
  exact Finset.mem_biUnion.mpr ⟨C, hC, hv⟩

/-- A special boundary facet must be contained in the original face missing
its omitted label. The barycenter argument also handles cells meeting several
original faces; containment in a single original face is proved, not assumed. -/
lemma specialBoundary_in_original_face {m n : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) (f : Euclidean m → Fin (n + 1))
    (hf : RespectsFaces T f) (j : Fin (n + 1))
    {F : Finset (Euclidean m)} (hF : F ∈ specialBoundary T f j) :
    cellHull F ⊆ simplexFace S (Finset.univ.erase j) := by
  obtain ⟨hb, hlabels⟩ := Finset.mem_filter.mp hF
  obtain ⟨hfacet, hboundary⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcell, hn, hcard⟩ := Finset.mem_filter.mp hfacet
  obtain ⟨e⟩ := exists_simplexCoordinates S
  obtain ⟨p, hp, hpos⟩ := exists_point_detects_affine_zeros
    (Finset.card_pos.mp (hcard ▸ hn))
  have hsub := cellHull_subset_simplexHull T hcell
  have hpB := hboundary hp
  change p ∈ ⋃ i, simplexFace S (Finset.univ.erase i) at hpB
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpB
  have hzero : ∀ v ∈ F, e.coord i v = 0 :=
    (hpos (e.coord i) (fun v hv => e.nonneg (hsub (subset_convexHull ℝ _ hv)) i)).mp
      ((e.face_iff (hsub hp) i).mp hpi)
  have hFi : cellHull F ⊆ simplexFace S (Finset.univ.erase i) := by
    intro x hx
    apply (e.face_iff (hsub hx) i).mpr
    exact affine_zero_on_span _ hzero (convexHull_subset_affineSpan (𝕜 := ℝ) _ hx)
  have hij : i = j := by
    by_contra hij
    have hiA : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
    obtain ⟨v, hv, hvlabel⟩ := Finset.mem_image.mp (hlabels ▸ hiA)
    have hallowed := hf (Finset.univ.erase i) v (vertex_of_cell T.complex hcell hv)
      (hFi (subset_convexHull ℝ _ hv))
    rw [hvlabel] at hallowed
    exact Finset.notMem_erase i Finset.univ hallowed
  simpa [hij] using hFi

lemma vertices_induced_subset {m n : ℕ} {S : AffineSimplex m (n + 1)}
    (T : Triangulation S) (I : Finset (Fin (n + 2)))
    {S' : AffineSimplex m n} (U : Triangulation S')
    (hU : U.complex = inducedComplex T I) {v : Euclidean m}
    (hv : v ∈ vertices U.complex) :
    v ∈ vertices T.complex ∧ v ∈ simplexFace S I := by
  obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
  rw [hU] at hC
  obtain ⟨hCT, hCI⟩ := Finset.mem_filter.mp hC
  exact ⟨vertex_of_cell T.complex hCT hvC, hCI hvC⟩

lemma simplexFace_face {m n k : ℕ} (S : AffineSimplex m n)
    (I : Finset (Fin (n + 1))) (hI : I.card = k + 1) (J : Finset (Fin (k + 1))) :
    simplexFace (S.face hI) J = simplexFace S (J.image (I.orderEmbOfFin hI)) := by
  change convexHull ℝ ((S.face hI).points '' (J : Set _)) =
    convexHull ℝ (S.points '' ((J.image (I.orderEmbOfFin hI)) : Set _))
  simp only [Affine.Simplex.face_points', Finset.coe_image, Set.image_comp]

/-- A total inverse of the enumeration of an original face. Its off-face
values play no role in the restricted triangulation. -/
def faceLabelInverse {n k : ℕ} (I : Finset (Fin (n + 1))) (hI : I.card = k + 1)
    (a : Fin (n + 1)) : Fin (k + 1) :=
  if ha : a ∈ I then (I.orderIsoOfFin hI).symm ⟨a, ha⟩ else 0

lemma faceLabelInverse_apply {n k : ℕ} (I : Finset (Fin (n + 1))) (hI : I.card = k + 1)
    (a : Fin (k + 1)) : faceLabelInverse I hI (I.orderEmbOfFin hI a) = a := by
  simp only [faceLabelInverse, Finset.orderEmbOfFin_mem, dite_true]
  exact (I.orderIsoOfFin hI).symm_apply_apply a

lemma faceLabelInverse_right {n k : ℕ} (I : Finset (Fin (n + 1))) (hI : I.card = k + 1)
    {a : Fin (n + 1)} (ha : a ∈ I) :
    I.orderEmbOfFin hI (faceLabelInverse I hI a) = a := by
  simp only [faceLabelInverse, ha, dite_true]
  exact congrArg Subtype.val ((I.orderIsoOfFin hI).apply_symm_apply ⟨a, ha⟩)

lemma restrict_respectsFaces {m n : ℕ} {S : AffineSimplex m (n + 1)}
    (T : Triangulation S) (f : Euclidean m → Fin (n + 2)) (hf : RespectsFaces T f)
    (I : Finset (Fin (n + 2))) (hI : I.card = n + 1)
    (U : Triangulation (S.face hI)) (hU : U.complex = inducedComplex T I) :
    RespectsFaces U (faceLabelInverse I hI ∘ f) := by
  intro J v hv hvJ
  have hvT := (vertices_induced_subset T I U hU hv).1
  rw [simplexFace_face] at hvJ
  obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp (hf _ v hvT hvJ)
  change faceLabelInverse I hI (f v) ∈ J
  rw [← hfa, faceLabelInverse_apply]
  exact ha

lemma image_faceLabelInverse {n k : ℕ} (I : Finset (Fin (n + 1))) (hI : I.card = k + 1) :
    I.image (faceLabelInverse I hI) = Finset.univ := by
  calc
    I.image (faceLabelInverse I hI) =
        (Finset.univ.image (I.orderEmbOfFin hI)).image (faceLabelInverse I hI) := by
      rw [Finset.image_orderEmbOfFin_univ]
    _ = Finset.univ := by
      simp only [Finset.image_image, Function.comp_def, faceLabelInverse_apply, Finset.image_id']

/-- Fully labeled cells on the induced original facet are exactly the special
boundary facets of the original triangulation. -/
lemma restricted_fullCells_eq_specialBoundary {m n : ℕ} {S : AffineSimplex m (n + 1)}
    (T : Triangulation S) (f : Euclidean m → Fin (n + 2)) (hf : RespectsFaces T f)
    (j : Fin (n + 2))
    (U : Triangulation (S.face (fs := Finset.univ.erase j) (m := n) (by simp)))
    (hU : U.complex = inducedComplex T (Finset.univ.erase j)) :
    fullCells U (faceLabelInverse (Finset.univ.erase j) (by simp) ∘ f) =
      specialBoundary T f j := by
  let I := Finset.univ.erase j
  let hI : I.card = n + 1 := by simp [I]
  let r := faceLabelInverse I hI
  let e := I.orderEmbOfFin hI
  ext C
  constructor
  · intro hC
    obtain ⟨hCU, hlabels⟩ := Finset.mem_filter.mp hC
    obtain ⟨hCUcell, hcard⟩ := Finset.mem_filter.mp hCU
    have hCind : C ∈ inducedCells T I := by
      change C ∈ (inducedComplex T I).cells
      rw [← hU]
      exact hCUcell
    obtain ⟨hCT, hCI⟩ := (inducedCells_iff T I C).mp hCind
    have hlabel_eq : C.image f = I := by
      calc
        C.image f = (C.image (r ∘ f)).image e := by
          rw [Finset.image_image]
          apply Finset.image_congr
          intro v hv
          exact (faceLabelInverse_right I hI
            (hf I v (vertex_of_cell T.complex hCT hv) (hCI (subset_convexHull ℝ _ hv)))).symm
        _ = I := by
          rw [hlabels]
          exact Finset.image_orderEmbOfFin_univ I hI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, hlabel_eq⟩
    · exact Finset.mem_filter.mpr ⟨hCT, Nat.succ_pos _, hcard⟩
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨j, hCI hx⟩
  · intro hC
    have hCI := specialBoundary_in_original_face T f hf j hC
    obtain ⟨hb, hlabels⟩ := Finset.mem_filter.mp hC
    obtain ⟨hfacet, _⟩ := Finset.mem_filter.mp hb
    obtain ⟨hCT, _, hcard⟩ := Finset.mem_filter.mp hfacet
    have hCU : C ∈ U.complex.cells := by
      rw [hU]
      exact (inducedCells_iff T I C).mpr ⟨hCT, hCI⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hCU, hcard⟩, ?_⟩
    change C.image (r ∘ f) = Finset.univ
    rw [← Finset.image_image, hlabels]
    exact image_faceLabelInverse I hI

lemma fullCells_zero {m : ℕ} {S : AffineSimplex m 0} (T : Triangulation S)
    (f : Euclidean m → Fin 1) : (fullCells T f).card = 1 := by
  have hS : simplexHull S = {S.points 0} := by
    have hr : Set.range S.points = {S.points 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        exact congrArg S.points (Fin.ext (by omega))
      · rintro rfl
        exact ⟨0, rfl⟩
    change convexHull ℝ (Set.range S.points) = _
    rw [hr, convexHull_singleton]
  have htop : ∀ C ∈ topCells T, C = {S.points 0} := by
    intro C hC
    obtain ⟨hcell, hcard⟩ := Finset.mem_filter.mp hC
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      have hp := cellHull_subset_simplexHull T hcell (subset_convexHull ℝ _ hv)
      rw [hS] at hp
      exact Finset.mem_singleton.mpr hp
    · simp only [Finset.card_singleton, hcard]; omega
  obtain ⟨C, hC, _⟩ := exists_topCell_superset T T.complex.empty_mem
  have htopEq : topCells T = {{S.points 0}} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨htop C hC ▸ hC, htop⟩
  have hf0 : f (S.points 0) = 0 := Fin.ext (by omega)
  unfold fullCells
  rw [htopEq, Finset.filter_singleton]
  have hlabel : Finset.image f {S.points 0} = Finset.univ := by
    rw [Finset.image_singleton, hf0]
    ext a
    simp only [Finset.mem_singleton, Finset.mem_univ, iff_true]
    exact Fin.ext (by omega)
  rw [ite_eq_left hlabel]
  exact Finset.card_singleton _

/-- Sperner parity for arbitrary affine simplexes and total vertex labels. -/
theorem fullCells_odd : ∀ n : ℕ, ∀ {m : ℕ} {S : AffineSimplex m n}
    (T : Triangulation S) (f : Euclidean m → Fin (n + 1)),
    RespectsFaces T f → Odd (fullCells T f).card := by
  intro n
  induction n with
  | zero =>
      intro m S T f _
      rw [fullCells_zero T f]
      exact ⟨0, rfl⟩
  | succ n ih =>
      intro m S T f hf
      let j : Fin (n + 2) := Fin.last (n + 1)
      obtain ⟨U, hU⟩ := original_facet_triangulation T j
      let r := faceLabelInverse (Finset.univ.erase j) (show (Finset.univ.erase j).card = n + 1 by simp)
      have huOdd := ih U (r ∘ f)
        (restrict_respectsFaces T f hf _ (by simp) U hU)
      rw [restricted_fullCells_eq_specialBoundary T f hf j U hU] at huOdd
      apply ZMod.natCast_eq_one_iff_odd.mp
      rw [incidence_parity T (Nat.succ_pos _) f j]
      exact huOdd.natCast_zmod_two

/-- Extend the canonical vertex labeling for use in the counting argument. -/
def extendLabel {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
    (ℓ : VertexLabeling T) (v : Euclidean m) : Fin (n + 1) :=
  if hv : v ∈ vertices T.complex then ℓ ⟨v, hv⟩ else 0

lemma extendLabel_at_vertex {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
    (ℓ : VertexLabeling T) {v : Euclidean m} (hv : v ∈ vertices T.complex) :
    extendLabel T ℓ v = ℓ ⟨v, hv⟩ := by
  simp only [extendLabel, hv, dite_true]

lemma cellLabels_extendLabel {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
    (ℓ : VertexLabeling T) (C : Finset (Euclidean m)) (hC : C ∈ T.complex.cells) :
    cellLabels T ℓ C hC = C.image (extendLabel T ℓ) := by
  ext i
  change (i ∈ C.attach.image _) ↔ _
  simp only [Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v.val, v.property, ?_⟩
    rw [extendLabel_at_vertex T ℓ (vertex_of_cell T.complex hC v.property)]
    exact hv
  · rintro ⟨v, hv, hlabel⟩
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [extendLabel_at_vertex T ℓ (vertex_of_cell T.complex hC hv)] at hlabel
    exact hlabel

lemma fullCells_extendLabel {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
    (ℓ : VertexLabeling T) : fullyLabeledCells T ℓ = fullCells T (extendLabel T ℓ) := by
  ext C
  simp only [fullyLabeledCells,
    Specs.D10Topology.Ch17.SimplexTriangulation.fullyLabeledCellsValue,
    fullCells, topCells, Specs.D10Topology.Ch17.SimplexTriangulation.topCellsValue,
    Finset.mem_filter]
  change (C ∈ T.complex.cells ∧ (∃ hC : C ∈ T.complex.cells,
      C.card = n + 1 ∧ cellLabels T ℓ C hC = Finset.univ)) ↔
    ((C ∈ T.complex.cells ∧ C.card = n + 1) ∧ C.image (extendLabel T ℓ) = Finset.univ)
  constructor
  · rintro ⟨hC, _, hcard, hlabels⟩
    exact ⟨⟨hC, hcard⟩, (cellLabels_extendLabel T ℓ C hC).symm.trans hlabels⟩
  · rintro ⟨⟨hC, hcard⟩, hlabels⟩
    exact ⟨hC, hC, hcard, (cellLabels_extendLabel T ℓ C hC).trans hlabels⟩

end SpernerCounting

/-- Geometric Sperner's lemma, including its odd-count conclusion and dimension zero. -/
theorem sperner_odd : Specs.D10Topology.Ch17.Sperner.sperner_odd := by
  intro m n S T ℓ hℓ
  change Odd (fullyLabeledCells T ℓ).card
  rw [SpernerCounting.fullCells_extendLabel T ℓ]
  apply SpernerCounting.fullCells_odd n T (SpernerCounting.extendLabel T ℓ)
  intro I v hv hvI
  rw [SpernerCounting.extendLabel_at_vertex T ℓ hv]
  exact hℓ I ⟨v, hv⟩ hvI

/-- In particular, every face-respecting labeling has a fully labeled top cell. -/
theorem sperner_exists : Specs.D10Topology.Ch17.Sperner.sperner_exists := by
  intro m n S T ℓ hℓ
  have ho : Odd (fullyLabeledCells T ℓ).card := sperner_odd T ℓ hℓ
  have hpos : 0 < (fullyLabeledCells T ℓ).card := by
    obtain ⟨k, hk⟩ := ho
    omega
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
  obtain ⟨_, hfull⟩ := Finset.mem_filter.mp hC
  have ht : C ∈ topCells T := by
    obtain ⟨hcell, hcard, _⟩ := hfull
    exact Finset.mem_filter.mpr ⟨hcell, hcard⟩
  exact ⟨C, ht, hfull⟩

end D10Topology.Ch17
