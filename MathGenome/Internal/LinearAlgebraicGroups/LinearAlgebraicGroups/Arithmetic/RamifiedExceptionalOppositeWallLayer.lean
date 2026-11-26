import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalOppositeWallLayer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import Batteries.Tactic.OpenPrivate

/-! Opposite simple wall layers in the marked ramified outer E₆ group. -/

namespace LinearAlgebraicGroups.RamifiedExceptionalOppositeWallLayer

open CategoryTheory ValuativeRel
open scoped CategoryTheory.MonObj Classical Matrix TensorProduct WithZero
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems (ApartmentRoots FoldedRootDirection IsLongF4Doubled
  foldedDepthDenominator)
open Specs.ExceptionalIwahoriCongruence (CellValues cellValue integralRing)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (markedRootPoint markedCellPoint markedWeylWord
  orderedRootPoint weylWordPerm)
open Specs.IntegralRootRelations (upper lower)
open Specs.IntegralSemisimpleModel (Integers Model IntegralMarking IntegralPoints IntegralAlgebra
  TorusValues torusPoint integerAlgebra)
open Specs.OrderedRootProducts (Enumerates)
open Specs.Pinning (BasedRootDatum BasedIso)
open Arithmetic.AffineArrangement (Datum)

universe u

attribute [local instance] integerAlgebra Specs.ExceptionalLocalRootCoordinates.canonicalExtension

open private cellValue_ofAbsoluteParameters from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open private markedRootPoint_zero markedTorusPointHom_apply from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private weylWord_index quadraticGalois from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

private theorem prod_filter_eq_prod_of_one {I H : Type*} [Monoid H] (l : List I)
    (g : I → H) (p : I → Bool) (h : ∀ i ∈ l, p i = false → g i = 1) :
    ((l.filter p).map g).prod = (l.map g).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    cases ha : p a <;> simp [ha, ht, h a List.mem_cons_self]

private theorem cellValue_supported {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (S : IntegralAlgebra.{u}) (ns ps ls : List D.I)
    (hn : Enumerates ns {i | ¬ D.base.IsPos i}) (hp : Enumerates ps {i | D.base.IsPos i})
    (hl : ls.Nodup) (v : D.I → S) (hv : ∀ i ∉ ls, v i = 0)
    (hc : ∀ i ∈ ls, ∀ j ∈ ls, i ≠ j →
      Commute (markedRootPoint M S i (v i)) (markedRootPoint M S j (v j))) :
    cellValue M S ns ps (fun a => v ns[a], 1, fun a => v ps[a]) =
      (ls.map fun i => markedRootPoint M S i (v i)).prod := by
  classical
  let g := fun i => markedRootPoint M S i (v i)
  let p := fun i => decide (i ∈ ls)
  have ht : (torusPoint D S 1 ≫ M.torus.hom.hom : IntegralPoints M.group S) = 1 := by
    rw [← markedTorusPointHom_apply]
    exact map_one _
  rw [cellValue_ofAbsoluteParameters, markedCellPoint, ht, one_mul,
    orderedRootPoint, orderedRootPoint, ← List.prod_append, ← List.map_append]
  have hnd : (ns ++ ps).Nodup := List.nodup_append.mpr
    ⟨hn.1, hp.1, fun i hi j hj e => (hn.2 i).mp hi (e ▸ (hp.2 j).mp hj)⟩
  have hall (i : D.I) : i ∈ ns ++ ps := by
    by_cases hi : D.base.IsPos i
    · exact List.mem_append_right _ ((hp.2 i).mpr hi)
    · exact List.mem_append_left _ ((hn.2 i).mpr hi)
  have hperm : ls.Perm ((ns ++ ps).filter p) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hl (hnd.filter _)
    ext i
    simp only [List.mem_toFinset, List.mem_filter, p, decide_eq_true_eq, hall i, true_and]
  have hcomm : (ls.map g).Pairwise Commute := by
    rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij
    exact hc _ (List.getElem_mem hi) _ (List.getElem_mem hj)
      (fun e => (Nat.ne_of_lt hij) (congrArg Fin.val (hl.injective_get e)))
  change (((ns ++ ps).map g).prod) = (ls.map g).prod
  rw [← prod_filter_eq_prod_of_one (ns ++ ps) g p (fun i _ hi => by
    have hm : i ∉ ls := by simpa [p] using hi
    simp [g, hv i hm, markedRootPoint_zero])]
  exact ((hperm.map g).prod_eq' hcomm).symm

private noncomputable def extendCoordinates {B I K : Type*} [Zero K]
    (l : List B) (label : B → I) (v : B → K) (i : I) : K :=
  if h : ∃ b ∈ l, label b = i then v h.choose else 0

private theorem extendCoordinates_apply {B I K : Type*} [Zero K]
    {l : List B} {label : B → I} (h : (l.map label).Nodup) (v : B → K)
    {b : B} (hb : b ∈ l) : extendCoordinates l label v (label b) = v b := by
  classical
  have hmem : ∃ b' ∈ l, label b' = label b := ⟨b, hb, rfl⟩
  rw [extendCoordinates, dite_eq_left hmem]
  congr 1
  exact ((List.nodup_map_iff_inj_on (h.of_map _)).mp h)
    _ hmem.choose_spec.1 _ hb hmem.choose_spec.2

private theorem extendCoordinates_zero {B I K : Type*} [Zero K]
    {l : List B} {label : B → I} (v : B → K) {i : I} (hi : i ∉ l.map label) :
    extendCoordinates l label v i = 0 := by
  classical
  rw [extendCoordinates, dite_eq_right]
  simpa only [List.mem_map] using hi

private theorem indexEquiv_neg {D : BasedRootDatum.{u}} (w : D.datum.Aut) (i : D.I) :
    w.indexEquiv (D.datum.reflectionPerm i i) =
      D.datum.reflectionPerm (w.indexEquiv i) (w.indexEquiv i) := by
  apply D.datum.root_eq_neg_iff.mp
  rw [← RootPairing.Hom.root_weightMap_apply _ _ _ w.toHom,
    ← RootPairing.Hom.root_weightMap_apply _ _ _ w.toHom,
    D.datum.root_eq_neg_iff.mpr rfl, map_neg]

private theorem foldedRoot_injective {D : BasedRootDatum.{u}} {τ : BasedIso D D}
    (A : FoldedApartment τ) : Function.Injective A.roots.root := by
  let B := A.roots.transport A.coordinates.symm
  have hB : B.root = Specs.ExceptionalAffineRootSystems.normalizedFoldedRoot ℚ := by
    funext i
    apply LinearMap.ext
    intro x
    exact A.normalized_root i x
  intro i j h
  apply (Arithmetic.ExceptionalAffineRootSystems.foldedReducedDirections B hB).1
  change (A.roots.root i).comp A.coordinates.toLinearMap =
    (A.roots.root j).comp A.coordinates.toLinearMap
  rw [h]

private theorem foldedNeg_long {D : BasedRootDatum.{u}} {τ : BasedIso D D}
    (A : FoldedApartment τ) (i : D.I) :
    IsLongF4Doubled (A.direction (D.datum.reflectionPerm i i)).val ↔
      IsLongF4Doubled (A.direction i).val := by
  rw [A.long, A.long, indexEquiv_neg τ.val]
  let _ := D.datum.indexNeg
  exact neg_inj

private theorem foldedNeg_root {D : BasedRootDatum.{u}} {τ : BasedIso D D}
    (A : FoldedApartment τ) (i : D.I) :
    A.roots.root (A.direction (D.datum.reflectionPerm i i)) = -A.roots.root (A.direction i) := by
  have hd : foldedDepthDenominator (A.direction (D.datum.reflectionPerm i i)) =
      foldedDepthDenominator (A.direction i) := by
    unfold foldedDepthDenominator
    simp only [foldedNeg_long A i]
  have hroot : D.datum.root' (D.datum.reflectionPerm i i) = -D.datum.root' i := by
    simp [RootPairing.root']
  ext x
  rw [LinearMap.neg_apply, A.root_value, A.root_value, hd]
  change (_ : ℚ) * RootData.extendFunctional ℚ
    (D.datum.root' (D.datum.reflectionPerm i i)) x.val =
      -(_ * RootData.extendFunctional ℚ (D.datum.root' i) x.val)
  rw [hroot]
  simp [RootData.extendFunctional, LinearMap.baseChange_neg]

private theorem foldedNeg_opposite {D : BasedRootDatum.{u}} {τ : BasedIso D D}
    (A : FoldedApartment τ) (a : FoldedRootDirection × ℤ) (i : D.I)
    (hi : A.direction i = a.1) :
    A.direction (D.datum.reflectionPerm i i) = (A.roots.opposite a).1 := by
  have h := foldedNeg_root A i
  rw [hi] at h
  have hex : ∃ j, A.roots.root j = -A.roots.root a.1 := ⟨_, h⟩
  unfold Datum.opposite
  rw [dite_eq_left hex]
  exact foldedRoot_injective A (h.trans hex.choose_spec.symm)

section Slots

variable {K : Type u} [Field K] {D : BasedRootDatum.{u}} {M : Model D}
  {G : Type u} [Group G] {j : G →* FieldPoints M K}
  {V : Type u} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V FoldedRootDirection} {p : V}

private abbrev absoluteCell (C : LocalRootChart (j := j) A p) (x : D.I → K)
    (t : TorusValues D (integralRing K)) : CellValues D (integralRing K) C.negative C.positive :=
  (fun i => x C.negative[i], t, fun i => x C.positive[i])

private structure RootSlot (C : LocalRootChart (j := j) A p) (i : D.I) (a : FoldedRootDirection) where
  embedding : C.parameter a →+* K
  unit : Integers.{u}ˣ
  read : CellValues D (integralRing K) C.negative C.positive → K
  read_absolute (x : D.I → K) (t) : read (absoluteCell C x t) = x i
  read_coordinates (t : C.chart.torus) (x : ∀ b, C.parameter b) :
    read (C.chart.coordinates t x) = algebraMap Integers.{u} K unit * embedding (x a)
  embedding_eq (e : C.parameter a →+* K) (he : C.UsesSlot i a e) : embedding = e

private theorem ringHom_transport_apply {J : Type*} {P : J → Type u} [∀ a, Field (P a)]
    {a b : J} (h : a = b) (f : P a →+* K) (x : P b) :
    (h ▸ f : P b →+* K) x = f (h.symm ▸ x) := by
  cases h
  rfl

private theorem transport_section {J : Type*} {P : J → Type u} {a b : J} (h : a = b)
    (x : ∀ j, P j) : (h.symm ▸ x b : P a) = x a := by
  cases h
  rfl

private theorem rootSlot_nonempty (C : LocalRootChart (j := j) A p) (i : D.I) (a : FoldedRootDirection)
    (ha : C.direction i = a) : Nonempty (RootSlot C i a) := by
  classical
  by_cases hi : D.base.IsPos i
  · obtain ⟨l, hl⟩ := List.get_of_mem ((C.positive_enumerates.2 i).mpr hi)
    have h : C.chart.pos l = a := (C.pos_slots l).trans ((congrArg C.direction hl).trans ha)
    refine ⟨⟨h ▸ C.chart.posMap l, C.chart.posUnit l, fun z => z.2.2 l,
      fun x _ => congrArg x hl, ?_, ?_⟩⟩
    · intro t x
      change _ * C.chart.posMap l (x (C.chart.pos l)) =
        _ * (h ▸ C.chart.posMap l) (x a)
      rw [ringHom_transport_apply h, transport_section h]
    · intro e he
      ext x
      have hx := he.2.2 l h x hl
      rw [ringHom_transport_apply h]
      exact hx
  · obtain ⟨l, hl⟩ := List.get_of_mem ((C.negative_enumerates.2 i).mpr hi)
    have h : C.chart.neg l = a := (C.neg_slots l).trans ((congrArg C.direction hl).trans ha)
    refine ⟨⟨h ▸ C.chart.negMap l, C.chart.negUnit l, fun z => z.1 l,
      fun x _ => congrArg x hl, ?_, ?_⟩⟩
    · intro t x
      change _ * C.chart.negMap l (x (C.chart.neg l)) =
        _ * (h ▸ C.chart.negMap l) (x a)
      rw [ringHom_transport_apply h, transport_section h]
    · intro e he
      ext x
      have hx := he.2.1 l h x hl
      rw [ringHom_transport_apply h]
      exact hx

end Slots

section FoldedSlots

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} (T : DiagramCompositum F L k σ) {A : FoldedApartment (R.diagram σ)}
  (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)

private theorem foldedSlot_data (i : D.I) (a : FoldedRootDirection) (hi : A.direction i = a)
    (s : RootSlot X.comparison.chart i a) :
    Set.range s.embedding =
      (if IsLongF4Doubled a.val then Set.range (algebraMap k T.field) else Set.univ) ∧
    ∀ x, normalizedValuation T.field (s.embedding x) =
      (X.comparison.chart.value a x) ^ (if IsLongF4Doubled a.val then (2 : ℕ) else 1) := by
  subst a
  by_cases hlong : IsLongF4Doubled (A.direction i).val
  · obtain ⟨e, he, hv⟩ := X.singleton i ((A.long i).mp hlong)
    rw [s.embedding_eq _ he, ite_eq_left hlong, ite_eq_left hlong]
    constructor
    · ext z
      exact ⟨fun ⟨x, hx⟩ => ⟨e x, hx⟩, fun ⟨y, hy⟩ => ⟨e.symm y, by simpa using hy⟩⟩
    · intro x
      change normalizedValuation T.field (algebraMap k T.field (e x)) = _
      rw [X.ramification, hv]
  · obtain ⟨b, hb, e, he, he', hv⟩ := X.pair (A.direction i) hlong
    have hσ : Function.Involutive T.diagram := fun z =>
      congrArg (fun g : Gal(T.field/k) => g z) (quadraticGalois T.degree T.diagram T.diagram_ne).2
    have hval := Arithmetic.ExceptionalLocalRootCoordinates.involutionPreservesValuation T.diagram hσ
    rw [ite_eq_right hlong, ite_eq_right hlong]
    rcases (A.orbits b i).mp hb with rfl | hi
    · rw [s.embedding_eq _ he]
      exact ⟨Set.range_eq_univ.mpr e.surjective, fun x => by rw [hv, pow_one]; rfl⟩
    · have hslot : X.comparison.chart.UsesSlot i (A.direction i)
          (T.diagram.toRingHom.comp e.toRingHom) := hi.symm ▸ he'
      rw [s.embedding_eq _ hslot]
      exact ⟨Set.range_eq_univ.mpr (T.diagram.surjective.comp e.surjective),
        fun x => by
          rw [hv, pow_one]
          exact hval (e x)⟩

end FoldedSlots

private theorem range_integralUnit_mul {P K : Type u} [Field P] [Field K]
    (f : P →+* K) (s : Integers.{u}ˣ) :
    Set.range (fun x => algebraMap Integers.{u} K (s : Integers.{u}) * f x) =
      Set.range f := by
  let c : Pˣ := Units.map (algebraMap Integers.{u} P).toMonoidHom s
  have hc : f (c : P) = algebraMap Integers.{u} K (s : Integers.{u}) := by
    change f ((s : Integers.{u}).down : P) = ((s : Integers.{u}).down : K)
    exact map_intCast f _
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(c : P) * x, by rw [map_mul, hc]⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(↑c⁻¹ : P) * x, ?_⟩
    change algebraMap Integers.{u} K (s : Integers.{u}) * f ((↑c⁻¹ : P) * x) = f x
    rw [← hc, ← map_mul, ← mul_assoc, Units.mul_inv, one_mul]

private theorem integralUnit_mul_injective {P K : Type u} [Field P] [Field K]
    (f : P →+* K) (s : Integers.{u}ˣ) :
    Function.Injective fun x => algebraMap Integers.{u} K (s : Integers.{u}) * f x :=
  fun _ _ h => f.injective
    (mul_left_cancel₀ (Units.map (algebraMap Integers.{u} K).toMonoidHom s).ne_zero h)

private theorem compareParameterFields {P Q K : Type u} [Field P] [Field Q] [Field K]
    (f : P →+* K) (g : Q →+* K) (s t : Integers.{u}ˣ) (h : Set.range f = Set.range g) :
    ∃ e : P ≃ Q, ∀ z, algebraMap Integers.{u} K (s : Integers.{u}) * f z =
      algebraMap Integers.{u} K (t : Integers.{u}) * g (e z) := by
  let f' := fun x => algebraMap Integers.{u} K (s : Integers.{u}) * f x
  let g' := fun x => algebraMap Integers.{u} K (t : Integers.{u}) * g x
  have he : Set.range f' = Set.range g' :=
    (range_integralUnit_mul f s).trans (h.trans (range_integralUnit_mul g t).symm)
  have hf := integralUnit_mul_injective f s
  have hg := integralUnit_mul_injective g t
  have hex (x : P) : f' x ∈ Set.range g' := by
    rw [← he]
    exact Set.mem_range_self x
  choose e e_eq using hex
  refine ⟨Equiv.ofBijective e ⟨fun x y hxy => hf ((e_eq x).symm.trans
    ((congrArg g' hxy).trans (e_eq y))), fun y => ?_⟩, fun x => (e_eq x).symm⟩
  obtain ⟨x, hx⟩ : g' y ∈ Set.range f' := he.symm ▸
    (Set.mem_range_self y : g' y ∈ Set.range g')
  exact ⟨x, hg ((e_eq x).trans hx)⟩

section Transport

open Matrix (SpecialLinearGroup)
open private map_upperMatrix from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

private theorem map_lowerMatrix {P K : Type u} [Field P] [Field K] (f : P →+* K) (z : P) :
    SpecialLinearGroup.map f (lower z) = lower (f z) := by
  apply Subtype.ext
  change (!![1, 0; z, 1] : Matrix (Fin 2) (Fin 2) P).map f = !![1, 0; f z, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private def rankOneIndex {D : BasedRootDatum.{u}} (op : Bool) (i : D.I) : D.I :=
  if op then D.datum.reflectionPerm i i else i

private def rankOneElement {P : Type u} [Field P] (op : Bool) (z : P) :
    SpecialLinearGroup (Fin 2) P :=
  if op then lower z else upper z

private theorem rankOne_transport {D : BasedRootDatum.{u}} (M : Model D)
    {P K : Type u} [Field P] [Field K] (word : List D.I)
    (unit : D.I → Integers.{u}ˣ)
    (hunit : ∀ i (z : K),
      let S := integralRing K
      let m := markedWeylWord M.toIntegralMarking S word
      m * markedRootPoint M.toIntegralMarking S i z * m⁻¹ =
        markedRootPoint M.toIntegralMarking S (weylWordPerm word i)
          (algebraMap Integers.{u} K (unit i : Integers.{u}) * z))
    (op : Bool) (ns ps : List D.I) (hn : Enumerates ns {i | ¬ D.base.IsPos i})
    (hp : Enumerates ps {i | D.base.IsPos i})
    (hs : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (orbit : List (D.base.support × (P →+* K))) :
    let S := integralRing K
    let m := markedWeylWord M.toIntegralMarking S word
    let label := fun b : D.base.support × (P →+* K) => weylWordPerm word (rankOneIndex op b.1.val)
    (orbit.map label).Nodup →
    (∀ i ∈ orbit.map label, ∀ j ∈ orbit.map label, i ≠ j → D.datum.pairing i j = 0) →
    ∀ z : P,
    let v := extendCoordinates orbit label (fun b =>
      algebraMap Integers.{u} K (unit (rankOneIndex op b.1.val) : Integers.{u}) * b.2 z)
    m * (orbit.map (fun b => (show FieldPoints M K from
      (M.rankOne b.1).app S (SpecialLinearGroup.map b.2 (rankOneElement op z))))).prod * m⁻¹ =
      cellValue M.toIntegralMarking S ns ps (fun i => v ns[i], 1, fun i => v ps[i]) := by
  intro S m label hnd horth z v
  rw [cellValue_supported M.toIntegralMarking S ns ps _ hn hp hnd v]
  · change (MulAut.conj m) (List.map _ orbit).prod = _
    rw [map_list_prod, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro b hb
    have hroot : ((M.rankOne b.1).app S
        (SpecialLinearGroup.map b.2 (rankOneElement op z)) : FieldPoints M K) =
        markedRootPoint M.toIntegralMarking S (rankOneIndex op b.1.val) (b.2 z) := by
      cases op
      · rw [show rankOneElement false z = upper z from rfl, map_upperMatrix, M.rankOneUpper]
        rfl
      · rw [show rankOneElement true z = lower z from rfl, map_lowerMatrix, M.rankOneLower]
        rfl
    change MulAut.conj m ((M.rankOne b.1).app S
      (SpecialLinearGroup.map b.2 (rankOneElement op z))) =
      markedRootPoint M.toIntegralMarking S (label b) (v (label b))
    rw [hroot]
    change m * _ * m⁻¹ = _
    rw [hunit]
    have hv : v (label b) =
        algebraMap Integers.{u} K (unit (rankOneIndex op b.1.val) : Integers.{u}) * b.2 z :=
      extendCoordinates_apply hnd (fun b => algebraMap Integers.{u} K
        (unit (rankOneIndex op b.1.val) : Integers.{u}) * b.2 z) hb
    rw [hv]
  · exact fun i hi => extendCoordinates_zero (K := K) _ hi
  · intro i hi j hj hij
    rw [markedRootPoint, markedRootPoint, ← M.rankOneUpper, ← M.rankOneUpper]
    exact Arithmetic.ExceptionalMarkedRootDescent.markedOrthogonalRankOneCommutation M hs i j
      (horth i hi j hj hij) K (CommAlgCat.of K K) (upper (v i)) (upper (v j))

end Transport

section RationalChart

variable {K : Type u} [Field K] {D : BasedRootDatum.{u}} {M : Model D}
  {G : Type u} [Group G] {j : G →* FieldPoints M K}
  {V : Type u} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V FoldedRootDirection} {p : V}

private theorem rationalChart_single (C : LocalRootChart (j := j) A p)
    (hs : Function.Surjective C.direction) (u₀ : C.chart.torus) (hu : u₀.val = 1)
    (a : FoldedRootDirection) (v : D.I → K) (hv : ∀ i, C.direction i ≠ a → v i = 0)
    (hr : cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
      (absoluteCell C v 1) ∈ j.range) :
    ∃ y : C.parameter a, C.chart.coordinates u₀ (Function.update (fun _ => 0) a y) =
      absoluteCell C v 1 := by
  obtain ⟨t, x, htx⟩ := (C.rational _).mp hr
  have ht : t = u₀ := Subtype.ext ((congrArg (fun t => t.2.1) htx).trans hu.symm)
  subst t
  have hz (b : FoldedRootDirection) (hb : b ≠ a) : x b = 0 := by
    obtain ⟨i, hi⟩ := hs b
    obtain ⟨s⟩ := rootSlot_nonempty C i b hi
    have he := congrArg s.read htx
    rw [s.read_coordinates, s.read_absolute, hv i (hi.trans_ne hb)] at he
    apply integralUnit_mul_injective s.embedding s.unit
    simpa only [map_zero, mul_zero] using he
  refine ⟨x a, ?_⟩
  have he : Function.update (fun _ => 0) a (x a) = x := by
    funext b
    by_cases hb : b = a
    · subst b
      exact Function.update_self a (x a) _
    · rw [Function.update_of_ne hb, hz b hb]
  rw [he, htx]

end RationalChart

open WithZero

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- The same marked rank-one map supplies the entire opposite layer in the
ordered chart, with valuations in the original parameter-field steps. -/
theorem oppositeWallLayer :
    Specs.RamifiedExceptionalOppositeWallLayer.OppositeWallLayer.{u} := by
  intro F L k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    σ _ _ _ _ D M R numbering hNum _ hτ A T X a C P S opposite labels
    word orbit r _ c u₀ _ _ hnd hlabels hRank hu hc hUpper _ _
  have hdec : (fun i j : FoldedRootDirection => Classical.propDecidable (i = j)) =
      (inferInstance : DecidableEq FoldedRootDirection) := Subsingleton.elim _ _
  rw [hdec] at hUpper
  let K := T.field
  let wallDir := a.val.1
  let oppositeDir := opposite.1
  let B := D.base.support × (P →+* K)
  let w := ((word.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val
  let negate (i : D.I) := D.datum.reflectionPerm i i
  let plus (b : B) := weylWordPerm word b.1.val
  let minus (b : B) := weylWordPerm word (negate b.1.val)
  have hminus (b : B) : minus b = negate (plus b) := by
    simp only [plus, minus, weylWord_index]
    exact indexEquiv_neg w b.1.val
  have hndUpper : (orbit.map plus).Nodup := by
    simpa only [plus, weylWord_index, labels] using hnd
  have hndLower : (orbit.map minus).Nodup := by
    have hmap : orbit.map minus = (orbit.map plus).map negate := by
      rw [List.map_map]
      exact congrArg (fun f => orbit.map f) (funext hminus)
    have hinj : Function.Injective negate := by
      let _ := D.datum.indexNeg
      exact neg_injective
    rw [hmap]
    exact hndUpper.map hinj
  have hfibre (i : D.I) : C.direction i = wallDir ↔ i ∈ orbit.map plus := by
    simpa only [wallDir, plus, weylWord_index, labels] using hlabels i
  have hfoldUpper (i : D.I) (hi : i ∈ orbit.map plus) : A.direction i = wallDir := by
    rw [← X.directions]
    exact (hfibre i).mpr hi
  have hfoldLower (b : B) (hb : b ∈ orbit) : A.direction (minus b) = oppositeDir := by
    rw [hminus]
    exact foldedNeg_opposite A a.val (plus b) (hfoldUpper _ (List.mem_map_of_mem hb))
  obtain ⟨_, _, hsym⟩ := Arithmetic.ExceptionalAffineBruhat.e6LocalRootSymmetries
    D numbering (R.diagram σ) hNum hτ
  have horthUpper (i : D.I) (hi : i ∈ orbit.map plus) (j : D.I) (hj : j ∈ orbit.map plus)
      (hne : i ≠ j) : D.datum.pairing i j = 0 := by
    rcases (A.orbits i j).mp ((hfoldUpper i hi).trans (hfoldUpper j hj).symm) with h | h
    · exact (hne h.symm).elim
    · subst j
      exact A.orthogonal i hne.symm
  have horthLower (i : D.I) (hi : i ∈ orbit.map minus) (j : D.I) (hj : j ∈ orbit.map minus)
      (hne : i ≠ j) : D.datum.pairing i j = 0 := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hj
    have hne' : plus b ≠ plus b' := by
      intro h
      apply hne
      rw [hminus, hminus, h]
    rw [hminus, hminus]
    simp only [negate, RootPairing.pairing_reflectionPerm_self_left,
      RootPairing.pairing_reflectionPerm_self_right, neg_neg]
    exact horthUpper _ (List.mem_map_of_mem hb) _ (List.mem_map_of_mem hb') hne'
  choose unit hunit using fun i =>
    Arithmetic.ExceptionalMarkedRootDescent.integralWeylWordTransport M word i
  have hunitK (i : D.I) (z : K) :
      let m := markedWeylWord M.toIntegralMarking (integralRing K) word
      m * markedRootPoint M.toIntegralMarking (integralRing K) i z * m⁻¹ =
        markedRootPoint M.toIntegralMarking (integralRing K) (weylWordPerm word i)
          (algebraMap Integers.{u} K (unit i : Integers.{u}) * z) :=
    hunit i (integralRing K) z
  let unitValue (s : Integers.{u}ˣ) : K := algebraMap Integers.{u} K (s : Integers.{u})
  let vUpper (z : P) := extendCoordinates orbit plus (fun b => unitValue (unit b.1.val) * b.2 z)
  let vLower (z : P) := extendCoordinates orbit minus (fun b => unitValue (unit (negate b.1.val)) * b.2 z)
  have hcellUpper (z : P) : X.points (r (upper z)) =
      cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
        (absoluteCell C (vUpper z) 1) := by
    refine (hRank (upper z)).trans ?_
    exact rankOne_transport M (P := P) (K := K) word unit hunitK false C.negative C.positive
      C.negative_enumerates C.positive_enumerates hsym orbit hndUpper horthUpper z
  have hcellLower (z : P) : X.points (r (lower z)) =
      cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
        (absoluteCell C (vLower z) 1) := by
    refine (hRank (lower z)).trans ?_
    exact rankOne_transport M (P := P) (K := K) word unit hunitK true C.negative C.positive
      C.negative_enumerates C.positive_enumerates hsym orbit hndLower horthLower z
  have hsupport (z : P) (i : D.I) (hi : C.direction i ≠ oppositeDir) : vLower z i = 0 := by
    refine extendCoordinates_zero _ (fun h => ?_)
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
    exact hi (by rw [X.directions]; exact hfoldLower b hb)
  obtain ⟨i, hi⟩ := A.surjective wallDir
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ((hfibre i).mp (by rw [X.directions]; exact hi))
  have hiLower := hfoldLower b hb
  obtain ⟨sUpper⟩ := rootSlot_nonempty C (plus b) wallDir (by rw [X.directions]; exact hi)
  obtain ⟨sLower⟩ := rootSlot_nonempty C (minus b) oppositeDir (by rw [X.directions]; exact hiLower)
  obtain ⟨hrangeUpper, hvalUpper⟩ := foldedSlot_data T X (plus b) wallDir hi sUpper
  obtain ⟨hrangeLower, hvalLower⟩ := foldedSlot_data T X (minus b) oppositeDir hiLower sLower
  have hlong : IsLongF4Doubled oppositeDir.val ↔ IsLongF4Doubled wallDir.val := by
    rw [← hiLower, hminus, ← hi]
    exact foldedNeg_long A (plus b)
  have hinj := (Arithmetic.ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking
    C.negative C.positive C.negative_enumerates C.positive_enumerates).1 (integralRing K)
  have hup (z : P) : unitValue (unit b.1.val) * b.2 z = unitValue sUpper.unit * sUpper.embedding ((c : P) * z) := by
    have h := congrArg sUpper.read (hinj ((hcellUpper z).symm.trans (hUpper z)))
    rw [sUpper.read_absolute, sUpper.read_coordinates,
      show vUpper z (plus b) = unitValue (unit b.1.val) * b.2 z from
        extendCoordinates_apply hndUpper (fun b => unitValue (unit b.1.val) * b.2 z) hb] at h
    change unitValue (unit b.1.val) * b.2 z = unitValue sUpper.unit *
      sUpper.embedding (Function.update (fun _ => 0) wallDir ((c : P) * z) wallDir) at h
    simpa only [Function.update_self] using h
  have hsurj : Function.Surjective (fun z : P => (c : P) * z) := by
    intro z
    refine ⟨(↑c⁻¹ : P) * z, ?_⟩
    change (c : P) * ((↑c⁻¹ : P) * z) = z
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hRange : Set.range b.2 = Set.range sLower.embedding := by
    calc
      Set.range b.2 = Set.range (fun z => unitValue (unit b.1.val) * b.2 z) :=
        (range_integralUnit_mul _ _).symm
      _ = Set.range (fun z : P => unitValue sUpper.unit * sUpper.embedding ((c : P) * z)) :=
        congrArg Set.range (funext hup)
      _ = Set.range (fun z => unitValue sUpper.unit * sUpper.embedding z) :=
        hsurj.range_comp (fun z : P => unitValue sUpper.unit * sUpper.embedding z)
      _ = Set.range sUpper.embedding := range_integralUnit_mul _ _
      _ = Set.range sLower.embedding := by
        refine hrangeUpper.trans (Eq.trans ?_ hrangeLower.symm)
        by_cases h : IsLongF4Doubled wallDir.val
        · rw [ite_eq_left h, ite_eq_left (hlong.mpr h)]
        · rw [ite_eq_right h, ite_eq_right (fun hg => h (hlong.mp hg))]
  obtain ⟨e, he⟩ := compareParameterFields b.2 sLower.embedding (unit (negate b.1.val)) sLower.unit hRange
  have hv (z : P) : C.value oppositeDir (e z) = C.value wallDir z := by
    have valUnit (s : Integers.{u}ˣ) (x : K) :
        normalizedValuation K (unitValue s * x) = normalizedValuation K x :=
      Arithmetic.ExceptionalMarkedRootDescent.integralUnitValuation K s x
    have hUpper := congrArg (normalizedValuation K) (hup z)
    rw [valUnit, valUnit, hvalUpper, map_mul, hc, one_mul] at hUpper
    have hLower := congrArg (normalizedValuation K) (he z)
    change normalizedValuation K (unitValue (unit (negate b.1.val)) * b.2 z) =
      normalizedValuation K (unitValue sLower.unit * sLower.embedding (e z)) at hLower
    rw [valUnit, valUnit, hvalLower] at hLower
    have h := hLower.symm.trans hUpper
    by_cases hwallDir : IsLongF4Doubled wallDir.val
    · rw [ite_eq_left (hlong.mpr hwallDir), ite_eq_left hwallDir] at h
      exact (sq_eq_sq₀ (zero_le : 0 ≤ C.value oppositeDir (e z)) (zero_le : 0 ≤ C.value wallDir z)).mp h
    · rwa [ite_eq_right (fun hg => hwallDir (hlong.mp hg)), ite_eq_right hwallDir, pow_one, pow_one] at h
  have hchart (z : P) : X.points (r (lower z)) =
      cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
        (C.chart.coordinates u₀ (Function.update (fun _ => 0) oppositeDir (e z))) := by
    have hsurj : Function.Surjective C.direction := by rw [X.directions]; exact A.surjective
    obtain ⟨y, hy⟩ := rationalChart_single C hsurj u₀ hu oppositeDir (vLower z) (hsupport z)
      ⟨r (lower z), hcellLower z⟩
    have hy' := congrArg sLower.read hy
    rw [sLower.read_coordinates, sLower.read_absolute, Function.update_self,
      show vLower z (minus b) = unitValue (unit (negate b.1.val)) * b.2 z from
        extendCoordinates_apply hndLower (fun b => unitValue (unit (negate b.1.val)) * b.2 z) hb] at hy'
    have hey : y = e z := integralUnit_mul_injective sLower.embedding sLower.unit
      (hy'.trans (he z))
    rw [← hey, hy]
    exact hcellLower z
  refine ⟨⟨e, fun z => ⟨hv z, hchart z⟩⟩, ?_⟩
  have hlevel : -opposite.2 = a.val.2 := by
    change -(-a.val.2) = a.val.2
    exact neg_neg _
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨u₀, e z, hu, by rwa [hv, hlevel], hchart z⟩
  · rintro ⟨s, y, hs, hy, hg⟩
    have hs' : s = u₀ := Subtype.ext (hs.trans hu.symm)
    subst s
    obtain ⟨z, rfl⟩ := e.surjective y
    refine ⟨z, ?_, X.comparison.point_injective ((hchart z).trans hg.symm)⟩
    rwa [hv, hlevel] at hy

end LinearAlgebraicGroups.RamifiedExceptionalOppositeWallLayer
