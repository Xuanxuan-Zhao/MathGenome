import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.VectorRepresentation
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Duality
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.DualColumns
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

namespace FiniteCombinatorics.Matroid
open Set Submodule Matrix
open scoped _root_.Matroid BigOperators
universe u v w

/-- On a finite index type, independence tests all coefficient functions
supported on the chosen set. -/
lemma linearIndepOn_iff_supported_sum {K : Type u} [Field K]
    {J : Type v} [Fintype J] {V : Type w} [AddCommGroup V] [Module K V]
    (v : J → V) (I : Set J) :
    LinearIndepOn K v I ↔ ∀ f : J → K, (∀ j ∉ I, f j = 0) →
      (∑ j, f j • v j) = 0 → f = 0 := by
  classical
  constructor
  · intro hi f hf hs
    have hs' : ∑ j ∈ Finset.univ.filter (· ∈ I), f j • v j = 0 := by
      rw [Finset.sum_filter]
      simpa only [show (fun j => if j ∈ I then f j • v j else 0) =
        (fun j => f j • v j) from funext (fun j => by
          by_cases h : j ∈ I <;> simp [h, hf j])] using hs
    have hzero := linearIndepOn_iff'.mp hi (Finset.univ.filter (· ∈ I)) f
      (by simp) hs'
    ext j
    by_cases h : j ∈ I
    · exact hzero j (by simp [h])
    · exact hf j h
  · intro hi
    apply linearIndepOn_iff'.mpr
    intro t f ht hs j hj
    let g : J → K := fun j => if j ∈ t then f j else 0
    have hg : g = 0 := hi g (by
      intro j hjI
      have hjt : j ∉ t := fun h => hjI (ht h)
      simp [g, hjt]) (by
        simpa [g, ← Finset.sum_filter] using hs)
    have := congrFun hg j
    simpa [g, hj] using this

/-- A finite family spans the coordinate space exactly when no nonzero
row functional vanishes on every vector. -/
lemma span_eq_top_iff_dotProduct {K : Type u} [Field K]
    {J : Type v} {R : Type w} [Fintype J] [Fintype R]
    (v : J → (R → K)) :
    span K (range v) = ⊤ ↔ ∀ x : R → K,
      (∀ j, dotProduct (v j) x = 0) → x = 0 := by
  classical
  let Q : Matrix J R K := v
  have hsurj : Function.Surjective Q.vecMul ↔ Function.Injective Q.mulVec := by
    rw [Matrix.vecMul_surjective_iff_rank_eq_card, Matrix.mulVec_injective_iff,
      linearIndependent_iff_card_eq_finrank_span]
    change Q.rank = Fintype.card R ↔ Fintype.card R = Module.finrank K (span K (range Q.col))
    rw [← Q.rank_eq_finrank_span_cols]
    exact eq_comm
  rw [← show LinearMap.range Q.vecMulLinear = span K (range v) from
    range_vecMulLinear Q, LinearMap.range_eq_top, Matrix.coe_vecMulLinear, hsurj]
  change Function.Injective Q.mulVecLin ↔ _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  simp only [Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply, Matrix.mulVec]
  rfl

/-- A maximal independent subfamily spans the represented subset. -/
lemma represents_basis_span {K : Type u} [Field K]
    {J : Type v} {V : Type w} [AddCommGroup V] [Module K V]
    {M : _root_.Matroid J} {v : J → V} (hv : Represents K M v)
    {B S : Set J} (hB : M.IsBasis B S) :
    span K (v '' S) = span K (v '' B) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨e, he, rfl⟩
    by_contra hn
    have hins : M.Indep (insert e B) := (hv _).mpr
      ⟨insert_subset (hB.subset_ground he) ((hv B).mp hB.indep).1,
        ((hv B).mp hB.indep).2.insert hn⟩
    exact hn (subset_span ⟨e, hB.mem_of_insert_indep he hins, rfl⟩)
  · exact span_mono (image_mono hB.subset)

/-- In a representation whose full column span is the ambient space,
matroid spanning is precisely vector-space spanning. -/
lemma represents_spanning_iff {K : Type u} [Field K]
    {J : Type v} {V : Type w} [AddCommGroup V] [Module K V]
    {M : _root_.Matroid J} {v : J → V} (hv : Represents K M v)
    (hfull : span K (v '' M.E) = ⊤) (S : Set J) (hS : S ⊆ M.E) :
    M.Spanning S ↔ span K (v '' S) = ⊤ := by
  constructor
  · intro hs
    obtain ⟨B, hB, hBS⟩ := hs.exists_isBase_subset
    apply top_unique
    rw [← hfull, represents_basis_span hv (_root_.Matroid.isBasis_ground_iff.mpr hB)]
    exact span_mono (image_mono hBS)
  · intro hs
    obtain ⟨B, hB⟩ := M.exists_isBasis S hS
    have hspan : span K (v '' B) = ⊤ := (represents_basis_span hv hB).symm.trans hs
    have hb : M.IsBase B := hB.indep.isBase_of_forall_insert (by
      rintro e ⟨_, heB⟩ hi
      have hli := ((hv _).mp hi).2
      exact hli.notMem_span_of_insert heB (by rw [hspan]; trivial))
    exact (_root_.Matroid.spanning_iff_exists_isBase_subset hS).mpr ⟨B, hb, hB.subset⟩

section Blocks
variable {K : Type u} [Field K] {R : Type v} {C : Type w}
  [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

omit [DecidableEq R] in
lemma sum_standardDualColumns_eq_zero (A : Matrix R C K) (f : R ⊕ C → K) :
    (∑ e, f e • standardDualColumns A e) = 0 ↔
      ∀ j, f (Sum.inr j) = ∑ i, A i j * f (Sum.inl i) := by
  classical
  simp [funext_iff, Fintype.sum_sum_type, standardDualColumns, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_comm, neg_add_eq_iff_eq_add]

omit [Fintype C] [DecidableEq C] in
lemma dotProduct_standardColumns_inl (A : Matrix R C K) (x : R → K) (i : R) :
    dotProduct (standardColumns A (Sum.inl i)) x = x i := by
  simp [standardColumns, dotProduct, Pi.single_apply]

lemma standardDualColumns_indep_iff (A : Matrix R C K) (I : Set (R ⊕ C)) :
    LinearIndepOn K (standardDualColumns A) I ↔
      span K (standardColumns A '' Iᶜ) = ⊤ := by
  classical
  rw [linearIndepOn_iff_supported_sum, image_eq_range, span_eq_top_iff_dotProduct]
  constructor
  · intro hi x hx
    let f : R ⊕ C → K := fun e => dotProduct (standardColumns A e) x
    have hf : f = 0 := hi f (fun e he => hx ⟨e, he⟩) <|
      (sum_standardDualColumns_eq_zero A f).mpr (by
        intro j
        simp [f, standardColumns, dotProduct, Pi.single_apply])
    ext i
    simpa [f, dotProduct_standardColumns_inl] using congrFun hf (Sum.inl i)
  · intro hi f hf hs
    have hs' := (sum_standardDualColumns_eq_zero A f).mp hs
    let x : R → K := fun i => f (Sum.inl i)
    have hfx : ∀ e, f e = dotProduct (standardColumns A e) x := by
      intro e
      cases e with
      | inl i => simp [x, dotProduct_standardColumns_inl]
      | inr j => exact hs' j
    have hx : x = 0 := hi x (by
      intro e
      rw [← hfx]
      exact hf e e.property)
    ext e
    rw [hfx e, hx]
    simp

lemma standardColumns_span (A : Matrix R C K) :
    span K (standardColumns A '' univ) = ⊤ := by
  rw [image_univ, span_eq_top_iff_dotProduct]
  intro x hx
  ext i
  simpa [dotProduct_standardColumns_inl] using hx (Sum.inl i)

/-- The dual representation theorem holds without rank or positivity assumptions:
the identity block guarantees the full primal span. -/
theorem dualColumns : Expected.dualColumns := by
  intro K _ R C _ _ _ _ A M hE hv I
  have hI : I ⊆ M.E := by rw [hE]; exact subset_univ _
  have hfull : span K (standardColumns A '' M.E) = ⊤ := by
    rw [hE]; exact standardColumns_span A
  change M.Coindep I ↔ _
  rw [_root_.Matroid.coindep_iff_compl_spanning hI,
    represents_spanning_iff hv hfull _ sdiff_subset, hE, show univ \ I = Iᶜ by ext; simp,
    ← standardDualColumns_indep_iff A I]
  simp [hE]

theorem complementaryColumnBases : Expected.complementaryColumnBases := by
  intro K _ R C _ _ _ _ A B
  let M := vectorMatroid K univ (toFinite _) (standardColumns A)
  have hE : M.E = univ := rfl
  have hv : Represents K M (standardColumns A) := vectorRepresents K _ _ _
  have hd := dualColumns A M hE hv
  have heq : M✶ = vectorMatroid K univ (toFinite _) (standardDualColumns A) := by
    exact _root_.Matroid.ext_indep rfl (fun I _ => (hd I).trans
      (vectorIndep K univ (toFinite _) (standardDualColumns A) I).symm)
  change M.IsBase B ↔ (vectorMatroid K univ (toFinite _) (standardDualColumns A)).IsBase (univ \ B)
  rw [← heq]
  constructor
  · intro hb
    exact hb.compl_isBase_dual
  · intro hb
    have := hb.compl_isBase_of_dual
    simpa only [hE, sdiff_sdiff_cancel_left (subset_univ B)] using this

end Blocks
/-- Transport an indexed representation along a bijection of its index set. -/
lemma represents_mapEquiv {K : Type u} [Field K]
    {J : Type v} {L : Type*} {V : Type w} [AddCommGroup V] [Module K V]
    {M : _root_.Matroid J} {v : J → V} (hv : Represents K M v) (e : J ≃ L) :
    Represents K (M.mapEquiv e) (v ∘ e.symm) := by
  intro I
  rw [_root_.Matroid.mapEquiv_indep_iff, hv, _root_.Matroid.mapEquiv_ground_eq]
  constructor
  · rintro ⟨hI, hi⟩
    refine ⟨?_, hi.comp_of_image e.symm.injective.injOn⟩
    intro j hj
    exact ⟨e.symm j, hI ⟨j, hj, rfl⟩, e.apply_symm_apply j⟩
  · rintro ⟨hI, hi⟩
    refine ⟨?_, hi.image_of_comp e.symm v⟩
    rintro _ ⟨j, hj, rfl⟩
    rcases hI hj with ⟨k, hk, rfl⟩
    simpa using hk

theorem dualColumnsOrdered : Expected.dualColumnsOrdered := by
  intro K _ r n h A M hE hv
  let e := blockColumnOrder h
  let Mb := M.mapEquiv e.symm
  have hb : Represents K Mb (standardColumns A) := by
    have ht := represents_mapEquiv hv e.symm
    simpa [e, Mb, Function.comp_def] using ht
  have hEb : Mb.E = univ := by simp [Mb, hE]
  have hd := dualColumns A Mb hEb hb
  have ht := represents_mapEquiv hd e
  have hdmap : Mb✶ = M✶.mapEquiv e.symm :=
    _root_.Matroid.map_dual (hf := e.symm.injective.injOn)
  have heq : Mb✶.mapEquiv e = M✶ := by
    rw [hdmap]
    apply _root_.Matroid.ext_indep
    · simp [image_image]
    · intro I _
      simp [image_image]
  rw [heq] at ht
  exact ht

end FiniteCombinatorics.Matroid
