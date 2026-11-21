import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.BinarySpaces.Cycles
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.BinarySpaces.Cuts

set_option backward.isDefEq.respectTransparency false
universe u
noncomputable section
namespace FiniteCombinatorics.Graph.BinarySpaces
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Specs.FiniteCombinatorics.Graph.BinarySpaces.Foundations
open Specs.FiniteCombinatorics.Graph.BinarySpaces.Cuts

variable {V : Type u} [Finite V] (G : SimpleGraph V)

lemma binary_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h := a.isLt
  change a.val < 2 at h
  have hv : a.val = 0 ∨ a.val = 1 := by omega
  exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)

/-- A cut coordinate is the sum of the two endpoint indicators. -/
lemma cutVector_apply_mk (S : Set V) (a b : V) (h : G.Adj a b) :
    cutVectorValue G S ⟨s(a,b), h⟩ =
      (if a ∈ S then (1 : ZMod 2) else 0) + (if b ∈ S then 1 else 0) := by
  have ht : (1 : ZMod 2) + 1 = 0 := by decide
  change (if (⟨s(a,b), h⟩ : EdgeValue G) ∈ cutEdgesValue G S then 1 else 0) = _
  rw [cut_membership G S a b h]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb, ht]

lemma cutVector_apply (S : Set V) (e : EdgeValue G) :
    cutVectorValue G S e =
      (if e.val.out.1 ∈ S then (1 : ZMod 2) else 0) +
      (if e.val.out.2 ∈ S then 1 else 0) := by
  have h : G.Adj e.val.out.1 e.val.out.2 := by
    change s(e.val.out.1, e.val.out.2) ∈ G.edgeSet
    rw [Sym2.mk_fst_out_snd_out]
    exact e.property
  have he : (⟨s(e.val.out.1, e.val.out.2), h⟩ : EdgeValue G) = e :=
    Subtype.ext (Sym2.mk_fst_out_snd_out _)
  simpa only [he] using cutVector_apply_mk G S _ _ h

lemma cutVector_mk_eq_zero_iff (S : Set V) (a b : V) (h : G.Adj a b) :
    cutVectorValue G S ⟨s(a,b), h⟩ = 0 ↔ (a ∈ S ↔ b ∈ S) := by
  rw [cutVector_apply_mk]
  have ht : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb, ht]

lemma cutVector_symmDiff (S T : Set V) :
    cutVectorValue G (symmDiff S T) = cutVectorValue G S + cutVectorValue G T := by
  ext e
  simp only [Pi.add_apply, cutVector_apply, Set.mem_symmDiff]
  have ht : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases ha : e.val.out.1 ∈ S <;> by_cases hb : e.val.out.2 ∈ S <;>
    by_cases hc : e.val.out.1 ∈ T <;> by_cases hd : e.val.out.2 ∈ T <;>
    simp [ha, hb, hc, hd, ht]

lemma cutVector_empty : cutVectorValue G (∅ : Set V) = 0 := by
  ext e
  simp [cutVector_apply]

/-- The span of cuts consists of cuts, since the field has two elements. -/
theorem cutSpace_exists_cut : cutSpace_exists_cutType := by
  intro V _ G x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨S, rfl⟩ := hx; exact ⟨S, rfl⟩
  | zero => exact ⟨∅, (cutVector_empty G).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨S, rfl⟩ := hx
    obtain ⟨T, rfl⟩ := hy
    exact ⟨symmDiff S T, (cutVector_symmDiff G S T).symm⟩
  | smul a x _ hx =>
    rcases binary_eq_zero_or_one a with rfl | rfl
    · exact ⟨∅, by simp [cutVector_empty]⟩
    · simpa using hx

lemma cutVector_mem (S : Set V) : cutVectorValue G S ∈ cutSpaceValue G :=
  Submodule.subset_span ⟨S, rfl⟩

/-- Along an edge not deleted, membership in a component of the deletion
is unchanged. -/
lemma fundamentalCut_coordinates (F : SpanningForestValue G) (e f : ForestEdgeValue G F) :
    fundamentalCutValue G F e f.val = if e = f then 1 else 0 := by
  classical
  have hf : G.Adj f.val.val.out.1 f.val.val.out.2 := by
    change s(f.val.val.out.1, f.val.val.out.2) ∈ G.edgeSet
    rw [Sym2.mk_fst_out_snd_out]
    exact f.val.property
  have hid : (⟨s(f.val.val.out.1, f.val.val.out.2), hf⟩ : EdgeValue G) = f.val :=
    Subtype.ext (Sym2.mk_fst_out_snd_out _)
  by_cases he : e = f
  · subst f
    rw [ite_eq_left rfl]
    change cutVectorValue G (fundamentalCutSideValue G F e) e.val = 1
    rw [← hid, cutVector_apply_mk]
    have hs := fundamentalCut_separates G F e
    simp [hs.1, hs.2]
  · rw [ite_eq_right he]
    change cutVectorValue G (fundamentalCutSideValue G F e) f.val = 0
    rw [← hid, cutVector_mk_eq_zero_iff]
    have hne : f.val.val ≠ e.val.val := fun h => he (Subtype.ext (Subtype.ext h.symm))
    have hdel : (F.val.deleteEdges {e.val.val}).Adj f.val.val.out.1 f.val.val.out.2 := by
      rw [SimpleGraph.deleteEdges_adj, Sym2.mk_fst_out_snd_out]
      refine ⟨?_, by simpa using hne⟩
      change s(f.val.val.out.1, f.val.val.out.2) ∈ F.val.edgeSet
      rw [Sym2.mk_fst_out_snd_out]
      exact f.property
    exact ⟨fun h => h.trans hdel.reachable, fun h => h.trans hdel.symm.reachable⟩

theorem fundamentalCut_forest_support : fundamentalCut_forest_supportType := by
  intro V _ G F e f
  exact fundamentalCut_coordinates G F e f

/-- A cut with no forest coordinates is zero: its defining set is constant
along forest walks, hence along every component of G. -/
lemma cutSpace_forest_coordinates_zero (F : SpanningForestValue G) (x : EdgeVectorValue G)
    (hx : x ∈ cutSpaceValue G) (hs : ∀ e : ForestEdgeValue G F, x e.val = 0) : x = 0 := by
  obtain ⟨S, rfl⟩ := cutSpace_exists_cut G x hx
  have hadj (a b : V) (h : F.val.Adj a b) : a ∈ S ↔ b ∈ S := by
    have hG := F.property.1 h
    exact (cutVector_mk_eq_zero_iff G S a b hG).mp (hs ⟨⟨s(a,b), hG⟩, h⟩)
  have hwalk {a b : V} (p : F.val.Walk a b) : a ∈ S ↔ b ∈ S := by
    induction p with
    | nil => rfl
    | cons h p ih => exact (hadj _ _ h).trans ih
  ext e
  change cutVectorValue G S e = 0
  have hG : G.Adj e.val.out.1 e.val.out.2 := by
    change s(e.val.out.1, e.val.out.2) ∈ G.edgeSet
    rw [Sym2.mk_fst_out_snd_out]
    exact e.property
  have hr : F.val.Reachable e.val.out.1 e.val.out.2 := by
    rw [F.property.2.2]
    exact hG.reachable
  have hc := (cutVector_mk_eq_zero_iff G S _ _ hG).mpr (hr.elim hwalk)
  simpa only [Sym2.mk_fst_out_snd_out] using hc

lemma fundamentalCut_mem (F : SpanningForestValue G) (e : ForestEdgeValue G F) :
    fundamentalCutValue G F e ∈ cutSpaceValue G :=
  cutVector_mem G _

lemma fundamentalCuts_linearIndependent (F : SpanningForestValue G) :
    LinearIndependent (ZMod 2) (fundamentalCutValue G F) := by
  classical
  rw [linearIndependent_iff']
  intro s a h e he
  have hx := congrFun h e.val
  simpa [Finset.sum_apply, Pi.smul_apply, fundamentalCut_coordinates,
    Finset.sum_ite_eq', he] using hx

/-- Eliminate the forest coordinates with the specified fundamental cuts. -/
lemma span_fundamentalCuts_eq (F : SpanningForestValue G) :
    Submodule.span (ZMod 2) (Set.range (fundamentalCutValue G F)) = cutSpaceValue G := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact fundamentalCut_mem G F e
  · intro x hx
    let : Fintype (ForestEdgeValue G F) := Fintype.ofFinite _
    let y := ∑ e : ForestEdgeValue G F, x e.val • fundamentalCutValue G F e
    have hy : y ∈ Submodule.span (ZMod 2) (Set.range (fundamentalCutValue G F)) := by
      apply Submodule.sum_mem
      intro e _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
    have hyc : y ∈ cutSpaceValue G := by
      apply Submodule.sum_mem
      intro e _
      exact Submodule.smul_mem _ _ (fundamentalCut_mem G F e)
    have hxy : x - y = 0 := cutSpace_forest_coordinates_zero G F (x - y)
      ((cutSpaceValue G).sub_mem hx hyc) (by
        intro e
        simp [y, Finset.sum_apply, Pi.smul_apply, fundamentalCut_coordinates])
    rwa [sub_eq_zero.mp hxy]

theorem fundamentalCuts_basis : fundamentalCuts_basisType := by
  intro V _ G F
  let v : ForestEdgeValue G F → cutSpaceValue G :=
    fun e => ⟨fundamentalCutValue G F e, fundamentalCut_mem G F e⟩
  have hli : LinearIndependent (ZMod 2) v :=
    LinearIndependent.of_comp (cutSpaceValue G).subtype (fundamentalCuts_linearIndependent G F)
  have hsp : ⊤ ≤ Submodule.span (ZMod 2) (Set.range v) := by
    exact ((Submodule.span_range_subtype_eq_top_iff (cutSpaceValue G)
      (fundamentalCut_mem G F)).mpr (span_fundamentalCuts_eq G F)).ge
  exact ⟨Module.Basis.mk hli hsp, fun e => by rw [Module.Basis.mk_apply]⟩

theorem cutSpace_dimension : cutSpace_dimensionType := by
  intro V _ G
  obtain ⟨F⟩ := exists_spanningForest G
  obtain ⟨b, _⟩ := fundamentalCuts_basis G F
  have hd := Module.finrank_eq_nat_card_basis b
  have hc : Nat.card F.val.ConnectedComponent = Nat.card G.ConnectedComponent := by
    change Nat.card (Quot F.val.Reachable) = Nat.card (Quot G.Reachable)
    rw [F.property.2.2]
  have hcn : Nat.card G.ConnectedComponent ≤ Nat.card V :=
    Nat.card_le_card_of_surjective G.connectedComponentMk (fun c => Quot.exists_rep c)
  have hf := Trees.forest_edge_count F.val F.property.2.1
  change Nat.card F.val.edgeSet = Nat.card V - Nat.card F.val.ConnectedComponent at hf
  rw [hc] at hf
  rw [forestEdge_card G F] at hd
  omega

/-- Summing over the incident vertices of a genuine unordered edge sums over
exactly its two distinct endpoints. -/
lemma sum_incident_endpoints (e : EdgeValue G) (f : V → ZMod 2) :
    letI := Fintype.ofFinite V
    (∑ v, if v ∈ e.val then f v else 0) = f e.val.out.1 + f e.val.out.2 := by
  classical
  let := Fintype.ofFinite V
  have hG : G.Adj e.val.out.1 e.val.out.2 := by
    change s(e.val.out.1, e.val.out.2) ∈ G.edgeSet
    rw [Sym2.mk_fst_out_snd_out]
    exact e.property
  have hm (v : V) : v ∈ e.val ↔ v = e.val.out.1 ∨ v = e.val.out.2 := by
    calc
      v ∈ e.val ↔ v ∈ s(e.val.out.1, e.val.out.2) := by rw [Sym2.mk_fst_out_snd_out]
      _ ↔ _ := Sym2.mem_iff
  have hs (v : V) :
      (if v ∈ e.val then f v else 0) =
        (if v = e.val.out.1 then f v else 0) + (if v = e.val.out.2 then f v else 0) := by
    simp only [hm]
    by_cases ha : v = e.val.out.1 <;> by_cases hb : v = e.val.out.2 <;>
      simp_all [hG.ne]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  simp

lemma cutVector_eq_incident_sum (S : Set V) (e : EdgeValue G) :
    letI := Fintype.ofFinite V
    cutVectorValue G S e = ∑ v, if v ∈ e.val then (if v ∈ S then (1 : ZMod 2) else 0) else 0 := by
  rw [sum_incident_endpoints, cutVector_apply]

/-- Incidence summation is adjoint to taking a cut, in the actual edge dot
product. No orientation or connectedness assumption is needed. -/
lemma dotProduct_cut_eq (x : EdgeVectorValue G) (S : Set V) :
    letI := Fintype.ofFinite V
    dotProductValue G x (cutVectorValue G S) =
      ∑ v, if v ∈ S then incidenceBoundary G x v else 0 := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite (EdgeValue G)
  change (∑ e, x e * cutVectorValue G S e) = _
  simp_rw [cutVector_eq_incident_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ S
  · simp only [hv, ite_true]
    change (∑ e, x e * (if v ∈ e.val then (1 : ZMod 2) else 0)) =
      ∑ e, if v ∈ e.val then x e else 0
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : v ∈ e.val <;> simp [he]
  · simp [hv]

theorem cycle_cut_orthogonal : cycle_cut_orthogonalType := by
  intro V _ G x y hx hy
  obtain ⟨S, rfl⟩ := cutSpace_exists_cut G y hy
  have hk : incidenceBoundary G x = 0 := cycleSpace_le_ker_incidenceBoundary G hx
  rw [dotProduct_cut_eq, hk]
  simp

/-- The dot product of indicators counts their common edges modulo two. -/
lemma dotProduct_indicators (H T : Set (EdgeValue G)) :
    dotProductValue G (edgeIndicatorValue G H) (edgeIndicatorValue G T) =
      (Nat.card {e : EdgeValue G // e ∈ H ∧ e ∈ T} : ZMod 2) := by
  classical
  let := Fintype.ofFinite (EdgeValue G)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_boole]
  change (∑ e, (if e ∈ H then (1 : ZMod 2) else 0) * (if e ∈ T then 1 else 0)) = _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hh : e ∈ H <;> by_cases ht : e ∈ T <;> simp [hh, ht]

theorem evenDegree_cut_intersection : evenDegree_cut_intersectionType := by
  intro V _ G H S hH
  have hd := cycle_cut_orthogonal G (edgeIndicatorValue G H) (cutVectorValue G S)
    ((cycleSpace_iff_evenDegree G H).mpr hH) (cutVector_mem G S)
  change dotProductValue G (edgeIndicatorValue G H)
    (edgeIndicatorValue G (cutEdgesValue G S)) = 0 at hd
  rw [dotProduct_indicators] at hd
  exact ZMod.natCast_eq_zero_iff_even.mp hd

end FiniteCombinatorics.Graph.BinarySpaces
