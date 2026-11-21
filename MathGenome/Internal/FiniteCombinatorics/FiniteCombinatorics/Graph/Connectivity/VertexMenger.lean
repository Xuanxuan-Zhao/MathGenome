import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Connectivity.VertexMenger
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Connectivity.VertexSplit
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.Integrality
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.UnitArcPacking
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.Finset.Max

open scoped Classical
universe u
noncomputable section
namespace FiniteCombinatorics.Graph.VertexMenger
open VertexMengerSpec
variable {V : Type u} {G : SimpleGraph V} {s t : V}

@[simp] theorem mem_interior (p : G.Path s t) (v : V) :
    v ∈ interior p ↔ v ∈ p.val.support ∧ v ≠ s ∧ v ≠ t := by
  classical
  simp [interior]

/-- Mapping a walk of the induced graph back to G never visits a deleted vertex. -/
theorem avoiding_walk_support (S : Finset V) (hs : s ∉ S) (ht : t ∉ S)
    (q : (G.induce {v | v ∉ S}).Walk ⟨s, hs⟩ ⟨t, ht⟩) :
    ∀ v ∈ (q.map (SimpleGraph.Embedding.induce _).toHom).support, v ∉ S := by
  intro v hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨w, _, hw⟩ := List.mem_map.mp hv
  exact hw ▸ w.property

/-- Path-hitting is exactly separation in the graph on the surviving vertices. -/
theorem separator_iff_deletion : VertexMengerSpec.separator_iff_deletion.{u} := by
  intro V G s t S hs ht
  constructor
  · rintro ⟨_, _, hhit⟩ ⟨q⟩
    let w := q.map (SimpleGraph.Embedding.induce _).toHom
    obtain ⟨v, hvS, hvp⟩ := hhit ⟨w.bypass, w.bypass_isPath⟩
    exact avoiding_walk_support S hs ht q v
      (w.support_bypass_sublist_support.subset hvp) hvS
  · intro h
    refine ⟨hs, ht, fun p => ?_⟩
    by_contra hn
    have hav : ∀ v ∈ p.val.support, v ∈ {v | v ∉ S} := by
      intro v hv hvS
      exact hn ⟨v, hvS, hv⟩
    exact h ⟨p.val.induce {v | v ∉ S} hav⟩

/-- A separator provides a different internal vertex for each packed path. -/
theorem packing_le_separator : VertexMengerSpec.packing_le_separator.{u} := by
  intro V G s t P S hP hS
  classical
  have hit (p : G.Path s t) : ∃ v, v ∈ S ∧ v ∈ interior p := by
    obtain ⟨v, hvS, hvp⟩ := hS.2.2 p
    exact ⟨v, hvS, (mem_interior p v).mpr ⟨hvp,
      fun h => hS.1 (h ▸ hvS), fun h => hS.2.1 (h ▸ hvS)⟩⟩
  choose f hfS hfp using hit
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    exact hfS p
  · intro p hp q hq heq
    by_contra hne
    have hd := hP hp hq hne
    exact Finset.disjoint_left.mp hd (hfp p) (heq ▸ hfp q)

/-- Every path of a nonadjacent pair contains an internal vertex.
This is where the nonadjacency assumption is essential. -/
theorem interior_nonempty (hst : s ≠ t) (hnadj : ¬G.Adj s t)
    (p : G.Path s t) : (interior p).Nonempty := by
  classical
  obtain ⟨p, hp⟩ := p
  cases p with
  | nil => exact (hst rfl).elim
  | @cons _ v _ hsv q =>
    have hvs : v ≠ s := hsv.ne.symm
    have hvt : v ≠ t := by
      intro h
      exact hnadj (h ▸ hsv)
    exact ⟨v, (mem_interior ⟨.cons hsv q, hp⟩ v).mpr
      ⟨by simp, hvs, hvt⟩⟩

/-- Deleting every internal vertex is a valid separator. -/
theorem all_internal_separator [Fintype V] (hst : s ≠ t) (hnadj : ¬G.Adj s t) :
    IsSeparator G s t (Finset.univ.filter (fun v => v ≠ s ∧ v ≠ t)) := by
  classical
  refine ⟨by simp, by simp, fun p => ?_⟩
  obtain ⟨v, hv⟩ := interior_nonempty hst hnadj p
  obtain ⟨hvp, hvs, hvt⟩ := (mem_interior p v).mp hv
  exact ⟨v, by simp [hvs, hvt], hvp⟩

/-- There are exactly n-2 available internal vertices. -/
theorem all_internal_card [Fintype V] (hst : s ≠ t) :
    (Finset.univ.filter (fun v : V => v ≠ s ∧ v ≠ t)).card = Fintype.card V - 2 := by
  have heq : Finset.univ.filter (fun v : V => v ≠ s ∧ v ≠ t) =
      (Finset.univ.erase s).erase t := by
    ext v
    simp [and_comm]
  rw [heq, Finset.card_erase_of_mem (by simp [hst.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, Nat.sub_sub]

/-- Nonadjacency gives the sharp universal n-2 bound needed for finite transit capacities. -/
theorem internal_bound : VertexMengerSpec.internal_bound.{u} := by
  intro V _ G s t hst hnadj
  let : Fintype V := Fintype.ofFinite V
  let S := Finset.univ.filter (fun v : V => v ≠ s ∧ v ≠ t)
  have hS : IsSeparator G s t S := all_internal_separator hst hnadj
  have hc : S.card = Nat.card V - 2 := by
    rw [Nat.card_eq_fintype_card]
    exact all_internal_card hst
  exact ⟨⟨S, hS, hc⟩, fun P hP => hc ▸ packing_le_separator G s t P S hP hS⟩

/-- Both optimization problems have attained extrema before proving equality. -/
theorem extrema_attained : VertexMengerSpec.extrema_attained.{u} := by
  intro V _ G s t hst hnadj
  classical
  let : Fintype V := Fintype.ofFinite V
  let packings : Finset (Finset (G.Path s t)) := Finset.univ.filter IsPacking
  have hpack : packings.Nonempty := ⟨∅, by simp [packings, IsPacking]⟩
  obtain ⟨P, hP, hmax⟩ := packings.exists_max_image Finset.card hpack
  let separators : Finset (Finset V) := Finset.univ.filter (IsSeparator G s t)
  have hsep : separators.Nonempty :=
    ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, all_internal_separator hst hnadj⟩⟩
  obtain ⟨S, hS, hmin⟩ := separators.exists_min_image Finset.card hsep
  refine ⟨⟨P, (Finset.mem_filter.mp hP).2, fun Q hQ => ?_⟩,
    ⟨S, (Finset.mem_filter.mp hS).2, fun T hT => ?_⟩⟩
  · exact hmax Q (by simp [packings, hQ])
  · exact hmin T (by simp [separators, hT])

/-- Equality witnesses and weak duality certify both optimizers. -/
theorem equal_card_suffices : VertexMengerSpec.equal_card_suffices.{u} := by
  intro V G s t P S hP hS heq
  exact ⟨P, S, hP, hS, heq,
    fun Q hQ => (packing_le_separator G s t Q S hQ hS).trans_eq heq.symm,
    fun T hT => heq ▸ packing_le_separator G s t P T hP hT⟩

/-- An already disconnected pair has the empty optimum and empty separator. -/
theorem disconnected_zero : VertexMengerSpec.disconnected_zero.{u} := by
  intro V _ G s t hn
  have no_path (p : G.Path s t) : False := hn p.val.reachable
  have hS : IsSeparator G s t ∅ := ⟨by simp, by simp, fun p => (no_path p).elim⟩
  refine ⟨equal_card_suffices G s t ∅ ∅ ?_ hS rfl, ?_, hS⟩
  · simp [IsPacking]
  · intro P _
    have : P = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun p _ => no_path p)
    simp [this]

/-- Projecting a unit split-arc packing preserves cardinality: two distinct
members cannot have the same projection, since every projected path has an
internal vertex, whose split arc would then be shared. -/
theorem equal_witnesses [Finite V] (hst : s ≠ t) (hnadj : ¬G.Adj s t) :
    EqualWitnesses G s t := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let N := VertexSplitSpec.network G s t
  let B := VertexSplitSpec.splitArcs G s t
  obtain ⟨project, _, _, _, _, hmem, hcover⟩ :=
    VertexSplit.path_transport G s t hst hnadj
  obtain ⟨f, U, hf, hU, hmax, hmin, heq⟩ :=
    Flows.Network.integral_max_flow_min_cut N
      (fun a => ⟨VertexSplitSpec.capacityNat G s t a, rfl⟩)
  obtain ⟨hinit, _, hcinit⟩ := VertexSplit.initial_cut G s t hst hnadj
  have hbound : Flows.Spec.cutCapacity N U ≤ ((Fintype.card V - 2 : ℕ) : ℝ) :=
    (hmin _ hinit).trans_eq hcinit
  obtain ⟨_, hs, ht, hcsep, hhit, _⟩ :=
    VertexSplit.small_cut G s t hst hnadj U hU hbound
  have hnonneg : 0 ≤ Flows.Spec.value N (fun a => (f a : ℝ)) := by
    have hz := hmax (fun _ => 0) (Flows.Network.zero_feasible N)
    have hz0 : Flows.Spec.value N (fun _ => 0) = 0 := Flows.Network.value_zero N
    exact hz0 ▸ hz
  have hunit : ∀ a ∈ B, N.capacity a = 1 := by
    intro a ha
    obtain ⟨v, rfl⟩ := (VertexSplit.mem_splitArcs a).mp ha
    simp [N, VertexSplitSpec.network, VertexSplitSpec.capacityNat]
  obtain ⟨D, hcard, hdisj, _⟩ := Flows.unit_arc_packing N B hunit hcover
    (fun a => (f a : ℝ)) hf (fun a => ⟨(f a : ℤ), by simp⟩) hnonneg
  have hinj : Set.InjOn project {p | p ∈ D} := by
    intro p hp q hq he
    by_contra hne
    obtain ⟨v, hv⟩ := interior_nonempty hst hnadj (project p)
    obtain ⟨hvp, hvs, hvt⟩ := (mem_interior _ _).mp hv
    let w : VertexSplitSpec.Internal s t := ⟨v, hvs, hvt⟩
    have ha : Sum.inl w ∈ B := (VertexSplit.mem_splitArcs _).mpr ⟨w, rfl⟩
    apply hdisj p hp q hq hne (Sum.inl w) ha
    exact ⟨(hmem p w).mp hvp, (hmem q w).mp (he ▸ hvp)⟩
  let P := D.image project
  have hP : IsPacking P := by
    intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    have hne : p' ≠ q' := fun h => hpq (congrArg project h)
    apply Finset.disjoint_left.mpr
    intro v hvp hvq
    obtain ⟨hvp, hvs, hvt⟩ := (mem_interior _ _).mp hvp
    have hvq := ((mem_interior _ _).mp hvq).1
    let w : VertexSplitSpec.Internal s t := ⟨v, hvs, hvt⟩
    exact hdisj p' hp' q' hq' hne (Sum.inl w)
      ((VertexSplit.mem_splitArcs _).mpr ⟨w, rfl⟩)
      ⟨(hmem p' w).mp hvp, (hmem q' w).mp hvq⟩
  have hPc : P.card = D.card := Finset.card_image_of_injOn hinj
  have hcards : P.card = (VertexSplitSpec.separator G s t U).card := by
    have hr : (P.card : ℝ) = ((VertexSplitSpec.separator G s t U).card : ℝ) := by
      rw [hPc, hcard, heq, hcsep]
    exact_mod_cast hr
  exact equal_card_suffices G s t P (VertexSplitSpec.separator G s t U)
    hP ⟨hs, ht, hhit⟩ hcards

/-- W48, vertex version: maximum internally vertex-disjoint path count equals
minimum endpoint-excluding vertex separator size, with both extrema attained. -/
theorem vertex_menger : VertexMengerSpec.vertex_menger.{u} := by
  intro V _ G s t hst hnadj
  exact ⟨equal_witnesses hst hnadj, fun hn => (disconnected_zero G s t hn).2⟩

end FiniteCombinatorics.Graph.VertexMenger
