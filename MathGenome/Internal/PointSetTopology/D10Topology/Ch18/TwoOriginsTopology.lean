import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.TwoOriginsTopology
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

/-! The actual doubled-origin quotient, paper.tex d10:18:two-origins.
The two charts are indexed by false (left copy) and true (right copy).
All topology instances come from the disjoint-sum quotient, not a transported
Hausdorff topology. -/

open Set Topology TopologicalSpace
open scoped Topology

namespace D10Topology.Ch18.TwoOrigins

abbrev Line := TwoOriginsData.Line
def classMap : ℝ ⊕ ℝ → Line := TwoOriginsData.classMap
def chart : Bool → ℝ → Line := TwoOriginsData.chart
def origin : Bool → Line := TwoOriginsData.origin
def coordinate : Line → ℝ := TwoOriginsData.coordinate

theorem class_eq (a b : ℝ ⊕ ℝ) :
    classMap a = classMap b ↔ TwoOriginsData.rawCoordinate a = TwoOriginsData.rawCoordinate b ∧
      (TwoOriginsData.rawCoordinate a ≠ 0 ∨ a = b) := Quotient.eq

theorem quotient_topology (U : Set Line) :
    IsOpen U ↔ IsOpen (classMap ⁻¹' U) := Iff.rfl

theorem quotient_map : IsQuotientMap classMap := isQuotientMap_quotient_mk'

@[simp] theorem coordinate_classMap (a : ℝ ⊕ ℝ) :
    coordinate (classMap a) = TwoOriginsData.rawCoordinate a := rfl

@[simp] theorem coordinate_chart (i : Bool) (x : ℝ) : coordinate (chart i x) = x := by
  cases i <;> rfl

theorem chart_eq (i j : Bool) (x y : ℝ) :
    chart i x = chart j y ↔ x = y ∧ (x ≠ 0 ∨ i = j) := by
  change classMap (TwoOriginsData.sheet i x) = classMap (TwoOriginsData.sheet j y) ↔ _
  rw [class_eq]
  cases i <;> cases j <;> simp [TwoOriginsData.sheet, TwoOriginsData.rawCoordinate] <;>
    exact fun h => Or.inr h

theorem coordinate_continuous : Continuous coordinate := by
  have h : Continuous TwoOriginsData.rawCoordinate := continuous_id.sumElim continuous_id
  exact h.quotient_lift (fun _ _ (h : TwoOriginsData.relation _ _) => h.1)

theorem coordinate_open : IsOpenMap coordinate :=
  IsOpenMap.of_comp quotient_map.continuous quotient_map.surjective
    (IsOpenMap.id.sumElim IsOpenMap.id)

theorem chart_continuous (i : Bool) : Continuous (chart i) := by
  cases i
  · exact quotient_map.continuous.comp continuous_inl
  · exact quotient_map.continuous.comp continuous_inr

theorem exists_chart (q : Line) : ∃ (i : Bool) (x : ℝ), chart i x = q := by
  induction q using Quotient.inductionOn with
  | h a =>
    cases a with
    | inl x => exact ⟨false, x, rfl⟩
    | inr x => exact ⟨true, x, rfl⟩

theorem origins_distinct : origin false ≠ origin true := by
  change chart false 0 ≠ chart true 0
  simp [chart_eq]

theorem chart_range (i : Bool) : range (chart i) = {origin (!i)}ᶜ := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change chart i x ≠ chart (!i) 0
    simp [chart_eq]
  · intro hq
    obtain ⟨j, x, rfl⟩ := exists_chart q
    by_cases h : i = j
    · exact ⟨x, by rw [h]⟩
    · have hx : x ≠ 0 := by
        intro hx
        subst x
        cases i <;> cases j <;> simp_all [origin, TwoOriginsData.origin, chart]
      exact ⟨x, (chart_eq i j x x).mpr ⟨rfl, Or.inl hx⟩⟩

theorem charts_cover : range (chart false) ∪ range (chart true) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨i, x, rfl⟩ := exists_chart q
  cases i
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨x, rfl⟩

theorem t1 : T1Space Line := by
  constructor
  intro q
  apply quotient_map.isCoinducing.isClosed_preimage.mp
  apply Set.Finite.isClosed
  apply (Set.toFinite ({Sum.inl (coordinate q), Sum.inr (coordinate q)} : Set (ℝ ⊕ ℝ))).subset
  intro a ha
  change classMap a = q at ha
  have hc := congrArg coordinate ha
  cases a with
  | inl x =>
    change x = coordinate q at hc
    simp [hc]
  | inr x =>
    change x = coordinate q at hc
    simp [hc]

theorem chart_open_embedding (i : Bool) : IsOpenEmbedding (chart i) := by
  have := t1
  refine ⟨Function.LeftInverse.isEmbedding (coordinate_chart i)
    coordinate_continuous (chart_continuous i), ?_⟩
  rw [chart_range]
  exact isClosed_singleton.isOpen_compl

theorem chart_homeomorph (i : Bool) :
    ∃ h : ℝ ≃ₜ ({origin (!i)}ᶜ : Set Line), ∀ x : ℝ, (h x).val = chart i x := by
  let h := (chart_open_embedding i).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (chart_range i))
  exact ⟨h, fun _ => rfl⟩

theorem locally_metrizable (q : Line) :
    ∃ U : Set Line, IsOpen U ∧ q ∈ U ∧ MetrizableSpace U := by
  obtain ⟨i, x, rfl⟩ := exists_chart q
  exact ⟨range (chart i), (chart_open_embedding i).isOpen_range, ⟨x, rfl⟩,
    (chart_open_embedding i).isEmbedding.toHomeomorph.symm.isEmbedding.metrizableSpace⟩

theorem second_countable : SecondCountableTopology Line := by
  let : ∀ i : Bool, SecondCountableTopology (range (chart i)) := fun i =>
    (chart_open_embedding i).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply secondCountableTopology_of_countable_cover
    (fun i : Bool => (chart_open_embedding i).isOpen_range)
  apply eq_univ_of_forall
  intro q
  obtain ⟨i, x, rfl⟩ := exists_chart q
  exact mem_iUnion.mpr ⟨i, ⟨x, rfl⟩⟩

theorem origin_neighborhoods_intersect (U V : Set Line)
    (hU : U ∈ nhds (origin false)) (hV : V ∈ nhds (origin true)) :
    ∃ x : ℝ, x ≠ 0 ∧ chart false x ∈ U ∩ V := by
  have hU' : chart false ⁻¹' U ∈ nhds (0 : ℝ) :=
    (chart_continuous false).continuousAt hU
  have hV' : chart true ⁻¹' V ∈ nhds (0 : ℝ) :=
    (chart_continuous true).continuousAt hV
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU' hV')
  have hx : ε / 2 ≠ 0 := ne_of_gt (by linarith)
  have hb : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < ε / 2)]
    linarith
  obtain ⟨hu, hv⟩ := hsub hb
  refine ⟨ε / 2, hx, hu, ?_⟩
  have he := (chart_eq false true (ε / 2) (ε / 2)).mpr ⟨rfl, Or.inl hx⟩
  exact he.symm ▸ hv

theorem not_hausdorff : ¬ T2Space Line := by
  intro h
  let := h
  obtain ⟨U, V, hU, hV, hu, hv, hd⟩ := t2_separation origins_distinct
  obtain ⟨x, _, hx⟩ := origin_neighborhoods_intersect U V (hU.mem_nhds hu) (hV.mem_nhds hv)
  exact Set.disjoint_left.mp hd hx.1 hx.2

theorem not_metrizable : ¬ MetrizableSpace Line := by
  intro h
  let := h
  exact not_hausdorff inferInstance

end D10Topology.Ch18.TwoOrigins
