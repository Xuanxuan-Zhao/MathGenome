import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.WeakMetrics
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.StrassenDudley
import Mathlib.Tactic.Linarith
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.FiniteTransportation

/-!
# Strassen--Dudley coupling

The coupling convention and Theorem `thm:p06-strassen` in paper.tex, §6.10.
The forward construction truncates a countable measurable partition, applies
finite transportation, and lifts the matrix with normalized restrictions.
No completeness or tightness assumption is used. Null rows and columns are
handled before normalization is used in the event estimate.
-/

open MeasureTheory TopologicalSpace
open scoped Classical

namespace ProbabilityFoundations.Ch06

universe u v w
noncomputable section

/-- A coupling is a probability on the product with the given marginals. -/
def IsCoupling {S : Type u} [MeasurableSpace S]
    (μ ν : ProbabilityMeasure S) (γ : ProbabilityMeasure (S × S)) : Prop :=
  Measure.map Prod.fst (γ : Measure (S × S)) = (μ : Measure S) ∧
  Measure.map Prod.snd (γ : Measure (S × S)) = (ν : Measure S)

/-- Separability suffices for equality of the product and Borel sigma algebras. -/
theorem coupling_product_borel {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SeparableSpace S] :
    (inferInstance : MeasurableSpace (S × S)) = borel (S × S) :=
  BorelSpace.measurable_eq

theorem coupling_distance_event_measurable {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SeparableSpace S] (a : ℝ) :
    MeasurableSet {z : S × S | a < dist z.1 z.2} :=
  isOpen_lt continuous_const (continuous_fst.dist continuous_snd) |>.measurableSet

/-- Couplings always exist, without any metric or completeness assumption. -/
theorem exists_product_coupling {S : Type u} [MeasurableSpace S]
    (μ ν : ProbabilityMeasure S) :
    ∃ γ : ProbabilityMeasure (S × S), IsCoupling μ ν γ := by
  refine ⟨⟨(μ : Measure S).prod (ν : Measure S), inferInstance⟩, ?_, ?_⟩ <;>
    simp

/-- A marginal set is contained in its enlargement under the other coordinate,
except on the event where the coordinates are farther apart than `a`. -/
theorem coupling_left_set_bound {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SeparableSpace S]
    (μ ν : ProbabilityMeasure S) (γ : ProbabilityMeasure (S × S))
    (hγ : IsCoupling μ ν γ) {a b : ℝ} (hab : a < b)
    (A : Set S) (hA : MeasurableSet A) :
    (μ : Measure S).real A ≤ (ν : Measure S).real (enlargement b A) +
      (γ : Measure (S × S)).real {z | a < dist z.1 z.2} := by
  have hsubset : Prod.fst ⁻¹' A ⊆
      Prod.snd ⁻¹' enlargement b A ∪ {z : S × S | a < dist z.1 z.2} := by
    intro z hz
    by_cases hd : a < dist z.1 z.2
    · exact Or.inr hd
    · exact Or.inl ⟨z.1, hz, by
        rw [dist_comm]
        exact lt_of_le_of_lt (le_of_not_gt hd) hab⟩
  have hm := measureReal_mono (μ := (γ : Measure (S × S))) hsubset
  have hu := measureReal_union_le (μ := (γ : Measure (S × S)))
    (Prod.snd ⁻¹' enlargement b A) {z : S × S | a < dist z.1 z.2}
  have hfst : (γ : Measure (S × S)).real (Prod.fst ⁻¹' A) =
      (μ : Measure S).real A := by
    rw [← map_measureReal_apply measurable_fst hA, hγ.1]
  have hsnd : (γ : Measure (S × S)).real (Prod.snd ⁻¹' enlargement b A) =
      (ν : Measure S).real (enlargement b A) := by
    rw [← map_measureReal_apply measurable_snd (enlargement_isOpen b A).measurableSet,
      hγ.2]
  rw [hfst] at hm
  rw [hsnd] at hu
  exact hm.trans hu

theorem coupling_right_set_bound {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SeparableSpace S]
    (μ ν : ProbabilityMeasure S) (γ : ProbabilityMeasure (S × S))
    (hγ : IsCoupling μ ν γ) {a b : ℝ} (hab : a < b)
    (A : Set S) (hA : MeasurableSet A) :
    (ν : Measure S).real A ≤ (μ : Measure S).real (enlargement b A) +
      (γ : Measure (S × S)).real {z | a < dist z.1 z.2} := by
  have hsubset : Prod.snd ⁻¹' A ⊆
      Prod.fst ⁻¹' enlargement b A ∪ {z : S × S | a < dist z.1 z.2} := by
    intro z hz
    by_cases hd : a < dist z.1 z.2
    · exact Or.inr hd
    · exact Or.inl ⟨z.2, hz, lt_of_le_of_lt (le_of_not_gt hd) hab⟩
  have hm := measureReal_mono (μ := (γ : Measure (S × S))) hsubset
  have hu := measureReal_union_le (μ := (γ : Measure (S × S)))
    (Prod.fst ⁻¹' enlargement b A) {z : S × S | a < dist z.1 z.2}
  have hsnd : (γ : Measure (S × S)).real (Prod.snd ⁻¹' A) =
      (ν : Measure S).real A := by
    rw [← map_measureReal_apply measurable_snd hA, hγ.2]
  have hfst : (γ : Measure (S × S)).real (Prod.fst ⁻¹' enlargement b A) =
      (μ : Measure S).real (enlargement b A) := by
    rw [← map_measureReal_apply measurable_fst (enlargement_isOpen b A).measurableSet,
      hγ.1]
  rw [hsnd] at hm
  rw [hfst] at hu
  exact hm.trans hu

/-- The non-strict converse in the Strassen--Dudley theorem. The enlargement
radius must first be strictly greater than the distance threshold. -/
theorem prokhorovDist_le_of_coupling {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SeparableSpace S]
    (μ ν : ProbabilityMeasure S) (a : ℝ) (ha : 0 < a)
    (γ : ProbabilityMeasure (S × S)) (hγ : IsCoupling μ ν γ)
    (hdef : (γ : Measure (S × S)).real {z | a < dist z.1 z.2} ≤ a) :
    prokhorovDist μ ν ≤ a := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hab
  apply prokhorovDist_le_of_admissible
  refine ⟨ha.trans hab, fun A hA => ⟨?_, ?_⟩⟩
  · exact (coupling_left_set_bound μ ν γ hγ hab A hA).trans
      (add_le_add le_rfl (hdef.trans hab.le))
  · exact (coupling_right_set_bound μ ν γ hγ hab A hA).trans
      (add_le_add le_rfl (hdef.trans hab.le))

/-- Normalize a nonnull restriction. On null cells use the original probability;
the corresponding transport row will have weight zero. -/
def cellProbability {S : Type u} [MeasurableSpace S]
    (μ : ProbabilityMeasure S) (B : Set S) : ProbabilityMeasure S :=
  if h : (μ : Measure S) B = 0 then μ else
    ⟨ProbabilityTheory.cond (μ : Measure S) B,
      ProbabilityTheory.cond_isProbabilityMeasure h⟩

/-- The mass-weighted normalization recovers the restriction, including null cells. -/
theorem mass_smul_cellProbability {S : Type u} [MeasurableSpace S]
    (μ : ProbabilityMeasure S) (B : Set S) :
    (μ : Measure S) B • (cellProbability μ B : Measure S) =
      (μ : Measure S).restrict B := by
  classical
  by_cases h : (μ : Measure S) B = 0
  · simp [cellProbability, h, Measure.restrict_eq_zero.mpr h]
  · unfold cellProbability
    erw [dite_eq_right h]
    change (μ : Measure S) B • ((μ : Measure S) B)⁻¹ • (μ : Measure S).restrict B = _
    rw [smul_smul]
    rw [ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_smul]

/-- A nonnull normalized restriction is concentrated on its cell. -/
theorem cellProbability_self {S : Type u} [MeasurableSpace S]
    (μ : ProbabilityMeasure S) (B : Set S) (hB : (μ : Measure S) B ≠ 0) :
    (cellProbability μ B : Measure S) B = 1 := by
  unfold cellProbability
  erw [dite_eq_right hB]
  exact ProbabilityTheory.cond_apply_self hB (measure_ne_top _ _)

/-- Marginals and an event bound for the lift of any finite transport matrix.
`G i j` means that the entire cell rectangle avoids `E`. -/
theorem finite_matrix_coupling {S : Type u} [MeasurableSpace S]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (μ ν : ProbabilityMeasure S) (B : I → Set S) (D : J → Set S)
    (hB : ∀ i, MeasurableSet (B i)) (hD : ∀ j, MeasurableSet (D j))
    (hdB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hdD : Pairwise (fun i j => Disjoint (D i) (D j)))
    (huB : ⋃ i, B i = Set.univ) (huD : ⋃ j, D j = Set.univ)
    (m : I → J → ℝ) (hm : ∀ i j, 0 ≤ m i j)
    (hr : ∀ i, ∑ j, m i j = (μ : Measure S).real (B i))
    (hc : ∀ j, ∑ i, m i j = (ν : Measure S).real (D j))
    (E : Set (S × S)) (G : I → J → Prop) [DecidableRel G]
    (hG : ∀ i j, G i j → ∀ x ∈ B i, ∀ y ∈ D j, (x,y) ∉ E) :
    ∃ γ : ProbabilityMeasure (S × S), IsCoupling μ ν γ ∧
      (γ : Measure (S × S)).real E ≤ ∑ i, ∑ j, if G i j then 0 else m i j := by
  classical
  let P := fun i => cellProbability μ (B i)
  let Q := fun j => cellProbability ν (D j)
  let Γ : Measure (S × S) := ∑ i, ∑ j,
    ENNReal.ofReal (m i j) • (P i : Measure S).prod (Q j : Measure S)
  have hp (i : I) : ENNReal.ofReal (∑ j, m i j) = (μ : Measure S) (B i) := by
    rw [hr, ofReal_measureReal]
  have hq (j : J) : ENNReal.ofReal (∑ i, m i j) = (ν : Measure S) (D j) := by
    rw [hc, ofReal_measureReal]
  have hfst : Measure.map Prod.fst Γ = (μ : Measure S) := by
    dsimp only [Γ]
    simp_rw [Measure.map_finset_sum' measurable_fst.aemeasurable,
      Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_fst_prod,
      measure_univ, one_smul]
    simp_rw [← Finset.sum_smul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hm _ j), hp]
    change (∑ i, (μ : Measure S) (B i) • (cellProbability μ (B i) : Measure S)) = _
    simp_rw [mass_smul_cellProbability]
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdB hB, huB,
      Measure.restrict_univ]
  have hsnd : Measure.map Prod.snd Γ = (ν : Measure S) := by
    dsimp only [Γ]
    simp_rw [Measure.map_finset_sum' measurable_snd.aemeasurable,
      Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_snd_prod,
      measure_univ, one_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hm i _), hq]
    change (∑ j, (ν : Measure S) (D j) • (cellProbability ν (D j) : Measure S)) = _
    simp_rw [mass_smul_cellProbability]
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdD hD, huD,
      Measure.restrict_univ]
  have hprob : IsProbabilityMeasure Γ := by
    constructor
    have h := congrArg (fun ρ : Measure S => ρ Set.univ) hfst
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
      Set.preimage_univ, measure_univ] using h
  let γ : ProbabilityMeasure (S × S) := ⟨Γ, hprob⟩
  refine ⟨γ, ⟨hfst, hsnd⟩, ?_⟩
  have hterm (i : I) (j : J) :
      (ENNReal.ofReal (m i j) • (P i : Measure S).prod (Q j : Measure S)).real E ≤
        if G i j then 0 else m i j := by
    by_cases hz : m i j = 0
    · simp [hz]
    have hpi : (μ : Measure S) (B i) ≠ 0 := by
      intro hzero
      have hle := Finset.single_le_sum (fun j _ => hm i j) (Finset.mem_univ j)
      rw [hr, Measure.real, hzero, ENNReal.toReal_zero] at hle
      exact hz (le_antisymm hle (hm i j))
    have hqj : (ν : Measure S) (D j) ≠ 0 := by
      intro hzero
      have hle := Finset.single_le_sum (fun i _ => hm i j) (Finset.mem_univ i)
      rw [hc, Measure.real, hzero, ENNReal.toReal_zero] at hle
      exact hz (le_antisymm hle (hm i j))
    split_ifs with hg
    · have hrect : ((P i : Measure S).prod (Q j : Measure S)) (B i ×ˢ D j) = 1 := by
        rw [Measure.prod_prod, cellProbability_self μ (B i) hpi,
          cellProbability_self ν (D j) hqj, mul_one]
      have he0 : ((P i : Measure S).prod (Q j : Measure S)) E = 0 := by
        apply measure_mono_null (t := (B i ×ˢ D j)ᶜ)
        · intro z hzE hzBD
          exact hG i j hg z.1 hzBD.1 z.2 hzBD.2 hzE
        · rw [measure_compl (hB i |>.prod (hD j)) (measure_ne_top _ _), hrect,
            measure_univ, tsub_self]
      simp [Measure.real, Measure.smul_apply, he0]
    · rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (hm i j)]
      exact mul_le_of_le_one_right (hm i j) measureReal_le_one
  change Γ.real E ≤ _
  have hfin (i : I) (j : J) :
      (ENNReal.ofReal (m i j) • (P i : Measure S).prod (Q j : Measure S)) E ≠ ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hexp : Γ.real E = ∑ i, ∑ j,
      (ENNReal.ofReal (m i j) • (P i : Measure S).prod (Q j : Measure S)).real E := by
    simp only [Γ, Measure.real, Measure.finsetSum_apply]
    rw [ENNReal.toReal_sum (fun i _ => ENNReal.sum_ne_top.mpr (fun j _ => hfin i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.toReal_sum (fun j _ => hfin i j)
  rw [hexp]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j

/-- A finite Borel partition with a common small remainder for two laws.
The ordinary cells have strictly small pairwise distances. -/
theorem exists_common_small_partition {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SeparableSpace S]
    (μ ν : ProbabilityMeasure S) (h : ℝ) (hh : 0 < h) :
    ∃ (n : ℕ) (B : Option (Fin n) → Set S),
      (∀ i, MeasurableSet (B i)) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (⋃ i, B i = Set.univ) ∧
      (μ : Measure S).real (B none) < h ∧
      (ν : Measure S).real (B none) < h ∧
      ∀ i : Fin n, ∀ x ∈ B (some i), ∀ y ∈ B (some i), dist x y < h := by
  classical
  obtain ⟨C, hC, hbC, hdC, huC, hdis⟩ :=
    SeparableSpace.exists_measurable_partition_diam_le S (half_pos hh)
  let ρ : Measure S := (μ : Measure S) + (ν : Measure S)
  have ht := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
    (μ := ρ) (fun n => (hC n).nullMeasurableSet) hdis
  have hev := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hh))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  let T : Set S := ⋃ k, ⋃ (_ : N ≤ k), C k
  have hT : ρ T < ENNReal.ofReal h := hN N le_rfl
  let B : Option (Fin N) → Set S := fun i => match i with
    | none => T
    | some i => C i
  have hμT : (μ : Measure S) T < ENNReal.ofReal h := by
    apply lt_of_le_of_lt (show (μ : Measure S) T ≤ ρ T from ?_) hT
    simp only [ρ, Measure.add_apply]
    exact le_add_of_nonneg_right zero_le
  have hνT : (ν : Measure S) T < ENNReal.ofReal h := by
    apply lt_of_le_of_lt (show (ν : Measure S) T ≤ ρ T from ?_) hT
    simp only [ρ, Measure.add_apply]
    exact le_add_of_nonneg_left zero_le
  refine ⟨N, B, ?_, ?_, ?_, ENNReal.toReal_lt_of_lt_ofReal hμT,
    ENNReal.toReal_lt_of_lt_ofReal hνT, ?_⟩
  · intro i
    cases i with
    | none => exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hC k
    | some i => exact hC i
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        apply Set.disjoint_left.mpr
        intro x hx hxj
        obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hk, hxk⟩ := Set.mem_iUnion.mp hx
        exact Set.disjoint_left.mp (hdis (by omega : k ≠ (j : ℕ))) hxk hxj
    | some i =>
      cases j with
      | none =>
        apply Disjoint.symm
        apply Set.disjoint_left.mpr
        intro x hx hxi
        obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hk, hxk⟩ := Set.mem_iUnion.mp hx
        exact Set.disjoint_left.mp (hdis (by omega : k ≠ (i : ℕ))) hxk hxi
      | some j =>
        exact hdis (fun heq => hij (congrArg some (Fin.ext heq)))
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ k, C k := huC ▸ Set.mem_univ x
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    by_cases hk : k < N
    · exact Set.mem_iUnion.mpr ⟨some ⟨k,hk⟩, hxk⟩
    · exact Set.mem_iUnion.mpr ⟨none, Set.mem_iUnion.mpr
        ⟨k, Set.mem_iUnion.mpr ⟨Nat.le_of_not_gt hk, hxk⟩⟩⟩
  · intro i x hx y hy
    exact ((Metric.dist_le_diam_of_mem (hbC i) hx hy).trans (hdC i)).trans_lt
      (by linarith)

/-- The Prokhorov inequality supplies the finite transportation cut inequalities
for any finite Borel partition. Allowed edges are pairs admitting close points. -/
theorem partition_cut_bound {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S]
    {I : Type v} [Fintype I]
    (μ ν : ProbabilityMeasure S) (δ : ℝ) (hδ : ProkhorovAdmissible μ ν δ)
    (B : I → Set S) (hB : ∀ i, MeasurableSet (B i))
    (hdB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (huB : ⋃ i, B i = Set.univ) (K : Finset I) :
    (∑ i ∈ K, (μ : Measure S).real (B i)) ≤
      (∑ j ∈ Finset.univ.filter (fun j => ∃ i ∈ K,
        ∃ x ∈ B i, ∃ y ∈ B j, dist x y < δ), (ν : Measure S).real (B j)) + δ := by
  classical
  let A := ⋃ i ∈ K, B i
  let J := Finset.univ.filter (fun j => ∃ i ∈ K,
    ∃ x ∈ B i, ∃ y ∈ B j, dist x y < δ)
  have hA : MeasurableSet A := MeasurableSet.biUnion (Finset.countable_toSet K)
    (fun i _ => hB i)
  have hs : enlargement δ A ⊆ ⋃ j ∈ J, B j := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hx
    have hyB : y ∈ ⋃ j, B j := huB ▸ Set.mem_univ y
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hyB
    refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨?_, hyj⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, x, hxi, y, hyj,
      by simpa only [dist_comm] using hxy⟩
  calc
    _ = (μ : Measure S).real A :=
      (measureReal_biUnion_finset (hdB.set_pairwise _) (fun i _ => hB i)).symm
    _ ≤ (ν : Measure S).real (enlargement δ A) + δ := (hδ.2 A hA).1
    _ ≤ (ν : Measure S).real (⋃ j ∈ J, B j) + δ :=
      add_le_add (measureReal_mono hs (measure_ne_top _ _)) le_rfl
    _ = _ := by rw [measureReal_biUnion_finset (hdB.set_pairwise _) (fun j _ => hB j)]

/-- The strict forward implication in Strassen--Dudley, without completeness. -/
theorem exists_coupling_of_prokhorovDist_lt {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [SeparableSpace S]
    (μ ν : ProbabilityMeasure S) (a : ℝ) (_ha : 0 < a)
    (hπ : prokhorovDist μ ν < a) :
    ∃ γ : ProbabilityMeasure (S × S), IsCoupling μ ν γ ∧
      (γ : Measure (S × S)).real {z | a < dist z.1 z.2} < a := by
  classical
  obtain ⟨δ, hδ, hδa⟩ := exists_lt_of_csInf_lt
    (show Set.Nonempty {b : ℝ | ProkhorovAdmissible μ ν b} from
      ⟨1, prokhorovAdmissible_one μ ν⟩) hπ
  let h := (a - δ) / 4
  have hh : 0 < h := by dsimp [h]; linarith
  have hhδ : δ + 2 * h < a := by dsimp [h]; linarith
  obtain ⟨n, B, hB, hdB, huB, hμ0, hν0, hsmall⟩ :=
    exists_common_small_partition μ ν h hh
  let p : Option (Fin n) → ℝ := fun i => (μ : Measure S).real (B i)
  let q : Option (Fin n) → ℝ := fun j => (ν : Measure S).real (B j)
  let R : Option (Fin n) → Option (Fin n) → Prop := fun i j =>
    ∃ x ∈ B i, ∃ y ∈ B j, dist x y < δ
  have hpsum : ∑ i, p i = 1 := by
    rw [← measureReal_iUnion_fintype hdB hB, huB, probReal_univ]
  have hqsum : ∑ j, q j = 1 := by
    rw [← measureReal_iUnion_fintype hdB hB, huB, probReal_univ]
  obtain ⟨m, hm, hr, hc, hbad⟩ := finite_transportation
    (Option (Fin n)) (Option (Fin n)) p q R δ
    (fun i => measureReal_nonneg) (fun j => measureReal_nonneg) hpsum hqsum
    (partition_cut_bound μ ν δ hδ B hB hdB huB)
  let G : Option (Fin n) → Option (Fin n) → Prop := fun i j =>
    i ≠ none ∧ j ≠ none ∧ R i j
  have hG : ∀ i j, G i j → ∀ x ∈ B i, ∀ y ∈ B j,
      (x,y) ∉ {z : S × S | a < dist z.1 z.2} := by
    intro i j hij x hx y hy
    obtain ⟨hi, hj, u, hu, v, hv, huv⟩ := hij
    obtain ⟨i, rfl⟩ := Option.ne_none_iff_exists'.mp hi
    obtain ⟨j, rfl⟩ := Option.ne_none_iff_exists'.mp hj
    have hxu := hsmall i x hx u hu
    have hvy := hsmall j v hv y hy
    have hxy : dist x y ≤ dist x u + dist u v + dist v y :=
      (dist_triangle x u y).trans (add_le_add le_rfl (dist_triangle u v y)) |>.trans_eq
        (add_assoc _ _ _).symm
    change ¬ a < dist x y
    linarith
  obtain ⟨γ, hγ, hγE⟩ := finite_matrix_coupling μ ν B B hB hB hdB hdB huB huB
    m hm hr hc {z : S × S | a < dist z.1 z.2} G hG
  have hleft : (∑ i, ∑ j, if i = none then m i j else 0) = p none := by
    rw [Finset.sum_comm]
    simp only [Fintype.sum_ite_eq']
    exact hr none
  have hright : (∑ i, ∑ j, if j = none then m i j else 0) = q none := by
    simp only [Fintype.sum_ite_eq']
    exact hc none
  have hsum : (∑ i, ∑ j, if G i j then 0 else m i j) ≤
      (∑ i, ∑ j, if R i j then 0 else m i j) + p none + q none := by
    rw [← hleft, ← hright, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hnonneg := hm i j
    by_cases hi : i = none <;> by_cases hj : j = none <;>
      by_cases hij : R i j <;> simp_all [G]
  refine ⟨γ, hγ, lt_of_le_of_lt (hγE.trans hsum) ?_⟩
  dsimp [p, q]
  linarith

end
end ProbabilityFoundations.Ch06
