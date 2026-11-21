import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.PropertyB
import MathGenome.Internal.ExtremalOptimization.P205.Probability.CoordinateDependency
import MathGenome.Internal.ExtremalOptimization.P205.Probability.PositiveProbability
import MathGenome.Internal.ExtremalOptimization.P205.Probability.SymmetricLocalLemma

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace P205.Probability.PropertyB

section Experiment

local instance : MeasurableSpace Bool := ⊤

/-- Probability of one specified constant color pattern, including the empty block. -/
theorem colorPattern_probability {V : Type*} [Fintype V] (F : Finset V) (b : Bool) :
    (coloringModel V).measure.real (colorPattern F b) = (1 / 2 : ℝ) ^ F.card := by
  classical
  have hsingle : fairBit.eventMass ({b} : Set Bool) = 1 / 2 := by
    cases b <;> norm_num [FiniteModel.eventMass, fairBit]
  have hcoord (v : V) :
      (coloringModel V).measure ((fun c : V → Bool => c v) ⁻¹' {b}) =
        ENNReal.ofReal (1 / 2) := by
    rw [coloringModel, FiniteModel.measure_eventMass]
    change ENNReal.ofReal ((FiniteModel.pi (fun _ : V => fairBit)).eventMass
      {c | c v ∈ ({b} : Set Bool)}) = _
    rw [FiniteModel.coordinate_eventMass, hsingle]
  have hset : colorPattern F b =
      ⋂ v ∈ F, (fun c : V → Bool => c v) ⁻¹' {b} := by
    ext c
    simp [colorPattern]
  have hind := (FiniteModel.independent_coordinates (fun _ : V => fairBit)).measure_inter_preimage_eq_mul F (sets := fun _ => {b})
      (fun _ _ => measurableSet_singleton b)
  change (coloringModel V).measure (⋂ v ∈ F, (fun c : V → Bool => c v) ⁻¹' {b}) =
    ∏ v ∈ F, (coloringModel V).measure ((fun c : V → Bool => c v) ⁻¹' {b}) at hind
  change ((coloringModel V).measure (colorPattern F b)).toReal = _
  rw [hset, hind]
  simp [hcoord]

/-- Nonempty edges have two disjoint monochromatic patterns. -/
theorem monochromatic_probability : Specs.P205.Probability.PropertyB.monochromaticProbability := by
  intro V _ F hF
  classical
  have hd : Disjoint (colorPattern F false) (colorPattern F true) := by
    apply Set.disjoint_left.mpr
    intro c hf ht
    obtain ⟨v, hv⟩ := hF
    exact Bool.false_ne_true ((hf v hv).symm.trans (ht v hv))
  rw [← FiniteModel.measureReal_eventMass]
  change (coloringModel V).measure.real (monochromatic F) = _
  rw [monochromatic, measureReal_union hd (FiniteModel.all_measurable _),
    colorPattern_probability, colorPattern_probability]
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_natCast]
  simp only [one_div, inv_pow]
  ring

/-- Membership in the bad event only depends on the vertices of the edge. -/
theorem monochromatic_dependsOn {V : Type*} (F : Finset V) :
    CoordinateDependency.DependsOn (F : Set V) (monochromatic F) := by
  intro c c' h
  simp only [monochromatic, Set.mem_union, colorPattern, Set.mem_ofPred_eq]
  have heq (b : Bool) : (∀ v ∈ F, c v = b) ↔ ∀ v ∈ F, c' v = b := by
    constructor <;> intro hb v hv
    · rw [← h v hv]; exact hb v hv
    · rw [h v hv]; exact hb v hv
  exact or_congr (heq false) (heq true)

/-- The full dependency graph, not just pairwise independence. -/
theorem monochromatic_dependency : Specs.P205.Probability.PropertyB.monochromaticDependency := by
  intro V _ H
  exact CoordinateDependency.isDependencyGraph (fun _ : V => fairBit)
    (fun F : H => (F.val : Set V)) (fun F => monochromatic F.val)
    (fun F => monochromatic_dependsOn F.val)

/-- The graph's degree is precisely the number of intersecting other edges. -/
theorem overlap_degree {V : Type*} (H : Finset (Finset V)) (F : H) :
    (Finset.univ.filter
      ((CoordinateDependency.overlapGraph (fun G : H => (G.val : Set V))).Adj F)).card =
    (H.filter (fun G => G ≠ F.val ∧ (F.val ∩ G).Nonempty)).card := by
  classical
  have hadj (G : H) :
      (CoordinateDependency.overlapGraph (fun G : H => (G.val : Set V))).Adj F G ↔
      G.val ≠ F.val ∧ (F.val ∩ G.val).Nonempty := by
    constructor
    · rintro ⟨hne, v, hv, hv'⟩
      exact ⟨fun heq => hne (Subtype.ext heq.symm), v, Finset.mem_inter.mpr ⟨hv, hv'⟩⟩
    · rintro ⟨hne, v, hv⟩
      exact ⟨fun heq => hne (congrArg Subtype.val heq.symm), v,
        (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
  apply Finset.card_bij (fun G _ => G.val)
  · intro G hG
    exact Finset.mem_filter.mpr ⟨G.property, (hadj G).mp (Finset.mem_filter.mp hG).2⟩
  · intro G _ G' _ heq
    exact Subtype.ext heq
  · intro G hG
    refine ⟨⟨G, (Finset.mem_filter.mp hG).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hadj _).mpr (Finset.mem_filter.mp hG).2⟩

/-- Property B from the symmetric local lemma, retaining empty edge families. -/
theorem property_b : Specs.P205.Probability.PropertyB.propertyB := by
  intro V _ H k d hk hsize hdegree hsmall
  classical
  let A : H → Set (V → Bool) := fun F => monochromatic F.val
  let D := CoordinateDependency.overlapGraph (fun F : H => (F.val : Set V))
  have hprob (F : H) :
      (coloringModel V).measure.real (A F) ≤ (2 : ℝ) ^ (1 - (k : ℤ)) := by
    change ((coloringModel V).measure (monochromatic F.val)).toReal ≤ _
    rw [FiniteModel.measureReal_eventMass, monochromatic_probability F.val
        (Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < k) (hsize F.val F.property)))]
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    have := Int.ofNat_le.mpr (hsize F.val F.property)
    omega
  have hdeg (F : H) : (Finset.univ.filter (D.Adj F)).card ≤ d := by
    rw [show D = CoordinateDependency.overlapGraph (fun F : H => (F.val : Set V)) from rfl,
      overlap_degree]
    exact hdegree F.val F.property
  have hpos := symmetricLocalLemma (coloringModel V).measure A D d
    ((2 : ℝ) ^ (1 - (k : ℤ))) (monochromatic_dependency H) hdeg
    (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)) hprob hsmall
  have hpos' : 0 < (coloringModel V).measure (⋂ F, (A F)ᶜ) :=
    ENNReal.toReal_pos_iff.mp hpos |>.1
  obtain ⟨c, hc⟩ := nonempty_of_positive_probability (coloringModel V).measure
    (⋂ F, (A F)ᶜ) (FiniteModel.all_measurable _) hpos'
  refine ⟨c, ?_⟩
  intro F hF
  have hgood : c ∉ monochromatic F := (Set.mem_iInter.mp hc ⟨F, hF⟩)
  have hnfalse : ¬ ∀ v ∈ F, c v = false := fun h => hgood (Or.inl h)
  have hntrue : ¬ ∀ v ∈ F, c v = true := fun h => hgood (Or.inr h)
  constructor
  · push Not at hntrue
    obtain ⟨v, hv, hb⟩ := hntrue
    refine ⟨v, hv, ?_⟩
    cases hcv : c v <;> simp_all
  · push Not at hnfalse
    obtain ⟨v, hv, hb⟩ := hnfalse
    refine ⟨v, hv, ?_⟩
    cases hcv : c v <;> simp_all

end Experiment

end P205.Probability.PropertyB
