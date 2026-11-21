import MathGenome.Internal.ExtremalOptimization.P205.Probability.DependencyGraph
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.LocalLemmaConditionals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped BigOperators Classical

universe u v

namespace P205.Probability

/-- Avoidance of the events indexed by a finite set. -/
def avoidEvents {I : Type u} {Ω : Type v} (A : I → Set Ω) (S : Finset I) : Set Ω :=
  ⋂ j ∈ S, (A j)ᶜ

@[simp] theorem avoidEvents_empty {I : Type u} {Ω : Type v} (A : I → Set Ω) :
    avoidEvents A ∅ = Set.univ := by simp [avoidEvents]

@[simp] theorem avoidEvents_insert {I : Type u} {Ω : Type v} (A : I → Set Ω)
    (j : I) (S : Finset I) :
    avoidEvents A (insert j S) = (A j)ᶜ ∩ avoidEvents A S := by
  ext ω
  simp [avoidEvents]

 theorem avoidEvents_antitone {I : Type u} {Ω : Type v} (A : I → Set Ω)
    {S T : Finset I} (h : S ⊆ T) : avoidEvents A T ⊆ avoidEvents A S := by
  intro ω hω
  simp only [avoidEvents, Set.mem_iInter] at hω ⊢
  exact fun j hj => hω j (h hj)

 theorem avoidEvents_measurable {I : Type u} {Ω : Type v} [MeasurableSpace Ω]
    (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (S : Finset I) :
    MeasurableSet (avoidEvents A S) := by
  exact MeasurableSet.biInter (Finset.countable_toSet _) (fun i _ => (hA i).compl)

 theorem avoidEvents_step {I : Type u} {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (S : Finset I) (j : I) :
    μ.real (avoidEvents A (insert j S)) =
      μ.real (avoidEvents A S) - μ.real (A j ∩ avoidEvents A S) := by
  have h := measureReal_inter_add_sdiff (μ := μ) (s := avoidEvents A S) (hA j)
  have he : avoidEvents A S \ A j = avoidEvents A (insert j S) := by
    rw [avoidEvents_insert]
    ext ω
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]
    exact and_comm
  rw [he, Set.inter_comm (avoidEvents A S) (A j)] at h
  linarith

/-- Chain-rule lower bound, using estimates only at proper subsets of `S`. -/
theorem avoidance_extension_lower {I : Type u} {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (x : I → ℝ) (hx : ∀ i, x i ≤ 1)
    (S : Finset I)
    (hcond : ∀ R ⊂ S, ∀ i ∉ R,
      μ.real (A i ∩ avoidEvents A R) ≤ x i * μ.real (avoidEvents A R))
    (T U : Finset I) (hTU : T ∪ U ⊆ S) (hdis : Disjoint T U) :
    μ.real (avoidEvents A T) * ∏ j ∈ U, (1 - x j) ≤
      μ.real (avoidEvents A (T ∪ U)) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert j U hj ih =>
    have hTU' : T ∪ U ⊆ S := (Finset.union_subset_union_right (Finset.subset_insert j U)).trans hTU
    have hd' : Disjoint T U := hdis.mono_right (Finset.subset_insert j U)
    have hjT : j ∉ T := fun hjT => Finset.disjoint_left.mp hdis hjT (Finset.mem_insert_self _ _)
    have hjR : j ∉ T ∪ U := by simp [hjT, hj]
    have hproper : T ∪ U ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hTU', fun he =>
        hjR (he.symm ▸ hTU (by simp))⟩
    have hc := hcond (T ∪ U) hproper j hjR
    have hs := avoidEvents_step μ A hA (T ∪ U) j
    have hi := mul_le_mul_of_nonneg_right (ih hTU' hd') (sub_nonneg.mpr (hx j))
    rw [Finset.prod_insert hj]
    have he : T ∪ insert j U = insert j (T ∪ U) := by ext k; simp
    rw [he]
    nlinarith

/-- Both induction claims, before division by the avoidance probability. -/
theorem localLemmaConditionals_mul {I : Type u} [Fintype I] {Ω : Type v}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : I → Set Ω) (D : SimpleGraph I) (x : I → ℝ)
    (hD : IsDependencyGraph μ A D) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hprob : ∀ i, μ.real (A i) ≤ x i *
      ∏ j ∈ Finset.univ.filter (D.Adj i), (1 - x j))
    (S : Finset I) :
    0 < μ.real (avoidEvents A S) ∧
      ∀ i ∉ S, μ.real (A i ∩ avoidEvents A S) ≤ x i * μ.real (avoidEvents A S) := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have hsmall : ∀ R ⊂ S, ∀ i ∉ R,
        μ.real (A i ∩ avoidEvents A R) ≤ x i * μ.real (avoidEvents A R) :=
      fun R hR => (ih R hR).2
    have hprod := avoidance_extension_lower μ A hD.1 x (fun j => (hx j).2.le)
      S hsmall ∅ S (by simp) (by simp)
    have hpos : 0 < μ.real (avoidEvents A S) := by
      have hp : 0 < ∏ j ∈ S, (1 - x j) :=
        Finset.prod_pos (fun j _ => sub_pos.mpr (hx j).2)
      simp only [avoidEvents_empty, probReal_univ, one_mul, Finset.empty_union] at hprod
      exact hp.trans_le hprod
    refine ⟨hpos, ?_⟩
    intro i hi
    let N : Finset I := Finset.univ.filter (D.Adj i)
    let U : Finset I := S.filter (D.Adj i)
    let T : Finset I := S \ U
    have hUS : U ⊆ S := Finset.filter_subset _ _
    have hUN : U ⊆ N := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    have hTS : T ⊆ S := Finset.sdiff_subset
    have hTU : T ∪ U = S := Finset.sdiff_union_of_subset hUS
    have hdis : Disjoint T U := Finset.sdiff_disjoint
    have hm : MeasurableSet[MeasurableSpace.generateFrom
        (A '' {j : I | j ≠ i ∧ ¬ D.Adj i j})] (avoidEvents A T) := by
      apply MeasurableSet.biInter (Finset.countable_toSet T)
      intro j hj
      have hjS : j ∈ S := hTS hj
      have hjne : j ≠ i := fun he => hi (he ▸ hjS)
      have hjnon : ¬ D.Adj i j := by
        intro hadj
        exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr ⟨hjS, hadj⟩)
      have hgen : A j ∈ A '' {j : I | j ≠ i ∧ ¬ D.Adj i j} :=
        ⟨j, ⟨hjne, hjnon⟩, rfl⟩
      exact (MeasurableSpace.measurableSet_generateFrom hgen).compl
    have hind : μ.real (A i ∩ avoidEvents A T) =
        μ.real (A i) * μ.real (avoidEvents A T) := by
      simpa only [Measure.real, ENNReal.toReal_mul] using
        congrArg ENNReal.toReal (hD.2 i (avoidEvents A T) hm)
    have hlow : μ.real (avoidEvents A T) * ∏ j ∈ U, (1 - x j) ≤
        μ.real (avoidEvents A S) := by
      have h := avoidance_extension_lower μ A hD.1 x (fun j => (hx j).2.le)
        S hsmall T U (by rw [hTU]) hdis
      rwa [hTU] at h
    have hnp : (∏ j ∈ N, (1 - x j)) ≤ ∏ j ∈ U, (1 - x j) :=
      Finset.prod_le_prod_of_subset_of_le_one₀ hUN
        (fun j _ => sub_nonneg.mpr (hx j).2.le)
        (fun j _ _ => by linarith [(hx j).1])
    calc
      μ.real (A i ∩ avoidEvents A S) ≤ μ.real (A i ∩ avoidEvents A T) :=
        measureReal_mono (Set.inter_subset_inter_right _ (avoidEvents_antitone A hTS))
      _ = μ.real (A i) * μ.real (avoidEvents A T) := hind
      _ ≤ (x i * ∏ j ∈ N, (1 - x j)) * μ.real (avoidEvents A T) :=
        mul_le_mul_of_nonneg_right (hprob i) (measureReal_nonneg)
      _ ≤ (x i * ∏ j ∈ U, (1 - x j)) * μ.real (avoidEvents A T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnp (hx i).1)
          measureReal_nonneg
      _ = x i * (μ.real (avoidEvents A T) * ∏ j ∈ U, (1 - x j)) := by ring
      _ ≤ x i * μ.real (avoidEvents A S) := mul_le_mul_of_nonneg_left hlow (hx i).1

/-- Conditional bad-event probabilities are bounded by `x`, and every finite
avoidance event has strictly positive probability (p205:lll-conditional). -/
theorem localLemmaConditionals : Specs.P205.Probability.LocalLemmaConditionalsType.{u, v} := by
  intro I _ Ω _ μ _ A D x hD hx hprob S
  have h := localLemmaConditionals_mul μ A D x hD hx hprob S
  refine ⟨h.1, ?_⟩
  intro i hi
  exact (div_le_iff₀ h.1).mpr (h.2 i hi)

end P205.Probability
