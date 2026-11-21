import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.CountableAdditivityCriterion

/-!
Continuity criteria for a finitely additive, extended nonnegative set function.
The sufficient condition at the empty set is proved by adding partial-union
and tail values and taking limits, so it needs no global finiteness assumption.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u

namespace D11.Ch01.CountableAdditivityCriterion

open D11.Ch01.MeasureDefinitions

variable {α : Type u} [MeasurableSpace α]
  (hA : IsSetAlgebra {s : Set α | MeasurableSet s}) (p : AlgebraMeasure _ hA)

/-- Upgrade only after proving the countable-additivity law. -/
private def sourceOfAdditive (hp : CountablyAdditive p) : SourceMeasure α where
  value := p.value
  empty := p.empty
  iUnion := hp

private def partialUnion (E : ℕ → MeasurableDomain α) (n : ℕ) : MeasurableDomain α :=
  ⟨Set.accumulate (fun i => (E i).1) n,
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => (E _).2⟩

private theorem partialUnion_sum (E : ℕ → MeasurableDomain α)
    (hd : Pairwise fun i j => Disjoint (E i).1 (E j).1) (n : ℕ) :
    p.value (partialUnion E n) = ∑ i ∈ Finset.range (n + 1), p.value (E i) := by
  have h := D11.Ch01.MeasureDefinitions.finite_additivity hA p
    (Finset.range (n + 1)) E (fun i _ j _ hij => hd hij)
  convert h using 2
  apply Subtype.ext
  ext x
  simp [partialUnion, Set.accumulate]

private theorem partialUnion_tendsto (E : ℕ → MeasurableDomain α)
    (hd : Pairwise fun i j => Disjoint (E i).1 (E j).1) :
    Tendsto (fun n => p.value (partialUnion E n)) atTop (𝓝 (∑' n, p.value (E n))) := by
  simp_rw [partialUnion_sum hA p E hd]
  exact (ENNReal.tendsto_nat_tsum (fun n => p.value (E n))).comp (tendsto_add_atTop_nat 1)

theorem countablyAdditive_iff_continuousFromBelow :
    CountablyAdditive p ↔ ContinuousFromBelow p := by
  constructor
  · intro hp E hE
    let q := sourceOfAdditive hA p hp
    let μ := measureOfSource q
    have h := (D11.Ch01.MeasureBoundsContinuity.continuity_from_below μ
      (fun n => (E n).1) (⋃ n, (E n).1) (fun n => (E n).2) hE rfl).2.2
    have hfun : (fun n => μ (E n).1) = fun n => p.value (E n) :=
      funext fun n => measureOfSource_apply q _ (E n).2
    have hmass : μ (⋃ n, (E n).1) =
        p.value ⟨⋃ n, (E n).1, MeasurableSet.iUnion fun n => (E n).2⟩ :=
      measureOfSource_apply q _ _
    simpa only [hfun, hmass] using h
  · intro hp E hd
    have h := hp (partialUnion E) Set.monotone_accumulate
    have hU : (⋃ n, (partialUnion E n).1) = ⋃ n, (E n).1 := Set.iUnion_accumulate
    have heq := tendsto_nhds_unique h (partialUnion_tendsto hA p E hd)
    simpa only [hU] using heq

theorem countablyAdditive_of_continuousAtEmpty
    (hp : ContinuousAtEmpty p) : CountablyAdditive p := by
  intro E hd
  let U : MeasurableDomain α := ⟨⋃ n, (E n).1, MeasurableSet.iUnion fun n => (E n).2⟩
  let T : ℕ → MeasurableDomain α := fun n =>
    ⟨U.1 \ (partialUnion E n).1, U.2.diff (partialUnion E n).2⟩
  have hanti : Antitone (fun n => (T n).1) := by
    intro i j hij x hx
    exact ⟨hx.1, fun hxi => hx.2 (Set.monotone_accumulate hij hxi)⟩
  have hzero : (⋂ n, (T n).1) = ∅ := by
    simp only [T, Set.sdiff_eq, Set.iInter_inter_distrib, Set.iInter_const,
      ← Set.compl_iUnion, partialUnion, Set.iUnion_accumulate, U,
      Set.inter_compl_self]
  have htail := hp T hanti hzero
  have hdec (n : ℕ) : p.value U = p.value (partialUnion E n) + p.value (T n) := by
    have h := p.union (partialUnion E n) (T n) disjoint_sdiff_self_right
    convert h using 1
    congr 1
    apply Subtype.ext
    dsimp [T, U, partialUnion]
    rw [Set.union_sdiff_self, Set.union_eq_right.mpr (Set.accumulate_subset_iUnion _)]
  have hsum := (partialUnion_tendsto hA p E hd).add htail
  have hconst : Tendsto (fun _ : ℕ => p.value U) atTop
      (𝓝 ((∑' n, p.value (E n)) + 0)) := by
    simpa only [← hdec] using hsum
  simpa only [add_zero] using tendsto_nhds_unique tendsto_const_nhds hconst

theorem continuousAtEmpty_of_countablyAdditive_of_finite
    (hp : CountablyAdditive p) (hfin : p.value ⟨univ, MeasurableSet.univ⟩ < ∞) :
    ContinuousAtEmpty p := by
  intro E hE hlim
  let q := sourceOfAdditive hA p hp
  let μ := measureOfSource q
  have hmass : μ univ < ∞ := by
    change measureOfSource q univ < ∞
    rw [measureOfSource_apply q _ MeasurableSet.univ]
    exact hfin
  have h := (D11.Ch01.MeasureBoundsContinuity.continuity_from_above μ
    (fun n => (E n).1) ∅ (fun n => (E n).2) hE hlim
    ⟨0, (measure_mono (Set.subset_univ _)).trans_lt hmass⟩).2.2
  have hfun : (fun n => μ (E n).1) = fun n => p.value (E n) :=
    funext fun n => measureOfSource_apply q _ (E n).2
  simpa only [measure_empty, hfun] using h

theorem finite_countablyAdditive_iff_continuousAtEmpty
    (hfin : p.value ⟨univ, MeasurableSet.univ⟩ < ∞) :
    CountablyAdditive p ↔ ContinuousAtEmpty p :=
  ⟨fun hp => continuousAtEmpty_of_countablyAdditive_of_finite hA p hp hfin,
    countablyAdditive_of_continuousAtEmpty hA p⟩

end D11.Ch01.CountableAdditivityCriterion
