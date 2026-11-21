import MathGenome.Internal.RealAnalysis.D11.Ch14.ScalarInterfaces
import MathGenome.Internal.RealAnalysis.D11.Ch14.Hahn
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ExtendedSignedVariant
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.IsLUB

open Set MeasureTheory
open scoped ENNReal symmDiff

universe u
noncomputable section

namespace D11.Ch14.ExtendedSignedVariant
open D11.Ch01.MeasureDefinitions D11.Ch14.ScalarInterfaces

/-- Positive and negative parts of an individual extended real number. -/
theorem extended_parts (x : EReal) :
    x = (x.toENNReal : EReal) - ((-x).toENNReal : EReal) := by
  by_cases h : 0 ≤ x
  · rw [EReal.toENNReal_of_nonpos (EReal.neg_le_zero.mpr h),
      EReal.coe_ennreal_zero, sub_zero, EReal.coe_toENNReal h]
  · have hx : x ≤ 0 := le_of_not_ge h
    rw [EReal.toENNReal_of_nonpos hx, EReal.coe_ennreal_zero, zero_sub,
      EReal.coe_toENNReal (EReal.neg_nonneg.mpr hx), neg_neg]

/-- A defined extended sum with a finite result has both sign sums finite. -/
theorem defined_sum_finite {f : ℕ → EReal} {a : EReal}
    (h : DefinedExtendedSum f a) (hat : a ≠ ⊤) (hab : a ≠ ⊥) :
    (∑' n, (f n).toENNReal) ≠ ⊤ ∧ (∑' n, (-f n).toENNReal) ≠ ⊤ := by
  rcases h with ⟨hfin, ha⟩
  constructor
  · intro hp
    rcases hfin with hfin | hfin
    · exact hfin hp
    · apply hat
      rw [ha, hp, EReal.coe_ennreal_top, EReal.top_sub]
      simpa using hfin
  · intro hq
    apply hab
    rw [ha, hq, EReal.coe_ennreal_top, EReal.sub_top]

theorem defined_sum_hasSum_toReal {f : ℕ → EReal} {a : EReal}
    (h : DefinedExtendedSum f a) (hat : a ≠ ⊤) (hab : a ≠ ⊥) :
    HasSum (fun n => (f n).toReal) a.toReal := by
  obtain ⟨hp,hq⟩ := defined_sum_finite h hat hab
  have hf : ∀ n, (f n).toReal = (f n).toENNReal.toReal - (-f n).toENNReal.toReal := by
    intro n
    have he := congrArg EReal.toReal (extended_parts (f n))
    rw [EReal.toReal_sub (by simpa using ENNReal.ne_top_of_tsum_ne_top hp n)
      (EReal.coe_ennreal_ne_bot _)
      (by simpa using ENNReal.ne_top_of_tsum_ne_top hq n)
      (EReal.coe_ennreal_ne_bot _)] at he
    simpa only [EReal.toReal_coe_ennreal] using he
  have ha : a.toReal = (∑' n, (f n).toENNReal).toReal -
      (∑' n, (-f n).toENNReal).toReal := by
    rw [h.2, EReal.toReal_sub (by simpa using hp) (EReal.coe_ennreal_ne_bot _)
      (by simpa using hq) (EReal.coe_ennreal_ne_bot _)]
    simp only [EReal.toReal_coe_ennreal]
  rw [ha]
  simp_rw [hf]
  simpa only [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hp),
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hq)] using
    (ENNReal.hasSum_toReal hp).sub (ENNReal.hasSum_toReal hq)

theorem two_parts_add (x y : EReal)
    (h : (x ≠ ⊤ ∧ y ≠ ⊤) ∨ (x ≠ ⊥ ∧ y ≠ ⊥)) :
    ((x.toENNReal + y.toENNReal : ℝ≥0∞) : EReal) -
      (((-x).toENNReal + (-y).toENNReal : ℝ≥0∞) : EReal) = x + y := by
  cases x <;> cases y <;>
    simp_all [EReal.toENNReal_of_ne_top, EReal.top_sub, ← EReal.coe_neg,
      EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal]
  rename_i x y
  simp only [max_def]
  split_ifs <;> norm_cast at * <;> norm_num at * <;> linarith

/-- Finite additivity on the original measurable domain. -/
theorem value_union {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α)
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B) :
    ν.value ⟨A ∪ B, hA.union hB⟩ = ν.value ⟨A,hA⟩ + ν.value ⟨B,hB⟩ := by
  classical
  let E : ℕ → MeasurableDomain α := fun n =>
    if n = 0 then ⟨A,hA⟩ else if n = 1 then ⟨B,hB⟩ else ⟨∅,MeasurableSet.empty⟩
  have hE : Pairwise fun i j => Disjoint (E i).1 (E j).1 := by
    intro i j hij
    dsimp [E]
    split_ifs <;> simp_all [Disjoint.symm]
  have hu : (⋃ n, (E n).1) = A ∪ B := by
    apply Set.Subset.antisymm
    · apply iUnion_subset
      intro n; dsimp [E]; split_ifs <;> simp
    · apply union_subset
      · exact (by simpa [E] using (subset_iUnion (fun n => (E n).1) 0))
      · exact (by simpa [E] using (subset_iUnion (fun n => (E n).1) 1))
  have hts (g : EReal → ℝ≥0∞) (hg : g 0 = 0) :
      ∑' n, g (ν.value (E n)) = g (ν.value ⟨A,hA⟩) + g (ν.value ⟨B,hB⟩) := by
    rw [tsum_eq_sum (s := ({0,1} : Finset ℕ))]
    · simp [E]
    · intro n hn
      have hn0 : n ≠ 0 := by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn; exact hn.1
      have hn1 : n ≠ 1 := by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn; exact hn.2
      dsimp [E]
      rw [ite_eq_right hn0, ite_eq_right hn1]
      change g (ν.value ⟨∅,MeasurableSet.empty⟩) = 0
      rw [ν.empty, hg]
  have h := (ν.iUnion E hE).2
  rw [hts EReal.toENNReal EReal.toENNReal_zero,
    hts (fun x => (-x).toENNReal) (by simp)] at h
  have hh : ((ν.value ⟨A,hA⟩ ≠ ⊤ ∧ ν.value ⟨B,hB⟩ ≠ ⊤) ∨
      (ν.value ⟨A,hA⟩ ≠ ⊥ ∧ ν.value ⟨B,hB⟩ ≠ ⊥)) :=
    ν.omitsInfinity.imp (fun h => ⟨h _,h _⟩) (fun h => ⟨h _,h _⟩)
  rw [two_parts_add _ _ hh] at h
  simpa only [hu] using h

/-- If negative infinity is omitted, a finite-valued set has only finite-valued
measurable subsets. This does not assert that the whole measure is finite. -/
theorem finite_subset {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α)
    (hbot : ∀ E, ν.value E ≠ ⊥) (E : Set α) (hE : MeasurableSet E)
    (hEt : ν.value ⟨E,hE⟩ ≠ ⊤) (A : Set α) (hA : MeasurableSet A) (hAE : A ⊆ E) :
    ν.value ⟨A,hA⟩ ≠ ⊤ := by
  have hsplit := value_union ν A (E \ A) hA (hE.diff hA) disjoint_sdiff_right
  have he : A ∪ E \ A = E := by grind
  simp only [he] at hsplit
  intro hAt
  apply hEt
  rw [hsplit, hAt, EReal.top_add_of_ne_bot (hbot _)]

/-- A genuinely finite restriction, converted to a real-valued signed measure. -/
def finiteRestriction {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α)
    (hbot : ∀ E, ν.value E ≠ ⊥) (E : Set α) (hE : MeasurableSet E)
    (hEt : ν.value ⟨E,hE⟩ ≠ ⊤) : SignedMeasure α :=
  scalarOfSource
    { value := fun A => (ν.value ⟨A.1 ∩ E,A.2.inter hE⟩).toReal
      empty := by simpa only [empty_inter, ν.empty] using EReal.toReal_zero
      iUnion := fun A hd => by
        let B : ℕ → MeasurableDomain α := fun n => ⟨(A n).1 ∩ E,(A n).2.inter hE⟩
        have hB : Pairwise fun i j => Disjoint (B i).1 (B j).1 :=
          fun i j hij => (hd hij).mono inter_subset_left inter_subset_left
        have hbU : (⋃ n, (B n).1) ⊆ E := iUnion_subset fun _ => inter_subset_right
        have hs := defined_sum_hasSum_toReal (ν.iUnion B hB)
          (finite_subset ν hbot E hE hEt _ (MeasurableSet.iUnion fun n => (B n).2) hbU)
          (hbot _)
        simpa only [B, ← iUnion_inter] using hs }

theorem finiteRestriction_apply {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (hbot : ∀ E, ν.value E ≠ ⊥)
    (E : Set α) (hE : MeasurableSet E) (hEt : ν.value ⟨E,hE⟩ ≠ ⊤)
    (A : Set α) (hA : MeasurableSet A) :
    finiteRestriction ν hbot E hE hEt A = (ν.value ⟨A ∩ E,hA.inter hE⟩).toReal :=
  scalarOfSource_apply _ A hA

/-- Negative-set extraction for the extended interface, proved by a finite
restriction rather than by assuming finite total variation. -/
theorem negative_extraction {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (hbot : ∀ E, ν.value E ≠ ⊥)
    (E : Set α) (hE : MeasurableSet E) (hneg : ν.value ⟨E,hE⟩ < 0) :
    ∃ (N : Set α) (hN : NegativeSet ν N), N ⊆ E ∧ ν.value ⟨N,hN.1⟩ < 0 := by
  have hEt : ν.value ⟨E,hE⟩ ≠ ⊤ := ne_top_of_lt hneg
  let s := finiteRestriction ν hbot E hE hEt
  have hsE : s E < 0 := by
    rw [finiteRestriction_apply ν hbot E hE hEt E hE]
    simp only [inter_self]
    have hc := EReal.coe_toReal hEt (hbot ⟨E,hE⟩)
    exact EReal.coe_lt_coe_iff.mp (by simpa only [hc, EReal.coe_zero] using hneg)
  obtain ⟨N,hN,hNE,hsN,hlt⟩ := s.exists_subset_restrict_nonpos hsE
  have hnegN : NegativeSet ν N := by
    refine ⟨hN, fun A hA hAN => ?_⟩
    have hAE : A ⊆ E := hAN.trans hNE
    have hsA : s A ≤ 0 := by
      simpa using (VectorMeasure.restrict_le_restrict_iff s 0 hN).mp hsN hA hAN
    rw [finiteRestriction_apply ν hbot E hE hEt A hA] at hsA
    simp only [inter_eq_left.mpr hAE] at hsA
    have hc := EReal.coe_toReal (finite_subset ν hbot E hE hEt A hA hAE) (hbot ⟨A,hA⟩)
    simpa only [hc, EReal.coe_zero] using EReal.coe_le_coe_iff.mpr hsA
  refine ⟨N,hnegN,hNE,?_⟩
  rw [finiteRestriction_apply ν hbot E hE hEt N hN] at hlt
  simp only [inter_eq_left.mpr hNE] at hlt
  have hc := EReal.coe_toReal (finite_subset ν hbot E hE hEt N hN hNE) (hbot ⟨N,hN⟩)
  simpa only [hc, EReal.coe_zero] using EReal.coe_lt_coe_iff.mpr hlt

/-- Countable unions of negative sets are negative, even before finiteness of
one Jordan mass has been established. -/
theorem negativeSet_iUnion {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (N : ℕ → Set α) (hN : ∀ n, NegativeSet ν (N n)) :
    NegativeSet ν (⋃ n, N n) := by
  refine ⟨MeasurableSet.iUnion fun n => (hN n).1, fun A hA hAN => ?_⟩
  let B : ℕ → MeasurableDomain α := fun n =>
    ⟨A ∩ disjointed N n,hA.inter (MeasurableSet.disjointed (fun n => (hN n).1) n)⟩
  have hd : Pairwise fun i j => Disjoint (B i).1 (B j).1 :=
    fun i j hij => (disjoint_disjointed N hij).mono inter_subset_right inter_subset_right
  have hu : (⋃ n, (B n).1) = A := by
    dsimp [B]
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left.mpr hAN]
  have hnval : ∀ n, ν.value (B n) ≤ 0 := fun n =>
    (hN n).2 _ (B n).2 (inter_subset_right.trans (disjointed_subset N n))
  have hs := (ν.iUnion B hd).2
  have hp : (∑' n, (ν.value (B n)).toENNReal) = 0 := by
    simp only [EReal.toENNReal_of_nonpos (hnval _), tsum_zero]
  rw [hp, EReal.coe_ennreal_zero, zero_sub] at hs
  simp only [hu] at hs
  rw [hs]
  exact EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _)

/-- Negative-set values decrease under measurable inclusion. -/
theorem negativeSet_antitone {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (N : Set α) (hN : NegativeSet ν N)
    (A : Set α) (hA : MeasurableSet A) (hAN : A ⊆ N) :
    ν.value ⟨N,hN.1⟩ ≤ ν.value ⟨A,hA⟩ := by
  have h := value_union ν A (N \ A) hA (hN.1.diff hA) disjoint_sdiff_right
  have he : A ∪ N \ A = N := by grind
  simp only [he] at h
  rw [h]
  exact add_le_of_nonpos_right ((hN.2 _ (hN.1.diff hA) sdiff_subset))

/-- Hahn existence when negative infinity is omitted. The infimum is taken
in the extended reals; the negative union itself proves it is finite. -/
theorem hahn_exists_of_omits_bot {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (hbot : ∀ E, ν.value E ≠ ⊥) :
    ∃ P : Set α, PositiveSet ν P ∧ NegativeSet ν Pᶜ := by
  let S : Set EReal := {r | ∃ (N : Set α) (hN : NegativeSet ν N), ν.value ⟨N,hN.1⟩ = r}
  have hS : S.Nonempty := by
    refine ⟨0,∅,⟨MeasurableSet.empty,?_⟩,ν.empty⟩
    intro A hA hAE
    have : A = ∅ := subset_empty_iff.mp hAE
    subst A; rw [ν.empty]
  obtain ⟨f,hfmono,hflim,hfS⟩ := exists_seq_tendsto_sInf hS (OrderBot.bddBelow S)
  choose N hN hfN using hfS
  let U := ⋃ n, N n
  have hU : NegativeSet ν U := negativeSet_iUnion ν N hN
  have hmin : ν.value ⟨U,hU.1⟩ = sInf S := by
    apply le_antisymm
    · apply le_of_tendsto_of_tendsto tendsto_const_nhds hflim
      exact Filter.Eventually.of_forall fun n => by
        rw [← hfN n]
        exact negativeSet_antitone ν U hU (N n) (hN n).1 (subset_iUnion N n)
    · exact sInf_le ⟨U,hU,rfl⟩
  refine ⟨Uᶜ,⟨hU.1.compl,?_⟩,by simpa using hU⟩
  intro A hA hAU
  by_contra hpos
  have hneg : ν.value ⟨A,hA⟩ < 0 := lt_of_not_ge hpos
  obtain ⟨B,hB,hBA,hBneg⟩ := negative_extraction ν hbot A hA hneg
  have hUB : NegativeSet ν (U ∪ B) := by
    let T : ℕ → Set α := fun n => if n = 0 then U else B
    have hT : ∀ n, NegativeSet ν (T n) := fun n => by
      dsimp [T]; split_ifs <;> assumption
    have hh := negativeSet_iUnion ν T hT
    have he : (⋃ n, T n) = U ∪ B := by
      apply Subset.antisymm
      · apply iUnion_subset; intro n; dsimp [T]; split_ifs <;> simp
      · apply union_subset
        · simpa [T] using (subset_iUnion T 0)
        · simpa [T] using (subset_iUnion T 1)
    simpa only [he] using hh
  have hdis : Disjoint U B := disjoint_compl_right.mono_right (hBA.trans hAU)
  have hless : ν.value ⟨U ∪ B,hUB.1⟩ < ν.value ⟨U,hU.1⟩ := by
    rw [value_union ν U B hU.1 hB.1 hdis]
    have hUt : ν.value ⟨U,hU.1⟩ ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top
      (hU.2 U hU.1 Subset.rfl)
    have hc := EReal.coe_toReal hUt (hbot ⟨U,hU.1⟩)
    simpa only [hc, add_zero] using
      EReal.add_lt_add_left_coe hBneg (ν.value ⟨U,hU.1⟩).toReal
  have hbound : sInf S ≤ ν.value ⟨U ∪ B,hUB.1⟩ := sInf_le ⟨U ∪ B,hUB,rfl⟩
  exact (not_lt_of_ge (hmin ▸ hbound)) hless

/-- Sign reversal preserves defined sums and the omitted-infinity condition. -/
def negate {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α) :
    ExtendedSignedMeasure α where
  value E := -ν.value E
  empty := by rw [ν.empty, neg_zero]
  omitsInfinity := by
    rcases ν.omitsInfinity with h | h
    · exact Or.inr (fun E => by simpa using h E)
    · exact Or.inl (fun E => by simpa using h E)
  iUnion E hd := by
    obtain ⟨hfin,heq⟩ := ν.iUnion E hd
    refine ⟨by simpa only [neg_neg, or_comm] using hfin,?_⟩
    rw [heq, EReal.neg_sub]
    · simp only [neg_neg, sub_eq_add_neg, add_comm]
    · exact Or.inl (EReal.coe_ennreal_ne_bot _)
    · exact hfin.imp (fun h => by simpa using h) (fun h => by simpa using h)

@[simp] theorem negate_value {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (E : MeasurableDomain α) :
    (negate ν).value E = -ν.value E := rfl

theorem hahn_exists {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α) :
    ∃ P : Set α, PositiveSet ν P ∧ NegativeSet ν Pᶜ := by
  rcases ν.omitsInfinity with ht | hb
  · have hb' : ∀ E, (negate ν).value E ≠ ⊥ := fun E => by simpa using ht E
    obtain ⟨P,hP,hN⟩ := hahn_exists_of_omits_bot (negate ν) hb'
    refine ⟨Pᶜ,⟨hN.1,?_⟩,⟨by simpa using hP.1,?_⟩⟩
    · intro A hA hAP
      simpa using hN.2 A hA hAP
    · intro A hA hAP
      have hAP' : A ⊆ P := by simpa using hAP
      simpa using hP.2 A hA hAP'
  · exact hahn_exists_of_omits_bot ν hb

/-- The positive restriction on a positive Hahn set, extended as a native measure
on the same measurable space. No finite-mass hypothesis is imposed. -/
def measureOnPositive {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (P : Set α) (hP : PositiveSet ν P) : Measure α :=
  measureOfSource
    { value := fun A => (ν.value ⟨A.1 ∩ P,A.2.inter hP.1⟩).toENNReal
      empty := by simpa only [empty_inter, ν.empty] using EReal.toENNReal_zero
      iUnion := fun A hd => by
        let B : ℕ → MeasurableDomain α := fun n => ⟨(A n).1 ∩ P,(A n).2.inter hP.1⟩
        have hB : Pairwise fun i j => Disjoint (B i).1 (B j).1 :=
          fun i j hij => (hd hij).mono inter_subset_left inter_subset_left
        have hnonneg : ∀ n, 0 ≤ ν.value (B n) := fun n =>
          hP.2 _ (B n).2 inter_subset_right
        have hs := (ν.iUnion B hB).2
        have hz : (∑' n, (-ν.value (B n)).toENNReal) = 0 := by
          simp only [EReal.toENNReal_of_nonpos (EReal.neg_le_zero.mpr (hnonneg _)), tsum_zero]
        rw [hz, EReal.coe_ennreal_zero, sub_zero] at hs
        have he := congrArg EReal.toENNReal hs
        simp only [EReal.toENNReal_coe] at he
        simpa only [B, ← iUnion_inter] using he }

theorem measureOnPositive_apply {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (P : Set α) (hP : PositiveSet ν P)
    (A : Set α) (hA : MeasurableSet A) :
    measureOnPositive ν P hP A = (ν.value ⟨A ∩ P,hA.inter hP.1⟩).toENNReal :=
  measureOfSource_apply _ A hA

/-- Hahn restrictions supply a Jordan pair with a finite opposing total mass. -/
theorem jordan_exists {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α) :
    ∃ μ η : Measure α, IsJordanPair ν μ η := by
  obtain ⟨P,hP,hN⟩ := hahn_exists ν
  have hneg : PositiveSet (negate ν) Pᶜ :=
    ⟨hN.1,fun A hA hAP => by simpa using hN.2 A hA hAP⟩
  let μ := measureOnPositive ν P hP
  let η := measureOnPositive (negate ν) Pᶜ hneg
  have hμ (A : Set α) (hA : MeasurableSet A) :
      μ A = (ν.value ⟨A ∩ P,hA.inter hP.1⟩).toENNReal := measureOnPositive_apply _ _ _ _ hA
  have hη (A : Set α) (hA : MeasurableSet A) :
      η A = (-ν.value ⟨A ∩ Pᶜ,hA.inter hN.1⟩).toENNReal := measureOnPositive_apply _ _ _ _ hA
  refine ⟨μ,η,⟨?_,?_,?_⟩⟩
  · refine ⟨Pᶜ,hN.1,?_,?_⟩
    · rw [hμ Pᶜ hN.1]; simp only [compl_inter_self,ν.empty,EReal.toENNReal_zero]
    · rw [hη (Pᶜ)ᶜ hN.1.compl]
      simp only [compl_compl,inter_compl_self,ν.empty,neg_zero,EReal.toENNReal_zero]
  · rcases ν.omitsInfinity with ht | hb
    · left; rw [hμ univ MeasurableSet.univ]
      exact EReal.toENNReal_ne_top_iff.mpr (ht _)
    · right; rw [hη univ MeasurableSet.univ]
      apply EReal.toENNReal_ne_top_iff.mpr
      simpa using hb ⟨univ ∩ Pᶜ,MeasurableSet.univ.inter hN.1⟩
  · intro A hA
    rw [hμ A hA,hη A hA,
      EReal.coe_toENNReal (hP.2 _ (hA.inter hP.1) inter_subset_right),
      EReal.coe_toENNReal (EReal.neg_nonneg.mpr (hN.2 _ (hA.inter hN.1) inter_subset_right)),
      sub_eq_add_neg,neg_neg]
    have hs := value_union ν (A ∩ P) (A ∩ Pᶜ) (hA.inter hP.1) (hA.inter hN.1)
      (disjoint_compl_right.mono inter_subset_right inter_subset_right)
    simpa only [← inter_union_distrib_left,union_compl_self,inter_univ] using hs

/-- A positive restriction is independent of the Hahn partition. Crossed pieces
are both positive and negative; their value is zero, so no infinity is cancelled. -/
theorem positive_restrictions_eq {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (P Q : Set α)
    (hP : PositiveSet ν P) (hN : NegativeSet ν Pᶜ)
    (hQ : PositiveSet ν Q) (hM : NegativeSet ν Qᶜ)
    (E : Set α) (hE : MeasurableSet E) :
    ν.value ⟨E ∩ P,hE.inter hP.1⟩ = ν.value ⟨E ∩ Q,hE.inter hQ.1⟩ := by
  have hreduce (P Q : Set α) (hp : PositiveSet ν P) (hq : PositiveSet ν Q)
      (hn : NegativeSet ν Qᶜ) :
      ν.value ⟨E ∩ P,hE.inter hp.1⟩ = ν.value ⟨(E ∩ P) ∩ Q,(hE.inter hp.1).inter hq.1⟩ := by
    have hmeas : MeasurableSet ((E ∩ P) \ Q) := (hE.inter hp.1).diff hq.1
    have hz : ν.value ⟨(E ∩ P) \ Q,hmeas⟩ = 0 :=
      le_antisymm (hn.2 _ hmeas (fun _ hx => hx.2))
        (hp.2 _ hmeas (sdiff_subset.trans inter_subset_right))
    have hs := value_union ν ((E ∩ P) \ Q) ((E ∩ P) ∩ Q)
      hmeas ((hE.inter hp.1).inter hq.1) disjoint_sdiff_inter
    simpa only [sdiff_union_inter,hz,zero_add] using hs
  calc
    _ = ν.value ⟨(E ∩ P) ∩ Q,(hE.inter hP.1).inter hQ.1⟩ := hreduce P Q hP hQ hM
    _ = ν.value ⟨(E ∩ Q) ∩ P,(hE.inter hQ.1).inter hP.1⟩ := by
      congr 1; apply Subtype.ext; exact inter_right_comm E P Q
    _ = _ := (hreduce Q P hQ hP hN).symm

/-- Every mutually singular positive difference has its own supporting Hahn
partition and its parts are the corresponding restrictions. -/
theorem jordanPair_support {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (μ η : Measure α) (h : IsJordanPair ν μ η) :
    ∃ (P : Set α) (hP : PositiveSet ν P) (hN : NegativeSet ν Pᶜ),
      ∀ (E : Set α) (hE : MeasurableSet E),
        μ E = (ν.value ⟨E ∩ P,hE.inter hP.1⟩).toENNReal ∧
        η E = (-ν.value ⟨E ∩ Pᶜ,hE.inter hN.1⟩).toENNReal := by
  obtain ⟨S,hS,hμS,hηSc⟩ := h.1
  have hP : PositiveSet ν Sᶜ := by
    refine ⟨hS.compl,fun A hA hAS => ?_⟩
    have hz : η A = 0 := measure_mono_null hAS hηSc
    rw [h.2.2 A hA,hz,EReal.coe_ennreal_zero,sub_zero]
    exact EReal.coe_ennreal_nonneg _
  have hN : NegativeSet ν (Sᶜ)ᶜ := by
    refine ⟨hS.compl.compl,fun A hA hAS => ?_⟩
    have hz : μ A = 0 := measure_mono_null (by simpa only [compl_compl] using hAS) hμS
    rw [h.2.2 A hA,hz,EReal.coe_ennreal_zero,zero_sub]
    exact EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _)
  refine ⟨Sᶜ,hP,hN,fun E hE => ?_⟩
  constructor
  · have hz : η (E ∩ Sᶜ) = 0 := measure_mono_null inter_subset_right hηSc
    rw [h.2.2 _ (hE.inter hP.1),hz,EReal.coe_ennreal_zero,sub_zero,EReal.toENNReal_coe]
    exact (measure_inter_conull (μ := μ) (s := E) (t := Sᶜ) (by simpa using hμS)).symm
  · have hz : μ (E ∩ (Sᶜ)ᶜ) = 0 :=
      measure_mono_null (by simpa only [compl_compl] using (inter_subset_right (s := E) (t := (Sᶜ)ᶜ))) hμS
    rw [h.2.2 _ (hE.inter hN.1),hz,EReal.coe_ennreal_zero,zero_sub,neg_neg,EReal.toENNReal_coe]
    exact (measure_inter_conull (μ := η) (s := E) (t := (Sᶜ)ᶜ) (by simpa using hηSc)).symm

/-- Any Jordan pair obeys the restrictions for every Hahn partition. -/
theorem jordanPair_hahn_formula {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (μ η : Measure α) (h : IsJordanPair ν μ η)
    (P : Set α) (hP : PositiveSet ν P) (hN : NegativeSet ν Pᶜ)
    (E : Set α) (hE : MeasurableSet E) :
    μ E = (ν.value ⟨E ∩ P,hE.inter hP.1⟩).toENNReal ∧
    η E = (-ν.value ⟨E ∩ Pᶜ,hE.inter hN.1⟩).toENNReal := by
  obtain ⟨Q,hQ,hM,hform⟩ := jordanPair_support ν μ η h
  have hp := positive_restrictions_eq ν Q P hQ hM hP hN E hE
  have hnQ : PositiveSet (negate ν) Qᶜ :=
    ⟨hM.1,fun A hA hAQ => by simpa using hM.2 A hA hAQ⟩
  have hnP : PositiveSet (negate ν) Pᶜ :=
    ⟨hN.1,fun A hA hAP => by simpa using hN.2 A hA hAP⟩
  have hpQ : NegativeSet (negate ν) (Qᶜ)ᶜ :=
    ⟨hQ.1.compl.compl,fun A hA hAQ => by
      simpa using hQ.2 A hA (by simpa only [compl_compl] using hAQ)⟩
  have hpP : NegativeSet (negate ν) (Pᶜ)ᶜ :=
    ⟨hP.1.compl.compl,fun A hA hAP => by
      simpa using hP.2 A hA (by simpa only [compl_compl] using hAP)⟩
  have hn := positive_restrictions_eq (negate ν) Qᶜ Pᶜ hnQ hpQ hnP hpP E hE
  constructor
  · exact (hform E hE).1.trans (congrArg EReal.toENNReal hp)
  · exact (hform E hE).2.trans (congrArg EReal.toENNReal hn)

def selectedPair {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α) :
    Measure α × Measure α := Specs.D11.Ch14.ExtendedSignedVariant.selectedPair_value ν

def positivePart {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α) : Measure α :=
  (selectedPair ν).1

def negativePart {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α) : Measure α :=
  (selectedPair ν).2

def variation {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α) : Measure α :=
  positivePart ν + negativePart ν

def partitionVariation {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α)
    (E : Set α) : ℝ≥0∞ := Specs.D11.Ch14.ExtendedSignedVariant.partitionVariation_value ν E

theorem jordan_decomposition {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) : IsJordanPair ν (positivePart ν) (negativePart ν) := by
  obtain ⟨μ,η,h⟩ := jordan_exists ν
  exact Classical.epsilon_spec (p := fun p : Measure α × Measure α => IsJordanPair ν p.1 p.2)
    ⟨(μ,η),h⟩

theorem jordan_hahn_formula {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (P : Set α) (hP : PositiveSet ν P) (hN : NegativeSet ν Pᶜ)
    (E : Set α) (hE : MeasurableSet E) :
    positivePart ν E = (ν.value ⟨E ∩ P,hE.inter hP.1⟩).toENNReal ∧
    negativePart ν E = (-ν.value ⟨E ∩ Pᶜ,hE.inter hN.1⟩).toENNReal :=
  jordanPair_hahn_formula ν _ _ (jordan_decomposition ν) P hP hN E hE

theorem jordan_unique {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (μ η : Measure α) (h : IsJordanPair ν μ η) :
    μ = positivePart ν ∧ η = negativePart ν := by
  obtain ⟨P,hP,hN⟩ := hahn_exists ν
  constructor
  · apply Measure.ext; intro E hE
    exact (jordanPair_hahn_formula ν μ η h P hP hN E hE).1.trans
      (jordan_hahn_formula ν P hP hN E hE).1.symm
  · apply Measure.ext; intro E hE
    exact (jordanPair_hahn_formula ν μ η h P hP hN E hE).2.trans
      (jordan_hahn_formula ν P hP hN E hE).2.symm

/-- The absolute cost of a defined difference is bounded by the sum of its
positive costs. The estimate remains valid when either cost is infinite. -/
theorem absolute_difference_le (p q : ℝ≥0∞) :
    ((p : EReal) - (q : EReal)).toENNReal +
      (-((p : EReal) - (q : EReal))).toENNReal ≤ p + q := by
  by_cases hq : q = ⊤
  · simp only [hq,add_top,le_top]
  have hp : ((p : EReal) - (q : EReal)).toENNReal ≤ p := by
    rw [EReal.toENNReal_sub (EReal.coe_ennreal_nonneg _),EReal.toENNReal_coe,EReal.toENNReal_coe]
    exact tsub_le_self
  have hn : (-((p : EReal) - (q : EReal))).toENNReal ≤ q := by
    rw [EReal.neg_sub (Or.inl (EReal.coe_ennreal_ne_bot _)) (Or.inr (by simpa using hq)),
      add_comm,← sub_eq_add_neg,EReal.toENNReal_sub (EReal.coe_ennreal_nonneg _),
      EReal.toENNReal_coe,EReal.toENNReal_coe]
    exact tsub_le_self
  exact add_le_add hp hn

/-- The supremum of finite partition costs is exactly the sum of the two
Jordan measures. The supporting two-piece partition attains this supremum. -/
theorem partition_variation_identity {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (E : Set α) (hE : MeasurableSet E) :
    partitionVariation ν E = variation ν E := by
  classical
  obtain ⟨P,hP,hN⟩ := hahn_exists ν
  have hrep := (jordan_decomposition ν).2.2
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    have hp : positivePart ν E = ∑ i, positivePart ν (F i).1 := by
      simpa only [tsum_fintype,hF.2] using
        measure_iUnion (μ := positivePart ν) hF.1 (fun i => (F i).2)
    have hn : negativePart ν E = ∑ i, negativePart ν (F i).1 := by
      simpa only [tsum_fintype,hF.2] using
        measure_iUnion (μ := negativePart ν) hF.1 (fun i => (F i).2)
    change (∑ i, ((ν.value (F i)).toENNReal + (-ν.value (F i)).toENNReal)) ≤
      (positivePart ν + negativePart ν) E
    rw [Measure.add_apply,hp,hn,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [hrep (F i).1 (F i).2]
    exact absolute_difference_le _ _
  · let F : Fin 2 → MeasurableDomain α := fun i =>
      if i = 0 then ⟨E ∩ P,hE.inter hP.1⟩ else ⟨E ∩ Pᶜ,hE.inter hN.1⟩
    have hF : PartitionOf E F := by
      constructor
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [F]
        all_goals first
          | exact disjoint_compl_right.mono inter_subset_right inter_subset_right
          | exact disjoint_compl_left.mono inter_subset_right inter_subset_right
      · apply Subset.antisymm
        · apply iUnion_subset
          intro i; dsimp [F]; split_ifs <;> exact inter_subset_left
        · intro x hx
          by_cases hxP : x ∈ P
          · exact mem_iUnion.mpr ⟨0,by simp [F,hx,hxP]⟩
          · exact mem_iUnion.mpr ⟨1,by simp [F,hx,hxP]⟩
    have hsum : (∑ i, ((ν.value (F i)).toENNReal + (-ν.value (F i)).toENNReal)) = variation ν E := by
      have hpos := hP.2 (E ∩ P) (hE.inter hP.1) inter_subset_right
      have hneg := hN.2 (E ∩ Pᶜ) (hE.inter hN.1) inter_subset_right
      simp only [Fin.sum_univ_two,F,ite_true,one_ne_zero,ite_false,
        EReal.toENNReal_of_nonpos (EReal.neg_le_zero.mpr hpos),
        EReal.toENNReal_of_nonpos hneg,add_zero,zero_add]
      rw [← (jordan_hahn_formula ν P hP hN E hE).1,
        ← (jordan_hahn_formula ν P hP hN E hE).2]
      exact (Measure.add_apply _ _ _).symm
    rw [← hsum]
    exact le_iSup_of_le 2 (le_iSup_of_le F (le_iSup_of_le hF le_rfl))

/-- The nullity statement for two Hahn partitions includes every measurable
subset, as well as the variation of their symmetric difference. -/
theorem hahn_unique {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (P Q : Set α)
    (hP : PositiveSet ν P) (hN : NegativeSet ν Pᶜ)
    (hQ : PositiveSet ν Q) (hM : NegativeSet ν Qᶜ) :
    (∀ (A : Set α) (hA : MeasurableSet A), A ⊆ P ∆ Q → ν.value ⟨A,hA⟩ = 0) ∧
    variation ν (P ∆ Q) = 0 := by
  have hz : ∀ (A : Set α) (hA : MeasurableSet A), A ⊆ P ∆ Q → ν.value ⟨A,hA⟩ = 0 := by
    intro A hA hAS
    have hAPQ : A ∩ P ⊆ Qᶜ := by
      intro x hx
      rcases mem_symmDiff.mp (hAS hx.1) with h | h
      · exact h.2
      · exact False.elim (h.2 hx.2)
    have hANQ : A ∩ Pᶜ ⊆ Q := by
      intro x hx
      rcases mem_symmDiff.mp (hAS hx.1) with h | h
      · exact False.elim (hx.2 h.1)
      · exact h.1
    have hzP : ν.value ⟨A ∩ P,hA.inter hP.1⟩ = 0 :=
      le_antisymm (hM.2 _ (hA.inter hP.1) hAPQ)
        (hP.2 _ (hA.inter hP.1) inter_subset_right)
    have hzN : ν.value ⟨A ∩ Pᶜ,hA.inter hN.1⟩ = 0 :=
      le_antisymm (hN.2 _ (hA.inter hN.1) inter_subset_right)
        (hQ.2 _ (hA.inter hN.1) hANQ)
    have hs := value_union ν (A ∩ P) (A ∩ Pᶜ) (hA.inter hP.1) (hA.inter hN.1)
      (disjoint_compl_right.mono inter_subset_right inter_subset_right)
    simpa only [← inter_union_distrib_left,union_compl_self,inter_univ,hzP,hzN,zero_add] using hs
  refine ⟨hz,?_⟩
  have hS : MeasurableSet (P ∆ Q) := hP.1.symmDiff hQ.1
  rw [variation,Measure.add_apply,
    (jordan_hahn_formula ν P hP hN (P ∆ Q) hS).1,
    (jordan_hahn_formula ν P hP hN (P ∆ Q) hS).2,
    hz _ (hS.inter hP.1) inter_subset_left,
    hz _ (hS.inter hN.1) inter_subset_left]
  simp

/-- The selected integral keeps the manuscript's measurable, absolutely
integrable domain; no value is asserted for nonintegrable functions. -/
def scalarIntegrable {α : Type u} [MeasurableSpace α] {𝕜 : Type}
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : ExtendedSignedMeasure α) (f : α → 𝕜) : Prop :=
  Specs.D11.Ch14.ExtendedSignedVariant.scalarIntegrable_value ν f

def scalarIntegral {α : Type u} [MeasurableSpace α] {𝕜 : Type}
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : ExtendedSignedMeasure α) (f : α → 𝕜) (_hf : scalarIntegrable ν f) : 𝕜 :=
  (∫ x, f x ∂positivePart ν) - (∫ x, f x ∂negativePart ν)

def isSigmaFinite {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α) : Prop :=
  SigmaFinite (variation ν)

theorem scalarIntegrable_iff {α : Type u} [MeasurableSpace α] {𝕜 : Type}
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : ExtendedSignedMeasure α) (f : α → 𝕜) :
    scalarIntegrable ν f ↔ Measurable f ∧ Integrable f (variation ν) :=
  D11.Ch06.ScalarIntegral.scalarIntegrable_iff (variation ν) f

theorem parts_integrable {α : Type u} [MeasurableSpace α] {𝕜 : Type}
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : ExtendedSignedMeasure α) (f : α → 𝕜) (hf : scalarIntegrable ν f) :
    Integrable f (positivePart ν) ∧ Integrable f (negativePart ν) := by
  have hi := ((scalarIntegrable_iff ν f).mp hf).2
  exact integrable_add_measure.mp hi

theorem scalarIntegral_add {α : Type u} [MeasurableSpace α] {𝕜 : Type}
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : ExtendedSignedMeasure α) (f g : α → 𝕜)
    (hf : scalarIntegrable ν f) (hg : scalarIntegrable ν g)
    (hfg : scalarIntegrable ν (fun x => f x + g x)) :
    scalarIntegral ν (fun x => f x + g x) hfg = scalarIntegral ν f hf + scalarIntegral ν g hg := by
  obtain ⟨hfP,hfN⟩ := parts_integrable ν f hf
  obtain ⟨hgP,hgN⟩ := parts_integrable ν g hg
  simp only [scalarIntegral,integral_add hfP hgP,integral_add hfN hgN]
  abel

theorem scalarIntegral_const_mul {α : Type u} [MeasurableSpace α] {𝕜 : Type}
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : ExtendedSignedMeasure α) (c : 𝕜) (f : α → 𝕜)
    (hf : scalarIntegrable ν f) (hcf : scalarIntegrable ν (fun x => c * f x)) :
    scalarIntegral ν (fun x => c * f x) hcf = c * scalarIntegral ν f hf := by
  simp only [scalarIntegral,integral_const_mul,mul_sub]

theorem sigmaFinite_iff {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α) :
    isSigmaFinite ν ↔ SigmaFinite (variation ν) := Iff.rfl

end D11.Ch14.ExtendedSignedVariant
