import MathGenome.Internal.RealAnalysis.D11.Ch20.RadonCaratheodoryLocalization
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.RadonDisjointCompactLocalization
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

open Set MeasureTheory
open scoped ENNReal
namespace D11.Ch20.RadonDisjointCompactLocalization
universe u v
noncomputable section
open Specs.D11.Ch20.RadonDisjointCompactLocalization

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

/-- Restrict to a compact first: its finite measure is compact-inner-regular
on all measurable sets, so its support is conull without a countability axiom. -/
theorem compact_full_support (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (K : Set X) (hK : IsCompact K) (hpos : 0 < m μ K) :
    ∃ K₀ : Set X, K₀ ⊆ K ∧ m μ K₀ = m μ K ∧ SupportedCompact μ K₀ := by
  letI : MeasurableSpace X := M μ
  letI : OpensMeasurableSpace X := ⟨RadonCaratheodoryLocalization.borel_measurable μ⟩
  letI : Measure.Regular (m μ) := RadonCaratheodoryLocalization.extension_regular μ hμ
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  let ν := (m μ).restrict K
  have hfinite : m μ K ≠ ∞ := hK.measure_lt_top.ne
  letI : Measure.InnerRegular ν :=
    ⟨Measure.InnerRegularWRT.restrict_of_measure_ne_top
      (Measure.InnerRegularCompactLTTop.innerRegular (μ := m μ)) hfinite⟩
  have hsub : ν.support ⊆ K := by
    have h := Measure.support_restrict_subset (μ := m μ) (s := K)
    exact h.trans (by rw [hK.isClosed.closure_eq]; exact inter_subset_left)
  have hc : IsCompact ν.support := hK.of_isClosed_subset Measure.isClosed_support hsub
  have hnull : m μ (K \ ν.support) = 0 := by
    have hn := Measure.measure_compl_support_of_innerRegular (μ := ν)
    simpa [ν, Measure.restrict_apply' hKm, inter_comm, sdiff_eq_compl_inter] using hn
  have heq : m μ ν.support = m μ K := by
    simpa only [inter_eq_right.mpr hsub] using
      (measure_inter_conull' (μ := m μ) hnull)
  refine ⟨ν.support, hsub, heq, hc, by rwa [heq], ?_⟩
  intro U hU hmeet
  obtain ⟨x, hxU, hxs⟩ := hmeet
  have hp : 0 < ν U := (Measure.mem_support_iff_forall x).mp hxs U (hU.mem_nhds hxU)
  have heqU : ν U = m μ (U ∩ ν.support) := by
    have h := measure_inter_conull (μ := ν) (s := U)
      (Measure.measure_compl_support_of_innerRegular (μ := ν))
    simpa only [ν, Measure.restrict_apply' hKm,
      inter_eq_left.mpr hsub, inter_assoc] using h.symm
  rwa [heqU] at hp

/-- Chain unions preserve both full support and pairwise disjointness. -/
theorem exists_maximal_family (μ : @Measure X (borel X)) (_hμ : Ch18.isRadon μ) :
    ∃ C : Set (Set X), MaximalFamily μ C := by
  apply zorn_subset {C | DisjointFamily μ C}
  intro c hgood hchain
  refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
  · intro K hK
    obtain ⟨s, hs, hKs⟩ := hK
    exact (hgood hs).1 K hKs
  · intro K hK L hL hne
    obtain ⟨s, hs, hKs⟩ := hK
    obtain ⟨t, ht, hLt⟩ := hL
    rcases hchain.total hs ht with hst | hts
    · exact (hgood ht).2 (hst hKs) hLt hne
    · exact (hgood hs).2 hKs (hts hLt) hne

/-- An open finite-mass envelope counts even compact pieces whose intersection
with the original set has measure zero. -/
theorem countable_meeting (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (C : Set (Set X)) (hC : DisjointFamily μ C)
    (A : Set X) (hfin : m μ A < ∞) : (meeting C A).Countable := by
  letI : MeasurableSpace X := M μ
  letI : OpensMeasurableSpace X := ⟨RadonCaratheodoryLocalization.borel_measurable μ⟩
  letI : Measure.Regular (m μ) := RadonCaratheodoryLocalization.extension_regular μ hμ
  obtain ⟨U, hAU, hU, hUfin⟩ := A.exists_isOpen_lt_of_lt ∞ hfin
  have hmeas (i : C) : MeasurableSet (U ∩ i.1) :=
    hU.measurableSet.inter (hC.1 i.1 i.2).1.isClosed.measurableSet
  have hdisj : Pairwise (fun i j : C => Disjoint (U ∩ i.1) (U ∩ j.1)) := by
    intro i j hij
    exact (hC.2 i.2 j.2 (fun heq => hij (Subtype.ext heq))).mono
      inter_subset_right inter_subset_right
  have hbound : m μ (⋃ i : C, U ∩ i.1) ≠ ∞ :=
    ((measure_mono (iUnion_subset fun _ => inter_subset_left)).trans_lt hUfin).ne
  have hc := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
    (m μ) hmeas hdisj hbound
  apply (hc.image Subtype.val).mono
  intro K hK
  refine ⟨⟨K, hK.1⟩, ?_, rfl⟩
  obtain ⟨x, hxA, hxK⟩ := hK.2
  exact (hC.1 K hK.1).2.2 U hU ⟨x, hAU hxA, hxK⟩

/-- Maximality eliminates the remaining positive part, using finite-set
compact approximation in the full splitting domain. -/
theorem finite_decomposition (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (C : Set (Set X)) (hC : MaximalFamily μ C)
    (A : Set X) (hA : MeasurableSet[M μ] A) (hfin : m μ A < ∞) :
    (meeting C A).Countable ∧ MeasurableSet[M μ] (A \ ⋃₀ meeting C A) ∧
      m μ (A \ ⋃₀ meeting C A) = 0 := by
  classical
  letI : MeasurableSpace X := M μ
  letI : OpensMeasurableSpace X := ⟨RadonCaratheodoryLocalization.borel_measurable μ⟩
  have hc := countable_meeting μ hμ C hC.1 A hfin
  have hS : MeasurableSet (⋃₀ meeting C A) :=
    MeasurableSet.sUnion hc (fun K hK => (hC.1.1 K hK.1).1.isClosed.measurableSet)
  have hR : MeasurableSet (A \ ⋃₀ meeting C A) := hA.diff hS
  refine ⟨hc, hR, ?_⟩
  by_contra hnonzero
  have hpos : 0 < m μ (A \ ⋃₀ meeting C A) := pos_iff_ne_zero.mpr hnonzero
  have hRfin : m μ (A \ ⋃₀ meeting C A) < ∞ :=
    (measure_mono sdiff_subset).trans_lt hfin
  rw [RadonCaratheodoryLocalization.finite_inner_regular μ hμ _ hR hRfin] at hpos
  obtain ⟨K, hKR, hK, hKpos⟩ : ∃ K, K ⊆ A \ ⋃₀ meeting C A ∧
      IsCompact K ∧ 0 < m μ K := by
    simpa only [lt_iSup_iff, exists_prop] using hpos
  obtain ⟨K₀, hK₀K, _, hK₀⟩ := compact_full_support μ hμ K hK hKpos
  have hK₀R := hK₀K.trans hKR
  have hd (L : Set X) (hL : L ∈ C) : Disjoint K₀ L := by
    apply Set.disjoint_left.mpr
    intro x hx₀ hxL
    have hxR := hK₀R hx₀
    exact hxR.2 (mem_sUnion.mpr ⟨L, ⟨hL, x, hxR.1, hxL⟩, hxL⟩)
  have hins : DisjointFamily μ (insert K₀ C) := by
    refine ⟨?_, ?_⟩
    · intro L hL
      rcases hL with rfl | hL
      · exact hK₀
      · exact hC.1.1 L hL
    · exact Set.pairwise_insert.mpr
        ⟨hC.1.2, fun L hL _ => ⟨hd L hL, (hd L hL).symm⟩⟩
  have hK₀C := hC.mem_of_prop_insert hins
  have hempty : K₀ = ∅ := disjoint_self.mp (hd K₀ hK₀C)
  have := hK₀.2.1
  simpa [hempty] using this

/-- Countably many traces and a null remainder give each compact test;
completeness is essential for the arbitrary subset of that remainder. -/
theorem measurable_iff (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (C : Set (Set X)) (hC : MaximalFamily μ C) (B : Set X) :
    MeasurableSet[M μ] B ↔ ∀ K ∈ C, MeasurableSet[M μ] (B ∩ K) := by
  letI : MeasurableSpace X := M μ
  letI : OpensMeasurableSpace X := ⟨RadonCaratheodoryLocalization.borel_measurable μ⟩
  letI : (m μ).IsComplete := RadonCaratheodoryLocalization.complete μ
  constructor
  · intro hB K hK
    exact hB.inter (hC.1.1 K hK).1.isClosed.measurableSet
  · intro hB
    apply (RadonCaratheodoryLocalization.local_measurable_iff μ hμ B).mpr
    intro L hL
    have hLm : MeasurableSet L := hL.isClosed.measurableSet
    have hLf : m μ L < ∞ := by
      rw [RadonCaratheodoryLocalization.measure_apply]
      exact hμ.1 L hL
    obtain ⟨hc, _, hn⟩ := finite_decomposition μ hμ C hC L hLm hLf
    let T : Set X := ⋃ K ∈ meeting C L, B ∩ K
    have hT : MeasurableSet T :=
      MeasurableSet.biUnion hc (fun K hK => hB K hK.1)
    have hN : MeasurableSet ((B ∩ L) \ ⋃₀ meeting C L) := by
      apply measurableSet_of_null (μ := m μ)
      exact measure_mono_null
        (show (B ∩ L) \ ⋃₀ meeting C L ⊆ L \ ⋃₀ meeting C L from
          fun _ hx => ⟨hx.1.2, hx.2⟩) hn
    have heq : B ∩ L = (L ∩ T) ∪ ((B ∩ L) \ ⋃₀ meeting C L) := by
      ext x
      constructor
      · intro hx
        by_cases hs : x ∈ ⋃₀ meeting C L
        · obtain ⟨K, hK, hxK⟩ := hs
          exact Or.inl ⟨hx.2, mem_iUnion.mpr ⟨K,
            mem_iUnion.mpr ⟨hK, hx.1, hxK⟩⟩⟩
        · exact Or.inr ⟨hx, hs⟩
      · intro hx
        rcases hx with ⟨hxL, hxT⟩ | hxN
        · obtain ⟨K, hxK⟩ := mem_iUnion.mp hxT
          obtain ⟨_, hxBK⟩ := mem_iUnion.mp hxK
          exact ⟨hxBK.1, hxL⟩
        · exact hxN.1
    rw [heq]
    exact (hLm.inter hT).union hN

/-- Choice glues the values as a set function. The compact-family criterion
then proves measurability without taking an uncountable measurable union. -/
theorem measurable_gluing (μ : @Measure X (borel X)) (hμ : Ch18.isRadon μ)
    (C : Set (Set X)) (hC : MaximalFamily μ C) :
    letI : MeasurableSpace X := M μ
    ∀ (Y : Type v) [MeasurableSpace Y] [Zero Y]
      (f : ∀ K : Set X, K ∈ C → K → Y),
      (∀ K (hK : K ∈ C), Measurable (f K hK)) →
      ∃ g : X → Y, Measurable g ∧
        (∀ K (hK : K ∈ C) (x : K), g x = f K hK x) ∧
        (∀ x : X, (∀ K ∈ C, x ∉ K) → g x = 0) := by
  classical
  letI : MeasurableSpace X := M μ
  letI : OpensMeasurableSpace X := ⟨RadonCaratheodoryLocalization.borel_measurable μ⟩
  intro Y _ _ f hf
  let E := Σ K : C, K.1
  let e : E → X := fun p => p.2.1
  let F : E → Y := fun p => f p.1.1 p.1.2 p.2
  have hinj : Function.Injective e := by
    rintro ⟨⟨K, hK⟩, x⟩ ⟨⟨L, hL⟩, y⟩ hxy
    change (x : X) = (y : X) at hxy
    have hKL : K = L := by
      by_contra hne
      exact Set.disjoint_left.mp (hC.1.2 hK hL hne) x.2 (hxy.symm ▸ y.2)
    subst L
    have hsub : x = y := Subtype.ext hxy
    subst y
    rfl
  let g : X → Y := Function.extend e F (fun _ => 0)
  have hg (K : Set X) (hK : K ∈ C) (x : K) : g x = f K hK x :=
    hinj.extend_apply F (fun _ => 0) ⟨⟨K, hK⟩, x⟩
  refine ⟨g, ?_, hg, ?_⟩
  · intro s hs
    apply (measurable_iff μ hμ C hC (g ⁻¹' s)).mpr
    intro K hK
    have hKm : MeasurableSet K := (hC.1.1 K hK).1.isClosed.measurableSet
    have hm := hKm.subtype_image (hf K hK hs)
    have heq : (g ⁻¹' s) ∩ K = Subtype.val '' ((f K hK) ⁻¹' s) := by
      ext x
      constructor
      · intro hx
        refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
        change f K hK ⟨x, hx.2⟩ ∈ s
        rw [← hg K hK ⟨x, hx.2⟩]
        exact hx.1
      · rintro ⟨y, hy, rfl⟩
        exact ⟨by change g y ∈ s; rw [hg K hK y]; exact hy, y.2⟩
    rw [heq]
    exact hm
  · intro x hx
    apply Function.extend_apply'
    rintro ⟨⟨⟨K, hK⟩, y⟩, hy⟩
    change (y : X) = x at hy
    exact hx K hK (hy ▸ y.2)

end
end D11.Ch20.RadonDisjointCompactLocalization
