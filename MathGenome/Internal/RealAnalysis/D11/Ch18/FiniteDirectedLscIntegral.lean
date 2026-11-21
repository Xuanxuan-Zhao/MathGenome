import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonFiniteInner
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.FiniteDirectedLscIntegral

/-! Arbitrary-index monotone convergence for LSC families. Compact inner
regularity replaces countable continuity from below in the simple-function
proof. No topology on the index and no countability assumption is used. -/
namespace D11.Ch18.FiniteDirectedLscIntegral

open Set MeasureTheory
open scoped ENNReal NNReal
universe u v

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X
local instance {X : Type u} [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

theorem supremum_regularity
    {X : Type u} [TopologicalSpace X] {I : Type v}
    (f : I → X → ℝ≥0∞) (hf : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (fun x => ⨆ i, f i x) ∧
      Measurable (fun x => ⨆ i, f i x) := by
  exact ⟨lowerSemicontinuous_iSup hf, (lowerSemicontinuous_iSup hf).measurable⟩

/-- A finite-mass Borel set covered by directed opens has its mass
approximated by intersections with single members of the cover. -/
theorem measure_eq_iSup_inter_of_directed_open_cover
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)) (hμ : isRadon μ)
    {E : Set X} (hE : MeasurableSet E) (hfin : μ E < ∞)
    {I : Type v} [Nonempty I] (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hd : Directed (· ⊆ ·) U) (hcover : E ⊆ ⋃ i, U i) :
    μ E = ⨆ i, μ (E ∩ U i) := by
  apply le_antisymm
  · rw [RadonFiniteInner.finite_inner_regular μ hμ E hE hfin]
    refine iSup_le fun K => iSup_le fun hKE => iSup_le fun hK => ?_
    obtain ⟨i, hi⟩ := hK.elim_directed_cover U hU (hKE.trans hcover) hd
    exact le_iSup_of_le i (measure_mono (subset_inter hKE hi))
  · exact iSup_le fun i => measure_mono inter_subset_left

/-- The finite Radon result actually needs no bound on the family.

For a simple minorant `s` of the supremum and `r < 1`, every nonzero
level `p` of `r * s` is covered by the directed opens `{p < f i}`.
The compact-cover lemma computes its mass as a supremum. Directedness
commutes that supremum with the finite sum of level contributions.
Those sums are integrals of restrictions of `r * s` lying below `f i`.
Finally let `r` tend to one and take the supremum over simple minorants. -/
theorem lintegral_iSup_directed_of_lowerSemicontinuous
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)) (hμ : isRadon μ) (hfin : μ univ < ∞)
    {I : Type v} [Nonempty I] (f : I → X → ℝ≥0∞)
    (hf : ∀ i, LowerSemicontinuous (f i)) (hd : Directed (· ≤ ·) f) :
    (∫⁻ x, ⨆ i, f i x ∂μ) = ⨆ i, ∫⁻ x, f i x ∂μ := by
  classical
  let c : ℝ≥0 → ℝ≥0∞ := (↑)
  refine le_antisymm ?_ (iSup_lintegral_le _)
  rw [lintegral_eq_nnreal]
  refine iSup_le fun s => iSup_le fun hsf => ?_
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  obtain ⟨r, rfl, _⟩ := ENNReal.lt_iff_exists_coe.mp ha
  have hr : r < 1 := ENNReal.coe_lt_coe.mp ha
  let rs := s.map fun b => r * b
  let t := rs.map c
  have ht : t = (SimpleFunc.const X (r : ℝ≥0∞)) * s.map c := rfl
  have hU : ∀ p, ∀ i, IsOpen {x | p < f i x} := fun p i =>
    (hf i).isOpen_preimage p
  have hdir : ∀ p, Directed (· ⊆ ·) (fun i => {x | p < f i x}) := by
    intro p i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, fun x hx => hx.trans_le (hik x), fun x hx => hx.trans_le (hjk x)⟩
  have heq : ∀ p, p * μ (t ⁻¹' {p}) = ⨆ i, p * μ (t ⁻¹' {p} ∩ {x | p < f i x}) := by
    intro p
    by_cases hp : p = 0
    · simp [hp]
    rw [measure_eq_iSup_inter_of_directed_open_cover μ hμ
      (t.measurableSet_preimage {p}) ((measure_mono (subset_univ _)).trans_lt hfin)
      (fun i => {x | p < f i x}) (hU p) (hdir p) ?_, ENNReal.mul_iSup]
    intro x hx
    have htx : t x = p := hx
    have hsx : s x ≠ 0 := by
      intro hz
      apply hp
      rw [← htx]
      simp [t, rs, c, hz]
    have hlt : t x < ⨆ i, f i x := by
      refine lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr ?_) (hsf x)
      change r * s x < s x
      simpa using mul_lt_mul_of_pos_right hr (pos_iff_ne_zero.mpr hsx)
    obtain ⟨i, hi⟩ := lt_iSup_iff.mp (htx ▸ hlt)
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hmeas : ∀ i, MeasurableSet {x | t x < f i x} := fun i =>
    measurableSet_lt t.measurable (hf i).measurable
  calc
    (r : ℝ≥0∞) * (s.map c).lintegral μ = ∑ p ∈ t.range, p * μ (t ⁻¹' {p}) := by
      rw [← SimpleFunc.const_mul_lintegral, ← ht, SimpleFunc.lintegral]
    _ = ∑ p ∈ t.range, ⨆ i, p * μ (t ⁻¹' {p} ∩ {x | p < f i x}) := by
      simp_rw [heq]
    _ = ⨆ i, ∑ p ∈ t.range, p * μ (t ⁻¹' {p} ∩ {x | p < f i x}) := by
      apply ENNReal.finsetSum_iSup
      intro i j
      obtain ⟨k, hik, hjk⟩ := hd i j
      refine ⟨k, fun p => ⟨?_, ?_⟩⟩
      · gcongr
        exact hik _
      · gcongr
        exact hjk _
    _ ≤ ⨆ i, (t.restrict {x | t x < f i x}).lintegral μ := by
      apply iSup_mono
      intro i
      rw [SimpleFunc.restrict_lintegral _ (hmeas i)]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro p hp
      congr 2
      ext x
      exact and_congr_right fun hx => by
        have hx' : t x = p := hx
        change (p < f i x ↔ t x < f i x)
        rw [hx']
    _ ≤ ⨆ i, ∫⁻ x, f i x ∂μ := by
      apply iSup_mono
      intro i
      rw [← SimpleFunc.lintegral_eq_lintegral]
      apply lintegral_mono
      intro x
      simp only [SimpleFunc.restrict_apply _ (hmeas i)]
      by_cases hx : t x < f i x
      · simpa [hx] using hx.le
      · simp [hx]

/-- The exact bounded specialization requested by the parent proof. -/
theorem lintegral_iSup_directed
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)) (hμ : isRadon μ) (hfin : μ univ < ∞)
    {I : Type v} [Nonempty I] (f : I → X → ℝ≥0∞)
    (hf : ∀ i, LowerSemicontinuous (f i)) (hd : Directed (· ≤ ·) f)
    (C : ℝ≥0∞) (_hC : C < ∞) (_hbound : ∀ i x, f i x ≤ C) :
    (∫⁻ x, ⨆ i, f i x ∂μ) = ⨆ i, ∫⁻ x, f i x ∂μ :=
  lintegral_iSup_directed_of_lowerSemicontinuous μ hμ hfin f hf hd

end D11.Ch18.FiniteDirectedLscIntegral

/- Mathlib proof attribution
Adapted portion near line 48:
The simple-function minorant and scaling steps in the integral argument,
adapted to finite Radon measure and directed lower semicontinuous families.

Upstream: Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean (around line 34)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
