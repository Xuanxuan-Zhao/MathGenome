import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.LebesgueDecompositionSigmaFinite
import MathGenome.Internal.RealAnalysis.D11.Ch15.RNPositiveSigmaFinite
import MathGenome.Internal.RealAnalysis.D11.Ch15.LebesgueDecompositionFiniteTarget
import MathGenome.Internal.RealAnalysis.D11.Ch15.RNSignedComplex

/-! Sigma-finite Lebesgue decomposition, paper.tex:4922–4945.
On each finite-mass block choose a maximal reference-null set using the
upstream finite-target construction. Their union supports the singular part.
The complement restriction is AC, so upstream positive RN supplies its density.
Uniqueness compares restrictions on a common null support; no infinities are
subtracted. The finite scalar statements combine finite-target decomposition
with finite scalar RN. -/

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace D11.Ch15.LebesgueDecompositionSigmaFinite

variable {X : Type u} [MeasurableSpace X]

/-- Patch the finite-target null supports along a countable finite partition. -/
theorem exists_null_support (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] :
    ∃ Z : Set X, MeasurableSet Z ∧ μ Z = 0 ∧ ν.restrict Zᶜ ≪ μ := by
  classical
  obtain ⟨A, hA, hdis, hcover⟩ := RNPositiveSigmaFinite.common_finite_partition μ ν
  have hex (n : ℕ) :=
    LebesgueDecompositionFiniteTarget.exists_maximal_null_set (ν.restrict (A n)) μ
  choose B hm hn hmax using hex
  let Z := ⋃ n, B n
  have hZm : MeasurableSet Z := MeasurableSet.iUnion hm
  have hZn : μ Z = 0 := measure_iUnion_null hn
  refine ⟨Z, hZm, hZn, Measure.AbsolutelyContinuous.mk ?_⟩
  intro E hE hEn
  rw [Measure.restrict_apply hE]
  have hlocal (n : ℕ) : (ν.restrict (A n)) (E ∩ Zᶜ) = 0 := by
    let : IsFiniteMeasure (ν.restrict (A n)) :=
      isFiniteMeasure_restrict.mpr (hA n).2.2.ne
    have hz := LebesgueDecompositionFiniteTarget.null_difference
      (ν.restrict (A n)) μ (B n) (hm n) (hn n) (hmax n) E hE hEn
    apply measure_mono_null (t := E \ B n) ?_ hz
    intro x hx
    exact ⟨hx.1, fun hxb => hx.2 (mem_iUnion.mpr ⟨n, hxb⟩)⟩
  have hν : (Measure.sum (fun n => ν.restrict (A n))) = ν := by
    rw [← Measure.restrict_iUnion hdis (fun n => (hA n).1), hcover,
      Measure.restrict_univ]
  rw [← hν, Measure.sum_apply _ (hE.inter hZm.compl)]
  simp only [hlocal, tsum_zero]

/-- A decomposition supported on a reference-null set is determined by
restrictions. This works for arbitrary masses. -/
theorem parts_from_null_support (μ ν a s : Measure X) (Z : Set X)
    (hZ : MeasurableSet Z) (hμZ : μ Z = 0) (hsZ : s Zᶜ = 0)
    (hsum : ν = a + s) (hac : a ≪ μ) :
    a = ν.restrict Zᶜ ∧ s = ν.restrict Z := by
  have ha0 : a.restrict Z = 0 := Measure.restrict_eq_zero.mpr (hac hμZ)
  have hs0 : s.restrict Zᶜ = 0 := Measure.restrict_eq_zero.mpr hsZ
  have ha : a.restrict Zᶜ = a := by
    simpa only [ha0, zero_add] using (Measure.restrict_add_restrict_compl (μ := a) hZ)
  have hs : s.restrict Z = s := by
    simpa only [hs0, add_zero] using (Measure.restrict_add_restrict_compl (μ := s) hZ)
  rw [hsum, Measure.restrict_add, Measure.restrict_add, ha0, hs0, ha, hs,
    add_zero, zero_add]
  exact ⟨rfl, rfl⟩

/-- Compare both decompositions on the union of their null supports.
There is no cancellation or subtraction of infinite measure values. -/
theorem positive_decomposition_unique (μ ν a s a' s' : Measure X)
    (heq : ν = a + s) (heq' : ν = a' + s') (ha : a ≪ μ) (ha' : a' ≪ μ)
    (hs : Specs.D11.Ch14.ScalarInterfaces.positiveSingular_value s μ)
    (hs' : Specs.D11.Ch14.ScalarInterfaces.positiveSingular_value s' μ) :
    a = a' ∧ s = s' := by
  obtain ⟨Z, hZ, hsZ, hμZ⟩ := hs
  obtain ⟨B, hB, hsB, hμB⟩ := hs'
  have hm : MeasurableSet (Z ∪ B) := hZ.union hB
  have hn : μ (Z ∪ B) = 0 := measure_union_null hμZ hμB
  have hsW : s (Z ∪ B)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr subset_union_left) hsZ
  have hsW' : s' (Z ∪ B)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr subset_union_right) hsB
  obtain ⟨h1, h2⟩ := parts_from_null_support μ ν a s (Z ∪ B) hm hn hsW heq ha
  obtain ⟨h1', h2'⟩ := parts_from_null_support μ ν a' s' (Z ∪ B) hm hn hsW' heq' ha'
  exact ⟨h1.trans h1'.symm, h2.trans h2'.symm⟩

theorem positive_decomposition :
    Specs.D11.Ch15.LebesgueDecompositionSigmaFinite.positive_decomposition := by
  intro X _ μ ν _ _
  obtain ⟨Z, hZm, hZn, hac⟩ := exists_null_support μ ν
  have hsum : ν = ν.restrict Zᶜ + ν.restrict Z :=
    (Measure.restrict_compl_add_restrict hZm).symm
  have hsing : Specs.D11.Ch14.ScalarInterfaces.positiveSingular_value (ν.restrict Z) μ := by
    refine ⟨Z, hZm, ?_, hZn⟩
    rw [Measure.restrict_apply hZm.compl, compl_inter_self, measure_empty]
  obtain ⟨h, hm, hf, hr⟩ :=
    RNPositiveSigmaFinite.rn_positive_sigmafinite_finite_everywhere μ (ν.restrict Zᶜ) hac
  refine ⟨Z, hZm, hZn, ⟨inferInstance, inferInstance, hsum, hac, hsing, ?_⟩,
    h, hm, hf, hr, ?_⟩
  · intro a s heq ha hs
    exact positive_decomposition_unique μ ν a s (ν.restrict Zᶜ) (ν.restrict Z)
      heq hsum ha hac hs hsing
  · intro k hk hkr
    exact RNPositiveSigmaFinite.density_unique μ (ν.restrict Zᶜ) h k hm hk hr hkr

theorem signed_decomposition :
    Specs.D11.Ch15.LebesgueDecompositionSigmaFinite.signed_decomposition := by
  intro X _ μ _ ν
  obtain ⟨Z, hZ, hdec, _⟩ := LebesgueDecompositionFiniteTarget.signed_decomposition ν μ
  obtain ⟨h, hm, hi, hr⟩ := RNSignedComplex.rn_signed μ (ν.restrict Zᶜ) hdec.2.2.2.1
  exact ⟨Z, hZ.1, hZ.2.1, hdec, h, hm, hi, hr⟩

theorem complex_decomposition :
    Specs.D11.Ch15.LebesgueDecompositionSigmaFinite.complex_decomposition := by
  intro X _ μ _ ν
  obtain ⟨Z, hZ, hdec, _⟩ := LebesgueDecompositionFiniteTarget.complex_decomposition ν μ
  obtain ⟨h, hm, hi, hr⟩ := RNSignedComplex.rn_complex μ (ν.restrict Zᶜ) hdec.2.2.2.1
  exact ⟨Z, hZ.1, hZ.2.1, hdec, h, hm, hi, hr⟩

end D11.Ch15.LebesgueDecompositionSigmaFinite
