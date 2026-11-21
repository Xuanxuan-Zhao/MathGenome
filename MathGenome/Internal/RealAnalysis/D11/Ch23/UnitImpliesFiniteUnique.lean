import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.UnitImpliesFiniteUnique
import MathGenome.Internal.RealAnalysis.D11.Ch23.DaniellStoneRepresentation
import MathGenome.Internal.RealAnalysis.D11.Ch23.GeneratedRingAlgebra

/-! A constant unit gives full uniqueness and finite mass (paper.tex:6304–6311).
Whole-space membership is used only for equality of the generated domains;
integrability of the unit supplies finiteness separately.
-/

open Set MeasureTheory
universe u

namespace D11.Ch23.UnitImpliesFiniteUnique

theorem unit_univ_mem :
    _root_.Specs.D11.Ch23.UnitImpliesFiniteUnique.unit_univ_mem := by
  intro X V hunit
  change (univ : Set X) ∈ positiveLevelSigmaRing V
  have h := positiveLevel_mem_sigmaRing V (fun _ : X => (1 : ℝ)) hunit
    (1 / 2) (by norm_num)
  have hlevel : {x : X | (1 / 2 : ℝ) < 1} = univ := by
    ext x
    norm_num
  rw [hlevel] at h
  exact h

theorem sigmaRing_eq_measurableSets_of_univ :
    _root_.Specs.D11.Ch23.UnitImpliesFiniteUnique.sigmaRing_eq_measurableSets_of_univ := by
  intro X V huniv
  ext A
  constructor
  · exact sigmaRing_sets_measurable V A
  · intro hA
    refine MeasurableSpace.generateFrom_induction (Specs.positiveLevelFamily V)
      (fun B _ => B ∈ Specs.positiveLevelSigmaRing V)
      (fun _ hB _ => subset_generatedSigmaRing _ hB)
      (Specs.positiveLevelSigmaRing V).empty_mem ?_
      (fun B _ hB => (Specs.positiveLevelSigmaRing V).iUnion_mem B hB) A hA
    intro B _ hB
    rw [compl_eq_univ_sdiff]
    exact (Specs.positiveLevelSigmaRing V).diff_mem huniv hB

theorem full_uniqueness_of_univ :
    _root_.Specs.D11.Ch23.UnitImpliesFiniteUnique.full_uniqueness_of_univ := by
  intro X V hV hStone L hL huniv
  letI : MeasurableSpace X := positiveLevelMeasurableSpace V
  intro μ ν hμ hν
  obtain ⟨ρ, _, hρ⟩ :=
    DaniellStoneRepresentation.daniell_stone_representation V hV hStone L hL
  apply Measure.ext
  intro A hA
  have hAr : A ∈ Specs.positiveLevelSigmaRing V := by
    change A ∈ (Specs.positiveLevelSigmaRing V : Set (Set X))
    rw [sigmaRing_eq_measurableSets_of_univ V huniv]
    exact hA
  exact (hρ μ hμ A hAr).symm.trans (hρ ν hν A hAr)

theorem unit_mass :
    _root_.Specs.D11.Ch23.UnitImpliesFiniteUnique.unit_mass := by
  intro X V L hunit
  letI : MeasurableSpace X := positiveLevelMeasurableSpace V
  intro μ hμ
  have hi : Integrable (fun _ : X => (1 : ℝ)) μ := (hμ ⟨_, hunit⟩).1
  have hfinite : IsFiniteMeasure μ :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp hi
  letI := hfinite
  have hreal : μ.real univ = L ⟨fun _ => 1, hunit⟩ := by
    simpa only [integral_const, smul_eq_mul, mul_one] using (hμ ⟨_, hunit⟩).2
  have hmass : μ univ = ENNReal.ofReal (L ⟨fun _ => 1, hunit⟩) := by
    rw [← hreal, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ univ)]
  refine ⟨hfinite, hmass, hreal, ?_⟩
  intro hnorm
  exact ⟨by simpa only [hnorm, ENNReal.ofReal_one] using hmass⟩

theorem unit_implies_finite_unique :
    _root_.Specs.D11.Ch23.UnitImpliesFiniteUnique.unit_implies_finite_unique := by
  intro X V hV hStone L hL hunit
  letI : MeasurableSpace X := positiveLevelMeasurableSpace V
  obtain ⟨μ, hμ, _⟩ :=
    DaniellStoneRepresentation.daniell_stone_representation V hV hStone L hL
  have hrepr := fun f => (hμ f).2
  obtain ⟨hfinite, hmass, _, hprob⟩ := unit_mass V L hunit μ hrepr
  refine ⟨μ, hμ, hfinite, hmass, hprob, ?_⟩
  intro ν hν
  exact full_uniqueness_of_univ V hV hStone L hL (unit_univ_mem V hunit) ν μ hν hrepr

end D11.Ch23.UnitImpliesFiniteUnique
