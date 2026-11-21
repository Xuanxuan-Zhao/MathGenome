import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.MaximalAdmissibleDensity
import MathGenome.Internal.RealAnalysis.D11.Ch15.AbsoluteContinuity
import MathGenome.Internal.RealAnalysis.D11.Ch05.DensityMeasureDomains
import MathGenome.Internal.RealAnalysis.D11.Ch05.MonotoneSeries
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-! The maximizing-density stage of the finite positive RN proof.

Finite maxima stay admissible by the measurable comparison partition. A
sequence approaching the supremum of total integrals is replaced by successive
finite maxima, then monotone convergence gives an admissible maximizer.
Subtracting its density measure from the finite target gives the residual.
The residual is not assumed zero, and neither RN reconstruction nor uniqueness
is used. The reference measure may even be arbitrary in the intermediate lemmas.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u
noncomputable section
namespace D11.Ch15.MaximalAdmissibleDensity

open Measure.LebesgueDecomposition

/-- The accepted source integral and the native lower integral agree here. -/
theorem admissible_iff_source :
    Specs.D11.Ch15.MaximalAdmissibleDensity.admissible_iff_source := by
  intro X _ μ ν g
  change admissible μ ν g ↔ Measurable g ∧ ∀ E, MeasurableSet E →
    Ch05.NonnegativeIntegral.nonnegativeIntegral (μ.restrict E) g ≤ ν E
  simp only [admissible, Ch05.NonnegativeIntegral.integral_eq_lintegral]

/-- Identification with the library family checks both its measurability
condition and all of its measurable-set inequalities. -/
lemma admissible_iff_mem {X : Type u} [MeasurableSpace X]
    (μ ν : Measure X) (g : X → ℝ≥0∞) :
    admissible μ ν g ↔ g ∈ measurableLE μ ν := Iff.rfl

theorem zero_admissible :
    Specs.D11.Ch15.MaximalAdmissibleDensity.zero_admissible := by
  intro X _ μ ν
  exact zero_mem_measurableLE

theorem max_admissible :
    Specs.D11.Ch15.MaximalAdmissibleDensity.max_admissible := by
  intro X _ μ ν f g hf hg
  exact sup_mem_measurableLE hf hg

theorem finite_max_admissible :
    Specs.D11.Ch15.MaximalAdmissibleDensity.finite_max_admissible := by
  intro X _ ι μ ν s f
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using zero_admissible μ ν
  | @insert i s hi ih =>
      intro hf
      have hrest := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hhead := hf i (Finset.mem_insert_self i s)
      simpa only [Finset.sup_insert] using
        max_admissible μ ν (f i) (fun x => s.sup (fun j => f j x)) hhead hrest

theorem supremum_bound :
    Specs.D11.Ch15.MaximalAdmissibleDensity.supremum_bound := by
  intro X _ μ ν
  apply sSup_le
  rintro a ⟨g, hg, rfl⟩
  simpa only [Measure.restrict_univ] using hg.2 univ MeasurableSet.univ

/-- The supremum used here is exactly the set of all admissible integrals. -/
lemma supremumIntegral_eq {X : Type u} [MeasurableSpace X] (μ ν : Measure X) :
    supremumIntegral μ ν = sSup (measurableLEEval μ ν) := rfl

/-- Countable approximation and monotone convergence give attainment without
requiring the reference measure to be finite or the target to be AC. -/
theorem exists_maximizer :
    Specs.D11.Ch15.MaximalAdmissibleDensity.exists_maximizer := by
  intro X _ μ ν _
  have hs := exists_seq_tendsto_sSup
    (S := measurableLEEval μ ν)
    ⟨0, 0, zero_mem_measurableLE, by simp⟩ (OrderTop.bddAbove _)
  choose a _ ha f hf hfa using hs
  let F : ℕ → X → ℝ≥0∞ := fun n x => ⨆ k, ⨆ (_ : k ≤ n), f k x
  have hF (n : ℕ) : admissible μ ν (F n) := iSup_mem_measurableLE f hf n
  have hm : Monotone F := iSup_monotone f
  let h : X → ℝ≥0∞ := fun x => ⨆ n, F n x
  have hh : Measurable h := Measurable.iSup (fun n => (hF n).1)
  have hE (E : Set X) (hE : MeasurableSet E) : (∫⁻ x in E, h x ∂μ) ≤ ν E := by
    rw [show (∫⁻ x in E, h x ∂μ) = ⨆ n, ∫⁻ x in E, F n x ∂μ from
      lintegral_iSup (fun n => (hF n).1) hm]
    exact iSup_le fun n => (hF n).2 E hE
  have h_adm : admissible μ ν h := ⟨hh, hE⟩
  have hmax : (∫⁻ x, h x ∂μ) = supremumIntegral μ ν := by
    have hconv : Tendsto (fun n => ∫⁻ x, F n x ∂μ) atTop
        (𝓝 (sSup (measurableLEEval μ ν))) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le ha tendsto_const_nhds ?_ ?_
      · intro n
        rw [← hfa n]
        exact lintegral_mono (iSup_le_le f n n le_rfl)
      · intro n
        exact le_sSup ⟨F n, hF n, rfl⟩
    have hlim : Tendsto (fun n => ∫⁻ x, F n x ∂μ) atTop (𝓝 (∫⁻ x, h x ∂μ)) := by
      apply lintegral_tendsto_of_tendsto_of_monotone
        (fun n => (hF n).1.aemeasurable)
      · exact Eventually.of_forall fun x i j hij => hm hij x
      · exact Eventually.of_forall fun x =>
          tendsto_atTop_iSup (fun i j hij => hm hij x)
    exact (tendsto_nhds_unique hlim hconv).trans (supremumIntegral_eq μ ν).symm
  have hfin : (∫⁻ x, h x ∂μ) < ∞ :=
    lt_of_le_of_lt (by simpa using hE univ MeasurableSet.univ) (measure_lt_top ν univ)
  exact ⟨h, h_adm, hmax, ae_lt_top hh hfin.ne⟩

/-- The setwise domination needed to make subtraction an actual difference. -/
lemma density_le {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    (h : X → ℝ≥0∞) (hh : admissible μ ν h) : μ.withDensity h ≤ ν := by
  apply Measure.le_intro
  intro E hE _
  rw [withDensity_apply _ hE]
  exact hh.2 E hE

theorem residual_properties :
    Specs.D11.Ch15.MaximalAdmissibleDensity.residual_properties := by
  intro X _ μ ν _ h hh hac
  have hle : μ.withDensity h ≤ ν := density_le μ ν h hh
  let : IsFiniteMeasure (μ.withDensity h) := isFiniteMeasure_of_le ν hle
  change IsFiniteMeasure (ν - μ.withDensity h) ∧ (ν - μ.withDensity h) ≪ μ ∧
    (∀ E, MeasurableSet E →
      (ν - μ.withDensity h) E = ν E - ∫⁻ x in E, h x ∂μ) ∧
    ν - μ.withDensity h + μ.withDensity h = ν
  refine ⟨inferInstance, Measure.absolutelyContinuous_of_le Measure.sub_le |>.trans hac, ?_,
    Measure.sub_add_cancel_of_le hle⟩
  intro E hE
  rw [Measure.sub_apply hE hle, withDensity_apply _ hE]

theorem maximal_admissible_density :
    Specs.D11.Ch15.MaximalAdmissibleDensity.maximal_admissible_density := by
  intro X _ μ ν _ _ hac
  obtain ⟨h, hh, hmax, hfin⟩ := exists_maximizer μ ν
  obtain ⟨hrfin, hrac, hrapply, hradd⟩ := residual_properties μ ν h hh hac
  exact ⟨h, hh, hmax, supremum_bound μ ν, hfin, hrfin, hrac, hrapply, hradd⟩

end D11.Ch15.MaximalAdmissibleDensity
