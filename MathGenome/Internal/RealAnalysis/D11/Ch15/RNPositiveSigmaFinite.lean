import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.RNPositiveSigmaFinite
import MathGenome.Internal.RealAnalysis.D11.Ch15.RNPositiveFinite
import MathGenome.Internal.RealAnalysis.D11.Ch01.ExhaustionRestriction
import MathGenome.Internal.RealAnalysis.D11.Ch05.MonotoneSeries

/-! Sigma-finite positive RN, `paper.tex:4861–4874`.
Apply the upstream finite theorem to the restrictions on a common disjoint
finite-mass partition. The sum of the densities extended by zero is measurable
and finite everywhere, since at each point at most one summand is nonzero.
Countable additivity for restrictions and for density measures reconstructs ν.
No global L¹ hypothesis, completion, or RN existence theorem from Mathlib is
used in this passage from finite to sigma-finite measures. -/

open Set Filter MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace D11.Ch15.RNPositiveSigmaFinite

/-- A common partition on which both measures are finite. -/
theorem common_finite_partition {X : Type u} [MeasurableSpace X]
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] :
    ∃ A : ℕ → Set X, (∀ n, MeasurableSet (A n) ∧ μ (A n) < ∞ ∧ ν (A n) < ∞) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧ (⋃ n, A n) = univ := by
  obtain ⟨A, hA, hdis, hcover⟩ :=
    (Ch01.ExhaustionRestriction.sigmaFinite_iff_disjoint_partition (μ + ν)).mp inferInstance
  refine ⟨A, fun n => ⟨(hA n).1, ?_, ?_⟩, hdis, hcover⟩
  · exact (le_add_right le_rfl : μ (A n) ≤ μ (A n) + ν (A n)).trans_lt (hA n).2
  · exact (le_add_left le_rfl : ν (A n) ≤ μ (A n) + ν (A n)).trans_lt (hA n).2

theorem rn_positive_sigmafinite_finite_everywhere :
    Specs.D11.Ch15.RNPositiveSigmaFinite.rn_positive_sigmafinite_finite_everywhere := by
  intro X _ μ ν _ _ hac
  obtain ⟨A, hA, hdis, hcover⟩ := common_finite_partition μ ν
  have hlocal (n : ℕ) : ∃ h : X → ℝ≥0∞, Measurable h ∧ (∀ x, h x < ∞) ∧
      (μ.restrict (A n)).withDensity h = ν.restrict (A n) := by
    let : IsFiniteMeasure (μ.restrict (A n)) := isFiniteMeasure_restrict.mpr (hA n).2.1.ne
    let : IsFiniteMeasure (ν.restrict (A n)) := isFiniteMeasure_restrict.mpr (hA n).2.2.ne
    obtain ⟨h, hh, hfin, _, hrep⟩ :=
      RNPositiveFinite.rn_positive_finite (μ.restrict (A n)) (ν.restrict (A n))
        (hac.restrict (A n))
    refine ⟨h, hh, hfin, ?_⟩
    ext E hE
    rw [withDensity_apply _ hE, hrep E hE]
    exact (Ch05.NonnegativeIntegral.integral_eq_lintegral _ h).symm
  choose h hm hf hrep using hlocal
  let f : ℕ → X → ℝ≥0∞ := fun n => (A n).indicator (h n)
  have hfm (n : ℕ) : Measurable (f n) := (hm n).indicator (hA n).1
  let g : X → ℝ≥0∞ := ∑' n, f n
  have hgm : Measurable g := Measurable.tsum' hfm
  have hgfin (x : X) : g x < ∞ := by
    have hx : x ∈ ⋃ n, A n := hcover.symm ▸ mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hsingle : g x = h n x := by
      change (∑' n, f n) x = h n x
      rw [Pi.tsum_apply (Pi.summable.mpr (fun _ => ENNReal.summable))]
      rw [tsum_eq_single n]
      · exact indicator_of_mem hn _
      · intro m hmn
        exact indicator_of_notMem (fun hx => Set.disjoint_left.mp (hdis hmn) hx hn) _
    rw [hsingle]
    exact hf n x
  have hgrec : μ.withDensity g = ν := by
    rw [withDensity_tsum hfm]
    simp_rw [f, withDensity_indicator (hA _).1, hrep]
    rw [← Measure.restrict_iUnion hdis (fun n => (hA n).1), hcover,
      Measure.restrict_univ]
  refine ⟨g, hgm, hgfin, fun E hE => ?_⟩
  change ν E = Ch05.NonnegativeIntegral.nonnegativeIntegral (μ.restrict E) g
  rw [Ch05.NonnegativeIntegral.integral_eq_lintegral, ← withDensity_apply _ hE, hgrec]

theorem rn_positive_sigmafinite :
    Specs.D11.Ch15.RNPositiveSigmaFinite.rn_positive_sigmafinite := by
  intro X _ μ ν _ _ hac
  obtain ⟨h, hm, hf, hr⟩ := rn_positive_sigmafinite_finite_everywhere μ ν hac
  exact ⟨h, hm, Eventually.of_forall hf, hr⟩

theorem density_unique : Specs.D11.Ch15.RNPositiveSigmaFinite.density_unique := by
  intro X _ μ ν _ _ h k hh hk hrep krep
  have hdensity : μ.withDensity h = ν := by
    ext E hE
    rw [withDensity_apply _ hE, hrep E hE]
    exact (Ch05.NonnegativeIntegral.integral_eq_lintegral (μ.restrict E) h).symm
  have kdensity : μ.withDensity k = ν := by
    ext E hE
    rw [withDensity_apply _ hE, krep E hE]
    exact (Ch05.NonnegativeIntegral.integral_eq_lintegral (μ.restrict E) k).symm
  exact (withDensity_eq_iff_of_sigmaFinite hh.aemeasurable hk.aemeasurable).mp
    (hdensity.trans kdensity.symm)

theorem rn_positive_sigmafinite_real :
    Specs.D11.Ch15.RNPositiveSigmaFinite.rn_positive_sigmafinite_real := by
  intro X _ μ ν _ _ hac
  obtain ⟨h, hm, hf, hrep⟩ := rn_positive_sigmafinite_finite_everywhere μ ν hac
  refine ⟨fun x => (h x).toReal, hm.ennreal_toReal,
    fun x => ENNReal.toReal_nonneg, ?_⟩
  have hrecover : (fun x => ENNReal.ofReal (h x).toReal) = h :=
    funext fun x => ENNReal.ofReal_toReal (hf x).ne
  simpa only [hrecover] using hrep

end D11.Ch15.RNPositiveSigmaFinite
