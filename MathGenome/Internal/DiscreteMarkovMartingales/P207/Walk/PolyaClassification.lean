import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.PolyaClassification
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.LatticeFourier
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.SpectralDivergence
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.SpectralFiniteness
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.GreenCriterion
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory
open scoped ENNReal MeasureTheory BigOperators

namespace P207.Walk.PolyaClassification
noncomputable section

/-- Time marginals of the explicit independent-increment construction. -/
theorem iidWalk_mass {d : ℕ} [NeZero d] (x y : Lattice d) (n : ℕ) :
    incrementMeasure d {ω | iidWalk x ω n = y} =
      Markov.power (latticeKernel d) n x y := by
  have h := congrArg (fun μ : Measure (Lattice d) => μ {y})
    (LatticeFourier.canonical_marginal d x n)
  rw [← LatticeFourier.iidWalk_pathLaw d x,
    Measure.map_map (measurable_pi_apply n) (LatticeFourier.measurable_iidWalk x),
    Measure.map_apply ((measurable_pi_apply n).comp (LatticeFourier.measurable_iidWalk x))
      (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h
  exact h

theorem power_translation : PolyaClassificationSpec.power_translation := by
  intro d _ n a x y
  rw [← iidWalk_mass, ← iidWalk_mass]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, iidWalk, add_assoc, add_right_inj]

/-- The return event itself is invariant, not just its classification. -/
theorem firstReturn_translation : PolyaClassificationSpec.firstReturn_translation := by
  intro d _ x
  change latticePathLaw d x {ω | Markov.returnTime x ω < ⊤} =
    latticePathLaw d 0 {ω | Markov.returnTime 0 ω < ⊤}
  rw [← LatticeFourier.iidWalk_pathLaw d x, ← LatticeFourier.iidWalk_pathLaw d 0,
    Measure.map_apply (LatticeFourier.measurable_iidWalk x)
      (Markov.measurableSet_returnTime_finite x),
    Measure.map_apply (LatticeFourier.measurable_iidWalk 0)
      (Markov.measurableSet_returnTime_finite 0)]
  congr 1
  ext ω
  change Markov.positiveReturnTime Markov.coordinate x (iidWalk x ω) < ⊤ ↔
    Markov.positiveReturnTime Markov.coordinate 0 (iidWalk 0 ω) < ⊤
  rw [Markov.positiveReturnTime_finite_iff, Markov.positiveReturnTime_finite_iff]
  simp [Markov.coordinate, iidWalk]

theorem diagonal_power {d : ℕ} [NeZero d] (n : ℕ) (x : Lattice d) :
    Markov.power (latticeKernel d) n x x = returnProbability d n := by
  simpa only [returnProbability, add_zero] using power_translation d n x 0 0

theorem greenSeries_translation {d : ℕ} [NeZero d] (x : Lattice d) :
    Markov.greenSeries (latticeKernel d) x =
      Markov.greenSeries (latticeKernel d) 0 := by
  unfold Markov.greenSeries
  exact tsum_congr (fun n => (diagonal_power n x).trans (diagonal_power n 0).symm)

theorem continuous_phi {d : ℕ} : Continuous (phi (d := d)) := by
  unfold phi
  exact continuous_const.mul (continuous_finsetSum _ fun j _ =>
    Real.Angle.continuous_cos.comp (continuous_apply j))

theorem abs_phi_le_one {d : ℕ} [NeZero d] (t : Torus d) : |phi t| ≤ 1 := by
  calc
    |phi t| = (d : ℝ)⁻¹ * |∑ j : Fin d, Real.Angle.cos (t j)| := by
      rw [phi, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (d : ℝ)⁻¹)]
    _ ≤ (d : ℝ)⁻¹ * ∑ j : Fin d, |Real.Angle.cos (t j)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (d : ℝ)⁻¹ * ∑ _j : Fin d, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun j _ => abs_le.mpr
        ⟨LatticeLocalBounds.neg_one_le_angle_cos (t j), LatticeLocalBounds.angle_cos_le_one (t j)⟩)
    _ = 1 := by simp [NeZero.ne d]

theorem returnProbability_even_lintegral {d : ℕ} [NeZero d] (n : ℕ) :
    returnProbability d (2 * n) =
      ∫⁻ t : Torus d, ENNReal.ofReal (phi t ^ (2 * n)) ∂torusMeasure d := by
  have hi : Integrable (fun t : Torus d => phi t ^ (2 * n)) (torusMeasure d) :=
    Integrable.of_bound (continuous_phi.pow _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_pow]
        simpa using pow_le_pow_left₀ (abs_nonneg (phi t)) (abs_phi_le_one t) (2 * n))
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun t => Even.pow_nonneg (even_two_mul n) (phi t)),
    ← LatticeFourier.fourier_return]
  exact (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm

theorem greenSeries_even {d : ℕ} [NeZero d] (x : Lattice d) :
    Markov.greenSeries (latticeKernel d) x = ∑' n : ℕ, returnProbability d (2 * n) := by
  unfold Markov.greenSeries
  simp_rw [diagonal_power]
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  have ho : ∀ n : ℕ, returnProbability d (2 * n + 1) = 0 :=
    fun n => LatticeFourier.odd_return d (2 * n + 1) ⟨n, rfl⟩
  simp_rw [ho]
  simp

theorem green_integral : PolyaClassificationSpec.green_integral := by
  intro d _ x
  rw [greenSeries_even]
  simp_rw [returnProbability_even_lintegral]
  rw [← lintegral_tsum (f := fun n (t : Torus d) => ENNReal.ofReal (phi t ^ (2 * n)))
    (fun n => ((continuous_phi (d := d)).pow (2 * n)).measurable.ennreal_ofReal.aemeasurable)]
  apply lintegral_congr
  intro t
  simp_rw [pow_mul, ENNReal.ofReal_pow (sq_nonneg (phi t))]
  rw [ENNReal.tsum_geometric, ENNReal.ofReal_sub 1 (sq_nonneg (phi t)), ENNReal.ofReal_one]

/-- Classification of every state, with recurrence defined by first positive return. -/
theorem recurrent_iff : PolyaClassificationSpec.recurrent_iff := by
  intro d _ x
  rw [Markov.recurrent_iff_greenSeries_eq_top, green_integral d x]
  constructor
  · intro h
    by_contra hd
    have hpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    exact (ne_of_lt (SpectralFiniteness.spectral_finiteness d (by omega))) h
  · exact SpectralDivergence.divergence d

theorem transient_iff : PolyaClassificationSpec.transient_iff := by
  intro d _ x
  rw [Markov.transient_iff_not_recurrent, recurrent_iff d x]
  have hpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  omega

end
end P207.Walk.PolyaClassification
