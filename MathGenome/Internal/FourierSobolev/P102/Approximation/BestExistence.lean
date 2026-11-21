import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.BestExistence
import Mathlib.Tactic.Linarith

noncomputable section

namespace P102.Approximation

theorem polynomialSpace_characterization :
    Specs.P102.Approximation.BestExistence.SpaceCharacterization := by
  intro a b n g
  simp only [polynomialSpace, Submodule.mem_map, Polynomial.mem_degreeLE]
  rfl

theorem polynomialSpace_finiteDimensional :
    Specs.P102.Approximation.BestExistence.SpaceFiniteDimensional := by
  intro a b n
  apply Module.Finite.of_fg
  apply Submodule.FG.map
  rw [Polynomial.degreeLE_eq_span_X_pow]
  exact Submodule.fg_span (Finset.finite_toSet _)

theorem uniformNorm_attained :
    Specs.P102.Approximation.BestExistence.UniformNormAttained := by
  intro a b hab g
  have : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set (Set.Icc a b)).Nonempty)
    g.continuous.norm.continuousOn
  refine ⟨x, ?_, fun y => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm y⟩
  apply le_antisymm
  · simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x
  · apply (ContinuousMap.norm_le _ (abs_nonneg _)).mpr
    intro y
    simpa only [Real.norm_eq_abs] using (show ‖g y‖ ≤ ‖g x‖ from hx (Set.mem_univ y))

/-- A finite dimensional subspace of a real normed space contains a nearest point.
Minimize on the closed ball of radius `2 * ‖f‖`; outside it the error is at least
that of the zero polynomial. -/
theorem exists_nearest_in_finiteDimensional_subspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) [FiniteDimensional ℝ S] (f : E) :
    ∃ p : S, ∀ q : S, ‖f - (p : E)‖ ≤ ‖f - (q : E)‖ := by
  have hzero : (0 : S) ∈ Metric.closedBall (0 : S) (2 * ‖f‖) := by
    simp only [Metric.mem_closedBall, dist_self]
    positivity
  have hc : Continuous (fun q : S => ‖f - (q : E)‖) :=
    (continuous_const.sub continuous_subtype_val).norm
  obtain ⟨p, hp, hmin⟩ := (isCompact_closedBall (0 : S) (2 * ‖f‖)).exists_isMinOn
    ⟨0, hzero⟩ hc.continuousOn
  refine ⟨p, fun q => ?_⟩
  by_cases hq : q ∈ Metric.closedBall (0 : S) (2 * ‖f‖)
  · exact hmin hq
  · have hp0 : ‖f - (p : E)‖ ≤ ‖f‖ := by
      simpa only [Submodule.coe_zero, sub_zero] using (show ‖f - (p : E)‖ ≤ ‖f - ((0 : S) : E)‖ from hmin hzero)
    have hqnorm : 2 * ‖f‖ < ‖(q : E)‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le, Submodule.norm_coe] using hq
    have htri := norm_sub_norm_le (q : E) f
    rw [norm_sub_rev] at htri
    linarith

theorem bestPolynomial_exists :
    Specs.P102.Approximation.BestExistence.BestExists := by
  intro a b hab f n
  let S := polynomialSpace a b n
  have : FiniteDimensional ℝ S := polynomialSpace_finiteDimensional a b n
  obtain ⟨g, hg⟩ := exists_nearest_in_finiteDimensional_subspace S f
  obtain ⟨p, hp, hpg⟩ := (polynomialSpace_characterization a b n g).mp g.property
  have hleast : ∀ q : Polynomial ℝ, q.degree ≤ (n : WithBot ℕ) →
      ‖f - p.toContinuousMapOn (Set.Icc a b)‖ ≤
        ‖f - q.toContinuousMapOn (Set.Icc a b)‖ := by
    intro q hq
    have hmem : q.toContinuousMapOn (Set.Icc a b) ∈ S :=
      (polynomialSpace_characterization a b n _).mpr ⟨q, hq, rfl⟩
    simpa only [hpg] using hg ⟨_, hmem⟩
  refine ⟨p, hp, ?_, hleast⟩
  symm
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨_, p, hp, rfl⟩
  · rintro r ⟨q, hq, rfl⟩
    exact hleast q hq
  · intro r hr
    exact ⟨_, ⟨p, hp, rfl⟩, hr⟩

end P102.Approximation
