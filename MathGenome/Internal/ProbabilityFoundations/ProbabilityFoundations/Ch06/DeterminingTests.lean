import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.Portmanteau
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.RealDistributionFunctions
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.DeterminingTests
import Mathlib.Topology.Algebra.Module.Cardinality

open MeasureTheory Filter Topology Set Metric TopologicalSpace

namespace ProbabilityFoundations.Ch06

universe u
noncomputable section

variable {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-- A separable metric space has a countable base of open continuity balls. -/
theorem exists_countable_continuity_ball_basis [SeparableSpace S]
    (μ : ProbabilityMeasure S) :
    ∃ B : Set (Set S), B.Countable ∧ IsTopologicalBasis B ∧
      ∀ A ∈ B, ∃ (x : S) (r : ℝ), 0 < r ∧ A = ball x r ∧
        IsContinuitySet (μ : Measure S) A := by
  let C : Set (Set S) := {A | ∃ (x : S) (r : ℝ), 0 < r ∧ A = ball x r ∧
    IsContinuitySet (μ : Measure S) A}
  have hC : IsTopologicalBasis C := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro A ⟨x, r, _, rfl, _⟩
      exact isOpen_ball
    · intro x U hx hU
      obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU x hx
      obtain ⟨r, hr, hnull⟩ := exists_continuity_ball_radius (μ : Measure S) x hε
      exact ⟨ball x r, ⟨x, r, hr.1, rfl, hnull⟩, mem_ball_self hr.1,
        (ball_subset_ball hr.2.le).trans hsub⟩
  obtain ⟨B, hBC, hcount, hB⟩ := hC.exists_countable
  exact ⟨B, hcount, hB, hBC⟩

/-- Convergence on finite intersections of basis members determines weak
convergence. In particular it applies to the continuity-ball base above. -/
theorem weaklyConverges_of_basis_intersections [SeparableSpace S]
    (B : Set (Set S)) (hB : IsTopologicalBasis B)
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (h : ∀ F : Finset (Set S), (∀ A ∈ F, A ∈ B) →
      Tendsto (fun n => (μs n : Measure S).real (⋂ A ∈ F, A)) atTop
        (𝓝 ((μ : Measure S).real (⋂ A ∈ F, A)))) :
    WeaklyConverges atTop μs μ := by
  classical
  let C : Set (Set S) := {A | ∃ F : Finset (Set S),
    (∀ U ∈ F, U ∈ B) ∧ (⋂ U ∈ F, U) = A}
  have hC : IsPiSystem C := by
    rintro A ⟨F, hF, rfl⟩ A' ⟨F', hF', rfl⟩ _
    refine ⟨F ∪ F', ?_, ?_⟩
    · intro U hU
      rcases Finset.mem_union.mp hU with hU | hU
      · exact hF U hU
      · exact hF' U hU
    · ext x
      simp [or_imp, forall_and]
  apply hC.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro A ⟨F, hF, rfl⟩
    exact MeasurableSet.biInter (Finset.countable_toSet F)
      (fun U hU => (hB.isOpen (hF U hU)).measurableSet)
  · intro U hU x hx
    obtain ⟨A, hAB, hxA, hAU⟩ := hB.exists_subset_of_mem_open hx hU
    refine ⟨A, ?_, (hB.isOpen hAB).mem_nhds hxA, hAU⟩
    exact ⟨{A}, by simpa using hAB, by simp⟩
  · rintro A ⟨F, hF, rfl⟩
    apply NNReal.tendsto_coe.mp
    simpa using h F hF

open Ch01

/-- Continuity of the CDF forces the boundary mass of the lower half-line
to vanish; its only boundary point is the threshold. -/
lemma measure_singleton_eq_zero_of_continuousAt_distributionFunction
    (μ : ProbabilityMeasure ℝ) (t : ℝ)
    (ht : ContinuousAt (realDistributionFunction (μ : Measure ℝ)) t) :
    (μ : Measure ℝ) {t} = 0 := by
  have hleft := ht.continuousWithinAt.leftLim_eq
  have hatom := realDistributionFunction_atom_mass (μ : Measure ℝ) t
  rw [hleft, sub_self] at hatom
  exact (ENNReal.toReal_eq_zero_iff _).mp hatom |>.resolve_right (measure_ne_top _ _)

/-- For arbitrary real probability laws, weak convergence is exactly CDF
convergence at the continuity points of the limiting CDF. -/
theorem weaklyConverges_iff_distributionFunction
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ) :
    WeaklyConverges atTop μs μ ↔
      ∀ t : ℝ, ContinuousAt (realDistributionFunction (μ : Measure ℝ)) t →
        Tendsto (fun n => realDistributionFunction (μs n : Measure ℝ) t) atTop
          (𝓝 (realDistributionFunction (μ : Measure ℝ) t)) := by
  constructor
  · intro h t ht
    have hnull : (μ : Measure ℝ) (frontier (Iic t)) = 0 := by
      rw [frontier_Iic]
      exact measure_singleton_eq_zero_of_continuousAt_distributionFunction μ t ht
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hnull)
  · intro h
    let D : Set ℝ := {t | ContinuousAt (realDistributionFunction (μ : Measure ℝ)) t}
    have hmono : Monotone (realDistributionFunction (μ : Measure ℝ)) :=
      (realDistributionFunction_properties (μ : Measure ℝ)).1
    have hdense : Dense D := by
      simpa only [D, compl_ofPred, not_not] using
        hmono.countable_not_continuousAt.dense_compl ℝ
    apply (isPiSystem_Ioc_mem D D).tendsto_probabilityMeasure_of_tendsto_of_mem
    · rintro A ⟨a, ha, b, hb, hab, rfl⟩
      exact measurableSet_Ioc
    · intro U hU x hx
      obtain ⟨l, u, ⟨hxl, hxu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
      obtain ⟨a, ha, hla, hax⟩ := hdense.exists_between hxl
      obtain ⟨b, hb, hxb, hbu⟩ := hdense.exists_between hxu
      refine ⟨Ioc a b, ⟨a, ha, b, hb, hax.trans hxb, rfl⟩,
        Ioc_mem_nhds hax hxb, ?_⟩
      exact (fun y hy => hsub ⟨hla.trans hy.1, hy.2.trans_lt hbu⟩)
    · rintro A ⟨a, ha, b, hb, hab, rfl⟩
      apply NNReal.tendsto_coe.mp
      have hi := (h b hb).sub (h a ha)
      simpa only [← realDistributionFunction_interval_mass _ a b hab.le,
        ← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real] using hi

end
end ProbabilityFoundations.Ch06
