import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.JointDistributionDetermination
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.DeterminingClasses
import Mathlib.MeasureTheory.Measure.Dirac.Basic

open Set MeasureTheory

namespace ProbabilityFoundations.Ch01

/-- Binary intersections are obtained by taking the coordinatewise minimum. -/
theorem lowerOrthants_isPiSystem (d : ℕ) : IsPiSystem (range (lowerOrthant d)) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
  refine ⟨fun j => min (x j) (y j), ?_⟩
  ext z
  simp [lowerOrthant, forall_and]

/-- The boxes formed from real closed half-lines are precisely the lower orthants. -/
private theorem boxes_eq_lowerOrthants (d : ℕ) :
    Set.pi univ '' Set.pi univ (fun _ : Fin d => range (Iic : ℝ → Set ℝ)) =
      range (lowerOrthant d) := by
  classical
  ext A
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hex : ∀ j, ∃ x : ℝ, Iic x = s j := fun j => hs j (mem_univ j)
    choose x hx using hex
    refine ⟨x, ?_⟩
    ext y
    simp [lowerOrthant, mem_pi, ← hx]
  · rintro ⟨x, rfl⟩
    refine ⟨fun j => Iic (x j), ?_, ?_⟩
    · intro j _
      exact ⟨x j, rfl⟩
    · ext y
      simp [lowerOrthant, Pi.le_def]

/-- Finite products of half-line generators generate the product Borel structure. -/
theorem borel_eq_generateFrom_lowerOrthants (d : ℕ) :
    borel (Fin d → ℝ) = MeasurableSpace.generateFrom (range (lowerOrthant d)) := by
  have hspan : IsCountablySpanning (range (Iic : ℝ → Set ℝ)) := by
    refine ⟨fun n => Iic (n : ℝ), fun n => ⟨(n : ℝ), rfl⟩, ?_⟩
    ext x
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact exists_nat_ge x
  have hgen := @generateFrom_eq_pi (Fin d) (fun _ => ℝ) _
    (fun _ => inferInstance) (fun _ => range (Iic : ℝ → Set ℝ))
    (fun _ => (borel_eq_generateFrom_Iic (α := ℝ)).symm) (fun _ => hspan)
  rw [boxes_eq_lowerOrthants] at hgen
  exact (BorelSpace.measurable_eq (α := Fin d → ℝ)).symm.trans hgen.symm

/-- The coordinate identification is a Borel measurable equivalence. -/
theorem euclidean_borel_bridge (d : ℕ) :
    (inferInstance : MeasurableSpace (Fin d → ℝ)) = borel (Fin d → ℝ) ∧
    (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d))) =
      borel (EuclideanSpace ℝ (Fin d)) ∧
    borel (EuclideanSpace ℝ (Fin d)) =
      MeasurableSpace.comap (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Fin d → ℝ)
        (borel (Fin d → ℝ)) := by
  refine ⟨BorelSpace.measurable_eq, BorelSpace.measurable_eq, ?_⟩
  rw [← BorelSpace.measurable_eq (α := EuclideanSpace ℝ (Fin d)),
    ← BorelSpace.measurable_eq (α := Fin d → ℝ)]
  rfl

/-- A Borel probability law is determined by all its closed lower-orthant masses. -/
theorem measure_eq_of_lowerOrthants (d : ℕ) (μ ν : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x : Fin d → ℝ, μ (lowerOrthant d x) = ν (lowerOrthant d x)) : μ = ν := by
  apply MeasureTheory.ext_of_generate_finite (range (lowerOrthant d))
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_lowerOrthants d))
    (lowerOrthants_isPiSystem d)
  · rintro A ⟨x, rfl⟩
    exact h x
  · simp

/-- Transport along the measurable coordinate equivalence gives Euclidean uniqueness. -/
theorem measure_eq_of_euclidean_lowerOrthants (d : ℕ)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x : Fin d → ℝ, μ (euclideanLowerOrthant d x) =
      ν (euclideanLowerOrthant d x)) : μ = ν := by
  let e := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
  apply e.map_measurableEquiv_injective
  apply measure_eq_of_lowerOrthants
  intro x
  simpa [e, MeasurableEquiv.map_apply, lowerOrthant, euclideanLowerOrthant] using h x

/-- A zero-dimensional Euclidean probability measure is the Dirac law at its sole point. -/
theorem zero_dimensional_law (μ : Measure (EuclideanSpace ℝ (Fin 0)))
    [IsProbabilityMeasure μ] : μ = Measure.dirac 0 := by
  apply measure_eq_of_euclidean_lowerOrthants
  intro x
  have heq : euclideanLowerOrthant 0 x = univ := by
    ext y
    simp [euclideanLowerOrthant]
  simp [heq]

end ProbabilityFoundations.Ch01
