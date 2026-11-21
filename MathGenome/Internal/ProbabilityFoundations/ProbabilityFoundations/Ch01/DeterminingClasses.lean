import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.DeterminingClasses

/-! Determining classes for finite measures, and the resulting integral identities. -/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace ProbabilityFoundations.Ch01

/-- Finite-subfamily closure implies Mathlib's pi-system condition. -/
private theorem isPiSystem_of_finite_intersections {S : Type u} {C : Set (Set S)}
    (hC : ∀ F : Set (Set S), F.Finite → F.Nonempty → F ⊆ C → ⋂₀ F ∈ C) :
    IsPiSystem C := by
  intro A hA B hB _
  have hfinite : ({A, B} : Set (Set S)).Finite := Set.toFinite _
  have hnonempty : ({A, B} : Set (Set S)).Nonempty := ⟨A, by simp⟩
  have hsubset : ({A, B} : Set (Set S)) ⊆ C := by
    intro D hD
    rcases Set.mem_insert_iff.mp hD with rfl | hD
    · exact hA
    · exact Set.mem_singleton_iff.mp hD ▸ hB
  simpa using hC {A, B} hfinite hnonempty hsubset

/-- A determining class and equal finite total masses determine the measure. -/
theorem measure_eq_of_determining_class
    (S : Type u) [m : MeasurableSpace S] (C : Set (Set S))
    (hgen : m = MeasurableSpace.generateFrom C)
    (hC : ∀ F : Set (Set S), F.Finite → F.Nonempty → F ⊆ C → ⋂₀ F ∈ C)
    (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) (hagree : ∀ A ∈ C, μ A = ν A) : μ = ν := by
  exact MeasureTheory.ext_of_generate_finite C hgen
    (isPiSystem_of_finite_intersections hC) hagree hmass

/-- The nonnegative integral identity includes functions with infinite values or integral. -/
theorem lintegral_eq_of_determining_class
    (S : Type u) [m : MeasurableSpace S] (C : Set (Set S))
    (hgen : m = MeasurableSpace.generateFrom C)
    (hC : ∀ F : Set (Set S), F.Finite → F.Nonempty → F ⊆ C → ⋂₀ F ∈ C)
    (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) (hagree : ∀ A ∈ C, μ A = ν A)
    (f : S → ℝ≥0∞) (_hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ∫⁻ x, f x ∂ν := by
  rw [measure_eq_of_determining_class S C hgen hC μ ν hmass hagree]

/-- The real integral identity, with integrability under either measure. -/
theorem integral_real_eq_of_determining_class
    (S : Type u) [m : MeasurableSpace S] (C : Set (Set S))
    (hgen : m = MeasurableSpace.generateFrom C)
    (hC : ∀ F : Set (Set S), F.Finite → F.Nonempty → F ⊆ C → ⋂₀ F ∈ C)
    (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) (hagree : ∀ A ∈ C, μ A = ν A)
    (f : S → ℝ) (_hf : Integrable f μ ∨ Integrable f ν) :
    (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  rw [measure_eq_of_determining_class S C hgen hC μ ν hmass hagree]

/-- The complex integral identity, with integrability under either measure. -/
theorem integral_complex_eq_of_determining_class
    (S : Type u) [m : MeasurableSpace S] (C : Set (Set S))
    (hgen : m = MeasurableSpace.generateFrom C)
    (hC : ∀ F : Set (Set S), F.Finite → F.Nonempty → F ⊆ C → ⋂₀ F ∈ C)
    (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) (hagree : ∀ A ∈ C, μ A = ν A)
    (f : S → ℂ) (_hf : Integrable f μ ∨ Integrable f ν) :
    (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  rw [measure_eq_of_determining_class S C hgen hC μ ν hmass hagree]

end ProbabilityFoundations.Ch01
