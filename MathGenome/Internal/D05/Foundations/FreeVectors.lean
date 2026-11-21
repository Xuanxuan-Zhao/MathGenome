import MathGenome.Internal.D05.M03.LinearMap
import MathGenome.Internal.Specs.D05.Foundations.FreeVectors

/-! The free vector construction and its universal property (paper.tex:350). -/

namespace D05.Foundations.FreeVectors

open scoped BigOperators

/-- The delta vector at an index in the canonical free vector space `S →₀ K`. -/
noncomputable def delta (K S : Type*) [Field K] (s : S) : S →₀ K :=
  Finsupp.single s 1

theorem pointwise_operations : Specs.D05.Foundations.FreeVectors.pointwise_operations := by
  intro K S _ a b r s
  exact ⟨rfl, rfl⟩

theorem delta_coordinates : Specs.D05.Foundations.FreeVectors.delta_coordinates := by
  intro K S _ s
  exact ⟨Finsupp.single_eq_same, fun t ht => Finsupp.single_eq_of_ne ht⟩

theorem support_expansion : Specs.D05.Foundations.FreeVectors.support_expansion := by
  intro K S _ a
  simpa only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one]
    using (Finsupp.sum_single a).symm

theorem coefficient_recovery : Specs.D05.Foundations.FreeVectors.coefficient_recovery := by
  intro K S _ c s
  exact congrArg (fun a : S →₀ K => a s) (support_expansion c).symm

theorem unique_coefficients : Specs.D05.Foundations.FreeVectors.unique_coefficients := by
  intro K S _ a
  refine ⟨a, support_expansion a, ?_⟩
  intro c hc
  apply Finsupp.ext
  intro s
  calc
    c s = (∑ t ∈ c.support, c t • Finsupp.single t (1 : K)) s :=
      (coefficient_recovery c s).symm
    _ = a s := congrArg (fun b : S →₀ K => b s) hc.symm

/-- The linear extension sends a finite coefficient family to its linear combination. -/
noncomputable def linearExtension (K S W : Type*) [Field K]
    [AddCommGroup W] [Module K W] (f : S → W) : (S →₀ K) →ₗ[K] W :=
  Finsupp.linearCombination K f

theorem linearExtension_apply : Specs.D05.Foundations.FreeVectors.linearExtension_apply := by
  intro K S W _ _ _ f a
  rfl

theorem linearExtension_delta : Specs.D05.Foundations.FreeVectors.linearExtension_delta := by
  intro K S W _ _ _ f s
  simp only [Finsupp.linearCombination_single, one_smul]

theorem extension_formula : Specs.D05.Foundations.FreeVectors.extension_formula := by
  intro K S W _ _ _ f T hT a
  calc
    T a = T (∑ s ∈ a.support, a s • Finsupp.single s (1 : K)) :=
      congrArg T (support_expansion a)
    _ = ∑ s ∈ a.support, a s • T (Finsupp.single s (1 : K)) :=
      D05.M03.LinearMap.map_finite_combination T a.support a (fun s => Finsupp.single s 1)
    _ = ∑ s ∈ a.support, a s • f s := by
      simp only [hT]

theorem unique_linear_extension : Specs.D05.Foundations.FreeVectors.unique_linear_extension := by
  intro K S W _ _ _ f
  refine ⟨linearExtension K S W f, linearExtension_delta f, ?_⟩
  intro T hT
  apply LinearMap.ext
  intro a
  exact (extension_formula f T hT a).trans (linearExtension_apply f a).symm

end D05.Foundations.FreeVectors
