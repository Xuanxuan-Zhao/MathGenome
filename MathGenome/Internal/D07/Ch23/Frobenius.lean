import MathGenome.Internal.Specs.D07.Ch23.Frobenius
import MathGenome.Internal.D07.Ch23.FrobeniusAnticommutingDecomposition
import Mathlib.RingTheory.Algebraic.Integral

/-! The final assembly of Frobenius's theorem. The preceding goals construct
the complex subfield and its centralizer, then prove the complex/quaternion
alternative using the anticommuting subspace. Distinct real dimensions give
uniqueness, and no finite-dimensional premise is added to that argument. -/

noncomputable section
universe u
namespace D07.Ch23.Frobenius

open Specs.D07.Ch23.Frobenius
open Specs.D07.Ch23.FrobeniusAnticommutingDecomposition

theorem existence : Existence.{u} := by
  intro D _ _ h
  classical
  by_cases hs : Function.Surjective (algebraMap ℝ D)
  · exact Or.inl ⟨AlgEquiv.ofBijective (Algebra.ofId ℝ D)
      ⟨(algebraMap ℝ D).injective, hs⟩⟩
  · have hn : ∃ x : D, x ∉ Set.range (algebraMap ℝ D) := by
      simpa only [Function.Surjective, Set.mem_range, not_forall] using hs
    obtain ⟨i, φ, hi, hφ, hinj⟩ :=
      FrobeniusComplexSubfieldCentralizer.complexEmbeddingExists D h hn
    have hc : CentralizerCondition φ :=
      FrobeniusComplexSubfieldCentralizer.complexCentralizerImage D h φ
    by_cases hz : negative φ = ⊥
    · obtain ⟨e, he⟩ := FrobeniusAnticommutingDecomposition.complexCase φ hc hz
      exact Or.inr (Or.inl ⟨e⟩)
    · obtain ⟨j, hj, hj2, e, he⟩ :=
        FrobeniusAnticommutingDecomposition.quaternionCase φ hc hz
      exact Or.inr (Or.inr ⟨e⟩)

/-- The model's index really is the dimension, even before finite dimension
of the ambient ring has been established. -/
lemma model_finrank (D : Type u) [DivisionRing D] [Algebra ℝ D] {n : ℕ}
    (h : ModelEquivalence D n) : Module.finrank ℝ D = n := by
  rcases h with ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
  · simpa using e.toLinearEquiv.finrank_eq.symm
  · simpa using e.toLinearEquiv.finrank_eq.symm
  · simpa only [Quaternion.finrank_eq_four] using e.toLinearEquiv.finrank_eq.symm

theorem classification : Classification.{u} := by
  intro D _ _ h
  have hex : ∃ n : ℕ, ModelEquivalence D n := by
    rcases existence D h with hR | hC | hH
    · exact ⟨1, Or.inl ⟨rfl, hR⟩⟩
    · exact ⟨2, Or.inr (Or.inl ⟨rfl, hC⟩)⟩
    · exact ⟨4, Or.inr (Or.inr ⟨rfl, hH⟩)⟩
  obtain ⟨n, hn⟩ := hex
  exact ⟨n, hn, fun m hm => (model_finrank D hm).symm.trans (model_finrank D hn)⟩

theorem pairwiseNonisomorphic : PairwiseNonisomorphic := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    rintro ⟨e⟩
    have he := e.toLinearEquiv.finrank_eq
    norm_num [Quaternion.finrank_eq_four] at he

theorem algebraicFiniteDimensional : AlgebraicFiniteDimensional.{u} := by
  intro D _ _ h
  rcases existence D h with hR | hC | hH
  · obtain ⟨e⟩ := hR
    exact ⟨e.toLinearEquiv.finiteDimensional,
      Or.inl (by simpa using e.toLinearEquiv.finrank_eq.symm)⟩
  · obtain ⟨e⟩ := hC
    exact ⟨e.toLinearEquiv.finiteDimensional,
      Or.inr (Or.inl (by simpa using e.toLinearEquiv.finrank_eq.symm))⟩
  · obtain ⟨e⟩ := hH
    exact ⟨e.toLinearEquiv.finiteDimensional,
      Or.inr (Or.inr (by simpa only [Quaternion.finrank_eq_four]
        using e.toLinearEquiv.finrank_eq.symm))⟩

theorem finiteDimensionalClassification : FiniteDimensionalClassification.{u} := by
  intro D _ _ _
  exact classification D (fun x => IsAlgebraic.of_finite ℝ x)

end D07.Ch23.Frobenius
