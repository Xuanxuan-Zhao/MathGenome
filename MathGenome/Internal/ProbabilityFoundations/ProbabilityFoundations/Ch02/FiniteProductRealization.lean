import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceJointLaws
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.FiniteProductRealization

/-!
The realization and transformation assertions of Theorem 2.4
(paper.tex:558–574). The realizing space is the finite dependent product with
its original product sigma-algebra and canonical product probability measure.
Empty families are included, and transformations have no index restriction.
-/

open MeasureTheory

namespace ProbabilityFoundations.Ch02

universe u v w z

/-- The finite product realizes the prescribed probability laws as the laws
of its mutually independent, measurable coordinate maps. -/
theorem finite_product_realization
    {I : Type v} [Fintype I] {S : I → Type w}
    [∀ i, MeasurableSpace (S i)]
    (μ : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (Measure.pi μ) ∧
      (∀ i, Measurable (fun x : (j : I) → S j => x i)) ∧
      IndependentRandomElements
        (Measure.pi μ) (fun i (x : (j : I) → S j) => x i) ∧
      (∀ i, Ch01.law (Measure.pi μ) (fun x : (j : I) → S j => x i) = μ i) := by
  refine ⟨inferInstance, fun i => measurable_pi_apply i, ?_, ?_⟩
  · apply (independentRandomElements_iff_iIndepFun _ _).mpr
    exact ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  · intro i
    exact (measurePreserving_eval μ i).map_eq

/-- Measurable coordinatewise transformations preserve mutual independence
of arbitrary families, including the empty family. -/
theorem independentRandomElements_comp
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} {T : I → Type z}
    [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (T i)]
    (X : ∀ i, Ω → S i) (g : ∀ i, S i → T i)
    (hX : ∀ i, Measurable (X i)) (hg : ∀ i, Measurable (g i))
    (h : IndependentRandomElements P X) :
    (∀ i, Measurable (g i ∘ X i)) ∧
      IndependentRandomElements P (fun i => g i ∘ X i) := by
  refine ⟨fun i => (hg i).comp (hX i), ?_⟩
  apply (independentRandomElements_iff_iIndepFun _ _).mpr
  exact ((independentRandomElements_iff_iIndepFun P X).mp h).comp g hg

end ProbabilityFoundations.Ch02
