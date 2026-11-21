import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.CountableCylinderReduction
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.CylinderFramework
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

open Set MeasureTheory

namespace ProbabilityFoundations.Ch05.CountableCylinderReduction

open CylinderFramework

universe u v

variable {I : Type u} {S : I → Type v} [∀ i, MeasurableSpace (S i)]
  {μ : FiniteLaws S}

@[fun_prop]
theorem measurable_subfamilyProjection (J : Set I) (F : Finset I)
    (hF : (↑F : Set I) ⊆ J) : Measurable (subfamilyProjection S J F hF) :=
  Measurable.of_eval (fun i => measurable_pi_apply (⟨i, hF i.property⟩ : J))

variable [∀ i, Nonempty (S i)]

/-- A countable collection of finite supports can be realized simultaneously by
a probability on the full product, using fixed values outside their union. -/
theorem exists_measure_for_supports (hcount : HasCountableExtensions S μ)
    (F : ℕ → Finset I) :
    ∃ ν : Measure (ProductSpace S), IsProbabilityMeasure ν ∧
      ∀ n, ν.map (finiteProjection S (F n)) = μ (F n) := by
  classical
  let J : Set I := ⋃ n, (↑(F n) : Set I)
  have hJ : J.Countable := countable_iUnion (fun n => (F n).countable_toSet)
  obtain ⟨ρ, hρ, hρlaw⟩ := hcount J hJ
  let pad : ProductSpace (fun i : J => S i) → ProductSpace S :=
    fun x i => if hi : i ∈ J then x ⟨i, hi⟩ else Classical.choice (inferInstance : Nonempty (S i))
  have hpad : Measurable pad := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ J
    · simpa only [pad, dite_eq_left hi] using (measurable_pi_apply (⟨i, hi⟩ : J))
    · simpa only [pad, dite_eq_right hi] using
        (measurable_const : Measurable (fun _ : ProductSpace (fun i : J => S i) =>
          Classical.choice (inferInstance : Nonempty (S i))))
  let _ : IsProbabilityMeasure ρ := hρ
  refine ⟨ρ.map pad, inferInstance, fun n => ?_⟩
  have hF : (↑(F n) : Set I) ⊆ J := subset_iUnion (fun n => (↑(F n) : Set I)) n
  rw [Measure.map_map (measurable_finiteProjection S _) hpad]
  have heq : finiteProjection S (F n) ∘ pad = subfamilyProjection S J (F n) hF := by
    funext x i
    exact dite_eq_left (hF i.property)
  rw [heq]
  exact hρlaw (F n) hF

/-- The prescribed content agrees with one genuine probability on any countable
list of cylinders. This is the countable-to-arbitrary-index step. -/
theorem exists_measure_agree_cylinders (hμ : IsProjectiveMeasureFamily μ)
    (hcount : HasCountableExtensions S μ) (s : ℕ → Set (ProductSpace S))
    (hs : ∀ n, s n ∈ measurableCylinders S) :
    ∃ ν : Measure (ProductSpace S), IsProbabilityMeasure ν ∧
      ∀ n, ν (s n) = projectiveFamilyContent hμ (s n) := by
  let F := fun n => measurableCylinders.finset (hs n)
  obtain ⟨ν, hν, hlaw⟩ := exists_measure_for_supports hcount F
  refine ⟨ν, hν, fun n => ?_⟩
  rw [measurableCylinders.eq_cylinder (hs n),
    projectiveFamilyContent_cylinder hμ (measurableCylinders.measurableSet (hs n))]
  change ν (finiteProjection S (F n) ⁻¹' measurableCylinders.set (hs n)) = _
  rw [← Measure.map_apply (measurable_finiteProjection S _)
    (measurableCylinders.measurableSet (hs n)), hlaw n]

/-- The algebra content is sigma-subadditive because every countable covering
in the algebra can be evaluated under a single countable-coordinate extension. -/
theorem content_sigmaSubadditive (hμ : IsProjectiveMeasureFamily μ)
    (hcount : HasCountableExtensions S μ) :
    (projectiveFamilyContent hμ).IsSigmaSubadditive := by
  intro f hf hU
  let s : ℕ → Set (ProductSpace S) := fun n =>
    match n with
    | 0 => ⋃ k, f k
    | k + 1 => f k
  have hs : ∀ n, s n ∈ measurableCylinders S := by
    intro n
    cases n with
    | zero => exact hU
    | succ k => exact hf k
  obtain ⟨ν, _, hagree⟩ := exists_measure_agree_cylinders hμ hcount s hs
  have h0 := hagree 0
  have hn : ∀ n, ν (f n) = projectiveFamilyContent hμ (f n) := fun n => hagree (n + 1)
  change ν (⋃ n, f n) = _ at h0
  rw [← h0, ← tsum_congr hn]
  exact measure_iUnion_le f

/-- Reduction to countably many coordinates, with arbitrary index type and
arbitrary nonempty measurable factors (paper.tex, Lemma 5.2). -/
theorem countable_cylinder_reduction :
    Specs.ProbabilityFoundations.Ch05.CountableCylinderReduction.ReductionTheorem.{u,v} := by
  intro I S inst instNE μ hprob hcons hcount
  let _ : ∀ F, IsProbabilityMeasure (μ F) := hprob
  have hμ : IsProjectiveMeasureFamily μ := fun F E h => (hcons E F h).symm
  let m := projectiveFamilyContent hμ
  have hsub := content_sigmaSubadditive hμ hcount
  have hgen : (inferInstance : MeasurableSpace (ProductSpace S)) =
      MeasurableSpace.generateFrom (measurableCylinders S) :=
    generateFrom_measurableCylinders.symm
  let ν : Measure (ProductSpace S) :=
    m.measure isSetSemiring_measurableCylinders hgen.le hsub
  have heval (A : Set (ProductSpace S)) (hA : A ∈ measurableCylinders S) : ν A = m A :=
    m.measure_eq isSetSemiring_measurableCylinders hgen hsub hA
  have hlaw : IsProjectiveLimit ν μ := by
    intro F
    apply Measure.ext
    intro B hB
    rw [Measure.map_apply F.measurable_restrict hB]
    change ν (cylinder F B) = μ F B
    rw [heval _ (cylinder_mem_measurableCylinders F B hB)]
    exact projectiveFamilyContent_cylinder hμ hB
  refine ⟨ν, ⟨hlaw.isProbabilityMeasure, hlaw⟩, ?_⟩
  intro ρ hρ
  exact (show IsProjectiveLimit ρ μ from hρ.2).unique hlaw

end ProbabilityFoundations.Ch05.CountableCylinderReduction
