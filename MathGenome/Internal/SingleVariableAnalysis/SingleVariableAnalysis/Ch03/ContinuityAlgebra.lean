import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.Continuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.LimitAlgebra
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.ContinuityAlgebra
import Mathlib.Topology.Algebra.Monoid

/-!
# Algebra and composition of relative continuous functions

K03.03.continuity_algebra (paper.tex:505–512). The upstream epsilon/within
bridge transfers continuity through the usual scalar algebra. Mathlib's finite
sum and product limit lemmas cover arbitrary finite families, including the
empty family. Quotient continuity uses inversion only at a nonzero value.
The composition theorem explicitly tracks the image of the inner domain;
it applies to metric intermediate spaces, subsets, and isolated points.

Proof provenance: Mathlib's topological algebra and finite-product limit laws,
and its relative-domain composition law. No later project result is used.
-/
namespace SingleVariableAnalysis

open scoped BigOperators
universe u v w

theorem real_relativeContinuousAt_linear_combination :
    ∀ {X : Type u} {ι : Type v} [MetricSpace X]
      (E : Set X) (a : E) (s : Finset ι) (c : ι → ℝ) (f : ι → X → ℝ),
      (∀ i ∈ s, RelativeContinuousAt (f i) E a) →
      RelativeContinuousAt (fun x => ∑ i ∈ s, c i * f i x) E a := by
  intro X ι _ E a s c f hf
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact tendsto_finsetSum s (fun i hi =>
    ((relativeContinuousAt_within_iff _ _ _).mp (hf i hi)).const_mul (c i))

theorem real_relativeContinuousAt_finprod :
    ∀ {X : Type u} {ι : Type v} [MetricSpace X]
      (E : Set X) (a : E) (s : Finset ι) (f : ι → X → ℝ),
      (∀ i ∈ s, RelativeContinuousAt (f i) E a) →
      RelativeContinuousAt (fun x => ∏ i ∈ s, f i x) E a := by
  intro X ι _ E a s f hf
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact tendsto_finsetProd s (fun i hi =>
    (relativeContinuousAt_within_iff _ _ _).mp (hf i hi))

theorem real_relativeContinuousAt_div :
    ∀ {X : Type u} [MetricSpace X] (E : Set X) (a : E) (f g : X → ℝ),
      RelativeContinuousAt f E a → RelativeContinuousAt g E a → g a ≠ 0 →
      RelativeContinuousAt (fun x => f x / g x) E a := by
  intro X _ E a f g hf hg hne
  exact (relativeContinuousAt_within_iff _ _ _).mpr
    (((relativeContinuousAt_within_iff _ _ _).mp hf).div
      ((relativeContinuousAt_within_iff _ _ _).mp hg) hne)

theorem real_relativeContinuous_linear_combination :
    ∀ {X : Type u} {ι : Type v} [MetricSpace X]
      (E : Set X) (s : Finset ι) (c : ι → ℝ) (f : ι → X → ℝ),
      (∀ i ∈ s, RelativeContinuous (f i) E) →
      RelativeContinuous (fun x => ∑ i ∈ s, c i * f i x) E := by
  intro X ι _ E s c f hf a ha
  exact real_relativeContinuousAt_linear_combination E ⟨a, ha⟩ s c f
    (fun i hi => hf i hi a ha)

theorem real_relativeContinuous_finprod :
    ∀ {X : Type u} {ι : Type v} [MetricSpace X]
      (E : Set X) (s : Finset ι) (f : ι → X → ℝ),
      (∀ i ∈ s, RelativeContinuous (f i) E) →
      RelativeContinuous (fun x => ∏ i ∈ s, f i x) E := by
  intro X ι _ E s f hf a ha
  exact real_relativeContinuousAt_finprod E ⟨a, ha⟩ s f
    (fun i hi => hf i hi a ha)

theorem real_relativeContinuous_div :
    ∀ {X : Type u} [MetricSpace X] (E : Set X) (f g : X → ℝ),
      RelativeContinuous f E → RelativeContinuous g E →
      (∀ a ∈ E, g a ≠ 0) → RelativeContinuous (fun x => f x / g x) E := by
  intro X _ E f g hf hg hne a ha
  exact real_relativeContinuousAt_div E ⟨a, ha⟩ f g (hf a ha) (hg a ha) (hne a ha)

theorem real_relativeContinuous_div_on_nonzero :
    ∀ {X : Type u} [MetricSpace X] (E : Set X) (f g : X → ℝ),
      RelativeContinuous f E → RelativeContinuous g E →
      RelativeContinuous (fun x => f x / g x) (E ∩ {x | g x ≠ 0}) := by
  intro X _ E f g hf hg a ha
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact (((relativeContinuousAt_within_iff _ _ _).mp (hf a ha.1)).div
    ((relativeContinuousAt_within_iff _ _ _).mp (hg a ha.1)) ha.2).mono
      Set.inter_subset_left

theorem complex_relativeContinuousAt_linear_combination :
    ∀ {X : Type u} {ι : Type v} [MetricSpace X]
      (E : Set X) (a : E) (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ),
      (∀ i ∈ s, RelativeContinuousAt (f i) E a) →
      RelativeContinuousAt (fun x => ∑ i ∈ s, c i * f i x) E a := by
  intro X ι _ E a s c f hf
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact tendsto_finsetSum s (fun i hi =>
    ((relativeContinuousAt_within_iff _ _ _).mp (hf i hi)).const_mul (c i))

theorem complex_relativeContinuousAt_finprod :
    ∀ {X : Type u} {ι : Type v} [MetricSpace X]
      (E : Set X) (a : E) (s : Finset ι) (f : ι → X → ℂ),
      (∀ i ∈ s, RelativeContinuousAt (f i) E a) →
      RelativeContinuousAt (fun x => ∏ i ∈ s, f i x) E a := by
  intro X ι _ E a s f hf
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact tendsto_finsetProd s (fun i hi =>
    (relativeContinuousAt_within_iff _ _ _).mp (hf i hi))

theorem complex_relativeContinuousAt_div :
    ∀ {X : Type u} [MetricSpace X] (E : Set X) (a : E) (f g : X → ℂ),
      RelativeContinuousAt f E a → RelativeContinuousAt g E a → g a ≠ 0 →
      RelativeContinuousAt (fun x => f x / g x) E a := by
  intro X _ E a f g hf hg hne
  exact (relativeContinuousAt_within_iff _ _ _).mpr
    (((relativeContinuousAt_within_iff _ _ _).mp hf).div
      ((relativeContinuousAt_within_iff _ _ _).mp hg) hne)

theorem complex_relativeContinuous_linear_combination :
    ∀ {X : Type u} {ι : Type v} [MetricSpace X]
      (E : Set X) (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ),
      (∀ i ∈ s, RelativeContinuous (f i) E) →
      RelativeContinuous (fun x => ∑ i ∈ s, c i * f i x) E := by
  intro X ι _ E s c f hf a ha
  exact complex_relativeContinuousAt_linear_combination E ⟨a, ha⟩ s c f
    (fun i hi => hf i hi a ha)

theorem complex_relativeContinuous_finprod :
    ∀ {X : Type u} {ι : Type v} [MetricSpace X]
      (E : Set X) (s : Finset ι) (f : ι → X → ℂ),
      (∀ i ∈ s, RelativeContinuous (f i) E) →
      RelativeContinuous (fun x => ∏ i ∈ s, f i x) E := by
  intro X ι _ E s f hf a ha
  exact complex_relativeContinuousAt_finprod E ⟨a, ha⟩ s f
    (fun i hi => hf i hi a ha)

theorem complex_relativeContinuous_div :
    ∀ {X : Type u} [MetricSpace X] (E : Set X) (f g : X → ℂ),
      RelativeContinuous f E → RelativeContinuous g E →
      (∀ a ∈ E, g a ≠ 0) → RelativeContinuous (fun x => f x / g x) E := by
  intro X _ E f g hf hg hne a ha
  exact complex_relativeContinuousAt_div E ⟨a, ha⟩ f g (hf a ha) (hg a ha) (hne a ha)

theorem complex_relativeContinuous_div_on_nonzero :
    ∀ {X : Type u} [MetricSpace X] (E : Set X) (f g : X → ℂ),
      RelativeContinuous f E → RelativeContinuous g E →
      RelativeContinuous (fun x => f x / g x) (E ∩ {x | g x ≠ 0}) := by
  intro X _ E f g hf hg a ha
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact (((relativeContinuousAt_within_iff _ _ _).mp (hf a ha.1)).div
    ((relativeContinuousAt_within_iff _ _ _).mp (hg a ha.1)) ha.2).mono
      Set.inter_subset_left

theorem relativeContinuousAt_comp :
    ∀ {X : Type u} {Y : Type v} {Z : Type w}
      [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
      (E : Set X) (D : Set Y) (a : E) (f : X → Y) (g : Y → Z),
      Set.MapsTo f E D → RelativeContinuousAt f E a →
      RelativeContinuousAt g D (f a) →
      RelativeContinuousAt (g ∘ f) E a := by
  intro X Y Z _ _ _ E D a f g hmaps hf hg
  exact (relativeContinuousAt_within_iff _ _ _).mpr
    (((relativeContinuousAt_within_iff _ _ _).mp hg).comp
      ((relativeContinuousAt_within_iff _ _ _).mp hf) hmaps)

theorem relativeContinuous_comp :
    ∀ {X : Type u} {Y : Type v} {Z : Type w}
      [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
      (E : Set X) (D : Set Y) (f : X → Y) (g : Y → Z),
      Set.MapsTo f E D → RelativeContinuous f E → RelativeContinuous g D →
      RelativeContinuous (g ∘ f) E := by
  intro X Y Z _ _ _ E D f g hmaps hf hg a ha
  exact relativeContinuousAt_comp E D ⟨a, ha⟩ f g hmaps (hf a ha)
    (hg (f a) (hmaps ha))

end SingleVariableAnalysis
