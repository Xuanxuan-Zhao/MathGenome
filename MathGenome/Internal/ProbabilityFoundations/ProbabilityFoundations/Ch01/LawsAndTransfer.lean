import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityObjects
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.LawsAndTransfer

/-!
Definition 1.4 and Proposition 1.5 (paper.tex, lines 162–201).
Products always carry their specified product measurable spaces. There is no
countability restriction on either index type and no completeness assumption.
The pushforward and transfer facts that do not use normalization are stated
for arbitrary measures.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch01

universe u v w z t

/-- The law is the canonical pushforward measure. -/
noncomputable def law {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) (X : Ω → S) : Measure S :=
  Measure.map X P

/-- Assemble a family of random elements, with no restriction on its index set. -/
def jointMap {Ω : Type u} {I : Type v} {S : I → Type w}
    (X : (i : I) → Ω → S i) : Ω → (i : I) → S i := fun ω i => X i ω

/-- The joint law uses the product sigma algebra, also for empty products. -/
noncomputable def jointLaw {Ω : Type u} {I : Type v} {S : I → Type w}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)]
    (P : Measure Ω) (X : (i : I) → Ω → S i) : Measure ((i : I) → S i) :=
  law P (jointMap X)

/-- Restrict coordinates along any index map; subtype inclusions give subfamilies. -/
def coordinateRestriction {I : Type v} {J : Type z} {S : I → Type w}
    (r : J → I) : ((i : I) → S i) → (j : J) → S (r j) := fun x j => x (r j)

theorem law_probability {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (hX : Measurable X) : IsProbabilityMeasure (law P X) :=
  (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr inferInstance

theorem law_apply {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    (X : Ω → S) (hX : Measurable X) (B : Set S) (hB : MeasurableSet B) :
    law P X B = P (X ⁻¹' B) :=
  Measure.map_apply hX hB

theorem jointMap_measurable {Ω : Type u} {I : Type v} {S : I → Type w}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)]
    (X : (i : I) → Ω → S i) (hX : ∀ i, Measurable (X i)) :
    Measurable (jointMap X) :=
  measurable_pi_iff.mpr hX

theorem jointLaw_probability {Ω : Type u} {I : Type v} {S : I → Type w}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (i : I) → Ω → S i) (hX : ∀ i, Measurable (X i)) :
    IsProbabilityMeasure (jointLaw P X) :=
  law_probability P (jointMap X) (jointMap_measurable X hX)

theorem coordinateRestriction_measurable {I : Type v} {J : Type z} {S : I → Type w}
    [∀ i, MeasurableSpace (S i)] (r : J → I) :
    Measurable (coordinateRestriction (S := S) r) :=
  measurable_pi_iff.mpr (fun j => measurable_pi_apply (r j))

/-- Every subfamily law is the corresponding pushforward marginal.
The index map can be the inclusion of any subset of the original index set. -/
theorem jointLaw_marginal {Ω : Type u} {I : Type v} {J : Type z} {S : I → Type w}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)] (P : Measure Ω)
    (X : (i : I) → Ω → S i) (hX : ∀ i, Measurable (X i)) (r : J → I) :
    Measure.map (coordinateRestriction (S := S) r) (jointLaw P X) =
      jointLaw P (fun j => X (r j)) :=
  Measure.map_map (coordinateRestriction_measurable r) (jointMap_measurable X hX)

theorem jointLaw_coordinate {Ω : Type u} {I : Type v} {S : I → Type w}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)] (P : Measure Ω)
    (X : (i : I) → Ω → S i) (hX : ∀ i, Measurable (X i)) (i : I) :
    Measure.map (fun x : (i : I) → S i => x i) (jointLaw P X) = law P (X i) :=
  Measure.map_map (measurable_pi_apply i) (jointMap_measurable X hX)

theorem law_comp {Ω : Type u} {S : Type v} {T : Type w}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] (P : Measure Ω)
    (X : Ω → S) (hX : Measurable X) (g : S → T) (hg : Measurable g) :
    law P (g ∘ X) = Measure.map g (law P X) :=
  (Measure.map_map hg hX).symm

/-- Extended nonnegative transfer, including infinite values. -/
theorem law_lintegral {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    (X : Ω → S) (hX : Measurable X) (f : S → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s, f s ∂law P X) = ∫⁻ ω, f (X ω) ∂P :=
  lintegral_map hf hX

theorem law_real_integrable_iff {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    (X : Ω → S) (hX : Measurable X) (f : S → ℝ) (hf : Measurable f) :
    Integrable f (law P X) ↔ Integrable (f ∘ X) P :=
  integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable

theorem law_complex_integrable_iff {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    (X : Ω → S) (hX : Measurable X) (f : S → ℂ) (hf : Measurable f) :
    Integrable f (law P X) ↔ Integrable (f ∘ X) P :=
  integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable

/-- Integrability under the law already supplies the measurability needed here. -/
theorem law_real_integral {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    (X : Ω → S) (hX : Measurable X) (f : S → ℝ) (hf : Integrable f (law P X)) :
    (∫ s, f s ∂law P X) = ∫ ω, f (X ω) ∂P :=
  integral_map hX.aemeasurable hf.aestronglyMeasurable

theorem law_complex_integral {Ω : Type u} {S : Type v}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    (X : Ω → S) (hX : Measurable X) (f : S → ℂ) (hf : Integrable f (law P X)) :
    (∫ s, f s ∂law P X) = ∫ ω, f (X ω) ∂P :=
  integral_map hX.aemeasurable hf.aestronglyMeasurable

end ProbabilityFoundations.Ch01
