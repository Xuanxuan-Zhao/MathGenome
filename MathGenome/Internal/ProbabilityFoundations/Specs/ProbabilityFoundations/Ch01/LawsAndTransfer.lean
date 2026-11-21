import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityObjects
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
Independent specifications for Definition 1.4 and Proposition 1.5.
Only canonical measures, measurable spaces and integrals occur below.
The Pi measurable space is the product sigma algebra for arbitrary index types.
Results not needing mass one are stated for arbitrary measures, and hence apply
to every probability space of the source without a completeness assumption.
-/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch01.LawsAndTransfer

universe u v w z

def lawType := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S], Measure Ω → (Ω → S) → Measure S
noncomputable def lawValue : lawType := fun P X => Measure.map X P

def jointMapType := ∀ {Ω : Type u} {I : Type v} {S : I → Type w},
  ((i : I) → Ω → S i) → Ω → (i : I) → S i
def jointMapValue : jointMapType := fun X ω i => X i ω

def jointLawType := ∀ {Ω : Type u} {I : Type v} {S : I → Type w}
  [MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)],
  Measure Ω → ((i : I) → Ω → S i) → Measure ((i : I) → S i)
noncomputable def jointLawValue : jointLawType :=
  fun P X => Measure.map (fun ω i => X i ω) P

def coordinateRestrictionType := ∀ {I : Type v} {J : Type z} {S : I → Type w},
  (r : J → I) → ((i : I) → S i) → (j : J) → S (r j)
def coordinateRestrictionValue : coordinateRestrictionType := fun r x j => x (r j)

def lawProbabilityType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
  (X : Ω → S), Measurable X → IsProbabilityMeasure (Measure.map X P)

def lawApplyType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X : Ω → S), Measurable X → ∀ (B : Set S), MeasurableSet B →
  Measure.map X P B = P (X ⁻¹' B)

def jointMapMeasurableType : Prop := ∀ {Ω : Type u} {I : Type v} {S : I → Type w}
  [MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)]
  (X : (i : I) → Ω → S i), (∀ i, Measurable (X i)) → Measurable (fun ω i => X i ω)

def jointLawProbabilityType : Prop := ∀ {Ω : Type u} {I : Type v} {S : I → Type w}
  [MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (X : (i : I) → Ω → S i), (∀ i, Measurable (X i)) →
  IsProbabilityMeasure (Measure.map (fun ω i => X i ω) P)

def coordinateRestrictionMeasurableType : Prop :=
  ∀ {I : Type v} {J : Type z} {S : I → Type w}
  [∀ i, MeasurableSpace (S i)] (r : J → I),
  Measurable (fun (x : (i : I) → S i) (j : J) => x (r j))

def jointLawMarginalType : Prop :=
  ∀ {Ω : Type u} {I : Type v} {J : Type z} {S : I → Type w}
  [MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)] (P : Measure Ω)
  (X : (i : I) → Ω → S i), (∀ i, Measurable (X i)) → ∀ r : J → I,
  Measure.map (fun (x : (i : I) → S i) j => x (r j))
    (Measure.map (fun ω i => X i ω) P) = Measure.map (fun ω j => X (r j) ω) P

def jointLawCoordinateType : Prop := ∀ {Ω : Type u} {I : Type v} {S : I → Type w}
  [MeasurableSpace Ω] [∀ i, MeasurableSpace (S i)] (P : Measure Ω)
  (X : (i : I) → Ω → S i), (∀ i, Measurable (X i)) → ∀ i : I,
  Measure.map (fun x : (i : I) → S i => x i) (Measure.map (fun ω i => X i ω) P) =
    Measure.map (X i) P

def lawCompType : Prop := ∀ {Ω : Type u} {S : Type v} {T : Type w}
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] (P : Measure Ω)
  (X : Ω → S), Measurable X → ∀ g : S → T, Measurable g →
  Measure.map (g ∘ X) P = Measure.map g (Measure.map X P)

def lawLIntegralType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X : Ω → S), Measurable X → ∀ f : S → ℝ≥0∞, Measurable f →
  (∫⁻ s, f s ∂Measure.map X P) = ∫⁻ ω, f (X ω) ∂P

def lawRealIntegrableIffType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X : Ω → S), Measurable X → ∀ f : S → ℝ, Measurable f →
  (Integrable f (Measure.map X P) ↔ Integrable (f ∘ X) P)

def lawComplexIntegrableIffType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X : Ω → S), Measurable X → ∀ f : S → ℂ, Measurable f →
  (Integrable f (Measure.map X P) ↔ Integrable (f ∘ X) P)

-- Integrable Bochner functions are already AE strongly measurable. These
-- versions also cover the source's possibly nonmeasurable representatives.
def lawRealIntegralType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X : Ω → S), Measurable X → ∀ f : S → ℝ, Integrable f (Measure.map X P) →
  (∫ s, f s ∂Measure.map X P) = ∫ ω, f (X ω) ∂P

def lawComplexIntegralType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
  (X : Ω → S), Measurable X → ∀ f : S → ℂ, Integrable f (Measure.map X P) →
  (∫ s, f s ∂Measure.map X P) = ∫ ω, f (X ω) ∂P

end Specs.ProbabilityFoundations.Ch01.LawsAndTransfer
