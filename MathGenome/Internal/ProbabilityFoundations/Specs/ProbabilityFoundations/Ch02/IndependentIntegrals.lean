import Mathlib.MeasureTheory.Integral.Pi
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces

/-! Independent specifications for Corollary 2.5 (paper.tex:588–619).
The product measurable space is the specified product sigma algebra. In the
signed case `Integrable` expresses absolute integrability, including the
necessary AE strong measurability. `AEStronglyMeasurable` in the equivalence
is in particular satisfied by every measurable real or complex function.
Finite index types include the empty type. Products of `ℝ≥0∞` use its usual
multiplication, where zero times infinity is zero. An arbitrary equivalence
`Fin n ≃ I` specifies an order for the fully iterated integrals.

The two recursive integral definitions are shared mathematical notation;
none of the propositions below assumes any certificate or candidate result.
-/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch02.IndependentIntegrals

universe u v w z
set_option linter.unusedVariables false

def independent_lintegralType : Prop := ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X)
    (f : ((i : I) → S i) → ℝ≥0∞) (hf : Measurable f),
    (∫⁻ ω, f (fun i => X i ω) ∂P) =
      ∫⁻ x, f x ∂Measure.pi (fun i => Measure.map (X i) P)

def independent_integrable_iffType : Prop := ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X)
    {𝕜 : Type z} [RCLike 𝕜]
    (f : ((i : I) → S i) → 𝕜)
    (hf : AEStronglyMeasurable f (Measure.pi (fun i => Measure.map (X i) P))),
    Integrable f (Measure.pi (fun i => Measure.map (X i) P)) ↔
      Integrable (fun ω => f (fun i => X i ω)) P

def independent_integralType : Prop := ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X)
    {𝕜 : Type z} [RCLike 𝕜]
    (f : ((i : I) → S i) → 𝕜)
    (hf : Integrable f (Measure.pi (fun i => Measure.map (X i) P))),
    (∫ ω, f (fun i => X i ω) ∂P) =
      ∫ x, f x ∂Measure.pi (fun i => Measure.map (X i) P)

def independent_nonnegative_factorsType : Prop := ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X)
    (f : (i : I) → S i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)),
    (∫⁻ ω, ∏ i, f i (X i ω) ∂P) =
      ∏ i, ∫⁻ x, f i x ∂Measure.map (X i) P

def independent_integrable_factorsType : Prop := ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X)
    {𝕜 : Type z} [RCLike 𝕜]
    (f : (i : I) → S i → 𝕜)
    (hf : ∀ i, Integrable (f i) (Measure.map (X i) P)),
    Integrable (fun ω => ∏ i, f i (X i ω)) P ∧
      (∫ ω, ∏ i, f i (X i ω) ∂P) =
        ∏ i, ∫ x, f i x ∂Measure.map (X i) P

def independent_nonnegative_factors_zeroType : Prop := ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X)
    (f : (i : I) → S i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (j : I) (hj : (∫⁻ x, f j x ∂Measure.map (X j) P) = 0),
    (∫⁻ ω, ∏ i, f i (X i ω) ∂P) = 0

/-- Successively integrate coordinate 0, then 1, and so on. At dimension
zero the product has its unique empty tuple and the integral is evaluation. -/
noncomputable def iteratedLIntegral :
    {n : ℕ} → {S : Fin n → Type w} → [∀ i, MeasurableSpace (S i)] →
      ((i : Fin n) → Measure (S i)) → (((i : Fin n) → S i) → ℝ≥0∞) → ℝ≥0∞
  | 0, _, _, _, f => f (fun i => Fin.elim0 i)
  | n + 1, _, _, μ, f =>
      ∫⁻ a, iteratedLIntegral (fun i : Fin n => μ i.succ) (fun x => f (Fin.cons a x)) ∂μ 0

/-- The signed/complex iterated integral, with the same empty-tuple convention.
The equality with the product integral is asserted only for integrable functions. -/
noncomputable def iteratedIntegral {𝕜 : Type z} [RCLike 𝕜] :
    {n : ℕ} → {S : Fin n → Type w} → [∀ i, MeasurableSpace (S i)] →
      ((i : Fin n) → Measure (S i)) → (((i : Fin n) → S i) → 𝕜) → 𝕜
  | 0, _, _, _, f => f (fun i => Fin.elim0 i)
  | n + 1, _, _, μ, f =>
      ∫ a, iteratedIntegral (fun i : Fin n => μ i.succ) (fun x => f (Fin.cons a x)) ∂μ 0

def pi_lintegral_iteratedType : Prop := ∀ {n : ℕ} {S : Fin n → Type w} [∀ i, MeasurableSpace (S i)]
    (μ : (i : Fin n) → Measure (S i)) [∀ i, SigmaFinite (μ i)]
    (f : ((i : Fin n) → S i) → ℝ≥0∞) (hf : Measurable f),
    (∫⁻ x, f x ∂Measure.pi μ) = iteratedLIntegral μ f

def pi_integral_iteratedType : Prop := ∀ {n : ℕ} {S : Fin n → Type w} [∀ i, MeasurableSpace (S i)]
    (μ : (i : Fin n) → Measure (S i)) [∀ i, SigmaFinite (μ i)]
    {𝕜 : Type z} [RCLike 𝕜]
    (f : ((i : Fin n) → S i) → 𝕜) (hf : Integrable f (Measure.pi μ)),
    (∫ x, f x ∂Measure.pi μ) = iteratedIntegral μ f

def independent_lintegral_iteratedType : Prop := ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X)
    {n : ℕ} (e : Fin n ≃ I)
    (f : ((i : I) → S i) → ℝ≥0∞) (hf : Measurable f),
    (∫⁻ ω, f (fun i => X i ω) ∂P) =
      iteratedLIntegral (fun j => Measure.map (X (e j)) P)
        (fun x => f (MeasurableEquiv.piCongrLeft S e x))

def independent_integral_iteratedType : Prop := ∀ {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X)
    {n : ℕ} (e : Fin n ≃ I)
    {𝕜 : Type z} [RCLike 𝕜]
    (f : ((i : I) → S i) → 𝕜)
    (hf : Integrable f (Measure.pi (fun i => Measure.map (X i) P))),
    (∫ ω, f (fun i => X i ω) ∂P) =
      iteratedIntegral (fun j => Measure.map (X (e j)) P)
        (fun x => f (MeasurableEquiv.piCongrLeft S e x))

end Specs.ProbabilityFoundations.Ch02.IndependentIntegrals
