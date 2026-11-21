import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.FtcSecond
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
K03.09.parts, paper.tex:2430–2448. All integrals below are the upstream
proper Darboux integrals; boundedness is part of their integrability predicate.
The derivative extensions `du`, `dv` are constrained only on the open interval,
so arbitrary finite endpoint assignments are allowed. Both products are proved
integrable, rather than assumed so. Complex derivatives use the field ℝ.

The oriented statements integrate over [min a b, max a b] with sign +1 when
`a ≤ b` and -1 otherwise. This explicitly includes reversal and a = b.
C¹ is `ContDiffOn ℝ 1` on this closed interval, with `derivWithin` as its
continuous derivative extension; no ambient endpoint derivative is required.
-/
namespace Specs.SingleVariableAnalysis.Ch09.Parts
open Set
open Specs.SingleVariableAnalysis.Ch08.Integral

def realParts : Prop :=
  ∀ (u v du dv : ℝ → ℝ) (a b : ℝ), a ≤ b →
    ContinuousOn u (Icc a b) → ContinuousOn v (Icc a b) →
    (∀ x ∈ Ioo a b, HasDerivAt u (du x) x) →
    (∀ x ∈ Ioo a b, HasDerivAt v (dv x) x) →
    realIntegrableValue du a b → realIntegrableValue dv a b →
    ∃ h₁ : realIntegrableValue (fun x => u x * dv x) a b,
    ∃ h₂ : realIntegrableValue (fun x => du x * v x) a b,
      realIntegralValue _ h₁ = u b * v b - u a * v a - realIntegralValue _ h₂

def realPartsOriented : Prop :=
  ∀ (u v du dv : ℝ → ℝ) (a b : ℝ),
    ContinuousOn u (Icc (min a b) (max a b)) →
    ContinuousOn v (Icc (min a b) (max a b)) →
    (∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (du x) x) →
    (∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (dv x) x) →
    realIntegrableValue du (min a b) (max a b) →
    realIntegrableValue dv (min a b) (max a b) →
    ∃ h₁ : realIntegrableValue (fun x => u x * dv x) (min a b) (max a b),
    ∃ h₂ : realIntegrableValue (fun x => du x * v x) (min a b) (max a b),
      (if a ≤ b then (1 : ℝ) else -1) * realIntegralValue _ h₁ =
        u b * v b - u a * v a -
          (if a ≤ b then (1 : ℝ) else -1) * realIntegralValue _ h₂

def realPartsC1 : Prop :=
  ∀ (u v : ℝ → ℝ) (a b : ℝ),
    ContDiffOn ℝ 1 u (Icc (min a b) (max a b)) →
    ContDiffOn ℝ 1 v (Icc (min a b) (max a b)) →
    ∃ _hu : realIntegrableValue (derivWithin u (Icc (min a b) (max a b)))
      (min a b) (max a b),
    ∃ _hv : realIntegrableValue (derivWithin v (Icc (min a b) (max a b)))
      (min a b) (max a b),
    ∃ h₁ : realIntegrableValue
      (fun x => u x * derivWithin v (Icc (min a b) (max a b)) x) (min a b) (max a b),
    ∃ h₂ : realIntegrableValue
      (fun x => derivWithin u (Icc (min a b) (max a b)) x * v x) (min a b) (max a b),
      (if a ≤ b then (1 : ℝ) else -1) * realIntegralValue _ h₁ =
        u b * v b - u a * v a -
          (if a ≤ b then (1 : ℝ) else -1) * realIntegralValue _ h₂

def complexParts : Prop :=
  ∀ (u v du dv : ℝ → ℂ) (a b : ℝ), a ≤ b →
    ContinuousOn u (Icc a b) → ContinuousOn v (Icc a b) →
    (∀ x ∈ Ioo a b, HasDerivAt u (du x) x) →
    (∀ x ∈ Ioo a b, HasDerivAt v (dv x) x) →
    complexIntegrableValue du a b → complexIntegrableValue dv a b →
    ∃ h₁ : complexIntegrableValue (fun x => u x * dv x) a b,
    ∃ h₂ : complexIntegrableValue (fun x => du x * v x) a b,
      complexIntegralValue _ h₁ = u b * v b - u a * v a - complexIntegralValue _ h₂

def complexPartsOriented : Prop :=
  ∀ (u v du dv : ℝ → ℂ) (a b : ℝ),
    ContinuousOn u (Icc (min a b) (max a b)) →
    ContinuousOn v (Icc (min a b) (max a b)) →
    (∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (du x) x) →
    (∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (dv x) x) →
    complexIntegrableValue du (min a b) (max a b) →
    complexIntegrableValue dv (min a b) (max a b) →
    ∃ h₁ : complexIntegrableValue (fun x => u x * dv x) (min a b) (max a b),
    ∃ h₂ : complexIntegrableValue (fun x => du x * v x) (min a b) (max a b),
      (if a ≤ b then (1 : ℂ) else -1) * complexIntegralValue _ h₁ =
        u b * v b - u a * v a -
          (if a ≤ b then (1 : ℂ) else -1) * complexIntegralValue _ h₂

def complexPartsC1 : Prop :=
  ∀ (u v : ℝ → ℂ) (a b : ℝ),
    ContDiffOn ℝ 1 u (Icc (min a b) (max a b)) →
    ContDiffOn ℝ 1 v (Icc (min a b) (max a b)) →
    ∃ _hu : complexIntegrableValue (derivWithin u (Icc (min a b) (max a b)))
      (min a b) (max a b),
    ∃ _hv : complexIntegrableValue (derivWithin v (Icc (min a b) (max a b)))
      (min a b) (max a b),
    ∃ h₁ : complexIntegrableValue
      (fun x => u x * derivWithin v (Icc (min a b) (max a b)) x) (min a b) (max a b),
    ∃ h₂ : complexIntegrableValue
      (fun x => derivWithin u (Icc (min a b) (max a b)) x * v x) (min a b) (max a b),
      (if a ≤ b then (1 : ℂ) else -1) * complexIntegralValue _ h₁ =
        u b * v b - u a * v a -
          (if a ≤ b then (1 : ℂ) else -1) * complexIntegralValue _ h₂

end Specs.SingleVariableAnalysis.Ch09.Parts
