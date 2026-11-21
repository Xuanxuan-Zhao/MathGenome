import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Algebra.Ring.Periodic

/-! Proper Darboux integrals, paper.tex:4770–4791 and 5058–5078.
A period is any positive real T. Integrability on a reference period is the
only regularity assumption. Integral values always carry integrability witnesses.
Translation and reflection use real variables for either scalar target. Finite
changes are local to each closed integration interval; no a.e. quotient is used.
The Fourier coefficient phase/rescaling and the kernel convolution identities
are separate downstream obligations. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral
open Ch08.Integral

def realTranslation : Prop := ∀ {f : ℝ → ℝ} {a b : ℝ} (c : ℝ)
    (hf : realIntegrableValue f (a+c) (b+c)),
    ∃ hg : realIntegrableValue (fun t => f (t+c)) a b,
      realIntegralValue _ hg = realIntegralValue f hf

def realReflection : Prop := ∀ {f : ℝ → ℝ} {a b : ℝ} (c : ℝ)
    (hf : realIntegrableValue f (c-b) (c-a)),
    ∃ hg : realIntegrableValue (fun t => f (c-t)) a b,
      realIntegralValue _ hg = realIntegralValue f hf

def realPeriodIntegral : Prop := ∀ {f : ℝ → ℝ} {T b : ℝ},
    0 < T → Function.Periodic f T →
    ∀ hf : realIntegrableValue f b (b+T), ∀ a : ℝ,
    ∃ hg : realIntegrableValue f a (a+T), realIntegralValue f hg = realIntegralValue f hf

def realPeriodicTranslation : Prop := ∀ {f : ℝ → ℝ} {T b : ℝ},
    0 < T → Function.Periodic f T →
    ∀ hf : realIntegrableValue f b (b+T), ∀ a c : ℝ,
    ∃ hg : realIntegrableValue (fun t => f (t+c)) a (a+T),
      realIntegralValue _ hg = realIntegralValue f hf

def realPeriodicReflection : Prop := ∀ {f : ℝ → ℝ} {T b : ℝ},
    0 < T → Function.Periodic f T →
    ∀ hf : realIntegrableValue f b (b+T), ∀ a c : ℝ,
    ∃ hg : realIntegrableValue (fun t => f (c-t)) a (a+T),
      realIntegralValue _ hg = realIntegralValue f hf

def realPeriodFiniteChanges : Prop := ∀ {f : ℝ → ℝ} {T b : ℝ},
    0 < T → Function.Periodic f T →
    ∀ hf : realIntegrableValue f b (b+T), ∀ (g : ℝ → ℝ) (a : ℝ),
    {x | x ∈ Set.Icc a (a+T) ∧ f x ≠ g x}.Finite →
    ∃ hg : realIntegrableValue g a (a+T), realIntegralValue g hg = realIntegralValue f hf

def complexTranslation : Prop := ∀ {f : ℝ → ℂ} {a b : ℝ} (c : ℝ)
    (hf : complexIntegrableValue f (a+c) (b+c)),
    ∃ hg : complexIntegrableValue (fun t => f (t+c)) a b,
      complexIntegralValue _ hg = complexIntegralValue f hf

def complexReflection : Prop := ∀ {f : ℝ → ℂ} {a b : ℝ} (c : ℝ)
    (hf : complexIntegrableValue f (c-b) (c-a)),
    ∃ hg : complexIntegrableValue (fun t => f (c-t)) a b,
      complexIntegralValue _ hg = complexIntegralValue f hf

def complexPeriodIntegral : Prop := ∀ {f : ℝ → ℂ} {T b : ℝ},
    0 < T → Function.Periodic f T →
    ∀ hf : complexIntegrableValue f b (b+T), ∀ a : ℝ,
    ∃ hg : complexIntegrableValue f a (a+T), complexIntegralValue f hg = complexIntegralValue f hf

def complexPeriodicTranslation : Prop := ∀ {f : ℝ → ℂ} {T b : ℝ},
    0 < T → Function.Periodic f T →
    ∀ hf : complexIntegrableValue f b (b+T), ∀ a c : ℝ,
    ∃ hg : complexIntegrableValue (fun t => f (t+c)) a (a+T),
      complexIntegralValue _ hg = complexIntegralValue f hf

def complexPeriodicReflection : Prop := ∀ {f : ℝ → ℂ} {T b : ℝ},
    0 < T → Function.Periodic f T →
    ∀ hf : complexIntegrableValue f b (b+T), ∀ a c : ℝ,
    ∃ hg : complexIntegrableValue (fun t => f (c-t)) a (a+T),
      complexIntegralValue _ hg = complexIntegralValue f hf

def complexPeriodFiniteChanges : Prop := ∀ {f : ℝ → ℂ} {T b : ℝ},
    0 < T → Function.Periodic f T →
    ∀ hf : complexIntegrableValue f b (b+T), ∀ (g : ℝ → ℂ) (a : ℝ),
    {x | x ∈ Set.Icc a (a+T) ∧ f x ≠ g x}.Finite →
    ∃ hg : complexIntegrableValue g a (a+T), complexIntegralValue g hg = complexIntegralValue f hf

/-- Consistent periodic finite assignments on one period are harmless on every period. -/
def realPeriodicFiniteChanges : Prop := ∀ {f g : ℝ → ℝ} {T b : ℝ},
    0 < T → Function.Periodic f T → Function.Periodic g T →
    ∀ hf : realIntegrableValue f b (b+T),
    {x | x ∈ Set.Icc b (b+T) ∧ f x ≠ g x}.Finite → ∀ a : ℝ,
    ∃ hg : realIntegrableValue g a (a+T),
      realIntegralValue g hg = realIntegralValue f hf

/-- Consistent periodic finite assignments on one period are harmless on every period. -/
def complexPeriodicFiniteChanges : Prop := ∀ {f g : ℝ → ℂ} {T b : ℝ},
    0 < T → Function.Periodic f T → Function.Periodic g T →
    ∀ hf : complexIntegrableValue f b (b+T),
    {x | x ∈ Set.Icc b (b+T) ∧ f x ≠ g x}.Finite → ∀ a : ℝ,
    ∃ hg : complexIntegrableValue g a (a+T),
      complexIntegralValue g hg = complexIntegralValue f hf

end Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral
