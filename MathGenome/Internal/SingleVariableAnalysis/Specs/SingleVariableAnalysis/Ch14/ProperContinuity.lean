import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperDefinition
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Basic

/-!
K03.14.proper_continuity (paper.tex:3257–3274).
The functions and their integral values are exactly the upstream proper Darboux
families on `[a,b] × T`. Both variables are real; the two scalar cases are
spelled out to retain the canonical norms and topologies without new instances.
The local hypothesis requires integrability only in a relative neighborhood,
including the base point. The supremum is over the actual closed interval.
The extension formulation expresses continuity relative to all of T near t₀;
outside the neighborhood an extension may take arbitrary values.
Joint continuity uses the product of the interval subtypes, so endpoints are
relative endpoints. Singleton integration and parameter intervals are included.
-/
namespace Specs.SingleVariableAnalysis.Ch14.ProperContinuity
open _root_.SingleVariableAnalysis
open scoped Topology
open ProperDefinition

/-- The actual uniform section error; bounded near the base point by section
integrability. No boundedness or integral existence is inferred from `sSup` alone. -/
noncomputable def sectionError {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {T : Set ℝ} (f : Set.Icc a b → T → E) (t t₀ : T) : ℝ :=
  sSup (Set.range (fun x : Set.Icc a b => ‖f x t - f x t₀‖))

/-- The same canonical family, with its concrete scalar codomain exposed. -/
noncomputable def realFamily {a b : ℝ} {T : Set ℝ}
    (f : Set.Icc a b → T → ℝ) : parametersValue .real f → ℝ := familyValue .real f

noncomputable def complexFamily {a b : ℝ} {T : Set ℝ}
    (f : Set.Icc a b → T → ℂ) : parametersValue .complex f → ℂ := familyValue .complex f

def realDifferenceBound : Prop :=
  ∀ {a b : ℝ} {T : Set ℝ} (f : Set.Icc a b → T → ℝ)
    (t t₀ : T) (ht : sectionIntegrableValue .real f t)
    (h₀ : sectionIntegrableValue .real f t₀),
    ‖realFamily f ⟨t, ht⟩ - realFamily f ⟨t₀, h₀⟩‖ ≤
      (b - a) * sectionError f t t₀

def realLocalContinuity : Prop :=
  ∀ {a b : ℝ} {T : Set ℝ} (f : Set.Icc a b → T → ℝ)
    (t₀ : T) (h₀ : sectionIntegrableValue .real f t₀),
    (∀ᶠ t in 𝓝 t₀, sectionIntegrableValue .real f t) →
    Filter.Tendsto (fun t => sectionError f t t₀) (𝓝 t₀) (𝓝 0) →
    ContinuousAt (realFamily f) ⟨t₀, h₀⟩

def realRelativeContinuity : Prop :=
  ∀ {a b : ℝ} {T : Set ℝ} (f : Set.Icc a b → T → ℝ)
    (t₀ : T) (h₀ : sectionIntegrableValue .real f t₀),
    (∀ᶠ t in 𝓝 t₀, sectionIntegrableValue .real f t) →
    Filter.Tendsto (fun t => sectionError f t t₀) (𝓝 t₀) (𝓝 0) →
    ∀ F : T → ℝ,
      (∀ t (ht : sectionIntegrableValue .real f t),
        F t = realFamily f ⟨t, ht⟩) → ContinuousAt F t₀

def realRectangleContinuity : Prop :=
  ∀ {a b c d : ℝ}, a ≤ b → c ≤ d →
    ∀ f : Set.Icc a b → Set.Icc c d → ℝ,
    Continuous (Function.uncurry f) →
    ∃ h : ∀ t, sectionIntegrableValue .real f t,
      Continuous (fun t => realFamily f ⟨t, h t⟩)

def complexDifferenceBound : Prop :=
  ∀ {a b : ℝ} {T : Set ℝ} (f : Set.Icc a b → T → ℂ)
    (t t₀ : T) (ht : sectionIntegrableValue .complex f t)
    (h₀ : sectionIntegrableValue .complex f t₀),
    ‖complexFamily f ⟨t, ht⟩ - complexFamily f ⟨t₀, h₀⟩‖ ≤
      (b - a) * sectionError f t t₀

def complexLocalContinuity : Prop :=
  ∀ {a b : ℝ} {T : Set ℝ} (f : Set.Icc a b → T → ℂ)
    (t₀ : T) (h₀ : sectionIntegrableValue .complex f t₀),
    (∀ᶠ t in 𝓝 t₀, sectionIntegrableValue .complex f t) →
    Filter.Tendsto (fun t => sectionError f t t₀) (𝓝 t₀) (𝓝 0) →
    ContinuousAt (complexFamily f) ⟨t₀, h₀⟩

def complexRelativeContinuity : Prop :=
  ∀ {a b : ℝ} {T : Set ℝ} (f : Set.Icc a b → T → ℂ)
    (t₀ : T) (h₀ : sectionIntegrableValue .complex f t₀),
    (∀ᶠ t in 𝓝 t₀, sectionIntegrableValue .complex f t) →
    Filter.Tendsto (fun t => sectionError f t t₀) (𝓝 t₀) (𝓝 0) →
    ∀ F : T → ℂ,
      (∀ t (ht : sectionIntegrableValue .complex f t),
        F t = complexFamily f ⟨t, ht⟩) → ContinuousAt F t₀

def complexRectangleContinuity : Prop :=
  ∀ {a b c d : ℝ}, a ≤ b → c ≤ d →
    ∀ f : Set.Icc a b → Set.Icc c d → ℂ,
    Continuous (Function.uncurry f) →
    ∃ h : ∀ t, sectionIntegrableValue .complex f t,
      Continuous (fun t => complexFamily f ⟨t, h t⟩)

end Specs.SingleVariableAnalysis.Ch14.ProperContinuity
