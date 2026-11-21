import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperDefinition
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
K03.14.proper_derivative, paper.tex:3274–3304.
The spatial argument has exactly the subtype `[a,b]`. The real parameter has an
ambient representative; all regularity and derivative hypotheses are restricted
to the specified open set J. Thus any function originally defined only on J can
be extended arbitrarily outside J. No spatial extension is differentiated.
The value is exactly the upstream proper Darboux integral, with its integrability
witness. The conclusions apply to every ambient representative of that family,
so ordinary `HasDerivAt` and `ContDiffOn ℝ 1` express differentiation on the open
parameter domain. No integrability is assumed: it is part of the conclusion.
An arbitrary open J is allowed; in particular this includes every open interval.
The compact-neighborhood versions conclude on `(c,d)` from hypotheses on `[c,d]`;
applying these at each point gives the stated local applicability. Both scalar
cases include `a = b` and differentiate using real increments.
-/
namespace Specs.SingleVariableAnalysis.Ch14.ProperDerivative
open Set ProperDefinition

/-- Joint continuity, including relative continuity at the spatial endpoints. -/
def JointContinuous {E : Type*} [TopologicalSpace E] {a b : ℝ}
    (J : Set ℝ) (f : ℝ → Icc a b → E) : Prop :=
  ContinuousOn (Function.uncurry f) (J ×ˢ Set.univ)

/-- All integrals exist, and their family is C¹ with the asserted derivative. -/
def RealConclusion {a b : ℝ} (J : Set ℝ) (f g : ℝ → Icc a b → ℝ) : Prop :=
  ∃ (hf : ∀ t : J, sectionIntegrableValue .real (fun x t => f t.val x) t)
    (hg : ∀ t : J, sectionIntegrableValue .real (fun x t => g t.val x) t),
    ∀ F G : ℝ → ℝ,
      (∀ t : J, F t.val = familyValue .real (fun x t => f t.val x) ⟨t, hf t⟩) →
      (∀ t : J, G t.val = familyValue .real (fun x t => g t.val x) ⟨t, hg t⟩) →
      ContDiffOn ℝ 1 F J ∧ ContinuousOn G J ∧ ∀ t ∈ J, HasDerivAt F (G t) t

def ComplexConclusion {a b : ℝ} (J : Set ℝ) (f g : ℝ → Icc a b → ℂ) : Prop :=
  ∃ (hf : ∀ t : J, sectionIntegrableValue .complex (fun x t => f t.val x) t)
    (hg : ∀ t : J, sectionIntegrableValue .complex (fun x t => g t.val x) t),
    ∀ F G : ℝ → ℂ,
      (∀ t : J, F t.val = familyValue .complex (fun x t => f t.val x) ⟨t, hf t⟩) →
      (∀ t : J, G t.val = familyValue .complex (fun x t => g t.val x) ⟨t, hg t⟩) →
      ContDiffOn ℝ 1 F J ∧ ContinuousOn G J ∧ ∀ t ∈ J, HasDerivAt F (G t) t

def realProperDerivative : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ (J : Set ℝ), IsOpen J →
    ∀ f g : ℝ → Icc a b → ℝ,
      JointContinuous J f → JointContinuous J g →
      (∀ t ∈ J, ∀ x, HasDerivAt (fun s => f s x) (g t x) t) →
      RealConclusion J f g

def complexProperDerivative : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ (J : Set ℝ), IsOpen J →
    ∀ f g : ℝ → Icc a b → ℂ,
      JointContinuous J f → JointContinuous J g →
      (∀ t ∈ J, ∀ x, HasDerivAt (fun s => f s x) (g t x) t) →
      ComplexConclusion J f g

def realCompactNeighborhoodDerivative : Prop :=
  ∀ {a b c d : ℝ}, a ≤ b → c < d → ∀ f g : ℝ → Icc a b → ℝ,
    JointContinuous (Icc c d) f → JointContinuous (Icc c d) g →
    (∀ t ∈ Ioo c d, ∀ x, HasDerivAt (fun s => f s x) (g t x) t) →
    RealConclusion (Ioo c d) f g

def complexCompactNeighborhoodDerivative : Prop :=
  ∀ {a b c d : ℝ}, a ≤ b → c < d → ∀ f g : ℝ → Icc a b → ℂ,
    JointContinuous (Icc c d) f → JointContinuous (Icc c d) g →
    (∀ t ∈ Ioo c d, ∀ x, HasDerivAt (fun s => f s x) (g t x) t) →
    ComplexConclusion (Ioo c d) f g

end Specs.SingleVariableAnalysis.Ch14.ProperDerivative
