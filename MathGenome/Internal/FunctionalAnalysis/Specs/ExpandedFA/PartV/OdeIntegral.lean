import Specs.ExpandedFA.PartV.VolterraOperator
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! The ODE clause of paper.tex, `fa2:p5:volterra-regularity`.
We use an arbitrary finite closed interval [a,b], with initial time a;
a=0 and b=T gives exactly the manuscript's statement, including T=0.
The data and unknowns are actual continuous maps on the interval. Their
constant extensions are used only to express ordinary Bochner integrals and
within derivatives. All derivatives are with respect to real time, with the
canonical real restriction of the real or complex state space.

`IsC1` means a continuous derivative field on the interval, including within
derivatives at its endpoints. On a singleton the derivative field need not be
unique, and the initial value, rather than a derivative constraint, fixes u.
-/
noncomputable section
open Set MeasureTheory
namespace ExpandedFA.PartV.OdeIntegralSpec

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
variable {a b : ℝ}

def extendCurve (hab : a ≤ b) (u : C(VolterraInterval a b, E)) (t : ℝ) : E :=
  u (projIcc a b hab t)

/-- The continuous vector field evaluated along the curve. -/
def rhs (A : C(VolterraInterval a b, E →L[𝕜] E))
    (B u : C(VolterraInterval a b, E)) : C(VolterraInterval a b, E) :=
  ⟨fun t => A t (u t) + B t, (A.continuous.clm_apply u.continuous).add B.continuous⟩

def IsIntegralSolution (hab : a ≤ b) (A : C(VolterraInterval a b, E →L[𝕜] E))
    (B : C(VolterraInterval a b, E)) (ξ : E) (u : C(VolterraInterval a b, E)) : Prop :=
  ∀ t, u t = ξ + ∫ s in a..(t : ℝ), extendCurve hab (rhs A B u) s

def IsC1 (hab : a ≤ b) (u : C(VolterraInterval a b, E)) : Prop :=
  ∃ d : C(VolterraInterval a b, E), ∀ t : VolterraInterval a b,
    HasDerivWithinAt (extendCurve hab u) (d t) (Icc a b) (t : ℝ)

def IsClassicalSolution (hab : a ≤ b) (A : C(VolterraInterval a b, E →L[𝕜] E))
    (B : C(VolterraInterval a b, E)) (ξ : E) (u : C(VolterraInterval a b, E)) : Prop :=
  IsC1 (𝕜 := 𝕜) hab u ∧ u ⟨a, le_rfl, hab⟩ = ξ ∧
    ∀ t : VolterraInterval a b,
      HasDerivWithinAt (extendCurve hab u) (A t (u t) + B t) (Icc a b) (t : ℝ)

end

def DifferentialEquivalence : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (A : C(VolterraInterval a b, E →L[𝕜] E))
  (B : C(VolterraInterval a b, E)) (ξ : E) (u : C(VolterraInterval a b, E)),
  IsIntegralSolution hab A B ξ u ↔ IsClassicalSolution hab A B ξ u

def UniqueSolvability : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (A : C(VolterraInterval a b, E →L[𝕜] E))
  (B : C(VolterraInterval a b, E)) (ξ : E),
  ∃ u : C(VolterraInterval a b, E),
    IsIntegralSolution hab A B ξ u ∧ IsClassicalSolution hab A B ξ u ∧
    (∀ v, IsIntegralSolution hab A B ξ v → v = u) ∧
    (∀ v, IsClassicalSolution hab A B ξ v → v = u)

/-- No assumptions on the values of A or B are needed on the zero interval. -/
def SingletonCharacterization : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a : ℝ) (A : C(VolterraInterval a a, E →L[𝕜] E))
  (B : C(VolterraInterval a a, E)) (ξ : E) (u : C(VolterraInterval a a, E)),
  (IsIntegralSolution (le_refl a) A B ξ u ↔ u ⟨a, le_rfl, le_rfl⟩ = ξ) ∧
  (IsClassicalSolution (le_refl a) A B ξ u ↔ u ⟨a, le_rfl, le_rfl⟩ = ξ)

end ExpandedFA.PartV.OdeIntegralSpec
