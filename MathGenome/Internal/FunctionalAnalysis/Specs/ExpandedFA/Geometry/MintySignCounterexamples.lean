import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.MintyCompactDomain
import Mathlib.Data.Fintype.BigOperators

/-! The two sign qualifications at `fa2:p2:minty-source-signs`, together
with the corrected weak inequality from `fa2:p2:minty-compact-domain`.
Real numbers represent their continuous linear dual by multiplication. -/
namespace Specs.ExpandedFA.Geometry.MintySignCounterexamples
open Set
open scoped BigOperators
universe u v

/-- The scalar identity operator, with values in the continuous real dual. -/
def identityDual (v : ℝ) : ℝ →L[ℝ] ℝ := v • ContinuousLinearMap.id ℝ ℝ

def twoPoints (i : Fin 2) : ℝ := if i = 0 then 0 else 1

def signedWeights (i : Fin 2) : ℝ := if i = 0 then 1 else -1

/-- The counterexample uses a monotone operator. -/
def IdentityMonotone : Prop :=
  ∀ x y : ℝ, 0 ≤ (identityDual x - identityDual y) (x-y)

/-- Even allowing u outside K cannot rescue the reversed printed sign. -/
def ReversedSignCounterexample : Prop :=
  ¬ ∃ u : ℝ, ∀ v ∈ Icc (-1 : ℝ) 1, 0 ≤ identityDual v (u-v)

/-- This is exactly the source's F(s,s) for its two specified points and
signed coefficients; in particular it is strictly positive. -/
def SignedQuadraticCounterexample : Prop :=
  (∑ i : Fin 2, ∑ j : Fin 2,
    signedWeights i * signedWeights j * identityDual (twoPoints j)
      (twoPoints i - twoPoints j)) = 1

/-- The nonpositive sign is valid for all finite probability coefficients,
including tests in an arbitrary (possibly empty) operator domain. -/
def ProbabilityQuadraticNonpositive : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (D : Set X) (A : D → (X →L[ℝ] ℝ)),
    Specs.ExpandedFA.Geometry.MintyCompactDomain.DomainMonotone A →
    ∀ (ι : Type v) [Fintype ι] (v : ι → D) (s : ι → ℝ),
      (∀ i, 0 ≤ s i) → (∑ i, s i) = 1 →
      (∑ i, ∑ j, s i * s j * A (v j) ((v i : X) - v j)) ≤ 0

/-- The corrected weak Minty conclusion keeps the exact domain D and tests
only D ∩ K. In particular there is no hidden assumption K ⊆ D. -/
def CorrectedWeakMintyExistence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ (D K : Set X) (A : D → (X →L[ℝ] ℝ)),
      K.Nonempty → IsClosed K → Bornology.IsBounded K → Convex ℝ K →
      Specs.ExpandedFA.Geometry.MintyCompactDomain.DomainMonotone A →
      ∃ u ∈ K, ∀ v : D, (v : X) ∈ K → A v (u-v) ≤ 0

end Specs.ExpandedFA.Geometry.MintySignCounterexamples
