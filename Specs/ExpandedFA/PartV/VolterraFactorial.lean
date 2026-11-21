import Specs.ExpandedFA.PartV.VolterraOperator
import Mathlib.Analysis.Normed.Operator.Basic

/-! Independent statements for the estimate and ordered-integral assertions of
`fa2:p5:volterra-resolvent` (paper.tex:21872–21907). The spectral conclusion is allocated separately.
The kernel maximum is the native supremum norm `‖k‖`, identified with the
attained maximum by the upstream kernel-maximum theorem. -/
noncomputable section
namespace ExpandedFA.PartV
open Set MeasureTheory

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E

/-- Nested ordered integrals, with an accumulated product `A` on the left.
At each stage the new factor is appended on the RIGHT: `A.comp k(t,s)`.
Starting with `A = id` therefore gives the integrand
`k(t,s₁)(k(s₁,s₂)(…(k(sₙ₋₁,sₙ)(u sₙ))…))`.
The projections only extend integrands outside their integration intervals;
for `a ≤ s ≤ t` they fix the original points. No iterate of `V` occurs in
this definition. The zero-fold integral is `A (u t)`. -/
def volterraOrderedIntegral {a b : ℝ} (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E))
    (u : C(VolterraInterval a b, E)) :
    ℕ → (E →L[𝕜] E) → VolterraInterval a b → E
  | 0, A, t => A (u t)
  | n + 1, A, t => ∫ s in a..(t : ℝ),
      volterraOrderedIntegral hab k u n
        (A.comp (k (volterraRetraction t s))) (Set.projIcc a b hab s)
end

namespace VolterraFactorialSpec

def PointwiseEstimate : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (n : ℕ) (u : C(VolterraInterval a b, E)) (t : VolterraInterval a b),
  ‖((VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n) u t‖ ≤
    ‖k‖ ^ n * ((t : ℝ) - a) ^ n / (n.factorial : ℝ) * ‖u‖

def OperatorEstimate : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)) (n : ℕ),
  ‖(VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n‖ ≤
    ‖k‖ ^ n * (b - a) ^ n / (n.factorial : ℝ)

/-- The estimate for any uniform bound `M` as stated in the paper.
The nonempty triangle implies `M ≥ 0`; it need not be assumed separately.
Taking `a = 0`, `b = T` gives `M^n T^n / n!` for every `T ≥ 0`.
Both powers use the zero-fold identity convention, including `a = b`. -/
def UniformOperatorEstimate : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (M : ℝ), (∀ p, ‖k p‖ ≤ M) → ∀ n : ℕ,
  ‖(VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n‖ ≤
    M ^ n * (b - a) ^ n / (n.factorial : ℝ)

def UniformPointwiseEstimate : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (M : ℝ), (∀ p, ‖k p‖ ≤ M) → ∀ (n : ℕ)
  (u : C(VolterraInterval a b, E)) (t : VolterraInterval a b),
  ‖((VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n) u t‖ ≤
    M ^ n * ((t : ℝ) - a) ^ n / (n.factorial : ℝ) * ‖u‖

/-- The equality includes the zero-fold identity, also on singleton intervals.
The accumulated-operator version is useful for inspecting composition order. -/
def OrderedIntegralFormula : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (n : ℕ) (u : C(VolterraInterval a b, E)) (t : VolterraInterval a b),
  ((VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) ^ n) u t =
    volterraOrderedIntegral hab k u n (ContinuousLinearMap.id 𝕜 E) t

/-- Every integration in the recursive ordered formula is a genuine integral
of a continuous Banach-valued function. No integrability certificate is assumed. -/
def OrderedIntegralsExist : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (n : ℕ) (u : C(VolterraInterval a b, E)) (A : E →L[𝕜] E)
  (t : VolterraInterval a b),
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  let f := fun s : ℝ => volterraOrderedIntegral hab k u n
    (A.comp (k (volterraRetraction t s))) (Set.projIcc a b hab s)
  Continuous f ∧ IntervalIntegrable f volume a (t : ℝ)

/-- Inside every integration interval the extensions in the recursive formula
are precisely the original triangle and interval points. Iterating this identity
exhibits the domain `a ≤ sₙ ≤ ⋯ ≤ s₁ ≤ t`. -/
def OrderedIntegrandRestriction : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (n : ℕ) (u : C(VolterraInterval a b, E)) (A : E →L[𝕜] E)
  (t : VolterraInterval a b) (s : ℝ) (hs : s ∈ Icc a (t : ℝ)),
  volterraOrderedIntegral hab k u n (A.comp (k (volterraRetraction t s)))
    (Set.projIcc a b hab s) =
  volterraOrderedIntegral hab k u n
    (A.comp (k ⟨((t : ℝ), s), hs.1, hs.2, t.property.2⟩))
    ⟨s, hs.1, hs.2.trans t.property.2⟩

end VolterraFactorialSpec
end ExpandedFA.PartV
