import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

/-! Independent specification of the continuous-kernel Volterra construction in
paper.tex, fa2:p5:volterra-resolvent (21872–21907).

We give the slightly more general interval `[a,b]`; setting `a = 0`, `b = T`
recovers the source interval for every `0 ≤ T`. The domain is the actual closed
triangle, the kernel is continuous in operator norm, and the function space has
its native supremum norm. No separability, finite-dimensionality, or
commutativity of operator values is required. The interval `[a,a]` is a singleton.
-/
noncomputable section
namespace ExpandedFA.PartV
open Set MeasureTheory

abbrev VolterraInterval (a b : ℝ) := Set.Icc a b

def volterraTriangle (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ b}

instance triangleCompactSpace (a b : ℝ) : CompactSpace (volterraTriangle a b) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst continuous_const))
  · intro p hp
    exact ⟨⟨hp.1.trans hp.2.1, hp.2.2⟩, ⟨hp.1, hp.2.1.trans hp.2.2⟩⟩

/-- A continuous retraction in the integration variable. It fixes `(t,s)`
whenever `a ≤ s ≤ t`; no extension by zero across the diagonal is used. -/
def volterraRetraction {a b : ℝ} (t : VolterraInterval a b) (s : ℝ) :
    volterraTriangle a b :=
  ⟨(t, max a (min (t : ℝ) s)),
    le_max_left _ _, max_le t.property.1 (min_le_left _ _), t.property.2⟩

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E

/-- A globally defined integrand whose restriction to `[a,t]` is exactly
`k(t,s)u(s)`. The second projection simply extends `u` constantly beyond `I`. -/
def volterraIntegrand {a b : ℝ} (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E))
    (u : C(VolterraInterval a b, E)) (t : VolterraInterval a b) (s : ℝ) : E :=
  k (volterraRetraction t s) (u (Set.projIcc a b hab s))

noncomputable def volterraIntegralValue {a b : ℝ} (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E))
    (u : C(VolterraInterval a b, E)) (t : VolterraInterval a b) : E :=
  ∫ s in a..(t : ℝ), volterraIntegrand hab k u t s

end

namespace VolterraOperatorSpec

/-- The integral, with the canonical real restriction of scalars. -/
def IntegralType := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (a b : ℝ) (_hab : a ≤ b),
  C(volterraTriangle a b, E →L[𝕜] E) →
  C(VolterraInterval a b, E) → VolterraInterval a b → E

noncomputable def IntegralValue : IntegralType :=
  fun _ _ _ _ _ _ _ hab k u t => volterraIntegralValue hab k u t

/-- The operator itself has no extra regularity or boundedness premises. -/
def OperatorType := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (_hab : a ≤ b) (_k : C(volterraTriangle a b, E →L[𝕜] E)),
  C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E)

/-- Select the bounded linear map having the integral formula. Existence is a
proof obligation, discharged in the implementation; it is not a hypothesis of
this definition or any theorem Spec. Uniqueness follows from the formula. -/
noncomputable def OperatorValue : OperatorType :=
  fun _ _ _ _ _ _ _ _ hab k => Classical.epsilon
    (fun V : C(VolterraInterval _ _, _) →L[_] C(VolterraInterval _ _, _) =>
      ∀ u t, V u t = volterraIntegralValue hab k u t)

/-- Laws of the selected concrete operator, as well as its existence below. -/
def OperatorProperties : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)),
  let V := OperatorValue 𝕜 E a b hab k
  (∀ u t, V u t = volterraIntegralValue hab k u t) ∧
  (∀ u t, ‖V u t‖ ≤ ‖k‖ * ((t : ℝ) - a) * ‖u‖) ∧
  ‖V‖ ≤ ‖k‖ * (b - a)

def KernelMaximum : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (a b : ℝ), a ≤ b →
  ∀ k : C(volterraTriangle a b, E →L[𝕜] E),
    0 ≤ ‖k‖ ∧ (∀ p, ‖k p‖ ≤ ‖k‖) ∧ ∃ p, ‖k p‖ = ‖k‖

def IntegralsExist : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (u : C(VolterraInterval a b, E)),
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  (∀ t, Continuous (volterraIntegrand hab k u t) ∧
    IntervalIntegrable (volterraIntegrand hab k u t) volume a (t : ℝ)) ∧
  (∀ (t : VolterraInterval a b) (s : ℝ) (hs : s ∈ Icc a (t : ℝ)),
    volterraIntegrand hab k u t s =
      k ⟨((t : ℝ), s), hs.1, hs.2, t.property.2⟩
        (u ⟨s, hs.1, hs.2.trans t.property.2⟩))

def IntegralContinuous : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (u : C(VolterraInterval a b, E)), Continuous (volterraIntegralValue hab k u)

/-- Construction of the bounded linear map, including both quantitative bounds.
Its displayed value is a Bochner integral of the original continuous integrand. -/
def OperatorConstruction : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)),
  ∃ V : C(VolterraInterval a b, E) →L[𝕜] C(VolterraInterval a b, E),
    (∀ u t, V u t = volterraIntegralValue hab k u t) ∧
    (∀ u t, ‖V u t‖ ≤ ‖k‖ * ((t : ℝ) - a) * ‖u‖) ∧
    ‖V‖ ≤ ‖k‖ * (b - a)

/-- Uniform kernel bounds give the source's `M (b-a)` operator bound.
Nonnegativity of `M` follows from the nonempty triangle; it is not an added
hypothesis. In particular `a=0, b=T` gives `‖V‖ ≤ M*T`. -/
def OperatorBound : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (M : ℝ), (∀ p, ‖k p‖ ≤ M) →
    ‖OperatorValue 𝕜 E a b hab k‖ ≤ M * (b - a)

def SingletonZero : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a : ℝ) (k : C(volterraTriangle a a, E →L[𝕜] E)),
  OperatorValue 𝕜 E a a (le_refl a) k = 0

def SingletonEvaluation : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (a : ℝ),
  ∃ e : C(VolterraInterval a a, E) ≃ₗᵢ[𝕜] E,
    (∀ u, e u = u ⟨a, le_rfl, le_rfl⟩) ∧
    (∀ x t, e.symm x t = x)

/-- Completeness and the actual supremum norm on Banach-valued functions.
The uniform bridge records compatibility with bounded continuous functions. -/
def BanachFunctionSpace : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (a b : ℝ),
  CompleteSpace C(VolterraInterval a b, E) ∧
  (∀ u : C(VolterraInterval a b, E), ‖u‖ = ⨆ t, ‖u t‖) ∧
  IsUniformInducing (ContinuousMap.equivBoundedOfCompact (VolterraInterval a b) E)

end VolterraOperatorSpec
end ExpandedFA.PartV
