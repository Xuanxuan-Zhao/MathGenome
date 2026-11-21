import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.LocalLipschitz
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Monotone

/-! Independent statements for the quotient and sublinearity clauses of
`paper.tex`, Proposition `prop:directional-support`, lines 1108–1142.
Only positive times are used. At such times the quotient below is precisely
`(toEReal (f (x + t • d)) - toEReal (f x)) * (t⁻¹ : ℝ)` when `f x` is finite.
The explicit infinity branch avoids any convention at nonpositive times.
The real representative is used only after its finiteness is proved. -/
noncomputable section
open Set Filter Topology
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

def directionalQuotientType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], (E → WithTop ℝ) → E → E → ℝ → EReal

def directionalQuotient {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (x d : E) (t : ℝ) : EReal :=
  if f (x + t • d) = ⊤ then ⊤
  else (((f (x + t • d)).untopD 0 - (f x).untopD 0) / t : ℝ)

def directionalDerivativeType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], (E → WithTop ℝ) → E → E → EReal

def directionalDerivative {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (x d : E) : EReal :=
  ⨅ t : {t : ℝ // 0 < t}, directionalQuotient f x d t

def realDirectionalDerivativeType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], (E → WithTop ℝ) → E → E → ℝ

def realDirectionalDerivative {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (x d : E) : ℝ := (directionalDerivative f x d).toReal

def directionalQuotient_eq : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (f : E → WithTop ℝ)
    (x d : E), f x < ⊤ → ∀ t : ℝ, 0 < t →
    directionalQuotient f x d t =
      (toEReal (f (x + t • d)) - toEReal (f x)) * (t⁻¹ : ℝ)

def directionalQuotient_monotone : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (f : E → WithTop ℝ),
    Proper f → IsConvex f → ∀ x : E, f x < ⊤ → ∀ d : E,
    MonotoneOn (directionalQuotient f x d) (Ioi 0)

def directionalQuotient_tendsto : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (f : E → WithTop ℝ),
    Proper f → IsConvex f → ∀ x : E, f x < ⊤ → ∀ d : E,
    Tendsto (directionalQuotient f x d) (𝓝[>] 0) (𝓝 (directionalDerivative f x d))

/-- Every local Lipschitz constant bounds the derivative, on all directions.
The real representative is finite, Lipschitz, and sublinear. -/
def directionalDerivative_of_localLipschitz : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → WithTop ℝ), Proper f → IsConvex f → ∀ (x : E) (U : Set E)
    (K : NNReal), U ∈ 𝓝 x → (∀ y ∈ U, f y < ⊤) →
    LipschitzOnWith K (fun y => (f y).untopD 0) U →
    (∀ d, directionalDerivative f x d = (realDirectionalDerivative f x d : EReal)) ∧
    LipschitzWith K (realDirectionalDerivative f x) ∧
    realDirectionalDerivative f x 0 = 0 ∧
    (∀ (a : ℝ), 0 ≤ a → ∀ d, realDirectionalDerivative f x (a • d) =
      a * realDirectionalDerivative f x d) ∧
    (∀ d e, realDirectionalDerivative f x (d + e) ≤
      realDirectionalDerivative f x d + realDirectionalDerivative f x e) ∧
    (∀ d, |realDirectionalDerivative f x d| ≤ (K : ℝ) * ‖d‖)

/-- The original neighborhood hypothesis, with no dimensional or completeness
assumption. Continuity of the finite representative is norm continuity. -/
def directionalDerivative_continuous_sublinear : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → WithTop ℝ), Proper f → IsConvex f → ∀ x : E,
    (∃ V : Set E, V ∈ 𝓝 x ∧ (∀ y ∈ V, f y < ⊤) ∧
      ContinuousOn (fun y => (f y).untopD 0) V) →
    (∀ d, directionalDerivative f x d = (realDirectionalDerivative f x d : EReal)) ∧
    Continuous (realDirectionalDerivative f x) ∧
    realDirectionalDerivative f x 0 = 0 ∧
    (∀ (a : ℝ), 0 ≤ a → ∀ d, realDirectionalDerivative f x (a • d) =
      a * realDirectionalDerivative f x d) ∧
    (∀ d e, realDirectionalDerivative f x (d + e) ≤
      realDirectionalDerivative f x d + realDirectionalDerivative f x e) ∧
    ∃ U : Set E, U ∈ 𝓝 x ∧ ∃ K : NNReal,
      (∀ y ∈ U, f y < ⊤) ∧ LipschitzOnWith K (fun y => (f y).untopD 0) U ∧
      ∀ d, |realDirectionalDerivative f x d| ≤ (K : ℝ) * ‖d‖

end VariationalNotes.ConvexAnalysis.Specs
