import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.LocalLipschitz
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Order.IsLUB

/-! Independent statements of paper.tex, d13:04:continuation.
An extended-real opposite endpoint allows either a bounded interval or a ray.
The finite endpoint is real. Graph convergence is to a point of the original
open domain; boundedness of the state alone is never a hypothesis here.
-/
noncomputable section
open Set Filter
open scoped Topology
open D13Unified
open Specs.D13Unified.Ch01.SolutionConcepts

namespace Specs.D13Unified.Ch04.Continuation
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A strictly increasing sequence of actual solution times with admissible
limit of its time-state graph. -/
def RightCluster (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E) (b : ℝ) (η : E) : Prop :=
  (b, η) ∈ F.domain ∧ ∃ t : ℕ → ℝ, StrictMono t ∧
    (∀ j, t j ∈ I.carrier) ∧ Tendsto (fun j => (t j, x (t j))) atTop (𝓝 (b, η))

/-- The precise reversed sequence approaches the finite left endpoint from
inside the original interval. -/
def LeftCluster (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E) (a : ℝ) (η : E) : Prop :=
  (a, η) ∈ F.domain ∧ ∃ t : ℕ → ℝ, StrictAnti t ∧
    (∀ j, t j ∈ I.carrier) ∧ Tendsto (fun j => (t j, x (t j))) atTop (𝓝 (a, η))

/-- Extension on exactly `(a,b+ε)`, agreeing on the whole original interval. -/
def RightExtension (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E)
    (a : EReal) (b : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ (J : OpenTimeInterval) (y : ℝ → E),
    J.carrier = {t : ℝ | a < (t : EReal) ∧ t < b + ε} ∧
    classicalSolutionOnValue F J y ∧ EqOn y x I.carrier

/-- Extension on exactly `(a-ε,b)`, with the opposite endpoint unchanged. -/
def LeftExtension (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E)
    (a : ℝ) (b : EReal) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ (J : OpenTimeInterval) (y : ℝ → E),
    J.carrier = {t : ℝ | a - ε < t ∧ (t : EReal) < b} ∧
    classicalSolutionOnValue F J y ∧ EqOn y x I.carrier

def rightContinuationExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), Ch03.LocalLipschitz.locallyLipschitzInStateValue F →
    ∀ (I : OpenTimeInterval) (x : ℝ → E) (a : EReal) (b : ℝ),
      I.carrier = {t : ℝ | a < (t : EReal) ∧ t < b} →
      classicalSolutionOnValue F I x →
      (RightExtension F I x a b ↔ ∃ η, RightCluster F I x b η)

def leftContinuationExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), Ch03.LocalLipschitz.locallyLipschitzInStateValue F →
    ∀ (I : OpenTimeInterval) (x : ℝ → E) (a : ℝ) (b : EReal),
      I.carrier = {t : ℝ | a < t ∧ (t : EReal) < b} →
      classicalSolutionOnValue F I x →
      (LeftExtension F I x a b ↔ ∃ η, LeftCluster F I x a η)

/-- The limit is along all times approaching from the left, and every
extension through the endpoint has exactly the specified limiting value. -/
def rightLimitExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), Ch03.LocalLipschitz.locallyLipschitzInStateValue F →
    ∀ (I : OpenTimeInterval) (x : ℝ → E) (a : EReal) (b : ℝ),
      I.carrier = {t : ℝ | a < (t : EReal) ∧ t < b} →
      classicalSolutionOnValue F I x → ∀ η, RightCluster F I x b η →
      Tendsto x (𝓝[<] b) (𝓝 η) ∧
      ∀ (J : OpenTimeInterval) (y : ℝ → E), b ∈ J.carrier →
        classicalSolutionOnValue F J y → EqOn y x I.carrier → y b = η

def leftLimitExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), Ch03.LocalLipschitz.locallyLipschitzInStateValue F →
    ∀ (I : OpenTimeInterval) (x : ℝ → E) (a : ℝ) (b : EReal),
      I.carrier = {t : ℝ | a < t ∧ (t : EReal) < b} →
      classicalSolutionOnValue F I x → ∀ η, LeftCluster F I x a η →
      Tendsto x (𝓝[>] a) (𝓝 η) ∧
      ∀ (J : OpenTimeInterval) (y : ℝ → E), a ∈ J.carrier →
        classicalSolutionOnValue F J y → EqOn y x I.carrier → y a = η

end Specs.D13Unified.Ch04.Continuation
