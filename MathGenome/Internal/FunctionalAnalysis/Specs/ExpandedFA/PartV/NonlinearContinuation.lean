import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonlinearVolterra
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Continuation part of `fa2:p5:nonlinear-volterra`, paper.tex:22197–22223.
Time is real and finite. Solutions on `[0,b)` are represented by arbitrary
ambient functions; their values outside that interval have no significance.
The closed triangle and all state balls use the original norm topology. -/
noncomputable section
namespace ExpandedFA.PartV.NonlinearContinuation
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]

/-- Bounds and Lipschitz constants may depend on the state radius, uniformly
on the entire available time triangle. Balls centered at zero exhaust all
bounded state sets, equivalently one may center them at `f 0`. -/
def LocalBounds {T : ℝ} (G : C(volterraTriangle 0 T × E, E)) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧
    (∀ p z, ‖z‖ ≤ R → ‖G (p,z)‖ ≤ B) ∧
    (∀ p z w, ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖G (p,z) - G (p,w)‖ ≤ L * ‖z-w‖)

/-- Time continuity uniform over each bounded state ball. It is not inferred
from continuity on noncompact Banach balls. -/
def UniformTimeOnBalls {T : ℝ} (G : C(volterraTriangle 0 T × E, E)) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (p q : volterraTriangle 0 T) (z : E), ‖z‖ ≤ R → dist p q < δ →
      dist (G (p,z)) (G (q,z)) < ε

variable [NormedSpace ℝ E]

/-- The exact (unnormalized) power-kernel equation. At order one it is the
ordinary integral equation. Retraction only supplies irrelevant values outside
`0 ≤ s ≤ t`, and hence does not change the equation on its domain. -/
def equation {T : ℝ} (α : ℝ) (f : C(VolterraInterval 0 T,E))
    (G : C(volterraTriangle 0 T × E,E)) (u : ℝ → E)
    (t : VolterraInterval 0 T) : Prop :=
  u t = f t + ∫ s in Ioc 0 (t : ℝ),
    ((t : ℝ)-s) ^ (α-1) • G (volterraRetraction t s, u s)

/-- Continuity and the equation at every time before the stopping time,
including zero. There is no assumed endpoint limit or extension. -/
def IsSolution {T : ℝ} (α : ℝ) (f : C(VolterraInterval 0 T,E))
    (G : C(volterraTriangle 0 T × E,E)) (b : ℝ) (u : ℝ → E) : Prop :=
  ContinuousOn u (Ico 0 b) ∧
    ∀ t : VolterraInterval 0 T, (t : ℝ) < b → equation α f G u t

/-- No larger solution on the same available cylinder agrees on the entire
old half-open interval. This is maximality by continuation, not an assumed
blow-up or endpoint nonexistence certificate. -/
def IsMaximal {T : ℝ} (α : ℝ) (f : C(VolterraInterval 0 T,E))
    (G : C(volterraTriangle 0 T × E,E)) (b : ℝ) (u : ℝ → E) : Prop :=
  IsSolution α f G b u ∧
    ∀ c : ℝ, b < c → c ≤ T →
      ¬ ∃ v : ℝ → E, IsSolution α f G c v ∧ EqOn u v (Ico 0 b)

namespace Spec

/-- Full premature-endpoint blow-up criterion for every positive singular
order and for both manuscript scalar fields. No compactness of Banach balls
is assumed. The positive stopping time is the nonempty solution interval;
there is no premature positive stopping time when the available interval is
zero. Unboundedness is an actual quantified norm conclusion. -/
def ContinuationTheorem : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (α T b : ℝ) (_hα : 0 < α) (_hb : 0 < b) (_hbT : b < T)
  (f : C(VolterraInterval 0 T,E)) (G : C(volterraTriangle 0 T × E,E)) (u : ℝ → E),
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  LocalBounds G → UniformTimeOnBalls G → IsMaximal α f G b u →
    ∀ M : ℝ, ∃ t ∈ Ico 0 b, M < ‖u t‖

/-- Ordinary continuity suffices for the time-uniformity assumption in finite
dimension, because the actual triangle times a closed norm ball is compact. -/
def FiniteDimensionalUniformity : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  (T : ℝ) (G : C(volterraTriangle 0 T × E,E)), UniformTimeOnBalls G

end Spec
end ExpandedFA.PartV.NonlinearContinuation
