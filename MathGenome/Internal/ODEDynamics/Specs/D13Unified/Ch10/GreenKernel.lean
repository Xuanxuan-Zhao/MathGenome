import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.RegularProblem
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.EvolutionMatrix
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! Independent statements for paper.tex, d13:10:green, kernel construction
and continuous forcing. The Hilbert-space assertions are allocated elsewhere.
All representatives have conditions only on the original nondegenerate [a,b].
The modes are defined from the upstream normalized IVP, not from a certificate
of positivity, a boundary inverse, or any of the conclusions below. -/
noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace D13Unified.Ch10.GreenKernel
abbrev Problem := Specs.D13Unified.Ch10.RegularProblem.Problem
abbrev interval := Specs.D13Unified.Ch10.RegularProblem.intervalValue

def Q (P : Problem) (c x : ℝ) : ℝ := P.q x + c * P.w x

def timeInterval (P : Problem) : TimeInterval :=
  ⟨interval P, nonempty_Icc.mpr P.a_lt_b.le, ordConnected_Icc⟩

/-- The equation for the state (y, p y′). -/
def systemMatrix (P : Problem) (c x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, (P.p x)⁻¹; Q P c x, 0]

/-- Left normalized mode: y(a)=0, (p y′)(a)=1. -/
def leftMode (P : Problem) (c x : ℝ) : ℝ :=
  Ch07.EvolutionMatrix.U (timeInterval P) (systemMatrix P c) x P.a 0 1

def leftFlux (P : Problem) (c x : ℝ) : ℝ :=
  Ch07.EvolutionMatrix.U (timeInterval P) (systemMatrix P c) x P.a 1 1

/-- Right normalized mode: y(b)=0, (p y′)(b)=−1. -/
def rightMode (P : Problem) (c x : ℝ) : ℝ :=
  -Ch07.EvolutionMatrix.U (timeInterval P) (systemMatrix P c) x P.b 0 1

def rightFlux (P : Problem) (c x : ℝ) : ℝ :=
  -Ch07.EvolutionMatrix.U (timeInterval P) (systemMatrix P c) x P.b 1 1

/-- Evaluation at a of the normalized Wronskian; equality at every x is proved. -/
def denominator (P : Problem) (c : ℝ) : ℝ := rightMode P c P.a

def wronskian (P : Problem) (c x : ℝ) : ℝ :=
  P.p x * (derivWithin (leftMode P c) (interval P) x * rightMode P c x -
    leftMode P c x * derivWithin (rightMode P c) (interval P) x)

def kernel (P : Problem) (c x t : ℝ) : ℝ :=
  leftMode P c (min x t) * rightMode P c (max x t) / denominator P c

/-- Real time, with either real or complex forcing. -/
def applyKernel {𝕂 : Type} [RCLike 𝕂] (P : Problem) (c : ℝ)
    (f : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ t in P.a..P.b, (kernel P c x t : 𝕂) * f t * (P.w t : 𝕂)

/-- Actual C² Dirichlet solutions, with one-sided derivatives at a and b. -/
def IsDirichletSolution {𝕂 : Type} [RCLike 𝕂] (P : Problem) (c : ℝ)
    (f y : ℝ → 𝕂) : Prop :=
  ContDiffOn ℝ 2 y (interval P) ∧ y P.a = 0 ∧ y P.b = 0 ∧
    ∀ x ∈ interval P,
      -derivWithin (fun t => (P.p t : 𝕂) * derivWithin y (interval P) t)
          (interval P) x + (Q P c x : 𝕂) * y x = (P.w x : 𝕂) * f x

end D13Unified.Ch10.GreenKernel

namespace Specs.D13Unified.Ch10.GreenKernel
open _root_.D13Unified.Ch10.GreenKernel

/-- Existence of a strictly positive scalar shift under exactly the standing
regular-problem hypotheses. -/
def ShiftExists : Prop := ∀ P : Problem,
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ interval P, 1 ≤ Q P c x

/-- Whole-interval homogeneous equations and the two normalizations. This
holds for every real c; positivity is asserted separately for Q≥1. -/
def Modes : Prop := ∀ (P : Problem) (c : ℝ),
  ContDiffOn ℝ 2 (leftMode P c) (interval P) ∧
  ContDiffOn ℝ 2 (rightMode P c) (interval P) ∧
  leftMode P c P.a = 0 ∧ rightMode P c P.b = 0 ∧
  P.p P.a * derivWithin (leftMode P c) (interval P) P.a = 1 ∧
  P.p P.b * derivWithin (rightMode P c) (interval P) P.b = -1 ∧
  (∀ x ∈ interval P,
    -derivWithin (fun t => P.p t * derivWithin (leftMode P c) (interval P) t)
      (interval P) x + Q P c x * leftMode P c x = 0) ∧
  (∀ x ∈ interval P,
    -derivWithin (fun t => P.p t * derivWithin (rightMode P c) (interval P) t)
      (interval P) x + Q P c x * rightMode P c x = 0)

def PositiveModes : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  (∀ x ∈ Ioc P.a P.b, 0 < leftMode P c x) ∧
  (∀ x ∈ Ico P.a P.b, 0 < rightMode P c x) ∧
  0 < denominator P c ∧
  ∀ x ∈ interval P, wronskian P c x = denominator P c

def KernelContinuity : Prop := ∀ (P : Problem) (c : ℝ),
  ContinuousOn (fun z : ℝ × ℝ => kernel P c z.1 z.2) ((interval P) ×ˢ (interval P))

def KernelSymmetry : Prop := ∀ (P : Problem) (c x t : ℝ),
  kernel P c x t = kernel P c t x

def KernelBoundary : Prop := ∀ (P : Problem) (c : ℝ) (t : ℝ),
  t ∈ interval P → kernel P c P.a t = 0 ∧ kernel P c P.b t = 0

def KernelPositivity : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  ∀ x ∈ Ioo P.a P.b, ∀ t ∈ Ioo P.a P.b, 0 < kernel P c x t

/-- The displayed numbers are the actual one-sided x-derivatives, and their
flux jump is −1. No derivative across the diagonal is postulated. -/
def KernelJump : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) → ∀ t ∈ Ioo P.a P.b,
  let dm := derivWithin (leftMode P c) (interval P) t * rightMode P c t /
    denominator P c
  let dp := leftMode P c t * derivWithin (rightMode P c) (interval P) t /
    denominator P c
  HasDerivWithinAt (fun x => kernel P c x t) dm (Icc P.a t) t ∧
  HasDerivWithinAt (fun x => kernel P c x t) dp (Icc t P.b) t ∧
  P.p t * (dp - dm) = -1

/-- Existence and uniqueness for every continuous forcing, over ℝ and ℂ.
Uniqueness concerns the actual interval, not ambient representatives. -/
def InverseContinuous : Prop := ∀ (𝕂 : Type) [RCLike 𝕂]
  (P : Problem) (c : ℝ), 0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  ∀ f : ℝ → 𝕂, ContinuousOn f (interval P) →
  IsDirichletSolution P c f (applyKernel P c f) ∧
  ∀ y : ℝ → 𝕂, IsDirichletSolution P c f y → EqOn y (applyKernel P c f) (interval P)

end Specs.D13Unified.Ch10.GreenKernel
