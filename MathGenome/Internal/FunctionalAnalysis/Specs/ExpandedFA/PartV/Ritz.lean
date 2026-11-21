import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.PNat.Basic

/-! Independent statements for paper.tex fa2:p5:ritz, 22967–23001.
The energy structure is built on the original module; all comparison norms
are explicitly the original ones. The counterexample uses positive-index ℓ²,
with trial spaces span(e₁,…,eₙ) at 2n and zero at 2n+1. -/
noncomputable section
open scoped InnerProductSpace Topology ComplexConjugate
namespace ExpandedFA.PartV.Ritz.Spec
open ExpandedFA.Hilbert.Conventions.Spec
universe u v

def EnergyHilbertNorm : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [n : NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : BoundedSesquilinearFormValue 𝕜 H H) (M α : ℝ),
    (∀ x y : H, ‖a x y‖ ≤ M * ‖x‖ * ‖y‖) →
    FormCoerciveValue 𝕜 H a α →
    FormHermitianValue 𝕜 H a →
    (∀ x, a x x = (RCLike.re (a x x) : 𝕜) ∧
      0 ≤ RCLike.re (a x x) ∧ (a x x = 0 ↔ x = 0)) ∧
    ∃ c : InnerProductSpace.Core 𝕜 H,
      (∀ x y, c.inner x y = a x y) ∧
      (letI : Module 𝕜 H := inferInstance
       letI := c.toNormedAddCommGroup
       letI := InnerProductSpace.ofCore c.toCore
       ∀ x y : H, ⟪x, y⟫_𝕜 = a x y) ∧
      (∀ x : H,
        let energyNorm := @norm H c.toNormedAddCommGroup.toNorm x
        energyNorm = Real.sqrt (RCLike.re (a x x)) ∧
        Real.sqrt α * ‖x‖ ≤ energyNorm ∧
        energyNorm ≤ Real.sqrt M * ‖x‖) ∧
      @CompleteSpace H c.toNormedAddCommGroup.toMetricSpace.toUniformSpace ∧
      c.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace =
        n.toMetricSpace.toUniformSpace.toTopologicalSpace

def EnergyProjection : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [n : NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : BoundedSesquilinearFormValue 𝕜 H H) (M α : ℝ),
    (∀ x y : H, ‖a x y‖ ≤ M * ‖x‖ * ‖y‖) → FormCoerciveValue 𝕜 H a α →
    FormHermitianValue 𝕜 H a →
    ∀ (F : H →L⋆[𝕜] 𝕜) (W : Submodule 𝕜 H), IsClosed (W : Set H) →
    ∀ (u : H) (u_h : W),
      (∀ v : H, a v u = F v) →
      (∀ v : W, a (v : H) (u_h : H) = F (v : H)) →
      ∃ c : InnerProductSpace.Core 𝕜 H,
        (∀ x y, c.inner x y = a x y) ∧
        (∀ x : H,
          let energyNorm := @norm H c.toNormedAddCommGroup.toNorm x
          energyNorm = Real.sqrt (RCLike.re (a x x)) ∧
          Real.sqrt α * ‖x‖ ≤ energyNorm ∧ energyNorm ≤ Real.sqrt M * ‖x‖) ∧
        (∃ hcomplete : @CompleteSpace H c.toNormedAddCommGroup.toMetricSpace.toUniformSpace,
        c.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace =
          n.toMetricSpace.toUniformSpace.toTopologicalSpace ∧
        (letI : Module 𝕜 H := inferInstance
         letI := c.toNormedAddCommGroup
         letI := InnerProductSpace.ofCore c.toCore
         letI : CompleteSpace H := hcomplete
         (∀ x y : H, ⟪x, y⟫_𝕜 = a x y) ∧
         ∃ hW : IsClosed (W : Set H),
           letI : CompleteSpace W := hW.isComplete.completeSpace_coe
           W.starProjection u = (u_h : H)))

/-- Pythagoras, the attained energy minimum, and uniqueness of best approximation. -/
def EnergyBestApproximation : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : BoundedSesquilinearFormValue 𝕜 H H) (M α : ℝ),
    (∀ x y : H, ‖a x y‖ ≤ M * ‖x‖ * ‖y‖) → FormCoerciveValue 𝕜 H a α →
    FormHermitianValue 𝕜 H a →
    ∀ (F : H →L⋆[𝕜] 𝕜) (W : Submodule 𝕜 H), IsClosed (W : Set H) →
    ∀ (u : H) (u_h : W),
      (∀ v : H, a v u = F v) →
      (∀ v : W, a (v : H) (u_h : H) = F (v : H)) →
      let d := fun v : W => Real.sqrt (RCLike.re (a (u - (v : H)) (u - (v : H))))
      (∀ v : W, d v ^ 2 = d u_h ^ 2 +
        (Real.sqrt (RCLike.re (a ((u_h : H) - (v : H)) ((u_h : H) - (v : H))))) ^ 2) ∧
      IsLeast (Set.range d) (d u_h) ∧
      (∀ v : W, d v = d u_h ↔ v = u_h) ∧
      (∃! w : W, ∀ v : W, d w ≤ d v)

namespace Counterexample

abbrev Space (𝕜 : Type u) [RCLike 𝕜] :=
  lp (fun _ : ℕ+ => 𝕜) 2

def e (𝕜 : Type u) [RCLike 𝕜] (i : ℕ+) : Space 𝕜 := lp.single 2 i 1

/-- The span of exactly e₁,…,eₙ, with the empty span for n=0. -/
def initialSpan (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : Submodule 𝕜 (Space 𝕜) :=
  Submodule.span 𝕜 (Set.range fun i : Fin n => e 𝕜 ⟨i.val + 1, Nat.succ_pos _⟩)

def trialSpace (𝕜 : Type u) [RCLike 𝕜] (m : ℕ) : Submodule 𝕜 (Space 𝕜) :=
  if m % 2 = 0 then initialSpan 𝕜 (m / 2) else ⊥

def form (𝕜 : Type u) [RCLike 𝕜] :
    BoundedSesquilinearFormValue 𝕜 (Space 𝕜) (Space 𝕜) := innerSL 𝕜

def datum (𝕜 : Type u) [RCLike 𝕜] : Space 𝕜 →L⋆[𝕜] 𝕜 :=
  innerSLFlip 𝕜 (e 𝕜 1)

/-- The actual ambient vectors solving the discrete problems. -/
def discreteSolution (𝕜 : Type u) [RCLike 𝕜] (m : ℕ) : Space 𝕜 :=
  if m % 2 = 0 ∧ 0 < m then e 𝕜 1 else 0

def TrialDescription : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], trialSpace 𝕜 0 = ⊥ ∧
    (∀ n : ℕ, trialSpace 𝕜 (2*n) = initialSpan 𝕜 n) ∧
    (∀ n : ℕ, trialSpace 𝕜 (2*n+1) = ⊥)

def ClosedTrialSpaces : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (m : ℕ),
    FiniteDimensional 𝕜 (trialSpace 𝕜 m) ∧ IsClosed (trialSpace 𝕜 m : Set (Space 𝕜))

def DenseUnion : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], Dense (⋃ m : ℕ, (trialSpace 𝕜 m : Set (Space 𝕜)))

def FormAndData : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    FormBoundValue 𝕜 (Space 𝕜) (Space 𝕜) (form 𝕜) 1 ∧
    FormCoerciveValue 𝕜 (Space 𝕜) (form 𝕜) 1 ∧
    (∀ v u : Space 𝕜, form 𝕜 v u = inner 𝕜 v u) ∧
    (∀ v : Space 𝕜, datum 𝕜 v = inner 𝕜 v (e 𝕜 1))

def ExactSolution : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ v : Space 𝕜, form 𝕜 v (e 𝕜 1) = datum 𝕜 v) ∧
    ∀ u : Space 𝕜, (∀ v, form 𝕜 v u = datum 𝕜 v) → u = e 𝕜 1

def DiscreteSolutions : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (m : ℕ),
    discreteSolution 𝕜 m ∈ trialSpace 𝕜 m ∧
    (∀ v ∈ trialSpace 𝕜 m, form 𝕜 v (discreteSolution 𝕜 m) = datum 𝕜 v) ∧
    (∀ w ∈ trialSpace 𝕜 m,
      (∀ v ∈ trialSpace 𝕜 m, form 𝕜 v w = datum 𝕜 v) → w = discreteSolution 𝕜 m)

def OddSolutions : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ),
    discreteSolution 𝕜 (2*n+1) = 0 ∧
    ‖e 𝕜 1 - discreteSolution 𝕜 (2*n+1)‖ = 1

def Nonconvergence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ Filter.Tendsto (discreteSolution 𝕜) Filter.atTop (nhds (e 𝕜 1))

/-- A fixed positive error remains unavoidable at arbitrarily late indices. -/
def FailureOfEventualApproximation : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ∃ ε : ℝ, 0 < ε ∧
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧
      ∀ v ∈ trialSpace 𝕜 m, ε ≤ ‖e 𝕜 1 - v‖

end Counterexample
end ExpandedFA.PartV.Ritz.Spec
