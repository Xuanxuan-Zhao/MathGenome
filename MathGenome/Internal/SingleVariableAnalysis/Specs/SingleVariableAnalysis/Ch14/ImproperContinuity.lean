import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformImproper
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
K03.14.improper_continuity, paper.tex:3429–3446.
The parameter domain is an arbitrary subset of ℝ. `N` is a relative neighborhood
of the base point; convergence and proper integrability are needed only there.
Truncations are the existing proper Darboux integrals, and the uniform limit
predicate identifies `F` with the improper integral at every parameter in `N`.
Continuity of truncations on `N` at the base point suffices; continuity on the
original parameter domain implies this by restriction. The conclusion is on the
original domain, so arbitrary extensions away from `N` are permitted.
WithTop/WithBot include finite singular endpoints as well as ±∞. The rectangle
specializations supply the sufficient joint-continuity hypothesis of the source,
including relative continuity at parameter endpoints and singleton intervals.
-/
namespace Specs.SingleVariableAnalysis.Ch14.ImproperContinuity
open _root_.SingleVariableAnalysis
open Ch10.OneEndpoint
open UniformImproper
open scoped Topology

def rightContinuity : Prop :=
  ∀ (k : ScalarKind) {T : Set ℝ} (N : Set T) (t₀ : N),
    N ∈ 𝓝 t₀.val → ∀ (f : ℝ → T → S.scalarValue k)
      (a : ℝ) (b : WithTop ℝ) (F : T → S.scalarValue k)
      (h : rightFamilyRegularValue k N (fun x t => f x t.val) a b),
    rightUniformHasIntegralValue k N (fun x t => f x t.val) a b (fun t => F t.val) →
    (∀ R : rightIndexValue a b,
      ContinuousAt (fun t : N =>
        rightTruncationValue k (fun x => f x t.val) a b (h.2 t) R) t₀) →
    ContinuousAt F t₀.val

def leftContinuity : Prop :=
  ∀ (k : ScalarKind) {T : Set ℝ} (N : Set T) (t₀ : N),
    N ∈ 𝓝 t₀.val → ∀ (f : ℝ → T → S.scalarValue k)
      (a : WithBot ℝ) (b : ℝ) (F : T → S.scalarValue k)
      (h : leftFamilyRegularValue k N (fun x t => f x t.val) a b),
    leftUniformHasIntegralValue k N (fun x t => f x t.val) a b (fun t => F t.val) →
    (∀ R : leftIndexValue a b,
      ContinuousAt (fun t : N =>
        leftTruncationValue k (fun x => f x t.val) a b (h.2 t) R) t₀) →
    ContinuousAt F t₀.val

def rightRectangleContinuity : Prop :=
  ∀ (k : ScalarKind) {c d : ℝ}, c ≤ d →
    ∀ (N : Set (Set.Icc c d)) (t₀ : N), N ∈ 𝓝 t₀.val →
    ∀ (f : ℝ → Set.Icc c d → S.scalarValue k)
      (a : ℝ) (b : WithTop ℝ) (F : Set.Icc c d → S.scalarValue k),
    rightUniformHasIntegralValue k N (fun x t => f x t.val) a b (fun t => F t.val) →
    (∀ R : rightIndexValue a b,
      Continuous (fun p : Set.Icc a R.val × Set.Icc c d => f p.1.val p.2)) →
    ContinuousAt F t₀.val

def leftRectangleContinuity : Prop :=
  ∀ (k : ScalarKind) {c d : ℝ}, c ≤ d →
    ∀ (N : Set (Set.Icc c d)) (t₀ : N), N ∈ 𝓝 t₀.val →
    ∀ (f : ℝ → Set.Icc c d → S.scalarValue k)
      (a : WithBot ℝ) (b : ℝ) (F : Set.Icc c d → S.scalarValue k),
    leftUniformHasIntegralValue k N (fun x t => f x t.val) a b (fun t => F t.val) →
    (∀ R : leftIndexValue a b,
      Continuous (fun p : Set.Icc R.val b × Set.Icc c d => f p.1.val p.2)) →
    ContinuousAt F t₀.val

end Specs.SingleVariableAnalysis.Ch14.ImproperContinuity
