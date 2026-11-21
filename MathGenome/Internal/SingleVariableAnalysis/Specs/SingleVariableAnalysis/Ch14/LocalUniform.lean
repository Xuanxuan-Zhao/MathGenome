import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ImproperDerivative
import Mathlib.Order.Interval.Set.OrdConnected

/-!
K03.14.local_uniform, paper.tex:3513–3536.
All integrals below are cofinal limits of the original proper Darboux integrals.
The parameter set is open; `OrdConnected` is needed only for propagation from
one base point. It includes unbounded intervals and the empty interval.

Ambient functions are representatives on ℝ; no condition is imposed off J.
The bundled proper hypotheses say precisely that the actual truncations are
continuous, and, for differentiation, have the stated proper integral derivative.
Uniform convergence is required separately on each compact subinterval, with
its own cutoff. No continuity of the limiting derivative is assumed.
-/
namespace Specs.SingleVariableAnalysis.Ch14.LocalUniform
open Set _root_.SingleVariableAnalysis
open Ch10.OneEndpoint Ch14.UniformImproper

/-- Proper truncations of a family on an open parameter domain. -/
structure ProperFamily (k : ScalarKind) (a : ℝ) (J : Set ℝ)
    (f : ℝ → ℝ → S.scalarValue k)
    (FR : rightIndexValue a ⊤ → ℝ → S.scalarValue k) : Prop where
  regular : rightFamilyRegularValue k J (fun x t => f x t.val) a ⊤
  equation : ∀ R (t : J), FR R t =
    rightTruncationValue k (fun x => f x t) a ⊤ (regular.2 t) R
  continuous : ∀ R, ContinuousOn (FR R) J

/-- Proper differentiation, without assuming the improper integrals exist. -/
structure ProperDerivativeFamily (k : ScalarKind) (a : ℝ) (J : Set ℝ)
    (f ft : ℝ → ℝ → S.scalarValue k)
    (FR D : rightIndexValue a ⊤ → ℝ → S.scalarValue k)
    : Prop extends ProperFamily k a J f FR where
  derivativeRegular : rightFamilyRegularValue k J (fun x t => ft x t.val) a ⊤
  derivativeEquation : ∀ R (t : J), D R t =
    rightTruncationValue k (fun x => ft x t) a ⊤ (derivativeRegular.2 t) R
  derivative : ∀ R t, t ∈ J → HasDerivAt (FR R) (D R t) t

/-- Actual integral limits, uniformly on every compact parameter interval. -/
def LocalIntegralLimit (k : ScalarKind) (a : ℝ) (J : Set ℝ)
    (f : ℝ → ℝ → S.scalarValue k) (F : ℝ → S.scalarValue k) : Prop :=
  ∀ c d : ℝ, c ≤ d → Icc c d ⊆ J →
    rightUniformHasIntegralValue k (Icc c d) (fun x t => f x t.val) a ⊤
      (fun t => F t.val)

/-- This hypothesis supplies no limit for the original integral family. -/
def LocalDerivativeLimit (k : ScalarKind) (a : ℝ) (J : Set ℝ)
    (D : rightIndexValue a ⊤ → ℝ → S.scalarValue k)
    (G : ℝ → S.scalarValue k) : Prop :=
  ∀ c d : ℝ, c ≤ d → Icc c d ⊆ J → ∀ ε : ℝ, 0 < ε →
    ∃ r : rightIndexValue a ⊤, ∀ R : rightIndexValue a ⊤, r.val < R.val →
      ∀ t ∈ Icc c d, dist (D R t) (G t) < ε

/-- The compact limits need not be supplied as one compatible G. -/
def LocalDerivativeConvergence (k : ScalarKind) (a : ℝ) (J : Set ℝ)
    (D : rightIndexValue a ⊤ → ℝ → S.scalarValue k) : Prop :=
  ∀ c d : ℝ, c ≤ d → Icc c d ⊆ J → ∃ G : ℝ → S.scalarValue k,
    ∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a ⊤,
      ∀ R : rightIndexValue a ⊤, r.val < R.val →
        ∀ t ∈ Icc c d, dist (D R t) (G t) < ε

/-- The common full conclusion of the two differentiation variants. -/
def DerivativeConclusion (k : ScalarKind) (a : ℝ) (J : Set ℝ)
    (f ft : ℝ → ℝ → S.scalarValue k) (G : ℝ → S.scalarValue k) : Prop :=
  ∃ F : ℝ → S.scalarValue k,
    LocalIntegralLimit k a J f F ∧
    (∀ t ∈ J, rightHasIntegralValue k (fun x => f x t) a ⊤ (F t)) ∧
    ContinuousOn F J ∧
    (∀ t ∈ J, HasDerivAt F (G t) t) ∧
    (∀ t ∈ J, rightHasIntegralValue k (fun x => ft x t) a ⊤ (G t))

/-- Uniform limits on compact intervals need not initially be supplied as one
compatible global function. Uniqueness patches them into that function. -/
def localContinuity : Prop :=
  ∀ (k : ScalarKind) (a : ℝ) (J : Set ℝ), IsOpen J →
    ∀ (f : ℝ → ℝ → S.scalarValue k)
      (FR : rightIndexValue a ⊤ → ℝ → S.scalarValue k),
    ProperFamily k a J f FR →
    (∀ c d : ℝ, c ≤ d → Icc c d ⊆ J →
      rightUniformConvergesValue k (Icc c d) (fun x t => f x t.val) a ⊤) →
    ∃ F : ℝ → S.scalarValue k,
      LocalIntegralLimit k a J f F ∧
      (∀ t ∈ J, rightHasIntegralValue k (fun x => f x t) a ⊤ (F t)) ∧
      ContinuousOn F J

def localDifferentiationWithLimit : Prop :=
  ∀ (k : ScalarKind) (a : ℝ) (J : Set ℝ), IsOpen J →
    ∀ (f ft : ℝ → ℝ → S.scalarValue k)
      (FR D : rightIndexValue a ⊤ → ℝ → S.scalarValue k)
      (G : ℝ → S.scalarValue k),
    ProperDerivativeFamily k a J f ft FR D → LocalDerivativeLimit k a J D G →
    (∀ c d : ℝ, c < d → Icc c d ⊆ J →
      ∃ (t₀ : Icc c d) (L : S.scalarValue k),
        rightHasIntegralValue k (fun x => f x t₀.val) a ⊤ L) →
    DerivativeConclusion k a J f ft G

def singleBasePointDifferentiationWithLimit : Prop :=
  ∀ (k : ScalarKind) (a : ℝ) (J : Set ℝ), IsOpen J → OrdConnected J →
    ∀ (f ft : ℝ → ℝ → S.scalarValue k)
      (FR D : rightIndexValue a ⊤ → ℝ → S.scalarValue k)
      (G : ℝ → S.scalarValue k),
    ProperDerivativeFamily k a J f ft FR D → LocalDerivativeLimit k a J D G →
    (∃ (t₀ : J) (L : S.scalarValue k),
      rightHasIntegralValue k (fun x => f x t₀.val) a ⊤ L) →
    DerivativeConclusion k a J f ft G

/-- The local base-point variant, including existence of the derivative-integral
limit from the compact convergence hypotheses alone. -/
def localDifferentiation : Prop :=
  ∀ (k : ScalarKind) (a : ℝ) (J : Set ℝ), IsOpen J →
    ∀ (f ft : ℝ → ℝ → S.scalarValue k)
      (FR D : rightIndexValue a ⊤ → ℝ → S.scalarValue k),
    ProperDerivativeFamily k a J f ft FR D → LocalDerivativeConvergence k a J D →
    (∀ c d : ℝ, c < d → Icc c d ⊆ J →
      ∃ (t₀ : Icc c d) (L : S.scalarValue k),
        rightHasIntegralValue k (fun x => f x t₀.val) a ⊤ L) →
    ∃ G : ℝ → S.scalarValue k, DerivativeConclusion k a J f ft G

/-- The interval variant needs only one base point in the whole domain. -/
def singleBasePointDifferentiation : Prop :=
  ∀ (k : ScalarKind) (a : ℝ) (J : Set ℝ), IsOpen J → OrdConnected J →
    ∀ (f ft : ℝ → ℝ → S.scalarValue k)
      (FR D : rightIndexValue a ⊤ → ℝ → S.scalarValue k),
    ProperDerivativeFamily k a J f ft FR D → LocalDerivativeConvergence k a J D →
    (∃ (t₀ : J) (L : S.scalarValue k),
      rightHasIntegralValue k (fun x => f x t₀.val) a ⊤ L) →
    ∃ G : ℝ → S.scalarValue k, DerivativeConclusion k a J f ft G

end Specs.SingleVariableAnalysis.Ch14.LocalUniform
