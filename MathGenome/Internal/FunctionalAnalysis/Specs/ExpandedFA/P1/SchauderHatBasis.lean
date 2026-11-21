import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Basis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Unconditional
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Canonical functions and independent obligations for the hat-function part of
`fa2:p1:schauder-haar`, paper.tex 4380–4404. The domain is the closed real unit
interval, and the codomain is either real or complex. Index zero denotes the
constant function, index one the identity function, and subsequent indices run
through levels n = 0,1,..., each level from left to right. The hats have height
one. In particular, no normalization by an L² norm is used.

The partition for a partial sum includes the endpoints and precisely the
midpoints already inserted, so the interpolation statement includes incomplete
levels. N = 0 gives the zero map, and N = 1 gives the constant f(0).
-/
noncomputable section
open Filter Topology
open scoped BigOperators
universe u
namespace ExpandedFA.P1.SchauderHatBasis.Spec

abbrev Interval := Set.Icc (0 : ℝ) 1
abbrev FunctionSpace (𝕜 : Type u) [RCLike 𝕜] := C(Interval, 𝕜)

/-- The dyadic point k/2^n, with its actual closed-interval membership. -/
def dyadicPoint (n k : ℕ) (hk : k ≤ 2 ^ n) : Interval :=
  ⟨(k : ℝ) / (2 : ℝ) ^ n, by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ n)).mpr
      exact_mod_cast hk⟩

def leftPoint (n : ℕ) (k : Fin (2 ^ n)) : Interval :=
  dyadicPoint n k.val (Nat.le_of_lt k.isLt)

def rightPoint (n : ℕ) (k : Fin (2 ^ n)) : Interval :=
  dyadicPoint n (k.val + 1) k.isLt

def midpoint (n : ℕ) (k : Fin (2 ^ n)) : Interval :=
  dyadicPoint (n + 1) (2 * k.val + 1) (by
    rw [pow_succ]
    omega)

/-- Decode the position after the two initial affine functions. -/
def hatIndex (j : ℕ) : (n : ℕ) × Fin (2 ^ n) :=
  ⟨Nat.log 2 (j + 1), ⟨j + 1 - 2 ^ Nat.log 2 (j + 1), by
    have hlo := Nat.pow_log_le_self 2 (Nat.succ_ne_zero j)
    have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (j + 1)
    rw [pow_succ] at hhi
    omega⟩⟩

/-- The height-one hat on [k/2^n,(k+1)/2^n]. -/
def hat (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (k : Fin (2 ^ n)) :
    FunctionSpace 𝕜 :=
  ⟨fun t => ((max 0 (1 - |(2 : ℝ) ^ (n + 1) * (t : ℝ) -
    (2 * (k.val : ℝ) + 1)|) : ℝ) : 𝕜), by fun_prop⟩

def linearFunction (𝕜 : Type u) [RCLike 𝕜] : FunctionSpace 𝕜 :=
  ⟨fun t => ((t : ℝ) : 𝕜), by fun_prop⟩

/-- 1,t,h₀₀,h₁₀,h₁₁,h₂₀,... . -/
def basis (𝕜 : Type u) [RCLike 𝕜] : ℕ → FunctionSpace 𝕜
  | 0 => 1
  | 1 => linearFunction 𝕜
  | j + 2 => hat 𝕜 (hatIndex j).1 (hatIndex j).2

/-- The new midpoint value minus the old linear interpolant's value. -/
def hatCoefficient {𝕜 : Type u} [RCLike 𝕜] (n : ℕ) (k : Fin (2 ^ n))
    (f : FunctionSpace 𝕜) : 𝕜 :=
  f (midpoint n k) - (f (leftPoint n k) + f (rightPoint n k)) / 2

def coefficients {𝕜 : Type u} [RCLike 𝕜] (f : FunctionSpace 𝕜) : ℕ → 𝕜
  | 0 => f 0
  | 1 => f 1 - f 0
  | j + 2 => hatCoefficient (hatIndex j).1 (hatIndex j).2 f

/-- Explicit initial sums; their interpolation and norm properties are obligations. -/
def partialSum {𝕜 : Type u} [RCLike 𝕜] (N : ℕ) (f : FunctionSpace 𝕜) :
    FunctionSpace 𝕜 :=
  C15Basis.Spec.orderedPartialSum (basis 𝕜) (coefficients f) N

/-- Knots present once N basis vectors have been retained (used for N ≥ 2). -/
def knots (N : ℕ) : Finset Interval :=
  {0, 1} ∪
    (Finset.range (N - 2)).image (fun j => midpoint (hatIndex j).1 (hatIndex j).2)

/-- An exact piecewise-affine interpolation condition, with no regular-grid
assumption on an incomplete level. -/
def Interpolates {𝕜 : Type u} [RCLike 𝕜] (N : ℕ)
    (f g : FunctionSpace 𝕜) : Prop :=
  (∀ t ∈ knots N, g t = f t) ∧
  ∀ a ∈ knots N, ∀ b ∈ knots N, (a : ℝ) < b →
    (∀ c ∈ knots N, ¬ ((a : ℝ) < c ∧ (c : ℝ) < b)) →
    ∀ t : Interval, (a : ℝ) ≤ t → (t : ℝ) ≤ b →
      g t = (((b : ℝ) - t) / ((b : ℝ) - a)) • f a +
        (((t : ℝ) - a) / ((b : ℝ) - a)) • f b

namespace Expected

def NormalizedHats : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (k : Fin (2 ^ n)),
    hat 𝕜 n k (midpoint n k) = 1 ∧ ‖hat 𝕜 n k‖ = 1

def NonzeroBasis : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (i : ℕ), basis 𝕜 i ≠ 0

def CoefficientContinuity : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (i : ℕ),
    ∃ L : FunctionSpace 𝕜 →L[𝕜] 𝕜, ∀ f, L f = coefficients f i

def Interpolation : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ f : FunctionSpace 𝕜, partialSum 0 f = 0) ∧
    (∀ f : FunctionSpace 𝕜, partialSum 1 f = ContinuousMap.const Interval (coefficients f 0)) ∧
    ∀ N, 2 ≤ N → ∀ f : FunctionSpace 𝕜, Interpolates N f (partialSum N f)

def Contractivity : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) (f : FunctionSpace 𝕜),
    ‖partialSum N f‖ ≤ ‖f‖

def Expansion : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (f : FunctionSpace 𝕜),
    Tendsto (fun N => partialSum N f) atTop (𝓝 f)

def BasisProperty : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (basis 𝕜)

def CoordinateFormula : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (f : FunctionSpace 𝕜) (a : ℕ → 𝕜),
    Tendsto (C15Basis.Spec.orderedPartialSum (basis 𝕜) a) atTop (𝓝 f) →
    a = coefficients f

/-- Conditionality uses the actual finite-subset net definition upstream. -/
def Conditionality : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 (FunctionSpace 𝕜) (basis 𝕜)

end Expected
end ExpandedFA.P1.SchauderHatBasis.Spec
