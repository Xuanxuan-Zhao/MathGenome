import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.RCLike.Basic

/-!
Independent statements for paper.tex, Chapter 19, `d11:19:cc-czero`.
The canonical spaces are Mathlib's `CompactlySupportedContinuousMap` and
`ZeroAtInftyContinuousMap` themselves. No second bundled function space is introduced.
The norms below specialize to absolute value on ℝ and modulus on ℂ.
-/

namespace Specs.D11.Ch19.CcCzero

universe u v

/-- Type of the canonical continuous-function spaces. -/
def functionSpaceType :=
  ∀ (X : Type u) [TopologicalSpace X] (E : Type v) [Zero E] [TopologicalSpace E],
    Type (max u v)

/-- Expected value for Cc: the native type, not a newly bundled space. -/
def ccValue : functionSpaceType.{u, v} :=
  fun X _ E _ _ => CompactlySupportedContinuousMap X E

/-- Expected value for C0: the native type, not a newly bundled space. -/
def czeroValue : functionSpaceType.{u, v} :=
  fun X _ E _ _ => ZeroAtInftyContinuousMap X E

/-- The paper's support is the topological support, including the closure. -/
def support_eq : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (E : Type v) [Zero E] (f : X → E),
    tsupport f = closure {x | f x ≠ 0}

/-- The native compact-support predicate uses exactly this closed support. -/
def compactSupport_iff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (E : Type v) [Zero E] (f : X → E),
    HasCompactSupport f ↔ IsCompact (closure {x | f x ≠ 0})

/-- The native cocompact-filter condition is exactly the paper's compact-level condition. -/
def zeroAtInfinity_iff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (E : Type v) [NormedAddCommGroup E]
    (f : X → E), Continuous f →
    (Filter.Tendsto f (Filter.cocompact X) (nhds 0) ↔
      ∀ ε : ℝ, 0 < ε → IsCompact {x | ε ≤ ‖f x‖})

/-- Full membership bridge, with a unique native representative of every paper Cc function.
It holds on all topological domains, in particular on every LCH space. -/
def cc_iff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜] (f : X → 𝕜),
    (∃! g : CompactlySupportedContinuousMap X 𝕜, (g : X → 𝕜) = f) ↔
      Continuous f ∧ IsCompact (closure {x | f x ≠ 0})

/-- Full membership bridge for C0, with precisely all positive real thresholds.
No countability, compactness, or nonemptiness assumption is imposed on X. -/
def czero_iff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (𝕜 : Type v) [RCLike 𝕜] (f : X → 𝕜),
    (∃! g : ZeroAtInftyContinuousMap X 𝕜, (g : X → 𝕜) = f) ↔
      Continuous f ∧ ∀ ε : ℝ, 0 < ε → IsCompact {x | ε ≤ ‖f x‖}

end Specs.D11.Ch19.CcCzero
