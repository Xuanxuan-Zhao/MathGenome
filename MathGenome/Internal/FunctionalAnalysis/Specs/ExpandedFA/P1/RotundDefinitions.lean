import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair

/-! Independent interface for paper.tex:4613–4628 (`fa2:p1:rotund-definitions`).
The given norm is used over ℝ or ℂ, with scalar-linear continuous duals.
Convergence in the local and Radon–Riesz definitions is sequential, as in
paper.tex:4672–4678 and 4901–4906. Neither completeness nor nontriviality
is assumed. The empty-set branch of the modulus is explicit: it is never
an infimum of the empty set. On the required interval in a nonzero space
that branch is inaccessible; in the zero space it gives the stated value 1.
-/
namespace ExpandedFA.P1.RotundDefinitions.Spec
universe u v
open Filter
open scoped Topology
noncomputable section

def PredicateType :=
  (𝕜 : Type u) → (E : Type v) → [RCLike 𝕜] → [NormedAddCommGroup E] →
    [NormedSpace 𝕜 E] → Prop

def PointPredicateType :=
  (𝕜 : Type u) → (E : Type v) → [RCLike 𝕜] → [NormedAddCommGroup E] →
    [NormedSpace 𝕜 E] → E → Prop

def DeficitsType :=
  (𝕜 : Type u) → (E : Type v) → [RCLike 𝕜] → [NormedAddCommGroup E] →
    [NormedSpace 𝕜 E] → ℝ → Set ℝ

def ModulusType :=
  (𝕜 : Type u) → (E : Type v) → [RCLike 𝕜] → [NormedAddCommGroup E] →
    [NormedSpace 𝕜 E] → ℝ → ℝ

/-- Strict convexity, also called rotundity, of the displayed norm. -/
def RotundValue : PredicateType.{u,v} :=
  fun 𝕜 E _ _ _ => ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y →
    ‖(2 : 𝕜)⁻¹ • (x + y)‖ < 1

/-- Local uniform convexity is asserted at a unit vector. -/
def LocallyUniformlyConvexAtValue : PointPredicateType.{u,v} :=
  fun 𝕜 E _ _ _ x => ‖x‖ = 1 ∧ ∀ y : ℕ → E,
    (∀ n, ‖y n‖ = 1) →
    Tendsto (fun n => ‖(2 : 𝕜)⁻¹ • (x + y n)‖) atTop (𝓝 1) →
    Tendsto y atTop (𝓝 x)

def LocallyUniformlyConvexValue : PredicateType.{u,v} :=
  fun 𝕜 E _ _ _ => ∀ x : E, ‖x‖ = 1 → LocallyUniformlyConvexAtValue 𝕜 E x

/-- All actual closed-unit-ball midpoint deficits at separation at least ε. -/
def DeficitsValue : DeficitsType.{u,v} :=
  fun 𝕜 E _ _ _ ε => {d | ∃ x y : E, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
    ε ≤ ‖x - y‖ ∧ d = 1 - ‖(2 : 𝕜)⁻¹ • (x + y)‖}

/-- At zero the modulus is zero. Empty separated-pair sets are assigned 1.
In particular this implements the manuscript's convention for the zero space.
For ε > 2 this is a harmless totalization outside the specified interval. -/
def ModulusValue : ModulusType.{u,v} := by
  classical
  exact fun 𝕜 E _ _ _ ε => if ε = 0 then 0 else
    if (DeficitsValue 𝕜 E ε).Nonempty then sInf (DeficitsValue 𝕜 E ε) else 1

/-- Weak convergence uses the fixed norm-continuous scalar-linear dual,
via the accepted initial topology. Norm convergence uses the original norm. -/
def RadonRieszValue : PredicateType.{u,v} :=
  fun 𝕜 E _ _ _ => ∀ (y : ℕ → E) (x : E),
    Tendsto y atTop (@nhds E
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x) →
    Tendsto (fun n => ‖y n‖) atTop (𝓝 ‖x‖) → Tendsto y atTop (𝓝 x)

def DeficitsBoundedBelow : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (ε : ℝ),
    BddBelow (DeficitsValue 𝕜 E ε)

def DeficitsNonempty : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E] {ε : ℝ},
    ε ≤ 2 → (DeficitsValue 𝕜 E ε).Nonempty

def ModulusZero : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], ModulusValue 𝕜 E 0 = 0

def ModulusSubsingleton : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E] (ε : ℝ),
    0 < ε → ModulusValue 𝕜 E ε = 1

/-- In every nonzero space this is exactly the printed real infimum. -/
def ModulusInfimum : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E] (ε : ℝ),
    0 < ε → ε ≤ 2 → ModulusValue 𝕜 E ε = sInf (DeficitsValue 𝕜 E ε)

def UniformlyConvexIffModulus : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E ↔
      ∀ ε : ℝ, 0 < ε → ε ≤ 2 → 0 < ModulusValue 𝕜 E ε

/-- Rotundity is the usual strict convexity of the underlying real space. -/
def RotundIffNative : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    RotundValue 𝕜 E ↔ StrictConvexSpace ℝ E

end
end ExpandedFA.P1.RotundDefinitions.Spec
