import Specs.ExpandedFA.PartV.VolterraResolvent
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Independent statement of the kernel part of `fa2:p5:volterra-resolvent`.
The index `n : ℕ` denotes the source's `k_(n+1)`, so no artificial
zeroth kernel is introduced. All products are ordered operator compositions.
The clamping below only extends integrands outside their actual intervals. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.PartV

/-- Clamping to the interval between the two coordinates of a triangle point. -/
def kernelIntegrationPoint {a b : ℝ} (p : volterraTriangle a b) (r : ℝ) : ℝ :=
  max p.val.2 (min p.val.1 r)

def kernelLeftPoint {a b : ℝ} (p : volterraTriangle a b) (r : ℝ) :
    volterraTriangle a b :=
  ⟨(p.val.1, kernelIntegrationPoint p r),
    p.property.1.trans (le_max_left _ _),
    max_le p.property.2.1 (min_le_left _ _), p.property.2.2⟩

def kernelRightPoint {a b : ℝ} (p : volterraTriangle a b) (r : ℝ) :
    volterraTriangle a b :=
  ⟨(kernelIntegrationPoint p r, p.val.2), p.property.1,
    le_max_left _ _, (max_le p.property.2.1 (min_le_left _ _)).trans p.property.2.2⟩

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E

/-- `(h*g)(t,s) = ∫_s^t h(t,r) ∘ g(r,s) dr`. -/
def kernelConvolution {a b : ℝ}
    (h g : volterraTriangle a b → E →L[𝕜] E) (p : volterraTriangle a b) : E →L[𝕜] E :=
  ∫ r in p.val.2..p.val.1, (h (kernelLeftPoint p r)).comp (g (kernelRightPoint p r))

/-- Source `k_(n+1)`, independently defined by its integral recursion. -/
def iteratedVolterraKernel {a b : ℝ}
    (k : C(volterraTriangle a b, E →L[𝕜] E)) : ℕ → volterraTriangle a b → E →L[𝕜] E
  | 0 => k
  | n + 1 => kernelConvolution k (iteratedVolterraKernel k n)

/-- Pointwise series. Continuity and uniform convergence are theorem obligations. -/
def volterraReducedResolventKernel {a b : ℝ}
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜)
    (p : volterraTriangle a b) : E →L[𝕜] E :=
  ∑' n : ℕ, lam ^ n • iteratedVolterraKernel k n p
/-- The kernel of `(I - λV)⁻¹ - I`. Index `n` is the source index `n+1`,
so this is precisely `∑_{m≥1} λ^m k_m`, including λ=0. -/
def volterraResolventKernel {a b : ℝ}
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜)
    (p : volterraTriangle a b) : E →L[𝕜] E :=
  ∑' n : ℕ, lam ^ (n + 1) • iteratedVolterraKernel k n p
end

namespace ResolventKernelSpec

def Recursion : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (_hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)),
  (∀ p, iteratedVolterraKernel k 0 p = k p) ∧
  (∀ n p, iteratedVolterraKernel k (n + 1) p =
    kernelConvolution k (iteratedVolterraKernel k n) p) ∧
  (∀ (p : volterraTriangle a b) (r : ℝ) (hr : r ∈ Icc p.val.2 p.val.1),
    kernelLeftPoint p r = ⟨(p.val.1, r), p.property.1.trans hr.1, hr.2, p.property.2.2⟩ ∧
    kernelRightPoint p r = ⟨(r, p.val.2), p.property.1, hr.1, hr.2.trans p.property.2.2⟩)

def RegularityEstimate : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (_hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)) (n : ℕ),
  Continuous (iteratedVolterraKernel k n) ∧
  ∀ p, ‖iteratedVolterraKernel k n p‖ ≤
    ‖k‖ ^ (n + 1) * (p.val.1 - p.val.2) ^ n / (n.factorial : ℝ)

def ReducedUniformSeries : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (_hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜),
  Continuous (volterraReducedResolventKernel k lam) ∧
  (∀ p, Summable (fun n : ℕ => ‖lam ^ n • iteratedVolterraKernel k n p‖) ∧
    HasSum (fun n : ℕ => lam ^ n • iteratedVolterraKernel k n p)
      (volterraReducedResolventKernel k lam p)) ∧
  TendstoUniformly
    (fun N p => ∑ n ∈ Finset.range N, lam ^ n • iteratedVolterraKernel k n p)
    (volterraReducedResolventKernel k lam) atTop

def ReducedKernelIdentities : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (_hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜),
  let R := volterraReducedResolventKernel k lam
  (∀ p, R p = k p + lam • kernelConvolution k R p) ∧
  (∀ p, R p = k p + lam • kernelConvolution R k p)

/-- The representation is for the unique solution of the original equation,
with no smallness restriction, for arbitrary continuous Banach-valued data. -/
def SolutionRepresentation : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (lam : 𝕜) (f u : C(VolterraInterval a b, E)),
  u - lam • (VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k) u = f →
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  ∀ t : VolterraInterval a b,
    u t = f t + lam • ∫ s in a..(t : ℝ),
      volterraReducedResolventKernel k lam (volterraRetraction t s)
        (f (Set.projIcc a b hab s))

/-- The source bound for every uniform bound M; no positivity or positive
interval length is an extra assumption. -/
def UniformKernelEstimate : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (_hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E))
  (M : ℝ), (∀ p, ‖k p‖ ≤ M) → ∀ (n : ℕ) (p : volterraTriangle a b),
  ‖iteratedVolterraKernel k n p‖ ≤
    M ^ (n + 1) * (p.val.1 - p.val.2) ^ n / (n.factorial : ℝ)

def UniformSeries : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (_hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜),
  Continuous (volterraResolventKernel k lam) ∧
  (∀ p, Summable (fun n : ℕ => ‖lam ^ (n + 1) • iteratedVolterraKernel k n p‖) ∧
    HasSum (fun n : ℕ => lam ^ (n + 1) • iteratedVolterraKernel k n p)
      (volterraResolventKernel k lam p)) ∧
  TendstoUniformly
    (fun N p => ∑ n ∈ Finset.range N, lam ^ (n + 1) • iteratedVolterraKernel k n p)
    (volterraResolventKernel k lam) atTop

/-- Both ordered identities, with no commutativity assumption on operators. -/
def KernelIdentities : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (_hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜),
  let R := volterraResolventKernel k lam
  (∀ p, R p = lam • k p + lam • kernelConvolution k R p) ∧
  (∀ p, R p = lam • k p + lam • kernelConvolution R k p)

/-- The actual native ring inverse, applied to arbitrary continuous data, is
represented by the full kernel series. Its subtraction of the identity has
exactly this integral formula. Covers a=b and the zero state space. -/
def InverseRepresentation : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜),
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  ∀ (f : C(VolterraInterval a b, E)) (t : VolterraInterval a b),
    ((Ring.inverse (1 - lam • V) - 1) f) t =
      ∫ s in a..(t : ℝ), volterraResolventKernel k lam (volterraRetraction t s)
        (f (Set.projIcc a b hab s))

/-- The independently defined iterated kernel represents the corresponding
power of the original integral operator, retaining the order of composition. -/
def IterateRepresentation : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b : ℝ) (hab : a ≤ b) (k : C(volterraTriangle a b, E →L[𝕜] E)) (n : ℕ),
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  ∀ (f : C(VolterraInterval a b, E)) (t : VolterraInterval a b),
    ((V ^ (n + 1)) f) t = ∫ s in a..(t : ℝ),
      iteratedVolterraKernel k n (volterraRetraction t s) (f (Set.projIcc a b hab s))

end ResolventKernelSpec
end ExpandedFA.PartV
