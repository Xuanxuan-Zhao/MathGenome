import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Projection

/-! Independent statements for the convex-set clause of
`fa2:p2:alternating-projections` (paper.tex 13117–13148).
The subspace improvement is a separately allocated obligation.
Real convexity and the nearest-point map are the accepted shared interfaces.
Weak convergence tests every continuous scalar-linear functional on the original
normed space. The initial vector is arbitrary, including outside both sets. -/
noncomputable section
namespace ExpandedFA.Geometry.AlternatingConvexProjections.Spec
universe u v
open Filter
open scoped Topology

/-- Interleave the two nearest-point projections, starting at the given vector. -/
def iteratesValue {H : Type v} (P₁ P₂ : H → H) (x₀ : H) : ℕ → H
  | 0 => x₀
  | n + 1 => if n % 2 = 0 then P₁ (iteratesValue P₁ P₂ x₀ n)
      else P₂ (iteratesValue P₁ P₂ x₀ n)

def IteratesType := ∀ {H : Type v}, (H → H) → (H → H) → H → ℕ → H

def IteratesValue : IteratesType.{v} := @iteratesValue

/-- The two displayed recurrences in the source, with the specified initial value. -/
def IteratesRecurrences : Prop :=
  ∀ {H : Type v} (P₁ P₂ : H → H) (x₀ : H),
    let x := iteratesValue P₁ P₂ x₀
    x 0 = x₀ ∧ ∀ n, x (2 * n + 1) = P₁ (x (2 * n)) ∧
      x (2 * n + 2) = P₂ (x (2 * n + 1))

def WeakConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C₁ C₂ : Set H) (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hc₁ : IsClosed C₁) (hc₂ : IsClosed C₂)
    (hv₁ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₁)
    (hv₂ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₂),
    (C₁ ∩ C₂).Nonempty → ∀ x₀ : H,
    let P₁ := Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₁ hne₁ hc₁ hv₁
    let P₂ := Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₂ hne₂ hc₂ hv₂
    ∃ p ∈ C₁ ∩ C₂, ∀ f : H →L[𝕜] 𝕜,
      Tendsto (fun n => f (iteratesValue P₁ P₂ x₀ n)) atTop (𝓝 (f p))

end ExpandedFA.Geometry.AlternatingConvexProjections.Spec
