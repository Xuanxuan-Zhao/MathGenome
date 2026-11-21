import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SchrodingerPotentialBounds

/-! Independent statements for the free operator used in
`fa2:p3:schrodinger-potential` (paper.tex:13642–13673).
All objects are the shared native-real-line objects. In particular the real
clause uses real-valued L², and both clauses retain the first and second L²
weak derivatives in the domain. No density or adjoint/core certificate is data.
-/
noncomputable section
open MeasureTheory Set

namespace ExpandedFA.Unbounded.SchrodingerFreeLaplacian.Spec
open SchrodingerPotential

/-- The complete free-operator obligation on genuine real-valued L²(ℝ). -/
def FreeReal : Prop := SchrodingerPotential.Spec.FreeFacts ℝ

/-- The complete free-operator obligation on complex-valued L²(ℝ). -/
def FreeComplex : Prop := SchrodingerPotential.Spec.FreeFacts ℂ

/-- The actual smooth compactly supported classes belong to the H² domain. -/
def SmoothDomain : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  smoothCompact 𝕜 ≤ (freeLaplacian 𝕜).domain

/-- Density in ambient L²; this does not assert density in the graph norm. -/
def SmoothDense : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  Dense (smoothCompact 𝕜 : Set (L2 𝕜))

def DenseDomain : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  Dense ((freeLaplacian 𝕜).domain : Set (L2 𝕜))

/-- Formal symmetry, with no equality to the full adjoint smuggled in. -/
def FreeSymmetry : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u v : (freeLaplacian 𝕜).domain),
  inner 𝕜 (freeLaplacian 𝕜 u) v.val = inner 𝕜 u.val (freeLaplacian 𝕜 v)

def FreeClosed : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  (freeLaplacian 𝕜).IsClosed

end ExpandedFA.Unbounded.SchrodingerFreeLaplacian.Spec
