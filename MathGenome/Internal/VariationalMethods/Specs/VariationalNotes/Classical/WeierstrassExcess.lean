import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.VariationSpaces

/-!
The Weierstrass condition in paper.tex:3492–3533.  The admissible class is
the shared continuous piecewise C¹ class, and minimality uses only the norm
of the states.  Smoothness is local to the graphs used for the tested velocity.
-/
noncomputable section
open Set
open scoped ContDiff

namespace VariationalNotes.Classical.Weierstrass

/-- C¹ regularity on an open neighborhood of the reference graph and the
nearby inserted velocity graph, including every joining velocity segment.
The neighborhood and the time radius may depend on the tested velocity.
No regularity away from this neighborhood is required. -/
def velocityInsertionRegular {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t₀ : I.Points) (w : State m) : Prop :=
  ∃ U : Set (ℝ × State m × State m), IsOpen U ∧ U ⊆ L.domain ∧
    ContDiffOn ℝ 1 L.value U ∧
    (∀ t : I.Points, graphPoint u t ∈ U) ∧
    ∃ δ > 0, ∀ t : I.Points, |(t : ℝ) - (t₀ : ℝ)| < δ →
      ∀ s ∈ Icc (0 : ℝ) 1,
        ((t : ℝ), u.state t, u.velocity t + s • (w - u.velocity t)) ∈ U

/-- The velocity excess, with the shared Euclidean momentum convention. -/
def excess {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t₀ : I.Points) (w : State m) : ℝ :=
  L.value ((t₀ : ℝ), u.state t₀, w) -
    L.value (graphPoint u t₀) -
    inner ℝ (momentum L u t₀) (w - u.velocity t₀)

end VariationalNotes.Classical.Weierstrass

namespace Specs.VariationalNotes.Classical
open _root_.VariationalNotes.Classical

def weierstrassExcess : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (xₐ xᵦ : State m)
    (u : C1Curve I m),
    piecewiseStrongLocalMinimum L xₐ xᵦ u.state →
    ∀ t₀ : I.Points, (t₀ : ℝ) ∈ Ioo I.a I.b →
    ∀ w : State m, Weierstrass.velocityInsertionRegular L u t₀ w →
      0 ≤ Weierstrass.excess L u t₀ w

end Specs.VariationalNotes.Classical
