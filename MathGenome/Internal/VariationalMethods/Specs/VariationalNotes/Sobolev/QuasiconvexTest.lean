import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.MinorDivergence

/-! Proposition `prop:polyconvex-test`, paper.tex 4159–4177.
We state the stronger bounded-open-set version, hence in particular every
nondegenerate open cube. The base point and state are fixed, so F and G below
are their slices. G is real valued on the entire independent coordinate space;
no convexity of F in matrix entries is imposed. -/
noncomputable section
open MeasureTheory TopologicalSpace
namespace VariationalNotes.Sobolev.QuasiconvexTest

/-- The open cube with center c and half-side r, written using the supremum
norm of the ordinary coordinate product (not the Euclidean norm). -/
def openCube {d : ℕ} (c : Domain d) (r : ℝ) : Opens (Domain d) :=
  ⟨(WithLp.ofLp : Domain d → (Fin d → ℝ)) ⁻¹' Metric.ball (WithLp.ofLp c) r,
    Metric.isOpen_ball.preimage (PiLp.continuous_ofLp 2 _)⟩

namespace Expected
open Minors MinorDivergence

def PolyconvexTest : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    volume (Ω : Set (Domain d)) ≠ 0 →
    ∀ (F : Gradient m d → ℝ) (G : Coordinates m d → ℝ),
      (∀ Z, F Z = G (allMinors Z)) → ConvexOn ℝ Set.univ G →
      ∀ (Z : Gradient m d) (φ : VectorTest Ω m),
        F Z ≤ (volume.real (Ω : Set (Domain d)))⁻¹ *
          ∫ x, F (Z + classicalGradient (φ : Domain d → Vector m) x) ∂domainMeasure Ω

/-- Explicit specialization to every center and every positive side length. -/
def CubeTest : Prop :=
  ∀ {d m : ℕ} (c : Domain d) (r : ℝ), 0 < r →
    ∀ (F : Gradient m d → ℝ) (G : Coordinates m d → ℝ),
      (∀ Z, F Z = G (allMinors Z)) → ConvexOn ℝ Set.univ G →
      ∀ (Z : Gradient m d) (φ : VectorTest (openCube c r) m),
        F Z ≤ (volume.real (openCube c r : Set (Domain d)))⁻¹ *
          ∫ x, F (Z + classicalGradient (φ : Domain d → Vector m) x)
            ∂domainMeasure (openCube c r)

end Expected
end VariationalNotes.Sobolev.QuasiconvexTest
