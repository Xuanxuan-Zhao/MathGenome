import MathGenome.Internal.FourierSobolev.Specs.P102.U4.BiLipschitzPullback
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.Truncations
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Polarization stage of paper.tex:2048–2081. The input and output use the
canonical distributional Sobolev space. The gradient below uses the Euclidean
norm, as required by the U5 convention at paper.tex:1708–1712. No rearrangement
or gradient inequality is assumed in any of these definitions. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Classical
namespace P102.Sobolev
open P102.U4
namespace Polarization

/-- A half-space containing the origin in its interior. -/
structure Halfspace (d : ℕ) where
  normal : Space d
  normal_unit : ‖normal‖ = 1
  offset : ℝ
  offset_pos : 0 < offset

namespace Halfspace

/-- The orthogonal linear part of reflection in the boundary plane. -/
def linearReflection {d : ℕ} (H : Halfspace d) : Space d ≃ₗᵢ[ℝ] Space d :=
  (Submodule.reflection (ℝ ∙ H.normal)).trans (LinearIsometryEquiv.neg ℝ)

/-- Reflection in x · normal = offset. -/
def reflection {d : ℕ} (H : Halfspace d) (x : Space d) : Space d :=
  H.linearReflection x + (2 * H.offset) • H.normal

/-- The open side on which the larger value is placed. -/
def nearSide {d : ℕ} (H : Halfspace d) : Set (Space d) :=
  {x | inner ℝ H.normal x < H.offset}

/-- On the boundary the reflected point is the point itself, so either branch
has the same value. -/
def polarize {d : ℕ} (H : Halfspace d) (g : Space d → ℝ) (x : Space d) : ℝ :=
  if x ∈ H.nearSide then max (g x) (g (H.reflection x))
  else min (g x) (g (H.reflection x))

/-- The gradient selected by the max/min formula. On ties we retain the
original gradient, a valid choice once the level-set derivative rule is used. -/
def selectedGradient {d : ℕ} (H : Halfspace d) (g : Space d → ℝ) (G : Space d → Space d) (x : Space d) : Space d :=
  if (if x ∈ H.nearSide then g (H.reflection x) ≤ g x else g x ≤ g (H.reflection x))
    then G x else H.linearReflection (G (H.reflection x))

end Halfspace

abbrev WholeSobolev (d : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  P102.U4.Sobolev ℝ (⊤ : Opens (Space d)) 1 p

/-- The canonical weak gradient as a Euclidean vector, not a coordinate sum. -/
def gradient {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : WholeSobolev d p) (x : Space d) : Space d :=
  WithLp.toLp 2 (fun j => firstWeakDerivative g j x)

/-- Nonnegativity and support are properties of the Lp class. -/
def SupportedNonnegative {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (R : ℝ) (g : WholeSobolev d p) : Prop :=
  (∀ᵐ x ∂volume, 0 ≤ sobolevUnderlying g x) ∧
  (∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Space d) R → sobolevUnderlying g x = 0)

end Polarization
namespace PolarizationExpected
open Polarization

/-- Sobolev membership, nonnegativity, preservation of every positive superlevel
measure and of the Lp norm, unchanged ball support, and the sharp gradient bound.
The witness is a genuine weak-derivative tuple representing the defined formula. -/
def Properties : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (H : Halfspace d) (R : ℝ), 0 < R →
    ∀ g : WholeSobolev d p, SupportedNonnegative R g →
    ∃ w : WholeSobolev d p,
      (sobolevUnderlying w =ᵐ[volume] H.polarize (sobolevUnderlying g)) ∧
      SupportedNonnegative R w ∧
      (∀ s : ℝ, 0 < s →
        volume {x | s < sobolevUnderlying w x} =
          volume {x | s < sobolevUnderlying g x}) ∧
      eLpNorm (sobolevUnderlying w) p volume = eLpNorm (sobolevUnderlying g) p volume ∧
      eLpNorm (gradient w) p volume ≤ eLpNorm (gradient g) p volume

/-- The stated p-th-power continuity estimate, for the actual reflected max/min
formula on the specified class. Extended nonnegative norms avoid any arbitrary
choice of representatives or conversion at infinity; p here is finite. -/
def Continuity : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (H : Halfspace d) (R : ℝ), 0 < R →
    ∀ g h : WholeSobolev d p,
      SupportedNonnegative R g → SupportedNonnegative R h →
      (eLpNorm (fun x => H.polarize (sobolevUnderlying g) x -
        H.polarize (sobolevUnderlying h) x) p volume) ^ p.toReal ≤
      2 * (eLpNorm (fun x => sobolevUnderlying g x - sobolevUnderlying h x)
        p volume) ^ p.toReal

end PolarizationExpected
end P102.Sobolev
