import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ACL
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
The ordinary flat trace construction in paper.tex:2439–2460.
The ambient space is the shared Euclidean `Space (m+1)`. Boundary coordinates
are indexed by all coordinates except the last: this is precisely a product of
m real lines with product Lebesgue measure. No surface normalization is inserted.
The main statement is restricted to m ≥ 1 and 1 ≤ p < ∞, including p = 1.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Topology ENNReal

namespace P102.Trace
open P102.U4

abbrev Boundary (m : ℕ) := ACL.Transverse (Fin.last m)

/-- The open upper half-space in the upstream Euclidean coordinates. -/
def halfSpace (m : ℕ) : Opens (Space (m + 1)) :=
  ⟨{x | 0 < x (Fin.last m)}, isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m))⟩

/-- The point with boundary coordinates z and height t. -/
def point (m : ℕ) (z : Boundary m) (t : ℝ) : Space (m + 1) :=
  ACL.line (Fin.last m) z t

/-- The multi-index of the vertical first weak derivative. -/
def verticalIndex (m : ℕ) : SobolevIndex (m + 1) 1 :=
  ⟨{Fin.last m}, by simp⟩

abbrev HalfSobolev (m : ℕ) (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  Sobolev 𝕜 (halfSpace m) 1 p

abbrev BoundaryLp (m : ℕ) (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) :=
  Lp 𝕜 p (volume : Measure (Boundary m))

/-- A slice-norm profile is only used under an a.e. slicing statement.
No value of a raw Lp representative at an exceptional height defines a trace. -/
def verticalProfile {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) (t : ℝ) : ℝ :=
  (eLpNorm (fun z : Boundary m => sobolevDerivative u (verticalIndex m) (point m z t))
    p volume).toReal

/-- A continuous Lp-valued representative including height zero. Agreement
with the Sobolev class is required at almost every positive height, in Lp. -/
def IsSliceRepresentative {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) (F : ℝ → BoundaryLp m 𝕜 p) : Prop :=
  ContinuousOn F (Ici 0) ∧
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (fun z : Boundary m => F t z) =ᵐ[volume]
        (fun z => sobolevUnderlying u (point m z t))

/-- Identification uses a vertical ACL representative of the original class,
rather than asserting a pointwise limit for an arbitrary quotient representative. -/
def HasVerticalBoundaryValues {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) (g : BoundaryLp m 𝕜 p) : Prop :=
  ∃ f : Space (m + 1) → 𝕜,
    sobolevUnderlying u =ᵐ[volume.restrict (halfSpace m : Set (Space (m + 1)))] f ∧
    ∀ᵐ z : Boundary m ∂volume,
      ACL.LocallyAC (fun t => f (point m z t)) (Ioi 0) ∧
      (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        HasDerivAt (fun s => f (point m z s))
          (sobolevDerivative u (verticalIndex m) (point m z t)) t) ∧
      Tendsto (fun t => f (point m z t)) (𝓝[>] 0) (𝓝 (g z))

namespace FlatTraceExpected

def HalfSpaceType := (m : ℕ) → Opens (Space (m + 1))
def HalfSpaceValue : HalfSpaceType := halfSpace

def PointType := (m : ℕ) → Boundary m → ℝ → Space (m + 1)
def PointValue : PointType := point

def VerticalIndexType := (m : ℕ) → SobolevIndex (m + 1) 1
def VerticalIndexValue : VerticalIndexType := verticalIndex

def VerticalProfileType := {m : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {p : ℝ≥0∞} →
  [Fact (1 ≤ p)] → HalfSobolev m 𝕜 p → ℝ → ℝ
def VerticalProfileValue : VerticalProfileType := @verticalProfile

/-- The ACL input supplied by the accepted U4 theorem, specialized to H. -/
def VerticalACL : Prop :=
  ∀ (m : ℕ) (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : HalfSobolev m 𝕜 p),
    ∃ f : Space (m + 1) → 𝕜,
      sobolevUnderlying u =ᵐ[volume.restrict (halfSpace m : Set (Space (m + 1)))] f ∧
      ∀ᵐ z : Boundary m ∂volume,
        ACL.LocallyAC (fun t => f (point m z t)) (Ioi 0) ∧
        ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          HasDerivAt (fun s => f (point m z s))
            (sobolevDerivative u (verticalIndex m) (point m z t)) t

/-- Both the positive-height representative and its endpoint are unique. -/
def SliceUniqueness : Prop :=
  ∀ (m : ℕ) (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : HalfSobolev m 𝕜 p) (F G : ℝ → BoundaryLp m 𝕜 p),
    IsSliceRepresentative u F → IsSliceRepresentative u G → EqOn F G (Ici 0)

/-- Compatibility of an identified vertical trace with every representative
continuous up to the flat boundary, in particular with smooth restrictions. -/
def VerticalBoundaryCompatibility : Prop :=
  ∀ (m : ℕ) (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : HalfSobolev m 𝕜 p) (g : BoundaryLp m 𝕜 p)
    (f : Space (m + 1) → 𝕜),
    HasVerticalBoundaryValues u g →
    ContinuousOn f {x | 0 ≤ x (Fin.last m)} →
    sobolevUnderlying u =ᵐ[volume.restrict (halfSpace m : Set (Space (m + 1)))] f →
    (fun z : Boundary m => g z) =ᵐ[volume] (fun z => f (point m z 0))

/-- The entire ordinary trace obligation, with one bounded linear map and the
continuous choice of slices that defines it. The scalar field can be real or complex.
The vertical profile is a genuine Lp function at almost every positive height;
its local L1 integrability at zero is explicit, also when p=1. -/
def TraceExists : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∃ C : ℝ, 0 ≤ C ∧
    ∃ T : HalfSobolev m 𝕜 p →L[𝕜] BoundaryLp m 𝕜 p,
      (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      (∀ u, ∃ F : ℝ → BoundaryLp m 𝕜 p,
        IsSliceRepresentative u F ∧ F 0 = T u ∧
        Tendsto F (𝓝[>] 0) (𝓝 (T u)) ∧
        (∀ R : ℝ, 0 < R → IntegrableOn (verticalProfile u) (Ioc 0 R)) ∧
        (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          MemLp (fun z : Boundary m =>
            sobolevDerivative u (verticalIndex m) (point m z t)) p volume) ∧
        (∀ a b : ℝ, 0 < a → 0 < b →
          ‖F b - F a‖ ≤ ∫ t in min a b..max a b, verticalProfile u t) ∧
        (∀ t : ℝ, 0 < t →
          ‖T u‖ ≤ ‖F t‖ + ∫ a in (0 : ℝ)..t, verticalProfile u a) ∧
        HasVerticalBoundaryValues u (T u)) ∧
      (∀ (u : HalfSobolev m 𝕜 p) (f : Space (m + 1) → 𝕜),
        ContinuousOn f {x | 0 ≤ x (Fin.last m)} →
        sobolevUnderlying u =ᵐ[volume.restrict (halfSpace m : Set (Space (m + 1)))] f →
        (fun z : Boundary m => T u z) =ᵐ[volume] (fun z => f (point m z 0)))

end FlatTraceExpected
end P102.Trace
