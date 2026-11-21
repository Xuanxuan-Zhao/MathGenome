import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.OrdinaryTrace
import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.BoundaryFractionalSpace
import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.GraphFractionalTransport

/-!
Independent statement of paper.tex:2610–2615, with the conventions at
1708–1712 and 2564–2593. The space below consists of the original physical
surface Lp classes. Its norm is the Lp norm plus the intrinsic Gagliardo
seminorm, with boundary dimension m in the denominator. No atlas, trace
estimate, or lifting certificate is assumed in the data.

The energy subtype has no algebraic instances here. Scalar linearity of the
lifting is expressed by equalities on its underlying Lp classes, as in the
upstream exact flat trace interface. These are the full addition and scalar
laws, not linearity on smooth data only.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal Topology

namespace P102.Trace.Exact
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry P102.Sobolev.Extension
open Ordinary MeasuredFractional

/-- The finite intrinsic-energy classes on the actual physical boundary. -/
def BoundaryData {m : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space (m + 1))) (s : ℝ) (p : ℝ≥0∞) :=
  {g : Ordinary.BoundaryLp 𝕜 Ω p //
    metricSeminorm m (Ordinary.boundaryMeasure Ω) s p
      (g : Space (m + 1) → 𝕜) < ⊤}

/-- The sum norm, with its original normalization. -/
def dataNorm {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space (m + 1))} {s : ℝ} {p : ℝ≥0∞}
    (g : BoundaryData 𝕜 Ω s p) : ℝ :=
  ‖g.val‖ + (metricSeminorm m (Ordinary.boundaryMeasure Ω) s p
    (g.val : Space (m + 1) → 𝕜)).toReal

namespace Expected

/-- Existence of the ordinary physical trace in the exact-trace range. -/
def TraceExistence : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ⊤ →
    ∃ T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p, IsTrace T

/-- Continuity into the intrinsic fractional space, for every representative
of the same ordinary trace. Constants do not depend on the bulk input. -/
def SharpBound : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ⊤ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p, IsTrace T →
      ∀ u, ∃ h : metricSeminorm m (Ordinary.boundaryMeasure Ω)
          (1 - 1 / p.toReal) p (T u : Space (m + 1) → 𝕜) < ⊤,
        dataNorm ⟨T u, h⟩ ≤ C * ‖u‖

/-- A bounded scalar-linear lifting of every intrinsic fractional datum.
The identity is in the original boundary Lp quotient and holds for the same
ordinary trace; the geometry is Lipschitz, with no smoothness upgrade. -/
def RightInverse : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ⊤ →
    ∃ (C : ℝ) (L : BoundaryData 𝕜 Ω (1 - 1 / p.toReal) p → Sobolev 𝕜 Ω 1 p),
      0 ≤ C ∧
      (∀ g h k, k.val = g.val + h.val → L k = L g + L h) ∧
      (∀ (c : 𝕜) g h, h.val = c • g.val → L h = c • L g) ∧
      (∀ g, ‖L g‖ ≤ C * dataNorm g) ∧
      ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p, IsTrace T →
        ∀ g, T (L g) = g.val

/-- Onto means every datum in this same physical boundary class space. -/
def Onto : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ⊤ →
    ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p, IsTrace T →
      ∀ g : BoundaryData 𝕜 Ω (1 - 1 / p.toReal) p,
        ∃ u, T u = g.val

/-- The kernel uses the actual closure of compactly supported smooth tests. -/
def Kernel : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ⊤ →
    ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p, IsTrace T →
      T.ker = sobolevZeroSubmodule 𝕜 Ω 1 p

/-- The entire exact trace theorem; conditional premises are not part of it. -/
def ExactTrace : Prop :=
  TraceExistence ∧ SharpBound ∧ RightInverse ∧ Onto ∧ Kernel

end Expected
end P102.Trace.Exact
