import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.FlatTrace

/-!
The complete obligation of paper.tex, Lemma `p102:u5-flat-zero` (2541–2562).
The zero extension is an Lp class, with no assumed weak-derivative equations.
Zero trace is expressed by the upstream vertical boundary-value relation; its
agreement with the continuous Lp slice trace is a separate required bridge.
The range includes real and complex scalars and the endpoint p = 1.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Topology ENNReal

namespace P102.Trace
open P102.U4

namespace FlatZeroTraceExpected

/-- Zero extension of a half-space Lp class, including the flat face in the zero side. -/
def flatZeroExtension {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (v : DomainLp 𝕜 (halfSpace m) p) : DomainLp 𝕜 (⊤ : Opens (Space (m + 1))) p :=
  (show MemLp ((halfSpace m : Set (Space (m + 1))).indicator v) p
      (volume.restrict ((⊤ : Opens (Space (m + 1))) : Set (Space (m + 1)))) from by
    simpa using (memLp_indicator_iff_restrict
      (halfSpace m).isOpen.measurableSet.nullMeasurableSet).mpr (Lp.memLp v)).toLp _

/-- This uses actual vertical ACL boundary values, as in the accepted trace theorem. -/
def HasZeroFlatTrace {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) : Prop :=
  HasVerticalBoundaryValues u (0 : BoundaryLp m 𝕜 p)

/-- Membership of the zero-extended Lp function in the ordinary whole-space Sobolev space.
In particular, this predicate does not assume the desired formula for derivatives. -/
def HasFlatZeroExtension {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) : Prop :=
  ∃ w : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p,
    sobolevUnderlying w = flatZeroExtension (sobolevUnderlying u)

/-- Smooth compact approximants have their topological supports contained in H,
as imposed by `TestSpace (halfSpace m)`. All weak derivative coordinates converge
in the existing Sobolev norm, which includes the zeroth coordinate. -/
def IsHalfSpaceTestLimit {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) : Prop :=
  ∃ (φ : ℕ → TestSpace 𝕜 (halfSpace m)) (v : ℕ → HalfSobolev m 𝕜 p),
    (∀ n (α : SobolevIndex (m + 1) 1),
      (sobolevDerivative (v n) α : Space (m + 1) → 𝕜) =ᵐ[
        volume.restrict (halfSpace m : Set (Space (m + 1)))]
          multiPartial (φ n) α.val) ∧
    Tendsto v atTop (𝓝 u)

def ExtensionType := {m : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {p : ℝ≥0∞} →
  DomainLp 𝕜 (halfSpace m) p → DomainLp 𝕜 (⊤ : Opens (Space (m + 1))) p
def ExtensionValue : ExtensionType := @flatZeroExtension

def ZeroTraceType := {m : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {p : ℝ≥0∞} →
  [Fact (1 ≤ p)] → HalfSobolev m 𝕜 p → Prop
def ZeroTraceValue : ZeroTraceType := @HasZeroFlatTrace

def ExtensionMembershipType := ZeroTraceType
def ExtensionMembershipValue : ExtensionMembershipType := @HasFlatZeroExtension

def TestLimitType := ZeroTraceType
def TestLimitValue : TestLimitType := @IsHalfSpaceTestLimit

/-- The boundary-value formulation is exactly vanishing of the Lp slice trace. -/
def SliceBridge : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (u : HalfSobolev m 𝕜 p) (F : ℝ → BoundaryLp m 𝕜 p),
      IsSliceRepresentative u F → (HasZeroFlatTrace u ↔ F 0 = 0)

def ExtensionImpliesZeroTrace : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ u : HalfSobolev m 𝕜 p, HasFlatZeroExtension u → HasZeroFlatTrace u

def Equivalence : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ u : HalfSobolev m 𝕜 p, HasZeroFlatTrace u ↔ HasFlatZeroExtension u

def Derivatives : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (u : HalfSobolev m 𝕜 p) (w : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p),
      sobolevUnderlying w = flatZeroExtension (sobolevUnderlying u) →
      ∀ α : SobolevIndex (m + 1) 1,
        sobolevDerivative w α = flatZeroExtension (sobolevDerivative u α)

def Density : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ u : HalfSobolev m 𝕜 p, HasZeroFlatTrace u → IsHalfSpaceTestLimit u

end FlatZeroTraceExpected
end P102.Trace
