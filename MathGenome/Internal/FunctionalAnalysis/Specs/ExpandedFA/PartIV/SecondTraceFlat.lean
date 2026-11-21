import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SharpTraceBound
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! Independent scope of the flat simultaneous-jet construction in
`paper.tex`, `fa2:p4:second-trace`. The normal coordinate points inward.
The target is the existing order-two distributional derivative graph, with
its full sum norm. Boundary dimension zero and both scalar fields are included.
There are no assumed extension or second-derivative estimate certificates.
-/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The unit normal multi-index in the order-two graph. -/
def normalIndex {d : ℕ} (i : Fin d) : DerivativeIndex d 2 :=
  ⟨fun j => if j = i then 1 else 0, by simp_rw [apply_ite]; simp⟩

/-- A fixed smooth cutoff equal to one near the boundary. -/
def jetCutoff : ℝ → ℝ :=
  (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ))

/-- A radial, hence even, smooth integral-one tangential mollifier. -/
def jetMollifier (n : ℕ) : Domain n → ℝ :=
  (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : Domain n)).normed volume

/-- Signed-scale formula; for t>0 the integrals are precisely rho_t*f and
rho_t*h after the substitution r=t*y. Signed scales make the smooth-data
formula meaningful at the boundary without a singular kernel definition. -/
def flatJet {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f h : Domain n → 𝕜)
    (z : Domain n × ℝ) : 𝕜 :=
  χ z.2 • ((∫ y, ρ y • f (z.1 - z.2 • y)) +
    z.2 • (∫ y, ρ y • h (z.1 - z.2 • y)))

def jetFunction {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (i : Fin (n + 1))
    (f h : Domain n → 𝕜) (x : Domain (n + 1)) : 𝕜 :=
  flatJet jetCutoff (jetMollifier n) f h (i.removeNth x, x i)

/-- Both traces are taken by the original first-order coordinate trace.
The existential first-order graph elements represent u and its actual normal
weak derivative; they are conclusions, not replacement trace assumptions. -/
def HasBoundaryJets {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    (u : SpaceValue 𝕜 (n + 1) (upper i) 2 p)
    (g h : Lp 𝕜 p (volume : Measure (Domain n))) : Prop :=
  ∃ v w : SpaceValue 𝕜 (n + 1) (upper i) 1 p,
    v.val (zeroIndex (n + 1) 1) = u.val (zeroIndex (n + 1) 2) ∧
    w.val (zeroIndex (n + 1) 1) = u.val (normalIndex i) ∧
    reindexedTrace i T v = g ∧ reindexedTrace i T w = h

end ExpandedFA.PartIV.SecondTraceFlat

namespace Specs.ExpandedFA.PartIV.SecondTraceFlat
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.HalfSpace _root_.ExpandedFA.Sobolev.Lines
open _root_.ExpandedFA.PartIV.FractionalSobolev
open _root_.ExpandedFA.PartIV.SharpTraceBound _root_.ExpandedFA.PartIV.SecondTraceFlat
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- A scalar-linear simultaneous right inverse given by the even-mollifier
formula, uniformly bounded in the full W^{2,p} norm. The trace existence
clause prevents vacuous quantification over trace maps. The sum convention
for the data norm is equivalent to the usual product norm. -/
def BoundedJetExtension : Prop :=
  ∀ (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1)),
      (∃ T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
        Lp 𝕜 p (volume : Measure (Transverse i)), CoordinateTraceCondition i T) ∧
      ∃ E : HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p →
          FractionalSpace 𝕜 n (1 - 1 / p.toReal) p →
          SpaceValue 𝕜 (n + 1) (upper i) 2 p,
        (∀ g₁ g₂ g₃ h₁ h₂ h₃,
          g₃.val = g₁.val + g₂.val → h₃.val = h₁.val + h₂.val →
          E g₃ h₃ = E g₁ h₁ + E g₂ h₂) ∧
        (∀ (c : 𝕜) g₁ g₂ h₁ h₂,
          g₂.val = c • g₁.val → h₂.val = c • h₁.val →
          E g₂ h₂ = c • E g₁ h₁) ∧
        (∀ g h, ‖E g h‖ ≤ C *
          (higherFractionalNorm (2 - 1 / p.toReal) p g +
            fractionalNorm (1 - 1 / p.toReal) p h)) ∧
        (∀ g h, (E g h).val (zeroIndex (n + 1) 2) =ᵐ[
            volume.restrict (upper i : Set (Domain (n + 1)))]
          jetFunction i (wholeLp (g.val.val (zeroIndex n 1))) h.val) ∧
        (∀ (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
            Lp 𝕜 p (volume : Measure (Transverse i))), CoordinateTraceCondition i T →
          ∀ g h, HasBoundaryJets i T (E g h)
            (wholeLp (g.val.val (zeroIndex n 1))) h.val)

end Specs.ExpandedFA.PartIV.SecondTraceFlat
