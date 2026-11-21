import MathGenome.Internal.FourierSobolev.Specs.P102.U4.RegularDerivatives
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.AbsoluteContinuityOnLines

/-!
The line-representative clause of paper.tex:1454–1466 (U4-05).
The ambient space, Euclidean volume, and distributional
coordinate derivative are the shared U4 objects. Transverse parameters have
exactly d-1 coordinates. In dimension one this is an empty product, with mass
one, rather than a positive-dimensional Lebesgue space.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory

namespace P102.U4.ACL

/-- Coordinates other than the direction of the line, with product Lebesgue measure. -/
abbrev Transverse {d : ℕ} (j : Fin d) := ExpandedFA.Sobolev.Lines.Transverse j

/-- Insert the line parameter into the j-th Euclidean coordinate. -/
def line {d : ℕ} (j : Fin d) (z : Transverse j) (t : ℝ) : Space d :=
  WithLp.toLp 2 (ExpandedFA.Sobolev.Lines.coordinateLine j z t)

/-- An open coordinate fiber; no connectedness assumption is made. -/
def fiber {d : ℕ} (Ω : Opens (Space d)) (j : Fin d) (z : Transverse j) : Set ℝ :=
  line j z ⁻¹' (Ω : Set (Space d))

/-- AC on each compact subinterval lying inside the open fiber. An interval
crossing a gap is excluded by the subset hypothesis. -/
abbrev LocallyAC {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (U : Set ℝ) : Prop :=
  ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn f U

/-- One ambient representative, with one exceptional transverse null set for
all compact intervals of each fiber. Derivatives are the prescribed ambient v. -/
def HasRepresentative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (j : Fin d) (u v : Space d → 𝕜) : Prop :=
  ∃ f : Space d → 𝕜,
    u =ᵐ[volume.restrict (Ω : Set (Space d))] f ∧
    ∀ᵐ z : Transverse j ∂volume,
      LocallyAC (fun t => f (line j z t)) (fiber Ω j z) ∧
      ∀ᵐ t ∂volume.restrict (fiber Ω j z),
        HasDerivAt (fun s => f (line j z s)) (v (line j z t)) t

end ACL

namespace ACLExpected

/-- Both directions under local L¹ hypotheses, with no global Lp assumption. -/
def Characterization : Prop :=
  ∀ (d : ℕ) (_hd : 0 < d) (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (j : Fin d) (u v : Space d → 𝕜),
    LocallyIntegrableOn u Ω volume → LocallyIntegrableOn v Ω volume →
      (distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v ↔
        ACL.HasRepresentative Ω j u v)

/-- The converse, with local integrability of the proposed derivative retained. -/
def Converse : Prop :=
  ∀ (d : ℕ) (_hd : 0 < d) (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (j : Fin d) (u v : Space d → 𝕜),
    LocallyIntegrableOn u Ω volume → LocallyIntegrableOn v Ω volume →
      ACL.HasRepresentative Ω j u v →
        distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v

/-- The no-transverse-variable specialization, retaining arbitrary open subsets
of the real line (and hence their disconnected components). -/
def DimensionOne : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space 1)) (u v : Space 1 → 𝕜),
    LocallyIntegrableOn u Ω volume → LocallyIntegrableOn v Ω volume →
      (distributionPartial {(0 : Fin 1)} (regularDistribution Ω u) =
        regularDistribution Ω v ↔
      ∃ f : Space 1 → 𝕜, u =ᵐ[volume.restrict (Ω : Set (Space 1))] f ∧
        ACL.LocallyAC (fun t => f (ACL.line 0 0 t)) (ACL.fiber Ω 0 0) ∧
        ∀ᵐ t ∂volume.restrict (ACL.fiber Ω 0 0),
          HasDerivAt (fun s => f (ACL.line 0 0 s)) (v (ACL.line 0 0 t)) t)

end ACLExpected
end P102.U4
