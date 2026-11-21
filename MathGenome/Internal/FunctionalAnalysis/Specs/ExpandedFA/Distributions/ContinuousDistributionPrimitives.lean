import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Independent statements for paper.tex:17236, `fa2:p4:distribution-structure`.
All pairings are scalar-linear. Ordered coordinate words include every mixed
partial and order zero. Integrals use Euclidean Lebesgue volume. -/
open Set TopologicalSpace MeasureTheory
open scoped Distributions

namespace ExpandedFA.Distributions

/-- The action of a distributional derivative of a continuous density.
The density need only be continuous on the test's open domain; test functions
vanish off that domain. This is the actual integral pairing, not a certificate
asserting the desired representation. -/
noncomputable def continuousPrimitivePairing {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} (w : List (Fin d)) (f : Domain d → 𝕜)
    (φ : Tests 𝕜 Ω) : 𝕜 :=
  (-1 : 𝕜) ^ w.length * ∫ x, f x * testPartialCLM w φ x

/-- A finite sum of derivatives, allowing the number and orders to depend on u.
`S` prescribes the allowed supports of the actual continuous densities. -/
def HasContinuousPrimitives {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} (u : ScalarDistribution 𝕜 Ω) (S : Set (Domain d)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → List (Fin d)) (f : ι → Domain d → 𝕜),
    (∀ j, Continuous (f j) ∧ HasCompactSupport (f j) ∧ tsupport (f j) ⊆ S) ∧
    ∀ φ : Tests 𝕜 Ω, u φ = ∑ j, continuousPrimitivePairing (w j) (f j) φ

end ExpandedFA.Distributions

namespace Specs.ExpandedFA.Distributions.ContinuousDistributionPrimitives
open _root_.ExpandedFA.Distributions

/-- Every point has an open neighborhood on which the distribution has finitely
many actual continuous primitives. No uniform order or global boundedness is
assumed. The pairing is with the original distribution via test inclusion. -/
def localPrimitivesType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω) (x : Domain d), x ∈ Ω →
  ∃ (U : Opens (Domain d)) (hU : U ≤ Ω), x ∈ U ∧
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → List (Fin d)) (f : ι → Domain d → 𝕜),
      (∀ j, ContinuousOn (f j) U) ∧
      ∀ φ : Tests 𝕜 U,
        u (TestFunction.monoCLM 𝕜 φ) =
          ∑ j, continuousPrimitivePairing (w j) (f j) φ

/-- For every prescribed V compactly contained in Ω and containing the compact
support of u, all continuous primitives have compact supports inside V. -/
def compactPrimitivesType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω V : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω),
  IsCompact (distributionSupport u) → distributionSupport u ⊆ V →
  IsCompact (closure (V : Set (Domain d))) → closure (V : Set (Domain d)) ⊆ Ω →
  HasContinuousPrimitives u V

/-- The global expansion is countable and locally finite on Ω, and its terms
are derivatives of genuine compactly supported continuous functions. Local
finiteness concerns the full topological supports, including those of their
derivatives; it is not convergence of a merely formal infinite series. -/
def globalPrimitivesType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω),
  ∃ (ι : Type) (_ : Countable ι) (w : ι → List (Fin d)) (f : ι → Domain d → 𝕜),
    (∀ j, Continuous (f j) ∧ HasCompactSupport (f j) ∧ tsupport (f j) ⊆ Ω) ∧
    LocallyFinite (fun j => (Subtype.val : Ω → Domain d) ⁻¹' tsupport (f j)) ∧
    ∀ φ : Tests 𝕜 Ω, u φ = ∑ᶠ j, continuousPrimitivePairing (w j) (f j) φ

end Specs.ExpandedFA.Distributions.ContinuousDistributionPrimitives
