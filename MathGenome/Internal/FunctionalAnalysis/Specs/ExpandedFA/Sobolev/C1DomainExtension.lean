import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-! Independent statements of the compact-boundary C¹ part of
`fa2:p4:sobolev-extension`, paper.tex:17715–17757. There is no boundedness,
connectedness, positive-dimension, or finite-exponent restriction on the
extension theorem. Smoothness up to the boundary means restriction of a
smooth ambient function, and does not mean compact support in the domain. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal

namespace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- A C¹ boundary chart identifies the domain locally with an upper
half-space. Both the chart and its inverse have their actual C¹ regularity.
This geometric hypothesis contains no Sobolev transport or extension theorem. -/
def IsC1Domain {d : ℕ} (Ω : Opens (Domain d)) : Prop :=
  ∀ x ∈ frontier (Ω : Set (Domain d)),
    ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
      x ∈ Φ.source ∧ Φ x i = 0 ∧
      ContDiffOn ℝ 1 Φ Φ.source ∧ ContDiffOn ℝ 1 Φ.symm Φ.target ∧
      ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i

/-- Right inverse to restriction, expressed on the underlying Lp classes. -/
def IsExtension {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p) : Prop :=
  ∀ u, (E u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
    u.val (zeroIndex d 1)

/-- One raw scalar-linear formula induces all exponent-specific bounded
operators. Compatibility is required for every representative, not only the
representative chosen by Lp. In particular this relates different p's on their
intersection. The same bounded output neighborhood works for all p and u. -/
def HasSimultaneousExtension {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) : Prop :=
  ∃ T : (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜),
  ∃ E : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p,
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], IsExtension Ω (E p)) ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p)
        (f : Domain d → 𝕜),
      f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
      (E p u).val (zeroIndex d 1) =ᵐ[volume] T f) ∧
    (Bornology.IsBounded (Ω : Set (Domain d)) →
      ∃ U : Opens (Domain d), Bornology.IsBounded (U : Set (Domain d)) ∧
        closure (Ω : Set (Domain d)) ⊆ U ∧
        ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p),
          ∀ᵐ x ∂volume, x ∉ U → (E p u).val (zeroIndex d 1) x = 0)

/-- A common raw formula and its bounded Sobolev realizations, before the
optional bounded-support normalization. No existence is assumed here. -/
def HasCompatibleExtension {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) : Prop :=
  ∃ T : (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜),
  ∃ E : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p,
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], IsExtension Ω (E p)) ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p)
        (f : Domain d → 𝕜),
      f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
      (E p u).val (zeroIndex d 1) =ᵐ[volume] T f)

/-- Ambient smooth representatives, with no zero boundary condition. -/
def SmoothUpToBoundary {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Set (SpaceValue 𝕜 d Ω 1 p) :=
  {u | ∃ f : Domain d → 𝕜, ContDiff ℝ (⊤ : ℕ∞) f ∧
    u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f}

end ExpandedFA.Sobolev.C1Extension

namespace ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.Distributions
/-- The part of a chart source mapped into an ambient open domain. -/
def chartPreimage {d : ℕ} (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (Ω : Opens (Domain d)) : Opens (Domain d) :=
  ⟨Φ.source ∩ Φ ⁻¹' (Ω : Set (Domain d)),
    Φ.continuousOn.isOpen_inter_preimage Φ.open_source Ω.isOpen⟩

/-- The part of an ambient open domain inside the chart target. -/
def chartTarget {d : ℕ} (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (Ω : Opens (Domain d)) : Opens (Domain d) :=
  ⟨(Ω : Set (Domain d)) ∩ Φ.target, Ω.isOpen.inter Φ.open_target⟩


end ExpandedFA.Sobolev.C1Extension.Transport

namespace Specs.ExpandedFA.Sobolev.C1DomainExtension
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.C1Extension WeakDerivativeSpaces

/-- The elementary finite atlas extraction, separate from the analytic
Sobolev transport through its charts. -/
def FiniteBoundaryCharts : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d)),
    IsC1Domain Ω → IsCompact (frontier (Ω : Set (Domain d))) →
    ∃ (n : ℕ) (i : Fin n → Fin d)
      (Φ : Fin n → OpenPartialHomeomorph (Domain d) (Domain d)),
      (∀ j, ContDiffOn ℝ 1 (Φ j) (Φ j).source ∧
        ContDiffOn ℝ 1 (Φ j).symm (Φ j).target ∧
        ∀ y ∈ (Φ j).source, y ∈ Ω ↔ 0 < Φ j y (i j)) ∧
      frontier (Ω : Set (Domain d)) ⊆ ⋃ j, (Φ j).source

/-- Full compact-boundary extension obligation, including exterior domains. -/
def ExtensionExists : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), IsC1Domain Ω →
    IsCompact (frontier (Ω : Set (Domain d))) →
    HasSimultaneousExtension (𝕜 := 𝕜) Ω

/-- Full finite-p density conclusion of the source. -/
def SmoothDensity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), IsC1Domain Ω →
    IsCompact (frontier (Ω : Set (Domain d))) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p)

/-- The source's consequence is proved from the extension conclusion. This
helper does not assert the existence of the extension. -/
def DensityConsequence : Prop := ExtensionExists → SmoothDensity

def WholeSpaceExtension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  HasSimultaneousExtension (𝕜 := 𝕜) (⊤ : Opens (Domain d))

def EmptyExtension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  HasSimultaneousExtension (𝕜 := 𝕜) (⊥ : Opens (Domain d))

/-- Analytic implication used to deduce the density clause, on any domain
which has an extension at this exponent. -/
def DensityOfExtension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p,
      IsExtension Ω E → Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p)


/-- Smooth bounded ambient coefficients multiply W1p boundedly, including
p=infinity. The bound is independent of the exponent. -/
def AmbientSmoothMultiplier : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : Domain d → 𝕜), ContDiff ℝ (⊤ : ℕ∞) a →
    ∀ C : ℝ, 0 ≤ C → (∀ x, ‖a x‖ ≤ C) →
    (∀ j x, ‖partialFunction [j] a x‖ ≤ C) →
    ∃ M : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p,
      (∀ u, (M u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => a x * u.val (zeroIndex d 1) x) ∧
      ‖M‖ ≤ Fintype.card (DerivativeIndex d 1) * (2 * C)

/-- Postmultiplying by one ambient cutoff proves the full fixed-neighborhood
clause from compatible extension maps. No boundary regularity is needed for
this normalization. -/
def BoundedSupportReduction : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), HasCompatibleExtension (𝕜 := 𝕜) Ω →
      HasSimultaneousExtension (𝕜 := 𝕜) Ω


/-- Relative zero extension preserves all derivatives and is isometric when
the jet is supported inside the source, closed relative to the target. -/
def RelativeZeroExtension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω Λ : Opens (Domain d)), Ω ≤ Λ →
    ∀ (K : Set (Domain d)), IsClosed (K ∪ (Λ : Set (Domain d))ᶜ) → K ⊆ Ω →
    ∀ (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω m p),
    (∀ α, ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), x ∉ K → u.val α x = 0) →
    ∃ v : SpaceValue 𝕜 d Λ m p,
      (∀ α, v.val α =ᵐ[volume.restrict (Λ : Set (Domain d))]
        (Ω : Set (Domain d)).indicator (u.val α)) ∧ ‖v‖ = ‖u‖

/-- Smooth localization followed by zero extension across an artificial
boundary is bounded, with the same estimate for every exponent. -/
def LocalizedZeroExtension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω Λ : Opens (Domain d)), Ω ≤ Λ →
    ∀ (K : Set (Domain d)), IsClosed (K ∪ (Λ : Set (Domain d))ᶜ) → K ⊆ Ω →
    ∀ (a : Domain d → 𝕜), ContDiff ℝ (⊤ : ℕ∞) a →
    ∀ C : ℝ, 0 ≤ C → (∀ x, ‖a x‖ ≤ C) →
    (∀ j x, ‖partialFunction [j] a x‖ ≤ C) →
    (Ω : Set (Domain d)) ∩ tsupport a ⊆ K →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d Λ 1 p,
      (∀ u, (E u).val (zeroIndex d 1) =ᵐ[volume.restrict (Λ : Set (Domain d))]
        (Ω : Set (Domain d)).indicator (fun x => a x * u.val (zeroIndex d 1) x)) ∧
      ‖E‖ ≤ Fintype.card (DerivativeIndex d 1) * (2 * C)

/-- Finite smooth localization on ambient boundary patches, with a possibly
unbounded interior support. All coefficients and bounds precede p. -/
def FiniteSmoothLocalization : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d n : ℕ)
    (Ω : Opens (Domain d)) (U : Fin n → Set (Domain d)),
    (∀ j, IsOpen (U j)) →
    (frontier (Ω : Set (Domain d)) ⊆ ⋃ j, U j) →
    IsCompact (frontier (Ω : Set (Domain d))) →
    ∃ (a : Option (Fin n) → Domain d → 𝕜) (S : Set (Domain d)) (C : ℝ),
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j)) ∧ 0 ≤ C ∧
      (∀ j x, ‖a j x‖ ≤ C) ∧
      (∀ j i x, ‖partialFunction [i] (a j) x‖ ≤ C) ∧
      (∀ x, a none x + ∑ j, a (some j) x = 1) ∧
      (∀ j, HasCompactSupport (a (some j)) ∧ tsupport (a (some j)) ⊆ U j) ∧
      IsClosed S ∧ S ⊆ Ω ∧
      closure (Ω : Set (Domain d)) ∩ tsupport (a none) ⊆ S


/-- Boundary charts can all be chosen bounded, with a common finite bound
on both derivative matrices. This choice does not restrict the interior patch. -/
def FiniteBoundedBoundaryCharts : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d)),
    IsC1Domain Ω → IsCompact (frontier (Ω : Set (Domain d))) →
    ∃ (n : ℕ) (i : Fin n → Fin d)
      (Φ : Fin n → OpenPartialHomeomorph (Domain d) (Domain d)) (C : ℝ),
      0 ≤ C ∧
      (∀ j, ContDiffOn ℝ 1 (Φ j) (Φ j).source ∧
        ContDiffOn ℝ 1 (Φ j).symm (Φ j).target ∧
        Bornology.IsBounded (Φ j).source ∧ Bornology.IsBounded (Φ j).target ∧
        (∀ y ∈ (Φ j).source, y ∈ Ω ↔ 0 < Φ j y (i j)) ∧
        (∀ y ∈ (Φ j).source, ‖fderiv ℝ (Φ j) y‖ ≤ C) ∧
        (∀ y ∈ (Φ j).target, ‖fderiv ℝ (Φ j).symm y‖ ≤ C)) ∧
      frontier (Ω : Set (Domain d)) ⊆ ⋃ j, (Φ j).source

/-- Finitely many localized recovery operators, compatible with fixed raw
formulas, assemble to an extension with the bounded-neighborhood clause. -/
def FiniteExtensionAssembly : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (ι : Type) [Fintype ι] (Ω : Opens (Domain d)) (a : ι → Domain d → 𝕜),
    (∀ x ∈ Ω, ∑ j, a j x = 1) →
    ∀ (T : ι → (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜))
      (E : ι → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
        SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p),
    (∀ j (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p),
      (E j p u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => a j x * u.val (zeroIndex d 1) x) →
    (∀ j (p : ℝ≥0∞) [Fact (1 ≤ p)]
      (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
      (E j p u).val (zeroIndex d 1) =ᵐ[volume] T j f) →
    HasSimultaneousExtension (𝕜 := 𝕜) Ω

/-- In particular the compact-boundary theorem includes all domains with
empty frontier, in every dimension. -/
def FrontierEmptyExtension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), frontier (Ω : Set (Domain d)) = ∅ →
      HasSimultaneousExtension (𝕜 := 𝕜) Ω


/-- Actual chart pullback on Lp classes. Null-set compatibility, complex
linearity and a single exponent-independent bound are included. This alone
does not assert a weak chain rule. -/
def ChartLpTransport : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
    ContDiffOn ℝ 1 Φ.symm Φ.target →
    ∀ C : ℝ, (∀ y ∈ Φ.target, ‖fderiv ℝ Φ.symm y‖ ≤ C) →
    ∃ J : ℝ, 1 ≤ J ∧ ∀ (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)],
      ∃ P : DomainLp 𝕜 (Transport.chartTarget Φ Ω) p →L[𝕜]
          DomainLp 𝕜 (Transport.chartPreimage Φ Ω) p,
        (∀ (u : DomainLp 𝕜 (Transport.chartTarget Φ Ω) p) (f : Domain d → 𝕜),
          u =ᵐ[volume.restrict (Transport.chartTarget Φ Ω : Set (Domain d))] f →
          P u =ᵐ[volume.restrict (Transport.chartPreimage Φ Ω : Set (Domain d))] f ∘ Φ) ∧
        ‖P‖ ≤ J


/-- The interior contribution is compatible for every exponent and every
representative; its closed support is allowed to be unbounded. -/
def InteriorCompatiblePiece : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (a : Domain d → 𝕜), ContDiff ℝ (⊤ : ℕ∞) a →
    ∀ C : ℝ, 0 ≤ C → (∀ x, ‖a x‖ ≤ C) →
    (∀ j x, ‖partialFunction [j] a x‖ ≤ C) →
    ∀ (K : Set (Domain d)), IsClosed K → K ⊆ Ω →
    (Ω : Set (Domain d)) ∩ tsupport a ⊆ K →
    ∃ (T : (Domain d → 𝕜) →ₗ[𝕜] (Domain d → 𝕜))
      (E : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
        SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p),
      (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p),
        (E p u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
          fun x => a x * u.val (zeroIndex d 1) x) ∧
      (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
        f =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) →
        (E p u).val (zeroIndex d 1) =ᵐ[volume] T f)

end Specs.ExpandedFA.Sobolev.C1DomainExtension
