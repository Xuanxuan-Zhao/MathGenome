import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SharpTraceExtension
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.TraceEndpointOne

/-! Independent scope of `paper.tex`, fa2:p4:sharp-trace (19147–19222).
The boundary model below identifies the *existing surface-measure quotient*
with the finite-atlas quotient. Its existence is an obligation, not a
hypothesis of the complete theorem. No trace or extension is a model field.
Both scalar fields, the one-dimensional half-line, and empty/zero-dimensional
bounded domains are retained. Only order 0 < s < 1 is transported by C1 charts.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev

/-- A finite geometric atlas together with the faithful change of measure
between the original surface Lp quotient and its atlas realization. The
agreement is required for every representative of the surface class.
The two Lp bounds exclude an unbounded change of measure. -/
structure BoundaryModel (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  chartCount : ℕ
  atlas : Boundary.FiniteAtlas (frontier (Ω : Set (Domain d))) (d - 1) (Fin chartCount)
  identify : BoundaryLp 𝕜 Ω p ≃ₗ[𝕜] Lp 𝕜 p atlas.atlasMeasure
  representative : ∀ (g : BoundaryLp 𝕜 Ω p) (f : Domain d → 𝕜),
    g =ᵐ[surfaceMeasure Ω] f →
    identify g =ᵐ[atlas.atlasMeasure] fun x => f x.val
  forwardConstant : ℝ
  backwardConstant : ℝ
  forward_nonneg : 0 ≤ forwardConstant
  backward_nonneg : 0 ≤ backwardConstant
  forward_bound : ∀ g, ‖identify g‖ ≤ forwardConstant * ‖g‖
  backward_bound : ∀ g, ‖g‖ ≤ backwardConstant * ‖identify g‖

namespace BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : BoundaryModel 𝕜 Ω p)

/-- Finite fractional energy in every localized chart; the datum remains
an element of the original surface-measure quotient. -/
def FiniteEnergy (s : ℝ) (g : BoundaryLp 𝕜 Ω p) : Prop :=
  ∀ j, differenceEnergy s p (B.atlas.localizedLp p j (B.identify g)) < ∞

abbrev Data (s : ℝ) := {g : BoundaryLp 𝕜 Ω p // B.FiniteEnergy s g}

def dataNorm (s : ℝ) (g : B.Data s) : ℝ :=
  B.atlas.fractionalNorm s p ⟨B.identify g.val, g.property⟩

end BoundaryModel
end ExpandedFA.PartIV.SharpTrace

namespace Specs.ExpandedFA.PartIV.SharpTrace
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.Trace _root_.ExpandedFA.Sobolev.C1Extension
open _root_.ExpandedFA.Sobolev.HalfSpace _root_.ExpandedFA.Sobolev.Lines
open _root_.ExpandedFA.PartIV.FractionalSobolev
open _root_.ExpandedFA.PartIV.SharpTraceBound _root_.ExpandedFA.PartIV.SharpTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Full half-space estimate, existence/uniqueness, and scalar-linear lift.
Both constants and all first weak derivatives are those of the upstream
full-norm statements, with no new certificate assumptions. -/
def HalfSpaceBoundAndLift : Prop :=
  SharpTraceBound.BoundedTrace ∧ SharpTraceExtension.BoundedRightInverse

def HalfSpaceOnto : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ ∞ →
    ∀ (i : Fin (n + 1))
      (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
        Lp 𝕜 p (volume : Measure (Transverse i))), CoordinateTraceCondition i T →
      ∀ g : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p,
        ∃ u, reindexedTrace i T u = g.val

/-- All finite exponents, including 1, have the original compact-test
closure as kernel. Half-spaces are unbounded, so bounded-domain kernel
theorems alone do not establish this clause. -/
def HalfSpaceKernel : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (i : Fin d)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))),
    (∀ (u : SpaceValue 𝕜 d (upper i) 1 p) (f : Domain d → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f →
      T u =ᵐ[volume] fun y : Transverse i => f (coordinateLine i y 0)) →
    T.ker = ZeroSpaceValue 𝕜 d (upper i) 1 p hp

def HalfSpaceEndpoint : Prop := TraceEndpointOne.OntoTraceExists

/-- Bounded C1 domains admit the geometric, surface-faithful boundary model.
No replacement of IsC1Domain by an assumed atlas or graph theorem is made. -/
def BoundaryModelsExist : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) → IsC1Domain Ω →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → Nonempty (BoundaryModel 𝕜 Ω p)

/-- Transport the sharp bound through charts and the subordinate partition
for every faithful finite atlas model, with the sum of full localized norms. -/
def DomainSharpBound : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) → IsC1Domain Ω →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ B : BoundaryModel 𝕜 Ω p, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u, ∃ h : B.FiniteEnergy (1 - 1 / p.toReal) (T u),
        B.dataNorm (1 - 1 / p.toReal) ⟨T u, h⟩ ≤ C * ‖u‖

/-- The right inverse is on every fractional datum of the actual boundary.
Linearity is expressed on underlying surface Lp classes because the
independent Specs do not install algebraic instances on the energy subtype. -/
def DomainRightInverse : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) → IsC1Domain Ω →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ B : BoundaryModel 𝕜 Ω p,
      ∃ (C : ℝ) (E : B.Data (1 - 1 / p.toReal) → SpaceValue 𝕜 d Ω 1 p),
        0 ≤ C ∧
        (∀ u v w, w.val = u.val + v.val → E w = E u + E v) ∧
        (∀ (c : 𝕜) u v, v.val = c • u.val → E v = c • E u) ∧
        (∀ u, ‖E u‖ ≤ C * B.dataNorm (1 - 1 / p.toReal) u) ∧
        (∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
          ∀ u, T (E u) = u.val)

/-- Surjectivity at 1 has no linear-lift assertion. -/
def DomainEndpoint : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) → IsC1Domain Ω →
    ∀ (T : SpaceValue 𝕜 d Ω 1 1 →L[𝕜] BoundaryLp 𝕜 Ω 1), IsTrace T →
      Function.Surjective T

def DomainKernel : Prop := Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.TraceKernel

/-- The complete original result, including existence of genuine traces.
The latter is kept explicit to avoid vacuous universal trace assertions. -/
def SharpTrace : Prop :=
  HalfSpaceBoundAndLift ∧ HalfSpaceOnto ∧ HalfSpaceEndpoint ∧ HalfSpaceKernel ∧
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.TraceExists ∧ BoundaryModelsExist ∧
    DomainSharpBound ∧ DomainRightInverse ∧ DomainEndpoint ∧ DomainKernel

/-- Assembly interface for the remaining chart obligations. -/
def Assembly : Prop :=
  BoundaryModelsExist → DomainSharpBound →
    DomainRightInverse → DomainEndpoint → SharpTrace

end Specs.ExpandedFA.PartIV.SharpTrace
