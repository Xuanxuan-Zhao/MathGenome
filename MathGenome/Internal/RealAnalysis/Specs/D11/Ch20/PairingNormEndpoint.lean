import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.IntegralPairing
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.ExhaustionRestriction

/-! Independent statements for paper.tex:5661–5668.
The ordinary measurable a.e. quotient is identified with native Lp by the
accepted representative-preserving isometries in QuotientConstruction and the
accepted integral-pairing bridge. The pairing below is bilinear, with no
conjugation. Semifiniteness is required only on measurable sets, the domain of
the source measure; there is no completeness or sigma-finiteness assumption.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch20.PairingNormEndpoint

def IsSemifinite {X : Type u} [MeasurableSpace X] (μ : Measure X) : Prop :=
  ∀ E : Set X, MeasurableSet E →
    μ E = ⨆ (A : Set X) (_ : A ⊆ E) (_ : MeasurableSet A) (_ : μ A < ∞), μ A

def semifinite_type := ∀ {X : Type u} [MeasurableSpace X], Measure X → Prop

def semifinite_value : semifinite_type.{u} := fun μ => IsSemifinite μ

def sigmaFinite_semifinite : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X),
    SigmaFinite μ → IsSemifinite μ

def pairing_norm_endpoint : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X), IsSemifinite μ → ∀ g : Lp 𝕜 ∞ μ,
      ‖Specs.D11.Ch20.IntegralPairing.pairing_value μ 1 ∞ g‖ = ‖g‖

/-- The same equality on the literal ordinary measurable a.e. quotient, with
representative formulas fixing both its norm and its bilinear integral pairing.
All normed-space structures and the pairing are supplied as conclusions. -/
def ordinary_pairing_norm_endpoint : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X), IsSemifinite μ →
    ∃ G1 : NormedAddCommGroup (Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ 1), letI := G1
    ∃ V1 : NormedSpace 𝕜 (Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ 1), letI := V1
    ∃ Ginf : NormedAddCommGroup (Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ ∞), letI := Ginf
    ∃ Vinf : NormedSpace 𝕜 (Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ ∞), letI := Vinf
    ∃ B : Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ ∞ →L[𝕜]
      Specs.D11.Ch10.QuotientConstruction.QuotientLp (𝕜 := 𝕜) μ 1 →L[𝕜] 𝕜,
      (∀ f : Specs.D11.Ch10.QuotientConstruction.Raw (𝕜 := 𝕜) μ 1,
        ‖Specs.D11.Ch10.QuotientConstruction.classOf f‖ =
          (Specs.D11.Ch10.QuotientConstruction.sourceNorm μ 1 f.val).toReal) ∧
      (∀ g : Specs.D11.Ch10.QuotientConstruction.Raw (𝕜 := 𝕜) μ ∞,
        ‖Specs.D11.Ch10.QuotientConstruction.classOf g‖ =
          (Specs.D11.Ch10.QuotientConstruction.sourceNorm μ ∞ g.val).toReal) ∧
      (∀ (f : Specs.D11.Ch10.QuotientConstruction.Raw (𝕜 := 𝕜) μ 1)
         (g : Specs.D11.Ch10.QuotientConstruction.Raw (𝕜 := 𝕜) μ ∞),
        ∃ h : Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value μ
          (fun x => f.val x * g.val x),
          B (Specs.D11.Ch10.QuotientConstruction.classOf g)
            (Specs.D11.Ch10.QuotientConstruction.classOf f) =
            Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value μ
              (fun x => f.val x * g.val x) h) ∧
      (∀ g, ‖B g‖ = ‖g‖)

end Specs.D11.Ch20.PairingNormEndpoint
