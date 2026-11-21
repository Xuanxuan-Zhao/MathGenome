import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.CellStokesC1
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.GeneralizedStokes

/-! Exact integrals on cycles, paper.tex, d04:15:exact-cycles.

The dimension is written as d+1, covering every k ≥ 1, including curves.
Chains are the shared finite formal integer combinations of C¹ cells.
The primitive is C¹; no second derivative of it is assumed. Manifold
integrals use the shared signed chart integrals and intrinsic tangent spaces.
-/
noncomputable section

namespace Specs.D04.C15.ExactFormsIntegrateToZeroOnCycles
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C15.IntrinsicExteriorDerivative.Model
open Specs.D04.C15.GeneralizedStokes.Model

/-- The form's open domain need only contain the images of the supported
cells. A cycle means its formal boundary is zero, without a quotient by
reparametrizations. -/
def exact_chain_integral_zeroType : Prop :=
  ∀ {d n : ℕ} {O : Set (E n)} (C : Chain 1 (d+1) O)
    (V : Set (E n)) (eta : FormField n d),
    IsCrForm (some 1) V eta →
    (∀ c ∈ C.support, ∀ x : cube (d+1), (c.toFun x).val ∈ V) →
    chainBoundarySucc C = 0 → chainIntegral (exteriorDerivative eta) C = 0

/-- Every C¹ intrinsic primitive is admissible on a compact oriented C²
embedded manifold with empty intrinsic boundary. The conclusion includes
existence of the proper localized integrals and their value for every
allowed signed chart partition. -/
def exact_intrinsic_integral_zeroType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 2 (d+1) M),
    IsCompact M → intrinsicBoundary 2 (d+1) M = ∅ →
    ∀ eta : IntrinsicForm (k := d+1) M d, IntrinsicC1 eta →
      HasPositiveIntegral o (intrinsicExteriorDerivative eta) 0

/-- On a compact oriented C¹ embedded manifold, differentiate the ambient
C¹ primitive and restrict its derivative to the tangent spaces. -/
def exact_ambient_integral_zeroType : Prop :=
  ∀ {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 (d+1) M),
    IsCompact M → intrinsicBoundary 1 (d+1) M = ∅ →
    ∀ (V : Set (E n)) (eta : FormField n d),
      M ⊆ V → IsCrForm (some 1) V eta →
      HasPositiveIntegral o
        (tangentRestriction 1 (d+1) M (exteriorDerivative eta)) 0

end Specs.D04.C15.ExactFormsIntegrateToZeroOnCycles
