import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.MobiusEmbedding
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.SurfaceAssembly

/-! The continuous-normal obstruction and unsigned integration for the actual
embedded strip of d04:10:mobius. No normal field is assumed in scalar integration. -/
noncomputable section
open Set Topology
open scoped RealInnerProductSpace BigOperators
namespace Specs.D04.C10.MobiusNonorientability
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C10.MobiusEmbedding.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model

namespace Model
/-- The center line in the original parameter rectangle, before identifying its ends. -/
def centerParameter (u : ℝ) : E 2 := WithLp.toLp 2 ![u, 0]
end Model
open Model

def center_normalType : Prop := ∀ (R : ℝ), 0 < R → ∀ u : ℝ,
  unitNormal (phi R) (centerParameter u) =
    WithLp.toLp 2 ![Real.sin (u / 2) * Real.cos u,
      Real.sin (u / 2) * Real.sin u, -Real.cos (u / 2)]

def normal_flipType : Prop := ∀ (R : ℝ), 0 < R →
  unitNormal (phi R) (centerParameter (2 * Real.pi)) =
    -unitNormal (phi R) (centerParameter 0)

/-- Any continuous unit-normal lift along the cut center curve has one sign.
This is a statement about the actual derivative planes, not assumed sign data. -/
def center_constant_signType : Prop := ∀ (R : ℝ), 0 < R →
  ∀ v : ℝ → E 3, ContinuousOn v (Icc 0 (2 * Real.pi)) →
  (∀ u ∈ Icc 0 (2 * Real.pi),
    IsUnitNormal (tangentPlane (phi R) (centerParameter u)) (v u)) →
  (∀ u ∈ Icc 0 (2 * Real.pi), v u = unitNormal (phi R) (centerParameter u)) ∨
  (∀ u ∈ Icc 0 (2 * Real.pi), v u = -unitNormal (phi R) (centerParameter u))

def nonorientableType : Prop := ∀ (R a : ℝ), 0 < a → a < R →
  IsEmpty (UnitNormalField (strip R a))

/-- Existence of integrable finite Gram localization, and independence of every
admissible chart partition. Taking f=1 gives the unsigned scalar area. -/
def scalar_integrationType : Prop := ∀ (R a : ℝ), 0 < a → a < R →
  (∀ (c : EmbeddedChart 1 2 3 (strip R a)) (u : c.source), 0 < chartDensity c u) ∧
  ∀ f : strip R a → ℝ, Continuous f →
    (∃ P : ChartPartition 1 2 (strip R a) (tsupport f),
      (∀ i, ProperIntegrable (localizedDensityCoefficient f (P.chart i) (P.weight i))) ∧
      surfaceIntegral (strip R a) f = ∑ i,
        coefficientIntegral (localizedDensityCoefficient f (P.chart i) (P.weight i))) ∧
    (∀ {K : Set (strip R a)} (P : ChartPartition 1 2 (strip R a) K), tsupport f ⊆ K →
      surfaceIntegral (strip R a) f = ∑ i,
        coefficientIntegral (localizedDensityCoefficient f (P.chart i) (P.weight i)))

end Specs.D04.C10.MobiusNonorientability
