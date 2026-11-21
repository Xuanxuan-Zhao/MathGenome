import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.ModularFunction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.TransportIntegrable
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.TransportNonnegative

/-!
Independent statements of paper.tex:5954–5958. The modular scalar is the
shared real-valued function defined by μ(Ea) = Δ(a) μ(E). Positivity,
multiplicativity, preservation of one, and continuity as a real-valued map
express precisely a continuous homomorphism into the positive reals, with
their subspace topology. No countability or measure-size hypotheses occur.
Scalar integrals retain the source's actual Borel measurability and absolute
integrability; nonnegative integrals are allowed to be infinite.
-/
namespace Specs.D11.Ch21.ModularProperties

open MeasureTheory
open scoped ENNReal
open ModularFunction (modularFunction_value)
open Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch05.NonnegativeIntegral
universe u

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

def positive : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ a : G, 0 < modularFunction_value μ a

def map_one : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → modularFunction_value μ 1 = 1

def map_mul : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ a b : G,
      modularFunction_value μ (a * b) = modularFunction_value μ a * modularFunction_value μ b

def map_inv : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ a : G,
      modularFunction_value μ a⁻¹ = (modularFunction_value μ a)⁻¹

def continuous : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → Continuous (modularFunction_value μ)

def nonnegative_translation : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ (a : G) (f : G → ℝ≥0∞), Measurable f →
      nonnegativeIntegral_value μ (fun x => f (x * a⁻¹)) =
        ENNReal.ofReal (modularFunction_value μ a) * nonnegativeIntegral_value μ f

def scalar_translation : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure G (borel G)), HaarDefinition.leftHaarValue μ →
    ∀ (a : G) (f : G → 𝕜) (hf : scalarIntegrable_value μ f),
      ∃ ht : scalarIntegrable_value μ (fun x => f (x * a⁻¹)),
        scalarIntegral_value μ (fun x => f (x * a⁻¹)) ht =
          modularFunction_value μ a • scalarIntegral_value μ f hf

end Specs.D11.Ch21.ModularProperties
