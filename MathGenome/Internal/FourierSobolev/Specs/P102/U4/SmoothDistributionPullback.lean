import MathGenome.Internal.FourierSobolev.Specs.P102.U4.BiLipschitzPullback
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.Truncations
import Mathlib.Topology.Algebra.Module.Determinant

/-! Ordinary-distribution clause of paper.tex:1677–1688, including the
prerequisite clauses of U4-06. Ambient representatives are unrestricted away
from their domains. The inverse Jacobian is real and absolute; scalar
pairings are bilinear. No global Lipschitz or finite-volume assumption is
made on a smooth diffeomorphism. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff Distributions ENNReal
namespace P102.U4

/-- Smooth inverse maps between arbitrary open Euclidean sets. -/
structure SmoothChart {d : ℕ} (U V : Opens (Space d)) where
  toFun : Space d → Space d
  invFun : Space d → Space d
  mapsTo : MapsTo toFun V U
  inv_mapsTo : MapsTo invFun U V
  left_inv : ∀ x ∈ V, invFun (toFun x) = x
  right_inv : ∀ y ∈ U, toFun (invFun y) = y
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) toFun V
  inv_smooth : ContDiffOn ℝ (⊤ : ℕ∞) invFun U

namespace SmoothChart

def refl {d : ℕ} (U : Opens (Space d)) : SmoothChart U U where
  toFun := id
  invFun := id
  mapsTo := mapsTo_id _
  inv_mapsTo := mapsTo_id _
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl
  smooth := contDiffOn_id
  inv_smooth := contDiffOn_id

def symm {d : ℕ} {U V : Opens (Space d)} (g : SmoothChart U V) : SmoothChart V U where
  toFun := g.invFun
  invFun := g.toFun
  mapsTo := g.inv_mapsTo
  inv_mapsTo := g.mapsTo
  left_inv := g.right_inv
  right_inv := g.left_inv
  smooth := g.inv_smooth
  inv_smooth := g.smooth

/-- g:V→U followed contravariantly by h:W→V; the point map is g∘h. -/
def comp {d : ℕ} {U V W : Opens (Space d)}
    (g : SmoothChart U V) (h : SmoothChart V W) : SmoothChart U W where
  toFun := g.toFun ∘ h.toFun
  invFun := h.invFun ∘ g.invFun
  mapsTo := g.mapsTo.comp h.mapsTo
  inv_mapsTo := h.inv_mapsTo.comp g.inv_mapsTo
  left_inv := fun x hx => by
    simp only [Function.comp_apply, g.left_inv _ (h.mapsTo hx), h.left_inv _ hx]
  right_inv := fun y hy => by
    simp only [Function.comp_apply, h.right_inv _ (g.inv_mapsTo hy), g.right_inv _ hy]
  smooth := g.smooth.comp h.smooth h.mapsTo
  inv_smooth := h.inv_smooth.comp g.inv_smooth g.inv_mapsTo

/-- Absolute real inverse Jacobian, without an orientation restriction. -/
def inverseJacobian {d : ℕ} {U V : Opens (Space d)} (g : SmoothChart U V)
    (y : Space d) : ℝ := |(fderiv ℝ g.invFun y).det|

/-- Zero extension of the transported density from U. -/
def transportFunction {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (g : SmoothChart U V) (φ : Space d → 𝕜) : Space d → 𝕜 :=
  (U : Set (Space d)).indicator (fun y => g.inverseJacobian y • φ (g.invFun y))

/-- The graph specifies the map, without presuming its existence. -/
def HasTestTransportGraph {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (g : SmoothChart U V)
    (A : TestSpace 𝕜 V →L[𝕜] TestSpace 𝕜 U) : Prop :=
  ∀ φ x, A φ x = g.transportFunction φ x

end SmoothChart

namespace SmoothDistributionPullbackExpected

/-- Admissibility and the exact compact support direction. -/
def Admissibility : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (U V : Opens (Space d))
    (g : SmoothChart U V) (φ : TestSpace 𝕜 V),
    ∃ ψ : TestSpace 𝕜 U,
      (∀ y, ψ y = g.transportFunction φ y) ∧
      tsupport ψ ⊆ g.toFun '' tsupport φ

/-- Fixed-support transport, continuity in the original topology and its
finite derivative estimate. -/
def FixedSupportContinuity : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (U V : Opens (Space d))
    (g : SmoothChart U V) (K : Compacts (Space d)) (_hK : (K : Set (Space d)) ⊆ V),
    ∃ (J : Compacts (Space d)) (_hJ : (J : Set (Space d)) ⊆ U)
      (A : FixedSupport d 𝕜 K →L[𝕜] FixedSupport d 𝕜 J),
      (J : Set (Space d)) = g.toFun '' (K : Set (Space d)) ∧
      (∀ φ y, A φ y = g.transportFunction φ y) ∧
      ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ,
        ∀ φ, coordinateSupSeminorm 𝕜 J m (A φ) ≤ C * coordinateSupSeminorm 𝕜 K n φ

/-- Existence of the global continuous map on tests and of its continuous
scalar-linear transpose on ordinary distributions. The CLM topology on the
dual is uniform convergence on bounded sets. -/
def Construction : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (U V : Opens (Space d)) (g : SmoothChart U V),
    ∃ A : TestSpace 𝕜 V →L[𝕜] TestSpace 𝕜 U,
      g.HasTestTransportGraph A ∧
      ∃ P : DistributionSpace 𝕜 U →L[𝕜] DistributionSpace 𝕜 V,
        ∀ T φ, P T φ = T (A φ)

/-- Includes preservation of local integrability under the smooth chart.
The existence of A is asserted independently by Construction. -/
def RegularCompatibility : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (U V : Opens (Space d)) (g : SmoothChart U V)
    (A : TestSpace 𝕜 V →L[𝕜] TestSpace 𝕜 U),
    g.HasTestTransportGraph A → ∀ f : Space d → 𝕜,
    LocallyIntegrableOn f U volume →
      LocallyIntegrableOn (f ∘ g.toFun) V volume ∧
      (regularDistribution U f).comp A = regularDistribution V (f ∘ g.toFun)

/-- Identity laws on tests and distributions, independent of a choice of A. -/
def Identity : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (U : Opens (Space d))
    (A : TestSpace 𝕜 U →L[𝕜] TestSpace 𝕜 U),
    (SmoothChart.refl U).HasTestTransportGraph A →
      A = ContinuousLinearMap.id 𝕜 _ ∧
      ∀ T : DistributionSpace 𝕜 U, T.comp A = T

/-- Includes the Jacobian product and the contravariant composition law. -/
def Composition : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (U V W : Opens (Space d))
    (g : SmoothChart U V) (h : SmoothChart V W),
    (∀ y ∈ U, (g.comp h).inverseJacobian y =
      g.inverseJacobian y * h.inverseJacobian (g.invFun y)) ∧
    ∀ (Ag : TestSpace 𝕜 V →L[𝕜] TestSpace 𝕜 U)
      (Ah : TestSpace 𝕜 W →L[𝕜] TestSpace 𝕜 V)
      (Agh : TestSpace 𝕜 W →L[𝕜] TestSpace 𝕜 U),
      g.HasTestTransportGraph Ag → h.HasTestTransportGraph Ah →
      (g.comp h).HasTestTransportGraph Agh →
      Agh = Ag.comp Ah ∧
      ∀ T : DistributionSpace 𝕜 U, T.comp Agh = (T.comp Ag).comp Ah

/-- The remaining clauses of the source theorem, using exactly the existing
upstream interfaces, including all stated endpoints and zero-order cases. -/
def RetainedClauses : Prop :=
  ChainProductExpected.ChainRule ∧ ChainProductExpected.ProductRule ∧
  TruncationsExpected.LevelSet ∧ TruncationsExpected.Truncation ∧
  TruncationsExpected.LowerTruncation ∧ TruncationsExpected.UpperTruncation ∧
  BiLipschitzPullbackExpected.Derivative ∧ BiLipschitzPullbackExpected.Distortion ∧
  BiLipschitzPullbackExpected.LpPullback ∧ BiLipschitzPullbackExpected.SobolevPullback

end SmoothDistributionPullbackExpected
end P102.U4
