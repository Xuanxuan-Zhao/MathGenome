import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.DiscreteSubset

/-! The common Euclidean chart representation for Chapters 10, 12, 14 and 15.
No transitions, tangent-space independence, or integration result is assumed here.
Finite positive orders and smoothness are admitted; the analytic order ω is excluded.
An injective derivative from E k is the full-column-rank condition.
Maps and their inverses are ambient functions whose values off their stated domains
have no geometric meaning. Half-space regularity is LOCAL extendibility, not the
existence of a single extension over the entire parameter domain. -/
noncomputable section
open Set Topology
open scoped ContDiff
namespace Specs.D04.C14.EmbeddedManifoldCharts
open Specs.D04.C01.EuclideanInterfaces.Model

namespace Model

def ManifoldRegularity (r : ℕ∞ω) : Prop := 1 ≤ r ∧ r ≤ ∞

/-- Coordinate k is indexed by `Fin.last d` when k = d+1.
The zero-dimensional convention does not authorize half-space charts in dimension zero. -/
def halfSpace : (k : ℕ) → Set (E k)
  | 0 => univ
  | d + 1 => {u | 0 ≤ u (Fin.last d)}

def flatBoundary : (k : ℕ) → Set (E k)
  | 0 => ∅
  | d + 1 => {u | u (Fin.last d) = 0}

def parameterSpace (k : ℕ) (half : Bool) : Set (E k) :=
  if half then halfSpace k else univ

/-- Every parameter point has an open Euclidean full-rank C^r extension.
For an open parameter domain this is equivalent to being C^r of rank k there. -/
def FullRankLocalExtension (r : ℕ∞ω) {k n : ℕ}
    (V : Set (E k)) (f : E k → E n) : Prop :=
  ∀ u ∈ V, ∃ (W : Set (E k)) (g : E k → E n),
    IsOpen W ∧ u ∈ W ∧ EqOn g f (V ∩ W) ∧ ContDiffOn ℝ r g W ∧
      ∀ v ∈ W, Function.Injective (fderiv ℝ g v)

/-- A chart is a homeomorphism from a relatively open model domain to M∩O.
The inverse identities and the two continuity fields give precisely that
homeomorphism, without assuming a smooth inverse or any transition theorem. -/
structure EmbeddedChart (r : ℕ∞ω) (k n : ℕ) (M : Set (E n)) where
  half : Bool
  half_pos : half = true → 0 < k
  source : Set (E k)
  source_open : ∃ W : Set (E k), IsOpen W ∧ source = parameterSpace k half ∩ W
  ambient : Set (E n)
  ambient_open : IsOpen ambient
  toFun : E k → E n
  invFun : E n → E k
  map_source : MapsTo toFun source (M ∩ ambient)
  map_target : MapsTo invFun (M ∩ ambient) source
  left_inv : ∀ u ∈ source, invFun (toFun u) = u
  right_inv : ∀ x ∈ M ∩ ambient, toFun (invFun x) = x
  continuous_toFun : ContinuousOn toFun source
  continuous_invFun : ContinuousOn invFun (M ∩ ambient)
  regular : FullRankLocalExtension r source toFun

/-- The marked center of a half-space chart must lie on its flat boundary.
A chart itself may also contain interior parameter points. -/
def CenteredAt {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (u : E k) : Prop :=
  u ∈ c.source ∧ (c.half = true → u ∈ flatBoundary k)

def IsEmbeddedManifold (r : ℕ∞ω) (k : ℕ) {n : ℕ} (M : Set (E n)) : Prop :=
  ManifoldRegularity r ∧ k ≤ n ∧
    ∀ x ∈ M, ∃ (c : EmbeddedChart r k n M) (u : E k),
      CenteredAt c u ∧ c.toFun u = x

/-- The intrinsic boundary is defined by flat-boundary chart points, not by
ambient frontier. Its chart independence is a later theorem. -/
def intrinsicBoundary (r : ℕ∞ω) (k : ℕ) {n : ℕ} (M : Set (E n)) : Set (E n) :=
  {x ∈ M | ∃ (c : EmbeddedChart r k n M) (u : E k),
    c.half = true ∧ u ∈ c.source ∧ u ∈ flatBoundary k ∧ c.toFun u = x}

end Model
open Model

-- Types and values of the canonical definitions.
abbrev ManifoldRegularityType := ℕ∞ω → Prop
def ManifoldRegularityValue : ManifoldRegularityType := Model.ManifoldRegularity
abbrev halfSpaceType := (k : ℕ) → Set (E k)
def halfSpaceValue : halfSpaceType := Model.halfSpace
abbrev flatBoundaryType := (k : ℕ) → Set (E k)
def flatBoundaryValue : flatBoundaryType := Model.flatBoundary
abbrev parameterSpaceType := (k : ℕ) → Bool → Set (E k)
def parameterSpaceValue : parameterSpaceType := Model.parameterSpace
abbrev FullRankLocalExtensionType := (r : ℕ∞ω) → {k n : ℕ} →
  Set (E k) → (E k → E n) → Prop
def FullRankLocalExtensionValue : FullRankLocalExtensionType := @Model.FullRankLocalExtension
abbrev EmbeddedChartType := ℕ∞ω → (k n : ℕ) → Set (E n) → Type
def EmbeddedChartValue : EmbeddedChartType := Model.EmbeddedChart
abbrev CenteredAtType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  EmbeddedChart r k n M → E k → Prop
def CenteredAtValue : CenteredAtType := @Model.CenteredAt
abbrev IsEmbeddedManifoldType := ℕ∞ω → ℕ → {n : ℕ} → Set (E n) → Prop
def IsEmbeddedManifoldValue : IsEmbeddedManifoldType := @Model.IsEmbeddedManifold
abbrev intrinsicBoundaryType := ℕ∞ω → ℕ → {n : ℕ} → Set (E n) → Set (E n)
def intrinsicBoundaryValue : intrinsicBoundaryType := @Model.intrinsicBoundary

-- Independent full propositions; none is an assumed certificate.
def halfSpace_succType : Prop := ∀ (d : ℕ) (u : E (d+1)),
  u ∈ halfSpace (d+1) ↔ 0 ≤ u (Fin.last d)
def flatBoundary_succType : Prop := ∀ (d : ℕ) (u : E (d+1)),
  u ∈ flatBoundary (d+1) ↔ u (Fin.last d) = 0

def embeddedChart_homeomorphType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M),
    ∃ e : c.source ≃ₜ ↥(M ∩ c.ambient), ∀ u : c.source, (e u).val = c.toFun u

def embeddedChart_restrictType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M)
    (O : Set (E n)), IsOpen O → ∃ d : EmbeddedChart r k n M,
      d.half = c.half ∧ d.source = c.source ∩ c.toFun ⁻¹' O ∧
      d.ambient = c.ambient ∩ O ∧ d.toFun = c.toFun ∧ d.invFun = c.invFun

def embeddedChart_restrict_parameterType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M)
    (W : Set (E k)), IsOpen W → ∃ d : EmbeddedChart r k n M,
      d.source = c.source ∩ W ∧ d.ambient ⊆ c.ambient ∧
      d.toFun = c.toFun ∧ d.invFun = c.invFun ∧ d.half = c.half

def centered_restrictionType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M)
    (u : E k) (O : Set (E n)), CenteredAt c u → IsOpen O → c.toFun u ∈ O →
      ∃ d : EmbeddedChart r k n M, CenteredAt d u ∧
        d.source = c.source ∩ c.toFun ⁻¹' O ∧ d.ambient = c.ambient ∩ O ∧
        d.toFun = c.toFun ∧ d.invFun = c.invFun ∧ d.half = c.half

/-- This checks the rank convention on the actual derivative, with no added
hypothesis on its image. -/
def derivative_rankType : Prop :=
  ∀ {k n : ℕ} (A : E k →L[ℝ] E n), Function.Injective A →
    Module.finrank ℝ (LinearMap.range A.toLinearMap) = k

/-- Open-domain maps give the same local extension notion, with no global
extension or inverse-regularity assumption. -/
def open_fullRankLocalExtension_iffType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} (V : Set (E k)) (f : E k → E n), IsOpen V →
    (FullRankLocalExtension r V f ↔
      ContDiffOn ℝ r f V ∧ ∀ u ∈ V, Function.Injective (fderiv ℝ f u))

def zero_manifold_iff_discreteType : Prop :=
  ∀ (r : ℕ∞ω) {n : ℕ} (M : Set (E n)),
    IsEmbeddedManifold r 0 M ↔ ManifoldRegularity r ∧ IsDiscrete M

def zero_intrinsicBoundaryType : Prop :=
  ∀ (r : ℕ∞ω) {n : ℕ} (M : Set (E n)), intrinsicBoundary r 0 M = ∅

def compact_zero_manifold_finiteType : Prop :=
  ∀ (r : ℕ∞ω) {n : ℕ} (M : Set (E n)),
    IsEmbeddedManifold r 0 M → Compact M → M.Finite

end Specs.D04.C14.EmbeddedManifoldCharts
