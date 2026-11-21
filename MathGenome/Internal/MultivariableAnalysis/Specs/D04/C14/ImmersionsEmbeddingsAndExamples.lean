import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.RegularLevelsAndGraphs
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.SubmersionImmersion
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.CircleMultiplicity
import Mathlib.Topology.Homeomorph.Lemmas

/-! Independent scope of d04:14:immersion. Boundary regularity is the shared
local extension condition; the embedding condition is exactly Chapter 4's.
The circle examples use the Chapter 9 circle, with E 1 as real parameter space.
Multiplicity is expressed by two bijective half-open turns (endpoint copies
are excluded), as well as the already defined traversal length. -/
noncomputable section
open Set Topology
open scoped ContDiff
namespace Specs.D04.C14.ImmersionsEmbeddingsAndExamples
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C04.SubmersionImmersion.Model
open Specs.D04.C09.CircleMultiplicity.Model
namespace Model

def Immersion (r : ℕ∞ω) {k n : ℕ} (V : Set (E k)) (f : E k → E n) : Prop :=
  ManifoldRegularity r ∧ FullRankLocalExtension r V f

def Embedding (r : ℕ∞ω) {k n : ℕ} (V : Set (E k)) (f : E k → E n) : Prop :=
  Immersion r V f ∧ EmbeddingOn f V

/-- The real coordinate identification, also used for the half-open example. -/
def realParameter (t : ℝ) : E 1 := WithLp.toLp 2 (fun _ => t)
def circleParam (m : ℤ) (u : E 1) : E 2 := circle m (u 0)
def turnDomain : Set (E 1) := {u | u 0 ∈ Ico (0 : ℝ) (2*Real.pi)}
def unitSphere (n : ℕ) : Set (E n) := {x | ‖x‖ = 1}

/-- A total extension of the inverse angle on the image of the half-open turn.
Its values away from the image have no role in continuity within the image. -/
def inverseAngle (x : E 2) : ℝ := by
  classical
  exact if h : ∃ t ∈ Ico (0 : ℝ) (2*Real.pi), circle 1 t = x
    then Classical.choose h else 0

end Model
open Model
abbrev ImmersionType := (r : ℕ∞ω) → {k n : ℕ} → Set (E k) → (E k → E n) → Prop
def ImmersionValue : ImmersionType := @Model.Immersion
abbrev EmbeddingType := ImmersionType
def EmbeddingValue : EmbeddingType := @Model.Embedding
abbrev realParameterType := ℝ → E 1
def realParameterValue : realParameterType := Model.realParameter
abbrev circleParamType := ℤ → E 1 → E 2
def circleParamValue : circleParamType := Model.circleParam
abbrev turnDomainType := Set (E 1)
def turnDomainValue : turnDomainType := Model.turnDomain
abbrev unitSphereType := (n : ℕ) → Set (E n)
def unitSphereValue : unitSphereType := Model.unitSphere
abbrev inverseAngleType := E 2 → ℝ
def inverseAngleValue : inverseAngleType := Model.inverseAngle

def immersion_open_iffType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} (V : Set (E k)) (f : E k → E n), IsOpen V →
    (Immersion r V f ↔ ManifoldRegularity r ∧ ContDiffOn ℝ r f V ∧
      ∀ u ∈ V, ImmersionAt f u)

def embedding_agreementType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} (V : Set (E k)) (f : E k → E n),
    (Embedding r V f ↔ Immersion r V f ∧
      ∃ e : V ≃ₜ (f '' V), ∀ u : V, (e u).val = f u)

/-- In particular this includes half-space boundary centers. No global
injectivity, compactness, or regular inverse is an input assumption. -/
def immersion_local_patchType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} (V : Set (E k)) (f : E k → E n) (half : Bool),
    (half = true → 0 < k) →
    (∃ O : Set (E k), IsOpen O ∧ V = parameterSpace k half ∩ O) →
    Immersion r V f → ∀ u ∈ V,
    ∃ (X : Set (E k)) (c : EmbeddedChart r k n (f '' (V ∩ X))),
      IsOpen X ∧ u ∈ X ∧ c.half = half ∧ c.source = V ∩ X ∧ c.toFun = f ∧
      Embedding r (V ∩ X) f

def compact_injective_homeomorphType : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] {n : ℕ} (f : X → E n),
    Continuous f → Function.Injective f →
      ∃ e : X ≃ₜ Set.range f, ∀ x, (e x).val = f x

def compact_injective_immersionType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} (V : Set (E k)) (f : E k → E n),
    IsCompact V → Immersion r V f → InjOn f V → Embedding r V f

/-- Exact full-column-rank calculation for the actual circle derivative. -/
def circle_immersionType : Prop :=
  ∀ (m : ℤ), m ≠ 0 →
    Immersion ∞ univ (circleParam m) ∧
    ∀ u, ImmersionAt (circleParam m) u ∧
      Module.finrank ℝ (LinearMap.range (fderiv ℝ (circleParam m) u).toLinearMap) = 1

def twice_traversed_circleType : Prop :=
  BijOn (circle 2) (Ico (0 : ℝ) Real.pi) (unitSphere 2) ∧
  BijOn (circle 2) (Ico Real.pi (2*Real.pi)) (unitSphere 2) ∧
  ¬ InjOn (circle 2) (Ico (0 : ℝ) (2*Real.pi)) ∧
  Specs.D04.C09.PathsLength.Model.length (circle 2) 0 (2*Real.pi) =
    ENNReal.ofReal (4*Real.pi)

/-- Every point has exactly two parameters in the full half-open double turn. -/
def twice_circle_fibersType : Prop :=
  ∀ x ∈ unitSphere 2, ∃ s ∈ Ico (0 : ℝ) Real.pi,
    ∃ t ∈ Ico Real.pi (2*Real.pi), s ≠ t ∧
      circle 2 s = x ∧ circle 2 t = x ∧
      ∀ v ∈ Ico (0 : ℝ) (2*Real.pi), circle 2 v = x ↔ v = s ∨ v = t

def half_open_circleType : Prop :=
  InjOn (circleParam 1) turnDomain ∧
  circleParam 1 '' turnDomain = unitSphere 2 ∧
  Immersion ∞ turnDomain (circleParam 1) ∧
  (∀ t ∈ Ico (0 : ℝ) (2*Real.pi), inverseAngle (circle 1 t) = t) ∧
  ¬ ContinuousWithinAt inverseAngle (unitSphere 2) (circle 1 0) ∧
  ¬ Embedding ∞ turnDomain (circleParam 1) ∧ ¬ IsCompact turnDomain

/-- The (n+1)-dimensional ambient sphere includes the zero-sphere case n=0. -/
def sphere_boundariesType : Prop :=
  ∀ (n : ℕ) (r : ℕ∞ω), ManifoldRegularity r →
    IsEmbeddedManifold r n (unitSphere (n+1)) ∧
    intrinsicBoundary r n (unitSphere (n+1)) = ∅ ∧
    frontier (unitSphere (n+1)) = unitSphere (n+1)

end Specs.D04.C14.ImmersionsEmbeddingsAndExamples
