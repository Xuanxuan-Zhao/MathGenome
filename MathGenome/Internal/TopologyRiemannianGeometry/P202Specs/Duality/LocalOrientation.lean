import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.RelativeSingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringLifting
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Atlases
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Data.ZMod.Basic

/-!
Local orientation objects for paper.tex, T29, 2040--2077.
The coefficient ring is any commutative unital ring (paper.tex 1027).
Manifolds include dimension zero and the empty manifold. All groups below are
ordinary relative singular homology, with the same integer indexing and
functor as the upstream pair sequence; no replacement homology theory is used.

An orientation is locally the restriction of a generator supported on a closed
coordinate ball. The expected independence statement below compares this with
the source's chartwise locally constant unit formulation on every ball.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
namespace P202Specs.LocalOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains

/-- Reuse P104's topological model, with its given topology, separation and
countability fields, and charts into the full Euclidean model. -/
abbrev Manifold (n : ℕ) (M : Type v) [TopologicalSpace M] :=
  SmoothManifolds.ModelData.TopologicalManifold n .euclidean M

abbrev Coordinate (n : ℕ) := SmoothManifolds.ModelData.ModelSpace n .euclidean
def coordinateOrigin (n : ℕ) : Coordinate n := ⟨0, Set.mem_univ _⟩

abbrev Chart (n : ℕ) (M : Type v) [TopologicalSpace M] :=
  SmoothManifolds.ModelData.ModelChart n .euclidean M

/-- The forgetful bridge discards smooth compatibility, retaining all chart data. -/
def forgetSmooth {n : ℕ} {M : Type v} [TopologicalSpace M]
    (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M) : Manifold n M :=
  S.topologicalManifold

/-- The local pair is (M, M minus the point), including in dimension zero. -/
def localPair (M : Type v) [TopologicalSpace M] (x : M) : Pair.{v} :=
  ⟨TopCat.of M, {y | y ≠ x}⟩

/-- Homology with support in K means the ordinary pair (M, M minus K). -/
def supportedPair (M : Type v) [TopologicalSpace M] (K : Set M) : Pair.{v} :=
  ⟨TopCat.of M, Kᶜ⟩

/-- Restriction of support, covariant on the associated relative pairs. -/
def supportMap {M : Type v} [TopologicalSpace M] {K L : Set M} (h : K ⊆ L) :
    supportedPair M L ⟶ supportedPair M K :=
  ⟨𝟙 _, fun _ hx hy => hx (h hy)⟩

/-- Restriction to the actual local pair, avoiding a cast between equal pairs. -/
def pointMap {M : Type v} [TopologicalSpace M] {K : Set M} {x : M} (hx : x ∈ K) :
    supportedPair M K ⟶ localPair M x :=
  ⟨𝟙 _, fun y hy he => hy (by change y = x at he; simpa only [he] using hx)⟩

abbrev LocalGroup (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]
    (x : M) (j : ℕ) := relativeHomology R R (localPair M x) (j : ℤ)

abbrev SupportedGroup (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]
    (K : Set M) (j : ℕ) := relativeHomology R R (supportedPair M K) (j : ℤ)

def restrictPoint (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    {K : Set M} {x : M} (hx : x ∈ K) (j : ℕ) :
    SupportedGroup R M K j →ₗ[R] LocalGroup R M x j :=
  ((relativeHomologyFunctor R R (j : ℤ)).map (pointMap hx)).hom

/-- A generator is a basis vector of a free rank-one module, not merely an
element spanning a possibly nonfree cyclic module. This also handles the zero ring. -/
def IsGenerator (R : Type u) [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    (o : V) : Prop := Function.Bijective (fun r : R => r • o)

abbrev Generators (R : Type u) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V] :=
  {o : V // IsGenerator R o}

/-- A relatively compact coordinate ball; neither chart compatibility nor any
homology assertion is part of these geometric data. -/
structure CoordinateBall {n : ℕ} {M : Type v} [TopologicalSpace M] (A : Manifold n M) where
  chart : Chart n M
  chart_mem : chart ∈ A.atlas
  center : Coordinate n
  radius : ℝ
  radius_pos : 0 < radius
  closedBall_subset : Metric.closedBall center radius ⊆ chart.target

namespace CoordinateBall
variable {n : ℕ} {M : Type v} [TopologicalSpace M] {A : Manifold n M}

def closed (B : CoordinateBall A) : Set M :=
  B.chart.source ∩ B.chart ⁻¹' Metric.closedBall B.center B.radius

def interior (B : CoordinateBall A) : Set M :=
  B.chart.source ∩ B.chart ⁻¹' Metric.ball B.center B.radius

lemma interior_subset_closed (B : CoordinateBall A) : B.interior ⊆ B.closed :=
  fun _ hx => ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩

end CoordinateBall

/-- The chart domain pair and its actual inclusion into the ambient local pair. -/
def chartLocalPair {n : ℕ} {M : Type v} [TopologicalSpace M]
    (c : Chart n M) (x : c.source) : Pair.{v} :=
  ⟨TopCat.of c.source, {y | y.val ≠ x.val}⟩

def chartInclusion {n : ℕ} {M : Type v} [TopologicalSpace M]
    (c : Chart n M) (x : c.source) : chartLocalPair c x ⟶ localPair M x.val :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, fun _ h => h⟩

/-- The canonical inclusion of local pairs for a subspace. Its definition
belongs to the shared objects, so independent downstream Specs do not import
an implementation just to name this map. Openness is needed for excision,
not for the existence of this pair map. -/
def openLocalInclusion {M : Type v} [TopologicalSpace M]
    (U : Set M) (x : U) : localPair U x ⟶ localPair M x.val where
  map := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  mapsTo := by
    intro y hy he
    exact hy (Subtype.ext he)

/-- A local choice of generators; regularity is stated separately. -/
abbrev LocalChoice (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M] :=
  (x : M) → LocalGroup R M x n

/-- The source's local compatibility in its ball-class form. Existence of the
ball generators and comparison with every other ball are conclusions below. -/
def IsOrientation (R : Type u) [CommRing R] {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) (o : LocalChoice R n M) : Prop :=
  (∀ x, IsGenerator R (o x)) ∧ ∀ x, ∃ (B : CoordinateBall A), x ∈ B.interior ∧
    ∃ g : SupportedGroup R M B.closed n, IsGenerator R g ∧
      ∀ (y : M) (hy : y ∈ B.interior),
        restrictPoint R (B.interior_subset_closed hy) n g = o y

abbrev Orientation (R : Type u) [CommRing R] {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) := {o : LocalChoice R n M // IsOrientation R A o}

/-- The integral orientation cover uses the generators of these very same
local homology groups as its fibers. -/
abbrev IntegralFiber {n : ℕ} {M : Type v} [TopologicalSpace M]
    (_A : Manifold n M) (x : M) := Generators ℤ (LocalGroup ℤ M x n)

abbrev IntegralCover {n : ℕ} {M : Type v} [TopologicalSpace M] (A : Manifold n M) :=
  (x : M) × IntegralFiber A x

def basicSheet {n : ℕ} {M : Type v} [TopologicalSpace M] {A : Manifold n M}
    (B : CoordinateBall A) (g : SupportedGroup ℤ M B.closed n) : Set (IntegralCover A) :=
  {z | ∃ hx : z.1 ∈ B.interior,
    z.2.val = restrictPoint ℤ (B.interior_subset_closed hx) n g}

/-- Topology generated by the signed ball generators; it is not assumed to be
a covering topology. The covering and chart statements below must prove that. -/
instance integralCoverTopology {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) : TopologicalSpace (IntegralCover A) :=
  TopologicalSpace.generateFrom {U | ∃ (B : CoordinateBall A)
    (g : SupportedGroup ℤ M B.closed n), IsGenerator ℤ g ∧ U = basicSheet B g}

namespace Expected

def orientation_type :=
  (R : Type u) → [CommRing R] → {n : ℕ} → {M : Type v} → [TopologicalSpace M] →
    Manifold n M → Type (max u v)

def orientation_value : orientation_type.{u,v} := @Orientation


def forgetSmooth_type :=
  ∀ {n : ℕ} {M : Type v} [TopologicalSpace M],
    SmoothManifolds.AtlasData.SmoothManifold n .euclidean M → Manifold n M

def forgetSmooth_value : forgetSmooth_type.{v} := @forgetSmooth


/-- Complete local computation, all nonnegative degrees and all coefficient rings. -/
def localHomology : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (_A : Manifold n M) (x : M) (j : ℕ),
    (j = n → Nonempty (LocalGroup R M x j ≃ₗ[R] R)) ∧
    (j ≠ n → IsZero (LocalGroup R M x j))

/-- The complete point/empty boundary case, for arbitrary zero-manifolds. -/
def zeroLocalHomology : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]
    (_A : Manifold 0 M) (x : M) (j : ℕ),
    (j = 0 → Nonempty (LocalGroup R M x j ≃ₗ[R] R)) ∧
    (j ≠ 0 → IsZero (LocalGroup R M x j))

/-- Excision uses the actual chart inclusion, including for n=0. -/
def chartExcision : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (_A : Manifold n M) (c : Chart n M) (x : c.source) (j : ℕ),
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (chartInclusion c x))

/-- Local Euclidean comparison without fixing a chart center or choosing a
smooth structure. Together with chartExcision this records the chart bridge. -/
def euclideanComparison : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (_A : Manifold n M) (x : M) (j : ℕ),
    Nonempty (LocalGroup R M x j ≃ₗ[R]
      LocalGroup R (Coordinate n) (coordinateOrigin n) j)

/-- Ball classes induce isomorphisms at every interior point. This is the
comparison needed for independence and for locally constant transition units. -/
def ballRestriction : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (B : CoordinateBall A),
    Nonempty (SupportedGroup R M B.closed n ≃ₗ[R] R) ∧
    ∀ (x : M) (hx : x ∈ B.interior),
      Function.Bijective (restrictPoint R (B.interior_subset_closed hx) n)

/-- Exact agreement with the source's locally constant unit formulation, on
every coordinate ball. No orientation is assumed to exist. -/
def orientationIndependence : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : LocalChoice R n M), IsOrientation R A o ↔
      ∀ B : CoordinateBall A, ∃ g : SupportedGroup R M B.closed n,
        IsGenerator R g ∧ ∃ a : B.interior → Rˣ, IsLocallyConstant a ∧
          ∀ x : B.interior, o x.val = (a x).val •
            restrictPoint R (B.interior_subset_closed x.property) n g

/-- The compatibility condition is independent of the chosen topological
atlas, including charts added to an arbitrary covering atlas. -/
def atlasIndependence : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A A' : Manifold n M) (o : LocalChoice R n M),
      IsOrientation R A o ↔ IsOrientation R A' o

/-- In particular every pair of integral signed chart generators has a locally
constant transition sign. The statement is also valid for all coefficient rings. -/
def transitionUnits : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A A' : Manifold n M) (B : CoordinateBall A) (C : CoordinateBall A')
    (g : SupportedGroup R M B.closed n) (h : SupportedGroup R M C.closed n),
    IsGenerator R g → IsGenerator R h →
      ∃ a : ↥(B.interior ∩ C.interior) → Rˣ, IsLocallyConstant a ∧
        ∀ x : ↥(B.interior ∩ C.interior),
          restrictPoint R (B.interior_subset_closed x.property.1) n g =
            (a x).val • restrictPoint R (C.interior_subset_closed x.property.2) n h

/-- Surjective covering with exactly two points in each integral fiber. -/
def orientationCover : Prop :=
  ∀ (n : ℕ) (M : Type v) [TopologicalSpace M] (A : Manifold n M),
    P202Specs.Topology.Covering (fun z : IntegralCover A => z.1) ∧
      ∀ x : M, Nonempty (IntegralFiber A x ≃ Bool)

/-- The signed local generators trivialize the actual homology-generator cover. -/
def signedTrivializations : Prop :=
  ∀ (n : ℕ) (M : Type v) [TopologicalSpace M] (A : Manifold n M)
    (B : CoordinateBall A) (g : SupportedGroup ℤ M B.closed n), IsGenerator ℤ g →
      ∃ e : {z : IntegralCover A // z.1 ∈ B.interior} ≃ₜ (B.interior × Bool),
        (∀ z, (e z).1.val = z.val.1) ∧
        ∀ (x : B.interior) (b : Bool),
          HEq (e.symm (x, b)).val.2.val
            (if b then -(restrictPoint ℤ (B.interior_subset_closed x.property) n g)
            else restrictPoint ℤ (B.interior_subset_closed x.property) n g)

/-- Continuous sections of the projection are precisely integral orientations. -/
def sections : Prop :=
  ∀ (n : ℕ) (M : Type v) [TopologicalSpace M] (A : Manifold n M)
    (s : ∀ x, IntegralFiber A x),
    Continuous (fun x => (⟨x, s x⟩ : IntegralCover A)) ↔
      IsOrientation ℤ A (fun x => (s x).val)

/-- Unique local generator and unique compatible global choice over F_2. -/
def modTwoOrientation : Prop :=
  ∀ (n : ℕ) (M : Type v) [TopologicalSpace M] (A : Manifold n M),
    (∀ x : M, ∃! g : LocalGroup (ZMod 2) M x n, IsGenerator (ZMod 2) g) ∧
      ∃! o : LocalChoice (ZMod 2) n M, IsOrientation (ZMod 2) A o

end Expected
end P202Specs.LocalOrientation
