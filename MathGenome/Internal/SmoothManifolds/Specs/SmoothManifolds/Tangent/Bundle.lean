import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Differential
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The total space uses the already specified intrinsic derivation fibers.
`TangentBundleStructure` is construction data, whose existence is a theorem
obligation below, not an additional hypothesis on the base manifold.  Smoothness
continues to mean local ambient extension, also at the face. -/
namespace SmoothManifolds.TangentBundleData
open ModelData AtlasData MapData TangentData DifferentialData ProductData BoundaryData
open Set Filter
open scoped Topology
universe u v

abbrev TotalSpace {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) := (p : M) × TangentSpace S p

def projection {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : TotalSpace S → M := Sigma.fst

def zeroSection {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) : TotalSpace S := ⟨p, 0⟩

/-- A family of intrinsic fiber differentials induces this map on total spaces.
The theorems require `IsDifferential`, and upstream existence supplies the family.
Keeping the family explicit lets independent Specs avoid importing its proof. -/
def totalMap {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) :
    TotalSpace S → TotalSpace T := fun z => ⟨f z.1, L z.1 z.2⟩

/-- All base charts have their actual intrinsic coordinate linear equivalences.
No coordinates are required outside a chart's source. -/
structure FiberCoordinates {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) where
  equiv : ∀ (e : ModelChart n a M), e ∈ S.smoothStructure.val →
    ∀ p ∈ e.source, TangentSpace S p ≃ₗ[ℝ] Euclidean n
  isCoordinates : ∀ e he p hp, IsChartCoordinates S p e (equiv e he p hp)

/-- A canonical tangent atlas, using a linear rearrangement which carries the
base's boundary coordinate to the final coordinate in dimension `n+n`.
In dimension zero both permitted models are points. The maximal-atlas equality
ensures canonicity independently of the chosen generating atlas. -/
structure TangentBundleStructure {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) where
  topology : TopologicalSpace (TotalSpace S)
  productCoordinates : ProductCoordinates n a n .euclidean a
  fiberCoordinates : FiberCoordinates S
  manifold : @SmoothManifold (n + n) a (TotalSpace S) topology
  chart : ∀ e : ModelChart n a M, e ∈ S.smoothStructure.val →
    @ModelChart (n + n) a (TotalSpace S) topology
  chart_source : ∀ e he, (chart e he).source = projection S ⁻¹' e.source
  chart_target : ∀ e he,
    (chart e he).target = productCoordinates.homeomorph '' (e.target ×ˢ univ)
  chart_apply : ∀ e he (z : TotalSpace S) (hz : z.1 ∈ e.source),
    ((chart e he) z).val = productCoordinates.linearEquiv
      ((e z.1).val, fiberCoordinates.equiv e he z.1 hz z.2)
  maximalAtlas : manifold.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
    {t | ∃ e he, t = chart e he}

/-- The atlas with its topology made explicit, for comparison of realizations. -/
def TangentBundleStructure.smoothAtlas {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S) :
    Set (@ModelChart (n+n) a (TotalSpace S) B.topology) :=
  letI := B.topology
  B.manifold.smoothStructure.val

/-- Smoothness of a scalar parameter on a test manifold. -/
def SmoothScalar {k : ℕ} {c : ModelKind} {Q : Type v} [TopologicalSpace Q]
    (R : SmoothManifold k c Q) (s : Q → ℝ) : Prop :=
  ∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val
    (fun y => fun _ : Fin 1 => s y) x

end SmoothManifolds.TangentBundleData

namespace Specs.SmoothManifolds.Tangent.Bundle
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.ProductData _root_.SmoothManifolds.BoundaryData
  _root_.SmoothManifolds.TangentBundleData
open Set Filter
open scoped Topology
universe u v

def TotalSpaceType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n a M → Type u
def TotalSpaceValue : TotalSpaceType := @TangentBundleData.TotalSpace

def projectionType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n a M) → TotalSpace S → M
def projectionValue : projectionType := @TangentBundleData.projection

def zeroSectionType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n a M) → M → TotalSpace S
def zeroSectionValue : zeroSectionType := @TangentBundleData.zeroSection

def totalMapType := {n m : ℕ} → {a b : ModelKind} → {M N : Type u} →
  [TopologicalSpace M] → [TopologicalSpace N] →
  (S : SmoothManifold n a M) → (T : SmoothManifold m b N) → (f : M → N) →
  (∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) → TotalSpace S → TotalSpace T
def totalMapValue : totalMapType := @TangentBundleData.totalMap

def FiberCoordinatesType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n a M → Type u
def FiberCoordinatesValue : FiberCoordinatesType := @TangentBundleData.FiberCoordinates

def TangentBundleStructureType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n a M → Type u
def TangentBundleStructureValue : TangentBundleStructureType :=
  @TangentBundleData.TangentBundleStructure

def SmoothScalarType := {k : ℕ} → {c : ModelKind} → {Q : Type v} →
  [TopologicalSpace Q] → SmoothManifold k c Q → (Q → ℝ) → Prop
def SmoothScalarValue : SmoothScalarType := @TangentBundleData.SmoothScalar

def fiberCoordinates_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M), Nonempty (FiberCoordinates S)

/-- Includes the specified tangent charts, the maximal smooth atlas, Hausdorffness
and second countability in the original smooth-manifold definition. -/
def tangentBundle_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M), Nonempty (TangentBundleStructure S)

/-- The identity is a diffeomorphism for any two realizations, even if their
linear rearrangements of the product coordinates differ. In particular the
topology and smoothness do not depend on choices. -/
def tangentBundle_canonicalType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B D : TangentBundleStructure S),
    ∃ h : @Diffeomorph (n+n) (n+n) a a (TotalSpace S) (TotalSpace S)
      B.topology D.topology B.smoothAtlas D.smoothAtlas,
      @ContDiffDiffeomorph.toEquiv (n+n) (n+n) a a (TotalSpace S) (TotalSpace S)
        B.topology D.topology (⊤ : ℕ∞) B.smoothAtlas D.smoothAtlas h =
          Equiv.refl (TotalSpace S)

def tangentBundle_projection_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S),
    letI := B.topology
    IsSmoothMap B.manifold S (projection S)

/-- A genuine product homeomorphism over each base chart, with the prescribed
fiberwise linear equivalence. Its smoothness in coordinates is also required by
`tangentBundle_lift_smooth_iffType` below. -/
def tangentBundle_locallyTrivialType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val),
    letI := B.topology
    ∃ h : (projection S ⁻¹' e.source) ≃ₜ (e.source × Euclidean n),
      ∀ z, (h z).1.val = z.val.1 ∧
        (h z).2 = B.fiberCoordinates.equiv e he z.val.1 z.property z.val.2

/-- Smooth maps into the bundle are exactly smooth base maps with smooth local
fiber coordinates. This is the full local-trivialization smoothness test, with
the same ambient extensions as the original manifold calculus. -/
def tangentBundle_lift_smooth_iffType : Prop :=
  ∀ {n k : ℕ} {a c : ModelKind} {M : Type u} {Q : Type v}
    [TopologicalSpace M] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (R : SmoothManifold k c Q) (f : Q → TotalSpace S),
    letI := B.topology
    IsSmoothMap R B.manifold f ↔
      IsSmoothMap R S (fun x => (f x).1) ∧
      ∀ x (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
        (hx : (f x).1 ∈ e.source),
        ∃ V : Set Q, IsOpen V ∧ x ∈ V ∧
          ∃ hV : ∀ y ∈ V, (f y).1 ∈ e.source,
            ∃ w : Q → Euclidean n,
              (∀ y (hy : y ∈ V), w y =
                B.fiberCoordinates.equiv e he (f y).1 (hV y hy) (f y).2) ∧
              ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) R.smoothStructure.val w x

/-- Transitions are actual linear isomorphisms and admit smooth, operator-valued
ambient extensions in base coordinates on every overlap, including its face.
Their inverses are the transitions with the charts reversed. -/
def tangentBundle_transition_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (e d : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source),
    ∃ U : Set (Euclidean n), IsOpen U ∧ (e p).val ∈ U ∧
      ∃ A : Euclidean n → (Euclidean n →L[ℝ] Euclidean n),
        ContDiffOn ℝ (⊤ : ℕ∞) A U ∧
        ∀ q (hq : q ∈ e.source) (hqd : q ∈ d.source), (e q).val ∈ U →
          ∀ v, A (e q).val v =
            K.equiv d hd q hqd ((K.equiv e he q hq).symm v)

/-- The displayed transition is exactly the derivative of every local ambient
representative of the base transition; this fixes the Jacobian convention. -/
def tangentBundle_transition_jacobianType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (e d : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source)
    (U : Set (Euclidean n)) (F : Euclidean n → Euclidean n),
    IsOpen U → (e p).val ∈ U → ContDiffOn ℝ (⊤ : ℕ∞) F U →
    (fun q => F (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val) →
    ∀ v, K.equiv d hd p hpd v = fderiv ℝ F (e p).val (K.equiv e he p hp v)

def tangentBundle_zero_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S),
    letI := B.topology
    IsSmoothMap S B.manifold (zeroSection S)

/-- Joint smoothness of addition and scalar multiplication expressed on every
smooth test manifold. The local coordinate formulas below explicitly identify
these operations with the standard smooth maps on their fiber-product domains.
The base map need not be constant and the test manifold may have boundary. -/
def tangentBundle_operations_smoothType : Prop :=
  ∀ {n k : ℕ} {a c : ModelKind} {M : Type u} {Q : Type v}
    [TopologicalSpace M] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (R : SmoothManifold k c Q) (p : Q → M)
    (v w : ∀ x, TangentSpace S (p x)) (s : Q → ℝ),
    letI := B.topology
    (IsSmoothMap R B.manifold (fun x => ⟨p x, v x⟩) →
      IsSmoothMap R B.manifold (fun x => ⟨p x, w x⟩) →
      IsSmoothMap R B.manifold (fun x => ⟨p x, v x + w x⟩)) ∧
    (IsSmoothMap R B.manifold (fun x => ⟨p x, v x⟩) → SmoothScalar R s →
      IsSmoothMap R B.manifold (fun x => ⟨p x, s x • v x⟩))

def tangentBundle_operations_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S),
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Euclidean n × (Euclidean n × Euclidean n) =>
      (z.1, z.2.1 + z.2.2)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (Euclidean n × Euclidean n) =>
      (z.2.1, z.1 • z.2.2)) ∧
    ∀ e he p hp (v w : TangentSpace S p) (s : ℝ),
      K.equiv e he p hp (v + w) = K.equiv e he p hp v + K.equiv e he p hp w ∧
      K.equiv e he p hp (s • v) = s • K.equiv e he p hp v

def tangentBundle_totalMap_smoothType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (B : TangentBundleStructure S) (D : TangentBundleStructure T)
    (f : M → N), IsSmoothMap S T f →
    letI := B.topology
    letI := D.topology
    ∀ L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p),
      (∀ p, IsDifferential S T f p (L p)) →
        IsSmoothMap B.manifold D.manifold (totalMap S T f L)

def tangentBundle_totalMap_coversType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    projection T ∘ totalMap S T f L = f ∘ projection S

def tangentBundle_totalMap_idType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace S p),
    (∀ p, IsDifferential S S id p (L p)) → totalMap S S id L = id

def tangentBundle_totalMap_compType : Prop :=
  ∀ {n m k : ℕ} {a b c : ModelKind} {M N Q : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (R : SmoothManifold k c Q) (f : M → N) (g : N → Q),
    IsSmoothMap S T f → IsSmoothMap T R g →
    ∀ (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
      (K : ∀ q, TangentSpace T q →ₗ[ℝ] TangentSpace R (g q))
      (H : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace R (g (f p))),
      (∀ p, IsDifferential S T f p (L p)) →
      (∀ q, IsDifferential T R g q (K q)) →
      (∀ p, IsDifferential S R (g ∘ f) p (H p)) →
      totalMap S R (g ∘ f) H = totalMap T R g K ∘ totalMap S T f L

def tangentBundle_boundaryType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S),
    letI := B.topology
    intrinsicBoundary B.manifold = projection S ⁻¹' intrinsicBoundary S

def tangentBundle_zeroDimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (B : TangentBundleStructure S),
    letI := B.topology
    DiscreteTopology (TotalSpace S) ∧
      ∃ h : TotalSpace S ≃ₜ M, (h : TotalSpace S → M) = projection S

def tangentBundle_emptyType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [IsEmpty M]
    (S : SmoothManifold n a M), IsEmpty (TotalSpace S)

end Specs.SmoothManifolds.Tangent.Bundle
