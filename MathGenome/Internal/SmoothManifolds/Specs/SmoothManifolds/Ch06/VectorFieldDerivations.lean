import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Bundle
import Mathlib.RingTheory.Derivation.Basic

/-! M06.01 and its pushforward paragraph. All fibers are the intrinsic germ
fibers of Chapter 2, and smoothness uses the given tangent-bundle atlas.
No tangency-to-boundary condition is imposed on a field. -/
namespace SmoothManifolds.VectorFieldData
open ModelData AtlasData MapData PartitionData TangentData DifferentialData
  TangentBundleData Set Filter
open scoped Topology
universe u

abbrev Section {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) := (p : M) → TangentSpace S p

/-- Actual smooth sections of the already specified tangent bundle. -/
structure SmoothField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) where
  val : Section S
  smooth : letI := B.topology
    IsSmoothMap S B.manifold (fun p => ⟨p, val p⟩)

/-- Real-linear Leibniz derivations, with no continuity or locality premise. -/
abbrev RealDerivation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) := Derivation ℝ (GlobalSmooth S) (GlobalSmooth S)

/-- Intrinsic meaning of Df(p)=df_p(X_p): a tangent vector acts on the germ of f.
This tests every representative and does not assume a smoothness certificate. -/
def Represents {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {B : TangentBundleStructure S}
    (X : SmoothField B) (D : RealDerivation S) : Prop :=
  ∀ (p : M) (f : GlobalSmooth S) (g : SmoothGerm S p),
    Germ.ofFun f.val = g.val → (D f).val p = (X.val p).val g

/-- The function identity includes existence of the smooth composite; this
avoids any vacuous quantification over representatives of a composition. -/
def FunctionsRelated {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (f : M → N) (D : RealDerivation S) (E : RealDerivation T) : Prop :=
  ∀ u : GlobalSmooth T, ∃ v : GlobalSmooth S,
    v.val = u.val ∘ f ∧ (D v).val = (E u).val ∘ f

/-- A smooth map with smooth inverse branches on open neighborhoods. -/
def IsLocalDiffeomorphism {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N) : Prop :=
  IsSmoothMap S T f ∧ ∀ p : M,
    ∃ (U : Set M) (V : Set N) (hU : IsOpen U) (hV : IsOpen V),
      p ∈ U ∧ f p ∈ V ∧
      ∃ h : Diffeomorph (openSubsetAtlas S.smoothStructure.val U hU)
          (openSubsetAtlas T.smoothStructure.val V hV),
        ∀ x : U, (h.toEquiv x).val = f x.val
end SmoothManifolds.VectorFieldData

namespace Specs.SmoothManifolds.Ch06.VectorFieldDerivations
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.PartitionData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.VectorFieldData
open Set Filter
open scoped Topology
universe u

/-- Full bijection, including empty and zero-dimensional bases and all boundary
points, characterized by its action on every globally smooth function. -/
def correspondenceType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S),
    ∃ e : SmoothField B ≃ RealDerivation S, ∀ X, Represents X (e X)

/-- Germ locality is derived from the algebraic Leibniz rule. -/
def localityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (D : RealDerivation S) (p : M)
    (f g : GlobalSmooth S), f.val =ᶠ[𝓝 p] g.val → (D f).val p = (D g).val p

/-- Local action is well-defined by any global extension obtained from cutoffs.
No global smoothness of the locally defined function r is required. -/
def local_actionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (D : RealDerivation S) (p : M) (r : M → ℝ),
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val r p →
    ∃! t : ℝ, ∀ f : GlobalSmooth S, f.val =ᶠ[𝓝 p] r → (D f).val p = t

/-- On a smaller chart all coordinates have global smooth extensions, and the
field's actual coefficients equal D applied to those extensions. In particular
these coefficients are smooth; the statement uses any intrinsic coordinates. -/
def chart_coefficientsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B) (D : RealDerivation S), Represents X D →
    ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
      (p : M) (hp : p ∈ e.source),
      ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ hUs : U ⊆ e.source,
        ∃ g : Fin n → GlobalSmooth S,
          (∀ i, EqOn (g i).val (fun y => (e y).val i) U) ∧
          ∀ (q : M) (hq : q ∈ U) (i : Fin n),
            B.fiberCoordinates.equiv e he q (hUs hq) (X.val q) i =
              (D (g i)).val q

/-- Related vectors are detected by all globally smooth target functions. -/
def related_iffType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (B : TangentBundleStructure S) (C : TangentBundleStructure T)
    (f : M → N), IsSmoothMap S T f →
    ∀ (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
      (∀ p, IsDifferential S T f p (L p)) →
    ∀ (X : SmoothField B) (Y : SmoothField C)
      (D : RealDerivation S) (E : RealDerivation T),
      Represents X D → Represents Y E →
      ((∀ p, L p (X.val p) = Y.val (f p)) ↔ FunctionsRelated f D E)

/-- The sigma equality states exactly (f_*X)(q)=df_(f⁻¹q)(X(f⁻¹q)),
including the equality of base points in its dependent tangent fibers. -/
def pushforwardType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (B : TangentBundleStructure S) (C : TangentBundleStructure T)
    (h : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (h.toEquiv p)),
    (∀ p, IsDifferential S T h.toEquiv p (L p)) → ∀ X : SmoothField B,
      ∃! Y : SmoothField C, ∀ q : N,
        (⟨q, Y.val q⟩ : TotalSpace T) =
          totalMap S T h.toEquiv L ⟨h.toEquiv.symm q, X.val (h.toEquiv.symm q)⟩

/-- Each local inverse branch has its own smooth pushforward on an open target
neighborhood. No global projectability is asserted for a local diffeomorphism. -/
def local_pushforwardType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (B : TangentBundleStructure S) (C : TangentBundleStructure T)
    (f : M → N), IsLocalDiffeomorphism S T f →
    ∀ (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
      (∀ p, IsDifferential S T f p (L p)) → ∀ (X : SmoothField B) (p : M),
      ∃ (U : Set M) (V : Set N) (hU : IsOpen U) (hV : IsOpen V),
        p ∈ U ∧ f p ∈ V ∧
        ∃ h : Diffeomorph (openSubsetAtlas S.smoothStructure.val U hU)
            (openSubsetAtlas T.smoothStructure.val V hV),
          (∀ x : U, (h.toEquiv x).val = f x.val) ∧
          ∃ Y : (q : V) → TangentSpace T q.val,
            (letI := C.topology
             ManifoldSmooth (openSubsetAtlas T.smoothStructure.val V hV)
               C.manifold.smoothStructure.val (fun q : V => ⟨q.val, Y q⟩)) ∧
            ∀ q : V, (⟨q.val, Y q⟩ : TotalSpace T) =
              totalMap S T f L ⟨(h.toEquiv.symm q).val, X.val (h.toEquiv.symm q).val⟩

end Specs.SmoothManifolds.Ch06.VectorFieldDerivations
