import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.MaximalFlow
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses

/-! M06.05, the boundaryless flow-box and hypersurface-flowout clauses.
The Euclidean models represent arbitrary boundaryless manifolds, as in the
upstream maximal-flow interface. Products are tested in the actual coordinates
(time, hypersurface coordinates), with no choice of an auxiliary product atlas.
The two coordinate tests below are the ordinary smoothness tests in those
charts, including continuity. In particular the inverse in a flowout is smooth
as a map to R × H, not merely separately smooth in the two variables.
-/
namespace SmoothManifolds.FlowoutData
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  VectorFieldData MaximalFlowData Set Filter
open scoped Topology ContDiff
universe u

/-- Smoothness of a map from time times a manifold, in all product charts. -/
def ProductSmoothAt {k n : ℕ} {H M : Type u}
    [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold n .euclidean M)
    (f : ℝ × H → M) (z : ℝ × H) : Prop :=
  ContinuousAt f z ∧ ∀ e ∈ T.smoothStructure.val, ∀ d ∈ S.smoothStructure.val,
    z.2 ∈ e.source → f z ∈ d.source →
    ∃ U : Set (ℝ × Euclidean k), IsOpen U ∧ (z.1, (e z.2).val) ∈ U ∧
      ∃ G : ℝ × Euclidean k → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
        (fun w : ℝ × H => G (w.1, (e w.2).val)) =ᶠ[𝓝 z]
          (fun w => (d (f w)).val)

/-- Smoothness of the inverse map into time times a manifold. -/
def SmoothToProductAt {k n : ℕ} {H M : Type u}
    [TopologicalSpace H] [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (T : SmoothManifold k .euclidean H)
    (g : M → ℝ × H) (p : M) : Prop :=
  ContinuousAt g p ∧ ∀ d ∈ S.smoothStructure.val, ∀ e ∈ T.smoothStructure.val,
    p ∈ d.source → (g p).2 ∈ e.source →
    ∃ U : Set (Euclidean n), IsOpen U ∧ (d p).val ∈ U ∧
      ∃ G : Euclidean n → ℝ × Euclidean k, ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
        (fun q => G (d q).val) =ᶠ[𝓝 p]
          (fun q => ((g q).1, (e (g q).2).val))

/-- The time coordinate vector is carried to X. This is the intrinsic integral
curve equation in every target chart, at every point of the parameter domain. -/
def CarriesTimeField {n : ℕ} {H M : Type u}
    [TopologicalSpace H] [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    (X : SmoothField B) (h : OpenPartialHomeomorph (ℝ × H) M) : Prop :=
  ∀ z ∈ h.source, ∀ (d : ModelChart n .euclidean M)
    (hd : d ∈ S.smoothStructure.val) (hp : h z ∈ d.source),
    HasDerivAt (fun t => (d (h (t, z.2))).val)
      (B.fiberCoordinates.equiv d hd (h z) hp (X.val (h z))) z.1

/-- Transversality to an embedded hypersurface uses the full intrinsic tangent
map. Its existence is a theorem upstream, rather than an assumed certificate
for a conclusion of the present theorem. -/
def IsTransverse {k : ℕ} {H M : Type u}
    [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold (k+1) .euclidean M)
    {B : TangentBundleStructure S} (X : SmoothField B) (i : H → M) : Prop :=
  ∀ q, ∃ L : TangentSpace T q →ₗ[ℝ] TangentSpace S (i q),
    IsDifferential T S i q L ∧ X.val (i q) ∉ LinearMap.range L

/-- A genuine diffeomorphism on open neighborhoods of the entire zero-time
section and its image. Neither neighborhood is required to be a product, and
no closedness or compactness of the embedded hypersurface is assumed. -/
def IsFlowout {k : ℕ} {H M : Type u}
    [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold (k+1) .euclidean M)
    {B : TangentBundleStructure S} (X : SmoothField B) (i : H → M)
    (F : CurveFamily M) (h : OpenPartialHomeomorph (ℝ × H) M) : Prop :=
  (∀ q, (0,q) ∈ h.source) ∧
  h.source ⊆ (fun z : ℝ × H => (z.1, i z.2)) ⁻¹' flowDomain F ∧
  EqOn h (fun z => F.curve (i z.2) z.1) h.source ∧
  (∀ q, h (0,q) = i q) ∧ Set.range i ⊆ h.target ∧
  (∀ z ∈ h.source, ProductSmoothAt T S h z) ∧
  (∀ p ∈ h.target, SmoothToProductAt S T h.symm p) ∧
  CarriesTimeField X h

/-- The full neighborhood statement uses maps on the open subspaces themselves.
This also represents an empty hypersurface in a nonempty ambient manifold:
there is no requirement for a total inverse from M into an empty parameter space.
The coordinate extension tests are joint in (time, hypersurface coordinates).
The final equation is the derivative of the restricted flow along the time line;
its domain is open, so this is exactly the pushforward of the time vector. -/
def IsFlowoutOn {k : ℕ} {H M : Type u}
    [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold (k+1) .euclidean M)
    {B : TangentBundleStructure S} (X : SmoothField B) (i : H → M)
    (F : CurveFamily M) (V : Set (ℝ × H)) (W : Set M) (h : V ≃ₜ W) : Prop :=
  (∀ q, (0,q) ∈ V) ∧
  V ⊆ (fun z : ℝ × H => (z.1, i z.2)) ⁻¹' flowDomain F ∧
  (∀ z : V, (h z).val = F.curve (i z.val.2) z.val.1) ∧
  Set.range i ⊆ W ∧
  (∀ z : V, ∀ e ∈ T.smoothStructure.val, ∀ d ∈ S.smoothStructure.val,
    z.val.2 ∈ e.source → (h z).val ∈ d.source →
    ∃ U : Set (ℝ × Euclidean k), IsOpen U ∧ (z.val.1,(e z.val.2).val) ∈ U ∧
      ∃ G : ℝ × Euclidean k → Euclidean (k+1), ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
        (fun w : V => G (w.val.1,(e w.val.2).val)) =ᶠ[𝓝 z]
          (fun w : V => (d (h w).val).val)) ∧
  (∀ p : W, ∀ d ∈ S.smoothStructure.val, ∀ e ∈ T.smoothStructure.val,
    p.val ∈ d.source → (h.symm p).val.2 ∈ e.source →
    ∃ U : Set (Euclidean (k+1)), IsOpen U ∧ (d p.val).val ∈ U ∧
      ∃ G : Euclidean (k+1) → ℝ × Euclidean k, ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
        (fun q : W => G (d q.val).val) =ᶠ[𝓝 p]
          (fun q : W => ((h.symm q).val.1,(e (h.symm q).val.2).val))) ∧
  ∀ z ∈ V, ∀ (d : ModelChart (k+1) .euclidean M)
    (hd : d ∈ S.smoothStructure.val) (hp : F.curve (i z.2) z.1 ∈ d.source),
    HasDerivAt (fun t => (d (F.curve (i z.2) t)).val)
      (B.fiberCoordinates.equiv d hd (F.curve (i z.2) z.1) hp
        (X.val (F.curve (i z.2) z.1))) z.1

/-- A coordinate chart with one time coordinate and n-1 transverse coordinates.
Both directions are jointly C-infinity in the original maximal smooth atlas.
The last condition says d(chart)(X)=(1,0), by testing the canonical integral
curve through each point at time zero. This also fixes which coordinate is first.
The nonzero-field hypothesis in the theorem forces n>0; n=1 uses a point as
transverse coordinate space. -/
def IsFlowBox {n k : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (F : CurveFamily M) (p : M)
    (h : OpenPartialHomeomorph M (ℝ × Euclidean k)) : Prop :=
  p ∈ h.source ∧ h p = (0,0) ∧
  (∀ q ∈ h.source, ContinuousAt h q ∧
    ∀ d ∈ S.smoothStructure.val, q ∈ d.source →
      ∃ U : Set (Euclidean n), IsOpen U ∧ (d q).val ∈ U ∧
        ∃ G : Euclidean n → ℝ × Euclidean k, ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
          (fun y => G (d y).val) =ᶠ[𝓝 q] h) ∧
  (∀ z ∈ h.target, ContinuousAt h.symm z ∧
    ∀ d ∈ S.smoothStructure.val, h.symm z ∈ d.source →
      ∃ U : Set (ℝ × Euclidean k), IsOpen U ∧ z ∈ U ∧
        ∃ G : ℝ × Euclidean k → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
          G =ᶠ[𝓝 z] (fun w => (d (h.symm w)).val)) ∧
  ∀ q ∈ h.source, HasDerivAt (fun t => h (F.curve q t)) (1,0) 0

end SmoothManifolds.FlowoutData

namespace Specs.SmoothManifolds.Ch06.Flowout
open _root_.SmoothManifolds _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapClassData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.VectorFieldData _root_.SmoothManifolds.MaximalFlowData
  _root_.SmoothManifolds.FlowoutData
universe u

def flow_boxType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M), IsMaximalFamily X F →
    ∀ p : M, X.val p ≠ 0 → 0 < n ∧
      ∃ h : OpenPartialHomeomorph M (ℝ × ModelData.Euclidean (n-1)),
        IsFlowBox S F p h

def hypersurface_flowoutType : Prop :=
  ∀ {k : ℕ} {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    (T : SmoothManifold k .euclidean H) (S : SmoothManifold (k+1) .euclidean M)
    (B : TangentBundleStructure S) (X : SmoothField B) (F : CurveFamily M),
    IsMaximalFamily X F → ∀ i : H → M, IsSmoothEmbedding T S i →
      IsTransverse T S X i →
      ∃ (V : Set (ℝ × H)) (W : Set M), IsOpen V ∧ IsOpen W ∧
        ∃ h : V ≃ₜ W, IsFlowoutOn T S X i F V W h

end Specs.SmoothManifolds.Ch06.Flowout
