import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.InducedConnections
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.LieBracket
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.RegularLevels

/-! Independent specification for paper.tex 3065–3084.
Torsion uses the actual tangent bundle and intrinsic Lie bracket. Metric
parallelness uses the induced dual/tensor connection, and all map statements
allow arbitrary, possibly nonconstant, differential rank. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P202.TorsionMetricData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.SectionExtensionData P202.ConnectionData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- Transport an original smooth tangent section through the proved canonical
bundle realization, preserving its values in every intrinsic tangent fiber. -/
noncomputable def realizedField (X : SmoothManifolds.VectorFieldData.SmoothField
    (P202.MetricData.tangentStructure S)) : Field S := by
  let R := P202.MetricData.tangentRealization S
  letI := R.space.topology
  letI := (P202.MetricData.tangentStructure S).topology
  exact ⟨X.val, fun p => SmoothManifolds.manifoldContDiffAt_comp
    (P202.MetricData.tangentStructure S).manifold.smoothStructure.property.1.1
    (X.smooth p) (R.smooth_from_original ⟨p, X.val p⟩)⟩

noncomputable def originalBracket := Classical.choose
  (SmoothManifolds.LieBrackets.bracket_exists S (P202.MetricData.tangentStructure S))

/-- Intrinsic bracket characterized by the commutator on smooth functions. -/
noncomputable def bracket (X Y : Field S) : Field S :=
  realizedField (originalBracket (originalField S X) (originalField S Y))

/-- Torsion of an arbitrary smooth tangent connection. -/
noncomputable def torsion (C : Connection (tangentBundle S)) (X Y : Field S) : Field S :=
  C.cov X Y + (-1 : ℝ) • C.cov Y X + (-1 : ℝ) • bracket X Y

/-- A tangent-valued two-tensor in its intrinsic multilinear-map representation.
Smoothness is tested on arbitrary smooth fields. Local frames admit global germ
representatives, so this is the ordinary smooth tensor condition. -/
structure TangentTwoTensor (S : SmoothManifold n a M) where
  val : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace S p
  smooth : ∀ X Y : Field S, SmoothSection (tangentBundle S)
    (fun p => val p (X.val p) (Y.val p))

end P202.TorsionMetricData

namespace P202Specs.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.TorsionMetricData
universe u

def torsionType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n a M} → Connection (tangentBundle S) → Field S → Field S → Field S
noncomputable def torsionValue : torsionType := @torsion

def torsion_formulaType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S))
    (X Y : Field S) (p : M),
    (torsion C X Y).val p =
      (C.cov X Y).val p - (C.cov Y X).val p - (bracket X Y).val p

def torsion_tensorialType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S)),
    (∀ X Y Z : Field S, torsion C (X + Y) Z = torsion C X Z + torsion C Y Z) ∧
    (∀ X Y Z : Field S, torsion C X (Y + Z) = torsion C X Y + torsion C X Z) ∧
    (∀ (f : GlobalSmooth S) (X Y : Field S),
      torsion C (mulSection f X) Y = mulSection f (torsion C X Y)) ∧
    (∀ (f : GlobalSmooth S) (X Y : Field S),
      torsion C X (mulSection f Y) = mulSection f (torsion C X Y))

def torsion_tensor_exists_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S)),
    ∃! T : TangentTwoTensor S, ∀ (X Y : Field S) (p : M),
      T.val p (X.val p) (Y.val p) = (torsion C X Y).val p
/-- The test-field definition gives smooth coefficients in the actual tangent
trivializations, rather than just a bilinear operation on global sections. -/
def tangent_tensor_coordinates_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (T : TangentTwoTensor S)
    (i : SmoothManifolds.BundleOperationsData.TangentIndex S) (j k : Fin n)
    (p : M), p ∈ (tangentBundle S).baseSet i →
    SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q => ((tangentBundle S).trivialization i
        ⟨q, T.val q
          (((tangentBundle S).trivialization i).symm q (Pi.single j 1))
          (((tangentBundle S).trivialization i).symm q (Pi.single k 1))⟩).2) p

end P202Specs.Geometry.TorsionAndMetric

namespace P202.TorsionMetricData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BundleData
  SmoothManifolds.BundleMetricData P202.ConnectionData
universe u v w
section Metric
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- The ordinary metric product rule on arbitrary smooth sections. -/
def MetricCompatible (C : Connection B) (h : SmoothFiberMetric B) : Prop :=
  ∀ (X : Field S) (s t : Section B) (p : M),
    scalarDerivative S (fun q => h.form q (s.val q) (t.val q)) p (X.val p) =
      h.form p ((C.cov X s).val p) (t.val p) +
        h.form p (s.val p) ((C.cov X t).val p)

/-- A covariant two-tensor is equivalently a linear functional on the tensor
product of the two primal fibers; this is the universal property, with no
nondegeneracy or frame assumption. -/
noncomputable def metricFunctional (h : SmoothFiberMetric B) (p : M) :
    Module.Dual ℝ (TensorProduct ℝ (E p) (E p)) :=
  TensorProduct.lift (h.form p)
end Metric
end P202.TorsionMetricData

namespace P202Specs.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
  P202.TorsionMetricData P202.CurveConnectionData
open Set
universe u v w

def metric_tensor_calculusType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E),
  ∀ (h : SmoothFiberMetric B) (C : Connection B)
    (T : TensorBundle B B),
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C C T N →
    ∀ (D : DualBundle T.space.bundle),
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule N D K →
    ∃ H : Section D.space.bundle,
      (∀ p, H.val p = metricFunctional B h p) ∧
      (∀ (X : Field S) (s t : Section B) (p : M),
        (K.cov X H).val p (TensorProduct.tmul ℝ (s.val p) (t.val p)) =
          scalarDerivative S (fun q => h.form q (s.val q) (t.val q)) p (X.val p) -
            h.form p ((C.cov X s).val p) (t.val p) -
            h.form p (s.val p) ((C.cov X t).val p)) ∧
      (MetricCompatible B C h ↔ ∀ X : Field S, K.cov X H = 0)

def metric_curve_productType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E),
  ∀ (h : SmoothFiberMetric B) (C : Connection B)
    (hc : MetricCompatible B C h)
    {c : ℝ → M} {f g : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {DF DG : E (c t)}
    (hF : HasCovariantDerivativeWithinAt C c f J t DF)
    (hG : HasCovariantDerivativeWithinAt C c g J t DG),
    HasDerivWithinAt (fun s => h.form (c s) (f s) (g s))
      (h.form (c t) DF (g t) + h.form (c t) (f t) DG) J t

def metric_curve_product_c1Type : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E),
  ∀ (h : SmoothFiberMetric B) (C : Connection B)
    (hc : MetricCompatible B C h)
    {c : ℝ → M} {f g : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hc1 : P202.CurveData.CoordinateC1On S c J) (hc' : ContinuousOn c J)
    (hf : C1FieldOn (B := B) c f J) (hg : C1FieldOn (B := B) c g J),
    HasDerivWithinAt (fun s => h.form (c s) (f s) (g s))
      (h.form (c t) (covariantDerivativeWithin C c f J t) (g t) +
        h.form (c t) (f t) (covariantDerivativeWithin C c g J t)) J t

end P202Specs.Geometry.TorsionAndMetric
namespace P202Specs.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
  P202.TorsionMetricData
open Set Filter
open scoped Topology
universe u v w

def metric_map_productType : Prop :=
  ∀ {n m r : ℕ} {a b : ModelKind} {M L : Type u}
    [TopologicalSpace M] [TopologicalSpace L]
    {S : SmoothManifold n a M} {R : SmoothManifold m b L}
    {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E),
  ∀ (h : SmoothFiberMetric B) (C : Connection B)
    (hc : MetricCompatible B C h) (F : L → M) (hF : IsSmoothMap R S F)
    (P : PullbackBundle B R F),
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle), P202.PullbackData.IsPullback B C F hF P CP →
    ∀ (X : Field R) (s t : Section P.space.bundle) (q : L),
      scalarDerivative R (fun z => h.form (F z) (s.val z) (t.val z)) q (X.val q) =
        h.form (F q) ((CP.cov X s).val q) (t.val q) +
          h.form (F q) (s.val q) ((CP.cov X t).val q)
end P202Specs.Geometry.TorsionAndMetric

namespace P202Specs.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData P202.ConnectionData P202.InducedConnectionData
  P202.TorsionMetricData
universe u v w

def metricCompatibleType :=
  {n r : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
  [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
  [TopologicalSpace (Bundle.TotalSpace (SmoothManifolds.ModelData.Euclidean r) E)] →
  (B : SmoothVectorBundle S r ι E) → Connection B →
  SmoothManifolds.BundleMetricData.SmoothFiberMetric B → Prop

def metricCompatibleValue : metricCompatibleType := @MetricCompatible

/-- Specialization to the fixed Riemannian metric on the intrinsic tangent
bundle: the displayed metric identity is equivalent to the vanishing of its
actual induced covariant two-tensor derivative. -/
def tangent_metric_calculusType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M}
    (g : P202.MetricData.RiemannianMetric S) (C : Connection (tangentBundle S))
    (T : TensorBundle (tangentBundle S) (tangentBundle S)),
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C C T N →
    ∀ (D : DualBundle T.space.bundle),
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule N D K →
    ∃ G : Section D.space.bundle,
      (∀ p, G.val p = metricFunctional (tangentBundle S) g p) ∧
      (∀ (X Y Z : Field S) (p : M),
        (K.cov X G).val p (TensorProduct.tmul ℝ (Y.val p) (Z.val p)) =
          scalarDerivative S (fun q => P202.MetricData.pairing g q (Y.val q) (Z.val q))
            p (X.val p) -
          P202.MetricData.pairing g p ((C.cov X Y).val p) (Z.val p) -
          P202.MetricData.pairing g p (Y.val p) ((C.cov X Z).val p)) ∧
      ((∀ (X Y Z : Field S) (p : M),
        scalarDerivative S (fun q => P202.MetricData.pairing g q (Y.val q) (Z.val q))
            p (X.val p) =
          P202.MetricData.pairing g p ((C.cov X Y).val p) (Z.val p) +
          P202.MetricData.pairing g p (Y.val p) ((C.cov X Z).val p)) ↔
        ∀ X : Field S, K.cov X G = 0)

end P202Specs.Geometry.TorsionAndMetric

namespace P202.TorsionMetricData
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData P202.ConnectionData
universe u

def TorsionFree {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S)) : Prop :=
  ∀ X Y : Field S, torsion C X Y = 0

end P202.TorsionMetricData

namespace P202Specs.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData P202.ConnectionData P202.TorsionMetricData
universe u

def torsionFreeType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} →
  Connection (tangentBundle S) → Prop

def torsionFreeValue : torsionFreeType := @TorsionFree

def torsion_free_tensorType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S))
    (T : TangentTwoTensor S)
    (hT : ∀ (X Y : Field S) (p : M),
      T.val p (X.val p) (Y.val p) = (torsion C X Y).val p),
    TorsionFree C ↔ ∀ p v w, T.val p v w = 0

end P202Specs.Geometry.TorsionAndMetric

namespace P202.TorsionMetricData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.SectionExtensionData SmoothManifolds.VectorFieldData
  SmoothManifolds.LieBracketData SmoothManifolds.FiniteRegularityData
  P202.ConnectionData P202.TorsionMetricData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}
noncomputable def fullChartConstantField (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hfull : e.source = univ) (v : Euclidean n) : Field S :=
  realizedField (Classical.choose
    (SmoothManifolds.LieBrackets.field_of_full_chart e he hfull (fun _ => v) contDiff_const))
noncomputable def parameterField (j : Fin 2) :
    Field (SmoothManifolds.RegularLevels.standardEuclideanManifold 2) :=
  fullChartConstantField (SmoothManifolds.RegularLevels.standardEuclideanChart 2)
    (SmoothManifolds.RegularLevels.singleChartManifold_chart_mem _ rfl) rfl (Pi.single j 1)
end P202.TorsionMetricData

namespace P202Specs.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData
  P202.ConnectionData P202.TorsionMetricData
open Set
universe u

/-- The two differential directions are actual smooth sections along F. -/
def differential_along_smoothType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {R : SmoothManifold m b N}
    (F : N → M) (hF : IsSmoothMap R S F)
    (P : PullbackBundle (tangentBundle S) R F) (X : Field R),
    letI := P.space.topology
    SmoothSection P.space.bundle
      (fun q => SmoothManifolds.differential R S F hF q (X.val q))

/-- Naturality of torsion for arbitrary smooth maps and arbitrary source fields.
The tensor's defining property refers to the intrinsic bracket and the original
connection; existence and uniqueness of this tensor are proved separately. -/
def differential_naturalityType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {R : SmoothManifold m b N}
    (C : Connection (tangentBundle S)) (τ : TangentTwoTensor S)
    (hτ : ∀ (A B : Field S) (p : M),
      τ.val p (A.val p) (B.val p) = (torsion C A B).val p)
    (F : N → M) (hF : IsSmoothMap R S F)
    (P : PullbackBundle (tangentBundle S) R F),
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle),
    P202.PullbackData.IsPullback (tangentBundle S) C F hF P CP →
    ∀ (X Y : Field R) (V W : Section P.space.bundle),
    (∀ q, V.val q = SmoothManifolds.differential R S F hF q (X.val q)) →
    (∀ q, W.val q = SmoothManifolds.differential R S F hF q (Y.val q)) →
    ∀ q, (CP.cov X W).val q - (CP.cov Y V).val q -
      SmoothManifolds.differential R S F hF q ((bracket X Y).val q) =
      τ.val (F q) (V.val q) (W.val q)

/-- The full-domain chart may have any open coordinate image, so the parameters
can range over arbitrary open subsets. No hypothesis concerns the rank of F. -/
def two_parameter_identityType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {R : SmoothManifold 2 b N}
    (e : ModelChart 2 b N) (he : e ∈ R.smoothStructure.val) (hfull : e.source = univ)
    (C : Connection (tangentBundle S)) (τ : TangentTwoTensor S)
    (hτ : ∀ (A B : Field S) (p : M),
      τ.val p (A.val p) (B.val p) = (torsion C A B).val p)
    (F : N → M) (hF : IsSmoothMap R S F)
    (P : PullbackBundle (tangentBundle S) R F),
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle),
    P202.PullbackData.IsPullback (tangentBundle S) C F hF P CP →
    let ds := fullChartConstantField e he hfull (Pi.single (0 : Fin 2) 1)
    let dt := fullChartConstantField e he hfull (Pi.single (1 : Fin 2) 1)
    ∃ V T : Section P.space.bundle,
      (∀ q, V.val q = SmoothManifolds.differential R S F hF q (ds.val q)) ∧
      (∀ q, T.val q = SmoothManifolds.differential R S F hF q (dt.val q)) ∧
      ∀ q, (CP.cov ds T).val q - (CP.cov dt V).val q =
        τ.val (F q) (V.val q) (T.val q)

/-- The torsion-free case on the same arbitrary parameter domains. -/
def two_parameter_torsion_freeType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {R : SmoothManifold 2 b N}
    (e : ModelChart 2 b N) (he : e ∈ R.smoothStructure.val) (hfull : e.source = univ)
    (C : Connection (tangentBundle S)) (hC : TorsionFree C)
    (F : N → M) (hF : IsSmoothMap R S F)
    (P : PullbackBundle (tangentBundle S) R F),
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle),
    P202.PullbackData.IsPullback (tangentBundle S) C F hF P CP →
    let ds := fullChartConstantField e he hfull (Pi.single (0 : Fin 2) 1)
    let dt := fullChartConstantField e he hfull (Pi.single (1 : Fin 2) 1)
    ∀ (V T : Section P.space.bundle),
      (∀ q, V.val q = SmoothManifolds.differential R S F hF q (ds.val q)) →
      (∀ q, T.val q = SmoothManifolds.differential R S F hF q (dt.val q)) →
      ∀ q, (CP.cov ds T).val q = (CP.cov dt V).val q

end P202Specs.Geometry.TorsionAndMetric
