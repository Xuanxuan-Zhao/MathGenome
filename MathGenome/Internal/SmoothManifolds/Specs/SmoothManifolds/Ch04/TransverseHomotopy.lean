import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.ParametricTransversality
import Mathlib.Topology.UnitInterval

/-! The fixed-endpoint example at paper.tex:1261. The interval and product
structures are specified by actual coordinate charts. Their choices impose no
compactness condition on M. The target uses the same harmless universe lift as
the frozen translation-perturbation interface. -/
set_option autoImplicit false

namespace SmoothManifolds.TransverseHomotopyData
open ModelData AtlasData MapData BoundaryData MapClassData ProductData
  BoundaryRegularLevelData TransversePreimageData Set
universe u

/-- The chart t ↦ t, omitting the right endpoint. The clamped inverse is only
relevant on the chart target, where it is exactly the identity coordinate. -/
noncomputable def intervalLeftChart : ModelChart 1 .halfSpace unitInterval where
  toFun t := ⟨fun _ => t.val, t.property.1⟩
  invFun y := ⟨min (y.val 0) 1, le_min y.property zero_le_one, min_le_right _ _⟩
  source := {t | t.val < 1}
  target := {y | y.val 0 < 1}
  map_source' _ ht := ht
  map_target' y hy := by
    change y.val 0 < 1 at hy
    change min (y.val 0) 1 < 1
    simpa only [min_eq_left hy.le] using hy
  left_inv' t _ := Subtype.ext (min_eq_left t.property.2)
  right_inv' y hy := by
    apply Subtype.ext
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact min_eq_left hy.le
  open_source := isOpen_lt continuous_subtype_val continuous_const
  open_target := isOpen_lt ((continuous_apply 0).comp continuous_subtype_val) continuous_const
  continuousOn_toFun := (Continuous.subtype_mk (continuous_pi fun _ =>
    continuous_subtype_val) _).continuousOn
  continuousOn_invFun := (Continuous.subtype_mk
    (((continuous_apply 0).comp continuous_subtype_val).min continuous_const) _).continuousOn

/-- The chart t ↦ 1-t, omitting the left endpoint. -/
noncomputable def intervalRightChart : ModelChart 1 .halfSpace unitInterval :=
  unitInterval.symmHomeomorph.toOpenPartialHomeomorph.trans intervalLeftChart

/-- The standard two-chart interval atlas, with its actual subspace topology. -/
noncomputable def intervalAtlas : Set (ModelChart 1 .halfSpace unitInterval) :=
  {intervalLeftChart, intervalRightChart}

/-- Multiplying a perturbation by this polynomial fixes both endpoints. -/
def endpointWeight (t : ℝ) : ℝ := t * (1 - t)

/-- The prescribed, finite-dimensional perturbation; no reparametrization of H. -/
def perturbation {n : ℕ} {M : Type u}
    (H : unitInterval × M → ULift.{u} (Euclidean n)) (a : Euclidean n) :
    unitInterval × M → ULift.{u} (Euclidean n) :=
  fun z => ULift.up ((H z).down + endpointWeight z.1.val • a)

/-- The two endpoint inverse images, as subsets of the cylinder. -/
def endpointFibers {n : ℕ} {M : Type u}
    (H : unitInterval × M → ULift.{u} (Euclidean n))
    (s : Set (ULift.{u} (Euclidean n))) : Set (unitInterval × M) :=
  ({0} ×ˢ {p | H (0, p) ∈ s}) ∪ ({1} ×ˢ {p | H (1, p) ∈ s})

/-- All inverse-image conclusions, including the full tangent at boundary
points. The natural-number dimension equality is restricted to nonempty fibers. -/
def PreimageConclusion {m n k : ℕ} {c : ModelKind} {M : Type u}
    [TopologicalSpace M]
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    {s : Set (ULift.{u} (Euclidean n))} (R : SmoothManifold k c s)
    (H : unitInterval × M → ULift.{u} (Euclidean n)) (a : Euclidean n) : Prop :=
  ((perturbation H a ⁻¹' s).Nonempty → n - k ≤ 1 + m) ∧
  (1 + m < n - k → perturbation H a ⁻¹' s = ∅) ∧
  ((perturbation H a ⁻¹' s ∩ intrinsicBoundary Q).Nonempty → n - k ≤ m) ∧
  ∃ P : SmoothManifold (1 + m - (n - k)) .halfSpace (perturbation H a ⁻¹' s),
    IsSmoothEmbedding P Q Subtype.val ∧
    intrinsicBoundary P = Subtype.val ⁻¹' endpointFibers H s ∧
    ((perturbation H a ⁻¹' s).Nonempty → (1 + m - (n - k)) + (n - k) = 1 + m) ∧
    ∀ p : perturbation H a ⁻¹' s,
      ∀ (L : TangentData.TangentSpace Q p.val →ₗ[ℝ]
          TangentData.TangentSpace T (perturbation H a p.val))
        (I : TangentData.TangentSpace R ⟨perturbation H a p.val, p.property⟩ →ₗ[ℝ]
          TangentData.TangentSpace T (perturbation H a p.val))
        (J : TangentData.TangentSpace P p →ₗ[ℝ] TangentData.TangentSpace Q p.val),
        DifferentialData.IsDifferential Q T (perturbation H a) p.val L →
        DifferentialData.IsDifferential R T Subtype.val
          ⟨perturbation H a p.val, p.property⟩ I →
        DifferentialData.IsDifferential P Q Subtype.val p J →
        Function.Injective J ∧ LinearMap.range J = (LinearMap.range I).comap L

end SmoothManifolds.TransverseHomotopyData

namespace Specs.SmoothManifolds.Ch04.TransverseHomotopy
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.ProductData _root_.SmoothManifolds.BoundaryRegularLevelData
  _root_.SmoothManifolds.TransversePreimageData
  _root_.SmoothManifolds.ParametricTransversalityData
  _root_.SmoothManifolds.TransverseHomotopyData Set
universe u

/-- I, E, Q, and B name the standard interval, a boundaryless Euclidean
representation of M, the product structure, and its natural boundary structure.
Existence of these canonical choices is a construction, not an additional
geometric hypothesis. The endpoint maps are preserved as functions. -/
def transverse_homotopyType : Prop :=
  ∀ {m n k : ℕ} {b c : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m b M) (E : SmoothManifold m .euclidean M)
    (I : SmoothManifold 1 .halfSpace unitInterval)
    (C : ProductCoordinates 1 .halfSpace m .euclidean .halfSpace)
    (Q : SmoothManifold (1 + m) .halfSpace (unitInterval × M))
    (B : SmoothManifold ((1 + m) - 1) .euclidean (intrinsicBoundary Q))
    (T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (s : Set (ULift.{u} (Euclidean n))) (R : SmoothManifold k c s)
    (H : unitInterval × M → ULift.{u} (Euclidean n)),
    intrinsicBoundary S = ∅ → IsSmoothMap S E id → IsSmoothMap E S id →
    I.smoothStructure.val = maximalExtension (⊤ : ℕ∞) intervalAtlas →
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C I.smoothStructure.val E.smoothStructure.val) →
    IsNaturalBoundaryStructure Q B →
    liftedEuclideanChart n ∈ T.smoothStructure.val → intrinsicBoundary R = ∅ →
    IsSmoothEmbedding R T Subtype.val → IsSmoothMap Q T H →
    IsTransverse S T R (fun p => H (0, p)) →
    IsTransverse S T R (fun p => H (1, p)) →
    ∀ ε : ℝ, 0 < ε → ∃ a : Euclidean n,
      ‖a‖ < ε ∧ IsSmoothMap Q T (perturbation H a) ∧
      IsTransverse Q T R (perturbation H a) ∧
      IsTransverse B T R (fun p => perturbation H a p.val) ∧
      (∀ p, perturbation H a (0, p) = H (0, p)) ∧
      (∀ p, perturbation H a (1, p) = H (1, p)) ∧
      PreimageConclusion Q T R H a

end Specs.SmoothManifolds.Ch04.TransverseHomotopy
