import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.TransversePreimage
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.Sard
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Products

/-! M04.07 and the translation example, paper.tex:1254–1261.
The fixed-endpoint homotopy example at the end of line 1261 is allocated to
Ch04.TransverseHomotopy. No compactness or closedness is assumed here.

A boundaryless parameter manifold is represented in Euclidean models using
an identity diffeomorphism E with its original structure A. This representation
always exists by Foundations.Products.exists_boundaryless_euclidean_smoothManifold.
The two product structures below are the actual maximal product atlases.
The boundary family uses P × ∂M, not the full tangent of P × M at its boundary.
-/
set_option autoImplicit false

namespace SmoothManifolds.ParametricTransversalityData
open ModelData AtlasData MapData BoundaryData MapClassData ProductData
  BoundaryRegularLevelData TransversePreimageData Set
universe u

/-- Coordinates for the standard smooth structure on real coordinate space. -/
def euclideanChart (n : ℕ) : ModelChart n .euclidean (Euclidean n) :=
  (Homeomorph.Set.univ (Euclidean n)).symm.toOpenPartialHomeomorph

/-- The same real coordinates, in any universe used by an abstract source. -/
def liftedEuclideanChart (n : ℕ) :
    ModelChart n .euclidean (ULift.{u} (Euclidean n)) :=
  (Homeomorph.ulift.trans (Homeomorph.Set.univ (Euclidean n)).symm).toOpenPartialHomeomorph

/-- Both the full and boundary restrictions of a slice are transverse. -/
def GoodParameter {r m n k : ℕ} {a b c d : ModelKind} {P M N : Type u}
    [TopologicalSpace P] [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m b M) (T : SmoothManifold n c N)
    {s : Set N} (R : SmoothManifold k d s)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (_A : SmoothManifold r a P) (F : P × M → N) (p : P) : Prop :=
  IsTransverse S T R (fun x => F (p, x)) ∧
  IsTransverse B T R (fun x => F (p, x.val))

end SmoothManifolds.ParametricTransversalityData

namespace Specs.SmoothManifolds.Ch04.ParametricTransversality
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.ProductData _root_.SmoothManifolds.BoundaryRegularLevelData
  _root_.SmoothManifolds.TransversePreimageData _root_.SmoothManifolds.SardData
  _root_.SmoothManifolds.ParametricTransversalityData Set
universe u

/-- The exceptional set is chart-null in the original parameter structure.
In dimension zero it is empty, using the stipulated counting-measure convention.
The choices of E, B and product atlases specify canonical structures and do not
impose new geometric hypotheses on the original manifolds. -/
def parametric_transversalityType : Prop :=
  ∀ {r m n k : ℕ} {a b c d q : ModelKind} {P M N : Type u}
    [TopologicalSpace P] [TopologicalSpace M] [TopologicalSpace N]
    (A : SmoothManifold r a P) (E : SmoothManifold r .euclidean P)
    (S : SmoothManifold m b M) (T : SmoothManifold n c N)
    (s : Set N) (R : SmoothManifold k d s)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (C : ProductCoordinates r .euclidean m b q)
    (Q : SmoothManifold (r + m) q (P × M))
    (CB : ProductCoordinates r .euclidean (m - 1) .euclidean .euclidean)
    (QB : SmoothManifold (r + (m - 1)) .euclidean (P × intrinsicBoundary S))
    (F : P × M → N),
    intrinsicBoundary A = ∅ →
    IsSmoothMap A E id → IsSmoothMap E A id →
    IsNaturalBoundaryStructure S B →
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C E.smoothStructure.val S.smoothStructure.val) →
    QB.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas CB E.smoothStructure.val B.smoothStructure.val) →
    intrinsicBoundary T = ∅ → intrinsicBoundary R = ∅ →
    IsSmoothEmbedding R T Subtype.val → IsSmoothMap Q T F →
    IsTransverse Q T R F →
    IsTransverse QB T R (fun z => F (z.1, z.2.val)) →
    ∃ bad : Set P, IsNull A bad ∧ (r = 0 → bad = ∅) ∧
      ∀ p, p ∉ bad → GoodParameter S T R B A F p

/-- The Euclidean perturbations have no size lower bound, are smooth, and are
homotopic to f through the explicit straight homotopy on all of R × M.
No assumption of transversality is made on f itself. The target is the standard
real coordinate space realized through the canonical homeomorphism ULift.down;
this trivial lift keeps arbitrary source universes available to the frozen
same-universe differential interface. Translation and homotopy use the actual
real coordinates, not an additional operation on an abstract target. -/
def translation_perturbationType : Prop :=
  ∀ {m n k : ℕ} {a c : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m a M) (T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (s : Set (ULift.{u} (Euclidean n))) (R : SmoothManifold k c s)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (f : M → ULift.{u} (Euclidean n)),
    liftedEuclideanChart n ∈ T.smoothStructure.val → intrinsicBoundary R = ∅ →
    IsSmoothEmbedding R T Subtype.val → IsNaturalBoundaryStructure S B →
    IsSmoothMap S T f → ∀ ε : ℝ, 0 < ε →
    ∃ v : Euclidean n, ‖v‖ < ε ∧
      IsSmoothMap S T (fun x => ULift.up.{u} ((f x).down + v)) ∧
      IsTransverse S T R (fun x => ULift.up.{u} ((f x).down + v)) ∧
      IsTransverse B T R (fun x => ULift.up.{u} ((f x.val).down + v)) ∧
      Continuous (fun z : ℝ × M => ULift.up.{u} ((f z.2).down + z.1 • v)) ∧
      (∀ x, ULift.up.{u} ((f x).down + (0 : ℝ) • v) = f x) ∧
      (∀ x, ULift.up.{u} ((f x).down + (1 : ℝ) • v) = ULift.up.{u} ((f x).down + v))

end Specs.SmoothManifolds.Ch04.ParametricTransversality
