import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.RegularLevels
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.BoundaryInverse
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.BoundaryCones

/-! Independent specification of M03.06(a) and its necessity example.
The boundary restriction uses the actual intrinsic boundary with its subspace
 topology and the natural face atlas. Zero and empty dimensions are included.
The two tangent statements deliberately have different source tangent spaces. -/
set_option autoImplicit false

namespace SmoothManifolds.BoundaryRegularLevelData
open ModelData AtlasData MapData BoundaryData Set
universe u

/-- Face restrictions of every ambient chart; dimension zero has no face. -/
def HasNaturalFaceCharts {m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m a M)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S)) : Prop := by
  cases m with
  | zero => exact True
  | succ r =>
    exact ∀ c ∈ S.smoothStructure.val,
      Nonempty {p : intrinsicBoundary S // p.val ∈ c.source} →
      ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S c b

/-- The canonical boundary atlas interface, for both global models and all m. -/
def IsNaturalBoundaryStructure {m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m a M)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S)) : Prop :=
  IsSmoothMap B S Subtype.val ∧ HasNaturalFaceCharts S B

/-- The actual function in the necessity example, with real target. -/
def parabolaMap (p : HalfSpace 2) : ℝ := p.val 1 + (p.val 0) ^ 2

def origin : HalfSpace 2 := ⟨0, by change (0 : ℝ) ≤ 0; exact le_rfl⟩

/-- A global standard coordinate chart on the real line. -/
def realChart : ModelChart 1 .euclidean ℝ :=
  ((Homeomorph.funUnique (Fin 1) ℝ).symm.trans
    (Homeomorph.Set.univ (Euclidean 1)).symm).toOpenPartialHomeomorph

end SmoothManifolds.BoundaryRegularLevelData

namespace Specs.SmoothManifolds.Ch03.BoundaryRegularLevels
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.BoundaryRegularLevelData Set
universe u v

/-- Existence discharges the boundary-atlas interface in the later statements;
it is not a new hypothesis on the original manifold. -/
def natural_boundary_existsType : Prop :=
  ∀ {m : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m a M),
    ∃ B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S),
      IsNaturalBoundaryStructure S B

def fiber_closedType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → ∀ y, IsClosed (f ⁻¹' {y})

/-- No global n ≤ m is assumed. A nonempty boundary fiber forces the stronger
bound n ≤ m-1; in particular a zero-dimensional source has no boundary fiber. -/
def regular_fiber_dimensionType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S)),
    IsNaturalBoundaryStructure S B → intrinsicBoundary T = ∅ → IsSmoothMap S T f →
    ∀ y, IsRegularValue S T f y →
      IsRegularValue B T (fun p => f p.val) y →
      ((f ⁻¹' {y}).Nonempty → n ≤ m) ∧
      (m < n → f ⁻¹' {y} = ∅) ∧
      ((f ⁻¹' {y} ∩ intrinsicBoundary S).Nonempty → 0 < m ∧ n ≤ m - 1)

/-- The constructed manifold has the exact fiber as underlying subspace.
The model kind is inherited from M, and the boundary equality is intrinsic. -/
def regular_fiber_structureType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S)),
    IsNaturalBoundaryStructure S B → intrinsicBoundary T = ∅ → IsSmoothMap S T f →
    ∀ y, IsRegularValue S T f y →
      IsRegularValue B T (fun p => f p.val) y →
    ∃ R : SmoothManifold (m - n) a (f ⁻¹' {y}),
      IsSmoothEmbedding R S Subtype.val ∧
      intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S ∧
      ((f ⁻¹' {y}).Nonempty → (m - n) + n = m)

/-- A stronger tangent statement: once the expected-dimensional embedded fiber
has been constructed, regularity of F alone identifies its full tangent image.
It applies at interior and boundary points and retains all normal vectors. -/
def regular_fiber_tangentType : Prop :=
  ∀ {m n : ℕ} {a b c : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → ∀ y, IsRegularValue S T f y →
    ∀ R : SmoothManifold (m - n) c (f ⁻¹' {y}),
    IsSmoothEmbedding R S Subtype.val → ∀ p : f ⁻¹' {y},
    ∀ (L : TangentSpace S p.val →ₗ[ℝ] TangentSpace T (f p.val))
      (K : TangentSpace R p →ₗ[ℝ] TangentSpace S p.val),
      IsDifferential S T f p.val L → IsDifferential R S Subtype.val p K →
      Function.Injective K ∧ LinearMap.range K = LinearMap.ker L

/-- The boundary tangent image is an intersection in the *ambient full* tangent
space. I is the natural boundary inclusion differential, and J is the composite
inclusion from the intrinsic boundary of the fiber. These are not full tangents
of the fiber itself. -/
def boundary_fiber_tangentType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S)),
    IsNaturalBoundaryStructure S B → intrinsicBoundary T = ∅ → IsSmoothMap S T f →
    ∀ y, IsRegularValue S T f y →
      IsRegularValue B T (fun p => f p.val) y →
    ∀ (R : SmoothManifold (m - n) a (f ⁻¹' {y})),
    IsSmoothEmbedding R S Subtype.val →
    ∀ (hboundary : intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S)
      (C : SmoothManifold (m - n - 1) .euclidean (intrinsicBoundary R)),
    IsNaturalBoundaryStructure R C → ∀ p : intrinsicBoundary R,
    let q : intrinsicBoundary S := ⟨p.val.val, (Set.ext_iff.mp hboundary p.val).mp p.property⟩
    ∀ (L : TangentSpace S p.val.val →ₗ[ℝ] TangentSpace T (f p.val.val))
      (I : TangentSpace B q →ₗ[ℝ] TangentSpace S p.val.val)
      (J : TangentSpace C p →ₗ[ℝ] TangentSpace S p.val.val),
    IsDifferential S T f p.val.val L → IsDifferential B S Subtype.val q I →
    IsDifferential C S (fun z => z.val.val) p J →
      Function.Injective J ∧ LinearMap.range J = LinearMap.ker L ⊓ LinearMap.range I

/-- Together with the structure and boundary-equality theorem this includes
codimension zero with its inherited boundary. No regularity assumption is needed
for this topological assertion. -/
def zero_target_clopenType : Prop :=
  ∀ {m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold 0 b N) (f : M → N),
    IsSmoothMap S T f → ∀ y, IsOpen (f ⁻¹' {y}) ∧ IsClosed (f ⁻¹' {y})

/-- The source and target have their standard structures. The fiber is a single
point and admits no one-dimensional half-space chart on any neighborhood of
that point, hence cannot have the expected codimension-one half-slice. -/
def boundary_regularity_counterexampleType : Prop :=
  ∃ (S : SmoothManifold 2 .halfSpace (HalfSpace 2))
    (T : SmoothManifold 1 .euclidean ℝ),
    OpenPartialHomeomorph.refl (HalfSpace 2) ∈ S.smoothStructure.val ∧
    realChart ∈ T.smoothStructure.val ∧
    IsSmoothMap S T parabolaMap ∧
    IsRegularValue S T parabolaMap 0 ∧
    (∃ B : SmoothManifold 1 .euclidean (intrinsicBoundary S),
      IsNaturalBoundaryStructure S B ∧
      ¬ IsRegularValue B T (fun p => parabolaMap p.val) 0) ∧
    parabolaMap ⁻¹' {0} = {origin} ∧
    ∀ p : parabolaMap ⁻¹' {0},
      ¬ ∃ c : ModelChart 1 .halfSpace (parabolaMap ⁻¹' {0}), p ∈ c.source

end Specs.SmoothManifolds.Ch03.BoundaryRegularLevels
