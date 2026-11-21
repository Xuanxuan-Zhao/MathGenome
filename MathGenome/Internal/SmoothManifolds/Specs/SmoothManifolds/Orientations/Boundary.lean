import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.ProductsAndSigns
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.BoundaryCones

/-! Independent interface for M09.03, paper.tex 1741--1760.

The normal half-lines are subsets of the actual quotient by the inclusion
differential. They are defined from coordinate germs, with chart independence
an obligation below. The wedge is multiplication in the actual exterior algebra.
The two product assertions use M × Int(N) and Int(M) × N as their bulk spaces;
they therefore say nothing about a higher-codimension corner intersection.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical SmoothManifolds.BoundaryConeData

namespace SmoothManifolds.BoundaryOrientationData
open ModelData AtlasData MapData BoundaryData TangentData DifferentialData
  TangentBundleData OrientationData OrientationProductData Set
universe u v

/-- The natural boundary structure, allowing also the empty Euclidean boundary.
For the half-space model this is definitionally `IsBoundaryStructure`. -/
def IsNaturalBoundary {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) : Prop :=
  IsSmoothMap B S Subtype.val ∧
  ∀ c ∈ S.smoothStructure.val,
    Nonempty {p : intrinsicBoundary S // p.val ∈ c.source} →
    ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S c b

/-- Strict inwardness, initially in one chart. The theorem makes this equivalent
to strict positivity in every chart through the boundary point. -/
def IsInward {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M) (p : intrinsicBoundary S)
    (v : TangentSpace S p.val) : Prop :=
  ∃ c ∈ S.smoothStructure.val, ∃ hp : p.val ∈ c.source,
    ∃ E : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1),
      IsChartCoordinates S p.val c E ∧ 0 < E v (Fin.last n)

def IsOutward {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M) (p : intrinsicBoundary S)
    (v : TangentSpace S p.val) : Prop := IsInward S p (-v)

abbrev NormalLine {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M}
    {B : SmoothManifold n .euclidean (intrinsicBoundary S)} {p : intrinsicBoundary S}
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val) :=
  TangentSpace S p.val ⧸ LinearMap.range L

def inwardRay {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M}
    {B : SmoothManifold n .euclidean (intrinsicBoundary S)} {p : intrinsicBoundary S}
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val) : Set (NormalLine L) :=
  Submodule.Quotient.mk '' {v | IsInward S p v}

def outwardRay {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M}
    {B : SmoothManifold n .euclidean (intrinsicBoundary S)} {p : intrinsicBoundary S}
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val) : Set (NormalLine L) :=
  Submodule.Quotient.mk '' {v | IsOutward S p v}

/-- Degree casts only: the underlying exterior algebra element is unchanged. -/
def castExterior {V : Type u} [AddCommGroup V] [Module ℝ V] {i j : ℕ}
    (h : i = j) (x : ⋀[ℝ]^i V) : ⋀[ℝ]^j V := h ▸ x

/-- An ambient vector is inserted FIRST, after transporting the tangential
determinant vector by the actual inclusion differential. -/
def normalWedge {V : Type u} {W : Type v} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {n : ℕ}
    (L : W →ₗ[ℝ] V) (v : V) (η : ⋀[ℝ]^n W) : ⋀[ℝ]^(n+1) V :=
  castExterior (Nat.add_comm 1 n)
    (exteriorPower.wedge ℝ V 1 n (exteriorPower.ιMulti ℝ 1 (fun _ => v))
      (exteriorPower.map n L η))

def IsInducedOrientation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M}
    {B : SmoothManifold n .euclidean (intrinsicBoundary S)}
    (o : Orientation S) (b : Orientation B) : Prop :=
  ∀ p (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
    IsDifferential B S Subtype.val p L →
    ∀ v, IsOutward S p v → ∀ η,
      (IsPositive (b.val p) η ↔ IsPositive (o.val p.val) (normalWedge L v η))

/-- Natural open restriction to the intrinsic interior, in the original model.
No product with a second boundary factor is smoothed over a corner. -/
def IsInteriorStructure {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (R : SmoothManifold n a (manifoldInterior S)) : Prop :=
  ∃ h : IsOpen (manifoldInterior S),
    R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val (manifoldInterior S) h) ∧
    IsSmoothMap R S Subtype.val

def IsRestrictedOrientation {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {R : SmoothManifold n a (manifoldInterior S)}
    (o : Orientation S) (r : Orientation R) : Prop :=
  ∀ p (E : TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val),
    IsDifferential R S Subtype.val p E.toLinearMap →
    Module.Ray.map (determinantMap n E) (r.val p) = o.val p.val

/-- The ordinary smooth product, specified by its smooth universal property
and by actual projection differentials. All factors may be empty. -/
def IsSmoothProduct {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (P : SmoothManifold (m+n) k (M × N)) : Prop :=
  IsSmoothMap P S Prod.fst ∧ IsSmoothMap P T Prod.snd ∧
  (∀ {l : ℕ} {c : ModelKind} {Q : Type u} [TopologicalSpace Q]
    (R : SmoothManifold l c Q) (f : Q → M) (g : Q → N),
    IsSmoothMap R S f → IsSmoothMap R T g →
    IsSmoothMap R P (fun x => (f x, g x))) ∧
  ∀ p, ∃ E, IsProductDifferential S T P p E

/-- The outward-first rule for a codimension-one face inclusion, without
identifying a corner intersection with a manifold boundary. -/
def IsFaceOrientation {d e : ℕ} {a b : ModelKind} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (h : e+1 = d)
    (P : SmoothManifold d a X) (F : SmoothManifold e b Y) (j : Y → X)
    (outward : ∀ p, TangentSpace P (j p) → Prop)
    (o : Orientation P) (r : RayField F) : Prop :=
  ∀ p (L : TangentSpace F p →ₗ[ℝ] TangentSpace P (j p)),
    IsDifferential F P j p L → ∀ v, outward p v → ∀ η,
    (IsPositive (r p) η ↔
      IsPositive (o.val (j p)) (castExterior h (normalWedge L v η)))

/-- Two actual affine half-space charts generating the usual interval structure.
Their sources omit the opposite endpoint, so both are relatively open. -/
def IsStandardInterval (a b : ℝ) (S : SmoothManifold 1 .halfSpace (Icc a b))
    (l r : ModelChart 1 .halfSpace (Icc a b)) : Prop :=
  l ∈ S.smoothStructure.val ∧ r ∈ S.smoothStructure.val ∧
  l.source = {x | x.val < b} ∧ r.source = {x | a < x.val} ∧
  (∀ x ∈ l.source, (l x).val 0 = x.val - a) ∧
  (∀ x ∈ r.source, (r x).val 0 = b - x.val) ∧
  S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) {l, r}

end SmoothManifolds.BoundaryOrientationData

namespace Specs.SmoothManifolds.Orientations.Boundary
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.OrientationData _root_.SmoothManifolds.OrientationProductData
  _root_.SmoothManifolds.BoundaryOrientationData Set
universe u

/-- The strict cones and the two rays in the actual normal quotient, in every
chart. The quantifier on `a` also permits empty boundaries of Euclidean models. -/
def normal_raysType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)),
    IsNaturalBoundary S B → ∀ (p : intrinsicBoundary S)
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
    IsDifferential B S Subtype.val p L →
    ∀ c ∈ S.smoothStructure.val, p.val ∈ c.source →
    ∀ E : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n+1),
    IsChartCoordinates S p.val c E →
    (∀ v, IsInward S p v ↔ 0 < E v (Fin.last n)) ∧
    (∀ v, IsOutward S p v ↔ E v (Fin.last n) < 0) ∧
    ∃ Q : NormalLine L ≃ₗ[ℝ] ℝ,
      (∀ v, Q (Submodule.Quotient.mk v) = E v (Fin.last n)) ∧
      Module.finrank ℝ (NormalLine L) = 1 ∧
      inwardRay L = {q | 0 < Q q} ∧ outwardRay L = {q | Q q < 0}

/-- A change of outward vector is positive rescaling modulo the tangent space;
inserting it changes every boundary determinant vector by that same scalar. -/
def outward_independentType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)),
    IsNaturalBoundary S B → ∀ (p : intrinsicBoundary S)
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
    IsDifferential B S Subtype.val p L →
    ∀ v w, IsOutward S p v → IsOutward S p w →
    ∃ t : ℝ, 0 < t ∧ w - t • v ∈ LinearMap.range L ∧
      ∀ η : DeterminantLine B p, normalWedge L w η = t • normalWedge L v η

/-- The canonical smooth outward-first orientation. Both existence of the natural
boundary and uniqueness on every natural realization are included. Smooth local
positive generators assert smoothness, not merely a pointwise choice of rays. -/
def boundary_orientationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M) (o : Orientation S),
    (∃ B : SmoothManifold n .euclidean (intrinsicBoundary S), IsNaturalBoundary S B) ∧
    ∀ B : SmoothManifold n .euclidean (intrinsicBoundary S),
      IsNaturalBoundary S B → ∃! b : Orientation B,
        IsInducedOrientation o b ∧
        ∃ G : LocalGenerators B, RepresentsGenerators b.val G

/-- Coordinate signs in a restricted face chart: ε_boundary = ε_bulk (-1)^dim M.
All coordinate systems and all signed descriptions of the two rays qualify. -/
def boundary_chart_signType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)),
    IsNaturalBoundary S B → ∀ (o : Orientation S) (q : Orientation B),
    IsInducedOrientation o q → ∀ (s : SignedCharts S) (t : SignedCharts B),
    RepresentsSignedCharts o.val s → RepresentsSignedCharts q.val t →
    ∀ (c : ModelChart (n+1) a M) (hc : c ∈ S.smoothStructure.val)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) (hb : b ∈ B.smoothStructure.val),
    IsFaceRestriction S c b → ∀ (p : intrinsicBoundary S) (hp : p ∈ b.source)
    (hpc : p.val ∈ c.source),
    signValue (t.sign b hb ⟨p, hp⟩) =
      signValue (s.sign c hc ⟨p.val, hpc⟩) * (-1 : ℝ)^(n+1)

/-- Restricting to the intrinsic interior supplies the actual oriented factors
used by the face formulas, without assuming a chosen orientation certificate. -/
def interior_orientationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o : Orientation S),
    ∃ R : SmoothManifold n a (manifoldInterior S),
      IsInteriorStructure S R ∧ intrinsicBoundary R = ∅ ∧
      (∀ p, ∃ E : TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val,
        IsDifferential R S Subtype.val p E.toLinearMap) ∧
      ∃! r : Orientation R, IsRestrictedOrientation o r

/-- The usual positively oriented [a,b], including its actual smooth structure,
boundary set, and zero-dimensional determinant-ray signs at BOTH endpoints. -/
def interval_signType : Prop :=
  ∀ a b : ℝ, a < b →
    ∃ S : SmoothManifold 1 .halfSpace (Icc a b),
    ∃ l r : ModelChart 1 .halfSpace (Icc a b),
      IsStandardInterval a b S l r ∧
      intrinsicBoundary S = {x | x.val = a ∨ x.val = b} ∧
      ∃ (o : Orientation S) (s : SignedCharts S),
        RepresentsSignedCharts o.val s ∧
        (∀ (hl : l ∈ S.smoothStructure.val) p, s.sign l hl p = true) ∧
        (∀ (hr : r ∈ S.smoothStructure.val) p, s.sign r hr p = false) ∧
        ∃ (B : SmoothManifold 0 .euclidean (intrinsicBoundary S)) (q : Orientation B),
          IsNaturalBoundary S B ∧ IsInducedOrientation o q ∧
          ∀ p : intrinsicBoundary S,
            (IsPositive (q.val p)
              ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1) ↔ p.val.val = b) ∧
            (IsPositive (q.val p)
              (-((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1)) ↔ p.val.val = a)

/-- The first face ∂M × Int(N) has the product orientation. The ambient ordinary
product is M × Int(N), so this includes the same face in a product with corners. -/
def product_left_faceType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold (m+1) a M) (T : SmoothManifold n b N)
    (B : SmoothManifold m .euclidean (intrinsicBoundary S)),
    IsNaturalBoundary S B → ∀ (o : Orientation S) (q : Orientation T) (s : Orientation B),
    IsInducedOrientation o s →
    ∀ (R : SmoothManifold n b (manifoldInterior T)) (r : Orientation R),
    IsInteriorStructure T R → IsRestrictedOrientation q r →
    ∃ k, ∃ P : SmoothManifold ((m+1)+n) k (M × manifoldInterior T),
    ∃ j, ∃ F : SmoothManifold (m+n) j (intrinsicBoundary S × manifoldInterior T),
      IsSmoothProduct S R P ∧ IsSmoothProduct B R F ∧
      IsSmoothMap F P (fun p => (p.1.val, p.2)) ∧
      ∃ (oP : Orientation P) (oF : Orientation F),
        IsProductOrientation o r oP ∧ IsProductOrientation s r oF ∧
        IsFaceOrientation (Nat.add_right_comm m n 1) P F (fun p => (p.1.val, p.2))
          (fun p v => ∃ E, IsProductDifferential S R P (p.1.val, p.2) E ∧
            IsOutward S p.1 (E v).1) oP oF.val

/-- The second face Int(M) × ∂N has (-1)^dim M times its product orientation.
The twist is an actual smooth orientation; it reverses the ray in odd dimension. -/
def product_right_faceType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold (n+1) b N)
    (B : SmoothManifold n .euclidean (intrinsicBoundary T)),
    IsNaturalBoundary T B → ∀ (o : Orientation S) (q : Orientation T) (s : Orientation B),
    IsInducedOrientation q s →
    ∀ (R : SmoothManifold m a (manifoldInterior S)) (r : Orientation R),
    IsInteriorStructure S R → IsRestrictedOrientation o r →
    ∃ k, ∃ P : SmoothManifold (m+(n+1)) k (manifoldInterior S × N),
    ∃ j, ∃ F : SmoothManifold (m+n) j (manifoldInterior S × intrinsicBoundary T),
      IsSmoothProduct R T P ∧ IsSmoothProduct R B F ∧
      IsSmoothMap F P (fun p => (p.1, p.2.val)) ∧
      ∃ (oP : Orientation P) (oF tF : Orientation F),
        IsProductOrientation r q oP ∧ IsProductOrientation r s oF ∧
        (∀ p, tF.val p = if Even m then oF.val p else -oF.val p) ∧
        IsFaceOrientation (Nat.add_assoc m n 1) P F (fun p => (p.1, p.2.val))
          (fun p v => ∃ E, IsProductDifferential R T P (p.1, p.2.val) E ∧
            IsOutward T p.2 (E v).2) oP tF.val

end Specs.SmoothManifolds.Orientations.Boundary
