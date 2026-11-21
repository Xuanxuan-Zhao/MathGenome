import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.FreeProperSlices
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.SmoothDescent
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.RealProjectiveSpace
import Mathlib.Topology.Covering.Basic

/-! The orbit quotient has its coinduced topology. The statements below do not
assume a quotient atlas, local sections, or uniqueness of a smooth structure. -/
namespace SmoothManifolds.FreeProperQuotientData
open ModelData AtlasData MapData MapClassData BoundaryData FreeProperSliceData Set
universe u v

abbrev OrbitSpace (G : Type u) (M : Type v) [Group G] [MulAction G M] :=
  Quotient (MulAction.orbitRel G M)

def orbitProjection {G : Type u} {M : Type v} [Group G] [MulAction G M] :
    M → OrbitSpace G M := Quotient.mk (MulAction.orbitRel G M)

/-- Evenly covered open neighborhoods, with the projection on each open sheet
itself a diffeomorphism. The index set is the actual fiber over the base point. -/
def IsSmoothCovering {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N) : Prop :=
  ∀ y : N, ∃ U : Set N, ∃ hU : IsOpen U, y ∈ U ∧
    ∃ V : (q ⁻¹' {y}) → Set M, ∃ hV : ∀ i, IsOpen (V i),
      Pairwise (fun i j => Disjoint (V i) (V j)) ∧
      q ⁻¹' U = ⋃ i, V i ∧
      ∀ i, ∃ e : Diffeomorph (openSubsetAtlas S.smoothStructure.val (V i) (hV i))
          (openSubsetAtlas T.smoothStructure.val U hU),
        ∀ z : V i, (e.toEquiv z).val = q z.val

/-- Universal property, with arbitrary target dimension and either model. -/
def SmoothMapTest {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N) : Prop :=
  ∀ {k : ℕ} {c : ModelKind} {P : Type v} [TopologicalSpace P]
    (R : SmoothManifold k c P) (h : N → P),
    IsSmoothMap T R h ↔ IsSmoothMap S R (h ∘ q)

/-- Uniqueness is required for every smooth structure making q a smooth
submersion, without requiring a section certificate or boundarylessness of that
competing structure. The comparison is the identity on the quotient set. -/
def UniqueSubmersionStructure {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N) : Prop :=
  (∀ {k : ℕ} {c : ModelKind} (R : SmoothManifold k c N),
    IsSmoothMap S R q → IsSubmersion S R q →
    IsSmoothMap T R id ∧ IsSmoothMap R T id) ∧
  ∀ R : SmoothManifold n b N, IsSmoothMap S R q → IsSubmersion S R q →
    R.smoothStructure = T.smoothStructure

/-- An identity-coordinate chart specifies the standard Euclidean structure. -/
def HasEuclideanIdentityChart (n : ℕ) (E : SmoothManifold n .euclidean (Euclidean n)) : Prop :=
  ∃ c ∈ E.smoothStructure.val, c.source = univ ∧ c.target = univ ∧
    ∀ x : Euclidean n, (c x).val = x

/-- The literal integer translation, including the empty tuple in dimension 0. -/
def integerTranslate (n : ℕ) (z : Fin n → ℤ) (x : Euclidean n) : Euclidean n :=
  fun i => x i + (z i : ℝ)

def integerTransport (n : ℕ) (z : (Fin n → ℤ) × Euclidean n) :
    Euclidean n × Euclidean n := (z.2, integerTranslate n z.1 z.2)

end SmoothManifolds.FreeProperQuotientData

namespace Specs.SmoothManifolds.Ch08.FreeProperQuotient
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.MapClassData _root_.SmoothManifolds.BoundaryData
  _root_.SmoothManifolds.FreeProperSliceData _root_.SmoothManifolds.FreeProperQuotientData
  _root_.SmoothManifolds.SphereTorusData _root_.SmoothManifolds.ProjectiveData Set
universe u v

/-- The topological part, for the genuine orbit space with quotient topology. -/
def quotient_topologyType : Prop :=
  ∀ {G : Type u} {M : Type v} [TopologicalSpace G] [TopologicalSpace M]
    [Group G] [MulAction G M] [T2Space M] [LocallyCompactSpace M]
    [SecondCountableTopology M],
    Continuous (fun z : G × M => z.1 • z.2) →
    IsProper (actionTransport (G := G) (M := M)) →
    IsOpenQuotientMap (orbitProjection (G := G) (M := M)) ∧
    T2Space (OrbitSpace G M) ∧ SecondCountableTopology (OrbitSpace G M)

/-- The topological covering assertion, retaining actual evenly covered
neighborhoods through Mathlib's covering-map definition. -/
def discrete_coveringType : Prop :=
  ∀ {G : Type u} {M : Type v} [TopologicalSpace G] [TopologicalSpace M]
    [Group G] [MulAction G M] [T2Space M] [LocallyCompactSpace M] [DiscreteTopology G],
    Continuous (fun z : G × M => z.1 • z.2) → FreeAction G M →
    IsProper (actionTransport (G := G) (M := M)) →
    IsCoveringMap (orbitProjection (G := G) (M := M))

/-- Quotient charts obtained from a local action product chart, on the actual
quotient topology. This is a support statement for the smooth atlas construction. -/
def local_quotient_chartType : Prop :=
  ∀ {G : Type u} {M : Type v} [TopologicalSpace G] [TopologicalSpace M]
    [Group G] [MulAction G M] [SeparatelyContinuousMul G] [ContinuousConstSMul G M]
    [T2Space M] [LocallyCompactSpace M],
    Continuous (fun z : G × M => z.1 • z.2) → FreeAction G M →
    IsProper (actionTransport (G := G) (M := M)) →
    ∀ (p : M) (W : Set G) (s₁ : Set M), IsOpen W → (1 : G) ∈ W → p ∈ s₁ →
    ∀ h : OpenPartialHomeomorph (G × s₁) M,
      h.source = W ×ˢ univ →
      EqOn h (fun z : G × s₁ => z.1 • z.2.val) h.source →
      ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
        let s := s₁ ∩ U
        p ∈ s ∧ IsOpen (orbitProjection (G := G) '' s) ∧
        (∃ e : s ≃ₜ (orbitProjection (G := G) '' s),
          ∀ x, (e x).val = orbitProjection (G := G) x.val) ∧
        ∀ y ∈ saturation (G := G) s, ∃! x : s, ∃ g : G, g • x.val = y

/-- The full general theorem; none of the asserted conclusions is an input. -/
def free_proper_quotientType : Prop :=
  ∀ {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    [Nonempty M] (A : SmoothManifold d a G) (B : SmoothManifold n b M),
    SmoothLieAction A B → FreeAction G M →
    IsProper (actionTransport (G := G) (M := M)) →
    d ≤ n ∧ IsOpenQuotientMap (orbitProjection (G := G) (M := M)) ∧
    T2Space (OrbitSpace G M) ∧ SecondCountableTopology (OrbitSpace G M) ∧
    ∃ Q : SmoothManifold (n - d) .euclidean (OrbitSpace G M),
      intrinsicBoundary Q = ∅ ∧
      IsSmoothMap B Q orbitProjection ∧ IsSubmersion B Q orbitProjection ∧
      SmoothDescentData.HasSmoothLocalSections B Q orbitProjection ∧
      SmoothMapTest.{u,v} B Q orbitProjection ∧
      UniqueSubmersionStructure B Q orbitProjection ∧
      (DiscreteTopology G → IsSmoothCovering B Q orbitProjection)

/-- The example is stated on the literal translation quotient, with the exact
standard torus and standard product hemisphere atlas. Properness is the source's
compact-inverse-image definition. All n, including n=0, are quantified. -/
def integer_translationType : Prop :=
  ∀ n : ℕ,
    (∀ (z : Fin n → ℤ) (x : Euclidean n), integerTranslate n z x = x → z = 0) ∧
    IsProper (integerTransport n) ∧
    ∃ (E : SmoothManifold n .euclidean (Euclidean n))
      (Q : SmoothManifold n .euclidean (LatticeQuotient n))
      (T : SmoothManifold n .euclidean (Torus n)),
      HasEuclideanIdentityChart n E ∧
      (∀ z : Fin n → ℤ, IsSmoothMap E E (integerTranslate n z)) ∧
      T.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (productHemisphereAtlas n) ∧
      IsSmoothMap E Q (latticeProjection n) ∧ IsSubmersion E Q (latticeProjection n) ∧
      IsSmoothCovering E Q (latticeProjection n) ∧
      UniqueSubmersionStructure E Q (latticeProjection n) ∧
      ∃ e : Diffeomorph Q.smoothStructure.val T.smoothStructure.val,
        ∀ x : Euclidean n, e.toEquiv (latticeProjection n x) = angleMap n x

/-- The two-element group acts by id and antipode. Its freeness is exactly the
absence of antipodal fixed points. Properness is recorded for the disjoint union
of these two action graphs. The smooth quotient atlas must equal the established
projective ratio atlas, with actual smooth local sections of the projection. -/
def antipodal_quotientType : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ x : Sphere n, antipode x ≠ x) ∧
    IsProper (fun z : Bool × Sphere n =>
      (z.2, if z.1 then antipode z.2 else z.2)) ∧
    ∃ (S : SmoothManifold n .euclidean (Sphere n))
      (Q : SmoothManifold n .euclidean (RealProjectiveSpace n)),
      S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas n) ∧
      IsSmoothMap S S antipode ∧
      Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (projectiveAtlas n) ∧
      intrinsicBoundary Q = ∅ ∧
      IsSmoothMap S Q projectiveProjection ∧ IsSubmersion S Q projectiveProjection ∧
      IsSmoothCovering S Q projectiveProjection ∧
      SmoothDescentData.HasSmoothLocalSections S Q projectiveProjection ∧
      UniqueSubmersionStructure S Q projectiveProjection

end Specs.SmoothManifolds.Ch08.FreeProperQuotient
