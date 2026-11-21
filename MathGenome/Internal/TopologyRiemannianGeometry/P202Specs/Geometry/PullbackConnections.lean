import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConnectionForms

/-! Independent interfaces for the arbitrary-smooth-map pullback construction
in paper.tex, Proposition 6.2, lines 3034--3035 and 3045--3049. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace P202.PullbackData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData P202.ConnectionData
universe u v w

section Pullbacks
variable {n m r : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]

/-- Choice from P104's proved construction, retaining the prescribed fibers,
pulled-back charts, topology and canonical smooth map. -/
noncomputable def bundle (B : SmoothVectorBundle S r ι E)
    (T : SmoothManifold m b N) (F : N → M) (hF : IsSmoothMap T S F) :
    PullbackBundle B T F :=
  Classical.choice (SmoothManifolds.BundleOperations.exists_pullback B T F hF)

variable (B : SmoothVectorBundle S r ι E) (C : Connection B)
  (F : N → M) (hF : IsSmoothMap T S F) (P : PullbackBundle B T F)

/-- Property of one connection, rather than a certificate carried by the input. -/
def IsPullback : letI := P.space.topology; Connection P.space.bundle → Prop :=
  letI := P.space.topology
  fun D => ∀ (X : Field T) (s : Section B) (t : Section P.space.bundle),
    (∀ q, t.val q = s.val (F q)) → ∀ q,
    (D.cov X t).val q = pointDerivative C s.val (F q)
      (SmoothManifolds.differential T S F hF q (X.val q))

/-- Local section form of the same universal property. -/
def LocalRule : letI := P.space.topology; Connection P.space.bundle → Prop :=
  letI := P.space.topology
  fun D => ∀ (U : Set M) (hU : IsOpen U)
    (hV : IsOpen (F ⁻¹' U))
    (s : LocalSection B U hU)
    (t : LocalSection P.space.bundle (F ⁻¹' U) hV)
    (X : LocalSection (tangentBundle T) (F ⁻¹' U) hV),
    (∀ q, t.val q = s.val ⟨F q.val, q.property⟩) →
    ∀ q : F ⁻¹' U,
      covOn D (F ⁻¹' U) hV X t q =
        pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) (F q.val)
          (SmoothManifolds.differential T S F hF q.val (X.val q))

/-- One-form matrix in every actual pulled-back local frame. -/
def FrameRule : letI := P.space.topology; Connection P.space.bundle → Prop :=
  letI := P.space.topology
  fun D => ∀ (U : Set M) (hU : IsOpen U) (hV : IsOpen (F ⁻¹' U))
    (e : LocalFrame B U hU) (c : LocalFrame P.space.bundle (F ⁻¹' U) hV),
    (∀ j q, c.section_ j q = e.section_ j ⟨F q.val, q.property⟩) →
    ∀ (q : F ⁻¹' U) (v : TangentSpace T q.val) (i j : Fin r),
      connectionForm D c q i j v =
        connectionForm C e ⟨F q.val, q.property⟩ i j
          (SmoothManifolds.differential T S F hF q.val v)

/-- Local Leibniz recipe in a pulled-back frame, with ordinary intrinsic
scalar differentials of its coefficient functions on N. -/
noncomputable def localFormula (U : Set M) (hU : IsOpen U)
    (hV : IsOpen (F ⁻¹' U)) (e : LocalFrame B U hU) :
    letI := P.space.topology
    (c : LocalFrame P.space.bundle (F ⁻¹' U) hV) →
    LocalSection P.space.bundle (F ⁻¹' U) hV →
    (q : F ⁻¹' U) → TangentSpace T q.val → E (F q.val) := by
  letI := P.space.topology
  intro c s q v
  exact (c.basis q).equivFun.symm (fun i =>
    scalarDerivative T (SmoothManifolds.FrameData.totalize (fun z : F ⁻¹' U =>
      SmoothManifolds.FrameData.coefficients c s.val z i)) q.val v +
    ∑ j, connectionForm C e ⟨F q.val, q.property⟩ i j
        (SmoothManifolds.differential T S F hF q.val v) *
      SmoothManifolds.FrameData.coefficients c s.val q j)

end Pullbacks
end P202.PullbackData

namespace P202Specs.Geometry.PullbackConnections
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData P202.ConnectionData P202.PullbackData
universe u v w

section Statements
variable {n m r : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]

/-- Full existence and uniqueness, including the local section and matrix rules.
There is no condition on the rank of dF, on the rank r, or on either ModelKind. -/
def exists_uniqueType : Prop :=
  ∀ {n m r : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (C : Connection B)
    (F : N → M) (hF : IsSmoothMap T S F) (P : PullbackBundle B T F),
    letI := P.space.topology
    ∃ D : Connection P.space.bundle,
      IsPullback B C F hF P D ∧ LocalRule B C F hF P D ∧ FrameRule B C F hF P D ∧
      ∀ D' : Connection P.space.bundle, IsPullback B C F hF P D' → D' = D

/-- Uniqueness uses only the original connection axioms and the differentiation
rule on global pulled-back sections. -/
def uniquenessType : Prop :=
  ∀ {n m r : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (C : Connection B)
    (F : N → M) (hF : IsSmoothMap T S F) (P : PullbackBundle B T F),
    letI := P.space.topology
    ∀ D D' : Connection P.space.bundle,
      IsPullback B C F hF P D → IsPullback B C F hF P D' → D = D'

/-- Pulled-back changes of frame obey the actual differential chain rule and
the gauge law, in the same fiber coordinates as the constructed connection. -/
def frame_changeType : Prop :=
  ∀ {n m r : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (C : Connection B)
    (F : N → M) (hF : IsSmoothMap T S F) (P : PullbackBundle B T F)
    (U : Set M) (hU : IsOpen U) (hV : IsOpen (F ⁻¹' U)) (e e' : LocalFrame B U hU),
    letI := P.space.topology
    ∀ (c c' : LocalFrame P.space.bundle (F ⁻¹' U) hV),
    (∀ j q, c.section_ j q = e.section_ j ⟨F q.val, q.property⟩) →
    (∀ j q, c'.section_ j q = e'.section_ j ⟨F q.val, q.property⟩) →
    ∀ (q : F ⁻¹' U) (v : TangentSpace T q.val),
      localTransition c c' q = localTransition e e' ⟨F q.val, q.property⟩ ∧
      localTransitionDerivative c c' q v =
        localTransitionDerivative e e' ⟨F q.val, q.property⟩
          (SmoothManifolds.differential T S F hF q.val v) ∧
      connectionMatrix C e' ⟨F q.val, q.property⟩
          (SmoothManifolds.differential T S F hF q.val v) =
        localTransition c' c q * connectionMatrix C e ⟨F q.val, q.property⟩
            (SmoothManifolds.differential T S F hF q.val v) * localTransition c c' q +
          localTransition c' c q * localTransitionDerivative c c' q v

/-- The local recipes glue as elements of the actual common fiber, for every
smooth local section, tangent vector and pair of pulled-back frames. -/
def local_formulas_agreeType : Prop :=
  ∀ {n m r : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (C : Connection B)
    (F : N → M) (hF : IsSmoothMap T S F) (P : PullbackBundle B T F)
    (U : Set M) (hU : IsOpen U) (hV : IsOpen (F ⁻¹' U)) (e e' : LocalFrame B U hU),
    letI := P.space.topology
    ∀ (c c' : LocalFrame P.space.bundle (F ⁻¹' U) hV),
    (∀ j q, c.section_ j q = e.section_ j ⟨F q.val, q.property⟩) →
    (∀ j q, c'.section_ j q = e'.section_ j ⟨F q.val, q.property⟩) →
    ∀ (s : LocalSection P.space.bundle (F ⁻¹' U) hV)
      (q : F ⁻¹' U) (v : TangentSpace T q.val),
      localFormula B C F hF P U hU hV e c s q v =
        localFormula B C F hF P U hU hV e' c' s q v

/-- The theorem also exposes the construction with no pullback realization
supplied by the caller: the bundle is the actual P104 construction above. -/
def canonical_exists_uniqueType : Prop :=
  ∀ {n m r : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (C : Connection B)
    (F : N → M) (hF : IsSmoothMap T S F),
    let P := bundle B T F hF
    letI := P.space.topology
    ∃ D : Connection P.space.bundle,
      IsPullback B C F hF P D ∧ LocalRule B C F hF P D ∧ FrameRule B C F hF P D ∧
      ∀ D' : Connection P.space.bundle, IsPullback B C F hF P D' → D' = D

/-- Every target local frame has an actual smooth pullback frame. -/
def frame_existsType : Prop :=
  ∀ {n m r : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ (B : SmoothVectorBundle S r ι E) (F : N → M) (hF : IsSmoothMap T S F)
    (P : PullbackBundle B T F) (U : Set M) (hU : IsOpen U) (e : LocalFrame B U hU),
    letI := P.space.topology
    ∃ c : LocalFrame P.space.bundle (F ⁻¹' U)
      (hU.preimage (continuous_iff_continuousAt.mpr (fun q => (hF q).1))),
      ∀ j q, c.section_ j q = e.section_ j ⟨F q.val, q.property⟩

end Statements

/-- A canonical pullback bundle is chosen from the proved P104 construction. -/
def bundleType := {n m r : ℕ} → {a b : ModelKind} → {M N : Type u} →
  [TopologicalSpace M] → [TopologicalSpace N] → {S : SmoothManifold n a M} →
  {ι : Type v} → {E : M → Type w} → [∀ p, AddCommGroup (E p)] →
  [∀ p, Module ℝ (E p)] → [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)] →
  (B : SmoothVectorBundle S r ι E) → (T : SmoothManifold m b N) →
  (F : N → M) → IsSmoothMap T S F → PullbackBundle B T F

noncomputable def bundleValue : bundleType := @P202.PullbackData.bundle

end P202Specs.Geometry.PullbackConnections
