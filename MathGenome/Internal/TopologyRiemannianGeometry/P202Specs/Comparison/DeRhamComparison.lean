import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Comparison.SmoothSingularComparison
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.IntegrationCochain

/-! Independent statement of the vector space part of `thm:p202-de-rham`,
paper.tex 2713–2819. The ring assertion is allocated to DeRhamRing.
The actual P104 intrinsic forms and the shared P202 ordinary real cohomology
are used. No support condition, finite cover, connectedness, nonemptiness,
or restriction on either of the two manifold model kinds is imposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory HomologicalComplex Opposite
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.TangentData SmoothManifolds.CovectorData
open SmoothManifolds.BundleOperationsData SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
namespace P202Specs.DeRhamComparison
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)

/-- The basis of the literal smooth submodule of the ordinary singular chains. -/
abbrev SmoothSimplex (q : ℕ) :=
  {σ : SingularChains.Simplex (TopCat.of M) q //
    SmoothSingularComparison.IsSmoothSimplex S q σ}

/-- The ordered affine homeomorphism already proved in the upstream Specs
identifies this simplex with the actual P104 integration domain. -/
def p104Simplex {q : ℕ} (σ : SmoothSimplex S q) :
    SmoothSingularData.SingularSimplex S q :=
  ⟨SingularChains.simplexEquiv (TopCat.of M) q σ.val ∘
    SmoothSingularComparison.toBarycentric q, σ.property⟩

/-- A smooth simplex as a literal element of the shared chain submodule. -/
def smoothGenerator {q : ℕ} (σ : SmoothSimplex S q) :
    SmoothSingularComparison.smoothModule S q :=
  ⟨Finsupp.single σ.val 1, Finsupp.single_mem_supported ℝ 1 σ.property⟩

/-- Undo extension by zero in a nonnegative degree. -/
def smoothDegreeIso (q : ℕ) :
    (SmoothSingularComparison.smoothOrdinaryComplex S).X (q : ℤ) ≅
      ModuleCat.of ℝ (SmoothSingularComparison.smoothModule S q) :=
  (SmoothSingularComparison.smoothComplex S).extendXIso
    (SingularChains.degreeEmbedding 0) (by change (0 : ℤ) + q = q; omega)

/-- Evaluate an actual categorical smooth cochain on the shared simplex basis. -/
def evaluateSmoothCochain {q : ℕ}
    (c : (SmoothSingularComparison.smoothCochains S).X (q : ℤ))
    (σ : SmoothSimplex S q) : ℝ :=
  (show (SmoothSingularComparison.smoothOrdinaryComplex S).X (q : ℤ) →ₗ[ℝ] ℝ from c)
    ((smoothDegreeIso S q).inv (smoothGenerator S σ))

/-- The precise integration-induced class: after the actual ordinary-to-smooth
restriction on cohomology, a cocycle representative evaluates to the literal
P104 simplex pullback integral on EVERY smooth simplex. This equation fixes
the comparison, and in particular does not allow an arbitrary vector space
isomorphism between the cohomology groups. -/
def IsIntegrationClass (C : CotangentBundle S) {q : ℕ} (ω : Field S q)
    (x : CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ)) : Prop :=
  ∃ c : (SmoothSingularComparison.smoothCochains S).cycles (q : ℤ),
    (SmoothSingularComparison.smoothCochains S).homologyπ (q : ℤ) c =
      homologyMap (SmoothSingularComparison.restriction S) (q : ℤ) x ∧
    ∀ σ : SmoothSimplex S q,
      evaluateSmoothCochain S
        ((SmoothSingularComparison.smoothCochains S).iCycles (q : ℤ) c) σ =
        IntegrationCochainData.simplexIntegral S C ω (p104Simplex S σ)

/-- Degreewise real linear equivalences to the ORIGINAL ordinary cohomology. -/
abbrev ComparisonFamily {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) :=
  (q : ℕ) → K.Cohomology q ≃ₗ[ℝ]
    CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ)

/-- Characterization on all closed intrinsic representatives. The restriction
map must itself be an isomorphism, so this is precisely integration followed
by its inverse, including degree zero. -/
def IsIntegrationComparison {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (e : ComparisonFamily S K) : Prop :=
  (∀ q : ℕ, IsIso (homologyMap (SmoothSingularComparison.restriction S) (q : ℤ))) ∧
  ∀ q (ω : K.closed q), IsIntegrationClass S C ω.val.val (e q (K.classOf q ω))

/-- Existence for arbitrary finite-dimensional Hausdorff second-countable
P104 manifolds, including their smooth boundary model. The bundle/calculus
realizations are the existing intrinsic P104 objects, not added comparison
certificates; their construction is proved in P104. -/
def comparisonIsomorphism_type : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (K : Calculus C B),
    ∃ e : ComparisonFamily S K, IsIntegrationComparison S K e

/-- Naturality under every smooth map, for the ordinary singular pullback and
the actual intrinsic de Rham pullback. It holds for every integration-induced
family, so it is independent of choices of cocycle representatives. -/
def comparisonNaturality_type : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (e : ComparisonFamily S K) (h : ComparisonFamily T J),
    IsIntegrationComparison S K e → IsIntegrationComparison T J h →
    ∀ (f : M → N) (hf : MapData.IsSmoothMap S T f)
      (L : (p : M) → TangentData.TangentSpace S p →ₗ[ℝ] TangentData.TangentSpace T (f p)),
      (∀ p, DifferentialData.IsDifferential S T f p (L p)) →
    ∀ P : ∀ q, J.Cohomology q →ₗ[ℝ] K.Cohomology q,
      IsCohomologyPullback C B K J f L P →
    ∀ q (x : J.Cohomology q),
      e q (P q x) =
        (CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map
          (SmoothSingularComparison.underlyingMap S T f hf).op (h q x)

/-- The original unconditional target. Conditional upstream assumptions belong
only on the implementation's separately named helper. -/
def deRhamComparison_type : Prop :=
  comparisonIsomorphism_type.{u} ∧ comparisonNaturality_type.{u}

end P202Specs.DeRhamComparison
