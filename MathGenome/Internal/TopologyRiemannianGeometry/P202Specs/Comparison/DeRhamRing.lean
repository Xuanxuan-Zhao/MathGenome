import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Comparison.DeRhamComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.CupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleChains

/-! Independent full ring conclusion of paper.tex, thm:p202-de-rham,
2713–2721 and 2821–2850. All manifold models and all nonnegative degrees
are retained. No compactness or finite dimensionality of cohomology is assumed.
The explicit product integral uses pullbacks to the common simplex, so also
makes sense when both factors have boundary and their product has corners. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open scoped Classical
open CategoryTheory HomologicalComplex Opposite
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.TangentData SmoothManifolds.CovectorData
open SmoothManifolds.BundleOperationsData SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open scoped DirectSum TensorProduct
namespace P202Specs.DeRhamRing
universe u
open P202Specs.DeRhamComparison
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)

/-- A real graded algebra on the actual de Rham quotient, with multiplication
and unit fixed by the intrinsic wedge and constant scalar field. -/
structure FormsAlgebra {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) where
  product : K.GradedProduct
  laws : K.IsGradedProduct product
  gradedRing : DirectSum.GRing K.Cohomology
  algebra : letI := gradedRing; DirectSum.GAlgebra ℝ K.Cohomology
  product_eq : letI := gradedRing
    ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
      GradedMonoid.GMul.mul (A := K.Cohomology) (i := p) (j := q) x y = product.mul p q x y
  unit_eq : letI := gradedRing
    GradedMonoid.GOne.one (A := K.Cohomology) = product.one

/-- The isomorphism is an algebra isomorphism on the direct sums and is graded.
Its homogeneous components are characterized by the literal integration map,
not by an arbitrary degreewise vector space isomorphism. -/
structure RingComparison {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (U : CupProduct.CohomologyRing ℝ (TopCat.of M)) where
  forms : FormsAlgebra S K
  degreewise : ComparisonFamily S K
  integration : IsIntegrationComparison S K degreewise
  equiv : letI := forms.gradedRing; letI := forms.algebra
    letI := U.gradedRing; letI := U.algebra
    (⨁ q : ℕ, K.Cohomology q) ≃ₐ[ℝ] CupProduct.HStar ℝ (TopCat.of M)
  homogeneous : ∀ q (x : K.Cohomology q),
    equiv (DirectSum.of K.Cohomology q x) =
      DirectSum.of (CupProduct.H ℝ (TopCat.of M)) q (degreewise q x)

/-- The same ordinary cup algebras work simultaneously for every manifold.
The second conjunct states naturality for EVERY integration-induced family
under EVERY smooth map with its genuine differential and de Rham pullback. -/
def ringIsomorphism_type : Prop :=
  (∃ U : CupProduct.NaturalCohomologyRing.{0,u} ℝ,
    ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
      (S : AtlasData.SmoothManifold n a M) (C : CotangentBundle S)
      (B : ∀ k, FormBundle C k) (K : Calculus C B),
      Nonempty (RingComparison S K (U.ring (TopCat.of M)))) ∧
    DeRhamComparison.comparisonNaturality_type.{u}

/-- Integration on the shared continuous chain basis; the nonsmooth values
are merely a totalization, and are never used in the cycle identity below. -/
def integralCochain (C : CotangentBundle S) {p : ℕ} (ω : Field S p) :
    CupProduct.Cochain ℝ (TopCat.of M) p := by
  classical
  exact Finsupp.linearCombination ℝ (fun σ =>
    if h : SmoothSingularComparison.IsSmoothSimplex S p σ then
      IntegrationCochainData.simplexIntegral S C ω (p104Simplex S ⟨σ,h⟩)
    else 0)

/-- Literal integral of the external wedge along a pair of smooth simplex
maps of the same dimension. The fiber pullbacks precede wedge, with the first
factor preceding the second, and determinant-normalized evaluation is used. -/
def productSimplexIntegral {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : AtlasData.SmoothManifold m b N) (C : CotangentBundle S) (A : CotangentBundle T)
    {p q r : ℕ} (ω : Field S p) (η : Field T q)
    (σ : SmoothSingularData.SingularSimplex S r)
    (τ : SmoothSingularData.SingularSimplex T r) (h : p+q=r) : ℝ :=
  ∫ y in CornerData.simplexSet r,
    if hy : y ∈ CornerData.simplexSet r then
      evaluate (ModelData.Euclidean r) (p+q)
        (wedge
          (exteriorPower.map p (IntegrationCochainData.simplexDifferential S C σ ⟨y,hy⟩).dualMap
            (ω (σ.val ⟨y,hy⟩)))
          (exteriorPower.map q (IntegrationCochainData.simplexDifferential T A τ ⟨y,hy⟩).dualMap
            (η (τ.val ⟨y,hy⟩))))
        (fun i => Pi.single (Fin.cast h i) 1)
    else 0

/-- Linear evaluation of the external form on product chains; projections
are the actual singular projections in the shared Alexander--Whitney model. -/
def externalIntegralCochain {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : AtlasData.SmoothManifold m b N) (C : CotangentBundle S) (A : CotangentBundle T)
    {p q : ℕ} (ω : Field S p) (η : Field T q) :
    CupProduct.Cochain ℝ (AlexanderWhitney.productSpace (TopCat.of M) (TopCat.of N)) (p+q) := by
  classical
  exact Finsupp.linearCombination ℝ (fun ρ =>
    let σ := AlexanderWhitney.postSimplex
      (AlexanderWhitney.firstProjection (TopCat.of M) (TopCat.of N)) (p+q) ρ
    let τ := AlexanderWhitney.postSimplex
      (AlexanderWhitney.secondProjection (TopCat.of M) (TopCat.of N)) (p+q) ρ
    if hσ : SmoothSingularComparison.IsSmoothSimplex S (p+q) σ then
      if hτ : SmoothSingularComparison.IsSmoothSimplex T (p+q) τ then
        productSimplexIntegral S T C A ω η (p104Simplex S ⟨σ,hσ⟩)
          (p104Simplex T ⟨τ,hτ⟩) rfl
      else 0
    else 0)

/-- The product-shuffle identity on all finite smooth cycles, including degree
zero, empty manifolds, disconnected manifolds and both boundary models.
`shuffleComponent` contains exactly the upstream product-orientation signs. -/
def productShuffleIntegral_type : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E) (p q : ℕ)
    (ω : K.closed p) (η : J.closed q)
    (z : (SmoothSingularComparison.smoothComplex S).cycles p)
    (w : (SmoothSingularComparison.smoothComplex T).cycles q),
    externalIntegralCochain S T C A ω.val.val η.val.val
      (ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q
        (((SmoothSingularComparison.smoothComplex S).iCycles p z).val ⊗ₜ[ℝ]
          ((SmoothSingularComparison.smoothComplex T).iCycles q w).val)) =
      integralCochain S C ω.val.val ((SmoothSingularComparison.smoothComplex S).iCycles p z).val *
      integralCochain T A η.val.val ((SmoothSingularComparison.smoothComplex T).iCycles q w).val

/-- Original unconditional ring target. Extra premises belong only on a
separately named implementation helper, in the supplied contract order. -/
def deRhamRing_type : Prop := ringIsomorphism_type.{u} ∧ productShuffleIntegral_type.{u}

end P202Specs.DeRhamRing
