import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.InteriorHomotopyEquivalence
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.SmoothingHomotopies
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Comparison.DeRhamRing
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.TopologicalKunneth
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.ShuffleTriangulation
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Convex.Measure
import Mathlib.LinearAlgebra.Determinant
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficients
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.CupProduct
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.FormPullback
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Comparison.IntegrationCochain

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Comparison.DeRhamComparison
/-! Conditional derivation of the full ring comparison from the exact upstream
de Rham comparison proposition. The original target is reserved for the owner's
closed wrapper after genuine dependency closure. The pending P202 comparison
implementation is not imported. The independent target has no added premise. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory HomologicalComplex Opposite
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.TangentData SmoothManifolds.CovectorData
open SmoothManifolds.BundleOperationsData SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open scoped DirectSum TensorProduct Classical
namespace P202.DeRhamRing
universe u v w
open P202Specs.DeRhamComparison P202Specs.DeRhamRing
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)

/-- The literal smooth generators span the smooth chain submodule. -/
theorem smoothFunctional_ext {q : ℕ}
    (f g : P202Specs.SmoothSingularComparison.smoothModule S q →ₗ[ℝ] ℝ)
    (h : ∀ σ : SmoothSimplex S q, f (smoothGenerator S σ) = g (smoothGenerator S σ)) :
    f = g := by
  let e := Finsupp.supportedEquivFinsupp (M := ℝ) (R := ℝ)
    {σ | P202Specs.SmoothSingularComparison.IsSmoothSimplex S q σ}
  have he : f.comp e.symm.toLinearMap = g.comp e.symm.toLinearMap := by
    apply (Finsupp.basisSingleOne : Module.Basis _ ℝ (SmoothSimplex S q →₀ ℝ)).ext
    intro σ
    change f (e.symm (Finsupp.single σ 1)) = g (e.symm (Finsupp.single σ 1))
    have hσ : e.symm (Finsupp.single σ 1) = smoothGenerator S σ := by
      apply Subtype.ext
      exact Finsupp.supportedEquivFinsupp_symm_single _ _ _
    rw [hσ]
    exact h σ
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun he (e z)
  change f (e.symm (e z)) = g (e.symm (e z)) at hz
  simpa only [LinearEquiv.symm_apply_apply] using hz

/-- Evaluation on all smooth simplices determines the full categorical cochain. -/
theorem smoothCochain_ext {q : ℕ}
    (c d : (P202Specs.SmoothSingularComparison.smoothCochains S).X (q : ℤ))
    (h : ∀ σ : SmoothSimplex S q, evaluateSmoothCochain S c σ = evaluateSmoothCochain S d σ) :
    c = d := by
  let e := smoothDegreeIso S q
  have he : (show (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).X (q : ℤ) →ₗ[ℝ] ℝ from c).comp e.inv.hom =
      (show (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).X (q : ℤ) →ₗ[ℝ] ℝ from d).comp e.inv.hom :=
    smoothFunctional_ext S _ _ h
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun he (e.hom z)
  have hi := congrArg (fun t => t z) e.hom_inv_id
  change e.inv (e.hom z) = z at hi
  let c' : (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).X (q : ℤ) →ₗ[ℝ] ℝ := c
  let d' : (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).X (q : ℤ) →ₗ[ℝ] ℝ := d
  change c' (e.inv (e.hom z)) = d' (e.inv (e.hom z)) at hz
  rwa [hi] at hz

/-- The integration characterization determines a unique ordinary class as
soon as the actual smooth restriction is an isomorphism. -/
theorem integrationClass_unique (C : CotangentBundle S) {q : ℕ} (ω : Field S q)
    [IsIso (homologyMap (P202Specs.SmoothSingularComparison.restriction S) (q : ℤ))]
    {x y : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ)}
    (hx : IsIntegrationClass S C ω x) (hy : IsIntegrationClass S C ω y) : x = y := by
  obtain ⟨c, hc, hce⟩ := hx
  obtain ⟨d, hd, hde⟩ := hy
  have hcd : (P202Specs.SmoothSingularComparison.smoothCochains S).iCycles (q : ℤ) c =
      (P202Specs.SmoothSingularComparison.smoothCochains S).iCycles (q : ℤ) d :=
    smoothCochain_ext S _ _ (fun σ => (hce σ).trans (hde σ).symm)
  have hcd' : c = d :=
    (ModuleCat.mono_iff_injective _).mp inferInstance hcd
  apply (ModuleCat.mono_iff_injective
    (homologyMap (P202Specs.SmoothSingularComparison.restriction S) (q : ℤ))).mp inferInstance
  rw [← hc, ← hd, hcd']

/-- Consequently every choice of integration-induced comparison is identical. -/
theorem integrationComparison_unique {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (e f : ComparisonFamily S K)
    (he : IsIntegrationComparison S K e) (hf : IsIntegrationComparison S K f) : e = f := by
  funext q
  apply LinearEquiv.ext
  intro x
  obtain ⟨ω, rfl⟩ := (K.boundaries q).mkQ_surjective x
  letI := he.1 q
  exact integrationClass_unique S C ω.val.val (he.2 q ω) (hf.2 q ω)

/-- Equality of real cohomology classes is detected by all homology evaluations,
for arbitrary spaces and unrestricted algebraic duals, without finite type. -/
theorem realClass_ext (X : TopCat.{u}) (q : ℕ)
    {x y : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ X (q : ℤ)}
    (h : ∀ z : P202Specs.SingularChains.homology ℝ ℝ X (q : ℤ),
      P202Specs.UniversalCoefficients.evaluation ℝ ℝ
        (P202Specs.SingularChains.ordinaryComplex ℝ ℝ X) (q : ℤ) x z =
      P202Specs.UniversalCoefficients.evaluation ℝ ℝ
        (P202Specs.SingularChains.ordinaryComplex ℝ ℝ X) (q : ℤ) y z) : x = y := by
  apply (P202.UniversalCoefficients.evaluation_bijective ℝ
    (P202Specs.SingularChains.ordinaryComplex ℝ ℝ X) (q : ℤ)).injective
  exact LinearMap.ext h

/-- Normalization of the actual integral of the constant zero-form, including
manifolds with smooth boundary. -/
theorem integral_unit_simplex (C : CotangentBundle S) (σ : SmoothSimplex S 0) :
    IntegrationCochainData.simplexIntegral S C
      (FormPullbackData.scalarField S (fun _ => 1)) (p104Simplex S σ) = 1 := by
  let x : SmoothSingularData.Simplex 0 := ⟨0, by
    constructor
    · intro i; exact Fin.elim0 i
    · simp⟩
  rw [SmoothManifolds.IntegrationCochain.simplexIntegral_zero _ _ x]
  simp [FormPullbackData.scalarField]

/-- Restriction evaluates the original cochain on exactly the same smooth
singular generator, through the specified degree-extension isomorphisms. -/
theorem evaluateRestriction {q : ℕ}
    (c : (P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).X (q : ℤ))
    (σ : SmoothSimplex S q) :
    evaluateSmoothCochain S ((P202Specs.SmoothSingularComparison.restriction S).f (q : ℤ) c) σ =
      P202Specs.CohomologyPairs.ordinaryCochainsEquiv ℝ ℝ (TopCat.of M) q c
        (Finsupp.single σ.val 1) := by
  change (show (P202Specs.SingularChains.ordinaryComplex ℝ ℝ (TopCat.of M)).X (q : ℤ) →ₗ[ℝ] ℝ from c)
    ((P202Specs.SmoothSingularComparison.ordinaryInclusion S).f (q : ℤ)
      ((smoothDegreeIso S q).inv (smoothGenerator S σ))) =
    (show (P202Specs.SingularChains.ordinaryComplex ℝ ℝ (TopCat.of M)).X (q : ℤ) →ₗ[ℝ] ℝ from c)
      ((P202Specs.SingularChains.ordinaryNonnegativeIso ℝ ℝ (TopCat.of M) q).inv
        (Finsupp.single σ.val 1))
  congr 1
  change (extendMap (P202Specs.SmoothSingularComparison.inclusion S)
    (P202Specs.SingularChains.degreeEmbedding 0)).f (q : ℤ)
      ((smoothDegreeIso S q).inv (smoothGenerator S σ)) = _
  rw [HomologicalComplex.extendMap_f _ _ (show (P202Specs.SingularChains.degreeEmbedding 0).f q = (q : ℤ) by
    change (0 : ℤ) + q = q; omega)]
  simp only [ModuleCat.comp_apply]
  have hi := congrArg (fun t => t (smoothGenerator S σ)) (smoothDegreeIso S q).inv_hom_id
  change (smoothDegreeIso S q).hom ((smoothDegreeIso S q).inv (smoothGenerator S σ)) =
    smoothGenerator S σ at hi
  change (P202Specs.SingularChains.ordinaryNonnegativeIso ℝ ℝ (TopCat.of M) q).inv
    ((P202Specs.SmoothSingularComparison.inclusion S).f q
      ((smoothDegreeIso S q).hom ((smoothDegreeIso S q).inv (smoothGenerator S σ)))) = _
  rw [hi]
  rfl

/-- The ordinary cup unit is the integration class of the constant function 1.
This proves a cohomology statement, not only a pointwise sample calculation. -/
theorem unit_integrationClass (C : CotangentBundle S)
    (U : P202Specs.CupProduct.CohomologyRing ℝ (TopCat.of M)) :
    letI := U.gradedRing
    IsIntegrationClass S C (FormPullbackData.scalarField S (fun _ => 1))
      (GradedMonoid.GOne.one (A := P202Specs.CupProduct.H ℝ (TopCat.of M))) := by
  letI := U.gradedRing
  obtain ⟨c, hc, hu⟩ := U.unit_represents
  refine ⟨cyclesMap (P202Specs.SmoothSingularComparison.restriction S) 0 c, ?_, ?_⟩
  · rw [hu]
    have hn := congrArg (fun t => t c)
      (homologyπ_naturality (P202Specs.SmoothSingularComparison.restriction S) 0)
    exact hn.symm
  · intro σ
    have hi := congrArg (fun t => t c)
      (cyclesMap_i (P202Specs.SmoothSingularComparison.restriction S) 0)
    change (P202Specs.SmoothSingularComparison.smoothCochains S).iCycles 0
      (cyclesMap (P202Specs.SmoothSingularComparison.restriction S) 0 c) =
      (P202Specs.SmoothSingularComparison.restriction S).f 0
        ((P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).iCycles 0 c) at hi
    erw [hi]
    erw [evaluateRestriction]
    change P202Specs.CupProduct.cocycleValue ℝ (TopCat.of M) 0 c (Finsupp.single σ.val 1) = _
    rw [hc, integral_unit_simplex]
    exact P202.SingularChains.augmentationLinear_single ℝ ℝ (TopCat.of M) σ.val 1

/-- Every integration comparison preserves the degree-zero unit. -/
theorem comparison_unit {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (P : K.GradedProduct) (hP : K.IsGradedProduct P)
    (U : P202Specs.CupProduct.CohomologyRing ℝ (TopCat.of M))
    (e : ComparisonFamily S K) (he : IsIntegrationComparison S K e) :
    letI := U.gradedRing
    e 0 P.one = GradedMonoid.GOne.one (A := P202Specs.CupProduct.H ℝ (TopCat.of M)) := by
  letI := U.gradedRing
  obtain ⟨ε, hε, hOne⟩ := hP.2.2.2.2.2.1
  rw [hOne]
  letI := he.1 0
  apply integrationClass_unique S C ε.val.val (he.2 0 ε)
  rw [hε]
  exact unit_integrationClass S C U

section GradedEquivalence
variable (A B : ℕ → Type u)
variable [∀ q, AddCommGroup (A q)] [∀ q, Module ℝ (A q)]
variable [∀ q, AddCommGroup (B q)] [∀ q, Module ℝ (B q)]
variable [DirectSum.GRing A] [DirectSum.GAlgebra ℝ A]
variable [DirectSum.GRing B] [DirectSum.GAlgebra ℝ B]

/-- Degreewise linear equivalences that preserve the homogeneous product and
unit assemble into a genuine algebra equivalence of the full direct sums.
The sum is algebraic; no finite dimensionality of any summand is needed. -/
def gradedComparisonEquiv (e : ∀ q, A q ≃ₗ[ℝ] B q)
    (hOne : e 0 (GradedMonoid.GOne.one (A := A)) = GradedMonoid.GOne.one (A := B))
    (hMul : ∀ p q (x : A p) (y : A q),
      e (p+q) (GradedMonoid.GMul.mul (A := A) x y) =
        GradedMonoid.GMul.mul (A := B) (e p x) (e q y)) :
    (⨁ q, A q) ≃ₐ[ℝ] ⨁ q, B q := by
  let f := P202.CupProduct.gradedAlgebraMap ℝ A B
    (fun q => (e q).toLinearMap) hOne hMul
  have hf : f.toLinearMap = (DirectSum.congrLinearEquiv e).toLinearMap := by
    apply DirectSum.linearMap_ext
    intro q
    apply LinearMap.ext
    intro x
    change f (DirectSum.of A q x) = (DirectSum.congrLinearEquiv e) (DirectSum.of A q x)
    rw [P202.CupProduct.gradedAlgebraMap_of]
    change _ = DirectSum.lmap (fun q => (e q).toLinearMap) (DirectSum.of A q x)
    rw [DirectSum.lmap_of]
  refine AlgEquiv.ofBijective f ?_
  change Function.Bijective f.toLinearMap
  rw [hf]
  exact (DirectSum.congrLinearEquiv e).bijective

@[simp] theorem gradedComparisonEquiv_of (e : ∀ q, A q ≃ₗ[ℝ] B q)
    (hOne : e 0 (GradedMonoid.GOne.one (A := A)) = GradedMonoid.GOne.one (A := B))
    (hMul : ∀ p q (x : A p) (y : A q),
      e (p+q) (GradedMonoid.GMul.mul (A := A) x y) =
        GradedMonoid.GMul.mul (A := B) (e p x) (e q y))
    (q : ℕ) (x : A q) :
    gradedComparisonEquiv A B e hOne hMul (DirectSum.of A q x) =
      DirectSum.of B q (e q x) := by
  exact P202.CupProduct.gradedAlgebraMap_of ℝ A B (fun q => (e q).toLinearMap) hOne hMul q x
end GradedEquivalence

/-- Package P104's actual wedge product in the standard direct-sum graded
algebra interface. All the laws here are supplied by the proved P104 result. -/
def formsAlgebraOfProduct {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (P : K.GradedProduct) (hP : K.IsGradedProduct P) :
    FormsAlgebra S K := by
  obtain ⟨hAL, hAR, hSL, hSR, hRep, hOne, hAssoc, hComm, hL, hR⟩ := hP
  let μ : ∀ p q, K.Cohomology p →ₗ[ℝ] K.Cohomology q →ₗ[ℝ] K.Cohomology (p+q) :=
    fun p q =>
      { toFun := fun x =>
          { toFun := P.mul p q x
            map_add' := fun y z => hAR p q x y z
            map_smul' := fun r y => by simpa using hSR p q r x y }
        map_add' := fun x y => LinearMap.ext (fun z => hAL p q x y z)
        map_smul' := fun r x => LinearMap.ext (fun y => by simpa using hSL p q r x y) }
  have hl : ∀ p (x : K.Cohomology p),
      GradedMonoid.mk (0+p) (μ 0 p P.one x) = GradedMonoid.mk p x := by
    intro p x
    exact Sigma.ext (Nat.zero_add p) (cast_eq_iff_heq.mp (hL p x))
  have hr : ∀ p (x : K.Cohomology p),
      GradedMonoid.mk (p+0) (μ p 0 x P.one) = GradedMonoid.mk p x := by
    intro p x
    exact congrArg (GradedMonoid.mk p) (hR p x)
  have ha : ∀ p q r (x : K.Cohomology p) (y : K.Cohomology q) (z : K.Cohomology r),
      GradedMonoid.mk ((p+q)+r) (μ (p+q) r (μ p q x y) z) =
        GradedMonoid.mk (p+(q+r)) (μ p (q+r) x (μ q r y z)) := by
    intro p q r x y z
    exact Sigma.ext (Nat.add_assoc p q r) (cast_eq_iff_heq.mp (hAssoc p q r x y z))
  exact {
    product := P
    laws := ⟨hAL, hAR, hSL, hSR, hRep, hOne, hAssoc, hComm, hL, hR⟩
    gradedRing := P202.CupProduct.gradedRingOfBilinear ℝ K.Cohomology μ P.one hl hr ha
    algebra := P202.CupProduct.gradedAlgebraOfBilinear ℝ K.Cohomology μ P.one hl hr ha
    product_eq := fun _ _ _ _ => rfl
    unit_eq := rfl }

/-- Existence is inherited from P104's intrinsic quotient and wedge theorem,
not postulated as an additional comparison hypothesis. -/
def intrinsicFormsAlgebra {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) : FormsAlgebra S K :=
  formsAlgebraOfProduct S K (Classical.choose (SmoothManifolds.DeRhamResults.product_exists K))
    (Classical.choose_spec (SmoothManifolds.DeRhamResults.product_exists K))

section FieldProducts
open P202Specs.TopologicalKunneth
open P103.Specs.Ch11.TorBalance P103.Specs.Ch11.ExtTorDefinitions
variable (R : Type v) [Field R]

/-- Positive Tor vanishes over a field for arbitrary homology modules and
for every projective resolution in the fixed Künneth interface. -/
theorem fieldTorSum_subsingleton (P : Models.{v,w} R)
    (T : TorMaps.{v,max v w,max v w} R 1) (X Y : TopCat.{w}) (n : ℕ) :
    Subsingleton (TorSum R P T X Y n) := by
  letI (i : TailDiagonal n) : Subsingleton (TorSummand R P X Y i.val) :=
    P103.Ch11.VanishingAndFlatness.tor_left_flat R _ (H R Y i.val.2)
      (P103.Ch02.FlatnessTests.projective_flat R (H R Y i.val.2) inferInstance)
      (P X i.val.1).val (P X i.val.1).property 0
  unfold TorSum
  infer_instance

/-- The tensor-sum arrow of any supplied Künneth sequence is surjective over
a field, with no finite rank or finite type assumptions. -/
theorem fieldKunneth_surjective (P : Models.{v,w} R)
    (T : TorMaps.{v,max v w,max v w} R 1) (s : NaturalSequence R P T)
    (X Y : TopCat.{w}) (n : ℕ) : Function.Surjective (s.α X Y n) := by
  letI := fieldTorSum_subsingleton R P T X Y n
  intro z
  exact (s.exact X Y n z).mp (Subsingleton.elim _ _)

/-- Linear functionals on product homology are determined by their values on
pure product classes. `NaturalSequence.α_external` identifies these generators
with the actual shuffle-induced external products. -/
theorem fieldProductFunctional_ext (P : Models.{v,w} R)
    (T : TorMaps.{v,max v w,max v w} R 1) (s : NaturalSequence R P T)
    (X Y : TopCat.{w}) (n : ℕ)
    (f g : H R (P202Specs.AlexanderWhitney.productSpace X Y) n →ₗ[R] R)
    (h : ∀ (i : P202Specs.AlexanderWhitney.Diagonal n)
      (x : H R X i.val.1) (y : H R Y i.val.2),
      f (s.α X Y n (DirectSum.lof R _ _ i (x ⊗ₜ[R] y))) =
      g (s.α X Y n (DirectSum.lof R _ _ i (x ⊗ₜ[R] y)))) : f = g := by
  have he : f.comp (s.α X Y n) = g.comp (s.α X Y n) := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.ext'
    intro x y
    exact h i x y
  apply LinearMap.ext
  intro z
  obtain ⟨t, rfl⟩ := fieldKunneth_surjective R P T s X Y n z
  exact LinearMap.congr_fun he t
end FieldProducts

section ExternalPairing
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CupProduct P202Specs.ShuffleModel
variable (R : Type v) [CommRing R]

/-- Evaluation in a fixed bidegree of the tensor total for two different
spaces. The order of the two factors is the product orientation order. -/
def externalTotalPairing {X Y : TopCat.{u}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q) :
    Total R X Y (p+q) →ₗ[R] R :=
  (tensorPairing R a b).comp (LinearMap.proj (R := R)
    (φ := fun i : Diagonal (p+q) => Summand R X Y i.val.1 i.val.2) ⟨(p,q),rfl⟩)

/-- The usual exterior cochain product, using the original singular cup
and the two continuous product projections. -/
def externalCup {X Y : TopCat.{u}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q) : Cochain R (productSpace X Y) (p+q) :=
  cup R (productSpace X Y) p q
    (pullback R (firstProjection X Y) p a)
    (pullback R (secondProjection X Y) q b)

/-- The external cup formula is exactly evaluation of the corresponding AW
component, on all finite chains. -/
theorem externalCup_aw {X Y : TopCat.{u}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q)
    (z : Chains R (productSpace X Y) (p+q)) :
    externalCup R a b z = externalTotalPairing R a b (aw R X Y (p+q) z) := by
  have he : externalCup R a b =
      (externalTotalPairing R a b).comp (aw R X Y (p+q)) := by
    apply (Finsupp.basisSingleOne : Module.Basis _ R
      (Chains R (productSpace X Y) (p+q))).ext
    intro σ
    change cup R (productSpace X Y) p q _ _ (Finsupp.single σ 1) = _
    rw [P202.CupProduct.cup_single]
    simp only [one_mul, pullback, LinearMap.lcomp_apply]
    erw [P202.SingularChains.chainMap_single, P202.SingularChains.chainMap_single]
    change _ = tensorPairing R a b (aw R X Y (p+q) (Finsupp.single σ 1) ⟨(p,q),rfl⟩)
    rw [P202.AlexanderWhitney.formula]
    simp only [one_smul, awComponent, P202.CupProduct.tensorPairing_tmul]
    change a (Finsupp.single (postSimplex (firstProjection X Y) p
      (interval σ 0 p (by omega))) 1) *
        b (Finsupp.single (postSimplex (secondProjection X Y) q
          (interval σ p q (by omega))) 1) = _
    rw [P202.AlexanderWhitney.post_interval, P202.AlexanderWhitney.post_interval]
  exact LinearMap.congr_fun he z

/-- Tensor evaluation by cocycles vanishes on every total boundary. This
holds without any finite-dimensionality condition and for distinct factors. -/
theorem externalTotalPairing_boundary {X Y : TopCat.{u}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q)
    (ha : delta R X p a = 0) (hb : delta R Y q b = 0)
    (z : Total R X Y (p+q+1)) :
    externalTotalPairing R a b (totalBoundary R X Y (p+q) z) = 0 := by
  have hl : ∀ t : Summand R X Y (p+1) q,
      tensorPairing R a b (leftBoundary R X Y p q t) = 0 := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c d =>
      change a (chainBoundary R X p c) * b d = 0
      have h := LinearMap.congr_fun ha c
      change a (chainBoundary R X p c) = 0 at h
      rw [h, zero_mul]
    | add t t' ht ht' => simp only [map_add, ht, ht', add_zero]
  have hr : ∀ t : Summand R X Y p (q+1),
      tensorPairing R a b (rightBoundary R X Y p q t) = 0 := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c d =>
      change a c * b (chainBoundary R Y q d) = 0
      have h := LinearMap.congr_fun hb d
      change b (chainBoundary R Y q d) = 0 at h
      rw [h, mul_zero]
    | add t t' ht ht' => simp only [map_add, ht, ht', add_zero]
  change tensorPairing R a b
    (leftBoundary R X Y p q (z ⟨(p+1,q),by omega⟩) +
      (-1 : ℤ)^p • rightBoundary R X Y p q (z ⟨(p,q+1),by omega⟩)) = 0
  rw [map_add, map_zsmul, hl, hr, smul_zero, add_zero]

/-- The actual tensor-side homotopy identifies external cup evaluation with
the tensor pairing on every total cycle, including total degree zero. -/
theorem externalCup_shuffle_totalCycle {X Y : TopCat.{u}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q)
    (ha : delta R X p a = 0) (hb : delta R Y q b = 0)
    (z : (tensorComplex R X Y).cycles (p+q)) :
    externalCup R a b
      (shuffle R X Y (p+q) ((tensorComplex R X Y).iCycles (p+q) z)) =
    externalTotalPairing R a b ((tensorComplex R X Y).iCycles (p+q) z) := by
  obtain ⟨H, _⟩ := P202.EZTensorHomotopy.naturalHomotopy.{v,u,0,0,0,0} R
  let t : Total R X Y (p+q) := (tensorComplex R X Y).iCycles (p+q) z
  have hz : ((tensorComplex R X Y).d (p+q) (p+q-1)).hom t = 0 :=
    congrArg (fun f => f.hom z) ((tensorComplex R X Y).iCycles_d (p+q) (p+q-1))
  have hdiff : ∀ n (t : Total R X Y n),
      ((tensorComplex R X Y).d n (n-1)).hom t = 0 →
      aw R X Y n (shuffle R X Y n t) - t =
        totalBoundary R X Y n (H.hom X Y n t) := by
    intro n t ht
    cases n with
    | zero => exact LinearMap.congr_fun (H.zero X Y) t
    | succ k =>
      have hh := LinearMap.congr_fun (H.succ X Y k) t
      have ht' : totalBoundary R X Y k t = 0 := by
        rw [show k+1-1=k by omega] at ht
        simpa only [tensorComplex, ChainComplex.of_d, ModuleCat.hom_ofHom] using ht
      simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_coe,
        id_eq, LinearMap.add_apply, ht', map_zero, add_zero] using hh
  rw [externalCup_aw]
  have he := congrArg (externalTotalPairing R a b) (hdiff (p+q) t hz)
  rw [map_sub, externalTotalPairing_boundary R a b ha hb] at he
  exact sub_eq_zero.mp he
end ExternalPairing

/-- Once the substantive wedge/cup identity is proved, the existing
integration comparison and its already proved unit law yield the full graded
algebra equivalence in the independent specification. -/
def ringComparisonOfMultiplicative {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (A : FormsAlgebra S K)
    (U : P202Specs.CupProduct.CohomologyRing ℝ (TopCat.of M))
    (e : ComparisonFamily S K) (he : IsIntegrationComparison S K e)
    (hm : ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
      e (p+q) (A.product.mul p q x y) = U.product p q (e p x) (e q y)) :
    RingComparison S K U := by
  letI := A.gradedRing
  letI := A.algebra
  letI := U.gradedRing
  letI := U.algebra
  have h1 : e 0 (GradedMonoid.GOne.one (A := K.Cohomology)) =
      GradedMonoid.GOne.one (A := P202Specs.CupProduct.H ℝ (TopCat.of M)) := by
    rw [A.unit_eq]
    exact comparison_unit S K A.product A.laws U e he
  have hm' : ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
      e (p+q) (GradedMonoid.GMul.mul (A := K.Cohomology) (i := p) (j := q) x y) =
        GradedMonoid.GMul.mul (A := P202Specs.CupProduct.H ℝ (TopCat.of M))
          (i := p) (j := q) (e p x) (e q y) := by
    intro p q x y
    rw [A.product_eq, U.product_eq]
    exact hm p q x y
  exact {
    forms := A
    degreewise := e
    integration := he
    equiv := gradedComparisonEquiv K.Cohomology (P202Specs.CupProduct.H ℝ (TopCat.of M)) e h1 hm'
    homogeneous := gradedComparisonEquiv_of K.Cohomology
      (P202Specs.CupProduct.H ℝ (TopCat.of M)) e h1 hm' }

/-- The exact upstream comparison proposition gives a unital comparison on
every intrinsic de Rham quotient. The full multiplicative conclusion is
assembled below in `deRhamRing_conditional`. -/
theorem unitalComparison_exists_conditional
    (hDR : P202Specs.DeRhamComparison.deRhamComparison_type.{u})
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B) :
    ∃ e : ComparisonFamily S K, IsIntegrationComparison S K e ∧
      ∀ (P : K.GradedProduct), K.IsGradedProduct P →
      ∀ U : P202Specs.CupProduct.CohomologyRing ℝ (TopCat.of M),
        letI := U.gradedRing
        e 0 P.one = GradedMonoid.GOne.one (A := P202Specs.CupProduct.H ℝ (TopCat.of M)) := by
  obtain ⟨e, he⟩ := hDR.1 S C B K
  exact ⟨e, he, fun P hP U => comparison_unit S K P hP U e he⟩

/-- Evaluation of categorical cycle classes is evaluation of their actual
chain and cochain representatives, with unrestricted algebraic duals. -/
theorem evaluation_cycles (R : Type v) [CommRing R]
    (A : Type w) [AddCommGroup A] [Module R A]
    (K : ChainComplex (ModuleCat.{u} R) ℤ) (q : ℤ)
    (c : (P202Specs.UniversalCoefficients.dualChain R A K).cycles q)
    (z : K.cycles q) :
    P202Specs.UniversalCoefficients.evaluation R A K q
      ((P202Specs.UniversalCoefficients.dualChain R A K).homologyπ q c)
      (K.homologyπ q z) =
      (show K.X q →ₗ[R] A from
        (P202Specs.UniversalCoefficients.dualChain R A K).iCycles q c) (K.iCycles q z) := by
  let D := P202Specs.UniversalCoefficients.dualChain R A K
  let c' : P202Specs.UniversalCoefficients.Algebraic.cycles D q :=
    (D.sc q).moduleCatCyclesIso.hom c
  let z' : P202Specs.UniversalCoefficients.Algebraic.cycles K q :=
    (K.sc q).moduleCatCyclesIso.hom z
  have hc : P202Specs.UniversalCoefficients.cycleClass R D q c' = D.homologyπ q c := by
    exact (P202.UniversalCoefficientsCohomology.cycleClass_eq R D q c').trans
      (congrArg (fun t => D.homologyπ q t) (ModuleCat.inv_hom_apply (D.sc q).moduleCatCyclesIso c))
  have hz : P202Specs.UniversalCoefficients.cycleClass R K q z' = K.homologyπ q z := by
    exact (P202.UniversalCoefficientsCohomology.cycleClass_eq R K q z').trans
      (congrArg (fun t => K.homologyπ q t) (ModuleCat.inv_hom_apply (K.sc q).moduleCatCyclesIso z))
  erw [← hc, ← hz, P202.UniversalCoefficients.evaluation_formula]
  have hc' : c'.val = D.iCycles q c :=
    congrArg (fun f => f c) (D.sc q).moduleCatCyclesIso_hom_i
  have hz' : z'.val = K.iCycles q z :=
    congrArg (fun f => f z) (K.sc q).moduleCatCyclesIso_hom_i
  change (show K.X q →ₗ[R] A from c'.val) z'.val = _
  rw [hc', hz']


/-- A cochain with the integration values on all smooth simplices has the
literal integral on every finite smooth chain. -/
theorem integration_on_smoothChains (C : CotangentBundle S) {q : ℕ}
    (ω : Field S q)
    (c : (P202Specs.SmoothSingularComparison.smoothCochains S).X (q : ℤ))
    (hc : ∀ σ : SmoothSimplex S q, evaluateSmoothCochain S c σ =
      IntegrationCochainData.simplexIntegral S C ω (p104Simplex S σ))
    (z : P202Specs.SmoothSingularComparison.smoothModule S q) :
    (show (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).X (q : ℤ) →ₗ[ℝ] ℝ
      from c) ((smoothDegreeIso S q).inv z) = integralCochain S C ω z.val := by
  have he :
      (show (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).X (q : ℤ) →ₗ[ℝ] ℝ
        from c).comp (smoothDegreeIso S q).inv.hom =
      (integralCochain S C ω).comp
        (P202Specs.SmoothSingularComparison.smoothModule S q).subtype := by
    apply smoothFunctional_ext S
    intro σ
    change evaluateSmoothCochain S c σ = integralCochain S C ω (Finsupp.single σ.val 1)
    rw [hc]
    simp [integralCochain, σ.property]
  exact LinearMap.congr_fun he z

/-- The integration characterization fixes evaluation on every smooth cycle,
not merely on the simplex generators. -/
theorem integrationClass_evaluation (C : CotangentBundle S) {q : ℕ}
    (ω : Field S q)
    (x : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ))
    (hx : IsIntegrationClass S C ω x)
    (z : (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).cycles (q : ℤ)) :
    P202Specs.UniversalCoefficients.evaluation ℝ ℝ
      (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S) (q : ℤ)
      (homologyMap (P202Specs.SmoothSingularComparison.restriction S) (q : ℤ) x)
      ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (q : ℤ) z) =
      integralCochain S C ω
        ((smoothDegreeIso S q).hom
          ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).iCycles (q : ℤ) z)).val := by
  obtain ⟨c, hc, hcv⟩ := hx
  rw [← hc]
  erw [evaluation_cycles]
  let t := (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).iCycles (q : ℤ) z
  have he := integration_on_smoothChains S C ω
    ((P202Specs.SmoothSingularComparison.smoothCochains S).iCycles (q : ℤ) c)
    hcv ((smoothDegreeIso S q).hom t)
  have hi := congrArg (fun f => f t) (smoothDegreeIso S q).hom_inv_id
  change (smoothDegreeIso S q).inv ((smoothDegreeIso S q).hom t) = t at hi
  rwa [hi] at he

/-- Integration computes the ordinary cohomology evaluation on the image of
every smooth cycle. The ordinary representative may differ by a coboundary. -/
theorem integrationClass_ordinaryEvaluation (C : CotangentBundle S) {q : ℕ}
    (ω : Field S q)
    (x : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ))
    (hx : IsIntegrationClass S C ω x)
    (z : (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).cycles (q : ℤ)) :
    P202Specs.UniversalCoefficients.evaluation ℝ ℝ
      (P202Specs.SingularChains.ordinaryComplex ℝ ℝ (TopCat.of M)) (q : ℤ) x
      (homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion S) (q : ℤ)
        ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (q : ℤ) z)) =
      integralCochain S C ω
        ((smoothDegreeIso S q).hom
          ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).iCycles (q : ℤ) z)).val := by
  have hn := P202.UniversalCoefficientsCohomology.evaluation_natural ℝ ℝ ℝ
    (P202Specs.SmoothSingularComparison.ordinaryInclusion S) LinearMap.id q x
    ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (q : ℤ) z)
  rw [P202.UniversalCoefficientsCohomology.dualMap_id] at hn
  exact hn.symm.trans (integrationClass_evaluation S C ω x hx z)

/-- Real cohomology is detected on smooth cycles once the actual restriction
is an isomorphism. Neither cohomology group is assumed finite dimensional. -/
theorem realClass_ext_smoothCycles {q : ℕ}
    [IsIso (homologyMap (P202Specs.SmoothSingularComparison.restriction S) (q : ℤ))]
    {x y : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ)}
    (h : ∀ z : (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).cycles (q : ℤ),
      P202Specs.UniversalCoefficients.evaluation ℝ ℝ
        (P202Specs.SingularChains.ordinaryComplex ℝ ℝ (TopCat.of M)) (q : ℤ) x
        (homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion S) (q : ℤ)
          ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (q : ℤ) z)) =
      P202Specs.UniversalCoefficients.evaluation ℝ ℝ
        (P202Specs.SingularChains.ordinaryComplex ℝ ℝ (TopCat.of M)) (q : ℤ) y
        (homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion S) (q : ℤ)
          ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (q : ℤ) z))) :
    x = y := by
  apply (ModuleCat.mono_iff_injective
    (homologyMap (P202Specs.SmoothSingularComparison.restriction S) (q : ℤ))).mp inferInstance
  apply (P202.UniversalCoefficients.evaluation_bijective ℝ
    (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S) (q : ℤ)).injective
  apply LinearMap.ext
  intro t
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (q : ℤ))).mp
      inferInstance t
  have hx := P202.UniversalCoefficientsCohomology.evaluation_natural ℝ ℝ ℝ
    (P202Specs.SmoothSingularComparison.ordinaryInclusion S) LinearMap.id q x
    ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (q : ℤ) z)
  have hy := P202.UniversalCoefficientsCohomology.evaluation_natural ℝ ℝ ℝ
    (P202Specs.SmoothSingularComparison.ordinaryInclusion S) LinearMap.id q y
    ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (q : ℤ) z)
  rw [P202.UniversalCoefficientsCohomology.dualMap_id] at hx hy
  exact hx.trans ((h z).trans hy.symm)


section ProductIntegration
/-- The determinant normalization of the exterior product is ordinary scalar
multiplication in degree zero. -/
theorem evaluate_wedge_zero (V : Type u) [AddCommGroup V] [Module ℝ V]
    (α β : Fiber V 0) (v : Fin 0 → V) :
    evaluate V 0 (wedge α β) v =
      exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V) α *
      exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V) β := by
  obtain ⟨r, rfl⟩ := (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)).symm.surjective α
  obtain ⟨s, rfl⟩ := (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ V)).symm.surjective β
  rw [SimplexPullbackIntegral.evaluate_zero]
  simp only [LinearEquiv.apply_symm_apply]
  simp only [exteriorPower.zeroEquiv_symm_apply, map_smul, LinearMap.smul_apply,
    ExteriorDerivativeResults.exterior_wedge_degree_zero, exteriorPower.zeroEquiv_ιMulti,
    smul_eq_mul]
  ring


variable {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
  (T : AtlasData.SmoothManifold m b N)

/-- The literal external integral over a zero-simplex is the product of the
two literal integrals, without any closure or nonemptiness assumption. -/
theorem productSimplexIntegral_zero_zero (C : CotangentBundle S) (A : CotangentBundle T)
    (ω : Field S 0) (η : Field T 0)
    (σ : SmoothSingularData.SingularSimplex S 0)
    (τ : SmoothSingularData.SingularSimplex T 0) :
    productSimplexIntegral S T C A ω η σ τ rfl =
      IntegrationCochainData.simplexIntegral S C ω σ *
      IntegrationCochainData.simplexIntegral T A η τ := by
  let x : SmoothSingularData.Simplex 0 := ⟨0, by
    constructor
    · intro i; exact Fin.elim0 i
    · simp⟩
  rw [IntegrationCochain.simplexIntegral_zero ω σ x,
    IntegrationCochain.simplexIntegral_zero η τ x]
  have hset : CornerData.simplexSet 0 = Set.univ := by
    ext y; simp [CornerData.simplexSet]
  unfold productSimplexIntegral
  have hf : (fun y : ModelData.Euclidean 0 =>
      if hy : y ∈ CornerData.simplexSet 0 then
        evaluate (ModelData.Euclidean 0) 0
          (wedge
            (exteriorPower.map 0 (IntegrationCochainData.simplexDifferential S C σ ⟨y,hy⟩).dualMap (ω (σ.val ⟨y,hy⟩)))
            (exteriorPower.map 0 (IntegrationCochainData.simplexDifferential T A τ ⟨y,hy⟩).dualMap (η (τ.val ⟨y,hy⟩))))
          (fun i => Pi.single (Fin.cast rfl i) 1)
      else 0) = fun _ =>
        exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentData.TangentSpace S (σ.val x))) (ω (σ.val x)) *
        exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentData.TangentSpace T (τ.val x))) (η (τ.val x)) := by
    funext y
    have hy : y ∈ CornerData.simplexSet 0 := by rw [hset]; trivial
    rw [dif_pos hy]
    rw [evaluate_wedge_zero]
    rw [show (⟨y, hy⟩ : SmoothSingularData.Simplex 0) = x by
      exact Subtype.ext (Subsingleton.elim _ _)]
    exact congrArg₂ (fun r s : ℝ => r * s)
      (LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality
        (IntegrationCochainData.simplexDifferential S C σ x).dualMap) (ω (σ.val x)))
      (LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality
        (IntegrationCochainData.simplexDifferential T A τ x).dualMap) (η (τ.val x)))
  rw [hf, hset, MeasureTheory.setIntegral_univ, MeasureTheory.integral_const]
  have hv : (MeasureTheory.volume : MeasureTheory.Measure (ModelData.Euclidean 0)) Set.univ = 1 :=
    MeasureTheory.Measure.pi_empty_univ (fun _ : Fin 0 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
  simp [MeasureTheory.Measure.real, hv]

/-- In dimension zero each shuffle projection is its original ordered point. -/
theorem shuffle_zero_zero_first
    (σ : P202Specs.SingularChains.Simplex (TopCat.of M) 0)
    (τ : P202Specs.SingularChains.Simplex (TopCat.of N) 0) :
    P202Specs.AlexanderWhitney.postSimplex
      (P202Specs.AlexanderWhitney.firstProjection (TopCat.of M) (TopCat.of N)) 0
      (P202Specs.ShuffleModel.shuffleSimplex (P202Specs.ShuffleModel.zeroLeft 0) σ τ) = σ := by
  apply (P202Specs.SingularChains.simplexEquiv (TopCat.of M) 0).injective
  unfold P202Specs.AlexanderWhitney.postSimplex
  rw [P202.SingularChains.simplexEquiv_postcomp]
  ext z
  simp only [P202Specs.ShuffleModel.shuffleSimplex, Equiv.apply_symm_apply,
    ContinuousMap.comp_apply]
  change P202Specs.SingularChains.simplexEquiv (TopCat.of M) 0 σ _ =
    P202Specs.SingularChains.simplexEquiv (TopCat.of M) 0 σ z
  congr 1
  letI : Subsingleton (Fin (0+1)) := ⟨by intro i j; apply Fin.ext; omega⟩
  exact Subsingleton.elim _ _

theorem shuffle_zero_zero_second
    (σ : P202Specs.SingularChains.Simplex (TopCat.of M) 0)
    (τ : P202Specs.SingularChains.Simplex (TopCat.of N) 0) :
    P202Specs.AlexanderWhitney.postSimplex
      (P202Specs.AlexanderWhitney.secondProjection (TopCat.of M) (TopCat.of N)) 0
      (P202Specs.ShuffleModel.shuffleSimplex (P202Specs.ShuffleModel.zeroLeft 0) σ τ) = τ := by
  apply (P202Specs.SingularChains.simplexEquiv (TopCat.of N) 0).injective
  unfold P202Specs.AlexanderWhitney.postSimplex
  rw [P202.SingularChains.simplexEquiv_postcomp]
  ext z
  simp only [P202Specs.ShuffleModel.shuffleSimplex, Equiv.apply_symm_apply,
    ContinuousMap.comp_apply]
  change P202Specs.SingularChains.simplexEquiv (TopCat.of N) 0 τ _ =
    P202Specs.SingularChains.simplexEquiv (TopCat.of N) 0 τ z
  congr 1
  letI : Subsingleton (Fin (0+1)) := ⟨by intro i j; apply Fin.ext; omega⟩
  exact Subsingleton.elim _ _

/-- The complete oriented shuffle identity on individual degree-zero smooth
basis chains. This uses the genuine upstream signed shuffle. -/
theorem productShuffleIntegral_basis_zero_zero (C : CotangentBundle S) (A : CotangentBundle T)
    (ω : Field S 0) (η : Field T 0) (σ : SmoothSimplex S 0) (τ : SmoothSimplex T 0) :
    externalIntegralCochain S T C A ω η
      (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) 0 0
        (Finsupp.single σ.val 1 ⊗ₜ[ℝ] Finsupp.single τ.val 1)) =
      integralCochain S C ω (Finsupp.single σ.val 1) *
      integralCochain T A η (Finsupp.single τ.val 1) := by
  rw [P202.ShuffleChains.component_zero_left]
  simp only [externalIntegralCochain, integralCochain, Finsupp.linearCombination_single,
    one_smul]
  rw [shuffle_zero_zero_first, shuffle_zero_zero_second]
  simp only [dif_pos σ.property, dif_pos τ.property]
  exact productSimplexIntegral_zero_zero S T C A ω η (p104Simplex S σ) (p104Simplex T τ)

/-- A shuffle integral identity on individual smooth simplex pairs extends to
all finite smooth chains, in every bidegree. -/
theorem productShuffleIntegral_chains_of_basis (C : CotangentBundle S) (A : CotangentBundle T)
    {p q : ℕ} (ω : Field S p) (η : Field T q)
    (h : ∀ (σ : SmoothSimplex S p) (τ : SmoothSimplex T q),
      externalIntegralCochain S T C A ω η
        (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q
          (Finsupp.single σ.val 1 ⊗ₜ[ℝ] Finsupp.single τ.val 1)) =
      integralCochain S C ω (Finsupp.single σ.val 1) *
        integralCochain T A η (Finsupp.single τ.val 1))
    (z : P202Specs.SmoothSingularComparison.smoothModule S p)
    (w : P202Specs.SmoothSingularComparison.smoothModule T q) :
    externalIntegralCochain S T C A ω η
      (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q
        (z.val ⊗ₜ[ℝ] w.val)) =
      integralCochain S C ω z.val * integralCochain T A η w.val := by
  let L := TensorProduct.curry ((externalIntegralCochain S T C A ω η).comp
    (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q))
  let R := (integralCochain S C ω).smulRight (integralCochain T A η)
  have hw : ∀ σ : SmoothSimplex S p,
      L (Finsupp.single σ.val 1) w.val = R (Finsupp.single σ.val 1) w.val := by
    intro σ
    apply LinearMap.eqOn_span (s := (fun τ => Finsupp.single τ (1 : ℝ)) ''
      {τ | P202Specs.SmoothSingularComparison.IsSmoothSimplex T q τ})
    · intro y hy
      obtain ⟨τ,hτ,rfl⟩ := hy
      exact h σ ⟨τ,hτ⟩
    · rw [← Finsupp.supported_eq_span_single]
      exact w.property
  change L z.val w.val = R z.val w.val
  apply LinearMap.eqOn_span (f := L.flip w.val) (g := R.flip w.val)
    (s := (fun σ => Finsupp.single σ (1 : ℝ)) ''
      {σ | P202Specs.SmoothSingularComparison.IsSmoothSimplex S p σ})
  · intro y hy
    obtain ⟨σ,hσ,rfl⟩ := hy
    exact hw ⟨σ,hσ⟩
  · rw [← Finsupp.supported_eq_span_single]
    exact z.property

/-- Fubini's product formula in degree zero for every finite smooth chain,
including arbitrary disconnected and empty manifolds with smooth boundary. -/
theorem productShuffleIntegral_zero_zero (C : CotangentBundle S) (A : CotangentBundle T)
    (ω : Field S 0) (η : Field T 0)
    (z : P202Specs.SmoothSingularComparison.smoothModule S 0)
    (w : P202Specs.SmoothSingularComparison.smoothModule T 0) :
    externalIntegralCochain S T C A ω η
      (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) 0 0
        (z.val ⊗ₜ[ℝ] w.val)) =
      integralCochain S C ω z.val * integralCochain T A η w.val :=
  productShuffleIntegral_chains_of_basis S T C A ω η
    (productShuffleIntegral_basis_zero_zero S T C A ω η) z w

/-- Literal Fubini for the separate simplex pullback coefficients in all
nonnegative degrees. The product measure uses the ordered factor orientation. -/
theorem simplexIntegral_product_fubini (C : CotangentBundle S) (A : CotangentBundle T)
    {p q : ℕ} (ω : Field S p) (η : Field T q)
    (σ : SmoothSingularData.SingularSimplex S p)
    (τ : SmoothSingularData.SingularSimplex T q) :
    (∫ xy in CornerData.simplexSet p ×ˢ CornerData.simplexSet q,
      IntegrationCochainData.ambientPullbackCoefficient S C ω σ xy.1 *
      IntegrationCochainData.ambientPullbackCoefficient T A η τ xy.2
      ∂(MeasureTheory.volume.prod MeasureTheory.volume)) =
      IntegrationCochainData.simplexIntegral S C ω σ *
      IntegrationCochainData.simplexIntegral T A η τ := by
  exact MeasureTheory.setIntegral_prod_mul
    (IntegrationCochainData.ambientPullbackCoefficient S C ω σ)
    (IntegrationCochainData.ambientPullbackCoefficient T A η τ)
    (CornerData.simplexSet p) (CornerData.simplexSet q)

end ProductIntegration

section PureCyclePairing
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CupProduct P202Specs.ShuffleModel
variable (R : Type v) [CommRing R]

private def tensorLeftIndex {n : ℕ} (j : Diagonal n) : Diagonal (n+1) :=
  ⟨(j.val.1+1,j.val.2),by have := j.property; omega⟩
private def tensorRightIndex {n : ℕ} (j : Diagonal n) : Diagonal (n+1) :=
  ⟨(j.val.1,j.val.2+1),by have := j.property; omega⟩

/-- An elementary tensor of cycles has zero total boundary in every positive degree. -/
theorem pureTensor_totalBoundary {X Y : TopCat.{u}} (n : ℕ) (i : Diagonal (n+1))
    (a : (complex R R X).cycles i.val.1) (b : (complex R R Y).cycles i.val.2) :
    totalBoundary R X Y n
      (LinearMap.single R (fun j : Diagonal (n+1) => Summand R X Y j.val.1 j.val.2)
        i ((complex R R X).iCycles i.val.1 a ⊗ₜ[R] (complex R R Y).iCycles i.val.2 b)) = 0 := by
  classical
  funext j
  change leftBoundary R X Y j.val.1 j.val.2
      (Pi.single (M := fun k : Diagonal (n+1) => Summand R X Y k.val.1 k.val.2) i ((complex R R X).iCycles i.val.1 a ⊗ₜ[R] (complex R R Y).iCycles i.val.2 b)
        (tensorLeftIndex j)) +
    (-1 : ℤ)^j.val.1 • rightBoundary R X Y j.val.1 j.val.2
      (Pi.single (M := fun k : Diagonal (n+1) => Summand R X Y k.val.1 k.val.2) i ((complex R R X).iCycles i.val.1 a ⊗ₜ[R] (complex R R Y).iCycles i.val.2 b)
        (tensorRightIndex j)) = 0
  have hl : leftBoundary R X Y j.val.1 j.val.2
      (Pi.single (M := fun k : Diagonal (n+1) => Summand R X Y k.val.1 k.val.2) i ((complex R R X).iCycles i.val.1 a ⊗ₜ[R] (complex R R Y).iCycles i.val.2 b)
        (tensorLeftIndex j)) = 0 := by
    by_cases h : (tensorLeftIndex j : Diagonal (n+1)) = i
    · rcases h with rfl
      simp only [Pi.single_eq_same, tensorLeftIndex]
      change (boundary R R X j.val.1 ((complex R R X).iCycles (j.val.1+1) a)) ⊗ₜ[R]
        ((complex R R Y).iCycles j.val.2 b) = 0
      have ha := CategoryTheory.congr_fun
        ((complex R R X).iCycles_d (j.val.1+1) j.val.1) a
      change boundary R R X j.val.1 ((complex R R X).iCycles (j.val.1+1) a) = 0 at ha
      rw [ha, TensorProduct.zero_tmul]
    · simp only [Pi.single_eq_of_ne h, map_zero]
  have hr : rightBoundary R X Y j.val.1 j.val.2
      (Pi.single (M := fun k : Diagonal (n+1) => Summand R X Y k.val.1 k.val.2) i ((complex R R X).iCycles i.val.1 a ⊗ₜ[R] (complex R R Y).iCycles i.val.2 b)
        (tensorRightIndex j)) = 0 := by
    by_cases h : (tensorRightIndex j : Diagonal (n+1)) = i
    · rcases h with rfl
      simp only [Pi.single_eq_same, tensorRightIndex]
      change ((complex R R X).iCycles j.val.1 a) ⊗ₜ[R]
        (boundary R R Y j.val.2 ((complex R R Y).iCycles (j.val.2+1) b)) = 0
      have hb := CategoryTheory.congr_fun
        ((complex R R Y).iCycles_d (j.val.2+1) j.val.2) b
      change boundary R R Y j.val.2 ((complex R R Y).iCycles (j.val.2+1) b) = 0 at hb
      rw [hb, TensorProduct.tmul_zero]
    · simp only [Pi.single_eq_of_ne h, map_zero]
  rw [hl, hr, smul_zero, add_zero]

/-- An elementary tensor of singular cycles is a cycle in the finite-diagonal total complex. -/
theorem pureTensor_cycle_at {X Y : TopCat.{u}} (n : ℕ) (i : Diagonal n)
    (a : (complex R R X).cycles i.val.1) (b : (complex R R Y).cycles i.val.2) :
    (tensorComplex R X Y).d n (n-1)
      (LinearMap.single R (fun j : Diagonal n => Summand R X Y j.val.1 j.val.2)
        i ((complex R R X).iCycles i.val.1 a ⊗ₜ[R] (complex R R Y).iCycles i.val.2 b)) = 0 := by
  cases n with
  | zero =>
    rw [(P202.ShuffleBoundary.ordinary_boundary_zero R X Y 0).1]
    rfl
  | succ n =>
    rw [show n+1-1=n by omega]
    have hh : (tensorComplex R X Y).d (n+1) n = ModuleCat.ofHom (totalBoundary R X Y n) := by
      dsimp only [tensorComplex]
      exact ChainComplex.of_d _ _ _
    rw [hh]
    change (ModuleCat.ofHom (totalBoundary R X Y n)).hom _ = 0
    exact pureTensor_totalBoundary R n i a b

/-- The elementary cycle formula in its natural sum degree. -/
theorem pureTensor_cycle {X Y : TopCat.{u}} (p q : ℕ)
    (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q) :
    (tensorComplex R X Y).d (p+q) (p+q-1)
      (LinearMap.single R (fun i : Diagonal (p+q) => Summand R X Y i.val.1 i.val.2)
        ⟨(p,q),rfl⟩ ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b)) = 0 :=
  pureTensor_cycle_at R (p+q) ⟨(p,q),rfl⟩ a b

/-- The finite-diagonal total cycle represented by the elementary tensor. -/
def pureTensorCycle {X Y : TopCat.{u}} (p q : ℕ)
    (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q) :
    (tensorComplex R X Y).cycles (p+q) :=
  (tensorComplex R X Y).cyclesMk
    (LinearMap.single R (fun i : Diagonal (p+q) => Summand R X Y i.val.1 i.val.2)
      ⟨(p,q),rfl⟩ ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b))
    (p+q-1) (by
      cases hn : p+q with
      | zero => exact (ComplexShape.down ℕ).next_eq_self' 0 (by intro j; simp [ComplexShape.down_Rel])
      | succ n => exact (ComplexShape.down ℕ).next_eq' (by simp [ComplexShape.down_Rel]))
      (pureTensor_cycle R p q a b)

@[simp] theorem pureTensorCycle_val {X Y : TopCat.{u}} (p q : ℕ)
    (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q) :
    (tensorComplex R X Y).iCycles (p+q) (pureTensorCycle R p q a b) =
      LinearMap.single R (fun i : Diagonal (p+q) => Summand R X Y i.val.1 i.val.2)
        ⟨(p,q),rfl⟩ ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b) := by
  change ((tensorComplex R X Y).iCycles (p+q)).hom _ = _
  have h := (tensorComplex R X Y).i_cyclesMk
    (LinearMap.single R (fun i : Diagonal (p+q) => Summand R X Y i.val.1 i.val.2)
      ⟨(p,q),rfl⟩ ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b))
    (p+q-1) (by
      cases hn : p+q with
      | zero => exact (ComplexShape.down ℕ).next_eq_self' 0 (by intro j; simp [ComplexShape.down_Rel])
      | succ n => exact (ComplexShape.down ℕ).next_eq' (by simp [ComplexShape.down_Rel]))
    (pureTensor_cycle R p q a b)
  simpa only [ModuleCat.forget₂_map, ModuleCat.forget₂_obj,
    ConcreteCategory.hom, ConcreteCategory.ofHom, AddCommGrpCat.ofHom, AddMonoidHom.coe_ofClass, LinearMap.toAddMonoidHom, LinearMap.toAddMonoidHom_coe, LinearMap.coe_toAddHom, pureTensorCycle] using h

/-- The singular external product evaluates on matching elementary product cycles as the product of the two evaluations. -/
theorem externalCup_shuffle_cycles {X Y : TopCat.{u}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q)
    (ha : delta R X p a = 0) (hb : delta R Y q b = 0)
    (z : (complex R R X).cycles p) (w : (complex R R Y).cycles q) :
    externalCup R a b (shuffleComponent R X Y p q
      ((complex R R X).iCycles p z ⊗ₜ[R] (complex R R Y).iCycles q w)) =
      a ((complex R R X).iCycles p z) * b ((complex R R Y).iCycles q w) := by
  have h := externalCup_shuffle_totalCycle R a b ha hb (pureTensorCycle R p q z w)
  rw [pureTensorCycle_val, P202.TopologicalKunneth.shuffle_single] at h
  exact h.trans (by simp [externalTotalPairing, P202.CupProduct.tensorPairing_tmul])

/-- The same elementary total cycle placed in any propositionally equal total degree. -/
def pureTensorCycleAt {X Y : TopCat.{u}} (p q n : ℕ) (h : p+q=n)
    (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q) :
    (tensorComplex R X Y).cycles n := h ▸ pureTensorCycle R p q a b

@[simp] theorem pureTensorCycleAt_val {X Y : TopCat.{u}} (p q n : ℕ) (h : p+q=n)
    (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q) :
    (tensorComplex R X Y).iCycles n (pureTensorCycleAt R p q n h a b) =
      LinearMap.single R (fun i : Diagonal n => Summand R X Y i.val.1 i.val.2)
        ⟨(p,q),h⟩ ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b) := by
  subst n
  exact pureTensorCycle_val R p q a b

/-- Every bidegree other than the degrees of the two cocycles evaluates to zero. -/
theorem externalCup_shuffle_cycles_offDiagonal {X Y : TopCat.{u}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q)
    (ha : delta R X p a = 0) (hb : delta R Y q b = 0)
    (i : Diagonal (p+q)) (hi : i ≠ ⟨(p,q),rfl⟩)
    (z : (complex R R X).cycles i.val.1) (w : (complex R R Y).cycles i.val.2) :
    externalCup R a b (shuffle R X Y (p+q)
      (LinearMap.single R (fun j : Diagonal (p+q) => Summand R X Y j.val.1 j.val.2)
        i ((complex R R X).iCycles i.val.1 z ⊗ₜ[R] (complex R R Y).iCycles i.val.2 w))) = 0 := by
  classical
  have h := externalCup_shuffle_totalCycle R a b ha hb
    (pureTensorCycleAt R i.val.1 i.val.2 (p+q) i.property z w)
  rw [pureTensorCycleAt_val] at h
  change externalCup R a b (shuffle R X Y (p+q)
    (LinearMap.single R (fun j : Diagonal (p+q) => Summand R X Y j.val.1 j.val.2)
      i ((complex R R X).iCycles i.val.1 z ⊗ₜ[R] (complex R R Y).iCycles i.val.2 w))) =
        externalTotalPairing R a b _ at h
  rw [h]
  simp only [externalTotalPairing, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.single_apply, Pi.single_eq_of_ne hi.symm, map_zero]

end PureCyclePairing

section ExternalAlgebra
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CupProduct P202Specs.ShuffleModel
variable (R : Type v) [CommRing R]

/-- The specified singular exterior product of cohomology classes has the
literal exterior cup of the two supplied ordinary cocycles as a representative. -/
theorem externalCup_represents {X Y : TopCat.{u}} (p q : ℕ)
    (U : CohomologyRing R (productSpace X Y))
    (a : (P202Specs.CohomologyPairs.ordinaryCochains R R X).cycles (p : ℤ))
    (b : (P202Specs.CohomologyPairs.ordinaryCochains R R Y).cycles (q : ℤ)) :
    ∃ c : (P202Specs.CohomologyPairs.ordinaryCochains R R (productSpace X Y)).cycles ((p+q : ℕ) : ℤ),
      cocycleValue R (productSpace X Y) (p+q) c =
        externalCup R (cocycleValue R X p a) (cocycleValue R Y q b) ∧
      U.product p q
        (hPullback R (firstProjection X Y) p ((P202Specs.CohomologyPairs.ordinaryCochains R R X).homologyπ (p : ℤ) a))
        (hPullback R (secondProjection X Y) q ((P202Specs.CohomologyPairs.ordinaryCochains R R Y).homologyπ (q : ℤ) b)) =
          (P202Specs.CohomologyPairs.ordinaryCochains R R (productSpace X Y)).homologyπ ((p+q : ℕ) : ℤ) c := by
  obtain ⟨c, hc, hπ⟩ := U.represents p q
    (cyclesMap ((P202Specs.CohomologyPairs.ordinaryCochainFunctor R R).map (firstProjection X Y).op) (p : ℤ) a)
    (cyclesMap ((P202Specs.CohomologyPairs.ordinaryCochainFunctor R R).map (secondProjection X Y).op) (q : ℤ) b)
  refine ⟨c, ?_, ?_⟩
  · simpa only [externalCup, P202.CupProduct.cocycleValue_pullback] using hc
  · rw [P202.CupProduct.hPullback_homologyπ, P202.CupProduct.hPullback_homologyπ]
    exact hπ

/-- The shuffle formula on cycle representatives makes the induced homology
external product independent of the choice of its packaging. -/
theorem externalProduct_map_unique
    (e f : P202Specs.EilenbergZilber.ExternalProduct.{v,u} R)
    (X Y : TopCat.{u}) (p q : ℕ) : e.map X Y p q = f.map X Y p q := by
  apply TensorProduct.ext'
  intro x y
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective ((complex R R X).homologyπ p)).mp inferInstance x
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective ((complex R R Y).homologyπ q)).mp inferInstance y
  obtain ⟨z, hz, he⟩ := e.represents X Y p q a b
  obtain ⟨w, hw, hf⟩ := f.represents X Y p q a b
  have hzw : z = w := (ModuleCat.mono_iff_injective
    ((complex R R (productSpace X Y)).iCycles (p+q))).mp inferInstance (hz.trans hw.symm)
  rw [he, hf, hzw]

end ExternalAlgebra

section FieldExternal
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.EilenbergZilber P202Specs.TopologicalKunneth
variable (R : Type v) [Field R]

/-- Product homology over a field is spanned by the literal shuffle external
products, with no finite rank assumption and with every choice of external
product satisfying the specified representative formula. -/
theorem fieldExternalFunctional_ext (e : ExternalProduct.{v,u} R)
    (X Y : TopCat.{u}) (n : ℕ)
    (f g : H R (productSpace X Y) n →ₗ[R] R)
    (h : ∀ (i : Diagonal n) (x : H R X i.val.1) (y : H R Y i.val.2),
      f (i.property ▸ ordinaryExternal R e X Y i.val.1 i.val.2 (x ⊗ₜ[R] y)) =
      g (i.property ▸ ordinaryExternal R e X Y i.val.1 i.val.2 (x ⊗ₜ[R] y))) : f = g := by
  obtain ⟨P, T, ⟨s⟩, _⟩ := P202.TopologicalKunneth.kunneth.{v,u} R
  apply fieldProductFunctional_ext R P T s X Y n f g
  intro i x y
  obtain ⟨⟨p,q⟩,hi⟩ := i
  subst n
  rw [s.α_external]
  have he : ordinaryExternal R s.external X Y p q = ordinaryExternal R e X Y p q := by
    unfold ordinaryExternal
    rw [externalProduct_map_unique R s.external e]
  rw [he]
  exact h ⟨(p,q),rfl⟩ x y

end FieldExternal

section ShuffleDifferentials
open P202Specs.SmoothSingularComparison P202Specs.SingularChains P202Specs.ShuffleModel

/-- Ordered affine simplex maps in the actual corner coordinates of P104. -/
def cornerReparametrization {r k : ℕ} (θ : Fin (r+1) → Fin (k+1)) :
    CornerSimplex r → CornerSimplex k :=
  fun x => toCorner k ((toBarycentric r x).map θ)

/-- The globally affine ambient extension of the same ordered simplex map. -/
def ambientReparametrization {r k : ℕ} (θ : Fin (r+1) → Fin (k+1)) :
    ModelData.Euclidean r → ModelData.Euclidean k :=
  fun y j => ambientMap θ (CornerData.simplexBarycentric y) j.succ

theorem cornerReparametrization_val {r k : ℕ} (θ : Fin (r+1) → Fin (k+1))
    (x : CornerSimplex r) :
    (cornerReparametrization θ x).val = ambientReparametrization θ x.val := by
  funext j
  change weights ((toBarycentric r x).map θ) j.succ =
    ambientMap θ (CornerData.simplexBarycentric x.val) j.succ
  rw [← P202.ShuffleModel.ambientMap_weights]
  rfl

theorem ambientReparametrization_smooth {r k : ℕ} (θ : Fin (r+1) → Fin (k+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (ambientReparametrization θ) := by
  have h := (P202.ShuffleModel.ambientMap_smooth θ).comp
    (CornerExamples.contDiff_barycentric r)
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_apply ℝ (fun _ : Fin (k+1) => ℝ) j.succ).comp h

/-- The actual ordinary simplex produced by affine precomposition. -/
def reparametrizedSimplex {r k : ℕ} {X : TopCat.{u}}
    (θ : Fin (r+1) → Fin (k+1)) (σ : Simplex X k) : Simplex X r :=
  (simplexEquiv X r).symm ((simplexEquiv X k σ).comp
    ⟨fun z => z.map θ, Convexity.StdSimplex.continuous_map ℝ θ⟩)

variable {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
  (T : AtlasData.SmoothManifold m b N)

theorem reparametrizedSimplex_smooth {r k : ℕ} (θ : Fin (r+1) → Fin (k+1))
    (σ : SmoothSimplex S k) : IsSmoothSimplex S r (reparametrizedSimplex θ σ.val) := by
  have h := SmoothSingular.smooth_precompose σ.property
    (cornerReparametrization θ) (ambientReparametrization θ)
    (ambientReparametrization_smooth θ) (cornerReparametrization_val θ)
  unfold IsSmoothSimplex
  convert h using 1
  funext x
  simp [reparametrizedSimplex, cornerReparametrization, Function.comp_def]

/-- Every ordered affine map gives a smooth simplex, with all faces and corners retained. -/
def reparametrizedSmoothSimplex {r k : ℕ} (θ : Fin (r+1) → Fin (k+1))
    (σ : SmoothSimplex S k) : SmoothSimplex S r :=
  ⟨reparametrizedSimplex θ σ.val, reparametrizedSimplex_smooth S θ σ⟩

/-- This identity identifies the entire P104 singular simplex, including its
intrinsic corner smoothness predicate, rather than only its point values. -/
theorem p104Simplex_reparametrized {r k : ℕ} (θ : Fin (r+1) → Fin (k+1))
    (σ : SmoothSimplex S k) :
    p104Simplex S (reparametrizedSmoothSimplex S θ σ) =
      ⟨(p104Simplex S σ).val ∘ cornerReparametrization θ,
        SmoothSingular.smooth_precompose σ.property
          (cornerReparametrization θ) (ambientReparametrization θ)
          (ambientReparametrization_smooth θ) (cornerReparametrization_val θ)⟩ := by
  apply Subtype.ext
  funext x
  simp [p104Simplex, reparametrizedSmoothSimplex, reparametrizedSimplex,
    cornerReparametrization, Function.comp_def]

/-- The genuine intrinsic pullback on affine cells satisfies the ambient chain
rule in every degree, with no restriction on manifold boundary points. -/
theorem coordinatePullback_reparametrized (C : CotangentBundle S)
    {r k l : ℕ} (θ : Fin (r+1) → Fin (k+1)) (ω : Field S l)
    (σ : SmoothSimplex S k) (x : CornerSimplex r) :
    SimplexPullbackIntegral.coordinatePullback (C := C) ω
        (p104Simplex S (reparametrizedSmoothSimplex S θ σ)) x.val =
      (SimplexPullbackIntegral.coordinatePullback (C := C) ω (p104Simplex S σ)
        (cornerReparametrization θ x).val).compContinuousLinearMap
          (fderiv ℝ (ambientReparametrization θ) x.val) := by
  rw [p104Simplex_reparametrized]
  exact SimplexPullbackIntegral.coordinatePullback_precompose ω (p104Simplex S σ)
    (cornerReparametrization θ) (ambientReparametrization θ)
    (ambientReparametrization_smooth θ) (cornerReparametrization_val θ) _ x

/-- Each factor projection of the actual shuffle is exactly ordered affine
precomposition of that factor; this connects the P202 cells to the P104 chain rule. -/
theorem shuffle_first_reparametrized {p q : ℕ} (s : LatticePath p q)
    (σ : Simplex (TopCat.of M) p) (τ : Simplex (TopCat.of N) q) :
    P202Specs.AlexanderWhitney.postSimplex
      (P202Specs.AlexanderWhitney.firstProjection (TopCat.of M) (TopCat.of N)) (p+q)
      (shuffleSimplex s σ τ) = reparametrizedSimplex s.horizontal σ := by
  apply (simplexEquiv (TopCat.of M) (p+q)).injective
  unfold P202Specs.AlexanderWhitney.postSimplex
  rw [P202.SingularChains.simplexEquiv_postcomp]
  ext z
  simp [shuffleSimplex, reparametrizedSimplex, parametrization,
    P202Specs.AlexanderWhitney.firstProjection]

theorem shuffle_second_reparametrized {p q : ℕ} (s : LatticePath p q)
    (σ : Simplex (TopCat.of M) p) (τ : Simplex (TopCat.of N) q) :
    P202Specs.AlexanderWhitney.postSimplex
      (P202Specs.AlexanderWhitney.secondProjection (TopCat.of M) (TopCat.of N)) (p+q)
      (shuffleSimplex s σ τ) = reparametrizedSimplex s.vertical τ := by
  apply (simplexEquiv (TopCat.of N) (p+q)).injective
  unfold P202Specs.AlexanderWhitney.postSimplex
  rw [P202.SingularChains.simplexEquiv_postcomp]
  ext z
  simp [shuffleSimplex, reparametrizedSimplex, parametrization,
    P202Specs.AlexanderWhitney.secondProjection]

/-- Genuine intrinsic tangent vectors obey the same chain rule. `HEq` merely
records the equality of the base points in the two displayed tangent fibers. -/
theorem simplexDifferential_reparametrized (C : CotangentBundle S)
    {r k : ℕ} (θ : Fin (r+1) → Fin (k+1)) (σ : SmoothSimplex S k)
    (x : CornerSimplex r) (v : ModelData.Euclidean r) :
    HEq (IntegrationCochainData.simplexDifferential S C
      (p104Simplex S (reparametrizedSmoothSimplex S θ σ)) x v)
      (IntegrationCochainData.simplexDifferential S C (p104Simplex S σ)
        (cornerReparametrization θ x) (fderiv ℝ (ambientReparametrization θ) x.val v)) := by
  rw [p104Simplex_reparametrized]
  exact heq_of_eq (SimplexPullbackIntegral.simplexDifferential_precompose (C := C)
    (p104Simplex S σ) (cornerReparametrization θ) (ambientReparametrization θ)
    (ambientReparametrization_smooth θ) (cornerReparametrization_val θ) _ x v)

/-- A shuffle's first factor is a genuine P104-smooth simplex at every corner. -/
theorem shuffle_first_smooth {p q : ℕ} (s : LatticePath p q)
    (σ : SmoothSimplex S p) (τ : Simplex (TopCat.of N) q) :
    IsSmoothSimplex S (p+q) (P202Specs.AlexanderWhitney.postSimplex
      (P202Specs.AlexanderWhitney.firstProjection (TopCat.of M) (TopCat.of N)) (p+q)
      (shuffleSimplex s σ.val τ)) := by
  rw [shuffle_first_reparametrized]
  exact reparametrizedSimplex_smooth S s.horizontal σ

theorem shuffle_second_smooth {p q : ℕ} (s : LatticePath p q)
    (σ : Simplex (TopCat.of M) p) (τ : SmoothSimplex T q) :
    IsSmoothSimplex T (p+q) (P202Specs.AlexanderWhitney.postSimplex
      (P202Specs.AlexanderWhitney.secondProjection (TopCat.of M) (TopCat.of N)) (p+q)
      (shuffleSimplex s σ τ.val)) := by
  rw [shuffle_second_reparametrized]
  exact reparametrizedSimplex_smooth T s.vertical τ

/-- All arbitrary nonsmooth totalization branches disappear on the actual
shuffle simplices, so their integrals are the intrinsic affine pullbacks. -/
theorem externalIntegral_shuffle_simplex (C : CotangentBundle S) (A : CotangentBundle T)
    {p q : ℕ} (ω : Field S p) (η : Field T q) (s : LatticePath p q)
    (σ : SmoothSimplex S p) (τ : SmoothSimplex T q) :
    externalIntegralCochain S T C A ω η (Finsupp.single (shuffleSimplex s σ.val τ.val) 1) =
      productSimplexIntegral S T C A ω η
        (p104Simplex S (reparametrizedSmoothSimplex S s.horizontal σ))
        (p104Simplex T (reparametrizedSmoothSimplex T s.vertical τ)) rfl := by
  simp only [externalIntegralCochain, Finsupp.linearCombination_single, one_smul,
    shuffle_first_reparametrized, shuffle_second_reparametrized]
  rw [dif_pos (reparametrizedSimplex_smooth S s.horizontal σ),
    dif_pos (reparametrizedSimplex_smooth T s.vertical τ)]
  rfl

/-- A basis product integral is exactly the finite signed sum of the intrinsic
P104 affine-cell integrals, with the upstream permutation orientation signs. -/
theorem productShuffleIntegral_basis_sum (C : CotangentBundle S) (A : CotangentBundle T)
    {p q : ℕ} (ω : Field S p) (η : Field T q)
    (σ : SmoothSimplex S p) (τ : SmoothSimplex T q) :
    externalIntegralCochain S T C A ω η
      (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q
        (Finsupp.single σ.val 1 ⊗ₜ[ℝ] Finsupp.single τ.val 1)) =
      ∑ s : LatticePath p q, (s.sign : ℝ) * productSimplexIntegral S T C A ω η
        (p104Simplex S (reparametrizedSmoothSimplex S s.horizontal σ))
        (p104Simplex T (reparametrizedSmoothSimplex T s.vertical τ)) rfl := by
  rw [P202.ShuffleChains.component_formula]
  simp only [mul_one, one_smul, map_sum, map_zsmul, zsmul_eq_mul,
    externalIntegral_shuffle_simplex]

end ShuffleDifferentials

section ExternalEvaluation
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CohomologyPairs P202Specs.CupProduct P202Specs.ShuffleModel
open P202Specs.EilenbergZilber P202Specs.TopologicalKunneth
variable (R : Type v) [CommRing R]

/-- Evaluation is unchanged when a nonnegative cycle class is transported to
ordinary integer-indexed singular homology by the specified extension isomorphism. -/
theorem evaluation_nonnegative_cycles (X : TopCat.{u}) (q : ℕ)
    (c : (ordinaryCochains R R X).cycles (q : ℤ))
    (z : (complex R R X).cycles q) :
    P202Specs.UniversalCoefficients.evaluation R R (ordinaryComplex R R X) (q : ℤ)
      ((ordinaryCochains R R X).homologyπ (q : ℤ) c)
      ((ordinaryHomologyIso R X q).inv ((complex R R X).homologyπ q z)) =
        cocycleValue R X q c ((complex R R X).iCycles q z) := by
  let C := complex R R X
  let hq : (degreeEmbedding 0).f q = (q : ℤ) := by simp [degreeEmbedding]
  let E := C.extendCyclesIso (degreeEmbedding 0) hq
  have hπ := congrArg (fun f => f.hom z)
    (C.homologyπ_extendHomologyIso_inv (degreeEmbedding 0) hq)
  change (ordinaryHomologyIso R X q).inv (C.homologyπ q z) =
    (ordinaryComplex R R X).homologyπ (q : ℤ) (E.inv z) at hπ
  rw [hπ]
  erw [evaluation_cycles]
  have hi := congrArg (fun f => f.hom z)
    (C.extendCyclesIso_inv_iCycles (degreeEmbedding 0) hq)
  change (ordinaryComplex R R X).iCycles (q : ℤ) (E.inv z) =
    (ordinaryNonnegativeIso R R X q).inv (C.iCycles q z) at hi
  rw [hi]
  rfl

/-- The same evaluation formula also permits a propositional change of the
nonnegative degree, as required for the off-diagonal Künneth summands. -/
theorem evaluation_nonnegative_cycles_cast {X : TopCat.{u}} {r s : ℕ} (h : r=s)
    (c : (ordinaryCochains R R X).cycles (s : ℤ))
    (z : (complex R R X).cycles r) :
    P202Specs.UniversalCoefficients.evaluation R R (ordinaryComplex R R X) (s : ℤ)
      ((ordinaryCochains R R X).homologyπ (s : ℤ) c)
      (h ▸ (ordinaryHomologyIso R X r).inv ((complex R R X).homologyπ r z)) =
        cocycleValue R X s c (castChains R h ((complex R R X).iCycles r z)) := by
  subst s
  exact evaluation_nonnegative_cycles R X r c z

/-- The specified ordinary external product class is represented by every
shuffle cycle supplied by the external-product interface. -/
theorem ordinaryExternal_cycles (e : ExternalProduct.{v,u} R)
    (X Y : TopCat.{u}) (p q : ℕ)
    (z : (complex R R X).cycles p) (w : (complex R R Y).cycles q)
    (t : (complex R R (productSpace X Y)).cycles (p+q))
    (ht : e.map X Y p q ((complex R R X).homologyπ p z ⊗ₜ[R]
      (complex R R Y).homologyπ q w) = (complex R R (productSpace X Y)).homologyπ (p+q) t) :
    ordinaryExternal R e X Y p q
      ((ordinaryHomologyIso R X p).inv ((complex R R X).homologyπ p z) ⊗ₜ[R]
        (ordinaryHomologyIso R Y q).inv ((complex R R Y).homologyπ q w)) =
      (ordinaryHomologyIso R (productSpace X Y) (p+q)).inv
        ((complex R R (productSpace X Y)).homologyπ (p+q) t) := by
  unfold ordinaryExternal
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul]
  change (ordinaryHomologyIso R (productSpace X Y) (p+q)).inv
    (e.map X Y p q
      ((ordinaryHomologyIso R X p).hom ((ordinaryHomologyIso R X p).inv
        ((complex R R X).homologyπ p z)) ⊗ₜ[R]
      (ordinaryHomologyIso R Y q).hom ((ordinaryHomologyIso R Y q).inv
        ((complex R R Y).homologyπ q w)))) = _
  rw [ModuleCat.hom_inv_apply, ModuleCat.hom_inv_apply, ht]

/-- The ordinary singular exterior cup evaluates on the matching shuffle
external product as the product of the evaluations of its two representatives. -/
theorem externalCup_class_evaluation {X Y : TopCat.{u}} (p q : ℕ)
    (e : ExternalProduct.{v,u} R) (U : CohomologyRing R (productSpace X Y))
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (b : (ordinaryCochains R R Y).cycles (q : ℤ))
    (z : (complex R R X).cycles p) (w : (complex R R Y).cycles q) :
    P202Specs.UniversalCoefficients.evaluation R R (ordinaryComplex R R (productSpace X Y)) ((p+q : ℕ) : ℤ)
      (U.product p q
        (hPullback R (firstProjection X Y) p ((ordinaryCochains R R X).homologyπ (p : ℤ) a))
        (hPullback R (secondProjection X Y) q ((ordinaryCochains R R Y).homologyπ (q : ℤ) b)))
      (ordinaryExternal R e X Y p q
        ((ordinaryHomologyIso R X p).inv ((complex R R X).homologyπ p z) ⊗ₜ[R]
          (ordinaryHomologyIso R Y q).inv ((complex R R Y).homologyπ q w))) =
      cocycleValue R X p a ((complex R R X).iCycles p z) *
        cocycleValue R Y q b ((complex R R Y).iCycles q w) := by
  obtain ⟨c, hc, hπ⟩ := externalCup_represents R p q U a b
  obtain ⟨t, ht, he⟩ := e.represents X Y p q z w
  rw [hπ, ordinaryExternal_cycles R e X Y p q z w t he,
    evaluation_nonnegative_cycles, hc, ht]
  exact externalCup_shuffle_cycles R _ _
    (P202.CupProduct.cocycleValue_delta R X p a)
    (P202.CupProduct.cocycleValue_delta R Y q b) z w

/-- Exterior cup of degrees p and q evaluates to zero on every other
Künneth bidegree, after the actual ordinary/nonnegative homology transport. -/
theorem externalCup_class_evaluation_offDiagonal {X Y : TopCat.{u}} (p q : ℕ)
    (e : ExternalProduct.{v,u} R) (U : CohomologyRing R (productSpace X Y))
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (b : (ordinaryCochains R R Y).cycles (q : ℤ))
    (i : Diagonal (p+q)) (hi : i ≠ ⟨(p,q),rfl⟩)
    (z : (complex R R X).cycles i.val.1) (w : (complex R R Y).cycles i.val.2) :
    P202Specs.UniversalCoefficients.evaluation R R (ordinaryComplex R R (productSpace X Y)) ((p+q : ℕ) : ℤ)
      (U.product p q
        (hPullback R (firstProjection X Y) p ((ordinaryCochains R R X).homologyπ (p : ℤ) a))
        (hPullback R (secondProjection X Y) q ((ordinaryCochains R R Y).homologyπ (q : ℤ) b)))
      (i.property ▸ ordinaryExternal R e X Y i.val.1 i.val.2
        ((ordinaryHomologyIso R X i.val.1).inv ((complex R R X).homologyπ i.val.1 z) ⊗ₜ[R]
          (ordinaryHomologyIso R Y i.val.2).inv ((complex R R Y).homologyπ i.val.2 w))) = 0 := by
  obtain ⟨c, hc, hπ⟩ := externalCup_represents R p q U a b
  obtain ⟨t, ht, he⟩ := e.represents X Y i.val.1 i.val.2 z w
  rw [hπ, ordinaryExternal_cycles R e X Y i.val.1 i.val.2 z w t he,
    evaluation_nonnegative_cycles_cast, hc, ht]
  rw [← P202.ShuffleBoundary.shuffle_single]
  exact externalCup_shuffle_cycles_offDiagonal R _ _
    (P202.CupProduct.cocycleValue_delta R X p a)
    (P202.CupProduct.cocycleValue_delta R Y q b) i hi z w

/-- Real cohomology of a product is detected by all shuffle product classes,
without a finiteness assumption on either space or any homology group. -/
theorem realProductClass_ext (e : ExternalProduct.{0,u} ℝ)
    (X Y : TopCat.{u}) (n : ℕ)
    {x y : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ (productSpace X Y) (n : ℤ)}
    (h : ∀ (i : Diagonal n) (z : P202Specs.TopologicalKunneth.H ℝ X i.val.1)
      (w : P202Specs.TopologicalKunneth.H ℝ Y i.val.2),
      P202Specs.UniversalCoefficients.evaluation ℝ ℝ (ordinaryComplex ℝ ℝ (productSpace X Y)) (n : ℤ) x
        (i.property ▸ ordinaryExternal ℝ e X Y i.val.1 i.val.2 (z ⊗ₜ[ℝ] w)) =
      P202Specs.UniversalCoefficients.evaluation ℝ ℝ (ordinaryComplex ℝ ℝ (productSpace X Y)) (n : ℤ) y
        (i.property ▸ ordinaryExternal ℝ e X Y i.val.1 i.val.2 (z ⊗ₜ[ℝ] w))) : x=y := by
  apply realClass_ext (productSpace X Y) n
  intro z
  exact LinearMap.congr_fun (fieldExternalFunctional_ext ℝ e X Y n
    (P202Specs.UniversalCoefficients.evaluation ℝ ℝ (ordinaryComplex ℝ ℝ (productSpace X Y)) (n : ℤ) x)
    (P202Specs.UniversalCoefficients.evaluation ℝ ℝ (ordinaryComplex ℝ ℝ (productSpace X Y)) (n : ℤ) y) h) z

end ExternalEvaluation

theorem exteriorPairing_natural {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (k : ℕ) (L : V →ₗ[ℝ] W) :
    (exteriorPower.pairingDual ℝ V k).comp (exteriorPower.map k L.dualMap) =
      (exteriorPower.map k L).dualMap.comp (exteriorPower.pairingDual ℝ W k) := by
  apply exteriorPower.linearMap_ext (R := ℝ) (M := Module.Dual ℝ W) (n := k)
  apply AlternatingMap.ext
  intro α
  apply exteriorPower.linearMap_ext (R := ℝ) (M := V) (n := k)
  apply AlternatingMap.ext
  intro z
  change exteriorPower.pairingDual ℝ V k
      (exteriorPower.map k L.dualMap (exteriorPower.ιMulti ℝ k α)) (exteriorPower.ιMulti ℝ k z) =
    exteriorPower.pairingDual ℝ W k (exteriorPower.ιMulti ℝ k α)
      (exteriorPower.map k L (exteriorPower.ιMulti ℝ k z))
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti,
    exteriorPower.pairingDual_ιMulti_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  rfl

theorem evaluate_exteriorMap {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (k : ℕ) (L : V →ₗ[ℝ] W) (ω : Fiber W k) (z : Fin k → V) :
    evaluate V k (exteriorPower.map k L.dualMap ω) z =
      evaluate W k ω (fun i => L (z i)) := by
  rw [FormPullbackResults.evaluate_eq_pairing, FormPullbackResults.evaluate_eq_pairing]
  change ((exteriorPower.pairingDual ℝ V k).comp (exteriorPower.map k L.dualMap)) ω
    (exteriorPower.ιMulti ℝ k z) = _
  rw [exteriorPairing_natural]
  change exteriorPower.pairingDual ℝ W k ω
    (exteriorPower.map k L (exteriorPower.ιMulti ℝ k z)) = _
  rw [exteriorPower.map_apply_ιMulti]
  rfl


theorem productSimplexIntegral_diagonal (C : CotangentBundle S)
    {p q : ℕ} (ω : Field S p) (η : Field S q)
    (σ : SmoothSingularData.SingularSimplex S (p+q)) :
    productSimplexIntegral S S C C ω η σ σ rfl =
      IntegrationCochainData.simplexIntegral S C (fieldWedge ω η) σ := by
  unfold productSimplexIntegral IntegrationCochainData.simplexIntegral
  congr 1
  funext y
  simp only [IntegrationCochainData.ambientPullbackCoefficient]
  split_ifs with hy
  · simp only [Fin.cast_refl]
    rw [← ExteriorAlgebraResults.map_wedge
      (IntegrationCochainData.simplexDifferential S C σ ⟨y,hy⟩).dualMap
      (ω (σ.val ⟨y,hy⟩)) (η (σ.val ⟨y,hy⟩))]
    simp only [IntegrationCochainData.pullbackCoefficient, fieldWedge, id_eq]
    have hh := evaluate_exteriorMap
      (V := ModelData.Euclidean (p+q)) (W := TangentData.TangentSpace S (σ.val ⟨y,hy⟩)) (p+q)
      (IntegrationCochainData.simplexDifferential S C σ ⟨y,hy⟩)
      (fieldWedge ω η (σ.val ⟨y,hy⟩)) (fun (i : Fin (p+q)) => Pi.single i (1 : ℝ))
    simpa only [fieldWedge] using hh
  · rfl


/-- On each genuine smooth singular generator, ordinary diagonal pullback
of external integration is literal integration of the intrinsic wedge. -/
theorem externalIntegralCochain_diagonal_single (C : CotangentBundle S)
    {p q : ℕ} (ω : Field S p) (η : Field S q) (σ : SmoothSimplex S (p+q)) :
    externalIntegralCochain S S C C ω η
      (((P202Specs.SingularChains.chainMap ℝ ℝ
        (P202Specs.CupProduct.diagonalMap (TopCat.of M))).f (p+q)).hom
          (Finsupp.single σ.val 1)) =
      integralCochain S C (fieldWedge ω η) (Finsupp.single σ.val 1) := by
  classical
  have h₁ : P202Specs.AlexanderWhitney.postSimplex
      (P202Specs.AlexanderWhitney.firstProjection (TopCat.of M) (TopCat.of M)) (p+q)
      (P202Specs.AlexanderWhitney.postSimplex
        (P202Specs.CupProduct.diagonalMap (TopCat.of M)) (p+q) σ.val) = σ.val := by
    apply (P202Specs.SingularChains.simplexEquiv (TopCat.of M) (p+q)).injective
    ext x
    rfl
  have h₂ : P202Specs.AlexanderWhitney.postSimplex
      (P202Specs.AlexanderWhitney.secondProjection (TopCat.of M) (TopCat.of M)) (p+q)
      (P202Specs.AlexanderWhitney.postSimplex
        (P202Specs.CupProduct.diagonalMap (TopCat.of M)) (p+q) σ.val) = σ.val := by
    apply (P202Specs.SingularChains.simplexEquiv (TopCat.of M) (p+q)).injective
    ext x
    rfl
  rw [P202.SingularChains.chainMap_single]
  change externalIntegralCochain S S C C ω η
    (Finsupp.single (P202Specs.AlexanderWhitney.postSimplex
      (P202Specs.CupProduct.diagonalMap (TopCat.of M)) (p+q) σ.val) 1) = _
  simp only [externalIntegralCochain, integralCochain, Finsupp.linearCombination_single, one_smul]
  rw [h₁, h₂]
  simp only [σ.property, dite_true]
  exact productSimplexIntegral_diagonal S C ω η (p104Simplex S σ)


/-- The diagonal identity holds on every finite smooth chain, hence also
on all smooth cycles, without an assertion about totalized nonsmooth values. -/
theorem externalIntegralCochain_diagonal (C : CotangentBundle S)
    {p q : ℕ} (ω : Field S p) (η : Field S q)
    (z : P202Specs.SmoothSingularComparison.smoothModule S (p+q)) :
    externalIntegralCochain S S C C ω η
      (((P202Specs.SingularChains.chainMap ℝ ℝ
        (P202Specs.CupProduct.diagonalMap (TopCat.of M))).f (p+q)).hom z.val) =
      integralCochain S C (fieldWedge ω η) z.val := by
  classical
  have hz := (Finsupp.mem_supported ℝ z.val).mp z.property
  have he : ∀ σ ∈ z.val.support,
      externalIntegralCochain S S C C ω η
        (((P202Specs.SingularChains.chainMap ℝ ℝ
          (P202Specs.CupProduct.diagonalMap (TopCat.of M))).f (p+q)).hom
            (Finsupp.single σ (z.val σ))) =
        integralCochain S C (fieldWedge ω η) (Finsupp.single σ (z.val σ)) := by
    intro σ hσ
    have hs : Finsupp.single σ (z.val σ) = (z.val σ) • Finsupp.single σ 1 := by simp
    rw [hs, map_smul, map_smul, map_smul]
    rw [externalIntegralCochain_diagonal_single S C ω η ⟨σ, hz hσ⟩]
  have hsum : (∑ σ ∈ z.val.support, Finsupp.single σ (z.val σ)) = z.val :=
    z.val.sum_single
  calc
    _ = externalIntegralCochain S S C C ω η
        (((P202Specs.SingularChains.chainMap ℝ ℝ
          (P202Specs.CupProduct.diagonalMap (TopCat.of M))).f (p+q)).hom
            (∑ σ ∈ z.val.support, Finsupp.single σ (z.val σ))) := by rw [hsum]
    _ = ∑ σ ∈ z.val.support,
        externalIntegralCochain S S C C ω η
          (((P202Specs.SingularChains.chainMap ℝ ℝ
            (P202Specs.CupProduct.diagonalMap (TopCat.of M))).f (p+q)).hom
              (Finsupp.single σ (z.val σ))) := by simp only [map_sum]
    _ = ∑ σ ∈ z.val.support,
        integralCochain S C (fieldWedge ω η) (Finsupp.single σ (z.val σ)) :=
      Finset.sum_congr rfl he
    _ = integralCochain S C (fieldWedge ω η) z.val := by
      rw [← map_sum, hsum]


/-- The smooth cochain complex has no incoming coboundaries in degree zero. -/
theorem smoothCochains_homologyπ_zero_isIso :
    IsIso ((P202Specs.SmoothSingularComparison.smoothCochains S).homologyπ 0) := by
  have hz : CategoryTheory.Limits.IsZero
      ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).X (-1)) := by
    apply (P202Specs.SmoothSingularComparison.smoothComplex S).isZero_extend_X
      (P202Specs.SingularChains.degreeEmbedding 0) (-1)
    intro q hq
    change (0 : ℤ) + q = -1 at hq
    omega
  have hz' : CategoryTheory.Limits.IsZero
      ((P202Specs.SmoothSingularComparison.smoothCochains S).X (-1)) :=
    P202.CohomologyPairs.dual_isZero ℝ ℝ _ hz
  apply (P202Specs.SmoothSingularComparison.smoothCochains S).isIso_homologyπ (-1) 0
    (((ComplexShape.down ℤ).symm).prev_eq' (by simp))
  exact hz'.eq_of_src _ _

/-- In degree zero every ordinary representative of an integration class
already has the exact integral values on smooth points. -/
theorem integrationClass_zero_cocycleValue (C : CotangentBundle S)
    (ω : Field S 0)
    (a : (P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).cycles 0)
    (ha : IsIntegrationClass S C ω
      ((P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).homologyπ 0 a))
    (σ : SmoothSimplex S 0) :
    P202Specs.CupProduct.cocycleValue ℝ (TopCat.of M) 0 a (Finsupp.single σ.val 1) =
      IntegrationCochainData.simplexIntegral S C ω (p104Simplex S σ) := by
  obtain ⟨c, hc, hcv⟩ := ha
  letI := smoothCochains_homologyπ_zero_isIso S
  have he : cyclesMap (P202Specs.SmoothSingularComparison.restriction S) 0 a = c := by
    apply (ModuleCat.mono_iff_injective
      ((P202Specs.SmoothSingularComparison.smoothCochains S).homologyπ 0)).mp inferInstance
    have hn := congrArg (fun t => t a)
      (homologyπ_naturality (P202Specs.SmoothSingularComparison.restriction S) 0)
    exact hn.symm.trans hc.symm
  have hv := hcv σ
  rw [← he] at hv
  have hi := congrArg (fun t => t a)
    (cyclesMap_i (P202Specs.SmoothSingularComparison.restriction S) 0)
  change (P202Specs.SmoothSingularComparison.smoothCochains S).iCycles 0
      (cyclesMap (P202Specs.SmoothSingularComparison.restriction S) 0 a) =
    (P202Specs.SmoothSingularComparison.restriction S).f 0
      ((P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).iCycles 0 a) at hi
  erw [hi, evaluateRestriction] at hv
  exact hv

/-- Literal zero-dimensional simplex integration preserves multiplication of
all intrinsic scalar forms, before passing to cohomology. -/
theorem simplexIntegral_wedge_zero (C : CotangentBundle S)
    (ω η : Field S 0) (σ : SmoothSingularData.SingularSimplex S 0) :
    IntegrationCochainData.simplexIntegral S C (fieldWedge ω η) σ =
      IntegrationCochainData.simplexIntegral S C ω σ *
      IntegrationCochainData.simplexIntegral S C η σ := by
  let x : SmoothSingularData.Simplex 0 := ⟨0, by
    constructor
    · intro i; exact Fin.elim0 i
    · simp⟩
  rw [SmoothManifolds.IntegrationCochain.simplexIntegral_zero _ _ x,
    SmoothManifolds.IntegrationCochain.simplexIntegral_zero _ _ x,
    SmoothManifolds.IntegrationCochain.simplexIntegral_zero _ _ x]
  have h := evaluate_wedge_zero (TangentData.TangentSpace S (σ.val x))
    (ω (σ.val x)) (η (σ.val x)) (fun i => Fin.elim0 i)
  simpa only [SimplexPullbackIntegral.evaluate_zero, fieldWedge] using h


section SmoothProductDetection
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CohomologyPairs P202Specs.EilenbergZilber P202Specs.TopologicalKunneth

/-- The actual smooth inclusion is surjective on real homology whenever
restriction is injective on cohomology. This uses unrestricted algebraic duals
and does not assume a finite-dimensional homology or cohomology group. -/
theorem smoothInclusion_homology_surjective {q : ℕ}
    [IsIso (homologyMap (P202Specs.SmoothSingularComparison.restriction S) (q : ℤ))] :
    Function.Surjective
      (homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion S) (q : ℤ)) := by
  let C := ordinaryComplex ℝ ℝ (TopCat.of M)
  let D := P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S
  let f : D.homology (q : ℤ) →ₗ[ℝ] C.homology (q : ℤ) :=
    (homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion S) (q : ℤ)).hom
  change Function.Surjective f
  apply (LinearMap.dualMap_injective_iff (f := f)).mp
  intro φ ψ h
  obtain ⟨x, hx⟩ := (P202.UniversalCoefficients.evaluation_bijective ℝ C (q : ℤ)).surjective φ
  obtain ⟨y, hy⟩ := (P202.UniversalCoefficients.evaluation_bijective ℝ C (q : ℤ)).surjective ψ
  have hxy : x = y := by
    apply realClass_ext_smoothCycles S
    intro z
    have hv := LinearMap.congr_fun h (D.homologyπ (q : ℤ) z)
    change φ (f (D.homologyπ (q : ℤ) z)) = ψ (f (D.homologyπ (q : ℤ) z)) at hv
    rw [← hx, ← hy] at hv
    exact hv
  rw [← hx, ← hy, hxy]

/-- Every ordinary real class has a literal finite smooth cycle representative,
as a consequence of the actual smooth cohomology restriction isomorphism. -/
theorem smoothCycle_representative {q : ℕ}
    [IsIso (homologyMap (P202Specs.SmoothSingularComparison.restriction S) (q : ℤ))]
    (x : P202Specs.SingularChains.homology ℝ ℝ (TopCat.of M) (q : ℤ)) :
    ∃ z : (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).cycles (q : ℤ),
      homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion S) (q : ℤ)
        ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (q : ℤ) z) = x := by
  obtain ⟨a, rfl⟩ := smoothInclusion_homology_surjective S x
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (q : ℤ))).mp inferInstance a
  exact ⟨z, rfl⟩

/-- Real cohomology on a product of smooth manifolds is detected on shuffle
external products of finite smooth cycles of every bidegree. The product
space need not itself be a manifold without corners. -/
theorem realProductClass_ext_smoothProducts
    {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : AtlasData.SmoothManifold m b N)
    (hS : ∀ q : ℕ, IsIso (homologyMap (P202Specs.SmoothSingularComparison.restriction S) (q : ℤ)))
    (hT : ∀ q : ℕ, IsIso (homologyMap (P202Specs.SmoothSingularComparison.restriction T) (q : ℤ)))
    (e : ExternalProduct.{0,u} ℝ) (r : ℕ)
    {x y : ordinaryCohomology ℝ ℝ (productSpace (TopCat.of M) (TopCat.of N)) (r : ℤ)}
    (h : ∀ (i : Diagonal r)
      (z : (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).cycles (i.val.1 : ℤ))
      (w : (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex T).cycles (i.val.2 : ℤ)),
      P202Specs.UniversalCoefficients.evaluation ℝ ℝ
        (ordinaryComplex ℝ ℝ (productSpace (TopCat.of M) (TopCat.of N))) (r : ℤ) x
        (i.property ▸ ordinaryExternal ℝ e (TopCat.of M) (TopCat.of N) i.val.1 i.val.2
          (homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion S) (i.val.1 : ℤ)
            ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (i.val.1 : ℤ) z) ⊗ₜ[ℝ]
           homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion T) (i.val.2 : ℤ)
            ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex T).homologyπ (i.val.2 : ℤ) w))) =
      P202Specs.UniversalCoefficients.evaluation ℝ ℝ
        (ordinaryComplex ℝ ℝ (productSpace (TopCat.of M) (TopCat.of N))) (r : ℤ) y
        (i.property ▸ ordinaryExternal ℝ e (TopCat.of M) (TopCat.of N) i.val.1 i.val.2
          (homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion S) (i.val.1 : ℤ)
            ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (i.val.1 : ℤ) z) ⊗ₜ[ℝ]
           homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion T) (i.val.2 : ℤ)
            ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex T).homologyπ (i.val.2 : ℤ) w)))) : x=y := by
  apply realProductClass_ext e (TopCat.of M) (TopCat.of N) r
  intro i a b
  letI := hS i.val.1
  letI := hT i.val.2
  obtain ⟨z, rfl⟩ := smoothCycle_representative S a
  obtain ⟨w, rfl⟩ := smoothCycle_representative T b
  exact h i z w

end SmoothProductDetection

section ExteriorClassEvaluation
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CohomologyPairs P202Specs.CupProduct
open P202Specs.EilenbergZilber P202Specs.TopologicalKunneth
variable (R : Type v) [CommRing R]

/-- The ordinary exterior cup and shuffle external product satisfy the
Kronecker pairing formula on arbitrary classes, with arbitrary coefficients. -/
theorem externalCup_evaluation {X Y : TopCat.{u}} (p q : ℕ)
    (e : ExternalProduct.{v,u} R) (U : CohomologyRing R (productSpace X Y))
    (x : P202Specs.CupProduct.H R X p) (y : P202Specs.CupProduct.H R Y q)
    (z : P202Specs.TopologicalKunneth.H R X p) (w : P202Specs.TopologicalKunneth.H R Y q) :
    P202Specs.UniversalCoefficients.evaluation R R (ordinaryComplex R R (productSpace X Y)) ((p+q : ℕ) : ℤ)
      (U.product p q (hPullback R (firstProjection X Y) p x) (hPullback R (secondProjection X Y) q y))
      (ordinaryExternal R e X Y p q (z ⊗ₜ[R] w)) =
    P202Specs.UniversalCoefficients.evaluation R R (ordinaryComplex R R X) (p : ℤ) x z *
      P202Specs.UniversalCoefficients.evaluation R R (ordinaryComplex R R Y) (q : ℤ) y w := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective ((ordinaryCochains R R X).homologyπ (p : ℤ))).mp inferInstance x
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective ((ordinaryCochains R R Y).homologyπ (q : ℤ))).mp inferInstance y
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (ordinaryHomologyIso R X p).inv).mp inferInstance z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective (ordinaryHomologyIso R Y q).inv).mp inferInstance w
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((complex R R X).homologyπ p)).mp inferInstance z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective ((complex R R Y).homologyπ q)).mp inferInstance w
  rw [evaluation_nonnegative_cycles, evaluation_nonnegative_cycles]
  exact externalCup_class_evaluation R p q e U a b z w

/-- Every other Künneth bidegree pairs trivially with an exterior cup. -/
theorem externalCup_evaluation_offDiagonal {X Y : TopCat.{u}} (p q : ℕ)
    (e : ExternalProduct.{v,u} R) (U : CohomologyRing R (productSpace X Y))
    (x : P202Specs.CupProduct.H R X p) (y : P202Specs.CupProduct.H R Y q)
    (i : Diagonal (p+q)) (hi : i ≠ ⟨(p,q),rfl⟩)
    (z : P202Specs.TopologicalKunneth.H R X i.val.1) (w : P202Specs.TopologicalKunneth.H R Y i.val.2) :
    P202Specs.UniversalCoefficients.evaluation R R (ordinaryComplex R R (productSpace X Y)) ((p+q : ℕ) : ℤ)
      (U.product p q (hPullback R (firstProjection X Y) p x) (hPullback R (secondProjection X Y) q y))
      (i.property ▸ ordinaryExternal R e X Y i.val.1 i.val.2 (z ⊗ₜ[R] w)) = 0 := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective ((ordinaryCochains R R X).homologyπ (p : ℤ))).mp inferInstance x
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective ((ordinaryCochains R R Y).homologyπ (q : ℤ))).mp inferInstance y
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (ordinaryHomologyIso R X i.val.1).inv).mp inferInstance z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective (ordinaryHomologyIso R Y i.val.2).inv).mp inferInstance w
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((complex R R X).homologyπ i.val.1)).mp inferInstance z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective ((complex R R Y).homologyπ i.val.2)).mp inferInstance w
  exact externalCup_class_evaluation_offDiagonal R p q e U a b i hi z w

open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.TangentData SmoothManifolds.CovectorData
open SmoothManifolds.BundleOperationsData SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open P202Specs.DeRhamComparison P202Specs.DeRhamRing

/-- On literal smooth product cycles, the singular exterior cup of two
integration classes evaluates as the product of their actual smooth integrals.
The ordinary cocycles may differ from integration by smooth coboundaries. -/
theorem integration_externalCup_evaluation
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) {p q : ℕ}
    (ω : Field S p) (η : Field T q)
    (x : ordinaryCohomology ℝ ℝ (TopCat.of M) (p : ℤ))
    (y : ordinaryCohomology ℝ ℝ (TopCat.of N) (q : ℤ))
    (hx : IsIntegrationClass S C ω x) (hy : IsIntegrationClass T A η y)
    (e : ExternalProduct.{0,u} ℝ)
    (U : CohomologyRing ℝ (productSpace (TopCat.of M) (TopCat.of N)))
    (z : (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).cycles (p : ℤ))
    (w : (P202Specs.SmoothSingularComparison.smoothOrdinaryComplex T).cycles (q : ℤ)) :
    P202Specs.UniversalCoefficients.evaluation ℝ ℝ
      (ordinaryComplex ℝ ℝ (productSpace (TopCat.of M) (TopCat.of N))) ((p+q : ℕ) : ℤ)
      (U.product p q
        (hPullback ℝ (firstProjection (TopCat.of M) (TopCat.of N)) p x)
        (hPullback ℝ (secondProjection (TopCat.of M) (TopCat.of N)) q y))
      (ordinaryExternal ℝ e (TopCat.of M) (TopCat.of N) p q
        (homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion S) (p : ℤ)
          ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).homologyπ (p : ℤ) z) ⊗ₜ[ℝ]
         homologyMap (P202Specs.SmoothSingularComparison.ordinaryInclusion T) (q : ℤ)
          ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex T).homologyπ (q : ℤ) w))) =
      integralCochain S C ω
        ((smoothDegreeIso S p).hom
          ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex S).iCycles (p : ℤ) z)).val *
      integralCochain T A η
        ((smoothDegreeIso T q).hom
          ((P202Specs.SmoothSingularComparison.smoothOrdinaryComplex T).iCycles (q : ℤ) w)).val := by
  rw [externalCup_evaluation,
    integrationClass_ordinaryEvaluation S C ω x hx z,
    integrationClass_ordinaryEvaluation T A η y hy w]

end ExteriorClassEvaluation

/-- Integration classes multiply exactly in degree zero. All ordinary
cocycle representatives are allowed. -/
theorem integrationClass_zero_product (C : CotangentBundle S)
    (U : P202Specs.CupProduct.CohomologyRing ℝ (TopCat.of M))
    (ω η : Field S 0)
    (x y : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of M) 0)
    (hx : IsIntegrationClass S C ω x) (hy : IsIntegrationClass S C η y) :
    IsIntegrationClass S C (fieldWedge ω η) (U.product 0 0 x y) := by
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective
    ((P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).homologyπ 0)).mp
      inferInstance x
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective
    ((P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).homologyπ 0)).mp
      inferInstance y
  obtain ⟨c, hc, hcπ⟩ := U.represents 0 0 a b
  refine ⟨cyclesMap (P202Specs.SmoothSingularComparison.restriction S) 0 c, ?_, ?_⟩
  · have hn := congrArg (fun t => t c)
      (homologyπ_naturality (P202Specs.SmoothSingularComparison.restriction S) 0)
    change homologyMap (P202Specs.SmoothSingularComparison.restriction S) 0
        ((P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).homologyπ 0 c) =
      (P202Specs.SmoothSingularComparison.smoothCochains S).homologyπ 0
        (cyclesMap (P202Specs.SmoothSingularComparison.restriction S) 0 c) at hn
    erw [← hcπ, ha, hb] at hn
    exact hn.symm
  · intro σ
    have hi := congrArg (fun t => t c)
      (cyclesMap_i (P202Specs.SmoothSingularComparison.restriction S) 0)
    change (P202Specs.SmoothSingularComparison.smoothCochains S).iCycles 0
      (cyclesMap (P202Specs.SmoothSingularComparison.restriction S) 0 c) =
        (P202Specs.SmoothSingularComparison.restriction S).f 0
          ((P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).iCycles 0 c) at hi
    erw [hi, evaluateRestriction]
    change P202Specs.CupProduct.cocycleValue ℝ (TopCat.of M) 0 c (Finsupp.single σ.val 1) = _
    rw [hc, P202.CupProduct.cup_single]
    simp only [one_mul, P202.AlexanderWhitney.interval_self]
    have hω := integrationClass_zero_cocycleValue S C ω a (by
      rw [ha]; exact hx) σ
    have hη := integrationClass_zero_cocycleValue S C η b (by
      rw [hb]; exact hy) σ
    rw [hω, hη, simplexIntegral_wedge_zero]


/-- Every integration-induced comparison preserves the actual degree-zero
product, including manifolds with smooth boundary and empty manifolds. -/
theorem comparison_mul_zero {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (P : K.GradedProduct) (hP : K.IsGradedProduct P)
    (U : P202Specs.CupProduct.CohomologyRing ℝ (TopCat.of M))
    (e : ComparisonFamily S K) (he : IsIntegrationComparison S K e)
    (x y : K.Cohomology 0) :
    e 0 (P.mul 0 0 x y) = U.product 0 0 (e 0 x) (e 0 y) := by
  have hs : Function.Surjective (K.classOf 0) := (K.boundaries 0).mkQ_surjective
  obtain ⟨ω, hωx⟩ := hs x
  obtain ⟨η, hηy⟩ := hs y
  rw [← hωx, ← hηy]
  obtain ⟨ξ, hξ, hPξ⟩ := hP.2.2.2.2.1 0 0 ω η
  change e 0 (P.mul 0 0 (K.classOf 0 ω) (K.classOf 0 η)) =
    U.product 0 0 (e 0 (K.classOf 0 ω)) (e 0 (K.classOf 0 η))
  rw [hPξ]
  letI := he.1 0
  have hLeft := he.2 0 ξ
  have hField := congrArg (fun f => IsIntegrationClass S C f (e 0 (K.classOf 0 ξ))) hξ
  have hRight := integrationClass_zero_product S C U ω.val.val η.val.val
    (e 0 (K.classOf 0 ω)) (e 0 (K.classOf 0 η)) (he.2 0 ω) (he.2 0 η)
  exact integrationClass_unique S C (fieldWedge ω.val.val η.val.val) (hField.mp hLeft) hRight


/-- An alternating form vanishes when its degree exceeds the dimension of
its Euclidean domain; no assumption on a target manifold is involved. -/
theorem alternatingForm_aboveDimension {k l : ℕ} (h : k < l)
    (A : (ModelData.Euclidean k) [⋀^Fin l]→L[ℝ] ℝ) : A = 0 := by
  have hA : A.toAlternatingMap = 0 := by
    apply (Pi.basisFun ℝ (Fin k)).ext_alternating
    intro j _
    have hj : ¬Function.Injective j := by
      intro hj
      have hc := Fintype.card_le_of_injective j hj
      simp only [Fintype.card_fin] at hc
      omega
    simp only [zero_apply]
    apply A.toAlternatingMap.map_eq_zero_of_not_injective
    intro hinj
    apply hj
    intro i i' hii'
    exact hinj (congrArg (Pi.basisFun ℝ (Fin k)) hii')
  ext v
  exact DFunLike.congr_fun hA v


/-- Intrinsic pullbacks to a lower-dimensional simplex vanish in degrees
above that simplex, including all corner points. -/
theorem coordinatePullback_aboveDimension (C : CotangentBundle S) {k l : ℕ}
    (h : k < l) (ω : Field S l) (σ : SmoothSingularData.SingularSimplex S k) :
    SimplexPullbackIntegral.coordinatePullback (C := C) ω σ = 0 := by
  funext y
  exact alternatingForm_aboveDimension h _

/-- Affine cells factoring through a simplex of dimension below the form
degree have identically zero pullback, regardless of the cell dimension. -/
theorem coordinatePullback_reparametrized_aboveDimension (C : CotangentBundle S)
    {r k l : ℕ} (h : k < l) (θ : Fin (r+1) → Fin (k+1))
    (ω : Field S l) (σ : SmoothSimplex S k)
    (x : P202Specs.SmoothSingularComparison.CornerSimplex r) :
    SimplexPullbackIntegral.coordinatePullback (C := C) ω
      (p104Simplex S (reparametrizedSmoothSimplex S θ σ)) x.val = 0 := by
  rw [coordinatePullback_reparametrized, coordinatePullback_aboveDimension S C h]
  rfl


section ShuffleMeasure
open scoped Matrix
open MeasureTheory Set
open P202Specs.ShuffleModel P202Specs.ShuffleTriangulation

/-- The affine shuffle maps fix the initial corner vertex, so their standard
ordered coordinate realization is the linear map of the orientation matrix. -/
def shuffleCellLinear {p q : ℕ} (s : LatticePath p q) :
    ModelData.Euclidean (p+q) →ₗ[ℝ] ModelData.Euclidean (p+q) :=
  Matrix.toLin' (standardOrientationMatrix s)

def flatShuffleCell {p q : ℕ} (s : LatticePath p q) : Set (ModelData.Euclidean (p+q)) :=
  shuffleCellLinear s '' CornerData.simplexSet (p+q)

 theorem standardOrientationMatrix_first {p q : ℕ} (s : LatticePath p q)
    (i : Fin p) (j : Fin (p+q)) :
    standardOrientationMatrix s (i.castAdd q) j =
      if s.horizontal j.succ = i.succ then 1 else 0 := by
  simp only [standardOrientationMatrix, standardProductCoordinates, Fin.val_castAdd,
    i.isLt, dite_true, vertex, weights, Convexity.StdSimplex.weights_single,
    Finsupp.single_apply, (P202.ShuffleModel.path_initial s).1]
  simp only [Fin.ext_iff, Fin.val_succ, Fin.val_zero]
  simp [eq_comm]

 theorem standardOrientationMatrix_second {p q : ℕ} (s : LatticePath p q)
    (i : Fin q) (j : Fin (p+q)) :
    standardOrientationMatrix s (i.natAdd p) j =
      if s.vertical j.succ = i.succ then 1 else 0 := by
  simp only [standardOrientationMatrix, standardProductCoordinates, Fin.val_natAdd,
    Nat.not_lt.mpr (Nat.le_add_right p i.val), dite_false, Nat.add_sub_cancel_left,
    vertex, weights, Convexity.StdSimplex.weights_single,
    Finsupp.single_apply, (P202.ShuffleModel.path_initial s).2]
  simp only [Fin.ext_iff, Fin.val_succ, Fin.val_zero]
  simp [eq_comm]

 theorem shuffleCellLinear_apply {p q : ℕ} (s : LatticePath p q)
    (x : ModelData.Euclidean (p+q)) :
    shuffleCellLinear s x = Fin.append
      (ambientReparametrization s.horizontal x) (ambientReparametrization s.vertical x) := by
  funext i
  rw [shuffleCellLinear, Matrix.toLin'_apply]
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp only [Matrix.mulVec, dotProduct, Fin.append_left, standardOrientationMatrix_first]
    simp only [ambientReparametrization, ambientMap, Finset.sum_filter, Fin.sum_univ_succ,
      CornerData.simplexBarycentric, Fin.cons_zero, Fin.cons_succ,
      (P202.ShuffleModel.path_initial s).1, Ne.symm (Fin.succ_ne_zero k), ite_false, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp_all
  · intro k
    simp only [Matrix.mulVec, dotProduct, Fin.append_right, standardOrientationMatrix_second]
    simp only [ambientReparametrization, ambientMap, Finset.sum_filter, Fin.sum_univ_succ,
      CornerData.simplexBarycentric, Fin.cons_zero, Fin.cons_succ,
      (P202.ShuffleModel.path_initial s).2, Ne.symm (Fin.succ_ne_zero k), ite_false, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp_all


theorem latticePath_eq_of_vertex_eq {p q : ℕ} {s t : LatticePath p q}
    (h : ∀ k, vertex s k = vertex t k) : s = t := by
  apply Subtype.ext
  apply Prod.ext
  · apply DFunLike.ext
    intro k
    apply Finsupp.single_left_injective (one_ne_zero : (1 : ℝ) ≠ 0)
    apply Finsupp.ext
    intro i
    exact congrFun (congrArg Prod.fst (h k)) i
  · apply DFunLike.ext
    intro k
    apply Finsupp.single_left_injective (one_ne_zero : (1 : ℝ) ≠ 0)
    apply Finsupp.ext
    intro i
    exact congrFun (congrArg Prod.snd (h k)) i

theorem exists_vertex_ne {p q : ℕ} {s t : LatticePath p q} (hst : s ≠ t) :
    ∃ k : Fin (p+q+1), vertex s k ≠ vertex t k := by
  by_contra h
  push Not at h
  exact hst (latticePath_eq_of_vertex_eq h)

def flatProductCoordinates {p q : ℕ} (z : StdSimplex p × StdSimplex q) :
    ModelData.Euclidean (p+q) :=
  Fin.append (P202Specs.SmoothSingularComparison.toCorner p z.1).val
    (P202Specs.SmoothSingularComparison.toCorner q z.2).val

def flatProductSimplex (p q : ℕ) : Set (ModelData.Euclidean (p+q)) :=
  Set.range (flatProductCoordinates (p := p) (q := q))

theorem flatProductCoordinates_injective {p q : ℕ} :
    Function.Injective (flatProductCoordinates (p := p) (q := q)) := by
  intro x y h
  apply Prod.ext
  · apply (P202Specs.SmoothSingularComparison.simplexHomeomorph p).symm.injective
    apply Subtype.ext
    funext i
    change (P202Specs.SmoothSingularComparison.toCorner p x.1).val i =
      (P202Specs.SmoothSingularComparison.toCorner p y.1).val i
    have hi := congrFun h (i.castAdd q)
    simpa only [flatProductCoordinates, Fin.append_left] using hi
  · apply (P202Specs.SmoothSingularComparison.simplexHomeomorph q).symm.injective
    apply Subtype.ext
    funext i
    change (P202Specs.SmoothSingularComparison.toCorner q x.2).val i =
      (P202Specs.SmoothSingularComparison.toCorner q y.2).val i
    have hi := congrFun h (i.natAdd p)
    simpa only [flatProductCoordinates, Fin.append_right] using hi

theorem shuffleCellLinear_barycentric {p q : ℕ} (s : LatticePath p q)
    (z : StdSimplex (p+q)) :
    shuffleCellLinear s (P202Specs.SmoothSingularComparison.toCorner (p+q) z).val =
      flatProductCoordinates (parametrization s z) := by
  rw [shuffleCellLinear_apply]
  have h₁ := cornerReparametrization_val s.horizontal
    (P202Specs.SmoothSingularComparison.toCorner (p+q) z)
  have h₂ := cornerReparametrization_val s.vertical
    (P202Specs.SmoothSingularComparison.toCorner (p+q) z)
  simp only [cornerReparametrization,
    P202Specs.SmoothSingularComparison.toBarycentric_toCorner] at h₁ h₂
  rw [← h₁, ← h₂]
  rfl

theorem flatProductSimplex_eq_iUnion (p q : ℕ) :
    flatProductSimplex p q = ⋃ s : LatticePath p q, flatShuffleCell s := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨s,x,hx⟩ := P202.ShuffleTriangulation.coverage p q z
    apply Set.mem_iUnion.mpr
    refine ⟨s, P202Specs.SmoothSingularComparison.toCorner (p+q) x,
      (P202Specs.SmoothSingularComparison.toCorner (p+q) x).property, ?_⟩
    exact (shuffleCellLinear_barycentric s x).trans (congrArg flatProductCoordinates hx)
  · intro z hz
    obtain ⟨s, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    refine ⟨parametrization s (P202Specs.SmoothSingularComparison.toBarycentric (p+q) ⟨x,hx⟩), ?_⟩
    have hh := shuffleCellLinear_barycentric s
      (P202Specs.SmoothSingularComparison.toBarycentric (p+q) ⟨x,hx⟩)
    simpa only [P202Specs.SmoothSingularComparison.toCorner_toBarycentric] using hh.symm

theorem shuffleCellLinear_det {p q : ℕ} (s : LatticePath p q) :
    LinearMap.det (shuffleCellLinear s) = (s.sign : ℝ) := by
  rw [shuffleCellLinear, LinearMap.det_toLin']
  exact P202.ShuffleTriangulation.standard_orientation s

theorem shuffleCellLinear_abs_det {p q : ℕ} (s : LatticePath p q) :
    |LinearMap.det (shuffleCellLinear s)| = 1 := by
  rw [shuffleCellLinear_det]
  have hs : (s.sign : ℝ) * (s.sign : ℝ) = 1 := by
    exact_mod_cast (Int.isUnit_mul_self (Equiv.Perm.sign s.permutation).isUnit)
  have hh : |(s.sign : ℝ)| = |(1 : ℝ)| :=
    abs_eq_iff_mul_self_eq.mpr (by simpa using hs)
  simpa only [abs_one] using hh

theorem shuffleCellLinear_injective {p q : ℕ} (s : LatticePath p q) :
    Function.Injective (shuffleCellLinear s) := by
  exact (shuffleCellLinear s).equivOfDetNeZero (by
    intro h
    have hh := shuffleCellLinear_abs_det s
    rw [h, abs_zero] at hh
    exact zero_ne_one hh) |>.injective

theorem flatShuffleCell_compact {p q : ℕ} (s : LatticePath p q) :
    IsCompact (flatShuffleCell s) :=
  (SimplexPullbackIntegral.simplex_isCompact (p+q)).image
    (shuffleCellLinear s).continuous_of_finiteDimensional


theorem coordinateHyperplane_null (d : ℕ) (j : Fin d) :
    volume {x : ModelData.Euclidean d | x j = 0} = 0 := by
  change volume (LinearMap.ker (LinearMap.proj j : ModelData.Euclidean d →ₗ[ℝ] ℝ) : Set (ModelData.Euclidean d)) = 0
  apply MeasureTheory.Measure.addHaar_submodule volume
  intro h
  have he : (Pi.single j (1 : ℝ) : ModelData.Euclidean d) ∈
      LinearMap.ker (LinearMap.proj j : ModelData.Euclidean d →ₗ[ℝ] ℝ) := by
    rw [h]
    trivial
  simpa using he

theorem flatShuffleCell_inter_null {p q : ℕ} {s t : LatticePath p q} (hst : s ≠ t) :
    volume (flatShuffleCell s ∩ flatShuffleCell t) = 0 := by
  obtain ⟨k,hk⟩ := exists_vertex_ne hst
  have hk0 : k ≠ 0 := by
    intro h
    apply hk
    subst k
    simp only [vertex, (P202.ShuffleModel.path_initial s).1,
      (P202.ShuffleModel.path_initial s).2, (P202.ShuffleModel.path_initial t).1,
      (P202.ShuffleModel.path_initial t).2]
  let j := k.pred hk0
  have hsubset : flatShuffleCell s ∩ flatShuffleCell t ⊆
      shuffleCellLinear s '' {x : ModelData.Euclidean (p+q) | x j = 0} := by
    rintro z ⟨⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩
    let X := P202Specs.SmoothSingularComparison.toBarycentric (p+q) ⟨x,hx⟩
    let Y := P202Specs.SmoothSingularComparison.toBarycentric (p+q) ⟨y,hy⟩
    have hX : flatProductCoordinates (parametrization s X) = z := by
      have hh := (shuffleCellLinear_barycentric s X).symm
      simpa only [X, P202Specs.SmoothSingularComparison.toCorner_toBarycentric] using hh.trans hxz
    have hY : flatProductCoordinates (parametrization t Y) = z := by
      have hh := (shuffleCellLinear_barycentric t Y).symm
      simpa only [Y, P202Specs.SmoothSingularComparison.toCorner_toBarycentric] using hh.trans hyz
    have hp := flatProductCoordinates_injective (hX.trans hY.symm)
    have hXY := P202.ShuffleTriangulation.same_barycentric_coordinates s t X Y hp
    have hp' : parametrization s X = parametrization t X := by rwa [← hXY] at hp
    have hw : weights X k = 0 := by
      by_contra h
      have hpos : 0 < weights X k := lt_of_le_of_ne (X.weights_nonneg k) (Ne.symm h)
      exact hk (P202.ShuffleTriangulation.positive_weight_vertex_eq s t X hp' k hpos)
    refine ⟨x, ?_, hxz⟩
    have hk' : j.succ = k := Fin.succ_pred k hk0
    rw [← hk'] at hw
    exact hw
  refine measure_mono_null hsubset ?_
  rw [MeasureTheory.Measure.addHaar_image_linearMap, coordinateHyperplane_null, mul_zero]

theorem flatShuffleCells_aedisjoint (p q : ℕ) :
    Pairwise (fun s t : LatticePath p q => AEDisjoint volume (flatShuffleCell s) (flatShuffleCell t)) :=
  fun _ _ hst => flatShuffleCell_inter_null hst

/-- Change of variables on the actual unimodular coordinate shuffle cell. -/
theorem integral_flatShuffleCell {p q : ℕ} (s : LatticePath p q)
    (f : ModelData.Euclidean (p+q) → ℝ) :
    ∫ x in flatShuffleCell s, f x =
      ∫ y in CornerData.simplexSet (p+q), f (shuffleCellLinear s y) := by
  let L := (shuffleCellLinear s).toContinuousLinearMap
  have h := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    (SimplexPullbackIntegral.simplex_isCompact (p+q)).measurableSet
    (fun x _ => L.hasFDerivAt.hasFDerivWithinAt)
    (shuffleCellLinear_injective s).injOn f
  change (∫ x in flatShuffleCell s, f x) =
    ∫ y in CornerData.simplexSet (p+q),
      |LinearMap.det (shuffleCellLinear s)| • f (shuffleCellLinear s y) at h
  simpa only [shuffleCellLinear_abs_det, one_smul] using h


/-- The actual finite shuffle cells partition the product simplex up to
null overlaps; their unimodular substitutions give the full scalar integral. -/
theorem integral_flatProductSimplex (p q : ℕ)
    (f : ModelData.Euclidean (p+q) → ℝ)
    (hf : IntegrableOn f (flatProductSimplex p q)) :
    ∫ x in flatProductSimplex p q, f x =
      ∑ s : LatticePath p q,
        ∫ y in CornerData.simplexSet (p+q), f (shuffleCellLinear s y) := by
  rw [flatProductSimplex_eq_iUnion] at hf ⊢
  rw [integral_iUnion_ae
    (fun s => (flatShuffleCell_compact s).measurableSet.nullMeasurableSet)
    (flatShuffleCells_aedisjoint p q) hf, tsum_fintype]
  apply Finset.sum_congr rfl
  intro s _
  exact integral_flatShuffleCell s f


end ShuffleMeasure

section FlatProductIntegration
open MeasureTheory Set
/-- Ordered flattening of two coordinate blocks, equipped with their actual
Lebesgue sigma algebras. -/
def flatProductEquiv (p q : ℕ) :
    (ModelData.Euclidean p × ModelData.Euclidean q) ≃ᵐ ModelData.Euclidean (p+q) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (p+q) => ℝ) finSumFinEquiv)

@[simp] theorem flatProductEquiv_apply (p q : ℕ)
    (xy : ModelData.Euclidean p × ModelData.Euclidean q) :
    flatProductEquiv p q xy = Fin.append xy.1 xy.2 := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · change MeasurableEquiv.piCongrLeft (fun _ : Fin (p+q) => ℝ) finSumFinEquiv
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => ℝ)).symm xy)
        (finSumFinEquiv (Sum.inl i)) = _
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp only [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi_symm_apply,
      Fin.append_left]
  · change MeasurableEquiv.piCongrLeft (fun _ : Fin (p+q) => ℝ) finSumFinEquiv
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => ℝ)).symm xy)
        (finSumFinEquiv (Sum.inr j)) = _
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp only [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi_symm_apply,
      Fin.append_right]

@[simp] theorem flatProductEquiv_symm_apply (p q : ℕ) (x : ModelData.Euclidean (p+q)) :
    (flatProductEquiv p q).symm x =
      ((fun i : Fin p => x (i.castAdd q)), (fun j : Fin q => x (j.natAdd p))) := by
  apply (flatProductEquiv p q).injective
  rw [(flatProductEquiv p q).apply_symm_apply, flatProductEquiv_apply]
  ext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;>
    simp only [Fin.append_left, Fin.append_right]

/-- Flattening preserves product Lebesgue volume, including either empty
coordinate block. -/
theorem flatProductEquiv_measurePreserving (p q : ℕ) :
    MeasurePreserving (flatProductEquiv p q) volume volume := by
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (p+q) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin p ⊕ Fin q => ℝ))

/-- The ordinary Cartesian product of the two standard simplexes in ordered
flat coordinates. -/
def flatProductSet (p q : ℕ) : Set (ModelData.Euclidean (p+q)) :=
  {x | (fun i : Fin p => x (i.castAdd q)) ∈ CornerData.simplexSet p ∧
    (fun j : Fin q => x (j.natAdd p)) ∈ CornerData.simplexSet q}

@[simp] theorem flatProductEquiv_image_simplex (p q : ℕ) :
    flatProductEquiv p q '' (CornerData.simplexSet p ×ˢ CornerData.simplexSet q) =
      flatProductSet p q := by
  change (flatProductEquiv p q).toEquiv '' _ = _
  rw [(flatProductEquiv p q).toEquiv.image_eq_preimage_symm]
  ext x
  change ((flatProductEquiv p q).symm x).1 ∈ CornerData.simplexSet p ∧
      ((flatProductEquiv p q).symm x).2 ∈ CornerData.simplexSet q ↔ _
  rw [flatProductEquiv_symm_apply]
  rfl

/-- The barycentric product-simplex domain used by shuffle triangulation is
exactly the same flat domain as the ordered product of the corner simplexes. -/
theorem flatProductSimplex_eq_flatProductSet (p q : ℕ) :
    flatProductSimplex p q = flatProductSet p q := by
  rw [← flatProductEquiv_image_simplex]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨((P202Specs.SmoothSingularComparison.toCorner p z.1).val,
      (P202Specs.SmoothSingularComparison.toCorner q z.2).val),
      ⟨(P202Specs.SmoothSingularComparison.toCorner p z.1).property,
        (P202Specs.SmoothSingularComparison.toCorner q z.2).property⟩, ?_⟩
    exact flatProductEquiv_apply p q _
  · rintro ⟨xy, hxy, hx⟩
    refine ⟨(P202Specs.SmoothSingularComparison.toBarycentric p ⟨xy.1,hxy.1⟩,
      P202Specs.SmoothSingularComparison.toBarycentric q ⟨xy.2,hxy.2⟩), ?_⟩
    simpa only [flatProductCoordinates, P202Specs.SmoothSingularComparison.toCorner_toBarycentric,
      flatProductEquiv_apply] using hx

/-- Transport of simplex product integration to the actual flat coordinate
volume. No integrability hypothesis is needed for this change of variables. -/
theorem integral_flatProductSet (p q : ℕ) (F : ModelData.Euclidean (p+q) → ℝ) :
    (∫ x in flatProductSet p q, F x) =
      ∫ xy in CornerData.simplexSet p ×ˢ CornerData.simplexSet q,
        F (Fin.append xy.1 xy.2) ∂(volume.prod volume) := by
  have h := (flatProductEquiv_measurePreserving p q).setIntegral_image_emb
    (flatProductEquiv p q).measurableEmbedding F
    (CornerData.simplexSet p ×ˢ CornerData.simplexSet q)
  rw [flatProductEquiv_image_simplex, Measure.volume_eq_prod] at h
  simpa only [flatProductEquiv_apply] using h

/-- Integrability is equivalent in the product and flattened coordinate
realizations of the simplex product. -/
theorem integrableOn_flatProductSet_iff (p q : ℕ) (F : ModelData.Euclidean (p+q) → ℝ) :
    IntegrableOn F (flatProductSet p q) ↔
      IntegrableOn (fun xy : ModelData.Euclidean p × ModelData.Euclidean q =>
        F (Fin.append xy.1 xy.2)) (CornerData.simplexSet p ×ˢ CornerData.simplexSet q)
          (volume.prod volume) := by
  have h := ((flatProductEquiv_measurePreserving p q).restrict_image_emb
    (flatProductEquiv p q).measurableEmbedding
    (CornerData.simplexSet p ×ˢ CornerData.simplexSet q)).integrable_comp_emb
      (flatProductEquiv p q).measurableEmbedding (g := F)
  rw [flatProductEquiv_image_simplex, Measure.volume_eq_prod] at h
  simpa only [IntegrableOn, Function.comp_def, flatProductEquiv_apply] using h.symm

/-- Fubini in the ordered flat coordinates of the two simplex factors. -/
theorem integral_flatProduct_mul (p q : ℕ)
    (f : ModelData.Euclidean p → ℝ) (g : ModelData.Euclidean q → ℝ) :
    (∫ x in flatProductSet p q,
      f (fun i : Fin p => x (i.castAdd q)) * g (fun j : Fin q => x (j.natAdd p))) =
      (∫ x in CornerData.simplexSet p, f x) * (∫ y in CornerData.simplexSet q, g y) := by
  rw [integral_flatProductSet]
  simp only [Fin.append_left, Fin.append_right]
  exact setIntegral_prod_mul f g (CornerData.simplexSet p) (CornerData.simplexSet q)

/-- Separate simplex integrability gives integrability of the flattened
product, with no regularity assumption on the coefficients beyond integrability. -/
theorem integrableOn_flatProduct_mul (p q : ℕ)
    (f : ModelData.Euclidean p → ℝ) (g : ModelData.Euclidean q → ℝ)
    (hf : IntegrableOn f (CornerData.simplexSet p))
    (hg : IntegrableOn g (CornerData.simplexSet q)) :
    IntegrableOn (fun x =>
      f (fun i : Fin p => x (i.castAdd q)) * g (fun j : Fin q => x (j.natAdd p)))
      (flatProductSet p q) := by
  apply (integrableOn_flatProductSet_iff p q _).mpr
  simp only [Fin.append_left, Fin.append_right]
  rw [IntegrableOn, ← Measure.prod_restrict]
  exact hf.mul_prod hg

section SmoothCoefficients
variable {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
  (T : AtlasData.SmoothManifold m b N)

/-- The ordinary product coefficient has the separate simplex integral
product when integrated using the actual flat Lebesgue volume. -/
theorem simplexIntegral_flatProduct_fubini (C : CotangentBundle S) (A : CotangentBundle T)
    {p q : ℕ} (ω : Field S p) (η : Field T q)
    (σ : SmoothSingularData.SingularSimplex S p)
    (τ : SmoothSingularData.SingularSimplex T q) :
    (∫ x in flatProductSet p q,
      IntegrationCochainData.ambientPullbackCoefficient S C ω σ
        (fun i : Fin p => x (i.castAdd q)) *
      IntegrationCochainData.ambientPullbackCoefficient T A η τ
        (fun j : Fin q => x (j.natAdd p))) =
      IntegrationCochainData.simplexIntegral S C ω σ *
      IntegrationCochainData.simplexIntegral T A η τ := by
  exact integral_flatProduct_mul p q _ _

/-- Smoothness of each intrinsic form supplies actual integrability of the
flattened product coefficient on the simplex product. -/
theorem integrableOn_flatProduct_pullbackCoefficient
    (C : CotangentBundle S) (A : CotangentBundle T) {p q : ℕ}
    (B : FormBundle C p) (E : FormBundle A q)
    (ω : Field S p) (η : Field T q) (hω : IsForm B ω) (hη : IsForm E η)
    (σ : SmoothSingularData.SingularSimplex S p)
    (τ : SmoothSingularData.SingularSimplex T q) :
    IntegrableOn (fun x =>
      IntegrationCochainData.ambientPullbackCoefficient S C ω σ
        (fun i : Fin p => x (i.castAdd q)) *
      IntegrationCochainData.ambientPullbackCoefficient T A η τ
        (fun j : Fin q => x (j.natAdd p))) (flatProductSet p q) := by
  exact integrableOn_flatProduct_mul p q _ _
    (SmoothManifolds.SimplexPullbackIntegral.simplexIntegral_integrable B ω hω σ)
    (SmoothManifolds.SimplexPullbackIntegral.simplexIntegral_integrable E η hη τ)

/-- The finite sum of actual scalar pullback product integrals on all
unimodular shuffle cells equals the separate simplex integral product. -/
theorem simplexIntegral_product_shuffleCells
    (C : CotangentBundle S) (A : CotangentBundle T) {p q : ℕ}
    (B : FormBundle C p) (E : FormBundle A q)
    (ω : Field S p) (η : Field T q) (hω : IsForm B ω) (hη : IsForm E η)
    (σ : SmoothSingularData.SingularSimplex S p)
    (τ : SmoothSingularData.SingularSimplex T q) :
    (∑ s : P202Specs.ShuffleModel.LatticePath p q,
      ∫ y in CornerData.simplexSet (p+q),
        IntegrationCochainData.ambientPullbackCoefficient S C ω σ
          (fun i : Fin p => shuffleCellLinear s y (i.castAdd q)) *
        IntegrationCochainData.ambientPullbackCoefficient T A η τ
          (fun j : Fin q => shuffleCellLinear s y (j.natAdd p))) =
      IntegrationCochainData.simplexIntegral S C ω σ *
      IntegrationCochainData.simplexIntegral T A η τ := by
  let f : ModelData.Euclidean (p+q) → ℝ := fun x =>
    IntegrationCochainData.ambientPullbackCoefficient S C ω σ
      (fun i : Fin p => x (i.castAdd q)) *
    IntegrationCochainData.ambientPullbackCoefficient T A η τ
      (fun j : Fin q => x (j.natAdd p))
  have hf : IntegrableOn f (flatProductSimplex p q) := by
    rw [flatProductSimplex_eq_flatProductSet]
    exact integrableOn_flatProduct_pullbackCoefficient S T C A B E ω η hω hη σ τ
  have h := integral_flatProductSimplex p q f hf
  rw [flatProductSimplex_eq_flatProductSet] at h
  exact h.symm.trans (simplexIntegral_flatProduct_fubini S T C A ω η σ τ)

end SmoothCoefficients
end FlatProductIntegration

/-- Multiplicativity descends along any smooth map whose ordinary real
cohomology pullback is injective. For the boundary reduction the map will be
the actual inclusion of the manifold interior. -/
theorem comparison_mul_of_pullback_injective
    (hDR : P202Specs.DeRhamComparison.deRhamComparison_type.{u})
    (U : P202Specs.CupProduct.NaturalCohomologyRing.{0,u} ℝ)
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (P : K.GradedProduct) (Q : J.GradedProduct)
    (hP : K.IsGradedProduct P) (hQ : J.IsGradedProduct Q)
    (e : ComparisonFamily S K) (h : ComparisonFamily T J)
    (he : IsIntegrationComparison S K e) (hh : IsIntegrationComparison T J h)
    (f : M → N) (hf : MapData.IsSmoothMap S T f)
    (L : ∀ x, TangentData.TangentSpace S x →ₗ[ℝ] TangentData.TangentSpace T (f x))
    (hL : ∀ x, DifferentialData.IsDifferential S T f x (L x))
    (F : ∀ q, J.Cohomology q →ₗ[ℝ] K.Cohomology q)
    (hF : IsCohomologyPullback C B K J f L F)
    (hInjective : ∀ q, Function.Injective
      (P202Specs.CupProduct.hPullback ℝ
        (P202Specs.SmoothSingularComparison.underlyingMap S T f hf) q))
    (hMul : ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
      e (p+q) (P.mul p q x y) = (U.ring (TopCat.of M)).product p q (e p x) (e q y)) :
    ∀ p q (x : J.Cohomology p) (y : J.Cohomology q),
      h (p+q) (Q.mul p q x y) = (U.ring (TopCat.of N)).product p q (h p x) (h q y) := by
  have hn := hDR.2 S T C A B E K J e h he hh f hf L hL F hF
  have hp := (SmoothManifolds.DeRhamResults.pullback_product S T C A B E K J
    P Q f L F hP hQ hF).2
  intro p q x y
  apply hInjective (p+q)
  change P202Specs.CupProduct.hPullback ℝ
      (P202Specs.SmoothSingularComparison.underlyingMap S T f hf) (p+q)
      (h (p+q) (Q.mul p q x y)) = _
  calc
    _ = e (p+q) (F (p+q) (Q.mul p q x y)) := (hn (p+q) _).symm
    _ = e (p+q) (P.mul p q (F p x) (F q y)) := congrArg (e (p+q)) (hp p q x y)
    _ = (U.ring (TopCat.of M)).product p q (e p (F p x)) (e q (F q y)) := hMul p q _ _
    _ = (U.ring (TopCat.of M)).product p q
        (P202Specs.CupProduct.hPullback ℝ
          (P202Specs.SmoothSingularComparison.underlyingMap S T f hf) p (h p x))
        (P202Specs.CupProduct.hPullback ℝ
          (P202Specs.SmoothSingularComparison.underlyingMap S T f hf) q (h q y)) := by
      rw [hn p x, hn q y]
      rfl
    _ = _ := (P202.CupProduct.represented_product_natural ℝ
      (fun X => (U.ring X).product) (fun X => (U.ring X).represents)
      (P202Specs.SmoothSingularComparison.underlyingMap S T f hf) p q (h p x) (h q y)).symm


section OffDiagonalIntegration
/-- Determinant-normalized evaluation detects every Euclidean covector. -/
theorem euclideanEvaluate_injective (r l : ℕ) :
    Function.Injective (evaluate (ModelData.Euclidean r) l) := by
  exact (exteriorPower.alternatingMapLinearEquiv.symm.injective).comp
    (exteriorPower.bijective_pairingDual ℝ (ModelData.Euclidean r) l).injective

variable {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
  (T : AtlasData.SmoothManifold m b N)

/-- A pulled-back covector vanishes if the affine simplex map factors through
a domain whose dimension is below the form degree. -/
theorem simplexCovector_reparametrized_aboveDimension (C : CotangentBundle S)
    {r k l : ℕ} (h : k < l) (θ : Fin (r+1) → Fin (k+1))
    (ω : Field S l) (σ : SmoothSimplex S k)
    (x : P202Specs.SmoothSingularComparison.CornerSimplex r) :
    exteriorPower.map l (IntegrationCochainData.simplexDifferential S C
      (p104Simplex S (reparametrizedSmoothSimplex S θ σ)) x).dualMap
      (ω ((p104Simplex S (reparametrizedSmoothSimplex S θ σ)).val x)) = 0 := by
  apply euclideanEvaluate_injective r l
  apply AlternatingMap.ext
  intro v
  simp only [map_zero, zero_apply]
  have he := evaluate_exteriorMap
    (V := ModelData.Euclidean r)
    (W := TangentData.TangentSpace S
      ((p104Simplex S (reparametrizedSmoothSimplex S θ σ)).val x)) l
    (IntegrationCochainData.simplexDifferential S C
      (p104Simplex S (reparametrizedSmoothSimplex S θ σ)) x)
    (ω ((p104Simplex S (reparametrizedSmoothSimplex S θ σ)).val x)) v
  have hz := coordinatePullback_reparametrized_aboveDimension S C h θ ω σ x
  have hv := DFunLike.congr_fun hz v
  rw [SimplexPullbackIntegral.coordinatePullback_apply] at hv
  exact he.trans hv

/-- External affine-cell integrals in the wrong bidegree vanish whenever one
factor form has degree greater than that factor's simplex dimension. -/
theorem productSimplexIntegral_affine_offDiagonal (C : CotangentBundle S) (A : CotangentBundle T)
    {p q k l : ℕ} (h : k < p ∨ l < q) (ω : Field S p) (η : Field T q)
    (θ : Fin (p+q+1) → Fin (k+1)) (φ : Fin (p+q+1) → Fin (l+1))
    (σ : SmoothSimplex S k) (τ : SmoothSimplex T l) :
    productSimplexIntegral S T C A ω η
      (p104Simplex S (reparametrizedSmoothSimplex S θ σ))
      (p104Simplex T (reparametrizedSmoothSimplex T φ τ)) rfl = 0 := by
  unfold productSimplexIntegral
  apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  rw [dite_eq_left hy]
  rcases h with h | h
  · rw [simplexCovector_reparametrized_aboveDimension S C h]
    change evaluate (ModelData.Euclidean (p+q)) (p+q) (wedge 0 _) _ = 0
    simp only [map_zero, LinearMap.zero_apply, zero_apply]
  · rw [simplexCovector_reparametrized_aboveDimension T A h]
    change evaluate (ModelData.Euclidean (p+q)) (p+q) (wedge _ 0) _ = 0
    rw [map_zero, map_zero]
    rfl

end OffDiagonalIntegration

section ShuffleCoefficients
/-- The determinant-normalized standard coordinate top covector. -/
def standardTopCovector (d : ℕ) : Fiber (ModelData.Euclidean d) d :=
  exteriorPower.ιMulti ℝ d (fun i => LinearMap.proj i)

theorem standardTopCovector_evaluate (d : ℕ) :
    evaluate (ModelData.Euclidean d) d (standardTopCovector d)
      (fun i => Pi.single i 1) = 1 := by
  rw [standardTopCovector, ExteriorAlgebraResults.determinant_normalization]
  have hmat : Matrix.of (fun i j : Fin d =>
      (LinearMap.proj i : ModelData.Euclidean d →ₗ[ℝ] ℝ) (Pi.single j 1)) = 1 := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hmat, Matrix.det_one]

theorem topCovector_eq_coefficient (d : ℕ) (α : Fiber (ModelData.Euclidean d) d) :
    α = (evaluate (ModelData.Euclidean d) d α (fun i => Pi.single i 1)) •
      standardTopCovector d := by
  have hd : Module.finrank ℝ (Fiber (ModelData.Euclidean d) d) = 1 := by
    simp [Fiber, exteriorPower.finrank_eq, Subspace.dual_finrank_eq]
  have hn : standardTopCovector d ≠ 0 := by
    intro h
    have hh := standardTopCovector_evaluate d
    rw [h, map_zero, AlternatingMap.zero_apply] at hh
    exact zero_ne_one hh
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (standardTopCovector d) hn).mp hd α
  rw [← hc, map_smul, AlternatingMap.smul_apply, standardTopCovector_evaluate,
    smul_eq_mul, mul_one]

/-- Matrix of the ordered pair of linear maps, with the first factor's
coordinates preceding the second factor's coordinates. -/
def orderedProductJacobian {p q : ℕ}
    (L : ModelData.Euclidean (p+q) →ₗ[ℝ] ModelData.Euclidean p)
    (K : ModelData.Euclidean (p+q) →ₗ[ℝ] ModelData.Euclidean q) :
    Matrix (Fin (p+q)) (Fin (p+q)) ℝ :=
  fun i j => Fin.append (L (Pi.single j 1)) (K (Pi.single j 1)) i

/-- Exact determinant coefficient of an external wedge of arbitrary top
covectors under a pair of linear maps. This includes zero-dimensional factors. -/
theorem evaluate_wedge_top_pullback {p q : ℕ}
    (L : ModelData.Euclidean (p+q) →ₗ[ℝ] ModelData.Euclidean p)
    (K : ModelData.Euclidean (p+q) →ₗ[ℝ] ModelData.Euclidean q)
    (α : Fiber (ModelData.Euclidean p) p) (β : Fiber (ModelData.Euclidean q) q) :
    evaluate (ModelData.Euclidean (p+q)) (p+q)
      (wedge (exteriorPower.map p L.dualMap α) (exteriorPower.map q K.dualMap β))
      (fun i => Pi.single i 1) =
      (orderedProductJacobian L K).det *
        evaluate (ModelData.Euclidean p) p α (fun i => Pi.single i 1) *
        evaluate (ModelData.Euclidean q) q β (fun i => Pi.single i 1) := by
  have hα := topCovector_eq_coefficient p α
  have hβ := topCovector_eq_coefficient q β
  conv_lhs => rw [hα, hβ]
  simp only [map_smul, LinearMap.smul_apply, AlternatingMap.smul_apply]
  rw [standardTopCovector, standardTopCovector, exteriorPower.map_apply_ιMulti,
    exteriorPower.map_apply_ιMulti, ExteriorAlgebraResults.wedge_decomposable,
    ExteriorAlgebraResults.determinant_normalization]
  have hmat : Matrix.of (fun i j : Fin (p+q) =>
      Fin.append (L.dualMap ∘ (fun a : Fin p => LinearMap.proj a))
        (K.dualMap ∘ (fun b : Fin q => LinearMap.proj b)) i (Pi.single j 1)) =
      orderedProductJacobian L K := by
    ext i j
    refine Fin.addCases ?_ ?_ i
    · intro a
      simp [orderedProductJacobian, LinearMap.dualMap_apply']
    · intro b
      simp [orderedProductJacobian, LinearMap.dualMap_apply']
  rw [hmat]
  simp only [smul_eq_mul]
  ring

open P202Specs.DeRhamComparison P202Specs.DeRhamRing
open P202Specs.SmoothSingularComparison P202Specs.SingularChains P202Specs.ShuffleModel

/-- The derivative matrix of an ordered simplex map fixing its zeroth vertex. -/
def reparametrizationMatrix {r k : ℕ} (θ : Fin (r+1) → Fin (k+1)) :
    Matrix (Fin k) (Fin r) ℝ :=
  fun i j => if θ j.succ = i.succ then 1 else 0

theorem ambientReparametrization_eq_linear {r k : ℕ}
    (θ : Fin (r+1) → Fin (k+1)) (hθ : θ 0 = 0) :
    ambientReparametrization θ = (reparametrizationMatrix θ).mulVecLin.toContinuousLinearMap := by
  funext y i
  simp only [ambientReparametrization, ambientMap, Finset.sum_filter, Fin.sum_univ_succ,
    CornerData.simplexBarycentric, Fin.cons_zero, Fin.cons_succ, hθ]
  have hi : (0 : Fin (k+1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
  simp [reparametrizationMatrix, Matrix.mulVec, dotProduct, ite_mul, hi]

theorem fderiv_ambientReparametrization {r k : ℕ}
    (θ : Fin (r+1) → Fin (k+1)) (hθ : θ 0 = 0) (x : ModelData.Euclidean r) :
    fderiv ℝ (ambientReparametrization θ) x =
      (reparametrizationMatrix θ).mulVecLin.toContinuousLinearMap := by
  rw [ambientReparametrization_eq_linear θ hθ]
  exact ContinuousLinearMap.fderiv _

/-- The Jacobian of the actual two affine shuffle coordinates is exactly the
accepted ordered vertex-difference orientation matrix. -/
theorem orderedProductJacobian_shuffle {p q : ℕ} (s : LatticePath p q)
    (x : ModelData.Euclidean (p+q)) :
    orderedProductJacobian
      (fderiv ℝ (ambientReparametrization s.horizontal) x).toLinearMap
      (fderiv ℝ (ambientReparametrization s.vertical) x).toLinearMap =
        P202Specs.ShuffleTriangulation.standardOrientationMatrix s := by
  rw [fderiv_ambientReparametrization s.horizontal (P202.ShuffleModel.path_initial s).1,
    fderiv_ambientReparametrization s.vertical (P202.ShuffleModel.path_initial s).2]
  ext i j
  refine Fin.addCases ?_ ?_ i
  · intro a
    simp [orderedProductJacobian, reparametrizationMatrix,
      P202Specs.ShuffleTriangulation.standardOrientationMatrix,
      P202Specs.ShuffleTriangulation.standardProductCoordinates, vertex, weights,
      (P202.ShuffleModel.path_initial s).1, (P202.ShuffleModel.path_initial s).2,
      a.isLt, Finsupp.single_apply, eq_comm]
    simp [Fin.ext_iff, eq_comm]
  · intro b
    simp [orderedProductJacobian, reparametrizationMatrix,
      P202Specs.ShuffleTriangulation.standardOrientationMatrix,
      P202Specs.ShuffleTriangulation.standardProductCoordinates, vertex, weights,
      (P202.ShuffleModel.path_initial s).1, (P202.ShuffleModel.path_initial s).2,
      Nat.not_lt.mpr (Nat.le_add_right p b.val), Finsupp.single_apply, eq_comm]
    simp [Fin.ext_iff, eq_comm]

/-- Therefore the actual differential has the exact prescribed product sign. -/
theorem det_orderedProductJacobian_shuffle {p q : ℕ} (s : LatticePath p q)
    (x : ModelData.Euclidean (p+q)) :
    (orderedProductJacobian
      (fderiv ℝ (ambientReparametrization s.horizontal) x).toLinearMap
      (fderiv ℝ (ambientReparametrization s.vertical) x).toLinearMap).det = (s.sign : ℝ) := by
  rw [orderedProductJacobian_shuffle]
  exact P202.ShuffleTriangulation.standard_orientation s

/-- The determinant formula also applies to covectors in arbitrary intrinsic
fibers once their separate simplex differentials have been taken. -/
theorem evaluate_external_linear_pullback {p q : ℕ}
    {V W : Type u} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (D : ModelData.Euclidean p →ₗ[ℝ] V) (E : ModelData.Euclidean q →ₗ[ℝ] W)
    (L : ModelData.Euclidean (p+q) →ₗ[ℝ] ModelData.Euclidean p)
    (K : ModelData.Euclidean (p+q) →ₗ[ℝ] ModelData.Euclidean q)
    (α : Fiber V p) (β : Fiber W q) :
    evaluate (ModelData.Euclidean (p+q)) (p+q)
      (wedge (exteriorPower.map p (D.comp L).dualMap α)
        (exteriorPower.map q (E.comp K).dualMap β)) (fun i => Pi.single i 1) =
      (orderedProductJacobian L K).det *
        evaluate V p α (fun i => D (Pi.single i 1)) *
        evaluate W q β (fun i => E (Pi.single i 1)) := by
  simp only [← LinearMap.dualMap_comp_dualMap, exteriorPower.map_comp, LinearMap.comp_apply]
  rw [evaluate_wedge_top_pullback]
  rw [show evaluate (ModelData.Euclidean p) p (exteriorPower.map p D.dualMap α)
      (fun i => Pi.single i 1) = evaluate V p α (fun i => D (Pi.single i 1)) from
    evaluate_exteriorMap p D α (fun i => Pi.single i 1)]
  rw [show evaluate (ModelData.Euclidean q) q (exteriorPower.map q E.dualMap β)
      (fun i => Pi.single i 1) = evaluate W q β (fun i => E (Pi.single i 1)) from
    evaluate_exteriorMap q E β (fun i => Pi.single i 1)]

variable {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
  (T : AtlasData.SmoothManifold m b N)

/-- Literal pointwise coefficient of the external wedge on a common simplex. -/
def externalSimplexCoefficient (C : CotangentBundle S) (A : CotangentBundle T)
    {p q : ℕ} (ω : Field S p) (η : Field T q)
    (σ : SmoothSingularData.SingularSimplex S (p+q))
    (τ : SmoothSingularData.SingularSimplex T (p+q)) (x : CornerSimplex (p+q)) : ℝ :=
  evaluate (ModelData.Euclidean (p+q)) (p+q)
    (wedge (exteriorPower.map p (IntegrationCochainData.simplexDifferential S C σ x).dualMap
      (ω (σ.val x)))
      (exteriorPower.map q (IntegrationCochainData.simplexDifferential T A τ x).dualMap
        (η (τ.val x)))) (fun i => Pi.single i 1)

/-- Linear-map form of the intrinsic chain rule on the exact precomposed
P104 simplex, keeping transport of its tangent base point definitional. -/
theorem precomposed_simplexDifferential (C : CotangentBundle S)
    {r k : ℕ} (θ : Fin (r+1) → Fin (k+1)) (σ : SmoothSimplex S k)
    (x : CornerSimplex r) :
    IntegrationCochainData.simplexDifferential S C
      ⟨(p104Simplex S σ).val ∘ cornerReparametrization θ,
        SmoothSingular.smooth_precompose σ.property
          (cornerReparametrization θ) (ambientReparametrization θ)
          (ambientReparametrization_smooth θ) (cornerReparametrization_val θ)⟩ x =
      (IntegrationCochainData.simplexDifferential S C (p104Simplex S σ)
        (cornerReparametrization θ x)).comp
        (fderiv ℝ (ambientReparametrization θ) x.val).toLinearMap := by
  apply LinearMap.ext
  intro v
  exact SimplexPullbackIntegral.simplexDifferential_precompose (C := C)
    (p104Simplex S σ) (cornerReparametrization θ) (ambientReparametrization θ)
    (ambientReparametrization_smooth θ) (cornerReparametrization_val θ) _ x v

/-- Pointwise external wedge coefficient on a genuine affine shuffle cell,
with exactly the stipulated product orientation and no exceptional corners. -/
theorem external_shuffle_pullback_coefficient (C : CotangentBundle S) (A : CotangentBundle T)
    {p q : ℕ} (ω : Field S p) (η : Field T q) (s : LatticePath p q)
    (σ : SmoothSimplex S p) (τ : SmoothSimplex T q) (x : CornerSimplex (p+q)) :
    externalSimplexCoefficient S T C A (p := p) (q := q) ω η
      (p104Simplex S (reparametrizedSmoothSimplex S s.horizontal σ))
      (p104Simplex T (reparametrizedSmoothSimplex T s.vertical τ)) x =
      (s.sign : ℝ) * IntegrationCochainData.pullbackCoefficient S C ω (p104Simplex S σ)
        (cornerReparametrization s.horizontal x) *
        IntegrationCochainData.pullbackCoefficient T A η (p104Simplex T τ)
          (cornerReparametrization s.vertical x) := by
  rw [p104Simplex_reparametrized S s.horizontal σ,
    p104Simplex_reparametrized T s.vertical τ]
  let F
      (D : ModelData.Euclidean (p+q) →ₗ[ℝ]
        TangentData.TangentSpace S ((p104Simplex S σ).val (cornerReparametrization s.horizontal x)))
      (E : ModelData.Euclidean (p+q) →ₗ[ℝ]
        TangentData.TangentSpace T ((p104Simplex T τ).val (cornerReparametrization s.vertical x))) : ℝ :=
    evaluate (ModelData.Euclidean (p+q)) (p+q)
      (wedge (exteriorPower.map p D.dualMap
          (ω ((p104Simplex S σ).val (cornerReparametrization s.horizontal x))))
        (exteriorPower.map q E.dualMap
          (η ((p104Simplex T τ).val (cornerReparametrization s.vertical x)))))
      (fun i => Pi.single i 1)
  have hcoeff := congrArg₂ F (precomposed_simplexDifferential S C s.horizontal σ x)
    (precomposed_simplexDifferential T A s.vertical τ x)
  have hh := evaluate_external_linear_pullback (p := p) (q := q)
    (V := TangentData.TangentSpace S ((p104Simplex S σ).val (cornerReparametrization s.horizontal x)))
    (W := TangentData.TangentSpace T ((p104Simplex T τ).val (cornerReparametrization s.vertical x)))
    (IntegrationCochainData.simplexDifferential S C (p104Simplex S σ)
      (cornerReparametrization s.horizontal x))
    (IntegrationCochainData.simplexDifferential T A (p104Simplex T τ)
      (cornerReparametrization s.vertical x))
    (fderiv ℝ (ambientReparametrization s.horizontal) x.val).toLinearMap
    (fderiv ℝ (ambientReparametrization s.vertical) x.val).toLinearMap
    (ω ((p104Simplex S σ).val (cornerReparametrization s.horizontal x)))
    (η ((p104Simplex T τ).val (cornerReparametrization s.vertical x)))
  rw [det_orderedProductJacobian_shuffle] at hh
  simpa only [F, externalSimplexCoefficient, IntegrationCochainData.pullbackCoefficient,
    Function.comp_apply] using hcoeff.trans hh

/-- Each literal P104 affine-cell integral is its orientation sign times the
integral of the separated pullback coefficients along the common affine map. -/
theorem productSimplexIntegral_shuffle_cell (C : CotangentBundle S) (A : CotangentBundle T)
    {p q : ℕ} (ω : Field S p) (η : Field T q) (s : LatticePath p q)
    (σ : SmoothSimplex S p) (τ : SmoothSimplex T q) :
    productSimplexIntegral S T C A (p := p) (q := q) (r := p+q) ω η
      (p104Simplex S (reparametrizedSmoothSimplex S s.horizontal σ))
      (p104Simplex T (reparametrizedSmoothSimplex T s.vertical τ)) rfl =
      (s.sign : ℝ) * ∫ y in CornerData.simplexSet (p+q),
        IntegrationCochainData.ambientPullbackCoefficient S C ω (p104Simplex S σ)
          (ambientReparametrization s.horizontal y) *
        IntegrationCochainData.ambientPullbackCoefficient T A η (p104Simplex T τ)
          (ambientReparametrization s.vertical y) := by
  unfold productSimplexIntegral
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun
    (SimplexPullbackIntegral.simplex_isCompact (p+q)).measurableSet
  intro y hy
  dsimp only
  rw [dif_pos hy]
  change externalSimplexCoefficient S T C A (p := p) (q := q) ω η
    (p104Simplex S (reparametrizedSmoothSimplex S s.horizontal σ))
    (p104Simplex T (reparametrizedSmoothSimplex T s.vertical τ)) ⟨y,hy⟩ = _
  rw [external_shuffle_pullback_coefficient S T C A ω η s σ τ ⟨y,hy⟩]
  rw [← cornerReparametrization_val s.horizontal ⟨y,hy⟩,
    ← cornerReparametrization_val s.vertical ⟨y,hy⟩]
  simp only [IntegrationCochainData.ambientPullbackCoefficient,
    dif_pos (cornerReparametrization s.horizontal ⟨y,hy⟩).property,
    dif_pos (cornerReparametrization s.vertical ⟨y,hy⟩).property]
  simp only [mul_assoc]

/-- The prescribed shuffle orientation signs square to one over the reals. -/
theorem shuffleSign_mul_self {p q : ℕ} (s : LatticePath p q) :
    (s.sign : ℝ) * (s.sign : ℝ) = 1 := by
  dsimp only [LatticePath.sign]
  exact_mod_cast Int.units_coe_mul_self (Equiv.Perm.sign s.permutation)

/-- The full product-shuffle integral formula for arbitrary finite smooth
chains and smooth intrinsic forms, with all boundary/corner cases retained. -/
theorem productShuffleIntegral_smoothForms (C : CotangentBundle S) (A : CotangentBundle T)
    {p q : ℕ} (B : FormBundle C p) (E : FormBundle A q)
    (ω : Field S p) (η : Field T q) (hω : IsForm B ω) (hη : IsForm E η)
    (z : P202Specs.SmoothSingularComparison.smoothModule S p)
    (w : P202Specs.SmoothSingularComparison.smoothModule T q) :
    externalIntegralCochain S T C A ω η
      (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q
        (z.val ⊗ₜ[ℝ] w.val)) =
      integralCochain S C ω z.val * integralCochain T A η w.val := by
  apply productShuffleIntegral_chains_of_basis S T C A ω η
  intro σ τ
  rw [productShuffleIntegral_basis_sum S T C A ω η σ τ]
  have hh := simplexIntegral_product_shuffleCells S T C A B E ω η hω hη
    (p104Simplex S σ) (p104Simplex T τ)
  simp only [shuffleCellLinear_apply, Fin.append_left, Fin.append_right] at hh
  calc
    _ = ∑ s : LatticePath p q, ∫ y in CornerData.simplexSet (p+q),
        IntegrationCochainData.ambientPullbackCoefficient S C ω (p104Simplex S σ)
          (ambientReparametrization s.horizontal y) *
        IntegrationCochainData.ambientPullbackCoefficient T A η (p104Simplex T τ)
          (ambientReparametrization s.vertical y) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [productSimplexIntegral_shuffle_cell S T C A ω η s σ τ,
        ← mul_assoc, shuffleSign_mul_self, one_mul]
    _ = IntegrationCochainData.simplexIntegral S C ω (p104Simplex S σ) *
        IntegrationCochainData.simplexIntegral T A η (p104Simplex T τ) := hh
    _ = _ := by
      simp [integralCochain, σ.property, τ.property]

/-- The original analytic component on all closed forms and all smooth cycles.
This theorem needs no comparison-isomorphism premise. -/
theorem productShuffleIntegral : P202Specs.DeRhamRing.productShuffleIntegral_type.{u} := by
  intro n m a b M N _ _ S T C A B E K J p q ω η z w
  exact productShuffleIntegral_smoothForms S T C A (B p) (E q) ω.val.val η.val.val
    ((K.mem_forms p ω.val.val).mp ω.val.property)
    ((J.mem_forms q η.val.val).mp η.val.property)
    ((P202Specs.SmoothSingularComparison.smoothComplex S).iCycles p z)
    ((P202Specs.SmoothSingularComparison.smoothComplex T).iCycles q w)

end ShuffleCoefficients

section ExternalPullbackIntegral
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations

theorem exteriorPullback_comp {V : Type u} {W : Type v} {Z : Type w}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z] (k : ℕ)
    (D : V →ₗ[ℝ] W) (L : W →ₗ[ℝ] Z) (α : Fiber Z k) :
    exteriorPower.map k (L.comp D).dualMap α =
      exteriorPower.map k D.dualMap (exteriorPower.map k L.dualMap α) := by
  change exteriorPower.map k (D.dualMap.comp L.dualMap) α = _
  rw [exteriorPower.map_comp]
  rfl

/-- Integration of the intrinsic exterior form on a genuine product manifold
agrees with the factorwise common-simplex integral used in the independent
shuffle specification. The product structure is witnessed by actual smooth
projections and their actual differentials. -/
theorem simplexIntegral_external_pullbacks
    {n m l : ℕ} {a b c : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
    (R : AtlasData.SmoothManifold l c (M × N))
    (C : CotangentBundle S) (A : CotangentBundle T) (V : CotangentBundle R)
    (hf : MapData.IsSmoothMap R S Prod.fst) (hg : MapData.IsSmoothMap R T Prod.snd)
    (Lf : ∀ z : M × N, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace S z.1)
    (Lg : ∀ z : M × N, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace T z.2)
    (hLf : ∀ z, DifferentialData.IsDifferential R S Prod.fst z (Lf z))
    (hLg : ∀ z, DifferentialData.IsDifferential R T Prod.snd z (Lg z))
    {p q : ℕ} (ω : Field S p) (η : Field T q)
    (σ : SmoothSingularData.SingularSimplex R (p+q)) :
    IntegrationCochainData.simplexIntegral R V
      (fieldWedge (FormPullbackData.pullbackField R S Prod.fst Lf ω)
        (FormPullbackData.pullbackField R T Prod.snd Lg η)) σ =
      productSimplexIntegral S T C A ω η
        ⟨Prod.fst ∘ σ.val, SmoothSingular.smooth_postcompose hf σ.property⟩
        ⟨Prod.snd ∘ σ.val, SmoothSingular.smooth_postcompose hg σ.property⟩ rfl := by
  unfold IntegrationCochainData.simplexIntegral productSimplexIntegral
  congr 1
  funext y
  simp only [IntegrationCochainData.ambientPullbackCoefficient]
  split_ifs with hy
  · let x : SmoothSingularData.Simplex (p+q) := ⟨y,hy⟩
    let D := IntegrationCochainData.simplexDifferential R V σ x
    have h₁ : IntegrationCochainData.simplexDifferential S C
        ⟨Prod.fst ∘ σ.val, SmoothSingular.smooth_postcompose hf σ.property⟩ x =
          (Lf (σ.val x)).comp D := by
      apply LinearMap.ext
      intro v
      exact SimplexPullbackIntegral.simplexDifferential_postcompose (C := V) S C σ Prod.fst hf Lf hLf
        (SmoothSingular.smooth_postcompose hf σ.property) x v
    have h₂ : IntegrationCochainData.simplexDifferential T A
        ⟨Prod.snd ∘ σ.val, SmoothSingular.smooth_postcompose hg σ.property⟩ x =
          (Lg (σ.val x)).comp D := by
      apply LinearMap.ext
      intro v
      exact SimplexPullbackIntegral.simplexDifferential_postcompose (C := V) T A σ Prod.snd hg Lg hLg
        (SmoothSingular.smooth_postcompose hg σ.property) x v
    change IntegrationCochainData.pullbackCoefficient R V
      (fieldWedge (FormPullbackData.pullbackField R S Prod.fst Lf ω)
        (FormPullbackData.pullbackField R T Prod.snd Lg η)) σ x = _
    simp only [Fin.cast_refl, id_eq]
    have hm₁ := congrArg
      (fun D' : ModelData.Euclidean (p+q) →ₗ[ℝ] TangentData.TangentSpace S (σ.val x).1 =>
        exteriorPower.map p D'.dualMap (ω (σ.val x).1)) h₁
    have hm₂ := congrArg
      (fun D' : ModelData.Euclidean (p+q) →ₗ[ℝ] TangentData.TangentSpace T (σ.val x).2 =>
        exteriorPower.map q D'.dualMap (η (σ.val x).2)) h₂
    let α := exteriorPower.map p (Lf (σ.val x)).dualMap (ω (σ.val x).1)
    let β := exteriorPower.map q (Lg (σ.val x)).dualMap (η (σ.val x).2)
    have hc₁ := exteriorPullback_comp
      (V := ModelData.Euclidean (p+q)) (W := TangentData.TangentSpace R (σ.val x))
      (Z := TangentData.TangentSpace S (σ.val x).1)
      p D (Lf (σ.val x)) (ω (σ.val x).1)
    have hc₂ := exteriorPullback_comp
      (V := ModelData.Euclidean (p+q)) (W := TangentData.TangentSpace R (σ.val x))
      (Z := TangentData.TangentSpace T (σ.val x).2)
      q D (Lg (σ.val x)) (η (σ.val x).2)
    have hw : wedge (V := ModelData.Euclidean (p+q))
        (exteriorPower.map p (IntegrationCochainData.simplexDifferential S C
          ⟨Prod.fst ∘ σ.val, SmoothSingular.smooth_postcompose hf σ.property⟩ x).dualMap
          (ω (σ.val x).1))
        (exteriorPower.map q (IntegrationCochainData.simplexDifferential T A
          ⟨Prod.snd ∘ σ.val, SmoothSingular.smooth_postcompose hg σ.property⟩ x).dualMap
          (η (σ.val x).2)) = exteriorPower.map (p+q) D.dualMap
            (wedge (V := TangentData.TangentSpace R (σ.val x)) α β) := by
      calc
        _ = wedge (V := ModelData.Euclidean (p+q))
            (exteriorPower.map p ((Lf (σ.val x)).comp D).dualMap (ω (σ.val x).1))
            (exteriorPower.map q ((Lg (σ.val x)).comp D).dualMap (η (σ.val x).2)) :=
          congrArg₂ (fun (a : Fiber (ModelData.Euclidean (p+q)) p)
                (b : Fiber (ModelData.Euclidean (p+q)) q) =>
                  wedge (V := ModelData.Euclidean (p+q)) a b) hm₁ hm₂
        _ = wedge (V := ModelData.Euclidean (p+q))
            (exteriorPower.map p D.dualMap α) (exteriorPower.map q D.dualMap β) :=
          congrArg₂ (fun (a : Fiber (ModelData.Euclidean (p+q)) p)
                (b : Fiber (ModelData.Euclidean (p+q)) q) =>
                  wedge (V := ModelData.Euclidean (p+q)) a b)
            hc₁ hc₂
        _ = _ := (ExteriorAlgebraResults.map_wedge D.dualMap α β).symm
    have hv := congrArg
      (fun γ : Fiber (ModelData.Euclidean (p+q)) (p+q) =>
        evaluate (ModelData.Euclidean (p+q)) (p+q) γ (fun i => Pi.single i 1)) hw
    have he := evaluate_exteriorMap
      (V := ModelData.Euclidean (p+q)) (W := TangentData.TangentSpace R (σ.val x))
      (p+q) D
      (wedge (V := TangentData.TangentSpace R (σ.val x))
        (exteriorPower.map p (Lf (σ.val x)).dualMap (ω (σ.val x).1))
        (exteriorPower.map q (Lg (σ.val x)).dualMap (η (σ.val x).2)))
      (fun i => Pi.single i 1)
    have hfinal := he.symm.trans hv.symm
    simpa only [IntegrationCochainData.pullbackCoefficient, fieldWedge,
      FormPullbackData.pullbackField, FormPullbackData.fiberPullback, D, x,
      Function.comp_apply] using hfinal

  · rfl

end ExternalPullbackIntegral

section ExternalOffDiagonal
open P202Specs.SmoothSingularComparison P202Specs.SingularChains P202Specs.ShuffleModel
open P202Specs.AlexanderWhitney

/-- Changing a simplex's degree index transports only its ordered source
vertices; the represented affine map is unchanged. -/
theorem cast_reparametrizedSimplex {X : TopCat.{u}} {r d k : ℕ} (h : r = d)
    (θ : Fin (r+1) → Fin (k+1)) (σ : Simplex X k) :
    P202.ShuffleBoundary.castSimplex h (reparametrizedSimplex θ σ) =
      reparametrizedSimplex (θ ∘ finCongr (congrArg (·+1) h.symm)) σ := by
  subst d
  simp [P202.ShuffleBoundary.castSimplex]

/-- Both projections of a degree-transported shuffle retain the exact affine
factor maps, now indexed by the target degree. -/
theorem cast_shuffle_first_reparametrized {X Y : TopCat.{u}} {k l d : ℕ}
    (h : k+l=d) (s : LatticePath k l) (σ : Simplex X k) (τ : Simplex Y l) :
    postSimplex (firstProjection X Y) d
      (P202.ShuffleBoundary.castSimplex h (shuffleSimplex s σ τ)) =
      reparametrizedSimplex (s.horizontal ∘ finCongr (congrArg (·+1) h.symm)) σ := by
  rw [← P202.ShuffleBoundary.castSimplex_postSimplex,
    shuffle_first_reparametrized, cast_reparametrizedSimplex]

theorem cast_shuffle_second_reparametrized {X Y : TopCat.{u}} {k l d : ℕ}
    (h : k+l=d) (s : LatticePath k l) (σ : Simplex X k) (τ : Simplex Y l) :
    postSimplex (secondProjection X Y) d
      (P202.ShuffleBoundary.castSimplex h (shuffleSimplex s σ τ)) =
      reparametrizedSimplex (s.vertical ∘ finCongr (congrArg (·+1) h.symm)) τ := by
  rw [← P202.ShuffleBoundary.castSimplex_postSimplex,
    shuffle_second_reparametrized, cast_reparametrizedSimplex]

variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)

/-- The literal external integral on a transported cell has the actual smooth
factorwise affine pullbacks, also in off-diagonal bidegrees. -/
theorem externalIntegral_cast_shuffle_simplex (C : CotangentBundle S) (A : CotangentBundle T)
    {p q k l : ℕ} (h : k+l=p+q) (ω : Field S p) (η : Field T q)
    (s : LatticePath k l) (σ : SmoothSimplex S k) (τ : SmoothSimplex T l) :
    externalIntegralCochain S T C A ω η
      (Finsupp.single (P202.ShuffleBoundary.castSimplex h (shuffleSimplex s σ.val τ.val)) 1) =
      productSimplexIntegral S T C A (p := p) (q := q) (r := p+q) ω η
        (p104Simplex S (reparametrizedSmoothSimplex S
          (s.horizontal ∘ finCongr (congrArg (·+1) h.symm)) σ))
        (p104Simplex T (reparametrizedSmoothSimplex T
          (s.vertical ∘ finCongr (congrArg (·+1) h.symm)) τ)) rfl := by
  simp only [externalIntegralCochain, Finsupp.linearCombination_single, one_smul,
    cast_shuffle_first_reparametrized, cast_shuffle_second_reparametrized]
  rw [dif_pos (reparametrizedSimplex_smooth S
      (s.horizontal ∘ finCongr (congrArg (·+1) h.symm)) σ),
    dif_pos (reparametrizedSimplex_smooth T
      (s.vertical ∘ finCongr (congrArg (·+1) h.symm)) τ)]
  rfl

/-- Every actual oriented shuffle cell of the wrong bidegree has zero
external integral, including cells meeting manifold boundary strata. -/
theorem externalIntegral_cast_shuffle_simplex_offDiagonal
    (C : CotangentBundle S) (A : CotangentBundle T)
    {p q k l : ℕ} (h : k+l=p+q) (hne : k ≠ p ∨ l ≠ q)
    (ω : Field S p) (η : Field T q)
    (s : LatticePath k l) (σ : SmoothSimplex S k) (τ : SmoothSimplex T l) :
    externalIntegralCochain S T C A ω η
      (Finsupp.single (P202.ShuffleBoundary.castSimplex h (shuffleSimplex s σ.val τ.val)) 1) = 0 := by
  rw [externalIntegral_cast_shuffle_simplex S T C A h ω η s σ τ]
  apply productSimplexIntegral_affine_offDiagonal S T C A
  omega

/-- The complete off-diagonal formula for the signed shuffle on smooth basis
pairs, with the precise degree transport used in Künneth. -/
theorem externalIntegral_shuffle_basis_offDiagonal
    (C : CotangentBundle S) (A : CotangentBundle T)
    {p q k l : ℕ} (h : k+l=p+q) (hne : k ≠ p ∨ l ≠ q)
    (ω : Field S p) (η : Field T q) (σ : SmoothSimplex S k) (τ : SmoothSimplex T l) :
    externalIntegralCochain S T C A ω η
      (castChains ℝ h (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) k l
        (Finsupp.single σ.val 1 ⊗ₜ[ℝ] Finsupp.single τ.val 1))) = 0 := by
  rw [P202.ShuffleChains.component_formula]
  simp only [mul_one, one_smul, map_sum, map_zsmul, P202.ShuffleBoundary.castChains_single]
  apply Finset.sum_eq_zero
  intro s _
  rw [externalIntegral_cast_shuffle_simplex_offDiagonal S T C A h hne ω η s σ τ]
  simp

/-- The external integral vanishes on every finite smooth product chain in a
bidegree other than the two form degrees. No closure or finite-rank hypothesis
is needed, so this applies directly to all product homology cycles. -/
theorem externalIntegral_shuffle_offDiagonal
    (C : CotangentBundle S) (A : CotangentBundle T)
    {p q k l : ℕ} (h : k+l=p+q) (hne : k ≠ p ∨ l ≠ q)
    (ω : Field S p) (η : Field T q)
    (z : P202Specs.SmoothSingularComparison.smoothModule S k)
    (w : P202Specs.SmoothSingularComparison.smoothModule T l) :
    externalIntegralCochain S T C A ω η
      (castChains ℝ h (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) k l
        (z.val ⊗ₜ[ℝ] w.val))) = 0 := by
  let L := TensorProduct.curry (((externalIntegralCochain S T C A ω η).comp
    (castChains ℝ h)).comp
      (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) k l))
  have hw : ∀ σ : SmoothSimplex S k, L (Finsupp.single σ.val 1) w.val = 0 := by
    intro σ
    apply LinearMap.eqOn_span (g := 0)
      (s := (fun τ => Finsupp.single τ (1 : ℝ)) '' {τ | IsSmoothSimplex T l τ})
    · intro y hy
      obtain ⟨τ,hτ,rfl⟩ := hy
      exact externalIntegral_shuffle_basis_offDiagonal S T C A h hne ω η σ ⟨τ,hτ⟩
    · rw [← Finsupp.supported_eq_span_single]
      exact w.property
  change L z.val w.val = 0
  apply LinearMap.eqOn_span (f := L.flip w.val) (g := 0)
    (s := (fun σ => Finsupp.single σ (1 : ℝ)) '' {σ | IsSmoothSimplex S k σ})
  · intro y hy
    obtain ⟨σ,hσ,rfl⟩ := hy
    exact hw ⟨σ,hσ⟩
  · rw [← Finsupp.supported_eq_span_single]
    exact z.property

end ExternalOffDiagonal

section ExteriorAssembly
open P202Specs.SmoothSingularComparison P202Specs.SingularChains
open P202Specs.CohomologyPairs P202Specs.CupProduct P202Specs.AlexanderWhitney
open P202Specs.EilenbergZilber P202Specs.TopologicalKunneth

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)

theorem smoothCycle_lift {q : ℕ} (z : (complex ℝ ℝ (TopCat.of M)).cycles q)
    (hz : (complex ℝ ℝ (TopCat.of M)).iCycles q z ∈ smoothModule S q) :
    ∃ w : (smoothComplex S).cycles q, cyclesMap (inclusion S) q w = z := by
  let j := (ComplexShape.down ℕ).next q
  let v : smoothModule S q := ⟨(complex ℝ ℝ (TopCat.of M)).iCycles q z, hz⟩
  have hv : (smoothComplex S).d q j v = 0 := by
    have hinj : Function.Injective ((inclusion S).f j) := Subtype.val_injective
    apply hinj
    rw [map_zero]
    have hc := congrArg (fun f => f.hom v) ((inclusion S).comm q j)
    change (complex ℝ ℝ (TopCat.of M)).d q j ((inclusion S).f q v) =
      (inclusion S).f j ((smoothComplex S).d q j v) at hc
    rw [← hc]
    change (complex ℝ ℝ (TopCat.of M)).d q j
      ((complex ℝ ℝ (TopCat.of M)).iCycles q z) = 0
    exact congrArg (fun f => f.hom z)
      ((complex ℝ ℝ (TopCat.of M)).iCycles_d q j)
  let w := (smoothComplex S).cyclesMk v j rfl hv
  refine ⟨w, ?_⟩
  apply (ModuleCat.mono_iff_injective ((complex ℝ ℝ (TopCat.of M)).iCycles q)).mp inferInstance
  have hw : (smoothComplex S).iCycles q w = v := by
    change ((smoothComplex S).iCycles q).hom w = v
    simpa only [ModuleCat.forget₂_map, ModuleCat.forget₂_obj,
      ConcreteCategory.hom, ConcreteCategory.ofHom, AddCommGrpCat.ofHom,
      AddMonoidHom.coe_ofClass, LinearMap.toAddMonoidHom, LinearMap.toAddMonoidHom_coe,
      LinearMap.coe_toAddHom, w] using (smoothComplex S).i_cyclesMk v j rfl hv
  change (complex ℝ ℝ (TopCat.of M)).iCycles q (cyclesMap (inclusion S) q w) = _
  have hc := congrArg (fun f => f.hom w) (cyclesMap_i (inclusion S) q)
  change (complex ℝ ℝ (TopCat.of M)).iCycles q (cyclesMap (inclusion S) q w) =
    (inclusion S).f q ((smoothComplex S).iCycles q w) at hc
  rw [hc, hw]
  rfl

theorem smoothInclusion_nonnegative_class {q : ℕ} (z : (smoothComplex S).cycles q) :
    homologyMap (ordinaryInclusion S) (q : ℤ)
      ((smoothOrdinaryComplex S).homologyπ (q : ℤ)
        (((smoothComplex S).extendCyclesIso (degreeEmbedding 0)
          (show (degreeEmbedding 0).f q = (q : ℤ) by simp [degreeEmbedding])).inv z)) =
    (ordinaryHomologyIso ℝ (TopCat.of M) q).inv
      ((complex ℝ ℝ (TopCat.of M)).homologyπ q (cyclesMap (inclusion S) q z)) := by
  let hq : (degreeEmbedding 0).f q = (q : ℤ) := by simp [degreeEmbedding]
  let E := (smoothComplex S).extendCyclesIso (degreeEmbedding 0) hq
  let H := (smoothComplex S).extendHomologyIso (degreeEmbedding 0) hq
  have hπ := congrArg (fun f => f.hom z)
    ((smoothComplex S).homologyπ_extendHomologyIso_inv (degreeEmbedding 0) hq)
  change H.inv ((smoothComplex S).homologyπ q z) =
    (smoothOrdinaryComplex S).homologyπ (q : ℤ) (E.inv z) at hπ
  change homologyMap (ordinaryInclusion S) (q : ℤ)
    ((smoothOrdinaryComplex S).homologyπ (q : ℤ) (E.inv z)) = _
  rw [← hπ]
  have hn := congrArg (fun f => f.hom (H.inv ((smoothComplex S).homologyπ q z)))
    (extendHomologyIso_hom_naturality (inclusion S) (degreeEmbedding 0) hq)
  change (ordinaryHomologyIso ℝ (TopCat.of M) q).hom
    (homologyMap (ordinaryInclusion S) (q : ℤ) (H.inv ((smoothComplex S).homologyπ q z))) =
      homologyMap (inclusion S) q (H.hom (H.inv ((smoothComplex S).homologyπ q z))) at hn
  rw [ModuleCat.hom_inv_apply] at hn
  have hn' := congrArg ((ordinaryHomologyIso ℝ (TopCat.of M) q).inv) hn
  rw [ModuleCat.inv_hom_apply] at hn'
  rw [hn']
  exact congrArg ((ordinaryHomologyIso ℝ (TopCat.of M) q).inv)
    (congrArg (fun f => f.hom z) (homologyπ_naturality (inclusion S) q))

theorem integrationClass_nonnegative_evaluation (C : CotangentBundle S) {q : ℕ}
    (ω : Field S q) (x : ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ))
    (hx : IsIntegrationClass S C ω x) (z : (smoothComplex S).cycles q) :
    P202Specs.UniversalCoefficients.evaluation ℝ ℝ
      (ordinaryComplex ℝ ℝ (TopCat.of M)) (q : ℤ) x
      ((ordinaryHomologyIso ℝ (TopCat.of M) q).inv
        ((complex ℝ ℝ (TopCat.of M)).homologyπ q (cyclesMap (inclusion S) q z))) =
    integralCochain S C ω ((smoothComplex S).iCycles q z).val := by
  let hq : (degreeEmbedding 0).f q = (q : ℤ) := by simp [degreeEmbedding]
  let E := (smoothComplex S).extendCyclesIso (degreeEmbedding 0) hq
  rw [← smoothInclusion_nonnegative_class S z]
  rw [integrationClass_ordinaryEvaluation S C ω x hx]
  have hi := congrArg (fun f => f.hom z)
    ((smoothComplex S).extendCyclesIso_inv_iCycles (degreeEmbedding 0) hq)
  change (smoothOrdinaryComplex S).iCycles (q : ℤ) (E.inv z) =
    (smoothDegreeIso S q).inv ((smoothComplex S).iCycles q z) at hi
  rw [hi, ModuleCat.hom_inv_apply]


/-- Integration on a native ordinary cycle supported on genuine smooth simplices. -/
theorem integrationClass_smoothChain_evaluation (C : CotangentBundle S) {q : ℕ}
    (ω : Field S q) (x : ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ))
    (hx : IsIntegrationClass S C ω x) (z : (complex ℝ ℝ (TopCat.of M)).cycles q)
    (hz : (complex ℝ ℝ (TopCat.of M)).iCycles q z ∈ smoothModule S q) :
    P202Specs.UniversalCoefficients.evaluation ℝ ℝ
      (ordinaryComplex ℝ ℝ (TopCat.of M)) (q : ℤ) x
      ((ordinaryHomologyIso ℝ (TopCat.of M) q).inv
        ((complex ℝ ℝ (TopCat.of M)).homologyπ q z)) =
    integralCochain S C ω ((complex ℝ ℝ (TopCat.of M)).iCycles q z) := by
  obtain ⟨w, hw⟩ := smoothCycle_lift S z hz
  have he := integrationClass_nonnegative_evaluation S C ω x hx w
  rw [hw] at he
  have hc := congrArg (fun f => f.hom w) (cyclesMap_i (inclusion S) q)
  change (complex ℝ ℝ (TopCat.of M)).iCycles q (cyclesMap (inclusion S) q w) =
    ((smoothComplex S).iCycles q w).val at hc
  rw [hw] at hc
  exact he.trans (congrArg (integralCochain S C ω) hc.symm)

/-- The same integration formula with the exact Künneth degree transport. -/
theorem integrationClass_smoothChain_evaluation_cast (C : CotangentBundle S) {r d : ℕ}
    (h : r=d) (ω : Field S d) (x : ordinaryCohomology ℝ ℝ (TopCat.of M) (d : ℤ))
    (hx : IsIntegrationClass S C ω x) (z : (complex ℝ ℝ (TopCat.of M)).cycles r)
    (hz : P202Specs.ShuffleModel.castChains ℝ h
      ((complex ℝ ℝ (TopCat.of M)).iCycles r z) ∈ smoothModule S d) :
    P202Specs.UniversalCoefficients.evaluation ℝ ℝ
      (ordinaryComplex ℝ ℝ (TopCat.of M)) (d : ℤ) x
      (h ▸ (ordinaryHomologyIso ℝ (TopCat.of M) r).inv
        ((complex ℝ ℝ (TopCat.of M)).homologyπ r z)) =
    integralCochain S C ω (P202Specs.ShuffleModel.castChains ℝ h
      ((complex ℝ ℝ (TopCat.of M)).iCycles r z)) := by
  subst d
  exact integrationClass_smoothChain_evaluation S C ω x hx z hz

variable {m l : ℕ} {b c : ModelKind} {N : Type u} [TopologicalSpace N]
  (T : AtlasData.SmoothManifold m b N)
  (R : AtlasData.SmoothManifold l c (M × N))

theorem integralCochain_external_pullbacks
    (C : CotangentBundle S) (A : CotangentBundle T) (V : CotangentBundle R)
    (hf : MapData.IsSmoothMap R S Prod.fst) (hg : MapData.IsSmoothMap R T Prod.snd)
    (Lf : ∀ z : M × N, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace S z.1)
    (Lg : ∀ z : M × N, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace T z.2)
    (hLf : ∀ z, DifferentialData.IsDifferential R S Prod.fst z (Lf z))
    (hLg : ∀ z, DifferentialData.IsDifferential R T Prod.snd z (Lg z))
    {p q : ℕ} (ω : Field S p) (η : Field T q)
    (z : smoothModule R (p+q)) :
    integralCochain R V
      (fieldWedge (FormPullbackData.pullbackField R S Prod.fst Lf ω)
        (FormPullbackData.pullbackField R T Prod.snd Lg η)) z.val =
      externalIntegralCochain S T C A ω η z.val := by
  have he : (integralCochain R V
      (fieldWedge (FormPullbackData.pullbackField R S Prod.fst Lf ω)
        (FormPullbackData.pullbackField R T Prod.snd Lg η))).comp (smoothModule R (p+q)).subtype =
      (externalIntegralCochain S T C A ω η).comp (smoothModule R (p+q)).subtype := by
    apply smoothFunctional_ext R
    intro σ
    let σf : SmoothSimplex S (p+q) :=
      ⟨postSimplex (firstProjection (TopCat.of M) (TopCat.of N)) (p+q) σ.val,
        SmoothSingular.smooth_postcompose hf σ.property⟩
    let σg : SmoothSimplex T (p+q) :=
      ⟨postSimplex (secondProjection (TopCat.of M) (TopCat.of N)) (p+q) σ.val,
        SmoothSingular.smooth_postcompose hg σ.property⟩
    change integralCochain R V _ (Finsupp.single σ.val 1) =
      externalIntegralCochain S T C A ω η (Finsupp.single σ.val 1)
    simp only [integralCochain, externalIntegralCochain,
      Finsupp.linearCombination_single, one_smul]
    rw [dif_pos σ.property, dif_pos σf.property, dif_pos σg.property]
    exact simplexIntegral_external_pullbacks S T R C A V hf hg Lf Lg hLf hLg
      ω η (p104Simplex R σ)
  exact LinearMap.congr_fun he z

end ExteriorAssembly

section InteriorReduction
open SmoothManifolds.MapData SmoothManifolds.BoundaryData SmoothManifolds.InteriorHomotopyData
open P202Specs.CohomologyPairs P202Specs.CupProduct

/-- A continuous right homotopy inverse for a map makes its ordinary real
cohomology pullback injective in every integer degree. -/
theorem ordinaryPullback_injective_of_rightHomotopyInverse
    {X Y : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (H : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (q : ℤ) :
    Function.Injective ((ordinaryCohomologyFunctor ℝ ℝ q).map f.op) := by
  let F := ordinaryCohomologyFunctor ℝ ℝ q
  have hH := (P202.CohomologyPairs.homotopy_invariant ℝ ℝ).1 H q
  have hi : F.map f.op ≫ F.map g.op = 𝟙 (F.obj (op Y)) := by
    rw [← F.map_comp]
    exact hH.trans (F.map_id (op Y))
  have hleft : Function.LeftInverse (F.map g.op) (F.map f.op) := by
    intro z
    exact congrArg (fun k => k z) hi
  exact hleft.injective

/-- The actual Euclidean-model structure on the full interior has a smooth
inclusion into the original manifold, whose ordinary real cohomology pullback
is injective in every degree, including zero and for empty manifolds. -/
theorem exists_interior_euclidean_pullback_injective
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) :
    ∃ (E : AtlasData.SmoothManifold n .euclidean (BoundaryData.manifoldInterior S))
      (hf : MapData.IsSmoothMap E S (Subtype.val : BoundaryData.manifoldInterior S → M)),
      ∀ q : ℕ, Function.Injective
        (hPullback ℝ (P202Specs.SmoothSingularComparison.underlyingMap E S Subtype.val hf) q) := by
  obtain ⟨R⟩ := SmoothManifolds.InteriorHomotopies.interior_inclusion_homotopy_equivalence S
  obtain ⟨E, _hAE, hES⟩ := SmoothManifolds.SmoothingHomotopies.interior_euclidean_structure S R.isOpen_interior
  refine ⟨E, hES, ?_⟩
  let j := P202Specs.SmoothSingularComparison.underlyingMap E S Subtype.val hES
  let r : TopCat.of M ⟶ TopCat.of (BoundaryData.manifoldInterior S) := TopCat.ofHom
    ⟨R.inverse, continuous_iff_continuousAt.mpr (fun x => (R.smooth_inverse x).1)⟩
  let H : TopCat.Homotopy (𝟙 (TopCat.of M)) (r ≫ j) := {
    toFun := R.homotopy
    continuous_toFun := R.smooth_homotopy.1
    map_zero_left := R.homotopy_zero
    map_one_left := R.homotopy_one }
  intro q
  exact ordinaryPullback_injective_of_rightHomotopyInverse j r H.symm (q : ℤ)

/-- The same boundary reduction carries the actual intrinsic differential
of the inclusion, so it can be used directly with de Rham pullback naturality. -/
theorem exists_interior_euclidean_differential_pullback_injective
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) :
    ∃ (E : AtlasData.SmoothManifold n .euclidean (BoundaryData.manifoldInterior S))
      (hf : MapData.IsSmoothMap E S (Subtype.val : BoundaryData.manifoldInterior S → M))
      (L : ∀ x : BoundaryData.manifoldInterior S,
        TangentData.TangentSpace E x →ₗ[ℝ] TangentData.TangentSpace S x.val),
      (∀ x, DifferentialData.IsDifferential E S Subtype.val x (L x)) ∧
      ∀ q : ℕ, Function.Injective
        (hPullback ℝ (P202Specs.SmoothSingularComparison.underlyingMap E S Subtype.val hf) q) := by
  obtain ⟨E, hf, hinj⟩ := exists_interior_euclidean_pullback_injective S
  refine ⟨E, hf, SmoothManifolds.differential E S Subtype.val hf, ?_, hinj⟩
  intro x
  exact SmoothManifolds.differential_spec E S Subtype.val hf x

/-- Compatibility with multiplication on every Euclidean-model manifold
implies compatibility on every ordinary boundary model, by pulling back to
the actual interior and its Euclidean smooth structure. -/
theorem comparison_mul_boundary_reduction
    (hDR : P202Specs.DeRhamComparison.deRhamComparison_type.{u})
    (U : P202Specs.CupProduct.NaturalCohomologyRing.{0,u} ℝ)
    (hEuclidean : ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
      (S : AtlasData.SmoothManifold n .euclidean M)
      (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
      (P : K.GradedProduct), K.IsGradedProduct P →
      ∀ (e : ComparisonFamily S K), IsIntegrationComparison S K e →
      ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
        e (p+q) (P.mul p q x y) =
          (U.ring (TopCat.of M)).product p q (e p x) (e q y))
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (P : K.GradedProduct) (hP : K.IsGradedProduct P)
    (e : ComparisonFamily S K) (he : IsIntegrationComparison S K e) :
    ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
      e (p+q) (P.mul p q x y) =
        (U.ring (TopCat.of M)).product p q (e p x) (e q y) := by
  obtain ⟨T, hf, L, hL, hinj⟩ := exists_interior_euclidean_differential_pullback_injective S
  obtain ⟨A⟩ := SmoothManifolds.BundleOperations.exists_cotangent T
  let E : ∀ k, FormBundle A k := fun k =>
    Classical.choice (SmoothManifolds.ExteriorAlgebraResults.exists_formBundle A k)
  let J : Calculus A E := Classical.choice (SmoothManifolds.DeRhamResults.complex_exists A E)
  obtain ⟨Q, hQ⟩ := SmoothManifolds.DeRhamResults.product_exists J
  obtain ⟨h, hh⟩ := hDR.1 T A E J
  obtain ⟨F, hF⟩ := SmoothManifolds.DeRhamResults.pullback_exists
    T S A C E B J K Subtype.val hf L hL
  exact comparison_mul_of_pullback_injective hDR U T S A C E B J K Q P hQ hP h e hh he
    Subtype.val hf L hL F hF hinj (hEuclidean T A E J Q hQ h hh)

end InteriorReduction

section SmoothProducts
open SmoothManifolds.MapData SmoothManifolds.ProductData
open Set Filter
open scoped Topology

/-- For a continuous map from the closed corner simplex, one actual smooth
chart extension at each point suffices; compatible transitions give the full
all-charts smoothness predicate. -/
theorem simplexSmooth_of_local_chart
    {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (f : SmoothSingularData.Simplex q → M)
    (hf : Continuous f)
    (h : ∀ x, ∃ e ∈ S.smoothStructure.val, f x ∈ e.source ∧
      MapData.LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val
        (fun y => (e (f y)).val) x) :
    SmoothSingularData.SimplexSmooth S f := by
  refine ⟨hf, ?_⟩
  intro x d hd hdx
  obtain ⟨e, he, hxe, hx⟩ := h x
  have ht := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he d hd) hxe hdx
  have hp := SmoothManifolds.LocalCoordinateExtension.precomp ht hf.continuousAt rfl
  exact SmoothManifolds.LocalCoordinateExtension.comp hp hx

/-- Pairing any two smooth singular simplex maps of the same dimension gives
a smooth simplex in the genuine P104 product smooth structure. All simplex
faces and corners are retained; only actual ProductCoordinates are used. -/
theorem simplexSmooth_pair
    {n m q : ℕ} {a b k : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
    (C : ProductCoordinates n a m b k)
    (P : AtlasData.SmoothManifold (n+m) k (M × N))
    (hP : P.smoothStructure.val = AtlasData.maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val))
    (σ : SmoothSingularData.SingularSimplex S q)
    (τ : SmoothSingularData.SingularSimplex T q) :
    SmoothSingularData.SimplexSmooth P (fun x => (σ.val x, τ.val x)) := by
  apply simplexSmooth_of_local_chart P _ (σ.property.1.prodMk τ.property.1)
  intro x
  obtain ⟨c, hc, hcx⟩ := S.smoothStructure.property.1.1 (σ.val x)
  obtain ⟨d, hd, hdx⟩ := T.smoothStructure.property.1.1 (τ.val x)
  let e := productChart C c d
  have he : e ∈ P.smoothStructure.val := by
    rw [hP]
    apply SmoothManifolds.subset_maximalExtension
      (SmoothManifolds.productAtlas_isContDiffAtlas C (⊤ : ℕ∞)
        S.smoothStructure.val T.smoothStructure.val
        S.smoothStructure.property.1 T.smoothStructure.property.1)
    exact ⟨c,hc,d,hd,rfl⟩
  have hxe : (σ.val x, τ.val x) ∈ e.source := by
    change (σ.val x, τ.val x) ∈ (productChart C c d).source
    rw [(SmoothManifolds.productChart_source_apply C c d).1]
    exact ⟨hcx,hdx⟩
  refine ⟨e,he,hxe,?_⟩
  have h₁ := σ.property.2 x c hc hcx
  have h₂ := τ.property.2 x d hd hdx
  have hh := SmoothManifolds.InteriorHomotopies.extension_combine h₁ h₂
    C.linearEquiv C.linearEquiv.contDiff
  convert hh using 1
  funext y
  exact (SmoothManifolds.productChart_source_apply C c d).2 (σ.val y, τ.val y)


/-- The literal shuffle simplexes of smooth factor simplexes are smooth in
the actual P104 product manifold, with the same corner-extension convention. -/
theorem shuffleSimplex_smooth_product
    {n m p q : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
    (C : ProductCoordinates n a m b k)
    (P : AtlasData.SmoothManifold (n+m) k (M × N))
    (hP : P.smoothStructure.val = AtlasData.maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val))
    (s : P202Specs.ShuffleModel.LatticePath p q)
    (σ : P202Specs.DeRhamComparison.SmoothSimplex S p)
    (τ : P202Specs.DeRhamComparison.SmoothSimplex T q) :
    P202Specs.SmoothSingularComparison.IsSmoothSimplex P (p+q)
      (P202Specs.ShuffleModel.shuffleSimplex s σ.val τ.val) := by
  have hh := simplexSmooth_pair S T C P hP
    (P202Specs.DeRhamComparison.p104Simplex S
      (reparametrizedSmoothSimplex S s.horizontal σ))
    (P202Specs.DeRhamComparison.p104Simplex T
      (reparametrizedSmoothSimplex T s.vertical τ))
  unfold P202Specs.SmoothSingularComparison.IsSmoothSimplex
  convert hh using 1
  funext x
  simp [P202Specs.DeRhamComparison.p104Simplex, reparametrizedSmoothSimplex,
    reparametrizedSimplex, P202Specs.ShuffleModel.shuffleSimplex,
    P202Specs.ShuffleModel.parametrization, P202Specs.AlexanderWhitney.productSpace,
    Function.comp_def]

/-- A genuine boundaryless self-product, with projection and diagonal smooth
maps and their actual intrinsic differentials. -/
structure EuclideanSelfProduct
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n .euclidean M) where
  coordinates : ProductCoordinates n .euclidean n .euclidean .euclidean
  manifold : AtlasData.SmoothManifold (n+n) .euclidean (M × M)
  smoothStructure_eq : manifold.smoothStructure.val =
    AtlasData.maximalExtension (⊤ : ℕ∞)
      (productAtlas coordinates S.smoothStructure.val S.smoothStructure.val)
  fst_smooth : MapData.IsSmoothMap manifold S Prod.fst
  snd_smooth : MapData.IsSmoothMap manifold S Prod.snd
  diagonal_smooth : MapData.IsSmoothMap S manifold (fun x => (x,x))
  fstDifferential : ∀ z : M × M,
    TangentData.TangentSpace manifold z →ₗ[ℝ] TangentData.TangentSpace S z.1
  sndDifferential : ∀ z : M × M,
    TangentData.TangentSpace manifold z →ₗ[ℝ] TangentData.TangentSpace S z.2
  diagonalDifferential : ∀ x : M,
    TangentData.TangentSpace S x →ₗ[ℝ] TangentData.TangentSpace manifold (x,x)
  fst_isDifferential : ∀ z, DifferentialData.IsDifferential manifold S Prod.fst z (fstDifferential z)
  snd_isDifferential : ∀ z, DifferentialData.IsDifferential manifold S Prod.snd z (sndDifferential z)
  diagonal_isDifferential : ∀ x, DifferentialData.IsDifferential S manifold (fun x => (x,x)) x
    (diagonalDifferential x)
  fst_diagonal : ∀ x, (fstDifferential (x,x)).comp (diagonalDifferential x) = LinearMap.id
  snd_diagonal : ∀ x, (sndDifferential (x,x)).comp (diagonalDifferential x) = LinearMap.id

/-- The self-product package exists for every Euclidean-model smooth manifold,
without assumptions of positive dimension or nonemptiness. -/
theorem exists_euclideanSelfProduct
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n .euclidean M) :
    Nonempty (EuclideanSelfProduct S) := by
  obtain ⟨C⟩ := SmoothManifolds.exists_euclidean_productCoordinates n n
  obtain ⟨P, _, hP⟩ := SmoothManifolds.exists_product_smoothManifold S S C
  obtain ⟨hf, hg, hE⟩ := SmoothManifolds.differential_product S S C P hP
  choose E hEf hEg using hE
  have hi : MapData.IsSmoothMap S S id :=
    SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1
  have hp := SmoothManifolds.differential_pair S S S C P hP id id hi hi
  let Lf := fun z : M × M => (LinearMap.fst ℝ _ _).comp (E z).toLinearMap
  let Lg := fun z : M × M => (LinearMap.snd ℝ _ _).comp (E z).toLinearMap
  let D := SmoothManifolds.differential S P (fun x => (x,x)) hp.1
  have hD := SmoothManifolds.differential_spec S P (fun x => (x,x)) hp.1
  have hcomp (x : M) : (E (x,x)).toLinearMap.comp (D x) =
      (LinearMap.id : TangentData.TangentSpace S x →ₗ[ℝ] _).prod LinearMap.id :=
    hp.2 x LinearMap.id LinearMap.id (D x) (E (x,x))
      (SmoothManifolds.differential_id S x) (SmoothManifolds.differential_id S x)
      (hD x) (hEf (x,x)) (hEg (x,x))
  refine ⟨⟨C, P, hP, hf, hg, hp.1, Lf, Lg, D, hEf, hEg, hD, ?_, ?_⟩⟩
  · intro x
    change ((LinearMap.fst ℝ _ _).comp (E (x,x)).toLinearMap).comp (D x) = _
    rw [LinearMap.comp_assoc, hcomp x]
    ext v
    rfl
  · intro x
    change ((LinearMap.snd ℝ _ _).comp (E (x,x)).toLinearMap).comp (D x) = _
    rw [LinearMap.comp_assoc, hcomp x]
    ext v
    rfl

private theorem map_smoothModule
    {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M)
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : P202Specs.SingularChains.Chains ℝ (TopCat.of M) q →ₗ[ℝ] W)
    (V : Submodule ℝ W)
    (hL : ∀ σ, P202Specs.SmoothSingularComparison.IsSmoothSimplex S q σ →
      L (Finsupp.single σ 1) ∈ V)
    (z : P202Specs.SingularChains.Chains ℝ (TopCat.of M) q)
    (hz : z ∈ P202Specs.SmoothSingularComparison.smoothModule S q) : L z ∈ V := by
  have hle : P202Specs.SmoothSingularComparison.smoothModule S q ≤ V.comap L := by
    unfold P202Specs.SmoothSingularComparison.smoothModule
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨σ,hσ,rfl⟩
    exact hL σ hσ
  exact hle hz

/-- The signed shuffle of finite smooth chains is a smooth chain in the actual
P104 product manifold. -/
theorem shuffleComponent_mem_smoothModule
    {n m p q : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
    (C : ProductCoordinates n a m b k)
    (P : AtlasData.SmoothManifold (n+m) k (M × N))
    (hP : P.smoothStructure.val = AtlasData.maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val))
    (z : P202Specs.SmoothSingularComparison.smoothModule S p)
    (w : P202Specs.SmoothSingularComparison.smoothModule T q) :
    P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q
      (z.val ⊗ₜ[ℝ] w.val) ∈ P202Specs.SmoothSingularComparison.smoothModule P (p+q) := by
  let V := P202Specs.SmoothSingularComparison.smoothModule P (p+q)
  apply map_smoothModule S
    ((P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q).comp
      ((TensorProduct.mk ℝ _ _).flip w.val)) V ?_ z.val z.property
  intro σ hσ
  apply map_smoothModule T
    ((P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q).comp
      ((TensorProduct.mk ℝ _ _) (Finsupp.single σ 1))) V ?_ w.val w.property
  intro τ hτ
  change P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q
    (Finsupp.single σ 1 ⊗ₜ[ℝ] Finsupp.single τ 1) ∈ V
  rw [P202.ShuffleChains.component_formula]
  simp only [one_mul, one_smul]
  apply Submodule.sum_mem
  intro s _
  exact V.toAddSubgroup.zsmul_mem
    (Finsupp.single_mem_supported ℝ 1
      (shuffleSimplex_smooth_product S T C P hP s ⟨σ,hσ⟩ ⟨τ,hτ⟩)) _

/-- Grading transport does not change smooth support of a shuffle chain. -/
theorem cast_shuffleComponent_mem_smoothModule
    {n m p q d : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
    (C : ProductCoordinates n a m b k)
    (P : AtlasData.SmoothManifold (n+m) k (M × N))
    (hP : P.smoothStructure.val = AtlasData.maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val))
    (h : p+q=d)
    (z : P202Specs.SmoothSingularComparison.smoothModule S p)
    (w : P202Specs.SmoothSingularComparison.smoothModule T q) :
    P202Specs.ShuffleModel.castChains ℝ h
      (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) p q
        (z.val ⊗ₜ[ℝ] w.val)) ∈ P202Specs.SmoothSingularComparison.smoothModule P d := by
  subst d
  exact shuffleComponent_mem_smoothModule S T C P hP z w

end SmoothProducts

section RingPackaging

/-- For a fixed natural singular cup algebra, universal Euclidean-model
multiplicativity produces an actual unital graded ring comparison on every
original manifold, using the actual boundary reduction. -/
theorem ringComparison_conditional_of_euclidean_multiplicativity
    (hDR : P202Specs.DeRhamComparison.deRhamComparison_type.{u})
    (U : P202Specs.CupProduct.NaturalCohomologyRing.{0,u} ℝ)
    (hEuclidean : ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
      (S : AtlasData.SmoothManifold n .euclidean M)
      (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
      (P : K.GradedProduct), K.IsGradedProduct P →
      ∀ (e : ComparisonFamily S K), IsIntegrationComparison S K e →
      ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
        e (p+q) (P.mul p q x y) =
          (U.ring (TopCat.of M)).product p q (e p x) (e q y))
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) :
    Nonempty (RingComparison S K (U.ring (TopCat.of M))) := by
  obtain ⟨P, hP⟩ := SmoothManifolds.DeRhamResults.product_exists K
  obtain ⟨e, he⟩ := hDR.1 S C B K
  let A : FormsAlgebra S K := formsAlgebraOfProduct S K P hP
  have hMul : ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
      e (p+q) (A.product.mul p q x y) =
        (U.ring (TopCat.of M)).product p q (e p x) (e q y) :=
    comparison_mul_boundary_reduction hDR U hEuclidean S C B K P hP e he
  exact ⟨ringComparisonOfMultiplicative S K A (U.ring (TopCat.of M)) e he hMul⟩

/-- Universal Euclidean-model multiplicativity, once established, closes the
full natural unital ring comparison on all original manifold models. The
Euclidean hypothesis is explicit on this packaging lemma and must be proved
before using it to close the original target. -/
theorem ringIsomorphism_conditional_of_euclidean_multiplicativity
    (hDR : P202Specs.DeRhamComparison.deRhamComparison_type.{u})
    (hEuclidean : ∀ (U : P202Specs.CupProduct.NaturalCohomologyRing.{0,u} ℝ)
      {n : ℕ} {M : Type u} [TopologicalSpace M]
      (S : AtlasData.SmoothManifold n .euclidean M)
      (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
      (P : K.GradedProduct), K.IsGradedProduct P →
      ∀ (e : ComparisonFamily S K), IsIntegrationComparison S K e →
      ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
        e (p+q) (P.mul p q x y) =
          (U.ring (TopCat.of M)).product p q (e p x) (e q y)) :
    P202Specs.DeRhamRing.ringIsomorphism_type.{u} := by
  obtain ⟨U⟩ := P202.CupProduct.cohomologyRing.{0,u} ℝ
  refine ⟨⟨U, ?_⟩, hDR.2⟩
  intro n a M instM S C B K
  exact ringComparison_conditional_of_euclidean_multiplicativity
    hDR U (hEuclidean U) S C B K

end RingPackaging

section DiagonalAssembly
open P202Specs.SmoothSingularComparison P202Specs.CohomologyPairs
open P202Specs.CupProduct P202Specs.AlexanderWhitney

/-- Ordinary cohomology takes a genuine retraction to the corresponding
pullback left inverse in every nonnegative degree. -/
theorem ordinaryPullback_retract {X Y : TopCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X) (q : ℕ)
    (x : P202Specs.CupProduct.H ℝ X q) :
    hPullback ℝ f q (hPullback ℝ g q x) = x := by
  have hh := congrArg
    (fun t : X ⟶ X => ((ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map t.op).hom x) hfg
  have hs : hPullback ℝ f q (hPullback ℝ g q x) =
      ((ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map (𝟙 X).op).hom x := by
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply] at hh
    exact hh
  have hi := congrArg (fun t => t.hom x)
    ((ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map_id (op X))
  exact hs.trans hi


/-- The diagonal converts compatibility with exterior products into full
wedge/cup compatibility. The only local multiplicativity assumption is the
exterior comparison on the actual product manifold; all pullbacks below are
the existing intrinsic P104 cohomology pullbacks with genuine differentials. -/
theorem comparison_mul_of_exterior_diagonal
    (hDR : P202Specs.DeRhamComparison.deRhamComparison_type.{u})
    (U : P202Specs.CupProduct.NaturalCohomologyRing.{0,u} ℝ)
    {n l : ℕ} {a c : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (R : AtlasData.SmoothManifold l c (M × M))
    (C : CotangentBundle S) (V : CotangentBundle R)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle V k)
    (K : Calculus C B) (J : Calculus V E)
    (P : K.GradedProduct) (Q : J.GradedProduct)
    (hP : K.IsGradedProduct P) (hQ : J.IsGradedProduct Q)
    (eS : ComparisonFamily S K) (eR : ComparisonFamily R J)
    (heS : IsIntegrationComparison S K eS) (heR : IsIntegrationComparison R J eR)
    (hf : MapData.IsSmoothMap R S Prod.fst) (hg : MapData.IsSmoothMap R S Prod.snd)
    (hd : MapData.IsSmoothMap S R (fun x => (x,x)))
    (Lf : ∀ z : M × M, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace S z.1)
    (Lg : ∀ z : M × M, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace S z.2)
    (Ld : ∀ x : M, TangentData.TangentSpace S x →ₗ[ℝ] TangentData.TangentSpace R (x,x))
    (hLf : ∀ z, DifferentialData.IsDifferential R S Prod.fst z (Lf z))
    (hLg : ∀ z, DifferentialData.IsDifferential R S Prod.snd z (Lg z))
    (hLd : ∀ x, DifferentialData.IsDifferential S R (fun x => (x,x)) x (Ld x))
    (Ffst Fsnd : ∀ q, K.Cohomology q →ₗ[ℝ] J.Cohomology q)
    (Fdiag : ∀ q, J.Cohomology q →ₗ[ℝ] K.Cohomology q)
    (hFfst : IsCohomologyPullback V E J K Prod.fst Lf Ffst)
    (hFsnd : IsCohomologyPullback V E J K Prod.snd Lg Fsnd)
    (hFdiag : IsCohomologyPullback C B K J (fun x => (x,x)) Ld Fdiag)
    (hExterior : ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
      eR (p+q) (Q.mul p q (Ffst p x) (Fsnd q y)) =
        (U.ring (TopCat.of (M × M))).product p q
          (hPullback ℝ (firstProjection (TopCat.of M) (TopCat.of M)) p (eS p x))
          (hPullback ℝ (secondProjection (TopCat.of M) (TopCat.of M)) q (eS q y))) :
    ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
      eS (p+q) (P.mul p q x y) =
        (U.ring (TopCat.of M)).product p q (eS p x) (eS q y) := by
  let Δ := underlyingMap S R (fun x => (x,x)) hd
  have hfcomp : Δ ≫ firstProjection (TopCat.of M) (TopCat.of M) = 𝟙 (TopCat.of M) := by
    ext x
    rfl
  have hgcomp : Δ ≫ secondProjection (TopCat.of M) (TopCat.of M) = 𝟙 (TopCat.of M) := by
    ext x
    rfl
  have hfret := ordinaryPullback_retract Δ
    (firstProjection (TopCat.of M) (TopCat.of M)) hfcomp
  have hgret := ordinaryPullback_retract Δ
    (secondProjection (TopCat.of M) (TopCat.of M)) hgcomp
  have hnf := hDR.2 R S V C E B J K eR eS heR heS Prod.fst hf Lf hLf Ffst hFfst
  have hng := hDR.2 R S V C E B J K eR eS heR heS Prod.snd hg Lg hLg Fsnd hFsnd
  have hnd := hDR.2 S R C V B E K J eS eR heS heR (fun x => (x,x)) hd Ld hLd Fdiag hFdiag
  have hleft : ∀ q (x : K.Cohomology q), Fdiag q (Ffst q x) = x := by
    intro q x
    apply (eS q).injective
    calc
      _ = hPullback ℝ Δ q (eR q (Ffst q x)) := hnd q _
      _ = hPullback ℝ Δ q
          (hPullback ℝ (firstProjection (TopCat.of M) (TopCat.of M)) q (eS q x)) :=
        congrArg (hPullback ℝ Δ q) (hnf q x)
      _ = eS q x := hfret q _
  have hright : ∀ q (x : K.Cohomology q), Fdiag q (Fsnd q x) = x := by
    intro q x
    apply (eS q).injective
    calc
      _ = hPullback ℝ Δ q (eR q (Fsnd q x)) := hnd q _
      _ = hPullback ℝ Δ q
          (hPullback ℝ (secondProjection (TopCat.of M) (TopCat.of M)) q (eS q x)) :=
        congrArg (hPullback ℝ Δ q) (hng q x)
      _ = eS q x := hgret q _
  have hprod := (SmoothManifolds.DeRhamResults.pullback_product S R C V B E K J
    P Q (fun x => (x,x)) Ld Fdiag hP hQ hFdiag).2
  intro p q x y
  calc
    _ = eS (p+q) (Fdiag (p+q) (Q.mul p q (Ffst p x) (Fsnd q y))) := by
      rw [hprod, hleft, hright]
    _ = hPullback ℝ Δ (p+q)
        (eR (p+q) (Q.mul p q (Ffst p x) (Fsnd q y))) := hnd (p+q) _
    _ = hPullback ℝ Δ (p+q) ((U.ring (TopCat.of (M × M))).product p q
        (hPullback ℝ (firstProjection (TopCat.of M) (TopCat.of M)) p (eS p x))
        (hPullback ℝ (secondProjection (TopCat.of M) (TopCat.of M)) q (eS q y))) :=
      congrArg (hPullback ℝ Δ (p+q)) (hExterior p q x y)
    _ = (U.ring (TopCat.of M)).product p q
        (hPullback ℝ Δ p (hPullback ℝ (firstProjection (TopCat.of M) (TopCat.of M)) p (eS p x)))
        (hPullback ℝ Δ q (hPullback ℝ (secondProjection (TopCat.of M) (TopCat.of M)) q (eS q y))) :=
      P202.CupProduct.represented_product_natural ℝ
        (fun X => (U.ring X).product) (fun X => (U.ring X).represents) Δ p q _ _
    _ = _ := congrArg₂
      (fun (a : H ℝ (TopCat.of M) p) (b : H ℝ (TopCat.of M) q) =>
        (U.ring (TopCat.of M)).product p q a b)
      (hfret p (eS p x)) (hgret q (eS q y))

end DiagonalAssembly

section ExteriorClasses
open P202Specs.SmoothSingularComparison P202Specs.SingularChains P202Specs.ShuffleModel
open P202Specs.CohomologyPairs P202Specs.CupProduct P202Specs.AlexanderWhitney
open P202Specs.EilenbergZilber P202Specs.TopologicalKunneth
variable {n m l : ℕ} {a b c : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
  (R : AtlasData.SmoothManifold l c (M × N))

theorem castChains_mem_smoothModule {d r : ℕ} (h : r=d)
    (z : Chains ℝ (TopCat.of M) r) (hz : z ∈ smoothModule S r) :
    castChains ℝ h z ∈ smoothModule S d := by
  subst d
  exact hz

theorem integrationClass_external_evaluation
    (C : CotangentBundle S) (A : CotangentBundle T) (V : CotangentBundle R)
    (hf : MapData.IsSmoothMap R S Prod.fst) (hg : MapData.IsSmoothMap R T Prod.snd)
    (Lf : ∀ z : M × N, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace S z.1)
    (Lg : ∀ z : M × N, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace T z.2)
    (hLf : ∀ z, DifferentialData.IsDifferential R S Prod.fst z (Lf z))
    (hLg : ∀ z, DifferentialData.IsDifferential R T Prod.snd z (Lg z))
    (hSh : ∀ k l (z : smoothModule S k) (w : smoothModule T l),
      P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) k l
        (z.val ⊗ₜ[ℝ] w.val) ∈ smoothModule R (k+l))
    {p q k j : ℕ} (h : k+j=p+q) (ω : Field S p) (η : Field T q)
    (x : ordinaryCohomology ℝ ℝ (TopCat.of (M × N)) ((p+q : ℕ) : ℤ))
    (hx : IsIntegrationClass R V
      (fieldWedge (FormPullbackData.pullbackField R S Prod.fst Lf ω)
        (FormPullbackData.pullbackField R T Prod.snd Lg η)) x)
    (e : ExternalProduct.{0,u} ℝ)
    (z : (smoothComplex S).cycles k) (w : (smoothComplex T).cycles j) :
    P202Specs.UniversalCoefficients.evaluation ℝ ℝ
      (ordinaryComplex ℝ ℝ (TopCat.of (M × N))) ((p+q : ℕ) : ℤ) x
      (h ▸ ordinaryExternal ℝ e (TopCat.of M) (TopCat.of N) k j
        ((ordinaryHomologyIso ℝ (TopCat.of M) k).inv
          ((complex ℝ ℝ (TopCat.of M)).homologyπ k (cyclesMap (inclusion S) k z)) ⊗ₜ[ℝ]
         (ordinaryHomologyIso ℝ (TopCat.of N) j).inv
          ((complex ℝ ℝ (TopCat.of N)).homologyπ j (cyclesMap (inclusion T) j w)))) =
    externalIntegralCochain S T C A ω η
      (castChains ℝ h (P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) k j
        (((smoothComplex S).iCycles k z).val ⊗ₜ[ℝ] ((smoothComplex T).iCycles j w).val))) := by
  obtain ⟨t, ht, he⟩ := e.represents (TopCat.of M) (TopCat.of N) k j
    (cyclesMap (inclusion S) k z) (cyclesMap (inclusion T) j w)
  have hz := congrArg (fun f => f.hom z) (cyclesMap_i (inclusion S) k)
  have hw := congrArg (fun f => f.hom w) (cyclesMap_i (inclusion T) j)
  change (complex ℝ ℝ (TopCat.of M)).iCycles k (cyclesMap (inclusion S) k z) =
    ((smoothComplex S).iCycles k z).val at hz
  change (complex ℝ ℝ (TopCat.of N)).iCycles j (cyclesMap (inclusion T) j w) =
    ((smoothComplex T).iCycles j w).val at hw
  rw [hz, hw] at ht
  have htSmooth : (complex ℝ ℝ (TopCat.of (M × N))).iCycles (k+j) t ∈ smoothModule R (k+j) := by
    erw [ht]
    exact hSh k j ((smoothComplex S).iCycles k z) ((smoothComplex T).iCycles j w)
  have hSmooth := castChains_mem_smoothModule R h _ htSmooth
  rw [ordinaryExternal_cycles ℝ e (TopCat.of M) (TopCat.of N) k j
    (cyclesMap (inclusion S) k z) (cyclesMap (inclusion T) j w) t he]
  erw [integrationClass_smoothChain_evaluation_cast R V h _ x hx t hSmooth]
  have hi := integralCochain_external_pullbacks S T R C A V hf hg Lf Lg hLf hLg ω η
    ⟨castChains ℝ h ((complex ℝ ℝ (TopCat.of (M × N))).iCycles (k+j) t), hSmooth⟩
  exact hi.trans (congrArg (fun v => externalIntegralCochain S T C A ω η (castChains ℝ h v)) ht)


/-- Literal external integration and singular external cup determine the same
ordinary cohomology class; every Künneth bidegree is tested, without a rank bound. -/
theorem integrationClass_external_product
    (C : CotangentBundle S) (A : CotangentBundle T) (V : CotangentBundle R)
    (hf : MapData.IsSmoothMap R S Prod.fst) (hg : MapData.IsSmoothMap R T Prod.snd)
    (Lf : ∀ z : M × N, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace S z.1)
    (Lg : ∀ z : M × N, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace T z.2)
    (hLf : ∀ z, DifferentialData.IsDifferential R S Prod.fst z (Lf z))
    (hLg : ∀ z, DifferentialData.IsDifferential R T Prod.snd z (Lg z))
    (hSh : ∀ k l (z : smoothModule S k) (w : smoothModule T l),
      P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of N) k l
        (z.val ⊗ₜ[ℝ] w.val) ∈ smoothModule R (k+l))
    (hS : ∀ q : ℕ, IsIso (homologyMap (restriction S) (q : ℤ)))
    (hT : ∀ q : ℕ, IsIso (homologyMap (restriction T) (q : ℤ)))
    {p q : ℕ} (Bp : FormBundle C p) (Eq : FormBundle A q)
    (ω : Field S p) (η : Field T q) (hω : IsForm Bp ω) (hη : IsForm Eq η)
    (x : ordinaryCohomology ℝ ℝ (TopCat.of M) (p : ℤ))
    (y : ordinaryCohomology ℝ ℝ (TopCat.of N) (q : ℤ))
    (t : ordinaryCohomology ℝ ℝ (TopCat.of (M × N)) ((p+q : ℕ) : ℤ))
    (hx : IsIntegrationClass S C ω x) (hy : IsIntegrationClass T A η y)
    (ht : IsIntegrationClass R V
      (fieldWedge (FormPullbackData.pullbackField R S Prod.fst Lf ω)
        (FormPullbackData.pullbackField R T Prod.snd Lg η)) t)
    (e : ExternalProduct.{0,u} ℝ)
    (U : CohomologyRing ℝ (productSpace (TopCat.of M) (TopCat.of N))) :
    t = U.product p q
      (hPullback ℝ (firstProjection (TopCat.of M) (TopCat.of N)) p x)
      (hPullback ℝ (secondProjection (TopCat.of M) (TopCat.of N)) q y) := by
  apply realProductClass_ext_smoothProducts S T hS hT e (p+q)
  intro i z w
  let hzk : (degreeEmbedding 0).f i.val.1 = (i.val.1 : ℤ) := by simp [degreeEmbedding]
  let hwk : (degreeEmbedding 0).f i.val.2 = (i.val.2 : ℤ) := by simp [degreeEmbedding]
  let EZ := (smoothComplex S).extendCyclesIso (degreeEmbedding 0) hzk
  let EW := (smoothComplex T).extendCyclesIso (degreeEmbedding 0) hwk
  let zs := EZ.hom z
  let ws := EW.hom w
  have hzclass : homologyMap (ordinaryInclusion S) (i.val.1 : ℤ)
      ((smoothOrdinaryComplex S).homologyπ (i.val.1 : ℤ) z) =
      (ordinaryHomologyIso ℝ (TopCat.of M) i.val.1).inv
        ((complex ℝ ℝ (TopCat.of M)).homologyπ i.val.1 (cyclesMap (inclusion S) i.val.1 zs)) := by
    have hh := smoothInclusion_nonnegative_class S zs
    change homologyMap (ordinaryInclusion S) (i.val.1 : ℤ)
      ((smoothOrdinaryComplex S).homologyπ (i.val.1 : ℤ) (EZ.inv (EZ.hom z))) = _ at hh
    rw [ModuleCat.inv_hom_apply] at hh
    exact hh
  have hwclass : homologyMap (ordinaryInclusion T) (i.val.2 : ℤ)
      ((smoothOrdinaryComplex T).homologyπ (i.val.2 : ℤ) w) =
      (ordinaryHomologyIso ℝ (TopCat.of N) i.val.2).inv
        ((complex ℝ ℝ (TopCat.of N)).homologyπ i.val.2 (cyclesMap (inclusion T) i.val.2 ws)) := by
    have hh := smoothInclusion_nonnegative_class T ws
    change homologyMap (ordinaryInclusion T) (i.val.2 : ℤ)
      ((smoothOrdinaryComplex T).homologyπ (i.val.2 : ℤ) (EW.inv (EW.hom w))) = _ at hh
    rw [ModuleCat.inv_hom_apply] at hh
    exact hh
  rw [hzclass, hwclass]
  erw [integrationClass_external_evaluation S T R C A V hf hg Lf Lg hLf hLg hSh
    i.property ω η t ht e zs ws]
  by_cases hi : i = ⟨(p,q),rfl⟩
  · subst i
    rw [externalCup_evaluation]
    rw [integrationClass_nonnegative_evaluation S C ω x hx,
      integrationClass_nonnegative_evaluation T A η y hy]
    exact productShuffleIntegral_smoothForms S T C A Bp Eq ω η hω hη
      ((smoothComplex S).iCycles p zs) ((smoothComplex T).iCycles q ws)
  · have hne : i.val.1 ≠ p ∨ i.val.2 ≠ q := by
      by_contra hn
      push_neg at hn
      apply hi
      exact Subtype.ext (Prod.ext hn.1 hn.2)
    rw [externalIntegral_shuffle_offDiagonal S T C A i.property hne ω η]
    exact (externalCup_evaluation_offDiagonal ℝ p q e U x y i hi _ _).symm

end ExteriorClasses

section EuclideanMultiplicativity
open P202Specs.SmoothSingularComparison P202Specs.CohomologyPairs
open P202Specs.CupProduct P202Specs.AlexanderWhitney
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations

/- The local kernel budget is unbounded because checking the intrinsic
quotient representatives is costly. -/
set_option maxHeartbeats 0 in
/-- Closed representative formulas turn literal external integration into
cohomological external product compatibility. -/
theorem comparison_external_product_closed
    (U : P202Specs.CupProduct.NaturalCohomologyRing.{0,u} ℝ)
    {n l : ℕ} {a c : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M)
    (R : AtlasData.SmoothManifold l c (M × M))
    (C : CotangentBundle S) (V : CotangentBundle R)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle V k)
    (K : Calculus C B) (J : Calculus V E)
    (Q : J.GradedProduct) (hQ : J.IsGradedProduct Q)
    (eS : ComparisonFamily S K) (eR : ComparisonFamily R J)
    (heS : IsIntegrationComparison S K eS) (heR : IsIntegrationComparison R J eR)
    (hf : MapData.IsSmoothMap R S Prod.fst) (hg : MapData.IsSmoothMap R S Prod.snd)
    (Lf : ∀ z : M × M, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace S z.1)
    (Lg : ∀ z : M × M, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace S z.2)
    (hLf : ∀ z, DifferentialData.IsDifferential R S Prod.fst z (Lf z))
    (hLg : ∀ z, DifferentialData.IsDifferential R S Prod.snd z (Lg z))
    (Ffst Fsnd : ∀ q, K.Cohomology q →ₗ[ℝ] J.Cohomology q)
    (hFfst : IsCohomologyPullback V E J K Prod.fst Lf Ffst)
    (hFsnd : IsCohomologyPullback V E J K Prod.snd Lg Fsnd)
    (hSh : ∀ k l (z : smoothModule S k) (w : smoothModule S l),
      P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of M) k l
        (z.val ⊗ₜ[ℝ] w.val) ∈ smoothModule R (k+l)) :
    ∀ p q (α : K.closed p) (β : K.closed q),
      eR (p+q) (Q.mul p q (Ffst p (K.classOf p α)) (Fsnd q (K.classOf q β))) =
        (U.ring (TopCat.of (M × M))).product p q
          (hPullback ℝ (firstProjection (TopCat.of M) (TopCat.of M)) p (eS p (K.classOf p α)))
          (hPullback ℝ (secondProjection (TopCat.of M) (TopCat.of M)) q (eS q (K.classOf q β))) := by
  intro p q α β
  obtain ⟨α',hα',hFα⟩ := hFfst p α
  obtain ⟨β',hβ',hFβ⟩ := hFsnd q β
  obtain ⟨γ,hγ,hQγ⟩ := hQ.2.2.2.2.1 p q α' β'
  have ht := heR.2 (p+q) γ
  rw [hγ,hα',hβ'] at ht
  have hh := integrationClass_external_product S S R C C V
    hf hg Lf Lg
    hLf hLg hSh heS.1 heS.1
    (B p) (B q) α.val.val β.val.val
    ((K.mem_forms p α.val.val).mp α.val.property)
    ((K.mem_forms q β.val.val).mp β.val.property)
    (eS p (K.classOf p α)) (eS q (K.classOf q β))
    (eR (p+q) (J.classOf (p+q) γ))
    (heS.2 p α) (heS.2 q β) ht
    (P202.EilenbergZilber.externalProductData ℝ)
    (U.ring (TopCat.of (M × M)))
  change eR (p+q) (Q.mul p q (Ffst p (K.classOf p α))
    (Fsnd q (K.classOf q β))) = _
  rw [hFα,hFβ,hQγ]
  exact hh

/-- Closed representative formulas turn literal external integration into
cohomological external product compatibility. -/
theorem comparison_external_product
    (U : P202Specs.CupProduct.NaturalCohomologyRing.{0,u} ℝ)
    {n l : ℕ} {a c : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M)
    (R : AtlasData.SmoothManifold l c (M × M))
    (C : CotangentBundle S) (V : CotangentBundle R)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle V k)
    (K : Calculus C B) (J : Calculus V E)
    (Q : J.GradedProduct) (hQ : J.IsGradedProduct Q)
    (eS : ComparisonFamily S K) (eR : ComparisonFamily R J)
    (heS : IsIntegrationComparison S K eS) (heR : IsIntegrationComparison R J eR)
    (hf : MapData.IsSmoothMap R S Prod.fst) (hg : MapData.IsSmoothMap R S Prod.snd)
    (Lf : ∀ z : M × M, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace S z.1)
    (Lg : ∀ z : M × M, TangentData.TangentSpace R z →ₗ[ℝ] TangentData.TangentSpace S z.2)
    (hLf : ∀ z, DifferentialData.IsDifferential R S Prod.fst z (Lf z))
    (hLg : ∀ z, DifferentialData.IsDifferential R S Prod.snd z (Lg z))
    (Ffst Fsnd : ∀ q, K.Cohomology q →ₗ[ℝ] J.Cohomology q)
    (hFfst : IsCohomologyPullback V E J K Prod.fst Lf Ffst)
    (hFsnd : IsCohomologyPullback V E J K Prod.snd Lg Fsnd)
    (hSh : ∀ k l (z : smoothModule S k) (w : smoothModule S l),
      P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of M) k l
        (z.val ⊗ₜ[ℝ] w.val) ∈ smoothModule R (k+l)) :
    ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
      eR (p+q) (Q.mul p q (Ffst p x) (Fsnd q y)) =
        (U.ring (TopCat.of (M × M))).product p q
          (hPullback ℝ (firstProjection (TopCat.of M) (TopCat.of M)) p (eS p x))
          (hPullback ℝ (secondProjection (TopCat.of M) (TopCat.of M)) q (eS q y)) := by
  intro p q x y
  have hsα : Function.Surjective (K.classOf p) := (K.boundaries p).mkQ_surjective
  have hsβ : Function.Surjective (K.classOf q) := (K.boundaries q).mkQ_surjective
  obtain ⟨α,hα⟩ := hsα x
  obtain ⟨β,hβ⟩ := hsβ y
  have hh := comparison_external_product_closed U S R C V B E K J Q hQ eS eR heS heR
    hf hg Lf Lg hLf hLg Ffst Fsnd hFfst hFsnd hSh p q α β
  rw [hα,hβ] at hh
  exact hh

/-- Integration preserves wedge/cup products on every Euclidean-model
manifold. The actual product manifold and all its form/calculus realizations
are constructed from P104, and the only conditional premise is hDR. -/
theorem comparison_mul_euclidean
    (hDR : P202Specs.DeRhamComparison.deRhamComparison_type.{u})
    (U : P202Specs.CupProduct.NaturalCohomologyRing.{0,u} ℝ)
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n .euclidean M)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (P : K.GradedProduct) (hP : K.IsGradedProduct P)
    (eS : ComparisonFamily S K) (heS : IsIntegrationComparison S K eS) :
    ∀ p q (x : K.Cohomology p) (y : K.Cohomology q),
      eS (p+q) (P.mul p q x y) =
        (U.ring (TopCat.of M)).product p q (eS p x) (eS q y) := by
  obtain ⟨D⟩ := exists_euclideanSelfProduct S
  let R := D.manifold
  obtain ⟨V⟩ := SmoothManifolds.BundleOperations.exists_cotangent R
  let E : ∀ k, FormBundle V k := fun k =>
    Classical.choice (SmoothManifolds.ExteriorAlgebraResults.exists_formBundle V k)
  let J : Calculus V E := Classical.choice (SmoothManifolds.DeRhamResults.complex_exists V E)
  obtain ⟨Q,hQ⟩ := SmoothManifolds.DeRhamResults.product_exists J
  obtain ⟨eR,heR⟩ := hDR.1 R V E J
  obtain ⟨Ffst,hFfst⟩ := SmoothManifolds.DeRhamResults.pullback_exists
    R S V C E B J K Prod.fst D.fst_smooth D.fstDifferential D.fst_isDifferential
  obtain ⟨Fsnd,hFsnd⟩ := SmoothManifolds.DeRhamResults.pullback_exists
    R S V C E B J K Prod.snd D.snd_smooth D.sndDifferential D.snd_isDifferential
  obtain ⟨Fdiag,hFdiag⟩ := SmoothManifolds.DeRhamResults.pullback_exists
    S R C V B E K J (fun x => (x,x)) D.diagonal_smooth
      D.diagonalDifferential D.diagonal_isDifferential
  have hSh : ∀ k l (z : smoothModule S k) (w : smoothModule S l),
      P202Specs.ShuffleChains.shuffleComponent ℝ (TopCat.of M) (TopCat.of M) k l
        (z.val ⊗ₜ[ℝ] w.val) ∈ smoothModule R (k+l) := by
    intro k l z w
    exact shuffleComponent_mem_smoothModule S S D.coordinates R D.smoothStructure_eq z w
  have hExterior := comparison_external_product U S R C V B E K J Q hQ eS eR heS heR
    D.fst_smooth D.snd_smooth D.fstDifferential D.sndDifferential
    D.fst_isDifferential D.snd_isDifferential Ffst Fsnd hFfst hFsnd hSh
  exact comparison_mul_of_exterior_diagonal hDR U S R C V B E K J P Q hP hQ
    eS eR heS heR D.fst_smooth D.snd_smooth D.diagonal_smooth
    D.fstDifferential D.sndDifferential D.diagonalDifferential
    D.fst_isDifferential D.snd_isDifferential D.diagonal_isDifferential
    Ffst Fsnd Fdiag hFfst hFsnd hFdiag hExterior

end EuclideanMultiplicativity

/-- The full natural unital graded algebra comparison, conditional only on the
specified upstream integration comparison proposition. -/
theorem ringIsomorphism_conditional
    (hDR : P202Specs.DeRhamComparison.deRhamComparison_type.{u}) :
    P202Specs.DeRhamRing.ringIsomorphism_type.{u} :=
  ringIsomorphism_conditional_of_euclidean_multiplicativity hDR
    (comparison_mul_euclidean hDR)

/-- Conditional draft of the original full target. The sole explicit premise
is exactly the ordered premise in the current conditional-proof contract.
The owner supplies the closed original wrapper after upstream proof closure. -/
theorem deRhamRing_conditional
    (hDR : P202Specs.DeRhamComparison.deRhamComparison_type.{u}) :
    P202Specs.DeRhamRing.deRhamRing_type.{u} :=
  ⟨ringIsomorphism_conditional hDR, productShuffleIntegral⟩

end P202.DeRhamRing

universe v8_closure_2902b764d85b6748_u0
theorem _root_.«P202».«DeRhamRing».«deRhamRing» : _root_.«P202Specs».«DeRhamRing».«deRhamRing_type».{v8_closure_2902b764d85b6748_u0} :=
  @_root_.«P202».«DeRhamRing».«deRhamRing_conditional».{v8_closure_2902b764d85b6748_u0} (@_root_.«P202».«DeRhamComparison».«deRhamComparison».{v8_closure_2902b764d85b6748_u0})
