import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Contractible
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Comparison.DeRhamComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Comparison.CochainCoverDescent
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Comparison.CochainCoverDescent
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Comparison.SmoothSingularComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficients
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Comparison.IntegrationCochain
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.HomotopyInvariance
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.MayerVietoris
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Spheres
import Mathlib.Algebra.Exact.Basic
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.FiniteSupport.Basic

/-! The natural integration-induced de Rham comparison. Literal intrinsic
integration is assembled through the actual open-cover totals, smooth-small
restriction, convex coordinate neighborhoods, and the smooth collar push. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory HomologicalComplex Opposite
open scoped Simplicial
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
open SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open P202Specs P202Specs.DeRhamComparison
namespace P202.DeRhamComparison
universe u v
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)

/-- The geometric identification is bijective on the actual smooth bases,
not just a comparison of simplex dimensions or names. -/
def p104SimplexEquiv (q : ℕ) :
    SmoothSimplex S q ≃ SmoothSingularData.SingularSimplex S q where
  toFun := p104Simplex S
  invFun σ := ⟨(SingularChains.simplexEquiv (TopCat.of M) q).symm
    ⟨σ.val ∘ SmoothSingularComparison.toCorner q,
      σ.property.1.comp (SmoothSingularComparison.continuous_toCorner q)⟩, by
        change SmoothSingularData.SimplexSmooth S _
        simpa only [Equiv.apply_symm_apply, ContinuousMap.coe_mk,
          Function.comp_assoc, Function.comp_def,
          SmoothSingularComparison.toCorner_toBarycentric] using σ.property⟩
  left_inv σ := by
    apply Subtype.ext
    apply (SingularChains.simplexEquiv (TopCat.of M) q).injective
    apply ContinuousMap.ext
    intro x
    simp [p104Simplex, Function.comp_def]
  right_inv σ := by
    apply Subtype.ext
    funext x
    simp [p104Simplex, Function.comp_def]

/-- Finite chains in the shared smooth submodule are exactly the P104 free
real chains on local-ambient-extension smooth simplices. -/
def p104ChainEquiv (q : ℕ) :
    SmoothSingularComparison.smoothModule S q ≃ₗ[ℝ] SmoothSingularData.Chains S q :=
  (Finsupp.supportedEquivFinsupp _).trans (Finsupp.domLCongr (p104SimplexEquiv S q))

/-- A cochain is determined by all its values on smooth simplex generators. -/
theorem smoothCochain_ext {q : ℕ}
    (c d : (SmoothSingularComparison.smoothCochains S).X (q : ℤ))
    (h : ∀ σ, evaluateSmoothCochain S c σ = evaluateSmoothCochain S d σ) : c = d := by
  change ((SmoothSingularComparison.smoothOrdinaryComplex S).X (q : ℤ) →ₗ[ℝ] ℝ) at c d
  change c = d
  apply LinearMap.ext
  intro z
  let E : SmoothSingularComparison.smoothModule S q ≃ₗ[ℝ]
      (SmoothSimplex S q →₀ ℝ) := Finsupp.supportedEquivFinsupp _
  let F := (smoothDegreeIso S q).toLinearEquiv.trans E
  have hlin : c.comp F.symm.toLinearMap = d.comp F.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro σ r
    have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hr, map_smul, map_smul]
    congr 1
    have hgen : E.symm (Finsupp.single σ 1) = smoothGenerator S σ := by
      apply Subtype.ext
      exact Finsupp.supportedEquivFinsupp_symm_single (R := ℝ) _ σ 1
    change c ((smoothDegreeIso S q).inv (E.symm (Finsupp.single σ 1))) =
      d ((smoothDegreeIso S q).inv (E.symm (Finsupp.single σ 1)))
    rw [hgen]
    exact h σ
  have hz := LinearMap.congr_fun hlin (F z)
  change c (F.symm (F z)) = d (F.symm (F z)) at hz
  simpa using hz

/-- The evaluation characterization specifies a unique class once restriction
is an isomorphism. This rules out arbitrary unrelated cohomology equivalences. -/
theorem integrationClass_unique (C : CotangentBundle S) {q : ℕ} (ω : Field S q)
    [IsIso (homologyMap (SmoothSingularComparison.restriction S) (q : ℤ))]
    {x y : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ)}
    (hx : IsIntegrationClass S C ω x) (hy : IsIntegrationClass S C ω y) : x = y := by
  obtain ⟨c, hc, hec⟩ := hx
  obtain ⟨d, hd, hed⟩ := hy
  have hcd : c = d := by
    apply (ModuleCat.mono_iff_injective
      ((SmoothSingularComparison.smoothCochains S).iCycles (q : ℤ))).mp inferInstance
    apply smoothCochain_ext S
    intro σ
    exact (hec σ).trans (hed σ).symm
  apply (ModuleCat.mono_iff_injective
    (homologyMap (SmoothSingularComparison.restriction S) (q : ℤ))).mp inferInstance
  exact hc.symm.trans ((congrArg _ hcd).trans hd)

/-- Hence any integration-induced equivalence has the same values on all
classes, including H⁰ and the zero groups of the empty manifold. -/
theorem integrationComparison_unique {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (e h : ComparisonFamily S K)
    (he : IsIntegrationComparison S K e) (hh : IsIntegrationComparison S K h) : e = h := by
  funext q
  apply LinearEquiv.ext
  intro x
  obtain ⟨ω, rfl⟩ := (K.boundaries q).mkQ_surjective x
  letI := he.1 q
  exact integrationClass_unique S C ω.val.val (he.2 q ω) (hh.2 q ω)

@[simp] theorem p104ChainEquiv_generator {q : ℕ} (σ : SmoothSimplex S q) :
    p104ChainEquiv S q (smoothGenerator S σ) =
      Finsupp.single (p104Simplex S σ) 1 := by
  let E : SmoothSingularComparison.smoothModule S q ≃ₗ[ℝ]
      (SmoothSimplex S q →₀ ℝ) := Finsupp.supportedEquivFinsupp _
  have he : E (smoothGenerator S σ) = Finsupp.single σ 1 := by
    apply E.symm.injective
    simp only [LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    exact (Finsupp.supportedEquivFinsupp_symm_single (R := ℝ) _ σ 1).symm
  change (Finsupp.domLCongr (R := ℝ) (p104SimplexEquiv S q)) (E (smoothGenerator S σ)) = _
  rw [he]
  exact Finsupp.domLCongr_single _ _ _

/-- Linear integration in the actual shared categorical cochain module.
P104 supplies existence of I for every intrinsic calculus. -/
def integrationInDegree {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ) :
    K.forms q →ₗ[ℝ] (SmoothSingularComparison.smoothCochains S).X (q : ℤ) :=
  (LinearMap.lcomp ℝ ℝ
    ((p104ChainEquiv S q).toLinearMap.comp (smoothDegreeIso S q).hom.hom)).comp (I.map q)

/-- The assembled shared cochain evaluates to the required literal integral. -/
@[simp] theorem integrationInDegree_evaluation
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) {q : ℕ}
    (ω : K.forms q) (σ : SmoothSimplex S q) :
    evaluateSmoothCochain S (integrationInDegree S I q ω) σ =
      IntegrationCochainData.simplexIntegral S C ω.val (p104Simplex S σ) := by
  change I.map q ω (p104ChainEquiv S q
    ((smoothDegreeIso S q).hom ((smoothDegreeIso S q).inv (smoothGenerator S σ)))) = _
  rw [Iso.inv_hom_id_apply, p104ChainEquiv_generator, I.evaluation]

/-- The bridge commutes with each ordered face, so Stokes has the same signs
on the P104 and P202 geometric domains. -/
theorem p104Simplex_face {q : ℕ} (σ : SmoothSimplex S (q+1)) (j : Fin (q+2)) :
    p104Simplex S
      ⟨SingularChains.face j σ.val, SmoothSingularComparison.isSmoothSimplex_face S σ.property j⟩ =
    ⟨(p104Simplex S σ).val ∘ SmoothSingularData.face j,
      SmoothSingular.smooth_face (p104Simplex S σ).property j⟩ := by
  apply Subtype.ext
  funext x
  change SingularChains.simplexEquiv (TopCat.of M) (q+1) σ.val
      (SingularChains.faceInclusion j (SmoothSingularComparison.toBarycentric q x)) =
    SingularChains.simplexEquiv (TopCat.of M) (q+1) σ.val
      (SmoothSingularComparison.toBarycentric (q+1) (SmoothSingularData.face j x))
  rw [SmoothSingularComparison.toBarycentric_face]

/-- Stokes transported to the actual smooth basis of the shared complex,
including the signed endpoint rule when q=0. -/
theorem integrationInDegree_stokes
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ)
    (ω : K.forms q) (σ : SmoothSimplex S (q+1)) :
    evaluateSmoothCochain S (integrationInDegree S I (q+1) (K.d q ω)) σ =
      ∑ j : Fin (q+2), (-1 : ℝ)^j.val *
        evaluateSmoothCochain S (integrationInDegree S I q ω)
          ⟨SingularChains.face j σ.val,
            SmoothSingularComparison.isSmoothSimplex_face S σ.property j⟩ := by
  simp only [integrationInDegree_evaluation]
  obtain ⟨τ, hτ, hs⟩ := IntegrationCochain.simplexStokes q ω (p104Simplex S σ)
  rw [hs]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  apply Subtype.ext
  exact (hτ j).trans (congrArg Subtype.val (p104Simplex_face S σ j)).symm

/-- The restricted chain differential has the ordinary signed face formula. -/
theorem smoothBoundary_generator {q : ℕ} (σ : SmoothSimplex S (q+1)) :
    (SmoothSingularComparison.smoothComplex S).d (q+1) q (smoothGenerator S σ) =
      ∑ j : Fin (q+2), (-1 : ℤ)^j.val •
        smoothGenerator S ⟨SingularChains.face j σ.val,
          SmoothSingularComparison.isSmoothSimplex_face S σ.property j⟩ := by
  simp only [SmoothSingularComparison.smoothComplex, ChainComplex.of_d]
  apply Subtype.ext
  change SingularChains.boundary ℝ ℝ (TopCat.of M) q (Finsupp.single σ.val 1) = _
  rw [P202.SingularChains.boundary_single]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, smoothGenerator]

/-- Coboundary on the actual Z-graded smooth cochains is evaluation on the
same signed faces; extension by zero does not change nonnegative degrees. -/
theorem evaluateSmoothCochain_coboundary {q : ℕ}
    (c : (SmoothSingularComparison.smoothCochains S).X (q : ℤ))
    (σ : SmoothSimplex S (q+1)) :
    evaluateSmoothCochain S
        ((SmoothSingularComparison.smoothCochains S).d (q : ℤ) (q+1 : ℕ) c) σ =
      ∑ j : Fin (q+2), (-1 : ℝ)^j.val *
        evaluateSmoothCochain S c
          ⟨SingularChains.face j σ.val,
            SmoothSingularComparison.isSmoothSimplex_face S σ.property j⟩ := by
  change ((SmoothSingularComparison.smoothOrdinaryComplex S).X (q : ℤ) →ₗ[ℝ] ℝ) at c
  change c ((SmoothSingularComparison.smoothOrdinaryComplex S).d (q+1 : ℕ) (q : ℤ)
    ((smoothDegreeIso S (q+1)).inv (smoothGenerator S σ))) = _
  have hi : (SingularChains.degreeEmbedding 0).f (q+1) = ((q+1 : ℕ) : ℤ) := by
    change (0 : ℤ) + (q+1 : ℕ) = (q+1 : ℕ)
    omega
  have hj : (SingularChains.degreeEmbedding 0).f q = (q : ℤ) := by
    change (0 : ℤ) + q = q
    omega
  rw [show (SmoothSingularComparison.smoothOrdinaryComplex S).d (q+1 : ℕ) (q : ℤ) =
      (smoothDegreeIso S (q+1)).hom ≫ (SmoothSingularComparison.smoothComplex S).d (q+1) q ≫
        (smoothDegreeIso S q).inv from
    HomologicalComplex.extend_d_eq _ _ hi hj]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  change c ((smoothDegreeIso S q).inv
    ((SmoothSingularComparison.smoothComplex S).d (q+1) q (smoothGenerator S σ))) = _
  rw [smoothBoundary_generator]
  simp [map_sum, map_zsmul, evaluateSmoothCochain, zsmul_eq_mul]

/-- The P104 Stokes map is a genuine cochain map in every nonnegative shared
degree, with no isomorphism assumption or omitted endpoint degree. -/
theorem integrationInDegree_commutes
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ) (ω : K.forms q) :
    integrationInDegree S I (q+1) (K.d q ω) =
      (SmoothSingularComparison.smoothCochains S).d (q : ℤ) (q+1 : ℕ)
        (integrationInDegree S I q ω) := by
  apply smoothCochain_ext S
  intro σ
  rw [evaluateSmoothCochain_coboundary]
  exact integrationInDegree_stokes S I q ω σ

/-- The degree-zero integral is point evaluation, with the P104 empty-product
normalization on the same geometric zero simplex. -/
theorem integrationInDegree_zero
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K)
    (ω : K.forms 0) (σ : SmoothSimplex S 0) (x : SmoothSingularData.Simplex 0) :
    evaluateSmoothCochain S (integrationInDegree S I 0 ω) σ =
      exteriorPower.zeroEquiv ℝ
        (Module.Dual ℝ (TangentData.TangentSpace S ((p104Simplex S σ).val x)))
        (ω.val ((p104Simplex S σ).val x)) := by
  rw [integrationInDegree_evaluation]
  exact IntegrationCochain.simplexIntegral_zero ω.val (p104Simplex S σ) x

/-- Integration takes all closed forms into the actual categorical cocycles. -/
def integrationToCycles
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ) :
    ModuleCat.of ℝ (K.closed q) ⟶ (SmoothSingularComparison.smoothCochains S).cycles (q : ℤ) :=
  (SmoothSingularComparison.smoothCochains S).liftCycles'
    (ModuleCat.ofHom ((integrationInDegree S I q).comp (K.closed q).subtype))
    (q+1 : ℕ) (by change (q : ℤ) + 1 = (q+1 : ℕ); omega) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      change (SmoothSingularComparison.smoothCochains S).d (q : ℤ) (q+1 : ℕ)
        (integrationInDegree S I q ω.val) = 0
      rw [← integrationInDegree_commutes]
      have hω : K.d q ω.val = 0 := ω.property
      rw [hω, map_zero])

@[simp] theorem integrationToCycles_i
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ) (ω : K.closed q) :
    (SmoothSingularComparison.smoothCochains S).iCycles (q : ℤ)
      (integrationToCycles S I q ω) = integrationInDegree S I q ω.val := by
  have h : integrationToCycles S I q ≫
      (SmoothSingularComparison.smoothCochains S).iCycles (q : ℤ) =
      ModuleCat.ofHom ((integrationInDegree S I q).comp (K.closed q).subtype) :=
    by
      unfold integrationToCycles HomologicalComplex.liftCycles'
      exact HomologicalComplex.liftCycles_i _ _ ((q+1 : ℕ) : ℤ) _ _
  exact congrArg (fun f => f.hom ω) h

/-- Exact intrinsic forms give the zero smooth singular cohomology class.
The incoming degree-zero submodule is zero, as required for ordinary cohomology. -/
theorem integrationToCycles_boundary
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ) (ω : K.closed q)
    (hω : ω ∈ K.boundaries q) :
    (SmoothSingularComparison.smoothCochains S).homologyπ (q : ℤ)
      (integrationToCycles S I q ω) = 0 := by
  cases q with
  | zero =>
      have hz : ω.val = 0 := hω
      have hz' : ω = 0 := Subtype.ext hz
      change ((SmoothSingularComparison.smoothCochains S).homologyπ 0).hom
        ((integrationToCycles S I 0).hom ω) = 0
      rw [hz', map_zero, map_zero]
  | succ q =>
      obtain ⟨η, hη⟩ := hω
      have heq : integrationToCycles S I (q+1) ω =
          (SmoothSingularComparison.smoothCochains S).toCycles (q : ℤ) (q+1 : ℕ)
            (integrationInDegree S I q η) := by
        apply (ModuleCat.mono_iff_injective
          ((SmoothSingularComparison.smoothCochains S).iCycles (q+1 : ℕ))).mp inferInstance
        rw [integrationToCycles_i]
        have ht := congrArg (fun f => f (integrationInDegree S I q η))
          ((SmoothSingularComparison.smoothCochains S).toCycles_i (q : ℤ) (q+1 : ℕ))
        change (SmoothSingularComparison.smoothCochains S).iCycles (q+1 : ℕ)
            ((SmoothSingularComparison.smoothCochains S).toCycles (q : ℤ) (q+1 : ℕ)
              (integrationInDegree S I q η)) =
            (SmoothSingularComparison.smoothCochains S).d (q : ℤ) (q+1 : ℕ)
              (integrationInDegree S I q η) at ht
        change _ = (SmoothSingularComparison.smoothCochains S).iCycles (q+1 : ℕ)
          ((SmoothSingularComparison.smoothCochains S).toCycles (q : ℤ) (q+1 : ℕ)
            (integrationInDegree S I q η))
        rw [ht]
        rw [← integrationInDegree_commutes]
        exact congrArg (integrationInDegree S I (q+1)) hη.symm
      rw [heq]
      exact congrArg (fun f => f (integrationInDegree S I q η))
        ((SmoothSingularComparison.smoothCochains S).toCycles_comp_homologyπ (q : ℤ) (q+1 : ℕ))

/-- The actual induced linear map to shared smooth cohomology. Its bijectivity
is the remaining local-to-global mathematical obligation. -/
def smoothIntegrationCohomology
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ) :
    K.Cohomology q →ₗ[ℝ] (SmoothSingularComparison.smoothCochains S).homology (q : ℤ) :=
  (K.boundaries q).liftQ
    ((integrationToCycles S I q ≫
      (SmoothSingularComparison.smoothCochains S).homologyπ (q : ℤ)).hom)
    (fun ω hω => integrationToCycles_boundary S I q ω hω)

@[simp] theorem smoothIntegrationCohomology_class
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ) (ω : K.closed q) :
    smoothIntegrationCohomology S I q (K.classOf q ω) =
      (SmoothSingularComparison.smoothCochains S).homologyπ (q : ℤ)
        (integrationToCycles S I q ω) := rfl

/-- The independent specification's literal-integral characterization equals
the class of the cochain map constructed above. No comparison isomorphism is
used to establish this bridge. -/
theorem isIntegrationClass_iff
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) {q : ℕ} (ω : K.closed q)
    (x : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ)) :
    IsIntegrationClass S C ω.val.val x ↔
      homologyMap (SmoothSingularComparison.restriction S) (q : ℤ) x =
        smoothIntegrationCohomology S I q (K.classOf q ω) := by
  constructor
  · rintro ⟨c, hc, he⟩
    have hrep : c = integrationToCycles S I q ω := by
      apply (ModuleCat.mono_iff_injective
        ((SmoothSingularComparison.smoothCochains S).iCycles (q : ℤ))).mp inferInstance
      apply smoothCochain_ext S
      intro σ
      rw [integrationToCycles_i, integrationInDegree_evaluation]
      exact he σ
    rw [← hc, hrep, smoothIntegrationCohomology_class]
  · intro h
    refine ⟨integrationToCycles S I q ω, ?_, ?_⟩
    · exact h.symm
    · intro σ
      rw [integrationToCycles_i, integrationInDegree_evaluation]

/-- Pure assembly step, separating the still-unproved bijectivity assertion
from the already proved cochain/quotient bridges. The original target does not
have the extra premise `hbij`; it must be proved by local-to-global descent. -/
theorem integrationComparisonOfBijective
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K)
    (hres : ∀ q : ℕ, IsIso (homologyMap (SmoothSingularComparison.restriction S) (q : ℤ)))
    (hbij : ∀ q : ℕ, Function.Bijective (smoothIntegrationCohomology S I q)) :
    ∃ e : ComparisonFamily S K, IsIntegrationComparison S K e := by
  let e : ComparisonFamily S K := fun q =>
    letI := hres q
    (LinearEquiv.ofBijective (smoothIntegrationCohomology S I q) (hbij q)).trans
      (asIso (homologyMap (SmoothSingularComparison.restriction S) (q : ℤ))).symm.toLinearEquiv
  refine ⟨e, hres, ?_⟩
  intro q ω
  rw [isIntegrationClass_iff S I ω]
  letI := hres q
  exact Iso.inv_hom_id_apply
    (asIso (homologyMap (SmoothSingularComparison.restriction S) (q : ℤ)))
    (smoothIntegrationCohomology S I q (K.classOf q ω))

section Naturality
variable {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
  (T : AtlasData.SmoothManifold m b N)
  (f : M → N) (hf : MapData.IsSmoothMap S T f)

/-- Postcomposition on the literal smooth subset of the ordinary simplex basis. -/
def smoothSimplexMap {q : ℕ} (σ : SmoothSimplex S q) : SmoothSimplex T q :=
  ⟨(TopCat.toSSet.map (SmoothSingularComparison.underlyingMap S T f hf)).app
    (op ⦋q⦌) σ.val, SmoothSingularComparison.isSmoothSimplex_map S T f hf q σ.property⟩

@[simp] theorem p104Simplex_map {q : ℕ} (σ : SmoothSimplex S q) :
    p104Simplex T (smoothSimplexMap S T f hf σ) =
      ⟨f ∘ (p104Simplex S σ).val,
        SmoothSingular.smooth_postcompose hf (p104Simplex S σ).property⟩ := by
  apply Subtype.ext
  funext x
  have h := P202.SingularChains.simplexEquiv_postcomp
    (SmoothSingularComparison.underlyingMap S T f hf) q σ.val
  exact congrArg (fun g => g (SmoothSingularComparison.toBarycentric q x)) h

@[simp] theorem smoothChainMap_generator {q : ℕ} (σ : SmoothSimplex S q) :
    (SmoothSingularComparison.smoothChainMap S T f hf).f q (smoothGenerator S σ) =
      smoothGenerator T (smoothSimplexMap S T f hf σ) := by
  apply Subtype.ext
  exact P202.SingularChains.chainMap_single ℝ ℝ
    (SmoothSingularComparison.underlyingMap S T f hf) q σ.val 1

/-- Extension by zero preserves the literal generator formula in degree q≥0. -/
theorem smoothOrdinaryMap_generator {q : ℕ} (σ : SmoothSimplex S q) :
    (SmoothSingularComparison.smoothOrdinaryMap S T f hf).f (q : ℤ)
      ((smoothDegreeIso S q).inv (smoothGenerator S σ)) =
        (smoothDegreeIso T q).inv (smoothGenerator T (smoothSimplexMap S T f hf σ)) := by
  have hq : (SingularChains.degreeEmbedding 0).f q = (q : ℤ) := by
    change (0 : ℤ) + q = q
    omega
  rw [show (SmoothSingularComparison.smoothOrdinaryMap S T f hf).f (q : ℤ) =
      (smoothDegreeIso S q).hom ≫
        (SmoothSingularComparison.smoothChainMap S T f hf).f q ≫
          (smoothDegreeIso T q).inv from HomologicalComplex.extendMap_f _ _ hq]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  change (smoothDegreeIso T q).inv
    ((SmoothSingularComparison.smoothChainMap S T f hf).f q (smoothGenerator S σ)) = _
  rw [smoothChainMap_generator]

/-- The actual shared cochain pullback evaluates by postcomposition. -/
theorem evaluateSmoothCochain_pullback {q : ℕ}
    (c : (SmoothSingularComparison.smoothCochains T).X (q : ℤ))
    (σ : SmoothSimplex S q) :
    evaluateSmoothCochain S
      ((SmoothSingularComparison.smoothCochainMap S T f hf).f (q : ℤ) c) σ =
        evaluateSmoothCochain T c (smoothSimplexMap S T f hf σ) := by
  change ((SmoothSingularComparison.smoothOrdinaryComplex T).X (q : ℤ) →ₗ[ℝ] ℝ) at c
  change c ((SmoothSingularComparison.smoothOrdinaryMap S T f hf).f (q : ℤ)
    ((smoothDegreeIso S q).inv (smoothGenerator S σ))) = _
  rw [smoothOrdinaryMap_generator]
  rfl

/-- Forgetting smoothness commutes with the actual chain pushforward. -/
theorem smoothChainMap_inclusion :
    SmoothSingularComparison.smoothChainMap S T f hf ≫ SmoothSingularComparison.inclusion T =
      SmoothSingularComparison.inclusion S ≫
        SingularChains.chainMap ℝ ℝ (SmoothSingularComparison.underlyingMap S T f hf) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

/-- The same square after extending by zero to all integer degrees. -/
theorem smoothOrdinaryMap_inclusion :
    SmoothSingularComparison.smoothOrdinaryMap S T f hf ≫
        SmoothSingularComparison.ordinaryInclusion T =
      SmoothSingularComparison.ordinaryInclusion S ≫
        (SingularChains.ordinaryFunctor ℝ ℝ).map
          (SmoothSingularComparison.underlyingMap S T f hf) := by
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ =
    HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    smoothChainMap_inclusion]

/-- Restriction and smooth pullback commute as literal shared cochain maps. -/
theorem restriction_pullback :
    (P202Specs.CohomologyPairs.ordinaryCochainFunctor ℝ ℝ).map
        (SmoothSingularComparison.underlyingMap S T f hf).op ≫
      SmoothSingularComparison.restriction S =
    SmoothSingularComparison.restriction T ≫
      SmoothSingularComparison.smoothCochainMap S T f hf := by
  have h := congrArg
    (fun g => (P202Specs.CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).map g.op)
    (smoothOrdinaryMap_inclusion S T f hf)
  simpa only [Functor.comp_map, Functor.op_map, op_comp, Functor.map_comp] using! h.symm

/-- The ordinary/smooth restriction square on cohomology requires no comparison
isomorphism theorem: it follows from the literal chain square. -/
theorem restriction_cohomology_pullback (q : ℤ) :
    (P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ q).map
        (SmoothSingularComparison.underlyingMap S T f hf).op ≫
      homologyMap (SmoothSingularComparison.restriction S) q =
    homologyMap (SmoothSingularComparison.restriction T) q ≫
      homologyMap (SmoothSingularComparison.smoothCochainMap S T f hf) q := by
  change homologyMap _ q ≫ homologyMap _ q = homologyMap _ q ≫ homologyMap _ q
  rw [← homologyMap_comp, ← homologyMap_comp, restriction_pullback]

/-- Pulling back a literal integration class gives the literal integration
class of the pulled-back field. This uses the shared categorical cycles. -/
theorem integrationClass_pullback
    (C : CotangentBundle S) (A : CotangentBundle T)
    {q : ℕ} (E : FormBundle A q) (α : Field T q) (hα : IsForm E α)
    (L : (p : M) → TangentData.TangentSpace S p →ₗ[ℝ] TangentData.TangentSpace T (f p))
    (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
    (x : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of N) (q : ℤ))
    (hx : IsIntegrationClass T A α x) :
    IsIntegrationClass S C (FormPullbackData.pullbackField S T f L α)
      ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map
        (SmoothSingularComparison.underlyingMap S T f hf).op x) := by
  obtain ⟨c, hc, he⟩ := hx
  let F := SmoothSingularComparison.smoothCochainMap S T f hf
  refine ⟨cyclesMap F (q : ℤ) c, ?_, ?_⟩
  · have hπ := congrArg (fun g => g.hom c) (homologyπ_naturality F (q : ℤ))
    have hsq := congrArg (fun g => g.hom x)
      (restriction_cohomology_pullback S T f hf (q : ℤ))
    change homologyMap F (q : ℤ)
        ((SmoothSingularComparison.smoothCochains T).homologyπ (q : ℤ) c) =
      (SmoothSingularComparison.smoothCochains S).homologyπ (q : ℤ)
        (cyclesMap F (q : ℤ) c) at hπ
    change homologyMap (SmoothSingularComparison.restriction S) (q : ℤ)
        ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map
          (SmoothSingularComparison.underlyingMap S T f hf).op x) =
      homologyMap F (q : ℤ)
        (homologyMap (SmoothSingularComparison.restriction T) (q : ℤ) x) at hsq
    exact hπ.symm.trans ((congrArg (fun y => homologyMap F (q : ℤ) y) hc).trans hsq.symm)
  · intro σ
    have hi := congrArg (fun g => g.hom c) (cyclesMap_i F (q : ℤ))
    change (SmoothSingularComparison.smoothCochains S).iCycles (q : ℤ)
        (cyclesMap F (q : ℤ) c) =
      F.f (q : ℤ) ((SmoothSingularComparison.smoothCochains T).iCycles (q : ℤ) c) at hi
    rw [hi, evaluateSmoothCochain_pullback, he, p104Simplex_map]
    exact (IntegrationCochain.naturality S T C A f hf L hL α E hα
      (p104Simplex S σ)
      (SmoothSingular.smooth_postcompose hf (p104Simplex S σ).property)).symm

end Naturality

section ComparisonNaturality
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The complete naturality assertion for the original comparison family,
proved without any isomorphism-existence premise or upstream draft theorem. -/
theorem comparisonNaturality : P202Specs.DeRhamComparison.comparisonNaturality_type.{u} := by
  intro n m a b M N _ _ S T C A B E K J e h he hh f hf L hL P hP q x
  refine Submodule.Quotient.induction_on _ x ?_
  intro α
  have hpα := hP q α
  let β : K.closed q := hpα.choose
  have hβ := hpα.choose_spec.1
  have hPβ := hpα.choose_spec.2
  have hclass := integrationClass_pullback S T f hf C A (E q) α.val.val
    ((J.mem_forms q α.val.val).mp α.val.property) L hL _ (hh.2 q α)
  have hclass' : IsIntegrationClass S C β.val.val
      ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map
        (SmoothSingularComparison.underlyingMap S T f hf).op (h q (J.classOf q α))) := by
    rw [show β.val.val = _ from hβ]
    exact hclass
  letI := he.1 q
  exact (congrArg (e q) hPβ).trans
    (integrationClass_unique S C β.val.val (he.2 q β) hclass')

end ComparisonNaturality

section DegreeZero
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false

/-- Constant maps on every corner simplex satisfy the actual local ambient
extension condition in every chart, also at boundary points of M. -/
def constantP104Simplex (p : M) (q : ℕ) : SmoothSingularData.SingularSimplex S q :=
  ⟨fun _ => p, continuous_const, by
    intro x d hd hx
    exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => (d p).val,
      contDiff_const.contDiffOn, Filter.Eventually.of_forall (fun _ => rfl)⟩⟩

/-- There is no incoming smooth coboundary in degree zero. -/
theorem smoothCochain_d_neg_one_zero :
    (SmoothSingularComparison.smoothCochains S).d (-1) 0 = 0 := by
  have hz : CategoryTheory.Limits.IsZero
      ((SmoothSingularComparison.smoothOrdinaryComplex S).X (-1)) :=
    (SmoothSingularComparison.smoothComplex S).isZero_extend_X
      (SingularChains.degreeEmbedding 0) (-1) (by
        intro q
        change (0 : ℤ) + q ≠ -1
        omega)
  have hd : (SmoothSingularComparison.smoothOrdinaryComplex S).d 0 (-1) = 0 :=
    hz.eq_of_tgt _ _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((SmoothSingularComparison.smoothOrdinaryComplex S).X (-1) →ₗ[ℝ] ℝ) at c
  change c.comp ((SmoothSingularComparison.smoothOrdinaryComplex S).d 0 (-1)).hom = 0
  rw [hd]
  exact LinearMap.comp_zero _

/-- At degree zero the actual cycles-to-cohomology quotient is an isomorphism. -/
theorem smoothHomologyπ_zero_isIso :
    IsIso ((SmoothSingularComparison.smoothCochains S).homologyπ (0 : ℤ)) :=
  (SmoothSingularComparison.smoothCochains S).isIso_homologyπ (-1) 0 (by
      apply ComplexShape.prev_eq'
      change (-1 : ℤ) + 1 = 0
      norm_num)
    (smoothCochain_d_neg_one_zero S)

/-- Integration is injective on H⁰ for every manifold in the original scope.
This follows from point evaluation and the absence of incoming boundaries,
and does not assume any comparison or local-to-global certificate. -/
theorem smoothIntegrationCohomology_zero_injective
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) :
    Function.Injective (smoothIntegrationCohomology S I 0) := by
  intro x y
  refine Submodule.Quotient.induction_on _ x ?_
  intro α
  refine Submodule.Quotient.induction_on _ y ?_
  intro β hxy
  letI := smoothHomologyπ_zero_isIso S
  have hc : integrationToCycles S I 0 α = integrationToCycles S I 0 β :=
    (ModuleCat.mono_iff_injective
      ((SmoothSingularComparison.smoothCochains S).homologyπ (0 : ℤ))).mp inferInstance hxy
  change K.classOf 0 α = K.classOf 0 β
  apply congrArg (K.classOf 0)
  apply Subtype.ext
  apply Subtype.ext
  funext p
  let τ := constantP104Simplex S p 0
  let σ : SmoothSimplex S 0 := (p104SimplexEquiv S 0).symm τ
  have hσ : p104Simplex S σ = τ := (p104SimplexEquiv S 0).apply_symm_apply τ
  let x₀ := SmoothSingularData.vertex (0 : Fin 1)
  have hv := congrArg (fun c => evaluateSmoothCochain S
    ((SmoothSingularComparison.smoothCochains S).iCycles (0 : ℤ) c) σ) hc
  have hα := congrArg (fun c => evaluateSmoothCochain S c σ)
    (integrationToCycles_i S I 0 α)
  have hβ := congrArg (fun c => evaluateSmoothCochain S c σ)
    (integrationToCycles_i S I 0 β)
  have hv' := (integrationInDegree_zero S I α.val σ x₀).symm.trans
    ((hα.symm.trans (hv.trans hβ)).trans (integrationInDegree_zero S I β.val σ x₀))
  apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentData.TangentSpace S p))).injective
  have hp : (p104Simplex S σ).val x₀ = p :=
    congrArg (fun t : SmoothSingularData.SingularSimplex S 0 => t.val x₀) hσ
  exact (congrArg (fun z =>
    exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentData.TangentSpace S z)) (α.val.val z)) hp).symm.trans
      (hv'.trans (congrArg (fun z =>
        exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentData.TangentSpace S z)) (β.val.val z)) hp))

end DegreeZero


section LocalComparison

/-- Positive-degree ordinary real cohomology vanishes on every nonempty
contractible space, using the actual full-dual evaluation isomorphism. -/
theorem ordinaryCohomology_positive_isZero_of_contractible
    (X : TopCat.{u}) [Nonempty X] [ContractibleSpace X]
    (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Limits.IsZero (P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ X (q : ℤ)) := by
  have hz : CategoryTheory.Limits.IsZero (SingularChains.homology ℝ ℝ X (q : ℤ)) :=
    (P202.SingularDegreeZero.reducedPositiveIso ℝ ℝ X q hq).isZero_iff.mp
      (P202.PrismHomotopy.contractible ℝ ℝ X (q : ℤ))
  letI := ModuleCat.subsingleton_of_isZero hz
  let E := LinearEquiv.ofBijective
    (UniversalCoefficients.evaluation ℝ ℝ (SingularChains.ordinaryComplex ℝ ℝ X) (q : ℤ))
    (P202.UniversalCoefficients.evaluation_bijective ℝ
      (SingularChains.ordinaryComplex ℝ ℝ X) (q : ℤ))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => E.injective (Subsingleton.elim _ _)⟩


/-- Local positive-degree comparison, valid for either manifold model.
The full smooth-singular premise is explicit; no global de Rham comparison
is assumed. Both actual cohomology spaces vanish by contraction. -/
theorem smoothIntegrationCohomology_positive_bijective_of_contractible
    (hcomparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    [Nonempty M] [ContractibleSpace M]
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ) (hq : 0 < q) :
    Function.Bijective (smoothIntegrationCohomology S I q) := by
  letI := HomotopyResults.contractible_vanishing S C B K q hq
  letI := (hcomparison.1 S (q : ℤ)).2
  have hz := ordinaryCohomology_positive_isZero_of_contractible (TopCat.of M) q hq
  have hs : CategoryTheory.Limits.IsZero ((SmoothSingularComparison.smoothCochains S).homology (q : ℤ)) :=
    (asIso (homologyMap (SmoothSingularComparison.restriction S) (q : ℤ))).isZero_iff.mp hz
  letI := ModuleCat.subsingleton_of_isZero hs
  constructor
  · intro x y _
    exact Subsingleton.elim _ _
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩

end LocalComparison

section ComparisonReduction

/-- Every comparison satisfying the literal integration specification
restricts to the constructed smooth integration map on all classes. -/
theorem smoothIntegrationCohomology_eq_comparison
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K)
    (e : ComparisonFamily S K) (he : IsIntegrationComparison S K e) (q : ℕ) :
    smoothIntegrationCohomology S I q =
      (homologyMap (SmoothSingularComparison.restriction S) (q : ℤ)).hom.comp
        (e q).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨ω, rfl⟩ := (K.boundaries q).mkQ_surjective x
  exact ((isIntegrationClass_iff S I ω _).mp (he.2 q ω)).symm

/-- Bijectivity of smooth integration is necessary as well as sufficient
for the specified integration comparison. -/
theorem smoothIntegrationCohomology_bijective_of_comparison
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K)
    (e : ComparisonFamily S K) (he : IsIntegrationComparison S K e) (q : ℕ) :
    Function.Bijective (smoothIntegrationCohomology S I q) := by
  rw [smoothIntegrationCohomology_eq_comparison S I e he q]
  letI := he.1 q
  exact (asIso (homologyMap (SmoothSingularComparison.restriction S) (q : ℤ))).toLinearEquiv.bijective.comp
    (e q).bijective

/-- Exact reduction of the original target to the remaining global
bijectivity obligation. This equivalence does not prove either side. -/
theorem deRhamComparison_iff_smoothIntegrationBijective
    (hcomparison : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    P202Specs.DeRhamComparison.deRhamComparison_type.{u} ↔
      ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
        (S : AtlasData.SmoothManifold n a M) (C : CotangentBundle S)
        (B : ∀ k, FormBundle C k) (K : Calculus C B)
        (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ),
        Function.Bijective (smoothIntegrationCohomology S I q) := by
  constructor
  · intro h n a M _ S C B K I q
    obtain ⟨e, he⟩ := h.1 S C B K
    exact smoothIntegrationCohomology_bijective_of_comparison S I e he q
  · intro h
    refine ⟨?_, comparisonNaturality⟩
    intro n a M _ S C B K
    obtain ⟨I⟩ := IntegrationCochain.integration_exists S C B K
    exact integrationComparisonOfBijective S I
      (fun q => (hcomparison.1 S (q : ℤ)).2) (h S C B K I)

end ComparisonReduction

section EmptyManifold

attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false

/-- Empty manifolds have zero forms and no smooth simplex generators,
so integration is bijective in every nonnegative degree. -/
theorem smoothIntegrationCohomology_empty_bijective [IsEmpty M]
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ) :
    Function.Bijective (smoothIntegrationCohomology S I q) := by
  constructor
  · intro x y _
    refine Submodule.Quotient.induction_on _ x ?_
    intro α
    refine Submodule.Quotient.induction_on _ y ?_
    intro β
    change K.classOf q α = K.classOf q β
    apply congrArg (K.classOf q)
    apply Subtype.ext
    apply Subtype.ext
    funext p
    exact isEmptyElim p
  · intro x
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((SmoothSingularComparison.smoothCochains S).homologyπ (q : ℤ))).mp inferInstance x
    refine ⟨0, ?_⟩
    have hc : c = 0 := by
      apply (ModuleCat.mono_iff_injective
        ((SmoothSingularComparison.smoothCochains S).iCycles (q : ℤ))).mp inferInstance
      apply smoothCochain_ext S
      intro σ
      exact isEmptyElim ((p104Simplex S σ).val
        (SmoothSingularData.vertex (⟨0, Nat.zero_lt_succ q⟩ : Fin (q+1))))
    rw [hc, map_zero, map_zero]

/-- The integration comparison for empty manifolds, preserving the
original cocycle characterization and actual inverse restriction. -/
theorem integrationComparison_empty
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    [IsEmpty M] {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) :
    ∃ e : ComparisonFamily S K, IsIntegrationComparison S K e := by
  obtain ⟨I⟩ := SmoothManifolds.IntegrationCochain.integration_exists S C B K
  exact integrationComparisonOfBijective S I (fun q => (hcomp.1 S (q : ℤ)).2)
    (smoothIntegrationCohomology_empty_bijective S I)

end EmptyManifold



section FiniteFiltration
variable {R X Y Z : Type*} [Ring R]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module R X] [Module R Y] [Module R Z]

/-- Finite elimination in a filtered three-term complex. The step hypothesis
is a lift only modulo the preceding filtration stage, rather than an assumed
primitive for the original cycle. No convergence or infinite sum is used. -/
theorem primitive_of_finite_filtration
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hcomplex : g.comp f = 0)
    (F : ℕ → Submodule R Y) (hzero : F 0 = ⊥)
    (hstep : ∀ k y, y ∈ F (k+1) → g y = 0 →
      ∃ x, y - f x ∈ F k) :
    ∀ k y, y ∈ F k → g y = 0 → ∃ x, f x = y := by
  intro k
  induction k with
  | zero =>
      intro y hy _
      have hy0 : y = 0 := by simpa only [hzero, Submodule.mem_bot] using hy
      exact ⟨0, (map_zero f).trans hy0.symm⟩
  | succ k ih =>
      intro y hy hgy
      obtain ⟨x, hx⟩ := hstep k y hy hgy
      have hgf : g (f x) = 0 := LinearMap.congr_fun hcomplex x
      have hres : g (y - f x) = 0 := by rw [map_sub, hgy, hgf, sub_self]
      obtain ⟨z, hz⟩ := ih (y - f x) hx hres
      refine ⟨z + x, ?_⟩
      rw [map_add, hz, sub_add_cancel]

/-- Exactness follows if every cycle lies in a finite filtration stage.
For a bounded-below bicomplex in a fixed total degree this is the finite
diagonal termination condition. The local lifting condition remains an
explicit separate obligation supplied by exactness of the leading row. -/
theorem exact_of_exhaustive_filtration
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hcomplex : g.comp f = 0)
    (F : ℕ → Submodule R Y) (hzero : F 0 = ⊥)
    (hexhaustive : ∀ y, ∃ k, y ∈ F k)
    (hstep : ∀ k y, y ∈ F (k+1) → g y = 0 →
      ∃ x, y - f x ∈ F k) :
    Function.Exact f g := by
  intro y
  constructor
  · intro hgy
    obtain ⟨k, hk⟩ := hexhaustive y
    exact primitive_of_finite_filtration f g hcomplex F hzero hstep k y hk hgy
  · rintro ⟨x, rfl⟩
    exact LinearMap.congr_fun hcomplex x

end FiniteFiltration

section OneBicomplexStep
variable {R A B C A' B' : Type*} [Ring R]
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup A'] [AddCommGroup B']
  [Module R A] [Module R B] [Module R C] [Module R A'] [Module R B']

/-- One step of diagonal cocycle elimination. The vertical maps include the
usual horizontal-degree signs, so the relevant square anticommutes. Exactness
of the horizontal row kills the first component and makes the corrected next
component horizontally closed. -/
theorem bicomplex_cycle_elimination
    (h : A →ₗ[R] B) (k : B →ₗ[R] C) (h' : A' →ₗ[R] B')
    (v : A →ₗ[R] A') (w : B →ₗ[R] B')
    (hrow : Function.Exact h k)
    (hanticommute : w.comp h + h'.comp v = 0)
    (b : B) (c : A') (hfirst : k b = 0) (hnext : w b + h' c = 0) :
    ∃ a, h a = b ∧ h' (c - v a) = 0 := by
  obtain ⟨a, ha⟩ := (hrow b).mp hfirst
  refine ⟨a, ha, ?_⟩
  have hanti : w (h a) + h' (v a) = 0 :=
    LinearMap.congr_fun hanticommute a
  rw [ha] at hanti
  have heq : h' c = h' (v a) :=
    add_left_cancel (hnext.trans hanti.symm)
  rw [map_sub, heq, sub_self]

end OneBicomplexStep

namespace CoverForms

open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  SmoothManifolds.CovectorData SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
  SmoothManifolds.MayerVietorisData SmoothManifolds.MayerVietorisData.OpenForms
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {C : CotangentBundle S}
  {B : ∀ k, FormBundle C k} (K : Calculus C B)
  {ι : Type v} (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)

def coverOpen (i : ι) : TopologicalSpace.Opens M := ⟨U.sets i, U.isOpen i⟩

def globalFormCoverRestriction
    (D : ∀ i, OpenCalculus C B (coverOpen U i)) (q : ℕ) :
    K.forms q →ₗ[ℝ] ((i : ι) → (D i).complex.Obj q) where
  toFun ω i := (globalRestriction K (coverOpen U i) (D i)).map q ω
  map_add' ω η := by funext i; exact map_add _ _ _
  map_smul' r ω := by funext i; exact map_smul _ _ _

theorem globalFormCoverRestriction_injective
    (D : ∀ i, OpenCalculus C B (coverOpen U i)) (q : ℕ) :
    Function.Injective (globalFormCoverRestriction S K U D q) := by
  intro ω η he
  apply Subtype.ext
  funext p
  obtain ⟨i, hi⟩ := U.covers p
  have h := congrArg (fun z => (D i).field q z ⟨p, hi⟩) (congrFun he i)
  change (D i).field q ((globalRestriction K (coverOpen U i) (D i)).map q ω) ⟨p, hi⟩ =
    (D i).field q ((globalRestriction K (coverOpen U i) (D i)).map q η) ⟨p, hi⟩ at h
  simpa only [globalRestriction_field] using h

/-- Pairwise compatible actual smooth restricted forms glue uniquely on an
arbitrary open cover, with no finiteness or nonemptiness hypothesis. -/
theorem exists_unique_global_form_of_compatible
    (q : ℕ) (ω : (i : ι) → RestrictedField S (coverOpen U i) q)
    (hω : ∀ i, IsRestrictedForm (B q) (coverOpen U i) (ω i))
    (hcompat : ∀ (i j : ι) (p : M) (hi : p ∈ U.sets i) (hj : p ∈ U.sets j),
      ω i ⟨p, hi⟩ = ω j ⟨p, hj⟩) :
    ∃! α : K.forms q, ∀ (i : ι) (p : coverOpen U i), α.val p.val = ω i p := by
  classical
  let index : M → ι := fun p => (U.covers p).choose
  have hindex (p : M) : p ∈ U.sets (index p) := (U.covers p).choose_spec
  let α : Field S q := fun p => ω (index p) ⟨p, hindex p⟩
  have hrestrict (i : ι) (p : coverOpen U i) : α p.val = ω i p :=
    hcompat _ _ _ (hindex p.val) p.property
  have hsmooth : IsForm (B q) α := by
    letI := (cotangentSpace C).topology
    letI := (B q).space.topology
    let f : M → Bundle.TotalSpace (ModelData.Euclidean (n.choose q))
        (fun p => Fiber (TangentData.TangentSpace S p) q) := fun p => ⟨p, α p⟩
    have hi (i : ι) : MapData.ManifoldSmoothOn S.smoothStructure.val
        (B q).space.bundle.totalManifold.smoothStructure.val f (coverOpen U i) := by
      apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ f
        (coverOpen U i) (coverOpen U i).isOpen).mpr
      have he : (fun p : coverOpen U i => f p.val) =
          (fun p : coverOpen U i =>
            (⟨p.val, ω i p⟩ : Bundle.TotalSpace (ModelData.Euclidean (n.choose q))
              (fun p => Fiber (TangentData.TangentSpace S p) q))) := by
        funext p
        exact congrArg (fun z => (⟨p.val, z⟩ : Bundle.TotalSpace
          (ModelData.Euclidean (n.choose q)) (fun p => Fiber (TangentData.TangentSpace S p) q))) (hrestrict i p)
      exact he.symm ▸ hω i
    intro p
    exact hi (index p) p (hindex p)
  refine ⟨⟨α, (K.mem_forms q α).mpr hsmooth⟩, hrestrict, ?_⟩
  intro β hβ
  apply Subtype.ext
  funext p
  obtain ⟨i, hi⟩ := U.covers p
  exact (hβ i ⟨p, hi⟩).trans (hrestrict i ⟨p, hi⟩).symm

/-- Actual alternating restriction to double intersections, in any full
realizations of the intrinsic restricted form spaces. -/
def formCoverDifference
    (D : ∀ i, OpenCalculus C B (coverOpen U i))
    (E : ∀ i j, OpenCalculus C B (coverOpen U i ⊓ coverOpen U j)) (q : ℕ) :
    ((i : ι) → (D i).complex.Obj q) →ₗ[ℝ]
      ((i j : ι) → (E i j).complex.Obj q) where
  toFun ω i j :=
    (openRestriction (coverOpen U j) (coverOpen U i ⊓ coverOpen U j)
      inf_le_right (D j) (E i j)).map q (ω j) -
    (openRestriction (coverOpen U i) (coverOpen U i ⊓ coverOpen U j)
      inf_le_left (D i) (E i j)).map q (ω i)
  map_add' ω η := by
    funext i j
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' r ω := by
    funext i j
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub]

@[simp] theorem formCoverDifference_field
    (D : ∀ i, OpenCalculus C B (coverOpen U i))
    (E : ∀ i j, OpenCalculus C B (coverOpen U i ⊓ coverOpen U j)) (q : ℕ)
    (ω : (i : ι) → (D i).complex.Obj q) (i j : ι)
    (p : ↥(coverOpen U i ⊓ coverOpen U j)) :
    (E i j).field q (formCoverDifference S U D E q ω i j) p =
      (D j).field q (ω j) ⟨p.val, p.property.2⟩ -
      (D i).field q (ω i) ⟨p.val, p.property.1⟩ := by
  change (E i j).field q (_ - _) p = _
  simp only [map_sub, Pi.sub_apply, openRestriction_field]

theorem formCoverDifference_eq_zero_iff
    (D : ∀ i, OpenCalculus C B (coverOpen U i))
    (E : ∀ i j, OpenCalculus C B (coverOpen U i ⊓ coverOpen U j)) (q : ℕ)
    (ω : (i : ι) → (D i).complex.Obj q) :
    formCoverDifference S U D E q ω = 0 ↔
      ∀ (i j : ι) (p : M) (hi : p ∈ U.sets i) (hj : p ∈ U.sets j),
        (D i).field q (ω i) ⟨p, hi⟩ = (D j).field q (ω j) ⟨p, hj⟩ := by
  constructor
  · intro he i j p hi hj
    have h := congrArg (fun x => (E i j).field q x ⟨p, hi, hj⟩)
      (congrFun (congrFun he i) j)
    have hz : (D j).field q (ω j) ⟨p, hj⟩ - (D i).field q (ω i) ⟨p, hi⟩ = 0 := by
      simpa only [formCoverDifference_field, Pi.zero_apply, map_zero] using h
    exact (sub_eq_zero.mp hz).symm
  · intro hcompat
    funext i j
    apply (E i j).injective q
    funext p
    simp only [formCoverDifference_field, Pi.zero_apply, map_zero]
    exact sub_eq_zero.mpr (hcompat j i p.val p.property.2 p.property.1)

/-- Exactness at the first product in the augmented forms Čech row. -/
theorem forms_cover_augmentation_exact
    (D : ∀ i, OpenCalculus C B (coverOpen U i))
    (E : ∀ i j, OpenCalculus C B (coverOpen U i ⊓ coverOpen U j)) (q : ℕ)
    (ω : (i : ι) → (D i).complex.Obj q) :
    formCoverDifference S U D E q ω = 0 ↔
      ∃ α : K.forms q, globalFormCoverRestriction S K U D q α = ω := by
  rw [formCoverDifference_eq_zero_iff]
  constructor
  · intro hcompat
    obtain ⟨α, hα, _⟩ := exists_unique_global_form_of_compatible S K U q
      (fun i => (D i).field q (ω i)) (fun i => field_smooth (D i) q (ω i)) hcompat
    refine ⟨α, ?_⟩
    funext i
    apply (D i).injective q
    funext p
    change (D i).field q ((globalRestriction K (coverOpen U i) (D i)).map q α) p = _
    rw [globalRestriction_field]
    exact hα i p
  · rintro ⟨α, rfl⟩ i j p hi hj
    change (D i).field q ((globalRestriction K (coverOpen U i) (D i)).map q α) ⟨p, hi⟩ =
      (D j).field q ((globalRestriction K (coverOpen U j) (D j)).map q α) ⟨p, hj⟩
    simp only [globalRestriction_field]

end CoverForms


section DegreeZeroSurjectivity

/-- Evaluate an actual ordinary zero-cochain at the point simplex. -/
def ordinaryZeroEval (c : (P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).X (0 : ℤ))
    (p : M) : ℝ :=
  P202Specs.CohomologyPairs.ordinaryCochainsEquiv ℝ ℝ (TopCat.of M) 0 c
    (Finsupp.single (TopCat.toSSetObj₀Equiv.symm p) 1)
/-- A categorical ordinary zero-cocycle is constant along every path. -/
theorem ordinaryZeroEval_path
    (c : (P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).cycles (0 : ℤ))
    {p r : M} (γ : Path p r) :
    ordinaryZeroEval ((P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).iCycles (0 : ℤ) c) p =
      ordinaryZeroEval ((P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).iCycles (0 : ℤ) c) r := by
  let K := P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)
  let a := K.iCycles (0 : ℤ) c
  let σ : SingularChains.Simplex (TopCat.of M) 1 :=
    TopCat.toSSetObj₁Equiv.symm ((TopCat.pathEquiv (X := TopCat.of M)).symm γ).hom
  have ha : K.d (0 : ℤ) 1 a = 0 :=
    congrArg (fun f => f.hom c) (K.iCycles_d (0 : ℤ) 1)
  have hb := P202.CohomologyPairs.natural_coboundary ℝ ℝ (TopCat.of M) 0
    (P202Specs.CohomologyPairs.ordinaryCochainsEquiv ℝ ℝ (TopCat.of M) 0 a)
    (Finsupp.single σ 1)
  rw [LinearEquiv.symm_apply_apply] at hb
  change (P202Specs.CohomologyPairs.ordinaryCochainsEquiv ℝ ℝ (TopCat.of M) 1
    (K.d 0 1 a)) (Finsupp.single σ 1) = _ at hb
  rw [ha, map_zero, LinearMap.zero_apply] at hb
  rw [P202.SingularChains.boundary_single] at hb
  change 0 = (P202Specs.CohomologyPairs.ordinaryCochainsEquiv ℝ ℝ (TopCat.of M) 0 a)
    (∑ i : Fin 2, (-1 : ℤ)^i.val • Finsupp.single (SingularChains.face i σ) (1 : ℝ)) at hb
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero,
    Fin.val_one, pow_one, neg_smul, one_smul, map_add, map_neg] at hb
  have h0 : SingularChains.face (0 : Fin 2) σ = TopCat.toSSetObj₀Equiv.symm r := by
    exact (TopCat.δ_zero_toSSetObj₁Equiv.symm
      ((TopCat.pathEquiv (X := TopCat.of M)).symm γ).hom).trans
      (congrArg (TopCat.toSSetObj₀Equiv (X := TopCat.of M)).symm
        ((TopCat.pathEquiv (X := TopCat.of M)).symm γ).hom₁)
  have h1 : SingularChains.face (1 : Fin 2) σ = TopCat.toSSetObj₀Equiv.symm p := by
    exact (TopCat.δ_one_toSSetObj₁Equiv.symm
      ((TopCat.pathEquiv (X := TopCat.of M)).symm γ).hom).trans
      (congrArg (TopCat.toSSetObj₀Equiv (X := TopCat.of M)).symm
        ((TopCat.pathEquiv (X := TopCat.of M)).symm γ).hom₀)
  rw [h0, h1] at hb
  unfold ordinaryZeroEval
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hb.symm)).symm
/-- Point evaluations of zero-cocycles are locally constant on locally
path connected spaces. -/
def ordinaryZeroLocallyConstant [LocallyPathConnectedSpace M]
    (c : (P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).cycles (0 : ℤ)) :
    LocallyConstant M ℝ := by
  let f := ordinaryZeroEval
    ((P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).iCycles (0 : ℤ) c)
  let g := ZerothHomotopy.lift f (fun _ _ γ => ordinaryZeroEval_path c γ)
  refine ⟨f, ?_⟩
  exact (IsLocallyConstant.of_discrete g).comp_continuous
    ZerothHomotopy.isQuotientMap_mk.continuous
/-- Restriction evaluates on the same literal shared singular generator. -/
theorem evaluateSmoothCochain_restriction {q : ℕ}
    (c : (P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)).X (q : ℤ))
    (σ : SmoothSimplex S q) :
    evaluateSmoothCochain S ((SmoothSingularComparison.restriction S).f (q : ℤ) c) σ =
      P202Specs.CohomologyPairs.ordinaryCochainsEquiv ℝ ℝ (TopCat.of M) q c
        (Finsupp.single σ.val 1) := by
  change ((SingularChains.ordinaryComplex ℝ ℝ (TopCat.of M)).X (q : ℤ) →ₗ[ℝ] ℝ) at c
  change c ((SmoothSingularComparison.ordinaryInclusion S).f (q : ℤ)
      ((smoothDegreeIso S q).inv (smoothGenerator S σ))) =
    c ((SingularChains.ordinaryNonnegativeIso ℝ ℝ (TopCat.of M) q).inv
      (Finsupp.single σ.val 1))
  congr 1
  have hq : (SingularChains.degreeEmbedding 0).f q = (q : ℤ) := by
    change (0 : ℤ) + q = q
    omega
  rw [show (SmoothSingularComparison.ordinaryInclusion S).f (q : ℤ) =
    (smoothDegreeIso S q).hom ≫ (SmoothSingularComparison.inclusion S).f q ≫
      (SingularChains.ordinaryNonnegativeIso ℝ ℝ (TopCat.of M) q).inv from
    HomologicalComplex.extendMap_f _ _ hq]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rfl
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- A zero-simplex is exactly its point, on the actual geometric domains. -/
theorem smoothZeroSimplex_point (σ : SmoothSimplex S 0) (x₀ : SmoothSingularData.Simplex 0) :
    σ.val = (TopCat.toSSetObj₀Equiv (X := TopCat.of M)).symm ((p104Simplex S σ).val x₀) := by
  apply (TopCat.toSSetObj₀Equiv (X := TopCat.of M)).injective
  rw [Equiv.apply_symm_apply]
  change SingularChains.simplexEquiv (TopCat.of M) 0 σ.val default =
    SingularChains.simplexEquiv (TopCat.of M) 0 σ.val (SmoothSingularComparison.toBarycentric 0 x₀)
  congr 1
  exact Subsingleton.elim _ _

/-- Full degree-zero surjectivity, using actual restriction and the intrinsic
identification of closed zero-forms with locally constant scalar functions. -/
theorem smoothIntegrationCohomology_zero_surjective_of_restriction
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K)
    (hres : Function.Surjective (homologyMap (SmoothSingularComparison.restriction S) (0 : ℤ))) :
    Function.Surjective (smoothIntegrationCohomology S I 0) := by
  letI := TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  intro y
  obtain ⟨x, hx⟩ := hres y
  let A := P202Specs.CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M)
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ (0 : ℤ))).mp inferInstance x
  let lc := ordinaryZeroLocallyConstant c
  obtain ⟨e, he⟩ := DeRhamResults.h0_locally_constant K
  obtain ⟨ω, hω⟩ := (K.boundaries 0).mkQ_surjective (e.symm lc)
  change K.classOf 0 ω = e.symm lc at hω
  have heω : ∀ p, exteriorPower.zeroEquiv ℝ
      (Module.Dual ℝ (TangentData.TangentSpace S p)) (ω.val.val p) = lc p := by
    intro p
    rw [← he, hω, LinearEquiv.apply_symm_apply]
  refine ⟨K.classOf 0 ω, ?_⟩
  rw [smoothIntegrationCohomology_class]
  have hcycles : integrationToCycles S I 0 ω =
      cyclesMap (SmoothSingularComparison.restriction S) (0 : ℤ) c := by
    apply (ModuleCat.mono_iff_injective
      ((SmoothSingularComparison.smoothCochains S).iCycles (0 : ℤ))).mp inferInstance
    refine (integrationToCycles_i S I 0 ω).trans ?_
    have hi := congrArg (fun f => f.hom c)
      (cyclesMap_i (SmoothSingularComparison.restriction S) (0 : ℤ))
    change (SmoothSingularComparison.smoothCochains S).iCycles (0 : ℤ)
      (cyclesMap (SmoothSingularComparison.restriction S) (0 : ℤ) c) =
      (SmoothSingularComparison.restriction S).f (0 : ℤ) (A.iCycles (0 : ℤ) c) at hi
    rw [hi]
    apply smoothCochain_ext S
    intro σ
    let x₀ := SmoothSingularData.vertex (0 : Fin 1)
    rw [integrationInDegree_zero S I ω.val σ x₀, heω]
    refine Eq.trans ?_ (evaluateSmoothCochain_restriction S (A.iCycles (0 : ℤ) c) σ).symm
    change ordinaryZeroEval (A.iCycles (0 : ℤ) c) ((p104Simplex S σ).val x₀) = _
    unfold ordinaryZeroEval
    rw [smoothZeroSimplex_point S σ x₀]
  rw [hcycles]
  have hπ := congrArg (fun f => f.hom c)
    (homologyπ_naturality (SmoothSingularComparison.restriction S) (0 : ℤ))
  change homologyMap (SmoothSingularComparison.restriction S) (0 : ℤ)
      (A.homologyπ (0 : ℤ) c) =
    (SmoothSingularComparison.smoothCochains S).homologyπ (0 : ℤ)
      (cyclesMap (SmoothSingularComparison.restriction S) (0 : ℤ) c) at hπ
  exact hπ.symm.trans ((congrArg _ hc).trans hx)
end DegreeZeroSurjectivity


section FullLocalComparison

/-- Degree-zero integration is bijective on every manifold in the original
scope, with the full smooth-singular comparison as an explicit premise. -/
theorem smoothIntegrationCohomology_zero_bijective
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) :
    Function.Bijective (smoothIntegrationCohomology S I 0) := by
  letI := (hcomp.1 S (0 : ℤ)).2
  exact ⟨smoothIntegrationCohomology_zero_injective S I,
    smoothIntegrationCohomology_zero_surjective_of_restriction S I
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)⟩

/-- The full local comparison on a nonempty contractible manifold, including
the degree-zero normalization. Both smooth manifold models are allowed. -/
theorem smoothIntegrationCohomology_bijective_of_contractible
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    [Nonempty M] [ContractibleSpace M]
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ) :
    Function.Bijective (smoothIntegrationCohomology S I q) := by
  cases q with
  | zero => exact smoothIntegrationCohomology_zero_bijective S hcomp I
  | succ q =>
      exact smoothIntegrationCohomology_positive_bijective_of_contractible S hcomp I (q+1)
        (Nat.zero_lt_succ q)

/-- Integration, followed by the inverse of actual smooth restriction, gives
the specified equivalence on every nonempty contractible manifold. -/
theorem integrationComparison_of_contractible
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    [Nonempty M] [ContractibleSpace M]
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B) :
    ∃ e : ComparisonFamily S K, IsIntegrationComparison S K e := by
  obtain ⟨I⟩ := IntegrationCochain.integration_exists S C B K
  exact integrationComparisonOfBijective S I (fun q => (hcomp.1 S (q : ℤ)).2)
    (smoothIntegrationCohomology_bijective_of_contractible S hcomp I)

/-- The source's local convex-open comparison, allowing the empty open set
and any actual intrinsic calculus on its smooth structure. -/
theorem integrationComparison_convex_open
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Set V) (_hU : IsOpen U) (hconv : Convex ℝ U)
    (S : AtlasData.SmoothManifold n .euclidean U)
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B) :
    ∃ e : ComparisonFamily S K, IsIntegrationComparison S K e := by
  classical
  cases isEmpty_or_nonempty ↥U with
  | inl h =>
    letI := h
    exact integrationComparison_empty S hcomp K
  | inr h =>
    letI := h
    letI := hconv.contractibleSpace (Set.nonempty_coe_sort.mp h)
    exact integrationComparison_of_contractible S hcomp K

end FullLocalComparison

section PullbackTransfer

variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false

/-- The literal integration-class characterization depends only on the
intrinsic de Rham class of a closed representative. -/
theorem isIntegrationClass_congr_class
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) {q : ℕ}
    (α β : K.closed q) (hclass : K.classOf q α = K.classOf q β)
    (x : P202Specs.CohomologyPairs.ordinaryCohomology ℝ ℝ (TopCat.of M) (q : ℤ)) :
    IsIntegrationClass S C α.val.val x ↔ IsIntegrationClass S C β.val.val x := by
  rw [isIntegrationClass_iff S I α x, isIntegrationClass_iff S I β x, hclass]


/-- The integration pullback square, with the target integration comparison
already known. This statement needs no comparison-isomorphism theorem on S. -/
theorem smoothIntegrationCohomology_comp_pullback
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (I : IntegrationCochainData.IntegrationMap S K)
    (f : M → N) (hf : MapData.IsSmoothMap S T f)
    (L : (p : M) → TangentData.TangentSpace S p →ₗ[ℝ] TangentData.TangentSpace T (f p))
    (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
    (P : ∀ q, J.Cohomology q →ₗ[ℝ] K.Cohomology q)
    (hP : IsCohomologyPullback C B K J f L P)
    (h : ComparisonFamily T J) (hh : IsIntegrationComparison T J h) (q : ℕ) :
    (smoothIntegrationCohomology S I q).comp (P q) =
      (homologyMap (SmoothSingularComparison.restriction S) (q : ℤ)).hom.comp
        (((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map
          (SmoothSingularComparison.underlyingMap S T f hf).op).hom.comp
            (h q).toLinearMap) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro β
  obtain ⟨δ, hδ, hPδ⟩ := hP q β
  have hpull := integrationClass_pullback S T f hf C A (E q) β.val.val
    ((J.mem_forms q β.val.val).mp β.val.property) L hL _ (hh.2 q β)
  have hδclass : IsIntegrationClass S C δ.val.val
      ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map
        (SmoothSingularComparison.underlyingMap S T f hf).op (h q (J.classOf q β))) := by
    rw [hδ]
    exact hpull
  change smoothIntegrationCohomology S I q (P q (J.classOf q β)) = _
  rw [hPδ]
  exact ((isIntegrationClass_iff S I δ _).mp hδclass).symm

/-- Integration comparison transfers through a smooth map inducing
isomorphisms on both actual cohomology theories. -/
theorem integrationComparison_of_pullback_bijective
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (f : M → N) (hf : MapData.IsSmoothMap S T f)
    (L : (p : M) → TangentData.TangentSpace S p →ₗ[ℝ] TangentData.TangentSpace T (f p))
    (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
    (P : ∀ q, J.Cohomology q →ₗ[ℝ] K.Cohomology q)
    (hP : IsCohomologyPullback C B K J f L P)
    (hPbij : ∀ q, Function.Bijective (P q))
    (hQ : ∀ q : ℕ, IsIso
      ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map
        (SmoothSingularComparison.underlyingMap S T f hf).op))
    (h : ComparisonFamily T J) (hh : IsIntegrationComparison T J h) :
    ∃ e : ComparisonFamily S K, IsIntegrationComparison S K e := by
  obtain ⟨I⟩ := IntegrationCochain.integration_exists S C B K
  refine integrationComparisonOfBijective S I (fun q => (hcomp.1 S (q : ℤ)).2) ?_
  intro q
  have hbij : Function.Bijective ((smoothIntegrationCohomology S I q).comp (P q)) := by
    rw [smoothIntegrationCohomology_comp_pullback S T C A B E K J I f hf L hL P hP h hh q]
    letI := (hcomp.1 S (q : ℤ)).2
    letI := hQ q
    exact (asIso (homologyMap (SmoothSingularComparison.restriction S)
      (q : ℤ))).toLinearEquiv.bijective.comp
        ((asIso ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ (q : ℤ)).map
          (SmoothSingularComparison.underlyingMap S T f hf).op)).toLinearEquiv.bijective.comp
            (h q).bijective)
  exact (Function.Bijective.of_comp_iff _ (hPbij q)).mp hbij

open SmoothManifolds.MapData SmoothManifolds.TangentData SmoothManifolds.DifferentialData
open SmoothManifolds.InteriorHomotopyData

/-- The actual intrinsic pullback of a smooth homotopy equivalence is
bijective; no unrelated cohomology equivalence is substituted for it. -/
theorem deRhamPullback_bijective_of_homotopy_inverse
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (f : M → N) (g : N → M)
    (hf : MapData.IsSmoothMap S T f) (hg : MapData.IsSmoothMap T S g)
    (hgf : ∃ H : HomotopyTime × M → M, Continuous H ∧
      (∀ p, H (timeZero, p) = g (f p)) ∧ (∀ p, H (timeOne, p) = p))
    (hfg : ∃ H : HomotopyTime × N → N, Continuous H ∧
      (∀ p, H (timeZero, p) = f (g p)) ∧ (∀ p, H (timeOne, p) = p))
    (L : ∀ p, TangentData.TangentSpace S p →ₗ[ℝ] TangentData.TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (P : ∀ q, J.Cohomology q →ₗ[ℝ] K.Cohomology q)
    (hP : IsCohomologyPullback C B K J f L P) :
    ∀ q, Function.Bijective (P q) := by
  let R := differential T S g hg
  have hR : ∀ p, IsDifferential T S g p (R p) := differential_spec T S g hg
  have hcompM : MapData.IsSmoothMap S S (g ∘ f) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ T.smoothStructure.property.1.1 f g hf hg
  have hcompN : MapData.IsSmoothMap T T (f ∘ g) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1 g f hg hf
  let LM := differential S S (g ∘ f) hcompM
  let LN := differential T T (f ∘ g) hcompN
  have hLM : ∀ p, IsDifferential S S (g ∘ f) p (LM p) :=
    differential_spec S S (g ∘ f) hcompM
  have hLN : ∀ p, IsDifferential T T (f ∘ g) p (LN p) :=
    differential_spec T T (f ∘ g) hcompN
  obtain ⟨G, hG⟩ := DeRhamResults.pullback_exists T S A C E B J K g hg R hR
  obtain ⟨QM, hQM⟩ := DeRhamResults.pullback_exists S S C C B B K K (g ∘ f) hcompM LM hLM
  obtain ⟨QN, hQN⟩ := DeRhamResults.pullback_exists T T A A E E J J (f ∘ g) hcompN LN hLN
  have hIdK : IsCohomologyPullback C B K K id (fun p => LinearMap.id)
      (fun _ => LinearMap.id) := by
    intro q ω
    exact ⟨ω, (FormPullbackResults.pullback_id S _ (differential_id S) q ω.val.val).symm, rfl⟩
  have hIdJ : IsCohomologyPullback A E J J id (fun p => LinearMap.id)
      (fun _ => LinearMap.id) := by
    intro q ω
    exact ⟨ω, (FormPullbackResults.pullback_id T _ (differential_id T) q ω.val.val).symm, rfl⟩
  have hQMId := HomotopyResults.homotopy_invariance S S C B C B K K
    (g ∘ f) id hcompM (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1)
    hgf LM (fun p => LinearMap.id) hLM (differential_id S) QM
    (fun _ => LinearMap.id) hQM hIdK
  have hQNId := HomotopyResults.homotopy_invariance T T A E A E J J
    (f ∘ g) id hcompN (manifoldContDiff_id (⊤ : ℕ∞) _ T.smoothStructure.property.1)
    hfg LN (fun p => LinearMap.id) hLN (differential_id T) QN
    (fun _ => LinearMap.id) hQN hIdJ
  have hPG := DeRhamResults.pullback_comp S T S C A C B E B K J K f g hf hg
    L R LM hL hR hLM P G QM hP hG hQM
  have hGP := DeRhamResults.pullback_comp T S T A C A E B E J K J g f hg hf
    R L LN hR hL hLN G P QN hG hP hQN
  intro q
  have hleft : Function.LeftInverse (G q) (P q) := fun x =>
    (hGP q x).symm.trans (congrArg (fun Q => Q x) (hQNId q))
  have hright : Function.RightInverse (G q) (P q) := fun x =>
    (hPG q x).symm.trans (congrArg (fun Q => Q x) (hQMId q))
  exact ⟨hleft.injective, hright.surjective⟩

/-- The ordinary singular pullback of a continuous homotopy equivalence is
an isomorphism, using the actual full-dual singular cohomology functor. -/
theorem ordinaryCohomologyPullback_isIso_of_homotopy_inverse
    {X Y : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hgf : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (hfg : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (q : ℤ) :
    IsIso ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ q).map f.op) := by
  have hM := (P202.CohomologyPairs.homotopy_invariant ℝ ℝ).1 hgf q
  have hN := (P202.CohomologyPairs.homotopy_invariant ℝ ℝ).1 hfg q
  exact ⟨⟨(P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ q).map g.op,
    by simpa only [op_comp, Functor.map_comp] using
      hN.trans ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ q).map_id (op Y)),
    by simpa only [op_comp, Functor.map_comp] using
      hM.trans ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ q).map_id (op X))⟩⟩


/-- Integration comparison is invariant under an actual smooth homotopy
equivalence, using the constructed intrinsic and singular pullback maps. -/
theorem integrationComparison_of_smooth_homotopy_inverse
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (f : M → N) (g : N → M)
    (hf : MapData.IsSmoothMap S T f) (hg : MapData.IsSmoothMap T S g)
    (hgf : ∃ H : HomotopyTime × M → M, Continuous H ∧
      (∀ p, H (timeZero, p) = g (f p)) ∧ (∀ p, H (timeOne, p) = p))
    (hfg : ∃ H : HomotopyTime × N → N, Continuous H ∧
      (∀ p, H (timeZero, p) = f (g p)) ∧ (∀ p, H (timeOne, p) = p))
    (h : ComparisonFamily T J) (hh : IsIntegrationComparison T J h) :
    ∃ e : ComparisonFamily S K, IsIntegrationComparison S K e := by
  let L := differential S T f hf
  have hL : ∀ p, IsDifferential S T f p (L p) := differential_spec S T f hf
  obtain ⟨P, hP⟩ := DeRhamResults.pullback_exists S T C A B E K J f hf L hL
  have hbij := deRhamPullback_bijective_of_homotopy_inverse S T C A B E K J f g
    hf hg hgf hfg L hL P hP
  refine integrationComparison_of_pullback_bijective S T hcomp C A B E K J
    f hf L hL P hP hbij ?_ h hh
  let F := SmoothSingularComparison.underlyingMap S T f hf
  let G := SmoothSingularComparison.underlyingMap T S g hg
  obtain ⟨HM, hHM, hHM0, hHM1⟩ := hgf
  obtain ⟨HN, hHN, hHN0, hHN1⟩ := hfg
  have hM : TopCat.Homotopy (F ≫ G) (𝟙 (TopCat.of M)) := {
    toFun := HM
    continuous_toFun := hHM
    map_zero_left := hHM0
    map_one_left := hHM1 }
  have hN : TopCat.Homotopy (G ≫ F) (𝟙 (TopCat.of N)) := {
    toFun := HN
    continuous_toFun := hHN
    map_zero_left := hHN0
    map_one_left := hHN1 }
  intro q
  exact ordinaryCohomologyPullback_isIso_of_homotopy_inverse F G hM hN (q : ℤ)

/-- The boundary comparison reduces to the comparison on the actual interior,
with its P104 boundaryless Euclidean smooth structure. All collar maps,
homotopies, differential maps and their cohomological inverses are proved or
constructed upstream; the remaining premise is only interior integration
comparison, never an assumed comparison on the original manifold. -/
theorem integrationComparison_of_interior
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (hInterior : ∀ (T : AtlasData.SmoothManifold n .euclidean
        (BoundaryData.manifoldInterior S)) (A : CotangentBundle T)
        (E : ∀ k, FormBundle A k) (J : Calculus A E),
      ∃ h : ComparisonFamily T J, IsIntegrationComparison T J h) :
    ∃ e : ComparisonFamily S K, IsIntegrationComparison S K e := by
  obtain ⟨R⟩ := InteriorHomotopies.interior_inclusion_homotopy_equivalence S
  obtain ⟨T, hAT, hTS⟩ :=
    SmoothingHomotopies.interior_euclidean_structure S R.isOpen_interior
  obtain ⟨A⟩ := BundleOperations.exists_cotangent T
  let E : ∀ k, FormBundle A k := fun k =>
    Classical.choice (ExteriorAlgebraResults.exists_formBundle A k)
  obtain ⟨J⟩ := DeRhamResults.complex_exists A E
  obtain ⟨h, hh⟩ := hInterior T A E J
  have hA := openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _
    S.smoothStructure.property.1 (BoundaryData.manifoldInterior S) R.isOpen_interior
  have hf : MapData.IsSmoothMap S T R.inverse :=
    manifoldContDiff_comp (⊤ : ℕ∞) S.smoothStructure.val _ T.smoothStructure.val
      hA.1 R.inverse id R.smooth_inverse hAT
  let F := SmoothSingularComparison.underlyingMap S T R.inverse hf
  let G := SmoothSingularComparison.underlyingMap T S Subtype.val hTS
  let HM : TopCat.Homotopy (𝟙 (TopCat.of M)) (F ≫ G) := {
    toFun := R.homotopy
    continuous_toFun := R.smooth_homotopy.1
    map_zero_left := R.homotopy_zero
    map_one_left := R.homotopy_one }
  let HN : TopCat.Homotopy (𝟙 (TopCat.of (BoundaryData.manifoldInterior S))) (G ≫ F) := {
    toFun := fun z => ⟨R.homotopy (z.1, z.2.val), R.preserves_interior z.1 z.2⟩
    continuous_toFun := R.smooth_restricted_homotopy.1
    map_zero_left := fun p => Subtype.ext (R.homotopy_zero p.val)
    map_one_left := fun p => Subtype.ext (R.homotopy_one p.val) }
  exact integrationComparison_of_smooth_homotopy_inverse S T hcomp C A B E K J
    R.inverse Subtype.val hf hTS
    ⟨HM.symm, HM.symm.continuous, HM.symm.map_zero_left, HM.symm.map_one_left⟩
    ⟨HN.symm, HN.symm.continuous, HN.symm.map_zero_left, HN.symm.map_one_left⟩ h hh


end PullbackTransfer

namespace CoverForms

open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  SmoothManifolds.CovectorData SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
  SmoothManifolds.MayerVietorisData SmoothManifolds.MayerVietorisData.OpenForms
open Set Filter
open scoped _root_.Topology
universe w

/-- Local finiteness of dependent sections reduces their pointwise algebraic
sum to a fixed finite sum on a neighborhood. -/
theorem dependent_locallyFinite_eventuallyEq_finsum
    {X : Type u} [TopologicalSpace X] {V : X → Type v}
    [∀ x, AddCommMonoid (V x)] {ι : Type w} {f : ι → (x : X) → V x}
    (hf : LocallyFinite (fun i => ModelData.sectionSupport (f i))) (x : X) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 x, (∑ᶠ i, f i y) = ∑ i ∈ s, f i y := by
  classical
  obtain ⟨V, hV, hfin⟩ := hf x
  refine ⟨hfin.toFinset, Filter.mem_of_superset hV (fun y hy => ?_)⟩
  apply finsum_eq_sum_of_support_subset
  intro i hi
  exact hfin.mem_toFinset.mpr ⟨y, subset_closure hi, hy⟩

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : AtlasData.SmoothManifold n a M} {C : CotangentBundle S}
  {B : ∀ k, FormBundle C k}

theorem restrictedForm_finset_sum {ι : Type v} {q : ℕ}
    (U : TopologicalSpace.Opens M) (s : Finset ι)
    (ω : ι → RestrictedField S U q)
    (hω : ∀ i, IsRestrictedForm (B q) U (ω i)) :
    IsRestrictedForm (B q) U (fun p => ∑ i ∈ s, ω i p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert restricted_zero (B q) U using 1
    funext p
    simp only [Finset.sum_empty, Pi.zero_apply]
  | @insert i s hi ih =>
    convert restricted_add (B q) U (ω i)
      (fun p => ∑ j ∈ s, ω j p) (hω i) ih using 1
    funext p
    simp only [Finset.sum_insert hi, Pi.add_apply]

/-- Locally finite sums of actual smooth restricted intrinsic forms are
smooth, on arbitrary opens including boundary and empty opens. -/
theorem restrictedForm_finsum {ι : Type v} {q : ℕ}
    (U : TopologicalSpace.Opens M) (ω : ι → RestrictedField S U q)
    (hω : ∀ i, IsRestrictedForm (B q) U (ω i))
    (hlf : LocallyFinite (fun i => ModelData.sectionSupport (ω i))) :
    IsRestrictedForm (B q) U (fun p => ∑ᶠ i, ω i p) := by
  letI := (cotangentSpace C).topology
  letI := (B q).space.topology
  intro p
  obtain ⟨s, hs⟩ := dependent_locallyFinite_eventuallyEq_finsum hlf p
  apply manifoldContDiffAt_congr (restrictedForm_finset_sum U s ω hω p)
  filter_upwards [hs] with y hy
  exact congrArg (fun z => (⟨y.val, z⟩ : Bundle.TotalSpace
    (ModelData.Euclidean (n.choose q)) (fun p => Fiber (TangentData.TangentSpace S p) q)))
      hy.symm

/-- Zero extension of a scalar-weighted restricted intrinsic form. -/
def weightedRestrictedExtension {ι : Type v} {q : ℕ}
    (W : TopologicalSpace.Opens M) (V : ι → TopologicalSpace.Opens M)
    (ρ : ι → M → ℝ) (ω : (i : ι) → RestrictedField S (V i) q)
    (i : ι) : RestrictedField S W q :=
  fun p => zeroExtend (fun y : V i => ρ i y.val • ω i y) p.val

theorem weightedRestrictedExtension_support_subset {ι : Type v} {q : ℕ}
    (W : TopologicalSpace.Opens M) (V : ι → TopologicalSpace.Opens M)
    (ρ : ι → M → ℝ) (ω : (i : ι) → RestrictedField S (V i) q) (i : ι) :
    ModelData.sectionSupport (weightedRestrictedExtension W V ρ ω i) ⊆
      Subtype.val ⁻¹' ModelData.sectionSupport (ρ i) := by
  apply closure_minimal
  · intro p hp
    apply subset_closure
    intro hz
    apply hp
    change zeroExtend (fun y : V i => ρ i y.val • ω i y) p.val = 0
    unfold zeroExtend
    split_ifs with h
    · simp only [hz, zero_smul]
    · rfl
  · exact isClosed_closure.preimage continuous_subtype_val

/-- A genuine full smooth partition gives locally finite smooth sums of
weighted zero extensions. This is the analytic operation needed by insertion
in every positive Čech degree. -/
theorem restrictedForm_partition_sum {ι : Type v} {q : ℕ}
    (W : TopologicalSpace.Opens M) (U : ι → TopologicalSpace.Opens M)
    (ρ : ι → M → ℝ) (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate (fun i => (U i : Set M)) ρ)
    (ω : (i : ι) → RestrictedField S (U i ⊓ W) q)
    (hω : ∀ i, IsRestrictedForm (B q) (U i ⊓ W) (ω i)) :
    IsRestrictedForm (B q) W
      (fun p => ∑ᶠ i, zeroExtend (fun y : ↥(U i ⊓ W) => ρ i y.val • ω i y) p.val) := by
  apply restrictedForm_finsum W
    (weightedRestrictedExtension W (fun i => U i ⊓ W) ρ ω)
  · intro i
    apply weighted_extension (B q) (U i ⊓ W) W (ρ i) (hρ.1 i) (ω i) (hω i)
    intro p hp
    exact ⟨hsub i hp.1, hp.2⟩
  · exact (hρ.2.2.1.preimage_continuous continuous_subtype_val).subset
      (weightedRestrictedExtension_support_subset W (fun i => U i ⊓ W) ρ ω)

end CoverForms


section VectorSimplexAlgebra

universe r w
variable (R : Type r) [CommRing R] (I : Type v) (V : Type w)
  [AddCommGroup V] [Module R V]
abbrev VectorSimplexRow (k : ℕ) := (Fin k → I) → V

def vectorSimplexD (k : ℕ) : VectorSimplexRow I V k →ₗ[R] VectorSimplexRow I V (k+1) where
  toFun f t := ∑ j : Fin (k+1), (-1 : R)^j.val • f (t ∘ j.succAbove)
  map_add' f g := by
    funext t
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext t
    simp only [Pi.smul_apply, RingHom.id_apply, smul_smul, Finset.smul_sum]
    congr 1
    funext j
    rw [mul_comm]

def vectorSimplexH (i : I) (k : ℕ) :
    VectorSimplexRow I V (k+1) →ₗ[R] VectorSimplexRow I V k where
  toFun f t := f (Fin.cons i t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem vectorSimplexD_zero_apply (f : VectorSimplexRow I V 0) (t : Fin 1 → I) :
    vectorSimplexD R I V 0 f t = f Fin.elim0 := by
  change (∑ j : Fin 1, (-1 : R)^j.val • f (t ∘ j.succAbove)) = _
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul]
  congr 1
  exact Subsingleton.elim _ _

theorem vectorSimplexD_cons (i : I) (k : ℕ) (f : VectorSimplexRow I V (k+1))
    (t : Fin (k+1) → I) :
    vectorSimplexD R I V (k+1) f (Fin.cons i t) =
      f t - vectorSimplexD R I V k (vectorSimplexH R I V i k f) t := by
  change (∑ j : Fin (k+2), (-1 : R)^j.val • f (Fin.cons i t ∘ j.succAbove)) =
    f t - ∑ j : Fin (k+1), (-1 : R)^j.val • f (Fin.cons i (t ∘ j.succAbove))
  rw [Fin.sum_univ_succ]
  have hhead : (Fin.cons i t ∘ (0 : Fin (k+2)).succAbove) = t := by
    funext j
    simp
  rw [hhead]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, Fin.cons_comp_succ_succAbove]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

theorem vectorSimplex_contract (i : I) (k : ℕ) (f : VectorSimplexRow I V (k+1)) :
    vectorSimplexD R I V k (vectorSimplexH R I V i k f) +
      vectorSimplexH R I V i (k+1) (vectorSimplexD R I V (k+1) f) = f := by
  funext t
  change vectorSimplexD R I V k (vectorSimplexH R I V i k f) t +
    vectorSimplexD R I V (k+1) f (Fin.cons i t) = f t
  rw [vectorSimplexD_cons]
  abel

theorem vectorSimplex_contract_zero (i : I) (f : VectorSimplexRow I V 0) :
    vectorSimplexH R I V i 0 (vectorSimplexD R I V 0 f) = f := by
  funext t
  change vectorSimplexD R I V 0 f (Fin.cons i t) = f t
  rw [vectorSimplexD_zero_apply]
  congr 1
  exact Subsingleton.elim _ _
theorem vectorSimplex_weighted_contract (s : Finset I) (w : I → R) (k : ℕ)
    (f : VectorSimplexRow I V (k+1)) :
    vectorSimplexD R I V k (∑ i ∈ s, w i • vectorSimplexH R I V i k f) +
      (∑ i ∈ s, w i • vectorSimplexH R I V i (k+1)
        (vectorSimplexD R I V (k+1) f)) = (∑ i ∈ s, w i) • f := by
  rw [map_sum]
  simp only [map_smul]
  rw [← Finset.sum_add_distrib]
  simp_rw [← smul_add, vectorSimplex_contract]
  exact Finset.sum_smul.symm

theorem vectorSimplex_weighted_contract_zero (s : Finset I) (w : I → R)
    (f : VectorSimplexRow I V 0) :
    (∑ i ∈ s, w i • vectorSimplexH R I V i 0 (vectorSimplexD R I V 0 f)) =
      (∑ i ∈ s, w i) • f := by
  simp_rw [vectorSimplex_contract_zero]
  exact Finset.sum_smul.symm

theorem vectorSimplex_finsum_contract (w : I → R) (hw : Function.HasFiniteSupport w)
    (k : ℕ) (f : VectorSimplexRow I V (k+1)) :
    vectorSimplexD R I V k (∑ᶠ i, w i • vectorSimplexH R I V i k f) +
      (∑ᶠ i, w i • vectorSimplexH R I V i (k+1)
        (vectorSimplexD R I V (k+1) f)) = (∑ᶠ i, w i) • f := by
  have h₁ : Function.HasFiniteSupport (fun i => w i • vectorSimplexH R I V i k f) :=
    hw.smul_left (fun i => vectorSimplexH R I V i k f)
  have h₂ : Function.HasFiniteSupport (fun i => w i • vectorSimplexH R I V i (k+1)
      (vectorSimplexD R I V (k+1) f)) :=
    hw.smul_left (fun i => vectorSimplexH R I V i (k+1) (vectorSimplexD R I V (k+1) f))
  rw [map_finsum (vectorSimplexD R I V k) h₁]
  simp_rw [map_smul]
  have h₃ : Function.HasFiniteSupport (fun i => w i •
      vectorSimplexD R I V k (vectorSimplexH R I V i k f)) :=
    hw.smul_left (fun i => vectorSimplexD R I V k (vectorSimplexH R I V i k f))
  rw [← finsum_add_distrib h₃ h₂]
  simp_rw [← smul_add, vectorSimplex_contract]
  exact (finsum_smul' hw f).symm

theorem vectorSimplex_finsum_contract_zero (w : I → R) (hw : Function.HasFiniteSupport w)
    (f : VectorSimplexRow I V 0) :
    (∑ᶠ i, w i • vectorSimplexH R I V i 0 (vectorSimplexD R I V 0 f)) =
      (∑ᶠ i, w i) • f := by
  simp_rw [vectorSimplex_contract_zero]
  exact (finsum_smul' hw f).symm
theorem vectorSimplexD_squared (k : ℕ) (f : VectorSimplexRow I V k) :
    vectorSimplexD R I V (k+1) (vectorSimplexD R I V k f) = 0 := by
  induction k with
  | zero =>
    funext t
    rw [← Fin.cons_self_tail t, vectorSimplexD_cons]
    rw [vectorSimplex_contract_zero, sub_self]
    rfl
  | succ k ih =>
    funext t
    have hc := congrArg (vectorSimplexD R I V (k+1))
      (vectorSimplex_contract R I V (t 0) k f)
    rw [map_add, ih, zero_add] at hc
    rw [← Fin.cons_self_tail t, vectorSimplexD_cons]
    exact sub_eq_zero.mpr (congrFun hc (Fin.tail t)).symm

theorem vectorSimplex_exact (i : I) (k : ℕ) (f : VectorSimplexRow I V (k+1)) :
    vectorSimplexD R I V (k+1) f = 0 ↔
      ∃ g, vectorSimplexD R I V k g = f := by
  constructor
  · intro hf
    refine ⟨vectorSimplexH R I V i k f, ?_⟩
    have hc := vectorSimplex_contract R I V i k f
    simpa only [hf, map_zero, add_zero] using hc
  · rintro ⟨g, rfl⟩
    exact vectorSimplexD_squared R I V k g

theorem vectorSimplex_augmentation_injective (i : I) :
    Function.Injective (vectorSimplexD R I V 0) := by
  intro f g he
  have h := congrArg (vectorSimplexH R I V i 0) he
  simpa only [vectorSimplex_contract_zero] using h

theorem finsum_subtype_of_support_subset {A : Type v} {W : Type w} [AddCommMonoid W]
    (f : A → W) (s : Set A) (hs : Function.support f ⊆ s) :
    (∑ᶠ i : s, f i.val) = ∑ᶠ i, f i := by
  rw [finsum_set_coe_eq_finsum_mem]
  calc (∑ᶠ i ∈ s, f i) = ∑ᶠ i ∈ Set.univ, f i := by
         apply finsum_mem_inter_support_eq
         ext i
         constructor
         · exact fun h => ⟨Set.mem_univ _, h.2⟩
         · exact fun h => ⟨hs h.2, h.2⟩
       _ = _ := finsum_mem_univ f
end VectorSimplexAlgebra

namespace DirectSumTotal
variable {R : Type*} [Ring R] {W : ℕ → Type*}
  [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]

def horizontal (h : ∀ i, W i →ₗ[R] W (i+1)) :
    (Π₀ i, W i) →ₗ[R] (Π₀ i, W i) :=
  DFinsupp.lsum ℕ (fun i => (DFinsupp.lsingle (i+1)).comp (h i))

def vertical (v : ∀ i, W i →ₗ[R] W i) :
    (Π₀ i, W i) →ₗ[R] (Π₀ i, W i) := DFinsupp.mapRange.linearMap v

def differential (h : ∀ i, W i →ₗ[R] W (i+1)) (v : ∀ i, W i →ₗ[R] W i) :
    (Π₀ i, W i) →ₗ[R] (Π₀ i, W i) := horizontal h + vertical v

@[simp] theorem horizontal_zero (h : ∀ i, W i →ₗ[R] W (i+1)) (y : Π₀ i, W i) :
    horizontal h y 0 = 0 := by
  have he : (DFinsupp.lapply 0).comp (horizontal h) = 0 := by
    apply DFinsupp.lhom_ext
    intro i x
    simp [horizontal]
  exact LinearMap.congr_fun he y

@[simp] theorem horizontal_succ (h : ∀ i, W i →ₗ[R] W (i+1))
    (y : Π₀ i, W i) (p : ℕ) : horizontal h y (p+1) = h p (y p) := by
  have he : (DFinsupp.lapply (p+1)).comp (horizontal h) =
      (h p).comp (DFinsupp.lapply p) := by
    apply DFinsupp.lhom_ext
    intro i x
    by_cases hi : i = p
    · subst i
      simp [horizontal]
    · have hi' : i+1 ≠ p+1 := by omega
      simp [horizontal, hi]
  exact LinearMap.congr_fun he y

@[simp] theorem differential_zero (h : ∀ i, W i →ₗ[R] W (i+1))
    (v : ∀ i, W i →ₗ[R] W i) (y : Π₀ i, W i) :
    differential h v y 0 = v 0 (y 0) := by
  simp [differential, vertical]

@[simp] theorem differential_succ (h : ∀ i, W i →ₗ[R] W (i+1))
    (v : ∀ i, W i →ₗ[R] W i) (y : Π₀ i, W i) (p : ℕ) :
    differential h v y (p+1) = h p (y p) + v (p+1) (y (p+1)) := by
  simp [differential, vertical]

theorem differential_single (h : ∀ i, W i →ₗ[R] W (i+1))
    (v : ∀ i, W i →ₗ[R] W i) (p : ℕ) (a : W p) :
    differential h v (DFinsupp.single p a) =
      DFinsupp.single (p+1) (h p a) + DFinsupp.single p (v p a) := by
  simp [differential, horizontal, vertical]

theorem differential_square (h : ∀ i, W i →ₗ[R] W (i+1))
    (v : ∀ i, W i →ₗ[R] W i)
    (hh : ∀ i, (h (i+1)).comp (h i) = 0)
    (hv : ∀ i, (v i).comp (v i) = 0)
    (ha : ∀ i, (h i).comp (v i) + (v (i+1)).comp (h i) = 0) :
    (differential h v).comp (differential h v) = 0 := by
  apply DFinsupp.lhom_ext
  intro i x
  simp only [LinearMap.comp_apply, differential_single, map_add, LinearMap.zero_apply]
  have hhh : h (i+1) (h i x) = 0 := LinearMap.congr_fun (hh i) x
  have hvv : v i (v i x) = 0 := LinearMap.congr_fun (hv i) x
  have haa : h i (v i x) + v (i+1) (h i x) = 0 := LinearMap.congr_fun (ha i) x
  rw [hhh, hvv]
  simp only [DFinsupp.single_zero, zero_add, add_zero]
  rw [← DFinsupp.single_add]
  simp [add_comm, haa]

def supportBelow (k : ℕ) : Submodule R (Π₀ i, W i) where
  carrier := {y | ∀ i, k ≤ i → y i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro r x hx i hi; simp [hx i hi]

theorem supportBelow_zero : supportBelow (R := R) (W := W) 0 = ⊥ := by
  ext y
  constructor
  · intro hy
    change y = 0
    ext i
    exact hy i (Nat.zero_le i)
  · intro hy
    have hy0 : y = 0 := hy
    subst y
    exact (supportBelow 0).zero_mem

theorem supportBelow_exhaustive (y : Π₀ i, W i) :
    ∃ k, y ∈ supportBelow (R := R) k := by
  classical
  refine ⟨y.support.sup id + 1, ?_⟩
  intro i hi
  by_contra hy
  have himem : i ∈ y.support := DFinsupp.mem_support_iff.mpr hy
  have hisup : i ≤ y.support.sup id := Finset.le_sup (f := id) himem
  omega

/-- Exact horizontal rows, including injectivity at horizontal degree zero,
make a signed differential on the direct sum acyclic. Every element has
finite horizontal support; no bound on the size of any row is imposed. -/
theorem exact_of_horizontal_exact
    (h : ∀ i, W i →ₗ[R] W (i+1)) (v : ∀ i, W i →ₗ[R] W i)
    (hh : ∀ i, (h (i+1)).comp (h i) = 0)
    (hv : ∀ i, (v i).comp (v i) = 0)
    (ha : ∀ i, (h i).comp (v i) + (v (i+1)).comp (h i) = 0)
    (hinj : Function.Injective (h 0)) (hexact : ∀ i, Function.Exact (h i) (h (i+1))) :
    Function.Exact (differential h v) (differential h v) := by
  classical
  apply exact_of_exhaustive_filtration (differential h v) (differential h v)
    (differential_square h v hh hv ha) (supportBelow (R := R)) supportBelow_zero
    supportBelow_exhaustive
  intro k y hy hdy
  have hcomponent (i : ℕ) : differential h v y i = 0 := congrArg (fun z => z i) hdy
  cases k with
  | zero =>
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero]
    intro i _
    cases i with
    | zero =>
      have hz : h 0 (y 0) = 0 := by
        simpa [hy 1 (by omega)] using hcomponent 1
      exact hinj (hz.trans (map_zero _).symm)
    | succ i => exact hy (i+1) (by omega)
  | succ k =>
    have htop : h (k+1) (y (k+1)) = 0 := by
      simpa [hy (k+2) (by omega)] using hcomponent (k+2)
    obtain ⟨a, ha⟩ := (hexact k (y (k+1))).mp htop
    refine ⟨DFinsupp.single k a, ?_⟩
    intro i hi
    rw [DFinsupp.sub_apply, differential_single, DFinsupp.add_apply]
    have hik : i ≠ k := by omega
    by_cases his : i = k+1
    · subst i
      simp [ha]
    · have hiy : y i = 0 := hy i (by omega)
      simp [hiy, Ne.symm his, Ne.symm hik]

end DirectSumTotal


namespace BigradedTotal
variable {R : Type*} [Ring R] {V : ℕ → ℕ → Type*}
  [∀ p q, AddCommGroup (V p q)] [∀ p q, Module R (V p q)]

abbrev Ambient := Π₀ p, Π₀ q, V p q

def horizontalColumn (h : ∀ p q, V p q →ₗ[R] V (p+1) q) (p : ℕ) :
    (Π₀ q, V p q) →ₗ[R] (Π₀ q, V (p+1) q) :=
  DFinsupp.mapRange.linearMap (h p)

def verticalColumn (v : ∀ p q, V p q →ₗ[R] V p (q+1)) (p : ℕ) :
    (Π₀ q, V p q) →ₗ[R] (Π₀ q, V p q) := DirectSumTotal.horizontal (v p)

def differential (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1)) :
    Ambient (V := V) →ₗ[R] Ambient (V := V) :=
  DirectSumTotal.differential (horizontalColumn h) (verticalColumn v)

@[simp] theorem horizontalColumn_apply (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (p q : ℕ) (x : Π₀ q, V p q) : horizontalColumn h p x q = h p q (x q) := rfl

@[simp] theorem verticalColumn_zero (v : ∀ p q, V p q →ₗ[R] V p (q+1))
    (p : ℕ) (x : Π₀ q, V p q) : verticalColumn v p x 0 = 0 :=
  DirectSumTotal.horizontal_zero _ _

@[simp] theorem verticalColumn_succ (v : ∀ p q, V p q →ₗ[R] V p (q+1))
    (p q : ℕ) (x : Π₀ q, V p q) : verticalColumn v p x (q+1) = v p q (x q) :=
  DirectSumTotal.horizontal_succ _ _ _

@[simp] theorem differential_zero_zero (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1)) (x : Ambient (V := V)) :
    differential h v x 0 0 = 0 := by
  simp [differential]

@[simp] theorem differential_succ_zero (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1)) (x : Ambient (V := V)) (p : ℕ) :
    differential h v x (p+1) 0 = h p 0 (x p 0) := by
  simp [differential]

@[simp] theorem differential_zero_succ (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1)) (x : Ambient (V := V)) (q : ℕ) :
    differential h v x 0 (q+1) = v 0 q (x 0 q) := by
  simp [differential]

@[simp] theorem differential_succ_succ (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1)) (x : Ambient (V := V)) (p q : ℕ) :
    differential h v x (p+1) (q+1) =
      h p (q+1) (x p (q+1)) + v (p+1) q (x (p+1) q) := by
  simp [differential]

def diagonalPart (n : ℕ) : Ambient (V := V) →ₗ[R] Ambient (V := V) :=
  DFinsupp.mapRange.linearMap (fun p =>
    DFinsupp.filterLinearMap R (fun q => V p q) (fun q => p+q=n))

@[simp] theorem diagonalPart_apply (n p q : ℕ) (x : Ambient (V := V)) :
    diagonalPart (R := R) n x p q = if p+q=n then x p q else 0 := by
  simp [diagonalPart, DFinsupp.filter_apply]

def homogeneous (n : ℕ) : Submodule R (Ambient (V := V)) where
  carrier := {x | ∀ p q, p+q ≠ n → x p q = 0}
  zero_mem' := by intro p q _; rfl
  add_mem' := by intro x y hx hy p q hpq; simp [hx p q hpq, hy p q hpq]
  smul_mem' := by intro r x hx p q hpq; simp [hx p q hpq]

theorem diagonalPart_mem (n : ℕ) (x : Ambient (V := V)) :
    diagonalPart (R := R) n x ∈ homogeneous (R := R) n := by
  intro p q hpq
  simp [hpq]

theorem diagonalPart_eq_self {n : ℕ} (x : Ambient (V := V))
    (hx : x ∈ homogeneous (R := R) n) : diagonalPart (R := R) n x = x := by
  ext p q
  by_cases hpq : p+q=n
  · simp [hpq]
  · simp [hpq, hx p q hpq]

/-- The signed total differential raises total degree by exactly one. -/
theorem diagonalPart_differential (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1)) (n : ℕ) (x : Ambient (V := V)) :
    diagonalPart (R := R) (n+1) (differential h v x) =
      differential h v (diagonalPart (R := R) n x) := by
  ext p q
  cases p with
  | zero =>
    cases q with
    | zero => simp
    | succ q =>
      by_cases hq : q=n
      · simp [hq]
      · simp [hq]
  | succ p =>
    cases q with
    | zero =>
      by_cases hp : p=n
      · simp [hp]
      · simp [hp]
    | succ q =>
      have h₁ : (p+1+(q+1)=n+1) ↔ (p+(q+1)=n) := by omega
      have h₂ : (p+1+q=n) ↔ (p+(q+1)=n) := by omega
      by_cases hpq : p+(q+1)=n
      · simp [h₁.mpr hpq, h₂.mpr hpq, hpq]
      · simp [not_congr h₁ |>.mpr hpq, not_congr h₂ |>.mpr hpq, hpq]

theorem differential_mem_homogeneous
    (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1)) {n : ℕ}
    (x : Ambient (V := V)) (hx : x ∈ homogeneous (R := R) n) :
    differential h v x ∈ homogeneous (R := R) (n+1) := by
  have heq := diagonalPart_differential h v n x
  rw [diagonalPart_eq_self x hx] at heq
  rw [← heq]
  exact diagonalPart_mem _ _

def homogeneousDifferential (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1)) (n : ℕ) :
    homogeneous (R := R) (V := V) n →ₗ[R] homogeneous (R := R) (V := V) (n+1) :=
  ((differential h v).comp (homogeneous (R := R) (V := V) n).subtype).codRestrict (homogeneous (R := R) (V := V) (n+1))
    (fun x => differential_mem_homogeneous h v x.val x.property)


theorem horizontalColumn_square
    (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (hh : ∀ p q, (h (p+1) q).comp (h p q) = 0) (p : ℕ) :
    (horizontalColumn h (p+1)).comp (horizontalColumn h p) = 0 := by
  apply LinearMap.ext
  intro x
  ext q
  exact LinearMap.congr_fun (hh p q) (x q)

theorem verticalColumn_square
    (v : ∀ p q, V p q →ₗ[R] V p (q+1))
    (hv : ∀ p q, (v p (q+1)).comp (v p q) = 0) (p : ℕ) :
    (verticalColumn v p).comp (verticalColumn v p) = 0 := by
  apply LinearMap.ext
  intro x
  ext q
  change verticalColumn v p (verticalColumn v p x) q = 0
  cases q with
  | zero => simp
  | succ q =>
    cases q with
    | zero => simp
    | succ q =>
      simpa only [verticalColumn_succ, LinearMap.comp_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun (hv p q) (x q)

theorem column_anticommute
    (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1))
    (ha : ∀ p q, (h p (q+1)).comp (v p q) + (v (p+1) q).comp (h p q) = 0)
    (p : ℕ) :
    (horizontalColumn h p).comp (verticalColumn v p) +
      (verticalColumn v (p+1)).comp (horizontalColumn h p) = 0 := by
  apply LinearMap.ext
  intro x
  ext q
  change horizontalColumn h p (verticalColumn v p x) q +
    verticalColumn v (p+1) (horizontalColumn h p x) q = 0
  cases q with
  | zero => simp
  | succ q =>
    simpa only [horizontalColumn_apply, verticalColumn_succ, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun (ha p q) (x q)

theorem horizontalColumn_zero_injective
    (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (hinj : ∀ q, Function.Injective (h 0 q)) : Function.Injective (horizontalColumn h 0) := by
  intro x y hxy
  ext q
  apply hinj q
  exact congrArg (fun z => z q) hxy

theorem horizontalColumn_exact
    (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (hexact : ∀ p q, Function.Exact (h p q) (h (p+1) q)) (p : ℕ) :
    Function.Exact (horizontalColumn h p) (horizontalColumn h (p+1)) := by
  apply LinearMap.exact_iff.mpr
  change LinearMap.ker (DFinsupp.mapRange.linearMap (h (p+1))) =
    LinearMap.range (DFinsupp.mapRange.linearMap (h p))
  rw [DFinsupp.ker_mapRangeLinearMap, DFinsupp.range_mapRangeLinearMap]
  have heq : (fun q => LinearMap.ker (h (p+1) q)) =
      (fun q => LinearMap.range (h p q)) :=
    funext (fun q => LinearMap.exact_iff.mp (hexact p q))
  rw [heq]

/-- An exact augmented first-quadrant horizontal bicomplex has an exact
homogeneous total complex in every positive degree. Both maps raise total
degree by one, and the primitive is projected to precisely the preceding
total degree. The vertical maps here already include the usual signs. -/
theorem homogeneousTotal_exact_of_horizontal_exact
    (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1))
    (hh : ∀ p q, (h (p+1) q).comp (h p q) = 0)
    (hv : ∀ p q, (v p (q+1)).comp (v p q) = 0)
    (ha : ∀ p q, (h p (q+1)).comp (v p q) + (v (p+1) q).comp (h p q) = 0)
    (hinj : ∀ q, Function.Injective (h 0 q))
    (hexact : ∀ p q, Function.Exact (h p q) (h (p+1) q)) (n : ℕ) :
    Function.Exact (homogeneousDifferential h v n) (homogeneousDifferential h v (n+1)) := by
  have he := DirectSumTotal.exact_of_horizontal_exact (horizontalColumn h) (verticalColumn v)
    (horizontalColumn_square h hh) (verticalColumn_square v hv) (column_anticommute h v ha)
    (horizontalColumn_zero_injective h hinj) (horizontalColumn_exact h hexact)
  intro y
  constructor
  · intro hy
    have hdy : differential h v y.val = 0 := congrArg Subtype.val hy
    obtain ⟨z, hz⟩ := (he y.val).mp hdy
    change differential h v z = y.val at hz
    refine ⟨⟨diagonalPart (R := R) n z, diagonalPart_mem n z⟩, ?_⟩
    apply Subtype.ext
    change differential h v (diagonalPart (R := R) n z) = y.val
    rw [← diagonalPart_differential, hz, diagonalPart_eq_self y.val y.property]
  · rintro ⟨z, rfl⟩
    apply Subtype.ext
    change differential h v (differential h v z.val) = 0
    exact LinearMap.congr_fun (DirectSumTotal.differential_square (horizontalColumn h)
      (verticalColumn v) (horizontalColumn_square h hh) (verticalColumn_square v hv)
        (column_anticommute h v ha)) z.val

/-- Exactness at the lowest total degree has no incoming term and means
injectivity of its outgoing differential. -/
theorem homogeneousTotal_zero_injective
    (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1))
    (hinj : Function.Injective (h 0 0)) : Function.Injective (homogeneousDifferential h v 0) := by
  intro x y hxy
  apply Subtype.ext
  ext p q
  by_cases hpq : p+q=0
  · have hp : p=0 := by omega
    have hq : q=0 := by omega
    subst p q
    apply hinj
    have heq := congrArg
      (fun z : homogeneous (R := R) (V := V) 1 => z.val 1 0) hxy
    change differential h v x.val 1 0 = differential h v y.val 1 0 at heq
    simpa only [differential_succ_zero] using heq
  · rw [x.property p q hpq, y.property p q hpq]


/-- The standard total-complex sign on a commuting raw vertical differential.
Integer scalar multiplication works over any coefficient ring. -/
def signedVertical (v : ∀ p q, V p q →ₗ[R] V p (q+1)) (p q : ℕ) :
    V p q →ₗ[R] V p (q+1) := (-1 : ℤ)^p • v p q

theorem signedVertical_square
    (v : ∀ p q, V p q →ₗ[R] V p (q+1))
    (hv : ∀ p q, (v p (q+1)).comp (v p q) = 0) (p q : ℕ) :
    (signedVertical v p (q+1)).comp (signedVertical v p q) = 0 := by
  apply LinearMap.ext
  intro x
  have hvx : v p (q+1) (v p q x) = 0 := LinearMap.congr_fun (hv p q) x
  change (-1 : ℤ)^p • v p (q+1) ((-1 : ℤ)^p • v p q x) = 0
  rw [map_zsmul, hvx, smul_zero, smul_zero]

theorem horizontal_signedVertical_anticommute
    (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1))
    (hc : ∀ p q, (h p (q+1)).comp (v p q) = (v (p+1) q).comp (h p q))
    (p q : ℕ) :
    (h p (q+1)).comp (signedVertical v p q) +
      (signedVertical v (p+1) q).comp (h p q) = 0 := by
  apply LinearMap.ext
  intro x
  have hcx : h p (q+1) (v p q x) = v (p+1) q (h p q x) :=
    LinearMap.congr_fun (hc p q) x
  have hsign : (-1 : ℤ)^(p+1) = -((-1 : ℤ)^p) := by
    rw [pow_succ, mul_neg_one]
  change h p (q+1) ((-1 : ℤ)^p • v p q x) +
    (-1 : ℤ)^(p+1) • v (p+1) q (h p q x) = 0
  rw [map_zsmul, hsign, neg_smul, hcx, add_neg_cancel]

/-- Exact total complex for a genuine commuting first-quadrant bicomplex,
with the usual dh + (-1)^p dv convention. All primitives have exactly the
preceding total degree, and no finite-dimensionality assumption occurs. -/
theorem homogeneousTotal_exact_of_commuting_bicomplex
    (h : ∀ p q, V p q →ₗ[R] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[R] V p (q+1))
    (hh : ∀ p q, (h (p+1) q).comp (h p q) = 0)
    (hv : ∀ p q, (v p (q+1)).comp (v p q) = 0)
    (hc : ∀ p q, (h p (q+1)).comp (v p q) = (v (p+1) q).comp (h p q))
    (hinj : ∀ q, Function.Injective (h 0 q))
    (hexact : ∀ p q, Function.Exact (h p q) (h (p+1) q)) (n : ℕ) :
    Function.Exact (homogeneousDifferential h (signedVertical v) n)
      (homogeneousDifferential h (signedVertical v) (n+1)) :=
  homogeneousTotal_exact_of_horizontal_exact h (signedVertical v) hh
    (signedVertical_square v hv) (horizontal_signedVertical_anticommute h v hc) hinj hexact n

end BigradedTotal

section OpenSmoothSimplex

open SmoothManifolds.MapData SmoothManifolds.SmoothSingularData

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) (U : TopologicalSpace.Opens M)
  (T : AtlasData.SmoothManifold n a U)

/-- A corner-smooth simplex whose image is in an open submanifold is smooth
there in the restricted intrinsic structure. -/
theorem simplexSmooth_codRestrict_open
    (hsub : MapData.openSubsetAtlas S.smoothStructure.val U U.isOpen ⊆ T.smoothStructure.val)
    {q : ℕ} (σ : Simplex q → U)
    (hσ : SimplexSmooth S (Subtype.val ∘ σ)) : SimplexSmooth T σ := by
  have hcont : Continuous σ := continuous_induced_rng.mpr hσ.1
  refine ⟨hcont, ?_⟩
  intro x d hd hdx
  obtain ⟨c, hc, hcx⟩ := S.smoothStructure.property.1.1 (σ x).val
  let e := c.subtypeRestr (s := U) ⟨σ x⟩
  have he : e ∈ T.smoothStructure.val := hsub ⟨⟨σ x⟩, c, hc, rfl⟩
  have hex : σ x ∈ e.source := by simpa [e] using hcx
  have hid : MapData.IsSmoothMap T T id :=
    manifoldContDiff_id (⊤ : ℕ∞) _ T.smoothStructure.property.1
  have hext := (hid (σ x)).2 e he d hd hex hdx
  have hpre := SmoothManifolds.LocalCoordinateExtension.precomp hext hcont.continuousAt rfl
  exact SmoothManifolds.LocalCoordinateExtension.comp hpre (hσ.2 x c hc hcx)

/-- The actual smooth simplex basis on an open submanifold is equivalent to
ambient smooth simplices supported in that open set. -/
def openP104SimplexEquiv
    (hsub : MapData.openSubsetAtlas S.smoothStructure.val U U.isOpen ⊆ T.smoothStructure.val)
    (hinc : MapData.IsSmoothMap T S Subtype.val) (q : ℕ) :
    SingularSimplex T q ≃ {σ : SingularSimplex S q // ∀ x, σ.val x ∈ U} where
  toFun σ := ⟨⟨Subtype.val ∘ σ.val, SmoothSingular.smooth_postcompose hinc σ.property⟩,
    fun x => (σ.val x).property⟩
  invFun σ := ⟨fun x => ⟨σ.val.val x, σ.property x⟩,
    simplexSmooth_codRestrict_open S U T hsub _ σ.val.property⟩
  left_inv σ := by rfl
  right_inv σ := by rfl


open P202Specs P202Specs.DeRhamComparison

/-- Ambient smooth simplices supported in the actual open set, using the
shared ordinary geometric simplex rather than a new simplex model. -/
def SupportedSmoothSimplex (q : ℕ) :=
  {σ : SmoothSimplex S q //
    Set.range (SingularChains.simplexEquiv (TopCat.of M) q σ.val) ⊆ U}

def supportedP104SimplexEquiv (q : ℕ) :
    SupportedSmoothSimplex S U q ≃
      {σ : SingularSimplex S q // ∀ x, σ.val x ∈ U} where
  toFun σ := ⟨p104Simplex S σ.val,
    fun x => σ.property ⟨SmoothSingularComparison.toBarycentric q x, rfl⟩⟩
  invFun τ := ⟨(p104SimplexEquiv S q).symm τ.val, by
    rintro _ ⟨x, rfl⟩
    have he := congrArg (fun σ : SingularSimplex S q =>
      σ.val (SmoothSingularComparison.toCorner q x))
      ((p104SimplexEquiv S q).apply_symm_apply τ.val)
    change SingularChains.simplexEquiv (TopCat.of M) q
      ((p104SimplexEquiv S q).symm τ.val).val
      (SmoothSingularComparison.toBarycentric q
        (SmoothSingularComparison.toCorner q x)) = _ at he
    rw [SmoothSingularComparison.toBarycentric_toCorner] at he
    exact he ▸ τ.property (SmoothSingularComparison.toCorner q x)⟩
  left_inv σ := by
    apply Subtype.ext
    exact (p104SimplexEquiv S q).symm_apply_apply σ.val
  right_inv σ := by
    apply Subtype.ext
    exact (p104SimplexEquiv S q).apply_symm_apply σ.val

/-- The intrinsic smooth basis on an open submanifold is the supported
subset of the shared ambient ordinary basis. -/
def openSmoothSimplexEquiv
    (hsub : MapData.openSubsetAtlas S.smoothStructure.val U U.isOpen ⊆ T.smoothStructure.val)
    (hinc : MapData.IsSmoothMap T S Subtype.val) (q : ℕ) :
    SmoothSimplex T q ≃ SupportedSmoothSimplex S U q :=
  ((p104SimplexEquiv T q).trans (openP104SimplexEquiv S U T hsub hinc q)).trans
    (supportedP104SimplexEquiv S U q).symm

end OpenSmoothSimplex


section OpenFormsBridge

open SmoothManifolds.MayerVietorisData SmoothManifolds.MapData SmoothManifolds.TangentData
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) (U : TopologicalSpace.Opens M)
  {C : CotangentBundle S} {B : ∀ k, FormBundle C k}

def openSubmanifold : AtlasData.SmoothManifold n a U :=
  (SmoothManifolds.exists_openSubset_smoothManifold S U U.isOpen).choose

theorem openSubmanifold_atlas :
    (openSubmanifold S U).smoothStructure.val = AtlasData.maximalExtension (⊤ : ℕ∞)
      (MapData.openSubsetAtlas S.smoothStructure.val U U.isOpen) :=
  (SmoothManifolds.exists_openSubset_smoothManifold S U U.isOpen).choose_spec.2.1

theorem openSubmanifold_inclusion_smooth :
    MapData.IsSmoothMap (openSubmanifold S U) S Subtype.val :=
  (SmoothManifolds.exists_openSubset_smoothManifold S U U.isOpen).choose_spec.2.2

theorem openSubmanifold_restricted_atlas_subset :
    MapData.openSubsetAtlas S.smoothStructure.val U U.isOpen ⊆ (openSubmanifold S U).smoothStructure.val := by
  rw [openSubmanifold_atlas]
  exact subset_maximalExtension
    (openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ S.smoothStructure.property.1 U U.isOpen)

def openInclusionTangentEquiv (p : U) :
    TangentData.TangentSpace (openSubmanifold S U) p ≃ₗ[ℝ] TangentData.TangentSpace S p.val :=
  LinearEquiv.ofBijective
    (SmoothManifolds.differential (openSubmanifold S U) S Subtype.val
      (openSubmanifold_inclusion_smooth S U) p)
    (SphereCohomology.openInclusionDifferential_bijective S U (openSubmanifold S U)
      (openSubmanifold_restricted_atlas_subset S U) (openSubmanifold_inclusion_smooth S U) p _
      (SmoothManifolds.differential_spec (openSubmanifold S U) S Subtype.val
        (openSubmanifold_inclusion_smooth S U) p))

theorem openInclusionTangentEquiv_isDifferential (p : U) :
    DifferentialData.IsDifferential (openSubmanifold S U) S Subtype.val p
      (openInclusionTangentEquiv S U p).toLinearMap :=
  SmoothManifolds.differential_spec (openSubmanifold S U) S Subtype.val
    (openSubmanifold_inclusion_smooth S U) p

def openFormsPullbackChain (K : Calculus C B)
    {A : CotangentBundle (openSubmanifold S U)} {E : ∀ k, FormBundle A k}
    (J : Calculus A E) (D : OpenCalculus C B U) :
    ChainMap D.complex (globalComplex J) :=
  SphereCohomology.inclusionPullChain S U (openSubmanifold S U)
    (openSubmanifold_inclusion_smooth S U)
    (fun p => (openInclusionTangentEquiv S U p).toLinearMap)
    (openInclusionTangentEquiv_isDifferential S U) K J D

theorem restrictedForms_positive_subsingleton_of_contractible
    [Nonempty U] [ContractibleSpace U] (K : Calculus C B) (D : OpenCalculus C B U)
    (q : ℕ) (hq : 0 < q) : Subsingleton (D.complex.H q) := by
  let R := openSubmanifold S U
  let A : CotangentBundle R := Classical.choice (BundleOperations.exists_cotangent R)
  let E (k : ℕ) : FormBundle A k := Classical.choice (ExteriorAlgebraResults.exists_formBundle A k)
  let J : Calculus A E := Classical.choice (DeRhamResults.complex_exists A E)
  obtain ⟨e⟩ := SphereCohomology.openCohomologyEquiv S U R
    (openSubmanifold_atlas S U) (openSubmanifold_inclusion_smooth S U) K J D q
  let := HomotopyResults.contractible_vanishing R A E J q hq
  exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
theorem openFormsPullbackChain_field (K : Calculus C B)
    {A : CotangentBundle (openSubmanifold S U)} {E : ∀ k, FormBundle A k}
    (J : Calculus A E) (D : OpenCalculus C B U) (q : ℕ) (ω : D.complex.Obj q) (p : U) :
    (((openFormsPullbackChain S U K J D).map q ω).val p) =
      FormPullbackData.fiberPullback (V := TangentData.TangentSpace (openSubmanifold S U) p)
        (W := TangentData.TangentSpace S p.val) q (openInclusionTangentEquiv S U p).toLinearMap
        (D.field q ω p) := rfl

theorem openFormsPullbackChain_bijective (K : Calculus C B)
    {A : CotangentBundle (openSubmanifold S U)} {E : ∀ k, FormBundle A k}
    (J : Calculus A E) (D : OpenCalculus C B U) (q : ℕ) :
    Function.Bijective ((openFormsPullbackChain S U K J D).map q) := by
  let F := openInclusionTangentEquiv S U
  have hF := openInclusionTangentEquiv_isDifferential S U
  constructor
  · intro α β h
    apply D.injective q
    funext p
    have hp := congrArg (fun γ : J.forms q => γ.val p) h
    change FormPullbackData.fiberPullback (V := TangentData.TangentSpace (openSubmanifold S U) p)
      (W := TangentData.TangentSpace S p.val) q (F p).toLinearMap (D.field q α p) =
      FormPullbackData.fiberPullback (V := TangentData.TangentSpace (openSubmanifold S U) p)
      (W := TangentData.TangentSpace S p.val) q (F p).toLinearMap (D.field q β p) at hp
    have hi := congrArg (FormPullbackData.fiberPullback (V := TangentData.TangentSpace S p.val)
      (W := TangentData.TangentSpace (openSubmanifold S U) p) q (F p).symm.toLinearMap) hp
    have hleft (η : Fiber (TangentData.TangentSpace S p.val) q) :
        FormPullbackData.fiberPullback (V := TangentData.TangentSpace S p.val)
      (W := TangentData.TangentSpace (openSubmanifold S U) p) q (F p).symm.toLinearMap
          (FormPullbackData.fiberPullback (V := TangentData.TangentSpace (openSubmanifold S U) p)
      (W := TangentData.TangentSpace S p.val) q (F p).toLinearMap η) = η :=
      @SphereCohomology.fiberPullback_symm_right
        (TangentData.TangentSpace S p.val) (TangentData.TangentSpace (openSubmanifold S U) p)
        (inferInstance : AddCommGroup (TangentData.TangentSpace S p.val))
        (inferInstance : Module ℝ (TangentData.TangentSpace S p.val))
        (inferInstance : AddCommGroup (TangentData.TangentSpace (openSubmanifold S U) p))
        (inferInstance : Module ℝ (TangentData.TangentSpace (openSubmanifold S U) p)) q (F p).symm η
    simpa only [hleft] using hi
  · intro α
    let ω : RestrictedField S U q := fun p =>
      FormPullbackData.fiberPullback (V := TangentData.TangentSpace S p.val)
      (W := TangentData.TangentSpace (openSubmanifold S U) p) q (F p).symm.toLinearMap (α.val p)
    have hω : IsRestrictedForm (B q) U ω :=
      SphereCohomology.openInverseField_smooth S U (openSubmanifold S U)
        (openSubmanifold_restricted_atlas_subset S U) (openSubmanifold_inclusion_smooth S U)
        C A (B q) (E q) F hF α.val ((J.mem_forms q _).mp α.property)
    obtain ⟨β, hβ⟩ := (D.range_smooth q ω).mp hω
    refine ⟨β, ?_⟩
    apply Subtype.ext
    funext p
    rw [openFormsPullbackChain_field, congrFun hβ p]
    exact @SphereCohomology.fiberPullback_symm_right
      (TangentData.TangentSpace (openSubmanifold S U) p) (TangentData.TangentSpace S p.val)
      (inferInstance : AddCommGroup (TangentData.TangentSpace (openSubmanifold S U) p))
      (inferInstance : Module ℝ (TangentData.TangentSpace (openSubmanifold S U) p))
      (inferInstance : AddCommGroup (TangentData.TangentSpace S p.val))
      (inferInstance : Module ℝ (TangentData.TangentSpace S p.val)) q (F p) (α.val p)

def openFormsCohomologyEquiv (K : Calculus C B)
    {A : CotangentBundle (openSubmanifold S U)} {E : ∀ k, FormBundle A k}
    (J : Calculus A E) (D : OpenCalculus C B U) (q : ℕ) :
    D.complex.H q ≃ₗ[ℝ] J.Cohomology q :=
  SphereCohomology.cohomologyEquivOfDegreewiseBijective
    (openFormsPullbackChain S U K J D) (openFormsPullbackChain_bijective S U K J D) q

@[simp] theorem openFormsCohomologyEquiv_class (K : Calculus C B)
    {A : CotangentBundle (openSubmanifold S U)} {E : ∀ k, FormBundle A k}
    (J : Calculus A E) (D : OpenCalculus C B U) (q : ℕ) (ω : D.complex.closed q) :
    openFormsCohomologyEquiv S U K J D q (D.complex.classOf q ω) =
      J.classOf q ((openFormsPullbackChain S U K J D).onClosed q ω) := by
  exact (openFormsPullbackChain S U K J D).onH_induced q ω
end OpenFormsBridge


namespace CoverForms
section HigherRows
open SmoothManifolds.MayerVietorisData SmoothManifolds.MayerVietorisData.OpenForms
open Set Filter
open scoped _root_.Topology
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : AtlasData.SmoothManifold n a M} {C : CotangentBundle S}
  {B : ∀ k, FormBundle C k}

variable (S)

/-- The intrinsic vector space of all actual smooth restricted q-forms. -/
def restrictedFormSpace (q : ℕ) (W : TopologicalSpace.Opens M) :
    Submodule ℝ (RestrictedField S W q) where
  carrier := IsRestrictedForm (B q) W
  zero_mem' := restricted_zero (B q) W
  add_mem' := fun hω hη => restricted_add (B q) W _ _ hω hη
  smul_mem' := fun r _ hω => restricted_smul (B q) W r _ hω

variable {ι : Type v} (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)

def formTupleOpen (k : ℕ) (t : Fin k → ι) : TopologicalSpace.Opens M :=
  ⟨{p | ∀ j, p ∈ U.sets (t j)},
    by
      convert isOpen_iInter_of_finite (fun j => U.isOpen (t j)) using 1
      ext p
      simp only [mem_iInter, mem_ofPred_eq]⟩

def formCoverOpen (i : ι) : TopologicalSpace.Opens M := ⟨U.sets i, U.isOpen i⟩

theorem formTupleOpen_delete_le {k : ℕ} (t : Fin (k+1) → ι) (j : Fin (k+1)) :
    formTupleOpen U (k+1) t ≤ formTupleOpen U k (t ∘ j.succAbove) :=
  fun _ hp l => hp (j.succAbove l)

theorem formTupleOpen_cons (k : ℕ) (t : Fin k → ι) (i : ι) :
    formTupleOpen U (k+1) (Fin.cons i t) = formCoverOpen U i ⊓ formTupleOpen U k t := by
  ext p
  change (∀ j : Fin (k+1), p ∈ U.sets ((Fin.cons i t : Fin (k+1) → ι) j)) ↔
    p ∈ U.sets i ∧ ∀ j : Fin k, p ∈ U.sets (t j)
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun j => by simpa using h j.succ⟩
  · rintro ⟨hi, ht⟩ j
    exact Fin.cases hi ht j

/-- Products over all ordered tuples, including the empty tuple. -/
abbrev FormsCechRow (q k : ℕ) :=
  (t : Fin k → ι) → restrictedFormSpace S (B := B) q (formTupleOpen U k t)

/-- Restriction of one deletion term in the horizontal differential. -/
def formsCechFace {q k : ℕ} (f : FormsCechRow S (B := B) U q k)
    (t : Fin (k+1) → ι) (j : Fin (k+1)) :
    restrictedFormSpace S (B := B) q (formTupleOpen U (k+1) t) :=
  ⟨fun p => (f (t ∘ j.succAbove)).val ⟨p.val, formTupleOpen_delete_le U t j p.property⟩,
    restricted_restrict (B q) _ _ (formTupleOpen_delete_le U t j)
      (f (t ∘ j.succAbove)).val (f (t ∘ j.succAbove)).property⟩

/-- Literal alternating restriction on actual products of intrinsic forms. -/
def formsCechD (q k : ℕ) :
    FormsCechRow S (B := B) U q k →ₗ[ℝ] FormsCechRow S (B := B) U q (k+1) where
  toFun f t := ⟨fun p => ∑ j : Fin (k+1), (-1 : ℝ)^j.val •
      (formsCechFace S U f t j).val p, by
    apply restrictedForm_finset_sum
    intro j
    exact restricted_smul (B q) _ ((-1 : ℝ)^j.val) _ (formsCechFace S U f t j).property⟩
  map_add' f g := by
    funext t
    apply Subtype.ext
    funext p
    change (∑ j : Fin (k+1), (-1 : ℝ)^j.val •
        (formsCechFace S U (f+g) t j).val p) =
      (∑ j : Fin (k+1), (-1 : ℝ)^j.val • (formsCechFace S U f t j).val p) +
      ∑ j : Fin (k+1), (-1 : ℝ)^j.val • (formsCechFace S U g t j).val p
    simp only [formsCechFace, Pi.add_apply, Submodule.coe_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext t
    apply Subtype.ext
    funext p
    change (∑ j : Fin (k+1), (-1 : ℝ)^j.val •
        (formsCechFace S U (r • f) t j).val p) =
      r • ∑ j : Fin (k+1), (-1 : ℝ)^j.val • (formsCechFace S U f t j).val p
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (-1 : ℝ)^j.val • (r • (f (t ∘ j.succAbove)).val
      ⟨p.val, formTupleOpen_delete_le U t j p.property⟩) =
      r • ((-1 : ℝ)^j.val • (f (t ∘ j.succAbove)).val
        ⟨p.val, formTupleOpen_delete_le U t j p.property⟩)
    exact smul_comm _ _ _

@[simp] theorem formsCechD_apply (q k : ℕ) (f : FormsCechRow S (B := B) U q k)
    (t : Fin (k+1) → ι) (p : formTupleOpen U (k+1) t) :
    (formsCechD S U q k f t).val p =
      ∑ j : Fin (k+1), (-1 : ℝ)^j.val •
        (f (t ∘ j.succAbove)).val ⟨p.val, formTupleOpen_delete_le U t j p.property⟩ := rfl

/-- Restriction of the inserted tuple to the identically equal open Ui ∩ Wt. -/
def formsCechCons {q k : ℕ} (f : FormsCechRow S (B := B) U q (k+1))
    (t : Fin k → ι) (i : ι) :
    restrictedFormSpace S (B := B) q (formCoverOpen U i ⊓ formTupleOpen U k t) := by
  let h : formCoverOpen U i ⊓ formTupleOpen U k t ≤
      formTupleOpen U (k+1) (Fin.cons i t) := by rw [formTupleOpen_cons]
  exact ⟨fun p => (f (Fin.cons i t)).val ⟨p.val, h p.property⟩,
    restricted_restrict (B q) _ _ h (f (Fin.cons i t)).val (f (Fin.cons i t)).property⟩

/-- Smooth partition insertion on actual intrinsic Čech forms. -/
def formsCechH (q k : ℕ) (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate U.sets ρ) :
    FormsCechRow S (B := B) U q (k+1) → FormsCechRow S (B := B) U q k :=
  fun f t => ⟨fun p => ∑ᶠ i, zeroExtend
    (fun y : ↥(formCoverOpen U i ⊓ formTupleOpen U k t) =>
      ρ i y.val • (formsCechCons S U f t i).val y) p.val,
    restrictedForm_partition_sum (formTupleOpen U k t) (formCoverOpen U) ρ hρ hsub
      (fun i => (formsCechCons S U f t i).val)
      (fun i => (formsCechCons S U f t i).property)⟩

@[simp] theorem formsCechH_apply (q k : ℕ) (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate U.sets ρ)
    (f : FormsCechRow S (B := B) U q (k+1)) (t : Fin k → ι)
    (p : formTupleOpen U k t) :
    (formsCechH S U q k ρ hρ hsub f t).val p =
      ∑ᶠ i, zeroExtend
        (fun y : ↥(formCoverOpen U i ⊓ formTupleOpen U k t) =>
          ρ i y.val • (formsCechCons S U f t i).val y) p.val := rfl


def formsCechAt {q k : ℕ} (f : FormsCechRow S (B := B) U q k)
    (p : M) : VectorSimplexRow ι (Fiber (TangentData.TangentSpace S p) q) k :=
  by
    classical
    exact fun t => if hp : p ∈ formTupleOpen U k t then (f t).val ⟨p, hp⟩ else 0

@[simp] theorem formsCechAt_of_mem {q k : ℕ}
    (f : FormsCechRow S (B := B) U q k) (p : M) (t : Fin k → ι)
    (hp : p ∈ formTupleOpen U k t) :
    formsCechAt S U f p t = (f t).val ⟨p, hp⟩ := by classical exact dite_eq_left hp

@[simp] theorem formsCechAt_of_not_mem {q k : ℕ}
    (f : FormsCechRow S (B := B) U q k) (p : M) (t : Fin k → ι)
    (hp : p ∉ formTupleOpen U k t) : formsCechAt S U f p t = 0 := by classical exact dite_eq_right hp

theorem formsCechAt_D_of_mem {q k : ℕ} (f : FormsCechRow S (B := B) U q k)
    (p : M) (t : Fin (k+1) → ι) (hp : p ∈ formTupleOpen U (k+1) t) :
    formsCechAt S U (formsCechD S U q k f) p t =
      vectorSimplexD ℝ ι (Fiber (TangentData.TangentSpace S p) q) k
        (formsCechAt S U f p) t := by
  rw [formsCechAt_of_mem S U _ _ _ hp, formsCechD_apply]
  change (∑ j : Fin (k+1), (-1 : ℝ)^j.val •
      (f (t ∘ j.succAbove)).val ⟨p, formTupleOpen_delete_le U t j hp⟩) =
    ∑ j : Fin (k+1), (-1 : ℝ)^j.val • formsCechAt S U f p (t ∘ j.succAbove)
  apply Finset.sum_congr rfl
  intro j _
  rw [formsCechAt_of_mem S U _ _ _ (formTupleOpen_delete_le U t j hp)]

theorem formsCechAt_H_term {q k : ℕ}
    (ρ : ι → M → ℝ) (f : FormsCechRow S (B := B) U q (k+1))
    (p : M) (t : Fin k → ι) (hp : p ∈ formTupleOpen U k t) (i : ι) :
    zeroExtend (fun y : ↥(formCoverOpen U i ⊓ formTupleOpen U k t) =>
      ρ i y.val • (formsCechCons S U f t i).val y) p =
      ρ i p • formsCechAt S U f p (Fin.cons i t) := by
  by_cases hi : p ∈ U.sets i
  · have hc : p ∈ formTupleOpen U (k+1) (Fin.cons i t) := by
      rw [formTupleOpen_cons]
      exact ⟨hi, hp⟩
    rw [formsCechAt_of_mem S U _ _ _ hc]
    unfold zeroExtend
    rw [dite_eq_left (show p ∈ formCoverOpen U i ⊓ formTupleOpen U k t from ⟨hi, hp⟩)]
    rfl
  · have hc : p ∉ formTupleOpen U (k+1) (Fin.cons i t) := by
      rw [formTupleOpen_cons]
      exact fun h => hi h.1
    rw [formsCechAt_of_not_mem S U _ _ _ hc, smul_zero]
    unfold zeroExtend
    rw [dite_eq_right (show p ∉ formCoverOpen U i ⊓ formTupleOpen U k t from fun h => hi h.1)]

theorem partition_weight_finite
    (ρ : ι → M → ℝ) (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (p : M) : Function.HasFiniteSupport (fun i => ρ i p) :=
  (hρ.2.2.1.point_finite p).subset (fun _ hi => subset_closure hi)

theorem formsCechAt_H {q k : ℕ}
    (ρ : ι → M → ℝ) (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate U.sets ρ)
    (f : FormsCechRow S (B := B) U q (k+1)) (p : M) :
    formsCechAt S U (formsCechH S U q k ρ hρ hsub f) p =
      ∑ᶠ i, ρ i p • vectorSimplexH ℝ ι
        (Fiber (TangentData.TangentSpace S p) q) i k (formsCechAt S U f p) := by
  funext t
  have hfin : Function.HasFiniteSupport (fun i => ρ i p •
      vectorSimplexH ℝ ι (Fiber (TangentData.TangentSpace S p) q)
        i k (formsCechAt S U f p)) := by
    convert (partition_weight_finite S ρ hρ p).smul_left
      (fun i => vectorSimplexH ℝ ι (Fiber (TangentData.TangentSpace S p) q)
        i k (formsCechAt S U f p)) using 1
  rw [finsum_apply hfin t]
  by_cases hp : p ∈ formTupleOpen U k t
  · rw [formsCechAt_of_mem S U _ _ _ hp, formsCechH_apply]
    apply finsum_congr
    intro i
    exact formsCechAt_H_term S U ρ f p t hp i
  · rw [formsCechAt_of_not_mem S U _ _ _ hp]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    change ρ i p • formsCechAt S U f p (Fin.cons i t) = 0
    have hc : p ∉ formTupleOpen U (k+1) (Fin.cons i t) := by
      rw [formTupleOpen_cons]
      exact fun h => hp h.2
    rw [formsCechAt_of_not_mem S U _ _ _ hc, smul_zero]

theorem formsCechAt_H_D_of_mem {q k : ℕ}
    (ρ : ι → M → ℝ) (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate U.sets ρ)
    (f : FormsCechRow S (B := B) U q k) (p : M) (t : Fin k → ι)
    (hp : p ∈ formTupleOpen U k t) :
    formsCechAt S U (formsCechH S U q k ρ hρ hsub (formsCechD S U q k f)) p t =
      (∑ᶠ i, ρ i p • vectorSimplexH ℝ ι
        (Fiber (TangentData.TangentSpace S p) q) i k
          (vectorSimplexD ℝ ι (Fiber (TangentData.TangentSpace S p) q) k
            (formsCechAt S U f p))) t := by
  rw [formsCechAt_H]
  have hfin (g : VectorSimplexRow ι (Fiber (TangentData.TangentSpace S p) q) (k+1)) :
      Function.HasFiniteSupport (fun i => ρ i p • vectorSimplexH ℝ ι
        (Fiber (TangentData.TangentSpace S p) q) i k g) := by
    convert (partition_weight_finite S ρ hρ p).smul_left
      (fun i => vectorSimplexH ℝ ι (Fiber (TangentData.TangentSpace S p) q) i k g) using 1
  rw [finsum_apply (hfin _) t, finsum_apply (hfin _) t]
  apply finsum_congr
  intro i
  change ρ i p • formsCechAt S U (formsCechD S U q k f) p (Fin.cons i t) =
    ρ i p • vectorSimplexD ℝ ι (Fiber (TangentData.TangentSpace S p) q) k
      (formsCechAt S U f p) (Fin.cons i t)
  by_cases hi : p ∈ U.sets i
  · have hc : p ∈ formTupleOpen U (k+1) (Fin.cons i t) := by
      rw [formTupleOpen_cons]
      exact ⟨hi, hp⟩
    rw [formsCechAt_D_of_mem S U f p _ hc]
  · have hz : ρ i p = 0 := by
      by_contra hn
      exact hi (hsub i (subset_closure hn))
    simp only [hz, zero_smul]

/-- The actual forms Čech row is contracted by the genuine smooth partition
insertion, in every horizontal degree and for arbitrary cover cardinality. -/
theorem formsCech_contract {q k : ℕ}
    (ρ : ι → M → ℝ) (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate U.sets ρ)
    (f : FormsCechRow S (B := B) U q (k+1)) :
    formsCechD S U q k (formsCechH S U q k ρ hρ hsub f) +
      formsCechH S U q (k+1) ρ hρ hsub (formsCechD S U q (k+1) f) = f := by
  funext t
  apply Subtype.ext
  funext p
  let V := Fiber (TangentData.TangentSpace S p.val) q
  have hc₀ := vectorSimplex_finsum_contract ℝ ι V (fun i => ρ i p.val)
    (partition_weight_finite S ρ hρ p.val) k (formsCechAt S U f p.val)
  have hnorm : (∑ᶠ i, ρ i p.val) • formsCechAt S U f p.val =
      formsCechAt S U f p.val :=
    (congrArg (fun r : ℝ => r • formsCechAt S U f p.val) (hρ.2.2.2 p.val)).trans
      (one_smul ℝ _)
  have hc := congrFun (hc₀.trans hnorm) t
  have hd₀ := formsCechAt_D_of_mem S U (formsCechH S U q k ρ hρ hsub f)
    p.val t p.property
  have hh₀ := formsCechAt_H S U ρ hρ hsub f p.val
  have hd := hd₀.trans (congrArg
    (fun g => vectorSimplexD ℝ ι V k g t) hh₀)
  have hh := formsCechAt_H_D_of_mem S U ρ hρ hsub f p.val t p.property
  have hd₁ := (formsCechAt_of_mem S U _ _ _ p.property).symm.trans hd
  have hh₁ := (formsCechAt_of_mem S U _ _ _ p.property).symm.trans hh
  change (formsCechD S U q k (formsCechH S U q k ρ hρ hsub f) t).val p +
    (formsCechH S U q (k+1) ρ hρ hsub (formsCechD S U q (k+1) f) t).val p = (f t).val p
  exact (congrArg₂ (fun x y : V => x+y) hd₁ hh₁).trans
    (hc.trans (formsCechAt_of_mem S U f p.val t p.property))

theorem formsCechD_squared {q k : ℕ} (f : FormsCechRow S (B := B) U q k) :
    formsCechD S U q (k+1) (formsCechD S U q k f) = 0 := by
  funext t
  apply Subtype.ext
  funext p
  let V := Fiber (TangentData.TangentSpace S p.val) q
  have hd := formsCechAt_D_of_mem S U (formsCechD S U q k f) p.val t p.property
  have hinner : vectorSimplexD ℝ ι V (k+1)
      (formsCechAt S U (formsCechD S U q k f) p.val) t =
      vectorSimplexD ℝ ι V (k+1)
        (vectorSimplexD ℝ ι V k (formsCechAt S U f p.val)) t := by
    change (∑ j : Fin (k+2), (-1 : ℝ)^j.val •
      formsCechAt S U (formsCechD S U q k f) p.val (t ∘ j.succAbove)) =
      ∑ j : Fin (k+2), (-1 : ℝ)^j.val •
        vectorSimplexD ℝ ι V k (formsCechAt S U f p.val) (t ∘ j.succAbove)
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun x : V => (-1 : ℝ)^j.val • x)
      (formsCechAt_D_of_mem S U f p.val (t ∘ j.succAbove)
        (formTupleOpen_delete_le U t j p.property))
  have hz := congrFun (vectorSimplexD_squared ℝ ι V k (formsCechAt S U f p.val)) t
  exact (formsCechAt_of_mem S U _ _ _ p.property).symm.trans
    (hd.trans (hinner.trans hz))

@[simp] theorem formsCechAt_zero {q k : ℕ} (p : M) :
    formsCechAt S U (0 : FormsCechRow S (B := B) U q k) p = 0 := by
  funext t
  unfold formsCechAt
  split_ifs <;> rfl

@[simp] theorem formsCechH_zero (q k : ℕ)
    (ρ : ι → M → ℝ) (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate U.sets ρ) :
    formsCechH S U q k ρ hρ hsub (0 : FormsCechRow S (B := B) U q (k+1)) = 0 := by
  funext t
  apply Subtype.ext
  funext p
  have hh := formsCechAt_H S U ρ hρ hsub
    (0 : FormsCechRow S (B := B) U q (k+1)) p.val
  have he := congrArg
    (fun g => ∑ᶠ i, ρ i p.val • vectorSimplexH ℝ ι
      (Fiber (TangentData.TangentSpace S p.val) q) i k g)
    (formsCechAt_zero S (B := B) U (q := q) (k := k+1) p.val)
  have hsum : (∑ᶠ i, ρ i p.val • vectorSimplexH ℝ ι
      (Fiber (TangentData.TangentSpace S p.val) q) i k
        (0 : VectorSimplexRow ι (Fiber (TangentData.TangentSpace S p.val) q) (k+1))) = 0 := by
    simp only [map_zero, smul_zero, finsum_zero]
  exact (formsCechAt_of_mem S U _ _ _ p.property).symm.trans
    (congrFun ((hh.trans he).trans hsum) t)

/-- Partition contraction includes the augmentation at the empty tuple. -/
theorem formsCech_contract_zero {q : ℕ}
    (ρ : ι → M → ℝ) (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate U.sets ρ)
    (f : FormsCechRow S (B := B) U q 0) :
    formsCechH S U q 0 ρ hρ hsub (formsCechD S U q 0 f) = f := by
  funext t
  apply Subtype.ext
  funext p
  let V := Fiber (TangentData.TangentSpace S p.val) q
  have hh := formsCechAt_H_D_of_mem S U ρ hρ hsub f p.val t p.property
  have hc₀ := vectorSimplex_finsum_contract_zero ℝ ι V (fun i => ρ i p.val)
    (partition_weight_finite S ρ hρ p.val) (formsCechAt S U f p.val)
  have hnorm : (∑ᶠ i, ρ i p.val) • formsCechAt S U f p.val =
      formsCechAt S U f p.val :=
    (congrArg (fun r : ℝ => r • formsCechAt S U f p.val) (hρ.2.2.2 p.val)).trans
      (one_smul ℝ _)
  have hc := congrFun (hc₀.trans hnorm) t
  exact (formsCechAt_of_mem S U _ _ _ p.property).symm.trans
    (hh.trans (hc.trans (formsCechAt_of_mem S U f p.val t p.property)))

theorem formsCech_augmentation_injective {q : ℕ}
    (ρ : ι → M → ℝ) (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate U.sets ρ) :
    Function.Injective (formsCechD S (B := B) U q 0) := by
  intro f g he
  exact (formsCech_contract_zero S U ρ hρ hsub f).symm.trans
    ((congrArg (formsCechH S U q 0 ρ hρ hsub) he).trans
      (formsCech_contract_zero S U ρ hρ hsub g))

theorem formsCech_exact {q k : ℕ}
    (ρ : ι → M → ℝ) (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate U.sets ρ)
    (f : FormsCechRow S (B := B) U q (k+1)) :
    formsCechD S U q (k+1) f = 0 ↔ ∃ g, formsCechD S U q k g = f := by
  constructor
  · intro hf
    have hc := formsCech_contract S U ρ hρ hsub f
    rw [hf, formsCechH_zero, add_zero] at hc
    exact ⟨formsCechH S U q k ρ hρ hsub f, hc⟩
  · rintro ⟨g, rfl⟩
    exact formsCechD_squared S U g

/-- Full augmented horizontal exactness of the actual differential-form
Čech row, with arbitrary open-cover index cardinality. -/
theorem formsCechRowsExact (q : ℕ) :
    Function.Injective (formsCechD S (B := B) U q 0) ∧
      ∀ k (f : FormsCechRow S (B := B) U q (k+1)),
        formsCechD S U q (k+1) f = 0 ↔ ∃ g, formsCechD S U q k g = f := by
  obtain ⟨ρ, hρ, hsub⟩ := SmoothManifolds.exists_smooth_partition S U.sets U.isOpen U.covers
  exact ⟨formsCech_augmentation_injective S U ρ hρ hsub,
    fun _ f => formsCech_exact S U ρ hρ hsub f⟩


/-- Restricting a global form to the unique empty tuple identifies it with
the actual augmentation row, rather than assuming a new global form model. -/
def formsCechAugmentation (K : Calculus C B) (q : ℕ) :
    K.forms q →ₗ[ℝ] FormsCechRow S (B := B) U q 0 where
  toFun ω t := ⟨fun p => ω.val p.val,
    restrict_smooth (B q) (formTupleOpen U 0 t) ω.val
      ((K.mem_forms q ω.val).mp ω.property)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem formsCechAugmentation_bijective (K : Calculus C B) (q : ℕ) :
    Function.Bijective (formsCechAugmentation S U K q) := by
  classical
  let t₀ : Fin 0 → ι := Fin.elim0
  have hp₀ (p : M) : p ∈ formTupleOpen U 0 t₀ := fun j => Fin.elim0 j
  constructor
  · intro ω η he
    apply Subtype.ext
    funext p
    exact congrArg (fun f => (f t₀).val ⟨p, hp₀ p⟩) he
  · intro f
    let α : Field S q := fun p => (f t₀).val ⟨p, hp₀ p⟩
    have hα : IsForm (B q) α := by
      letI := (cotangentSpace C).topology
      letI := (B q).space.topology
      let F : M → Bundle.TotalSpace (ModelData.Euclidean (n.choose q))
          (fun p => Fiber (TangentData.TangentSpace S p) q) := fun p => ⟨p, α p⟩
      have he : (fun p : formTupleOpen U 0 t₀ => F p.val) =
          (fun p : formTupleOpen U 0 t₀ =>
            (⟨p.val, (f t₀).val p⟩ : Bundle.TotalSpace (ModelData.Euclidean (n.choose q))
              (fun p => Fiber (TangentData.TangentSpace S p) q))) := by
        funext p
        rfl
      have hs : MapData.ManifoldSmoothOn S.smoothStructure.val
          (B q).space.bundle.totalManifold.smoothStructure.val F (formTupleOpen U 0 t₀) :=
        (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ F (formTupleOpen U 0 t₀)
          (formTupleOpen U 0 t₀).isOpen).mpr (he.symm ▸ (f t₀).property)
      intro p
      exact hs p (hp₀ p)
    refine ⟨⟨α, (K.mem_forms q α).mpr hα⟩, ?_⟩
    funext t
    have ht : t = t₀ := Subsingleton.elim _ _
    subst t
    apply Subtype.ext
    funext p
    rfl

def formsCechAugmentationEquiv (K : Calculus C B) (q : ℕ) :
    K.forms q ≃ₗ[ℝ] FormsCechRow S (B := B) U q 0 :=
  LinearEquiv.ofBijective (formsCechAugmentation S U K q)
    (formsCechAugmentation_bijective S U K q)


def openFormEquiv (W : TopologicalSpace.Opens M) (D : OpenCalculus C B W) (q : ℕ) :
    D.complex.Obj q ≃ₗ[ℝ] restrictedFormSpace S (B := B) q W :=
  LinearEquiv.ofBijective
    ((D.field q).codRestrict (restrictedFormSpace S (B := B) q W)
      (fun ω => field_smooth D q ω)) (by
    constructor
    · intro x y he
      exact D.injective q (congrArg Subtype.val he)
    · intro ω
      obtain ⟨x, hx⟩ := (D.range_smooth q ω.val).mp ω.property
      exact ⟨x, Subtype.ext hx⟩)

@[simp] theorem openFormEquiv_field (W : TopologicalSpace.Opens M)
    (D : OpenCalculus C B W) (q : ℕ) (x : D.complex.Obj q) :
    (openFormEquiv S W D q x).val = D.field q x := rfl

@[simp] theorem openFormEquiv_symm_field (W : TopologicalSpace.Opens M)
    (D : OpenCalculus C B W) (q : ℕ) (ω : restrictedFormSpace S (B := B) q W) :
    D.field q ((openFormEquiv S W D q).symm ω) = ω.val :=
  congrArg Subtype.val ((openFormEquiv S W D q).apply_symm_apply ω)

def chosenOpenCalculus (K : Calculus C B) (W : TopologicalSpace.Opens M) :
    OpenCalculus C B W := (openCalculus_exists K W).some

/-- The genuine restricted intrinsic exterior differential, transported from
an actual full OpenCalculus realization. -/
def restrictedFormsD (K : Calculus C B) (W : TopologicalSpace.Opens M) (q : ℕ) :
    restrictedFormSpace S (B := B) q W →ₗ[ℝ] restrictedFormSpace S (B := B) (q+1) W :=
  (openFormEquiv S W (chosenOpenCalculus S K W) (q+1)).toLinearMap ∘ₗ
    (chosenOpenCalculus S K W).complex.d q ∘ₗ
      (openFormEquiv S W (chosenOpenCalculus S K W) q).symm.toLinearMap

theorem restrictedFormsD_coordinates (K : Calculus C B)
    (W : TopologicalSpace.Opens M) (q : ℕ)
    (ω : restrictedFormSpace S (B := B) q W) :
    HasRestrictedDerivative C W ω.val (restrictedFormsD S K W q ω).val := by
  have h := (chosenOpenCalculus S K W).coordinates q
    ((openFormEquiv S W (chosenOpenCalculus S K W) q).symm ω)
  rw [openFormEquiv_symm_field] at h
  exact h

theorem restrictedFormsD_squared (K : Calculus C B)
    (W : TopologicalSpace.Opens M) (q : ℕ)
    (ω : restrictedFormSpace S (B := B) q W) :
    restrictedFormsD S K W (q+1) (restrictedFormsD S K W q ω) = 0 := by
  change openFormEquiv S W (chosenOpenCalculus S K W) (q+2)
    ((chosenOpenCalculus S K W).complex.d (q+1)
      ((openFormEquiv S W (chosenOpenCalculus S K W) (q+1)).symm
        (openFormEquiv S W (chosenOpenCalculus S K W) (q+1)
          ((chosenOpenCalculus S K W).complex.d q
            ((openFormEquiv S W (chosenOpenCalculus S K W) q).symm ω))))) = 0
  rw [LinearEquiv.symm_apply_apply, Cochain.square, map_zero]

/-- Literal restriction on the full vector spaces of actual smooth forms. -/
def restrictedFormsRestriction (V W : TopologicalSpace.Opens M) (hWV : W ≤ V) (q : ℕ) :
    restrictedFormSpace S (B := B) q V →ₗ[ℝ] restrictedFormSpace S (B := B) q W where
  toFun ω := ⟨fun p => ω.val ⟨p.val, hWV p.property⟩,
    restricted_restrict (B q) V W hWV ω.val ω.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrictedFormsD_restriction (K : Calculus C B)
    (V W : TopologicalSpace.Opens M) (hWV : W ≤ V) (q : ℕ)
    (ω : restrictedFormSpace S (B := B) q V) :
    restrictedFormsD S K W q (restrictedFormsRestriction S V W hWV q ω) =
      restrictedFormsRestriction S V W hWV (q+1) (restrictedFormsD S K V q ω) := by
  apply Subtype.ext
  exact restricted_derivative_unique C W _ _ _
    (restrictedFormsD_coordinates S K W q (restrictedFormsRestriction S V W hWV q ω))
    (restricted_derivative_restrict C V W hWV ω.val
      (restrictedFormsD S K V q ω).val (restrictedFormsD_coordinates S K V q ω))

variable {ι : Type v} (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)

def formsCechV (K : Calculus C B) (q k : ℕ) :
    FormsCechRow S (B := B) U q k →ₗ[ℝ] FormsCechRow S (B := B) U (q+1) k where
  toFun f t := restrictedFormsD S K (formTupleOpen U k t) q (f t)
  map_add' f g := by
    funext t
    exact (restrictedFormsD S K (formTupleOpen U k t) q).map_add (f t) (g t)
  map_smul' r f := by
    funext t
    exact (restrictedFormsD S K (formTupleOpen U k t) q).map_smul r (f t)

theorem formsCechV_squared (K : Calculus C B) (q k : ℕ)
    (f : FormsCechRow S (B := B) U q k) :
    formsCechV S U K (q+1) k (formsCechV S U K q k f) = 0 := by
  funext t
  exact restrictedFormsD_squared S K (formTupleOpen U k t) q (f t)

def restrictedFormEvaluation (W : TopologicalSpace.Opens M) (q : ℕ) (p : W) :
    restrictedFormSpace S (B := B) q W →ₗ[ℝ] Fiber (TangentData.TangentSpace S p.val) q where
  toFun ω := ω.val p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem formsCechD_sum (q k : ℕ) (f : FormsCechRow S (B := B) U q k)
    (t : Fin (k+1) → ι) :
    formsCechD S U q k f t =
      ∑ j : Fin (k+1), (-1 : ℝ)^j.val • formsCechFace S U f t j := by
  apply Subtype.ext
  funext p
  have he := map_sum (restrictedFormEvaluation S (B := B) (formTupleOpen U (k+1) t) q p)
    (fun j : Fin (k+1) => (-1 : ℝ)^j.val • formsCechFace S U f t j) Finset.univ
  simp only [map_smul] at he
  exact he.symm

theorem formsCechV_face (K : Calculus C B) {q k : ℕ}
    (f : FormsCechRow S (B := B) U q k) (t : Fin (k+1) → ι) (j : Fin (k+1)) :
    restrictedFormsD S K (formTupleOpen U (k+1) t) q (formsCechFace S U f t j) =
      formsCechFace S U (formsCechV S U K q k f) t j :=
  restrictedFormsD_restriction S K (formTupleOpen U k (t ∘ j.succAbove))
    (formTupleOpen U (k+1) t) (formTupleOpen_delete_le U t j) q (f (t ∘ j.succAbove))

/-- Actual intrinsic exterior differentiation commutes with the literal
alternating restrictions in the full forms Čech bicomplex. -/
theorem formsCechV_D (K : Calculus C B) (q k : ℕ)
    (f : FormsCechRow S (B := B) U q k) :
    formsCechV S U K q (k+1) (formsCechD S U q k f) =
      formsCechD S U (q+1) k (formsCechV S U K q k f) := by
  funext t
  change restrictedFormsD S K (formTupleOpen U (k+1) t) q (formsCechD S U q k f t) = _
  let L := restrictedFormsD S K (formTupleOpen U (k+1) t) q
  have h₁ := congrArg L (formsCechD_sum S U q k f t)
  have h₂ := map_sum L (fun j : Fin (k+1) =>
    (-1 : ℝ)^j.val • formsCechFace S U f t j) Finset.univ
  have h₃ : (∑ j : Fin (k+1), L ((-1 : ℝ)^j.val • formsCechFace S U f t j)) =
      ∑ j : Fin (k+1), (-1 : ℝ)^j.val •
        formsCechFace S U (formsCechV S U K q k f) t j := by
    apply Finset.sum_congr rfl
    intro j _
    exact (L.map_smul ((-1 : ℝ)^j.val) (formsCechFace S U f t j)).trans
      (congrArg (fun ω => (-1 : ℝ)^j.val • ω) (formsCechV_face S U K f t j))
  exact (h₁.trans h₂).trans (h₃.trans
    (formsCechD_sum S U (q+1) k (formsCechV S U K q k f) t).symm)

/-- Restriction from the original intrinsic global forms to the full smooth
restricted-form space, including an empty or all-space open. -/
def globalRestrictedForm (K : Calculus C B) (W : TopologicalSpace.Opens M) (q : ℕ) :
    K.forms q →ₗ[ℝ] restrictedFormSpace S (B := B) q W where
  toFun ω := ⟨fun p => ω.val p.val,
    restrict_smooth (B q) W ω.val ((K.mem_forms q _).mp ω.property)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual global de Rham differential agrees with the vertical
restricted differential at every augmentation component. -/
theorem restrictedFormsD_global (K : Calculus C B)
    (W : TopologicalSpace.Opens M) (q : ℕ) (ω : K.forms q) :
    restrictedFormsD S K W q (globalRestrictedForm S K W q ω) =
      globalRestrictedForm S K W (q+1) (K.d q ω) := by
  apply Subtype.ext
  exact restricted_derivative_unique C W _ _ _
    (restrictedFormsD_coordinates S K W q (globalRestrictedForm S K W q ω))
    (global_derivative_restrict K q ω W)


end HigherRows
end CoverForms


open SmoothManifolds.MayerVietorisData
namespace BigradedTotal
variable {V : ℕ → ℕ → Type u}
  [∀ p q, AddCommGroup (V p q)] [∀ p q, Module ℝ (V p q)]

/-- The homogeneous total is an actual P104 nonnegative cochain complex,
with the ordinary closed/exact quotient cohomology and standard total signs. -/
def cochain
    (h : ∀ p q, V p q →ₗ[ℝ] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[ℝ] V p (q+1))
    (hh : ∀ p q, (h (p+1) q).comp (h p q) = 0)
    (hv : ∀ p q, (v p (q+1)).comp (v p q) = 0)
    (hc : ∀ p q, (h p (q+1)).comp (v p q) = (v (p+1) q).comp (h p q)) : SmoothManifolds.MayerVietorisData.Cochain.{u} where
  Obj n := homogeneous (R := ℝ) (V := V) n
  d n := homogeneousDifferential h (signedVertical v) n
  square n x := by
    apply Subtype.ext
    change differential h (signedVertical v) (differential h (signedVertical v) x.val) = 0
    exact LinearMap.congr_fun (DirectSumTotal.differential_square (horizontalColumn h)
      (verticalColumn (signedVertical v)) (horizontalColumn_square h hh)
      (verticalColumn_square (signedVertical v) (signedVertical_square v hv))
      (column_anticommute h (signedVertical v) (horizontal_signedVertical_anticommute h v hc))) x.val

theorem cochain_exact
    (h : ∀ p q, V p q →ₗ[ℝ] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[ℝ] V p (q+1))
    (hh : ∀ p q, (h (p+1) q).comp (h p q) = 0)
    (hv : ∀ p q, (v p (q+1)).comp (v p q) = 0)
    (hc : ∀ p q, (h p (q+1)).comp (v p q) = (v (p+1) q).comp (h p q))
    (hinj : ∀ q, Function.Injective (h 0 q))
    (hexact : ∀ p q, Function.Exact (h p q) (h (p+1) q)) (n : ℕ) :
    Function.Exact ((cochain h v hh hv hc).d n) ((cochain h v hh hv hc).d (n+1)) :=
  homogeneousTotal_exact_of_commuting_bicomplex h v hh hv hc hinj hexact n

theorem cochain_zero_injective
    (h : ∀ p q, V p q →ₗ[ℝ] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[ℝ] V p (q+1))
    (hh : ∀ p q, (h (p+1) q).comp (h p q) = 0)
    (hv : ∀ p q, (v p (q+1)).comp (v p q) = 0)
    (hc : ∀ p q, (h p (q+1)).comp (v p q) = (v (p+1) q).comp (h p q))
    (hinj : Function.Injective (h 0 0)) : Function.Injective ((cochain h v hh hv hc).d 0) :=
  homogeneousTotal_zero_injective h (signedVertical v) hinj

/-- Exact augmented rows annihilate the actual quotient cohomology of the
shifted augmented total, including its zero-incoming initial degree. -/
theorem cochain_cohomology_subsingleton
    (h : ∀ p q, V p q →ₗ[ℝ] V (p+1) q)
    (v : ∀ p q, V p q →ₗ[ℝ] V p (q+1))
    (hh : ∀ p q, (h (p+1) q).comp (h p q) = 0)
    (hv : ∀ p q, (v p (q+1)).comp (v p q) = 0)
    (hc : ∀ p q, (h p (q+1)).comp (v p q) = (v (p+1) q).comp (h p q))
    (hinj : ∀ q, Function.Injective (h 0 q))
    (hexact : ∀ p q, Function.Exact (h p q) (h (p+1) q)) (n : ℕ) :
    Subsingleton ((cochain h v hh hv hc).H n) := by
  let C := cochain h v hh hv hc
  have hall : ∀ x : C.H n, x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := C.class_surjective n x
    apply (C.class_zero_iff n a).mpr
    cases n with
    | zero =>
      have hda : C.d 0 a.val = 0 := a.property
      exact cochain_zero_injective h v hh hv hc (hinj 0) (hda.trans (map_zero _).symm)
    | succ n =>
      exact (cochain_exact h v hh hv hc hinj hexact n a.val).mp a.property
  exact ⟨fun x y => (hall x).trans (hall y).symm⟩

end BigradedTotal

section CochainDescentAlgebra

open SmoothManifolds.MayerVietorisData

namespace CochainDescent
variable {A B : Cochain.{u}} (f : ChainMap A B)

abbrev fiberObj (_f : ChainMap A B) : ℕ → Type u := fun n => match n with
  | 0 => A.Obj 0
  | n+1 => A.Obj (n+1) × B.Obj n

instance fiberObjGroup : ∀ n, AddCommGroup (fiberObj f n) := fun n => match n with
  | 0 => A.group 0
  | n+1 => inferInstanceAs (AddCommGroup (A.Obj (n+1) × B.Obj n))
instance fiberObjModule : ∀ n, Module ℝ (fiberObj f n) := fun n => match n with
  | 0 => A.module 0
  | n+1 => inferInstanceAs (Module ℝ (A.Obj (n+1) × B.Obj n))

def fiberD : ∀ n, fiberObj f n →ₗ[ℝ] fiberObj f (n+1) := fun n => match n with
  | 0 => {
    toFun := fun x => (A.d 0 x, f.map 0 x)
    map_add' := by intro x y; simp
    map_smul' := by intro r x; simp }
  | n+1 => {
    toFun := fun x => (A.d (n+1) x.1, f.map (n+1) x.1 - B.d n x.2)
    map_add' := by
      intro x y
      apply Prod.ext
      · exact map_add _ _ _
      · dsimp
        rw [map_add, map_add]
        abel
    map_smul' := by intro r x; simp [smul_sub] }

def mappingFiber : Cochain.{u} where
  Obj := fiberObj f
  d := fiberD f
  square n x := by
    cases n with
    | zero =>
      apply Prod.ext
      · exact A.square 0 x
      · change f.map 1 (A.d 0 x) - B.d 0 (f.map 0 x) = 0
        rw [f.comm, sub_self]
    | succ n =>
      apply Prod.ext
      · exact A.square (n+1) x.1
      · change f.map (n+2) (A.d (n+1) x.1) -
          B.d (n+1) (f.map (n+1) x.1 - B.d n x.2) = 0
        rw [map_sub, B.square, sub_zero, f.comm, sub_self]

def fiberSource : ∀ n, fiberObj f n →ₗ[ℝ] A.Obj n := fun n => match n with
  | 0 => LinearMap.id
  | n+1 => LinearMap.fst ℝ (A.Obj (n+1)) (B.Obj n)

theorem fiberSource_d (n : ℕ) (x : fiberObj f n) :
    fiberSource f (n+1) (fiberD f n x) = A.d n (fiberSource f n x) := by
  cases n <;> rfl

/-- Acyclicity of the explicit nonnegative mapping fiber implies that the
actual induced quotient cohomology map is bijective in every degree. The
initial injectivity condition is the zero-incoming-term case, not an assumed
cohomology isomorphism. -/
theorem onH_bijective_of_mappingFiber_exact
    (hzero : Function.Injective ((mappingFiber f).d 0))
    (hexact : ∀ n, Function.Exact ((mappingFiber f).d n) ((mappingFiber f).d (n+1))) :
    ∀ n, Function.Bijective (f.onH n) := by
  intro n
  constructor
  · apply (injective_iff_map_eq_zero (f.onH n)).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := A.class_surjective n x
    rw [f.onH_class] at hx
    have hfa := (B.class_zero_iff n (f.onClosed n a)).mp hx
    apply (A.class_zero_iff n a).mpr
    cases n with
    | zero =>
      have hfa0 : f.map 0 a.val = 0 := hfa
      have hda : (mappingFiber f).d 0 a.val = 0 :=
        Prod.ext a.property hfa0
      have ha0 : a.val = 0 := hzero (hda.trans (map_zero _).symm)
      exact ha0
    | succ n =>
      obtain ⟨b, hb⟩ := hfa
      let c : (mappingFiber f).Obj (n+1) := (a.val, b)
      have hc : (mappingFiber f).d (n+1) c = 0 := by
        apply Prod.ext
        · exact a.property
        · change f.map (n+1) a.val - B.d n b = 0
          exact sub_eq_zero.mpr hb.symm
      obtain ⟨z, hz⟩ := (hexact n c).mp hc
      refine ⟨fiberSource f n z, ?_⟩
      have hfirst := congrArg (fiberSource f (n+1)) hz
      change fiberSource f (n+1) (fiberD f n z) = a.val at hfirst
      exact (fiberSource_d f n z).symm.trans hfirst
  · intro x
    obtain ⟨b, rfl⟩ := B.class_surjective n x
    let c : (mappingFiber f).Obj (n+1) := (0, b.val)
    have hc : (mappingFiber f).d (n+1) c = 0 := by
      apply Prod.ext
      · exact map_zero _
      · change f.map (n+1) 0 - B.d n b.val = 0
        rw [map_zero, show B.d n b.val = 0 from b.property, sub_self]
    obtain ⟨z, hz⟩ := (hexact n c).mp hc
    have hclosed : A.d n (fiberSource f n z) = 0 := by
      have hfirst := congrArg (fiberSource f (n+1)) hz
      change fiberSource f (n+1) (fiberD f n z) = 0 at hfirst
      exact (fiberSource_d f n z).symm.trans hfirst
    let a : A.closed n := ⟨fiberSource f n z, hclosed⟩
    refine ⟨A.classOf n a, ?_⟩
    rw [f.onH_class]
    apply (B.class_eq_iff n (f.onClosed n a) b).mpr
    cases n with
    | zero =>
      have hsecond := congrArg Prod.snd hz
      change f.map 0 z = b.val at hsecond
      change f.map 0 z - b.val = 0
      exact sub_eq_zero.mpr hsecond
    | succ n =>
      refine ⟨z.2, ?_⟩
      have hsecond := congrArg Prod.snd hz
      change f.map (n+1) z.1 - B.d n z.2 = b.val at hsecond
      change B.d n z.2 = f.map (n+1) z.1 - b.val
      rw [← hsecond]
      abel

end CochainDescent

namespace CochainDescent
variable {A B : SmoothManifolds.MayerVietorisData.Cochain.{u}}
  (f : SmoothManifolds.MayerVietorisData.ChainMap A B)

/-- A proved degreewise chain equivalence to an exact nonnegative cochain
complex transfers the mapping-fiber criterion to its actual induced map. -/
theorem onH_bijective_of_mappingFiber_degreeEquiv
    (C : SmoothManifolds.MayerVietorisData.Cochain.{u})
    (e : ∀ n, (mappingFiber f).Obj n ≃ₗ[ℝ] C.Obj n)
    (he : ∀ n x, C.d n (e n x) = e (n+1) ((mappingFiber f).d n x))
    (hzero : Function.Injective (C.d 0))
    (hexact : ∀ n, Function.Exact (C.d n) (C.d (n+1))) :
    ∀ n, Function.Bijective (f.onH n) := by
  apply onH_bijective_of_mappingFiber_exact f
  · intro x y hxy
    apply (e 0).injective
    apply hzero
    rw [he, he, hxy]
  · intro n y
    constructor
    · intro hy
      have hcy : C.d (n+1) (e (n+1) y) = 0 := by rw [he, hy, map_zero]
      obtain ⟨x, hx⟩ := (hexact n (e (n+1) y)).mp hcy
      refine ⟨(e n).symm x, ?_⟩
      apply (e (n+1)).injective
      rw [← he, LinearEquiv.apply_symm_apply]
      exact hx
    · rintro ⟨x, rfl⟩
      exact (mappingFiber f).square n x

/-- Exactness including the initial term annihilates the actual quotient
cohomology groups of a nonnegative cochain complex. -/
theorem cohomology_subsingleton_of_exact
    (C : SmoothManifolds.MayerVietorisData.Cochain.{u}) (hzero : Function.Injective (C.d 0))
    (hexact : ∀ n, Function.Exact (C.d n) (C.d (n+1))) (n : ℕ) :
    Subsingleton (C.H n) := by
  have hall : ∀ x : C.H n, x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := C.class_surjective n x
    apply (C.class_zero_iff n a).mpr
    cases n with
    | zero =>
      have hda : C.d 0 a.val = 0 := a.property
      exact hzero (hda.trans (map_zero _).symm)
    | succ n =>
      exact (hexact n a.val).mp a.property
  exact ⟨fun x y => (hall x).trans (hall y).symm⟩

end CochainDescent

end CochainDescentAlgebra


section NestedOpenInclusions

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)

def openInclusionMap (U W : TopologicalSpace.Opens M) (hWU : W ≤ U) : W → U :=
  fun p => ⟨p.val, hWU p.property⟩

theorem openInclusionMap_smooth
    (U W : TopologicalSpace.Opens M) (hWU : W ≤ U) :
    MapData.IsSmoothMap (openSubmanifold S W) (openSubmanifold S U)
      (openInclusionMap U W hWU) := by
  intro p
  obtain ⟨c, hc, hcp⟩ := S.smoothStructure.property.1.1 p.val
  let e := c.subtypeRestr (s := W) ⟨p⟩
  let d := c.subtypeRestr (s := U) ⟨openInclusionMap U W hWU p⟩
  have he : e ∈ (openSubmanifold S W).smoothStructure.val :=
    openSubmanifold_restricted_atlas_subset S W ⟨⟨p⟩, c, hc, rfl⟩
  have hd : d ∈ (openSubmanifold S U).smoothStructure.val :=
    openSubmanifold_restricted_atlas_subset S U
      ⟨⟨openInclusionMap U W hWU p⟩, c, hc, rfl⟩
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    (openSubmanifold S W).smoothStructure.property.1
    (openSubmanifold S U).smoothStructure.property.1 (openInclusionMap U W hWU) p).mpr
  have hcont : Continuous (openInclusionMap U W hWU) := continuous_subtype_val.subtype_mk _
  refine ⟨hcont.continuousAt, e, he, d, hd, ?_, ?_, ?_⟩
  · simpa [e] using hcp
  · simpa [d, openInclusionMap] using hcp
  · exact SmoothManifolds.LocalCoordinateExtension.self _ (fun q : W => (c q.val).val) p

end NestedOpenInclusions

section SupportedSmoothColumns

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) (U : TopologicalSpace.Opens M)
  (T : AtlasData.SmoothManifold n a U)
  (hsub : MapData.openSubsetAtlas S.smoothStructure.val U U.isOpen ⊆ T.smoothStructure.val)
  (hinc : MapData.IsSmoothMap T S Subtype.val)

theorem openSmoothSimplexEquiv_map {q : ℕ} (σ : SmoothSimplex T q) :
    (openSmoothSimplexEquiv S U T hsub hinc q σ).val =
      smoothSimplexMap T S Subtype.val hinc σ := by
  apply (p104SimplexEquiv S q).injective
  rw [show p104SimplexEquiv S q (smoothSimplexMap T S Subtype.val hinc σ) =
    p104Simplex S (smoothSimplexMap T S Subtype.val hinc σ) from rfl, p104Simplex_map]
  exact congrArg Subtype.val ((supportedP104SimplexEquiv S U q).apply_symm_apply
    (openP104SimplexEquiv S U T hsub hinc q (p104SimplexEquiv T q σ)))

def supportedSmoothModule (q : ℕ) :
    Submodule ℝ (SingularChains.Chains ℝ (TopCat.of M) q) :=
  Finsupp.supported ℝ ℝ {τ | SmoothSingularComparison.IsSmoothSimplex S q τ ∧
    Set.range (SingularChains.simplexEquiv (TopCat.of M) q τ) ⊆ U}

def supportedSmoothBasisFlatten (q : ℕ) :
    SupportedSmoothSimplex S U q ≃
      {τ : SingularChains.Simplex (TopCat.of M) q //
        SmoothSingularComparison.IsSmoothSimplex S q τ ∧
          Set.range (SingularChains.simplexEquiv (TopCat.of M) q τ) ⊆ U} where
  toFun σ := ⟨σ.val.val, σ.val.property, σ.property⟩
  invFun σ := ⟨⟨σ.val, σ.property.1⟩, σ.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def supportedSmoothBasisEquiv (q : ℕ) :
    supportedSmoothModule S U q ≃ₗ[ℝ] (SupportedSmoothSimplex S U q →₀ ℝ) :=
  (Finsupp.supportedEquivFinsupp _).trans
    (Finsupp.domLCongr (supportedSmoothBasisFlatten S U q).symm)

def openSmoothChainEquiv (q : ℕ) :
    SmoothSingularComparison.smoothModule T q ≃ₗ[ℝ] supportedSmoothModule S U q :=
  (Finsupp.supportedEquivFinsupp _).trans
    ((Finsupp.domLCongr (openSmoothSimplexEquiv S U T hsub hinc q)).trans
      (supportedSmoothBasisEquiv S U q).symm)

def supportedSmoothGenerator {q : ℕ} (σ : SupportedSmoothSimplex S U q) :
    supportedSmoothModule S U q :=
  ⟨Finsupp.single σ.val.val 1, Finsupp.single_mem_supported ℝ 1 ⟨σ.val.property, σ.property⟩⟩

@[simp] theorem supportedSmoothBasisEquiv_generator {q : ℕ} (σ : SupportedSmoothSimplex S U q) :
    supportedSmoothBasisEquiv S U q (supportedSmoothGenerator S U σ) =
      Finsupp.single σ 1 := by
  let E : supportedSmoothModule S U q ≃ₗ[ℝ]
      ({τ : SingularChains.Simplex (TopCat.of M) q //
        SmoothSingularComparison.IsSmoothSimplex S q τ ∧
          Set.range (SingularChains.simplexEquiv (TopCat.of M) q τ) ⊆ U} →₀ ℝ) :=
    Finsupp.supportedEquivFinsupp _
  have he : E (supportedSmoothGenerator S U σ) =
      Finsupp.single (supportedSmoothBasisFlatten S U q σ) 1 := by
    apply E.symm.injective
    simp only [LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    exact (Finsupp.supportedEquivFinsupp_symm_single (R := ℝ) (M := ℝ) _
      (supportedSmoothBasisFlatten S U q σ) (1 : ℝ)).symm
  change (Finsupp.domLCongr (R := ℝ) (supportedSmoothBasisFlatten S U q).symm)
    (E (supportedSmoothGenerator S U σ)) = _
  rw [he, Finsupp.domLCongr_single, Equiv.symm_apply_apply]

@[simp] theorem openSmoothChainEquiv_generator {q : ℕ} (σ : SmoothSimplex T q) :
    openSmoothChainEquiv S U T hsub hinc q (smoothGenerator T σ) =
      supportedSmoothGenerator S U (openSmoothSimplexEquiv S U T hsub hinc q σ) := by
  apply (supportedSmoothBasisEquiv S U q).injective
  rw [supportedSmoothBasisEquiv_generator]
  have he : (Finsupp.supportedEquivFinsupp _) (smoothGenerator T σ) = Finsupp.single σ 1 := by
    apply (Finsupp.supportedEquivFinsupp (R := ℝ) (M := ℝ)
      {τ | SmoothSingularComparison.IsSmoothSimplex T q τ}).symm.injective
    simp only [LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    exact (Finsupp.supportedEquivFinsupp_symm_single (R := ℝ) _ σ 1).symm
  change (supportedSmoothBasisEquiv S U q)
    ((supportedSmoothBasisEquiv S U q).symm
      (Finsupp.domLCongr (openSmoothSimplexEquiv S U T hsub hinc q)
        (Finsupp.supportedEquivFinsupp _ (smoothGenerator T σ)))) = _
  rw [LinearEquiv.apply_symm_apply]
  change (Finsupp.domLCongr (openSmoothSimplexEquiv S U T hsub hinc q))
    ((Finsupp.supportedEquivFinsupp {τ | SmoothSingularComparison.IsSmoothSimplex T q τ})
      (smoothGenerator T σ)) = _
  rw [he, Finsupp.domLCongr_single]

theorem openSmoothChainEquiv_generator_underlying {q : ℕ} (σ : SmoothSimplex T q) :
    (openSmoothChainEquiv S U T hsub hinc q (smoothGenerator T σ)).val =
      ((SmoothSingularComparison.smoothChainMap T S Subtype.val hinc).f q
        (smoothGenerator T σ)).val := by
  rw [openSmoothChainEquiv_generator, smoothChainMap_generator]
  change Finsupp.single (openSmoothSimplexEquiv S U T hsub hinc q σ).val.val 1 =
    Finsupp.single (smoothSimplexMap T S Subtype.val hinc σ).val 1
  rw [openSmoothSimplexEquiv_map]
theorem openSmoothChainEquiv_underlying {q : ℕ}
    (z : SmoothSingularComparison.smoothModule T q) :
    (openSmoothChainEquiv S U T hsub hinc q z).val =
      ((SmoothSingularComparison.smoothChainMap T S Subtype.val hinc).f q z).val := by
  let f : SmoothSingularComparison.smoothModule T q →ₗ[ℝ]
      SingularChains.Chains ℝ (TopCat.of M) q :=
    (supportedSmoothModule S U q).subtype.comp (openSmoothChainEquiv S U T hsub hinc q).toLinearMap
  let g : SmoothSingularComparison.smoothModule T q →ₗ[ℝ]
      SingularChains.Chains ℝ (TopCat.of M) q :=
    (SmoothSingularComparison.smoothModule S q).subtype.comp
      ((SmoothSingularComparison.smoothChainMap T S Subtype.val hinc).f q).hom
  change f z = g z
  let E : SmoothSingularComparison.smoothModule T q ≃ₗ[ℝ] (SmoothSimplex T q →₀ ℝ) :=
    Finsupp.supportedEquivFinsupp _
  obtain ⟨d, rfl⟩ := E.symm.surjective z
  induction d using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add d e hd he => simp only [map_add, hd, he]
  | single σ r =>
    have hsingle : E.symm (Finsupp.single σ r) = r • smoothGenerator T σ := by
      apply Subtype.ext
      change ((Finsupp.supportedEquivFinsupp _).symm (Finsupp.single σ r)).val =
        r • (Finsupp.single σ.val (1 : ℝ))
      rw [Finsupp.supportedEquivFinsupp_symm_single]
      simp
    rw [hsingle, map_smul, map_smul]
    exact congrArg (r • ·) (openSmoothChainEquiv_generator_underlying S U T hsub hinc σ)

def supportedSmoothFace {q : ℕ} (σ : SupportedSmoothSimplex S U (q+1))
    (j : Fin (q+2)) : SupportedSmoothSimplex S U q :=
  ⟨⟨SingularChains.face j σ.val.val,
      SmoothSingularComparison.isSmoothSimplex_face S σ.val.property j⟩, by
    rintro y ⟨x, rfl⟩
    rw [P202.SingularChains.simplexEquiv_face]
    exact σ.property ⟨SingularChains.faceInclusion j x, rfl⟩⟩

theorem boundary_mem_supportedSmoothModule (q : ℕ)
    (z : SingularChains.Chains ℝ (TopCat.of M) (q+1))
    (hz : z ∈ supportedSmoothModule S U (q+1)) :
    SingularChains.boundary ℝ ℝ (TopCat.of M) q z ∈ supportedSmoothModule S U q := by
  classical
  change ((AlgebraicTopology.AlternatingFaceMapComplex.obj
    (SingularChains.simplicialChains ℝ ℝ (TopCat.of M))).d (q+1) q).hom z ∈ _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ j : Fin (q+2), (-1 : ℤ)^j.val •
    Finsupp.mapDomain ((TopCat.toSSet.obj (TopCat.of M)).δ j) z) ∈ supportedSmoothModule S U q
  apply Submodule.sum_mem
  intro j _
  apply (supportedSmoothModule S U q).toAddSubgroup.zsmul_mem
  intro τ hτ
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hτ)
  exact ⟨(supportedSmoothFace S U ⟨⟨σ, (hz hσ).1⟩, (hz hσ).2⟩ j).val.property,
    (supportedSmoothFace S U ⟨⟨σ, (hz hσ).1⟩, (hz hσ).2⟩ j).property⟩
def supportedSmoothBoundary (q : ℕ) :
    supportedSmoothModule S U (q+1) →ₗ[ℝ] supportedSmoothModule S U q :=
  ((SingularChains.boundary ℝ ℝ (TopCat.of M) q).comp
    (supportedSmoothModule S U (q+1)).subtype).codRestrict (supportedSmoothModule S U q)
      (fun z => boundary_mem_supportedSmoothModule S U q z.val z.property)

theorem openSmoothChainEquiv_boundary (q : ℕ)
    (z : SmoothSingularComparison.smoothModule T (q+1)) :
    openSmoothChainEquiv S U T hsub hinc q
        ((SmoothSingularComparison.smoothComplex T).d (q+1) q z) =
      supportedSmoothBoundary S U q (openSmoothChainEquiv S U T hsub hinc (q+1) z) := by
  apply Subtype.ext
  change (openSmoothChainEquiv S U T hsub hinc q
      ((SmoothSingularComparison.smoothComplex T).d (q+1) q z)).val =
    SingularChains.boundary ℝ ℝ (TopCat.of M) q
      (openSmoothChainEquiv S U T hsub hinc (q+1) z).val
  rw [openSmoothChainEquiv_underlying, openSmoothChainEquiv_underlying]
  have hc := congrArg (fun f => (f.hom z).val)
    ((SmoothSingularComparison.smoothChainMap T S Subtype.val hinc).comm (q+1) q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
  simpa only [SmoothSingularComparison.smoothComplex, ChainComplex.of_d,
    ModuleCat.hom_ofHom, LinearMap.codRestrict_apply, LinearMap.comp_apply] using! hc.symm


end SupportedSmoothColumns

end P202.DeRhamComparison


namespace P202.DeRhamComparison.ConeBridge
open SmoothManifolds.MayerVietorisData
open P202.CochainCoverDescent.ConeAlgebra
universe u v
variable {E : Type u} [AddCommGroup E] [Module ℝ E]
  (A : Cochain.{v}) (C : Complex E)
  (e : ∀ q, A.Obj q ≃ₗ[ℝ] C.space (q:ℤ))
  (hd : ∀ (q : ℕ) (x : A.Obj q), C.differential (q:ℤ) (e q x).val = (e (q+1) (A.d q x)).val)

def closedEquiv (q : ℕ) : A.closed q ≃ₗ[ℝ] C.cycles (q:ℤ) where
  toFun x := ⟨(e q x.val).val, (e q x.val).property, by
    change C.differential (q:ℤ) (e q x.val).val = 0
    rw [hd, show A.d q x.val = 0 from x.property, map_zero]
    rfl⟩
  invFun x := ⟨(e q).symm ⟨x.val,x.property.1⟩, by
    apply (e (q+1)).injective
    apply Subtype.ext
    rw [map_zero, ← hd]
    simp only [LinearEquiv.apply_symm_apply]
    change C.differential (q:ℤ) x.val = 0
    exact x.property.2⟩
  left_inv x := by apply Subtype.ext; exact (e q).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    change (e q ((e q).symm ⟨x.val,x.property.1⟩)).val = x.val
    exact congrArg (fun z : C.space (q:ℤ) => z.val) ((e q).apply_symm_apply ⟨x.val,x.property.1⟩)
  map_add' x y := by
    apply Subtype.ext
    change (e q (x.val+y.val)).val = (e q x.val).val + (e q y.val).val
    exact congrArg (fun z : C.space (q:ℤ) => z.val) ((e q).map_add x.val y.val)
  map_smul' r x := by
    apply Subtype.ext
    change (e q (r • x.val)).val = r • (e q x.val).val
    exact congrArg (fun z : C.space (q:ℤ) => z.val) ((e q).map_smul r x.val)

variable (hneg : C.space (-1) = ⊥)
include hneg in
theorem boundaries_iff (q : ℕ) (x : A.closed q) :
    closedEquiv A C e hd q x ∈ C.boundaries (q:ℤ) ↔ x ∈ A.boundaries q := by
  rw [C.boundary_mem_iff]
  cases q with
  | zero =>
    constructor
    · rintro ⟨y,hy,he⟩
      have hy0 : y=0 := by simpa only [Int.natCast_zero,zero_sub,hneg,Submodule.mem_bot] using hy
      have hx0 : x.val=0 := by
        apply (e 0).injective
        apply Subtype.ext
        rw [map_zero]
        exact he.symm.trans (hy0 ▸ map_zero _)
      exact hx0
    · intro hx
      have hx0 : x.val=0 := hx
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero]
      change 0 = (e 0 x.val).val
      rw [hx0,map_zero]
      rfl
  | succ q =>
    have hcast : (↑(q+1):ℤ)-1=(q:ℤ) := by omega
    simp only [hcast]
    constructor
    · rintro ⟨y,hy,he⟩
      refine ⟨(e q).symm ⟨y,hy⟩, ?_⟩
      apply (e (q+1)).injective
      apply Subtype.ext
      rw [← hd]
      simp only [LinearEquiv.apply_symm_apply]
      change C.differential (q:ℤ) y = (e (q+1) x.val).val
      exact he
    · rintro ⟨y,hy⟩
      refine ⟨(e q y).val,(e q y).property,?_⟩
      rw [hd,hy]
      rfl

def cohomologyEquiv (q : ℕ) : A.H q ≃ₗ[ℝ] C.Cohomology (q:ℤ) :=
  Submodule.Quotient.equiv (A.boundaries q) (C.boundaries (q:ℤ))
    (closedEquiv A C e hd q) (by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact (boundaries_iff A C e hd hneg q y).mpr hy
      · intro hx
        refine ⟨(closedEquiv A C e hd q).symm x,?_,by simp⟩
        apply (boundaries_iff A C e hd hneg q _).mp
        simpa using hx)

@[simp] theorem cohomologyEquiv_class (q : ℕ) (x : A.closed q) :
    cohomologyEquiv A C e hd hneg q (A.classOf q x) =
      (C.boundaries (q:ℤ)).mkQ (closedEquiv A C e hd q x) := rfl

end P202.DeRhamComparison.ConeBridge


namespace P202.DeRhamComparison
universe u v

open P202Specs.CochainCoverDescent

/-- The geometric P104 basis identification preserves the actual signed
boundary of every finite smooth chain. -/
theorem p104ChainEquiv_boundary
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (q : ℕ)
    (z : SmoothSingularComparison.smoothModule S (q+1)) :
    p104ChainEquiv S q ((SmoothSingularComparison.smoothComplex S).d (q+1) q z) =
      SmoothSingularData.boundary S q (p104ChainEquiv S (q+1) z) := by
  let f : SmoothSingularComparison.smoothModule S (q+1) →ₗ[ℝ] SmoothSingularData.Chains S q :=
    (p104ChainEquiv S q).toLinearMap.comp ((SmoothSingularComparison.smoothComplex S).d (q+1) q).hom
  let g : SmoothSingularComparison.smoothModule S (q+1) →ₗ[ℝ] SmoothSingularData.Chains S q :=
    (SmoothSingularData.boundary S q).comp (p104ChainEquiv S (q+1)).toLinearMap
  let E : SmoothSingularComparison.smoothModule S (q+1) ≃ₗ[ℝ] (SmoothSimplex S (q+1) →₀ ℝ) :=
    Finsupp.supportedEquivFinsupp _
  have hgen (σ : SmoothSimplex S (q+1)) : f (smoothGenerator S σ) = g (smoothGenerator S σ) := by
    change p104ChainEquiv S q ((SmoothSingularComparison.smoothComplex S).d (q+1) q (smoothGenerator S σ)) =
      SmoothSingularData.boundary S q (p104ChainEquiv S (q+1) (smoothGenerator S σ))
    rw [smoothBoundary_generator, map_sum, p104ChainEquiv_generator, SmoothSingular.boundary_single]
    simp only [one_smul, map_zsmul]
    apply Finset.sum_congr rfl
    intro j _
    rw [p104ChainEquiv_generator, p104Simplex_face]
    simp [SmoothSingular.restrict, ← Int.cast_smul_eq_zsmul ℝ]

  have he : f.comp E.symm.toLinearMap = g.comp E.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro σ r
    have hsingle : E.symm (Finsupp.single σ r) = r • smoothGenerator S σ := by
      apply Subtype.ext
      change ((Finsupp.supportedEquivFinsupp _).symm (Finsupp.single σ r)).val =
        r • (Finsupp.single σ.val (1 : ℝ))
      rw [Finsupp.supportedEquivFinsupp_symm_single]
      simp
    change f (E.symm (Finsupp.single σ r)) = g (E.symm (Finsupp.single σ r))
    rw [hsingle, map_smul, map_smul, hgen]
  have hz := LinearMap.congr_fun he (E z)
  change f (E.symm (E z)) = g (E.symm (E z)) at hz
  simpa only [LinearEquiv.symm_apply_apply, f, g, LinearMap.comp_apply] using! hz

section IntersectionColumns
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {ι : Type v}
  (U : SmallChainHomology.OpenCover (TopCat.of M) ι)

def coverOpens (i : ι) : TopologicalSpace.Opens M := ⟨U.sets i, U.isOpen i⟩

def intersectionSupportedEquiv (q k : ℕ) (t : Fin (k+1) → ι) :
    supportedSmoothModule S (tupleOpen (coverOpens U) t) q ≃ₗ[ℝ]
      intersectionChainModule S U q (k+1) t :=
  LinearEquiv.ofEq _ _ (by
    ext z
    constructor
    · intro hz σ hσ
      have h := hz hσ
      refine ⟨h.1, ⟨t 0, ?_⟩, ?_⟩
      · intro y hy
        exact h.2 hy 0
      · intro j y hy
        exact h.2 hy j
    · intro hz σ hσ
      have h := hz hσ
      refine ⟨h.1, ?_⟩
      intro y hy j
      exact h.2.2 j hy)

def openIntersectionChainEquiv (q k : ℕ) (t : Fin (k+1) → ι) :
    SmoothSingularComparison.smoothModule (openSubmanifold S (tupleOpen (coverOpens U) t)) q ≃ₗ[ℝ]
      intersectionChainModule S U q (k+1) t :=
  (openSmoothChainEquiv S (tupleOpen (coverOpens U) t) _
    (openSubmanifold_restricted_atlas_subset S _) (openSubmanifold_inclusion_smooth S _) q).trans
      (intersectionSupportedEquiv S U q k t)

@[simp] theorem openIntersectionChainEquiv_boundary (q k : ℕ) (t : Fin (k+1) → ι)
    (z : SmoothSingularComparison.smoothModule (openSubmanifold S (tupleOpen (coverOpens U) t)) (q+1)) :
    openIntersectionChainEquiv S U q k t
      ((SmoothSingularComparison.smoothComplex _).d (q+1) q z) =
        intersectionBoundary S U q (k+1) t (openIntersectionChainEquiv S U (q+1) k t z) := by
  apply Subtype.ext
  change ((openSmoothChainEquiv S (tupleOpen (coverOpens U) t) _
      (openSubmanifold_restricted_atlas_subset S _) (openSubmanifold_inclusion_smooth S _) q)
        ((SmoothSingularComparison.smoothComplex _).d (q+1) q z)).val =
    SingularChains.boundary ℝ ℝ (TopCat.of M) q
      ((openSmoothChainEquiv S (tupleOpen (coverOpens U) t) _
        (openSubmanifold_restricted_atlas_subset S _) (openSubmanifold_inclusion_smooth S _) (q+1)) z).val
  exact congrArg Subtype.val (openSmoothChainEquiv_boundary S (tupleOpen (coverOpens U) t) _
    (openSubmanifold_restricted_atlas_subset S _) (openSubmanifold_inclusion_smooth S _) q z)

/-- Intrinsic smooth chains on an open intersection are exactly the literal
finite chains on its ambient smooth simplex basis. -/
def openIntersectionFreeChainEquiv (q k : ℕ) (t : Fin (k+1) → ι) :
    SmoothSingularComparison.smoothModule (openSubmanifold S (tupleOpen (coverOpens U) t)) q ≃ₗ[ℝ]
      (IntersectionSimplex S U q (k+1) t →₀ ℝ) :=
  (openIntersectionChainEquiv S U q k t).trans (intersectionChainBasisEquiv S U q (k+1) t)

/-- The column bridge preserves the genuine signed singular boundary. -/
theorem openIntersectionFreeChainEquiv_boundary (q k : ℕ) (t : Fin (k+1) → ι)
    (z : SmoothSingularComparison.smoothModule (openSubmanifold S (tupleOpen (coverOpens U) t)) (q+1)) :
    openIntersectionFreeChainEquiv S U q k t
      ((SmoothSingularComparison.smoothComplex _).d (q+1) q z) =
    (intersectionChainBasisEquiv S U q (k+1) t)
      (intersectionBoundary S U q (k+1) t
        ((intersectionChainBasisEquiv S U (q+1) (k+1) t).symm
          (openIntersectionFreeChainEquiv S U (q+1) k t z))) := by
  change _ = (intersectionChainBasisEquiv S U q (k+1) t)
    (intersectionBoundary S U q (k+1) t
      ((intersectionChainBasisEquiv S U (q+1) (k+1) t).symm
        ((intersectionChainBasisEquiv S U (q+1) (k+1) t)
          (openIntersectionChainEquiv S U (q+1) k t z))))
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (intersectionChainBasisEquiv S U q (k+1) t)
    (openIntersectionChainEquiv_boundary S U q k t z)

/-- Every positive-length literal intersection column has the actual
intrinsic smooth-chain complex, including the empty open set. -/
def openIntersectionChainIso (k : ℕ) (t : Fin (k+1) → ι) :
    SmoothSingularComparison.smoothComplex (openSubmanifold S (tupleOpen (coverOpens U) t)) ≅
      intersectionComplex S U (k+1) t :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (openIntersectionChainEquiv S U q k t).toModuleIso)
    (by
      intro i j hij
      obtain rfl : j+1=i := by simpa only [ComplexShape.down_Rel] using hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
        ModuleCat.hom_ofHom, intersectionComplex, ChainComplex.of_d] using!
          (openIntersectionChainEquiv_boundary S U j k t z).symm)

/-- On each nonnegative degree, a cochain is pulled back by the actual
open-intersection smooth-chain identification. -/
def intersectionCochainEquiv (q k : ℕ) (t : Fin (k+1) → ι) :
    ((IntersectionSimplex S U q (k+1) t →₀ ℝ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      (SmoothSingularComparison.smoothModule (openSubmanifold S (tupleOpen (coverOpens U) t)) q →ₗ[ℝ] ℝ) :=
  LinearEquiv.congrLeft ℝ ℝ (openIntersectionFreeChainEquiv S U q k t).symm

/-- The full algebraic dual identification commutes with vertical coboundary. -/
theorem intersectionCochainEquiv_d (q k : ℕ) (f : IntersectionCochainRow S U q (k+1))
    (t : Fin (k+1) → ι)
    (z : SmoothSingularComparison.smoothModule (openSubmanifold S (tupleOpen (coverOpens U) t)) (q+1)) :
    intersectionCochainEquiv S U (q+1) k t (intersectionV S U q (k+1) f t) z =
      intersectionCochainEquiv S U q k t (f t)
        ((SmoothSingularComparison.smoothComplex _).d (q+1) q z) := by
  change f t ((intersectionChainBasisEquiv S U q (k+1) t)
    (intersectionBoundary S U q (k+1) t
      ((intersectionChainBasisEquiv S U (q+1) (k+1) t).symm
        (openIntersectionFreeChainEquiv S U (q+1) k t z)))) =
    f t (openIntersectionFreeChainEquiv S U q k t
      ((SmoothSingularComparison.smoothComplex _).d (q+1) q z))
  rw [openIntersectionFreeChainEquiv_boundary]

/-- Extension by zero and full algebraic duality preserve the actual
intrinsic smooth-column isomorphism. -/
def openIntersectionCochainIso (k : ℕ) (t : Fin (k+1) → ι) :
    SmoothSingularComparison.smoothCochains (openSubmanifold S (tupleOpen (coverOpens U) t)) ≅
      (P202Specs.CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).obj
        (op ((intersectionComplex S U (k+1) t).extend (SingularChains.degreeEmbedding 0))) :=
  (P202Specs.CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).mapIso
    ((((SingularChains.degreeEmbedding 0).extendFunctor (ModuleCat ℝ)).mapIso
      (openIntersectionChainIso S U k t)).symm.op)

/-- The literal Čech column is the unrestricted product of full intrinsic
open-intersection smooth cochains, degree by degree. -/
def intersectionCochainRowEquiv (q k : ℕ) :
    IntersectionCochainRow S U q (k+1) ≃ₗ[ℝ]
      ((t : Fin (k+1) → ι) →
        (SmoothSingularComparison.smoothModule (openSubmanifold S (tupleOpen (coverOpens U) t)) q →ₗ[ℝ] ℝ)) :=
  LinearEquiv.piCongrRight (intersectionCochainEquiv S U q k)

/-- Direct intrinsic P104 cochain coordinates for the literal intersection
column. No finiteness condition is imposed on the dual. -/
def intersectionP104CochainEquiv (q k : ℕ) (t : Fin (k+1) → ι) :
    ((IntersectionSimplex S U q (k+1) t →₀ ℝ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      SmoothSingularData.Cochains (openSubmanifold S (tupleOpen (coverOpens U) t)) q :=
  (intersectionCochainEquiv S U q k t).trans
    (LinearEquiv.congrLeft ℝ ℝ (p104ChainEquiv (openSubmanifold S (tupleOpen (coverOpens U) t)) q))

theorem intersectionP104CochainEquiv_d (q k : ℕ) (f : IntersectionCochainRow S U q (k+1))
    (t : Fin (k+1) → ι) :
    intersectionP104CochainEquiv S U (q+1) k t (intersectionV S U q (k+1) f t) =
      SmoothSingularData.coboundary (openSubmanifold S (tupleOpen (coverOpens U) t)) q
        (intersectionP104CochainEquiv S U q k t (f t)) := by
  apply LinearMap.ext
  intro z
  change intersectionCochainEquiv S U (q+1) k t (intersectionV S U q (k+1) f t)
    ((p104ChainEquiv _ (q+1)).symm z) =
    intersectionCochainEquiv S U q k t (f t)
      ((p104ChainEquiv _ q).symm (SmoothSingularData.boundary _ q z))
  rw [intersectionCochainEquiv_d]
  congr 1
  apply (p104ChainEquiv _ q).injective
  rw [p104ChainEquiv_boundary, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Product coordinates for all intrinsic P104 cochains on the intersections. -/
def intersectionP104CochainRowEquiv (q k : ℕ) :
    IntersectionCochainRow S U q (k+1) ≃ₗ[ℝ]
      ((t : Fin (k+1) → ι) →
        SmoothSingularData.Cochains (openSubmanifold S (tupleOpen (coverOpens U) t)) q) :=
  LinearEquiv.piCongrRight (intersectionP104CochainEquiv S U q k)

end IntersectionColumns
end P202.DeRhamComparison


namespace P202.DeRhamComparison.CoverAssembly
open P202.CochainCoverDescent.TotalAlgebra
open P202.CochainCoverDescent.ConeAlgebra
universe u v
variable {E : Type u} [AddCommGroup E] [Module ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F]
  {A : Data E} {B : Data F} (f : DataMap A B)

def augmentationSourceMap : Map A.augmentationComplex B.augmentationComplex where
  map _ := f.linear
  map_mem n x hx := by
    change x ∈ (if 0 ≤ n then A.space 0 n.toNat else ⊥) at hx
    change f.linear x ∈ (if 0 ≤ n then B.space 0 n.toNat else ⊥)
    by_cases hn : 0 ≤ n
    · rw [if_pos hn] at hx ⊢
      exact f.map_mem 0 n.toNat x hx
    · rw [if_neg hn] at hx ⊢
      have hx0 : x=0 := hx
      rw [hx0,map_zero]
      exact Submodule.zero_mem _
  commute n x := by
    change (if 0 ≤ n then -B.vertical else 0) (f.linear x) =
      f.linear ((if 0 ≤ n then -A.vertical else 0) x)
    by_cases hn : 0 ≤ n
    · simp only [if_pos hn,LinearMap.neg_apply,f.vertical_commute,map_neg]
    · simp only [if_neg hn,LinearMap.zero_apply,map_zero]

def positiveTotalMap : Map A.positiveComplex B.positiveComplex where
  map _ := {
    toFun x q := f.linear (x q)
    map_add' x y := by funext q; exact map_add _ _ _
    map_smul' r x := by funext q; exact map_smul _ _ _ }
  map_mem n x hx := by
    constructor
    · intro q
      exact f.map_mem _ _ _ (hx.1 q)
    · intro q hq
      change f.linear (x q)=0
      rw [hx.2 q hq,map_zero]
  commute n x := by
    funext q
    cases q <;> simp [Data.positiveComplex,Data.differential,
      f.horizontal_commute,f.vertical_commute,map_add,map_smul]

theorem augmentation_naturality (n : ℤ) (x : E) :
    B.augmentationMap.map n ((augmentationSourceMap f).map n x) =
      (positiveTotalMap f).map n (A.augmentationMap.map n x) := by
  change B.augmentationMapLinear n (f.linear x) =
    fun q => f.linear (A.augmentationMapLinear n x q)
  by_cases hn : 0 ≤ n
  · rw [B.augmentationMapLinear_nonneg n hn,A.augmentationMapLinear_nonneg n hn]
    funext q
    by_cases hq : n.toNat=q
    · subst q
      simp only [Pi.single_eq_same,f.horizontal_commute]
    · simp [Pi.single_apply,hq,Ne.symm hq]
  · simp only [Data.augmentationMapLinear,if_neg hn,LinearMap.zero_apply]
    funext q
    exact (map_zero f.linear).symm

theorem augmentation_cohomology_naturality (n : ℤ)
    (x : A.augmentationComplex.Cohomology n) :
    B.augmentationMap.cohomologyMap n ((augmentationSourceMap f).cohomologyMap n x) =
      (positiveTotalMap f).cohomologyMap n (A.augmentationMap.cohomologyMap n x) := by
  obtain ⟨x,rfl⟩ := (A.augmentationComplex.boundaries n).mkQ_surjective x
  change (B.positiveComplex.boundaries n).mkQ
      (B.augmentationMap.cycleMap n ((augmentationSourceMap f).cycleMap n x)) =
    (B.positiveComplex.boundaries n).mkQ
      ((positiveTotalMap f).cycleMap n (A.augmentationMap.cycleMap n x))
  congr 1
  apply Subtype.ext
  exact augmentation_naturality f n x.val

theorem augmentationSourceMap_bijective (n : ℤ)
    (hA : Function.Bijective (A.augmentationMap.cohomologyMap n))
    (hB : Function.Bijective (B.augmentationMap.cohomologyMap n))
    (hT : Function.Bijective ((positiveTotalMap f).cohomologyMap n)) :
    Function.Bijective ((augmentationSourceMap f).cohomologyMap n) := by
  constructor
  · intro x y hxy
    apply hA.1
    apply hT.1
    rw [← augmentation_cohomology_naturality, ← augmentation_cohomology_naturality,hxy]
  · intro y
    obtain ⟨z,hz⟩ := hT.2 (B.augmentationMap.cohomologyMap n y)
    obtain ⟨x,hx⟩ := hA.2 z
    refine ⟨x,hB.1 ?_⟩
    rw [augmentation_cohomology_naturality,hx,hz]

theorem cohomologyMap_bijective_congr
    {C C' : Complex E} {D D' : Complex F} (hC : C=C') (hD : D=D')
    (f : Map C D) (g : Map C' D')
    (hmap : ∀ n x, f.map n x=g.map n x) (n : ℤ) :
    Function.Bijective (f.cohomologyMap n) ↔ Function.Bijective (g.cohomologyMap n) := by
  subst C'
  subst D'
  have hlin : f.map=g.map := by
    funext n
    ext x
    exact hmap n x
  have heq : f=g := by
    cases f
    cases g
    cases hlin
    rfl
  rw [heq]

theorem positiveTotalMap_bijective_of_columns
    (htotal : P202Specs.CochainCoverDescent.columnTotalComparison_type.{u,v})
    (hcol : ∀ p : ℕ, ∀ n : ℤ,
      Function.Bijective ((f.positiveMap.columnMap (p:ℤ)).cohomologyMap n)) (n : ℤ) :
    Function.Bijective ((positiveTotalMap f).cohomologyMap n) := by
  apply (cohomologyMap_bijective_congr A.positiveData_totalComplex
    B.positiveData_totalComplex f.positiveMap.totalMap (positiveTotalMap f)
    (fun _ _ => rfl) n).mp
  exact htotal E F A.positiveData B.positiveData f.positiveMap hcol n

theorem augmentationSourceMap_bijective_of_columns
    (htotal : P202Specs.CochainCoverDescent.columnTotalComparison_type.{u,v})
    (hA : ∀ n : ℤ, Function.Bijective (A.augmentationMap.cohomologyMap n))
    (hB : ∀ n : ℤ, Function.Bijective (B.augmentationMap.cohomologyMap n))
    (hcol : ∀ p : ℕ, ∀ n : ℤ,
      Function.Bijective ((f.positiveMap.columnMap (p:ℤ)).cohomologyMap n)) (n : ℤ) :
    Function.Bijective ((augmentationSourceMap f).cohomologyMap n) :=
  augmentationSourceMap_bijective f n (hA n) (hB n)
    (positiveTotalMap_bijective_of_columns f htotal hcol n)

end P202.DeRhamComparison.CoverAssembly


set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open Set TopologicalSpace
namespace P202.DeRhamComparison
universe u v
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Every open subset of a normed real vector space has a convex open cover.
Arbitrary intersections of the chosen convex sets remain convex. -/
def ConvexCoordinateIndex (U : Opens V) :=
  {B : Opens V // B ≤ U ∧ Convex ℝ (B : Set V)}

variable {X : Type u} [TopologicalSpace X]

def convexCoordinateOpen (U : Opens V) (h : X ≃ₜ U)
    (i : ConvexCoordinateIndex U) : Opens X :=
  ⟨{x | (h x).val ∈ i.val},
    i.val.isOpen.preimage (continuous_subtype_val.comp h.continuous)⟩

def convexCoordinateCover (U : Opens V) (h : X ≃ₜ U) :
    P202Specs.SmallChainHomology.OpenCover (TopCat.of X) (ConvexCoordinateIndex U) where
  sets i := convexCoordinateOpen U h i
  isOpen i := (convexCoordinateOpen U h i).isOpen
  covers x := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp U.isOpen (h x).val (h x).property
    refine ⟨⟨⟨Metric.ball (h x).val ε, Metric.isOpen_ball⟩, hball, convex_ball _ _⟩, ?_⟩
    exact Metric.mem_ball_self hε

def convexCoordinateTuple (U : Opens V) {k : ℕ}
    (t : Fin (k+1) → ConvexCoordinateIndex U) : Opens V :=
  P202Specs.CochainCoverDescent.tupleOpen (fun i => i.val) t

theorem convexCoordinateTuple_convex (U : Opens V) {k : ℕ}
    (t : Fin (k+1) → ConvexCoordinateIndex U) :
    Convex ℝ (convexCoordinateTuple U t : Set V) := by
  change Convex ℝ {x | ∀ j, x ∈ (t j).val}
  intro x hx y hy a b ha hb hab j
  exact (t j).property.2 (hx j) (hy j) ha hb hab

def convexCoordinateTupleHomeomorph (U : Opens V) (h : X ≃ₜ U) {k : ℕ}
    (t : Fin (k+1) → ConvexCoordinateIndex U) :
    (P202Specs.CochainCoverDescent.tupleOpen (convexCoordinateOpen U h) t) ≃ₜ
      convexCoordinateTuple U t where
  toFun x := ⟨(h x.val).val, x.property⟩
  invFun x := ⟨h.symm ⟨x.val, (t 0).property.1 (x.property 0)⟩, by
    change ∀ j, (h (h.symm _)).val ∈ (t j).val
    simpa only [h.apply_symm_apply] using (show ∀ j, x.val ∈ (t j).val from x.property)⟩
  left_inv x := by apply Subtype.ext; exact h.symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    change (h (h.symm _)).val = x.val
    rw [h.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (h.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply h.symm.continuous.comp
    apply Continuous.subtype_mk
    exact continuous_subtype_val

theorem convexCoordinateTuple_contractible (U : Opens V) (h : X ≃ₜ U) {k : ℕ}
    (t : Fin (k+1) → ConvexCoordinateIndex U)
    [Nonempty (P202Specs.CochainCoverDescent.tupleOpen (convexCoordinateOpen U h) t)] :
    ContractibleSpace (P202Specs.CochainCoverDescent.tupleOpen (convexCoordinateOpen U h) t) := by
  let e := convexCoordinateTupleHomeomorph U h t
  have hne : Nonempty (convexCoordinateTuple U t) :=
    Nonempty.map e (inferInstance : Nonempty _)
  letI := (convexCoordinateTuple_convex U t).contractibleSpace (Set.nonempty_coe_sort.mp hne)
  exact e.contractibleSpace

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
variable {n : ℕ} {M : Type u} [TopologicalSpace M]

def boundarylessChart (c : SmoothManifolds.ModelData.ModelChart n .euclidean M) :
    OpenPartialHomeomorph M (SmoothManifolds.ModelData.Euclidean n) :=
  c.trans (show SmoothManifolds.ModelData.ModelSpace n .euclidean ≃ₜ SmoothManifolds.ModelData.Euclidean n from
    Homeomorph.Set.univ (SmoothManifolds.ModelData.Euclidean n)).toOpenPartialHomeomorph

@[simp] theorem boundarylessChart_source (c : SmoothManifolds.ModelData.ModelChart n .euclidean M) :
    (boundarylessChart c).source = c.source := by
  simp [boundarylessChart, OpenPartialHomeomorph.trans_source]

def chartCoordinateOpen (c : SmoothManifolds.ModelData.ModelChart n .euclidean M) (U : Opens M)
    (hU : (U : Set M) ⊆ c.source) : Opens (SmoothManifolds.ModelData.Euclidean n) :=
  ⟨boundarylessChart c '' (U : Set M),
    (boundarylessChart c).isOpen_image_of_subset_source U.isOpen (by simpa using hU)⟩

def chartCoordinateHomeomorph (c : SmoothManifolds.ModelData.ModelChart n .euclidean M) (U : Opens M)
    (hU : (U : Set M) ⊆ c.source) : U ≃ₜ chartCoordinateOpen c U hU :=
  (boundarylessChart c).homeomorphOfImageSubsetSource (by simpa using hU) rfl

def ChartCoverIndex (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M) :=
  {c : SmoothManifolds.ModelData.ModelChart n .euclidean M // c ∈ S.smoothStructure.val}

def chartCoverOpen (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M) (i : ChartCoverIndex S) : Opens M :=
  ⟨i.val.source, i.val.open_source⟩

def chartCover (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M) :
    P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ChartCoverIndex S) where
  sets i := chartCoverOpen S i
  isOpen i := (chartCoverOpen S i).isOpen
  covers x := by
    obtain ⟨c, hc, hx⟩ := S.smoothStructure.property.1.1 x
    exact ⟨⟨c, hc⟩, hx⟩

def chartTupleCoordinateOpen (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M) {k : ℕ}
    (t : Fin (k+1) → ChartCoverIndex S) : Opens (SmoothManifolds.ModelData.Euclidean n) :=
  chartCoordinateOpen (t 0).val
    (P202Specs.CochainCoverDescent.tupleOpen (chartCoverOpen S) t) (fun _ hx => hx 0)

def chartTupleCoordinateHomeomorph (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M) {k : ℕ}
    (t : Fin (k+1) → ChartCoverIndex S) :
    (P202Specs.CochainCoverDescent.tupleOpen (chartCoverOpen S) t) ≃ₜ
      chartTupleCoordinateOpen S t :=
  chartCoordinateHomeomorph (t 0).val
    (P202Specs.CochainCoverDescent.tupleOpen (chartCoverOpen S) t) (fun _ hx => hx 0)

open SmoothManifolds.CovectorData SmoothManifolds.BundleOperationsData
  SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open P202Specs.DeRhamComparison

/-- The local comparison property is about all actual intrinsic realizations. -/
def ManifoldIntegrationComparison {n : ℕ} {a : SmoothManifolds.ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifolds.AtlasData.SmoothManifold n a M) : Prop :=
  ∀ (C : CotangentBundle S) (B : ∀ q, FormBundle C q) (K : Calculus C B),
    ∃ e : ComparisonFamily S K, IsIntegrationComparison S K e

/-- The precise local-to-global closure property needed from open-cover descent.
Only boundaryless manifolds and covers in the ambient universe are needed. -/
def IntegrationCoverLocality : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M)
    (ι : Type u) (U : ι → Opens M) (_ : ∀ x, ∃ i, x ∈ U i),
    (∀ k (t : Fin (k+1) → ι),
      ManifoldIntegrationComparison (openSubmanifold S
        (P202Specs.CochainCoverDescent.tupleOpen U t))) →
    ManifoldIntegrationComparison S

/-- Convex coordinate neighborhoods and their intersections supply the first
source globalization step, with all empty intersections retained. The smooth
structure need not be the standard structure on the coordinate domain. -/
theorem integrationComparison_of_coordinateDomain
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    (hdescent : IntegrationCoverLocality.{u})
    {n m : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M) (U : Opens (SmoothManifolds.ModelData.Euclidean m)) (h : M ≃ₜ U) :
    ManifoldIntegrationComparison S := by
  let I := ULift.{u} (ConvexCoordinateIndex U)
  let V : I → Opens M := fun i => convexCoordinateOpen U h i.down
  have hcover : ∀ x : M, ∃ i, x ∈ V i := by
    intro x
    obtain ⟨i, hi⟩ := (convexCoordinateCover U h).covers x
    exact ⟨ULift.up i, hi⟩
  apply hdescent S I V hcover
  intro k t
  let W := P202Specs.CochainCoverDescent.tupleOpen V t
  cases isEmpty_or_nonempty ↥W with
  | inl hempty =>
    letI := hempty
    intro C B K
    exact integrationComparison_empty (openSubmanifold S W) hcomp K
  | inr hne =>
    letI := hne
    letI : Nonempty (P202Specs.CochainCoverDescent.tupleOpen
        (convexCoordinateOpen U h) (fun j => (t j).down)) := hne
    letI : ContractibleSpace W :=
      convexCoordinateTuple_contractible U h (fun j => (t j).down)
    intro C B K
    exact integrationComparison_of_contractible (openSubmanifold S W) hcomp K

/-- Every finite coordinate-domain intersection is itself a coordinate-open
space; applying the first step there and descent again proves all boundaryless
manifolds in the original dimension and separation/countability scope. -/
theorem integrationComparison_boundaryless_of_coverLocality
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    (hdescent : IntegrationCoverLocality.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M) : ManifoldIntegrationComparison S := by
  apply hdescent S (ChartCoverIndex S) (chartCoverOpen S) (chartCover S).covers
  intro k t
  exact integrationComparison_of_coordinateDomain hcomp hdescent
    (openSubmanifold S (P202Specs.CochainCoverDescent.tupleOpen (chartCoverOpen S) t))
    (chartTupleCoordinateOpen S t) (chartTupleCoordinateHomeomorph S t)

/-- The actual collar/interior transfer closes the boundary case from the two
cover arguments. No comparison premise on the original manifold is assumed. -/
theorem comparisonIsomorphism_of_coverLocality
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    (hdescent : IntegrationCoverLocality.{u}) :
    P202Specs.DeRhamComparison.comparisonIsomorphism_type.{u} := by
  intro n a M _ S C B K
  apply integrationComparison_of_interior S hcomp C B K
  intro T A E J
  exact integrationComparison_boundaryless_of_coverLocality hcomp hdescent T A E J

/-- Global integration comparison, with the exact missing cover-locality
statement visible as a premise. Naturality was established independently. -/
theorem deRhamComparison_of_coverLocality
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u})
    (hdescent : IntegrationCoverLocality.{u}) :
    P202Specs.DeRhamComparison.deRhamComparison_type.{u} :=
  ⟨comparisonIsomorphism_of_coverLocality hcomp hdescent, comparisonNaturality⟩

end P202.DeRhamComparison


namespace P202.DeRhamComparison.CategoricalBridge
open SmoothManifolds.MayerVietorisData
open P202Specs.UniversalCoefficients
open CategoryTheory HomologicalComplex
universe u v
variable (A : Cochain.{u}) (C : CochainComplex (ModuleCat.{v} ℝ) ℤ)
  (e : ∀ q, A.Obj q ≃ₗ[ℝ] C.X (q:ℤ))
  (hd : ∀ (q : ℕ) (x : A.Obj q), C.d (q:ℤ) ((q:ℤ)+1) (e q x) = e (q+1) (A.d q x))

def closedEquiv (q : ℕ) : A.closed q ≃ₗ[ℝ] Algebraic.cycles C (q:ℤ) where
  toFun x := ⟨e q x.val, by
    simp only [Algebraic.cycles, LinearMap.mem_ker]
    rw [CochainComplex.next]
    change C.d (q:ℤ) ((q:ℤ)+1) (e q x.val) = 0
    rw [hd, show A.d q x.val = 0 from x.property, map_zero]⟩
  invFun x := ⟨(e q).symm x.val, by
    apply (e (q+1)).injective
    rw [map_zero, ← hd, LinearEquiv.apply_symm_apply]
    have hx : C.d (q:ℤ) ((ComplexShape.up ℤ).next (q:ℤ)) x.val = 0 := x.property
    rw [CochainComplex.next] at hx
    exact hx⟩
  left_inv x := by apply Subtype.ext; exact (e q).symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact (e q).apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact (e q).map_add x.val y.val
  map_smul' r x := by apply Subtype.ext; exact (e q).map_smul r x.val

variable (hzero : C.d (-1) 0 = 0)
include hzero in
theorem boundaries_iff (q : ℕ) (x : A.closed q) :
    closedEquiv A C e hd q x ∈ Algebraic.cycleBoundaries C (q:ℤ) ↔
      x ∈ A.boundaries q := by
  simp only [Algebraic.cycleBoundaries, Submodule.mem_comap, Algebraic.boundaries, LinearMap.mem_range]
  rw [CochainComplex.prev]
  change (∃ y, C.d ((q:ℤ)-1) (q:ℤ) y = e q x.val) ↔ _
  cases q with
  | zero =>
    constructor
    · rintro ⟨y,hy⟩
      have hx0 : x.val=0 := by
        apply (e 0).injective
        rw [map_zero]
        exact hy.symm.trans (by change C.d (-1) 0 y=0; rw [hzero]; rfl)
      exact hx0
    · intro hx
      have hx0 : x.val=0 := hx
      refine ⟨0,?_⟩
      change C.d (-1) 0 0 = e 0 x.val
      rw [hx0,map_zero,map_zero]
  | succ q =>
    have hcast : (↑(q+1):ℤ)-1=(q:ℤ) := by omega
    have hcast' : (↑(q+1):ℤ)=(q:ℤ)+1 := by omega
    rw [hcast]
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨(e q).symm y,?_⟩
      apply (e (q+1)).injective
      rw [← hd,LinearEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨y,hy⟩
      refine ⟨e q y,?_⟩
      exact (hd q y).trans (congrArg (e (q+1)) hy)

def quotientEquiv (q : ℕ) : A.H q ≃ₗ[ℝ] Algebraic.Homology C (q:ℤ) :=
  Submodule.Quotient.equiv (A.boundaries q) (Algebraic.cycleBoundaries C (q:ℤ))
    (closedEquiv A C e hd q) (by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact (boundaries_iff A C e hd hzero q y).mpr hy
      · intro hx
        refine ⟨(closedEquiv A C e hd q).symm x,?_,by simp⟩
        apply (boundaries_iff A C e hd hzero q _).mp
        simpa using hx)

def cohomologyEquiv (q : ℕ) : A.H q ≃ₗ[ℝ] C.homology (q:ℤ) :=
  (quotientEquiv A C e hd hzero q).trans (quotientHomologyEquiv ℝ C (q:ℤ)).symm

@[simp] theorem cohomologyEquiv_class (q : ℕ) (x : A.closed q) :
    cohomologyEquiv A C e hd hzero q (A.classOf q x) =
      P202Specs.UniversalCoefficientsCohomology.cycleClass ℝ C (q:ℤ)
        (closedEquiv A C e hd q x) := rfl

end P202.DeRhamComparison.CategoricalBridge


namespace P202.DeRhamComparison.CochainProducts
open SmoothManifolds.MayerVietorisData
universe u
variable {ι : Type u}

def product (A : ι → Cochain.{u}) : Cochain.{u} where
  Obj k := (i : ι) → (A i).Obj k
  d k := {
    toFun x i := (A i).d k (x i)
    map_add' x y := by funext i; exact map_add _ _ _
    map_smul' r x := by funext i; exact map_smul _ _ _ }
  square k x := by funext i; exact (A i).square k (x i)

def closedEval (A : ι → Cochain.{u}) (k : ℕ) (i : ι) :
    (product A).closed k →ₗ[ℝ] (A i).closed k where
  toFun x := ⟨x.val i, congrFun x.property i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def classProduct (A : ι → Cochain.{u}) (k : ℕ) :
    (product A).closed k →ₗ[ℝ] ((i : ι) → (A i).H k) :=
  LinearMap.pi (fun i => ((A i).classOf k).comp (closedEval A k i))

theorem classProduct_zero_iff (A : ι → Cochain.{u}) (k : ℕ)
    (x : (product A).closed k) : classProduct A k x = 0 ↔ x.val ∈ (product A).exact k := by
  constructor
  · intro hx
    have hc (i : ι) : x.val i ∈ (A i).exact k := by
      apply ((A i).class_zero_iff k (closedEval A k i x)).mp
      exact congrFun hx i
    cases k with
    | zero =>
      change x.val = 0
      funext i
      exact hc i
    | succ k =>
      choose y hy using hc
      exact ⟨y, funext hy⟩
  · intro hx
    funext i
    apply ((A i).class_zero_iff k (closedEval A k i x)).mpr
    cases k with
    | zero =>
      change x.val = 0 at hx
      change x.val i = 0
      exact congrFun hx i
    | succ k =>
      obtain ⟨y,hy⟩ := hx
      exact ⟨y i, congrFun hy i⟩

def cohomologyMap (A : ι → Cochain.{u}) (k : ℕ) :
    (product A).H k →ₗ[ℝ] ((i : ι) → (A i).H k) :=
  ((product A).boundaries k).liftQ (classProduct A k)
    (fun x hx => (classProduct_zero_iff A k x).mpr hx)

@[simp] theorem cohomologyMap_class (A : ι → Cochain.{u}) (k : ℕ) (x : (product A).closed k) :
    cohomologyMap A k ((product A).classOf k x) = classProduct A k x := rfl

theorem cohomologyMap_bijective (A : ι → Cochain.{u}) (k : ℕ) :
    Function.Bijective (cohomologyMap A k) := by
  constructor
  · apply (cohomologyMap A k).ker_eq_bot.mp
    apply le_antisymm
    · intro z hz
      obtain ⟨x,rfl⟩ := (product A).class_surjective k z
      exact ((product A).class_zero_iff k x).mpr
        ((classProduct_zero_iff A k x).mp hz)
    · exact bot_le
  · intro z
    choose x hx using (fun i => (A i).class_surjective k (z i))
    let y : (product A).closed k := ⟨fun i => (x i).val, funext (fun i => (x i).property)⟩
    refine ⟨(product A).classOf k y, ?_⟩
    funext i
    exact hx i

def productMap {A B : ι → Cochain.{u}} (f : ∀ i, ChainMap (A i) (B i)) :
    ChainMap (product A) (product B) where
  map k := {
    toFun x i := (f i).map k (x i)
    map_add' x y := by funext i; exact map_add _ _ _
    map_smul' r x := by funext i; exact map_smul _ _ _ }
  comm k x := by funext i; exact (f i).comm k (x i)

theorem cohomologyMap_naturality {A B : ι → Cochain.{u}} (f : ∀ i, ChainMap (A i) (B i))
    (k : ℕ) (x : (product A).H k) :
    cohomologyMap B k ((productMap f).onH k x) =
      fun i => (f i).onH k (cohomologyMap A k x i) := by
  obtain ⟨x,rfl⟩ := (product A).class_surjective k x
  funext i
  rfl

/-- Arbitrary products preserve quasi-isomorphisms of nonnegative real
cochain complexes. Representatives and primitives are selected coordinatewise. -/
theorem productMap_onH_bijective {A B : ι → Cochain.{u}} (f : ∀ i, ChainMap (A i) (B i))
    (hf : ∀ i k, Function.Bijective ((f i).onH k)) (k : ℕ) :
    Function.Bijective ((productMap f).onH k) := by
  constructor
  · intro x y hxy
    apply (cohomologyMap_bijective A k).1
    funext i
    apply (hf i k).1
    have h := congrArg (fun z => cohomologyMap B k z i) hxy
    simpa only [cohomologyMap_naturality] using h
  · intro y
    let z (i : ι) := ((hf i k).2 (cohomologyMap B k y i)).choose
    have hz (i : ι) : (f i).onH k (z i) = cohomologyMap B k y i :=
      ((hf i k).2 (cohomologyMap B k y i)).choose_spec
    obtain ⟨x,hx⟩ := (cohomologyMap_bijective A k).2 z
    refine ⟨x, (cohomologyMap_bijective B k).1 ?_⟩
    rw [cohomologyMap_naturality, hx]
    exact funext hz
end P202.DeRhamComparison.CochainProducts


namespace P202.DeRhamComparison.CoverAssembly
universe u v
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {ι : Type v}
  (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)

abbrev smallSmoothOrdinaryComplex :=
  (P202.SmoothSingularComparison.smallSmoothComplex S U).extend
    (P202Specs.SingularChains.degreeEmbedding 0)

def smallSmoothOrdinaryInclusion : smallSmoothOrdinaryComplex S U ⟶
    SmoothSingularComparison.smoothOrdinaryComplex S :=
  HomologicalComplex.extendMap (P202.SmoothSingularComparison.smallSmoothInclusion S U)
    (P202Specs.SingularChains.degreeEmbedding 0)

abbrev smallSmoothCochains :=
  (P202Specs.CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).obj
    (op (smallSmoothOrdinaryComplex S U))

def smallSmoothRestriction : SmoothSingularComparison.smoothCochains S ⟶
    smallSmoothCochains S U :=
  (P202Specs.CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).map
    (smallSmoothOrdinaryInclusion S U).op

theorem smallSmoothRestriction_cohomology_isIso (q : ℤ) :
    IsIso (homologyMap (smallSmoothRestriction S U) q) := by
  haveI : QuasiIso (P202.SmoothSingularComparison.smallSmoothInclusion S U) := by
    rw [quasiIso_iff]
    intro k
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
      (P202.SmoothSingularComparison.smallSmoothComparison S U k)
  haveI : QuasiIso (smallSmoothOrdinaryInclusion S U) := by
    change QuasiIso (extendMap (P202.SmoothSingularComparison.smallSmoothInclusion S U)
      (P202Specs.SingularChains.degreeEmbedding 0))
    infer_instance
  haveI : IsIso (homologyMap (smallSmoothOrdinaryInclusion S U) q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  exact P202.SmoothSingularComparison.dual_homology_isIso_of_isIso
    (smallSmoothOrdinaryInclusion S U) q

open P202Specs.CochainCoverDescent P202.CochainCoverDescent.CechTotals
open P202.CochainCoverDescent.TotalAlgebra

def smallSmoothDegreeIso (q : ℕ) :
    (smallSmoothOrdinaryComplex S U).X (q : ℤ) ≅
      ModuleCat.of ℝ (P202.SmoothSingularComparison.smallSmoothModule S U q) :=
  (P202.SmoothSingularComparison.smallSmoothComplex S U).extendXIso
    (P202Specs.SingularChains.degreeEmbedding 0) (by change (0 : ℤ) + q = q; omega)

theorem augmentationChainModule_eq (q : ℕ) :
    intersectionChainModule S U q 0 Fin.elim0 =
      P202.SmoothSingularComparison.smallSmoothModule S U q := by
  ext z
  simp only [intersectionChainModule, P202.SmoothSingularComparison.smallSmoothModule,
    SmoothSingularComparison.smoothModule, SmallChainHomology.smallModule,
    Submodule.mem_inf, Finsupp.mem_supported, Set.mem_setOf_eq]
  constructor
  · intro hz
    exact ⟨fun σ hσ => (hz hσ).1, fun σ hσ => (hz hσ).2.1⟩
  · intro hz σ hσ
    exact ⟨hz.1 hσ, hz.2 hσ, fun j => Fin.elim0 j⟩

def smallSmoothCochainDegreeEquiv (q : ℕ) :
    (smallSmoothCochains S U).X (q : ℤ) ≃ₗ[ℝ]
      (P202.SmoothSingularComparison.smallSmoothModule S U q →ₗ[ℝ] ℝ) :=
  LinearEquiv.congrLeft ℝ ℝ (smallSmoothDegreeIso S U q).toLinearEquiv

def smallIntersectionChainEquiv (q : ℕ) :
    P202.SmoothSingularComparison.smallSmoothModule S U q ≃ₗ[ℝ]
      intersectionChainModule S U q 0 Fin.elim0 :=
  LinearEquiv.ofEq _ _ (augmentationChainModule_eq S U q).symm

def smallCochainRowEquiv (q : ℕ) :
    (smallSmoothCochains S U).X (q : ℤ) ≃ₗ[ℝ] IntersectionCochainRow S U q 0 :=
  (smallSmoothCochainDegreeEquiv S U q).trans
    ((LinearEquiv.congrLeft ℝ ℝ (smallIntersectionChainEquiv S U q)).trans
      ((LinearEquiv.congrLeft ℝ ℝ (intersectionChainBasisEquiv S U q 0 Fin.elim0)).trans
        (LinearEquiv.piUnique ℝ (fun t : Fin 0 → ι =>
          (IntersectionSimplex S U q 0 t →₀ ℝ) →ₗ[ℝ] ℝ)).symm))

@[simp] theorem smallCochainRowEquiv_apply (q : ℕ)
    (c : (smallSmoothCochains S U).X (q : ℤ))
    (z : IntersectionSimplex S U q 0 Fin.elim0 →₀ ℝ) :
    smallCochainRowEquiv S U q c Fin.elim0 z =
      smallSmoothCochainDegreeEquiv S U q c
        ((smallIntersectionChainEquiv S U q).symm
          ((intersectionChainBasisEquiv S U q 0 Fin.elim0).symm z)) := rfl

theorem smallSmoothCochainDegreeEquiv_d (q : ℕ)
    (c : (smallSmoothCochains S U).X (q : ℤ))
    (z : P202.SmoothSingularComparison.smallSmoothModule S U (q+1)) :
    smallSmoothCochainDegreeEquiv S U (q+1)
        ((smallSmoothCochains S U).d (q:ℤ) (q+1:ℕ) c) z =
      smallSmoothCochainDegreeEquiv S U q c
        ((P202.SmoothSingularComparison.smallSmoothComplex S U).d (q+1) q z) := by
  change ((smallSmoothOrdinaryComplex S U).X (q:ℤ) →ₗ[ℝ] ℝ) at c
  change c ((smallSmoothOrdinaryComplex S U).d (q+1:ℕ) (q:ℤ)
    ((smallSmoothDegreeIso S U (q+1)).inv z)) =
      c ((smallSmoothDegreeIso S U q).inv
        ((P202.SmoothSingularComparison.smallSmoothComplex S U).d (q+1) q z))
  have hi : (SingularChains.degreeEmbedding 0).f (q+1) = ((q+1:ℕ):ℤ) := by
    change (0:ℤ)+(q+1:ℕ)=(q+1:ℕ)
    omega
  have hj : (SingularChains.degreeEmbedding 0).f q = (q:ℤ) := by
    change (0:ℤ)+q=q
    omega
  rw [show (smallSmoothOrdinaryComplex S U).d (q+1:ℕ) (q:ℤ) =
      (smallSmoothDegreeIso S U (q+1)).hom ≫
        (P202.SmoothSingularComparison.smallSmoothComplex S U).d (q+1) q ≫
          (smallSmoothDegreeIso S U q).inv from HomologicalComplex.extend_d_eq _ _ hi hj]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

theorem smallCochainRowEquiv_d (q : ℕ)
    (c : (smallSmoothCochains S U).X (q : ℤ)) :
    intersectionV S U q 0 (smallCochainRowEquiv S U q c) =
      smallCochainRowEquiv S U (q+1)
        ((smallSmoothCochains S U).d (q:ℤ) (q+1:ℕ) c) := by
  funext t
  have ht : t=Fin.elim0 := Subsingleton.elim _ _
  subst t
  apply LinearMap.ext
  intro z
  change smallCochainRowEquiv S U q c Fin.elim0
    ((intersectionChainBasisEquiv S U q 0 Fin.elim0)
      (intersectionBoundary S U q 0 Fin.elim0
        ((intersectionChainBasisEquiv S U (q+1) 0 Fin.elim0).symm z))) = _
  rw [smallCochainRowEquiv_apply,smallCochainRowEquiv_apply,
    smallSmoothCochainDegreeEquiv_d]
  simp only [LinearEquiv.symm_apply_apply]
  apply congrArg (smallSmoothCochainDegreeEquiv S U q c)
  apply Subtype.ext
  simp only [smallIntersectionChainEquiv, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, P202.SmoothSingularComparison.smallSmoothComplex, ChainComplex.of_d]
  rfl

def smallCochainAugmentationEquiv (q : ℕ) :
    (smallSmoothCochains S U).X (q : ℤ) ≃ₗ[ℝ]
      (cochainData S U).augmentationComplex.space (q : ℤ) :=
  (smallCochainRowEquiv S U q).trans
    ((GridEmbedding.spaceEquiv (fun p q => IntersectionCochainRow S U q p) 0 q).trans
      (LinearEquiv.ofEq _ _ (by
        simp only [Data.augmentationComplex, if_pos (Int.natCast_nonneg q), Int.toNat_natCast]
        rfl)))

@[simp] theorem smallCochainAugmentationEquiv_val (q : ℕ)
    (c : (smallSmoothCochains S U).X (q : ℤ)) :
    (smallCochainAugmentationEquiv S U q c).val =
      GridEmbedding.embed (fun p q => IntersectionCochainRow S U q p) 0 q
        (smallCochainRowEquiv S U q c) := rfl

theorem cochainData_augmentation_d_embed (q : ℕ)
    (c : IntersectionCochainRow S U q 0) :
    (cochainData S U).augmentationComplex.differential (q:ℤ)
      (GridEmbedding.embed (fun p q => IntersectionCochainRow S U q p) 0 q c) =
    GridEmbedding.embed (fun p q => IntersectionCochainRow S U q p) 0 (q+1)
      (intersectionV S U q 0 c) := by
  change (if 0 ≤ (q:ℤ) then
      -GridEmbedding.vertical (fun p q => IntersectionCochainRow S U q p)
        (fun p q => (-1:ℝ) • intersectionV S U q p) else 0)
      (GridEmbedding.embed (fun p q => IntersectionCochainRow S U q p) 0 q c) = _
  rw [if_pos (Int.natCast_nonneg q), LinearMap.neg_apply, GridEmbedding.vertical_embed]
  simp only [LinearMap.smul_apply]
  rw [map_smul]
  let z := GridEmbedding.embed (fun p q => IntersectionCochainRow S U q p) 0 (q+1)
    (intersectionV S U q 0 c)
  funext r s t
  apply LinearMap.ext
  intro x
  change -((-1:ℝ) • (z r s t x)) = z r s t x
  rw [neg_one_smul, neg_neg]

theorem smallCochainAugmentationEquiv_d (q : ℕ)
    (c : (smallSmoothCochains S U).X (q : ℤ)) :
    (cochainData S U).augmentationComplex.differential (q:ℤ)
      (smallCochainAugmentationEquiv S U q c).val =
      (smallCochainAugmentationEquiv S U (q+1)
        ((smallSmoothCochains S U).d (q:ℤ) (q+1:ℕ) c)).val := by
  rw [smallCochainAugmentationEquiv_val, smallCochainAugmentationEquiv_val,
    cochainData_augmentation_d_embed, smallCochainRowEquiv_d]

theorem smallSmoothRestriction_degree (q : ℕ)
    (c : (SmoothSingularComparison.smoothCochains S).X (q:ℤ))
    (z : P202.SmoothSingularComparison.smallSmoothModule S U q) :
    smallSmoothCochainDegreeEquiv S U q ((smallSmoothRestriction S U).f (q:ℤ) c) z =
      (show (SmoothSingularComparison.smoothOrdinaryComplex S).X (q:ℤ) →ₗ[ℝ] ℝ from c)
        ((P202Specs.DeRhamComparison.smoothDegreeIso S q).inv ⟨z.val,z.property.1⟩) := by
  change ((SmoothSingularComparison.smoothOrdinaryComplex S).X (q:ℤ) →ₗ[ℝ] ℝ) at c
  change c ((smallSmoothOrdinaryInclusion S U).f (q:ℤ)
    ((smallSmoothDegreeIso S U q).inv z)) = _
  have hq : (SingularChains.degreeEmbedding 0).f q = (q:ℤ) := by
    change (0:ℤ)+q=q
    omega
  rw [show (smallSmoothOrdinaryInclusion S U).f (q:ℤ) =
      (smallSmoothDegreeIso S U q).hom ≫
        (P202.SmoothSingularComparison.smallSmoothInclusion S U).f q ≫
          (P202Specs.DeRhamComparison.smoothDegreeIso S q).inv from
      HomologicalComplex.extendMap_f _ _ hq]
  simp only [ModuleCat.comp_apply,Iso.inv_hom_id_apply]
  rfl

theorem smallCochainRowEquiv_restriction_generator (q : ℕ)
    (c : (SmoothSingularComparison.smoothCochains S).X (q:ℤ))
    (σ : IntersectionSimplex S U q 0 Fin.elim0) :
    smallCochainRowEquiv S U q ((smallSmoothRestriction S U).f (q:ℤ) c) Fin.elim0
        (Finsupp.single σ 1) =
      P202Specs.DeRhamComparison.evaluateSmoothCochain S c
        ⟨σ.val.val,σ.val.property.1⟩ := by
  rw [smallCochainRowEquiv_apply, smallSmoothRestriction_degree]
  change ((SmoothSingularComparison.smoothOrdinaryComplex S).X (q:ℤ) →ₗ[ℝ] ℝ) at c
  apply congrArg c
  apply congrArg ((P202Specs.DeRhamComparison.smoothDegreeIso S q).inv)
  apply Subtype.ext
  simp only [smallIntersectionChainEquiv,LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply,
    P202.CochainCoverDescent.intersectionChainBasisEquiv_symm_single,
    P202Specs.DeRhamComparison.smoothGenerator]

theorem smallSmoothCochain_d_neg_one_zero :
    (smallSmoothCochains S U).d (-1) 0 = 0 := by
  have hz : CategoryTheory.Limits.IsZero ((smallSmoothOrdinaryComplex S U).X (-1)) :=
    (P202.SmoothSingularComparison.smallSmoothComplex S U).isZero_extend_X
      (SingularChains.degreeEmbedding 0) (-1) (by
        intro q
        change (0:ℤ)+q ≠ -1
        omega)
  have hd : (smallSmoothOrdinaryComplex S U).d 0 (-1)=0 := hz.eq_of_tgt _ _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((smallSmoothOrdinaryComplex S U).X (-1) →ₗ[ℝ] ℝ) at c
  change c.comp ((smallSmoothOrdinaryComplex S U).d 0 (-1)).hom=0
  rw [hd]
  exact LinearMap.comp_zero _

end P202.DeRhamComparison.CoverAssembly


namespace P202.DeRhamComparison
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
open SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData SmoothManifolds.MayerVietorisData
open P202Specs P202.CochainCoverDescent P202.CochainCoverDescent.TotalAlgebra
universe u v
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : AtlasData.SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ q, FormBundle C q}

def formAugmentationCohomologyEquiv (K : Calculus C B)
    {ι : Type v} (U : ι → TopologicalSpace.Opens M) (q : ℕ) :
    K.Cohomology q ≃ₗ[ℝ] (CechTotals.formData C B U).augmentationComplex.Cohomology (q:ℤ) :=
  ConeBridge.cohomologyEquiv (globalComplex K) (CechTotals.formData C B U).augmentationComplex
    (CechTotals.formGlobalAugmentationEquiv K U)
    (CechTotals.formGlobalAugmentationEquiv_d K U) (by
      change (if 0 ≤ (-1:ℤ) then (CechTotals.formData C B U).space 0 (-1:ℤ).toNat else ⊥)=⊥
      rw [if_neg (by omega)]) q

end P202.DeRhamComparison


namespace P202.DeRhamComparison.ConeBridge
open SmoothManifolds.MayerVietorisData
open P202.CochainCoverDescent.ConeAlgebra
universe u v w z
variable {E : Type u} [AddCommGroup E] [Module ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F]
  (A : Cochain.{w}) (B : Cochain.{w})
  (C : Complex E) (D : Complex F)
  (eA : ∀ q, A.Obj q ≃ₗ[ℝ] C.space (q:ℤ))
  (eB : ∀ q, B.Obj q ≃ₗ[ℝ] D.space (q:ℤ))
  (hdA : ∀ (q : ℕ) (x : A.Obj q), C.differential (q:ℤ) (eA q x).val = (eA (q+1) (A.d q x)).val)
  (hdB : ∀ (q : ℕ) (x : B.Obj q), D.differential (q:ℤ) (eB q x).val = (eB (q+1) (B.d q x)).val)
  (hnegA : C.space (-1) = ⊥) (hnegB : D.space (-1) = ⊥)
  (f : ChainMap A B) (g : Map C D)
  (hfg : ∀ (q : ℕ) (x : A.Obj q), g.map (q:ℤ) (eA q x).val = (eB q (f.map q x)).val)

include eA eB hdA hdB hnegA hnegB hfg
theorem cohomologyEquiv_natural (q : ℕ) (x : A.H q) :
    g.cohomologyMap (q:ℤ) (cohomologyEquiv A C eA hdA hnegA q x) =
      cohomologyEquiv B D eB hdB hnegB q (f.onH q x) := by
  obtain ⟨a,rfl⟩ := A.class_surjective q x
  rw [cohomologyEquiv_class, f.onH_class, cohomologyEquiv_class]
  change (D.boundaries (q:ℤ)).mkQ (g.cycleMap (q:ℤ) (closedEquiv A C eA hdA q a)) = _
  congr 1
  apply Subtype.ext
  exact hfg q a.val

theorem onH_bijective_of_cohomologyMap_bijective (q : ℕ)
    (hg : Function.Bijective (g.cohomologyMap (q:ℤ))) :
    Function.Bijective (f.onH q) := by
  constructor
  · intro x y hxy
    apply (cohomologyEquiv A C eA hdA hnegA q).injective
    apply hg.1
    rw [cohomologyEquiv_natural A B C D eA eB hdA hdB hnegA hnegB f g hfg,
      cohomologyEquiv_natural A B C D eA eB hdA hdB hnegA hnegB f g hfg,hxy]
  · intro y
    obtain ⟨z,hz⟩ := hg.2 (cohomologyEquiv B D eB hdB hnegB q y)
    refine ⟨(cohomologyEquiv A C eA hdA hnegA q).symm z,?_⟩
    apply (cohomologyEquiv B D eB hdB hnegB q).injective
    rw [← cohomologyEquiv_natural A B C D eA eB hdA hdB hnegA hnegB f g hfg,
      LinearEquiv.apply_symm_apply,hz]

end P202.DeRhamComparison.ConeBridge


namespace P202.DeRhamComparison.CoverAssembly
open SmoothManifolds.MayerVietorisData
open CategoryTheory HomologicalComplex
open P202.CochainCoverDescent.TotalAlgebra
open P202.CochainCoverDescent.CechTotals
universe u v

def nonnegativeModel (C : CochainComplex (ModuleCat.{u} ℝ) ℤ) : Cochain.{u} where
  Obj q := C.X (q:ℤ)
  d q := (C.d (q:ℤ) (q+1:ℕ)).hom
  square q x := by
    have h := congrArg (fun f => f x) (C.d_comp_d (q:ℤ) (q+1:ℕ) (q+2:ℕ))
    exact h

def nonnegativeModelMap {C D : CochainComplex (ModuleCat.{u} ℝ) ℤ} (f : C ⟶ D) :
    ChainMap (nonnegativeModel C) (nonnegativeModel D) where
  map q := (f.f (q:ℤ)).hom
  comm q x := by
    have h := congrArg (fun f => f x) (f.comm (q:ℤ) (q+1:ℕ))
    exact h

def nonnegativeCohomologyEquiv (C : CochainComplex (ModuleCat.{u} ℝ) ℤ)
    (hzero : C.d (-1) 0=0) (q : ℕ) :
    (nonnegativeModel C).H q ≃ₗ[ℝ] C.homology (q:ℤ) :=
  P202.DeRhamComparison.CategoricalBridge.cohomologyEquiv (nonnegativeModel C) C
    (fun q => LinearEquiv.refl ℝ (C.X (q:ℤ))) (fun _ _ => rfl) hzero q

theorem nonnegativeCohomologyEquiv_natural
    {C D : CochainComplex (ModuleCat.{u} ℝ) ℤ} (f : C ⟶ D)
    (hC : C.d (-1) 0=0) (hD : D.d (-1) 0=0) (q : ℕ)
    (x : (nonnegativeModel C).H q) :
    nonnegativeCohomologyEquiv D hD q ((nonnegativeModelMap f).onH q x) =
      homologyMap f (q:ℤ) (nonnegativeCohomologyEquiv C hC q x) := by
  obtain ⟨a,rfl⟩ := (nonnegativeModel C).class_surjective q x
  simp only [nonnegativeCohomologyEquiv, ChainMap.onH_class,
    CategoricalBridge.cohomologyEquiv_class,
    P202.UniversalCoefficientsCohomology.cycleClass_map]
  rfl

theorem nonnegativeModelMap_bijective
    {C D : CochainComplex (ModuleCat.{u} ℝ) ℤ} (f : C ⟶ D)
    (hC : C.d (-1) 0=0) (hD : D.d (-1) 0=0) (q : ℕ)
    (hf : Function.Bijective (homologyMap f (q:ℤ))) :
    Function.Bijective ((nonnegativeModelMap f).onH q) := by
  constructor
  · intro x y hxy
    apply (nonnegativeCohomologyEquiv C hC q).injective
    apply hf.1
    rw [← nonnegativeCohomologyEquiv_natural f hC hD q,
      ← nonnegativeCohomologyEquiv_natural f hC hD q,hxy]
  · intro y
    obtain ⟨z,hz⟩ := hf.2 (nonnegativeCohomologyEquiv D hD q y)
    refine ⟨(nonnegativeCohomologyEquiv C hC q).symm z,?_⟩
    apply (nonnegativeCohomologyEquiv D hD q).injective
    rw [nonnegativeCohomologyEquiv_natural f hC hD q,LinearEquiv.apply_symm_apply,hz]

variable {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifolds.AtlasData.SmoothManifold n a M) {ι : Type v}
  (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)

def smallSmoothAugmentationCohomologyEquiv (q : ℕ) :
    (smallSmoothCochains S U).homology (q:ℤ) ≃ₗ[ℝ]
      (cochainData S U).augmentationComplex.Cohomology (q:ℤ) :=
  (nonnegativeCohomologyEquiv (smallSmoothCochains S U)
    (smallSmoothCochain_d_neg_one_zero S U) q).symm.trans
      (P202.DeRhamComparison.ConeBridge.cohomologyEquiv
        (nonnegativeModel (smallSmoothCochains S U))
        (cochainData S U).augmentationComplex
        (smallCochainAugmentationEquiv S U)
        (smallCochainAugmentationEquiv_d S U)
        (by simp [Data.augmentationComplex]) q)

end P202.DeRhamComparison.CoverAssembly


namespace P202.DeRhamComparison
universe u v
attribute [local irreducible] SmoothManifolds.TangentData.smoothGermAlgebra
  SmoothManifolds.TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false
open SmoothManifolds.MayerVietorisData SmoothManifolds.MayerVietorisData.OpenForms
open P202Specs.CochainCoverDescent
section OpenIntegration
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)
  {C : CotangentBundle S} {B : ∀ q, FormBundle C q}
  (K : Calculus C B)
  (V : TopologicalSpace.Opens M)
  {A : CotangentBundle (openSubmanifold S V)} {E : ∀ q, FormBundle A q}
  (J : Calculus A E)

def openIntrinsicFormLinear (q : ℕ) : formsOn (B q) V →ₗ[ℝ] J.forms q :=
  ((openFormsPullbackChain S V K J (formOpenCalculus C B V)).map q).comp
    (openFormEquiv (formOpenCalculus C B V) q).symm.toLinearMap

@[simp] theorem openIntrinsicFormLinear_field (q : ℕ) (ω : formsOn (B q) V) (p : V) :
    (openIntrinsicFormLinear S K V J q ω).val p =
      FormPullbackData.fiberPullback
        (V := TangentData.TangentSpace (openSubmanifold S V) p)
        (W := TangentData.TangentSpace S p.val) q (openInclusionTangentEquiv S V p).toLinearMap (ω.val p) := by
  change (((openFormsPullbackChain S V K J (formOpenCalculus C B V)).map q)
    ((openFormEquiv (formOpenCalculus C B V) q).symm ω)).val p = _
  rw [openFormsPullbackChain_field]
  congr 1
  exact congrFun (field_realize (formOpenCalculus C B V) q ω.val ω.property) p

def openIntegrationLinear (I : IntegrationCochainData.IntegrationMap _ J) (q : ℕ) :
    formsOn (B q) V →ₗ[ℝ] SmoothSingularData.Cochains (openSubmanifold S V) q :=
  (I.map q).comp (openIntrinsicFormLinear S K V J q)

theorem openIntrinsicFormLinear_d (q : ℕ) (ω : formsOn (B q) V) :
    J.d q (openIntrinsicFormLinear S K V J q ω) =
      openIntrinsicFormLinear S K V J (q+1) (exteriorOn C B V q ω) := by
  change ((globalComplex J).d q)
    ((openFormsPullbackChain S V K J (formOpenCalculus C B V)).map q
      ((openFormEquiv (formOpenCalculus C B V) q).symm ω)) =
    (openFormsPullbackChain S V K J (formOpenCalculus C B V)).map (q+1)
      ((openFormEquiv (formOpenCalculus C B V) (q+1)).symm
        ((openFormEquiv (formOpenCalculus C B V) (q+1))
          ((formOpenCalculus C B V).complex.d q
            ((openFormEquiv (formOpenCalculus C B V) q).symm ω))))
  rw [LinearEquiv.symm_apply_apply]
  exact (openFormsPullbackChain S V K J (formOpenCalculus C B V)).comm q _

theorem openIntegrationLinear_d (I : IntegrationCochainData.IntegrationMap _ J)
    (q : ℕ) (ω : formsOn (B q) V) :
    SmoothSingularData.coboundary (openSubmanifold S V) q (openIntegrationLinear S K V J I q ω) =
      openIntegrationLinear S K V J I (q+1) (exteriorOn C B V q ω) := by
  change SmoothSingularData.coboundary _ q (I.map q (openIntrinsicFormLinear S K V J q ω)) = _
  rw [← I.commutes, openIntrinsicFormLinear_d]
  rfl

variable (W : TopologicalSpace.Opens M) (hWV : W ≤ V)
  {A' : CotangentBundle (openSubmanifold S W)} {E' : ∀ q, FormBundle A' q}
  (J' : Calculus A' E')

def nestedOpenDifferential (p : W) :
    TangentData.TangentSpace (openSubmanifold S W) p →ₗ[ℝ]
      TangentData.TangentSpace (openSubmanifold S V) (openInclusionMap V W hWV p) :=
  SmoothManifolds.differential (openSubmanifold S W) (openSubmanifold S V)
    (openInclusionMap V W hWV) (openInclusionMap_smooth S V W hWV) p

theorem nestedOpenDifferential_comp (p : W) :
    (openInclusionTangentEquiv S V (openInclusionMap V W hWV p)).toLinearMap.comp
      (nestedOpenDifferential S V W hWV p) =
        (openInclusionTangentEquiv S W p).toLinearMap := by
  have hc := SmoothManifolds.differential_comp (openSubmanifold S W) (openSubmanifold S V) S
    (openInclusionMap V W hWV) Subtype.val (openInclusionMap_smooth S V W hWV)
    (openSubmanifold_inclusion_smooth S V) p (nestedOpenDifferential S V W hWV p)
    (openInclusionTangentEquiv S V (openInclusionMap V W hWV p)).toLinearMap
    (SmoothManifolds.differential_spec _ _ _ _ p)
    (openInclusionTangentEquiv_isDifferential S V _)
  exact (SmoothManifolds.differential_exists (openSubmanifold S W) S Subtype.val
    (openSubmanifold_inclusion_smooth S W) p).unique hc (openInclusionTangentEquiv_isDifferential S W p)

/-- Ambient restriction becomes the genuine intrinsic pullback along the
inclusion of one open submanifold into another. -/
theorem openIntrinsicFormLinear_restriction (q : ℕ) (ω : formsOn (B q) V) :
    (openIntrinsicFormLinear S K W J' q (formRestriction (B q) V W hWV ω)).val =
      FormPullbackData.pullbackField (openSubmanifold S W) (openSubmanifold S V)
        (openInclusionMap V W hWV) (nestedOpenDifferential S V W hWV)
        (openIntrinsicFormLinear S K V J q ω).val := by
  funext p
  simp only [openIntrinsicFormLinear_field, FormPullbackData.pullbackField]
  change FormPullbackData.fiberPullback
    (V := TangentData.TangentSpace (openSubmanifold S W) p)
    (W := TangentData.TangentSpace S p.val) q (openInclusionTangentEquiv S W p).toLinearMap
      (ω.val (openInclusionMap V W hWV p)) =
    FormPullbackData.fiberPullback
      (V := TangentData.TangentSpace (openSubmanifold S W) p)
      (W := TangentData.TangentSpace (openSubmanifold S V) (openInclusionMap V W hWV p))
      q (nestedOpenDifferential S V W hWV p)
      (FormPullbackData.fiberPullback
        (V := TangentData.TangentSpace (openSubmanifold S V) (openInclusionMap V W hWV p))
        (W := TangentData.TangentSpace S p.val) q
        (openInclusionTangentEquiv S V (openInclusionMap V W hWV p)).toLinearMap
        (ω.val (openInclusionMap V W hWV p)))
  rw [← nestedOpenDifferential_comp S V W hWV p]
  simp only [FormPullbackData.fiberPullback, ← LinearMap.dualMap_comp_dualMap,
    exteriorPower.map_comp, LinearMap.comp_apply]

/-- Literal integral cochains commute with restriction between arbitrary
open subsets, including those meeting the manifold boundary. -/
theorem openIntegrationLinear_restriction
    (I : IntegrationCochainData.IntegrationMap _ J)
    (I' : IntegrationCochainData.IntegrationMap _ J')
    (q : ℕ) (ω : formsOn (B q) V) :
    openIntegrationLinear S K W J' I' q (formRestriction (B q) V W hWV ω) =
      SmoothSingularData.cochainMap (openSubmanifold S W) (openSubmanifold S V)
        (openInclusionMap V W hWV) q (openIntegrationLinear S K V J I q ω) := by
  exact IntegrationCochain.integrationMap_pullback _ _ A' A E' E J' J I' I
    (openInclusionMap V W hWV) (openInclusionMap_smooth S V W hWV)
    (nestedOpenDifferential S V W hWV)
    (fun p => SmoothManifolds.differential_spec _ _ _ _ p) q
    (openIntrinsicFormLinear S K V J q ω)
    (openIntrinsicFormLinear S K W J' q (formRestriction (B q) V W hWV ω))
    (openIntrinsicFormLinear_restriction S K V J W hWV J' q ω)
end OpenIntegration
end P202.DeRhamComparison


namespace P202.DeRhamComparison.GridColumns
open SmoothManifolds.MayerVietorisData
open P202.CochainCoverDescent.TotalAlgebra
open P202.CochainCoverDescent.TotalAlgebra.GridEmbedding
universe u v
variable {C : ℕ → ℕ → Type u} [∀ p q, AddCommGroup (C p q)] [∀ p q, Module ℝ (C p q)]
  (h : ∀ p q, C p q →ₗ[ℝ] C (p+1) q)
  (v : ∀ p q, C p q →ₗ[ℝ] C p (q+1))
  (hh : ∀ p q z, h (p+1) q (h p q z)=0)
  (hv : ∀ p q z, v p (q+1) (v p q z)=0)
  (hc : ∀ p q z, h p (q+1) (v p q z)=v (p+1) q (h p q z))

def degreeEquiv (p q : ℕ) : C (p+1) q ≃ₗ[ℝ]
    (data C h v hh hv hc).positiveData.columnComplex (p:ℤ) |>.space (q:ℤ) :=
  (spaceEquiv C (p+1) q).trans (LinearEquiv.ofEq _ _ (by
    simp only [Data.columnComplex, if_pos (Int.natCast_nonneg q), Int.toNat_natCast,
      Data.positiveData, if_pos (Int.natCast_nonneg p)]
    have he : (↑p+1:ℤ)=↑(p+1) := by omega
    rw [he]
    rfl))

@[simp] theorem degreeEquiv_val (p q : ℕ) (z : C (p+1) q) :
    (degreeEquiv h v hh hv hc p q z).val = embed C (p+1) q z := rfl

theorem degreeEquiv_d (p q : ℕ) (z : C (p+1) q) :
    ((data C h v hh hv hc).positiveData.columnComplex (p:ℤ)).differential (q:ℤ)
      (degreeEquiv h v hh hv hc p q z).val =
      (degreeEquiv h v hh hv hc p (q+1) (-v (p+1) q z)).val := by
  change -vertical C v (embed C (p+1) q z) = embed C (p+1) (q+1) (-v (p+1) q z)
  rw [vertical_embed,map_neg]

 def cohomologyEquiv (p : ℕ) (A : Cochain.{v})
    (e : ∀ q, A.Obj q ≃ₗ[ℝ] C (p+1) q)
    (he : ∀ q x, -v (p+1) q (e q x) = e (q+1) (A.d q x)) (q : ℕ) :
    A.H q ≃ₗ[ℝ] ((data C h v hh hv hc).positiveData.columnComplex (p:ℤ)).Cohomology (q:ℤ) :=
  ConeBridge.cohomologyEquiv A ((data C h v hh hv hc).positiveData.columnComplex (p:ℤ))
    (fun q => (e q).trans (degreeEquiv h v hh hv hc p q))
    (fun q x => by
      change ((data C h v hh hv hc).positiveData.columnComplex (p:ℤ)).differential (q:ℤ)
        (degreeEquiv h v hh hv hc p q (e q x)).val =
        (degreeEquiv h v hh hv hc p (q+1) (e (q+1) (A.d q x))).val
      rw [degreeEquiv_d,he])
    (by simp only [Data.columnComplex, if_neg (show ¬0≤(-1:ℤ) by omega)]) q
end P202.DeRhamComparison.GridColumns

namespace P202.DeRhamComparison.ConeBridge
open P202.CochainCoverDescent.ConeAlgebra
universe u v
variable {E : Type u} [AddCommGroup E] [Module ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F]

theorem cohomology_subsingleton_of_space_bot (C : Complex E) (n : ℤ)
    (hn : C.space n=⊥) : Subsingleton (C.Cohomology n) := by
  haveI : Subsingleton (C.cycles n) := ⟨fun x y => by
    apply Subtype.ext
    have hx : x.val=0 := by
      have hx : x.val ∈ C.space n := x.property.1
      rw [hn] at hx
      exact hx
    have hy : y.val=0 := by
      have hy : y.val ∈ C.space n := y.property.1
      rw [hn] at hy
      exact hy
    exact hx.trans hy.symm⟩
  infer_instance

theorem map_bijective_of_space_bot {C : Complex E} {D : Complex F} (f : Map C D)
    (n : ℤ) (hC : C.space n=⊥) (hD : D.space n=⊥) :
    Function.Bijective (f.cohomologyMap n) := by
  haveI := cohomology_subsingleton_of_space_bot C n hC
  haveI := cohomology_subsingleton_of_space_bot D n hD
  exact ⟨fun _ _ _ => Subsingleton.elim _ _,fun y => ⟨0,Subsingleton.elim _ _⟩⟩
end P202.DeRhamComparison.ConeBridge


namespace P202.DeRhamComparison.ConeBridge
open SmoothManifolds.MayerVietorisData
open P202.CochainCoverDescent.ConeAlgebra
universe u v w
variable {E : Type u} [AddCommGroup E] [Module ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F]
  (A B : Cochain.{w}) (C : Complex E) (D : Complex F)
  (eA : ∀ q, A.Obj q ≃ₗ[ℝ] C.space (q:ℤ))
  (eB : ∀ q, B.Obj q ≃ₗ[ℝ] D.space (q:ℤ))
  (hdA : ∀ (q : ℕ) (x : A.Obj q), C.differential (q:ℤ) (eA q x).val = (eA (q+1) (A.d q x)).val)
  (hdB : ∀ (q : ℕ) (x : B.Obj q), D.differential (q:ℤ) (eB q x).val = (eB (q+1) (B.d q x)).val)
  (hnegA : C.space (-1) = ⊥) (hnegB : D.space (-1) = ⊥)
  (f : ChainMap A B) (g : Map C D)
  (hfg : ∀ (q : ℕ) (x : A.Obj q), g.map (q:ℤ) (eA q x).val = (eB q (f.map q x)).val)

include eA eB hdA hdB hnegA hnegB hfg in
theorem cohomologyMap_bijective_of_onH_bijective (q : ℕ)
    (hf : Function.Bijective (f.onH q)) : Function.Bijective (g.cohomologyMap (q:ℤ)) := by
  constructor
  · intro x y hxy
    obtain ⟨x,rfl⟩ := (cohomologyEquiv A C eA hdA hnegA q).surjective x
    obtain ⟨y,rfl⟩ := (cohomologyEquiv A C eA hdA hnegA q).surjective y
    congr 1
    apply hf.1
    apply (cohomologyEquiv B D eB hdB hnegB q).injective
    rw [← cohomologyEquiv_natural A B C D eA eB hdA hdB hnegA hnegB f g hfg,
      ← cohomologyEquiv_natural A B C D eA eB hdA hdB hnegA hnegB f g hfg]
    exact hxy
  · intro y
    obtain ⟨z,hz⟩ := hf.2 ((cohomologyEquiv B D eB hdB hnegB q).symm y)
    refine ⟨cohomologyEquiv A C eA hdA hnegA q z,?_⟩
    rw [cohomologyEquiv_natural A B C D eA eB hdA hdB hnegA hnegB f g hfg,hz,
      LinearEquiv.apply_symm_apply]
end P202.DeRhamComparison.ConeBridge


namespace P202.DeRhamComparison
universe u v
open SmoothManifolds.MayerVietorisData SmoothManifolds.MayerVietorisData.OpenForms
open P202Specs.CochainCoverDescent
section LiteralRowIntegration
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1000000
attribute [local irreducible] SmoothManifolds.TangentData.smoothGermAlgebra
  SmoothManifolds.TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)
  {C : CotangentBundle S} {B : ∀ q, FormBundle C q} (K : Calculus C B)
  {ι : Type v} (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)

/-- Actual intrinsic data on each open submanifold, chosen once for every open. -/
def openIntegrationCotangent (W : TopologicalSpace.Opens M) :
    CotangentBundle (openSubmanifold S W) :=
  Classical.choice (BundleOperations.exists_cotangent (openSubmanifold S W))

def openIntegrationBundle (W : TopologicalSpace.Opens M) (q : ℕ) :
    FormBundle (openIntegrationCotangent S W) q :=
  Classical.choice (ExteriorAlgebraResults.exists_formBundle (openIntegrationCotangent S W) q)

def openIntegrationCalculus (W : TopologicalSpace.Opens M) :
    Calculus (openIntegrationCotangent S W) (openIntegrationBundle S W) :=
  Classical.choice (DeRhamResults.complex_exists _ _)

def openIntegrationMap (W : TopologicalSpace.Opens M) :
    IntegrationCochainData.IntegrationMap (openSubmanifold S W) (openIntegrationCalculus S W) :=
  Classical.choice (IntegrationCochain.integration_exists _ _ _ _)

/-- Every literal intersection generator lifts to the actual intrinsic P104
simplex of its intersection. At length zero its cover-small condition is kept. -/
def intersectionIntrinsicSimplex (q k : ℕ) (t : Fin k → ι)
    (σ : IntersectionSimplex S U q k t) :
    SmoothSingularData.SingularSimplex (openSubmanifold S (tupleOpen (coverOpens U) t)) q := by
  let τ : SmoothSimplex S q := ⟨σ.val.val, σ.val.property.1⟩
  let f : SmoothSingularData.Simplex q → tupleOpen (coverOpens U) t :=
    fun x => ⟨(p104Simplex S τ).val x, fun j =>
      σ.property j ⟨SmoothSingularComparison.toBarycentric q x, rfl⟩⟩
  exact ⟨f, simplexSmooth_codRestrict_open S _ _
    (openSubmanifold_restricted_atlas_subset S _) f (p104Simplex S τ).property⟩

@[simp] theorem intersectionIntrinsicSimplex_face (q k : ℕ) (t : Fin k → ι)
    (σ : IntersectionSimplex S U (q+1) k t) (j : Fin (q+2)) :
    intersectionIntrinsicSimplex S U q k t (intersectionFace S U σ j) =
      SmoothSingular.restrict _ (intersectionIntrinsicSimplex S U (q+1) k t σ) j := by
  apply Subtype.ext
  funext x
  apply Subtype.ext
  exact congrFun (congrArg Subtype.val
    (p104Simplex_face S ⟨σ.val.val, σ.val.property.1⟩ j)) x

/-- The actual inclusion of intersections preserves the lifted generator. -/
theorem intersectionIntrinsicSimplex_delete (q k : ℕ) (t : Fin (k+1) → ι)
    (σ : IntersectionSimplex S U q (k+1) t) (j : Fin (k+1)) :
    (openInclusionMap (tupleOpen (coverOpens U) (t ∘ j.succAbove))
      (tupleOpen (coverOpens U) t) (fun _ hx l => hx (j.succAbove l))) ∘
        (intersectionIntrinsicSimplex S U q (k+1) t σ).val =
      (intersectionIntrinsicSimplex S U q k (t ∘ j.succAbove) (deleteIndex S U q σ j)).val := rfl

def intersectionIntrinsicChain (q k : ℕ) (t : Fin k → ι) :
    (IntersectionSimplex S U q k t →₀ ℝ) →ₗ[ℝ]
      SmoothSingularData.Chains (openSubmanifold S (tupleOpen (coverOpens U) t)) q :=
  Finsupp.lmapDomain ℝ ℝ (intersectionIntrinsicSimplex S U q k t)

@[simp] theorem intersectionIntrinsicChain_single (q k : ℕ) (t : Fin k → ι)
    (σ : IntersectionSimplex S U q k t) (r : ℝ) :
    intersectionIntrinsicChain S U q k t (Finsupp.single σ r) =
      Finsupp.single (intersectionIntrinsicSimplex S U q k t σ) r := by
  simp [intersectionIntrinsicChain, Finsupp.lmapDomain_apply]

/-- Integration of the intrinsic pullback of an ambient restricted form,
on the literal smooth-chain basis of its intersection. -/
def tupleIntegration (q k : ℕ) (t : Fin k → ι) :
    formsOn (B q) (tupleOpen (coverOpens U) t) →ₗ[ℝ]
      ((IntersectionSimplex S U q k t →₀ ℝ) →ₗ[ℝ] ℝ) where
  toFun ω := (openIntegrationLinear S K _ (openIntegrationCalculus S _) (openIntegrationMap S _) q ω).comp
    (intersectionIntrinsicChain S U q k t)
  map_add' ω η := by simp only [map_add, LinearMap.add_comp]
  map_smul' r ω := by simp only [map_smul, LinearMap.smul_comp, RingHom.id_apply]

def rowIntegration (q k : ℕ) :
    FormRow (B q) (coverOpens U) k →ₗ[ℝ] IntersectionCochainRow S U q k where
  toFun f t := tupleIntegration S K U q k t (f t)
  map_add' f g := by funext t; exact map_add _ _ _
  map_smul' r f := by
    funext t
    exact (tupleIntegration S K U q k t).map_smul r (f t)

@[simp] theorem rowIntegration_single (q k : ℕ)
    (f : FormRow (B q) (coverOpens U) k) (t : Fin k → ι)
    (σ : IntersectionSimplex S U q k t) :
    rowIntegration S K U q k f t (Finsupp.single σ 1) =
      openIntegrationLinear S K _ (openIntegrationCalculus S _) (openIntegrationMap S _) q
        (f t) (Finsupp.single (intersectionIntrinsicSimplex S U q k t σ) 1) := by
  change openIntegrationLinear S K _ (openIntegrationCalculus S _) (openIntegrationMap S _) q
    (f t) (intersectionIntrinsicChain S U q k t (Finsupp.single σ 1)) = _
  rw [intersectionIntrinsicChain_single]

@[simp] theorem tupleIntegration_single (q k : ℕ) (t : Fin k → ι)
    (ω : formsOn (B q) (tupleOpen (coverOpens U) t))
    (σ : IntersectionSimplex S U q k t) :
    tupleIntegration S K U q k t ω (Finsupp.single σ 1) =
      openIntegrationLinear S K _ (openIntegrationCalculus S _) (openIntegrationMap S _) q
        ω (Finsupp.single (intersectionIntrinsicSimplex S U q k t σ) 1) := by
  change openIntegrationLinear S K _ (openIntegrationCalculus S _) (openIntegrationMap S _) q
    ω (intersectionIntrinsicChain S U q k t (Finsupp.single σ 1)) = _
  rw [intersectionIntrinsicChain_single]

/-- Evaluation on every literal simplex commutes with dropping a cover
index, even when its shorter tuple is the global small-chain augmentation. -/
theorem tupleIntegration_restriction_single (q k : ℕ) (t : Fin (k+1) → ι)
    (σ : IntersectionSimplex S U q (k+1) t) (j : Fin (k+1))
    (ω : formsOn (B q) (tupleOpen (coverOpens U) (t ∘ j.succAbove))) :
    tupleIntegration S K U q (k+1) t
      (formRestriction (B q) (tupleOpen (coverOpens U) (t ∘ j.succAbove))
        (tupleOpen (coverOpens U) t) (fun _ hx l => hx (j.succAbove l)) ω)
      (Finsupp.single σ 1) =
    tupleIntegration S K U q k (t ∘ j.succAbove) ω
      (Finsupp.single (deleteIndex S U q σ j) 1) := by
  rw [tupleIntegration_single, tupleIntegration_single]
  let V := tupleOpen (coverOpens U) (t ∘ j.succAbove)
  let W := tupleOpen (coverOpens U) t
  let hWV : W ≤ V := fun _ hx l => hx (j.succAbove l)
  have h := openIntegrationLinear_restriction S K V (openIntegrationCalculus S V)
    W hWV (openIntegrationCalculus S W) (openIntegrationMap S V) (openIntegrationMap S W) q ω
  have he := congrArg (fun c => c
    (Finsupp.single (intersectionIntrinsicSimplex S U q (k+1) t σ) 1)) h
  change openIntegrationLinear S K W _ _ q (formRestriction (B q) V W hWV ω)
      (Finsupp.single (intersectionIntrinsicSimplex S U q (k+1) t σ) 1) =
    openIntegrationLinear S K V _ _ q ω
      (SmoothSingularData.chainMap _ _ (openInclusionMap V W hWV) q
        (Finsupp.single (intersectionIntrinsicSimplex S U q (k+1) t σ) 1)) at he
  rw [SmoothSingular.chainMap_single, one_smul] at he
  change _ = openIntegrationLinear S K V _ _ q ω
    (SmoothSingularData.generate _
      ((openInclusionMap V W hWV) ∘
        (intersectionIntrinsicSimplex S U q (k+1) t σ).val)) at he
  rw [intersectionIntrinsicSimplex_delete] at he
  have hg : SmoothSingularData.generate (openSubmanifold S V)
      (intersectionIntrinsicSimplex S U q k (t ∘ j.succAbove) (deleteIndex S U q σ j)).val =
        Finsupp.single (intersectionIntrinsicSimplex S U q k (t ∘ j.succAbove)
          (deleteIndex S U q σ j)) 1 :=
    SmoothSingular.generate_simplex (openSubmanifold S V)
      (intersectionIntrinsicSimplex S U q k (t ∘ j.succAbove) (deleteIndex S U q σ j))
  rw [hg] at he
  exact he

/-- Literal integration intertwines the complete alternating restriction
rows, including the augmentation from global forms to cover-small cochains. -/
theorem rowIntegration_horizontal (q k : ℕ)
    (f : FormRow (B q) (coverOpens U) k) :
    intersectionD S U q k (rowIntegration S K U q k f) =
      rowIntegration S K U q (k+1) (formD (B q) (coverOpens U) k f) := by
  funext t
  apply Finsupp.lhom_ext
  intro σ r
  have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
  rw [hr, map_smul, map_smul]
  congr 1
  rw [P202.CochainCoverDescent.intersectionD_alternating]
  change (∑ j : Fin (k+1), (-1 : ℝ)^j.val *
    tupleIntegration S K U q k (t ∘ j.succAbove) (f (t ∘ j.succAbove))
      (Finsupp.single (deleteIndex S U q σ j) 1)) =
    tupleIntegration S K U q (k+1) t
      (∑ j : Fin (k+1), (-1 : ℝ)^j.val •
        formRestriction (B q) (tupleOpen (coverOpens U) (t ∘ j.succAbove))
          (tupleOpen (coverOpens U) t) (fun _ hx l => hx (j.succAbove l))
          (f (t ∘ j.succAbove)))
      (Finsupp.single σ 1)
  rw [map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [tupleIntegration_restriction_single]

/-- Stokes has precisely the same face signs in each literal intersection
column, including length zero and empty open intersections. -/
theorem rowIntegration_vertical (q k : ℕ)
    (f : FormRow (B q) (coverOpens U) k) :
    intersectionV S U q k (rowIntegration S K U q k f) =
      rowIntegration S K U (q+1) k (formV C B (coverOpens U) q k f) := by
  funext t
  apply Finsupp.lhom_ext
  intro σ r
  have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
  rw [hr, map_smul, map_smul]
  congr 1
  rw [P202.CochainCoverDescent.intersectionV_formula, rowIntegration_single]
  let W := tupleOpen (coverOpens U) t
  have hd := openIntegrationLinear_d S K W (openIntegrationCalculus S W)
    (openIntegrationMap S W) q (f t)
  have he := congrArg (fun c => c
    (Finsupp.single (intersectionIntrinsicSimplex S U (q+1) k t σ) 1)) hd
  change openIntegrationLinear S K W _ _ q (f t)
    (SmoothSingularData.boundary _ q
      (Finsupp.single (intersectionIntrinsicSimplex S U (q+1) k t σ) 1)) = _ at he
  rw [SmoothSingular.boundary_single, one_smul, map_sum] at he
  simp only [map_smul, smul_eq_mul] at he
  refine (Finset.sum_congr rfl ?_).trans he
  intro j _
  rw [rowIntegration_single]
  exact congrArg (fun τ => (-1 : ℝ)^j.val *
    openIntegrationLinear S K W (openIntegrationCalculus S W) (openIntegrationMap S W) q
      (f t) (Finsupp.single τ 1)) (intersectionIntrinsicSimplex_face S U q k t σ j)


open P202.CochainCoverDescent.TotalAlgebra

/-- The literal integration map of both augmented commuting bicomplexes.
It uses the same shifted vertical sign on the forms and cochains grids. -/
def integrationDataMap :
    DataMap (P202.CochainCoverDescent.CechTotals.formData C B (coverOpens U))
      (P202.CochainCoverDescent.CechTotals.cochainData S U) := by
  exact GridEmbedding.dataMap _ _ _ _ _ _ _ _ _ _
    (fun p q => rowIntegration S K U q p)
    (fun p q f => rowIntegration_horizontal S K U q p f)
    (by
      intro p q f
      change (-1 : ℝ) • intersectionV S U q p (rowIntegration S K U q p f) =
        rowIntegration S K U (q+1) p ((-1 : ℝ) • formV C B (coverOpens U) q p f)
      rw [map_smul, rowIntegration_vertical])

end LiteralRowIntegration
end P202.DeRhamComparison



namespace P202.DeRhamComparison.ColumnIntegration
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
open SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open SmoothManifolds.MayerVietorisData SmoothManifolds.MayerVietorisData.OpenForms
open P202Specs P202Specs.DeRhamComparison P202Specs.CochainCoverDescent
universe u

/-- The genuine intrinsic smooth singular cochain complex in nonnegative degrees. -/
def intrinsicCochain {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) : Cochain.{u} where
  Obj := SmoothSingularData.Cochains S
  d := SmoothSingularData.coboundary S
  square q x := LinearMap.congr_fun (SmoothSingular.coboundary_squared S q) x

def intrinsicIntegration {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M)
    {C : CotangentBundle S} {B : ∀ q, FormBundle C q} {K : Calculus C B}
    (I : IntegrationCochainData.IntegrationMap S K) :
    ChainMap (globalComplex K) (intrinsicCochain S) where
  map := I.map
  comm q ω := (I.commutes q ω).symm

section Columns
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {ι : Type u}
  (U : SmallChainHomology.OpenCover (TopCat.of M) ι)
  {C : CotangentBundle S} (B : ∀ q, FormBundle C q) (k : ℕ)

def literalFormColumn : Cochain.{u} where
  Obj q := FormRow (B q) (coverOpens U) (k+1)
  d q := formV C B (coverOpens U) q (k+1)
  square q f := (P202.CochainCoverDescent.formsBicomplex S C B ι (coverOpens U)).1 q (k+1) f

def literalCochainColumn : Cochain.{u} where
  Obj q := IntersectionCochainRow S U q (k+1)
  d q := intersectionV S U q (k+1)
  square q f := (P202.CochainCoverDescent.cochainBicomplex S ι U).1 q (k+1) f

def cochainColumnToIntrinsic :
    ChainMap (literalCochainColumn S U k)
      (CochainProducts.product (fun t : Fin (k+1) → ι =>
        intrinsicCochain (openSubmanifold S (tupleOpen (coverOpens U) t)))) where
  map q := (intersectionP104CochainRowEquiv S U q k).toLinearMap
  comm q f := by
    funext t
    exact (intersectionP104CochainEquiv_d S U q k f t).symm

theorem cochainColumnToIntrinsic_bijective (q : ℕ) :
    Function.Bijective ((cochainColumnToIntrinsic S U k).map q) :=
  (intersectionP104CochainRowEquiv S U q k).bijective

variable
  (A : (t : Fin (k+1) → ι) → CotangentBundle (openSubmanifold S (tupleOpen (coverOpens U) t)))
  (E : (t : Fin (k+1) → ι) → ∀ q, FormBundle (A t) q)
  (J : (t : Fin (k+1) → ι) → Calculus (A t) (E t))

def formColumnToIntrinsic :
    ChainMap (literalFormColumn S U B k)
      (CochainProducts.product (fun t : Fin (k+1) → ι => globalComplex (J t))) where
  map q := {
    toFun f t := openIntrinsicFormLinear S (formCalculus C B) (tupleOpen (coverOpens U) t) (J t) q (f t)
    map_add' f g := by funext t; exact map_add _ _ _
    map_smul' r f := by
      funext t
      exact (openIntrinsicFormLinear S (formCalculus C B) (tupleOpen (coverOpens U) t) (J t) q).map_smul r (f t) }
  comm q f := by
    funext t
    exact openIntrinsicFormLinear_d S (formCalculus C B) (tupleOpen (coverOpens U) t) (J t) q (f t)

theorem formColumnToIntrinsic_bijective (q : ℕ) :
    Function.Bijective ((formColumnToIntrinsic S U B k A E J).map q) := by
  have h (t : Fin (k+1) → ι) :
      Function.Bijective (openIntrinsicFormLinear S (formCalculus C B) (tupleOpen (coverOpens U) t) (J t) q) :=
    (openFormsPullbackChain_bijective S (tupleOpen (coverOpens U) t)
      (formCalculus C B) (J t) (formOpenCalculus C B _) q).comp
      (openFormEquiv (formOpenCalculus C B _) q).symm.bijective
  constructor
  · intro f g hfg
    funext t
    exact (h t).1 (congrFun hfg t)
  · intro g
    choose f hf using (fun t => (h t).2 (g t))
    exact ⟨f, funext hf⟩
end Columns

/-- A commuting degreewise square of cochain maps transfers quasi-isomorphism
across actual degreewise linear isomorphisms. -/
theorem onH_bijective_of_square
    {A B A' B' : Cochain.{u}} (f : ChainMap A B) (g : ChainMap A' B')
    (a : ChainMap A A') (b : ChainMap B B')
    (ha : ∀ q, Function.Bijective (a.map q)) (hb : ∀ q, Function.Bijective (b.map q))
    (hsq : ∀ q x, b.map q (f.map q x) = g.map q (a.map q x))
    (hg : ∀ q, Function.Bijective (g.onH q)) :
    ∀ q, Function.Bijective (f.onH q) := by
  intro q
  have haq : Function.Bijective (a.onH q) :=
    (SmoothManifolds.SphereCohomology.cohomologyEquivOfDegreewiseBijective a ha q).bijective
  have hbq : Function.Bijective (b.onH q) :=
    (SmoothManifolds.SphereCohomology.cohomologyEquivOfDegreewiseBijective b hb q).bijective
  have hsqH (x : A.H q) : b.onH q (f.onH q x) = g.onH q (a.onH q x) := by
    obtain ⟨x,rfl⟩ := A.class_surjective q x
    simp only [ChainMap.onH_class]
    congr 1
    apply Subtype.ext
    exact hsq q x.val
  constructor
  · intro x y hxy
    apply haq.1
    apply (hg q).1
    rw [← hsqH, ← hsqH, hxy]
  · intro y
    obtain ⟨x,hx⟩ := (hg q).2 (b.onH q y)
    obtain ⟨z,hz⟩ := haq.2 x
    refine ⟨z,hbq.1 ?_⟩
    rw [hsqH, hz, hx]

end P202.DeRhamComparison.ColumnIntegration



namespace P202.DeRhamComparison
open P202Specs.CochainCoverDescent
universe u v
section PositiveIntegration
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1000000
attribute [local irreducible] SmoothManifolds.TangentData.smoothGermAlgebra SmoothManifolds.TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {ι : Type v}
  (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)

def intersectionSupportedSimplexEquiv (q k : ℕ) (t : Fin (k+1) → ι) :
    IntersectionSimplex S U q (k+1) t ≃ SupportedSmoothSimplex S (tupleOpen (coverOpens U) t) q where
  toFun σ := ⟨⟨σ.val.val, σ.val.property.1⟩, fun _y hy j => σ.property j hy⟩
  invFun σ := ⟨⟨σ.val.val, σ.val.property, t 0, fun _y hy => σ.property hy 0⟩,
    fun j _y hy => σ.property hy j⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual codomain-restricted simplex construction is bijective on
all positive intersections. -/
def intersectionIntrinsicSimplexEquiv (q k : ℕ) (t : Fin (k+1) → ι) :
    IntersectionSimplex S U q (k+1) t ≃
      SmoothSingularData.SingularSimplex (openSubmanifold S (tupleOpen (coverOpens U) t)) q :=
  ((intersectionSupportedSimplexEquiv S U q k t).trans
    (supportedP104SimplexEquiv S (tupleOpen (coverOpens U) t) q)).trans
      (openP104SimplexEquiv S (tupleOpen (coverOpens U) t) _
        (openSubmanifold_restricted_atlas_subset S _) (openSubmanifold_inclusion_smooth S _) q).symm

@[simp] theorem intersectionIntrinsicSimplexEquiv_apply (q k : ℕ) (t : Fin (k+1) → ι)
    (σ : IntersectionSimplex S U q (k+1) t) :
    intersectionIntrinsicSimplexEquiv S U q k t σ = intersectionIntrinsicSimplex S U q (k+1) t σ := rfl

def intersectionIntrinsicChainEquiv (q k : ℕ) (t : Fin (k+1) → ι) :
    (IntersectionSimplex S U q (k+1) t →₀ ℝ) ≃ₗ[ℝ]
      SmoothSingularData.Chains (openSubmanifold S (tupleOpen (coverOpens U) t)) q :=
  Finsupp.domLCongr (intersectionIntrinsicSimplexEquiv S U q k t)

theorem intersectionIntrinsicChainEquiv_apply (q k : ℕ) (t : Fin (k+1) → ι)
    (z : IntersectionSimplex S U q (k+1) t →₀ ℝ) :
    intersectionIntrinsicChainEquiv S U q k t z = intersectionIntrinsicChain S U q (k+1) t z := by
  change Finsupp.domCongr (intersectionIntrinsicSimplexEquiv S U q k t) z =
    Finsupp.mapDomain (intersectionIntrinsicSimplex S U q (k+1) t) z
  exact Finsupp.equivMapDomain_eq_mapDomain _ _

/-- This dual equivalence uses exactly the literal intrinsic simplex used by
row integration, so compatibility holds on every chain. -/
def positiveIntersectionCochainEquiv (q k : ℕ) (t : Fin (k+1) → ι) :
    ((IntersectionSimplex S U q (k+1) t →₀ ℝ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      SmoothSingularData.Cochains (openSubmanifold S (tupleOpen (coverOpens U) t)) q :=
  LinearEquiv.congrLeft ℝ ℝ (intersectionIntrinsicChainEquiv S U q k t)


@[simp] theorem positiveIntersectionCochainEquiv_evaluation (q k : ℕ) (t : Fin (k+1) → ι)
    (f : (IntersectionSimplex S U q (k+1) t →₀ ℝ) →ₗ[ℝ] ℝ)
    (σ : IntersectionSimplex S U q (k+1) t) (r : ℝ) :
    positiveIntersectionCochainEquiv S U q k t f
      (Finsupp.single (intersectionIntrinsicSimplex S U q (k+1) t σ) r) =
        f (Finsupp.single σ r) := by
  change f ((intersectionIntrinsicChainEquiv S U q k t).symm
    (Finsupp.single (intersectionIntrinsicSimplexEquiv S U q k t σ) r)) = _
  unfold intersectionIntrinsicChainEquiv
  rw [← Finsupp.domLCongr_single (R := ℝ), LinearEquiv.symm_apply_apply]

/-- The direct geometric dual equivalence preserves actual coboundary. -/
theorem positiveIntersectionCochainEquiv_d (q k : ℕ) (f : IntersectionCochainRow S U q (k+1))
    (t : Fin (k+1) → ι) :
    positiveIntersectionCochainEquiv S U (q+1) k t (intersectionV S U q (k+1) f t) =
      SmoothSingularData.coboundary (openSubmanifold S (tupleOpen (coverOpens U) t)) q
        (positiveIntersectionCochainEquiv S U q k t (f t)) := by
  let e := intersectionIntrinsicChainEquiv S U (q+1) k t
  have he :
      (positiveIntersectionCochainEquiv S U (q+1) k t (intersectionV S U q (k+1) f t)).comp e.toLinearMap =
      (SmoothSingularData.coboundary (openSubmanifold S (tupleOpen (coverOpens U) t)) q
        (positiveIntersectionCochainEquiv S U q k t (f t))).comp e.toLinearMap := by
    apply Finsupp.lhom_ext
    intro σ r
    have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hr,map_smul,map_smul]
    congr 1
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show e (Finsupp.single σ 1) =
      Finsupp.single (intersectionIntrinsicSimplex S U (q+1) (k+1) t σ) 1 by
        exact Finsupp.domLCongr_single _ _ _]
    rw [positiveIntersectionCochainEquiv_evaluation]
    change intersectionV S U q (k+1) f t (Finsupp.single σ 1) =
      positiveIntersectionCochainEquiv S U q k t (f t)
        (SmoothSingularData.boundary _ q
          (Finsupp.single (intersectionIntrinsicSimplex S U (q+1) (k+1) t σ) 1))
    rw [SmoothSingular.boundary_single, one_smul, map_sum]
    simp only [map_smul, smul_eq_mul, ← intersectionIntrinsicSimplex_face]
    rw [(P202.CochainCoverDescent.cochainBicomplex S ι U).2.2 q (k+1) f t σ]
    simp only [positiveIntersectionCochainEquiv_evaluation]
  apply LinearMap.ext
  intro z
  obtain ⟨w,rfl⟩ := e.surjective z
  exact LinearMap.congr_fun he w

variable {C : CotangentBundle S} {B : ∀ q, FormBundle C q} (K : Calculus C B)

theorem positiveIntersectionCochainEquiv_integration (q k : ℕ)
    (f : FormRow (B q) (coverOpens U) (k+1)) (t : Fin (k+1) → ι) :
    positiveIntersectionCochainEquiv S U q k t (rowIntegration S K U q (k+1) f t) =
      openIntegrationLinear S K _ (openIntegrationCalculus S _) (openIntegrationMap S _) q (f t) := by
  apply LinearMap.ext
  intro z
  change openIntegrationLinear S K _ (openIntegrationCalculus S _) (openIntegrationMap S _) q (f t)
    (intersectionIntrinsicChain S U q (k+1) t ((intersectionIntrinsicChainEquiv S U q k t).symm z)) = _
  rw [← intersectionIntrinsicChainEquiv_apply, LinearEquiv.apply_symm_apply]
end PositiveIntegration
end P202.DeRhamComparison


set_option maxHeartbeats 5000000
namespace P202.DeRhamComparison.ColumnIntegration
attribute [local irreducible] SmoothManifolds.TangentData.smoothGermAlgebra SmoothManifolds.TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
open SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData SmoothManifolds.MayerVietorisData
open P202Specs P202Specs.DeRhamComparison
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)

def intrinsicDegreeEquiv (q : ℕ) : SmoothSingularData.Cochains S q ≃ₗ[ℝ]
    (SmoothSingularComparison.smoothCochains S).X (q:ℤ) :=
  (((smoothDegreeIso S q).toLinearEquiv.trans (p104ChainEquiv S q)).arrowCongr
    (LinearEquiv.refl ℝ ℝ)).symm

@[simp] theorem intrinsicDegreeEquiv_evaluate {q : ℕ} (c : SmoothSingularData.Cochains S q)
    (σ : SmoothSimplex S q) :
    evaluateSmoothCochain S (intrinsicDegreeEquiv S q c) σ =
      c (Finsupp.single (p104Simplex S σ) 1) := by
  change c (p104ChainEquiv S q ((smoothDegreeIso S q).hom
    ((smoothDegreeIso S q).inv (smoothGenerator S σ)))) = _
  rw [Iso.inv_hom_id_apply,p104ChainEquiv_generator]

theorem intrinsicDegreeEquiv_d (q : ℕ) (c : SmoothSingularData.Cochains S q) :
    (SmoothSingularComparison.smoothCochains S).d (q:ℤ) ((q:ℤ)+1)
      (intrinsicDegreeEquiv S q c) =
        intrinsicDegreeEquiv S (q+1) (SmoothSingularData.coboundary S q c) := by
  apply smoothCochain_ext S
  intro σ
  change evaluateSmoothCochain S ((SmoothSingularComparison.smoothCochains S).d (q:ℤ) (q+1:ℕ) (intrinsicDegreeEquiv S q c)) σ = _
  rw [evaluateSmoothCochain_coboundary,intrinsicDegreeEquiv_evaluate]
  simp only [intrinsicDegreeEquiv_evaluate]
  change _ = c (SmoothSingularData.boundary S q (Finsupp.single (p104Simplex S σ) 1))
  rw [SmoothSingular.boundary_single]
  simp only [one_smul,map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [p104Simplex_face]
  rfl

 def intrinsicCohomologyEquiv (q : ℕ) : (intrinsicCochain S).H q ≃ₗ[ℝ]
    (SmoothSingularComparison.smoothCochains S).homology (q:ℤ) :=
  CategoricalBridge.cohomologyEquiv (intrinsicCochain S) _ (intrinsicDegreeEquiv S)
    (intrinsicDegreeEquiv_d S) (smoothCochain_d_neg_one_zero S) q

 theorem intrinsicIntegration_comparison {C : CotangentBundle S} {B : ∀ q, FormBundle C q}
    {K : Calculus C B} (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ)
    (x : K.Cohomology q) :
    intrinsicCohomologyEquiv S q ((intrinsicIntegration S I).onH q x) =
      smoothIntegrationCohomology S I q x := by
  obtain ⟨ω,rfl⟩ := (K.boundaries q).mkQ_surjective x
  change intrinsicCohomologyEquiv S q ((intrinsicCochain S).classOf q
    ((intrinsicIntegration S I).onClosed q ω)) = smoothIntegrationCohomology S I q (K.classOf q ω)
  change CategoricalBridge.cohomologyEquiv _ _ _ _ _ q
    ((intrinsicCochain S).classOf q ((intrinsicIntegration S I).onClosed q ω)) = _
  rw [CategoricalBridge.cohomologyEquiv_class]
  rw [P202.UniversalCoefficientsCohomology.cycleClass_eq]
  rw [smoothIntegrationCohomology_class]
  congr 1
  apply (ModuleCat.mono_iff_injective ((SmoothSingularComparison.smoothCochains S).iCycles (q:ℤ))).mp inferInstance
  rw [integrationToCycles_i]
  have h := congrArg (fun f => f
    (CategoricalBridge.closedEquiv (intrinsicCochain S) _ (intrinsicDegreeEquiv S)
      (intrinsicDegreeEquiv_d S) q ((intrinsicIntegration S I).onClosed q ω)))
    ((SmoothSingularComparison.smoothCochains S).sc (q:ℤ)).moduleCatCyclesIso_inv_iCycles
  simp only [ModuleCat.comp_apply] at h
  exact h.trans rfl

 theorem intrinsicIntegration_onH_bijective {C : CotangentBundle S} {B : ∀ q, FormBundle C q}
    {K : Calculus C B} (I : IntegrationCochainData.IntegrationMap S K) (q : ℕ)
    (h : Function.Bijective (smoothIntegrationCohomology S I q)) :
    Function.Bijective ((intrinsicIntegration S I).onH q) := by
  constructor
  · intro x y hxy
    apply h.1
    rw [← intrinsicIntegration_comparison,← intrinsicIntegration_comparison,hxy]
  · intro y
    obtain ⟨x,hx⟩ := h.2 (intrinsicCohomologyEquiv S q y)
    refine ⟨x, (intrinsicCohomologyEquiv S q).injective ?_⟩
    rw [intrinsicIntegration_comparison,hx]
end P202.DeRhamComparison.ColumnIntegration


namespace P202.DeRhamComparison.GridColumns
open P202.CochainCoverDescent.TotalAlgebra
universe u v
variable {E : Type u} [AddCommGroup E] [Module ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F]

theorem columnMap_bijective_all {A : Data E} {B : Data F} (f : DataMap A B) (p : ℤ)
    (hf : ∀ q : ℕ, Function.Bijective ((f.columnMap p).cohomologyMap (q:ℤ)))
    (n : ℤ) : Function.Bijective ((f.columnMap p).cohomologyMap n) := by
  cases n with
  | ofNat q => exact hf q
  | negSucc q =>
    apply ConeBridge.map_bijective_of_space_bot
    · simp only [Data.columnComplex,if_neg (show ¬0 ≤ Int.negSucc q by omega)]
    · simp only [Data.columnComplex,if_neg (show ¬0 ≤ Int.negSucc q by omega)]
end P202.DeRhamComparison.GridColumns


namespace P202.DeRhamComparison.ColumnIntegration
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
open SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open SmoothManifolds.MayerVietorisData SmoothManifolds.MayerVietorisData.OpenForms
open P202Specs P202Specs.DeRhamComparison P202Specs.CochainCoverDescent
universe u
section LocalColumnIntegration
attribute [local irreducible] SmoothManifolds.TangentData.smoothGermAlgebra
  SmoothManifolds.TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 5000000
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {ι : Type u}
  (U : SmallChainHomology.OpenCover (TopCat.of M) ι)
  {C : CotangentBundle S} {B : ∀ q, FormBundle C q} (K : Calculus C B) (k : ℕ)

def positiveCochainColumnToIntrinsic :
    ChainMap (literalCochainColumn S U k)
      (CochainProducts.product (fun t : Fin (k+1) → ι =>
        intrinsicCochain (openSubmanifold S (tupleOpen (coverOpens U) t)))) where
  map q := (LinearEquiv.piCongrRight (fun t => positiveIntersectionCochainEquiv S U q k t)).toLinearMap
  comm q f := by
    funext t
    exact (positiveIntersectionCochainEquiv_d S U q k f t).symm

theorem positiveCochainColumnToIntrinsic_bijective (q : ℕ) :
    Function.Bijective ((positiveCochainColumnToIntrinsic S U k).map q) :=
  (LinearEquiv.piCongrRight (fun t => positiveIntersectionCochainEquiv S U q k t)).bijective

def canonicalFormColumnToIntrinsic :
    ChainMap (literalFormColumn S U B k)
      (CochainProducts.product (fun t : Fin (k+1) → ι => globalComplex
        (openIntegrationCalculus S (tupleOpen (coverOpens U) t)))) where
  map q := {
    toFun f t := openIntrinsicFormLinear S K (tupleOpen (coverOpens U) t)
      (openIntegrationCalculus S _) q (f t)
    map_add' f g := by funext t; exact map_add _ _ _
    map_smul' r f := by
      funext t
      exact (openIntrinsicFormLinear S K (tupleOpen (coverOpens U) t)
        (openIntegrationCalculus S _) q).map_smul r (f t) }
  comm q f := by
    funext t
    exact openIntrinsicFormLinear_d S K (tupleOpen (coverOpens U) t) (openIntegrationCalculus S _) q (f t)

theorem canonicalFormColumnToIntrinsic_bijective (q : ℕ) :
    Function.Bijective ((canonicalFormColumnToIntrinsic S U K k).map q) := by
  have h (t : Fin (k+1) → ι) : Function.Bijective
      (fun ω : formsOn (B q) (tupleOpen (coverOpens U) t) =>
        openIntrinsicFormLinear S K (tupleOpen (coverOpens U) t) (openIntegrationCalculus S _) q ω) :=
    (openFormsPullbackChain_bijective S (tupleOpen (coverOpens U) t) K
      (openIntegrationCalculus S _) (formOpenCalculus C B _) q).comp
      (openFormEquiv (formOpenCalculus C B _) q).symm.bijective
  constructor
  · intro f g hfg
    funext t
    exact (h t).1 (congrFun hfg t)
  · intro g
    choose f hf using (fun t => (h t).2 (g t))
    exact ⟨f,funext hf⟩

/-- Literal integration on a positive intersection column is a genuine
cochain map with exactly the given exterior and singular differentials. -/
def literalColumnIntegration : ChainMap (literalFormColumn S U B k) (literalCochainColumn S U k) where
  map q := rowIntegration S K U q (k+1)
  comm q f := by
    simpa only [literalFormColumn, literalCochainColumn] using!
      rowIntegration_vertical S K U q (k+1) f

/-- Pointwise local integration quasi-isomorphisms imply the literal product
column integration quasi-isomorphism, with no cardinality restriction. -/
theorem literalColumnIntegration_onH_bijective
    (hlocal : ∀ (t : Fin (k+1) → ι) q, Function.Bijective
      ((intrinsicIntegration (openSubmanifold S (tupleOpen (coverOpens U) t))
        (openIntegrationMap S _)).onH q)) :
    ∀ q, Function.Bijective ((literalColumnIntegration S U K k).onH q) := by
  let g := CochainProducts.productMap (fun t : Fin (k+1) → ι =>
    intrinsicIntegration (openSubmanifold S (tupleOpen (coverOpens U) t)) (openIntegrationMap S _))
  apply onH_bijective_of_square (literalColumnIntegration S U K k) g
    (canonicalFormColumnToIntrinsic S U K k) (positiveCochainColumnToIntrinsic S U k)
    (canonicalFormColumnToIntrinsic_bijective S U K k)
    (positiveCochainColumnToIntrinsic_bijective S U k)
  · intro q f
    funext t
    exact positiveIntersectionCochainEquiv_integration S U K q k f t
  · exact CochainProducts.productMap_onH_bijective _ hlocal
end LocalColumnIntegration
end P202.DeRhamComparison.ColumnIntegration


namespace P202.DeRhamComparison
universe u v
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
open SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open P202Specs P202Specs.DeRhamComparison
open SmoothManifolds.MayerVietorisData SmoothManifolds.MayerVietorisData.OpenForms
open P202Specs.CochainCoverDescent
open P202.CochainCoverDescent.TotalAlgebra P202.CochainCoverDescent.CechTotals
section GlobalSquare
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1000000
attribute [local irreducible] SmoothManifolds.TangentData.smoothGermAlgebra
  SmoothManifolds.TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)
  {C : CotangentBundle S} {B : ∀ q, FormBundle C q} (K : Calculus C B)
  (I : IntegrationCochainData.IntegrationMap S K)
  {ι : Type v} (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)

theorem rowIntegration_augmentation_generator (q : ℕ) (ω : K.forms q)
    (σ : IntersectionSimplex S U q 0 Fin.elim0) :
    rowIntegration S K U q 0
        ((P202.CochainCoverDescent.Augmentation.formAugmentationEquiv K (coverOpens U) q).symm ω)
        Fin.elim0 (Finsupp.single σ 1) =
      evaluateSmoothCochain S (integrationInDegree S I q ω) ⟨σ.val.val,σ.val.property.1⟩ := by
  rw [rowIntegration_single,integrationInDegree_evaluation]
  let W := tupleOpen (coverOpens U) (Fin.elim0 : Fin 0 → ι)
  let J := openIntegrationCalculus S W
  let H := openIntegrationMap S W
  let ωrow := ((P202.CochainCoverDescent.Augmentation.formAugmentationEquiv K (coverOpens U) q).symm ω) Fin.elim0
  let β := openIntrinsicFormLinear S K W J q ωrow
  have hβ : β.val = FormPullbackData.pullbackField (openSubmanifold S W) S Subtype.val
      (fun p => (openInclusionTangentEquiv S W p).toLinearMap) ω.val := by
    funext p
    rw [openIntrinsicFormLinear_field]
    rfl
  have h := IntegrationCochain.integrationMap_pullback
    (openSubmanifold S W) S (openIntegrationCotangent S W) C
    (openIntegrationBundle S W) B J K H I Subtype.val
    (openSubmanifold_inclusion_smooth S W)
    (fun p => (openInclusionTangentEquiv S W p).toLinearMap)
    (fun p => openInclusionTangentEquiv_isDifferential S W p) q ω β hβ
  have he := congrArg (fun c => c (Finsupp.single (intersectionIntrinsicSimplex S U q 0 Fin.elim0 σ) 1)) h
  change openIntegrationLinear S K W J H q ωrow
      (Finsupp.single (intersectionIntrinsicSimplex S U q 0 Fin.elim0 σ) 1) =
    I.map q ω (SmoothSingularData.chainMap (openSubmanifold S W) S Subtype.val q
      (Finsupp.single (intersectionIntrinsicSimplex S U q 0 Fin.elim0 σ) 1)) at he
  rw [SmoothSingular.chainMap_single,one_smul] at he
  change _ = I.map q ω (SmoothSingularData.generate S
    (Subtype.val ∘ (intersectionIntrinsicSimplex S U q 0 Fin.elim0 σ).val)) at he
  have hs : Subtype.val ∘ (intersectionIntrinsicSimplex S U q 0 Fin.elim0 σ).val =
      (p104Simplex S ⟨σ.val.val,σ.val.property.1⟩).val := rfl
  rw [hs] at he
  have hgen : SmoothSingularData.generate S
      (p104Simplex S ⟨σ.val.val,σ.val.property.1⟩).val =
      Finsupp.single (p104Simplex S ⟨σ.val.val,σ.val.property.1⟩) 1 :=
    SmoothSingular.generate_simplex S _
  rw [hgen,I.evaluation] at he
  exact he

open CoverAssembly

theorem rowIntegration_augmentation (q : ℕ) (ω : K.forms q) :
    rowIntegration S K U q 0
      ((P202.CochainCoverDescent.Augmentation.formAugmentationEquiv K (coverOpens U) q).symm ω) =
      smallCochainRowEquiv S U q
        ((smallSmoothRestriction S U).f (q:ℤ) (integrationInDegree S I q ω)) := by
  funext t
  have ht : t=Fin.elim0 := Subsingleton.elim _ _
  subst t
  apply Finsupp.lhom_ext
  intro σ r
  have hr : Finsupp.single σ r=r • Finsupp.single σ 1 := by simp
  rw [hr,map_smul,map_smul]
  congr 1
  rw [rowIntegration_augmentation_generator S K I U,
    smallCochainRowEquiv_restriction_generator]

theorem integrationDataMap_augmentation_degree (q : ℕ) (ω : K.forms q) :
    (augmentationSourceMap (integrationDataMap S K U)).map (q:ℤ)
      (formGlobalAugmentationEquiv K (coverOpens U) q ω).val =
      (smallCochainAugmentationEquiv S U q
        ((smallSmoothRestriction S U).f (q:ℤ) (integrationInDegree S I q ω))).val := by
  change GridEmbedding.mapAmbient (fun p q => rowIntegration S K U q p)
      (formGlobalAugmentationEquiv K (coverOpens U) q ω).val = _
  rw [formGlobalAugmentationEquiv_val, smallCochainAugmentationEquiv_val,
    GridEmbedding.mapAmbient_embed,rowIntegration_augmentation S K I U]

end GlobalSquare
end P202.DeRhamComparison


namespace P202.DeRhamComparison
universe u v
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
open SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open P202Specs P202Specs.DeRhamComparison
open SmoothManifolds.MayerVietorisData
open P202.CochainCoverDescent.TotalAlgebra P202.CochainCoverDescent.CechTotals
open CoverAssembly
section CoverLocality
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M)
  {C : CotangentBundle S} {B : ∀ q, FormBundle C q} (K : Calculus C B)
  (I : IntegrationCochainData.IntegrationMap S K)
  {ι : Type v} (U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι)

def integrationModelMap : ChainMap (globalComplex K)
    (nonnegativeModel (SmoothSingularComparison.smoothCochains S)) where
  map := integrationInDegree S I
  comm q ω := (integrationInDegree_commutes S I q ω).symm

def smallIntegrationModelMap : ChainMap (globalComplex K)
    (nonnegativeModel (smallSmoothCochains S U)) where
  map q := ((smallSmoothRestriction S U).f (q:ℤ)).hom.comp (integrationInDegree S I q)
  comm q ω := by
    change (smallSmoothCochains S U).d (q:ℤ) (q+1:ℕ)
      ((smallSmoothRestriction S U).f (q:ℤ) (integrationInDegree S I q ω)) =
      (smallSmoothRestriction S U).f (q+1:ℕ) (integrationInDegree S I (q+1) (K.d q ω))
    have h := congrArg (fun f => f (integrationInDegree S I q ω))
      ((smallSmoothRestriction S U).comm (q:ℤ) (q+1:ℕ))
    simp only [ModuleCat.comp_apply] at h
    exact h.trans (congrArg ((smallSmoothRestriction S U).f (q+1:ℕ))
      (integrationInDegree_commutes S I q ω).symm)

theorem integrationModelMap_cohomology (q : ℕ) (x : K.Cohomology q) :
    nonnegativeCohomologyEquiv (SmoothSingularComparison.smoothCochains S)
      (smoothCochain_d_neg_one_zero S) q ((integrationModelMap S K I).onH q x) =
      smoothIntegrationCohomology S I q x := by
  obtain ⟨ω,rfl⟩ := (K.boundaries q).mkQ_surjective x
  have hclass := (integrationModelMap S K I).onH_class q ω
  change (integrationModelMap S K I).onH q (K.classOf q ω) = _ at hclass
  change nonnegativeCohomologyEquiv (SmoothSingularComparison.smoothCochains S)
    (smoothCochain_d_neg_one_zero S) q
    ((integrationModelMap S K I).onH q (K.classOf q ω)) = _
  rw [hclass]
  change _ = (SmoothSingularComparison.smoothCochains S).homologyπ (q:ℤ)
    (integrationToCycles S I q ω)
  dsimp only [nonnegativeCohomologyEquiv]
  rw [CategoricalBridge.cohomologyEquiv_class,
    P202.UniversalCoefficientsCohomology.cycleClass_eq]
  congr 1
  apply (ModuleCat.mono_iff_injective
    ((SmoothSingularComparison.smoothCochains S).iCycles (q:ℤ))).mp inferInstance
  rw [integrationToCycles_i]
  have h := congrArg (fun f => f
    (CategoricalBridge.closedEquiv
      (nonnegativeModel (SmoothSingularComparison.smoothCochains S))
      (SmoothSingularComparison.smoothCochains S)
      (fun q => LinearEquiv.refl ℝ _) (fun _ _ => rfl) q
      ((integrationModelMap S K I).onClosed q ω)))
    ((SmoothSingularComparison.smoothCochains S).sc (q:ℤ)).moduleCatCyclesIso_inv_iCycles
  exact h

theorem smallIntegrationModelMap_cohomology (q : ℕ) (x : K.Cohomology q) :
    nonnegativeCohomologyEquiv (smallSmoothCochains S U)
      (smallSmoothCochain_d_neg_one_zero S U) q
      ((smallIntegrationModelMap S K I U).onH q x) =
      homologyMap (smallSmoothRestriction S U) (q:ℤ)
        (smoothIntegrationCohomology S I q x) := by
  have hcomp : (smallIntegrationModelMap S K I U).onH q x =
      (nonnegativeModelMap (smallSmoothRestriction S U)).onH q
        ((integrationModelMap S K I).onH q x) := by
    obtain ⟨ω,rfl⟩ := (K.boundaries q).mkQ_surjective x
    have hsmall := (smallIntegrationModelMap S K I U).onH_class q ω
    have hfull := (integrationModelMap S K I).onH_class q ω
    change (smallIntegrationModelMap S K I U).onH q (K.classOf q ω) = _ at hsmall
    change (integrationModelMap S K I).onH q (K.classOf q ω) = _ at hfull
    change (smallIntegrationModelMap S K I U).onH q (K.classOf q ω) =
      (nonnegativeModelMap (smallSmoothRestriction S U)).onH q
        ((integrationModelMap S K I).onH q (K.classOf q ω))
    rw [hsmall,hfull,(nonnegativeModelMap (smallSmoothRestriction S U)).onH_class]
    congr 1
  exact (congrArg (nonnegativeCohomologyEquiv (smallSmoothCochains S U)
    (smallSmoothCochain_d_neg_one_zero S U) q) hcomp).trans
      ((nonnegativeCohomologyEquiv_natural (smallSmoothRestriction S U)
        (smoothCochain_d_neg_one_zero S) (smallSmoothCochain_d_neg_one_zero S U) q
        ((integrationModelMap S K I).onH q x)).trans
          (congrArg (homologyMap (smallSmoothRestriction S U) (q:ℤ))
            (integrationModelMap_cohomology S K I q x)))

/-- Descent for literal integration on an arbitrary open cover. The only
local hypothesis is quasi-isomorphism of the actual positive columns. -/
theorem smoothIntegration_bijective_of_cover_columns
    (hcol : ∀ p : ℕ, ∀ m : ℤ,
      Function.Bijective (((integrationDataMap S K U).positiveMap.columnMap (p:ℤ)).cohomologyMap m))
    (q : ℕ) : Function.Bijective (smoothIntegrationCohomology S I q) := by
  have hsource : Function.Bijective
      ((augmentationSourceMap (integrationDataMap S K U)).cohomologyMap (q:ℤ)) := by
    apply augmentationSourceMap_bijective_of_columns _
      P202.CochainCoverDescent.columnTotalComparison
    · intro m
      exact (formData C B (coverOpens U)).augmentation_quasiIso
        (formData_rows_exact C B (coverOpens U) U.covers) m
    · intro m
      exact (cochainData S U).augmentation_quasiIso (cochainData_rows_exact S U) m
    · exact hcol
  have hsmall : Function.Bijective ((smallIntegrationModelMap S K I U).onH q) := by
    apply ConeBridge.onH_bijective_of_cohomologyMap_bijective
      (globalComplex K) (nonnegativeModel (smallSmoothCochains S U))
      (formData C B (coverOpens U)).augmentationComplex
      (cochainData S U).augmentationComplex
      (formGlobalAugmentationEquiv K (coverOpens U))
      (smallCochainAugmentationEquiv S U)
      (formGlobalAugmentationEquiv_d K (coverOpens U))
      (smallCochainAugmentationEquiv_d S U)
      (by simp [Data.augmentationComplex]) (by simp [Data.augmentationComplex])
      (smallIntegrationModelMap S K I U)
      (augmentationSourceMap (integrationDataMap S K U))
      (integrationDataMap_augmentation_degree S K I U) q hsource
  haveI := smallSmoothRestriction_cohomology_isIso S U (q:ℤ)
  have hr := (ConcreteCategory.isIso_iff_bijective
    (homologyMap (smallSmoothRestriction S U) (q:ℤ))).mp inferInstance
  let e := nonnegativeCohomologyEquiv (smallSmoothCochains S U)
    (smallSmoothCochain_d_neg_one_zero S U) q
  constructor
  · intro x y hxy
    apply hsmall.1
    apply e.injective
    exact (smallIntegrationModelMap_cohomology S K I U q x).trans
      ((congrArg (homologyMap (smallSmoothRestriction S U) (q:ℤ)) hxy).trans
        (smallIntegrationModelMap_cohomology S K I U q y).symm)
  · intro y
    obtain ⟨x,hx⟩ := hsmall.2 (e.symm (homologyMap (smallSmoothRestriction S U) (q:ℤ) y))
    refine ⟨x,hr.1 ?_⟩
    exact (smallIntegrationModelMap_cohomology S K I U q x).symm.trans
      ((congrArg e hx).trans (e.apply_symm_apply _))

end CoverLocality
end P202.DeRhamComparison




namespace P202.DeRhamComparison.GridColumns
open P202.CochainCoverDescent.TotalAlgebra
open P202.CochainCoverDescent.TotalAlgebra.GridEmbedding
universe u
variable {C : ℕ → ℕ → Type u} [∀ p q, AddCommGroup (C p q)] [∀ p q, Module ℝ (C p q)]

def degreeEquivForData (D : Data (Ambient C)) (hs : D.space=space C) (p q : ℕ) :
    C (p+1) q ≃ₗ[ℝ] (D.positiveData.columnComplex (p:ℤ)).space (q:ℤ) :=
  (spaceEquiv C (p+1) q).trans (LinearEquiv.ofEq _ _ (by
    simp only [Data.columnComplex,ite_eq_left (Int.natCast_nonneg q),Int.toNat_natCast,
      Data.positiveData,ite_eq_left (Int.natCast_nonneg p),hs]
    have he : (p:ℤ)+1=(p+1:ℕ) := by omega
    rw [he]))

@[simp] theorem degreeEquivForData_val (D : Data (Ambient C)) (hs : D.space=space C)
    (p q : ℕ) (z : C (p+1) q) :
    (degreeEquivForData D hs p q z).val=embed C (p+1) q z := rfl

/-- Degreewise differentiation for the shifted signed grid, proved for an
arbitrary family of real vector spaces before any geometric specialization. -/
theorem degreeEquivForData_d (D : Data (Ambient C)) (hs : D.space=space C)
    (v : ∀ p q, C p q →ₗ[ℝ] C p (q+1))
    (hv : D.vertical=vertical C (fun p q => (-1:ℝ) • v p q))
    (p q : ℕ) (z : C (p+1) q) :
    (D.positiveData.columnComplex (p:ℤ)).differential (q:ℤ)
      (degreeEquivForData D hs p q z).val =
        (degreeEquivForData D hs p (q+1) (v (p+1) q z)).val := by
  change -(D.vertical (embed C (p+1) q z)) = embed C (p+1) (q+1) (v (p+1) q z)
  rw [hv,vertical_embed,LinearMap.smul_apply,map_smul,neg_one_smul,neg_neg]

end P202.DeRhamComparison.GridColumns

namespace P202.DeRhamComparison.ColumnIntegration
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
open SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open SmoothManifolds.MayerVietorisData
open P202Specs P202Specs.CochainCoverDescent
open P202.CochainCoverDescent.TotalAlgebra
open P202.CochainCoverDescent.TotalAlgebra.GridEmbedding
open P202.CochainCoverDescent.CechTotals
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {ι : Type u}
  (U : SmallChainHomology.OpenCover (TopCat.of M) ι)
  {C : CotangentBundle S} {B : ∀ q, FormBundle C q} (K : Calculus C B)
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1000000
attribute [local irreducible] SmoothManifolds.TangentData.smoothGermAlgebra
  SmoothManifolds.TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false

theorem positiveColumnMap_bijective (k : ℕ)
    (hf : ∀ q, Function.Bijective ((literalColumnIntegration S U K k).onH q)) :
    ∀ m : ℤ, Function.Bijective
      ((((integrationDataMap S K U).positiveMap).columnMap (k:ℤ)).cohomologyMap m) := by
  apply GridColumns.columnMap_bijective_all
  intro q
  let A := literalFormColumn S U B k
  let D := literalCochainColumn S U k
  let F := formData C B (coverOpens U)
  let G := cochainData S U
  let eF : ∀ q, A.Obj q ≃ₗ[ℝ] (F.positiveData.columnComplex (k:ℤ)).space (q:ℤ) :=
    fun q => GridColumns.degreeEquivForData F rfl k q
  let eG : ∀ q, D.Obj q ≃ₗ[ℝ] (G.positiveData.columnComplex (k:ℤ)).space (q:ℤ) :=
    fun q => GridColumns.degreeEquivForData G rfl k q
  have hdF : ∀ q (x : A.Obj q),
      (F.positiveData.columnComplex (k:ℤ)).differential (q:ℤ) (eF q x).val =
        (eF (q+1) (A.d q x)).val := by
    intro q x
    exact GridColumns.degreeEquivForData_d F rfl
      (fun p q => formV C B (coverOpens U) q p) rfl k q x
  have hdG : ∀ q (x : D.Obj q),
      (G.positiveData.columnComplex (k:ℤ)).differential (q:ℤ) (eG q x).val =
        (eG (q+1) (D.d q x)).val := by
    intro q x
    exact GridColumns.degreeEquivForData_d G rfl
      (fun p q => intersectionV S U q p) rfl k q x
  apply ConeBridge.cohomologyMap_bijective_of_onH_bijective A D
    (F.positiveData.columnComplex (k:ℤ)) (G.positiveData.columnComplex (k:ℤ))
    eF eG hdF hdG
    (by simp only [Data.columnComplex,ite_eq_right (show ¬0≤(-1:ℤ) by omega)])
    (by simp only [Data.columnComplex,ite_eq_right (show ¬0≤(-1:ℤ) by omega)])
    (literalColumnIntegration S U K k)
    (((integrationDataMap S K U).positiveMap).columnMap (k:ℤ))
    (fun q x => by
      change mapAmbient (fun p q => rowIntegration S K U q p)
        (embed (fun p q => FormRow (B q) (coverOpens U) p) (k+1) q x) =
          embed (fun p q => IntersectionCochainRow S U q p) (k+1) q
            (rowIntegration S K U q (k+1) x)
      exact mapAmbient_embed _ _ _ _) q (hf q)
end P202.DeRhamComparison.ColumnIntegration


namespace P202.DeRhamComparison
open CategoryTheory HomologicalComplex
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
open SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
open SmoothManifolds.ExteriorData SmoothManifolds.DeRhamData
open P202Specs P202Specs.DeRhamComparison P202Specs.CochainCoverDescent
universe u
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1000000
attribute [local irreducible] SmoothManifolds.TangentData.smoothGermAlgebra
  SmoothManifolds.TangentData.pointDerivations
set_option backward.isDefEq.respectTransparency.types false

/-- The concrete integration morphism satisfies the open-cover closure
property used in both geometric globalization steps. -/
theorem integrationCoverLocality_of_smoothSingularComparison
    (hcomp : P202Specs.SmoothSingularComparison.smoothSingularComparison_type.{u}) :
    IntegrationCoverLocality.{u} := by
  intro n M _ S ι V hcover hlocal C B K
  let U : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) ι := {
    sets i := V i
    isOpen i := (V i).isOpen
    covers := hcover }
  obtain ⟨I⟩ := IntegrationCochain.integration_exists S C B K
  refine integrationComparisonOfBijective S I (fun q => (hcomp.1 S (q:ℤ)).2) ?_
  intro q
  apply smoothIntegration_bijective_of_cover_columns S K I U ?_ q
  intro p
  apply ColumnIntegration.positiveColumnMap_bijective S U K p
  apply ColumnIntegration.literalColumnIntegration_onH_bijective S U K p
  intro t q
  let W := tupleOpen (coverOpens U) t
  obtain ⟨e, he⟩ := hlocal p t (openIntegrationCotangent S W)
    (openIntegrationBundle S W) (openIntegrationCalculus S W)
  exact ColumnIntegration.intrinsicIntegration_onH_bijective (openSubmanifold S W)
    (openIntegrationMap S W) q
    (smoothIntegrationCohomology_bijective_of_comparison (openSubmanifold S W)
      (openIntegrationMap S W) e he q)

/-- Actual open-cover locality for integration, with no comparison premise. -/
theorem integrationCoverLocality : IntegrationCoverLocality.{u} :=
  integrationCoverLocality_of_smoothSingularComparison
    P202.SmoothSingularComparison.smoothSingularComparison

/-- Integration on the actual intrinsic forms, followed by the inverse of
actual smooth-singular restriction, gives the natural ordinary real
cohomology isomorphism on every manifold in the original scope. -/
theorem deRhamComparison : P202Specs.DeRhamComparison.deRhamComparison_type.{u} :=
  deRhamComparison_of_coverLocality P202.SmoothSingularComparison.smoothSingularComparison
    integrationCoverLocality

end P202.DeRhamComparison
