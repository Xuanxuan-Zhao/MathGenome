import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Comparison.SmoothSingularComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularSubdivision
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficients
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SmallChainHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.MayerVietoris
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.InteriorHomotopyEquivalence
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.FiniteProperEmbedding
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.SmoothingHomotopies
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Proof progress for Lemma `lem:p202-smooth-singular`.
The smooth subcomplex uses the shared ordinary singular basis and the actual
P104 corner-extension convention. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory HomologicalComplex Opposite
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
namespace P202.SmoothSingularComparison
open P202Specs.SmoothSingularComparison P202Specs.SingularChains
universe u
variable {n m : ℕ} {a b : SmoothManifolds.ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]

/-- The smooth complex is literally a degreewise submodule of ordinary chains. -/
theorem inclusion_injective (S : SmoothManifold n a M) (q : ℕ) :
    Function.Injective ((inclusion S).f q) := Subtype.val_injective

/-- If the supported simplex set is all simplices, the actual inclusion
is an isomorphism of chain complexes. -/
theorem inclusion_isIso_of_forall_smooth (S : SmoothManifold n a M)
    (h : ∀ (q : ℕ) (σ : Simplex (TopCat.of M) q), IsSmoothSimplex S q σ) :
    IsIso (inclusion S) := by
  have hinc (q : ℕ) : IsIso ((inclusion S).f q) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨Subtype.val_injective, fun z => ⟨⟨z, fun σ _ => h q σ⟩, rfl⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

theorem inclusion_natural (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : SmoothManifolds.MapData.IsSmoothMap S T f) :
    smoothChainMap S T f hf ≫ inclusion T =
      inclusion S ≫ chainMap ℝ ℝ (underlyingMap S T f hf) := by
  ext q z
  rfl

theorem ordinaryInclusion_natural (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : SmoothManifolds.MapData.IsSmoothMap S T f) :
    smoothOrdinaryMap S T f hf ≫ ordinaryInclusion T =
      ordinaryInclusion S ≫ (ordinaryFunctor ℝ ℝ).map (underlyingMap S T f hf) := by
  change extendMap (smoothChainMap S T f hf) (degreeEmbedding 0) ≫
      extendMap (inclusion T) (degreeEmbedding 0) =
    extendMap (inclusion S) (degreeEmbedding 0) ≫
      extendMap (chainMap ℝ ℝ (underlyingMap S T f hf)) (degreeEmbedding 0)
  rw [← extendMap_comp, ← extendMap_comp, inclusion_natural]

theorem restriction_natural (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (hf : SmoothManifolds.MapData.IsSmoothMap S T f) :
    (P202Specs.CohomologyPairs.ordinaryCochainFunctor ℝ ℝ).map
        (underlyingMap S T f hf).op ≫ restriction S =
      restriction T ≫ smoothCochainMap S T f hf := by
  change (P202Specs.CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).map
      ((ordinaryFunctor ℝ ℝ).map (underlyingMap S T f hf)).op ≫
      (P202Specs.CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).map
        (ordinaryInclusion S).op = _
  rw [← Functor.map_comp, ← op_comp, ← ordinaryInclusion_natural]
  rw [op_comp, Functor.map_comp]
  rfl

/-- Naturality on both homology and cohomology is independent of proving that
the comparison maps are isomorphisms. -/
theorem comparison_natural : comparisonNaturality_type.{u} := by
  intro n m a b M N _ _ S T f hf q
  constructor
  · change homologyMap (smoothOrdinaryMap S T f hf) q ≫
      homologyMap (ordinaryInclusion T) q =
        homologyMap (ordinaryInclusion S) q ≫
          homologyMap ((ordinaryFunctor ℝ ℝ).map (underlyingMap S T f hf)) q
    rw [← homologyMap_comp, ← homologyMap_comp, ordinaryInclusion_natural]
  · change homologyMap ((P202Specs.CohomologyPairs.ordinaryCochainFunctor ℝ ℝ).map
      (underlyingMap S T f hf).op) q ≫ homologyMap (restriction S) q =
        homologyMap (restriction T) q ≫ homologyMap (smoothCochainMap S T f hf) q
    rw [← homologyMap_comp, ← homologyMap_comp, restriction_natural]

/-- Every degree-zero continuous simplex is smooth, including for manifolds
with boundary. This is a statement about chain groups, not yet about H₀. -/
theorem degreeZero_smooth (S : SmoothManifold n a M) (σ : Simplex (TopCat.of M) 0) :
    IsSmoothSimplex S 0 σ := by
  letI : Subsingleton (CornerSimplex 0) := SmoothManifolds.SmoothSingular.simplex_zero.2
  refine ⟨((simplexEquiv (TopCat.of M) 0 σ).continuous.comp
    (continuous_toBarycentric 0)), ?_⟩
  intro x d _ _
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _,
    (fun _ => (d (simplexEquiv (TopCat.of M) 0 σ (toBarycentric 0 x))).val),
      contDiff_const.contDiffOn, ?_⟩
  apply Filter.Eventually.of_forall
  intro y
  rw [Subsingleton.elim y x]
  rfl

theorem smoothModule_zero (S : SmoothManifold n a M) : smoothModule S 0 = ⊤ := by
  apply top_unique
  intro z _ σ _
  exact degreeZero_smooth S σ

/-- All degrees of both comparison maps on the empty manifold. -/
theorem empty_comparison (S : SmoothManifold n a M) [IsEmpty M] (q : ℤ) :
    IsIso (homologyMap (ordinaryInclusion S) q) ∧
      IsIso (homologyMap (restriction S) q) := by
  have hσ (k : ℕ) : IsEmpty (Simplex (TopCat.of M) k) := by
    refine ⟨fun σ => ?_⟩
    exact isEmptyElim (simplexEquiv (TopCat.of M) k σ (Convexity.StdSimplex.single 0))
  have hinc (k : ℕ) : IsIso ((inclusion S).f k) := by
    letI := hσ k
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · exact Subtype.val_injective
    · intro z
      have hz : z = 0 := by
        apply Finsupp.ext
        intro σ
        exact isEmptyElim σ
      exact ⟨0, by simpa using hz.symm⟩
  letI : IsIso (inclusion S) := HomologicalComplex.Hom.isIso_of_components _
  letI : IsIso (ordinaryInclusion S) :=
    (degreeEmbedding 0).extendFunctor (ModuleCat ℝ) |>.map_isIso (inclusion S)
  letI : IsIso (restriction S) :=
    (P202Specs.CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).map_isIso
      (ordinaryInclusion S).op
  exact ⟨inferInstance, inferInstance⟩

section Duality
open P202Specs.UniversalCoefficients

/-- The field-dual argument, for arbitrary complexes and all integer degrees.
It uses the accepted evaluation theorem on unrestricted algebraic duals. -/
theorem dual_homology_isIso_of_isIso
    {C D : ChainComplex (ModuleCat.{u} ℝ) ℤ} (f : D ⟶ C) (q : ℤ)
    [IsIso (homologyMap f q)] :
    IsIso (homologyMap
      ((P202Specs.CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).map f.op) q) := by
  let E := (P202Specs.CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).map f.op
  let e := (asIso (homologyMap f q)).toLinearEquiv
  have hC := P202.UniversalCoefficients.evaluation_bijective ℝ C q
  have hD := P202.UniversalCoefficients.evaluation_bijective ℝ D q
  have hn (a : (dualChain ℝ ℝ C).homology q) (z : D.homology q) :
      evaluation ℝ ℝ D q (homologyMap E q a) z =
        evaluation ℝ ℝ C q a (homologyMap f q z) := by
    have h := P202.UniversalCoefficientsCohomology.evaluation_natural
      ℝ ℝ ℝ f LinearMap.id q a z
    rw [P202.UniversalCoefficientsCohomology.dualMap_id] at h
    exact h
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hC.1
    ext z
    obtain ⟨w, rfl⟩ := (ConcreteCategory.isIso_iff_bijective (homologyMap f q)).mp inferInstance |>.2 z
    rw [← hn, ← hn, hab]
  · intro b
    obtain ⟨a, ha⟩ := hC.2 ((evaluation ℝ ℝ D q b).comp e.symm.toLinearMap)
    refine ⟨a, hD.1 ?_⟩
    ext z
    rw [hn, ha]
    change evaluation ℝ ℝ D q b (e.symm (e z)) = _
    rw [e.symm_apply_apply]

/-- Cohomology comparison reduces to homology comparison, without a finite
rank hypothesis or any assumption about the comparison's conclusion. -/
theorem cohomology_comparison_of_homology (S : SmoothManifold n a M) (q : ℤ)
    [IsIso (homologyMap (ordinaryInclusion S) q)] :
    IsIso (homologyMap (restriction S) q) :=
  dual_homology_isIso_of_isIso (ordinaryInclusion S) q

end Duality

/-- Once the homology comparison in nonnegative degrees is established, all
of the original homology/cohomology conclusions and naturality follow. This is
only an assembly lemma; its premise remains an outstanding obligation. -/
theorem comparison_from_homology
    (h : ∀ {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
      (S : SmoothManifold n a M) (q : ℕ), IsIso (homologyMap (inclusion S) q)) :
    smoothSingularComparison_type.{u} := by
  refine ⟨?_, comparison_natural⟩
  intro n a M _ S q
  haveI : QuasiIso (inclusion S) := by
    rw [quasiIso_iff]
    intro k
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr (h S k)
  haveI : QuasiIso (ordinaryInclusion S) := by
    change QuasiIso (extendMap (inclusion S) (degreeEmbedding 0))
    infer_instance
  haveI : IsIso (homologyMap (ordinaryInclusion S) q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  exact ⟨inferInstance, cohomology_comparison_of_homology S q⟩

section Boundary
open SmoothManifolds.BoundaryData SmoothManifolds.InteriorHomotopyData

/-- The actual interior inclusion, without replacing the manifold structure. -/
def interiorInclusion (S : SmoothManifold n a M) :
    TopCat.of (manifoldInterior S) ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The actual smooth inward push from P104 supplies a homotopy inverse to the
interior inclusion on the shared ordinary singular homology. The smooth-chain
prism restriction is still needed to finish the smooth boundary comparison. -/
theorem interior_ordinary_homology (S : SmoothManifold n a M) (q : ℤ) :
    IsIso ((homologyFunctor ℝ ℝ q).map (interiorInclusion S)) := by
  obtain ⟨e⟩ := SmoothManifolds.InteriorHomotopies.interior_inclusion_homotopy_equivalence S
  let p : TopCat.of M ⟶ TopCat.of (manifoldInterior S) :=
    TopCat.ofHom ⟨e.inverse, continuous_iff_continuousAt.mpr
      (fun x => (e.smooth_inverse x).1)⟩
  let hM : TopCat.Homotopy (𝟙 (TopCat.of M)) (p ≫ interiorInclusion S) := {
    toFun := e.homotopy
    continuous_toFun := e.smooth_homotopy.1
    map_zero_left := e.homotopy_zero
    map_one_left := e.homotopy_one }
  let hI : TopCat.Homotopy (𝟙 (TopCat.of (manifoldInterior S))) (interiorInclusion S ≫ p) := {
    toFun := fun z => ⟨e.homotopy (z.1, z.2.val), e.preserves_interior z.1 z.2⟩
    continuous_toFun := e.smooth_restricted_homotopy.1
    map_zero_left := fun x => Subtype.ext (e.homotopy_zero x.val)
    map_one_left := fun x => Subtype.ext (e.homotopy_one x.val) }
  exact (P202.PrismHomotopy.equivalence ℝ ℝ (interiorInclusion S) p hI.symm hM.symm q).1

end Boundary

section AffineRestrictions
open Convexity P202Specs.SingularSubdivision
open SmoothManifolds.CornerData

/-- Ambient formula for every affine simplex map used by subdivision. -/
def affineAmbient {p q : ℕ} (t : Fin (p+1) → Delta q) : Euclidean p → Euclidean q :=
  fun x j => ∑ i : Fin (p+1), simplexBarycentric x i * (t i).weights j.succ

theorem affineAmbient_smooth {p q : ℕ} (t : Fin (p+1) → Delta q) :
    ContDiff ℝ (⊤ : ℕ∞) (affineAmbient t) := by
  apply contDiff_pi.mpr
  intro j
  apply ContDiff.sum
  intro i _
  exact ((contDiff_apply ℝ (fun _ : Fin (p+1) => ℝ) i).comp
    (SmoothManifolds.CornerExamples.contDiff_barycentric p)).mul contDiff_const

theorem affineSimplexMap_weights {p q : ℕ} (t : Fin (p+1) → Delta q)
    (x : Delta p) (j : Fin (q+1)) :
    (affineSimplexMap t x).weights j = ∑ i : Fin (p+1), x.weights i * (t i).weights j := by
  simp only [affineSimplexMap, ContinuousMap.coe_mk, StdSimplex.affineMapMk_apply,
    iConvexComb, StdSimplex.weights_sConvexComb, Finsupp.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  rw [StdSimplex.weights_map, Finsupp.sum_mapDomain_index]
  · rw [Finsupp.sum_fintype _ _ (by simp)]
  · intro y; simp
  · intro y r s; exact add_mul r s _

theorem affineSimplexMap_toCorner {p q : ℕ} (t : Fin (p+1) → Delta q)
    (x : CornerSimplex p) :
    (toCorner q (affineSimplexMap t (toBarycentric p x))).val = affineAmbient t x.val := by
  funext j
  rw [toCorner_val, affineSimplexMap_weights]
  rfl

/-- Every affine reparametrization of a smooth simplex remains smooth.
This includes the simplex pieces in subdivision and its homotopy. -/
theorem isSmoothSimplex_affine {p q : ℕ} (S : SmoothManifold n a M)
    {σ : Simplex (TopCat.of M) q} (hσ : IsSmoothSimplex S q σ)
    (t : Fin (p+1) → Delta q) :
    IsSmoothSimplex S p ((simplexEquiv (TopCat.of M) p).symm
      ((simplexEquiv (TopCat.of M) q σ).comp (affineSimplexMap t))) := by
  let g : CornerSimplex p → CornerSimplex q :=
    fun x => toCorner q (affineSimplexMap t (toBarycentric p x))
  have hg : ∀ x, (g x).val = affineAmbient t x.val := affineSimplexMap_toCorner t
  have h := SmoothManifolds.SmoothSingular.smooth_precompose hσ g
    (affineAmbient t) (affineAmbient_smooth t) hg
  unfold IsSmoothSimplex
  have heq : (⇑((simplexEquiv (TopCat.of M) p)
      ((simplexEquiv (TopCat.of M) p).symm
        ((simplexEquiv (TopCat.of M) q σ).comp (affineSimplexMap t)))) ∘ toBarycentric p) =
      ((simplexEquiv (TopCat.of M) q σ ∘ toBarycentric q) ∘ g) := by
    funext x
    simp [g, Function.comp_def]
  rw [heq]
  exact h

/-- Evaluating any finite affine chain in a smooth simplex gives a smooth chain. -/
theorem evaluate_mem_smoothModule {p q : ℕ} (S : SmoothManifold n a M)
    {σ : Simplex (TopCat.of M) q} (hσ : IsSmoothSimplex S q σ)
    (c : AffineChains ℝ (Delta q) (p+1)) :
    evaluate ℝ σ p c ∈ smoothModule S p := by
  classical
  intro τ hτ
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hτ)
  exact isSmoothSimplex_affine S hσ t

/-- The actual shared subdivision operator restricts to smooth chains. -/
theorem subdivision_mem_smoothModule (S : SmoothManifold n a M) (q : ℕ)
    (z : smoothModule S q) :
    subdivision ℝ (TopCat.of M) q z.val ∈ smoothModule S q := by
  classical
  rw [subdivision, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro σ hσ
  exact Submodule.smul_mem _ _ (evaluate_mem_smoothModule S (z.property hσ) _)

/-- The actual shared subdivision homotopy also restricts to smooth chains. -/
theorem subdivisionHomotopy_mem_smoothModule (S : SmoothManifold n a M) (q : ℕ)
    (z : smoothModule S q) :
    P202Specs.SingularSubdivision.homotopy ℝ (TopCat.of M) q z.val ∈ smoothModule S (q+1) := by
  classical
  rw [P202Specs.SingularSubdivision.homotopy, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro σ hσ
  exact Submodule.smul_mem _ _ (evaluate_mem_smoothModule S (z.property hσ) _)

/-- Concrete restricted subdivision, retaining the shared operator on underlying chains. -/
def smoothSubdivision (S : SmoothManifold n a M) (q : ℕ) :
    smoothModule S q →ₗ[ℝ] smoothModule S q :=
  ((subdivision ℝ (TopCat.of M) q).comp (smoothModule S q).subtype).codRestrict
    (smoothModule S q) (subdivision_mem_smoothModule S q)

def smoothSubdivisionHomotopy (S : SmoothManifold n a M) (q : ℕ) :
    smoothModule S q →ₗ[ℝ] smoothModule S (q+1) :=
  ((P202Specs.SingularSubdivision.homotopy ℝ (TopCat.of M) q).comp
    (smoothModule S q).subtype).codRestrict
      (smoothModule S (q+1)) (subdivisionHomotopy_mem_smoothModule S q)

end AffineRestrictions
section SmallChains
open P202Specs.SmallChainHomology P202Specs.SingularSubdivision
open P202.SmallChainHomology
universe w
variable {ι : Type w}

/-- Smooth chains whose every simplex lies in some covering member. -/
def smallSmoothModule (S : SmoothManifold n a M) (U : OpenCover (TopCat.of M) ι) (q : ℕ) :=
  smoothModule S q ⊓ smallModule ℝ U q

theorem boundary_mem_smallSmoothModule (S : SmoothManifold n a M)
    (U : OpenCover (TopCat.of M) ι) (q : ℕ)
    (z : smallSmoothModule S U (q+1)) :
    boundary ℝ ℝ (TopCat.of M) q z.val ∈ smallSmoothModule S U q :=
  ⟨boundary_mem_smoothModule S q z.val z.property.1,
    P202Specs.SmallChainHomology.boundary_mem_smallModule ℝ U q z.val z.property.2⟩

def smallSmoothComplex (S : SmoothManifold n a M) (U : OpenCover (TopCat.of M) ι) :
    ChainComplex (ModuleCat.{u} ℝ) ℕ :=
  ChainComplex.of (fun q => ModuleCat.of ℝ (smallSmoothModule S U q))
    (fun q => ModuleCat.ofHom (((boundary ℝ ℝ (TopCat.of M) q).comp
      (smallSmoothModule S U (q+1)).subtype).codRestrict (smallSmoothModule S U q)
        (boundary_mem_smallSmoothModule S U q)))
    (by
      intro q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun f => f z.val)
        ((complex ℝ ℝ (TopCat.of M)).d_comp_d (q+2) (q+1) q))

def smallSmoothInclusion (S : SmoothManifold n a M) (U : OpenCover (TopCat.of M) ι) :
    smallSmoothComplex S U ⟶ smoothComplex S :=
  ChainComplex.ofHom
    (fun q => ModuleCat.ofHom (((smallSmoothModule S U q).subtype).codRestrict
      (smoothModule S q) (fun z => z.property.1)))
    (by
      intro q
      simp only [smallSmoothComplex, smoothComplex, ChainComplex.of_d]
      rfl)

theorem iterateSubdivision_smooth (S : SmoothManifold n a M) (q k : ℕ)
    (z : smoothModule S q) :
    iterateSubdivision ℝ (TopCat.of M) q k z.val ∈ smoothModule S q := by
  induction k with
  | zero => exact z.property
  | succ k ih =>
    rw [iterateSubdivision_succ]
    exact subdivision_mem_smoothModule S q ⟨_, ih⟩

theorem iterateHomotopy_smooth (S : SmoothManifold n a M) (q k : ℕ)
    (z : smoothModule S q) :
    iterateHomotopy ℝ (TopCat.of M) q k z.val ∈ smoothModule S (q+1) := by
  induction k with
  | zero => simpa only [iterateHomotopy_zero] using (smoothModule S (q+1)).zero_mem
  | succ k ih =>
    rw [iterateHomotopy_succ]
    exact (smoothModule S (q+1)).add_mem ih
      (subdivisionHomotopy_mem_smoothModule S q ⟨_, iterateSubdivision_smooth S q k z⟩)

/-- The smooth version of small-chain comparison, for every indexed open cover.
No smooth/continuous comparison theorem is used. -/
theorem smallSmoothComparison (S : SmoothManifold n a M)
    (U : OpenCover (TopCat.of M) ι) (q : ℕ) :
    IsIso (homologyMap (smallSmoothInclusion S U) q) := by
  have hsmall (k : ℕ) (z : Chains ℝ (TopCat.of M) k) :
      ∃ m, IsSmall U.sets (iterateSubdivision ℝ (TopCat.of M) k m z) :=
    eventualSmall_of_generators ℝ (TopCat.of M) U k
      (P202.SmallChainSubdivision.eventualSmall_generator ℝ (TopCat.of M)
        U.sets U.isOpen U.covers k) z
  let f := smallSmoothInclusion S U
  apply (quasiIsoAt_iff_isIso_homologyMap f q).mp
  apply (quasiIsoAt_iff' f (q+1) q (q-1) (by simp) (by cases q <;> simp)).mpr
  apply (ShortComplex.quasiIso_iff _).mpr
  apply shortComplex_comparison
  · intro z hz
    change smoothModule S q at z
    change (smoothComplex S).d q (q-1) z = 0 at hz
    obtain ⟨k, hk⟩ := hsmall q z.val
    let y : smallSmoothModule S U q :=
      ⟨iterateSubdivision ℝ (TopCat.of M) q k z.val,
        iterateSubdivision_smooth S q k z, hk⟩
    refine ⟨y, ?_, ⟨iterateHomotopy ℝ (TopCat.of M) q k z.val,
      iterateHomotopy_smooth S q k z⟩, ?_⟩
    · change (smallSmoothComplex S U).d q (q-1) y = 0
      cases q with
      | zero => rw [(smallSmoothComplex S U).shape _ _ (by simp)]; rfl
      | succ q =>
        change (smallSmoothComplex S U).d (q+1) q y = 0
        simp only [smallSmoothComplex, ChainComplex.of_d]
        apply Subtype.ext
        change chainDifferential ℝ (TopCat.of M) q
          (iterateSubdivision ℝ (TopCat.of M) (q+1) k z.val) = 0
        rw [iterateSubdivision_boundary]
        change (smoothComplex S).d (q+1) q z = 0 at hz
        simp only [smoothComplex, ChainComplex.of_d] at hz
        have hz' : chainDifferential ℝ (TopCat.of M) q z.val = 0 :=
          congrArg Subtype.val hz
        rw [hz', map_zero]
    · change (smallSmoothInclusion S U).f q y - (show (smoothComplex S).X q from z) =
        (smoothComplex S).d (q+1) q
          ⟨iterateHomotopy ℝ (TopCat.of M) q k z.val, iterateHomotopy_smooth S q k z⟩
      simp only [smoothComplex, ChainComplex.of_d]
      apply Subtype.ext
      change iterateSubdivision ℝ (TopCat.of M) q k z.val - z.val =
        chainDifferential ℝ (TopCat.of M) q (iterateHomotopy ℝ (TopCat.of M) q k z.val)
      symm
      cases q with
      | zero => exact iterateHomotopy_identity_zero ℝ (TopCat.of M) k z.val
      | succ q =>
        change (smoothComplex S).d (q+1) q z = 0 at hz
        simp only [smoothComplex, ChainComplex.of_d] at hz
        have hz' : chainDifferential ℝ (TopCat.of M) q z.val = 0 :=
          congrArg Subtype.val hz
        simpa only [hz', map_zero, add_zero] using
          iterateHomotopy_identity ℝ (TopCat.of M) q k z.val
  · intro x hx c hc
    change smallSmoothModule S U q at x
    change smoothModule S (q+1) at c
    change (smallSmoothComplex S U).d q (q-1) x = 0 at hx
    change (smoothComplex S).d (q+1) q c = (smallSmoothInclusion S U).f q x at hc
    simp only [smoothComplex, ChainComplex.of_d] at hc
    have hc' : chainDifferential ℝ (TopCat.of M) q c.val = x.val :=
      congrArg Subtype.val hc
    obtain ⟨k, hk⟩ := hsmall (q+1) c.val
    let y := iterateSubdivision ℝ (TopCat.of M) (q+1) k c.val -
      iterateHomotopy ℝ (TopCat.of M) q k x.val
    have hy : y ∈ smallSmoothModule S U (q+1) := by
      constructor
      · exact (smoothModule S (q+1)).sub_mem
          (iterateSubdivision_smooth S (q+1) k c)
          (iterateHomotopy_smooth S q k ⟨x.val, x.property.1⟩)
      · exact (smallModule ℝ U (q+1)).sub_mem hk
          (iterateHomotopy_small ℝ (TopCat.of M) U q k x.val x.property.2)
    refine ⟨⟨y, hy⟩, ?_⟩
    change (smallSmoothComplex S U).d (q+1) q ⟨y, hy⟩ = x
    simp only [smallSmoothComplex, ChainComplex.of_d]
    apply Subtype.ext
    change chainDifferential ℝ (TopCat.of M) q y = x.val
    dsimp only [y]
    rw [map_sub, iterateSubdivision_boundary, hc']
    have hi : chainDifferential ℝ (TopCat.of M) q
        (iterateHomotopy ℝ (TopCat.of M) q k x.val) =
        iterateSubdivision ℝ (TopCat.of M) q k x.val - x.val := by
      cases q with
      | zero => exact iterateHomotopy_identity_zero ℝ (TopCat.of M) k x.val
      | succ q =>
        change (smallSmoothComplex S U).d (q+1) q x = 0 at hx
        simp only [smallSmoothComplex, ChainComplex.of_d] at hx
        have hz' : chainDifferential ℝ (TopCat.of M) q x.val = 0 :=
          congrArg Subtype.val hx
        simpa only [hz', map_zero, add_zero] using
          iterateHomotopy_identity ℝ (TopCat.of M) q k x.val
    rw [hi]
    abel

end SmallChains

section SmoothPrism
open SmoothManifolds.InteriorHomotopyData SmoothManifolds.MapData
open SmoothManifolds.SmoothSingularData
open Set Filter
open scoped _root_.Topology Simplicial

/-- A smooth cylinder evaluated on a smooth simplex and a smooth ambient time
function has local extensions at all corners, also at time zero and one. -/
theorem smoothHomotopy_simplex (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    {H : HomotopyTime × M → N}
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H)
    {p : ℕ} {σ : CornerSimplex p → M} (hσ : SimplexSmooth S σ)
    (t : CornerSimplex p → HomotopyTime) (τ : Euclidean p → ℝ)
    (hτ : ContDiff ℝ (⊤ : ℕ∞) τ) (ht : ∀ x, (t x).val = τ x.val) :
    SimplexSmooth T (fun x => H (t x, σ x)) := by
  have htc : Continuous t := by
    apply continuous_induced_rng.mpr
    simpa only [Function.comp_def, ht] using hτ.continuous.comp continuous_subtype_val
  have hpair : Continuous (fun x => (t x, σ x)) := htc.prodMk hσ.1
  refine ⟨hH.1.comp hpair, ?_⟩
  intro x d hd hdx
  obtain ⟨e, he, hxe⟩ := S.smoothStructure.property.1.1 (σ x)
  have houter := SmoothManifolds.LocalCoordinateExtension.precomp
    (hH.2 e he d hd (t x, σ x) hxe hdx) hpair.continuousAt rfl
  apply SmoothManifolds.LocalCoordinateExtension.comp houter
  obtain ⟨U, hU, hxU, F, hF, hFeq⟩ := hσ.2 x e he hxe
  refine ⟨U, hU, hxU, (fun y => Fin.cons (τ y) (F y)), ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hτ.contDiffOn
    · exact (contDiffOn_pi.mp hF) j
  · filter_upwards [hFeq] with y hy
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (ht y).symm
    · exact congrFun hy j

open Convexity P202Specs.SingularSubdivision
open CategoryTheory.MonoidalCategory

/-- An ordered simplex map is the affine map on its images of the vertices. -/
theorem simplexMap_affine {p q : ℕ} (f : Fin (p+1) → Fin (q+1)) (x : Delta p) :
    affineSimplexMap (fun i => StdSimplex.single (f i)) x = StdSimplex.map f x := by
  have h : StdSimplex.affineMapMk (R := ℝ) (fun i => StdSimplex.single (f i)) =
      StdSimplex.affineMap f := by
    apply StdSimplex.affineMap_ext
    intro i
    simp
  exact congrArg (fun g => g x) h

/-- Explicit affine realization of a singular cylinder. This construction avoids
any choice of a triangulation or smooth structure on the target product. -/
def affineCylinder {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    TopCat.toSSet.obj X ⊗ Δ[1] ⟶ TopCat.toSSet.obj Y where
  app k := ↾fun z => (TopCat.toSSetObjEquiv Y k).symm
    ⟨fun x => H (StdSimplex.homeomorphI
      (StdSimplex.map (SSet.stdSimplex.objEquiv z.2) x),
      TopCat.toSSetObjEquiv X k z.1 x),
      H.continuous.comp ((StdSimplex.homeomorphI.continuous.comp
        (by fun_prop)).prodMk (TopCat.toSSetObjEquiv X k z.1).continuous)⟩
  naturality k l α := by
    ext z
    apply (TopCat.toSSetObjEquiv Y l).injective
    ext x
    symm
    change H (StdSimplex.homeomorphI
        (StdSimplex.map (SSet.stdSimplex.objEquiv z.2) (StdSimplex.map α.unop x)),
        TopCat.toSSetObjEquiv X k z.1 (StdSimplex.map α.unop x)) =
      H (StdSimplex.homeomorphI
        (StdSimplex.map (α.unop ≫ SSet.stdSimplex.objEquiv z.2) x),
        TopCat.toSSetObjEquiv X k z.1 (StdSimplex.map α.unop x))
    congr 3
    exact (StdSimplex.map_comp x _ _).symm

/-- The explicit cylinder has the prescribed endpoint maps. -/
def affineSimplicialHomotopy {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) : SSet.Homotopy (TopCat.toSSet.map f) (TopCat.toSSet.map g) where
  h := affineCylinder H
  h₀ := by
    ext k z
    apply (TopCat.toSSetObjEquiv Y k).injective
    ext x
    change H (StdSimplex.homeomorphI (StdSimplex.map (fun _ => 0) x),
        TopCat.toSSetObjEquiv X k z x) = f (TopCat.toSSetObjEquiv X k z x)
    simp
  h₁ := by
    ext k z
    apply (TopCat.toSSetObjEquiv Y k).injective
    ext x
    change H (StdSimplex.homeomorphI (StdSimplex.map (fun _ => 1) x),
        TopCat.toSSetObjEquiv X k z x) = g (TopCat.toSSetObjEquiv X k z x)
    simp
  rel := by ext k ⟨⟨_, ⟨⟩⟩, _⟩

/-- The positive prism induced by the explicit affine cylinder. -/
def affineChainPrism {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    _root_.Homotopy (chainMap ℝ ℝ g) (chainMap ℝ ℝ f) :=
  ((affineSimplicialHomotopy H).toSimplicialObjectHomotopy.whiskerRight
    (finsuppFunctor ℝ ℝ)).toChainHomotopy.symm

/-- Formula for each prism simplex in barycentric coordinates. -/
theorem affinePrismSimplex_formula {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (q : ℕ) (i : Fin (q+1))
    (σ : P202Specs.SingularChains.Simplex X q) (x : Delta (q+1)) :
    simplexEquiv Y (q+1)
        ((affineSimplicialHomotopy H).toSimplicialObjectHomotopy.h i σ) x =
      H (StdSimplex.homeomorphI (StdSimplex.map
        (SSet.stdSimplex.objEquiv (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc)) x),
        simplexEquiv X q σ (StdSimplex.map i.predAbove x)) := by
  change simplexEquiv Y (q+1) ((affineCylinder H).app (op ⦋q+1⦌)
    ((SSet.yonedaEquiv.symm σ ▷ Δ[1]).app _
      (SSet.prodStdSimplex₁.nonDegenerateEquiv i).val)) x = _
  rfl

/-- Every affine piece of a smooth prism satisfies the full corner extension test. -/
theorem affinePrismSimplex_smooth (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    {f g : TopCat.of M ⟶ TopCat.of N} (H : TopCat.Homotopy f g)
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H)
    (q : ℕ) (i : Fin (q+1)) {σ : P202Specs.SingularChains.Simplex (TopCat.of M) q}
    (hσ : IsSmoothSimplex S q σ) :
    IsSmoothSimplex T (q+1)
      ((affineSimplicialHomotopy H).toSimplicialObjectHomotopy.h i σ) := by
  let v : Fin (q+2) → Delta q := fun j => StdSimplex.single (i.predAbove j)
  let w : Fin (q+2) → Delta 1 := fun j => StdSimplex.single
    (SSet.stdSimplex.objEquiv (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) j)
  let t : CornerSimplex (q+1) → HomotopyTime := fun x =>
    StdSimplex.homeomorphI (StdSimplex.map
      (SSet.stdSimplex.objEquiv (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc))
      (toBarycentric (q+1) x))
  have ht (x : CornerSimplex (q+1)) : (t x).val = affineAmbient w x.val 0 := by
    change (StdSimplex.map
      (SSet.stdSimplex.objEquiv (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc))
      (toBarycentric (q+1) x)).weights 1 = _
    rw [← simplexMap_affine]
    exact congrFun (affineSimplexMap_toCorner w x) 0
  have hτ : ContDiff ℝ (⊤ : ℕ∞) (fun x => affineAmbient w x 0) :=
    (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).comp (affineAmbient_smooth w)
  have hσ' := isSmoothSimplex_affine S hσ v
  have hh := smoothHomotopy_simplex S T hH hσ' t _ hτ ht
  unfold IsSmoothSimplex
  convert hh using 1
  funext x
  rw [Function.comp_apply, affinePrismSimplex_formula]
  congr 1
  congr 1
  change simplexEquiv (TopCat.of M) q σ (StdSimplex.map i.predAbove (toBarycentric (q+1) x)) =
    simplexEquiv (TopCat.of M) q σ (affineSimplexMap v (toBarycentric (q+1) x))
  exact congrArg (simplexEquiv (TopCat.of M) q σ)
    (simplexMap_affine i.predAbove (toBarycentric (q+1) x)).symm

/-- The prism is supported on smooth simplices in every degree. -/
theorem affineChainPrism_smooth (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    {f g : TopCat.of M ⟶ TopCat.of N} (H : TopCat.Homotopy f g)
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H)
    (i j : ℕ) (z : smoothModule S i) :
    (affineChainPrism H).hom i j z.val ∈ smoothModule T j := by
  classical
  by_cases hij : i+1 = j
  · subst j
    simp only [affineChainPrism, Homotopy.symm_hom,
      CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy,
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      neg_neg, ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply,
      LinearMap.smul_apply]
    change (∑ k : Fin (i+1), (-1 : ℤ)^k.val •
      Finsupp.mapDomain ((affineSimplicialHomotopy H).toSimplicialObjectHomotopy.h k)
        z.val) ∈ smoothModule T (i+1)
    apply Submodule.sum_mem
    intro k _
    apply (smoothModule T (i+1)).toAddSubgroup.zsmul_mem
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hτ)
    exact affinePrismSimplex_smooth S T H hH i k (z.property hσ)
  · rw [(affineChainPrism H).zero i j (by simpa using hij)]
    exact (smoothModule T j).zero_mem

/-- Restrict the affine prism to the actual supported smooth subcomplex. -/
def smoothPrism (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    {f g : M → N} (hf : IsSmoothMap S T f) (hg : IsSmoothMap S T g)
    (H : TopCat.Homotopy (underlyingMap S T f hf) (underlyingMap S T g hg))
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H) :
    _root_.Homotopy (smoothChainMap S T g hg) (smoothChainMap S T f hf) where
  hom i j := ModuleCat.ofHom ((((affineChainPrism H).hom i j).hom.comp
    (smoothModule S i).subtype).codRestrict (smoothModule T j)
      (affineChainPrism_smooth S T H hH i j))
  zero i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun k => k z.val) ((affineChainPrism H).zero i j hij)
  comm i := by
    have h := (affineChainPrism H).comm i
    cases i with
    | zero =>
      rw [dNext_eq_zero _ _ (by simp),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 by simp)] at h ⊢
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      dsimp +instances [smoothComplex, smoothChainMap, ChainComplex.of.d,
        chainFunctor, finsuppFunctor] at h ⊢
      try simp only [ite_true, eq_self, Nat.add_assoc, Nat.reduceAdd, Category.id_comp]
      convert (congrArg (fun k => k z.val) h) using 1 <;> rfl
    | succ i =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (i+1) i by simp),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (i+2) (i+1) by simp)] at h ⊢
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      dsimp +instances [smoothComplex, smoothChainMap, ChainComplex.of.d,
        chainFunctor, finsuppFunctor] at h ⊢
      try simp only [ite_true, eq_self, Nat.add_assoc, Nat.reduceAdd, Category.id_comp]
      convert (congrArg (fun k => k z.val) h) using 1 <;> rfl

/-- Smooth homotopies induce equal maps on smooth singular homology, including H₀. -/
theorem smoothHomotopy_homology (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    {f g : M → N} (hf : IsSmoothMap S T f) (hg : IsSmoothMap S T g)
    (H : TopCat.Homotopy (underlyingMap S T f hf) (underlyingMap S T g hg))
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H) (q : ℕ) :
    homologyMap (smoothChainMap S T g hg) q = homologyMap (smoothChainMap S T f hf) q :=
  (smoothPrism S T hf hg H hH).homologyMap_eq q

/-- Extension of the smooth prism by zero to the ordinary integer grading. -/
def smoothOrdinaryPrism (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    {f g : M → N} (hf : IsSmoothMap S T f) (hg : IsSmoothMap S T g)
    (H : TopCat.Homotopy (underlyingMap S T f hf) (underlyingMap S T g hg))
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H) :
    _root_.Homotopy (smoothOrdinaryMap S T g hg) (smoothOrdinaryMap S T f hf) :=
  (smoothPrism S T hf hg H hH).extend (degreeEmbedding 0)

/-- Smooth homotopies induce equal maps in every integer homology degree. -/
theorem smoothHomotopy_ordinaryHomology (S : SmoothManifold n a M)
    (T : SmoothManifold m b N) {f g : M → N}
    (hf : IsSmoothMap S T f) (hg : IsSmoothMap S T g)
    (H : TopCat.Homotopy (underlyingMap S T f hf) (underlyingMap S T g hg))
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H) (q : ℤ) :
    homologyMap (smoothOrdinaryMap S T g hg) q =
      homologyMap (smoothOrdinaryMap S T f hf) q :=
  (smoothOrdinaryPrism S T hf hg H hH).homologyMap_eq q

/-- The smooth pushforward of the identity is the identity. -/
theorem smoothChainMap_id (S : SmoothManifold n a M)
    (hf : IsSmoothMap S S id) : smoothChainMap S S id hf = 𝟙 _ := by
  ext q z
  apply Subtype.ext
  change (chainMap ℝ ℝ (underlyingMap S S id hf)).f q z.val = z.val
  have hm : underlyingMap S S id hf = 𝟙 (TopCat.of M) := rfl
  rw [hm, P202.SingularChains.chainMap_id]
  rfl

/-- Smooth pushforward respects composition on the same underlying spaces. -/
theorem smoothChainMap_comp {l : ℕ} {c : SmoothManifolds.ModelKind}
    {P : Type u} [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (U : SmoothManifold l c P) (f : M → N) (g : N → P)
    (hf : IsSmoothMap S T f) (hg : IsSmoothMap T U g)
    (hgf : IsSmoothMap S U (g ∘ f)) :
    smoothChainMap S U (g ∘ f) hgf =
      smoothChainMap S T f hf ≫ smoothChainMap T U g hg := by
  ext q z
  apply Subtype.ext
  change (chainMap ℝ ℝ (underlyingMap S U (g ∘ f) hgf)).f q z.val =
    (chainMap ℝ ℝ (underlyingMap T U g hg)).f q
      ((chainMap ℝ ℝ (underlyingMap S T f hf)).f q z.val)
  have hm : underlyingMap S U (g ∘ f) hgf =
      underlyingMap S T f hf ≫ underlyingMap T U g hg := rfl
  rw [hm, P202.SingularChains.chainMap_comp]
  rfl

/-- Identity law after extension by zero to integer degrees. -/
theorem smoothOrdinaryMap_id (S : SmoothManifold n a M)
    (hf : IsSmoothMap S S id) : smoothOrdinaryMap S S id hf = 𝟙 _ := by
  rw [smoothOrdinaryMap, smoothChainMap_id, HomologicalComplex.extendMap_id]
  rfl

/-- Composition law after extension by zero to integer degrees. -/
theorem smoothOrdinaryMap_comp {l : ℕ} {c : SmoothManifolds.ModelKind}
    {P : Type u} [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (U : SmoothManifold l c P) (f : M → N) (g : N → P)
    (hf : IsSmoothMap S T f) (hg : IsSmoothMap T U g)
    (hgf : IsSmoothMap S U (g ∘ f)) :
    smoothOrdinaryMap S U (g ∘ f) hgf =
      smoothOrdinaryMap S T f hf ≫ smoothOrdinaryMap T U g hg := by
  rw [smoothOrdinaryMap, smoothChainMap_comp S T U f g hf hg hgf,
    HomologicalComplex.extendMap_comp]
  rfl

end SmoothPrism

section AtlasChanges
open SmoothManifolds.MapData SmoothManifolds.InteriorHomotopyData Set

theorem manifoldSmooth_maximalExtension
    {A : Set (ModelChart n a M)} {B : Set (ModelChart m b N)}
    (hA : IsAtlas A) (hB : IsAtlas B) {f : M → N}
    (hf : ManifoldSmooth A B f) :
    ManifoldSmooth (maximalExtension (⊤ : ℕ∞) A) (maximalExtension (⊤ : ℕ∞) B) f := by
  intro x
  refine ⟨(hf x).1, ?_⟩
  intro e' he' d' hd' hx' hfx'
  obtain ⟨e, he, hx⟩ := hA x
  obtain ⟨d, hd, hfx⟩ := hB (f x)
  exact SmoothManifolds.chartContDiffAt_changeCharts (hf x).1 (he' e he)
    (SmoothManifolds.contDiffCompatible_symm (hd' d hd)) hx hx' hfx hfx'
      ((hf x).2 e he d hd hx hfx)

/-- Changing compatible descriptions of the same two smooth structures
preserves smoothness jointly in time and source coordinates. -/
theorem smoothHomotopy_changeAtlases
    {a' b' : SmoothManifolds.ModelKind}
    {A : Set (ModelChart n a M)} {B : Set (ModelChart m b N)}
    {A' : Set (ModelChart n a' M)} {B' : Set (ModelChart m b' N)}
    (hA : IsAtlas A) (hB : IsAtlas B)
    (hsource : ManifoldSmooth A' A id) (htarget : ManifoldSmooth B B' id)
    {H : HomotopyTime × M → N} (hH : SmoothHomotopy A B H) :
    SmoothHomotopy A' B' H := by
  refine ⟨hH.1, ?_⟩
  intro e' he' d' hd' z hx' hHx'
  obtain ⟨e, he, hx⟩ := hA z.2
  obtain ⟨d, hd, hHx⟩ := hB (H z)
  have hs := (hsource z.2).2 e' he' e he hx' hx
  have ht := SmoothManifolds.LocalCoordinateExtension.precomp
    ((htarget (H z)).2 d hd d' hd' hHx hHx') hH.1.continuousAt rfl
  exact SmoothManifolds.LocalCoordinateExtension.comp ht
    (SmoothManifolds.LocalCoordinateExtension.comp (hH.2 e he d hd z hx hHx)
      (SmoothManifolds.SmoothingHomotopies.LocalCoordinateExtension.with_time hs id contDiff_id z.1))

theorem smoothHomotopy_maximalExtension
    {A : Set (ModelChart n a M)} {B : Set (ModelChart m b N)}
    (hA : IsAtlas A) (hB : IsAtlas B) {H : HomotopyTime × M → N}
    (hH : SmoothHomotopy A B H) :
    SmoothHomotopy (maximalExtension (⊤ : ℕ∞) A) (maximalExtension (⊤ : ℕ∞) B) H := by
  refine ⟨hH.1, ?_⟩
  intro e' he' d' hd' z hx' hHx'
  obtain ⟨e, he, hx⟩ := hA z.2
  obtain ⟨d, hd, hHx⟩ := hB (H z)
  have hs := SmoothManifolds.chartContDiffAt_of_compatible (he' e he) hx' hx
  have ht := SmoothManifolds.LocalCoordinateExtension.precomp
    (SmoothManifolds.chartContDiffAt_of_compatible
      (SmoothManifolds.contDiffCompatible_symm (hd' d hd)) hHx hHx')
    hH.1.continuousAt rfl
  exact SmoothManifolds.LocalCoordinateExtension.comp ht
    (SmoothManifolds.LocalCoordinateExtension.comp (hH.2 e he d hd z hx hHx)
      (SmoothManifolds.SmoothingHomotopies.LocalCoordinateExtension.with_time hs id contDiff_id z.1))

end AtlasChanges

section BoundaryTransfer
open SmoothManifolds.BoundaryData SmoothManifolds.InteriorHomotopyData
open SmoothManifolds.MapData

/-- The collar push and its restricted homotopy make the actual interior
inclusion an isomorphism on smooth singular homology. The interior uses the
boundaryless structure proved equivalent to P104's restricted atlas. -/
theorem interior_smooth_homology (S : SmoothManifold n a M) :
    ∃ E : SmoothManifold n .euclidean (manifoldInterior S),
      ∃ hi : IsSmoothMap E S Subtype.val,
        ∀ q : ℤ, IsIso (homologyMap (smoothOrdinaryMap E S Subtype.val hi) q) := by
  obtain ⟨e⟩ := SmoothManifolds.InteriorHomotopies.interior_inclusion_homotopy_equivalence S
  obtain ⟨E, hAE, hi⟩ :=
    SmoothManifolds.SmoothingHomotopies.interior_euclidean_structure S e.isOpen_interior
  let A := openSubsetAtlas S.smoothStructure.val (manifoldInterior S) e.isOpen_interior
  have hA : IsContDiffAtlas (⊤ : ℕ∞) A :=
    SmoothManifolds.FiniteProperEmbedding.openSubsetAtlas_isContDiffAtlas S _ _
  have hp : IsSmoothMap S E e.inverse :=
    SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ A _ hA.1
      e.inverse id e.smooth_inverse hAE
  have hSE : IsSmoothMap S S (Subtype.val ∘ e.inverse) :=
    SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
      E.smoothStructure.property.1.1 e.inverse Subtype.val hp hi
  have hES : IsSmoothMap E E (e.inverse ∘ Subtype.val) :=
    SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
      S.smoothStructure.property.1.1 Subtype.val e.inverse hi hp
  have hS : IsSmoothMap S S id :=
    SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1
  have hE : IsSmoothMap E E id :=
    SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ E.smoothStructure.property.1
  let HS : TopCat.Homotopy (underlyingMap S S id hS)
      (underlyingMap S S (Subtype.val ∘ e.inverse) hSE) := {
    toFun := e.homotopy
    continuous_toFun := e.smooth_homotopy.1
    map_zero_left := e.homotopy_zero
    map_one_left := e.homotopy_one }
  have hEA : ManifoldSmooth E.smoothStructure.val A id :=
    SmoothManifolds.InteriorHomotopies.smooth_codRestrict e.isOpen_interior id hi
  have hHE : SmoothHomotopy E.smoothStructure.val E.smoothStructure.val
      (fun z : HomotopyTime × manifoldInterior S =>
        ⟨e.homotopy (z.1, z.2.val), e.preserves_interior z.1 z.2⟩) :=
    smoothHomotopy_changeAtlases hA.1 hA.1 hEA hAE e.smooth_restricted_homotopy
  let HE : TopCat.Homotopy (underlyingMap E E id hE)
      (underlyingMap E E (e.inverse ∘ Subtype.val) hES) := {
    toFun := fun z => ⟨e.homotopy (z.1, z.2.val), e.preserves_interior z.1 z.2⟩
    continuous_toFun := hHE.1
    map_zero_left := fun x => Subtype.ext (e.homotopy_zero x.val)
    map_one_left := fun x => Subtype.ext (e.homotopy_one x.val) }
  refine ⟨E, hi, fun q => ?_⟩
  refine ⟨⟨homologyMap (smoothOrdinaryMap S E e.inverse hp) q, ?_, ?_⟩⟩
  · rw [← homologyMap_comp, ← smoothOrdinaryMap_comp E S E Subtype.val e.inverse hi hp hES,
      smoothHomotopy_ordinaryHomology E E hE hES HE hHE q,
      smoothOrdinaryMap_id, homologyMap_id]
  · rw [← homologyMap_comp, ← smoothOrdinaryMap_comp S E S e.inverse Subtype.val hp hi hSE,
      smoothHomotopy_ordinaryHomology S S hS hSE HS e.smooth_homotopy q,
      smoothOrdinaryMap_id, homologyMap_id]

/-- It suffices to prove the nonnegative homology comparison on manifolds
without boundary. The actual P104 smooth collar push establishes the transfer
for every boundary manifold, including the empty and zero-dimensional cases. -/
theorem comparison_from_boundaryless_homology
    (h : ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
      (S : SmoothManifold n .euclidean M) (q : ℕ),
        IsIso (homologyMap (inclusion S) q)) : smoothSingularComparison_type.{u} := by
  refine ⟨?_, comparison_natural⟩
  intro n a M _ S q
  obtain ⟨E, hi, hE⟩ := interior_smooth_homology S
  haveI : QuasiIso (inclusion E) := by
    rw [quasiIso_iff]
    intro k
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr (h E k)
  haveI : QuasiIso (ordinaryInclusion E) := by
    change QuasiIso (extendMap (inclusion E) (degreeEmbedding 0))
    infer_instance
  haveI : IsIso (homologyMap (ordinaryInclusion E) q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  haveI : IsIso (homologyMap (smoothOrdinaryMap E S Subtype.val hi) q) := hE q
  haveI : IsIso (homologyMap ((ordinaryFunctor ℝ ℝ).map
      (underlyingMap E S Subtype.val hi)) q) := by
    exact interior_ordinary_homology S q
  have hsq := congrArg (fun f => homologyMap f q) (ordinaryInclusion_natural E S Subtype.val hi)
  rw [homologyMap_comp, homologyMap_comp] at hsq
  haveI : IsIso (homologyMap (smoothOrdinaryMap E S Subtype.val hi) q ≫
      homologyMap (ordinaryInclusion S) q) := by
    rw [hsq]
    infer_instance
  haveI : IsIso (homologyMap (ordinaryInclusion S) q) :=
    IsIso.of_isIso_comp_left (homologyMap (smoothOrdinaryMap E S Subtype.val hi) q) _
  exact ⟨inferInstance, cohomology_comparison_of_homology S q⟩

end BoundaryTransfer

section ConstantSmoothing
open SmoothManifolds.MapData
open scoped Simplicial

lemma constant_smooth (S : SmoothManifold n a M) (p : M) :
    IsSmoothMap S S (fun _ : M => p) := by
  intro x
  refine ⟨continuousAt_const, ?_⟩
  intro e _ d _ _ _
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => (d p).val,
    contDiff_const.contDiffOn, Filter.Eventually.of_forall (fun _ => rfl)⟩

def constantUnderlying (p : M) : TopCat.of M ⟶ TopCat.of M :=
  TopCat.ofHom ⟨fun _ : M => p, continuous_const⟩

lemma constantImage_smooth (S : SmoothManifold n a M) (p : M) (q : ℕ)
    (σ : Simplex (TopCat.of M) q) :
    IsSmoothSimplex S q ((TopCat.toSSet.map (constantUnderlying p)).app (op ⦋q⦌) σ) := by
  change SmoothManifolds.SmoothSingularData.SimplexSmooth S (fun _ => p)
  refine ⟨continuous_const, ?_⟩
  intro x d _ _
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => (d p).val,
    contDiff_const.contDiffOn, Filter.Eventually.of_forall (fun _ => rfl)⟩

lemma constantChain_mem_smooth (S : SmoothManifold n a M) (p : M) (q : ℕ)
    (z : Chains ℝ (TopCat.of M) q) :
    (chainMap ℝ ℝ (constantUnderlying p)).f q z ∈ smoothModule S q := by
  classical
  intro τ hτ
  obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hτ)
  exact constantImage_smooth S p q σ

/-- The ordinary constant map has smooth range in every degree. -/
def constantSmoothing (S : SmoothManifold n a M) (p : M) :
    complex ℝ ℝ (TopCat.of M) ⟶ smoothComplex S :=
  ChainComplex.ofHom
    (fun q => ModuleCat.ofHom (((chainMap ℝ ℝ (constantUnderlying p)).f q).hom.codRestrict
      (smoothModule S q) (constantChain_mem_smooth S p q)))
    (by
      intro q
      simp only [smoothComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun g => g z) ((chainMap ℝ ℝ (constantUnderlying p)).comm (q+1) q))

lemma constantSmoothing_inclusion (S : SmoothManifold n a M) (p : M) :
    constantSmoothing S p ≫ inclusion S = chainMap ℝ ℝ (constantUnderlying p) := by
  ext q z
  rfl

lemma inclusion_constantSmoothing (S : SmoothManifold n a M) (p : M) :
    inclusion S ≫ constantSmoothing S p = smoothChainMap S S (fun _ => p) (constant_smooth S p) := by
  ext q z
  rfl


open SmoothManifolds.InteriorHomotopyData

/-- A smooth contraction makes inclusion of the smooth singular complex a
homotopy equivalence, by factoring the constant map through smooth chains. -/
lemma comparison_of_smoothContraction (S : SmoothManifold n a M) (p : M)
    (H : TopCat.Homotopy (𝟙 (TopCat.of M)) (constantUnderlying p))
    (hH : SmoothHomotopy S.smoothStructure.val S.smoothStructure.val H) (q : ℕ) :
    IsIso (homologyMap (inclusion S) q) := by
  let hid : IsSmoothMap S S id :=
    SmoothManifolds.manifoldContDiff_id _ _ S.smoothStructure.property.1
  have hord : homologyMap (chainMap ℝ ℝ (constantUnderlying p)) q = 𝟙 _ := by
    have hh := (P202.PrismHomotopy.chainPrism ℝ ℝ H).homologyMap_eq q
    simpa only [(chainFunctor ℝ ℝ).map_id, homologyMap_id] using hh
  have hsm : homologyMap (smoothChainMap S S (fun _ => p) (constant_smooth S p)) q = 𝟙 _ := by
    have hh := smoothHomotopy_homology S S hid (constant_smooth S p) H hH q
    simpa only [smoothChainMap_id S hid, homologyMap_id] using hh
  refine ⟨⟨homologyMap (constantSmoothing S p) q, ?_, ?_⟩⟩
  · rw [← homologyMap_comp, inclusion_constantSmoothing]
    exact hsm
  · rw [← homologyMap_comp, constantSmoothing_inclusion]
    exact hord


end ConstantSmoothing

section LocalContractions
open SmoothManifolds.MapData SmoothManifolds.InteriorHomotopyData Set Filter
open scoped _root_.Topology

/-- Contraction through a global chart whose ambient coordinate target is convex. -/
def chartContraction (c : ModelChart n .euclidean M) (p : M)
    (z : HomotopyTime × M) : M :=
  c.symm ⟨(1 - z.1.val) • (c z.2).val + z.1.val • (c p).val, mem_univ _⟩

lemma chartContraction_mem (c : ModelChart n .euclidean M)
    (hs : c.source = univ) (hc : Convex ℝ (Subtype.val '' c.target)) (p : M)
    (z : HomotopyTime × M) :
    (⟨(1 - z.1.val) • (c z.2).val + z.1.val • (c p).val, mem_univ _⟩ :
      ModelSpace n .euclidean) ∈ c.target := by
  have hp : p ∈ c.source := by rw [hs]; trivial
  have hx : z.2 ∈ c.source := by rw [hs]; trivial
  have h := hc ⟨c z.2, c.map_source hx, rfl⟩ ⟨c p, c.map_source hp, rfl⟩
    (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel 1 z.1.val)
  obtain ⟨y, hy, heq⟩ := h
  convert hy using 1
  apply Subtype.ext
  exact heq.symm

lemma continuous_chartContraction (c : ModelChart n .euclidean M)
    (hs : c.source = univ) (hc : Convex ℝ (Subtype.val '' c.target)) (p : M) :
    Continuous (chartContraction c p) := by
  have hcoord : Continuous (fun x : M => (c x).val) :=
    continuous_subtype_val.comp (continuousOn_univ.mp (by simpa [hs] using c.continuousOn))
  have hlin : Continuous (fun z : HomotopyTime × M =>
      (⟨(1 - z.1.val) • (c z.2).val + z.1.val • (c p).val, mem_univ _⟩ :
        ModelSpace n .euclidean)) := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hcoord.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
  exact c.symm.continuousOn.comp_continuous hlin (chartContraction_mem c hs hc p)

lemma chartContraction_coordinate (c : ModelChart n .euclidean M)
    (hs : c.source = univ) (hc : Convex ℝ (Subtype.val '' c.target)) (p : M)
    (z : HomotopyTime × M) :
    (c (chartContraction c p z)).val =
      (1 - z.1.val) • (c z.2).val + z.1.val • (c p).val := by
  exact congrArg Subtype.val (c.right_inv (chartContraction_mem c hs hc p z))

lemma chartContraction_smooth (S : SmoothManifold n .euclidean M)
    (c : ModelChart n .euclidean M) (hca : c ∈ S.smoothStructure.val)
    (hs : c.source = univ) (hc : Convex ℝ (Subtype.val '' c.target)) (p : M) :
    SmoothHomotopy S.smoothStructure.val S.smoothStructure.val (chartContraction c p) := by
  have hcont := continuous_chartContraction c hs hc p
  refine ⟨hcont, ?_⟩
  intro e he d hd z hze hzd
  have hzc : z.2 ∈ c.source := by rw [hs]; trivial
  have hHc : chartContraction c p z ∈ c.source := by rw [hs]; trivial
  have hxc := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he c hca) hze hzc
  have hpc : LocalCoordinateExtension (⊤ : ℕ∞) (fun y => (e y).val)
      (fun _ : M => (c p).val) z.2 :=
    ⟨univ, isOpen_univ, mem_univ _, fun _ => (c p).val,
      contDiff_const.contDiffOn, Eventually.of_forall (fun _ => rfl)⟩
  have hlin := SmoothManifolds.RelativeManifoldApproximation.straight_localCoordinateExtension
    hxc hpc z.1
  have hcc : LocalCoordinateExtension (⊤ : ℕ∞)
      (fun w : HomotopyTime × M => Fin.cons w.1.val (e w.2).val)
      (fun w => (c (chartContraction c p w)).val) z := by
    exact hlin.congr (Eventually.of_forall (fun w => (chartContraction_coordinate c hs hc p w).symm))
  have htrans := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 c hca d hd) hHc hzd
  exact SmoothManifolds.LocalCoordinateExtension.comp
    (SmoothManifolds.LocalCoordinateExtension.precomp
      (ι := fun y : M => (c y).val) (f := fun y : M => (d y).val)
      (h := chartContraction c p) htrans hcont.continuousAt rfl) hcc

lemma chartContraction_zero (c : ModelChart n .euclidean M) (hs : c.source = univ)
    (p x : M) : chartContraction c p (timeZero, x) = x := by
  change c.symm ⟨(1 - (0 : ℝ)) • (c x).val + (0 : ℝ) • (c p).val, _⟩ = x
  simpa using c.left_inv (by rw [hs]; trivial : x ∈ c.source)

lemma chartContraction_one (c : ModelChart n .euclidean M) (hs : c.source = univ)
    (p x : M) : chartContraction c p (timeOne, x) = p := by
  change c.symm ⟨(1 - (1 : ℝ)) • (c x).val + (1 : ℝ) • (c p).val, _⟩ = p
  simpa using c.left_inv (by rw [hs]; trivial : p ∈ c.source)

/-- Local comparison on a convex coordinate domain. Empty domains are included. -/
theorem comparison_convexChart (S : SmoothManifold n .euclidean M)
    (c : ModelChart n .euclidean M) (hca : c ∈ S.smoothStructure.val)
    (hs : c.source = univ) (hc : Convex ℝ (Subtype.val '' c.target)) (q : ℕ) :
    IsIso (homologyMap (inclusion S) q) := by
  classical
  by_cases hM : Nonempty M
  · obtain ⟨p⟩ := hM
    let H : TopCat.Homotopy (𝟙 (TopCat.of M)) (constantUnderlying p) := {
      toFun := chartContraction c p
      continuous_toFun := continuous_chartContraction c hs hc p
      map_zero_left := chartContraction_zero c hs p
      map_one_left := chartContraction_one c hs p }
    exact comparison_of_smoothContraction S p H (chartContraction_smooth S c hca hs hc p) q
  · letI : IsEmpty M := not_nonempty_iff.mp hM
    haveI : IsIso (inclusion S) := inclusion_isIso_of_forall_smooth S (fun k σ =>
      isEmptyElim (simplexEquiv (TopCat.of M) k σ (Convexity.StdSimplex.single 0)))
    infer_instance

end LocalContractions

section OpenSubspaces
open SmoothManifolds SmoothManifolds.MapData SmoothManifolds.SmoothSingularData Set Filter
open scoped _root_.Topology
variable {q : ℕ}

theorem simplexSmooth_openSubmanifold_iff (S : AtlasData.SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) (σ : Simplex q → U) :
    SimplexSmooth (FiniteProperEmbedding.openSubmanifold S U hU) σ ↔
      SimplexSmooth S (Subtype.val ∘ σ) := by
  constructor
  · intro hσ
    refine ⟨continuous_subtype_val.comp hσ.1, ?_⟩
    intro x d hd hdx
    let d' := d.subtypeRestr (s := ⟨U, hU⟩) ⟨σ x⟩
    have hd' : d' ∈ MapData.openSubsetAtlas S.smoothStructure.val U hU :=
      ⟨⟨σ x⟩, d, hd, rfl⟩
    have hd'' : d' ∈ (FiniteProperEmbedding.openSubmanifold S U hU).smoothStructure.val :=
      subset_maximalExtension (FiniteProperEmbedding.openSubsetAtlas_isContDiffAtlas S U hU) hd'
    have hdx' : σ x ∈ d'.source := by
      simpa only [d', OpenPartialHomeomorph.subtypeRestr_source, mem_preimage, Function.comp_apply] using hdx
    exact hσ.2 x d' hd'' hdx'
  · intro hσ
    have hcσ : Continuous σ := continuous_induced_rng.mpr hσ.1
    refine ⟨hcσ, ?_⟩
    intro x d hd hdx
    obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 (σ x).val
    let c' := c.subtypeRestr (s := ⟨U, hU⟩) ⟨σ x⟩
    have hc' : c' ∈ MapData.openSubsetAtlas S.smoothStructure.val U hU :=
      ⟨⟨σ x⟩, c, hc, rfl⟩
    have hxc' : σ x ∈ c'.source := by
      simpa only [c', OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxc
    have hg := chartContDiffAt_of_compatible (contDiffCompatible_symm (hd c' hc')) hxc' hdx
    exact LocalCoordinateExtension.comp
      (LocalCoordinateExtension.precomp (ι := fun z : U => (c' z).val)
        (f := fun z : U => (d z).val) hg hcσ.continuousAt rfl) (hσ.2 x c hc hxc)

theorem smooth_openSubmanifold_inclusion (S : AtlasData.SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) :
    MapData.IsSmoothMap (FiniteProperEmbedding.openSubmanifold S U hU) S Subtype.val := by
  intro x
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    (FiniteProperEmbedding.openSubmanifold S U hU).smoothStructure.property.1
    S.smoothStructure.property.1 Subtype.val x).mpr
  obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 x.val
  let c' := c.subtypeRestr (s := ⟨U, hU⟩) ⟨x⟩
  have hc' : c' ∈ MapData.openSubsetAtlas S.smoothStructure.val U hU :=
    ⟨⟨x⟩, c, hc, rfl⟩
  refine ⟨continuousAt_subtype_val, c',
    subset_maximalExtension (FiniteProperEmbedding.openSubsetAtlas_isContDiffAtlas S U hU) hc',
    c, hc, ?_, hxc, ?_⟩
  · simpa only [c', OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxc
  · exact LocalCoordinateExtension.self _ (fun y : U => (c y.val).val) x

open CategoryTheory HomologicalComplex Opposite
open scoped Simplicial
open P202Specs.SmoothSingularComparison P202Specs.SingularChains
open P202Specs.RelativeSingularChains

theorem isSmoothSimplex_openSubmanifold_iff (S : AtlasData.SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) (τ : P202Specs.SingularChains.Simplex (TopCat.of U) q) :
    IsSmoothSimplex (FiniteProperEmbedding.openSubmanifold S U hU) q τ ↔
      IsSmoothSimplex S q
        ((TopCat.toSSet.map (Pair.inclusion ⟨TopCat.of M, U⟩)).app (op ⦋q⦌) τ) := by
  exact simplexSmooth_openSubmanifold_iff S U hU
    (simplexEquiv (TopCat.of U) q τ ∘ toBarycentric q)

theorem image_smoothSimplex_openSubmanifold (S : AtlasData.SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) :
    ((TopCat.toSSet.map (Pair.inclusion ⟨TopCat.of M, U⟩)).app (op ⦋q⦌)) ''
        {τ | IsSmoothSimplex (FiniteProperEmbedding.openSubmanifold S U hU) q τ} =
      {σ | IsSmoothSimplex S q σ} ∩
        {σ | ∀ x, simplexEquiv (TopCat.of M) q σ x ∈ U} := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨(isSmoothSimplex_openSubmanifold_iff S U hU τ).mp hτ,
      (P202.RelativeSingularChains.simplex_image ⟨TopCat.of M, U⟩ q _).mp ⟨τ, rfl⟩⟩
  · rintro ⟨hσ, hUσ⟩
    obtain ⟨τ, rfl⟩ := (P202.RelativeSingularChains.simplex_image
      ⟨TopCat.of M, U⟩ q σ).mpr hUσ
    exact ⟨τ, (isSmoothSimplex_openSubmanifold_iff S U hU τ).mpr hσ, rfl⟩

theorem range_openSmoothInclusion (S : AtlasData.SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) :
    ((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, U⟩)).f q).hom).comp
      (smoothModule (FiniteProperEmbedding.openSubmanifold S U hU) q).subtype).range =
      smoothModule S q ⊓ Finsupp.supported ℝ ℝ
        {σ | ∀ x, simplexEquiv (TopCat.of M) q σ x ∈ U} := by
  rw [LinearMap.range_comp, Submodule.range_subtype]
  change (Finsupp.supported ℝ ℝ _).map (Finsupp.lmapDomain ℝ ℝ _) = _
  rw [Finsupp.lmapDomain_supported, image_smoothSimplex_openSubmanifold S U hU,
    Finsupp.supported_inter]
  rfl

/-- Actual smooth chains on an open submanifold, identified with their image
in the ambient simplex basis. -/
def openSmoothChainsEquiv (S : AtlasData.SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) :
    smoothModule (FiniteProperEmbedding.openSubmanifold S U hU) q ≃ₗ[ℝ]
      ↥(smoothModule S q ⊓ Finsupp.supported ℝ ℝ
        {σ | ∀ x, simplexEquiv (TopCat.of M) q σ x ∈ U}) :=
  (LinearEquiv.ofInjective
    ((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, U⟩)).f q).hom).comp
      (smoothModule (FiniteProperEmbedding.openSubmanifold S U hU) q).subtype)
    ((P202.RelativeSingularChains.inclusion_injective ℝ ℝ
      ⟨TopCat.of M, U⟩ q).comp Subtype.val_injective)).trans
    (LinearEquiv.ofEq _ _ (range_openSmoothInclusion S U hU))

theorem openSmoothChainsEquiv_val (S : AtlasData.SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U)
    (z : smoothModule (FiniteProperEmbedding.openSubmanifold S U hU) q) :
    (openSmoothChainsEquiv S U hU z).val =
      (chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, U⟩)).f q z.val := rfl

/-- The smooth overlap formula, in the common ambient finite-chain module. -/
theorem range_openSmoothInclusion_inter (S : AtlasData.SmoothManifold n a M)
    (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) :
    ((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, U ∩ V⟩)).f q).hom).comp
        (smoothModule (FiniteProperEmbedding.openSubmanifold S (U ∩ V) (hU.inter hV)) q).subtype).range =
      ((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, U⟩)).f q).hom).comp
        (smoothModule (FiniteProperEmbedding.openSubmanifold S U hU) q).subtype).range ⊓
      ((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, V⟩)).f q).hom).comp
        (smoothModule (FiniteProperEmbedding.openSubmanifold S V hV) q).subtype).range := by
  rw [range_openSmoothInclusion S (U ∩ V) (hU.inter hV),
    range_openSmoothInclusion S U hU, range_openSmoothInclusion S V hV]
  have hs : ({σ | ∀ x, simplexEquiv (TopCat.of M) q σ x ∈ U ∩ V} :
      Set (P202Specs.SingularChains.Simplex (TopCat.of M) q)) =
      {σ | ∀ x, simplexEquiv (TopCat.of M) q σ x ∈ U} ∩
        {σ | ∀ x, simplexEquiv (TopCat.of M) q σ x ∈ V} := by
    ext σ
    simp only [Set.mem_ofPred_eq, mem_inter_iff, forall_and]
  rw [hs, Finsupp.supported_inter]
  ext z
  simp only [Submodule.mem_inf]
  aesop

/-- Every smooth two-set-small chain is a sum of actual smooth chains on the
open cover members. -/
theorem smallSmoothModule_eq_sup_ranges (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) Bool) :
    smoothModule S q ⊓ P202Specs.SmallChainHomology.smallModule ℝ C q =
      ((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, C.sets false⟩)).f q).hom).comp
        (smoothModule (FiniteProperEmbedding.openSubmanifold S _ (C.isOpen false)) q).subtype).range ⊔
      ((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, C.sets true⟩)).f q).hom).comp
        (smoothModule (FiniteProperEmbedding.openSubmanifold S _ (C.isOpen true)) q).subtype).range := by
  rw [range_openSmoothInclusion S _ (C.isOpen false),
    range_openSmoothInclusion S _ (C.isOpen true)]
  change Finsupp.supported ℝ ℝ _ ⊓ Finsupp.supported ℝ ℝ _ =
    (Finsupp.supported ℝ ℝ _ ⊓ Finsupp.supported ℝ ℝ _) ⊔
      (Finsupp.supported ℝ ℝ _ ⊓ Finsupp.supported ℝ ℝ _)
  simp only [← Finsupp.supported_inter, ← Finsupp.supported_union]
  congr 1
  ext σ
  simp only [mem_inter_iff, mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨hσ, ⟨b, hb⟩⟩
    cases b with
    | false => exact Or.inl ⟨hσ, Set.range_subset_iff.mp hb⟩
    | true => exact Or.inr ⟨hσ, Set.range_subset_iff.mp hb⟩
  · rintro (⟨hσ, hU⟩ | ⟨hσ, hV⟩)
    · exact ⟨hσ, false, Set.range_subset_iff.mpr hU⟩
    · exact ⟨hσ, true, Set.range_subset_iff.mpr hV⟩


universe v
/-- Smooth maps into a canonical open submanifold are exactly the maps smooth
as ambient maps. -/
theorem isSmoothMap_openSubmanifold_iff {m : ℕ} {b : ModelKind}
    {N : Type v} [TopologicalSpace N] (T : AtlasData.SmoothManifold m b N)
    (S : AtlasData.SmoothManifold n a M) (U : Set M) (hU : IsOpen U) (f : N → U) :
    MapData.IsSmoothMap T (FiniteProperEmbedding.openSubmanifold S U hU) f ↔
      MapData.IsSmoothMap T S (Subtype.val ∘ f) := by
  constructor
  · intro hf
    exact manifoldContDiff_comp _ _ _ _
      (FiniteProperEmbedding.openSubmanifold S U hU).smoothStructure.property.1.1
      f Subtype.val hf (smooth_openSubmanifold_inclusion S U hU)
  · intro hf x
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      T.smoothStructure.property.1
      (FiniteProperEmbedding.openSubmanifold S U hU).smoothStructure.property.1 f x).mpr
    obtain ⟨c, hc, hxc⟩ := T.smoothStructure.property.1.1 x
    obtain ⟨d, hd, hfd⟩ := S.smoothStructure.property.1.1 (f x).val
    let d' := d.subtypeRestr (s := ⟨U, hU⟩) ⟨f x⟩
    have hd' : d' ∈ MapData.openSubsetAtlas S.smoothStructure.val U hU :=
      ⟨⟨f x⟩, d, hd, rfl⟩
    refine ⟨_root_.Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (hf x).1, c, hc, d',
      subset_maximalExtension (FiniteProperEmbedding.openSubsetAtlas_isContDiffAtlas S U hU) hd',
      hxc, ?_, (hf x).2 c hc d hd hxc hfd⟩
    simpa only [d', OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hfd

theorem smooth_openSubmanifold_inclusion_of_subset (S : AtlasData.SmoothManifold n a M)
    (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) :
    MapData.IsSmoothMap (FiniteProperEmbedding.openSubmanifold S U hU)
      (FiniteProperEmbedding.openSubmanifold S V hV) (Set.inclusion hUV) := by
  apply (isSmoothMap_openSubmanifold_iff _ S V hV _).mpr
  exact smooth_openSubmanifold_inclusion S U hU

/-- Canonical inclusion of an open submanifold's smooth singular complex. -/
def openSmoothInclusion (S : AtlasData.SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) :
    smoothComplex (FiniteProperEmbedding.openSubmanifold S U hU) ⟶ smoothComplex S :=
  smoothChainMap _ S Subtype.val (smooth_openSubmanifold_inclusion S U hU)

@[reassoc] theorem openSmoothInclusion_square (S : AtlasData.SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) :
    openSmoothInclusion S U hU ≫ inclusion S =
      inclusion (FiniteProperEmbedding.openSubmanifold S U hU) ≫
        chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, U⟩) := by
  ext k z
  rfl

theorem openSmoothInclusion_injective (S : AtlasData.SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) (k : ℕ) :
    Function.Injective ((openSmoothInclusion S U hU).f k) := by
  intro z w hzw
  apply Subtype.ext
  apply P202.RelativeSingularChains.inclusion_injective ℝ ℝ ⟨TopCat.of M, U⟩ k
  exact congrArg Subtype.val hzw


/-- A convex coordinate open subset has the comparison for its canonical
induced smooth structure; the coordinate chart is the actual restricted chart. -/
theorem comparison_open_convexChart (S : AtlasData.SmoothManifold n .euclidean M)
    (U : Set M) (hU : IsOpen U) (c : SmoothManifolds.ModelData.ModelChart n .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (hUc : U ⊆ c.source)
    (hconv : Convex ℝ (Subtype.val '' (c '' U))) (q : ℕ) :
    IsIso (homologyMap (inclusion (FiniteProperEmbedding.openSubmanifold S U hU)) q) := by
  classical
  by_cases hne : Nonempty U
  · let d := c.subtypeRestr (s := ⟨U, hU⟩) hne
    have hd : d ∈ (FiniteProperEmbedding.openSubmanifold S U hU).smoothStructure.val :=
      subset_maximalExtension (FiniteProperEmbedding.openSubsetAtlas_isContDiffAtlas S U hU)
        ⟨hne, c, hc, rfl⟩
    have hds : d.source = Set.univ := by
      ext x
      simp only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage,
        Set.mem_univ, iff_true]
      exact hUc x.property
    have hdt : d.target = c '' U := by
      rw [← d.image_source_eq_target, hds]
      ext y
      constructor
      · rintro ⟨x, _, rfl⟩
        exact ⟨x.val, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
    exact comparison_convexChart _ d hd hds (by rwa [hdt]) q
  · letI : IsEmpty U := not_nonempty_iff.mp hne
    haveI : IsIso (inclusion (FiniteProperEmbedding.openSubmanifold S U hU)) :=
      inclusion_isIso_of_forall_smooth _ (fun k σ => isEmptyElim
        (simplexEquiv (TopCat.of U) k σ (Convexity.StdSimplex.single 0)))
    infer_instance

end OpenSubspaces

section ChainCovers
universe v

/-- Concrete cycles/boundaries criterion extracted from a categorical homology isomorphism. -/
theorem shortComplex_comparison_conditions {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)
    [IsIso (ShortComplex.homologyMap f)] :
    (∀ z : T.X₂, T.g z = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ y : T.X₁, f.τ₂ x - z = T.f y) ∧
    (∀ x : S.X₂, S.g x = 0 → ∀ y : T.X₁,
      T.f y = f.τ₂ x → ∃ a : S.X₁, S.f a = x) := by
  let γ : ShortComplex.LeftHomologyMapData f
      S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData := default
  have hK (x : S.g.hom.ker) : (γ.φK x).val = f.τ₂ x.val := by
    exact congrArg (fun g => g x) γ.commi
  have hH (x : S.g.hom.ker) :
      γ.φH (Submodule.Quotient.mk x) = Submodule.Quotient.mk (γ.φK x) := by
    exact congrArg (fun g => g x) γ.commπ
  have hqi : ShortComplex.QuasiIso f := (ShortComplex.quasiIso_iff f).mpr inferInstance
  haveI : IsIso γ.φH := γ.quasiIso_iff.mp hqi
  have hbij := (ConcreteCategory.isIso_iff_bijective γ.φH).mp inferInstance
  constructor
  · intro z hz
    obtain ⟨w, hw⟩ := hbij.2 (Submodule.Quotient.mk (⟨z, hz⟩ : T.g.hom.ker))
    induction w using Submodule.Quotient.induction_on with
    | _ x =>
      rw [hH] at hw
      obtain ⟨y, hy⟩ := (Submodule.Quotient.eq _).mp hw
      refine ⟨x.val, x.property, y, ?_⟩
      have he := congrArg Subtype.val hy
      change T.f y = (γ.φK x).val - z at he
      rw [hK] at he
      exact he.symm
  · intro x hx y hy
    have hz : γ.φH (Submodule.Quotient.mk (⟨x, hx⟩ : S.g.hom.ker)) = 0 := by
      rw [hH]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨y, ?_⟩
      apply Subtype.ext
      exact hy.trans (hK ⟨x, hx⟩).symm
    have hx0 : Submodule.Quotient.mk (⟨x, hx⟩ : S.g.hom.ker) = 0 :=
      hbij.1 (hz.trans γ.φH.hom.map_zero.symm)
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx0
    exact ⟨a, congrArg Subtype.val ha⟩

/-- Homology comparison passes from a family of injectively embedded short
complexes to their union; cycle and bounding-chain representatives suffice. -/
theorem shortComplex_comparison_of_cover {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)
    {ι : Type*} (A B : ι → ShortComplex (ModuleCat.{v} R))
    (g : ∀ i, A i ⟶ B i) (k : ∀ i, A i ⟶ S) (l : ∀ i, B i ⟶ T)
    (hcomm : ∀ i, g i ≫ l i = k i ≫ f)
    (hkinj : ∀ i, Function.Injective (k i).τ₃)
    (hlinj₂ : ∀ i, Function.Injective (l i).τ₂)
    (hlinj₃ : ∀ i, Function.Injective (l i).τ₃)
    (hcover : ∀ z : T.X₂, ∃ i, ∃ z' : (B i).X₂, (l i).τ₂ z' = z)
    (hcoverPair : ∀ (x : S.X₂) (y : T.X₁), ∃ i,
      ∃ x' : (A i).X₂, ∃ y' : (B i).X₁, (k i).τ₂ x' = x ∧ (l i).τ₁ y' = y)
    (hiso : ∀ i, IsIso (ShortComplex.homologyMap (g i))) :
    IsIso (ShortComplex.homologyMap f) := by
  apply P202.SmallChainHomology.shortComplex_comparison
  · intro z hz
    obtain ⟨i, z', hz'⟩ := hcover z
    have hzcycle : (B i).g z' = 0 := by
      apply hlinj₃ i
      have he := congrArg (fun h => h z') (l i).comm₂₃
      change T.g ((l i).τ₂ z') = (l i).τ₃ ((B i).g z') at he
      rw [hz', hz] at he
      exact he.symm.trans (l i).τ₃.hom.map_zero.symm
    letI := hiso i
    obtain ⟨x', hx', y', hy'⟩ := (shortComplex_comparison_conditions (g i)).1 z' hzcycle
    refine ⟨(k i).τ₂ x', ?_, (l i).τ₁ y', ?_⟩
    · have he := congrArg (fun h => h x') (k i).comm₂₃
      change S.g ((k i).τ₂ x') = (k i).τ₃ ((A i).g x') at he
      rw [hx', (k i).τ₃.hom.map_zero] at he
      exact he
    · have he := congrArg (fun h => h.τ₂ x') (hcomm i)
      change (l i).τ₂ ((g i).τ₂ x') = f.τ₂ ((k i).τ₂ x') at he
      have hb := congrArg (fun h => h y') (l i).comm₁₂
      change T.f ((l i).τ₁ y') = (l i).τ₂ ((B i).f y') at hb
      calc
        f.τ₂ ((k i).τ₂ x') - z = (l i).τ₂ ((g i).τ₂ x') - (l i).τ₂ z' := by rw [he, hz']
        _ = (l i).τ₂ ((g i).τ₂ x' - z') := ((l i).τ₂.hom.map_sub _ _).symm
        _ = T.f ((l i).τ₁ y') := by rw [hy', hb]
  · intro x hx y hy
    obtain ⟨i, x', y', hx', hy'⟩ := hcoverPair x y
    have hxcycle : (A i).g x' = 0 := by
      apply hkinj i
      have he := congrArg (fun h => h x') (k i).comm₂₃
      change S.g ((k i).τ₂ x') = (k i).τ₃ ((A i).g x') at he
      rw [hx', hx] at he
      exact he.symm.trans (k i).τ₃.hom.map_zero.symm
    have hbound : (B i).f y' = (g i).τ₂ x' := by
      apply hlinj₂ i
      have hb := congrArg (fun h => h y') (l i).comm₁₂
      change T.f ((l i).τ₁ y') = (l i).τ₂ ((B i).f y') at hb
      have he := congrArg (fun h => h.τ₂ x') (hcomm i)
      change (l i).τ₂ ((g i).τ₂ x') = f.τ₂ ((k i).τ₂ x') at he
      calc
        (l i).τ₂ ((B i).f y') = T.f y := by rw [← hb, hy']
        _ = f.τ₂ x := hy
        _ = (l i).τ₂ ((g i).τ₂ x') := by rw [he, hx']
    letI := hiso i
    obtain ⟨a, ha⟩ := (shortComplex_comparison_conditions (g i)).2 x' hxcycle y' hbound
    refine ⟨(k i).τ₁ a, ?_⟩
    have he := congrArg (fun h => h a) (k i).comm₁₂
    change S.f ((k i).τ₁ a) = (k i).τ₂ ((A i).f a) at he
    rw [ha, hx'] at he
    exact he

/-- The finite-representative argument for an increasing or directed union of
chain complexes, phrased without categorical colimits. -/
theorem chainComplex_comparison_of_cover {R : Type u} [CommRing R]
    {K L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
    {ι : Type*} (A B : ι → ChainComplex (ModuleCat.{v} R) ℕ)
    (g : ∀ i, A i ⟶ B i) (k : ∀ i, A i ⟶ K) (l : ∀ i, B i ⟶ L)
    (hcomm : ∀ i, g i ≫ l i = k i ≫ f)
    (hkinj : ∀ i q, Function.Injective ((k i).f q))
    (hlinj : ∀ i q, Function.Injective ((l i).f q))
    (hcover : ∀ q (z : L.X q), ∃ i, ∃ z' : (B i).X q, (l i).f q z' = z)
    (hcoverPair : ∀ q (x : K.X q) (y : L.X (q+1)), ∃ i,
      ∃ x' : (A i).X q, ∃ y' : (B i).X (q+1), (k i).f q x' = x ∧ (l i).f (q+1) y' = y)
    (hiso : ∀ i q, IsIso (homologyMap (g i) q)) (q : ℕ) :
    IsIso (homologyMap f q) := by
  let F := shortComplexFunctor' (ModuleCat.{v} R) (ComplexShape.down ℕ) (q+1) q (q-1)
  apply (quasiIsoAt_iff_isIso_homologyMap f q).mp
  apply (quasiIsoAt_iff' f (q+1) q (q-1) (by simp) (by cases q <;> simp)).mpr
  apply (ShortComplex.quasiIso_iff _).mpr
  apply shortComplex_comparison_of_cover (F.map f) (fun i => F.obj (A i))
    (fun i => F.obj (B i)) (fun i => F.map (g i)) (fun i => F.map (k i))
    (fun i => F.map (l i))
  · intro i
    rw [← F.map_comp, ← F.map_comp, hcomm i]
  · intro i
    exact hkinj i (q-1)
  · intro i
    exact hlinj i q
  · intro i
    exact hlinj i (q-1)
  · exact hcover q
  · exact hcoverPair q
  · intro i
    apply (ShortComplex.quasiIso_iff _).mp
    apply (quasiIsoAt_iff' (g i) (q+1) q (q-1) (by simp) (by cases q <;> simp)).mp
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr (hiso i q)

end ChainCovers

section DirectedSupport
universe v w

/-- Compactness of the image of a finite singular chain places it in one
member of any directed open cover. -/
theorem finiteChain_in_directed_open {R : Type u} [CommRing R]
    {X : TopCat.{v}} {ι : Type w} [Nonempty ι] (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hUc : ∀ x, ∃ i, x ∈ U i)
    (hdU : Directed (· ⊆ ·) U) (q : ℕ) (z : Chains R X q) :
    ∃ i, ∀ σ ∈ z.support, ∀ x, simplexEquiv X q σ x ∈ U i := by
  classical
  let B : Set X := ⋃ σ ∈ z.support, Set.range (simplexEquiv X q σ)
  have hB : IsCompact B := z.support.isCompact_biUnion
    (fun σ _ => isCompact_range (simplexEquiv X q σ).continuous)
  obtain ⟨i, hi⟩ := hB.elim_directed_cover U hUo
    (fun x _ => Set.mem_iUnion.mpr (hUc x)) hdU
  refine ⟨i, ?_⟩
  intro σ hσ x
  apply hi
  exact Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨hσ, Set.mem_range_self x⟩⟩

end DirectedSupport

section GoodCovers
universe v w
variable {X : Type v} {ι : Type w}
open Set

/-- Mayer–Vietoris gluing iterated over a finite good cover. -/
theorem finiteUnion_of_finiteInter {P : Set X → Prop}
    (h0 : P ∅)
    (hunion : ∀ U V, P U → P V → P (U ∩ V) → P (U ∪ V))
    (s : Finset ι) :
    ∀ U : ι → Set X,
      (∀ t : Finset ι, t.Nonempty → P (⋂ i ∈ t, U i)) → P (⋃ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro U _; simpa using h0
  | @insert a s ha ih =>
    intro U hU
    have hUs := ih U hU
    have hUa : P (U a) := by simpa using hU {a} (by simp)
    have hInt : P (⋃ i ∈ s, U i ∩ U a) := by
      apply ih (fun i => U i ∩ U a)
      intro t ht
      have hh := hU (insert a t) (by simp)
      have heq : (⋂ i ∈ t, U i ∩ U a) = ⋂ i ∈ insert a t, U i := by
        ext x
        simp only [mem_iInter, Finset.mem_insert]
        constructor
        · intro hx i hi
          rcases hi with rfl | hi
          · obtain ⟨j, hj⟩ := ht
            exact (hx j hj).2
          · exact (hx i hi).1
        · intro hx i hi
          exact ⟨hx i (Or.inr hi), hx a (Or.inl rfl)⟩
      rwa [heq]
    have heq : (⋃ i ∈ s, U i ∩ U a) = (⋃ i ∈ s, U i) ∩ U a := by
      simp only [iUnion_inter]
    rw [heq] at hInt
    simpa only [Finset.set_biUnion_insert, union_comm] using
      hunion (⋃ i ∈ s, U i) (U a) hUs hUa hInt

/-- A good cover globalizes any property closed under binary gluing and
directed unions. This uses finite subfamilies, without local finiteness. -/
theorem iUnion_of_finiteInter {P : Set X → Prop}
    (h0 : P ∅)
    (hunion : ∀ U V, P U → P V → P (U ∩ V) → P (U ∪ V))
    (hdirected : ∀ (V : Finset ι → Set X), Directed (· ⊆ ·) V →
      (∀ s, P (V s)) → P (⋃ s, V s))
    (U : ι → Set X) (hU : ∀ t : Finset ι, t.Nonempty → P (⋂ i ∈ t, U i)) :
    P (⋃ i, U i) := by
  classical
  let V : Finset ι → Set X := fun s => ⋃ i ∈ s, U i
  have hV : Directed (· ⊆ ·) V := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_union_left _ hi, hxi⟩
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_union_right _ hi, hxi⟩
  have hh := hdirected V hV (fun s => finiteUnion_of_finiteInter h0 hunion s U hU)
  have heq : (⋃ s, V s) = ⋃ i, U i := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hs
      exact mem_iUnion.mpr ⟨i, hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨{i}, mem_iUnion₂.mpr ⟨i, by simp, hi⟩⟩
  rwa [heq] at hh

end GoodCovers

section DirectedComparison
universe v w
open P202Specs.RelativeSingularChains

/-- A chain with all simplex images in a subspace is the image of an actual
chain on that subspace. -/
lemma openChain_lift {X : TopCat.{v}} (U : Set X) (q : ℕ) (z : Chains ℝ X q)
    (hz : ∀ σ ∈ z.support, ∀ x, simplexEquiv X q σ x ∈ U) :
    ∃ z' : Chains ℝ (TopCat.of U) q,
      (chainMap ℝ ℝ (Pair.inclusion ⟨X, U⟩)).f q z' = z := by
  classical
  apply (Finsupp.mem_range_mapDomain_iff _
    (P202.RelativeSingularChains.simplex_injective ⟨X, U⟩ q) z).mpr
  intro σ hσ
  by_contra hne
  exact hσ ((P202.RelativeSingularChains.simplex_image ⟨X, U⟩ q σ).mpr
    (hz σ (Finsupp.mem_support_iff.mpr hne)))

lemma openSmoothChain_lift {n : ℕ} {a : SmoothManifolds.ModelKind}
    {M : Type v} [TopologicalSpace M] (S : SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) (q : ℕ) (z : smoothModule S q)
    (hz : ∀ σ ∈ z.val.support, ∀ x, simplexEquiv (TopCat.of M) q σ x ∈ U) :
    ∃ z' : smoothModule (SmoothManifolds.FiniteProperEmbedding.openSubmanifold S U hU) q,
      (openSmoothInclusion S U hU).f q z' = z := by
  have hzrange : z.val ∈
      ((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, U⟩)).f q).hom).comp
      (smoothModule (SmoothManifolds.FiniteProperEmbedding.openSubmanifold S U hU) q).subtype).range := by
    rw [range_openSmoothInclusion S U hU]
    exact ⟨z.property, hz⟩
  obtain ⟨z', hz'⟩ := hzrange
  refine ⟨z', ?_⟩
  apply Subtype.ext
  exact hz'

/-- Smooth/continuous homology comparison passes through every directed
open union, including increasing countable unions. -/
theorem comparison_of_directed_open_cover {n : ℕ} {a : SmoothManifolds.ModelKind}
    {M : Type v} [TopologicalSpace M] (S : SmoothManifold n a M)
    {ι : Type w} [Nonempty ι] (U : ι → Set M) (hUo : ∀ i, IsOpen (U i))
    (hUc : ∀ x, ∃ i, x ∈ U i) (hdU : Directed (· ⊆ ·) U)
    (hiso : ∀ i q, IsIso (homologyMap
      (inclusion (SmoothManifolds.FiniteProperEmbedding.openSubmanifold S (U i) (hUo i))) q))
    (q : ℕ) : IsIso (homologyMap (inclusion S) q) := by
  apply chainComplex_comparison_of_cover (inclusion S)
    (fun i => smoothComplex (SmoothManifolds.FiniteProperEmbedding.openSubmanifold S (U i) (hUo i)))
    (fun i => complex ℝ ℝ (TopCat.of (U i)))
    (fun i => inclusion (SmoothManifolds.FiniteProperEmbedding.openSubmanifold S (U i) (hUo i)))
    (fun i => openSmoothInclusion S (U i) (hUo i))
    (fun i => chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, U i⟩))
  · intro i
    exact (openSmoothInclusion_square S (U i) (hUo i)).symm
  · intro i k
    exact openSmoothInclusion_injective S (U i) (hUo i) k
  · intro i k
    exact P202.RelativeSingularChains.inclusion_injective ℝ ℝ ⟨TopCat.of M, U i⟩ k
  · intro k z
    obtain ⟨i, hi⟩ := finiteChain_in_directed_open U hUo hUc hdU k z
    obtain ⟨z', hz'⟩ := openChain_lift (X := TopCat.of M) (U i) k z hi
    exact ⟨i, z', hz'⟩
  · intro k x y
    obtain ⟨i, hi⟩ := finiteChain_in_directed_open U hUo hUc hdU k x.val
    obtain ⟨j, hj⟩ := finiteChain_in_directed_open U hUo hUc hdU (k+1) y
    obtain ⟨t, hit, hjt⟩ := hdU i j
    obtain ⟨x', hx'⟩ := openSmoothChain_lift S (U t) (hUo t) k x
      (fun σ hσ z => hit (hi σ hσ z))
    obtain ⟨y', hy'⟩ := openChain_lift (X := TopCat.of M) (U t) (k+1) y
      (fun σ hσ z => hjt (hj σ hσ z))
    exact ⟨t, x', y', hx', hy'⟩
  · exact hiso

end DirectedComparison

section SubmoduleMayerVietoris
universe v
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

def submoduleIntersectionMap (A B : Submodule R V) :
    ↥(A ⊓ B) →ₗ[R] (A × B) where
  toFun x := (⟨x.val, x.property.1⟩, ⟨-x.val, B.neg_mem x.property.2⟩)
  map_add' _ _ := by ext <;> simp [add_comm]
  map_smul' _ _ := by ext <;> simp

def submoduleAdditionMap (A B : Submodule R V) : (A × B) →ₗ[R] ↥(A ⊔ B) where
  toFun x := ⟨x.1.val + x.2.val,
    (A ⊔ B).add_mem (Submodule.mem_sup_left x.1.property) (Submodule.mem_sup_right x.2.property)⟩
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_add]

theorem submoduleIntersection_addition (A B : Submodule R V) :
    (submoduleAdditionMap A B).comp (submoduleIntersectionMap A B) = 0 := by
  ext x
  change x.val + -x.val = 0
  exact add_neg_cancel _

def submoduleSignedSequence (A B : Submodule R V) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom (submoduleIntersectionMap A B))
    (ModuleCat.ofHom (submoduleAdditionMap A B))
    (by apply ModuleCat.hom_ext; exact submoduleIntersection_addition A B)

theorem submoduleSignedSequence_shortExact (A B : Submodule R V) :
    (submoduleSignedSequence A B).ShortExact := by
  have hi : Function.Injective (submoduleIntersectionMap A B) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : A × B => z.1.val) hxy
  have hs : Function.Surjective (submoduleAdditionMap A B) := by
    intro z
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp z.property
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  haveI : Mono (submoduleSignedSequence A B).f :=
    (ModuleCat.mono_iff_injective _).mpr hi
  haveI : Epi (submoduleSignedSequence A B).g :=
    (ModuleCat.epi_iff_surjective _).mpr hs
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro y hy
  have hy' : y.1.val + y.2.val = 0 := congrArg Subtype.val hy
  have hyB : y.1.val ∈ B := by
    rw [eq_neg_of_add_eq_zero_left hy']
    exact B.neg_mem y.2.property
  refine ⟨⟨y.1.val, y.1.property, hyB⟩, ?_⟩
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change -y.1.val = y.2.val
    rw [eq_neg_of_add_eq_zero_left hy', neg_neg]


end SubmoduleMayerVietoris

section OpenSetGlobalization
universe v
variable {X : Type u} [TopologicalSpace X]
open Set

/-- Good-cover gluing with openness retained in the property. -/
theorem open_iUnion_of_finiteInter {P : Set X → Prop}
    (h0 : P ∅)
    (hunion : ∀ U V, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) → P (U ∪ V))
    (hdir : ∀ C : Set (Set X), C.Nonempty → DirectedOn (· ⊆ ·) C →
      (∀ U ∈ C, IsOpen U ∧ P U) → P (⋃₀ C))
    {ι : Type v} (U : ι → Set X)
    (hU : ∀ t : Finset ι, t.Nonempty → IsOpen (⋂ i ∈ t, U i) ∧ P (⋂ i ∈ t, U i)) :
    P (⋃ i, U i) := by
  have hh : IsOpen (⋃ i, U i) ∧ P (⋃ i, U i) := by
    apply iUnion_of_finiteInter (P := fun W => IsOpen W ∧ P W) ⟨isOpen_empty, h0⟩
    · intro V W hV hW hVW
      exact ⟨hV.1.union hW.1, hunion V W hV.1 hW.1 hV.2 hW.2 hVW.2⟩
    · intro V hd hV
      refine ⟨isOpen_iUnion (fun s => (hV s).1), ?_⟩
      have hh := hdir (range V) (range_nonempty V) hd.directedOn_range
        (by rintro _ ⟨s, rfl⟩; exact hV s)
      simpa only [sUnion_range] using hh
    · exact hU
  exact hh.2

/-- An open subset of one Euclidean chart is covered by convex coordinate
pieces, and every nonempty finite intersection remains a convex coordinate piece. -/
theorem openSubset_chart_property {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set X → Prop} (h0 : P ∅)
    (hunion : ∀ U V, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) → P (U ∪ V))
    (hdir : ∀ C : Set (Set X), C.Nonempty → DirectedOn (· ⊆ ·) C →
      (∀ U ∈ C, IsOpen U ∧ P U) → P (⋃₀ C))
    (e : OpenPartialHomeomorph X E)
    (hlocal : ∀ V, IsOpen V → V ⊆ e.source → Convex ℝ (e '' V) → P V)
    (U : Set X) (hU : IsOpen U) (hUs : U ⊆ e.source) : P U := by
  classical
  let W := e '' U
  have hW : IsOpen W := e.isOpen_image_of_subset_source hU hUs
  let J := {V : Set E // IsOpen V ∧ Convex ℝ V ∧ V ⊆ W}
  let A : J → Set X := fun V => e.source ∩ e ⁻¹' V.val
  have hAopen : ∀ V : J, IsOpen (A V) := fun V => e.isOpen_inter_preimage V.property.1
  have hcover : (⋃ V : J, A V) = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨V, hxV⟩ := mem_iUnion.mp hx
      obtain ⟨y, hy, hey⟩ := V.property.2.2 hxV.2
      have hxy : y = x := e.injOn (hUs hy) hxV.1 hey
      simpa only [hxy] using hy
    · intro hx
      have hxW : e x ∈ W := ⟨x, hx, rfl⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW (e x) hxW
      let V : J := ⟨Metric.ball (e x) ε, Metric.isOpen_ball, convex_ball _ _, hball⟩
      exact mem_iUnion.mpr ⟨V, hUs hx, Metric.mem_ball_self hε⟩
  rw [← hcover]
  apply open_iUnion_of_finiteInter h0 hunion hdir A
  intro t ht
  have hTopen : IsOpen (⋂ V ∈ t, A V) := isOpen_biInter_finset (fun V _ => hAopen V)
  have hTs : (⋂ V ∈ t, A V) ⊆ e.source := by
    obtain ⟨V, hV⟩ := ht
    intro x hx
    exact (mem_iInter₂.mp hx V hV).1
  refine ⟨hTopen, hlocal _ hTopen hTs ?_⟩
  have heq : e '' (⋂ V ∈ t, A V) = ⋂ V ∈ t, V.val := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_iInter₂.mpr (fun V hV => (mem_iInter₂.mp hx V hV).2)
    · intro hy
      obtain ⟨V, hV⟩ := ht
      have hyW : y ∈ W := V.property.2.2 (mem_iInter₂.mp hy V hV)
      obtain ⟨x, hx, hxy⟩ := hyW
      refine ⟨x, ?_, hxy⟩
      apply mem_iInter₂.mpr
      intro V hV
      exact ⟨hUs hx, by change e x ∈ V.val; rw [hxy]; exact mem_iInter₂.mp hy V hV⟩
  rw [heq]
  exact convex_iInter₂ (fun V _ => V.property.2.1)

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
/-- A property of open subsets that is local on convex coordinate pieces and
obeys Mayer–Vietoris gluing and directed-union passage holds globally. -/
theorem manifold_property_of_convexCharts {n : ℕ}
    (S : SmoothManifold n .euclidean X) {P : Set X → Prop} (h0 : P ∅)
    (hunion : ∀ U V, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) → P (U ∪ V))
    (hdir : ∀ C : Set (Set X), C.Nonempty → DirectedOn (· ⊆ ·) C →
      (∀ U ∈ C, IsOpen U ∧ P U) → P (⋃₀ C))
    (hlocal : ∀ c : ModelChart n .euclidean X, c ∈ S.smoothStructure.val →
      ∀ U, IsOpen U → U ⊆ c.source → Convex ℝ (Subtype.val '' (c '' U)) → P U) :
    P Set.univ := by
  classical
  have hchart : ∀ c : ModelChart n .euclidean X, c ∈ S.smoothStructure.val →
      ∀ U, IsOpen U → U ⊆ c.source → P U := by
    intro c hc U hU hUs
    let e := c.transHomeomorph (Homeomorph.Set.univ (Euclidean n))
    apply openSubset_chart_property h0 hunion hdir e ?_ U hU hUs
    intro V hV hVs hconv
    apply hlocal c hc V hV hVs
    have heq : e '' V = Subtype.val '' (c '' V) := by
      rw [Set.image_image]
      rfl
    rwa [heq] at hconv
  let J := {c : ModelChart n .euclidean X // c ∈ S.smoothStructure.val}
  let U : J → Set X := fun c => c.val.source
  have hcover : (⋃ c : J, U c) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 x
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hxc⟩
  rw [← hcover]
  apply open_iUnion_of_finiteInter h0 hunion hdir U
  intro t ht
  have hTopen : IsOpen (⋂ c ∈ t, U c) :=
    isOpen_biInter_finset (fun c _ => c.val.open_source)
  obtain ⟨c, hc⟩ := ht
  refine ⟨hTopen, hchart c.val c.property _ hTopen ?_⟩
  exact fun _ hx => mem_iInter₂.mp hx c hc

end OpenSetGlobalization

section DiffeomorphismComparison
open SmoothManifolds.MapData Set

def smoothChainIsoOfHomeomorph (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (h : M ≃ₜ N) (hf : IsSmoothMap S T h) (hg : IsSmoothMap T S h.symm) :
    smoothComplex S ≅ smoothComplex T where
  hom := smoothChainMap S T h hf
  inv := smoothChainMap T S h.symm hg
  hom_inv_id := by
    ext q z
    apply Subtype.ext
    change ((chainMap ℝ ℝ (underlyingMap T S h.symm hg)).f q)
      (((chainMap ℝ ℝ (underlyingMap S T h hf)).f q) z.val) = z.val
    have hm : underlyingMap S T h hf ≫ underlyingMap T S h.symm hg = 𝟙 (TopCat.of M) := by
      ext x
      exact h.symm_apply_apply x
    change ((chainMap ℝ ℝ (underlyingMap S T h hf) ≫
      chainMap ℝ ℝ (underlyingMap T S h.symm hg)).f q) z.val = z.val
    rw [← P202.SingularChains.chainMap_comp, hm, P202.SingularChains.chainMap_id]
    rfl
  inv_hom_id := by
    ext q z
    apply Subtype.ext
    change ((chainMap ℝ ℝ (underlyingMap S T h hf)).f q)
      (((chainMap ℝ ℝ (underlyingMap T S h.symm hg)).f q) z.val) = z.val
    have hm : underlyingMap T S h.symm hg ≫ underlyingMap S T h hf = 𝟙 (TopCat.of N) := by
      ext x
      exact h.apply_symm_apply x
    change ((chainMap ℝ ℝ (underlyingMap T S h.symm hg) ≫
      chainMap ℝ ℝ (underlyingMap S T h hf)).f q) z.val = z.val
    rw [← P202.SingularChains.chainMap_comp, hm, P202.SingularChains.chainMap_id]
    rfl

/-- The inclusion comparison is invariant under a smooth diffeomorphism of the
actual smooth structures. -/
theorem comparison_homeomorph_iff (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (h : M ≃ₜ N) (hf : IsSmoothMap S T h) (hg : IsSmoothMap T S h.symm) (q : ℕ) :
    IsIso (homologyMap (inclusion S) q) ↔ IsIso (homologyMap (inclusion T) q) := by
  let e := smoothChainIsoOfHomeomorph S T h hf hg
  haveI : IsIso (smoothChainMap S T h hf) := by
    change IsIso e.hom
    infer_instance
  have heq : underlyingMap S T h hf = (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) h).hom := rfl
  haveI : IsIso (underlyingMap S T h hf) := by rw [heq]; infer_instance
  haveI : IsIso (chainMap ℝ ℝ (underlyingMap S T h hf)) := by infer_instance
  haveI : IsIso (homologyMap (smoothChainMap S T h hf) q) := by infer_instance
  haveI : IsIso (homologyMap (chainMap ℝ ℝ (underlyingMap S T h hf)) q) := by infer_instance
  have he := congrArg (fun k => homologyMap k q) (inclusion_natural S T h hf)
  simp only [homologyMap_comp] at he
  constructor
  · intro hs
    haveI := hs
    haveI : IsIso (homologyMap (smoothChainMap S T h hf) q ≫ homologyMap (inclusion T) q) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left (homologyMap (smoothChainMap S T h hf) q) _
  · intro ht
    haveI := ht
    haveI : IsIso (homologyMap (inclusion S) q ≫ homologyMap (chainMap ℝ ℝ (underlyingMap S T h hf)) q) := by
      rw [← he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (homologyMap (chainMap ℝ ℝ (underlyingMap S T h hf)) q)

open Set

/-- The canonical open manifold construction is compatible with nested opens,
up to the identity map on the actual ambient points. -/
theorem comparison_openSubmanifold_nested_iff
    (S : SmoothManifolds.AtlasData.SmoothManifold n a M) (U : Set M) (hU : IsOpen U)
    (V : Set U) (hV : IsOpen V) (q : ℕ) :
    IsIso (homologyMap (inclusion
      (SmoothManifolds.FiniteProperEmbedding.openSubmanifold
        (SmoothManifolds.FiniteProperEmbedding.openSubmanifold S U hU) V hV)) q) ↔
      IsIso (homologyMap (inclusion (SmoothManifolds.FiniteProperEmbedding.openSubmanifold S
        (Subtype.val '' V) (hU.isOpenMap_subtype_val V hV))) q) := by
  let W : Set M := Subtype.val '' V
  have hW : IsOpen W := hU.isOpenMap_subtype_val V hV
  let h : V ≃ₜ W := _root_.Topology.IsEmbedding.subtypeVal.homeomorphImage V
  have hv (x : V) : (h x).val = x.val.val := rfl
  have hiv (x : W) : (h.symm x).val.val = x.val := by
    rw [← hv, h.apply_symm_apply]
  let SU := SmoothManifolds.FiniteProperEmbedding.openSubmanifold S U hU
  let SV := SmoothManifolds.FiniteProperEmbedding.openSubmanifold SU V hV
  let SW := SmoothManifolds.FiniteProperEmbedding.openSubmanifold S W hW
  have hf : IsSmoothMap SV SW h := by
    apply (isSmoothMap_openSubmanifold_iff SV S W hW h).mpr
    change IsSmoothMap SV S (fun x : V => x.val.val)
    exact SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
      SU.smoothStructure.property.1.1 Subtype.val Subtype.val
      (smooth_openSubmanifold_inclusion SU V hV)
      (smooth_openSubmanifold_inclusion S U hU)
  have hg : IsSmoothMap SW SV h.symm := by
    apply (isSmoothMap_openSubmanifold_iff SW SU V hV h.symm).mpr
    apply (isSmoothMap_openSubmanifold_iff SW S U hU (Subtype.val ∘ h.symm)).mpr
    have heq : Subtype.val ∘ (Subtype.val ∘ h.symm) = (Subtype.val : W → M) := by
      funext x
      exact hiv x
    rw [heq]
    exact smooth_openSubmanifold_inclusion S W hW
  exact comparison_homeomorph_iff SV SW h hf hg q


end DiffeomorphismComparison

section BiprodComparison
open CategoryTheory.Limits

theorem homology_biprod_map_isIso
    {A B C D : ChainComplex (ModuleCat.{u} ℝ) ℕ} (f : A ⟶ B) (g : C ⟶ D) (q : ℕ)
    [IsIso (homologyMap f q)] [IsIso (homologyMap g q)] :
    IsIso (homologyMap (biprod.map f g) q) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℝ) (ComplexShape.down ℕ) q
  haveI : IsIso (F.map f) := by exact ‹IsIso (homologyMap f q)›
  haveI : IsIso (F.map g) := by exact ‹IsIso (homologyMap g q)›
  letI : F.Additive := by dsimp only [F]; infer_instance
  letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  have heq : F.map (biprod.map f g) = (F.mapBiprod A C).hom ≫
      biprod.map (F.map f) (F.map g) ≫ (F.mapBiprod B D).inv := by
    apply (cancel_mono (F.mapBiprod B D).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext
    · simp only [F.mapBiprod_hom, biprod.lift_fst, Category.assoc, biprod.map_fst,
        ← F.map_comp]
      simp only [biprod.lift_fst_assoc, F.map_comp]
    · simp only [F.mapBiprod_hom, biprod.lift_snd, Category.assoc, biprod.map_snd,
        ← F.map_comp]
      simp only [biprod.lift_snd_assoc, F.map_comp]
  letI : IsIso (biprod.map (F.map f) (F.map g)) := by
    change IsIso (biprod.mapIso (asIso (F.map f)) (asIso (F.map g))).hom
    infer_instance
  change IsIso (F.map (biprod.map f g))
  rw [heq]
  infer_instance

theorem quasiIso_biprod_map
    {A B C D : ChainComplex (ModuleCat.{u} ℝ) ℕ} (f : A ⟶ B) (g : C ⟶ D)
    [QuasiIso f] [QuasiIso g] : QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  haveI : IsIso (homologyMap f q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  haveI : IsIso (homologyMap g q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  exact homology_biprod_map_isIso f g q

end BiprodComparison

section SmoothMayerVietoris
open SmoothManifolds SmoothManifolds.AtlasData SmoothManifolds.MapData Set Filter
open CategoryTheory.Limits
open P202Specs.RelativeSingularChains
open scoped Simplicial
variable {q : ℕ}

private lemma smooth_biprod_element_ext {B D : ModuleCat.{u} ℝ} {x y : (B ⊞ D : ModuleCat.{u} ℝ)}
    (h₁ : (biprod.fst : B ⊞ D ⟶ B) x = (biprod.fst : B ⊞ D ⟶ B) y)
    (h₂ : (biprod.snd : B ⊞ D ⟶ D) x = (biprod.snd : B ⊞ D ⟶ D) y) : x = y := by
  have h := congrArg (fun k : B ⊞ D ⟶ B ⊞ D => k x - k y)
    (biprod.total (X := B) (Y := D))
  have he : x - y = 0 := by
    simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
      h₁, h₂, sub_self, ModuleCat.id_apply] using h.symm
  exact sub_eq_zero.mp he

/-- The signed overlap diagram is exact as soon as its embedded ranges have
intersection equal to the overlap range. -/
private lemma smooth_signed_biprod_exact {A B D E : ModuleCat.{u} ℝ} (i : A ⟶ B) (j : A ⟶ D) (l : B ⟶ E) (r : D ⟶ E)
    (hcomm : i ≫ l = j ≫ r) (hl : Function.Injective l) (hr : Function.Injective r)
    (hinf : (i ≫ l).hom.range = l.hom.range ⊓ r.hom.range) :
    (ShortComplex.mk (biprod.lift i (-j)) (biprod.desc l r)
      (by simp only [biprod.lift_desc, Preadditive.neg_comp, hcomm, add_neg_cancel])).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro y hy
  have hs : l ((biprod.fst : B ⊞ D ⟶ B) y) +
      r ((biprod.snd : B ⊞ D ⟶ D) y) = 0 := by
    simpa only [biprod.desc_eq, ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.comp_apply] using hy
  have hneg : -r ((biprod.snd : B ⊞ D ⟶ D) y) =
      l ((biprod.fst : B ⊞ D ⟶ B) y) := by
    exact (eq_neg_of_add_eq_zero_left hs).symm
  have hmem : l ((biprod.fst : B ⊞ D ⟶ B) y) ∈ l.hom.range ⊓ r.hom.range :=
    ⟨⟨_, rfl⟩, ⟨-(biprod.snd : B ⊞ D ⟶ D) y, by rw [map_neg]; exact hneg⟩⟩
  rw [← hinf] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, smooth_biprod_element_ext ?_ ?_⟩
  · have hi : (biprod.fst : B ⊞ D ⟶ B) ((biprod.lift i (-j)) x) = i x :=
      congrArg (fun k : A ⟶ B => k x) (biprod.lift_fst i (-j))
    rw [hi]
    exact hl hx
  · have hj : (biprod.snd : B ⊞ D ⟶ D) ((biprod.lift i (-j)) x) = -j x :=
      congrArg (fun k : A ⟶ D => k x) (biprod.lift_snd i (-j))
    rw [hj]
    apply hr
    rw [map_neg]
    have hx' : r (j x) = l ((biprod.fst : B ⊞ D ⟶ B) y) :=
      (congrArg (fun k : A ⟶ E => k x) hcomm).symm.trans hx
    rw [hx', ← hneg, neg_neg]


theorem smallSmoothModule_eq_sup_ranges_lift (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    smoothModule S q ⊓ P202Specs.SmallChainHomology.smallModule ℝ C q =
      ((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, C.sets ⟨false⟩⟩)).f q).hom).comp
        (smoothModule (FiniteProperEmbedding.openSubmanifold S _ (C.isOpen ⟨false⟩)) q).subtype).range ⊔
      ((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, C.sets ⟨true⟩⟩)).f q).hom).comp
        (smoothModule (FiniteProperEmbedding.openSubmanifold S _ (C.isOpen ⟨true⟩)) q).subtype).range := by
  rw [range_openSmoothInclusion S _ (C.isOpen ⟨false⟩),
    range_openSmoothInclusion S _ (C.isOpen ⟨true⟩)]
  change Finsupp.supported ℝ ℝ _ ⊓ Finsupp.supported ℝ ℝ _ =
    (Finsupp.supported ℝ ℝ _ ⊓ Finsupp.supported ℝ ℝ _) ⊔
      (Finsupp.supported ℝ ℝ _ ⊓ Finsupp.supported ℝ ℝ _)
  simp only [← Finsupp.supported_inter, ← Finsupp.supported_union]
  congr 1
  ext σ
  simp only [mem_inter_iff, mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨hσ, ⟨⟨b⟩, hb⟩⟩
    cases b with
    | false => exact Or.inl ⟨hσ, Set.range_subset_iff.mp hb⟩
    | true => exact Or.inr ⟨hσ, Set.range_subset_iff.mp hb⟩
  · rintro (⟨hσ, hU⟩ | ⟨hσ, hV⟩)
    · exact ⟨hσ, ⟨false⟩, Set.range_subset_iff.mpr hU⟩
    · exact ⟨hσ, ⟨true⟩, Set.range_subset_iff.mpr hV⟩

abbrev smoothCoverPiece (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) (b : Bool) :=
  FiniteProperEmbedding.openSubmanifold S (C.sets ⟨b⟩) (C.isOpen ⟨b⟩)

abbrev smoothCoverIntersection (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :=
  FiniteProperEmbedding.openSubmanifold S (C.sets ⟨false⟩ ∩ C.sets ⟨true⟩)
    ((C.isOpen ⟨false⟩).inter (C.isOpen ⟨true⟩))

def smoothCoverToPiece (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) (b : Bool) :
    smoothComplex (smoothCoverIntersection S C) ⟶ smoothComplex (smoothCoverPiece S C b) := by
  have hsubset : C.sets ⟨false⟩ ∩ C.sets ⟨true⟩ ⊆ C.sets ⟨b⟩ := by
    cases b
    · exact inter_subset_left
    · exact inter_subset_right
  exact smoothChainMap _ _ (Set.inclusion hsubset)
    (smooth_openSubmanifold_inclusion_of_subset S _ _ _ _ hsubset)

abbrev smoothCoverMiddle (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :=
  smoothComplex (smoothCoverPiece S C false) ⊞ smoothComplex (smoothCoverPiece S C true)

def smoothCoverFirst (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    smoothComplex (smoothCoverIntersection S C) ⟶ smoothCoverMiddle S C :=
  biprod.lift (smoothCoverToPiece S C false) (-smoothCoverToPiece S C true)

def smoothCoverSum (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    smoothCoverMiddle S C ⟶ smoothComplex S :=
  biprod.desc (openSmoothInclusion S _ (C.isOpen ⟨false⟩))
    (openSmoothInclusion S _ (C.isOpen ⟨true⟩))

theorem smoothCover_piece_square (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) (b : Bool) :
    smoothCoverToPiece S C b ≫ openSmoothInclusion S _ (C.isOpen ⟨b⟩) =
      openSmoothInclusion S _ ((C.isOpen ⟨false⟩).inter (C.isOpen ⟨true⟩)) := by
  cases b <;>
    apply HomologicalComplex.hom_ext <;> intro q <;>
    apply ModuleCat.hom_ext <;> apply LinearMap.ext <;> intro z <;>
    apply Subtype.ext <;>
    change Finsupp.mapDomain _ (Finsupp.mapDomain _ z.val) = Finsupp.mapDomain _ z.val <;>
    rw [← Finsupp.mapDomain_comp] <;> rfl

theorem smoothCoverFirst_sum (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    smoothCoverFirst S C ≫ smoothCoverSum S C = 0 := by
  simp only [smoothCoverFirst, smoothCoverSum, biprod.lift_desc,
    Preadditive.neg_comp, smoothCover_piece_square, add_neg_cancel]

theorem smoothCoverFirst_degree (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) (q : ℕ) :
    (smoothCoverFirst S C).f q ≫ (biprodXIso _ _ q).hom =
      biprod.lift ((smoothCoverToPiece S C false).f q)
        (-((smoothCoverToPiece S C true).f q)) := by
  apply biprod.hom_ext <;>
    simp only [Category.assoc, biprodXIso_hom_fst, biprodXIso_hom_snd,
      smoothCoverFirst, biprod_lift_fst_f, biprod_lift_snd_f, biprod.lift_fst,
      biprod.lift_snd, neg_f_apply]

theorem smoothCoverSum_degree (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) (q : ℕ) :
    (biprodXIso _ _ q).inv ≫ (smoothCoverSum S C).f q =
      biprod.desc ((openSmoothInclusion S _ (C.isOpen ⟨false⟩)).f q)
        ((openSmoothInclusion S _ (C.isOpen ⟨true⟩)).f q) := by
  apply biprod.hom_ext' <;>
    simp only [← Category.assoc, inl_biprodXIso_inv, inr_biprodXIso_inv,
      smoothCoverSum, biprod_inl_desc_f, biprod_inr_desc_f, biprod.inl_desc, biprod.inr_desc]

theorem smoothCover_overlap_exact (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    (ShortComplex.mk (smoothCoverFirst S C) (smoothCoverSum S C)
      (smoothCoverFirst_sum S C)).Exact := by
  apply HomologicalComplex.exact_of_degreewise_exact
  intro q
  have hc : (smoothCoverToPiece S C false).f q ≫
      (openSmoothInclusion S _ (C.isOpen ⟨false⟩)).f q =
      (smoothCoverToPiece S C true).f q ≫
      (openSmoothInclusion S _ (C.isOpen ⟨true⟩)).f q := by
    rw [← comp_f, ← comp_f, smoothCover_piece_square, smoothCover_piece_square]
  have hi : ((smoothCoverToPiece S C false).f q ≫
      (openSmoothInclusion S _ (C.isOpen ⟨false⟩)).f q).hom.range =
      ((openSmoothInclusion S _ (C.isOpen ⟨false⟩)).f q).hom.range ⊓
        ((openSmoothInclusion S _ (C.isOpen ⟨true⟩)).f q).hom.range := by
    rw [← comp_f, smoothCover_piece_square]
    apply Submodule.map_injective_of_injective (inclusion_injective S q)
    rw [Submodule.map_inf _ (inclusion_injective S q),
      ← LinearMap.range_comp, ← LinearMap.range_comp, ← LinearMap.range_comp]
    exact range_openSmoothInclusion_inter S _ _ (C.isOpen ⟨false⟩) (C.isOpen ⟨true⟩)
  have he := smooth_signed_biprod_exact _ _ _ _ hc
    (openSmoothInclusion_injective S _ (C.isOpen ⟨false⟩) q)
    (openSmoothInclusion_injective S _ (C.isOpen ⟨true⟩) q) hi
  let T := ShortComplex.mk
    (biprod.lift ((smoothCoverToPiece S C false).f q) (-((smoothCoverToPiece S C true).f q)))
    (biprod.desc ((openSmoothInclusion S _ (C.isOpen ⟨false⟩)).f q)
      ((openSmoothInclusion S _ (C.isOpen ⟨true⟩)).f q))
    (by simp only [biprod.lift_desc, Preadditive.neg_comp, hc, add_neg_cancel])
  let e : ((ShortComplex.mk (smoothCoverFirst S C) (smoothCoverSum S C)
      (smoothCoverFirst_sum S C)).map (eval _ _ q)) ≅ T :=
    ShortComplex.isoMk (Iso.refl _) (biprodXIso _ _ q) (Iso.refl _)
      (by
        change 𝟙 _ ≫ _ = _
        rw [Category.id_comp]
        exact (smoothCoverFirst_degree S C q).symm)
      (by
        dsimp only [T]
        change (biprodXIso _ _ q).hom ≫ _ = (smoothCoverSum S C).f q ≫ 𝟙 _
        rw [Category.comp_id, ← smoothCoverSum_degree S C q, Iso.hom_inv_id_assoc])
  exact (ShortComplex.exact_iff_of_iso e).mpr he

def smoothPieceToSmall (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) (b : Bool) :
    smoothComplex (smoothCoverPiece S C b) ⟶ smallSmoothComplex S C :=
  ChainComplex.ofHom (fun q => ModuleCat.ofHom
    (((((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, C.sets ⟨b⟩⟩)).f q).hom).comp
      (smoothModule (smoothCoverPiece S C b) q).subtype).codRestrict
        (smallSmoothModule S C q) (by
          intro z
          have hz : (chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, C.sets ⟨b⟩⟩)).f q z.val ∈
              smoothModule S q ⊓ Finsupp.supported ℝ ℝ
                {σ | ∀ x, simplexEquiv (TopCat.of M) q σ x ∈ C.sets ⟨b⟩} := by
            rw [← range_openSmoothInclusion S _ (C.isOpen ⟨b⟩)]
            exact ⟨z, rfl⟩
          refine ⟨hz.1, ?_⟩
          intro σ hσ
          exact ⟨⟨b⟩, Set.range_subset_iff.mpr (hz.2 hσ)⟩)))
    (by
      intro q
      simp only [smallSmoothComplex, smoothComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun k => k z.val)
        ((chainMap ℝ ℝ (Pair.inclusion ⟨TopCat.of M, C.sets ⟨b⟩⟩)).comm (q+1) q))

@[reassoc (attr := simp)] theorem smoothPieceToSmall_inclusion
    (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) (b : Bool) :
    smoothPieceToSmall S C b ≫ smallSmoothInclusion S C =
      openSmoothInclusion S _ (C.isOpen ⟨b⟩) := by
  ext q z
  rfl

def smoothCoverSmallSum (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    smoothCoverMiddle S C ⟶ smallSmoothComplex S C :=
  biprod.desc (smoothPieceToSmall S C false) (smoothPieceToSmall S C true)

@[reassoc (attr := simp)] theorem smoothCoverSmallSum_inclusion
    (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    smoothCoverSmallSum S C ≫ smallSmoothInclusion S C = smoothCoverSum S C := by
  apply biprod.hom_ext' <;>
    simp only [smoothCoverSmallSum, smoothCoverSum, ← Category.assoc,
      biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.inl_desc,
      biprod.inr_desc, smoothPieceToSmall_inclusion]

instance smallSmoothInclusion_mono (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    Mono (smallSmoothInclusion S C) := by
  apply HomologicalComplex.mono_of_mono_f
  intro q
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : smoothModule S q => z.val) h

theorem smoothCoverFirst_smallSum (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    smoothCoverFirst S C ≫ smoothCoverSmallSum S C = 0 := by
  apply (cancel_mono (smallSmoothInclusion S C)).mp
  rw [Category.assoc, smoothCoverSmallSum_inclusion, smoothCoverFirst_sum, zero_comp]

theorem smoothCoverFirst_mono (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    Mono (smoothCoverFirst S C) := by
  haveI : Mono (openSmoothInclusion S (C.sets ⟨false⟩ ∩ C.sets ⟨true⟩)
      ((C.isOpen ⟨false⟩).inter (C.isOpen ⟨true⟩))) := by
    apply HomologicalComplex.mono_of_mono_f
    intro q
    exact (ModuleCat.mono_iff_injective _).mpr (openSmoothInclusion_injective S _ _ q)
  have hfac : smoothCoverFirst S C ≫
      ((biprod.fst : smoothCoverMiddle S C ⟶ _) ≫
        openSmoothInclusion S _ (C.isOpen ⟨false⟩)) =
      openSmoothInclusion S _ ((C.isOpen ⟨false⟩).inter (C.isOpen ⟨true⟩)) := by
    rw [smoothCoverFirst, biprod.lift_fst_assoc, smoothCover_piece_square]
  exact mono_of_mono_fac hfac

theorem smoothCoverSmallSum_epi (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    Epi (smoothCoverSmallSum S C) := by
  apply HomologicalComplex.epi_of_epi_f
  intro q
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro z
  have hz := (smallSmoothModule_eq_sup_ranges_lift (q := q) S C).le z.property
  obtain ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, hab⟩ := Submodule.mem_sup.mp hz
  let w : (smoothCoverMiddle S C).X q :=
    (biprod.inl : _ ⟶ smoothCoverMiddle S C).f q x +
      (biprod.inr : _ ⟶ smoothCoverMiddle S C).f q y
  refine ⟨w, ?_⟩
  apply Subtype.ext
  have hw : ((smoothCoverSum S C).f q w).val = z.val := by
    dsimp only [w]
    rw [map_add, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      smoothCoverSum, biprod_inl_desc_f, biprod_inr_desc_f]
    exact hab
  exact (congrArg (fun k => (k.f q w).val) (smoothCoverSmallSum_inclusion S C)).trans hw

theorem smoothCover_small_shortExact (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    (ShortComplex.mk (smoothCoverFirst S C) (smoothCoverSmallSum S C)
      (smoothCoverFirst_smallSum S C)).ShortExact := by
  letI := smoothCoverFirst_mono S C
  letI := smoothCoverSmallSum_epi S C
  refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
  let φ : ShortComplex.mk (smoothCoverFirst S C) (smoothCoverSmallSum S C)
      (smoothCoverFirst_smallSum S C) ⟶
      ShortComplex.mk (smoothCoverFirst S C) (smoothCoverSum S C) (smoothCoverFirst_sum S C) :=
    ShortComplex.Hom.mk (𝟙 _) (𝟙 _) (smallSmoothInclusion S C)
      (by simp) (by simpa using (smoothCoverSmallSum_inclusion S C).symm)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr (smoothCover_overlap_exact S C)

def smoothCoverPair (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    P202Specs.MayerVietoris.CoverPair.{u,0} where
  pair := ⟨TopCat.of M, ∅⟩
  cover := C

def smallSmoothToOrdinary (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    smallSmoothComplex S C ⟶ P202Specs.SmallChainHomology.smallComplex ℝ C :=
  ChainComplex.ofHom (fun q => ModuleCat.ofHom
    (((smallSmoothModule S C q).subtype).codRestrict
      (P202Specs.SmallChainHomology.smallModule ℝ C q) (fun z => z.property.2)))
    (by intro q; simp only [smallSmoothComplex, P202Specs.SmallChainHomology.smallComplex,
      ChainComplex.of_d]; rfl)

@[reassoc (attr := simp)] theorem smallSmoothToOrdinary_square
    (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    smallSmoothToOrdinary S C ≫ P202Specs.SmallChainHomology.smallInclusion ℝ C =
      smallSmoothInclusion S C ≫ inclusion S := by
  ext q z
  rfl

def smoothCoverComparison (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool)) :
    ShortComplex.mk (smoothCoverFirst S C) (smoothCoverSmallSum S C)
      (smoothCoverFirst_smallSum S C) ⟶
      ShortComplex.mk (P202.MayerVietoris.firstN ℝ (smoothCoverPair C))
        (P202.MayerVietoris.smallSumN ℝ (smoothCoverPair C))
        (P202.MayerVietoris.firstN_smallSumN ℝ (smoothCoverPair C)) :=
  ShortComplex.Hom.mk (inclusion (smoothCoverIntersection S C))
    (biprod.map (inclusion (smoothCoverPiece S C false)) (inclusion (smoothCoverPiece S C true)))
    (smallSmoothToOrdinary S C)
    (by
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
          smoothCoverFirst, P202.MayerVietoris.firstN, biprod.lift_fst]
        ext q z
        rfl
      · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
          smoothCoverFirst, P202.MayerVietoris.firstN, biprod.lift_snd,
          Preadditive.comp_neg, Preadditive.neg_comp]
        ext q z
        rfl)
    (by
      apply biprod.hom_ext'
      · simp only [Category.assoc, biprod.inl_map_assoc,
          P202.MayerVietoris.smallSumN, smoothCoverSmallSum, biprod.inl_desc_assoc,
          biprod.inl_desc]
        ext q z
        rfl
      · simp only [Category.assoc, biprod.inr_map_assoc,
          P202.MayerVietoris.smallSumN, smoothCoverSmallSum, biprod.inr_desc_assoc,
          biprod.inr_desc]
        ext q z
        rfl)

set_option maxHeartbeats 800000 in
theorem binaryCover_comparison_of_middle (S : AtlasData.SmoothManifold n a M)
    (C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool))
    (hi : QuasiIso (inclusion (smoothCoverIntersection S C)))
    (hm : QuasiIso (biprod.map (inclusion (smoothCoverPiece S C false))
      (inclusion (smoothCoverPiece S C true)))) : QuasiIso (inclusion S) := by
  have hsmall : QuasiIso (smallSmoothToOrdinary S C) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ (smoothCoverComparison S C)
      (smoothCover_small_shortExact S C)
      (P202.MayerVietoris.nonnegative_small_shortExact ℝ (smoothCoverPair C)) hi hm
  letI := hsmall
  haveI : QuasiIso (P202Specs.SmallChainHomology.smallInclusion ℝ C) := by
    rw [quasiIso_iff]
    intro q
    exact (quasiIsoAt_iff_isIso_homologyMap _ q).mpr
      (P202.SmallChainHomology.absoluteComparison ℝ (TopCat.of M) _ C q)
  haveI : QuasiIso (smallSmoothInclusion S C) := by
    rw [quasiIso_iff]
    intro q
    exact (quasiIsoAt_iff_isIso_homologyMap _ q).mpr (smallSmoothComparison S C q)
  haveI : QuasiIso (smallSmoothInclusion S C ≫ inclusion S) := by
    rw [← smallSmoothToOrdinary_square]
    infer_instance
  exact quasiIso_of_comp_left (smallSmoothInclusion S C) (inclusion S)

/-- Binary-open-cover comparison with the actual open-submanifold complexes. -/
theorem comparison_of_binary_open_cover (S : AtlasData.SmoothManifold n a M)
    (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hleft : ∀ q, IsIso (homologyMap
      (inclusion (FiniteProperEmbedding.openSubmanifold S U hU)) q))
    (hright : ∀ q, IsIso (homologyMap
      (inclusion (FiniteProperEmbedding.openSubmanifold S V hV)) q))
    (hinter : ∀ q, IsIso (homologyMap
      (inclusion (FiniteProperEmbedding.openSubmanifold S (U ∩ V) (hU.inter hV))) q))
    (q : ℕ) : IsIso (homologyMap (inclusion S) q) := by
  let C : P202Specs.SmallChainHomology.OpenCover (TopCat.of M) (ULift.{0} Bool) := {
    sets := fun b => if b.down then V else U
    isOpen := by intro ⟨b⟩; cases b <;> assumption
    covers := by
      intro x
      have hx : x ∈ U ∪ V := by rw [hcover]; trivial
      rcases hx with hx | hx
      · exact ⟨⟨false⟩, hx⟩
      · exact ⟨⟨true⟩, hx⟩ }
  haveI : QuasiIso (inclusion (smoothCoverPiece S C false)) := by
    rw [quasiIso_iff]
    intro k
    exact (quasiIsoAt_iff_isIso_homologyMap _ k).mpr (hleft k)
  haveI : QuasiIso (inclusion (smoothCoverPiece S C true)) := by
    rw [quasiIso_iff]
    intro k
    exact (quasiIsoAt_iff_isIso_homologyMap _ k).mpr (hright k)
  have hi : QuasiIso (inclusion (smoothCoverIntersection S C)) := by
    rw [quasiIso_iff]
    intro k
    exact (quasiIsoAt_iff_isIso_homologyMap _ k).mpr (hinter k)
  have h := binaryCover_comparison_of_middle S C hi
    (quasiIso_biprod_map (inclusion (smoothCoverPiece S C false))
      (inclusion (smoothCoverPiece S C true)))
  exact (quasiIsoAt_iff_isIso_homologyMap _ q).mp (h.quasiIsoAt q)

end SmoothMayerVietoris



section BoundarylessAssembly
open Set SmoothManifolds.MapData SmoothManifolds.FiniteProperEmbedding

/-- Restricting first to a larger open does not alter the comparison on an
open subset of it; both sides use their actual maximal induced structures. -/
theorem comparison_open_subset_of_subset (S : SmoothManifold n a M)
    (W U : Set M) (hW : IsOpen W) (hU : IsOpen U) (hUW : U ⊆ W)
    (hcmp : ∀ q, IsIso (homologyMap (inclusion (openSubmanifold S U hU)) q)) (q : ℕ) :
    IsIso (homologyMap (inclusion (openSubmanifold (openSubmanifold S W hW)
      {x : W | x.val ∈ U} (hU.preimage continuous_subtype_val))) q) := by
  apply (comparison_openSubmanifold_nested_iff S W hW _ _ q).mpr
  have him : Subtype.val '' {x : W | x.val ∈ U} = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUW hx⟩, hx, rfl⟩
  let Q : Set M → Prop := fun A => ∀ hA : IsOpen A,
    IsIso (homologyMap (inclusion (openSubmanifold S A hA)) q)
  have hQ : Q U := fun _ => hcmp q
  have hQI : Q (Subtype.val '' {x : W | x.val ∈ U}) :=
    Eq.mpr (congrArg Q him) hQ
  exact hQI _

/-- Boundaryless comparison follows from the binary Mayer–Vietoris comparison
step. This lemma contains only a local-to-global reduction. -/
theorem comparison_boundaryless_of_binary
    (hbinary : ∀ {n : ℕ} {X : Type u} [TopologicalSpace X]
      (S : SmoothManifold n .euclidean X) (U V : Set X)
      (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ),
      (∀ q, IsIso (homologyMap (inclusion (openSubmanifold S U hU)) q)) →
      (∀ q, IsIso (homologyMap (inclusion (openSubmanifold S V hV)) q)) →
      (∀ q, IsIso (homologyMap (inclusion (openSubmanifold S (U ∩ V) (hU.inter hV))) q)) →
      ∀ q, IsIso (homologyMap (inclusion S) q))
    (S : SmoothManifold n .euclidean M) (q : ℕ) :
    IsIso (homologyMap (inclusion S) q) := by
  let Good : Set M → Prop := fun U => ∀ hU : IsOpen U, ∀ q,
    IsIso (homologyMap (inclusion (openSubmanifold S U hU)) q)
  have h0 : Good ∅ := by
    intro hU k
    haveI : IsIso (inclusion (openSubmanifold S ∅ hU)) :=
      inclusion_isIso_of_forall_smooth _ (fun j σ => isEmptyElim
        (simplexEquiv (TopCat.of (∅ : Set M)) j σ (Convexity.StdSimplex.single 0)))
    infer_instance
  have hunion : ∀ U V, IsOpen U → IsOpen V → Good U → Good V → Good (U ∩ V) → Good (U ∪ V) := by
    intro U V hU hV hGU hGV hGI hW k
    let E := openSubmanifold S (U ∪ V) hW
    let A : Set ↥(U ∪ V) := {x | x.val ∈ U}
    let B : Set ↥(U ∪ V) := {x | x.val ∈ V}
    have hA : IsOpen A := hU.preimage continuous_subtype_val
    have hB : IsOpen B := hV.preimage continuous_subtype_val
    have hcover : A ∪ B = univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact x.property
    apply hbinary E A B hA hB hcover
    · exact comparison_open_subset_of_subset S (U ∪ V) U hW hU subset_union_left (hGU hU)
    · exact comparison_open_subset_of_subset S (U ∪ V) V hW hV subset_union_right (hGV hV)
    · have hi : U ∩ V ⊆ U ∪ V := inter_subset_left.trans subset_union_left
      exact comparison_open_subset_of_subset S (U ∪ V) (U ∩ V) hW (hU.inter hV) hi (hGI (hU.inter hV))
  have hdir : ∀ C : Set (Set M), C.Nonempty → DirectedOn (· ⊆ ·) C →
      (∀ U ∈ C, IsOpen U ∧ Good U) → Good (⋃₀ C) := by
    intro C hC hd hG hW k
    obtain ⟨U₀, hU₀⟩ := hC
    letI : Nonempty C := ⟨⟨U₀, hU₀⟩⟩
    let E := openSubmanifold S (⋃₀ C) hW
    let V : C → Set (⋃₀ C) := fun U => {x | x.val ∈ U.val}
    have hV : ∀ U, IsOpen (V U) := fun U => (hG U.val U.property).1.preimage continuous_subtype_val
    have hVc : ∀ x : (⋃₀ C), ∃ U, x ∈ V U := by
      intro x
      obtain ⟨U, hUC, hxU⟩ := Set.mem_sUnion.mp x.property
      exact ⟨⟨U, hUC⟩, hxU⟩
    have hVd : Directed (· ⊆ ·) V := by
      intro U V
      obtain ⟨W, hWC, hUW, hVW⟩ := hd U.val U.property V.val V.property
      exact ⟨⟨W, hWC⟩, fun _ hx => hUW hx, fun _ hx => hVW hx⟩
    apply comparison_of_directed_open_cover E V hV hVc hVd
    intro U j
    exact comparison_open_subset_of_subset S (⋃₀ C) U.val hW (hG U.val U.property).1
      (fun _ hx => Set.mem_sUnion.mpr ⟨U.val, U.property, hx⟩)
      ((hG U.val U.property).2 (hG U.val U.property).1) j
  have hlocal : ∀ c : ModelChart n .euclidean M, c ∈ S.smoothStructure.val →
      ∀ U, IsOpen U → U ⊆ c.source → Convex ℝ (Subtype.val '' (c '' U)) → Good U := by
    intro c hc U _ hUc hconv hU k
    exact comparison_open_convexChart S U hU c hc hUc hconv k
  have hgood : Good univ := manifold_property_of_convexCharts S h0 hunion hdir hlocal
  let T := openSubmanifold S univ isOpen_univ
  let h : (univ : Set M) ≃ₜ M := Homeomorph.Set.univ M
  have hf : IsSmoothMap T S h := smooth_openSubmanifold_inclusion S univ isOpen_univ
  have hg : IsSmoothMap S T h.symm := by
    apply (isSmoothMap_openSubmanifold_iff S S univ isOpen_univ h.symm).mpr
    change IsSmoothMap S S id
    exact SmoothManifolds.manifoldContDiff_id _ _ S.smoothStructure.property.1
  exact (comparison_homeomorph_iff T S h hf hg q).mp (hgood isOpen_univ q)

end BoundarylessAssembly

/-- Smooth and continuous singular homology agree on every boundaryless smooth
manifold, in all nonnegative degrees, with no connectedness or compactness assumption. -/
theorem boundaryless_homology_comparison (S : SmoothManifold n .euclidean M) (q : ℕ) :
    IsIso (homologyMap (inclusion S) q) :=
  comparison_boundaryless_of_binary
    (fun S U V hU hV hUV hL hR hI q =>
      comparison_of_binary_open_cover S U V hU hV hUV hL hR hI q) S q

/-- Lemma `lem:p202-smooth-singular`: inclusion induces all homology
isomorphisms and restriction induces all real cohomology isomorphisms,
naturally for smooth maps, also for manifolds with smooth boundary. -/
theorem smoothSingularComparison : smoothSingularComparison_type.{u} :=
  comparison_from_boundaryless_homology
    (fun S q => boundaryless_homology_comparison S q)

end P202.SmoothSingularComparison
