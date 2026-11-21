import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.Pairs
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Comparison.SmoothSingularComplex
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! Independent objects for paper.tex, Lemma `lem:p202-smooth-singular`.
The manifold and local ambient extension convention are those of P104.
The ordinary complex is the shared P202 singular complex, with finite real chains.
No comparison isomorphism is assumed in any of the constructions below. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory HomologicalComplex Opposite
open scoped Simplicial
open SmoothManifolds SmoothManifolds.ModelData SmoothManifolds.AtlasData
namespace P202Specs.SmoothSingularComparison
universe u v

abbrev BarycentricSimplex (q : ℕ) := Convexity.StdSimplex ℝ (Fin (q+1))
abbrev CornerSimplex := SmoothManifolds.SmoothSingularData.Simplex

/-- The P104 ordered simplex, expressed in the barycentric coordinates of P202. -/
def toBarycentric (q : ℕ) (x : CornerSimplex q) : BarycentricSimplex q where
  weights := Finsupp.equivFunOnFinite.symm (SmoothManifolds.CornerData.simplexBarycentric x.val)
  nonneg := by
    intro i
    change 0 ≤ SmoothManifolds.CornerData.simplexBarycentric x.val i
    refine Fin.cases ?_ (fun j => x.property.1 j) i
    exact sub_nonneg.mpr x.property.2
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp [SmoothManifolds.CornerData.simplexBarycentric, Fin.sum_univ_succ]

/-- Delete the zeroth barycentric coordinate. -/
def toCorner (q : ℕ) (x : BarycentricSimplex q) : CornerSimplex q :=
  SmoothManifolds.SmoothSingularData.fromBarycentric x.weights
    x.weights_nonneg x.total_of_fintype

@[simp] theorem toBarycentric_weights (q : ℕ) (x : CornerSimplex q) (i : Fin (q+1)) :
    (toBarycentric q x).weights i =
      SmoothManifolds.CornerData.simplexBarycentric x.val i := by rfl

@[simp] theorem toCorner_val (q : ℕ) (x : BarycentricSimplex q) (i : Fin q) :
    (toCorner q x).val i = x.weights i.succ := rfl

@[simp] theorem toCorner_toBarycentric (q : ℕ) (x : CornerSimplex q) :
    toCorner q (toBarycentric q x) = x := by
  apply Subtype.ext
  rfl

@[simp] theorem toBarycentric_toCorner (q : ℕ) (x : BarycentricSimplex q) :
    toBarycentric q (toCorner q x) = x := by
  apply Convexity.StdSimplex.ext
  ext i
  refine Fin.cases ?_ (fun j => by rfl) i
  change 1 - ∑ j : Fin q, x.weights j.succ = x.weights 0
  have hx := x.total_of_fintype
  rw [Fin.sum_univ_succ] at hx
  linarith

theorem continuous_toBarycentric (q : ℕ) : Continuous (toBarycentric q) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (q+1))).continuous_iff]
  apply continuous_pi
  intro i
  simp only [Function.comp_def, toBarycentric_weights]
  refine Fin.cases ?_ (fun j => (continuous_apply j).comp continuous_subtype_val) i
  exact continuous_const.sub (continuous_finsetSum _ (fun j _ =>
    (continuous_apply j).comp continuous_subtype_val))

theorem continuous_toCorner (q : ℕ) : Continuous (toCorner q) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact Convexity.StdSimplex.continuous_weights_apply ℝ i.succ

/-- A homeomorphism of the actual two geometric domains, including degree zero. -/
def simplexHomeomorph (q : ℕ) : CornerSimplex q ≃ₜ BarycentricSimplex q where
  toFun := toBarycentric q
  invFun := toCorner q
  left_inv := toCorner_toBarycentric q
  right_inv := toBarycentric_toCorner q
  continuous_toFun := continuous_toBarycentric q
  continuous_invFun := continuous_toCorner q

/-- The homeomorphism preserves the ordered affine face maps, including signs. -/
theorem toBarycentric_face {q : ℕ} (j : Fin (q+2)) (x : CornerSimplex q) :
    toBarycentric (q+1) (SmoothManifolds.SmoothSingularData.face j x) =
      SingularChains.faceInclusion j (toBarycentric q x) := by
  apply Convexity.StdSimplex.ext
  ext i
  change SmoothManifolds.CornerData.simplexBarycentric
      (SmoothManifolds.SmoothSingularData.face j x).val i =
    ((toBarycentric q x).weights.mapDomain j.succAbove) i
  rw [SmoothManifolds.SmoothSingular.face_barycentric]
  refine Fin.succAboveCases j ?_ (fun k => ?_) i
  · rw [Fin.insertNth_apply_same]
    symm
    apply Finsupp.mapDomain_of_notMem_image_support
    intro h
    obtain ⟨k, _, hk⟩ := h
    exact Fin.succAbove_ne j k hk
  · rw [Fin.insertNth_apply_succAbove,
      Finsupp.mapDomain_apply_of_injective j.succAbove_right_injective]
    rfl

open SingularChains
variable {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]

/-- Smoothness means local smooth ambient extensions at every corner, in all
charts of the actual P104 maximal atlas. -/
def IsSmoothSimplex (S : AtlasData.SmoothManifold n a M) (q : ℕ)
    (σ : Simplex (TopCat.of M) q) : Prop :=
  SmoothManifolds.SmoothSingularData.SimplexSmooth S
    (simplexEquiv (TopCat.of M) q σ ∘ toBarycentric q)

theorem isSmoothSimplex_face (S : AtlasData.SmoothManifold n a M) {q : ℕ}
    {σ : Simplex (TopCat.of M) (q+1)} (hσ : IsSmoothSimplex S (q+1) σ)
    (j : Fin (q+2)) : IsSmoothSimplex S q (face j σ) := by
  have h := SmoothManifolds.SmoothSingular.smooth_face hσ j
  have heq : (simplexEquiv (TopCat.of M) q (face j σ) ∘ toBarycentric q) =
      ((simplexEquiv (TopCat.of M) (q+1) σ ∘ toBarycentric (q+1)) ∘
        SmoothManifolds.SmoothSingularData.face j) := by
    funext x
    change simplexEquiv (TopCat.of M) (q+1) σ
      (faceInclusion j (toBarycentric q x)) =
      simplexEquiv (TopCat.of M) (q+1) σ
        (toBarycentric (q+1) (SmoothManifolds.SmoothSingularData.face j x))
    rw [toBarycentric_face]
  unfold IsSmoothSimplex
  rw [heq]
  exact h

/-- Literal finite chains supported on the smooth subset of the shared basis. -/
def smoothModule (S : AtlasData.SmoothManifold n a M) (q : ℕ) :
    Submodule ℝ (Chains ℝ (TopCat.of M) q) :=
  Finsupp.supported ℝ ℝ {σ | IsSmoothSimplex S q σ}

theorem boundary_mem_smoothModule (S : AtlasData.SmoothManifold n a M) (q : ℕ)
    (z : Chains ℝ (TopCat.of M) (q+1)) (hz : z ∈ smoothModule S (q+1)) :
    boundary ℝ ℝ (TopCat.of M) q z ∈ smoothModule S q := by
  classical
  change ((AlgebraicTopology.AlternatingFaceMapComplex.obj
    (simplicialChains ℝ ℝ (TopCat.of M))).d (q+1) q).hom z ∈ _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ j : Fin (q+2), (-1 : ℤ)^j.val •
    Finsupp.mapDomain ((TopCat.toSSet.obj (TopCat.of M)).δ j) z) ∈ smoothModule S q
  apply Submodule.sum_mem
  intro j _
  apply (smoothModule S q).toAddSubgroup.zsmul_mem
  intro τ hτ
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hτ)
  exact isSmoothSimplex_face S (hz hσ) j

/-- The smooth subcomplex, with ordinary zero outgoing boundary in degree zero. -/
def smoothComplex (S : AtlasData.SmoothManifold n a M) : ChainComplex (ModuleCat.{u} ℝ) ℕ :=
  ChainComplex.of (fun q => ModuleCat.of ℝ (smoothModule S q))
    (fun q => ModuleCat.ofHom (((boundary ℝ ℝ (TopCat.of M) q).comp
      (smoothModule S (q+1)).subtype).codRestrict (smoothModule S q)
        (fun z => boundary_mem_smoothModule S q z.val z.property)))
    (by
      intro q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun f => f z.val)
        ((complex ℝ ℝ (TopCat.of M)).d_comp_d (q+2) (q+1) q))

def inclusion (S : AtlasData.SmoothManifold n a M) :
    smoothComplex S ⟶ complex ℝ ℝ (TopCat.of M) :=
  ChainComplex.ofHom (fun q => ModuleCat.ofHom (smoothModule S q).subtype)
    (by intro q; simp only [smoothComplex, ChainComplex.of_d]; rfl)

/-- Extension by zero to negative degrees, exactly as for ordinary chains. -/
def smoothOrdinaryComplex (S : AtlasData.SmoothManifold n a M) :=
  (smoothComplex S).extend (degreeEmbedding 0)

def ordinaryInclusion (S : AtlasData.SmoothManifold n a M) :
    smoothOrdinaryComplex S ⟶ ordinaryComplex ℝ ℝ (TopCat.of M) :=
  HomologicalComplex.extendMap (inclusion S) (degreeEmbedding 0)

def smoothCochains (S : AtlasData.SmoothManifold n a M) :=
  (CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).obj
    (op (smoothOrdinaryComplex S))

/-- Restriction of the full algebraic dual, with the shared ordinary cochains
as its literal domain. -/
def restriction (S : AtlasData.SmoothManifold n a M) :
    CohomologyPairs.ordinaryCochains ℝ ℝ (TopCat.of M) ⟶ smoothCochains S :=
  (CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).map
    (ordinaryInclusion S).op

/-- A smooth map, as a continuous map on the same underlying spaces. -/
def underlyingMap (S : AtlasData.SmoothManifold n a M)
    (T : AtlasData.SmoothManifold m b N) (f : M → N)
    (hf : SmoothManifolds.MapData.IsSmoothMap S T f) : TopCat.of M ⟶ TopCat.of N :=
  TopCat.ofHom ⟨f, continuous_iff_continuousAt.mpr (fun x => (hf x).1)⟩

theorem isSmoothSimplex_map (S : AtlasData.SmoothManifold n a M)
    (T : AtlasData.SmoothManifold m b N) (f : M → N)
    (hf : SmoothManifolds.MapData.IsSmoothMap S T f) (q : ℕ)
    {σ : Simplex (TopCat.of M) q} (hσ : IsSmoothSimplex S q σ) :
    IsSmoothSimplex T q
      ((TopCat.toSSet.map (underlyingMap S T f hf)).app (op ⦋q⦌) σ) := by
  exact SmoothManifolds.SmoothSingular.smooth_postcompose hf hσ

theorem chainMap_mem_smoothModule (S : AtlasData.SmoothManifold n a M)
    (T : AtlasData.SmoothManifold m b N) (f : M → N)
    (hf : SmoothManifolds.MapData.IsSmoothMap S T f) (q : ℕ)
    (z : smoothModule S q) :
    (chainMap ℝ ℝ (underlyingMap S T f hf)).f q z.val ∈ smoothModule T q := by
  classical
  intro τ hτ
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hτ)
  exact isSmoothSimplex_map S T f hf q (z.property hσ)

/-- Smooth pushforward is the restriction of the ordinary singular chain map. -/
def smoothChainMap (S : AtlasData.SmoothManifold n a M)
    (T : AtlasData.SmoothManifold m b N) (f : M → N)
    (hf : SmoothManifolds.MapData.IsSmoothMap S T f) : smoothComplex S ⟶ smoothComplex T :=
  ChainComplex.ofHom
    (fun q => ModuleCat.ofHom ((((chainMap ℝ ℝ (underlyingMap S T f hf)).f q).hom.comp
      (smoothModule S q).subtype).codRestrict (smoothModule T q)
        (chainMap_mem_smoothModule S T f hf q)))
    (by
      intro q
      simp only [smoothComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun g => g z.val)
        ((chainMap ℝ ℝ (underlyingMap S T f hf)).comm (q+1) q))

def smoothOrdinaryMap (S : AtlasData.SmoothManifold n a M)
    (T : AtlasData.SmoothManifold m b N) (f : M → N)
    (hf : SmoothManifolds.MapData.IsSmoothMap S T f) :
    smoothOrdinaryComplex S ⟶ smoothOrdinaryComplex T :=
  HomologicalComplex.extendMap (smoothChainMap S T f hf) (degreeEmbedding 0)

def smoothCochainMap (S : AtlasData.SmoothManifold n a M)
    (T : AtlasData.SmoothManifold m b N) (f : M → N)
    (hf : SmoothManifolds.MapData.IsSmoothMap S T f) : smoothCochains T ⟶ smoothCochains S :=
  (CohomologyPairs.dualComplexFunctor ℝ ℝ (ComplexShape.down ℤ)).map
    (smoothOrdinaryMap S T f hf).op

/-- The full original isomorphism assertion, with no conditional premise.
Both manifold models are included, and no compactness, connectedness,
positive dimension or nonemptiness assumption occurs. -/
def comparisonIsomorphisms_type : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (q : ℤ),
    IsIso (homologyMap (ordinaryInclusion S) q) ∧
      IsIso (homologyMap (restriction S) q)

/-- Naturality for all smooth maps; the ordinary arrows are the fixed shared
singular homology and cohomology functors. -/
def comparisonNaturality_type : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : AtlasData.SmoothManifold n a M) (T : AtlasData.SmoothManifold m b N)
    (f : M → N) (hf : SmoothManifolds.MapData.IsSmoothMap S T f) (q : ℤ),
    (homologyMap (smoothOrdinaryMap S T f hf) q ≫ homologyMap (ordinaryInclusion T) q =
      homologyMap (ordinaryInclusion S) q ≫
        (SingularChains.homologyFunctor ℝ ℝ q).map (underlyingMap S T f hf)) ∧
    ((CohomologyPairs.ordinaryCohomologyFunctor ℝ ℝ q).map (underlyingMap S T f hf).op ≫
        homologyMap (restriction S) q =
      homologyMap (restriction T) q ≫ homologyMap (smoothCochainMap S T f hf) q)

/-- Lemma `lem:p202-smooth-singular`: the original comparison, without any extra premise. -/
def smoothSingularComparison_type : Prop :=
  comparisonIsomorphisms_type.{u} ∧ comparisonNaturality_type.{u}

end P202Specs.SmoothSingularComparison
