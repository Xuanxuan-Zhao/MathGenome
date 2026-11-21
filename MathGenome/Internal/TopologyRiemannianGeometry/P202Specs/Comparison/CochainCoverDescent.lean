import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Comparison.SmoothSingularComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SmallChainHomology
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.MayerVietoris
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Lift
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! Independent interface for the open-cover argument in
`paper.tex:2748–2813`. In the augmented row, tuple length `k` represents
horizontal degree `k-1`; in particular length zero is the augmentation.
Tuples are ordered, with repetitions allowed (the unnormalized Čech model).
No finiteness hypothesis on any of the index types is imposed.

The full smooth-form and smooth-cochain rows use actual restrictions and
intrinsic vertical differentials. Signed totals, their augmentations and
columnwise comparisons use unrestricted real vector spaces and finite
diagonals, with all cohomology maps induced on actual cycle quotients. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace P202Specs.CochainCoverDescent
universe u v w

/-- The augmented full-simplex cochains with values in the reals. -/
abbrev FullSimplexRow (I : Type v) (k : ℕ) := (Fin k → I) → ℝ

/-- Recursive alternating restriction. The first face has sign +1, and all
remaining faces have the opposite signs of the shorter alternating sum. -/
def fullSimplexD (I : Type v) : (k : ℕ) →
    FullSimplexRow I k →ₗ[ℝ] FullSimplexRow I (k+1)
  | 0 => {
      toFun := fun f _ => f Fin.elim0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  | k+1 => {
      toFun := fun f t => f (Fin.tail t) -
        fullSimplexD I k (fun s => f (Fin.cons (t 0) s)) (Fin.tail t)
      map_add' := by
        intro f g
        funext t
        change (f (Fin.tail t) + g (Fin.tail t)) -
          fullSimplexD I k ((fun s => f (Fin.cons (t 0) s)) +
            (fun s => g (Fin.cons (t 0) s))) (Fin.tail t) = _
        rw [map_add]
        simp only [Pi.add_apply]
        change _ = (f (Fin.tail t) - _) + (g (Fin.tail t) - _)
        abel
      map_smul' := by
        intro r f
        funext t
        change r * f (Fin.tail t) -
          fullSimplexD I k (r • (fun s => f (Fin.cons (t 0) s))) (Fin.tail t) = _
        rw [map_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        change _ = r * (f (Fin.tail t) - _)
        ring }

/-- The insertion operator, including the map to augmentation degree -1. -/
def fullSimplexH {I : Type v} (i : I) (k : ℕ) :
    FullSimplexRow I (k+1) →ₗ[ℝ] FullSimplexRow I k where
  toFun f t := f (Fin.cons i t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Products of simplex rows, as opposed to finitely supported families. -/
abbrev ProductRow {B : Type u} (I : B → Type v) (k : ℕ) :=
  (b : B) → FullSimplexRow (I b) k

def productD {B : Type u} (I : B → Type v) (k : ℕ) :
    ProductRow I k →ₗ[ℝ] ProductRow I (k+1) where
  toFun f b := fullSimplexD (I b) k (f b)
  map_add' f g := by funext b; exact map_add _ _ _
  map_smul' r f := by
    funext b
    exact (fullSimplexD (I b) k).map_smul r (f b)

/-- All simplices in this type are smooth in the actual P104 sense and small
for the given cover in the actual shared ordinary singular basis. -/
def SmallSmoothSimplex {n : ℕ} {a : SmoothManifolds.ModelKind}
    {M : Type u} [TopologicalSpace M]
    (S : SmoothManifolds.AtlasData.SmoothManifold n a M)
    {ι : Type v} (U : SmallChainHomology.OpenCover (TopCat.of M) ι) (q : ℕ) :=
  {σ : SingularChains.Simplex (TopCat.of M) q //
    SmoothSingularComparison.IsSmoothSimplex S q σ ∧
      ∃ i, Set.range (SingularChains.simplexEquiv (TopCat.of M) q σ) ⊆ U.sets i}

/-- Cover members containing the whole geometric image of the simplex. -/
def ContainingIndex {n : ℕ} {a : SmoothManifolds.ModelKind}
    {M : Type u} [TopologicalSpace M]
    {S : SmoothManifolds.AtlasData.SmoothManifold n a M}
    {ι : Type v} {U : SmallChainHomology.OpenCover (TopCat.of M) ι} {q : ℕ}
    (σ : SmallSmoothSimplex S U q) :=
  {i : ι // Set.range (SingularChains.simplexEquiv (TopCat.of M) q σ.val) ⊆ U.sets i}

/-- After evaluation on simplex generators, a cochain row is this dependent
product. The geometric intersection/evaluation equivalence is `cochainRowEquiv` below. -/
abbrev EvaluatedCochainRow {n : ℕ} {a : SmoothManifolds.ModelKind}
    {M : Type u} [TopologicalSpace M]
    (S : SmoothManifolds.AtlasData.SmoothManifold n a M)
    {ι : Type v} (U : SmallChainHomology.OpenCover (TopCat.of M) ι) (q k : ℕ) :=
  ProductRow (fun σ : SmallSmoothSimplex S U q => ContainingIndex σ) k

/-- The actual alternating formula, not an assumed differential identity. -/
def alternatingFormula_type : Prop :=
  ∀ (I : Type v) (k : ℕ) (f : FullSimplexRow I k) (t : Fin (k+1) → I),
    fullSimplexD I k f t =
      ∑ j : Fin (k+1), (-1 : ℝ)^j.val * f (t ∘ j.succAbove)

/-- Exactness of the entire augmented row, including injectivity at its first
term, for an arbitrary dependent product of nonempty full simplices. -/
def productRowsExact_type : Prop :=
  ∀ (B : Type u) (I : B → Type v) (_ : ∀ b, Nonempty (I b)),
    Function.Injective (productD I 0) ∧
    ∀ k (f : ProductRow I (k+1)),
      productD I (k+1) f = 0 ↔ ∃ g, productD I k g = f

/-- Application to all cover-small smooth simplices, with arbitrary cover
indices, all degrees, and the empty manifold included. -/
def evaluatedCochainRowsExact_type : Prop :=
  ∀ {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifolds.AtlasData.SmoothManifold n a M) (ι : Type v)
    (U : SmallChainHomology.OpenCover (TopCat.of M) ι) (q : ℕ),
    let I := fun σ : SmallSmoothSimplex S U q => ContainingIndex σ
    Function.Injective (productD I 0) ∧
    ∀ k (f : EvaluatedCochainRow S U q (k+1)),
      productD I (k+1) f = 0 ↔ ∃ g, productD I k g = f


section GeometricRows
open SmoothManifolds SmoothManifolds.AtlasData
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {ι : Type v}
  (U : SmallChainHomology.OpenCover (TopCat.of M) ι) (q : ℕ)

/-- The actual common submodule of smooth chains and cover-small chains. -/
def smallSmoothModule : Submodule ℝ (SingularChains.Chains ℝ (TopCat.of M) q) :=
  SmoothSingularComparison.smoothModule S q ⊓ SmallChainHomology.smallModule ℝ U q

/-- This equivalence connects the finite free model to the literal shared
singular chain submodule, without replacing the underlying singular theory. -/
def smallSmoothBasisEquiv :
    smallSmoothModule S U q ≃ₗ[ℝ] (SmallSmoothSimplex S U q →₀ ℝ) :=
  (LinearEquiv.ofEq _ _ (show smallSmoothModule S U q =
      Finsupp.supported ℝ ℝ {σ | SmoothSingularComparison.IsSmoothSimplex S q σ ∧
        ∃ i, Set.range (SingularChains.simplexEquiv (TopCat.of M) q σ) ⊆ U.sets i} by
      exact (Finsupp.supported_inter _ _).symm)).trans
    (Finsupp.supportedEquivFinsupp _)

/-- A generator supported in every member in an ordered tuple. At tuple
length zero the basis is precisely the cover-small smooth simplex basis. -/
def IntersectionSimplex (k : ℕ) (t : Fin k → ι) :=
  {σ : SmallSmoothSimplex S U q //
    ∀ j, Set.range (SingularChains.simplexEquiv (TopCat.of M) q σ.val) ⊆ U.sets (t j)}

/-- In positive tuple length the smallness condition is automatic. Thus the
basis is exactly all ambient smooth singular simplices supported in the
intersection; no simplex is discarded by the augmentation convention. -/
def positiveIntersectionEquiv (k : ℕ) (t : Fin (k+1) → ι) :
    {σ : SingularChains.Simplex (TopCat.of M) q //
      SmoothSingularComparison.IsSmoothSimplex S q σ ∧
        ∀ j, Set.range (SingularChains.simplexEquiv (TopCat.of M) q σ) ⊆ U.sets (t j)} ≃
      IntersectionSimplex S U q (k+1) t where
  toFun σ := ⟨⟨σ.val, σ.property.1, t 0, σ.property.2 0⟩, σ.property.2⟩
  invFun σ := ⟨σ.val.val, σ.val.property.1, σ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Literal products of full algebraic duals of finite real chains on the
intersections. No finite-support condition is placed on the cochains. -/
abbrev IntersectionCochainRow (k : ℕ) :=
  (t : Fin k → ι) → (IntersectionSimplex S U q k t →₀ ℝ) →ₗ[ℝ] ℝ

/-- The same row after evaluation on basis generators. -/
abbrev IncidenceRow (k : ℕ) :=
  (t : Fin k → ι) → IntersectionSimplex S U q k t → ℝ

/-- Algebraic-dual evaluation works for arbitrary, possibly infinite bases. -/
def cochainEvaluation (k : ℕ) :
    IntersectionCochainRow S U q k ≃ₗ[ℝ] IncidenceRow S U q k :=
  LinearEquiv.piCongrRight (fun t =>
    (Finsupp.llift ℝ ℝ ℝ (IntersectionSimplex S U q k t)).symm)

/-- Reordering the incidence pairs (tuple, simplex) as (simplex, tuple of
containing indices) is a linear equivalence of actual products. -/
def incidenceEquiv (k : ℕ) :
    IncidenceRow S U q k ≃ₗ[ℝ] EvaluatedCochainRow S U q k where
  toFun f σ t := f (fun j => (t j).val) ⟨σ, fun j => (t j).property⟩
  invFun f t σ := f σ.val (fun j => ⟨t j, σ.property j⟩)
  left_inv f := by
    funext t σ
    rfl
  right_inv f := by
    funext σ t
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The product decomposition of the cochain row. -/
def cochainRowEquiv (k : ℕ) :
    IntersectionCochainRow S U q k ≃ₗ[ℝ] EvaluatedCochainRow S U q k :=
  (cochainEvaluation S U q k).trans (incidenceEquiv S U q k)

/-- At augmentation degree the row is exactly the full algebraic dual
of the cover-small smooth submodule of the shared ordinary real chains. -/
def augmentationEquiv : IntersectionCochainRow S U q 0 ≃ₗ[ℝ]
    (smallSmoothModule S U q →ₗ[ℝ] ℝ) :=
  (cochainRowEquiv S U q 0).trans
    ((LinearEquiv.piCongrRight (fun σ : SmallSmoothSimplex S U q =>
      LinearEquiv.piUnique ℝ (fun _ : Fin 0 → ContainingIndex σ => ℝ))).trans
      ((Finsupp.llift ℝ ℝ ℝ (SmallSmoothSimplex S U q)).trans
        (LinearEquiv.congrLeft ℝ ℝ (smallSmoothBasisEquiv S U q).symm)))

/-- Horizontal restriction, transported through the proved evaluation and
incidence equivalences. Its alternating restriction formula is specified
below on every simplex basis generator. -/
def intersectionD (k : ℕ) :
    IntersectionCochainRow S U q k →ₗ[ℝ] IntersectionCochainRow S U q (k+1) :=
  (cochainRowEquiv S U q (k+1)).symm.toLinearMap ∘ₗ
    productD (fun σ : SmallSmoothSimplex S U q => ContainingIndex σ) k ∘ₗ
      (cochainRowEquiv S U q k).toLinearMap

/-- Deleting an index restricts a simplex to the larger intersection. -/
def deleteIndex {k : ℕ} {t : Fin (k+1) → ι}
    (σ : IntersectionSimplex S U q (k+1) t) (j : Fin (k+1)) :
    IntersectionSimplex S U q k (t ∘ j.succAbove) :=
  ⟨σ.val, fun l => σ.property (j.succAbove l)⟩
/-- The literal submodule of ordinary chains used at a fixed cover tuple.
Smallness is retained also for the empty tuple, giving the augmentation. -/
def intersectionChainModule (k : ℕ) (t : Fin k → ι) :
    Submodule ℝ (SingularChains.Chains ℝ (TopCat.of M) q) :=
  Finsupp.supported ℝ ℝ {σ |
    SmoothSingularComparison.IsSmoothSimplex S q σ ∧
      (∃ i, Set.range (SingularChains.simplexEquiv (TopCat.of M) q σ) ⊆ U.sets i) ∧
      ∀ j, Set.range (SingularChains.simplexEquiv (TopCat.of M) q σ) ⊆ U.sets (t j)}

/-- Restriction to support is just a change from the ordinary singular basis
to the explicitly evaluated intersection simplex basis. -/
def intersectionChainBasisEquiv (k : ℕ) (t : Fin k → ι) :
    intersectionChainModule S U q k t ≃ₗ[ℝ] (IntersectionSimplex S U q k t →₀ ℝ) :=
  (Finsupp.supportedEquivFinsupp _).trans (Finsupp.domLCongr {
    toFun := fun σ => ⟨⟨σ.val, σ.property.1, σ.property.2.1⟩, σ.property.2.2⟩
    invFun := fun σ => ⟨σ.val.val, σ.val.property.1, σ.val.property.2, σ.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl })

end GeometricRows

section IntersectionDifferential
open SingularChains CategoryTheory HomologicalComplex
open scoped Simplicial
open SmoothManifolds SmoothManifolds.AtlasData
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : AtlasData.SmoothManifold n a M) {ι : Type v}
  (U : SmallChainHomology.OpenCover (TopCat.of M) ι)

theorem face_image_subset {q : ℕ} (σ : Simplex (TopCat.of M) (q+1))
    (j : Fin (q+2)) :
    Set.range (simplexEquiv (TopCat.of M) q (face j σ)) ⊆
      Set.range (simplexEquiv (TopCat.of M) (q+1) σ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨faceInclusion j x, rfl⟩

/-- Face closure follows from the actual smoothness and geometric support
conditions, with no extra smooth comparison certificate. -/
def intersectionFace {q k : ℕ} {t : Fin k → ι}
    (σ : IntersectionSimplex S U (q+1) k t) (j : Fin (q+2)) :
    IntersectionSimplex S U q k t :=
  ⟨⟨face j σ.val.val,
    SmoothSingularComparison.isSmoothSimplex_face S σ.val.property.1 j,
    by
      obtain ⟨i, hi⟩ := σ.val.property.2
      exact ⟨i, (face_image_subset _ j).trans hi⟩⟩,
    fun l => (face_image_subset _ j).trans (σ.property l)⟩

theorem boundary_mem_intersection (q k : ℕ) (t : Fin k → ι)
    (z : Chains ℝ (TopCat.of M) (q+1))
    (hz : z ∈ intersectionChainModule S U (q+1) k t) :
    boundary ℝ ℝ (TopCat.of M) q z ∈ intersectionChainModule S U q k t := by
  classical
  change ((AlgebraicTopology.AlternatingFaceMapComplex.obj
    (simplicialChains ℝ ℝ (TopCat.of M))).d (q+1) q).hom z ∈ _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ j : Fin (q+2), (-1 : ℤ)^j.val •
    Finsupp.mapDomain ((TopCat.toSSet.obj (TopCat.of M)).δ j) z) ∈ _
  apply Submodule.sum_mem
  intro j _
  apply (intersectionChainModule S U q k t).toAddSubgroup.zsmul_mem
  intro τ hτ
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hτ)
  have hs := hz hσ
  let hface := intersectionFace S U ⟨⟨σ, hs.1, hs.2.1⟩, hs.2.2⟩ j
  exact ⟨hface.val.property.1, hface.val.property.2, hface.property⟩

/-- The differential is the restriction of the shared singular boundary. -/
def intersectionBoundary (q k : ℕ) (t : Fin k → ι) :
    intersectionChainModule S U (q+1) k t →ₗ[ℝ]
      intersectionChainModule S U q k t :=
  (((boundary ℝ ℝ (TopCat.of M) q).comp
    (intersectionChainModule S U (q+1) k t).subtype).codRestrict
      (intersectionChainModule S U q k t)
        (fun z => boundary_mem_intersection S U q k t z.val z.property))

/-- Every tuple has the actual singular chain subcomplex on its support,
with the ordinary nonnegative convention in degree zero. -/
def intersectionComplex (k : ℕ) (t : Fin k → ι) :
    ChainComplex (ModuleCat.{u} ℝ) ℕ :=
  ChainComplex.of (fun q => ModuleCat.of ℝ (intersectionChainModule S U q k t))
    (fun q => ModuleCat.ofHom (intersectionBoundary S U q k t))
    (by
      intro q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun f => f z.val)
        ((complex ℝ ℝ (TopCat.of M)).d_comp_d (q+2) (q+1) q))

/-- The cochain differential on the free intersection generators, obtained
by transporting the actual shared chain boundary and taking its full dual. -/
def intersectionV (q k : ℕ) :
    IntersectionCochainRow S U q k →ₗ[ℝ] IntersectionCochainRow S U (q+1) k where
  toFun f t := (f t).comp
    ((intersectionChainBasisEquiv S U q k t).toLinearMap ∘ₗ
      intersectionBoundary S U q k t ∘ₗ
        (intersectionChainBasisEquiv S U (q+1) k t).symm.toLinearMap)
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

end IntersectionDifferential

/-- The differential really is the signed sum of the actual restrictions,
with the same simplex evaluated in each larger intersection. -/
def intersectionAlternatingFormula_type : Prop :=
  ∀ {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifolds.AtlasData.SmoothManifold n a M) (ι : Type v)
    (U : SmallChainHomology.OpenCover (TopCat.of M) ι) (q k : ℕ)
    (f : IntersectionCochainRow S U q k) (t : Fin (k+1) → ι)
    (σ : IntersectionSimplex S U q (k+1) t),
    intersectionD S U q k f t (Finsupp.single σ 1) =
      ∑ j : Fin (k+1), (-1 : ℝ)^j.val *
        f (t ∘ j.succAbove) (Finsupp.single (deleteIndex S U q σ j) 1)

/-- Horizontal exactness in the geometric product-of-cochains model,
including the cover-small augmentation at horizontal degree -1. -/
def intersectionRowsExact_type : Prop :=
  ∀ {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifolds.AtlasData.SmoothManifold n a M) (ι : Type v)
    (U : SmallChainHomology.OpenCover (TopCat.of M) ι) (q : ℕ),
    Function.Injective (intersectionD S U q 0) ∧
    (∀ k (f : IntersectionCochainRow S U q k),
      intersectionD S U q (k+1) (intersectionD S U q k f) = 0) ∧
    ∀ k (f : IntersectionCochainRow S U q (k+1)),
      intersectionD S U q (k+1) f = 0 ↔ ∃ g, intersectionD S U q k g = f

/-- Arbitrary products of real vector-space exact sequences preserve
exactness. There is no cardinality, dimension, or finite generation bound. -/
def productsPreserveExactness_type : Prop :=
  ∀ (B : Type u) (V W Z : B → Type v)
    [∀ b, AddCommGroup (V b)] [∀ b, AddCommGroup (W b)] [∀ b, AddCommGroup (Z b)]
    [∀ b, Module ℝ (V b)] [∀ b, Module ℝ (W b)] [∀ b, Module ℝ (Z b)]
    (f : ∀ b, V b →ₗ[ℝ] W b) (g : ∀ b, W b →ₗ[ℝ] Z b),
    (∀ b w, g b w = 0 ↔ ∃ v, f b v = w) →
    ∀ w : (b : B) → W b,
      (fun b => g b (w b)) = 0 ↔ ∃ v : (b : B) → V b, (fun b => f b (v b)) = w

/-- The smooth singular cover rows form a commuting cochain bicomplex,
with the standard signed face formula for the vertical coboundary. -/
def cochainBicomplex_type : Prop :=
  ∀ {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifolds.AtlasData.SmoothManifold n a M) (ι : Type v)
    (U : SmallChainHomology.OpenCover (TopCat.of M) ι),
    (∀ q k (f : IntersectionCochainRow S U q k),
      intersectionV S U (q+1) k (intersectionV S U q k f) = 0) ∧
    (∀ q k (f : IntersectionCochainRow S U q k),
      intersectionV S U q (k+1) (intersectionD S U q k f) =
        intersectionD S U (q+1) k (intersectionV S U q k f)) ∧
    (∀ q k (f : IntersectionCochainRow S U q k) (t : Fin k → ι)
      (σ : IntersectionSimplex S U (q+1) k t),
      intersectionV S U q k f t (Finsupp.single σ 1) =
        ∑ j : Fin (q+2), (-1 : ℝ)^j.val *
          f t (Finsupp.single (intersectionFace S U σ j) 1))


set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
section FormRows
open SmoothManifolds SmoothManifolds.AtlasData SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
  SmoothManifolds.ExteriorData SmoothManifolds.MayerVietorisData
  SmoothManifolds.MayerVietorisData.OpenForms
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : AtlasData.SmoothManifold n a M} {C : CotangentBundle S}

/-- Full smooth exterior sections on an open set, with the ambient fibers.
In particular this includes open sets meeting the smooth boundary. -/
def formsOn (B : FormBundle C q) (V : TopologicalSpace.Opens M) :
    Submodule ℝ (RestrictedField S V q) where
  carrier := {ω | IsRestrictedForm B V ω}
  zero_mem' := restricted_zero B V
  add_mem' := fun hω hη => restricted_add B V _ _ hω hη
  smul_mem' := fun r _ hω => restricted_smul B V r _ hω

/-- The empty intersection is the whole manifold, giving the augmentation. -/
def tupleOpen {ι : Type v} (U : ι → TopologicalSpace.Opens M)
    {k : ℕ} (t : Fin k → ι) : TopologicalSpace.Opens M :=
  ⟨{x | ∀ j, x ∈ U (t j)}, by
    convert isOpen_iInter_of_finite (fun j => (U (t j)).isOpen) using 1
    ext x
    simp⟩

/-- A product of actual smooth forms, with no support or cardinality bound. -/
abbrev FormRow (B : FormBundle C q) {ι : Type v}
    (U : ι → TopologicalSpace.Opens M) (k : ℕ) :=
  (t : Fin k → ι) → formsOn B (tupleOpen U t)

/-- The usual restriction on full spaces of smooth forms. -/
def formRestriction (B : FormBundle C q) (V W : TopologicalSpace.Opens M)
    (hWV : W ≤ V) : formsOn B V →ₗ[ℝ] formsOn B W where
  toFun ω := ⟨fun x => ω.val ⟨x.val, hWV x.property⟩,
    restricted_restrict B V W hWV ω.val ω.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Alternating restriction, including the augmentation from global forms. -/
def formD (B : FormBundle C q) {ι : Type v}
    (U : ι → TopologicalSpace.Opens M) (k : ℕ) :
    FormRow B U k →ₗ[ℝ] FormRow B U (k+1) where
  toFun f t := ∑ j : Fin (k+1), (-1 : ℝ)^j.val •
    formRestriction B (tupleOpen U (t ∘ j.succAbove)) (tupleOpen U t)
      (fun _ hx l => hx (j.succAbove l)) (f (t ∘ j.succAbove))
  map_add' f g := by
    funext t
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext t
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _

/-- The horizontal forms row is exact for every arbitrary open cover and
all exterior degrees. The length-zero term is the full space of global forms. -/
def formsRowsExact_type : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (C : CotangentBundle S) (q : ℕ)
    (B : FormBundle C q) (ι : Type v) (U : ι → TopologicalSpace.Opens M)
    (_ : ∀ x, ∃ i, x ∈ U i),
    Function.Injective (formD B U 0) ∧
    (∀ k (f : FormRow B U k), formD B U (k+1) (formD B U k f) = 0) ∧
    ∀ k (f : FormRow B U (k+1)),
      formD B U (k+1) f = 0 ↔ ∃ g, formD B U k g = f

/-- Fix the actual intrinsic de Rham calculus constructed by P104; no
existence or square-zero certificate is added to the hypotheses. -/
def formCalculus (C : CotangentBundle S) (B : ∀ q, FormBundle C q) :
    DeRhamData.Calculus C B :=
  Classical.choice (SmoothManifolds.DeRhamResults.complex_exists C B)

/-- The actual full restricted calculus on each open set. -/
def formOpenCalculus (C : CotangentBundle S) (B : ∀ q, FormBundle C q)
    (V : TopologicalSpace.Opens M) : OpenCalculus C B V :=
  Classical.choice (openCalculus_exists (formCalculus C B) V)

/-- Its realization is linearly equivalent to all genuine smooth sections. -/
def openFormEquiv {B : ∀ q, FormBundle C q} {V : TopologicalSpace.Opens M}
    (D : OpenCalculus C B V) (q : ℕ) :
    D.complex.Obj q ≃ₗ[ℝ] formsOn (B q) V where
  toFun ω := ⟨D.field q ω, field_smooth D q ω⟩
  invFun ω := realize D q ω.val ω.property
  left_inv ω := D.injective q (field_realize D q _ _)
  right_inv ω := Subtype.ext (field_realize D q _ _)
  map_add' ω η := Subtype.ext ((D.field q).map_add ω η)
  map_smul' r ω := Subtype.ext ((D.field q).map_smul r ω)

/-- Exterior differentiation on all smooth restricted forms, transported
from the constructed intrinsic calculus, with its coordinate formula. -/
def exteriorOn (C : CotangentBundle S) (B : ∀ q, FormBundle C q)
    (V : TopologicalSpace.Opens M) (q : ℕ) :
    formsOn (B q) V →ₗ[ℝ] formsOn (B (q+1)) V :=
  let D := formOpenCalculus C B V
  (openFormEquiv D (q+1)).toLinearMap ∘ₗ D.complex.d q ∘ₗ
    (openFormEquiv D q).symm.toLinearMap

/-- The vertical operator is the actual exterior derivative in every tuple. -/
def formV (C : CotangentBundle S) (B : ∀ q, FormBundle C q)
    {ι : Type v} (U : ι → TopologicalSpace.Opens M) (q k : ℕ) :
    FormRow (B q) U k →ₗ[ℝ] FormRow (B (q+1)) U k where
  toFun f t := exteriorOn C B (tupleOpen U t) q (f t)
  map_add' f g := by funext t; exact (exteriorOn C B (tupleOpen U t) q).map_add (f t) (g t)
  map_smul' r f := by funext t; exact (exteriorOn C B (tupleOpen U t) q).map_smul r (f t)

/-- The forms form a commuting cochain bicomplex with the genuine local
coordinate exterior derivative, including the global augmentation row. -/
def formsBicomplex_type : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (C : CotangentBundle S)
    (B : ∀ q, FormBundle C q) (ι : Type v) (U : ι → TopologicalSpace.Opens M),
    (∀ q k (f : FormRow (B q) U k),
      formV C B U (q+1) k (formV C B U q k f) = 0) ∧
    (∀ q k (f : FormRow (B q) U k),
      formV C B U q (k+1) (formD (B q) U k f) =
        formD (B (q+1)) U k (formV C B U q k f)) ∧
    (∀ q k (f : FormRow (B q) U k) (t : Fin k → ι),
      HasRestrictedDerivative C (tupleOpen U t) (f t).val
        (formV C B U q k f t).val)

/-- The horizontal augmentation consists of the original global smooth
forms, with their original exterior differential. -/
def formsAugmentation_type : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (C : CotangentBundle S)
    (B : ∀ q, FormBundle C q) (K : DeRhamData.Calculus C B)
    (ι : Type v) (U : ι → TopologicalSpace.Opens M),
    ∃ e : ∀ q, FormRow (B q) U 0 ≃ₗ[ℝ] K.forms q,
      (∀ q ω x, (e q ω).val x = (ω Fin.elim0).val ⟨x, fun j => Fin.elim0 j⟩) ∧
      ∀ q ω, e (q+1) (formV C B U q 0 ω) = K.d q (e q ω)

end FormRows

end P202Specs.CochainCoverDescent

noncomputable section
namespace P202.CochainCoverDescent.TotalAlgebra
universe v
variable {E : Type v} [AddCommGroup E] [Module ℝ E]

/-- A commuting bicomplex in a common ambient real vector space. The subspaces
are zero in negative horizontal degrees. No dimension bound is imposed. -/
structure Data (E : Type v) [AddCommGroup E] [Module ℝ E] where
  space : ℤ → ℕ → Submodule ℝ E
  horizontal : E →ₗ[ℝ] E
  vertical : E →ₗ[ℝ] E
  horizontal_mem : ∀ p q x, x ∈ space p q → horizontal x ∈ space (p+1) q
  vertical_mem : ∀ p q x, x ∈ space p q → vertical x ∈ space p (q+1)
  horizontal_square : ∀ x, horizontal (horizontal x) = 0
  vertical_square : ∀ x, vertical (vertical x) = 0
  commute : ∀ x, horizontal (vertical x) = vertical (horizontal x)
  below : ∀ p q, p < 0 → space p q = ⊥

namespace Data
variable (B : Data E)

/-- The homogeneous total degree subspace. Every element has finitely many
nonzero components, since the horizontal degree is bounded below by zero. -/
def total (n : ℤ) : Submodule ℝ (ℕ → E) where
  carrier := {x | ∀ q : ℕ, x q ∈ B.space (n - q) q}
  zero_mem' := fun q => (B.space _ _).zero_mem
  add_mem' := fun hx hy q => (B.space _ _).add_mem (hx q) (hy q)
  smul_mem' := fun r x hx q => (B.space _ _).smul_mem r (hx q)

/-- The differential is horizontal plus `(-1)^p` vertical on the component
of horizontal degree `p`. Integer degrees also cover the shifted cone. -/
def differential (n : ℤ) : (ℕ → E) →ₗ[ℝ] (ℕ → E) where
  toFun x q := match q with
    | 0 => B.horizontal (x 0)
    | q+1 => B.horizontal (x (q+1)) + (-1 : ℝ)^(n-q) • B.vertical (x q)
  map_add' x y := by
    funext q
    cases q <;> simp [map_add, smul_add, add_add_add_comm]
  map_smul' r x := by
    funext q
    cases q with
    | zero => exact B.horizontal.map_smul r (x 0)
    | succ q =>
      simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add]
      rw [smul_comm r ((-1 : ℝ)^(n-q))]

@[simp] theorem differential_zero (n : ℤ) (x : ℕ → E) :
    B.differential n x 0 = B.horizontal (x 0) := rfl
@[simp] theorem differential_succ (n : ℤ) (x : ℕ → E) (q : ℕ) :
    B.differential n x (q+1) =
      B.horizontal (x (q+1)) + (-1 : ℝ)^(n-q) • B.vertical (x q) := rfl

private theorem sign_succ (n : ℤ) : (-1 : ℝ)^(n+1) = -((-1 : ℝ)^n) := by
  rw [zpow_add₀ (by norm_num), zpow_one]
  ring

 theorem differential_square (n : ℤ) (x : ℕ → E) :
    B.differential (n+1) (B.differential n x) = 0 := by
  funext q
  cases q with
  | zero => simp [B.horizontal_square]
  | succ q =>
    cases q with
    | zero =>
      simp only [differential_succ, differential_zero, map_add, map_smul,
        B.horizontal_square, B.commute, zero_add]
      rw [show n+1-(0:ℕ) = (n-(0:ℕ))+1 by omega, sign_succ]
      simp
    | succ q =>
      simp only [differential_succ, map_add, map_smul,
        B.horizontal_square, B.vertical_square, B.commute, zero_add, smul_zero, add_zero]
      rw [show n+1-((q+1:ℕ):ℤ) = (n-((q+1:ℕ):ℤ))+1 by omega, sign_succ]
      simp

 theorem differential_mem (n : ℤ) {x : ℕ → E} (hx : x ∈ B.total n) :
    B.differential n x ∈ B.total (n+1) := by
  intro q
  cases q with
  | zero =>
    have h := B.horizontal_mem n 0 (x 0) (by simpa using hx 0)
    simpa using h
  | succ q =>
    apply (B.space ((n+1)-(q+1)) (q+1)).add_mem
    · convert B.horizontal_mem (n-(q+1)) (q+1) _ (hx (q+1)) using 1 <;> congr 2 <;> omega
    · apply (B.space ((n+1)-(q+1)) (q+1)).smul_mem
      have he : (n+1)-((q:ℤ)+1) = n-q := by omega
      rw [he]
      exact B.vertical_mem (n-q) q _ (hx q)

 theorem total_component_zero (n : ℤ) {x : ℕ → E} (hx : x ∈ B.total n)
    (q : ℕ) (hq : n < q) : x q = 0 := by
  have h := hx q
  rw [B.below (n-q) q (by omega)] at h
  exact h

 theorem head_closed (n : ℤ) {x : ℕ → E} (hx : B.differential n x = 0)
    (k : ℕ) (hk : ∀ q, q < k → x q = 0) : B.horizontal (x k) = 0 := by
  have h := congrFun hx k
  cases k with
  | zero => exact h
  | succ k => simpa [hk k (by omega)] using h

 theorem differential_single_self (n : ℤ) (k : ℕ) (z : E) :
    B.differential n (Pi.single k z) k = B.horizontal z := by
  cases k with
  | zero => simp
  | succ k => simp [show k ≠ k+1 by omega]

 theorem differential_single_before (n : ℤ) (k : ℕ) (z : E) (q : ℕ) (hq : q < k) :
    B.differential n (Pi.single k z) q = 0 := by
  cases q with
  | zero => simp [show k ≠ 0 by omega]
  | succ q => simp [show k ≠ q+1 by omega, show k ≠ q by omega]

 theorem single_mem (n : ℤ) (k : ℕ) (z : E) (hz : z ∈ B.space (n-k) k) :
    Pi.single k z ∈ B.total n := by
  intro q
  by_cases h : k=q
  · subst q; simpa
  · simpa [h] using (B.space (n-q) q).zero_mem

end Data
end P202.CochainCoverDescent.TotalAlgebra

noncomputable section
namespace P202.CochainCoverDescent.ConeAlgebra
universe v w
variable {E : Type v} [AddCommGroup E] [Module ℝ E]
  {F : Type w} [AddCommGroup F] [Module ℝ F]

/-- An integer-indexed complex, presented by graded subspaces of one ambient
space. The differential outside its prescribed degree is irrelevant. -/
structure Complex (E : Type v) [AddCommGroup E] [Module ℝ E] where
  space : ℤ → Submodule ℝ E
  differential : ℤ → E →ₗ[ℝ] E
  differential_mem : ∀ n x, x ∈ space n → differential n x ∈ space (n+1)
  square : ∀ n x, differential (n+1) (differential n x) = 0

namespace Complex
variable (C : Complex E) (D : Complex F)

def cycles (n : ℤ) : Submodule ℝ E :=
  C.space n ⊓ LinearMap.ker (C.differential n)

def boundaryMap (n : ℤ) : C.space (n-1) →ₗ[ℝ] C.cycles n where
  toFun x := ⟨C.differential (n-1) x.val, by
    constructor
    · change C.differential (n-1) x.val ∈ C.space n
      have ht := C.differential_mem (n-1) x.val x.property
      have hn : n-1+1=n := by omega
      rw [hn] at ht
      exact ht
    · have h := C.square (n-1) x.val
      have he : n-1+1=n := by omega
      rw [he] at h
      exact h⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext (map_smul _ _ _)

def boundaries (n : ℤ) : Submodule ℝ (C.cycles n) := LinearMap.range (C.boundaryMap n)
abbrev Cohomology (n : ℤ) := C.cycles n ⧸ C.boundaries n

def Acyclic : Prop := ∀ n x, x ∈ C.space n → C.differential n x = 0 →
  ∃ y, y ∈ C.space (n-1) ∧ C.differential (n-1) y = x

theorem boundary_mem_iff (n : ℤ) (x : C.cycles n) :
    x ∈ C.boundaries n ↔ ∃ y, y ∈ C.space (n-1) ∧ C.differential (n-1) y = x.val := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨⟨y,hy⟩, Subtype.ext he⟩

end Complex

/-- A genuine map of the prescribed complexes. -/
structure Map (C : Complex E) (D : Complex F) where
  map : ℤ → E →ₗ[ℝ] F
  map_mem : ∀ n x, x ∈ C.space n → map n x ∈ D.space n
  commute : ∀ n x, D.differential n (map n x) = map (n+1) (C.differential n x)

namespace Map
variable {C : Complex E} {D : Complex F} (f : Map C D)

def cycleMap (n : ℤ) : C.cycles n →ₗ[ℝ] D.cycles n where
  toFun x := ⟨f.map n x.val, ⟨f.map_mem n x.val x.property.1, by
    change D.differential n (f.map n x.val) = 0
    rw [f.commute, show C.differential n x.val = 0 from x.property.2, map_zero]⟩⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext (map_smul _ _ _)

theorem maps_boundaries (n : ℤ) : C.boundaries n ≤ (D.boundaries n).comap (f.cycleMap n) := by
  intro x hx
  obtain ⟨y, hy, he⟩ := (C.boundary_mem_iff n x).mp hx
  apply (D.boundary_mem_iff n (f.cycleMap n x)).mpr
  refine ⟨f.map (n-1) y, f.map_mem (n-1) y hy, ?_⟩
  rw [f.commute]
  have hn : n-1+1=n := by omega
  rw [hn,he]
  rfl

def cohomologyMap (n : ℤ) : C.Cohomology n →ₗ[ℝ] D.Cohomology n :=
  (C.boundaries n).mapQ (D.boundaries n) (f.cycleMap n) (f.maps_boundaries n)

/-- The ordinary cochain mapping cone, with `D^n × C^(n+1)` in degree n. -/
def cone : Complex (F × E) where
  space n := (D.space n).prod (C.space (n+1))
  differential n := {
    toFun x := (D.differential n x.1 + f.map (n+1) x.2, -C.differential (n+1) x.2)
    map_add' x y := by ext <;> simp [map_add] <;> abel
    map_smul' r x := by ext <;> simp [map_smul, smul_add] }
  differential_mem n x hx := by
    constructor
    · exact (D.space _).add_mem (D.differential_mem n x.1 hx.1)
        (f.map_mem (n+1) x.2 hx.2)
    · exact (C.space _).neg_mem (C.differential_mem (n+1) x.2 hx.2)
  square n x := by
    ext <;> simp [map_add, D.square, C.square, f.commute]

@[simp] theorem cone_differential (n : ℤ) (x : F × E) :
    f.cone.differential n x =
      (D.differential n x.1 + f.map (n+1) x.2, -C.differential (n+1) x.2) := rfl

end Map
end P202.CochainCoverDescent.ConeAlgebra

namespace P202.CochainCoverDescent.TotalAlgebra
namespace GridEmbedding
universe u
variable (C : ℕ → ℕ → Type u)
  [∀ p q, AddCommGroup (C p q)] [∀ p q, Module ℝ (C p q)]
abbrev Ambient := (p q : ℕ) → C p q

def embed (p q : ℕ) : C p q →ₗ[ℝ] Ambient C :=
  (LinearMap.single ℝ (fun p => (q : ℕ) → C p q) p).comp
    (LinearMap.single ℝ (C p) q)

@[simp] theorem embed_apply (p q : ℕ) (z : C p q) :
    embed C p q z = Pi.single p (Pi.single q z) := rfl

theorem embed_injective (p q : ℕ) : Function.Injective (embed C p q) := by
  intro x y h
  have he := congrFun (congrFun h p) q
  simpa using he

def horizontal (h : ∀ p q, C p q →ₗ[ℝ] C (p+1) q) :
    Ambient C →ₗ[ℝ] Ambient C where
  toFun x p q := match p with
    | 0 => 0
    | p+1 => h p q (x p q)
  map_add' x y := by
    funext p q
    cases p <;> simp [map_add]
  map_smul' r x := by
    funext p q
    cases p <;> simp [map_smul]

def vertical (v : ∀ p q, C p q →ₗ[ℝ] C p (q+1)) :
    Ambient C →ₗ[ℝ] Ambient C where
  toFun x p q := match q with
    | 0 => 0
    | q+1 => v p q (x p q)
  map_add' x y := by
    funext p q
    cases q <;> simp [map_add]
  map_smul' r x := by
    funext p q
    cases q <;> simp [map_smul]

theorem horizontal_embed (h : ∀ p q, C p q →ₗ[ℝ] C (p+1) q)
    (p q : ℕ) (z : C p q) :
    horizontal C h (embed C p q z) = embed C (p+1) q (h p q z) := by
  funext r s
  cases r with
  | zero => simp [horizontal]
  | succ r =>
    by_cases hr : r=p
    · subst r
      by_cases hs : s=q
      · subst s; simp [horizontal]
      · simp [horizontal, hs]
    · simp [horizontal, hr]

theorem vertical_embed (v : ∀ p q, C p q →ₗ[ℝ] C p (q+1))
    (p q : ℕ) (z : C p q) :
    vertical C v (embed C p q z) = embed C p (q+1) (v p q z) := by
  funext r s
  cases s with
  | zero =>
    by_cases hr : r=p
    · subst r; simp [vertical]
    · simp [vertical, hr]
  | succ s =>
    by_cases hr : r=p
    · subst r
      by_cases hs : s=q
      · subst s; simp [vertical]
      · simp [vertical, hs]
    · simp [vertical, hr]

def space (p : ℤ) (q : ℕ) : Submodule ℝ (Ambient C) :=
  if 0 ≤ p then LinearMap.range (embed C p.toNat q) else ⊥

@[simp] theorem space_neg (p : ℤ) (q : ℕ) (hp : p < 0) :
    space C p q = ⊥ := if_neg (by omega)

@[simp] theorem space_nat (p q : ℕ) :
    space C p q = LinearMap.range (embed C p q) := by
  simp [space]

def data (h : ∀ p q, C p q →ₗ[ℝ] C (p+1) q)
    (v : ∀ p q, C p q →ₗ[ℝ] C p (q+1))
    (hh : ∀ p q z, h (p+1) q (h p q z) = 0)
    (hv : ∀ p q z, v p (q+1) (v p q z) = 0)
    (hcomm : ∀ p q z, h p (q+1) (v p q z) = v (p+1) q (h p q z)) :
    Data (Ambient C) where
  space := space C
  horizontal := horizontal C h
  vertical := vertical C v
  horizontal_mem := by
    intro p q x hx
    by_cases hp : 0 ≤ p
    · rw [space, if_pos hp] at hx
      obtain ⟨z,rfl⟩ := hx
      rw [horizontal_embed]
      have hpn : (p+1).toNat = p.toNat+1 := by omega
      rw [space, if_pos (by omega), hpn]
      exact ⟨h p.toNat q z,rfl⟩
    · rw [space, if_neg hp] at hx
      have hx0 : x=0 := hx
      rw [hx0,map_zero]
      exact Submodule.zero_mem _
  vertical_mem := by
    intro p q x hx
    by_cases hp : 0 ≤ p
    · rw [space, if_pos hp] at hx ⊢
      obtain ⟨z,rfl⟩ := hx
      rw [vertical_embed]
      exact ⟨v p.toNat q z,rfl⟩
    · rw [space, if_neg hp] at hx
      have hx0 : x=0 := hx
      rw [hx0,map_zero]
      exact Submodule.zero_mem _
  horizontal_square := by
    intro x
    funext p q
    cases p with
    | zero => rfl
    | succ p =>
      cases p with
      | zero => simp [horizontal]
      | succ p => exact hh p q (x p q)
  vertical_square := by
    intro x
    funext p q
    cases q with
    | zero => rfl
    | succ q =>
      cases q with
      | zero => simp [vertical]
      | succ q => exact hv p q (x p q)
  commute := by
    intro x
    funext p q
    cases p with
    | zero => cases q <;> simp [horizontal,vertical]
    | succ p =>
      cases q with
      | zero => simp [horizontal,vertical]
      | succ q => exact hcomm p q (x p q)
  below := space_neg C

/-- Row exactness of the original dependent family passes to the canonical
ambient model, including injectivity at its zero-th (augmentation) term. -/
theorem rows_exact
    (h : ∀ p q, C p q →ₗ[ℝ] C (p+1) q)
    (hinj : ∀ q, Function.Injective (h 0 q))
    (hexact : ∀ p q (z : C (p+1) q), h (p+1) q z = 0 →
      ∃ y : C p q, h p q y = z)
    (p : ℤ) (q : ℕ) (z : Ambient C)
    (hz : z ∈ space C p q) (hd : horizontal C h z = 0) :
    ∃ y, y ∈ space C (p-1) q ∧ horizontal C h y = z := by
  by_cases hp : 0 ≤ p
  · lift p to ℕ using hp with p
    rw [space_nat] at hz
    obtain ⟨w,rfl⟩ := hz
    rw [horizontal_embed] at hd
    have hd0 : h p q w = 0 := embed_injective C (p+1) q (by simpa using hd)
    cases p with
    | zero =>
      have hw : w = 0 := (hinj q) (by simpa using hd0)
      subst w
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simp
    | succ p =>
      obtain ⟨y,hy⟩ := hexact p q w hd0
      refine ⟨embed C p q y, ?_, ?_⟩
      · have he : ((p+1 : ℕ) : ℤ)-1 = (p:ℤ) := by omega
        rw [he,space_nat]
        exact ⟨y,rfl⟩
      · rw [horizontal_embed,hy]
  · rw [space, if_neg hp] at hz
    have hz0 : z=0 := hz
    refine ⟨0,Submodule.zero_mem _,?_⟩
    simpa using hz0.symm

end GridEmbedding
end P202.CochainCoverDescent.TotalAlgebra

noncomputable section
namespace P202.CochainCoverDescent.TotalAlgebra.Data
open P202.CochainCoverDescent.ConeAlgebra
universe v
variable {E : Type v} [AddCommGroup E] [Module ℝ E] (B : Data E)

/-- The total of the augmented grid, indexed so horizontal tuple length k
represents original horizontal degree k-1. -/
def augmentedComplex : Complex (ℕ → E) where
  space n := B.total (n+1)
  differential n := B.differential (n+1)
  differential_mem n x hx := B.differential_mem (n+1) hx
  square n x := B.differential_square (n+1) x

/-- Total coordinates with positive tuple length; original total degree n
corresponds to augmented total degree n+1. -/
def positiveTotal (n : ℤ) : Submodule ℝ (ℕ → E) where
  carrier := {x | x ∈ B.total (n+1) ∧ ∀ q : ℕ, n < q → x q = 0}
  zero_mem' := ⟨(B.total _).zero_mem, fun _ _ => rfl⟩
  add_mem' := fun hx hy => ⟨(B.total _).add_mem hx.1 hy.1, fun q hq => by simp [hx.2 q hq,hy.2 q hq]⟩
  smul_mem' := fun r x hx => ⟨(B.total _).smul_mem r hx.1, fun q hq => by simp [hx.2 q hq]⟩

theorem positiveTotal_differential_mem (n : ℤ) {x : ℕ → E} (hx : x ∈ B.positiveTotal n) :
    B.differential (n+1) x ∈ B.positiveTotal (n+1) := by
  constructor
  · exact B.differential_mem (n+1) hx.1
  · intro q hq
    cases q with
    | zero => simp [hx.2 0 (by omega)]
    | succ q => simp [hx.2 (q+1) (by omega),hx.2 q (by omega)]

def positiveComplex : Complex (ℕ → E) where
  space := B.positiveTotal
  differential n := B.differential (n+1)
  differential_mem n x hx := B.positiveTotal_differential_mem n hx
  square n x := B.differential_square (n+1) x

/-- The original augmentation column; its differential is -B.vertical.
For the actual Cech grid B.vertical is minus the original exterior/coboundary
differential, giving precisely the original global complex. -/
def augmentationComplex : Complex E where
  space n := if 0 ≤ n then B.space 0 n.toNat else ⊥
  differential n := if 0 ≤ n then -B.vertical else 0
  differential_mem n x hx := by
    by_cases hn : 0 ≤ n
    · simp only [if_pos hn] at hx ⊢
      rw [if_pos (show 0 ≤ n+1 by omega)]
      have he : (n+1).toNat=n.toNat+1 := by omega
      rw [he]
      exact (B.space _ _).neg_mem (B.vertical_mem 0 n.toNat x hx)
    · simp only [if_neg hn, LinearMap.zero_apply]
      exact (if 0 ≤ n+1 then B.space 0 (n+1).toNat else ⊥).zero_mem
  square n x := by
    by_cases hn : 0 ≤ n
    · simp only [if_pos hn, if_pos (show 0 ≤ n+1 by omega), LinearMap.neg_apply,
        map_neg, neg_neg, B.vertical_square]
    · simp only [if_neg hn, LinearMap.zero_apply, map_zero]

/-- Insertion of the actual horizontal augmentation in total degree n. -/
def augmentationMapLinear (n : ℤ) : E →ₗ[ℝ] (ℕ → E) :=
  if 0 ≤ n then (LinearMap.single ℝ (fun _ : ℕ => E) n.toNat).comp B.horizontal else 0

@[simp] theorem augmentationMapLinear_nonneg (n : ℤ) (hn : 0 ≤ n) (a : E) :
    B.augmentationMapLinear n a = Pi.single n.toNat (B.horizontal a) := by
  simp [augmentationMapLinear,hn]

theorem differential_single (n : ℤ) (k : ℕ) (a : E) :
    B.differential n (Pi.single k a) =
      Pi.single k (B.horizontal a) + Pi.single (k+1) ((-1:ℝ)^(n-k) • B.vertical a) := by
  funext q
  cases q with
  | zero => by_cases hk : k=0 <;> simp [hk]
  | succ q =>
    by_cases hk : k=q+1
    · subst k
      simp
    · by_cases hkq : k=q
      · subst k
        simp
      · simp [hk,hkq,show k+1 ≠ q+1 by omega]

 def augmentationMap : Map B.augmentationComplex B.positiveComplex where
  map := B.augmentationMapLinear
  map_mem n a ha := by
    by_cases hn : 0 ≤ n
    · change a ∈ (if 0 ≤ n then B.space 0 n.toNat else ⊥) at ha
      rw [if_pos hn] at ha
      rw [B.augmentationMapLinear_nonneg n hn]
      constructor
      · apply B.single_mem
        have he : (n+1)-(n.toNat:ℤ)=1 := by omega
        rw [he]
        exact B.horizontal_mem 0 n.toNat a ha
      · intro q hq
        simp [show n.toNat ≠ q by omega]
    · simp only [augmentationMapLinear,if_neg hn,LinearMap.zero_apply]
      exact (B.positiveTotal _).zero_mem
  commute n a := by
    change B.differential (n+1) (B.augmentationMapLinear n a) =
      B.augmentationMapLinear (n+1) (B.augmentationComplex.differential n a)
    by_cases hn : 0 ≤ n
    · rw [B.augmentationMapLinear_nonneg n hn, B.differential_single]
      simp only [B.horizontal_square, Pi.single_zero, zero_add]
      rw [B.augmentationMapLinear_nonneg (n+1) (by omega)]
      change Pi.single (n.toNat+1) ((-1:ℝ)^(n+1-(n.toNat:ℤ)) • B.vertical (B.horizontal a)) =
        (Pi.single (n+1).toNat (B.horizontal ((if 0 ≤ n then -B.vertical else 0) a)) : ℕ → E)
      have he : n+1-(n.toNat:ℤ)=1 := by omega
      have ht : (n+1).toNat=n.toNat+1 := by omega
      rw [he,ht,if_pos hn]
      simp [B.commute]
    · rw [show B.augmentationMapLinear n = 0 by simp [augmentationMapLinear,hn]]
      simp only [LinearMap.zero_apply,map_zero]
      change 0 = B.augmentationMapLinear (n+1) ((if 0 ≤ n then -B.vertical else 0) a)
      simp [hn]

/-- The concrete cone-to-augmented-total map. The last coordinate is the
augmentation column; all remaining coordinates have positive tuple length. -/
def coneToTotalLinear (_B : Data E) (n : ℤ) : ((ℕ → E) × E) →ₗ[ℝ] (ℕ → E) :=
  LinearMap.fst ℝ (ℕ → E) E +
    (if 0 ≤ n+1 then
      (LinearMap.single ℝ (fun _ : ℕ => E) (n+1).toNat).comp (LinearMap.snd ℝ (ℕ → E) E)
    else 0)

@[simp] theorem coneToTotalLinear_apply (n : ℤ) (x : (ℕ → E) × E) :
    B.coneToTotalLinear n x = x.1 +
      (if 0 ≤ n+1 then Pi.single (n+1).toNat x.2 else 0) := by
  by_cases hn : 0 ≤ n+1 <;> simp [coneToTotalLinear,hn]

def coneToTotal : Map B.augmentationMap.cone B.augmentedComplex where
  map := B.coneToTotalLinear
  map_mem n x hx := by
    change x.1 ∈ B.positiveTotal n ∧ x.2 ∈ B.augmentationComplex.space (n+1) at hx
    change B.coneToTotalLinear n x ∈ B.total (n+1)
    rw [B.coneToTotalLinear_apply]
    apply (B.total _).add_mem hx.1.1
    by_cases hn : 0 ≤ n+1
    · rw [if_pos hn]
      apply B.single_mem
      have hax : x.2 ∈ (if 0 ≤ n+1 then B.space 0 (n+1).toNat else ⊥) := hx.2
      have he : n+1-((n+1).toNat:ℤ)=0 := by omega
      rw [he]
      exact (show x.2 ∈ B.space 0 (n+1).toNat from by simpa only [if_pos hn] using hax)
    · rw [if_neg hn]
      exact (B.total _).zero_mem
  commute n x := by
    change B.differential (n+1) (B.coneToTotalLinear n x) =
      B.coneToTotalLinear (n+1) (B.augmentationMap.cone.differential n x)
    rw [B.coneToTotalLinear_apply,B.coneToTotalLinear_apply]
    change B.differential (n+1) (x.1 + (if 0 ≤ n+1 then Pi.single (n+1).toNat x.2 else 0)) =
      (B.differential (n+1) x.1 + B.augmentationMapLinear (n+1) x.2) +
      (if 0 ≤ n+1+1 then Pi.single (n+1+1).toNat (-B.augmentationComplex.differential (n+1) x.2) else 0)
    by_cases hn : 0 ≤ n+1
    · rw [if_pos hn,if_pos (show 0 ≤ n+1+1 by omega),map_add,B.differential_single,
        B.augmentationMapLinear_nonneg (n+1) hn]
      have he : n+1-((n+1).toNat:ℤ)=0 := by omega
      have ht : (n+1+1).toNat=(n+1).toNat+1 := by omega
      rw [he,ht]
      change _ = _ + (Pi.single ((n+1).toNat+1) (-((if 0 ≤ n+1 then -B.vertical else 0) x.2)) : ℕ → E)
      simp [hn,add_assoc]
    · rw [if_neg hn]
      have hf : B.augmentationMapLinear (n+1) = 0 := by simp [augmentationMapLinear,hn]
      have hd : B.augmentationComplex.differential (n+1) = 0 := by simp [augmentationComplex,hn]
      rw [hf,hd]
      simp

/-- The cone identification is onto in every degree, including the empty
negative degrees. No independent-grading assumption is required. -/
theorem coneToTotal_surjective (n : ℤ) (z : B.total (n+1)) :
    ∃ x, x ∈ B.augmentationMap.cone.space n ∧ B.coneToTotalLinear n x = z.val := by
  by_cases hn : 0 ≤ n+1
  · let k := (n+1).toNat
    let a := z.val k
    have ha : a ∈ B.space 0 k := by
      have h := z.property k
      have he : n+1-(k:ℤ)=0 := by dsimp [k]; omega
      rwa [he] at h
    have has : Pi.single k a ∈ B.total (n+1) := by
      apply B.single_mem
      have he : n+1-(k:ℤ)=0 := by dsimp [k]; omega
      rwa [he]
    let b := z.val - Pi.single k a
    have hb : b ∈ B.positiveTotal n := by
      constructor
      · exact (B.total _).sub_mem z.property has
      · intro q hq
        by_cases he : q=k
        · subst q; simp [b,a]
        · have hqn : n+1 < q := by dsimp [k] at he; omega
          have hz := B.total_component_zero (n+1) z.property q hqn
          simp [b,hz,Ne.symm he]
    refine ⟨(b,a),⟨hb,?_⟩,?_⟩
    · change a ∈ (if 0 ≤ n+1 then B.space 0 (n+1).toNat else ⊥)
      simpa only [if_pos hn] using ha
    · rw [B.coneToTotalLinear_apply,if_pos hn]
      change z.val - Pi.single k a + Pi.single k a = z.val
      abel
  · have hz : z.val = 0 := by
      funext q
      exact B.total_component_zero (n+1) z.property q (by omega)
    refine ⟨0,(B.augmentationMap.cone.space n).zero_mem,?_⟩
    simp [hz]

/-- The cone identification is injective on its prescribed degree subspace. -/
theorem coneToTotal_injective (n : ℤ) (x : (ℕ → E) × E)
    (hx : x ∈ B.augmentationMap.cone.space n) (he : B.coneToTotalLinear n x = 0) : x = 0 := by
  change x.1 ∈ B.positiveTotal n ∧ x.2 ∈ B.augmentationComplex.space (n+1) at hx
  by_cases hn : 0 ≤ n+1
  · have hk : n < ((n+1).toNat:ℤ) := by omega
    have hlast := congrFun he (n+1).toNat
    rw [B.coneToTotalLinear_apply,if_pos hn] at hlast
    have ha : x.2=0 := by simpa [hx.1.2 _ hk] using hlast
    have hb : x.1=0 := by simpa [B.coneToTotalLinear_apply,hn,ha] using he
    exact Prod.ext hb ha
  · have ha : x.2=0 := by
      have hax : x.2 ∈ (if 0 ≤ n+1 then B.space 0 (n+1).toNat else ⊥) := hx.2
      simpa only [if_neg hn,Submodule.mem_bot] using hax
    have hb : x.1=0 := by simpa [B.coneToTotalLinear_apply,hn] using he
    exact Prod.ext hb ha

end P202.CochainCoverDescent.TotalAlgebra.Data

namespace P202.CochainCoverDescent.TotalAlgebra.GridEmbedding
universe u
variable (C : ℕ → ℕ → Type u)
  [∀ p q, AddCommGroup (C p q)] [∀ p q, Module ℝ (C p q)]
  (h : ∀ p q, C p q →ₗ[ℝ] C (p+1) q)
  (v : ∀ p q, C p q →ₗ[ℝ] C p (q+1))
  (hh : ∀ p q z, h (p+1) q (h p q z) = 0)
  (hv : ∀ p q z, v p (q+1) (v p q z) = 0)
  (hcomm : ∀ p q z, h p (q+1) (v p q z) = v (p+1) q (h p q z))

/-- Each original grid object is exactly its coordinate subspace. -/
def spaceEquiv (p q : ℕ) : C p q ≃ₗ[ℝ] space C p q :=
  (LinearEquiv.ofInjective (embed C p q) (embed_injective C p q)).trans
    (LinearEquiv.ofEq _ _ (space_nat C p q).symm)

/-- The original zero-th column is the actual augmentation complex. -/
def augmentationEquiv (q : ℕ) :
    C 0 q ≃ₗ[ℝ] (data C h v hh hv hcomm).augmentationComplex.space (q : ℤ) :=
  (spaceEquiv C 0 q).trans
    (LinearEquiv.ofEq _ _ (by
      simp only [Data.augmentationComplex,if_pos (Int.natCast_nonneg q),Int.toNat_natCast]
      rfl))

@[simp] theorem augmentationEquiv_val (q : ℕ) (z : C 0 q) :
    (augmentationEquiv C h v hh hv hcomm q z).val = embed C 0 q z := rfl

/-- The augmentation differential is minus the original grid vertical map.
In a Cech grid one sets the latter to minus the geometric derivative. -/
theorem augmentationEquiv_d (q : ℕ) (z : C 0 q) :
    (data C h v hh hv hcomm).augmentationComplex.differential (q:ℤ)
      (augmentationEquiv C h v hh hv hcomm q z).val =
        (augmentationEquiv C h v hh hv hcomm (q+1) (-v 0 q z)).val := by
  change (if 0 ≤ (q:ℤ) then -vertical C v else 0) (embed C 0 q z) =
    embed C 0 (q+1) (-v 0 q z)
  rw [if_pos (Int.natCast_nonneg q),LinearMap.neg_apply,vertical_embed,map_neg]

end P202.CochainCoverDescent.TotalAlgebra.GridEmbedding

namespace P202Specs.CochainCoverDescent
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 5000000
open P202.CochainCoverDescent.TotalAlgebra
open SmoothManifolds SmoothManifolds.AtlasData SmoothManifolds.BundleOperationsData
  SmoothManifolds.CovectorData SmoothManifolds.ExteriorData
universe u v

/-- For every arbitrary open cover, the literal smooth-form Čech grid has
its actual signed total and actual horizontal augmentation, and that
augmentation is an isomorphism on cohomology in every degree. Tuple length p
represents original horizontal degree p-1, so the canonical grid's vertical
operator is minus exterior differentiation. No row-exactness certificate is
an additional hypothesis. -/
def formsTotalAugmentation_type : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (C : CotangentBundle S)
    (B : ∀ q, FormBundle C q) (ι : Type v) (U : ι → TopologicalSpace.Opens M)
    (_hcover : ∀ x, ∃ i, x ∈ U i),
    ∃ D : Data (GridEmbedding.Ambient (fun p q => FormRow (B q) U p)),
      D.space = GridEmbedding.space (fun p q => FormRow (B q) U p) ∧
      D.horizontal = GridEmbedding.horizontal (fun p q => FormRow (B q) U p)
        (fun p q => formD (B q) U p) ∧
      D.vertical = GridEmbedding.vertical (fun p q => FormRow (B q) U p)
        (fun p q => (-1 : ℝ) • formV C B U q p) ∧
      ∀ m : ℤ, Function.Bijective (D.augmentationMap.cohomologyMap m)

/-- The same statement for literal products of full real algebraic duals of
smooth chains on all cover intersections. The length-zero augmentation is
cochains on cover-small smooth chains, via the previously specified actual
augmentation equivalence. -/
def cochainTotalAugmentation_type : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (ι : Type v)
    (U : SmallChainHomology.OpenCover (TopCat.of M) ι),
    ∃ D : Data (GridEmbedding.Ambient (fun p q => IntersectionCochainRow S U q p)),
      D.space = GridEmbedding.space (fun p q => IntersectionCochainRow S U q p) ∧
      D.horizontal = GridEmbedding.horizontal (fun p q => IntersectionCochainRow S U q p)
        (fun p q => intersectionD S U q p) ∧
      D.vertical = GridEmbedding.vertical (fun p q => IntersectionCochainRow S U q p)
        (fun p q => (-1 : ℝ) • intersectionV S U q p) ∧
      ∀ m : ℤ, Function.Bijective (D.augmentationMap.cohomologyMap m)

end P202Specs.CochainCoverDescent

namespace P202.CochainCoverDescent.TotalAlgebra
open P202.CochainCoverDescent.ConeAlgebra
universe v w
variable {E : Type v} [AddCommGroup E] [Module ℝ E]
  {F : Type w} [AddCommGroup F] [Module ℝ F]

/-- An actual morphism of commuting bigraded complexes. -/
structure DataMap (A : Data E) (B : Data F) where
  linear : E →ₗ[ℝ] F
  map_mem : ∀ p q x, x ∈ A.space p q → linear x ∈ B.space p q
  horizontal_commute : ∀ x, B.horizontal (linear x) = linear (A.horizontal x)
  vertical_commute : ∀ x, B.vertical (linear x) = linear (A.vertical x)

namespace Data

def totalComplex (A : Data E) : Complex (ℕ → E) where
  space := A.total
  differential := A.differential
  differential_mem n x hx := A.differential_mem n hx
  square := A.differential_square

def columnComplex (A : Data E) (p : ℤ) : Complex E where
  space n := if 0 ≤ n then A.space p n.toNat else ⊥
  differential _ := A.vertical
  differential_mem n x hx := by
    by_cases hn : 0 ≤ n
    · rw [if_pos hn] at hx
      rw [if_pos (show 0 ≤ n+1 by omega)]
      have he : (n+1).toNat=n.toNat+1 := by omega
      rw [he]
      exact A.vertical_mem p n.toNat x hx
    · rw [if_neg hn] at hx
      have hx0 : x=0 := hx
      rw [hx0,map_zero]
      exact (if 0 ≤ n+1 then A.space p (n+1).toNat else ⊥).zero_mem
  square _ x := A.vertical_square x
end Data

namespace DataMap
variable {A : Data E} {B : Data F} (f : DataMap A B)

def totalMap : Map A.totalComplex B.totalComplex where
  map _ := {
    toFun x q := f.linear (x q)
    map_add' _ _ := by funext q; exact map_add _ _ _
    map_smul' _ _ := by funext q; exact map_smul _ _ _ }
  map_mem n x hx q := f.map_mem _ q _ (hx q)
  commute n x := by
    funext q
    cases q <;> simp [Data.totalComplex,Data.differential,f.horizontal_commute,f.vertical_commute,map_add,map_smul]

def columnMap (p : ℤ) : Map (A.columnComplex p) (B.columnComplex p) where
  map _ := f.linear
  map_mem n x hx := by
    by_cases hn : 0 ≤ n
    · change x ∈ (if 0 ≤ n then A.space p n.toNat else ⊥) at hx
      rw [if_pos hn] at hx
      change f.linear x ∈ (if 0 ≤ n then B.space p n.toNat else ⊥)
      rw [if_pos hn]
      exact f.map_mem p n.toNat x hx
    · have hx0 : x=0 := by simpa [Data.columnComplex,hn] using hx
      rw [hx0,map_zero]
      exact (B.columnComplex p).space n |>.zero_mem
  commute _ x := f.vertical_commute x

end DataMap
end P202.CochainCoverDescent.TotalAlgebra

namespace P202Specs.CochainCoverDescent
open P202.CochainCoverDescent.TotalAlgebra
universe u v

/-- Every morphism of nonnegative commuting bicomplexes that induces an
isomorphism on the actual cohomology of every vertical column induces an
isomorphism on signed total cohomology. Ambient spaces, bidegree objects,
and their dimensions are unrestricted. Negative horizontal columns vanish;
column complexes are extended by zero to negative vertical degrees. -/
def columnTotalComparison_type : Prop :=
  ∀ (E : Type u) (F : Type v) [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F] (A : Data E) (B : Data F) (f : DataMap A B),
    (∀ p : ℕ, ∀ n : ℤ, Function.Bijective ((f.columnMap (p:ℤ)).cohomologyMap n)) →
    ∀ degree : ℤ, Function.Bijective (f.totalMap.cohomologyMap degree)

end P202Specs.CochainCoverDescent

namespace P202.CochainCoverDescent.TotalAlgebra
open P202.CochainCoverDescent.ConeAlgebra
universe v w
variable {E : Type v} [AddCommGroup E] [Module ℝ E]
  {F : Type w} [AddCommGroup F] [Module ℝ F]
namespace Data
variable (B : Data E)

/-- Remove the augmentation column and restore the original vertical sign.
The horizontal index p now means tuple length p+1. -/
def positiveData : Data E where
  space p q := if 0 ≤ p then B.space (p+1) q else ⊥
  horizontal := B.horizontal
  vertical := -B.vertical
  horizontal_mem p q x hx := by
    by_cases hp : 0 ≤ p
    · rw [if_pos hp] at hx
      rw [if_pos (show 0 ≤ p+1 by omega)]
      exact B.horizontal_mem (p+1) q x hx
    · rw [if_neg hp] at hx
      have hx0 : x=0 := hx
      rw [hx0,map_zero]
      exact (if 0 ≤ p+1 then B.space (p+1+1) q else ⊥).zero_mem
  vertical_mem p q x hx := by
    by_cases hp : 0 ≤ p
    · rw [if_pos hp] at hx ⊢
      exact (B.space _ _).neg_mem (B.vertical_mem (p+1) q x hx)
    · rw [if_neg hp] at hx
      have hx0 : x=0 := hx
      rw [hx0,map_zero]
      exact (if 0 ≤ p then B.space (p+1) (q+1) else ⊥).zero_mem
  horizontal_square := B.horizontal_square
  vertical_square x := by simp [B.vertical_square]
  commute x := by simp [B.commute]
  below p q hp := if_neg (by omega)

 theorem positiveData_total (n : ℤ) : B.positiveData.total n=B.positiveTotal n := by
  ext x
  constructor
  · intro hx
    constructor
    · intro q
      have hq := hx q
      change x q ∈ (if 0 ≤ n-q then B.space (n-q+1) q else ⊥) at hq
      by_cases hn : 0 ≤ n-q
      · rw [if_pos hn] at hq
        have he : n-q+1=n+1-q := by omega
        rwa [he] at hq
      · rw [if_neg hn] at hq
        have hz : x q=0 := hq
        rw [hz]
        exact (B.space _ _).zero_mem
    · intro q hq
      have h := hx q
      change x q ∈ (if 0 ≤ n-q then B.space (n-q+1) q else ⊥) at h
      simpa only [if_neg (show ¬0 ≤ n-q by omega),Submodule.mem_bot] using h
  · intro hx q
    change x q ∈ (if 0 ≤ n-q then B.space (n-q+1) q else ⊥)
    by_cases hn : 0 ≤ n-q
    · rw [if_pos hn]
      have he : n-q+1=n+1-q := by omega
      rw [he]
      exact hx.1 q
    · rw [if_neg hn]
      exact hx.2 q (by omega)

 theorem positiveData_differential (n : ℤ) :
    B.positiveData.differential n=B.differential (n+1) := by
  ext x q
  cases q with
  | zero => rfl
  | succ q =>
    change B.horizontal (x (q+1)) + (-1:ℝ)^(n-q) • (-B.vertical (x q)) =
      B.horizontal (x (q+1)) + (-1:ℝ)^(n+1-q) • B.vertical (x q)
    have he : n+1-q=(n-q)+1 := by omega
    rw [he,zpow_add₀ (by norm_num),zpow_one]
    simp

 theorem positiveData_totalComplex : B.positiveData.totalComplex=B.positiveComplex := by
  unfold totalComplex positiveComplex
  congr 1
  · funext n
    exact B.positiveData_total n
  · funext n
    exact B.positiveData_differential n

end Data
namespace DataMap
variable {A : Data E} {B : Data F} (f : DataMap A B)

/-- A map of augmented grids restricts to their genuine nonaugmented
bicomplexes, with the original source horizontal and vertical signs. -/
def positiveMap : DataMap A.positiveData B.positiveData where
  linear := f.linear
  map_mem p q x hx := by
    change x ∈ (if 0 ≤ p then A.space (p+1) q else ⊥) at hx
    change f.linear x ∈ (if 0 ≤ p then B.space (p+1) q else ⊥)
    by_cases hp : 0 ≤ p
    · rw [if_pos hp] at hx ⊢
      exact f.map_mem (p+1) q x hx
    · rw [if_neg hp] at hx ⊢
      have hx0 : x=0 := hx
      rw [hx0,map_zero]
      exact Submodule.zero_mem _
  horizontal_commute := f.horizontal_commute
  vertical_commute x := by
    change -B.vertical (f.linear x) = f.linear (-A.vertical x)
    rw [f.vertical_commute,map_neg]

end DataMap
end P202.CochainCoverDescent.TotalAlgebra
