import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.OrientedSimplicialAlgebra
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Quotient.Basic
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularChains

/-! Finite ordered Δ chains, subcomplex quotients for both simplicial models,
and affine maps to the shared singular complexes (paper.tex §T19).
Subcomplexes are actual face-closed selections, including the empty selection.
All realization maps use the weak topologies of the canonical CellStructures
interface. No local finiteness, degeneracies, or dimension bound is assumed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory
open CategoryTheory.Preadditive
open scoped Simplicial TensorProduct
universe u v w

open private P202Specs.OrientedSimplicialAlgebra.differential
  P202Specs.OrientedSimplicialAlgebra.faceMap
  from MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.OrientedSimplicialAlgebra

namespace P202Specs.RelativeParametrizations
open P202.Cellular

variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

abbrev DeltaChains (D : DeltaComplex.{w}) (n : ℕ) := D.Simplex n →₀ A

/-- Module coefficients are the tensor extension of the free ring chains. -/
def deltaCoefficientEquiv (D : DeltaComplex.{w}) (n : ℕ) :
    (DeltaChains R D n ⊗[R] A) ≃ₗ[R] DeltaChains A D n :=
  by classical exact TensorProduct.finsuppScalarLeft R A (D.Simplex n)

/-- Deleting the indicated ordered vertex. -/
def deltaFace (D : DeltaComplex.{w}) {n : ℕ} (i : Fin (n+2)) :
    D.Simplex (n+1) → D.Simplex n := D.face i.succAboveOrderEmb

/-- Every face contributes separately, even if some labels coincide. -/
def deltaBoundary (D : DeltaComplex.{w}) (n : ℕ) :
    DeltaChains A D (n+1) →ₗ[R] DeltaChains A D n :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.lmapDomain A R (deltaFace D i)

/-- The two ordered ways of deleting a pair of vertices agree. -/
theorem deltaFace_comp (D : DeltaComplex.{w}) {n : ℕ}
    (i : Fin (n+3)) (j : Fin (n+2)) (h : i ≤ j.castSucc) :
    deltaFace D (i.castLT (Nat.lt_of_le_of_lt h j.is_lt)) ∘ deltaFace D j.succ =
      deltaFace D j ∘ deltaFace D i := by
  funext s
  dsimp [deltaFace]
  rw [D.face_comp, D.face_comp]
  congr 1
  ext k
  exact congrArg Fin.val (congrArg
    (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk (n+2) => f k)
    (SimplexCategory.δ_comp_δ'' h))

private def faceMap (D : DeltaComplex.{w}) {n : ℕ} (i : Fin (n+2)) :
    ModuleCat.of R (DeltaChains A D (n+1)) ⟶ ModuleCat.of R (DeltaChains A D n) :=
  ModuleCat.ofHom (Finsupp.lmapDomain A R (deltaFace D i))

private theorem faceMap_comp (D : DeltaComplex.{w}) {n : ℕ}
    (i : Fin (n+3)) (j : Fin (n+2)) (h : i ≤ j.castSucc) :
    faceMap R A D j.succ ≫ faceMap R A D (i.castLT (Nat.lt_of_le_of_lt h j.is_lt)) =
      faceMap R A D i ≫ faceMap R A D j := by
  apply ModuleCat.hom_ext
  change (Finsupp.lmapDomain A R (deltaFace D _)).comp
      (Finsupp.lmapDomain A R (deltaFace D _)) =
    (Finsupp.lmapDomain A R (deltaFace D j)).comp
      (Finsupp.lmapDomain A R (deltaFace D i))
  rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
  rw [deltaFace_comp D i j h]

private def differential (D : DeltaComplex.{w}) (n : ℕ) :
    ModuleCat.of R (DeltaChains A D (n+1)) ⟶ ModuleCat.of R (DeltaChains A D n) :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • faceMap R A D i

/-- Pair the terms `(i,j)` with `(j,i+1)`; equal faces have opposite signs. -/
private theorem differential_squared (D : DeltaComplex.{w}) (n : ℕ) :
    differential R A D (n+1) ≫ differential R A D n = 0 := by
  classical
  dsimp [differential]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n+2) × Fin (n+3)
  let S : Finset P := Finset.univ.filter (fun ij : P => (ij.2 : ℕ) ≤ (ij.1 : ℕ))
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i,j⟩ hij ⟨i',j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using congrArg (fun p => Fin.castSucc p.1) h⟩
  · rintro ⟨i',j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, Fin.castSucc i'), ?_, ?_⟩
    · intro h
      subst h
      simp at hij'
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i,j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · rw [faceMap_comp]
      simpa [S, Fin.le_iff_val_le_val] using hij

/-- The finite ordered Δ-chain complex in nonnegative ordinary degrees. -/
def deltaComplex (D : DeltaComplex.{w}) : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (DeltaChains A D n))
    (differential R A D) (differential_squared R A D)

/-- The specified affine characteristic simplex, with the quotient weak topology. -/
def deltaParametrization (D : DeltaComplex.{w}) (n : ℕ) (s : D.Simplex n) :
    C(StandardSimplex n, D.Realization) :=
  ⟨D.simplexChart n s,
    continuous_quotient_mk'.comp (continuous_sigmaMk.comp continuous_sigmaMk)⟩

def deltaSingularSimplex (D : DeltaComplex.{w}) (n : ℕ) :
    D.Simplex n → P202Specs.SingularChains.Simplex (TopCat.of D.Realization) n :=
  fun s => (P202Specs.SingularChains.simplexEquiv _ n).symm (deltaParametrization D n s)

def deltaParametrizationLinear (D : DeltaComplex.{w}) (n : ℕ) :
    DeltaChains A D n →ₗ[R]
      P202Specs.SingularChains.Chains A (TopCat.of D.Realization) n :=
  Finsupp.lmapDomain A R (deltaSingularSimplex D n)

namespace Simplicial
open P202Specs.OrientedSimplicialAlgebra
attribute [local instance] vertexOrder
variable {V : Type w} (K : AbstractSimplicialComplex V)

/-- The affine simplex on the chosen increasing vertex representative. -/
def parametrization (n : ℕ) (s : Simplex K n) :
    C(StandardSimplex n, K.Realization) := by
  classical
  let r : Fin (n+1) → (Finset.univ.image s.1 : Finset V) :=
    fun i => ⟨s.1 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  exact ⟨K.simplexChart ⟨_, s.2⟩ ∘ Convexity.StdSimplex.map r,
    (continuous_iSup_rng (i := (⟨_, s.2⟩ : K.Simplex)) continuous_coinduced_rng).comp
      (Convexity.StdSimplex.continuous_map ℝ r)⟩

def singularSimplex (n : ℕ) (s : Simplex K n) :
    P202Specs.SingularChains.Simplex (TopCat.of K.Realization) n :=
  (P202Specs.SingularChains.simplexEquiv _ n).symm (parametrization K n s)

variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

def affineLinear (n : ℕ) : Chains K A n →ₗ[R]
    P202Specs.SingularChains.Chains A (TopCat.of K.Realization) n :=
  Finsupp.lmapDomain A R (singularSimplex K n)

end Simplicial


/-! Transparent subcomplex and quotient operations on the shared module complexes. -/

/-- The submodules selected in each degree, stable under the actual differential. -/
structure ChainSelection (C : ChainComplex (ModuleCat.{w} R) ℕ) where
  module : ∀ n, Submodule R (C.X n)
  boundary_mem : ∀ n x, x ∈ module (n+1) → (C.d (n+1) n).hom x ∈ module n

namespace ChainSelection
variable {R} {C E : ChainComplex (ModuleCat.{w} R) ℕ}

def subBoundary (S : ChainSelection R C) (n : ℕ) :
    S.module (n+1) →ₗ[R] S.module n :=
  ((C.d (n+1) n).hom.comp (S.module (n+1)).subtype).codRestrict _
    (fun x => S.boundary_mem n x.1 x.2)

def subcomplex (S : ChainSelection R C) : ChainComplex (ModuleCat.{w} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (S.module n))
    (fun n => ModuleCat.ofHom (S.subBoundary n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact congrArg (fun f : C.X (n+2) ⟶ C.X n => f.hom x.1) (C.d_comp_d (n+2) (n+1) n))

def inclusion (S : ChainSelection R C) : S.subcomplex ⟶ C :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (S.module n).subtype) (by
    intro n
    simp only [subcomplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    rfl)

def quotientBoundary (S : ChainSelection R C) (n : ℕ) :
    (C.X (n+1) ⧸ S.module (n+1)) →ₗ[R] (C.X n ⧸ S.module n) :=
  (S.module (n+1)).mapQ (S.module n) (C.d (n+1) n).hom (S.boundary_mem n)

def quotient (S : ChainSelection R C) : ChainComplex (ModuleCat.{w} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (C.X n ⧸ S.module n))
    (fun n => ModuleCat.ofHom (S.quotientBoundary n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := (S.module (n+2)).mkQ_surjective x
      change (S.module n).mkQ ((C.d (n+1) n).hom ((C.d (n+2) (n+1)).hom x)) = 0
      have h := congrArg (fun f : C.X (n+2) ⟶ C.X n => f.hom x) (C.d_comp_d (n+2) (n+1) n)
      change (C.d (n+1) n).hom ((C.d (n+2) (n+1)).hom x) = 0 at h
      rw [h, map_zero])

def projection (S : ChainSelection R C) : C ⟶ S.quotient :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (S.module n).mkQ) (by
    intro n
    simp only [quotient, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    rfl)

/-- A map of pairs descends to their actual degreewise module quotients. -/
def quotientMap (S : ChainSelection R C) (T : ChainSelection R E)
    (f : C ⟶ E) (hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ T.module n) :
    S.quotient ⟶ T.quotient :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((S.module n).mapQ (T.module n) (f.f n).hom (hf n))) (by
      intro n
      simp only [quotient, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := (S.module (n+1)).mkQ_surjective x
      change (T.module n).mkQ ((E.d (n+1) n).hom ((f.f (n+1)).hom x)) =
        (T.module n).mkQ ((f.f n).hom ((C.d (n+1) n).hom x))
      exact congrArg (T.module n).mkQ
        (congrArg (fun g : C.X (n+1) ⟶ E.X n => g.hom x) (f.comm (n+1) n)))

end ChainSelection

/-- Linear maps on supported chains need only be checked on the selected generators. -/
theorem map_supported {I : Type*} {M : Type*} [AddCommGroup M] [Module R M]
    (S : Set I) (T : Submodule R M) (f : (I →₀ A) →ₗ[R] M)
    (hf : ∀ i ∈ S, ∀ a, f (Finsupp.single i a) ∈ T)
    (x : I →₀ A) (hx : x ∈ Finsupp.supported A R S) : f x ∈ T := by
  classical
  rw [← x.sum_single, Finsupp.sum, map_sum]
  exact Submodule.sum_mem _ (fun i hi => hf i (hx hi) (x i))


/-- Actual face-closed selections of ordered simplex labels. -/
structure DeltaSubcomplex (D : DeltaComplex.{w}) where
  selected : ∀ n, Set (D.Simplex n)
  face_closed : ∀ {m n} (a : Fin (m+1) ↪o Fin (n+1)) (s : D.Simplex n),
    s ∈ selected n → D.face a s ∈ selected m

def DeltaSubcomplex.empty (D : DeltaComplex.{w}) : DeltaSubcomplex D :=
  ⟨fun _ => ∅, by intros; contradiction⟩

def DeltaSubcomplex.carrier {D : DeltaComplex.{w}} (S : DeltaSubcomplex D) :
    Set D.Realization :=
  {x | ∃ n s, s ∈ S.selected n ∧ ∃ t, D.simplexChart n s t = x}


/-- A map preserving all specified ordered parametrizations. -/
structure DeltaMap (D E : DeltaComplex.{w}) where
  simplex : ∀ n, D.Simplex n → E.Simplex n
  face : ∀ {m n} (a : Fin (m+1) ↪o Fin (n+1)) (s : D.Simplex n),
    simplex m (D.face a s) = E.face a (simplex n s)

def deltaPushforward {D E : DeltaComplex.{w}} (f : DeltaMap D E) (n : ℕ) :
    DeltaChains A D n →ₗ[R] DeltaChains A E n := Finsupp.lmapDomain A R (f.simplex n)

def DeltaSubcomplex.asComplex {D : DeltaComplex.{w}} (S : DeltaSubcomplex D) :
    DeltaComplex.{w} where
  Simplex n := S.selected n
  face a s := ⟨D.face a s.1, S.face_closed a s.1 s.2⟩
  face_id n s := Subtype.ext (D.face_id n s.1)
  face_comp a b s := Subtype.ext (D.face_comp a b s.1)

def DeltaSubcomplex.inclusion {D : DeltaComplex.{w}} (S : DeltaSubcomplex D) :
    DeltaMap S.asComplex D where
  simplex _ := Subtype.val
  face _ _ := rfl

/-- The chains supported on the selected labels, with the restricted signed boundary. -/
def deltaSelection (D : DeltaComplex.{w}) (S : DeltaSubcomplex D) :
    ChainSelection R (deltaComplex R A D) where
  module n := Finsupp.supported A R (S.selected n)
  boundary_mem n x hx := by
    simp only [deltaComplex, ChainComplex.of_d, differential, faceMap,
      ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom]
    change deltaBoundary R A D n x ∈ Finsupp.supported A R (S.selected n)
    apply map_supported R A (S.selected (n+1)) _ (deltaBoundary R A D n) ?_ x hx
    intro s hs a
    classical
    simp only [deltaBoundary, LinearMap.sum_apply, LinearMap.smul_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact Submodule.sum_mem _ (fun i _ => zsmul_mem
      (Finsupp.single_mem_supported R a (S.face_closed i.succAboveOrderEmb s hs)) _)

def deltaRelativeComplex (D : DeltaComplex.{w}) (S : DeltaSubcomplex D) :=
  (deltaSelection R A D S).quotient

namespace Simplicial
open P202Specs.OrientedSimplicialAlgebra
attribute [local instance] vertexOrder
variable {V : Type w} (K : AbstractSimplicialComplex V)

/-- A subcomplex on the same vertex type, with its actual face-closed simplices. -/
structure Subcomplex where
  complex : AbstractSimplicialComplex V
  subset : complex.simplices ⊆ K.simplices

def Subcomplex.empty : Subcomplex K where
  complex := ⟨∅, by simp, by simp⟩
  subset := Set.empty_subset _

def Subcomplex.selected (S : Subcomplex K) (n : ℕ) : Set (Simplex K n) :=
  {s | Finset.univ.image s.1 ∈ S.complex.simplices}

def Subcomplex.carrier (S : Subcomplex K) : Set K.Realization :=
  {x | x.1.weights.support ∈ S.complex.simplices}

def selection (S : Subcomplex K) : ChainSelection R (complex R A (K := K)) where
  module n := Finsupp.supported A R (S.selected K n)
  boundary_mem n x hx := by
    simp only [complex, ChainComplex.of_d,
      P202Specs.OrientedSimplicialAlgebra.differential,
      P202Specs.OrientedSimplicialAlgebra.faceMap,
      ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom]
    change boundary R A n x ∈ Finsupp.supported A R (S.selected K n)
    apply map_supported R A (S.selected K (n+1)) _ (boundary R A n) ?_ x hx
    intro s hs a
    classical
    simp only [boundary, LinearMap.sum_apply, LinearMap.smul_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    apply Submodule.sum_mem
    intro i _
    apply zsmul_mem
    apply Finsupp.single_mem_supported
    exact (face i (⟨s.1, hs⟩ : Simplex S.complex (n+1))).2

def relativeComplex (S : Subcomplex K) := (selection R A K S).quotient

end Simplicial

/-- Signed faces of a singular simplex landing in a subspace still land there. -/
theorem singularBoundary_supported (X : TopCat.{w}) (Y : Set X) (n : ℕ)
    (x : P202Specs.SingularChains.Chains A X (n+1))
    (hx : x ∈ Finsupp.supported A R
      {s | ∀ t, P202Specs.SingularChains.simplexEquiv X (n+1) s t ∈ Y}) :
    P202Specs.SingularChains.boundary R A X n x ∈ Finsupp.supported A R
      {s | ∀ t, P202Specs.SingularChains.simplexEquiv X n s t ∈ Y} := by
    apply map_supported (M := P202Specs.SingularChains.Chains A X n) R A _ _
      (P202Specs.SingularChains.boundary R A X n) ?_ x hx
    intro s hs a
    classical
    have hsingle : P202Specs.SingularChains.boundary R A X n (Finsupp.single s a) =
        ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
          Finsupp.single (P202Specs.SingularChains.face i s) a := by
      change ((AlgebraicTopology.AlternatingFaceMapComplex.obj
        (P202Specs.SingularChains.simplicialChains R A X)).d (n+1) n).hom
          (Finsupp.single s a) = _
      rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
      simp [P202Specs.SingularChains.simplicialChains,
        P202Specs.SingularChains.finsuppFunctor, LinearMap.sum_apply, LinearMap.smul_apply]
    erw [hsingle]
    apply Submodule.sum_mem
    intro i _
    apply zsmul_mem
    apply Finsupp.single_mem_supported
    intro t
    exact hs (P202Specs.SingularChains.faceInclusion i t)


/-- Shared singular chains whose continuous simplices land in the given subspace. -/
def singularSelection (X : TopCat.{w}) (Y : Set X) :
    ChainSelection R (P202Specs.SingularChains.complex R A X) where
  module n := Finsupp.supported A R
    {s | ∀ t, P202Specs.SingularChains.simplexEquiv X n s t ∈ Y}
  boundary_mem := singularBoundary_supported R A X Y

/-- The actual inclusion of a subspace, in the upstream singular functor. -/
def subspaceInclusion (X : TopCat.{w}) (Y : Set X) : TopCat.of Y ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def singularRelativeComplex (X : TopCat.{w}) (Y : Set X) :=
  (singularSelection R A X Y).quotient



/-! Full independent expected declarations for the submitted implementation. -/
namespace Expected
open P202Specs.OrientedSimplicialAlgebra
open P202Specs.RelativeParametrizations.Simplicial
attribute [local instance] vertexOrder

def deltaChainComplex_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}),
    ChainComplex (ModuleCat.{max v w} R) ℕ

def deltaChainComplex_value (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) :
    ChainComplex (ModuleCat.{max v w} R) ℕ :=
  deltaComplex R A D

def deltaBoundary_zero_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (n : ℕ),
    (deltaComplex R A D).d 0 n = 0

def deltaBoundary_eq_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (n : ℕ),
    ((deltaComplex R A D).d (n+1) n).hom = deltaBoundary R A D n

def deltaBoundary_single_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (n : ℕ)
    (s : D.Simplex (n+1)) (a : A),
    deltaBoundary R A D n (Finsupp.single s a) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single (deltaFace D i s) a

def deltaBoundary_squared_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (n : ℕ),
    (deltaBoundary R A D n).comp (deltaBoundary R A D (n+1)) = 0

def deltaCoefficientEquiv_single_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (n : ℕ)
    (s : D.Simplex n) (r : R) (a : A),
    deltaCoefficientEquiv R A D n (Finsupp.single s r ⊗ₜ[R] a) =
      Finsupp.single s (r • a)

def deltaCoefficientEquiv_boundary_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (n : ℕ)
    (x : DeltaChains R D (n+1) ⊗[R] A),
    deltaBoundary R A D n (deltaCoefficientEquiv R A D (n+1) x) =
      deltaCoefficientEquiv R A D n ((deltaBoundary R R D n).rTensor A x)

def deltaSingularSimplex_face_type :=
  ∀ (D : DeltaComplex.{w}) (n : ℕ)
    (i : Fin (n+2)) (s : D.Simplex (n+1)),
    deltaSingularSimplex D n (deltaFace D i s) =
      P202Specs.SingularChains.face i (deltaSingularSimplex D (n+1) s)

def deltaParametrizationLinear_single_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (n : ℕ)
    (s : D.Simplex n) (a : A),
    deltaParametrizationLinear R A D n (Finsupp.single s a) =
      Finsupp.single (deltaSingularSimplex D n s) a

def deltaAffineChainMap_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}),
    ∃ f : deltaComplex R A D ⟶
      P202Specs.SingularChains.complex R A (TopCat.of D.Realization),
      ∀ n, (f.f n).hom = deltaParametrizationLinear R A D n

def deltaPushforward_single_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {D E : DeltaComplex.{w}} (f : DeltaMap D E)
    (n : ℕ) (s : D.Simplex n) (a : A),
    deltaPushforward R A f n (Finsupp.single s a) = Finsupp.single (f.simplex n s) a

def deltaPushforward_chainMap_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {D E : DeltaComplex.{w}} (f : DeltaMap D E),
    ∃ F : deltaComplex R A D ⟶ deltaComplex R A E,
      ∀ n, (F.f n).hom = deltaPushforward R A f n

def Simplicial.parametrization_value_type :=
  ∀ {V : Type w} (K : AbstractSimplicialComplex V)
  (n : ℕ) (s : Simplex K n) (x : StandardSimplex n),
    (parametrization K n s x).1 = x.map s.1

def Simplicial.singularSimplex_face_type :=
  ∀ {V : Type w} (K : AbstractSimplicialComplex V)
  (n : ℕ) (i : Fin (n+2)) (s : Simplex K (n+1)),
    singularSimplex K n (face i s) =
      P202Specs.SingularChains.face i (singularSimplex K (n+1) s)

def Simplicial.affineLinear_single_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  (n : ℕ) (s : Simplex K n) (a : A),
    affineLinear K R A n (Finsupp.single s a) =
      Finsupp.single (singularSimplex K n s) a

def Simplicial.affineChainMap_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V),
    ∃ f : complex R A (K := K) ⟶
      P202Specs.SingularChains.complex R A (TopCat.of K.Realization),
      ∀ n, (f.f n).hom = affineLinear K R A n

def Quotient.inclusion_injective_type :=
  ∀ {R : Type u} [CommRing R] {C : ChainComplex (ModuleCat.{w} R) ℕ}
  (S : ChainSelection R C) (n : ℕ),
    Function.Injective ((S.inclusion.f n).hom)

def Quotient.projection_surjective_type :=
  ∀ {R : Type u} [CommRing R] {C : ChainComplex (ModuleCat.{w} R) ℕ}
  (S : ChainSelection R C) (n : ℕ),
    Function.Surjective ((S.projection.f n).hom)

def Quotient.projection_kernel_type :=
  ∀ {R : Type u} [CommRing R] {C : ChainComplex (ModuleCat.{w} R) ℕ}
  (S : ChainSelection R C) (n : ℕ),
    LinearMap.ker ((S.projection.f n).hom) = S.module n

def Quotient.boundary_mk_type :=
  ∀ {R : Type u} [CommRing R] {C : ChainComplex (ModuleCat.{w} R) ℕ}
  (S : ChainSelection R C) (n : ℕ) (x : C.X (n+1)),
    ((S.quotient.d (n+1) n).hom) ((S.module (n+1)).mkQ x) =
      (S.module n).mkQ ((C.d (n+1) n).hom x)

def Quotient.boundary_zero_type :=
  ∀ {R : Type u} [CommRing R] {C : ChainComplex (ModuleCat.{w} R) ℕ}
  (S : ChainSelection R C) (n : ℕ),
    S.quotient.d 0 n = 0

def Quotient.boundary_squared_type :=
  ∀ {R : Type u} [CommRing R] {C : ChainComplex (ModuleCat.{w} R) ℕ}
  (S : ChainSelection R C) (n : ℕ),
    ((S.quotient.d (n+1) n).hom).comp ((S.quotient.d (n+2) (n+1)).hom) = 0

def Quotient.map_mk_type :=
  ∀ {R : Type u} [CommRing R] {C E : ChainComplex (ModuleCat.{w} R) ℕ}
  (S : ChainSelection R C) (T : ChainSelection R E)
    (f : C ⟶ E) (hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ T.module n)
    (n : ℕ) (x : C.X n),
    (((S.quotientMap T f hf).f n).hom) ((S.module n).mkQ x) =
      (T.module n).mkQ ((f.f n).hom x)

def singularSelection_range_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (X : TopCat.{w}) (Y : Set X) (n : ℕ),
    LinearMap.range ((P202Specs.SingularChains.chainMap R A
      (subspaceInclusion X Y)).f n).hom = (singularSelection R A X Y).module n

def deltaEmpty_module_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (n : ℕ),
    (deltaSelection R A D (DeltaSubcomplex.empty D)).module n = ⊥

def deltaSelectedEquiv_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (S : DeltaSubcomplex D) (n : ℕ),
    (deltaSelection R A D S).module n ≃ₗ[R] ((S.selected n) →₀ A)

def deltaSelectedEquiv_value (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (S : DeltaSubcomplex D) (n : ℕ) :
    (deltaSelection R A D S).module n ≃ₗ[R] ((S.selected n) →₀ A) :=
  Finsupp.supportedEquivFinsupp (R := R) _

def deltaPairComplex_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (S : DeltaSubcomplex D),
    ChainComplex (ModuleCat.{max v w} R) ℕ

def deltaPairComplex_value (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (S : DeltaSubcomplex D) :
    ChainComplex (ModuleCat.{max v w} R) ℕ :=
  deltaRelativeComplex R A D S

def deltaRelativeBoundary_single_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (S : DeltaSubcomplex D)
    (n : ℕ) (s : D.Simplex (n+1)) (a : A),
    ((deltaRelativeComplex R A D S).d (n+1) n).hom
      (((deltaSelection R A D S).module (n+1)).mkQ (Finsupp.single s a)) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        (((deltaSelection R A D S).module n).mkQ (Finsupp.single (deltaFace D i s) a))

def deltaAffine_preserves_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (S : DeltaSubcomplex D)
    (n : ℕ) (x : DeltaChains A D n) (hx : x ∈ (deltaSelection R A D S).module n),
    deltaParametrizationLinear R A D n x ∈
      (singularSelection R A (TopCat.of D.Realization) S.carrier).module n

def deltaRelativeAffineChainMap_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (S : DeltaSubcomplex D),
    ∃ f : deltaRelativeComplex R A D S ⟶
      singularRelativeComplex R A (TopCat.of D.Realization) S.carrier,
      ∀ n x, (f.f n).hom (((deltaSelection R A D S).module n).mkQ x) =
        ((singularSelection R A (TopCat.of D.Realization) S.carrier).module n).mkQ
          (deltaParametrizationLinear R A D n x)

def deltaInclusion_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  (D : DeltaComplex.{w}) (S : DeltaSubcomplex D),
    ∃ f : deltaComplex R A S.asComplex ⟶ deltaComplex R A D,
      (∀ n, (f.f n).hom = deltaPushforward R A S.inclusion n) ∧
      (∀ n, Function.Injective (f.f n).hom) ∧
      (∀ n, LinearMap.range (f.f n).hom = (deltaSelection R A D S).module n)

def deltaPushforward_preserves_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {D E : DeltaComplex.{w}} (S : DeltaSubcomplex D)
    (T : DeltaSubcomplex E) (f : DeltaMap D E)
    (hpair : ∀ n s, s ∈ S.selected n → f.simplex n s ∈ T.selected n)
    (n : ℕ) (x : DeltaChains A D n) (hx : x ∈ (deltaSelection R A D S).module n),
    deltaPushforward R A f n x ∈ (deltaSelection R A E T).module n

def deltaRelativePushforward_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {D E : DeltaComplex.{w}} (S : DeltaSubcomplex D)
    (T : DeltaSubcomplex E) (f : DeltaMap D E)
    (hpair : ∀ n s, s ∈ S.selected n → f.simplex n s ∈ T.selected n),
    ∃ F : deltaRelativeComplex R A D S ⟶ deltaRelativeComplex R A E T,
      ∀ n x, (F.f n).hom (((deltaSelection R A D S).module n).mkQ x) =
        ((deltaSelection R A E T).module n).mkQ (deltaPushforward R A f n x)

def Simplicial.pairComplex_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  (S : Subcomplex K),
    ChainComplex (ModuleCat.{max v w} R) ℕ

def Simplicial.pairComplex_value (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  (S : Subcomplex K) :
    ChainComplex (ModuleCat.{max v w} R) ℕ :=
  relativeComplex R A K S

def Simplicial.empty_module_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  (n : ℕ),
    (selection R A K (Subcomplex.empty K)).module n = ⊥

def Simplicial.relativeBoundary_single_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  (S : Subcomplex K) (n : ℕ)
    (s : Simplex K (n+1)) (a : A),
    ((relativeComplex R A K S).d (n+1) n).hom
      (((selection R A K S).module (n+1)).mkQ (Finsupp.single s a)) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        (((selection R A K S).module n).mkQ (Finsupp.single (face i s) a))

def Simplicial.parametrization_lands_type :=
  ∀ {V : Type w} (K : AbstractSimplicialComplex V)
  (S : Subcomplex K) (n : ℕ) (s : Simplex K n)
    (hs : s ∈ S.selected K n) (t : StandardSimplex n),
    parametrization K n s t ∈ S.carrier K

def Simplicial.affine_preserves_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  (S : Subcomplex K) (n : ℕ) (x : Chains K A n)
    (hx : x ∈ (selection R A K S).module n),
    affineLinear K R A n x ∈
      (singularSelection R A (TopCat.of K.Realization) (S.carrier K)).module n

def Simplicial.relativeAffineChainMap_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  (S : Subcomplex K),
    ∃ f : relativeComplex R A K S ⟶
      singularRelativeComplex R A (TopCat.of K.Realization) (S.carrier K),
      ∀ n x, (f.f n).hom (((selection R A K S).module n).mkQ x) =
        ((singularSelection R A (TopCat.of K.Realization) (S.carrier K)).module n).mkQ
          (affineLinear K R A n x)

def Simplicial.inclusion_range_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  (S : Subcomplex K) (n : ℕ),
    LinearMap.range (pushforward R A (SimplicialMap.inclusion S.subset) n) =
      (selection R A K S).module n

def Simplicial.inclusion_chainMap_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  (S : Subcomplex K),
    ∃ f : complex R A (K := S.complex) ⟶ complex R A (K := K),
      (∀ n, (f.f n).hom = pushforward R A (SimplicialMap.inclusion S.subset) n) ∧
      (∀ n, Function.Injective (f.f n).hom) ∧
      (∀ n, LinearMap.range (f.f n).hom = (selection R A K S).module n)

def Simplicial.pushforward_preserves_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  {W : Type w} (L : AbstractSimplicialComplex W)
    (S : Subcomplex K) (T : Subcomplex L) (f : SimplicialMap (K := K) L)
    (hpair : ∀ s ∈ S.complex.simplices, s.image f.vertices ∈ T.complex.simplices)
    (n : ℕ) (x : Chains K A n) (hx : x ∈ (selection R A K S).module n),
    pushforward R A f n x ∈ (selection R A L T).module n

def Simplicial.relativePushforward_type :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
  {V : Type w} (K : AbstractSimplicialComplex V)
  {W : Type w} (L : AbstractSimplicialComplex W)
    (S : Subcomplex K) (T : Subcomplex L) (f : SimplicialMap (K := K) L)
    (hpair : ∀ s ∈ S.complex.simplices, s.image f.vertices ∈ T.complex.simplices),
    ∃ F : relativeComplex R A K S ⟶ relativeComplex R A L T,
      ∀ n x, (F.f n).hom (((selection R A K S).module n).mkQ x) =
        ((selection R A L T).module n).mkQ (pushforward R A f n x)

end Expected
end P202Specs.RelativeParametrizations

/- Mathlib proof attribution
Adapted portion near line 81:
The face-index pairing and Finset.sum_bij argument for the squared
differential in the relative parametrization construction.

Upstream: Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean (around line 75)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz, Johan Commelin

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
