import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! Canonical finite oriented chains for the complexes of Definition 2.1.
A vertex order is chosen for every type; no orderability or finiteness assumption
is imposed on the complex. Coefficients are an arbitrary module. -/
noncomputable section
open CategoryTheory CategoryTheory.Preadditive
open scoped TensorProduct
universe u v w w'
namespace P202Specs.OrientedSimplicialAlgebra
open P202.Cellular

/-- A fixed choice, also for types not supplied with an order. -/
@[instance_reducible] def vertexOrder (V : Type w) : LinearOrder V := by
  classical
  exact linearOrderOfSTO WellOrderingRel
attribute [local instance] vertexOrder

variable {V : Type w} (K : AbstractSimplicialComplex V)

/-- The increasing representative of a simplex. -/
def Simplex (n : ℕ) :=
  {s : Fin (n+1) ↪o V // Finset.univ.image s ∈ K.simplices}

/-- The underlying unoriented simplex has exactly `n+1` vertices. -/
def UnorderedSimplex (n : ℕ) :=
  {s : Finset V // s ∈ K.simplices ∧ s.card = n+1}

/-- Increasing representatives are in bijection with the actual finite vertex sets. -/
def simplexEquiv (n : ℕ) : Simplex K n ≃ UnorderedSimplex K n where
  toFun s := ⟨Finset.univ.image s.1, s.2, by
    rw [Finset.card_image_of_injective _ s.1.injective, Finset.card_univ, Fintype.card_fin]⟩
  invFun s := ⟨s.1.orderEmbOfFin s.2.2, by
    simpa only [Finset.image_orderEmbOfFin_univ] using s.2.1⟩
  left_inv s := by
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique' _ (fun i =>
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).symm
  right_inv s := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ _ _

/-- Tuples may repeat vertices. This permits the signed image of a collapsing map. -/
def VertexTuple (n : ℕ) :=
  {s : Fin (n+1) → V // Finset.univ.image s ∈ K.simplices}

abbrev Chains (A : Type v) [AddCommGroup A] (n : ℕ) := Simplex K n →₀ A

variable {K}

/-- Deleting a vertex from an increasing representative gives an increasing face. -/
def face {n : ℕ} (i : Fin (n+2)) (s : Simplex K (n+1)) : Simplex K n :=
  ⟨i.succAboveOrderEmb.trans s.1, K.face s.2
    (by intro x hx; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨i.succAbove j, Finset.mem_univ _, rfl⟩)
    (Finset.image_nonempty.mpr Finset.univ_nonempty)⟩

/-- The increasing tuple underlying an oriented tuple with distinct vertices. -/
def sorted {n : ℕ} (s : VertexTuple K n) (hs : Function.Injective s.1) : Simplex K n :=
  ⟨OrderEmbedding.ofStrictMono (s.1 ∘ Tuple.sort s.1)
    ((Tuple.monotone_sort s.1).strictMono_of_injective
      (hs.comp (Tuple.sort s.1).injective)), by
      convert s.2 using 1
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
      exact ⟨fun ⟨i, hi⟩ => ⟨Tuple.sort s.1 i, hi⟩,
        fun ⟨i, hi⟩ => ⟨(Tuple.sort s.1).symm i, by simpa using hi⟩⟩⟩

/-- A permutation changes only the parametrization of the tuple. -/
def permute {n : ℕ} (s : VertexTuple K n) (σ : Equiv.Perm (Fin (n+1))) : VertexTuple K n :=
  ⟨s.1 ∘ σ, by
    convert s.2 using 1
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩,
      fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa using hi⟩⟩⟩

/-- Delete one entry, retaining the original ordering and any repetitions. -/
def tupleFace {n : ℕ} (i : Fin (n+2)) (s : VertexTuple K (n+1)) : VertexTuple K n :=
  ⟨s.1 ∘ i.succAbove, K.face s.2
    (by intro x hx; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨i.succAbove j, Finset.mem_univ _, rfl⟩)
    (Finset.image_nonempty.mpr Finset.univ_nonempty)⟩

variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- Over the coefficient ring these increasing simplices are a genuine basis. -/
def increasingBasis (n : ℕ) : Module.Basis (Simplex K n) R (Chains K R n) :=
  Finsupp.basisSingleOne

/-- For a module, chains are the extension of scalars of these free chains. -/
def coefficientEquiv (n : ℕ) : (Chains K R n) ⊗[R] A ≃ₗ[R] Chains K A n :=
  TensorProduct.finsuppScalarLeft R A (Simplex K n)

/-- Coefficients on increasing representatives, extended by zero on repeated tuples.
In particular this construction does not quotient by `x = -x`. -/
def oriented {n : ℕ} (s : VertexTuple K n) (a : A) : Chains K A n := by
  classical
  exact if hs : Function.Injective s.1 then
    (Equiv.Perm.sign (Tuple.sort s.1) : ℤ) • Finsupp.single (sorted s hs) a
  else 0

/-- The ordinary differential in positive degrees. -/
def boundary (n : ℕ) : Chains K A (n+1) →ₗ[R] Chains K A n :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.lmapDomain A R (face i)

private theorem face_coherence {n : ℕ}
    (i : Fin (n+3)) (j : Fin (n+2)) (h : i ≤ j.castSucc) :
    face (K := K) (i.castLT (Nat.lt_of_le_of_lt h j.is_lt)) ∘ face j.succ =
      face j ∘ face i := by
  funext s
  apply Subtype.ext
  apply DFunLike.ext
  intro k
  change s.1 (j.succ.succAbove ((i.castLT _).succAbove k)) =
    s.1 (i.succAbove (j.succAbove k))
  congr 1
  exact congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk (n+2) => f k)
    (SimplexCategory.δ_comp_δ'' h)

private def faceMap  {n : ℕ} (i : Fin (n+2)) :
    ModuleCat.of R (Chains K A (n+1)) ⟶ ModuleCat.of R (Chains K A n) :=
  ModuleCat.ofHom (Finsupp.lmapDomain A R (face (K := K) i))

private theorem faceMap_comp  {n : ℕ}
    (i : Fin (n+3)) (j : Fin (n+2)) (h : i ≤ j.castSucc) :
    faceMap R A (K := K) j.succ ≫ faceMap R A (K := K) (i.castLT (Nat.lt_of_le_of_lt h j.is_lt)) =
      faceMap R A (K := K) i ≫ faceMap R A (K := K) j := by
  apply ModuleCat.hom_ext
  change (Finsupp.lmapDomain A R (face (K := K) _)).comp
      (Finsupp.lmapDomain A R (face (K := K) _)) =
    (Finsupp.lmapDomain A R (face (K := K) j)).comp
      (Finsupp.lmapDomain A R (face (K := K) i))
  rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
  rw [face_coherence i j h]

private def differential  (n : ℕ) :
    ModuleCat.of R (Chains K A (n+1)) ⟶ ModuleCat.of R (Chains K A n) :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • faceMap R A (K := K) i

/-- Pair the terms `(i,j)` with `(j,i+1)`; equal faces have opposite signs. -/
private theorem differential_squared  (n : ℕ) :
    differential R A (K := K) (n+1) ≫ differential R A (K := K) n = 0 := by
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

/-- Finite oriented ordinary chains, with zero outgoing degree-zero differential. -/
def complex  : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (Chains K A n))
    (differential R A (K := K)) (differential_squared R A (K := K))


/-- A simplicial map need not be injective or preserve the chosen orders. -/
structure SimplicialMap {W : Type w'} (L : AbstractSimplicialComplex W) where
  vertices : V → W
  map_simplex : ∀ s ∈ K.simplices, s.image vertices ∈ L.simplices

namespace SimplicialMap
variable {W : Type w'} {L : AbstractSimplicialComplex W}

def id (K : AbstractSimplicialComplex V) : SimplicialMap (K := K) K :=
  ⟨_root_.id, by intro s hs; simpa using hs⟩

def comp {U : Type*} {M : AbstractSimplicialComplex U}
    (g : SimplicialMap (K := L) M) (f : SimplicialMap (K := K) L) :
    SimplicialMap (K := K) M :=
  ⟨g.vertices ∘ f.vertices, by
    intro s hs
    simpa only [Finset.image_image] using g.map_simplex _ (f.map_simplex s hs)⟩

/-- An inclusion of subcomplexes is a simplicial map with identity vertex map. -/
def inclusion {L : AbstractSimplicialComplex V} (h : K.simplices ⊆ L.simplices) :
    SimplicialMap (K := K) L := ⟨_root_.id, by intro s hs; simpa using h hs⟩

/-- The image tuple still spans a target simplex, including when vertices collapse. -/
def imageTuple (f : SimplicialMap (K := K) L) {n : ℕ} (s : VertexTuple K n) :
    VertexTuple L n :=
  ⟨f.vertices ∘ s.1, by
    simpa only [Finset.image_image] using f.map_simplex _ s.2⟩
end SimplicialMap

/-- The map on increasing representatives for a subcomplex inclusion. -/
def inclusionSimplex {L : AbstractSimplicialComplex V}
    (h : K.simplices ⊆ L.simplices) {n : ℕ} (s : Simplex K n) : Simplex L n :=
  ⟨s.1, h s.2⟩

/-- A linear signed pushforward specified on the increasing generators. -/
def pushforward {W : Type w'} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) (n : ℕ) : Chains K A n →ₗ[R] Chains L A n :=
  Finsupp.lsum R fun s =>
    { toFun := fun a => oriented A (f.imageTuple ⟨s.1, s.2⟩) a
      map_add' := by
        classical
        intro a b
        simp only [oriented]
        split <;> simp [Finsupp.single_add, smul_add]
      map_smul' := by
        classical
        intro r a
        simp only [oriented]
        split <;> simp [Finsupp.single_smul, smul_comm r] }


/-! Full independent expected propositions for the implementation bindings. -/

def oriented_repeated_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (A : Type v) [AddCommGroup A]
    {n : ℕ} (s : VertexTuple K n)
    (hs : ¬ Function.Injective s.1) (a : A),
    oriented A s a = 0

def oriented_permute_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (A : Type v) [AddCommGroup A]
    {n : ℕ} (s : VertexTuple K n)
    (σ : Equiv.Perm (Fin (n+1))) (a : A),
    oriented A (permute s σ) a = (Equiv.Perm.sign σ : ℤ) • oriented A s a

def oriented_increasing_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (A : Type v) [AddCommGroup A]
    {n : ℕ} (s : Simplex K n) (a : A),
    oriented A ⟨s.1, s.2⟩ a = Finsupp.single s a

def boundary_single_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (n : ℕ) (s : Simplex K (n+1)) (a : A),
    boundary R A n (Finsupp.single s a) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single (face i s) a

def boundary_oriented_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {n : ℕ} (s : VertexTuple K (n+1)) (a : A),
    boundary R A n (oriented A s a) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • oriented A (tupleFace i s) a

def boundary_squared_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (n : ℕ),
    (boundary R A (K := K) n).comp (boundary R A (n+1)) = 0

def boundary_zero_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (n : ℕ),
    (complex R A (K := K)).d 0 n = 0

def boundary_eq_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (n : ℕ),
    ((complex R A (K := K)).d (n+1) n).hom = boundary R A n

def pushforward_single_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {W : Type w'} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) (n : ℕ) (s : Simplex K n) (a : A),
    pushforward R A f n (Finsupp.single s a) =
      oriented A (f.imageTuple ⟨s.1, s.2⟩) a

def pushforward_collapse_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {W : Type w'} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) (n : ℕ) (s : Simplex K n)
    (hs : ¬ Function.Injective (f.vertices ∘ s.1)) (a : A),
    pushforward R A f n (Finsupp.single s a) = 0

def pushforward_oriented_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {W : Type w'} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) {n : ℕ} (s : VertexTuple K n) (a : A),
    pushforward R A f n (oriented A s a) = oriented A (f.imageTuple s) a

def pushforward_boundary_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {W : Type w'} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) (n : ℕ),
    (boundary R A n).comp (pushforward R A f (n+1)) =
      (pushforward R A f n).comp (boundary R A n)

def pushforward_id_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (n : ℕ),
    pushforward R A (SimplicialMap.id K) n = LinearMap.id

def pushforward_comp_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {W : Type w'} {U : Type*}
    {L : AbstractSimplicialComplex W} {M : AbstractSimplicialComplex U}
    (g : SimplicialMap (K := L) M) (f : SimplicialMap (K := K) L) (n : ℕ),
    (pushforward R A g n).comp (pushforward R A f n) =
      pushforward R A (g.comp f) n

def pushforward_chainMap_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {W : Type w} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L),
    ∃ F : complex R A (K := K) ⟶ complex R A (K := L),
      ∀ n, (F.f n).hom = pushforward R A f n

def pushforward_inclusion_single_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {L : AbstractSimplicialComplex V}
    (h : K.simplices ⊆ L.simplices) (n : ℕ) (s : Simplex K n) (a : A),
    pushforward R A (SimplicialMap.inclusion h) n (Finsupp.single s a) =
      Finsupp.single (inclusionSimplex h s) a

def pushforward_inclusion_injective_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    {L : AbstractSimplicialComplex V}
    (h : K.simplices ⊆ L.simplices) (n : ℕ),
    Function.Injective (pushforward R A (SimplicialMap.inclusion h) n)

def increasingBasis_apply_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R]
    (n : ℕ) (s : Simplex K n),
    increasingBasis R (K := K) n s = Finsupp.single s (1 : R)

def coefficientEquiv_single_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (n : ℕ) (s : Simplex K n) (a : A),
    coefficientEquiv R A n (Finsupp.single s 1 ⊗ₜ[R] a) = Finsupp.single s a

def coefficientEquiv_tmul_single_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (n : ℕ) (s : Simplex K n) (r : R) (a : A),
    coefficientEquiv R A n (Finsupp.single s r ⊗ₜ[R] a) =
      Finsupp.single s (r • a)

def coefficientEquiv_boundary_type : Prop :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (n : ℕ) (x : Chains K R (n+1) ⊗[R] A),
    boundary R A n (coefficientEquiv R A (n+1) x) =
      coefficientEquiv R A n ((boundary R R n).rTensor A x)

def chainComplex_type :=
  ∀ {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A],
    ChainComplex (ModuleCat.{max v w} R) ℕ

def chainComplex_value {V : Type w} {K : AbstractSimplicialComplex V}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A] :
    ChainComplex (ModuleCat.{max v w} R) ℕ := complex R A (K := K)

end P202Specs.OrientedSimplicialAlgebra

/- Mathlib proof attribution
Adapted portion near line 150:
The face-index pairing and Finset.sum_bij argument for the squared
differential in oriented simplicial chains.

Upstream: Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean (around line 75)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz, Johan Commelin

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
