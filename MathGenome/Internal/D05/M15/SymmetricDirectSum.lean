import MathGenome.Internal.Specs.D05.M15.SymmetricDirectSum
import MathGenome.Internal.D05.M15.SymmetricBasis

/-! The algebra maps are inverse by their actions on generators. For the
homogeneous restriction we first descend tensor-algebra component projections
through the commutator quotient. Tensor distribution then gives a left inverse
for the total-degree inclusion. Subset expansion proves that the forward map
lands in that total degree; multiplication of homogeneous images proves the
reverse containment. Everything applies to arbitrary-dimensional spaces over
any field, including p = 0. -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace D05.M15.SymmetricDirectSum
open scoped TensorProduct
open Specs.D05.M15.Symmetric
open Specs.D05.M15.SymmetricBasis (powerInclusion)
open Specs.D05.M15.SymmetricDirectSum (leftMap rightMap DegreePairs DegreeSum degreeInclusion)

abbrev forward := Specs.D05.M15.SymmetricDirectSum.forward
abbrev backward := Specs.D05.M15.SymmetricDirectSum.backward

theorem tensor_multiplication : Specs.D05.M15.SymmetricDirectSum.tensor_multiplication := by
  intro K V W _ _ _ _ _ a c b d
  exact ⟨Algebra.TensorProduct.tmul_mul_tmul _ _ _ _, mul_comm _ _⟩

theorem tensor_commutative : Specs.D05.M15.SymmetricDirectSum.tensor_commutative := by
  intro K V W _ _ _ _ _ x y
  exact mul_comm x y

theorem forward_generator : Specs.D05.M15.SymmetricDirectSum.forward_generator := by
  intro K V W _ _ _ _ _ v w
  simp [Specs.D05.M15.SymmetricDirectSum.forward, LinearMap.coprod_apply]

theorem backward_tmul : Specs.D05.M15.SymmetricDirectSum.backward_tmul := by
  intro K V W _ _ _ _ _ a b
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

section Algebra
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

@[simp] theorem forward_ι (v : V) (w : W) :
    forward K V W (_root_.SymmetricAlgebra.ι K (V × W) (v,w)) =
      _root_.SymmetricAlgebra.ι K V v ⊗ₜ[K] 1 +
        1 ⊗ₜ[K] _root_.SymmetricAlgebra.ι K W w := forward_generator K V W v w

@[simp] theorem backward_pure (a : symmetricAlgebra K V) (b : symmetricAlgebra K W) :
    backward K V W (a ⊗ₜ[K] b) = leftMap K V W a * rightMap K V W b :=
  backward_tmul K V W a b

@[simp] theorem left_generator (v : V) :
    leftMap K V W (_root_.SymmetricAlgebra.ι K V v) =
      _root_.SymmetricAlgebra.ι K (V × W) (v,0) := by
  simp [leftMap]

@[simp] theorem right_generator (w : W) :
    rightMap K V W (_root_.SymmetricAlgebra.ι K W w) =
      _root_.SymmetricAlgebra.ι K (V × W) (0,w) := by
  simp [rightMap]

theorem backward_forward : (backward K V W).comp (forward K V W) = AlgHom.id K _ := by
  apply D05.M15.Symmetric.hom_ext
  rintro ⟨v,w⟩
  simp only [AlgHom.comp_apply, forward_ι, map_add, backward_pure,
    map_one, mul_one, one_mul, left_generator, right_generator, AlgHom.id_apply]
  rw [← map_add]
  simp

theorem forward_left : (forward K V W).comp (leftMap K V W) =
    Algebra.TensorProduct.includeLeft := by
  apply D05.M15.Symmetric.hom_ext
  intro v
  simp [Algebra.TensorProduct.includeLeft_apply]

theorem forward_right : (forward K V W).comp (rightMap K V W) =
    Algebra.TensorProduct.includeRight := by
  apply D05.M15.Symmetric.hom_ext
  intro w
  simp [Algebra.TensorProduct.includeRight_apply]

theorem forward_backward : (forward K V W).comp (backward K V W) = AlgHom.id K _ := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro a b
  change forward K V W (backward K V W (a ⊗ₜ[K] b)) = a ⊗ₜ[K] b
  rw [backward_pure, map_mul]
  have hl := DFunLike.congr_fun (forward_left (K := K) (V := V) (W := W)) a
  have hr := DFunLike.congr_fun (forward_right (K := K) (V := V) (W := W)) b
  change forward K V W (leftMap K V W a) = a ⊗ₜ[K] 1 at hl
  change forward K V W (rightMap K V W b) = 1 ⊗ₜ[K] b at hr
  rw [hl, hr, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

def algebraEquiv : symmetricAlgebra K (V × W) ≃ₐ[K]
    symmetricAlgebra K V ⊗[K] symmetricAlgebra K W :=
  AlgEquiv.ofAlgHom (forward K V W) (backward K V W) forward_backward backward_forward
end Algebra

theorem algebra_equiv : Specs.D05.M15.SymmetricDirectSum.algebra_equiv := by
  intro K V W _ _ _ _ _
  exact ⟨algebraEquiv, rfl, rfl⟩

section Degree
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Quotient each homogeneous tensor component, before descending the global quotient. -/
def tensorComponents : _root_.TensorAlgebra K V →ₗ[K]
    _root_.DirectSum ℕ (symmetricPower K V) :=
  (_root_.DirectSum.lmap (fun p => (adjacentRelations K V p).mkQ)).comp
    _root_.TensorAlgebra.equivDirectSum.toLinearMap

theorem tensorComponents_kills :
    LinearMap.ker (_root_.SymmetricAlgebra.algHom K V).toLinearMap ≤
      LinearMap.ker (tensorComponents (K := K) (V := V)) := by
  intro t ht
  have heq : _root_.SymmetricAlgebra.algHom K V t =
      _root_.SymmetricAlgebra.algHom K V 0 := by simpa using ht
  have hi : t ∈ commutatorIdeal K V := by
    simpa using (D05.M15.Symmetric.quotient_eq_iff t 0).mp heq
  apply _root_.DirectSum.ext
  intro p
  change (adjacentRelations K V p).mkQ
    (_root_.TensorAlgebra.equivDirectSum t p) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (D05.M15.Symmetric.relation_component t
      (D05.M15.Symmetric.ideal_le_homogeneousRelations t hi) p)

/-- The homogeneous component map on the actual symmetric algebra quotient. -/
def components : symmetricAlgebra K V →ₗ[K]
    _root_.DirectSum ℕ (symmetricPower K V) where
  toFun := Quotient.lift (tensorComponents (K := K) (V := V)) (by
    intro a b hab
    have hz : tensorComponents (K := K) (V := V) (a-b) = 0 := by
      apply tensorComponents_kills
      change _root_.SymmetricAlgebra.algHom K V (a-b) = 0
      rw [map_sub, sub_eq_zero]
      exact Quotient.sound hab
    have hh := map_sub (tensorComponents (K := K) (V := V)) a b
    rw [hz] at hh
    exact (sub_eq_zero.mp hh.symm))
  map_add' a b := by
    obtain ⟨a,rfl⟩ := _root_.SymmetricAlgebra.algHom_surjective K V a
    obtain ⟨b,rfl⟩ := _root_.SymmetricAlgebra.algHom_surjective K V b
    exact map_add (tensorComponents (K := K) (V := V)) a b
  map_smul' c a := by
    obtain ⟨a,rfl⟩ := _root_.SymmetricAlgebra.algHom_surjective K V a
    exact map_smul (tensorComponents (K := K) (V := V)) c a

@[simp] theorem components_inclusion (p : ℕ) (q : symmetricPower K V p) :
    components (K := K) (V := V) (powerInclusion (K := K) (V := V) p q) =
      _root_.DirectSum.lof K ℕ _ p q := by
  obtain ⟨t,rfl⟩ := (adjacentRelations K V p).mkQ_surjective q
  change _root_.DirectSum.lmap _ (_root_.TensorAlgebra.equivDirectSum
    (TensorPower.toTensorAlgebra t)) = _
  rw [D05.M15.TensorAlgebra.direct_sum_inclusion, _root_.DirectSum.lmap_lof]

/-- Recombine the two homogeneous component maps into a bidegree component map. -/
def tensorBicomponents : (symmetricAlgebra K V ⊗[K] symmetricAlgebra K W) →ₗ[K]
    _root_.DirectSum (ℕ × ℕ)
      (fun ij => symmetricPower K V ij.1 ⊗[K] symmetricPower K W ij.2) :=
  (TensorProduct.directSum K K (symmetricPower K V) (symmetricPower K W)).toLinearMap.comp
    (TensorProduct.map (components (K := K) (V := V)) (components (K := K) (V := W)))

@[simp] theorem tensorBicomponents_tmul (i j : ℕ)
    (a : symmetricPower K V i) (b : symmetricPower K W j) :
    tensorBicomponents (K := K) (V := V) (W := W)
      (powerInclusion (K := K) (V := V) i a ⊗ₜ[K] powerInclusion (K := K) (V := W) j b) =
      _root_.DirectSum.lof K (ℕ × ℕ) _ (i,j) (a ⊗ₜ[K] b) := by
  simp [tensorBicomponents]

/-- Discard bidegrees of total degree different from p. -/
def selectDegree (p : ℕ) :
    (_root_.DirectSum (ℕ × ℕ)
      (fun ij => symmetricPower K V ij.1 ⊗[K] symmetricPower K W ij.2)) →ₗ[K]
        DegreeSum K V W p :=
  _root_.DirectSum.toModule K _ _ (fun ij =>
    if h : ij.1 + ij.2 = p then _root_.DirectSum.lof K (DegreePairs p)
      (fun ij => symmetricPower K V ij.val.1 ⊗[K] symmetricPower K W ij.val.2) ⟨ij,h⟩ else 0)

theorem degreeInclusion_split (p : ℕ) :
    ((selectDegree p).comp (tensorBicomponents (K := K) (V := V) (W := W))).comp
      (degreeInclusion K V W p) = LinearMap.id := by
  apply _root_.DirectSum.linearMap_ext
  intro ij
  apply TensorProduct.ext'
  intro a b
  simp [degreeInclusion, selectDegree, ij.property]

theorem degreeInclusion_injective (p : ℕ) :
    Function.Injective (degreeInclusion K V W p) := by
  have h : Function.LeftInverse
      ((selectDegree p).comp (tensorBicomponents (K := K) (V := V) (W := W)))
      (degreeInclusion K V W p) := fun x =>
    DFunLike.congr_fun (degreeInclusion_split (K := K) (V := V) (W := W) p) x
  exact h.injective

/-- Products of two homogeneous quotient images have the sum of their degrees. -/
theorem inclusion_mul_mem (i j : ℕ) (a : symmetricAlgebra K V)
    (ha : a ∈ LinearMap.range (powerInclusion (K := K) (V := V) i))
    (b : symmetricAlgebra K V)
    (hb : b ∈ LinearMap.range (powerInclusion (K := K) (V := V) j)) :
    a*b ∈ LinearMap.range (powerInclusion (K := K) (V := V) (i+j)) := by
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨b,rfl⟩ := hb
  obtain ⟨x,rfl⟩ := (adjacentRelations K V i).mkQ_surjective a
  obtain ⟨y,rfl⟩ := (adjacentRelations K V j).mkQ_surjective b
  refine ⟨(adjacentRelations K V (i+j)).mkQ
    ((TensorPower.mulEquiv (R := K) (M := V)) (x ⊗ₜ[K] y)), ?_⟩
  change _root_.SymmetricAlgebra.algHom K V (TensorPower.toTensorAlgebra _) =
    _root_.SymmetricAlgebra.algHom K V (TensorPower.toTensorAlgebra x) *
      _root_.SymmetricAlgebra.algHom K V (TensorPower.toTensorAlgebra y)
  rw [← TensorPower.gMul_def, TensorPower.toTensorAlgebra_gMul, map_mul]

/-- Ordinary finite products of generators, with their actual cardinal degree. -/
theorem generator_prod_mem {ι : Type*} (s : Finset ι) (x : ι → V) :
    (∏ i ∈ s, _root_.SymmetricAlgebra.ι K V (x i)) ∈
      LinearMap.range (powerInclusion (K := K) (V := V) s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨elementary K V 0 Fin.elim0, ?_⟩
    simpa using D05.M15.SymmetricBasis.inclusion_elementary (K := K) (V := V) 0 Fin.elim0
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 : _root_.SymmetricAlgebra.ι K V (x a) ∈
        LinearMap.range (powerInclusion (K := K) (V := V) 1) := by
      refine ⟨elementary K V 1 (fun _ => x a), ?_⟩
      simpa using D05.M15.SymmetricBasis.inclusion_elementary (K := K) 1 (fun _ => x a)
    have h := inclusion_mul_mem 1 s.card _ h1 _ ih
    rw [Nat.add_comm 1 s.card] at h
    exact h

/-- Applying a linear map to all generators preserves each degree. -/
theorem induced_mem (f : V →ₗ[K] W) (p : ℕ) (a : symmetricPower K V p) :
    _root_.SymmetricAlgebra.lift ((_root_.SymmetricAlgebra.ι K W).comp f)
      (powerInclusion (K := K) (V := V) p a) ∈
        LinearMap.range (powerInclusion (K := K) (V := W) p) := by
  obtain ⟨t,rfl⟩ := (adjacentRelations K V p).mkQ_surjective a
  change _root_.SymmetricAlgebra.lift _ (homogeneousMap K V p t) ∈ _
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, map_smul]
    apply Submodule.smul_mem
    rw [D05.M15.Symmetric.homogeneousMap_tprod, map_prod]
    refine ⟨elementary K W p (fun i => f (x i)), ?_⟩
    rw [D05.M15.SymmetricBasis.inclusion_elementary]
    simp
  | add t u ht hu =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ht hu

/-- The inverse algebra map takes every total-degree-p tensor sum to degree p. -/
theorem backward_degree_mem (p : ℕ) (z : DegreeSum K V W p) :
    backward K V W (degreeInclusion K V W p z) ∈
      LinearMap.range (powerInclusion (K := K) (V := V × W) p) := by
  induction z using _root_.DirectSum.induction_on with
  | zero => simp
  | of ij z =>
    rw [← _root_.DirectSum.lof_eq_of K]
    simp only [degreeInclusion, _root_.DirectSum.toModule_lof]
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      rw [TensorProduct.map_tmul, backward_pure]
      have h := inclusion_mul_mem ij.val.1 ij.val.2 _
        (induced_mem (LinearMap.inl K V W) ij.val.1 a) _
        (induced_mem (LinearMap.inr K V W) ij.val.2 b)
      rw [ij.property] at h
      exact h
    | add x y hx hy =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hx hy
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

/-- Subset expansion of a product of v⊗1+1⊗w, with no binomial divisions. -/
theorem forward_degree_mem (p : ℕ) (q : symmetricPower K (V × W) p) :
    forward K V W (powerInclusion (K := K) (V := V × W) p q) ∈
      LinearMap.range (degreeInclusion K V W p) := by
  classical
  obtain ⟨t,rfl⟩ := (adjacentRelations K (V × W) p).mkQ_surjective q
  change forward K V W (homogeneousMap K (V × W) p t) ∈ _
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, map_smul]
    apply Submodule.smul_mem
    rw [D05.M15.Symmetric.homogeneousMap_tprod, map_prod]
    have hf (u : V × W) : forward K V W (_root_.SymmetricAlgebra.ι K (V × W) u) =
        (_root_.SymmetricAlgebra.ι K V u.1) ⊗ₜ[K] 1 +
          1 ⊗ₜ[K] (_root_.SymmetricAlgebra.ι K W u.2) := forward_ι u.1 u.2
    simp only [hf]
    rw [Finset.prod_add]
    apply Submodule.sum_mem
    intro s hs
    have hsub : s ⊆ Finset.univ := Finset.mem_powerset.mp hs
    have hcard : s.card + (Finset.univ \ s).card = p := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin]
      have : s.card ≤ p := by simpa using Finset.card_le_card hsub
      omega
    obtain ⟨a,ha⟩ := generator_prod_mem (K := K) s (fun i => (x i).1)
    obtain ⟨b,hb⟩ := generator_prod_mem (K := K) (Finset.univ \ s) (fun i => (x i).2)
    refine ⟨_root_.DirectSum.lof K (DegreePairs p) _
      ⟨(s.card, (Finset.univ \ s).card), hcard⟩ (a ⊗ₜ[K] b), ?_⟩
    simp only [degreeInclusion, _root_.DirectSum.toModule_lof, TensorProduct.map_tmul]
    rw [ha, hb]
    have hl : (∏ i ∈ s, _root_.SymmetricAlgebra.ι K V (x i).1) ⊗ₜ[K]
        (1 : symmetricAlgebra K W) =
        ∏ i ∈ s, (_root_.SymmetricAlgebra.ι K V (x i).1) ⊗ₜ[K] 1 := by
      exact map_prod (Algebra.TensorProduct.includeLeft :
        symmetricAlgebra K V →ₐ[K] symmetricAlgebra K V ⊗[K] symmetricAlgebra K W) _ _
    have hr : (1 : symmetricAlgebra K V) ⊗ₜ[K]
        (∏ i ∈ Finset.univ \ s, _root_.SymmetricAlgebra.ι K W (x i).2) =
        ∏ i ∈ Finset.univ \ s, (1 : symmetricAlgebra K V) ⊗ₜ[K]
          (_root_.SymmetricAlgebra.ι K W (x i).2) := by
      exact map_prod (Algebra.TensorProduct.includeRight :
        symmetricAlgebra K W →ₐ[K] symmetricAlgebra K V ⊗[K] symmetricAlgebra K W) _ _
    rw [← hl, ← hr, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add t u ht hu =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ht hu

/-- The degree restriction is obtained from the algebra map by extracting its
bidegree components. No basis is chosen. -/
def degreeMap (p : ℕ) : symmetricPower K (V × W) p →ₗ[K] DegreeSum K V W p :=
  ((selectDegree p).comp tensorBicomponents).comp
    ((forward K V W).toLinearMap.comp (powerInclusion p))

theorem degreeMap_inclusion (p : ℕ) (q : symmetricPower K (V × W) p) :
    degreeInclusion K V W p (degreeMap p q) =
      forward K V W (powerInclusion (K := K) (V := V × W) p q) := by
  obtain ⟨z,hz⟩ := forward_degree_mem (K := K) (V := V) (W := W) p q
  change degreeInclusion K V W p
    (((selectDegree p).comp tensorBicomponents)
      (forward K V W (powerInclusion (K := K) (V := V × W) p q))) = _
  rw [← hz]
  rw [show ((selectDegree p).comp tensorBicomponents) (degreeInclusion K V W p z) = z from
    DFunLike.congr_fun (degreeInclusion_split p) z]

theorem degreeMap_bijective (p : ℕ) :
    Function.Bijective (degreeMap (K := K) (V := V) (W := W) p) := by
  constructor
  · intro a b hab
    apply D05.M15.SymmetricBasis.inclusion_injective p
    apply (algebraEquiv (K := K) (V := V) (W := W)).injective
    change forward K V W (powerInclusion (K := K) (V := V × W) p a) =
      forward K V W (powerInclusion (K := K) (V := V × W) p b)
    rw [← degreeMap_inclusion p a, ← degreeMap_inclusion p b, hab]
  · intro z
    obtain ⟨q,hq⟩ := backward_degree_mem (K := K) (V := V) (W := W) p z
    refine ⟨q, degreeInclusion_injective p ?_⟩
    rw [degreeMap_inclusion, hq]
    exact DFunLike.congr_fun (forward_backward (K := K) (V := V) (W := W))
      (degreeInclusion K V W p z)

/-- The canonical isomorphism of degree-p quotient spaces. -/
def degreeEquiv (p : ℕ) : symmetricPower K (V × W) p ≃ₗ[K] DegreeSum K V W p :=
  LinearEquiv.ofBijective (degreeMap p) (degreeMap_bijective p)

end Degree

theorem degree_decomposition : Specs.D05.M15.SymmetricDirectSum.degree_decomposition := by
  intro K V W _ _ _ _ _ p
  exact ⟨degreeInclusion_injective p, degreeEquiv p, degreeMap_inclusion p⟩

end D05.M15.SymmetricDirectSum
