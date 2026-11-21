import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.Algebra
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Grading
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.FinCases

/-! The spans of the adjacent-swap differences assemble into the commutator ideal.
Projecting that ideal to each tensor degree computes the kernel of the quotient there
and proves injectivity of recomposition from the symmetric degree submodules. -/

namespace Alg01SymmetricWitt.Symmetric.Grading

open scoped DirectSum TensorProduct
open Alg01SymmetricWitt.Symmetric.Algebra

abbrev adjacentRelations := Specs.Alg01SymmetricWitt.Symmetric.Grading.adjacentRelations
abbrev permutationRelations := Specs.Alg01SymmetricWitt.Symmetric.Grading.permutationRelations
abbrev degreeQuotientMap := Specs.Alg01SymmetricWitt.Symmetric.Grading.degreeQuotientMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Adjacent transpositions generate all permutation symmetries of functions on finite tuples. -/
theorem invariant_of_adjacent {V W : Type*} (n : ℕ) (f : (Fin n → V) → W)
    (h : ∀ (x : Fin n → V) (i j : Fin n), j.val = i.val + 1 →
      f (x ∘ Equiv.swap i j) = f x) :
    ∀ (x : Fin n → V) (σ : Equiv.Perm (Fin n)), f (x ∘ σ) = f x := by
  cases n with
  | zero =>
    intro x σ
    exact congrArg f (funext fun i => Fin.elim0 i)
  | succ n =>
    let S : Submonoid (Equiv.Perm (Fin (n + 1))) := {
      carrier := {σ | ∀ x : Fin (n + 1) → V, f (x ∘ σ) = f x}
      one_mem' := fun _ => rfl
      mul_mem' := by
        intro σ τ hσ hτ x
        change f ((x ∘ σ) ∘ τ) = f x
        exact (hτ (x ∘ σ)).trans (hσ x) }
    have hS : Submonoid.closure
        (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ≤ S := by
      apply Submonoid.closure_le.mpr
      rintro _ ⟨i, rfl⟩ x
      exact h x i.castSucc i.succ rfl
    rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hS
    intro x σ
    exact hS (Submonoid.mem_top σ) x

private theorem perm_difference_mem (n : ℕ) (x : Fin n → M) (σ : Equiv.Perm (Fin n)) :
    PiTensorProduct.tprod R x - PiTensorProduct.tprod R (x ∘ σ) ∈ adjacentRelations R M n := by
  let S := adjacentRelations R M n
  let f : (Fin n → M) → (TensorPower R n M ⧸ S) := fun y => S.mkQ (PiTensorProduct.tprod R y)
  have hadj (y : Fin n → M) (i j : Fin n) (hij : j.val = i.val + 1) :
      f (y ∘ Equiv.swap i j) = f y := by
    apply (Submodule.Quotient.eq S).2
    rw [← neg_sub]
    exact S.neg_mem (Submodule.subset_span ⟨y, i, j, hij, rfl⟩)
  exact (Submodule.Quotient.eq S).1 ((invariant_of_adjacent n f hadj x σ).symm)

variable (R M) in
theorem adjacent_eq_permutation (n : ℕ) :
    adjacentRelations R M n = permutationRelations R M n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, i, j, _, rfl⟩
    exact Submodule.subset_span ⟨x, Equiv.swap i j, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, σ, rfl⟩
    exact perm_difference_mem n x σ

private def blockPerm {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m + n)) :=
  finSumFinEquiv.symm.trans ((σ.sumCongr τ).trans finSumFinEquiv)

private theorem append_blockPerm {V : Type*} {m n : ℕ} (x : Fin m → V) (y : Fin n → V)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Fin.append (x ∘ σ) (y ∘ τ) = Fin.append x y ∘ blockPerm σ τ := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [blockPerm, Function.comp_def]
  · intro j
    simp [blockPerm, Function.comp_def]

private theorem tensor_mul_left_mem {m n : ℕ} (x : Fin m → M) (r : TensorPower R n M)
    (hr : r ∈ adjacentRelations R M n) :
    GradedMonoid.GMul.mul (A := fun i => TensorPower R i M) (PiTensorProduct.tprod R x : TensorPower R m M) r ∈
      adjacentRelations R M (m + n) := by
  let f : TensorPower R n M →ₗ[R] TensorPower R (m + n) M :=
    ((TensorProduct.mk R _ _).compr₂ TensorPower.mulEquiv.toLinearMap) (PiTensorProduct.tprod R x)
  change f r ∈ adjacentRelations R M (m + n)
  rw [adjacent_eq_permutation] at hr
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨y, σ, rfl⟩ := hr
    rw [map_sub]
    change GradedMonoid.GMul.mul (A := fun i => TensorPower R i M) (PiTensorProduct.tprod R x : TensorPower R m M)
        (PiTensorProduct.tprod R y : TensorPower R n M) -
      GradedMonoid.GMul.mul (A := fun i => TensorPower R i M) (PiTensorProduct.tprod R x : TensorPower R m M)
        (PiTensorProduct.tprod R (y ∘ σ) : TensorPower R n M) ∈ _
    rw [TensorPower.tprod_mul_tprod, TensorPower.tprod_mul_tprod,
      show Fin.append x (y ∘ σ) = Fin.append x y ∘ blockPerm (Equiv.refl _) σ from
        append_blockPerm x y (Equiv.refl _) σ]
    exact perm_difference_mem (m + n) _ _
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

private theorem tensor_mul_right_mem {m n : ℕ} (y : Fin n → M) (r : TensorPower R m M)
    (hr : r ∈ adjacentRelations R M m) :
    GradedMonoid.GMul.mul (A := fun i => TensorPower R i M) r (PiTensorProduct.tprod R y : TensorPower R n M) ∈
      adjacentRelations R M (m + n) := by
  let f : TensorPower R m M →ₗ[R] TensorPower R (m + n) M :=
    ((TensorProduct.mk R _ _).compr₂ TensorPower.mulEquiv.toLinearMap).flip (PiTensorProduct.tprod R y)
  change f r ∈ adjacentRelations R M (m + n)
  rw [adjacent_eq_permutation] at hr
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨x, σ, rfl⟩ := hr
    rw [map_sub]
    change GradedMonoid.GMul.mul (A := fun i => TensorPower R i M) (PiTensorProduct.tprod R x : TensorPower R m M)
        (PiTensorProduct.tprod R y : TensorPower R n M) -
      GradedMonoid.GMul.mul (A := fun i => TensorPower R i M) (PiTensorProduct.tprod R (x ∘ σ) : TensorPower R m M)
        (PiTensorProduct.tprod R y : TensorPower R n M) ∈ _
    rw [TensorPower.tprod_mul_tprod, TensorPower.tprod_mul_tprod,
      show Fin.append (x ∘ σ) y = Fin.append x y ∘ blockPerm σ (Equiv.refl _) from
        append_blockPerm x y σ (Equiv.refl _)]
    exact perm_difference_mem (m + n) _ _
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

private theorem directSum_inclusion (n : ℕ) (t : TensorPower R n M) :
    TensorAlgebra.equivDirectSum (TensorPower.toTensorAlgebra t) =
      DirectSum.of (fun j => TensorPower R j M) n t := by
  have h : (TensorAlgebra.equivDirectSum (R := R) (M := M)).toLinearMap.comp
      TensorPower.toTensorAlgebra = DirectSum.lof R ℕ (fun j => TensorPower R j M) n := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      TensorPower.toTensorAlgebra_tprod, DirectSum.lof_eq_of, AlgEquiv.toLinearMap_apply,
      TensorAlgebra.equivDirectSum_apply] using TensorAlgebra.toDirectSum_tensorPower_tprod x
  simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, DirectSum.lof_eq_of] using
    LinearMap.congr_fun h t

private theorem word_induction {P : TensorAlgebra R M → Prop}
    (word : ∀ n (x : Fin n → M), P (TensorPower.toTensorAlgebra (PiTensorProduct.tprod R x)))
    (zero : P 0) (add : ∀ a b, P a → P b → P (a + b))
    (smul : ∀ (c : R) a, P a → P (c • a)) (a : TensorAlgebra R M) : P a := by
  rw [← TensorAlgebra.equivDirectSum.symm_apply_apply a]
  induction TensorAlgebra.equivDirectSum a using DirectSum.induction_on with
  | zero => simpa only [map_zero] using zero
  | add a b ha hb => simpa only [map_add] using add _ _ ha hb
  | of n t =>
    rw [← directSum_inclusion, AlgEquiv.symm_apply_apply]
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c x => rw [map_smul]; exact smul c _ (word n x)
    | add x y hx hy => rw [map_add]; exact add _ _ hx hy

private def homogeneousRelations : Submodule R (TensorAlgebra R M) :=
  Submodule.span R {t | ∃ (n : ℕ) (r : TensorPower R n M),
    r ∈ adjacentRelations R M n ∧ t = TensorPower.toTensorAlgebra r}

private theorem homogeneousRelation_mem (n : ℕ) (r : TensorPower R n M)
    (hr : r ∈ adjacentRelations R M n) : TensorPower.toTensorAlgebra r ∈ homogeneousRelations :=
  Submodule.subset_span ⟨n, r, hr, rfl⟩

private theorem homogeneousRelations_mul_left (a t : TensorAlgebra R M)
    (ht : t ∈ homogeneousRelations) : a * t ∈ homogeneousRelations := by
  induction a using word_induction with
  | word m x =>
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨n, r, hr, rfl⟩ := ht
      rw [← TensorPower.toTensorAlgebra_gMul]
      exact homogeneousRelation_mem (m + n) _ (tensor_mul_left_mem x r hr)
    | zero => simp
    | add t u _ _ ht hu => simpa only [mul_add] using Submodule.add_mem _ ht hu
    | smul c t _ ht => simpa only [mul_smul_comm] using Submodule.smul_mem _ c ht
  | zero => simp
  | add a b ha hb => simpa only [add_mul] using Submodule.add_mem _ ha hb
  | smul c a ha => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ha

private theorem homogeneousRelations_mul_right (a t : TensorAlgebra R M)
    (ht : t ∈ homogeneousRelations) : t * a ∈ homogeneousRelations := by
  induction a using word_induction with
  | word n y =>
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨m, r, hr, rfl⟩ := ht
      rw [← TensorPower.toTensorAlgebra_gMul]
      exact homogeneousRelation_mem (m + n) _ (tensor_mul_right_mem y r hr)
    | zero => simp
    | add t u _ _ ht hu => simpa only [add_mul] using Submodule.add_mem _ ht hu
    | smul c t _ ht => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ht
  | zero => simp
  | add a b ha hb => simpa only [mul_add] using Submodule.add_mem _ ha hb
  | smul c a ha => simpa only [mul_smul_comm] using Submodule.smul_mem _ c ha

private def homogeneousRelationsIdeal : TwoSidedIdeal (TensorAlgebra R M) :=
  TwoSidedIdeal.mk' (homogeneousRelations : Submodule R (TensorAlgebra R M))
    (Submodule.zero_mem _) (Submodule.add_mem _) (Submodule.neg_mem _)
    (fun {_ _} h => homogeneousRelations_mul_left _ _ h)
    (fun {_ _} h => homogeneousRelations_mul_right _ _ h)

private theorem ideal_le_relations {t : TensorAlgebra R M}
    (ht : t ∈ commutatorIdeal R M) : t ∈ homogeneousRelations := by
  have hle : commutatorIdeal R M ≤ homogeneousRelationsIdeal := by
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    let x : Fin 2 → M := Fin.cons u (Fin.cons v Fin.elim0)
    have hs : x ∘ Equiv.swap 0 1 = Fin.cons v (Fin.cons u Fin.elim0) := by
      funext i
      fin_cases i <;> simp [x]
    have hh := homogeneousRelation_mem 2 _
      (perm_difference_mem (R := R) 2 x (Equiv.swap 0 1))
    rw [map_sub, TensorPower.toTensorAlgebra_tprod, TensorPower.toTensorAlgebra_tprod, hs,
      TensorAlgebra.tprod_apply, TensorAlgebra.tprod_apply] at hh
    simpa [x, List.ofFn_succ, homogeneousRelationsIdeal] using hh
  exact (TwoSidedIdeal.mem_mk' ..).mp (hle ht)

private theorem relation_component {t : TensorAlgebra R M}
    (ht : t ∈ homogeneousRelations) (n : ℕ) :
    TensorAlgebra.equivDirectSum t n ∈ adjacentRelations R M n := by
  let π : TensorAlgebra R M →ₗ[R] TensorPower R n M :=
    (DirectSum.component R ℕ (fun j => TensorPower R j M) n).comp
      TensorAlgebra.equivDirectSum.toLinearMap
  change π t ∈ adjacentRelations R M n
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨j, r, hr, rfl⟩ := ht
    change TensorAlgebra.equivDirectSum (TensorPower.toTensorAlgebra r) n ∈ _
    rw [directSum_inclusion]
    by_cases h : j = n
    · subst j
      simpa only [DirectSum.of_eq_same] using hr
    · simpa only [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)] using
        (adjacentRelations R M n).zero_mem
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

@[simp] theorem degreeMap_tprod (n : ℕ) (x : Fin n → M) :
    degreeMap R M n (PiTensorProduct.tprod R x) = ∏ i, SymmetricAlgebra.ι R M (x i) :=
  pureProductCoe R M n x

private theorem relations_le_degreeKernel (n : ℕ) :
    adjacentRelations R M n ≤ LinearMap.ker (degreeMap R M n) := by
  rw [adjacent_eq_permutation]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, σ, rfl⟩
  apply LinearMap.mem_ker.mpr
  rw [map_sub, degreeMap_tprod, degreeMap_tprod, sub_eq_zero]
  exact (Equiv.prod_comp σ (fun i => SymmetricAlgebra.ι R M (x i))).symm

private theorem mem_commutatorIdeal_iff {t : TensorAlgebra R M} :
    t ∈ commutatorIdeal R M ↔ SymmetricAlgebra.algHom R M t = 0 := by
  rw [← (quotientKernel R M).2, TwoSidedIdeal.mem_ker]

variable (R M) in
theorem idealHomogeneous (t : TensorAlgebra R M) (ht : t ∈ commutatorIdeal R M)
    (n : ℕ) : TensorPower.toTensorAlgebra (TensorAlgebra.equivDirectSum t n) ∈
      commutatorIdeal R M :=
  mem_commutatorIdeal_iff.mpr
    (relations_le_degreeKernel n (relation_component (ideal_le_relations ht) n))

variable (R M) in
theorem degreeKernel (n : ℕ) : LinearMap.ker (degreeMap R M n) = adjacentRelations R M n := by
  apply le_antisymm _ (relations_le_degreeKernel n)
  intro t ht
  have h := relation_component (ideal_le_relations (mem_commutatorIdeal_iff.mpr ht)) n
  rwa [directSum_inclusion, DirectSum.of_eq_same] at h

variable (R M) in
theorem lowDegreeKernels :
    LinearMap.ker (degreeMap R M 0) = ⊥ ∧ LinearMap.ker (degreeMap R M 1) = ⊥ := by
  constructor <;> rw [degreeKernel] <;> apply le_bot_iff.mp <;> apply Submodule.span_le.mpr
  · rintro _ ⟨_, i, _, _, _⟩
    exact Fin.elim0 i
  · rintro _ ⟨_, i, j, hij, _⟩
    omega

variable (R M) in
/-- The isomorphism induced by the tensor-to-symmetric quotient in degree `n`. -/
noncomputable def degreeQuotientEquiv (n : ℕ) :
    (TensorPower R n M ⧸ adjacentRelations R M n) ≃ₗ[R] degree R M n :=
  (Submodule.quotEquivOfEq _ _ (degreeKernel R M n).symm).trans (degreeMap R M n).quotKerEquivRange

variable (R M) in
@[simp] theorem degreeQuotientEquiv_mkQ (n : ℕ) (t : TensorPower R n M) :
    degreeQuotientEquiv R M n ((adjacentRelations R M n).mkQ t) =
      degreeQuotientMap R M n t := by
  apply Subtype.ext
  exact (degreeMap R M n).quotKerEquivRange_apply_mk t

variable (R M) in
@[simp] theorem degreeQuotientEquiv_tprod (n : ℕ) (x : Fin n → M) :
    degreeQuotientEquiv R M n ((adjacentRelations R M n).mkQ (PiTensorProduct.tprod R x)) =
      pureProduct R M n x :=
  degreeQuotientEquiv_mkQ R M n _

variable (R M) in
theorem degreeQuotient (n : ℕ) :
    ∃ e : (TensorPower R n M ⧸ adjacentRelations R M n) ≃ₗ[R] degree R M n,
      ∀ t : TensorPower R n M, e ((adjacentRelations R M n).mkQ t) = degreeQuotientMap R M n t :=
  ⟨degreeQuotientEquiv R M n, degreeQuotientEquiv_mkQ R M n⟩

private theorem degreeGradedMonoid : SetLike.GradedMonoid (degree R M) where
  one_mem := ⟨GradedMonoid.GOne.one (A := fun i => TensorPower R i M), by
    change SymmetricAlgebra.algHom R M (TensorPower.toTensorAlgebra _) = 1
    rw [TensorPower.toTensorAlgebra_gOne, map_one]⟩
  mul_mem := by
    rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨GradedMonoid.GMul.mul (A := fun i => TensorPower R i M) a b, ?_⟩
    change SymmetricAlgebra.algHom R M (TensorPower.toTensorAlgebra _) =
      SymmetricAlgebra.algHom R M (TensorPower.toTensorAlgebra a) *
        SymmetricAlgebra.algHom R M (TensorPower.toTensorAlgebra b)
    rw [TensorPower.toTensorAlgebra_gMul, map_mul]

private theorem recompose_lmap (s : ⨁ i, TensorPower R i M) :
    DirectSum.coeLinearMap (degree R M)
      (DirectSum.lmap (degreeQuotientMap R M) s) =
      SymmetricAlgebra.algHom R M (TensorAlgebra.equivDirectSum.symm s) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | of n t =>
    rw [DirectSum.lmap_of, DirectSum.coeLinearMap_of, ← directSum_inclusion,
      AlgEquiv.symm_apply_apply]
    rfl

private theorem degreeIsInternal : DirectSum.IsInternal (degree R M) := by
  let recompose := DirectSum.coeLinearMap (degree R M)
  change Function.Bijective recompose
  constructor
  · intro x y hxy
    have hsurj := (DirectSum.lmap_surjective (degreeQuotientMap R M)).mpr
      (fun n => (degreeMap R M n).surjective_rangeRestrict)
    obtain ⟨s, rfl⟩ := hsurj x
    obtain ⟨t, rfl⟩ := hsurj y
    change DirectSum.coeLinearMap _ (DirectSum.lmap (degreeQuotientMap R M) s) =
      DirectSum.coeLinearMap _ (DirectSum.lmap (degreeQuotientMap R M) t) at hxy
    rw [recompose_lmap, recompose_lmap] at hxy
    have hJ : TensorAlgebra.equivDirectSum.symm s - TensorAlgebra.equivDirectSum.symm t ∈
        commutatorIdeal R M := by
      apply mem_commutatorIdeal_iff.mpr
      rw [map_sub, hxy, sub_self]
    ext n
    rw [DirectSum.lmap_apply, DirectSum.lmap_apply]
    change degreeMap R M n (s n) = degreeMap R M n (t n)
    have hn := relation_component (ideal_le_relations hJ) n
    let π : TensorAlgebra R M →ₗ[R] TensorPower R n M :=
      (DirectSum.component R ℕ (fun j => TensorPower R j M) n).comp
        TensorAlgebra.equivDirectSum.toLinearMap
    change π (TensorAlgebra.equivDirectSum.symm s - TensorAlgebra.equivDirectSum.symm t) ∈ _ at hn
    rw [map_sub] at hn
    change TensorAlgebra.equivDirectSum (TensorAlgebra.equivDirectSum.symm s) n -
      TensorAlgebra.equivDirectSum (TensorAlgebra.equivDirectSum.symm t) n ∈ _ at hn
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply] at hn
    have hz := LinearMap.mem_ker.mp (relations_le_degreeKernel n hn)
    rwa [map_sub, sub_eq_zero] at hz
  · intro z
    obtain ⟨t, rfl⟩ := (quotientKernel R M).1 z
    refine ⟨DirectSum.lmap (degreeQuotientMap R M)
      (TensorAlgebra.equivDirectSum t), ?_⟩
    change DirectSum.coeLinearMap _ (DirectSum.lmap (degreeQuotientMap R M) _) = _
    rw [recompose_lmap, AlgEquiv.symm_apply_apply]

variable (R M) in
/-- The canonical grading by the images of the tensor powers. -/
noncomputable instance gradedAlgebra : GradedAlgebra (degree R M) where
  toGradedMonoid := degreeGradedMonoid
  toDecomposition := degreeIsInternal.chooseDecomposition

variable (R M) in
theorem decompose_quotient (t : TensorAlgebra R M) :
    DirectSum.decomposeAlgEquiv (degree R M) (SymmetricAlgebra.algHom R M t) =
      DirectSum.lmap (degreeQuotientMap R M) (TensorAlgebra.equivDirectSum t) := by
  apply (degreeIsInternal (R := R) (M := M)).1
  change DirectSum.coeAddMonoidHom (degree R M)
    (DirectSum.decompose (degree R M) (SymmetricAlgebra.algHom R M t)) = _
  calc
    _ = SymmetricAlgebra.algHom R M t := DirectSum.Decomposition.left_inv _
    _ = _ := by
      change _ = DirectSum.coeLinearMap _ (DirectSum.lmap (degreeQuotientMap R M) _)
      rw [recompose_lmap, AlgEquiv.symm_apply_apply]

theorem grading : Specs.Alg01SymmetricWitt.Symmetric.Grading.grading := by
  intro R M _ _ _
  exact ⟨gradedAlgebra R M, decompose_quotient R M⟩

private theorem degreeMap_injective_of_ker_eq_bot (n : ℕ)
    (h : LinearMap.ker (degreeMap R M n) = ⊥) :
    Function.Injective (degreeMap R M n).rangeRestrict := by
  intro x y hxy
  exact (LinearMap.ker_eq_bot.mp h) (congrArg Subtype.val hxy)

variable (R M) in
/-- Scalar inclusion as an equivalence onto the degree-zero submodule. -/
noncomputable def degreeZeroEquiv : R ≃ₗ[R] degree R M 0 :=
  (TensorPower.algebraMap₀ (M := M)).trans (LinearEquiv.ofBijective
    (degreeMap R M 0).rangeRestrict
    ⟨degreeMap_injective_of_ker_eq_bot 0 (lowDegreeKernels R M).1,
      (degreeMap R M 0).surjective_rangeRestrict⟩)

variable (R M) in
@[simp] theorem degreeZeroEquiv_coe (r : R) :
    (degreeZeroEquiv R M r : SymmetricAlgebra R M) = algebraMap R _ r := by
  change SymmetricAlgebra.algHom R M (TensorPower.toTensorAlgebra (TensorPower.algebraMap₀ r)) =
    algebraMap R _ r
  rw [← TensorPower.galgebra_toFun_def, TensorPower.toTensorAlgebra_galgebra_toFun, AlgHom.commutes]

variable (R M) in
/-- Degree zero is canonically the base algebra. -/
noncomputable def degreeZeroAlgEquiv : R ≃ₐ[R] degree R M 0 := by
  let f := Algebra.ofId R (degree R M 0)
  have hf : (f : R → degree R M 0) = degreeZeroEquiv R M := by
    funext r
    apply Subtype.ext
    rw [degreeZeroEquiv_coe]
    exact SetLike.GradeZero.coe_algebraMap (degree R M) r
  apply AlgEquiv.ofBijective f
  rw [hf]
  exact (degreeZeroEquiv R M).bijective

variable (R M) in
@[simp] theorem degreeZeroAlgEquiv_coe (r : R) :
    (degreeZeroAlgEquiv R M r : SymmetricAlgebra R M) = algebraMap R _ r :=
  SetLike.GradeZero.coe_algebraMap (degree R M) r

theorem degreeZero : Specs.Alg01SymmetricWitt.Symmetric.Grading.degreeZero := by
  intro R M _ _ _
  exact ⟨gradedAlgebra R M, degreeZeroAlgEquiv R M, degreeZeroAlgEquiv_coe R M⟩

variable (R M) in
/-- Generator inclusion as an equivalence onto the degree-one submodule. -/
noncomputable def degreeOneEquiv : M ≃ₗ[R] degree R M 1 :=
  (PiTensorProduct.subsingletonEquiv (0 : Fin 1)).symm.trans (LinearEquiv.ofBijective
    (degreeMap R M 1).rangeRestrict
    ⟨degreeMap_injective_of_ker_eq_bot 1 (lowDegreeKernels R M).2,
      (degreeMap R M 1).surjective_rangeRestrict⟩)

variable (R M) in
@[simp] theorem degreeOneEquiv_coe (x : M) :
    (degreeOneEquiv R M x : SymmetricAlgebra R M) = SymmetricAlgebra.ι R M x := by
  change degreeMap R M 1 ((PiTensorProduct.subsingletonEquiv (0 : Fin 1)).symm x) = _
  rw [PiTensorProduct.subsingletonEquiv_symm_apply', degreeMap_tprod, Fin.prod_univ_one]

variable (R M) in
theorem degreeOne :
    ∃ e : M ≃ₗ[R] degree R M 1, ∀ m : M,
      (e m : SymmetricAlgebra R M) = SymmetricAlgebra.ι R M m :=
  ⟨degreeOneEquiv R M, degreeOneEquiv_coe R M⟩

end Alg01SymmetricWitt.Symmetric.Grading
