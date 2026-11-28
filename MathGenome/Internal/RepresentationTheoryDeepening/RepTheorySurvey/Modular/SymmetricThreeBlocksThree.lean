import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeBlocksThree
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.PrincipalBlockDefect
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SymmetricThreeModules
import Mathlib.GroupTheory.IndexNormal

namespace RepTheorySurvey.Modular.SymmetricThree

open scoped MonoidAlgebra

local notation "c" => threeCycle
local notation "t" => transposition

private theorem permutation_cases (g : Group) :
    g = 1 ∨ g = c ∨ g = c ^ 2 ∨ g = t ∨ g = c * t ∨ g = c ^ 2 * t :=
  (by decide : ∀ g : Group, g = 1 ∨ g = c ∨ g = c ^ 2 ∨
    g = t ∨ g = c * t ∨ g = c ^ 2 * t) g

private theorem conj_cycle_square : IsConj (c ^ 2) c := by
  rw [Equiv.Perm.isConj_iff_cycleType_eq]
  decide

private theorem conj_cycle_mul_swap : IsConj (c * t) t := by
  rw [Equiv.Perm.isConj_iff_cycleType_eq]
  decide

private theorem conj_cycle_sq_mul_swap : IsConj (c ^ 2 * t) t := by
  rw [Equiv.Perm.isConj_iff_cycleType_eq]
  decide

section GroupAlgebra

variable (k : Type*) [Field k]

/-- The sum over the cyclic subgroup of order three. -/
private noncomputable def cycleSum : k[Group] :=
  1 + MonoidAlgebra.of k Group c + MonoidAlgebra.of k Group (c ^ 2)

private theorem swap_commute_cycleSum :
    Commute (MonoidAlgebra.of k Group t) (cycleSum k) := by
  have h₁ : t * c = c ^ 2 * t := by decide
  have h₂ : t * c ^ 2 = c * t := by decide
  unfold Commute SemiconjBy cycleSum
  simp only [mul_add, add_mul, mul_one, one_mul, ← map_mul, h₁, h₂]
  rw [add_right_comm]

private theorem cycleSum_squared [CharP k 3] : cycleSum k * cycleSum k = 0 := by
  have h₁ : c ^ 2 * c = 1 := by decide
  have h₄ : c * c = c ^ 2 := (pow_two c).symm
  have hmul : cycleSum k * MonoidAlgebra.of k Group c = cycleSum k := by
    simp only [cycleSum, add_mul, one_mul, ← map_mul, h₁, h₄, map_one]
    abel
  have hpow : cycleSum k * MonoidAlgebra.of k Group (c ^ 2) = cycleSum k := by
    rw [pow_two, map_mul, ← mul_assoc, hmul, hmul]
  calc
    cycleSum k * cycleSum k = cycleSum k + cycleSum k + cycleSum k := by
      change cycleSum k * (1 + MonoidAlgebra.of k Group c +
        MonoidAlgebra.of k Group (c ^ 2)) = _
      rw [mul_add, mul_add, mul_one, hmul, hpow]
    _ = (3 : k) • cycleSum k := by
      rw [show (3 : k) = 1 + 1 + 1 by norm_num]
      simp only [add_smul, one_smul]
    _ = 0 := by rw [show (3 : k) = 0 from CharP.cast_eq_zero k 3, zero_smul]

private theorem augmentation_cycleSum [CharP k 3] :
    Specs.augmentation k Group (cycleSum k) = 0 := by
  simp only [cycleSum, Specs.augmentation, map_add, map_one, MonoidAlgebra.lift_of,
    MonoidHom.one_apply]
  rw [show (1 : k) + 1 + 1 = (3 : k) by norm_num]
  exact CharP.cast_eq_zero k 3

/-- A central element differs from its scalar part by a linear combination
of the sums over the two cosets of the order-three subgroup. -/
private theorem central_decomposition (z : Subalgebra.center k k[Group]) :
    let a := z.val.coeff 1 - z.val.coeff c
    let v := z.val.coeff c • (1 : k[Group]) + z.val.coeff t • MonoidAlgebra.of k Group t
    z.val = algebraMap k k[Group] a + cycleSum k * v := by
  dsimp
  have hcoeff (x y : Group) (h : IsConj x y) : z.val.coeff x = z.val.coeff y :=
    (GroupAlgebraCenter.mem_center_iff _).1 z.property _ _
      (ConjClasses.mk_eq_mk_iff_isConj.mpr h)
  have h₂ := hcoeff _ _ conj_cycle_square
  have h₃ := hcoeff _ _ conj_cycle_mul_swap
  have h₄ := hcoeff _ _ conj_cycle_sq_mul_swap
  simp only [mul_add, mul_smul_comm, mul_one, cycleSum, add_mul, one_mul, ← map_mul]
  ext g
  rcases permutation_cases g with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) [MonoidAlgebra.one_def, MonoidAlgebra.coeff_add, h₂, h₃, h₄]

private theorem central_idempotent_eq_zero_or_one [CharP k 3]
    (z : Subalgebra.center k k[Group]) (hz : IsIdempotentElem z.val) :
    z.val = 0 ∨ z.val = 1 := by
  let a := z.val.coeff 1 - z.val.coeff c
  let v := z.val.coeff c • (1 : k[Group]) + z.val.coeff t • MonoidAlgebra.of k Group t
  let n := cycleSum k * v
  have hrep : z.val = algebraMap k k[Group] a + n := central_decomposition k z
  have hcomm : Commute v (cycleSum k) :=
    ((Commute.one_left _).smul_left _).add_left ((swap_commute_cycleSum k).smul_left _)
  have hn : n * n = 0 := by
    change cycleSum k * v * (cycleSum k * v) = 0
    rw [← mul_assoc, mul_assoc (cycleSum k) v, hcomm.eq,
      ← mul_assoc (cycleSum k) (cycleSum k), cycleSum_squared, zero_mul, zero_mul]
  have haug : Specs.augmentation k Group z.val = a := by
    rw [hrep, map_add, AlgHom.commutes, Algebra.algebraMap_self_apply]
    simp [n, augmentation_cycleSum]
  have ha : IsIdempotentElem a := haug ▸ hz.map (Specs.augmentation k Group)
  rcases eq_zero_or_one_of_sq_eq_self (show a ^ 2 = a by rwa [pow_two]) with ha₀ | ha₁
  · left
    rw [ha₀, map_zero, zero_add] at hrep
    exact hz.eq.symm.trans (by rw [hrep, hn])
  · right
    rw [ha₁, map_one] at hrep
    have hcomplement : 1 - z.val = -n := by rw [hrep, sub_add_eq_sub_sub, sub_self, zero_sub]
    have hzero : 1 - z.val = 0 := hz.one_sub.eq.symm.trans (by
      rw [hcomplement, neg_mul_neg, hn])
    exact (sub_eq_zero.mp hzero).symm

end GroupAlgebra

private theorem cycle_card : Nat.card (Subgroup.zpowers c) = 3 :=
  (Nat.card_zpowers c).trans representative_orders.2.2

private theorem group_card : Nat.card Group = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem cycle_index : (Subgroup.zpowers c).index = 2 := by
  have h := (Subgroup.zpowers c).card_mul_index
  rw [cycle_card, group_card] at h
  omega

private noncomputable def cycleSylow : Sylow 3 Group :=
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  (IsPGroup.of_card (n := 1) (p := 3) (show Nat.card (Subgroup.zpowers c) = 3 ^ 1 from
    cycle_card)).toSylow (by
      rw [cycle_index]
      decide)

private theorem cycleSylow_subgroup : (cycleSylow : Subgroup Group) = Subgroup.zpowers c := rfl

private theorem sylow_three_eq (S : Sylow 3 Group) : S = cycleSylow := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hnormal : (cycleSylow : Subgroup Group).Normal := by
    rw [cycleSylow_subgroup]
    exact Subgroup.normal_of_index_eq_two cycle_index
  let := Sylow.unique_of_normal cycleSylow hnormal
  exact Subsingleton.elim _ _

/-- The unique block in characteristic three is principal and has the cyclic
Sylow subgroup generated by the three-cycle as its defect group. -/
theorem blocks_three : BlocksThreeSpec.principalAndDefect := by
  intro O _ _ _ K _ _ system
  let k := IsLocalRing.ResidueField O
  let : CharP k 3 := system.residueChar
  let : Fact (Nat.Prime 3) := ⟨system.prime⟩
  let b := principalBlock k Group
  have hb := principalBlock_belongs k Group
  have helem (d : BlockIdempotent k Group) : d.element = 1 :=
    (central_idempotent_eq_zero_or_one k d.val d.idempotent).resolve_left d.element_ne_zero
  refine ⟨b, hb, fun d => BlockIdempotent.element_injective
    ((helem d).trans (helem b).symm), cycleSylow, cycleSylow_subgroup, ?_, ?_⟩
  · change Nat.card (cycleSylow : Subgroup Group) = 3
    rw [cycleSylow_subgroup, cycle_card]
  · intro P
    rw [PrincipalBlockDefect.principal_block_defect_iff 3 b hb P]
    constructor
    · rintro ⟨S, rfl⟩
      rw [sylow_three_eq S]
    · rintro rfl
      exact ⟨cycleSylow, rfl⟩

end RepTheorySurvey.Modular.SymmetricThree
