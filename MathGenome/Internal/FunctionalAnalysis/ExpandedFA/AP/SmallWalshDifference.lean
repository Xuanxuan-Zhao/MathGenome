import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.WalshBlocks
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.SmallWalshDifference
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-! The proof uses the exact discrete squared sum, coordinate symmetry, and
binomial bounds on the sizes of Hamming spheres. This avoids the coefficient
integral in the source while retaining its exact norm and extremizers. -/

noncomputable section
namespace ExpandedFA.AP.SmallWalshDifference
open ExpandedFA.AP.Walsh
open ExpandedFA.AP.WalshBlocks
open scoped BigOperators

/-- Coordinates at which a cube point is one. -/
def support (n : ℕ) (a : Cube n) : Finset (Fin (2 * n)) :=
  Finset.univ.filter (fun j => a j = true)

@[simp] lemma mem_support (n : ℕ) (a : Cube n) (j : Fin (2 * n)) :
    j ∈ support n a ↔ a j = true := by simp [support]

/-- A subset regarded as a Boolean cube point. -/
def point (n : ℕ) (S : Finset (Fin (2 * n))) : Cube n :=
  fun j => decide (j ∈ S)

@[simp] lemma support_point (n : ℕ) (S : Finset (Fin (2 * n))) :
    support n (point n S) = S := by ext j; simp [point]

@[simp] lemma point_support (n : ℕ) (a : Cube n) :
    point n (support n a) = a := by
  funext j
  simp [point]

lemma point_injective (n : ℕ) : Function.Injective (point n) := by
  intro S T h
  simpa using congrArg (support n) h

lemma levelSum_permute (n r : ℕ) (σ : Equiv.Perm (Fin (2 * n))) (a : Cube n) :
    levelSum n r (fun j => a (σ j)) = levelSum n r a := by
  simp only [levelSum, Finset.sum_apply, character_permute]
  apply Finset.sum_bij (fun S _ => S.map σ.toEmbedding)
  · intro S hS
    simpa [level, Finset.mem_powersetCard] using hS
  · intro S hS T hT h
    exact Finset.map_injective _ h
  · intro T hT
    refine ⟨T.map σ.symm.toEmbedding, ?_, ?_⟩
    · simpa [level, Finset.mem_powersetCard] using hT
    · ext j; simp
  · intro S hS; rfl

lemma difference_permute (n : ℕ) (σ : Equiv.Perm (Fin (2 * n))) (a : Cube n) :
    difference n (fun j => a (σ j)) = difference n a := by
  simp only [difference, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, levelSum_permute]

lemma difference_eq_of_support_card_eq (n : ℕ) (a b : Cube n)
    (hab : (support n a).card = (support n b).card) :
    difference n a = difference n b := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq (support n a) (support n b) hab
  have he : (fun j => b (σ j)) = a := by
    funext j
    have hmem : σ j ∈ support n b ↔ j ∈ support n a := by
      rw [← hσ]; simp
    simpa using hmem
  rw [← he]
  exact difference_permute n σ b

lemma character_sq (n : ℕ) (S : Finset (Fin (2 * n))) (a : Cube n) :
    character n S a * character n S a = 1 := by
  unfold character
  rw [← mul_pow]
  norm_num

lemma character_compl (n : ℕ) (S : Finset (Fin (2 * n))) (a : Cube n) :
    character n Sᶜ a = character n Finset.univ a * character n S a := by
  have hp : character n S a * character n Sᶜ a = character n Finset.univ a := by
    simpa only [character_product] using
      Finset.prod_mul_prod_compl S (fun j => bitSign (a j))
  rw [← hp]
  symm
  calc
    character n S a * character n Sᶜ a * character n S a =
        character n Sᶜ a * (character n S a * character n S a) := by ring
    _ = character n Sᶜ a := by rw [character_sq, mul_one]

lemma levelSum_compl (n r : ℕ) (hr : r ≤ 2 * n) (a : Cube n) :
    levelSum n (2 * n - r) a = character n Finset.univ a * levelSum n r a := by
  simp only [levelSum, Finset.sum_apply, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun S _ => Sᶜ)
  · intro S hS
    simp only [level, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS ⊢
    simp [Finset.card_compl, hS]
  · intro S hS T hT h
    simpa using congrArg (fun U : Finset (Fin (2 * n)) => Uᶜ) h
  · intro T hT
    refine ⟨Tᶜ, ?_, by simp⟩
    simp only [level, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hT ⊢
    simp [Finset.card_compl, hT, Nat.sub_sub_self hr]
  · intro S hS
    exact (character_compl n S a).symm

lemma character_univ (n : ℕ) (a : Cube n) :
    character n Finset.univ a = (-1 : ℝ) ^ (support n a).card := by
  unfold character
  congr 1
  simp only [support, Finset.card_filter]

lemma difference_of_even (n : ℕ) (hn : 2 ≤ n) (a : Cube n)
    (ha : Even (support n a).card) : difference n a = 0 := by
  have hU : character n Finset.univ a = 1 := by
    rw [character_univ]
    exact ha.neg_one_pow
  have hc := levelSum_compl n (n - 1) (by omega) a
  rw [show 2 * n - (n - 1) = n + 1 by omega, hU, one_mul] at hc
  simp [difference, hc]

lemma levelSum_pair (n r s : ℕ) :
    (∑ a : Cube n, levelSum n r a * levelSum n s a) =
      if r = s then (Fintype.card (Cube n) : ℝ) * (level n r).card else 0 := by
  simp only [levelSum, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ), character_pair_sum]
  by_cases hrs : r = s
  · subst s
    simp [mul_comm]
  · have hne : ∀ S ∈ level n r, ∀ T ∈ level n s, S ≠ T := by
      intro S hS T hT h
      subst T
      have h1 := (Finset.mem_powersetCard.mp hS).2
      have h2 := (Finset.mem_powersetCard.mp hT).2
      exact hrs (h1.symm.trans h2)
    rw [if_neg hrs]
    apply Finset.sum_eq_zero
    intro S hS
    apply Finset.sum_eq_zero
    intro T hT
    simp [hne T hT S hS]

lemma difference_energy (n : ℕ) (hn : 2 ≤ n) :
    (∑ a : Cube n, (difference n a) ^ 2) =
      2 * (4 : ℝ) ^ n / (levelSize n : ℝ) := by
  have ht : (levelSize n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show n - 1 ≤ 2 * n by omega)).ne'
  have he : ∀ a : Cube n, (difference n a) ^ 2 =
      (levelSize n : ℝ)⁻¹ ^ 2 *
      (levelSum n (n - 1) a * levelSum n (n - 1) a -
        2 * (levelSum n (n - 1) a * levelSum n (n + 1) a) +
        levelSum n (n + 1) a * levelSum n (n + 1) a) := by
    intro a
    simp only [difference, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    levelSum_pair, ite_true, show n - 1 ≠ n + 1 by omega, ite_false,
    (adjacent_level_sizes n hn).1, (adjacent_level_sizes n hn).2]
  have hcard : (Fintype.card (Cube n) : ℝ) = 4 ^ n := by
    simp [Cube, pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num]
  rw [hcard]
  field_simp
  ring

lemma levelSum_singleton (n r : ℕ) (hr : 1 ≤ r) (i : Fin (2 * n)) :
    levelSum n r (fun j => decide (j = i)) =
      ((2 * n).choose r : ℝ) - 2 * ((2 * n - 1).choose (r - 1) : ℝ) := by
  have hc : ((level n r).filter (fun S => i ∈ S)).card =
      (2 * n - 1).choose (r - 1) := by
    simpa [level] using Finset.card_filter_powersetCard_subset
      ({i} : Finset (Fin (2 * n))) Finset.univ r (Finset.subset_univ _) (by simpa)
  have hs : ∀ S : Finset (Fin (2 * n)),
      character n S (fun j => decide (j = i)) = if i ∈ S then -1 else 1 := by
    intro S
    simp [character_product, bitSign, Finset.prod_ite_eq, eq_comm]
  simp only [levelSum, Finset.sum_apply, hs]
  have he : ∀ S : Finset (Fin (2 * n)),
      (if i ∈ S then (-1 : ℝ) else 1) = 1 - 2 * (if i ∈ S then 1 else 0) := by
    intro S; split_ifs <;> norm_num
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  rw [← Finset.sum_filter]
  simp [hc, level_card]

lemma singleton_value (n : ℕ) (hn : 2 ≤ n) (i : Fin (2 * n)) :
    difference n (fun j => decide (j = i)) = 2 / (n : ℝ) := by
  have ht : (levelSize n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show n - 1 ≤ 2 * n by omega)).ne'
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hchoose (r : ℕ) (hr : 1 ≤ r) :
      (2 * n : ℝ) * ((2 * n - 1).choose (r - 1) : ℝ) =
        (r : ℝ) * ((2 * n).choose r : ℝ) := by
    have he := Nat.add_one_mul_choose_eq (2 * n - 1) (r - 1)
    rw [show 2 * n - 1 + 1 = 2 * n by omega,
      show r - 1 + 1 = r by omega] at he
    exact_mod_cast (he.trans (Nat.mul_comm _ _))
  have hl := hchoose (n - 1) (by omega)
  have hu := hchoose (n + 1) (by omega)
  have hlev : (2 * n).choose (n + 1) = levelSize n := (adjacent_level_sizes n hn).2 ▸
      (level_card n (n + 1)).symm
  rw [hlev] at hu
  change (2 * n : ℝ) * _ = ((n - 1 : ℕ) : ℝ) * (levelSize n : ℝ) at hl
  have hpred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  simp only [difference, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [levelSum_singleton n (n - 1) (by omega),
    levelSum_singleton n (n + 1) (by omega), hlev]
  change (levelSize n : ℝ)⁻¹ * ((↑(levelSize n) - 2 * _) - (↑(levelSize n) - 2 * _)) = _
  push_cast at hl hu
  rw [hpred] at hl
  simp only [Nat.add_sub_cancel]
  apply (mul_left_cancel₀ hn0)
  field_simp
  nlinarith

lemma levelSum_flip (n r : ℕ) (a : Cube n) :
    levelSum n r (fun j => !(a j)) = (-1 : ℝ) ^ r * levelSum n r a := by
  have hs (S : Finset (Fin (2 * n))) (hS : S ∈ level n r) :
      character n S (fun j => !(a j)) = (-1 : ℝ) ^ r * character n S a := by
    have he : (fun j => !(a j)) = (fun j => xor (a j) true) := by ext j; cases a j <;> rfl
    rw [he, character_xor]
    have hc : character n S (fun _ => true) = (-1 : ℝ) ^ r := by
      simp [character, (Finset.mem_powersetCard.mp hS).2]
    rw [hc, mul_comm]
  simpa only [levelSum, Finset.sum_apply, Finset.mul_sum] using
    Finset.sum_congr rfl hs

lemma norm_difference_flip (n : ℕ) (hn : 2 ≤ n) (a : Cube n) :
    ‖difference n (fun j => !(a j))‖ = ‖difference n a‖ := by
  have hp : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ (n - 1) := by
    rw [show n + 1 = (n - 1) + 2 by omega, pow_add]; norm_num
  have he : difference n (fun j => !(a j)) = (-1 : ℝ) ^ (n - 1) * difference n a := by
    simp only [difference, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      levelSum_flip, hp]
    ring
  rw [he, norm_mul]
  simp

lemma support_flip_card (n : ℕ) (a : Cube n) :
    (support n (fun j => !(a j))).card = 2 * n - (support n a).card := by
  have he : support n (fun j => !(a j)) = (support n a)ᶜ := by
    ext j; simp
  rw [he, Finset.card_compl]
  simp

/-- Each Hamming sphere contributes its cardinality times a single squared value. -/
lemma sphere_energy_le (n : ℕ) (hn : 2 ≤ n) (a : Cube n) :
    (((2 * n).choose (support n a).card : ℕ) : ℝ) * (difference n a) ^ 2 ≤
      2 * (4 : ℝ) ^ n / (levelSize n : ℝ) := by
  let q := (support n a).card
  have he : ∀ S ∈ level n q, difference n (point n S) = difference n a := by
    intro S hS
    apply difference_eq_of_support_card_eq
    simpa using (Finset.mem_powersetCard.mp hS).2
  calc
    _ = ∑ S ∈ level n q, (difference n (point n S)) ^ 2 := by
      rw [Finset.sum_congr rfl (fun S hS => congrArg (fun x : ℝ => x ^ 2) (he S hS))]
      simp only [Finset.sum_const, nsmul_eq_mul, level_card]
      rfl
    _ = ∑ b ∈ (level n q).image (point n), (difference n b) ^ 2 := by
      rw [Finset.sum_image]
      intro S hS T hT heq
      exact point_injective n heq
    _ ≤ ∑ b : Cube n, (difference n b) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro b _ _
      exact sq_nonneg _
    _ = _ := difference_energy n hn

lemma choose_mono_to_middle {N r s : ℕ} (hrs : r ≤ s) (hs : s ≤ N / 2) :
    N.choose r ≤ N.choose s := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma sphere_card_lower (n q : ℕ) (hn : 3 ≤ n) (hq : 3 ≤ q) (hq' : q ≤ 2 * n - 3) :
    (2 * n).choose 3 ≤ (2 * n).choose q := by
  by_cases hqn : q ≤ n
  · exact choose_mono_to_middle hq (by omega)
  · rw [← Nat.choose_symm (by omega : q ≤ 2 * n)]
    exact choose_mono_to_middle (by omega) (by omega)

/-- A simple central-binomial bound suffices for the interior spheres. -/
lemma interior_numerical_bound (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) ^ 2 * (4 : ℝ) ^ n ≤
      2 * (levelSize n : ℝ) * ((2 * n).choose 3 : ℝ) := by
  by_cases hn3 : n = 3
  · subst n
    norm_num [levelSize, Nat.choose]
  have hn4 : 4 ≤ n := by omega
  have hrec := Nat.choose_succ_right_eq (2 * n) (n - 1)
  rw [show n - 1 + 1 = n by omega,
    show 2 * n - (n - 1) = n + 1 by omega] at hrec
  have hpowNat : 4 ^ n ≤ (n + 1) * levelSize n := by
    have h := (Nat.four_pow_lt_mul_centralBinom n hn4).le
    change 4 ^ n ≤ (n + 1) * (2 * n).choose (n - 1)
    calc
      4 ^ n ≤ n * (2 * n).choose n := h
      _ = (n + 1) * (2 * n).choose (n - 1) := by nlinarith [hrec]
  have hpow : (4 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (levelSize n : ℝ) := by
    exact_mod_cast hpowNat
  have h2 := Nat.choose_succ_right_eq (2 * n) 1
  have h3 := Nat.choose_succ_right_eq (2 * n) 2
  simp only [Nat.choose_one_right] at h2
  have h2r : ((2 * n).choose 2 : ℝ) * 2 = (2 * (n : ℝ)) * (2 * n - 1) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) h2
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * n)] at h
    exact h
  have h3r : ((2 * n).choose 3 : ℝ) * 3 =
      ((2 * n).choose 2 : ℝ) * (2 * (n : ℝ) - 2) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) h3
    push_cast [Nat.cast_sub (by omega : 2 ≤ 2 * n)] at h
    exact h
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h3formula : 6 * ((2 * n).choose 3 : ℝ) =
      (2 * (n : ℝ)) * (2 * n - 1) * (2 * n - 2) := by
    nlinarith [h2r]
  have hcard : (n : ℝ) ^ 2 * (n + 1) ≤ 2 * ((2 * n).choose 3 : ℝ) := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ (n : ℝ))
      (mul_nonneg (by positivity : 0 ≤ (n : ℝ)) (sub_nonneg.mpr hnR))]
  calc
    (n : ℝ) ^ 2 * 4 ^ n ≤ (n : ℝ) ^ 2 * ((n + 1) * ↑(levelSize n)) :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = ((n : ℝ) ^ 2 * (n + 1)) * ↑(levelSize n) := by ring
    _ ≤ (2 * ((2 * n).choose 3 : ℝ)) * ↑(levelSize n) := by gcongr
    _ = _ := by ring

lemma interior_point_bound (n : ℕ) (hn : 3 ≤ n) (a : Cube n)
    (hq : 3 ≤ (support n a).card) (hq' : (support n a).card ≤ 2 * n - 3) :
    ‖difference n a‖ ≤ 2 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have ht : (0 : ℝ) < levelSize n := by
    exact_mod_cast Nat.choose_pos (show n - 1 ≤ 2 * n by omega)
  have hC : (0 : ℝ) < (2 * n).choose (support n a).card := by
    exact_mod_cast Nat.choose_pos (show (support n a).card ≤ 2 * n by omega)
  have hnum : (n : ℝ) ^ 2 * (4 : ℝ) ^ n ≤
      2 * (levelSize n : ℝ) * ((2 * n).choose (support n a).card : ℝ) := by
    apply (interior_numerical_bound n hn).trans
    gcongr
    exact_mod_cast sphere_card_lower n (support n a).card hn hq hq'
  have hs : (difference n a) ^ 2 ≤ (2 / (n : ℝ)) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hC).mp
    apply (sphere_energy_le n (by omega) a).trans
    apply (div_le_iff₀ ht).mpr
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hnpos)).mp
    have he : (n : ℝ) ^ 2 *
        (((2 * n).choose (support n a).card : ℝ) * (2 / (n : ℝ)) ^ 2 *
          (levelSize n : ℝ)) =
        4 * (levelSize n : ℝ) * ((2 * n).choose (support n a).card : ℝ) := by
      field_simp
      ring
    rw [he]
    nlinarith only [hnum]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 / (n : ℝ))).mp
  simpa only [Real.norm_eq_abs, sq_abs] using hs

lemma norm_of_support_card_one (n : ℕ) (hn : 2 ≤ n) (a : Cube n)
    (ha : (support n a).card = 1) : ‖difference n a‖ = 2 / (n : ℝ) := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp ha
  have he : a = (fun j => decide (j = i)) := by
    rw [← point_support n a, hi]
    ext j
    simp [point]
  rw [he, singleton_value n hn i]
  exact Real.norm_of_nonneg (by positivity)

/-- The uniform estimate includes every cube point, with no restriction on weight. -/
lemma pointwise_bound (n : ℕ) (hn : 2 ≤ n) (a : Cube n) :
    ‖difference n a‖ ≤ 2 / (n : ℝ) := by
  have hqle : (support n a).card ≤ 2 * n := by
    simpa using Finset.card_le_univ (support n a)
  by_cases he : Even (support n a).card
  · rw [difference_of_even n hn a he, norm_zero]
    positivity
  by_cases h1 : (support n a).card = 1
  · exact (norm_of_support_card_one n hn a h1).le
  by_cases hlast : 2 * n - (support n a).card = 1
  · rw [← norm_difference_flip n hn a]
    apply (norm_of_support_card_one n hn _ _).le
    rw [support_flip_card, hlast]
  have hmod : (support n a).card % 2 ≠ 0 := by
    simpa only [Nat.even_iff] using he
  have hq : 3 ≤ (support n a).card := by omega
  have hq' : (support n a).card ≤ 2 * n - 3 := by omega
  exact interior_point_bound n (by omega) a hq hq'

/-- The source's explicitly indicated maximizers. -/
theorem singleton_extremizers :
    Specs.ExpandedFA.AP.SmallWalshDifference.singletonExtremizers := by
  intro n hn i
  exact singleton_value n hn i

/-- Exact supremum norm of the adjacent-level difference. -/
theorem exact_norm : Specs.ExpandedFA.AP.SmallWalshDifference.exactNorm := by
  intro n hn
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr (pointwise_bound n hn)
  · let i : Fin (2 * n) := ⟨0, by omega⟩
    have h := norm_le_pi_norm (difference n) (fun j => decide (j = i))
    rw [singleton_value n hn i, Real.norm_of_nonneg (by positivity)] at h
    exact h

end ExpandedFA.AP.SmallWalshDifference
