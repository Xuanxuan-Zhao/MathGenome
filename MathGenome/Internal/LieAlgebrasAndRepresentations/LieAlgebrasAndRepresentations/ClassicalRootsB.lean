import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsB
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Aesop

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieAlgebrasAndRepresentations.ClassicalRootsB
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsB

theorem opposite_eq_iff {n : ℕ} (p q : Index n) :
    p = opposite q ↔ q = opposite p := by
  constructor <;> intro h <;> subst_vars <;> simp

@[simp] theorem opposite_inj {n : ℕ} (p q : Index n) :
    opposite p = opposite q ↔ p = q :=
  (show Function.Injective (@opposite n) from fun _ _ h => by
    simpa using congrArg opposite h).eq_iff

@[simp] theorem coordinateWeight_opposite {n : ℕ} (p : Index n) :
    coordinateWeight (opposite p) = -coordinateWeight p := by
  cases p with
  | none => simp [coordinateWeight, opposite]
  | some p => cases p <;> simp [coordinateWeight, opposite]

lemma form_mul {n : ℕ} (X : Mat n) (p q : Index n) :
    (form n * X) p q = X (opposite p) q := by
  simp only [Matrix.mul_apply, form, opposite_eq_iff p]
  simp

lemma mul_form {n : ℕ} (X : Mat n) (p q : Index n) :
    (X * form n) p q = X p (opposite q) := by
  simp [Matrix.mul_apply, form]

theorem form_properties : form_properties_type := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · ext p q
    simp only [Matrix.transpose_apply, form, opposite_eq_iff q p]
  · ext p q
    rw [form_mul]
    simp [form, Matrix.one_apply]
  · simp [Index]; omega

theorem algebra_entries : algebra_entries_type := by
  intro n X
  rw [algebra, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  change X.transpose * form n = form n * (-X) ↔ _
  constructor
  · intro h p q
    have h' := congrArg (fun M : Mat n => M q (opposite p)) h
    simpa only [mul_form, form_mul, opposite_opposite, Matrix.transpose_apply,
      Matrix.neg_apply] using h'
  · intro h
    ext p q
    simp only [mul_form, form_mul, Matrix.transpose_apply, Matrix.neg_apply]
    simpa using h (opposite q) p

theorem diagonal_injective : diagonal_injective_type := by
  intro n t u h
  funext i
  have hi := congrArg (fun M : Mat n => M (some (Sum.inl i)) (some (Sum.inl i))) h
  simpa [diagonal, coordinateWeight, epsilon] using hi

theorem diagonal_mem : diagonal_mem_type := by
  intro n t
  rw [algebra_entries]
  intro p q
  by_cases h : p = q
  · subst q
    simp [diagonal, coordinateWeight_opposite]
  · have h' : opposite q ≠ opposite p := fun he => h (by simpa using congrArg opposite he.symm)
    simp [diagonal, h, h']

lemma diagonal_bracket {n : ℕ} (t : Parameters n) (X : Mat n) (p q : Index n) :
    ⁅diagonal n t, X⁆ p q =
      (coordinateWeight p t - coordinateWeight q t) * X p q := by
  change ((Matrix.diagonal (fun p => coordinateWeight p t) : Mat n) * X -
    X * Matrix.diagonal (fun p => coordinateWeight p t)) p q = _
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

lemma mem_weightSpace {n : ℕ} (a : Weight n) (X : Mat n) :
    X ∈ weightSpace a ↔ X ∈ algebra n ∧
      ∀ t : Parameters n, ⁅diagonal n t, X⁆ = a t • X := by
  simp only [weightSpace, Submodule.mem_inf, LieSubalgebra.mem_toSubmodule,
    Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

theorem weightSpace_entries : weightSpace_entries_type := by
  intro n a X
  rw [mem_weightSpace]
  constructor
  · rintro ⟨hX, h⟩
    refine ⟨hX, fun p q hne => ?_⟩
    apply LinearMap.ext
    intro t
    have ht := congrArg (fun M : Mat n => M p q) (h t)
    rw [diagonal_bracket] at ht
    exact (mul_right_cancel₀ hne ht).symm
  · rintro ⟨hX, h⟩
    refine ⟨hX, fun t => ?_⟩
    ext p q
    rw [diagonal_bracket]
    change _ = a t * X p q
    by_cases hne : X p q = 0
    · simp [hne]
    · rw [h p q hne]
      rfl

@[simp] lemma epsilon_single {n : ℕ} (i j : Fin n) (c : ℂ) :
    epsilon i (Pi.single j c) = if i = j then c else 0 := by
  simp [epsilon, Pi.single_apply]

@[simp] lemma epsilon_ne_zero {n : ℕ} (i : Fin n) : epsilon i ≠ 0 := by
  intro h
  have hh := congrArg (fun a : Weight n => a (Pi.single i 1)) h
  simp at hh

@[simp] lemma epsilon_inj {n : ℕ} (i j : Fin n) : epsilon i = epsilon j ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    have hh := congrArg (fun a : Weight n => a (Pi.single i 1)) h
    simp [Ne.symm hij] at hh
  · rintro rfl; rfl

@[simp] lemma epsilon_ne_neg {n : ℕ} (i j : Fin n) : epsilon i ≠ -epsilon j := by
  intro h
  have hh := congrArg (fun a : Weight n => a (Pi.single i 1)) h
  by_cases hij : i = j
  · subst j; norm_num at hh
  · simp [Ne.symm hij] at hh

lemma coordinateWeight_injective {n : ℕ} : Function.Injective (@coordinateWeight n) := by
  intro p q h
  rcases p with _ | (i | i) <;> rcases q with _ | (j | j)
  all_goals try simp only [coordinateWeight] at h
  all_goals simp_all [eq_comm]

theorem zero_space : zero_space_type := by
  intro n
  ext X
  constructor
  · intro h
    obtain ⟨hX, hw⟩ := (weightSpace_entries n 0 X).mp h
    have hd : ∀ p q, p ≠ q → X p q = 0 := by
      intro p q hpq
      by_contra hx
      have he := hw p q hx
      have hc : coordinateWeight p = coordinateWeight q := sub_eq_zero.mp he.symm
      exact hpq (coordinateWeight_injective hc)
    refine ⟨fun i => X (some (Sum.inl i)) (some (Sum.inl i)), ?_⟩
    ext p q
    by_cases hpq : p = q
    · subst q
      rw [algebra_entries] at hX
      rcases p with _ | (i | i)
      · have hh := hX none none
        simp only [opposite] at hh
        simp only [diagonal, LinearMap.coe_mk, AddHom.coe_mk, Matrix.diagonal_apply_eq,
          coordinateWeight, LinearMap.zero_apply]
        have hz : X none none = 0 := by linear_combination (1/2 : ℂ) * hh
        exact hz.symm
      · simp [diagonal, coordinateWeight, epsilon]
      · simpa [diagonal, coordinateWeight, epsilon, opposite] using (hX (some (Sum.inr i)) (some (Sum.inr i))).symm
    · simp [diagonal, hpq, hd p q hpq]
  · rintro ⟨t, rfl⟩
    rw [weightSpace_entries]
    refine ⟨diagonal_mem n t, fun p q h => ?_⟩
    by_cases hpq : p = q
    · subst q; simp
    · exact False.elim (h (by simp [diagonal, hpq]))

lemma rootVector_mem {n : ℕ} (p q : Index n) :
    rootVector p q ∈ weightSpace (coordinateWeight p - coordinateWeight q) := by
  rw [weightSpace_entries]
  constructor
  · rw [algebra_entries]
    intro r s
    simp only [rootVector, Matrix.sub_apply, Matrix.single_apply]
    simp only [opposite_inj]
    simp [opposite_eq_iff, eq_comm, and_comm]
  · intro r s h
    by_cases h1 : r = p ∧ s = q
    · rcases h1 with ⟨rfl, rfl⟩; rfl
    · have h2 : r = opposite q ∧ s = opposite p := by
        by_contra h2
        have h1' : ¬(p = r ∧ q = s) := by simpa only [eq_comm] using h1
        have h2' : ¬(opposite q = r ∧ opposite p = s) := by simpa only [eq_comm] using h2
        exact h (by simp only [rootVector, Matrix.sub_apply, Matrix.single_apply,
          ite_eq_right h1', ite_eq_right h2', sub_zero])
      rcases h2 with ⟨rfl, rfl⟩
      simp [sub_eq_add_neg, add_comm]

lemma rootVector_entry {n : ℕ} (p q : Index n) (h : p ≠ opposite q) :
    rootVector p q p q = 1 := by
  simp [rootVector, Ne.symm h]

lemma rootVector_ne_zero {n : ℕ} (p q : Index n) (h : p ≠ opposite q) :
    rootVector p q ≠ 0 := by
  intro hz
  have he := congrArg (fun M : Mat n => M p q) hz
  rw [rootVector_entry p q h] at he
  exact one_ne_zero he

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
lemma difference_unique {n : ℕ} (p q r s : Index n)
    (hpq : p ≠ q) (hpb : p ≠ opposite q)
    (hrs : r ≠ s) (hrb : r ≠ opposite s)
    (h : coordinateWeight p - coordinateWeight q = coordinateWeight r - coordinateWeight s) :
    (r = p ∧ s = q) ∨ (r = opposite q ∧ s = opposite p) := by
  have coeff (k : Fin n) := congrArg (fun a : Weight n => a (Pi.single k 1)) h
  rcases p with _ | (i | i) <;> rcases q with _ | (j | j) <;>
    rcases r with _ | (k | k) <;> rcases s with _ | (l | l)
  all_goals try have hi := coeff i
  all_goals try have hj := coeff j
  all_goals try have hk := coeff k
  all_goals try have hl := coeff l
  all_goals clear coeff h
  all_goals try simp only [opposite, Option.some.injEq, Sum.inl.injEq, Sum.inr.injEq,
    reduceCtorEq, ne_eq, not_true_eq_false, not_false_eq_true] at hpq hpb hrs hrb ⊢
  all_goals try simp only [coordinateWeight, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.zero_apply, epsilon_single] at *
  all_goals try simp only [eq_comm, ite_true, zero_sub, sub_zero,
    true_and, and_true, false_and, and_false, false_or, or_false] at *
  all_goals split_ifs at * <;> norm_num at * <;> aesop

lemma antidiagonal_zero {n : ℕ} (X : Mat n) (hX : X ∈ algebra n) (p : Index n) :
    X p (opposite p) = 0 := by
  have h := (algebra_entries n X).mp hX p (opposite p)
  simp only [opposite_opposite] at h
  linear_combination (1/2 : ℂ) * h

lemma nonzero_entry_indices {n : ℕ} (a : Weight n) (ha : a ≠ 0)
    (X : Mat n) (hX : X ∈ weightSpace a) (p q : Index n) (hx : X p q ≠ 0) :
    p ≠ q ∧ p ≠ opposite q := by
  have h := (weightSpace_entries n a X).mp hX
  constructor
  · rintro rfl
    exact ha (by simpa using h.2 p p hx)
  · intro hp
    subst p
    exact hx (by simpa using antidiagonal_zero X h.1 (opposite q))

theorem root_spaces : root_spaces_type := by
  intro n p q hpq hpb
  have ha : coordinateWeight p - coordinateWeight q ≠ 0 := by
    intro h
    exact hpq (coordinateWeight_injective (sub_eq_zero.mp h))
  apply le_antisymm
  · intro X hX
    have h := (weightSpace_entries n _ X).mp hX
    have he : X = X p q • rootVector p q := by
      ext r s
      by_cases h1 : r = p ∧ s = q
      · rcases h1 with ⟨h1r, h1s⟩
        subst r; subst s
        change _ = X p q * rootVector p q p q
        rw [rootVector_entry p q hpb, mul_one]
      by_cases h2 : r = opposite q ∧ s = opposite p
      · rcases h2 with ⟨rfl, rfl⟩
        have hm := (algebra_entries n X).mp h.1 (opposite q) (opposite p)
        simp only [opposite_opposite] at hm
        change _ = X p q * rootVector p q (opposite q) (opposite p)
        rw [hm]
        simp [rootVector, hpb, mul_neg]
      have hz : X r s = 0 := by
        by_contra hx
        have hind := nonzero_entry_indices _ ha X hX r s hx
        exact (difference_unique p q r s hpq hpb hind.1 hind.2 (h.2 r s hx)).elim h1 h2
      have h1' : ¬(p = r ∧ q = s) := by simpa only [eq_comm] using h1
      have h2' : ¬(opposite q = r ∧ opposite p = s) := by simpa only [eq_comm] using h2
      simp only [rootVector, Matrix.sub_apply, Matrix.single_apply, ite_eq_right h1',
        ite_eq_right h2', sub_zero, hz, Matrix.smul_apply, smul_zero]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (rootVector_mem p q))

lemma root_iff_pair {n : ℕ} (a : Weight n) : a ∈ roots n ↔
    ∃ p q : Index n, p ≠ q ∧ p ≠ opposite q ∧ a = coordinateWeight p - coordinateWeight q := by
  constructor
  · rintro ⟨ha, hs⟩
    obtain ⟨X, hX, hx⟩ := (Submodule.ne_bot_iff _).mp hs
    obtain ⟨p, q, hpq⟩ : ∃ p q, X p q ≠ 0 := by
      by_contra! hh
      exact hx (Matrix.ext fun p q => hh p q)
    have hi := nonzero_entry_indices a ha X hX p q hpq
    exact ⟨p, q, hi.1, hi.2, ((weightSpace_entries n a X).mp hX).2 p q hpq⟩
  · rintro ⟨p, q, hpq, hpb, rfl⟩
    refine ⟨fun h => hpq (coordinateWeight_injective (sub_eq_zero.mp h)), ?_⟩
    exact (Submodule.ne_bot_iff _).mpr ⟨rootVector p q, rootVector_mem p q,
      rootVector_ne_zero p q hpb⟩

theorem root_dimensions : root_dimensions_type := by
  intro n a ha
  obtain ⟨p, q, hpq, hpb, rfl⟩ := (root_iff_pair a).mp ha
  rw [root_spaces n p q hpq hpb]
  exact finrank_span_singleton (rootVector_ne_zero p q hpb)

theorem roots_eq : roots_eq_type := by
  intro n
  ext a
  rw [root_iff_pair]
  constructor
  · rintro ⟨p, q, hpq, hpb, rfl⟩
    rcases p with _ | (i | i) <;> rcases q with _ | (j | j)
    all_goals change _ ∨ _
    all_goals simp only [opposite, Option.some.injEq, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, ne_eq, not_true_eq_false, not_false_eq_true] at hpq hpb
    · left; exact ⟨j, Or.inr (by simp [coordinateWeight])⟩
    · left; exact ⟨j, Or.inl (by simp [coordinateWeight])⟩
    · left; exact ⟨i, Or.inl (by simp [coordinateWeight])⟩
    · right
      rcases lt_or_gt_of_ne hpq with hij | hji
      · exact ⟨i, j, hij, Or.inr (Or.inl rfl)⟩
      · refine ⟨j, i, hji, Or.inr (Or.inr (Or.inl ?_))⟩
        simp [coordinateWeight, sub_eq_add_neg, add_comm]
    · right
      rcases lt_or_gt_of_ne hpb with hij | hji
      · exact ⟨i, j, hij, Or.inl (by simp [coordinateWeight])⟩
      · exact ⟨j, i, hji, Or.inl (by simp [coordinateWeight, add_comm])⟩
    · left; exact ⟨i, Or.inr (by simp [coordinateWeight])⟩
    · right
      rcases lt_or_gt_of_ne hpb with hij | hji
      · exact ⟨i, j, hij, Or.inr (Or.inr (Or.inr rfl))⟩
      · refine ⟨j, i, hji, Or.inr (Or.inr (Or.inr ?_))⟩
        simp [coordinateWeight, sub_eq_add_neg, add_comm]
    · right
      rcases lt_or_gt_of_ne hpq with hij | hji
      · exact ⟨i, j, hij, Or.inr (Or.inr (Or.inl (by simp [coordinateWeight])))⟩
      · refine ⟨j, i, hji, Or.inr (Or.inl ?_)⟩
        simp [coordinateWeight, sub_eq_add_neg, add_comm]
  · rintro (⟨i, rfl | rfl⟩ | ⟨i, j, hij, rfl | rfl | rfl | rfl⟩)
    · exact ⟨some (Sum.inl i), none, by simp, by simp [opposite], by simp [coordinateWeight]⟩
    · exact ⟨some (Sum.inr i), none, by simp, by simp [opposite], by simp [coordinateWeight]⟩
    · exact ⟨some (Sum.inl i), some (Sum.inr j), by simp,
        by simpa [opposite] using ne_of_lt hij, by simp [coordinateWeight]⟩
    · exact ⟨some (Sum.inl i), some (Sum.inl j), by simpa using ne_of_lt hij,
        by simp [opposite], rfl⟩
    · exact ⟨some (Sum.inr i), some (Sum.inr j), by simpa using ne_of_lt hij,
        by simp [opposite], by simp [coordinateWeight]⟩
    · exact ⟨some (Sum.inr i), some (Sum.inl j), by simp,
        by simpa [opposite] using ne_of_lt hij, rfl⟩

/-- The sole entry in the rank-zero model is its own negative. -/
theorem algebra_zero : algebra 0 = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro X hX
  rw [LieSubalgebra.mem_bot]
  ext p q
  have hp : p = none := Subsingleton.elim _ _
  have hq : q = none := Subsingleton.elim _ _
  subst p
  subst q
  simpa [opposite] using antidiagonal_zero X hX none

theorem roots_zero : roots 0 = ∅ := by
  rw [roots_eq]
  ext a
  simp [listedRoots]

@[simp] lemma opposite_eq {n : ℕ} (p q : Index n) :
    opposite p = q ↔ p = opposite q := by
  constructor <;> intro h <;> subst_vars <;> simp

lemma rootVector_sum {n : ℕ} (X : Mat n) (hX : X ∈ algebra n) :
    (∑ p : Index n, ∑ q : Index n, X p q • rootVector p q) = (2 : ℂ) • X := by
  ext r s
  simp only [rootVector, smul_sub, Finset.sum_sub_distrib,
    Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp only [opposite_eq]
  simp only [ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  have h := (algebra_entries n X).mp hX r s
  change X r s - X (opposite s) (opposite r) = 2 * X r s
  linear_combination -h

theorem decomposition : decomposition_type := by
  intro n
  constructor
  · apply le_antisymm
    · exact iSup_le fun a => inf_le_left
    · intro X hX
      have hs : (∑ p : Index n, ∑ q : Index n, X p q • rootVector p q) ∈
          ⨆ a : Weight n, weightSpace a := by
        apply Submodule.sum_mem
        intro p hp
        apply Submodule.sum_mem
        intro q hq
        exact (le_iSup (fun a : Weight n => weightSpace a) _)
          (Submodule.smul_mem _ (X p q) (rootVector_mem p q))
      rw [rootVector_sum X hX] at hs
      have hh := Submodule.smul_mem (⨆ a : Weight n, weightSpace a) (1/2 : ℂ) hs
      simpa [smul_smul] using hh
  · rw [iSupIndep_def]
    intro a
    rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro X ⟨hXa, hXs⟩
    ext p q
    by_contra hx
    have hweight := ((weightSpace_entries n a X).mp hXa).2 p q hx
    let ev : Mat n →ₗ[ℂ] ℂ := (LinearMap.proj q : (Index n → ℂ) →ₗ[ℂ] ℂ).comp
      (LinearMap.proj p : Mat n →ₗ[ℂ] (Index n → ℂ))
    have hle : (⨆ (b : Weight n) (_ : b ≠ a), weightSpace b) ≤ LinearMap.ker ev := by
      refine iSup_le fun b => iSup_le fun hba => ?_
      intro Y hY
      change Y p q = 0
      by_contra hy
      have he := ((weightSpace_entries n b Y).mp hY).2 p q hy
      exact hba (he.trans hweight.symm)
    exact hx (show X p q = 0 from hle hXs)

lemma coefficient_diagonal {n : ℕ} (p : Index n) :
    diagonal n (fun i => coordinateWeight p (Pi.single i 1)) =
      Matrix.single p p 1 - Matrix.single (opposite p) (opposite p) 1 := by
  rcases p with _ | (i | i)
  · simp only [coordinateWeight, LinearMap.zero_apply, opposite, sub_self]
    exact map_zero (diagonal n)
  all_goals
    ext r s
    by_cases hrs : r = s
    · subst s
      rcases r with _ | (j | j) <;>
        simp [diagonal, coordinateWeight, opposite, epsilon, Pi.single_apply, Matrix.single_apply, eq_comm]
    · have hn : ∀ p : Index n, ¬(p = r ∧ p = s) := by
        intro p h
        exact hrs (h.1.symm.trans h.2)
      simp only [diagonal, LinearMap.coe_mk, AddHom.coe_mk, Matrix.diagonal_apply,
        ite_eq_right hrs, Matrix.sub_apply, Matrix.single_apply, ite_eq_right (hn _), sub_self]

lemma rootVector_bracket {n : ℕ} (p q : Index n) (hpb : p ≠ opposite q) :
    ⁅rootVector p q, rootVector q p⁆ =
      diagonal n (fun i => (coordinateWeight p - coordinateWeight q) (Pi.single i 1)) := by
  have h1 : q ≠ opposite p := fun h => hpb ((opposite_eq_iff p q).mpr h)
  have h2 : opposite p ≠ q := Ne.symm h1
  have h3 : opposite q ≠ p := Ne.symm hpb
  change _ = diagonal n ((fun i => coordinateWeight p (Pi.single i 1)) -
    (fun i => coordinateWeight q (Pi.single i 1)))
  rw [map_sub, coefficient_diagonal, coefficient_diagonal]
  simp only [rootVector, LieRing.of_associative_ring_bracket, sub_mul, mul_sub,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ h1,
    Matrix.single_mul_single_of_ne _ _ _ _ h2,
    Matrix.single_mul_single_of_ne _ _ _ _ hpb,
    Matrix.single_mul_single_of_ne _ _ _ _ h3, one_mul]
  abel

@[simp] lemma squaredLength_neg {n : ℕ} (a : Weight n) :
    squaredLength (-a) = squaredLength a := by
  simp [squaredLength]

@[simp] lemma squaredLength_epsilon {n : ℕ} (i : Fin n) :
    squaredLength (epsilon i) = 1 := by
  simp [squaredLength, epsilon_single, eq_comm]

lemma squaredLength_add {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    squaredLength (epsilon i + epsilon j) = 2 := by
  unfold squaredLength
  have hh (k : Fin n) : ((epsilon i + epsilon j) (Pi.single k 1)) ^ 2 =
      (if i = k then (1 : ℂ) else 0) + (if j = k then 1 else 0) := by
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp_all
  simp_rw [hh]
  rw [Finset.sum_add_distrib]
  norm_num [eq_comm]

lemma squaredLength_sub {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    squaredLength (epsilon i - epsilon j) = 2 := by
  unfold squaredLength
  have hh (k : Fin n) : ((epsilon i - epsilon j) (Pi.single k 1)) ^ 2 =
      (if i = k then (1 : ℂ) else 0) + (if j = k then 1 else 0) := by
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp_all
  simp_rw [hh]
  rw [Finset.sum_add_distrib]
  norm_num [eq_comm]

lemma squaredLength_root_ne_zero {n : ℕ} (a : Weight n) (ha : a ∈ roots n) :
    squaredLength a ≠ 0 := by
  rw [roots_eq n] at ha
  rcases ha with (⟨i, rfl | rfl⟩ | ⟨i, j, hij, rfl | rfl | rfl | rfl⟩)
  · simp
  · simp
  · rw [squaredLength_add i j (ne_of_lt hij)]; norm_num
  · rw [squaredLength_sub i j (ne_of_lt hij)]; norm_num
  · have he : -epsilon i + epsilon j = -(epsilon i - epsilon j) := by module
    rw [he, squaredLength_neg, squaredLength_sub i j (ne_of_lt hij)]; norm_num
  · have he : -epsilon i - epsilon j = -(epsilon i + epsilon j) := by module
    rw [he, squaredLength_neg, squaredLength_add i j (ne_of_lt hij)]; norm_num

lemma evaluate_coefficients {n : ℕ} (a : Weight n) (t : Parameters n) :
    a t = ∑ i : Fin n, t i * a (Pi.single i 1) := by
  have ht : t = ∑ i : Fin n, t i • Pi.single i 1 := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [ht, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

lemma coroot_eq_smul {n : ℕ} (a : Weight n) :
    coroot a = (2 / squaredLength a) • diagonal n (fun i => a (Pi.single i 1)) := by
  rw [coroot, ← map_smul]
  rfl

lemma coroot_evaluation {n : ℕ} (a : Weight n) (ha : squaredLength a ≠ 0) :
    a (fun i => (2 / squaredLength a) * a (Pi.single i 1)) = 2 := by
  change a ((2 / squaredLength a) • (fun i => a (Pi.single i 1))) = 2
  rw [map_smul, evaluate_coefficients]
  change (2 / squaredLength a) * (∑ i : Fin n, a (Pi.single i 1) * a (Pi.single i 1)) = 2
  simp_rw [← pow_two]
  change (2 / squaredLength a) * squaredLength a = 2
  exact div_mul_cancel₀ _ ha

theorem coroot_triples : coroot_triples_type := by
  intro n a ha
  have hlen := squaredLength_root_ne_zero a ha
  refine ⟨hlen, diagonal_mem _ _, ?_⟩
  obtain ⟨p, q, hpq, hpb, rfl⟩ := (root_iff_pair a).mp ha
  let a : Weight n := coordinateWeight p - coordinateWeight q
  let c : ℂ := 2 / squaredLength a
  have hc : c ≠ 0 := div_ne_zero (by norm_num) hlen
  have he := rootVector_mem p q
  have hf : c • rootVector q p ∈ weightSpace (-a) := by
    apply Submodule.smul_mem
    simpa [a, neg_sub] using rootVector_mem q p
  refine ⟨rootVector p q, c • rootVector q p, he, hf, rootVector_ne_zero p q hpb,
    smul_ne_zero hc (rootVector_ne_zero q p ((opposite_eq_iff p q).mpr.mt hpb)), ?_, ?_, ?_⟩
  · rw [lie_smul, rootVector_bracket p q hpb]
    exact (coroot_eq_smul a).symm
  · have hh := (mem_weightSpace a (rootVector p q)).mp he |>.2
    simpa only [coroot, coroot_evaluation a hlen] using
      hh (fun i => (2 / squaredLength a) * a (Pi.single i 1))
  · have hh := (mem_weightSpace (-a) (c • rootVector q p)).mp hf |>.2
    simpa only [coroot, LinearMap.neg_apply, coroot_evaluation a hlen] using
      hh (fun i => (2 / squaredLength a) * a (Pi.single i 1))

theorem form_nondegenerate : form_nondegenerate_type := by
  intro n
  apply Matrix.nondegenerate_of_det_ne_zero
  intro hz
  have h := congrArg Matrix.det (form_properties n).2.1
  simp only [Matrix.det_mul, Matrix.det_one, hz, zero_mul] at h
  exact zero_ne_one h

lemma coordinates_of_diagonal {n : ℕ} (h : cartan n) (t : Parameters n)
    (ht : diagonal n t = h.val.val) : coordinates n h = t := by
  funext i
  change h.val.val (some (Sum.inl i)) (some (Sum.inl i)) = t i
  rw [← ht]
  simp [diagonal, coordinateWeight, epsilon]

lemma cartan_reconstruction {n : ℕ} (h : cartan n) :
    diagonal n (coordinates n h) = h.val.val := by
  obtain ⟨t, ht⟩ := h.property
  rw [coordinates_of_diagonal h t ht]
  exact ht

theorem cartan_identification : cartan_identification_type := by
  intro n
  have hbij : Function.Bijective (coordinates n) := by
    constructor
    · intro h k he
      apply Subtype.ext
      apply Subtype.ext
      rw [← cartan_reconstruction h, ← cartan_reconstruction k, he]
    · intro t
      let h : cartan n := ⟨⟨diagonal n t, diagonal_mem n t⟩, t, rfl⟩
      exact ⟨h, coordinates_of_diagonal h t rfl⟩
  refine ⟨hbij, ?_, ?_⟩
  · intro a b he
    apply LinearMap.ext
    intro t
    obtain ⟨h, rfl⟩ := hbij.2 t
    exact congrArg (fun a : Module.Dual ℂ (cartan n) => a h) he
  · intro a
    let e : cartan n ≃ₗ[ℂ] Parameters n := LinearEquiv.ofBijective (coordinates n) hbij
    refine ⟨a.comp e.symm.toLinearMap, ?_⟩
    apply LinearMap.ext
    intro h
    change a (e.symm (e h)) = a h
    rw [e.symm_apply_apply]

theorem root_space_bridge : root_space_bridge_type := by
  intro n a
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rw [mem_weightSpace]
    refine ⟨Y.property, fun t => ?_⟩
    let h : cartan n := ⟨⟨diagonal n t, diagonal_mem n t⟩, t, rfl⟩
    have hy := (LieModule.mem_weightSpace (character a) Y).mp hY h
    have hy' := congrArg (fun Z : algebra n => (Z : Mat n)) hy
    change ⁅diagonal n t, (Y : Mat n)⁆ = character a h • (Y : Mat n) at hy'
    simpa only [character, LinearMap.comp_apply, coordinates_of_diagonal h t rfl,
      Submodule.subtype_apply] using hy'
  · intro hX
    have hx := (mem_weightSpace a X).mp hX
    refine ⟨⟨X, hx.1⟩, ?_, rfl⟩
    apply (LieModule.mem_weightSpace (character a) (⟨X, hx.1⟩ : algebra n)).mpr
    intro h
    apply Subtype.ext
    change ⁅h.val.val, X⁆ = character a h • X
    rw [← cartan_reconstruction h]
    exact hx.2 (coordinates n h)

end LieAlgebrasAndRepresentations.ClassicalRootsB
