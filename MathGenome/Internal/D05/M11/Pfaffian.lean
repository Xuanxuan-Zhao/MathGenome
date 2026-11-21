import MathGenome.Internal.Specs.D05.M11.Pfaffian
import MathGenome.Internal.D05.M11.Alternating
import MathGenome.Internal.D05.M15.ExteriorBasis
import MathGenome.Internal.D05.Foundations.PermutationSign
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace D05.M11.Pfaffian
open scoped BigOperators
open Specs.D05.M11.Pfaffian

abbrev omega : omega_type := @omega_value
abbrev volume := volume_value
abbrev pfaffian : pfaffian_type := @pfaffian_value

/-- Currying an ordered list of 2m indices into its m ordered pairs. -/
def pairFunctions (m n : ℕ) : (Fin (2*m) → Fin n) ≃ (Fin m → Fin n × Fin n) :=
  ((Equiv.arrowCongr (pairIndex m).symm (Equiv.refl (Fin n))).trans
    (Equiv.curry (Fin m) (Fin 2) (Fin n))).trans
      (Equiv.piCongrRight fun _ => finTwoArrowEquiv (Fin n))

@[simp] lemma pairFunctions_apply (m n : ℕ) (f : Fin (2*m) → Fin n) (j : Fin m) :
    pairFunctions m n f j = (f (pairIndex m (j,0)), f (pairIndex m (j,1))) := rfl

/-- Expanding a power into ordered words works even in a noncommutative algebra. -/
lemma power_sum_words {R : Type*} [Ring R] [Algebra ℝ R]
    {I : Type*} [Fintype I] (a : I → R) (m : ℕ) :
    (∑ i, a i)^m = ∑ f : Fin m → I, (List.ofFn fun j => a (f j)).prod := by
  classical
  simpa only [MultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate] using
    (MultilinearMap.mkPiAlgebraFin ℝ m R).map_sum (fun _ i => a i)

/-- Flattening m adjacent pairs gives the 2m-fold exterior product. -/
lemma paired_word {V : Type*} [AddCommGroup V] [Module ℝ V]
    (m : ℕ) (b : Fin (2*m) → V) (f : Fin (2*m) → Fin (2*m)) :
    (List.ofFn fun j : Fin m =>
      ExteriorAlgebra.ι ℝ (b (f (pairIndex m (j,0)))) *
      ExteriorAlgebra.ι ℝ (b (f (pairIndex m (j,1))))).prod =
    ExteriorAlgebra.ιMulti ℝ (2*m) (b ∘ f) := by
  rw [ExteriorAlgebra.ιMulti_apply, List.ofFn_mul', List.prod_flatten, List.map_ofFn]
  congr 1
  congr 1
  funext j
  simp [List.ofFn_succ, pairIndex, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- The full ordered-pair expansion, before eliminating repetitions. -/
lemma full_pair_power {V : Type*} [AddCommGroup V] [Module ℝ V]
    (m : ℕ) (b : Fin (2*m) → V) (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) :
    (∑ i, ∑ j, A i j • (ExteriorAlgebra.ι ℝ (b i) * ExteriorAlgebra.ι ℝ (b j)))^m =
    ∑ f : Fin (2*m) → Fin (2*m),
      (∏ j : Fin m, A (f (pairIndex m (j,0))) (f (pairIndex m (j,1)))) •
        ExteriorAlgebra.ιMulti ℝ (2*m) (b ∘ f) := by
  classical
  rw [← Fintype.sum_prod_type (fun p : Fin (2*m) × Fin (2*m) =>
    A p.1 p.2 • (ExteriorAlgebra.ι ℝ (b p.1) * ExteriorAlgebra.ι ℝ (b p.2)))]
  rw [power_sum_words]
  symm
  apply Fintype.sum_equiv (pairFunctions m (2*m))
  intro f
  change _ = (MultilinearMap.mkPiAlgebraFin ℝ m (ExteriorAlgebra ℝ V))
    (fun j => A ((pairFunctions m (2*m) f j).1) ((pairFunctions m (2*m) f j).2) •
      (ExteriorAlgebra.ι ℝ (b ((pairFunctions m (2*m) f j).1)) *
       ExteriorAlgebra.ι ℝ (b ((pairFunctions m (2*m) f j).2))))
  rw [MultilinearMap.map_smul_univ]
  simp only [pairFunctions_apply, MultilinearMap.mkPiAlgebraFin_apply]
  rw [paired_word]

/-- Repeated indices contribute zero; all remaining lists are permutations.
This argument also applies in degree zero. -/
lemma sum_words_eq_sum_permutations {V : Type*} [AddCommGroup V] [Module ℝ V]
    (n : ℕ) (b : Fin n → V) (c : (Fin n → Fin n) → ℝ) :
    (∑ f : Fin n → Fin n, c f • ExteriorAlgebra.ιMulti ℝ n (b ∘ f)) =
    ∑ σ : Equiv.Perm (Fin n), c σ • ExteriorAlgebra.ιMulti ℝ n (b ∘ σ) := by
  classical
  symm
  apply Finset.sum_bij_ne_zero (fun (σ : Equiv.Perm (Fin n)) _ _ => (σ : Fin n → Fin n))
  · intros; exact Finset.mem_univ _
  · intro σ _ _ τ _ _ h
    exact Equiv.ext (congrFun h)
  · intro f _ hf
    have hinj : Function.Injective f := by
      by_contra h
      have hb : ¬Function.Injective (b ∘ f) := by
        intro hb
        exact h (fun i j hij => hb (congrArg b hij))
      exact hf (by rw [ExteriorAlgebra.ιMulti_eq_zero_of_not_inj hb, smul_zero])
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩)
    refine ⟨σ, Finset.mem_univ _, ?_, rfl⟩
    exact hf
  · intros; rfl

/-- Applying a permutation to the top word gives its integer inversion sign. -/
lemma permutation_word {V : Type*} [AddCommGroup V] [Module ℝ V]
    (n : ℕ) (b : Fin n → V) (σ : Equiv.Perm (Fin n)) :
    ExteriorAlgebra.ιMulti ℝ n (b ∘ σ) =
      (D05.Foundations.permutationSign σ : ℝ) • ExteriorAlgebra.ιMulti ℝ n b := by
  rw [(ExteriorAlgebra.ιMulti ℝ n).map_perm b σ,
    D05.Foundations.PermutationSign.signIdentification]
  rw [Units.smul_def, Int.cast_smul_eq_zsmul]

/-- The expanded full pair sum has precisely the signed permutation coefficient. -/
lemma full_pair_power_permutations {V : Type*} [AddCommGroup V] [Module ℝ V]
    (m : ℕ) (b : Fin (2*m) → V) (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) :
    (∑ i, ∑ j, A i j • (ExteriorAlgebra.ι ℝ (b i) * ExteriorAlgebra.ι ℝ (b j)))^m =
    (∑ σ : Equiv.Perm (Fin (2*m)), (D05.Foundations.permutationSign σ : ℝ) *
      ∏ j : Fin m, A (σ (pairIndex m (j,0))) (σ (pairIndex m (j,1)))) •
        ExteriorAlgebra.ιMulti ℝ (2*m) b := by
  classical
  rw [full_pair_power, sum_words_eq_sum_permutations]
  simp_rw [permutation_word, smul_smul]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_comm]

/-- Skew symmetry and anticommutation make the two orientations of each pair
contribute equally. The diagonal contribution is zero. -/
lemma full_pair_sum_eq_two_omega (m : ℕ)
    (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) (hA : ∀ i j, A i j = -A j i) :
    (∑ i, ∑ j, A i j •
      (ExteriorAlgebra.ι ℝ (coordinateBasis (2*m) i) *
       ExteriorAlgebra.ι ℝ (coordinateBasis (2*m) j))) = (2 : ℝ) • omega A := by
  classical
  let t := fun i j : Fin (2*m) => A i j •
    (ExteriorAlgebra.ι ℝ (coordinateBasis (2*m) i) *
     ExteriorAlgebra.ι ℝ (coordinateBasis (2*m) j))
  have ht (i j : Fin (2*m)) : t i j = t j i := by
    dsimp [t]
    rw [hA i j, D05.M15.Exterior.generator_anticommutation]
    simp
  have hd (i : Fin (2*m)) : t i i = 0 := by simp [t]
  have hterm (i j : Fin (2*m)) : t i j =
      (if i < j then t i j else 0) + (if j < i then t j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hd]
    · simp [h, not_lt_of_gt h, ht i j]
  have hupper (i : Fin (2*m)) :
      (∑ j, if i < j then t i j else 0) = ∑ j ∈ Finset.Ioi i, t i j := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  change (∑ i, ∑ j, t i j) = _
  rw [show (∑ i, ∑ j, t i j) =
      ∑ i, ∑ j, ((if i < j then t i j else 0) +
        (if j < i then t j i else 0)) from
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then t j i else 0)]
  simp_rw [hupper]
  change omega A + omega A = (2 : ℝ) • omega A
  rw [two_smul ℝ]

/-- The ordered dual coordinate volume is nonzero, including degree zero. -/
lemma volume_ne_zero (m : ℕ) : volume m ≠ 0 := by
  intro h
  have hz : exteriorPower.ιMulti ℝ (2*m) (coordinateBasis (2*m)) = 0 :=
    Subtype.ext h
  have hc := congrArg
    (exteriorPower.alternatingMapLinearEquiv (coordinateBasis (2*m)).det) hz
  simp only [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Module.Basis.det_self, map_zero, one_ne_zero] at hc

/-- The signed formula satisfies the defining top-wedge identity. -/
theorem wedge_normalization : Specs.D05.M11.Pfaffian.wedge_normalization := by
  intro m A hA
  have h := full_pair_power_permutations m (coordinateBasis (2*m)) A
  rw [full_pair_sum_eq_two_omega m A hA, smul_pow] at h
  have hs := congrArg (fun x => ((2 : ℝ)^m * (Nat.factorial m : ℝ))⁻¹ • x) h
  rw [smul_smul, smul_smul] at hs
  have hc : (2^m * (Nat.factorial m : ℝ))⁻¹ * 2^m = (Nat.factorial m : ℝ)⁻¹ := by
    field_simp
  rw [hc] at hs
  exact hs

/-- The top-wedge identity uniquely determines the scalar. -/
theorem normalization_unique : Specs.D05.M11.Pfaffian.normalization_unique := by
  intro m A hA
  refine ⟨pfaffian A, wedge_normalization m A hA, ?_⟩
  intro p hp
  exact smul_left_injective ℝ (volume_ne_zero m)
    (hp.symm.trans (wedge_normalization m A hA))

theorem empty_pfaffian : Specs.D05.M11.Pfaffian.empty_pfaffian := by
  intro A
  simp [pfaffian_value, D05.Foundations.permutationSign, D05.Foundations.inversionCount]

theorem empty_normalization : Specs.D05.M11.Pfaffian.empty_normalization := by
  intro A
  exact ⟨pow_zero _, ExteriorAlgebra.ιMulti_zero_apply _⟩

theorem permutation_formula : Specs.D05.M11.Pfaffian.permutation_formula := by
  intro m A _
  simp only [pfaffian_value, one_div]

end D05.M11.Pfaffian
