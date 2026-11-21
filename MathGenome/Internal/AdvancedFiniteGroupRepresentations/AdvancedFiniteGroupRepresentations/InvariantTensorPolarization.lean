import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.EndomorphismTensor
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.InvariantTensorPolarization

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

private theorem alternating_supersets {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) :
    (∑ J : Finset α, if I ⊆ J then (-1 : ℤ) ^ (Fintype.card α - J.card) else 0) =
      if I = Finset.univ then 1 else 0 := by
  classical
  calc
    _ = ∑ K : Finset α, if K ⊆ Iᶜ then (-1 : ℤ) ^ K.card else 0 := by
      apply Fintype.sum_bijective (fun J : Finset α => Jᶜ) compl_involutive.bijective
      intro J
      simp only [Finset.compl_subset_compl, Finset.card_compl]
    _ = ∑ K ∈ (Iᶜ).powerset, (-1 : ℤ) ^ K.card := by
      rw [← Finset.sum_filter]
      congr 1
      ext K
      simp
    _ = _ := by simp [Finset.sum_powerset_neg_one_pow_card]

variable (W : Type*) [AddCommGroup W] [Module ℂ W]

private theorem pureTensor_sum (n : ℕ) (T : Fin n → W) (J : Finset (Fin n)) :
    pureTensor W n (fun _ => ∑ j ∈ J, T j) =
      ∑ f : Fin n → Fin n, if Finset.univ.image f ⊆ J then
        pureTensor W n (fun i => T (f i)) else 0 := by
  classical
  change (PiTensorProduct.tprod ℂ) (fun _ => ∑ j ∈ J, T j) = _
  rw [MultilinearMap.map_sum_finset]
  rw [← Finset.sum_filter]
  congr 1
  ext f
  simp [Fintype.mem_piFinset, Finset.image_subset_iff]

/-- Inclusion-exclusion polarization, with the signs acting as integer scalars. -/
private theorem tensor_polarization_int (n : ℕ) (T : Fin n → W) :
    (∑ J : Finset (Fin n), (-1 : ℤ) ^ (n - J.card) •
      pureTensor W n (fun _ => ∑ j ∈ J, T j)) =
      ∑ σ : SymmetricGroup n, pureTensor W n (fun i => T (σ i)) := by
  classical
  calc
    _ = ∑ f : Fin n → Fin n,
        (if Finset.univ.image f = Finset.univ then (1 : ℤ) else 0) •
          pureTensor W n (fun i => T (f i)) := by
      simp_rw [pureTensor_sum W]
      simp_rw [← Int.cast_smul_eq_zsmul ℂ, Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      have h := alternating_supersets (Finset.univ.image f)
      simp only [Fintype.card_fin] at h
      rw [← h, Int.cast_sum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro J _
      split_ifs <;> simp_all
    _ = ∑ f ∈ (Finset.univ : Finset (Fin n → Fin n)).filter Function.Surjective,
        pureTensor W n (fun i => T (f i)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro f _
      have hf : Finset.univ.image f = Finset.univ ↔ Function.Surjective f := by
        constructor
        · intro h j
          have hj : j ∈ Finset.univ.image f := h.symm ▸ Finset.mem_univ j
          simpa using hj
        · intro h
          ext j
          simp [h j]
      simp [hf]
    _ = _ := by
      symm
      apply Finset.sum_bij (fun (σ : SymmetricGroup n) _ => (σ : Fin n → Fin n))
      · intro σ _
        simp [σ.surjective]
      · intro σ _ τ _ h
        exact Equiv.ext (congrFun h)
      · intro f hf
        have hs : Function.Surjective f := (Finset.mem_filter.mp hf).2
        exact ⟨Equiv.ofBijective f hs.bijective_of_finite, Finset.mem_univ _, rfl⟩
      · intro σ _
        rfl

/-- The source's polarization identity over the complex numbers. -/
theorem tensor_polarization (n : ℕ) (T : Fin n → W) :
    (∑ J : Finset (Fin n), (-1 : ℂ) ^ (n - J.card) •
      pureTensor W n (fun _ => ∑ j ∈ J, T j)) =
      ∑ σ : SymmetricGroup n, pureTensor W n (fun i => T (σ i)) := by
  simpa only [← Int.cast_smul_eq_zsmul ℂ, Int.cast_pow, Int.cast_neg, Int.cast_one]
    using tensor_polarization_int W n T

/-- Averaging over the symmetric group produces a fixed tensor. -/
theorem tensor_average_invariant (n : ℕ) (t : TensorPower W n) (τ : SymmetricGroup n) :
    slotOperator W n τ ((n.factorial : ℂ)⁻¹ • ∑ σ : SymmetricGroup n,
      slotOperator W n σ t) =
      (n.factorial : ℂ)⁻¹ • ∑ σ : SymmetricGroup n, slotOperator W n σ t := by
  classical
  rw [map_smul, map_sum]
  congr 1
  calc
    _ = ∑ σ : SymmetricGroup n, slotOperator W n (τ * σ) t := by
      apply Finset.sum_congr rfl
      intro σ _
      exact congrArg (fun L : Module.End ℂ (TensorPower W n) => L t)
        (slot_mul W n τ σ).symm
    _ = _ := Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)

/-- A fixed tensor equals its average; the scalar denominator is nonzero. -/
theorem tensor_average_eq_self (n : ℕ) (t : TensorPower W n)
    (ht : ∀ σ : SymmetricGroup n, slotOperator W n σ t = t) :
    (n.factorial : ℂ)⁻¹ • (∑ σ : SymmetricGroup n, slotOperator W n σ t) = t := by
  classical
  simp only [ht, Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero n

private theorem tensor_orbitSum_mem_span (n : ℕ) (t : TensorPower W n) :
    (∑ σ : SymmetricGroup n, slotOperator W n σ t) ∈
      Submodule.span ℂ (Set.range (fun T : W => pureTensor W n (fun _ => T))) := by
  classical
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c T =>
    change (∑ σ : SymmetricGroup n, slotOperator W n σ (c • pureTensor W n T)) ∈ _
    simp only [map_smul, ← Finset.smul_sum]
    apply Submodule.smul_mem
    have ho : (∑ σ : SymmetricGroup n, slotOperator W n σ (pureTensor W n T)) =
        ∑ σ : SymmetricGroup n, pureTensor W n (fun i => T (σ i)) := by
      simp only [slot_pureTensor]
      exact Fintype.sum_bijective (fun σ : SymmetricGroup n => σ⁻¹)
        inv_involutive.bijective _ _ (fun _ => rfl)
    rw [ho, ← tensor_polarization]
    apply Submodule.sum_mem
    intro J _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨∑ j ∈ J, T j, rfl⟩
  | add x y hx hy =>
    simp only [map_add, Finset.sum_add_distrib]
    exact Submodule.add_mem _ hx hy

/-- Fixed tensors are precisely the linear combinations of diagonal pure tensors. -/
theorem tensor_invariant_iff_mem_purePowerSpan (n : ℕ) (t : TensorPower W n) :
    (∀ σ : SymmetricGroup n, slotOperator W n σ t = t) ↔
      t ∈ Submodule.span ℂ (Set.range (fun T : W => pureTensor W n (fun _ => T))) := by
  constructor
  · intro ht
    rw [← tensor_average_eq_self W n t ht]
    exact Submodule.smul_mem _ _ (tensor_orbitSum_mem_span W n t)
  · intro ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨T, rfl⟩ := hx
      intro σ
      rw [slot_pureTensor]
    | zero => intro σ; exact map_zero _
    | add x y hx hy ihx ihy => intro σ; simp only [map_add, ihx σ, ihy σ]
    | smul c x hx ih => intro σ; simp only [map_smul, ih σ]

/-- Specialization to the original endomorphism tensor space, with its canonical fixed predicate. -/
theorem endomorphismTensor_invariants_span (V : Type*) [AddCommGroup V] [Module ℂ V]
    (n : ℕ) :
    {t : EndomorphismTensor V n | IsInvariantEndomorphismTensor V n t} =
      (Submodule.span ℂ (Set.range (fun T : Module.End ℂ V =>
        pureTensor (Module.End ℂ V) n (fun _ => T))) : Set (EndomorphismTensor V n)) := by
  ext t
  exact tensor_invariant_iff_mem_purePowerSpan (Module.End ℂ V) n t

end AdvancedFiniteGroupRepresentations
