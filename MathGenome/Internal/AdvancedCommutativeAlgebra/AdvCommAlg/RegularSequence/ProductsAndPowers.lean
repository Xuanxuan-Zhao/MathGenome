import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Concatenation
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.ExactReduction
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.ProductsAndPowers

/-! Products in a fixed coordinate and arbitrary positive powers (RK-09). -/
universe u v
open scoped Pointwise
open Function Submodule RingTheory.Sequence
namespace AdvCommAlg.RegularSequence
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Multiplication by b on representatives, from M/aM to M/abM. -/
private def productInclusion (a b : R) : QuotSMulTop a M →ₗ[R] QuotSMulTop (a * b) M :=
  (a • (⊤ : Submodule R M)).mapQ ((a * b) • ⊤) (LinearMap.lsmul R M b) (by
    intro m hm
    obtain ⟨t, _, rfl⟩ := (mem_smul_pointwise_iff_exists m a ⊤).mp hm
    change b • (a • t) ∈ (a * b) • (⊤ : Submodule R M)
    rw [smul_comm b a, ← mul_smul]
    exact smul_mem_pointwise_smul t (a * b) ⊤ trivial)

private theorem product_le (a b : R) :
    (a * b) • (⊤ : Submodule R M) ≤ b • ⊤ := by
  intro m hm
  obtain ⟨t, _, rfl⟩ := (mem_smul_pointwise_iff_exists m (a * b) ⊤).mp hm
  rw [mul_comm a b, mul_smul]
  exact smul_mem_pointwise_smul (a • t) b ⊤ trivial

private theorem productInclusion_injective (a b : R) (hb : IsSMulRegular M b) :
    Injective (productInclusion M a b) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro q hq
  change productInclusion M a b q = 0 at hq
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change (Submodule.Quotient.mk (b • m) : QuotSMulTop (a * b) M) = 0 at hq
  obtain ⟨t, _, ht⟩ := (mem_smul_pointwise_iff_exists (b • m) (a * b) ⊤).mp
    ((Submodule.Quotient.mk_eq_zero _).mp hq)
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine (mem_smul_pointwise_iff_exists m a ⊤).mpr ⟨t, trivial, ?_⟩
  apply hb
  simpa only [mul_smul, smul_comm a b] using ht

private theorem product_exact (a b : R) :
    Exact (productInclusion M a b) (Submodule.factor (product_le M a b)) := by
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  constructor
  · intro hm
    change (Submodule.Quotient.mk m : QuotSMulTop b M) = 0 at hm
    obtain ⟨t, _, ht⟩ := (mem_smul_pointwise_iff_exists m b ⊤).mp
      ((Submodule.Quotient.mk_eq_zero _).mp hm)
    exact ⟨Submodule.Quotient.mk t, congrArg Submodule.Quotient.mk ht⟩
  · rintro ⟨q, hq⟩
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← hq]
    change (Submodule.Quotient.mk (b • t) : QuotSMulTop b M) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (smul_mem_pointwise_smul t b ⊤ trivial)

private theorem weaklyRegular_mul_cons (a b : R) (s : List R)
    (ha : WeaklyRegular M (a :: s)) (hb : WeaklyRegular M (b :: s)) :
    WeaklyRegular M ((a * b) :: s) := by
  obtain ⟨ha, hsA⟩ := (isWeaklyRegular_cons_iff M a s).mp ha
  obtain ⟨hb, hsB⟩ := (isWeaklyRegular_cons_iff M b s).mp hb
  apply (isWeaklyRegular_cons_iff M (a * b) s).mpr
  refine ⟨ha.mul hb, ?_⟩
  exact weaklyRegular_extension s (productInclusion M a b)
    (Submodule.factor (product_le M a b)) (productInclusion_injective M a b hb)
    (product_exact M a b) (Submodule.factor_surjective _) hsA hsB

theorem weaklyRegular_mul (p s : List R) (a b : R)
    (ha : WeaklyRegular M (p ++ a :: s)) (hb : WeaklyRegular M (p ++ b :: s)) :
    WeaklyRegular M (p ++ (a * b) :: s) := by
  obtain ⟨hp, ha⟩ := (weaklyRegular_append_iff M p (a :: s)).mp ha
  obtain ⟨_, hb⟩ := (weaklyRegular_append_iff M p (b :: s)).mp hb
  exact (weaklyRegular_append_iff M p ((a * b) :: s)).mpr
    ⟨hp, weaklyRegular_mul_cons _ a b s ha hb⟩

/-- The ideal of the product list is contained in that of the list with a. -/
private theorem product_ideal_le (p s : List R) (a b : R) :
    Ideal.ofList (p ++ (a * b) :: s) ≤ Ideal.ofList (p ++ a :: s) := by
  simp only [Ideal.ofList_append, Ideal.ofList_cons]
  apply sup_le_sup_left
  apply sup_le_sup_right
  exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right a b)

theorem regular_mul (p s : List R) (a b : R)
    (ha : Regular M (p ++ a :: s)) (hb : Regular M (p ++ b :: s)) :
    Regular M (p ++ (a * b) :: s) := by
  refine ⟨weaklyRegular_mul M p s a b ha.toIsWeaklyRegular hb.toIsWeaklyRegular, ?_⟩
  apply Ne.symm
  apply ne_top_of_le_ne_top ha.top_ne_smul.symm
  apply Submodule.smul_mono_left
  exact product_ideal_le p s a b

/-- Iterating a fixed-coordinate multiplication rule gives every positive power. -/
private theorem coordinate_power_of_mul (P : List R → Prop)
    (hmul : ∀ (p s : List R) (a b : R),
      P (p ++ a :: s) → P (p ++ b :: s) → P (p ++ (a * b) :: s))
    (p s : List R) (a : R) (n : ℕ) (hn : 0 < n) (hx : P (p ++ a :: s)) :
    P (p ++ (a ^ n) :: s) := by
  induction n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n ih =>
    by_cases hn0 : n = 0
    · simpa [hn0] using hx
    · simpa only [pow_succ] using
        hmul p s (a ^ n) a (ih (Nat.pos_of_ne_zero hn0)) hx

/-- Iterate along the list, keeping already changed coordinates in the prefix. -/
private theorem powers_append_of_mul (P : List R → Prop)
    (hmul : ∀ (p s : List R) (a b : R),
      P (p ++ a :: s) → P (p ++ b :: s) → P (p ++ (a * b) :: s))
    (p x : List R) (n : ℕ → ℕ) (hn : ∀ i, i < x.length → 0 < n i)
    (hx : P (p ++ x)) : P (p ++ x.mapIdx (fun i a => a ^ n i)) := by
  induction x generalizing p n with
  | nil => simpa using hx
  | cons a x ih =>
    rw [List.mapIdx_cons]
    have hpow := coordinate_power_of_mul P hmul p x a (n 0)
      (hn 0 (Nat.zero_lt_succ _)) hx
    have ht := ih (p ++ [a ^ n 0]) (fun i => n (i + 1))
      (fun i hi => hn (i + 1) (Nat.succ_lt_succ hi))
      (by simpa only [List.append_assoc, List.singleton_append] using hpow)
    simpa only [List.append_assoc, List.singleton_append] using ht

theorem weaklyRegular_powers (x : List R) (n : ℕ → ℕ)
    (hn : ∀ i, i < x.length → 0 < n i) (hx : WeaklyRegular M x) :
    WeaklyRegular M (x.mapIdx fun i a => a ^ n i) := by
  simpa only [List.nil_append] using
    powers_append_of_mul (WeaklyRegular M) (weaklyRegular_mul M) [] x n hn hx

theorem regular_powers (x : List R) (n : ℕ → ℕ)
    (hn : ∀ i, i < x.length → 0 < n i) (hx : Regular M x) :
    Regular M (x.mapIdx fun i a => a ^ n i) := by
  simpa only [List.nil_append] using
    powers_append_of_mul (Regular M) (regular_mul M) [] x n hn hx

end AdvCommAlg.RegularSequence
