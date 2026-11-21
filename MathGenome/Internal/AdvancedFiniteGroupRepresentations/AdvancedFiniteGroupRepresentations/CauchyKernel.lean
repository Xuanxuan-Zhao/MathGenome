import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.PowerSumsAlternants
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CauchyKernel
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev CauchyAlphabet := Specs.AdvancedFiniteGroupRepresentations.CauchyAlphabet
abbrev cauchyBidegreeWeight := Specs.AdvancedFiniteGroupRepresentations.cauchyBidegreeWeight
abbrev xAlphabet := Specs.AdvancedFiniteGroupRepresentations.xAlphabet
abbrev yAlphabet := Specs.AdvancedFiniteGroupRepresentations.yAlphabet
abbrev pairedPowerSum := Specs.AdvancedFiniteGroupRepresentations.pairedPowerSum
abbrev pairedPartitionPowerSum := @Specs.AdvancedFiniteGroupRepresentations.pairedPartitionPowerSum
abbrev cauchyFactor := @Specs.AdvancedFiniteGroupRepresentations.cauchyFactor
abbrev cauchyKernel := Specs.AdvancedFiniteGroupRepresentations.cauchyKernel
abbrev cauchyPartitionCoefficient := Specs.AdvancedFiniteGroupRepresentations.cauchyPartitionCoefficient
abbrev cauchyPartitionSeries := Specs.AdvancedFiniteGroupRepresentations.cauchyPartitionSeries

/-- Formal geometric series over an arbitrary commutative ring. -/
def geometricSeries {R : Type*} [CommRing R] (a : R) : PowerSeries R :=
  PowerSeries.mk fun n => a ^ n

@[simp] theorem coeff_geometricSeries {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    PowerSeries.coeff n (geometricSeries a) = a ^ n :=
  PowerSeries.coeff_mk _ _

@[simp] theorem constantCoeff_geometricSeries {R : Type*} [CommRing R] (a : R) :
    PowerSeries.constantCoeff (geometricSeries a) = 1 := by
  simp [geometricSeries, PowerSeries.constantCoeff_mk]

theorem geometricSeries_mul_one_sub {R : Type*} [CommRing R] (a : R) :
    geometricSeries a * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [mul_sub, mul_one, ← mul_assoc, map_sub, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_mul_C, coeff_geometricSeries, PowerSeries.coeff_one,
      Nat.add_one_ne_zero, ite_false, pow_succ, sub_self]

theorem one_sub_mul_geometricSeries {R : Type*} [CommRing R] (a : R) :
    (1 - PowerSeries.C a * PowerSeries.X) * geometricSeries a = 1 := by
  rw [mul_comm, geometricSeries_mul_one_sub]

/-- Differentiating a geometric factor without assuming that its coefficient
ring is a field. -/
theorem derivative_geometricSeries {R : Type*} [CommRing R] (a : R) :
    PowerSeries.derivative (geometricSeries a) =
      geometricSeries a * (PowerSeries.C a * geometricSeries a) := by
  have h := congrArg (fun f : PowerSeries R => PowerSeries.derivative f)
    (geometricSeries_mul_one_sub a)
  simp only [Derivation.leibniz, Derivation.map_sub, PowerSeries.derivative_one,
    PowerSeries.derivative_C, PowerSeries.derivative_X, smul_eq_mul, mul_one,
    mul_zero, add_zero, zero_sub] at h
  have hd : (1 - PowerSeries.C a * PowerSeries.X) *
      PowerSeries.derivative (geometricSeries a) =
      geometricSeries a * PowerSeries.C a := by
    rw [mul_neg, neg_add_eq_zero] at h
    exact h.symm
  calc
    PowerSeries.derivative (geometricSeries a) =
        geometricSeries a * ((1 - PowerSeries.C a * PowerSeries.X) *
          PowerSeries.derivative (geometricSeries a)) := by
      rw [← mul_assoc, geometricSeries_mul_one_sub, one_mul]
    _ = geometricSeries a * (PowerSeries.C a * geometricSeries a) := by
      rw [hd, mul_comm (geometricSeries a) (PowerSeries.C a)]

/-- Each factor used in the kernel is the actual formal inverse of its printed
linear denominator. -/
theorem cauchyFactor_mul_denominator {r : ℕ} (i j : Fin r) :
    cauchyFactor i j *
      (1 - PowerSeries.C ((MvPolynomial.X (Sum.inl i) : CauchyAlphabet r) *
        MvPolynomial.X (Sum.inr j)) * PowerSeries.X) = 1 :=
  geometricSeries_mul_one_sub _

@[simp] theorem cauchyKernel_constantCoeff (r : ℕ) :
    PowerSeries.constantCoeff (cauchyKernel r) = 1 := by
  simp [cauchyKernel, Specs.AdvancedFiniteGroupRepresentations.cauchyKernel,
    Specs.AdvancedFiniteGroupRepresentations.cauchyFactor,
    PowerSeries.constantCoeff_mk]

/-- The paired power sum is the sum of all `(x_i*y_j)^k`. -/
theorem pairedPowerSum_eq_sum (r k : ℕ) :
    pairedPowerSum r k = ∑ i : Fin r, ∑ j : Fin r,
      ((MvPolynomial.X (Sum.inl i) : CauchyAlphabet r) * MvPolynomial.X (Sum.inr j)) ^ k := by
  simp only [pairedPowerSum, Specs.AdvancedFiniteGroupRepresentations.pairedPowerSum,
    Specs.AdvancedFiniteGroupRepresentations.xAlphabet,
    Specs.AdvancedFiniteGroupRepresentations.yAlphabet,
    Specs.AdvancedFiniteGroupRepresentations.powerSum, map_sum, map_pow,
    MvPolynomial.rename_X, Finset.sum_mul, Finset.mul_sum, mul_pow]
  rw [Finset.sum_comm]

/-- The two-alphabet partition monomial is the product of paired power sums
with the full cycle multiplicities. -/
theorem pairedPartitionPowerSum_eq_prod {n : ℕ} (r : ℕ) (ν : Partition n) :
    pairedPartitionPowerSum r ν =
      ∏ j ∈ ν.parts.toFinset, pairedPowerSum r j ^ cycleMultiplicity ν j := by
  simp only [pairedPartitionPowerSum,
    Specs.AdvancedFiniteGroupRepresentations.pairedPartitionPowerSum,
    Specs.AdvancedFiniteGroupRepresentations.partitionPowerSum,
    map_prod, map_pow, pairedPowerSum,
    Specs.AdvancedFiniteGroupRepresentations.pairedPowerSum,
    mul_pow, Finset.prod_mul_distrib]

/-- The denominator in every partition summand is nonzero. -/
theorem zFactor_pos {n : ℕ} (ν : Partition n) : 0 < zFactor ν := by
  apply Finset.prod_pos
  intro j hj
  exact Nat.mul_pos (Nat.pow_pos (ν.parts_pos (Multiset.mem_toFinset.mp hj)))
    (Nat.factorial_pos _)

@[simp] theorem cauchyPartitionCoefficient_zero (r : ℕ) :
    cauchyPartitionCoefficient r 0 = 1 := by
  have h : ∀ ν : Partition 0, pairedPartitionPowerSum r ν = 1 := by
    intro ν
    rw [zero_partition_unique ν]
    simp [pairedPartitionPowerSum,
      Specs.AdvancedFiniteGroupRepresentations.pairedPartitionPowerSum,
      empty_partitionPowerSum r]
  simp [cauchyPartitionCoefficient,
    Specs.AdvancedFiniteGroupRepresentations.cauchyPartitionCoefficient,
    h, Specs.AdvancedFiniteGroupRepresentations.zFactor,
    Specs.AdvancedFiniteGroupRepresentations.centralizerFactor]

@[simp] theorem cauchyPartitionSeries_constantCoeff (r : ℕ) :
    PowerSeries.constantCoeff (cauchyPartitionSeries r) = 1 := by
  exact cauchyPartitionCoefficient_zero r

/-- A finite product whose factors satisfy logarithmic differential equations
satisfies the equation with the sum of their logarithmic derivatives. -/
theorem derivative_prod_of_logDerivative {R ι : Type*} [CommRing R]
    (s : Finset ι) (f a : ι → PowerSeries R)
    (h : ∀ i ∈ s, PowerSeries.derivative (f i) = f i * a i) :
    PowerSeries.derivative (∏ i ∈ s, f i) =
      (∏ i ∈ s, f i) * ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Derivation.leibniz,
      h i (Finset.mem_insert_self i s), ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
    simp only [smul_eq_mul]
    ring

/-- The logarithmic derivative of the geometric kernel is the paired power-sum
series. This identity is entirely formal. -/
theorem derivative_cauchyKernel (r : ℕ) :
    PowerSeries.derivative (cauchyKernel r) = cauchyKernel r *
      PowerSeries.mk (fun n => pairedPowerSum r (n + 1)) := by
  let a (i j : Fin r) : CauchyAlphabet r :=
    MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr j)
  have hg (i j : Fin r) : cauchyFactor i j = geometricSeries (a i j) := rfl
  have hd (i : Fin r) :
      PowerSeries.derivative (∏ j : Fin r, cauchyFactor i j) =
      (∏ j : Fin r, cauchyFactor i j) *
        ∑ j : Fin r, PowerSeries.C (a i j) * cauchyFactor i j := by
    apply derivative_prod_of_logDerivative
    intro j _
    rw [hg]
    exact derivative_geometricSeries _
  have hall := derivative_prod_of_logDerivative Finset.univ
    (fun i : Fin r => ∏ j : Fin r, cauchyFactor i j)
    (fun i : Fin r => ∑ j : Fin r, PowerSeries.C (a i j) * cauchyFactor i j)
    (fun i _ => hd i)
  change PowerSeries.derivative (∏ i : Fin r, ∏ j : Fin r, cauchyFactor i j) = _
  rw [hall]
  congr 1
  apply PowerSeries.ext
  intro n
  simp only [map_sum, PowerSeries.coeff_C_mul, hg, coeff_geometricSeries,
    PowerSeries.coeff_mk, pairedPowerSum_eq_sum, pow_succ']
  rfl

/-- Uniqueness of the formal initial-value problem `f' = f*a`. -/
theorem eq_of_derivative_eq_mul {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (a f g : PowerSeries R)
    (hf : PowerSeries.derivative f = f * a)
    (hg : PowerSeries.derivative g = g * a)
    (h0 : PowerSeries.constantCoeff f = PowerSeries.constantCoeff g) : f = g := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
    | succ n =>
      have hh : PowerSeries.coeff n (PowerSeries.derivative f) =
          PowerSeries.coeff n (PowerSeries.derivative g) := by
        rw [hf, hg, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        apply Finset.sum_congr rfl
        intro ij hij
        rw [ih ij.1 (by have := Finset.mem_antidiagonal.mp hij; omega)]
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at hh
      exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n) hh

/-- Effect on the multiplicity-factorial product of adjoining one part. -/
theorem multiplicityFactorialProduct_cons (m : Multiset ℕ) (j : ℕ) :
    (∏ k ∈ (j ::ₘ m).toFinset, ((j ::ₘ m).count k).factorial) =
      (m.count j + 1) * ∏ k ∈ m.toFinset, (m.count k).factorial := by
  have hext : (∏ k ∈ insert j m.toFinset, (m.count k).factorial) =
      ∏ k ∈ m.toFinset, (m.count k).factorial := by
    by_cases hj : j ∈ m.toFinset
    · rw [Finset.insert_eq_of_mem hj]
    · rw [Finset.prod_insert hj]
      simp [Multiset.count_eq_zero.mpr (by simpa using hj)]
  have hpoint (k : ℕ) : ((j ::ₘ m).count k).factorial =
      (if k = j then m.count j + 1 else 1) * (m.count k).factorial := by
    by_cases h : k = j
    · subst k
      simp [Nat.factorial_succ]
    · simp [Multiset.count_cons_of_ne h, h]
  simp_rw [Multiset.toFinset_cons, hpoint]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', ite_eq_left (Finset.mem_insert_self _ _), hext]

/-- Adjoining a part `j` multiplies `z` by `j` times its new multiplicity. -/
theorem zFactor_cons {n m : ℕ} (ν : Partition n) (μ : Partition m) (j : ℕ)
    (h : ν.parts = j ::ₘ μ.parts) :
    zFactor ν = j * (μ.parts.count j + 1) * zFactor μ := by
  have hz {k : ℕ} (p : Partition k) : zFactor p =
      p.parts.prod * ∏ i ∈ p.parts.toFinset, (p.parts.count i).factorial := by
    change (∏ i ∈ p.parts.toFinset, i ^ p.parts.count i * (p.parts.count i).factorial) = _
    rw [Finset.prod_mul_distrib, ← Finset.prod_multiset_count]
  rw [hz ν, hz μ, h, Multiset.prod_cons, multiplicityFactorialProduct_cons]
  ring

/-- Adjoining a part contributes one corresponding paired power sum. -/
theorem pairedPartitionPowerSum_cons {n m : ℕ} (r : ℕ)
    (ν : Partition n) (μ : Partition m) (j : ℕ)
    (h : ν.parts = j ::ₘ μ.parts) :
    pairedPartitionPowerSum r ν = pairedPowerSum r j * pairedPartitionPowerSum r μ := by
  rw [pairedPartitionPowerSum_eq_prod, pairedPartitionPowerSum_eq_prod]
  change (∏ k ∈ ν.parts.toFinset, pairedPowerSum r k ^ ν.parts.count k) = _
  rw [← Finset.prod_multiset_map_count, h, Multiset.map_cons, Multiset.prod_cons,
    Finset.prod_multiset_map_count]
  rfl

/-- A partition of `n-j` with an additional positive part `j` is a partition of `n`. -/
def addPartitionPart {n : ℕ} (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
    (μ : Partition (n - j)) : Partition n where
  parts := j ::ₘ μ.parts
  parts_pos := by
    intro k hk
    rcases Multiset.mem_cons.mp hk with h | h
    · simpa [h] using hj
    · exact μ.parts_pos h
  parts_sum := by rw [Multiset.sum_cons, μ.parts_sum]; omega

/-- Remove one specified occurring part. -/
def erasePartitionPart {n : ℕ} (ν : Partition n) (j : ℕ) (hj : j ∈ ν.parts) :
    Partition (n - j) where
  parts := ν.parts.erase j
  parts_pos := fun hk => ν.parts_pos (Multiset.mem_of_mem_erase hk)
  parts_sum := by
    have hs := congrArg Multiset.sum (Multiset.cons_erase hj)
    rw [Multiset.sum_cons, ν.parts_sum] at hs
    omega

/-- The multiplicity-weighted summand is unchanged by distinguishing and
removing one part, except for its paired power-sum factor. -/
theorem cauchySummand_cons {n m : ℕ} (r : ℕ)
    (ν : Partition n) (μ : Partition m) (j : ℕ) (hj : 0 < j)
    (h : ν.parts = j ::ₘ μ.parts) :
    ((j * (μ.parts.count j + 1) : ℕ) : ℂ) •
        ((zFactor ν : ℂ)⁻¹ • pairedPartitionPowerSum r ν) =
      pairedPowerSum r j * ((zFactor μ : ℂ)⁻¹ • pairedPartitionPowerSum r μ) := by
  rw [smul_smul, pairedPartitionPowerSum_cons r ν μ j h, mul_smul_comm]
  congr 1
  have hd : ((j * (μ.parts.count j + 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.mul_pos hj (by omega))
  have hz : (zFactor μ : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (zFactor_pos μ)
  have he : (zFactor ν : ℂ) =
      ((j * (μ.parts.count j + 1) : ℕ) : ℂ) * (zFactor μ : ℂ) := by
    exact_mod_cast zFactor_cons ν μ j h
  rw [he]
  field_simp

/-- Distinguishing an occurring part and deleting it is inverse to adjoining it. -/
def partitionWithPartEquiv (n j : ℕ) (hj : 0 < j) (hjn : j ≤ n) :
    Partition (n - j) ≃ {ν : Partition n // j ∈ ν.parts} where
  toFun μ := ⟨addPartitionPart j hj hjn μ, Multiset.mem_cons_self _ _⟩
  invFun ν := erasePartitionPart ν.val j ν.property
  left_inv μ := by
    apply Nat.Partition.ext
    exact Multiset.erase_cons_head _ _
  right_inv ν := by
    apply Subtype.ext
    apply Nat.Partition.ext
    exact Multiset.cons_erase ν.property

/-- Summing the distinguished-`j` contributions is equivalent to summing all
partitions of `n-j`. -/
theorem cauchySummand_sum_multiplicity (r n j : ℕ) (hj : 0 < j) (hjn : j ≤ n) :
    (∑ ν : Partition n, ((j * ν.parts.count j : ℕ) : ℂ) •
      ((zFactor ν : ℂ)⁻¹ • pairedPartitionPowerSum r ν)) =
      pairedPowerSum r j * cauchyPartitionCoefficient r (n - j) := by
  classical
  let w (ν : Partition n) : CauchyAlphabet r :=
    ((j * ν.parts.count j : ℕ) : ℂ) •
      ((zFactor ν : ℂ)⁻¹ • pairedPartitionPowerSum r ν)
  have hw : (∑ ν : Partition n, w ν) = ∑ ν ∈ Finset.univ.filter
      (fun ν : Partition n => j ∈ ν.parts), w ν := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro ν _ hν
    have hjν : j ∉ ν.parts := by simpa using hν
    simp [w, Multiset.count_eq_zero.mpr hjν]
  change (∑ ν : Partition n, w ν) = _
  rw [hw, Finset.sum_subtype (p := fun ν : Partition n => j ∈ ν.parts) _ (by simp)]
  rw [← (partitionWithPartEquiv n j hj hjn).sum_comp (fun ν => w ν.val)]
  simp only [cauchyPartitionCoefficient,
    Specs.AdvancedFiniteGroupRepresentations.cauchyPartitionCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  change ((j * (j ::ₘ μ.parts).count j : ℕ) : ℂ) •
    ((zFactor (addPartitionPart j hj hjn μ) : ℂ)⁻¹ •
      pairedPartitionPowerSum r (addPartitionPart j hj hjn μ)) = _
  rw [Multiset.count_cons_self]
  exact cauchySummand_cons r _ μ j hj rfl

/-- The sum of size times multiplicity is the degree, including fixed points. -/
theorem partition_sum_size_mul_count {n : ℕ} (ν : Partition n) :
    (∑ j ∈ Finset.Icc 1 n, j * ν.parts.count j) = n := by
  have hsub : ν.parts.toFinset ⊆ Finset.Icc 1 n := by
    intro j hj
    have hmem := Multiset.mem_toFinset.mp hj
    exact Finset.mem_Icc.mpr ⟨ν.parts_pos hmem, ν.le_of_mem_parts hmem⟩
  calc
    (∑ j ∈ Finset.Icc 1 n, j * ν.parts.count j) =
        ∑ j ∈ ν.parts.toFinset, j * ν.parts.count j := by
      symm
      apply Finset.sum_subset hsub
      intro j _ hj
      simp [Multiset.count_eq_zero.mpr (by simpa using hj)]
    _ = n := by
      simpa [smul_eq_mul, mul_comm] using
        (Finset.sum_multiset_map_count ν.parts (fun j => j)).symm.trans (by simpa using ν.parts_sum)

/-- The partition coefficients satisfy the Newton recurrence, proved by
summing over a distinguished part and then deleting that part. -/
theorem cauchyPartitionCoefficient_recurrence (r n : ℕ) :
    (n : ℂ) • cauchyPartitionCoefficient r n =
      ∑ j ∈ Finset.Icc 1 n, pairedPowerSum r j * cauchyPartitionCoefficient r (n - j) := by
  classical
  change (n : ℂ) • (∑ ν : Partition n, (zFactor ν : ℂ)⁻¹ •
    pairedPartitionPowerSum r ν) = _
  rw [Finset.smul_sum]
  calc
    (∑ ν : Partition n, (n : ℂ) • ((zFactor ν : ℂ)⁻¹ • pairedPartitionPowerSum r ν)) =
        ∑ ν : Partition n, ∑ j ∈ Finset.Icc 1 n,
          ((j * ν.parts.count j : ℕ) : ℂ) •
            ((zFactor ν : ℂ)⁻¹ • pairedPartitionPowerSum r ν) := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [← Finset.sum_smul, ← Nat.cast_sum, partition_sum_size_mul_count]
    _ = ∑ j ∈ Finset.Icc 1 n, ∑ ν : Partition n,
          ((j * ν.parts.count j : ℕ) : ℂ) •
            ((zFactor ν : ℂ)⁻¹ • pairedPartitionPowerSum r ν) := Finset.sum_comm
    _ = ∑ j ∈ Finset.Icc 1 n,
        pairedPowerSum r j * cauchyPartitionCoefficient r (n - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact cauchySummand_sum_multiplicity r n j
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2

/-- The partition series has the same logarithmic differential equation as
the geometric kernel. -/
theorem derivative_cauchyPartitionSeries (r : ℕ) :
    PowerSeries.derivative (cauchyPartitionSeries r) = cauchyPartitionSeries r *
      PowerSeries.mk (fun n => pairedPowerSum r (n + 1)) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    cauchyPartitionSeries, Specs.AdvancedFiniteGroupRepresentations.cauchyPartitionSeries,
    PowerSeries.coeff_mk]
  have hscalar : cauchyPartitionCoefficient r (n + 1) * ((n : CauchyAlphabet r) + 1) =
      (n + 1 : ℂ) • cauchyPartitionCoefficient r (n + 1) := by
    simp [Algebra.smul_def, mul_comm]
  rw [hscalar]
  have hc := cauchyPartitionCoefficient_recurrence r (n + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hc
  rw [hc]
  symm
  apply Finset.sum_bij (fun ij _ => ij.2 + 1)
  · intro ij hij
    have hs := Finset.mem_antidiagonal.mp hij
    exact Finset.mem_Icc.mpr (by omega)
  · intro ij hij kl hkl heq
    have hs := Finset.mem_antidiagonal.mp hij
    have ht := Finset.mem_antidiagonal.mp hkl
    apply Prod.ext <;> omega
  · intro j hj
    refine ⟨(n + 1 - j, j - 1), ?_, ?_⟩
    · apply Finset.mem_antidiagonal.mpr
      have := Finset.mem_Icc.mp hj
      omega
    · have := Finset.mem_Icc.mp hj
      dsimp
      omega
  · intro ij hij
    have hs := Finset.mem_antidiagonal.mp hij
    have he : n + 1 - (ij.2 + 1) = ij.1 := by omega
    rw [he, mul_comm]

/-- FR-C02, first Cauchy identity. -/
theorem cauchy_identity (r : ℕ) (_hr : 1 ≤ r) :
    cauchyKernel r = cauchyPartitionSeries r := by
  apply eq_of_derivative_eq_mul (PowerSeries.mk (fun n => pairedPowerSum r (n + 1)))
  · exact derivative_cauchyKernel r
  · exact derivative_cauchyPartitionSeries r
  · rw [cauchyKernel_constantCoeff, cauchyPartitionSeries_constantCoeff]

/-- The identity in each common degree is a finite polynomial equality. -/
theorem cauchy_identity_degree (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    PowerSeries.coeff n (cauchyKernel r) =
      ∑ ν : Partition n, (zFactor ν : ℂ)⁻¹ • pairedPartitionPowerSum r ν := by
  rw [cauchy_identity r hr]
  exact PowerSeries.coeff_mk _ _

/-- Each factor contributes equal degrees in the two alphabets. -/
theorem pairedPowerSum_bihomogeneous (r k : ℕ) :
    (pairedPowerSum r k).IsWeightedHomogeneous (cauchyBidegreeWeight r) (k, k) := by
  rw [pairedPowerSum_eq_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i _
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j _
  have h := ((MvPolynomial.isWeightedHomogeneous_X (R := ℂ)
    (cauchyBidegreeWeight r) (Sum.inl i)).mul
      (MvPolynomial.isWeightedHomogeneous_X (R := ℂ)
        (cauchyBidegreeWeight r) (Sum.inr j))).pow k
  simpa [cauchyBidegreeWeight, Specs.AdvancedFiniteGroupRepresentations.cauchyBidegreeWeight] using h

/-- The upstream partition degree is preserved independently in both alphabets. -/
theorem pairedPartitionPowerSum_bihomogeneous {n : ℕ} (r : ℕ) (ν : Partition n) :
    (pairedPartitionPowerSum r ν).IsWeightedHomogeneous (cauchyBidegreeWeight r) (n, n) := by
  rw [pairedPartitionPowerSum_eq_prod]
  have h := MvPolynomial.IsWeightedHomogeneous.prod ν.parts.toFinset
    (fun j => pairedPowerSum r j ^ cycleMultiplicity ν j)
    (fun j => ν.parts.count j • (j, j))
    (fun j _ => (pairedPowerSum_bihomogeneous r j).pow (ν.parts.count j))
  have hs : (∑ j ∈ ν.parts.toFinset, ν.parts.count j • (j, j)) = (n, n) := by
    have hsum : (∑ j ∈ ν.parts.toFinset, ν.parts.count j * j) = n := by
      simpa [smul_eq_mul] using
        (Finset.sum_multiset_map_count ν.parts (fun j => j)).symm.trans (by simpa using ν.parts_sum)
    have hp := congrArg (fun k : ℕ => (k, k)) hsum
    simpa [← prod_mk_sum] using hp
  rwa [hs] at h

/-- This makes the degreewise interpretation explicit: the coefficient of
`t^n` is bihomogeneous of degree `(n,n)`. -/
theorem cauchyPartitionCoefficient_bihomogeneous (r n : ℕ) :
    (cauchyPartitionCoefficient r n).IsWeightedHomogeneous (cauchyBidegreeWeight r) (n, n) := by
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ν _
  simpa only [MvPolynomial.smul_eq_C_mul] using
    (pairedPartitionPowerSum_bihomogeneous r ν).C_mul (zFactor ν : ℂ)⁻¹

/-- The left-hand side of the Cauchy identity is the formal inverse of the
product of the printed denominators. -/
theorem cauchyKernel_mul_denominator (r : ℕ) :
    cauchyKernel r * (∏ i : Fin r, ∏ j : Fin r,
      (1 - PowerSeries.C ((MvPolynomial.X (Sum.inl i) : CauchyAlphabet r) *
        MvPolynomial.X (Sum.inr j)) * PowerSeries.X)) = 1 := by
  change (∏ i : Fin r, ∏ j : Fin r, cauchyFactor i j) * _ = _
  rw [← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib, cauchyFactor_mul_denominator]
  simp

end AdvancedFiniteGroupRepresentations
