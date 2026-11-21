import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.EulerProduct
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Partition.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.MultiplicativeInverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace FiniteCombinatorics.Partition

abbrev partitionCount : ℕ → ℕ := Specs.partitionCountValue
abbrev eulerFactor := Specs.eulerFactorValue
abbrev initialProduct := Specs.initialProductValue
abbrev eulerProduct := Specs.eulerProductValue

open PowerSeries Finset

/-- The coefficient of each factor counts the possible multiplicity of its part. -/
theorem eulerFactor_coeff : Specs.EulerFactorCoefficients := by
  intro R _ k n
  simp [Specs.eulerFactorValue, PowerSeries.coeff_expand]

/-- Each geometric factor is the two-sided unit inverse of `1-z^k`. -/
theorem eulerFactor_inverse : Specs.EulerFactorInverse := by
  intro R _ k
  have h : eulerFactor R k * (1 - X ^ (k : ℕ)) = 1 := by
    have he := congrArg (PowerSeries.expand (k : ℕ) k.ne_zero)
      (PowerSeries.mk_one_mul_one_sub_eq_one R)
    simpa [eulerFactor, Specs.eulerFactorValue, Pi.one_def] using he
  have hc : constantCoeff (1 - X ^ (k : ℕ) : PowerSeries R) = (↑(1 : Rˣ) : R) := by
    simp [k.ne_zero]
  have hi := (FiniteCombinatorics.Series.invOfUnit_two_sided _ 1 hc).1
  refine ⟨by simpa [mul_comm] using h, h, ?_⟩
  calc
    eulerFactor R k = eulerFactor R k *
        ((1 - X ^ (k : ℕ)) * invOfUnit (1 - X ^ (k : ℕ)) 1) := by rw [hi, mul_one]
    _ = invOfUnit (1 - X ^ (k : ℕ)) 1 := by rw [← mul_assoc, h, one_mul]

section Counting

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

/-- The expanded geometric series agrees with the form used by Mathlib's
partition generating function. The topology is only an auxiliary tool. -/
private theorem eulerFactor_eq_term {R : Type} [CommRing R]
    [TopologicalSpace R] [T2Space R] [IsTopologicalRing R] (i : ℕ) :
    eulerFactor R ⟨i + 1, Nat.succ_pos i⟩ =
      1 + ∑' j : ℕ, (1 : R) • X ^ ((i + 1) * (j + 1)) := by
  let k : ℕ+ := ⟨i + 1, Nat.succ_pos i⟩
  have hc : constantCoeff (X ^ (i + 1) : PowerSeries R) = 0 := by simp
  have hg : (∑' j : ℕ, (X : PowerSeries R) ^ ((i + 1) * j)) *
      (1 - X ^ (i + 1)) = 1 := by
    simpa [pow_mul] using tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hc
  have hsum : (∑' j : ℕ, (X : PowerSeries R) ^ ((i + 1) * j)) =
      1 + ∑' j : ℕ, (1 : R) • X ^ ((i + 1) * (j + 1)) := by
    rw [tsum_eq_zero_add' (by simpa only [one_smul] using
      Nat.Partition.summable_genFun_term (fun _ _ => (1 : R)) i)]
    simp
  rw [← hsum]
  have hi := (eulerFactor_inverse R k).1
  change (1 - X ^ (i + 1)) * eulerFactor R k = 1 at hi
  calc
    eulerFactor R k = ((∑' j : ℕ, X ^ ((i + 1) * j)) *
        (1 - X ^ (i + 1))) * eulerFactor R k := by rw [hg, one_mul]
    _ = ∑' j : ℕ, X ^ ((i + 1) * j) := by rw [mul_assoc, hi, mul_one]

open private aux_prod_coeff_eq_zero_of_notMem_range aux_prod_f_eq_prod_coeff
  from Mathlib.Combinatorics.Enumerative.Partition.GenFun

/-- A finite version of the Mathlib coefficient enumeration, valid as soon as
all positive parts at most the requested degree have been included. -/
private theorem coeff_product_terms {R : Type} [CommRing R]
    [TopologicalSpace R] [T2Space R] [IsTopologicalRing R]
    (n N : ℕ) (hn : n ≤ N) :
    coeff n (initialProduct R N) = (Fintype.card (Nat.Partition n) : R) := by
  classical
  let f : ℕ → ℕ → R := fun _ _ => 1
  let s := (range N).map (addRightEmbedding 1)
  have hs : Icc 1 n ⊆ s := by
    intro i hi
    simp only [mem_Icc] at hi
    simp only [s, mem_map, mem_range, addRightEmbedding, Function.Embedding.coeFn_mk]
    exact ⟨i - 1, by omega, by omega⟩
  have hs0 : 0 ∉ s := by simp [s]
  have hprod : initialProduct R N =
      ∏ i ∈ s, (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) := by
    simp only [initialProduct, Specs.initialProductValue, eulerFactor_eq_term]
    simp [s, f]
  rw [hprod, coeff_prod]
  have he : (∑ p : Nat.Partition n, p.parts.toFinsupp.prod f) =
      ∑ l ∈ s.finsuppAntidiag n,
        ∏ i ∈ s, coeff (l i) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) := by
    apply (sum_of_injOn Nat.Partition.toFinsuppAntidiag
      (Nat.Partition.toFinsuppAntidiag_injective n).injOn ?_ ?_ ?_)
    · intro p _
      exact mem_of_subset (finsuppAntidiag_mono hs _) p.toFinsuppAntidiag_mem_finsuppAntidiag
    · exact fun g hg hg' => aux_prod_coeff_eq_zero_of_notMem_range f hs0 hg
        (by simpa using hg')
    · exact fun p _ => aux_prod_f_eq_prod_coeff f p hs hs0
  rw [← he]
  simp [f, Finsupp.prod]

end Counting

/-- The list and multiset representations count the same actual partitions. -/
theorem partitionCount_eq_card (n : ℕ) :
    partitionCount n = Fintype.card (Nat.Partition n) := by
  rw [partitionCount, Specs.partitionCountValue,
    Nat.card_congr (mathlibEquiv n), Nat.card_eq_fintype_card]

/-- Finite initial products already give every coefficient through their length. -/
theorem initialProduct_coeff : Specs.InitialProductCoefficients := by
  intro R _ n N hn
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  rw [coeff_product_terms n N hn, ← partitionCount_eq_card]

/-- Stabilization holds at the explicit bound in the source, including degree zero. -/
theorem eulerProduct_stabilization : Specs.EulerProductStabilization := by
  intro R _ N M n hNM hnN
  constructor
  · rw [initialProduct_coeff R n M (hnN.trans hNM), initialProduct_coeff R n N hnN]
  · change coeff n (PowerSeries.mk _) = _
    rw [coeff_mk, initialProduct_coeff R n n le_rfl, initialProduct_coeff R n N hnN]

/-- Euler's partition product over the integers and rationals. -/
theorem euler_partition_product : Specs.EulerPartitionProduct := by
  constructor <;> apply PowerSeries.ext <;> intro n <;>
    simp only [coeff_mk, Specs.eulerProductValue, initialProduct_coeff _ n n le_rfl]

/-- The coefficient map transports every finite initial product and its
coefficientwise stabilized infinite product. -/
theorem eulerProduct_rational_map : Specs.EulerProductRationalMap := by
  constructor
  · intro N
    have hm : PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk fun _ => (1 : ℤ)) =
        PowerSeries.mk (fun _ => (1 : ℚ)) := by
      ext n
      simp
    simp [Specs.initialProductValue, Specs.eulerFactorValue, PowerSeries.map_expand, hm]
  · apply PowerSeries.ext
    intro n
    simp only [coeff_map, Specs.eulerProductValue, coeff_mk,
      initialProduct_coeff _ n n le_rfl]
    simp

end FiniteCombinatorics.Partition
