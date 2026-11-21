import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CauchyKernel
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.AlternatingCauchyKernel
import Mathlib.Order.WellFounded
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace AdvancedFiniteGroupRepresentations

abbrev shiftedPartition := @Specs.AdvancedFiniteGroupRepresentations.shiftedPartition
abbrev staircaseDegree := Specs.AdvancedFiniteGroupRepresentations.staircaseDegree
abbrev partitionAlternant := @Specs.AdvancedFiniteGroupRepresentations.partitionAlternant
abbrev pairedPartitionAlternant := @Specs.AdvancedFiniteGroupRepresentations.pairedPartitionAlternant
abbrev alternatingPartitionCoefficient :=
  Specs.AdvancedFiniteGroupRepresentations.alternatingPartitionCoefficient
abbrev alternatingPartitionSeries :=
  Specs.AdvancedFiniteGroupRepresentations.alternatingPartitionSeries
abbrev pairedVandermonde := Specs.AdvancedFiniteGroupRepresentations.pairedVandermonde
abbrev alternatingCauchyKernel := Specs.AdvancedFiniteGroupRepresentations.alternatingCauchyKernel
abbrev pairedNaturalCoefficient := @Specs.AdvancedFiniteGroupRepresentations.pairedNaturalCoefficient

/-- Weakly decreasing rows become strictly decreasing after adding δ. -/
theorem shiftedPartition_strictAnti {n r : ℕ} (ν : Partition n) :
    StrictAnti (shiftedPartition r ν) := by
  intro i j hij
  have hr := rowLength_antitone ν (show i.val ≤ j.val by omega)
  have hi := i.isLt
  have hj := j.isLt
  change rowLength ν j.val + (r - 1 - j.val) <
    rowLength ν i.val + (r - 1 - i.val)
  have hij' : i.val < j.val := hij
  omega

/-- Equality of padded rows determines the full shape under the row cutoff. -/
theorem diagram_eq_of_shiftedPartition_eq {n m r : ℕ}
    (lam : Partition n) (μ : Partition m) (hlam : length lam ≤ r) (hμ : length μ ≤ r)
    (h : shiftedPartition r lam = shiftedPartition r μ) : diagram lam = diagram μ := by
  have he : ∀ i, rowLength lam i = rowLength μ i := by
    intro i
    by_cases hi : i < r
    · have hh := congrFun h (⟨i, hi⟩ : Fin r)
      exact Nat.add_right_cancel hh
    · rw [rowLength_zero_of_length_le lam i (by omega),
          rowLength_zero_of_length_le μ i (by omega)]
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i, j⟩
  change (i,j) ∈ cells lam ↔ (i,j) ∈ cells μ
  rw [cell_iff, cell_iff, he]

/-- Reindex a determinant term so that each variable has its own exponent. -/
theorem alternant_eq_sum_monomial {r : ℕ} (b : Fin r → ℕ) :
    alternant b = ∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ •
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => b (σ.symm i))) (1 : ℂ) := by
  classical
  rw [alternant, Specs.AdvancedFiniteGroupRepresentations.alternant, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  change (∏ i : Fin r, (MvPolynomial.X (σ i) : Alphabet r) ^ b i) = _
  calc
    _ = ∏ i : Fin r, (MvPolynomial.X i : Alphabet r) ^ b (σ.symm i) := by
      apply Fintype.prod_equiv σ
      intro i
      simp
    _ = _ := by
      rw [MvPolynomial.prod_X_pow]
      have he : Finsupp.indicator (Finset.univ : Finset (Fin r))
          (fun i _ => b (σ.symm i)) =
          Finsupp.equivFunOnFinite.symm (fun i => b (σ.symm i)) := by
        ext i
        simp
      rw [he]

/-- An ordered set of exponents has only its own ordered monomial in any
alternant with strictly decreasing column exponents. -/
theorem naturalCoefficient_alternant {r : ℕ} (a b : Fin r → ℕ)
    (ha : StrictAnti a) (hb : StrictAnti b) :
    naturalCoefficient a (alternant b) = if a = b then 1 else 0 := by
  classical
  rw [alternant_eq_sum_monomial]
  change (∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ •
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => b (σ.symm i))) (1 : ℂ)).coeff
      (Finsupp.equivFunOnFinite.symm a) = _
  rw [MvPolynomial.coeff_sum]
  have he (σ : Equiv.Perm (Fin r)) :
      Finsupp.equivFunOnFinite.symm (fun i => b (σ.symm i)) =
        Finsupp.equivFunOnFinite.symm a ↔ a = b ∧ σ = 1 := by
    constructor
    · intro h
      have hh : (fun i => b (σ.symm i)) = a := Finsupp.equivFunOnFinite.symm.injective h
      have hr : Set.range a = Set.range b := by
        rw [← hh]
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨σ.symm i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨σ i, by simp⟩
      have hab : a = b := (ha.range_inj_of_wellFoundedGT hb).mp hr
      refine ⟨hab, ?_⟩
      apply Equiv.ext
      intro i
      have hi := congrFun hh (σ i)
      simp only [Equiv.symm_apply_apply, hab] at hi
      exact (hb.injective hi).symm
    · rintro ⟨rfl, rfl⟩
      rfl
  simp_rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, he]
  by_cases h : a = b <;> simp [h]

/-- Coefficients of a product in disjoint alphabets factor. -/
theorem pairedNaturalCoefficient_mul {r : ℕ} (a b : Fin r → ℕ)
    (p q : Alphabet r) :
    pairedNaturalCoefficient a b (xAlphabet r p * yAlphabet r q) =
      naturalCoefficient a p * naturalCoefficient b q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p p' hp hp' =>
    simp_all [pairedNaturalCoefficient,
      Specs.AdvancedFiniteGroupRepresentations.pairedNaturalCoefficient,
      naturalCoefficient, Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient,
      map_add, add_mul]
  | monomial u c =>
    induction q using MvPolynomial.induction_on' with
    | add q q' hq hq' =>
      simp_all [pairedNaturalCoefficient,
        Specs.AdvancedFiniteGroupRepresentations.pairedNaturalCoefficient,
        naturalCoefficient, Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient,
        map_add, mul_add]
    | monomial v d =>
      have he : u.mapDomain Sum.inl + v.mapDomain Sum.inr =
          Finsupp.equivFunOnFinite.symm (Sum.elim a b) ↔
          u = Finsupp.equivFunOnFinite.symm a ∧
          v = Finsupp.equivFunOnFinite.symm b := by
        rw [← Finsupp.sumElim_eq_add]
        constructor
        · intro h
          constructor
          · ext i
            exact congrArg (fun f : Fin r ⊕ Fin r →₀ ℕ => f (.inl i)) h
          · ext i
            exact congrArg (fun f : Fin r ⊕ Fin r →₀ ℕ => f (.inr i)) h
        · rintro ⟨rfl, rfl⟩
          ext (i | i) <;> rfl
      simp only [pairedNaturalCoefficient,
        Specs.AdvancedFiniteGroupRepresentations.pairedNaturalCoefficient,
        xAlphabet, Specs.AdvancedFiniteGroupRepresentations.xAlphabet,
        yAlphabet, Specs.AdvancedFiniteGroupRepresentations.yAlphabet,
        naturalCoefficient, Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient,
        MvPolynomial.rename_monomial, MvPolynomial.monomial_mul_monomial,
        MvPolynomial.coeff_monomial, he]
      split_ifs <;> simp_all

/-- The coefficient in a product of two alternants, before identifying shapes. -/
theorem pairedNaturalCoefficient_alternants {r : ℕ}
    (a b c : Fin r → ℕ) (ha : StrictAnti a) (hb : StrictAnti b) (hc : StrictAnti c) :
    pairedNaturalCoefficient a b (xAlphabet r (alternant c) * yAlphabet r (alternant c)) =
      if a = c ∧ b = c then 1 else 0 := by
  rw [pairedNaturalCoefficient_mul,
    naturalCoefficient_alternant a c ha hc, naturalCoefficient_alternant b c hb hc]
  split_ifs <;> simp_all

theorem shiftedPartition_eq_of_diagram_eq {n m r : ℕ}
    (lam : Partition n) (μ : Partition m) (h : diagram lam = diagram μ) :
    shiftedPartition r lam = shiftedPartition r μ := by
  funext i
  change (diagram lam).rowLen i.val + _ = (diagram μ).rowLen i.val + _
  rw [h]

theorem partition_eq_of_diagram_eq {n : ℕ} (lam μ : Partition n)
    (h : diagram lam = diagram μ) : lam = μ := by
  apply (diagramEquiv n).injective
  exact Subtype.ext h

/-- The coefficient consequence on the partition side of FR-C02, with no
assumption of the still-to-be-proved kernel identity. -/
theorem alternatingPartitionCoefficient_coefficient {r n m : ℕ}
    (lam : Partition n) (μ : Partition m) (hlam : length lam ≤ r) (hμ : length μ ≤ r) :
    pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r μ)
      (alternatingPartitionCoefficient r n) =
        if diagram lam = diagram μ then 1 else 0 := by
  classical
  have hsum : pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r μ)
      (alternatingPartitionCoefficient r n) =
      ∑ ν : Partition n, pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r μ)
        (if length ν ≤ r then pairedPartitionAlternant r ν else 0) := by
    exact MvPolynomial.coeff_sum _ _ _
  rw [hsum, Finset.sum_eq_single lam]
  · rw [ite_eq_left hlam]
    change pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r μ)
      (xAlphabet r (alternant (shiftedPartition r lam)) *
       yAlphabet r (alternant (shiftedPartition r lam))) = _
    rw [pairedNaturalCoefficient_alternants _ _ _
      (shiftedPartition_strictAnti lam) (shiftedPartition_strictAnti μ)
      (shiftedPartition_strictAnti lam)]
    have he : shiftedPartition r μ = shiftedPartition r lam ↔ diagram lam = diagram μ := by
      constructor
      · exact fun h => (diagram_eq_of_shiftedPartition_eq μ lam hμ hlam h).symm
      · exact fun h => shiftedPartition_eq_of_diagram_eq μ lam h.symm
    simp [he]
  · intro ν _ hν
    by_cases hlen : length ν ≤ r
    · rw [ite_eq_left hlen]
      change pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r μ)
        (xAlphabet r (alternant (shiftedPartition r ν)) *
         yAlphabet r (alternant (shiftedPartition r ν))) = 0
      rw [pairedNaturalCoefficient_alternants _ _ _
        (shiftedPartition_strictAnti lam) (shiftedPartition_strictAnti μ)
        (shiftedPartition_strictAnti ν)]
      have he : shiftedPartition r lam ≠ shiftedPartition r ν := by
        intro h
        exact hν (partition_eq_of_diagram_eq ν lam
          (diagram_eq_of_shiftedPartition_eq lam ν hlam hlen h).symm)
      simp [he]
    · simp [hlen, pairedNaturalCoefficient,
        Specs.AdvancedFiniteGroupRepresentations.pairedNaturalCoefficient]
  · simp

/-- Assembly of the extraction assertion once the formal identity is supplied.
This theorem is a proved implication, not an assumption of the kernel identity. -/
theorem alternating_cauchy_coefficient_of_identity
    (h : Specs.AdvancedFiniteGroupRepresentations.alternating_cauchy_identityType) :
    Specs.AdvancedFiniteGroupRepresentations.alternating_cauchy_coefficientType := by
  intro r hr n m lam μ hlam hμ
  rw [h r hr]
  change pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r μ)
    (PowerSeries.coeff n (PowerSeries.mk (alternatingPartitionCoefficient r))) = _
  rw [PowerSeries.coeff_mk]
  exact alternatingPartitionCoefficient_coefficient lam μ hlam hμ

/-- The row cutoff makes summing the padded row lengths recover the size. -/
theorem sum_rowLength_fin {n r : ℕ} (ν : Partition n) (hν : length ν ≤ r) :
    (∑ i : Fin r, rowLength ν i.val) = n := by
  have he (k : ℕ) : (∑ i ∈ Finset.range k, rowLength ν i) =
      ((List.range k).map (rowLength ν)).sum := by
    induction k with
    | zero => simp
    | succ k ih => simp [Finset.sum_range_succ, List.range_succ, ih]
  rw [Fin.sum_univ_eq_sum_range]
  have hsub := Finset.sum_subset (Finset.range_mono hν)
    (f := rowLength ν) (by
      intro i _ hi
      apply rowLength_zero_of_length_le ν i
      simpa using hi)
  rw [← hsub, he, length_eq_columnLength_zero]
  exact parts_sum ν

theorem sum_shiftedPartition {n r : ℕ} (ν : Partition n) (hν : length ν ≤ r) :
    (∑ i : Fin r, shiftedPartition r ν i) = n + staircaseDegree r := by
  change (∑ i : Fin r, (rowLength ν i.val + staircase r i)) = _
  rw [Finset.sum_add_distrib, sum_rowLength_fin ν hν]
  rfl

/-- A determinant with power columns has the sum of the column degrees. -/
theorem powerDeterminant_weightedHomogeneous {R ι M : Type*}
    [CommRing R] [AddCommMonoid M] {r : ℕ}
    (w : ι → M) (d : M) (g : Fin r → MvPolynomial ι R)
    (hg : ∀ i, (g i).IsWeightedHomogeneous w d) (b : Fin r → ℕ) :
    (Matrix.of (fun i j : Fin r => g i ^ b j)).det.IsWeightedHomogeneous w
      ((∑ j : Fin r, b j) • d) := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro σ _
  have hp := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i : Fin r => g (σ i) ^ b i) (fun i => b i • d)
    (fun i _ => (hg (σ i)).pow (b i))
  rw [← Finset.sum_smul] at hp
  change (Equiv.Perm.sign σ • ∏ i : Fin r, g (σ i) ^ b i).IsWeightedHomogeneous _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa only [h, one_smul] using hp
  · simpa [h, Units.smul_def] using hp.neg

theorem pairedAlternant_bihomogeneous {r : ℕ} (b : Fin r → ℕ) :
    (xAlphabet r (alternant b) * yAlphabet r (alternant b)).IsWeightedHomogeneous
      (cauchyBidegreeWeight r) (∑ j : Fin r, b j, ∑ j : Fin r, b j) := by
  have hx : (xAlphabet r (alternant b)).IsWeightedHomogeneous
      (cauchyBidegreeWeight r) ((∑ j : Fin r, b j), 0) := by
    have he : xAlphabet r (alternant b) =
        (Matrix.of fun i j : Fin r => (MvPolynomial.X (Sum.inl i) : CauchyAlphabet r) ^ b j).det := by
      change (xAlphabet r).toRingHom
        (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ b j).det = _
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [xAlphabet, Specs.AdvancedFiniteGroupRepresentations.xAlphabet,
        RingHom.mapMatrix_apply]
    rw [he]
    simpa using powerDeterminant_weightedHomogeneous
      (cauchyBidegreeWeight r) (1, 0)
      (fun i : Fin r => (MvPolynomial.X (Sum.inl i) : CauchyAlphabet r))
      (fun i => MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (cauchyBidegreeWeight r) (Sum.inl i)) b
  have hy : (yAlphabet r (alternant b)).IsWeightedHomogeneous
      (cauchyBidegreeWeight r) (0, (∑ j : Fin r, b j)) := by
    have he : yAlphabet r (alternant b) =
        (Matrix.of fun i j : Fin r => (MvPolynomial.X (Sum.inr i) : CauchyAlphabet r) ^ b j).det := by
      change (yAlphabet r).toRingHom
        (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ b j).det = _
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [yAlphabet, Specs.AdvancedFiniteGroupRepresentations.yAlphabet,
        RingHom.mapMatrix_apply]
    rw [he]
    simpa using powerDeterminant_weightedHomogeneous
      (cauchyBidegreeWeight r) (0, 1)
      (fun i : Fin r => (MvPolynomial.X (Sum.inr i) : CauchyAlphabet r))
      (fun i => MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (cauchyBidegreeWeight r) (Sum.inr i)) b
  simpa using hx.mul hy

theorem alternatingPartitionCoefficient_bihomogeneous (r n : ℕ) :
    (alternatingPartitionCoefficient r n).IsWeightedHomogeneous
      (cauchyBidegreeWeight r) (n + staircaseDegree r, n + staircaseDegree r) := by
  classical
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ν _
  split_ifs with hν
  · change (xAlphabet r (alternant (shiftedPartition r ν)) *
        yAlphabet r (alternant (shiftedPartition r ν))).IsWeightedHomogeneous _ _
    simpa only [sum_shiftedPartition ν hν] using
      pairedAlternant_bihomogeneous (shiftedPartition r ν)
  · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _

/-- The geometric kernel has the same interpretation of the degree index. -/
theorem alternatingCauchyKernel_bihomogeneous (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    (PowerSeries.coeff n (alternatingCauchyKernel r)).IsWeightedHomogeneous
      (cauchyBidegreeWeight r) (n + staircaseDegree r, n + staircaseDegree r) := by
  change (PowerSeries.coeff n (PowerSeries.C (pairedVandermonde r) *
    cauchyKernel r)).IsWeightedHomogeneous _ _
  rw [PowerSeries.coeff_C_mul, cauchy_identity r hr]
  simp only [cauchyPartitionSeries,
    Specs.AdvancedFiniteGroupRepresentations.cauchyPartitionSeries, PowerSeries.coeff_mk]
  have hv := pairedAlternant_bihomogeneous (staircase r)
  have hk := cauchyPartitionCoefficient_bihomogeneous r n
  simpa only [pairedVandermonde, Specs.AdvancedFiniteGroupRepresentations.pairedVandermonde,
    Specs.AdvancedFiniteGroupRepresentations.vandermonde, staircaseDegree,
    Specs.AdvancedFiniteGroupRepresentations.staircaseDegree, Prod.mk_add_mk, Nat.add_comm] using hv.mul hk

theorem pairedExponent_weight {r : ℕ} (a b : Fin r → ℕ) :
    Finsupp.weight (cauchyBidegreeWeight r)
      (Finsupp.equivFunOnFinite.symm (Sum.elim a b)) =
        (∑ i : Fin r, a i, ∑ i : Fin r, b i) := by
  apply Prod.ext <;>
    simp [Finsupp.weight_eq_sum, Fintype.sum_sum_type,
      cauchyBidegreeWeight, Specs.AdvancedFiniteGroupRepresentations.cauchyBidegreeWeight,
      Prod.fst_sum, Prod.snd_sum, Prod.mul_def]

/-- Every other series degree has zero coefficient at the requested monomial.
Together with extraction at the degree of `lam`, this identifies its coefficient
in the original degreewise formal expression without the bookkeeping variable. -/
theorem alternatingCauchyKernel_coefficient_wrong_degree {r n m k : ℕ}
    (hr : 1 ≤ r) (lam : Partition n) (μ : Partition m)
    (hlam : length lam ≤ r) (hk : k ≠ n) :
    pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r μ)
      (PowerSeries.coeff k (alternatingCauchyKernel r)) = 0 := by
  apply (alternatingCauchyKernel_bihomogeneous r hr k).coeff_eq_zero
  rw [pairedExponent_weight, sum_shiftedPartition lam hlam]
  intro h
  have hh := congrArg Prod.fst h
  exact hk (Nat.add_right_cancel hh).symm

/-- Eliminate the first column using a nonzero pivot. -/
theorem det_succ_schur {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (h : A 0 0 ≠ 0) :
    A.det = A 0 0 * (Matrix.of fun i j : Fin n =>
      A i.succ j.succ - A i.succ 0 * (A 0 0)⁻¹ * A 0 j.succ).det := by
  classical
  let c : Fin (n + 1) → K := Fin.cons 0 (fun i => A i.succ 0 * (A 0 0)⁻¹)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    fun i j => A i j - c i * A 0 j
  have hdet : A.det = B.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c])
    intro i j
    simp only [B, c, Fin.cons_zero]
    ring
  rw [hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz (i : Fin n) : B i.succ 0 = 0 := by
    simp only [B, c, Fin.cons_succ]
    field_simp
    ring
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  congr 1
  simp [B, c]

/-- The rational Cauchy double alternant, with the two descending-column
signs paired. The only nonvanishing assumptions concern denominators. -/
theorem cauchy_det_field {K : Type*} [Field K] (n : ℕ)
    (x y : Fin n → K) (h : ∀ i j, 1 - x i * y j ≠ 0) :
    (Matrix.of fun i j : Fin n => (1 - x i * y j)⁻¹).det =
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x i - x j) * (y i - y j)) *
        ∏ i : Fin n, ∏ j : Fin n, (1 - x i * y j)⁻¹ := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    let f (i j : Fin (n + 1)) := (1 - x i * y j)⁻¹
    have he (i j : Fin n) :
        f i.succ j.succ - f i.succ 0 * (f 0 0)⁻¹ * f 0 j.succ =
        ((x i.succ - x 0) * f i.succ 0) *
          (((y j.succ - y 0) * f 0 j.succ) * f i.succ j.succ) := by
      dsimp [f]
      rw [inv_inv]
      have h3 : 1 - y j.succ * x 0 ≠ 0 := by simpa [mul_comm] using h 0 j.succ
      field_simp [h, h3]
      ring
    rw [det_succ_schur _ (inv_ne_zero (h 0 0))]
    change f 0 0 * (Matrix.of fun i j : Fin n =>
      f i.succ j.succ - f i.succ 0 * (f 0 0)⁻¹ * f 0 j.succ).det = _
    simp_rw [he]
    have hrow := Matrix.det_mul_column (fun i : Fin n => (x i.succ - x 0) * f i.succ 0)
      (Matrix.of fun i j : Fin n => ((y j.succ - y 0) * f 0 j.succ) * f i.succ j.succ)
    have hcol := Matrix.det_mul_row (fun j : Fin n => (y j.succ - y 0) * f 0 j.succ)
      (Matrix.of fun i j : Fin n => f i.succ j.succ)
    simp only [Matrix.of_apply] at hrow hcol
    rw [hrow, hcol,
      ih (fun i => x i.succ) (fun j => y j.succ) (fun i j => h i.succ j.succ)]
    simp only [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ]
    simp only [Finset.prod_mul_distrib]
    have hsign : (∏ i : Fin n, (x i.succ - x 0)) *
        (∏ i : Fin n, (y i.succ - y 0)) =
        (∏ i : Fin n, (x 0 - x i.succ)) * (∏ i : Fin n, (y 0 - y i.succ)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    dsimp [f] at *
    calc
      _ = ((∏ i : Fin n, (x i.succ - x 0)) * (∏ i : Fin n, (y i.succ - y 0))) *
          ((1 - x 0 * y 0)⁻¹ * (∏ i : Fin n, (1 - x i.succ * y 0)⁻¹) *
            (∏ j : Fin n, (1 - x 0 * y j.succ)⁻¹) *
            (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x i.succ - x j.succ)) *
            (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y i.succ - y j.succ)) *
            (∏ i : Fin n, ∏ j : Fin n, (1 - x i.succ * y j.succ)⁻¹)) := by ring
      _ = _ := by rw [hsign]; ring

/-- A Cauchy matrix over an integral domain, given its actual inverses.
The fraction field is used only inside the proof. -/
theorem cauchy_det_of_inverse {R : Type*} [CommRing R] [IsDomain R]
    (n : ℕ) (x y : Fin n → R) (z : Matrix (Fin n) (Fin n) R)
    (hz : ∀ i j, z i j * (1 - x i * y j) = 1) :
    z.det = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x i - x j) * (y i - y j)) *
      ∏ i : Fin n, ∏ j : Fin n, z i j := by
  let φ := algebraMap R (FractionRing R)
  have he (i j : Fin n) : φ (z i j) * (1 - φ (x i) * φ (y j)) = 1 := by
    simpa only [map_mul, map_sub, map_one] using congrArg φ (hz i j)
  have hn (i j : Fin n) : 1 - φ (x i) * φ (y j) ≠ 0 := by
    intro h
    have hh := he i j
    rw [h, mul_zero] at hh
    exact zero_ne_one hh
  have hi (i j : Fin n) : φ (z i j) = (1 - φ (x i) * φ (y j))⁻¹ :=
    eq_inv_of_mul_eq_one_left (he i j)
  apply IsFractionRing.injective R (FractionRing R)
  change φ z.det = φ _
  rw [RingHom.map_det]
  have hm : φ.mapMatrix z = Matrix.of (fun i j : Fin n => (1 - φ (x i) * φ (y j))⁻¹) := by
    ext i j
    exact hi i j
  rw [hm]
  simpa only [map_mul, map_prod, map_sub, hi] using
    cauchy_det_field n (fun i => φ (x i)) (fun j => φ (y j)) hn

/-- The paired Vandermonde as a product, preserving the source signs. -/
theorem pairedVandermonde_product (r : ℕ) :
    pairedVandermonde r = ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
      ((MvPolynomial.X (Sum.inl i) : CauchyAlphabet r) - MvPolynomial.X (Sum.inl j)) *
      (MvPolynomial.X (Sum.inr i) - MvPolynomial.X (Sum.inr j)) := by
  simp only [pairedVandermonde, Specs.AdvancedFiniteGroupRepresentations.pairedVandermonde,
    vandermonde_product, map_prod, map_sub,
    xAlphabet, Specs.AdvancedFiniteGroupRepresentations.xAlphabet,
    yAlphabet, Specs.AdvancedFiniteGroupRepresentations.yAlphabet,
    MvPolynomial.rename_X, Finset.prod_mul_distrib]

/-- Evaluation of the formal geometric Cauchy determinant. -/
theorem cauchyFactor_det (r : ℕ) :
    (Matrix.of (fun i j : Fin r => cauchyFactor i j)).det =
      PowerSeries.X ^ staircaseDegree r * alternatingCauchyKernel r := by
  classical
  let x (i : Fin r) : CauchyAlphabet r := MvPolynomial.X (Sum.inl i)
  let y (i : Fin r) : CauchyAlphabet r := MvPolynomial.X (Sum.inr i)
  have hd := cauchy_det_of_inverse r
    (fun i => PowerSeries.C (x i))
    (fun j => PowerSeries.C (y j) * PowerSeries.X)
    (Matrix.of (fun i j : Fin r => cauchyFactor i j)) (by
      intro i j
      simpa only [Matrix.of_apply, x, y, ← mul_assoc, ← map_mul] using cauchyFactor_mul_denominator i j)
  have hp (i j : Fin r) :
      (PowerSeries.C (x i) - PowerSeries.C (x j)) *
        (PowerSeries.C (y i) * PowerSeries.X - PowerSeries.C (y j) * PowerSeries.X) =
        PowerSeries.C ((x i - x j) * (y i - y j)) * PowerSeries.X := by
    simp only [map_mul, map_sub]
    ring
  rw [hd]
  simp_rw [hp]
  have hc : ∑ i : Fin r, (Finset.Ioi i).card = staircaseDegree r := by
    apply Finset.sum_congr rfl
    intro i _
    simp [staircase, Specs.AdvancedFiniteGroupRepresentations.staircase,
      Nat.sub_sub, Nat.add_comm]
  have hprod : (∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
      PowerSeries.C ((x i - x j) * (y i - y j)) * PowerSeries.X) =
        PowerSeries.C (pairedVandermonde r) * PowerSeries.X ^ staircaseDegree r := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
      hc, ← map_prod, pairedVandermonde_product]
    rfl
  rw [hprod]
  change (PowerSeries.C (pairedVandermonde r) * PowerSeries.X ^ staircaseDegree r) *
    cauchyKernel r = PowerSeries.X ^ staircaseDegree r *
      (PowerSeries.C (pairedVandermonde r) * cauchyKernel r)
  ring

/-- The monomial attached to a finite exponent vector. -/
theorem prod_X_pow_eq_monomial {r : ℕ} (a : Fin r → ℕ) :
    (∏ i : Fin r, (MvPolynomial.X i : Alphabet r) ^ a i) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) (1 : ℂ) := by
  rw [MvPolynomial.prod_X_pow]
  have he : Finsupp.indicator (Finset.univ : Finset (Fin r)) (fun i _ => a i) =
      Finsupp.equivFunOnFinite.symm a := by ext; simp
  rw [he]

/-- A permutation term of the geometric determinant in a fixed series degree. -/
theorem coeff_prod_cauchyFactor {r : ℕ} (σ : Equiv.Perm (Fin r)) (N : ℕ) :
    PowerSeries.coeff N (∏ i : Fin r, cauchyFactor (σ i) i) =
      ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin r)) N,
        xAlphabet r (MvPolynomial.monomial
          (Finsupp.equivFunOnFinite.symm (fun i => l (σ.symm i))) 1) *
        yAlphabet r (MvPolynomial.monomial l 1) := by
  classical
  rw [PowerSeries.coeff_prod]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Specs.AdvancedFiniteGroupRepresentations.cauchyFactor, PowerSeries.coeff_mk,
    mul_pow, Finset.prod_mul_distrib]
  have hx : (∏ i : Fin r,
      (MvPolynomial.X (Sum.inl (σ i)) : CauchyAlphabet r) ^ l i) =
      xAlphabet r (MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun i => l (σ.symm i))) 1) := by
    rw [← prod_X_pow_eq_monomial]
    simp only [map_prod, map_pow, Specs.AdvancedFiniteGroupRepresentations.xAlphabet,
      MvPolynomial.rename_X]
    apply Fintype.prod_equiv σ
    intro i
    simp
  have hy : (∏ i : Fin r,
      (MvPolynomial.X (Sum.inr i) : CauchyAlphabet r) ^ l i) =
      yAlphabet r (MvPolynomial.monomial l 1) := by
    have he : Finsupp.equivFunOnFinite.symm (fun i => l i) = l := by ext; rfl
    rw [← he, ← prod_X_pow_eq_monomial]
    simp only [map_prod, map_pow, Specs.AdvancedFiniteGroupRepresentations.yAlphabet,
      MvPolynomial.rename_X]
    rfl
  rw [hx, hy]

/-- Expand the determinant in the y-monomial basis. Fixing a y-exponent
leaves exactly the corresponding x-alternant. -/
theorem coeff_cauchyFactor_det (r N : ℕ) :
    PowerSeries.coeff N (Matrix.of (fun i j : Fin r => cauchyFactor i j)).det =
      ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin r)) N,
        xAlphabet r (alternant (fun i => l i)) *
        yAlphabet r (MvPolynomial.monomial l 1) := by
  classical
  rw [Matrix.det_apply]
  have hs (u : ℤˣ) (f : PowerSeries (CauchyAlphabet r)) :
      PowerSeries.coeff N (u • f) = u • PowerSeries.coeff N f := by
    rcases Int.units_eq_one_or u with h | h <;> simp [h, Units.smul_def]
  simp only [map_sum, hs, Matrix.of_apply, coeff_prod_cauchyFactor, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [alternant_eq_sum_monomial, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  have hx (u : ℤˣ) (p : Alphabet r) : xAlphabet r (u • p) = u • xAlphabet r p := by
    rcases Int.units_eq_one_or u with h | h <;> simp [h, Units.smul_def]
  rw [hx, smul_mul_assoc]

/-- Coefficient extraction in the y-alphabet of the determinant expansion. -/
theorem pairedNaturalCoefficient_cauchyFactor_det_general {r : ℕ}
    (a b : Fin r → ℕ) (N : ℕ) :
    pairedNaturalCoefficient a b
      (PowerSeries.coeff N (Matrix.of (fun i j : Fin r => cauchyFactor i j)).det) =
      if (∑ i : Fin r, b i) = N then naturalCoefficient a (alternant b) else 0 := by
  classical
  rw [coeff_cauchyFactor_det]
  change (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin r)) N,
    xAlphabet r (alternant (fun i => l i)) *
      yAlphabet r (MvPolynomial.monomial l 1)).coeff
        (Finsupp.equivFunOnFinite.symm (Sum.elim a b)) = _
  rw [MvPolynomial.coeff_sum]
  change (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin r)) N,
    pairedNaturalCoefficient a b (xAlphabet r (alternant (fun i => l i)) *
      yAlphabet r (MvPolynomial.monomial l 1))) = _
  simp only [pairedNaturalCoefficient_mul, naturalCoefficient,
    Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient, MvPolynomial.coeff_monomial,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_finsuppAntidiag,
    Finset.subset_univ, and_true]
  rfl

/-- Removing the staircase from strictly decreasing natural exponents gives
weakly decreasing, nonnegative row lengths. -/
theorem strictAnti_sub_staircase {r : ℕ} (b : Fin r → ℕ) (hb : StrictAnti b) :
    (∀ i, staircase r i ≤ b i) ∧ Antitone (fun i => b i - staircase r i) := by
  cases r with
  | zero => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ r =>
    have ht : Antitone (fun i : Fin (r + 1) => b i + i.val) := by
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      have hh := hb (show i.castSucc < i.succ by exact Fin.castSucc_lt_succ)
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hbound (i : Fin (r + 1)) : staircase (r + 1) i ≤ b i := by
      have hh := ht (Fin.le_last i)
      change b (Fin.last r) + r ≤ b i + i.val at hh
      change r + 1 - 1 - i.val ≤ b i
      omega
    refine ⟨hbound, ?_⟩
    intro i j hij
    have hh := ht hij
    dsimp only at hh
    have hi := hbound i
    have hj := hbound j
    change b j - (r + 1 - 1 - j.val) ≤ b i - (r + 1 - 1 - i.val)
    change r + 1 - 1 - i.val ≤ b i at hi
    change r + 1 - 1 - j.val ≤ b j at hj
    have hi' := i.isLt
    have hj' := j.isLt
    omega

/-- The exact partition correspondence used in the source's exponent sum. -/
theorem strictAnti_eq_shiftedPartition {r n : ℕ} (b : Fin r → ℕ)
    (hb : StrictAnti b) (hs : (∑ i : Fin r, b i) = n + staircaseDegree r) :
    ∃ ν : Partition n, length ν ≤ r ∧ shiftedPartition r ν = b := by
  classical
  obtain ⟨hbound, hrows⟩ := strictAnti_sub_staircase b hb
  let w := List.ofFn (fun i => b i - staircase r i)
  have hw : w.SortedGE := List.sortedGE_ofFn_iff.mpr hrows
  let D := YoungDiagram.ofRowLens w hw
  have hlen : D.rowLens.length ≤ r := by
    rw [YoungDiagram.length_rowLens]
    by_contra h
    have hmem : (r, 0) ∈ D := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    rw [YoungDiagram.mem_ofRowLens] at hmem
    have := hmem.1
    simp [w] at this
  have hrow (i : Fin r) : D.rowLen i.val = b i - staircase r i := by
    have hi : i.val < w.length := by simpa [w] using i.isLt
    simpa [D, w] using YoungDiagram.rowLen_ofRowLens (hw := hw) (⟨i.val, hi⟩ : Fin w.length)
  let ν : Partition D.card := D.toPartition rfl
  have hd : diagram ν = D := YoungDiagram.ofPartition_toPartition rfl
  have hlν : length ν ≤ r := by change (diagram ν).rowLens.length ≤ r; rw [hd]; exact hlen
  have hsν : (∑ i : Fin r, D.rowLen i.val) = D.card := by
    simpa only [rowLength, Specs.AdvancedFiniteGroupRepresentations.rowLength, hd] using
      sum_rowLength_fin ν hlν
  have hcard : D.card = n := by
    have he : (∑ i : Fin r, b i) = D.card + staircaseDegree r := by
      change (∑ i : Fin r, b i) = D.card + ∑ i : Fin r, staircase r i
      rw [← hsν, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hrow, Nat.sub_add_cancel (hbound i)]
    omega
  refine ⟨D.toPartition hcard, ?_, ?_⟩
  · change (YoungDiagram.ofPartition (D.toPartition hcard)).rowLens.length ≤ r
    rw [YoungDiagram.ofPartition_toPartition]
    exact hlen
  · funext i
    change (YoungDiagram.ofPartition (D.toPartition hcard)).rowLen i.val + staircase r i = b i
    rw [YoungDiagram.ofPartition_toPartition, hrow, Nat.sub_add_cancel (hbound i)]

/-- Sort an injective exponent vector by a permutation into decreasing order. -/
theorem exists_perm_strictAnti {r : ℕ} (b : Fin r → ℕ) (hb : Function.Injective b) :
    ∃ σ : Equiv.Perm (Fin r), StrictAnti (fun i => b (σ i)) := by
  classical
  let b' : Fin r → OrderDual ℕ := b
  let s : Finset (OrderDual ℕ) := Finset.univ.image b'
  have hc : s.card = r := by
    dsimp only [s]
    rw [Finset.card_image_of_injective _ (show Function.Injective b' from hb),
      Finset.card_univ, Fintype.card_fin]
  let e : Fin r ≃ s := Equiv.ofBijective (fun i => ⟨b i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩)
    ⟨by intro i j h; exact hb (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl⟩⟩
  let σ : Equiv.Perm (Fin r) := (s.orderIsoOfFin hc).toEquiv.trans e.symm
  refine ⟨σ, ?_⟩
  have he (i : Fin r) : b (σ i) = s.orderEmbOfFin hc i := by
    exact congrArg Subtype.val (e.apply_symm_apply ((s.orderIsoOfFin hc) i))
  intro i j hij
  change b (σ j) < b (σ i)
  rw [he, he]
  exact (s.orderEmbOfFin hc).strictMono hij

/-- Permuting exponent columns changes the alternant by the permutation sign. -/
theorem alternant_comp_perm {r : ℕ} (b : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) :
    alternant (fun i => b (σ i)) = Equiv.Perm.sign σ • alternant b := by
  change (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ b (σ j)).det = _
  have hm : (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ b (σ j)) =
      (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ b j).submatrix id σ := rfl
  rw [hm, Matrix.det_permute']
  simp only [Units.smul_def, zsmul_eq_mul]
  rfl

/-- An alternant with a repeated exponent vanishes. -/
theorem alternant_eq_zero_of_not_injective {r : ℕ} (b : Fin r → ℕ)
    (hb : ¬ Function.Injective b) : alternant b = 0 := by
  obtain ⟨i, j, he, hne⟩ := Function.not_injective_iff.mp hb
  apply Matrix.det_zero_of_column_eq hne
  intro k
  change (MvPolynomial.X k : Alphabet r) ^ b i = MvPolynomial.X k ^ b j
  rw [he]

/-- Renaming the variables of an alternant has the same permutation sign. -/
theorem rename_alternant {r : ℕ} (b : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) :
    MvPolynomial.rename σ (alternant b) = Equiv.Perm.sign σ • alternant b := by
  change (MvPolynomial.rename σ).toRingHom
    (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ b j).det = _
  rw [RingHom.map_det]
  have hm : (MvPolynomial.rename σ).toRingHom.mapMatrix
      (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ b j) =
      (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ b j).submatrix σ id := by
    ext i j
    simp [RingHom.mapMatrix_apply]
  rw [hm, Matrix.det_permute]
  simp only [Units.smul_def, zsmul_eq_mul]
  rfl

/-- Reordering a requested exponent vector in an alternant coefficient. -/
theorem naturalCoefficient_comp_perm {r : ℕ} (a b : Fin r → ℕ)
    (σ : Equiv.Perm (Fin r)) :
    naturalCoefficient (fun i => a (σ i)) (alternant b) =
      Equiv.Perm.sign σ • naturalCoefficient a (alternant b) := by
  have hd : (Finsupp.equivFunOnFinite.symm a).mapDomain σ.symm =
      Finsupp.equivFunOnFinite.symm (fun i => a (σ i)) := by
    ext i
    simp [Finsupp.mapDomain_equiv_apply]
  have hc := MvPolynomial.coeff_rename_mapDomain σ.symm σ.symm.injective
    (alternant b) (Finsupp.equivFunOnFinite.symm a)
  rw [hd, rename_alternant, Equiv.Perm.sign_symm] at hc
  change Equiv.Perm.sign σ • naturalCoefficient (fun i => a (σ i)) (alternant b) =
    naturalCoefficient a (alternant b) at hc
  rw [← hc, smul_smul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, Units.smul_def]

/-- The coefficient at a noninjective exponent vanishes in every alternant. -/
theorem naturalCoefficient_alternant_eq_zero_of_not_injective {r : ℕ}
    (a b : Fin r → ℕ) (ha : ¬ Function.Injective a) :
    naturalCoefficient a (alternant b) = 0 := by
  classical
  obtain ⟨i, j, he, hne⟩ := Function.not_injective_iff.mp ha
  have hs := naturalCoefficient_comp_perm a b (Equiv.swap i j)
  have hp : (fun k => a (Equiv.swap i j k)) = a := by
    funext k
    by_cases hki : k = i
    · subst k; simpa using he.symm
    by_cases hkj : k = j
    · subst k; simpa using he
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hp, Equiv.Perm.sign_swap hne] at hs
  have hz : naturalCoefficient a (alternant b) = -naturalCoefficient a (alternant b) := by
    simpa [Units.smul_def] using hs
  exact CharZero.eq_neg_self_iff.mp hz

/-- Expansion in the ordered alternant basis, first for decreasing exponents. -/
theorem alternant_basis_expansion_strictAnti {r n : ℕ} (b : Fin r → ℕ)
    (hb : StrictAnti b) :
    (if (∑ i : Fin r, b i) = n + staircaseDegree r then alternant b else 0) =
      ∑ ν : Partition n, if length ν ≤ r then
        naturalCoefficient b (partitionAlternant r ν) • partitionAlternant r ν else 0 := by
  classical
  by_cases hs : (∑ i : Fin r, b i) = n + staircaseDegree r
  · rw [ite_eq_left hs]
    obtain ⟨μ, hμ, he⟩ := strictAnti_eq_shiftedPartition b hb hs
    rw [Finset.sum_eq_single μ]
    · rw [ite_eq_left hμ]
      change alternant b = naturalCoefficient b (alternant (shiftedPartition r μ)) •
        alternant (shiftedPartition r μ)
      rw [he, naturalCoefficient_alternant b b hb hb, ite_eq_left rfl, one_smul]
    · intro ν _ hν
      by_cases hl : length ν ≤ r
      · rw [ite_eq_left hl]
        change naturalCoefficient b (alternant (shiftedPartition r ν)) • _ = 0
        rw [naturalCoefficient_alternant b _ hb (shiftedPartition_strictAnti ν)]
        have hn : b ≠ shiftedPartition r ν := by
          intro hh
          exact hν (partition_eq_of_diagram_eq ν μ
            (diagram_eq_of_shiftedPartition_eq μ ν hμ hl (he.trans hh)).symm)
        simp [hn]
      · simp [hl]
    · simp
  · rw [ite_eq_right hs]
    symm
    apply Finset.sum_eq_zero
    intro ν _
    by_cases hl : length ν ≤ r
    · rw [ite_eq_left hl]
      change naturalCoefficient b (alternant (shiftedPartition r ν)) • _ = 0
      rw [naturalCoefficient_alternant b _ hb (shiftedPartition_strictAnti ν)]
      have hn : b ≠ shiftedPartition r ν := by
        intro hh
        exact hs (by rw [hh, sum_shiftedPartition ν hl])
      simp [hn]
    · simp [hl]

/-- Every exponent vector has the alternating projection prescribed by the
partition basis; repeated exponents contribute zero. -/
theorem alternant_basis_expansion {r n : ℕ} (b : Fin r → ℕ) :
    (if (∑ i : Fin r, b i) = n + staircaseDegree r then alternant b else 0) =
      ∑ ν : Partition n, if length ν ≤ r then
        naturalCoefficient b (partitionAlternant r ν) • partitionAlternant r ν else 0 := by
  classical
  by_cases hb : Function.Injective b
  · obtain ⟨σ, hσ⟩ := exists_perm_strictAnti b hb
    let c : Fin r → ℕ := fun i => b (σ i)
    have hc : StrictAnti c := hσ
    have hsum : (∑ i : Fin r, c i) = ∑ i : Fin r, b i := Equiv.sum_comp σ b
    have hfun : (fun i => c (σ.symm i)) = b := by funext i; simp [c]
    have halt : alternant b = Equiv.Perm.sign σ • alternant c := by
      have hh := alternant_comp_perm c σ.symm
      simpa only [hfun, Equiv.Perm.sign_symm] using hh
    have hcoef (ν : Partition n) : naturalCoefficient b (partitionAlternant r ν) =
        Equiv.Perm.sign σ • naturalCoefficient c (partitionAlternant r ν) := by
      change naturalCoefficient b (alternant (shiftedPartition r ν)) = _
      have hh := naturalCoefficient_comp_perm c (shiftedPartition r ν) σ.symm
      simpa only [hfun, Equiv.Perm.sign_symm, partitionAlternant,
        Specs.AdvancedFiniteGroupRepresentations.partitionAlternant] using hh
    have he := alternant_basis_expansion_strictAnti (n := n) c hc
    rw [hsum] at he
    rw [halt]
    simp_rw [hcoef]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simpa only [h, one_smul] using he
    · have hneg : (if (∑ i : Fin r, b i) = n + staircaseDegree r then -alternant c else 0) =
          ∑ ν : Partition n, if length ν ≤ r then
            (-naturalCoefficient c (partitionAlternant r ν)) • partitionAlternant r ν else 0 := by
        calc
          _ = -(if (∑ i : Fin r, b i) = n + staircaseDegree r then alternant c else 0) := by
            split_ifs <;> simp
          _ = -(∑ ν : Partition n, if length ν ≤ r then
              naturalCoefficient c (partitionAlternant r ν) • partitionAlternant r ν else 0) :=
            congrArg Neg.neg he
          _ = _ := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro ν _
            split_ifs <;> simp
      simpa [h, Units.smul_def] using hneg
  · rw [alternant_eq_zero_of_not_injective b hb]
    simp only [ite_self]
    symm
    apply Finset.sum_eq_zero
    intro ν _
    by_cases hl : length ν ≤ r
    · rw [ite_eq_left hl]
      change naturalCoefficient b (alternant (shiftedPartition r ν)) • _ = 0
      rw [naturalCoefficient_alternant_eq_zero_of_not_injective b _ hb, zero_smul]
    · simp [hl]

/-- The ordered coefficient in the geometric determinant. -/
theorem pairedNaturalCoefficient_cauchyFactor_det {r : ℕ}
    (a b : Fin r → ℕ) (ha : StrictAnti a) (hb : StrictAnti b) :
    pairedNaturalCoefficient a b
      (PowerSeries.coeff (∑ i : Fin r, b i)
        (Matrix.of (fun i j : Fin r => cauchyFactor i j)).det) =
      if a = b then 1 else 0 := by
  classical
  rw [coeff_cauchyFactor_det]
  change (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin r)) (∑ i, b i),
    xAlphabet r (alternant (fun i => l i)) *
      yAlphabet r (MvPolynomial.monomial l 1)).coeff
        (Finsupp.equivFunOnFinite.symm (Sum.elim a b)) = _
  rw [MvPolynomial.coeff_sum]
  change (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin r)) (∑ i, b i),
    pairedNaturalCoefficient a b (xAlphabet r (alternant (fun i => l i)) *
      yAlphabet r (MvPolynomial.monomial l 1))) = _
  simp only [pairedNaturalCoefficient_mul]
  simp only [naturalCoefficient, Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm b)]
  · simp only [ite_true, mul_one]
    exact naturalCoefficient_alternant a b ha hb
  · intro l _ hne
    rw [if_neg hne, mul_zero]
  · intro hnot
    exact (hnot (by simp)).elim

/-- FR-C02 coefficient extraction, obtained directly from the determinant
rather than assuming the full partition expansion. -/
theorem alternating_cauchy_coefficient :
    Specs.AdvancedFiniteGroupRepresentations.alternating_cauchy_coefficientType := by
  intro r hr n m lam μ hlam hμ
  change pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r μ)
    (PowerSeries.coeff n (alternatingCauchyKernel r)) =
      if diagram lam = diagram μ then 1 else 0
  have hd := congrArg (PowerSeries.coeff (n + staircaseDegree r)) (cauchyFactor_det r)
  rw [PowerSeries.coeff_X_pow_mul] at hd
  rw [← hd]
  by_cases hnm : n = m
  · subst m
    rw [← sum_shiftedPartition μ hμ,
      pairedNaturalCoefficient_cauchyFactor_det (r := r) _ _
        (shiftedPartition_strictAnti lam) (shiftedPartition_strictAnti μ)]
    have he : shiftedPartition r lam = shiftedPartition r μ ↔ diagram lam = diagram μ :=
      ⟨diagram_eq_of_shiftedPartition_eq lam μ hlam hμ,
       shiftedPartition_eq_of_diagram_eq lam μ⟩
    simp only [he]
  · have hh : diagram lam ≠ diagram μ := by
      intro h
      have := congrArg YoungDiagram.card h
      rw [diagram_card, diagram_card] at this
      exact hnm this
    rw [if_neg hh]
    -- The x-degree fixes the series index; unequal y-degree then vanishes.
    have hdegree := alternatingCauchyKernel_bihomogeneous r hr n
    rw [hd]
    apply hdegree.coeff_eq_zero
    rw [pairedExponent_weight, sum_shiftedPartition lam hlam, sum_shiftedPartition μ hμ]
    intro h
    exact hnm (Nat.add_right_cancel (congrArg Prod.snd h)).symm

/-- The degreewise partition expansion of the geometric determinant. This
uses its y-monomial expansion and the proved alternant basis correspondence. -/
theorem cauchyFactor_det_partition_expansion (r n : ℕ) :
    PowerSeries.coeff (n + staircaseDegree r)
      (Matrix.of (fun i j : Fin r => cauchyFactor i j)).det =
        alternatingPartitionCoefficient r n := by
  classical
  apply MvPolynomial.ext
  intro l
  let a : Fin r → ℕ := fun i => l (Sum.inl i)
  let b : Fin r → ℕ := fun i => l (Sum.inr i)
  have hl : Finsupp.equivFunOnFinite.symm (Sum.elim a b) = l := by
    ext (i | i) <;> rfl
  rw [← hl]
  change pairedNaturalCoefficient a b
    (PowerSeries.coeff (n + staircaseDegree r)
      (Matrix.of (fun i j : Fin r => cauchyFactor i j)).det) =
        pairedNaturalCoefficient a b (alternatingPartitionCoefficient r n)
  rw [pairedNaturalCoefficient_cauchyFactor_det_general]
  have hright : pairedNaturalCoefficient a b (alternatingPartitionCoefficient r n) =
      ∑ ν : Partition n, if length ν ≤ r then
        naturalCoefficient a (partitionAlternant r ν) *
          naturalCoefficient b (partitionAlternant r ν) else 0 := by
    change (∑ ν : Partition n,
      if length ν ≤ r then pairedPartitionAlternant r ν else 0).coeff _ = _
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro ν _
    by_cases hν : length ν ≤ r
    · rw [ite_eq_left hν, ite_eq_left hν]
      exact pairedNaturalCoefficient_mul a b (partitionAlternant r ν) (partitionAlternant r ν)
    · simp [hν]
  rw [hright]
  have he := congrArg (fun p : Alphabet r => naturalCoefficient a p)
    (alternant_basis_expansion (n := n) b)
  have hleft : naturalCoefficient a
      (if (∑ i : Fin r, b i) = n + staircaseDegree r then alternant b else 0) =
      if (∑ i : Fin r, b i) = n + staircaseDegree r then naturalCoefficient a (alternant b) else 0 := by
    split_ifs <;> rfl
  rw [hleft] at he
  rw [he]
  change (∑ ν : Partition n, if length ν ≤ r then
    naturalCoefficient b (partitionAlternant r ν) • partitionAlternant r ν else 0).coeff _ = _
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases hν : length ν ≤ r
  · simp only [ite_eq_left hν, MvPolynomial.coeff_smul]
    change naturalCoefficient b (partitionAlternant r ν) *
      naturalCoefficient a (partitionAlternant r ν) = _
    exact mul_comm _ _
  · simp [hν]

/-- The two hard determinant statements suffice; only coefficients numbered
`n+|δ|` are needed, so no separate low-degree vanishing assertion is required. -/
theorem alternating_cauchy_identity_of_determinant
    (hdet : ∀ (r : ℕ), 1 ≤ r →
      (Matrix.of (fun i j : Fin r => cauchyFactor i j)).det =
        PowerSeries.X ^ staircaseDegree r * alternatingCauchyKernel r)
    (hexp : ∀ (r : ℕ), 1 ≤ r → ∀ n : ℕ,
      PowerSeries.coeff (n + staircaseDegree r)
        (Matrix.of (fun i j : Fin r => cauchyFactor i j)).det =
          alternatingPartitionCoefficient r n) :
    Specs.AdvancedFiniteGroupRepresentations.alternating_cauchy_identityType := by
  intro r hr
  apply PowerSeries.ext
  intro n
  have h := hexp r hr n
  rw [hdet r hr, PowerSeries.coeff_X_pow_mul] at h
  simpa only [Specs.AdvancedFiniteGroupRepresentations.alternatingPartitionSeries,
    PowerSeries.coeff_mk] using h

theorem alternating_cauchy_identity_iff_degree :
    Specs.AdvancedFiniteGroupRepresentations.alternating_cauchy_identityType ↔
      Specs.AdvancedFiniteGroupRepresentations.alternating_cauchy_identity_degreeType := by
  constructor
  · intro h r hr n
    have hc := congrArg (PowerSeries.coeff n) (h r hr)
    simpa [Specs.AdvancedFiniteGroupRepresentations.alternatingCauchyKernel,
      Specs.AdvancedFiniteGroupRepresentations.alternatingPartitionSeries] using hc
  · intro h r hr
    apply PowerSeries.ext
    intro n
    simpa [Specs.AdvancedFiniteGroupRepresentations.alternatingCauchyKernel,
      Specs.AdvancedFiniteGroupRepresentations.alternatingPartitionSeries] using h r hr n

/-- FR-C02, the alternating Cauchy kernel as a degreewise formal identity. -/
theorem alternating_cauchy_identity :
    Specs.AdvancedFiniteGroupRepresentations.alternating_cauchy_identityType :=
  alternating_cauchy_identity_of_determinant (fun r _ => cauchyFactor_det r)
    (fun r _ n => cauchyFactor_det_partition_expansion r n)

/-- The finite polynomial equality in each degree above the staircase. -/
theorem alternating_cauchy_identity_degree :
    Specs.AdvancedFiniteGroupRepresentations.alternating_cauchy_identity_degreeType :=
  alternating_cauchy_identity_iff_degree.mp alternating_cauchy_identity

end AdvancedFiniteGroupRepresentations
