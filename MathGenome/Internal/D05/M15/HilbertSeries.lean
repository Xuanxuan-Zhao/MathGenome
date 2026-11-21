import MathGenome.Internal.Specs.D05.M15.HilbertSeries
import MathGenome.Internal.D05.M15.ExteriorBasis
import MathGenome.Internal.D05.M15.SymmetricBasis
import MathGenome.Internal.D05.Foundations.StarsBars
import MathGenome.Internal.D05.Foundations.SubsetCount
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.TensorProduct.Finite

noncomputable section
namespace D05.M15.HilbertSeries
open Specs.D05.M15.HilbertSeries
open scoped TensorProduct DirectSum

/-- The binomial theorem is used in ℤ⟦X⟧, not in the scalar field. -/
theorem exterior_series : Specs.D05.M15.HilbertSeries.exterior_series := by
  intro K V _ _ _ _
  apply PowerSeries.ext
  intro p
  rw [dimensionSeries, PowerSeries.coeff_mk, D05.M15.ExteriorBasis.dimension]
  have h := Polynomial.coeff_one_add_X_pow ℤ (Module.finrank K V) p
  simpa only [← Polynomial.coeff_coe, Polynomial.coe_pow, Polynomial.coe_add,
    Polynomial.coe_one, Polynomial.coe_X] using h.symm

/-- Includes the exceptional zero-variable case explicitly. -/
theorem symmetric_dimension (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (p : ℕ) :
    Module.finrank K (Specs.D05.M15.Symmetric.symmetricPower K V p) =
      ((Module.finrank K V + p - 1).choose p) := by
  classical
  rw [Module.finrank_eq_nat_card_basis
    (D05.M15.SymmetricBasis.monomialBasis (Module.finBasis K V) p)]
  exact D05.Foundations.StarsBars.tuples_card _ _

theorem symmetric_series : Specs.D05.M15.HilbertSeries.symmetric_series := by
  intro K V _ _ _ _
  classical
  have hcard (p : ℕ) := symmetric_dimension K V p
  cases hn : Module.finrank K V with
  | zero =>
    apply PowerSeries.ext
    intro p
    rw [dimensionSeries, PowerSeries.coeff_mk, hcard, hn, pow_zero]
    cases p with
    | zero => simp
    | succ p => simp
  | succ n =>
    trans PowerSeries.mk (fun p => ((n+p).choose n : ℤ))
    · apply PowerSeries.ext
      intro p
      simp only [dimensionSeries, PowerSeries.coeff_mk, hcard, hn]
      congr 1
      rw [show n + 1 + p - 1 = n + p by omega]
      simpa using (Nat.choose_symm (Nat.le_add_right n p))
    · exact (PowerSeries.mk_one_pow_eq_mk_choose_add ℤ n).symm

theorem geometric_inverse : Specs.D05.M15.HilbertSeries.geometric_inverse :=
  PowerSeries.mk_one_mul_one_sub_eq_one ℤ

theorem symmetric_inverse : Specs.D05.M15.HilbertSeries.symmetric_inverse := by
  intro K V _ _ _ _
  rw [symmetric_series, ← mul_pow, geometric_inverse, one_pow]

theorem symmetric_product : Specs.D05.M15.HilbertSeries.symmetric_product := by
  intro K V _ _ _ _
  rw [symmetric_series]
  simp

theorem zero_dimension : Specs.D05.M15.HilbertSeries.zero_dimension := by
  intro K V _ _ _ _ h
  rw [exterior_series, symmetric_series, h, pow_zero, pow_zero]
  exact ⟨rfl, rfl⟩

theorem tensor_dimension : Specs.D05.M15.HilbertSeries.tensor_dimension := by
  intro K V _ _ _ _ p
  classical
  rw [Module.finrank_eq_card_basis
    (Basis.piTensorProduct (fun _ : Fin p => Module.finBasis K V))]
  simp

theorem tensor_series : Specs.D05.M15.HilbertSeries.tensor_series := by
  intro K V _ _ _ _
  ext p
  simp only [dimensionSeries, PowerSeries.coeff_mk]
  rw [tensor_dimension p, Nat.cast_pow]

/-- Coefficient cancellation proves the geometric identity for arbitrary
integer ratio; in particular it includes ratio zero. -/
theorem geometric_ratio (n : ℤ) :
    PowerSeries.mk (fun p => n ^ p) * (1 - PowerSeries.C n * PowerSeries.X) = 1 := by
  apply PowerSeries.ext
  intro p
  cases p with
  | zero => simp
  | succ p => simp [mul_sub, ← mul_assoc, PowerSeries.coeff_succ_mul_X, pow_succ]

theorem tensor_inverse : Specs.D05.M15.HilbertSeries.tensor_inverse := by
  intro K V _ _ _ _
  rw [tensor_series]
  exact geometric_ratio _

theorem tensor_product_series : Specs.D05.M15.HilbertSeries.tensor_product_series := by
  intro K _ U W _ _ _ _ _ _
  apply PowerSeries.ext
  intro k
  rw [dimensionSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [Module.finrank_directSum]
  simp only [Module.finrank_tensorProduct, Nat.cast_sum, Nat.cast_mul,
    dimensionSeries, PowerSeries.coeff_mk]
  exact Finset.sum_coe_sort (Finset.antidiagonal k)
    (fun ab => (Module.finrank K (U ab.1) : ℤ) * (Module.finrank K (W ab.2) : ℤ))

/-- Positivity gives an explicit finite bound on every exponent. -/
theorem weighted_exponent_bound {I : Type*} [Fintype I] (d a : I → ℕ)
    (hd : ∀ i, 0 < d i) {k : ℕ} (ha : ∑ i, d i * a i = k) (i : I) : a i ≤ k := by
  classical
  calc
    a i = 1 * a i := by simp
    _ ≤ d i * a i := Nat.mul_le_mul_right _ (hd i)
    _ ≤ ∑ j, d j * a j := Finset.single_le_sum (f := fun j => d j * a j)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = k := ha

/-- Restricting the exponents to Fin(k+1) loses no monomial of weight k. -/
def boundedWeightedTuples {I : Type*} [Fintype I] (d : I → ℕ)
    (hd : ∀ i, 0 < d i) (k : ℕ) :
    {a : I → ℕ // ∑ i, d i * a i = k} ≃
      {a : I → Fin (k+1) // ∑ i, d i * (a i).val = k} where
  toFun a := ⟨fun i => ⟨a.val i, Nat.lt_succ_of_le
    (weighted_exponent_bound d a.val hd a.property i)⟩, a.property⟩
  invFun a := ⟨fun i => (a.val i).val, a.property⟩
  left_inv a := rfl
  right_inv a := by apply Subtype.ext; funext i; apply Fin.ext; rfl

theorem weighted_tuples_finite {I : Type*} [Fintype I] (d : I → ℕ)
    (hd : ∀ i, 0 < d i) (k : ℕ) :
    Finite {a : I → ℕ // ∑ i, d i * a i = k} := by
  classical
  exact Finite.of_equiv _ (boundedWeightedTuples d hd k).symm

/-- Restrict the exterior basis to the given weight; the vectors lie in the
original exterior algebra, rather than in a separately defined counting space. -/
def weightedExteriorBasis {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (b : Module.Basis I K V) (d : I → ℕ) (k : ℕ) :
    Module.Basis {s : Finset I // ∑ i ∈ s, d i = k} K (weightedExteriorPart b d k) := by
  letI := basisIndexOrder I
  exact Module.Basis.span (b.ExteriorAlgebra.linearIndependent.comp
    (fun s : {s : Finset I // ∑ i ∈ s, d i = k} => s.val) Subtype.val_injective)

/-- The full symmetric basis is literally the ordinary generator monomials. -/
theorem symmetricAlgebra_monomial {K V I : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (b : Module.Basis I K V) (a : I → ℕ) :
    b.symmetricAlgebra (Finsupp.equivFunOnFinite.symm a) =
      ∏ i, (_root_.SymmetricAlgebra.ι K V (b i)) ^ a i := by
  classical
  apply (_root_.SymmetricAlgebra.equivMvPolynomial b).injective
  change (_root_.SymmetricAlgebra.equivMvPolynomial b)
    ((_root_.SymmetricAlgebra.equivMvPolynomial b).symm
      (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) 1)) = _
  rw [AlgEquiv.apply_symm_apply]
  simp only [map_prod, map_pow, _root_.SymmetricAlgebra.equivMvPolynomial_ι_apply]
  rw [MvPolynomial.monic_monomial_eq,
    Finsupp.prod_fintype _ _ (by simp)]
  rfl

theorem weighted_symmetric_part_monomials :
    Specs.D05.M15.HilbertSeries.weighted_symmetric_part_monomials := by
  intro K V I _ _ _ _ b d k
  unfold weightedSymmetricPart
  congr 2
  funext a
  exact symmetricAlgebra_monomial b a.val

/-- Restrict the ordinary monomial basis to the given weight. -/
def weightedSymmetricBasis {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (b : Module.Basis I K V) (d : I → ℕ) (k : ℕ) :
    Module.Basis {a : I → ℕ // ∑ i, d i * a i = k} K (weightedSymmetricPart b d k) :=
  Module.Basis.span (b.symmetricAlgebra.linearIndependent.comp
    (fun a : {a : I → ℕ // ∑ i, d i * a i = k} =>
      Finsupp.equivFunOnFinite.symm a.val)
    (Finsupp.equivFunOnFinite.symm.injective.comp Subtype.val_injective))

theorem positive_weight_finiteness : Specs.D05.M15.HilbertSeries.positive_weight_finiteness := by
  intro K V I _ _ _ _ b d hd k
  classical
  have := weighted_tuples_finite d hd k
  exact ⟨Module.Finite.of_basis (weightedExteriorBasis b d k),
    Module.Finite.of_basis (weightedSymmetricBasis b d k)⟩

/-- A single positively weighted polynomial generator contributes a geometric
series. This also identifies its coefficient definition with formal substitution. -/
theorem weightedGeometric_eq_expand (d : ℕ) (hd : 0 < d) :
    weightedGeometric d = PowerSeries.expand d (Nat.ne_of_gt hd)
      (PowerSeries.mk (fun _ => (1 : ℤ))) := by
  ext k
  simp [weightedGeometric, PowerSeries.coeff_expand]

theorem weighted_geometric_inverse : Specs.D05.M15.HilbertSeries.weighted_geometric_inverse := by
  intro d hd
  have h := congrArg (PowerSeries.expand d (Nat.ne_of_gt hd) (R := ℤ)) geometric_inverse
  simpa only [map_mul, map_sub, map_one, PowerSeries.expand_X,
    ← weightedGeometric_eq_expand d hd] using h

/-- Selecting each generator zero or one times enumerates all finite subsets. -/
theorem weighted_exterior_basis_series {K V I : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (b : Module.Basis I K V) (d : I → ℕ) :
    dimensionSeries K (fun k => ↥(weightedExteriorPart b d k)) =
      ∏ i, (1 + PowerSeries.X ^ d i) := by
  classical
  apply PowerSeries.ext
  intro k
  rw [dimensionSeries, PowerSeries.coeff_mk,
    Module.finrank_eq_nat_card_basis (weightedExteriorBasis b d k),
    Finset.prod_one_add, Finset.powerset_univ, map_sum]
  simp_rw [Finset.prod_pow_eq_pow_sum, PowerSeries.coeff_X_pow]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext s
  simp [eq_comm]

/-- A product coefficient depends only on coefficients up to that degree. -/
theorem coeff_prod_congr_upto {I : Type*} [DecidableEq I] (s : Finset I)
    (f g : I → PowerSeries ℤ) (k : ℕ)
    (h : ∀ i ∈ s, ∀ m ≤ k, PowerSeries.coeff m (f i) = PowerSeries.coeff m (g i)) :
    PowerSeries.coeff k (∏ i ∈ s, f i) = PowerSeries.coeff k (∏ i ∈ s, g i) := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, PowerSeries.coeff_mul,
      PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    have hab' := Finset.mem_antidiagonal.mp hab
    rw [h i (Finset.mem_insert_self _ _) ab.1 (by omega)]
    rw [ih ab.2 (fun j hj m hm => h j (Finset.mem_insert_of_mem hj) m (by omega))]

/-- In any fixed degree, the geometric series can be replaced by a finite sum. -/
theorem coeff_weighted_geometric_trunc (d : ℕ) (hd : 0 < d) (k p : ℕ) (hp : p ≤ k) :
    PowerSeries.coeff p (weightedGeometric d) =
      PowerSeries.coeff p (∑ a : Fin (k+1), (PowerSeries.X : PowerSeries ℤ) ^ (d * a.val)) := by
  classical
  rw [weightedGeometric, PowerSeries.coeff_mk, map_sum]
  simp only [PowerSeries.coeff_X_pow]
  by_cases h : d ∣ p
  · obtain ⟨a, rfl⟩ := h
    let q : Fin (k+1) := ⟨a, Nat.lt_succ_of_le
      ((Nat.le_mul_of_pos_left a hd).trans hp)⟩
    rw [ite_eq_left (dvd_mul_right d a)]
    have hs : (∑ x : Fin (k+1), if d*a = d*x.val then (1 : ℤ) else 0) = 1 := by
      calc
        _ = (if d*a = d*q.val then (1 : ℤ) else 0) := by
          apply Finset.sum_eq_single q
          · intro x _ hx
            apply ite_eq_right
            intro he
            apply hx
            exact Fin.ext (Nat.eq_of_mul_eq_mul_left hd he).symm
          · simp
        _ = 1 := by simp [q]
    exact hs.symm
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro a _
    apply ite_eq_right
    intro he
    exact h ⟨a.val, he⟩

/-- Expanding the finite product enumerates bounded exponent tuples; positivity
then removes the artificial bound, proving the full symmetric series. -/
theorem weighted_symmetric_basis_series {K V I : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (b : Module.Basis I K V) (d : I → ℕ)
    (hd : ∀ i, 0 < d i) :
    dimensionSeries K (fun k => ↥(weightedSymmetricPart b d k)) =
      ∏ i, weightedGeometric (d i) := by
  classical
  apply PowerSeries.ext
  intro k
  rw [dimensionSeries, PowerSeries.coeff_mk,
    Module.finrank_eq_nat_card_basis (weightedSymmetricBasis b d k)]
  rw [Nat.card_congr (boundedWeightedTuples d hd k), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  have htrunc := coeff_prod_congr_upto Finset.univ
    (fun i => weightedGeometric (d i))
    (fun i => ∑ a : Fin (k+1), (PowerSeries.X : PowerSeries ℤ) ^ (d i * a.val)) k
    (fun i _ p hp => coeff_weighted_geometric_trunc (d i) (hd i) k p hp)
  rw [htrunc, Fintype.prod_sum, map_sum]
  simp_rw [Finset.prod_pow_eq_pow_sum, PowerSeries.coeff_X_pow]
  rw [Finset.sum_boole]
  congr 2
  ext a
  simp [eq_comm]

/-- Grouping the finitely many generators by their component gives the powers
n_j in the paper's weighted product. -/
theorem weighted_exterior_series : Specs.D05.M15.HilbertSeries.weighted_exterior_series := by
  intro K _ r W _ _ _ d hd
  rw [weighted_exterior_basis_series, Fintype.prod_sigma]
  simp

theorem weighted_symmetric_series : Specs.D05.M15.HilbertSeries.weighted_symmetric_series := by
  intro K _ r W _ _ _ d hd
  rw [weighted_symmetric_basis_series
    (DFinsupp.basis (fun j => Module.finBasis K (W j))) (fun i => d i.1)
    (fun i => hd i.1), Fintype.prod_sigma]
  simp

theorem weighted_symmetric_inverse : Specs.D05.M15.HilbertSeries.weighted_symmetric_inverse := by
  intro K _ r W _ _ _ d hd
  rw [weighted_symmetric_series r W d hd, ← Finset.prod_mul_distrib]
  have h (j : Fin r) : weightedGeometric (d j) ^ Module.finrank K (W j) *
      (1 - PowerSeries.X ^ d j) ^ Module.finrank K (W j) = 1 := by
    rw [← mul_pow, weighted_geometric_inverse (d j) (hd j), one_pow]
  simp only [h, Finset.prod_const_one]

end D05.M15.HilbertSeries
