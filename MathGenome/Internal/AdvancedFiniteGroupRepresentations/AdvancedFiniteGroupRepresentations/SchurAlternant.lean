import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.AlternatingCauchyKernel
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SymmetricPolynomialData
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurAlternant
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev schurPolynomial := @Specs.AdvancedFiniteGroupRepresentations.schurPolynomial
abbrev jacobiTrudiMatrix := @Specs.AdvancedFiniteGroupRepresentations.jacobiTrudiMatrix
abbrev jacobiTrudi := @Specs.AdvancedFiniteGroupRepresentations.jacobiTrudi

/-- Identify one variable with another, leaving all remaining variables fixed. -/
def identifyVariables {r : ℕ} (i j : Fin r) : Alphabet r →ₐ[ℂ] Alphabet r :=
  MvPolynomial.rename (fun k => if k = i then j else k)

/-- The elementary polynomial remainder identity for identifying two variables. -/
theorem variableDifference_dvd_remainder {r : ℕ} (i j : Fin r) (p : Alphabet r) :
    (MvPolynomial.X i - MvPolynomial.X j : Alphabet r) ∣ p - identifyVariables i j p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [identifyVariables]
  | add p q hp hq =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hp hq
  | mul_X p k hp =>
    have hk : (MvPolynomial.X i - MvPolynomial.X j : Alphabet r) ∣
        MvPolynomial.X k - identifyVariables i j (MvPolynomial.X k) := by
      by_cases he : k = i
      · subst k
        simp [identifyVariables]
      · simp [identifyVariables, he]
    rw [map_mul]
    have he : p * MvPolynomial.X k - identifyVariables i j p *
        identifyVariables i j (MvPolynomial.X k) =
        (p - identifyVariables i j p) * MvPolynomial.X k +
        identifyVariables i j p * (MvPolynomial.X k - identifyVariables i j (MvPolynomial.X k)) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hk _)

theorem variableDifference_dvd_iff {r : ℕ} (i j : Fin r) (hij : i ≠ j)
    (p : Alphabet r) :
    (MvPolynomial.X i - MvPolynomial.X j : Alphabet r) ∣ p ↔ identifyVariables i j p = 0 := by
  classical
  constructor
  · intro hp
    have he := map_dvd (identifyVariables i j).toRingHom hp
    simpa [identifyVariables, hij.symm] using he
  · intro hp
    simpa [hp] using variableDifference_dvd_remainder i j p

theorem variableDifference_prime {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    Prime (MvPolynomial.X i - MvPolynomial.X j : Alphabet r) := by
  classical
  refine ⟨sub_ne_zero.mpr ?_, ?_, ?_⟩
  · exact fun h => hij (MvPolynomial.X_injective h)
  · intro hu
    have hd : (MvPolynomial.X i - MvPolynomial.X j : Alphabet r) ∣ 1 := hu.dvd
    have he := (variableDifference_dvd_iff i j hij 1).mp hd
    simp at he
  · intro p q hpq
    rw [variableDifference_dvd_iff i j hij, map_mul, mul_eq_zero] at hpq
    simpa only [variableDifference_dvd_iff i j hij] using hpq

/-- Distinct ordered pairs give distinct prime factors of the Vandermonde. -/
theorem variableDifferences_relPrime {r : ℕ} (i j k l : Fin r)
    (hij : i < j) (hkl : k < l) (hne : (i, j) ≠ (k, l)) :
    IsRelPrime (MvPolynomial.X i - MvPolynomial.X j : Alphabet r)
      (MvPolynomial.X k - MvPolynomial.X l) := by
  classical
  apply (variableDifference_prime i j hij.ne).irreducible.isRelPrime_iff_not_dvd.mpr
  rw [variableDifference_dvd_iff i j hij.ne]
  simp only [identifyVariables, map_sub, MvPolynomial.rename_X, sub_eq_zero]
  intro he
  have he := MvPolynomial.X_injective he
  split_ifs at he with hk hl hl
  · exact hkl.ne (hk.trans hl.symm)
  · have hlj : l = j := he.symm
    exact hne (Prod.ext hk.symm hlj.symm)
  · have hkj : k = j := he
    have : l = i := hl
    subst k
    subst l
    exact (not_lt_of_ge hij.le) hkl
  · exact hkl.ne he

/-- Setting two variables equal makes two rows of the determinant equal. -/
theorem variableDifference_dvd_alternant {r : ℕ} (b : Fin r → ℕ)
    (i j : Fin r) (hij : i ≠ j) :
    (MvPolynomial.X i - MvPolynomial.X j : Alphabet r) ∣ alternant b := by
  classical
  rw [variableDifference_dvd_iff i j hij]
  change (identifyVariables i j).toRingHom
    (Matrix.of fun k l : Fin r => (MvPolynomial.X k : Alphabet r) ^ b l).det = 0
  rw [RingHom.map_det]
  apply Matrix.det_zero_of_row_eq hij
  funext l
  simp [RingHom.mapMatrix_apply, identifyVariables, hij.symm]

/-- All unordered variable differences divide the alternant simultaneously. -/
theorem vandermonde_dvd_alternant {r : ℕ} (b : Fin r → ℕ) :
    vandermonde r ∣ alternant b := by
  classical
  let pairs : Finset (Fin r × Fin r) := Finset.univ.filter (fun z => z.1 < z.2)
  have hp : (pairs : Set (Fin r × Fin r)).Pairwise
      (fun a c => IsRelPrime
        (MvPolynomial.X a.1 - MvPolynomial.X a.2 : Alphabet r)
        (MvPolynomial.X c.1 - MvPolynomial.X c.2 : Alphabet r)) := by
    intro a ha c hc hne
    exact variableDifferences_relPrime a.1 a.2 c.1 c.2
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hc).2 hne
  have hd := Finset.prod_dvd_of_isRelPrime hp (fun z hz =>
    variableDifference_dvd_alternant b z.1 z.2 (Finset.mem_filter.mp hz).2.ne)
  have he : (∏ z ∈ pairs, (MvPolynomial.X z.1 - MvPolynomial.X z.2 : Alphabet r)) =
      vandermonde r := by
    rw [vandermonde_product]
    simp only [pairs, Finset.prod_filter]
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rwa [he] at hd

theorem vandermonde_ne_zero (r : ℕ) : vandermonde r ≠ 0 := by
  classical
  rw [vandermonde_product]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro he
  have hij := MvPolynomial.X_injective he
  exact (Finset.mem_Ioi.mp hj).ne hij

theorem vandermonde_dvd_partitionAlternant {n : ℕ} (p : Partition n) (r : ℕ) :
    vandermonde r ∣ partitionAlternant r p :=
  vandermonde_dvd_alternant _

theorem schurPolynomial_characterization {n : ℕ} (p : Partition n) (r : ℕ)
    (hp : length p ≤ r) :
    vandermonde r * schurPolynomial p r = partitionAlternant r p := by
  rw [schurPolynomial, Specs.AdvancedFiniteGroupRepresentations.schurPolynomial,
    ite_eq_left hp]
  obtain ⟨q, hq⟩ := vandermonde_dvd_partitionAlternant p r
  exact Classical.epsilon_spec (p := fun q : Alphabet r =>
    vandermonde r * q = partitionAlternant r p) ⟨q, hq.symm⟩

theorem schurPolynomial_unique {n : ℕ} (p : Partition n) (r : ℕ)
    (hp : length p ≤ r) (q : Alphabet r)
    (hq : vandermonde r * q = partitionAlternant r p) :
    q = schurPolynomial p r := by
  exact mul_left_cancel₀ (vandermonde_ne_zero r)
    (hq.trans (schurPolynomial_characterization p r hp).symm)

theorem schurPolynomial_eq_zero_of_length_gt {n r : ℕ} (p : Partition n)
    (hp : r < length p) : schurPolynomial p r = 0 := by
  simp [schurPolynomial, Specs.AdvancedFiniteGroupRepresentations.schurPolynomial,
    Nat.not_le.mpr hp]

/-- The signs from the numerator and denominator cancel in the integral domain. -/
theorem schurPolynomial_isSymmetric {n : ℕ} (p : Partition n) (r : ℕ) :
    (schurPolynomial p r).IsSymmetric := by
  by_cases hp : length p ≤ r
  · intro σ
    have hc := congrArg (MvPolynomial.rename σ) (schurPolynomial_characterization p r hp)
    have ha : MvPolynomial.rename σ (partitionAlternant r p) =
        Equiv.Perm.sign σ • partitionAlternant r p := rename_alternant _ σ
    rw [map_mul, ha] at hc
    have hv : MvPolynomial.rename σ (vandermonde r) =
        Equiv.Perm.sign σ • vandermonde r := rename_alternant _ σ
    rw [hv, smul_mul_assoc] at hc
    have hh := congrArg (fun q : Alphabet r => (Equiv.Perm.sign σ)⁻¹ • q) hc
    simp only [inv_smul_smul] at hh
    exact schurPolynomial_unique p r hp _ hh
  · rw [schurPolynomial_eq_zero_of_length_gt p (Nat.lt_of_not_ge hp)]
    exact MvPolynomial.IsSymmetric.zero

theorem empty_partitionAlternant (r : ℕ) :
    partitionAlternant r emptyPartition = vandermonde r := by
  have he : shiftedPartition r emptyPartition = staircase r := by
    funext i
    have hz := rowLength_zero_of_length_le emptyPartition i.val
      (by rw [empty_length]; exact Nat.zero_le _)
    change rowLength emptyPartition i.val + staircase r i = staircase r i
    rw [hz, zero_add]
  change alternant (shiftedPartition r emptyPartition) = alternant (staircase r)
  rw [he]

theorem empty_schurPolynomial (r : ℕ) : schurPolynomial emptyPartition r = 1 := by
  symm
  apply schurPolynomial_unique emptyPartition r (by rw [empty_length]; exact Nat.zero_le _) 1
  rw [mul_one, empty_partitionAlternant]

theorem schurPolynomial_no_variables {n : ℕ} (p : Partition n) :
    schurPolynomial p 0 = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst n
    rw [zero_partition_unique p, empty_schurPolynomial]
  · apply schurPolynomial_eq_zero_of_length_gt
    by_contra hp
    have hz : length p = 0 := by omega
    have he : parts p = [] := List.length_eq_zero_iff.mp hz
    have hs := parts_sum p
    rw [he, List.sum_nil] at hs
    exact hn hs.symm

/-- Forget the order of a weakly increasing word. Sortedness will make this
map a bijection, so no multinomial coefficients occur in `h`. -/
def weakWordToSym {r k : ℕ} (w : {w : Word r k // Monotone w}) : Sym (Fin r) k :=
  ⟨(List.ofFn w.val : Multiset (Fin r)), by simp⟩

theorem weakWordToSym_bijective (r k : ℕ) :
    Function.Bijective (@weakWordToSym r k) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply List.ofFn_injective
    have hp : (List.ofFn a.val).Perm (List.ofFn b.val) :=
      Multiset.coe_eq_coe.mp (congrArg Subtype.val hab)
    exact List.Perm.eq_of_pairwise'
      (List.pairwise_ofFn.mpr (fun _ _ h => a.property h.le))
      (List.pairwise_ofFn.mpr (fun _ _ h => b.property h.le)) hp
  · intro s
    let l := s.val.sort (· ≤ ·)
    have hl : l.length = k := (Multiset.length_sort (· ≤ ·)).trans s.property
    let w : Word r k := fun i => l.get (Fin.cast hl.symm i)
    have hw : Monotone w :=
      ((Multiset.pairwise_sort s.val (· ≤ ·)).sortedLE.monotone_get).comp
        (fun _ _ h => h)
    refine ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    change (List.ofFn w : Multiset (Fin r)) = s.val
    have he : List.ofFn w = l := by
      rw [show w = fun i => l.get (Fin.cast hl.symm i) from rfl,
        ← List.ofFn_congr hl l.get, List.ofFn_get]
    rw [he]
    exact Multiset.sort_eq _ _

/-- Bridge to the library's complete homogeneous symmetric polynomial,
proved for the actual upstream weak-word sum. -/
theorem h_eq_hsymm (r k : ℕ) : h r (k : ℤ) = MvPolynomial.hsymm (Fin r) ℂ k := by
  classical
  rw [h_nat]
  change (∑ w ∈ Finset.univ.filter Monotone, wordWeight w) = _
  rw [Finset.sum_subtype (p := fun w : Word r k => Monotone w) _ (fun w => by simp)]
  unfold MvPolynomial.hsymm
  apply Fintype.sum_bijective weakWordToSym (weakWordToSym_bijective r k) _ _
  intro w
  change (∏ i : Fin k, MvPolynomial.X (w.val i)) =
    ((List.ofFn w.val : Multiset (Fin r)).map MvPolynomial.X).prod
  simp [List.prod_ofFn]

theorem multisetMonomial {r : ℕ} (f : Fin r →₀ ℕ) :
    (f.toMultiset.map (MvPolynomial.X : Fin r → Alphabet r)).prod =
      MvPolynomial.monomial f 1 := by
  classical
  induction f using Finsupp.induction with
  | zero => simp [Finsupp.toMultiset_zero]
  | @single_add a k f ha hk ih =>
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, ih,
      Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul]
    simp only [Multiset.map_singleton, Multiset.prod_singleton,
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul]

theorem h_eq_sum_monomial (r k : ℕ) :
    h r (k : ℤ) = ∑ f ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin r)) k,
      MvPolynomial.monomial f (1 : ℂ) := by
  classical
  let e := Sym.equivNatSum (Fin r) k
  let : Fintype {f : Fin r →₀ ℕ // f.sum (fun _ => id) = k} :=
    Fintype.ofEquiv (Sym (Fin r) k) e
  rw [h_eq_hsymm]
  calc
    MvPolynomial.hsymm (Fin r) ℂ k =
        ∑ s : Sym (Fin r) k, MvPolynomial.monomial (e s).val (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro s _
      have he : (e s).val.toMultiset = s.val := by
        exact Multiset.toFinsupp_toMultiset s.val
      rw [← multisetMonomial, he]
    _ = ∑ f : {f : Fin r →₀ ℕ // f.sum (fun _ => id) = k},
        MvPolynomial.monomial f.val (1 : ℂ) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      symm
      apply Finset.sum_subtype
      intro f
      simp [Finset.mem_finsuppAntidiag, Finsupp.sum_fintype]

/-- The formal series in which the coefficient numbered `k` is the upstream
complete homogeneous symmetric polynomial. -/
def hGeneratingSeries (r : ℕ) : PowerSeries (Alphabet r) :=
  PowerSeries.mk (fun k => h r (k : ℤ))

def variableGeometricSeries {r : ℕ} (i : Fin r) : PowerSeries (Alphabet r) :=
  PowerSeries.mk (fun k => (MvPolynomial.X i : Alphabet r) ^ k)

/-- The weak-word generating function, in formal power series. -/
theorem hGeneratingSeries_eq_product (r : ℕ) :
    hGeneratingSeries r = ∏ i : Fin r, variableGeometricSeries i := by
  classical
  apply PowerSeries.ext
  intro k
  rw [hGeneratingSeries, PowerSeries.coeff_mk, h_eq_sum_monomial,
    PowerSeries.coeff_prod]
  apply Finset.sum_congr rfl
  intro f _
  simp only [variableGeometricSeries, PowerSeries.coeff_mk]
  symm
  have he : Finsupp.equivFunOnFinite.symm (fun i => f i) = f := by ext i; rfl
  simpa only [he] using prod_X_pow_eq_monomial (fun i => f i)

/-- Place an ordinary formal series in the indicated variable of a
multivariate formal series ring. -/
def seriesInVariable {R : Type*} [CommRing R] {r : ℕ} (i : Fin r) :
    PowerSeries R →ₐ[R] MvPowerSeries (Fin r) R :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.X i)

theorem coeff_seriesInVariable {R : Type*} [CommRing R] {r : ℕ}
    (i : Fin r) (f : PowerSeries R) (d : Fin r →₀ ℕ) :
    MvPowerSeries.coeff d (seriesInVariable i f) =
      if d = Finsupp.single i (d i) then PowerSeries.coeff (d i) f else 0 :=
  by
    rw [seriesInVariable, PowerSeries.coe_substAlgHom]
    exact PowerSeries.coeff_subst_single i f d

/-- Coefficient extraction factors for series in disjoint single variables. -/
theorem coeff_product_seriesInVariable {R : Type*} [CommRing R] [IsDomain R] {r : ℕ}
    (f : Fin r → PowerSeries R) (d : Fin r →₀ ℕ) :
    MvPowerSeries.coeff d (∏ i : Fin r, seriesInVariable i (f i)) =
      ∏ i : Fin r, PowerSeries.coeff (d i) (f i) := by
  classical
  let L : Fin r →₀ (Fin r →₀ ℕ) :=
    Finsupp.equivFunOnFinite.symm (fun i => Finsupp.single i (d i))
  have hL : ∑ i : Fin r, L i = d := by
    ext j
    simp [L]
  rw [MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single L]
  · apply Finset.prod_congr rfl
    intro i _
    rw [coeff_seriesInVariable]
    simp [L]
  · intro l hl hne
    by_contra hn
    have ht : ∀ i : Fin r, l i = Finsupp.single i (l i i) := by
      intro i
      have hi := (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
      rw [coeff_seriesInVariable] at hi
      exact of_not_not (fun he => hi (ite_eq_right he))
    have hs : ∑ i : Fin r, l i = d := (Finset.mem_finsuppAntidiag.mp hl).1
    have hs' : (∑ i : Fin r, Finsupp.single i (l i i)) = d := by
      calc
        _ = ∑ i : Fin r, l i := by
          apply Finset.sum_congr rfl
          intro i _
          exact (ht i).symm
        _ = d := hs
    have hd : ∀ i : Fin r, l i i = d i := by
      intro i
      have hi := congrArg (fun a : Fin r →₀ ℕ => a i) hs'
      simp only [Finsupp.finsetSum_apply] at hi
      simpa [Finsupp.single_apply] using hi
    apply hne
    apply Finsupp.ext
    intro i
    change l i = Finsupp.single i (d i)
    rw [ht i, hd i]
  · intro hnot
    exact (hnot (Finset.mem_finsuppAntidiag.mpr ⟨hL, Finset.subset_univ _⟩)).elim

def seriesAlternant (R : Type*) [CommRing R] {r : ℕ} (b : Fin r → ℕ) :
    MvPowerSeries (Fin r) R :=
  (Matrix.of fun i j : Fin r => (MvPowerSeries.X i : MvPowerSeries (Fin r) R) ^ b j).det

theorem seriesAlternant_eq_sum_monomial (R : Type*) [CommRing R] {r : ℕ}
    (b : Fin r → ℕ) :
    seriesAlternant R b = ∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ •
      MvPowerSeries.monomial
        (Finsupp.equivFunOnFinite.symm (fun i => b (σ.symm i))) (1 : R) := by
  classical
  rw [seriesAlternant, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  calc
    (∏ i : Fin r, (MvPowerSeries.X (σ i) : MvPowerSeries (Fin r) R) ^ b i) =
        ∏ i : Fin r, (MvPowerSeries.X i : MvPowerSeries (Fin r) R) ^ b (σ.symm i) := by
      apply Fintype.prod_equiv σ
      intro i
      simp
    _ = _ := by
      simp only [MvPowerSeries.X_pow_eq]
      rw [MvPowerSeries.prod_monomial]
      simp only [Finset.prod_const_one]
      have he : (∑ i : Fin r, Finsupp.single i (b (σ.symm i))) =
          Finsupp.equivFunOnFinite.symm (fun i => b (σ.symm i)) := by
        ext i
        simp [Finsupp.single_apply]
      rw [he]

theorem det_staircase_product {R : Type*} [CommRing R] (φ : ℂ →+* R)
    {r : ℕ} (x : Fin r → R) :
    (Matrix.of fun i j : Fin r => x i ^ staircase r j).det =
      ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (x i - x j) := by
  let F := MvPolynomial.eval₂Hom φ x
  calc
    _ = F (vandermonde r) := by
      change _ = F (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ staircase r j).det
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [F, RingHom.mapMatrix_apply]
    _ = _ := by
      rw [vandermonde_product]
      simp [F]

theorem coeff_intUnit_smul {R : Type*} [CommRing R] {r : ℕ}
    (d : Fin r →₀ ℕ) (u : ℤˣ) (f : MvPowerSeries (Fin r) R) :
    MvPowerSeries.coeff d (u • f) = u • MvPowerSeries.coeff d f := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h, Units.smul_def]

def cauchyMatrixSeries (r : ℕ) :
    Matrix (Fin r) (Fin r) (MvPowerSeries (Fin r) (Alphabet r)) :=
  Matrix.of fun i j => seriesInVariable j (variableGeometricSeries i)

theorem coeff_cauchyMatrixSeries_det (r : ℕ) (d : Fin r →₀ ℕ) :
    MvPowerSeries.coeff d (cauchyMatrixSeries r).det = alternant (fun i => d i) := by
  classical
  rw [Matrix.det_apply]
  simp only [map_sum, coeff_intUnit_smul, cauchyMatrixSeries, Matrix.of_apply,
    coeff_product_seriesInVariable, variableGeometricSeries, PowerSeries.coeff_mk]
  rw [alternant, Specs.AdvancedFiniteGroupRepresentations.alternant, Matrix.det_apply]
  rfl

theorem cauchyMatrixSeries_det (r : ℕ) :
    (cauchyMatrixSeries r).det =
      MvPowerSeries.C (vandermonde r) * seriesAlternant (Alphabet r) (staircase r) *
        ∏ j : Fin r, seriesInVariable j (hGeneratingSeries r) := by
  classical
  let : IsDomain (MvPowerSeries (Fin r) (Alphabet r)) := NoZeroDivisors.to_isDomain _
  let x : Fin r → MvPowerSeries (Fin r) (Alphabet r) :=
    fun i => MvPowerSeries.C (MvPolynomial.X i)
  let y : Fin r → MvPowerSeries (Fin r) (Alphabet r) := MvPowerSeries.X
  have hz : ∀ i j, cauchyMatrixSeries r i j * (1 - x i * y j) = 1 := by
    intro i j
    have he := congrArg (seriesInVariable (R := Alphabet r) j)
      (geometricSeries_mul_one_sub (MvPolynomial.X i : Alphabet r))
    simpa only [map_mul, map_sub, map_one, seriesInVariable,
      PowerSeries.substAlgHom_X, PowerSeries.coe_substAlgHom, PowerSeries.subst_C,
      cauchyMatrixSeries, Matrix.of_apply, variableGeometricSeries, geometricSeries,
      x, y] using he
  rw [cauchy_det_of_inverse r x y _ hz]
  have hx : (∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (x i - x j)) =
      MvPowerSeries.C (vandermonde r) := by
    rw [vandermonde_product]
    simp [x]
  have hy : (∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (y i - y j)) =
      seriesAlternant (Alphabet r) (staircase r) := by
    exact (det_staircase_product (algebraMap ℂ _) y).symm
  have hp : (∏ i : Fin r, ∏ j : Fin r, cauchyMatrixSeries r i j) =
      ∏ j : Fin r, seriesInVariable j (hGeneratingSeries r) := by
    change (∏ i : Fin r, ∏ j : Fin r, seriesInVariable j (variableGeometricSeries i)) = _
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    rw [hGeneratingSeries_eq_product, map_prod]
  simp only [Finset.prod_mul_distrib]
  rw [hx, hy, hp]

/-- Multiplying by a monomial shifts all nonnegative coefficient indices;
negative shifted indices vanish by the source convention for `h`. -/
theorem coeff_monomial_hProduct (r : ℕ) (d e : Fin r →₀ ℕ) :
    MvPowerSeries.coeff d
      (MvPowerSeries.monomial e (1 : Alphabet r) *
        ∏ i : Fin r, seriesInVariable i (hGeneratingSeries r)) =
      ∏ i : Fin r, h r ((d i : ℤ) - (e i : ℤ)) := by
  classical
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases he : e ≤ d
  · rw [ite_eq_left he, one_mul, coeff_product_seriesInVariable]
    apply Finset.prod_congr rfl
    intro i _
    rw [hGeneratingSeries, PowerSeries.coeff_mk]
    congr 1
    have hi : e i ≤ d i := he i
    simp only [Finsupp.tsub_apply, Int.ofNat_sub hi]
  · rw [ite_eq_right he]
    symm
    obtain ⟨i, hi⟩ : ∃ i : Fin r, d i < e i := by
      simpa only [Finsupp.le_def, not_forall, not_le] using he
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply h_neg
    omega

theorem coeff_seriesAlternant_hProduct (r : ℕ) (d : Fin r →₀ ℕ) :
    MvPowerSeries.coeff d
      (seriesAlternant (Alphabet r) (staircase r) *
        ∏ i : Fin r, seriesInVariable i (hGeneratingSeries r)) =
      (Matrix.of fun i j : Fin r => h r ((d i : ℤ) - (staircase r j : ℤ))).det := by
  classical
  rw [seriesAlternant_eq_sum_monomial, Finset.sum_mul, Matrix.det_apply]
  simp only [smul_mul_assoc, map_sum, coeff_intUnit_smul, coeff_monomial_hProduct]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply Fintype.prod_equiv σ.symm
  intro i
  simp

/-- Polynomial Jacobi–Trudi identity with an arbitrary nonnegative exponent
vector. The partition specialization uses `b = λ + δ`. -/
theorem vandermonde_mul_hDet {r : ℕ} (b : Fin r → ℕ) :
    vandermonde r *
      (Matrix.of fun i j : Fin r => h r ((b i : ℤ) - (staircase r j : ℤ))).det =
        alternant b := by
  let d := Finsupp.equivFunOnFinite.symm b
  have he := congrArg (MvPowerSeries.coeff d) (cauchyMatrixSeries_det r)
  rw [coeff_cauchyMatrixSeries_det, mul_assoc, MvPowerSeries.coeff_C_mul,
    coeff_seriesAlternant_hProduct] at he
  exact he.symm

theorem vandermonde_mul_jacobiTrudi {n : ℕ} (p : Partition n) (r : ℕ) :
    vandermonde r * jacobiTrudi p r = partitionAlternant r p := by
  have he := vandermonde_mul_hDet (shiftedPartition r p)
  have hm : (Matrix.of fun i j : Fin r =>
      h r (((shiftedPartition r p i : ℕ) : ℤ) - (staircase r j : ℤ))) =
      jacobiTrudiMatrix p r := by
    apply Matrix.ext
    intro i j
    change h r _ = h r _
    congr 1
    have hi := i.isLt
    have hj := j.isLt
    change (((rowLength p i.val + (r - 1 - i.val) : ℕ) : ℤ) -
      ((r - 1 - j.val : ℕ) : ℤ)) =
      (rowLength p i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)
    omega
  rw [hm] at he
  exact he

theorem schurPolynomial_eq_jacobiTrudi {n : ℕ} (p : Partition n) (r : ℕ)
    (hp : length p ≤ r) : schurPolynomial p r = jacobiTrudi p r := by
  exact (schurPolynomial_unique p r hp _ (vandermonde_mul_jacobiTrudi p r)).symm

end AdvancedFiniteGroupRepresentations
