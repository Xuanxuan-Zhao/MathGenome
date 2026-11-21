import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SchurTableauFormula
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.PowerSumsAlternants
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StableSymmetricFunctions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators DirectSum
namespace AdvancedFiniteGroupRepresentations

abbrev deleteLast := Specs.AdvancedFiniteGroupRepresentations.deleteLast
abbrev PolynomialFamily := Specs.AdvancedFiniteGroupRepresentations.PolynomialFamily
abbrev IsCompatible := Specs.AdvancedFiniteGroupRepresentations.IsCompatible
abbrev stableDegree := Specs.AdvancedFiniteGroupRepresentations.stableDegree
abbrev StableSymmetricRing := Specs.AdvancedFiniteGroupRepresentations.StableSymmetricRing
abbrev stableRealization := Specs.AdvancedFiniteGroupRepresentations.stableRealization
abbrev stableSpecialization := Specs.AdvancedFiniteGroupRepresentations.stableSpecialization
abbrev degreeSpecialization := Specs.AdvancedFiniteGroupRepresentations.degreeSpecialization
abbrev stableMonomialCoefficient := @Specs.AdvancedFiniteGroupRepresentations.stableMonomialCoefficient

abbrev stablePartitionPowerSum := @Specs.AdvancedFiniteGroupRepresentations.stablePartitionPowerSum
abbrev stableSchur := @Specs.AdvancedFiniteGroupRepresentations.stableSchur
abbrev powerSumSynthesis := Specs.AdvancedFiniteGroupRepresentations.powerSumSynthesis
abbrev powerSumCoordinates := Specs.AdvancedFiniteGroupRepresentations.powerSumCoordinates
abbrev hallPairing := Specs.AdvancedFiniteGroupRepresentations.hallPairing

@[simp] theorem deleteLast_X_castSucc (r : ℕ) (i : Fin r) :
    deleteLast r (MvPolynomial.X i.castSucc) = MvPolynomial.X i := by
  simp [deleteLast, Specs.AdvancedFiniteGroupRepresentations.deleteLast]

@[simp] theorem deleteLast_X_last (r : ℕ) :
    deleteLast r (MvPolynomial.X (Fin.last r)) = 0 := by
  simp [deleteLast, Specs.AdvancedFiniteGroupRepresentations.deleteLast]

theorem degreeSpecialization_compatible (n r : ℕ) (f : stableDegree n) :
    deleteLast r (degreeSpecialization n (r+1) f) = degreeSpecialization n r f :=
  f.property.1 r

@[simp] theorem stableSpecialization_of (n r : ℕ) (f : stableDegree n) :
    stableSpecialization r (DirectSum.of (fun n => stableDegree n) n f) = f.val r := by
  change (DirectSum.coeAlgHom stableDegree (DirectSum.of _ n f)) r = _
  rw [DirectSum.coeAlgHom_of]

theorem stableSpecialization_mul (r : ℕ) (f g : StableSymmetricRing) :
    stableSpecialization r (f * g) = stableSpecialization r f * stableSpecialization r g :=
  map_mul _ _ _

/-- Homogeneous projection recovers a grade from its simultaneous realization. -/
theorem homogeneousComponent_stableRealization (f : StableSymmetricRing) (n r : ℕ) :
    MvPolynomial.homogeneousComponent n (stableRealization f r) = (f n).val r := by
  induction f using DirectSum.induction_on with
  | zero => simp [stableRealization, Specs.AdvancedFiniteGroupRepresentations.stableRealization]
  | of i f =>
    change MvPolynomial.homogeneousComponent n
      ((DirectSum.coeAlgHom stableDegree (DirectSum.of _ i f)) r) = _
    rw [DirectSum.coeAlgHom_of, MvPolynomial.homogeneousComponent_of_mem (f.property.2 r).2]
    by_cases h : i = n
    · subst i
      simp
    · simp [h, Ne.symm h, DirectSum.of_apply]
  | add f g hf hg =>
    simpa using congrArg₂ (· + ·) hf hg

theorem stableRealization_injective : Function.Injective stableRealization := by
  intro f g h
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  funext r
  rw [← homogeneousComponent_stableRealization f n r,
    ← homogeneousComponent_stableRealization g n r, h]

/-- The zeroth power sum is excluded: it is the alphabet size, hence is
not compatible. All positive power sums have the required deletion rule. -/
theorem deleteLast_powerSum (r j : ℕ) (hj : 0 < j) :
    deleteLast r (powerSum (r+1) j) = powerSum r j := by
  simp only [powerSum, Specs.AdvancedFiniteGroupRepresentations.powerSum, map_sum, map_pow]
  rw [Fin.sum_univ_castSucc]
  simp [Nat.ne_of_gt hj]

theorem partitionPowerSum_compatible {n : ℕ} (ν : Partition n) :
    IsCompatible (fun r => partitionPowerSum r ν) := by
  intro r
  simp only [partitionPowerSum, Specs.AdvancedFiniteGroupRepresentations.partitionPowerSum,
    map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro j hj
  rw [deleteLast_powerSum r j (ν.parts_pos (Multiset.mem_toFinset.mp hj))]

theorem partitionPowerSum_mem_stableDegree {n : ℕ} (ν : Partition n) :
    (fun r => partitionPowerSum r ν) ∈ stableDegree n := by
  refine ⟨partitionPowerSum_compatible ν, fun r => ⟨?_, partitionPowerSum_isHomogeneous r ν⟩⟩
  change (∏ j ∈ ν.parts.toFinset, powerSum r j ^ cycleMultiplicity ν j).IsSymmetric
  apply (MvPolynomial.symmetricSubalgebra (Fin r) ℂ).prod_mem
  intro j hj
  apply (MvPolynomial.symmetricSubalgebra (Fin r) ℂ).pow_mem
  exact MvPolynomial.psum_isSymmetric (Fin r) ℂ j

/-- Deleting the last variable is the library's coordinate-complement map. -/
theorem deleteLast_eq_killCompl (r : ℕ) :
    deleteLast r = MvPolynomial.killCompl (R := ℂ) (Fin.castSucc_injective r) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [deleteLast_X_last]
    simp [MvPolynomial.killCompl]
  · rw [deleteLast_X_castSucc]
    have h := MvPolynomial.killCompl_rename_app (R := ℂ) (Fin.castSucc_injective r)
      (MvPolynomial.X j)
    simpa using h.symm

theorem coeff_deleteLast (r : ℕ) (p : Alphabet (r+1)) (d : Fin r →₀ ℕ) :
    (deleteLast r p).coeff d = p.coeff (d.mapDomain Fin.castSucc) := by
  rw [deleteLast_eq_killCompl]
  exact MvPolynomial.coeff_killCompl _

theorem partition_length_le_size {n : ℕ} (p : Partition n) : length p ≤ n := by
  exact (List.length_le_sum_of_one_le _ (fun j hj => parts_positive p j hj)).trans_eq
    (parts_sum p)

/-- Zero padding of a partition is precisely extension of its exponent
finsupp by zero at the deleted variable. -/
theorem partitionExponent_castSucc {n r : ℕ} (μ : Partition n) (hμ : length μ ≤ r) :
    (Finsupp.equivFunOnFinite.symm (fun i : Fin r => rowLength μ i.val)).mapDomain
        Fin.castSucc =
      Finsupp.equivFunOnFinite.symm (fun i : Fin (r+1) => rowLength μ i.val) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Finsupp.mapDomain_of_notMem_range]
    · exact (rowLength_zero_of_length_le μ r hμ).symm
    · simp
  · simp only [Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective r)]
    rfl

theorem stableMonomialCoefficient_succ {n : ℕ} (f : stableDegree n)
    (μ : Partition n) (r : ℕ) (hμ : length μ ≤ r) :
    stableMonomialCoefficient f μ r = stableMonomialCoefficient f μ (r+1) := by
  change (f.val r).coeff _ = (f.val (r+1)).coeff _
  rw [← f.property.1 r, coeff_deleteLast, partitionExponent_castSucc μ hμ]

theorem stableMonomialCoefficient_of_le {n : ℕ} (f : stableDegree n)
    (μ : Partition n) (r s : ℕ) (hμ : length μ ≤ r) (hrs : r ≤ s) :
    stableMonomialCoefficient f μ r = stableMonomialCoefficient f μ s := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | @succ s hrs ih =>
    exact ih.trans (stableMonomialCoefficient_succ f μ s (hμ.trans hrs))

theorem monomialCoefficient_stable {n : ℕ} (f : stableDegree n)
    (μ : Partition n) (r s : ℕ) (hr : n ≤ r) (hs : n ≤ s) :
    stableMonomialCoefficient f μ r = stableMonomialCoefficient f μ s := by
  have hμ := partition_length_le_size μ
  exact (stableMonomialCoefficient_of_le f μ n r hμ hr).symm.trans
    (stableMonomialCoefficient_of_le f μ n s hμ hs)

/-- A coefficient using no deleted letter is preserved, even for a
nonsymmetric polynomial. -/
theorem coeff_eq_zero_of_deleteLast_eq_zero {r : ℕ} (p : Alphabet (r+1))
    (hp : deleteLast r p = 0) (d : Fin (r+1) →₀ ℕ) (hd : d (Fin.last r) = 0) :
    p.coeff d = 0 := by
  have hs : ↑d.support ⊆ Set.range (@Fin.castSucc r) := by
    intro i hi
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i <;> intro hi
    · exact False.elim ((Finsupp.mem_support_iff.mp hi) hd)
    · exact ⟨j, rfl⟩
  have he := d.mapDomain_comapDomain Fin.castSucc (Fin.castSucc_injective r) hs
  rw [← he, ← coeff_deleteLast, hp]
  rfl

/-- In degree at most r, every exponent has a zero coordinate among r+1
letters. Symmetry moves that coordinate into the position being deleted. -/
theorem eq_zero_of_deleteLast_eq_zero {r n : ℕ} (p : Alphabet (r+1))
    (hs : p.IsSymmetric) (hh : p.IsHomogeneous n) (hn : n ≤ r)
    (hp : deleteLast r p = 0) : p = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  change p.coeff d = 0
  by_cases hcoeff : p.coeff d = 0
  · exact hcoeff
  have hdegree : d.degree = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hh hcoeff
  have hz : ∃ i, d i = 0 := by
    by_contra h
    have hpos : ∀ i, 1 ≤ d i := by simpa only [not_exists, Nat.one_le_iff_ne_zero] using h
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpos i)
    have hsum' : r + 1 ≤ d.degree := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
        Finsupp.degree_eq_sum] using hsum
    omega
  obtain ⟨i, hi⟩ := hz
  let σ := Equiv.swap i (Fin.last r)
  have hz' : (d.mapDomain σ) (Fin.last r) = 0 := by
    rw [Finsupp.mapDomain_equiv_apply]
    simpa [σ] using hi
  have hzero := coeff_eq_zero_of_deleteLast_eq_zero p hp (d.mapDomain σ) hz'
  have he := MvPolynomial.coeff_rename_mapDomain σ σ.injective p d
  rw [hs σ] at he
  exact he.symm.trans hzero

theorem degreeSpecialization_injective (n r : ℕ) (hr : n ≤ r) :
    Function.Injective (degreeSpecialization n r) := by
  classical
  suffices hzero : ∀ f : stableDegree n, f.val r = 0 → f = 0 by
    intro f g hfg
    have h := hzero (f - g) (sub_eq_zero.mpr hfg)
    exact sub_eq_zero.mp h
  intro f hf
  have hge : ∀ s, r ≤ s → f.val s = 0 := by
    intro s hrs
    induction s, hrs using Nat.le_induction with
    | base => exact hf
    | @succ s hrs ih =>
      apply eq_zero_of_deleteLast_eq_zero (f.val (s+1))
        (f.property.2 (s+1)).1 (f.property.2 (s+1)).2 (hr.trans hrs)
      rw [f.property.1 s, ih]
  have hle : ∀ s, s ≤ r → f.val s = 0 := by
    intro s hsr
    have h : ∀ t, s ≤ t → f.val t = 0 → f.val s = 0 := by
      intro t hst
      induction t, hst using Nat.le_induction with
      | base => exact id
      | @succ t hst ih =>
        intro ht
        apply ih
        rw [← f.property.1 t, ht, map_zero]
    exact h r hsr hf
  apply Subtype.ext
  funext s
  exact (le_total r s).elim (hge s) (hle s)

theorem deleteLast_rename_castSucc (r : ℕ) (p : Alphabet r) :
    deleteLast r (MvPolynomial.rename Fin.castSucc p) = p := by
  rw [deleteLast_eq_killCompl]
  exact MvPolynomial.killCompl_rename_app _ p

theorem deleteLast_h (r : ℕ) (k : ℤ) : deleteLast r (h (r+1) k) = h r k := by
  classical
  by_cases hk : k < 0
  · rw [h_neg _ _ hk, h_neg _ _ hk, map_zero]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hk)
    rw [h_succ_alphabet, map_sum]
    simp only [map_mul, map_pow, deleteLast_rename_castSucc, deleteLast_X_last]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro a ha hne
      simp [hne]
    · simp

theorem deleteLast_paddedJacobiTrudi {n : ℕ} (p : Partition n) (r m : ℕ) :
    deleteLast r (paddedJacobiTrudi p (r+1) m) = paddedJacobiTrudi p r m := by
  change deleteLast r (Matrix.det _) = Matrix.det _
  rw [AlgHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  exact deleteLast_h r _

theorem schurPolynomial_compatible {n : ℕ} (p : Partition n) :
    IsCompatible (fun r => schurPolynomial p r) := by
  intro r
  change deleteLast r (schurPolynomial p (r+1)) = schurPolynomial p r
  rw [← paddedJacobiTrudi_eq_schurPolynomial p (r+1) (length p) le_rfl,
    ← paddedJacobiTrudi_eq_schurPolynomial p r (length p) le_rfl]
  exact deleteLast_paddedJacobiTrudi p r (length p)

theorem fillingWeight_isHomogeneous {n r : ℕ} {p : Partition n} (t : Filling p r) :
    (fillingWeight t).IsHomogeneous n := by
  rw [fillingWeight_eq_monomial]
  apply MvPolynomial.isHomogeneous_monomial
  simpa only [Finsupp.degree_eq_sum] using fillingContent_total t

theorem schurPolynomial_isHomogeneous {n : ℕ} (p : Partition n) (r : ℕ) :
    (schurPolynomial p r).IsHomogeneous n := by
  rw [schurPolynomial_eq_tableauSum]
  apply MvPolynomial.IsHomogeneous.sum
  intro t ht
  exact fillingWeight_isHomogeneous t

theorem schurPolynomial_mem_stableDegree {n : ℕ} (p : Partition n) :
    (fun r => schurPolynomial p r) ∈ stableDegree n :=
  ⟨schurPolynomial_compatible p,
    fun r => ⟨schurPolynomial_isSymmetric p r, schurPolynomial_isHomogeneous p r⟩⟩

theorem stablePartitionPowerSum_specialization {n : ℕ} (ν : Partition n) (r : ℕ) :
    (stablePartitionPowerSum ν).val r = partitionPowerSum r ν := by
  have he : ∃ f : stableDegree n, ∀ r, f.val r = partitionPowerSum r ν :=
    ⟨⟨_, partitionPowerSum_mem_stableDegree ν⟩, fun r => rfl⟩
  exact Classical.epsilon_spec he r

theorem stableSchur_specialization {n : ℕ} (p : Partition n) (r : ℕ) :
    (stableSchur p).val r = schurPolynomial p r := by
  have he : ∃ f : stableDegree n, ∀ r, f.val r = schurPolynomial p r :=
    ⟨⟨_, schurPolynomial_mem_stableDegree p⟩, fun r => rfl⟩
  exact Classical.epsilon_spec he r

/-- Multiplication by the Vandermonde turns a symmetric polynomial into an
alternating polynomial. -/
theorem rename_vandermonde_mul {r : ℕ} (p : Alphabet r) (hp : p.IsSymmetric)
    (σ : Equiv.Perm (Fin r)) :
    MvPolynomial.rename σ (vandermonde r * p) =
      Equiv.Perm.sign σ • (vandermonde r * p) := by
  change (MvPolynomial.rename σ) (alternant (staircase r) * p) = _
  rw [map_mul, rename_alternant, hp, smul_mul_assoc]
  rfl

theorem alternating_coefficient_comp_perm {r : ℕ} (q : Alphabet r)
    (hq : ∀ σ : Equiv.Perm (Fin r), MvPolynomial.rename σ q = Equiv.Perm.sign σ • q)
    (a : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) :
    naturalCoefficient (fun i => a (σ i)) q = Equiv.Perm.sign σ • naturalCoefficient a q := by
  have hd : (Finsupp.equivFunOnFinite.symm a).mapDomain σ.symm =
      Finsupp.equivFunOnFinite.symm (fun i => a (σ i)) := by
    ext i
    simp [Finsupp.mapDomain_equiv_apply]
  have hc := MvPolynomial.coeff_rename_mapDomain σ.symm σ.symm.injective
    q (Finsupp.equivFunOnFinite.symm a)
  rw [hd, hq, Equiv.Perm.sign_symm] at hc
  change Equiv.Perm.sign σ • naturalCoefficient (fun i => a (σ i)) q =
    naturalCoefficient a q at hc
  rw [← hc, smul_smul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem alternating_coefficient_zero_of_repeated {r : ℕ} (q : Alphabet r)
    (hq : ∀ σ : Equiv.Perm (Fin r), MvPolynomial.rename σ q = Equiv.Perm.sign σ • q)
    (a : Fin r → ℕ) (ha : ¬ Function.Injective a) : naturalCoefficient a q = 0 := by
  classical
  obtain ⟨i, j, he, hne⟩ := Function.not_injective_iff.mp ha
  have hs := alternating_coefficient_comp_perm q hq a (Equiv.swap i j)
  have hp : (fun k => a (Equiv.swap i j k)) = a := by
    funext k
    by_cases hki : k = i
    · subst k; simpa using he.symm
    by_cases hkj : k = j
    · subst k; simpa using he
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hp, Equiv.Perm.sign_swap hne] at hs
  have hz : naturalCoefficient a q = -naturalCoefficient a q := by
    simpa [Units.smul_def] using hs
  exact CharZero.eq_neg_self_iff.mp hz

theorem vandermonde_isHomogeneous (r : ℕ) :
    (vandermonde r).IsHomogeneous (staircaseDegree r) := by
  change (Matrix.of (fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ staircase r j)).det.IsHomogeneous (∑ i : Fin r, staircase r i)
  have h := powerDeterminant_weightedHomogeneous (R := ℂ) (fun _ : Fin r => (1 : ℕ)) 1
    (fun i => MvPolynomial.X i) (fun i => MvPolynomial.isHomogeneous_X ℂ i) (staircase r)
  simpa only [MvPolynomial.IsHomogeneous, smul_eq_mul, mul_one, Pi.one_def] using h

/-- Ordered alternating coefficients detect a symmetric homogeneous polynomial. -/
theorem eq_zero_of_alternating_coefficients_zero {n r : ℕ} (p : Alphabet r)
    (hp : p.IsSymmetric) (hh : p.IsHomogeneous n)
    (hc : ∀ lam : Partition n,
      naturalCoefficient (shiftedPartition r lam) (vandermonde r * p) = 0) : p = 0 := by
  classical
  have hq := rename_vandermonde_mul p hp
  have hd : (vandermonde r * p).IsHomogeneous (n + staircaseDegree r) := by
    simpa only [add_comm] using (vandermonde_isHomogeneous r).mul hh
  suffices hz : vandermonde r * p = 0 from
    (mul_eq_zero.mp hz).resolve_left (vandermonde_ne_zero r)
  apply MvPolynomial.ext
  intro d
  change (vandermonde r * p).coeff d = 0
  by_cases hcoeff : (vandermonde r * p).coeff d = 0
  · exact hcoeff
  have hdeg : d.degree = n + staircaseDegree r := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd hcoeff
  have hd' : Finsupp.equivFunOnFinite.symm (fun i => d i) = d := by ext; rfl
  suffices hz : naturalCoefficient (fun i => d i) (vandermonde r * p) = 0 by
    simpa only [naturalCoefficient, Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient, hd'] using hz
  by_cases hi : Function.Injective (fun i => d i)
  · obtain ⟨σ, hσ⟩ := exists_perm_strictAnti (fun i => d i) hi
    have hs : (∑ i : Fin r, d (σ i)) = n + staircaseDegree r := by
      rw [Equiv.sum_comp σ]
      simpa only [Finsupp.degree_eq_sum] using hdeg
    obtain ⟨lam, _, hlam⟩ := strictAnti_eq_shiftedPartition (fun i => d (σ i)) hσ hs
    have hz := hc lam
    rw [hlam, alternating_coefficient_comp_perm _ hq] at hz
    exact (smul_eq_zero_iff_eq _).mp hz
  · exact alternating_coefficient_zero_of_repeated _ hq _ hi

/-- A decreasing exponent vector of total degree n is a padded partition. -/
theorem antitone_eq_partition_rows {n r : ℕ} (a : Fin r → ℕ)
    (ha : Antitone a) (hs : ∑ i, a i = n) :
    ∃ μ : Partition n, length μ ≤ r ∧ (fun i : Fin r => rowLength μ i.val) = a := by
  let b : Fin r → ℕ := fun i => a i + staircase r i
  have hb : StrictAnti b := by
    intro i j hij
    have hle := ha hij.le
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    change a j + (r - 1 - j.val) < a i + (r - 1 - i.val)
    omega
  have hsum : (∑ i, b i) = n + staircaseDegree r := by
    simp only [b, Finset.sum_add_distrib, hs, staircaseDegree,
      Specs.AdvancedFiniteGroupRepresentations.staircaseDegree]
  obtain ⟨μ, hμ, he⟩ := strictAnti_eq_shiftedPartition b hb hsum
  refine ⟨μ, hμ, funext fun i => Nat.add_right_cancel (congrFun he i)⟩

/-- Symmetry reduces all homogeneous coefficients to the monomial orbit
representatives indexed by partitions. -/
theorem eq_zero_of_monomial_coefficients_zero {n r : ℕ} (p : Alphabet r)
    (hp : p.IsSymmetric) (hh : p.IsHomogeneous n)
    (hc : ∀ μ : Partition n,
      naturalCoefficient (fun i : Fin r => rowLength μ i.val) p = 0) : p = 0 := by
  apply MvPolynomial.ext
  intro d
  change p.coeff d = 0
  by_cases hd : p.coeff d = 0
  · exact hd
  have hdeg : d.degree = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hh hd
  let σ := Tuple.sort (α := OrderDual ℕ) (fun i : Fin r => OrderDual.toDual (d i))
  have hs : (∑ i : Fin r, d (σ i)) = n := by
    rw [Equiv.sum_comp σ]
    simpa only [Finsupp.degree_eq_sum] using hdeg
  have ha : Antitone (fun i => d (σ i)) := by
    intro i j hij
    exact Tuple.monotone_sort (α := OrderDual ℕ)
      (fun i : Fin r => OrderDual.toDual (d i)) hij
  obtain ⟨μ, _, hμ⟩ := antitone_eq_partition_rows (fun i => d (σ i)) ha hs
  have hm : d.mapDomain σ.symm = Finsupp.equivFunOnFinite.symm (fun i => d (σ i)) := by
    ext i
    simp [Finsupp.mapDomain_equiv_apply]
  have he := MvPolynomial.coeff_rename_mapDomain σ.symm σ.symm.injective p d
  rw [hp σ.symm, hm] at he
  have hz := hc μ
  rw [hμ] at hz
  exact he.symm.trans hz

/-- The stabilized monomial-sum coefficients determine the stable function. -/
theorem monomialCoefficient_ext {n : ℕ} (r : ℕ) (hr : n ≤ r)
    (f g : stableDegree n)
    (hfg : ∀ μ : Partition n, stableMonomialCoefficient f μ r = stableMonomialCoefficient g μ r) :
    f = g := by
  apply degreeSpecialization_injective n r hr
  change f.val r = g.val r
  apply sub_eq_zero.mp
  apply eq_zero_of_monomial_coefficients_zero (f.val r - g.val r)
    ((f.property.2 r).1.sub (g.property.2 r).1)
    ((f.property.2 r).2.sub (g.property.2 r).2)
  intro μ
  change (f.val r - g.val r).coeff _ = 0
  rw [MvPolynomial.coeff_sub, sub_eq_zero]
  exact hfg μ

/-- The coefficient matrix of the actual finite power-sum polynomials. -/
def alternatingPowerSumMatrix (n r : ℕ) : Matrix (Partition n) (Partition n) ℂ :=
  fun lam ν => naturalCoefficient (shiftedPartition r lam) (vandermonde r * partitionPowerSum r ν)

set_option maxHeartbeats 1200000 in
/-- Cauchy's two identities give a right inverse for this square matrix. -/
theorem alternatingPowerSumMatrix_gram (n r : ℕ) (hr : 1 ≤ r) (hn : n ≤ r)
    (lam μ : Partition n) :
    (∑ ν : Partition n, (zFactor ν : ℂ)⁻¹ *
      alternatingPowerSumMatrix n r lam ν * alternatingPowerSumMatrix n r μ ν) =
      if lam = μ then 1 else 0 := by
  classical
  have h := alternating_cauchy_coefficient r hr lam μ
    ((partition_length_le_size lam).trans hn) ((partition_length_le_size μ).trans hn)
  change pairedNaturalCoefficient _ _ (PowerSeries.coeff n
    (PowerSeries.C (pairedVandermonde r) * cauchyKernel r)) = _ at h
  rw [PowerSeries.coeff_C_mul, cauchy_identity_degree r hr n, Finset.mul_sum] at h
  have he (ν : Partition n) : pairedVandermonde r *
      ((zFactor ν : ℂ)⁻¹ • pairedPartitionPowerSum r ν) =
      (zFactor ν : ℂ)⁻¹ •
        (xAlphabet r (vandermonde r * partitionPowerSum r ν) *
         yAlphabet r (vandermonde r * partitionPowerSum r ν)) := by
    simp only [pairedVandermonde, Specs.AdvancedFiniteGroupRepresentations.pairedVandermonde,
      pairedPartitionPowerSum, Specs.AdvancedFiniteGroupRepresentations.pairedPartitionPowerSum,
      map_mul, mul_smul_comm]
    apply congrArg ((zFactor ν : ℂ)⁻¹ • ·)
    ac_rfl
  simp_rw [he] at h
  simp only [pairedNaturalCoefficient, Specs.AdvancedFiniteGroupRepresentations.pairedNaturalCoefficient, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at h
  change (∑ ν : Partition n, (zFactor ν : ℂ)⁻¹ *
    pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r μ)
      (xAlphabet r (vandermonde r * partitionPowerSum r ν) *
       yAlphabet r (vandermonde r * partitionPowerSum r ν))) = _ at h
  simp_rw [pairedNaturalCoefficient_mul] at h
  have hiff : diagram lam = diagram μ ↔ lam = μ :=
    ⟨partition_eq_of_diagram_eq lam μ, congrArg diagram⟩
  simpa only [hiff, alternatingPowerSumMatrix, mul_assoc] using h

theorem alternatingPowerSumMatrix_isUnit (n r : ℕ) (hr : 1 ≤ r) (hn : n ≤ r) :
    IsUnit (alternatingPowerSumMatrix n r) := by
  classical
  apply (Matrix.mulVec_surjective_iff_isUnit).mp
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨fun ν μ => (zFactor ν : ℂ)⁻¹ * alternatingPowerSumMatrix n r μ ν, ?_⟩
  apply Matrix.ext
  intro lam μ
  change (∑ ν : Partition n, alternatingPowerSumMatrix n r lam ν *
    ((zFactor ν : ℂ)⁻¹ * alternatingPowerSumMatrix n r μ ν)) = if lam = μ then 1 else 0
  simpa only [mul_left_comm, mul_assoc] using
    alternatingPowerSumMatrix_gram n r hr hn lam μ

/-- Coordinates obtained from the ordered monomials in Δ times the finite
specialization. These coordinates do not presuppose a power-sum basis. -/
def stableAlternatingCoordinates (n r : ℕ) : stableDegree n →ₗ[ℂ] (Partition n → ℂ) where
  toFun f lam := naturalCoefficient (shiftedPartition r lam) (vandermonde r * f.val r)
  map_add' f g := by
    ext lam
    simp [naturalCoefficient, Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient, mul_add]
  map_smul' c f := by
    ext lam
    simp [naturalCoefficient, Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient]

theorem stableAlternatingCoordinates_injective (n r : ℕ) (hn : n ≤ r) :
    Function.Injective (stableAlternatingCoordinates n r) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply degreeSpecialization_injective n r hn
  apply eq_zero_of_alternating_coefficients_zero (f.val r)
    (f.property.2 r).1 (f.property.2 r).2
  intro lam
  exact congrFun hf lam

theorem stableAlternatingCoordinates_synthesis (n r : ℕ) (c : Partition n →₀ ℂ) :
    stableAlternatingCoordinates n r (powerSumSynthesis n c) =
      (alternatingPowerSumMatrix n r).mulVec c := by
  classical
  change stableAlternatingCoordinates n r
    (Finsupp.linearCombination ℂ stablePartitionPowerSum c) = _
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype c (fun i a => a • stablePartitionPowerSum i) (fun _ => zero_smul ℂ _)]
  rw [map_sum]
  ext lam
  simp only [LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    stableAlternatingCoordinates, LinearMap.coe_mk, AddHom.coe_mk,
    stablePartitionPowerSum_specialization, Matrix.mulVec, dotProduct, alternatingPowerSumMatrix]
  apply Finset.sum_congr rfl
  intro ν _
  exact mul_comm _ _

/-- The finite Cauchy matrix proves the basis assertion directly for compatible
families, including degree zero, by using the nonempty alphabet n+1. -/
theorem powerSumSynthesis_bijective (n : ℕ) : Function.Bijective (powerSumSynthesis n) := by
  classical
  have hu := alternatingPowerSumMatrix_isUnit n (n+1) (by omega) (by omega)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
  have hsurj := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  have hcoord := stableAlternatingCoordinates_injective n (n+1) (by omega)
  constructor
  · intro c d h
    apply DFunLike.coe_injective
    apply hinj
    rw [← stableAlternatingCoordinates_synthesis, ← stableAlternatingCoordinates_synthesis, h]
  · intro f
    obtain ⟨c, hc⟩ := hsurj (stableAlternatingCoordinates n (n+1) f)
    refine ⟨Finsupp.equivFunOnFinite.symm c, hcoord ?_⟩
    rw [stableAlternatingCoordinates_synthesis]
    exact hc

theorem powerSumCoordinates_inverse (n : ℕ) :
    Function.LeftInverse (powerSumCoordinates n) (powerSumSynthesis n) ∧
    Function.RightInverse (powerSumCoordinates n) (powerSumSynthesis n) := by
  have hr : Function.RightInverse (powerSumCoordinates n) (powerSumSynthesis n) := by
    intro f
    exact Classical.epsilon_spec ((powerSumSynthesis_bijective n).2 f)
  exact ⟨fun c => (powerSumSynthesis_bijective n).1 (hr _), hr⟩

/-- The actual coordinate equivalence, with its epsilon-selected inverse
identified by the proved inverse laws. -/
def powerSumCoordinateEquiv (n : ℕ) : stableDegree n ≃ₗ[ℂ] (Partition n →₀ ℂ) :=
  (LinearEquiv.ofBijective (powerSumSynthesis n) (powerSumSynthesis_bijective n)).symm

theorem powerSumCoordinateEquiv_apply (n : ℕ) (f : stableDegree n) :
    powerSumCoordinateEquiv n f = powerSumCoordinates n f := by
  apply (powerSumSynthesis_bijective n).1
  rw [(powerSumCoordinates_inverse n).2]
  exact (LinearEquiv.ofBijective (powerSumSynthesis n)
    (powerSumSynthesis_bijective n)).apply_symm_apply f

theorem powerSumBasis : Specs.AdvancedFiniteGroupRepresentations.powerSumBasisType := by
  intro n
  refine ⟨Module.Basis.ofRepr (powerSumCoordinateEquiv n), ?_⟩
  intro ν r
  change (powerSumSynthesis n (Finsupp.single ν 1)).val r = partitionPowerSum r ν
  rw [powerSumSynthesis, Specs.AdvancedFiniteGroupRepresentations.powerSumSynthesis,
    Finsupp.linearCombination_single, one_smul, stablePartitionPowerSum_specialization]

/-- The degreewise Hall form in the proved power-sum coordinates. -/
def degreeHallPairing (n : ℕ) (f g : stableDegree n) : ℂ :=
  ∑ ν : Partition n, powerSumCoordinateEquiv n f ν *
    star (powerSumCoordinateEquiv n g ν) * (zFactor ν : ℂ)

@[simp] theorem degreeHallPairing_zero_left (n : ℕ) (g : stableDegree n) :
    degreeHallPairing n 0 g = 0 := by simp [degreeHallPairing]

@[simp] theorem degreeHallPairing_zero_right (n : ℕ) (f : stableDegree n) :
    degreeHallPairing n f 0 = 0 := by simp [degreeHallPairing]

theorem degreeHallPairing_add_left (n : ℕ) (f g h : stableDegree n) :
    degreeHallPairing n (f+g) h = degreeHallPairing n f h + degreeHallPairing n g h := by
  simp [degreeHallPairing, add_mul, Finset.sum_add_distrib]

theorem degreeHallPairing_smul_left (n : ℕ) (c : ℂ) (f g : stableDegree n) :
    degreeHallPairing n (c • f) g = c * degreeHallPairing n f g := by
  simp [degreeHallPairing, mul_assoc, Finset.mul_sum]

theorem degreeHallPairing_add_right (n : ℕ) (f g h : stableDegree n) :
    degreeHallPairing n f (g+h) = degreeHallPairing n f g + degreeHallPairing n f h := by
  simp [degreeHallPairing, mul_add, add_mul, Finset.sum_add_distrib]

theorem degreeHallPairing_smul_right (n : ℕ) (c : ℂ) (f g : stableDegree n) :
    degreeHallPairing n f (c • g) = star c * degreeHallPairing n f g := by
  simp only [degreeHallPairing, map_smul, Finsupp.smul_apply, smul_eq_mul, star_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  ring

theorem degreeHallPairing_conj_symm (n : ℕ) (f g : stableDegree n) :
    degreeHallPairing n g f = star (degreeHallPairing n f g) := by
  simp only [degreeHallPairing, star_sum, star_mul, star_star, star_natCast]
  apply Finset.sum_congr rfl
  intro ν _
  ring

/-- Each diagonal term is a positive weight times an ordinary complex norm. -/
theorem degreeHallPairing_self (n : ℕ) (f : stableDegree n) :
    degreeHallPairing n f f =
      ((∑ ν : Partition n, Complex.normSq (powerSumCoordinateEquiv n f ν) *
        (zFactor ν : ℝ) : ℝ) : ℂ) := by
  simp only [degreeHallPairing, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.star_def, Complex.mul_conj]

theorem degreeHallPairing_self_nonneg (n : ℕ) (f : stableDegree n) :
    0 ≤ (degreeHallPairing n f f).re := by
  rw [degreeHallPairing_self, Complex.ofReal_re]
  exact Finset.sum_nonneg fun ν _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem degreeHallPairing_self_eq_zero (n : ℕ) (f : stableDegree n) :
    (degreeHallPairing n f f).re = 0 ↔ f = 0 := by
  classical
  constructor
  · intro h
    rw [degreeHallPairing_self, Complex.ofReal_re] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (ν : Partition n) _ => mul_nonneg
        (Complex.normSq_nonneg (powerSumCoordinateEquiv n f ν))
        (show (0 : ℝ) ≤ zFactor ν from Nat.cast_nonneg _))).mp h
    apply (powerSumCoordinateEquiv n).injective
    rw [map_zero]
    ext ν
    have hv := hz ν (Finset.mem_univ ν)
    have hp : (zFactor ν : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (zFactor_pos ν))
    exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hv).resolve_right hp)
  · rintro rfl
    simp

theorem hallPairing_eq_sum (f g : StableSymmetricRing) :
    hallPairing f g = ∑ n ∈ f.support, degreeHallPairing n (f n) (g n) := by
  classical
  change (∑ n ∈ f.support, (powerSumCoordinates n (f n)).sum fun ν c =>
    c * star (powerSumCoordinates n (g n) ν) * (zFactor ν : ℂ)) = _
  apply Finset.sum_congr rfl
  intro n _
  rw [Finsupp.sum_fintype (powerSumCoordinates n (f n))
    (fun ν c => c * star (powerSumCoordinates n (g n) ν) * (zFactor ν : ℂ)) (by simp)]
  simp only [degreeHallPairing, powerSumCoordinateEquiv_apply]

/-- Extending the finite sum by zero permits comparison of different supports. -/
theorem hallPairing_eq_sum_of_support_subset (f g : StableSymmetricRing) (s : Finset ℕ)
    (hs : f.support ⊆ s) :
    hallPairing f g = ∑ n ∈ s, degreeHallPairing n (f n) (g n) := by
  classical
  rw [hallPairing_eq_sum]
  apply Finset.sum_subset hs
  intro n _ hn
  have hz : f n = 0 := by simpa only [DFinsupp.mem_support_iff, not_not] using hn
  simp [hz]

@[simp] theorem hallPairing_zero_left (g : StableSymmetricRing) : hallPairing 0 g = 0 := by
  classical
  simp [hallPairing_eq_sum]

@[simp] theorem hallPairing_zero_right (f : StableSymmetricRing) : hallPairing f 0 = 0 := by
  classical
  simp [hallPairing_eq_sum]

theorem hallPairing_add_left (f g h : StableSymmetricRing) :
    hallPairing (f+g) h = hallPairing f h + hallPairing g h := by
  classical
  rw [hallPairing_eq_sum_of_support_subset (f+g) h (f.support ∪ g.support) DFinsupp.support_add,
    hallPairing_eq_sum_of_support_subset f h (f.support ∪ g.support) Finset.subset_union_left,
    hallPairing_eq_sum_of_support_subset g h (f.support ∪ g.support) Finset.subset_union_right]
  simp only [DirectSum.add_apply, degreeHallPairing_add_left, Finset.sum_add_distrib]

theorem hallPairing_smul_left (c : ℂ) (f g : StableSymmetricRing) :
    hallPairing (c • f) g = c * hallPairing f g := by
  classical
  rw [hallPairing_eq_sum_of_support_subset (c • f) g f.support (DFinsupp.support_smul c f),
    hallPairing_eq_sum]
  simp only [DirectSum.smul_apply, degreeHallPairing_smul_left, Finset.mul_sum]

theorem hallPairing_add_right (f g h : StableSymmetricRing) :
    hallPairing f (g+h) = hallPairing f g + hallPairing f h := by
  classical
  simp only [hallPairing_eq_sum, DirectSum.add_apply, degreeHallPairing_add_right,
    Finset.sum_add_distrib]

theorem hallPairing_smul_right (c : ℂ) (f g : StableSymmetricRing) :
    hallPairing f (c • g) = star c * hallPairing f g := by
  classical
  simp only [hallPairing_eq_sum, DirectSum.smul_apply, degreeHallPairing_smul_right, Finset.mul_sum]

theorem hallPairing_conj_symm (f g : StableSymmetricRing) :
    hallPairing g f = star (hallPairing f g) := by
  classical
  rw [hallPairing_eq_sum_of_support_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    hallPairing_eq_sum_of_support_subset g f _ Finset.subset_union_right, star_sum]
  exact Finset.sum_congr rfl fun n _ => degreeHallPairing_conj_symm n (f n) (g n)

theorem hallPairing_positive (f : StableSymmetricRing) :
    (hallPairing f f).im = 0 ∧ 0 ≤ (hallPairing f f).re ∧
      ((hallPairing f f).re = 0 ↔ f = 0) := by
  classical
  have hn n : 0 ≤ (degreeHallPairing n (f n) (f n)).re :=
    degreeHallPairing_self_nonneg n (f n)
  rw [hallPairing_eq_sum]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Complex.im_sum, degreeHallPairing_self, Complex.ofReal_im, Finset.sum_const_zero]
  · rw [Complex.re_sum]
    exact Finset.sum_nonneg fun n _ => hn n
  · constructor
    · intro hz
      rw [Complex.re_sum] at hz
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => hn n)).mp hz
      apply DFinsupp.ext
      intro n
      by_cases hmem : n ∈ f.support
      · exact (degreeHallPairing_self_eq_zero n (f n)).mp (hzero n hmem)
      · simpa only [DFinsupp.mem_support_iff, not_not, DFinsupp.zero_apply] using hmem
    · intro hf
      subst f
      simp

@[simp] theorem hallPairing_of_left (n : ℕ) (f : stableDegree n) (g : StableSymmetricRing) :
    hallPairing (DirectSum.of (fun n => stableDegree n) n f) g = degreeHallPairing n f (g n) := by
  classical
  rw [hallPairing_eq_sum]
  change (DFinsupp.single n f).sum (fun n x => degreeHallPairing n x (g n)) = _
  rw [DFinsupp.sum_single_index (degreeHallPairing_zero_left n (g n))]

/-- The required norms of the actual power-sum basis vectors. -/
theorem hallPairing_powerSum (n : ℕ) (ν μ : Partition n) :
    hallPairing (DirectSum.of (fun n => stableDegree n) n (stablePartitionPowerSum ν))
      (DirectSum.of (fun n => stableDegree n) n (stablePartitionPowerSum μ)) =
        if ν = μ then (zFactor ν : ℂ) else 0 := by
  classical
  have hcoord (ρ : Partition n) :
      powerSumCoordinateEquiv n (stablePartitionPowerSum ρ) = Finsupp.single ρ 1 := by
    rw [powerSumCoordinateEquiv_apply]
    have hs : powerSumSynthesis n (Finsupp.single ρ 1) = stablePartitionPowerSum ρ := by
      simp [powerSumSynthesis, Specs.AdvancedFiniteGroupRepresentations.powerSumSynthesis]
    rw [← hs, (powerSumCoordinates_inverse n).1]
  rw [hallPairing_of_left, DirectSum.of_eq_same]
  simp only [degreeHallPairing, hcoord, Finsupp.single_apply]
  rw [Finset.sum_eq_single ν]
  · by_cases h : ν = μ <;> simp [h, eq_comm]
  · intro ρ _ hρ
    simp [Ne.symm hρ]
  · simp

theorem hallPairing_degrees_orthogonal (n m : ℕ) (hnm : n ≠ m)
    (f : stableDegree n) (g : stableDegree m) :
    hallPairing (DirectSum.of (fun n => stableDegree n) n f)
      (DirectSum.of (fun n => stableDegree n) m g) = 0 := by
  classical
  rw [hallPairing_of_left]
  simp [DirectSum.of_apply, Ne.symm hnm]

theorem hallPairing_spec : Specs.AdvancedFiniteGroupRepresentations.hallPairing_specType :=
  ⟨hallPairing_add_left, hallPairing_smul_left, hallPairing_add_right, hallPairing_smul_right,
    hallPairing_conj_symm, hallPairing_positive, hallPairing_powerSum, hallPairing_degrees_orthogonal⟩

end AdvancedFiniteGroupRepresentations
