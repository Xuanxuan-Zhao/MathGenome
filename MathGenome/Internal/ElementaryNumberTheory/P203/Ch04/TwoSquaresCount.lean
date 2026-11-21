import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.TwoSquaresCount
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch04.GaussianPrimes
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.Multiplicativity
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace P203.Ch04.TwoSquaresCount
open P203Specs.Ch04.TwoSquaresCount

theorem character_values : CharacterValues := ZMod.χ₄_nat_eq_if_mod_four

theorem character_multiplicative : CharacterMultiplicative := by
  refine ⟨?_, ?_⟩
  · exact map_one ZMod.χ₄
  · intro a b
    simpa only [chi4, Nat.cast_mul] using
      (map_mul ZMod.χ₄ (a : ZMod 4) (b : ZMod 4))

lemma coordinate_bounds {n : ℕ} {a b : ℤ} (h : a ^ 2 + b ^ 2 = (n : ℤ)) :
    -(n : ℤ) ≤ a ∧ a ≤ n ∧ -(n : ℤ) ≤ b ∧ b ≤ n := by
  have hn : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  constructor
  · nlinarith [sq_nonneg (a + 1)]
  constructor
  · nlinarith [sq_nonneg (a - 1)]
  constructor
  · nlinarith [sq_nonneg (b + 1)]
  · nlinarith [sq_nonneg (b - 1)]

theorem representation_finiteness : RepresentationFiniteness := by
  intro n
  apply ((Set.finite_Icc (-(n : ℤ)) n).prod (Set.finite_Icc (-(n : ℤ)) n)).subset
  intro ab hab
  obtain ⟨ha, ha', hb, hb'⟩ := coordinate_bounds hab
  exact ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩

theorem zero_representations : ZeroRepresentations := by
  have hz : representations 0 = {(0, 0)} := by
    ext ab
    rcases ab with ⟨a, b⟩
    simp only [representations, Set.mem_ofPred_eq, Nat.cast_zero, Set.mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · intro h
      have hbounds := coordinate_bounds (n := 0) h
      exact ⟨by omega, by omega⟩
    · rintro ⟨rfl, rfl⟩
      norm_num
  refine ⟨hz, ?_⟩
  simp [r2, hz]

/-- The coordinate map preserves every signed pair individually. -/
def gaussianRepresentationEquiv (n : ℕ) :
    representations n ≃ {z : GaussianInt // z.norm = (n : ℤ)} where
  toFun ab := ⟨⟨ab.1.1, ab.1.2⟩, by
    simpa [Zsqrtd.norm, pow_two, representations] using ab.2⟩
  invFun z := ⟨(z.1.re, z.1.im), by
    simpa [Zsqrtd.norm, pow_two, representations] using z.2⟩
  left_inv ab := by cases ab; rfl
  right_inv z := by cases z; rfl

theorem gaussian_count_bridge : GaussianCountBridge := by
  intro n
  exact Nat.card_congr (gaussianRepresentationEquiv n)

/-- The arithmetic function with the paper's character coefficients. -/
def characterFunction : ArithmeticFunction ℤ :=
  ⟨chi4, by norm_num [chi4, ZMod.χ₄]⟩

lemma characterFunction_multiplicative : characterFunction.IsMultiplicative := by
  refine ⟨character_multiplicative.1, ?_⟩
  intro a b _
  exact character_multiplicative.2 a b

/-- Convolution with constant one gives precisely the positive-divisor sum. -/
def divisorFunction : ArithmeticFunction ℤ :=
  characterFunction * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)

lemma divisorFunction_apply (n : ℕ) : divisorFunction n = ∑ d ∈ n.divisors, chi4 d := by
  exact ArithmeticFunction.coe_mul_zeta_apply

lemma divisorFunction_multiplicative : divisorFunction.IsMultiplicative :=
  characterFunction_multiplicative.mul (ArithmeticFunction.isMultiplicative_zeta.natCast)

lemma divisorFunction_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    divisorFunction (p ^ e) = ∑ j ∈ Finset.range (e + 1), chi4 p ^ j := by
  rw [divisorFunction_apply, Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [chi4, Nat.cast_pow] using map_pow ZMod.χ₄ (p : ZMod 4) j

lemma divisorFunction_localFactor {p : ℕ} (hp : p.Prime) (e : ℕ) :
    divisorFunction (p ^ e) = (localFactor p e : ℤ) := by
  rw [divisorFunction_prime_pow hp]
  by_cases hp2 : p = 2
  · subst p
    have hc : chi4 2 = 0 := by decide
    simp [localFactor, hc]
  · by_cases hp1 : p % 4 = 1
    · have hc : chi4 p = 1 := ZMod.χ₄_nat_one_mod_four hp1
      simp [localFactor, hp2, hp1, hc]
    · have hpodd := hp.mod_two_eq_one_iff_ne_two.mpr hp2
      have hp3 : p % 4 = 3 := by omega
      have hc : chi4 p = -1 := ZMod.χ₄_nat_three_mod_four hp3
      simp only [hc, neg_one_geom_sum, Nat.even_add_one, localFactor, ite_eq_right hp2, ite_eq_right hp1]
      by_cases he : Even e <;> simp [he]

theorem divisor_sum_factors : DivisorSumFactors := by
  intro n hn
  rw [← divisorFunction_apply, divisorFunction_multiplicative.multiplicative_factorization _ hn.ne']
  change (∏ p ∈ n.primeFactors, divisorFunction (p ^ n.factorization p)) = _
  apply Finset.prod_congr rfl
  intro p hp
  exact divisorFunction_localFactor (Nat.prime_of_mem_primeFactors hp) _

/-- Quarter turns realize multiplication by 1, i, -1, -i. -/
def rotate (k : Fin 4) (z : GaussianInt) : GaussianInt :=
  if k = 0 then z else if k = 1 then ⟨-z.im, z.re⟩
  else if k = 2 then ⟨-z.re, -z.im⟩ else ⟨z.im, -z.re⟩

lemma rotate_norm (k : Fin 4) (z : GaussianInt) : (rotate k z).norm = z.norm := by
  fin_cases k <;> simp [rotate, Zsqrtd.norm] <;> ring

lemma rotate_injective (n : ℕ) : Function.Injective
    (fun kq : Fin 4 × quarterRepresentations n => rotate kq.1 kq.2.1) := by
  rintro ⟨k, z⟩ ⟨l, w⟩ h
  have hz := z.2
  have hw := w.2
  have hr := congrArg Zsqrtd.re h
  have hi := congrArg Zsqrtd.im h
  have hval : z.1 = w.1 → z = w := Subtype.ext
  fin_cases k <;> fin_cases l <;> simp [rotate] at hr hi ⊢ <;>
    first | (exact hval (Zsqrtd.ext hr hi)) | (apply hval; apply Zsqrtd.ext <;> omega) | omega

lemma rotate_surjective {n : ℕ} (hn : 0 < n) : Function.Surjective
    (fun kq : Fin 4 × quarterRepresentations n =>
      (⟨rotate kq.1 kq.2.1, (rotate_norm _ _).trans kq.2.2.1⟩ :
        {z : GaussianInt // z.norm = (n : ℤ)})) := by
  rintro ⟨z, hz⟩
  have hnonzero : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra h
    push Not at h
    have hnorm : z.norm = 0 := by simp [Zsqrtd.norm, h.1, h.2]
    have : (n : ℤ) = 0 := hz.symm.trans hnorm
    exact hn.ne' (by exact_mod_cast this)
  by_cases h0 : 0 < z.re ∧ 0 ≤ z.im
  · refine ⟨⟨0, ⟨z, hz, h0⟩⟩, ?_⟩
    apply Subtype.ext
    simp [rotate]
  by_cases h1 : z.re ≤ 0 ∧ 0 < z.im
  · let w : GaussianInt := ⟨z.im, -z.re⟩
    have hw : w.norm = (n : ℤ) := by
      convert hz using 1; simp [w, Zsqrtd.norm]; ring
    refine ⟨⟨1, ⟨w, hw, h1.2, by dsimp [w]; omega⟩⟩, ?_⟩
    apply Subtype.ext
    ext <;> simp [rotate, w]
  by_cases h2 : z.re < 0 ∧ z.im ≤ 0
  · let w : GaussianInt := ⟨-z.re, -z.im⟩
    have hw : w.norm = (n : ℤ) := by simpa [w, Zsqrtd.norm] using hz
    refine ⟨⟨2, ⟨w, hw, by dsimp [w]; omega, by dsimp [w]; omega⟩⟩, ?_⟩
    apply Subtype.ext
    ext <;> simp [rotate, w]
  · have h3 : 0 ≤ z.re ∧ z.im < 0 := by omega
    let w : GaussianInt := ⟨-z.im, z.re⟩
    have hw : w.norm = (n : ℤ) := by
      convert hz using 1; simp [w, Zsqrtd.norm]; ring
    refine ⟨⟨3, ⟨w, hw, by dsimp [w]; omega, h3.1⟩⟩, ?_⟩
    apply Subtype.ext
    ext <;> simp [rotate, w]

/-- Every nonzero Gaussian integer is uniquely a quarter turn of an element
in the half-open first quadrant. This preserves axis representations. -/
noncomputable def fourUnitEquiv (n : ℕ) (hn : 0 < n) :
    (Fin 4 × quarterRepresentations n) ≃ {z : GaussianInt // z.norm = (n : ℤ)} :=
  Equiv.ofBijective _ ⟨fun _ _ h => rotate_injective n (congrArg Subtype.val h),
    rotate_surjective hn⟩

theorem four_unit_count : FourUnitCount := by
  intro n hn
  rw [gaussian_count_bridge n, ← Nat.card_congr (fourUnitEquiv n hn), Nat.card_prod]
  simp [quarterCount]

lemma quarter_finite (n : ℕ) : Finite (quarterRepresentations n) := by
  let : Finite (representations n) := (representation_finiteness n).to_subtype
  apply Finite.of_injective (fun z : quarterRepresentations n =>
    (gaussianRepresentationEquiv n).symm ⟨z.1, z.2.1⟩)
  intro z w h
  have hg := congrArg (gaussianRepresentationEquiv n) h
  apply Subtype.ext
  simpa only [Equiv.apply_symm_apply] using
    congrArg (fun t : {z : GaussianInt // z.norm = (n : ℤ)} => t.1) hg

/-- The half-open quadrant is a genuine transversal for association. -/
lemma quarter_associated_iff {m n : ℕ}
    (z : quarterRepresentations m) (w : quarterRepresentations n) :
    Associated z.1 w.1 ↔ z.1 = w.1 := by
  refine ⟨?_, fun h => h ▸ Associated.refl z.1⟩
  rintro ⟨u, hu⟩
  have huunit := (GaussianArithmetic.units (u : GaussianInt)).2.1.mp
    ((GaussianArithmetic.units (u : GaussianInt)).1.mp u.isUnit)
  have hzre := z.2.2.1
  have hzim := z.2.2.2
  have hwre := w.2.2.1
  have hwim := w.2.2.2
  rcases huunit with hu1 | hu1 | hu1 | hu1
  · simpa [hu1] using hu
  · rw [hu1] at hu
    have hr := congrArg Zsqrtd.re hu
    simp at hr
    omega
  · rw [hu1] at hu
    have hr := congrArg Zsqrtd.re hu
    simp at hr
    omega
  · rw [hu1] at hu
    have hi := congrArg Zsqrtd.im hu
    simp at hi
    omega

lemma quarter_count_one : quarterCount 1 = 1 := by
  have heq : ∀ z : quarterRepresentations 1, z.1 = 1 := by
    intro z
    have hnorm := z.2.1
    have hx := z.2.2.1
    have hy := z.2.2.2
    have hs : z.1.re ^ 2 + z.1.im ^ 2 = 1 := by
      simpa [Zsqrtd.norm, pow_two] using hnorm
    have hx1 : z.1.re = 1 := by nlinarith [sq_nonneg z.1.im]
    have hy0 : z.1.im = 0 := by nlinarith
    ext <;> simp [hx1, hy0]
  let z : quarterRepresentations 1 := ⟨1, by norm_num [Zsqrtd.norm]⟩
  have huniq : Unique (quarterRepresentations 1) :=
    ⟨⟨z⟩, fun w => Subtype.ext ((heq w).trans (heq z).symm)⟩
  let := huniq
  exact Nat.card_unique

lemma quarter_count_zero : quarterCount 0 = 0 := by
  have : IsEmpty (quarterRepresentations 0) := ⟨fun z => by
    have hs : z.1.re ^ 2 + z.1.im ^ 2 = 0 := by
      simpa [Zsqrtd.norm, pow_two] using z.2.1
    have hx := z.2.2.1
    nlinarith [sq_nonneg z.1.im]⟩
  exact Nat.card_of_isEmpty

/-- An alternative assembly of the Gaussian count from quadrant multiplicativity
and its prime-power values. The unconditional proof below uses norm fibers. -/
theorem gaussian_factor_count_of_quarter
    (hmul : QuarterMultiplicative) (hpow : QuarterPrimePowers) : GaussianFactorCount := by
  intro n hn
  rw [four_unit_count n hn]
  congr 1
  have hmul' : ∀ a b : ℕ, a.Coprime b →
      quarterCount (a * b) = quarterCount a * quarterCount b := by
    intro a b hab
    by_cases ha : a = 0
    · simp [ha, quarter_count_zero]
    by_cases hb : b = 0
    · simp [hb, quarter_count_zero]
    exact hmul.2 a b (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hab
  rw [Nat.multiplicative_factorization quarterCount hmul' hmul.1 hn.ne']
  change (∏ p ∈ n.primeFactors, quarterCount (p ^ n.factorization p)) = _
  apply Finset.prod_congr rfl
  intro p hp
  exact hpow p (Nat.prime_of_mem_primeFactors hp) _

/-- The finite Gaussian count also implies the divisor-sum formula through
the checked natural-to-integer conversion of the finite product. -/
theorem count_formula_of_gaussian_factor_count (hc : GaussianFactorCount) : CountFormula := by
  intro n hn
  rw [hc n hn, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_prod, divisor_sum_factors n hn]

/-- Alternative assembly from the two structural properties of quadrant counts. -/
theorem count_formula_of_quarter
    (hmul : QuarterMultiplicative) (hpow : QuarterPrimePowers) : CountFormula :=
  count_formula_of_gaussian_factor_count (gaussian_factor_count_of_quarter hmul hpow)


def normSet (n : ℕ) : Set GaussianInt := {z | z.norm = (n : ℤ)}

lemma normSet_finite (n : ℕ) : (normSet n).Finite := by
  let : Finite (representations n) := (representation_finiteness n).to_subtype
  let : Finite (normSet n) := Finite.of_equiv _ (gaussianRepresentationEquiv n)
  exact Set.toFinite _

lemma r2_eq_ncard (n : ℕ) : r2 n = (normSet n).ncard := by
  exact gaussian_count_bridge n

lemma norm_mul_mem {a : GaussianInt} {d n : ℕ} (ha : a.norm = (d : ℤ))
    (z : GaussianInt) (hz : z ∈ normSet n) : a * z ∈ normSet (d * n) := by
  change (a * z).norm = _
  rw [Zsqrtd.norm_mul, ha, hz, Nat.cast_mul]

lemma mem_normImage {a z : GaussianInt} {d n : ℕ} (hd : d ≠ 0)
    (ha : a.norm = (d : ℤ)) :
    z ∈ (fun w => a * w) '' normSet n ↔ z ∈ normSet (d * n) ∧ a ∣ z := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨norm_mul_mem ha w hw, dvd_mul_right _ _⟩
  · rintro ⟨hz, w, rfl⟩
    refine ⟨w, ?_, rfl⟩
    change w.norm = (n : ℤ)
    have he : (d : ℤ) * w.norm = (d : ℤ) * n := by
      simpa only [normSet, Set.mem_ofPred_eq, Zsqrtd.norm_mul, ha, Nat.cast_mul] using hz
    exact mul_left_cancel₀ (by exact_mod_cast hd) he

lemma normImage_card {a : GaussianInt} {d : ℕ} (hd : d ≠ 0)
    (ha : a.norm = (d : ℤ)) (n : ℕ) :
    ((fun w => a * w) '' normSet n).ncard = r2 n := by
  rw [Set.ncard_image_of_injective, r2_eq_ncard]
  apply mul_right_injective₀
  intro haz
  rw [haz] at ha
  have : (d : ℤ) = 0 := ha.symm
  exact hd (by exact_mod_cast this)

lemma conj_dvd_conj {a z : GaussianInt} (h : a ∣ star z) : star a ∣ z := by
  obtain ⟨w, hw⟩ := h
  exact ⟨star w, by simpa using congrArg star hw⟩

lemma prime_dvd_of_norm {a z : GaussianInt} {p n : ℕ}
    (hp : Prime a) (ha : a ∣ (p : GaussianInt)) (hz : z ∈ normSet (p * n)) :
    a ∣ z ∨ star a ∣ z := by
  have h : a ∣ z * star z := by
    rw [← Zsqrtd.norm_eq_mul_conj, hz, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    exact dvd_mul_of_dvd_left ha _
  exact (hp.dvd_or_dvd h).imp id conj_dvd_conj

/-- A split prime gives two images of the preceding norm fiber. -/
lemma split_union {p n : ℕ} {a : GaussianInt} (hp : p.Prime)
    (ha : a.norm = (p : ℤ)) (hprime : Prime a) :
    normSet (p * n) = (fun w => a * w) '' normSet n ∪
      (fun w => star a * w) '' normSet n := by
  have hconj : (star a).norm = (p : ℤ) := by rw [Zsqrtd.norm_conj, ha]
  ext z
  rw [Set.mem_union, mem_normImage hp.ne_zero ha, mem_normImage hp.ne_zero hconj]
  constructor
  · intro hz
    have had : a ∣ (p : GaussianInt) := by
      have he : a * star a = (p : GaussianInt) := by
        rw [← Zsqrtd.norm_eq_mul_conj, ha]; rfl
      exact he ▸ dvd_mul_right a (star a)
    exact (prime_dvd_of_norm hprime had hz).imp (fun h => ⟨hz, h⟩) (fun h => ⟨hz, h⟩)
  · exact fun h => h.elim And.left And.left

lemma both_dvd_iff {a b z : GaussianInt} (ha : Prime a) (hb : Prime b)
    (hab : ¬ Associated a b) : (a ∣ z ∧ b ∣ z) ↔ a * b ∣ z := by
  refine ⟨?_, fun h => ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩⟩
  rintro ⟨⟨w, rfl⟩, hbz⟩
  have hba : ¬ b ∣ a := fun h => hab (hb.irreducible.associated_of_dvd ha.irreducible h).symm
  obtain ⟨v, rfl⟩ := (hb.dvd_or_dvd hbz).resolve_left hba
  exact ⟨v, by ring⟩

lemma split_inter {p n : ℕ} {a : GaussianInt} (hp : p.Prime)
    (ha : a.norm = (p : ℤ)) (hprime : Prime a) (hstar : Prime (star a))
    (hnot : ¬ Associated a (star a)) :
    (fun w => a * w) '' normSet (p * n) ∩
      (fun w => star a * w) '' normSet (p * n) =
      (fun w => (p : GaussianInt) * w) '' normSet n := by
  have hs : (star a).norm = (p : ℤ) := by rw [Zsqrtd.norm_conj, ha]
  have hab : a * star a = (p : GaussianInt) := by rw [← Zsqrtd.norm_eq_mul_conj, ha]; rfl
  have hpn : (p : GaussianInt).norm = ((p * p : ℕ) : ℤ) := by simp [Zsqrtd.norm_natCast]
  ext z
  rw [Set.mem_inter_iff, mem_normImage hp.ne_zero ha, mem_normImage hp.ne_zero hs,
    mem_normImage (mul_ne_zero hp.ne_zero hp.ne_zero) hpn]
  have hd : (a ∣ z ∧ star a ∣ z) ↔ (p : GaussianInt) ∣ z := by
    rw [← hab]
    exact both_dvd_iff hprime hstar hnot
  simp only [normSet, Set.mem_ofPred_eq, Nat.cast_mul, mul_assoc]
  tauto

lemma norm_dvd_of_dvd {a z : GaussianInt} (h : a ∣ z) : a.norm ∣ z.norm := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w.norm, Zsqrtd.norm_mul a w⟩

lemma rational_not_dvd_of_norm {p n : ℕ} (hp : p.Prime) (hn : ¬ p ∣ n)
    {z : GaussianInt} (hz : z ∈ normSet (p * n)) : ¬ (p : GaussianInt) ∣ z := by
  intro h
  change z.norm = ((p * n : ℕ) : ℤ) at hz
  have hd : ((p * p : ℕ) : ℤ) ∣ ((p * n : ℕ) : ℤ) := by
    simpa [Zsqrtd.norm_natCast, hz] using norm_dvd_of_dvd h
  exact hn (Nat.dvd_of_mul_dvd_mul_left hp.pos (Int.natCast_dvd_natCast.mp hd))

lemma split_disjoint {p n : ℕ} {a : GaussianInt} (hp : p.Prime)
    (ha : a.norm = (p : ℤ)) (hprime : Prime a) (hstar : Prime (star a))
    (hnot : ¬ Associated a (star a)) (hn : ¬ p ∣ n) :
    Disjoint ((fun w => a * w) '' normSet n) ((fun w => star a * w) '' normSet n) := by
  apply Set.disjoint_left.mpr
  intro z hza hzb
  obtain ⟨hz, had⟩ := (mem_normImage hp.ne_zero ha).mp hza
  have hs : (star a).norm = (p : ℤ) := by rw [Zsqrtd.norm_conj, ha]
  have hbd := ((mem_normImage hp.ne_zero hs).mp hzb).2
  have hab : a * star a = (p : GaussianInt) := by rw [← Zsqrtd.norm_eq_mul_conj, ha]; rfl
  apply rational_not_dvd_of_norm hp hn hz
  rw [← hab]
  exact (both_dvd_iff hprime hstar hnot).mp ⟨had, hbd⟩

lemma split_count_base {p n : ℕ} {a : GaussianInt} (hp : p.Prime)
    (ha : a.norm = (p : ℤ)) (hprime : Prime a) (hstar : Prime (star a))
    (hnot : ¬ Associated a (star a)) (hn : ¬ p ∣ n) :
    r2 (p * n) = 2 * r2 n := by
  rw [r2_eq_ncard, split_union hp ha hprime,
    Set.ncard_union_eq (split_disjoint hp ha hprime hstar hnot hn)
      ((normSet_finite n).image _) ((normSet_finite n).image _),
    normImage_card hp.ne_zero ha,
    normImage_card hp.ne_zero ((Zsqrtd.norm_conj a).trans ha)]
  omega

lemma split_count_step {p n : ℕ} {a : GaussianInt} (hp : p.Prime)
    (ha : a.norm = (p : ℤ)) (hprime : Prime a) (hstar : Prime (star a))
    (hnot : ¬ Associated a (star a)) :
    r2 (p * (p * n)) + r2 n = 2 * r2 (p * n) := by
  have hc := Set.ncard_union_add_ncard_inter
    ((fun w => a * w) '' normSet (p * n))
    ((fun w => star a * w) '' normSet (p * n))
    ((normSet_finite (p * n)).image _) ((normSet_finite (p * n)).image _)
  rw [← split_union hp ha hprime, split_inter hp ha hprime hstar hnot,
    normImage_card (mul_ne_zero hp.ne_zero hp.ne_zero)
      (by simp [Zsqrtd.norm_natCast] : (p : GaussianInt).norm = ((p * p : ℕ) : ℤ)),
    normImage_card hp.ne_zero ha,
    normImage_card hp.ne_zero ((Zsqrtd.norm_conj a).trans ha), ← r2_eq_ncard] at hc
  omega

lemma rational_prime_dvd {p n : ℕ} (hp : Prime (p : GaussianInt))
    {z : GaussianInt} (hz : z ∈ normSet (p * n)) : (p : GaussianInt) ∣ z := by
  rcases prime_dvd_of_norm hp dvd_rfl hz with h | h
  · exact h
  · simpa using h

lemma inert_count_base {p n : ℕ} (hp : p.Prime) (hprime : Prime (p : GaussianInt))
    (hn : ¬ p ∣ n) : r2 (p * n) = 0 := by
  rw [r2_eq_ncard]
  have he : normSet (p * n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact rational_not_dvd_of_norm hp hn hz (rational_prime_dvd hprime hz)
  simp [he]

lemma inert_count_step {p n : ℕ} (hp : p.Prime) (hprime : Prime (p : GaussianInt)) :
    r2 (p * (p * n)) = r2 n := by
  have he : normSet (p * (p * n)) = (fun w => (p : GaussianInt) * w) '' normSet n := by
    ext z
    rw [mem_normImage (mul_ne_zero hp.ne_zero hp.ne_zero)
      (by simp [Zsqrtd.norm_natCast] : (p : GaussianInt).norm = ((p * p : ℕ) : ℤ))]
    simp only [mul_assoc]
    exact ⟨fun hz => ⟨hz, rational_prime_dvd hprime hz⟩, And.left⟩
  rw [r2_eq_ncard, he, normImage_card (mul_ne_zero hp.ne_zero hp.ne_zero)
    (by simp [Zsqrtd.norm_natCast] : (p : GaussianInt).norm = ((p * p : ℕ) : ℤ))]

lemma ramified_count (n : ℕ) : r2 (2 * n) = r2 n := by
  let a : GaussianInt := ⟨1, 1⟩
  have ha : a.norm = (2 : ℕ) := by norm_num [a, Zsqrtd.norm]
  have had : a ∣ (2 : GaussianInt) := by
    have he : a * star a = (2 : GaussianInt) := by decide
    exact he ▸ dvd_mul_right a (star a)
  have has : a ∣ star a := ⟨⟨0, -1⟩, by decide⟩
  have he : normSet (2 * n) = (fun w => a * w) '' normSet n := by
    ext z
    rw [mem_normImage (by decide : (2 : ℕ) ≠ 0) ha]
    refine ⟨fun hz => ⟨hz, ?_⟩, And.left⟩
    rcases prime_dvd_of_norm GaussianPrimes.one_add_i_prime had hz with h | h
    · exact h
    · exact dvd_trans has h
  rw [r2_eq_ncard, he, normImage_card (by decide : (2 : ℕ) ≠ 0) ha]

lemma split_count_pow_mul {p n : ℕ} {a : GaussianInt} (hp : p.Prime)
    (ha : a.norm = (p : ℤ)) (hprime : Prime a) (hstar : Prime (star a))
    (hnot : ¬ Associated a (star a)) (hn : ¬ p ∣ n) (e : ℕ) :
    r2 (p ^ e * n) = (e + 1) * r2 n := by
  induction e using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using split_count_base hp ha hprime hstar hnot hn
  | more e ih ih1 =>
    have hc := split_count_step (n := p ^ e * n) hp ha hprime hstar hnot
    have he1 : p * (p ^ e * n) = p ^ (e + 1) * n := by ring
    have he2 : p * (p * (p ^ e * n)) = p ^ (e + 2) * n := by ring
    rw [he2, he1, ih, ih1] at hc
    nlinarith

lemma inert_count_pow_mul {p n : ℕ} (hp : p.Prime) (hprime : Prime (p : GaussianInt))
    (hn : ¬ p ∣ n) (e : ℕ) :
    r2 (p ^ e * n) = (if Even e then 1 else 0) * r2 n := by
  induction e using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using inert_count_base hp hprime hn
  | more e ih ih1 =>
    have hc := inert_count_step (n := p ^ e * n) hp hprime
    have he2 : p * (p * (p ^ e * n)) = p ^ (e + 2) * n := by ring
    rw [he2, ih] at hc
    simpa [Nat.even_add] using hc

lemma ramified_count_pow_mul (n e : ℕ) : r2 (2 ^ e * n) = r2 n := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', mul_assoc, ramified_count, ih]

lemma count_prime_pow_mul {p n : ℕ} (hp : p.Prime) (hn : ¬ p ∣ n) (e : ℕ) :
    r2 (p ^ e * n) = localFactor p e * r2 n := by
  by_cases hp2 : p = 2
  · subst p
    simpa [localFactor] using ramified_count_pow_mul n e
  have hpZ : D07.Foundations.IntegerArithmetic.PositivePrime (p : ℤ) :=
    ⟨by exact_mod_cast hp.pos, by simpa using hp⟩
  by_cases hp1 : p % 4 = 1
  · have hp1Z : (p : ℤ) % 4 = 1 := by exact_mod_cast hp1
    obtain ⟨a, ha, _, _, hprime, hstar, hnot⟩ :=
      GaussianPrimes.conjugate_factorization (p : ℤ) hpZ hp1Z
    simpa [localFactor, hp2, hp1] using split_count_pow_mul hp ha hprime hstar hnot hn e
  · have hp3 : p % 4 = 3 := by
      have hodd := hp.mod_two_eq_one_iff_ne_two.mpr hp2
      omega
    have hprime : Prime (p : GaussianInt) := by
      have h := (GaussianPrimes.rational_prime_criterion (p : ℤ) hpZ).mpr
        (by exact_mod_cast hp3)
      simpa using h
    simpa [localFactor, hp2, hp1] using inert_count_pow_mul hp hprime hn e

lemma r2_one : r2 1 = 4 := by
  rw [four_unit_count 1 (by decide), quarter_count_one]

/-- The norm-fiber recurrences and the character convolution have the same
local factors. Prime-power induction therefore gives their exact equality. -/
theorem count_formula : CountFormula := by
  have main : ∀ n : ℕ, n ≠ 0 → (r2 n : ℤ) = 4 * divisorFunction n := by
    apply Nat.recOnPrimePow
    · exact fun h => (h rfl).elim
    · intro _
      rw [r2_one, divisorFunction_apply]
      norm_num [chi4, ZMod.χ₄]
    · intro n p e hp hpn _ ih hne
      have hn : n ≠ 0 := right_ne_zero_of_mul hne
      rw [count_prime_pow_mul hp hpn e, Nat.cast_mul,
        divisorFunction_multiplicative.map_mul_of_coprime
          ((hp.coprime_iff_not_dvd.mpr hpn).pow_left e),
        divisorFunction_localFactor hp e, ih hn]
      ring
  intro n hn
  simpa only [divisorFunction_apply] using main n hn.ne'

/-- This is the full finite Gaussian factor count, including all four units. -/
theorem gaussian_factor_count : GaussianFactorCount := by
  intro n hn
  have h := count_formula n hn
  rw [divisor_sum_factors n hn] at h
  exact_mod_cast h

lemma quarter_prime_powers : QuarterPrimePowers := by
  intro p hp e
  have h := count_prime_pow_mul hp hp.not_dvd_one e
  rw [mul_one, r2_one] at h
  rw [four_unit_count (p ^ e) (pow_pos hp.pos e)] at h
  omega

lemma quarter_count_eq_divisorFunction {n : ℕ} (hn : 0 < n) :
    (quarterCount n : ℤ) = divisorFunction n := by
  have h := count_formula n hn
  rw [four_unit_count n hn] at h
  push_cast at h
  rw [← divisorFunction_apply] at h
  omega

theorem quarter_multiplicative : QuarterMultiplicative := by
  refine ⟨quarter_count_one, ?_⟩
  intro m n hm hn hmn
  apply Int.natCast_inj.mp
  rw [Nat.cast_mul, quarter_count_eq_divisorFunction (Nat.mul_pos hm hn),
    quarter_count_eq_divisorFunction hm, quarter_count_eq_divisorFunction hn]
  exact divisorFunction_multiplicative.map_mul_of_coprime hmn

end P203.Ch04.TwoSquaresCount
