import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.HalfPeriodValues
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.DivisorDegree
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.WeierstrassPeriods
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.WeierstrassEquations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! The branch values for the canonical regularized Weierstrass series.
The literal quotient group identifies exactly three nonzero points killed by 2.
Oddness gives zeros of ℘′ there. Its one triple pole and the effective-divisor
count force those three zeros to be simple and exhaustive. Subtracting a branch
value leaves one double pole; the corresponding zero has order two, so two
branch values cannot coincide. The differential equation and elementary
polynomial algebra give the factorization and nonzero discriminant. -/

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace D12Complex.Ch22.HalfPeriodValues
open TorusSurface
open Specs.D12Complex.Ch22.HalfPeriodValues (halfPeriod branchValue)
open WeierstrassSeries (periodPair)

private def hp (L : PeriodPair) : Fin 3 → ℂ := ![L.ω₁ / 2, L.ω₂ / 2, (L.ω₁ + L.ω₂) / 2]

lemma halfPeriod_notMem (L : PeriodPair) (i : Fin 3) : hp L i ∉ L.lattice := by
  fin_cases i
  · exact L.ω₁_div_two_notMem_lattice
  · exact L.ω₂_div_two_notMem_lattice
  · have h := (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 1 / 2)).not.mpr
      (by norm_num)
    convert h using 1 <;> simp [hp, add_div, inv_mul_eq_div]

lemma twice_halfPeriod_mem (L : PeriodPair) (i : Fin 3) : 2 * hp L i ∈ L.lattice := by
  fin_cases i <;> dsimp [hp]
  · convert L.ω₁_mem_lattice using 1 <;> ring
  · convert L.ω₂_mem_lattice using 1 <;> ring
  · convert add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice using 1 <;> ring

lemma halfPeriod_sub_notMem (L : PeriodPair) {i j : Fin 3} (hij : i ≠ j) :
    hp L i - hp L j ∉ L.lattice := by
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals
    dsimp [hp]
  · convert (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1/2) (β := -(1/2))).not.mpr (by norm_num) using 1 <;> push_cast <;> ring
  · convert (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := -(1/2))).not.mpr (by norm_num) using 1 <;> push_cast <;> ring
  · convert (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := -(1/2)) (β := 1/2)).not.mpr (by norm_num) using 1 <;> push_cast <;> ring
  · convert (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := -(1/2)) (β := 0)).not.mpr (by norm_num) using 1 <;> push_cast <;> ring
  · convert (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := 1/2)).not.mpr (by norm_num) using 1 <;> push_cast <;> ring
  · convert (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1/2) (β := 0)).not.mpr (by norm_num) using 1 <;> push_cast <;> ring

lemma halfPeriod_deriv_zero (L : PeriodPair) (i : Fin 3) :
    deriv L.weierstrassP (hp L i) = 0 := by
  rw [L.deriv_weierstrassP]
  have he : -hp L i + 2 * hp L i = hp L i := by ring
  have h := L.derivWeierstrassP_add_coe (-hp L i)
    ⟨2 * hp L i, twice_halfPeriod_mem L i⟩
  simp only [he, L.derivWeierstrassP_neg] at h
  exact (CharZero.eq_neg_self_iff).mp h

/-- A periodic meromorphic function with one pole class of order n has total
zero multiplicity n. No assumptions on finite fibre values are needed. -/
lemma zero_divisor {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {f : ℂ → ℂ} (hm : Meromorphic f) (hf : Periodic ω₁ ω₂ f) (n : ℕ)
    (hpole : ∀ a ∈ lattice ω₁ ω₂,
      meromorphicOrderAt f a = (-(n : ℤ) : WithTop ℤ))
    (ha : ∀ a ∉ lattice ω₁ ω₂, AnalyticAt ℂ f a) :
    ∃ Z : Torus ω₁ ω₂ →₀ ℕ,
      (∀ a, meromorphicOrderAt f a ≠ ⊤ ∧
        Z (projection ω₁ ω₂ a) = (meromorphicOrderAt f a).untop₀.toNat) ∧
      Z.sum (fun _ n => n) = n := by
  classical
  have hfin (a : ℂ) : meromorphicOrderAt f a ≠ ⊤ :=
    (hm.meromorphicOn (s := univ)).meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ 0) (mem_univ a)
      (by rw [hpole 0 (zero_mem _)]; simp)
  obtain ⟨Z, P, hZP, heq⟩ := DivisorDegree.effective_divisors h₁ h₂ hm hf hfin
  have hP : P = Finsupp.single 0 n := by
    ext q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q
    change P (projection ω₁ ω₂ a) = (Finsupp.single 0 n) (projection ω₁ ω₂ a)
    rw [(hZP a).2]
    by_cases haL : a ∈ lattice ω₁ ω₂
    · have hq : projection ω₁ ω₂ a = 0 := by
        simpa using (projection_eq_iff a 0).mpr (by simpa using haL)
      simp [hpole a haL, hq]
    · have hq : projection ω₁ ω₂ a ≠ 0 := by
        intro h; apply haL
        exact (by simpa using (projection_eq_iff a 0).mp (by simpa using h))
      have hnonneg := WithTop.untop₀_nonneg.mpr (ha a haL).meromorphicOrderAt_nonneg
      simp [Finsupp.single_eq_of_ne hq, Int.toNat_of_nonpos (neg_nonpos.mpr hnonneg)]
  exact ⟨Z, fun a => ⟨hfin a, (hZP a).1⟩, by simpa [hP] using heq⟩

lemma analytic_zero_iff_order_pos {f : ℂ → ℂ} {a : ℂ} (ha : AnalyticAt ℂ f a) :
    f a = 0 ↔ 0 < meromorphicOrderAt f a := by
  rw [← tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt]
  exact ⟨fun h => h ▸ ha.continuousAt.continuousWithinAt.tendsto,
    fun h => (tendsto_nhds_unique ha.continuousAt.continuousWithinAt.tendsto h)⟩

lemma nat_order_pos {o : WithTop ℤ} (ho : o ≠ ⊤) :
    0 < o.untop₀.toNat ↔ 0 < o := by
  obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp ho
  simp only [WithTop.untop₀_coe, WithTop.coe_pos]
  omega

lemma derivative_pole_order (L : PeriodPair) {a : ℂ} (ha : a ∈ L.lattice) :
    meromorphicOrderAt (deriv L.weierstrassP) a = (-3 : ℤ) := by
  simpa using meromorphicOrderAt_deriv_eq_sub_one (f := L.weierstrassP)
    (n := -2) (by norm_num) (L.order_weierstrassP a ha)

lemma projection_zero_iff {ω₁ ω₂ : ℂ} (a : ℂ) :
    projection ω₁ ω₂ a = 0 ↔ a ∈ lattice ω₁ ω₂ := by
  simpa using (projection_eq_iff (ω₁ := ω₁) (ω₂ := ω₂) a 0)

lemma halfPeriod_classes_injective {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) :
    Function.Injective (fun i => projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)) := by
  intro i j he
  by_contra hij
  exact halfPeriod_sub_notMem (periodPair h₁ h₂) hij ((projection_eq_iff _ _).mp he)

theorem classes : Specs.D12Complex.Ch22.HalfPeriodValues.classes_type := by
  intro ω₁ ω₂ h₁ h₂
  let L := periodPair h₁ h₂
  have hnot (i) : halfPeriod ω₁ ω₂ i ∉ lattice ω₁ ω₂ := halfPeriod_notMem L i
  refine ⟨halfPeriod_classes_injective h₁ h₂, hnot, fun q => ?_⟩
  constructor
  · rintro ⟨hq0, hq2⟩
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q
    change projection ω₁ ω₂ z ≠ 0 at hq0
    change (2 : ℕ) • projection ω₁ ω₂ z = 0 at hq2
    change ∃ i, projection ω₁ ω₂ z = projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)
    have hzL : 2 * z ∈ lattice ω₁ ω₂ := (projection_zero_iff _).mp (by
      simpa only [two_mul, map_add, two_nsmul] using hq2)
    obtain ⟨m, n, he⟩ := L.mem_lattice.mp hzL
    have hm : (m : ℂ) = 2 * ((m / 2 : ℤ) : ℂ) + ((m % 2 : ℤ) : ℂ) := by
      have h : m = 2 * (m / 2) + m % 2 := by omega
      exact_mod_cast h
    have hn : (n : ℂ) = 2 * ((n / 2 : ℤ) : ℂ) + ((n % 2 : ℤ) : ℂ) := by
      have h : n = 2 * (n / 2) + n % 2 := by omega
      exact_mod_cast h
    have hr : projection ω₁ ω₂ z = projection ω₁ ω₂
        (((m % 2 : ℤ) : ℂ) * ω₁ / 2 + ((n % 2 : ℤ) : ℂ) * ω₂ / 2) := by
      apply (projection_eq_iff _ _).mpr
      have hl : ((m / 2 : ℤ) : ℂ) * ω₁ + ((n / 2 : ℤ) : ℂ) * ω₂ ∈ L.lattice :=
        L.mem_lattice.mpr ⟨m / 2, n / 2, rfl⟩
      have heq : z - (((m % 2 : ℤ) : ℂ) * ω₁ / 2 + ((n % 2 : ℤ) : ℂ) * ω₂ / 2) =
          ((m / 2 : ℤ) : ℂ) * ω₁ + ((n / 2 : ℤ) : ℂ) * ω₂ := by
        change (m : ℂ) * ω₁ + (n : ℂ) * ω₂ = 2 * z at he
        linear_combination -he / 2 + hm * ω₁ / 2 + hn * ω₂ / 2
      rw [heq]
      exact hl
    have hm0 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    have hn0 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hm0 with hm0 | hm0 <;> rcases hn0 with hn0 | hn0
    · simp [hm0, hn0] at hr
      exact (hq0 hr).elim
    · exact ⟨1, by simpa [halfPeriod, hm0, hn0] using hr⟩
    · exact ⟨0, by simpa [halfPeriod, hm0, hn0] using hr⟩
    · exact ⟨2, by simpa [halfPeriod, hm0, hn0, add_div] using hr⟩
  · rintro ⟨i, rfl⟩
    refine ⟨fun he => hnot i ((projection_zero_iff _).mp he), ?_⟩
    have hzL : 2 * halfPeriod ω₁ ω₂ i ∈ lattice ω₁ ω₂ := twice_halfPeriod_mem L i
    have he := (projection_zero_iff _).mpr hzL
    simpa only [two_mul, map_add, two_nsmul] using he

/-- The sum over any finite subset is bounded by the total effective degree. -/
lemma finite_sum_le {A : Type*} (Z : A →₀ ℕ) (s : Finset A) :
    ∑ q ∈ s, Z q ≤ Z.sum (fun _ n => n) := by
  classical
  have he := Z.sum_of_support_subset (s := s ∪ Z.support)
    Finset.subset_union_right (fun _ n => n) (by simp)
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by intros; omega)

lemma order_eq_of_nat {o : WithTop ℤ} (ho : o ≠ ⊤) (hpos : 0 ≤ o) {n : ℕ}
    (hn : o.untop₀.toNat = n) : o = (n : ℤ) := by
  have hnonneg := WithTop.untop₀_nonneg.mpr hpos
  have hi : o.untop₀ = (n : ℤ) := by omega
  rw [← WithTop.coe_untop₀_of_ne_top ho, hi]

/-- The three exhibited zeros use up the total degree three. -/
lemma derivative_data {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    (∀ i, meromorphicOrderAt (deriv (WeierstrassSeries.weierstrassP ω₁ ω₂))
      (halfPeriod ω₁ ω₂ i) = 1) ∧
    (∀ z ∉ lattice ω₁ ω₂, deriv (WeierstrassSeries.weierstrassP ω₁ ω₂) z = 0 ↔
      ∃ i, projection ω₁ ω₂ z = projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)) := by
  classical
  let L := periodPair h₁ h₂
  have hper : Periodic ω₁ ω₂ (deriv L.weierstrassP) := by
    intro z l hl
    rw [L.deriv_weierstrassP]
    exact L.derivWeierstrassP_add_coe z ⟨l, hl⟩
  obtain ⟨Z, hZ, htotal⟩ := zero_divisor h₁ h₂ L.meromorphic_weierstrassP.deriv hper 3
    (fun a ha => derivative_pole_order L ha)
    (fun a ha => (L.analyticOnNhd_weierstrassP a ha).deriv)
  let q : Fin 3 → Torus ω₁ ω₂ := fun i => projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)
  have hinj : Function.Injective q := halfPeriod_classes_injective h₁ h₂
  have hpos (i : Fin 3) : 0 < Z (q i) := by
    rw [(hZ _).2]
    apply (nat_order_pos (hZ _).1).mpr
    exact (analytic_zero_iff_order_pos
      (L.analyticOnNhd_weierstrassP _ (halfPeriod_notMem L i)).deriv).mp
      (halfPeriod_deriv_zero L i)
  let s : Finset (Torus ω₁ ω₂) := Finset.univ.image q
  have hsum : Z (q 0) + Z (q 1) + Z (q 2) ≤ 3 := by
    have h := finite_sum_le Z s
    rw [htotal, Finset.sum_image (fun i _ j _ he => hinj he), Fin.sum_univ_three] at h
    exact h
  have hone (i : Fin 3) : Z (q i) = 1 := by
    have h0 := hpos 0
    have h1 := hpos 1
    have h2 := hpos 2
    have he0 : Z (q 0) = 1 := by omega
    have he1 : Z (q 1) = 1 := by omega
    have he2 : Z (q 2) = 1 := by omega
    fin_cases i
    · exact he0
    · exact he1
    · exact he2
  have hsupport (a : Torus ω₁ ω₂) : Z a ≠ 0 ↔ ∃ i, a = q i := by
    constructor
    · intro ha
      by_contra hnone
      have hnot : a ∉ s := by
        intro has
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp has
        exact hnone ⟨i, hi.symm⟩
      have h := finite_sum_le Z (insert a s)
      rw [htotal, Finset.sum_insert hnot, Finset.sum_image (fun i _ j _ he => hinj he),
        Fin.sum_univ_three, hone 0, hone 1, hone 2] at h
      omega
    · rintro ⟨i, rfl⟩
      exact ne_of_gt (hpos i)
  constructor
  · intro i
    apply order_eq_of_nat (hZ _).1
      (L.analyticOnNhd_weierstrassP _ (halfPeriod_notMem L i)).deriv.meromorphicOrderAt_nonneg
    exact (hZ _).2.symm.trans (hone i)
  · intro z hz
    change deriv L.weierstrassP z = 0 ↔ ∃ i, projection ω₁ ω₂ z = q i
    rw [analytic_zero_iff_order_pos (L.analyticOnNhd_weierstrassP z hz).deriv,
      ← nat_order_pos (hZ z).1, ← (hZ z).2, Nat.pos_iff_ne_zero]
    exact hsupport _

theorem simple_zeros : Specs.D12Complex.Ch22.HalfPeriodValues.simple_zeros_type := by
  intro ω₁ ω₂ h₁ h₂
  exact (derivative_data h₁ h₂).1

theorem zeros : Specs.D12Complex.Ch22.HalfPeriodValues.zeros_type := by
  intro ω₁ ω₂ h₁ h₂
  exact (derivative_data h₁ h₂).2

lemma analytic_order_of_meromorphic {f : ℂ → ℂ} {a : ℂ} (ha : AnalyticAt ℂ f a)
    {n : ℕ} (hn : meromorphicOrderAt f a = (n : ℤ)) : analyticOrderAt f a = n := by
  have he := ha.meromorphicOrderAt_eq
  rw [hn] at he
  cases ho : analyticOrderAt f a with
  | top => simp [ho] at he
  | coe k =>
    have hk : n = k := by exact_mod_cast (show (n : ℤ) = k from by simpa [ho] using he)
    simpa [hk] using ho

theorem all_simple_zeros : Specs.D12Complex.Ch22.HalfPeriodValues.all_simple_zeros_type := by
  intro ω₁ ω₂ h₁ h₂ z hz hd
  obtain ⟨i, hi⟩ := (zeros ω₁ ω₂ h₁ h₂ z hz).mp hd
  let L := periodPair h₁ h₂
  have hper : Periodic ω₁ ω₂ (deriv L.weierstrassP) := by
    intro a l hl
    rw [L.deriv_weierstrassP]
    exact L.derivWeierstrassP_add_coe a ⟨l, hl⟩
  have he := EllipticResidueSum.order_translation hper
    (halfPeriod ω₁ ω₂ i) (z - halfPeriod ω₁ ω₂ i) ((projection_eq_iff _ _).mp hi)
  rw [add_sub_cancel] at he
  exact he.trans (simple_zeros ω₁ ω₂ h₁ h₂ i)

theorem double_zeros : Specs.D12Complex.Ch22.HalfPeriodValues.double_zeros_type := by
  intro ω₁ ω₂ h₁ h₂ i
  let L := periodPair h₁ h₂
  have ha := L.analyticOnNhd_weierstrassP _ (halfPeriod_notMem L i)
  have hd : analyticOrderAt (deriv L.weierstrassP) (hp L i) = 1 :=
    analytic_order_of_meromorphic ha.deriv (n := 1) (simple_zeros ω₁ ω₂ h₁ h₂ i)
  have hshift := ha.analyticOrderAt_deriv_add_one
  rw [hd] at hshift
  change meromorphicOrderAt (fun z => L.weierstrassP z - L.weierstrassP (hp L i)) (hp L i) = 2
  have haSub : AnalyticAt ℂ (fun z => L.weierstrassP z - L.weierstrassP (hp L i)) (hp L i) :=
    ha.sub analyticAt_const
  rw [haSub.meromorphicOrderAt_eq, ← hshift]
  norm_num

theorem second_derivative : Specs.D12Complex.Ch22.HalfPeriodValues.second_derivative_type := by
  intro ω₁ ω₂ h₁ h₂ i
  let L := periodPair h₁ h₂
  have ha := (L.analyticOnNhd_weierstrassP _ (halfPeriod_notMem L i)).deriv.deriv
  have hs : meromorphicOrderAt (deriv L.weierstrassP) (hp L i) = (1 : ℤ) :=
    simple_zeros ω₁ ω₂ h₁ h₂ i
  have ho : meromorphicOrderAt (deriv (deriv L.weierstrassP)) (hp L i) = 0 := by
    convert meromorphicOrderAt_deriv_eq_sub_one (f := deriv L.weierstrassP)
      (x := hp L i) (n := 1) (by norm_num) hs using 1
    norm_num
  intro hz
  have h := (analytic_zero_iff_order_pos ha).mp hz
  rw [ho] at h
  exact (lt_irrefl _ h).elim

/-- Subtracting a branch value preserves the one double pole class. -/
lemma shifted_divisor {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (c : ℂ) :
    ∃ Z : Torus ω₁ ω₂ →₀ ℕ,
      (∀ a, meromorphicOrderAt (fun z => WeierstrassSeries.weierstrassP ω₁ ω₂ z - c) a ≠ ⊤ ∧
        Z (projection ω₁ ω₂ a) =
          (meromorphicOrderAt (fun z => WeierstrassSeries.weierstrassP ω₁ ω₂ z - c) a).untop₀.toNat) ∧
      Z.sum (fun _ n => n) = 2 := by
  let L := periodPair h₁ h₂
  apply zero_divisor h₁ h₂ (fun a => (L.meromorphic_weierstrassP a).sub analyticAt_const.meromorphicAt)
    (f := fun z => L.weierstrassP z - c) ?_ 2 ?_ ?_
  · intro z l hl
    change L.weierstrassP (z + l) - c = L.weierstrassP z - c
    rw [L.weierstrassP_add_coe z ⟨l, hl⟩]
  · intro a ha
    rw [(DivisorDegree.pole_order_sub_const (L.meromorphic_weierstrassP a) c).2
      (by rw [L.order_weierstrassP a ha]; exact WithTop.coe_lt_coe.mpr (by norm_num)),
      L.order_weierstrassP a ha]
    norm_num
  · intro a ha
    exact (L.analyticOnNhd_weierstrassP a ha).sub analyticAt_const

theorem distinct_values : Specs.D12Complex.Ch22.HalfPeriodValues.distinct_values_type := by
  classical
  intro ω₁ ω₂ h₁ h₂ i j he
  by_contra hij
  let qi := projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)
  let qj := projection ω₁ ω₂ (halfPeriod ω₁ ω₂ j)
  have hq : qi ≠ qj := fun h => hij (halfPeriod_classes_injective h₁ h₂ h)
  obtain ⟨Z, hZ, ht⟩ := shifted_divisor h₁ h₂ (branchValue ω₁ ω₂ i)
  have hi : Z qi = 2 := by
    rw [(hZ _).2, double_zeros ω₁ ω₂ h₁ h₂ i]
    rfl
  have hj : Z qj = 2 := by
    rw [(hZ _).2, he, double_zeros ω₁ ω₂ h₁ h₂ j]
    rfl
  have h := finite_sum_le Z {qi, qj}
  rw [Finset.sum_pair hq, ht, hi, hj] at h
  norm_num at h

/-- Vieta's identities derived from three distinct roots; no root-existence
assumption or discriminant theorem is used. -/
lemma cubic_coefficients {a b c A B : ℂ}
    (ha : 4 * a ^ 3 - A * a - B = 0)
    (hb : 4 * b ^ 3 - A * b - B = 0)
    (hc : 4 * c ^ 3 - A * c - B = 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a + b + c = 0 ∧ A = -4 * (a*b + a*c + b*c) ∧ B = 4*a*b*c := by
  have hab' : 4 * (a^2 + a*b + b^2) - A = 0 := by
    apply (mul_eq_zero.mp (show (a-b) * (4 * (a^2 + a*b + b^2) - A) = 0 by
      linear_combination ha - hb)).resolve_left (sub_ne_zero.mpr hab)
  have hac' : 4 * (a^2 + a*c + c^2) - A = 0 := by
    apply (mul_eq_zero.mp (show (a-c) * (4 * (a^2 + a*c + c^2) - A) = 0 by
      linear_combination ha - hc)).resolve_left (sub_ne_zero.mpr hac)
  have hs : a + b + c = 0 := by
    apply (mul_eq_zero.mp (show (4 * (b-c)) * (a+b+c) = 0 by
      linear_combination hab' - hac')).resolve_left
        (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hbc))
  refine ⟨hs, ?_, ?_⟩
  · linear_combination -hab' + 4*(a+b)*hs
  · linear_combination -ha + a*hab' - 4*a*b*hs

lemma branch_roots {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (i : Fin 3) :
    4 * branchValue ω₁ ω₂ i ^ 3 - Specs.D12Complex.Ch22.WeierstrassEquations.g₂ ω₁ ω₂ * branchValue ω₁ ω₂ i -
      Specs.D12Complex.Ch22.WeierstrassEquations.g₃ ω₁ ω₂ = 0 := by
  have hd : deriv (WeierstrassSeries.weierstrassP ω₁ ω₂) (halfPeriod ω₁ ω₂ i) = 0 :=
    halfPeriod_deriv_zero (periodPair h₁ h₂) i
  have h := WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ (halfPeriod ω₁ ω₂ i)
    (halfPeriod_notMem (periodPair h₁ h₂) i)
  change deriv (WeierstrassSeries.weierstrassP ω₁ ω₂) (halfPeriod ω₁ ω₂ i)^2 =
    4 * branchValue ω₁ ω₂ i ^ 3 - Specs.D12Complex.Ch22.WeierstrassEquations.g₂ ω₁ ω₂ *
      branchValue ω₁ ω₂ i - Specs.D12Complex.Ch22.WeierstrassEquations.g₃ ω₁ ω₂ at h
  rw [hd] at h
  simpa using h.symm

lemma branch_coefficients {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    let e := branchValue ω₁ ω₂
    e 0 + e 1 + e 2 = 0 ∧
    Specs.D12Complex.Ch22.WeierstrassEquations.g₂ ω₁ ω₂ = -4 * (e 0 * e 1 + e 0 * e 2 + e 1 * e 2) ∧
    Specs.D12Complex.Ch22.WeierstrassEquations.g₃ ω₁ ω₂ = 4 * e 0 * e 1 * e 2 := by
  have hinj := distinct_values ω₁ ω₂ h₁ h₂
  exact cubic_coefficients (branch_roots h₁ h₂ 0) (branch_roots h₁ h₂ 1) (branch_roots h₁ h₂ 2)
    (hinj.ne (by decide : (0 : Fin 3) ≠ 1))
    (hinj.ne (by decide : (0 : Fin 3) ≠ 2))
    (hinj.ne (by decide : (1 : Fin 3) ≠ 2))

theorem factorization : Specs.D12Complex.Ch22.HalfPeriodValues.factorization_type := by
  intro ω₁ ω₂ h₁ h₂ X
  obtain ⟨hs, hA, hB⟩ := branch_coefficients h₁ h₂
  rw [Fin.prod_univ_three, hA, hB]
  linear_combination 4 * X^2 * hs

theorem discriminant : Specs.D12Complex.Ch22.HalfPeriodValues.discriminant_type := by
  intro ω₁ ω₂ h₁ h₂
  let e := branchValue ω₁ ω₂
  obtain ⟨hs, hA, hB⟩ := branch_coefficients h₁ h₂
  have hc : e 2 = - e 0 - e 1 := by linear_combination hs
  have hdisc : Specs.D12Complex.Ch22.WeierstrassEquations.g₂ ω₁ ω₂ ^ 3 - 27 * Specs.D12Complex.Ch22.WeierstrassEquations.g₃ ω₁ ω₂ ^ 2 =
      16 * (e 0 - e 1)^2 * (e 0 - e 2)^2 * (e 1 - e 2)^2 := by
    rw [hA, hB]
    change (-4 * (e 0 * e 1 + e 0 * e 2 + e 1 * e 2))^3 - 27 * (4 * e 0 * e 1 * e 2)^2 = _
    rw [hc]
    ring
  have hinj := distinct_values ω₁ ω₂ h₁ h₂
  rw [hdisc]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ (sub_ne_zero.mpr (hinj.ne (by decide : (0 : Fin 3) ≠ 1)))))
    (pow_ne_zero _ (sub_ne_zero.mpr (hinj.ne (by decide : (0 : Fin 3) ≠ 2)))))
    (pow_ne_zero _ (sub_ne_zero.mpr (hinj.ne (by decide : (1 : Fin 3) ≠ 2))))

end D12Complex.Ch22.HalfPeriodValues
