import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.Alternation
import MathGenome.Internal.FourierSobolev.P102.Approximation.BestExistence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Fin.Tuple
import Mathlib.Topology.Order.ProjIcc

noncomputable section

namespace P102.Approximation

/-- Restriction to a nondegenerate real interval is injective on polynomials. -/
theorem polynomial_eq_of_eqOn_interval {a b : ℝ} (hab : a < b)
    (p q : Polynomial ℝ) (h : ∀ x : Set.Icc a b, p.eval (x : ℝ) = q.eval (x : ℝ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  exact (Set.Icc_infinite hab).mono (fun x hx => h ⟨x, hx⟩)

theorem zeroError_unique : Specs.P102.Approximation.Alternation.ZeroErrorUnique := by
  intro a b hab f n p q hdegree hp hq
  have hpmap : f = p.toContinuousMapOn (Set.Icc a b) := sub_eq_zero.mp (norm_eq_zero.mp hp)
  have hqmap : f = q.toContinuousMapOn (Set.Icc a b) := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [hp] using hq.2 p hdegree) (norm_nonneg _)
  apply polynomial_eq_of_eqOn_interval hab p q
  intro x
  have hpval := congrArg (fun g : C(Set.Icc a b, ℝ) => g x) hpmap
  have hqval := congrArg (fun g : C(Set.Icc a b, ℝ) => g x) hqmap
  exact hpval.symm.trans hqval

/-- A degree-at-most-`n` polynomial cannot change strict sign across `n+1`
ordered, disjoint intervals. -/
theorem polynomial_not_alternating {n : ℕ} (r : Polynomial ℝ)
    (hr : r.degree ≤ (n : WithBot ℕ)) (x : Fin (n + 2) → ℝ)
    (hx : StrictMono x)
    (hs : ∀ i : Fin (n + 1), r.eval (x i.castSucc) * r.eval (x i.succ) < 0) : False := by
  have hroot : ∀ i : Fin (n + 1),
      ∃ z : ℝ, z ∈ Set.Ioo (x i.castSucc) (x i.succ) ∧ r.eval z = 0 := by
    intro i
    have hlt : x i.castSucc < x i.succ := hx (by simp)
    rcases mul_neg_iff.mp (hs i) with h | h
    · exact intermediate_value_Ioo' hlt.le r.continuous.continuousOn ⟨h.2, h.1⟩
    · exact intermediate_value_Ioo hlt.le r.continuous.continuousOn h
  choose z hz hzroot using hroot
  have hzmono : StrictMono z := by
    intro i j hij
    have hle : i.succ ≤ j.castSucc := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_of_lt hij
    exact (hz i).2.trans_le (hx.monotone hle) |>.trans (hz j).1
  have hzero : r = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    r hzmono.injective hzroot (by
      simpa only [Fintype.card_fin] using
        Nat.lt_succ_of_le (Polynomial.natDegree_le_of_degree_le hr))
  simpa [hzero] using hs (0 : Fin (n + 1))

/-- Alternating extremal errors prevent any strict improvement. -/
theorem alternation_sufficient :
    Specs.P102.Approximation.Alternation.AlternationSufficient := by
  intro a b _ f n p hp _ halt
  refine ⟨hp, fun q hq => ?_⟩
  by_contra hnot
  have hbetter : ‖f - q.toContinuousMapOn (Set.Icc a b)‖ <
      ‖f - p.toContinuousMapOn (Set.Icc a b)‖ := lt_of_not_ge hnot
  obtain ⟨x, hx, σ, hσ, hext⟩ := halt
  have hbound (i : Fin (n + 2)) :
      |f (x i) - q.eval (x i : ℝ)| < ‖f - p.toContinuousMapOn (Set.Icc a b)‖ := by
    have h := (f - q.toContinuousMapOn (Set.Icc a b)).norm_coe_le_norm (x i)
    have h' : |f (x i) - q.eval (x i : ℝ)| ≤
        ‖f - q.toContinuousMapOn (Set.Icc a b)‖ := by
      simpa only [ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
        Real.norm_eq_abs] using h
    exact h'.trans_lt hbetter
  have hsign (i : Fin (n + 2)) :
      0 < (σ * (-1 : ℝ) ^ (i : ℕ)) * (q - p).eval (x i : ℝ) := by
    have hb := abs_lt.mp (hbound i)
    have he := hext i
    rw [Polynomial.eval_sub]
    rcases hσ with rfl | rfl <;>
      rcases neg_one_pow_eq_or ℝ (i : ℕ) with hi | hi <;>
      simp only [hi] at he ⊢ <;> nlinarith
  apply polynomial_not_alternating (q - p) ((Polynomial.degree_sub_le q p).trans (max_le hq hp))
    (fun i => (x i : ℝ)) hx
  intro i
  have hi := hsign i.castSucc
  have hj := hsign i.succ
  have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hpow : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by
    rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;> simp [h]
  have hprod := mul_pos hi hj
  simp only [Fin.val_castSucc, Fin.val_succ, pow_succ] at hprod
  have hid : (σ * (-1 : ℝ) ^ (i : ℕ) * (q - p).eval (x i.castSucc : ℝ)) *
      (σ * ((-1 : ℝ) ^ (i : ℕ) * -1) * (q - p).eval (x i.succ : ℝ)) =
      -((q - p).eval (x i.castSucc : ℝ) * (q - p).eval (x i.succ : ℝ)) := by
    calc
      _ = -(σ * σ * ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) *
        ((q - p).eval (x i.castSucc : ℝ) * (q - p).eval (x i.succ : ℝ))) := by ring
      _ = _ := by rw [hσsq, hpow]; ring
  rw [hid] at hprod
  linarith

/-- The midpoint proof reduces uniqueness to the necessity half alone.
This helper makes no claim that necessity has already been proved. -/
theorem uniqueBest_of_necessity
    (hnecessity : ∀ (a b : ℝ), a < b → ∀ (f : C(Set.Icc a b, ℝ)) (n : ℕ)
      (p : Polynomial ℝ), IsBestPolynomial f n p →
      0 < ‖f - p.toContinuousMapOn (Set.Icc a b)‖ → HasAlternation f n p) :
    Specs.P102.Approximation.Alternation.UniqueBest := by
  intro a b hab f n
  obtain ⟨p, hp, _, hmin⟩ := bestPolynomial_exists a b hab f n
  refine ⟨p, ⟨hp, hmin⟩, ?_⟩
  intro q hq
  have heq : ‖f - q.toContinuousMapOn (Set.Icc a b)‖ =
      ‖f - p.toContinuousMapOn (Set.Icc a b)‖ :=
    le_antisymm (hq.2 p hp) (hmin q hq.1)
  by_cases hzero : ‖f - p.toContinuousMapOn (Set.Icc a b)‖ = 0
  · exact (zeroError_unique a b hab f n p q hp hzero hq).symm
  have hpos : 0 < ‖f - p.toContinuousMapOn (Set.Icc a b)‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  let r : Polynomial ℝ := (1 / 2 : ℝ) • (p + q)
  have hr : r.degree ≤ (n : WithBot ℕ) :=
    (Polynomial.degree_smul_le (1 / 2 : ℝ) (p + q)).trans
      ((Polynomial.degree_add_le p q).trans (max_le hp hq.1))
  have herr : f - r.toContinuousMapOn (Set.Icc a b) =
      (1 / 2 : ℝ) • ((f - p.toContinuousMapOn (Set.Icc a b)) +
        (f - q.toContinuousMapOn (Set.Icc a b))) := by
    ext x
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply,
      Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
      r, Polynomial.eval_smul, Polynomial.eval_add, smul_eq_mul]
    ring
  have hmidbound : ‖f - r.toContinuousMapOn (Set.Icc a b)‖ ≤
      ‖f - p.toContinuousMapOn (Set.Icc a b)‖ := by
    rw [herr, norm_smul]
    have htri := norm_add_le (f - p.toContinuousMapOn (Set.Icc a b))
      (f - q.toContinuousMapOn (Set.Icc a b))
    rw [heq] at htri
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hmidnorm : ‖f - r.toContinuousMapOn (Set.Icc a b)‖ =
      ‖f - p.toContinuousMapOn (Set.Icc a b)‖ :=
    le_antisymm hmidbound (hmin r hr)
  have hmidbest : IsBestPolynomial f n r :=
    ⟨hr, fun s hs => hmidbound.trans (hmin s hs)⟩
  obtain ⟨x, hx, σ, hσ, hext⟩ := hnecessity a b hab f n r hmidbest
    (by rw [hmidnorm]; exact hpos)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq q p hx.injective
  · intro i
    have hbp := (f - p.toContinuousMapOn (Set.Icc a b)).norm_coe_le_norm (x i)
    have hbq := (f - q.toContinuousMapOn (Set.Icc a b)).norm_coe_le_norm (x i)
    have he := hext i
    rw [hmidnorm] at he
    simp only [ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply, Real.norm_eq_abs] at hbp hbq
    rw [heq] at hbq
    obtain ⟨hpl, hpu⟩ := abs_le.mp hbp
    obtain ⟨hql, hqu⟩ := abs_le.mp hbq
    simp only [r, Polynomial.eval_smul, Polynomial.eval_add, smul_eq_mul] at he
    rcases hσ with rfl | rfl <;>
      rcases neg_one_pow_eq_or ℝ (i : ℕ) with hi | hi <;>
      simp only [hi] at he <;> nlinarith
  · simp only [Fintype.card_fin]
    have hp' := Polynomial.natDegree_le_of_degree_le hp
    have hq' := Polynomial.natDegree_le_of_degree_le hq.1
    exact lt_of_le_of_lt (max_le hq' hp') (Nat.lt_add_of_pos_right (by decide))

/-- A direction with the error's strict sign at every extreme point improves
that error for some positive step. Compactness supplies one step for all points. -/
theorem exists_improving_step {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g h : C(K, ℝ)) (hE : 0 < ‖g‖)
    (hsign : ∀ x, |g x| = ‖g‖ → 0 < g x * h x) :
    ∃ t : ℝ, 0 < t ∧ ‖g - t • h‖ < ‖g‖ := by
  classical
  have hpoint : ∀ x : K, ∃ t : ℝ, 0 < t ∧ |g x - t * h x| < ‖g‖ := by
    intro x
    have hbound : |g x| ≤ ‖g‖ := by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x
    by_cases hext : |g x| = ‖g‖
    · have hs := hsign x hext
      have hne : h x ≠ 0 := by intro hz; simp [hz] at hs
      refine ⟨g x / h x, ?_, ?_⟩
      · rcases mul_pos_iff.mp hs with hp | hn
        · exact div_pos hp.1 hp.2
        · exact div_pos_of_neg_of_neg hn.1 hn.2
      · simpa only [div_mul_cancel₀ _ hne, sub_self, abs_zero] using hE
    · have hslack : 0 < ‖g‖ - |g x| := sub_pos.mpr (lt_of_le_of_ne hbound hext)
      let t := (‖g‖ - |g x|) / (|h x| + 1)
      have hden : 0 < |h x| + 1 := by positivity
      have ht : 0 < t := div_pos hslack hden
      have hrel : t * (|h x| + 1) = ‖g‖ - |g x| :=
        div_mul_cancel₀ _ (ne_of_gt hden)
      refine ⟨t, ht, ?_⟩
      have htri := abs_sub (g x) (t * h x)
      rw [abs_mul, abs_of_pos ht] at htri
      nlinarith
  let U : {t : ℝ // 0 < t} → Set K := fun t => {x | |g x - (t : ℝ) * h x| < ‖g‖}
  have hopen : ∀ t, IsOpen (U t) := fun t =>
    isOpen_lt (g.continuous.sub (continuous_const.mul h.continuous)).abs continuous_const
  have hcover : Set.univ ⊆ ⋃ t, U t := by
    intro x _
    obtain ⟨t, ht, hx⟩ := hpoint x
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  have hlower : ∃ t : ℝ, 0 < t ∧ ∀ u ∈ s, t ≤ (u : ℝ) := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert u s hu ih =>
      obtain ⟨t, ht, hts⟩ := ih
      refine ⟨min (u : ℝ) t, lt_min u.property ht, ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hts v hv)
  obtain ⟨t, ht, hts⟩ := hlower
  refine ⟨t, ht, (ContinuousMap.norm_lt_iff _ hE).mpr ?_⟩
  intro x
  obtain ⟨u, hu, hux⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  have hsmall : |g x - (u : ℝ) * h x| < ‖g‖ := hux
  have hbound : |g x| ≤ ‖g‖ := by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x
  obtain ⟨hgl, hgu⟩ := abs_le.mp hbound
  obtain ⟨hul, huu⟩ := abs_lt.mp hsmall
  have htu := hts u hu
  have hfinal : |g x - t * h x| < ‖g‖ := by
    apply abs_lt.mpr
    rcases lt_trichotomy (h x) 0 with hh | hh | hh
    · constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr htu) (le_of_lt (neg_pos.mpr hh))]
    · simp only [hh, mul_zero, sub_zero] at hul huu ⊢
      exact ⟨hul, huu⟩
    · constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr htu) (le_of_lt hh)]
  simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
    Real.norm_eq_abs] using hfinal

/-- An oriented alternating chain, beginning in the first set. -/
def StartsAlternating (A B : Set ℝ) (k : ℕ) : Prop :=
  ∃ x : Fin k → ℝ, StrictMono x ∧
    ∀ i : Fin k, if Even (i : ℕ) then x i ∈ A else x i ∈ B

theorem startsAlternating_prepend {A B : Set ℝ} {k : ℕ} {l : ℝ}
    (hl : l ∈ A) (x : Fin k → ℝ) (hx : StrictMono x) (hlt : ∀ i, l < x i)
    (hmem : ∀ i : Fin k, if Even (i : ℕ) then x i ∈ B else x i ∈ A) :
    StartsAlternating A B (k + 1) := by
  refine ⟨Fin.cons l x, Fin.strictMono_cons.mpr ⟨hlt, hx⟩, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hl
  · have hm := hmem j
    by_cases he : Even (j : ℕ) <;>
      simpa [Fin.val_succ, Nat.even_add_one, he] using hm

/-- With its leftmost point in `A`, a pair of disjoint compact signed sets
with no `n+2` point alternation admits a degree-at-most-`n` separator.
The extra left-half-line sign invariant permits induction. -/
theorem compact_sign_separator_left (n : ℕ) (A B : Set ℝ)
    (hA : IsCompact A) (hB : IsCompact B) (hd : Disjoint A B)
    (l : ℝ) (hl : l ∈ A) (hleft : ∀ x ∈ A ∪ B, l ≤ x)
    (halt : ¬StartsAlternating A B (n + 2)) :
    ∃ q : Polynomial ℝ, q.degree ≤ (n : WithBot ℕ) ∧
      (∀ x ∈ A, 0 < q.eval x) ∧ (∀ x ∈ B, q.eval x < 0) ∧
      ∀ x ≤ l, 0 < q.eval x := by
  induction n generalizing A B l with
  | zero =>
    have hBempty : B = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hlv : l < v := lt_of_le_of_ne (hleft v (Or.inr hv)) (by
        intro heq
        exact Set.disjoint_left.mp hd hl (heq ▸ hv))
      apply halt
      apply startsAlternating_prepend hl (fun _ : Fin 1 => v)
      · intro i j hij
        exact False.elim (by have hi := i.isLt; have hj := j.isLt; omega)
      · intro _; exact hlv
      · intro i
        have hi : i = 0 := Fin.eq_zero i
        simp [hi, hv]
    refine ⟨1, by simp, ?_, ?_, ?_⟩
    · intro x _; simp
    · simp [hBempty]
    · intro x _; simp
  | succ n ih =>
    by_cases hBempty : B = ∅
    · refine ⟨1, ?_, ?_, ?_, ?_⟩
      · simp only [Polynomial.degree_one]
        exact WithBot.coe_le_coe.mpr (Nat.zero_le _)
      · intro x _; simp
      · simp [hBempty]
      · intro x _; simp
    have hBne : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hBempty
    obtain ⟨v, hv, hvmin⟩ := hB.exists_isMinOn hBne continuous_id.continuousOn
    have hlv : l < v := lt_of_le_of_ne (hleft v (Or.inr hv)) (by
      intro heq
      exact Set.disjoint_left.mp hd hl (heq ▸ hv))
    have hcut : IsCompact (A ∩ Set.Iic v) := hA.inter_right isClosed_Iic
    obtain ⟨w, hw, hwmax⟩ := hcut.exists_isMaxOn ⟨l, hl, hlv.le⟩ continuous_id.continuousOn
    have hwv : w < v := lt_of_le_of_ne hw.2 (by
      intro heq
      exact Set.disjoint_left.mp hd hw.1 (heq ▸ hv))
    obtain ⟨c, hwc, hcv⟩ := exists_between hwv
    have hlw : l ≤ w := hwmax ⟨hl, hlv.le⟩
    have htail : ¬StartsAlternating B (A ∩ Set.Ici v) (n + 2) := by
      rintro ⟨x, hx, hmem⟩
      apply halt
      apply startsAlternating_prepend hl x hx
      · intro i
        have hm := hmem i
        by_cases he : Even (i : ℕ)
        · simp only [he, ↓reduceIte] at hm
          exact hlv.trans_le (hvmin hm)
        · simp only [he, ↓reduceIte] at hm
          exact hlv.trans_le hm.2
      · intro i
        have hm := hmem i
        by_cases he : Even (i : ℕ)
        · simpa [he] using hm
        · simp only [he, ↓reduceIte] at hm
          simpa [he] using hm.1
    obtain ⟨q, hq, hqB, hqA, hqleft⟩ := ih B (A ∩ Set.Ici v) hB
      (hA.inter_right isClosed_Ici) (hd.symm.mono_right Set.inter_subset_left) v hv
      (by intro x hx; rcases hx with hx | hx; exact hvmin hx; exact hx.2) htail
    refine ⟨(Polynomial.C c - Polynomial.X) * q, ?_, ?_, ?_, ?_⟩
    · apply Polynomial.degree_le_of_natDegree_le
      have hfactor : (Polynomial.C c - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
        (Polynomial.natDegree_sub_le _ _).trans (by simp)
      exact Polynomial.natDegree_mul_le.trans
        ((Nat.add_le_add hfactor (Polynomial.natDegree_le_of_degree_le hq)).trans_eq
          (Nat.add_comm 1 n))
    · intro x hx
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      by_cases hxv : x < v
      · have hxc : x < c := (hwmax ⟨hx, hxv.le⟩).trans_lt hwc
        exact mul_pos (sub_pos.mpr hxc) (hqleft x hxv.le)
      · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hcv.trans_le (le_of_not_gt hxv)))
          (hqA x ⟨hx, le_of_not_gt hxv⟩)
    · intro x hx
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr (hcv.trans_le (hvmin hx))) (hqB x hx)
    · intro x hx
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      exact mul_pos (sub_pos.mpr (hx.trans hlw |>.trans_lt hwc)) (hqleft x (hx.trans hlv.le))

/-- The unoriented form of compact sign separation. -/
theorem compact_sign_separator (n : ℕ) (A B : Set ℝ)
    (hA : IsCompact A) (hB : IsCompact B) (hd : Disjoint A B)
    (hne : (A ∪ B).Nonempty)
    (hnoA : ¬StartsAlternating A B (n + 2))
    (hnoB : ¬StartsAlternating B A (n + 2)) :
    ∃ q : Polynomial ℝ, q.degree ≤ (n : WithBot ℕ) ∧
      (∀ x ∈ A, 0 < q.eval x) ∧ (∀ x ∈ B, q.eval x < 0) := by
  obtain ⟨l, hl, hmin⟩ := (hA.union hB).exists_isMinOn hne continuous_id.continuousOn
  rcases hl with hl | hl
  · obtain ⟨q, hq, hpos, hneg, _⟩ :=
      compact_sign_separator_left n A B hA hB hd l hl hmin hnoA
    exact ⟨q, hq, hpos, hneg⟩
  · obtain ⟨q, hq, hpos, hneg, _⟩ :=
      compact_sign_separator_left n B A hB hA hd.symm l hl
        (by intro x hx; exact hmin (by simpa only [Set.union_comm] using hx)) hnoB
    refine ⟨-q, by simpa only [Polynomial.degree_neg] using hq, ?_, ?_⟩
    · intro x hx; simpa only [Polynomial.eval_neg, neg_pos] using hneg x hx
    · intro x hx; simpa only [Polynomial.eval_neg, neg_neg_iff_pos] using hpos x hx

/-- Necessity: failure of alternation supplies a sign-matching polynomial,
which gives a strictly smaller error after a sufficiently small positive step. -/
theorem alternation_necessary
    (a b : ℝ) (hab : a < b) (f : C(Set.Icc a b, ℝ)) (n : ℕ)
    (p : Polynomial ℝ) (hbest : IsBestPolynomial f n p)
    (hE : 0 < ‖f - p.toContinuousMapOn (Set.Icc a b)‖) :
    HasAlternation f n p := by
  classical
  by_contra hnot
  let g := f - p.toContinuousMapOn (Set.Icc a b)
  let E := ‖g‖
  let G : ℝ → ℝ := fun x => g (Set.projIcc a b hab.le x)
  have hG : Continuous G := g.continuous.comp (continuous_projIcc (a := a) (b := b) (h := hab.le))
  let S : ℝ → Set ℝ := fun σ => Set.Icc a b ∩ {x | G x = σ * E}
  have hcompact (σ : ℝ) : IsCompact (S σ) :=
    isCompact_Icc.inter_right (isClosed_eq hG continuous_const)
  have hchain (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) :
      ¬StartsAlternating (S σ) (S (-σ)) (n + 2) := by
    rintro ⟨x, hx, hmem⟩
    have hxI (i : Fin (n + 2)) : x i ∈ Set.Icc a b := by
      have hm := hmem i
      by_cases he : Even (i : ℕ) <;> simp only [he, ↓reduceIte] at hm <;> exact hm.1
    let xs : Fin (n + 2) → Set.Icc a b := fun i => ⟨x i, hxI i⟩
    apply hnot
    refine ⟨xs, hx, σ, hσ, ?_⟩
    intro i
    change g (xs i) = σ * (-1 : ℝ) ^ (i : ℕ) * E
    have hgx : G (x i) = g (xs i) := by
      dsimp only [G, xs]
      rw [Set.projIcc_of_mem]
    have hm := hmem i
    rw [← hgx, neg_one_pow_eq_ite]
    by_cases he : Even (i : ℕ)
    · simp only [he, ↓reduceIte, mul_one] at hm ⊢
      exact hm.2
    · simp only [he, ↓reduceIte] at hm ⊢
      rw [hm.2]
      ring
  have hdisjoint : Disjoint (S 1) (S (-1)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' := hx.2
    have hy' := hy.2
    change G x = 1 * E at hx'
    change G x = -1 * E at hy'
    have : 0 < E := hE
    nlinarith
  have hnonempty : (S 1 ∪ S (-1)).Nonempty := by
    obtain ⟨x, hx, _⟩ := uniformNorm_attained a b hab g
    rcases (abs_eq (norm_nonneg g)).mp hx with hx | hx
    · refine ⟨x, Or.inl ⟨x.property, ?_⟩⟩
      simpa only [Set.mem_ofPred_eq, G, Set.projIcc_val, one_mul, E] using hx
    · refine ⟨x, Or.inr ⟨x.property, ?_⟩⟩
      simpa only [Set.mem_ofPred_eq, G, Set.projIcc_val, neg_one_mul, E] using hx
  obtain ⟨q, hq, hpos, hneg⟩ := compact_sign_separator n (S 1) (S (-1))
    (hcompact 1) (hcompact (-1)) hdisjoint hnonempty
    (by simpa only [neg_one_mul] using hchain 1 (Or.inr rfl))
    (by simpa only [neg_neg] using hchain (-1) (Or.inl rfl))
  have hsign : ∀ x : Set.Icc a b, |g x| = ‖g‖ →
      0 < g x * q.toContinuousMapOn (Set.Icc a b) x := by
    intro x hx
    change 0 < g x * q.eval (x : ℝ)
    rcases (abs_eq (norm_nonneg g)).mp hx with hx | hx
    · have hqx := hpos (x : ℝ) ⟨x.property, by
        simpa only [Set.mem_ofPred_eq, G, Set.projIcc_val, one_mul, E] using hx⟩
      rw [hx]
      exact mul_pos hE hqx
    · have hqx := hneg (x : ℝ) ⟨x.property, by
        simpa only [Set.mem_ofPred_eq, G, Set.projIcc_val, neg_one_mul, E] using hx⟩
      rw [hx]
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos hE) hqx
  obtain ⟨t, _, himprove⟩ := exists_improving_step g
    (q.toContinuousMapOn (Set.Icc a b)) hE hsign
  have hdegree : (p + t • q).degree ≤ (n : WithBot ℕ) :=
    (Polynomial.degree_add_le _ _).trans (max_le hbest.1
      ((Polynomial.degree_smul_le t q).trans hq))
  have herr : f - (p + t • q).toContinuousMapOn (Set.Icc a b) =
      g - t • q.toContinuousMapOn (Set.Icc a b) := by
    ext x
    simp only [g, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
      Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
    ring
  have hmin := hbest.2 (p + t • q) hdegree
  rw [herr] at hmin
  exact (not_lt_of_ge hmin) himprove

theorem alternation_iff : Specs.P102.Approximation.Alternation.AlternationIff := by
  intro a b hab f n p hp hE
  exact ⟨fun h => alternation_necessary a b hab f n p h hE,
    alternation_sufficient a b hab f n p hp hE⟩

theorem uniqueBestPolynomial : Specs.P102.Approximation.Alternation.UniqueBest :=
  uniqueBest_of_necessity alternation_necessary

end P102.Approximation
