import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.BoxAlgebra
import MathGenome.Internal.MultivariableAnalysis.D04.C06.DarbouxIntegral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Set
open scoped BigOperators
namespace D04.Darboux
variable {n : ℕ} {Q : Box n} {f g : E n → ℝ}

/-- An absolute bound is equivalent to the two finite bounds used in the definition. -/
theorem bounded_of_abs_le {h : E n → ℝ} {M : ℝ}
    (hM : ∀ x ∈ carrier Q, |h x| ≤ M) : Bounded h Q := by
  constructor
  · refine ⟨-M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x hx)).1
  · refine ⟨M, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x hx)).2

theorem exists_abs_bound (hf : Bounded f Q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ carrier Q, |f x| ≤ M := by
  obtain ⟨l, hl⟩ := hf.1
  obtain ⟨u, hu⟩ := hf.2
  refine ⟨|l| + |u|, add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro x hx
  have hxl := hl ⟨x, hx, rfl⟩
  have hxu := hu ⟨x, hx, rfl⟩
  exact abs_le.mpr ⟨by linarith [neg_abs_le l, abs_nonneg u],
    by linarith [le_abs_self u, abs_nonneg l]⟩

theorem bounded_const (Q : Box n) (a : ℝ) : Bounded (fun _ => a) Q :=
  bounded_of_abs_le (fun _ _ => le_rfl)

theorem bounded_add (hf : Bounded f Q) (hg : Bounded g Q) :
    Bounded (fun x => f x + g x) Q := by
  obtain ⟨M, _, hM⟩ := exists_abs_bound hf
  obtain ⟨N, _, hN⟩ := exists_abs_bound hg
  exact bounded_of_abs_le (M := M + N) fun x hx =>
    (abs_add_le _ _).trans (add_le_add (hM x hx) (hN x hx))

theorem bounded_smul (a : ℝ) (hf : Bounded f Q) :
    Bounded (fun x => a * f x) Q := by
  obtain ⟨M, _, hM⟩ := exists_abs_bound hf
  apply bounded_of_abs_le (M := |a| * M)
  intro x hx
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg a)

theorem bounded_mul (hf : Bounded f Q) (hg : Bounded g Q) :
    Bounded (fun x => f x * g x) Q := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hf
  obtain ⟨N, _, hN⟩ := exists_abs_bound hg
  apply bounded_of_abs_le (M := M * N)
  intro x hx
  rw [abs_mul]
  exact mul_le_mul (hM x hx) (hN x hx) (abs_nonneg _) hM0

theorem bounded_abs (hf : Bounded f Q) : Bounded (fun x => |f x|) Q := by
  obtain ⟨M, _, hM⟩ := exists_abs_bound hf
  exact bounded_of_abs_le (M := M) fun x hx => by simpa using hM x hx

/-- Pairwise differences control a cell's Darboux oscillation, without requiring
that either extremum be attained. -/
theorem cell_oscillation_le {h : E n → ℝ} (P : Grid Q) (c : CellIndex P)
    {D : ℝ} (hd : ∀ x ∈ cell P c, ∀ y ∈ cell P c, h x - h y ≤ D) :
    cellSupremum h P c - cellInfimum h P c ≤ D := by
  apply sub_le_iff_le_add.mpr
  apply csSup_le ((cell_nonempty P c).image h)
  rintro _ ⟨x, hx, rfl⟩
  have hi : h x - D ≤ cellInfimum h P c := by
    apply le_csInf ((cell_nonempty P c).image h)
    rintro _ ⟨y, hy, rfl⟩
    linarith [hd x hx y hy]
  linarith

theorem abs_sub_le_cell_oscillation (hf : Bounded f Q) (P : Grid Q)
    (c : CellIndex P) {x y : E n} (hx : x ∈ cell P c) (hy : y ∈ cell P c) :
    |f x - f y| ≤ cellSupremum f P c - cellInfimum f P c := by
  have hxl := cellInfimum_le f hf P c hx
  have hxu := le_cellSupremum f hf P c hx
  have hyl := cellInfimum_le f hf P c hy
  have hyu := le_cellSupremum f hf P c hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A common refinement makes two integrable oscillations simultaneously small. -/
theorem integrable_of_oscillation_bound {h : E n → ℝ}
    (hf : Integrable f Q) (hg : Integrable g Q) (hh : Bounded h Q)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcell : ∀ (P : Grid Q) (c : CellIndex P),
      cellSupremum h P c - cellInfimum h P c ≤
        A * (cellSupremum f P c - cellInfimum f P c) +
        B * (cellSupremum g P c - cellInfimum g P c)) : Integrable h Q := by
  apply (integrable_iff_gap h Q hh).mpr
  intro ε hε
  let η := ε / (A + B + 1)
  have hd : 0 < A + B + 1 := by linarith
  have hη : 0 < η := div_pos hε hd
  have heq : η * (A + B + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hd)
  obtain ⟨P, hP⟩ := (integrable_iff_gap f Q hf.1).mp hf η hη
  obtain ⟨R, hR⟩ := (integrable_iff_gap g Q hg.1).mp hg η hη
  obtain ⟨T, hTP, hTR⟩ := common_refinement P R
  have hfT : upperSum f T - lowerSum f T < η := by
    have hu := upper_refinement f hf.1 P T hTP
    have hl := lower_refinement f hf.1 P T hTP
    linarith
  have hgT : upperSum g T - lowerSum g T < η := by
    have hu := upper_refinement g hg.1 R T hTR
    have hl := lower_refinement g hg.1 R T hTR
    linarith
  have hs : upperSum h T - lowerSum h T ≤
      A * (upperSum f T - lowerSum f T) +
      B * (upperSum g T - lowerSum g T) := by
    change (∑ c, cellSupremum h T c * cellContent T c) -
      (∑ c, cellInfimum h T c * cellContent T c) ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ c, (A * (cellSupremum f T c - cellInfimum f T c) +
          B * (cellSupremum g T c - cellInfimum g T c)) * cellContent T c := by
        apply Finset.sum_le_sum
        intro c _
        rw [← sub_mul]
        exact mul_le_mul_of_nonneg_right (hcell T c) (cellContent_nonneg T c)
      _ = _ := by
        simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
          sub_mul, Finset.sum_sub_distrib]
        rfl
  have hAf := mul_le_mul_of_nonneg_left hfT.le hA
  have hBg := mul_le_mul_of_nonneg_left hgT.le hB
  exact ⟨T, by nlinarith⟩

theorem integrable_add (hf : Integrable f Q) (hg : Integrable g Q) :
    Integrable (fun x => f x + g x) Q := by
  apply integrable_of_oscillation_bound hf hg (bounded_add hf.1 hg.1)
    (A := 1) (B := 1) (by norm_num) (by norm_num)
  intro P c
  apply cell_oscillation_le
  intro x hx y hy
  have h1 := abs_sub_le_cell_oscillation hf.1 P c hx hy
  have h2 := abs_sub_le_cell_oscillation hg.1 P c hx hy
  linarith [le_abs_self (f x - f y), le_abs_self (g x - g y)]

theorem integrable_smul (a : ℝ) (hf : Integrable f Q) :
    Integrable (fun x => a * f x) Q := by
  apply integrable_of_oscillation_bound hf hf (bounded_smul a hf.1)
    (A := |a|) (B := 0) (abs_nonneg _) le_rfl
  intro P c
  apply cell_oscillation_le
  intro x hx y hy
  have hm := mul_le_mul_of_nonneg_left
    (abs_sub_le_cell_oscillation hf.1 P c hx hy) (abs_nonneg a)
  have ha : a * f x - a * f y ≤ |a| * |f x - f y| := by
    calc
      _ ≤ |a * f x - a * f y| := le_abs_self _
      _ = _ := by rw [← mul_sub, abs_mul]
  simpa only [zero_mul, add_zero] using ha.trans hm

theorem integrable_mul (hf : Integrable f Q) (hg : Integrable g Q) :
    Integrable (fun x => f x * g x) Q := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hf.1
  obtain ⟨N, hN0, hN⟩ := exists_abs_bound hg.1
  apply integrable_of_oscillation_bound hf hg (bounded_mul hf.1 hg.1) hN0 hM0
  intro P c
  apply cell_oscillation_le
  intro x hx y hy
  have hfc := abs_sub_le_cell_oscillation hf.1 P c hx hy
  have hgc := abs_sub_le_cell_oscillation hg.1 P c hx hy
  calc
    f x * g x - f y * g y ≤ |f x * g x - f y * g y| := le_abs_self _
    _ = |f x * (g x - g y) + g y * (f x - f y)| := by congr 1; ring
    _ ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
    _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
    _ ≤ M * (cellSupremum g P c - cellInfimum g P c) +
        N * (cellSupremum f P c - cellInfimum f P c) :=
      add_le_add (mul_le_mul (hM x (cell_subset P c hx)) hgc (abs_nonneg _) hM0)
        (mul_le_mul (hN y (cell_subset P c hy)) hfc (abs_nonneg _) hN0)
    _ = _ := add_comm _ _

theorem integrable_abs (hf : Integrable f Q) : Integrable (fun x => |f x|) Q := by
  apply integrable_of_oscillation_bound hf hf (bounded_abs hf.1)
    (A := 1) (B := 0) (by norm_num) le_rfl
  intro P c
  apply cell_oscillation_le
  intro x hx y hy
  have ha : |f x| - |f y| ≤ |f x - f y| := by
    have := abs_add_le (f x - f y) (f y)
    rw [sub_add_cancel] at this
    linarith
  simpa only [one_mul, zero_mul, add_zero] using
    ha.trans (abs_sub_le_cell_oscillation hf.1 P c hx hy)

theorem constant_sums (Q : Box n) (a : ℝ) (P : Grid Q) :
    lowerSum (fun _ => a) P = a * content Q ∧
    upperSum (fun _ => a) P = a * content Q := by
  have hl (c : CellIndex P) : cellInfimum (fun _ => a) P c = a := by
    change sInf _ = a
    rw [(cell_nonempty P c).image_const a, csInf_singleton]
  have hu (c : CellIndex P) : cellSupremum (fun _ => a) P c = a := by
    change sSup _ = a
    rw [(cell_nonempty P c).image_const a, csSup_singleton]
  constructor
  · change (∑ c, cellInfimum (fun _ => a) P c * cellContent P c) = _
    simp_rw [hl]
    rw [← Finset.mul_sum, content_partition]
  · change (∑ c, cellSupremum (fun _ => a) P c * cellContent P c) = _
    simp_rw [hu]
    rw [← Finset.mul_sum, content_partition]

theorem constant_integrals (Q : Box n) (a : ℝ) :
    lowerIntegral (fun _ => a) Q = a * content Q ∧
    upperIntegral (fun _ => a) Q = a * content Q := by
  obtain ⟨P₀⟩ := grid_exists Q
  have hl : Set.range (lowerSum (fun _ => a) (Q := Q)) = {a * content Q} := by
    ext t
    constructor
    · rintro ⟨P, rfl⟩
      exact (constant_sums Q a P).1
    · rintro rfl
      exact ⟨P₀, (constant_sums Q a P₀).1⟩
  have hu : Set.range (upperSum (fun _ => a) (Q := Q)) = {a * content Q} := by
    ext t
    constructor
    · rintro ⟨P, rfl⟩
      exact (constant_sums Q a P).2
    · rintro rfl
      exact ⟨P₀, (constant_sums Q a P₀).2⟩
  change sSup _ = _ ∧ sInf _ = _
  rw [hl, hu, csSup_singleton, csInf_singleton]
  exact ⟨rfl, rfl⟩

theorem integrable_const (Q : Box n) (a : ℝ) : Integrable (fun _ => a) Q :=
  ⟨bounded_const Q a, (constant_integrals Q a).1.trans (constant_integrals Q a).2.symm⟩

theorem integral_const (Q : Box n) (a : ℝ) (h : Integrable (fun _ => a) Q) :
    integral (fun _ => a) Q h = a * content Q := (constant_integrals Q a).1

theorem taggedSum_add (P : Grid Q) (ξ : Tagging P) :
    taggedSum (fun x => f x + g x) P ξ = taggedSum f P ξ + taggedSum g P ξ := by
  change (∑ c, (f (ξ c) + g (ξ c)) * cellContent P c) = _
  simp only [add_mul, Finset.sum_add_distrib]
  rfl

theorem taggedSum_smul (a : ℝ) (P : Grid Q) (ξ : Tagging P) :
    taggedSum (fun x => a * f x) P ξ = a * taggedSum f P ξ := by
  change (∑ c, (a * f (ξ c)) * cellContent P c) = _
  simp only [mul_assoc, ← Finset.mul_sum]
  rfl

theorem hasTaggedIntegral_add {I J : ℝ}
    (hf : HasTaggedIntegral f Q I) (hg : HasTaggedIntegral g Q J) :
    HasTaggedIntegral (fun x => f x + g x) Q (I + J) := by
  intro ε hε
  obtain ⟨δf, hδf, htf⟩ := hf (ε / 2) (half_pos hε)
  obtain ⟨δg, hδg, htg⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P ξ hP
  have hfP := htf P ξ (hP.trans_le (min_le_left _ _))
  have hgP := htg P ξ (hP.trans_le (min_le_right _ _))
  change |taggedSum (fun x => f x + g x) P ξ - (I + J)| < ε
  rw [taggedSum_add]
  have ht := abs_add_le (taggedSum f P ξ - I) (taggedSum g P ξ - J)
  have he : taggedSum f P ξ + taggedSum g P ξ - (I + J) =
      (taggedSum f P ξ - I) + (taggedSum g P ξ - J) := by ring
  rw [he]
  linarith

theorem hasTaggedIntegral_smul (a : ℝ) {I : ℝ} (hf : HasTaggedIntegral f Q I) :
    HasTaggedIntegral (fun x => a * f x) Q (a * I) := by
  intro ε hε
  have hd : 0 < |a| + 1 := by linarith [abs_nonneg a]
  obtain ⟨δ, hδ, ht⟩ := hf (ε / (|a| + 1)) (div_pos hε hd)
  refine ⟨δ, hδ, ?_⟩
  intro P ξ hP
  have h := ht P ξ hP
  change |taggedSum (fun x => a * f x) P ξ - a * I| < ε
  rw [taggedSum_smul, ← mul_sub, abs_mul]
  have hp := mul_le_mul_of_nonneg_left h.le (abs_nonneg a)
  have hε' : ε / (|a| + 1) * (|a| + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hd)
  have hpos : 0 < ε / (|a| + 1) := div_pos hε hd
  nlinarith

theorem nondegenerate_of_not_degenerate (h : ¬Degenerate Q) : Nondegenerate Q := by
  intro i
  exact lt_of_le_of_ne (Q.ordered i) (fun he => h ⟨i, he⟩)

theorem integral_add (hf : Integrable f Q) (hg : Integrable g Q)
    (h : Integrable (fun x => f x + g x) Q) :
    integral (fun x => f x + g x) Q h = integral f Q hf + integral g Q hg := by
  by_cases hd : Degenerate Q
  · change lowerIntegral _ Q = lowerIntegral f Q + lowerIntegral g Q
    rw [(degenerate_integrals _ Q hd).1, (degenerate_integrals f Q hd).1,
      (degenerate_integrals g Q hd).1, add_zero]
  · have hq := nondegenerate_of_not_degenerate hd
    exact taggedIntegral_unique _ Q hq (tagged_forward _ Q hq h)
      (hasTaggedIntegral_add (tagged_forward f Q hq hf) (tagged_forward g Q hq hg))

theorem integral_smul (a : ℝ) (hf : Integrable f Q)
    (h : Integrable (fun x => a * f x) Q) :
    integral (fun x => a * f x) Q h = a * integral f Q hf := by
  by_cases hd : Degenerate Q
  · change lowerIntegral _ Q = a * lowerIntegral f Q
    rw [(degenerate_integrals _ Q hd).1, (degenerate_integrals f Q hd).1, mul_zero]
  · have hq := nondegenerate_of_not_degenerate hd
    exact taggedIntegral_unique _ Q hq (tagged_forward _ Q hq h)
      (hasTaggedIntegral_smul a (tagged_forward f Q hq hf))

theorem integrable_sum {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → E n → ℝ) (hf : ∀ i ∈ s, Integrable (f i) Q) :
    Integrable (fun x => ∑ i ∈ s, f i x) Q := by
  induction s using Finset.induction_on with
  | empty => simpa using integrable_const Q 0
  | @insert i s hi ih =>
    have his := integrable_add (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using his

theorem integral_sum {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → E n → ℝ) (hf : ∀ i ∈ s, Integrable (f i) Q)
    (h : Integrable (fun x => ∑ i ∈ s, f i x) Q) :
    integral (fun x => ∑ i ∈ s, f i x) Q h =
      ∑ i ∈ s, if hi : i ∈ s then integral (f i) Q (hf i hi) else 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using integral_const Q 0 h
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, Integrable (f j) Q := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsi := integrable_sum s f hs
    have hsplit : (fun x => ∑ j ∈ insert i s, f j x) =
        (fun x => f i x + ∑ j ∈ s, f j x) := by
      funext x
      exact Finset.sum_insert hi
    have hval := integral_add (hf i (Finset.mem_insert_self i s)) hsi
      (hsplit ▸ h)
    have hind := ih hs hsi
    change lowerIntegral _ Q = _ at hval ⊢
    rw [hsplit, hval, hind]
    rw [Finset.sum_insert hi]
    simp only [Finset.mem_insert_self, ↓reduceDIte]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_insert_of_mem hj, hj, ↓reduceDIte]

/-- Monotonicity uses pointwise order only on Q, including its boundary. -/
theorem integral_mono (hf : Integrable f Q) (hg : Integrable g Q)
    (hfg : ∀ x ∈ carrier Q, f x ≤ g x) : integral f Q hf ≤ integral g Q hg := by
  apply (lowerIntegral_isLUB f Q hf.1).2
  rintro _ ⟨P, rfl⟩
  apply le_trans ?_ ((lowerIntegral_isLUB g Q hg.1).1 ⟨P, rfl⟩)
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_right ?_ (cellContent_nonneg P c)
  apply le_csInf ((cell_nonempty P c).image g)
  rintro _ ⟨x, hx, rfl⟩
  exact (cellInfimum_le f hf.1 P c hx).trans (hfg x (cell_subset P c hx))

theorem integral_abs_bound (hf : Integrable f Q) (ha : Integrable (fun x => |f x|) Q) :
    |integral f Q hf| ≤ integral (fun x => |f x|) Q ha ∧
    integral (fun x => |f x|) Q ha ≤ content Q * sSup ((fun x => |f x|) '' carrier Q) := by
  constructor
  · have hu := integral_mono hf ha (fun x _ => le_abs_self (f x))
    have hn := integrable_smul (-1) hf
    have hl := integral_mono hn ha (fun x _ => by simpa using neg_le_abs (f x))
    rw [integral_smul (-1) hf hn] at hl
    exact abs_le.mpr ⟨by linarith, hu⟩
  · let M := sSup ((fun x => |f x|) '' carrier Q)
    have hm : ∀ x ∈ carrier Q, |f x| ≤ M := fun x hx =>
      le_csSup ha.1.2 ⟨x, hx, rfl⟩
    have h := integral_mono ha (integrable_const Q M) hm
    rw [integral_const] at h
    simpa only [mul_comm M (content Q)] using h

end D04.Darboux
