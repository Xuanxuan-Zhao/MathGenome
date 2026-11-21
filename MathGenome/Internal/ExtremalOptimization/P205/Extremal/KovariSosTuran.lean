import MathGenome.Internal.ExtremalOptimization.Specs.P205.Extremal.KovariSosTuran
import MathGenome.Internal.ExtremalOptimization.P205.Extremal.KSTStarCount
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace P205.Extremal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Disjoint complete parts give an injective graph homomorphism, with no
restriction on the ambient edges inside the parts. -/
theorem containsCompleteBipartite_copy (G : SimpleGraph V) (s t : ℕ)
    (h : ContainsCompleteBipartite G s t) :
    Nonempty ((completeBipartiteGraph (Fin s) (Fin t)).Copy G) := by
  classical
  obtain ⟨A, B, hA, hB, hd, hab⟩ := h
  let a : Fin s ≃ A := (Fintype.equivFinOfCardEq (by simpa using hA)).symm
  let b : Fin t ≃ B := (Fintype.equivFinOfCardEq (by simpa using hB)).symm
  let f : Fin s ⊕ Fin t → V := Sum.elim (fun i => (a i).val) (fun j => (b j).val)
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => simp [completeBipartiteGraph_adj] at hxy
      | inr j => exact hab _ (a i).property _ (b j).property
    | inr i =>
      cases y with
      | inl j => exact G.adj_symm (hab _ (a j).property _ (b i).property)
      | inr j => simp [completeBipartiteGraph_adj] at hxy
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (a.injective (Subtype.ext hxy))
      | inr j =>
        exact False.elim (Finset.disjoint_left.mp hd (a i).property
          (by change (a i).val = (b j).val at hxy
              rw [hxy]
              exact (b j).property))
    | inr i =>
      cases y with
      | inl j =>
        exact False.elim (Finset.disjoint_left.mp hd (a j).property
          (by change (b i).val = (a j).val at hxy
              rw [← hxy]
              exact (b i).property))
      | inr j => exact congrArg Sum.inr (b.injective (Subtype.ext hxy))

/-- The falling factorial lies between a truncated power and the full power. -/
theorem truncated_power_le_factorial_choose (d s : ℕ) (hs : 1 ≤ s) :
    (d - (s - 1)) ^ s ≤ s.factorial * d.choose s := by
  have heq : d - (s - 1) = d + 1 - s := by omega
  rw [heq, ← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.pow_sub_le_descFactorial d s

/-- The star-count bound controls the s-th powers of truncated degrees. -/
theorem sum_truncated_degree_pow_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : ℕ) (hs : 1 ≤ s) (hst : s ≤ t)
    (hfree : ¬ ContainsCompleteBipartite G s t) :
    (∑ v : V, ((G.degree v - (s - 1) : ℕ) : ℝ) ^ s) ≤
      ((t - 1 : ℕ) : ℝ) * (Fintype.card V : ℝ) ^ s := by
  have hnat : (∑ v : V, (G.degree v - (s - 1)) ^ s) ≤
      (t - 1) * Fintype.card V ^ s := by
    calc
      _ ≤ ∑ v : V, s.factorial * (G.degree v).choose s :=
        sum_le_sum fun v _ => truncated_power_le_factorial_choose _ s hs
      _ = s.factorial * ∑ v : V, (G.degree v).choose s := (mul_sum ..).symm
      _ ≤ s.factorial * ((t - 1) * (Fintype.card V).choose s) :=
        Nat.mul_le_mul_left _ (star_count_le G s t hs hst hfree)
      _ = (t - 1) * (s.factorial * (Fintype.card V).choose s) := by ring
      _ ≤ (t - 1) * Fintype.card V ^ s := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ s)
  exact_mod_cast hnat

/-- A finite nonnegative power-mean estimate in the form used in KST. -/
theorem sum_le_root_mul_card_rpow {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (s : ℕ) (hs : 1 ≤ s)
    (a : ℝ) (ha : 0 ≤ a)
    (h : (∑ i, f i ^ s) ≤ a * (Fintype.card ι : ℝ) ^ s) :
    (∑ i, f i) ≤ a ^ (1 / (s : ℝ)) *
      (Fintype.card ι : ℝ) ^ (2 - 1 / (s : ℝ)) := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp only [sum_of_isEmpty]
    positivity
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (s : ℝ) ≠ 0 := by linarith
  have hr : 0 ≤ 1 / (s : ℝ) := by positivity
  have hw : (∑ _ : ι, (Fintype.card ι : ℝ)⁻¹) = 1 := by
    simp [ne_of_gt hn]
  have hm := Real.arith_mean_le_rpow_mean (univ : Finset ι)
    (fun _ => (Fintype.card ι : ℝ)⁻¹) f
    (fun _ _ => inv_nonneg.mpr hn.le) hw (fun i _ => hf i) hsR
  simp only [Real.rpow_natCast, ← mul_sum] at hm
  have hroot := Real.rpow_le_rpow
    (mul_nonneg (inv_nonneg.mpr hn.le) (sum_nonneg fun i _ => pow_nonneg (hf i) _))
    (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hn.le)) hr
  have hmean := hm.trans hroot
  have hmul := mul_le_mul_of_nonneg_left hmean hn.le
  have hid : (Fintype.card ι : ℝ) *
      ((Fintype.card ι : ℝ)⁻¹ * (a * (Fintype.card ι : ℝ) ^ s)) ^ (1 / (s : ℝ)) =
      a ^ (1 / (s : ℝ)) * (Fintype.card ι : ℝ) ^ (2 - 1 / (s : ℝ)) := by
    rw [show (Fintype.card ι : ℝ)⁻¹ * (a * (Fintype.card ι : ℝ) ^ s) =
      a * ((Fintype.card ι : ℝ) ^ s / (Fintype.card ι : ℝ)) by ring]
    rw [Real.mul_rpow ha (by positivity), Real.div_rpow (by positivity) hn.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    rw [show (s : ℝ) * (1 / (s : ℝ)) = 1 by field_simp, Real.rpow_one,
      Real.rpow_sub hn, Real.rpow_two]
    ring
  rw [hid] at hmul
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn), one_mul] using hmul

/-- Kővári–Sós–Turán for arbitrary finite simple graphs and non-induced copies. -/
theorem kovari_sos_turan : KovariSosTuranSpec.quantitativeBound := by
  intro V _ _ G _ s t hs hst hcopy
  have hfree : ¬ ContainsCompleteBipartite G s t := by
    intro h
    obtain ⟨c⟩ := containsCompleteBipartite_copy G s t h
    exact hcopy.false c
  have hroot := sum_le_root_mul_card_rpow
    (fun v => ((G.degree v - (s - 1) : ℕ) : ℝ)) (fun _ => Nat.cast_nonneg _)
    s hs ((t - 1 : ℕ) : ℝ) (Nat.cast_nonneg _)
    (sum_truncated_degree_pow_le G s t hs hst hfree)
  have hdeg : (∑ v : V, (G.degree v : ℝ)) ≤
      ((s - 1 : ℕ) : ℝ) * Fintype.card V +
        ∑ v : V, ((G.degree v - (s - 1) : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ v : V, (((s - 1 : ℕ) : ℝ) + ((G.degree v - (s - 1) : ℕ) : ℝ)) := by
        apply sum_le_sum
        intro v _
        exact_mod_cast (show G.degree v ≤ (s - 1) + (G.degree v - (s - 1)) by omega)
      _ = _ := by simp [sum_add_distrib, mul_comm]
  have hsum : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hdeg
  have hcastS : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    rw [Nat.cast_sub hs, Nat.cast_one]
  have hcastT : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub (hs.trans hst), Nat.cast_one]
  rw [hcastS] at hdeg
  rw [hcastT] at hroot
  linarith

/-- The exact maximum among the labelled forbidden-subgraph-free graphs. -/
noncomputable abbrev extremalEdgeCount : ℕ → ℕ → ℕ → ℕ :=
  KovariSosTuranSpec.extremalEdgeCountValue

private theorem cast_finset_sup_le {α : Type*} (S : Finset α) (f : α → ℕ)
    (b : ℝ) (hb : 0 ≤ b) (h : ∀ x ∈ S, (f x : ℝ) ≤ b) :
    ((S.sup f : ℕ) : ℝ) ≤ b := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hb
  | @insert x S hx ih =>
    rw [Finset.sup_insert, Nat.cast_max]
    exact max_le (h x (mem_insert_self _ _))
      (ih (fun y hy => h y (mem_insert_of_mem hy)))

/-- A uniform bound on the actual extremal count (the harmless factor two is dropped). -/
theorem extremalEdgeCount_le (s t n : ℕ) (hs : 1 ≤ s) (hst : s ≤ t) :
    (extremalEdgeCount s t n : ℝ) ≤
      ((s : ℝ) - 1) * n + ((t : ℝ) - 1) ^ (1 / (s : ℝ)) *
        (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
  classical
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  unfold extremalEdgeCount KovariSosTuranSpec.extremalEdgeCountValue
  apply cast_finset_sup_le
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hsR) (Nat.cast_nonneg n))
      (mul_nonneg (Real.rpow_nonneg (by
        have htR : (1 : ℝ) ≤ t := by exact_mod_cast hs.trans hst
        linarith) _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · intro G hG
    have hfree := (mem_filter.mp hG).2
    have h := kovari_sos_turan G s t hs hst hfree
    simp only [Fintype.card_fin] at h
    have he : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
    linarith

/-- Fixed-parameter big-O for the maximum edge count on n vertices. -/
theorem extremalEdgeCount_isBigO : KovariSosTuranSpec.asymptoticBound := by
  intro s t hs hst
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hexp : (1 : ℝ) ≤ 2 - 1 / (s : ℝ) := by
    have hdiv : (1 : ℝ) / s ≤ 1 :=
      (div_le_iff₀ (by linarith : (0 : ℝ) < s)).mpr (by linarith)
    linarith
  apply Asymptotics.IsBigO.of_bound
    (((s : ℝ) - 1) + ((t : ℝ) - 1) ^ (1 / (s : ℝ)))
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hnR hexp
  have h := extremalEdgeCount_le s t n hs hst
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0 _)]
  calc
    _ ≤ ((s : ℝ) - 1) * n + ((t : ℝ) - 1) ^ (1 / (s : ℝ)) *
        (n : ℝ) ^ (2 - 1 / (s : ℝ)) := h
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hsR)]

end P205.Extremal
