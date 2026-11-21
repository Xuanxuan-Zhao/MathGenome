import MathGenome.Internal.ExtremalOptimization.Specs.P205.Extremal.ErdosStoneSimonovits
import MathGenome.Internal.ExtremalOptimization.P205.Extremal.Turan
import MathGenome.Internal.ExtremalOptimization.P205.Extremal.CliqueBlowups
import Mathlib.Tactic.FieldSimp

namespace P205.Extremal

open SimpleGraph Filter
open scoped Topology

/-- The chromatic number is finite for every graph on a finite vertex type. -/
lemma finite_chromaticNumber {W : Type*} [Fintype W] (H : SimpleGraph W) :
    (H.chromaticNumber.toNat : ℕ∞) = H.chromaticNumber := by
  exact ENat.natCast_toNat (ne_top_of_le_ne_top (by simp) H.chromaticNumber_le_card)

/-- A proper coloring embeds the whole graph, including its isolated vertices,
into a complete equipartite graph whose parts have the size of its vertex set. -/
lemma contained_chromatic_blowup {W : Type*} [Fintype W] (H : SimpleGraph W) :
    H ⊑ completeEquipartiteGraph H.chromaticNumber.toNat (Fintype.card W) := by
  classical
  obtain ⟨C⟩ := colorable_chromaticNumber_of_fintype H
  exact isContained_completeEquipartiteGraph_of_colorable C _
    (fun _ => Fintype.card_subtype_le _)

/-- Residues modulo the number of parts are a proper coloring of the Turán graph. -/
def turan_residue_coloring (n k : ℕ) (hk : 0 < k) :
    (turanGraph n k).Coloring (Fin k) :=
  Coloring.mk (fun v => ⟨v.val % k, Nat.mod_lt _ hk⟩)
    (fun h he => h (congrArg Fin.val he))

/-- A graph needing more than `k` colors cannot be a subgraph of `T_k(n)`. -/
lemma turan_free_of_chromatic {W : Type*} [Fintype W] (H : SimpleGraph W)
    (n k : ℕ) (hk : 0 < k) (hχ : k < H.chromaticNumber.toNat) :
    H.Free (turanGraph n k) := by
  rintro ⟨f⟩
  have hc : H.Colorable k := ⟨(turan_residue_coloring n k hk).comap f.toHom⟩
  have he : (H.chromaticNumber.toNat : ℕ∞) ≤ k := by
    rw [finite_chromaticNumber]
    exact hc.chromaticNumber_le
  have : H.chromaticNumber.toNat ≤ k := by exact_mod_cast he
  omega

private lemma twice_choose_two (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

private lemma choose_two_add (n k : ℕ) :
    (n + k).choose 2 = n.choose 2 + k.choose 2 + n * k := by
  have hn := twice_choose_two n
  have hk := twice_choose_two k
  have hnk := twice_choose_two (n + k)
  nlinarith

/-- A useful finite version of the Turán lower density bound. -/
lemma choose_mul_pred_le_mul_turanNumber (n k : ℕ) (hk : 0 < k) :
    (k - 1) * n.choose 2 ≤ k * turanNumber n k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnk : n < k
    · have ht : turanGraph n k = ⊤ := turanGraph_eq_top.mpr (Or.inr hnk.le)
      have he : turanNumber n k = n.choose 2 := by
        have he := card_edgeFinset_top_eq_card_choose_two (V := Fin n)
        rw [Fintype.card_fin] at he
        convert he
      rw [he]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    · have hkn : k ≤ n := by omega
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
      have hm := ih m (by omega)
      rw [Nat.add_comm k m, turanNumber_add, choose_two_add]
      have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
      nlinarith

/-- The balanced Turán graph has at least the limiting density already at each
finite order, before division by the number of vertex pairs. -/
lemma turan_real_lower_bound (n k : ℕ) (hk : 0 < k) :
    (1 - 1 / (k : ℝ)) * (n.choose 2 : ℝ) ≤ (turanNumber n k : ℝ) := by
  have hb := choose_mul_pred_le_mul_turanNumber n k hk
  have hb' : ((k : ℝ) - 1) * (n.choose 2 : ℝ) ≤ (k : ℝ) * (turanNumber n k : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_one] using
      (show (((k - 1) * n.choose 2 : ℕ) : ℝ) ≤ (k * turanNumber n k : ℕ) from
        Nat.cast_le.mpr hb)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply (mul_le_mul_iff_right₀ hk').mp
  field_simp
  nlinarith

/-- The nonempty-edge assumption ensures at least two colors. -/
lemma two_le_finite_chromaticNumber {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hH : H ≠ ⊥) : 2 ≤ H.chromaticNumber.toNat := by
  have h := two_le_chromaticNumber_iff_ne_bot.mpr hH
  rw [← finite_chromaticNumber H] at h
  exact_mod_cast h

lemma finite_chromaticNumber_le_card {W : Type*} [Fintype W] (H : SimpleGraph W) :
    H.chromaticNumber.toNat ≤ Fintype.card W := by
  have h := H.chromaticNumber_le_card
  rw [← finite_chromaticNumber H] at h
  exact_mod_cast h

/-- The Turán lower examples for every order. -/
lemma turan_le_extremalNumber {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H ≠ ⊥) (n : ℕ) :
    turanNumber n (H.chromaticNumber.toNat - 1) ≤ extremalNumber n H := by
  have hr := two_le_finite_chromaticNumber H hH
  have hfree := turan_free_of_chromatic H n (H.chromaticNumber.toNat - 1)
    (by omega) (by omega)
  simpa only [Fintype.card_fin] using card_edgeFinset_le_extremalNumber hfree

/-- Above any positive excess, sufficiently large `H`-free graphs are excluded
by the clique blow-up theorem and the proper-coloring embedding. -/
lemma extremalNumber_eventually_lt_threshold {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hH : H ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      (extremalNumber n H : ℝ) <
        (1 - 1 / ((H.chromaticNumber.toNat : ℝ) - 1) + ε) * (n.choose 2 : ℝ) := by
  classical
  have hr := two_le_finite_chromaticNumber H hH
  have ht : 1 ≤ Fintype.card W := le_trans (by omega) (finite_chromaticNumber_le_card H)
  obtain ⟨N, hN⟩ := clique_blowups H.chromaticNumber.toNat (Fintype.card W) hr ht ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨G, _, hG⟩ := exists_isExtremal_free (V := Fin n) hH
  have he : G.edgeFinset.card = extremalNumber n H := by
    simpa only [Fintype.card_fin] using (isExtremal_free_iff.mp hG).2
  apply lt_of_not_ge
  intro hd
  have hcopy : completeEquipartiteGraph H.chromaticNumber.toNat (Fintype.card W) ⊑ G := by
    apply hN G (by simpa only [Fintype.card_fin] using hn)
    simpa only [Fintype.card_fin, he] using hd
  exact hG.prop ((contained_chromatic_blowup H).trans hcopy)

/-- Erdős–Stone–Simonovits for all finite graphs with at least one edge. -/
theorem erdos_stone_simonovits : ErdosStoneSimonovitsSpecs.densityStatement := by
  intro W _ H hH
  have hr := two_le_finite_chromaticNumber H hH
  have hcast : ((H.chromaticNumber.toNat - 1 : ℕ) : ℝ) =
      (H.chromaticNumber.toNat : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ H.chromaticNumber.toNat), Nat.cast_one]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hp : (0 : ℝ) < n.choose 2 := by
      exact_mod_cast (Nat.choose_pos hn)
    have hl := turan_real_lower_bound n (H.chromaticNumber.toNat - 1) (by omega)
    rw [hcast] at hl
    have he : (turanNumber n (H.chromaticNumber.toNat - 1) : ℝ) ≤ extremalNumber n H := by
      exact_mod_cast turan_le_extremalNumber H hH n
    exact ha.trans_le ((le_div_iff₀ hp).mpr (hl.trans he))
  · intro b hb
    obtain ⟨N, hN⟩ := extremalNumber_eventually_lt_threshold H hH
      (b - (1 - 1 / ((H.chromaticNumber.toNat : ℝ) - 1))) (sub_pos.mpr hb)
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 2] with n hn hn2
    have hp : (0 : ℝ) < n.choose 2 := by
      exact_mod_cast (Nat.choose_pos hn2)
    apply (div_lt_iff₀ hp).mpr
    convert hN n hn using 1; ring

/-- In particular every finite bipartite forbidden graph with an edge has
limiting extremal density zero. -/
theorem bipartite_extremal_density : ErdosStoneSimonovitsSpecs.bipartiteStatement := by
  intro W _ H hH hb
  have he : H.chromaticNumber.toNat = 2 := by
    rw [chromaticNumber_eq_two_iff.mpr ⟨hb, hH⟩]
    rfl
  simpa only [he, Nat.cast_ofNat, show (1 - 1 / ((2 : ℝ) - 1)) = 0 by norm_num] using
    erdos_stone_simonovits H hH

end P205.Extremal
