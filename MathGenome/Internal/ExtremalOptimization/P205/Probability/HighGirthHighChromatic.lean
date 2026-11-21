import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.HighGirthHighChromatic
import MathGenome.Internal.ExtremalOptimization.P205.Probability.RandomGraphIndependence
import Mathlib.Data.Finset.Sigma

open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

namespace P205.Probability.HighGirthHighChromatic
open RandomGraphCycles RandomGraphIndependence

/-- Choose one endpoint of one edge of each original short cycle. -/
theorem cycle_deletion : Specs.P205.Probability.HighGirthHighChromatic.CycleDeletion := by
  intro n g G
  let B := (Finset.Icc 3 g).sigma (fun l =>
    (cycles n l).filter (fun S => ∀ e ∈ S, e.val ∈ G.edgeSet))
  have hB (i : Σ _ : ℕ, Finset (Edge n)) (hi : i ∈ B) : i.2.Nonempty := by
    have hm := Finset.mem_sigma.mp hi
    have hc := card_cycle (Finset.mem_Icc.mp hm.1).1 (Finset.mem_filter.mp hm.2).1
    apply Finset.card_pos.mp
    rw [hc]
    exact lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hm.1).1
  let pick (i : {i // i ∈ B}) : Fin n := ((hB i.val i.property).choose).val.out.1
  let D := B.attach.image pick
  let S := Finset.univ \ D
  have hD : D.card ≤ shortCycleCount g G := by
    calc
      D.card ≤ B.card := (Finset.card_image_le).trans_eq Finset.card_attach
      _ = shortCycleCount g G := by simp [B, shortCycleCount, Finset.card_sigma]
  have hsize : n - S.card = D.card := by
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    dsimp [S]
    omega
  refine ⟨S, hsize ▸ hD, ?_⟩
  intro v w hw
  by_contra hlen
  have hl : w.length ≤ g := by omega
  have hc := (SimpleGraph.cycleGraph_isContained_iff (by have := hw.three_le_length; omega)).mpr
    ⟨v, w, hw, rfl⟩
  obtain ⟨f, hf⟩ := SimpleGraph.isContained_iff_exists_le_comap.mp hc
  let j : Fin w.length ↪ Fin n :=
    ⟨fun x => (f x).val, Subtype.val_injective.comp f.injective⟩
  let H := (SimpleGraph.cycleGraph w.length).map j
  have hHG : H ≤ G := by
    apply SimpleGraph.map_le_iff_le_comap.mpr
    exact hf
  let i : Σ _ : ℕ, Finset (Edge n) := ⟨w.length, graphEdges H⟩
  have hi : i ∈ B := by
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hw.three_le_length, hl⟩, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · intro e he
      exact SimpleGraph.edgeSet_mono hHG ((mem_graphEdges H e).mp he)
  let e := (hB i hi).choose
  have he : e ∈ graphEdges H := (hB i hi).choose_spec
  have heH : H.Adj e.val.out.1 e.val.out.2 := by
    have hh := (mem_graphEdges H e).mp he
    rwa [← Sym2.mk_fst_out_snd_out e.val] at hh
  obtain ⟨x, _y, _, hx, _⟩ := (SimpleGraph.map_adj j _ _ _).mp heH
  have hpS : pick ⟨i, hi⟩ ∈ S := by
    change e.val.out.1 ∈ S
    rw [← hx]
    exact (f x).property
  have hpD : pick ⟨i, hi⟩ ∈ D := Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩
  exact (Finset.mem_sdiff.mp hpS).2 hpD

/-- Independent sets of an induced graph embed into the original graph. -/
lemma independent_card_le {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (T : Finset (S : Set (Fin n)))
    (hT : (G.induce (S : Set (Fin n))).IsIndepSet (T : Set (S : Set (Fin n)))) :
    T.card ≤ G.indepNum := by
  let emb : (S : Set (Fin n)) ↪ Fin n := ⟨Subtype.val, Subtype.val_injective⟩
  have hI : G.IsIndepSet ((T.map emb : Finset (Fin n)) : Set (Fin n)) := by
    intro u hu v hv hne hadj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hv
    exact hT hx hy (fun h => hne (congrArg emb h)) hadj
  simpa using hI.card_le_indepNum

/-- Counting the fibers of a proper coloring. -/
lemma cardinal_le_colors_mul_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k b : ℕ) (h : ∀ T : Finset V, G.IsIndepSet (T : Set V) → T.card ≤ b)
    (hc : G.Colorable k) : Fintype.card V ≤ k * b := by
  obtain ⟨c⟩ := hc
  let F : Fin k → Finset V := fun i => Finset.univ.filter (fun v => c v = i)
  have hf (i : Fin k) : (F i).card ≤ b := by
    apply h
    intro u hu v hv _ hadj
    exact c.valid hadj ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
  have hsum : (∑ i : Fin k, (F i).card) = Fintype.card V := by
    simpa [F] using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset V) (Finset.univ : Finset (Fin k)) c
  calc
    Fintype.card V = ∑ i : Fin k, (F i).card := hsum.symm
    _ ≤ ∑ _i : Fin k, b := Finset.sum_le_sum (fun i _ => hf i)
    _ = k * b := by simp

/-- Quantitative deletion and the color-class obstruction. -/
theorem alteration : Specs.P205.Probability.HighGirthHighChromatic.Alteration := by
  intro g k n G _hg hk hn hC hI
  obtain ⟨S, hdel, hcycles⟩ := cycle_deletion n g G
  have hScard : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hret : (n : ℝ) / 2 < (S.card : ℝ) := by
    have hnat : n ≤ S.card + shortCycleCount g G := by omega
    have hreal : (n : ℝ) ≤ (S.card : ℝ) + (shortCycleCount g G : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hapos : 1 ≤ threshold k n := by omega
  have ha : ((threshold k n - 1 : ℕ) : ℝ) < (n : ℝ) / (4 * (k : ℝ)) := by
    rw [Nat.cast_sub hapos, Nat.cast_one]
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) / (4 * (k : ℝ)) by positivity)
    change (threshold k n : ℝ) < (n : ℝ) / (4 * (k : ℝ)) + 1 at hceil
    linarith
  have hind (T : Finset (S : Set (Fin n)))
      (hT : (G.induce (S : Set (Fin n))).IsIndepSet (T : Set (S : Set (Fin n)))) :
      T.card ≤ threshold k n - 1 := by
    have h := independent_card_le G S T hT
    omega
  refine ⟨S, hdel, hret, hcycles, ha, ?_, ?_⟩
  · intro T hT
    exact ⟨hind T hT, lt_of_le_of_lt (by exact_mod_cast hind T hT) ha⟩
  · intro hcol
    have hcover := cardinal_le_colors_mul_bound (G.induce (S : Set (Fin n)))
      k (threshold k n - 1) hind hcol
    have hcover' : (S.card : ℝ) ≤ (k : ℝ) * ((threshold k n - 1 : ℕ) : ℝ) := by
      have hcoverNat : S.card ≤ k * (threshold k n - 1) := by simpa using hcover
      exact_mod_cast hcoverNat
    have hprod := mul_lt_mul_of_pos_left ha hkpos
    have heq : (k : ℝ) * ((n : ℝ) / (4 * (k : ℝ))) = (n : ℝ) / 4 := by
      field_simp
    rw [heq] at hprod
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    linarith

/-- The full high-girth, high-chromatic-number theorem (paper W24). -/
theorem high_girth_high_chromatic :
    Specs.P205.Probability.HighGirthHighChromatic.Existence := by
  intro g k hg hk
  obtain ⟨n, G, hn, hC, hI⟩ := good_graph_exists g k hg hk
  have hcount : (shortCycleCount g G : ℝ) < (n : ℝ) / 2 := by
    simpa only [shortCycleCount, Nat.cast_sum] using hC
  obtain ⟨S, _hdel, _hret, hcycles, _ha, _hind, hcol⟩ := alteration g k n G hg hk hn hcount hI
  refine ⟨n, S, G.induce (S : Set (Fin n)), hcycles, ?_⟩
  exact lt_of_not_ge (fun h => hcol (SimpleGraph.chromaticNumber_le_iff_colorable.mp h))

end P205.Probability.HighGirthHighChromatic
