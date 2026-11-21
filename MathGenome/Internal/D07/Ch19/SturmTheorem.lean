import MathGenome.Internal.Specs.D07.Ch19.SturmTheorem
import MathGenome.Internal.D07.Ch19.SturmTheoremLocalSignVariation
import MathGenome.Internal.D07.Ch19.CauchyRootBound
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
namespace D07.Ch19.SturmTheorem
open Polynomial Filter
open Specs.D07.Ch19.SturmTheorem
open Specs.D07.Ch19.SturmTheoremLocalSignVariation
open scoped Topology Classical BigOperators

lemma mem_realRoots {f : Poly} (hf : f ≠ 0) (x : ℝ) :
    x ∈ realRoots f ↔ f.eval x = 0 := by
  simp only [realRoots, Multiset.mem_toFinset, Polynomial.mem_roots hf, IsRoot.def]

/-- Each root contributes a unit step, including the root itself. -/
def steps (R : Finset ℝ) (x : ℝ) : ℤ := ∑ r ∈ R, if r ≤ x then 1 else 0

lemma step_eventually_eq {r c : ℝ} (h : r ≠ c) :
    ∀ᶠ x in 𝓝 c, (if r ≤ x then (1 : ℤ) else 0) = if r ≤ c then 1 else 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · filter_upwards [eventually_gt_nhds h] with x hx
    simp [hx.le, h.le]
  · filter_upwards [eventually_lt_nhds h] with x hx
    simp [not_le.mpr hx, not_le.mpr h]

lemma steps_eventually_eq (R : Finset ℝ) (c : ℝ) (hc : c ∉ R) :
    ∀ᶠ x in 𝓝 c, steps R x = steps R c := by
  have h : ∀ᶠ x in 𝓝 c, ∀ r ∈ R,
      (if r ≤ x then (1 : ℤ) else 0) = if r ≤ c then 1 else 0 :=
    (R.eventually_all).mpr (fun r hr => step_eventually_eq (fun he => hc (he ▸ hr)))
  filter_upwards [h] with x hx
  exact Finset.sum_congr rfl hx

/-- Adding the steps of the roots cancels the jumps in the variation. -/
lemma corrected_variation_locally_constant (s : Poly) (L : List Poly)
    (hL : IsSturmChain s L) (c : ℝ) :
    ∀ᶠ x in 𝓝 c,
      (variation L x : ℤ) + steps (realRoots s) x =
      (variation L c : ℤ) + steps (realRoots s) c := by
  have hs : s ≠ 0 := ne_zero_of_natDegree_gt hL.1
  by_cases hc : s.eval c = 0
  · have hmem : c ∈ realRoots s := (mem_realRoots hs c).mpr hc
    have hsteps := steps_eventually_eq ((realRoots s).erase c) c (Finset.notMem_erase c _)
    have hsplit (x : ℝ) : steps (realRoots s) x =
        (if c ≤ x then 1 else 0) + steps ((realRoots s).erase c) x := by
      exact (Finset.add_sum_erase _ _ hmem).symm
    obtain ⟨hleft, hright⟩ := SturmTheoremLocalSignVariation.root_jump s L hL c hc
    have hl : ∀ᶠ x in 𝓝[<] c,
        (variation L x : ℤ) + steps (realRoots s) x =
        (variation L c : ℤ) + steps (realRoots s) c := by
      filter_upwards [hleft, hsteps.filter_mono nhdsWithin_le_nhds,
        (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[<] c, x < c)] with x hv ht hx
      change x < c at hx
      rw [hsplit x, hsplit c, hv, ht]
      simp only [not_le.mpr hx, ↓reduceIte, le_refl, Nat.cast_add, Nat.cast_one]
      ring
    have hr : ∀ᶠ x in 𝓝[>] c,
        (variation L x : ℤ) + steps (realRoots s) x =
        (variation L c : ℤ) + steps (realRoots s) c := by
      filter_upwards [hright, hsteps.filter_mono nhdsWithin_le_nhds,
        (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] c, c < x)] with x hv ht hx
      change c < x at hx
      rw [hsplit x, hsplit c, hv, ht]
      simp [hx.le]
    rw [← nhdsLT_sup_nhdsGE c, Filter.eventually_sup]
    refine ⟨hl, ?_⟩
    rw [← nhdsGT_sup_nhdsWithin_singleton c, Filter.eventually_sup]
    refine ⟨hr, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x = c := Set.mem_singleton_iff.mp hx
    subst x
    rfl
  · filter_upwards [SturmTheoremLocalSignVariation.nonroot_local_constancy s L hL c hc,
      steps_eventually_eq (realRoots s) c (by simpa only [mem_realRoots hs c] using hc)]
      with x hv ht
    rw [hv, ht]

lemma corrected_variation_constant (s : Poly) (L : List Poly)
    (hL : IsSturmChain s L) (a b : ℝ) :
    (variation L a : ℤ) + steps (realRoots s) a =
    (variation L b : ℤ) + steps (realRoots s) b := by
  have hcont : Continuous (fun x => (variation L x : ℤ) + steps (realRoots s) x) := by
    apply continuous_iff_continuousAt.mpr
    intro c
    exact continuousAt_const.congr_of_eventuallyEq
      (corrected_variation_locally_constant s L hL c)
  exact isPreconnected_univ.constant hcont.continuousOn (Set.mem_univ a) (Set.mem_univ b)

/-- Difference of the cumulative steps counts the half-open interval (a,b]. -/
lemma steps_sub (R : Finset ℝ) {a b : ℝ} (hab : a ≤ b) :
    steps R b - steps R a = ((R.filter (fun r => a < r ∧ r ≤ b)).card : ℤ) := by
  rw [steps, steps, ← Finset.sum_sub_distrib]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> norm_num <;> grind

lemma realRoots_eq {f s : Poly} (hf : f ≠ 0) (hs : s ≠ 0)
    (hroots : ∀ x : ℝ, s.eval x = 0 ↔ f.eval x = 0) : realRoots s = realRoots f := by
  ext x
  rw [mem_realRoots hs, mem_realRoots hf, hroots]

theorem interval_count_for_chain : IntervalCountForChain := by
  intro f s L hf hroots hL a b hab ha hb
  have hs : s ≠ 0 := ne_zero_of_natDegree_gt hL.1
  have hconst := corrected_variation_constant s L hL a b
  have hstep := steps_sub (realRoots s) hab.le
  have heq : (realRoots s).filter (fun r => a < r ∧ r ≤ b) =
      (realRoots f).filter (fun r => a < r ∧ r < b) := by
    rw [realRoots_eq hf hs hroots]
    apply Finset.filter_congr
    intro r hr
    have hne : r ≠ b := by
      intro he
      subst r
      exact hb ((hroots b).mpr ((mem_realRoots hf b).mp hr))
    exact and_congr_right (fun _ => le_iff_lt_or_eq.trans (by simp [hne]))
  rw [heq] at hstep
  change steps (realRoots s) b - steps (realRoots s) a = (rootCount f a b : ℤ) at hstep
  have hsum : variation L a = variation L b + rootCount f a b := by omega
  exact ⟨hsum, by omega⟩

/-- A finite set of roots eventually lies strictly to the left. -/
lemma roots_eventually_lt (p : Poly) :
    ∀ᶠ x : ℝ in atTop, ∀ r ∈ realRoots p, r < x :=
  (Finset.eventually_all _).mpr (fun r _ => eventually_gt_atTop r)

lemma sign_eval_atTop (p : Poly) (hp : p ≠ 0) :
    ∀ᶠ x : ℝ in atTop, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  filter_upwards [roots_eventually_lt p] with x hx
  have hroots : ∀ r, p.IsRoot r → r < x := by
    intro r hr
    exact hx r ((mem_realRoots hp r).mpr hr)
  rcases (leadingCoeff_ne_zero.mpr hp).lt_or_gt with hn | hp
  · rw [sign_neg hn, sign_neg (eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hroots hn.le)]
  · rw [sign_pos hp, sign_pos (zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hroots hp.le)]

lemma sign_eval_atBot (p : Poly) (hp : p ≠ 0) :
    ∀ᶠ x : ℝ in atBot, SignType.sign (p.eval x) =
      SignType.sign (p.leadingCoeff * (-1 : ℝ) ^ p.natDegree) := by
  have hq : p.comp (-X) ≠ 0 := by simpa using hp
  have h := tendsto_neg_atBot_atTop.eventually (sign_eval_atTop (p.comp (-X)) hq)
  have hlc : (p.comp (-X)).leadingCoeff = p.leadingCoeff * (-1 : ℝ) ^ p.natDegree := by
    simp [mul_comm]
  simpa only [Function.comp_def, eval_comp, eval_neg, eval_X, neg_neg, hlc] using h

theorem infinity_signs : InfinitySigns := by
  intro L hL
  exact ⟨(L.finite_toSet.eventually_all).mpr (fun p hp => sign_eval_atTop p (hL p hp)),
    (L.finite_toSet.eventually_all).mpr (fun p hp => sign_eval_atBot p (hL p hp))⟩

lemma variation_eq_of_signs (L : List Poly) (v : Poly → ℝ) (x : ℝ)
    (h : ∀ p ∈ L, SignType.sign (p.eval x) = SignType.sign (v p)) :
    variation L x = (L.map v).signVariations := by
  apply List.signVariations_congr
  simp only [List.map_map]
  exact List.map_congr_left h

theorem infinity_variations : InfinityVariations := by
  intro L hL
  obtain ⟨ht, hb⟩ := infinity_signs L hL
  exact ⟨ht.mono (fun x hx => variation_eq_of_signs L _ x hx),
    hb.mono (fun x hx => variation_eq_of_signs L _ x hx)⟩

theorem all_roots_count_for_chain : AllRootsCountForChain := by
  intro f s L hf hroots hL
  obtain ⟨ht, hb⟩ := infinity_variations L hL.2.2.2.1
  have hleft : ∀ᶠ x : ℝ in atBot, ∀ r ∈ realRoots f, x < r :=
    (Finset.eventually_all _).mpr (fun r _ => eventually_lt_atBot r)
  obtain ⟨a, ⟨haV, haR⟩, ha0⟩ := ((hb.and hleft).and (eventually_lt_atBot (0 : ℝ))).exists
  obtain ⟨b, ⟨hbV, hbR⟩, hb0⟩ := ((ht.and (roots_eventually_lt f)).and
    (eventually_gt_atTop (0 : ℝ))).exists
  have ha : s.eval a ≠ 0 := by
    intro ha
    have hamem := (mem_realRoots hf a).mpr ((hroots a).mp ha)
    exact lt_irrefl a (haR a hamem)
  have hb' : s.eval b ≠ 0 := by
    intro hb'
    have hbmem := (mem_realRoots hf b).mpr ((hroots b).mp hb')
    exact lt_irrefl b (hbR b hbmem)
  have hcount : rootCount f a b = (realRoots f).card := by
    unfold rootCount
    rw [Finset.filter_eq_self.mpr (fun r hr => ⟨haR r hr, hbR r hr⟩)]
  have h := interval_count_for_chain f s L hf hroots hL a b (ha0.trans hb0) ha hb'
  rwa [haV, hbV, hcount] at h

theorem sturm_theorem : Specs.D07.Ch19.SturmTheorem.SturmTheorem := by
  intro f hf d hd hdf hdf' hgreatest
  obtain ⟨_, hs, hroots, hsq, hgcd, _, _⟩ :=
    SturmChain.sturm_chain_for_monic_gcd f hf d hd hdf hdf' hgreatest
  have hL := SturmTheoremLocalSignVariation.canonical_chain (f / d) hs hsq hgcd
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  exact ⟨fun a b hab ha hb =>
    (interval_count_for_chain f (f / d) _ hf0 hroots hL a b hab ha hb).2,
    (all_roots_count_for_chain f (f / d) _ hf0 hroots hL).2⟩

theorem constant_root_count : ConstantRootCount := by
  intro c hc
  simp [realRoots, rootCount]

theorem cauchy_endpoints : CauchyEndpoints := by
  intro f hf
  let B : ℝ := 1 + (Specs.D07.Ch19.CauchyRootBound.normalizedCoefficientMaximum
    (f.map Complex.ofRealHom) : ℝ)
  change ∀ a b : ℝ, a ≤ -B → B ≤ b →
    f.eval a ≠ 0 ∧ f.eval b ≠ 0 ∧ rootCount f a b = (realRoots f).card
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  have hbound (x : ℝ) (hx : f.eval x = 0) : |x| < B := by
    have hmap : 0 < (f.map Complex.ofRealHom).natDegree := by simpa using hf
    have hroot : (f.map Complex.ofRealHom).IsRoot (x : ℂ) := by
      change (f.map Complex.ofRealHom).eval (Complex.ofRealHom x) = 0
      rw [Polynomial.eval_map_apply, hx, map_zero]
    have h := CauchyRootBound.rootBound _ hmap (x : ℂ) hroot
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  intro a b ha hb
  have hinside (x : ℝ) (hx : f.eval x = 0) : a < x ∧ x < b := by
    have h := abs_lt.mp (hbound x hx)
    exact ⟨ha.trans_lt h.1, h.2.trans_le hb⟩
  refine ⟨fun h => lt_irrefl a (hinside a h).1,
    fun h => lt_irrefl b (hinside b h).2, ?_⟩
  unfold rootCount
  rw [Finset.filter_eq_self.mpr (fun x hx => hinside x ((mem_realRoots hf0 x).mp hx))]

end D07.Ch19.SturmTheorem
