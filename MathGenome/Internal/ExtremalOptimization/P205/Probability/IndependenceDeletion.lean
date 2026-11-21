import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.IndependenceDeletion
import MathGenome.Internal.ExtremalOptimization.P205.Probability.Alteration
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

open scoped BigOperators Classical

namespace P205.Probability.IndependenceDeletion

variable {V : Type*} [Fintype V]

/-- One vertex is kept with probability `p`. Zero weights at the endpoints
of the probability interval are allowed. -/
noncomputable def bernoulli (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FiniteModel Bool where
  weight b := if b then p else 1 - p
  weight_nonneg b := by cases b <;> simp [hp, sub_nonneg.mpr hp1]
  weight_sum := by simp

/-- Independent choices for all vertices, using the canonical finite product. -/
noncomputable def retention (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FiniteModel (V → Bool) :=
  FiniteModel.pi (fun _ => bernoulli p hp hp1)

/-- A simultaneous retention event factors over the independent coordinates. -/
lemma retention_event (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : Finset V) :
    (retention p hp hp1).expectation
      (fun ω => if ∀ v ∈ s, ω v = true then 1 else 0) = p ^ s.card := by
  classical
  have hprod (ω : V → Bool) :
      (if ∀ v ∈ s, ω v = true then (1 : ℝ) else 0) =
        ∏ v, if v ∈ s → ω v = true then (1 : ℝ) else 0 := by
    rw [Fintype.prod_boole]
  simp_rw [hprod]
  unfold FiniteModel.expectation retention FiniteModel.pi bernoulli
  simp only
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (v : V) (b : Bool) =>
    (if b then p else 1 - p) * (if v ∈ s → b = true then (1 : ℝ) else 0))]
  have hsum (v : V) :
      (∑ b : Bool, (if b then p else 1 - p) *
        (if v ∈ s → b = true then (1 : ℝ) else 0)) =
          if v ∈ s then p else 1 := by
    by_cases hv : v ∈ s <;> simp [hv]
  simp_rw [hsum]
  rw [← Finset.prod_filter]
  simp

/-- The retained vertices and their originally retained edges. -/
noncomputable def sample (ω : V → Bool) : Finset V :=
  Finset.univ.filter (fun v => ω v = true)

noncomputable def defects (G : SimpleGraph V) (ω : V → Bool) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e.toFinset, ω v = true)

/-- Delete a fixed chosen endpoint of every original defect. Different edges
may charge the same deleted vertex, which can only improve the size bound. -/
noncomputable def repair (G : SimpleGraph V) (ω : V → Bool) : Finset V :=
  sample ω \ (defects G ω).image (fun e => e.out.1)

lemma repair_subset (G : SimpleGraph V) (ω : V → Bool) :
    repair G ω ⊆ sample ω := Finset.sdiff_subset

lemma repair_removed (G : SimpleGraph V) (ω : V → Bool) :
    ((sample ω) \ repair G ω).card ≤ (defects G ω).card := by
  apply le_trans (Finset.card_le_card (show
    sample ω \ repair G ω ⊆ (defects G ω).image (fun e => e.out.1) from ?_))
    (Finset.card_image_le)
  intro v hv
  simp only [repair, Finset.mem_sdiff, not_and, not_not] at hv
  exact hv.2 hv.1

lemma repair_independent (G : SimpleGraph V) (ω : V → Bool) :
    G.IsIndepSet (repair G ω : Set V) := by
  intro u hu v hv huv hadj
  have hu' := Finset.mem_sdiff.mp hu
  have hv' := Finset.mem_sdiff.mp hv
  have he : s(u, v) ∈ defects G ω := by
    simp only [defects, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq]
    exact ⟨hadj, fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact (Finset.mem_filter.mp hu'.1).2
      · have : w = v := Finset.mem_singleton.mp hw
        subst w
        exact (Finset.mem_filter.mp hv'.1).2⟩
  have hout := Sym2.out_fst_mem s(u, v)
  have himage : (s(u, v)).out.1 ∈ (defects G ω).image (fun e => e.out.1) :=
    Finset.mem_image.mpr ⟨s(u, v), he, rfl⟩
  rcases Sym2.mem_iff.mp hout with h | h
  · exact hu'.2 (h ▸ himage)
  · exact hv'.2 (h ▸ himage)

lemma expected_sample_card (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (retention p hp hp1).expectation (fun ω : V → Bool => ((sample ω).card : ℝ)) =
      p * (Fintype.card V : ℝ) := by
  have hcard (ω : V → Bool) : ((sample ω).card : ℝ) =
      ∑ v : V, if ω v = true then (1 : ℝ) else 0 := by
    simp [sample]
  simp_rw [hcard]
  rw [FiniteModel.expectation_sum]
  have hvert (v : V) :
      (retention p hp hp1).expectation (fun ω => if ω v = true then 1 else 0) = p := by
    simpa using retention_event p hp hp1 ({v} : Finset V)
  simp_rw [hvert]
  simp [mul_comm]

lemma expected_defects_card (G : SimpleGraph V) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (retention p hp hp1).expectation (fun ω => ((defects G ω).card : ℝ)) =
      p ^ 2 * (G.edgeFinset.card : ℝ) := by
  have hcard (ω : V → Bool) : ((defects G ω).card : ℝ) =
      ∑ e ∈ G.edgeFinset, if ∀ v ∈ e.toFinset, ω v = true then (1 : ℝ) else 0 := by
    simp [defects]
  simp_rw [hcard]
  rw [FiniteModel.expectation_sum]
  have hedge (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      (retention p hp hp1).expectation
        (fun ω => if ∀ v ∈ e.toFinset, ω v = true then 1 else 0) = p ^ 2 := by
    rw [retention_event, Sym2.card_toFinset_of_not_isDiag e
      (G.not_isDiag_of_mem_edgeFinset he)]
  rw [Finset.sum_congr rfl hedge]
  simp [mul_comm]

/-- Corollary 4.5: independent retention followed by endpoint deletion. -/
theorem independence_bound (G : SimpleGraph V) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (Fintype.card V : ℝ) - p ^ 2 * (G.edgeFinset.card : ℝ) ≤
      (G.indepNum : ℝ) := by
  let M : FiniteModel (V → Bool) := retention p hp hp1
  obtain ⟨ω, hclear, hsize⟩ := M.finite_set_alteration sample
    (fun ω => (defects G ω).card) (fun s => G.IsIndepSet (s : Set V))
    (fun ω => repair G ω.val)
    (fun ω => repair_subset G ω.val)
    (fun ω => repair_removed G ω.val)
    (fun ω => repair_independent G ω.val)
  have hexpect : M.expectation
      (fun ω => ((sample ω).card : ℝ) - ((defects G ω).card : ℝ)) =
      p * (Fintype.card V : ℝ) - p ^ 2 * (G.edgeFinset.card : ℝ) := by
    have hlin := M.expectation_linear 1 (-1)
      (fun ω => ((sample ω).card : ℝ)) (fun ω => ((defects G ω).card : ℝ))
    simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg,
      expected_sample_card, expected_defects_card, M] using hlin
  rw [hexpect] at hsize
  exact hsize.trans (by exact_mod_cast hclear.card_le_indepNum)

end P205.Probability.IndependenceDeletion
