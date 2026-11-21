import MathGenome.Internal.ExtremalOptimization.Specs.P205.Extremal.CliqueBlowups
import MathGenome.Internal.ExtremalOptimization.P205.Extremal.CliqueDensity
import MathGenome.Internal.ExtremalOptimization.P205.Extremal.TransversalDensity
import Mathlib.Data.Fintype.EquivFin

namespace P205.Extremal
open SimpleGraph Finset

/-- Ordered cliques, with the positions retaining their part indices. -/
def cliqueTuples {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) : Finset (Fin r → V) :=
  univ.filter fun x => ∀ i j, i ≠ j → G.Adj (x i) (x j)

/-- Forgetting the ordering maps the ordered cliques onto the clique subsets. -/
lemma card_cliqueFinset_le_cliqueTuples {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) :
    (G.cliqueFinset r).card ≤ (cliqueTuples G r).card := by
  classical
  apply card_le_card_of_surjOn (fun x : Fin r → V => univ.image x)
  intro s hs
  have hs' := mem_cliqueFinset_iff.mp hs
  let e : s ≃ Fin r := s.equivFinOfCardEq hs'.card_eq
  let x : Fin r → V := fun i => (e.symm i).val
  have hx : Function.Injective x := Subtype.val_injective.comp e.symm.injective
  refine ⟨x, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
  · intro i j hij
    exact hs'.isClique (e.symm i).prop (e.symm j).prop (hx.ne hij)
  · ext v
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).prop
    · intro hv
      exact ⟨e ⟨v, hv⟩, by simp [x]⟩

/-- A product consisting of ordered cliques gives all cross-part edges.
The tuple lemma allows overlapping input sets. Thus we can apply it directly
to ordered cliques, and obtain disjoint parts afterwards from irreflexivity,
without the preliminary random partition used in the paper. -/
lemma complete_between_of_clique_box {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {r t : ℕ} (ht : 1 ≤ t)
    (T : Fin r → Finset V) (hT : ∀ i, (T i).card = t)
    (hbox : ∀ x : Fin r → V, (∀ i, x i ∈ T i) →
      ∀ i j, i ≠ j → G.Adj (x i) (x j)) :
    ∀ i j, i ≠ j → ∀ v ∈ T i, ∀ w ∈ T j, G.Adj v w := by
  classical
  have hne (i : Fin r) : (T i).Nonempty := card_pos.mp (by rw [hT]; omega)
  choose a ha using hne
  intro i j hij v hv w hw
  let x : Fin r → V := fun k => if k = i then v else if k = j then w else a k
  have hx : ∀ k, x k ∈ T k := by
    intro k
    dsimp [x]
    split_ifs with hki hkj
    · simpa [hki] using hv
    · simpa [hkj] using hw
    · exact ha k
  simpa [x, hij, hij.symm] using hbox x hx i j hij

/-- The parts extracted from a clique box are disjoint and produce an injective
homomorphism from the canonical complete equipartite graph. -/
lemma copy_of_complete_parts {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {r t : ℕ}
    (T : Fin r → Finset V) (hT : ∀ i, (T i).card = t)
    (hcross : ∀ i j, i ≠ j → ∀ v ∈ T i, ∀ w ∈ T j, G.Adj v w) :
    Nonempty (Copy (completeEquipartiteGraph r t) G) := by
  classical
  let e (i : Fin r) : T i ≃ Fin t := (T i).equivFinOfCardEq (hT i)
  let f : Fin r × Fin t → V := fun p => ((e p.1).symm p.2).val
  have hf (i j : Fin r) (hij : i ≠ j) (a b : Fin t) :
      G.Adj (f (i, a)) (f (j, b)) :=
    hcross i j hij _ ((e i).symm a).prop _ ((e j).symm b).prop
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro p q hpq
    exact hf p.1 q.1 hpq p.2 q.2
  · rintro ⟨i, a⟩ ⟨j, b⟩ hab
    by_cases hij : i = j
    · subst j
      have heq : (e i).symm a = (e i).symm b := Subtype.ext hab
      have : a = b := (e i).symm.injective heq
      subst b
      rfl
    · exact False.elim ((hf i j hij a b).ne hab)

/-- W03: clique blow-ups above the edge-density Turán threshold. -/
theorem clique_blowups : CliqueBlowupsSpecs.blowupsStatement := by
  classical
  intro r t hr ht ε hε
  obtain ⟨c, hc, N₁, hN₁⟩ := clique_supersaturation r hr ε hε
  let d : ℝ := min c 1
  have hd : 0 < d := lt_min hc (by norm_num)
  have hd1 : d ≤ 1 := min_le_right _ _
  obtain ⟨N₂, hN₂⟩ := transversal_density r t (by omega) ht d hd hd1
  refine ⟨max N₁ N₂, ?_⟩
  intro V _ _ G _ hn he
  have hcount := hN₁ G ((le_max_left _ _).trans hn) he
  have htuples : d * (Fintype.card V : ℝ) ^ r ≤ (cliqueTuples G r).card := by
    calc
      _ ≤ c * (Fintype.card V : ℝ) ^ r :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (G.cliqueFinset r).card := hcount
      _ ≤ (cliqueTuples G r).card := by
        exact_mod_cast card_cliqueFinset_le_cliqueTuples G r
  obtain ⟨T, hT, hbox⟩ := hN₂ (Fintype.card V) ((le_max_right _ _).trans hn)
    V (fun _ => univ) (cliqueTuples G r) (fun _ => by simp)
    (fun _ _ _ => mem_univ _) htuples
  apply copy_of_complete_parts G T (fun i => (hT i).2)
  apply complete_between_of_clique_box G ht T (fun i => (hT i).2)
  intro x hx
  exact (mem_filter.mp (hbox x hx)).2

end P205.Extremal
