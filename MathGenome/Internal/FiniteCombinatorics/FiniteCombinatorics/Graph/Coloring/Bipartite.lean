import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.Bipartite
import Lean.Elab.Tactic.Omega

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Coloring

open SimpleGraph

/-- Removing a repeated closed segment reduces a closed walk. Thus if all simple
cycles are even, strong induction proves that every closed walk is even. -/
theorem closed_walk_even_of_cycles_even {V : Type u} (G : SimpleGraph V)
    (hc : ∀ (a : V) (p : G.Walk a a), p.IsCycle → Even p.length)
    (a : V) (p : G.Walk a a) : Even p.length := by
  classical
  suffices h : ∀ n, ∀ (a : V) (p : G.Walk a a), p.length = n → Even p.length by
    exact h p.length a p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a p hn
    cases p with
    | nil => simp
    | @cons _ b _ hab q =>
      by_cases hq : q.IsPath
      · by_cases hl : 3 ≤ (q.cons hab).length
        · exact hc a (q.cons hab)
            (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by simpa using hq, hl⟩)
        · have hne : (q.cons hab).length ≠ 1 := by
            intro he
            exact G.irrefl (SimpleGraph.Walk.adj_of_length_eq_one he)
          have heq : (q.cons hab).length = 2 := by
            simp only [SimpleGraph.Walk.length_cons] at hne hl ⊢
            omega
          simp [heq]
      · obtain ⟨b', r, hr, hrnil⟩ :
            ∃ (b' : V) (r : G.Walk b' b'), r.IsSubwalk q ∧ ¬r.Nil := by
          simpa only [SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil, not_forall,
            Classical.not_imp, exists_prop] using hq
        obtain ⟨s, t, hst⟩ := hr
        have hlen : q.length = s.length + r.length + t.length := by
          rw [hst]
          simp
        have hrpos : 0 < r.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hrnil
        have her : Even r.length := ih r.length (by simp_all; omega) b' r rfl
        let rem := (s.append t).cons hab
        have hrem : rem.length < n := by
          dsimp [rem]
          simp only [SimpleGraph.Walk.length_append]
          simp only [SimpleGraph.Walk.length_cons] at hn
          omega
        have hem := ih rem.length hrem a rem rfl
        rw [even_iff_two_dvd] at her hem ⊢
        have : (q.cons hab).length = rem.length + r.length := by
          simp [rem]
          omega
        rw [this]
        exact dvd_add hem her

/-- A proper two-coloring switches color on every step. -/
theorem two_coloring_walk_parity {V : Type u} {G : SimpleGraph V}
    (c : G.Coloring (Fin 2)) {a b : V} (p : G.Walk a b) :
    ((c a).val + p.length) % 2 = (c b).val := by
  induction p with
  | nil => simp [Nat.mod_eq_of_lt (c _).isLt]
  | @cons a b d hab q ih =>
    have hne := c.valid hab
    have ha := (c a).isLt
    have hb := (c b).isLt
    have hd := (c d).isLt
    have hvals : (c a).val ≠ (c b).val := fun he => hne (Fin.ext he)
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- Color vertices by the parity of any chosen walk from a representative of
 their component. Evenness of all closed walks makes adjacent parities differ. -/
theorem bipartite_of_closed_walks_even {V : Type u} (G : SimpleGraph V)
    (h : ∀ (a : V) (p : G.Walk a a), Even p.length) : G.IsBipartite := by
  classical
  let root : G.ConnectedComponent → V := Quot.out
  have reach (v : V) : G.Reachable (root (G.connectedComponentMk v)) v :=
    SimpleGraph.ConnectedComponent.exact (Quot.out_eq _)
  let p (v : V) : G.Walk (root (G.connectedComponentMk v)) v := (reach v).some
  refine ⟨SimpleGraph.Coloring.mk (fun v => ⟨(p v).length % 2, Nat.mod_lt _ (by decide)⟩) ?_⟩
  intro a b hab heq
  have hr : root (G.connectedComponentMk a) = root (G.connectedComponentMk b) :=
    congrArg root (SimpleGraph.ConnectedComponent.sound hab.reachable)
  let q : G.Walk (root (G.connectedComponentMk a)) b := (p b).copy hr.symm rfl
  have heven := h _ (((p a).concat hab).append q.reverse)
  have heq' : (p a).length % 2 = (p b).length % 2 := congrArg Fin.val heq
  rw [even_iff_two_dvd] at heven
  simp only [q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_concat,
    SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_copy] at heven
  omega

/-- The contrapositive of the closed-walk induction. -/
theorem exists_odd_cycle_of_odd_closed_walk {V : Type u} (G : SimpleGraph V)
    (a : V) (p : G.Walk a a) (hp : Odd p.length) :
    ∃ (b : V) (c : G.Walk b b), c.IsCycle ∧ Odd c.length := by
  by_contra hn
  have hc : ∀ (b : V) (c : G.Walk b b), c.IsCycle → Even c.length := by
    intro b c hcyc
    apply Nat.not_odd_iff_even.mp
    intro ho
    exact hn ⟨b, c, hcyc, ho⟩
  exact (Nat.not_even_iff_odd.mpr hp) (closed_walk_even_of_cycles_even G hc a p)

/-- Apply the induction inside the graph traced by the walk, so the resulting
odd cycle uses only edges of that walk. -/
theorem odd_closed_walk_exists_odd_cycle :
    Specs.FiniteCombinatorics.Graph.Coloring.Bipartite.odd_closed_walk_exists_odd_cycleType := by
  intro V _ G a p hp
  let H := p.toSubgraph.spanningCoe
  have hedge (e : Sym2 V) : e ∈ H.edgeSet ↔ e ∈ p.edges := by
    induction e using Sym2.ind with
    | _ u v => exact p.adj_toSubgraph_iff_mem_edges
  let q : H.Walk a a := p.transfer H (fun e he => (hedge e).mpr he)
  have hq : Odd q.length := by simpa [q] using hp
  obtain ⟨b, c, hcycle, hodd⟩ := exists_odd_cycle_of_odd_closed_walk H a q hq
  let d := c.mapLe p.toSubgraph.spanningCoe_le
  refine ⟨b, ⟨d, hcycle.mapLe _⟩, ?_, ?_⟩
  · simpa [d] using hodd
  · intro e he
    apply (hedge e).mp
    apply c.edges_subset_edgeSet
    simpa [d] using he

theorem bipartite_iff_no_odd_cycle :
    Specs.FiniteCombinatorics.Graph.Coloring.Bipartite.bipartite_iff_no_odd_cycleType := by
  intro V _ G
  constructor
  · rintro ⟨c⟩ a p hp
    have h := two_coloring_walk_parity c p.val
    have hv := (c a).isLt
    have ho := hp
    rw [Nat.odd_iff] at ho
    omega
  · intro hc
    apply bipartite_of_closed_walks_even G
    intro a p
    apply Nat.not_odd_iff_even.mp
    intro hp
    obtain ⟨b, c, hodd, _⟩ := odd_closed_walk_exists_odd_cycle G a p hp
    exact hc b c hodd

theorem bipartite_two_coloring :
    Specs.FiniteCombinatorics.Graph.Coloring.Bipartite.bipartite_two_coloringType := by
  intro V _ G h
  exact h

theorem bipartite_chromaticNumber_le_two :
    Specs.FiniteCombinatorics.Graph.Coloring.Bipartite.bipartite_chromaticNumber_le_twoType := by
  intro V _ G h
  exact (chromaticNumber_minimum G).2 2 h

end FiniteCombinatorics.Graph.Coloring
