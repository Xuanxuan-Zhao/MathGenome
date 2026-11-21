import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Directed.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.CirculationDecomposition
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

open scoped BigOperators
universe u v w
namespace FiniteCombinatorics.Directed
namespace Circulation
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]
variable {G : Digraph V A}

private theorem prefix_to_vertex {x y t : V} (p : Walk G x y) (ht : t ∈ p.vertices) :
    ∃ q : Walk G x t, q.vertices.Sublist p.vertices ∧
      ∀ a ∈ q.arcs, a ∈ p.arcs := by
  induction p with
  | nil x =>
    simp only [Walk.vertices_nil, List.mem_singleton] at ht
    subst t
    exact ⟨Walk.nil x, List.Sublist.refl _, by simp⟩
  | @cons x y z a p ih =>
    simp only [Walk.vertices_cons, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨Walk.nil t, by simp, by simp⟩
    · obtain ⟨q, hq, hqa⟩ := ih ht
      exact ⟨Walk.cons a q, hq.cons_cons x, by
        intro b hb
        simp only [Walk.arcs_cons, List.mem_cons] at hb ⊢
        exact hb.imp_right (hqa b)⟩

private theorem vertices_append_single {x y z : V} (p : Walk G x y) (a : Arc G y z) :
    ((p.append (.cons a (.nil z))).vertices).dropLast = p.vertices := by
  rw [Walk.vertices_append]
  simp only [Walk.vertices_cons, Walk.vertices_nil]
  rw [List.dropLast_append_of_ne_nil (by simp)]
  simpa using List.dropLast_append_getLast? y (by rw [Walk.getLast_vertices]; simp)

/-- In the absence of a positive simple cycle, every positive walk is a path. -/
private theorem path_of_no_cycle (P : A → Prop)
    (hn : ¬ ∃ c : Cycle G, ∀ a ∈ c.2.val.arcs, P a)
    {x y : V} (p : Walk G x y) (hp : ∀ a ∈ p.arcs, P a) : p.IsPath := by
  induction p with
  | nil => exact Walk.nil_isPath _ _
  | @cons x y z a p ih =>
    have hp' : ∀ b ∈ p.arcs, P b := fun b hb => hp b (by simp [hb])
    have hpath : p.vertices.Nodup := ih hp'
    change (x :: p.vertices).Nodup
    refine List.nodup_cons.mpr ⟨?_, hpath⟩
    intro hx
    obtain ⟨q, hq, hqa⟩ := prefix_to_vertex p hx
    have hqc : (q.append (.cons a (.nil y))).IsCycle := by
      constructor
      · change 0 < (q.append (.cons a (.nil y))).length
        simp [Walk.length_append]
      · change ((q.append (.cons a (.nil y))).vertices).dropLast.Nodup
        rw [vertices_append_single]
        exact hq.nodup hpath
    apply hn
    refine ⟨⟨y, q.append (.cons a (.nil y)), hqc⟩, ?_⟩
    intro b hb
    simp only [Walk.arcs_append, Walk.arcs_cons, Walk.arcs_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | rfl
    · exact hp' b (hqa b hb)
    · exact hp a.val (by simp)

variable {R : Type w} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]

open scoped Classical in
/-- Conservation, expressed over any linearly ordered additive group. -/
def Balanced (G : Digraph V A) (f : A → R) : Prop :=
  ∀ x, (∑ a : A, if G.tail a = x then f a else 0) =
    ∑ a : A, if G.head a = x then f a else 0

private theorem positive_outgoing (f : A → R) (hf : ∀ a, 0 ≤ f a)
    (hb : Balanced G f) (a : A) (ha : 0 < f a) :
    ∃ b : A, G.tail b = G.head a ∧ 0 < f b := by
  classical
  by_contra hn
  have hz : ∀ b, (if G.tail b = G.head a then f b else 0) = 0 := by
    intro b
    split_ifs with h
    · have := not_lt.mp (fun hp => hn ⟨b, h, hp⟩)
      exact le_antisymm this (hf b)
    · rfl
  have hin : 0 < ∑ b : A, if G.head b = G.head a then f b else 0 := by
    exact lt_of_lt_of_le (by simpa using ha)
      (Finset.single_le_sum (fun b _ => by split_ifs <;> simp [hf]) (Finset.mem_univ a))
  have := hb (G.head a)
  simp only [hz, Finset.sum_const_zero] at this
  exact (ne_of_gt hin) this.symm

/-- Finite positive support with conservation contains a simple directed cycle. -/
theorem exists_positive_cycle (f : A → R) (hf : ∀ a, 0 ≤ f a)
    (hb : Balanced G f) (hpos : ∃ a, 0 < f a) :
    ∃ c : Cycle G, ∀ a ∈ c.2.val.arcs, 0 < f a := by
  classical
  by_contra hn
  obtain ⟨a, ha⟩ := hpos
  have hw : ∀ n : ℕ, ∃ x : V, ∃ b : A, ∃ p : Walk G x (G.head b),
      n < p.length ∧ (∀ d ∈ p.arcs, 0 < f d) ∧ 0 < f b := by
    intro n
    induction n with
    | zero => exact ⟨_, a, Walk.single G a, by simp, by simpa using ha, ha⟩
    | succ n ih =>
      obtain ⟨x, b, p, hlen, hp, hbpos⟩ := ih
      obtain ⟨c, hc, hcpos⟩ := positive_outgoing f hf hb b hbpos
      let e : Arc G (G.head b) (G.head c) := ⟨c, hc, rfl⟩
      refine ⟨x, c, p.append (.cons e (.nil _)), ?_, ?_, hcpos⟩
      · simp only [Walk.length_append, Walk.length_cons, Walk.length_nil]
        omega
      · intro d hd
        simp only [Walk.arcs_append, Walk.arcs_cons, Walk.arcs_nil,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
        exact hd.elim (hp d) (fun he => he ▸ hcpos)
  obtain ⟨x, b, p, hlen, hp, _⟩ := hw (Fintype.card V)
  have hpath : p.vertices.Nodup := path_of_no_cycle _ hn p hp
  have := hpath.length_le_card
  rw [Walk.length_vertices] at this
  omega

private theorem tails_eq_dropLast {x y : V} (p : Walk G x y) :
    p.arcs.map G.tail = p.vertices.dropLast := by
  induction p with
  | nil => rfl
  | @cons x y z a p ih =>
    obtain ⟨l, hl⟩ := Walk.vertices_eq_cons p
    simp only [Walk.arcs_cons, List.map_cons, Walk.vertices_cons, hl,
      List.dropLast_cons_cons] at *
    rw [a.property.1, ih]

/-- Vertex simplicity ensures each original arc is used at most once. -/
theorem cycle_arcs_nodup (c : Cycle G) : c.2.val.arcs.Nodup := by
  apply List.Nodup.of_map G.tail
  rw [tails_eq_dropLast]
  exact c.2.property.2

open scoped Classical in
omit [LinearOrder R] [IsOrderedAddMonoid R] in
private theorem sum_mem_list (l : List A) (hl : l.Nodup) (g : A → R) :
    (∑ a : A, if a ∈ l then g a else 0) = (l.map g).sum := by
  classical
  rw [← List.sum_toFinset g hl]
  calc
    _ = ∑ a ∈ l.toFinset, (if a ∈ l then g a else 0) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      simp only [List.mem_toFinset] at ha
      simp [ha]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact ite_eq_left (List.mem_toFinset.mp ha)

open scoped Classical in
omit [LinearOrder R] [IsOrderedAddMonoid R] in
private theorem walk_balance {x y : V} (p : Walk G x y) (r : R) (z : V) :
    (p.arcs.map (fun a => if G.tail a = z then r else 0)).sum -
      (p.arcs.map (fun a => if G.head a = z then r else 0)).sum =
    (if x = z then r else 0) - (if y = z then r else 0) := by
  classical
  induction p with
  | nil => simp
  | @cons x y t a p ih =>
    simp only [Walk.arcs_cons, List.map_cons, List.sum_cons, a.property.1, a.property.2]
    calc
      _ = (if x = z then r else 0) - (if y = z then r else 0) +
          ((p.arcs.map (fun a => if G.tail a = z then r else 0)).sum -
          (p.arcs.map (fun a => if G.head a = z then r else 0)).sum) := by abel
      _ = _ := by rw [ih]; abel

omit [LinearOrder R] [IsOrderedAddMonoid R] in
/-- A constant load around a simple cycle is balanced, including a loop. -/
theorem balanced_contribution (r : R) (c : Cycle G) :
    Balanced G (CirculationSpec.contribution r c) := by
  classical
  intro x
  have hs (P : A → Prop) [DecidablePred P] :
      (∑ a : A, if P a then CirculationSpec.contribution r c a else 0) =
      (c.2.val.arcs.map (fun a => if P a then r else 0)).sum := by
    rw [← sum_mem_list _ (cycle_arcs_nodup c)]
    apply Finset.sum_congr rfl
    intro a _
    simp only [CirculationSpec.contribution, Walk.arcs]
    split_ifs <;> rfl
  rw [hs, hs]
  exact sub_eq_zero.mp (by simpa using walk_balance c.2.val r x)

omit [LinearOrder R] [IsOrderedAddMonoid R] in
private theorem balanced_sub (f g : A → R) (hf : Balanced G f) (hg : Balanced G g) :
    Balanced G (fun a => f a - g a) := by
  classical
  intro x
  have hs (P : A → Prop) [DecidablePred P] :
      (∑ a : A, if P a then f a - g a else 0) =
      (∑ a : A, if P a then f a else 0) - ∑ a : A, if P a then g a else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [hs, hs, hf x, hg x]

/-- The support decreases at every minimum-weight cycle subtraction.
The argument works for both real and integer coefficients. -/
theorem decomposition (f : A → R) (hf : ∀ a, 0 ≤ f a) (hb : Balanced G f) :
    ∃ d : List (R × Spec.cycle G), CirculationSpec.Decomposes f d := by
  classical
  suffices aux : ∀ n : ℕ, ∀ f : A → R,
      (Finset.univ.filter (fun a => 0 < f a)).card = n →
      (∀ a, 0 ≤ f a) → Balanced G f →
      ∃ d : List (R × Spec.cycle G), CirculationSpec.Decomposes f d from
    aux _ f rfl hf hb
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hn hf hb
    by_cases hp : ∃ a, 0 < f a
    · obtain ⟨c, hc⟩ := exists_positive_cycle f hf hb hp
      have hne : c.2.val.arcs.toFinset.Nonempty := by
        have hlen : 0 < c.2.val.arcs.length := c.2.property.1
        cases he : c.2.val.arcs with
        | nil => simp [he] at hlen
        | cons a l => exact ⟨a, by simp⟩
      obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image c.2.val.arcs.toFinset f hne
      have hm : 0 < f a₀ := hc a₀ (List.mem_toFinset.mp ha₀)
      let g : A → R := fun a => f a - CirculationSpec.contribution (f a₀) c a
      have hg : ∀ a, 0 ≤ g a := by
        intro a
        dsimp [g, CirculationSpec.contribution]
        split_ifs with ha
        · exact sub_nonneg.mpr (hmin a (List.mem_toFinset.mpr ha))
        · simpa using hf a
      have hgb : Balanced G g := balanced_sub f _ hb (balanced_contribution _ c)
      have hsub : Finset.univ.filter (fun a => 0 < g a) ⊂
          Finset.univ.filter (fun a => 0 < f a) := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨?_, ?_⟩
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          have hle : g a ≤ f a := by
            dsimp [g, CirculationSpec.contribution]
            split_ifs
            · exact sub_le_self _ hm.le
            · simp
          exact lt_of_lt_of_le ha hle
        · intro he
          have hga : a₀ ∈ Finset.univ.filter (fun a => 0 < g a) := by
            rw [he]
            simp [hm]
          have hzero : g a₀ = 0 := by
            have ha₀' : a₀ ∈ Spec.arcs c.2.val := List.mem_toFinset.mp ha₀
            simp [g, CirculationSpec.contribution, ha₀']
          simp [hzero] at hga
      have hlt : (Finset.univ.filter (fun a => 0 < g a)).card < n := by
        rw [← hn]
        exact Finset.card_lt_card hsub
      obtain ⟨d, hdpos, hd⟩ := ih _ hlt g rfl hg hgb
      refine ⟨(f a₀, c) :: d, ?_, ?_⟩
      · intro t ht
        simp only [List.mem_cons] at ht
        exact ht.elim (fun he => he ▸ hm) (hdpos t)
      · intro a
        simp only [List.map_cons, List.sum_cons]
        have := hd a
        dsimp [g] at this
        exact (sub_eq_iff_eq_add.mp this).trans (add_comm _ _)
    · refine ⟨[], by simp, ?_⟩
      intro a
      simp only [List.map_nil, List.sum_nil]
      exact le_antisymm (not_lt.mp (fun h => hp ⟨a, h⟩)) (hf a)

end Circulation

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- Every nonnegative real circulation is a finite sum of positively weighted
simple directed cycles, with equality on each original arc (W47). -/
theorem circulation_decomposition (G : Digraph V A) (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hb : ∀ x, G.divergence f x = 0) :
    ∃ d : List (ℝ × Spec.cycle G), CirculationSpec.Decomposes f d := by
  apply Circulation.decomposition f hf
  intro x
  exact sub_eq_zero.mp (by simpa only [G.divergence_eq] using hb x)

/-- Integral loads admit positive integer cycle coefficients, without changing
the graph or losing any original arc coordinate (W47). -/
theorem integer_circulation_decomposition (G : Digraph V A) (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hb : ∀ x, G.divergence f x = 0)
    (hint : ∀ a, ∃ z : ℤ, (z : ℝ) = f a) :
    ∃ d : List (ℤ × Spec.cycle G),
      (∀ t ∈ d, 0 < t.1) ∧
      ∀ a, f a = ((d.map fun t => CirculationSpec.contribution t.1 t.2 a).sum : ℤ) := by
  classical
  choose z hz using hint
  have hzpos : ∀ a, 0 ≤ z a := by
    intro a
    have : (0 : ℝ) ≤ (z a : ℝ) := by rw [hz]; exact hf a
    exact_mod_cast this
  have hzb : Circulation.Balanced G z := by
    intro x
    have hr := sub_eq_zero.mp (by simpa only [G.divergence_eq] using hb x)
    have hzreal : (∑ a : A, if G.tail a = x then (z a : ℝ) else 0) =
        ∑ a : A, if G.head a = x then (z a : ℝ) else 0 := by
      simpa only [hz] using hr
    exact_mod_cast hzreal
  obtain ⟨d, hpos, hd⟩ := Circulation.decomposition z hzpos hzb
  refine ⟨d, hpos, ?_⟩
  intro a
  rw [← hz a]
  exact_mod_cast hd a

/-- The zero circulation is represented by the empty family, even on an empty
vertex or arc type. -/
theorem zero_circulation_decomposition (G : Digraph V A) :
    CirculationSpec.Decomposes (G := G) (fun _ => (0 : ℝ)) [] := by
  constructor <;> simp

end FiniteCombinatorics.Directed
