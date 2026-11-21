import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.CirculationDecomposition
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.PathCycleDecomposition
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Linarith

open scoped BigOperators
universe u v w
namespace FiniteCombinatorics.Graph.Flows
open FiniteCombinatorics.Directed
namespace PathCycle
open private path_of_no_cycle tails_eq_dropLast sum_mem_list walk_balance
  from MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.CirculationDecomposition
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]
variable {G : Digraph V A} {s t : V}
variable {R : Type w} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

open scoped Classical in
/-- Boundary of a nonnegative load with oriented value r. -/
def Boundary (G : Digraph V A) (f : A → R) (s t : V) (r : R) : Prop :=
  ∀ x, (∑ a : A, if G.tail a = x then f a else 0) -
    (∑ a : A, if G.head a = x then f a else 0) =
      (if s = x then r else 0) - (if t = x then r else 0)

private theorem path_arcs_nodup (p : Directed.Spec.path G s t) :
    p.val.arcs.Nodup := by
  apply List.Nodup.of_map G.tail
  rw [tails_eq_dropLast]
  exact p.property.sublist (List.dropLast_sublist _)

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem path_boundary (p : Directed.Spec.path G s t) (r : R) :
    Boundary G (PathCycleSpec.pathContribution r p) s t r := by
  classical
  intro x
  have hs (P : A → Prop) [DecidablePred P] :
      (∑ a : A, if P a then PathCycleSpec.pathContribution r p a else 0) =
      (p.val.arcs.map (fun a => if P a then r else 0)).sum := by
    rw [← sum_mem_list _ (path_arcs_nodup p)]
    apply Finset.sum_congr rfl
    intro a _
    simp only [PathCycleSpec.pathContribution, Walk.arcs]
    split_ifs <;> rfl
  rw [hs, hs]
  exact walk_balance p.val r x

private theorem boundary_sub (f g : A → R) (r q : R)
    (hf : Boundary G f s t r) (hg : Boundary G g s t q) :
    Boundary G (fun a => f a - g a) s t (r - q) := by
  classical
  intro x
  have hs (P : A → Prop) [DecidablePred P] :
      (∑ a : A, if P a then f a - g a else 0) =
      (∑ a : A, if P a then f a else 0) - ∑ a : A, if P a then g a else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [hs, hs]
  have hfx := hf x
  have hgx := hg x
  split_ifs at * <;> linarith

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem boundary_zero_iff (f : A → R) :
    Boundary G f s t 0 ↔ Circulation.Balanced G f := by
  classical
  simp only [Boundary, Circulation.Balanced, ite_self, sub_self, sub_eq_zero]

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem cycle_boundary (c : Directed.Spec.cycle G) (r : R) :
    Boundary G (CirculationSpec.contribution r c) s t 0 :=
  (boundary_zero_iff _).2 (Circulation.balanced_contribution r c)

/-- Without a positive cycle, positive source imbalance forces a positive path.
Conservation extends any unfinished positive walk. Finiteness precludes extending
past the vertex bound, since the absence of cycles makes every such walk simple. -/
private theorem exists_positive_path (f : A → R) (hf : ∀ a, 0 ≤ f a)
    (hst : s ≠ t) (r : R) (hr : 0 < r) (hb : Boundary G f s t r)
    (hn : ¬ ∃ c : Cycle G, ∀ a ∈ c.2.val.arcs, 0 < f a) :
    ∃ p : Directed.Spec.path G s t, ∀ a ∈ p.val.arcs, 0 < f a := by
  classical
  have hout (x : V) (hxt : x ≠ t)
      (hin : x = s ∨ ∃ a : A, G.head a = x ∧ 0 < f a) :
      ∃ b : A, G.tail b = x ∧ 0 < f b := by
    have hbx := hb x
    have hnonneg : 0 ≤ ∑ a : A, if G.head a = x then f a else 0 :=
      Finset.sum_nonneg (fun a _ => by split_ifs <;> simp [hf])
    have hsum : 0 < ∑ a : A, if G.tail a = x then f a else 0 := by
      rcases hin with rfl | ⟨a, ha, hap⟩
      · simp only [ite_true, ite_eq_right hst.symm, sub_zero] at hbx
        linarith
      · have hpos : 0 < ∑ b : A, if G.head b = x then f b else 0 :=
          lt_of_lt_of_le (by simpa [ha] using hap)
            (Finset.single_le_sum (fun b _ => by split_ifs <;> simp [hf])
              (Finset.mem_univ a))
        have : 0 ≤ (if s = x then r else 0) := by split_ifs <;> positivity
        simp only [ite_eq_right hxt.symm, sub_zero] at hbx
        linarith
    by_contra hn
    have hz : ∀ a : A, (if G.tail a = x then f a else 0) ≤ 0 := by
      intro a
      split_ifs with ha
      · exact not_lt.mp (fun h => hn ⟨a, ha, h⟩)
      · exact le_refl 0
    exact (not_le.mpr hsum) (Finset.sum_nonpos (fun a _ => hz a))
  by_contra hp
  have not_end {x : V} (p : Walk G s x) (hpa : ∀ a ∈ p.arcs, 0 < f a) : x ≠ t := by
    intro he
    subst x
    exact hp ⟨⟨p, path_of_no_cycle _ hn p hpa⟩, hpa⟩
  have hw : ∀ n : ℕ, ∃ x : V, ∃ p : Walk G s x,
      n < p.length ∧ (∀ a ∈ p.arcs, 0 < f a) ∧
      ∃ a : A, G.head a = x ∧ 0 < f a := by
    intro n
    induction n with
    | zero =>
      obtain ⟨a, ha, hap⟩ := hout s hst (Or.inl rfl)
      let e : Arc G s (G.head a) := ⟨a, ha, rfl⟩
      refine ⟨G.head a, .cons e (.nil _), by simp, ?_, a, rfl, hap⟩
      simpa using hap
    | succ n ih =>
      obtain ⟨x, p, hlen, hpa, hin⟩ := ih
      obtain ⟨a, ha, hap⟩ := hout x (not_end p hpa) (Or.inr hin)
      let e : Arc G x (G.head a) := ⟨a, ha, rfl⟩
      refine ⟨G.head a, p.append (.cons e (.nil _)), ?_, ?_, a, rfl, hap⟩
      · simp only [Walk.length_append, Walk.length_cons, Walk.length_nil]
        omega
      · intro b hb
        simp only [Walk.arcs_append, Walk.arcs_cons, Walk.arcs_nil,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
        exact hb.elim (hpa b) (fun he => he ▸ hap)
  obtain ⟨x, p, hlen, hpa, _⟩ := hw (Fintype.card V)
  have hpath : p.vertices.Nodup := path_of_no_cycle _ hn p hpa
  have := hpath.length_le_card
  rw [Walk.length_vertices] at this
  omega

open scoped Classical in
omit [Fintype A] in
private theorem residual_nonneg (f : A → R) (hf : ∀ a, 0 ≤ f a)
    (l : List A) (w : R) (hw : ∀ a ∈ l, w ≤ f a) :
    ∀ a, 0 ≤ f a - (if a ∈ l then w else 0) := by
  intro a
  split_ifs with ha
  · exact sub_nonneg.mpr (hw a ha)
  · simpa using hf a

open scoped Classical in
private theorem support_decreases (f : A → R) (l : List A) (w : R)
    (hw : 0 < w) (a₀ : A) (ha₀ : a₀ ∈ l) (heq : f a₀ = w) :
    (Finset.univ.filter (fun a => 0 < f a - (if a ∈ l then w else 0))).card <
      (Finset.univ.filter (fun a => 0 < f a)).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    split_ifs at ha <;> linarith
  · intro he
    have ha : a₀ ∈ Finset.univ.filter (fun a => 0 < f a -
        (if a ∈ l then w else 0)) := by
      rw [he]
      simp [heq, hw]
    simp [ha₀, heq] at ha

private theorem zero_boundary_decomposition (f : A → R)
    (hf : ∀ a, 0 ≤ f a) (hb : Boundary G f s t 0) :
    ∃ ps cs, PathCycleSpec.Decomposes (G := G) (s := s) (t := t) f 0 ps cs := by
  obtain ⟨cs, hcs, hload⟩ := Circulation.decomposition f hf ((boundary_zero_iff f).1 hb)
  exact ⟨[], cs, by simpa [PathCycleSpec.Decomposes] using And.intro hcs hload⟩

/-- Support induction, over both real and integer weights. Each cycle subtraction
kills an arc. For a path, subtract the lesser of the remaining value and the
minimum arc load: either an arc disappears, or the remainder is a circulation. -/
theorem decomposition (f : A → R) (hf : ∀ a, 0 ≤ f a) (hst : s ≠ t)
    (r : R) (hr : 0 ≤ r) (hb : Boundary G f s t r) :
    ∃ ps cs, PathCycleSpec.Decomposes (G := G) (s := s) (t := t) f r ps cs := by
  classical
  suffices aux : ∀ n : ℕ, ∀ (f : A → R) (r : R),
      (Finset.univ.filter (fun a => 0 < f a)).card = n →
      (∀ a, 0 ≤ f a) → 0 ≤ r → Boundary G f s t r →
      ∃ ps cs, PathCycleSpec.Decomposes (G := G) (s := s) (t := t) f r ps cs from
    aux _ f r rfl hf hr hb
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f r hn hf hr hb
    by_cases hz : r = 0
    · subst r
      exact zero_boundary_decomposition f hf hb
    have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    by_cases hc : ∃ c : Cycle G, ∀ a ∈ c.2.val.arcs, 0 < f a
    · obtain ⟨c, hc⟩ := hc
      have hne : c.2.val.arcs.toFinset.Nonempty := by
        have hlen : 0 < c.2.val.arcs.length := c.2.property.1
        cases he : c.2.val.arcs with
        | nil => simp [he] at hlen
        | cons a l => exact ⟨a, by simp⟩
      obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image c.2.val.arcs.toFinset f hne
      have hm : 0 < f a₀ := hc a₀ (List.mem_toFinset.mp ha₀)
      let g : A → R := fun a => f a - CirculationSpec.contribution (f a₀) c a
      have hg : ∀ a, 0 ≤ g a :=
        residual_nonneg f hf c.2.val.arcs (f a₀)
          (fun a ha => hmin a (List.mem_toFinset.mpr ha))
      have hgb : Boundary G g s t r := by
        simpa using boundary_sub f _ r 0 hb (cycle_boundary c (f a₀))
      have hlt : (Finset.univ.filter (fun a => 0 < g a)).card < n := by
        rw [← hn]
        exact support_decreases f c.2.val.arcs (f a₀) hm a₀
          (List.mem_toFinset.mp ha₀) rfl
      obtain ⟨ps, cs, hps, hcs, hsum, hload⟩ := ih _ hlt g r rfl hg hr hgb
      refine ⟨ps, (f a₀, c) :: cs, hps, ?_, hsum, ?_⟩
      · intro q hq
        simp only [List.mem_cons] at hq
        exact hq.elim (fun he => he ▸ hm) (hcs q)
      · intro a
        have ha := hload a
        change f a - CirculationSpec.contribution (f a₀) c a = _ at ha
        simp only [List.map_cons, List.sum_cons]
        linarith [ha]
    · obtain ⟨p, hp⟩ := exists_positive_path f hf hst r hrpos hb hc
      have hne : p.val.arcs.toFinset.Nonempty := by
        cases he : p.val with
        | nil x => exact (hst rfl).elim
        | cons a q => exact ⟨a.val, by simp⟩
      obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image p.val.arcs.toFinset f hne
      have hm : 0 < f a₀ := hp a₀ (List.mem_toFinset.mp ha₀)
      let w : R := min r (f a₀)
      have hw : 0 < w := lt_min hrpos hm
      have hwr : w ≤ r := min_le_left _ _
      have hwm : w ≤ f a₀ := min_le_right _ _
      let g : A → R := fun a => f a - PathCycleSpec.pathContribution w p a
      have hg : ∀ a, 0 ≤ g a :=
        residual_nonneg f hf p.val.arcs w
          (fun a ha => hwm.trans (hmin a (List.mem_toFinset.mpr ha)))
      have hgb : Boundary G g s t (r - w) :=
        boundary_sub f _ r w hb (path_boundary p w)
      have hrest : ∃ ps cs,
          PathCycleSpec.Decomposes (G := G) (s := s) (t := t) g (r - w) ps cs := by
        by_cases hle : r ≤ f a₀
        · have he : r - w = 0 := by simp [w, min_eq_left hle]
          rw [he] at hgb ⊢
          exact zero_boundary_decomposition g hg hgb
        · have hwmin : w = f a₀ := min_eq_right (le_of_not_ge hle)
          have hlt : (Finset.univ.filter (fun a => 0 < g a)).card < n := by
            rw [← hn]
            exact support_decreases f p.val.arcs w hw a₀
              (List.mem_toFinset.mp ha₀) hwmin.symm
          exact ih _ hlt g (r - w) rfl hg (sub_nonneg.mpr hwr) hgb
      obtain ⟨ps, cs, hps, hcs, hsum, hload⟩ := hrest
      refine ⟨(w, p) :: ps, cs, ?_, hcs, ?_, ?_⟩
      · intro q hq
        simp only [List.mem_cons] at hq
        exact hq.elim (fun he => he ▸ hw) (hps q)
      · simp only [List.map_cons, List.sum_cons]
        rw [hsum]
        abel
      · intro a
        have ha := hload a
        change f a - PathCycleSpec.pathContribution w p a = _ at ha
        simp only [List.map_cons, List.sum_cons]
        linarith [ha]

/-- Interchanging the two endpoints changes the sign of the value. -/
theorem Boundary.swap {f : A → R} {r : R} (hb : Boundary G f s t r) :
    Boundary G f t s (-r) := by
  classical
  intro x
  have hbx := hb x
  split_ifs at * <;> linarith

private theorem network_boundary (N : Network V A) (f : A → ℝ) (hf : N.Feasible f) :
    Boundary N.graph f N.source N.sink (N.value f) := by
  classical
  intro x
  rw [← Digraph.divergence_eq]
  by_cases hs : N.source = x
  · subst x
    simp [N.source_ne_sink.symm]
  · by_cases ht : N.sink = x
    · subst x
      simp [hs, N.sink_divergence f hf]
    · simp only [ite_eq_right hs, ite_eq_right ht, sub_self]
      exact hf.2 x (Ne.symm hs) (Ne.symm ht)

end PathCycle

/-- W47, all three signs of the value; each original arc coordinate is preserved. -/
theorem flow_path_cycle_decomposition : PathCycleSpec.real_decomposition.{u,v} := by
  intro V A _ _ N f hf
  have hb := PathCycle.network_boundary N f hf
  refine ⟨?_, ?_, ?_⟩
  · intro hpos
    exact PathCycle.decomposition f (fun a => (hf.1 a).1) N.source_ne_sink
      (N.value f) hpos.le hb
  · intro hz
    change N.value f = 0 at hz
    rw [hz] at hb
    exact Circulation.decomposition f (fun a => (hf.1 a).1)
      ((PathCycle.boundary_zero_iff f).1 hb)
  · intro hneg
    exact PathCycle.decomposition f (fun a => (hf.1 a).1) N.source_ne_sink.symm
      (-N.value f) (neg_nonneg.mpr hneg.le) hb.swap

namespace PathCycle
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- Casting integer load sums commutes with the boundary equation. -/
private theorem integer_boundary (N : Network V A) (f : A → ℝ) (hf : N.Feasible f)
    (z : A → ℤ) (hz : ∀ a, (z a : ℝ) = f a) :
    ∃ q : ℤ, (q : ℝ) = N.value f ∧ Boundary N.graph z N.source N.sink q := by
  classical
  let q : ℤ := (∑ a : A, if N.graph.tail a = N.source then z a else 0) -
    ∑ a : A, if N.graph.head a = N.source then z a else 0
  have hq : (q : ℝ) = N.value f := by
    rw [N.value_eq, Digraph.divergence_eq]
    simp [q, hz]
  refine ⟨q, hq, ?_⟩
  intro x
  have hb := network_boundary N f hf x
  have hb' : (∑ a : A, if N.graph.tail a = x then (z a : ℝ) else 0) -
      (∑ a : A, if N.graph.head a = x then (z a : ℝ) else 0) =
      (if N.source = x then (q : ℝ) else 0) - (if N.sink = x then (q : ℝ) else 0) := by
    simpa only [hq, hz] using hb
  exact_mod_cast hb'

private theorem integral_of_decomposes {G : Digraph V A} {s t : V}
    (f : A → ℝ) (z : A → ℤ) (hz : ∀ a, (z a : ℝ) = f a)
    (r : ℝ) (q : ℤ) (hq : (q : ℝ) = r)
    (ps : List (ℤ × Directed.Spec.path G s t))
    (cs : List (ℤ × Directed.Spec.cycle G))
    (hd : PathCycleSpec.Decomposes z q ps cs) :
    PathCycleSpec.IntegralDecomposes f r ps cs := by
  refine ⟨hd.1, hd.2.1, ?_, ?_⟩
  · rw [hd.2.2.1, hq]
  · intro a
    rw [← hz a, hd.2.2.2 a]
end PathCycle

/-- W47 for integral loads: positive integer coefficients for paths and cycles,
with the same signed cases and exact original real loads. -/
theorem integer_flow_path_cycle_decomposition :
    PathCycleSpec.integer_decomposition.{u,v} := by
  intro V A _ _ N f hf hint
  classical
  choose z hz using hint
  have hzpos : ∀ a, 0 ≤ z a := by
    intro a
    have hr : (0 : ℝ) ≤ (z a : ℝ) := by rw [hz]; exact (hf.1 a).1
    exact_mod_cast hr
  obtain ⟨q, hq, hb⟩ := PathCycle.integer_boundary N f hf z hz
  refine ⟨?_, ?_, ?_⟩
  · intro hpos
    have hqp : 0 ≤ q := by
      have : (0 : ℝ) ≤ (q : ℝ) := by rw [hq]; exact hpos.le
      exact_mod_cast this
    obtain ⟨ps, cs, hd⟩ := PathCycle.decomposition z hzpos N.source_ne_sink q hqp hb
    exact ⟨ps, cs, PathCycle.integral_of_decomposes f z hz _ q hq ps cs hd⟩
  · intro hzero
    have hqz : q = 0 := by
      have : (q : ℝ) = 0 := hq.trans hzero
      exact_mod_cast this
    rw [hqz] at hb
    obtain ⟨cs, hpos, hload⟩ := Circulation.decomposition z hzpos
      ((PathCycle.boundary_zero_iff z).1 hb)
    refine ⟨cs, hpos, ?_⟩
    intro a
    rw [← hz a, hload a]
  · intro hneg
    have hqp : 0 ≤ -q := by
      have : (0 : ℝ) ≤ (-q : ℤ) := by
        push_cast
        rw [hq]
        exact neg_nonneg.mpr hneg.le
      exact_mod_cast this
    obtain ⟨ps, cs, hd⟩ := PathCycle.decomposition z hzpos N.source_ne_sink.symm
      (-q) hqp hb.swap
    refine ⟨ps, cs, PathCycle.integral_of_decomposes f z hz _ (-q) ?_ ps cs hd⟩
    change ((-q : ℤ) : ℝ) = -N.value f
    rw [Int.cast_neg, hq]
end FiniteCombinatorics.Graph.Flows
