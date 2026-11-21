import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.NegativeCyclePotentials
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace P205.Networks

universe u v
variable {V : Type u} {E : Type v} {tail head : E → V} {cost : E → ℝ}

@[simp] theorem walkCost_nil : walkCost cost [] = 0 := rfl

@[simp] theorem walkCost_cons (e : E) (es : List E) :
    walkCost cost (e :: es) = cost e + walkCost cost es := rfl

@[simp] theorem walkCost_append (es fs : List E) :
    walkCost cost (es ++ fs) = walkCost cost es + walkCost cost fs := by
  simp [walkCost]

theorem isWalk_append {a b : V} (es fs : List E) :
    IsWalk tail head a (es ++ fs) b ↔
      ∃ c, IsWalk tail head a es c ∧ IsWalk tail head c fs b := by
  induction es generalizing a with
  | nil => simp [IsWalk]
  | cons e es ih =>
    simp only [List.cons_append, IsWalk, ih]
    constructor
    · rintro ⟨h, c, hc, hb⟩
      exact ⟨c, ⟨h, hc⟩, hb⟩
    · rintro ⟨c, ⟨h, hc⟩, hb⟩
      exact ⟨h, c, hc, hb⟩

/-- Repeated vertices among the tails identify two different edge positions. -/
theorem repeated_tail_split (es : List E) (h : ¬ (es.map tail).Nodup) :
    ∃ p e q f r, es = p ++ e :: (q ++ f :: r) ∧ tail e = tail f := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    by_cases hm : tail e ∈ es.map tail
    · obtain ⟨f, hf, he⟩ := List.mem_map.mp hm
      obtain ⟨q, r, hr⟩ := List.mem_iff_append.mp hf
      exact ⟨[], e, q, f, r, by simpa using congrArg (List.cons e) hr, he.symm⟩
    · have hn : ¬ (es.map tail).Nodup := by
        simpa [List.nodup_cons, hm] using h
      obtain ⟨p, f, q, g, r, hp, hfg⟩ := ih hn
      exact ⟨e :: p, f, q, g, r, by simp [hp], hfg⟩

/-- Splitting a repeated tail isolates a nonempty closed subwalk. There is
still an edge after that subwalk, so both pieces are strictly shorter. -/
theorem split_repeated_walk {a b : V} {es : List E}
    (hw : IsWalk tail head a es b) (hn : ¬ (es.map tail).Nodup) :
    ∃ (p q r : List E) (x : V),
      es = p ++ q ++ r ∧ q ≠ [] ∧ r ≠ [] ∧
      IsWalk tail head a p x ∧ IsWalk tail head x q x ∧
      IsWalk tail head x r b := by
  obtain ⟨p, e, q, f, r, he, htf⟩ := repeated_tail_split es hn
  subst es
  obtain ⟨x, hp, hrest⟩ := (isWalk_append p (e :: (q ++ f :: r))).mp hw
  have hx : tail e = x := hrest.1
  obtain ⟨y, hq, hr⟩ := (isWalk_append q (f :: r)).mp hrest.2
  have hy : y = x := hr.1.symm.trans (htf.symm.trans hx)
  rw [hy] at hq hr
  exact ⟨p, e :: q, f :: r, x, by simp, by simp, by simp, hp,
    ⟨hx, hq⟩, hr⟩

/-- Every closed walk has nonnegative cost: split at a repeated vertex and
induct on the number of arcs until only simple cycles remain. -/
theorem closed_walk_nonnegative (h : NoNegativeSimpleCycles tail head cost)
    {a : V} {es : List E} (hw : IsWalk tail head a es a) :
    0 ≤ walkCost cost es := by
  generalize hn : es.length = n
  induction n using Nat.strong_induction_on generalizing a es with
  | h n ih =>
    by_cases he : es = []
    · subst es
      simp
    by_cases hd : (es.map tail).Nodup
    · exact h a es ⟨hw, he, hd⟩
    obtain ⟨p, q, r, x, hpqr, hq, hr, hp, hqc, hrc⟩ :=
      split_repeated_walk hw hd
    have hql : 0 < q.length := List.length_pos_iff.mpr hq
    have hrl : 0 < r.length := List.length_pos_iff.mpr hr
    have hlen : es.length = p.length + q.length + r.length := by
      simp [hpqr, Nat.add_assoc]
    have hq0 := ih q.length (by omega) hqc rfl
    have hpr : IsWalk tail head a (p ++ r) a :=
      (isWalk_append p r).mpr ⟨x, hp, hrc⟩
    have hpr0 := ih (p ++ r).length (by simp; omega) hpr rfl
    simp only [hpqr, walkCost_append] at *
    linarith

/-- Remove closed subwalks without increasing cost. The resulting list of
visited vertices, including the final vertex, has no repetition. -/
theorem exists_simple_path_le (h : NoNegativeSimpleCycles tail head cost)
    {a b : V} {es : List E} (hw : IsWalk tail head a es b) :
    ∃ fs, IsWalk tail head a fs b ∧ (fs.map tail ++ [b]).Nodup ∧
      walkCost cost fs ≤ walkCost cost es := by
  generalize hn : es.length = n
  induction n using Nat.strong_induction_on generalizing a b es with
  | h n ih =>
    by_cases hd : (es.map tail).Nodup
    · by_cases hb : b ∈ es.map tail
      · obtain ⟨e, he, heb⟩ := List.mem_map.mp hb
        obtain ⟨p, r, hpr⟩ := List.mem_iff_append.mp he
        obtain ⟨x, hp, hr⟩ := (isWalk_append p (e :: r)).mp (hpr ▸ hw)
        have hx : x = b := hr.1.symm.trans heb
        rw [hx] at hp hr
        have hc := closed_walk_nonnegative h hr
        have hlen : p.length < n := by
          simp only [hpr, List.length_append, List.length_cons] at hn
          omega
        obtain ⟨fs, hf, hs, hle⟩ := ih p.length hlen hp rfl
        refine ⟨fs, hf, hs, ?_⟩
        rw [hpr, walkCost_append]
        linarith
      · refine ⟨es, hw, ?_, le_rfl⟩
        simpa [List.nodup_append, hd] using hb
    · obtain ⟨p, q, r, x, hpqr, hq, _, hp, hqc, hrc⟩ :=
        split_repeated_walk hw hd
      have hq0 := closed_walk_nonnegative h hqc
      have hql : 0 < q.length := List.length_pos_iff.mpr hq
      have hlen : (p ++ r).length < n := by
        simp only [hpqr, List.length_append] at hn
        simp only [List.length_append]
        omega
      have hpr : IsWalk tail head a (p ++ r) b :=
        (isWalk_append p r).mpr ⟨x, hp, hrc⟩
      obtain ⟨fs, hf, hs, hle⟩ := ih (p ++ r).length hlen hpr rfl
      refine ⟨fs, hf, hs, ?_⟩
      simp only [hpqr, walkCost_append] at *
      linarith

/-- There are finitely many simple labelled paths ending at a fixed vertex.
Their start is free; this is equivalent to adding a zero-cost super-source. -/
theorem finite_simple_paths [Fintype V] [Finite E] (b : V) :
    {es : List E | (∃ a, IsWalk tail head a es b) ∧
      (es.map tail ++ [b]).Nodup}.Finite := by
  apply (List.finite_length_le E (Fintype.card V)).subset
  intro es hes
  have hc := hes.2.length_le_card
  simp only [List.length_append, List.length_map, List.length_singleton] at hc
  exact le_trans (Nat.le_add_right _ _) hc

/-- The minimum over simple paths exists and is a lower bound for every
walk ending at the same vertex, without any reachability assumption. -/
theorem exists_minimum_walk [Finite V] [Finite E]
    (h : NoNegativeSimpleCycles tail head cost) (b : V) :
    ∃ es : List E, (∃ a, IsWalk tail head a es b) ∧
      (es.map tail ++ [b]).Nodup ∧
      ∀ a fs, IsWalk tail head a fs b → walkCost cost es ≤ walkCost cost fs := by
  classical
  let _ := Fintype.ofFinite V
  let s : Set (List E) := {es | (∃ a, IsWalk tail head a es b) ∧
    (es.map tail ++ [b]).Nodup}
  have hs : s.Finite := finite_simple_paths b
  have hne : s.Nonempty := ⟨[], ⟨⟨b, rfl⟩, by simp⟩⟩
  obtain ⟨es, hes, hmin⟩ := Set.exists_min_image s (walkCost cost) hs hne
  refine ⟨es, hes.1, hes.2, ?_⟩
  intro a fs hw
  obtain ⟨gs, hg, hgs, hle⟩ := exists_simple_path_le h hw
  exact (hmin gs ⟨⟨a, hg⟩, hgs⟩).trans hle

/-- Construct real potentials from the finite minima just proved. -/
theorem exists_potential_of_no_negative_cycles [Finite V] [Finite E]
    (h : NoNegativeSimpleCycles tail head cost) :
    ∃ π : V → ℝ, ∀ e, 0 ≤ cost e + π (tail e) - π (head e) := by
  classical
  have hmin := fun b => exists_minimum_walk h b
  choose path hwalk hsimple hleast using hmin
  refine ⟨fun b => walkCost cost (path b), ?_⟩
  intro e
  obtain ⟨a, ha⟩ := hwalk (tail e)
  have hwe : IsWalk tail head a (path (tail e) ++ [e]) (head e) :=
    (isWalk_append _ _).mpr ⟨tail e, ha, ⟨rfl, rfl⟩⟩
  have hle := hleast (head e) a _ hwe
  simp only [walkCost_append, walkCost_cons, walkCost_nil, add_zero] at hle
  linarith

/-- Reduced costs telescope along a directed walk. -/
theorem potential_walk_bound (π : V → ℝ)
    (hπ : ∀ e, 0 ≤ cost e + π (tail e) - π (head e))
    {a b : V} {es : List E} (hw : IsWalk tail head a es b) :
    π b ≤ π a + walkCost cost es := by
  induction es generalizing a with
  | nil =>
    have hab : a = b := hw
    subst b
    simp
  | cons e es ih =>
    obtain ⟨ht, hr⟩ := hw
    have hrec := ih hr
    have he := hπ e
    rw [ht] at he
    rw [walkCost_cons]
    linarith

/-- The full finite-digraph potential criterion; loops and parallel labelled
arcs are included, and both finite types are permitted to be empty. -/
theorem negative_cycles_iff_potential : NegativeCyclePotentialsStatement := by
  intro V E _ _ tail head cost
  constructor
  · exact exists_potential_of_no_negative_cycles
  · rintro ⟨π, hπ⟩ a es ⟨hw, _, _⟩
    have hc := potential_walk_bound π hπ hw
    linarith

end P205.Networks
