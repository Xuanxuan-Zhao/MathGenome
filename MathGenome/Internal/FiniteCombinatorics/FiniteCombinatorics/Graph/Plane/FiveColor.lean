import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.FiveColor
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Plane.KempeSeparation
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Coloring.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.DegreesLeaves
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.SplitIfs

import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Plane.EdgeBounds
universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Plane.FiveColor
attribute [local instance] Classical.propDecidable
open Specs.FiniteCombinatorics.Graph.Plane.Foundations
open Specs.FiniteCombinatorics.Graph.Plane.KempeSeparation

/-- Restrict an actual drawing along an induced-subgraph embedding. -/
def inducedDrawing {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Drawing G) (s : Set V) : Drawing (G.induce s) where
  point a := D.point a
  point_injective := D.point_injective.comp Subtype.val_injective
  edge e := D.edge ((SimpleGraph.Embedding.induce s).mapEdgeSet e)
  edge_arc a b h := D.edge_arc a b h
  vertex_edge e v := by
    rw [D.vertex_edge]
    change v.val ∈ Sym2.map Subtype.val e.val ↔ v ∈ e.val
    simp only [Sym2.mem_map, Subtype.val_inj, exists_eq_right]
  edge_intersection e f h := by
    rw [D.edge_intersection _ _ ((SimpleGraph.Embedding.induce s).mapEdgeSet.injective.ne h)]
    ext z
    constructor
    · rintro ⟨v, he, rfl⟩
      obtain ⟨a, ha, rfl⟩ := (Sym2.mem_map.mp he.1)
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      obtain ⟨b, hb, heq⟩ := Sym2.mem_map.mp he.2
      exact (Subtype.val_injective heq) ▸ hb
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, ⟨Sym2.mem_map.mpr ⟨v, hv.1, rfl⟩,
        Sym2.mem_map.mpr ⟨v, hv.2, rfl⟩⟩, rfl⟩

/-- The edge bound and handshaking yield a low-degree vertex in every
nonempty planar graph, including the one- and two-vertex cases. -/
theorem exists_degree_le_five
    (bound : Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds.planar_edge_boundType.{u})
    {V : Type u} [Finite V] [Nonempty V] (G : SimpleGraph V) (hG : Planar G) :
    ∃ x, Nat.card (G.neighborSet x) ≤ 5 := by
  classical
  let := Fintype.ofFinite V
  by_contra! h
  have hsum : 6 * Fintype.card V ≤ ∑ x : V, Nat.card (G.neighborSet x) := by
    have hdeg (x : V) : 6 ≤ Nat.card (G.neighborSet x) := by
      have := h x
      omega
    simpa [Nat.mul_comm] using
      (Finset.sum_le_sum (s := Finset.univ) (fun x _ => hdeg x))
  have hcard : Fintype.card V = Nat.card V := Nat.card_eq_fintype_card.symm
  have hs := FiniteCombinatorics.Graph.Trees.degree_sum G
  change (∑ x : V, Nat.card (G.neighborSet x)) = 2 * Nat.card G.edgeSet at hs
  by_cases hn : 3 ≤ Nat.card V
  · have hb := bound hG hn
    omega
  · obtain ⟨x⟩ := ‹Nonempty V›
    have hd : Nat.card (G.neighborSet x) ≤ Nat.card V :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have := h x
    omega

/-- The spanning graph of the edges whose two endpoints use a chosen palette. -/
def paletteGraph {V : Type u} (G : SimpleGraph V) {C : Type*}
    (color : V → C) (i j : C) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ (color a = i ∨ color a = j) ∧ (color b = i ∨ color b = j)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma reachable_palette {V : Type u} {G : SimpleGraph V} {C : Type*}
    {color : V → C} {i j : C} {a b : V}
    (ha : color a = i ∨ color a = j) (h : (paletteGraph G color i j).Reachable a b) :
    color b = i ∨ color b = j := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons h p ih => exact ih h.2.2

/-- Swap exactly one full two-color component. -/
def swapComponent {V : Type u} (G : SimpleGraph V) {C : Type*} [DecidableEq C]
    (color : G.Coloring C) (i j : C) (a : V) : G.Coloring C := by
  classical
  let H := paletteGraph G color i j
  let f v := if H.Reachable a v then Equiv.swap i j (color v) else color v
  refine SimpleGraph.Coloring.mk f ?_
  intro v w hvw
  have hv := color.valid hvw
  by_cases hrv : H.Reachable a v <;> by_cases hrw : H.Reachable a w
  · simpa [f, hrv, hrw] using (Equiv.swap i j).injective.ne hv
  · simp only [f, ite_eq_left hrv, ite_eq_right hrw]
    intro heq
    have hcv : color v = i ∨ color v = j := by
      by_contra! hn
      exact hv (by simpa [Equiv.swap_apply_of_ne_of_ne hn.1 hn.2] using heq)
    have hcw : color w = i ∨ color w = j := by
      rcases hcv with hcv | hcv <;> simp_all
    exact hrw (hrv.trans (SimpleGraph.Adj.reachable ⟨hvw, hcv, hcw⟩))
  · simp only [f, ite_eq_right hrv, ite_eq_left hrw]
    intro heq
    have hcw : color w = i ∨ color w = j := by
      by_contra! hn
      exact hv (by simpa [Equiv.swap_apply_of_ne_of_ne hn.1 hn.2] using heq)
    have hcv : color v = i ∨ color v = j := by
      rcases hcw with hcw | hcw <;> simp_all
    exact hrv (hrw.trans (SimpleGraph.Adj.reachable ⟨hvw.symm, hcw, hcv⟩))
  · simpa [f, hrv, hrw] using hv

/-- Two distinct spokes cannot have the same angular direction. -/
lemma initial_arguments_ne {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Drawing G) {x a b : V} (ha : G.Adj x a) (hb : G.Adj x b)
    (hab : a ≠ b) {va vb : Point}
    (hva : IsInitialDirection D x a ha va) (hvb : IsInitialDirection D x b hb vb) :
    (⟨va.1, va.2⟩ : ℂ).arg ≠ (⟨vb.1, vb.2⟩ : ℂ).arg := by
  intro heq
  have hna : (⟨va.1, va.2⟩ : ℂ) ≠ 0 := by
    simpa using (complex_direction_ne_zero va 1 one_ne_zero).mpr hva.1
  have hnb : (⟨vb.1, vb.2⟩ : ℂ) ≠ 0 := by
    simpa using (complex_direction_ne_zero vb 1 one_ne_zero).mpr hvb.1
  obtain ⟨εa, hεa, hea⟩ := hva.2
  obtain ⟨εb, hεb, heb⟩ := hvb.2
  obtain ⟨z, hz, hzx, hzb⟩ := ray_point_near hva.1 (lt_min hεa hεb)
  have hza : z ∈ D.edge ⟨s(x,a), ha⟩ := by
    exact (hea.symm ▸ (show z ∈ rayFrom (D.point x) va ∩ Metric.ball (D.point x) εa from
      ⟨hz, Metric.ball_subset_ball (min_le_left _ _) hzb⟩)).1
  have hzray : z ∈ rayFrom (D.point x) vb := by
    obtain ⟨t, ht, hzt⟩ := hz
    have hmul := (Complex.arg_eq_arg_iff hnb hna).mp heq.symm
    rw [← Complex.ofReal_div] at hmul
    have heva : va = (‖(⟨va.1,va.2⟩ : ℂ)‖ / ‖(⟨vb.1,vb.2⟩ : ℂ)‖) • vb := by
      apply Prod.ext
      · simpa using (congrArg Complex.re hmul).symm
      · simpa using (congrArg Complex.im hmul).symm
    refine ⟨t * (‖(⟨va.1,va.2⟩ : ℂ)‖ / ‖(⟨vb.1,vb.2⟩ : ℂ)‖),
      mul_nonneg ht (div_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
    exact hzt.trans (by simpa only [smul_smul] using
      (congrArg (fun w : Point => D.point x + t • w) heva))
  have hzb' : z ∈ D.edge ⟨s(x,b), hb⟩ := by
    exact (heb.symm ▸ (show z ∈ rayFrom (D.point x) vb ∩ Metric.ball (D.point x) εb from
      ⟨hzray, Metric.ball_subset_ball (min_le_right _ _) hzb⟩)).1
  exact hzx (incident_edges_intersection D ha hb hab ⟨hza, hzb'⟩)

/-- Choose four neighbors in actual angular order. We need only four of the
five neighbors, since the two alternating color pairs are the relevant ones. -/
theorem exists_cyclic_four {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Drawing G) (x : V) (hsize : 4 ≤ Nat.card (G.neighborSet x)) :
    ∃ a : Fin 4 → G.neighborSet x, Function.Injective a ∧
      CyclicSpokes D x (a 0) (a 1) (a 2) (a 3)
        (a 0).property (a 1).property (a 2).property (a 3).property := by
  classical
  let := Fintype.ofFinite (G.neighborSet x)
  choose dir hdir using (fun a : G.neighborSet x => initial_direction_exists D x a a.property)
  let angle (a : G.neighborSet x) := (⟨(dir a).1, (dir a).2⟩ : ℂ).arg
  have hinj : Function.Injective angle := by
    intro a b hab
    by_contra h
    exact initial_arguments_ne D a.property b.property
      (fun heq => h (Subtype.ext heq)) (hdir a) (hdir b) hab
  let s : Finset ℝ := Finset.univ.image angle
  have hs : 4 ≤ s.card := by
    simpa [s, Finset.card_image_of_injective _ hinj, Nat.card_eq_fintype_card] using hsize
  let f : Fin 4 ↪o ℝ := s.orderEmbOfCardLe hs
  have hm (i : Fin 4) : ∃ a : G.neighborSet x, angle a = f i := by
    have := s.orderEmbOfCardLe_mem hs i
    simpa [s] using this
  choose a ha using hm
  have hai : Function.Injective a := by
    intro i j hij
    apply f.injective
    rw [← ha i, ← ha j, hij]
  have hmono : StrictMono (angle ∘ a) := by
    simpa only [Function.comp_def, ha] using f.strictMono
  refine ⟨a, hai, dir (a 0), dir (a 1), dir (a 2), dir (a 3),
    hdir _, hdir _, hdir _, hdir _, Or.inl ?_⟩
  refine ⟨1, one_ne_zero, ?_, ?_, ?_⟩
  · simpa [angle] using hmono (show (0 : Fin 4) < 1 by decide)
  · simpa [angle] using hmono (show (1 : Fin 4) < 2 by decide)
  · simpa [angle] using hmono (show (2 : Fin 4) < 3 by decide)

@[simp] theorem swapComponent_apply {V : Type u} (G : SimpleGraph V) {C : Type*}
    [DecidableEq C] (color : G.Coloring C) (i j : C) (a v : V) :
    swapComponent G color i j a v =
      if (paletteGraph G color i j).Reachable a v then Equiv.swap i j (color v) else color v := by
  classical
  rfl

abbrev Deleted {V : Type u} (x : V) := {v : V // v ≠ x}

/-- A neighbor is a vertex of the deleted graph. -/
def deletedNeighbor {V : Type u} {G : SimpleGraph V} (x : V)
    (a : G.neighborSet x) : Deleted x := ⟨a, a.property.ne.symm⟩

/-- Extend a coloring when a color is absent from the neighborhood. -/
def extendColoring {V : Type u} (G : SimpleGraph V) (x : V)
    (c : (G.induce {v | v ≠ x}).Coloring (Fin 5)) (i : Fin 5)
    (hi : ∀ a : G.neighborSet x, c (deletedNeighbor x a) ≠ i) : G.Coloring (Fin 5) := by
  classical
  let f v := if h : v = x then i else c ⟨v, h⟩
  refine SimpleGraph.Coloring.mk f ?_
  intro v w h
  by_cases hv : v = x
  · subst v
    have hw : w ≠ x := h.ne.symm
    simpa [f, hw, deletedNeighbor] using (hi ⟨w, h⟩).symm
  · by_cases hw : w = x
    · subst w
      simpa [f, hv, deletedNeighbor] using hi ⟨v, h.symm⟩
    · simpa [f, hv, hw] using c.valid (show (G.induce {v | v ≠ x}).Adj ⟨v,hv⟩ ⟨w,hw⟩ from h)

/-- When neighbor colors are distinct, a component swap separating two
neighbors frees the color of the first neighbor. -/
theorem swap_frees_color {V : Type u} (G : SimpleGraph V) (x : V)
    (c : (G.induce {v | v ≠ x}).Coloring (Fin 5))
    (hc : Function.Injective (fun a : G.neighborSet x => c (deletedNeighbor x a)))
    (a b : G.neighborSet x)
    (h : ¬(paletteGraph (G.induce {v | v ≠ x}) c
      (c (deletedNeighbor x a)) (c (deletedNeighbor x b))).Reachable
        (deletedNeighbor x a) (deletedNeighbor x b)) :
    ∀ y : G.neighborSet x,
      swapComponent (G.induce {v | v ≠ x}) c
        (c (deletedNeighbor x a)) (c (deletedNeighbor x b))
        (deletedNeighbor x a) (deletedNeighbor x y) ≠ c (deletedNeighbor x a) := by
  classical
  intro y
  rw [swapComponent_apply]
  split_ifs with hy
  · intro heq
    have hb : c (deletedNeighbor x y) = c (deletedNeighbor x b) := by
      apply (Equiv.swap (c (deletedNeighbor x a)) (c (deletedNeighbor x b))).injective
      simpa using heq
    have hby := hc hb
    subst y
    exact h hy
  · intro heq
    have hay := hc heq
    subst y
    exact hy (.refl _)

lemma palette_walk_support {V : Type u} {G : SimpleGraph V} {C : Type*}
    {c : V → C} {i j : C} {a b : V}
    (p : (paletteGraph G c i j).Walk a b) (ha : c a = i ∨ c a = j) :
    ∀ v ∈ p.support, c v = i ∨ c v = j := by
  induction p with
  | nil => simpa using ha
  | cons h p ih =>
    intro v hv
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ha
    · exact ih h.2.2 v hv

/-- A palette path in the deleted graph gives a walk in the original graph
which avoids the deleted vertex and has precisely the same palette. -/
theorem palette_reachable_walk {V : Type u} {G : SimpleGraph V} (x : V)
    (c : (G.induce {v | v ≠ x}).Coloring (Fin 5)) (i j : Fin 5)
    {a b : Deleted x} (ha : c a = i ∨ c a = j)
    (h : (paletteGraph (G.induce {v | v ≠ x}) c i j).Reachable a b) :
    ∃ p : G.Walk a.val b.val, x ∉ p.support ∧
      ∀ v ∈ p.support, ∃ hv : v ≠ x, c ⟨v,hv⟩ = i ∨ c ⟨v,hv⟩ = j := by
  obtain ⟨p⟩ := h
  let f : paletteGraph (G.induce {v | v ≠ x}) c i j →g G :=
    { toFun := Subtype.val, map_rel' := fun h => h.1 }
  refine ⟨p.map f, ?_, ?_⟩
  · simp only [SimpleGraph.Walk.support_map, List.mem_map]
    rintro ⟨v, hv, heq⟩
    exact v.property heq
  · intro v hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact ⟨w.property, palette_walk_support p ha w hw⟩

/-- The supplied separation theorem rules out simultaneous connections in
the two disjoint alternating palettes, for the actual deleted-graph coloring. -/
theorem alternating_palettes_not_both {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Drawing G) (x : V) (a b c d : G.neighborSet x)
    (col : (G.induce {v | v ≠ x}).Coloring (Fin 5))
    (hn : [a.val,b.val,c.val,d.val].Nodup)
    (hcyc : CyclicSpokes D x a b c d a.property b.property c.property d.property)
    (hcol : [col (deletedNeighbor x a), col (deletedNeighbor x b),
      col (deletedNeighbor x c), col (deletedNeighbor x d)].Nodup) :
    ¬((paletteGraph (G.induce {v | v ≠ x}) col
        (col (deletedNeighbor x a)) (col (deletedNeighbor x c))).Reachable
          (deletedNeighbor x a) (deletedNeighbor x c) ∧
      (paletteGraph (G.induce {v | v ≠ x}) col
        (col (deletedNeighbor x b)) (col (deletedNeighbor x d))).Reachable
          (deletedNeighbor x b) (deletedNeighbor x d)) := by
  classical
  let ca := col (deletedNeighbor x a)
  let cb := col (deletedNeighbor x b)
  let cc := col (deletedNeighbor x c)
  let cd := col (deletedNeighbor x d)
  have hdif : ca ≠ cb ∧ ca ≠ cc ∧ ca ≠ cd ∧ cb ≠ cc ∧ cb ≠ cd ∧ cc ≠ cd := by
    simpa [ca, cb, cc, cd, List.nodup_cons, not_or, and_assoc] using hcol
  let encode (i : Fin 5) : Fin 4 := if i = ca then 0 else if i = cb then 1 else if i = cc then 2 else 3
  have henc : encode ca = 0 ∧ encode cb = 1 ∧ encode cc = 2 ∧ encode cd = 3 := by
    simp [encode, hdif.1, hdif.2.1, hdif.2.2.1, hdif.2.2.2.1,
      hdif.2.2.2.2.1, hdif.2.2.2.2.2, Ne.symm]
  let color (v : V) : Fin 4 := if hv : v ≠ x then encode (col ⟨v,hv⟩) else 0
  have hcolor (v : Deleted x) : color v.val = encode (col v) := by simp [color, v.property]
  rintro ⟨hac, hbd⟩
  apply alternating_color_paths D x a b c d a.property b.property c.property d.property color hn hcyc
    (by simpa [deletedNeighbor] using (hcolor (deletedNeighbor x a)).trans henc.1)
    (by simpa [deletedNeighbor] using (hcolor (deletedNeighbor x b)).trans henc.2.1)
    (by simpa [deletedNeighbor] using (hcolor (deletedNeighbor x c)).trans henc.2.2.1)
    (by simpa [deletedNeighbor] using (hcolor (deletedNeighbor x d)).trans henc.2.2.2)
  obtain ⟨p, hpx, hp⟩ := palette_reachable_walk x col ca cc (Or.inl rfl) hac
  obtain ⟨q, hqx, hq⟩ := palette_reachable_walk x col cb cd (Or.inl rfl) hbd
  refine ⟨⟨p, hpx, ?_⟩, q, hqx, ?_⟩
  · intro v hv
    obtain ⟨hne, h | h⟩ := hp v hv
    · exact Or.inl ((hcolor ⟨v,hne⟩).trans ((congrArg encode h).trans henc.1))
    · exact Or.inr ((hcolor ⟨v,hne⟩).trans ((congrArg encode h).trans henc.2.2.1))
  · intro v hv
    obtain ⟨hne, h | h⟩ := hq v hv
    · exact Or.inl ((hcolor ⟨v,hne⟩).trans ((congrArg encode h).trans henc.2.1))
    · exact Or.inr ((hcolor ⟨v,hne⟩).trans ((congrArg encode h).trans henc.2.2.2))

/-- Complete the induction step: either a color is already missing, or the
five neighbors use distinct colors and one of the two Kempe swaps frees one. -/
theorem extend_five_coloring {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Drawing G) (x : V) (hx : Nat.card (G.neighborSet x) ≤ 5)
    (col : (G.induce {v | v ≠ x}).Coloring (Fin 5)) : Nonempty (G.Coloring (Fin 5)) := by
  classical
  let nc : G.neighborSet x → Fin 5 := fun a => col (deletedNeighbor x a)
  by_cases hsur : Function.Surjective nc
  · have hbij := hsur.bijective_of_nat_card_le (by simpa using hx)
    have hsize : 4 ≤ Nat.card (G.neighborSet x) := by
      have := Nat.card_le_card_of_surjective nc hsur
      simp only [Nat.card_fin] at this
      omega
    obtain ⟨a, hai, hcyc⟩ := exists_cyclic_four D x hsize
    have hn : [(a 0).val, (a 1).val, (a 2).val, (a 3).val].Nodup := by
      have hi : Function.Injective (fun i => (a i).val) := Subtype.val_injective.comp hai
      have hlist : ([0,1,2,3] : List (Fin 4)).Nodup := by decide
      exact hlist.map hi
    have hcol : [nc (a 0), nc (a 1), nc (a 2), nc (a 3)].Nodup := by
      have hlist : ([0,1,2,3] : List (Fin 4)).Nodup := by decide
      exact hlist.map (hbij.1.comp hai)
    have hnot := alternating_palettes_not_both D x (a 0) (a 1) (a 2) (a 3) col hn hcyc hcol
    by_cases hac : (paletteGraph (G.induce {v | v ≠ x}) col (nc (a 0)) (nc (a 2))).Reachable
        (deletedNeighbor x (a 0)) (deletedNeighbor x (a 2))
    · have hbd : ¬(paletteGraph (G.induce {v | v ≠ x}) col (nc (a 1)) (nc (a 3))).Reachable
          (deletedNeighbor x (a 1)) (deletedNeighbor x (a 3)) := fun h => hnot ⟨hac,h⟩
      exact ⟨extendColoring G x (swapComponent _ col _ _ (deletedNeighbor x (a 1)))
        (nc (a 1)) (swap_frees_color G x col hbij.1 (a 1) (a 3) hbd)⟩
    · exact ⟨extendColoring G x (swapComponent _ col _ _ (deletedNeighbor x (a 0)))
        (nc (a 0)) (swap_frees_color G x col hbij.1 (a 0) (a 2) hac)⟩
  · obtain ⟨i, hi⟩ : ∃ i, ∀ a, nc a ≠ i := by simpa [Function.Surjective] using hsur
    exact ⟨extendColoring G x col i hi⟩

/-- Conditional draft of W63. The four frozen premises are in the contract's
specified order; only the general edge bound is needed by this derivation.
The original closed target is deliberately left for dependency closure. -/
theorem five_color_conditional
    (_k5 : Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds.complete_five_nonplanarType)
    (_k33 : Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds.complete_three_three_nonplanarType)
    (_bip : Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds.planar_bipartite_edge_boundType.{u})
    (bound : Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds.planar_edge_boundType.{u}) :
    Specs.FiniteCombinatorics.Graph.Plane.FiveColor.five_colorType.{u} := by
  classical
  have aux : ∀ n, ∀ {V : Type u} [Finite V], Nat.card V = n →
      ∀ (G : SimpleGraph V), Planar G → Nonempty (G.Coloring (Fin 5)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ hn G hG
      by_cases he : IsEmpty V
      · let := he
        exact ⟨SimpleGraph.Coloring.mk (fun v => isEmptyElim v) (fun {v} => isEmptyElim v)⟩
      · have : Nonempty V := not_isEmpty_iff.mp he
        obtain ⟨x, hx⟩ := exists_degree_le_five bound G hG
        obtain ⟨D⟩ := hG
        have hlt : Nat.card (Deleted x) < n := by
          let := Fintype.ofFinite V
          simpa [Nat.card_eq_fintype_card, ← hn] using
            (Fintype.card_subtype_lt (x := x) (by simp : ¬(x ≠ x)))
        obtain ⟨col⟩ := ih (Nat.card (Deleted x)) hlt rfl
          (G.induce {v | v ≠ x}) ⟨inducedDrawing D {v | v ≠ x}⟩
        exact extend_five_coloring D x hx col
  intro V _ G hG
  exact aux (Nat.card V) rfl G hG

end FiniteCombinatorics.Graph.Plane.FiveColor

universe v8_closure_518e7d60776b3aad_u0
theorem _root_.«FiniteCombinatorics».«Graph».«Plane».«FiveColor».«five_color» : _root_.«Specs».«FiniteCombinatorics».«Graph».«Plane».«FiveColor».«five_colorType».{v8_closure_518e7d60776b3aad_u0} :=
  @_root_.«FiniteCombinatorics».«Graph».«Plane».«FiveColor».«five_color_conditional».{v8_closure_518e7d60776b3aad_u0} (@_root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«complete_five_nonplanar») (@_root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«complete_three_three_nonplanar») (@_root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«planar_bipartite_edge_bound».{v8_closure_518e7d60776b3aad_u0}) (@_root_.«FiniteCombinatorics».«Graph».«Plane».«EdgeBounds».«planar_edge_bound».{v8_closure_518e7d60776b3aad_u0})
