import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.GraphShapes
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.DynkinClassification
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open scoped BigOperators Matrix

namespace RepTheorySurvey.Quiver.DynkinClassification

open SimpleGraph
open GraphShapesSpec (underlyingGraph IsPathGraph IsThreeArmedTree)
open DynkinClassificationSpec (ThreeArms)

universe u v

abbrev isDynkinDiagram := @DynkinClassificationSpec.isDynkinDiagram
abbrev hasDynkinComponents := DynkinClassificationSpec.hasDynkinComponents

noncomputable section

/-- Twice the form of a simple graph, counting each unoriented edge twice. -/
private def energy {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V → ℝ) : ℝ :=
  open Classical in
  (2 * ∑ i, x i ^ 2) - ∑ i, ∑ j, if G.Adj i j then x i * x j else 0

private theorem two_titsForm_eq_energy {Q : Type u} [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)] (hacyclic : ¬ RM03.HasOrientedCycle Q)
    (hm : ∀ i j : Q, Forms.edgeMultiplicity i j ≤ 1) (x : Q → ℝ) :
    2 * Forms.titsForm x = energy underlyingGraph x := by
  classical
  rw [Forms.real_quadratic_matrix hacyclic, energy]
  have hentry (i j : Q) :
      x i * (Forms.polarizationMatrix ℝ i j * x j) =
        (if i = j then 2 * x i ^ 2 else 0) -
          (if (underlyingGraph (Q := Q)).Adj i j then x i * x j else 0) := by
    by_cases he : i = j
    · subst j
      simp [Forms.polarizationMatrix_apply_self]
      ring
    · rw [Forms.polarizationMatrix_apply_of_ne he]
      by_cases h : 0 < Forms.edgeMultiplicity i j
      · have h1 : Forms.edgeMultiplicity i j = 1 := by have := hm i j; omega
        simp [h1, he, show underlyingGraph.Adj i j from ⟨he, h⟩]
      · have h0 : Forms.edgeMultiplicity i j = 0 := by omega
        simp [h0, he, show ¬ underlyingGraph.Adj i j from fun h' => h h'.2]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, hentry, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]


section WalkEnergy

variable {V : Type*} {G : SimpleGraph V} {a b : V}

/-- Successive differences, with a final step from the endpoint to zero. -/
private def differences (x : V → ℝ) : {a b : V} → G.Walk a b → List ℝ
  | a, _, .nil => [x a]
  | a, _, @Walk.cons _ _ _ j _ _ p => (x a - x j) :: differences x p

private def armEnergy (x : V → ℝ) (p : G.Walk a b) : ℝ :=
  ((differences x p).map (· ^ 2)).sum

private def edgeProducts (x : V → ℝ) : {a b : V} → G.Walk a b → ℝ
  | _, _, .nil => 0
  | a, _, @Walk.cons _ _ _ j _ _ p => x a * x j + edgeProducts x p

private theorem differences_sum (x : V → ℝ) (p : G.Walk a b) :
    (differences x p).sum = x a := by
  induction p with
  | nil => simp [differences]
  | cons _ _ ih => simp [differences, ih]

private theorem differences_length (x : V → ℝ) (p : G.Walk a b) :
    (differences x p).length = p.length + 1 := by
  induction p <;> simp [differences, *]

private theorem armEnergy_nonneg (x : V → ℝ) (p : G.Walk a b) :
    0 ≤ armEnergy x p := by
  induction p with
  | @nil a => simpa [armEnergy, differences] using sq_nonneg (x a)
  | cons _ _ ih =>
    simp only [armEnergy, differences, List.map_cons, List.sum_cons]
    exact add_nonneg (sq_nonneg _) ih

private theorem eq_zero_on_support_of_armEnergy_zero (x : V → ℝ) (p : G.Walk a b)
    (he : armEnergy x p = 0) {i : V} (hi : i ∈ p.support) : x i = 0 := by
  induction p generalizing i with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hi
    subst i
    simpa [armEnergy, differences] using he
  | @cons a j b h p ih =>
    have hs : (x a - x j) ^ 2 + armEnergy x p = 0 := he
    have hnon := armEnergy_nonneg x p
    have hd := sq_nonneg (x a - x j)
    have htail : armEnergy x p = 0 := by linarith
    rw [Walk.support_cons, List.mem_cons] at hi
    rcases hi with rfl | hi
    · have hj := ih htail p.start_mem_support
      have hij : (x i - x j) ^ 2 = 0 := by linarith
      exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp (by simpa only [hj, sub_zero] using hij)
    · exact ih htail hi

private theorem armEnergy_lower_bound (x : V → ℝ) (p : G.Walk a b) :
    x a ^ 2 / (p.length + 1 : ℝ) ≤ armEnergy x p := by
  have h := Multiset.sq_sum_le_card_mul_sum_sq (↑(differences x p) : Multiset ℝ)
  change ((differences x p).sum) ^ 2 ≤
    ((differences x p).length : ℝ) * armEnergy x p at h
  rw [differences_sum, differences_length, Nat.cast_add, Nat.cast_one] at h
  apply (div_le_iff₀ (by positivity)).2
  simpa only [mul_comm] using h

private theorem armEnergy_identity (x : V → ℝ) (p : G.Walk a b) :
    armEnergy x p =
      2 * (p.support.map (fun i => x i ^ 2)).sum - x a ^ 2 - 2 * edgeProducts x p := by
  induction p with
  | nil => simp [armEnergy, differences, edgeProducts]; ring
  | cons _ _ ih =>
    simp only [armEnergy, differences, edgeProducts, Walk.support_cons,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

private theorem expanded_steps_eq_replicate (x : V → ℝ) (p : G.Walk a b) (t : ℝ)
    (hx : ∀ i ≤ p.length, x (p.getVert i) = ((p.length : ℝ) + 1 - (i : ℝ)) * t) :
    differences x p = List.replicate (p.length + 1) t := by
  induction p with
  | nil =>
    have h := hx 0 (by simp)
    simpa [differences] using h
  | @cons a j b h p ih =>
    have htail (i : ℕ) (hi : i ≤ p.length) :
        x (p.getVert i) = ((p.length : ℝ) + 1 - (i : ℝ)) * t := by
      have he := hx (i + 1) (by simpa using hi)
      rw [Walk.getVert_cons_succ, Walk.length_cons, Nat.cast_add, Nat.cast_add,
        Nat.cast_one] at he
      rw [he]
      ring
    have ha := hx 0 (by simp)
    simp only [Walk.getVert_zero, Walk.length_cons, Nat.cast_add,
      Nat.cast_one, Nat.cast_zero, sub_zero] at ha
    have hj := htail 0 (by simp)
    simp only [Walk.getVert_zero, Nat.cast_zero, sub_zero] at hj
    simp only [differences, Walk.length_cons, List.replicate_succ, ha, hj]
    change ((↑p.length + 1 + 1) * t - (↑p.length + 1) * t) :: differences x p =
      t :: List.replicate (p.length + 1) t
    rw [ih htail]
    congr 1
    ring

private theorem armEnergy_eq_of_linear (x : V → ℝ) (p : G.Walk a b)
    (hx : ∀ i ≤ p.length,
      x (p.getVert i) = ((p.length : ℝ) + 1 - (i : ℝ)) * (x a / (p.length + 1))) :
    armEnergy x p = x a ^ 2 / (p.length + 1 : ℝ) := by
  rw [armEnergy, expanded_steps_eq_replicate x p _ hx, List.map_replicate, List.sum_replicate,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hn : (p.length : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end WalkEnergy

section WalkSums

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}

open Classical in
private theorem sum_support (f : V → ℝ) (p : G.Walk a b) (hp : p.IsPath) :
    (∑ i, if i ∈ p.support then f i else 0) = (p.support.map f).sum := by
  induction p with
  | nil => simp
  | @cons a j b h p ih =>
    obtain ⟨hp', ha⟩ := (Walk.cons_isPath_iff h p).mp hp
    have he (i : V) : (if i ∈ (p.cons h).support then f i else 0) =
        (if i = a then f i else 0) + (if i ∈ p.support then f i else 0) := by
      by_cases hi : i = a
      · subst i
        simp [ha]
      · simp [hi]
    simp_rw [he]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, ih hp', Walk.support_cons, List.map_cons, List.sum_cons]

open Classical in
private theorem single_edge_sum (x : V → ℝ) {i j : V} (h : i ≠ j) :
    (∑ a, ∑ b, if s(a, b) = s(i, j) then x a * x b else 0) = 2 * (x i * x j) := by
  have he (a b : V) : (if s(a, b) = s(i, j) then x a * x b else 0) =
      (if a = i then if b = j then x a * x b else 0 else 0) +
      (if a = j then if b = i then x a * x b else 0 else 0) := by
    simp only [Sym2.eq_iff]
    by_cases hai : a = i
    · subst a
      simp [h]
    · by_cases haj : a = j <;> simp [hai, haj, h.symm]
  simp only [he, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', Finset.sum_ite_irrel, mul_comm (x j) (x i), two_mul]

open Classical in
private theorem sum_edges (x : V → ℝ) (p : G.Walk a b) (hp : p.IsPath) :
    (∑ i, ∑ j, if s(i, j) ∈ p.edges then x i * x j else 0) = 2 * edgeProducts x p := by
  induction p with
  | nil => simp [edgeProducts]
  | @cons a b c h p ih =>
    obtain ⟨hp', ha⟩ := (Walk.cons_isPath_iff h p).mp hp
    have hn : s(a, b) ∉ p.edges := fun hm => ha (p.fst_mem_support_of_mem_edges hm)
    have he (i j : V) : (if s(i, j) ∈ (p.cons h).edges then x i * x j else 0) =
        (if s(i, j) = s(a, b) then x i * x j else 0) +
        (if s(i, j) ∈ p.edges then x i * x j else 0) := by
      by_cases hij : s(i, j) = s(a, b)
      · simp [hij, hn]
      · simp [hij]
    simp only [he, Finset.sum_add_distrib, single_edge_sum x h.ne, ih hp', edgeProducts]
    ring

end WalkSums


section GraphEnergy

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem walk_adj_iff {a b : V} (p : G.Walk a b) (i j : V) :
    p.toSubgraph.Adj i j ↔ s(i, j) ∈ p.edges := by
  rw [← Subgraph.mem_edgeSet, p.mem_edges_toSubgraph]

private theorem path_positive (h : IsPathGraph G) (x : V → ℝ) (hx : x ≠ 0) :
    0 < energy G x := by
  classical
  obtain ⟨a, b, p, hp, hcover, hadj⟩ := h
  have hv := sum_support (fun i => x i ^ 2) p hp
  simp only [hcover, ite_true] at hv
  have hE : energy G x = armEnergy x p + x a ^ 2 := by
    simp only [energy, hadj, walk_adj_iff, sum_edges x p hp, hv, armEnergy_identity]
    ring
  have hpos : 0 < armEnergy x p := by
    refine lt_of_le_of_ne (armEnergy_nonneg x p) ?_
    intro he
    apply hx
    funext i
    exact eq_zero_on_support_of_armEnergy_zero x p he.symm (hcover i)
  rw [hE]
  linarith [sq_nonneg (x a)]

open Classical in
private theorem sum_ite_of_unique {I : Type*} [Fintype I] (P : I → Prop) (r : ℝ)
    [DecidablePred P] [Decidable (∃ i, P i)] (h : ∀ i j, P i → P j → i = j) :
    (∑ i, if P i then r else 0) = if ∃ i, P i then r else 0 := by
  by_cases he : ∃ i, P i
  · obtain ⟨i, hi⟩ := he
    rw [ite_eq_left ⟨i, hi⟩, Finset.sum_eq_single i, ite_eq_left hi]
    · intro j _ hj
      exact ite_eq_right (fun h' => hj (h j i h' hi))
    · simp
  · have hn (i : I) : ¬ P i := fun hi => he ⟨i, hi⟩
    simp [hn]

private theorem threeArms_energy (T : ThreeArms G) (x : V → ℝ) :
    energy G x = (∑ a, armEnergy x (T.arm a)) - x T.center ^ 2 := by
  classical
  have hv (i : V) :
      (∑ a, if i ∈ (T.arm a).support then x i ^ 2 else 0) =
        x i ^ 2 + (if i = T.center then 2 * x i ^ 2 else 0) := by
    by_cases hi : i = T.center
    · subst i
      simp [Walk.start_mem_support]
      ring
    · rw [sum_ite_of_unique (fun a : Fin 3 => i ∈ (T.arm a).support) _ (fun a b ha hb => by
          by_contra hab
          exact hi (T.disjoint a b hab i ha hb))]
      simp [hi, (T.cover i).resolve_left hi]
  have hvs :
      (∑ a, ((T.arm a).support.map (fun i => x i ^ 2)).sum) =
        (∑ i, x i ^ 2) + 2 * x T.center ^ 2 := by
    simp_rw [← sum_support _ _ (T.isPath _)]
    rw [Finset.sum_comm]
    simp [hv, Finset.sum_add_distrib, Finset.sum_ite_eq']
  have he (i j : V) :
      (∑ a, if s(i, j) ∈ (T.arm a).edges then x i * x j else 0) =
        if G.Adj i j then x i * x j else 0 := by
    have hu (a b : Fin 3) (ha : s(i, j) ∈ (T.arm a).edges)
        (hb : s(i, j) ∈ (T.arm b).edges) : a = b := by
      by_contra hab
      have hi := T.disjoint a b hab i
        ((T.arm a).fst_mem_support_of_mem_edges ha) ((T.arm b).fst_mem_support_of_mem_edges hb)
      have hj := T.disjoint a b hab j
        ((T.arm a).snd_mem_support_of_mem_edges ha) ((T.arm b).snd_mem_support_of_mem_edges hb)
      have hij := (T.arm a).toSubgraph.adj_sub ((walk_adj_iff _ _ _).2 ha)
      exact hij.ne (hi.trans hj.symm)
    calc
      _ = (if ∃ a, s(i, j) ∈ (T.arm a).edges then x i * x j else 0) :=
        sum_ite_of_unique (fun a : Fin 3 => s(i, j) ∈ (T.arm a).edges) _ hu
      _ = _ := by simp only [T.adj_iff, walk_adj_iff]
  have hes : (∑ i, ∑ j, if G.Adj i j then x i * x j else 0) =
      ∑ a, 2 * edgeProducts x (T.arm a) := by
    simp_rw [← he]
    have hswap (i : V) :
        (∑ j : V, ∑ a : Fin 3, if s(i, j) ∈ (T.arm a).edges then x i * x j else 0) =
        ∑ a : Fin 3, ∑ j : V, if s(i, j) ∈ (T.arm a).edges then x i * x j else 0 :=
      Finset.sum_comm
    simp_rw [hswap]
    rw [Finset.sum_comm]
    simp_rw [sum_edges _ _ (T.isPath _)]
  simp only [energy, hes, armEnergy_identity, Finset.sum_sub_distrib, ← Finset.mul_sum, hvs,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

private def reciprocalSum (T : ThreeArms G) : ℝ := ∑ a, 1 / ((T.arm a).length + 1 : ℝ)

private theorem threeArms_positive_of_one_lt (T : ThreeArms G) (h : 1 < reciprocalSum T) :
    ∀ x : V → ℝ, x ≠ 0 → 0 < energy G x := by
  intro x hx
  rw [threeArms_energy T x]
  by_cases hc : x T.center = 0
  · simp only [hc, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
    by_contra! hs
    have hs0 : (∑ a, armEnergy x (T.arm a)) = 0 :=
      le_antisymm hs (Finset.sum_nonneg (fun a _ => armEnergy_nonneg _ _))
    have hz (a : Fin 3) : armEnergy x (T.arm a) = 0 := by
      have he := Finset.single_le_sum
        (f := fun a => armEnergy x (T.arm a)) (fun a _ => armEnergy_nonneg _ _)
        (Finset.mem_univ a)
      rw [hs0] at he
      exact le_antisymm he (armEnergy_nonneg _ _)
    apply hx
    funext i
    rcases T.cover i with rfl | ⟨a, ha⟩
    · exact hc
    · exact eq_zero_on_support_of_armEnergy_zero x (T.arm a) (hz a) ha
  · have hle := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (fun a _ => armEnergy_lower_bound x (T.arm a))
    have hfactor :
        (∑ a, x T.center ^ 2 / ((T.arm a).length + 1 : ℝ)) =
          x T.center ^ 2 * reciprocalSum T := by
      simp [reciprocalSum, Finset.mul_sum, div_eq_mul_inv]
    rw [hfactor] at hle
    have hsq : 0 < x T.center ^ 2 := sq_pos_of_ne_zero hc
    have hprod := mul_lt_mul_of_pos_left h hsq
    linarith

private theorem threeArms_exists_minimizer (T : ThreeArms G) :
    ∃ x : V → ℝ, x T.center = 1 ∧ energy G x = reciprocalSum T - 1 := by
  classical
  let x : V → ℝ := fun i => if h : i = T.center then 1 else
    let a := Classical.choose ((T.cover i).resolve_left h)
    ((T.arm a).length + 1 - ((T.arm a).support.idxOf i : ℝ)) / ((T.arm a).length + 1)
  have hxc : x T.center = 1 := by simp [x]
  have ha (a : Fin 3) : armEnergy x (T.arm a) = 1 / ((T.arm a).length + 1 : ℝ) := by
    rw [armEnergy_eq_of_linear, hxc, one_pow]
    intro j hj
    by_cases h0 : j = 0
    · subst j
      simp only [Walk.getVert_zero, hxc, Nat.cast_zero, sub_zero]
      field_simp
    · let p := T.arm a
      let i := p.getVert j
      have hm : i ∈ p.support := p.getVert_mem_support j
      have hn : i ≠ T.center := by
        intro hie
        apply h0
        exact (T.isPath a).getVert_injOn hj (Nat.zero_le _) (hie.trans p.getVert_zero.symm)
      let b := Classical.choose ((T.cover i).resolve_left hn)
      have hb : b = a := by
        by_contra hne
        exact hn (T.disjoint b a hne i (Classical.choose_spec ((T.cover i).resolve_left hn)) hm)
      have hindex : p.support.idxOf i = j := by
        apply (T.isPath a).getVert_injOn
        · have := List.idxOf_lt_length_of_mem hm
          rw [Walk.length_support] at this
          exact Nat.le_of_lt_succ this
        · exact hj
        · exact p.getVert_support_idxOf hm
      change x i = ((↑p.length + 1 - ↑j) : ℝ) * (x T.center / (↑p.length + 1))
      rw [hxc]
      simp only [x, dite_eq_right hn]
      change (((T.arm b).length : ℝ) + 1 - ((T.arm b).support.idxOf i : ℝ)) / (↑(T.arm b).length + 1) =
        (↑p.length + 1 - ↑j) * (1 / (↑p.length + 1))
      rw [hb]
      change ((↑p.length + 1 - ↑(p.support.idxOf i)) : ℝ) / (↑p.length + 1) = _
      rw [hindex, mul_one_div]
  exact ⟨x, hxc, by rw [threeArms_energy, hxc, one_pow]; simp only [ha, reciprocalSum]⟩

end GraphEnergy


section DiagramTypes

variable {V : Type*} {G : SimpleGraph V}

private theorem threeArms_of_shape [Finite V] (h : IsThreeArmedTree G) :
    Nonempty (ThreeArms G) := by
  classical
  obtain ⟨c, hc, tip, arm, hp, hd, hv, he⟩ := h
  let : Fintype (G.neighborSet c) := Fintype.ofFinite _
  have hcard : Fintype.card (G.neighborSet c) = 3 := by
    rwa [Set.ncard_eq_toFinset_card', Set.toFinset_card] at hc
  let e : Fin 3 ≃ G.neighborSet c := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨⟨c, tip ∘ e, fun a => arm (e a), fun a => (hp (e a)).1, fun a => (hp (e a)).2.1,
    fun a b hab => hd _ _ (fun heq => hab (e.injective heq)), ?_, ?_⟩⟩
  · intro i
    rcases hv i with hi | ⟨a, ha⟩
    · exact Or.inl hi
    · obtain ⟨b, rfl⟩ := e.surjective a
      exact Or.inr ⟨b, ha⟩
  · intro i j
    rw [he]
    refine ⟨?_, fun ⟨a, ha⟩ => ⟨e a, ha⟩⟩
    rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := e.surjective a
    exact ⟨b, ha⟩

private theorem reciprocalSum_eq (T : ThreeArms G) (σ : Equiv.Perm (Fin 3)) :
    reciprocalSum T = 1 / ((T.arm (σ 0)).length + 1 : ℝ) +
      1 / ((T.arm (σ 1)).length + 1 : ℝ) + 1 / ((T.arm (σ 2)).length + 1 : ℝ) := by
  rw [reciprocalSum, ← Equiv.sum_comp σ (fun a => 1 / ((T.arm a).length + 1 : ℝ))]
  exact Fin.sum_univ_three _

private theorem reciprocal_antitone {a b : ℕ} (h : a ≤ b) :
    (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
  one_div_le_one_div_of_le (by positivity) (by exact add_le_add_left (Nat.cast_le.mpr h) 1)

private theorem lengths_of_reciprocal (p r s : ℕ) (hp : 0 < p) (hpr : p ≤ r) (hrs : r ≤ s)
    (h : 1 < (1 : ℝ) / (p + 1) + 1 / (r + 1) + 1 / (s + 1)) :
    p = 1 ∧ (r = 1 ∨ r = 2 ∧ (s = 2 ∨ s = 3 ∨ s = 4)) := by
  simp only [one_div] at h
  have hp1 : p = 1 := by
    by_contra hn
    have he : 2 ≤ p := by omega
    have h1 := reciprocal_antitone he
    have h2 := reciprocal_antitone (he.trans hpr)
    have h3 := reciprocal_antitone (he.trans (hpr.trans hrs))
    norm_num at h1 h2 h3
    linarith
  refine ⟨hp1, ?_⟩
  by_cases hr : r = 1
  · exact Or.inl hr
  right
  norm_num [hp1] at h
  have hr2 : r = 2 := by
    by_contra hn
    have he : 3 ≤ r := by omega
    have h2 := reciprocal_antitone he
    have h3 := reciprocal_antitone (he.trans hrs)
    norm_num at h2 h3
    linarith
  refine ⟨hr2, ?_⟩
  norm_num [hr2] at h
  have hs : s < 5 := by
    by_contra! hn
    have h3 := reciprocal_antitone hn
    norm_num at h3
    linarith
  omega

private theorem diagram_of_threeArms {T : ThreeArms G} (h : 1 < reciprocalSum T) :
    isDynkinDiagram G := by
  let n : Fin 3 → ℕ := fun a => (T.arm a).length
  let σ := Tuple.sort n
  have hmono := Tuple.monotone_sort n
  refine Or.inr ⟨T, σ, ?_⟩
  rw [reciprocalSum_eq T σ] at h
  exact lengths_of_reciprocal _ _ _ (T.length_pos _) (hmono (by decide : (0 : Fin 3) ≤ 1))
    (hmono (by decide : (1 : Fin 3) ≤ 2)) h

private theorem one_lt_reciprocal_of_lengths (T : ThreeArms G) (σ : Equiv.Perm (Fin 3))
    (h : (T.arm (σ 0)).length = 1 ∧
      ((T.arm (σ 1)).length = 1 ∨ (T.arm (σ 1)).length = 2 ∧
        ((T.arm (σ 2)).length = 2 ∨ (T.arm (σ 2)).length = 3 ∨
          (T.arm (σ 2)).length = 4))) :
    1 < reciprocalSum T := by
  rw [reciprocalSum_eq T σ]
  obtain ⟨h0, h1 | ⟨h1, h2 | h2 | h2⟩⟩ := h
  · have hpos : 0 < (1 : ℝ) / ((T.arm (σ 2)).length + 1) := by positivity
    norm_num [h0, h1]
    linarith
  · norm_num [h0, h1, h2]
  · norm_num [h0, h1, h2]
  · norm_num [h0, h1, h2]

end DiagramTypes

section Components

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

private noncomputable instance componentFintype : Fintype G.ConnectedComponent :=
  Fintype.ofFinite _

private noncomputable instance componentVertexFintype (C : G.ConnectedComponent) : Fintype C :=
  Fintype.ofFinite _

private def vertexEquiv : V ≃ (Σ C : G.ConnectedComponent, C) where
  toFun i := ⟨G.connectedComponentMk i, ⟨i, rfl⟩⟩
  invFun i := i.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨C, i, hi⟩
    obtain rfl : G.connectedComponentMk i = C := hi
    rfl

private theorem sum_by_component (f : V → ℝ) :
    (∑ i, f i) = ∑ C : G.ConnectedComponent, ∑ i : C, f i := by
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (vertexEquiv G) _ _ (fun _ => rfl)

private theorem energy_by_component (x : V → ℝ) :
    energy G x = ∑ C : G.ConnectedComponent, energy C.toSimpleGraph (fun i => x i.val) := by
  classical
  have hrow (C : G.ConnectedComponent) (i : C) :
      (∑ j, if G.Adj i.val j then x i.val * x j else 0) =
        ∑ j : C, if C.toSimpleGraph.Adj i j then x i.val * x j.val else 0 := by
    let f : V → ℝ := fun j => if G.Adj i.val j then x i.val * x j else 0
    change (∑ j, f j) = ∑ j : C, f j.val
    calc
      _ = ∑ j ∈ Finset.univ.filter (· ∈ C.supp), f j := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ C.supp
        · simp [hj]
        · have hna : ¬G.Adj i.val j := fun ha => hj (C.mem_supp_of_adj_mem_supp i.property ha)
          simp [hj, f, hna]
      _ = _ := Finset.sum_subtype _ (fun _ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl) _
  rw [energy]
  rw [sum_by_component G (fun i => x i ^ 2),
    sum_by_component G (fun i => ∑ j, if G.Adj i j then x i * x j else 0)]
  simp only [hrow, energy, Finset.sum_sub_distrib, Finset.mul_sum]

private theorem component_positive (hpos : ∀ x : V → ℝ, x ≠ 0 → 0 < energy G x)
    (C : G.ConnectedComponent) (y : C → ℝ) (hy : y ≠ 0) : 0 < energy C.toSimpleGraph y := by
  classical
  let x : V → ℝ := fun i => if h : i ∈ C.supp then y ⟨i, h⟩ else 0
  have hC : (fun i : C => x i.val) = y := by
    funext i
    simp only [x, dite_eq_left (show i.val ∈ C.supp from i.property)]
  have hx : x ≠ 0 := by
    intro hz
    apply hy
    rw [← hC, hz]
    rfl
  have hh := hpos x hx
  rw [energy_by_component] at hh
  have hzero (D : G.ConnectedComponent) (hD : D ≠ C) :
      energy D.toSimpleGraph (fun i => x i.val) = 0 := by
    have hval (i : D) : x i.val = 0 := by
      have hi : i.val ∉ C.supp := fun hi => hD (i.property.symm.trans hi)
      simp only [x, dite_eq_right hi]
    simp [energy, hval]
  rw [Finset.sum_eq_single C (fun D _ hD => hzero D hD) (by simp), hC] at hh
  exact hh

private theorem positive_of_components
    (hpos : ∀ C : G.ConnectedComponent, ∀ y : C → ℝ, y ≠ 0 → 0 < energy C.toSimpleGraph y) :
    ∀ x : V → ℝ, x ≠ 0 → 0 < energy G x := by
  classical
  intro x hx
  rw [energy_by_component]
  apply Finset.sum_pos'
  · intro C _
    by_cases hc : (fun i : C => x i.val) = 0
    · rw [hc]
      simp [energy]
    · exact (hpos C _ hc).le
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! hh
      exact hx (funext hh)
    refine ⟨G.connectedComponentMk i, Finset.mem_univ _, hpos _ _ ?_⟩
    intro hc
    exact hi (congrFun hc ⟨i, rfl⟩)

end Components

/-- The Tits form is positive definite precisely for disjoint unions of the
simply laced Dynkin diagrams. -/
theorem positiveDefiniteIffDynkin : DynkinClassificationSpec.PositiveDefiniteIffDynkin.{u, v} := by
  classical
  intro Q _ _ _ hacyclic
  constructor
  · intro hpos
    have hm := GraphShapes.positiveDefiniteMultiplicity hacyclic hpos
    refine ⟨hm, fun C => ?_⟩
    rcases GraphShapes.positiveDefiniteComponentShapes hacyclic hpos C with hp | ht
    · exact Or.inl hp
    · obtain ⟨T⟩ := threeArms_of_shape ht
      have hglobal (x : Q → ℝ) (hx : x ≠ 0) : 0 < energy underlyingGraph x := by
        rw [← two_titsForm_eq_energy hacyclic hm]
        exact mul_pos (by norm_num) (hpos x hx)
      obtain ⟨y, hy, he⟩ := threeArms_exists_minimizer T
      have hne : y ≠ 0 := by
        intro hz
        simp [hz] at hy
      have h := component_positive underlyingGraph hglobal C y hne
      rw [he] at h
      exact diagram_of_threeArms (by linarith)
  · rintro ⟨hm, hd⟩ x hx
    have h := positive_of_components (underlyingGraph (Q := Q)) (fun C => by
      rcases hd C with hp | ⟨T, σ, hT⟩
      · exact path_positive hp
      · exact threeArms_positive_of_one_lt T (one_lt_reciprocal_of_lengths T σ hT)) x hx
    rw [← two_titsForm_eq_energy hacyclic hm] at h
    linarith

end
end RepTheorySurvey.Quiver.DynkinClassification
