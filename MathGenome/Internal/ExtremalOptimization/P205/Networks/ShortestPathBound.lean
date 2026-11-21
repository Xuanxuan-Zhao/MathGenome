import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ShortestPathBound
import MathGenome.Internal.ExtremalOptimization.P205.Networks.ShortestPathDistances
import Mathlib.Data.Fintype.Prod

open scoped Classical
universe u v
namespace P205.Networks
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows
open ShortestBoundSpec
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

namespace ShortestBound

/-- Every selected arc has consecutive, finite distance levels. -/
theorem selected_levels {G : Digraph V A} {s t : V} (p : Walk G s t)
    (hp : p.IsPath) (hs : DistanceSpec.IsShortest p) {r : A} (hr : r ∈ p.arcs) :
    ∃ k : ℕ, k < Fintype.card V ∧
      DistanceSpec.distance G s (G.tail r) = k ∧
      DistanceSpec.distance G s (G.head r) = (k + 1 : ℕ) := by
  obtain ⟨q, z, hz⟩ := ShortestDistances.split_at_arc p hr
  have ht : DistanceSpec.distance G s (G.tail r) = (q.length : ℕ∞) := by
    apply le_antisymm (ShortestDistances.distance_le_walk q)
    apply le_iInf
    intro q'
    have h := hs (q'.append ((Walk.single G r).append z))
    simp only [Walk.length_append, Walk.length_single] at h
    have hle : q.length ≤ q'.length := by omega
    exact_mod_cast hle
  have hh : DistanceSpec.distance G s (G.head r) = (q.length + 1 : ℕ) := by
    apply le_antisymm
    · simpa using ShortestDistances.distance_le_walk (q.append (Walk.single G r))
    · apply le_iInf
      intro q'
      have h := hs (q'.append z)
      rw [Walk.length_append] at h
      have hle : q.length + 1 ≤ q'.length := by omega
      exact_mod_cast hle
  have hv := List.Nodup.length_le_card hp
  change p.vertices.length ≤ Fintype.card V at hv
  rw [Walk.length_vertices] at hv
  exact ⟨q.length, by omega, ht, hh⟩

@[simp] theorem tail_reverse (G : Digraph V A) (r : A × Bool) :
    tail G (reverse r) = head G r := by
  cases r with | mk a d => cases d <;> rfl

@[simp] theorem head_reverse (G : Digraph V A) (r : A × Bool) :
    head G (reverse r) = tail G r := by
  cases r with | mk a d => cases d <;> rfl

/-- A simple shortest path cannot use both signed copies of one label. -/
theorem no_reverse {N : Network V A} {f g : A → ℝ}
    (S : AugmentationStep N f g) {r : A × Bool} (hr : Used S r) :
    ¬ Used S (reverse r) := by
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hr
  obtain ⟨k, hk, ht, hh⟩ := selected_levels S.path S.isPath S.shortest ha
  change DistanceSpec.distance _ _ (tail N.graph a.val) = _ at ht
  change DistanceSpec.distance _ _ (head N.graph a.val) = _ at hh
  rw [he] at ht hh
  intro hrev
  obtain ⟨b, hb, hbval⟩ := List.mem_map.mp hrev
  obtain ⟨l, hl, hbt, hbh⟩ := selected_levels S.path S.isPath S.shortest hb
  change DistanceSpec.distance _ _ (tail N.graph b.val) = _ at hbt
  change DistanceSpec.distance _ _ (head N.graph b.val) = _ at hbh
  rw [hbval, tail_reverse, hh] at hbt
  rw [hbval, head_reverse, ht] at hbh
  have h₁ : k + 1 = l := by exact_mod_cast hbt
  have h₂ : k = l + 1 := by exact_mod_cast hbh
  omega

/-- Capacity of a signed copy changes only when that copy or its paired
reverse is selected. The latter is the only way its capacity can increase. -/
theorem capacity_update {N : Network V A} {f g : A → ℝ}
    (S : AugmentationStep N f g) (r : A × Bool) :
    BoundedSpec.capacity (fun _ => 0) N.capacity g r =
      BoundedSpec.capacity (fun _ => 0) N.capacity f r -
      (if Used S r then S.amount else 0) +
      (if Used S (reverse r) then S.amount else 0) := by
  unfold Used
  conv_lhs => rw [S.update]
  have hn := (path_arcs_nodup S.path S.isPath).map Subtype.val_injective
  change BoundedSpec.capacity _ _
    (fun a => f a + BoundedSpec.adjustment S.amount (S.path.arcs.map Subtype.val) a) r = _
  generalize hl : S.path.arcs.map Subtype.val = l at hn ⊢
  rw [BoundedSpec.capacity, adjustment_eq _ hn]
  rcases r with ⟨a, d⟩
  cases d <;>
    simp only [BoundedSpec.capacity, reverse, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] <;> ring_nf

theorem saturated_zero {N : Network V A} {f g : A → ℝ}
    (S : AugmentationStep N f g) {r : A × Bool} (hr : Saturates S r) :
    BoundedSpec.capacity (fun _ => 0) N.capacity g r = 0 := by
  rw [capacity_update, ite_eq_left hr.1, ite_eq_right (no_reverse S hr.1), hr.2]
  ring

theorem saturation_exists {N : Network V A} {f g : A → ℝ}
    (S : AugmentationStep N f g) :
    ∃ r, Saturates S r ∧ BoundedSpec.capacity (fun _ => 0) N.capacity g r = 0 := by
  obtain ⟨a, ha, he⟩ := S.bottleneck.2.2
  have hs : Saturates S a.val := ⟨List.mem_map.mpr ⟨a, ha, rfl⟩, he⟩
  exact ⟨a.val, hs, saturated_zero S hs⟩

theorem used_levels {N : Network V A} {f g : A → ℝ}
    (S : AugmentationStep N f g) {r : A × Bool} (hr : Used S r) :
    ∃ k : ℕ, k < Fintype.card V ∧
      DistanceSpec.distance (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f)
        N.source (tail N.graph r) = k ∧
      DistanceSpec.distance (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f)
        N.source (head N.graph r) = (k + 1 : ℕ) := by
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hr
  obtain ⟨k, hk, ht, hh⟩ := selected_levels S.path S.isPath S.shortest ha
  change DistanceSpec.distance _ _ (tail N.graph a.val) = _ at ht
  change DistanceSpec.distance _ _ (head N.graph a.val) = _ at hh
  rw [he] at ht hh
  exact ⟨k, hk, ht, hh⟩

theorem used_positive {N : Network V A} {f g : A → ℝ}
    (S : AugmentationStep N f g) {r : A × Bool} (hr : Used S r) :
    0 < BoundedSpec.capacity (fun _ => 0) N.capacity f r := by
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hr
  rw [← he]
  exact a.property

theorem level_step {N : Network V A} {n : ℕ} (R : Run N n)
    (i : ℕ) (hi : i < n) (x : V) : level R i x ≤ level R (i + 1) x := by
  let S := R.step ⟨i, hi⟩
  have h := ShortestDistances.shortest_augmentation_distance_mono N.graph
    (fun _ => 0) N.capacity (R.flow i) S.path S.isPath S.shortest
    S.amount (le_of_lt S.bottleneck.1) x
  rw [← S.update] at h
  exact h

theorem level_mono {N : Network V A} {n : ℕ} (R : Run N n)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) (x : V) :
    level R i x ≤ level R j x := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; exact le_rfl
    · exact (ih (by omega) (by omega)).trans (level_step R j (by omega) x)

/-- Positive capacity after a nonpositive value requires an intervening use
of the paired signed copy; no assumption on capacity magnitudes is used. -/
theorem restoration {N : Network V A} {n : ℕ} (R : Run N n) (r : A × Bool)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n)
    (hi : BoundedSpec.capacity (fun _ => 0) N.capacity (R.flow i) r ≤ 0)
    (hpos : 0 < BoundedSpec.capacity (fun _ => 0) N.capacity (R.flow j) r) :
    ∃ k : Fin n, i ≤ k.val ∧ k.val < j ∧ Used (R.step k) (reverse r) := by
  induction j with
  | zero =>
    have he : i = 0 := by omega
    subst i
    exact False.elim (not_lt_of_ge hi hpos)
  | succ j ih =>
    have hij' : i ≤ j := by
      by_contra h
      have he : i = j + 1 := by omega
      subst i
      exact not_lt_of_ge hi hpos
    by_cases hprev : 0 < BoundedSpec.capacity (fun _ => 0) N.capacity (R.flow j) r
    · obtain ⟨k, hik, hkj, huse⟩ := ih hij' (by omega) hprev
      exact ⟨k, hik, by omega, huse⟩
    · let k : Fin n := ⟨j, by omega⟩
      by_cases huse : Used (R.step k) (reverse r)
      · exact ⟨k, hij', by simp [k], huse⟩
      · have hu := capacity_update (R.step k) r
        rw [ite_eq_right huse] at hu
        have hamount := (R.step k).bottleneck.1
        have hold : BoundedSpec.capacity (fun _ => 0) N.capacity (R.flow j) r ≤ 0 :=
          le_of_not_gt hprev
        change BoundedSpec.capacity (fun _ => 0) N.capacity (R.flow (j + 1)) r =
          BoundedSpec.capacity (fun _ => 0) N.capacity (R.flow j) r -
            (if Used (R.step k) r then (R.step k).amount else 0) + 0 at hu
        split_ifs at hu <;> linarith

/-- Two saturations force reverse use and a rise of at least two levels. -/
theorem repeated {N : Network V A} {n : ℕ} (R : Run N n)
    (i j : Fin n) (r : A × Bool) (hij : i.val < j.val)
    (hi : Saturates (R.step i) r) (hj : Saturates (R.step j) r) :
    ∃ k : Fin n, i.val < k.val ∧ k.val < j.val ∧
      Used (R.step k) (reverse r) ∧
      level R i.val (tail N.graph r) + 2 ≤ level R k.val (tail N.graph r) ∧
      level R k.val (tail N.graph r) ≤ level R j.val (tail N.graph r) := by
  have hzero := saturated_zero (R.step i) hi
  have hpos := used_positive (R.step j) hj.1
  obtain ⟨k, hik, hkj, huse⟩ := restoration R r (by omega) (by omega)
    (le_of_eq hzero) hpos
  obtain ⟨a, ha, hat, hah⟩ := used_levels (R.step i) hi.1
  obtain ⟨b, hb, hbt, hbh⟩ := used_levels (R.step k) huse
  change level R i.val (tail N.graph r) = _ at hat
  change level R i.val (head N.graph r) = _ at hah
  change level R k.val (tail N.graph (reverse r)) = _ at hbt
  change level R k.val (head N.graph (reverse r)) = _ at hbh
  rw [tail_reverse] at hbt
  rw [head_reverse] at hbh
  refine ⟨k, by omega, hkj, huse, ?_, level_mono R (by omega) (by omega) _⟩
  calc
    level R i.val (tail N.graph r) + 2 = level R i.val (head N.graph r) + 1 := by
      rw [hat, hah]
      simp only [Nat.cast_add, Nat.cast_one]
      simp [add_assoc, show (2 : ℕ∞) = 1 + 1 from rfl]
    _ ≤ level R k.val (head N.graph r) + 1 :=
      add_le_add (level_mono R (by omega) (by omega) _) le_rfl
    _ = level R k.val (tail N.graph r) := by
      rw [hbt, hbh]
      simp

/-- Charge to a signed label and a finite tail level. -/
theorem charge_exists {N : Network V A} {n : ℕ} (R : Run N n) (i : Fin n) :
    ∃ c : (A × Bool) × Fin (Fintype.card V),
      Saturates (R.step i) c.1 ∧ level R i.val (tail N.graph c.1) = c.2.val := by
  obtain ⟨r, hr, hz⟩ := saturation_exists (R.step i)
  obtain ⟨a, ha, ht, hh⟩ := used_levels (R.step i) hr.1
  exact ⟨(r, ⟨a, ha⟩), hr, ht⟩

theorem bound {N : Network V A} {n : ℕ} (R : Run N n) :
    n ≤ 2 * Fintype.card V * Fintype.card A := by
  let c : Fin n → (A × Bool) × Fin (Fintype.card V) :=
    fun i => Classical.choose (charge_exists R i)
  have hc (i : Fin n) : Saturates (R.step i) (c i).1 ∧
      level R i.val (tail N.graph (c i).1) = (c i).2.val :=
    Classical.choose_spec (charge_exists R i)
  have hneq (i j : Fin n) (hij : i.val < j.val) : c i ≠ c j := by
    intro he
    have hr : (c i).1 = (c j).1 := congrArg Prod.fst he
    have hl : (c i).2.val = (c j).2.val := congrArg (fun z => z.2.val) he
    have hjsat : Saturates (R.step j) (c i).1 := hr.symm ▸ (hc j).1
    obtain ⟨k, hik, hkj, huse, hgrow, hmono⟩ := repeated R i j (c i).1 hij (hc i).1 hjsat
    have hgrow := hgrow.trans hmono
    rw [(hc i).2, hr, (hc j).2] at hgrow
    have hnat : (c i).2.val + 2 ≤ (c j).2.val := by exact_mod_cast hgrow
    omega
  have hinj : Function.Injective c := by
    intro i j he
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hneq i j h he
    · exact hneq j i h he.symm
  have hcard := Fintype.card_le_of_injective c hinj
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] at hcard
  calc
    n ≤ (Fintype.card A * 2) * Fintype.card V := hcard
    _ = 2 * Fintype.card V * Fintype.card A := by ac_rfl

end ShortestBound

/-- Every full-bottleneck shortest augmentation saturates a labelled copy. -/
theorem shortest_step_saturates : ShortestBoundSpec.step_saturates.{u,v} := by
  intro V A _ _ N f g S
  exact ShortestBound.saturation_exists S

/-- The same copy can be saturated twice only after reverse use and growth. -/
theorem shortest_repeated_saturation : ShortestBoundSpec.repeated_saturation.{u,v} := by
  intro V A _ _ N n R i j r hij hi hj
  exact ShortestBound.repeated R i j r hij hi hj

/-- Explicit real-capacity bound, valid for every finite algorithm prefix. -/
theorem shortest_augmentation_bound : ShortestBoundSpec.augmentation_bound.{u,v} := by
  intro V A _ _ N n R
  exact ShortestBound.bound R

end P205.Networks
