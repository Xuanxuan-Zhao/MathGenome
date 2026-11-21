import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ChaosDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ShiftSpaces
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.FullShiftChaos
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace D13Unified.Ch17.FullShiftChaos
open Set TopologicalSpace
open scoped Topology
open ShiftSpaces ChaosDefinitions
noncomputable section

lemma shiftPlus_iterate (n : ℕ) (s : OneSided) (j : ℕ) :
    shiftPlus^[n] s j = s (j + n) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (shiftPlus^[n] s) (j + 1) = _
    rw [ih]
    congr 1
    omega

lemma shift_iterate (n : ℕ) (s : TwoSided) (j : ℤ) :
    shift^[n] s j = s (j + n) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (shift^[n] s) (j + 1) = _
    rw [ih]
    congr 1
    push_cast
    omega

lemma cylinder_neighborhood {I : Type} (s : I → Binary) (U : Set (I → Binary))
    (hU : U ∈ 𝓝 s) : ∃ F : Finset I, cylinder s F ⊆ U := by
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hV, hsV⟩
  rcases (cylinders_basis I).exists_subset_of_mem_open hsV hV with
    ⟨W, ⟨t, F, rfl⟩, hsW, hWV⟩
  refine ⟨F, fun u hu => hVU (hWV ?_)⟩
  intro j hj
  exact (hu j hj).trans (hsW j hj)

lemma nat_bound (F : Finset ℕ) : ∃ N : ℕ, ∀ j ∈ F, j < N := by
  exact ⟨F.sup id + 1, fun j hj => Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)⟩

lemma int_bound (F : Finset ℤ) : ∃ N : ℕ, ∀ j ∈ F, -(N : ℤ) < j ∧ j < N := by
  refine ⟨F.sup Int.natAbs + 1, ?_⟩
  intro j hj
  have h : j.natAbs < F.sup Int.natAbs + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup hj)
  have h' : (j.natAbs : ℤ) < (F.sup Int.natAbs + 1 : ℕ) := by exact_mod_cast h
  have : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  have : -(j.natAbs : ℤ) ≤ j := by
    have h := Int.le_natAbs (a := -j)
    simpa using (neg_le_neg h)
  constructor <;> omega

theorem shiftPlus_transitive :
     Specs.D13Unified.Ch17.FullShiftChaos.shiftPlus_transitiveStatement := by
  change TopologicallyTransitive shiftPlus
  apply (topologicallyTransitive_iff_exists_mem shiftPlus).2
  intro U V hU ⟨s, hs⟩ hV ⟨t, ht⟩
  rcases cylinder_neighborhood s U (hU.mem_nhds hs) with ⟨F, hF⟩
  rcases cylinder_neighborhood t V (hV.mem_nhds ht) with ⟨G, hG⟩
  rcases nat_bound F with ⟨N, hN⟩
  let u : OneSided := fun j => if j < N then s j else t (j - N)
  refine ⟨u, hF ?_, N, hG ?_⟩
  · intro j hj
    simp [u, hN j hj]
  · intro j hj
    rw [shiftPlus_iterate]
    simp [u]

theorem shift_transitive :
     Specs.D13Unified.Ch17.FullShiftChaos.shift_transitiveStatement := by
  change TopologicallyTransitive shift
  apply (topologicallyTransitive_iff_exists_mem shift).2
  intro U V hU ⟨s, hs⟩ hV ⟨t, ht⟩
  rcases cylinder_neighborhood s U (hU.mem_nhds hs) with ⟨F, hF⟩
  rcases cylinder_neighborhood t V (hV.mem_nhds ht) with ⟨G, hG⟩
  rcases int_bound (F ∪ G) with ⟨N, hN⟩
  let u : TwoSided := fun j => if j < (N : ℤ) then s j else t (j - 2 * N)
  refine ⟨u, hF ?_, 2 * N, hG ?_⟩
  · intro j hj
    have h := (hN j (Finset.mem_union_left G hj)).2
    simp [u, h]
  · intro j hj
    have h := (hN j (Finset.mem_union_right F hj)).1
    rw [shift_iterate]
    have hn : ¬ j + ((2 * N : ℕ) : ℤ) < (N : ℤ) := by push_cast; omega
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hn
    simp [u, hn]

def flip (a : Binary) : Binary := if a = 0 then 1 else 0
lemma flip_ne (a : Binary) : flip a ≠ a := by
  fin_cases a <;> norm_num [flip]

lemma distancePlus_of_zero_ne (s t : OneSided) (h : s 0 ≠ t 0) :
     distancePlus s t = 1 := by
  have hne : s ≠ t := fun he => h (congrFun he 0)
  have hz : PiNat.firstDiff s t = 0 := by
    by_contra hn
    exact h (PiNat.apply_eq_of_lt_firstDiff (Nat.pos_of_ne_zero hn))
  have he := distancePlus_eq s t
  change distancePlus s t = _ at he
  rw [he, ite_eq_right hne, hz]
  norm_num

theorem shiftPlus_sensitive :
     Specs.D13Unified.Ch17.FullShiftChaos.shiftPlus_sensitiveStatement := by
  intro s U hU
  rcases cylinder_neighborhood s U hU with ⟨F, hF⟩
  rcases nat_bound F with ⟨N, hN⟩
  let t : OneSided := Function.update s N (flip (s N))
  refine ⟨t, hF ?_, N, ?_⟩
  · intro j hj
    have : j ≠ N := by have := hN j hj; omega
    simp [t, this]
  · have hd : (shiftPlus^[N] s) 0 ≠ (shiftPlus^[N] t) 0 := by
      simp only [shiftPlus_iterate, zero_add]
      simpa [t] using (flip_ne (s N)).symm
    change (1 / 2 : ℝ) < distancePlus _ _
    rw [distancePlus_of_zero_ne _ _ hd]
    norm_num

theorem shift_sensitive :
     Specs.D13Unified.Ch17.FullShiftChaos.shift_sensitiveStatement := by
  intro s U hU
  rcases cylinder_neighborhood s U hU with ⟨F, hF⟩
  rcases int_bound F with ⟨N, hN⟩
  let t : TwoSided := Function.update s (N : ℤ) (flip (s N))
  refine ⟨t, hF ?_, N, ?_⟩
  · intro j hj
    have : j ≠ (N : ℤ) := by have := (hN j hj).2; omega
    simp [t, this]
  · have hd : (shift^[N] s) 0 ≠ (shift^[N] t) 0 := by
      simp only [shift_iterate, zero_add]
      simpa [t] using (flip_ne (s N)).symm
    have hh := coordinate_le_distance (shift^[N] s) (shift^[N] t) 0
    rw [symbol_abs_of_ne hd, mul_one] at hh
    norm_num [weight, Specs.D13Unified.Ch17.ShiftSpaces.weight] at hh
    linarith

theorem shiftPlus_dense_periodic :
     Specs.D13Unified.Ch17.FullShiftChaos.shiftPlus_dense_periodicStatement := by
  change DensePeriodicPoints shiftPlus
  apply (densePeriodicPoints_iff_open shiftPlus).2
  intro U hU ⟨s, hs⟩
  rcases cylinder_neighborhood s U (hU.mem_nhds hs) with ⟨F, hF⟩
  rcases nat_bound (insert 0 F) with ⟨N, hN⟩
  have hpos : 0 < N := hN 0 (Finset.mem_insert_self _ _)
  let t : OneSided := fun j => s (j % N)
  refine ⟨t, hF ?_, N, hpos, ?_⟩
  · intro j hj
    simp [t, Nat.mod_eq_of_lt (hN j (Finset.mem_insert_of_mem hj))]
  · funext j
    rw [shiftPlus_iterate]
    simp [t]

theorem shift_dense_periodic :
     Specs.D13Unified.Ch17.FullShiftChaos.shift_dense_periodicStatement := by
  change DensePeriodicPoints shift
  apply (densePeriodicPoints_iff_open shift).2
  intro U hU ⟨s, hs⟩
  rcases cylinder_neighborhood s U (hU.mem_nhds hs) with ⟨F, hF⟩
  rcases int_bound F with ⟨N, hN⟩
  let n : ℕ := 2 * N + 1
  have hn : 0 < n := by dsimp [n]; omega
  let t : TwoSided := fun j => s ((j + N) % (n : ℤ) - N)
  refine ⟨t, hF ?_, n, hn, ?_⟩
  · intro j hj
    obtain ⟨hl, hu⟩ := hN j hj
    have hz : 0 ≤ j + N := by omega
    have hb : j + N < (n : ℤ) := by dsimp [n]; omega
    simp [t, Int.emod_eq_of_lt hz hb]
  · funext j
    rw [shift_iterate]
    dsimp [t]
    congr 2
    rw [show j + (n : ℤ) + N = (j + N) + n by ring, Int.add_emod_right]

/-- The forward direction of Birkhoff transitivity, with exactly its needed
Baire and countable-basis hypotheses. No assertion about inverse iterates. -/
lemma exists_dense_forward_orbit {X : Type*} [TopologicalSpace X]
    [Nonempty X] [SecondCountableTopology X] [BaireSpace X]
    (f : X → X) (hc : Continuous f) (ht : TopologicallyTransitive f) :
    ∃ x, Dense (range (fun n : ℕ => f^[n] x)) := by
  classical
  let B := countableBasis X
  let W : Set X → Set X := fun V => ⋃ n : ℕ, f^[n] ⁻¹' V
  have hOpen : ∀ V ∈ B, IsOpen (W V) := by
    intro V hV
    exact isOpen_iUnion fun n => (isBasis_countableBasis X).isOpen hV |>.preimage (hc.iterate n)
  have hDense : ∀ V ∈ B, Dense (W V) := by
    intro V hV
    rw [dense_iff_inter_open]
    intro U hU hUne
    have hVne : V.Nonempty := Set.nonempty_iff_ne_empty.mpr (fun he =>
      empty_notMem_countableBasis X (he ▸ hV))
    obtain ⟨x, hx, n, hn⟩ :=
      (topologicallyTransitive_iff_exists_mem f).1 ht U V hU hUne
        ((isBasis_countableBasis X).isOpen hV) hVne
    exact ⟨x, hx, mem_iUnion.mpr ⟨n, hn⟩⟩
  have hd : Dense (⋂ V ∈ B, W V) :=
    dense_biInter_of_isOpen hOpen (countable_countableBasis X) hDense
  obtain ⟨x, hx⟩ := hd.nonempty
  refine ⟨x, ?_⟩
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨V, hV, hVne, hVU⟩ := (isBasis_countableBasis X).exists_nonempty_subset hUne hU
  have hxV : x ∈ W V := mem_iInter.mp (mem_iInter.mp hx V) hV
  obtain ⟨n, hn⟩ := mem_iUnion.mp hxV
  exact ⟨f^[n] x, hVU hn, ⟨n, rfl⟩⟩

theorem shiftPlus_dense_orbit :
     Specs.D13Unified.Ch17.FullShiftChaos.shiftPlus_dense_orbitStatement :=
  exists_dense_forward_orbit shiftPlus shiftPlus_continuous shiftPlus_transitive

theorem shift_dense_orbit :
     Specs.D13Unified.Ch17.FullShiftChaos.shift_dense_orbitStatement :=
  exists_dense_forward_orbit shift shift_continuous shift_transitive

lemma shiftPlus_fixed_iff_periodic (s : OneSided) (n : ℕ) :
    shiftPlus^[n] s = s ↔ Function.Periodic s n := by
  constructor
  · intro h j
    simpa only [shiftPlus_iterate] using congrFun h j
  · intro h
    funext j
    exact (shiftPlus_iterate n s j).trans (h j)

lemma shift_fixed_iff_periodic (s : TwoSided) (n : ℕ) :
    shift^[n] s = s ↔ Function.Periodic s (n : ℤ) := by
  constructor
  · intro h j
    simpa only [shift_iterate] using congrFun h j
  · intro h
    funext j
    exact (shift_iterate n s j).trans (h j)

/-- Evaluation on a block of length n is a bijection from all n-fixed
one-sided sequences to binary blocks, including repetitions of shorter blocks. -/
def fixedPlusEquiv (n : ℕ) (hn : 0 < n) :
    {s : OneSided // shiftPlus^[n] s = s} ≃ (Fin n → Binary) where
  toFun s i := s.val i
  invFun w := ⟨fun j => w ⟨j % n, Nat.mod_lt _ hn⟩, by
    apply (shiftPlus_fixed_iff_periodic _ _).2
    intro j
    simp⟩
  left_inv s := by
    apply Subtype.ext
    funext j
    exact ((shiftPlus_fixed_iff_periodic _ _).1 s.property).map_mod_nat j
  right_inv w := by
    funext i
    dsimp
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

lemma periodic_mod_int {A : Type*} {s : ℤ → A} {n : ℤ}
    (h : Function.Periodic s n) (j : ℤ) : s (j % n) = s j := by
  have hh := (h.int_mul (j / n)) (j % n)
  change s (j % n + j / n * n) = s (j % n) at hh
  rw [Int.emod_add_ediv_mul] at hh
  exact hh.symm

/-- The analogous evaluation bijection for bi-infinite sequences. Euclidean
remainder, rather than absolute value, determines the negative coordinates. -/
def fixedEquiv (n : ℕ) (hn : 0 < n) :
    {s : TwoSided // shift^[n] s = s} ≃ (Fin n → Binary) where
  toFun s i := s.val (i.val : ℤ)
  invFun w := ⟨fun j => w ⟨(j % (n : ℤ)).toNat, by
    have h0 := Int.emod_nonneg j (show (n : ℤ) ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos j (show (0 : ℤ) < n by omega)
    omega⟩, by
    apply (shift_fixed_iff_periodic _ _).2
    intro j
    simp⟩
  left_inv s := by
    apply Subtype.ext
    funext j
    change s.val (↑(j % (n : ℤ)).toNat) = s.val j
    rw [Int.toNat_of_nonneg (Int.emod_nonneg j (by omega : (n : ℤ) ≠ 0))]
    exact periodic_mod_int ((shift_fixed_iff_periodic _ _).1 s.property) j
  right_inv w := by
    funext i
    dsimp
    congr 1
    apply Fin.ext
    change (↑i.val % (n : ℤ)).toNat = i.val
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)]
    simp

theorem shiftPlus_fixed_card :
     Specs.D13Unified.Ch17.FullShiftChaos.shiftPlus_fixed_cardStatement := by
  intro n hn
  change Nat.card {s : OneSided // shiftPlus^[n] s = s} = 2 ^ n
  rw [Nat.card_congr (fixedPlusEquiv n hn)]
  simp [Binary, Specs.D13Unified.Ch17.ShiftSpaces.Binary]

theorem shift_fixed_card :
     Specs.D13Unified.Ch17.FullShiftChaos.shift_fixed_cardStatement := by
  intro n hn
  change Nat.card {s : TwoSided // shift^[n] s = s} = 2 ^ n
  rw [Nat.card_congr (fixedEquiv n hn)]
  simp [Binary, Specs.D13Unified.Ch17.ShiftSpaces.Binary]

lemma chaotic_of_compatible_metric {X : Type*} [t : TopologicalSpace X]
    (f : X → X) (d : X → X → ℝ) (m : MetricSpace X)
    (hm : m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = t)
    (hd : ∀ x y, @dist _ m.toDist x y = d x y)
    (ht : TopologicallyTransitive f) (hp : DensePeriodicPoints f)
    (δ : ℝ) (hδ : 0 < δ)
    (hs : ∀ x : X, ∀ U ∈ 𝓝 x, ∃ y ∈ U, ∃ n : ℕ, δ < d (f^[n] x) (f^[n] y)) :
    @Chaotic X m f := by
  change @TopologicallyTransitive X m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace f ∧
    @DensePeriodicPoints X m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace f ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ x : X,
      ∀ U ∈ @nhds X m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace x,
        ∃ y ∈ U, ∃ n : ℕ, δ < @dist X m.toDist (f^[n] x) (f^[n] y))
  rw [hm]
  refine ⟨ht, hp, δ, hδ, ?_⟩
  simpa only [hd] using hs

theorem shiftPlus_chaotic :
     Specs.D13Unified.Ch17.FullShiftChaos.shiftPlus_chaoticStatement := by
  obtain ⟨m, hm, hd⟩ := metricPlus_exists
  exact ⟨m, hm, hd, chaotic_of_compatible_metric shiftPlus distancePlus m hm hd
    shiftPlus_transitive shiftPlus_dense_periodic (1 / 2) (by norm_num) shiftPlus_sensitive⟩

theorem shift_chaotic :
     Specs.D13Unified.Ch17.FullShiftChaos.shift_chaoticStatement := by
  obtain ⟨m, hm, hd⟩ := metric_exists
  exact ⟨m, hm, hd, chaotic_of_compatible_metric shift distance m hm hd
    shift_transitive shift_dense_periodic (1 / 8) (by norm_num) shift_sensitive⟩

end
end D13Unified.Ch17.FullShiftChaos
