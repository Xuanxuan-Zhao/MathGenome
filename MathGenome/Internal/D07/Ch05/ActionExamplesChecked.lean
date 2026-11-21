import MathGenome.Internal.Specs.D07.Ch05.ActionExamplesChecked
import MathGenome.Internal.D07.Ch05.Burnside
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Square vertex and coloring actions, and their Burnside counts.
All color counts are natural numbers, including zero. -/
namespace D07.Ch05.ActionExamplesChecked
open Specs.D07.Ch05.ActionExamplesChecked

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem vertex_formulas : VertexFormulas := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; change 1 + i = i + 1; exact add_comm _ _
  · intro i; change -(0 + i) = -i; simp
  · exact DihedralGroup.r_one_pow_n
  · rw [pow_two, DihedralGroup.sr_mul_self]
  · simp

theorem rotation_identification : RotationIdentification := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y h
    change DihedralGroup.r x.toAdd = DihedralGroup.r y.toAdd at h
    exact Multiplicative.toAdd.injective (DihedralGroup.r.inj h)
  · intro g; constructor
    · rintro ⟨j, rfl⟩; exact ⟨j.toAdd, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨Multiplicative.ofAdd j, rfl⟩
  · change Nat.card (ZMod 4) = 4; simp [Nat.card_eq_fintype_card]
  · exact DihedralGroup.nat_card
  · intro j i; rfl

theorem vertex_stabilizers : VertexStabilizers := by
  refine ⟨?_, ?_, ?_⟩
  · change ∀ g : SquareGroup, vertexMap g 0 = 0 ↔ g = 1 ∨ g = .sr 0
    decide
  · change ∀ j : Vertex, (vertexMap (.r j) 0 = 0 ↔ j = 0) ∧
      (vertexMap ((.r j : SquareGroup) * .sr 0) 0 = 0 ↔ j = 0)
    decide
  · ext j
    change j.toAdd + 0 = 0 ↔ j = 1
    constructor
    · intro h; apply Multiplicative.toAdd.injective; simpa using h
    · rintro rfl; rfl

/-- A pullback coloring is fixed exactly when the forward motion preserves colors. -/
lemma color_fixed_iff {G : Type*} [Group G] [MulAction G Vertex]
    (q : ℕ) (g : G) (c : Coloring q) :
    g • c = c ↔ ∀ i : Vertex, c (g • i) = c i := by
  constructor
  · intro h i
    have hi := congrFun h (g • i)
    change c (g⁻¹ • (g • i)) = c (g • i) at hi
    simpa using hi.symm
  · intro h
    funext i
    change c (g⁻¹ • i) = c i
    simpa using (h (g⁻¹ • i)).symm

theorem coloring_laws : ColoringLaws := by
  intro q
  exact ⟨fun _ _ _ => rfl, one_smul _, mul_smul,
    fun g c => MulAction.mem_stabilizer_iff.trans (color_fixed_iff q g c),
    fun _ _ _ => rfl⟩

lemma oneRed_stabilizer {G : Type*} [Group G] [MulAction G Vertex]
    {q : ℕ} (red blue : Fin q) (hne : red ≠ blue) :
    MulAction.stabilizer G (oneRed red blue) = MulAction.stabilizer G (0 : Vertex) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, color_fixed_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h0 := h 0
    by_contra hn
    simp [oneRed, hn] at h0
    exact hne h0.symm
  · intro h i
    have hi : g • i = (0 : Vertex) ↔ i = 0 := by
      simpa only [h] using
        ((MulAction.injective g : Function.Injective (fun x : Vertex => g • x)).eq_iff
          (a := i) (b := (0 : Vertex)))
    simp only [oneRed, hi]

theorem special_coloring_stabilizers : SpecialColoringStabilizers := by
  refine ⟨?_, ?_, ?_⟩
  · intro q a
    constructor <;>
      apply (Subgroup.eq_top_iff' _).mpr <;>
      intro g <;>
      apply MulAction.mem_stabilizer_iff.mpr <;>
      rfl
  · exact fun _ red blue hne => oneRed_stabilizer red blue hne
  · intro q red blue hne
    rw [oneRed_stabilizer red blue hne, vertex_stabilizers.2.2]

/-- Propagate preservation around any number of turns of a single permutation. -/
lemma color_pow_preserved (q : ℕ) (g : SquareGroup) (c : Coloring q)
    (h : ∀ i : Vertex, c (g • i) = c i) (n : ℕ) (i : Vertex) :
    c ((vertexPermutation g ^ n) i) = c i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact (h _).trans ih

theorem fixed_iff_cycle_constant : FixedIffCycleConstant := by
  intro q g c
  rw [color_fixed_iff]
  constructor
  · intro h i j hij
    obtain ⟨n, rfl⟩ := hij.exists_nat_pow_eq
    exact (color_pow_preserved q g c h n i).symm
  · intro h i
    exact (h i (g • i) ⟨1, rfl⟩).symm

/-- A fixed coloring is precisely an arbitrary coloring of the cycle quotient. -/
def fixedColoringEquiv (q : ℕ) (g : SquareGroup) :
    {c : Coloring q // g • c = c} ≃ (Cycles g → Fin q) where
  toFun c := Quotient.lift c.1 ((fixed_iff_cycle_constant q g c.1).mp c.2)
  invFun f := ⟨fun i => f (Quotient.mk _ i), by
    apply (fixed_iff_cycle_constant q g _).mpr
    intro i j hij
    exact congrArg f (Quotient.sound hij)⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv f := by funext x; induction x using Quotient.inductionOn; rfl

theorem fixed_coloring_count : FixedColoringCount := by
  intro q g
  rw [Nat.card_congr (fixedColoringEquiv q g), Nat.card_fun]
  simp [cycleCount]

instance (g : SquareGroup) : Fintype (Cycles g) :=
  @Quotient.fintype Vertex inferInstance _
    (inferInstanceAs (DecidableRel (vertexPermutation g).SameCycle))

theorem cycle_counts : CycleCounts := by
  unfold CycleCounts cycleCount
  simp only [Nat.card_eq_fintype_card]
  decide

lemma fixed_rotation_count (q : ℕ) (j : Rotations) :
    Nat.card {c : Coloring q // j • c = c} = q ^ cycleCount (rotationInclusion j) := by
  change Nat.card {c : Coloring q // rotationInclusion j • c = c} = _
  exact fixed_coloring_count q _

lemma rotation_fixed_sum (q : ℕ) :
    (∑ j : Rotations, Nat.card {c : Coloring q // j • c = c}) = q^4 + q^2 + 2*q := by
  simp only [fixed_rotation_count]
  rw [← Multiplicative.ofAdd.sum_comp]
  change (∑ j : Fin 4, q ^ cycleCount (.r j)) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change q ^ cycleCount (.r 0) + (q ^ cycleCount (.r 1) +
    (q ^ cycleCount (.r 2) + q ^ cycleCount (.r 3))) = _
  rw [cycle_counts.1, cycle_counts.2.1, cycle_counts.2.2.1, cycle_counts.2.2.2.1]
  ring

lemma square_fixed_sum (q : ℕ) :
    (∑ g : SquareGroup, Nat.card {c : Coloring q // g • c = c}) =
      q^4 + 2*q^3 + 3*q^2 + 2*q := by
  simp only [fixed_coloring_count q]
  rw [← (DihedralGroup.equivSum (n:=4)).symm.sum_comp, Fintype.sum_sum_type]
  change (∑ j : Fin 4, q ^ cycleCount (.r j)) +
    (∑ j : Fin 4, q ^ cycleCount (.sr j)) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (q ^ cycleCount (.r 0) + (q ^ cycleCount (.r 1) +
    (q ^ cycleCount (.r 2) + q ^ cycleCount (.r 3)))) +
    (q ^ cycleCount (.sr 0) + (q ^ cycleCount (.sr 1) +
    (q ^ cycleCount (.sr 2) + q ^ cycleCount (.sr 3)))) = _
  rcases cycle_counts with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  rw [h0,h1,h2,h3,h4,h5,h6,h7]
  ring

theorem exact_averages : ExactAverages := by
  intro q
  constructor
  · have h := Burnside.counting_identity Rotations (Coloring q)
    have hf : Fintype.ofFinite Rotations = (inferInstance : Fintype Rotations) := Subsingleton.elim _ _
    rw [hf] at h
    change 4 * Nat.card (MulAction.orbitRel.Quotient Rotations (Coloring q)) = _
    rw [← rotation_fixed_sum q]
    simpa only [rotation_identification.2.2.1] using h
  · have h := Burnside.counting_identity SquareGroup (Coloring q)
    have hf : Fintype.ofFinite SquareGroup = (inferInstance : Fintype SquareGroup) := Subsingleton.elim _ _
    rw [hf] at h
    change 8 * Nat.card (MulAction.orbitRel.Quotient SquareGroup (Coloring q)) = _
    rw [← square_fixed_sum q]
    simpa only [rotation_identification.2.2.2.1] using h

theorem orbit_formulas : OrbitFormulas := by
  intro q
  constructor
  · rw [← (exact_averages q).1, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  · rw [← (exact_averages q).2, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]

theorem three_colors : ThreeColors := by
  obtain ⟨hr, hs⟩ := orbit_formulas 3
  norm_num at hr hs
  exact ⟨hr, hs, by omega⟩

theorem different_equivalence_relations : DifferentEquivalenceRelations := by
  constructor
  · intro c d h
    obtain ⟨j, hj⟩ := h
    exact ⟨rotationInclusion j, hj⟩
  · let c : Coloring 3 := fun i => if i = 0 ∨ i = 1 then 0 else if i = 2 then 1 else 2
    refine ⟨(DihedralGroup.sr 0 : SquareGroup) • c, c, ?_, ?_⟩
    · exact ⟨.sr 0, rfl⟩
    · change ¬ ∃ j : Rotations, j • c = (DihedralGroup.sr 0 : SquareGroup) • c
      decide

end D07.Ch05.ActionExamplesChecked
