import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.PerfectAssignment
import MathGenome.Internal.ExtremalOptimization.P205.Matching.BipartiteHulls
import MathGenome.Internal.ExtremalOptimization.P205.LinearProgramming.Certificates

noncomputable section
open scoped BigOperators
open Matrix
universe u v
namespace P205.Matching.PerfectAssignment
open P205.Matching
open VariationalNotes.Ch05.LinearProgramModels.Specs

/-- Degree equalities, including all isolated vertices, in standard LP form. -/
theorem degree_lp : AssignmentSpecs.degree_lp.{u,v} := by
  intro L R _ _ G x
  change ((AssignmentSpecs.matrix G) *ᵥ x = (fun _ => 1) ∧ ∀ e, 0 ≤ x e) ↔ _
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨hn, fun z => congrFun h z⟩
  · rintro ⟨hn, h⟩
    exact ⟨funext h, hn⟩

lemma transpose_mul {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (y : L ⊕ R → ℝ) (e : Edge G) :
    ((AssignmentSpecs.matrix G)ᵀ *ᵥ y) e =
      y (.inl e.val.1) + y (.inr e.val.2) := by
  classical
  have hc (z : L ⊕ R) :
      (AssignmentSpecs.matrix G) z e = if incident z e then 1 else 0 := by
    by_cases hz : incident z e <;>
      simp [AssignmentSpecs.matrix, Specs.P205.Matching.incidence, hz]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hc,
    Fintype.sum_sum_type, Specs.P205.Matching.incident, ite_mul, one_mul, zero_mul]
  simp

lemma transpose_multiplier {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (u : L → ℝ) (v : R → ℝ) (e : Edge G) :
    ((AssignmentSpecs.matrix G)ᵀ *ᵥ AssignmentSpecs.multiplier u v) e =
      -(u e.val.1 + v e.val.2) := by
  simp [transpose_mul, AssignmentSpecs.multiplier, add_comm]

theorem dual_sign : AssignmentSpecs.dual_sign.{u,v} := by
  intro L R _ _ G w u v
  change (∀ e, _ ≤ -w e) ↔ ∀ e, w e ≤ u e.val.1 + v e.val.2
  simp only [transpose_multiplier, neg_le_neg_iff]

theorem objective_bridge : AssignmentSpecs.objective_bridge.{u,v} := by
  intro L R _ _ G w x u v
  constructor
  · change (∑ e, -w e * x e) = -(∑ e, w e * x e)
    simp only [neg_mul, Finset.sum_neg_distrib]
  · change (∑ z, (1 : ℝ) * AssignmentSpecs.multiplier u v z) = _
    simp [Fintype.sum_sum_type, AssignmentSpecs.multiplier,
      Specs.P205.Matching.potentialSum, add_comm]

lemma indicator_primal {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    (G : BipartiteGraph L R) (M : Set (Edge G)) (hM : IsPerfectMatching M) :
    primalFeasible (AssignmentSpecs.matrix G) (fun _ => 1) (indicator M) :=
  (degree_lp G (indicator M)).mpr (perfect_indicator_feasible hM)

theorem weak_duality : AssignmentSpecs.weak_duality.{u,v} := by
  intro L R _ _ G w M u v hM huv
  have h := LinearProgramming.Certificates.weak_duality
    (AssignmentSpecs.matrix G) (fun _ => 1) (fun e => -w e)
    (indicator M) (AssignmentSpecs.multiplier u v) (indicator_primal G M hM)
    ((dual_sign G w u v).mpr huv)
  rw [(objective_bridge G w (indicator M) u v).1,
    (objective_bridge G w (indicator M) u v).2] at h
  exact neg_le_neg_iff.mp h

theorem gap_identity : AssignmentSpecs.gap_identity.{u,v} := by
  intro L R _ _ G w M u v hM
  have h := LinearProgramming.Certificates.gap_identity
    (AssignmentSpecs.matrix G) (fun _ => 1) (fun e => -w e)
    (indicator M) (AssignmentSpecs.multiplier u v) (indicator_primal G M hM)
  rw [(objective_bridge G w (indicator M) u v).1,
    (objective_bridge G w (indicator M) u v).2] at h
  convert h using 1
  · change potentialSum u v - totalWeight w (indicator M) = _
    ring
  · apply Finset.sum_congr rfl
    intro e _
    rw [transpose_multiplier]
    change indicator M e * (u e.val.1 + v e.val.2 - w e) = _
    ring

theorem equality_iff_tight : AssignmentSpecs.equality_iff_tight.{u,v} := by
  intro L R _ _ G w M u v hM huv
  classical
  have h := LinearProgramming.Certificates.objective_eq_iff_complementarity
    (AssignmentSpecs.matrix G) (fun _ => 1) (fun e => -w e)
    (indicator M) (AssignmentSpecs.multiplier u v) (indicator_primal G M hM)
    ((dual_sign G w u v).mpr huv)
  rw [(objective_bridge G w (indicator M) u v).1,
    (objective_bridge G w (indicator M) u v).2, neg_inj] at h
  change (matchingWeight w M = potentialSum u v ↔ _) at h
  rw [h]
  constructor
  · intro hc e he
    have hh := hc e
    rw [transpose_multiplier] at hh
    simp only [indicator, Specs.P205.Matching.indicator, ite_eq_left he, one_mul] at hh
    change u e.val.1 + v e.val.2 = w e
    linarith
  · intro ht e
    rw [transpose_multiplier]
    by_cases he : e ∈ M
    · have hh := ht e he
      change u e.val.1 + v e.val.2 = w e at hh
      rw [hh]
      simp
    · simp [indicator, Specs.P205.Matching.indicator, he]

/-- A linear objective bounded on all perfect indicators has the same bound on
its convex hull, hence on the entire degree-equality relaxation. -/
theorem lp_optimizer : AssignmentSpecs.lp_optimizer.{u,v} := by
  intro L R _ _ G w hex
  classical
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image
    {M : Set (Edge G) | IsPerfectMatching M} (matchingWeight w) (Set.toFinite _) hex
  refine ⟨M, hM, ?_⟩
  let f : (Edge G → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := totalWeight w
      map_add' := by
        intro x y
        change (∑ e, w e * (x e + y e)) = _
        simp only [mul_add, Finset.sum_add_distrib]
        rfl
      map_smul' := by
        intro a x
        change (∑ e, w e * (a * x e)) = a * (∑ e, w e * x e)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring }
  have hsub : convexHull ℝ {x : Edge G → ℝ | ∃ N : Set (Edge G),
      IsPerfectMatching N ∧ x = indicator N} ⊆
      {x | totalWeight w x ≤ matchingWeight w M} := by
    apply convexHull_min
    · rintro x ⟨N, hN, rfl⟩
      exact hmax N hN
    · exact (convex_Iic (matchingWeight w M)).linear_preimage f
  rw [perfect_matching_hull G] at hsub
  intro x hn heq
  exact hsub ⟨hn, heq⟩

/-- Negating an unrestricted LP multiplier gives precisely the two free
potential functions. There is no positivity restriction on either function. -/
theorem attained_duality : AssignmentSpecs.attained_duality.{u,v} := by
  intro L R _ _ G w hex
  obtain ⟨M, hM, hmax⟩ := lp_optimizer G w hex
  have hprimal := indicator_primal G M hM
  have hp : primalValue (AssignmentSpecs.matrix G) (fun _ => 1) (fun e => -w e) =
      ((-matchingWeight w M : ℝ) : EReal) := by
    change sInf ((fun x => (primalObjective (fun e => -w e) x : EReal)) ''
      {x | primalFeasible (AssignmentSpecs.matrix G) (fun _ => 1) x}) = _
    apply le_antisymm
    · apply sInf_le
      refine ⟨indicator M, hprimal, ?_⟩
      exact congrArg (fun t : ℝ => (t : EReal))
        (objective_bridge G w (indicator M) (fun _ => 0) (fun _ => 0)).1
    · apply le_sInf
      rintro z ⟨x, hx, rfl⟩
      obtain ⟨hn, heq⟩ := (degree_lp G x).mp hx
      have hbound : -matchingWeight w M ≤ primalObjective (fun e => -w e) x := by
        calc
          -matchingWeight w M ≤ -totalWeight w x := neg_le_neg (hmax x hn heq)
          _ = primalObjective (fun e => -w e) x :=
            (objective_bridge G w x (fun _ => 0) (fun _ => 0)).1.symm
      exact EReal.coe_le_coe_iff.mpr hbound
  obtain ⟨x, y, _, hy, _, hyp⟩ :=
    LinearProgramming.Certificates.finite_infimum_attained
      (AssignmentSpecs.matrix G) (fun _ => 1) (fun e => -w e)
      (-matchingWeight w M) ⟨indicator M, hprimal⟩ hp
  let u : L → ℝ := fun i => -y (.inl i)
  let v : R → ℝ := fun j => -y (.inr j)
  have hrep : AssignmentSpecs.multiplier u v = y := by
    funext z
    cases z <;> simp [AssignmentSpecs.multiplier, u, v]
  have hfeas : FreeFeasible w u v := by
    apply (dual_sign G w u v).mp
    rw [hrep]
    exact hy.1
  have heq : matchingWeight w M = potentialSum u v := by
    have hobj := (objective_bridge G w (indicator M) u v).2
    rw [hrep, hyp] at hobj
    exact neg_injective hobj
  refine ⟨M, u, v, hM, hfeas, heq, ?_, ?_⟩
  · intro N hN
    obtain ⟨hn, he⟩ := perfect_indicator_feasible hN
    exact hmax (indicator N) hn he
  · intro a b hab
    exact heq.symm.trans_le (weak_duality G w M a b hM hab)

theorem joint_optimal_iff_tight : AssignmentSpecs.joint_optimal_iff_tight.{u,v} := by
  intro L R _ _ G w M u v hM huv
  rw [← equality_iff_tight G w M u v hM huv]
  constructor
  · rintro ⟨hm, hp⟩
    obtain ⟨N, a, b, hN, hab, heq, _, _⟩ := attained_duality G w ⟨M, hM⟩
    exact le_antisymm (weak_duality G w M u v hM huv)
      ((hp a b hab).trans (heq ▸ hm N hN))
  · intro heq
    constructor
    · intro N hN
      rw [heq]
      exact weak_duality G w N u v hN huv
    · intro a b hab
      rw [← heq]
      exact weak_duality G w M a b hM hab

end P205.Matching.PerfectAssignment
