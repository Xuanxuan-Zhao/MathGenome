import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.WeightedDuality
import MathGenome.Internal.ExtremalOptimization.P205.Matching.BipartiteHulls
import MathGenome.Internal.ExtremalOptimization.P205.LinearProgramming.Certificates
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
open scoped BigOperators
open Matrix Set
universe u v
namespace P205.Matching.WeightedDuality
open WeightedSpecs
open VariationalNotes.Ch05.LinearProgramModels

variable {L : Type u} {R : Type v} [Fintype L] [Fintype R]
  {G : BipartiteGraph L R}

lemma matrix_mul (q : Edge G ⊕ (L ⊕ R) → ℝ) (z : L ⊕ R) :
    (standardMatrix G *ᵥ q) z = load (fun e => q (.inl e)) z + q (.inr z) := by
  classical
  simp [standardMatrix, mulVec, dotProduct, Fintype.sum_sum_type,
    load, Specs.P205.Matching.load]

lemma transpose_edge (u : L → ℝ) (v : R → ℝ) (e : Edge G) :
    ((standardMatrix G)ᵀ *ᵥ (-Sum.elim u v)) (.inl e) =
      -(u e.val.1 + v e.val.2) := by
  classical
  have hcol : (standardMatrix G)ᵀ (.inl e) =
      Sum.elim (fun i : L => if i = e.val.1 then (1 : ℝ) else 0)
        (fun j : R => if j = e.val.2 then (1 : ℝ) else 0) := by
    funext z
    cases z with
    | inl i =>
      change ((↑(if i = e.val.1 then (1 : ℤ) else 0)) : ℝ) =
        if i = e.val.1 then 1 else 0
      split_ifs <;> norm_num
    | inr j =>
      change ((↑(if j = e.val.2 then (1 : ℤ) else 0)) : ℝ) =
        if j = e.val.2 then 1 else 0
      split_ifs <;> norm_num
  change (standardMatrix G)ᵀ (.inl e) ⬝ᵥ (-Sum.elim u v) = _
  rw [hcol]
  simp [dotProduct, Fintype.sum_sum_type, ite_mul]

lemma transpose_slack (p : L ⊕ R → ℝ) (z : L ⊕ R) :
    ((standardMatrix G)ᵀ *ᵥ p) (.inr z) = p z := by
  classical
  simp [standardMatrix, mulVec, dotProduct, eq_comm]

theorem primal_correspondence : WeightedSpecs.primal_correspondence.{u,v} := by
  intro L R _ _ G q
  change ((standardMatrix G *ᵥ q = fun _ => 1) ∧ (∀ t, 0 ≤ q t)) ↔ _
  constructor
  · rintro ⟨heq, hn⟩
    have he (z) := congrFun heq z
    simp only [matrix_mul] at he
    exact ⟨fun e => hn (.inl e), fun z => by have := hn (.inr z); linarith [he z],
      fun z => by linarith [he z]⟩
  · rintro ⟨hn, hl, hs⟩
    refine ⟨funext (fun z => ?_), ?_⟩
    · simp only [matrix_mul, hs]; ring
    · rintro (e | z)
      · exact hn e
      · rw [hs]; exact sub_nonneg.mpr (hl z)

theorem dual_correspondence : WeightedSpecs.dual_correspondence.{u,v} := by
  intro L R _ _ G w u v
  change (∀ t, ((standardMatrix G)ᵀ *ᵥ (-Sum.elim u v)) t ≤ standardCost w t) ↔ _
  constructor
  · intro h
    refine ⟨fun e => ?_, fun i => ?_, fun j => ?_⟩
    · have := h (.inl e)
      simpa [transpose_edge, standardCost] using this
    · have := h (.inr (.inl i))
      simpa [transpose_slack, standardCost] using this
    · have := h (.inr (.inr j))
      simpa [transpose_slack, standardCost] using this
  · rintro ⟨he, hu, hv⟩ (e | (i | j))
    · simpa [transpose_edge, standardCost] using he e
    · simpa [transpose_slack, standardCost] using hu i
    · simpa [transpose_slack, standardCost] using hv j

theorem objective_correspondence : WeightedSpecs.objective_correspondence.{u,v} := by
  intro L R _ _ G w q u v
  constructor
  · simp [VariationalNotes.Ch05.LinearProgramModels.Specs.primalObjective,
      standardCost, dotProduct, Fintype.sum_sum_type,
      Specs.P205.Matching.totalWeight, Finset.sum_neg_distrib]
  · simp [VariationalNotes.Ch05.LinearProgramModels.Specs.dualObjective,
      dotProduct, Fintype.sum_sum_type, Specs.P205.Matching.potentialSum,
      Finset.sum_neg_distrib]

lemma lift_feasible {x : Edge G → ℝ}
    (hx : (∀ e, 0 ≤ x e) ∧ ∀ z, load x z ≤ 1) :
    primalFeasible (standardMatrix G) (fun _ => 1) (lift x) := by
  apply (primal_correspondence G _).mpr
  exact ⟨hx.1, hx.2, fun _ => rfl⟩

theorem weak_duality : WeightedSpecs.weak_duality.{u,v} := by
  intro L R _ _ G w M u v hM huv
  have h := LinearProgramming.Certificates.weak_duality
    (standardMatrix G) (fun _ => 1) (standardCost w) (lift (indicator M))
    (-Sum.elim u v) (lift_feasible (indicator_feasible hM))
    ((dual_correspondence G w u v).mpr huv)
  rw [(objective_correspondence G w _ u v).1,
    (objective_correspondence G w (lift (indicator M)) u v).2] at h
  exact neg_le_neg_iff.mp h

/-- A maximum over the finite set of matchings bounds the entire degree
relaxation, by its exact convex-hull representation. -/
lemma matching_maximizes_relaxation (w : Edge G → ℝ) :
    ∃ M : Set (Edge G), IsMatching M ∧
      ∀ x, (∀ e, 0 ≤ x e) → (∀ z, load x z ≤ 1) →
        totalWeight w x ≤ matchingWeight w M := by
  classical
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun N : Set (Edge G) => IsMatching N))
    (matchingWeight w) ⟨∅, by simp [empty_matching]⟩
  refine ⟨M, (Finset.mem_filter.mp hM).2, ?_⟩
  let f : (Edge G → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ w
  have hb : convexHull ℝ {x : Edge G → ℝ | ∃ N, IsMatching N ∧ x = indicator N} ⊆
      {x | totalWeight w x ≤ matchingWeight w M} := by
    apply convexHull_min
    · rintro x ⟨N, hN, rfl⟩
      exact hmax N (by simp [hN])
    · exact (convex_Iic _).linear_preimage f
  rw [matching_hull G] at hb
  exact fun x hn hl => hb ⟨hn, hl⟩

lemma equality_implies_joint {w : Edge G → ℝ} {M : Set (Edge G)}
    {u : L → ℝ} {v : R → ℝ} (hM : IsMatching M)
    (huv : NonnegativeFeasible w u v) (he : matchingWeight w M = potentialSum u v) :
    JointOptimal w M u v := by
  constructor
  · intro N hN
    exact (weak_duality G w N u v hN huv).trans_eq he.symm
  · intro a b hab
    exact he.symm.le.trans (weak_duality G w M a b hM hab)

theorem attained_duality : WeightedSpecs.attained_duality.{u,v} := by
  intro L R _ _ G w
  obtain ⟨M, hM, hmax⟩ := matching_maximizes_relaxation w
  let q := lift (indicator M)
  have hq : primalFeasible (standardMatrix G) (fun _ => 1) q :=
    lift_feasible (indicator_feasible hM)
  have ho : PrimalOptimal (standardMatrix G) (fun _ => 1) (standardCost w) q := by
    apply (primalOptimal_iff _ _ _ _).mpr
    refine ⟨hq, ?_⟩
    intro r hr
    obtain ⟨hn, hl, _⟩ := (primal_correspondence G r).mp hr
    rw [(objective_correspondence G w q (fun _ => 0) (fun _ => 0)).1,
      (objective_correspondence G w r (fun _ => 0) (fun _ => 0)).1]
    exact neg_le_neg (hmax _ hn hl)
  have hvalue : primalValue (standardMatrix G) (fun _ => 1) (standardCost w) =
      ((-matchingWeight w M : ℝ) : EReal) := by
    have heobj : primalObjective (standardCost w) q = -matchingWeight w M :=
      (objective_correspondence G w q (fun _ => 0) (fun _ => 0)).1
    exact ho.2.trans (congrArg (fun t : ℝ => (t : EReal)) heobj)
  obtain ⟨_, y, _, hy, _, he⟩ := LinearProgramming.Certificates.finite_infimum_attained
    (standardMatrix G) (fun _ => 1) (standardCost w) (-matchingWeight w M) ⟨q, hq⟩ hvalue
  let u : L → ℝ := fun i => -y (.inl i)
  let v : R → ℝ := fun j => -y (.inr j)
  have hyuv : y = -Sum.elim u v := by
    funext z
    cases z <;> simp [u, v]
  have huv : NonnegativeFeasible w u v :=
    (dual_correspondence G w u v).mp (hyuv ▸ hy.1)
  have heq : matchingWeight w M = potentialSum u v := by
    rw [hyuv, (objective_correspondence G w q u v).2] at he
    exact (neg_inj.mp he).symm
  exact ⟨M, u, v, hM, huv, heq, equality_implies_joint hM huv heq⟩

/-- A matching has load one at covered vertices and zero at every other vertex. -/
lemma matching_load {M : Set (Edge G)} (hM : IsMatching M) (z : L ⊕ R) :
    load (indicator M) z = (by classical exact if Covered M z then 1 else 0) := by
  classical
  rw [load_indicator]
  have hd := (matching_iff_degree M).mp hM z
  by_cases hz : Covered M z
  · rw [ite_eq_left hz]
    have hp := (covered_iff_degree_pos M z).mp hz
    have he : degree M z = 1 := by omega
    simp [he]
  · rw [ite_eq_right hz]
    have hp := mt (covered_iff_degree_pos M z).mpr hz
    have he : degree M z = 0 := by omega
    simp [he]

theorem equality_iff_certificate : WeightedSpecs.equality_iff_certificate.{u,v} := by
  intro L R _ _ G w M u v hM huv
  classical
  have hp := lift_feasible (indicator_feasible hM)
  have hd := (dual_correspondence G w u v).mpr huv
  have heq := LinearProgramming.Certificates.objective_eq_iff_complementarity
    (standardMatrix G) (fun _ => 1) (standardCost w) (lift (indicator M))
    (-Sum.elim u v) hp hd
  rw [(objective_correspondence G w (lift (indicator M)) u v).1,
    (objective_correspondence G w (lift (indicator M)) u v).2] at heq
  have heq' : matchingWeight w M = potentialSum u v ↔
      ∀ t, lift (indicator M) t * (standardCost w t -
        ((standardMatrix G)ᵀ *ᵥ (-Sum.elim u v)) t) = 0 := by
    simpa only [lift, Sum.elim_inl, neg_inj,
      matchingWeight, Specs.P205.Matching.matchingWeight] using heq
  apply heq'.trans
  constructor
  · intro hc
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      have hh := hc (.inl e)
      rw [transpose_edge] at hh
      have hh' : -(w e) - -(u e.val.1 + v e.val.2) = 0 := by
        simpa [lift, standardCost, Specs.P205.Matching.indicator, he] using hh
      change u e.val.1 + v e.val.2 = w e
      linarith
    · intro i hi
      have hh := hc (.inr (.inl i))
      rw [transpose_slack] at hh
      simpa [lift, standardCost, matching_load hM, hi] using hh
    · intro j hj
      have hh := hc (.inr (.inr j))
      rw [transpose_slack] at hh
      simpa [lift, standardCost, matching_load hM, hj] using hh
  · rintro ⟨ht, hu, hv⟩ (e | (i | j))
    · rw [transpose_edge]
      by_cases he : e ∈ M
      · have hh := ht e he
        change u e.val.1 + v e.val.2 = w e at hh
        simp [lift, standardCost, Specs.P205.Matching.indicator, he, hh]
      · simp [lift, standardCost, Specs.P205.Matching.indicator, he]
    · rw [transpose_slack]
      by_cases hi : Covered M (.inl i)
      · simp [lift, standardCost, matching_load hM, hi]
      · simp [lift, standardCost, matching_load hM, hi, hu i hi]
    · rw [transpose_slack]
      by_cases hj : Covered M (.inr j)
      · simp [lift, standardCost, matching_load hM, hj]
      · simp [lift, standardCost, matching_load hM, hj, hv j hj]

theorem joint_optimality_iff_certificate :
    WeightedSpecs.joint_optimality_iff_certificate.{u,v} := by
  intro L R _ _ G w M u v hM huv
  rw [← equality_iff_certificate G w M u v hM huv]
  constructor
  · intro h
    obtain ⟨N, a, b, hN, hab, heq, _⟩ := attained_duality G w
    have h₁ := h.1 N hN
    have h₂ := h.2 a b hab
    have h₃ := weak_duality G w M u v hM huv
    linarith
  · exact equality_implies_joint hM huv

end P205.Matching.WeightedDuality
