import MathGenome.Internal.ExtremalOptimization.Specs.P205.LinearProgramming.StandardForm
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.LinearProgramStandardForm

noncomputable section
open Matrix Set
open VariationalNotes.Ch05
universe u v w z
namespace P205.LinearProgramming.StandardForm

variable {E : Type u} {U : Type v} {L : Type w} {N : Type z}
variable [Fintype E] [Fintype U] [Fintype L] [Fintype N]

/-- Negating every lower row yields exactly the original feasible set. -/
theorem normalization :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, LinearProgramStandardForm.feasible (toProblem P) x ↔ feasible P x := by
  intro E U L N _ _ _ _ P x
  constructor
  · rintro ⟨hi, he⟩
    refine ⟨he, fun i => hi (.inl i), fun i => ?_⟩
    have h := hi (.inr i)
    change ((-P.lower) *ᵥ x) i ≤ -P.lowerBound i at h
    simpa only [neg_mulVec, Pi.neg_apply, neg_le_neg_iff] using h
  · rintro ⟨he, hu, hl⟩
    refine ⟨?_, he⟩
    rintro (i | i)
    · exact hu i
    · change ((-P.lower) *ᵥ x) i ≤ -P.lowerBound i
      simpa only [neg_mulVec, Pi.neg_apply, neg_le_neg_iff] using hl i

theorem decode_lift :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, decode (lift P x) = x := by
  intro E U L N _ _ _ _ P x
  exact LinearProgramStandardForm.decode_lift (toProblem P) x

theorem standard_feasible_iff :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) q,
    LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q ↔
    (∀ j, 0 ≤ q j) ∧ feasible P (decode q) ∧
      ∀ i, q (.inr (.inr i)) = (toProblem P).ineqBound i - ((toProblem P).ineq *ᵥ decode q) i := by
  intro E U L N _ _ _ _ P q
  simpa only [normalization] using LinearProgramStandardForm.standard_feasible_iff (toProblem P) q

theorem lift_feasible :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, feasible P x →
    LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) (lift P x) := by
  intro E U L N _ _ _ _ P x hx
  exact LinearProgramStandardForm.lift_feasible (toProblem P) x ((normalization P x).mpr hx)

theorem feasible_correspondence :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, feasible P x ↔
    ∃ q, LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q ∧ decode q = x := by
  intro E U L N _ _ _ _ P x
  simpa only [normalization] using LinearProgramStandardForm.feasible_correspondence (toProblem P) x

theorem objective_preserved :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) q,
    LinearProgramModels.Specs.primalObjective (standardCost P) q = objective P (decode q) := by
  intro E U L N _ _ _ _ P q
  exact LinearProgramStandardForm.objective_preserved (toProblem P) q

theorem objective_range_eq :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N), values P =
    LinearProgramModels.Specs.primalObjective (standardCost P) '' {q | LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q} := by
  intro E U L N _ _ _ _ P
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨lift P x, lift_feasible P x hx, by rw [objective_preserved, decode_lift]⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨decode q, ((standard_feasible_iff P q).mp hq).2.1, (objective_preserved P q).symm⟩

theorem infimum_preserved :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N), infimum P =
    LinearProgramModels.Specs.primalValue (standardMatrix P) (standardBound P) (standardCost P) := by
  intro E U L N _ _ _ _ P
  unfold infimum LinearProgramModels.Specs.primalValue
  rw [objective_range_eq, Set.image_image]

theorem optimal_correspondence :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) q,
    LinearProgramModels.Specs.PrimalOptimal (standardMatrix P) (standardBound P) (standardCost P) q ↔
    LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q ∧ Minimizes P (decode q) := by
  intro E U L N _ _ _ _ P q
  rw [LinearProgramModels.primalOptimal_iff]
  constructor
  · rintro ⟨hq, hmin⟩
    refine ⟨hq, ((standard_feasible_iff P q).mp hq).2.1, ?_⟩
    intro x hx
    have h := hmin (lift P x) (lift_feasible P x hx)
    simpa only [objective_preserved, decode_lift] using h
  · rintro ⟨hq, _, hmin⟩
    refine ⟨hq, ?_⟩
    intro r hr
    simpa only [objective_preserved] using hmin (decode r) (((standard_feasible_iff P r).mp hr).2.1)

theorem attainment_correspondence :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) (p : ℝ),
    (∃ x, Minimizes P x ∧ objective P x = p) ↔
    LinearProgramModels.Specs.PrimalAttains (standardMatrix P) (standardBound P) (standardCost P) p := by
  intro E U L N _ _ _ _ P p
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨lift P x, (optimal_correspondence P _).mpr ⟨lift_feasible P x hx.1, ?_⟩, ?_⟩
    · rwa [decode_lift]
    · rw [objective_preserved, decode_lift, hp]
  · rintro ⟨q, hq, hp⟩
    exact ⟨decode q, ((optimal_correspondence P q).mp hq).2, by rwa [← objective_preserved]⟩

theorem infeasible_correspondence :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N), (¬ ∃ x, feasible P x) ↔
    ¬ ∃ q, LinearProgramModels.Specs.primalFeasible (standardMatrix P) (standardBound P) q := by
  intro E U L N _ _ _ _ P
  constructor
  · rintro h ⟨q, hq⟩
    exact h ⟨decode q, ((standard_feasible_iff P q).mp hq).2.1⟩
  · rintro h ⟨x, hx⟩
    exact h ⟨lift P x, lift_feasible P x hx⟩

theorem unbounded_correspondence :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N),
    (∀ r : ℝ, ∃ x, feasible P x ∧ objective P x < r) ↔
    LinearProgramModels.Specs.PrimalUnbounded (standardMatrix P) (standardBound P) (standardCost P) := by
  intro E U L N _ _ _ _ P
  constructor
  · intro h r
    obtain ⟨x, hx, hxr⟩ := h r
    exact ⟨lift P x, lift_feasible P x hx, by rwa [objective_preserved, decode_lift]⟩
  · intro h r
    obtain ⟨q, hq, hqr⟩ := h r
    exact ⟨decode q, ((standard_feasible_iff P q).mp hq).2.1, by rwa [← objective_preserved]⟩

theorem negation_feasible :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, feasible (negateCost P) x ↔ feasible P x := by
  intro E U L N _ _ _ _ P x
  rfl

theorem negation_objective :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, objective (negateCost P) x = -objective P x := by
  intro E U L N _ _ _ _ P x
  exact neg_dotProduct _ _

theorem negation_range :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N), values (negateCost P) = Neg.neg '' values P := by
  intro E U L N _ _ _ _ P
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨objective P x, ⟨x, hx, rfl⟩, (negation_objective P x).symm⟩
  · rintro ⟨s, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, negation_objective P x⟩

theorem negation_optimal :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) x, Minimizes (negateCost P) x ↔ Maximizes P x := by
  intro E U L N _ _ _ _ P x
  simp only [Minimizes, Maximizes, negation_feasible, negation_objective, neg_le_neg_iff]

omit [Fintype E] [Fintype U] [Fintype L] [Fintype N] in
@[simp] lemma negation_matrix (P : Problem E U L N) :
    standardMatrix (negateCost P) = standardMatrix P := rfl
omit [Fintype E] [Fintype U] [Fintype L] [Fintype N] in
@[simp] lemma negation_bound (P : Problem E U L N) :
    standardBound (negateCost P) = standardBound P := rfl

theorem maximization_attainment :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N) (p : ℝ),
    (∃ x, Maximizes P x ∧ objective P x = p) ↔
    LinearProgramModels.Specs.PrimalAttains (standardMatrix P) (standardBound P) (standardCost (negateCost P)) (-p) := by
  intro E U L N _ _ _ _ P p
  have h := attainment_correspondence (negateCost P) (-p)
  simp only [negation_matrix, negation_bound] at h
  rw [← h]
  simp only [negation_optimal, negation_objective, neg_inj]

theorem maximization_unbounded :
  ∀ {E : Type u} {U : Type v} {L : Type w} {N : Type z}
    [Fintype E] [Fintype U] [Fintype L] [Fintype N],
  ∀ (P : Problem E U L N),
    (∀ r : ℝ, ∃ x, feasible P x ∧ r < objective P x) ↔
    LinearProgramModels.Specs.PrimalUnbounded (standardMatrix P) (standardBound P) (standardCost (negateCost P)) := by
  intro E U L N _ _ _ _ P
  have h := unbounded_correspondence (negateCost P)
  simp only [negation_matrix, negation_bound] at h
  rw [← h]
  simp only [negation_feasible, negation_objective]
  constructor
  · intro h r
    obtain ⟨x, hx, hr⟩ := h (-r)
    exact ⟨x, hx, by linarith⟩
  · intro h r
    obtain ⟨x, hx, hr⟩ := h (-r)
    exact ⟨x, hx, by linarith⟩

theorem negation_value : Specs.negation_value.{u,v,w,z} := by
  intro E U L N _ _ _ _ P
  unfold infimum supremum
  rw [negation_range]
  have hs : ((fun t : ℝ => (t : EReal)) '' (Neg.neg '' values P)) =
      Neg.neg '' ((fun t : ℝ => (t : EReal)) '' values P) := by
    rw [Set.image_image, Set.image_image]
    congr 1
  rw [hs]
  have h := (EReal.negOrderIso.map_sSup ((fun t : ℝ => (t : EReal)) '' values P)).symm
  change (⨅ a ∈ ((fun t : ℝ => (t : EReal)) '' values P), -a) =
    -sSup ((fun t : ℝ => (t : EReal)) '' values P) at h
  simpa only [sInf_image] using h

omit [Fintype N] in
/-- The signed lower rows and the sign change of every dual multiplier
turn the minimization stationarity equation into the maximization one. -/
lemma max_stationarity (P : Problem E U L N) (a : U → ℝ) (d : L → ℝ) (e : E → ℝ) :
    (toProblem (negateCost P)).ineqᵀ *ᵥ Sum.elim (-a) d +
      (toProblem (negateCost P)).eqnᵀ *ᵥ (-e) =
    -(P.upperᵀ *ᵥ a + P.lowerᵀ *ᵥ d + P.equalityᵀ *ᵥ e) := by
  ext j
  simp [toProblem, negateCost, mulVec, dotProduct, Matrix.transpose, Sum.elim,
    Fintype.sum_sum_type, neg_mul, mul_neg, Finset.sum_neg_distrib]
  ring

theorem maximization_dual : Specs.maximization_dual.{u,v,w,z} := by
  intro E U L N _ _ _ _ P a d e
  change LinearProgramModels.Specs.dualFeasible (standardMatrix (negateCost P))
    (standardCost (negateCost P)) (maxJoinDual a d e) ↔ _
  refine (LinearProgramStandardForm.dual_feasible_iff
    (toProblem (negateCost P)) (Sum.elim (-a) d) (-e)).trans ?_
  change ((∀ i, (Sum.elim (-a) d) i ≤ 0) ∧
    (toProblem (negateCost P)).ineqᵀ *ᵥ Sum.elim (-a) d +
      (toProblem (negateCost P)).eqnᵀ *ᵥ (-e) = -P.cost) ↔ _
  rw [max_stationarity, neg_inj]
  simp only [maxDualFeasible, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    Pi.neg_apply, neg_nonpos, and_assoc]

theorem max_dual_surjective : Specs.max_dual_surjective.{u,v,w,z} := by
  intro E U L N _ _ _ _ _P r
  refine ⟨(fun i => -r (.inl (.inl i))), (fun i => r (.inl (.inr i))),
    (fun i => -r (.inr i)), ?_⟩
  funext i
  rcases i with (i | i) | i <;> simp [maxJoinDual, LinearProgramStandardForm.joinDual]

theorem maximization_dual_objective : Specs.maximization_dual_objective.{u,v,w,z} := by
  intro E U L N _ _ _ _ P a d e
  calc
    _ = LinearProgramStandardForm.dualObjective (toProblem P) (Sum.elim (-a) d) (-e) :=
      LinearProgramStandardForm.dual_objective_preserved (toProblem P) (Sum.elim (-a) d) (-e)
    _ = _ := by
      simp [LinearProgramStandardForm.dualObjective, toProblem, maxDualObjective,
        dotProduct, Fintype.sum_sum_type, mul_neg, neg_mul, Finset.sum_neg_distrib]
      ring

theorem nonnegative_max_dual : Specs.nonnegative_max_dual.{u,v} := by
  intro R C _ _ A c p
  classical
  have hcol (j : C) : ((withSlacks A)ᵀ *ᵥ (-p)) (.inl j) = -(Aᵀ *ᵥ p) j := by
    simp [withSlacks, mulVec, dotProduct, mul_neg, Finset.sum_neg_distrib]
  have hslack (i : R) : ((withSlacks A)ᵀ *ᵥ (-p)) (.inr i) = -p i := by
    simp [withSlacks, mulVec, dotProduct]
  constructor
  · constructor
    · intro h
      exact ⟨fun i => by simpa [hslack] using h (.inr i),
        fun j => by simpa [hcol] using h (.inl j)⟩
    · rintro ⟨hp, hc⟩ (j | i)
      · simpa [hcol] using hc j
      · simpa [hslack] using hp i
  · change (∀ j, (Aᵀ *ᵥ (-p)) j ≤ (-c) j) ↔ _
    simp only [mulVec_neg, Pi.neg_apply, neg_le_neg_iff]

end P205.LinearProgramming.StandardForm
