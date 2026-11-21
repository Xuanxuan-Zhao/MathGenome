import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.OrthantLorentzCones
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.SingularSchurComplement
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.ConicRepresentations

noncomputable section
open scoped InnerProductSpace
universe u v
namespace VariationalNotes.Ch05.ConicRepresentations

def standardCone : Specs.standardConeType.{u,v} := @Specs.standardCone
def standardMap : Specs.standardMapType.{u,v} := @Specs.standardMap
def standardLift : Specs.standardLiftType.{u,v} := @Specs.standardLift
def standardCost : Specs.standardCostType.{u,v} := @Specs.standardCost

theorem lorentz_representation : Specs.lorentz_representation.{u,v} := by
  intro m n _ _ B d a x β
  rfl

/-- Specializing the block quadratic form to the identity gives the exact
Euclidean squared norm epigraph, without any positive dimension assumption. -/
lemma identity_schur {n : Type v} [Fintype n] [DecidableEq n]
    (w : EuclideanSpace ℝ n) (t : ℝ) :
    (SingularSchurComplement.Specs.schurBlock (1 : Matrix n n ℝ) t w).PosSemidef ↔
      ‖w‖ ^ 2 ≤ t := by
  rw [SingularSchurComplement.block_posSemidef_iff _ Matrix.isHermitian_one]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply]
  constructor
  · intro h
    have hn := h 1 (-w)
    simp only [one_pow, one_mul, inner_neg_right, inner_neg_left,
      real_inner_self_eq_norm_sq] at hn
    linarith
  · intro ht r v
    have he := SingularSchurComplement.complete_square
      (LinearMap.id : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n)
      (by intro x y; rfl) w w rfl t r v
    simp only [LinearMap.id_apply, real_inner_self_eq_norm_sq] at he
    rw [real_inner_self_eq_norm_sq, he]
    exact add_nonneg (mul_nonneg (sq_nonneg r) (sub_nonneg.mpr ht)) (sq_nonneg _)

theorem squared_norm_representation : Specs.squared_norm_representation.{u,v} := by
  intro m n _ _ _ B d x t
  exact (identity_schur (B x + d) t).symm

theorem standardCone_properties : Specs.standardCone_properties.{u,v} := by
  intro X _ _ Y _ _ K hclosed hcone
  have hc : VariationalNotes.ConvexGeometry.Specs.IsCone (Specs.standardCone (X := X) K) := by
    refine ⟨⟨Set.mem_univ _, hcone.1⟩, ?_, ?_⟩
    · intro x y hx hy
      exact ⟨Set.mem_univ _, hcone.2.1 hx.2 hy.2⟩
    · intro r hr x hx
      exact ⟨Set.mem_univ _, hcone.2.2 r hr hx.2⟩
  refine ⟨?_, VariationalNotes.ConvexGeometry.cone_convex _ hc, hc⟩
  change IsClosed (WithLp.ofLp ⁻¹' (Set.univ ×ˢ K))
  exact (isClosed_univ.prod hclosed).preimage
    (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).continuous

theorem standard_feasibility : Specs.standard_feasibility.{u,v} := by
  intro X _ _ _ Y _ _ _ K A d p
  change ((p.fst ∈ Set.univ ∧ p.snd ∈ K) ∧ p.snd - A p.fst = d) ↔ _
  constructor
  · rintro ⟨⟨_, hp⟩, he⟩
    have hs : p.snd = A p.fst + d := by
      rw [sub_eq_iff_eq_add] at he
      simpa only [add_comm] using he
    refine ⟨hs ▸ hp, ?_⟩
    apply (WithLp.linearEquiv 2 ℝ (X × Y)).injective
    exact Prod.ext rfl hs
  · rintro ⟨hp, he⟩
    have hs : p.snd = A p.fst + d := congrArg WithLp.snd he
    exact ⟨⟨Set.mem_univ _, hs.symm ▸ hp⟩, by rw [hs]; abel⟩

theorem standard_feasible_lift : Specs.standard_feasible_lift.{u,v} := by
  intro X _ _ _ Y _ _ _ K A d x
  rw [standard_feasibility]
  simp [Specs.standardLift]

theorem standard_feasible_exists : Specs.standard_feasible_exists.{u,v} := by
  intro X _ _ _ Y _ _ _ K A d
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨Specs.standardLift A d x, (standard_feasible_lift K A d x).mp hx⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.fst, ((standard_feasibility K A d p).mp hp).1⟩

theorem standard_objective : Specs.standard_objective.{u,v} := by
  intro X _ _ _ Y _ _ _ c p
  simp [Specs.standardCost, WithLp.prod_inner_apply]

theorem standard_value : Specs.standard_value.{u,v} := by
  intro X _ _ _ Y _ _ _ K A d c
  unfold ConicProgramModels.Specs.primalValue
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun hx => ?_
    calc
      _ ≤ (inner ℝ (Specs.standardCost c) (Specs.standardLift A d x) : EReal) :=
        iInf₂_le (Specs.standardLift A d x) ((standard_feasible_lift K A d x).mp hx)
      _ = (inner ℝ c x : EReal) := by rw [standard_objective]; rfl
  · refine le_iInf fun p => le_iInf fun hp => ?_
    calc
      _ ≤ (inner ℝ c p.fst : EReal) :=
        iInf₂_le p.fst ((standard_feasibility K A d p).mp hp).1
      _ = (inner ℝ (Specs.standardCost c) p : EReal) := by rw [standard_objective]

end VariationalNotes.Ch05.ConicRepresentations
