import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SemidirectFaithfulModule
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ReductiveDecomposition
import Mathlib.Tactic.Abel

noncomputable section
namespace LieAlgebrasAndRepresentations.SemidirectFaithfulModule
universe u v w t
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The direct sum of two representations, on the ordinary product module. -/
def productRepresentation {k G V W : Type*} [Field k] [LieRing G] [LieAlgebra k G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : G →ₗ⁅k⁆ Module.End k V) (τ : G →ₗ⁅k⁆ Module.End k W) :
    G →ₗ⁅k⁆ Module.End k (V × W) where
  toLinearMap :=
    { toFun := fun x => (ρ x).prodMap (τ x)
      map_add' := by intro x y; ext z <;> simp
      map_smul' := by intro r x; ext z <;> simp }
  map_lie' := by
    intro x y
    ext z <;> simp only [LieHom.map_lie]
    all_goals rfl

theorem semidirectAction :
    Specs.LieAlgebrasAndRepresentations.SemidirectFaithfulModule.semidirectActionExpected.{u,v,w,t} := by
  intro k _ K _ _ N _ _ V _ _ θ ρ D hcomm
  letI := Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect.semidirect_lie_ring_value θ
  letI := Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect.semidirect_lie_algebra_value θ
  let f : (K × N) →ₗ[k] Module.End k V :=
    (D.toLinearMap.comp (θ.toLinearMap.comp (LinearMap.fst k K N))) +
      (ρ.toLinearMap.comp (LinearMap.snd k K N))
  refine ⟨{ f with map_lie' := ?_ }, fun _ _ => rfl⟩
  rintro ⟨a, x⟩ ⟨b, y⟩
  change D (θ (⁅(a, x), (b, y)⁆.1)) + ρ (⁅(a, x), (b, y)⁆.2) =
    ⁅D (θ a) + ρ x, D (θ b) + ρ y⁆
  change D (θ ⁅a, b⁆) + ρ (⁅x, y⁆ + θ a y - θ b x) = _
  simp only [LieHom.map_lie, map_add, map_sub, lie_add, add_lie, hcomm]
  rw [show ⁅ρ x, D (θ b)⁆ = -ρ (θ b x) by
    rw [← lie_skew, hcomm]]
  abel

/-- Coordinates of an abelian algebra act by diagonal matrices. -/
def diagonalRepresentation {k Z : Type*} [Field k] [LieRing Z] [LieAlgebra k Z]
    [IsLieAbelian Z] {m : ℕ} (b : Module.Basis (Fin m) k Z) :
    Z →ₗ⁅k⁆ Module.End k (Fin m → k) where
  toLinearMap :=
    { toFun := fun z =>
        { toFun := fun f i => b.repr z i * f i
          map_add' := by intro f g; ext i; exact mul_add _ _ _
          map_smul' := by intro r f; ext i; simp [mul_left_comm] }
      map_add' := by intro x y; ext f i; simp [add_mul]
      map_smul' := by intro r x; ext f i; simp [mul_assoc] }
  map_lie' := by
    intro x y
    apply LinearMap.ext
    intro f
    funext i
    change b.repr ⁅x, y⁆ i * f i =
      b.repr x i * (b.repr y i * f i) - b.repr y i * (b.repr x i * f i)
    simp [trivial_lie_zero, mul_left_comm]

theorem diagonalRepresentation_injective {k Z : Type*} [Field k]
    [LieRing Z] [LieAlgebra k Z] [IsLieAbelian Z] {m : ℕ}
    (b : Module.Basis (Fin m) k Z) : Function.Injective (diagonalRepresentation b) := by
  intro x y h
  apply b.repr.injective
  ext i
  have hi := congrArg (fun f : Module.End k (Fin m → k) => f (fun _ => 1) i) h
  change b.repr x i * 1 = b.repr y i * 1 at hi
  simpa only [mul_one] using hi

/-- The adjoint action and diagonal center characters detect complementary
parts of a reductive algebra. -/
theorem reductiveFaithful :
    Specs.LieAlgebrasAndRepresentations.SemidirectFaithfulModule.reductiveFaithfulExpected.{u,v} := by
  intro k _ _ K _ _ _ hred
  obtain ⟨S, _, hc⟩ := (ReductiveDecomposition.reductive_iff k K).mp hred
  obtain ⟨e, he⟩ := ReductiveDecomposition.center_direct_sum k K S hc
  let Z := LieAlgebra.center k K
  let b := Module.finBasis k Z
  let p : K →ₗ⁅k⁆ Z := (LieHom.snd k S Z).comp e.symm.toLieHom
  let τ := productRepresentation (LieAlgebra.ad k K) ((diagonalRepresentation b).comp p)
  refine ⟨K × (Fin (Module.finrank k Z) → k), inferInstance, inferInstance,
    inferInstance, τ, ?_⟩
  apply (LieHom.ker_eq_bot τ).mp
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  have had : LieAlgebra.ad k K x = 0 := by
    apply LinearMap.ext
    intro y
    have h := congrArg (fun f : Module.End k (K × (Fin (Module.finrank k Z) → k)) =>
      (f (y, 0)).1) hx
    exact h
  have hz : x ∈ LieAlgebra.center k K := by
    rw [← LieAlgebra.self_module_ker_eq_center, ← LieAlgebra.ad_ker_eq_self_module_ker]
    exact had
  have hp : p x = 0 := by
    apply diagonalRepresentation_injective b
    rw [map_zero]
    apply LinearMap.ext
    intro y
    have h := congrArg (fun f : Module.End k (K × (Fin (Module.finrank k Z) → k)) =>
      (f (0, y)).2) hx
    exact h
  have hsecond : (e.symm x).2 = 0 := hp
  have hsum := he (e.symm x).1 (e.symm x).2
  rw [e.apply_symm_apply, hsecond] at hsum
  simp only [ZeroMemClass.coe_zero, add_zero] at hsum
  have hs : x ∈ S := hsum ▸ (e.symm x).1.property
  exact (show x ∈ (⊥ : Submodule k K) from
    (hc.disjoint.eq_bot ▸ (show x ∈ S.toSubmodule ⊓ Z.toSubmodule from ⟨hs, hz⟩)))

/-- Add an inflated faithful reductive module to the PBW quotient action. -/
theorem faithful :
    Specs.LieAlgebrasAndRepresentations.SemidirectFaithfulModule.faithfulExpected.{u,v,w} := by
  intro k _ _ K _ _ _ N _ _ _ _ hred θ
  obtain ⟨d, b, wt, n, hn, hb, hfin, ρ, D, hinj, hnil, hρ, h1, hcomm⟩ :=
    NilpotentTruncation.faithful_spec k N
  letI := hfin
  obtain ⟨W, hWadd, hWmod, hWfin, τ, hτ⟩ := reductiveFaithful k K hred
  letI := hWadd
  letI := hWmod
  letI := hWfin
  letI := Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect.semidirect_lie_ring_value θ
  letI := Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect.semidirect_lie_algebra_value θ
  obtain ⟨σ, hσ⟩ := semidirectAction k K N _ θ ρ D hcomm
  let p : (K × N) →ₗ⁅k⁆ K :=
    { LinearMap.fst k K N with map_lie' := fun {_ _} => rfl }
  let f := productRepresentation σ (τ.comp p)
  refine ⟨NilpotentTruncation.QuotientSpace b wt n × W,
    inferInstance, inferInstance, inferInstance, f, ?_⟩
  apply (LieHom.ker_eq_bot f).mp
  apply eq_bot_iff.mpr
  rintro ⟨a, x⟩ hx
  change (a, x) = 0
  have ha : a = 0 := by
    apply hτ
    rw [map_zero]
    apply LinearMap.ext
    intro z
    exact congrArg (fun F : Module.End k (NilpotentTruncation.QuotientSpace b wt n × W) =>
      (F (0, z)).2) hx
  have hleft : σ (a, x) = 0 := by
    apply LinearMap.ext
    intro z
    exact congrArg (fun F : Module.End k (NilpotentTruncation.QuotientSpace b wt n × W) =>
      (F (z, 0)).1) hx
  have hx0 : x = 0 := by
    apply hinj
    rw [map_zero]
    simpa only [hσ, ha, map_zero, zero_add] using hleft
  simp [ha, hx0]

end LieAlgebrasAndRepresentations.SemidirectFaithfulModule
