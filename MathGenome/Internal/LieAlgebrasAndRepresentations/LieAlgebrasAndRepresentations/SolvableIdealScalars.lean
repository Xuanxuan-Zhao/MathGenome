import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableIdealScalars
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.LieTheorem
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CyclicWeight

universe u v w

namespace LieAlgebrasAndRepresentations

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {G : Type v} [LieRing G] [LieAlgebra k G] [Module.Finite k G]
variable {V : Type w} [AddCommGroup V] [Module k V]
  [LieRingModule G V] [LieModule k G V] [Module.Finite k V]
  [Nontrivial V] [LieModule.IsIrreducible k G V]

/-- A solvable ideal acts by a single linear character on an irreducible
module, and the entire commutator ideal with the ambient algebra acts by zero. -/
theorem solvable_ideal_scalars (r : LieIdeal k G) [LieAlgebra.IsSolvable r] :
    ∃ χ : Module.Dual k r,
      (∀ a b : r, χ ⁅a, b⁆ = 0) ∧
      (∀ (a : r) (v : V), ⁅a, v⁆ = χ a • v) ∧
      (∀ z ∈ (⁅(⊤ : LieIdeal k G), r⁆ : LieIdeal k G),
        ∀ v : V, ⁅z, v⁆ = 0) := by
  obtain ⟨χ, v, hv, he⟩ := common_eigenvector (k := k) (G := r) (V := V)
  let E : LieSubmodule k G V :=
    { toSubmodule := (LieModule.weightSpace V χ).toSubmodule
      lie_mem := fun {x z} hz =>
        (LieModule.mem_weightSpace χ _).mpr
          (common_weight_stable r χ x z ((LieModule.mem_weightSpace χ z).mp hz)) }
  have hE : E ≠ ⊥ := by
    intro h
    have hm : v ∈ E := (LieModule.mem_weightSpace χ v).mpr he
    rw [h] at hm
    exact hv hm
  have htop : E = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top E).resolve_left hE
  have hscalar (a : r) (z : V) : ⁅a, z⁆ = χ a • z := by
    have hz : z ∈ E := by rw [htop]; exact LieSubmodule.mem_top z
    exact (LieModule.mem_weightSpace χ z).mp hz a
  have hcomm (x : G) (a : r) : χ ⁅x, a⁆ = 0 :=
    (cyclic_weight r x χ v hv he).2.2.2.1 a
  refine ⟨χ, fun a b => hcomm (a : G) b, hscalar, ?_⟩
  intro z hz w
  change z ∈ (⁅(⊤ : LieIdeal k G), r⁆ : LieIdeal k G).toSubmodule at hz
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, _, a, ha, rfl⟩ := hz
    change ⁅(⁅x, (⟨a, ha⟩ : r)⁆ : r), w⁆ = 0
    rw [hscalar, hcomm, zero_smul]
  | zero => exact zero_lie w
  | add x y _ _ hx hy => rw [add_lie, hx, hy, add_zero]
  | smul a z _ hz => rw [smul_lie, hz, smul_zero]

end LieAlgebrasAndRepresentations
