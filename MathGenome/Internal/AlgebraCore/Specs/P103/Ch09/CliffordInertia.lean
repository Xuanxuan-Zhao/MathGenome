import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.CliffordRestriction
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InductionModels

/-! Clifford's inertia theorem, paper.tex 2131–2139 and 2153–2163.
The subspace is the full intrinsic isotypic component, not a simple summand.
The finite-dimensionality of an irreducible representation is not an assumption.
-/
noncomputable section
universe u v
namespace P103.Ch09.CliffordInertiaSpecs
open P103.Ch08 CliffordRestrictionSpecs
open scoped MonoidAlgebra

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The stabilizer of a vector subspace under the given group action. -/
def inertia (ρ : Representation ℂ G V) (U : Submodule ℂ V) : Subgroup G where
  carrier := {g | U.map (ρ g) = U}
  one_mem' := by simp [Module.End.one_eq_id]
  mul_mem' := by
    intro g h hg hh
    change U.map (ρ (g * h)) = U
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp, hh, hg]
  inv_mem' := by
    intro g hg
    have he : (ρ g⁻¹).comp (ρ g) = LinearMap.id := by
      rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
      rfl
    have hm := congrArg (fun W : Submodule ℂ V => W.map (ρ g⁻¹)) hg
    rw [← Submodule.map_comp, he, Submodule.map_id] at hm
    exact hm.symm

/-- The inherited action on the stabilized subspace. -/
def inertiaSubrepresentation (ρ : Representation ℂ G V) (U : Submodule ℂ V) :
    Subrepresentation (ρ.comp (inertia ρ U).subtype) where
  toSubmodule := U
  apply_mem_toSubmodule g _ hv := by
    change ρ g.val _ ∈ U
    exact (show U.map (ρ g.val) = U from g.property).le ⟨_, hv, rfl⟩

def inertiaRepresentation (ρ : Representation ℂ G V) (U : Submodule ℂ V) :
    Representation ℂ (inertia ρ U) U :=
  (inertiaSubrepresentation ρ U).toRepresentation

def containsType : Prop :=
  ∀ {G : Type u} [Group G] (A : Subgroup G) [A.Normal]
    (C : RegularMultiplicitySpecs.Family A)
    {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (i : Fin C.n), A ≤ inertia ρ (component A C ρ i)

def irreducibleType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (C : RegularMultiplicitySpecs.Family A),
    RegularMultiplicitySpecs.Valid C → RegularMultiplicitySpecs.Exhaustive.{u,u} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      Irreducible ℂ G V ρ → ∀ i, component A C ρ i ≠ ⊥ →
      Irreducible ℂ (inertia ρ (component A C ρ i)) (component A C ρ i)
        (inertiaRepresentation ρ (component A C ρ i))

/-- The equivalence has exactly the source's map on every group-basis pure
 tensor, with the original shared balanced tensor and induced action. -/
def inductionType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (C : RegularMultiplicitySpecs.Family A),
    RegularMultiplicitySpecs.Valid C → RegularMultiplicitySpecs.Exhaustive.{u,u} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      Irreducible ℂ G V ρ → ∀ i, component A C ρ i ≠ ⊥ →
      let U := component A C ρ i
      let I := inertia ρ U
      let τ := inertiaRepresentation ρ U
      ∃ D : InductionData I τ,
        letI := D.module
        ∃ e : D.representation.Equiv ρ,
          ∀ (g : G) (z : U),
            e (tensor I τ (MonoidAlgebra.single g 1) z) = ρ g (z : V)

/-- If the inertia subgroup is the whole group, the chosen intrinsic
isotypic component is all of V. Thus restriction to A is isotypic. -/
def isotypicType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (C : RegularMultiplicitySpecs.Family A)
    {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      Irreducible ℂ G V ρ → ∀ i, component A C ρ i ≠ ⊥ →
        inertia ρ (component A C ρ i) = ⊤ → component A C ρ i = ⊤

/-- Full Clifford statement: the assumption-free complete restriction theorem
and the inertia conclusions for every occurring intrinsic component. -/
def cliffordInertiaType : Prop :=
  cliffordType.{u,v} ∧ containsType.{u,v} ∧ irreducibleType.{u,v} ∧
    inductionType.{u,v} ∧ isotypicType.{u,v}

end P103.Ch09.CliffordInertiaSpecs
