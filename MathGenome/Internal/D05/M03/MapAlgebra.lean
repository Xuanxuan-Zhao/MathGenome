import MathGenome.Internal.D05.M03.LinearMap
import MathGenome.Internal.Specs.D05.M03.MapAlgebra

/-! K05.03.map_algebra: pointwise vector-space operations, composition, and End. -/

namespace D05.M03.MapAlgebra

/-- Use the canonical module structure on the already defined linear maps. -/
abbrev homModule (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] : Module K (V →ₗ[K] W) := inferInstance

/-- Endomorphisms form a ring under pointwise addition and composition. -/
abbrev endomorphismRing (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    Ring (Module.End K V) := inferInstance

/-- Scalars act pointwise in the canonical unital endomorphism algebra. -/
abbrev endomorphismAlgebra (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    Algebra K (Module.End K V) := inferInstance

theorem add_apply : Specs.D05.M03.MapAlgebra.add_apply := by
  intro K V W _ _ _ _ _ S T v
  rfl

theorem smul_apply : Specs.D05.M03.MapAlgebra.smul_apply := by
  intro K V W _ _ _ _ _ a T v
  rfl

theorem zero_apply : Specs.D05.M03.MapAlgebra.zero_apply := by
  intro K V W _ _ _ _ _ v
  rfl

theorem neg_apply : Specs.D05.M03.MapAlgebra.neg_apply := by
  intro K V W _ _ _ _ _ T v
  rfl

theorem comp_apply : Specs.D05.M03.MapAlgebra.comp_apply := by
  intro K U V W _ _ _ _ _ _ _ S T u
  rfl

theorem comp_assoc : Specs.D05.M03.MapAlgebra.comp_assoc := by
  intro K U V W X _ _ _ _ _ _ _ _ _ R S T
  rfl

theorem comp_add : Specs.D05.M03.MapAlgebra.comp_add := by
  intro K U V W _ _ _ _ _ _ _ R S T
  exact LinearMap.comp_add S T R

theorem add_comp : Specs.D05.M03.MapAlgebra.add_comp := by
  intro K U V W _ _ _ _ _ _ _ R S T
  exact LinearMap.add_comp T S R

theorem comp_smul : Specs.D05.M03.MapAlgebra.comp_smul := by
  intro K U V W _ _ _ _ _ _ _ R a T
  ext u
  exact R.map_smul a (T u)

theorem smul_comp : Specs.D05.M03.MapAlgebra.smul_comp := by
  intro K U V W _ _ _ _ _ _ _ a R T
  rfl

theorem comp_id : Specs.D05.M03.MapAlgebra.comp_id := by
  intro K V W _ _ _ _ _ T
  rfl

theorem id_comp : Specs.D05.M03.MapAlgebra.id_comp := by
  intro K V W _ _ _ _ _ T
  rfl

theorem end_mul_eq_comp : Specs.D05.M03.MapAlgebra.end_mul_eq_comp := by
  intro K V _ _ _ S T
  rfl

theorem end_one_eq_id : Specs.D05.M03.MapAlgebra.end_one_eq_id := by
  intro K V _ _ _
  rfl

theorem end_algebraMap_apply : Specs.D05.M03.MapAlgebra.end_algebraMap_apply := by
  intro K V _ _ _ a v
  rfl

theorem noncommuting_example : Specs.D05.M03.MapAlgebra.noncommuting_example := by
  intro K _
  let S : Module.End K (K × K) :=
    { toFun := fun v => (0, v.1)
      map_add' := by intro x y; ext <;> simp
      map_smul' := by intro a x; ext <;> simp }
  let T : Module.End K (K × K) :=
    { toFun := fun v => (v.1, 0)
      map_add' := by intro x y; ext <;> simp
      map_smul' := by intro a x; ext <;> simp }
  refine ⟨S, T, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  have heval := congrArg (fun F : Module.End K (K × K) => (F (1, 0)).2) h
  exact one_ne_zero (show (1 : K) = 0 from heval)

end D05.M03.MapAlgebra
