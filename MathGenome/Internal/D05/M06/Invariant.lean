import MathGenome.Internal.D05.M03.LinearMap
import MathGenome.Internal.D05.M06.QuotientLift
import MathGenome.Internal.Specs.D05.M06.Invariant

/-! K05.06.invariant: restriction and quotient descent for invariant subspaces. -/

namespace D05.M06.Invariant

/-- A subspace is invariant when each of its vectors is sent back into it. -/
abbrev invariant (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) : Prop :=
  ∀ x ∈ U, T x ∈ U

/-- The same operator formula with domain and codomain restricted to `U`. -/
abbrev restriction (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant K V U T) : U →ₗ[K] U :=
  T.restrict h

/-- The operator on cosets, with codomain the algebraic quotient. -/
abbrev inducedMap (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (T : V →ₗ[K] V) (h : invariant K V U T) :
    (V ⧸ U) →ₗ[K] (V ⧸ U) :=
  U.mapQ U T h

theorem invariant_iff_image_subset : Specs.D05.M06.Invariant.invariant_iff_image_subset := by
  intro K V _ _ _ U T
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact h x hx
  · intro h x hx
    exact h ⟨x, hx, rfl⟩

theorem invariant_iff_map_le : Specs.D05.M06.Invariant.invariant_iff_map_le := by
  intro K V _ _ _ U T
  exact (Submodule.map_le_iff_le_comap).symm

theorem restriction_apply : Specs.D05.M06.Invariant.restriction_apply := by
  intro K V _ _ _ U T h x
  rfl

theorem restriction_operations : Specs.D05.M06.Invariant.restriction_operations := by
  intro K V _ _ _ U T h
  exact ⟨(restriction K V U T h).map_add, (restriction K V U T h).map_smul⟩

theorem restriction_commutes : Specs.D05.M06.Invariant.restriction_commutes := by
  intro K V _ _ _ U T h
  rfl

theorem restriction_unique : Specs.D05.M06.Invariant.restriction_unique := by
  intro K V _ _ _ U T h R hR
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun f : U →ₗ[K] V => f x) hR

theorem representative_independence :
    Specs.D05.M06.Invariant.representative_independence := by
  intro K V _ _ _ U T h x y hxy
  simpa only [map_sub] using h (x - y) hxy

theorem inducedMap_apply : Specs.D05.M06.Invariant.inducedMap_apply := by
  intro K V _ _ _ U T h x
  rfl

theorem inducedMap_operations : Specs.D05.M06.Invariant.inducedMap_operations := by
  intro K V _ _ _ U T h
  exact ⟨(inducedMap K V U T h).map_add, (inducedMap K V U T h).map_smul⟩

theorem inducedMap_commutes : Specs.D05.M06.Invariant.inducedMap_commutes := by
  intro K V _ _ _ U T h
  exact U.mapQ_mkQ U T

theorem inducedMap_unique : Specs.D05.M06.Invariant.inducedMap_unique := by
  intro K V _ _ _ U T h S hS
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := D05.M06.QuotientMap.surjective U x
  exact congrArg (fun f : V →ₗ[K] (V ⧸ U) => f v) hS

end D05.M06.Invariant
