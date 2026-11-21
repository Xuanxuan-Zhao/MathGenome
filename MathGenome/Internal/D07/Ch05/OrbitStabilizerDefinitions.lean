import MathGenome.Internal.D07.Ch01.SubgroupDefinitionTest
import MathGenome.Internal.D07.Ch05.ActionDefinition
import MathGenome.Internal.Specs.D07.Ch05.OrbitStabilizerDefinitions

/-!
# Orbits, stabilizers, and the orbit partition

`K07.05.orbit_stabilizer_definitions` (paper.tex:830–840), for an
arbitrary left group action, including actions on the empty type.
-/

namespace D07.Ch05.OrbitStabilizerDefinitions

universe u v

/-- The orbit consists of all action values at x. -/
abbrev orbit (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X) : Set X :=
  MulAction.orbit G x

/-- The stabilizer uses the inherited group operations. -/
abbrev stabilizer (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X) :
    Subgroup G :=
  MulAction.stabilizer G x

theorem orbit_description (G : Type u) (X : Type v) [Group G] [MulAction G X]
    (x : X) : orbit G X x = {y : X | ∃ g : G, g • x = y} := rfl

theorem stabilizer_description (G : Type u) (X : Type v) [Group G] [MulAction G X]
    (x : X) : (stabilizer G X x : Set G) = {g : G | g • x = x} := rfl

theorem stabilizer_is_subgroup (G : Type u) (X : Type v) [Group G] [MulAction G X]
    (x : X) : ∃ H : Subgroup G, (H : Set G) = {g : G | g • x = x} :=
  ⟨stabilizer G X x, stabilizer_description G X x⟩

theorem orbit_relation_equivalence (G : Type u) (X : Type v)
    [Group G] [MulAction G X] :
    Equivalence (fun x y : X => y ∈ orbit G X x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact MulAction.mem_orbit_self x
  · intro x y h
    exact MulAction.mem_orbit_symm.mp h
  · intro x y z hxy hyz
    exact MulAction.mem_orbit_trans hyz hxy

theorem orbit_classes (G : Type u) (X : Type v) [Group G] [MulAction G X]
    (x : X) : {y : X | MulAction.orbitRel G X x y} = orbit G X x := by
  apply Set.ext
  intro y
  exact MulAction.mem_orbit_symm

theorem orbits_partition (G : Type u) (X : Type v) [Group G] [MulAction G X] :
    (∀ x : X, (orbit G X x).Nonempty) ∧
    (⋃ x : X, orbit G X x) = Set.univ ∧
    (∀ x y : X, orbit G X x = orbit G X y ∨
      Disjoint (orbit G X x) (orbit G X y)) := by
  classical
  refine ⟨fun x => ⟨x, MulAction.mem_orbit_self x⟩, ?_, ?_⟩
  · apply Set.ext
    intro x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨x, MulAction.mem_orbit_self x⟩
  · intro x y
    by_cases h : orbit G X x = orbit G X y
    · exact Or.inl h
    · right
      apply Set.disjoint_left.mpr
      intro z hzx hzy
      apply h
      exact (MulAction.orbit_eq_iff.mpr hzx).symm.trans
        (MulAction.orbit_eq_iff.mpr hzy)

/-- Conjugation transports stabilizers, stated as an equality of carriers. -/
theorem stabilizer_conjugation (G : Type u) (X : Type v)
    [Group G] [MulAction G X] (g : G) (x : X) :
    (stabilizer G X (g • x) : Set G) =
      (fun h : G => g * h * g⁻¹) '' (stabilizer G X x : Set G) := by
  apply Set.ext
  intro h
  constructor
  · intro hh
    change h • (g • x) = g • x at hh
    refine ⟨g⁻¹ * h * g, ?_, ?_⟩
    · change (g⁻¹ * h * g) • x = x
      calc
        (g⁻¹ * h * g) • x = g⁻¹ • (h • (g • x)) := by
          rw [mul_smul, mul_smul]
        _ = g⁻¹ • (g • x) := congrArg (fun y : X => g⁻¹ • y) hh
        _ = x := inv_smul_smul g x
    · simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  · rintro ⟨k, hk, rfl⟩
    change k • x = x at hk
    change (g * k * g⁻¹) • (g • x) = g • x
    calc
      (g * k * g⁻¹) • (g • x) = g • (k • x) := by
        rw [mul_smul, mul_smul, inv_smul_smul]
      _ = g • x := congrArg (fun y : X => g • y) hk

end D07.Ch05.OrbitStabilizerDefinitions
