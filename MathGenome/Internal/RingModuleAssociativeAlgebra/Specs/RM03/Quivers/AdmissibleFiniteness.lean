import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.Relations
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The vector-space conclusions for quotients of a path algebra. -/

universe u v w

namespace RM03.AdmissibleFinitenessSpec

open PathAlgebraSpec
attribute [local instance] QuiverRelationSpec.nonUnitalNonAssocRing

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]

private theorem mul_unit_apply (x : Carrier k Q) : mul k Q (one k Q) x = x := by
  classical
  have h : mul k Q (one k Q) = LinearMap.id := (basis k Q).ext fun p => by
    change ((mul k Q).flip (basis k Q p)) (∑ i : Q, vertex k Q i) = basis k Q p
    rw [map_sum]
    calc
      _ = ∑ i : Q, if i = p.target then basis k Q p else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        change mul k Q (basis k Q (Path.vertex i)) (basis k Q p) = _
        unfold mul
        rw [Module.Basis.constr_basis, Module.Basis.constr_basis]
        rcases p with ⟨s, t, p⟩
        change (if h : i = t then ofPath k Q ((Path.vertex i).concat ⟨s, t, p⟩ h)
          else 0) = if i = t then basis k Q ⟨s, t, p⟩ else 0
        by_cases hit : i = t
        · subst i
          rw [dite_eq_left rfl, ite_eq_left rfl]
          rfl
        · rw [dite_eq_right hit, ite_eq_right hit]
      _ = _ := by simp
  exact LinearMap.congr_fun h x

/-- The ideal as a submodule over the coefficient field. Its quotient uses
the same cosets and scalar multiplication as the algebra quotient. -/
noncomputable def idealSubmodule (I : TwoSidedIdeal (Carrier k Q)) : Submodule k (Carrier k Q) where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' c x hx := by
    change c • x ∈ I
    have h : (c • one k Q) * x = c • x := by
      change ((mul k Q).flip x) (c • one k Q) = c • x
      rw [map_smul]
      exact congrArg (c • ·) (mul_unit_apply x)
    rw [← h]
    exact I.mul_mem_left _ _ hx

def QuotientFiniteAndSpanned : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q] [Nonempty Q]
    [Finite (Arrow Q)] (I : TwoSidedIdeal (Carrier k Q)) (m : ℕ),
    1 ≤ m → QuiverRelationSpec.idealPower (QuiverRelationSpec.arrowIdeal k Q) m ≤ I →
    FiniteDimensional k (Carrier k Q ⧸ idealSubmodule I) ∧
      Submodule.span k (Set.range fun p : {p : Path Q // p.length < m} =>
        (idealSubmodule I).mkQ (ofPath k Q p.val)) = ⊤

def QuotientShortPathsIndependent : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q] [Nonempty Q]
    [Finite (Arrow Q)] (I : TwoSidedIdeal (Carrier k Q)),
    I ≤ QuiverRelationSpec.idealPower (QuiverRelationSpec.arrowIdeal k Q) 2 →
    LinearIndependent k (fun p : {p : Path Q // p.length < 2} =>
      (idealSubmodule I).mkQ (ofPath k Q p.val))

end RM03.AdmissibleFinitenessSpec
