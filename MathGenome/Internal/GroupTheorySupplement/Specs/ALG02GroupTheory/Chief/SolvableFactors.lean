import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.Series
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.Solvable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The structure and ambient action of chief factors of finite solvable groups
(paper.tex, Corollary 1.4). -/

namespace Specs.ALG02GroupTheory.Chief.SolvableFactors

open Specs.ALG02GroupTheory.Chief.Series

universe u

/-- Every chief factor is nontrivial and has no proper nontrivial subgroup
stable under the ambient conjugation action. -/
def ChiefFactorMinimalInvariant : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (s : Chain G) (i : Fin s.length),
    Nontrivial (chiefFactorValue s i) ∧
      ∀ H : Subgroup (chiefFactorValue s i),
        gInvariantValue (G := G) H → H = ⊥ ∨ H = ⊤

/-- Every chief factor of a finite solvable group is abelian of prime exponent. -/
def SolvableChiefFactorElementaryAbelian : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] [Group.IsSolvable G] (s : Chain G) (i : Fin s.length),
    ∃ p : ℕ, p.Prime ∧ IsMulCommutative (chiefFactorValue s i) ∧
      Monoid.exponent (chiefFactorValue s i) = p

/-- On the additive form of the actual quotient group, the scalar action is
multiplication by a residue representative via repeated addition. Each ambient
conjugation automorphism is a linear equivalence for this module. -/
def SolvableChiefFactorVectorSpace : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] [Group.IsSolvable G] (s : Chain G) (i : Fin s.length),
    ∃ (p : ℕ) (hp : p.Prime) (hc : IsMulCommutative (chiefFactorValue s i)),
      Monoid.exponent (chiefFactorValue s i) = p ∧
        (let D := chiefFactorValue s i
         letI : Fact p.Prime := ⟨hp⟩
         letI : CommGroup D :=
           { chiefFactorGroup s i with mul_comm := fun a b => hc.is_comm.comm a b }
         ∃ m : Module (ZMod p) (Additive D),
           letI := m
           Nontrivial (Additive D) ∧ FiniteDimensional (ZMod p) (Additive D) ∧
             (∀ (a : ZMod p) (x : Additive D), a • x = a.val • x) ∧
             ∀ g : G, ∃ e : Additive D ≃ₗ[ZMod p] Additive D,
               ∀ x, e x = Additive.ofMul (g • x.toMul))

end Specs.ALG02GroupTheory.Chief.SolvableFactors
