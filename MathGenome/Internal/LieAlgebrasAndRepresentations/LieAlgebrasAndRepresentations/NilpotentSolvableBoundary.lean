import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DerivedLowerSeries
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.NilpotentSolvableBoundary

/-! Nilpotence implies solvability, but is not closed under extensions.
Source: notes/005/lie-algebras-and-representations.tex, lines 254–257. -/

universe u v
open Module
namespace LieAlgebrasAndRepresentations

variable {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]

theorem derived_le_lower (r : ℕ) :
    derivedSeries k L r ≤ lowerCentralSeries k L (r + 1) := by
  simpa only [derivedSeries, lowerCentralSeries, Nat.add_sub_cancel] using
    LieModule.derivedSeries_le_lowerCentralSeries k L r

include k in
theorem nilpotent_implies_solvable (hL : LieRing.IsNilpotent L) :
    LieAlgebra.IsSolvable L := by
  obtain ⟨n, hn, hzero⟩ := (nilpotent_iff (k := k)).mp hL
  apply (solvable_iff (k := k)).mpr
  refine ⟨n - 1, le_bot_iff.mp ?_⟩
  simpa only [Nat.sub_add_cancel hn, hzero] using
    derived_le_lower (k := k) (L := L) (n - 1)

namespace Boundary
variable (k : Type u) [Field k]

theorem bracket_h_e : ⁅h k, e k⁆ = e k := by
  apply Prod.ext
  · rfl
  · change (1 : k) * 1 - 0 * 0 = 1
    simp

theorem basis_h_e :
    ∃ b : Basis (Fin 2) k (AffineLie k), b 0 = h k ∧ b 1 = e k := by
  exact ⟨Basis.finTwoProd k, Basis.finTwoProd_zero k, Basis.finTwoProd_one k⟩

theorem lineIdeal_eq_span :
    (lineIdeal k).toSubmodule = Submodule.span k {e k} := by
  apply le_antisymm
  · intro x hx
    have hx : x.1 = 0 := hx
    have he : e k ∈ Submodule.span k {e k} := Submodule.subset_span (by simp)
    have hx' : x = x.2 • e k := by
      apply Prod.ext
      · change x.1 = x.2 * 0
        simp [hx]
      · change x.2 = x.2 * 1
        simp
    rw [hx']
    exact Submodule.smul_mem _ x.2 he
  · apply Submodule.span_le.mpr
    intro x hx
    have hx : x = e k := Set.mem_singleton_iff.mp hx
    subst x
    rfl

theorem lineIdeal_abelian : IsLieAbelian (lineIdeal k) := by
  constructor
  intro x y
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change x.val.1 * y.val.2 - y.val.1 * x.val.2 = 0
    have hx : x.val.1 = 0 := x.property
    have hy : y.val.1 = 0 := y.property
    rw [hx, hy]
    simp

theorem quotient_abelian : IsLieAbelian (AffineLie k ⧸ lineIdeal k) := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change (LieSubmodule.Quotient.mk ⁅x, y⁆ : AffineLie k ⧸ lineIdeal k) = 0
      apply LieSubmodule.Quotient.mk_eq_zero'.mpr
      rfl

theorem e_mem_lower (n : ℕ) :
    e k ∈ LieModule.lowerCentralSeries k (AffineLie k) (AffineLie k) n := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [LieModule.lowerCentralSeries_succ, ← bracket_h_e k]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top (h k)) ih

theorem affine_not_nilpotent : ¬ LieRing.IsNilpotent (AffineLie k) := by
  intro hnil
  obtain ⟨n, _, hn⟩ := (nilpotent_iff (k := k)).mp hnil
  have he := e_mem_lower k (n - 1)
  change e k ∈ lowerCentralSeries k (AffineLie k) n at he
  rw [hn] at he
  have he : e k = 0 := he
  have : (1 : k) = 0 := congrArg Prod.snd he
  exact one_ne_zero this

end Boundary

open Boundary

theorem affine_counterexample (k : Type u) [Field k] :
    (∃ b : Basis (Fin 2) k (AffineLie k), b 0 = h k ∧ b 1 = e k) ∧
    ⁅h k, e k⁆ = e k ∧
    (lineIdeal k).toSubmodule = Submodule.span k {e k} ∧
    IsLieAbelian (lineIdeal k) ∧
    IsLieAbelian (AffineLie k ⧸ lineIdeal k) ∧
    LieRing.IsNilpotent (lineIdeal k) ∧
    LieRing.IsNilpotent (AffineLie k ⧸ lineIdeal k) ∧
    ¬ LieRing.IsNilpotent (AffineLie k) := by
  have := lineIdeal_abelian k
  have := quotient_abelian k
  exact ⟨basis_h_e k, bracket_h_e k, lineIdeal_eq_span k,
    inferInstance, inferInstance, inferInstance, inferInstance, affine_not_nilpotent k⟩

end LieAlgebrasAndRepresentations
