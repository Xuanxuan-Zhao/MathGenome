import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ReductiveDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.LeviDecomposition
import Mathlib.LinearAlgebra.Projection

noncomputable section
universe u v
namespace LieAlgebrasAndRepresentations.ReductiveDecomposition

/-- The source notion of reductivity, without any representation hypothesis. -/
def IsReductive (k : Type u) (L : Type v) [Field k] [LieRing L]
    [LieAlgebra k L] : Prop := radical k L = LieAlgebra.center k L

variable (k : Type u) (L : Type v) [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

/-- The canonical sum map realizes an ideal complement to the center as a
direct product of Lie algebras. -/
theorem center_direct_sum (S : LieIdeal k L)
    (hc : IsCompl S.toSubmodule (LieAlgebra.center k L).toSubmodule) :
    ∃ e : (S × LieAlgebra.center k L) ≃ₗ⁅k⁆ L,
      ∀ (x : S) (z : LieAlgebra.center k L), e (x, z) = (x : L) + (z : L) := by
  let e := Submodule.prodEquivOfIsCompl S.toSubmodule
    (LieAlgebra.center k L).toSubmodule hc
  let f : (S × LieAlgebra.center k L) ≃ₗ⁅k⁆ L :=
    { e with
      map_lie' := by
        intro x y
        change (⁅x.1, y.1⁆ : S).val + (⁅x.2, y.2⁆ : LieAlgebra.center k L).val =
          ⁅(x.1 : L) + (x.2 : L), (y.1 : L) + (y.2 : L)⁆
        change ⁅(x.1 : L), (y.1 : L)⁆ + ⁅(x.2 : L), (y.2 : L)⁆ = _
        have hxy := y.2.property (x.1 : L)
        have hyx : ⁅(x.2 : L), (y.1 : L)⁆ = 0 := by
          rw [← lie_skew, x.2.property, neg_zero]
        simp only [lie_add, add_lie, hxy, hyx, add_zero, zero_add] }
  exact ⟨f, fun _ _ => rfl⟩

/-- A central radical makes a Levi subalgebra into an ideal; conversely the
radical has zero image in a semisimple direct summand. -/
theorem reductive_iff :
    IsReductive k L ↔
      ∃ S : LieIdeal k L, IsSemisimple k S ∧
        IsCompl S.toSubmodule (LieAlgebra.center k L).toSubmodule := by
  constructor
  · intro h
    change radical k L = LieAlgebra.center k L at h
    obtain ⟨S, hs, hc, _⟩ := LeviDecomposition.leviDecomposition k L
    have hc' : IsCompl S.toSubmodule (LieAlgebra.center k L).toSubmodule := by
      change IsCompl S.toSubmodule (radical k L).toSubmodule at hc
      rwa [h] at hc
    let I : LieIdeal k L :=
      { S.toSubmodule with
        lie_mem := by
          intro x y hy
          obtain ⟨⟨s, z⟩, hx⟩ :=
            (Submodule.prodEquivOfIsCompl S.toSubmodule
              (LieAlgebra.center k L).toSubmodule hc').surjective x
          change (s : L) + (z : L) = x at hx
          rw [← hx, add_lie]
          have hz : ⁅(z : L), y⁆ = 0 := by
            rw [← lie_skew, z.property, neg_zero]
          rw [hz, add_zero]
          exact S.lie_mem s.property hy }
    exact ⟨I, hs, hc'⟩
  · rintro ⟨S, hs, hc⟩
    obtain ⟨e, he⟩ := center_direct_sum k L S hc
    let p : L →ₗ⁅k⁆ S :=
      (LieHom.fst k S (LieAlgebra.center k L)).comp e.symm.toLieHom
    let J := (radical k L).map p
    let t : radical k L →ₗ⁅k⁆ J :=
      { (p.toLinearMap.comp (radical k L).incl.toLinearMap).codRestrict
          J.toSubmodule (fun x => LieIdeal.mem_map x.property) with
        map_lie' := by intro x y; apply Subtype.ext; exact p.map_lie x y }
    have hp : Function.Surjective p := by
      intro x
      refine ⟨e (x, 0), ?_⟩
      change (e.symm (e (x, 0))).1 = x
      rw [e.symm_apply_apply]
    have ht : Function.Surjective t := by
      intro y
      obtain ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective hp y.property
      exact ⟨x, Subtype.ext hx⟩
    have := radical_solvable k L
    have hJ : LieAlgebra.IsSolvable J := ht.lieAlgebra_isSolvable
    have hJ0 : J = ⊥ := (semisimple_iff_no_solvable_ideals k S).mp hs J hJ
    apply le_antisymm
    · intro x hx
      have hpx : p x = 0 := by
        have hm : p x ∈ J := LieIdeal.mem_map hx
        rw [hJ0] at hm
        exact hm
      have hfst : (e.symm x).1 = 0 := hpx
      have hsum := he (e.symm x).1 (e.symm x).2
      rw [e.apply_symm_apply, hfst] at hsum
      simp only [ZeroMemClass.coe_zero, zero_add] at hsum
      rw [hsum]
      exact (e.symm x).2.property
    · exact LieAlgebra.center_le_radical k L

end LieAlgebrasAndRepresentations.ReductiveDecomposition
