import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Profinite.FreeWordPermutations
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.ResiduallyFinite

namespace ALG02GroupTheory.Profinite.FreeGroup

open FreeWordPermutations

/-- The product of the signed permutations follows the path from the rightmost
letter to the leftmost. The vertices can lie in any permutation domain. -/
private theorem wordPerm_apply {α β : Type*} (p : (α × Bool) → Equiv.Perm β)
    (w : List (α × Bool)) (v : Fin (w.length + 1) → β)
    (hstep : ∀ i : Fin w.length, p (stepLetter w i) (v i.castSucc) = v i.succ) :
    (w.map p).prod (v 0) = v (Fin.last w.length) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have htail (i : Fin w.length) :
        p (stepLetter w i) (v i.castSucc.castSucc) = v i.succ.castSucc := by
      simpa only [stepLetter, Fin.rev_castSucc, List.get_cons_succ', Fin.succ_castSucc]
        using hstep i.castSucc
    have hrest := ih (fun j => v j.castSucc) htail
    have hlast : p a (v (Fin.last w.length).castSucc) = v (Fin.last (w.length + 1)) := by
      simpa only [stepLetter, Fin.rev_last, List.get_cons_zero, Fin.succ_last]
        using hstep (Fin.last w.length)
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    exact (congrArg (p a) hrest).trans hlast

/-- A nonidentity free-group element is detected by a surjection onto a finite group. -/
theorem existsFiniteQuotient {α : Type*} (g : _root_.FreeGroup α) (hg : g ≠ 1) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (f : _root_.FreeGroup α →* Q),
      Function.Surjective f ∧ f g ≠ 1 := by
  classical
  let w := g.toWord
  have hne : w ≠ [] := fun h => hg (FreeGroup.toWord_eq_nil_iff.mp h)
  have hw : _root_.FreeGroup.IsReduced w := FreeGroup.isReduced_toWord
  obtain ⟨σ, hstep, _⟩ := existsPathPermutations w hne hw
  let f := FreeGroup.lift σ
  have hmove : f g 0 = Fin.last w.length := by
    have hword : FreeGroup.mk w = g := FreeGroup.mk_toWord
    rw [← hword, FreeGroup.lift_mk]
    apply wordPerm_apply (fun x => cond x.2 (σ x.1) (σ x.1)⁻¹) w id
    simpa only [Bool.cond_eq_ite, id_eq] using hstep
  have hlast : Fin.last w.length ≠ 0 := by
    intro h
    apply hne
    exact List.length_eq_zero_iff.mp (congrArg Fin.val h)
  have hf : f g ≠ 1 := by
    intro h
    apply hlast
    simpa [h] using hmove.symm
  refine ⟨f.range, inferInstance, inferInstance, f.rangeRestrict, f.rangeRestrict_surjective, ?_⟩
  exact fun h => hf (congrArg Subtype.val h)

/-- GR02-C05.08. A free group of any rank is residually finite. -/
theorem residuallyFinite {G : Type*} [Group G] [IsFreeGroup G] : Group.ResiduallyFinite G := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  let e := IsFreeGroup.toFreeGroup G
  have hne : e g ≠ 1 := fun h => hg (e.injective (h.trans e.map_one.symm))
  obtain ⟨Q, _, _, f, _, hf⟩ := existsFiniteQuotient (e g) hne
  exact ⟨Q, inferInstance, inferInstance, f.comp e.toMonoidHom, hf⟩

end ALG02GroupTheory.Profinite.FreeGroup
