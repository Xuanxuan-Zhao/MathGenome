import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.FreeWordPermutations
import Mathlib.Logic.Equiv.Fintype

namespace ALG02GroupTheory.Profinite.FreeWordPermutations

variable {α : Type*}

private theorem adjacent_sign_eq {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    {i j : Fin w.length} (hij : j.val = i.val + 1)
    (hs : (stepLetter w i).1 = (stepLetter w j).1) :
    (stepLetter w i).2 = (stepLetter w j).2 := by
  have hrev : j.rev.val + 1 = i.rev.val := by
    simp only [Fin.val_rev]
    omega
  have hlt : j.rev.val + 1 < w.length := hrev ▸ i.rev.isLt
  have heq : (⟨j.rev.val + 1, hlt⟩ : Fin w.length) = i.rev := Fin.ext hrev
  have hchain := List.isChain_iff_getElem.mp hw j.rev.val hlt
  change (w.get j.rev).1 = (w.get ⟨j.rev.val + 1, hlt⟩).1 →
    (w.get j.rev).2 = (w.get ⟨j.rev.val + 1, hlt⟩).2 at hchain
  rw [heq] at hchain
  exact (hchain hs.symm).symm

/-- Reducedness prevents any repetition among the domains or among the ranges
of the prescriptions for one generator. -/
theorem prescriptionsInjective (w : List (α × Bool)) (hw : FreeGroup.IsReduced w) (s : α)
    (leftSign : Bool) :
    Function.Injective (fun i : {i : Fin w.length // (stepLetter w i).1 = s} =>
      stepEndpoint w leftSign i.val) := by
  intro i j h
  apply Subtype.ext
  apply Fin.ext
  have hs : (stepLetter w i.val).1 = (stepLetter w j.val).1 := i.property.trans j.property.symm
  have hv := congrArg Fin.val h
  by_cases hi : (stepLetter w i.val).2 = leftSign <;>
    by_cases hj : (stepLetter w j.val).2 = leftSign <;>
    simp only [stepEndpoint, hi, hj, ite_true, ite_false, Fin.val_castSucc, Fin.val_succ] at hv
  · exact hv
  · exact (hj ((adjacent_sign_eq hw hv hs.symm).trans hi)).elim
  · exact (hi ((adjacent_sign_eq hw hv.symm hs).trans hj)).elim
  · exact Nat.succ.inj hv

/-- Simultaneously extend the prescriptions to permutations of the path vertices. -/
theorem existsPathPermutations (w : List (α × Bool)) (_hne : w ≠ [])
    (hw : FreeGroup.IsReduced w) :
    ∃ σ : α → Equiv.Perm (Fin (w.length + 1)),
      (∀ i : Fin w.length,
        (if (stepLetter w i).2 then σ (stepLetter w i).1 else (σ (stepLetter w i).1)⁻¹)
          i.castSucc = i.succ) ∧
      (∀ s : α, (∀ b : Bool, (s, b) ∉ w) → σ s = 1) := by
  classical
  have extend (s : α) : ∃ p : Equiv.Perm (Fin (w.length + 1)),
      (∀ i : {i : Fin w.length // (stepLetter w i).1 = s},
        p (stepEndpoint w true i.val) = stepEndpoint w false i.val) ∧
      ((∀ b : Bool, (s, b) ∉ w) → p = 1) := by
    by_cases hs : ∀ b : Bool, (s, b) ∉ w
    · refine ⟨1, ?_, fun _ => rfl⟩
      intro i
      have hm : stepLetter w i.val ∈ w := List.get_mem w i.val.rev
      have heq : stepLetter w i.val = (s, (stepLetter w i.val).2) := Prod.ext i.property rfl
      exact (hs _ (heq ▸ hm)).elim
    · obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair _ _
        (prescriptionsInjective w hw s true) (prescriptionsInjective w hw s false)
      exact ⟨p, hp, fun h => (hs h).elim⟩
  let σ (s : α) := Classical.choose (extend s)
  have hσ (s : α) := Classical.choose_spec (extend s)
  refine ⟨σ, ?_, fun s => (hσ s).2⟩
  intro i
  have hstep := (hσ (stepLetter w i).1).1 ⟨i, rfl⟩
  change σ (stepLetter w i).1 (stepEndpoint w true i) = stepEndpoint w false i at hstep
  cases hsign : (stepLetter w i).2 with
  | false =>
    simp [stepEndpoint, hsign] at hstep
    simp only [Bool.false_eq_true, ite_false, Equiv.Perm.inv_def]
    rw [← hstep, Equiv.symm_apply_apply]
  | true =>
    simpa [stepEndpoint, hsign] using hstep

end ALG02GroupTheory.Profinite.FreeWordPermutations
