import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.ResiduallyFinite

namespace ALG02GroupTheory.Profinite

universe u

/-- Every finitely generated abelian group is residually finite. -/
theorem finitelyGeneratedAbelian_residuallyFinite
    (G : Type u) [CommGroup G] [Group.FG G] : Group.ResiduallyFinite G := by
  classical
  obtain ⟨ι, κ, _, _, p, hp, e, ⟨decompose⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod G
  let A := (i : ι) → Multiplicative (ZMod (p i ^ e i))
  have (i : ι) : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  let freeProjection := (MonoidHom.fst (κ → Multiplicative ℤ) A).comp decompose.toMonoidHom
  let finiteProjection := (MonoidHom.snd (κ → Multiplicative ℤ) A).comp decompose.toMonoidHom
  by_cases hFinite : finiteProjection g = 1
  · have hFree : freeProjection g ≠ 1 := by
      intro h
      apply hg
      apply decompose.injective
      rw [map_one]
      exact Prod.ext h hFinite
    have hex : ∃ i : κ, freeProjection g i ≠ 1 := by
      by_contra! h
      exact hFree (funext h)
    obtain ⟨i, hi⟩ := hex
    let a := (freeProjection g i).toAdd
    let n := a.natAbs + 1
    have : NeZero n := ⟨Nat.succ_ne_zero _⟩
    let reduce : Multiplicative ℤ →* Multiplicative (ZMod n) :=
      (Int.castRingHom (ZMod n)).toAddMonoidHom.toMultiplicative
    let coordinate := (Pi.evalMonoidHom (fun _ : κ => Multiplicative ℤ) i).comp freeProjection
    refine ⟨Multiplicative (ZMod n), inferInstance, inferInstance, reduce.comp coordinate, ?_⟩
    intro h
    change (a : ZMod n) = 0 at h
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd a n).mp h
    have ha := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by
      rw [Int.natAbs_natCast]
      exact Nat.lt_succ_self a.natAbs)
    exact hi ha
  · exact ⟨A, inferInstance, inferInstance, finiteProjection, hFinite⟩

end ALG02GroupTheory.Profinite
