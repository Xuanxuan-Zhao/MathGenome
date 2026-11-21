import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.FlatGoingDown
import Mathlib.Order.Fin.Basic

universe u v

namespace P103.Ch04.FlatGoingDown

/-- Flatness gives going down via faithful flatness of the localized local maps. -/
theorem going_down : Specs.P103.Ch04.FlatGoingDown.goingDown.{u,v} := by
  intro R A _ _ g hg p p' q' hpp hq
  let := g.toAlgebra
  let : Module.Flat R A := hg
  have hle : p.asIdeal ≤ q'.asIdeal.under R := by
    change p.asIdeal ≤ (PrimeSpectrum.comap g q').asIdeal
    rw [hq]
    exact hpp
  obtain ⟨Q, hQle, hQ, hQover⟩ :=
    q'.asIdeal.exists_ideal_le_liesOver_of_le
      (p := p.asIdeal) (q := q'.asIdeal.under R) hle
  exact ⟨⟨Q, hQ⟩, hQle, PrimeSpectrum.ext hQover.over.symm⟩

/-- This also exposes the local map and its nonzero fibers explicitly. -/
theorem localized_faithful_fiber :
    Specs.P103.Ch04.FlatGoingDown.localizedFaithfulFiber.{u,v} := by
  intro R A _ _ g hg q'
  let f := Localization.localRingHom
    (q'.asIdeal.comap g) q'.asIdeal g rfl
  let := f.toAlgebra
  let : Module.Flat (Localization.AtPrime (q'.asIdeal.comap g))
      (Localization.AtPrime q'.asIdeal) := hg.localRingHom q'.asIdeal _ rfl
  let : IsLocalHom f := Localization.isLocalHom_localRingHom _ _ g rfl
  let : IsLocalHom (algebraMap (Localization.AtPrime (q'.asIdeal.comap g))
      (Localization.AtPrime q'.asIdeal)) := ‹IsLocalHom f›
  let : Module.FaithfullyFlat (Localization.AtPrime (q'.asIdeal.comap g))
      (Localization.AtPrime q'.asIdeal) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨inferInstance, fun p => inferInstance⟩

theorem finite_descending_chains :
    Specs.P103.Ch04.FlatGoingDown.finiteDescendingChains.{u,v} := by
  intro R A _ _ g hg n
  induction n with
  | zero =>
    intro p hp q₀ hq₀
    refine ⟨fun _ => q₀, fun _ _ _ => le_rfl, rfl, ?_⟩
    intro i
    simpa only [Fin.eq_zero i] using hq₀
  | succ n ih =>
    intro p hp q₀ hq₀
    obtain ⟨q₁, hq₁le, hq₁⟩ := going_down R A g hg
      (p (Fin.succ 0)) (p 0) q₀ (hp (Fin.zero_le _)) hq₀
    obtain ⟨q, hqanti, hqzero, hq⟩ := ih (fun i => p i.succ)
      (fun _ _ hij => hp (Fin.succ_le_succ_iff.mpr hij)) q₁ hq₁
    refine ⟨Fin.cons q₀ q, ?_, rfl, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j _
        refine Fin.cases le_rfl (fun j => ?_) j
        exact (hqanti (Fin.zero_le j)).trans (hqzero ▸ hq₁le)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact False.elim (not_le_of_gt (Fin.succ_pos i) hij)
        · intro hij
          exact hqanti (Fin.succ_le_succ_iff.mp hij)
    · intro i
      exact Fin.cases hq₀ hq i

theorem finite_strict_descending_chains :
    Specs.P103.Ch04.FlatGoingDown.finiteStrictDescendingChains.{u,v} := by
  intro R A _ _ g hg n p hp q₀ hq₀
  obtain ⟨q, hqa, hqzero, hq⟩ := finite_descending_chains R A g hg n p hp.antitone q₀ hq₀
  refine ⟨q, ?_, hqzero, hq⟩
  intro i j hij
  refine lt_of_le_of_ne (hqa hij.le) ?_
  intro heq
  exact (hp hij).ne ((hq j).symm.trans ((congrArg (PrimeSpectrum.comap g) heq).trans (hq i)))

end P103.Ch04.FlatGoingDown
