import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.HeightAndGrade
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.AuslanderBuchsbaum
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.PerfectModuleCriterion

/-! The finite-projective-dimension Cohen–Macaulay criterion of CM-12.
Auslander–Buchsbaum and CM-07 give the two sums whose cancellation proves
the criterion. In particular, the annihilator grade is the grade on `R`. -/

universe u
open CategoryTheory
namespace AdvCommAlg.CohenMacaulay
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Local Cohen–Macaulayness of the ring gives the prime-local ring condition. -/
lemma cohenMacaulayRing_of_localCohenMacaulay_self (hCM : LocalCohenMacaulay R R) :
    CohenMacaulayRing R := by
  intro p
  let : Nontrivial (LocalizedModule.AtPrime p.asIdeal R) := self_mem_support p
  have h := (localCohenMacaulay_iff_depth_eq _ _).mp
    (localCohenMacaulay_atPrime R hCM p (self_mem_support p))
  rw [dimension, Module.supportDim_eq_of_equiv (localizedSelfEquiv p),
    Module.supportDim_self_eq_ringKrullDim,
    IsLocalRing.depth_eq_of_linearEquiv (localizedSelfEquiv p)] at h
  exact (cohenMacaulayAt_iff_depth_eq R p).mpr h

private theorem criterion_of_projectiveDimension_eq_nat
    (hCM : LocalCohenMacaulay R R)
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (e : ℕ) (he : projectiveDimension M = (e : WithBot ℕ∞)) :
    LocalCohenMacaulay R M ↔
      projectiveDimension M = (Depth.grade (Module.annihilator R M) R : WithBot ℕ∞) := by
  have hCM' := cohenMacaulayRing_of_localCohenMacaulay_self hCM
  have hAnn : Module.annihilator R M ≠ ⊤ := by
    intro h
    exact not_subsingleton M (Module.annihilator_eq_top_iff.mp h)
  have hR : (Depth.depth R R : WithBot ℕ∞) = ringKrullDim R := by
    rw [Depth.depth_eq_libraryDepth (ModuleCat.of R R)]
    exact (localCohenMacaulay_self_iff R).mp hCM
  have hAB : (e : WithBot ℕ∞) + (Depth.depth R M : WithBot ℕ∞) = ringKrullDim R := by
    have h := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞))
      (Depth.auslanderBuchsbaum M e he)
    simpa only [WithBot.coe_add, ENat.WithBot.coe_eq_natCast] using h.trans hR
  have hdim : (Depth.grade (Module.annihilator R M) R : WithBot ℕ∞) +
      dimension R M = ringKrullDim R := by
    rw [grade_eq_height hCM' _ hAnn, dimension_eq_quotient_annihilator]
    exact height_add_quotient_dimension hCM' _ hAnn
  rw [localCohenMacaulay_iff_sourceDepth]
  constructor
  · intro hM
    rw [← hM] at hdim
    obtain ⟨t, ht⟩ := Depth.exists_depth_eq_nat M
    rw [ht] at hAB hdim
    exact he.trans (ENat.WithBot.add_natCast_cancel.mp (hAB.trans hdim.symm))
  · intro hpd
    apply (ENat.WithBot.natCast_add_cancel (c := e)).mp
    calc
      (e : WithBot ℕ∞) + (Depth.depth R M : WithBot ℕ∞) = ringKrullDim R := hAB
      _ = (Depth.grade (Module.annihilator R M) R : WithBot ℕ∞) + dimension R M :=
        hdim.symm
      _ = (e : WithBot ℕ∞) + dimension R M := by rw [← hpd, he]

/-- Over a Noetherian Cohen–Macaulay local ring, a nonzero finite module
of finite projective dimension is Cohen–Macaulay exactly when its projective
dimension equals the grade of its annihilator on the ring. -/
theorem localCohenMacaulay_iff_projectiveDimension_eq_grade
    (hCM : LocalCohenMacaulay R R)
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (hpd : projectiveDimension M ≠ ⊤) :
    LocalCohenMacaulay R M ↔
      projectiveDimension M = (Depth.grade (Module.annihilator R M) R : WithBot ℕ∞) := by
  have hnb : projectiveDimension M ≠ ⊥ := by
    intro h
    exact not_subsingleton M
      (ModuleCat.isZero_iff_subsingleton.mp ((projectiveDimension_eq_bot_iff M).mp h))
  obtain ⟨p, hp⟩ := WithBot.ne_bot_iff_exists.mp hnb
  have hpfin : p ≠ ⊤ := by
    intro h
    apply hpd
    rw [← hp, h, WithBot.coe_top]
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hpfin
  apply criterion_of_projectiveDimension_eq_nat hCM M e
  rw [← hp, ← he]
  rfl

end AdvCommAlg.CohenMacaulay
