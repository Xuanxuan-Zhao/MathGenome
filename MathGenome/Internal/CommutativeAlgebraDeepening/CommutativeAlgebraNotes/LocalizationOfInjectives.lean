import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Noetherian.Defs

namespace CommutativeAlgebraNotes

universe u v w

variable {R : Type u} [CommRing R] {Q : Type v} [AddCommGroup Q] [Module R Q]
  {Qf : Type w} [AddCommGroup Qf] [Module R Qf]

/-- For an injective module over a Noetherian ring, localization away from one element
is surjective with kernel the torsion submodule for the principal ideal. -/
theorem localizationAway_surjective_ker_of_baer [IsNoetherianRing R] (f : R)
    (loc : Q →ₗ[R] Qf) [IsLocalizedModule.Away f loc] (hQ : Module.Baer R Q) :
    Function.Surjective loc ∧ LinearMap.ker loc = idealTorsion (Ideal.span {f}) Q := by
  constructor
  · intro y
    obtain ⟨a, e, hy⟩ := IsLocalizedModule.Away.surj loc f y
    let mulF : Module.End R R := algebraMap R (Module.End R R) f
    obtain ⟨b, hb⟩ := monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherianRing R› mulF.iterateKer
    let p : R →ₗ[R] R := mulF ^ (a + b)
    let g : R →ₗ[R] Q := LinearMap.id.smulRight (f ^ b • e)
    have hp (r : R) : p r = f ^ (a + b) * r := by
      simp [p, mulF, ← map_pow, Module.algebraMap_end_apply, smul_eq_mul]
    have hker : LinearMap.ker p ≤ LinearMap.ker g := by
      intro r hr
      have hstable : LinearMap.ker (mulF ^ b) = LinearMap.ker p :=
        hb (a + b) (Nat.le_add_left b a)
      have hr' : (mulF ^ b) r = 0 := LinearMap.mem_ker.mp (hstable.symm ▸ hr)
      have hmul : f ^ b * r = 0 := by
        simpa [mulF, ← map_pow, Module.algebraMap_end_apply, smul_eq_mul] using hr'
      change r • (f ^ b • e) = 0
      rw [← mul_smul, mul_comm r, hmul, zero_smul]
    -- Descend the map to the principal ideal that is the range of `p`, then extend.
    have hker' : LinearMap.ker p.rangeRestrict ≤ LinearMap.ker g := by
      rwa [LinearMap.ker_rangeRestrict]
    let descend := p.rangeRestrict.liftOfSurjective p.surjective_rangeRestrict ⟨g, hker'⟩
    obtain ⟨extend, hextend⟩ := hQ (LinearMap.range p) descend
    have hextend_one : extend (p 1) = f ^ b • e := calc
      extend (p 1) = descend (p.rangeRestrict 1) := hextend _ _
      _ = g 1 := LinearMap.equivOfSurjective_apply p.surjective_rangeRestrict hker'
      _ = _ := one_smul _ _
    have hq : f ^ (a + b) • extend 1 = f ^ b • e := by
      rw [← extend.map_smul]
      simpa only [hp, mul_one, smul_eq_mul] using hextend_one
    refine ⟨extend 1, IsLocalizedModule.smul_injective loc
      (⟨f ^ (a + b), a + b, rfl⟩ : Submonoid.powers f) ?_⟩
    change f ^ (a + b) • loc (extend 1) = f ^ (a + b) • y
    rw [← loc.map_smul, hq, loc.map_smul, ← hy, pow_add, mul_comm (f ^ a), mul_smul]
  · ext x
    rw [LinearMap.mem_ker, IsLocalizedModule.eq_zero_iff (Submonoid.powers f) loc,
      mem_idealTorsion]
    constructor
    · rintro ⟨⟨_, n, rfl⟩, hn⟩
      have hn' : f ^ n • x = 0 := hn
      have hnext : f ^ (n + 1) • x = 0 := by
        rw [pow_succ', mul_smul, hn', smul_zero]
      refine ⟨n + 1, Nat.succ_pos n, fun r hr => ?_⟩
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr
      obtain ⟨c, rfl⟩ := hr
      rw [mul_comm (f ^ (n + 1)) c, mul_smul, hnext, smul_zero]
    · rintro ⟨n, _, hn⟩
      refine ⟨⟨f ^ n, n, rfl⟩, hn _ ?_⟩
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _

/-- The localization-away lemma in terms of Mathlib's injective module class. -/
theorem localizationAway_surjective_ker [IsNoetherianRing R] [Small.{v} R] [Module.Injective R Q]
    (f : R) (loc : Q →ₗ[R] Qf) [IsLocalizedModule.Away f loc] :
    Function.Surjective loc ∧ LinearMap.ker loc = idealTorsion (Ideal.span {f}) Q :=
  localizationAway_surjective_ker_of_baer f loc (Module.Baer.of_injective inferInstance)

end CommutativeAlgebraNotes
