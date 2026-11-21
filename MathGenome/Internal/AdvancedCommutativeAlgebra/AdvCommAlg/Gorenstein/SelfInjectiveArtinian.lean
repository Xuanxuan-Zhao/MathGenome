import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.SelfInjectiveArtinian
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The first assertion of GC-05, paper.tex:4518–4536.
Stabilization of annihilators makes division by one power of an element
well defined on a principal ideal. Injectivity extends this division to the
ring. For an element of the maximal ideal the resulting relation forces
nilpotence. The finitely generated maximal ideal is then nilpotent. -/

universe u

namespace AdvCommAlg.Gorenstein

private theorem nilpotent_of_selfInjective (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Module.Injective R R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) : IsNilpotent x := by
  let f (n : ℕ) : R →ₗ[R] R := LinearMap.mulLeft R (x ^ n)
  have mono : Monotone (fun n => LinearMap.ker (f n)) := by
    apply monotone_nat_of_le_succ
    intro n r hr
    change x ^ n * r = 0 at hr
    change x ^ (n + 1) * r = 0
    rw [pow_succ', mul_assoc, hr, mul_zero]
  let chain : ℕ →o Submodule R R := ⟨_, mono⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) chain
  have hker : LinearMap.ker (f (n + 1)) = LinearMap.ker (f n) :=
    (hn (n + 1) (Nat.le_succ n)).symm
  let K := LinearMap.ker (f (n + 1))
  let i : (R ⧸ K) →ₗ[R] R := K.liftQ (f (n + 1)) le_rfl
  let g : (R ⧸ K) →ₗ[R] R := K.liftQ (f n) hker.le
  have hi : Function.Injective i := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot K (f (n + 1)) le_rfl le_rfl
  obtain ⟨h, hh⟩ := Module.Injective.out i hi g
  have heq : h (x ^ (n + 1)) = x ^ n := by
    have he := hh (K.mkQ 1)
    change h (x ^ (n + 1) * 1) = x ^ n * 1 at he
    simpa only [mul_one] using he
  have hmul : (1 - h 1 * x) * x ^ n = 0 := by
    have hlin : h (x ^ (n + 1)) = x ^ (n + 1) * h 1 := by
      simpa using h.map_smul (x ^ (n + 1)) (1 : R)
    rw [hlin] at heq
    rw [sub_mul, one_mul]
    calc
      x ^ n - h 1 * x * x ^ n = x ^ n - x ^ (n + 1) * h 1 := by
        rw [pow_succ']
        ring
      _ = 0 := sub_eq_zero.mpr heq.symm
  have hu : IsUnit (1 - h 1 * x) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.maximalIdeal R).mul_mem_left (h 1) hx)
  obtain ⟨u, hu⟩ := hu
  refine ⟨n, ?_⟩
  rw [← hu] at hmul
  exact (Units.mul_right_inj u).mp (hmul.trans (mul_zero _).symm)

/-- A self-injective Noetherian local ring is Artinian. -/
theorem isArtinianRing_of_selfInjective (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (hR : CategoryTheory.Injective (ModuleCat.of R R)) : IsArtinianRing R := by
  have := hR
  have : Module.Injective R R := Module.injective_module_of_injective_object R R
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal R).mpr
  apply (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R))).mpr
  intro x hx
  exact nilpotent_of_selfInjective R x hx

end AdvCommAlg.Gorenstein
