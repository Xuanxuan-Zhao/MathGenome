import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.LocalDetection
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.LocalizationBound
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.LocalExtVanishing

/-! The local Ext-vanishing bound of DP-11. -/

universe u
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.Depth

/-- Every prime in the support bounds the dimension of its closed subset
by the dimension of the whole support. -/
lemma dim_quotient_le_supportDim_of_mem_support
    {R : Type u} [CommRing R] (N : Type u) [AddCommGroup N] [Module R N]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R N) :
    ringKrullDim (R ⧸ p.asIdeal) ≤ Module.supportDim R N := by
  rw [ringKrullDim_quotient]
  exact Order.krullDim_le_of_strictMono
    (fun q : PrimeSpectrum.zeroLocus (p.asIdeal : Set R) =>
      (⟨q.1, Module.mem_support_mono q.2 hp⟩ : Module.support R N))
    (fun _ _ h => h)

/-- Ext vanishes in the full nonnegative range below depth minus support
dimension. The additive inequality avoids truncated subtraction. -/
theorem ext_subsingleton_of_add_supportDim_lt_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (N M : ModuleCat.{u} R) [Module.Finite R N] [Module.Finite R M]
    [Nontrivial N] [Nontrivial M] (i : ℕ)
    (hi : (i : WithBot ℕ∞) + Module.supportDim R N < (depth R M : WithBot ℕ∞)) :
    Subsingleton (Ext N M i) := by
  apply ModuleCat.subsingleton_ext_of_lt_depth
  rw [← grade_eq_extDepth N M]
  by_contra h
  have hgi : grade (Module.annihilator R N) M ≤ (i : ℕ∞) := le_of_not_gt h
  have hproper : Module.annihilator R N • (⊤ : Submodule R M) ≠ ⊤ := by
    intro he
    rw [grade_of_smul_eq_top _ _ he] at hgi
    simp at hgi
  obtain ⟨p, hIp, hpM, he⟩ :=
    exists_localDepth_eq_grade M (Module.annihilator R N) hproper
  have hpN : p ∈ Module.support R N := by
    rw [Module.support_eq_zeroLocus]
    exact hIp
  have hdim := dim_quotient_le_supportDim_of_mem_support N p hpN
  have hb := depth_le_localized_depth_add_dim R M p.asIdeal
  rw [he] at hb
  have hle : (depth R M : WithBot ℕ∞) ≤
      (i : WithBot ℕ∞) + Module.supportDim R N :=
    hb.trans (add_le_add (WithBot.coe_le_coe.mpr hgi) hdim)
  exact (not_lt_of_ge hle) hi

end AdvCommAlg.Depth
