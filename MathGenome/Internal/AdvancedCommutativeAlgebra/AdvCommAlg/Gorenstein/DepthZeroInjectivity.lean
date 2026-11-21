import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.InjectiveDimensionTest
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ZeroTest
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.DepthZeroInjectivity

/-! The last assertion of GC-05 (paper.tex:4548–4556).
A nonzero socle element gives a residue-field embedding into the free
module R. The associated Ext sequence contradicts top-degree nonvanishing
if the finite injective dimension is positive. -/

universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AdvCommAlg.Gorenstein.DepthZeroInjectivity

variable (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]

lemma exists_injective_residueField_map (hdepth : Depth.depth R R = 0) :
    ∃ f : IsLocalRing.ResidueField R →ₗ[R] R, Function.Injective f := by
  have hs := (Depth.depth_zero_iff_socle_ne_bot R R).mp hdepth
  obtain ⟨a, ha, hane⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  let f : R →ₗ[R] R := LinearMap.mulRight R a
  have hm : IsLocalRing.maximalIdeal R ≤ LinearMap.ker f := by
    intro r hr
    exact (Submodule.mem_torsionBySet_iff _ _).mp ha ⟨r, hr⟩
  have hk : LinearMap.ker f ≤ IsLocalRing.maximalIdeal R := by
    intro r hr
    by_contra h
    have hu := IsLocalRing.notMem_maximalIdeal.mp h
    have hz : r * a = 0 := hr
    exact hane ((hu.mul_right_eq_zero).mp hz)
  refine ⟨(IsLocalRing.maximalIdeal R).liftQ f hm, ?_⟩
  exact LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot _ f hm hk)

theorem injective_of_depth_zero_of_finite_injectiveDimension
    (hdepth : Depth.depth R R = 0)
    (N : ModuleCat.{u} R) [Module.Finite R N]
    (hfinite : injectiveDimension N ≠ ⊤) : Injective N := by
  classical
  by_cases hzero : Subsingleton N
  · have hz : IsZero N := ModuleCat.isZero_iff_subsingleton.mpr hzero
    have := (injectiveDimension_le_iff N 0).mp
      (show injectiveDimension N ≤ (0 : WithBot ℕ∞) by
        rw [(injectiveDimension_eq_bot_iff N).mpr hz]
        exact bot_le)
    exact (injective_iff_hasInjectiveDimensionLE_zero N).mpr this
  · have : Nontrivial N := not_subsingleton_iff_nontrivial.mp hzero
    obtain ⟨n, hn, htop⟩ :=
      InjectiveDimensionTest.finite_injectiveDimension_eq_greatest R N hfinite
    cases n with
    | zero =>
      have := (injectiveDimension_le_iff N 0).mp hn.le
      exact (injective_iff_hasInjectiveDimensionLE_zero N).mpr this
    | succ n =>
      obtain ⟨f, hf⟩ := exists_injective_residueField_map R hdepth
      let i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R R :=
        ModuleCat.ofHom f
      have : Mono i := (ModuleCat.mono_iff_injective i).mpr hf
      let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
      have : HasInjectiveDimensionLE N (n + 1) :=
        (injectiveDimension_le_iff N (n + 1)).mp hn.le
      have : Subsingleton (Ext S.X₃ N (n + 2)) :=
        HasInjectiveDimensionLT.subsingleton N (n + 2) (n + 2) le_rfl _
      have : Subsingleton (Ext S.X₂ N (n + 1)) :=
        Ext.subsingleton_of_projective (ModuleCat.of R R) N n
      have hvan : Subsingleton (Ext S.X₁ N (n + 1)) := by
        apply subsingleton_of_forall_eq 0
        intro e
        obtain ⟨e', he'⟩ := Ext.contravariant_sequence_exact₁ hS N e
          (n₁ := n + 2) (by omega) (Subsingleton.elim _ _)
        rw [← he', Subsingleton.elim e' 0]
        simp
      exact False.elim (not_nontrivial _ htop.1)

end AdvCommAlg.Gorenstein.DepthZeroInjectivity
