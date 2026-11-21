import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Homological.RegularQuotientProjectiveDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Homological.MinimalFreeResolution
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.LocalRing.RingHom.Basic

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped Pointwise
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvCommAlg

variable {R : Type u} [CommRing R] (x : R)

@[simp] lemma regularQuotientFunctor_map_mk {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (m : M) :
    (regularQuotientFunctor x).map f (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (f m) := rfl

/-- Right exactness of reduction, with the quotient-ring scalar structure. -/
lemma regularQuotient_shortExact (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (hx : IsSMulRegular S.X₃ x) :
    (S.map (regularQuotientFunctor x)).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact QuotSMulTop.map_exact x
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
      hS.moduleCat_surjective_g
  · rw [ModuleCat.mono_iff_injective]
    have hzero : Function.Exact (0 : S.X₁ →ₗ[R] S.X₁) S.f.hom := by
      rw [LinearMap.exact_zero_iff_injective]
      exact hS.moduleCat_injective_f
    have h := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
      (r := x) hzero
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) hx
    have hz : QuotSMulTop.map x (0 : S.X₁ →ₗ[R] S.X₁) = 0 := map_zero _
    rw [hz, LinearMap.exact_zero_iff_injective] at h
    exact h
  · rw [ModuleCat.epi_iff_surjective]
    exact QuotSMulTop.map_surjective x hS.moduleCat_surjective_g

instance regularQuotient_finite (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite (R ⧸ Ideal.span {x}) ((regularQuotientFunctor x).obj M) :=
  Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x M)

/-- A regular scalar on R is regular on a free module. -/
lemma regular_on_free (hx : IsSMulRegular R x) (F : ModuleCat.{u} R)
    [Module.Free R F] : IsSMulRegular F x :=
  ((TensorProduct.rid R F).isSMulRegular_congr x).mp (hx.lTensor F)

section Dimension

variable [IsNoetherianRing R] [IsLocalRing R]

/-- Reduction preserves every finite projective dimension bound. This statement
also permits the zero module, which is necessary for the kernel induction. -/
lemma regularQuotient_hasProjectiveDimensionLE_iff
    (hmem : x ∈ IsLocalRing.maximalIdeal R) (hxR : IsSMulRegular R x)
    (n : ℕ) (M : ModuleCat.{u} R) [Module.Finite R M] (hxM : IsSMulRegular M x) :
    HasProjectiveDimensionLE M n ↔
      HasProjectiveDimensionLE ((regularQuotientFunctor x).obj M) n := by
  have hproper : Ideal.span ({x} : Set R) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    exact Ideal.span_le.mpr (by simpa using hmem)
  let : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  induction n generalizing M with
  | zero =>
    rw [← projective_iff_hasProjectiveDimensionLE_zero,
      ← projective_iff_hasProjectiveDimensionLE_zero]
    constructor
    · intro hp
      have : Projective M := hp
      have : Module.Free R M := finite_projective_free M
      change Projective (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M))
      infer_instance
    · intro hp
      have : Projective ((regularQuotientFunctor x).obj M) := hp
      have : Module.Projective (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
        ModuleCat.projective_of_module_projective ((regularQuotientFunctor x).obj M)
      have : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) := regularQuotient_finite x M
      have : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
        Module.free_of_flat_of_isLocalRing
      have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
      have : Module.Free R M := (Module.free_quotSMulTop_iff_free R M
        (by simpa only [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] using hmem)
        hxM).mp inferInstance
      infer_instance
  | succ n ih =>
    obtain ⟨F, hfin, hfree, f, hsurj, _⟩ := exists_minimalFreeCover M
    let : Module.Finite R F := hfin
    let : Module.Free R F := hfree
    let S := f.hom.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hsurj
    have hred := regularQuotient_shortExact x S hS hxM
    have hK : IsSMulRegular S.X₁ x :=
      (regular_on_free x hxR F).of_injective S.f.hom hS.moduleCat_injective_f
    change HasProjectiveDimensionLT S.X₃ (n + 2) ↔
      HasProjectiveDimensionLT (S.map (regularQuotientFunctor x)).X₃ (n + 2)
    rw [hS.hasProjectiveDimensionLT_X₃_iff n (by dsimp [S]; infer_instance),
      hred.hasProjectiveDimensionLT_X₃_iff n (by
        change Projective (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x F))
        infer_instance)]
    exact ih S.X₁ hK

/-- The quotient-ring comparison of DP-13. -/
theorem regularQuotient_projectiveDimension :
    Specs.AdvCommAlg.regularQuotient_projectiveDimension.{u} := by
  intro R _ _ _ M _ _ x hmem hxR hxM e he
  have hb := regularQuotient_hasProjectiveDimensionLE_iff x hmem hxR e M hxM
  have hu : projectiveDimension ((regularQuotientFunctor x).obj M) ≤ (e : WithBot ℕ∞) :=
    (projectiveDimension_le_iff _ e).mpr (hb.mp ((projectiveDimension_le_iff _ e).mp he.le))
  refine le_antisymm hu ?_
  by_contra hn
  have hlt : projectiveDimension ((regularQuotientFunctor x).obj M) < (e : WithBot ℕ∞) :=
    lt_of_not_ge hn
  cases e with
  | zero =>
    have hz : IsZero ((regularQuotientFunctor x).obj M) :=
      (hasProjectiveDimensionLT_zero_iff_isZero _).mp (projectiveDimension_lt_iff.mp hlt)
    have : Subsingleton (QuotSMulTop x M) := ModuleCat.subsingleton_of_isZero hz
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hmem
    exact not_subsingleton (QuotSMulTop x M) inferInstance
  | succ b =>
    have hle : HasProjectiveDimensionLE ((regularQuotientFunctor x).obj M) b :=
      projectiveDimension_lt_iff.mp hlt
    have hM : projectiveDimension M ≤ (b : WithBot ℕ∞) :=
      (projectiveDimension_le_iff _ b).mpr
        ((regularQuotient_hasProjectiveDimensionLE_iff x hmem hxR b M hxM).mpr hle)
    rw [he] at hM
    exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self b)) hM

end Dimension

section Resolution

variable {M : ModuleCat.{u} R} (P : ProjectiveResolution M)

/-- The original free resolution with every term and differential reduced modulo x. -/
abbrev regularQuotientComplex : ChainComplex (ModuleCat.{u} (R ⧸ Ideal.span {x})) ℕ :=
  ((regularQuotientFunctor x).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex

/-- The augmentation is the reduction of the original augmentation. -/
noncomputable def regularQuotientAugmentation : regularQuotientComplex x P ⟶
    (ChainComplex.single₀ (ModuleCat (R ⧸ Ideal.span {x}))).obj
      ((regularQuotientFunctor x).obj M) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(regularQuotientFunctor x).map (P.π.f 0), by
      change (regularQuotientFunctor x).map (P.complex.d 1 0) ≫
        (regularQuotientFunctor x).map (P.π.f 0) = 0
      rw [← Functor.map_comp, P.complex_d_comp_π_f_zero, Functor.map_zero]⟩

/-- Positive-degree exactness follows from the four-term quotient lemma.
At degree one the last module is M; in higher degrees it is a free term. -/
lemma regularQuotientComplex_exactAt_succ
    (hfree : ∀ i, Module.Free R (P.complex.X i))
    (hxR : IsSMulRegular R x) (hxM : IsSMulRegular M x) (n : ℕ) :
    (regularQuotientComplex x P).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact (QuotSMulTop.map x (P.complex.d (n + 2) (n + 1)).hom)
    (QuotSMulTop.map x (P.complex.d (n + 1) n).hom)
  have hn := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ n)
  cases n with
  | zero =>
    exact QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last hn
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀) hxM
  | succ n =>
    have := hfree n
    exact QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last hn
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ n))
      (regular_on_free x hxR (P.complex.X n))

/-- Reduction resolves M/xM; exactness is proved before assigning the resolution. -/
lemma regularQuotientAugmentation_quasiIso
    (hfree : ∀ i, Module.Free R (P.complex.X i))
    (hxR : IsSMulRegular R x) (hxM : IsSMulRegular M x) :
    QuasiIso (regularQuotientAugmentation x P) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine ⟨?_, ?_⟩
      · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
        change Function.Exact (QuotSMulTop.map x (P.complex.d 1 0).hom)
          (QuotSMulTop.map x (P.π.f 0).hom)
        exact QuotSMulTop.map_exact x
          ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀)
          ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      · change Epi ((regularQuotientFunctor x).map (P.π.f 0))
        rw [ModuleCat.epi_iff_surjective]
        exact QuotSMulTop.map_surjective x
          ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    · change (regularQuotientComplex x P).d 0 0 = 0
      simp
    · change ((ChainComplex.single₀ (ModuleCat (R ⧸ Ideal.span {x}))).obj _).d 1 0 = 0
      simp
    · change ((ChainComplex.single₀ (ModuleCat (R ⧸ Ideal.span {x}))).obj _).d 0 0 = 0
      simp
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ n)]
    exact regularQuotientComplex_exactAt_succ x P hfree hxR hxM n

/-- The reduced free resolution, with its canonical augmentation. -/
noncomputable def regularQuotientResolution
    (hfree : ∀ i, Module.Free R (P.complex.X i))
    (hxR : IsSMulRegular R x) (hxM : IsSMulRegular M x) :
    ProjectiveResolution ((regularQuotientFunctor x).obj M) where
  complex := regularQuotientComplex x P
  projective i := by
    have := hfree i
    change Projective (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (P.complex.X i)))
    infer_instance
  π := regularQuotientAugmentation x P
  quasiIso := regularQuotientAugmentation_quasiIso x P hfree hxR hxM

end Resolution

/-- The reduced finite free resolution required in DP-13. -/
theorem regularQuotient_resolution : Specs.AdvCommAlg.regularQuotient_resolution.{u} := by
  intro R _ _ _ M _ _ x _ hxR hxM P hP e he
  refine ⟨regularQuotientResolution x P hP.free hxR hxM, rfl, ?_, ?_, ?_⟩
  · rfl
  · intro i
    have := hP.finite i
    have := hP.free i
    change Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x (P.complex.X i)) ∧
      Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x (P.complex.X i))
    exact ⟨regularQuotient_finite x (P.complex.X i), inferInstance⟩
  · intro i hi
    have := minimalFreeResolution_vanishes_above M P hP e he.le i hi
    change Subsingleton (QuotSMulTop x (P.complex.X i))
    infer_instance

end AdvCommAlg
