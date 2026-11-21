import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.FiniteExtDetection
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.LocalRing.Module

/-!
The finite-module detection stage in GC-02 (paper.tex:4410–4452).
We use Noetherian induction on annihilating ideals, rather than numerical
support dimension. Prime filtrations reduce to prime cyclic modules. For a
nonmaximal prime choose x in the maximal ideal outside the prime. The cokernel
of multiplication by x is killed by a strictly larger ideal. The long exact
Ext sequence, the scalar-action identity, and Nakayama finish the induction.
This proof also appears in the Stacks Project, more-algebra.tex,
lemma-finite-injective-dimension-Noetherian-radical (specialized to modules).
-/

universe u v
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped Pointwise
namespace AdvCommAlg.Gorenstein.FiniteExtDetection

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- Transport Ext vanishing along a linear equivalence in the first variable. -/
lemma subsingleton_ext_of_linearEquiv {A B N : ModuleCat.{v} R}
    (e : A ≃ₗ[R] B) (i : ℕ) [Subsingleton (Ext B N i)] :
    Subsingleton (Ext A N i) := by
  apply subsingleton_of_forall_eq 0
  intro x
  have hz : (Ext.mk₀ (ModuleCat.ofHom e.symm.toLinearMap)).comp x (zero_add i) = 0 :=
    Subsingleton.elim _ _
  have hh := congrArg (fun y =>
    (Ext.mk₀ (ModuleCat.ofHom e.toLinearMap)).comp y (zero_add i)) hz
  have he : ModuleCat.ofHom e.toLinearMap ≫ ModuleCat.ofHom e.symm.toLinearMap = 𝟙 A := by
    ext a
    exact e.symm_apply_apply a
  simpa only [Ext.mk₀_comp_mk₀_assoc, he, Ext.mk₀_id_comp, Ext.comp_zero] using hh

/-- Ext is zero in every degree when its first argument is zero. -/
lemma subsingleton_ext_of_subsingleton (A N : ModuleCat.{v} R) [Subsingleton A] (i : ℕ) :
    Subsingleton (Ext A N i) := by
  apply subsingleton_of_forall_eq 0
  intro x
  have h : 𝟙 A = 0 := (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).eq_zero_of_src _
  have hh := Ext.mk₀_id_comp x
  rw [h] at hh
  simpa using hh.symm

/-- In a short exact sequence, vanishing for the outer terms implies vanishing
for the middle term, at the same degree. -/
lemma subsingleton_ext_of_shortExact {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) (N : ModuleCat.{v} R) (i : ℕ)
    [Subsingleton (Ext S.X₁ N i)] [Subsingleton (Ext S.X₃ N i)] :
    Subsingleton (Ext S.X₂ N i) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₂ hS N x (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0] at hy
  simpa using hy.symm

omit [Small.{v} R] in
/-- Nakayama in the form needed for the Ext endomorphism. -/
lemma subsingleton_of_surjective_smul [IsLocalRing R]
    (E : Type v) [AddCommGroup E] [Module R E] [Module.Finite R E]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hsurj : Function.Surjective (fun z : E => x • z)) : Subsingleton E := by
  have heq : (⊤ : Submodule R E) = x • (⊤ : Submodule R E) := by
    apply le_antisymm _ le_top
    intro z _
    obtain ⟨w, rfl⟩ := hsurj z
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_top)
  have hz : (⊤ : Submodule R E) = ⊥ :=
    Submodule.eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator
      Module.Finite.fg_top heq (by
        rw [Submodule.annihilator_top]
        exact IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R E) hx)
  exact subsingleton_of_forall_eq 0 (fun z => by
    have : z ∈ (⊥ : Submodule R E) := hz ▸ Submodule.mem_top
    exact this)

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing for the cokernel makes multiplication by x surjective on Ext;
finiteness and Nakayama then kill Ext itself. -/
lemma subsingleton_ext_of_smul_cokernel [IsNoetherianRing R] [IsLocalRing R]
    (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x)
    (i : ℕ) [Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x M)) N (1 + i))] :
    Subsingleton (Ext M N i) := by
  apply subsingleton_of_surjective_smul (Ext M N i) x hx
  intro z
  have : Subsingleton (Ext (M.smulShortComplex x).X₃ N (1 + i)) := by
    change Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x M)) N (1 + i))
    infer_instance
  obtain ⟨w, hw⟩ := Ext.contravariant_sequence_exact₁
    hreg.smulShortComplex_shortExact N z (n₁ := 1 + i) rfl (Subsingleton.elim _ _)
  refine ⟨w, ?_⟩
  change (Ext.mk₀ (x • 𝟙 M)).comp w (zero_add i) = z at hw
  simpa only [ModuleCat.smulShortComplex_f_eq_smul_id, Ext.mk₀_smul,
    Ext.smul_comp, Ext.mk₀_id_comp] using hw

omit [Small.{v} R] in
/-- Scalar multiplication outside a prime is injective on its cyclic quotient. -/
lemma isSMulRegular_of_equiv_prime_quotient (M : Type v) [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (e : M ≃ₗ[R] R ⧸ p.asIdeal) (x : R) (hx : x ∉ p.asIdeal) :
    IsSMulRegular M x := by
  let : p.asIdeal.IsPrime := p.isPrime
  apply IsSMulRegular.of_injective e e.injective
  intro a b hab
  apply mul_left_cancel₀ (show (algebraMap R (R ⧸ p.asIdeal)) x ≠ 0 from
    fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mp h))
  simpa only [Algebra.smul_def] using hab

set_option backward.isDefEq.respectTransparency false in
/-- Residue-field Ext vanishing propagates to every finite first argument.
The induction is on annihilating ideals, ordered by strict reverse inclusion. -/
theorem finite_ext_vanishing (R : Type u) [CommRing R] [Nontrivial R]
    [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R]
    (N : ModuleCat.{v} R) [Module.Finite R N] (n : ℕ)
    (h : ∀ i : ℕ, n < i →
      Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R))) N i))
    (M : ModuleCat.{v} R) [Module.Finite R M] (i : ℕ) (hi : n < i) :
    Subsingleton (Ext M N i) := by
  classical
  have H : ∀ (I : Ideal R) (A : Type v) [AddCommGroup A] [Module R A] [Module.Finite R A],
      I ≤ Module.annihilator R A → ∀ j : ℕ, n < j →
      Subsingleton (Ext (ModuleCat.of R A) N j) := by
    intro I
    induction I using WellFoundedGT.induction with
    | ind I ih =>
      intro A _ _ hfin
      induction hfin using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
      | subsingleton A =>
        intro _ j _
        exact subsingleton_ext_of_subsingleton (ModuleCat.of R A) N j
      | quotient A p e =>
        intro hI j hj
        have hann : Module.annihilator R A = p.asIdeal := by
          rw [e.annihilator_eq, Ideal.annihilator_quotient]
        have hIp : I ≤ p.asIdeal := hann ▸ hI
        by_cases hEq : I = p.asIdeal
        · subst I
          by_cases hp : p.asIdeal = IsLocalRing.maximalIdeal R
          · have e' : A ≃ₗ[R] R ⧸ IsLocalRing.maximalIdeal R :=
              e.trans (Submodule.quotEquivOfEq _ _ hp)
            have := h j hj
            exact subsingleton_ext_of_linearEquiv
              (B := ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R)))
              (e'.trans (Shrink.linearEquiv R _).symm) j
          · have hplt : p.asIdeal < IsLocalRing.maximalIdeal R :=
              lt_of_le_of_ne (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) hp
            obtain ⟨x, hxm, hxp⟩ := IsConcreteLE.exists_of_lt hplt
            let J : Ideal R := p.asIdeal ⊔ Ideal.span {x}
            have hpJ : p.asIdeal < J := by
              apply lt_of_le_of_ne le_sup_left
              intro heq
              apply hxp
              rw [heq]
              exact (show Ideal.span {x} ≤ J from le_sup_right)
                (Ideal.subset_span (Set.mem_singleton x))
            have hJ : J ≤ Module.annihilator R (QuotSMulTop x A) := by
              apply sup_le
              · rw [← hann]
                exact LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)
              · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
                  (QuotSMulTop.mem_annihilator A x))
            have := ih J hpJ (QuotSMulTop x A) hJ (1 + j) (by omega)
            exact subsingleton_ext_of_smul_cokernel (ModuleCat.of R A) N x hxm
              (isSMulRegular_of_equiv_prime_quotient A p e x hxp) j
        · exact ih p.asIdeal (lt_of_le_of_ne hIp hEq) A (by rw [hann]) j hj
      | exact A₁ A₂ A₃ f g hf hg hfg h₁ h₃ =>
        intro hI j hj
        let S := ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero
        have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hfg hf hg
        have := h₁ (hI.trans (f.annihilator_le_of_injective hf)) j hj
        have := h₃ (hI.trans (g.annihilator_le_of_surjective hg)) j hj
        exact subsingleton_ext_of_shortExact hS N j
  exact H ⊥ M bot_le i hi

end AdvCommAlg.Gorenstein.FiniteExtDetection
