import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.FiniteFieldStandardFactors
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.Permanence
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.CompositeNotStandard
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace AdvCommAlg.Etale.CompositeNotStandard

noncomputable section
open Polynomial
open Specs.AdvCommAlg.Etale.StandardAndPointwise
open Specs.AdvCommAlg.Etale.FiniteFieldStandardFactors
open Specs.AdvCommAlg.Etale.CompositeNotStandard

set_option backward.isDefEq.respectTransparency false in
theorem unique_quadratic : uniqueQuadratic := by
  intro p hm hd hi
  have hp : p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    ext n
    rcases n with _ | _ | _ | n
    · simp
    · simp
    · have hc : p.coeff 2 = 1 := by simpa [hd] using hm.coeff_natDegree
      simp [hc]
    · have hn : p.natDegree < n + 1 + 1 + 1 := by omega
      simp [coeff_eq_zero_of_natDegree_lt hn, show n + 1 + 1 + 1 ≠ 2 by omega]
  have h0 : ¬ p.IsRoot 0 := hi.not_isRoot_of_natDegree_ne_one (by omega)
  have h1 : ¬ p.IsRoot 1 := hi.not_isRoot_of_natDegree_ne_one (by omega)
  generalize ha : p.coeff 0 = a at hp
  generalize hb : p.coeff 1 = b at hp
  fin_cases a <;> fin_cases b <;>
    simp_all [IsRoot, quadratic, CharTwo.add_self_eq_zero]

variable {K : Type} [Field K] [Fintype K] [Algebra (ZMod 2) K]

/-- A surjective polynomial evaluation onto a four-element field cannot send
X into the prime field. -/
lemma generator_not_scalar (hK : Fintype.card K = 4)
    (φ : (ZMod 2)[X] →ₐ[ZMod 2] K) (hφ : Function.Surjective φ) (a : ZMod 2) :
    φ X ≠ algebraMap (ZMod 2) K a := by
  intro h
  have he : φ = (Algebra.ofId (ZMod 2) K).comp (aeval a) := by
    apply Polynomial.algHom_ext
    simpa using h
  have hs : Function.Surjective (algebraMap (ZMod 2) K) := by
    intro y
    obtain ⟨p, hp⟩ := hφ y
    exact ⟨aeval a p, by simpa [he, Algebra.ofId] using hp⟩
  have hc := Fintype.card_le_of_surjective _ hs
  rw [hK, ZMod.card] at hc
  norm_num at hc

/-- Every surjective evaluation has precisely the unique quadratic as kernel. -/
lemma polynomial_kernel (hK : Fintype.card K = 4)
    (φ : (ZMod 2)[X] →ₐ[ZMod 2] K) (hφ : Function.Surjective φ) :
    RingHom.ker φ = Ideal.span ({quadratic} : Set (ZMod 2)[X]) := by
  have hx0 : φ X ≠ 0 := by simpa using generator_not_scalar hK φ hφ 0
  have hx1 : φ X ≠ 1 := by simpa using generator_not_scalar hK φ hφ 1
  have hp : (φ X) ^ 3 = 1 := by
    simpa [hK] using FiniteField.pow_card_sub_one_eq_one (φ X) hx0
  have hroot : φ quadratic = 0 := by
    have hmul : (φ X - 1) * ((φ X)^2 + φ X + 1) = 0 := by
      linear_combination hp
    have hr := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hx1)
    simpa [quadratic] using hr
  let : Fact (Irreducible quadratic) := ⟨FiniteFieldStandardFactors.quadratic_irreducible⟩
  have hm : (Ideal.span ({quadratic} : Set (ZMod 2)[X])).IsMaximal := inferInstance
  exact (hm.eq_of_le (RingHom.ker_ne_top φ)
    (Ideal.span_le.mpr (by simpa using hroot))).symm

/-- Localization does not enlarge an image in a finite field: inverses of
nonzero denominator images are their squares when the field has order four. -/
lemma polynomial_map_surjective (hK : Fintype.card K = 4) (f g : (ZMod 2)[X])
    (φ : LocalizedQuotient f g →ₐ[ZMod 2] K) (hφ : Function.Surjective φ) :
    Function.Surjective
      ((φ.comp (IsScalarTower.toAlgHom (ZMod 2) (AdjoinRoot f) _)).comp
        (AdjoinRoot.mkₐ f)) := by
  intro y
  obtain ⟨z, rfl⟩ := hφ y
  obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (AdjoinRoot.mk f g)) z
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective r
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective (s : AdjoinRoot f)
  have hu : φ (algebraMap (AdjoinRoot f) _ s) ≠ 0 :=
    ((IsLocalization.map_units (LocalizedQuotient f g) s).map φ).ne_zero
  have hpow : φ (algebraMap (AdjoinRoot f) _ s) ^ 3 = 1 := by
    simpa [hK] using FiniteField.pow_card_sub_one_eq_one _ hu
  have heq := congrArg φ hs
  simp only [map_mul] at heq
  refine ⟨p * q ^ 2, ?_⟩
  simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, map_mul, map_pow]
  change φ (algebraMap (AdjoinRoot f) _ (AdjoinRoot.mk f p)) *
    φ (algebraMap (AdjoinRoot f) _ (AdjoinRoot.mk f q)) ^ 2 = φ z
  rw [hp, hq, ← heq]
  calc
    (φ z * φ (algebraMap (AdjoinRoot f) _ s)) *
        φ (algebraMap (AdjoinRoot f) _ s) ^ 2 =
        φ z * φ (algebraMap (AdjoinRoot f) _ s) ^ 3 := by ring
    _ = φ z := by rw [hpow, mul_one]

/-- Pulling kernels back through a localization and its polynomial quotient
is injective on ideals. -/
lemma localized_kernel_unique (hK : Fintype.card K = 4) (f g : (ZMod 2)[X])
    (φ ψ : LocalizedQuotient f g →ₐ[ZMod 2] K)
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ) :
    RingHom.ker φ = RingHom.ker ψ := by
  apply (IsLocalization.orderEmbedding (Submonoid.powers (AdjoinRoot.mk f g))
    (LocalizedQuotient f g)).injective
  apply Ideal.comap_injective_of_surjective (AdjoinRoot.mk f) AdjoinRoot.mk_surjective
  exact (polynomial_kernel hK _ (polynomial_map_surjective hK f g φ hφ)).trans
    (polynomial_kernel hK _ (polynomial_map_surjective hK f g ψ hψ)).symm

/-- A prime with finite residue field is maximal, since its quotient is a
finite domain. Consequently the residue map is surjective. -/
lemma finite_residue_map_surjective {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime]
    [Finite p.ResidueField] : Function.Surjective (algebraMap R p.ResidueField) := by
  let : Finite (R ⧸ p) := Finite.of_injective _ p.injective_algebraMap_quotient_residueField
  let : p.IsMaximal := Ideal.Quotient.maximal_of_isField p (Finite.isField_of_domain (R ⧸ p))
  exact p.algebraMap_residueField_surjective

theorem localized_residue_obstruction : localizedResidueObstruction := by
  intro K _ _ _ hK f g p q ⟨ep⟩ ⟨eq⟩
  let : Finite p.asIdeal.ResidueField := Finite.of_injective ep ep.injective
  let : Finite q.asIdeal.ResidueField := Finite.of_injective eq eq.injective
  let φ := ep.toAlgHom.comp
    (IsScalarTower.toAlgHom (ZMod 2) (LocalizedQuotient f g) p.asIdeal.ResidueField)
  let ψ := eq.toAlgHom.comp
    (IsScalarTower.toAlgHom (ZMod 2) (LocalizedQuotient f g) q.asIdeal.ResidueField)
  have hk := localized_kernel_unique hK f g φ ψ
    (ep.surjective.comp (finite_residue_map_surjective p.asIdeal))
    (eq.surjective.comp (finite_residue_map_surjective q.asIdeal))
  apply PrimeSpectrum.ext
  have hφ : RingHom.ker φ = p.asIdeal := by
    ext x
    change ep (algebraMap _ _ x) = 0 ↔ x ∈ p.asIdeal
    rw [map_eq_zero_iff ep ep.injective, Ideal.algebraMap_residueField_eq_zero]
  have hψ : RingHom.ker ψ = q.asIdeal := by
    ext x
    change eq (algebraMap _ _ x) = 0 ↔ x ∈ q.asIdeal
    rw [map_eq_zero_iff eq eq.injective, Ideal.algebraMap_residueField_eq_zero]
  exact hφ.symm.trans (hk.trans hψ)

/-- The four coordinate kernels. -/
def coordinatePrime (i : Fin 4) : PrimeSpectrum (Fin 4 → K) :=
  ⟨RingHom.ker (Pi.evalAlgHom (ZMod 2) (fun _ : Fin 4 => K) i), RingHom.ker_isPrime _⟩

omit [Fintype K] in
lemma coordinatePrime_injective : Function.Injective (coordinatePrime (K := K)) := by
  intro i j h
  by_contra hij
  have hk := congrArg PrimeSpectrum.asIdeal h
  have hz : Pi.single i (1 : K) ∈ (coordinatePrime (K := K) j).asIdeal := by
    simp [coordinatePrime, Ne.symm hij]
  rw [← hk] at hz
  simp [coordinatePrime] at hz

omit [Fintype K] in
lemma coordinatePrime_residue (i : Fin 4) :
    Nonempty ((coordinatePrime (K := K) i).asIdeal.ResidueField ≃ₐ[ZMod 2] K) := by
  let φ := Pi.evalAlgHom (ZMod 2) (fun _ : Fin 4 => K) i
  have hφ : Function.Surjective φ := fun y => ⟨fun _ => y, rfl⟩
  let p := RingHom.ker φ
  let : p.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφ
  let e : ((Fin 4 → K) ⧸ p) ≃ₐ[ZMod 2] p.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom (ZMod 2) _ _)
      p.bijective_algebraMap_quotient_residueField
  exact ⟨e.symm.trans (Ideal.quotientKerAlgEquivOfSurjective hφ)⟩

theorem four_residue_primes : fourResiduePrimes := by
  intro K _ _ _ _
  exact ⟨coordinatePrime, coordinatePrime_injective, coordinatePrime_residue⟩

theorem no_single_variable_presentation : noSingleVariablePresentation := by
  intro K _ _ _ hK f g ⟨e⟩
  let φ := (Pi.evalAlgHom (ZMod 2) (fun _ : Fin 4 => K) 0).comp e.symm.toAlgHom
  let ψ := (Pi.evalAlgHom (ZMod 2) (fun _ : Fin 4 => K) 1).comp e.symm.toAlgHom
  have hφ : Function.Surjective φ := by
    intro y
    exact ⟨e (fun _ => y), by simp [φ]⟩
  have hψ : Function.Surjective ψ := by
    intro y
    exact ⟨e (fun _ => y), by simp [ψ]⟩
  have hk := localized_kernel_unique hK f g φ ψ hφ hψ
  have hz : e (Pi.single (0 : Fin 4) (1 : K)) ∈ RingHom.ker ψ := by simp [ψ]
  rw [← hk] at hz
  simp [φ] at hz

theorem composite_example : compositeExample := by
  intro K _ _ _ hK
  have hfirst := (FiniteFieldStandardFactors.first_presentation K hK).2.2.2
  have hsecond := (FiniteFieldStandardFactors.second_presentation K hK).2.2.2
  have hfirst' : Algebra.IsStandardEtale (ZMod 2) K := (standardEtale_iff _ _).mp hfirst
  have hsecond' : Algebra.IsStandardEtale K (Fin 4 → K) := (standardEtale_iff _ _).mp hsecond
  let := hfirst'
  let := hsecond'
  refine ⟨hfirst, hsecond, etale_composition (ZMod 2) K (Fin 4 → K)
    (by change Algebra.Etale _ _; infer_instance)
    (by change Algebra.Etale _ _; infer_instance), ?_⟩
  rintro ⟨f, _, g, _, he⟩
  exact no_single_variable_presentation K hK f g he

end
end AdvCommAlg.Etale.CompositeNotStandard
