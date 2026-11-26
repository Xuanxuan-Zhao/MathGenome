import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.AdicFiniteGeneration
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Finiteness.Ideal

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
  [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]

local notation "J" => extendedMaximalIdeal A B

/-- The powers of the extended maximal ideal and the target maximal ideal are cofinal. -/
theorem adicPowersCofinal (h : Ideal.radical J = maximalIdeal B) :
    (∀ n : ℕ, J ^ n ≤ maximalIdeal B ^ n) ∧
      (∃ e : ℕ, ∀ n : ℕ, maximalIdeal B ^ (e * n) ≤ J ^ n) := by
  refine ⟨Ideal.pow_right_mono (map_maximalIdeal_le (algebraMap A B)), ?_⟩
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h.ge
    (Ideal.fg_of_isNoetherianRing (maximalIdeal B))
  refine ⟨e, fun n ↦ ?_⟩
  rw [pow_mul]
  exact Ideal.pow_right_mono he n

private theorem isHausdorff_extendedMaximalIdeal [IsAdicComplete (maximalIdeal B) B]
    (h : Ideal.radical J = maximalIdeal B) : IsHausdorff J B := by
  refine ⟨fun x hx ↦ IsHausdorff.haus
    (inferInstance : IsHausdorff (maximalIdeal B) B) x (fun n ↦ ?_)⟩
  exact SModEq.mono (Submodule.smul_mono_left ((adicPowersCofinal h).1 n)) (hx n)

private theorem isPrecomplete_finiteProduct {R ι : Type*} [CommRing R] [Fintype ι]
    (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I (ι → R) := by
  classical
  apply (AdicCompletion.of_surjective_iff (I := I) (M := ι → R)).mp
  intro x
  let M : ι → Type _ := fun _ ↦ R
  choose c hc using fun i ↦ AdicCompletion.of_surjective I R (AdicCompletion.pi I M x i)
  refine ⟨c, (AdicCompletion.piEquivOfFintype I M).injective ?_⟩
  simp only [AdicCompletion.piEquivOfFintype_apply]
  funext i
  change AdicCompletion.map I (LinearMap.proj i : (ι → R) →ₗ[R] R)
    (AdicCompletion.of I (ι → R) c) = AdicCompletion.pi I M x i
  rw [AdicCompletion.map_of]
  exact hc i

variable [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
  [IsAdicComplete (maximalIdeal B) B]

-- Keep the Noetherian hypotheses of the complete local ring statement in the public API.
set_option linter.unusedSectionVars false

attribute [local instance] closedFiberAlgebra

/-- Lifts of a finite spanning family of the closed fibre span the target over the source. -/
theorem spanOfLifts {ι : Type*} [Fintype ι] (b : ι → B)
    (h : Ideal.radical J = maximalIdeal B)
    (hspan : Submodule.span (ResidueField A)
      (Set.range fun i ↦ Ideal.Quotient.mk J (b i)) = ⊤) :
    Submodule.span A (Set.range b) = ⊤ := by
  classical
  let I := maximalIdeal A
  let f := Fintype.linearCombination A b
  have : IsPrecomplete I (ι → A) := isPrecomplete_finiteProduct I
  have : IsHausdorff I B := (IsHausdorff.map_algebraMap_iff (S := B)).mp
    (isHausdorff_extendedMaximalIdeal h)
  rw [span_range_eq_top_iff_surjective_fintypeLinearCombination]
  change Function.Surjective f
  apply surjective_of_mkQ_comp_surjective (I := I)
  rw [Ideal.smul_top_eq_map]
  change Function.Surjective (fun c ↦ Ideal.Quotient.mk J (f c))
  intro y
  have hsurj := (span_range_eq_top_iff_surjective_fintypeLinearCombination
    (ResidueField A) _).mp hspan
  obtain ⟨d, hd⟩ := hsurj y
  choose c hc using fun i ↦ residue_surjective (d i)
  refine ⟨c, ?_⟩
  rw [← hd]
  simp only [f, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [← hc i]
  rfl

/-- Finiteness of the closed fibre implies finiteness over the source. -/
theorem finiteOfFiniteClosedFiber (h : Ideal.radical J = maximalIdeal B)
    (hfinite : Module.Finite (ResidueField A) (B ⧸ J)) : Module.Finite A B := by
  classical
  have := hfinite
  obtain ⟨n, d, hd⟩ := Module.Finite.exists_fin (R := ResidueField A) (M := B ⧸ J)
  choose b hb using fun i ↦ Ideal.Quotient.mk_surjective (d i)
  refine Module.Finite.of_fg_top (Submodule.fg_iff_exists_fin_generating_family.mpr
    ⟨n, b, spanOfLifts b h ?_⟩)
  simpa only [hb] using hd

/-- If the class of one spans the closed fibre, the local map is surjective. -/
theorem surjectiveOfOneSpansClosedFiber (h : Ideal.radical J = maximalIdeal B)
    (hspan : Submodule.span (ResidueField A) ({1} : Set (B ⧸ J)) = ⊤) :
    Function.Surjective (algebraMap A B) := by
  have := isHausdorff_extendedMaximalIdeal h
  apply surjective_of_mk_map_comp_surjective (I := maximalIdeal A) (algebraMap A B)
  intro y
  have hy : y ∈ Submodule.span (ResidueField A) ({1} : Set (B ⧸ J)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨r, rfl⟩ := residue_surjective a
  rw [Algebra.smul_def, mul_one] at ha
  exact ⟨r, ha⟩

/-- A surjective residue map lifts to a surjection if the maximal ideal extends exactly. -/
theorem surjectiveOfMaximalIdealAndResidue (hJ : J = maximalIdeal B)
    (hres : Function.Surjective (ResidueField.map (algebraMap A B))) :
    Function.Surjective (algebraMap A B) := by
  have : IsHausdorff J B := hJ ▸ (inferInstance : IsHausdorff (maximalIdeal B) B)
  apply surjective_of_mk_map_comp_surjective (I := maximalIdeal A) (algebraMap A B)
  change Function.Surjective ((Ideal.Quotient.mk J).comp (algebraMap A B))
  rw [hJ]
  exact hres.comp residue_surjective

end CommutativeAlgebraNotes.CoefficientRings
