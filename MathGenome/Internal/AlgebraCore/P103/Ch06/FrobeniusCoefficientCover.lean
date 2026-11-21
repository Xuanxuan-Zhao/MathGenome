import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.FrobeniusCoefficientCover
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

namespace P103.Ch06.FrobeniusCover
universe u v

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

/-- Inverse Frobenius transports a separable annihilator once its coefficient
roots belong to the proposed base field. -/
lemma separable_of_coefficient_roots [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP K p] (e : ℕ)
    (M : IntermediateField K Ω) (f : Polynomial K) (x : Ω)
    (hf : f.Separable) (hx : Polynomial.aeval (x ^ (p ^ e)) f = 0)
    (hc : ∀ n, ∃ b : M, (b : Ω) ^ (p ^ e) = algebraMap K Ω (f.coeff n)) :
    IsSeparable M x := by
  have : CharP Ω p := CharP.of_ringHom_of_ne_zero (algebraMap K Ω) p
    (Fact.out : p.Prime).ne_zero
  let φ := iterateFrobeniusEquiv Ω p e
  let g := (f.map (algebraMap K Ω)).map φ.symm.toRingHom
  have hg : g.Separable := hf.map.map
  have hcoeff (n : ℕ) : g.coeff n ∈ Set.range (algebraMap M Ω) := by
    obtain ⟨b, hb⟩ := hc n
    refine ⟨b, ?_⟩
    simp only [g, Polynomial.coeff_map]
    change (b : Ω) = φ.symm (algebraMap K Ω (f.coeff n))
    apply φ.injective
    simpa only [φ, iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply] using hb
  obtain ⟨gM, hgM⟩ := (Polynomial.mem_lifts g).mp
    ((Polynomial.lifts_iff_coeff_lifts g).mpr hcoeff)
  have hgMsep : gM.Separable := (Polynomial.separable_map (algebraMap M Ω)).mp
    (hgM ▸ hg)
  have hroot : g.eval x = 0 := by
    have hx' : (f.map (algebraMap K Ω)).eval (φ x) = 0 := by
      simpa only [φ, iterateFrobeniusEquiv_def, Polynomial.eval_map,
        Polynomial.aeval_def] using hx
    calc
      g.eval x = φ.symm ((f.map (algebraMap K Ω)).eval (φ x)) := by
        simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          RingEquiv.symm_apply_apply, g] using
          (Polynomial.eval_map_apply (p := f.map (algebraMap K Ω))
            φ.symm.toRingHom (φ x))
      _ = 0 := by rw [hx', map_zero]
  apply hgMsep.of_dvd (minpoly.dvd M x ?_)
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, hgM]
  exact hroot

/-- A finite extension has a common power in its maximal separable subfield. -/
lemma common_separable_power (p : ℕ) [Fact p.Prime] [CharP K p]
    (L : IntermediateField K Ω) [Module.Finite K L] :
    ∃ e : ℕ, ∀ x : L, IsSeparable K (x ^ (p ^ e)) := by
  have : CharP (separableClosure K L) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap K (separableClosure K L)) p
      (Fact.out : p.Prime).ne_zero
  refine ⟨IsPurelyInseparable.exponent (separableClosure K L) L, fun x => ?_⟩
  obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' (separableClosure K L) p x
  exact hy ▸ y.property

/-- Finite coefficient extraction suffices to remove the inseparability of a
finite extension after enlarging the base inside an algebraically closed field. -/
theorem coefficientCover : CoefficientCover.{u,v} := by
  classical
  intro K Ω _ _ _ _ p _ _ L hfin
  have : Module.Finite K L := hfin
  obtain ⟨e, he⟩ := common_separable_power p L
  obtain ⟨T, hT⟩ := (IntermediateField.essFiniteType_iff (K := L)).mp inferInstance
  let f : Ω → Polynomial K := fun x => minpoly K (x ^ (p ^ e))
  let S : Finset K := T.biUnion (fun x => (f x).coeffs)
  refine ⟨e, S, fun M hM => ?_⟩
  have hsep : ∀ x ∈ T, IsSeparable M x := by
    intro x hx
    have hxL : x ∈ L := hT ▸ IntermediateField.subset_adjoin K (↑T : Set Ω) hx
    have hp : (f x).Separable := by
      have h := (he ⟨x, hxL⟩).map L.val Subtype.val_injective
      simpa only [map_pow, IntermediateField.coe_val, IsSeparable, f] using h
    apply separable_of_coefficient_roots p e M (f x) x hp (minpoly.aeval _ _)
    intro n
    by_cases hc : (f x).coeff n = 0
    · refine ⟨0, ?_⟩
      simp [hc, (Fact.out : p.Prime).ne_zero]
    · apply hM
      exact Finset.mem_biUnion.mpr ⟨x, hx,
        Polynomial.coeff_mem_coeffs hc⟩
  let A := IntermediateField.adjoin M (↑T : Set Ω)
  have hAfinite : Module.Finite M A :=
    IntermediateField.finiteDimensional_adjoin (fun x hx => (hsep x hx).isIntegral)
  have hAsep : Algebra.IsSeparable M A :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable M Ω).mpr hsep
  let N := A.restrictScalars K
  have hMN : M ≤ N := by
    intro x hx
    exact A.algebraMap_mem ⟨x, hx⟩
  have hLN : L ≤ N := by
    rw [← hT]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    exact IntermediateField.subset_adjoin M (↑T : Set Ω) hx
  refine ⟨N, hLN, hMN, ?_⟩
  let : Algebra M N := (IntermediateField.inclusion hMN).toAlgebra
  exact ⟨hAfinite, hAsep⟩

end P103.Ch06.FrobeniusCover
