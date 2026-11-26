import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.CompleteIntersectionEuler
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.SerreKoszulEulerFormula
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.RingHom.Basic

namespace CommutativeAlgebraNotes.Intersection.CompleteIntersectionEuler

open CategoryTheory
open AdvCommAlg.Koszul (listIdeal homology coefficientComplex coefficientComplex_vanish)
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue ringDimensionValue)
open IsolatedTorSupport (Tor koszulHomologyTorEquiv isolated_tensor_iff)
open IsolatedIntersectionEuler (cutoffEuler intersectionEuler intersectionEuler_eq_cutoff
  cutoffEuler_eq_of_vanishes_above)

universe u v

theorem torFiniteLength : Specs.torFiniteLength.{u,v} := by
  intro R _ _ _ z N _ hz hJ hN i
  exact (koszulHomologyTorEquiv N z hz i).isFiniteLength
    (SerreKoszulEulerFormula.homologyFiniteLength R N z hJ hN i)

theorem torVanishesAbove : Specs.torVanishesAbove.{u,v} := by
  intro R _ z N hz i hi
  have : Subsingleton (homology N z i) := by
    apply ModuleCat.subsingleton_of_isZero
    exact ((coefficientComplex N z).sc i).isZero_homology_of_isZero_X₂
      (ModuleCat.isZero_iff_subsingleton.mpr (coefficientComplex_vanish N z i hi))
  exact (koszulHomologyTorEquiv N z hz i).symm.injective.subsingleton

theorem eulerFormula : Specs.eulerFormula.{u,v} := by
  intro R _ _ _ z N _ _ hz hJ hN
  unfold IsolatedIntersectionEuler.Specs.cutoffEuler
  rw [← SerreKoszulEulerFormula.serreKoszulEulerFormula R N z hJ hN]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← (koszulHomologyTorEquiv N z hz i).length_eq]
  rfl

theorem eulerSigns : Specs.eulerSigns.{u,v} := by
  intro R _ _ _ z N _ _ hz hJ hN
  dsimp only
  let χ := cutoffEuler (ModuleCat.of R (R ⧸ listIdeal z)) N z.length
  have hformula := eulerFormula z N hz hJ hN
  have hle := SerreKoszulEulerFormula.dimensionBound R N z hJ hN inferInstance
  have hzero (hdim : moduleDimensionValue R N < (z.length : WithBot ℕ∞)) : χ = 0 := by
    have h : (χ : ℚ) = 0 :=
      hformula.trans (SerreKoszulEulerFormula.zeroOfDimensionLT R N z hJ hN hdim)
    exact_mod_cast h
  have hpos (hdim : moduleDimensionValue R N = (z.length : WithBot ℕ∞)) : 0 < χ := by
    obtain ⟨n, hn, he⟩ :=
      SerreKoszulEulerFormula.positiveInteger R N z hJ hN inferInstance hdim
    have h : (χ : ℚ) = (n : ℚ) := hformula.trans he
    have hχ : χ = n := by exact_mod_cast h
    exact hχ.symm ▸ hn
  refine ⟨hle, ⟨fun h => lt_of_le_of_ne hle ?_, hzero⟩, ⟨fun h => ?_, hpos⟩⟩
  · exact fun he => (hpos he).ne' h
  · exact (lt_or_eq_of_le hle).resolve_left (fun hl => h.ne' (hzero hl))

theorem quotientDimension : Specs.quotientDimension.{u} := by
  intro R _ _ _ z d hz hd
  let J := listIdeal z
  have hJ : J ≠ ⊤ := by
    simpa [J, listIdeal, ne_comm] using hz.top_ne_smul
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  let : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  obtain ⟨q, _, hq, _, _⟩ := P103.Ch06.SystemsParameters.local_ring_parameters (R ⧸ J)
  have hdrop := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular z hz
  change ringKrullDim (R ⧸ J) + (z.length : WithBot ℕ∞) = ringKrullDim R at hdrop
  rw [hq, hd, ← Nat.cast_add] at hdrop
  have hsum : q + z.length = d := by exact_mod_cast hdrop
  have he : q = d - z.length := by omega
  exact ⟨by omega, he ▸ hq⟩

theorem finiteLengthQuotientIffIsolated : Specs.finiteLengthQuotientIffIsolated.{u,v} := by
  intro R _ _ _ z N _
  let M := ModuleCat.of R (R ⧸ listIdeal z)
  let e := TensorProduct.quotTensorEquivQuotSMul N (listIdeal z)
  exact ⟨fun h => (isolated_tensor_iff M N).mp (e.symm.isFiniteLength h),
    fun h => e.isFiniteLength ((isolated_tensor_iff M N).mpr h)⟩

theorem regularLocalIntersection : Specs.regularLocalIntersection.{u,v} := by
  intro R _ _ z N _ _ d hz hJ hN hd
  dsimp only
  let M := ModuleCat.of R (R ⧸ listIdeal z)
  have ⟨hrd, hquot⟩ := quotientDimension z d hz hd
  have hdimM : moduleDimensionValue R M = ((d - z.length : ℕ) : WithBot ℕ∞) := by
    unfold moduleDimensionValue ringDimensionValue
    change ringKrullDim (R ⧸ Module.annihilator R (R ⧸ listIdeal z)) = _
    rwa [Ideal.annihilator_quotient]
  have hχ : intersectionEuler M N = cutoffEuler M N z.length :=
    (intersectionEuler_eq_cutoff M N d hd).trans
      (cutoffEuler_eq_of_vanishes_above M N z.length d hrd (torVanishesAbove z N hz))
  obtain ⟨hle, hzero, hpos⟩ := eulerSigns z N hz hJ hN
  obtain ⟨n, hn, _, _⟩ := P103.Ch06.SystemsParameters.parameter_count R N
  have hnr : n ≤ z.length := by
    rw [hn] at hle
    exact_mod_cast hle
  change cutoffEuler M N z.length = 0 ↔ _ at hzero
  change 0 < cutoffEuler M N z.length ↔ _ at hpos
  refine ⟨hχ, ?_, ?_, ?_⟩
  · rw [hdimM, hn, ← Nat.cast_add]
    exact_mod_cast (show d - z.length + n ≤ d by omega)
  · change intersectionEuler M N = 0 ↔ _
    rw [hχ, hzero, hdimM, hn, ← Nat.cast_add]
    exact_mod_cast (show n < z.length ↔ d - z.length + n < d by omega)
  · change 0 < intersectionEuler M N ↔ _
    rw [hχ, hpos, hdimM, hn, ← Nat.cast_add]
    exact_mod_cast (show n = z.length ↔ d - z.length + n = d by omega)

end CommutativeAlgebraNotes.Intersection.CompleteIntersectionEuler
