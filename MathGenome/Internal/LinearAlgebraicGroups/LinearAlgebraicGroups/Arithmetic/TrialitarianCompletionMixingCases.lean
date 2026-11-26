import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianCompletionMixingCases
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
set_option autoImplicit false

universe u

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianCompletionMixingCases

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.LocalProjectedClosure (LocalNormalClosure FiniteCovolumeSubgroup)
open Specs.Arithmetic.LocalQuotientMixing
  (IsIsotropicQuadraticSpin IsIsotropicQuaternionicSpin)
open Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel IsOrthogonal)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.Arithmetic.TrialitarianCompletionMixingCases (Statement)
open Specs.CharacterDescent (Cocharacter)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.Specs.RM03.CSA (isCentralSimple)

open private absoluteAlmostSimple absoluteAlmostSimpleForRadicals fixedVectorVertex
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
open private recoverOrthogonalForm scalarSpinRepresentation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity

private theorem isotropicScalarSpin
    {F K I : Type u} [Field F] [Field K] [Algebra F K] [IsGalois F K]
    [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {J : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (M : SpinModel J D) (hsimple : AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple J)
    (hI : 4 ≤ Fintype.card I) (h₂ : (2 : F) ≠ 0)
    (horth : IsOrthogonal (toDivisionInvolution D.involution))
    {r : ℕ} (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin r) (Fin r) F)
    (c : Cocharacter J.val) (hc : IsNoncentral c) : IsIsotropicQuadraticSpin J := by
  classical
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let : LinearOrder (I ⊕ I) :=
    LinearOrder.lift' (Fintype.equivFin (I ⊕ I)) (Fintype.equivFin (I ⊕ I)).injective
  obtain ⟨E, H, q, b, hq, hH, hE⟩ :=
    recoverOrthogonalForm NontrialitarianSpinModels.fieldOrthogonalModel D h₂ horth e
  obtain ⟨spin, hspin⟩ := scalarSpinRepresentation b
    NontrialitarianSpinModels.splitProjectiveSpinAction M hsimple h₂ E H hH hE hq
  have hiso := OddSpinInnerDescent.spinCocharacterIsotropy q b J spin hq hspin c hc
  have hdim : 5 ≤ Module.finrank F (Fin r → F) := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_sum]
    omega
  exact ⟨Fin r → F, inferInstance, inferInstance, inferInstance, q, spin, hdim, hq, hiso,
    hspin⟩

private theorem isotropicSpinInCharacteristicTwo
    {F K I : Type u} [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {J : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (M : SpinModel J D) (hI : 4 ≤ Fintype.card I)
    (hsimple : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple J) :
    IsIsotropicQuadraticSpin J ∨ IsIsotropicQuaternionicSpin J := by
  obtain ⟨r, B, _, _, hB, hr, ⟨e⟩⟩ :=
    RM03.CSA.MatrixDivision.exists_presentation F ρ.fixedSubalgebra D.centralSimple
  have hB' : isCentralSimple F B := ⟨inferInstance, hB.1, hB.2⟩
  obtain ⟨_, hdiv⟩ := CharacteristicTwoQuadraticPairs.divisionDegreeOverSquares
    (CharacteristicTwoQuadraticPairs.localSquareDegree F)
    D.centralSimple hB' r hr e (toDivisionInvolution D.involution).anti
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hd | hd
  · obtain ⟨iso⟩ := SymplecticInvolutionModels.degreeOneDivision hB' hd
    let e' := e.trans iso.mapMatrix
    obtain ⟨P⟩ := SplitQuadraticPairSpinComparison.recoveredForm_nonempty (D := D) e'
    have h₈ : 8 ≤ r := by
      have hrank := P.rank
      omega
    obtain ⟨spin, h, _, hspin, _, _, _⟩ :=
      SplitQuadraticPairSpinComparison.localSplitSpinGeneration M hsimple r h₈ e' P
    have he : h.e ≠ 0 := by
      intro he
      simpa [he] using h.polar_ef
    have hdim : 5 ≤ Module.finrank F (Fin r → F) := by simpa using (show 5 ≤ r by omega)
    exact Or.inl ⟨Fin r → F, inferInstance, inferInstance, inferInstance, P.form, spin, hdim,
      Or.inl (LinearMap.BilinForm.Nondegenerate.ker_eq_bot P.regular), ⟨h.e, he, h.q_e⟩,
      hspin.1⟩
  · obtain ⟨P⟩ := CharacteristicTwoQuadraticPairs.quaternionPairRecovery D hB' hd r e
    have h₄ : 4 ≤ r := P.rank.symm ▸ hI
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, Q, _⟩ :=
      QuaternionHyperbolicRadicals.arithmeticPresentation M hB' hd r h₄ e
    exact Or.inr ⟨K, I, B, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, ρ, D, hB', r - 2,
      hI, hd, fun h => (h (CharP.cast_eq_zero F 2)).elim, ⟨M⟩, ⟨Q⟩⟩

/-- The original completion satisfies a local mixing case for either
action on its marked diagram. -/
theorem mixingCases_conditional
    (_normal : LocalNormalClosure.{u}) (_covolume : FiniteCovolumeSubgroup.{u}) :
    Statement.{u} := by
  classical
  intro F _ _ _ _ J hss hsc diagram
  by_cases ht : diagram.IsTransitive
  · have htrial : Specs.Arithmetic.TrialitarianLocalForms.IsTrialitarian J := ⟨diagram, ht⟩
    have hqs := TrialitarianLocalForms.finiteQuasiSplit F J hss hsc htrial
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hsc, Or.inr (Or.inl ⟨htrial, hqs⟩)⟩)))
  · have hsimple := absoluteAlmostSimple diagram hss hsc
    obtain ⟨K, _, _, _, _, ρ, D, _, horth, ⟨M⟩⟩ :=
      NontrialitarianSpinModels.nontrialitarianSpinModel F J 4 le_rfl hsimple hsc
        (fixedVectorVertex diagram ht)
    have hI : 4 ≤ Fintype.card (ULift.{u} (Fin 4)) := by simp
    have hspin : IsIsotropicQuadraticSpin J ∨ IsIsotropicQuaternionicSpin J := by
      by_cases h₂ : (2 : F) = 0
      · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h₂
        exact isotropicSpinInCharacteristicTwo M hI (absoluteAlmostSimpleForRadicals hsimple)
      · obtain ⟨c, hc⟩ := TrialitarianLocalForms.finiteIsotropy F J ⟨hss, hsc, ⟨diagram⟩⟩
        obtain ⟨B, _, _, r, hB, _, ⟨e⟩, hdivision⟩ :=
          NontrialitarianSpinModels.nonarchimedeanDivision h₂ D.centralSimple
            (toDivisionInvolution D.involution)
        rcases hdivision with hscalar | hdegree
        · obtain ⟨b⟩ := hscalar
          exact Or.inl (isotropicScalarSpin M hsimple hI h₂ (horth h₂) (e.trans b.mapMatrix) c hc)
        · obtain ⟨d, hd, hQ⟩ :=
            QuaternionSpinOddCharacteristic.quaternionPresentationAtIsotropy M hI h₂
              hB hdegree ⟨r, ⟨e⟩⟩ ⟨c, hc⟩
          exact Or.inr ⟨K, ULift.{u} (Fin 4), B, inferInstance, inferInstance, inferInstance,
            inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
            ρ, D, hB, d, hI, hdegree, fun _ => hd, ⟨M⟩, hQ⟩
    rcases hspin with hq | hB
    · exact Or.inr (Or.inr (Or.inl hq))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hB)))

end LinearAlgebraicGroups.Arithmetic.TrialitarianCompletionMixingCases

universe v8_closure_6a1612a8dd89b22f_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«TrialitarianCompletionMixingCases».«mixingCases» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«TrialitarianCompletionMixingCases».«Statement».{v8_closure_6a1612a8dd89b22f_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«TrialitarianCompletionMixingCases».«mixingCases_conditional».{v8_closure_6a1612a8dd89b22f_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localNormalClosure».{v8_closure_6a1612a8dd89b22f_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localProjectedClosure».{v8_closure_6a1612a8dd89b22f_u0})
