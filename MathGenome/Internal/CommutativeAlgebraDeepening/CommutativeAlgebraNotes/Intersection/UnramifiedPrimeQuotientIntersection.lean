import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.UnramifiedPrimeQuotientIntersection
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.DVRDiagonalReduction
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.EqualCharacteristicIntersection
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.OneSpecialFibreTor
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.RegularElementEulerCancellation
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.RedundantGenerators
import Mathlib.Data.ENat.Monoid
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace CommutativeAlgebraNotes.Intersection.UnramifiedPrimeQuotientIntersection

open CategoryTheory IsLocalRing
open scoped TensorProduct PowerSeriesDiagonal nonZeroDivisors
open ExteriorTensorProduct (X S OnY)
open PowerSeriesDiagonal (difference diagonalIdeal diagonalReduction
  identify_surjective restrictDiagonal)
open IsolatedIntersectionEuler
open IsolatedTorSupport (Tor tensor_nontrivial)
open OneSpecialFibreTor.Specs (SpecialFibre killedModule reduceModule)
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)
open AdvCommAlg.Koszul (homology listIdeal)

universe u

private theorem shift_bound_and_sign (s : WithBot ℕ∞) (a : ℕ) (χ : ℤ)
    (h : s ≤ a ∧ (s < a → χ = 0) ∧ (s = a → 0 < χ)) :
    s + 1 ≤ ((a + 1 : ℕ) : WithBot ℕ∞) ∧
      (s + 1 < ((a + 1 : ℕ) : WithBot ℕ∞) → χ = 0) ∧
      (s + 1 = ((a + 1 : ℕ) : WithBot ℕ∞) → 0 < χ) := by
  have he : ((a + 1 : ℕ) : WithBot ℕ∞) = a + 1 := by simp
  rw [he]
  have hle := @ENat.WithBot.add_le_add_one_right_iff
  exact ⟨hle.mpr h.1, fun hl => h.2.1 (lt_of_not_ge (fun hn => hl.not_ge (hle.mpr hn))),
    fun heq => h.2.2 (le_antisymm (hle.mp heq.le) (hle.mp heq.ge))⟩

/-- Restriction to the joint power-series ring preserves lengths of diagonal modules. -/
private theorem length_restrictDiagonal (V : Type u) [CommRing V] (a : ℕ)
    (L : ModuleCat.{u} (X V a)) :
    Module.length (S V a a) ((restrictDiagonal V a).obj L) = Module.length (X V a) L := by
  let L' := (restrictDiagonal V a).obj L
  let : Module (X V a) L' := L.isModule
  let : IsScalarTower (S V a a) (X V a) L' := IsScalarTower.of_compHom _ _ _
  exact Module.length_eq_of_surjective (identify_surjective V a)

private theorem finite_length_quotient_congr {A E : Type u} [CommRing A]
    [AddCommGroup E] [Module A E] {I J : Ideal A} (h : I = J)
    (hlen : IsFiniteLength A (E ⧸ (J • ⊤ : Submodule A E))) :
    IsFiniteLength A (E ⧸ (I • ⊤ : Submodule A E)) := h.symm ▸ hlen

set_option backward.isDefEq.respectTransparency false in
private theorem both_regular
    (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] (π : V) (hπ : Irreducible π) (a : ℕ)
    [IsRegularLocalRing (X V a)]
    (hd : ringKrullDim (X V a) = ((a + 1 : ℕ) : WithBot ℕ∞))
    (M N : ModuleCat.{u} (X V a))
    [Module.Finite (X V a) M] [Module.Finite (X V a) N] [Nontrivial M] [Nontrivial N]
    (hM : IsSMulRegular M (MvPowerSeries.C π : X V a))
    (hN : IsSMulRegular N (MvPowerSeries.C π : X V a))
    (hMN : IsFiniteLength (X V a) (M ⊗[X V a] N)) :
    let s := moduleDimensionValue (X V a) M + moduleDimensionValue (X V a) N
    let d : WithBot ℕ∞ := ((a + 1 : ℕ) : WithBot ℕ∞)
    s ≤ d ∧ (s < d → intersectionEuler M N = 0) ∧ (s = d → 0 < intersectionEuler M N) := by
  let T := ExteriorTensorProduct.Spec.diagonalValue V a M N
  let z := List.ofFn (difference V a)
  have hz : z.length = a := List.length_ofFn
  have hJ : listIdeal z = diagonalIdeal V a := by
    unfold listIdeal diagonalIdeal
    congr 1
    ext s
    simp [z, List.mem_ofFn]
  have hmax : listIdeal z ≤ maximalIdeal (S V a a) := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (maximalIdeal (S V a a)).sub_mem
      ((mem_maximalIdeal _).mpr (by simp [MvPowerSeries.isUnit_iff_constantCoeff]))
      ((mem_maximalIdeal _).mpr (by simp [MvPowerSeries.isUnit_iff_constantCoeff]))
  let : Nontrivial (OnY N) := inferInstanceAs (Nontrivial N)
  let : Module.Finite (S V a a) T := ExteriorTensorProduct.finite
  obtain ⟨e, _⟩ := DVRDiagonalReduction.tensorQuotient V a M N
  have hlen' : IsFiniteLength (S V a a) (diagonalReduction V a T) := by
    apply Module.length_ne_top_iff.mp
    rw [e.length_eq, length_restrictDiagonal V a]
    exact Module.length_ne_top_iff.mpr hMN
  have hlen := finite_length_quotient_congr hJ hlen'
  have : Nontrivial ((restrictDiagonal V a).obj
      (ModuleCat.of (X V a) (M ⊗[X V a] N))) := tensor_nontrivial M N
  have : Nontrivial (diagonalReduction V a T) := e.surjective.nontrivial
  have hT : Nontrivial T :=
    (Submodule.mkQ_surjective (diagonalIdeal V a • (⊤ : Submodule (S V a a) T))).nontrivial
  have hdim := DVRDiagonalReduction.dimension V π hπ a M N hM hN
  change moduleDimensionValue (S V a a) T + 1 = _ at hdim
  have htor := DVRDiagonalReduction.koszulHomologyTor V π hπ a M N hM hN
  have hlength (i : ℕ) :
      Module.length (S V a a) (homology T z i) = Module.length (X V a) (Tor M N i) :=
    (htor i).some.length_eq.trans (length_restrictDiagonal V a _)
  have hcut : intersectionEuler M N = cutoffEuler M N a := by
    rw [intersectionEuler_eq_cutoff M N (a + 1) hd]
    apply cutoffEuler_eq_of_vanishes_above M N a (a + 1) (Nat.le_succ a)
    intro i hi
    have := AdvCommAlg.Koszul.homology_vanish T z i (by simpa only [hz] using hi)
    exact (htor i).some.surjective.subsingleton
  have hEuler := SerreKoszulEulerFormula.serreKoszulEulerFormula (S V a a) T z hmax hlen
  rw [hz] at hEuler
  have hχ : (intersectionEuler M N : ℚ) =
      _root_.Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity.degreeMultiplicity
        (listIdeal z) T a := by
    rw [hcut, ← hEuler]
    congr 1
    unfold cutoffEuler IsolatedIntersectionEuler.Specs.cutoffEuler
    exact Finset.sum_congr rfl (fun i _ => by rw [← hlength i]; rfl)
  have hb := SerreKoszulEulerFormula.dimensionBound (S V a a) T z hmax hlen hT
  rw [hz] at hb
  have hzero (hlt : moduleDimensionValue (S V a a) T < (a : WithBot ℕ∞)) :
      intersectionEuler M N = 0 := by
    have hh := SerreKoszulEulerFormula.zeroOfDimensionLT (S V a a) T z hmax hlen (hz.symm ▸ hlt)
    rw [hz] at hh
    exact_mod_cast hχ.trans hh
  have hpos (heq : moduleDimensionValue (S V a a) T = (a : WithBot ℕ∞)) :
      0 < intersectionEuler M N := by
    obtain ⟨n, hn, hh⟩ :=
      SerreKoszulEulerFormula.positiveInteger (S V a a) T z hmax hlen hT (hz.symm ▸ heq)
    rw [hz] at hh
    have hχn : intersectionEuler M N = n := by exact_mod_cast hχ.trans hh
    rwa [hχn]
  simpa only [← hdim] using shift_bound_and_sign _ a _ ⟨hb, hzero, hpos⟩

private theorem cast_not_mem_maximalIdeal_sq (V : Type u) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (p a : ℕ) (hp : Irreducible (p : V)) :
    (p : X V a) ∉ maximalIdeal (X V a) ^ 2 := by
  intro h
  have hcoeff := (CompleteRegularPowerSeries.maximalIdealPower V a 2 _).mp h 0
  have hpow : (p : V) ∈ maximalIdeal V ^ 2 := by
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hcoeff
  rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two] at hpow
  exact hp.not_isUnit (hp.isUnit_of_mul_self_dvd hpow)

private def specialFibreEquiv (V : Type u) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (p a : ℕ) (hp : Irreducible (p : V)) :
    SpecialFibre (p : X V a) ≃+* X (ResidueField V) a := by
  obtain ⟨hsurj, hker⟩ := DVRExteriorTensorResolution.reductionRing V (p : V) hp (Fin a)
  let f := DVRExteriorTensorResolution.reduce V (Fin a)
  have hk : Ideal.span {(p : X V a)} = RingHom.ker f := by simpa [f] using hker.symm
  exact (Ideal.quotEquivOfEq hk).trans (f.quotientKerEquivOfSurjective hsurj)

private theorem equal_characteristic_signs {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (a : ℕ) (hd : ringKrullDim A = (a : WithBot ℕ∞))
    (hc : ringChar (ResidueField A) = ringChar A)
    (M N : ModuleCat.{u} A) [Module.Finite A M] [Module.Finite A N]
    [Nontrivial M] [Nontrivial N] (hMN : IsFiniteLength A (M ⊗[A] N)) :
    let s := moduleDimensionValue A M + moduleDimensionValue A N
    s ≤ (a : WithBot ℕ∞) ∧
      (s < (a : WithBot ℕ∞) → intersectionEuler M N = 0) ∧
      (s = (a : WithBot ℕ∞) → 0 < intersectionEuler M N) := by
  obtain ⟨_, _, _, _, _, _, _, h⟩ :=
    EqualCharacteristicIntersection.equalCharacteristic A a hd hc M N hMN
  exact h

private theorem dimension_eq_support {R : Type u} [CommRing R] (L : ModuleCat.{u} R)
    [Module.Finite R L] : moduleDimensionValue R L = Module.supportDim R L :=
  (Module.supportDim_eq_ringKrullDim_quotient_annihilator R L).symm

private instance killedModule_finite {R : Type u} [CommRing R] {x : R} {M : ModuleCat.{u} R}
    [Module.Finite R M] (hM : Module.IsTorsionBy R M x) :
    Module.Finite (SpecialFibre x) (killedModule hM) := by
  let : Module (SpecialFibre x) M := hM.module
  let : IsScalarTower R (SpecialFibre x) M :=
    Module.IsTorsionBySet.isScalarTower ((Module.isTorsionBySet_span_singleton_iff x).mpr hM)
  exact Module.Finite.of_restrictScalars_finite R (SpecialFibre x) M

open private length_restriction exists_bounded_free_resolution from
  MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.OneSpecialFibreTor

set_option backward.isDefEq.respectTransparency false in
private theorem one_killed {R : Type u} [CommRing R] [IsRegularLocalRing R] [CharZero R]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hp : (p : R) ∉ maximalIdeal R ^ 2)
    [IsRegularLocalRing (SpecialFibre (p : R))]
    (a : ℕ) (hd : ringKrullDim R = ((a + 1 : ℕ) : WithBot ℕ∞))
    (hd' : ringKrullDim (SpecialFibre (p : R)) = (a : WithBot ℕ∞))
    (hc : ringChar (ResidueField (SpecialFibre (p : R))) = ringChar (SpecialFibre (p : R)))
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hM : Module.IsTorsionBy R M (p : R)) (hN : IsSMulRegular N (p : R))
    (hMN : IsFiniteLength R (M ⊗[R] N)) :
    let s := moduleDimensionValue R M + moduleDimensionValue R N
    let d : WithBot ℕ∞ := ((a + 1 : ℕ) : WithBot ℕ∞)
    s ≤ d ∧ (s < d → intersectionEuler M N = 0) ∧ (s = d → 0 < intersectionEuler M N) := by
  let x : R := p
  let A := SpecialFibre x
  let M' := killedModule hM
  let N' := reduceModule x N
  let : Module.Finite A N' := AdvCommAlg.regularQuotient_finite x N
  let : Nontrivial M' := ‹Nontrivial M›
  obtain ⟨hN', hMd, _, hNd⟩ := OneSpecialFibreTor.dimension_comparison p hp M N hM hN
  let : Nontrivial N' := hN'
  change Module.supportDim A M' = Module.supportDim R M at hMd
  change Module.supportDim A N' + 1 = Module.supportDim R N at hNd
  have hdim : (moduleDimensionValue A M' + moduleDimensionValue A N') + 1 =
      moduleDimensionValue R M + moduleDimensionValue R N := by
    simp only [dimension_eq_support, add_assoc, hMd, hNd]
  obtain ⟨e⟩ := OneSpecialFibreTor.tensor_comparison p hp M N hM hN
  let e' : (M ⊗[R] N) ≃ₗ[R] RestrictScalars R A (M' ⊗[A] N') := e
  have hMN' : IsFiniteLength A (M' ⊗[A] N') := by
    apply Module.length_ne_top_iff.mp
    have hh := e'.length_eq.trans (length_restriction x (M' ⊗[A] N'))
    exact hh ▸ Module.length_ne_top_iff.mpr hMN
  have heuler : intersectionEuler M N = intersectionEuler M' N' := by
    rw [intersectionEuler_eq_cutoff M N (a + 1) hd, intersectionEuler_eq_cutoff M' N' a hd',
      ← cutoffEuler_eq_of_vanishes_above M' N' a (a + 1) (Nat.le_succ a)
        (tor_vanishes_above M' N' a hd')]
    unfold cutoffEuler IsolatedIntersectionEuler.Specs.cutoffEuler
    apply Finset.sum_congr rfl
    intro i _
    rw [(OneSpecialFibreTor.length_comparison p hp M N hM hN hMN i).2.2]
  have hs := equal_characteristic_signs a hd' hc M' N' hMN'
  rw [← heuler] at hs
  dsimp only
  rw [← hdim]
  exact shift_bound_and_sign _ a _ hs

open RegularElementEulerCancellation.Specs (IsBoundedFiniteFree restrict)
open private tensorRestrictionEquiv from
  MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.RegularElementEulerCancellation
open private torCongr from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.EqualCharacteristicIntersection
open private dimension_restrict from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.DVRDiagonalReduction

private def restrictKilledEquiv {R : Type u} [CommRing R] {x : R} {M : ModuleCat.{u} R}
    (hM : Module.IsTorsionBy R M x) : M ≃ₗ[R] restrict x (killedModule hM) where
  toAddEquiv := AddEquiv.refl M
  map_smul' _ _ := rfl

private theorem killedModule_dimension {R : Type u} [CommRing R] {x : R} {M : ModuleCat.{u} R}
    (hM : Module.IsTorsionBy R M x) :
    moduleDimensionValue (SpecialFibre x) (killedModule hM) = moduleDimensionValue R M := by
  let : Module (SpecialFibre x) M := hM.module
  let : IsScalarTower R (SpecialFibre x) M :=
    Module.IsTorsionBySet.isScalarTower ((Module.isTorsionBySet_span_singleton_iff x).mpr hM)
  exact (dimension_restrict (B := SpecialFibre x) M Ideal.Quotient.mk_surjective).symm

private theorem both_killed {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hx' : x ∈ R⁰)
    [IsRegularLocalRing (SpecialFibre x)]
    (a : ℕ) (hd' : ringKrullDim (SpecialFibre x) = (a : WithBot ℕ∞))
    (hc : ringChar (ResidueField (SpecialFibre x)) = ringChar (SpecialFibre x))
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hM : Module.IsTorsionBy R M x) (hN : Module.IsTorsionBy R N x)
    (hMN : IsFiniteLength R (M ⊗[R] N)) :
    let s := moduleDimensionValue R M + moduleDimensionValue R N
    let d : WithBot ℕ∞ := ((a + 1 : ℕ) : WithBot ℕ∞)
    s ≤ d ∧ (s < d → intersectionEuler M N = 0) ∧ (s = d → 0 < intersectionEuler M N) := by
  let A := SpecialFibre x
  let M' := killedModule hM
  let N' := killedModule hN
  let : Nontrivial M' := ‹Nontrivial M›
  let : Nontrivial N' := ‹Nontrivial N›
  let eM := restrictKilledEquiv hM
  let eN := restrictKilledEquiv hN
  let e := (TensorProduct.congr eM eN).trans (tensorRestrictionEquiv x M' N').symm
  let : Module.Finite R (restrict x N') := Module.Finite.equiv eN
  have hMN' : IsFiniteLength A (M' ⊗[A] N') := by
    apply Module.length_ne_top_iff.mp
    have hh := e.length_eq.trans (length_restriction x (M' ⊗[A] N'))
    exact hh ▸ Module.length_ne_top_iff.mpr hMN
  have hs := (equal_characteristic_signs a hd' hc M' N' hMN').1
  rw [killedModule_dimension hM, killedModule_dimension hN] at hs
  have hlt : moduleDimensionValue R M + moduleDimensionValue R N <
      ((a + 1 : ℕ) : WithBot ℕ∞) := hs.trans_lt (by exact_mod_cast Nat.lt_succ_self a)
  refine ⟨hlt.le, fun _ => ?_, fun h => (hlt.ne h).elim⟩
  obtain ⟨P, b, hP, hb⟩ := exists_bounded_free_resolution M'
  obtain ⟨Q, c, hQ, hc'⟩ := exists_bounded_free_resolution (restrict x N')
  have hP' : IsBoundedFiniteFree P b := ⟨fun i => (hP i).2, fun i => (hP i).1, hb⟩
  have hQ' : IsBoundedFiniteFree Q c := ⟨fun i => (hQ i).2, fun i => (hQ i).1, hc'⟩
  have hz := RegularElementEulerCancellation.intersection_euler_zero x hx hx' M' N'
    hMN' P Q b c hP' hQ'
  rw [← hz]
  unfold intersectionEuler IsolatedIntersectionEuler.Specs.intersectionEuler
    IsolatedIntersectionEuler.Specs.cutoffEuler
  exact Finset.sum_congr rfl (fun i _ => by rw [(torCongr eM eN i).length_eq])

private theorem quotient_killed_or_regular {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] (x : R) :
    Module.IsTorsionBy R (R ⧸ P) x ∨ IsSMulRegular (R ⧸ P) x := by
  by_cases hx : x ∈ P
  · left
    intro m
    change (Ideal.Quotient.mk P x) * m = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_mul]
  · right
    intro m n h
    change (Ideal.Quotient.mk P x) * m = (Ideal.Quotient.mk P x) * n at h
    exact mul_left_cancel₀ (fun hz => hx (Ideal.Quotient.eq_zero_iff_mem.mp hz)) h

/-- Serre's dimension bound and the sign of the Euler characteristic for prime
quotients of a complete unramified mixed-characteristic power-series ring. -/
theorem primeQuotientIntersection : Specs.primeQuotientIntersectionType.{u} := by
  intro V _ _ _ _ _ p _ _ hp a
  let R := X V a
  obtain ⟨_, hreg, _, _, hd, _, _, ⟨eres, _⟩⟩ :=
    CompleteRegularPowerSeries.overCompleteDVR V (p : V) hp a
  let : IsRegularLocalRing R := hreg
  have hp' := cast_not_mem_maximalIdeal_sq V p a hp
  refine ⟨hreg, hd, hp', ?_⟩
  intro P Q _ _ M N hMN
  let : CharZero R := charZero_of_injective_ringHom
    (f := MvPowerSeries.C) MvPowerSeries.C_injective
  let : CharP (ResidueField R) p := eres.toRingHom.charP eres.injective p
  have hpm : (p : R) ∈ maximalIdeal R := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change residue R (p : R) = 0
    rw [map_natCast, CharP.cast_eq_zero]
  have hpn : (p : R) ∈ R⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  let A := SpecialFibre (p : R)
  let e := specialFibreEquiv V p a hp
  obtain ⟨hdom, hreg', _, _, hd', _⟩ := CompleteRegularPowerSeries.overField (ResidueField V) a
  let : IsRegularLocalRing (X (ResidueField V) a) := hreg'
  let : IsRegularLocalRing A := IsRegularLocalRing.of_ringEquiv e.symm
  let : IsDomain (X (ResidueField V) a) := hdom
  let : IsDomain A := e.toMulEquiv.isDomain _
  have hA : ringKrullDim A = (a : WithBot ℕ∞) := e.ringKrullDim.trans hd'
  let : CharP (X (ResidueField V) a) p :=
    charP_of_injective_ringHom (f := MvPowerSeries.C) MvPowerSeries.C_injective p
  let : CharP A p := e.toRingHom.charP e.injective p
  let : CharP (ResidueField A) p :=
    CharP.of_ringHom_of_ne_zero (residue A) p (Fact.out : p.Prime).ne_zero
  have hc : ringChar (ResidueField A) = ringChar A := (ringChar.eq _ p).trans (ringChar.eq _ p).symm
  let : Module.Finite R M := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ R P).toLinearMap Ideal.Quotient.mk_surjective
  let : Module.Finite R N := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ R Q).toLinearMap Ideal.Quotient.mk_surjective
  let : Nontrivial M := inferInstanceAs (Nontrivial (R ⧸ P))
  let : Nontrivial N := inferInstanceAs (Nontrivial (R ⧸ Q))
  rcases quotient_killed_or_regular P (p : R) with hM | hM <;>
    rcases quotient_killed_or_regular Q (p : R) with hN | hN
  · exact both_killed (p : R) hpm hpn a hA hc M N hM hN hMN
  · exact one_killed p hp' a hd hA hc M N hM hN hMN
  · have hNM := Module.length_ne_top_iff.mp
      ((TensorProduct.comm R M N).length_eq ▸ Module.length_ne_top_iff.mpr hMN)
    have h := one_killed p hp' a hd hA hc N M hN hM hNM
    dsimp only at h
    rwa [add_comm, intersectionEuler_symm N M hNM] at h
  · apply both_regular V (p : V) hp a hd M N _ _ hMN
    · simpa using hM
    · simpa using hN

end CommutativeAlgebraNotes.Intersection.UnramifiedPrimeQuotientIntersection
