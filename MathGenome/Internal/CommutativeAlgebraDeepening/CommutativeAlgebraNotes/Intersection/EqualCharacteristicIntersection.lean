import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.EqualCharacteristicIntersection
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.FieldDiagonalTor
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IntersectionEulerCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorDimensionAndMultiplicity
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.SerreKoszulEulerFormula
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.EqualCharacteristicRegularPresentation
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct Pointwise
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)

namespace CommutativeAlgebraNotes.Intersection.EqualCharacteristicIntersection

open ExteriorTensorProduct (S Y OnY xToY includeX)
open PowerSeriesDiagonal
open FieldDiagonalTor (diagonalList)
open IntersectionEulerCompletion.Specs (CompletedRing CompletedModule completedModuleCat)
open IsolatedTorSupport (Tor)
open IsolatedIntersectionEuler (cutoffEuler intersectionEuler)
open _root_.Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity (degreeMultiplicity)
open scoped ExteriorTensorProduct PowerSeriesDiagonal

universe u v w v' w'

private theorem dimension_eq_support {A : Type u} [CommRing A] (E : Type v)
    [AddCommGroup E] [Module A E] [Module.Finite A E] :
    moduleDimensionValue A E = Module.supportDim A E :=
  (Module.supportDim_eq_ringKrullDim_quotient_annihilator A E).symm

private theorem diagonal_le_maximalIdeal (k : Type u) [Field k] (d : ℕ) :
    diagonalIdeal k d ≤ maximalIdeal (S k d d) := by
  change Ideal.span (Set.range (difference k d)) ≤ _
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  apply Ideal.sub_mem
  · exact (IsLocalRing.mem_maximalIdeal _).mpr <| by
      simp [leftVar, MvPowerSeries.isUnit_iff_constantCoeff]
  · exact (IsLocalRing.mem_maximalIdeal _).mpr <| by
      simp [rightVar, MvPowerSeries.isUnit_iff_constantCoeff]

private theorem right_dimension (k : Type u) [Field k] (d : ℕ)
    (N : ModuleCat.{w} (R k d)) :
    moduleDimensionValue (Y k d) (OnY N) = moduleDimensionValue (R k d) N := by
  let e := (xToY k d).toRingEquiv
  have h : Module.annihilator (Y k d) (OnY N) =
      (Module.annihilator (R k d) N).map e.toRingHom := by
    change _ = Ideal.map e _
    rw [← Ideal.comap_symm e]
    rfl
  exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e h)).symm

section HomologyCongruence

open P103.Specs.Ch10.Complexes (Homology cycles boundaries cycleBoundaries)
open P103.Specs.Ch12.TorBaseChange (coefficientComplex)
open private categoricalHomologyEquiv from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport

variable {A : Type u} [CommRing A]

/-- Degreewise linear equivalences that commute with differentials induce an
equivalence of the cycle quotients, even across module universes. -/
private def quotientHomologyCongr
    {C : ChainComplex (ModuleCat.{v} A) ℕ} {D : ChainComplex (ModuleCat.{w} A) ℕ}
    (e : ∀ i, C.X i ≃ₗ[A] D.X i)
    (he : ∀ i j (x : C.X i), e j (C.d i j x) = D.d i j (e i x)) (i : ℕ) :
    Homology C i ≃ₗ[A] Homology D i := by
  let next := (ComplexShape.down ℕ).next i
  let prev := (ComplexShape.down ℕ).prev i
  have hc : (cycles C i).map (e i).toLinearMap = cycles D i := by
    ext x
    rw [Submodule.mem_map_equiv]
    change C.d i next ((e i).symm x) = 0 ↔ D.d i next x = 0
    rw [← (e next).map_eq_zero_iff, he, LinearEquiv.apply_symm_apply]
  let ec := (e i).ofSubmodules _ _ hc
  apply Submodule.Quotient.equiv _ _ ec
  ext x
  rw [Submodule.mem_map_equiv]
  change (e i).symm (x : D.X i) ∈ boundaries C i ↔ (x : D.X i) ∈ boundaries D i
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e prev y, ?_⟩
    change C.d prev i y = (e i).symm (x : D.X i) at hy
    change D.d prev i (e prev y) = (x : D.X i)
    rw [← he, hy, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, hy⟩
    refine ⟨(e prev).symm y, (e i).injective ?_⟩
    change D.d prev i y = (x : D.X i) at hy
    change e i (C.d prev i ((e prev).symm y)) = e i ((e i).symm (x : D.X i))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hy]

private def torCongrRight (M : ModuleCat.{v} A)
    {N : ModuleCat.{w} A} {N' : ModuleCat.{w'} A} (e : N ≃ₗ[A] N') (i : ℕ) :
    Tor M N i ≃ₗ[A] Tor M N' i := by
  let P := P103.Ch11.ExtTorDefinitions.resolutionFamily A M
  let C := coefficientComplex (S := A) P.val.complex N
  let D := coefficientComplex (S := A) P.val.complex N'
  let E : ∀ j, C.X j ≃ₗ[A] D.X j := fun j =>
    TensorProduct.congr e (LinearEquiv.refl A (P.val.complex.X j))
  refine (IsolatedTorSupport.torLeftEquiv M N P.val P.property i).trans
    ((quotientHomologyCongr E ?_ i).trans
      (IsolatedTorSupport.torLeftEquiv M N' P.val P.property i).symm)
  intro j l x
  change ((E l).toLinearMap.comp (C.d j l).hom) x = ((D.d j l).hom.comp (E j).toLinearMap) x
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro a b
  rfl

private def torCongr {M : ModuleCat.{v} A} {M' : ModuleCat.{v'} A}
    {N : ModuleCat.{w} A} {N' : ModuleCat.{w'} A} (eM : M ≃ₗ[A] M')
    (eN : N ≃ₗ[A] N') (i : ℕ) : Tor M N i ≃ₗ[A] Tor M' N' i :=
  (torCongrRight M eN i).trans
    ((IsolatedTorSupport.torSymmetryEquiv M N' i).trans
      ((torCongrRight N' eM i).trans (IsolatedTorSupport.torSymmetryEquiv N' M' i)))

private def koszulHomologyCongr {M : Type v} {N : Type w}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    (z : List A) (i : ℕ) :
    AdvCommAlg.Koszul.homology M z i ≃ₗ[A] AdvCommAlg.Koszul.homology N z i := by
  let C := AdvCommAlg.Koszul.coefficientComplex M z
  let D := AdvCommAlg.Koszul.coefficientComplex N z
  let E : ∀ j, C.X j ≃ₗ[A] D.X j := fun j =>
    TensorProduct.congr (LinearEquiv.refl A _) e
  let q := quotientHomologyCongr E (fun j l x => by
    by_cases h : (ComplexShape.down ℕ).Rel j l
    · change l + 1 = j at h
      subst j
      have hC : (C.d (l + 1) l).hom = AdvCommAlg.Koszul.coefficientDifferential M z l := by
        simp only [C, AdvCommAlg.Koszul.coefficientComplex, ChainComplex.of_d]
        rfl
      have hD : (D.d (l + 1) l).hom = AdvCommAlg.Koszul.coefficientDifferential N z l := by
        simp only [D, AdvCommAlg.Koszul.coefficientComplex, ChainComplex.of_d]
        rfl
      change ((E l).toLinearMap.comp (C.d (l + 1) l).hom) x =
        ((D.d (l + 1) l).hom.comp (E (l + 1)).toLinearMap) x
      rw [hC, hD]
      apply LinearMap.congr_fun
      apply TensorProduct.ext'
      intro a b
      rfl
    · simp [C.shape j l h, D.shape j l h]) i
  exact (categoricalHomologyEquiv C i).trans
    (q.trans (categoricalHomologyEquiv D i).symm)

end HomologyCongruence

private theorem diagonal_listIdeal (k : Type u) [Field k] (d : ℕ) :
    AdvCommAlg.Koszul.listIdeal (diagonalList k d) = diagonalIdeal k d := by
  simp only [AdvCommAlg.Koszul.listIdeal, diagonalList, List.mem_ofFn',
    Set.ofPred_mem_eq, diagonalIdeal]

private theorem koszul_diagonal_action (k : Type u) [Field k] (d : ℕ)
    (M : ModuleCat.{v} (R k d)) (N : ModuleCat.{w} (R k d)) :
    Specs.diagonalAction M N := by
  intro i s x
  have hs : s - includeX k d d (identify k d s) ∈ AdvCommAlg.Koszul.listIdeal (diagonalList k d) := by
    rw [diagonal_listIdeal, ← identifyKernel k d]
    change identify k d (s - includeX k d d (identify k d s)) = 0
    rw [map_sub, identify_includeX, sub_self]
  exact sub_eq_zero.mp (by
    simpa only [sub_smul] using
      AdvCommAlg.Koszul.annihilates_homology (Specs.diagonalTensor M N) _ _ hs i x)

private theorem length_over_diagonal (k : Type u) [Field k] (d : ℕ)
    (L : Type v) [AddCommGroup L] [Module (S k d d) L] [Module (R k d) L]
    (h : ∀ (s : S k d d) (x : L), s • x = identify k d s • x) :
    Module.length (S k d d) L = Module.length (R k d) L := by
  let : IsScalarTower (S k d d) (R k d) L :=
    IsScalarTower.of_algebraMap_smul (fun s x => (h s x).symm)
  exact Module.length_eq_of_surjective (identify_surjective k d)

set_option backward.isDefEq.respectTransparency false in
private def diagonalHomologyEquiv (k : Type u) [Field k] (d : ℕ)
    (M : ModuleCat.{v} (R k d)) (N : ModuleCat.{w} (R k d))
    [Module.Finite (R k d) M] [Module.Finite (R k d) N] (i : ℕ) :
    Tor M N i ≃ₗ[R k d] Specs.diagonalModule M N i := by
  let : Small.{u} M := Module.Finite.small (R k d) M
  let : Small.{u} N := Module.Finite.small (R k d) N
  let M₀ := ModuleCat.of (R k d) (Shrink.{u} M)
  let N₀ := ModuleCat.of (R k d) (Shrink.{u} N)
  let eM : M ≃ₗ[R k d] M₀ := (Shrink.linearEquiv (R k d) M).symm
  let eN : N ≃ₗ[R k d] N₀ := (Shrink.linearEquiv (R k d) N).symm
  let : Module.Finite (R k d) M₀ := Module.Finite.of_surjective eM.toLinearMap eM.surjective
  let : Module.Finite (R k d) N₀ := Module.Finite.of_surjective eN.toLinearMap eN.surjective
  let eY : OnY N ≃ₗ[Y k d] OnY N₀ :=
    LinearEquiv.ofBijective (ExteriorTensorProduct.onYMap eN.toLinearMap) eN.bijective
  let eTensor : Specs.diagonalTensor M N ≃ₗ[S k d d] Specs.diagonalTensor M₀ N₀ :=
    TensorProduct.AlgebraTensorModule.congr
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (S k d d) (S k d d)) eM) eY
  let eH := koszulHomologyCongr (A := S k d d) (M := Specs.diagonalTensor M N)
    (N := Specs.diagonalTensor M₀ N₀) eTensor (diagonalList k d) i
  let eH' : Specs.diagonalModule M N i ≃ₗ[R k d] Specs.diagonalModule M₀ N₀ i :=
    { eH with map_smul' := fun r x => eH.map_smul (includeX k d d r) x }
  exact (torCongr eM eN i).trans
    ((FieldDiagonalTor.homology_tor k d M₀ N₀ i).some.symm.trans eH'.symm)

set_option backward.isDefEq.respectTransparency false in
theorem powerSeriesDiagonal : Specs.powerSeriesDiagonalType.{u,v,w} := by
  intro k _ d M N _ _ _ _ h
  let T := Specs.diagonalTensor M N
  let : Nontrivial (OnY N) := inferInstanceAs (Nontrivial N)
  let : Module.Finite (S k d d) T := ExteriorTensorProduct.finite
  obtain ⟨hT, hdim, _⟩ :=
    ExteriorTensorDimensionAndMultiplicity.dimensionAndMultiplicity k d d M (OnY N)
  have hdim' : moduleDimensionValue (S k d d) T =
      moduleDimensionValue (R k d) M + moduleDimensionValue (R k d) N :=
    hdim.trans (congrArg (_ + ·) (right_dimension k d N))
  let : Nontrivial T := hT
  have hlen : IsFiniteLength (S k d d) (diagonalReduction k d T) := by
    let E := PowerSeriesDiagonal.tensorQuotientEquiv k d M N
    apply Module.length_ne_top_iff.mp
    rw [E.length_eq]
    let : Module (S k d d) (M ⊗[R k d] N) :=
      ((restrictDiagonal k d).obj (ModuleCat.of _ (M ⊗[R k d] N))).isModule
    exact fun htop => (Module.length_ne_top_iff.mpr h)
      ((length_over_diagonal k d (M ⊗[R k d] N) (fun _ _ => rfl)).symm.trans htop)
  unfold diagonalReduction at hlen
  rw [← diagonal_listIdeal] at hlen
  have hmax := (diagonal_listIdeal k d).trans_le (diagonal_le_maximalIdeal k d)
  have hcard : (diagonalList k d).length = d := List.length_ofFn
  have hAction := koszul_diagonal_action k d M N
  let e := diagonalHomologyEquiv k d M N
  have hLength (i : ℕ) :
      Module.length (S k d d) (Specs.diagonalHomology M N i) =
      Module.length (R k d) (Tor M N i) := by
    let H := Specs.diagonalHomology M N i
    let : Module (R k d) H := (Specs.diagonalModule M N i).isModule
    exact (length_over_diagonal k d H (hAction i)).trans (e i).length_eq.symm
  have hχ : (cutoffEuler M N d : ℚ) = degreeMultiplicity (diagonalIdeal k d) T d := by
    have hf := SerreKoszulEulerFormula.serreKoszulEulerFormula (S k d d) T
      (diagonalList k d) hmax hlen
    change _ = degreeMultiplicity _ _ _ at hf
    rw [hcard, diagonal_listIdeal] at hf
    rw [← hf]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← hLength i]
    rfl
  have hfield := CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k d
  let : IsRegularLocalRing (R k d) := hfield.2.1
  have hd : ringKrullDim (R k d) = (d : WithBot ℕ∞) := hfield.2.2.2.2.1
  refine ⟨hfield.2.1, hd, hAction, fun i => ⟨e i⟩, ?_, ?_, ?_, ?_⟩
  · change (intersectionEuler M N : ℚ) = _
    rw [IsolatedIntersectionEuler.intersectionEuler_eq_cutoff M N d hd]
    exact hχ
  · have hb := SerreKoszulEulerFormula.dimensionBound (S k d d) T (diagonalList k d) hmax hlen hT
    rwa [hcard, hdim'] at hb
  · intro hs
    change intersectionEuler M N = 0
    rw [IsolatedIntersectionEuler.intersectionEuler_eq_cutoff M N d hd]
    have hz := SerreKoszulEulerFormula.zeroOfDimensionLT (S k d d) T (diagonalList k d)
      hmax hlen (by rwa [hcard, hdim'])
    rw [hcard, diagonal_listIdeal] at hz
    exact_mod_cast hχ.trans hz
  · intro hs
    change 0 < intersectionEuler M N
    rw [IsolatedIntersectionEuler.intersectionEuler_eq_cutoff M N d hd]
    obtain ⟨n, hn, hnum⟩ := SerreKoszulEulerFormula.positiveInteger (S k d d) T
      (diagonalList k d) hmax hlen hT (by rwa [hcard, hdim'])
    rw [hcard, diagonal_listIdeal] at hnum
    have hn' : cutoffEuler M N d = n := by exact_mod_cast hχ.trans hnum
    change 0 < cutoffEuler M N d
    rwa [hn']

section Completion

open IntersectionEulerCompletion

/-- A power of the maximal ideal kills a finite-length module, so its
adic Cauchy sequences are eventually constant. -/
private def finiteLengthCompletionEquiv {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (L : Type v) [AddCommGroup L] [Module A L] (h : IsFiniteLength A L) :
    L ≃ₗ[A] CompletedRing A ⊗[A] L := by
  let : IsNoetherian A L := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).1
  let hex := P103.Ch06.FiniteColength.finite_length_power A L h
  let n := hex.choose
  have hn := hex.choose_spec
  have hbot : maximalIdeal A ^ n • (⊤ : Submodule A L) = ⊥ := by
    rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top]
    exact hn
  have hcomplete : IsAdicComplete (maximalIdeal A) L :=
    { haus' := fun x hx => by simpa [hbot, SModEq] using hx n
      prec' := fun f hf => by
        refine ⟨f n, fun m => ?_⟩
        rcases le_total m n with hmn | hnm
        · exact hf hmn
        · have he : f n = f m := by
            simpa [hbot, sub_eq_zero] using SModEq.sub_mem.mp (hf hnm)
          rw [he] }
  exact (LinearEquiv.ofBijective (AdicCompletion.of (maximalIdeal A) L)
    (AdicCompletion.of_bijective_iff.mpr hcomplete)).trans
      ((completionTensorEquiv (R := A) L).restrictScalars A).symm

private def mapCoefficients {k l : Type u} [Field k] [Field l] (e : k ≃+* l) (d : ℕ) :
    R k d ≃+* R l d where
  __ := MvPowerSeries.map e.toRingHom
  invFun := MvPowerSeries.map e.symm.toRingHom
  left_inv f := MvPowerSeries.ext fun n => by simp
  right_inv f := MvPowerSeries.ext fun n => by simp

private theorem completionPresentation (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞))
    (hchar : ringChar (ResidueField A) = ringChar A) :
    ∃ σ : ResidueField A →+* CompletedRing A,
      (residue (CompletedRing A)).comp σ = ResidueField.map (algebraMap A (CompletedRing A)) ∧
      ∃ e : R (ResidueField A) d ≃+* CompletedRing A, ∀ a, e (MvPowerSeries.C a) = σ a := by
  let C := CompletedRing A
  let : IsRegularLocalRing C := completion_regular_local A
  let : Module.FaithfullyFlat A C := AdvCommAlg.CohenMacaulay.completion_faithfullyFlat A
  let r : ResidueField A ≃+* ResidueField C :=
    RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective (R := A))
  have hcharC : ringChar (ResidueField C) = ringChar C := by
    have hk : ringChar (ResidueField A) = ringChar (ResidueField C) :=
      by
        let : CharP (ResidueField C) (ringChar (ResidueField A)) :=
          charP_of_injective_ringHom r.toRingHom.injective _
        exact (ringChar.eq _ _).symm
    have hC : ringChar A = ringChar C :=
      by
        let : CharP C (ringChar A) := charP_of_injective_algebraMap' A _
        exact (ringChar.eq _ _).symm
    exact hk.symm.trans (hchar.trans hC)
  obtain ⟨σ, hσ, e, he, _⟩ :=
    CoefficientRings.equalCharacteristicRegularPresentation C d
      ((completion_ring_dimension A).trans hd) hcharC
  refine ⟨σ.comp r.toRingHom, ?_, (mapCoefficients r d).trans e, ?_⟩
  · rw [← RingHom.comp_assoc, hσ, RingHom.id_comp]
    rfl
  · intro a
    change e (MvPowerSeries.map r.toRingHom (MvPowerSeries.C a)) = σ (r a)
    rw [MvPowerSeries.map_C, he]
    rfl
end Completion

section BijectiveBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

private def baseChangeEquiv (h : Function.Bijective (algebraMap A B))
    (L : Type v) [AddCommGroup L] [Module A L] : L ≃ₗ[A] B ⊗[A] L :=
  (TensorProduct.lid A L).symm.trans
    (TensorProduct.congr (LinearEquiv.ofBijective (Algebra.linearMap A B) h) (LinearEquiv.refl A L))

private theorem baseChange_length (h : Function.Bijective (algebraMap A B))
    (L : Type v) [AddCommGroup L] [Module A L] :
    Module.length B (B ⊗[A] L) = Module.length A L :=
  (Module.length_eq_of_surjective (M := B ⊗[A] L) h.surjective).symm.trans
    (baseChangeEquiv h L).length_eq.symm

private theorem baseChange_dimension (e : A ≃+* B) (he : algebraMap A B = e.toRingHom)
    (L : Type v) [AddCommGroup L] [Module A L] :
    moduleDimensionValue B (B ⊗[A] L) = moduleDimensionValue A L := by
  have hb : Function.Bijective (algebraMap A B) := he ▸ e.bijective
  have hann : Module.annihilator B (B ⊗[A] L) = (Module.annihilator A L).map e.toRingHom := by
    rw [(baseChangeEquiv hb L).annihilator_eq, ← Module.comap_annihilator (R₀ := A) (R := B), ← he]
    exact (Ideal.map_comap_of_surjective _ hb.surjective _).symm
  exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e hann)).symm

end BijectiveBaseChange

open IntersectionEulerCompletion

private theorem completion_nontrivial {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (L : ModuleCat.{v} A) [Module.Finite A L] [Nontrivial L] :
    Nontrivial (completedModuleCat L) := by
  let : Module.FaithfullyFlat A (CompletedRing A) :=
    AdvCommAlg.CohenMacaulay.completion_faithfullyFlat A
  let : Nontrivial (CompletedRing A ⊗[A] L) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right A (CompletedRing A)).mpr
      (inferInstanceAs (Nontrivial L))
  exact (completionTensorEquiv (R := A) L).injective.nontrivial

private theorem presentedModule_dimension {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {d : ℕ} (e : R (ResidueField A) d ≃+* CompletedRing A)
    (L : ModuleCat.{v} A) [Module.Finite A L] :
    moduleDimensionValue (R (ResidueField A) d) (Specs.presentedModule e L) =
      moduleDimensionValue A L := by
  let C := CompletedRing A
  let B := R (ResidueField A) d
  let : Algebra C B := e.symm.toRingHom.toAlgebra
  let Lc := completedModuleCat L
  let : Module.Finite C Lc := completion_module_finite A L
  calc
    moduleDimensionValue B (Specs.presentedModule e L) =
        moduleDimensionValue C Lc := baseChange_dimension e.symm rfl Lc
    _ = Module.supportDim C Lc := dimension_eq_support Lc
    _ = Module.supportDim A L := completion_module_dimension A L
    _ = moduleDimensionValue A L := (dimension_eq_support L).symm

theorem equalCharacteristic : Specs.equalCharacteristicType.{u,v,w} := by
  intro A _ _ d hd hchar M N _ _ _ _ h
  obtain ⟨σ, hσ, e, he⟩ := completionPresentation A d hd hchar
  refine ⟨σ, hσ, e, he, ?_⟩
  dsimp only
  let C := CompletedRing A
  let k := ResidueField A
  let B := R k d
  let : IsRegularLocalRing C := completion_regular_local A
  let Mc := completedModuleCat M
  let Nc := completedModuleCat N
  let : Module.Finite C Mc := completion_module_finite A M
  let : Module.Finite C Nc := completion_module_finite A N
  let : Nontrivial Mc := completion_nontrivial M
  let : Nontrivial Nc := completion_nontrivial N
  let : Algebra C B := e.symm.toRingHom.toAlgebra
  have hb : Function.Bijective (algebraMap C B) := e.symm.bijective
  let : Module.Flat C B := Module.Flat.of_linearEquiv
    (LinearEquiv.ofBijective (Algebra.linearMap C B) hb).symm
  let M' := Specs.presentedModule e M
  let N' := Specs.presentedModule e N
  let : Module.Finite B M' := inferInstanceAs (Module.Finite B (B ⊗[C] Mc))
  let : Module.Finite B N' := inferInstanceAs (Module.Finite B (B ⊗[C] Nc))
  let : Nontrivial M' := (baseChangeEquiv hb Mc).injective.nontrivial
  let : Nontrivial N' := (baseChangeEquiv hb Nc).injective.nontrivial
  have hMcNc : IsFiniteLength C (Mc ⊗[C] Nc) :=
    completion_tensor_finite_length M N h
  have hM'N' : IsFiniteLength B (M' ⊗[B] N') := by
    apply Module.length_ne_top_iff.mp
    rw [← (TensorProduct.AlgebraTensorModule.distribBaseChange C B Mc Nc).length_eq,
      baseChange_length hb]
    exact Module.length_ne_top_iff.mpr hMcNc
  obtain ⟨hregB, hdB, hAction, hTor, hmult, hbound, hzero, hpos⟩ :=
    powerSeriesDiagonal k d M' N' hM'N'
  let := hregB
  let P := P103.Ch11.ExtTorDefinitions.resolutionFamily C Mc
  let torBaseChange (i : ℕ) : B ⊗[C] Tor Mc Nc i ≃ₗ[B] Tor M' N' i :=
    IsolatedTorSupport.flatTorBaseChangeEquiv Mc Nc P.val P.property i
  have hEulerTransport : cutoffEuler M' N' d = cutoffEuler Mc Nc d := by
    unfold cutoffEuler IsolatedIntersectionEuler.Specs.cutoffEuler
    apply Finset.sum_congr rfl
    intro i _
    rw [← (torBaseChange i).length_eq, baseChange_length hb]
  obtain ⟨hreg, hEulerCompletion⟩ := completion_euler M N h
  have hEuler : intersectionEuler M' N' = intersectionEuler M N := by
    rw [IsolatedIntersectionEuler.intersectionEuler_eq_cutoff M' N' d hdB, hEulerTransport, ← IsolatedIntersectionEuler.intersectionEuler_eq_cutoff Mc Nc d
      ((completion_ring_dimension A).trans hd)]
    exact hEulerCompletion
  have hDim := congrArg₂ (· + ·) (presentedModule_dimension e M) (presentedModule_dimension e N)
  refine ⟨hAction, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    let H := Specs.diagonalModule M' N' i
    let f := e.symm.toRingHom
    let g := algebraMap A C
    let post := (torBaseChange i).trans (hTor i).some
    let postC := (ModuleCat.restrictScalars f).mapIso post.toModuleIso
    let middle : Tor Mc Nc i ≃ₗ[C] ↥((ModuleCat.restrictScalars f).obj H) :=
      (baseChangeEquiv hb (Tor Mc Nc i)).trans postC.toLinearEquiv
    let middleA := (ModuleCat.restrictScalars g).mapIso middle.toModuleIso
    let comp := (ModuleCat.restrictScalarsComp g f).app H
    let completionTorA := (ModuleCat.restrictScalars g).mapIso (completionTorEquiv M N i).toModuleIso
    exact ⟨(finiteLengthCompletionEquiv _ (IsolatedIntersectionEuler.tor_finite_length M N h i)).trans
      (completionTorA.toLinearEquiv.trans
        (middleA.toLinearEquiv.trans comp.symm.toLinearEquiv))⟩
  · change (intersectionEuler M N : ℚ) = _
    rw [← hEuler]
    exact hmult
  · exact hDim ▸ hbound
  · intro hs
    change intersectionEuler M N = 0
    rw [← hEuler]
    exact hzero (hDim.symm ▸ hs)
  · intro hs
    change 0 < intersectionEuler M N
    rw [← hEuler]
    exact hpos (hDim.symm ▸ hs)

end CommutativeAlgebraNotes.Intersection.EqualCharacteristicIntersection
