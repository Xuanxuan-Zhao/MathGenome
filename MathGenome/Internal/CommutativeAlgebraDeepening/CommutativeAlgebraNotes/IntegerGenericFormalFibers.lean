import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IntegerGenericFormalFibers
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExtendDerivations
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FormalFiberQuotient
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularAuxiliaryRings
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.GeometricClosedPointRegularity
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Batteries.Tactic.OpenPrivate

/-! Geometric regularity of the generic formal fibres over the integers. -/

universe u

open IsLocalRing
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Excellence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private abbrev AbsoluteDerivation (R : Type*) [CommRing R] := Derivation ℤ R R

private theorem formallySmooth_field_of_charZero (K : Type*) [Field K]
    [Algebra ℤ K] [Algebra.EssFiniteType ℤ K] [CharZero K] :
    Algebra.FormallySmooth ℤ K := by
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI htower := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := K)
    (RingHom.ext_int _ _)
  haveI : Algebra.EssFiniteType ℚ K := Algebra.EssFiniteType.of_comp ℤ ℚ K
  haveI : Algebra.FormallySmooth ℤ ℚ := .of_isLocalization (nonZeroDivisors ℤ)
  exact Algebra.FormallySmooth.comp ℤ ℚ K

/-- A functional on the cotangent space of a local algebra with formally
smooth residue field is realized by a derivation to the residue field. -/
private theorem exists_residue_derivation (k S : Type*) [CommRing k] [CommRing S] [IsLocalRing S]
    [Algebra k S]
    [Algebra.FormallySmooth k S] [Algebra.FormallySmooth k (ResidueField S)]
    (l : CotangentSpace S →ₗ[ResidueField S] ResidueField S) :
    ∃ d : S →+ ResidueField S,
      (∀ a : k, d (algebraMap k S a) = 0) ∧
      (∀ x y : S, d (x * y) = x • d y + y • d x) ∧
      (∀ x : maximalIdeal S, d x = l ((maximalIdeal S).toCotangent x)) := by
  let K := ResidueField S
  have hs : Function.Surjective (algebraMap S K) := Ideal.Quotient.mk_surjective
  obtain ⟨r, hr⟩ := (Algebra.FormallySmooth.iff_split_injection
    (R := k) hs).mp (inferInstance : Algebra.FormallySmooth k K)
  let e := Ideal.Cotangent.equivOfEq (RingHom.ker (algebraMap S K)) (maximalIdeal S)
    (ker_residue (R := S))
  let l' : K ⊗[S] KaehlerDifferential k S →ₗ[S] K := l.restrictScalars S ∘ₗ e.toLinearMap ∘ₗ r
  have hlinear (x : maximalIdeal S) :
      l' (1 ⊗ₜ KaehlerDifferential.D k S (x : S)) =
        l ((maximalIdeal S).toCotangent x) := by
    let x' : RingHom.ker (algebraMap S K) := ⟨x, (residue_eq_zero_iff (x : S)).mpr x.2⟩
    have he : r (1 ⊗ₜ KaehlerDifferential.D k S (x : S)) =
        (RingHom.ker (algebraMap S K)).toCotangent x' :=
      DFunLike.congr_fun hr ((RingHom.ker (algebraMap S K)).toCotangent x')
    change l (e (r (1 ⊗ₜ KaehlerDifferential.D k S (x : S)))) = _
    rw [he]
    rfl
  let t : KaehlerDifferential k S →ₗ[S] K := l' ∘ₗ TensorProduct.mk S K _ 1
  let d := t.compDer (KaehlerDifferential.D k S)
  exact ⟨d.toLinearMap.toAddMonoidHom, d.map_algebraMap, d.leibniz, hlinear⟩

/-- Clearing the finitely many denominators in the values on the variables
realizes a residue-valued derivation up to a nonzero residue scalar. -/
private theorem exists_scaled_polynomial_derivation {ι : Type*} [Finite ι]
    {S : Type*} [CommRing S] [IsLocalRing S] [Algebra (MvPolynomial ι ℤ) S]
    (I : Ideal (MvPolynomial ι ℤ)) [I.IsPrime] [IsLocalization.AtPrime S I]
    (d : S →+ ResidueField S)
    (hd₀ : ∀ z : ℤ, d (algebraMap (MvPolynomial ι ℤ) S (MvPolynomial.C z)) = 0)
    (hdm : ∀ x y : S, d (x * y) = x • d y + y • d x) :
    ∃ (D : Derivation ℤ (MvPolynomial ι ℤ) (MvPolynomial ι ℤ))
      (b : I.primeCompl), ∀ x : MvPolynomial ι ℤ,
        residue S (algebraMap (MvPolynomial ι ℤ) S (D x)) =
          residue S (algebraMap (MvPolynomial ι ℤ) S b) *
            d (algebraMap (MvPolynomial ι ℤ) S x) := by
  let C := MvPolynomial ι ℤ
  let K := ResidueField S
  choose a ha using fun j : ι => (Ideal.Quotient.mk_surjective
    (I := maximalIdeal S)) (d (algebraMap C S (MvPolynomial.X j)))
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite I.primeCompl a
  choose g hg using hb
  let D : Derivation ℤ C C := MvPolynomial.mkDerivation ℤ g
  have hvar (j : ι) : residue S (algebraMap C S (D (MvPolynomial.X j))) =
      residue S (algebraMap C S b) * d (algebraMap C S (MvPolynomial.X j)) := by
    rw [show D (MvPolynomial.X j) = g j from MvPolynomial.mkDerivation_X _ _ _,
      hg j, Algebra.smul_def, map_mul]
    congr 1
    exact ha j
  let r : C →+* K := (residue S).comp (algebraMap C S)
  refine ⟨D, b, fun x => ?_⟩
  change r (D x) = r b * d (algebraMap C S x)
  induction x using MvPolynomial.induction_on with
  | C z =>
    rw [hd₀, ← MvPolynomial.algebraMap_eq, D.map_algebraMap, map_zero, mul_zero]
  | add x y hx hy =>
    rw [map_add D, map_add r, map_add (algebraMap C S), map_add d, mul_add, hx, hy]
  | mul_X x j hx =>
    rw [D.leibniz, map_add r, map_mul (algebraMap C S), hdm]
    simp only [smul_eq_mul, Algebra.smul_def, map_mul r, mul_add, ResidueField.algebraMap_eq,
      hx, show r (D (MvPolynomial.X j)) = r b * d (algebraMap C S (MvPolynomial.X j)) from hvar j]
    change r x * (r b * d (algebraMap C S (MvPolynomial.X j))) +
      r (MvPolynomial.X j) * (r b * d (algebraMap C S x)) =
      r b * (r x * d (algebraMap C S (MvPolynomial.X j))) +
      r b * (r (MvPolynomial.X j) * d (algebraMap C S x))
    rw [mul_left_comm (r x), mul_left_comm (r (MvPolynomial.X j))]

/-- The preimages of a cotangent basis generate the maximal ideal. -/
private theorem span_of_cotangent_basis {S : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] {ι : Type*}
    (b : Module.Basis ι (ResidueField S) (CotangentSpace S))
    (x : ι → maximalIdeal S) (hx : ∀ i, (maximalIdeal S).toCotangent (x i) = b i) :
    Ideal.span (Set.range (fun i => (x i : S))) = maximalIdeal S := by
  have htop : Submodule.span S (Set.range x) = ⊤ := by
    apply CotangentSpace.span_image_eq_top_iff.mp
    rw [← Set.range_comp, show (maximalIdeal S).toCotangent ∘ x = b from funext hx]
    exact b.span_eq
  have hmap := congrArg (Submodule.map (maximalIdeal S).subtype) htop
  change Submodule.span S (Set.range (fun i => (x i : S))) = _
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at hmap
  exact hmap

open AdvCommAlg.Smooth in
/-- At a prime above the original generic point, equations from its local
polynomial presentation cut out a regular quotient in the completed ring. -/
private theorem regular_quotient_of_extended_derivations {ι : Type*} [Finite ι]
    (I : Ideal (MvPolynomial ι ℤ)) [I.IsPrime]
    [CharZero (ResidueField (Localization.AtPrime I))]
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (f : Localization.AtPrime I →+* R) [IsLocalHom f]
    (hext : ∀ D : Derivation ℤ (MvPolynomial ι ℤ) (MvPolynomial ι ℤ),
      ∃ E : AbsoluteDerivation R, ∀ x : MvPolynomial ι ℤ,
        E (f (algebraMap _ _ x)) = f (algebraMap _ _ (D x))) :
    IsRegularLocalRing (R ⧸ (maximalIdeal (Localization.AtPrime I)).map f) := by
  classical
  let C := MvPolynomial ι ℤ
  let S := Localization.AtPrime I
  let K := ResidueField S
  let F := ResidueField R
  let c := Module.finrank K (CotangentSpace S)
  let b : Module.Basis (Fin c) K (CotangentSpace S) := Module.finBasis K _
  let fr : K →+* F := ResidueField.map f
  haveI hS : Algebra.FormallySmooth ℤ S := Algebra.FormallySmooth.comp ℤ C S
  haveI hess : Algebra.EssFiniteType ℤ K := by
    change Algebra.EssFiniteType ℤ (S ⧸ maximalIdeal S)
    infer_instance
  haveI hK : Algebra.FormallySmooth ℤ K :=
    @formallySmooth_field_of_charZero K _ _ hess ‹CharZero (ResidueField (Localization.AtPrime I))›
  choose x hx using fun i : Fin c => (maximalIdeal S).toCotangent_surjective (b i)
  choose g a hga using fun i : Fin c =>
    IsLocalization.exists_mk'_eq I.primeCompl (x i : S)
  have hg (i : Fin c) : algebraMap C S (g i) = algebraMap C S (a i) * (x i : S) := by
    rw [← hga i, IsLocalization.mk'_spec']
  choose d hd₀ hdm hd using fun j : Fin c =>
    @exists_residue_derivation ℤ S _ _ _ _ hS hK (b.coord j)
  have hconst (j : Fin c) (z : ℤ) :
      d j (algebraMap C S (MvPolynomial.C z)) = 0 := by
    rw [← MvPolynomial.algebraMap_eq ℤ ι, ← IsScalarTower.algebraMap_apply ℤ C S]
    exact hd₀ j z
  choose D s hD using fun j => exists_scaled_polynomial_derivation I (d j) (hconst j) (hdm j)
  choose E hE using fun j => hext (D j)
  have hval (i j : Fin c) :
      residue R (E j (f (x i : S))) = fr (residue S (algebraMap C S (s j))) *
          fr (b.coord j (b i)) := by
    have hmem : residue R (f (x i : S)) = 0 :=
      (residue_eq_zero_iff _).mpr (map_maximalIdeal_le f (Ideal.mem_map_of_mem f (x i).2))
    have hmul : residue R (E j (f (algebraMap C S (g i)))) =
        residue R (f (algebraMap C S (a i))) * residue R (E j (f (x i : S))) := by
      rw [hg, map_mul, (E j).leibniz, map_add]
      simp only [smul_eq_mul, map_mul, hmem, zero_mul, add_zero]
    rw [hE, ← ResidueField.map_residue, hD, hg, hdm, hd, hx] at hmul
    have hx0 : residue S (x i : S) = 0 := (residue_eq_zero_iff _).mpr (x i).2
    simp only [Algebra.smul_def, ResidueField.algebraMap_eq, hx0, zero_mul, add_zero,
      map_mul] at hmul
    have hu : IsUnit (residue R (f (algebraMap C S (a i)))) :=
      ((IsLocalization.map_units S (a i)).map f).map (residue R)
    have haR : fr (residue S (algebraMap C S (a i))) =
        residue R (f (algebraMap C S (a i))) := ResidueField.map_residue f _
    rw [mul_left_comm (fr (residue S (algebraMap C S (s j)))), haR] at hmul
    exact ((IsUnit.mul_right_inj hu).mp hmul).symm
  let y : Fin c → maximalIdeal R := fun i =>
    ⟨f (x i : S), map_maximalIdeal_le f (Ideal.mem_map_of_mem f (x i).2)⟩
  have hgen : Ideal.span (Set.range fun i => (y i : R)) = (maximalIdeal S).map f := by
    rw [← span_of_cotangent_basis b x hx, Ideal.map_span, ← Set.range_comp]
    rfl
  let L : CotangentSpace R →ₗ[F] (Fin c → F) := LinearMap.pi fun j =>
    (fr (residue S (algebraMap C S (s j))))⁻¹ • cotangentFunctional (E j)
  have hv (i : Fin c) : L ((maximalIdeal R).toCotangent (y i)) = Pi.single i 1 := by
    ext j
    change (fr (residue S (algebraMap C S (s j))))⁻¹ *
      residue R (E j (f (x i : S))) = _
    rw [hval, ← mul_assoc, inv_mul_cancel₀ (show fr (residue S (algebraMap C S (s j))) ≠ 0
      from isUnit_iff_ne_zero.mp
        (((IsLocalization.map_units S (s j)).map (residue S)).map fr)), one_mul]
    by_cases hij : j = i
    · simp [hij, Module.Basis.coord_apply]
    · simp [hij, Module.Basis.coord_apply]
  have hli : LinearIndependent F (fun i => (maximalIdeal R).toCotangent (y i)) := by
    apply LinearIndependent.of_comp L
    have hcomp : (L ∘ fun i => (maximalIdeal R).toCotangent (y i)) =
        ⇑(Pi.basisFun F (Fin c)) := by
      funext i
      exact (hv i).trans (Pi.basisFun_apply F (Fin c) i).symm
    rw [hcomp]
    exact (Pi.basisFun F (Fin c)).linearIndependent
  rw [← hgen]
  exact (regular_quotient_of_cotangent_independent
    ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm y hli).1

open private completionTensorEquiv from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FormalFiberQuotient

/-- The quotient identification for the completions of a surjective map of
Noetherian local rings, with its effect on the original local rings. -/
private theorem exists_completion_quotient {B S : Type u} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [CommRing S] [IsLocalRing S]
    (f : B →+* S) (hf : Function.Surjective f) :
    ∃ F : AdicCompletion (maximalIdeal B) B →+* AdicCompletion (maximalIdeal S) S,
      Function.Surjective F ∧
      RingHom.ker F = (RingHom.ker f).map (algebraMap B _) ∧
      ∀ x : B, F (algebraMap B _ x) = algebraMap S _ (f x) := by
  let U := AdicCompletion (maximalIdeal B) B
  have hm := map_maximalIdeal_of_surjective f hf
  suffices ∃ F : U →+* AdicCompletion ((maximalIdeal B).map f) S,
      Function.Surjective F ∧ RingHom.ker F = (RingHom.ker f).map (algebraMap B U) ∧
        ∀ x : B, F (algebraMap B U x) = algebraMap S _ (f x) by
    rw [← hm]
    exact this
  letI : Algebra B S := f.toAlgebra
  let K := RingHom.ker f
  let Q := B ⧸ K
  let V := AdicCompletion ((maximalIdeal B).map f) S
  haveI : Module.Finite B S := Module.Finite.of_surjective (Algebra.linearMap B S) hf
  let e₀ : Q ≃ₐ[B] S := Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId B S) hf
  let e₁ := Algebra.TensorProduct.quotIdealMapEquivQuotTensor U K
  let e₂ := Algebra.TensorProduct.congr e₀ (AlgEquiv.refl : U ≃ₐ[B] U)
  let e₃ : S ⊗[B] U ≃ₐ[S] V := completionTensorEquiv (maximalIdeal B) S
  let e := e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃.toRingEquiv)
  let F : U →+* V := e.toRingHom.comp (Ideal.Quotient.mk (K.map (algebraMap B U)))
  refine ⟨F, e.surjective.comp Ideal.Quotient.mk_surjective, ?_, ?_⟩
  · change RingHom.ker (e.toRingHom.comp (Ideal.Quotient.mk _)) = _
    rw [RingHom.ker_comp_of_injective _ e.injective, Ideal.mk_ker]
  · intro x
    change e₃ (e₂ (e₁ (Ideal.Quotient.mk _ (algebraMap B U x)))) = algebraMap S V (f x)
    dsimp only [e₁, e₂]
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    change e₃ (1 ⊗ₜ[B] algebraMap B U x) = _
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact e₃.commutes (f x)

set_option maxHeartbeats 800000 in
theorem integerGenericFormalFiber : Specs.integerGenericFormalFiberType.{u} := by
  intro A _ _ _ hZ p hp
  classical
  let K := FractionRing A
  let S := Localization.AtPrime p
  let T := AdicCompletion (maximalIdeal S) S
  let W := K ⊗[A] T
  change GeometricallyRegular K W
  haveI : CharZero A := charZero_of_injective_algebraMap hZ
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  haveI : IsNoetherianRing T := P103.Ch07.CompletedNoetherian.completed_noetherian S (maximalIdeal S)
  letI : Algebra T W := Algebra.TensorProduct.rightAlgebra
  let M := (nonZeroDivisors A).map (algebraMap A T)
  haveI : IsLocalization M W := IsLocalization.tensorRight (S := T) K (nonZeroDivisors A)
  haveI : IsNoetherianRing W := IsLocalization.isNoetherianRing M W inferInstance
  suffices hregular : RegularRing W by
    intro L _ _ _
    haveI : Algebra.IsSeparable K L := inferInstance
    have hn : IsNoetherianRing (W ⊗[K] L) := IsNoetherianRing.of_finite W (W ⊗[K] L)
    exact ⟨isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm K W L).toRingEquiv,
      regularRing_separableScalarExtension K L W hregular⟩
  obtain ⟨ι, _, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
    (inferInstance : Algebra.FiniteType ℤ A)
  let C := MvPolynomial ι ℤ
  let I := RingHom.ker π.toRingHom
  haveI : I.IsPrime := RingHom.ker_isPrime π.toRingHom
  haveI : CharZero (ResidueField (Localization.AtPrime I)) := by
    change CharZero I.ResidueField
    apply charZero_of_injective_algebraMap (R := ℤ)
    rw [injective_iff_map_eq_zero]
    intro z hz
    rw [IsScalarTower.algebraMap_apply ℤ C I.ResidueField,
      Ideal.algebraMap_residueField_eq_zero] at hz
    apply hZ
    change π (algebraMap ℤ C z) = 0 at hz
    exact (π.commutes z).symm.trans (hz.trans (map_zero _).symm)
  let P := p.comap π.toRingHom
  haveI : P.IsPrime := Ideal.comap_isPrime π.toRingHom p
  let B := Localization.AtPrime P
  let U := AdicCompletion (maximalIdeal B) B
  let g : B →+* S := Localization.localRingHom P p π.toRingHom rfl
  obtain ⟨hg, hgker⟩ := AdvCommAlg.Smooth.localRingHom_surjective_ker π.toRingHom hπ p
  obtain ⟨F, hF, hFker, hFmap⟩ := exists_completion_quotient g hg
  have hB : IsRegularLocalRing B := regularRing_mvPolynomial ℤ ι
    ((regularRing_iff ℤ).mpr inferInstance) P
  have hU : RegularRing U := regularRing_completion B hB
  intro q hq
  let qT := q.comap (algebraMap T W)
  haveI : qT.IsPrime := Ideal.comap_isPrime (algebraMap T W) q
  let qU := qT.comap F
  haveI : qU.IsPrime := Ideal.comap_isPrime F qT
  let R := Localization.AtPrime qU
  haveI : IsRegularLocalRing R := hU qU
  let φ : C →+* U := (algebraMap B U).comp (algebraMap C B)
  have hI : I = qU.comap φ := by
    ext x
    change π x = 0 ↔ algebraMap T W (F (algebraMap B U (algebraMap C B x))) ∈ q
    rw [hFmap, Localization.localRingHom_to_map]
    rw [← IsScalarTower.algebraMap_apply A S T, ← IsScalarTower.algebraMap_apply A T W]
    change π x = 0 ↔ algebraMap A W (π x) ∈ q
    constructor
    · rintro h
      rw [h, map_zero]
      exact q.zero_mem
    · intro h
      by_contra hn
      have hu : IsUnit (algebraMap A W (π x)) := by
        rw [IsScalarTower.algebraMap_apply A K W]
        have hn' : algebraMap A K (π x) ≠ 0 := by
          intro hz
          exact hn ((IsFractionRing.injective A K) (hz.trans (map_zero _).symm))
        exact (isUnit_iff_ne_zero.mpr hn').map (algebraMap K W)
      exact hq.ne_top (q.eq_top_of_isUnit_mem h hu)
  let f : Localization.AtPrime I →+* R := Localization.localRingHom I qU φ hI
  haveI : IsLocalHom f := Localization.isLocalHom_localRingHom I qU φ hI
  have hfmap (x : C) : f (algebraMap C _ x) =
      algebraMap U R (algebraMap B U (algebraMap C B x)) :=
    Localization.localRingHom_to_map I qU φ hI x
  have hext (D : Derivation ℤ C C) : ∃ E : AbsoluteDerivation R, ∀ x : C,
      E (f (algebraMap C _ x)) = f (algebraMap C _ (D x)) := by
    let D₁ := localizationDerivation P.primeCompl D (L := B)
    let D₂ := adicCompletionDerivation D₁ (maximalIdeal B)
    refine ⟨localizationDerivation qU.primeCompl D₂, ?_⟩
    intro x
    rw [hfmap x, hfmap (D x), localizationDerivation_algebraMap]
    change algebraMap U R (adicCompletionDerivation D₁ (maximalIdeal B)
      (algebraMap B U (algebraMap C B x))) = _
    rw [adicCompletionDerivation_algebraMap]
    change algebraMap U R (algebraMap B U
      (localizationDerivation P.primeCompl D (algebraMap C B x))) = _
    rw [localizationDerivation_algebraMap]
  have hj : (maximalIdeal (Localization.AtPrime I)).map f =
      (RingHom.ker F).map (algebraMap U R) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := I), Ideal.map_map,
      hFker, hgker, Ideal.map_map, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro x
    exact hfmap x
  have hquot := regular_quotient_of_extended_derivations I f hext
  rw [hj] at hquot
  haveI : IsRegularLocalRing (Localization.AtPrime qT) := by
    letI := hquot
    exact IsRegularLocalRing.of_ringEquiv (AdvCommAlg.Smooth.localQuotientEquiv F hF qT)
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) qT :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ q
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv qT.primeCompl
    (Localization.AtPrime qT) (Localization.AtPrime q)).toRingEquiv

end

end CommutativeAlgebraNotes.Excellence
