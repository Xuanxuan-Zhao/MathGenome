import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.AffineIntegralClosureFinite
import MathGenome.Internal.AlgebraCore.P103.Ch06.NoetherNormalization
import MathGenome.Internal.AlgebraCore.P103.Ch06.SeparableIntegralClosureFinite
import MathGenome.Internal.AlgebraCore.P103.Ch06.InseparableAffineCover
import MathGenome.Internal.AlgebraCore.P103.Ch05.NoetherianFiniteness
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace P103.Ch06.AffineIntegralClosureFinite

universe u v w

/-- Integral elements in a smaller field embed in the upstairs closure.  The
Noetherian hypothesis applies to the base, so no finiteness of the smaller
closure is assumed. -/
theorem finite_closure_of_cover
    (B C : Type*) [CommRing B] [CommRing C] [Algebra B C]
    [IsNoetherianRing B] [Module.Finite B C]
    (L N : Type*) [Field L] [Field N]
    [Algebra B L] [Algebra B N] [Algebra C N] [IsScalarTower B C N]
    (j : L →ₐ[B] N) [Module.Finite C (integralClosure C N)] :
    Module.Finite B (integralClosure B L) := by
  let : Module.Finite B (integralClosure C N) :=
    Module.Finite.trans C (integralClosure C N)
  let f : integralClosure B L →ₗ[B] integralClosure C N :=
    { toFun := fun x => ⟨j x.val, (x.property.map j).tower_top⟩
      map_add' := fun x y => Subtype.ext (map_add j x.val y.val)
      map_smul' := fun r x => Subtype.ext (j.toLinearMap.map_smul r x.val) }
  exact Module.Finite.of_injective f (fun x y h =>
    Subtype.ext (j.injective (congrArg Subtype.val h)))

open P103.Ch06.AffineCover
open scoped IntermediateField.algebraAdjoinAdjoin

local instance coordinateBaseAlgebra {k : Type u} [Field k] {Ω : Type v} [Field Ω]
    [Algebra k Ω] {d : ℕ} (t : Fin d → Ω) :
    Algebra (polynomialRing k t) (rationalField k t) :=
  (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k (Set.range t))).toAlgebra

local instance coordinateAlgebra {k : Type u} [Field k] {Ω : Type v} [Field Ω]
    [Algebra k Ω] {d : ℕ} (t : Fin d → Ω)
    (L : IntermediateField (rationalField k t) Ω) : Algebra (polynomialRing k t) L :=
  ((algebraMap (rationalField k t) L).comp
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k
      (Set.range t))).toRingHom).toAlgebra

/-- A polynomial coordinate subalgebra is Noetherian and normal. -/
theorem polynomial_properties (k : Type u) [Field k]
    (Ω : Type v) [Field Ω] [Algebra k Ω]
    (d : ℕ) (t : Fin d → Ω) (ht : AlgebraicIndependent k t) :
    IsNoetherianRing (polynomialRing k t) ∧ IsIntegrallyClosed (polynomialRing k t) := by
  exact ⟨isNoetherianRing_of_ringEquiv (MvPolynomial (Fin d) k) ht.aevalEquiv.toRingEquiv,
    IsIntegrallyClosed.of_equiv ht.aevalEquiv.toRingEquiv⟩

set_option maxHeartbeats 800000 in
/-- Positive-characteristic polynomial case inside an algebraic closure. -/
theorem finite_polynomial_closure_pos
    (k : Type u) [Field k] (Ω : Type v) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (d : ℕ) (t : Fin d → Ω) (ht : AlgebraicIndependent k t)
    (L : IntermediateField (rationalField k t) Ω)
    [Module.Finite (rationalField k t) L] :
    Module.Finite (polynomialRing k t) (integralClosure (polynomialRing k t) L) := by
  obtain ⟨e, c, z, N, hcfin, _hcpure, _hcpow, _hz, hzind, hLN,
    ⟨hMN, hNfin, hNsep⟩, ⟨hBC, hCfin⟩⟩ :=
    P103.Ch06.AffineCover.inseparableAffineCover k Ω p d t ht L inferInstance
  let B := polynomialRing k t
  let C := coveringRing k c z
  let E := coveringField k c z
  let : Algebra B C := (Subalgebra.inclusion hBC).toAlgebra
  let : Module.Finite B C := hCfin
  let : Algebra E N := (IntermediateField.inclusion hMN).toAlgebra
  let : Module.Finite E N := hNfin
  let : Algebra.IsSeparable E N := hNsep
  let : Algebra C E := (Subalgebra.inclusion
    (IntermediateField.algebra_adjoin_le_adjoin c (Set.range z))).toAlgebra
  have : IsFractionRing C E :=
    show IsFractionRing (Algebra.adjoin c (Set.range z))
      (IntermediateField.adjoin c (Set.range z)) from inferInstance
  let : Algebra C N := ((algebraMap E N).comp (algebraMap C E)).toAlgebra
  let : IsScalarTower C E N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra B N := ((algebraMap C N).comp (algebraMap B C)).toAlgebra
  let : IsScalarTower B C N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsNoetherianRing B := (polynomial_properties k Ω d t ht).1
  let : IsNoetherianRing C := (polynomial_properties c Ω d z hzind).1
  let : IsIntegrallyClosed C := (polynomial_properties c Ω d z hzind).2
  let : Module.Finite C (integralClosure C N) :=
    P103.Ch06.SeparableIntegralClosureFinite.finite_integralClosure C E N
  let j : L →ₐ[B] N :=
    { toRingHom := (IntermediateField.inclusion hLN).toRingHom
      commutes' := fun _ => rfl }
  exact finite_closure_of_cover B C L N j

/-- Polynomial case in every characteristic. -/
theorem finite_polynomial_closure
    (k : Type u) [Field k] (Ω : Type v) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (d : ℕ) (t : Fin d → Ω) (ht : AlgebraicIndependent k t)
    (L : IntermediateField (rationalField k t) Ω)
    [Module.Finite (rationalField k t) L] :
    Module.Finite (polynomialRing k t) (integralClosure (polynomialRing k t) L) := by
  obtain ⟨p, hp⟩ := CharP.exists k
  let : CharP k p := hp
  rcases CharP.char_is_prime_or_zero k p with hprime | rfl
  · let : Fact p.Prime := ⟨hprime⟩
    exact finite_polynomial_closure_pos k Ω p d t ht L
  · let : CharZero k := CharP.charP_to_charZero k
    let B := polynomialRing k t
    let K := rationalField k t
    let : IsFractionRing B K := show IsFractionRing (Algebra.adjoin k (Set.range t))
      (IntermediateField.adjoin k (Set.range t)) from inferInstance
    let : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : IsNoetherianRing B := (polynomial_properties k Ω d t ht).1
    let : IsIntegrallyClosed B := (polynomial_properties k Ω d t ht).2
    exact P103.Ch06.SeparableIntegralClosureFinite.finite_integralClosure B K L

/-- Change polynomial coordinates and embed the ambient field. -/
theorem finite_closure_transport (R S : Type*) [CommRing R] [CommRing S]
    [IsNoetherianRing S] (F G : Type*) [Field F] [Field G]
    [Algebra R F] [Algebra S G] (e : R ≃+* S) (j : F →+* G)
    (h : (algebraMap S G).comp e.toRingHom = j.comp (algebraMap R F))
    [Module.Finite S (integralClosure S G)] :
    Module.Finite R (integralClosure R F) := by
  let f : integralClosure R F →ₛₗ[e.toRingHom] integralClosure S G :=
    { toFun := fun x => ⟨j x.val, x.property.map_of_comp_eq e.toRingHom j h⟩
      map_add' := fun x y => Subtype.ext (map_add j x.val y.val)
      map_smul' := fun r x => by
        apply Subtype.ext
        dsimp only
        rw [Subalgebra.coe_smul, Subalgebra.coe_smul]
        simp only [Algebra.smul_def, map_mul]
        exact congrArg (fun z => z * j x.val) (RingHom.congr_fun h r).symm }
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm
  exact Module.Finite.of_injective (σ' := e.symm.toRingHom) f (fun x y hx =>
    Subtype.ext (j.injective (congrArg Subtype.val hx)))

set_option maxHeartbeats 800000 in
/-- The polynomial case for arbitrary fraction fields and arbitrary finite
field extensions, with no ambient realization built into its hypotheses. -/
theorem finite_mvPolynomial_closure
    (k : Type u) [Field k] (d : ℕ)
    (K : Type v) [Field K] [Algebra (MvPolynomial (Fin d) k) K]
    [Algebra k K] [IsScalarTower k (MvPolynomial (Fin d) k) K]
    [IsFractionRing (MvPolynomial (Fin d) k) K]
    (L : Type w) [Field L] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [Algebra (MvPolynomial (Fin d) k) L]
    [IsScalarTower (MvPolynomial (Fin d) k) K L]
    [Module.Finite K L] :
    Module.Finite (MvPolynomial (Fin d) k) (integralClosure (MvPolynomial (Fin d) k) L) := by
  let P := MvPolynomial (Fin d) k
  let Ω := AlgebraicClosure L
  let g : L →ₐ[k] Ω := IsScalarTower.toAlgHom k L Ω
  let f : K →ₐ[k] Ω := g.comp (IsScalarTower.toAlgHom k K L)
  let a : P →ₐ[k] Ω := f.comp (IsScalarTower.toAlgHom k P K)
  let t : Fin d → Ω := a ∘ MvPolynomial.X
  have hat : MvPolynomial.aeval t = a := (MvPolynomial.aeval_unique a).symm
  have ht : AlgebraicIndependent k t :=
    algebraicIndependent_iff_injective_aeval.mpr (hat ▸
      (f.injective.comp (IsFractionRing.injective P K)))
  let B := polynomialRing k t
  let E := rationalField k t
  have hf : f.fieldRange = E := by
    apply IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
      (A := P) (K := K) (g := a)
    · rfl
    · rw [← hat, MvPolynomial.aeval_range]
  have hEG : E ≤ g.fieldRange := by
    rw [← hf]
    rintro x ⟨y, rfl⟩
    exact ⟨algebraMap K L y, rfl⟩
  let L' : IntermediateField E Ω := IntermediateField.extendScalars hEG
  let eK : K ≃ₐ[k] E := (AlgEquiv.ofInjectiveField f).trans (IntermediateField.equivOfEq hf)
  let ell : L →+* L' := (AlgEquiv.ofInjectiveField g).toRingEquiv.toRingHom
  let lin : L →ₛₗ[eK.toRingEquiv.toRingHom] L' :=
    { toFun := ell
      map_add' := ell.map_add
      map_smul' := fun r x => by
        apply Subtype.ext
        dsimp only [ell]
        simp only [RingEquiv.toRingHom_eq_coe]
        rw [IntermediateField.coe_smul]
        change g (r • x) = (eK r) • g x
        simp only [Algebra.smul_def, map_mul]
        rfl }
  let : Module.Finite E L' := Module.Finite.of_surjective lin
    (AlgEquiv.ofInjectiveField g).surjective
  let : IsNoetherianRing B := (polynomial_properties k Ω d t ht).1
  let : Module.Finite B (integralClosure B L') := finite_polynomial_closure k Ω d t ht L'
  apply finite_closure_transport P B L L' ht.aevalEquiv.toRingEquiv ell
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change (ht.aevalEquiv x : Ω) = g (algebraMap P L x)
  change algebraMap (Algebra.adjoin k (Set.range t)) Ω (ht.aevalEquiv x) = _
  rw [ht.algebraMap_aevalEquiv, hat]
  change f (algebraMap P K x) = g (algebraMap P L x)
  rw [IsScalarTower.algebraMap_apply P K L]
  rfl

/-- Equality of closures and transfer of finiteness along the finite
normalizing map. -/
theorem normalization_reduction :
    P103.Specs.Ch06.AffineIntegralClosureFinite.normalization_reductionType := by
  intro B A L _ _ _ _ _ _ _ _
  have heq : (integralClosure A L).restrictScalars B = integralClosure B L := by
    ext z
    exact ⟨fun h => isIntegral_trans z h, fun h => h.tower_top⟩
  refine ⟨heq, fun hfin => ?_⟩
  let := hfin
  have hmodule : Module.Finite B ((integralClosure A L).restrictScalars B) := by
    rw [heq]
    infer_instance
  let : Module.Finite B (integralClosure A L) := hmodule
  exact Module.Finite.of_restrictScalars_finite B A (integralClosure A L)

set_option maxHeartbeats 1000000 in
/-- Theorem 6.8, including finite inseparable extensions over imperfect fields. -/
theorem affine_integral_closure :
    P103.Specs.Ch06.AffineIntegralClosureFinite.affine_integral_closureType := by
  intro k A E L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  let : Algebra k E := ((algebraMap A E).comp (algebraMap k A)).toAlgebra
  let : IsScalarTower k A E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower k E L := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap k L r = algebraMap E L (algebraMap A E (algebraMap k A r))
    rw [← IsScalarTower.algebraMap_apply A E L, ← IsScalarTower.algebraMap_apply k A L]
  obtain ⟨d, g, hinj, hfin, _hdim⟩ :=
    P103.Ch06.NoetherNormalization.normalization_map k A
  let P := MvPolynomial (Fin d) k
  let : Algebra P A := g.toRingHom.toAlgebra
  let : Module.Finite P A := hfin
  let : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  let : Algebra P E := ((algebraMap A E).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower k P E := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap A E (algebraMap k A r) = algebraMap A E (g (algebraMap k P r))
    rw [g.commutes])
  let K := FractionRing P
  let a : P →ₐ[k] E := (IsScalarTower.toAlgHom k A E).comp g
  let q : K →ₐ[k] E := IsFractionRing.liftAlgHom (K := K) (g := a)
    ((IsFractionRing.injective A E).comp hinj)
  have hq (r : P) : q (algebraMap P K r) = algebraMap A E (g r) := by
    change IsFractionRing.lift (g := a.toRingHom)
      ((IsFractionRing.injective A E).comp hinj) (algebraMap P K r) = _
    exact IsFractionRing.lift_algebraMap (K := K) (g := a.toRingHom)
      ((IsFractionRing.injective A E).comp hinj) r
  let : Algebra K E := q.toRingHom.toAlgebra
  let : IsScalarTower P K E := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap P E r = q (algebraMap P K r)
    exact (hq r).symm)
  let : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq (fun r => (q.commutes r).symm)
  let : Algebra.EssFiniteType A E := Algebra.EssFiniteType.of_isLocalization E
    (nonZeroDivisors A)
  let : Algebra.EssFiniteType k E := Algebra.EssFiniteType.comp k A E
  let : Algebra.EssFiniteType K E := Algebra.EssFiniteType.of_comp k K E
  let : Algebra.IsAlgebraic K E := isAlgebraic_of_isFractionRing P A K E
  let : Module.Finite K E := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let : Algebra K L := ((algebraMap E L).comp q.toRingHom).toAlgebra
  let : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite K L := Module.Finite.trans E L
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap k L r = algebraMap E L (q (algebraMap k K r))
    rw [q.commutes, IsScalarTower.algebraMap_apply k E L])
  let : Algebra P L := ((algebraMap A L).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower P K L := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap A L (g r) = algebraMap E L (q (algebraMap P K r))
    rw [hq, ← IsScalarTower.algebraMap_apply A E L])
  have hpoly := finite_mvPolynomial_closure k d K L
  have hA : Module.Finite A (integralClosure A L) :=
    (normalization_reduction P A L).2 hpoly
  let := hA
  exact ⟨hA, Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k A)
    (inferInstance : Algebra.FiniteType A (integralClosure A L)), inferInstance⟩

end P103.Ch06.AffineIntegralClosureFinite
