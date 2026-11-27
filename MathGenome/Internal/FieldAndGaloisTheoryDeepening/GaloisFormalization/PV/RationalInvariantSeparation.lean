import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.RationalInvariantSeparation
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.TorsorSpecialization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.CoordinateRationalSeparation
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Finite

import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.TorsorSpecialization
namespace GaloisFormalization.PV

open scoped Matrix TensorProduct nonZeroDivisors MatrixGroupCoordinates.Specs
open Algebra.TensorProduct (includeRight)
open CoordinateRationalSeparation.Specs (GroupCoordinateRing TotalCoordinateRing extendToTotal)

universe u v

noncomputable section

open private finiteType_of_matrixGenerated from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTensor

/-- The total quotient ring of a Picard–Vessiot ring is Artinian, by the
field and finite product decompositions for simple operator rings. -/
private theorem isArtinian_totalQuotient
    {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    [Algebra K R] {n : ℕ}
    {δ : Specs.operatorField kind K} {A : Specs.linearSystem kind K n}
    {E : Specs.operator kind R} (hk : Specs.isBaseField δ)
    (hpv : Specs.isPicardVessiotRing δ A E) : IsArtinianRing (FractionRing R) := by
  let : CharZero K := hk.1
  obtain ⟨_, hs, W, _, hW⟩ := hpv
  let : Algebra.FiniteType K R := finiteType_of_matrixGenerated W hW
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  cases kind with
  | differential =>
    let : Algebra ℚ R := Algebra.compHom R (algebraMap ℚ K)
    let : IsDomain R := (Operator.simpleDifferentialFractionField (K := FractionRing R) E hs).1
    infer_instance
  | difference =>
    let σ := Specs.toRingEquiv E
    let τ : FractionRing R ≃+* FractionRing R := IsFractionRing.ringEquivOfRingEquiv σ
    have hτ : Specs.commutes (Specs.difference σ) (Specs.difference τ)
        (algebraMap R (FractionRing R)) := by
      intro r
      exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := FractionRing R)
        (L := FractionRing R) σ r).symm
    obtain ⟨hfin, _, hdom, _, _, _, _, eQ, _⟩ :=
      simpleDifferenceFractionComponents σ τ hs hτ
    let : Finite (minimalPrimes R) := hfin
    let (i : minimalPrimes R) : IsDomain (R ⧸ i.val) := hdom i
    exact eQ.symm.isArtinianRing

/-- Scalar extension over a field preserves regularity in the ring factor. -/
private theorem includeRight_mem_nonZeroDivisors
    {C L B : Type*} [Field C] [Field L] [CommRing B] [Algebra C L] [Algebra C B]
    (d : B⁰) : (1 : L) ⊗ₜ[C] d.val ∈ (L ⊗[C] B)⁰ := by
  let m := LinearMap.mulLeft C d.val
  have hm : Function.Injective m := (isRegular_iff_mem_nonZeroDivisors.mpr d.property).left
  have ht : Function.Injective (m.lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap m hm
  have hmul : m.lTensor L = LinearMap.mulLeft C ((1 : L) ⊗ₜ[C] d.val) := by
    apply TensorProduct.ext'
    intro l b
    simp [m, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hmul] at ht
  apply mem_nonZeroDivisors_iff_left.mpr
  intro y hy
  exact ht (by simpa using hy)

/-- A finite field extension tensored with the total ring still inverts
every regular element of the base-changed ring. -/
private theorem units_in_tensor_fraction
    {K L R Q : Type*} [Field K] [Field L] [CommRing R] [CommRing Q]
    [Algebra K L] [Algebra K R] [Algebra K Q] [Algebra R Q] [IsScalarTower K R Q]
    [Module.Finite K L] [IsFractionRing R Q] [IsArtinianRing Q]
    (d : (L ⊗[K] R)⁰) :
    IsUnit (Algebra.TensorProduct.map (AlgHom.id K L)
      (IsScalarTower.toAlgHom K R Q) d.val) := by
  let j := Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K R Q)
  let : Algebra (L ⊗[K] R) (L ⊗[K] Q) := j.toAlgebra
  let : IsScalarTower L (L ⊗[K] R) (L ⊗[K] Q) :=
    IsScalarTower.of_algebraMap_eq' (by ext; simp [j, RingHom.algebraMap_toAlgebra])
  have := IsLocalization.tensorProduct_tensorProduct_right K L R⁰ Q (by
    ext r
    simp [j, RingHom.algebraMap_toAlgebra])
  have : IsArtinianRing (Q ⊗[K] L) := IsArtinianRing.of_finite Q _
  have : IsArtinianRing (L ⊗[K] Q) :=
    (Algebra.TensorProduct.comm K Q L).toRingEquiv.isArtinianRing
  apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
  exact IsLocalization.nonZeroDivisors_le_comap (R⁰.map (includeRight :
    R →ₐ[K] L ⊗[K] R)) (L ⊗[K] Q) d.property

/-- The coefficients in a basis of the left factor detect movement by maps
acting on the right factor. -/
private theorem exists_moved_coefficient
    {K L Q : Type*} [Field K] [Field L] [CommRing Q] [Algebra K L] [Algebra K Q]
    {ι : Type*} (a : ι → Q →ₐ[K] Q) (S : Set ι) (g : ι) (z : L ⊗[K] Q)
    (hfixed : ∀ h ∈ S, Algebra.TensorProduct.map (AlgHom.id K L) (a h) z = z)
    (hmoved : Algebra.TensorProduct.map (AlgHom.id K L) (a g) z ≠ z) :
    ∃ q : Q, (∀ h ∈ S, a h q = q) ∧ a g q ≠ q := by
  let b := Module.Free.chooseBasis K L
  let c := TensorProduct.equivFinsuppOfBasisLeft (N := Q) b
  have hc (h : ι) (x : L ⊗[K] Q) (i : Module.Free.ChooseBasisIndex K L) :
      c (Algebra.TensorProduct.map (AlgHom.id K L) (a h) x) i = a h (c x i) := by
    induction x using TensorProduct.inductionOn with
    | tmul l q =>
      simp [c]
    | add x y hx hy => simp [hx, hy]
  have hex : ∃ i, a g (c z i) ≠ c z i := by
    by_contra! h
    apply hmoved
    apply c.injective
    ext i
    exact (hc g z i).trans (h i)
  obtain ⟨i, hi⟩ := hex
  refine ⟨c z i, fun h hh => ?_, hi⟩
  rw [← hc, hfixed h hh]

/-- Lemma 2.6, conditional on the two full torsor-specialization statements. -/
theorem rationalInvariantSeparation_conditional
    (specialize : Specs.torsorSpecialization.{u, v, v})
    (atResidue : Specs.torsorSpecializationAtResidue.{u, v}) :
    Specs.rationalInvariantSeparation.{u, v} := by
  classical
  intro kind K _ R _ _ n δ A E Y hk hpv hY G H hH g hg
  let C := Specs.constantSubfield δ
  let : IsAlgClosed C := hk.2
  let : CharZero K := hk.1
  let : CharZero C := RingHom.charZero (Specs.constantSubfield δ).subtype
  have hG := (galoisCoordinateAlgebra δ A E Y hk hpv hY).2.1
  obtain ⟨m, hm, hL, _, _, _⟩ := atResidue δ A E Y hk hpv hY
  let : m.IsMaximal := hm
  let L := R ⧸ m
  let : Field L := Ideal.Quotient.field m
  let : Algebra K L := inferInstanceAs (Algebra K (R ⧸ m))
  let : Module.Finite K L := hL
  let : Algebra C L := Algebra.compHom L (Specs.constantSubfield δ).subtype
  let B := GroupCoordinateRing G
  let : CommRing B := inferInstanceAs (CommRing (GroupCoordinateRing G))
  let : Algebra C B := inferInstanceAs (Algebra C (GroupCoordinateRing G))
  let V := L ⊗[C] B
  let : CommRing V := Algebra.TensorProduct.instCommRing
  let : Algebra C V := Algebra.TensorProduct.leftAlgebra
  let : Algebra L V := Algebra.TensorProduct.leftAlgebra
  let S := L ⊗[K] R
  let : CommRing S := Algebra.TensorProduct.instCommRing
  let : Algebra L S := Algebra.TensorProduct.leftAlgebra
  let Q := FractionRing R
  let : IsArtinianRing Q := isArtinian_totalQuotient hk hpv
  obtain ⟨eₐ, τ, _, hτ, he⟩ :=
    specialize δ A E Y hk hpv hY (Ideal.Quotient.mkₐ K m)
  change V ≃ₐ[L] S at eₐ
  let e : V ≃+* S := eₐ.toRingEquiv
  obtain ⟨_, _, _, _, _, d, r, _, _, _, _, _, _, _, _, _, _, hf⟩ :=
    CoordinateRationalSeparation.exists_coordinateRationalSeparator G hG H hH g hg τ hτ
  let j := Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K R Q)
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (IsScalarTower.toAlgHom K R Q).toLinearMap (IsFractionRing.injective R Q)
  let i : B →ₐ[C] V := includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (algebraMap C L).injective
  let s : B →+* L ⊗[K] Q := j.toRingHom.comp (e.toRingHom.comp i.toRingHom)
  have hs : Function.Injective s := hj.comp (e.injective.comp hi)
  have hu (d : B⁰) : IsUnit (s d.val) := by
    have hd := includeRight_mem_nonZeroDivisors (C := C) (L := L) d
    let d' : (L ⊗[K] R)⁰ :=
      ⟨e (i d.val), (Operator.ringEquiv_mem_nonZeroDivisors_iff e (i d.val)).2 hd⟩
    exact units_in_tensor_fraction d'
  let f : TotalCoordinateRing G →+* L ⊗[K] Q := IsLocalization.lift hu
  have hfinj : Function.Injective f := (IsLocalization.lift_injective_iff hu).2
    (fun a b => ⟨fun h => congrArg s (IsFractionRing.injective B _ h),
      fun h => congrArg (algebraMap B (TotalCoordinateRing G)) (hs h)⟩)
  let action (x : G) : Q ≃ₐ[K] Q :=
    IsFractionRing.algEquivOfAlgEquiv (matrixAutomorphism δ E Y x).val
  have ha (x : G) (q : Q) : action x q = matrixFractionAutomorphism δ E Y x q := rfl
  let T (x : G) := Algebra.TensorProduct.map (AlgHom.id K L) (action x).toAlgHom
  have hcomm (x : G) :
      (T x).toRingHom.comp j.toRingHom =
        j.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id K L)
          (matrixAutomorphism δ E Y x).val.toAlgHom).toRingHom := by
    have hMaps : (T x).comp j = j.comp (Algebra.TensorProduct.map (AlgHom.id K L)
        (matrixAutomorphism δ E Y x).val.toAlgHom) := by
      apply Algebra.TensorProduct.ext'
      intro l r
      simp [T, j, action]
    exact congrArg AlgHom.toRingHom hMaps
  have htransport (x : G) :
      (T x).toRingHom.comp f = f.comp (extendToTotal (τ x)).toRingHom := by
    apply IsLocalization.ringHom_ext B⁰
    apply RingHom.ext
    intro b
    change T x (f (algebraMap B (TotalCoordinateRing G) b)) =
      f (extendToTotal (τ x) (algebraMap B (TotalCoordinateRing G) b))
    have hmap (b : B) : f (algebraMap B (TotalCoordinateRing G) b) = s b :=
      IsLocalization.lift_eq hu b
    have hτmap : extendToTotal (τ x) (algebraMap B (TotalCoordinateRing G) b) =
        algebraMap B (TotalCoordinateRing G) (τ x b) :=
      IsFractionRing.ringEquivOfRingEquiv_algebraMap (τ x).toRingEquiv b
    rw [hτmap, hmap, hmap]
    change T x (j (e (i b))) = j (e (i (τ x b)))
    have h := DFunLike.congr_fun (hcomm x) (e (i b))
    exact h.trans (congrArg j (he x 1 b).symm)
  let z := IsLocalization.mk' (TotalCoordinateRing G) r d
  obtain ⟨q, hq, hqg⟩ := exists_moved_coefficient
    (fun x : G => (action x).toAlgHom) (H : Set G) g (f z)
    (fun h hh => (DFunLike.congr_fun (htransport h) z).trans
      (congrArg f (hf.1 ⟨h, hh⟩)))
    (fun h => hf.2 (hfinj ((DFunLike.congr_fun (htransport g) z).symm.trans h)))
  exact ⟨q, fun h => (ha h.val q).symm.trans (hq h.val h.property),
    fun h => hqg ((ha g q).trans h)⟩

end

end GaloisFormalization.PV

universe v8_closure_c3e7434750dfa48c_u0 v8_closure_c3e7434750dfa48c_u1
theorem _root_.«GaloisFormalization».«PV».«rationalInvariantSeparation» : _root_.«GaloisFormalization».«PV».«Specs».«rationalInvariantSeparation».{v8_closure_c3e7434750dfa48c_u0, v8_closure_c3e7434750dfa48c_u1} :=
  @_root_.«GaloisFormalization».«PV».«rationalInvariantSeparation_conditional».{v8_closure_c3e7434750dfa48c_u0, v8_closure_c3e7434750dfa48c_u1} (@_root_.«GaloisFormalization».«PV».«torsorSpecialization».{v8_closure_c3e7434750dfa48c_u0, v8_closure_c3e7434750dfa48c_u1, v8_closure_c3e7434750dfa48c_u1}) (@_root_.«GaloisFormalization».«PV».«torsorSpecializationAtResidue».{v8_closure_c3e7434750dfa48c_u0, v8_closure_c3e7434750dfa48c_u1})
