import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SplitQuotient
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Classification.IntegralRootCoordinates

open LinearAlgebraicGroups.Specs
open Specs.IntegralRootCoordinates
open IntegralCentralQuotient (IntegralRing HopfSpectrum spectrumOfHopfHom spectrumOfAlgHom
  RootScalarAction)
open Specs.Pinning (BasedRootDatum BasedIso SplitBorelPair AttachedDatum RootCoordinate RootVector)
open CharacterDescent (Character)
open Specs.RootGroups (AdditiveLine IsRootSubgroup HasScalarAction rootPoint)
open RootData.RootGroups (rootSubgroups additivePoints)

noncomputable section

set_option maxHeartbeats 800000

private def characterEquiv {D E : BasedRootDatum.{u}} (e : BasedIso D E) :
    Multiplicative D.X ≃* Multiplicative E.X :=
  e.val.weightEquiv.toAddEquiv.toMultiplicative

private theorem characterEquiv_root {D E : BasedRootDatum.{u}} (e : BasedIso D E) (i : D.I) :
    characterEquiv e (Multiplicative.ofAdd (D.datum.root i)) =
      Multiplicative.ofAdd (E.datum.root (e.val.indexEquiv i)) := by
  exact RootPairing.Hom.root_weightMap_apply D.datum E.datum i e.val.toHom

private def attachedCharacterEquiv {D : BasedRootDatum.{u}} {k : Type u} [Field k]
    {P : SplitBorelPair k} {A : AttachedDatum P} (d : BasedIso D A.toBased) :
    Multiplicative D.X ≃* Character P.T.group :=
  d.val.weightEquiv.toAddEquiv.toMultiplicative

section BialgebraExtension

variable {R K B C : Type*} [CommRing R] [CommRing K] [CommRing B] [CommRing C] [Algebra R K]

/-- Base change on the two factors of the comultiplication is injective for
a flat underlying module and an injective base-ring map. -/
private def extendTensorSquare (R K B : Type*) [CommRing R] [CommRing K] [CommRing B]
    [Algebra R K] [Algebra R B] :
    B ⊗[R] B →ₗ[R] (K ⊗[R] B) ⊗[K] (K ⊗[R] B) :=
  ((TensorProduct.AlgebraTensorModule.distribBaseChange R K B B).restrictScalars R).toLinearMap ∘ₗ
    (Algebra.TensorProduct.includeRight : B ⊗[R] B →ₐ[R] K ⊗[R] (B ⊗[R] B)).toLinearMap

@[simp] private theorem extendTensorSquare_tmul [Algebra R B] (b b' : B) :
    extendTensorSquare R K B (b ⊗ₜ[R] b') =
      ((1 : K) ⊗ₜ[R] b) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b') :=
  TensorProduct.AlgebraTensorModule.distribBaseChange_tmul R K b b' 1

private theorem extendTensorSquare_comul [Bialgebra R B] (b : B) :
    extendTensorSquare R K B (Bialgebra.comulAlgHom R B b) =
      Bialgebra.comulAlgHom K (K ⊗[R] B) ((1 : K) ⊗ₜ[R] b) := by
  let p : B →ₐ[R] (K ⊗[R] B) := Algebra.TensorProduct.includeRight
  let η : R →+* K := algebraMap R K
  have hp : p.toRingHom.comp (algebraMap R B) = (algebraMap K (K ⊗[R] B)).comp η := by
    ext r
    exact (p.commutes r).trans (IsScalarTower.algebraMap_apply R K (K ⊗[R] B) r)
  have hb := DFunLike.congr_fun (Bialgebra.comul_includeRight (R := R) (A := K) (B := B)) b
  change Bialgebra.comulAlgHom K (K ⊗[R] B) ((1 : K) ⊗ₜ[R] b) =
    Algebra.TensorProduct.mapRingHom η p.toRingHom p.toRingHom hp hp
      (Bialgebra.comulAlgHom R B b) at hb
  rw [hb]
  generalize Bialgebra.comulAlgHom R B b = z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro b b'
    rw [extendTensorSquare_tmul, Algebra.TensorProduct.mapRingHom_tmul]
    rfl
  · intro z z' hz hz'
    rw [map_add, map_add, hz, hz']

end BialgebraExtension

private theorem modelSmoothAlgebra {A : Type u} [CommRing A] [HopfAlgebra IntegralRing.{u} A]
    (smooth : Smooth (HopfSpectrum IntegralRing.{u} A).X.hom) :
    Algebra.Smooth IntegralRing.{u} A := by
  have h := smooth
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap IntegralRing.{u} A))) at h
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

private theorem integralRing_isDomain : IsDomain IntegralRing.{u} :=
  (ULift.ringEquiv (R := ℤ)).toMulEquiv.isDomain ℤ

private theorem integralRing_isPrincipalIdealRing : IsPrincipalIdealRing IntegralRing.{u} :=
  IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ℤ)).symm.toRingHom
    (ULift.ringEquiv (R := ℤ)).symm.surjective

section PointGroup

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]

-- The test algebra is only a commutative algebra. Its points still form a group
-- via the antipode in the source Hopf algebra.
@[instance_reducible] private def pointConvolutionGroup {S : Type u} [CommRing S] [Algebra R S] :
    Group (WithConv (A →ₐ[R] S)) where
  inv f := toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A))
  inv_mul_cancel f := by
    change toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)) * f = 1
    have h := AlgHom.comp_convMul_distrib f.ofConv
      (toConv (HopfAlgebra.antipodeAlgHom R A)) (toConv (AlgHom.id R A))
    rw [AlgHom.antipode_id_cancel, AlgHom.convOne_def] at h
    apply WithConv.ext
    rw [AlgHom.comp_id] at h
    rw [← h]
    apply AlgHom.ext
    intro a
    exact f.ofConv.commutes _

end PointGroup

section TangentExtension

variable {R K A : Type u} [CommRing R] [CommRing K] [CommRing A]
  [Algebra R K] [HopfAlgebra R A]

/-- Extend an identity tangent vector to the scalar-extended Hopf algebra. -/
private def extendTangent (v : Tangent R A) : Tangent K (K ⊗[R] A) := by
  let p := Algebra.TensorProduct.lift (Algebra.ofId K (DualNumber K))
    ((dualCoefficients K).comp v.val) (fun _ _ => Commute.all _ _)
  refine ⟨p, AlgHom.ext fun a => ?_⟩
  refine TensorProduct.inductionOn a ?_ ?_
  · intro k b
    change (TrivSqZeroExt.fstHom K K K) (p (k ⊗ₜ[R] b)) =
      Bialgebra.counitAlgHom K (K ⊗[R] A) (k ⊗ₜ[R] b)
    have hb : (v.val b).fst = Bialgebra.counitAlgHom R A b :=
      DFunLike.congr_fun v.property b
    rw [Bialgebra.TensorProduct.counitAlgHom_def]
    simp only [p, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, map_mul,
      Algebra.TensorProduct.map_tmul]
    change k * algebraMap R K (v.val b).fst =
      Algebra.TensorProduct.rid R K K
        ((Bialgebra.counitAlgHom K K k) ⊗ₜ[R] (Bialgebra.counitAlgHom R A b))
    rw [Algebra.TensorProduct.rid_tmul, hb, Algebra.smul_def, mul_comm]
    rfl
  · intro a b ha hb
    rw [map_add, map_add, ha, hb]

private theorem extendTangent_snd (v : Tangent R A) (a : A) :
    ((extendTangent (K := K) v).val ((1 : K) ⊗ₜ[R] a)).snd =
      algebraMap R K (v.val a).snd := by
  unfold extendTangent
  simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply]
  rfl

private theorem extendTangent_has_nonzero_coefficient (v : Tangent R A)
    (h : ∃ a, (v.val a).snd ≠ 0) (hK : Function.Injective (algebraMap R K)) :
    ∃ a : K ⊗[R] A, ((extendTangent (K := K) v).val a).snd ≠ 0 := by
  obtain ⟨a, ha⟩ := h
  refine ⟨1 ⊗ₜ[R] a, ?_⟩
  rw [extendTangent_snd]
  exact fun hz => ha (hK (hz.trans (map_zero _).symm))

private theorem integralRing_algebraMap_injective (k : Type u) [Field k] [CharZero k]
    [Algebra IntegralRing.{u} k] : Function.Injective (algebraMap IntegralRing.{u} k) := by
  have h (x : IntegralRing.{u}) : algebraMap IntegralRing.{u} k x = Int.cast x.down := by
    obtain ⟨n⟩ := x
    exact map_intCast (algebraMap IntegralRing.{u} k) n
  intro x y eq
  apply ULift.ext
  rw [h, h] at eq
  exact Int.cast_injective eq

end TangentExtension

section AffinePoints

set_option backward.isDefEq.respectTransparency false

open WithConv
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open IntegralCentralQuotient (spectrumOfAlgHom)
open AdjointRepresentation (GroupPoints)

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]

private theorem spectrumOfAlgHom_comp [Algebra R A] [Algebra R B] [Algebra R C]
    (g : B →ₐ[R] C) (f : A →ₐ[R] B) :
    spectrumOfAlgHom (g.comp f) = spectrumOfAlgHom g ≫ spectrumOfAlgHom f := by
  rw [← Functor.map_comp]
  rfl

/-- The Laurent generator evaluates under the point corresponding to an algebra map
by applying that map to the character monomial. -/
private theorem characterValue_spectrum {k : Type u} [Field k]
    [HopfAlgebra k A] [Algebra k B] (χ : Character (HopfSpectrum k A))
    (t : A →ₐ[k] B) :
    CharacterPairing.characterValue χ (CommAlgCat.of k B) (spectrumOfAlgHom t) =
      t (characterMonomial χ) := by
  let F := algSpec (CommRingCat.of k)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let L := CommAlgCat.of k (MonoidAlgebra k DiagonalizableGroups.IntegerCharacters)
  let a := CommAlgCat.of k A
  let b := CommAlgCat.of k B
  let q : op a ⟶ op L := ff.preimage χ.hom.hom
  have h : F.map q = χ.hom.hom := ff.map_preimage _
  have heq : ff.preimage (spectrumOfAlgHom t ≫ χ.hom.hom) =
      (CommAlgCat.ofHom t : a ⟶ b).op ≫ q := by
    apply ff.map_injective
    change F.map (ff.preimage (spectrumOfAlgHom t ≫ χ.hom.hom)) =
      F.map ((CommAlgCat.ofHom t : a ⟶ b).op ≫ q)
    rw [ff.map_preimage, F.map_comp, h]
  change ((ff.preimage (spectrumOfAlgHom t ≫ χ.hom.hom)).unop).hom _ = _
  rw [heq]
  rfl

/-- Vanishing on the identity tangent is detected on its algebra-valued point. -/
private def tangentPoint {k : Type u} [Field k] [HopfAlgebra k A]
    {G : GroupScheme k} (e : HopfSpectrum k A ≅ G) (p : Tangent k A) : Lie k G := by
  refine ⟨spectrumOfAlgHom p.val ≫ e.hom.hom.hom, ?_⟩
  change mapPoints (dualReduction k) (spectrumOfAlgHom p.val ≫ e.hom.hom.hom) = 1
  rw [show mapPoints (dualReduction k) (spectrumOfAlgHom p.val ≫ e.hom.hom.hom) =
    spectrumOfAlgHom ((TrivSqZeroExt.fstHom k k k).comp p.val) ≫ e.hom.hom.hom by
      rw [spectrumOfAlgHom_comp]; rfl]
  rw [p.property]
  change Spec.mapMulEquiv (1 : WithConv (A →ₐ[k] k)) ≫ e.hom.hom.hom = 1
  rw [map_one]
  exact MonObj.one_comp e.hom.hom.hom

private theorem tangentPoint_ne_zero {k : Type u} [Field k] [HopfAlgebra k A]
    {G : GroupScheme k} (e : HopfSpectrum k A ≅ G) (p : Tangent k A)
    (hp : ∃ a : A, (p.val a).snd ≠ 0) : tangentPoint e p ≠ 0 := by
  intro h
  have eq := congrArg (fun v : Lie k G => v.toMul.val) h
  change spectrumOfAlgHom p.val ≫ e.hom.hom.hom = 1 at eq
  have ho : (1 : (testSpec k).obj (op (CommAlgCat.of k (DualNumber k))) ⟶
      (HopfSpectrum k A).X) ≫ e.hom.hom.hom = 1 := MonObj.one_comp e.hom.hom.hom
  have hh := (cancel_mono e.hom.hom.hom).mp (eq.trans ho.symm)
  have hval : toConv p.val = (1 : WithConv (A →ₐ[k] DualNumber k)) := by
    apply Spec.mapMulEquiv.injective
    rw [map_one]
    exact hh
  obtain ⟨a, ha⟩ := hp
  apply ha
  have heq := congrArg (fun f : WithConv (A →ₐ[k] DualNumber k) => (f.ofConv a).snd) hval
  exact heq.trans (map_zero (algebraMap k k))

end AffinePoints

section ExtendPoint

open WithConv

variable {R K A S : Type u} [CommRing R] [CommRing K] [CommRing A] [CommRing S]
  [Algebra R K] [HopfAlgebra R A] [Algebra K S] [Algebra R S] [IsScalarTower R K S]

/-- Restrict a point of a scalar-extended algebra to the original algebra. -/
private abbrev restrictPoint : (K ⊗[R] A →ₐ[K] S) ≃ (A →ₐ[R] S) :=
  (AlgHom.liftEquiv R K A S).symm

private theorem restrictPoint_mul (p q : WithConv (K ⊗[R] A →ₐ[K] S)) :
    toConv (restrictPoint (p * q).ofConv) =
      toConv (restrictPoint p.ofConv) * toConv (restrictPoint q.ofConv) := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  change (p * q).ofConv ((1 : K) ⊗ₜ[R] a) =
    (toConv (restrictPoint p.ofConv) * toConv (restrictPoint q.ofConv)).ofConv a
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  change (Algebra.TensorProduct.lift p.ofConv q.ofConv _) (Bialgebra.comulAlgHom K (K ⊗[R] A)
      ((1 : K) ⊗ₜ[R] a)) =
    (Algebra.TensorProduct.lift (restrictPoint p.ofConv) (restrictPoint q.ofConv) _)
      (Bialgebra.comulAlgHom R A a)
  rw [← extendTensorSquare_comul]
  generalize Bialgebra.comulAlgHom R A a = z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro b c
    rw [extendTensorSquare_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  · intro x y hx hy
    rw [map_add, map_add, map_add, hx, hy]

private theorem restrictPoint_one :
    toConv (restrictPoint (K := K) (1 : WithConv (K ⊗[R] A →ₐ[K] S)).ofConv) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  simp only [AlgHom.convOne_def, AlgHom.comp_apply, AlgHom.liftEquiv_symm_apply]
  have e := DFunLike.congr_fun
    (Bialgebra.counitAlgHom_comp_includeRight (R := R) (A := K) (B := A)) a
  change Bialgebra.counitAlgHom K (K ⊗[R] A) ((1 : K) ⊗ₜ[R] a) =
    algebraMap R K (Bialgebra.counitAlgHom R A a) at e
  exact congrArg (algebraMap K S) e |>.trans (IsScalarTower.algebraMap_apply R K S _).symm

private theorem restrictPoint_extendedTangent (v : Tangent R A) :
    restrictPoint (K := K) (S := DualNumber S)
      ((dualCoefficients S).comp (extendTangent (K := K) v).val) =
        (dualCoefficients S).comp v.val := by
  apply AlgHom.ext
  intro a
  change dualCoefficients S ((extendTangent (K := K) v).val ((1 : K) ⊗ₜ[R] a)) =
    dualCoefficients S (v.val a)
  simp only [extendTangent, Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply]
  apply TrivSqZeroExt.ext <;> exact (IsScalarTower.algebraMap_apply R K S _).symm

end ExtendPoint

section ExtendedWeights

open WithConv
open AdjointRepresentation (scale)
attribute [local instance] pointConvolutionGroup

variable {R K A : Type u} [CommRing R] [Field K] [CommRing A]
  [Algebra R K] [HopfAlgebra R A]

private def restrictPointMonoidHom {S : Type u} [CommRing S] [Algebra K S] [Algebra R S]
    [IsScalarTower R K S] :
    WithConv (K ⊗[R] A →ₐ[K] S) →* WithConv (A →ₐ[R] S) where
  toFun p := toConv (restrictPoint p.ofConv)
  map_one' := restrictPoint_one
  map_mul' := restrictPoint_mul

private theorem extendTangent_weight {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (α : X) (v : Tangent R A) (hv : HasWeight t α v)
    (S : CommAlgCat.{u} K) (s : K ⊗[R] MonoidAlgebra R X →ₐ[K] S) :
    let tK := Bialgebra.TensorProduct.map (BialgHom.id K K) t
    let g := toConv ((TrivSqZeroExt.inlAlgHom K S S).comp (s.comp tK.toAlgHom))
    let p := (dualCoefficients S).comp (extendTangent (K := K) v).val
    let c := s ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
    g * toConv p * g⁻¹ = toConv ((scale S c).hom.comp p) := by
  dsimp only
  letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let s₀ : MonoidAlgebra R X →ₐ[R] S := restrictPoint s
  let j := restrictPointMonoidHom (R := R) (K := K) (A := A) (S := DualNumber S)
  have hj : Function.Injective j := fun p q h =>
    WithConv.ofConv_injective (restrictPoint.injective (congrArg WithConv.ofConv h))
  let tK := Bialgebra.TensorProduct.map (BialgHom.id K K) t
  let g := toConv ((TrivSqZeroExt.inlAlgHom K S S).comp (s.comp tK.toAlgHom))
  let p := (dualCoefficients S).comp (extendTangent (K := K) v).val
  let c := s ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
  change g * toConv p * g⁻¹ = toConv ((scale S c).hom.comp p)
  apply hj
  rw [map_mul, map_mul, map_inv]
  have hg : j g = toConv ((TrivSqZeroExt.inlAlgHom R S S).comp (s₀.comp t.toAlgHom)) := by
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    change (TrivSqZeroExt.inlAlgHom K S S) (s (tK ((1 : K) ⊗ₜ[R] a))) =
      (TrivSqZeroExt.inlAlgHom R S S) (s₀ (t a))
    rw [Bialgebra.TensorProduct.map_tmul]
    rfl
  have hp : j (toConv p) = toConv ((dualCoefficients S).comp v.val) :=
    congrArg toConv (restrictPoint_extendedTangent v)
  have hsc : j (toConv ((scale S c).hom.comp p)) =
      toConv (((TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))).restrictScalars R).comp
        ((dualCoefficients S).comp v.val)) := by
    apply WithConv.ext
    have heq := restrictPoint_extendedTangent (K := K) (S := S) v
    apply AlgHom.ext
    intro a
    have ha := DFunLike.congr_fun heq a
    change (scale S c).hom (p ((1 : K) ⊗ₜ[R] a)) =
      (TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))) (dualCoefficients S (v.val a))
    change p ((1 : K) ⊗ₜ[R] a) = dualCoefficients S (v.val a) at ha
    rw [ha]
    apply TrivSqZeroExt.ext
    · exact (TrivSqZeroExt.fst_map _ _).symm
    · change c * _ = _
      simp only [TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  rw [hg, hp, hsc]
  exact hv (CommAlgCat.of R S) s₀

end ExtendedWeights

section FibrePinning

set_option backward.isDefEq.respectTransparency false

open WithConv
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open IntegralCentralQuotient (spectrumOfAlgHom)
open AdjointRepresentation (GroupPoints constants dualMap scale)
attribute [local instance] pointConvolutionGroup

variable {R K A : Type u} [CommRing R] [Field K] [CommRing A]
  [Algebra R K] [HopfAlgebra R A]

/-- The weight equality in coordinates is the adjoint weight equality for
the geometric fibre, with the character read on the marked torus. -/
private theorem tangentPoint_weight {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (α : X) (v : Tangent R A) (hv : HasWeight t α v)
    {G : GroupScheme K} (T : ClosedSubgroup G) (χ : Character T.group)
    (e : HopfSpectrum K (K ⊗[R] A) ≅ G)
    (s : HopfSpectrum K (K ⊗[R] MonoidAlgebra R X) ≅ T.group)
    (hT : spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id K K) t) ≫ e.hom =
      s.hom ≫ T.inclusion)
    (hχ : characterMonomial (s.hom ≫ χ) = (1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α) :
    tangentPoint e (extendTangent (K := K) v) ∈ CharacterPairing.adjointWeightVectors T χ := by
  intro S a
  let q : WithConv (K ⊗[R] MonoidAlgebra R X →ₐ[K] S) :=
    Spec.mapMulEquiv.symm (a ≫ s.inv.hom.hom)
  have hq : spectrumOfAlgHom q.ofConv ≫ s.hom.hom.hom = a := by
    change Spec.mapMulEquiv q ≫ s.hom.hom.hom = a
    rw [MulEquiv.apply_symm_apply, Category.assoc]
    have hs := congrArg (fun f : T.group ⟶ T.group => f.hom.hom) s.inv_hom_id
    rw [Grp.comp_hom_hom, Grp.id_hom_hom] at hs
    rw [hs, Category.comp_id]
  let tK := Bialgebra.TensorProduct.map (BialgHom.id K K) t
  let g := toConv ((TrivSqZeroExt.inlAlgHom K S S).comp (q.ofConv.comp tK.toAlgHom))
  let p := (dualCoefficients S).comp (extendTangent (K := K) v).val
  let c := q.ofConv ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
  have hc : CharacterPairing.characterValue χ S a = c := by
    rw [← hq]
    have hh : CharacterPairing.characterValue χ S
        (spectrumOfAlgHom q.ofConv ≫ s.hom.hom.hom) =
      CharacterPairing.characterValue (s.hom ≫ χ) S (spectrumOfAlgHom q.ofConv) := by
      unfold CharacterPairing.characterValue
      rw [Category.assoc]
      rfl
    rw [hh]
    exact (characterValue_spectrum (s.hom ≫ χ) q.ofConv).trans (congrArg q.ofConv hχ)
  let W := CommAlgCat.of K (DualNumber S)
  let m : WithConv (K ⊗[R] A →ₐ[K] W) →* GroupPoints G W :=
    (((groupPointsFunctor K).map e.hom).app W).hom.comp Spec.mapMulEquiv.toMonoidHom
  have hg : m g = mapPoints (constants S) (a ≫ T.inclusion.hom.hom) := by
    change spectrumOfAlgHom ((TrivSqZeroExt.inlAlgHom K S S).comp (q.ofConv.comp tK.toAlgHom)) ≫
      e.hom.hom.hom = spectrumOfAlgHom (TrivSqZeroExt.inlAlgHom K S S) ≫
        (a ≫ T.inclusion.hom.hom)
    rw [spectrumOfAlgHom_comp, spectrumOfAlgHom_comp, Category.assoc, Category.assoc]
    change _ ≫ (_ ≫ (spectrumOfHopfHom tK).hom.hom ≫ e.hom.hom.hom) = _
    rw [← Grp.comp_hom_hom, hT, Grp.comp_hom_hom]
    rw [← Category.assoc (spectrumOfAlgHom q.ofConv), hq]
  have hp : m (toConv p) =
      mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId K S)))
        (tangentPoint e (extendTangent (K := K) v)).toMul.val := by
    change spectrumOfAlgHom p ≫ e.hom.hom.hom =
      spectrumOfAlgHom (dualCoefficients (R := K) S) ≫
        (spectrumOfAlgHom (extendTangent (K := K) v).val ≫ e.hom.hom.hom)
    rw [← Category.assoc, ← spectrumOfAlgHom_comp]
  have hscale : m (toConv ((scale S c).hom.comp p)) = mapPoints (scale S c) (m (toConv p)) := by
    change spectrumOfAlgHom ((scale S c).hom.comp p) ≫ e.hom.hom.hom =
      spectrumOfAlgHom (scale S c).hom ≫ (spectrumOfAlgHom p ≫ e.hom.hom.hom)
    rw [spectrumOfAlgHom_comp, Category.assoc]
  have he := congrArg m (extendTangent_weight t α v hv S q.ofConv)
  change m (g * toConv p * g⁻¹) = m (toConv ((scale S c).hom.comp p)) at he
  rw [map_mul, map_mul, map_inv, hscale, hg, hp] at he
  dsimp only
  rw [hc]
  exact he

end FibrePinning

section ModelFibre

open IntegralCentralQuotient (spectrumOfAlgHom)
set_option maxHeartbeats 400000

-- Use the action associated to the given algebra in each tensor product.
local instance (priority := 2000) integralAlgebraModule {A : Type u} [CommRing A]
    [Algebra IntegralRing.{u} A] : Module IntegralRing.{u} A := Algebra.toModule
set_option backward.isDefEq.respectTransparency false

open WithConv

/-- A nontrivial non-root character of the integral split torus has no integral
tangent vector with a nonzero dual-number coefficient. -/
private theorem missingWeight_tangent_snd_eq_zero {D : BasedRootDatum.{u}}
    {A : Type u} [CommRing A] [HopfAlgebra IntegralRing.{u} A]
    (t : A →ₐc[IntegralRing.{u}] MonoidAlgebra IntegralRing.{u} (Multiplicative D.X))
    (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] [Algebra IntegralRing.{u} K]
    (fibre : HasFibreDatum D t K)
    (χ : Multiplicative D.X) (hχ : χ ≠ 1)
    (hroot : ∀ i, χ ≠ Multiplicative.ofAdd (D.datum.root i))
    (v : Tangent IntegralRing.{u} A) (hv : HasWeight t χ v) :
    ∀ a, (v.val a).snd = 0 := by
  intro a
  by_contra ha
  obtain ⟨Q, e, s, E, d, ht, hmon⟩ := fibre
  let := E.comm
  let ψ := attachedCharacterEquiv d χ
  let w := tangentPoint e (extendTangent (K := K) v)
  have hψ : ψ ≠ 1 := fun h => hχ ((attachedCharacterEquiv d).injective
    (h.trans (map_one (attachedCharacterEquiv d)).symm))
  have hw : w ∈ CharacterPairing.adjointWeightVectors Q.T ψ :=
    tangentPoint_weight t χ v hv Q.T ψ e s ht (hmon χ.toAdd)
  have hwn : w ≠ 0 := tangentPoint_ne_zero e _
    (extendTangent_has_nonzero_coefficient v ⟨a, ha⟩ (integralRing_algebraMap_injective K))
  let α : AbstractPairing.Root Q.T := ⟨ψ, hψ, w, hw, hwn⟩
  let i := d.val.indexEquiv.symm α
  have hi : d.val.indexEquiv i = α := d.val.indexEquiv.apply_symm_apply α
  have he : attachedCharacterEquiv d (Multiplicative.ofAdd (D.datum.root i)) = α.val :=
    (characterEquiv_root d i).trans ((congrArg Multiplicative.ofAdd
      (E.datum.root_eq (d.val.indexEquiv i))).trans (congrArg Subtype.val hi))
  exact hroot i ((attachedCharacterEquiv d).injective he.symm)

end ModelFibre

section AugmentationCotangent

variable {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The conormal sequence of the augmentation is split by the structural map.
The last term is the module of differentials of the base over itself. -/
private theorem augmentedCotangentEquiv (ε : A →ₐ[R] R) :
    let : Algebra A R := ε.toRingHom.toAlgebra
    ∃ e : (RingHom.ker ε.toRingHom).Cotangent ≃ₗ[R] R ⊗[A] KaehlerDifferential R A,
      ∀ a : RingHom.ker ε.toRingHom,
        e (Ideal.toCotangent _ a) = 1 ⊗ₜ[A] KaehlerDifferential.D R A a.val := by
  let : Algebra A R := ε.toRingHom.toAlgebra
  have hs : Function.RightInverse (Algebra.ofId R A) (algebraMap A R) :=
    fun a => ε.commutes a
  have h := hs.surjective
  obtain ⟨_, _, _, _, _, hinj, hex, _, _, _⟩ :=
    AdvCommAlg.Differentials.split_quotient R A R h (Algebra.ofId R A) hs
  let : Subsingleton (KaehlerDifferential R R) := KaehlerDifferential.subsingleton_of_surjective R R (by simpa using Function.surjective_id)
  have hsurj : Function.Surjective (AdvCommAlg.Differentials.conormalMap R A R h) := by
    intro z
    exact (hex z).mp (Subsingleton.elim _ _)
  let c := LinearEquiv.ofBijective (AdvCommAlg.Differentials.conormalMap R A R h) ⟨hinj, hsurj⟩
  let P := Specs.AdvCommAlg.Differentials.conormalExtension R A R h
  let q := P.cotangentEquivCotangentKer.restrictScalars R
  refine ⟨q.symm.trans c, ?_⟩
  exact AdvCommAlg.Differentials.conormalMap_apply R A R h

private theorem augmentedCotangent_projective (ε : A →ₐ[R] R) [Algebra.FormallySmooth R A] :
    Module.Projective R (RingHom.ker ε.toRingHom).Cotangent := by
  let : Algebra A R := ε.toRingHom.toAlgebra
  obtain ⟨e, _⟩ := augmentedCotangentEquiv ε
  exact Module.Projective.of_equiv' e.symm

private theorem augmentedCotangent_finite (ε : A →ₐ[R] R) [Algebra.FiniteType R A] :
    Module.Finite R (RingHom.ker ε.toRingHom).Cotangent := by
  let : Algebra A R := ε.toRingHom.toAlgebra
  obtain ⟨e, _⟩ := augmentedCotangentEquiv ε
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- The augmentation cotangent of a smooth finite-type algebra over a PID is finite free. -/
private theorem augmentedCotangent_free (ε : A →ₐ[R] R) [IsDomain R]
    [IsPrincipalIdealRing R] [Algebra.Smooth R A] :
    Module.Free R (RingHom.ker ε.toRingHom).Cotangent := by
  let : Module.Projective R (RingHom.ker ε.toRingHom).Cotangent :=
    augmentedCotangent_projective ε
  let : Module.Finite R (RingHom.ker ε.toRingHom).Cotangent :=
    augmentedCotangent_finite ε
  exact Module.free_of_finite_type_torsion_free'

/-- A derivation with respect to the augmentation determines an identity tangent point. -/
private def tangentFromDerivative (ε : A →ₐ[R] R)
    (d : A →ₗ[R] R)
    (hconst : ∀ r, d (algebraMap R A r) = 0)
    (hmul : ∀ a b, d (a * b) = ε a * d b + ε b * d a) : A →ₐ[R] DualNumber R where
  toFun a := (ε a, d a)
  map_zero' := TrivSqZeroExt.ext (map_zero ε) (map_zero d)
  map_one' := TrivSqZeroExt.ext (map_one ε) (by
    change d 1 = 0
    simpa only [map_one] using hconst 1)
  map_add' a b := TrivSqZeroExt.ext (map_add ε a b) (map_add d a b)
  map_mul' a b := TrivSqZeroExt.ext (map_mul ε a b) (by
    change d (a * b) = ε a * d b + d a * ε b
    rw [hmul, mul_comm (ε b)])
  commutes' r := TrivSqZeroExt.ext (ε.commutes r) (hconst r)

/-- Every functional on the cotangent module gives a tangent lift at the augmentation. -/
private theorem lift_cotangentFunctional (ε : A →ₐ[R] R)
    (ℓ : (RingHom.ker ε.toRingHom).Cotangent →ₗ[R] R) :
    ∃ v : A →ₐ[R] DualNumber R, (TrivSqZeroExt.fstHom R R R).comp v = ε ∧
      ∀ a : RingHom.ker ε.toRingHom, (v a.val).snd = ℓ (Ideal.toCotangent _ a) := by
  let : Algebra A R := ε.toRingHom.toAlgebra
  obtain ⟨e, he⟩ := augmentedCotangentEquiv ε
  let L := ℓ.comp e.symm.toLinearMap
  let d := (L.restrictScalars R).comp
    ((TensorProduct.mk A R (KaehlerDifferential R A) 1).restrictScalars R) ∘ₗ
    (KaehlerDifferential.D R A).toLinearMap
  have hsmul (a b : A) :
      L ((a • (1 : R)) ⊗ₜ[A] KaehlerDifferential.D R A b) =
        ε a * L (1 ⊗ₜ[A] KaehlerDifferential.D R A b) := by
    have h : a • (1 : R) = ε a • (1 : R) := by
      rw [Algebra.smul_def]
      rfl
    rw [h, ← TensorProduct.smul_tmul', map_smul, smul_eq_mul]
  let v := tangentFromDerivative ε d (fun r => by
    change L (1 ⊗ₜ[A] KaehlerDifferential.D R A (algebraMap R A r)) = 0
    rw [Derivation.map_algebraMap, TensorProduct.tmul_zero, map_zero]) (fun a b => by
    change L (1 ⊗ₜ[A] KaehlerDifferential.D R A (a * b)) =
      ε a * L (1 ⊗ₜ[A] KaehlerDifferential.D R A b) +
        ε b * L (1 ⊗ₜ[A] KaehlerDifferential.D R A a)
    rw [Derivation.leibniz, TensorProduct.tmul_add, map_add,
      ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, hsmul, hsmul])
  refine ⟨v, AlgHom.ext fun _ => rfl, fun a => ?_⟩
  change L (1 ⊗ₜ[A] KaehlerDifferential.D R A a.val) = _
  rw [← he]
  exact congrArg ℓ (e.symm_apply_apply _)

/-- The coefficients of all dual-number lifts detect the augmentation cotangent classes. -/
private theorem mem_augmentationSquare_of_tangents (ε : A →ₐ[R] R)
    [Module.Free R (RingHom.ker ε.toRingHom).Cotangent]
    (a : RingHom.ker ε.toRingHom)
    (h : ∀ v : A →ₐ[R] DualNumber R,
      (TrivSqZeroExt.fstHom R R R).comp v = ε → (v a.val).snd = 0) :
    a.val ∈ (RingHom.ker ε.toRingHom) ^ 2 := by
  let b := Module.Free.chooseBasis R (RingHom.ker ε.toRingHom).Cotangent
  apply ((RingHom.ker ε.toRingHom).toCotangent_eq_zero a).mp
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨v, hv, he⟩ := lift_cotangentFunctional ε (b.coord i)
  exact (he a).symm.trans (h v hv)

end AugmentationCotangent

section PrimitiveTangents

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- Dividing the coefficients of a nonzero tangent by the generator of
their image ideal produces a tangent with a coefficient equal to one. -/
private theorem primitiveTangent [IsDomain R] [IsPrincipalIdealRing R] (v : Tangent R A)
    (hv : ∃ a, (v.val a).snd ≠ 0) :
    ∃ (c : R) (w : Tangent R A), c ≠ 0 ∧
      (∀ a, (v.val a).snd = c * (w.val a).snd) ∧
      ∃ a, (w.val a).snd = 1 := by
  let D := (TrivSqZeroExt.sndHom (R := R) (M := R)).comp v.val.toLinearMap
  let I : Ideal R := LinearMap.range D
  let c := Submodule.IsPrincipal.generator I
  have hc : c ≠ 0 := by
    intro hz
    obtain ⟨a, ha⟩ := hv
    have hI : I = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hz
    have hmem : D a ∈ I := ⟨a, rfl⟩
    rw [hI] at hmem
    apply ha
    change D a = 0
    simpa using hmem
  let m := LinearMap.toSpanSingleton R R c
  have hm : Function.Injective m := fun x y h => mul_right_cancel₀ hc h
  have hI : LinearMap.range m = I :=
    (LinearMap.range_toSpanSingleton c).trans (Ideal.span_singleton_generator I)
  let e := LinearEquiv.ofInjective m hm
  let d : A →ₗ[R] R :=
    e.symm.toLinearMap.comp (D.codRestrict (LinearMap.range m) (fun a => hI ▸ ⟨a, rfl⟩))
  have hd (a : A) : c * d a = (v.val a).snd := by
    rw [mul_comm]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  let ε := Bialgebra.counitAlgHom R A
  have hfst (a : A) : (v.val a).fst = ε a := AlgHom.congr_fun v.property a
  have hconst (r : R) : d (algebraMap R A r) = 0 := by
    apply mul_left_cancel₀ hc
    rw [hd, AlgHom.commutes, mul_zero]
    rfl
  have hmul (a b : A) : d (a * b) = ε a * d b + ε b * d a := by
    apply mul_left_cancel₀ hc
    calc
      _ = (v.val (a * b)).snd := hd _
      _ = ε a * (v.val b).snd + (v.val a).snd * ε b := by
        rw [map_mul, DualNumber.snd_mul, hfst, hfst]
      _ = _ := by rw [← hd b, ← hd a]; ring
  let w : Tangent R A := ⟨tangentFromDerivative ε d hconst hmul, AlgHom.ext fun _ => rfl⟩
  refine ⟨c, w, hc, fun a => (hd a).symm, ?_⟩
  obtain ⟨a, ha⟩ : c ∈ I := Submodule.IsPrincipal.generator_mem I
  refine ⟨a, mul_left_cancel₀ hc ?_⟩
  change c * d a = c * 1
  rw [hd, mul_one]
  exact ha

end PrimitiveTangents

section PolynomialCoordinates

open Polynomial

variable {R K A : Type u} [CommRing R] [Field K] [CommRing A] [Algebra R K] [Algebra R A]

private abbrev extendPolynomial : Polynomial R →ₐ[R] Polynomial K :=
  Polynomial.mapAlgHom (Algebra.ofId R K)

/-- For an augmented algebra mapping to a root line on the generic fibre,
only the constant and linear coefficients need to be checked directly.
A higher-degree weight projection lies in the square of the augmentation
ideal, and its coefficient is a sum of products of lower-degree ones. -/
private theorem integralPolynomialCoefficients
    (ε : A →ₐ[R] R) (f : A →ₐ[R] Polynomial K)
    (h₀ : ∀ a, (f a).coeff 0 = algebraMap R K (ε a))
    (h₁ : ∀ a, (f a).coeff 1 ∈ Set.range (algebraMap R K))
    (project : ∀ a n, 2 ≤ n → ∃ b ∈ (RingHom.ker ε.toRingHom) ^ 2,
      (f b).coeff n = (f a).coeff n) :
    ∀ a n, (f a).coeff n ∈ Set.range (algebraMap R K) := by
  classical
  let S := (algebraMap R K).range
  intro a n
  change (f a).coeff n ∈ S
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn₀ : n = 0
    · subst n
      exact ⟨ε a, (h₀ a).symm⟩
    by_cases hn₁ : n = 1
    · subst n
      exact h₁ a
    obtain ⟨b, hb, hba⟩ := project a n (by omega)
    rw [← hba]
    rw [pow_two] at hb
    refine Submodule.mul_induction_on
      (M := RingHom.ker ε.toRingHom) (N := RingHom.ker ε.toRingHom) hb ?_ ?_
    · intro x hx y hy
      rw [map_mul, coeff_mul]
      apply S.sum_mem
      rintro ⟨i, j⟩ hij
      have hs := Finset.mem_antidiagonal.mp hij
      by_cases hi : i = 0
      · have hε : ε x = 0 := hx
        simp only [hi, h₀, hε, map_zero, zero_mul, S.zero_mem]
      by_cases hj : j = 0
      · have hε : ε y = 0 := hy
        simp only [hj, h₀, hε, map_zero, mul_zero, S.zero_mem]
      exact S.mul_mem (ih i (by omega) x) (ih j (by omega) y)
    · intro x y hx hy
      rw [map_add, coeff_add]
      exact S.add_mem hx hy

private theorem polynomialInRange_of_coefficients {p : Polynomial K}
    (hp : ∀ n, p.coeff n ∈ Set.range (algebraMap R K)) :
    p ∈ (extendPolynomial (R := R) (K := K)).range := by
  classical
  let P := (extendPolynomial (R := R) (K := K)).range
  have hm (n : ℕ) : monomial n (p.coeff n) ∈ P := by
    obtain ⟨r, hr⟩ := hp n
    refine ⟨monomial n r, ?_⟩
    change (Polynomial.mapAlgHom (Algebra.ofId R K)) (monomial n r) = _
    rw [Polynomial.mapAlgHom_monomial]
    exact congrArg (monomial n) hr
  change p ∈ P
  rw [← p.sum_monomial_eq]
  exact P.sum_mem fun n _ => hm n

/-- Recover the closed integral root coordinate from the polynomial
coefficient bounds and a lift of the generic coordinate parameter. -/
private theorem integralPolynomialCoordinate
    (ε : A →ₐ[R] R) (f : A →ₐ[R] Polynomial K)
    (hR : Function.Injective (algebraMap R K))
    (h₀ : ∀ a, (f a).coeff 0 = algebraMap R K (ε a))
    (h₁ : ∀ a, (f a).coeff 1 ∈ Set.range (algebraMap R K))
    (project : ∀ a n, 2 ≤ n → ∃ b ∈ (RingHom.ker ε.toRingHom) ^ 2,
      (f b).coeff n = (f a).coeff n)
    (hX : Polynomial.X ∈ f.range) :
    ∃! g : A →ₐ[R] Polynomial R, extendPolynomial.comp g = f ∧ Function.Surjective g := by
  let q : Polynomial R →ₐ[R] Polynomial K := extendPolynomial
  have hq : Function.Injective q := Polynomial.map_injective _ hR
  let e := AlgEquiv.ofInjective q hq
  have hr (a : A) : f a ∈ q.range :=
    polynomialInRange_of_coefficients (integralPolynomialCoefficients ε f h₀ h₁ project a)
  let g := e.symm.toAlgHom.comp (f.codRestrict q.range hr)
  have hg : q.comp g = f := AlgHom.ext fun a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨f a, hr a⟩)
  have hgX : Polynomial.X ∈ g.range := by
    obtain ⟨a, ha⟩ := hX
    refine ⟨a, hq ?_⟩
    exact (DFunLike.congr_fun hg a).trans (ha.trans (Polynomial.map_X _).symm)
  have hgs : Function.Surjective g := fun p => by
    suffices hmem : p ∈ g.range by exact hmem
    have hc (r : R) : Polynomial.C r ∈ g.range := g.range.algebraMap_mem r
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact g.range.add_mem hp hq
    | monomial n r =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      exact g.range.mul_mem (hc r) (g.range.pow_mem hgX n)
  exact ⟨g, ⟨hg, hgs⟩, fun g' hg' => AlgHom.ext fun a =>
    hq ((DFunLike.congr_fun hg'.1 a).trans (DFunLike.congr_fun hg a).symm)⟩

end PolynomialCoordinates

section RootWeightProjections

set_option backward.isDefEq.respectTransparency false

open WithConv
open IntegralCentralQuotient (RootScalarAction)
open Polynomial
attribute [local instance] pointConvolutionGroup

variable {R A K X : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup X]
  [Field K] [Algebra R K]

/-- The universal conjugation by the marked split torus, with the torus
coordinate in the right tensor factor. -/
private def torusConjugation (t : A →ₐc[R] MonoidAlgebra R X) :
    A →ₐ[R] A ⊗[R] MonoidAlgebra R X :=
  let g : A →ₐ[R] A ⊗[R] MonoidAlgebra R X :=
    Algebra.TensorProduct.includeRight.comp t.toAlgHom
  (toConv g * toConv (Algebra.TensorProduct.includeLeft : A →ₐ[R] _) *
    (toConv g)⁻¹).ofConv

private def tensorMonomialCoeff {V : Type u} [AddCommGroup V] [Module R V]
    (x : X) : (V ⊗[R] MonoidAlgebra R X) →ₗ[R] V :=
  (TensorProduct.rid R V).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id ((Finsupp.lapply x).comp
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap)

@[simp] private theorem tensorMonomialCoeff_tmul {V : Type u} [AddCommGroup V] [Module R V]
    [DecidableEq X] (x y : X) (v : V) :
    tensorMonomialCoeff (R := R) x (v ⊗ₜ[R] MonoidAlgebra.of R X y) =
      if x = y then v else 0 := by
  change (MonoidAlgebra.of R X y).coeff x • v = _
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
  by_cases he : x = y <;> simp [he, Ne.symm]

private theorem tensorMonomialCoeff_map {V W : Type u} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (f : V →ₗ[R] W) (x : X)
    (a : V ⊗[R] MonoidAlgebra R X) :
    tensorMonomialCoeff x (TensorProduct.map f LinearMap.id a) =
      f (tensorMonomialCoeff x a) := by
  refine TensorProduct.inductionOn a ?_ ?_
  · intro b c
    change tensorMonomialCoeff x (f b ⊗ₜ[R] c) = _
    change c.coeff x • f b = f (c.coeff x • b)
    exact (f.map_smul _ _).symm
  · intro a b ha hb
    rw [map_add, map_add, map_add, map_add, ha, hb]

private def torusWeightProjection (t : A →ₐc[R] MonoidAlgebra R X)
    (x : X) : A →ₗ[R] A :=
  (tensorMonomialCoeff x).comp (torusConjugation t).toLinearMap

open Algebra.TensorProduct (includeLeft includeRight lift)
local notation "H" => MonoidAlgebra R X

private def postcomposePoint {A S T : Type u} [CommRing A] [HopfAlgebra R A]
    [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] (q : S →ₐ[R] T) :
    WithConv (A →ₐ[R] S) →* WithConv (A →ₐ[R] T) where
  toFun f := toConv (q.comp f.ofConv)
  map_one' := by
    rw [AlgHom.convOne_def, AlgHom.convOne_def]
    apply WithConv.ext
    ext a
    exact q.commutes _
  map_mul' f g := WithConv.ext (AlgHom.comp_convMul_distrib q f g)

private theorem torusConjugation_eval {S : Type u} [CommRing S] [Algebra R S]
    (t : A →ₐc[R] H) (q : A ⊗[R] H →ₐ[R] S) :
    let g := toConv ((q.comp includeRight).comp t.toAlgHom)
    toConv (q.comp (torusConjugation t)) = g * toConv (q.comp includeLeft) * g⁻¹ := by
  let m := postcomposePoint q (A := A)
  let g := toConv ((includeRight : H →ₐ[R] A ⊗[R] H).comp t.toAlgHom)
  change m (g * toConv includeLeft * g⁻¹) = m g * m (toConv includeLeft) * (m g)⁻¹
  rw [map_mul, map_mul]
  rfl

private def conjugationTorusProduct :
    H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := by
  let b : H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := includeLeft.comp includeRight
  let c : H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := includeRight
  exact (lift c b (fun x y => Commute.all (c x) (b y))).comp (Bialgebra.comulAlgHom R H)

private def iteratedTorusConjugation :
    A ⊗[R] H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) :=
  let a : A →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := includeLeft.comp includeLeft
  let c : H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := conjugationTorusProduct
  lift a c (fun x y => Commute.all (a x) (c y))

private theorem torusConjugation_coassoc (t : A →ₐc[R] H) :
    (Algebra.TensorProduct.map (torusConjugation t) (AlgHom.id R H)).comp (torusConjugation t) =
      (iteratedTorusConjugation (R := R) (A := A) (X := X)).comp (torusConjugation t) := by
  let : Group (WithConv (A →ₐ[R] ((A ⊗[R] H) ⊗[R] H))) :=
    pointConvolutionGroup (R := R) (A := A) (S := ((A ⊗[R] H) ⊗[R] H))
  let a : A →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := includeLeft.comp includeLeft
  let b : H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := includeLeft.comp includeRight
  let c : H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := includeRight
  let B := toConv (b.comp t.toAlgHom)
  let C := toConv (c.comp t.toAlgHom)
  let F : A ⊗[R] H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) :=
    Algebra.TensorProduct.map (torusConjugation t) (AlgHom.id R H)
  let J : A ⊗[R] H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := iteratedTorusConjugation
  have eF := torusConjugation_eval (S := ((A ⊗[R] H) ⊗[R] H)) t F
  dsimp only at eF
  rw [show F.comp includeRight = c from Algebra.TensorProduct.map_comp_includeRight _ _,
    show F.comp includeLeft = includeLeft.comp (torusConjugation t) from
      Algebra.TensorProduct.map_comp_includeLeft _ _] at eF
  have eL := torusConjugation_eval (S := ((A ⊗[R] H) ⊗[R] H)) t
    (includeLeft : A ⊗[R] H →ₐ[R] ((A ⊗[R] H) ⊗[R] H))
  dsimp only at eL
  rw [eL] at eF
  have eJ := torusConjugation_eval (S := ((A ⊗[R] H) ⊗[R] H)) t J
  dsimp only at eJ
  have hJ : J.comp includeRight = conjugationTorusProduct := by
    dsimp only [J, iteratedTorusConjugation]
    rw [Algebra.TensorProduct.lift_comp_includeRight']
  have hmul : toConv ((J.comp includeRight).comp t.toAlgHom) = C * B := by
    rw [hJ]
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    change (lift c b (fun x y => Commute.all (c x) (b y))) (Bialgebra.comulAlgHom R H (t x)) =
      (C * B) x
    have hb := AlgHom.convMul_apply (R := R) (A := ((A ⊗[R] H) ⊗[R] H)) (C := A) C B x
    refine Eq.trans ?_ hb.symm
    have ht := AlgHom.congr_fun t.map_comp_comulAlgHom x
    change Algebra.TensorProduct.map t.toAlgHom t.toAlgHom (Coalgebra.comul x) =
      Bialgebra.comulAlgHom R H (t x) at ht
    rw [← ht]
    have h : (lift c b (fun x y => Commute.all (c x) (b y))).comp
        (Algebra.TensorProduct.map t.toAlgHom t.toAlgHom) =
        lift (c.comp t.toAlgHom) (b.comp t.toAlgHom)
          (fun x y => Commute.all (c (t x)) (b (t y))) := by
      apply AlgHom.ext
      intro z
      refine TensorProduct.inductionOn z ?_ ?_
      · intro x y
        rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
          Algebra.TensorProduct.lift_tmul]
        rfl
      · intro x y hx hy
        rw [map_add, map_add, hx, hy]
    exact AlgHom.congr_fun h (Coalgebra.comul x)
  rw [hmul] at eJ
  have hJa : J.comp includeLeft = a := by
    dsimp only [J, iteratedTorusConjugation]
    rw [Algebra.TensorProduct.lift_comp_includeLeft]
  rw [hJa] at eJ
  have he : C * (B * toConv a * B⁻¹) * C⁻¹ = (C * B) * toConv a * (C * B)⁻¹ := by
    simp only [mul_inv_rev, mul_assoc]
  exact toConv_injective (eF.trans (he.trans eJ.symm))

private theorem iteratedTorusConjugation_monomial (a : A) (χ : X) :
    iteratedTorusConjugation (a ⊗ₜ[R] MonoidAlgebra.of R X χ) =
      (a ⊗ₜ[R] MonoidAlgebra.of R X χ) ⊗ₜ[R] MonoidAlgebra.of R X χ := by
  rw [iteratedTorusConjugation, Algebra.TensorProduct.lift_tmul]
  have h : (conjugationTorusProduct : H →ₐ[R] ((A ⊗[R] H) ⊗[R] H))
      (MonoidAlgebra.of R X χ) =
      ((1 : A) ⊗ₜ[R] MonoidAlgebra.of R X χ) ⊗ₜ[R] MonoidAlgebra.of R X χ := by
    let ℓ : H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := includeRight
    let r : H →ₐ[R] ((A ⊗[R] H) ⊗[R] H) := includeLeft.comp includeRight
    change lift ℓ r (fun x y => Commute.all (ℓ x) (r y))
      (Bialgebra.comulAlgHom R H (MonoidAlgebra.of R X χ)) = _
    have hχ : Bialgebra.comulAlgHom R H (MonoidAlgebra.of R X χ) =
        MonoidAlgebra.of R X χ ⊗ₜ[R] MonoidAlgebra.of R X χ :=
      (MonoidAlgebra.isGroupLikeElem_single_one (R := R) (A := R) χ).comul_eq_tmul_self
    rw [hχ, Algebra.TensorProduct.lift_tmul]
    change ((1 : A ⊗[R] H) ⊗ₜ[R] MonoidAlgebra.of R X χ) *
      (((1 : A) ⊗ₜ[R] MonoidAlgebra.of R X χ) ⊗ₜ[R] (1 : H)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [h]
  change ((a ⊗ₜ[R] (1 : H)) ⊗ₜ[R] (1 : H)) *
    (((1 : A) ⊗ₜ[R] MonoidAlgebra.of R X χ) ⊗ₜ[R] MonoidAlgebra.of R X χ) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul]

/-- Selecting one coefficient in the middle factor records the same weight
in the right factor, since the torus monomials are group-like. -/
private theorem iteratedTorusConjugation_weight (χ : X) (z : A ⊗[R] H) :
    TensorProduct.map (tensorMonomialCoeff χ) LinearMap.id (iteratedTorusConjugation z) =
      tensorMonomialCoeff χ z ⊗ₜ[R] MonoidAlgebra.of R X χ := by
  classical
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a b
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b c hb hc =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, TensorProduct.add_tmul, hb, hc]
    | single ψ r =>
      have hr : (MonoidAlgebra.single ψ r : H) = r • MonoidAlgebra.of R X ψ := by
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [hr, TensorProduct.tmul_smul, map_smul, map_smul, map_smul,
        ← TensorProduct.smul_tmul', iteratedTorusConjugation_monomial, TensorProduct.map_tmul,
        LinearMap.id_apply, tensorMonomialCoeff_tmul]
      by_cases h : χ = ψ
      · subst ψ
        simp
      · simp [h]
  · intro b c hb hc
    rw [map_add, map_add, map_add, TensorProduct.add_tmul, hb, hc]

private theorem torusProjection_comul (t : A →ₐc[R] H) (χ : X) (a : A) :
    TensorProduct.map (torusWeightProjection t χ) LinearMap.id (torusConjugation t a) =
      torusWeightProjection t χ a ⊗ₜ[R] MonoidAlgebra.of R X χ := by
  let T := TensorProduct.map (tensorMonomialCoeff (R := R) (V := A) χ)
    (LinearMap.id (R := R) (M := H))
  have he := congrArg (fun g : A →ₐ[R] ((A ⊗[R] H) ⊗[R] H) => T (g a))
    (torusConjugation_coassoc t)
  change T ((Algebra.TensorProduct.map (torusConjugation t) (AlgHom.id R H)) (torusConjugation t a)) =
    T (iteratedTorusConjugation (torusConjugation t a)) at he
  rw [iteratedTorusConjugation_weight] at he
  change (T.comp (TensorProduct.map (torusConjugation t).toLinearMap LinearMap.id))
    (torusConjugation t a) = _ at he
  rw [show T = TensorProduct.map (tensorMonomialCoeff χ) LinearMap.id from rfl,
    ← TensorProduct.map_comp, LinearMap.id_comp] at he
  exact he

private theorem counit_torusConjugation (t : A →ₐc[R] H) :
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (AlgHom.id R H)).comp
      (torusConjugation t) =
      (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] H).comp (Bialgebra.counitAlgHom R A) := by
  let : Group (WithConv (A →ₐ[R] R ⊗[R] H)) :=
    pointConvolutionGroup (R := R) (A := A)
  let f : A ⊗[R] H →ₐ[R] R ⊗[R] H :=
    Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (AlgHom.id R H)
  have hf : f.comp includeLeft = (includeLeft : R →ₐ[R] R ⊗[R] H).comp
      (Bialgebra.counitAlgHom R A) := Algebra.TensorProduct.map_comp_includeLeft _ _
  have h := torusConjugation_eval t f
  dsimp only at h
  rw [hf] at h
  have h₁ : toConv ((includeLeft : R →ₐ[R] R ⊗[R] H).comp
      (Bialgebra.counitAlgHom R A)) = 1 := by
    rw [AlgHom.convOne_def]
    rfl
  rw [h₁] at h
  let g : WithConv (A →ₐ[R] R ⊗[R] H) := toConv ((f.comp includeRight).comp t.toAlgHom)
  have h₂ : g * 1 * g⁻¹ = 1 :=
    (congrArg (· * g⁻¹) (mul_one g)).trans (mul_inv_cancel g)
  exact toConv_injective (h.trans (h₂.trans h₁.symm))

private theorem torusProjection_mem_augmentation (t : A →ₐc[R] H)
    (χ : X) (hne : χ ≠ 1) (a : A) :
    torusWeightProjection t χ a ∈ RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom := by
  classical
  let ε := Bialgebra.counitAlgHom R A
  have h := tensorMonomialCoeff_map ε.toLinearMap χ (torusConjugation t a)
  have hε := DFunLike.congr_fun (counit_torusConjugation t) a
  change tensorMonomialCoeff χ
      ((Algebra.TensorProduct.map ε (AlgHom.id R H)) (torusConjugation t a)) =
    ε (torusWeightProjection t χ a) at h
  change (Algebra.TensorProduct.map ε (AlgHom.id R H)) (torusConjugation t a) =
    ε a ⊗ₜ[R] (1 : H) at hε
  rw [hε, ← map_one (MonoidAlgebra.of R X), tensorMonomialCoeff_tmul, ite_eq_right hne] at h
  exact h.symm

private abbrev tangentSlope (v : Tangent R A) : A →ₗ[R] R :=
  (TrivSqZeroExt.sndHom (R := R) (M := R)).comp v.val.toLinearMap

private def tangentTorusEvaluation {S : Type u} [CommRing S] [Algebra R S]
    (v : Tangent R A) (s : H →ₐ[R] S) : A ⊗[R] H →ₐ[R] DualNumber S :=
  let p := (dualCoefficients S).comp v.val
  let q := (TrivSqZeroExt.inlAlgHom R S S).comp s
  lift p q (fun x y => Commute.all (p x) (q y))

private theorem tangentTorusEvaluation_fst {S : Type u} [CommRing S] [Algebra R S]
    (t : A →ₐc[R] H) (v : Tangent R A) (s : H →ₐ[R] S) (a : A) :
    (tangentTorusEvaluation v s (torusConjugation t a)).fst =
      algebraMap R S (Bialgebra.counitAlgHom R A a) := by
  let ε := Bialgebra.counitAlgHom R A
  let F := (Algebra.TensorProduct.lid R S).toAlgHom
  have eq : (TrivSqZeroExt.fstHom R S S).comp (tangentTorusEvaluation v s) =
      F.comp (Algebra.TensorProduct.map ε s) := by
    apply AlgHom.ext
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro x y
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
      change ((tangentTorusEvaluation v s) (x ⊗ₜ[R] y)).fst = ε x • s y
      simp only [tangentTorusEvaluation, Algebra.TensorProduct.lift_tmul,
        TrivSqZeroExt.fst_mul, AlgHom.comp_apply]
      have h := AlgHom.congr_fun v.property x
      change (v.val x).fst = ε x at h
      change algebraMap R S (v.val x).fst * s y = _
      rw [h, Algebra.smul_def]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  have h := AlgHom.congr_fun eq (torusConjugation t a)
  change _ = F (Algebra.TensorProduct.map ε s (torusConjugation t a)) at h
  have hfac : Algebra.TensorProduct.map ε s =
      (Algebra.TensorProduct.map (AlgHom.id R R) s).comp
        (Algebra.TensorProduct.map ε (AlgHom.id R H)) := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id]
  rw [hfac] at h
  simp only [AlgHom.comp_apply] at h
  have hr := AlgHom.congr_fun (counit_torusConjugation t) a
  change (Algebra.TensorProduct.map ε (AlgHom.id R H)) (torusConjugation t a) =
    ε a ⊗ₜ[R] (1 : H) at hr
  rw [hr, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one] at h
  change (tangentTorusEvaluation v s (torusConjugation t a)).fst = ε a • (1 : S) at h
  exact h.trans (by rw [Algebra.smul_def, mul_one])

private theorem tangentTorusEvaluation_snd {S : Type u} [CommRing S] [Algebra R S]
    (v : Tangent R A) (s : H →ₐ[R] S) (z : A ⊗[R] H) :
    (tangentTorusEvaluation v s z).snd =
      TensorProduct.lid R S (TensorProduct.map (tangentSlope v) s.toLinearMap z) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro x y
    rw [TensorProduct.map_tmul]
    simp only [tangentTorusEvaluation, Algebra.TensorProduct.lift_tmul, DualNumber.snd_mul,
      AlgHom.comp_apply]
    change algebraMap R S (v.val x).fst * 0 + algebraMap R S (v.val x).snd * s y =
      (v.val x).snd • s y
    rw [mul_zero, zero_add, Algebra.smul_def]
  · intro x y hx hy
    rw [map_add, TrivSqZeroExt.snd_add, map_add, map_add, hx, hy]

private theorem tangentTorusEvaluation_snd_coeff (t : A →ₐc[R] H) (v : Tangent R A)
    (χ : X) (a : A) :
    ((tangentTorusEvaluation v (AlgHom.id R H) (torusConjugation t a)).snd).coeff χ =
      tangentSlope v (torusWeightProjection t χ a) := by
  rw [tangentTorusEvaluation_snd]
  have hi (z : R ⊗[R] H) :
      (TensorProduct.lid R H z).coeff χ = tensorMonomialCoeff χ z := by
    refine TensorProduct.inductionOn z ?_ ?_
    · intro x y
      change (x • y).coeff χ = y.coeff χ • x
      rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
    · intro x y hx hy
      rw [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, hx, hy]
  rw [hi]
  exact tensorMonomialCoeff_map (tangentSlope v) χ (torusConjugation t a)

/-- Project a tangent vector onto a character by taking that monomial coefficient
in its conjugation by the universal point of the split torus. -/
private theorem tangentWeightProjection (t : A →ₐc[R] H) (v : Tangent R A) (χ : X) :
    ∃ w : Tangent R A, HasWeight t χ w ∧
      ∀ a, (w.val a).snd = (v.val (torusWeightProjection t χ a)).snd := by
  let ε := Bialgebra.counitAlgHom R A
  let d := (tangentSlope v).comp (torusWeightProjection t χ)
  let q := (tangentTorusEvaluation v (AlgHom.id R H)).comp (torusConjugation t)
  have hfst (a : A) : (q a).fst = algebraMap R H (ε a) :=
    tangentTorusEvaluation_fst t v (AlgHom.id R H) a
  have hsnd (a : A) : (q a).snd.coeff χ = d a :=
    tangentTorusEvaluation_snd_coeff t v χ a
  have hconst (r : R) : d (algebraMap R A r) = 0 := by
    rw [← hsnd, AlgHom.commutes]
    change (0 : H).coeff χ = 0
    rfl
  have hmul (a b : A) : d (a * b) = ε a * d b + ε b * d a := by
    rw [← hsnd, map_mul, DualNumber.snd_mul, hfst, hfst]
    rw [mul_comm (q a).snd, ← Algebra.smul_def, ← Algebra.smul_def,
      MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_smul_apply,
      MonoidAlgebra.coeff_smul_apply, hsnd, hsnd, smul_eq_mul, smul_eq_mul]
  let w : Tangent R A := ⟨tangentFromDerivative ε d hconst hmul, AlgHom.ext fun _ => rfl⟩
  refine ⟨w, ?_, fun a => rfl⟩
  intro S s
  let f := tangentTorusEvaluation w s
  let g := toConv ((TrivSqZeroExt.inlAlgHom R S S).comp (s.comp t.toAlgHom))
  let p := (dualCoefficients S).comp w.val
  let c := s (MonoidAlgebra.of R X χ)
  let scale := (TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S))).restrictScalars R
  change g * toConv p * g⁻¹ = toConv (scale.comp p)
  have hg : (f.comp includeRight).comp t.toAlgHom = g.ofConv := by
    unfold f tangentTorusEvaluation g
    rw [Algebra.TensorProduct.lift_comp_includeRight']
    rfl
  have hp : f.comp includeLeft = p := by
    unfold f tangentTorusEvaluation p
    rw [Algebra.TensorProduct.lift_comp_includeLeft]
  have h := torusConjugation_eval (S := DualNumber S) t f
  dsimp only at h
  rw [hg, hp] at h
  rw [← h]
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · rw [AlgHom.comp_apply, tangentTorusEvaluation_fst t w s a]
    change algebraMap R S (ε a) = (TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S)) (p a)).fst
    rw [TrivSqZeroExt.fst_map]
    exact congrArg (algebraMap R S) (AlgHom.congr_fun w.property a).symm
  · rw [AlgHom.comp_apply, tangentTorusEvaluation_snd]
    change _ = (TrivSqZeroExt.map (c • (LinearMap.id : S →ₗ[S] S)) (p a)).snd
    rw [TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply]
    change TensorProduct.lid R S
      (TensorProduct.map d s.toLinearMap (torusConjugation t a)) =
      c * algebraMap R S (d a)
    have hmap : TensorProduct.map d s.toLinearMap =
        (TensorProduct.map (tangentSlope v) s.toLinearMap).comp
          (TensorProduct.map (torusWeightProjection t χ) LinearMap.id) := by
      rw [← TensorProduct.map_comp, LinearMap.comp_id]
    rw [hmap, LinearMap.comp_apply, torusProjection_comul, TensorProduct.map_tmul]
    change d a • c = c * algebraMap R S (d a)
    rw [Algebra.smul_def, mul_comm]

private theorem torusWeightProjection_idempotent
    (t : A →ₐc[R] H) (χ : X) (a : A) :
    torusWeightProjection t χ (torusWeightProjection t χ a) =
      torusWeightProjection t χ a := by
  classical
  have h := tensorMonomialCoeff_map (torusWeightProjection t χ) χ (torusConjugation t a)
  rw [torusProjection_comul, tensorMonomialCoeff_tmul, if_pos rfl] at h
  exact h.symm

/-- A nonzero integral tangent coefficient on a weight projection yields
a tangent vector of that weight with a coefficient equal to one. -/
private theorem primitiveWeightTangent [IsDomain R] [IsPrincipalIdealRing R]
    (t : A →ₐc[R] H) (χ : X) (v : Tangent R A)
    (h : ∃ a, (v.val (torusWeightProjection t χ a)).snd ≠ 0) :
    ∃ w : Tangent R A, HasWeight t χ w ∧ ∃ a, (w.val a).snd = 1 := by
  obtain ⟨u, _, hu⟩ := tangentWeightProjection t v χ
  obtain ⟨a, ha⟩ := h
  obtain ⟨c, w, hc, he, b, hb⟩ := primitiveTangent u ⟨a, fun h => ha ((hu a).symm.trans h)⟩
  obtain ⟨w', hw', hw⟩ := tangentWeightProjection t w χ
  refine ⟨w', hw', b, (hw b).trans ?_⟩
  suffices (w.val (torusWeightProjection t χ b)).snd = (w.val b).snd from this.trans hb
  apply mul_left_cancel₀ hc
  rw [← he, ← he, hu, hu, torusWeightProjection_idempotent]

/-- A character power on the marked torus selects the corresponding
polynomial coefficient of an equivariant root map. -/
private theorem rootWeightProjection
    (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (hα : Function.Injective fun n : ℕ => α ^ n)
    (f : A →ₐ[R] Polynomial K)
    (equivariant :
      let T := Polynomial K ⊗[R] MonoidAlgebra R X
      let U : K →ₐ[R] T := Algebra.TensorProduct.includeLeft.comp
        ((Algebra.ofId K (Polynomial K)).restrictScalars R)
      let v := (Polynomial.X : Polynomial K) ⊗ₜ[R] MonoidAlgebra.of R X α
      (Algebra.TensorProduct.map f (AlgHom.id R (MonoidAlgebra R X))).comp
        (torusConjugation t) = (Polynomial.eval₂AlgHom U v fun _ => Commute.all _ _).comp f)
    (a : A) (n : ℕ) :
    f (torusWeightProjection t (α ^ n) a) = monomial n ((f a).coeff n) := by
  classical
  let T := Polynomial K ⊗[R] MonoidAlgebra R X
  let U : K →ₐ[R] T := Algebra.TensorProduct.includeLeft.comp
    ((Algebra.ofId K (Polynomial K)).restrictScalars R)
  let v : T := (Polynomial.X : Polynomial K) ⊗ₜ[R] MonoidAlgebra.of R X α
  let p : Polynomial K ⊗[R] MonoidAlgebra R X →ₗ[R] Polynomial K :=
    tensorMonomialCoeff (α ^ n)
  let f' : Polynomial K →ₐ[R] T :=
    Polynomial.eval₂AlgHom U v (fun _ => Commute.all _ _)
  have hm := DFunLike.congr_fun equivariant a
  change (Algebra.TensorProduct.map f (AlgHom.id R (MonoidAlgebra R X))) (torusConjugation t a) =
    f' (f a) at hm
  have hmap := tensorMonomialCoeff_map f.toLinearMap (α ^ n) (torusConjugation t a)
  change p ((Algebra.TensorProduct.map f (AlgHom.id R (MonoidAlgebra R X)))
    (torusConjugation t a)) = f (torusWeightProjection t (α ^ n) a) at hmap
  rw [← hmap, hm]
  generalize f a = q
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, coeff_add, map_add]
  | monomial m b =>
    have hmon : f' (monomial m b) = (monomial m b : Polynomial K) ⊗ₜ[R]
        MonoidAlgebra.of R X (α ^ m) := by
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      simp only [f', Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C, Polynomial.eval₂_X]
      change (Polynomial.C b ⊗ₜ[R] (1 : MonoidAlgebra R X)) * v ^ m = _
      change (Polynomial.C b ⊗ₜ[R] (1 : MonoidAlgebra R X)) *
        ((Polynomial.X : Polynomial K) ⊗ₜ[R] MonoidAlgebra.of R X α) ^ m = _
      rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_pow]
    rw [hmon]
    change tensorMonomialCoeff (α ^ n) (_ ⊗ₜ[R] _) = _
    rw [tensorMonomialCoeff_tmul, coeff_monomial]
    by_cases h : n = m
    · subst m
      simp
    · have ht : α ^ n ≠ α ^ m := fun he => h (hα he)
      simp [ht, Ne.symm h]

end RootWeightProjections

section ModelWeightProjections

attribute [local instance] integralAlgebraModule
set_option backward.isDefEq.respectTransparency false

/-- If the character is nontrivial and is absent from the root datum, its
weight projection vanishes in the integral augmentation cotangent. -/
private theorem modelWeightProjection_mem_augmentationSquare
    {D : BasedRootDatum.{u}} {A : Type u} [CommRing A] [HopfAlgebra IntegralRing.{u} A]
    (t : A →ₐc[IntegralRing.{u}] MonoidAlgebra IntegralRing.{u} (Multiplicative D.X))
    (smooth : Smooth (HopfSpectrum IntegralRing.{u} A).X.hom)
    (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] [Algebra IntegralRing.{u} K]
    (fibre : HasFibreDatum D t K)
    (χ : Multiplicative D.X) (hχ : χ ≠ 1)
    (hroot : ∀ i, χ ≠ Multiplicative.ofAdd (D.datum.root i)) (a : A) :
    torusWeightProjection t χ a ∈
      (RingHom.ker (Bialgebra.counitAlgHom IntegralRing.{u} A).toRingHom) ^ 2 := by
  let : IsDomain IntegralRing.{u} := integralRing_isDomain
  let : IsPrincipalIdealRing IntegralRing.{u} := integralRing_isPrincipalIdealRing
  let : Algebra.Smooth IntegralRing.{u} A := modelSmoothAlgebra smooth
  let ε := Bialgebra.counitAlgHom IntegralRing.{u} A
  have hfree := augmentedCotangent_free ε
  let b : RingHom.ker ε.toRingHom :=
    ⟨torusWeightProjection t χ a, torusProjection_mem_augmentation t χ hχ a⟩
  refine @mem_augmentationSquare_of_tangents IntegralRing.{u} A _ _ _ ε hfree b ?_
  intro v hv
  obtain ⟨w, hw, he⟩ := tangentWeightProjection t ⟨v, hv⟩ χ
  exact (he a).symm.trans (missingWeight_tangent_snd_eq_zero t K fibre χ hχ hroot w hw a)

end ModelWeightProjections

section RootCoordinatesFromWeights

open Polynomial

private theorem rootPowers_injective {D : BasedRootDatum.{u}} (i : D.I) :
    Function.Injective (fun n : ℕ => Multiplicative.ofAdd (D.datum.root i) ^ n) := by
  letI := D.freeX
  intro n m h
  have e : n • D.datum.root i = m • D.datum.root i :=
    congrArg Multiplicative.toAdd h
  apply Int.ofNat.inj
  apply smul_left_injective ℤ (D.datum.ne_zero i)
  change ((n : ℤ) • D.datum.root i) = ((m : ℤ) • D.datum.root i)
  simpa only [natCast_zsmul] using e

private theorem higherRootPower_not_root {D : BasedRootDatum.{u}} (i : D.I) (n : ℕ)
    (hn : 2 ≤ n) (j : D.I) :
    Multiplicative.ofAdd (D.datum.root i) ^ n ≠ Multiplicative.ofAdd (D.datum.root j) := by
  letI := D.reduced
  letI := D.freeX
  haveI : HasUniqueDiv D.X := HasUniqueDiv.of_isTorsionFree ℤ D.X
  letI : n.AtLeastTwo := ⟨hn⟩
  intro h
  exact D.datum.nsmul_notMem_range_root (n := n) (i := i) ⟨j,
    (congrArg Multiplicative.toAdd h).symm⟩

variable {R K A : Type u} [CommRing R] [Field K] [CommRing A] [Algebra R K] [HopfAlgebra R A]

private theorem linearCoeff_eq_zero_of_augmentationSquare
    (ε : A →ₐ[R] R) (f : A →ₐ[R] Polynomial K)
    (h₀ : ∀ a, (f a).coeff 0 = algebraMap R K (ε a))
    (a : A) (ha : a ∈ (RingHom.ker ε.toRingHom) ^ 2) :
    (f a).coeff 1 = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro b hb c hc
    have hb' : Polynomial.X ∣ f b := Polynomial.X_dvd_iff.mpr (by rw [h₀, show ε b = 0 from hb, map_zero])
    have hc' : Polynomial.X ∣ f c := Polynomial.X_dvd_iff.mpr (by rw [h₀, show ε c = 0 from hc, map_zero])
    rw [map_mul]
    exact Polynomial.X_pow_dvd_iff.mp (by rw [pow_two]; exact mul_dvd_mul hb' hc') 1 (by decide)
  · intro b c hb hc
    rw [map_add, Polynomial.coeff_add, hb, hc, add_zero]

/-- A generic root polynomial with a nonzero linear term detects a
primitive integral tangent vector of the marked weight. -/
private theorem primitiveTangent_of_rootPolynomial {X : Type u} [CommGroup X]
    [IsDomain R] [IsPrincipalIdealRing R] [Algebra.Smooth R A]
    (t : A →ₐc[R] MonoidAlgebra R X) (χ : X) (hχ : χ ≠ 1) (f : A →ₐ[R] Polynomial K)
    (h₀ : ∀ a, (f a).coeff 0 = algebraMap R K (Bialgebra.counitAlgHom R A a))
    (h₁ : ∃ a, (f a).coeff 1 ≠ 0)
    (hproj : ∀ a, (f (torusWeightProjection t χ a)).coeff 1 = (f a).coeff 1) :
    ∃ v : Tangent R A, HasWeight t χ v ∧ ∃ a, (v.val a).snd = 1 := by
  obtain ⟨a, ha⟩ := h₁
  let ε := Bialgebra.counitAlgHom R A
  let b : RingHom.ker ε.toRingHom :=
    ⟨torusWeightProjection t χ a, torusProjection_mem_augmentation t χ hχ a⟩
  let : Module.Free R (RingHom.ker ε.toRingHom).Cotangent := augmentedCotangent_free ε
  have h : ∃ v : Tangent R A, (v.val b.val).snd ≠ 0 := by
    by_contra! hz
    have hb := mem_augmentationSquare_of_tangents ε b (fun v hv => hz ⟨v, hv⟩)
    apply ha
    rw [← hproj]
    exact linearCoeff_eq_zero_of_augmentationSquare ε f h₀ b.val hb
  obtain ⟨v, hv⟩ := h
  exact primitiveWeightTangent t χ v ⟨a, hv⟩

/-- A root parameter with an integral basis in degree one gives an integral
polynomial coordinate once the higher character powers vanish in the
augmentation cotangent space. -/
private theorem integralRootPolynomial {D : BasedRootDatum.{u}}
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)) (i : D.I)
    (f : A →ₐ[R] Polynomial K) (hR : Function.Injective (algebraMap R K))
    (h₀ : ∀ a, (f a).coeff 0 = algebraMap R K (Bialgebra.counitAlgHom R A a))
    (h₁ : ∀ a, (f a).coeff 1 ∈ Set.range (algebraMap R K))
    (hgen : ∃ a, (f a).coeff 1 = 1)
    (equivariant : ∀ a n,
      f (torusWeightProjection t (Multiplicative.ofAdd (D.datum.root i) ^ n) a) =
        monomial n ((f a).coeff n))
    (cotangent : ∀ (χ : Multiplicative D.X), χ ≠ 1 →
      (∀ j, χ ≠ Multiplicative.ofAdd (D.datum.root j)) →
      ∀ a, torusWeightProjection t χ a ∈ (RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom) ^ 2) :
    ∃! g : A →ₐ[R] Polynomial R, extendPolynomial.comp g = f ∧ Function.Surjective g := by
  apply integralPolynomialCoordinate (Bialgebra.counitAlgHom R A) f hR h₀ h₁
  · intro a n hn
    let α := Multiplicative.ofAdd (D.datum.root i)
    have hα : α ^ n ≠ 1 := by
      intro h
      have eq := rootPowers_injective i (a₂ := 0) (h.trans (pow_zero α).symm)
      omega
    refine ⟨torusWeightProjection t (α ^ n) a,
      cotangent _ hα (higherRootPower_not_root i n hn) a, ?_⟩
    rw [equivariant a n, coeff_monomial, ite_eq_left rfl]
  · obtain ⟨a, ha⟩ := hgen
    refine ⟨torusWeightProjection t (Multiplicative.ofAdd (D.datum.root i)) a, ?_⟩
    change f (torusWeightProjection t (Multiplicative.ofAdd (D.datum.root i)) a) = Polynomial.X
    rw [← pow_one (Multiplicative.ofAdd (D.datum.root i)), equivariant a 1, ha]
    rfl

end RootCoordinatesFromWeights

open private additivePoints_add rootPoint_eq rootPoint_zero
  normalizes_of_point_conjugation tangent_weight_of_scalarAction
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private subgroupOf_mutual_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

section FieldCoordinates

open AdjointRepresentation (GroupPoints)
open CharacterPairing (characterValue)
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

set_option backward.isDefEq.respectTransparency false

variable {R K A X : Type u} [CommRing R] [Field K] [CommRing A]
  [Algebra R K] [HopfAlgebra R A] [CommGroup X]

private theorem calibratedRootCharacter {D : BasedRootDatum.{u}} {Q : SplitBorelPair K}
    (E : AttachedDatum Q) (d : BasedIso D E.toBased) (i : D.I) :
    attachedCharacterEquiv d (Multiplicative.ofAdd (D.datum.root i)) =
      (d.val.indexEquiv i).val := by
  letI := E.comm
  exact (characterEquiv_root d i).trans (congrArg Multiplicative.ofAdd
    (E.datum.root_eq (d.val.indexEquiv i)))

private def affinePullback {C B : Type u} [CommRing C] [CommRing B] [Algebra K C] [Algebra K B]
    (f : (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K B)) ⟶
      (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K C))) : C →ₐ[K] B :=
  ((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage f).unop.hom

private theorem spectrum_affinePullback {C B : Type u} [CommRing C] [CommRing B]
    [Algebra K C] [Algebra K B]
    (f : (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K B)) ⟶
      (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K C))) :
    spectrumOfAlgHom (affinePullback f) = f :=
  (algSpec.fullyFaithful (R := CommRingCat.of K)).map_preimage f

private theorem spectrumOfAlgHom_injective {C B : Type u} [CommRing C] [CommRing B]
    [Algebra K C] [Algebra K B] :
    Function.Injective (fun f : C →ₐ[K] B => spectrumOfAlgHom f) := by
  intro f g h
  exact congrArg (fun m => m.unop.hom)
    ((algSpec.fullyFaithful (R := CommRingCat.of K)).map_injective h)

private theorem affinePullback_surjective {C B : Type u} [CommRing C] [CommRing B]
    [Algebra K C] [Algebra K B]
    (f : (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K B)) ⟶
      (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K C)))
    (hf : IsClosedImmersion f.left) :
    Function.Surjective (affinePullback f) := by
  let q := CommRingCat.ofHom (affinePullback f).toRingHom
  have h : Spec.map q = f.left := congrArg Over.Hom.left (spectrum_affinePullback f)
  letI : IsClosedImmersion (Spec.map q) := h ▸ hf
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map q)).2
  have eq : q = (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (Spec.map q).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  change Function.Surjective q.hom
  rw [eq]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).2.comp hs).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv).2

private theorem groupIso_left_isIso {G H : GroupScheme K} (e : G ≅ H) :
    IsIso e.hom.hom.hom.left := by
  change IsIso ((Grp.forget _ ⋙ Over.forget _).map e.hom)
  infer_instance

-- The following transports a root point through the affine calibration.
private theorem rootPoint_of_pullback {L : AdditiveLine K} {G : GroupScheme K}
    (e : HopfSpectrum K (K ⊗[R] A) ≅ G) (x : L.group ⟶ G)
    (f : K ⊗[R] A →ₐ[K] Polynomial K)
    (h : spectrumOfAlgHom f ≫ e.hom.hom.hom = x.hom.hom) (S : TestAlgebra K) (a : S) :
    spectrumOfAlgHom ((Polynomial.aeval a).comp f) ≫ e.hom.hom.hom = rootPoint x S a := by
  rw [spectrumOfAlgHom_comp, Category.assoc, h]
  rfl

private theorem rootPoint_convolution_laws {L : AdditiveLine K} {G : GroupScheme K}
    (e : HopfSpectrum K (K ⊗[R] A) ≅ G) (x : L.group ⟶ G)
    (f : K ⊗[R] A →ₐ[K] Polynomial K)
    (h : spectrumOfAlgHom f ≫ e.hom.hom.hom = x.hom.hom) (S : TestAlgebra K) :
    (∀ a b : S, coordinatePoint f S (a + b) = coordinatePoint f S a * coordinatePoint f S b) ∧
      coordinatePoint f S 0 = 1 := by
  let m : WithConv (K ⊗[R] A →ₐ[K] S) →* GroupPoints G S :=
    (((groupPointsFunctor K).map e.hom).app S).hom.comp Spec.mapMulEquiv.toMonoidHom
  have hm : Function.Injective m :=
    fun p q eq => Spec.mapMulEquiv.injective ((cancel_mono e.hom.hom.hom).mp eq)
  have hp (a : S) : m (coordinatePoint f S a) = rootPoint x S a :=
    rootPoint_of_pullback e x f h S a
  constructor
  · intro a b
    apply hm
    rw [map_mul, hp, hp, hp, rootPoint_eq, rootPoint_eq, rootPoint_eq, additivePoints_add]
    exact MonObj.mul_comp _ _ _
  · apply hm
    rw [map_one, hp, rootPoint_zero]

attribute [local instance] pointConvolutionGroup

private theorem scalarAction_calibration {G : GroupScheme K}
    (t : A →ₐc[R] MonoidAlgebra R X) (α : X) (T : ClosedSubgroup G)
    (χ : Character T.group)
    (e : HopfSpectrum K (K ⊗[R] A) ≅ G)
    (s : HopfSpectrum K (K ⊗[R] MonoidAlgebra R X) ≅ T.group)
    (hT : spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id K K) t) ≫ e.hom =
      s.hom ≫ T.inclusion)
    (hχ : characterMonomial (s.hom ≫ χ) = (1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
    {L : AdditiveLine K} (x : L.group ⟶ G)
    (f : K ⊗[R] A →ₐ[K] Polynomial K)
    (h : spectrumOfAlgHom f ≫ e.hom.hom.hom = x.hom.hom) :
    HasScalarAction T χ x ↔
      ∀ (S : TestAlgebra K) (a : S) (q : K ⊗[R] MonoidAlgebra R X →ₐ[K] S),
        let g := toConv (q.comp (Bialgebra.TensorProduct.map (BialgHom.id K K) t).toAlgHom)
        let c := q ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
        g * coordinatePoint f S a * g⁻¹ = coordinatePoint f S (c * a) := by
  let tK := Bialgebra.TensorProduct.map (BialgHom.id K K) t
  have test (S : TestAlgebra K) (a : S) (q : K ⊗[R] MonoidAlgebra R X →ₐ[K] S) :
      let b : GroupPoints T.group S := spectrumOfAlgHom q ≫ s.hom.hom.hom
      let g := toConv (q.comp tK.toAlgHom)
      let c := q ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
      g * coordinatePoint f S a * g⁻¹ = coordinatePoint f S (c * a) ↔
        let z : GroupPoints G S := b ≫ T.inclusion.hom.hom
        z * rootPoint x S a * z⁻¹ = rootPoint x S (characterValue χ S b * a) := by
    dsimp only
    let m : WithConv (K ⊗[R] A →ₐ[K] S) →* GroupPoints G S :=
      (((groupPointsFunctor K).map e.hom).app S).hom.comp Spec.mapMulEquiv.toMonoidHom
    have hm : Function.Injective m := fun p q eq =>
      Spec.mapMulEquiv.injective ((cancel_mono e.hom.hom.hom).mp eq)
    have hp (a : S) : m (coordinatePoint f S a) = rootPoint x S a :=
      rootPoint_of_pullback e x f h S a
    have hg : m (toConv (q.comp tK.toAlgHom)) =
        (spectrumOfAlgHom q ≫ s.hom.hom.hom) ≫ T.inclusion.hom.hom := by
      change spectrumOfAlgHom (q.comp tK.toAlgHom) ≫ e.hom.hom.hom = _
      rw [spectrumOfAlgHom_comp, Category.assoc, Category.assoc]
      exact congrArg (fun z : HopfSpectrum K (K ⊗[R] MonoidAlgebra R X) ⟶ G =>
        spectrumOfAlgHom q ≫ z.hom.hom) hT
    have hc : characterValue χ S (spectrumOfAlgHom q ≫ s.hom.hom.hom) =
        q ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α) := by
      have hcomp : characterValue χ S (spectrumOfAlgHom q ≫ s.hom.hom.hom) =
          characterValue (s.hom ≫ χ) S (spectrumOfAlgHom q) := by
        unfold characterValue
        rw [Category.assoc]
        rfl
      rw [hcomp, characterValue_spectrum, hχ]
    rw [← hm.eq_iff, map_mul, map_mul, map_inv, hg, hp, hp, hc]
  constructor
  · intro hscalar S a q
    exact (test S a q).2 (hscalar S _ a)
  · intro hscalar S b a
    let q := affinePullback (b ≫ s.inv.hom.hom)
    have hb : spectrumOfAlgHom q ≫ s.hom.hom.hom = b := by
      rw [spectrum_affinePullback, Category.assoc]
      have hs := congrArg (fun f : T.group ⟶ T.group => f.hom.hom) s.inv_hom_id
      rw [Grp.comp_hom_hom, Grp.id_hom_hom] at hs
      rw [hs, Category.comp_id]
    have hh := (test S a q).1 (hscalar S a q)
    simpa only [hb] using hh

end FieldCoordinates

section CoordinateLaws

open Algebra.TensorProduct (includeLeft includeRight lift)
open Polynomial

attribute [local instance] pointConvolutionGroup
set_option backward.isDefEq.respectTransparency false

variable {R K A X : Type u} [CommRing R] [Field K] [CommRing A]
  [Algebra R K] [HopfAlgebra R A] [CommGroup X]

private def PolynomialPointLaws (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (x : A →ₐ[R] Polynomial R) : Prop :=
  (∀ (S : CommAlgCat.{u} R) (a b : S),
    coordinatePoint x S (a + b) = coordinatePoint x S a * coordinatePoint x S b) ∧
  (∀ S : CommAlgCat.{u} R, coordinatePoint x S 0 = 1) ∧ RootScalarAction t x α

private def FibrePointLaws (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (f : K ⊗[R] A →ₐ[K] Polynomial K) : Prop :=
  (∀ (S : TestAlgebra K) (a b : S),
    coordinatePoint f S (a + b) = coordinatePoint f S a * coordinatePoint f S b) ∧
  (∀ S : TestAlgebra K, coordinatePoint f S 0 = 1) ∧
  ∀ (S : TestAlgebra K) (a : S) (q : K ⊗[R] MonoidAlgebra R X →ₐ[K] S),
    let g := toConv (q.comp (Bialgebra.TensorProduct.map (BialgHom.id K K) t).toAlgHom)
    let c := q ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R X α)
    g * coordinatePoint f S a * g⁻¹ = coordinatePoint f S (c * a)

private theorem restrict_fibreCoordinate (x : A →ₐ[R] Polynomial R) :
    restrictPoint (fibreCoordinate K x) = extendPolynomial.comp x :=
  Equiv.symm_apply_apply _ _

private theorem restrict_coordinatePoint (S : TestAlgebra K) [Algebra R S]
    [IsScalarTower R K S] (f : K ⊗[R] A →ₐ[K] Polynomial K) (a : S) :
    restrictPoint (coordinatePoint f S a).ofConv =
      ((Polynomial.aeval a : Polynomial K →ₐ[K] S).restrictScalars R).comp (restrictPoint f) :=
  rfl

private theorem restrict_torusPoint {S : Type u} [CommRing S] [Algebra K S] [Algebra R S]
    [IsScalarTower R K S] (t : A →ₐc[R] MonoidAlgebra R X)
    (q : K ⊗[R] MonoidAlgebra R X →ₐ[K] S) :
    restrictPoint (q.comp (Bialgebra.TensorProduct.map (BialgHom.id K K) t).toAlgHom) =
      (restrictPoint q).comp t.toAlgHom := by
  ext a
  change q ((Bialgebra.TensorProduct.map (BialgHom.id K K) t) ((1 : K) ⊗ₜ[R] a)) =
    q ((1 : K) ⊗ₜ[R] t a)
  rw [Bialgebra.TensorProduct.map_tmul]
  rfl

private theorem aeval_restrict_map {S : Type u} [CommRing S] [Algebra K S] [Algebra R S]
    [IsScalarTower R K S] (a : S) :
    ((Polynomial.aeval a : Polynomial K →ₐ[K] S).restrictScalars R).comp
      (extendPolynomial : Polynomial R →ₐ[R] Polynomial K) = Polynomial.aeval a := by
  apply Polynomial.algHom_ext
  simp [Polynomial.coe_mapAlgHom]

private theorem restrict_integralPoint (S : TestAlgebra K) [Algebra R S]
    [IsScalarTower R K S] (x : A →ₐ[R] Polynomial R) (a : S) :
    restrictPoint (coordinatePoint (fibreCoordinate K x) S a).ofConv =
      (coordinatePoint x (CommAlgCat.of R S) a).ofConv := by
  rw [restrict_coordinatePoint, restrict_fibreCoordinate, ← AlgHom.comp_assoc, aeval_restrict_map]
  rfl

private theorem restrictPoint_injective {S : Type u} [CommRing S] [Algebra K S] [Algebra R S]
    [IsScalarTower R K S] :
    Function.Injective (restrictPointMonoidHom (R := R) (K := K) (A := A) (S := S)) := by
  intro p q h
  exact WithConv.ofConv_injective (restrictPoint.injective (congrArg WithConv.ofConv h))

private theorem polynomialPointLaws_on_fibre (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (x : A →ₐ[R] Polynomial R) (h : PolynomialPointLaws t α x) :
    FibrePointLaws t α (fibreCoordinate K x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S a b
    letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
    letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    apply restrictPoint_injective (R := R)
    rw [map_mul]
    change toConv (restrictPoint (coordinatePoint (fibreCoordinate K x) S (a + b)).ofConv) =
      toConv (restrictPoint (coordinatePoint (fibreCoordinate K x) S a).ofConv) *
        toConv (restrictPoint (coordinatePoint (fibreCoordinate K x) S b).ofConv)
    rw [restrict_integralPoint S x (a + b), restrict_integralPoint S x a,
      restrict_integralPoint S x b]
    exact h.1 (CommAlgCat.of R S) a b
  · intro S
    letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
    letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    apply restrictPoint_injective (R := R)
    rw [map_one]
    change toConv (restrictPoint (coordinatePoint (fibreCoordinate K x) S 0).ofConv) = 1
    rw [restrict_integralPoint S x 0]
    exact h.2.1 (CommAlgCat.of R S)
  · intro S a q
    letI : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
    letI : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    dsimp only
    apply restrictPoint_injective (R := R)
    rw [map_mul, map_mul, map_inv]
    let g := q.comp (Bialgebra.TensorProduct.map (BialgHom.id K K) t).toAlgHom
    let f := fibreCoordinate K x
    change toConv (restrictPoint g) * toConv (restrictPoint (coordinatePoint f S a).ofConv) *
        (toConv (restrictPoint g))⁻¹ =
      toConv (restrictPoint (coordinatePoint f S ((restrictPoint q) (MonoidAlgebra.of R X α) * a)).ofConv)
    rw [show f = fibreCoordinate K x from rfl, restrict_integralPoint S x a,
      restrict_integralPoint S x ((restrictPoint q) (MonoidAlgebra.of R X α) * a),
      show g = q.comp (Bialgebra.TensorProduct.map (BialgHom.id K K) t).toAlgHom from rfl,
      restrict_torusPoint]
    exact h.2.2 (CommAlgCat.of R S) a (restrictPoint q)

private theorem restrict_fibrePointLaws (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (f : K ⊗[R] A →ₐ[K] Polynomial K) (h : FibrePointLaws t α f)
    (S : Type u) [CommRing S] [Algebra K S] [Algebra R S] [IsScalarTower R K S] :
    let pt (a : S) := toConv (((Polynomial.aeval a : Polynomial K →ₐ[K] S).restrictScalars R).comp
      (restrictPoint f))
    (∀ a b : S, pt (a + b) = pt a * pt b) ∧ pt 0 = 1 ∧
    ∀ (a : S) (q : MonoidAlgebra R X →ₐ[R] S), let g := toConv (q.comp t.toAlgHom)
      g * pt a * g⁻¹ = pt (q (MonoidAlgebra.of R X α) * a) := by
  let m := restrictPointMonoidHom (R := R) (K := K) (A := A) (S := S)
  let T := CommAlgCat.of K S
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have eq := congrArg m (h.1 T a b)
    rw [map_mul] at eq
    exact eq
  · have eq := congrArg m (h.2.1 T)
    rw [map_one] at eq
    exact eq
  · intro a q
    let qK := (AlgHom.liftEquiv R K (MonoidAlgebra R X) S) q
    have eq := congrArg m (h.2.2 T a qK)
    rw [map_mul, map_mul, map_inv] at eq
    let g := qK.comp (Bialgebra.TensorProduct.map (BialgHom.id K K) t).toAlgHom
    change toConv (restrictPoint g) * toConv (restrictPoint (coordinatePoint f T a).ofConv) *
        (toConv (restrictPoint g))⁻¹ =
      toConv (restrictPoint (coordinatePoint f T ((restrictPoint qK) (MonoidAlgebra.of R X α) * a)).ofConv) at eq
    rw [restrict_coordinatePoint T f a, restrict_coordinatePoint T f
      ((restrictPoint qK) (MonoidAlgebra.of R X α) * a)] at eq
    simpa only [g, restrict_torusPoint, qK, Equiv.symm_apply_apply] using eq

private theorem postcompose_coordinatePoint {B C : CommAlgCat.{u} R} (q : B →ₐ[R] C) (x : A →ₐ[R] Polynomial R) (a : B) :
    postcomposePoint q (coordinatePoint x B a) =
      coordinatePoint x C (q a) := by
  have h : q.comp (Polynomial.aeval a) = Polynomial.aeval (q a) :=
    Polynomial.algHom_ext (by simp)
  exact congrArg (fun e : Polynomial R →ₐ[R] C => toConv (e.comp x)) h

private theorem postcomposePoint_injective {B C : Type u} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (q : B →ₐ[R] C) (hq : Function.Injective q) :
    Function.Injective (postcomposePoint q (A := A)) := by
  intro p r h
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  exact hq (congrArg (fun p : WithConv (A →ₐ[R] C) => p.ofConv a) h)

private theorem laws_on_flat_test (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (x : A →ₐ[R] Polynomial R) (hK : Function.Injective (algebraMap R K))
    (h : FibrePointLaws t α (fibreCoordinate K x))
    (S : CommAlgCat.{u} R) [Module.Flat R S] :
    (∀ a b : S, coordinatePoint x S (a + b) = coordinatePoint x S a * coordinatePoint x S b) ∧
      coordinatePoint x S 0 = 1 ∧
    ∀ (a : S) (q : MonoidAlgebra R X →ₐ[R] S), let g := toConv (q.comp t.toAlgHom)
      g * coordinatePoint x S a * g⁻¹ = coordinatePoint x S (q (MonoidAlgebra.of R X α) * a) := by
  let B := K ⊗[R] S
  let j : S →ₐ[R] B := includeRight
  have hj := postcomposePoint_injective (A := A) j (Algebra.TensorProduct.includeRight_injective hK)
  have hb := restrict_fibrePointLaws t α (fibreCoordinate K x) h B
  simp only [restrict_fibreCoordinate, ← AlgHom.comp_assoc, aeval_restrict_map] at hb
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    apply hj
    rw [map_mul, postcompose_coordinatePoint (C := CommAlgCat.of R B),
      postcompose_coordinatePoint (C := CommAlgCat.of R B),
      postcompose_coordinatePoint (C := CommAlgCat.of R B), map_add]
    exact hb.1 (j a) (j b)
  · apply hj
    rw [map_one, postcompose_coordinatePoint (C := CommAlgCat.of R B), map_zero]
    exact hb.2.1
  · intro a q
    dsimp only
    apply hj
    rw [map_mul, map_mul, map_inv, postcompose_coordinatePoint (C := CommAlgCat.of R B),
      postcompose_coordinatePoint (C := CommAlgCat.of R B), map_mul]
    exact hb.2.2 (j a) (j.comp q)

private theorem polynomialPointLaws_of_fibre (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (x : A →ₐ[R] Polynomial R) (hK : Function.Injective (algebraMap R K))
    (h : FibrePointLaws t α (fibreCoordinate K x)) :
    PolynomialPointLaws t α x := by
  let P := Polynomial R
  let H := MonoidAlgebra R X
  let a₀ : P ⊗[R] P := (Polynomial.X : P) ⊗ₜ[R] 1
  let b₀ : P ⊗[R] P := (1 : P) ⊗ₜ[R] Polynomial.X
  let a₁ : P ⊗[R] H := (Polynomial.X : P) ⊗ₜ[R] 1
  have hadd := (laws_on_flat_test t α x hK h (CommAlgCat.of R (P ⊗[R] P))).1 a₀ b₀
  have hzero := (laws_on_flat_test t α x hK h (CommAlgCat.of R R)).2.1
  have hscalar := (laws_on_flat_test t α x hK h (CommAlgCat.of R (P ⊗[R] H))).2.2
    a₁ (includeRight : H →ₐ[R] P ⊗[R] H)
  refine ⟨?_, ?_, ?_⟩
  · intro S a b
    let q : P ⊗[R] P →ₐ[R] S := lift (Polynomial.aeval a) (Polynomial.aeval b) (fun _ _ => Commute.all _ _)
    have eq := congrArg (postcomposePoint q (A := A)) hadd
    have hq := postcompose_coordinatePoint (B := CommAlgCat.of R (P ⊗[R] P)) (C := S) q x
    simp only [map_mul, hq, map_add] at eq
    have ha : q a₀ = a := by
      simpa only [q, a₀, Algebra.TensorProduct.lift_tmul, map_one, mul_one] using
        (Polynomial.aeval_X (R := R) a)
    have hb : q b₀ = b := by
      simpa only [q, b₀, Algebra.TensorProduct.lift_tmul, map_one, one_mul] using
        (Polynomial.aeval_X (R := R) b)
    rwa [ha, hb] at eq
  · intro S
    have eq := congrArg (postcomposePoint (Algebra.ofId R S) (A := A)) hzero
    rwa [map_one, postcompose_coordinatePoint (B := CommAlgCat.of R R) (C := S), map_zero] at eq
  · intro S a p
    let q : P ⊗[R] H →ₐ[R] S := lift (Polynomial.aeval a) p (fun _ _ => Commute.all _ _)
    have eq := congrArg (postcomposePoint q (A := A)) hscalar
    dsimp only at eq ⊢
    have hpt := postcompose_coordinatePoint (B := CommAlgCat.of R (P ⊗[R] H)) (C := S) q x
    simp only [map_mul, map_inv, hpt] at eq
    have ha : q a₁ = a := by
      simpa only [q, a₁, Algebra.TensorProduct.lift_tmul, map_one, mul_one] using
        (Polynomial.aeval_X (R := R) a)
    have hq : q.comp includeRight = p := by
      exact Algebra.TensorProduct.lift_comp_includeRight' _ _ _
    rw [ha, show q (includeRight (MonoidAlgebra.of R X α)) = p (MonoidAlgebra.of R X α) from
      DFunLike.congr_fun hq _, show postcomposePoint q (toConv ((includeRight : H →ₐ[R] _).comp t.toAlgHom)) =
      toConv (p.comp t.toAlgHom) by
        change toConv (q.comp (includeRight.comp t.toAlgHom)) = _
        rw [← AlgHom.comp_assoc, hq]] at eq
    exact eq

private theorem genericWeightProjection (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (hinj : Function.Injective fun n : ℕ => α ^ n)
    (f : K ⊗[R] A →ₐ[K] Polynomial K) (h : FibrePointLaws t α f) (a : A) (n : ℕ) :
    restrictPoint f (torusWeightProjection t (α ^ n) a) =
      monomial n ((restrictPoint f a).coeff n) := by
  let H := MonoidAlgebra R X
  let T := Polynomial K ⊗[R] H
  let U : K →ₐ[R] T := includeLeft.comp ((Algebra.ofId K (Polynomial K)).restrictScalars R)
  let v := (Polynomial.X : Polynomial K) ⊗ₜ[R] (1 : H)
  let F := restrictPoint f
  apply rootWeightProjection t α hinj F ?_ a n
  dsimp only
  let m : A →ₐ[R] T := includeLeft.comp F
  let q : A ⊗[R] H →ₐ[R] T := Algebra.TensorProduct.map F (AlgHom.id R H)
  have hleft : q.comp includeLeft = m := by
    ext a
    change F a ⊗ₜ[R] (1 : H) = _
    rfl
  have hright : q.comp includeRight = (includeRight : H →ₐ[R] T) := by
    apply AlgHom.ext
    intro a
    change F 1 ⊗ₜ[R] a = (1 : Polynomial K) ⊗ₜ[R] a
    rw [map_one]
  have hpol (b : T) :
      ((Polynomial.aeval b : Polynomial K →ₐ[K] T).restrictScalars R) =
        Polynomial.eval₂AlgHom U b (fun _ => Commute.all _ _) := by
    apply AlgHom.ext
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
      simp only [Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C, Polynomial.eval₂_X]
      change Polynomial.aeval b (C c) * Polynomial.aeval b Polynomial.X ^ n = U c * b ^ n
      rw [aeval_C, aeval_X]
      rfl
  have hev : ((Polynomial.aeval v : Polynomial K →ₐ[K] T).restrictScalars R) = includeLeft := by
    have h : (Polynomial.aeval v : Polynomial K →ₐ[K] T) =
        (includeLeft : Polynomial K →ₐ[K] T) := Polynomial.algHom_ext (Polynomial.aeval_X v)
    exact congrArg (AlgHom.restrictScalars R) h
  have eq := (restrict_fibrePointLaws t α f h T).2.2 v (includeRight : H →ₐ[R] T)
  dsimp only at eq
  rw [hev, hpol, show (includeRight : H →ₐ[R] T) (MonoidAlgebra.of R X α) * v =
      (Polynomial.X : Polynomial K) ⊗ₜ[R] MonoidAlgebra.of R X α by
    simp [v, Algebra.TensorProduct.tmul_mul_tmul]] at eq
  have hconj := torusConjugation_eval t q
  dsimp only at hconj
  rw [hleft, hright] at hconj
  exact WithConv.toConv_injective (hconj.trans eq)

end CoordinateLaws

section FibreComparison

open Algebra.TensorProduct (includeLeft includeRight lift)
open AdjointRepresentation (GroupPoints)
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

set_option backward.isDefEq.respectTransparency false

variable {R K A X : Type u} [CommRing R] [Field K] [CommRing A]
  [Algebra R K] [HopfAlgebra R A] [CommGroup X]

private theorem polynomial_surjective_of_X {B : Type u} [CommRing B] [Algebra K B]
    (f : B →ₐ[K] Polynomial K) (hx : Polynomial.X ∈ f.range) : Function.Surjective f := by
  intro p
  change p ∈ f.range
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact f.range.add_mem hp hq
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    exact f.range.mul_mem (f.range.algebraMap_mem c) (f.range.pow_mem hx n)

private theorem fibreCoordinate_surjective (x : A →ₐ[R] Polynomial R)
    (hx : Function.Surjective x) :
    Function.Surjective (fibreCoordinate K x) := by
  apply polynomial_surjective_of_X
  obtain ⟨a, ha⟩ := hx Polynomial.X
  refine ⟨(1 : K) ⊗ₜ[R] a, ?_⟩
  change fibreCoordinate K x ((1 : K) ⊗ₜ[R] a) = Polynomial.X
  unfold fibreCoordinate
  rw [AlgHom.liftEquiv_tmul, one_smul, AlgHom.comp_apply, ha, Polynomial.coe_mapAlgHom,
    Polynomial.map_X]

private theorem tensor_lift_include_comp {B C : Type u} [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C] (f : B →ₐ[K] C) :
    lift (includeLeft.comp f) (includeRight.comp f) (fun _ _ => Commute.all _ _) =
      Algebra.TensorProduct.map f f := by
  apply AlgHom.ext
  intro z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro b c
    simp
  · intro b c hb hc
    rw [map_add, map_add, hb, hc]

private def bialgCoordinate {B : Type u} [CommRing B] [HopfAlgebra K B]
    (L : AdditiveLine K) (f : B →ₐ[K] Polynomial K)
    (hadd : ∀ (S : TestAlgebra K) (a b : S),
      coordinatePoint f S (a + b) = coordinatePoint f S a * coordinatePoint f S b)
    (hzero : ∀ S : TestAlgebra K, coordinatePoint f S 0 = 1) :
    letI := L.operations.hopf
    B →ₐc[K] Polynomial K := by
  letI := L.operations.hopf
  refine BialgHom.ofAlgHom f ?_ ?_
  · have h : (Polynomial.aeval (0 : K) : Polynomial K →ₐ[K] K) =
        Bialgebra.counitAlgHom K (Polynomial K) := by
      apply Polynomial.algHom_ext
      exact (Polynomial.aeval_X _).trans L.counit.symm
    have eq := congrArg WithConv.ofConv (hzero (CommAlgCat.of K K))
    change (Polynomial.aeval (0 : K)).comp f = _ at eq
    rw [h, AlgHom.convOne_def] at eq
    change (Bialgebra.counitAlgHom K (Polynomial K)).comp f =
      (AlgHom.id K K).comp (Bialgebra.counitAlgHom K B) at eq
    rw [AlgHom.id_comp] at eq
    exact eq
  · let P := Polynomial K
    let p : P →ₐ[K] P ⊗[K] P := includeLeft
    let q : P →ₐ[K] P ⊗[K] P := includeRight
    have hp : Polynomial.aeval (p Polynomial.X) = p := Polynomial.algHom_ext (Polynomial.aeval_X _)
    have hq : Polynomial.aeval (q Polynomial.X) = q := Polynomial.algHom_ext (Polynomial.aeval_X _)
    have hd : Polynomial.aeval (p Polynomial.X + q Polynomial.X) =
        Bialgebra.comulAlgHom K P :=
      Polynomial.algHom_ext ((Polynomial.aeval_X _).trans L.comultiplication.symm)
    have eq := hadd (CommAlgCat.of K (P ⊗[K] P)) (p Polynomial.X) (q Polynomial.X)
    apply AlgHom.ext
    intro b
    have he := congrArg (fun m : WithConv (B →ₐ[K] P ⊗[K] P) => m.ofConv b) eq
    change Polynomial.aeval (p Polynomial.X + q Polynomial.X) (f b) =
      (toConv ((Polynomial.aeval (p Polynomial.X)).comp f) *
        toConv ((Polynomial.aeval (q Polynomial.X)).comp f)).ofConv b at he
    rw [hp, hq, hd, AlgHom.convMul_apply] at he
    change _ = lift (p.comp f) (q.comp f) (fun _ _ => Commute.all _ _)
      (Bialgebra.comulAlgHom K B b) at he
    rw [show lift (p.comp f) (q.comp f) (fun _ _ => Commute.all _ _) =
      Algebra.TensorProduct.map f f from tensor_lift_include_comp f] at he
    exact he.symm

private theorem fibre_rootCoordinate {D : BasedRootDatum.{u}} (t : A →ₐc[R]
    MonoidAlgebra R (Multiplicative D.X)) (i : D.I) (g : A →ₐ[R] Polynomial R)
    (hg : Function.Surjective g)
    (hlaws : PolynomialPointLaws t (Multiplicative.ofAdd (D.datum.root i)) g) :
    IsFibreRootCoordinate t i g := by
  intro K _ _ _ Q e s E d ht hmon
  let α : Character Q.T.group := (d.val.indexEquiv i).val
  let χ := Multiplicative.ofAdd (D.datum.root i)
  have hm : characterMonomial (s.hom ≫ α) = (1 : K) ⊗ₜ[R] MonoidAlgebra.of R _ χ := by
    rw [show α = _ from (calibratedRootCharacter E d i).symm]
    exact hmon (D.datum.root i)
  let L := LinearAlgebraicGroups.Classification.Pinning.standardAdditiveLine K
  letI := L.operations.hopf
  let f := fibreCoordinate K g
  have hf := fibreCoordinate_surjective (K := K) g hg
  have hl : FibrePointLaws t χ f := polynomialPointLaws_on_fibre t χ g hlaws
  let x : L.group ⟶ Q.G.val := spectrumOfHopfHom (bialgCoordinate L f hl.1 hl.2.1) ≫ e.hom
  have hx : spectrumOfAlgHom f ≫ e.hom.hom.hom = x.hom.hom := rfl
  have hclosed : IsClosedImmersion x.hom.hom.left := by
    rw [← hx, Over.comp_left]
    letI : IsClosedImmersion (spectrumOfAlgHom f).left :=
      IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom f.toRingHom) hf
    letI := groupIso_left_isIso e
    infer_instance
  let V : ClosedSubgroup Q.G.val := ⟨L.group, x, hclosed⟩
  have hscalar := (scalarAction_calibration t χ Q.T α e s ht hm x f hx).2 hl.2.2
  have hV : IsRootSubgroup Q.T V α := by
    refine ⟨?_, ⟨L.operations, L.comultiplication, L.counit, L.antipode, ⟨Iso.refl _⟩⟩,
      ?_, ?_⟩
    · change Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))))
      exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
        (RingHom.smooth_algebraMap.mpr (show Algebra.Smooth K (Polynomial K) from
          Algebra.Smooth.of_equiv (MvPolynomial.uniqueAlgEquiv K (PUnit : Type))))
    · apply normalizes_of_point_conjugation Q.T V
      intro S t p
      obtain ⟨a, rfl⟩ := (additivePoints L S).surjective p
      refine ⟨additivePoints L S (CharacterPairing.characterValue α S t * a), ?_⟩
      simpa only [rootPoint_eq] using (hscalar S t a).symm
    · apply tangent_weight_of_scalarAction Q.T V α L (Iso.refl _)
      simpa only [Iso.refl_hom, Category.id_comp] using hscalar
  obtain ⟨U, hU, _, _, _, huniq⟩ :=
    ((rootSubgroups Q.G Q.reductive Q.T Q.split Q.maximal).2 α
      (d.val.indexEquiv i).property).2.2
  have h := huniq V hV
  obtain ⟨j, hj⟩ := subgroupOf_mutual_iso (A := V) (B := U) h.2 h.1
  refine ⟨U, L, j, hU, huniq, ?_, ?_⟩
  · rw [hj]
    exact hscalar
  · rw [hj]
    exact hx

end FibreComparison

section PolynomialTangents

open Polynomial

private theorem aeval_eps_coeff {B : Type u} [CommRing B] (p : Polynomial B) :
    Polynomial.aeval (DualNumber.eps : DualNumber B) p =
      (⟨p.coeff 0, p.coeff 1⟩ : DualNumber B) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, coeff_add, coeff_add]
    rfl
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_X, aeval_C]
    rw [C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
    have hpow : ∀ m : ℕ, (DualNumber.eps : DualNumber B) ^ (m + 2) = 0 := by
      intro m
      rw [pow_add, DualNumber.eps_pow_two, mul_zero]
    rcases n with _ | _ | n
    · change algebraMap B (DualNumber B) c * (DualNumber.eps : DualNumber B) ^ 0 = ⟨c, 0⟩
      rw [pow_zero, mul_one]
      rfl
    · change algebraMap B (DualNumber B) c * (DualNumber.eps : DualNumber B) ^ 1 = ⟨0, c⟩
      rw [pow_one]
      apply TrivSqZeroExt.ext
      · change c * 0 = 0
        exact mul_zero c
      · change c * 1 + 0 * 0 = c
        rw [mul_one, zero_mul, add_zero]
    · have h0 : n + 1 + 1 ≠ 0 := by omega
      have h1 : n + 1 + 1 ≠ 1 := by omega
      rw [hpow n, if_neg h0, if_neg h1]
      exact mul_zero _

variable {R K A X : Type u} [CommRing R] [Field K] [CommRing A]
  [Algebra R K] [HopfAlgebra R A] [CommGroup X]

private theorem generic_constant_coefficient (t : A →ₐc[R] MonoidAlgebra R X) (α : X)
    (f : K ⊗[R] A →ₐ[K] Polynomial K) (h : FibrePointLaws t α f) (a : A) :
    (restrictPoint f a).coeff 0 = algebraMap R K (Bialgebra.counitAlgHom R A a) := by
  have z := (restrict_fibrePointLaws t α f h K).2.1
  have eq := congrArg (fun p : WithConv (A →ₐ[R] K) => p.ofConv a) z
  rw [AlgHom.convOne_def] at eq
  change Polynomial.aeval (0 : K) (restrictPoint f a) =
    algebraMap R K (Bialgebra.counitAlgHom R A a) at eq
  simpa only [Polynomial.aeval_def, Polynomial.eval₂_at_zero, Algebra.algebraMap_self,
    RingHom.id_apply] using eq

private theorem generic_linear_coefficient_nonzero (f : K ⊗[R] A →ₐ[K] Polynomial K)
    (hf : Function.Surjective f) : ∃ a : A, (restrictPoint f a).coeff 1 ≠ 0 := by
  by_contra! h
  have hzero (z : K ⊗[R] A) : (f z).coeff 1 = 0 := by
    refine TensorProduct.inductionOn z ?_ ?_
    · intro k a
      have eq : f = (AlgHom.liftEquiv R K A (Polynomial K)) (restrictPoint f) :=
        (Equiv.apply_symm_apply _ _).symm
      rw [eq, AlgHom.liftEquiv_tmul, coeff_smul, h, smul_zero]
    · intro b c hb hc
      rw [map_add, coeff_add, hb, hc, add_zero]
  obtain ⟨z, hz⟩ := hf Polynomial.X
  exact one_ne_zero ((coeff_X_one (R := K)).symm.trans (hz ▸ hzero z))

end PolynomialTangents

section CalibratedCoordinates

open AdjointRepresentation (GroupPoints)
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open Polynomial

set_option backward.isDefEq.respectTransparency false

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  {D : BasedRootDatum.{u}}
private abbrev torusFibreInclusion {K X : Type u} [Field K] [Algebra R K] [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) :
    HopfSpectrum K (K ⊗[R] MonoidAlgebra R X) ⟶ HopfSpectrum K (K ⊗[R] A) :=
  spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id K K) t)

private theorem calibratedPullback {K : Type u} [Field K] [Algebra R K]
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)) (i : D.I)
    (Q : SplitBorelPair K) (e : HopfSpectrum K (K ⊗[R] A) ≅ Q.G.val)
    (s : HopfSpectrum K (K ⊗[R] MonoidAlgebra R (Multiplicative D.X)) ≅ Q.T.group)
    (E : AttachedDatum Q) (d : BasedIso D E.toBased)
    (ht : torusFibreInclusion (K := K) t ≫ e.hom = s.hom ≫ Q.T.inclusion)
    (hmon : ∀ χ : D.X, characterMonomial (s.hom ≫ Additive.toMul (d.val.weightEquiv χ)) =
      (1 : K) ⊗ₜ[R] MonoidAlgebra.of R _ (Multiplicative.ofAdd χ))
    {U : ClosedSubgroup Q.G.val} {L : AdditiveLine K}
    (p : RootCoordinate L Q.T U (d.val.indexEquiv i).val) :
    ∃ f : K ⊗[R] A →ₐ[K] Polynomial K, Function.Surjective f ∧
      FibrePointLaws t (Multiplicative.ofAdd (D.datum.root i)) f ∧
      spectrumOfAlgHom f ≫ e.hom.hom.hom = (p.val.hom ≫ U.inclusion).hom.hom := by
  let x := p.val.hom ≫ U.inclusion
  let y := x.hom.hom ≫ e.inv.hom.hom
  let f := affinePullback y
  have hSpec : spectrumOfAlgHom f = y := spectrum_affinePullback y
  have h : spectrumOfAlgHom f ≫ e.hom.hom.hom = x.hom.hom := by
    rw [hSpec, Category.assoc]
    have he := congrArg (fun g : Q.G.val ⟶ Q.G.val => g.hom.hom) e.inv_hom_id
    rw [Grp.comp_hom_hom, Grp.id_hom_hom] at he
    rw [he, Category.comp_id]
  have hclosed : IsClosedImmersion y.left := by
    change IsClosedImmersion ((p.val.hom.hom.hom ≫ U.inclusion.hom.hom) ≫ e.inv.hom.hom).left
    rw [Over.comp_left, Over.comp_left]
    letI : IsClosedImmersion U.inclusion.hom.hom.left := U.isClosedImmersion
    letI : IsIso p.val.hom.hom.hom.left := groupIso_left_isIso p.val
    letI : IsIso e.inv.hom.hom.left := groupIso_left_isIso e.symm
    exact IsClosedImmersion.comp
      (p.val.hom.hom.hom.left ≫ U.inclusion.hom.hom.left) e.inv.hom.hom.left
  refine ⟨f, affinePullback_surjective y hclosed, ⟨?_, ?_, ?_⟩, h⟩
  · intro S
    exact (rootPoint_convolution_laws e x f h S).1
  · intro S
    exact (rootPoint_convolution_laws e x f h S).2
  · apply (scalarAction_calibration t _ Q.T _ e s ht _ x f h).mp p.property
    rw [← calibratedRootCharacter E d i]
    exact hmon (D.datum.root i)

private theorem linear_coefficient_of_tangent {K : Type u} [Field K] [Algebra R K]
    {L : AdditiveLine K} {G : GroupScheme K} (e : HopfSpectrum K (K ⊗[R] A) ≅ G)
    (x : L.group ⟶ G) (F : K ⊗[R] A →ₐ[K] Polynomial K)
    (hSpec : spectrumOfAlgHom F ≫ e.hom.hom.hom = x.hom.hom) (v : Tangent R A)
    (hq : rootPoint x (CommAlgCat.of K (DualNumber K)) DualNumber.eps =
      (tangentPoint e (extendTangent (K := K) v)).toMul.val) (a : A) :
    (restrictPoint F a).coeff 1 = algebraMap R K (v.val a).snd := by
  let S := CommAlgCat.of K (DualNumber K)
  let ev : Polynomial K →ₐ[K] DualNumber K := Polynomial.aeval DualNumber.eps
  have he := rootPoint_of_pullback e x F hSpec S DualNumber.eps
  have hcat : spectrumOfAlgHom (ev.comp F) ≫ e.hom.hom.hom =
      spectrumOfAlgHom (extendTangent (K := K) v).val ≫ e.hom.hom.hom :=
    he.trans hq
  have htangent : ev.comp F = (extendTangent (K := K) v).val :=
    spectrumOfAlgHom_injective ((cancel_mono e.hom.hom.hom).mp hcat)
  have h := DFunLike.congr_fun htangent ((1 : K) ⊗ₜ[R] a)
  change Polynomial.aeval (DualNumber.eps : DualNumber K) (restrictPoint F a) =
    (extendTangent (K := K) v).val ((1 : K) ⊗ₜ[R] a) at h
  rw [aeval_eps_coeff] at h
  exact (congrArg TrivSqZeroExt.snd h).trans (extendTangent_snd v a)

private theorem weightBasis_has_unit {X : Type u} [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (χ : X) (b : Tangent R A) (hb : IsWeightBasis t χ b)
    (w : Tangent R A) (hw : HasWeight t χ w) (h : ∃ a, (w.val a).snd = 1) :
    ∃ a, (b.val a).snd = 1 := by
  obtain ⟨c, hc, _⟩ := hb.2 w hw
  obtain ⟨a, ha⟩ := h
  refine ⟨algebraMap R A c * a, ?_⟩
  rw [map_mul, b.val.commutes, DualNumber.snd_mul]
  change c * (b.val a).snd + 0 * (b.val a).fst = 1
  rw [zero_mul, add_zero]
  exact (hc a).symm.trans ha

end CalibratedCoordinates

section IntegralConstruction

open AdjointRepresentation (GroupPoints)
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open Polynomial

attribute [local instance] integralAlgebraModule
set_option backward.isDefEq.respectTransparency false

variable {D : BasedRootDatum.{u}} {A : Type u} [CommRing A]
  [HopfAlgebra IntegralRing.{u} A]

private theorem integralRootCoordinate {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    [Algebra IntegralRing.{u} K] (t : A →ₐc[IntegralRing.{u}] MonoidAlgebra IntegralRing.{u} (Multiplicative D.X))
    (smooth : Smooth (HopfSpectrum IntegralRing.{u} A).X.hom) (fibre : HasFibreDatum D t K)
    (pin : ↥D.base.support → Tangent IntegralRing.{u} A)
    (pin_basis : ∀ j : ↥D.base.support,
      IsWeightBasis t (Multiplicative.ofAdd (D.datum.root j.val)) (pin j))
    (i : D.I) :
    ∃ g : A →ₐ[IntegralRing.{u}] Polynomial IntegralRing.{u}, Function.Surjective g ∧
      PolynomialPointLaws t (Multiplicative.ofAdd (D.datum.root i)) g ∧
      (∀ hi : i ∈ D.base.support, (Polynomial.aeval (DualNumber.eps : DualNumber IntegralRing.{u})).comp g =
        (pin ⟨i, hi⟩).val) := by
  classical
  letI : IsDomain IntegralRing.{u} := integralRing_isDomain
  letI : IsPrincipalIdealRing IntegralRing.{u} := integralRing_isPrincipalIdealRing
  letI : Algebra.Smooth IntegralRing.{u} A := modelSmoothAlgebra smooth
  let χ := Multiplicative.ofAdd (D.datum.root i)
  have hχ : χ ≠ 1 := D.datum.ne_zero i
  have hR := integralRing_algebraMap_injective K
  obtain ⟨Q, e, s, E, d, ht, hmon⟩ := fibre
  have hfibre : HasFibreDatum D t K := ⟨Q, e, s, E, d, ht, hmon⟩
  let j := d.val.indexEquiv i
  obtain ⟨U, hU, _, _, ⟨L, x, hx⟩, _⟩ :=
    ((rootSubgroups Q.G Q.reductive Q.T Q.split Q.maximal).2 j.val j.property).2.2
  obtain ⟨f, hf, hfl, _⟩ := calibratedPullback t i Q e s E d ht hmon
    (show RootCoordinate L Q.T U j.val from ⟨x, hx⟩)
  have hproj (a : A) :
      (restrictPoint f (torusWeightProjection t χ a)).coeff 1 = (restrictPoint f a).coeff 1 := by
    have h := genericWeightProjection t χ (rootPowers_injective i) f hfl a 1
    rw [pow_one] at h
    rw [h, coeff_monomial, if_pos rfl]
  obtain ⟨w, hw, hwa⟩ := primitiveTangent_of_rootPolynomial t χ hχ (restrictPoint f)
    (generic_constant_coefficient t χ f hfl) (generic_linear_coefficient_nonzero f hf) hproj
  have hv : ∃ v : Tangent IntegralRing.{u} A, HasWeight t χ v ∧ (∃ a, (v.val a).snd = 1) ∧
      ∀ hi : i ∈ D.base.support, v = pin ⟨i, hi⟩ := by
    by_cases hi : i ∈ D.base.support
    · let b := pin ⟨i, hi⟩
      have hb := pin_basis ⟨i, hi⟩
      exact ⟨b, hb.1, weightBasis_has_unit t χ b hb w hw hwa, fun _ => rfl⟩
    · exact ⟨w, hw, hwa, fun h => (hi h).elim⟩
  obtain ⟨v, hv, hva, hp⟩ := hv
  have hnonzero := extendTangent_has_nonzero_coefficient (K := K) v
    (by obtain ⟨a, ha⟩ := hva; exact ⟨a, ha ▸ one_ne_zero⟩) hR
  have hwgt : tangentPoint e (extendTangent (K := K) v) ∈
      CharacterPairing.adjointWeightVectors Q.T j.val := by
    apply tangentPoint_weight t χ v hv Q.T j.val e s ht
    rw [← calibratedRootCharacter E d i]
    exact hmon (D.datum.root i)
  let wK : RootVector Q.T j.val :=
    ⟨tangentPoint e (extendTangent (K := K) v), hwgt, tangentPoint_ne_zero e _ hnonzero⟩
  obtain ⟨Evec, hvec, _⟩ :=
    LinearAlgebraicGroups.Classification.Pinning.coordinateVectors L Q j U hU
  let q := Evec.symm wK
  have hq : rootPoint (q.val.hom ≫ U.inclusion) (CommAlgCat.of K (DualNumber K)) DualNumber.eps =
      (tangentPoint e (extendTangent (K := K) v)).toMul.val := by
    have h := (hvec q).symm
    rw [show Evec q = wK from Equiv.apply_symm_apply _ _] at h
    exact h
  obtain ⟨F, _, hF, hSpec⟩ := calibratedPullback t i Q e s E d ht hmon q
  have hlinear (a : A) : (restrictPoint F a).coeff 1 = algebraMap IntegralRing.{u} K (v.val a).snd :=
    linear_coefficient_of_tangent e (q.val.hom ≫ U.inclusion) F hSpec v hq a
  have hconst := generic_constant_coefficient t χ F hF
  have hc (ψ : Multiplicative D.X) (hψ : ψ ≠ 1)
      (hn : ∀ j, ψ ≠ Multiplicative.ofAdd (D.datum.root j)) (a : A) :=
    modelWeightProjection_mem_augmentationSquare t smooth K hfibre ψ hψ hn a
  obtain ⟨g, ⟨hg, hgs⟩, _⟩ := integralRootPolynomial t i (restrictPoint F) hR hconst
    (fun a => ⟨(v.val a).snd, (hlinear a).symm⟩)
    (by obtain ⟨a, ha⟩ := hva; exact ⟨a, by rw [hlinear, ha, map_one]⟩)
    (genericWeightProjection t χ (rootPowers_injective i) F hF) hc
  have hFg : fibreCoordinate K g = F := restrictPoint.injective
    ((restrict_fibreCoordinate g).trans hg)
  refine ⟨g, hgs, polynomialPointLaws_of_fibre t χ g hR (by simpa only [hFg] using hF), ?_⟩
  intro hi
  rw [← hp hi]
  apply AlgHom.ext
  intro a
  have he (n : ℕ) : algebraMap IntegralRing.{u} K ((g a).coeff n) = (restrictPoint F a).coeff n := by
    have h := congrArg (fun p : Polynomial K => p.coeff n) (DFunLike.congr_fun hg a)
    simpa only [AlgHom.comp_apply, Polynomial.coeff_mapAlgHom_apply,
      Algebra.ofId_apply] using h
  change Polynomial.aeval (DualNumber.eps : DualNumber IntegralRing.{u}) (g a) = v.val a
  rw [aeval_eps_coeff]
  apply TrivSqZeroExt.ext
  · apply hR
    rw [show (v.val a).fst = Bialgebra.counitAlgHom IntegralRing.{u} A a from DFunLike.congr_fun v.property a]
    exact (he 0).trans (hconst a)
  · exact hR ((he 1).trans (hlinear a))

/-- Each root has an integral additive coordinate, compatible with the marked
torus, the simple tangent bases, and the root subgroup of every geometric fibre. -/
theorem integralRootCoordinates : IntegralRootCoordinates.{u} := by
  classical
  intro D A _ _ t _ smooth _ fibre pin pin_basis
  letI : CharZero (ULift.{u} ℚ) :=
    charZero_of_injective_ringHom (f := (ULift.ringEquiv (R := ℚ)).symm.toRingHom)
      (ULift.ringEquiv (R := ℚ)).symm.injective
  let K := AlgebraicClosure (ULift.{u} ℚ)
  letI : CharZero K := Algebra.charZero_of_charZero (ULift.{u} ℚ) K
  letI : Algebra IntegralRing.{u} K := ((Int.castRingHom K).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
  choose g hg laws hpin using integralRootCoordinate (K := K) t smooth (fibre K) pin pin_basis
  exact ⟨g, hg, (fun i => (laws i).1), (fun i => (laws i).2.1), (fun i => (laws i).2.2),
    (fun i => hpin i.val i.property), (fun i => fibre_rootCoordinate t i (g i) (hg i) (laws i))⟩

end IntegralConstruction

end

end LinearAlgebraicGroups.Classification.IntegralRootCoordinates
