import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertSerreDimension
import MathGenome.Internal.AlgebraCore.P103.Ch06.DimensionConventions
import MathGenome.Internal.AlgebraCore.P103.Ch06.NoetherNormalization
import MathGenome.Internal.AlgebraCore.P103.Ch06.LinearGradedNormalization
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertSerreLength
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertAnnihilatorQuotient
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertScalarExtension
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertNormalizedGrowth
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.Basic
import Lean.Elab.Tactic.Omega

namespace P103.HilbertSerreDimension

open P103.Graded P103.HilbertSerreLength
open P103.Specs.Ch06.LinearGradedNormalization
open P103.Specs.Ch06.DimensionConventions

universe u v w x

/-- Projection onto degree i+j of a scalar acting on a homogeneous vector. -/
theorem decompose_smul_homogeneous {A : Type v} {M : Type w}
    [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (i j : ℤ) (a : A) (m : U.piece j) :
    (DirectSum.decompose U.piece (a • (m : M)) (i + j) : M) =
      (DirectSum.decompose G.piece a i : A) • (m : M) := by
  classical
  induction a using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | add a b ha hb =>
    simp only [add_smul, DirectSum.decompose_add]
    change (DirectSum.decompose U.piece (a • (m : M)) (i + j) : M) +
        (DirectSum.decompose U.piece (b • (m : M)) (i + j) : M) =
      ((DirectSum.decompose G.piece a i : A) +
        (DirectSum.decompose G.piece b i : A)) • (m : M)
    rw [add_smul, ha, hb]
  | @homogeneous n a =>
    have hm : (a : A) • (m : M) ∈ U.piece (n + j) :=
      SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) a.2 m.2
    by_cases hn : n = i
    · subst n
      rw [DirectSum.decompose_of_mem_same U.piece hm,
        DirectSum.decompose_of_mem_same G.piece a.2]
    · rw [DirectSum.decompose_of_mem_ne U.piece hm (by omega),
        DirectSum.decompose_of_mem_ne G.piece a.2 hn, zero_smul]

theorem annihilator_homogeneous :
    Specs.P103.HilbertSerreDimension.annihilatorHomogeneousType.{v,w} := by
  intro A M _ _ _ G U a ha i
  rw [Module.mem_annihilator] at ha ⊢
  intro m
  induction m using DirectSum.Decomposition.inductionOn U.piece with
  | zero => exact smul_zero _
  | add m n hm hn => rw [smul_add, hm, hn, add_zero]
  | @homogeneous j m =>
    have h := decompose_smul_homogeneous G U i j a m
    rw [ha m] at h
    simpa using h.symm

section Components

variable (k : Type u) {A : Type v} {M : Type w}
  [Field k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- The structural map into the actual degree-zero ring. -/
def baseScalarMap (G : NonnegativeGrading A) (hzero : Connected k G) :
    k →+* Base G where
  toFun a := ⟨algebraMap k A a, (hzero _).mpr ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem baseScalarMap_surjective (G : NonnegativeGrading A) (hzero : Connected k G) :
    Function.Surjective (baseScalarMap k G hzero) := by
  intro a
  obtain ⟨b, hb⟩ := (hzero a).mp a.2
  exact ⟨b, Subtype.ext hb⟩

theorem base_isArtinian (G : NonnegativeGrading A) (hzero : Connected k G) :
    IsArtinianRing (Base G) := by
  letI : Algebra k (Base G) := (baseScalarMap k G hzero).toAlgebra
  let : Module.Finite k (Base G) := Module.Finite.of_surjective
    (Algebra.linearMap k (Base G)) (baseScalarMap_surjective k G hzero)
  exact IsArtinianRing.of_finite k (Base G)

theorem finite_components : Specs.P103.HilbertSerreDimension.finiteComponentsType.{u,v,w} := by
  intro k A M _ _ _ _ _ _ _ _ _ G U hzero hstd
  letI : Algebra k (Base G) := (baseScalarMap k G hzero).toAlgebra
  have hsurj : Function.Surjective (algebraMap k (Base G)) :=
    baseScalarMap_surjective k G hzero
  let : Module.Finite k (Base G) :=
    Module.Finite.of_surjective (Algebra.linearMap k (Base G)) hsurj
  let : IsScalarTower k (Base G) M :=
    IsScalarTower.of_algebraMap_smul fun a m => by
      change (algebraMap k A a) • m = a • m
      exact algebraMap_smul A a m
  let : Algebra.FiniteType k A :=
    P103.Ch06.LinearGradedNormalization.finiteType_of_standard G hzero hstd
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hfin (j : ℤ) : Module.Finite k (fieldComponent k G U hzero j) := by
    letI : Module (Base G) (fieldComponent k G U hzero j) :=
      (component G U j).module
    let : IsScalarTower k (Base G) (fieldComponent k G U hzero j) :=
      ⟨fun a b m => Subtype.ext (smul_assoc a b (m : M))⟩
    let : Module.Finite (Base G) (fieldComponent k G U hzero j) :=
      component_finite_of_noetherian G U j
    exact Module.Finite.trans (Base G) (fieldComponent k G U hzero j)
  refine ⟨hfin, ?_⟩
  funext j
  letI : Module (Base G) (fieldComponent k G U hzero j) :=
    (component G U j).module
  let : IsScalarTower k (Base G) (fieldComponent k G U hzero j) :=
    ⟨fun a b m => Subtype.ext (smul_assoc a b (m : M))⟩
  let := hfin j
  have hlength := Module.length_eq_of_surjective
    (R := Base G) (M := fieldComponent k G U hzero j) hsurj
  rw [Module.length_eq_finrank] at hlength
  change (Module.finrank k (fieldComponent k G U hzero j) : ℤ) =
    ((Module.length (Base G) (fieldComponent k G U hzero j)).toNat : ℤ)
  rw [← hlength]
  simp

end Components

theorem base_change_dimension :
    Specs.P103.HilbertSerreDimension.baseChangeDimensionType.{u,v,x} := by
  intro k K C _ _ _ _ _ _ _
  obtain ⟨d, g, hinj, hfin, hdim⟩ := P103.Ch06.NoetherNormalization.normalization_map k C
  let gK := Algebra.TensorProduct.lTensor (S := K) K g
  have hgKinj : Function.Injective gK := by
    change Function.Injective (g.toLinearMap.lTensor K)
    exact Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hinj
  have hgKfin : gK.Finite :=
    RingHom.Finite.tensorProductMap (AlgHom.Finite.id k K) hfin
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin d) k K
  let f := gK.comp e.symm.toAlgHom
  have hfinf : f.Finite := hgKfin.comp e.symm.toRingEquiv.finite
  have hinjf : Function.Injective f := hgKinj.comp e.symm.injective
  have hdimK := P103.Ch04.IntegralDimension.dimension_eq
    (MvPolynomial (Fin d) K) (TensorProduct k K C) f.toRingHom hfinf.to_isIntegral
  rw [(RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hinjf] at hdimK
  exact (hdimK.trans ((ringKrullDim_eq_of_ringEquiv
    (RingEquiv.quotientBot (MvPolynomial (Fin d) K))).trans
    (P103.Ch06.PolynomialDimension.polynomial_dimension K d))).trans hdim.symm

theorem rational : Specs.P103.HilbertSerreDimension.rationalType.{u,v,w} := by
  intro k A M _ _ _ _ _ _ _ _ _ G U hzero hstd
  have := base_isArtinian k G hzero
  obtain ⟨hfinite, heq⟩ := finite_components k G U hzero hstd
  obtain ⟨_, b, p, e, q, hp, hred, hq, hz, hd⟩ :=
    P103.HilbertSerreLength.hilbert_serre G U hstd
  refine ⟨hfinite, b, p, e, q, ?_, hred, ?_, ?_, ?_⟩
  · rwa [heq]
  · rwa [heq]
  · simpa only [heq] using hz
  · intro he
    exact ⟨(hd he).1, (hd he).2.1⟩

/-- The reduced exponent is the dimension of the annihilator quotient.
The rational function field gives a uniform infinite-field reduction. -/
theorem dimension_eq_exponent (k : Type u) {A : Type v} {M : Type w}
    [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Nontrivial M] [Module.Finite A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (hzero : Connected k G) (hstd : Specs.P103.Graded.standardValue G)
    (b : ℤ) (p : Polynomial ℤ) (e : ℕ)
    (hp : RationalPresentation (hilbertFunction G U) b p e)
    (hred : e = 0 ∨ p.eval 1 ≠ 0) :
    moduleDimensionValue A M = (e : WithBot ℕ∞) := by
  let C := A ⧸ Module.annihilator A M
  letI : Module C M := Module.quotientAnnihilator (R := A) (M := M)
  obtain ⟨hC, hfaith, hfin, htower, _, GC, UC, hzeroC, hstdC,
    _, _, hcoeffC, hdimC⟩ := P103.HilbertAnnihilatorQuotient.quotient k G U hzero hstd
  letI : Nontrivial C := hC
  letI : FaithfulSMul C M := hfaith
  letI : Module.Finite C M := hfin
  letI : IsScalarTower k C M := htower
  obtain ⟨hK, hCK, hMK, hfinK, hfaithK, hdimK, GK, UK, hzeroK,
    hstdK, _, _, _, _, _, _, _, _, hcoeffK⟩ :=
    P103.HilbertScalarExtension.ratFunc_extension k GC UC hzeroC hstdC
  letI : Infinite (RatFunc k) := hK
  letI : Nontrivial (TensorProduct k (RatFunc k) C) := hCK
  letI : Nontrivial (TensorProduct k (RatFunc k) M) := hMK
  letI : Module.Finite (TensorProduct k (RatFunc k) C)
      (TensorProduct k (RatFunc k) M) := hfinK
  letI : FaithfulSMul (TensorProduct k (RatFunc k) C)
      (TensorProduct k (RatFunc k) M) := hfaithK
  have hpK : RationalPresentation (hilbertFunction GK UK) b p e := by
    rwa [hcoeffK, hcoeffC]
  calc
    moduleDimensionValue A M = ringKrullDim C := hdimC.symm
    _ = ringKrullDim (TensorProduct k (RatFunc k) C) := hdimK.symm
    _ = (e : WithBot ℕ∞) :=
      P103.HilbertNormalizedGrowth.normalized_growth
        (RatFunc k) GK UK hzeroK hstdK b p e hpK hred

/-- Hilbert--Serre over every field, with the pole order equal to the
module's actual Krull dimension and with the zero-dimensional boundary. -/
theorem hilbert_serre : Specs.P103.HilbertSerreDimension.hilbertSerreType.{u,v,w} := by
  intro k A M _ _ _ _ _ _ _ _ _ _ G U hzero hstd
  obtain ⟨hfinite, b, p, e, q, hp, hred, hq, hz, hd⟩ := rational k G U hzero hstd
  have heq := (finite_components k G U hzero hstd).2
  have hdim : moduleDimensionValue A M = (e : WithBot ℕ∞) :=
    dimension_eq_exponent k G U hzero hstd b p e (by rwa [← heq]) hred
  refine ⟨hfinite, e, b, p, q, hdim, hp, hred, hq, ?_, hd⟩
  intro he
  obtain ⟨hqzero, J, hJ⟩ := hz he
  letI : IsArtinianRing (Base G) := base_isArtinian k G hzero
  refine ⟨hqzero, J, fun j hj => ?_⟩
  apply P103.HilbertNormalizedGrowth.piece_eq_bot_of_hilbertFunction_eq_zero G U hstd j
  rw [← heq]
  exact hJ j hj

theorem finite_dimension : Specs.P103.HilbertSerreDimension.finiteDimensionType.{u,v,w} := by
  intro k A M _ _ _ _ _ _ _ G hzero hstd
  let : Algebra.FiniteType k A :=
    P103.Ch06.LinearGradedNormalization.finiteType_of_standard G hzero hstd
  have hproper : Module.annihilator A M ≠ ⊤ := by
    intro h
    have : Subsingleton M := Module.annihilator_eq_top_iff.mp h
    exact not_nontrivial M inferInstance
  let : Nontrivial (A ⧸ Module.annihilator A M) :=
    Submodule.Quotient.nontrivial_iff.mpr hproper
  obtain ⟨d, _, _, _, hd⟩ := P103.Ch06.NoetherNormalization.normalization_map
    k (A ⧸ Module.annihilator A M)
  exact ⟨d, hd⟩

theorem zero : Specs.P103.HilbertSerreDimension.zeroType.{u,v,w} := by
  intro k A M _ _ _ _ _ _ _ _ G U hzero
  have h : fieldHilbertFunction k G U hzero = 0 := by
    funext j
    change (Module.finrank k (fieldComponent k G U hzero j) : ℤ) = 0
    exact_mod_cast Module.finrank_zero_of_subsingleton
      (R := k) (M := fieldComponent k G U hzero j)
  refine ⟨P103.Ch06.DimensionConventions.moduleDimension_zero A M, h, ?_⟩
  exact ⟨0, fun j hj => by simp [h]⟩

end P103.HilbertSerreDimension
