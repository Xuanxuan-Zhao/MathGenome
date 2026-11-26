import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.SplitContractingRadical
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.MvPolynomial.Ideal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open scoped TensorProduct CategoryTheory.MonObj LaurentPolynomial

universe u

namespace LinearAlgebraicGroups.Relative.SplitContractingRadical

open LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive)
open Specs.Unipotent (ClosedSeries IsFppfGroupQuotient closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics
open private affineSpectrum affinePointEquiv smooth_affine_iff affineSmooth_iff_lifts quotientMap
  conjugationCoaction orbitCoordinates_onWeight orbitCoordinates
  polynomialContract polynomialContract_restrict polynomialContract_natural
  polynomialContract_zero polynomialContract_one polynomialContract_mul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
open private weight_induction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private groupPresentation schemeKernel_exists quotientRepresentsImage
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private terminalIso onPoints onPoints_comp scheme_hom_spec kernel_points
  onPoints_injective onPoints_natural scheme_kernel_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private isReduced_of_smooth_algebra from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private spectrumPointsIso additiveRepresentation Representation.convolutionIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private abbrev AlgPoint (A : HopfAlgebraCategory k) (R : TestAlgebra k) :=
  (convolutionPoints A).obj R

/-- Pullback by the polynomial extension of an action that contracts to the identity. -/
private structure GradedContraction (A : HopfAlgebraCategory k) where
  action : A →ₐ[k] Polynomial A
  zero : ∀ a, (action a).coeff 0 = algebraMap k A (Coalgebra.counit (R := k) a)
  one : ∀ a, (action a).eval 1 = a
  homogeneous : ∀ n a, action ((action a).coeff n) =
    Polynomial.monomial n ((action a).coeff n)
  preserve_mul : ∀ (R : TestAlgebra k) (x y : AlgPoint A R),
    (toConv ((Polynomial.mapAlgHom (x * y).ofConv).comp action) :
        AlgPoint A (polynomialAlgebra R)) =
      (toConv ((Polynomial.mapAlgHom x.ofConv).comp action) :
        AlgPoint A (polynomialAlgebra R)) *
      (toConv ((Polynomial.mapAlgHom y.ofConv).comp action) :
        AlgPoint A (polynomialAlgebra R))

private theorem homPoint_comp {A B : HopfAlgebraCategory k} (e : specGroup A ⟶ specGroup B)
    (R : TestAlgebra k) (x : AlgPoint A R) :
    let f := ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage e).unop
    ((groupPointsFunctor k).map e).app R ((hopfSpecPointIso A).hom.app R x) =
      (hopfSpecPointIso B).hom.app R (toConv (x.ofConv.comp f.hom.toAlgHom)) := by
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let f := (ff.preimage e).unop
  change _ = (hopfSpecPointIso B).hom.app R (toConv (x.ofConv.comp f.hom.toAlgHom))
  have hf : specGroupMap f = e := ff.map_preimage e
  rw [← hf]
  apply Over.OverMorphism.ext
  exact (Spec.map_comp (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)
    (CommRingCat.ofHom x.ofConv.toRingHom)).symm

private theorem polynomial_coeff_of_weight {R : Type u} [CommRing R] (p : Polynomial R)
    (m : ℤ) (a : R)
    (h : Polynomial.toLaurent p = LaurentPolynomial.C a * LaurentPolynomial.T m) :
    (∀ n : ℕ, (n : ℤ) ≠ m → p.coeff n = 0) ∧
    (0 ≤ m → p = Polynomial.monomial m.toNat a) := by
  constructor
  · intro n hn
    have he := congrArg (fun l : LaurentPolynomial R ↦ l.coeff (n : ℤ)) h
    rw [← LaurentPolynomial.single_eq_C_mul_T] at he
    rw [LaurentPolynomial.coeff_toLaurent, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      ite_eq_right (Ne.symm hn)] at he
    change (p.toFinsupp.coeff.mapDomain Nat.castEmbedding) (Nat.castEmbedding n) = 0 at he
    rw [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective] at he
    exact he
  · intro hm
    apply Polynomial.toLaurent_injective
    rw [h, Polynomial.toLaurent_C_mul_T,
      Int.toNat_of_nonneg hm]

private theorem contraction_of_cocharacter (G : AffineAlgebraicGroup k)
    (c : Cocharacter G.val) (D : LimitDecomposition c)
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ D.contracting.group) :
    ∃ g : GradedContraction A, Specs.SplitContractingRadical.IsConjugationExtension D e g.action := by
  let I := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso e
  let E (R : TestAlgebra k) := (I.app R).groupIsoToMulEquiv
  let F (R : TestAlgebra k) (x : AlgPoint A R) : AlgPoint A (polynomialAlgebra R) :=
    (E _).symm (polynomialContract G.property.1 c D (E _ x))
  have hE {R S : TestAlgebra k} (a : R ⟶ S) (v : AlgPoint A R) :
      E S ((convolutionPoints A).map a v) = mapPoints a (E R v) :=
    congrArg (fun f ↦ GrpCat.Hom.hom f v) (I.hom.naturality a)
  have hF {R S : TestAlgebra k} (a : R ⟶ S) (x : AlgPoint A R) :
      F S ((convolutionPoints A).map a x) =
        (convolutionPoints A).map (mapPolynomial a) (F R x) := by
    apply (E _).injective
    simp only [F, MulEquiv.apply_symm_apply, hE, polynomialContract_natural]
  have hzero (R : TestAlgebra k) (x : AlgPoint A R) :
      (convolutionPoints A).map (polynomialEvaluate R 0) (F R x) = 1 := by
    apply (E _).injective
    rw [hE]
    simp only [F, MulEquiv.apply_symm_apply, polynomialContract_zero, map_one]
  have hone (R : TestAlgebra k) (x : AlgPoint A R) :
      (convolutionPoints A).map (polynomialEvaluate R 1) (F R x) = x := by
    apply (E _).injective
    rw [hE]
    simp only [F, MulEquiv.apply_symm_apply, polynomialContract_one]
  let R := CommAlgCat.of k A
  let id : AlgPoint A R := toConv (AlgHom.id k A)
  let p : A →ₐ[k] Polynomial A := (F R id).ofConv
  have hAt (S : TestAlgebra k) (x : AlgPoint A S) :
      F S x = toConv ((Polynomial.mapAlgHom x.ofConv).comp p) :=
    hF (CommAlgCat.ofHom x.ofConv) id
  have hOrbit : Specs.SplitContractingRadical.IsConjugationExtension D e p := by
    intro S a
    let x : AlgPoint A S := toConv a
    let j := e.hom ≫ D.contracting.inclusion
    change mapPoints (polynomialToLaurent S)
        (onPoints j _ ((hopfSpecPointIso A).hom.app _ (toConv ((Polynomial.mapAlgHom x.ofConv).comp p)))) =
      orbit c (onPoints j S ((hopfSpecPointIso A).hom.app S x))
    rw [← hAt]
    change mapPoints (polynomialToLaurent S) (onPoints D.contracting.inclusion _ (E _ (F S x))) =
      orbit c (onPoints D.contracting.inclusion S (E S x))
    rw [show E _ (F S x) = polynomialContract G.property.1 c D (E S x) from
      (E _).apply_symm_apply _]
    exact polynomialContract_restrict G.property.1 c D (E S x)
  refine ⟨⟨p, ?_, ?_, ?_, ?_⟩, hOrbit⟩
  · intro a
    have h := congrArg (fun g : AlgPoint A R ↦ g.ofConv a) (hzero R id)
    change (p a).eval₂ (RingHom.id A) 0 = _ at h
    rwa [Polynomial.eval₂_at_zero, RingHom.id_apply] at h
  · intro a
    exact congrArg (fun g : AlgPoint A R ↦ g.ofConv a) (hone R id)
  · obtain ⟨B, _, ⟨eG⟩⟩ := groupPresentation G
    let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
    let i := e.hom ≫ D.contracting.inclusion ≫ eG.inv
    let b : B ⟶ A := (ff.preimage i).unop
    have hb : specGroupMap b = i := ff.map_preimage _
    have hc : IsClosedImmersion (specGroupMap b).hom.hom.left := by
      rw [hb]
      let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
      let : IsIso e.hom.hom.hom.left := F.map_isIso e.hom
      let : IsIso eG.inv.hom.hom.left := F.map_isIso eG.inv
      let := D.contracting.isClosedImmersion
      change IsClosedImmersion (e.hom.hom.hom.left ≫
        D.contracting.inclusion.hom.hom.left ≫ eG.inv.hom.hom.left)
      infer_instance
    have hsurj : Function.Surjective b.hom.toAlgHom := (hopfMapClosedImmersion k b).mp hc
    let g : affineSpectrum (CommAlgCat.of k B) ≅ G.val.X :=
      (Grp.forget (SchemeOver k)).mapIso eG
    have point_eq (S : TestAlgebra k) (x : AlgPoint A S) :
        affinePointEquiv g S (x.ofConv.comp b.hom.toAlgHom) =
          (E S x : Points D.contracting.group.X S) ≫ D.contracting.inclusion.hom.hom := by
      have h := homPoint_comp i S x
      change ((groupPointsFunctor k).map i).app S ((hopfSpecPointIso A).hom.app S x) =
        (hopfSpecPointIso B).hom.app S (toConv (x.ofConv.comp b.hom.toAlgHom)) at h
      have he := congrArg (onPoints eG.hom S) h
      change onPoints eG.hom S (onPoints i S ((hopfSpecPointIso A).hom.app S x)) =
        affinePointEquiv g S (x.ofConv.comp b.hom.toAlgHom) at he
      rw [← onPoints_comp, show i ≫ eG.hom = e.hom ≫ D.contracting.inclusion by
        simp [i]] at he
      exact he.symm
    have hp : (polynomialToLaurent R).hom.comp (p.comp b.hom.toAlgHom) =
        orbitCoordinates g c b.hom.toAlgHom := by
      apply (affinePointEquiv g (laurentAlgebra R)).injective
      rw [← AlgHom.comp_assoc, orbitCoordinates, Equiv.apply_symm_apply]
      change affinePointEquiv g (laurentAlgebra R)
        (((convolutionPoints A).map (polynomialToLaurent R) (F R id)).ofConv.comp b.hom.toAlgHom)
        = _
      have hright : affinePointEquiv g R b.hom.toAlgHom =
          (E R id : Points D.contracting.group.X R) ≫ D.contracting.inclusion.hom.hom :=
        point_eq R id
      rw [point_eq, hE, hright]
      change mapPoints (polynomialToLaurent R)
        ((E _ (F R id) : Points D.contracting.group.X _) ≫ D.contracting.inclusion.hom.hom) =
        orbit c ((E R id : Points D.contracting.group.X R) ≫ D.contracting.inclusion.hom.hom)
      have he : E _ (F R id) = polynomialContract G.property.1 c D (E R id) :=
        (E _).apply_symm_apply _
      rw [he]
      exact polynomialContract_restrict G.property.1 c D (E R id)
    intro n a
    obtain ⟨v, rfl⟩ := hsurj a
    refine weight_induction (conjugationCoaction g c) (fun v ↦
      p ((p (b.hom.toAlgHom v)).coeff n) =
        Polynomial.monomial n ((p (b.hom.toAlgHom v)).coeff n)) ?_ (by simp) ?_
    · intro m w hw
      have he := DFunLike.congr_fun hp w
      rw [orbitCoordinates_onWeight (R := R) g c b.hom.toAlgHom hw] at he
      change Polynomial.toLaurent (p (b.hom.toAlgHom w)) =
        LaurentPolynomial.C (b.hom.toAlgHom w) * LaurentPolynomial.T m.down.toAdd at he
      obtain ⟨hcoeff, hpoly⟩ := polynomial_coeff_of_weight _ _ _ he
      by_cases hn : (n : ℤ) = m.down.toAdd
      · have hm : 0 ≤ m.down.toAdd := hn ▸ Int.natCast_nonneg n
        have hn' : m.down.toAdd.toNat = n := by omega
        have hh := hpoly hm
        rw [hn'] at hh
        rw [show (p (b.hom.toAlgHom w)).coeff n = b.hom.toAlgHom w by
          rw [hh, Polynomial.coeff_monomial, ite_eq_left rfl]]
        exact hh
      · rw [hcoeff n hn, map_zero, Polynomial.monomial_zero_right]
    · intro x y hx hy
      simp only [map_add, Polynomial.coeff_add, hx, hy]
  · intro S x y
    rw [← hAt, ← hAt, ← hAt]
    apply (E _).injective
    simp only [F, MulEquiv.apply_symm_apply, map_mul, polynomialContract_mul]

private theorem coeff_mul_first {R : Type u} [CommRing R] (d : ℕ) (hd : 0 < d)
    {p q : Polynomial R} (hp : ∀ i, 0 < i → i < d → p.coeff i = 0)
    (hq : ∀ i, 0 < i → i < d → q.coeff i = 0) :
    (p * q).coeff d = p.coeff 0 * q.coeff d + p.coeff d * q.coeff 0 := by
  let s := Finset.antidiagonal d
  let f (ij : ℕ × ℕ) := p.coeff ij.1 * q.coeff ij.2
  have h0 : (0, d) ∈ s := Finset.mem_antidiagonal.mpr (zero_add _)
  have h1 : (d, 0) ∈ s.erase (0, d) :=
    Finset.mem_erase.mpr ⟨by simp [hd.ne'], Finset.mem_antidiagonal.mpr (add_zero _)⟩
  rw [Polynomial.coeff_mul]
  change ∑ ij ∈ s, f ij = _
  rw [← Finset.sum_erase_add s f h0, ← Finset.sum_erase_add (s.erase (0, d)) f h1]
  have hz : ∑ ij ∈ (s.erase (0, d)).erase (d, 0), f ij = 0 := by
    apply Finset.sum_eq_zero
    intro ij h
    obtain ⟨h1, h0, hs⟩ := Finset.mem_erase.mp h |>.imp id Finset.mem_erase.mp
    have he := Finset.mem_antidiagonal.mp hs
    have ha : 0 < ij.1 := by
      by_contra! hn
      apply h0
      ext <;> omega
    have hb : 0 < ij.2 := by
      by_contra! hn
      apply h1
      ext <;> omega
    simp [f, hp _ ha (by omega), hq _ hb (by omega)]
  rw [hz, zero_add, add_comm]

private abbrev GradedContraction.coefficient {A : HopfAlgebraCategory k}
    (g : GradedContraction A) (d : ℕ) : A →ₗ[k] A :=
  ((Polynomial.lcoeff A d).restrictScalars k).comp g.action.toLinearMap

private theorem counit_first {A : HopfAlgebraCategory k} (g : GradedContraction A)
    {d : ℕ} (hd : 0 < d) (a : A) : Coalgebra.counit (R := k) (g.coefficient d a) = 0 := by
  have h := congrArg (fun p : Polynomial A ↦ p.coeff 0) (g.homogeneous d a)
  rw [g.zero, Polynomial.coeff_monomial, ite_eq_right hd.ne'] at h
  have hh := congrArg (Bialgebra.counitAlgHom k A) h
  rw [(Bialgebra.counitAlgHom k A).commutes, map_zero] at hh
  exact hh

private theorem first_leibniz {A : HopfAlgebraCategory k} (g : GradedContraction A)
    {d : ℕ} (hd : 0 < d) (hmin : ∀ i, 0 < i → i < d → ∀ a, g.coefficient i a = 0)
    (a b : A) :
    g.coefficient d (a * b) =
      Coalgebra.counit (R := k) a • g.coefficient d b +
        Coalgebra.counit (R := k) b • g.coefficient d a := by
  change (g.action (a * b)).coeff d = _
  rw [map_mul, coeff_mul_first (p := g.action a) (q := g.action b) d hd
    (fun i hi hj ↦ hmin i hi hj a) (fun i hi hj ↦ hmin i hi hj b), g.zero, g.zero]
  simp only [Algebra.smul_def]
  change _ = _ + algebraMap k A (Coalgebra.counit (R := k) b) * (g.action a).coeff d
  rw [mul_comm ((g.action a).coeff d)]
  rfl

/-- The first nonzero positive degree is primitive because the only contributing
degrees in a product at that degree are the two counit terms. -/
private theorem first_primitive {A : HopfAlgebraCategory k} (g : GradedContraction A)
    {d : ℕ} (hd : 0 < d) (hmin : ∀ i, 0 < i → i < d → ∀ a, g.coefficient i a = 0)
    (R : TestAlgebra k) (x y : AlgPoint A R) (a : A) :
    (x * y).ofConv (g.coefficient d a) =
      x.ofConv (g.coefficient d a) + y.ofConv (g.coefficient d a) := by
  let p (x : AlgPoint A R) : AlgPoint A (polynomialAlgebra R) :=
    toConv ((Polynomial.mapAlgHom x.ofConv).comp g.action)
  have hp (f : AlgPoint A R) (i : ℕ) (b : A) :
      ((p f).ofConv b).coeff i = f.ofConv (g.coefficient i b) :=
    Polynomial.coeff_mapAlgHom_apply _ _ _
  have h0 (f : AlgPoint A R) (b : A) :
      ((p f).ofConv b).coeff 0 = algebraMap k R (Coalgebra.counit (R := k) b) := by
    rw [hp, show g.coefficient 0 b = (g.action b).coeff 0 from rfl, g.zero,
      AlgHom.commutes]
  let l (v w : AlgPoint A (polynomialAlgebra R)) :=
    Algebra.TensorProduct.lift v.ofConv w.ofConv (fun _ _ ↦ .all _ _)
  have ht (t : A ⊗[k] A) :
      (l (p x) (p y) t).coeff d =
        (l (p x) 1 t).coeff d + (l 1 (p y) t).coeff d := by
    induction t using TensorProduct.inductionOn with
    | tmul b c =>
      simp only [l, Algebra.TensorProduct.lift_tmul]
      rw [coeff_mul_first d hd
        (fun i hi hj ↦ by rw [hp, hmin i hi hj, map_zero])
        (fun i hi hj ↦ by rw [hp, hmin i hi hj, map_zero])]
      change _ =
        ((p x).ofConv b * Polynomial.C (algebraMap k R (Coalgebra.counit (R := k) c))).coeff d +
          (Polynomial.C (algebraMap k R (Coalgebra.counit (R := k) b)) * (p y).ofConv c).coeff d
      rw [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, h0, h0, add_comm]
    | add t s ht hs =>
      simp only [map_add, Polynomial.coeff_add, ht, hs]
      abel
  rw [← hp (x * y), ← hp x, ← hp y]
  have hm : p (x * y) = p x * p y := g.preserve_mul R x y
  rw [hm]
  have hc (v w : AlgPoint A (polynomialAlgebra R)) :
      (v * w).ofConv a = l v w (Coalgebra.comul (R := k) a) :=
    AlgHom.convMul_apply v w a
  have h : ((p x * p y).ofConv a).coeff d =
      ((p x * 1).ofConv a).coeff d + ((1 * p y).ofConv a).coeff d := by
    rw [hc, hc, hc]
    exact ht _
  simpa only [mul_one, one_mul] using h

private abbrev spectrumGroup (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] :
    AffineAlgebraicGroup k :=
  (finiteTypeHopfSpec k).obj (op ⟨A, inferInstance⟩)

private abbrev additiveAlgebra (k : Type u) [Field k] : HopfAlgebraCategory k :=
  letI := StandardGroups.additiveHopf k
  CommHopfAlgCat.of k (Polynomial k)

private abbrev fromAlgebra {A : HopfAlgebraCategory k} {R : TestAlgebra k} :
    AlgPoint A R ≃* GroupPoints (specGroup A) R :=
  ((hopfSpecPointIso A).app R).groupIsoToMulEquiv

private theorem fromAlgebra_natural {A : HopfAlgebraCategory k} {R S : TestAlgebra k}
    (a : R ⟶ S) (x : AlgPoint A R) :
    fromAlgebra ((convolutionPoints A).map a x) = mapPoints a (fromAlgebra x) :=
  congrArg (fun f ↦ GrpCat.Hom.hom f x) ((hopfSpecPointIso A).hom.naturality a)

private def additiveEvaluation {A : HopfAlgebraCategory k} (v : A)
    (hv : ∀ (R : TestAlgebra k) (x y : AlgPoint A R),
      (x * y).ofConv v = x.ofConv v + y.ofConv v)
    (hz : Coalgebra.counit (R := k) v = 0) :
    convolutionPoints A ⟶ Specs.StandardGroups.additivePoints k where
  app R :=
    GrpCat.ofHom (X := (convolutionPoints A).obj R) (Y := (Specs.StandardGroups.additivePoints k).obj R)
      { toFun := fun x ↦ Multiplicative.ofAdd (x.ofConv v)
        map_one' := by
          change Multiplicative.ofAdd (algebraMap k R (Coalgebra.counit (R := k) v)) =
            Multiplicative.ofAdd (0 : R)
          rw [hz, map_zero]
        map_mul' := fun x y ↦ congrArg Multiplicative.ofAdd (hv R x y) }
  naturality _ _ a := by ext x; rfl

private def additiveMap {A : HopfAlgebraCategory k} [Algebra.FiniteType k A] (v : A)
    (hv : ∀ (R : TestAlgebra k) (x y : AlgPoint A R),
      (x * y).ofConv v = x.ofConv v + y.ofConv v)
    (hz : Coalgebra.counit (R := k) v = 0) :
    specGroup A ⟶ (StandardGroups.additiveGroup k).val :=
  (AffineAlgebraicGroup.groupHomEquiv (spectrumGroup A) (StandardGroups.additiveGroup k)).symm
    ((hopfSpecPointIso A).inv ≫ additiveEvaluation v hv hz ≫
      (StandardGroups.additiveGroupPointsIso k).inv)

private theorem additiveMap_apply {A : HopfAlgebraCategory k} [Algebra.FiniteType k A]
    (v : A) (hv) (hz) (R : TestAlgebra k) (x : AlgPoint A R) :
    (StandardGroups.additiveGroupPointsIso k).hom.app R
      (onPoints (additiveMap v hv hz) R (fromAlgebra x)) = Multiplicative.ofAdd (x.ofConv v) := by
  let E := StandardGroups.additiveGroupPointsIso k
  have h := scheme_hom_spec (G := spectrumGroup A) (H := StandardGroups.additiveGroup k)
    ((hopfSpecPointIso A).inv ≫ additiveEvaluation v hv hz ≫ E.inv) R (fromAlgebra x)
  change onPoints (additiveMap v hv hz) R (fromAlgebra x) = E.inv.app R
    ((additiveEvaluation v hv hz).app R ((hopfSpecPointIso A).inv.app R
      ((hopfSpecPointIso A).hom.app R x))) at h
  have h₁ := ((hopfSpecPointIso A).app R).hom_inv_id_apply x
  have h₂ := (E.app R).inv_hom_id_apply ((additiveEvaluation v hv hz).app R x)
  change (hopfSpecPointIso A).inv.app R ((hopfSpecPointIso A).hom.app R x) = x at h₁
  change E.hom.app R (E.inv.app R ((additiveEvaluation v hv hz).app R x)) = _ at h₂
  rw [h₁] at h
  exact (congrArg (fun y : GroupPoints (StandardGroups.additiveGroup k).val R ↦ E.hom.app R y)
    h).trans h₂

private theorem additive_coordinates {A : HopfAlgebraCategory k} [Algebra.FiniteType k A]
    (v : A) (hv) (hz) :
    let f : additiveAlgebra k ⟶ A :=
      ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage (additiveMap v hv hz)).unop
    f.hom.toAlgHom = Polynomial.aeval v := by
  let q := additiveMap v hv hz
  let f : additiveAlgebra k ⟶ A :=
    ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage q).unop
  let R := CommAlgCat.of k A
  let x : AlgPoint A R := toConv (AlgHom.id k A)
  have hq := additiveMap_apply v hv hz R x
  have he := homPoint_comp (A := A) (B := additiveAlgebra k) q R x
  change onPoints q R (fromAlgebra x) =
    (hopfSpecPointIso (additiveAlgebra k)).hom.app R (toConv f.hom.toAlgHom) at he
  rw [he] at hq
  have hX : f.hom.toAlgHom Polynomial.X = v := by
    let := StandardGroups.additiveHopf k
    have hcancel (F : TestAlgebra k ⥤ GrpCat.{u})
        (E : convolutionPoints (additiveAlgebra k) ≅ F) (y : AlgPoint (additiveAlgebra k) R) :
        (spectrumPointsIso E).hom.app R ((hopfSpecPointIso (additiveAlgebra k)).hom.app R y) =
          E.hom.app R y := by
      change E.hom.app R ((hopfSpecPointIso (additiveAlgebra k)).inv.app R
        ((hopfSpecPointIso (additiveAlgebra k)).hom.app R y)) = _
      exact congrArg (fun z : AlgPoint (additiveAlgebra k) R ↦ E.hom.app R z)
        (((hopfSpecPointIso (additiveAlgebra k)).app R).hom_inv_id_apply y)
    let E := Representation.convolutionIso (additiveRepresentation k)
    have h := (hcancel (Specs.StandardGroups.additivePoints k) E
      (toConv f.hom.toAlgHom)).symm.trans hq
    change Multiplicative.ofAdd (f.hom.toAlgHom Polynomial.X) = Multiplicative.ofAdd v at h
    exact Multiplicative.ofAdd.injective h
  ext
  simpa using hX

private theorem aeval_injective_of_weight {A : HopfAlgebraCategory k} [IsReduced A]
    (g : GradedContraction A) {d : ℕ} (hd : 0 < d) {v : A} (hv : v ≠ 0)
    (hw : g.action v = Polynomial.monomial d v) :
    Function.Injective (Polynomial.aeval v : Polynomial k →ₐ[k] A) := by
  have hi : Function.Injective (algebraMap k A) :=
    Function.LeftInverse.injective (fun a ↦ (Bialgebra.counitAlgHom k A).commutes a)
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  by_contra hne
  let P := p.map (algebraMap k A)
  let V : Polynomial A := Polynomial.monomial d v
  have hV : V.natDegree = d := Polynomial.natDegree_monomial_eq _ hv
  have hprod : P.leadingCoeff * V.leadingCoeff ^ P.natDegree ≠ 0 := by
    rw [show V.leadingCoeff = v from Polynomial.leadingCoeff_monomial _ _]
    have hunit : IsUnit P.leadingCoeff := by
      change IsUnit (p.map (algebraMap k A)).leadingCoeff
      rw [Polynomial.leadingCoeff_map_of_injective hi]
      exact (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hne)).map (algebraMap k A)
    intro he
    have he' : P.leadingCoeff * v ^ P.natDegree = P.leadingCoeff * 0 := he.trans (mul_zero _).symm
    exact hv (IsNilpotent.eq_zero ⟨_, hunit.mul_right_inj.mp he'⟩)
  have he : (P.comp V).coeff (P.natDegree * V.natDegree) ≠ 0 := by
    rw [Polynomial.coeff_comp_degree_mul_degree (hV.symm ▸ hd.ne')]
    exact hprod
  apply he
  have h : P.comp V = g.action (Polynomial.aeval v p) := by
    change (p.map (algebraMap k A)).comp V = g.action (Polynomial.aeval v p)
    rw [← AlgHom.comp_apply]
    have hm : g.action.comp (Polynomial.aeval v) = Polynomial.aeval V := by
      ext
      simp [hw, V]
    rw [hm, Polynomial.comp_eq_aeval]
    have hMap : ((Polynomial.aeval V : Polynomial A →ₐ[A] Polynomial A).restrictScalars k).comp
        (Polynomial.mapAlg k A) = Polynomial.aeval V := by
      ext : 1
      simp [Polynomial.mapAlg_eq_map]
    exact DFunLike.congr_fun hMap p
  rw [h, hp, map_zero, Polynomial.coeff_zero]

private theorem additiveMap_quotient {A : HopfAlgebraCategory k} [Algebra.FiniteType k A]
    [IsReduced A] (g : GradedContraction A) {d : ℕ} (hd : 0 < d)
    (v : A) (hv : v ≠ 0) (hw : g.action v = Polynomial.monomial d v)
    (hadd) (hz) :
    let q := additiveMap v hadd hz
    ∃ N : ClosedSubgroup (specGroup A),
      IsFppfGroupQuotient (G := spectrumGroup A) (Q := StandardGroups.additiveGroup k) N q ∧
        Function.Injective (v * ·) := by
  let q := additiveMap v hadd hz
  let f : additiveAlgebra k ⟶ A :=
    ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage q).unop
  have hq : specGroupMap f = q := (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage q
  have hi : Function.Injective f.hom := by
    change Function.Injective f.hom.toAlgHom
    rw [additive_coordinates v hadd hz]
    exact aeval_injective_of_weight g hd hv hw
  let b := CommRingCat.ofHom f.hom.toAlgHom.toRingHom
  have hff := hopfFaithfulFlatness k f hi
  have hflat := (flat_and_surjective_SpecMap_iff b).mpr hff
  have hregular : Function.Injective (v * ·) := by
    let ev : Polynomial k →ₐ[k] A := Polynomial.aeval v
    let : Algebra (Polynomial k) A := ev.toRingHom.toAlgebra
    have : Module.Flat (Polynomial k) A := by
      change ev.toRingHom.Flat
      rw [show ev = f.hom.toAlgHom from (additive_coordinates v hadd hz).symm]
      exact hff.flat
    have hX : (Polynomial.X : Polynomial k) ∈ nonZeroDivisors (Polynomial k) :=
      mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A) hX
    change Function.Injective (fun a : A => ev Polynomial.X * a) at h
    simpa only [ev, Polynomial.aeval_X] using h
  have : IsNoetherianRing (additiveAlgebra k) := Algebra.FiniteType.isNoetherianRing k _
  have hbft : b.hom.FiniteType := RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap k (additiveAlgebra k)) (by
      rw [show b.hom.comp (algebraMap k (additiveAlgebra k)) = algebraMap k A from
        f.hom.toAlgHom.comp_algebraMap]
      exact RingHom.finiteType_algebraMap.mpr inferInstance)
  have hfp : LocallyOfFinitePresentation (Spec.map b) :=
    (LocallyOfFinitePresentation.SpecMap_iff b).mpr (RingHom.FinitePresentation.of_finiteType.mp hbft)
  have hfac : IsImageFactorization (G := specGroup A)
      (H := (StandardGroups.additiveGroup k).val) q q (𝟙 (StandardGroups.additiveGroup k).val) := by
    rw [← hq]
    exact ⟨Category.comp_id _, hflat.1, hflat.2, hfp,
      inferInstanceAs (IsAffineHom (Spec.map b)), inferInstanceAs (IsClosedImmersion (𝟙 _))⟩
  let := (StandardGroups.additiveGroup k).property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists q
  exact ⟨N, ⟨hN, hfac.2.1, hfac.2.2.1, hfac.2.2.2.1, quotientRepresentsImage hfac hN⟩, hregular⟩

private theorem infinitesimalPoint {A : HopfAlgebraCategory k} (g : GradedContraction A)
    {d : ℕ} (hd : 0 < d) (hmin : ∀ i, 0 < i → i < d → ∀ a, g.coefficient i a = 0)
    {a : A} (hv : g.coefficient d a ≠ 0)
    {R : Type u} [CommRing R] [Algebra k R] (J : Ideal R) (hJ : J ^ 2 = ⊥)
    {r : R} (hr : r ∈ J) :
    ∃ z : AlgPoint A (CommAlgCat.of k R), z.ofConv (g.coefficient d a) = r ∧
      (convolutionPoints A).map (quotientMap J) z = 1 := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hv
  let δ : A →ₗ[k] k := l.comp (g.coefficient d)
  let ε := Bialgebra.counitAlgHom k A
  have δmul (x y : A) : δ (x * y) = ε x * δ y + ε y * δ x := by
    change l (g.coefficient d (x * y)) = _
    rw [first_leibniz g hd hmin, map_add, map_smul, map_smul]
    rfl
  have δscalar (t : k) : δ (algebraMap k A t) = 0 := by
    change l ((g.action (algebraMap k A t)).coeff d) = 0
    rw [g.action.commutes, show algebraMap k (Polynomial A) t =
      Polynomial.C (algebraMap k A t) from rfl, Polynomial.coeff_C, ite_eq_right hd.ne',
      map_zero]
  have hrr : r * r = 0 := by
    have hm := Ideal.mul_mem_mul hr hr
    simpa [← pow_two, hJ] using hm
  let z : A →ₐ[k] R :=
    { toFun := fun x ↦ algebraMap k R (ε x) + algebraMap k R (δ x) * r
      map_zero' := by simp
      map_one' := by
        have h : δ 1 = 0 := by simpa only [map_one] using δscalar 1
        rw [map_one ε, h, map_zero, zero_mul, add_zero, map_one]
      map_add' := by intro x y; simp only [map_add]; ring
      map_mul' := by
        intro x y
        rw [δmul, map_mul, map_mul, map_add, map_mul, map_mul]
        linear_combination -(algebraMap k R (δ x) * algebraMap k R (δ y)) * hrr
      commutes' := by
        intro t
        rw [ε.commutes, δscalar, map_zero, zero_mul, add_zero]
        rfl }
  refine ⟨toConv z, ?_, ?_⟩
  · have he : δ (g.coefficient d a) = 1 := by
      change l ((g.action ((g.action a).coeff d)).coeff d) = 1
      rw [g.homogeneous, Polynomial.coeff_monomial, ite_eq_left rfl]
      exact hl
    change algebraMap k R (Coalgebra.counit (R := k) (g.coefficient d a)) +
      algebraMap k R (δ (g.coefficient d a)) * r = r
    rw [counit_first g hd a, he, map_zero, map_one, zero_add, one_mul]
  · apply WithConv.ofConv_injective
    ext x
    change (Ideal.Quotient.mkₐ k J) (algebraMap k R (ε x) + algebraMap k R (δ x) * r) =
      algebraMap k (R ⧸ J) (ε x)
    rw [map_add, map_mul, (Ideal.Quotient.mkₐ k J).commutes]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]

/-- Correct an ambient lift by an infinitesimal point with the same additive
coordinate. The corrected point lies in the kernel and still lifts the given point. -/
private theorem firstKernel_smooth {A : HopfAlgebraCategory k} [Algebra.FiniteType k A]
    (g : GradedContraction A) (hA : Smooth (specGroup A).X.hom)
    {d : ℕ} (hd : 0 < d) (hmin : ∀ i, 0 < i → i < d → ∀ a, g.coefficient i a = 0)
    {a : A} (hv : g.coefficient d a ≠ 0)
    {N : ClosedSubgroup (specGroup A)}
    (hN : IsSchemeKernel
      (additiveMap (g.coefficient d a) (fun R x y ↦ first_primitive g hd hmin R x y a)
        (counit_first g hd a)) N) :
    Smooth N.group.X.hom := by
  let v := g.coefficient d a
  let q := additiveMap v (fun R x y ↦ first_primitive g hd hmin R x y a) (counit_first g hd a)
  let U := closedSubgroupAlgebraicGroup (G := spectrumGroup A) N
  let V := spectrumGroup A
  apply (affineSmooth_iff_lifts U.val.X U.property.1 U.property.2.1).mpr
  intro R _ _ J hJ n
  let R₀ := CommAlgCat.of k (R ⧸ J)
  let R₁ := CommAlgCat.of k R
  let π : R₁ ⟶ R₀ := quotientMap J
  obtain ⟨y, hy⟩ := (affineSmooth_iff_lifts V.val.X V.property.1 V.property.2.1).mp hA R J hJ
    (onPoints N.inclusion R₀ n)
  let x : AlgPoint A R₁ := fromAlgebra.symm y
  have hx : fromAlgebra x = y := MulEquiv.apply_symm_apply _ _
  have hqzero (S : TestAlgebra k) (t : AlgPoint A S) :
      onPoints q S (fromAlgebra t) = 1 ↔ t.ofConv v = 0 := by
    let e := ((StandardGroups.additiveGroupPointsIso k).app S).groupIsoToMulEquiv
    have he := additiveMap_apply v (fun R x y ↦ first_primitive g hd hmin R x y a)
      (counit_first g hd a) S t
    change e (onPoints q S (fromAlgebra t)) = Multiplicative.ofAdd (t.ofConv v) at he
    rw [← e.injective.eq_iff, he, map_one]
    rfl
  have hyq : onPoints q R₀ (fromAlgebra ((convolutionPoints A).map π x)) = 1 := by
    rw [fromAlgebra_natural, hx, show mapPoints π y = onPoints N.inclusion R₀ n from hy]
    exact (kernel_points q N hN R₀ _).mpr ⟨n, rfl⟩
  have hxJ : x.ofConv v ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp ((hqzero _ _).mp hyq)
  obtain ⟨z, hz, hzred⟩ := infinitesimalPoint g hd hmin hv J hJ hxJ
  let t : AlgPoint A R₁ := x * z⁻¹
  have hqt : onPoints q R₁ (fromAlgebra t) = 1 := by
    have hval : onPoints q R₁ (fromAlgebra x) = onPoints q R₁ (fromAlgebra z) := by
      apply ((StandardGroups.additiveGroupPointsIso k).app R₁).groupIsoToMulEquiv.injective
      change (StandardGroups.additiveGroupPointsIso k).hom.app R₁ (onPoints q R₁ (fromAlgebra x)) =
        (StandardGroups.additiveGroupPointsIso k).hom.app R₁ (onPoints q R₁ (fromAlgebra z))
      exact (additiveMap_apply v _ _ R₁ x).trans
        ((congrArg Multiplicative.ofAdd hz.symm).trans (additiveMap_apply v _ _ R₁ z).symm)
    change onPoints q R₁ (fromAlgebra (x * z⁻¹)) = 1
    rw [(fromAlgebra (A := A) (R := R₁)).map_mul, (fromAlgebra (A := A) (R := R₁)).map_inv,
      (onPoints q R₁).map_mul, (onPoints q R₁).map_inv, hval, mul_inv_cancel]
  obtain ⟨w, hw⟩ := (kernel_points q N hN R₁ _).mp hqt
  refine ⟨w, onPoints_injective N.inclusion N.isClosedImmersion R₀ ?_⟩
  change onPoints N.inclusion R₀ (((groupPointsFunctor k).obj N.group).map π w) =
    onPoints N.inclusion R₀ n
  rw [onPoints_natural, hw]
  change mapPoints π (fromAlgebra t) = onPoints N.inclusion R₀ n
  rw [← fromAlgebra_natural]
  have ht : (convolutionPoints A).map π t = (convolutionPoints A).map π x := by
    change ((convolutionPoints A).map π).hom (x * z⁻¹) = _
    rw [map_mul, map_inv]
    change _ * (((convolutionPoints A).map π) z)⁻¹ = _
    rw [hzred, inv_one, mul_one]
  rw [ht, fromAlgebra_natural, hx]
  exact hy

private theorem preserve_mul_of_surjective {A B : HopfAlgebraCategory k}
    (φ : A ⟶ B) (hφ : Function.Surjective φ.hom.toAlgHom)
    (g : GradedContraction A) (ψ : B →ₐ[k] Polynomial B)
    (hψ : ψ.comp φ.hom.toAlgHom = (Polynomial.mapAlgHom φ.hom.toAlgHom).comp g.action)
    (S : TestAlgebra k) (x y : AlgPoint B S) :
    (toConv ((Polynomial.mapAlgHom (x * y).ofConv).comp ψ) : AlgPoint B (polynomialAlgebra S)) =
      (toConv ((Polynomial.mapAlgHom x.ofConv).comp ψ) : AlgPoint B (polynomialAlgebra S)) *
      (toConv ((Polynomial.mapAlgHom y.ofConv).comp ψ) : AlgPoint B (polynomialAlgebra S)) := by
  let b := φ.hom.toAlgHom
  let restrict (T : TestAlgebra k) (t : AlgPoint B T) : AlgPoint A T :=
    toConv (t.ofConv.comp b)
  have restrict_inj (T : TestAlgebra k) : Function.Injective (restrict T) := by
    intro r s h
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro u
    obtain ⟨a, rfl⟩ := hφ u
    exact congrArg (fun x : AlgPoint A T ↦ x.ofConv a) h
  have restrict_mul (T : TestAlgebra k) (r s : AlgPoint B T) :
      restrict T (r * s) = restrict T r * restrict T s :=
    congrArg toConv (AlgHom.convMul_comp_bialgHom_distrib r s φ.hom)
  let P (t : AlgPoint B S) : AlgPoint B (polynomialAlgebra S) :=
    toConv ((Polynomial.mapAlgHom t.ofConv).comp ψ)
  let F (t : AlgPoint A S) : AlgPoint A (polynomialAlgebra S) :=
    toConv ((Polynomial.mapAlgHom t.ofConv).comp g.action)
  have hcomp (t : AlgPoint B S) : restrict (polynomialAlgebra S) (P t) = F (restrict S t) := by
    apply WithConv.ofConv_injective
    change ((Polynomial.mapAlgHom t.ofConv).comp ψ).comp b =
      (Polynomial.mapAlgHom (t.ofConv.comp b)).comp g.action
    rw [AlgHom.comp_assoc, hψ, ← AlgHom.comp_assoc, Polynomial.mapAlgHom_comp]
  change P (x * y) = P x * P y
  apply restrict_inj
  rw [hcomp, restrict_mul, restrict_mul, hcomp, hcomp]
  exact g.preserve_mul S (restrict S x) (restrict S y)

private theorem contraction_on_kernel {A : HopfAlgebraCategory k} [Algebra.FiniteType k A]
    (g : GradedContraction A) {d : ℕ} {v : A} (hv : g.action v = Polynomial.monomial d v)
    (hadd) (hz) {N : ClosedSubgroup (specGroup A)}
    (hN : IsSchemeKernel (additiveMap v hadd hz) N) :
    ∃ (B : HopfAlgebraCategory k) (_ : Algebra.FiniteType k B)
      (_ : specGroup B ≅ N.group) (b : A →ₐ[k] B),
      Function.Surjective b ∧ b v = 0 ∧ RingHom.ker b.toRingHom = Ideal.span {v} ∧
        ∃ gB : GradedContraction B,
          gB.action.comp b = (Polynomial.mapAlgHom b).comp g.action := by
  let q := additiveMap v hadd hz
  obtain ⟨B, hB, ⟨e⟩⟩ := groupPresentation (closedSubgroupAlgebraicGroup (G := spectrumGroup A) N)
  let i := e.hom ≫ N.inclusion
  let φ : A ⟶ B := ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage i).unop
  let b := φ.hom.toAlgHom
  have hφ : specGroupMap φ = i :=
    (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage i
  have hb : Function.Surjective b := by
    apply (hopfMapClosedImmersion k φ).mp
    rw [hφ]
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    let : IsIso e.hom.hom.hom.left := F.map_isIso e.hom
    let := N.isClosedImmersion
    change IsClosedImmersion (e.hom.hom.hom.left ≫ N.inclusion.hom.hom.left)
    infer_instance
  have hpoint (R : TestAlgebra k) (x : AlgPoint B R) :
      onPoints N.inclusion R (onPoints e.hom R (fromAlgebra x)) =
        fromAlgebra (toConv (x.ofConv.comp b)) :=
    homPoint_comp i R x
  have hzero (R : TestAlgebra k) (x : AlgPoint A R) :
      onPoints q R (fromAlgebra x) = 1 ↔ x.ofConv v = 0 := by
    let E := ((StandardGroups.additiveGroupPointsIso k).app R).groupIsoToMulEquiv
    have hx : E (onPoints q R (fromAlgebra x)) = Multiplicative.ofAdd (x.ofConv v) :=
      additiveMap_apply v hadd hz R x
    rw [← E.injective.eq_iff, hx, map_one]
    rfl
  let R := CommAlgCat.of k B
  let x : AlgPoint B R := toConv (AlgHom.id k B)
  have hbv : b v = 0 := by
    apply (hzero R (toConv b)).mp
    have h := hpoint R x
    change onPoints N.inclusion R (onPoints e.hom R (fromAlgebra x)) =
      fromAlgebra (toConv b) at h
    rw [← h]
    exact (kernel_points q N hN R _).mpr ⟨_, rfl⟩
  have factor (S : TestAlgebra k) (p : A →ₐ[k] S) (hp : p v = 0) :
      ∃ ψ : B →ₐ[k] S, ψ.comp b = p := by
    obtain ⟨y, hy⟩ := (kernel_points q N hN S (fromAlgebra (toConv p))).mp
      ((hzero S (toConv p)).mpr hp)
    let z : AlgPoint B S := fromAlgebra.symm (onPoints e.inv S y)
    have hz' : onPoints e.hom S (fromAlgebra z) = y := by
      change onPoints e.hom S (fromAlgebra (fromAlgebra.symm (onPoints e.inv S y))) = y
      rw [MulEquiv.apply_symm_apply, ← onPoints_comp, Iso.inv_hom_id]
      rfl
    refine ⟨z.ofConv, ?_⟩
    apply WithConv.toConv_injective
    apply (fromAlgebra (A := A) (R := S)).injective
    rw [← hpoint, hz', hy]
  have hker : RingHom.ker b.toRingHom = Ideal.span {v} := by
    let J : Ideal A := Ideal.span {v}
    let p := Ideal.Quotient.mkₐ k J
    have hpv : p v = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    obtain ⟨ψ, hψ⟩ := factor (CommAlgCat.of k (A ⧸ J)) p hpv
    apply le_antisymm
    · intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change p a = 0
      rw [← hψ, AlgHom.comp_apply, show b a = 0 from ha, map_zero]
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbv)
  let p : A →ₐ[k] Polynomial B := (Polynomial.mapAlgHom b).comp g.action
  have hpv : p v = 0 := by
    simp [p, hv, hbv]
  obtain ⟨ψ, hψ⟩ := factor (polynomialAlgebra R) p hpv
  have hmap (j : ℕ) (a : A) : (ψ (b a)).coeff j = b ((g.action a).coeff j) := by
    have h := congrArg (fun q : Polynomial B ↦ q.coeff j) (DFunLike.congr_fun hψ a)
    exact h.trans (Polynomial.coeff_mapAlgHom_apply _ _ _)
  refine ⟨B, hB, e, b, hb, hbv, hker, ⟨ψ, ?_, ?_, ?_, ?_⟩, hψ⟩
  · intro u
    obtain ⟨a, rfl⟩ := hb u
    rw [hmap, g.zero, AlgHom.commutes]
    congr 1
    exact (CoalgHomClass.counit_comp_apply φ.hom a).symm
  · intro u
    obtain ⟨a, rfl⟩ := hb u
    change (ψ.comp b a).eval 1 = b a
    rw [hψ]
    change ((g.action a).map b.toRingHom).eval 1 = _
    rw [Polynomial.eval_map, ← map_one b.toRingHom, Polynomial.eval₂_at_apply, g.one]
    rfl
  · intro j u
    obtain ⟨a, rfl⟩ := hb u
    rw [hmap]
    change ψ.comp b ((g.action a).coeff j) = _
    rw [hψ]
    change Polynomial.mapAlgHom b (g.action ((g.action a).coeff j)) = _
    rw [g.homogeneous, Polynomial.mapAlgHom_monomial]
  · exact preserve_mul_of_surjective φ hb g ψ hψ

section PolynomialCoordinates

variable {A B C : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Nontrivial C] [Algebra k C]

private theorem aevalTower_injective_of_regular
    (b : A →ₐ[k] B) (s : C →ₐ[k] A) (hs : Function.Injective (b.comp s))
    (v : A) (hv : b v = 0) (hreg : Function.Injective (v * ·)) :
    Function.Injective (Polynomial.aevalTower s v) := by
  let f := Polynomial.aevalTower s v
  have hconst (p : Polynomial C) : b (f p) = b (s (p.coeff 0)) := by
    change b.toRingHom (p.eval₂ s.toRingHom v) = _
    rw [Polynomial.hom_eval₂, show b.toRingHom v = 0 from hv, Polynomial.eval₂_at_zero]
    rfl
  apply (injective_iff_map_eq_zero _).mpr
  change ∀ p, f p = 0 → p = 0
  suffices h : ∀ n (p : Polynomial C), p.natDegree = n → f p = 0 → p = 0 by
    exact fun p hp => h _ p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hp hf
    have hz : p.coeff 0 = 0 := hs (by simpa [hf] using (hconst p).symm)
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr hz
    by_cases hq : q = 0
    · simp [hq]
    · rw [Polynomial.natDegree_X_mul hq] at hp
      have heq : q = 0 := ih _ (by omega) q rfl (hreg (by simpa [f] using hf))
      exact (hq heq).elim

/-- A homogeneous regular element gives one more polynomial coordinate
if its quotient has polynomial coordinates with homogeneous lifts. -/
private theorem polynomialCoordinates_succ {n : ℕ}
    (aA : A →ₐ[k] Polynomial A) (hone : ∀ x, (aA x).eval 1 = x)
    (b : A →ₐ[k] B)
    (v : A) {d : ℕ} (hd : 0 < d) (hw : aA v = Polynomial.monomial d v)
    (hreg : Function.Injective (v * ·)) (hkill : b v = 0)
    (hker : RingHom.ker b.toRingHom = Ideal.span {v})
    (e : MvPolynomial (Fin n) k ≃ₐ[k] B) (w : Fin n → ℕ)
    (x : Fin n → A) (hx : ∀ i, b (x i) = e (MvPolynomial.X i))
    (hgrade : ∀ i, aA (x i) = Polynomial.monomial (w i) (x i)) :
    Function.Bijective (MvPolynomial.aeval (Fin.cases v x) : MvPolynomial (Fin (n + 1)) k →ₐ[k] A) := by
  classical
  let s : MvPolynomial (Fin n) k →ₐ[k] A := MvPolynomial.aeval x
  have hs : b.comp s = e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa [s] using hx i
  let f : MvPolynomial (Fin (n + 1)) k →ₐ[k] A := MvPolynomial.aeval (Fin.cases v x)
  have hf : f = (Polynomial.aevalTower s v).comp (MvPolynomial.finSuccEquiv k n).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [f, MvPolynomial.finSuccEquiv_X_zero]
    · simp [f, s, MvPolynomial.finSuccEquiv_X_succ]
  change Function.Bijective f
  refine ⟨?_, ?_⟩
  · rw [hf]
    exact (aevalTower_injective_of_regular b s (hs ▸ e.injective) v hkill hreg).comp
      (MvPolynomial.finSuccEquiv k n).injective
  · let w' : Fin (n + 1) → ℕ := Fin.cases d w
    let aP : MvPolynomial (Fin (n + 1)) k →ₐ[k] Polynomial (MvPolynomial (Fin (n + 1)) k) :=
      MvPolynomial.aeval fun i => Polynomial.monomial (w' i) (MvPolynomial.X i)
    have hcomp : aA.comp f = (Polynomial.mapAlgHom f).comp aP := by
      apply MvPolynomial.algHom_ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [f, aP, w', hw]
      · simp [f, aP, w', hgrade]
    have hcoeff (p : MvPolynomial (Fin (n + 1)) k) (i : ℕ) :
        (aA (f p)).coeff i ∈ f.range := by
      refine ⟨(aP p).coeff i, ?_⟩
      have he := congrArg (fun q : Polynomial A => q.coeff i) (DFunLike.congr_fun hcomp p)
      exact ((Polynomial.coeff_mapAlgHom_apply f _ _).symm.trans he.symm)
    have hv : v ∈ f.range := ⟨MvPolynomial.X 0, by simp [f]⟩
    have hcoeff_range (i : ℕ) (a : A) : (aA a).coeff i ∈ f.range := by
      induction i using Nat.strong_induction_on generalizing a with
      | h i ih =>
        obtain ⟨p, hp⟩ := e.surjective (b a)
        let q := (MvPolynomial.finSuccEquiv k n).symm (Polynomial.C p)
        have hq : f q = s p := by rw [hf]; simp [q]
        have hba : b (f q) = b a := by
          rw [hq, ← AlgHom.comp_apply, hs]
          exact hp
        have hdiff : a - f q ∈ Ideal.span ({v} : Set A) := by
          rw [← hker]
          change b (a - f q) = 0
          rw [map_sub, hba, sub_self]
        obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hdiff
        have hz' : (aA (a - f q)).coeff i ∈ f.range := by
          rw [hz, map_mul, hw]
          by_cases hi : d ≤ i
          · nth_rw 1 [show i = (i - d) + d by omega]
            rw [Polynomial.coeff_monomial_mul]
            exact f.range.mul_mem hv (ih _ (by omega) z)
          · rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, Polynomial.coeff_C_mul,
              Polynomial.coeff_X_pow_mul', ite_eq_right hi, mul_zero]
            exact f.range.zero_mem
        rw [map_sub, Polynomial.coeff_sub] at hz'
        simpa only [sub_add_cancel] using f.range.add_mem hz' (hcoeff q i)
    intro a
    change a ∈ f.range
    have hsum : a = ∑ i ∈ (aA a).support, (aA a).coeff i := by
      calc
        a = (aA a).eval 1 := (hone a).symm
        _ = _ := by simp [Polynomial.eval_eq_sum, Polynomial.sum]
    rw [hsum]
    exact f.range.sum_mem fun i _ => hcoeff_range i a

/-- The linear coefficients give the cotangent basis for polynomial coordinates
at the augmentation which vanishes on the variables. -/
private theorem polynomialCotangentBasis {n : ℕ}
    (eps : A →ₐ[k] k) (e : MvPolynomial (Fin n) k ≃ₐ[k] A)
    (he : ∀ i, eps (e (MvPolynomial.X i)) = 0) :
    let I := RingHom.ker eps.toRingHom
    ∃ basis : Module.Basis (Fin n) k I.Cotangent,
      ∀ i, basis i = I.toCotangent ⟨e (MvPolynomial.X i), he i⟩ := by
  classical
  let I := RingHom.ker eps.toRingHom
  let J := MvPolynomial.idealOfVars (Fin n) k
  let r := e.toRingEquiv.toRingHom
  let x (i : Fin n) : I := ⟨e (MvPolynomial.X i), he i⟩
  let t := I.toCotangent.restrictScalars k
  have hε : eps.comp e.toAlgHom = MvPolynomial.aeval (fun _ : Fin n => (0 : k)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, MvPolynomial.aeval_X] using he i
  have hconst (p : MvPolynomial (Fin n) k) : eps (e p) = p.coeff 0 := by
    change (eps.comp e.toAlgHom) p = _
    rw [hε, MvPolynomial.aeval_zero']
    rfl
  have hJ (p : MvPolynomial (Fin n) k) : p ∈ J ↔ r p ∈ I := by
    change p ∈ J ↔ eps (e p) = 0
    rw [hconst, ← pow_one J, MvPolynomial.mem_pow_idealOfVars_iff']
    constructor
    · exact fun h => h 0 (by simp)
    · intro h m hm
      rwa [(Finsupp.degree_eq_zero_iff m).mp (Nat.lt_one_iff.mp hm)]
  have hJI : Ideal.map r J = I := by
    ext a
    obtain ⟨p, rfl⟩ := e.surjective a
    change r p ∈ Ideal.map r J ↔ r p ∈ I
    rw [Ideal.mem_map_iff_of_surjective r e.surjective]
    constructor
    · rintro ⟨q, hq, h⟩
      exact h ▸ (hJ q).mp hq
    · exact fun h => ⟨p, (hJ p).mpr h, rfl⟩
  have hpow (p : MvPolynomial (Fin n) k) : e p ∈ I ^ 2 ↔ p ∈ J ^ 2 := by
    change r p ∈ I ^ 2 ↔ _
    rw [← hJI, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective r e.surjective]
    constructor
    · rintro ⟨q, hq, h⟩
      exact e.injective h ▸ hq
    · exact fun h => ⟨p, h, rfl⟩
  let L (s : Fin n → k) : MvPolynomial (Fin n) k := ∑ i, s i • MvPolynomial.X i
  have hL0 (s) : (L s).coeff 0 = 0 := by
    simp [L, MvPolynomial.coeff_X]
  have hL1 (s) (i : Fin n) : (L s).coeff (Finsupp.single i 1) = s i := by
    simp [L, MvPolynomial.coeff_X,
      Finsupp.single_left_inj, mul_ite]
  have hvals (s) : e (L s) = ((∑ i, s i • x i : I) : A) := by
    let j := I.subtype.restrictScalars k
    change e (L s) = j (∑ i, s i • x i)
    simp [L, map_smul, map_sum, x, j]
  have ht (s : Fin n → k) : t (∑ i, s i • x i) = ∑ i, s i • t (x i) := by
    simp only [map_sum, map_smul]
  have hinj : LinearIndependent k (fun i => t (x i)) := by
    rw [Fintype.linearIndependent_iff]
    intro s hs i
    rw [← ht] at hs
    have hm := (I.toCotangent_eq_zero (∑ i, s i • x i)).mp hs
    rw [← hvals] at hm
    have hp := (MvPolynomial.mem_pow_idealOfVars_iff' 2 (L s)).mp ((hpow _).mp hm)
    rw [← hL1 s i]
    exact hp _ (by simp)
  have hspan : ⊤ ≤ Submodule.span k (Set.range fun i => t (x i)) := by
    intro q _
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective q
    let p := e.symm (a : A)
    let s := fun i => p.coeff (Finsupp.single i 1)
    have hp : e p = a := e.apply_symm_apply _
    have h0 : p.coeff 0 = 0 := by
      rw [← hconst, hp]
      exact a.property
    have hq : p - L s ∈ J ^ 2 := by
      rw [MvPolynomial.mem_pow_idealOfVars_iff']
      intro m hm
      rw [MvPolynomial.coeff_sub]
      rcases (show m.degree = 0 ∨ m.degree = 1 by omega) with hz | h₁
      · rw [(Finsupp.degree_eq_zero_iff m).mp hz, h0, hL0, sub_self]
      · have h₁' : m ∈ {d | Finsupp.degree d = 1} := h₁
        rw [← Finsupp.range_single_one] at h₁'
        obtain ⟨i, rfl⟩ := h₁'
        simp [hL1, s]
    have hdiff := (hpow _).mpr hq
    rw [map_sub, hp, hvals] at hdiff
    have heq := I.toCotangent_eq.mpr hdiff
    change t a = t (∑ i, s i • x i) at heq
    change t a ∈ _
    rw [heq, ht]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hinj hspan, Module.Basis.mk_apply hinj hspan⟩

end PolynomialCoordinates

private def HasSplitSeries (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (length : ℕ) (S : ClosedSeries G length), ∀ i < length,
    ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
      IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧
      (Nonempty (Q.val ≅ Grp.trivial (SchemeOver k)) ∨
        Nonempty ((groupPointsFunctor k).obj Q.val ≅ Specs.StandardGroups.additivePoints k))

private theorem HasSplitSeries.of_iso {G H : AffineAlgebraicGroup k}
    (e : G.val ≅ H.val) (h : HasSplitSeries G) : HasSplitSeries H := by
  obtain ⟨n, S, hS⟩ := h
  exact ⟨n, ⟨S.term, S.top ≪≫ e, S.bottom, S.step, S.closed⟩, hS⟩

private theorem HasSplitSeries.cons {G : AffineAlgebraicGroup k}
    {N : ClosedSubgroup G.val} {q : G.val ⟶ (StandardGroups.additiveGroup k).val}
    (hq : IsFppfGroupQuotient N q)
    (hS : HasSplitSeries (closedSubgroupAlgebraicGroup N)) : HasSplitSeries G := by
  obtain ⟨n, S, hS⟩ := hS
  let term : ℕ → AffineAlgebraicGroup k
    | 0 => G
    | i + 1 => S.term i
  let step (i : ℕ) : (term (i + 1)).val ⟶ (term i).val :=
    match i with
    | 0 => S.top.hom ≫ N.inclusion
    | i + 1 => S.step i
  have hclosed (i : ℕ) : IsClosedImmersion (step i).hom.hom.left := by
    cases i with
    | zero =>
      let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
      let : IsIso S.top.hom.hom.hom.left := F.map_isIso S.top.hom
      let := N.isClosedImmersion
      change IsClosedImmersion (S.top.hom.hom.hom.left ≫ N.inclusion.hom.hom.left)
      infer_instance
    | succ i => exact S.closed i
  refine ⟨n + 1, ⟨term, Iso.refl _, S.bottom, step, hclosed⟩, ?_⟩
  intro i hi
  cases i with
  | zero =>
    let Q := StandardGroups.additiveGroup k
    have hK : IsSchemeKernel q ⟨(S.term 0).val, step 0, hclosed 0⟩ :=
      scheme_kernel_of_iso q (step 0) (hclosed 0) N hq.1 S.top rfl
    let := G.property.1
    let := Q.property.1
    have hfac : IsImageFactorization q q (𝟙 Q.val) :=
      ⟨Category.comp_id _, hq.2.1, hq.2.2.1, hq.2.2.2.1,
        inferInstanceAs (IsAffineHom q.hom.hom.left),
        inferInstanceAs (IsClosedImmersion (𝟙 _))⟩
    exact ⟨Q, q, ⟨hK, hq.2.1, hq.2.2.1, hq.2.2.2.1, quotientRepresentsImage hfac hK⟩,
      Or.inr ⟨StandardGroups.additiveGroupPointsIso k⟩⟩
  | succ i => exact hS i (Nat.lt_of_succ_lt_succ hi)

private def HasHomogeneousCoordinates {A : HopfAlgebraCategory k} (g : GradedContraction A) : Prop :=
  ∃ (n : ℕ) (w : Fin n → ℕ) (e : MvPolynomial (Fin n) k ≃ₐ[k] A),
    ∀ i, 0 < w i ∧ g.action (e (MvPolynomial.X i)) = Polynomial.monomial (w i) (e (MvPolynomial.X i))

private theorem trivial_of_no_positive_coefficients {A : HopfAlgebraCategory k}
    [Algebra.FiniteType k A] (g : GradedContraction A)
    (hg : ∀ (i : ℕ), 0 < i → ∀ a, g.coefficient i a = 0) :
    HasSplitSeries (spectrumGroup A) ∧ HasHomogeneousCoordinates g := by
  let G := spectrumGroup A
  have h (a : A) : algebraMap k A (Coalgebra.counit (R := k) a) = a := by
    have hp : g.action a = Polynomial.C (algebraMap k A (Coalgebra.counit (R := k) a)) := by
      ext i
      cases i with
      | zero => simpa only [Polynomial.coeff_C_zero] using g.zero a
      | succ i =>
        rw [Polynomial.coeff_C, ite_eq_right (Nat.succ_ne_zero i)]
        exact hg _ (Nat.succ_pos i) a
    simpa [hp] using g.one a
  have htriv : ∀ (R : TestAlgebra k) (x : GroupPoints G.val R), x = 1 := by
    intro R x
    apply (fromAlgebra (A := A) (R := R)).symm.injective
    rw [map_one]
    apply WithConv.ofConv_injective
    ext a
    change (fromAlgebra.symm x : AlgPoint A R).ofConv a = algebraMap k R (Coalgebra.counit (R := k) a)
    calc
      (fromAlgebra.symm x : AlgPoint A R).ofConv a =
          (fromAlgebra.symm x : AlgPoint A R).ofConv
            (algebraMap k A (Coalgebra.counit (R := k) a)) := congrArg _ (h a).symm
      _ = _ := AlgHom.commutes _ _
  let e : k ≃ₐ[k] A := AlgEquiv.ofBijective (Algebra.ofId k A)
    ⟨Function.LeftInverse.injective (fun a ↦ (Bialgebra.counitAlgHom k A).commutes a),
      fun a ↦ ⟨Coalgebra.counit (R := k) a, h a⟩⟩
  refine ⟨⟨0, ⟨fun _ ↦ G, Iso.refl _, terminalIso G htriv, fun _ ↦ 𝟙 _,
    fun _ ↦ inferInstanceAs (IsClosedImmersion (𝟙 _))⟩, fun _ hi ↦ (Nat.not_lt_zero _ hi).elim⟩,
    ⟨0, Fin.elim0, (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).trans e, fun i ↦ Fin.elim0 i⟩⟩

/-- Take one coordinate of the lowest positive weight at a time. Its additive
quotient induces a strictly larger defining ideal for the next kernel, and the
homogeneous coordinates of that kernel lift to the current group. -/
private theorem splitSeries_and_coordinates_of_contraction {A₀ : HopfAlgebraCategory k}
    [Algebra.FiniteType k A₀] (g₀ : GradedContraction A₀)
    (hs₀ : Smooth (specGroup A₀).X.hom) :
    HasSplitSeries (spectrumGroup A₀) ∧ HasHomogeneousCoordinates g₀ := by
  let : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing k A₀
  have descend (I : Ideal A₀) :
      ∀ (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] (f : A₀ →ₐ[k] A),
        Function.Surjective f → RingHom.ker f = I → ∀ g : GradedContraction A,
        Smooth (specGroup A).X.hom → HasSplitSeries (spectrumGroup A) ∧ HasHomogeneousCoordinates g := by
    induction I using (wellFounded_gt (α := Ideal A₀)).induction with
    | h I ih =>
      intro A hA f hf hker g hs
      classical
      by_cases h : ∃ d : ℕ, 0 < d ∧ ∃ a, g.coefficient d a ≠ 0
      · let d := Nat.find h
        obtain ⟨hd, a, hva⟩ := Nat.find_spec h
        have hmin (i : ℕ) (hi : 0 < i) (hi' : i < d) (x : A) : g.coefficient i x = 0 := by
          by_contra hne
          exact Nat.find_min h hi' ⟨hi, x, hne⟩
        let v := g.coefficient d a
        have hv : v ≠ 0 := hva
        have hw : g.action v = Polynomial.monomial d v := g.homogeneous d a
        have hadd (R : TestAlgebra k) (x y : AlgPoint A R) :
            (x * y).ofConv v = x.ofConv v + y.ofConv v := first_primitive g hd hmin R x y a
        have hz : Coalgebra.counit (R := k) v = 0 := counit_first g hd a
        have : Algebra.Smooth k A :=
          (smooth_affine_iff (Iso.refl ((specGroup A).X))).mp hs
        let : IsReduced A := isReduced_of_smooth_algebra k A
        obtain ⟨N, hN, hregular⟩ := additiveMap_quotient g hd v hv hw hadd hz
        have hsN := firstKernel_smooth g hs hd hmin hva hN.1
        obtain ⟨B, hB, e, b, hb, hbv, hkerB, gB, hgradeB⟩ := contraction_on_kernel g hw hadd hz hN.1
        have hsB : Smooth (specGroup B).X.hom := by
          let eX : (specGroup B).X ≅ N.group.X := (Grp.forget _).mapIso e
          have : IsIso eX.hom.left := (Over.forget _).map_isIso eX.hom
          rw [← Over.w eX.hom]
          infer_instance
        have hlt : I < RingHom.ker (b.comp f) := by
          rw [← hker]
          apply lt_of_le_of_ne
          · intro x hx
            change b (f x) = 0
            rw [show f x = 0 from hx, map_zero]
          · intro he
            obtain ⟨x, hx⟩ := hf v
            have hx' : x ∈ RingHom.ker (b.comp f) := by
              change b (f x) = 0
              rwa [hx]
            rw [← he] at hx'
            exact hv (hx ▸ hx')
        obtain ⟨hBsplit, n, w, E, hE⟩ := ih _ hlt B (b.comp f) (hb.comp hf) rfl gB hsB
        refine ⟨HasSplitSeries.cons hN (HasSplitSeries.of_iso e hBsplit), ?_⟩
        have hmap (j : ℕ) (y : A) : gB.coefficient j (b y) = b (g.coefficient j y) := by
          have h := congrArg (fun q : Polynomial B ↦ q.coeff j) (DFunLike.congr_fun hgradeB y)
          exact h.trans (Polynomial.coeff_mapAlgHom_apply b _ _)
        choose y hy using fun i : Fin n ↦ hb (E (MvPolynomial.X i))
        let x (i : Fin n) : A := g.coefficient (w i) (y i)
        have hx (i : Fin n) : b (x i) = E (MvPolynomial.X i) := by
          change b (g.coefficient (w i) (y i)) = _
          rw [← hmap, hy]
          change (gB.action (E (MvPolynomial.X i))).coeff (w i) = _
          rw [(hE i).2, Polynomial.coeff_monomial, ite_eq_left rfl]
        have hxgrade (i : Fin n) : g.action (x i) = Polynomial.monomial (w i) (x i) :=
          g.homogeneous (w i) (y i)
        let coordinates := AlgEquiv.ofBijective _ (polynomialCoordinates_succ
          g.action g.one b v hd hw hregular hbv hkerB E w x hx hxgrade)
        refine ⟨n + 1, Fin.cases d w, coordinates, fun i ↦ ?_⟩
        change 0 < Fin.cases d w i ∧
          g.action (MvPolynomial.aeval (Fin.cases v x) (MvPolynomial.X i)) =
            Polynomial.monomial (Fin.cases d w i) (MvPolynomial.aeval (Fin.cases v x) (MvPolynomial.X i))
        rw [MvPolynomial.aeval_X]
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa only [Fin.cases_zero] using And.intro hd hw
        · simpa only [Fin.cases_succ] using And.intro (hE j).1 (hxgrade j)
      · apply trivial_of_no_positive_coefficients g
        intro i hi a
        by_contra hne
        exact h ⟨i, hi, a, hne⟩
  exact descend _ A₀ (AlgHom.id _ _) Function.surjective_id rfl g₀ hs₀

open private cocharacterImageIsTorus geometricMaximal_of_rationalMaximal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private exists_maximal_torus_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private connected_of_geometricallyConnected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private centralizes_comp_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterDynamics
open private same_subgroup_of_same_sections subgroupIso_of_same reductive_of_groupIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private contracting_is_radical from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi

/-- The contracting kernel is the radical of its limit parabolic. -/
theorem contractingSubgroupIsRadical :
    Specs.SplitContractingRadical.ContractingSubgroupIsRadical.{u} := by
  intro k _ G hG c D
  obtain ⟨S, p, hS, hp, hflat, hsurj⟩ := cocharacterImageIsTorus G c
  obtain ⟨T, hT, hST⟩ := exists_maximal_torus_over G S hS
  have hTm := geometricMaximal_of_rationalMaximal G hG.1
    (connected_of_geometricallyConnected hG.2.1) T hT
  obtain ⟨C, hC, hCr⟩ := Reductive.SubtorusCentralizer.centralizerReductive
    G hG T S hT.1 hS hST hTm
  have hD : RepresentsSubgroup D.centralizer (fun _ g ↦ Centralizes S.inclusion g) := by
    intro X x
    let := hflat
    let := hsurj
    change Centralizes S.inclusion x ↔ _
    rw [← centralizes_comp_iff p S.inclusion x, hp]
    exact D.centralizer_points X x
  obtain ⟨e, _⟩ := subgroupIso_of_same (same_subgroup_of_same_sections (H := G) hC hD)
  have hDr : IsReductive (closedSubgroupAlgebraicGroup D.centralizer) :=
    reductive_of_groupIso e hCr
  let := hG.1
  let := connected_of_geometricallyConnected hG.2.1
  exact contracting_is_radical D hDr (limitSubgroupsSmooth G c D).2.1
    (geometricallyConnectedLimitSubgroups G c D).2.1 (contractingSubgroupUnipotent G c D)

/-- The split series for the contracting subgroup of a cocharacter. -/
theorem splitContractingSubgroup :
    Specs.SplitContractingRadical.SplitContractingSubgroup.{u} := by
  intro k _ G hG c D
  let : Smooth G.val.X.hom := hG.1
  let U := closedSubgroupAlgebraicGroup D.contracting
  have hU : Smooth U.val.X.hom := (limitSubgroupsSmooth G c D).2.1
  obtain ⟨A, hA, ⟨e⟩⟩ := groupPresentation U
  obtain ⟨g, _⟩ := contraction_of_cocharacter G c D e
  have hs : Smooth (specGroup A).X.hom := by
    let eX : (specGroup A).X ≅ U.val.X := (Grp.forget _).mapIso e
    have : IsIso eX.hom.left := (Over.forget _).map_isIso eX.hom
    rw [← Over.w eX.hom]
    infer_instance
  have hsplit := HasSplitSeries.of_iso e (splitSeries_and_coordinates_of_contraction g hs).1
  exact ⟨contractingSubgroupUnipotent G c D, hsplit⟩

/-- The contracting action gives affine-space coordinates of positive weights,
with the identity at the origin. -/
theorem contractingPolynomialCoordinates :
    Specs.SplitContractingRadical.ContractingPolynomialCoordinates.{u} := by
  intro k _ G hG c D A e
  let := hG.1
  let eX : (specGroup A).X ≅ D.contracting.group.X := (Grp.forget _).mapIso e
  have hft : Algebra.FiniteType k A := by
    let : IsIso eX.hom.left := (Over.forget _).map_isIso eX.hom
    let : LocallyOfFiniteType D.contracting.group.X.hom :=
      (closedSubgroupAlgebraicGroup (G := G) D.contracting).property.2.1
    have h : LocallyOfFiniteType (specGroup A).X.hom := by
      rw [← Over.w eX.hom]
      infer_instance
    exact (hopfSpec_locallyOfFiniteType_iff k A).mp h
  have hs : Smooth (specGroup A).X.hom := by
    let : IsIso eX.hom.left := (Over.forget _).map_isIso eX.hom
    let := (limitSubgroupsSmooth G c D).2.1
    rw [← Over.w eX.hom]
    infer_instance
  obtain ⟨g, hOrbit⟩ := contraction_of_cocharacter G c D e
  obtain ⟨n, w, E, hE⟩ := (splitSeries_and_coordinates_of_contraction g hs).2
  have hz (i : Fin n) : Bialgebra.counitAlgHom k A (E (MvPolynomial.X i)) = 0 := by
    have h : g.coefficient (w i) (E (MvPolynomial.X i)) = E (MvPolynomial.X i) := by
      change (g.action (E (MvPolynomial.X i))).coeff (w i) = _
      rw [(hE i).2, Polynomial.coeff_monomial, ite_eq_left rfl]
    exact h ▸ counit_first g (hE i).1 (E (MvPolynomial.X i))
  obtain ⟨basis, hbasis⟩ := polynomialCotangentBasis (Bialgebra.counitAlgHom k A) E hz
  exact ⟨n, w, E, g.action, hOrbit, hE, hz, basis, hbasis⟩

/-- Apply the contracting subgroup result to a cocharacter for a given parabolic. -/
theorem parabolicSplitRadical :
    Specs.SplitContractingRadical.ParabolicSplitRadical.{u} := by
  intro k _ G P hP
  obtain ⟨c, D, hsame, _, hrad⟩ := RationalCocharacter.rationalParabolic G P hP
  exact ⟨c, D, hsame, hrad, splitContractingSubgroup G hP.1 c D⟩

end

end LinearAlgebraicGroups.Relative.SplitContractingRadical
