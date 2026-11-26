import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.NontrialitarianCompactRealConnectedness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RealDefiniteSpin
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite Topology
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.NontrialitarianCompactRealConnectedness

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianCompactRealConnectedness (CompactRealConnectedness)
open Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair EquivariantSpinTrivialization SpinModel gramAdjoint)
open Specs.Arithmetic.IsotropicSpinGeneration (IsRegular)
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open AdelicGroups (PointsIn LocalPoints)
open LinearAlgebraicGroups.Albert
open LinearAlgebraicGroups.Albert.SpinSpecification
  (ScalarClifford IsSpinPointRepresentation)
open CliffordAlgebra

open private finite_galois_field_over_extension extendSpinTrivialization
  arithmetic_absolute_simplicity
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
open private spinModel_of_trivialization descendedPair_isOrthogonal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
open private reindexGramAdjoint scalarSpinRepresentation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ScalarEvenSpinLocalDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open private orderedBasis extendedBasis EvenIndex homFromPoint homFromPoint_variable
  variableClass equationIdeal changeModule_coord
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private matrix_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation

private theorem continuousPolynomialEvaluation
    {F J X : Type*} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
    [TopologicalSpace X] (c : X → J → F) (hc : ∀ j, Continuous (fun x ↦ c x j))
    (P : MvPolynomial J F) : Continuous (fun x ↦ MvPolynomial.aeval (c x) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C]
    exact continuous_const
  | add P Q hP hQ =>
    simp only [map_add]
    exact continuous_add.comp (hP.prodMk hQ)
  | mul_X P j hP =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact continuous_mul.comp (hP.prodMk (hc j))

/-- The universal spin point expresses every matrix entry of a point in a
closed realization as a polynomial in its even Clifford coordinates. -/
private theorem connectedOfSpinParameters
    {F V J : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [AddCommGroup V] [Module F V] [Fintype J] [LinearOrder J]
    {G : AffineAlgebraicGroup F} (i : MatrixRealization G)
    (q : QuadraticForm F V) (b : Module.Basis J F V)
    (spin : ∀ T : TestAlgebra F, GroupPoints G.val T →* (ScalarClifford q T)ˣ)
    (hspin : IsSpinPointRepresentation q G.val spin)
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (a : X → SpinFunctor.Spin q F b) (ha : Function.Surjective a)
    (hc : ∀ s : EvenIndex J, Continuous (fun x =>
      (extendedBasis q F b).coord s.val ((a x).val : ScalarClifford q F))) :
    ConnectedSpace (PointsIn i F) := by
  classical
  let A := CommAlgCat.of F (SpinFunctor.CoordinateRing q b)
  let T := CommAlgCat.of F F
  let a₀ := SpinFunctor.pointEquiv q b A (AlgHom.id F A)
  have hrange : Set.range (spin A) = SpinSpecification.spinUnits q A := (hspin.1 A).2
  have hmem : a₀.val ∈ Set.range (spin A) := hrange.symm ▸ a₀.property
  obtain ⟨p, hp⟩ := hmem
  let f (x : X) : A ⟶ T := CommAlgCat.ofHom (homFromPoint q b F (a x))
  let g (x : X) : PointsIn i F := mapPoints (f x) p
  have hg (x : X) : spin T (g x) = (a x).val := by
    have h := hspin.2 (f x) p
    change spin T (g x) = Units.map
      (SpinSpecification.coefficientMap q A (f x).hom).toMonoidHom
      (spin A p) at h
    refine h.trans ((congrArg (Units.map
      (SpinSpecification.coefficientMap q A (f x).hom).toMonoidHom) hp).trans ?_)
    have hn := SpinFunctor.pointEquiv_natural q b (f x).hom (AlgHom.id F A)
    change SpinFunctor.pointEquiv q b F (homFromPoint q b F (a x)) =
      SpinFunctor.map q b (f x).hom a₀ at hn
    rw [show homFromPoint q b F (a x) = (SpinFunctor.pointEquiv q b F).symm (a x) from rfl,
      Equiv.apply_symm_apply] at hn
    exact congrArg Subtype.val hn.symm
  have hsurj : Function.Surjective g := by
    intro y
    have hrangeT : Set.range (spin T) = SpinSpecification.spinUnits q T := (hspin.1 T).2
    have hy := hrangeT ▸ Set.mem_range_self (f := spin T) y
    obtain ⟨x, hx⟩ := ha ⟨spin T y, hy⟩
    exact ⟨x, (hspin.1 T).1 ((hg x).trans (congrArg Subtype.val hx))⟩
  have heval (v : A) : Continuous (fun x ↦ (f x).hom v) := by
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective v
    let c (x : X) (s : EvenIndex J) :=
      (extendedBasis q F b).coord s.val ((a x).val : ScalarClifford q F)
    let π : MvPolynomial (EvenIndex J) F →ₐ[F] A := Ideal.Quotient.mkₐ F (equationIdeal q b)
    have hpoly (x : X) : ((f x).hom).comp π = MvPolynomial.aeval (c x) := by
      apply MvPolynomial.algHom_ext
      intro s
      change homFromPoint q b F (a x) (variableClass q b s) = MvPolynomial.aeval (c x) (MvPolynomial.X s)
      rw [homFromPoint_variable, MvPolynomial.aeval_X]
    change Continuous (fun x ↦ (((f x).hom).comp π) P)
    simp_rw [hpoly]
    exact continuousPolynomialEvaluation c hc P
  refine hsurj.connectedSpace ?_
  apply continuous_induced_rng.mpr
  apply Units.continuous_iff.mpr
  let α := (groupPointsFunctor F).map i.embedding ≫ i.matrix.hom
  refine ⟨continuous_matrix (fun l m ↦ ?_), continuous_matrix (fun l m ↦ ?_)⟩
  · change Continuous (fun x ↦ ((α.app T).hom (mapPoints (f x) p)).val l m)
    simp_rw [matrix_naturality α (f _) p]
    exact heval (((α.app A).hom p).val l m)
  · change Continuous (fun x ↦ (((α.app T).hom (mapPoints (f x) p))⁻¹).val l m)
    have hentry (x : X) :
        (((α.app T).hom (mapPoints (f x) p))⁻¹).val l m =
          (f x).hom ((((α.app A).hom p)⁻¹).val l m) := by
      let φ := (((groupPointsFunctor F).obj G.val).map (f x)).hom
      have h := matrix_naturality α (f x) p⁻¹ l m
      change ((α.app T).hom (φ p⁻¹)).val l m =
        (f x).hom (((α.app A).hom p⁻¹).val l m) at h
      change (((α.app T).hom (φ p))⁻¹).val l m = _
      simpa only [map_inv] using h
    simp_rw [hentry]
    exact heval ((((α.app A).hom p)⁻¹).val l m)

private theorem conjugationImage_eq_iff {A : Type*} [Monoid A] (a : Aˣ) (W : Set A) :
    (fun x : A => (a : A) * x * ↑a⁻¹) '' W = W ↔
      Set.MapsTo (fun x : A => (a : A) * x * ↑a⁻¹) W W ∧
      Set.MapsTo (fun x : A => (↑a⁻¹ : A) * x * a) W W := by
  let f (x : A) := (a : A) * x * ↑a⁻¹
  let g (x : A) := (↑a⁻¹ : A) * x * a
  have hfg (x : A) : f (g x) = x := by
    dsimp only [f, g]
    rw [← mul_assoc (a : A), ← mul_assoc (a : A), Units.mul_inv, one_mul,
      mul_assoc, Units.mul_inv, mul_one]
  have hgf (x : A) : g (f x) = x := by
    dsimp only [f, g]
    rw [← mul_assoc (↑a⁻¹ : A), ← mul_assoc (↑a⁻¹ : A), Units.inv_mul, one_mul,
      mul_assoc, Units.inv_mul, mul_one]
  change f '' W = W ↔ Set.MapsTo f W W ∧ Set.MapsTo g W W
  constructor
  · intro h
    refine ⟨Set.image_subset_iff.mp h.le, ?_⟩
    intro x hx
    rw [← h] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [hgf] using hy
  · rintro ⟨hf, hg⟩
    exact Set.Subset.antisymm (Set.image_subset_iff.mpr hf)
      (fun x hx => ⟨g x, hg hx, hfg x⟩)

private theorem topologicalRingOfRealEquiv {F : Type*} [Field F] [TopologicalSpace F]
    (R : F ≃+* ℝ) (hR : IsHomeomorph R) : IsTopologicalRing F where
  continuous_add := hR.isInducing.continuous_iff.mpr (by
    change Continuous (fun p : F × F ↦ R (p.1 + p.2))
    simp only [map_add]
    exact (hR.continuous.comp continuous_fst).add (hR.continuous.comp continuous_snd))
  continuous_mul := hR.isInducing.continuous_iff.mpr (by
    change Continuous (fun p : F × F ↦ R (p.1 * p.2))
    simp only [map_mul]
    exact (hR.continuous.comp continuous_fst).mul (hR.continuous.comp continuous_snd))
  continuous_neg := hR.isInducing.continuous_iff.mpr (by
    change Continuous (fun x : F ↦ R (-x))
    simp only [map_neg]
    exact hR.continuous.neg)

private theorem connectedOfDefiniteSpin
    {F V J : Type u} [Field F] [TopologicalSpace F]
    [AddCommGroup V] [Module F V] [Fintype J] [LinearOrder J]
    {G : AffineAlgebraicGroup F} (i : MatrixRealization G)
    (R : F ≃+* ℝ) (hR : IsHomeomorph R)
    (q : QuadraticForm F V) (b : Module.Basis J F V) (hd : 2 ≤ Fintype.card J)
    (hq : (∀ x ≠ 0, 0 < R (q x)) ∨ (∀ x ≠ 0, R (q x) < 0))
    (spin : ∀ T : TestAlgebra F, GroupPoints G.val T →* (ScalarClifford q T)ˣ)
    (hspin : IsSpinPointRepresentation q G.val spin) : ConnectedSpace (PointsIn i F) := by
  classical
  letI : IsTopologicalRing F := topologicalRingOfRealEquiv R hR
  letI : Algebra F ℝ := R.toRingHom.toAlgebra
  let Q := CliffordSpecification.coefficientForm ℝ q b
  let B := b.baseChange ℝ
  letI : Module.Finite ℝ (ℝ ⊗[F] V) := Module.Finite.of_basis B
  have hdim : 2 ≤ Module.finrank ℝ (ℝ ⊗[F] V) := by
    rw [Module.finrank_eq_card_basis B]
    exact hd
  have hvec : ∀ x : ℝ ⊗[F] V, ∃ v : V, (1 : ℝ) ⊗ₜ[F] v = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t v =>
      obtain ⟨a, rfl⟩ := R.surjective t
      refine ⟨a • v, ?_⟩
      rw [TensorProduct.tmul_smul]
      change (R a * 1) ⊗ₜ[F] v = _
      rw [mul_one]
    | add x y hx hy =>
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      exact ⟨v + w, TensorProduct.tmul_add _ _ _⟩
  have hQ : RealDefiniteSpinSpec.IsDefinite Q := by
    have hval (v : V) : Q ((1 : ℝ) ⊗ₜ[F] v) = R (q v) := by
      change Q ((1 : ℝ) ⊗ₜ[F] v) = algebraMap F ℝ (q v)
      have h := CliffordModel.coefficientForm_tmul ℝ q b 1 v
      rw [one_mul, one_mul] at h
      exact h
    rcases hq with hpos | hneg
    · left
      intro x hx
      obtain ⟨v, rfl⟩ := hvec x
      rw [hval]
      exact hpos v (fun h => hx (by simp [h]))
    · right
      intro x hx
      obtain ⟨v, rfl⟩ := hvec x
      rw [hval]
      exact hneg v (fun h => hx (by simp [h]))
  obtain ⟨e, _, he⟩ := SpinFunctor.intrinsicCriterion q b ℝ
  let E : (ScalarClifford q ℝ)ˣ ≃* (CliffordAlgebra Q)ˣ := Units.mapEquiv e.toMulEquiv
  have heSpin (a : (ScalarClifford q ℝ)ˣ) :
      a ∈ SpinSpecification.spinUnits q ℝ ↔
        E a ∈ RealDefiniteSpinSpec.spinPoints Q := by
    refine (he a).trans ?_
    have h := conjugationImage_eq_iff (E a) (LinearMap.range (ι Q) : Set _)
    rw [← (map_inv E a)] at h
    exact and_congr_right' (and_congr_right' h)
  let X := ↥(RealDefiniteSpinSpec.cliffordPoints Q)
  letI : TopologicalSpace (CliffordAlgebra Q) := moduleTopology ℝ (CliffordAlgebra Q)
  letI : IsModuleTopology ℝ (CliffordAlgebra Q) := ⟨rfl⟩
  letI : ConnectedSpace X := isConnected_iff_connectedSpace.mp
    (RealDefiniteSpin.pathConnected Q hQ hdim).isConnected
  let f (a : SpinFunctor.Spin q ℝ b) : X :=
    ⟨e a.val, ⟨E a.val, (heSpin a.val).mp a.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a c h ↦ Subtype.ext (Units.ext (e.injective (congrArg Subtype.val h))), ?_⟩
    rintro ⟨x, a, ha, rfl⟩
    let a' := E.symm a
    have ha' : a' ∈ SpinSpecification.spinUnits q ℝ :=
      (heSpin a').mpr (by simpa only [a', MulEquiv.apply_symm_apply] using ha)
    refine ⟨⟨a', ha'⟩, Subtype.ext ?_⟩
    exact congrArg Units.val (E.apply_symm_apply a)
  let aR := (Equiv.ofBijective f hf).symm
  have hval (x : X) : e (aR x).val = x.val :=
    congrArg Subtype.val ((Equiv.ofBijective f hf).apply_symm_apply x)
  let γ : ℝ →ₐ[F] F :=
    { toRingHom := R.symm.toRingHom
      commutes' := R.symm_apply_apply }
  let aF (x : X) := SpinFunctor.map q b γ (aR x)
  have hmap : Function.Surjective (SpinFunctor.map q b γ) := by
    intro a
    let δ : F →ₐ[F] ℝ := Algebra.ofId F ℝ
    have hδ : γ.comp δ = AlgHom.id F F := AlgHom.ext R.symm_apply_apply
    refine ⟨SpinFunctor.map q b δ a, ?_⟩
    rw [← SpinFunctor.map_comp, hδ, SpinFunctor.map_id]
  refine connectedOfSpinParameters i q b spin hspin aF (hmap.comp aR.surjective) ?_
  intro s
  have hcoord (x : X) :
      (extendedBasis q F b).coord s.val ((aF x).val : ScalarClifford q F) =
        R.symm ((extendedBasis q ℝ b).coord s.val (e.symm x.val)) := by
    rw [← hval x, AlgEquiv.symm_apply_apply]
    exact changeModule_coord (orderedBasis q b) γ _ s.val
  simp_rw [hcoord]
  have hc : Continuous (fun x : CliffordAlgebra Q =>
      (extendedBasis q ℝ b).coord s.val (e.symm x)) :=
    IsModuleTopology.continuous_of_linearMap
      (((extendedBasis q ℝ b).coord s.val).comp e.symm.toLinearMap)
  have hRs : Continuous R.symm := (R.toEquiv.toHomeomorphOfIsInducing hR.isInducing).symm.continuous
  exact hRs.comp (hc.comp continuous_subtype_val)

/-- The local spin scheme represents the spin functor of the definite form
obtained from compactness. The basis reindexes its Gram matrix to the
indices of the split vector model. -/
private theorem compactLocalSpinConnected
    {F T I : Type u} [Field F] [TopologicalSpace F] [Field T] [Algebra F T]
    [FiniteDimensional F T] [IsGalois F T] [Fintype I] [DecidableEq I] [Nonempty I]
    {G : AffineAlgebraicGroup F}
    (C : EquivariantSpinTrivialization (K := T) (I := I) G)
    (Q : DescendedQuadraticPair C.action) (M : SpinModel G Q)
    (hG : AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G) (hn : 4 ≤ Fintype.card I)
    (i : MatrixRealization G) (R : F ≃+* ℝ) (hR : IsHomeomorph R)
    (hi : CompactSpace (PointsIn i F)) : ConnectedSpace (PointsIn i F) := by
  classical
  have hcompact :
      letI : TopologicalSpace F := TopologicalSpace.induced R inferInstance
      IsCompact (Set.univ : Set (PointsIn i F)) := by
    exact (congrArg (fun t : TopologicalSpace F =>
      letI := t
      IsCompact (Set.univ : Set (PointsIn i F))) hR.isInducing.eq_induced).mp hi.isCompact_univ
  obtain ⟨r, e, H, q, hr, _, hpolar, hnd, hadj, hq⟩ :=
    QuaternionSpinIsotropy.compactRealModel G Q M hn (descendedPair_isOrthogonal Q)
      F R i hcompact
  have h₂ : (2 : F) ≠ 0 := fun h =>
    (by norm_num : (2 : ℝ) ≠ 0) (by simpa only [map_ofNat, map_zero] using congrArg R h)
  let j : Fin r ≃ I ⊕ I := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, hr, Fintype.card_sum, two_mul])
  let E := Matrix.reindexAlgEquiv F F j
  let b := (Pi.basisFun F (Fin r)).reindex j
  let H' := Units.map E.toMonoidHom H
  let e' := ((Algebra.TensorProduct.lid F C.action.fixedSubalgebra).symm.trans e).trans E
  letI : LinearOrder (I ⊕ I) :=
    LinearOrder.lift' (Fintype.equivFin (I ⊕ I)) (Fintype.equivFin (I ⊕ I)).injective
  have hb : LinearMap.BilinForm.toMatrix b q.polarBilin = H'.val := by
    rw [hpolar]
    ext a l
    change LinearMap.BilinForm.toMatrix ((Pi.basisFun F (Fin r)).reindex j)
      (Matrix.toLinearMap₂' F H.val) a l = _
    rw [LinearMap.BilinForm.toMatrix_apply, Module.Basis.reindex_apply,
      Module.Basis.reindex_apply, ← Matrix.toLinearMap₂_basisFun,
      Matrix.toLinearMap₂_apply_basis]
    rfl
  have he (x : C.action.fixedSubalgebra) :
      e' (Q.involution.toLinearMap x) = gramAdjoint H' (e' x) := by
    change E (e ((1 : F) ⊗ₜ[F] Q.involution.toLinearMap x)) =
      gramAdjoint H' (E (e ((1 : F) ⊗ₜ[F] x)))
    rw [← show (Q.involution.baseChange F).toLinearMap ((1 : F) ⊗ₜ[F] x) =
      (1 : F) ⊗ₜ[F] Q.involution.toLinearMap x from rfl, hadj]
    exact reindexGramAdjoint j H _
  have hreg : IsRegular q := Or.inl (LinearMap.separatingLeft_iff_ker_eq_bot.mp hnd.1)
  obtain ⟨s, hs⟩ := scalarSpinRepresentation b NontrialitarianSpinModels.splitProjectiveSpinAction
    M hG h₂ e' H' hb he hreg
  exact connectedOfDefiniteSpin i R hR q b (by rw [Fintype.card_sum]; omega) hq s hs

private theorem absoluteSimplicityFromArithmetic
    {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G) :
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G := by
  refine ⟨hG.1, ?_, ?_⟩
  · intro hz
    exact hG.2.1 ⟨hz.iso (Grp.isZero_trivial _)⟩
  · intro N hN
    exact (hG.2.2 N hN).imp (fun ⟨e⟩ => (Grp.isZero_trivial _).of_iso e) id

theorem compactRealConnectedness : CompactRealConnectedness.{u} := by
  classical
  intro k L I _ _ _ _ _ _ _ _ hK G hG hn C _Q _M _ho D _hD i w R hR hc
  let F := D.Completion (.inr w)
  let J := baseChangedAlgebraicGroup F G
  have hJ : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple J :=
    OppositeRadicals.absolutelyAlmostSimpleFieldExtension G (arithmetic_absolute_simplicity hG)
  obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
  let e := hj.homeomorph
  letI : CompactSpace (LocalPoints D i (.inr w)) := hc
  have hjcompact : CompactSpace (PointsIn j F) := e.symm.compactSpace
  -- The base-changed trivialization gives a spin model over the completion itself.
  obtain ⟨T, _, _, _, _, _, _, _, hTower⟩ := finite_galois_field_over_extension k L F
  letI : IsScalarTower k L T := hTower
  obtain ⟨C'⟩ := extendSpinTrivialization (L := F) (T := T) C hn
  obtain ⟨Q'⟩ := NontrialitarianSpinModels.quadraticPairDescent F T I C'.action
    (fun σ => ⟨C'.g σ, C'.multiplier σ, C'.actionFormula σ, C'.similarity σ⟩)
  obtain ⟨M'⟩ := spinModel_of_trivialization J hJ.1.2.1 hn C' Q'
  letI : ConnectedSpace (PointsIn j F) :=
    compactLocalSpinConnected C' Q' M' (absoluteSimplicityFromArithmetic hJ) hn j R hR hjcompact
  exact e.surjective.connectedSpace e.continuous

end
end LinearAlgebraicGroups.Arithmetic.NontrialitarianCompactRealConnectedness
