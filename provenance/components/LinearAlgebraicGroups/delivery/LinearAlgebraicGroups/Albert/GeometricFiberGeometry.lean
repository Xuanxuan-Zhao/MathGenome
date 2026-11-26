import Specs.LinearAlgebraicGroups.Albert.GeometricFiberGeometry
import LinearAlgebraicGroups.Albert.IdempotentCharts
import LinearAlgebraicGroups.Albert.Triality
import LinearAlgebraicGroups.Albert.SpinWeights
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Albert.GeometricFiberGeometry

open AlgebraicGeometry Topology
open GeometricFiberSpecification ShortDirectionSpecification
open TrialitySpecification (Model modelOp mapModel)
open FrameSpecification (frameAxis)
open IdempotentSpecification
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 1400
set_option linter.style.haveILetI false

open private albertPoints albertPoints_natural mem_splitAutomorphisms
  splitAutomorphisms modelAction_ext coordinateFinitePresentation identityPoint
  identityPoint_isIdentity identityPoint_over from LinearAlgebraicGroups.Albert.ShortDirections
open private quotientMatrixEquiv from LinearAlgebraicGroups.Albert.AutomorphismScheme

private abbrev Automorphisms (S : Type) [CommRing S] := splitAutomorphisms S

private def points (P : IntegralPresentation) (k S : Type) [Field k] [CommRing S] [Algebra k S] :
    (FiberRing P k →ₐ[k] S) ≃ Automorphisms S :=
  (AlgHom.liftEquiv ℤ k P.Coordinates S).symm.trans (albertPoints P S)

private lemma points_natural (P : IntegralPresentation) {k S T : Type} [Field k]
    [CommRing S] [CommRing T] [Algebra k S] [Algebra k T] (f : S →ₐ[k] T)
    (a : FiberRing P k →ₐ[k] S) (x : Model S) :
    mapModel f.toRingHom ((points P k S a).val x) =
      (points P k T (f.comp a)).val (mapModel f.toRingHom x) :=
  albertPoints_natural P (f.restrictScalars ℤ) _ x

private lemma points_eq_of_natural (P : IntegralPresentation) {k S T : Type} [Field k]
    [CommRing S] [CommRing T] [Algebra k S] [Algebra k T] (f : S →ₐ[k] T)
    {g : Automorphisms S} {h : Automorphisms T}
    (hh : ∀ x, mapModel f.toRingHom (g.val x) = h.val (mapModel f.toRingHom x)) :
    f.comp ((points P k S).symm g) = (points P k T).symm h := by
  apply (points P k T).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  apply modelAction_ext P f.toRingHom
  intro x
  rw [← points_natural, Equiv.apply_symm_apply, hh]

private def primeOfHom {k A : Type} [Field k] [CommRing A] [Algebra k A] (a : A →ₐ[k] k) :
    PrimeSpectrum A where
  asIdeal := RingHom.ker a.toRingHom
  isPrime := RingHom.ker_isPrime _

private lemma primeOfHom_comp {k A B : Type} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (a : B →ₐ[k] k) :
    PrimeSpectrum.comap f.toRingHom (primeOfHom a) = primeOfHom (a.comp f) := rfl

private instance fiberFinitePresentation (P : IntegralPresentation) (k : Type) [Field k] :
    Algebra.FinitePresentation k (FiberRing P k) := by
  letI := coordinateFinitePresentation P
  change Algebra.FinitePresentation k (FiberRing P k)
  exact Algebra.FinitePresentation.baseChange k

private lemma exists_rationalPoint {k A : Type} [Field k] [IsAlgClosed k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (p : PrimeSpectrum A) (hp : IsClosed {p}) :
    ∃ a : A →ₐ[k] k, primeOfHom a = p := by
  letI : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hp
  letI : Field (A ⧸ p.asIdeal) := Ideal.Quotient.field _
  letI := finite_of_finite_type_of_isJacobsonRing k (A ⧸ p.asIdeal)
  let a : (A ⧸ p.asIdeal) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨a.comp (Ideal.Quotient.mkₐ k p.asIdeal), PrimeSpectrum.ext ?_⟩
  apply Ideal.ext
  intro x
  change a (Ideal.Quotient.mk _ x) = 0 ↔ x ∈ p.asIdeal
  exact ⟨fun h => Ideal.Quotient.eq_zero_iff_mem.mp (a.injective (h.trans (map_zero a).symm)),
    fun h => by rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]⟩

open private extendFrameAuto extendFrameAuto_natural extendFrameAuto_preserves
  extendFrameAuto_symm extendFrameAuto_self from LinearAlgebraicGroups.Albert.IdempotentCharts

private def extendAuto {k : Type} [Field k] (g : Automorphisms k)
    (S : Type) [CommRing S] [Algebra k S] : Automorphisms S :=
  ⟨extendFrameAuto g.val S,
    (mem_splitAutomorphisms _).mpr
      (extendFrameAuto_preserves _ ((mem_splitAutomorphisms _).mp g.property))⟩

private lemma extendAuto_inv {k : Type} [Field k] (g : Automorphisms k)
    (S : Type) [CommRing S] [Algebra k S] : extendAuto g⁻¹ S = (extendAuto g S)⁻¹ :=
  Subtype.ext (extendFrameAuto_symm g.val)

private lemma extendAuto_self {k : Type} [Field k] (g : Automorphisms k) : extendAuto g k = g :=
  Subtype.ext (LinearEquiv.ext (extendFrameAuto_self g.val))

set_option backward.isDefEq.respectTransparency false in
private def translate (P : IntegralPresentation) {k : Type} [Field k] (g : Automorphisms k) :
    FiberRing P k →ₐ[k] FiberRing P k :=
  (points P k (FiberRing P k)).symm
    (extendAuto g (FiberRing P k) * points P k (FiberRing P k) (AlgHom.id k _))

private lemma extend_mul_natural {k R S : Type} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (g : Automorphisms k)
    (a : Automorphisms R) (b : Automorphisms S)
    (hab : ∀ x, mapModel f.toRingHom (a.val x) = b.val (mapModel f.toRingHom x)) (x : Model R) :
    mapModel f.toRingHom ((extendAuto g R * a).val x) =
      (extendAuto g S * b).val (mapModel f.toRingHom x) :=
  (extendFrameAuto_natural g.val f (a.val x)).trans (congrArg (extendFrameAuto g.val S) (hab x))

set_option backward.isDefEq.respectTransparency false in
private lemma translate_eval (P : IntegralPresentation) {k S : Type} [Field k]
    [CommRing S] [Algebra k S] (g : Automorphisms k) (a : FiberRing P k →ₐ[k] S) :
    points P k S (a.comp (translate P g)) = extendAuto g S * points P k S a := by
  let u := AlgHom.id k (FiberRing P k)
  let v := points P k (FiberRing P k) u
  let w := points P k S a
  have h (x : Model (FiberRing P k)) :
      mapModel a.toRingHom (v.val x) = w.val (mapModel a.toRingHom x) := by
    have he := points_natural P (S := FiberRing P k) (T := S) a u x
    rw [AlgHom.comp_id] at he
    exact he
  have he := points_eq_of_natural P (S := FiberRing P k) (T := S) a
    (g := extendAuto g (FiberRing P k) * v) (h := extendAuto g S * w)
    (extend_mul_natural (R := FiberRing P k) (S := S) a g v w h)
  exact (congrArg (points P k S) he).trans ((points P k S).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
private lemma translate_cancel (P : IntegralPresentation) {k : Type} [Field k]
    (g : Automorphisms k) :
    (translate P g).comp (translate P g⁻¹) = AlgHom.id k (FiberRing P k) := by
  apply (points P k (FiberRing P k)).injective
  rw [translate_eval, extendAuto_inv]
  have ht : points P k (FiberRing P k) (translate P g) =
      extendAuto g (FiberRing P k) * points P k (FiberRing P k) (AlgHom.id k _) :=
    (points P k (FiberRing P k)).apply_symm_apply _
  rw [ht, inv_mul_cancel_left]

private def translation (P : IntegralPresentation) {k : Type} [Field k] (g : Automorphisms k) :
    FiberRing P k ≃ₐ[k] FiberRing P k :=
  AlgEquiv.ofAlgHom (translate P g) (translate P g⁻¹) (translate_cancel P g)
    (by simpa only [inv_inv] using translate_cancel P g⁻¹)

private lemma section_is_identity (P : IntegralPresentation) (e : P.Coordinates →ₐ[ℤ] ℤ)
    (he : P.IsIdentity e) : e = identityPoint P := by
  apply (quotientMatrixEquiv P.cutsOut (S := ℤ)).injective
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact (he i j).trans (identityPoint_isIdentity P i j).symm

private lemma translating_chart {k A : Type} [Field k] [CommRing A] [Algebra k A]
    (h : A ≃ₐ[k] A) (f : A) [Algebra.Smooth k (Localization.Away f)] :
    Algebra.Smooth k (Localization.Away (h f)) :=
  Algebra.Smooth.of_equiv
    (IsLocalization.algEquivOfAlgEquiv (Localization.Away f) (Localization.Away (h f)) h
      (Submonoid.map_powers h f))

private lemma smooth_baseChange_away (k A : Type) [Field k] [CommRing A] [Algebra ℤ A]
    (f : A) (hs : Algebra.IsStandardSmoothOfRelativeDimension 52 ℤ (Localization.Away f)) :
    letI : Module ℤ k := Algebra.toModule
    letI : Module ℤ A := Algebra.toModule
    Algebra.Smooth k (Localization.Away ((1 : k) ⊗ₜ[ℤ] f)) := by
  letI := hs
  letI := Algebra.IsStandardSmoothOfRelativeDimension.baseChange (R := ℤ)
    (S := Localization.Away f) 52 k
  let e := IsLocalization.Away.tensorProductEquivTMulRight ℤ k f (Localization.Away f)
  letI : Module ℤ k := Algebra.toModule
  letI : Module ℤ A := Algebra.toModule
  letI : Algebra.IsStandardSmoothOfRelativeDimension 52 k (Localization.Away ((1 : k) ⊗ₜ[ℤ] f)) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 52 e
  letI : Algebra.IsStandardSmooth k (Localization.Away ((1 : k) ⊗ₜ[ℤ] f)) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 52
  exact inferInstance

set_option backward.isDefEq.respectTransparency false in
private lemma fiberSmooth (P : IntegralPresentation) (e : P.Coordinates →ₐ[ℤ] ℤ)
    (he : P.IsIdentity e) (k : Type) [Field k] [IsAlgClosed k]
    (f : P.Coordinates) (hf : algebraMap ℤ k (e f) ≠ 0)
    (hs : Algebra.IsStandardSmoothOfRelativeDimension 52 ℤ (Localization.Away f)) :
    Smooth (fiberStructure P k) := by
  let A := FiberRing P k
  letI : Algebra.FinitePresentation k A := fiberFinitePresentation P k
  let b : A := (Algebra.TensorProduct.includeRight : P.Coordinates →ₐ[ℤ] A) f
  letI : Algebra.Smooth k (Localization.Away b) :=
    smooth_baseChange_away k P.Coordinates f hs
  let a₀ : A →ₐ[k] k := (AlgHom.liftEquiv ℤ k P.Coordinates k) ((Algebra.ofId ℤ k).comp e)
  have ha₀ : points P k k a₀ = 1 := by
    change albertPoints P k ((AlgHom.liftEquiv ℤ k P.Coordinates k).symm
      (AlgHom.liftEquiv ℤ k P.Coordinates k ((Algebra.ofId ℤ k).comp e))) = 1
    rw [Equiv.symm_apply_apply, section_is_identity P e he]
    exact identityPoint_over P k
  have ha₀b : a₀ b ≠ 0 := by
    letI : Module ℤ k := Algebra.toModule
    letI : Module ℤ P.Coordinates := Algebra.toModule
    change (AlgHom.liftEquiv ℤ k P.Coordinates k ((Algebra.ofId ℤ k).comp e))
      ((1 : k) ⊗ₜ[ℤ] f) ≠ 0
    rw [AlgHom.liftEquiv_tmul, one_smul]
    exact hf
  have hclosed : closedPoints (PrimeSpectrum A) ⊆ Algebra.smoothLocus k A := by
    intro p hp
    obtain ⟨a, rfl⟩ := exists_rationalPoint (k := k) (A := A) p (mem_closedPoints_iff.mp hp)
    let g := (points P k k a)⁻¹
    let t := translation P g
    have ht : a.comp t.toAlgHom = a₀ := by
      apply (points P k k).injective
      change points P k k (a.comp (translate P g)) = _
      rw [translate_eval, extendAuto_self, ha₀]
      exact inv_mul_cancel _
    have htb : primeOfHom (A := A) (k := k) a ∈ PrimeSpectrum.basicOpen (t b) :=
      show a (t b) ≠ 0 from (DFunLike.congr_fun ht b).symm ▸ ha₀b
    exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := k) (A := A)).mpr
      (translating_chart t b) htb
  have hU : Algebra.smoothLocus k A = Set.univ := by
    by_contra h
    have hne : (Algebra.smoothLocus k A)ᶜ.Nonempty := by
      rwa [Set.nonempty_compl]
    haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
    obtain ⟨p, hp, hc⟩ := nonempty_inter_closedPoints hne
      (Algebra.isOpen_smoothLocus (R := k) (A := A)).isClosed_compl.isLocallyClosed
    exact hp (hclosed hc)
  have hsmooth : Algebra.Smooth k A := ⟨Algebra.smoothLocus_eq_univ_iff.mp hU, inferInstance⟩
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
  exact RingHom.smooth_algebraMap.mpr hsmooth

section OrbitParameters

open MvPolynomial
open scoped DualNumber
open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticJordan)
open _root_.Specs.AdvCommAlg.Differentials.Tangent (PointLifts)
open IntegralZornDirectionsSpecification (DirectionIndex)

open private frameWord frameWord_isAuto frameWord_natural frameWord_zero
  frameProduct_jet parameterVelocities frameAxis_jet_eq_iff frameAxis_eval_zero frameAxis_eval_one
  modelOfVariables_map pairedFunctions_map precomposeLifts openImage_of_lifts quadric_smooth
  from LinearAlgebraicGroups.Albert.IdempotentCharts
open private shortFamily_evaluates mapModel_axis
  from LinearAlgebraicGroups.Albert.ShortDirections

/-- The directions in the first orbit are the two blocks incident to axis zero.
The directions in the second orbit lie in its opposite block. -/
private def relevant (corner : Bool) (i : Fin 3) : Prop :=
  if corner then i = 0 else i ≠ 0

private instance (corner : Bool) (i : Fin 3) : Decidable (relevant corner i) :=
  inferInstanceAs (Decidable (if corner then i = 0 else i ≠ 0))

private abbrev OrbitIndex (corner : Bool) := {i : Fin 3 // relevant corner i} × DirectionIndex

private abbrev OrbitParameters (k : Type) [Field k] (corner : Bool) :=
  MvPolynomial (OrbitIndex corner) k

private def extendParameters {S : Type} [Zero S] (corner : Bool) (t : OrbitIndex corner → S) :
    Fin 3 × DirectionIndex → S :=
  fun i => if h : relevant corner i.1 then t (⟨i.1, h⟩, i.2) else 0

private lemma extendParameters_map {S T : Type} [CommRing S] [CommRing T]
    (f : S →+* T) (corner : Bool) (t : OrbitIndex corner → S) :
    f ∘ extendParameters corner t = extendParameters corner (f ∘ t) := by
  funext i
  by_cases hi : relevant corner i.1 <;> simp [extendParameters, hi]

private def orbitWord {S : Type} [CommRing S] (corner : Bool) (t : OrbitIndex corner → S) :
    Automorphisms S :=
  ⟨frameWord (extendParameters corner t) Finset.univ.toList,
    (mem_splitAutomorphisms _).mpr (frameWord_isAuto _ _)⟩

private lemma orbitWord_natural {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
    (corner : Bool) (t : OrbitIndex corner → S) (x : Model S) :
    mapModel f (orbitWord corner t |>.val x) =
      (orbitWord corner (f ∘ t)).val (mapModel f x) := by
  change mapModel f (frameWord (extendParameters corner t) _ x) = _
  rw [frameWord_natural, extendParameters_map]
  rfl

private lemma cornerWord_fixes {S : Type} [CommRing S] (t : OrbitIndex true → S) :
    (orbitWord true t).val (frameAxis 0) = frameAxis 0 := by
  change frameWord (extendParameters true t) _ (frameAxis 0) = _
  generalize (Finset.univ : Finset (Fin 3 × DirectionIndex)).toList = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    change ShortDirections.shortFamily S i.1 i.2
      (Multiplicative.ofAdd (extendParameters true t i))
      (frameWord (extendParameters true t) l (frameAxis 0)) = _
    rw [ih]
    by_cases hi : i.1 = 0
    · simpa only [hi] using (shortFamily_evaluates i.1 i.2 (extendParameters true t i)).1
    · rw [show extendParameters true t i = 0 by simp [extendParameters, relevant, hi],
        show Multiplicative.ofAdd (0 : S) = 1 from rfl, map_one]
      rfl

private abbrev OrbitRing (k : Type) [Field k] (corner : Bool) :=
  match corner with
  | false => IdempotentRing k
  | true => SecondRing k

@[instance_reducible]
private instance orbitRingCommRing (k : Type) [Field k] (corner : Bool) : CommRing (OrbitRing k corner) :=
  match corner with
  | false => inferInstanceAs (CommRing (IdempotentRing k))
  | true => inferInstanceAs (CommRing (SecondRing k))

@[instance_reducible]
private instance orbitRingAlgebra (k : Type) [Field k] (corner : Bool) : Algebra k (OrbitRing k corner) :=
  match corner with
  | false => inferInstanceAs (Algebra k (IdempotentRing k))
  | true => inferInstanceAs (Algebra k (SecondRing k))

private abbrev OrbitCondition {S : Type} [CommRing S] (corner : Bool) (x : Model S) : Prop :=
  match corner with
  | false => IsRankOneIdempotent x
  | true => IsFramePair (frameAxis 0) x

private def orbitAxis {S : Type} [CommRing S] (corner : Bool) : Model S :=
  frameAxis (if corner then 1 else 0)

private lemma map_orbitAxis {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
    (corner : Bool) : mapModel f (orbitAxis corner : Model S) = (orbitAxis corner : Model T) :=
  mapModel_axis _ _

private lemma acted_orbitCondition {S : Type} [CommRing S] (corner : Bool)
    (g : Automorphisms S) (hg : corner = true → g.val (frameAxis 0) = frameAxis 0)
    (x : Model S) (hx : OrbitCondition corner x) :
    OrbitCondition corner (g.val x) := by
  have h := IdempotentCharts.orbitValues S g.val ((mem_splitAutomorphisms _).mp g.property)
  cases corner
  · exact (h.1 x).mpr hx
  · simpa only [hg rfl] using (h.2.1 (frameAxis 0) x).mpr hx

private lemma orbitAxis_condition (S : Type) [CommRing S] (corner : Bool) :
    OrbitCondition corner (orbitAxis corner : Model S) := by
  have h := (IdempotentCharts.orbitValues S 1
    ((mem_splitAutomorphisms (1 : Model S ≃ₗ[S] Model S)).mp (Subgroup.one_mem _))).2.2
  cases corner
  · exact h.1
  · exact h

private def orbitPoints (k S : Type) [Field k] [CommRing S] [Algebra k S] (corner : Bool) :
    (OrbitRing k corner →ₐ[k] S) ≃ {x : Model S // OrbitCondition corner x} :=
  match corner with
  | false => (IdempotentCharts.firstRepresentation k S).choose
  | true => (IdempotentCharts.secondRepresentation k S).choose

private lemma orbitPoints_natural {k S T : Type} [Field k] [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) (corner : Bool)
    (a : OrbitRing k corner →ₐ[k] S) :
    mapModel f.toRingHom (orbitPoints k S corner a).val =
      (orbitPoints k T corner (f.comp a)).val := by
  cases corner
  · change mapModel f.toRingHom ((IdempotentCharts.firstRepresentation k S).choose a).val =
      ((IdempotentCharts.firstRepresentation k T).choose (f.comp a)).val
    rw [(IdempotentCharts.firstRepresentation k S).choose_spec,
      (IdempotentCharts.firstRepresentation k T).choose_spec]
    exact (modelOfVariables_map f.toRingHom _).symm
  · change mapModel f.toRingHom ((IdempotentCharts.secondRepresentation k S).choose a).val =
      ((IdempotentCharts.secondRepresentation k T).choose (f.comp a)).val
    rw [(IdempotentCharts.secondRepresentation k S).choose_spec,
      (IdempotentCharts.secondRepresentation k T).choose_spec]
    let z := quadricOfHom k (Option (Fin 3)) a
    apply Prod.ext
    · funext i
      change f (if i = 0 then 0 else if i = 1 then z none else 1 - z none) =
        (if i = 0 then 0 else if i = 1 then f (z none) else 1 - f (z none))
      by_cases h₀ : i = 0
      · rw [ite_eq_left h₀, ite_eq_left h₀, map_zero]
      · rw [ite_eq_right h₀, ite_eq_right h₀]
        by_cases h₁ : i = 1
        · rw [ite_eq_left h₁, ite_eq_left h₁]
        · rw [ite_eq_right h₁, ite_eq_right h₁, map_sub, map_one]
    · funext i
      apply (LinearAlgebraicGroups.Composition.Zorn.pairedFunctions T).injective
      funext j
      change LinearAlgebraicGroups.Composition.Zorn.pairedFunctions T
        (LinearAlgebraicGroups.Composition.ZornSpecification.mapCoordinates f.toRingHom
          (Pi.single (M := fun _ : Fin 3 => LinearAlgebraicGroups.Composition.Zorn S) 0
            (octonionOfPairs fun j => z (some j)) i)) j =
        LinearAlgebraicGroups.Composition.Zorn.pairedFunctions T
          (Pi.single (M := fun _ : Fin 3 => LinearAlgebraicGroups.Composition.Zorn T) 0
            (octonionOfPairs fun j => f (z (some j))) i) j
      rw [pairedFunctions_map]
      by_cases hi : i = 0
      · subst i
        simp only [Pi.single_eq_same, octonionOfPairs, LinearEquiv.apply_symm_apply]
        cases j <;> rfl
      · simp only [Pi.single_eq_of_ne hi, map_zero, Pi.zero_apply]

private lemma cornerWord_condition {S : Type} [CommRing S] (corner : Bool) (t : OrbitIndex corner → S) :
    OrbitCondition corner ((orbitWord corner t).val (orbitAxis corner)) := by
  apply acted_orbitCondition corner _ _ _ (orbitAxis_condition S corner)
  rintro rfl
  exact cornerWord_fixes t

private def parameterMap (k : Type) [Field k] (corner : Bool) :
    OrbitRing k corner →ₐ[k] OrbitParameters k corner :=
  (orbitPoints k _ corner).symm ⟨(orbitWord corner X).val (orbitAxis corner), cornerWord_condition corner X⟩

private lemma parameterMap_eval {k S : Type} [Field k] [CommRing S] [Algebra k S]
    (corner : Bool) (f : OrbitParameters k corner →ₐ[k] S) :
    (orbitPoints k S corner (f.comp (parameterMap k corner))).val =
      (orbitWord corner (fun i => f (X i))).val (orbitAxis corner) := by
  rw [← orbitPoints_natural f, parameterMap, Equiv.apply_symm_apply]
  exact (orbitWord_natural f.toRingHom corner X _).trans
    (congrArg ((orbitWord corner (f ∘ X)).val) (map_orbitAxis f.toRingHom corner))

private def parameterOrigin (k : Type) [Field k] (corner : Bool) :
    OrbitParameters k corner →ₐ[k] k := aeval fun _ => 0

private lemma parameterOrigin_eval (k : Type) [Field k] (corner : Bool) :
    (orbitPoints k k corner ((parameterOrigin k corner).comp (parameterMap k corner))).val =
      orbitAxis corner := by
  rw [parameterMap_eval]
  simp only [parameterOrigin, aeval_X]
  have h : extendParameters corner (fun _ => (0 : k)) = fun _ => 0 := by
    funext i
    simp [extendParameters]
  change frameWord (extendParameters corner (fun _ => (0 : k))) _ (orbitAxis corner) =
    orbitAxis corner
  rw [h, frameWord_zero]
  rfl

private def parameterLifts (k : Type) [Field k] (corner : Bool) :
    (OrbitIndex corner → k) ≃ PointLifts k (OrbitParameters k corner) k (parameterOrigin k corner) where
  toFun t := ⟨aeval (TrivSqZeroExt.inr ∘ t), by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X, parameterOrigin]
    rfl⟩
  invFun f i := (f.val (X i)).snd
  left_inv t := by
    funext i
    change (aeval (R := k) (TrivSqZeroExt.inr ∘ t) (X i)).snd = _
    rw [aeval_X]
    rfl
  right_inv f := by
    apply Subtype.ext
    apply MvPolynomial.algHom_ext
    intro i
    change aeval (R := k) (fun j => TrivSqZeroExt.inr (f.val (X j)).snd) (X i) = _
    rw [aeval_X]
    apply TrivSqZeroExt.ext
    · have h := DFunLike.congr_fun f.property (X i)
      exact (h.trans (aeval_X _ _)).symm
    · rfl

private lemma parameterVelocities_apply {k : Type} [Field k]
    (t : Fin 3 × DirectionIndex → k) (i : Fin 3) :
    parameterVelocities k t i =
      (IntegralZornDirections.directionBasis k).equivFun.symm (fun j => t (i, j)) := rfl

private lemma jet_eq_iff {k : Type} [Field k] (corner : Bool) (J : QuadraticJordan k (Model k))
    (hu : J.unit = CubicSpecification.cubicUnit) (ho : ∀ a b, J.groundOp a b = modelOp a b)
    (D E : splitDerivations J)
    (hD : corner = true → frameEvaluation k D.val 2 = 0)
    (hE : corner = true → frameEvaluation k E.val 2 = 0) :
    axisJet D.val (if corner then 1 else 0) = axisJet E.val (if corner then 1 else 0) ↔
      ∀ i : Fin 3, relevant corner i → frameEvaluation k D.val i = frameEvaluation k E.val i := by
  rw [frameAxis_jet_eq_iff]
  cases corner
  · change D.val (frameAxis 0) = E.val (frameAxis 0) ↔ _
    rw [frameAxis_eval_zero J hu ho, frameAxis_eval_zero J hu ho]
    constructor
    · intro h i hi
      fin_cases i
      · exact (hi rfl).elim
      · exact neg_injective (congrArg (fun x : Model k => x.2 1) h)
      · have he := congrArg (fun x : Model k => x.2 2) h
        exact he
    · intro h
      rw [h 1 (by decide), h 2 (by decide)]
  · change D.val (frameAxis 1) = E.val (frameAxis 1) ↔ _
    rw [frameAxis_eval_one J hu ho, frameAxis_eval_one J hu ho, hD rfl, hE rfl]
    constructor
    · intro h i hi
      have hi' : i = 0 := hi
      subst i
      have he := congrArg (fun x : Model k => x.2 0) h
      exact he
    · intro h
      rw [h 0 (by decide)]

private lemma restricted_velocity {k : Type} [Field k] (corner : Bool)
    (t : OrbitIndex corner → k) (i : Fin 3) (hi : ¬ relevant corner i) :
    parameterVelocities k (extendParameters corner t) i = 0 := by
  rw [parameterVelocities_apply]
  simp [extendParameters, hi]

private lemma restrict_velocity {k : Type} [Field k] (corner : Bool)
    (v : Fin 3 → LinearAlgebraicGroups.Composition.Zorn k) :
    ∃ t : OrbitIndex corner → k, ∀ i, relevant corner i →
      parameterVelocities k (extendParameters corner t) i = v i := by
  refine ⟨fun i => (IntegralZornDirections.directionBasis k).equivFun (v i.1) i.2, ?_⟩
  intro i hi
  rw [parameterVelocities_apply]
  simp [extendParameters, hi]

private lemma corner_frame_evaluation {k : Type} [Field k] (J : QuadraticJordan k (Model k))
    (hu : J.unit = CubicSpecification.cubicUnit) (ho : ∀ a b, J.groundOp a b = modelOp a b)
    (D : splitDerivations J) (hD : D.val (frameAxis 0) = 0) :
    frameEvaluation k D.val 2 = 0 := by
  rw [frameAxis_eval_zero J hu ho] at hD
  exact congrArg (fun x : Model k => x.2 2) hD

private lemma parameter_jet {k : Type} [Field k] (corner : Bool) (J : QuadraticJordan k (Model k))
    (hu : J.unit = CubicSpecification.cubicUnit) (ho : ∀ a b, J.groundOp a b = modelOp a b)
    (t : OrbitIndex corner → k) :
    ∃ D : splitDerivations J,
      (orbitPoints k (DualNumber k) corner
        (((parameterLifts k corner t).val).comp (parameterMap k corner))).val =
        axisJet D.val (if corner then 1 else 0) ∧
      frameEvaluation k D.val = parameterVelocities k (extendParameters corner t) := by
  obtain ⟨D, hD, he⟩ := frameProduct_jet J hu ho (extendParameters corner t)
  refine ⟨D, ?_, he⟩
  rw [parameterMap_eval]
  have ht (i : Fin 3 × DirectionIndex) :
      extendParameters corner (((TrivSqZeroExt.inr : k → DualNumber k)) ∘ t) i =
        (TrivSqZeroExt.inr ∘ extendParameters corner t) i := by
    by_cases hi : relevant corner i.1 <;> simp [extendParameters, hi]
  change frameWord (extendParameters corner
    (fun i => (aeval (R := k) (TrivSqZeroExt.inr ∘ t)) (X i))) Finset.univ.toList (frameAxis _) = _
  simp only [aeval_X]
  rw [funext ht]
  exact hD _

private lemma parameterLifts_bijective (k : Type) [Field k] (corner : Bool) :
    Function.Bijective (precomposeLifts (parameterMap k corner) (parameterOrigin k corner)) := by
  apply ((parameterLifts k corner).bijective_comp _).mp
  obtain ⟨J, _, hu, ho, _, _, _, _⟩ := Triality.cubicFrameStabilizer k
  let F := precomposeLifts (parameterMap k corner) (parameterOrigin k corner) ∘ parameterLifts k corner
  change Function.Bijective F
  have ht (t : OrbitIndex corner → k) :
      ∃ D : splitDerivations J,
        (orbitPoints k (DualNumber k) corner (F t).val).val =
          axisJet D.val (if corner then 1 else 0) ∧
        frameEvaluation k D.val = parameterVelocities k (extendParameters corner t) ∧
        (corner = true → frameEvaluation k D.val 2 = 0) := by
    obtain ⟨D, he, hv⟩ := parameter_jet corner J hu ho t
    refine ⟨D, he, hv, ?_⟩
    rintro rfl
    rw [hv]
    exact restricted_velocity true t 2 (by decide)
  constructor
  · intro s t hst
    obtain ⟨D, hD, hvD, h0D⟩ := ht s
    obtain ⟨E, hE, hvE, h0E⟩ := ht t
    have he := (jet_eq_iff corner J hu ho D E h0D h0E).mp (by rw [← hD, hst, hE])
    funext i
    have h := he i.1 i.1.property
    rw [hvD, hvE, parameterVelocities_apply, parameterVelocities_apply] at h
    simpa only [extendParameters, dite_eq_left i.1.property] using
      congrFun ((IntegralZornDirections.directionBasis k).equivFun.symm.injective h) i.2
  · intro f
    let p := orbitPoints k (DualNumber k) corner f.val
    have hr : reduceModel k p.val = orbitAxis corner := by
      change mapModel (TrivSqZeroExt.fstHom k k k).toRingHom (orbitPoints k _ corner f.val).val = _
      rw [orbitPoints_natural, f.property, parameterOrigin_eval]
    obtain ⟨D, hD, h0D⟩ : ∃ D : splitDerivations J,
        axisJet D.val (if corner then 1 else 0) = p.val ∧
          (corner = true → frameEvaluation k D.val 2 = 0) := by
      cases corner
      · obtain ⟨D, hD⟩ := IdempotentCharts.firstOrbitDifferential k J hu ho p hr
        exact ⟨D, hD, by simp⟩
      · obtain ⟨D, hz, hD⟩ := IdempotentCharts.secondOrbitDifferential k J hu ho p hr
        exact ⟨D, hD, fun _ => corner_frame_evaluation J hu ho D hz⟩
    obtain ⟨t, hv⟩ := restrict_velocity corner (frameEvaluation k D.val)
    obtain ⟨E, hE, hvE, h0E⟩ := ht t
    refine ⟨t, Subtype.ext ((orbitPoints k _ corner).injective (Subtype.ext ?_))⟩
    rw [hE, ← hD, jet_eq_iff corner J hu ho E D h0E h0D, hvE]
    exact hv

private instance orbitFinitePresentation (k : Type) [Field k] (corner : Bool) :
    Algebra.FinitePresentation k (OrbitRing k corner) := by
  cases corner
  · change Algebra.FinitePresentation k (IdempotentRing k)
    unfold IdempotentRing idempotentIdeal
    exact Algebra.FinitePresentation.quotient (Submodule.fg_span
      (((Set.finite_range _).insert _).union (Set.finite_range _)))
  · exact (quadric_smooth k (Option (Fin 3))).finitePresentation

private lemma parameterOpenImage (k : Type) [Field k] (corner : Bool) :
    ∃ s : OrbitParameters k corner, parameterOrigin k corner s ≠ 0 ∧
      IsOpen (Set.range (PrimeSpectrum.comap
        ((algebraMap _ (Localization.Away s)).comp (parameterMap k corner).toRingHom))) :=
  openImage_of_lifts (parameterMap k corner) (parameterOrigin k corner) (parameterLifts_bijective k corner)

end OrbitParameters

section OrbitOverlap

open MvPolynomial
open IntegralZornDirectionsSpecification (DirectionIndex)
open private mapModel_axis from LinearAlgebraicGroups.Albert.ShortDirections

private lemma rationalPoint_injective {k A : Type} [Field k] [CommRing A] [Algebra k A] :
    Function.Injective (primeOfHom (k := k) (A := A)) := by
  intro a b hab
  ext x
  have hx : x - algebraMap k A (a x) ∈ (primeOfHom a).asIdeal := by
    change a (x - algebraMap k A (a x)) = 0
    simp
  rw [hab] at hx
  change b (x - algebraMap k A (a x)) = 0 at hx
  rw [map_sub, AlgHom.commutes] at hx
  exact (sub_eq_zero.mp hx).symm

private lemma rationalPoint_lift {k A B : Type} [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra.FiniteType k B] (f : A →ₐ[k] B)
    {p : PrimeSpectrum A} (hp : IsClosed {p}) (hr : p ∈ Set.range (PrimeSpectrum.comap f.toRingHom)) :
    ∃ b : B →ₐ[k] k, primeOfHom (b.comp f) = p := by
  rcases hr with ⟨q, rfl⟩
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  let r : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  obtain ⟨b, hb⟩ := exists_rationalPoint (k := k) r ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm)
  refine ⟨b, ?_⟩
  rw [← primeOfHom_comp, hb]
  apply PrimeSpectrum.ext
  have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hp
  exact (hmax.eq_of_le (PrimeSpectrum.comap f.toRingHom r).isPrime.ne_top
    (Ideal.comap_mono hqm)).symm

private def FixesFirst {S : Type} [CommRing S] (g : Automorphisms S) : Prop :=
  g.val (frameAxis 0) = frameAxis 0

private lemma extendAuto_fixed {k S : Type} [Field k] [CommRing S] [Algebra k S]
    (g : Automorphisms k) (h : FixesFirst g) : FixesFirst (extendAuto g S) := by
  have he := extendFrameAuto_natural g.val (Algebra.ofId k S) (frameAxis 0)
  change mapModel (algebraMap k S) (extendFrameAuto g.val k (frameAxis 0)) =
    extendFrameAuto g.val S (mapModel (algebraMap k S) (frameAxis 0)) at he
  rw [extendFrameAuto_self, h, mapModel_axis] at he
  exact he.symm

private lemma inverse_fixesFirst {S : Type} [CommRing S] {g : Automorphisms S}
    (hg : FixesFirst g) : FixesFirst (g⁻¹) := by
  change g.val.symm (frameAxis 0) = frameAxis 0
  exact (congrArg g.val.symm hg).symm.trans
    (LinearEquiv.symm_apply_apply g.val (frameAxis 0))

private def orbitTranslate {k : Type} [Field k] (corner : Bool) (g : Automorphisms k)
    (hg : corner = true → FixesFirst g) :
    OrbitRing k corner →ₐ[k] OrbitRing k corner :=
  let a := (orbitPoints k _ corner (AlgHom.id k _)).val
  let h := extendAuto g (OrbitRing k corner)
  (orbitPoints k _ corner).symm
    ⟨h.val a, acted_orbitCondition corner h (fun e => extendAuto_fixed g (hg e))
      a (orbitPoints k _ corner (AlgHom.id k _)).property⟩

private lemma orbitTranslate_eval {k S : Type} [Field k] [CommRing S] [Algebra k S]
    (corner : Bool) (g : Automorphisms k) (hg : corner = true → FixesFirst g)
    (a : OrbitRing k corner →ₐ[k] S) :
    (orbitPoints k S corner (a.comp (orbitTranslate corner g hg))).val =
      (extendAuto g S).val (orbitPoints k S corner a).val := by
  rw [← orbitPoints_natural a, orbitTranslate, Equiv.apply_symm_apply]
  change mapModel a.toRingHom (extendFrameAuto g.val _ _) = _
  refine (extendFrameAuto_natural g.val a _).trans ?_
  exact congrArg (extendFrameAuto g.val S)
    ((orbitPoints_natural a corner (AlgHom.id k _)).trans
      (congrArg (fun f => (orbitPoints k S corner f).val) (AlgHom.comp_id a)))

private lemma orbitTranslate_cancel {k : Type} [Field k] (corner : Bool) (g : Automorphisms k)
    (hg : corner = true → FixesFirst g) (hgi : corner = true → FixesFirst g⁻¹) :
    (orbitTranslate corner g hg).comp (orbitTranslate corner g⁻¹ hgi) = AlgHom.id k _ := by
  apply (orbitPoints k _ corner).injective
  apply Subtype.ext
  rw [orbitTranslate_eval, extendAuto_inv]
  have ha : orbitTranslate corner g hg = (AlgHom.id k _).comp (orbitTranslate corner g hg) :=
    (AlgHom.id_comp _).symm
  rw [ha, orbitTranslate_eval]
  exact LinearEquiv.symm_apply_apply _ _

/-- Intersect an open orbit image with its translate and lift the intersection point to
both parameter spaces. The resulting two words differ by an element fixing the axis. -/
private lemma word_factorization (k : Type) [Field k] [IsAlgClosed k] (corner : Bool)
    (g : Automorphisms k) (hg : corner = true → FixesFirst g) :
    ∃ (s t : OrbitIndex corner → k) (h : Automorphisms k),
      (corner = true → FixesFirst h) ∧ h.val (orbitAxis corner) = orbitAxis corner ∧
      g = orbitWord corner s * h * (orbitWord corner t)⁻¹ := by
  obtain ⟨z, hz, ho⟩ := parameterOpenImage k corner
  let C := Localization.Away z
  let f : OrbitRing k corner →ₐ[k] C :=
    (IsScalarTower.toAlgHom k (OrbitParameters k corner) C).comp (parameterMap k corner)
  let U := Set.range (PrimeSpectrum.comap f.toRingHom)
  have hU : IsOpen U := ho
  let a₀ : C →ₐ[k] k := IsLocalization.Away.liftAlgHom z (isUnit_iff_ne_zero.mpr hz)
  have hne : U.Nonempty := ⟨_, ⟨primeOfHom a₀, rfl⟩⟩
  let hgi : corner = true → FixesFirst g⁻¹ := fun e => inverse_fixesFirst (hg e)
  let T := AlgEquiv.ofAlgHom (orbitTranslate corner g hg) (orbitTranslate corner g⁻¹ hgi)
    (orbitTranslate_cancel corner g hg hgi)
    (by simpa only [inv_inv] using orbitTranslate_cancel corner g⁻¹ hgi (fun e => hg e))
  have hT : IsOpenMap (PrimeSpectrum.comap T.toRingHom) :=
    (PrimeSpectrum.homeomorphOfRingEquiv T.toRingEquiv).symm.isOpenMap
  letI : IrreducibleSpace (PrimeSpectrum (OrbitRing k corner)) := by
    cases corner
    · exact (IdempotentCharts.firstGeometry k).2.1
    · exact (IdempotentCharts.secondGeometry k).2.1
  letI : IsJacobsonRing (OrbitRing k corner) := isJacobsonRing_of_finiteType (A := k)
  obtain ⟨p, hp, hc⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing _
    (hU.inter (hT _ hU))
    (nonempty_preirreducible_inter hU (hT _ hU) hne (hne.image _))
  letI : Algebra.FinitePresentation (OrbitParameters k corner) C :=
    IsLocalization.Away.finitePresentation z
  letI : Algebra.FinitePresentation k C :=
    Algebra.FinitePresentation.trans k (OrbitParameters k corner) C
  obtain ⟨a, ha⟩ := rationalPoint_lift f hc hp.1
  have hp' : p ∈ Set.range (PrimeSpectrum.comap (f.comp T.toAlgHom).toRingHom) := by
    obtain ⟨q, ⟨r, rfl⟩, hq⟩ := hp.2
    exact ⟨r, hq⟩
  obtain ⟨b, hb⟩ := rationalPoint_lift (f.comp T.toAlgHom) hc hp'
  have he := rationalPoint_injective (ha.trans hb.symm)
  change a.comp f = b.comp (f.comp (orbitTranslate corner g hg)) at he
  let s : OrbitIndex corner → k := fun i => a (algebraMap (OrbitParameters k corner) C (X i))
  let t : OrbitIndex corner → k := fun i => b (algebraMap (OrbitParameters k corner) C (X i))
  have heval : (orbitWord corner s).val (orbitAxis corner) =
      g.val ((orbitWord corner t).val (orbitAxis corner)) := by
    have hcomp : a.comp f = (b.comp f).comp (orbitTranslate corner g hg) :=
      he.trans (AlgHom.comp_assoc _ _ _).symm
    have hs := parameterMap_eval corner (a.comp (IsScalarTower.toAlgHom k _ C))
    have ht := parameterMap_eval corner (b.comp (IsScalarTower.toAlgHom k _ C))
    have ha' : (orbitPoints k k corner (a.comp f)).val = (orbitWord corner s).val (orbitAxis corner) :=
      (congrArg (fun m => (orbitPoints k k corner m).val) (AlgHom.comp_assoc _ _ _).symm).trans hs
    have hb' : (orbitPoints k k corner (b.comp f)).val = (orbitWord corner t).val (orbitAxis corner) :=
      (congrArg (fun m => (orbitPoints k k corner m).val) (AlgHom.comp_assoc _ _ _).symm).trans ht
    calc
      _ = (orbitPoints k k corner (a.comp f)).val := ha'.symm
      _ = (orbitPoints k k corner ((b.comp f).comp (orbitTranslate corner g hg))).val :=
        congrArg (fun m => (orbitPoints k k corner m).val) hcomp
      _ = (extendAuto g k).val (orbitPoints k k corner (b.comp f)).val :=
        orbitTranslate_eval corner g hg (b.comp f)
      _ = _ := by rw [extendAuto_self, hb']

  let h := (orbitWord corner s)⁻¹ * g * orbitWord corner t
  refine ⟨s, t, h, ?_, ?_, ?_⟩
  · rintro rfl
    change (orbitWord true s).val.symm (g.val ((orbitWord true t).val (frameAxis 0))) = _
    rw [cornerWord_fixes, hg rfl]
    exact inverse_fixesFirst (cornerWord_fixes s)
  · change (orbitWord corner s).val.symm (g.val ((orbitWord corner t).val (orbitAxis corner))) = _
    rw [← heval, LinearEquiv.symm_apply_apply]
  · simp [h, mul_assoc]

end OrbitOverlap

section Irreducibility

open MvPolynomial
open TrialitySpecification (frameStabilizer FixesFrame)
open IntegralZornDirectionsSpecification (DirectionIndex)
open SplitSpinSpecification (EvenSwitches)
open private integralCoordinates from LinearAlgebraicGroups.Albert.FrameTangentRank
open private framePoints framePoints_natural frameInclusion from
  LinearAlgebraicGroups.Albert.ShortDirections
open private standardDet StandardRing from LinearAlgebraicGroups.Albert.SplitSpin
open private fieldSpinRing fieldDenominator fieldOpens_cover chartScalarChange
  switchDenominator switchChartIso standardChart_domain fieldChart_overlap from LinearAlgebraicGroups.Albert.SpinWeights

private instance spinFiberCommRing (k : Type) [Field k] : CommRing (fieldSpinRing k) :=
  inferInstance

private lemma spinChart_domain (k : Type) [Field k] (a : integralCoordinates)
    (e : StandardRing 4 ≃ₐ[ℤ] Localization.Away a) :
    IsDomain (Localization.Away (fieldDenominator k a)) := by
  let eK := (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) e).trans (chartScalarChange k a)
  have := standardChart_domain k
  exact Function.Injective.isDomain eK.symm eK.symm.injective

/-- A domain chart meeting every domain chart of a principal open cover detects
vanishing in the entire ring. -/
private lemma domain_of_principalOpen_cover {A I : Type} [CommRing A] (d : A) (a : I → A)
    [IsDomain (Localization.Away d)] (hcover : (⨆ j, PrimeSpectrum.basicOpen (a j)) = ⊤)
    (hdom : ∀ j, IsDomain (Localization.Away (a j)))
    (hinter : ∀ j, ((PrimeSpectrum.basicOpen d : Set (PrimeSpectrum A)) ∩
      PrimeSpectrum.basicOpen (a j)).Nonempty) : IsDomain A := by
  refine Function.Injective.isDomain (algebraMap A (Localization.Away d))
    ((injective_iff_map_eq_zero _).mpr fun x hx => ?_)
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers d)
    (Localization.Away d) x).mp hx
  obtain ⟨n, hn⟩ := m.property
  have he : d ^ n * x = 0 := (congrArg (· * x) hn).trans hm
  have hz (j : I) : algebraMap A (Localization.Away (a j)) x = 0 := by
    letI := hdom j
    have hdn : algebraMap A (Localization.Away (a j)) d ≠ 0 := by
      obtain ⟨p, hp, hq⟩ := hinter j
      change d ∉ p.asIdeal at hp
      have hq' : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away (a j)))) := by
        rw [PrimeSpectrum.localization_away_comap_range _ (a j)]
        exact hq
      obtain ⟨q, rfl⟩ := hq'
      intro h
      exact hp (show algebraMap A (Localization.Away (a j)) d ∈ q.asIdeal from h ▸ q.asIdeal.zero_mem)
    have h := congrArg (algebraMap A (Localization.Away (a j))) he
    simp only [map_mul, map_pow, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hdn)
  apply eq_zero_of_localization x
  intro P hP
  let p : PrimeSpectrum A := ⟨P, hP.isPrime⟩
  have hp : p ∈ ⨆ j, PrimeSpectrum.basicOpen (a j) := by
    rw [hcover]
    exact trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  let φ := IsLocalization.Away.lift (S := Localization.Away (a j)) (a j)
    ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P _).mpr hj)
  have h := congrArg φ (hz j)
  rw [map_zero, IsLocalization.Away.lift_eq] at h
  exact h

private lemma spinFiber_domain (k : Type) [Field k] : IsDomain (fieldSpinRing k) := by
  letI := spinChart_domain k (standardDet 4) (AlgEquiv.refl)
  exact domain_of_principalOpen_cover (fieldDenominator k (standardDet 4))
    (fun J : EvenSwitches 4 => fieldDenominator k (switchDenominator J))
    (fieldOpens_cover k)
    (fun J => spinChart_domain k (switchDenominator J) (switchChartIso J))
    (fieldChart_overlap k)

private abbrev FactorIndex :=
  (OrbitIndex false × Bool) ⊕ (OrbitIndex true × Bool)

private abbrev FactorRing (k : Type) [Field k] := MvPolynomial FactorIndex (fieldSpinRing k)

private def framePointsOver (k S : Type) [Field k] [CommRing S] [Algebra k S] :
    (fieldSpinRing k →ₐ[k] S) ≃ frameStabilizer (R := S) :=
  (AlgHom.liftEquiv ℤ k integralCoordinates S).symm.trans (framePoints S)

private lemma framePointsOver_natural {k S T : Type} [Field k] [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) (a : fieldSpinRing k →ₐ[k] S) (x : Model S) :
    mapModel f.toRingHom ((framePointsOver k S a).val x) =
      (framePointsOver k T (f.comp a)).val (mapModel f.toRingHom x) :=
  framePoints_natural (f.restrictScalars ℤ) _ x

private def factorPoint {k S : Type} [Field k] [CommRing S] [Algebra k S]
    (a : fieldSpinRing k →ₐ[k] S) (t : FactorIndex → S) : Automorphisms S :=
  orbitWord false (fun i => t (.inl (i, false))) *
    (orbitWord true (fun i => t (.inr (i, false))) *
      frameInclusion S (framePointsOver k S a) *
      (orbitWord true (fun i => t (.inr (i, true))))⁻¹) *
    (orbitWord false (fun i => t (.inl (i, true))))⁻¹

private lemma map_auto_inv {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
    (g : Automorphisms S) (h : Automorphisms T)
    (hh : ∀ x, mapModel f (g.val x) = h.val (mapModel f x)) (x : Model S) :
    mapModel f ((g⁻¹).val x) = (h⁻¹).val (mapModel f x) := by
  change mapModel f (g.val.symm x) = h.val.symm (mapModel f x)
  apply h.val.injective
  rw [← hh, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private lemma factorPoint_natural {k S T : Type} [Field k] [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] (f : S →ₐ[k] T) (a : fieldSpinRing k →ₐ[k] S)
    (t : FactorIndex → S) (x : Model S) :
    mapModel f.toRingHom ((factorPoint a t).val x) =
      (factorPoint (f.comp a) (f ∘ t)).val (mapModel f.toRingHom x) := by
  simp only [factorPoint]
  change mapModel f.toRingHom ((orbitWord false (fun i => t (.inl (i, false)))).val
    ((orbitWord true (fun i => t (.inr (i, false)))).val
      ((framePointsOver k S a).val
        (((orbitWord true (fun i => t (.inr (i, true))))⁻¹).val
          (((orbitWord false (fun i => t (.inl (i, true))))⁻¹).val x))))) = _
  rw [orbitWord_natural, orbitWord_natural, framePointsOver_natural,
    map_auto_inv f.toRingHom _ _ (orbitWord_natural f.toRingHom true _),
    map_auto_inv f.toRingHom _ _ (orbitWord_natural f.toRingHom false _)]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def factorMap (P : IntegralPresentation) (k : Type) [Field k] :
    FiberRing P k →ₐ[k] FactorRing k :=
  (points P k (FactorRing k)).symm
    (factorPoint (IsScalarTower.toAlgHom k (fieldSpinRing k) _) X)

set_option backward.isDefEq.respectTransparency false in
private def factorEvaluation (k : Type) [Field k] (a : fieldSpinRing k →ₐ[k] k)
    (t : FactorIndex → k) : FactorRing k →ₐ[k] k where
  __ := MvPolynomial.eval₂Hom a.toRingHom t
  commutes' r := by
    change MvPolynomial.eval₂Hom a.toRingHom t (MvPolynomial.C (algebraMap k _ r)) = _
    rw [MvPolynomial.eval₂Hom_C]
    exact a.commutes r

set_option backward.isDefEq.respectTransparency false in
private lemma factorMap_eval (P : IntegralPresentation) (k : Type) [Field k]
    (a : fieldSpinRing k →ₐ[k] k) (t : FactorIndex → k) :
    points P k k ((factorEvaluation k a t).comp (factorMap P k)) = factorPoint a t := by
  have h₁ : (factorEvaluation k a t).comp
      (IsScalarTower.toAlgHom k (fieldSpinRing k) (FactorRing k)) = a := by
    apply AlgHom.ext
    intro x
    change MvPolynomial.eval₂Hom a.toRingHom t (C x) = a x
    exact MvPolynomial.eval₂Hom_C a.toRingHom t x
  have h₂ : (factorEvaluation k a t) ∘ (X : FactorIndex → FactorRing k) = t := by
    funext i
    change MvPolynomial.eval₂Hom a.toRingHom t (X i) = t i
    exact MvPolynomial.eval₂Hom_X' a.toRingHom t i
  have h := points_eq_of_natural P (S := FactorRing k) (T := k) (factorEvaluation k a t)
    (g := factorPoint (IsScalarTower.toAlgHom k (fieldSpinRing k) (FactorRing k)) X)
    (h := factorPoint a t) (by
      intro x
      rw [factorPoint_natural, h₁, h₂])
  exact (congrArg (points P k k) h).trans ((points P k k).apply_symm_apply _)

private lemma factorMap_covers_points (P : IntegralPresentation) (k : Type) [Field k]
    [IsAlgClosed k] (a : FiberRing P k →ₐ[k] k) :
    ∃ b : FactorRing k →ₐ[k] k, b.comp (factorMap P k) = a := by
  obtain ⟨s, t, h, _, hh, he⟩ := word_factorization k false (points P k k a) (by simp)
  obtain ⟨s', t', h', h₁, h₂, he'⟩ := word_factorization k true h (fun _ => hh)
  have hfix : FixesFrame h'.val := by
    have hz := h₁ rfl
    have h1 : h'.val (frameAxis 1) = frameAxis 1 := h₂
    have hp := (mem_splitAutomorphisms _).mp h'.property
    refine ⟨?_, hp.2⟩
    intro i
    fin_cases i
    · exact hz
    · exact h1
    · have hsum : (∑ j : Fin 3, (frameAxis j : Model k)) = CubicSpecification.cubicUnit :=
        (hermitian_frame (Composition.ZornSpecification.norm k)
          (LowerRankSpecification.untwisted k)).1
      rw [Fin.sum_univ_three] at hsum
      have h := congrArg h'.val hsum
      rw [hp.1, map_add, map_add, hz, h1] at h
      exact add_left_cancel (h.trans hsum.symm)
  let b₀ := (framePointsOver k k).symm ⟨h'.val, hfix⟩
  let u : FactorIndex → k := Sum.elim (fun i => if i.2 then t i.1 else s i.1)
    (fun i => if i.2 then t' i.1 else s' i.1)
  refine ⟨factorEvaluation k b₀ u, (points P k k).injective ?_⟩
  rw [factorMap_eval, he, he']
  have hb : frameInclusion k (framePointsOver k k b₀) = h' := by
    rw [show framePointsOver k k b₀ = ⟨h'.val, hfix⟩ from (framePointsOver k k).apply_symm_apply _]
    rfl
  simp [factorPoint, u, hb]

private lemma irreducible_of_parametrization {k A B : Type} [Field k] [IsAlgClosed k]
    [CommRing A] [CommRing B] [IsDomain B] [Algebra k A] [Algebra k B]
    [Algebra.FiniteType k A] (m : A →ₐ[k] B)
    (h : ∀ a : A →ₐ[k] k, ∃ b : B →ₐ[k] k, b.comp m = a) :
    IrreducibleSpace (PrimeSpectrum A) := by
  let f := PrimeSpectrum.comap m.toRingHom
  have hirr : IsIrreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum B)).image f
        (PrimeSpectrum.continuous_comap _).continuousOn
  have hclosed : closedPoints (PrimeSpectrum A) ⊆ Set.range f := by
    intro p hp
    obtain ⟨a, rfl⟩ := exists_rationalPoint (k := k) p (mem_closedPoints_iff.mp hp)
    obtain ⟨b, hb⟩ := h a
    exact ⟨primeOfHom b, (primeOfHom_comp m b).trans (congrArg primeOfHom hb)⟩
  letI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hdense : closure (Set.range f) = Set.univ :=
    Set.eq_univ_of_univ_subset ((closure_closedPoints (X := PrimeSpectrum A)) ▸
      closure_mono hclosed)
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (PrimeSpectrum A))
  rw [← hdense]
  exact hirr.closure

private lemma fiberIrreducible (P : IntegralPresentation) (k : Type) [Field k] [IsAlgClosed k] :
    IrreducibleSpace (fiberScheme P k) := by
  letI := spinFiber_domain k
  exact irreducible_of_parametrization (A := FiberRing P k) (B := FactorRing k)
    (factorMap P k) (factorMap_covers_points P k)

end Irreducibility

/-- The geometric fibers of the split Albert presentation are smooth and irreducible. -/
theorem geometricFiberGeometry : GeometricFiberGeometryType := by
  intro P e he hcharts k _ _
  obtain ⟨f, hf, hs⟩ := hcharts k
  exact ⟨fiberSmooth P e he k f hf hs, fiberIrreducible P k⟩

end
end LinearAlgebraicGroups.Albert.GeometricFiberGeometry
