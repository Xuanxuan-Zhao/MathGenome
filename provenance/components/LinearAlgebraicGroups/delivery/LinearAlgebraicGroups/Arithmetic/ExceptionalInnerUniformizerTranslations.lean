import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerUniformizerTranslations
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

import LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Opposite
open scoped CategoryTheory.MonObj TensorProduct WithZero

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalInnerUniformizerTranslations

open LinearAlgebraicGroups.Specs
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineBuilding
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalTwistedTraceComparison (PointCocycle Twist)
open Specs.IntegralSemisimpleModel (Model fibre integerAlgebra forgetFibrePoint)
open Specs.Pinning (BasedRootDatum)
open Specs.AutomorphismSequence (AdjointQuotient)

attribute [local instance] integerAlgebra

noncomputable section

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} {p : ℚ ⊗[ℤ] D.Y}
  {C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
    (ApartmentRoots.split D.datum ℚ) p}

/-- The coefficient operators with identity apartment part preserve the vertex labels. -/
theorem coefficient_types_eq_one {Γ : Type u} [Group Γ]
    {B : Building C} {ρ : Γ →* MulAut (FieldPoints M K)}
    (coef : CoefficientAction B ρ (fun _ => 1)) (σ : Γ) : coef.types σ = 1 := by
  apply Equiv.ext
  intro i
  change coef.types σ i = i
  let A := ApartmentRoots.split D.datum ℚ
  have h : A.wallHyperplane i.val = A.wallHyperplane (coef.types σ i).val := by
    simpa using coef.wall σ i
  by_contra hne
  have hz : A.wallValue (coef.types σ i).val (B.realization.vertex i) = 0 :=
    ((B.realization.vertex_marked i).2 _).mpr hne
  have hm : B.realization.vertex i ∈ A.wallHyperplane i.val := by
    rw [h]
    exact hz
  exact ((B.realization.vertex_marked i).2 i).mp hm rfl

/-- Formation of the twist and its vertex permutation at the given level. -/
theorem twist_with_type_change {Γ : Type u} [Group Γ] [Finite Γ]
    {B : Building C} {Q : C.TypeQuotient} (ad : AdjointAction B Q)
    (ρ : Γ →* MulAut (FieldPoints M K))
    (hρ : ∀ σ, AutomorphismComparison C (ρ σ) 1)
    (actions : AdjointCoefficientActions ad) (a : Γ → FieldPoints M K)
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) :
    ∃ (coef : CoefficientAction B ρ (fun _ => 1))
      (twist : Γ →* (B.realization.Point ≃ᵢ B.realization.Point)),
      (∀ σ g x, coef.action σ (ad.action g x) = ad.action (ρ σ g) (coef.action σ x)) ∧
      (∀ σ x, twist σ x = ad.action (a σ) (coef.action σ x)) ∧
      ∀ σ g t, ∃ h s, twist σ (B.realization.place g t) = B.realization.place h s ∧
        ∀ i, s.val (Q.wallPerm (typeChange Q (a σ)) i) = t.val i := by
  obtain ⟨coef, hc, ht⟩ := actions Γ ρ (fun _ => 1) hρ
  obtain ⟨twist, types, htw, htypes, hplace, _⟩ := ht a ha
  refine ⟨coef, twist, hc, htw, ?_⟩
  intro σ g t
  simpa only [htypes, coefficient_types_eq_one coef σ, mul_one] using hplace σ g t

section Coefficients

open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRing)
open Specs.IntegralSemisimpleModel (torusPoint TorusValues integralSpec)
open Specs.ExceptionalMarkedRootDescent (markedWeylWord)
open LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open private markedWeylWord_map from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private torusPoint_natural from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private rootOrderings_exist from LinearAlgebraicGroups.Classification.IntegralRealization

variable {F : Type u} [Field F] [Algebra F K] [FiniteDimensional F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeExtension F K]

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_torus_point (f : K →+* K) (t : TorusValues D (integralRing K)) :
    scalarPoints M f (torusPoint D (integralRing K) t ≫ M.torus.hom.hom) =
      torusPoint D (integralRing K) ((Units.map f.toMonoidHom).comp t) ≫ M.torus.hom.hom := by
  change integralSpec.map (integralRingMap f).op ≫
    torusPoint D (integralRing K) t ≫ M.torus.hom.hom = _
  rw [← Category.assoc]
  exact congrArg (· ≫ M.torus.hom.hom) (torusPoint_natural (integralRingMap f) t)

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_weyl_lift (σ : Gal(K/F)) (w : D.datum.weylGroup) :
    let N := C.localIwahori.normalizer
    scalarPoints M σ.toRingHom (N.lift w) = (N.lift w : FieldPoints M K) := by
  intro N
  have h : (N.lift w : FieldPoints M K) =
      markedWeylWord M.toIntegralMarking (integralRing K) (N.word w) := N.lift_point w
  rw [h]
  exact markedWeylWord_map M.toIntegralMarking (integralRingMap σ.toRingHom) (N.word w)

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_torus_mem (σ : Gal(K/F)) {t : FieldPoints M K}
    (ht : t ∈ C.localIwahori.normalizer.torus) :
    scalarPoints M σ.toRingHom t ∈ C.localIwahori.normalizer.torus := by
  let N := C.localIwahori.normalizer
  obtain ⟨v, hv⟩ := (N.torusPoints t).mp ht
  refine (N.torusPoints _).mpr ⟨(Units.map σ.toRingHom.toMonoidHom).comp v, ?_⟩
  change t = _ at hv
  change scalarPoints M σ.toRingHom t = _
  rw [hv, scalar_torus_point]

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_normalizer_data
    {B : Specs.ExceptionalMarkedRootDescent.MarkedFibre M K} {adj : Bool}
    (hC : SplitPointComparison B adj C) (hv : IsUnramifiedLocalExtension F K)
    (σ : Gal(K/F)) (n : C.N) :
    ∃ n' : C.N, (n' : FieldPoints M K) = scalarPoints M σ.toRingHom n ∧
      C.affine n' = C.affine n := by
  let N := C.localIwahori.normalizer
  let f := scalarPoints M σ.toRingHom
  let t := N.torusPart n
  let w := N.label n
  have ht := scalar_torus_mem (C := C) σ t.property
  let t' : N.torus := ⟨f t, ht⟩
  let n' : C.N := ⟨(t' : FieldPoints M K) * N.lift w, N.normalizer.mul_mem
    (N.torus_le t'.property) (N.lift w).property⟩
  have hprod : (t : FieldPoints M K) * N.lift w = n := by
    change ((n : FieldPoints M K) * (N.lift w : FieldPoints M K)⁻¹) * N.lift w = n
    exact inv_mul_cancel_right _ _
  have hn : (n' : FieldPoints M K) = f n := by
    change f t * (N.lift w : FieldPoints M K) = _
    rw [← scalar_weyl_lift (C := C) σ w]
    change f t * f (N.lift w) = _
    rw [← map_mul, hprod]
  have hlabel : N.label n' = w := by
    have hprod' : n' = (⟨t', N.torus_le t'.property⟩ : N.normalizer) * N.lift w := rfl
    rw [hprod', map_mul, (N.labelKernel _).mpr t'.property, one_mul, N.lift_label]
  have ht' : N.torusPart n' = t' := by
    apply Subtype.ext
    change (n' : FieldPoints M K) * (N.lift (N.label n') : FieldPoints M K)⁻¹ = t'
    rw [hlabel]
    exact mul_inv_cancel_right _ _
  have htrans : (N.translation t').toAdd = (N.translation t).toAdd := by
    obtain ⟨v, htv⟩ := (N.torusPoints t).mp t.property
    have htv' : identityPoints M K t' =
        torusPoint D (integralRing K) ((Units.map σ.toRingHom.toMonoidHom).comp v) ≫
          M.torus.hom.hom := by
      change f t = _
      change (t : FieldPoints M K) = _ at htv
      rw [htv]
      exact scalar_torus_point σ.toRingHom v
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext χ
    change D.datum.toLinearMap χ (N.translation t').toAdd =
      D.datum.toLinearMap χ (N.translation t).toAdd
    rw [N.characterLog t' _ htv', N.characterLog t _ htv]
    exact congrArg WithZero.log (normalizedValuation_unramifiedAut hv σ _)
  refine ⟨n', hn, AffineEquiv.ext fun x => ?_⟩
  rw [hC.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.1, hlabel, ht', htrans]

set_option backward.isDefEq.respectTransparency false in
private theorem map_of_preserved {G : Type*} [Group G] (a : MulAut G) (H : Subgroup G)
    (h : ∀ g ∈ H, a g ∈ H) (hinv : ∀ g ∈ H, a⁻¹ g ∈ H) :
    H.map a.toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact h g hg
  · intro g hg
    refine ⟨a⁻¹ g, hinv g hg, ?_⟩
    change a (a.symm g) = g
    exact a.apply_symm_apply g

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary coefficients act on any of the supplied split adjoint levels.
The marked words are fixed because their parameters are integral constants. -/
theorem scalar_adjoint_comparison
    {B : Specs.ExceptionalMarkedRootDescent.MarkedFibre M K}
    (hC : SplitPointComparison B true C) (br : C.Bruhat (Nat.card (residue K)))
    (Q : C.TypeQuotient) (hv : IsUnramifiedLocalExtension F K) (σ : Gal(K/F)) :
    AutomorphismComparison C (markedCoefficientAction M σ) 1 := by
  let a := markedCoefficientAction M σ
  let N := C.localIwahori.normalizer
  let _ := D.finiteRoots
  have hval := normalizedValuation_unramifiedAut hv σ
  obtain ⟨neg, pos, hn, hp⟩ := rootOrderings_exist D
  have hI := splitIwahoriScalar C.localIwahori C.localIwahori σ.toRingHom hval neg pos hn hp
  change C.I.comap a.toMonoidHom = C.I at hI
  have hI' : C.I.map a.toMonoidHom = C.I := by
    nth_rw 1 [← hI]
    exact Subgroup.map_comap_eq_self_of_surjective a.surjective _
  have hN (τ : Gal(K/F)) : ∀ g ∈ C.N, markedCoefficientAction M τ g ∈ C.N := by
    intro g hg
    obtain ⟨n', he, _⟩ := scalar_normalizer_data hC hv τ ⟨g, hg⟩
    change scalarPoints M τ.toRingHom g ∈ C.N
    exact he ▸ n'.property
  have hN' : C.N.map a.toMonoidHom = C.N :=
    map_of_preserved a C.N (hN σ) (by simpa only [map_inv] using hN σ⁻¹)
  have hT (τ : Gal(K/F)) : ∀ g ∈ N.torus, markedCoefficientAction M τ g ∈ N.torus :=
    fun _ h => scalar_torus_mem (C := C) τ h
  have hT' : N.torus.map a.toMonoidHom = N.torus :=
    map_of_preserved a N.torus (hT σ) (by simpa only [map_inv] using hT σ⁻¹)
  have hlabel (n n' : C.N) (he : (n' : FieldPoints M K) = a n) :
      C.affine n' = C.affine n := by
    obtain ⟨n'', he', h⟩ := scalar_normalizer_data hC hv σ n
    exact (congrArg C.affine (Subtype.ext (he.trans he'.symm))).trans h
  have hG : C.G₀.comap a.toMonoidHom = C.G₀ :=
    ordinarySubgroup_pullback C C a.toMonoidHom (le_of_eq hI.symm) (hN σ) hlabel Q.normal
      br.ordinary_normalizer br.ordinary_normalizer
  have hG' : C.G₀.map a.toMonoidHom = C.G₀ := by
    nth_rw 1 [← hG]
    exact Subgroup.map_comap_eq_self_of_surjective a.surjective _
  have hT₀ : C.T₀.map a.toMonoidHom = C.T₀ := by
    have hInt : C.I ⊓ C.N = C.T₀ := C.localIwahori.intersection
    rw [← hInt]
    exact (Subgroup.map_inf _ _ a.toMonoidHom a.injective).trans (congrArg₂ (· ⊓ ·) hI' hN')
  refine ⟨hI', hN', hT₀, hG', hT', by simp, ?_, ?_⟩
  · intro n n' h
    simpa only [one_mul, inv_one, mul_one] using hlabel n n' h
  · intro w
    refine ⟨w, by simp, ?_⟩
    let n' : C.N := ⟨a (C.lift w), hN σ _ (C.lift w).property⟩
    exact sameLabel_div_mem_unitTorus C (n := n') (m := C.lift w) (hlabel _ _ rfl)

end Coefficients

section Descent

open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalIwahoriImageComparison (integralPointHom)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRing)
open Specs.ExceptionalTwistedTraceComparison
open Specs.IntegralSemisimpleModel (integralSpec)
open Specs.RelativeFormComparison (fieldTest fieldMap)
open Specs.SteinbergPinnedDescent (coefficientAction comparisonOnPoints)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (pointMap)
open LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat (markedCoefficientAction)
open private forgetFibrePoint_mul forgetFibrePoint_comp
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private inner_conjugation adjoint_projection_surjective_over_closed_field
  adjoint_action_extends_points
  from LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison

open private mapPoints_injective from LinearAlgebraicGroups.Classification.RankOneRelations

variable {F : Type u} [Field F] [Algebra F K]

set_option backward.isDefEq.respectTransparency false in
/-- Transport on points through the marked fibre identification. -/
def markedPointHom {H : GroupScheme F} (i : H ≅ (fibre F).obj M.group) :
    GroupPoints H (CommAlgCat.of F K) →* FieldPoints M K where
  toFun x := forgetFibrePoint M.group (CommAlgCat.of F K) (x ≫ i.hom.hom.hom)
  map_mul' x y := by
    rw [MonObj.mul_comp, forgetFibrePoint_mul]
  map_one' := by
    rw [MonObj.one_comp]
    have h := forgetFibrePoint_mul M.group (CommAlgCat.of F K) 1 1
    rw [mul_one] at h
    exact mul_eq_left.mp h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem markedPointHom_coefficient {H : GroupScheme F}
    (i : H ≅ (fibre F).obj M.group) (σ : Gal(K/F))
    (x : GroupPoints H (CommAlgCat.of F K)) :
    markedPointHom i (coefficientAction K H σ x) = markedCoefficientAction M σ (markedPointHom i x) := by
  apply Over.OverMorphism.ext
  change ((fieldMap F K σ).left ≫ x.left) ≫ i.hom.hom.hom.left ≫ _ =
    (integralSpec.map (integralRingMap σ.toRingHom).op).left ≫
      x.left ≫ i.hom.hom.hom.left ≫ _
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem markedCocycle_mul {H : GroupScheme F} (i : H ≅ (fibre F).obj M.group)
    (a : PointCocycle (S := K) H) (σ τ : Gal(K/F)) :
    markedPointHom i (a.val (σ * τ)) =
      markedPointHom i (a.val σ) * markedCoefficientAction M σ (markedPointHom i (a.val τ)) := by
  have h := a.property.2 σ τ
  change a.val (σ * τ) = a.val σ * coefficientAction K H σ (a.val τ) at h
  rw [h, map_mul, markedPointHom_coefficient]

set_option backward.isDefEq.respectTransparency false in
private theorem project_adjointAction
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    (inn : InnerMap Q) (hinn : ActsByConjugation inn)
    (q : GroupPoints Q.quotient.val (CommAlgCat.of F K))
    (y : GroupPoints G.val (CommAlgCat.of F K)) :
    projectionOnPoints Q (adjointAction inn q y) =
      q * projectionOnPoints Q y * q⁻¹ := by
  let L := AlgebraicClosure K
  let a : CommAlgCat.of F K ⟶ CommAlgCat.of F L :=
    CommAlgCat.ofHom (IsScalarTower.toAlgHom F K L)
  let m := pointMap F K Q.quotient.val.X a.hom
  have hm : Function.Injective (fun x : GroupPoints Q.quotient.val (CommAlgCat.of F K) =>
      mapPoints a x) :=
    mapPoints_injective Q.quotient.property.1 a a.hom.injective
  apply hm
  have hp (x : GroupPoints G.val (CommAlgCat.of F K)) :
      mapPoints a (projectionOnPoints Q x) = projectionOnPoints Q (mapPoints a x) := by
    change (testSpec F).map a.op ≫ x ≫ Q.projection.hom.hom =
      ((testSpec F).map a.op ≫ x) ≫ Q.projection.hom.hom
    exact (Category.assoc _ _ _).symm
  obtain ⟨g, hg⟩ := adjoint_projection_surjective_over_closed_field Q (mapPoints a q)
  calc
    mapPoints a (projectionOnPoints Q (adjointAction inn q y)) =
        projectionOnPoints Q (adjointAction inn (mapPoints a q) (mapPoints a y)) := by
          rw [hp, adjoint_action_extends_points]
    _ = mapPoints a (q * projectionOnPoints Q y * q⁻¹) := by
      rw [← hg, inner_conjugation hinn, map_mul, map_mul, map_inv]
      change _ = m (q * projectionOnPoints Q y * q⁻¹)
      rw [map_mul, map_mul, map_inv]
      change _ = mapPoints a q * mapPoints a (projectionOnPoints Q y) * (mapPoints a q)⁻¹
      rw [hg, hp]

set_option backward.isDefEq.respectTransparency false in
private theorem markedPoint_projection {E : BasedRootDatum.{u}} {M' : Model E}
    (c : MarkedCentralCover M M') {G : AffineAlgebraicGroup F} (Q : AdjointQuotient G)
    (iG : G.val ≅ (fibre F).obj M.group) (iQ : Q.quotient.val ≅ (fibre F).obj M'.group)
    (h : Q.projection ≫ iQ.hom = iG.hom ≫ (fibre F).map c.map)
    (y : GroupPoints G.val (CommAlgCat.of F K)) :
    markedPointHom iQ (projectionOnPoints Q y) =
      integralPointHom c.map (integralRing K) (markedPointHom iG y) := by
  have h' : Q.projection.hom.hom ≫ iQ.hom.hom.hom =
      iG.hom.hom.hom ≫ ((fibre F).map c.map).hom.hom :=
    congrArg (fun f : G.val ⟶ (fibre F).obj M'.group => f.hom.hom) h
  change forgetFibrePoint M'.group (CommAlgCat.of F K)
    ((y ≫ Q.projection.hom.hom) ≫ iQ.hom.hom.hom) = _
  rw [Category.assoc, h', ← Category.assoc, forgetFibrePoint_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem fixed_adjoint_point {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    {a : PointCocycle (S := K) Q.quotient.val} (T : Twist a)
    (x : GroupPoints T.group.val (CommAlgCat.of F F)) (σ : Gal(K/F)) :
    let y := (comparisonOnPoints T.trivialization).symm (extendPoint x)
    a.val σ * coefficientAction K Q.quotient.val σ (projectionOnPoints Q y) * (a.val σ)⁻¹ =
      projectionOnPoints Q y := by
  intro y
  have he := congrArg (projectionOnPoints Q) (T.fixed x σ)
  rw [project_adjointAction _ T.onLift] at he
  have hcoe : projectionOnPoints Q (coefficientAction K G.val σ y) =
      coefficientAction K Q.quotient.val σ (projectionOnPoints Q y) :=
    by
      change (fieldMap F K σ ≫ y) ≫ Q.projection.hom.hom =
        fieldMap F K σ ≫ y ≫ Q.projection.hom.hom
      exact Category.assoc _ _ _
  rwa [hcoe] at he

/-- Every fixed adjoint point acts by isometries commuting with finite twisted descent. -/
theorem commute_twist_of_fixed {Γ : Type u} [Group Γ]
    {B : Building C} {Q : C.TypeQuotient} (ad : AdjointAction B Q)
    (ρ : Γ →* MulAut (FieldPoints M K))
    (coef : CoefficientAction B ρ (fun _ => 1))
    (tw : Γ →* (B.realization.Point ≃ᵢ B.realization.Point))
    (a : Γ → FieldPoints M K)
    (h : ∀ σ x, tw σ x = ad.action (a σ) (coef.action σ x))
    (hc : ∀ σ g x, coef.action σ (ad.action g x) = ad.action (ρ σ g) (coef.action σ x))
    (z : FieldPoints M K) (hz : ∀ σ, a σ * ρ σ z * (a σ)⁻¹ = z)
    (σ : Γ) (x : B.realization.Point) :
    ad.action z (tw σ x) = tw σ (ad.action z x) := by
  have hcomm : z * a σ = a σ * ρ σ z :=
    (congrArg (· * a σ) (hz σ).symm).trans (inv_mul_cancel_right _ _)
  rw [h, h, hc]
  change (ad.action z * ad.action (a σ)) (coef.action σ x) =
    (ad.action (a σ) * ad.action (ρ σ z)) (coef.action σ x)
  rw [← map_mul, ← map_mul, hcomm]

/-- The finite action on the specified adjoint building and its commutation
with points of the descended group after transport through the cover. -/
theorem finite_twist_and_rational_commutation
    [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeExtension F K]
    (hv : IsUnramifiedLocalExtension F K)
    {E : BasedRootDatum.{u}} {M' : Model E} (c : MarkedCentralCover M M')
    {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e} (B : SplitBuildingLevel Y)
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    (iG : G.val ≅ (fibre F).obj M.group) (iQ : Q.quotient.val ≅ (fibre F).obj M'.group)
    (h : Q.projection ≫ iQ.hom = iG.hom ≫ (fibre F).map c.map)
    {a : PointCocycle (S := K) Q.quotient.val} (T : Twist a) :
    let ρ := markedCoefficientAction (F := F) (K := K) M'
    let aK := fun σ => markedPointHom iQ (a.val σ)
    ∃ (coef : CoefficientAction B.ad ρ (fun _ => 1))
      (twist : Gal(K/F) →* (B.ad.realization.Point ≃ᵢ B.ad.realization.Point)),
      (∀ σ x, twist σ x = B.adjoint.action (aK σ) (coef.action σ x)) ∧
      (∀ σ g t, ∃ h s, twist σ (B.ad.realization.place g t) = B.ad.realization.place h s ∧
        ∀ i, s.val (Y.typeQuotient.wallPerm (typeChange Y.typeQuotient (aK σ)) i) = t.val i) ∧
      ∀ (x : GroupPoints T.group.val (CommAlgCat.of F F)) (σ : Gal(K/F)) (b : B.ad.realization.Point),
        let y := (comparisonOnPoints T.trivialization).symm (extendPoint x)
        let z := integralPointHom c.map (integralRing K) (markedPointHom iG y)
        B.adjoint.action z (twist σ b) = twist σ (B.adjoint.action z b) := by
  intro ρ aK
  letI : Finite Gal(K/F) := inferInstance
  have hρ (σ : Gal(K/F)) : AutomorphismComparison Y.ad (ρ σ) 1 :=
    scalar_adjoint_comparison Y.ad_points Y.ad_bruhat Y.typeQuotient hv σ
  obtain ⟨coef, tw, hc, htw, ht⟩ :=
    twist_with_type_change B.adjoint ρ hρ B.coefficients aK (markedCocycle_mul iQ a)
  refine ⟨coef, tw, htw, ht, ?_⟩
  intro x σ b y z
  apply commute_twist_of_fixed B.adjoint ρ coef tw aK htw hc z _ σ b
  intro τ
  have hz : z = markedPointHom iQ (projectionOnPoints Q y) :=
    (markedPoint_projection c Q iG iQ h y).symm
  rw [hz]
  have hf := congrArg (markedPointHom iQ) (fixed_adjoint_point T x τ)
  simpa only [map_mul, map_inv, markedPointHom_coefficient] using hf

open Specs.ExceptionalInnerUniformizerTranslations (uniformizerPoint)
open Specs.StandardGroups (multiplicativePowerGroup multiplicativePowerPoints)

private def uniformizerPowers {r : ℕ} (π : Fˣ) :
    Multiplicative (Fin r → ℤ) →* (ULift.{u} (Fin r) → Fˣ) where
  toFun z i := π ^ z.toAdd i.down
  map_one' := by funext i; exact zpow_zero π
  map_mul' z w := by funext i; exact zpow_add π (z.toAdd i.down) (w.toAdd i.down)

private def uniformizerHom {H : GroupScheme F} (S : ClosedSubgroup H) {r : ℕ}
    (s : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅ S.group)
    (points : (groupPointsFunctor F).obj (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅
      multiplicativePowerPoints F (ULift.{u} (Fin r)))
    (π : Fˣ) : Multiplicative (Fin r → ℤ) →* GroupPoints H (CommAlgCat.of F F) :=
  (((groupPointsFunctor F).map (s.hom ≫ S.inclusion)).app (CommAlgCat.of F F)).hom.comp
    ((points.inv.app (CommAlgCat.of F F)).hom.comp (uniformizerPowers π))

private theorem uniformizerHom_apply {H : GroupScheme F} (S : ClosedSubgroup H) {r : ℕ}
    (s : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅ S.group)
    (points : (groupPointsFunctor F).obj (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅
      multiplicativePowerPoints F (ULift.{u} (Fin r)))
    (π : Fˣ) (z : Fin r → ℤ) :
    uniformizerHom S s points π (Multiplicative.ofAdd z) = uniformizerPoint S s points π z :=
  by
    unfold uniformizerHom uniformizerPoint
    rfl

private def untwistedMarkedPointHom {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    {a : PointCocycle (S := K) Q.quotient.val} (T : Twist a)
    (iG : G.val ≅ (fibre F).obj M.group) :
    GroupPoints T.group.val (CommAlgCat.of F F) →* FieldPoints M K :=
  (markedPointHom iG).comp ((comparisonOnPoints T.trivialization).symm.toMonoidHom.comp
    (((groupPointsFunctor F).obj T.group.val).map
      (CommAlgCat.ofHom (Algebra.ofId F K))).hom)

end Descent

section Translations

open Specs.ExceptionalIwahoriImageComparison (integralPointHom integralUnitTorus)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.IntegralSemisimpleModel (torusPoint TorusValues)
open Specs.ExceptionalMarkedRootDescent (markedWeylWord)
open LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open scoped BigOperators

private theorem extend_integer_directions {V : Type u} [AddCommGroup V] [Module ℚ V]
    {r : ℕ} (d : (Fin r → ℤ) →+ V) (hd : Function.Injective d) (b : RealCoordinates V) :
    ∃ v : (Fin r → ℝ) →ₗ[ℝ] EuclideanApartment V, Function.Injective v ∧
      ∀ z : Fin r → ℤ, v (fun i => (z i : ℝ)) = rationalPoint b (d z) := by
  classical
  let w : Fin r → V := fun i => d (Pi.single i 1)
  have sum_directions (z : Fin r → ℤ) : (∑ i, z i • w i) = d z := by
    simp only [w, ← map_zsmul, ← map_sum]
    congr 1
    ext i
    simp [Pi.single_apply]
  have hi : LinearIndependent ℚ w := by
    apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
    rw [linearIndependent_iff_injective_fintypeLinearCombination]
    intro z z' h
    apply hd
    exact (sum_directions z).symm.trans (h.trans (sum_directions z'))
  let S : Set V := hi.linearIndepOn_id.extend (Set.subset_univ _)
  let basis : Module.Basis S ℚ V := .extend hi.linearIndepOn_id
  let idx (i : Fin r) : S := ⟨w i, hi.linearIndepOn_id.subset_extend _ ⟨i, rfl⟩⟩
  have hidx : Function.Injective idx := fun i j h => hi.injective (congrArg Subtype.val h)
  let wR (i : Fin r) := rationalPoint b (w i)
  have hreal : LinearIndependent ℝ wR := by
    have h := ((basis.baseChange ℝ).map b).linearIndependent.comp idx hidx
    convert h using 1
    funext i
    simp only [Function.comp_apply, Module.Basis.map_apply, Module.Basis.baseChange_apply]
    change b (1 ⊗ₜ[ℚ] w i) = b (1 ⊗ₜ[ℚ] Module.Basis.extend hi.linearIndepOn_id (idx i))
    rw [Module.Basis.extend_apply_self]
  refine ⟨Fintype.linearCombination ℝ wR,
    linearIndependent_iff_injective_fintypeLinearCombination.mp hreal, ?_⟩
  intro z
  change (∑ i, (z i : ℝ) • rationalPoint b (w i)) = rationalPoint b (d z)
  rw [← sum_directions z]
  unfold rationalPoint Specs.ExceptionalRealAlcove.rationalPoint
  rw [TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.cast_smul_eq_zsmul, ← map_zsmul]
  congr 1
  exact (map_zsmul (TensorProduct.mk ℚ ℝ V 1) (z i) (w i)).symm

private theorem realAffine_of_translation {V : Type u} [AddCommGroup V] [Module ℚ V]
    (b : RealCoordinates V) (f : V ≃ᵃ[ℚ] V) (d : V) (h : ∀ x, f x = x + d)
    (x : EuclideanApartment V) : realAffine b b f x = x + rationalPoint b d := by
  have h0 : f 0 = d := by simpa using h 0
  have hlin : f.linear.toLinearMap = LinearMap.id := by
    ext q
    change f.linear q = q
    have hf := f.map_vadd (0 : V) q
    change f (q + 0) = f.linear q + f 0 at hf
    rw [add_zero, h, h0] at hf
    exact add_right_cancel hf.symm
  change b (f.linear.toLinearMap.baseChange ℝ (b.symm x) + 1 ⊗ₜ[ℚ] f 0) = _
  rw [h0, hlin, LinearMap.baseChange_id, LinearMap.id_apply, map_add, b.apply_symm_apply]
  rfl

set_option maxHeartbeats 1000000 in
private theorem lattice_chart
    {E : BasedRootDatum.{u}} {M' : Model E} (c : MarkedCentralCover M M')
    {p' : ℚ ⊗[ℤ] E.Y} {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e} (B : SplitBuildingLevel Y)
    {r : ℕ} (q : Multiplicative (Fin r → ℤ) →* FieldPoints M K)
    (hq : ∀ z, q z ∈ Y.sc.localIwahori.normalizer.torus)
    (hk : ∀ z, q z ∈ Y.sc.T₀ → z = 1)
    (g : FieldPoints M K) :
    ∃ (h : Y.ad.G₀) (v : (Fin r → ℝ) →ₗ[ℝ] EuclideanApartment (ℚ ⊗[ℤ] E.Y)),
      Function.Injective v ∧
      ∀ (z : Fin r → ℤ) x,
        B.adjoint.action (integralPointHom c.map (integralRing K)
          (g * q (Multiplicative.ofAdd z) * g⁻¹)) (B.ad.realization.chart h x) =
        B.ad.realization.chart h (x + v (fun i => (z i : ℝ))) := by
  let φ := integralPointHom c.map (integralRing K)
  let N := Y.sc.localIwahori.normalizer
  let qN : Multiplicative (Fin r → ℤ) →* Y.sc.N :=
    q.codRestrict _ (fun z => N.torus_le (hq z))
  have htrans (z) : ∀ x, Y.sc.affine (qN z) x = x + Y.sc.affine (qN z) 0 := by
    have hlabel : N.label (qN z) = 1 := (N.labelKernel _).mpr (hq z)
    have ha := Y.sc_points.2.2.2.2.2.2.1
    intro x
    rw [ha, ha, hlabel]
    have hone : (↑(1 : D.datum.weylGroup) : D.datum.Aut).coweightEquiv =
        LinearEquiv.refl ℤ D.Y := by
      apply LinearEquiv.toLinearMap_injective
      change ((1 : D.datum.Aut).coweightEquiv : D.Y →ₗ[ℤ] D.Y) = LinearMap.id
      exact RootPairing.Equiv.coweightEquiv_one _
    rw [hone, LinearEquiv.refl_symm]
    change (LinearMap.id.baseChange ℚ) x + _ = x + ((LinearMap.id.baseChange ℚ) 0 + _)
    simp
  let qAd : Multiplicative (Fin r → ℤ) →* Y.ad.N :=
    (φ.comp q).codRestrict _ (fun z => by
      change q z ∈ Y.ad.N.comap φ
      rw [Y.central.2.2.2.1]
      exact (qN z).property)
  have hcompare (z) (x : ℚ ⊗[ℤ] D.Y) :
      e (Y.sc.affine (qN z) x) = Y.ad.affine (qAd z) (e x) :=
    Y.central.2.2.2.2.2.2.1 _ _ rfl x
  have had (z) (x : ℚ ⊗[ℤ] E.Y) :
      Y.ad.affine (qAd z) x = x + e (Y.sc.affine (qN z) 0) := by
    obtain ⟨w, rfl⟩ := e.surjective x
    rw [← hcompare, htrans, map_add]
  let d : (Fin r → ℤ) →+ (ℚ ⊗[ℤ] E.Y) :=
    { toFun := fun z => Y.ad.affine (qAd (Multiplicative.ofAdd z)) 0
      map_zero' := by change Y.ad.affine (qAd 1) 0 = _; rw [map_one, map_one]; rfl
      map_add' := by
        intro z w
        change Y.ad.affine (qAd (Multiplicative.ofAdd z * Multiplicative.ofAdd w)) 0 = _
        rw [map_mul, map_mul]
        change Y.ad.affine (qAd (Multiplicative.ofAdd z)) (Y.ad.affine (qAd (Multiplicative.ofAdd w)) 0) =
          Y.ad.affine (qAd (Multiplicative.ofAdd z)) 0 + Y.ad.affine (qAd (Multiplicative.ofAdd w)) 0
        rw [had, add_comm, had (Multiplicative.ofAdd z) 0, zero_add] }
  have hd : Function.Injective d := by
    apply (AddMonoidHom.ker_eq_bot_iff _).mp
    rw [AddSubgroup.eq_bot_iff_forall]
    intro z hz
    change Y.ad.affine (qAd (Multiplicative.ofAdd z)) 0 = 0 at hz
    have hs : Y.sc.affine (qN (Multiplicative.ofAdd z)) 0 = 0 := by
      apply e.injective
      have he := hcompare (Multiplicative.ofAdd z) 0
      rw [e.map_zero, hz] at he
      simpa only [map_zero] using he
    have hn : qN (Multiplicative.ofAdd z) ∈ Y.sc.affine.ker := by
      apply MonoidHom.mem_ker.mpr
      apply AffineEquiv.ext
      intro x
      rw [htrans, hs, add_zero]
      rfl
    have hm : q (Multiplicative.ofAdd z) ∈ Y.sc.T₀ := by
      change q (Multiplicative.ofAdd z) ∈
        (integralUnitTorus (K := K) M).comap (identityPoints M K)
      rw [← Y.sc.kernel]
      exact ⟨_, hn, rfl⟩
    exact congrArg Multiplicative.toAdd (hk _ hm)
  obtain ⟨v, hv, hdv⟩ := extend_integer_directions d hd B.ad.realization.coordinates
  have htop : Y.sc.G₀ = ⊤ := ordinaryRange_generates _
    Y.sc_points.2.2.2.2.2.2.2.2
  let h : Y.ad.G₀ := ⟨φ g, B.central.maps_group (show g ∈ Y.sc.G₀ by rw [htop]; trivial)⟩
  refine ⟨h, v, hv, ?_⟩
  intro z x
  have hh (x) : B.adjoint.action (φ g) (B.ad.realization.chart 1 x) =
      B.ad.realization.chart h x := by
    change B.adjoint.action (h : FieldPoints M' K) _ = _
    rw [B.adjoint.restrict, B.ad.realization.translate_chart, mul_one]
  have hq' : B.adjoint.action (φ (q (Multiplicative.ofAdd z))) (B.ad.realization.chart 1 x) =
      B.ad.realization.chart 1 (x + v (fun i => (z i : ℝ))) := by
    change B.adjoint.action ((qAd (Multiplicative.ofAdd z) : Y.ad.N) : FieldPoints M' K) _ = _
    rw [B.adjoint.chart_normalizer, hdv, realAffine_of_translation]
    intro y
    change _ = y + Y.ad.affine (qAd (Multiplicative.ofAdd z)) 0
    rw [had, had (Multiplicative.ofAdd z) 0, zero_add]
  rw [← hh x, ← hh, ← hq']
  change B.adjoint.action (φ (g * q (Multiplicative.ofAdd z) * g⁻¹)) _ = _
  simp only [map_mul, map_inv]
  change ((B.adjoint.action (φ g) * B.adjoint.action (φ (q (Multiplicative.ofAdd z))) *
      (B.adjoint.action (φ g))⁻¹) * B.adjoint.action (φ g)) (B.ad.realization.chart 1 x) =
    (B.adjoint.action (φ g) * B.adjoint.action (φ (q (Multiplicative.ofAdd z))))
      (B.ad.realization.chart 1 x)
  rw [inv_mul_cancel_right]

end Translations

section SplitTorusTransport

open CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalTwistedTraceComparison (extendPoint)
open Specs.GeometricRadicals (IsSplitTorus baseChangedSubgroup)
open Specs.IntegralSemisimpleModel (splitTorus)
open Specs.RelativeFormComparison (fieldTest)
open Specs.SteinbergPinnedDescent (comparisonOnPoints)
open Specs.StandardGroups (multiplicativePowerGroup)
open private relativeSectionGroupEquiv relativeSection_natural relativeSchemeIso relativeSchemeIso_natural
  from LinearAlgebraicGroups.Descent.AutomorphismSequence
open private fibreTowerIso from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private maximalSplitTorusAbove from LinearAlgebraicGroups.Relative.RelativeWeylScheme
open private splitGeometricallyMaximal from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private splitTorus_baseChange splitTorus_hom_descends from LinearAlgebraicGroups.Reductive.SplitToriConjugacy
open private fieldTorus_split from LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components
open private forgetFibrePoint_mul forgetFibrePoint_comp
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private forgetFibrePointEquiv from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

variable {F : Type u} [Field F] [Algebra F K]

private abbrev groundSections (H : GroupScheme K) := 𝟙_ (SchemeOver K) ⟶ H.X

private def baseSections (H : GroupScheme F) :
    groundSections ((groupBaseChange F K).obj H) ≃* GroupPoints H (CommAlgCat.of F K) :=
  relativeSectionGroupEquiv (Over.mk (𝟙 (fieldTest F K))) H

private theorem baseSections_conj (H : GroupScheme F)
    (x g y : groundSections ((groupBaseChange F K).obj H))
    (a b : GroupPoints H (CommAlgCat.of F K))
    (h : x = g * y * g⁻¹) (ha : baseSections H x = a) (hb : baseSections H y = b) :
    a = baseSections H g * b * (baseSections H g)⁻¹ := by
  rw [← ha, h, map_mul, map_mul, map_inv, hb]

private theorem baseSections_comp {H J : GroupScheme F} (f : H ⟶ J)
    (x : groundSections ((groupBaseChange F K).obj H)) :
    baseSections J (x ≫ ((groupBaseChange F K).map f).hom.hom) =
      baseSections H x ≫ f.hom.hom :=
  relativeSection_natural (Over.mk (𝟙 (fieldTest F K))) f.hom.hom x

private theorem baseSections_comparison {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    {a : PointCocycle (S := K) Q.quotient.val} (T : Twist a)
    (x : groundSections ((groupBaseChange F K).obj T.group.val)) :
    baseSections G.val (x ≫ (relativeSchemeIso T.trivialization.symm).hom.hom.hom) =
      (comparisonOnPoints T.trivialization).symm (baseSections T.group.val x) :=
  relativeSchemeIso_natural T.trivialization.symm (Over.mk (𝟙 (fieldTest F K))) x

private theorem baseChange_closed {H J : GroupScheme F} (f : H ⟶ J)
    (hf : IsClosedImmersion f.hom.hom.left) :
    IsClosedImmersion ((groupBaseChange F K).map f).hom.hom.left := by
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (baseChangeMapPullback (K := K) f.hom.hom).flip hf

private theorem project_conjugate_torus
    (R : TestAlgebra F) (b : GroupPoints ((fibre F).obj M.group) R)
    (x : GroupPoints ((fibre F).obj (splitTorus D)) R) :
    let y : GroupPoints ((fibre F).obj M.group) R := x ≫ ((fibre F).map M.torus).hom.hom
    forgetFibrePoint M.group R (b * y * b⁻¹) =
      forgetFibrePoint M.group R b *
        (forgetFibrePoint (splitTorus D) R x ≫ M.torus.hom.hom) *
        (forgetFibrePoint M.group R b)⁻¹ := by
  intro y
  let E := forgetFibrePointEquiv M.group R
  change E (b * y * b⁻¹) = E b * _ * (E b)⁻¹
  have h : E y = forgetFibrePoint (splitTorus D) R x ≫ M.torus.hom.hom :=
    forgetFibrePoint_comp M.torus R x
  exact (E.map_mul (b * y) b⁻¹).trans
    (congrArg₂ (· * ·) ((E.map_mul b y).trans (congrArg (E b * ·) h)) (E.map_inv b))

private theorem markedPointHom_conjugate_torus
    {H : GroupScheme F} (i : H ≅ (fibre F).obj M.group)
    (a : GroupPoints H (CommAlgCat.of F K))
    (b : GroupPoints ((fibre F).obj M.group) (CommAlgCat.of F K))
    (t : GroupPoints ((fibre F).obj (splitTorus D)) (CommAlgCat.of F K))
    (h : let y : GroupPoints ((fibre F).obj M.group) (CommAlgCat.of F K) :=
        t ≫ ((fibre F).map M.torus).hom.hom
      a ≫ i.hom.hom.hom = b * y * b⁻¹) :
    markedPointHom i a =
      forgetFibrePoint M.group (CommAlgCat.of F K) b *
        (forgetFibrePoint (splitTorus D) (CommAlgCat.of F K) t ≫ M.torus.hom.hom) *
        (forgetFibrePoint M.group (CommAlgCat.of F K) b)⁻¹ := by
  calc
    markedPointHom i a =
        forgetFibrePoint M.group (CommAlgCat.of F K) (a ≫ i.hom.hom.hom) := rfl
    _ = _ := (congrArg (forgetFibrePoint M.group (CommAlgCat.of F K)) h).trans
      (project_conjugate_torus (CommAlgCat.of F K) b t)

private theorem conjugation_from_sections
    {U H R : GroupScheme K} (i : U ≅ H) (a : groundSections H)
    (w : groundSections R) (j j' : R ⟶ H)
    (h : j'.hom.hom = (toUnit R.X ≫ a) * j.hom.hom * (toUnit R.X ≫ a)⁻¹)
    (x y : groundSections U)
    (hx : x ≫ i.hom.hom.hom = w ≫ j.hom.hom)
    (hy : y ≫ i.hom.hom.hom = w ≫ j'.hom.hom) :
    x = (a⁻¹ ≫ i.inv.hom.hom) * y * (a⁻¹ ≫ i.inv.hom.hom)⁻¹ := by
  let b : groundSections U := a⁻¹ ≫ i.inv.hom.hom
  have hb : b ≫ i.hom.hom.hom = a⁻¹ := by
    change (a⁻¹ ≫ i.inv.hom.hom) ≫ i.hom.hom.hom = a⁻¹
    rw [Category.assoc, ← Grp.comp_hom_hom, i.inv_hom_id]
    exact Category.comp_id _
  have hu : w ≫ toUnit R.X = 𝟙 (𝟙_ (SchemeOver K)) := Subsingleton.elim _ _
  have hw : w ≫ j'.hom.hom = a * (w ≫ j.hom.hom) * a⁻¹ := by
    rw [h, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hu,
      Category.id_comp]
  change x = b * y * b⁻¹
  apply (cancel_mono i.hom.hom.hom).mp
  rw [hx, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hb, inv_inv, hy, hw]
  group

private theorem conjugation_of_composites
    {A U H R : GroupScheme K} (i : U ≅ H) (a : groundSections H)
    (s : A ⟶ R) (j j' : R ⟶ H) (m n : A ⟶ U)
    (h : j'.hom.hom = (toUnit R.X ≫ a) * j.hom.hom * (toUnit R.X ≫ a)⁻¹)
    (hm : m ≫ i.hom = s ≫ j) (hn : n ≫ i.hom = s ≫ j')
    (x : groundSections A) :
    (x ≫ m.hom.hom) =
      (a⁻¹ ≫ i.inv.hom.hom) * (x ≫ n.hom.hom) * (a⁻¹ ≫ i.inv.hom.hom)⁻¹ := by
  refine conjugation_from_sections i a (x ≫ s.hom.hom) j j' h
    (x ≫ m.hom.hom) (x ≫ n.hom.hom) ?_ ?_
  · simpa only [Grp.comp_hom_hom, Category.assoc] using
      (congrArg (fun v : A ⟶ H => x ≫ v.hom.hom) hm)
  · simpa only [Grp.comp_hom_hom, Category.assoc] using
      (congrArg (fun v : A ⟶ H => x ≫ v.hom.hom) hn)

set_option backward.isDefEq.respectTransparency false in
private theorem conjugate_into_maximal_split_torus
    (G : AffineAlgebraicGroup K) (S T : ClosedSubgroup G.val)
    (hG : Specs.GeometricRadicals.IsReductive G) (hS : IsSplitTorus S.group)
    (hT : Specs.Relative.MaximalSplitTori.IsMaximalSplitTorus T) :
    ∃ (a : groundSections G.val) (j : S.group ⟶ T.group),
      IsClosedImmersion j.hom.hom.left ∧
      (j ≫ T.inclusion).hom.hom = (toUnit S.group.X ≫ a) *
        S.inclusion.hom.hom * (toUnit S.group.X ≫ a)⁻¹ := by
  obtain ⟨R, hR, j, hj⟩ := maximalSplitTorusAbove G S hS
  obtain ⟨a, e, he⟩ := LinearAlgebraicGroups.Relative.MaximalSplitTori.maximalSplitToriConjugate
    G hG R T hR hT
  have hc : IsClosedImmersion (j.hom.hom.left ≫ R.inclusion.hom.hom.left) := by
    change IsClosedImmersion (j ≫ R.inclusion).hom.hom.left
    rw [hj]
    exact S.isClosedImmersion
  haveI : IsClosedImmersion j.hom.hom.left := @IsClosedImmersion.of_comp_isClosedImmersion
    _ _ _ j.hom.hom.left R.inclusion.hom.hom.left R.isClosedImmersion hc
  let forget := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  letI : IsIso (forget.map e.hom) := forget.map_isIso _
  refine ⟨a, j ≫ e.hom, IsClosedImmersion.comp j.hom.hom.left (forget.map e.hom), ?_⟩
  have hu : j.hom.hom ≫ toUnit R.group.X = toUnit S.group.X := Subsingleton.elim _ _
  have h := congrArg (j.hom.hom ≫ ·) he
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hu] at h
  have h' : j.hom.hom ≫ R.inclusion.hom.hom = S.inclusion.hom.hom :=
    congrArg (fun f : S.group ⟶ G.val => f.hom.hom) hj
  rw [h'] at h
  simpa only [Grp.comp_hom_hom, Category.assoc] using h

private theorem closedImmersion_of_iso_composite
    {A B C D : GroupScheme K} (a : A ≅ B) (f : B ⟶ C) (b : C ≅ D)
    (hf : IsClosedImmersion f.hom.hom.left) :
    IsClosedImmersion (a.hom ≫ f ≫ b.hom).hom.hom.left := by
  let forget := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  haveI : IsIso (forget.map a.hom) := forget.map_isIso _
  haveI : IsIso (forget.map b.hom) := forget.map_isIso _
  letI : IsClosedImmersion (forget.map f) := hf
  change IsClosedImmersion (forget.map (a.hom ≫ f ≫ b.hom))
  rw [forget.map_comp, forget.map_comp]
  exact IsClosedImmersion.comp _ (forget.map f ≫ forget.map b.hom)

private theorem conjugate_with_marked_identifications
    {A H U V : GroupScheme F} (L : GroupScheme F ⥤ GroupScheme K)
    (S : ClosedSubgroup H) (s : A ≅ S.group) (j : V ⟶ U)
    (G : AffineAlgebraicGroup K) (P : ClosedSubgroup G.val)
    (i : L.obj U ≅ G.val) (t : L.obj V ≅ P.group) (f : L.obj H ≅ L.obj U)
    (hti : L.map j ≫ i.hom = t.hom ≫ P.inclusion)
    (hG : Specs.GeometricRadicals.IsReductive G)
    (hP : Specs.Relative.MaximalSplitTori.IsMaximalSplitTorus P)
    (hS : IsSplitTorus (L.obj S.group))
    (hc : IsClosedImmersion (L.map S.inclusion).hom.hom.left)
    (hdesc : ∀ k : L.obj A ⟶ L.obj V, ∃ τ : A ⟶ V, L.map τ = k) :
    ∃ (g : groundSections (L.obj U)) (τ : A ⟶ V),
      IsClosedImmersion (L.map τ).hom.hom.left ∧
      ∀ x : groundSections (L.obj A),
        x ≫ (L.map (s.hom ≫ S.inclusion) ≫ f.hom).hom.hom =
          g * (x ≫ (L.map τ ≫ L.map j).hom.hom) * g⁻¹ := by
  let forget := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  have hSf : IsClosedImmersion (L.map S.inclusion ≫ f.hom ≫ i.hom).hom.hom.left := by
    letI : IsClosedImmersion (forget.map (L.map S.inclusion)) := hc
    haveI : IsIso (forget.map f.hom) := forget.map_isIso _
    haveI : IsIso (forget.map i.hom) := forget.map_isIso _
    change IsClosedImmersion (forget.map (L.map S.inclusion ≫ f.hom ≫ i.hom))
    rw [forget.map_comp, forget.map_comp]
    exact IsClosedImmersion.comp _ (forget.map f.hom ≫ forget.map i.hom)
  let S' : ClosedSubgroup G.val := ⟨L.obj S.group, L.map S.inclusion ≫ f.hom ≫ i.hom, hSf⟩
  obtain ⟨a, jS, hjS, hd⟩ := conjugate_into_maximal_split_torus G S' P hG hS hP
  let sK : L.obj A ≅ S'.group := L.mapIso s
  obtain ⟨τ, hτ⟩ := hdesc (sK.hom ≫ jS ≫ t.inv)
  have hclosed : IsClosedImmersion (L.map τ).hom.hom.left := by
    rw [hτ]
    exact closedImmersion_of_iso_composite sK jS t.symm hjS
  refine ⟨a⁻¹ ≫ i.inv.hom.hom, τ, hclosed, ?_⟩
  have hm : (L.map (s.hom ≫ S.inclusion) ≫ f.hom) ≫ i.hom = sK.hom ≫ S'.inclusion := by
    change (L.map (s.hom ≫ S.inclusion) ≫ f.hom) ≫ i.hom =
      L.map s.hom ≫ L.map S.inclusion ≫ f.hom ≫ i.hom
    rw [L.map_comp, Category.assoc, Category.assoc]
  have hn : (L.map τ ≫ L.map j) ≫ i.hom = sK.hom ≫ (jS ≫ P.inclusion) := by
    rw [Category.assoc, hti, hτ]
    simp
  exact conjugation_of_composites i a sK.hom S'.inclusion (jS ≫ P.inclusion)
    (L.map (s.hom ≫ S.inclusion) ≫ f.hom) (L.map τ ≫ L.map j) hd hm hn

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
private theorem conjugate_after_base_change
    {H : GroupScheme F} (C : MarkedFibre M K) (S : ClosedSubgroup H) {r : ℕ}
    (s : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅ S.group)
    (f : (groupBaseChange F K).obj H ≅ (groupBaseChange F K).obj ((fibre F).obj M.group)) :
    let L := groupBaseChange F K
    let A := (multiplicativePowerGroup F (ULift.{u} (Fin r))).val
    let U := (fibre F).obj M.group
    let V := (fibre F).obj (splitTorus D)
    ∃ (g : groundSections (L.obj U)) (τ : A ⟶ V),
      IsClosedImmersion (L.map τ).hom.hom.left ∧
      ∀ x : groundSections (L.obj A),
        x ≫ (L.map (s.hom ≫ S.inclusion) ≫ f.hom).hom.hom =
          g * (x ≫ (L.map τ ≫ L.map ((fibre F).map M.torus)).hom.hom) * g⁻¹ := by
  intro L A U V
  let j : V ⟶ U := (fibre F).map M.torus
  let P := C.realization.pinned.pair
  let i : L.obj U ≅ P.G.val := ((fibreTowerIso F K).app M.group).symm ≪≫ C.groupIso
  let t : L.obj V ≅ P.T.group := ((fibreTowerIso F K).app (splitTorus D)).symm ≪≫ C.torusIso
  have hti : L.map j ≫ i.hom = t.hom ≫ P.T.inclusion := by
    as_aux_lemma =>
      change L.map j ≫ (fibreTowerIso F K).inv.app M.group ≫ C.groupIso.hom =
        ((fibreTowerIso F K).inv.app (splitTorus D) ≫ C.torusIso.hom) ≫ P.T.inclusion
      have hn : L.map j ≫ (fibreTowerIso F K).inv.app M.group =
          (fibreTowerIso F K).inv.app (splitTorus D) ≫ (fibre K).map M.torus :=
        (fibreTowerIso F K).inv.naturality M.torus
      rw [← Category.assoc, hn, Category.assoc, C.torus_comm, Category.assoc]
  have hS : IsSplitTorus (L.obj S.group) := splitTorus_baseChange (K := K) ⟨r, ⟨s.symm⟩⟩
  have hc : IsClosedImmersion (L.map S.inclusion).hom.hom.left :=
    baseChange_closed S.inclusion S.isClosedImmersion
  have hdesc (k : L.obj A ⟶ L.obj V) : ∃ τ : A ⟶ V, L.map τ = k :=
    splitTorus_hom_descends (K := K) (show IsSplitTorus A from ⟨r, ⟨Iso.refl _⟩⟩)
      (fieldTorus_split F D) k
  exact conjugate_with_marked_identifications L S s j P.G P.T i t f hti
    P.reductive (splitGeometricallyMaximal P.T P.split P.maximal) hS hc hdesc


set_option backward.isDefEq.respectTransparency false in
private theorem conjugate_split_torus_on_sections
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    {a : PointCocycle (S := K) Q.quotient.val} (T : Twist a)
    (iG : G.val ≅ (fibre F).obj M.group) (C : MarkedFibre M K)
    (S : ClosedSubgroup T.group.val) {r : ℕ}
    (s : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅ S.group) :
    ∃ (b : GroupPoints ((fibre F).obj M.group) (CommAlgCat.of F K))
      (τ : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ⟶ (fibre F).obj (splitTorus D)),
      IsClosedImmersion ((groupBaseChange F K).map τ).hom.hom.left ∧
      ∀ x : GroupPoints (multiplicativePowerGroup F (ULift.{u} (Fin r))).val (CommAlgCat.of F K),
        let y : GroupPoints ((fibre F).obj M.group) (CommAlgCat.of F K) :=
          (x ≫ τ.hom.hom) ≫ ((fibre F).map M.torus).hom.hom
        (comparisonOnPoints T.trivialization).symm
          (x ≫ s.hom.hom.hom ≫ S.inclusion.hom.hom) ≫ iG.hom.hom.hom = b * y * b⁻¹ := by
  let L := groupBaseChange F K
  let A := (multiplicativePowerGroup F (ULift.{u} (Fin r))).val
  let U := (fibre F).obj M.group
  let V := (fibre F).obj (splitTorus D)
  let j : V ⟶ U := (fibre F).map M.torus
  let f : L.obj T.group.val ≅ L.obj U :=
    relativeSchemeIso T.trivialization.symm ≪≫ L.mapIso iG
  obtain ⟨gK, τ, hτ, h⟩ := conjugate_after_base_change C S s f
  refine ⟨baseSections U gK, τ, hτ, ?_⟩
  intro x
  let xK := (baseSections A).symm x
  have hx : baseSections A xK = x := (baseSections A).apply_symm_apply x
  let y : groundSections (L.obj U) := xK ≫ (L.map (s.hom ≫ S.inclusion) ≫ f.hom).hom.hom
  have hy : baseSections U y =
      (comparisonOnPoints T.trivialization).symm (x ≫ s.hom.hom.hom ≫ S.inclusion.hom.hom) ≫
        iG.hom.hom.hom := by
    simp only [y, f, Iso.trans_hom, Functor.mapIso_hom, Grp.comp_hom_hom, ← Category.assoc]
    rw [baseSections_comp iG.hom, baseSections_comparison, baseSections_comp, hx]
    simp only [Grp.comp_hom_hom, Category.assoc]
  let z : groundSections (L.obj U) := xK ≫ (L.map τ ≫ L.map j).hom.hom
  have hyK : y = gK * z * gK⁻¹ := h xK
  intro yt
  have hbase : baseSections U (xK ≫ (L.map τ ≫ L.map j).hom.hom) = yt := by
    as_aux_lemma =>
      rw [Grp.comp_hom_hom, ← Category.assoc]
      rw [baseSections_comp, baseSections_comp, hx]
  let a' : GroupPoints U (CommAlgCat.of F K) :=
    (comparisonOnPoints T.trivialization).symm
      (x ≫ s.hom.hom.hom ≫ S.inclusion.hom.hom) ≫ iG.hom.hom.hom
  have h := baseSections_conj (F := F) (K := K) U y gK z a' yt hyK hy hbase
  exact h

private theorem conjugate_split_torus_to_marked
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    {a : PointCocycle (S := K) Q.quotient.val} (T : Twist a)
    (iG : G.val ≅ (fibre F).obj M.group) (C : MarkedFibre M K)
    (S : ClosedSubgroup T.group.val) {r : ℕ}
    (s : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅ S.group) :
    ∃ (g : FieldPoints M K)
      (τ : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ⟶ (fibre F).obj (splitTorus D)),
      IsClosedImmersion ((groupBaseChange F K).map τ).hom.hom.left ∧
      ∀ x : GroupPoints (multiplicativePowerGroup F (ULift.{u} (Fin r))).val (CommAlgCat.of F K),
        markedPointHom iG ((comparisonOnPoints T.trivialization).symm
          (x ≫ s.hom.hom.hom ≫ S.inclusion.hom.hom)) =
        g * (forgetFibrePoint (splitTorus D) (CommAlgCat.of F K) (x ≫ τ.hom.hom) ≫
          M.torus.hom.hom) * g⁻¹ := by
  obtain ⟨b, τ, hτ, h⟩ := conjugate_split_torus_on_sections T iG C S s
  refine ⟨forgetFibrePoint M.group (CommAlgCat.of F K) b, τ, hτ, ?_⟩
  intro x
  exact markedPointHom_conjugate_torus (M := M) iG
    ((comparisonOnPoints T.trivialization).symm (x ≫ s.hom.hom.hom ≫ S.inclusion.hom.hom))
    b (x ≫ τ.hom.hom) (h x)

end SplitTorusTransport

section TorusCoordinates

open CategoryTheory.Limits
open WithConv ValuativeRel
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalIwahoriImageComparison (integralPointHom integralUnitTorus)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open Specs.IntegralSemisimpleModel (IntegralPoints integralPointFunctor integralSpec
  splitTorus torusPoint TorusValues)
open Specs.StandardGroups (LaurentPowerCoordinates laurentVariable multiplicativePowerPoints
  multiplicativePowerGroup)
open Specs.DiagonalizableGroups (groupAlgebra)
open LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open private laurentPowerIso laurentPowerMulEquiv laurentPowerMulEquiv_eval
  exponentEvaluation spectrumPointsIso
  from LinearAlgebraicGroups.Affine.StandardGroups
open private schemeHopfHomEquiv from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private torusFibreIso torusFibre_monomial torusPoint_surjective
  from LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private forgetFibrePointEquiv
  from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private affineTorusPointEquiv torusPoint_natural
  from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private valuation_unit_iff from LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

variable {F : Type u} [Field F] [Algebra F K]

private def powerPoints (F : Type u) [Field F] (r : ℕ) :
    (groupPointsFunctor F).obj (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅
      multiplicativePowerPoints F (ULift.{u} (Fin r)) :=
  spectrumPointsIso (laurentPowerIso (k := F) («ι» := ULift.{u} (Fin r)))

private def powerEvaluation {r : ℕ} (π : Kˣ) (z : Fin r → ℤ) :
    LaurentPowerCoordinates F (ULift.{u} (Fin r)) →ₐ[F] K :=
  ((laurentPowerMulEquiv (k := F) («ι» := ULift.{u} (Fin r)) (CommAlgCat.of F K)).symm
    (fun i => π ^ z i.down)).ofConv

private theorem powerEvaluation_monomial {r : ℕ} (π : Kˣ) (z : Fin r → ℤ)
    (m : Multiplicative (ULift.{u} (Fin r) → ℤ)) :
    (powerEvaluation (F := F) π z) (AddMonoidAlgebra.of F _ m) =
      ((π ^ (∑ i, z i.down * m.toAdd i) : Kˣ) : K) := by
  classical
  unfold powerEvaluation laurentPowerMulEquiv
  change (AddMonoidAlgebra.lift F K _ _) _ = _
  rw [AddMonoidAlgebra.lift_of]
  change (↑(∏ i : ULift.{u} (Fin r), (π ^ z i.down) ^ m.toAdd i) : K) = _
  simp only [← zpow_mul]
  apply congrArg (fun a : Kˣ => (a : K))
  generalize (Finset.univ : Finset (ULift.{u} (Fin r))) = indices
  induction indices using Finset.induction_on with
  | empty => simp
  | insert i indices hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

private theorem powerPoint_of_evaluation {r : ℕ} (π : Kˣ) (z : Fin r → ℤ) :
    (powerPoints F r).inv.app (CommAlgCat.of F K) (fun i => π ^ z i.down) =
      (testSpec F).map (CommAlgCat.ofHom (powerEvaluation (F := F) π z)).op := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem torusPoint_powers {r : ℕ}
    (τ : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ⟶ (fibre F).obj (splitTorus D))
    (π : Kˣ) (z : Fin r → ℤ)
    (t : TorusValues D (integralRing K))
    (ht : forgetFibrePoint (splitTorus D) (CommAlgCat.of F K)
      ((powerPoints F r).inv.app (CommAlgCat.of F K) (fun i => π ^ z i.down) ≫ τ.hom.hom) =
        torusPoint D (integralRing K) t) :
    ∀ χ : Multiplicative D.X, ∃ n : ℤ, t χ = π ^ n := by
  intro χ
  let I := ULift.{u} (Fin r)
  let j := torusFibreIso (K := F) (Multiplicative D.X)
  let A := groupAlgebra F (Multiplicative D.X)
  let L := CommHopfAlgCat.of F (LaurentPowerCoordinates F I)
  let q := (schemeHopfHomEquiv A L).symm (τ ≫ j.hom)
  have hq : τ ≫ j.hom = (hopfSpec (CommRingCat.of F)).map q.op :=
    ((schemeHopfHomEquiv A L).apply_symm_apply _).symm
  have hg : IsGroupLikeElem F (q.hom (MonoidAlgebra.of F _ χ)) :=
    (MonoidAlgebra.isGroupLikeElem_single_one (R := F) (A := F) χ).map q.hom
  obtain ⟨m, hm⟩ := AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_of.mp hg
  refine ⟨∑ i, z i.down * m.toAdd i, Units.ext ?_⟩
  have hvalue := torusFibre_monomial D (CommAlgCat.of F K) _ t ht χ
  have he : ((powerPoints F r).inv.app (CommAlgCat.of F K) (fun i => π ^ z i.down) ≫
      τ.hom.hom) ≫ j.hom.hom.hom =
      (testSpec F).map (CommAlgCat.ofHom
        ((powerEvaluation (F := F) π z).comp q.hom.toAlgHom)).op := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hq, powerPoint_of_evaluation]
    change (testSpec F).map (CommAlgCat.ofHom (powerEvaluation (F := F) π z)).op ≫
      (testSpec F).map (CommAlgCat.ofHom q.hom.toAlgHom).op = _
    rw [← Functor.map_comp]
    rfl
  change ((algSpec.fullyFaithful (R := CommRingCat.of F)).preimage
    (((powerPoints F r).inv.app (CommAlgCat.of F K) (fun i => π ^ z i.down) ≫ τ.hom.hom) ≫
      j.hom.hom.hom)).unop.hom (MonoidAlgebra.of F _ χ) = (t χ : K) at hvalue
  rw [he, Functor.FullyFaithful.preimage_map] at hvalue
  change (powerEvaluation (F := F) π z) (q.hom (MonoidAlgebra.of F _ χ)) = (t χ : K) at hvalue
  rw [← hm, powerEvaluation_monomial] at hvalue
  exact hvalue.symm

set_option backward.isDefEq.respectTransparency false in
private theorem unitTorus_valuation (t : TorusValues D (integralRing K))
    (ht : (torusPoint D (integralRing K) t ≫ M.torus.hom.hom) ∈
      integralUnitTorus (K := K) M) :
    ∀ χ, normalizedValuation K (t χ : K) = 1 := by
  obtain ⟨s, hs⟩ := ht
  obtain ⟨a, rfl⟩ := torusPoint_surjective D _ s
  let m := valuationRingInclusion K
  change ((integralSpec.map m.op ≫ torusPoint D _ a) ≫ M.torus.hom.hom) =
      torusPoint D _ t ≫ M.torus.hom.hom at hs
  rw [torusPoint_natural] at hs
  letI : IsClosedImmersion M.torus.hom.hom.left := M.torusClosed
  have hsame : torusPoint D (integralRing K) ((Units.map m.hom.toMonoidHom).comp a) =
      torusPoint D (integralRing K) t := by
    apply Over.OverMorphism.ext
    have hl := congrArg Over.Hom.left hs
    exact (cancel_mono M.torus.hom.hom.left).mp hl
  have hta : (Units.map m.hom.toMonoidHom).comp a = t :=
    (affineTorusPointEquiv (k := IntegralSemisimpleModel.Integers.{u})
      (M := Multiplicative D.X) K).injective hsame
  intro χ
  rw [← hta, valuation_unit_iff]
  let v := valuation K
  let a' := v.valuationSubring.unitGroupMulEquiv.symm (a χ)
  have ha := (Valuation.mem_unitGroup_iff K v (a' : Kˣ)).mp a'.property
  change v (((v.valuationSubring.unitGroupMulEquiv.symm (a χ)) : Kˣ) : K) = 1 at ha
  rw [ValuationSubring.coe_unitGroupMulEquiv_symm_apply] at ha
  exact ha

private theorem power_eq_one_of_value_eq_one (π : Kˣ)
    (hπ : normalizedValuation K (π : K) = WithZero.exp (-1 : ℤ))
    (n : ℤ) (hn : normalizedValuation K ((π ^ n : Kˣ) : K) = 1) : n = 0 := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul,
    ← WithZero.exp_zero] at hn
  simpa using WithZero.exp_injective hn

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
private theorem uniformizerTorus_kernel {r : ℕ}
    (τ : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ⟶ (fibre F).obj (splitTorus D))
    (hτ : IsClosedImmersion ((groupBaseChange F K).map τ).hom.hom.left)
    (π : Kˣ) (hπ : normalizedValuation K (π : K) = WithZero.exp (-1 : ℤ))
    (z : Fin r → ℤ)
    (t : TorusValues D (integralRing K))
    (p₀ : GroupPoints (multiplicativePowerGroup F (ULift.{u} (Fin r))).val (CommAlgCat.of F K))
    (hp₀ : p₀ = (powerPoints F r).inv.app (CommAlgCat.of F K) (fun i => π ^ z i.down))
    (ht : forgetFibrePoint (splitTorus D) (CommAlgCat.of F K) (p₀ ≫ τ.hom.hom) =
        torusPoint D (integralRing K) t)
    (hu : (torusPoint D (integralRing K) t ≫ M.torus.hom.hom) ∈
      integralUnitTorus (K := K) M) :
    z = 0 := by
  have hts : ∀ χ, ∃ n : ℤ, t χ = π ^ n := torusPoint_powers τ π z t (hp₀ ▸ ht)
  have htv := unitTorus_valuation t hu
  have he : t = 1 := by
    apply MonoidHom.ext
    intro χ
    obtain ⟨n, hn⟩ := hts χ
    have hn0 := power_eq_one_of_value_eq_one π hπ n (hn ▸ htv χ)
    simp [hn, hn0]
  have h1 : p₀ ≫ τ.hom.hom = 1 := by
    let e := forgetFibrePointEquiv (splitTorus D) (CommAlgCat.of F K)
    apply e.injective
    change forgetFibrePoint (splitTorus D) (CommAlgCat.of F K) (p₀ ≫ τ.hom.hom) = e 1
    rw [ht, he, map_one]
    let ev : TorusValues D (integralRing K) ≃*
        IntegralPoints (splitTorus D) (integralRing K) :=
      affineTorusPointEquiv (k := IntegralSemisimpleModel.Integers.{u})
        (M := Multiplicative D.X) K
    have hsrc : (1 : TorusValues D (integralRing K)) * 1 = 1 := by
      apply MonoidHom.ext
      intro χ
      exact mul_one (1 : Kˣ)
    have hmul : ev 1 = ev 1 * ev 1 :=
      (congrArg ev hsrc).symm.trans (ev.map_mul 1 1)
    exact mul_eq_left.mp hmul.symm
  let A := (multiplicativePowerGroup F (ULift.{u} (Fin r))).val
  let f := (groupBaseChange F K).map τ
  have hp : (baseSections A).symm p₀ = 1 := by
    letI : IsClosedImmersion f.hom.hom.left := hτ
    apply Over.OverMorphism.ext
    apply (cancel_mono f.hom.hom.left).mp
    have hh : (baseSections A).symm p₀ ≫ f.hom.hom = 1 ≫ f.hom.hom := by
      apply (baseSections ((fibre F).obj (splitTorus D))).injective
      rw [baseSections_comp, baseSections_comp, MulEquiv.apply_symm_apply, map_one,
        MonObj.one_comp, h1]
    exact congrArg Over.Hom.left hh
  have hp' : p₀ = 1 := by
    simpa only [MulEquiv.apply_symm_apply, map_one] using congrArg (baseSections A) hp
  rw [hp₀] at hp'
  have hp'' := congrArg ((powerPoints F r).hom.app (CommAlgCat.of F K)) hp'
  change (powerPoints F r).hom.app (CommAlgCat.of F K)
    ((powerPoints F r).inv.app (CommAlgCat.of F K) (fun i => π ^ z i.down)) = _ at hp''
  have hh : (powerPoints F r).hom.app (CommAlgCat.of F K)
    ((powerPoints F r).inv.app (CommAlgCat.of F K) (fun i => π ^ z i.down)) =
      (fun i => π ^ z i.down) :=
    (((powerPoints F r).app (CommAlgCat.of F K)).groupIsoToMulEquiv).apply_symm_apply _
  rw [hh, map_one] at hp''
  funext i
  apply power_eq_one_of_value_eq_one π hπ
  have hv := congrFun hp'' (ULift.up i)
  rw [hv]
  exact map_one _

private def powerCoordinates (F : Type u) [Field F] (r : ℕ) :
    convolutionPoints (CommHopfAlgCat.of F (LaurentPowerCoordinates F (ULift.{u} (Fin r)))) ≅
      (groupPointsFunctor F).obj (multiplicativePowerGroup F (ULift.{u} (Fin r))).val :=
  hopfSpecPointIso (CommHopfAlgCat.of F (LaurentPowerCoordinates F (ULift.{u} (Fin r))))

private theorem powerCoordinates_spec (F : Type u) [Field F] (r : ℕ)
    (R : TestAlgebra F) (f : LaurentPowerCoordinates F (ULift.{u} (Fin r)) →ₐ[F] R) :
    ( (powerCoordinates F r).hom.app R (toConv f) :
        GroupPoints (multiplicativePowerGroup F (ULift.{u} (Fin r))).val R).left =
      Spec.map (CommRingCat.ofHom f.toRingHom) ∧
    ∀ i, (((powerPoints F r).hom.app R ((powerCoordinates F r).hom.app R (toConv f)) :
      ULift.{u} (Fin r) → Rˣ) i).val = f (laurentVariable F (ULift.{u} (Fin r)) i) := by
  refine ⟨rfl, ?_⟩
  have h : powerCoordinates F r ≪≫ powerPoints F r =
      laurentPowerIso (k := F) («ι» := ULift.{u} (Fin r)) := by
    unfold powerPoints spectrumPointsIso powerCoordinates
    exact Iso.self_symm_id_assoc _ _
  intro i
  change ((((powerCoordinates F r ≪≫ powerPoints F r).hom.app R (toConv f)) :
    ULift.{u} (Fin r) → Rˣ) i).val = _
  rw [h]
  exact laurentPowerMulEquiv_eval R f i

open Specs.ExceptionalTwistedTraceComparison (extendPoint)
open Specs.ExceptionalInnerUniformizerTranslations (uniformizerPoint)

private def extendedUniformizerPoint {r : ℕ} (π : Fˣ) :
    Multiplicative (Fin r → ℤ) →*
      GroupPoints (multiplicativePowerGroup F (ULift.{u} (Fin r))).val (CommAlgCat.of F K) :=
  (((groupPointsFunctor F).obj (multiplicativePowerGroup F (ULift.{u} (Fin r))).val).map
    (CommAlgCat.ofHom (Algebra.ofId F K))).hom.comp
    ((powerPoints F r).inv.app (CommAlgCat.of F F)).hom |>.comp (uniformizerPowers π)

private theorem extendedUniformizerPoint_apply {r : ℕ} (π : Fˣ) (z : Fin r → ℤ) :
    extendedUniformizerPoint (K := K) π (Multiplicative.ofAdd z) =
      (powerPoints F r).inv.app (CommAlgCat.of F K)
        (fun i => (Units.map (algebraMap F K).toMonoidHom π) ^ z i.down) := by
  let a : CommAlgCat.of F F ⟶ CommAlgCat.of F K := CommAlgCat.ofHom (Algebra.ofId F K)
  have h := ConcreteCategory.congr_hom ((powerPoints F r).inv.naturality a)
    (fun i : ULift.{u} (Fin r) => π ^ z i.down)
  change (powerPoints F r).inv.app (CommAlgCat.of F K)
    (fun i => Units.map (algebraMap F K).toMonoidHom (π ^ z i.down)) =
      extendedUniformizerPoint π (Multiplicative.ofAdd z) at h
  simpa only [map_zpow] using h.symm

private theorem extendedUniformizerPoint_in_torus {r : ℕ}
    {H : GroupScheme F} (S : ClosedSubgroup H)
    (s : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅ S.group)
    (π : Fˣ) (z : Fin r → ℤ) :
    extendPoint (uniformizerPoint S s (powerPoints F r) π z) =
      extendedUniformizerPoint (K := K) π (Multiplicative.ofAdd z) ≫ s.hom.hom.hom ≫
        S.inclusion.hom.hom :=
  (Category.assoc _ _ _).symm

end TorusCoordinates

section Assembly

open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralSemisimpleModel (splitTorus torusPoint)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalIwahoriImageComparison (integralPointHom integralUnitTorus)
open Specs.ExceptionalTwistedTraceComparison (extendPoint)
open Specs.ExceptionalInnerUniformizerTranslations (UniformizerTranslations uniformizerPoint)
open Specs.SteinbergPinnedDescent (comparisonOnPoints)
open LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat (markedCoefficientAction)
open private torusPoint_surjective from LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private forgetFibrePointEquiv from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
private theorem uniformizerTranslations_proof : UniformizerTranslations.{u} := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ hv D E M M' c p p' e Y B G Q iG iQ hc a T
  obtain ⟨coef, tw, htw, htypes, hcomm⟩ := finite_twist_and_rational_commutation hv c B iG iQ hc T
  refine ⟨markedCoefficientAction (F := F) (K := K) M', coef, tw, fun _ _ => rfl, htw,
    fun σ _ => htypes σ, ?_⟩
  intro S r s π hπ
  let points := powerPoints F r
  let coordinates := powerCoordinates F r
  let φ := integralPointHom c.map (integralRing K)
  let q₀ := (untwistedMarkedPointHom T iG).comp (uniformizerHom S s points π)
  let lattice := φ.comp q₀
  have hr (z : Fin r → ℤ) :
      q₀ (Multiplicative.ofAdd z) =
        markedPointHom iG ((comparisonOnPoints T.trivialization).symm
          (extendPoint (uniformizerPoint S s points π z))) := by
    change untwistedMarkedPointHom T iG (uniformizerHom S s points π (Multiplicative.ofAdd z)) = _
    rw [uniformizerHom_apply]
    rfl
  obtain ⟨g, τ, hτ, hconj⟩ := conjugate_split_torus_to_marked T iG Y.sc_fibre S s
  let qT := (forgetFibrePointEquiv (splitTorus D) (CommAlgCat.of F K)).toMonoidHom.comp
    ((((groupPointsFunctor F).map τ).app (CommAlgCat.of F K)).hom.comp
      (extendedUniformizerPoint (K := K) π))
  let q := (integralPointHom M.torus (integralRing K)).comp qT
  have hq (z) : q z ∈ Y.sc.localIwahori.normalizer.torus := by
    obtain ⟨t, ht⟩ := torusPoint_surjective D (integralRing K) (qT z)
    exact (Y.sc.localIwahori.normalizer.torusPoints _).mpr ⟨t,
      congrArg (· ≫ M.torus.hom.hom) ht.symm⟩
  let πK := Units.map (algebraMap F K).toMonoidHom π
  have hπK : normalizedValuation K (πK : K) = WithZero.exp (-1 : ℤ) :=
    (hv (π : F)).trans hπ
  have hk (z) (hz : q z ∈ Y.sc.T₀) : z = 1 := by
    as_aux_lemma =>
      obtain ⟨t, ht⟩ := torusPoint_surjective D (integralRing K) (qT z)
      have hu : (torusPoint D (integralRing K) t ≫ M.torus.hom.hom) ∈
          integralUnitTorus (K := K) M := by
        change q z ∈ integralUnitTorus (K := K) M at hz
        have hp : torusPoint D (integralRing K) t ≫ M.torus.hom.hom = q z :=
          congrArg (· ≫ M.torus.hom.hom) ht
        exact hp.symm ▸ hz
      apply Multiplicative.toAdd.injective
      exact uniformizerTorus_kernel τ hτ πK hπK z.toAdd t _
        (extendedUniformizerPoint_apply π z.toAdd) ht.symm hu
  obtain ⟨h, v, hv', hchart⟩ := lattice_chart c B q hq hk g
  refine ⟨points, coordinates, lattice, h, v, powerCoordinates_spec F r, ?_,
    hv', ?_, ?_⟩
  · intro z
    change φ (q₀ (Multiplicative.ofAdd z)) = _
    rw [hr]
    rfl
  · intro z σ x
    change B.adjoint.action (φ (q₀ (Multiplicative.ofAdd z.toAdd))) (tw σ x) =
      tw σ (B.adjoint.action (φ (q₀ (Multiplicative.ofAdd z.toAdd))) x)
    rw [hr]
    exact hcomm (uniformizerPoint S s points π z.toAdd) σ x
  · intro z x
    have hz : q₀ (Multiplicative.ofAdd z) = g * q (Multiplicative.ofAdd z) * g⁻¹ := by
      as_aux_lemma =>
        rw [hr, extendedUniformizerPoint_in_torus]
        exact hconj (extendedUniformizerPoint π (Multiplicative.ofAdd z))
    change B.adjoint.action (φ (q₀ (Multiplicative.ofAdd z))) (B.ad.realization.chart h x) = _
    rw [hz]
    exact hchart z x

end Assembly


/-- The finite twisted action and the uniformizer translations on the supplied building. -/
theorem uniformizerTranslations_conditional
    (_exceptionalAlcoveNormalForm :
      LinearAlgebraicGroups.Specs.ExceptionalStableAlcoves.ExceptionalAlcoveNormalForm.{u})
    (_integralScalingDenominator :
      LinearAlgebraicGroups.Specs.ExceptionalStableAlcoves.IntegralScalingDenominator.{u})
    (_stableIncidentAlcoves :
      LinearAlgebraicGroups.Specs.ExceptionalStableAlcoves.StableIncidentAlcoves.{u})
    : Specs.ExceptionalInnerUniformizerTranslations.UniformizerTranslations.{u} :=
  uniformizerTranslations_proof

end
end LinearAlgebraicGroups.Arithmetic.ExceptionalInnerUniformizerTranslations

universe v8_closure_1fc4736b178c3441_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalInnerUniformizerTranslations».«uniformizerTranslations» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalInnerUniformizerTranslations».«UniformizerTranslations».{v8_closure_1fc4736b178c3441_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalInnerUniformizerTranslations».«uniformizerTranslations_conditional».{v8_closure_1fc4736b178c3441_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalStableAlcoves».«exceptionalAlcoveNormalForm».{v8_closure_1fc4736b178c3441_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalStableAlcoves».«integralScalingDenominator».{v8_closure_1fc4736b178c3441_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalStableAlcoves».«stableIncidentAlcoves».{v8_closure_1fc4736b178c3441_u0})
