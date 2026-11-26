import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SplitFixedPoint
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.FieldTheory.RatFunc.IntermediateField

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

open LinearAlgebraicGroups.Specs (fppfOver projectSection)
open LinearAlgebraicGroups.Specs.SchemeDerivedGroup (RepresentsQuotient IsSplitSolvable)
open private locallySurjective_pair_ext closedSubgroupAlgebraic
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup

variable {k : Type u} [Field k]

private theorem whisker_eq_lift {H X Y : SchemeOver k} (f : X ⟶ Y) :
    H ◁ f = lift (fst H X) (snd H X ≫ f) := by
  rw [← Category.id_comp (H ◁ f), ← lift_fst_snd, lift_whiskerLeft]

private theorem fixed_iff_sections {H : GroupScheme k} {X T : SchemeOver k}
    [act : ModObj H.X X] (x : T ⟶ X) :
    IsFixedBy act.smul x ↔
      ∀ {U : SchemeOver k} (t : U ⟶ T) (h : U ⟶ H.X), h • (t ≫ x) = t ≫ x := by
  constructor
  · intro hx U t h
    simpa [IsFixedBy, Hom.smul_def, ← comp_lift, lift_whiskerLeft] using
      congrArg (lift h t ≫ ·) hx
  · intro hx
    simpa only [IsFixedBy, Hom.smul_def, whisker_eq_lift] using hx (snd H.X T) (fst H.X T)

@[instance_reducible]
private def actionOfSections {G : GroupScheme k} {Z : SchemeOver k}
    (a : G.X ⊗ Z ⟶ Z)
    (h₁ : ∀ (T : SchemeOver k) (z : T ⟶ Z), lift 1 z ≫ a = z)
    (h₂ : ∀ (T : SchemeOver k) (g h : T ⟶ G.X) (z : T ⟶ Z),
      lift (g * h) z ≫ a = lift g (lift h z ≫ a) ≫ a) : ModObj G.X Z where
  smul := a
  one_smul := by
    change (η[G.X] ▷ Z) ≫ a = (λ_ Z).hom
    have hl : lift (1 : Z ⟶ G.X) (𝟙 Z) = (λ_ Z).inv ≫ (η[G.X] ▷ Z) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc, whiskerRight_fst, leftUnitor_inv_fst_assoc, Hom.one_def]
      · rw [lift_snd, Category.assoc, whiskerRight_snd, leftUnitor_inv_snd]
    rw [← cancel_epi (λ_ Z).inv, ← Category.assoc, ← hl, Iso.inv_hom_id]
    exact h₁ Z (𝟙 Z)
  mul_smul := by
    change (μ[G.X] ▷ Z) ≫ a = (α_ G.X G.X Z).hom ≫ (G.X ◁ a) ≫ a
    let T := (G.X ⊗ G.X) ⊗ Z
    let g : T ⟶ G.X := fst (G.X ⊗ G.X) Z ≫ fst G.X G.X
    let h : T ⟶ G.X := fst (G.X ⊗ G.X) Z ≫ snd G.X G.X
    let z : T ⟶ Z := snd (G.X ⊗ G.X) Z
    have hl : lift (g * h) z = μ[G.X] ▷ Z := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, whiskerRight_fst, g, h, Hom.mul_def, ← comp_lift,
          lift_fst_snd, Category.comp_id]
      · rw [lift_snd, whiskerRight_snd]
    have hr : lift g (lift h z ≫ a) = (α_ G.X G.X Z).hom ≫ (G.X ◁ a) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, Category.assoc, whiskerLeft_fst, associator_hom_fst, g]
      · simp only [lift_snd, Category.assoc, whiskerLeft_snd]
        rw [← Category.assoc]
        congr 1
        apply CartesianMonoidalCategory.hom_ext
        · simp only [lift_fst, Category.assoc, associator_hom_snd_fst, h]
        · simp only [lift_snd, Category.assoc, associator_hom_snd_snd, z]
    rw [← hl, ← Category.assoc, ← hr]
    exact h₂ T g h z

private abbrev restrictAction {G H : GroupScheme k} {X : SchemeOver k}
    (i : H ⟶ G) [ModObj G.X X] : ModObj H.X X :=
  Mod.scalarRestriction i.hom.hom X

private theorem normal_stabilizes_fixed {G : GroupScheme k} (D : Specs.ClosedSubgroup G)
    (hn : Specs.IsNormalSubgroup D.inclusion) {X Z : SchemeOver k} [ModObj G.X X]
    (i : Z ⟶ X) (hi : RepresentsFixedPoints (restrictAction D.inclusion (X := X)).smul i) :
    ∃ a : G.X ⊗ Z ⟶ Z, a ≫ i = (G.X ◁ i) ≫ γ[G.X, X] := by
  let := restrictAction D.inclusion (X := X)
  apply (hi _ _).mp
  apply (fixed_iff_sections _).mpr
  intro U t h
  let g : U ⟶ G.X := t ≫ fst G.X Z
  let z : U ⟶ Z := t ≫ snd G.X Z
  have ht : t ≫ (G.X ◁ i) ≫ γ[G.X, X] = g • (z ≫ i) := by
    simp only [g, z, Hom.smul_def, ← comp_lift, whisker_eq_lift, Category.assoc]
  obtain ⟨c, hc⟩ := hn
  let d := lift g⁻¹ h ≫ c
  have hd : d ≫ D.inclusion.hom.hom = g⁻¹ * (h ≫ D.inclusion.hom.hom) * g := by
    rw [show d = lift g⁻¹ h ≫ c from rfl, Category.assoc, hc]
    simp only [Specs.subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv,
      lift_fst, lift_snd_assoc, inv_inv]
  have hfix : d • (z ≫ i) = z ≫ i :=
    (fixed_iff_sections i).mp ((hi _ _).mpr ⟨𝟙 Z, Category.id_comp _⟩) z d
  have hres (v : U ⟶ D.group.X) (w : U ⟶ X) :
      v • w = (v ≫ D.inclusion.hom.hom) • w := by
    change lift v w ≫ ((D.inclusion.hom.hom ▷ X) ≫ γ[G.X, X]) = _
    rw [← Category.assoc, lift_whiskerRight]
    rfl
  rw [hres, hd] at hfix
  rw [ht, hres, ← mul_smul]
  have hg : g * (g⁻¹ * (h ≫ D.inclusion.hom.hom) * g) =
      (h ≫ D.inclusion.hom.hom) * g := by group
  rw [← hg, mul_smul, hfix]

private theorem induced_fixed_action {G : GroupScheme k} (D : Specs.ClosedSubgroup G)
    (hn : Specs.IsNormalSubgroup D.inclusion) {X Z : SchemeOver k} [ModObj G.X X]
    (i : Z ⟶ X) [Mono i]
    (hi : RepresentsFixedPoints (restrictAction D.inclusion (X := X)).smul i) :
    ∃ act : ModObj G.X Z,
      (∀ {T : SchemeOver k} (g : T ⟶ G.X) (z : T ⟶ Z),
        lift g z ≫ act.smul ≫ i = g • (z ≫ i)) ∧
      (∀ {T : SchemeOver k} (h : T ⟶ D.group.X) (z : T ⟶ Z),
        lift (h ≫ D.inclusion.hom.hom) z ≫ act.smul = z) := by
  obtain ⟨a, ha⟩ := normal_stabilizes_fixed D hn i hi
  have he {T : SchemeOver k} (g : T ⟶ G.X) (z : T ⟶ Z) :
      (lift g z ≫ a) ≫ i = g • (z ≫ i) := by
    simp only [ha, Category.assoc, Hom.smul_def, lift_whiskerLeft_assoc]
  refine ⟨actionOfSections a ?_ ?_, ?_, ?_⟩
  · intro T z
    apply (cancel_mono i).mp
    rw [he, one_smul]
  · intro T g h z
    apply (cancel_mono i).mp
    rw [he, he, he, mul_smul]
  · intro T g z
    change lift g z ≫ a ≫ i = _
    simpa only [Category.assoc] using he g z
  · intro T h z
    change lift (h ≫ D.inclusion.hom.hom) z ≫ a = z
    apply (cancel_mono i).mp
    rw [he]
    let := restrictAction D.inclusion (X := X)
    have hf := (fixed_iff_sections i).mp
      ((hi Z i).mpr ⟨𝟙 Z, Category.id_comp _⟩) z h
    change lift h (z ≫ i) ≫ ((D.inclusion.hom.hom ▷ X) ≫ γ[G.X, X]) = _ at hf
    rwa [← Category.assoc, lift_whiskerRight] at hf

private theorem quotient_section_eq {G Q : GroupScheme k} (D : Specs.ClosedSubgroup G)
    (q : G ⟶ Q) (hq : RepresentsQuotient D q) {T : SchemeOver k} (g g' : T ⟶ G.X)
    (he : g ≫ q.hom.hom = g' ≫ q.hom.hom) :
    ∃ h : T ⟶ D.group.X, h ≫ D.inclusion.hom.hom = g⁻¹ * g' := by
  obtain ⟨e, eq⟩ := hq
  apply (rightQuotientProjectionEquality D g g').mp
  have hh : ∀ a : T ⟶ G.X,
      e.hom.hom.app (op T) (projectSection D a) = ULift.up (a ≫ q.hom.hom) := by
    intro a
    exact congrArg (fun f => f.hom.app (op T) (ULift.up a)) eq
  apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (op T))).1
  rw [hh, hh, he]

private theorem quotient_locally_surjective {G Q : GroupScheme k} (D : Specs.ClosedSubgroup G)
    (q : G ⟶ Q) (hq : RepresentsQuotient D q) :
    Presheaf.IsLocallySurjective (fppfOver k)
      ((fppfOver k).uliftYoneda.{u + 1}.map q.hom.hom).hom := by
  obtain ⟨e, he⟩ := hq
  rw [← he]
  have := rightQuotientLocalLifts D
  infer_instance

private theorem descend_action {G Q : GroupScheme k} (D : Specs.ClosedSubgroup G)
    (q : G ⟶ Q) (hq : RepresentsQuotient D q) {Z : SchemeOver k}
    [act : ModObj G.X Z] (hk : ∀ {T : SchemeOver k}
      (h : T ⟶ D.group.X) (z : T ⟶ Z), (h ≫ D.inclusion.hom.hom) • z = z) :
    ∃ b : ModObj Q.X Z, ∀ {T : SchemeOver k} (g : T ⟶ G.X) (z : T ⟶ Z),
      lift (g ≫ q.hom.hom) z ≫ b.smul = g • z := by
  classical
  let J := fppfOver k
  let P := J.yoneda.obj Z
  let φ := (J.uliftYoneda.{u + 1}.map q.hom.hom).hom
  have hl := quotient_locally_surjective D q hq
  have equal_lifts {U : SchemeOver k} (g g' : U ⟶ G.X) (z : U ⟶ Z)
      (he : g ≫ q.hom.hom = g' ≫ q.hom.hom) : g • z = g' • z := by
    obtain ⟨h, hh⟩ := quotient_section_eq D q hq g g' he
    have he' : g * (h ≫ D.inclusion.hom.hom) = g' := by rw [hh]; group
    rw [← he', mul_smul, hk]
  have amalgamate {T : SchemeOver k} (v : T ⟶ Q.X) (z : T ⟶ Z) :
      ∃ w : T ⟶ Z, ∀ {U : SchemeOver k} (f : U ⟶ T) (g : U ⟶ G.X),
        g ≫ q.hom.hom = f ≫ v → f ≫ w = g • (f ≫ z) := by
    let S := Presheaf.imageSieve φ (ULift.up v)
    have hS : S ∈ J T := hl.imageSieve_mem _
    have localLift {U : SchemeOver k} (f : U ⟶ T) (hf : S f) :
        ∃ g : U ⟶ G.X, g ≫ q.hom.hom = f ≫ v := by
      obtain ⟨⟨g⟩, hg⟩ := hf
      exact ⟨g, congrArg ULift.down hg⟩
    let g {U : SchemeOver k} (f : U ⟶ T) (hf : S f) := (localLift f hf).choose
    have hg {U : SchemeOver k} (f : U ⟶ T) (hf : S f) :
        g f hf ≫ q.hom.hom = f ≫ v := (localLift f hf).choose_spec
    let family : Presieve.FamilyOfElements P.obj S.arrows := fun _ f hf ↦ g f hf • (f ≫ z)
    have hcompat : family.Compatible := by
      intro U₁ U₂ V f₁ f₂ a₁ a₂ ha₁ ha₂ e
      change f₁ ≫ (g a₁ ha₁ • (a₁ ≫ z)) = f₂ ≫ (g a₂ ha₂ • (a₂ ≫ z))
      simp only [ModObj.comp_smul, ← Category.assoc, e]
      apply equal_lifts
      rw [Category.assoc, Category.assoc, hg a₁ ha₁, hg a₂ ha₂,
        ← Category.assoc, ← Category.assoc, e]
    obtain ⟨w, hw, _⟩ := (P.property.isSheafFor S hS) family hcompat
    refine ⟨w, ?_⟩
    intro U f g' hg'
    have hf : S f := ⟨ULift.up g', congrArg ULift.up hg'⟩
    calc
      f ≫ w = g f hf • (f ≫ z) := hw f hf
      _ = g' • (f ≫ z) := equal_lifts _ _ _ ((hg f hf).trans hg'.symm)
  obtain ⟨a, ha⟩ := amalgamate (fst Q.X Z) (snd Q.X Z)
  have he {T : SchemeOver k} (g : T ⟶ G.X) (z : T ⟶ Z) :
      lift (g ≫ q.hom.hom) z ≫ a = g • z := by
    simpa only [lift_fst, lift_snd] using ha (lift (g ≫ q.hom.hom) z) g (by simp)
  refine ⟨actionOfSections a ?_ ?_, he⟩
  · intro T z
    let F := ((yonedaGrp.map q).app (op T)).hom
    have h : (1 : T ⟶ G.X) ≫ q.hom.hom = 1 := F.map_one
    simpa only [h, one_smul] using he (1 : T ⟶ G.X) z
  · intro T g h z
    apply locallySurjective_pair_ext q hl g h
    intro U f g' h' hg hh
    simp only [← Category.assoc, comp_lift, MonObj.comp_mul]
    rw [← hg, ← hh]
    let F := ((yonedaGrp.map q).app (op U)).hom
    have hm : (g' * h') ≫ q.hom.hom = (g' ≫ q.hom.hom) * (h' ≫ q.hom.hom) :=
      F.map_mul _ _
    rw [← hm, he, he, he, mul_smul]


section BoundaryRing

variable (k : Type u) [Field k]

private abbrev zeroIdeal : Ideal (Polynomial k) := RingHom.ker Polynomial.constantCoeff
private instance : (zeroIdeal k).IsPrime := RingHom.ker_isPrime _
private abbrev BoundaryRing := Localization.AtPrime (zeroIdeal k)
private abbrev BoundaryField := FractionRing (Polynomial k)

private theorem zeroIdeal_ne_bot : zeroIdeal k ≠ ⊥ := by
  intro h
  have hx : (Polynomial.X : Polynomial k) ∈ zeroIdeal k := by simp [zeroIdeal]
  rw [h, Ideal.mem_bot] at hx
  exact Polynomial.X_ne_zero hx

private instance : IsDiscreteValuationRing (BoundaryRing k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ (zeroIdeal_ne_bot k) _

private abbrev parameter : BoundaryRing k := algebraMap (Polynomial k) _ Polynomial.X

private theorem parameter_ne_zero : parameter k ≠ 0 :=
  fun h => Polynomial.X_ne_zero <| (IsLocalization.injective (BoundaryRing k)
    (zeroIdeal k).primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm)

private def specialize : BoundaryRing k →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := (zeroIdeal k).primeCompl)
    (f := { toRingHom := Polynomial.constantCoeff
            commutes' := fun _ => Polynomial.coeff_C_zero }) fun x =>
      isUnit_iff_ne_zero.mpr (show Polynomial.constantCoeff x.val ≠ 0 from x.prop)

private theorem specialize_poly (p : Polynomial k) :
    specialize k (algebraMap (Polynomial k) (BoundaryRing k) p) = Polynomial.constantCoeff p := by
  simp [specialize]

private theorem specialize_parameter : specialize k (parameter k) = 0 := by
  rw [specialize_poly]
  simp

private theorem specialize_unit {r : BoundaryRing k} (hr : specialize k r ≠ 0) :
    IsUnit r := by
  have hk : RingHom.ker (specialize k).toRingHom = IsLocalRing.maximalIdeal (BoundaryRing k) :=
    IsLocalRing.ker_eq_maximalIdeal _ (fun y => ⟨algebraMap k _ y, (specialize k).commutes y⟩)
  apply IsLocalRing.notMem_maximalIdeal.mp
  rwa [← hk, RingHom.mem_ker]

private def includeBoundary : BoundaryRing k →ₐ[k] BoundaryField k :=
  { toRingHom := algebraMap (BoundaryRing k) (BoundaryField k)
    commutes' := fun c => by
      change algebraMap (BoundaryRing k) (BoundaryField k) (algebraMap k (BoundaryRing k) c) = _
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (BoundaryRing k),
        ← IsScalarTower.algebraMap_apply (Polynomial k) (BoundaryRing k) (BoundaryField k),
        ← IsScalarTower.algebraMap_apply k (Polynomial k) (BoundaryField k)] }

private theorem boundary_transcendental {r : BoundaryRing k} (hr : r ≠ 0)
    (hz : specialize k r = 0) : Transcendental k (includeBoundary k r) := by
  let e := RatFunc.toFractionRingAlgEquiv k k
  have h := RatFunc.transcendental_of_ne_C (f := e.symm (includeBoundary k r)) (by
    rintro ⟨c, hc⟩
    have hc' : includeBoundary k r = algebraMap k (BoundaryField k) c := by
      have he := congrArg e hc
      change e (e.symm (includeBoundary k r)) = e (algebraMap k (RatFunc k) c) at he
      rwa [e.apply_symm_apply, e.commutes] at he
    have hf : r = algebraMap k (BoundaryRing k) c :=
      (IsFractionRing.injective (BoundaryRing k) (BoundaryField k)) (hc'.trans
        ((includeBoundary k).commutes c).symm)
    rw [hf, (specialize k).commutes, Algebra.algebraMap_self_apply] at hz
    exact hr (by rw [hf, hz, map_zero]))
  apply (transcendental_iff_injective).2
  have hi := (transcendental_iff_injective).1 h
  have he : e.symm.toAlgHom.comp (Polynomial.aeval (includeBoundary k r)) =
      Polynomial.aeval (e.symm (includeBoundary k r)) := Polynomial.algHom_ext (by simp)
  intro p q hpq
  apply hi
  rw [← he]
  exact congrArg e.symm hpq

variable {k} {K : Type u} [Field K] [Algebra k K]

private def boundaryMap (r : BoundaryRing K) (hr : specialize K r = 0) :
    BoundaryRing k →ₐ[k] BoundaryRing K :=
  IsLocalization.liftAlgHom (M := (zeroIdeal k).primeCompl)
    (f := Polynomial.aeval r) fun p => by
    apply specialize_unit K
    have he : ((specialize K).restrictScalars k).comp (Polynomial.aeval r) =
        (Algebra.ofId k K).comp (Polynomial.aeval 0) := by
      apply Polynomial.algHom_ext
      simp [hr]
    change (((specialize K).restrictScalars k).comp (Polynomial.aeval r)) p ≠ 0
    rw [he]
    change algebraMap k K (Polynomial.aeval 0 (p : Polynomial k)) ≠ 0
    rw [← Polynomial.coeff_zero_eq_aeval_zero]
    simpa only [map_zero, Polynomial.constantCoeff_apply] using (algebraMap k K).injective.ne
      (show Polynomial.constantCoeff p.val ≠ 0 from p.prop)

private theorem boundaryMap_poly {r : BoundaryRing K} (hr : specialize K r = 0)
    (p : Polynomial k) :
    boundaryMap (k := k) r hr (algebraMap (Polynomial k) (BoundaryRing k) p) =
      Polynomial.aeval r p := by
  simp [boundaryMap]

private theorem boundaryMap_parameter {r : BoundaryRing K} (hr : specialize K r = 0) :
    boundaryMap (k := k) r hr (parameter k) = r := by
  rw [boundaryMap_poly, Polynomial.aeval_X]

private theorem boundaryMap_specialize {r : BoundaryRing K} (hr : specialize K r = 0) :
    ((specialize K).restrictScalars k).comp (boundaryMap (k := k) r hr) =
      (Algebra.ofId k K).comp (specialize k) := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (zeroIdeal k).primeCompl
  have h :
      ((specialize K).restrictScalars k).comp
        ((boundaryMap (k := k) r hr).comp (IsScalarTower.toAlgHom k (Polynomial k) (BoundaryRing k))) =
      (Algebra.ofId k K).comp ((specialize k).comp
        (IsScalarTower.toAlgHom k (Polynomial k) (BoundaryRing k))) := by
    apply Polynomial.algHom_ext
    change specialize K (boundaryMap (k := k) r hr (parameter k)) =
      algebraMap k K (specialize k (parameter k))
    rw [boundaryMap_parameter, hr, specialize_parameter, map_zero]
  exact congrArg AlgHom.toRingHom h

private def fractionMap (r : BoundaryRing K) (hn : r ≠ 0) (hr : specialize K r = 0) :
    BoundaryField k →ₐ[k] BoundaryField K :=
  IsFractionRing.liftAlgHom (g := Polynomial.aeval (includeBoundary K r))
    (transcendental_iff_injective.mp
      ((boundary_transcendental K hn hr).restrictScalars (algebraMap k K).injective))

private theorem fractionMap_X {r : BoundaryRing K} (hn : r ≠ 0) (hr : specialize K r = 0) :
    fractionMap (k := k) r hn hr (algebraMap (Polynomial k) (BoundaryField k) Polynomial.X) =
      includeBoundary K r := by
  rw [fractionMap, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  exact Polynomial.aeval_X _

private theorem fractionMap_include {r : BoundaryRing K} (hn : r ≠ 0) (hr : specialize K r = 0) :
    (fractionMap (k := k) r hn hr).comp (includeBoundary k) =
      ((includeBoundary K).restrictScalars k).comp (boundaryMap (k := k) r hr) := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (zeroIdeal k).primeCompl
  have h :
      (fractionMap (k := k) r hn hr).comp
        ((includeBoundary k).comp (IsScalarTower.toAlgHom k (Polynomial k) (BoundaryRing k))) =
      ((includeBoundary K).restrictScalars k).comp ((boundaryMap (k := k) r hr).comp
        (IsScalarTower.toAlgHom k (Polynomial k) (BoundaryRing k))) := by
    apply Polynomial.algHom_ext
    change fractionMap (k := k) r hn hr (includeBoundary k (parameter k)) =
      includeBoundary K (boundaryMap (k := k) r hr (parameter k))
    rw [boundaryMap_parameter]
    change fractionMap (k := k) r hn hr (algebraMap (BoundaryRing k) (BoundaryField k)
      (algebraMap (Polynomial k) (BoundaryRing k) Polynomial.X)) = _
    rw [← IsScalarTower.algebraMap_apply, fractionMap_X]
  exact congrArg AlgHom.toRingHom h

end BoundaryRing

section Valuation

variable {k : Type u} [Field k] {X : SchemeOver k}

private abbrev affine (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A] :
    SchemeOver k := (testSpec k).obj (op (CommAlgCat.of k A))

private abbrev affineMap {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) : affine k B ⟶ affine k A :=
  (testSpec k).map (CommAlgCat.ofHom f).op

private theorem affineMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    affineMap g ≫ affineMap f = affineMap (g.comp f) := by
  rw [← CategoryTheory.Functor.map_comp]
  rfl

private def valuativeSquare {R F : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Algebra k R] [Algebra k F]
    (jAlg : R →ₐ[k] F) (hi : jAlg.toRingHom = algebraMap R F)
    (p : affine k F ⟶ X) : ValuativeCommSq X.hom where
  R := R
  K := F
  i₁ := p.left
  i₂ := (affine k R).hom
  commSq := ⟨by
    rw [Over.w p, ← hi]
    exact (Over.w (affineMap jAlg)).symm⟩

private theorem extend_point [IsProper X.hom]
    (p : affine k (BoundaryField k) ⟶ X) :
    ∃ z : affine k (BoundaryRing k) ⟶ X, affineMap (includeBoundary k) ≫ z = p := by
  let S := valuativeSquare (includeBoundary k) rfl p
  have hprop : IsProper X.hom := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hprop
  have hc : ValuativeCriterion X.hom := hprop.1.1.1
  obtain ⟨⟨l⟩⟩ := hc S
  refine ⟨Over.homMk l.default.l l.default.fac_right, ?_⟩
  apply Over.OverMorphism.ext
  exact l.default.fac_left

private theorem equal_of_generic_fiber [IsSeparated X.hom]
    {R F : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Algebra k R] [Algebra k F]
    (jAlg : R →ₐ[k] F) (hi : jAlg.toRingHom = algebraMap R F)
    (p q : affine k R ⟶ X) (h : affineMap jAlg ≫ p = affineMap jAlg ≫ q) :
    p = q := by
  let S := valuativeSquare jAlg hi (affineMap jAlg ≫ p)
  let lq : S.commSq.LiftStruct := ⟨q.left, by
    change Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ q.left =
      (affineMap jAlg ≫ p).left
    rw [← hi]
    exact (congrArg (fun f => f.left) h).symm, Over.w q⟩
  let lp : S.commSq.LiftStruct := ⟨p.left, by
    change Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ p.left =
      (affineMap jAlg ≫ p).left
    rw [← hi]
    rfl, Over.w p⟩
  have := IsSeparated.valuativeCriterion X.hom S
  apply Over.OverMorphism.ext
  exact congrArg (fun l : S.commSq.LiftStruct => l.l)
    (Subsingleton.elim lp lq)

private theorem fixed_at_fields {G : Specs.GroupScheme k} [act : ModObj G.X X]
    [IsReduced G.X.left] [IsSeparated X.hom]
    (y : 𝟙_ (SchemeOver k) ⟶ X)
    (hf : ∀ (K : Type u) [Field K] [Algebra k K] (g : affine k K ⟶ G.X),
      g • (toUnit (affine k K) ≫ y) = toUnit (affine k K) ≫ y) :
    IsFixedBy act.smul y := by
  unfold IsFixedBy
  apply (cancel_epi (ρ_ G.X).inv).mp
  have hpair : (ρ_ G.X).inv = lift (𝟙 G.X) (toUnit G.X) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · exact toUnit_unique _ _
  rw [hpair]
  simp only [← Category.assoc, lift_whiskerLeft, lift_snd]
  change (𝟙 G.X) • (toUnit G.X ≫ y) = toUnit G.X ≫ y
  apply Over.OverMorphism.ext
  apply ext_of_fromSpecResidueField_eq _ _ X.hom Set.univ dense_univ
  · intro x _
    let K := G.X.left.residueField x
    let f := G.X.left.fromSpecResidueField x
    let i : k →+* K := Spec.homEquivRingHom (f ≫ G.X.hom)
    let : Algebra k K := i.toAlgebra
    let g : affine k K ⟶ G.X :=
      Over.homMk f (Spec.map_preimage _).symm
    have hh := hf K g
    have ht : g ≫ toUnit G.X = toUnit (affine k K) := toUnit_unique _ _
    have hl : g ≫ ((𝟙 G.X) • (toUnit G.X ≫ y)) = g • (toUnit (affine k K) ≫ y) := by
      rw [ModObj.comp_smul, Category.comp_id, ← Category.assoc, ht]
    have hr : g ≫ toUnit G.X ≫ y = toUnit (affine k K) ≫ y := by
      rw [← Category.assoc, ht]
    exact congrArg (fun p => p.left) (hl.trans (hh.trans hr.symm))
  · exact (Over.w _).trans (Over.w _).symm

/-- Compatibility with the group action over the generic point descends by
separatedness and can then be restricted to the special fiber. -/
private theorem action_at_specialization {G : GroupScheme k} [ModObj G.X X]
    {Y R F S E : SchemeOver k} (x : 𝟙_ (SchemeOver k) ⟶ X)
    (p : E ⟶ G.X) (z : Y ⟶ X) (g : S ⟶ G.X)
    (j : F ⟶ R) (w : S ⟶ R) (c : R ⟶ S) (d : E ⟶ Y)
    (a₀ a₁ : R ⟶ Y) (b₀ b₁ : F ⟶ E) (l : S ⟶ Y)
    (hsep : ∀ {v v' : R ⟶ X}, j ≫ v = j ≫ v' → v = v')
    (hz : d ≫ z = p • (toUnit E ≫ x))
    (ha₀ : j ≫ a₀ = b₀ ≫ d) (ha₁ : j ≫ a₁ = b₁ ≫ d)
    (hw₀ : w ≫ a₀ = l) (hw₁ : w ≫ a₁ = l) (hwc : w ≫ c = 𝟙 _)
    (hg : ((j ≫ c ≫ g) * (b₀ ≫ p)) = b₁ ≫ p) :
    g • (l ≫ z) = l ≫ z := by
  have generic_orbit (β : F ⟶ E) :
      β ≫ (p • (toUnit E ≫ x)) = (β ≫ p) • (toUnit F ≫ x) := by
    rw [ModObj.comp_smul]
    congr 1
    rw [← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  have h₀ : j ≫ (a₀ ≫ z) = (b₀ ≫ p) • (toUnit F ≫ x) := by
    rw [← Category.assoc, ha₀, Category.assoc, hz, generic_orbit]
  have h₁ : j ≫ (a₁ ≫ z) = (b₁ ≫ p) • (toUnit F ≫ x) := by
    rw [← Category.assoc, ha₁, Category.assoc, hz, generic_orbit]
  have heq : (c ≫ g) • (a₀ ≫ z) = a₁ ≫ z := hsep (by
    rw [ModObj.comp_smul, h₀, h₁, ← mul_smul, hg])
  have hs := congrArg (w ≫ ·) heq
  change w ≫ ((c ≫ g) • (a₀ ≫ z)) = w ≫ a₁ ≫ z at hs
  rw [ModObj.comp_smul, ← Category.assoc w c, hwc, Category.id_comp,
    ← Category.assoc w a₀, ← Category.assoc w a₁, hw₀, hw₁] at hs
  exact hs

private theorem rationalSpec_hom (k : Type u) [Field k] :
    (affine k k).hom = 𝟙 (Spec (CommRingCat.of k)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
  have h : CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) :=
    CommRingCat.hom_ext (RingHom.ext fun c => Algebra.algebraMap_self_apply c)
  rw [h, Spec.map_id]

private def affineBaseTerminal (k : Type u) [Field k] : IsTerminal (affine k k) :=
  Over.mkIdTerminal.ofIso (Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
    change 𝟙 (Spec (CommRingCat.of k)) ≫ (affine k k).hom = 𝟙 (Spec (CommRingCat.of k))
    exact (Category.id_comp _).trans (rationalSpec_hom k)))

private def rationalSpec (k : Type u) [Field k] : 𝟙_ (SchemeOver k) ⟶ affine k k :=
  (affineBaseTerminal k).from _

private theorem toUnit_rationalSpec (K : Type u) [Field K] [Algebra k K] :
    toUnit (affine k K) ≫ rationalSpec k = affineMap (Algebra.ofId k K) :=
  (affineBaseTerminal k).hom_ext _ _

private theorem boundary_generic_square {K : Type u} [Field K] [Algebra k K]
    {r : BoundaryRing K} (hn : r ≠ 0) (hr : specialize K r = 0) :
    affineMap ((includeBoundary K).restrictScalars k) ≫ affineMap (boundaryMap (k := k) r hr) =
      affineMap (fractionMap (k := k) r hn hr) ≫ affineMap (includeBoundary k) := by
  rw [affineMap_comp, affineMap_comp, fractionMap_include]

private theorem boundary_special_square {K : Type u} [Field K] [Algebra k K]
    {r : BoundaryRing K} (hr : specialize K r = 0) :
    affineMap ((specialize K).restrictScalars k) ≫ affineMap (boundaryMap (k := k) r hr) =
      (toUnit (affine k K) ≫ rationalSpec k) ≫ affineMap (specialize k) := by
  rw [toUnit_rationalSpec, affineMap_comp, affineMap_comp, boundaryMap_specialize]

private theorem boundary_generic_constants (K : Type u) [Field K] [Algebra k K] :
    affineMap ((includeBoundary K).restrictScalars k) ≫
        affineMap ((Algebra.ofId K (BoundaryRing K)).restrictScalars k) =
      affineMap ((Algebra.ofId K (BoundaryField K)).restrictScalars k) := by
  rw [affineMap_comp]
  congr 1
  apply AlgHom.ext
  exact (includeBoundary K).commutes

private theorem boundary_special_constants (K : Type u) [Field K] [Algebra k K] :
    affineMap ((specialize K).restrictScalars k) ≫
        affineMap ((Algebra.ofId K (BoundaryRing K)).restrictScalars k) = 𝟙 _ := by
  rw [affineMap_comp]
  have he : ((specialize K).restrictScalars k).comp
      ((Algebra.ofId K (BoundaryRing K)).restrictScalars k) = AlgHom.id k K := by
    apply AlgHom.ext
    exact (specialize K).commutes
  rw [he]
  exact CategoryTheory.Functor.map_id _ _

/-- The two maps of valuation rings agree at the boundary.  A relation
between their generic orbit sections therefore specializes to a fixed point. -/
private theorem fixed_from_boundary {G : Specs.GroupScheme k} [ModObj G.X X]
    [IsReduced G.X.left] [IsProper X.hom] (x : 𝟙_ (SchemeOver k) ⟶ X)
    (p : affine k (BoundaryField k) ⟶ G.X)
    (h : ∀ (K : Type u) [Field K] [Algebra k K] (g : affine k K ⟶ G.X),
      ∃ (r₀ r₁ : BoundaryRing K) (n₀ : r₀ ≠ 0) (n₁ : r₁ ≠ 0)
        (z₀ : specialize K r₀ = 0) (z₁ : specialize K r₁ = 0),
        ((affineMap ((Algebra.ofId K (BoundaryField K)).restrictScalars k) ≫ g) *
            (affineMap (fractionMap (k := k) r₀ n₀ z₀) ≫ p)) =
          affineMap (fractionMap (k := k) r₁ n₁ z₁) ≫ p) :
    ∃ y : 𝟙_ (SchemeOver k) ⟶ X, IsFixedBy γ[G.X, X] y := by
  let b := toUnit (affine k (BoundaryField k)) ≫ x
  obtain ⟨z, hz⟩ := extend_point (p • b)
  let y := rationalSpec k ≫ affineMap (specialize k) ≫ z
  refine ⟨y, fixed_at_fields y ?_⟩
  intro K _ _ g
  obtain ⟨r₀, r₁, n₀, n₁, z₀, z₁, he⟩ := h K g
  let α₀ := affineMap (boundaryMap (k := k) r₀ z₀)
  let α₁ := affineMap (boundaryMap (k := k) r₁ z₁)
  let β₀ := affineMap (fractionMap (k := k) r₀ n₀ z₀)
  let β₁ := affineMap (fractionMap (k := k) r₁ n₁ z₁)
  let j := affineMap ((includeBoundary K).restrictScalars k)
  let w := affineMap ((specialize K).restrictScalars k)
  let c := affineMap ((Algebra.ofId K (BoundaryRing K)).restrictScalars k)
  let l := (toUnit (affine k K) ≫ rationalSpec k) ≫ affineMap (specialize k)
  have hsep {v v' : affine k (BoundaryRing K) ⟶ X} (h : j ≫ v = j ≫ v') : v = v' :=
    equal_of_generic_fiber ((includeBoundary K).restrictScalars k) rfl v v' h
  have hg : ((j ≫ c ≫ g) * (β₀ ≫ p)) = β₁ ≫ p :=
    calc
      _ = ((affineMap ((Algebra.ofId K (BoundaryField K)).restrictScalars k) ≫ g) *
          (β₀ ≫ p)) := by rw [← Category.assoc j c, boundary_generic_constants]
      _ = _ := he
  have hs := action_at_specialization x p z g j w c (affineMap (includeBoundary k))
    α₀ α₁ β₀ β₁ l hsep hz (boundary_generic_square n₀ z₀) (boundary_generic_square n₁ z₁)
    (boundary_special_square z₀) (boundary_special_square z₁) (boundary_special_constants K) hg
  simpa only [l, y, Category.assoc] using hs

end Valuation

section RankOne

open LinearAlgebraicGroups.Specs.StandardGroups (additivePoints multiplicativePoints)

variable {k : Type u} [Field k] {X : SchemeOver k}
variable {H : GroupScheme k}

private theorem coordinates_natural {A B : Type u} [CommRing A] [CommRing B] [Algebra k A]
    [Algebra k B] {P : TestAlgebra k ⥤ GrpCat.{u}}
    (e : (groupPointsFunctor k).obj H ≅ P) (f : A →ₐ[k] B) (p : affine k A ⟶ H.X) :
    e.hom.app (CommAlgCat.of k B) (affineMap f ≫ p) =
      P.map (CommAlgCat.ofHom f) (e.hom.app (CommAlgCat.of k A) p) := by
  exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom
    (e.hom.naturality (CommAlgCat.ofHom f))) p

private theorem coordinates_inv {A : Type u} [CommRing A] [Algebra k A]
    {P : TestAlgebra k ⥤ GrpCat.{u}}
    (e : (groupPointsFunctor k).obj H ≅ P) (v : P.obj (CommAlgCat.of k A)) :
    e.hom.app (CommAlgCat.of k A) (e.inv.app (CommAlgCat.of k A) v) = v := by
  exact DFunLike.congr_fun (congrArg (fun f => (f.app (CommAlgCat.of k A)).hom) e.inv_hom_id) v

private theorem coordinate_injective {A : Type u} [CommRing A] [Algebra k A]
    {P : TestAlgebra k ⥤ GrpCat.{u}} (e : (groupPointsFunctor k).obj H ≅ P) :
    Function.Injective (e.hom.app (CommAlgCat.of k A)) :=
  (ConcreteCategory.bijective_of_isIso (e.hom.app (CommAlgCat.of k A))).1

private abbrev fracParameter (k : Type u) [Field k] : BoundaryField k :=
  algebraMap (Polynomial k) (BoundaryField k) Polynomial.X

private theorem fracParameter_ne_zero (k : Type u) [Field k] : fracParameter k ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := BoundaryField k)
    (mem_nonZeroDivisors_iff_ne_zero.mpr Polynomial.X_ne_zero)

private theorem additive_map_toAdd {A B : Type u} [CommRing A] [CommRing B] [Algebra k A]
    [Algebra k B] (f : A →ₐ[k] B) (v : (additivePoints k).obj (CommAlgCat.of k A)) :
    Multiplicative.toAdd ((additivePoints k).map (CommAlgCat.ofHom f) v) =
      f (Multiplicative.toAdd v) := rfl

private theorem additive_fixed [ModObj H.X X] [IsReduced H.X.left] [IsProper X.hom]
    (e : (groupPointsFunctor k).obj H ≅ additivePoints k) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    ∃ y : 𝟙_ (SchemeOver k) ⟶ X, IsFixedBy γ[H.X, X] y := by
  let genericCoord : BoundaryField k := (fracParameter k)⁻¹
  let coord : Multiplicative (BoundaryField k) := Multiplicative.ofAdd genericCoord
  have hcoord : Multiplicative.toAdd coord = genericCoord := rfl
  let p : affine k (BoundaryField k) ⟶ H.X := e.inv.app (CommAlgCat.of k (BoundaryField k)) coord
  have hp : e.hom.app (CommAlgCat.of k (BoundaryField k)) p = coord :=
    coordinates_inv (A := BoundaryField k) e coord
  apply fixed_from_boundary x p
  intro K _ _ g
  let s : K := Multiplicative.toAdd (e.hom.app (CommAlgCat.of k K) g)
  let t := parameter K
  let d : BoundaryRing K := 1 + algebraMap K (BoundaryRing K) s * t
  have hd : specialize K d = 1 := by
    simp only [d, t, map_add, map_one, map_mul, specialize_parameter, mul_zero, add_zero]
  let u : (BoundaryRing K)ˣ := (specialize_unit K (by rw [hd]; exact one_ne_zero)).unit
  have hu : (u : BoundaryRing K) = d :=
    (specialize_unit K (by rw [hd]; exact one_ne_zero)).unit_spec
  let r : BoundaryRing K := t * ↑u⁻¹
  have hn : r ≠ 0 := mul_ne_zero (parameter_ne_zero K) (Units.ne_zero _)
  have hz : specialize K r = 0 := by
    simp only [r, t, map_mul, specialize_parameter, zero_mul]
  refine ⟨t, r, parameter_ne_zero K, hn, specialize_parameter K, hz, ?_⟩
  apply coordinate_injective e
  rw [(e.hom.app (CommAlgCat.of k (BoundaryField K))).hom.map_mul,
    coordinates_natural, coordinates_natural, coordinates_natural, hp]
  let a : Multiplicative (BoundaryField K) :=
    (additivePoints k).map (CommAlgCat.ofHom ((Algebra.ofId K (BoundaryField K)).restrictScalars k))
      (e.hom.app (CommAlgCat.of k K) g)
  let b : Multiplicative (BoundaryField K) :=
    (additivePoints k).map
      (CommAlgCat.ofHom (fractionMap (k := k) t (parameter_ne_zero K) (specialize_parameter K))) coord
  let c : Multiplicative (BoundaryField K) :=
    (additivePoints k).map (CommAlgCat.ofHom (fractionMap (k := k) r hn hz)) coord
  change a * b = c
  apply Multiplicative.ext
  rw [toAdd_mul]
  have ha : a.toAdd = algebraMap K (BoundaryField K) s :=
    additive_map_toAdd (A := K) (B := BoundaryField K)
      ((Algebra.ofId K (BoundaryField K)).restrictScalars k) (e.hom.app (CommAlgCat.of k K) g)
  have hb : b.toAdd =
      fractionMap (k := k) t (parameter_ne_zero K) (specialize_parameter K) (fracParameter k)⁻¹ :=
    (additive_map_toAdd (A := BoundaryField k) (B := BoundaryField K)
      (fractionMap (k := k) t (parameter_ne_zero K) (specialize_parameter K)) coord).trans
      (congrArg (fractionMap (k := k) t (parameter_ne_zero K) (specialize_parameter K)) hcoord)
  have hc : c.toAdd = fractionMap (k := k) r hn hz (fracParameter k)⁻¹ :=
    (additive_map_toAdd (A := BoundaryField k) (B := BoundaryField K)
      (fractionMap (k := k) r hn hz) coord).trans
      (congrArg (fractionMap (k := k) r hn hz) hcoord)
  rw [ha, hb, hc]
  simp only [map_inv₀, fracParameter, fractionMap_X]
  let T := includeBoundary K t
  let S := algebraMap K (BoundaryField K) s
  have hT : T ≠ 0 := by
    intro ht
    apply parameter_ne_zero K
    apply IsFractionRing.injective (BoundaryRing K) (BoundaryField K)
    rw [map_zero]
    exact ht
  have hdenom : includeBoundary K (↑(u⁻¹) : BoundaryRing K) = (1 + S * T)⁻¹ := by
    have hm : includeBoundary K (↑u : BoundaryRing K) = 1 + S * T := by
      rw [hu]
      simp only [d, map_add, map_one, map_mul, AlgHom.commutes, S, T]
    rw [← hm]
    have hprod : includeBoundary K (↑(u⁻¹) : BoundaryRing K) *
        includeBoundary K (↑u : BoundaryRing K) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hnonzero : includeBoundary K (↑u : BoundaryRing K) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hprod
      exact zero_ne_one hprod
    simpa only [one_mul] using (eq_mul_inv_iff_mul_eq₀ hnonzero).2 hprod
  rw [show (includeBoundary K) r = T * (1 + S * T)⁻¹ by rw [map_mul, hdenom]]
  rw [mul_inv_rev, inv_inv]
  rw [eq_mul_inv_iff_mul_eq₀ hT, add_mul, inv_mul_cancel₀ hT]
  exact add_comm _ _

private theorem multiplicative_fixed [ModObj H.X X] [IsReduced H.X.left] [IsProper X.hom]
    (e : (groupPointsFunctor k).obj H ≅ multiplicativePoints k) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    ∃ y : 𝟙_ (SchemeOver k) ⟶ X, IsFixedBy γ[H.X, X] y := by
  let coord := Units.mk0 (fracParameter k) (fracParameter_ne_zero k)
  let p : affine k (BoundaryField k) ⟶ H.X := e.inv.app _ coord
  have hp : e.hom.app (CommAlgCat.of k (BoundaryField k)) p = coord := coordinates_inv (A := BoundaryField k) e _
  apply fixed_from_boundary x p
  intro K _ _ g
  let s : Kˣ := e.hom.app (CommAlgCat.of k K) g
  let t := parameter K
  let r : BoundaryRing K := algebraMap K _ (s : K) * t
  have hn : r ≠ 0 := mul_ne_zero
    (by simpa only [map_zero] using (algebraMap K (BoundaryRing K)).injective.ne (Units.ne_zero s))
    (parameter_ne_zero K)
  have hz : specialize K r = 0 := by
    simp only [r, t, map_mul, specialize_parameter, mul_zero]
  refine ⟨t, r, parameter_ne_zero K, hn, specialize_parameter K, hz, ?_⟩
  apply coordinate_injective e
  rw [(e.hom.app (CommAlgCat.of k (BoundaryField K))).hom.map_mul,
    coordinates_natural, coordinates_natural, coordinates_natural, hp]
  apply Units.ext
  change algebraMap K (BoundaryField K) (s : K) *
      fractionMap (k := k) t (parameter_ne_zero K) (specialize_parameter K) (fracParameter k) =
    fractionMap (k := k) r hn hz (fracParameter k)
  simp only [fracParameter, fractionMap_X, r, map_mul, AlgHom.commutes]

private theorem reduced_of_points_iso (A B : AffineAlgebraicGroup k)
    [IsReduced B.val.X.left] (e : (groupPointsFunctor k).obj A.val ≅
      (groupPointsFunctor k).obj B.val) : IsReduced A.val.X.left := by
  let h := (LinearAlgebraicGroups.AffineAlgebraicGroup.groupHomEquiv A B).symm e.hom
  let j := (LinearAlgebraicGroups.AffineAlgebraicGroup.groupHomEquiv B A).symm e.inv
  have hh : (groupPointsFunctor k).map h = e.hom :=
    (LinearAlgebraicGroups.AffineAlgebraicGroup.groupHomEquiv A B).apply_symm_apply _
  have hj : (groupPointsFunctor k).map j = e.inv :=
    (LinearAlgebraicGroups.AffineAlgebraicGroup.groupHomEquiv B A).apply_symm_apply _
  have h₁ : h ≫ j = 𝟙 _ := (groupHomComparison k A.val A.val A.property.1).1 (by simp [hh, hj])
  have h₂ : j ≫ h = 𝟙 _ := (groupHomComparison k B.val B.val B.property.1).1 (by simp [hh, hj])
  let φ : A.val ≅ B.val := ⟨h, j, h₁, h₂⟩
  let f := ((Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso φ).hom
  have : IsReduced ((Grp.forget (SchemeOver k) ⋙ Over.forget _).obj B.val) := ‹IsReduced B.val.X.left›
  exact isReduced_of_isOpenImmersion f

end RankOne

private theorem split_fixed_has_point {G : GroupScheme k} (hs : IsSplitSolvable G) :
    ∀ (_hG : IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom)
      {X : SchemeOver k} [act : ModObj G.X X] [IsProper X.hom], (𝟙_ (SchemeOver k) ⟶ X) →
      ∃ y : 𝟙_ (SchemeOver k) ⟶ X, IsFixedBy act.smul y := by
  induction hs with
  | @trivial H e =>
    intro _ X act _ x
    obtain ⟨e⟩ := e
    refine ⟨x, (fixed_iff_sections x).mpr ?_⟩
    intro U f g
    let j := ((Grp.forget (SchemeOver k)).mapIso e).hom
    have h : g = 1 := (cancel_mono j).mp (toUnit_unique _ _)
    rw [h, one_smul]
  | @step H D hn hs Q q hq hfactor ih =>
    intro hH X act hproper x
    let D' := closedSubgroupAlgebraic ⟨H, hH⟩ D
    let actD := restrictAction D.inclusion (X := X)
    obtain ⟨xD, hD⟩ := ih D'.property x
    obtain ⟨Y, i, hclosed, hrep⟩ := fixedPointScheme k D' X actD
      inferInstance inferInstance inferInstance
    obtain ⟨y, _⟩ := (hrep _ _).mp hD
    have : Mono i := Over.mono_of_mono_left i
    have : IsProper Y.hom := by
      rw [← Over.w i]
      infer_instance
    obtain ⟨b, hb, hbD⟩ := induced_fixed_action D hn i hrep
    let := b
    obtain ⟨c, hc⟩ := descend_action D q hq (Z := Y) hbD
    let := c
    obtain ⟨z, hz⟩ : ∃ z : 𝟙_ (SchemeOver k) ⟶ Y, IsFixedBy c.smul z := by
      rcases hfactor with e | e
      · obtain ⟨e⟩ := e
        have : IsReduced (StandardGroups.additiveGroup k).val.X.left := by
          change IsReduced (Spec (CommRingCat.of (Polynomial k)))
          infer_instance
        have : IsReduced Q.val.X.left :=
          reduced_of_points_iso Q (StandardGroups.additiveGroup k)
            (e ≪≫ (StandardGroups.additiveGroupPointsIso k).symm)
        exact additive_fixed e y
      · obtain ⟨e⟩ := e
        have : IsReduced (StandardGroups.multiplicativeGroup k).val.X.left := by
          change IsReduced (Spec (CommRingCat.of (LaurentPolynomial k)))
          infer_instance
        have : IsReduced Q.val.X.left :=
          reduced_of_points_iso Q (StandardGroups.multiplicativeGroup k)
            (e ≪≫ (StandardGroups.multiplicativeGroupPointsIso k).symm)
        exact multiplicative_fixed e y
    refine ⟨z ≫ i, (fixed_iff_sections _).mpr ?_⟩
    intro U t g
    have hfix : (g ≫ q.hom.hom) • (t ≫ z) = t ≫ z :=
      (fixed_iff_sections z).mp hz t (g ≫ q.hom.hom)
    change lift (g ≫ q.hom.hom) (t ≫ z) ≫ c.smul = t ≫ z at hfix
    rw [hc] at hfix
    change lift g (t ≫ z) ≫ b.smul = t ≫ z at hfix
    rw [← Category.assoc t z i, ← hb, ← Category.assoc, hfix]

/-- The Borel fixed-point theorem for split solvable groups over any field. -/
theorem splitSolvableFixedPoint : Specs.SplitSolvableFixedPoint.{u} := by
  intro k _ G X act hG hproper hx
  obtain ⟨x⟩ := hx
  obtain ⟨y, hy⟩ := split_fixed_has_point hG G.property x
  obtain ⟨Z, i, hi, hrep⟩ := fixedPointScheme k G X act
    inferInstance inferInstance inferInstance
  obtain ⟨z, _⟩ := (hrep _ _).mp hy
  exact ⟨Z, i, hi, hrep, ⟨z⟩⟩

end
end LinearAlgebraicGroups
