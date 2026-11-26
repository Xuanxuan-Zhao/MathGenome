import Specs.LinearAlgebraicGroups.Flag.FrobeniusObstruction
import LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import LinearAlgebraicGroups.Flag.TorsorObstruction
import Mathlib.Algebra.CharP.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.KummerPolynomial
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.FrobeniusObstruction

open Specs Specs.FrobeniusObstruction
open Specs.DiagonalizableGroups Specs.Fppf Specs.TorsorObstruction

noncomputable section

open IsDedekindDomain.HeightOneSpectrum WithZero in
theorem noRationalRoot : NoRationalRoot := by
  intro p _ b h
  have hp : p.Prime := Fact.out
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, zero_pow hp.ne_zero] at h
    exact RatFunc.X_ne_zero h.symm
  let v := (Polynomial.idealX (ZMod p)).valuation (BaseField p)
  have hv : v b ≠ 0 := (map_ne_zero v).2 hb
  have e : v b ^ p = exp (-1 : ℤ) := by
    rw [← map_pow, h]
    exact Polynomial.valuation_X_eq_neg_one (ZMod p)
  rw [← exp_log hv, ← exp_nsmul] at e
  have hi := exp_injective e
  have hd : (p : ℤ) ∣ (-1 : ℤ) := ⟨log (v b), by simpa [nsmul_eq_mul] using hi.symm⟩
  have hone := Int.eq_one_of_dvd_one (by positivity : (0 : ℤ) ≤ p) (dvd_neg.mp hd)
  exact hp.ne_one (by exact_mod_cast hone)

private theorem baseChar (p : ℕ) [Fact p.Prime] : CharP (BaseField p) p :=
  CharP.of_ringHom_of_ne_zero (algebraMap (ZMod p) (BaseField p)) p
    (Fact.out : p.Prime).ne_zero

theorem noSeparableRoot : NoSeparableRoot := by
  intro p _ L _ _ _ b h
  let : CharP (BaseField p) p := baseChar p
  let f : Polynomial (BaseField p) := Polynomial.X ^ p - Polynomial.C RatFunc.X
  have hf : Irreducible f := X_pow_sub_C_irreducible_of_prime Fact.out (noRationalRoot p)
  have hd : f.derivative = 0 := by
    simp [f, Polynomial.derivative_X_pow]
  have hroot : Polynomial.aeval b f = 0 := by
    simpa [f] using sub_eq_zero.mpr h
  have he : f = minpoly (BaseField p) b := by
    have hm : f.Monic := Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero
    simpa [hm.leadingCoeff] using minpoly.eq_of_irreducible hf hroot
  apply (Polynomial.separable_iff_derivative_ne_zero hf).mp _ hd
  rw [he]
  exact Algebra.IsSeparable.isSeparable (BaseField p) b

open private integerPointsIso pointsIso_precompose
  from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups

private abbrev M := IntegerCharacters.{0}

private abbrev powerCharacters (p : ℕ) : M →* M := powMonoidHom p

private abbrev powerRange (p : ℕ) : Subgroup M := (powerCharacters p).range

private def powerRangeIso (p : ℕ) (hp : p ≠ 0) : M ≃* powerRange p :=
  MulEquiv.ofBijective (powerCharacters p).rangeRestrict ⟨fun a b h ↦ by
    have e := congrArg (fun z : powerRange p ↦ z.val.down.toAdd) h
    change (p : ℤ) * a.down.toAdd = (p : ℤ) * b.down.toAdd at e
    have hcast : (p : ℤ) ≠ 0 := by exact_mod_cast hp
    exact ULift.ext (mul_left_cancel₀ (M₀ := ℤ) hcast e),
    (powerCharacters p).rangeRestrict_surjective⟩

private abbrev powerMap (p : ℕ) [Fact p.Prime] : Gm p ⟶ Gm p :=
  specGroupMap (groupAlgebraMap (BaseField p) (powerCharacters p))

private def rankOnePoints (p : ℕ) [Fact p.Prime] :
    (groupPointsFunctor (BaseField p)).obj (Gm p) ≅
      Specs.StandardGroups.multiplicativePoints (BaseField p) :=
  LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso (BaseField p) M ≪≫
    integerPointsIso (k := BaseField p)

private theorem rankOnePoints_power (p : ℕ) [Fact p.Prime] (R : TestAlgebra (BaseField p))
    (g : Points (Gm p).X R) :
    ((rankOnePoints p).hom.app R (g ≫ (powerMap p).hom.hom) : Rˣ) =
      ((rankOnePoints p).hom.app R g : Rˣ) ^ p := by
  let e := LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso (BaseField p) M
  change (show M →* Rˣ from e.hom.app R
      (((groupPointsFunctor (BaseField p)).map (powerMap p)).app R g)) integerGenerator =
    (show M →* Rˣ from e.hom.app R g) integerGenerator ^ p
  refine (pointsIso_precompose (k := BaseField p) (powerCharacters p) R g integerGenerator).trans ?_
  exact map_pow (show M →* Rˣ from e.hom.app R g) integerGenerator p

set_option maxHeartbeats 1500000 in
open MonoidAlgebra in
private def rangeTargetIso (p : ℕ) [Fact p.Prime] :
    specGroup (groupAlgebra (BaseField p) (powerRange p)) ≅ Gm p := by
  let e := powerRangeIso p (Fact.out : p.Prime).ne_zero
  let k := BaseField p
  refine (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).mapIso
    (CommHopfAlgCat.isoMk (BialgEquiv.ofBialgHom
      (mapDomainBialgHom k e.toMonoidHom) (mapDomainBialgHom k e.symm.toMonoidHom) ?_ ?_)).op
  · rw [← mapDomainBialgHom_comp]
    exact (congrArg (mapDomainBialgHom k) (MulEquiv.toMonoidHom_comp_toMonoidHom_symm e)).trans
      mapDomainBialgHom_id
  · rw [← mapDomainBialgHom_comp]
    exact (congrArg (mapDomainBialgHom k) (MulEquiv.toMonoidHom_symm_comp_toMonoidHom e)).trans
      mapDomainBialgHom_id

set_option maxHeartbeats 1500000 in
private theorem powerMap_factor (p : ℕ) [Fact p.Prime] :
    diagonalRestriction (BaseField p) (powerRange p) ≫ (rangeTargetIso p).hom = powerMap p := by
  change specGroupMap (groupAlgebraMap _ (powerRange p).subtype) ≫
      specGroupMap (groupAlgebraMap _ (powerCharacters p).rangeRestrict) = _
  rw [← specGroupMap_comp]
  congr 1
  apply CommHopfAlgCat.hom_ext
  exact (MonoidAlgebra.mapDomainBialgHom_comp (powerRange p).subtype
    (powerCharacters p).rangeRestrict).symm

set_option maxHeartbeats 1500000 in
private theorem powerQuotient (p : ℕ) [Fact p.Prime] :
    ∃ H : ClosedSubgroup (Gm p),
      IsSchemeKernel (powerMap p) H ∧
      Flat (powerMap p).hom.hom.left ∧ Surjective (powerMap p).hom.hom.left ∧
      LocallyOfFinitePresentation (powerMap p).hom.hom.left ∧
      ∃ e : rightQuotientSheaf H ≅ schemeFppfSheaf (Gm p).X,
        rightQuotientProjection H ≫ e.hom = (fppfOver (BaseField p)).uliftYoneda.map
          (powerMap p).hom.hom := by
  let k := BaseField p
  obtain ⟨hc, hf, hs, hp, hK, e, hq⟩ :=
    LinearAlgebraicGroups.DiagonalizableGroups.diagonalRestrictionKernelAndQuotient
      k M (powerRange p)
  let H : ClosedSubgroup (Gm p) :=
    ⟨specGroup (groupAlgebra k (M ⧸ powerRange p)), diagonalClosedInclusion k _, hc⟩
  let r := diagonalRestriction k (powerRange p)
  let i := (Grp.forget (SchemeOver k)).mapIso (rangeTargetIso p)
  have hi : r.hom.hom ≫ i.hom = (powerMap p).hom.hom :=
    congrArg (fun f ↦ f.hom.hom) (powerMap_factor p)
  have hl : r.hom.hom.left ≫ i.hom.left = (powerMap p).hom.hom.left :=
    congrArg Over.Hom.left hi
  have hKr : IsSchemeKernel r H := hK
  have hk : IsSchemeKernel (powerMap p) H := by
    change IsPullback H.inclusion.hom.hom (CategoryTheory.CartesianMonoidalCategory.toUnit _)
      (powerMap p).hom.hom η[(Gm p).X]
    refine hKr.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) i ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact hi.trans (Category.id_comp _).symm
    · exact (IsMonHom.one_hom (rangeTargetIso p).hom.hom.hom).trans (Category.id_comp _).symm
  let : IsIso i.hom.left := inferInstance
  let : IsOpenImmersion i.hom.left := inferInstance
  refine ⟨H, hk, ?_, ?_, ?_, e ≪≫ (fppfOver k).uliftYoneda.mapIso i, ?_⟩
  · rw [← hl]
    exact MorphismProperty.comp_mem @Flat _ _ hf (show Flat i.hom.left from inferInstance)
  · rw [← hl]
    exact (MorphismProperty.cancel_right_of_respectsIso @Surjective _ i.hom.left).2 hs
  · rw [← hl]
    exact MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ hp
      (show LocallyOfFinitePresentation i.hom.left from inferInstance)
  · let F := (fppfOver k).uliftYoneda.{1}
    have hq' : rightQuotientProjection H ≫ e.hom = F.map r.hom.hom := hq
    calc
      _ = (rightQuotientProjection H ≫ e.hom) ≫ F.map i.hom := (Category.assoc _ _ _).symm
      _ = F.map r.hom.hom ≫ F.map i.hom := congrArg (· ≫ F.map i.hom) hq'
      _ = F.map (r.hom.hom ≫ i.hom) := (F.map_comp _ _).symm
      _ = _ := congrArg F.map hi

private def fieldTestIso (k : Type) [Field k] :
    fieldBase k ≅ (testSpec k).obj (op (CommAlgCat.of k k)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
    rw [Category.id_comp]
    exact Spec.map_id (CommRingCat.of k))

private theorem liftAffinePoint {k : Type} [Field k] {X : SchemeOver k}
    (hX : IsAffine X.left) (hs : Smooth X.hom)
    {B : Type} [CommRing B] [Algebra k B] (I : Ideal B) (hI : IsNilpotent I)
    (x : Points X (CommAlgCat.of k (B ⧸ I))) :
    ∃ y : Points X (CommAlgCat.of k B),
      mapPoints (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)) y = x := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hX
  have he : IsIso e.hom.left := inferInstance
  let : IsOpenImmersion e.hom.left := inferInstance
  have hsA : Smooth ((testSpec k).obj A).hom := by
    rw [← Over.w e.hom]
    exact MorphismProperty.comp_mem @Smooth _ _ (show Smooth e.hom.left from inferInstance) hs
  have hr : (algebraMap k A.unop).Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsA
  let : Algebra.Smooth k A.unop := RingHom.smooth_algebraMap.mp hr
  let F := testSpec k
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let b : A.unop ⟶ CommAlgCat.of k (B ⧸ I) := (ff.preimage (x ≫ e.inv)).unop
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift I hI b.hom
  let f' : A.unop ⟶ CommAlgCat.of k B := CommAlgCat.ofHom f
  let π : CommAlgCat.of k B ⟶ CommAlgCat.of k (B ⧸ I) :=
    CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)
  have hf' : f' ≫ π = b := CommAlgCat.hom_ext hf
  refine ⟨F.map f'.op ≫ e.hom, ?_⟩
  change F.map π.op ≫ F.map f'.op ≫ e.hom = x
  calc
    _ = F.map (f' ≫ π).op ≫ e.hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ e.hom) (F.map_comp _ _).symm)
    _ = F.map b.op ≫ e.hom := congrArg (fun a : A.unop ⟶ _ ↦ F.map a.op ≫ e.hom) hf'
    _ = (x ≫ e.inv) ≫ e.hom := congrArg (· ≫ e.hom) (ff.map_preimage _)
    _ = x := (Category.assoc _ _ _).trans
      ((congrArg (x ≫ ·) e.inv_hom_id).trans (Category.comp_id _))

open Polynomial in
private theorem rootWithoutInfinitesimalLift (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra k B) (I : Ideal B) (u : (B ⧸ I)ˣ),
      IsNilpotent I ∧ u ^ p = 1 ∧
        ¬ ∃ v : Bˣ, v ^ p = 1 ∧ Units.map (Ideal.Quotient.mk I).toMonoidHom v = u := by
  have hp : p.Prime := Fact.out
  let f : k[X] := X ^ (p + 1)
  let B := AdjoinRoot f
  let r : B := AdjoinRoot.root f
  have hr0 : r ^ (p + 1) = 0 := by
    change AdjoinRoot.mk f X ^ (p + 1) = 0
    rw [← map_pow]
    exact AdjoinRoot.mk_self
  have hrne : r ^ p ≠ 0 := by
    change AdjoinRoot.mk f X ^ p ≠ 0
    rw [← map_pow]
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X.pow _) (pow_ne_zero _ X_ne_zero)
    simp
  let : Nontrivial B := nontrivial_of_ne _ _ hrne
  let : CharP B p := CharP.of_ringHom_of_ne_zero (algebraMap k B) p hp.ne_zero
  let I : Ideal B := Ideal.span {r ^ p}
  let π := Ideal.Quotient.mk I
  have hI : I ^ 2 = ⊥ := by
    change Ideal.span {r ^ p} ^ 2 = ⊥
    rw [Ideal.span_singleton_pow, ← pow_mul, pow_eq_zero_of_le _ hr0, Ideal.span_singleton_eq_bot]
    have := hp.pos
    omega
  have hπ : (π r) ^ p = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hu : IsUnit (1 + π r) := IsNilpotent.isUnit_one_add ⟨p, hπ⟩
  let u := hu.unit
  have huv : u.val = 1 + π r := hu.unit_spec
  refine ⟨B, inferInstance, inferInstance, I, u, ⟨2, hI⟩, ?_, ?_⟩
  · apply Units.ext
    change u.val ^ p = 1
    rw [huv, ← map_one π, ← map_add, ← map_pow, add_pow_char, one_pow, map_add, map_one, map_pow, hπ, add_zero]
  · rintro ⟨v, hv, hvm⟩
    have hv' : v.val ^ p = 1 := congrArg Units.val hv
    have heq : π v.val = π (1 + r) := by
      exact (congrArg Units.val hvm).trans (huv.trans (map_add π _ _ |>.trans (congrArg (· + π r) (map_one π))).symm)
    have hmem : v.val - (1 + r) ∈ I := Ideal.Quotient.eq.mp heq
    have hsquare : (v.val - (1 + r)) ^ 2 = 0 := by
      have hm := Ideal.pow_mem_pow hmem 2
      rwa [hI, Ideal.mem_bot] at hm
    have hpow := pow_eq_zero_of_le hp.two_le hsquare
    rw [sub_pow_char, hv', add_pow_char, one_pow, sub_add_eq_sub_sub, sub_self, zero_sub, neg_eq_zero] at hpow
    exact hrne hpow

private theorem kernelPoint_iff (p : ℕ) [Fact p.Prime] {H : ClosedSubgroup (Gm p)}
    (hK : IsSchemeKernel (powerMap p) H) (R : TestAlgebra (BaseField p))
    (g : Points (Gm p).X R) :
    (∃ a : Points H.group.X R, a ≫ H.inclusion.hom.hom = g) ↔
      ((rankOnePoints p).hom.app R g : Rˣ) ^ p = 1 := by
  let U := (testSpec (BaseField p)).obj (op R)
  let j := CategoryTheory.CartesianMonoidalCategory.toUnit U
  have h1 : ((rankOnePoints p).hom.app R (1 : Points (Gm p).X R) : Rˣ) = 1 :=
    map_one ((rankOnePoints p).hom.app R).hom
  have heq : g ≫ (powerMap p).hom.hom = j ≫ η[(Gm p).X] ↔
      ((rankOnePoints p).hom.app R g : Rˣ) ^ p = 1 := by
    constructor
    · intro h
      exact (rankOnePoints_power p R g).symm.trans
        ((congrArg ((rankOnePoints p).hom.app R) h).trans h1)
    · intro h
      apply (ConcreteCategory.bijective_of_isIso ((rankOnePoints p).hom.app R)).injective
      exact (rankOnePoints_power p R g).trans (h.trans h1.symm)
  constructor
  · rintro ⟨a, rfl⟩
    apply heq.mp
    have hterm : a ≫ CategoryTheory.CartesianMonoidalCategory.toUnit H.group.X = j :=
      CategoryTheory.CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
    exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) hK.w).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ η[(Gm p).X]) hterm)))
  · intro h
    exact ⟨hK.lift g j (heq.mpr h), hK.lift_fst g j (heq.mpr h)⟩

set_option maxHeartbeats 600000 in
private theorem kernelNotSmooth (p : ℕ) [Fact p.Prime] {H : ClosedSubgroup (Gm p)}
    (hK : IsSchemeKernel (powerMap p) H) : ¬ Smooth H.group.X.hom := by
  intro hs
  let k := BaseField p
  let : CharP k p := baseChar p
  obtain ⟨B, _, _, I, u, hI, hu, hn⟩ := rootWithoutInfinitesimalLift k p
  let R := CommAlgCat.of k (B ⧸ I)
  let S := CommAlgCat.of k B
  let c := rankOnePoints p
  let a : Points (Gm p).X R := c.inv.app R u
  have ha : (c.hom.app R a : Rˣ) = u :=
    congrArg (fun m : GrpCat.of Rˣ ⟶ GrpCat.of Rˣ ↦ m u) (NatTrans.congr_app c.inv_hom_id R)
  obtain ⟨x, hx⟩ := (kernelPoint_iff p hK R a).2 ((congrArg (· ^ p) ha).trans hu)
  let : IsAffine (Gm p).X.left := by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra k M)))
    infer_instance
  let : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  have hX := isAffine_of_isAffineHom H.inclusion.hom.hom.left
  obtain ⟨y, hy⟩ := liftAffinePoint hX hs I hI x
  let g : Points (Gm p).X S := y ≫ H.inclusion.hom.hom
  let v : Bˣ := c.hom.app S g
  have hv : v ^ p = 1 := (kernelPoint_iff p hK S _).1 ⟨y, rfl⟩
  refine hn ⟨v, hv, ?_⟩
  let π : S ⟶ R := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)
  have hh : mapPoints π g = a := by
    change (testSpec k).map π.op ≫ y ≫ H.inclusion.hom.hom = a
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ H.inclusion.hom.hom) hy).trans hx)
  have hnat := c.hom.naturality_apply π g
  change (c.hom.app R (mapPoints (X := (Gm p).X) π g) : Rˣ) =
    Units.map (Ideal.Quotient.mk I).toMonoidHom v at hnat
  exact (hnat.symm.trans (congrArg (c.hom.app R) hh)).trans ha

private theorem kernelPointsSubs (p : ℕ) [Fact p.Prime] {H : ClosedSubgroup (Gm p)}
    (hK : IsSchemeKernel (powerMap p) H) (L : Type) [Field L] [Algebra (BaseField p) L] :
    Subsingleton (Points H.group.X (CommAlgCat.of (BaseField p) L)) := by
  let k := BaseField p
  let R := CommAlgCat.of k L
  let : CharP k p := baseChar p
  let : CharP L p := CharP.of_ringHom_of_ne_zero (algebraMap k L) p
    (Fact.out : p.Prime).ne_zero
  have hj : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  have : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  have hroot (a : Points H.group.X R) :
      ((rankOnePoints p).hom.app R (a ≫ H.inclusion.hom.hom) : Lˣ) = 1 := by
    apply Units.ext
    apply frobenius_inj L p
    change ((rankOnePoints p).hom.app R (a ≫ H.inclusion.hom.hom) : Lˣ).val ^ p = (1 : L) ^ p
    have h := (kernelPoint_iff p hK R (a ≫ H.inclusion.hom.hom)).1 ⟨a, rfl⟩
    exact congrArg (fun u : Lˣ ↦ u.val) (h.trans (one_pow p).symm)
  refine ⟨fun a b ↦ (cancel_mono H.inclusion.hom.hom).mp ?_⟩
  apply (ConcreteCategory.bijective_of_isIso ((rankOnePoints p).hom.app R)).1
  exact (hroot a).trans (hroot b).symm

private theorem fibreProjectionEquation {k : Type} [Field k] {G : GroupScheme k}
    {H : ClosedSubgroup G} {q : G.X ⟶ G.X}
    (e : rightQuotientSheaf H ≅ schemeFppfSheaf G.X)
    (hq : rightQuotientProjection H ≫ e.hom = (fppfOver k).uliftYoneda.map q)
    {t : fieldBase k ⟶ G.X} {x : RationalPoints H}
    (hx : e.hom.hom.app (op (fieldBase k)) x = ULift.up t)
    {U : SchemeOver k} (g : U ⟶ G.X) :
    projectSection H g = (rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from U).op x ↔
      g ≫ q = Over.mkIdTerminal.from U ≫ t := by
  let f := e.hom.hom.app (op U)
  have hg : f (projectSection H g) = ULift.up (g ≫ q) :=
    congrArg (fun m ↦ m.hom.app (op U) (ULift.up g)) hq
  have hn : f ((rightQuotientSheaf H).obj.map (Over.mkIdTerminal.from U).op x) =
      ULift.up (Over.mkIdTerminal.from U ≫ t) :=
    (e.hom.hom.naturality_apply (Over.mkIdTerminal.from U).op x).trans
      (congrArg ((schemeFppfSheaf G.X).obj.map (Over.mkIdTerminal.from U).op) hx)
  constructor
  · intro h
    exact ULift.up.inj (hg.symm.trans ((congrArg f h).trans hn))
  · intro h
    exact (ConcreteCategory.bijective_of_isIso f).injective
      (hg.trans ((congrArg ULift.up h).trans hn.symm))

private theorem terminalSliceFrom {k : Type} [Field k] (U : Over (fieldBase k)) :
    (Over.mkIdTerminal.from U).left = Over.mkIdTerminal.from U.left :=
  Over.mkIdTerminal.hom_ext _ _

set_option maxHeartbeats 1500000 in
theorem powerQuotientObstruction : PowerQuotientObstruction := by
  intro p _
  let k := BaseField p
  let G := Gm p
  let c := rankOnePoints p
  let q := powerMap p
  obtain ⟨H, hK, hf, hs, hp, e, hq⟩ := powerQuotient p
  let R₀ := CommAlgCat.of k k
  let b := Units.mk0 (RatFunc.X : k) RatFunc.X_ne_zero
  let z : Points G.X R₀ := c.inv.app R₀ b
  let t : fieldBase k ⟶ G.X := (fieldTestIso k).hom ≫ z
  let x : RationalPoints H := e.inv.hom.app (op (fieldBase k)) (ULift.up t)
  have hx : e.hom.hom.app (op (fieldBase k)) x = ULift.up t :=
    congrArg (fun m ↦ m.hom.app (op (fieldBase k)) (ULift.up t)) e.inv_hom_id
  have hz : (c.hom.app R₀ z : kˣ) = b :=
    congrArg (fun m : GrpCat.of kˣ ⟶ GrpCat.of kˣ ↦ m b) (NatTrans.congr_app c.inv_hom_id R₀)
  have ht (R : TestAlgebra k) :
      (c.hom.app R (Over.mkIdTerminal.from ((testSpec k).obj (op R)) ≫ t) : Rˣ).val =
        algebraMap k R RatFunc.X := by
    let a : R₀ ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have hbase : (testSpec k).map a.op ≫ (fieldTestIso k).inv =
        Over.mkIdTerminal.from ((testSpec k).obj (op R)) :=
      Over.mkIdTerminal.hom_ext _ _
    have he : Over.mkIdTerminal.from ((testSpec k).obj (op R)) ≫ t = mapPoints a z := by
      rw [← hbase]
      simp [t, mapPoints]
    rw [he]
    have hn := c.hom.naturality_apply a z
    change (c.hom.app R (mapPoints a z) : Rˣ) =
      Units.map (algebraMap k R).toMonoidHom (c.hom.app R₀ z : kˣ) at hn
    exact (congrArg Units.val (hn.trans (congrArg (Units.map (algebraMap k R).toMonoidHom) hz)))
  have hfib {U : SchemeOver k} (g : U ⟶ G.X) :=
    fibreProjectionEquation e hq hx g
  have hfibR (R : TestAlgebra k) (g : Points G.X R) :
      projectSection H g = (rightQuotientSheaf H).obj.map
        (Over.mkIdTerminal.from ((testSpec k).obj (op R))).op x ↔
        ((c.hom.app R g : Rˣ).val) ^ p = algebraMap k R RatFunc.X := by
    rw [hfib]
    have hinj : Function.Injective (c.hom.app R) :=
      (ConcreteCategory.bijective_of_isIso (c.hom.app R)).injective
    constructor
    · intro h
      exact (congrArg Units.val ((rankOnePoints_power p R g).symm.trans
        (congrArg (c.hom.app R) h))).trans (ht R)
    · intro h
      apply hinj
      apply Units.ext
      exact (congrArg Units.val (rankOnePoints_power p R g)).trans (h.trans (ht R).symm)
  have hno : ¬ ∃ g : fieldBase k ⟶ G.X, g ≫ q.hom.hom = t := by
    rintro ⟨g, hg⟩
    let a := Over.mkIdTerminal.from ((testSpec k).obj (op R₀))
    have h := (hfibR R₀ (a ≫ g)).1 ((hfib (a ≫ g)).2 (by
      change (a ≫ g) ≫ q.hom.hom = a ≫ t
      rw [Category.assoc, hg]))
    exact noRationalRoot p (c.hom.app R₀ (a ≫ g) : kˣ).val h
  refine ⟨c, q, H, rankOnePoints_power p, hK, kernelPoint_iff p hK, kernelNotSmooth p hK,
    hf, hs, hp, e, hq, t, x,
    ht R₀, congrArg ULift.down hx, hfibR, hno, ?_, ?_, ?_⟩
  · let P := LinearAlgebraicGroups.TorsorObstruction.fibreTorsor H x
    refine ⟨P.2, ?_⟩
    intro hneutral
    obtain ⟨s⟩ := LinearAlgebraicGroups.Fppf.rationalPointCriterion
      (fieldGroupSectionsAreSheaf H.group) P |>.mp hneutral
    change FibreSection H x (fieldTest k) at s
    have hsec := s.property.trans (congrArg (fun a ↦ (rightQuotientSheaf H).obj.map a.op x)
      (terminalSliceFrom (fieldTest k)))
    have hlift := (hfib s.val.down).1 hsec
    have hterm : Over.mkIdTerminal.from (fieldTest k).left = 𝟙 _ :=
      Over.mkIdTerminal.hom_ext _ _
    exact hno ⟨s.val.down, hlift.trans
      ((congrArg (· ≫ t) hterm).trans (Category.id_comp _))⟩
  · let R := CommAlgCat.of k (SeparableClosure k)
    let U := Over.mk (Over.mkIdTerminal.from ((testSpec k).obj (op R)))
    refine ⟨fun s ↦ ?_⟩
    change FibreSection H x U at s
    have hsec := s.property.trans (congrArg (fun a ↦ (rightQuotientSheaf H).obj.map a.op x)
      (terminalSliceFrom U))
    have h := (hfibR R s.val.down).1 hsec
    exact noSeparableRoot p (SeparableClosure k) (c.hom.app R s.val.down : (SeparableClosure k)ˣ).val h
  · let h := kernelPointsSubs p hK (SeparableClosure k)
    intro cocycle
    exact funext fun σ ↦ h.elim (cocycle σ) 1

end

end LinearAlgebraicGroups.FrobeniusObstruction
