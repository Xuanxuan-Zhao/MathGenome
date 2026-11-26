import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.GrassmannianExample
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieLeftExact
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.PartialFlags
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Logic.Equiv.Fintype
import Mathlib.RingTheory.Localization.FractionRing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj BigOperators TensorProduct

universe u

namespace LinearAlgebraicGroups.Flag.GrassmannianExample

open _root_.LinearAlgebraicGroups.Specs
open Specs.GrassmannianExample

noncomputable section

set_option linter.style.haveILetI false

theorem blockExponentOrder : BlockExponentOrder := by
  classical
  intro n m ranks i j
  let cuts (l : Fin n) := Finset.univ.filter fun a : Fin m ↦ l.val < ranks a
  change ((cuts i).card : ℤ) < (cuts j).card ↔ _
  rw [Int.ofNat_lt]
  have hsub {l l' : Fin n} (h : l ≤ l') : cuts l' ⊆ cuts l := by
    intro a ha
    simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact lt_of_le_of_lt h ha
  constructor
  · intro h
    have hji : j ≤ i := le_of_not_ge fun hi ↦ (not_lt_of_ge (Finset.card_le_card (hsub hi))) h
    have hss : cuts i ⊂ cuts j :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub hji, fun he ↦ by rw [he] at h; exact (lt_irrefl _ h)⟩
    obtain ⟨a, haj, hai⟩ := Finset.exists_of_ssubset hss
    exact ⟨a, (Finset.mem_filter.mp haj).2, le_of_not_gt fun hlt ↦
      hai (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)⟩
  · rintro ⟨a, hj, hi⟩
    have hji : j ≤ i := (hj.trans_le hi).le
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub hji, ?_⟩
    intro he
    have hmem : a ∈ cuts j := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hj⟩
    rw [← he] at hmem
    exact (not_lt_of_ge hi) (Finset.mem_filter.mp hmem).2

theorem pivotRankOrder : PivotRankOrder := by
  intro d n I J
  constructor
  · intro h r
    by_contra! hr
    let j := (I r).val + 1
    have hI : Finset.Iic r ⊆ earlierPivots I j := by
      intro s hs
      have hsi : I s ≤ I r := I.monotone (Finset.mem_Iic.mp hs)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_succ_of_le hsi⟩
    have hJ : earlierPivots J j ⊆ Finset.Iio r := by
      intro s hs
      have hsj := (Finset.mem_filter.mp hs).2
      have hh : J s < J r := (Nat.lt_succ_iff.mp hsj).trans_lt hr
      exact Finset.mem_Iio.mpr (J.lt_iff_lt.mp hh)
    have hcI := Finset.card_le_card hI
    have hcJ := Finset.card_le_card hJ
    have hp := h j (I r).isLt
    change (earlierPivots I j).card ≤ (earlierPivots J j).card at hp
    simp at hcI hcJ
    omega
  · intro h j hj
    apply Finset.card_le_card
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Nat.lt_of_le_of_lt (h r) (Finset.mem_filter.mp hr).2⟩


theorem endpointPivots : EndpointPivots := by
  intro n
  constructor
  · intro I
    refine ⟨?_, fun j _ ↦ ?_⟩
    · ext r
      exact r.elim0
    · simp [pivotRank, earlierPivots]
  · intro I
    have hI : I = Fin.castLEOrderEmb (le_refl n) := by
      ext r
      exact congrArg Fin.val (I.strictMono.apply_eq (x := r))
    refine ⟨hI, ?_⟩
    subst I
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | heq
    · let r : Fin n := ⟨j, hlt⟩
      have he : earlierPivots (Fin.castLEOrderEmb (le_refl n)) j = Finset.Iio r := by
        ext t
        simp [earlierPivots, r, Fin.lt_def]
      rw [pivotRank, he, Fin.card_Iio]
    · subst j
      have he : earlierPivots (Fin.castLEOrderEmb (le_refl n)) n = Finset.univ := by
        ext t
        simp [earlierPivots]
      simp [pivotRank, he]

theorem echelonCoordinateCount : EchelonCoordinateCount := by
  intro d n I
  classical
  let fibre (r : Fin d) := {i : Fin n // i < I r ∧ i ∉ Set.range I}
  let e : EchelonVariable I ≃ Σ r, fibre r :=
    { toFun := fun x ↦ ⟨x.1.2, x.1.1, x.2⟩
      invFun := fun x ↦ ⟨(x.2.1, x.1), x.2.2⟩
      left_inv := by rintro ⟨⟨i, r⟩, h⟩; rfl
      right_inv := by rintro ⟨r, ⟨i, h⟩⟩; rfl }
  letI (r : Fin d) : Fintype (fibre r) :=
    inferInstanceAs (Fintype {i : Fin n // i < I r ∧ i ∉ Set.range I})
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  have hs : (Finset.Iio r).image I ⊆ Finset.Iio (I r) := by
    intro i hi
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Iio.mpr (I.strictMono (Finset.mem_Iio.mp hs))
  have hfilter : Finset.univ.filter (fun i => i < I r ∧ i ∉ Set.range I) =
      Finset.Iio (I r) \ (Finset.Iio r).image I := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_Iio,
      Finset.mem_image]
    refine and_congr_right (fun hi ↦ ⟨?_, ?_⟩)
    · rintro hi' ⟨s, _, hs'⟩
      exact hi' ⟨s, hs'⟩
    · rintro hi' ⟨s, rfl⟩
      exact hi' ⟨s, I.lt_iff_lt.mp hi, rfl⟩
  change Fintype.card {i : Fin n // i < I r ∧ i ∉ Set.range I} = _
  rw [Fintype.card_subtype, hfilter, Finset.card_sdiff_of_subset hs,
    Finset.card_image_of_injective _ I.injective, Fin.card_Iio, Fin.card_Iio]

open LaurentPolynomial in
private theorem monomial_hasPolynomialExtension {R : Type*} [CommRing R] (a : R) (e : ℤ) :
    (∃ p : Polynomial R, p.toLaurent = C a * T e) ↔ (e < 0 → a = 0) := by
  constructor
  · rintro ⟨p, hp⟩ he
    by_contra ha
    have hs := support_coeff_C_mul_T_of_ne_zero ha e
    rw [← hp, support_coeff_toLaurent] at hs
    have hmem : e ∈ p.support.map Nat.castEmbedding := by rw [hs]; simp
    obtain ⟨n, -, hn⟩ := Finset.mem_map.mp hmem
    have hnn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    exact (not_lt_of_ge (hn ▸ hnn)) he
  · intro h
    by_cases he : e < 0
    · exact ⟨0, by simp [h he]⟩
    · refine ⟨Polynomial.monomial e.toNat a, ?_⟩
      rw [Polynomial.toLaurent_C_mul_T, Int.toNat_of_nonneg (le_of_not_gt he)]


theorem laurentConjugate_entry : LaurentConjugateEntry.{u} := by
  intro J R _ _ _ w g i j
  change (((Matrix.diagonal (fun l ↦ LaurentPolynomial.T (w l)) :
    Matrix J J (LaurentPolynomial R)) * LaurentPolynomial.C.mapMatrix g.val) *
      Matrix.diagonal (fun l ↦ LaurentPolynomial.T (-w l)) : Matrix J J (LaurentPolynomial R)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, LaurentPolynomial.T_add]
  change _ * LaurentPolynomial.C (g i j) * _ = _
  ac_rfl

theorem laurentConjugate_hasPolynomialExtension : LaurentConjugateExtension.{u} := by
  intro J R _ _ _ w g
  classical
  let b := laurentDiagonal R w * Matrix.GeneralLinearGroup.map LaurentPolynomial.C g *
    (laurentDiagonal R w)⁻¹
  constructor
  · rintro ⟨f, hf⟩ i j h
    have hentry : (f i j).toLaurent =
        LaurentPolynomial.C (g i j) * LaurentPolynomial.T (w i - w j) := by
      rw [← laurentConjugate_entry w g, ← hf]
      rfl
    exact (monomial_hasPolynomialExtension (g i j) (w i - w j)).mp
      ⟨f i j, hentry⟩ (sub_neg.mpr h)
  · intro hz
    choose p hp using fun i j ↦
      (monomial_hasPolynomialExtension (g i j) (w i - w j)).mpr
        (fun hn ↦ hz i j (sub_neg.mp hn))
    let A : Matrix J J (Polynomial R) := Matrix.of p
    have hA : Polynomial.toLaurent.mapMatrix A = b.val := by
      apply Matrix.ext
      intro i j
      exact (hp i j).trans (laurentConjugate_entry w g i j).symm
    have hdet : A.det = Polynomial.C g.val.det := by
      apply Polynomial.toLaurent_injective
      rw [RingHom.map_det, hA, Polynomial.toLaurent_C]
      change (Matrix.GeneralLinearGroup.det b).val = _
      simp only [b, map_mul, map_inv, mul_inv_cancel_comm]
      exact (LaurentPolynomial.C.map_det g.val).symm
    refine ⟨Matrix.GeneralLinearGroup.mk'' A ?_, ?_⟩
    · rw [hdet]
      exact (Matrix.GeneralLinearGroup.det g).isUnit.map Polynomial.C
    · exact Units.ext hA


open CocharacterDynamics in
theorem limitGroupMatrixEquations : LimitGroupMatrixEquations.{u} := by
  intro k J _ _ _ G E c w hc D R g
  have hnat {S T : TestAlgebra k} (a : S ⟶ T) (p : Points G.X S) :
      E.hom.app T (mapPoints a p) =
        Matrix.GeneralLinearGroup.map a.hom.toRingHom (E.hom.app S p) :=
    E.hom.naturality_apply a p
  have hconst : (laurentConstants R).hom.toRingHom = LaurentPolynomial.C := by
    ext r
    rfl
  have hpoly : (polynomialToLaurent R).hom.toRingHom = Polynomial.toLaurent := rfl
  have horbit : E.hom.app (laurentAlgebra R) (orbit c g) =
      laurentConjugate w (E.hom.app R g) := by
    unfold orbit laurentConjugate
    rw [map_mul, map_mul, map_inv, hc R, hnat, hconst]
    rfl
  change (∃ p : AdjointRepresentation.GroupPoints D.parabolic.group R,
    ((groupPointsFunctor k).map D.parabolic.inclusion).app R p = g) ↔ _
  refine (D.parabolic_points R g).symm.trans
    (?_ : HasExtension c g ↔ _)
  refine Iff.trans ?_ (laurentConjugate_hasPolynomialExtension w (E.hom.app R g))
  constructor
  · rintro ⟨z, f, hf, hz⟩
    refine ⟨E.hom.app (polynomialAlgebra R) f, ?_⟩
    rw [← hpoly, ← hnat (polynomialToLaurent R) f, hf, horbit]
  · rintro ⟨F, hF⟩
    let f : Points G.X (polynomialAlgebra R) := E.inv.app (polynomialAlgebra R) F
    have hf : E.hom.app (polynomialAlgebra R) f = F :=
      congrArg (fun a ↦ a.app (polynomialAlgebra R) F) E.inv_hom_id
    refine ⟨mapPoints (polynomialEvaluate R 0) f, f, ?_, rfl⟩
    apply (ConcreteCategory.bijective_of_isIso (E.hom.app (laurentAlgebra R))).1
    rw [hnat (polynomialToLaurent R) f, hpoly, hf, hF, horbit]

theorem blockLimitEquations : BlockLimitEquations.{u} := by
  intro k _ n m G E ranks c hc D R g
  let w (i : ULift.{u} (Fin n)) := blockExponent ranks i.down
  refine (limitGroupMatrixEquations E c w hc D R g).trans ?_
  constructor
  · intro h a i j hj hi
    exact h i j ((blockExponentOrder ranks i.down j.down).mpr ⟨a, hj, hi⟩)
  · intro h i j hlt
    obtain ⟨a, hj, hi⟩ := (blockExponentOrder ranks i.down j.down).mp hlt
    exact h a i j hj hi

open private comp_toBasePoint hom_toBase_eq orbit_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagSchemes
open private compareRepresentatives compareRepresentatives_projection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private representedProjection_apply subgroupSections_of_affine
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

variable {k : Type u} [Field k] {G : GroupScheme k} {Y : SchemeOver k}

private theorem comp_orbitMap {T : SchemeOver k} (g : T ⟶ G.X)
    (action : G.X ⨯ Y ⟶ Y) (z : Points Y (CommAlgCat.of k k)) :
    g ≫ orbitMap action z = prod.lift g (FlagSchemes.toBasePoint T ≫ z) ≫ action := by
  exact orbit_apply action z g

private theorem orbitMap_localLifts (q : G.X ⟶ Y)
    (localLifts : ∀ (T : SchemeOver k) (p : T ⟶ Y) (x : T.left),
      ∃ (R : TestAlgebra k) (a : Points T R) (g : Points G.X R),
        IsOpenImmersion a.left ∧ x ∈ Set.range a.left ∧ g ≫ q = a ≫ p) :
    Presheaf.IsLocallySurjective (fppfOver k) ((fppfOver k).uliftYoneda.{u + 1, u, u + 1}.map q).hom := by
  classical
  constructor
  intro T z
  choose R a g ha hx hg using localLifts T z.down
  apply (fppfOver k).superset_covering (S := Sieve.ofArrows _ a)
  · intro U f hf
    rcases hf with ⟨W, l, r, ⟨x⟩, rfl⟩
    refine ⟨ULift.up (l ≫ g x), ?_⟩
    apply congrArg ULift.up
    change (l ≫ g x) ≫ q = (l ≫ a x) ≫ z.down
    rw [Category.assoc, Category.assoc, hg]
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    apply Precoverage.generate_mem_toGrothendieck
    apply Scheme.zariskiPrecoverage_le_fppfPrecoverage
    exact (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ⟨x, hx x⟩, ha⟩

set_option backward.isDefEq.respectTransparency false in
private theorem orbitMap_representsQuotient (H : ClosedSubgroup G) (q : G.X ⟶ Y)
    (hlocal : Presheaf.IsLocallySurjective (fppfOver k) ((fppfOver k).uliftYoneda.{u + 1, u, u + 1}.map q).hom)
    (hfibres : ∀ (T : SchemeOver k) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ SubgroupSections H T) :
    ∃ e : rightQuotientSheaf H ≅ schemeFppfSheaf Y,
      rightQuotientProjection H ≫ e.hom = (fppfOver k).uliftYoneda.{u + 1, u, u + 1}.map q := by
  let p : rightCosetPresheaf H ⟶ (schemeFppfSheaf Y).obj :=
    { app T := ↾fun x ↦ Quotient.lift (fun g ↦ ULift.up (g ≫ q))
        (fun g h he ↦ congrArg ULift.up ((hfibres T.unop g h).2 (QuotientGroup.leftRel_apply.mp he)))
        x.down
      naturality := by
        intro T U f
        ext ⟨x⟩
        induction x using QuotientGroup.induction_on with
        | H g => exact congrArg ULift.up (Category.assoc f.unop g q) }
  have hp : rightCosetProjection H ≫ p = ((fppfOver k).uliftYoneda.{u + 1, u, u + 1}.map q).hom := by
    ext T ⟨g⟩
    rfl
  letI := hlocal
  letI : Presheaf.IsLocallySurjective (fppfOver k) p :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (fppfOver k) hp
  letI : Presheaf.IsLocallyInjective (fppfOver k) p := by
    apply Presheaf.isLocallyInjective_of_injective
    rintro T ⟨a⟩ ⟨b⟩
    induction a using QuotientGroup.induction_on with
    | H g =>
      induction b using QuotientGroup.induction_on with
      | H h =>
        intro he
        exact congrArg ULift.up (QuotientGroup.eq.mpr ((hfibres T.unop g h).1 (ULift.up.inj he)))
  let f : rightQuotientSheaf H ⟶ schemeFppfSheaf Y :=
    ⟨sheafifyLift (fppfOver k) p (schemeFppfSheaf Y).property⟩
  have hf : toSheafify (fppfOver k) (rightCosetPresheaf H) ≫ f.hom = p :=
    toSheafify_sheafifyLift _ _ _
  haveI : Sheaf.IsLocallySurjective f :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hf
  haveI : Sheaf.IsLocallyInjective f :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ p hf
  haveI : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).mp ⟨inferInstance, inferInstance⟩
  refine ⟨asIso f, ?_⟩
  apply (sheafToPresheaf _ _).map_injective
  change (rightCosetProjection H ≫ toSheafify (fppfOver k) _) ≫ f.hom = _
  rw [Category.assoc, hf, hp]
  rfl

private theorem orbitMap_fibres (H : ClosedSubgroup G)
    (action : G.X ⨯ Y ⟶ Y) (z : Points Y (CommAlgCat.of k k))
    (hone : ∀ (T : SchemeOver k) (p : T ⟶ Y), prod.lift (1 : T ⟶ G.X) p ≫ action = p)
    (hmul : ∀ (T : SchemeOver k) (g h : T ⟶ G.X) (p : T ⟶ Y),
      prod.lift (g * h) p ≫ action = prod.lift g (prod.lift h p ≫ action) ≫ action)
    (hfix : ∀ (T : SchemeOver k) (g : T ⟶ G.X),
      g ≫ orbitMap action z = FlagSchemes.toBasePoint T ≫ z ↔ g ∈ SubgroupSections H T)
    (T : SchemeOver k) (g h : T ⟶ G.X) :
    g ≫ orbitMap action z = h ≫ orbitMap action z ↔ g⁻¹ * h ∈ SubgroupSections H T := by
  rw [← hfix, comp_orbitMap, comp_orbitMap, comp_orbitMap, hmul]
  let p := FlagSchemes.toBasePoint T ≫ z
  change prod.lift g p ≫ action = prod.lift h p ≫ action ↔
    prod.lift g⁻¹ (prod.lift h p ≫ action) ≫ action = p
  constructor
  · intro hp
    rw [← hp, ← hmul, inv_mul_cancel, hone]
  · intro hp
    calc
      prod.lift g p ≫ action =
          prod.lift g (prod.lift g⁻¹ (prod.lift h p ≫ action) ≫ action) ≫ action :=
        congrArg (fun t ↦ prod.lift g t ≫ action) hp.symm
      _ = prod.lift (g * g⁻¹) (prod.lift h p ≫ action) ≫ action :=
        (hmul T g g⁻¹ _).symm
      _ = prod.lift h p ≫ action := by rw [mul_inv_cancel, hone]

open private actOnSection_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.RightQuotientSheaf

set_option backward.isDefEq.respectTransparency false in
private theorem quotientComparison_action {H : ClosedSubgroup G}
    (Q : QuotientEmbedding.Presentation H) (e : Q.scheme ≅ Y)
    (action : G.X ⨯ Y ⟶ Y) (z : Points Y (CommAlgCat.of k k))
    (he : Q.projection ≫ e.hom = orbitMap action z)
    (hmul : ∀ (T : SchemeOver k) (g h : T ⟶ G.X) (p : T ⟶ Y),
      prod.lift (g * h) p ≫ action = prod.lift g (prod.lift h p ≫ action) ≫ action)
    (T : SchemeOver k) (g : T ⟶ G.X) (x : T ⟶ Q.scheme) :
    Q.quotientIso.hom.hom.app (op T)
      (actOnSection H g (Q.quotientIso.inv.hom.app (op T) (ULift.up x))) =
      ULift.up ((prod.lift g (x ≫ e.hom) ≫ action) ≫ e.inv) := by
  let y := Q.quotientIso.inv.hom.app (op T) (ULift.up x)
  have hy : Q.quotientIso.hom.hom.app (op T) y = ULift.up x :=
    congrArg (fun f ↦ f.hom.app (op T) (ULift.up x)) Q.quotientIso.inv_hom_id
  haveI := rightQuotientLocalLifts H
  let S := Presheaf.imageSieve (rightQuotientProjection H).hom y
  have hS : S ∈ fppfOver k T := Presheaf.imageSieve_mem _ _ _
  apply ((schemeFppfSheaf Q.scheme).property.isSheafFor S hS).isSeparatedFor.ext
  intro U f hf
  obtain ⟨⟨h⟩, hh⟩ := hf
  change projectSection H h = (rightQuotientSheaf H).obj.map f.op y at hh
  have natural (v : (rightQuotientSheaf H).obj.obj (op T)) :
      (schemeFppfSheaf Q.scheme).obj.map f.op (Q.quotientIso.hom.hom.app (op T) v) =
        Q.quotientIso.hom.hom.app (op U) ((rightQuotientSheaf H).obj.map f.op v) :=
    (Q.quotientIso.hom.hom.naturality_apply f.op v).symm
  have hq : h ≫ Q.projection = f ≫ x := by
    have hres := congrArg ((schemeFppfSheaf Q.scheme).obj.map f.op) hy
    rw [natural, ← hh, representedProjection_apply] at hres
    exact ULift.up.inj hres
  change (schemeFppfSheaf Q.scheme).obj.map f.op
    (Q.quotientIso.hom.hom.app (op T) (actOnSection H g y)) =
    ULift.up (f ≫ (prod.lift g (x ≫ e.hom) ≫ action) ≫ e.inv)
  rw [natural, actOnSection_naturality, ← hh, rightQuotientActionOnLifts,
    representedProjection_apply]
  apply congrArg ULift.up
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, he, comp_orbitMap,
    hmul, prod.comp_lift_assoc]
  have hOrb : prod.lift h (FlagSchemes.toBasePoint U ≫ z) ≫ action = f ≫ x ≫ e.hom := by
    rw [← comp_orbitMap, ← he, ← Category.assoc h, hq, Category.assoc]
  rw [hOrb]

private theorem coordinateOrbitLocalLifts
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n m : ℕ} (β : Module.Basis (Fin n) k V) (ranks : Fin m → ℕ)
    (P : ∀ i : Fin m, PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) (ranks i))
    (D : FlagIncidence.Presentation ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (A : FlagIncidence.Action ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) D.inclusion G E)
    (S : FlagSchemes.CoordinateStabilizer β ranks P D G E A)
    (hlocal : FlagIncidence.HasLocalTransitivity ranks (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) D.inclusion G E A) :
    Presheaf.IsLocallySurjective (fppfOver k)
      ((fppfOver k).uliftYoneda.{u + 1, u, u + 1}.map (orbitMap A.onFlags S.point)).hom := by
  obtain ⟨z, hz, hlocal⟩ := hlocal n β
  have hpoint : z = S.point := by
    letI : IsClosedImmersion D.inclusion.left := D.closed
    letI : Mono D.inclusion := Over.mono_of_mono_left D.inclusion
    apply (cancel_mono D.inclusion).mp
    apply Pi.hom_ext
    intro i
    apply (ConcreteCategory.bijective_of_isIso ((P i).charts.affinePoints.hom.app _)).1
    apply Module.Grassmannian.ext
    exact (hz i).trans (S.point_formula i).symm
  subst z
  apply orbitMap_localLifts _
  intro T p x
  obtain ⟨R, a, g, ha, hx, hg⟩ := hlocal T p x
  refine ⟨R, a, g, ha, hx, ?_⟩
  let baseMap : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have hbase : (testSpec k).map baseMap.op =
      FlagSchemes.toBasePoint ((testSpec k).obj (op R)) := hom_toBase_eq _
  rw [comp_orbitMap]
  change prod.lift g ((testSpec k).map baseMap.op ≫ S.point) ≫ A.onFlags = _ at hg
  rwa [hbase] at hg

set_option maxHeartbeats 800000 in
theorem coordinateFlagQuotient : CoordinateFlagQuotient.{u} := by
  intro k V _ _ _ _ n m β ranks P D G E A S hlocal
  let q := orbitMap A.onFlags S.point
  let j := FlagSchemes.coordinateFlagInclusion k (ULift.{u} (Fin n))
    (FlagSchemes.prefixCuts ranks) ≫ S.matrixIso.hom
  obtain ⟨L, f, t, ht⟩ := S.subgroup
  have hj : IsClosedImmersion j.left := S.closed
  have hclosed : IsClosedImmersion f.hom.hom.left := by
    rw [ht, ← Category.assoc]
    letI : IsClosedImmersion j.left := hj
    change IsClosedImmersion (t.hom.left ≫ j.left)
    infer_instance
  let H : ClosedSubgroup G := ⟨L, f, hclosed⟩
  have hfactor {T : SchemeOver k} (g : T ⟶ G.X) :
      g ∈ SubgroupSections H T ↔ ∃ a, a ≫ j = g := by
    change (∃ a : T ⟶ L.X, a ≫ f.hom.hom = g) ↔ _
    rw [ht, ← Category.assoc]
    exact ⟨fun ⟨a, ha⟩ ↦ ⟨a ≫ t.hom, by rwa [Category.assoc]⟩,
      fun ⟨a, ha⟩ ↦ ⟨a ≫ t.inv, by simpa only [Category.assoc, Iso.inv_hom_id_assoc] using ha⟩⟩
  have hfix (T : SchemeOver k) (g : T ⟶ G.X) :
      g ≫ q = FlagSchemes.toBasePoint T ≫ S.point ↔ g ∈ SubgroupSections H T := by
    rw [hfactor]
    constructor
    · intro h
      exact ⟨S.stabilizer_pullback.lift g (FlagSchemes.toBasePoint T) h,
        S.stabilizer_pullback.lift_fst _ _ _⟩
    · rintro ⟨a, rfl⟩
      have hcomm : j ≫ q = FlagSchemes.toBasePoint _ ≫ S.point := S.stabilizer_pullback.w
      rw [Category.assoc, hcomm, ← Category.assoc, comp_toBasePoint]
  let L₀ := StandardGroups.generalLinearGroup k (ULift.{u} (Fin n))
  let e₀ : L₀.val.X ≅ G.X := S.matrixIso
  letI : IsIso e₀.inv.left := ((Over.forget _).mapIso e₀).symm.isIso_hom
  letI : IsAffine L₀.val.X.left := L₀.property.1
  letI : LocallyOfFiniteType L₀.val.X.hom := L₀.property.2.1
  letI : QuasiCompact L₀.val.X.hom := L₀.property.2.2
  have hAff : IsAffine G.X.left := isAffine_of_isAffineHom e₀.inv.left
  have hFt : LocallyOfFiniteType G.X.hom := by
    rw [← Over.w e₀.inv]
    infer_instance
  have hQc : QuasiCompact G.X.hom := by
    rw [← Over.w e₀.inv]
    infer_instance
  let G₀ : AffineAlgebraicGroup k := ⟨G, hAff, hFt, hQc⟩
  refine ⟨H, (_root_.LinearAlgebraicGroups.HomogeneousQuotient.homogeneousQuotient k G₀ H).1, fun T g ↦ (hfix T g).symm,
    fun R g ↦ (hfactor g).trans (S.equations R g), ?_⟩
  have hloc := coordinateOrbitLocalLifts β ranks P D E A S hlocal
  obtain ⟨f, hf⟩ :=
    orbitMap_representsQuotient H q hloc (orbitMap_fibres H A.onFlags S.point A.one A.mul hfix)
  intro Q
  exact ⟨compareRepresentatives Q f, compareRepresentatives_projection Q q f hf,
    quotientComparison_action Q _ A.onFlags S.point
      (compareRepresentatives_projection Q q f hf) A.mul⟩

theorem coordinateFlagQuotientExists : CoordinateFlagQuotientExists.{u} := by
  intro k V _ _ _ _ n β m ranks hmono hr
  obtain ⟨P, D, G, E, A, _, _, _, hlocal, _, ⟨S⟩⟩ :=
    LinearAlgebraicGroups.FlagSchemes.flagSchemeGeometry k V n β m ranks hmono hr
  obtain ⟨H, hH⟩ := coordinateFlagQuotient β ranks P D G E A S hlocal
  exact ⟨P, D, G, E, A, S, H, hH⟩

open CocharacterDynamics
open DiagonalizableGroups (IntegerCharacters groupAlgebra)
open private unitEquiv unitEquiv_unitPoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private def diagonalUnitsHom (J R : Type u) [Fintype J] [DecidableEq J] [CommRing R] :
    (J → Rˣ) →* Matrix.GeneralLinearGroup J R :=
  (Units.map (Matrix.diagonalRingHom J R).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : J ↦ R)).symm.toMonoidHom

private def diagonalPowerPoints {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
    (w : J → ℤ) :
    (groupPointsFunctor k).obj (specGroup (groupAlgebra k IntegerCharacters)) ⟶
      StandardGroups.generalLinearPoints k J where
  app R := GrpCat.ofHom <| (diagonalUnitsHom J R).comp <|
    (MonoidHom.pi fun i ↦ zpowGroupHom (α := Rˣ) (w i)).comp (unitEquiv R).toMonoidHom
  naturality R S a := by
    apply GrpCat.ext
    intro x
    symm
    have hx : x = unitPoint R (unitEquiv R x) :=
      (unitEquiv R).injective (unitEquiv_unitPoint R _).symm
    change Matrix.GeneralLinearGroup.map a.hom.toRingHom
      (diagonalUnitsHom J R (fun i ↦ (unitEquiv R x) ^ w i)) =
      diagonalUnitsHom J S (fun i ↦ (unitEquiv S (mapPoints a x)) ^ w i)
    have h : unitEquiv S (mapPoints a x) = Units.map a.hom.toMonoidHom (unitEquiv R x) := by
      conv_lhs => rw [hx, mapPoints_unitPoint, unitEquiv_unitPoint]
    rw [h]
    apply Units.ext
    change (Matrix.diagonal (fun i ↦ ((unitEquiv R x ^ w i : Rˣ) : R))).map a.hom =
      Matrix.diagonal (fun i ↦ (((Units.map a.hom.toMonoidHom (unitEquiv R x)) ^ w i : Sˣ) : S))
    simp only [Matrix.diagonal_map (map_zero a.hom), ← map_zpow (Units.map a.hom.toMonoidHom)]
    rfl

theorem diagonalCocharacterExists : DiagonalCocharacterExists.{u} := by
  intro k J _ _ _ G E w
  let M := specGroup (groupAlgebra k IntegerCharacters)
  have haff : IsAffine M.X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters))))
  let e := _root_.LinearAlgebraicGroups.groupHomEquiv M G haff
  let f := diagonalPowerPoints (k := k) w
  let c := e.symm (f ≫ E.inv)
  have hc : (groupPointsFunctor k).map c = f ≫ E.inv := e.apply_symm_apply _
  refine ⟨c, fun R t ↦ ?_⟩
  have he : (groupPointsFunctor k).map c ≫ E.hom = f := by
    rw [hc, Category.assoc, E.inv_hom_id, Category.comp_id]
  have ht := congrArg (fun z ↦ z.app R (unitPoint R t)) he
  change E.hom.app R (cocharacterPoint c R t) = _ at ht
  rw [ht]
  change Matrix.diagonal (fun i ↦ ((unitEquiv R (unitPoint R t) ^ w i : Rˣ) : R)) = _
  rw [unitEquiv_unitPoint]

private theorem laurentParameter_zpow {k : Type u} [Field k] (R : TestAlgebra k) (z : ℤ) :
    ((laurentParameter R ^ z : (laurentAlgebra R)ˣ) : LaurentPolynomial R) =
      LaurentPolynomial.T z := by
  have h1 : ∀ m : ℕ, (LaurentPolynomial.T (R := R) 1) ^ m = LaurentPolynomial.T (m : ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, ← LaurentPolynomial.T_add, Nat.cast_succ]
  have h2 : ∀ m : ℕ, (LaurentPolynomial.T (R := R) (-1)) ^ m =
      LaurentPolynomial.T (-(m : ℤ)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, ← LaurentPolynomial.T_add, Nat.cast_succ, neg_add]
  cases z with
  | ofNat m =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
      exact h1 m
  | negSucc m =>
      rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      exact h2 (m + 1)

theorem blockParabolicExists : BlockParabolicExists.{u} := by
  intro k _ n m G E ranks
  obtain ⟨c, hc⟩ := diagonalCocharacterExists E (fun i ↦ blockExponent ranks i.down)
  obtain ⟨D⟩ := LinearAlgebraicGroups.CocharacterDynamics.existsLimitDecomposition G c
  refine ⟨c, D, hc, blockLimitEquations E ranks c (fun R ↦ ?_) D⟩
  apply Units.ext
  rw [hc]
  exact congrArg Matrix.diagonal (funext fun i ↦ laurentParameter_zpow R _)

theorem dynamicCoordinateFlagQuotient : DynamicCoordinateFlagQuotient.{u} := by
  intro k V _ _ _ _ n m β ranks P D G E A S hlocal
  obtain ⟨H, _, hfix, heq, _⟩ := coordinateFlagQuotient β ranks P D G.val E A S hlocal
  obtain ⟨c, L, hc, hL⟩ := blockParabolicExists G E ranks
  have hs := subgroupSections_of_affine G.property.1 (A := L.parabolic) (B := H)
    (fun R g ↦ (hL R g).trans (heq R g).symm)
  let q := orbitMap A.onFlags S.point
  have hstab (T : SchemeOver k) (g : T ⟶ G.val.X) :
      g ∈ SubgroupSections L.parabolic T ↔ g ≫ q = FlagSchemes.toBasePoint T ≫ S.point :=
    (hs T g).trans (hfix T g)
  refine ⟨c, L, hc, (LinearAlgebraicGroups.HomogeneousQuotient.homogeneousQuotient k G
    L.parabolic).1, hstab, hL, ?_⟩
  have hloc := coordinateOrbitLocalLifts β ranks P D E A S hlocal
  obtain ⟨f, hf⟩ := orbitMap_representsQuotient L.parabolic q hloc
    (orbitMap_fibres L.parabolic A.onFlags S.point A.one A.mul (fun T g ↦ (hstab T g).symm))
  intro Q
  exact ⟨compareRepresentatives Q f, compareRepresentatives_projection Q q f hf,
    quotientComparison_action Q _ A.onFlags S.point
      (compareRepresentatives_projection Q q f hf) A.mul⟩


open private liftPointGroupHom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

theorem diagonalCocharacterInTorus : DiagonalCocharacterInTorus.{u} := by
  intro k J _ _ _ G E T hT w
  let M := specGroup (groupAlgebra k IntegerCharacters)
  have haff : IsAffine M.X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters))))
  let f := diagonalPowerPoints (k := k) w
  let a : (groupPointsFunctor k).obj M ⟶ (groupPointsFunctor k).obj G := f ≫ E.inv
  have hdiag (R : TestAlgebra k) (p : Points M.X R) :
      E.hom.app R (a.app R p) = f.app R p :=
    (E.app R).groupIsoToMulEquiv.apply_symm_apply _
  obtain ⟨c, hc⟩ := liftPointGroupHom haff T a (fun R p ↦ by
    apply (hT R (a.app R p)).mpr
    intro i j hij
    refine (congrArg (fun x : Matrix.GeneralLinearGroup J R ↦ x.val i j) (hdiag R p)).trans ?_
    change (Matrix.diagonal (fun l ↦ ((unitEquiv R p ^ w l : Rˣ) : R))) i j = 0
    exact Matrix.diagonal_apply_ne _ hij)
  refine ⟨c, fun R t ↦ ?_⟩
  have he := congrArg (fun z ↦ E.hom.app R (z.app R (unitPoint R t))) hc
  change E.hom.app R (cocharacterPoint (c ≫ T.inclusion) R t) = E.hom.app R (a.app R (unitPoint R t)) at he
  refine (congrArg (fun x : Matrix.GeneralLinearGroup J R ↦ x.val)
    (he.trans (hdiag R (unitPoint R t)))).trans ?_
  change Matrix.diagonal (fun i ↦ ((unitEquiv R (unitPoint R t) ^ w i : Rˣ) : R)) = _
  rw [unitEquiv_unitPoint]


private theorem eq_diagonal_of_entries_zero {J S : Type u} [DecidableEq J] [Zero S]
    {A : Matrix J J S} (ha : ∀ i j, i ≠ j → A i j = 0) :
    A = Matrix.diagonal (fun i ↦ A i i) := by
  ext i j
  by_cases h : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
  · rw [ha i j h, Matrix.diagonal_apply_ne _ h]

private def diagonalEntryUnit {J S : Type u} [Fintype J] [DecidableEq J] [CommRing S]
    (g : Matrix.GeneralLinearGroup J S)
    (hg : g.val = Matrix.diagonal (fun i ↦ g.val i i)) (i : J) : Sˣ where
  val := g.val i i
  inv := g.inv i i
  val_inv := by
    have h := congrArg (fun M : Matrix J J S ↦ M i i) g.val_inv
    have he := congrArg (fun M : Matrix J J S ↦ (M * g.inv) i i) hg
    exact (Matrix.diagonal_mul _ _ _ _).symm.trans
      (he.symm.trans (h.trans (Matrix.one_apply_eq _)))
  inv_val := by
    have h := congrArg (fun M : Matrix J J S ↦ M i i) g.inv_val
    have he := congrArg (fun M : Matrix J J S ↦ (g.inv * M) i i) hg
    exact (Matrix.mul_diagonal (fun j ↦ g.val j j) g.inv i i).symm.trans
      (he.symm.trans (h.trans (Matrix.one_apply_eq _)))

open private pointHom_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

set_option backward.isDefEq.respectTransparency false in
theorem diagonalTorusCoordinates : DiagonalTorusCoordinates.{u} := by
  intro k J _ _ _ G E T hT
  let D := (groupPointsFunctor k).map T.inclusion ≫ E.hom
  have hd (R : TestAlgebra k) (t : Points T.group.X R) :
      (D.app R t : Matrix.GeneralLinearGroup J R).val =
        Matrix.diagonal (fun i ↦ (D.app R t : Matrix.GeneralLinearGroup J R).val i i) :=
    eq_diagonal_of_entries_zero ((hT R (t ≫ T.inclusion.hom.hom)).mp ⟨t, rfl⟩)
  let Fapp (R : TestAlgebra k) : AdjointRepresentation.GroupPoints T.group R →* (J → Rˣ) :=
    MonoidHom.pi fun i ↦ {
      toFun := fun t ↦ diagonalEntryUnit (D.app R t) (hd R t) i
      map_one' := Units.ext (by
        change (D.app R (1 : AdjointRepresentation.GroupPoints T.group R) :
          Matrix.GeneralLinearGroup J R).val i i = 1
        rw [map_one]
        exact Matrix.one_apply_eq _)
      map_mul' := fun x y ↦ Units.ext (by
        change ((D.app R).hom (x * y) : Matrix.GeneralLinearGroup J R).val i i = _
        rw [map_mul]
        change (((D.app R x : Matrix.GeneralLinearGroup J R).val) *
          ((D.app R y : Matrix.GeneralLinearGroup J R).val)) i i = _
        exact (congrArg (fun M : Matrix J J R ↦ (M * (D.app R y :
          Matrix.GeneralLinearGroup J R).val) i i) (hd R x)).trans (Matrix.diagonal_mul _ _ _ _)) }
  let F : (groupPointsFunctor k).obj T.group ⟶ StandardGroups.multiplicativePowerPoints k J :=
    { app R := GrpCat.ofHom (Fapp R)
      naturality R S a := by
        apply GrpCat.ext
        intro t
        funext i
        apply Units.ext
        exact congrArg (fun v : Matrix.GeneralLinearGroup J S ↦ v.val i i)
          (D.naturality_apply a t) }
  have hf (R : TestAlgebra k) (t : Points T.group.X R) :
      (D.app R t : Matrix.GeneralLinearGroup J R).val =
        Matrix.diagonal (fun i ↦ ((F.app R t : J → Rˣ) i : R)) :=
    hd R t
  letI (R : TestAlgebra k) : IsIso (F.app R) := by
    apply (ConcreteCategory.isIso_iff_bijective (F.app R)).mpr
    constructor
    · intro x y h
      have hm : (D.app R x : Matrix.GeneralLinearGroup J R) = D.app R y := by
        apply Units.ext
        rw [hf, hf, h]
      exact pointHom_injective T R ((E.app R).groupIsoToMulEquiv.injective hm)
    · intro a
      let g := E.inv.app R (diagonalUnitsHom J R a)
      have hg : E.hom.app R g = diagonalUnitsHom J R a :=
        (E.app R).groupIsoToMulEquiv.apply_symm_apply _
      obtain ⟨t, ht⟩ := (hT R g).mpr (fun i j hij ↦ by
        rw [hg]
        exact Matrix.diagonal_apply_ne _ hij)
      refine ⟨t, ?_⟩
      funext i
      apply Units.ext
      have he : (D.app R t : Matrix.GeneralLinearGroup J R) = diagonalUnitsHom J R a := by
        change E.hom.app R (t ≫ T.inclusion.hom.hom) = _
        change (t : Points T.group.X R) ≫ T.inclusion.hom.hom = g at ht
        exact (congrArg (fun z : Points G.X R ↦ E.hom.app R z) ht).trans hg
      change (D.app R t : Matrix.GeneralLinearGroup J R).val i i = _
      rw [he]
      exact Matrix.diagonal_apply_eq _ _
  letI := NatIso.isIso_of_isIso_app F
  exact ⟨asIso F, hf⟩


open private unitPointHom unitPointHom_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private def diagonalCoordinateProjection (k : Type u) [Field k] {J : Type u} (i : J) :
    StandardGroups.multiplicativePowerPoints k J ⟶
      (groupPointsFunctor k).obj (specGroup (groupAlgebra k IntegerCharacters)) where
  app R := GrpCat.ofHom ((unitPointHom R).comp (Pi.evalMonoidHom (fun _ : J ↦ Rˣ) i))
  naturality R S a := by
    apply GrpCat.ext
    intro t
    change unitPointHom S (Units.map a.hom.toMonoidHom (t i)) =
      mapPoints a (unitPointHom R (t i))
    simp only [unitPointHom_apply]
    exact (mapPoints_unitPoint a (t i)).symm

theorem diagonalCoordinateCharacters : DiagonalCoordinateCharacters.{u} := by
  intro k J _ _ _ G E T hG hT
  obtain ⟨e, he⟩ := diagonalTorusCoordinates E T hT
  let M : GroupScheme k := specGroup (groupAlgebra k IntegerCharacters)
  have hAff : IsAffine T.group.X.left := by
    letI := hG
    letI := T.isClosedImmersion
    exact isAffine_of_isAffineHom T.inclusion.hom.hom.left
  let compEquiv := LinearAlgebraicGroups.groupHomEquiv T.group M hAff
  let χ (i : J) : CharacterDescent.Character T.group :=
    compEquiv.symm (e.hom ≫ diagonalCoordinateProjection k i)
  refine ⟨e, χ, he, fun R t i ↦ ?_⟩
  have h := congrArg (fun α ↦ α.app R t)
    (compEquiv.apply_symm_apply (e.hom ≫ diagonalCoordinateProjection k i))
  change t ≫ (χ i).hom.hom = unitPointHom R ((e.hom.app R t : J → Rˣ) i) at h
  exact h.trans (unitPointHom_apply R _)

section EchelonCells

open _root_.LinearAlgebraicGroups.Specs.GrassmannianCharts

variable {d n : ℕ}

private theorem mem_pivotSet (I : Fin d ↪o Fin n) (i : ULift.{u} (Fin n)) :
    i ∈ (pivotSet.{u} I).val ↔ i.down ∈ Set.range I := by
  constructor
  · intro hi
    obtain ⟨r, -, hr⟩ := Finset.mem_map.mp hi
    exact ⟨r, congrArg ULift.down hr⟩
  · rintro ⟨r, hr⟩
    exact Finset.mem_map.mpr ⟨r, Finset.mem_univ _, ULift.ext hr⟩

private def pivotColumn (I : Fin d ↪o Fin n) : Fin d ≃ Inside (pivotSet.{u} I) :=
  Equiv.ofBijective (fun r ↦ ⟨ULift.up (I r), (mem_pivotSet I _).mpr ⟨r, rfl⟩⟩)
    ⟨fun _ _ h ↦ I.injective (congrArg (fun z : Inside (pivotSet.{u} I) ↦ z.val.down) h),
      fun j ↦ by
        obtain ⟨r, hr⟩ := (mem_pivotSet I j.val).mp j.property
        exact ⟨r, Subtype.ext (ULift.ext hr)⟩⟩

private theorem pivotColumn_apply (I : Fin d ↪o Fin n) (r : Fin d) :
    (pivotColumn.{u} I r).val.down = I r := rfl

private def cellEntryEquiv (I : Fin d ↪o Fin n) : CellEntry.{u} I ≃ EchelonVariable I where
  toFun p := ⟨(p.val.1.val.down, (pivotColumn I).symm p.val.2), by
    rw [← pivotColumn_apply.{u} I, Equiv.apply_symm_apply]
    exact ⟨p.property, fun h ↦ p.val.1.property ((mem_pivotSet I _).mpr h)⟩⟩
  invFun p := ⟨(⟨ULift.up p.val.1, fun h ↦ p.property.2 ((mem_pivotSet I _).mp h)⟩,
    pivotColumn I p.val.2), p.property.1⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (Subtype.ext (ULift.up_down _)) ((pivotColumn I).apply_symm_apply _)
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl ((pivotColumn.{u} I).symm_apply_apply _)

private def restrictionAlgebraMap (k : Type u) [Field k] (I : Fin d ↪o Fin n) :
    chartAlgebra (k := k) (pivotSet.{u} I) →ₐ[k] MvPolynomial (CellEntry.{u} I) k :=
  MvPolynomial.aeval fun p : ChartEntry.{u} I ↦
    if h : p.1.val.down < p.2.val.down then MvPolynomial.X ⟨p, h⟩ else 0

private theorem restrictionAlgebraMap_surjective (k : Type u) [Field k] (I : Fin d ↪o Fin n) :
    Function.Surjective (restrictionAlgebraMap k I) := by
  let ρ := MvPolynomial.rename (R := k) (Subtype.val : CellEntry.{u} I → ChartEntry.{u} I)
  have h : (restrictionAlgebraMap k I).comp ρ = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, ρ, MvPolynomial.rename_X, restrictionAlgebraMap, MvPolynomial.aeval_X,
      dite_eq_left p.property, AlgHom.id_apply]
  intro x
  exact ⟨ρ x, DFunLike.congr_fun h x⟩

private theorem echelonInChart_factor {k : Type u} [Field k] (I : Fin d ↪o Fin n)
    (R : TestAlgebra k) (f : Points (chartScheme (k := k) (pivotSet.{u} I)) R) :
    (∃ g : Points (echelonScheme k I) R, g ≫ echelonInChart k I = f) ↔
    ∀ (i : Outside (pivotSet.{u} I)) (j : Inside (pivotSet.{u} I)),
      ¬ i.val.down < j.val.down → matrixOfPoint (pivotSet.{u} I) R f i j = 0 := by
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let φ := restrictionAlgebraMap k I
  change (∃ g : Points (echelonScheme k I) R,
      g ≫ (testSpec k).map (CommAlgCat.ofHom φ).op = f) ↔ _
  constructor
  · rintro ⟨g, rfl⟩ i j h
    have hp : ff.preimage (g ≫ (testSpec k).map (CommAlgCat.ofHom φ).op) =
        ff.preimage g ≫ (CommAlgCat.ofHom φ).op := by
      apply ff.map_injective
      rw [Functor.map_comp, ff.map_preimage, ff.map_preimage]
    change ((ff.preimage (g ≫ (testSpec k).map (CommAlgCat.ofHom φ).op)).unop.hom)
      (MvPolynomial.X (i, j)) = 0
    rw [hp]
    change (ff.preimage g).unop.hom (φ (MvPolynomial.X (i, j))) = 0
    simp only [φ, restrictionAlgebraMap, MvPolynomial.aeval_X, dite_eq_right h, map_zero]
  · intro h
    let ψ : MvPolynomial (CellEntry.{u} I) k →ₐ[k] R :=
      MvPolynomial.aeval fun p ↦ (ff.preimage f).unop.hom (MvPolynomial.X p.val)
    refine ⟨(testSpec k).map (CommAlgCat.ofHom ψ).op, ?_⟩
    rw [← Functor.map_comp]
    refine (congrArg ((testSpec k).map) (show
      (CommAlgCat.ofHom ψ).op ≫ (CommAlgCat.ofHom φ).op = ff.preimage f from ?_)).trans
      (ff.map_preimage f)
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro p
    change ψ (φ (MvPolynomial.X p)) = (ff.preimage f).unop.hom (MvPolynomial.X p)
    by_cases hp : p.1.val.down < p.2.val.down
    · simp only [φ, restrictionAlgebraMap, MvPolynomial.aeval_X, dite_eq_left hp, ψ]
    · rw [show φ (MvPolynomial.X p) = 0 by
        simp only [φ, restrictionAlgebraMap, MvPolynomial.aeval_X, dite_eq_right hp], map_zero]
      exact (h p.1 p.2 hp).symm

theorem echelonCellImmersion : EchelonCellImmersion.{u} := by
  classical
  intro k V _ _ _ n d β C I
  have hc : IsClosedImmersion (echelonInChart k I).left :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (restrictionAlgebraMap k I).toRingHom)
      (restrictionAlgebraMap_surjective k I)
  have hi : IsImmersion (echelonCell β C I).left := by
    letI := hc
    letI := C.openChart (pivotSet.{u} I)
    change IsImmersion ((echelonInChart k I).left ≫ (C.chart (pivotSet.{u} I)).left)
    infer_instance
  refine ⟨hc, hi, ?_, fun R p ↦ ?_⟩
  · have hcard : Fintype.card (CellEntry.{u} I) = ∑ r, ((I r).val - r.val) := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr (cellEntryEquiv I), echelonCoordinateCount]
    let e : CellEntry.{u} I ≃ ULift.{u} (Fin (∑ r, ((I r).val - r.val))) :=
      (Fintype.equivFinOfCardEq hcard).trans Equiv.ulift.symm
    exact ⟨((testSpec k).mapIso (CommAlgCat.isoMk (MvPolynomial.renameEquiv k e)).op).symm⟩
  · constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g ≫ echelonInChart k I, Category.assoc _ _ _,
        (echelonInChart_factor I R _).mp ⟨g, rfl⟩⟩
    · rintro ⟨f, rfl, hf⟩
      obtain ⟨g, rfl⟩ := (echelonInChart_factor I R f).mpr hf
      exact ⟨g, (Category.assoc _ _ _).symm⟩

open private prefixSubmodule_coordinates mem_coordinateSubmodule
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagSchemes

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  (β : Module.Basis (Fin n) k V)

private theorem mem_prefix (R : TestAlgebra k) (j : ℕ) (v : R ⊗[k] V) :
    v ∈ FlagIncidence.prefixSubmodule β R j ↔
      ∀ i : ULift.{u} (Fin n), j ≤ i.down.val → coordinates (FlagSchemes.liftedBasis β) R v i = 0 := by
  let e := coordinates (FlagSchemes.liftedBasis β) R
  calc
    v ∈ FlagIncidence.prefixSubmodule β R j ↔
      e v ∈ (FlagIncidence.prefixSubmodule β R j).map e.toLinearMap := by
        constructor
        · intro hv
          exact ⟨v, hv, rfl⟩
        · rintro ⟨w, hw, he⟩
          exact e.injective he ▸ hw
    _ ↔ _ := by
      rw [prefixSubmodule_coordinates]
      simpa only [Set.mem_ofPred_eq, not_lt] using
        (mem_coordinateSubmodule (x := e v) (selected := {i : ULift.{u} (Fin n) | i.down.val < j}))

private theorem graph_coord_pivot (I : Pivot (ULift.{u} (Fin n)) d) (R : TestAlgebra k)
    (A : Matrix (Outside I) (Inside I) R) (x : Inside I → R) (c : Inside I) :
    coordinates (FlagSchemes.liftedBasis β) R
      (graphInclusion (FlagSchemes.liftedBasis β) I R A x) c.val = x c := by
  change (coordinates (FlagSchemes.liftedBasis β) R)
    ((coordinates (FlagSchemes.liftedBasis β) R).symm (graphColumns I R A x)) c.val = _
  rw [LinearEquiv.apply_symm_apply]
  change (if h : c.val ∈ I.val then
    (LinearMap.proj (R := R) (φ := fun _ : Inside I ↦ R) ⟨c.val, h⟩)
    else (LinearMap.proj (R := R) (φ := fun _ : Outside I ↦ R) ⟨c.val, h⟩).comp
      (Matrix.toLin' A)) x = _
  rw [dite_eq_left c.property]
  rfl

private theorem graph_coord_nonpivot (I : Pivot (ULift.{u} (Fin n)) d) (R : TestAlgebra k)
    (A : Matrix (Outside I) (Inside I) R) (x : Inside I → R) (i : Outside I) :
    coordinates (FlagSchemes.liftedBasis β) R
      (graphInclusion (FlagSchemes.liftedBasis β) I R A x) i.val = ∑ c, A i c * x c := by
  change (coordinates (FlagSchemes.liftedBasis β) R)
    ((coordinates (FlagSchemes.liftedBasis β) R).symm (graphColumns I R A x)) i.val = _
  rw [LinearEquiv.apply_symm_apply]
  change (if h : i.val ∈ I.val then
    (LinearMap.proj (R := R) (φ := fun _ : Inside I ↦ R) ⟨i.val, h⟩)
    else (LinearMap.proj (R := R) (φ := fun _ : Outside I ↦ R) ⟨i.val, h⟩).comp
      (Matrix.toLin' A)) x = _
  rw [dite_eq_right i.property]
  change Matrix.toLin' A x i = _
  rw [Matrix.toLin'_apply]
  rfl

variable {F : Type u} [Field F] [Algebra k F]

local notation "R" => CommAlgCat.of k F
local notation "b" => FlagSchemes.liftedBasis β

private abbrev EarlierPivots (I : Fin d ↪o Fin n) (j : ℕ) :=
  {r : Fin d // (I r).val < j}

private def prefixProjection (I : Fin d ↪o Fin n) (j : ℕ)
    (L : Submodule F (F ⊗[k] V)) :
    (L ⊓ FlagIncidence.prefixSubmodule β R j : Submodule F (F ⊗[k] V)) →ₗ[F]
      (EarlierPivots I j → F) :=
  (LinearMap.funLeft F F (fun r : EarlierPivots I j ↦ ULift.up (I r.val))).comp
    ((coordinates b R).toLinearMap.comp (L ⊓ FlagIncidence.prefixSubmodule β R j).subtype)

private theorem prefixProjection_injective (I : Fin d ↪o Fin n) (j : ℕ)
    (L : Submodule F (F ⊗[k] V))
    (hL : Function.Injective ((pivotProjection b (pivotSet.{u} I) R).comp L.subtype)) :
    Function.Injective (prefixProjection β I j L) := by
  have hexact (x : (L ⊓ FlagIncidence.prefixSubmodule β R j : Submodule F (F ⊗[k] V)))
      (h : prefixProjection β I j L x = 0) : x = 0 := by
    have hz : pivotProjection b (pivotSet.{u} I) R x.val = 0 := by
      funext c
      change coordinates b R x.val c.val = 0
      let r := (pivotColumn I).symm c
      have hr : I r = c.val.down :=
        (pivotColumn_apply.{u} I r).symm.trans
          (congrArg (fun z : Inside (pivotSet.{u} I) ↦ z.val.down) ((pivotColumn I).apply_symm_apply c))
      by_cases hlt : (I r).val < j
      · have hx := congrFun h ⟨r, hlt⟩
        change coordinates b R x.val (ULift.up (I r)) = 0 at hx
        rwa [hr] at hx
      · exact (mem_prefix β R j x.val).mp x.property.2 c.val (by simpa [hr] using Nat.le_of_not_gt hlt)
    have hzero : (⟨x.val, x.property.1⟩ : L) = 0 := by
      apply hL
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply, map_zero] using hz
    exact Subtype.ext (congrArg (fun z : L ↦ z.val) hzero)
  intro x y h
  apply sub_eq_zero.mp
  apply hexact
  rw [map_sub, h, sub_self]

private theorem finrank_earlierPivots (I : Fin d ↪o Fin n) (j : ℕ) :
    Module.finrank F (EarlierPivots I j → F) = pivotRank I j := by
  rw [Module.finrank_pi]
  exact Fintype.card_subtype _

private theorem intersectionRank_le_pivotRank (I : Fin d ↪o Fin n) (j : ℕ)
    (L : Plane k V d R) (hL : IsPivot b (pivotSet.{u} I) R L) :
    intersectionRank β L j ≤ pivotRank I j := by
  rw [← finrank_earlierPivots (F := F) I j]
  exact (prefixProjection β I j L.toSubmodule).finrank_le_finrank_of_injective
    (prefixProjection_injective β I j L.toSubmodule hL.1)

private theorem echelon_graph_intersectionRank (I : Fin d ↪o Fin n) (j : ℕ)
    (L : Plane k V d R) (A : Matrix (Outside (pivotSet.{u} I)) (Inside (pivotSet.{u} I)) F)
    (hL : L.toSubmodule = (graphInclusion b (pivotSet.{u} I) R A).range)
    (hA : ∀ i c, ¬ i.val.down < c.val.down → A i c = 0) :
    intersectionRank β L j = pivotRank I j := by
  let P := pivotSet.{u} I
  have hP : IsPivot b P R L := by
    have h := _root_.LinearAlgebraicGroups.GrassmannianCharts.graphPlane_isPivot b P R A
    have he : L = _root_.LinearAlgebraicGroups.GrassmannianCharts.graphPlane b P R A :=
      Module.Grassmannian.ext hL
    rwa [← he] at h
  have hs : Function.Surjective (prefixProjection β I j L.toSubmodule) := by
    intro x
    let y : Inside P → F := fun c ↦
      if h : (I ((pivotColumn I).symm c)).val < j then x ⟨(pivotColumn I).symm c, h⟩ else 0
    let v := graphInclusion b P R A y
    have hv : v ∈ FlagIncidence.prefixSubmodule β R j := by
      apply (mem_prefix β R j v).mpr
      intro i hi
      by_cases hp : i ∈ P.val
      · let c : Inside P := ⟨i, hp⟩
        change coordinates b R v c.val = 0
        rw [graph_coord_pivot β P R A y c]
        have hc : I ((pivotColumn I).symm c) = c.val.down :=
          (pivotColumn_apply.{u} I _).symm.trans
            (congrArg (fun z : Inside P ↦ z.val.down) ((pivotColumn I).apply_symm_apply c))
        simp only [y, dite_eq_right (show ¬ (I ((pivotColumn I).symm c)).val < j by
          rw [hc]; exact Nat.not_lt_of_ge hi)]
      · let row : Outside P := ⟨i, hp⟩
        change coordinates b R v row.val = 0
        rw [graph_coord_nonpivot β P R A y row]
        apply Finset.sum_eq_zero
        intro c _
        by_cases he : (I ((pivotColumn I).symm c)).val < j
        · have hc : I ((pivotColumn I).symm c) = c.val.down :=
            (pivotColumn_apply.{u} I _).symm.trans
              (congrArg (fun z : Inside P ↦ z.val.down) ((pivotColumn I).apply_symm_apply c))
          rw [hc] at he
          rw [hA row c (show ¬ row.val.down < c.val.down from
            Nat.not_lt_of_ge (Nat.le_trans he.le hi)), zero_mul]
        · rw [show y c = 0 by simp only [y, dite_eq_right he], mul_zero]
    refine ⟨⟨v, ⟨hL.symm ▸ (LinearMap.mem_range_self _ y), hv⟩⟩, ?_⟩
    funext r
    change coordinates b R v (pivotColumn I r.val).val = x r
    rw [graph_coord_pivot β P R A y]
    simp only [y, Equiv.symm_apply_apply, dite_eq_left r.property]
  let e := LinearEquiv.ofBijective (prefixProjection β I j L.toSubmodule)
    ⟨prefixProjection_injective β I j _ hP.1, hs⟩
  exact e.finrank_eq.trans (finrank_earlierPivots I j)

theorem echelonCellRank : EchelonCellRank.{u} := by
  intro k V _ _ _ n d β C I F _ _ p hp j
  obtain ⟨f, hf, hzero⟩ := (echelonCellImmersion β C I).2.2.2 _ p |>.mp hp
  exact echelon_graph_intersectionRank β I j (C.affinePoints.hom.app _ p)
    (matrixOfPoint (pivotSet.{u} I) _ f) (hf ▸ C.coordinates_eq _ _ f) hzero

private theorem exists_tuple_of_pivot (P : Pivot (ULift.{u} (Fin n)) d) :
    ∃ I : Fin d ↪o Fin n, pivotSet.{u} I = P := by
  let e : ULift.{u} (Fin n) ↪ Fin n := ⟨ULift.down, fun _ _ h ↦ ULift.ext h⟩
  let D := P.val.map e
  have hD : D.card = d := (Finset.card_map _).trans P.property
  refine ⟨D.orderEmbOfFin hD, Subtype.ext ?_⟩
  ext i
  rw [mem_pivotSet, D.range_orderEmbOfFin, Finset.mem_coe]
  constructor
  · intro hi
    obtain ⟨l, hl, he⟩ := Finset.mem_map.mp hi
    exact e.injective he ▸ hl
  · intro hi
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

private def pivotHeight (P : Pivot (ULift.{u} (Fin n)) d) : ℕ :=
  ∑ i ∈ P.val, i.down.val

include β in
private theorem pivot_exchange (P : Pivot (ULift.{u} (Fin n)) d)
    (A : Matrix (Outside P) (Inside P) F) (i : Outside P) (c : Inside P)
    (hgt : c.val.down < i.val.down) (hac : A i c ≠ 0) :
    ∃ Q : Pivot (ULift.{u} (Fin n)) d, Q.val = insert i.val (P.val.erase c.val) ∧
      pivotHeight P < pivotHeight Q ∧
      Function.Bijective (pivotChange P R Q A) := by
  classical
  let q := insert i.val (P.val.erase c.val)
  have hnew : i.val ∉ P.val.erase c.val := fun h ↦ i.property (Finset.mem_of_mem_erase h)
  have hcard : q.card = d := by
    rw [Finset.card_insert_of_notMem hnew, Finset.card_erase_add_one c.property, P.property]
  let Q : Pivot (ULift.{u} (Fin n)) d := ⟨q, hcard⟩
  have hi : pivotHeight P < pivotHeight Q := by
    have hp : c.val.down.val + (∑ z ∈ P.val.erase c.val, z.down.val) = pivotHeight P :=
      Finset.add_sum_erase P.val (fun z ↦ z.down.val) c.property
    have hq : pivotHeight Q = i.val.down.val + ∑ z ∈ P.val.erase c.val, z.down.val :=
      Finset.sum_insert hnew
    rw [← hp, hq]
    exact Nat.add_lt_add_right hgt _
  refine ⟨Q, rfl, hi, ?_⟩
  have hinj : Function.Injective (pivotChange P R Q A) := by
    apply (LinearMap.ker_eq_bot (f := pivotChange P R Q A)).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hzero (l : Inside P) (hne : l ≠ c) : x l = 0 := by
      have hl : l.val ∈ Q.val := Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨fun h ↦ hne (Subtype.ext h), l.property⟩)
      have he := congrFun hx ⟨l.val, hl⟩
      change graphColumns P R A x l.val = 0 at he
      have hc := graph_coord_pivot β P R A x l
      rw [show coordinates b R (graphInclusion b P R A x) = graphColumns P R A x from
        (coordinates b R).apply_symm_apply _, he] at hc
      exact hc.symm
    have he := congrFun hx (⟨i.val, Finset.mem_insert_self _ _⟩ : Inside Q)
    change graphColumns P R A x i.val = 0 at he
    have hs := graph_coord_nonpivot β P R A x i
    rw [show coordinates b R (graphInclusion b P R A x) = graphColumns P R A x from
      (coordinates b R).apply_symm_apply _, he, Finset.sum_eq_single c] at hs
    · have hxc := (mul_eq_zero.mp hs.symm).resolve_left hac
      funext l
      by_cases hl : l = c
      · simpa [hl] using hxc
      · exact hzero l hl
    · intro l _ hl
      rw [hzero l hl, mul_zero]
    · simp
  have hrank : Module.finrank F (Inside P → F) = Module.finrank F (Inside Q → F) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_coe, Fintype.card_coe,
      P.property, Q.property]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩

set_option maxHeartbeats 400000 in
private theorem exists_echelon_field_point (hd : d ≤ n)
    (C : ChartSystem (k := k) (V := V) b d) (p : Points C.scheme R) :
    ∃ (I : Fin d ↪o Fin n) (f : Points (echelonScheme k I) R),
      f ≫ echelonCell β C I = p := by
  classical
  let L := C.affinePoints.hom.app R p
  let S : Finset (Pivot (ULift.{u} (Fin n)) d) :=
    Finset.univ.filter fun P ↦ IsPivot b P R L
  have hd' : d ≤ Module.finrank k V := by
    simpa [Module.finrank_eq_card_basis β] using hd
  obtain ⟨P₀, hP₀⟩ := _root_.LinearAlgebraicGroups.GrassmannianCharts.fieldPivotCoverage
    k V (ULift.{u} (Fin n)) b d hd' F L
  obtain ⟨P, hP, hmax⟩ := S.exists_max_image pivotHeight
    ⟨P₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP₀⟩⟩
  obtain ⟨f, hf⟩ := (C.factor_iff P R p).mpr (Finset.mem_filter.mp hP).2
  let A := matrixOfPoint P R f
  have hgraph : L = _root_.LinearAlgebraicGroups.GrassmannianCharts.graphPlane b P R A := by
    apply Module.Grassmannian.ext
    change (C.affinePoints.hom.app R p).toSubmodule = _
    rw [← hf, C.coordinates_eq, _root_.LinearAlgebraicGroups.GrassmannianCharts.graphPlane_toSubmodule]
  have hzero : ∀ (i : Outside P) (c : Inside P), ¬ i.val.down < c.val.down → A i c = 0 := by
    intro i c hic
    by_contra hA
    have hne : c.val.down ≠ i.val.down := fun he ↦ i.property (ULift.ext he ▸ c.property)
    have hlt := lt_of_le_of_ne (le_of_not_gt hic) hne
    obtain ⟨Q, -, hQ, hinv⟩ := pivot_exchange β P A i c hlt hA
    have hqp : IsPivot b Q R L := by
      rw [hgraph, _root_.LinearAlgebraicGroups.GrassmannianCharts.isPivot_graphPlane_iff]
      exact hinv
    exact (not_lt_of_ge (hmax Q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqp⟩))) hQ
  obtain ⟨I, rfl⟩ := exists_tuple_of_pivot P
  obtain ⟨g, hg⟩ := ((echelonCellImmersion β C I).2.2.2 R p).mpr ⟨f, hf, hzero⟩
  exact ⟨I, g, hg⟩

theorem echelonCellRankCriterion : EchelonCellRankCriterion.{u} := by
  intro k V _ _ _ n d β C I F _ _ p
  constructor
  · exact echelonCellRank β C I p
  · intro h
    have hd : d ≤ n := by
      simpa using Fintype.card_le_of_injective I I.injective
    obtain ⟨J, f, hf⟩ := exists_echelon_field_point β hd C p
    have he := echelonCellRank β C J p ⟨f, hf⟩
    have hp : I = J := by
      ext r
      have hJI := (pivotRankOrder I J).mp (fun j _ ↦ (h j).symm.trans (he j) |>.le) r
      have hIJ := (pivotRankOrder J I).mp (fun j _ ↦ (he j).symm.trans (h j) |>.le) r
      exact congrArg Fin.val (le_antisymm hIJ hJI)
    subst J
    exact ⟨f, hf⟩


theorem echelonCellCoverage : EchelonCellCoverage.{u} := by
  intro k V _ _ _ n d β C hd F _ _ p
  exact exists_echelon_field_point β hd C p

private theorem residuePoint_factors_iff {X Y : SchemeOver k}
    (f : X ⟶ Y) [SurjectiveOnStalks f.left] (x : Y.left) :
    (∃ g : Points X (residueTestAlgebra Y x), g ≫ f = residuePoint Y x) ↔
      x ∈ Set.range f.left := by
  constructor
  · rintro ⟨g, hg⟩
    let y := IsLocalRing.closedPoint (Y.left.residueField x)
    refine ⟨g.left y, ?_⟩
    have hh := congrArg (fun l : Points Y (residueTestAlgebra Y x) ↦ l.left y) hg
    exact hh.trans (Y.left.fromSpecResidueField_apply x y)
  · rintro ⟨y, rfl⟩
    let a := f.left.residueFieldMap y
    have hs : Function.Surjective a := by
      intro z
      obtain ⟨v, rfl⟩ := X.left.residue_surjective y z
      obtain ⟨w, hw⟩ := f.left.stalkMap_surjective y v
      refine ⟨Y.left.residue (f.left y) w, ?_⟩
      have he := congrArg
        (fun l : Y.left.presheaf.stalk (f.left y) ⟶ X.left.residueField y ↦ l w)
        (Scheme.residue_residueFieldMap f.left y)
      change a (Y.left.residue (f.left y) w) = X.left.residue y (f.left.stalkMap y w) at he
      rwa [hw] at he
    let e := (RingEquiv.ofBijective a.hom ⟨a.hom.injective, hs⟩).toCommRingCatIso
    let g := Spec.map e.inv ≫ X.left.fromSpecResidueField y
    have hg : g ≫ f.left = Y.left.fromSpecResidueField (f.left y) := by
      change (Spec.map e.inv ≫ X.left.fromSpecResidueField y) ≫ f.left = _
      rw [Category.assoc, ← f.left.SpecMap_residueFieldMap_fromSpecResidueField y,
        ← Spec.map_comp_assoc]
      change Spec.map (e.hom ≫ e.inv) ≫ _ = _
      rw [e.hom_inv_id, Spec.map_id, Category.id_comp]
    refine ⟨Over.homMk g ?_, Over.OverMorphism.ext hg⟩
    calc
      g ≫ X.hom = g ≫ (f.left ≫ Y.hom) := congrArg (g ≫ ·) (Over.w f).symm
      _ = (g ≫ f.left) ≫ Y.hom := (Category.assoc _ _ _).symm
      _ = Y.left.fromSpecResidueField (f.left y) ≫ Y.hom := congrArg (· ≫ Y.hom) hg
      _ = Spec.map (Spec.preimage (Y.left.fromSpecResidueField (f.left y) ≫ Y.hom)) :=
        (Spec.map_preimage _).symm

private theorem residueRank_on_cell
    (C : ChartSystem (k := k) (V := V) b d)
    (I : Fin d ↪o Fin n) {x : C.scheme.left} (hx : x ∈ Set.range (echelonCell β C I).left) :
    ∀ j, residueRank β C x j = pivotRank I j := by
  letI := (echelonCellImmersion β C I).2.1
  letI := residueBaseAlgebra C.scheme x
  exact echelonCellRank β C I (residuePoint C.scheme x)
    ((residuePoint_factors_iff (echelonCell β C I) x).mpr hx)

private theorem residueRank_le_of_chart
    (C : ChartSystem (k := k) (V := V) b d)
    (I : Fin d ↪o Fin n) {x : C.scheme.left} (hx : x ∈ Set.range (C.chart (pivotSet.{u} I)).left) :
    ∀ j, residueRank β C x j ≤ pivotRank I j := by
  letI := C.openChart (pivotSet.{u} I)
  letI := residueBaseAlgebra C.scheme x
  have hf := (residuePoint_factors_iff (C.chart (pivotSet.{u} I)) x).mpr hx
  have hp := (C.factor_iff (pivotSet.{u} I) _ (residuePoint C.scheme x)).mp hf
  intro j
  exact intersectionRank_le_pivotRank β I j _ hp

theorem closedRankLocus : ClosedRankLocus.{u} := by
  classical
  intro k V _ _ _ n d β C I
  have hd : d ≤ n := by simpa using Fintype.card_le_of_injective I I.injective
  have cover (x : C.scheme.left) :
      ∃ J : Fin d ↪o Fin n, x ∈ Set.range (echelonCell β C J).left := by
    letI := residueBaseAlgebra C.scheme x
    obtain ⟨J, f, h⟩ := exists_echelon_field_point β hd C (residuePoint C.scheme x)
    letI := (echelonCellImmersion β C J).2.1
    exact ⟨J, (residuePoint_factors_iff _ x).mp ⟨f, h⟩⟩
  have coe (J : Fin d ↪o Fin n) :
      Set.range (echelonCell β C J).left ⊆ Set.range (C.chart (pivotSet.{u} J)).left := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(echelonInChart k J).left z, rfl⟩
  have heq : rankLocus β C I = ⋂ (J : Fin d ↪o Fin n) (_ : ¬ ∀ r, J r ≤ I r),
      (Set.range (C.chart (pivotSet.{u} J)).left)ᶜ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    constructor
    · intro hx J hJ hchart
      apply hJ
      apply (pivotRankOrder I J).mp
      intro j hj
      exact (hx j hj).trans (residueRank_le_of_chart β C J hchart j)
    · intro hx j hj
      obtain ⟨J, hJ⟩ := cover x
      have hle : ∀ r, J r ≤ I r := by
        by_contra h
        exact hx J h (coe J hJ)
      rw [residueRank_on_cell β C J hJ j]
      exact (pivotRankOrder I J).mpr hle j hj
  constructor
  · rw [heq]
    exact isClosed_iInter fun J ↦ isClosed_iInter fun _ ↦
      (C.openChart (pivotSet.{u} J)).isOpen_range.isClosed_compl
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨J, hJ⟩ := cover x
      refine ⟨J, (pivotRankOrder I J).mp ?_, hJ⟩
      intro j hj
      rw [← residueRank_on_cell β C J hJ j]
      exact hx j hj
    · rintro ⟨J, hJ, hx⟩ j hj
      rw [residueRank_on_cell β C J hx j]
      exact (pivotRankOrder I J).mpr hJ j hj

theorem echelonEndpointGeometry : EchelonEndpointGeometry.{u} := by
  classical
  intro k V _ _ _ n d β C hd I
  have hdim : Module.finrank k V = n := by simpa using Module.finrank_eq_card_basis β
  obtain ⟨hzero, hfull⟩ := _root_.LinearAlgebraicGroups.GrassmannianCharts.endpoints
    k V (ULift.{u} (Fin n)) (FlagSchemes.liftedBasis β)
  have ht' : Nonempty (IsTerminal C.scheme) := by
    rcases hd with h | h
    · subst d
      exact hzero C
    · subst d
      rw [hdim] at hfull
      exact hfull C
  let ht := ht'.some
  let ht₀ : IsTerminal (FlagSchemes.pointScheme k) := Over.mkIdTerminal
  have hvars : (∑ r, ((I r).val - r.val)) = 0 := by
    rcases hd with h | h
    · subst d
      simp
    · subst d
      rw [((endpointPivots n).2 I).1]
      simp
  have hc : IsTerminal (echelonScheme k I) := by
    have hcard : Fintype.card (CellEntry.{u} I) = 0 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr (cellEntryEquiv I),
        echelonCoordinateCount, hvars]
    letI : IsEmpty (CellEntry.{u} I) := Fintype.card_eq_zero_iff.mp hcard
    let e : CommAlgCat.of k (MvPolynomial (CellEntry.{u} I) k) ≅ CommAlgCat.of k k :=
      CommAlgCat.isoMk (MvPolynomial.isEmptyAlgEquiv k (CellEntry.{u} I))
    let e₀ : FlagSchemes.pointScheme k ≅ (testSpec k).obj (op (CommAlgCat.of k k)) :=
      Over.isoMk (Iso.refl _) (by
        change (𝟙 (Spec (CommRingCat.of k))) ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) = _
        rw [Category.id_comp]
        exact Spec.map_id (CommRingCat.of k))
    exact ht₀.ofIso (e₀ ≪≫ (testSpec k).mapIso e.op)
  let e := ht.uniqueUpToIso ht₀
  letI : IsIso (echelonCell β C I) := isIso_of_isTerminal hc ht _
  haveI : IsIso (echelonCell β C I).left := inferInstanceAs
    (IsIso ((Over.forget _).map (echelonCell β C I)))
  have hsurj := (echelonCell β C I).left.surjective
  letI : AlgebraicGeometry.IsReduced C.scheme.left := by
    haveI : AlgebraicGeometry.IsReduced (FlagSchemes.pointScheme k).left :=
      inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (CommRingCat.of k)))
    letI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    exact isReduced_of_isOpenImmersion e.hom.left
  let D := Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure (Set.range (echelonCell β C I).left))
  haveI : Surjective D.subschemeι := by
    constructor
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι]
    simp [D, Scheme.IdealSheafData.coe_support_vanishingIdeal, Set.range_eq_univ.mpr hsurj]
  refine ⟨⟨e⟩, inferInstance, isIso_of_isClosedImmersion_of_surjective D.subschemeι, ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  intro j hj
  exact (residueRank_on_cell β C I ⟨y, rfl⟩ j).ge

theorem tailProjectionQuotient : TailProjectionQuotient.{u} := by
  intro k V F _ _ _ _ _ n β j
  constructor
  · ext v
    refine Iff.trans LinearMap.mem_ker ?_
    exact (funext_iff.trans ⟨fun h i hi ↦ h ⟨i, hi⟩, fun h i ↦ h i.val i.property⟩).trans
      (mem_prefix β (CommAlgCat.of k F) j v).symm
  · classical
    intro y
    let e := coordinates (FlagSchemes.liftedBasis β) (CommAlgCat.of k F)
    refine ⟨e.symm (fun i ↦ if h : j ≤ i.down.val then y ⟨i, h⟩ else 0), ?_⟩
    funext i
    change e (e.symm _) i.val = y i
    rw [LinearEquiv.apply_symm_apply, dite_eq_left i.property]

theorem tailRankComparison : TailRankComparison.{u} := by
  intro k V F _ _ _ _ _ n d β I L j
  let _ : Module.Finite k V := Module.Finite.of_basis β
  let R₀ := CommAlgCat.of k F
  let U : Submodule F (F ⊗[k] V) := L.toSubmodule
  let E : Submodule F (F ⊗[k] V) := FlagIncidence.prefixSubmodule β R₀ j
  let π : U →ₗ[F] ({i : ULift.{u} (Fin n) // j ≤ i.down.val} → F) :=
    (tailProjection β j).comp U.subtype
  have hker (x : U) : x ∈ LinearMap.ker π ↔ x.val ∈ E := by
    change x.val ∈ LinearMap.ker (tailProjection β j) ↔ _
    rw [(tailProjectionQuotient (F := F) β j).1]
  let v : (U ⊓ E : Submodule F (F ⊗[k] V)) →ₗ[F] LinearMap.ker π :=
    (Submodule.inclusion (show U ⊓ E ≤ U from inf_le_left)).codRestrict _ (fun x ↦ (hker _).mpr x.property.2)
  have hv : Function.Bijective v := by
    refine ⟨fun _ _ eq ↦ Subtype.ext (congrArg (fun z : LinearMap.ker π ↦ z.val.val) eq), ?_⟩
    intro y
    exact ⟨⟨y.val.val, y.val.property, (hker _).mp y.property⟩, Subtype.ext (Subtype.ext rfl)⟩
  have hk : Module.finrank F (LinearMap.ker π) = intersectionRank β L j :=
    (LinearEquiv.ofBijective v hv).finrank_eq.symm
  have hd : d ≤ Module.finrank k V := by
    rw [Module.finrank_eq_card_basis β]
    simpa using Fintype.card_le_of_injective I I.injective
  obtain ⟨_, hfinite, _, hr⟩ := _root_.LinearAlgebraicGroups.GrassmannianCharts.planeSplitAndRank
    k V d hd R₀ L
  letI : Module.Finite F U := hfinite
  letI : Module.Free F U := Module.Free.of_basis (Module.Basis.ofVectorSpace F U)
  have hdim : Module.finrank F U = d := by
    have h := hr (IsLocalRing.closedPoint F)
    change Module.rankAtStalk («R» := F) U (IsLocalRing.closedPoint F) = d at h
    rwa [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply] at h
  have he := LinearMap.finrank_range_add_finrank_ker (K := F) (V := U) π
  rw [hk, hdim] at he
  have hb : pivotRank I j ≤ d :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Fintype.card_fin d)
  change pivotRank I j ≤ intersectionRank β L j ↔ Module.finrank F π.range ≤ d - pivotRank I j
  omega

private theorem advancesPivot_le {J I : Fin d ↪o Fin n} {r : Fin d} (h : AdvancesPivot J I r) :
    ∀ s, J s ≤ I s := by
  intro s
  by_cases hs : s = r
  · subst s
    change (J r).val ≤ (I r).val
    rw [h.1]
    exact Nat.le_succ _
  · rw [h.2 s hs]

private theorem exists_pivot_advance {J I : Fin d ↪o Fin n} (h : ∀ s, J s ≤ I s) (hne : J ≠ I) :
    ∃ (K : Fin d ↪o Fin n) (r : Fin d), AdvancesPivot J K r ∧ ∀ s, K s ≤ I s := by
  classical
  let s := Finset.univ.filter fun r : Fin d ↦ J r < I r
  have hs : s.Nonempty := by
    by_contra hEmpty
    apply hne
    ext r
    have hn : ¬ J r < I r := fun hl ↦ hEmpty ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩⟩
    exact congrArg Fin.val ((h r).antisymm (not_lt.mp hn))
  obtain ⟨r, hr, hmax⟩ := s.exists_max_image id hs
  have hlt := (Finset.mem_filter.mp hr).2
  let up : Fin n := ⟨(J r).val + 1, (Nat.succ_le_of_lt hlt).trans_lt (I r).isLt⟩
  have hup : up ≤ I r := Nat.succ_le_of_lt hlt
  have hafter (a : Fin d) (ha : r < a) : I a = J a := by
    by_contra hneq
    exact (not_le_of_gt ha) (hmax a (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, lt_of_le_of_ne (h a) (Ne.symm hneq)⟩))
  let f (a : Fin d) := if a = r then up else J a
  have hf : StrictMono f := by
    intro a c hac
    by_cases ha : a = r
    · subst a
      have hc : c ≠ r := ne_of_gt hac
      simp only [f, ite_eq_left rfl, ite_eq_right hc]
      rw [← hafter c hac]
      exact hup.trans_lt (I.strictMono hac)
    · by_cases hc : c = r
      · subst c
        simp only [f, ite_eq_right ha, ite_eq_left rfl]
        exact (J.strictMono hac).trans_le (show J r ≤ up from Nat.le_succ _)
      · simpa only [f, ite_eq_right ha, ite_eq_right hc] using J.strictMono hac
  let K := OrderEmbedding.ofStrictMono f hf
  refine ⟨K, r, ⟨?_, ?_⟩, ?_⟩
  · change (f r).val = _
    simp [f, up]
  · intro a ha
    change f a = J a
    simp [f, ha]
  · intro a
    change f a ≤ I a
    by_cases ha : a = r
    · simpa [f, ha] using hup
    · simpa [f, ha] using h a


theorem adjacentPivotOrder : AdjacentPivotOrder := by
  classical
  intro d n I J
  constructor
  · intro h
    let height (K : Fin d ↪o Fin n) := ∑ r, (K r).val
    suffices ∀ (m : ℕ) (K : Fin d ↪o Fin n), height I - height K = m → (∀ r, K r ≤ I r) →
        Relation.ReflTransGen (fun M L : Fin d ↪o Fin n ↦ ∃ r, AdvancesPivot M L r) K I from
      this _ J rfl h
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro K hmeasure hKI
      by_cases he : K = I
      · subst K
        exact .refl
      · obtain ⟨L, r, hKL, hLI⟩ := exists_pivot_advance hKI he
        have hlt : height K < height L := by
          apply Finset.sum_lt_sum (fun s _ ↦ show (K s).val ≤ (L s).val from advancesPivot_le hKL s)
          refine ⟨r, Finset.mem_univ _, ?_⟩
          rw [hKL.1]
          exact Nat.lt_succ_self _
        have hle : height L ≤ height I :=
          Finset.sum_le_sum fun r _ ↦ (show (L r).val ≤ (I r).val from hLI r)
        have hdiff : height I - height L < m := by omega
        exact (Relation.ReflTransGen.single ⟨r, hKL⟩).trans (ih _ hdiff L rfl hLI)
  · intro h
    induction h with
    | refl => exact fun _ ↦ le_rfl
    | tail _ hstep ih =>
      obtain ⟨r, hstep⟩ := hstep
      exact fun s ↦ (ih s).trans (advancesPivot_le hstep s)

theorem pivotAdvanceTransposition : PivotAdvanceTransposition := by
  intro d n J I r h s
  by_cases hs : s = r
  · subst s
    exact Equiv.swap_apply_left _ _
  · have hj : J s ≠ J r := fun eq ↦ hs (J.injective eq)
    have hi : J s ≠ I r := fun eq ↦ hs (I.injective ((h.2 s hs).trans eq))
    rw [Equiv.swap_apply_of_ne_of_ne hj hi, h.2 s hs]

private theorem prefix_rank_of_bounded_graph (I J : Fin d ↪o Fin n) (j : ℕ)
    (hIJ : ∀ r, J r ≤ I r)
    (L : Plane k V d R) (A : Matrix (Outside (pivotSet.{u} J)) (Inside (pivotSet.{u} J)) F)
    (hL : L.toSubmodule = (graphInclusion b (pivotSet.{u} J) R A).range)
    (hA : ∀ i c, I ((pivotColumn J).symm c) < i.val.down → A i c = 0) :
    pivotRank I j ≤ intersectionRank β L j := by
  letI : Module.Finite F (F ⊗[k] V) := Module.Finite.of_basis (β.baseChange F)
  let P := pivotSet.{u} J
  let e : (EarlierPivots I j → F) →ₗ[F] (Inside P → F) := LinearMap.pi fun c ↦
    if h : (I ((pivotColumn J).symm c)).val < j then
      LinearMap.proj («R» := F) (φ := fun _ : EarlierPivots I j ↦ F) ⟨(pivotColumn J).symm c, h⟩
    else 0
  have he (x : EarlierPivots I j → F) (c : Inside P) :
      e x c =
        if h : (I ((pivotColumn J).symm c)).val < j then x ⟨(pivotColumn J).symm c, h⟩ else 0 := by
    change (if h : (I ((pivotColumn J).symm c)).val < j then
      LinearMap.proj («R» := F) (φ := fun _ : EarlierPivots I j ↦ F) ⟨(pivotColumn J).symm c, h⟩
      else 0) x = _
    split <;> rfl
  have heInj : Function.Injective e := by
    intro x y h
    funext r
    have h' := congrFun h (pivotColumn J r.val)
    simpa only [he, Equiv.symm_apply_apply, dite_eq_left r.property] using h'
  let g := graphInclusion b P R A
  have hgInj : Function.Injective g := by
    have h := _root_.LinearAlgebraicGroups.GrassmannianCharts.pivotProjection_graph b P R A
    have hleft : Function.LeftInverse (pivotProjection b P R) g :=
      fun x ↦ DFunLike.congr_fun h x
    exact hleft.injective
  have hin (x : EarlierPivots I j → F) :
      g (e x) ∈ (L.toSubmodule ⊓ FlagIncidence.prefixSubmodule β R j :
        Submodule F (F ⊗[k] V)) := by
    refine ⟨hL.symm ▸ LinearMap.mem_range_self g (e x), ?_⟩
    apply (mem_prefix β R j _).mpr
    intro i hi
    by_cases hp : i ∈ P.val
    · let c : Inside P := ⟨i, hp⟩
      change coordinates b R (g (e x)) c.val = 0
      rw [graph_coord_pivot β P R A (e x) c, he]
      apply dite_eq_right
      have hc : J ((pivotColumn J).symm c) = c.val.down :=
        (pivotColumn_apply.{u} J _).symm.trans
          (congrArg (fun z : Inside P ↦ z.val.down) ((pivotColumn J).apply_symm_apply c))
      exact Nat.not_lt_of_ge (hi.trans ((congrArg Fin.val hc).ge.trans (hIJ _)))
    · let row : Outside P := ⟨i, hp⟩
      change coordinates b R (g (e x)) row.val = 0
      rw [graph_coord_nonpivot β P R A (e x) row]
      apply Finset.sum_eq_zero
      intro c _
      rw [he]
      split
      · rename_i hc
        rw [hA row c (hc.trans_le hi), zero_mul]
      · rw [mul_zero]
  let f := (g.comp e).codRestrict _ hin
  have hf : Function.Injective f :=
    fun x y h ↦ heInj (hgInj (congrArg Subtype.val h))
  have hf' := f.finrank_le_finrank_of_injective hf
  exact (finrank_earlierPivots I j).symm.le.trans hf'

open private matrixOfPoint_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.GrassmannianCharts

private abbrev polynomialFractionMap (F : Type u) [Field F] [Algebra k F] :
    polynomialAlgebra (CommAlgCat.of k F) ⟶ CommAlgCat.of k (FractionRing (Polynomial F)) :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k (Polynomial F) (FractionRing (Polynomial F)))

private theorem polynomialFamily_specializes {X : SchemeOver k}
    (p : Points X (polynomialAlgebra R)) :
    (mapPoints (polynomialFractionMap F) p).left
        (IsLocalRing.closedPoint (FractionRing (Polynomial F))) ⤳
      (mapPoints (polynomialEvaluate R 0) p).left (IsLocalRing.closedPoint F) := by
  let K := FractionRing (Polynomial F)
  let q : PrimeSpectrum (Polynomial F) := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : ((testSpec k).map (polynomialFractionMap F).op).left (IsLocalRing.closedPoint K) = q := by
    change PrimeSpectrum.comap (algebraMap (Polynomial F) K) (IsLocalRing.closedPoint K) = q
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap (Polynomial F) K) (IsLocalRing.maximalIdeal K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    ext x
    change algebraMap (Polynomial F) K x = 0 ↔ x = 0
    exact map_eq_zero_iff _ (IsFractionRing.injective (Polynomial F) K)
  let x : PrimeSpectrum (Polynomial F) :=
    ((testSpec k).map (polynomialEvaluate R 0).op).left (IsLocalRing.closedPoint F)
  have hx : q ⤳ x := by
    rw [specializes_iff_mem_closure, PrimeSpectrum.closure_singleton]
    change x ∈ PrimeSpectrum.zeroLocus ((⊥ : Ideal (Polynomial F)) : Set (Polynomial F))
    simp
  change p.left (((testSpec k).map (polynomialFractionMap F).op).left _) ⤳ p.left x
  rw [hq]
  exact hx.map p.left.continuous


private def advancedRow {J I : Fin d ↪o Fin n} {r : Fin d} (h : AdvancesPivot J I r) :
    Outside (pivotSet.{u} J) :=
  ⟨ULift.up (I r), by
    intro hm
    obtain ⟨s, hs⟩ := (mem_pivotSet J _).mp hm
    by_cases e : s = r
    · subst s
      have hp : (J r).val = (I r).val := congrArg Fin.val hs
      have hr := h.1
      omega
    · exact e (I.injective ((h.2 s e).trans hs))⟩

private theorem advancedRow_lt {J I : Fin d ↪o Fin n} {r : Fin d} (h : AdvancesPivot J I r) :
    (pivotColumn.{u} J r).val.down < (advancedRow.{u} h).val.down := by
  change (J r).val < (I r).val
  rw [h.1]
  exact Nat.lt_succ_self _

private theorem pivotSet_advance {J I : Fin d ↪o Fin n} {r : Fin d} (h : AdvancesPivot J I r) :
    insert (advancedRow.{u} h).val ((pivotSet.{u} J).val.erase (pivotColumn.{u} J r).val) =
      (pivotSet.{u} I).val := by
  ext l
  rw [Finset.mem_insert, Finset.mem_erase, mem_pivotSet, mem_pivotSet]
  constructor
  · rintro (hl | ⟨hl, s, hs⟩)
    · exact ⟨r, (congrArg ULift.down hl).symm⟩
    · have hsr : s ≠ r := by
        intro hr
        subst s
        exact hl (ULift.ext hs.symm)
      exact ⟨s, (h.2 s hsr).trans hs⟩
  · rintro ⟨s, hs⟩
    by_cases hsr : s = r
    · subst s
      exact Or.inl (ULift.ext hs.symm)
    · have hz := (h.2 s hsr).symm.trans hs
      exact Or.inr ⟨fun he ↦ hsr (J.injective (hz.trans (congrArg ULift.down he))), s, hz⟩

private def advancedGraph {J I : Fin d ↪o Fin n} {r : Fin d} (h : AdvancesPivot J I r)
    {S : Type u} (A : Matrix (Outside (pivotSet.{u} J)) (Inside (pivotSet.{u} J)) S) (a : S) :
    Matrix (Outside (pivotSet.{u} J)) (Inside (pivotSet.{u} J)) S :=
  Matrix.of fun i c ↦ if i = advancedRow.{u} h ∧ c = pivotColumn.{u} J r then a else A i c

private theorem advancedGraph_map {J I : Fin d ↪o Fin n} {r : Fin d} (h : AdvancesPivot J I r)
    {S T : Type u} (A : Matrix (Outside (pivotSet.{u} J)) (Inside (pivotSet.{u} J)) S) (a : S)
    (f : S → T) : (advancedGraph h A a).map f = advancedGraph h (A.map f) (f a) := by
  ext i c
  simp only [advancedGraph, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> rfl

private theorem advancedGraph_zero {J I : Fin d ↪o Fin n} {r : Fin d} (h : AdvancesPivot J I r)
    {S : Type u} [Zero S] (A : Matrix (Outside (pivotSet.{u} J)) (Inside (pivotSet.{u} J)) S)
    (hzero : ∀ i c, ¬ i.val.down < c.val.down → A i c = 0) :
    advancedGraph h A 0 = A := by
  ext i c
  change (if i = advancedRow.{u} h ∧ c = pivotColumn.{u} J r then 0 else A i c) = _
  split
  · rename_i h'
    obtain ⟨rfl, rfl⟩ := h'
    exact (hzero _ _ (not_lt_of_ge (advancedRow_lt.{u} h).le)).symm
  · rfl

private theorem advancedGraph_rank {J I : Fin d ↪o Fin n} {r : Fin d} (h : AdvancesPivot J I r)
    (A : Matrix (Outside (pivotSet.{u} J)) (Inside (pivotSet.{u} J)) F)
    (hzero : ∀ i c, ¬ i.val.down < c.val.down → A i c = 0)
    (a : F) (ha : a ≠ 0) (L : Plane k V d R)
    (hL : L.toSubmodule = (graphInclusion b (pivotSet.{u} J) R (advancedGraph h A a)).range) :
    ∀ j, intersectionRank β L j = pivotRank I j := by
  let P := pivotSet.{u} J
  let i := advancedRow.{u} h
  let c := pivotColumn.{u} J r
  let B := advancedGraph h A a
  have hb : B i c = a := by
    change (if i = i ∧ c = c then a else A i c) = _
    rw [ite_eq_left ⟨rfl, rfl⟩]
  obtain ⟨Q, hQset, -, hinv⟩ := pivot_exchange β P B i c (advancedRow_lt.{u} h) (hb ▸ ha)
  have hQ : Q = pivotSet.{u} I := Subtype.ext (hQset.trans (pivotSet_advance h))
  have hp : IsPivot b (pivotSet.{u} I) R L := by
    have e : L = _root_.LinearAlgebraicGroups.GrassmannianCharts.graphPlane b P R B :=
      Module.Grassmannian.ext hL
    rw [e, _root_.LinearAlgebraicGroups.GrassmannianCharts.isPivot_graphPlane_iff, ← hQ]
    exact hinv
  have hB (row : Outside P) (col : Inside P) (hlt : I ((pivotColumn J).symm col) < row.val.down) :
      B row col = 0 := by
    change (if row = i ∧ col = c then a else A row col) = _
    split
    · rename_i hd
      obtain ⟨rfl, rfl⟩ := hd
      simp only [c, Equiv.symm_apply_apply, i, advancedRow, ULift.down_up, lt_self_iff_false] at hlt
    · have he : col.val.down = J ((pivotColumn J).symm col) :=
        (congrArg (fun z : Inside P ↦ z.val.down) ((pivotColumn J).apply_symm_apply col)).symm
      apply hzero row col
      rw [he]
      exact not_lt_of_ge (((advancesPivot_le h) _).trans hlt.le)
  intro j
  exact le_antisymm (intersectionRank_le_pivotRank β I j L hp)
    (prefix_rank_of_bounded_graph β I J j (advancesPivot_le h) L B hL hB)

private def chartPointOfMatrix {Idx : Type u} (P : Pivot Idx d) (S : TestAlgebra k)
    (A : Matrix (Outside P) (Inside P) S) : Points (chartScheme (k := k) P) S :=
  (_root_.LinearAlgebraicGroups.GrassmannianCharts.chartMatrixEquiv (k := k) P S).symm A

private theorem matrixOfChartPoint {Idx : Type u} (P : Pivot Idx d) (S : TestAlgebra k)
    (A : Matrix (Outside P) (Inside P) S) : matrixOfPoint P S (chartPointOfMatrix P S A) = A := by
  rw [← _root_.LinearAlgebraicGroups.GrassmannianCharts.chartMatrixEquiv_apply]
  exact (_root_.LinearAlgebraicGroups.GrassmannianCharts.chartMatrixEquiv (k := k) P S).apply_symm_apply A


set_option maxHeartbeats 900000 in
private theorem chartPoint_subset_closure_of_advance
    (C : ChartSystem (k := k) (V := V) b d)
    {J I : Fin d ↪o Fin n} {r : Fin d} (h : AdvancesPivot J I r)
    (f : Points (chartScheme (k := k) (pivotSet.{u} J)) R)
    (hzero : ∀ i c, ¬ i.val.down < c.val.down → matrixOfPoint (pivotSet.{u} J) R f i c = 0) :
    (f ≫ C.chart (pivotSet.{u} J)).left (IsLocalRing.closedPoint F) ∈
      closure (Set.range (echelonCell β C I).left) := by
  classical
  let R₀ := R
  let P := pivotSet.{u} J
  let A : Matrix (Outside P) (Inside P) F := matrixOfPoint P R₀ f
  let M : Matrix (Outside P) (Inside P) (Polynomial F) :=
    advancedGraph h (A.map (Polynomial.C : F →+* Polynomial F)) Polynomial.X
  let p : Points (chartScheme (k := k) P) (polynomialAlgebra R₀) :=
    chartPointOfMatrix P (polynomialAlgebra R₀) M
  have hp : matrixOfPoint P (polynomialAlgebra R₀) p = M :=
    matrixOfChartPoint P (polynomialAlgebra R₀) M
  let ev := polynomialEvaluate R₀ 0
  have hspecial : mapPoints ev p = f := by
    apply (_root_.LinearAlgebraicGroups.GrassmannianCharts.chartMatrixEquiv P R₀).injective
    change matrixOfPoint P R₀ (mapPoints ev p) = A
    rw [matrixOfPoint_map, hp]
    change (advancedGraph h (A.map Polynomial.C) Polynomial.X).map ev.hom = A
    rw [advancedGraph_map h]
    have hcoeff : (A.map Polynomial.C).map ev.hom = A := by
      ext i j
      exact Polynomial.aevalTower_C _ _ _
    rw [hcoeff, show ev.hom Polynomial.X = 0 from Polynomial.aevalTower_X _ _]
    exact advancedGraph_zero h A hzero
  let K := FractionRing (Polynomial F)
  let R₁ := CommAlgCat.of k K
  let ga := polynomialFractionMap (k := k) F
  let φ : F →+* K := (algebraMap (Polynomial F) K).comp Polynomial.C
  let a : K := algebraMap (Polynomial F) K Polynomial.X
  have ha : a ≠ 0 := fun hz ↦ Polynomial.X_ne_zero
    (IsFractionRing.injective (Polynomial F) K (hz.trans (map_zero (algebraMap (Polynomial F) K)).symm))
  have hA : matrixOfPoint P R₁ (mapPoints ga p) = advancedGraph h (A.map φ) a := by
    rw [matrixOfPoint_map, hp]
    change (advancedGraph h (A.map Polynomial.C) Polynomial.X).map ga.hom = _
    rw [advancedGraph_map h]
    rfl
  have hcoeffzero (i : Outside P) (c : Inside P) (hic : ¬ i.val.down < c.val.down) :
      (A.map φ) i c = 0 := by
    rw [Matrix.map_apply, show A i c = 0 from hzero i c hic, map_zero]
  let q : Points C.scheme (polynomialAlgebra R₀) := p ≫ C.chart P
  let L := C.affinePoints.hom.app R₁ (mapPoints ga q)
  have hL : L.toSubmodule = (graphInclusion b P R₁ (advancedGraph h (A.map φ) a)).range := by
    rw [← hA]
    simpa only [L, q, mapPoints, Category.assoc] using C.coordinates_eq P R₁ (mapPoints ga p)
  have hrank := advancedGraph_rank β h (A.map φ) hcoeffzero a ha L hL
  obtain ⟨z, hz⟩ := (echelonCellRankCriterion β C I (mapPoints ga q)).mpr hrank
  have hg : (mapPoints ga q).left (IsLocalRing.closedPoint K) ∈ Set.range (echelonCell β C I).left := by
    refine ⟨z.left (IsLocalRing.closedPoint K), ?_⟩
    exact congrArg (fun t : Points C.scheme R₁ ↦ t.left (IsLocalRing.closedPoint K)) hz
  have he : mapPoints ev q = f ≫ C.chart P := by
    calc
      mapPoints ev q = mapPoints ev p ≫ C.chart P := (Category.assoc _ _ _).symm
      _ = f ≫ C.chart P := congrArg (· ≫ C.chart P) hspecial
  have hs := (polynomialFamily_specializes (F := F) q).mem_closure
  change (mapPoints ev q).left (IsLocalRing.closedPoint F) ∈
    closure {(mapPoints ga q).left (IsLocalRing.closedPoint K)} at hs
  rw [he] at hs
  exact closure_mono (Set.singleton_subset_iff.mpr hg) hs

private theorem cell_subset_closure_of_advance
    (C : ChartSystem (k := k) (V := V) b d)
    {J I : Fin d ↪o Fin n} {r : Fin d} (h : AdvancesPivot J I r) :
    Set.range (echelonCell β C J).left ⊆ closure (Set.range (echelonCell β C I).left) := by
  intro x hx
  letI := (echelonCellImmersion β C J).2.1
  letI := residueBaseAlgebra C.scheme x
  have hfactor := (residuePoint_factors_iff (echelonCell β C J) x).mpr hx
  obtain ⟨f, hf, hzero⟩ := ((echelonCellImmersion β C J).2.2.2 _ _).mp hfactor
  have hs := chartPoint_subset_closure_of_advance β C h f hzero
  rw [hf] at hs
  change C.scheme.left.fromSpecResidueField x (IsLocalRing.closedPoint
    (C.scheme.left.residueField x)) ∈ _ at hs
  have hpt : C.scheme.left.fromSpecResidueField x
      (IsLocalRing.closedPoint (C.scheme.left.residueField x)) = x :=
    C.scheme.left.fromSpecResidueField_apply x _
  exact hpt ▸ hs

private theorem cell_subset_closure_of_componentwise
    (C : ChartSystem (k := k) (V := V) b d) (I J : Fin d ↪o Fin n)
    (h : ∀ r, J r ≤ I r) :
    Set.range (echelonCell β C J).left ⊆ closure (Set.range (echelonCell β C I).left) := by
  have walk := (adjacentPivotOrder I J).mp h
  clear h
  induction walk with
  | refl => exact subset_closure
  | tail _ hstep ih =>
    obtain ⟨r, hstep⟩ := hstep
    exact ih.trans (closure_minimal (cell_subset_closure_of_advance β C hstep) isClosed_closure)

theorem echelonReducedClosure : EchelonReducedClosure.{u} := by
  intro k V _ _ _ n d β C I
  obtain ⟨hclosed, hunion⟩ := closedRankLocus β C I
  have hclosure : closure (Set.range (echelonCell β C I).left) = rankLocus β C I := by
    apply Set.Subset.antisymm
    · apply closure_minimal _ hclosed
      intro y hy
      rw [hunion]
      exact Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr ⟨fun _ ↦ le_rfl, hy⟩⟩
    · intro y hy
      rw [hunion] at hy
      obtain ⟨J, hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hJI, hy⟩ := Set.mem_iUnion.mp hy
      exact cell_subset_closure_of_componentwise β C I J hJI hy
  let D := Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure (Set.range (echelonCell β C I).left))
  change AlgebraicGeometry.IsReduced D.subscheme ∧ Set.range D.subschemeι = _
  constructor
  · apply (AlgebraicGeometry.IsReduced.iff_of_openCover _ D.subschemeCover.openCover).2
    intro U
    change AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (_ ⧸ D.ideal U)))
    rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
    exact (Scheme.IdealSheafData.vanishingIdeal_ideal _ _).symm ▸ PrimeSpectrum.isRadical_vanishingIdeal _
  · rw [Scheme.IdealSheafData.range_subschemeι]
    exact (Scheme.IdealSheafData.coe_support_vanishingIdeal _).trans hclosure

open private span_coordinateSingles from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagSchemes

set_option maxHeartbeats 650000 in
theorem echelonUpperUnitriangularOrbit : EchelonUpperUnitriangularOrbit.{u} := by
  classical
  intro k V _ _ _ n d β C I S p h
  obtain ⟨f, hf, hz⟩ := ((echelonCellImmersion β C I).2.2.2 S p).mp h
  let P := pivotSet.{u} I
  let B := FlagSchemes.liftedBasis β
  let A := matrixOfPoint P S f
  let N : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) S := Matrix.of fun i j ↦
    if hi : i ∉ P.val then if hj : j ∈ P.val then A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0
  have hN : N * N = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l ∈ P.val
    · rw [show N l j = 0 by simp [N, hl], mul_zero]
    · rw [show N i l = 0 by simp [N, hl], zero_mul]
  let g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) S :=
    { val := 1 + N
      inv := 1 - N
      val_inv := by
        rw [add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
      inv_val := by
        rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right] }
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i j hji
    have hij : i ≠ j := fun he ↦ by subst i; exact (lt_irrefl _) hji
    change (1 + N) i j = 0
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, zero_add]
    by_cases hi : i ∈ P.val
    · simp [N, hi]
    · by_cases hj : j ∈ P.val
      · change (if hi : i ∉ P.val then if hj : j ∈ P.val then
          A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) = 0
        rw [dite_eq_left hi, dite_eq_left hj]
        exact hz ⟨i, hi⟩ ⟨j, hj⟩ (not_lt_of_ge hji.le)
      · simp [N, hj]
  · intro i
    change (1 + N) i i = 1
    rw [Matrix.add_apply, Matrix.one_apply_eq]
    by_cases hi : i ∈ P.val <;> simp [N, hi]
  · have hform : (C.affinePoints.hom.app S p).toSubmodule = (graphInclusion B P S A).range := by
      rw [← hf, C.coordinates_eq]
    let e := coordinates B S
    have hcomp : e.toLinearMap.comp (graphInclusion B P S A) = graphColumns P S A := by
      apply LinearMap.ext
      intro x
      exact e.apply_symm_apply (graphColumns P S A x)
    let v (c : Inside P) : Inside P → S := Pi.single c 1
    have hspan : LinearMap.range (graphColumns P S A) =
        Submodule.span S (Set.range (fun c : Inside P ↦ graphColumns P S A (v c))) := by
      rw [← Submodule.map_top, ← (Pi.basisFun S (Inside P)).span_eq,
        Submodule.map_span, ← Set.range_comp]
      have he : (⇑(graphColumns P S A) ∘ ⇑(Pi.basisFun S (Inside P))) =
          (fun c ↦ graphColumns P S A (v c)) := by
        funext c
        rw [Function.comp_apply, Pi.basisFun_apply]
      rw [he]
    have hcolumn (c : Inside P) :
        graphColumns P S A (v c) = Matrix.toLin' g.val (Pi.single c.val (1 : S)) := by
      funext i
      rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
      have hcols : e (graphInclusion B P S A (v c)) =
          graphColumns P S A (v c) := e.apply_symm_apply _
      by_cases hi : i ∈ P.val
      · have hd := graph_coord_pivot β P S A (v c) ⟨i, hi⟩
        change e (graphInclusion B P S A (v c)) i = v c ⟨i, hi⟩ at hd
        rw [hcols] at hd
        rw [hd]
        change v c ⟨i, hi⟩ = (1 + N) i c.val
        by_cases hci : i = c.val
        · subst i
          simp [N, hi, v]
        · have hne : (⟨i, hi⟩ : Inside P) ≠ c := fun he ↦ hci (congrArg Subtype.val he)
          simp [N, hi, v, Matrix.one_apply_ne hci, Pi.single_eq_of_ne hne]
      · let row : Outside P := ⟨i, hi⟩
        have hd := graph_coord_nonpivot β P S A (v c) row
        change e (graphInclusion B P S A (v c)) i =
          ∑ a, A row a * v c a at hd
        rw [hcols, Finset.sum_eq_single c] at hd
        · rw [hd]
          change A row c * v c c = (1 + N) i c.val
          have hci : i ≠ c.val := fun he ↦ hi (he ▸ c.property)
          simp [N, hi, v, c.property, Matrix.one_apply_ne hci, row]
        · intro a _ ha
          have hv : v c a = 0 := by simp [v, ha]
          rw [hv, mul_zero]
        · simp
    rw [hform, ← LinearMap.range_comp, hcomp, hspan, ← span_coordinateSingles,
      Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Pi.single c.val (1 : S), ⟨c.val, c.property, rfl⟩, (hcolumn c).symm⟩
    · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨⟨j, hj⟩, hcolumn ⟨j, hj⟩⟩

end EchelonCells

open Specs.AdjointRepresentation (GroupPoints dualMap constants scale)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue pairing powerMorphism)
open DiagonalizableGroups (integerGenerator)
open CocharacterDynamics

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

section Characters

variable {k : Type u} [Field k]
local notation "Gm" => specGroup (groupAlgebra k IntegerCharacters)

private theorem characterValue_unitPoint (R : TestAlgebra k) (t : Rˣ) :
    (((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (unitPoint R t)).unop.hom (MonoidAlgebra.single integerGenerator 1)) = (t : R) := by
  unfold unitPoint
  rw [Functor.FullyFaithful.preimage_map]
  change unitCoordinates R t (MonoidAlgebra.single integerGenerator 1) = _
  simp [unitCoordinates, MonoidAlgebra.lift_single,
    show Multiplicative.toAdd (MulEquiv.ulift integerGenerator) = (1 : ℤ) from rfl]

private theorem characterValue_unitEquiv {T : GroupScheme k} (χ : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue χ R t = ((unitEquiv R (t ≫ χ.hom.hom) : Rˣ) : R) := by
  let s := unitEquiv R (t ≫ χ.hom.hom)
  have h : t ≫ χ.hom.hom = unitPoint R s :=
    (unitEquiv R).injective (unitEquiv_unitPoint R s).symm
  unfold characterValue
  rw [h, unitEquiv_unitPoint]
  exact characterValue_unitPoint R s

private def characterUnitHom {T : GroupScheme k} (R : TestAlgebra k)
    (t : GroupPoints T R) : Character T →* Rˣ where
  toFun χ := unitEquiv R (t ≫ χ.hom.hom)
  map_one' := by
    change unitEquiv R (t ≫ (1 : Character T).hom.hom) = _
    rw [show t ≫ (1 : Character T).hom.hom = (1 : GroupPoints Gm R) from MonObj.comp_one _, map_one]
  map_mul' χ ψ := by
    rw [show t ≫ (χ * ψ).hom.hom = (t ≫ χ.hom.hom) * (t ≫ ψ.hom.hom) from MonObj.comp_mul _ _ _, map_mul]

private theorem characterUnit_comp {S T : GroupScheme k} (g : S ⟶ T) (χ : Character T)
    (R : TestAlgebra k) (t : GroupPoints S R) :
    characterUnitHom R t (g ≫ χ) = characterUnitHom R (t ≫ g.hom.hom) χ :=
  congrArg (unitEquiv R) (Category.assoc t g.hom.hom χ.hom.hom).symm

private theorem characterValue_eq_coe {T : GroupScheme k} (χ : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue χ R t = ↑(characterUnitHom R t χ) := characterValue_unitEquiv χ R t

private theorem diagonalCharacter_unit {J : Type u} [Fintype J] [DecidableEq J]
    {G : GroupScheme k} {E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J}
    {T : ClosedSubgroup G} (a : DiagonalCharacters E T)
    (R : TestAlgebra k) (t : GroupPoints T.group R) (i : J) :
    characterUnitHom R t (a.character i) = (a.coordinates.hom.app R t : J → Rˣ) i := by
  change unitEquiv R (t ≫ (a.character i).hom.hom) = _
  rw [a.evaluates, unitEquiv_unitPoint]

end Characters

section MatrixWeights

variable {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
  {G : GroupScheme k} {E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J}
  {T : ClosedSubgroup G}

private theorem matrix_mapPoints {R S : TestAlgebra k} (f : R ⟶ S) (p : Points G.X R) :
    E.hom.app S (mapPoints f p) = Matrix.GeneralLinearGroup.map f.hom.toRingHom (E.hom.app R p) :=
  E.hom.naturality_apply f p

private theorem tangent_fst (v : Lie k G) (i j : J) :
    ((E.hom.app (CommAlgCat.of k (DualNumber k)) v.toMul.val :
      Matrix.GeneralLinearGroup J (DualNumber k)).val i j).fst = (1 : Matrix J J k) i j := by
  have h := matrix_mapPoints (E := E) (dualReduction k) v.toMul.val
  change E.hom.app (CommAlgCat.of k k)
    (((groupPointsFunctor k).obj G).map (dualReduction k) v.toMul.val) = _ at h
  rw [v.toMul.property, map_one] at h
  exact (congrArg (fun g : Matrix.GeneralLinearGroup J k ↦ g.val i j) h).symm

private theorem weight_matrix (a : DiagonalCharacters E T) (χ : Character T.group) (v : Lie k G) :
    v ∈ adjointWeightVectors T χ ↔
      ∀ (R : TestAlgebra k) (t : GroupPoints T.group R) (i j : J),
        characterValue (a.ratio i j) R t * algebraMap k R (glTangentCoefficient E v i j) =
          characterValue χ R t * algebraMap k R (glTangentCoefficient E v i j) := by
  have hpoint (R : TestAlgebra k) (t : GroupPoints T.group R) :
      let p := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val
      let g := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
      g * p * g⁻¹ = mapPoints (scale R (characterValue χ R t)) p ↔
      ∀ i j : J, characterValue (a.ratio i j) R t * algebraMap k R (glTangentCoefficient E v i j) =
          characterValue χ R t * algebraMap k R (glTangentCoefficient E v i j) := by
    let S := CommAlgCat.of k (DualNumber R)
    let f := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
    let p := mapPoints f v.toMul.val
    let z := (a.coordinates.hom.app R t : J → Rˣ)
    let g := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
    let B := (E.hom.app S p : Matrix.GeneralLinearGroup J (DualNumber R)).val
    let c := characterValue χ R t
    have hg : (E.hom.app S g : Matrix.GeneralLinearGroup J (DualNumber R)).val =
        Matrix.diagonal (fun i ↦ (constants R).hom (z i : R)) := by
      change (E.hom.app S (mapPoints (constants R) (t ≫ T.inclusion.hom.hom)) :
        Matrix.GeneralLinearGroup J (DualNumber R)).val = _
      rw [matrix_mapPoints]
      change (E.hom.app R (t ≫ T.inclusion.hom.hom) :
        Matrix.GeneralLinearGroup J R).val.map (constants R).hom = _
      rw [a.diagonal, Matrix.diagonal_map (map_zero (constants R).hom)]
    have hb (i j : J) : (B i j).snd = algebraMap k R (glTangentCoefficient E v i j) := by
      change ((E.hom.app S (mapPoints f v.toMul.val) : Matrix.GeneralLinearGroup J (DualNumber R)).val i j).snd = _
      rw [matrix_mapPoints]
      rfl
    have hb₀ (i j : J) (hij : i ≠ j) : (B i j).fst = 0 := by
      change ((E.hom.app S (mapPoints f v.toMul.val) : Matrix.GeneralLinearGroup J (DualNumber R)).val i j).fst = _
      rw [matrix_mapPoints]
      change algebraMap k R (((E.hom.app (CommAlgCat.of k (DualNumber k)) v.toMul.val :
        Matrix.GeneralLinearGroup J (DualNumber k)).val i j).fst) = 0
      rw [tangent_fst, Matrix.one_apply_ne hij, map_zero]
    have hr (i j : J) : characterValue (a.ratio i j) R t * (z j : R) = (z i : R) := by
      rw [characterValue_unitEquiv]
      change ((characterUnitHom R t (a.ratio i j) : Rˣ) : R) * (z j : R) = _
      rw [DiagonalCharacters.ratio, map_div, diagonalCharacter_unit, diagonalCharacter_unit]
      exact congrArg Units.val (div_mul_cancel (z i : Rˣ) (z j))
    change g * p * g⁻¹ = mapPoints (scale R c) p ↔ _
    rw [mul_inv_eq_iff_eq_mul]
    have hscale : E.hom.app S (mapPoints (scale R c) p) =
        Matrix.GeneralLinearGroup.map (scale R c).hom.toRingHom (E.hom.app S p) :=
      matrix_mapPoints (E := E) (scale R c) p
    have hM : g * p = mapPoints (scale R c) p * g ↔
        ∀ i j : J, (constants R).hom (z i : R) * B i j =
          (scale R c).hom (B i j) * (constants R).hom (z j : R) := by
      constructor
      · intro h i j
        have hh := congrArg (fun x ↦ E.hom.app S x) h
        rw [map_mul, map_mul, hscale] at hh
        have hh := congrArg (fun x : Matrix.GeneralLinearGroup J (DualNumber R) ↦ x.val i j) hh
        change ((E.hom.app S g : Matrix.GeneralLinearGroup J (DualNumber R)).val * B) i j =
          (B.map (scale R c).hom * (E.hom.app S g : Matrix.GeneralLinearGroup J (DualNumber R)).val) i j at hh
        rwa [hg, Matrix.diagonal_mul, Matrix.mul_diagonal] at hh
      · intro h
        apply (E.app S).groupIsoToMulEquiv.injective
        change E.hom.app S (g * p) = E.hom.app S (mapPoints (scale R c) p * g)
        rw [map_mul, map_mul, hscale]
        apply Units.ext
        apply Matrix.ext
        intro i j
        change ((E.hom.app S g : Matrix.GeneralLinearGroup J (DualNumber R)).val * B) i j =
          (B.map (scale R c).hom * (E.hom.app S g : Matrix.GeneralLinearGroup J (DualNumber R)).val) i j
        rw [hg, Matrix.diagonal_mul, Matrix.mul_diagonal]
        exact h i j
    rw [hM]
    constructor
    · intro h i j
      have hs := congrArg (fun x : DualNumber R ↦ x.snd) (h i j)
      change (z i : R) * (B i j).snd + 0 * (B i j).fst =
        (B i j).fst * 0 + (c * (B i j).snd) * (z j : R) at hs
      simp only [zero_mul, mul_zero, add_zero, zero_add] at hs
      rw [← hb]
      apply (z j).mul_left_inj.mp
      calc
        (characterValue (a.ratio i j) R t * (B i j).snd) * (z j : R) =
            (characterValue (a.ratio i j) R t * (z j : R)) * (B i j).snd := by ring
        _ = _ := by rw [hr]; exact hs
    · intro h i j
      apply TrivSqZeroExt.ext
      · change (z i : R) * (B i j).fst = (B i j).fst * (z j : R)
        by_cases hij : i = j
        · subst j
          exact mul_comm _ _
        · rw [hb₀ i j hij, mul_zero, zero_mul]
      · change (z i : R) * (B i j).snd + 0 * (B i j).fst =
          (B i j).fst * 0 + (c * (B i j).snd) * (z j : R)
        simp only [zero_mul, mul_zero, add_zero, zero_add]
        rw [← hr, mul_right_comm, hb, h i j]
  exact ⟨fun h R t ↦ (hpoint R t).mp (h R t), fun h R t ↦ (hpoint R t).mpr (h R t)⟩


private theorem lie_upper_triangular {n : ℕ} {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (B : ClosedSubgroup G)
    (hB : ∀ (R : TestAlgebra k) (g : Points G.X R),
      g ∈ SubgroupSections B ((testSpec k).obj (op R)) ↔
        ∀ (i j : ULift.{u} (Fin n)), j.down < i.down →
          (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0)
    (v : Lie k G) :
    v ∈ _root_.LinearAlgebraicGroups.CocharacterDynamics.lieImage B ↔
      ∀ (i j : ULift.{u} (Fin n)), j.down < i.down → glTangentCoefficient E v i j = 0 := by
  let S := CommAlgCat.of k (DualNumber k)
  let R := CommAlgCat.of k k
  have hcoeff : v.toMul.val ∈ SubgroupSections B ((testSpec k).obj (op S)) ↔
      ∀ (i j : ULift.{u} (Fin n)), j.down < i.down → glTangentCoefficient E v i j = 0 := by
    rw [hB]
    constructor
    · intro h i j hji
      exact congrArg (fun x : DualNumber k ↦ x.snd) (h i j hji)
    · intro h i j hji
      apply TrivSqZeroExt.ext
      · rw [tangent_fst, Matrix.one_apply_ne (fun he ↦ (ne_of_gt hji) (congrArg ULift.down he))]
        rfl
      · exact h i j hji
  refine Iff.trans ?_ hcoeff
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.toMul.val, congrArg (fun q : Lie k G ↦ q.toMul.val) hw⟩
  · rintro ⟨p, hp⟩
    let p' : GroupPoints B.group S := p
    change p' ≫ B.inclusion.hom.hom = v.toMul.val at hp
    have hk : ((groupPointsFunctor k).obj B.group).map (dualReduction k) p' = 1 := by
      let f := (groupPointsFunctor k).map B.inclusion
      apply pointHom_injective B R
      change f.app R (((groupPointsFunctor k).obj B.group).map (dualReduction k) p') = f.app R 1
      rw [f.naturality_apply (dualReduction k) p', map_one]
      change ((groupPointsFunctor k).obj G).map (dualReduction k) (p' ≫ B.inclusion.hom.hom) = 1
      rw [hp]
      exact v.toMul.property
    exact ⟨⟨p', hk⟩, Subtype.ext hp⟩

private theorem laurent_T_injective (k : Type u) [Field k] :
    Function.Injective (LaurentPolynomial.T (R := k)) := by
  intro m n h
  by_contra hne
  have he := congrArg (fun f : LaurentPolynomial k ↦ f.coeff n) h
  simp [LaurentPolynomial.T_apply, hne] at he

private theorem charValue_ratio (a : DiagonalCharacters E T) (R : TestAlgebra k)
    (t : GroupPoints T.group R) (i j : J) :
    characterValue (a.ratio i j) R t =
      (((a.coordinates.hom.app R t : J → Rˣ) i / (a.coordinates.hom.app R t : J → Rˣ) j : Rˣ) : R) := by
  rw [characterValue_unitEquiv]
  change ((characterUnitHom R t (a.ratio i j) : Rˣ) : R) = _
  rw [DiagonalCharacters.ratio, map_div, diagonalCharacter_unit, diagonalCharacter_unit]

private theorem matrix_character_ratios (a : DiagonalCharacters E T)
    {χ : Character T.group} (hT : GeometricRadicals.IsSplitTorus T.group)
    {v : Lie k G} (hv : v ∈ adjointWeightVectors T χ) {i j : J}
    (hij : glTangentCoefficient E v i j ≠ 0) : χ = a.ratio i j := by
  apply RootData.CharacterPairing.characterValuesDetectCharacters hT
  intro R t
  have h := (weight_matrix a χ v).mp hv R t i j
  exact (((isUnit_iff_ne_zero.mpr hij).map (algebraMap k R)).mul_left_inj.mp h).symm

end MatrixWeights

section MatrixRoots

variable {k : Type u} [Field k] {n : ℕ} (G : AffineAlgebraicGroup k)
variable (E : (groupPointsFunctor k).obj G.val ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
  (T B : ClosedSubgroup G.val)

private theorem typeAMatrixRootsAux (a : DiagonalCharacters E T)
    (hT : GeometricRadicals.IsSplitTorus T.group)
    (hB : ∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ∈ SubgroupSections B ((testSpec k).obj (op R)) ↔
        ∀ (i j : (ULift.{u} (Fin n))), j.down < i.down → (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0)
    (ratio_ne_one : ∀ i j, i ≠ j → a.ratio i j ≠ 1)
    (ratio_inj : ∀ {i j p q : (ULift.{u} (Fin n))}, i ≠ j → p ≠ q → a.ratio i j = a.ratio p q → i = p ∧ j = q) :
    (∀ χ, χ ∈ absoluteRoots T ↔ ∃ i j, i ≠ j ∧ χ = a.ratio i j) ∧
    ∀ α : AbstractPairing.Root T, α ∈ BorelsAndChambers.subgroupRoots T B ↔
      ∃ (i j : (ULift.{u} (Fin n))), i.down < j.down ∧ α.val = a.ratio i j := by
  let s := LinearAlgebraicGroups.identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨d, hd, _⟩ := LinearAlgebraicGroups.lieGeneralLinear k (ULift.{u} (Fin n)) G E s
  have single_weight (i j : (ULift.{u} (Fin n))) :
      ∃ v : Lie k G.val, v ∈ adjointWeightVectors T (a.ratio i j) ∧
        glTangentCoefficient E v = Matrix.single i j 1 := by
    let v := d.symm (Matrix.single i j 1)
    have hv : glTangentCoefficient E v = Matrix.single i j 1 := (hd v).symm.trans (d.apply_symm_apply _)
    refine ⟨v, (weight_matrix a _ v).mpr (fun R t p q ↦ ?_), hv⟩
    rw [hv]
    by_cases h : p = i ∧ q = j
    · obtain ⟨rfl, rfl⟩ := h
      rfl
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h' ↦ h ⟨h'.1.symm, h'.2.symm⟩), map_zero, mul_zero, mul_zero]
  have abs_iff (χ : Character T.group) : χ ∈ absoluteRoots T ↔ ∃ i j, i ≠ j ∧ χ = a.ratio i j := by
    constructor
    · rintro ⟨hχ, v, hv, hn⟩
      have hm : glTangentCoefficient E v ≠ 0 := by
        intro hm
        apply hn
        exact d.injective ((hd v).trans (hm.trans d.map_zero.symm))
      have h : ∃ i j, glTangentCoefficient E v i j ≠ 0 := by
        by_contra! hz
        exact hm (Matrix.ext hz)
      obtain ⟨i, j, hij⟩ := h
      have h := matrix_character_ratios a hT hv hij
      refine ⟨i, j, ?_, h⟩
      intro he
      subst j
      exact hχ (h.trans (by simp [DiagonalCharacters.ratio]))
    · rintro ⟨i, j, hij, rfl⟩
      obtain ⟨v, hv, hm⟩ := single_weight i j
      refine ⟨ratio_ne_one i j hij, v, hv, ?_⟩
      intro he
      have hd' : (d v) i j = 1 := by rw [hd, hm, Matrix.single_apply_same]
      rw [he, d.map_zero] at hd'
      exact zero_ne_one hd'
  refine ⟨abs_iff, fun α ↦ ?_⟩
  constructor
  · intro h
    obtain ⟨i, j, hij, hα⟩ := (abs_iff α.val).mp α.property
    obtain ⟨v, hv, hm⟩ := single_weight i j
    have hu := (lie_upper_triangular E B hB v).mp (h (hα.symm ▸ hv))
    refine ⟨i, j, lt_of_le_of_ne (le_of_not_gt fun hji ↦ ?_) (fun he ↦ hij (ULift.down_injective he)), hα⟩
    exact one_ne_zero ((Matrix.single_apply_same _ _ _).symm.trans (congrArg (fun M : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) k ↦ M i j) hm.symm |>.trans (hu i j hji)))
  · rintro ⟨i, j, hij, hα⟩ v hv
    apply (lie_upper_triangular E B hB v).mpr
    intro p q hqp
    by_contra he
    have h := (matrix_character_ratios a hT hv he).symm.trans hα
    obtain ⟨hp, hq⟩ := ratio_inj (fun he ↦ (ne_of_gt hqp) (congrArg ULift.down he))
      (fun he ↦ (ne_of_lt hij) (congrArg ULift.down he)) h
    exact (lt_asymm hij) (hp ▸ hq ▸ hqp)

end MatrixRoots

section CoordinateDistinction

variable {k J : Type u} [Field k] [Fintype J] [DecidableEq J] {G : GroupScheme k}
  {E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J}
  {T : ClosedSubgroup G}

private def coordinateTest (a : DiagonalCharacters E T) (l : J) :
    GroupPoints T.group (laurentAlgebra (CommAlgCat.of k k)) :=
  a.coordinates.inv.app _ (fun i ↦ if i = l then laurentParameter (CommAlgCat.of k k) else 1)

private theorem coordinateTest_value (a : DiagonalCharacters E T) (i l : J) :
    characterValue (a.character i) _ (coordinateTest a l) =
      LaurentPolynomial.T (R := k) (if i = l then 1 else 0) := by
  rw [characterValue_unitEquiv]
  change ((characterUnitHom _ _ (a.character i) : (laurentAlgebra (CommAlgCat.of k k))ˣ) :
    LaurentPolynomial k) = _
  rw [diagonalCharacter_unit]
  have h := (a.coordinates.app (laurentAlgebra (CommAlgCat.of k k))).groupIsoToMulEquiv.apply_symm_apply
    (fun j : J ↦ if j = l then laurentParameter (CommAlgCat.of k k) else 1)
  change a.coordinates.hom.app _ (coordinateTest a l) = _ at h
  rw [h]
  by_cases hil : i = l <;> simp [hil, laurentParameter]

private theorem coordinateTest_ratio (a : DiagonalCharacters E T) (i j l : J) :
    characterValue (a.ratio i j) _ (coordinateTest a l) =
      LaurentPolynomial.T (R := k) ((if i = l then 1 else 0) - (if j = l then 1 else 0)) := by
  let R := laurentAlgebra (CommAlgCat.of k k)
  let z := (a.coordinates.hom.app R (coordinateTest a l) : J → Rˣ)
  have hi (p : J) : (z p : R) = LaurentPolynomial.T (R := k) (if p = l then 1 else 0) := by
    change ((a.coordinates.hom.app R (coordinateTest a l) : J → Rˣ) p : R) = _
    rw [← diagonalCharacter_unit, ← characterValue_eq_coe, coordinateTest_value]
  rw [charValue_ratio]
  change (↑(z i / z j) : R) = _
  apply (z j).mul_left_inj.mp
  rw [← Units.val_mul, div_mul_cancel, hi, hi, ← LaurentPolynomial.T_add, sub_add_cancel]

private theorem diagonal_characters_injective (a : DiagonalCharacters E T) :
    Function.Injective a.character := by
  intro i j h
  by_contra hne
  have h := congrArg (fun χ ↦ characterValue χ _ (coordinateTest a i)) h
  rw [coordinateTest_value, coordinateTest_value] at h
  have hp := laurent_T_injective k h
  exact hne (show j = i by simpa using hp).symm

private theorem ratio_ne_one (a : DiagonalCharacters E T) (i j : J) (h : i ≠ j) :
    a.ratio i j ≠ 1 := by
  intro he
  exact h (diagonal_characters_injective a (div_eq_one.mp he))

private theorem ratio_injective (a : DiagonalCharacters E T) {i j p q : J}
    (hij : i ≠ j) (_hpq : p ≠ q) (h : a.ratio i j = a.ratio p q) : i = p ∧ j = q := by
  have he (l : J) := congrArg (fun χ ↦ characterValue χ _ (coordinateTest a l)) h
  have eq (l : J) := laurent_T_injective k (by simpa only [coordinateTest_ratio] using he l)
  have hi : p = i := by
    by_contra hn
    have hs := eq i
    by_cases hq : q = i <;> simp [hij.symm, hn, hq] at hs
  have hj : q = j := by
    by_contra hn
    have hs := eq j
    by_cases hp : p = j <;> simp [hij, hn, hp] at hs
  exact ⟨hi.symm, hj.symm⟩

end CoordinateDistinction

private theorem diagonal_character_pairings {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
    {G : GroupScheme k} {E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J}
    {T : ClosedSubgroup G} (a : DiagonalCharacters E T) (c : Cocharacter T.group)
    (R : TestAlgebra k) (t : Rˣ) :
    (E.hom.app R (cocharacterPoint (c ≫ T.inclusion) R t) : Matrix.GeneralLinearGroup J R).val =
      Matrix.diagonal (fun i ↦ ((t ^ pairing T.group (a.character i) c : Rˣ) : R)) := by
  change (E.hom.app R (cocharacterPoint c R t ≫ T.inclusion.hom.hom) : Matrix.GeneralLinearGroup J R).val = _
  rw [a.diagonal]
  congr 1
  funext i
  rw [← diagonalCharacter_unit, ← characterValue_eq_coe]
  exact (RootData.CharacterPairing.characterPairingComposition T.group (a.character i) c).2 R t

private theorem coordinate_pairings_eq {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
    {G : GroupScheme k} {E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J}
    {T : ClosedSubgroup G} (a : DiagonalCharacters E T) (c : Cocharacter T.group) (w : J → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : Rˣ),
      (E.hom.app R (cocharacterPoint (c ≫ T.inclusion) R t) : Matrix.GeneralLinearGroup J R).val =
        Matrix.diagonal (fun i ↦ ((t ^ w i : Rˣ) : R))) (i : J) :
    pairing T.group (a.character i) c = w i := by
  let R := CommAlgCat.of k k
  have he := congrArg (fun M : Matrix J J (LaurentPolynomial k) ↦ M i i)
    ((diagonal_character_pairings a c (laurentAlgebra R) (laurentParameter R)).symm.trans
      (h (laurentAlgebra R) (laurentParameter R)))
  simp only [Matrix.diagonal_apply_eq] at he
  rw [laurentParameter_zpow R, laurentParameter_zpow R] at he
  exact laurent_T_injective k he

section SimpleRoots

open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.SimpleRoots (evaluate IsBaseFor positive)

variable {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
variable {E : (groupPointsFunctor k).obj G.val ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n))}
  {T B : ClosedSubgroup G.val}

private theorem evaluate_root [IsCommMonObj T.group.X] (D : Datum T) (c : Cocharacter T.group) (α : Root T) :
    evaluate D c (D.rootDatum.root α) = pairing T.group α.val c := by
  change D.rootDatum.toLinearMap (D.rootDatum.root α) (Additive.ofMul c) = _
  rw [D.root_eq, D.pairing_eq]

private theorem pairing_ratio [IsCommMonObj T.group.X] (D : Datum T) (a : DiagonalCharacters E T)
    (c : Cocharacter T.group) (i j : (ULift.{u} (Fin n))) :
    pairing T.group (a.ratio i j) c = pairing T.group (a.character i) c - pairing T.group (a.character j) c := by
  rw [← D.pairing_eq, ← D.pairing_eq, ← D.pairing_eq]
  change evaluate D c (Additive.ofMul (a.ratio i j)) =
    evaluate D c (Additive.ofMul (a.character i)) - evaluate D c (Additive.ofMul (a.character j))
  exact map_sub (evaluate D c) (Additive.ofMul (a.character i)) (Additive.ofMul (a.character j))

private theorem root_positive_iff [IsCommMonObj T.group.X] (D : Datum T) (c : Cocharacter T.group)
    (hc : positiveRoots T c = subgroupRoots T B) (α : Root T) :
    α ∈ positive D.rootDatum (evaluate D c) ↔ α ∈ subgroupRoots T B := by
  change (0 < evaluate D c (D.rootDatum.root α)) ↔ _
  rw [evaluate_root]
  exact Set.ext_iff.mp hc α

private theorem typeA_simple_roots [IsCommMonObj T.group.X] (D : Datum T)
    (a : DiagonalCharacters E T)
    (hT : ∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔
        ∀ i j, i ≠ j → (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0)
    (habs : ∀ χ, χ ∈ absoluteRoots T ↔ ∃ i j, i ≠ j ∧ χ = a.ratio i j)
    (hpos : ∀ α : Root T, α ∈ subgroupRoots T B ↔ ∃ (i j : (ULift.{u} (Fin n))), i.down < j.down ∧ α.val = a.ratio i j)
    (c : Cocharacter T.group) (b : D.rootDatum.Base)
    (hc : positiveRoots T c = subgroupRoots T B) (hb : IsBaseFor D.rootDatum (evaluate D c) b)
    (α : Root T) : α ∈ b.support ↔ ∃ (i j : (ULift.{u} (Fin n))), j.down.val = i.down.val + 1 ∧ α.val = a.ratio i j := by
  obtain ⟨c₀, hc₀⟩ := diagonalCocharacterInTorus E T hT (fun i ↦ -(i.down.val : ℤ))
  have heval {β : Root T} {i j : (ULift.{u} (Fin n))} (hβ : β.val = a.ratio i j) :
      evaluate D c₀ (D.rootDatum.root β) = (j.down.val : ℤ) - (i.down.val : ℤ) := by
    rw [evaluate_root, hβ, pairing_ratio D, coordinate_pairings_eq a c₀ _ hc₀,
      coordinate_pairings_eq a c₀ _ hc₀]
    omega
  rw [hb.simple_iff]
  constructor
  · rintro ⟨hα, indecomposable⟩
    obtain ⟨i, j, hij, hα⟩ := (hpos α).mp ((root_positive_iff D c hc α).mp hα)
    refine ⟨i, j, ?_, hα⟩
    by_contra hne
    let m : (ULift.{u} (Fin n)) := ULift.up ⟨i.down.val + 1, by omega⟩
    have him : i.down < m.down := by change i.down.val < i.down.val + 1; omega
    have hmj : m.down < j.down := by change i.down.val + 1 < j.down.val; omega
    let β : Root T := ⟨a.ratio i m, (habs _).mpr ⟨i, m, fun h ↦ (ne_of_lt him) (congrArg ULift.down h), rfl⟩⟩
    let rootRight : Root T := ⟨a.ratio m j, (habs _).mpr ⟨m, j, fun h ↦ (ne_of_lt hmj) (congrArg ULift.down h), rfl⟩⟩
    apply indecomposable β ((root_positive_iff D c hc β).mpr ((hpos β).mpr ⟨i, m, him, rfl⟩))
      rootRight ((root_positive_iff D c hc rootRight).mpr ((hpos rootRight).mpr ⟨m, j, hmj, rfl⟩))
    rw [D.root_eq, D.root_eq, D.root_eq, hα]
    change a.ratio i j = a.ratio i m * a.ratio m j
    simp [DiagonalCharacters.ratio, div_mul_div_cancel]
  · rintro ⟨i, j, hj, hα⟩
    have hij : i.down < j.down := by omega
    refine ⟨(root_positive_iff D c hc α).mpr ((hpos α).mpr ⟨i, j, hij, hα⟩), ?_⟩
    intro β hβ rootRight hγ hsum
    obtain ⟨p, q, hpq, hβ⟩ := (hpos β).mp ((root_positive_iff D c hc β).mp hβ)
    obtain ⟨r, s, hrs, hγ⟩ := (hpos rootRight).mp ((root_positive_iff D c hc rootRight).mp hγ)
    have hf := congrArg (evaluate D c₀) hsum
    rw [map_add, heval hα, heval hβ, heval hγ] at hf
    omega

end SimpleRoots

section BlockFaces

open Specs.AbstractPairing (Datum Root)
open Specs.StandardParabolicLevi (HasFace StandardParabolic)
open Specs.OrderedRootProducts (RootSubgroupFamily)

private theorem decreasing_across_cuts {n m : ℕ} (ranks : Fin m → ℕ) (w : Fin n → ℤ)
    (h : ∀ i j : Fin n, j.val = i.val + 1 →
      w j ≤ w i ∧ (w j < w i ↔ ∃ a, ranks a = j.val)) (i j : Fin n) :
    w i < w j ↔ ∃ a, j.val < ranks a ∧ ranks a ≤ i.val := by
  have hw : Antitone w := by
    cases n with
    | zero => exact fun i ↦ Fin.elim0 i
    | succ n => exact Fin.antitone_iff_succ_le.mpr (fun p ↦ (h p.castSucc p.succ rfl).1)
  constructor
  · intro hlt
    have hji : j ≤ i := le_of_not_gt fun hij ↦ hlt.not_ge (hw hij.le)
    by_contra! hnocut
    have he (p : ℕ) (hp : j.val ≤ p) (hpi : p ≤ i.val) :
        w ⟨p, hpi.trans_lt i.isLt⟩ = w j := by
      induction p, hp using Nat.le_induction with
      | base => rfl
      | succ p hp ih =>
        let x : Fin n := ⟨p, by omega⟩
        let y : Fin n := ⟨p + 1, by omega⟩
        have hn : ¬ ∃ a, ranks a = y.val := by
          rintro ⟨a, ha⟩
          have hlt' : j.val < ranks a := by change ranks a = p + 1 at ha; omega
          have := hnocut a hlt'
          change ranks a = p + 1 at ha
          omega
        have heq : w y = w x := le_antisymm (h x y rfl).1 (le_of_not_gt ((h x y rfl).2.not.mpr hn))
        exact heq.trans (ih (by omega))
    exact hlt.ne (he i.val hji le_rfl)
  · rintro ⟨a, hj, hi⟩
    let x : Fin n := ⟨ranks a - 1, by omega⟩
    let y : Fin n := ⟨ranks a, hi.trans_lt i.isLt⟩
    have hxy : y.val = x.val + 1 := by dsimp [x, y]; omega
    have hiy : y ≤ i := hi
    have hjx : j ≤ x := by change j.val ≤ ranks a - 1; omega
    exact (hw hiy).trans_lt (((h x y hxy).2.mpr ⟨a, rfl⟩).trans_le (hw hjx))

variable {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
variable {E : (groupPointsFunctor k).obj G.val ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n))}
  {T B : ClosedSubgroup G.val} [IsCommMonObj T.group.X]

private theorem hasFace_blockExponent (D : Datum T) {b : D.rootDatum.Base} (a : DiagonalCharacters E T)
    (hsimple : ∀ α : Root T, α ∈ b.support ↔ ∃ (i j : (ULift.{u} (Fin n))), j.down.val = i.down.val + 1 ∧ α.val = a.ratio i j)
    {m : ℕ} (ranks : Fin m → ℕ) (c : Cocharacter T.group)
    (hc : ∀ (R : TestAlgebra k) (t : Rˣ),
      (E.hom.app R (cocharacterPoint (c ≫ T.inclusion) R t) : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val =
        Matrix.diagonal (fun i ↦ ((t ^ blockExponent ranks i.down : Rˣ) : R))) :
    HasFace b (uncutSimpleRoots a ranks) c := by
  have hp (i j : (ULift.{u} (Fin n))) : pairing T.group (a.ratio i j) c =
      blockExponent ranks i.down - blockExponent ranks j.down := by
    rw [pairing_ratio D, coordinate_pairings_eq a c _ hc, coordinate_pairings_eq a c _ hc]
  constructor
  · rintro α ⟨i, j, hj, hα, hcut⟩
    rw [hα, hp]
    apply sub_eq_zero.mpr
    apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      obtain ⟨s, hs, ht⟩ := (blockExponentOrder ranks j.down i.down).mp hlt
      exact hcut s (by omega)
    · apply le_of_not_gt
      intro hlt
      obtain ⟨s, hs, ht⟩ := (blockExponentOrder ranks i.down j.down).mp hlt
      omega
  · intro α hα
    obtain ⟨i, j, hj, hr⟩ := (hsimple α).mp hα.1
    rw [hr, hp, sub_pos]
    apply (blockExponentOrder ranks j.down i.down).mpr
    by_contra! hne
    exact hα.2 ⟨i, j, hj, hr, fun s h ↦ by have := hne s (by omega); omega⟩

private theorem face_matrix_equations (D : Datum T) {b : D.rootDatum.Base} (a : DiagonalCharacters E T)
    (habs : ∀ χ, χ ∈ absoluteRoots T ↔ ∃ i j, i ≠ j ∧ χ = a.ratio i j)
    (hsimple : ∀ α : Root T, α ∈ b.support ↔ ∃ (i j : (ULift.{u} (Fin n))), j.down.val = i.down.val + 1 ∧ α.val = a.ratio i j)
    {m : ℕ} (ranks : Fin m → ℕ) (c : Cocharacter T.group) (hc : HasFace b (uncutSimpleRoots a ranks) c)
    (L : LimitDecomposition (c ≫ T.inclusion)) (R : TestAlgebra k) (g : Points G.val.X R) :
    g ∈ SubgroupSections L.parabolic ((testSpec k).obj (op R)) ↔
      ∀ (r : Fin m) (i j : (ULift.{u} (Fin n))), j.down.val < ranks r → ranks r ≤ i.down.val →
        (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0 := by
  let w (i : Fin n) := pairing T.group (a.character (ULift.up i)) c
  have hl (S : TestAlgebra k) :
      E.hom.app (laurentAlgebra S) (cocharacterPoint (c ≫ T.inclusion) (laurentAlgebra S)
        (laurentParameter S)) = laurentDiagonal S (fun i : (ULift.{u} (Fin n)) ↦ w i.down) := by
    apply Units.ext
    rw [diagonal_character_pairings]
    exact congrArg Matrix.diagonal (funext (fun i : (ULift.{u} (Fin n)) ↦ laurentParameter_zpow S (w i.down)))
  have hw (i j : Fin n) (hj : j.val = i.val + 1) :
      w j ≤ w i ∧ (w j < w i ↔ ∃ r, ranks r = j.val) := by
    let p : (ULift.{u} (Fin n)) := ULift.up i
    let q : (ULift.{u} (Fin n)) := ULift.up j
    have hpq : p ≠ q := by intro h; have he := congrArg (fun a : (ULift.{u} (Fin n)) ↦ a.down.val) h; change i.val = j.val at he; omega
    let α : Root T := ⟨a.ratio p q, (habs _).mpr ⟨p, q, hpq, rfl⟩⟩
    have hs : α ∈ b.support := (hsimple α).mpr ⟨p, q, hj, rfl⟩
    have hp : pairing T.group α.val c = w i - w j := pairing_ratio D a c p q
    by_cases hcut : ∃ r, ranks r = j.val
    · obtain ⟨r, hr⟩ := hcut
      have hn : α ∉ uncutSimpleRoots a ranks := by
        rintro ⟨p', q', hj', he, hnot⟩
        have hne : p' ≠ q' := by intro h; subst q'; omega
        obtain ⟨_, hq⟩ := ratio_injective a hpq hne he
        exact hnot r (by rw [← hq]; exact hr)
      have hlt := hc.2 α ⟨hs, hn⟩
      rw [hp, sub_pos] at hlt
      exact ⟨hlt.le, iff_of_true hlt ⟨r, hr⟩⟩
    · have hzero := hc.1 α ⟨p, q, hj, rfl, fun r hr ↦ hcut ⟨r, hr⟩⟩
      rw [hp, sub_eq_zero] at hzero
      exact ⟨hzero.ge, iff_of_false (by rw [hzero]; exact lt_irrefl _) hcut⟩
  refine (limitGroupMatrixEquations E _ _ hl L R g).trans ?_
  constructor
  · intro hz r i j hj hi
    exact hz i j ((decreasing_across_cuts ranks w hw i.down j.down).mpr ⟨r, hj, hi⟩)
  · intro hz i j hlt
    obtain ⟨r, hj, hi⟩ := (decreasing_across_cuts ranks w hw i.down j.down).mp hlt
    exact hz r i j hj hi

end BlockFaces

private theorem diagonalCharactersOfMatrices {k J : Type u} [Field k] [Fintype J] [DecidableEq J]
    {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k J)
    (T : ClosedSubgroup G) (hG : IsAffine G.X.left)
    (hT : ∀ (R : TestAlgebra k) (g : Points G.X R),
      g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔
        ∀ i j, i ≠ j → (E.hom.app R g : Matrix.GeneralLinearGroup J R).val i j = 0) :
    Nonempty (DiagonalCharacters E T) := by
  obtain ⟨a, χ, h, hχ⟩ := diagonalCoordinateCharacters E T hG hT
  exact ⟨⟨a, χ, h, hχ⟩⟩

theorem canonicalTypeAPair : CanonicalTypeAPair.{u} := by
  classical
  intro k _ n hn G E
  obtain ⟨T, B, hT, hB, hsplit, hin, _, _, _, _, hTc, hBc, hmax, hb⟩ :=
    _root_.LinearAlgebraicGroups.GeneralLinearStructure.generalLinearBorelPair k n hn G E
  have hB' (R : TestAlgebra k) (g : Points G.val.X R) :
      g ∈ SubgroupSections B ((testSpec k).obj (op R)) ↔
        ∀ (i j : ULift.{u} (Fin n)), j.down < i.down →
          (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0 := hB R g
  obtain ⟨a⟩ := diagonalCharactersOfMatrices E T G.property.1 hT
  obtain ⟨ha, hp⟩ := typeAMatrixRootsAux G E T B a hsplit hB' (ratio_ne_one a)
    (fun hi hj he ↦ ratio_injective a hi hj he)
  refine ⟨⟨T, B, _root_.LinearAlgebraicGroups.GeneralLinearStructure.generalLinearReductive k n hn G E,
    hsplit, ⟨hTc, hmax⟩, ⟨hBc, ⟨hb.1, hb.2.1, hb.2.2.1⟩, ?_⟩, hin, hT, hB', a, ha, hp⟩⟩
  exact fun X hX ↦ hb.2.2.2 X hX.1 hX.2.1 hX.2.2

theorem typeAMatrixRoots : TypeAMatrixRoots.{u} := by
  intro k _ n G E T B hsplit hT hB
  obtain ⟨a⟩ := diagonalCharactersOfMatrices E T G.property.1 hT
  exact ⟨a, typeAMatrixRootsAux G E T B a hsplit hB (ratio_ne_one a)
    (fun hi hj he ↦ ratio_injective a hi hj he)⟩

theorem typeASimpleRoots : TypeASimpleRoots.{u} := by
  intro k _ n G E M h D c b hc hb α
  exact typeA_simple_roots D M.characters M.diagonal M.absolute M.positive c b hc hb α

theorem typeABlockCuts : TypeABlockCuts.{u} := by
  classical
  intro k _ n G E M h D c b hc hb I hI
  have hs α := typeASimpleRoots M D c b hc hb α
  let cuts := (Finset.univ : Finset (Fin n)).filter fun j ↦
    ∃ α : Specs.AbstractPairing.Root M.torus, α ∈ b.support ∧ α ∉ I ∧
      ∃ i : Fin n, j.val = i.val + 1 ∧ α.val = M.characters.ratio (ULift.up i) (ULift.up j)
  let f := cuts.orderEmbOfFin rfl
  let ranks (r : Fin cuts.card) := (f r).val
  have hj (j : Fin n) : (∃ r, ranks r = j.val) ↔ j ∈ cuts := by
    have hm := Finset.range_orderEmbOfFin cuts rfl
    constructor
    · rintro ⟨r, hr⟩
      have he : f r = j := Fin.ext hr
      change j ∈ (cuts : Set (Fin n))
      rw [← hm]
      exact ⟨r, he⟩
    · intro h
      obtain ⟨r, hr⟩ : j ∈ Set.range f := by rw [hm]; exact h
      exact ⟨r, congrArg Fin.val hr⟩
  have hmem (j : Fin n) : j ∈ cuts ↔
      ∃ α : Specs.AbstractPairing.Root M.torus, α ∈ b.support ∧ α ∉ I ∧
        ∃ i : Fin n, j.val = i.val + 1 ∧ α.val = M.characters.ratio (ULift.up i) (ULift.up j) := by
    simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨cuts.card, ranks, fun _ _ h ↦ f.strictMono h, fun r ↦ ⟨?_, (f r).isLt⟩, ?_⟩
  · obtain ⟨α, _, _, i, hi, _⟩ := (hmem (f r)).mp ((hj (f r)).mp ⟨r, rfl⟩)
    change 0 < (f r).val
    omega
  · ext α
    constructor
    · rintro ⟨i, j, hij, hα, hcut⟩
      by_contra hn
      have he := (hj j.down).mpr ((hmem j.down).mpr
        ⟨α, (hs α).mpr ⟨i, j, hij, hα⟩, hn, i.down, hij, hα⟩)
      obtain ⟨r, hr⟩ := he
      exact hcut r hr
    · intro hα
      obtain ⟨i, j, hij, hr⟩ := (hs α).mp (hI hα)
      refine ⟨i, j, hij, hr, fun r hh ↦ ?_⟩
      obtain ⟨α', _, hn, i', hji, he⟩ := (hmem j.down).mp ((hj j.down).mp ⟨r, hh⟩)
      have hi : i' = i.down := Fin.ext (by omega)
      subst i'
      apply hn
      have hEq : α' = α := Subtype.ext (he.trans hr.symm)
      rwa [hEq]

theorem typeABlockParabolics : TypeABlockParabolics.{u} := by
  intro k _ n G E M h D c b hc hb m ranks
  have hs α := typeASimpleRoots M D c b hc hb α
  obtain ⟨lam, hlam⟩ := diagonalCocharacterInTorus E M.torus M.diagonal (fun i ↦ blockExponent ranks i.down)
  refine ⟨?_, ⟨lam, hasFace_blockExponent D M.characters hs ranks lam hlam, hlam⟩,
    fun f hf L R g ↦ face_matrix_equations D M.characters M.absolute hs ranks f hf L R g⟩
  rintro α ⟨i, j, hij, hα, _⟩
  exact (hs α).mpr ⟨i, j, hij, hα⟩

theorem standardCoordinateFlagQuotient : StandardCoordinateFlagQuotient.{u} := by
  intro k V _ _ _ _ n m β ranks P F G E A S M h D c b hc hb U H hlocal
  obtain ⟨H', _, hfix, heq, _⟩ := coordinateFlagQuotient β ranks P F G.val E A S hlocal
  have hblocks := (typeABlockParabolics M D c b hc hb ranks).2.2 H.cocharacter H.face H.limitGroups
  have hs := subgroupSections_of_affine G.property.1 (A := H.limitGroups.parabolic) (B := H')
    (fun R g ↦ (hblocks R g).trans (heq R g).symm)
  let q := orbitMap A.onFlags S.point
  have hstab (X : SchemeOver k) (g : X ⟶ G.val.X) :
      g ∈ SubgroupSections H.limitGroups.parabolic X ↔ g ≫ q = FlagSchemes.toBasePoint X ≫ S.point :=
    (hs X g).trans (hfix X g)
  refine ⟨(HomogeneousQuotient.homogeneousQuotient k G H.limitGroups.parabolic).1, hstab, hblocks, ?_⟩
  obtain ⟨f, hf⟩ := orbitMap_representsQuotient H.limitGroups.parabolic q
    (coordinateOrbitLocalLifts β ranks P F E A S hlocal)
    (orbitMap_fibres H.limitGroups.parabolic A.onFlags S.point A.one A.mul (fun X g ↦ (hstab X g).symm))
  intro Q
  exact ⟨compareRepresentatives Q f, compareRepresentatives_projection Q q f hf,
    quotientComparison_action Q _ A.onFlags S.point (compareRepresentatives_projection Q q f hf) A.mul⟩

section WeylAction

open Specs.AbstractPairing (Datum Root)
open Specs.DatumAndWeyl (Identification)
open Specs.BruhatOrbitParametrization (IsRepresentative)
open CategoryTheory.CartesianMonoidalCategory

variable {k J : Type u} [Field k] [Fintype J] [DecidableEq J] {G : AffineAlgebraicGroup k}
  {E : (groupPointsFunctor k).obj G.val ≅ StandardGroups.generalLinearPoints k J}
  {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] {D : Datum T}

private theorem matrix_has_nonzero_diagonal_permutation (g : Matrix.GeneralLinearGroup J k) :
    ∃ σ : Equiv.Perm J, ∀ i, g.val (σ i) i ≠ 0 := by
  classical
  by_contra! h
  have hz : g.val.det = 0 := by
    rw [Matrix.det_apply]
    apply Finset.sum_eq_zero
    intro σ _
    obtain ⟨i, hi⟩ := h σ
    have hzero : (∏ j : J, g.val (σ j) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hzero, smul_zero]
  exact (Matrix.GeneralLinearGroup.det g).ne_zero hz

private def representativeMatrix (W : Identification D) (E : (groupPointsFunctor k).obj G.val ≅
    StandardGroups.generalLinearPoints k J)
    (x : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X) : Matrix.GeneralLinearGroup J k :=
  E.hom.app (CommAlgCat.of k k)
    (toUnit _ ≫ x ≫ W.normalizer.inclusion.hom.hom)

private theorem representative_matrix_map (W : Identification D)
    (x : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X) (R : TestAlgebra k) :
    E.hom.app R (toUnit ((testSpec k).obj (op R)) ≫ x ≫ W.normalizer.inclusion.hom.hom) =
      Matrix.GeneralLinearGroup.map (algebraMap k R) (representativeMatrix W E x) := by
  let i := CommAlgCat.ofHom (Algebra.ofId k R)
  let p : Points G.val.X (CommAlgCat.of k k) := toUnit _ ≫ x ≫ W.normalizer.inclusion.hom.hom
  have hp : mapPoints i p = toUnit ((testSpec k).obj (op R)) ≫ x ≫ W.normalizer.inclusion.hom.hom := by
    change (testSpec k).map i.op ≫ toUnit _ ≫ x ≫ W.normalizer.inclusion.hom.hom = _
    have hbase : (testSpec k).map i.op ≫ toUnit ((testSpec k).obj (op (CommAlgCat.of k k))) =
        toUnit ((testSpec k).obj (op R)) := toUnit_unique _ _
    rw [← Category.assoc ((testSpec k).map i.op) (toUnit _), hbase]
  exact (congrArg (fun g : Points G.val.X R ↦ E.hom.app R g) hp.symm).trans
    (matrix_mapPoints (E := E) i p)

open private comp_conjugateFamily from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private theorem representative_conjugation_entry (a : DiagonalCharacters E T)
    (W : Identification D) {w : D.rootDatum.weylGroup}
    {x : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X} (hx : IsRepresentative W w x)
    (R : TestAlgebra k) (t : Points T.group.X R) (i j : J) :
    let c := W.image.conjugation (W.labelEquiv w)
    algebraMap k R ((representativeMatrix W E x).val i j) * characterValue (a.character j) R t =
      characterValue (a.character i) R (t ≫ c.hom.hom.hom) *
        algebraMap k R ((representativeMatrix W E x).val i j) := by
  let Y := (testSpec k).obj (op R)
  let c := W.image.conjugation (W.labelEquiv w)
  let gt : GroupPoints G.val R := toUnit Y ≫ x ≫ W.normalizer.inclusion.hom.hom
  let f := lift t (toUnit Y : Y ⟶ 𝟙_ (SchemeOver k))
  let t₀ : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
  let t₁ : GroupPoints G.val R := (t ≫ c.hom.hom.hom) ≫ T.inclusion.hom.hom
  have h := W.image.conjugates (𝟙_ (SchemeOver k)) x (W.labelEquiv w)
    (by simpa only [toUnit_unit, Category.id_comp] using (show x ≫ W.quotient.hom.hom = _ from hx))
  have h' := congrArg (fun z ↦ f ≫ z) h
  simp only [f, comp_conjugateFamily, lift_fst_assoc, lift_snd_assoc] at h'
  change gt * t₀ * gt⁻¹ = t₁ at h'
  have h'' := congrArg (fun z ↦ E.hom.app R z) (mul_inv_eq_iff_eq_mul.mp h')
  rw [map_mul, map_mul] at h''
  have hh := congrArg (fun g : Matrix.GeneralLinearGroup J R ↦ g.val i j) h''
  change ((E.hom.app R gt : Matrix.GeneralLinearGroup J R).val *
    (E.hom.app R (t ≫ T.inclusion.hom.hom) : Matrix.GeneralLinearGroup J R).val) i j =
    ((E.hom.app R ((t ≫ c.hom.hom.hom) ≫ T.inclusion.hom.hom) : Matrix.GeneralLinearGroup J R).val *
      (E.hom.app R gt : Matrix.GeneralLinearGroup J R).val) i j at hh
  rw [a.diagonal, a.diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
  rw [← diagonalCharacter_unit, ← diagonalCharacter_unit, ← characterValue_eq_coe,
    ← characterValue_eq_coe] at hh
  rw [representative_matrix_map W x R] at hh
  exact hh

private theorem representative_character (a : DiagonalCharacters E T)
    (hT : GeometricRadicals.IsSplitTorus T.group) (W : Identification D)
    {w : D.rootDatum.weylGroup} {x : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X}
    (hx : IsRepresentative W w x) {i j : J}
    (hij : (representativeMatrix W E x).val i j ≠ 0) :
    (W.labelEquiv w).val (a.character j) = a.character i := by
  apply RootData.CharacterPairing.characterValuesDetectCharacters hT
  intro R t
  rw [W.image.characterAction]
  let c := W.image.conjugation (W.labelEquiv w)
  have he := representative_conjugation_entry a W hx R (t ≫ c.inv.hom.hom) i j
  have hcancel : c.inv.hom.hom ≫ c.hom.hom.hom = 𝟙 T.group.X :=
    ((Grp.forget (SchemeOver k)).mapIso c).inv_hom_id
  have hc : (t ≫ c.inv.hom.hom) ≫ c.hom.hom.hom = t := by
    rw [Category.assoc, hcancel, Category.comp_id]
  dsimp only at he
  rw [hc, mul_comm (algebraMap k R _)] at he
  have h := ((isUnit_iff_ne_zero.mpr hij).map (algebraMap k R)).mul_left_inj.mp he
  rw [characterValue_eq_coe, characterUnit_comp, ← characterValue_eq_coe]
  exact h

private theorem representative_permutation (a : DiagonalCharacters E T)
    (hT : GeometricRadicals.IsSplitTorus T.group) (W : Identification D)
    {w : D.rootDatum.weylGroup} {x : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X}
    (hx : IsRepresentative W w x) :
    ∃ σ : Equiv.Perm J, (∀ j, (W.labelEquiv w).val (a.character j) = a.character (σ j)) ∧
      (∀ i j, i ≠ σ j → (representativeMatrix W E x).val i j = 0) := by
  obtain ⟨σ, hσ⟩ := matrix_has_nonzero_diagonal_permutation (representativeMatrix W E x)
  have hχ j := representative_character a hT W hx (hσ j)
  refine ⟨σ, hχ, ?_⟩
  intro i j hij
  by_contra hz
  apply hij (diagonal_characters_injective a ?_)
  exact (representative_character a hT W hx hz).symm.trans (hχ j)

private def weylPermutationHom (a : DiagonalCharacters E T)
    (hT : GeometricRadicals.IsSplitTorus T.group) (W : Identification D)
    (hrep : ∀ w, ∃ x, IsRepresentative W w x) : D.rootDatum.weylGroup →* Equiv.Perm J := by
  classical
  let s (w : D.rootDatum.weylGroup) := (representative_permutation a hT W
    (Classical.choose_spec (hrep w))).choose
  have h (w) (j) : (W.labelEquiv w).val (a.character j) = a.character (s w j) :=
    (Classical.choose_spec (representative_permutation a hT W (Classical.choose_spec (hrep w)))).1 j
  exact {
    toFun := s
    map_one' := Equiv.ext fun j ↦ (diagonal_characters_injective a) (by
      rw [← h, map_one]; rfl)
    map_mul' := fun w v ↦ Equiv.ext fun j ↦ (diagonal_characters_injective a) (by
      change a.character (s (w * v) j) = a.character (s w (s v j))
      rw [← h, map_mul]
      change (W.labelEquiv w).val ((W.labelEquiv v).val (a.character j)) = _
      rw [h, h]) }

private theorem weylPermutationHom_character (a : DiagonalCharacters E T)
    (hT : GeometricRadicals.IsSplitTorus T.group) (W : Identification D)
    (hrep : ∀ w, ∃ x, IsRepresentative W w x) (w : D.rootDatum.weylGroup) (j : J) :
    (W.labelEquiv w).val (a.character j) = a.character (weylPermutationHom a hT W hrep w j) :=
  (Classical.choose_spec (representative_permutation a hT W (Classical.choose_spec (hrep w)))).1 j

private theorem weylPermutation_reflection (a : DiagonalCharacters E T)
    (hT : GeometricRadicals.IsSplitTorus T.group)
    (hd : ∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔
        ∀ i j, i ≠ j → (E.hom.app R g : Matrix.GeneralLinearGroup J R).val i j = 0)
    (W : Identification D) (hrep : ∀ w, ∃ x, IsRepresentative W w x)
    (α : Root T) (i j : J) (hij : i ≠ j) (hα : α.val = a.ratio i j) :
    weylPermutationHom a hT W hrep (RootPairing.weylGroup.ofIdx D.rootDatum α) = Equiv.swap i j := by
  classical
  let w := RootPairing.weylGroup.ofIdx D.rootDatum α
  let σ := weylPermutationHom a hT W hrep w
  have hchar (l : J) : w.val.weightEquiv (Additive.ofMul (a.character l)) =
      Additive.ofMul (a.character (σ l)) :=
    (W.characterAction w _).trans (congrArg Additive.ofMul (weylPermutationHom_character a hT W hrep w l))
  have hm := D.rootDatum.reflection_apply_self (i := α)
  change w.val.weightEquiv (D.rootDatum.root α) = _ at hm
  rw [D.root_eq, hα] at hm
  have hn : -Additive.ofMul (a.ratio i j) = Additive.ofMul (a.ratio j i) :=
    congrArg Additive.ofMul (inv_div (a.character i) (a.character j))
  rw [hn] at hm
  change w.val.weightEquiv (Additive.ofMul (a.character i) - Additive.ofMul (a.character j)) =
    Additive.ofMul (a.ratio j i) at hm
  have hm' : w.val.weightEquiv (Additive.ofMul (a.character i)) -
      w.val.weightEquiv (Additive.ofMul (a.character j)) = Additive.ofMul (a.ratio j i) :=
    (w.val.weightEquiv.toLinearMap.map_sub (Additive.ofMul (a.character i))
      (Additive.ofMul (a.character j))).symm.trans hm
  rw [hchar, hchar] at hm'
  have hs : a.ratio (σ i) (σ j) = a.ratio j i := congrArg Additive.toMul hm'
  obtain ⟨hi, hj⟩ := ratio_injective a (fun h ↦ hij (σ.injective h)) hij.symm hs
  ext l
  change σ l = Equiv.swap i j l
  by_cases hli : l = i
  · subst l
    rwa [Equiv.swap_apply_left]
  by_cases hlj : l = j
  · subst l
    rwa [Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
  obtain ⟨c, hc⟩ := diagonalCocharacterInTorus E T hd (fun p ↦ if p = l then 1 else 0)
  let f := Specs.SimpleRoots.evaluate D c
  have hf (p : J) : f (Additive.ofMul (a.character p)) = if p = l then 1 else 0 :=
    (D.pairing_eq _ _).trans (coordinate_pairings_eq a c _ hc p)
  have hz : f (D.rootDatum.root α) = 0 := by
    rw [D.root_eq, hα]
    change f (Additive.ofMul (a.character i) - Additive.ofMul (a.character j)) = 0
    rw [map_sub, hf, hf, ite_eq_right (Ne.symm hli), ite_eq_right (Ne.symm hlj), sub_self]
  have hr := congrArg f (D.rootDatum.reflection_apply (i := α) (Additive.ofMul (a.character l)))
  change f (w.val.weightEquiv (Additive.ofMul (a.character l))) = _ at hr
  rw [hchar, map_sub, map_zsmul, hz, smul_zero, sub_zero, hf, hf, ite_eq_left rfl] at hr
  by_contra hn
  rw [ite_eq_right hn] at hr
  exact zero_ne_one hr

private theorem weylPermutation_surjective (a : DiagonalCharacters E T)
    (hT : GeometricRadicals.IsSplitTorus T.group)
    (hd : ∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔
        ∀ i j, i ≠ j → (E.hom.app R g : Matrix.GeneralLinearGroup J R).val i j = 0)
    (habs : ∀ χ, χ ∈ absoluteRoots T ↔ ∃ i j, i ≠ j ∧ χ = a.ratio i j)
    (W : Identification D) (hrep : ∀ w, ∃ x, IsRepresentative W w x) :
    Function.Surjective (weylPermutationHom a hT W hrep) := by
  classical
  let e := weylPermutationHom a hT W hrep
  intro π
  refine π.swap_induction_on ⟨1, map_one e⟩ (fun π i j hij ⟨v, hv⟩ ↦ ?_)
  let α : Root T := ⟨a.ratio i j, (habs _).mpr ⟨i, j, hij, rfl⟩⟩
  refine ⟨RootPairing.weylGroup.ofIdx D.rootDatum α * v, ?_⟩
  exact (map_mul e _ _).trans (congrArg₂ (· * ·) (weylPermutation_reflection a hT hd W hrep α i j hij rfl) hv)

private theorem weylPermutation_matrix (a : DiagonalCharacters E T)
    (hT : GeometricRadicals.IsSplitTorus T.group) (W : Identification D)
    (hrep : ∀ w, ∃ x, IsRepresentative W w x) (w : D.rootDatum.weylGroup)
    (x : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X) (hx : IsRepresentative W w x)
    (i j : J) (hij : i ≠ weylPermutationHom a hT W hrep w j) :
    (representativeMatrix W E x).val i j = 0 := by
  by_contra hn
  exact hij (diagonal_characters_injective a ((representative_character a hT W hx hn).symm.trans
    (weylPermutationHom_character a hT W hrep w j)))

open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

private theorem weylPermutation_injective (a : DiagonalCharacters E T)
    (hT : GeometricRadicals.IsSplitTorus T.group) (W : Identification D)
    (hrep : ∀ w, ∃ x, IsRepresentative W w x) :
    Function.Injective (weylPermutationHom a hT W hrep) := by
  intro w v h
  let c₁ := W.image.conjugation (W.labelEquiv w)
  let c₂ := W.image.conjugation (W.labelEquiv v)
  have hχ (j : J) : c₁.inv ≫ a.character j = c₂.inv ≫ a.character j := by
    rw [← W.image.characterAction, ← W.image.characterAction, weylPermutationHom_character a hT W hrep,
      weylPermutationHom_character a hT W hrep, h]
  letI := G.property.1
  letI := T.isClosedImmersion
  have hAff : IsAffine T.group.X.left := isAffine_of_isAffineHom T.inclusion.hom.hom.left
  have he : c₁.inv = c₂.inv := by
    apply Grp.hom_ext
    apply hom_ext_of_points hAff
    intro R t
    apply (a.coordinates.app R).groupIsoToMulEquiv.injective
    change (a.coordinates.hom.app R (t ≫ c₁.inv.hom.hom) : J → Rˣ) =
      (a.coordinates.hom.app R (t ≫ c₂.inv.hom.hom) : J → Rˣ)
    funext j
    have hu := congrArg (fun χ : Character T.group ↦ characterUnitHom R t χ) (hχ j)
    simpa only [characterUnit_comp, diagonalCharacter_unit] using hu
  apply W.labelEquiv.injective
  apply Subtype.ext
  apply MulEquiv.ext
  intro χ
  rw [W.image.characterAction, W.image.characterAction]
  exact congrArg (fun f ↦ f ≫ χ) he

end WeylAction

theorem typeAWeylAction : TypeAWeylAction.{u} := by
  intro k _ n G E M h D W hrep
  let e := weylPermutationHom M.characters M.split W hrep
  have he : Function.Bijective e := ⟨weylPermutation_injective M.characters M.split W hrep,
    weylPermutation_surjective M.characters M.split M.diagonal M.absolute W hrep⟩
  exact ⟨⟨MulEquiv.ofBijective e he, weylPermutationHom_character M.characters M.split W hrep,
    fun α i j hij hα ↦ weylPermutation_reflection M.characters M.split M.diagonal W hrep α i j hij hα,
    fun w x hx i j hne ↦ weylPermutation_matrix M.characters M.split W hrep w x hx i j hne⟩⟩

section GrassmannianComparison

open private prefixSubmodule_coordinates mem_coordinateSubmodule span_coordinateSingles
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagSchemes

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

section GrassmannianOrbits

open _root_.LinearAlgebraicGroups.Specs.GrassmannianCharts
open Specs.FlagSchemes (coordinateSubmodule)

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {n d : ℕ}
  (β : Module.Basis (Fin n) k V)
local notation "b" => FlagSchemes.liftedBasis β

private theorem matrixTransport_coordinates (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R) :
    (coordinates b R).toLinearMap.comp (FlagIncidence.matrixTransport b R g).toLinearMap =
      (Matrix.toLin' g.val).comp (coordinates b R).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact (coordinates b R).apply_symm_apply (Matrix.toLin' g.val (coordinates b R x))

private theorem upper_triangular_preserves_prefix (R : TestAlgebra k)
    (g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R) (h : ∀ i j : (ULift.{u} (Fin n)), j.down < i.down → g.val i j = 0) (s : ℕ) :
    (FlagIncidence.prefixSubmodule β R s).map (FlagIncidence.matrixTransport b R g).toLinearMap =
      FlagIncidence.prefixSubmodule β R s := by
  let e := coordinates b R
  apply Submodule.map_injective_of_injective e.injective
  rw [← Submodule.map_comp, matrixTransport_coordinates, Submodule.map_comp, prefixSubmodule_coordinates]
  let cuts : Fin 1 → Set (ULift.{u} (Fin n)) := fun _ ↦ {i | i.down.val < s}
  have hstable := (LinearAlgebraicGroups.FlagSchemes.coordinateFlagStabilizer R (ULift.{u} (Fin n)) cuts g).mpr
    (fun a i j hj hi ↦ h i j (by dsimp [cuts] at hj hi; omega))
  exact hstable 0

private theorem transported_intersection_rank {F : Type u} [Field F] [Algebra k F]
    (L M : Plane k V d (CommAlgCat.of k F))
    (g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) F) (h : ∀ i j : (ULift.{u} (Fin n)), j.down < i.down → g.val i j = 0)
    (transport : L.toSubmodule = M.toSubmodule.map
      (FlagIncidence.matrixTransport b (CommAlgCat.of k F) g).toLinearMap) (j : ℕ) :
    intersectionRank β L j = intersectionRank β M j := by
  let R := CommAlgCat.of k F
  let e := FlagIncidence.matrixTransport b R g
  let P := FlagIncidence.prefixSubmodule β R j
  change Module.finrank F (L.toSubmodule ⊓ P : Submodule F (F ⊗[k] V)) = _
  change L.toSubmodule = M.toSubmodule.map e.toLinearMap at transport
  have hP : P.map e.toLinearMap = P := upper_triangular_preserves_prefix β R g h j
  rw [transport, ← hP, ← Submodule.map_inf _ e.injective]
  exact LinearEquiv.finrank_map_eq e _

private theorem coordinate_chart_plane (C : ChartSystem (k := k) (V := V) b d)
    (I : Fin d ↪o Fin n) (R : TestAlgebra k) :
    ∃ f : Points (echelonScheme k I) R,
      (C.affinePoints.hom.app R (f ≫ echelonCell β C I)).toSubmodule.map
        (coordinates b R).toLinearMap = coordinateSubmodule R (↑(pivotSet.{u} I).val : Set (ULift.{u} (Fin n))) := by
  let P := pivotSet.{u} I
  let A : Matrix (Outside P) (Inside P) R := 0
  let p := chartPointOfMatrix P R A
  have hp : matrixOfPoint P R p = A := matrixOfChartPoint P R A
  have h := ((echelonCellImmersion β C I).2.2.2 R (p ≫ C.chart P)).mpr
    ⟨p, rfl, fun i j _ ↦ by rw [hp]; rfl⟩
  obtain ⟨f, hf⟩ := h
  refine ⟨f, ?_⟩
  rw [hf, C.coordinates_eq, hp]
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    apply mem_coordinateSubmodule.mpr
    intro i hi
    have hz := graph_coord_nonpivot β P R A z ⟨i, hi⟩
    simpa [A] using hz
  · intro hx
    let z : Inside P → R := fun i ↦ x i.val
    refine ⟨graphInclusion b P R A z, ⟨z, rfl⟩, ?_⟩
    funext i
    change (coordinates b R) (graphInclusion b P R A z) i = x i
    by_cases hi : i ∈ P.val
    · exact graph_coord_pivot β P R A z ⟨i, hi⟩
    · have hz := graph_coord_nonpivot β P R A z ⟨i, hi⟩
      rw [mem_coordinateSubmodule.mp hx i hi]
      simpa [A] using hz

private theorem upperOrbit_field (C : ChartSystem (k := k) (V := V) b d) (I : Fin d ↪o Fin n)
    {F : Type u} [Field F] [Algebra k F] (p : Points C.scheme (CommAlgCat.of k F)) :
    (∃ f : Points (echelonScheme k I) (CommAlgCat.of k F), f ≫ echelonCell β C I = p) ↔
      ∃ g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) F,
        (∀ i j : (ULift.{u} (Fin n)), j.down < i.down → g.val i j = 0) ∧
        (C.affinePoints.hom.app (CommAlgCat.of k F) p).toSubmodule.map
          (coordinates b (CommAlgCat.of k F)).toLinearMap =
          (coordinateSubmodule F (↑(pivotSet.{u} I).val : Set (ULift.{u} (Fin n)))).map (Matrix.toLin' g.val) := by
  let R := CommAlgCat.of k F
  constructor
  · intro h
    obtain ⟨g, ht, _, he⟩ := echelonUpperUnitriangularOrbit β C I R p h
    exact ⟨g, ht, he⟩
  · rintro ⟨g, ht, he⟩
    obtain ⟨f, hf⟩ := coordinate_chart_plane β C I R
    let q := f ≫ echelonCell β C I
    let L := C.affinePoints.hom.app R p
    let M := C.affinePoints.hom.app R q
    have h : L.toSubmodule = M.toSubmodule.map (FlagIncidence.matrixTransport b R g).toLinearMap := by
      apply Submodule.map_injective_of_injective (coordinates b R).injective
      rw [← Submodule.map_comp, matrixTransport_coordinates, Submodule.map_comp, hf]
      exact he
    apply (echelonCellRankCriterion β C I p).mpr
    intro j
    exact (transported_intersection_rank β L M g ht h j).trans (echelonCellRank β C I q ⟨f, rfl⟩ j)

end GrassmannianOrbits

section SingletonIncidence

open _root_.LinearAlgebraicGroups.Specs.GrassmannianCharts
open Specs.FlagSchemes (coordinateSubmodule)

private theorem monomial_maps_coordinate {R J : Type u} [CommRing R] [Fintype J] [DecidableEq J]
    (g : Matrix.GeneralLinearGroup J R) (σ : Equiv.Perm J)
    (h : ∀ i j, i ≠ σ j → g.val i j = 0) (s : Set J) :
    (coordinateSubmodule R s).map (Matrix.toLin' g.val) = coordinateSubmodule R (σ '' s) := by
  classical
  let a (j : J) : Rˣ :=
    Units.mkOfMulEqOne (g.val (σ j) j) (g.inv j (σ j)) (by
      have hsum := congrArg (fun M : Matrix J J R ↦ M j j) g.inv_val
      change (g.inv * g.val) j j = (1 : Matrix J J R) j j at hsum
      rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single (σ j)] at hsum
      · rwa [mul_comm]
      · intro i _ hi
        rw [h i j hi, mul_zero]
      · simp)
  have hcol (j : J) : Matrix.toLin' g.val (Pi.single j (1 : R)) =
      (a j : R) • Pi.single (σ j) 1 := by
    funext i
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    by_cases hi : i = σ j
    · subst i
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, a, Units.val_mkOfMulEqOne, Matrix.col_apply]
    · simp [Pi.single_eq_of_ne hi, h _ _ hi]
  rw [← span_coordinateSingles, Submodule.map_span, ← span_coordinateSingles]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    rw [hcol j]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ j, ⟨j, hj, rfl⟩, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have hmem : Matrix.toLin' g.val (Pi.single j (1 : R)) ∈
        Submodule.span R (Matrix.toLin' g.val '' (fun i ↦ Pi.single i (1 : R)) '' s) :=
      Submodule.subset_span ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    rw [hcol j] at hmem
    change (Pi.single (σ j) (1 : R) : J → R) ∈ Submodule.span R
      ((Matrix.toLin' g.val) '' ((fun i ↦ Pi.single i (1 : R)) '' s))
    have hm : (↑((a j)⁻¹) : R) * (a j : R) = 1 := (a j).inv_val
    simpa only [smul_smul, hm, one_smul] using
      (Submodule.smul_mem _ (↑((a j)⁻¹) : R) hmem)

private abbrev singletonProjection {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V)
    (P : Fin 1 → PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) d)
    (F : FlagIncidence.Presentation (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families)) :
    (F.scheme : SchemeOver k) ⟶ ((P (0 : Fin 1)).charts.scheme : SchemeOver k) :=
  F.inclusion ≫ Pi.π (fun i : Fin 1 ↦ (P i).charts.scheme) 0

private theorem singletonIncidence_isIso {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V)
    (P : Fin 1 → PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) d)
    (F : FlagIncidence.Presentation (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families)) : IsIso (singletonProjection β P F) := by
  letI := F.closed
  letI : Mono F.inclusion := Over.mono_of_mono_left _
  obtain ⟨f, hf⟩ := (F.factor_iff_zero _ (𝟙 _)).mpr (by
    intro i j h
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i j
    exact (by decide : ¬ ((0 : Fin 1).val + 1 = (0 : Fin 1).val)) h |>.elim)
  let e : F.scheme ≅ FlagIncidence.GrassmannianProduct (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β) (fun i ↦ (P i).charts) :=
    ⟨F.inclusion, f, (cancel_mono F.inclusion).mp (by rw [Category.assoc, hf, Category.comp_id, Category.id_comp]), hf⟩
  let e' := productUniqueIso (fun i ↦ (P i).charts.scheme)
  have he : (e ≪≫ e').hom = singletonProjection β P F := by
    rw [Iso.trans_hom, productUniqueIso_hom]
    rfl
  rw [← he]
  infer_instance

open private prefixPlane prefixPlane_map prefixPlane_submodule
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagIncidence

private theorem singleton_standardPlane {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V)
    (P : Fin 1 → PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) d)
    (F : FlagIncidence.Presentation (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
    {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (A : FlagIncidence.Action (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) F.inclusion G E)
    (S : FlagSchemes.CoordinateStabilizer β (fun _ : Fin 1 ↦ d) P F G E A)
    (hd : d ≤ n) (R : TestAlgebra k) :
    ((P 0).charts.affinePoints.hom.app R
      ((FlagSchemes.toBasePoint ((testSpec k).obj (op R)) ≫ S.point) ≫ singletonProjection β P F)).toSubmodule.map
      (coordinates (FlagSchemes.liftedBasis β) R).toLinearMap = coordinateSubmodule R {i : ULift.{u} (Fin n) | i.down.val < d} := by
  let K := CommAlgCat.of k k
  let a : K ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have hpoint : ((P 0).charts.affinePoints.hom.app K (S.point ≫ singletonProjection β P F)) = prefixPlane β hd K :=
    Module.Grassmannian.ext ((S.point_formula 0).trans (prefixPlane_submodule β hd K).symm)
  have hbase : (testSpec k).map a.op = FlagSchemes.toBasePoint ((testSpec k).obj (op R)) := hom_toBase_eq _
  rw [← hbase, Category.assoc]
  change ((P 0).charts.affinePoints.hom.app R (mapPoints a (S.point ≫ singletonProjection β P F))).toSubmodule.map _ = _
  let p : Points (P 0).charts.scheme K := S.point ≫ singletonProjection β P F
  have hn := congrArg (fun f : Points (P 0).charts.scheme K ⟶ Plane k V d R ↦ f p)
    ((P 0).charts.affinePoints.hom.naturality a)
  change ((P 0).charts.affinePoints.hom.app R (mapPoints a (S.point ≫ singletonProjection β P F))) =
    Module.Grassmannian.map a.hom ((P 0).charts.affinePoints.hom.app K (S.point ≫ singletonProjection β P F)) at hn
  rw [hn, hpoint, prefixPlane_map, prefixPlane_submodule, prefixSubmodule_coordinates]

private theorem singleton_matrixTransport {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V)
    (P : Fin 1 → PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) d)
    (F : FlagIncidence.Presentation (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
    {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (A : FlagIncidence.Action (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) F.inclusion G E)
    (R : TestAlgebra k) (g : Points G.X R) (p : Points F.scheme R) :
    ((P 0).charts.affinePoints.hom.app R ((prod.lift g p ≫ A.onFlags) ≫ singletonProjection β P F)).toSubmodule.map
      (coordinates (FlagSchemes.liftedBasis β) R).toLinearMap =
      (((P 0).charts.affinePoints.hom.app R (p ≫ singletonProjection β P F)).toSubmodule.map (coordinates (FlagSchemes.liftedBasis β) R).toLinearMap).map
        (Matrix.toLin' (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val) := by
  let x := prod.lift g (p ≫ F.inclusion)
  have h := A.transport R x 0
  have hx : (prod.lift g p ≫ A.onFlags) ≫ F.inclusion = x ≫ A.onProduct := by
    rw [Category.assoc, A.restricts, ← Category.assoc, prod.lift_map, Category.comp_id]
  have hp : x ≫ prod.snd = p ≫ F.inclusion := prod.lift_snd _ _
  have hg : x ≫ prod.fst = g := prod.lift_fst _ _
  rw [hp, hg, ← hx] at h
  unfold FlagIncidence.productPlanes at h
  simp only [Category.assoc] at h ⊢
  rw [h, ← Submodule.map_comp, matrixTransport_coordinates, Submodule.map_comp]

end SingletonIncidence

section GrassmannianOrbitComparison

open _root_.LinearAlgebraicGroups.Specs.GrassmannianCharts
open CategoryTheory.CartesianMonoidalCategory
open Specs.FlagSchemes (coordinateSubmodule)

private theorem pivot_tuples_same_set {n d : ℕ} {I J : Fin d ↪o Fin n}
    (h : (pivotSet.{u} I).val = (pivotSet.{u} J).val) : I = J := by
  apply (OrderEmbedding.range_inj_of_wellFoundedLT).mp
  ext i
  simpa only [mem_pivotSet.{u}] using show (ULift.up i : ULift.{u} (Fin n)) ∈ (pivotSet.{u} I).val ↔
    (ULift.up i : ULift.{u} (Fin n)) ∈ (pivotSet.{u} J).val by rw [h]

private theorem pivot_of_permutation_exists {n d : ℕ} (hd : d ≤ n)
    (σ : Equiv.Perm (ULift.{u} (Fin n))) : ∃ I : Fin d ↪o Fin n,
    ((pivotSet.{u} I).val : Set (ULift.{u} (Fin n))) = σ '' {i | i.down.val < d} := by
  let f : Fin d ↪ ULift.{u} (Fin n) :=
    ⟨fun i ↦ σ (ULift.up (Fin.castLE hd i)), fun i j hij ↦ (Fin.castLE_injective hd)
      (congrArg ULift.down (σ.injective hij))⟩
  let p : Pivot (ULift.{u} (Fin n)) d := ⟨Finset.univ.map f, by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]⟩
  obtain ⟨I, hI⟩ := exists_tuple_of_pivot p
  refine ⟨I, ?_⟩
  rw [hI]
  ext x
  change x ∈ Finset.univ.map f ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨ULift.up (Fin.castLE hd i), i.isLt, hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.down.val, hi⟩, Finset.mem_univ _, by cases i; rfl⟩

private theorem permutation_extending_pivots {n d : ℕ} (hd : d ≤ n) (I : Fin d ↪o Fin n) :
    ∃ σ : Equiv.Perm (ULift.{u} (Fin n)),
      ((pivotSet.{u} I).val : Set (ULift.{u} (Fin n))) = σ '' {i | i.down.val < d} := by
  let f (r : Fin d) : ULift.{u} (Fin n) := ULift.up (Fin.castLE hd r)
  let g (r : Fin d) : ULift.{u} (Fin n) := ULift.up (I r)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g
    (fun i j h ↦ (Fin.castLE_injective hd) (congrArg ULift.down h))
    (fun i j h ↦ I.injective (congrArg ULift.down h))
  refine ⟨σ, ?_⟩
  ext x
  simp only [Finset.mem_coe, mem_pivotSet]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨f r, r.isLt, (hσ r).trans (ULift.down_injective hr)⟩
  · rintro ⟨i, hi, rfl⟩
    let r : Fin d := ⟨i.down.val, hi⟩
    have h : f r = i := ULift.down_injective (Fin.ext rfl)
    exact ⟨r, congrArg ULift.down ((hσ r).symm.trans (congrArg σ h))⟩

private theorem matrixOrbit_affine {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V)
    (P : Fin 1 → PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) d)
    (F : FlagIncidence.Presentation (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
    {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (A : FlagIncidence.Action (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) F.inclusion G E)
    (S : FlagSchemes.CoordinateStabilizer β (fun _ : Fin 1 ↦ d) P F G E A)
    (hd : d ≤ n) (I : Fin d ↪o Fin n)
    (σ : Equiv.Perm (ULift.{u} (Fin n)))
    (hI : ((pivotSet.{u} I).val : Set (ULift.{u} (Fin n))) = σ '' {i | i.down.val < d})
    (R : TestAlgebra k) (g z : AdjointRepresentation.GroupPoints G R)
    (hz : ∀ (i j : ULift.{u} (Fin n)), i ≠ σ j →
      (E.hom.app R z : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0) :
    ((P 0).charts.affinePoints.hom.app R
      ((g * z) ≫ orbitMap A.onFlags S.point ≫ singletonProjection β P F)).toSubmodule.map
        (coordinates (FlagSchemes.liftedBasis β) R).toLinearMap =
      (coordinateSubmodule R (↑(pivotSet.{u} I).val : Set (ULift.{u} (Fin n)))).map
        (Matrix.toLin' (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val) := by
  have h := comp_orbitMap (G := G) (g * z) A.onFlags S.point
  rw [A.mul] at h
  rw [← Category.assoc, h, singleton_matrixTransport β P F E A,
    singleton_matrixTransport β P F E A]
  apply congrArg (Submodule.map (Matrix.toLin' (E.hom.app R g : Matrix.GeneralLinearGroup _ R).val))
  exact (congrArg (Submodule.map (Matrix.toLin' (E.hom.app R z : Matrix.GeneralLinearGroup _ R).val))
    (singleton_standardPlane β P F E A S hd R)).trans ((monomial_maps_coordinate _ σ hz _).trans (congrArg (coordinateSubmodule R) hI.symm))

private def borelOrbitThrough {k : Type u} [Field k] {G : GroupScheme k} {X : SchemeOver k}
    (q : G.X ⟶ X) (B : ClosedSubgroup G) (z : 𝟙_ (SchemeOver k) ⟶ G.X) : B.group.X ⟶ X :=
  (B.inclusion.hom.hom * (toUnit _ ≫ z)) ≫ q

private theorem borelOrbitThrough_point {k : Type u} [Field k] {G : GroupScheme k} {X : SchemeOver k}
    (p : G.X ⟶ X) (B : ClosedSubgroup G) (z : 𝟙_ (SchemeOver k) ⟶ G.X)
    (R : TestAlgebra k) (q : Points B.group.X R) :
    q ≫ borelOrbitThrough p B z =
      ((q ≫ B.inclusion.hom.hom) * (toUnit ((testSpec k).obj (op R)) ≫ z)) ≫ p := by
  simp only [borelOrbitThrough, ← Category.assoc q, MonObj.comp_mul]
  have h : q ≫ toUnit B.group.X = toUnit ((testSpec k).obj (op R)) := toUnit_unique _ _
  simp only [Category.assoc, reassoc_of% h]

private theorem singleton_borel_orbit_range {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V] {n d : ℕ}
    (β : Module.Basis (Fin n) k V)
    (P : Fin 1 → PluckerEmbedding.PluckerMorphism (FlagSchemes.liftedBasis β) d)
    (F : FlagIncidence.Presentation (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
    {G : GroupScheme k}
    (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (A : FlagIncidence.Action (fun _ : Fin 1 ↦ d) (FlagSchemes.liftedBasis β)
      (fun i ↦ (P i).charts) F.inclusion G E)
    (S : FlagSchemes.CoordinateStabilizer β (fun _ : Fin 1 ↦ d) P F G E A)
    (hd : d ≤ n) (B : ClosedSubgroup G)
    (hB : ∀ (R : TestAlgebra k) (g : Points G.X R),
      g ∈ SubgroupSections B ((testSpec k).obj (op R)) ↔
      ∀ (i j : ULift.{u} (Fin n)), j.down < i.down →
        (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0)
    (z : 𝟙_ (SchemeOver k) ⟶ G.X) (σ : Equiv.Perm (ULift.{u} (Fin n)))
    (hz : ∀ (R : TestAlgebra k) (i j : ULift.{u} (Fin n)), i ≠ σ j →
      (E.hom.app R (toUnit ((testSpec k).obj (op R)) ≫ z) :
        Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0)
    (I : Fin d ↪o Fin n) (hI : ((pivotSet.{u} I).val : Set (ULift.{u} (Fin n))) =
      σ '' {i | i.down.val < d}) :
    Set.range (borelOrbitThrough (orbitMap A.onFlags S.point ≫ singletonProjection β P F) B z).left = Set.range (echelonCell β (P 0).charts I).left := by
  let e := echelonCell β (P 0).charts I
  let f := borelOrbitThrough (orbitMap A.onFlags S.point ≫ singletonProjection β P F) B z
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    let R := residueTestAlgebra B.group.X x
    letI := residueBaseAlgebra B.group.X x
    let q := residuePoint B.group.X x
    let p := q ≫ f
    obtain ⟨q', h⟩ := (upperOrbit_field β (P 0).charts I p).mpr
      ⟨E.hom.app R (q ≫ B.inclusion.hom.hom), (hB R _).mp ⟨q, rfl⟩, by
        rw [show p = q ≫ f from rfl, borelOrbitThrough_point]
        exact matrixOrbit_affine β P F E A S hd I σ hI R _ _ (hz R)⟩
    let x₀ := IsLocalRing.closedPoint (B.group.X.left.residueField x)
    refine ⟨q'.left x₀, ?_⟩
    have he := congrArg (fun h : Points (P 0).charts.scheme R ↦ h.left x₀) h
    change e.left (q'.left x₀) = f.left (q.left x₀) at he
    exact he.trans (congrArg f.left (B.group.X.left.fromSpecResidueField_apply x x₀))
  · rintro ⟨x, rfl⟩
    let R := residueTestAlgebra (echelonScheme k I) x
    letI := residueBaseAlgebra (echelonScheme k I) x
    let q := residuePoint (echelonScheme k I) x
    let p := q ≫ e
    obtain ⟨g, htri, h⟩ := (upperOrbit_field β (P 0).charts I p).mp ⟨q, rfl⟩
    let g' := E.inv.app R g
    have hg : E.hom.app R g' = g := (E.app R).groupIsoToMulEquiv.apply_symm_apply _
    obtain ⟨v, hv⟩ := (hB R g').mpr (by rw [hg]; exact htri)
    change v ≫ B.inclusion.hom.hom = g' at hv
    have he : v ≫ f = p := by
      apply (ConcreteCategory.bijective_of_isIso ((P 0).charts.affinePoints.hom.app R)).1
      apply Module.Grassmannian.ext
      apply Submodule.map_injective_of_injective (coordinates (FlagSchemes.liftedBasis β) R).injective
      rw [show v ≫ f = v ≫ borelOrbitThrough (orbitMap A.onFlags S.point ≫ singletonProjection β P F) B z from rfl, borelOrbitThrough_point,
        hv, matrixOrbit_affine β P F E A S hd I σ hI R _ _ (hz R), hg]
      exact h.symm
    let x₀ := IsLocalRing.closedPoint ((echelonScheme k I).left.residueField x)
    refine ⟨v.left x₀, ?_⟩
    have hf := congrArg (fun h : Points (P 0).charts.scheme R ↦ h.left x₀) he
    change f.left (v.left x₀) = e.left (q.left x₀) at hf
    exact hf.trans (congrArg e.left ((echelonScheme k I).left.fromSpecResidueField_apply x x₀))

end GrassmannianOrbitComparison

section GrassmannianOrder

open _root_.LinearAlgebraicGroups.Specs.GrassmannianCharts
open Specs.ParabolicCosetLength (IsShortestInCoset)

private theorem shortest_translate {W : Type*} [Group W] (H : Subgroup W) (length : W → ℕ)
    {w v : W} (h : w⁻¹ * v ∈ H) :
    IsShortestInCoset length H v v → IsShortestInCoset length H w v := by
  intro hv
  refine ⟨h, fun u ↦ ?_⟩
  have h' : v⁻¹ * w ∈ H := by simpa only [mul_inv_rev, inv_inv] using H.inv_mem h
  let u' : H := ⟨(v⁻¹ * w) * u.val, H.mul_mem h' u.property⟩
  exact (hv.2 u').trans_eq (congrArg length (by change v * ((v⁻¹ * w) * u.val) = w * u.val; group))

private theorem shortest_at_self {W : Type*} [Group W] (H : Subgroup W) (length : W → ℕ)
    {w v : W} (h : IsShortestInCoset length H w v) : IsShortestInCoset length H v v := by
  refine ⟨by rw [inv_mul_cancel]; exact H.one_mem, fun u ↦ ?_⟩
  let u' : H := ⟨(w⁻¹ * v) * u.val, H.mul_mem h.1 u.property⟩
  exact (h.2 u').trans_eq (congrArg length (by change w * ((w⁻¹ * v) * u.val) = v * u.val; group))

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {n d : ℕ}
  (β : Module.Basis (Fin n) k V)
  (C : ChartSystem (k := k) (V := V) (FlagSchemes.liftedBasis β) d)

private theorem echelon_range_nonempty (I : Fin d ↪o Fin n) :
    (Set.range (echelonCell β C I).left).Nonempty := by
  obtain ⟨p, _⟩ := coordinate_chart_plane β C I (CommAlgCat.of k k)
  exact ⟨_, ⟨p.left (IsLocalRing.closedPoint k), rfl⟩⟩

private theorem echelon_same_at_point {I J : Fin d ↪o Fin n} {x : C.scheme.left}
    (hi : x ∈ Set.range (echelonCell β C I).left) (hj : x ∈ Set.range (echelonCell β C J).left) : I = J := by
  have h (j : ℕ) : pivotRank I j = pivotRank J j :=
    (residueRank_on_cell β C I hi j).symm.trans (residueRank_on_cell β C J hj j)
  have h₁ := (pivotRankOrder I J).mp (fun j _ ↦ (h j).le)
  have h₂ := (pivotRankOrder J I).mp (fun j _ ↦ (h j).ge)
  ext r
  exact le_antisymm (h₂ r) (h₁ r)

private theorem closure_echelon_range (I : Fin d ↪o Fin n) :
    closure (Set.range (echelonCell β C I).left) = rankLocus β C I := by
  have h := (echelonReducedClosure β C I).2
  rwa [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal] at h

private theorem echelon_range_containment {I J : Fin d ↪o Fin n} :
    Set.range (echelonCell β C J).left ⊆ closure (Set.range (echelonCell β C I).left) ↔
      ∀ r, J r ≤ I r := by
  rw [closure_echelon_range]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := echelon_range_nonempty β C J
    apply (pivotRankOrder I J).mp
    intro j hj
    exact (h hx j hj).trans_eq (residueRank_on_cell β C J hx j)
  · intro h x hx j hj
    exact ((pivotRankOrder I J).mpr h j hj).trans_eq (residueRank_on_cell β C J hx j).symm

private theorem echelon_subword_order {W : Type*} (I : W → Fin d ↪o Fin n)
    (shortest : W → Prop) (le : W → W → Prop)
    (hinj : Function.Injective (fun w : {w // shortest w} ↦ I w.val))
    (hclosure : ∀ w, shortest w → closure (Set.range (echelonCell β C (I w)).left) =
      ⋃ (v : {v // shortest v}) (_ : le v.val w), Set.range (echelonCell β C (I v.val)).left)
    {v w : W} (hv : shortest v) (hw : shortest w) :
    le v w ↔ ∀ r, I v r ≤ I w r := by
  constructor
  · intro h
    apply (echelon_range_containment β C).mp
    rw [hclosure w hw]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨v, hv⟩, Set.mem_iUnion.mpr ⟨h, hx⟩⟩
  · intro h
    obtain ⟨x, hx⟩ := echelon_range_nonempty β C (I v)
    have hx' := (echelon_range_containment β C).mpr h hx
    rw [hclosure w hw] at hx'
    obtain ⟨v', hv', hx'⟩ := by simpa only [Set.mem_iUnion] using hx'
    have hi := echelon_same_at_point β C hx hx'
    have he := congrArg Subtype.val (hinj (a₁ := ⟨v, hv⟩) (a₂ := v') hi)
    exact (show v = v'.val from he) ▸ hv'

end GrassmannianOrder

section GrassmannianD07

open CategoryTheory.CartesianMonoidalCategory
open Specs.BruhatOrbitParametrization (IsRepresentative)
open Specs.ParabolicCosetLength (IsShortestInCoset)

private theorem range_comp_schemeOver {k : Type u} [Field k] {X Y Z : SchemeOver k}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Set.range (f ≫ g).left = g.left '' Set.range f.left :=
  Set.range_comp g.left f.left

open private actionOnQuotient from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization

private theorem reduced_immersions_same_range {k : Type u} [Field k] {X Y Z : SchemeOver k}
    (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.IsReduced X.left] [AlgebraicGeometry.IsReduced Y.left]
    [IsImmersion f.left] [IsImmersion g.left] (hr : Set.range f.left = Set.range g.left) :
    ∃ e : X ≅ Y, e.hom ≫ g = f := by
  let a := pullback.fst f.left g.left
  let b := pullback.snd f.left g.left
  have ha : Set.range a = Set.univ := by
    change Set.range (pullback.fst f.left g.left) = _
    rw [Scheme.Pullback.range_fst, ← hr]
    exact Set.eq_univ_of_forall (fun x ↦ Set.mem_range_self x)
  have hb : Set.range b = Set.univ := by
    change Set.range (pullback.snd f.left g.left) = _
    rw [Scheme.Pullback.range_snd, hr]
    exact Set.eq_univ_of_forall (fun x ↦ Set.mem_range_self x)
  letI : IsImmersion a := MorphismProperty.pullback_fst _ _ (inferInstanceAs (IsImmersion g.left))
  letI : IsImmersion b := MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsImmersion f.left))
  letI : IsClosedImmersion a := IsClosedImmersion.of_isPreimmersion a (ha.symm ▸ isClosed_univ)
  letI : IsClosedImmersion b := IsClosedImmersion.of_isPreimmersion b (hb.symm ▸ isClosed_univ)
  letI : Surjective a := ⟨Set.range_eq_univ.mp ha⟩
  letI : Surjective b := ⟨Set.range_eq_univ.mp hb⟩
  letI : IsIso a := isIso_of_isClosedImmersion_of_surjective a
  letI : IsIso b := isIso_of_isClosedImmersion_of_surjective b
  let e := (asIso a).symm ≪≫ asIso b
  have he : e.hom ≫ g.left = f.left := by
    change inv a ≫ b ≫ g.left = _
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  refine ⟨Over.isoMk e (by rw [← Over.w g, ← Category.assoc, he, Over.w f]), ?_⟩
  exact Over.OverMorphism.ext he

open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem bruhatAffineSpace_reduced (k : Type u) [Field k] (m : ℕ) :
    AlgebraicGeometry.IsReduced (Specs.BruhatCells.affineSpace k m).left := by
  let L := (testSpec k).obj (op (CommAlgCat.of k (Polynomial k)))
  letI : Algebra.Smooth k (MvPolynomial PUnit.{u+1} k) := ⟨inferInstance, inferInstance⟩
  have hPol : Algebra.Smooth k (Polynomial k) := Algebra.Smooth.of_equiv
    (MvPolynomial.uniqueAlgEquiv k PUnit.{u+1})
  letI hL : Smooth L.hom := HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr hPol)
  have hs (l : List PUnit.{u+1}) : Smooth (Specs.OrderedRootProducts.product (fun _ ↦ L) l).hom := by
    induction l with
    | nil => exact inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of k))))
    | cons i l ih =>
      letI := ih
      let X := Specs.OrderedRootProducts.product (fun _ : PUnit.{u+1} ↦ L) l
      change Smooth (pullback.fst L.hom X.hom ≫ L.hom)
      infer_instance
  letI : Smooth (Specs.BruhatCells.affineSpace k m).hom := hs (List.replicate m PUnit.unit)
  exact isReduced_of_smooth_over_field (Specs.BruhatCells.affineSpace k m).hom

private theorem pivotSet_swap_of_advance {d n : ℕ} {J I : Fin d ↪o Fin n} {r : Fin d}
    (h : AdvancesPivot J I r) :
    Equiv.swap (ULift.up (J r) : ULift.{u} (Fin n)) (ULift.up (I r)) ''
      ((pivotSet.{u} J).val : Set (ULift.{u} (Fin n))) =
      ((pivotSet.{u} I).val : Set (ULift.{u} (Fin n))) := by
  let f := Equiv.swap (ULift.up (J r) : ULift.{u} (Fin n)) (ULift.up (I r))
  have hf (s : Fin d) : f (ULift.up (J s)) = ULift.up (I s) := by
    let e : Fin n ≃ ULift.{u} (Fin n) := Equiv.ulift.symm
    exact (Function.Injective.map_swap e.injective (J r) (I r) (J s)).symm.trans
      (congrArg e (pivotAdvanceTransposition J I r h s))
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, hs⟩ := (mem_pivotSet J y).mp hy
    have he : y = ULift.up (J s) := ULift.down_injective hs.symm
    rw [he, hf]
    exact (mem_pivotSet I _).mpr ⟨s, rfl⟩
  · intro hx
    obtain ⟨s, hs⟩ := (mem_pivotSet I x).mp hx
    exact ⟨ULift.up (J s), (mem_pivotSet J _).mpr ⟨s, rfl⟩, (hf s).trans (ULift.down_injective hs)⟩

private theorem strict_wordLength_of_subword {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum Idx X Y) (b : P.Base) {v w : P.weylGroup}
    (h : Specs.SchubertClosures.SubwordLE P b v w) (hne : v ≠ w) :
    Specs.SimpleRoots.wordLength P b v < Specs.SimpleRoots.wordLength P b w := by
  obtain ⟨l, hred, hl, m, hm, hv⟩ := h
  have hlen : Specs.SimpleRoots.wordLength P b w = l.length := hl ▸ hred
  have hlt : m.length < l.length := lt_of_le_of_ne hm.length_le (fun he ↦ hne
    (hv.symm.trans ((congrArg (Specs.SimpleRoots.wordProduct P b) (hm.eq_of_length he)).trans hl)))
  have hle : Specs.SimpleRoots.wordLength P b v ≤ m.length := csInf_le' ⟨m, rfl, hv⟩
  exact hle.trans_lt (hlen ▸ hlt)

set_option maxHeartbeats 1800000 in
private theorem grassmannianBruhat_of_splitCells
    (hD07 : Specs.PartialFlags.SplitCells.{u}) : GrassmannianBruhat.{u} := by
  classical
  intro k V _ _ _ _ n d β hn hd
  dsimp only
  intro P F G E A S hlocal
  let ranks : Fin 1 → ℕ := fun _ ↦ d
  let C := (P 0).charts
  obtain ⟨M⟩ := canonicalTypeAPair k n hn G E
  obtain ⟨hcT, hdata⟩ := hD07 k G M.reductive M.torus M.borel M.split M.maximal M.isBorel M.torusInBorel
  letI := hcT
  obtain ⟨D, W, U, c, b, hregular, hpositive, hbase, hrep, hQ, hpara⟩ := hdata
  let I := uncutSimpleRoots M.characters ranks
  have hI : I ⊆ b.support := (typeABlockParabolics M D c b hpositive hbase ranks).1
  obtain ⟨H, hR, hshort, hpartial⟩ := hpara I hI
  have hF := standardCoordinateFlagQuotient β ranks P F G E A S M D c b hpositive hbase U H hlocal
  obtain ⟨Q⟩ := hQ
  obtain ⟨R⟩ := hR
  obtain ⟨q, hq, -⟩ := hF.2.2.2 R
  letI := singletonIncidence_isIso β P F
  let e := q ≪≫ asIso (singletonProjection β P F)
  have hproj : R.projection ≫ e.hom = orbitMap A.onFlags S.point ≫ singletonProjection β P F := by
    dsimp [e]
    rw [← Category.assoc, hq]
  obtain ⟨W₀⟩ := typeAWeylAction M D W hrep
  choose n₀ hn₀ using hrep
  let g (w : D.rootDatum.weylGroup) := n₀ w ≫ W.normalizer.inclusion.hom.hom
  have hcells := hpartial Q R n₀ hn₀
  dsimp only at hcells
  obtain ⟨π, a, a', Z, C₀, hπ, hproper, ha, ha', hOrbit, hcoset, hdisj, hcov, hclosed⟩ := hcells
  let j (w : D.rootDatum.weylGroup) := (C₀ w).orbitInclusion ≫ π
  let cells (w : D.rootDatum.weylGroup) := Set.range (j w).left
  let isMin := Specs.PartialFlags.IsMinimal D b I
  choose piv hpiv using fun w : D.rootDatum.weylGroup ↦ pivot_of_permutation_exists hd (W₀.equiv w)
  have hmatch (w : D.rootDatum.weylGroup) :
      e.hom.left '' cells w = Set.range (echelonCell β C (piv w)).left := by
    change e.hom.left '' Set.range (j w).left = _
    rw [hOrbit w, ← range_comp_schemeOver, ← Category.assoc (toUnit _) (g w) R.projection,
      actionOnQuotient (G := G) R a' ha', Category.assoc, hproj]
    exact singleton_borel_orbit_range β P F E A S hd M.borel M.upper (g w) (W₀.equiv w)
      (fun S i j hij ↦ by
        change (E.hom.app S (toUnit ((testSpec k).obj (op S)) ≫ n₀ w ≫ W.normalizer.inclusion.hom.hom) :
          Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) S).val i j = 0
        rw [representative_matrix_map W (n₀ w) S]
        change algebraMap k S ((representativeMatrix W E (n₀ w)).val i j) = 0
        exact (congrArg (algebraMap k S) (W₀.matrices w (n₀ w) (hn₀ w) i j hij)).trans (map_zero _)) (piv w) (hpiv w)
  have he_inj : Function.Injective e.hom.left := (asIso ((Over.forget _).map e.hom)).hom.homeomorph.injective
  have hpiv_match {u v : D.rootDatum.weylGroup} (huv : cells u = cells v) : piv u = piv v := by
    have he := (hmatch u).symm.trans (congrArg (e.hom.left '' ·) huv |>.trans (hmatch v))
    obtain ⟨x, hx⟩ := echelon_range_nonempty β C (piv u)
    exact echelon_same_at_point β C hx (he ▸ hx)
  have hlabels : Function.Bijective (fun w : {w // isMin w} ↦ piv w.val) := by
    constructor
    · intro v w hvw
      apply Subtype.ext
      have hs : cells v.val = cells w.val := (Set.image_injective.mpr he_inj)
        ((hmatch v.val).trans (congrArg (fun p ↦ Set.range (echelonCell β C p).left) hvw |>.trans (hmatch w.val).symm))
      have hh := (hcoset v.val w.val).mp hs
      exact (hshort v.val).unique v.property (shortest_translate _ _ hh w.property)
    · intro p
      obtain ⟨σ, hσ⟩ := permutation_extending_pivots hd p
      let w := W₀.equiv.symm σ
      have he : W₀.equiv w = σ := W₀.equiv.apply_symm_apply σ
      have hw : piv w = p := pivot_tuples_same_set (Finset.coe_inj.mp ((hpiv w).trans (he ▸ hσ.symm)))
      obtain ⟨v, hv, -⟩ := hshort w
      exact ⟨⟨v, shortest_at_self _ _ hv⟩, (hpiv_match ((hcoset w v).mpr hv.1).symm).trans hw⟩
  let labels := Equiv.ofBijective (fun w : {w // isMin w} ↦ piv w.val) hlabels
  have hcl (w : D.rootDatum.weylGroup) (hw : isMin w) :
      closure (Set.range (echelonCell β C (piv w)).left) =
        ⋃ (v : {v // isMin v}) (_ : Specs.SchubertClosures.SubwordLE D.rootDatum b v.val w),
          Set.range (echelonCell β C (piv v.val)).left := by
    have hh := (hclosed w hw).2.2.2.2
    change Set.range (Specs.SchubertClosures.closureIdeal (j w).left).subschemeι = _ at hh
    rw [Specs.SchubertClosures.closureIdeal, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at hh
    change closure (cells w) = ⋃ (v : {v // isMin v})
      (_ : Specs.SchubertClosures.SubwordLE D.rootDatum b v.val w), cells v.val at hh
    have hei := ((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom.homeomorph.image_closure (cells w)
    change e.hom.left '' closure (cells w) = closure (e.hom.left '' cells w) at hei
    rw [← hmatch w, ← hei, hh]
    simp only [Set.image_iUnion, hmatch]
  have horder (v w : {w // isMin w}) : Specs.SchubertClosures.SubwordLE D.rootDatum b v.val w.val ↔
      ∀ r, labels v r ≤ labels w r :=
    echelon_subword_order β C piv isMin (Specs.SchubertClosures.SubwordLE D.rootDatum b)
      hlabels.1 hcl v.property w.property
  refine ⟨M, hcT, D, W, U, c, b, hpositive, hbase, H, hF, R, e, W₀, n₀, a',
    (fun w ↦ (C₀ w).orbit), j, labels, hn₀, hproj, ha', ?_, ?_, horder, ?_⟩
  · intro w
    simpa only [g, j, Category.assoc] using hOrbit w
  · intro w
    refine ⟨hpiv w.val, ?_⟩
    have hh := hclosed w.val w.property
    letI : IsImmersion (j w.val).left := hh.1
    letI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    haveI : IsImmersion (j w.val ≫ e.hom).left := inferInstanceAs (IsImmersion ((j w.val).left ≫ e.hom.left))
    letI : IsImmersion (echelonCell β C (piv w.val)).left := (echelonCellImmersion β C (piv w.val)).2.1
    letI : AlgebraicGeometry.IsReduced (echelonScheme k (piv w.val)).left := inferInstanceAs
      (AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (MvPolynomial (CellEntry.{u} (piv w.val)) k))))
    obtain ⟨f⟩ := hh.2.1
    letI := bruhatAffineSpace_reduced k (Specs.SimpleRoots.wordLength D.rootDatum b w.val)
    letI : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
    letI := isReduced_of_isOpenImmersion f.hom.left
    exact reduced_immersions_same_range (j w.val ≫ e.hom) (echelonCell β C (piv w.val))
      ((range_comp_schemeOver (j w.val) e.hom).trans (hmatch w.val))
  · intro v w r hadv
    change AdvancesPivot (piv v.val) (piv w.val) r at hadv
    let p : ULift.{u} (Fin n) := ULift.up (piv v.val r)
    let q : ULift.{u} (Fin n) := ULift.up (piv w.val r)
    have hnext : q.down.val = p.down.val + 1 := hadv.1
    have hne : p ≠ q := by
      intro he
      have := congrArg (fun i : ULift.{u} (Fin n) ↦ i.down.val) he
      omega
    let α : Specs.AbstractPairing.Root M.torus :=
      ⟨M.characters.ratio p q, (M.absolute _).mpr ⟨p, q, hne, rfl⟩⟩
    have hα : α ∈ b.support := (typeASimpleRoots M D c b hpositive hbase α).mpr ⟨p, q, hnext, rfl⟩
    let s := RootPairing.weylGroup.ofIdx D.rootDatum α
    have hs : W₀.equiv s = Equiv.swap p q := W₀.reflection α p q hne rfl
    have hp : piv (s * v.val) = piv w.val := by
      apply pivot_tuples_same_set
      apply Finset.coe_inj.mp
      rw [hpiv, map_mul, hs]
      change ((Equiv.swap p q : Equiv.Perm (ULift.{u} (Fin n))) ∘ W₀.equiv v.val) ''
        {i | i.down.val < d} = _
      rw [Set.image_comp, ← hpiv v.val, pivotSet_swap_of_advance hadv]
    have hCell : cells w.val = cells (s * v.val) := (Set.image_injective.mpr he_inj)
      ((hmatch w.val).trans ((congrArg (fun P ↦ Set.range (echelonCell β C P).left) hp.symm).trans (hmatch _).symm))
    have hCoset := (hcoset w.val (s * v.val)).mp hCell
    let len := Specs.SimpleRoots.wordLength D.rootDatum b
    have hlt : len v.val < len w.val := by
      apply strict_wordLength_of_subword
      · exact (horder v w).mpr (advancesPivot_le hadv)
      · intro he
        have hl := hadv.1
        rw [he] at hl
        omega
    have hup : len (s * v.val) ≤ len v.val + 1 := by
      obtain ⟨l, hred, hl, _⟩ := (horder v v).mpr (fun _ ↦ le_rfl)
      let letter : b.support := ⟨α, hα⟩
      have hv : len v.val = l.length := hl ▸ hred
      have hp : Specs.SimpleRoots.wordProduct D.rootDatum b (letter :: l) = s * v.val := by
        change s * Specs.SimpleRoots.wordProduct D.rootDatum b l = s * v.val
        rw [hl]
      rw [hv]
      exact csInf_le' ⟨letter :: l, rfl, hp⟩
    have hlo : len w.val ≤ len (s * v.val) := by
      have h := w.property.2 ⟨w.val⁻¹ * (s * v.val), hCoset⟩
      change len w.val ≤ len (w.val * (w.val⁻¹ * (s * v.val))) at h
      simpa only [mul_inv_cancel_left] using h
    have hLen : len w.val = len v.val + 1 := by omega
    have hLen' : len (s * v.val) = len w.val := by omega
    have hsv : s * v.val = w.val := (hshort w.val).unique
      ⟨hCoset, fun u ↦ hLen'.trans_le (w.property.2 u)⟩ w.property
    have hss : s * s = 1 := W₀.equiv.injective (by rw [map_mul, hs, map_one, Equiv.swap_mul_self])
    exact ⟨α, hα, rfl, by rw [← hsv, ← mul_assoc, hss, one_mul], hLen⟩

end GrassmannianD07

/-- The actual split partial flag decomposition agrees with the echelon cells. -/
theorem grassmannianBruhat : GrassmannianBruhat.{u} :=
  grassmannianBruhat_of_splitCells (_root_.LinearAlgebraicGroups.Flag.PartialFlags.partialFlags.{u}).2

end GrassmannianComparison

end

end LinearAlgebraicGroups.Flag.GrassmannianExample
