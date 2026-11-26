import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj LaurentPolynomial

universe u

namespace LinearAlgebraicGroups.CocharacterDynamics

open LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open private schemeKernel_exists schemeKernel_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra groupAlgebraMap)
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private integerHomEquiv pointsIso_spec pointsIso_precompose
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private mono_over closedSubgroupOfLocus centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private factorsThrough_iff_cover overCoverMap overCoverObj quotientProjection
  factorsThrough_affineQuotient
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes
open private conjugationAction isFixedBy_conjugation_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G H : GroupScheme k}

section LaurentCoefficients

variable {R : Type u} [CommRing R]

theorem coeff_toLaurent_nat (p : Polynomial R) (n : ℕ) :
    p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  change (Finsupp.mapDomain ((↑) : ℕ → ℤ) p.toFinsupp.coeff) (n : ℤ) = p.coeff n
  rw [Finsupp.mapDomain_apply_of_injective Nat.cast_injective]
  rfl

theorem coeff_toLaurent_neg (p : Polynomial R) {n : ℤ} (hn : n < 0) :
    p.toLaurent.coeff n = 0 := by
  rw [← Finsupp.notMem_support_iff, LaurentPolynomial.support_coeff_toLaurent]
  intro h
  rcases Finset.mem_map.mp h with ⟨m, hm, he⟩
  change (m : ℤ) = n at he
  exact (not_lt_of_ge (Int.natCast_nonneg m)) (he ▸ hn)

theorem coeff_trunc (f : LaurentPolynomial R) (n : ℕ) :
    (LaurentPolynomial.trunc f).coeff n = f.coeff (n : ℤ) := rfl

/-- A Laurent polynomial extends over zero precisely when every negative
coefficient vanishes, with arbitrary coefficients in the test ring. -/
theorem exists_toLaurent_eq_iff {f : LaurentPolynomial R} :
    (∃ p : Polynomial R, p.toLaurent = f) ↔ ∀ n < 0, f.coeff n = 0 := by
  constructor
  · rintro ⟨p, rfl⟩ n hn
    exact coeff_toLaurent_neg p hn
  · intro h
    refine ⟨LaurentPolynomial.trunc f, LaurentPolynomial.ext fun n ↦ ?_⟩
    by_cases hn : n < 0
    · rw [coeff_toLaurent_neg _ hn, h n hn]
    · lift n to ℕ using le_of_not_gt hn
      rw [coeff_toLaurent_nat, coeff_trunc]

/-- Absence of negative coefficients also gives a lift of algebra homomorphisms. -/
theorem exists_polynomialLift_iff {A : Type u} [CommRing A] [Algebra k A] [Algebra k R]
    (f : A →ₐ[k] LaurentPolynomial R) :
    (∃ p : A →ₐ[k] Polynomial R, (Polynomial.toLaurentAlg.restrictScalars k).comp p = f) ↔
      ∀ a n, n < 0 → (f a).coeff n = 0 := by
  let j : Polynomial R →ₐ[k] LaurentPolynomial R := Polynomial.toLaurentAlg.restrictScalars k
  constructor
  · rintro ⟨p, rfl⟩ a n hn
    exact coeff_toLaurent_neg (p a) hn
  · intro h
    let e := AlgEquiv.ofInjective j Polynomial.toLaurent_injective
    let fr := f.codRestrict j.range fun a ↦ (AlgHom.mem_range j).mpr
      (exists_toLaurent_eq_iff.mpr (h a))
    refine ⟨e.symm.toAlgHom.comp fr, ?_⟩
    ext a : 1
    exact congrArg Subtype.val (e.apply_symm_apply (fr a))

/-- Regularity in both the original and the inverse parameter leaves only the
constant coefficient. -/
theorem constant_of_regular_and_inverse {f : LaurentPolynomial R}
    (h₁ : ∃ p : Polynomial R, p.toLaurent = f)
    (h₂ : ∃ p : Polynomial R, p.toLaurent = LaurentPolynomial.invert f) :
    f = LaurentPolynomial.C (f.coeff 0) := by
  apply LaurentPolynomial.ext
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [exists_toLaurent_eq_iff.mp h₁ n hn]
    simp only [LaurentPolynomial.C_apply, ite_eq_right (ne_of_lt hn)]
  · simp only [LaurentPolynomial.C_apply, ite_true]
  · have he := exists_toLaurent_eq_iff.mp h₂ (-n) (by lia)
    rw [LaurentPolynomial.invert_apply, neg_neg] at he
    rw [he]
    simp only [LaurentPolynomial.C_apply, ite_eq_right (ne_of_gt hn)]

end LaurentCoefficients

/-- Factorization through a closed immersion can be checked on every affine family. -/
theorem factorsThroughClosed_iff {X Y T : SchemeOver k} (i : Y ⟶ X)
    (hi : IsClosedImmersion i.left) (g : T ⟶ X) :
    (∃ h, h ≫ i = g) ↔
      ∀ (R : TestAlgebra k) (a : Points T R), ∃ h, h ≫ i = a ≫ g := by
  constructor
  · rintro ⟨h, rfl⟩ R a
    exact ⟨a ≫ h, Category.assoc _ _ _⟩
  · intro H
    let := hi
    apply (factorsThrough_iff_cover T.left.affineCover i g).mpr
    intro j
    let U := overCoverObj T.left.affineCover j
    have hU : IsAffine U.left := by
      change IsAffine (T.left.affineCover.X j)
      infer_instance
    obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hU
    let e' : (testSpec k).obj (op A.unop) ≅ U := e
    obtain ⟨h, hh⟩ := H A.unop (e'.hom ≫ overCoverMap T.left.affineCover j)
    refine ⟨e'.inv ≫ h, ?_⟩
    rw [Category.assoc, hh, ← Category.assoc e'.inv, Iso.inv_hom_id_assoc]

/-- A closed affine locus whose affine families form a natural subgroup
inherits its subgroup scheme structure. -/
theorem closedSubgroupOfAffineLocus
    (P : ∀ R : TestAlgebra k, Subgroup (GroupPoints G R))
    (natural : ∀ {R S : TestAlgebra k} (f : R ⟶ S) {g : GroupPoints G R},
      g ∈ P R → mapPoints f g ∈ P S)
    {Z : SchemeOver k} (j : Z ⟶ G.X) (hj : IsClosedImmersion j.left)
    (hP : ∀ (R : TestAlgebra k) (g : GroupPoints G R),
      g ∈ P R ↔ ∃ z : Points Z R, z ≫ j = g) :
    ∃ S : ClosedSubgroup G, RepresentsOnAlgebras S (fun R g ↦ g ∈ P R) := by
  let Q (T : SchemeOver k) : Subgroup (T ⟶ G.X) :=
    { carrier := {g | ∀ (R : TestAlgebra k) (a : Points T R), a ≫ g ∈ P R}
      one_mem' := fun R a ↦ by rw [MonObj.comp_one]; exact (P R).one_mem
      mul_mem' := fun {x y} hx hy R a ↦ by
        rw [MonObj.comp_mul]; exact (P R).mul_mem (hx R a) (hy R a)
      inv_mem' := fun {x} hx R a ↦ by
        rw [GrpObj.comp_inv]; exact (P R).inv_mem (hx R a) }
  obtain ⟨S, hS⟩ := closedSubgroupOfLocus Q j hj (fun T g ↦ by
    change (∀ (R : TestAlgebra k) (a : Points T R), a ≫ g ∈ P R) ↔ _
    rw [factorsThroughClosed_iff j hj]
    exact ⟨fun h R a ↦ (hP R _).mp (h R a), fun h R a ↦ (hP R _).mpr (h R a)⟩)
  refine ⟨S, fun R g ↦ ?_⟩
  apply Iff.trans _ (hS _ g)
  change g ∈ P R ↔ ∀ (S : TestAlgebra k)
    (a : Points ((testSpec k).obj (op R)) S), a ≫ g ∈ P S
  constructor
  · intro hg S a
    let F := algSpec.fullyFaithful (R := CommRingCat.of k)
    let f := F.preimage a
    have hf : (testSpec k).map f.unop.op = a := F.map_preimage a
    have ha := natural f.unop hg
    change ((testSpec k).map f.unop.op ≫ g) ∈ P S at ha
    rwa [hf] at ha
  · intro h
    have hg := h R (𝟙 _)
    change (𝟙 ((testSpec k).obj (op R)) ≫ g) ∈ P R at hg
    rwa [Category.id_comp] at hg

/-- A polynomial family in an affine scheme is determined on the punctured line,
even for a test algebra with nilpotents. -/
theorem polynomialFamily_injective (ha : IsAffine G.X.left) (R : TestAlgebra k) :
    Function.Injective (mapPoints (X := G.X) (polynomialToLaurent R)) := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  intro f g h
  have hh : mapPoints (polynomialToLaurent R) (f ≫ e.inv) =
      mapPoints (polynomialToLaurent R) (g ≫ e.inv) := by
    simpa only [mapPoints, Category.assoc] using congrArg (· ≫ e.inv) h
  let a := F.preimage (f ≫ e.inv)
  let b := F.preimage (g ≫ e.inv)
  have ha' : (testSpec k).map a = f ≫ e.inv := F.map_preimage _
  have hb' : (testSpec k).map b = g ≫ e.inv := F.map_preimage _
  have hab : (polynomialToLaurent R).op ≫ a = (polynomialToLaurent R).op ≫ b := by
    apply F.map_injective
    change (testSpec k).map (_ ≫ _) = (testSpec k).map (_ ≫ _)
    rw [Functor.map_comp, Functor.map_comp, ha', hb']
    exact hh
  have hpre : a = b := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply Polynomial.toLaurent_injective
    exact DFunLike.congr_fun (congrArg (fun p ↦ p.unop.hom) hab) x
  apply (cancel_mono e.inv).mp
  rw [← ha', ← hb', hpre]

/-- Coefficient extension on polynomial algebras. -/
def mapPolynomial {R S : TestAlgebra k} (a : R ⟶ S) :
    polynomialAlgebra R ⟶ polynomialAlgebra S :=
  CommAlgCat.ofHom (Polynomial.mapAlgHom a.hom)

/-- Coefficient extension on Laurent polynomial algebras. -/
def mapLaurent {R S : TestAlgebra k} (a : R ⟶ S) :
    laurentAlgebra R ⟶ laurentAlgebra S :=
  CommAlgCat.ofHom (AddMonoidAlgebra.mapAlgHom ℤ a.hom)

theorem mapPoints_comp {X : SchemeOver k} {R S T : TestAlgebra k}
    (a : R ⟶ S) (b : S ⟶ T) (p : Points X R) :
    mapPoints (a ≫ b) p = mapPoints b (mapPoints a p) := by
  simp only [mapPoints, op_comp, Functor.map_comp, Category.assoc]

theorem mapPoints_unitPoint {R S : TestAlgebra k} (a : R ⟶ S) (t : Rˣ) :
    mapPoints a (unitPoint R t) = unitPoint S (Units.map a.hom.toMonoidHom t) := by
  unfold mapPoints unitPoint
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply CommAlgCat.hom_ext
  change a.hom.comp (unitCoordinates R t) = unitCoordinates S (Units.map a.hom.toMonoidHom t)
  apply (MonoidAlgebra.lift k S Specs.DiagonalizableGroups.IntegerCharacters).symm.injective
  apply MonoidHom.ext
  intro m
  simp only [MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply, unitCoordinates,
    MonoidAlgebra.lift_single, one_smul]
  change a.hom (↑(t ^ Multiplicative.toAdd m.down) : R) =
    (↑((Units.map a.hom.toMonoidHom t) ^ Multiplicative.toAdd m.down) : S)
  exact congrArg Units.val (map_zpow (Units.map a.hom.toMonoidHom) t _)

theorem mapPoints_cocharacterPoint {R S : TestAlgebra k} (a : R ⟶ S)
    (cochar : Cocharacter G) (t : Rˣ) :
    mapPoints a (cocharacterPoint cochar R t) =
      cocharacterPoint cochar S (Units.map a.hom.toMonoidHom t) := by
  change (testSpec k).map a.op ≫ unitPoint R t ≫ cochar.hom.hom =
    unitPoint S (Units.map a.hom.toMonoidHom t) ≫ cochar.hom.hom
  rw [← Category.assoc]
  exact congrArg (· ≫ cochar.hom.hom) (mapPoints_unitPoint a t)

theorem mapLaurent_parameter {R S : TestAlgebra k} (a : R ⟶ S) :
    Units.map (mapLaurent a).hom.toMonoidHom (laurentParameter R) = laurentParameter S := by
  apply Units.ext
  change AddMonoidAlgebra.mapAlgHom ℤ a.hom (LaurentPolynomial.T 1) = LaurentPolynomial.T 1
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapAlgHom_single, map_one]

theorem polynomialToLaurent_naturality {R S : TestAlgebra k} (a : R ⟶ S) :
    mapPolynomial a ≫ polynomialToLaurent S = polynomialToLaurent R ≫ mapLaurent a := by
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext'
  · apply AlgHom.ext
    intro c
    change Polynomial.toLaurent (Polynomial.map a.hom.toRingHom (Polynomial.C c)) =
      AddMonoidAlgebra.mapAlgHom ℤ a.hom (Polynomial.toLaurent (Polynomial.C c))
    simp only [Polynomial.map_C, Polynomial.toLaurent_C, ← LaurentPolynomial.single_eq_C,
      AddMonoidAlgebra.mapAlgHom_single]
    rfl
  · change Polynomial.toLaurent (Polynomial.map a.hom.toRingHom Polynomial.X) =
      AddMonoidAlgebra.mapAlgHom ℤ a.hom (Polynomial.toLaurent Polynomial.X)
    simp only [Polynomial.map_X, Polynomial.toLaurent_X, LaurentPolynomial.T,
      AddMonoidAlgebra.mapAlgHom_single, map_one]

theorem polynomialEvaluate_zero_naturality {R S : TestAlgebra k} (a : R ⟶ S) :
    mapPolynomial a ≫ polynomialEvaluate S 0 = polynomialEvaluate R 0 ≫ a := by
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext'
  · apply AlgHom.ext
    intro c
    change Polynomial.aevalTower (AlgHom.id k S) 0
        (Polynomial.map a.hom.toRingHom (Polynomial.C c)) =
      a.hom (Polynomial.aevalTower (AlgHom.id k R) 0 (Polynomial.C c))
    simp
  · change Polynomial.aevalTower (AlgHom.id k S) 0 (Polynomial.map a.hom.toRingHom Polynomial.X) =
      a.hom (Polynomial.aevalTower (AlgHom.id k R) 0 Polynomial.X)
    simp

theorem laurentConstants_naturality {R S : TestAlgebra k} (a : R ⟶ S) :
    laurentConstants R ≫ mapLaurent a = a ≫ laurentConstants S := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro c
  change AddMonoidAlgebra.mapAlgHom ℤ a.hom (LaurentPolynomial.C c) =
    LaurentPolynomial.C (a.hom c)
  simp only [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapAlgHom_single]

theorem orbit_naturality {R S : TestAlgebra k} (a : R ⟶ S) (cochar : Cocharacter G)
    (g : GroupPoints G R) :
    mapPoints (mapLaurent a) (orbit cochar g) = orbit cochar (mapPoints a g) := by
  let t := cocharacterPoint cochar (laurentAlgebra R) (laurentParameter R)
  let t' := cocharacterPoint cochar (laurentAlgebra S) (laurentParameter S)
  let gR : GroupPoints G (laurentAlgebra R) := mapPoints (laurentConstants R) g
  let gS : GroupPoints G (laurentAlgebra S) := mapPoints (laurentConstants S) (mapPoints a g)
  let m := (((groupPointsFunctor k).obj G).map (mapLaurent a)).hom
  have ht : m t = t' := by
    change mapPoints (mapLaurent a) t = t'
    exact (mapPoints_cocharacterPoint (mapLaurent a) cochar (laurentParameter R)).trans
      (congrArg (cocharacterPoint cochar (laurentAlgebra S)) (mapLaurent_parameter a))
  have hg : m gR = gS := by
    change mapPoints (mapLaurent a) (mapPoints (laurentConstants R) g) =
      mapPoints (laurentConstants S) (mapPoints a g)
    rw [← mapPoints_comp, laurentConstants_naturality, mapPoints_comp]
  change m (t * gR * t⁻¹) = t' * gS * t'⁻¹
  rw [map_mul, map_mul, map_inv, ht, hg]

theorem HasLimit.map {cochar : Cocharacter G} {R S : TestAlgebra k} {g z : GroupPoints G R}
    (h : HasLimit cochar g z) (a : R ⟶ S) :
    HasLimit cochar (mapPoints a g) (mapPoints a z) := by
  obtain ⟨f, hf, hz⟩ := h
  refine ⟨mapPoints (mapPolynomial a) f, ?_, ?_⟩
  · rw [← mapPoints_comp, polynomialToLaurent_naturality, mapPoints_comp, hf, orbit_naturality]
  · rw [← mapPoints_comp, polynomialEvaluate_zero_naturality, mapPoints_comp, hz]

/-- The orbit family is a homomorphism of the point groups over the two test rings. -/
def orbitHom (cochar : Cocharacter G) (R : TestAlgebra k) :
    GroupPoints G R →* GroupPoints G (laurentAlgebra R) :=
  (MulAut.conj (cocharacterPoint cochar (laurentAlgebra R) (laurentParameter R))).toMonoidHom.comp
    (((groupPointsFunctor k).obj G).map (laurentConstants R)).hom

theorem orbitHom_apply (cochar : Cocharacter G) (R : TestAlgebra k) (g : GroupPoints G R) :
    orbitHom cochar R g = orbit cochar g :=
  rfl

theorem hasLimit_one (cochar : Cocharacter G) (R : TestAlgebra k) :
    HasLimit cochar (1 : GroupPoints G R) 1 := by
  refine ⟨1, ?_, ?_⟩
  · change (((groupPointsFunctor k).obj G).map (polynomialToLaurent R)).hom 1 =
      orbitHom cochar R 1
    rw [map_one, map_one]
  · exact map_one (((groupPointsFunctor k).obj G).map (polynomialEvaluate R 0)).hom

theorem HasLimit.mul {cochar : Cocharacter G} {R : TestAlgebra k}
    {g h z w : GroupPoints G R} (hg : HasLimit cochar g z) (hh : HasLimit cochar h w) :
    HasLimit cochar (g * h) (z * w) := by
  obtain ⟨g', hg', hz⟩ := hg
  obtain ⟨h', hh', hw⟩ := hh
  exact ⟨g' * h',
    (map_mul (((groupPointsFunctor k).obj G).map (polynomialToLaurent R)).hom g' h').trans
      ((congrArg₂ (· * ·) hg' hh').trans ((orbitHom cochar R).map_mul g h).symm),
    (map_mul (((groupPointsFunctor k).obj G).map (polynomialEvaluate R 0)).hom g' h').trans
      (congrArg₂ (· * ·) hz hw)⟩

theorem HasLimit.inv {cochar : Cocharacter G} {R : TestAlgebra k} {g z : GroupPoints G R}
    (hg : HasLimit cochar g z) : HasLimit cochar g⁻¹ z⁻¹ := by
  obtain ⟨g', hg', hz⟩ := hg
  exact ⟨g'⁻¹,
    (map_inv (((groupPointsFunctor k).obj G).map (polynomialToLaurent R)).hom g').trans
      ((congrArg Inv.inv hg').trans ((orbitHom cochar R).map_inv g).symm),
    (map_inv (((groupPointsFunctor k).obj G).map (polynomialEvaluate R 0)).hom g').trans
      (congrArg Inv.inv hz)⟩

theorem parabolicSubgroupExists : Specs.CocharacterDynamics.ParabolicSubgroupExists.{u} := by
  intro k _ G cochar
  let H := G.val
  let P (R : TestAlgebra k) : Subgroup (GroupPoints H R) :=
    { carrier := {g | HasExtension cochar g}
      one_mem' := ⟨1, hasLimit_one cochar R⟩
      mul_mem' := fun ⟨z, hz⟩ ⟨w, hw⟩ ↦ ⟨z * w, hz.mul hw⟩
      inv_mem' := fun ⟨z, hz⟩ ↦ ⟨z⁻¹, hz.inv⟩ }
  have hP {R S : TestAlgebra k} (a : R ⟶ S) {g : GroupPoints H R}
      (hg : g ∈ P R) : mapPoints a g ∈ P S := by
    obtain ⟨z, hz⟩ := hg
    exact ⟨_, hz.map a⟩
  obtain ⟨Aop, ⟨e₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr G.property.1
  let A := Aop.unop
  let e : (testSpec k).obj (op A) ≅ H.X := e₀
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let x : GroupPoints H A := e.hom
  let α : A ⟶ laurentAlgebra A := (F.preimage (orbit cochar x ≫ e.inv)).unop
  have hα : (testSpec k).map α.op = orbit cochar x ≫ e.inv := F.map_preimage _
  let I : Ideal A := Ideal.span {c | ∃ a n, n < 0 ∧ c = (α.hom a).coeff n}
  let q := (testSpec k).map (quotientProjection I).op
  have hq : IsClosedImmersion q.left :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hj : IsClosedImmersion (q ≫ e.hom).left :=
    IsClosedImmersion.comp q.left e.hom.left
  refine closedSubgroupOfAffineLocus P (fun {_ _} a {_} hg ↦ hP a hg) (q ≫ e.hom) hj ?_
  intro R g
  let f : A ⟶ R := (F.preimage (g ≫ e.inv)).unop
  have hf : (testSpec k).map f.op = g ≫ e.inv := F.map_preimage _
  have hfx : mapPoints f x = g := by
    change (testSpec k).map f.op ≫ e.hom = g
    rw [hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have horbit : (testSpec k).map (α ≫ mapLaurent f).op = orbit cochar g ≫ e.inv := by
    rw [op_comp, Functor.map_comp, hα, ← Category.assoc]
    exact congrArg (· ≫ e.inv) ((orbit_naturality f cochar x).trans (congrArg (orbit cochar) hfx))
  have hquot : (∃ z : Points ((testSpec k).obj (op (CommAlgCat.of k (A ⧸ I)))) R,
      z ≫ q ≫ e.hom = (g : Points H.X R)) ↔ I ≤ RingHom.ker f.hom := by
    rw [← factorsThrough_affineQuotient I (g ≫ e.inv)]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have hh := congrArg (· ≫ e.inv) hz
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have hh := congrArg (· ≫ e.hom) hz
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh
  refine Iff.trans ?_ hquot.symm
  rw [Ideal.span_le]
  have crit : HasExtension cochar g ↔
      ∃ p : A →ₐ[k] Polynomial R,
        (Polynomial.toLaurentAlg.restrictScalars k).comp p = (α ≫ mapLaurent f).hom := by
    constructor
    · rintro ⟨_, y, hy, _⟩
      let p := (F.preimage (y ≫ e.inv)).unop
      have hp : (testSpec k).map p.op = y ≫ e.inv := F.map_preimage _
      have hh : (p ≫ polynomialToLaurent R).op = (α ≫ mapLaurent f).op := by
        apply F.map_injective
        change (testSpec k).map (p ≫ polynomialToLaurent R).op = _
        rw [op_comp, Functor.map_comp, hp, horbit, ← Category.assoc]
        exact congrArg (· ≫ e.inv) hy
      exact ⟨p.hom, congrArg (fun a ↦ a.unop.hom) hh⟩
    · rintro ⟨p, hp⟩
      let p' : A ⟶ polynomialAlgebra R := CommAlgCat.ofHom p
      let y : GroupPoints H (polynomialAlgebra R) := (testSpec k).map p'.op ≫ e.hom
      refine ⟨mapPoints (polynomialEvaluate R 0) y, y, ?_, rfl⟩
      have hp' : p' ≫ polynomialToLaurent R = α ≫ mapLaurent f := CommAlgCat.hom_ext hp
      change (testSpec k).map (polynomialToLaurent R).op ≫ (testSpec k).map p'.op ≫ e.hom = _
      rw [← Category.assoc, ← Functor.map_comp, ← op_comp, hp', horbit, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
  change HasExtension cochar g ↔ _
  rw [crit, exists_polynomialLift_iff]
  constructor
  · rintro h c ⟨a, n, hn, rfl⟩
    change f.hom ((α.hom a).coeff n) = 0
    exact (AddMonoidAlgebra.coeff_mapAlgHom f.hom (α.hom a) n).symm.trans (h a n hn)
  · intro h a n hn
    change (AddMonoidAlgebra.mapAlgHom ℤ f.hom (α.hom a)).coeff n = 0
    rw [AddMonoidAlgebra.coeff_mapAlgHom]
    exact h ⟨a, n, hn, rfl⟩

theorem limitIsUnique : Specs.CocharacterDynamics.LimitIsUnique.{u} := by
  intro k _ G hG cochar R g z z' h h'
  obtain ⟨f, hf, rfl⟩ := h
  obtain ⟨f', hf', rfl⟩ := h'
  rw [polynomialFamily_injective hG R (hf.trans hf'.symm)]

private instance : Group.FG Specs.DiagonalizableGroups.IntegerCharacters.{u} :=
  let e : Multiplicative ℤ ≃* Specs.DiagonalizableGroups.IntegerCharacters.{u} := MulEquiv.ulift.symm
  Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

theorem cocharacterCentralizerExists :
    Specs.CocharacterDynamics.CocharacterCentralizerExists.{u} := by
  intro k _ G cochar
  let := G.property.1
  let T := Specs.DiagonalizableGroups.diagonalGroup k Specs.DiagonalizableGroups.IntegerCharacters
  obtain ⟨X, i, hi, hx⟩ :=
    fixedPointScheme k T G.val.X (conjugationAction cochar) (IsSeparated.of_isAffineHom _)
      G.property.2.1 G.property.2.2
  let C (S : SchemeOver k) : Subgroup (S ⟶ G.val.X) :=
    { carrier := {p | Centralizes cochar p}
      one_mem' := (centralizes_iff cochar _).mpr fun _ t _ ↦ by
        rw [MonObj.comp_one]
        exact Commute.one_left _
      mul_mem' := fun {p q} hp hq ↦ (centralizes_iff cochar _).mpr fun U t h ↦ by
        rw [MonObj.comp_mul]
        exact ((centralizes_iff cochar p).mp hp U t h).mul_left
          ((centralizes_iff cochar q).mp hq U t h)
      inv_mem' := fun {p} hp ↦ (centralizes_iff cochar _).mpr fun U t h ↦ by
        rw [GrpObj.comp_inv]
        exact ((centralizes_iff cochar p).mp hp U t h).inv_left }
  refine closedSubgroupOfLocus C i hi fun S g ↦ ?_
  exact (isFixedBy_conjugation_iff cochar g).symm.trans (hx S g)

private abbrev gm (k : Type u) [Field k] : GroupScheme k :=
  specGroup (groupAlgebra k IntegerCharacters)

private def unitEquiv (R : TestAlgebra k) : GroupPoints (gm k) R ≃* Rˣ :=
  ((DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters).app R).groupIsoToMulEquiv.trans (integerHomEquiv Rˣ).symm

private theorem unitEquiv_unitPoint (R : TestAlgebra k) (s : Rˣ) :
    unitEquiv R (unitPoint R s) = s := by
  let a : IntegerCharacters →* Rˣ :=
    (DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters).hom.app R (unitPoint R s)
  change (integerHomEquiv Rˣ).symm a = s
  apply (integerHomEquiv Rˣ).injective
  rw [(integerHomEquiv Rˣ).apply_symm_apply a]
  apply MonoidHom.ext
  intro m
  apply Units.ext
  have h := pointsIso_spec IntegerCharacters R (unitCoordinates R s) m
  change ((show IntegerCharacters →* Rˣ from
    (DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters).hom.app R
      (unitPoint R s)) m).val = _ at h
  change ((show IntegerCharacters →* Rˣ from
    (DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters).hom.app R
      (unitPoint R s)) m).val = _
  rw [h]
  simp [unitCoordinates, MonoidAlgebra.lift_single, integerHomEquiv]

private def unitPointHom (R : TestAlgebra k) : Rˣ →* GroupPoints (gm k) R :=
  (unitEquiv R).symm.toMonoidHom

private theorem unitPointHom_apply (R : TestAlgebra k) (s : Rˣ) :
    unitPointHom R s = unitPoint R s :=
  (unitEquiv R).symm_apply_eq.mpr (unitEquiv_unitPoint R s).symm

private theorem cocharacterPoint_mul (cochar : Cocharacter G) (R : TestAlgebra k)
    (s t : Rˣ) :
    cocharacterPoint cochar R (s * t) =
      cocharacterPoint cochar R s * cocharacterPoint cochar R t := by
  simp only [cocharacterPoint, ← unitPointHom_apply]
  exact (((groupPointsFunctor k).map cochar).app R).hom.comp (unitPointHom R) |>.map_mul s t

private theorem centralizes_onAlgebras (cochar : Cocharacter G)
    {R : TestAlgebra k} (z : GroupPoints G R) :
    Centralizes cochar z ↔
      ∀ (S : TestAlgebra k) (a : R ⟶ S) (s : Sˣ),
        Commute (mapPoints a z : GroupPoints G S) (cocharacterPoint cochar S s) := by
  constructor
  · intro h S a s
    exact (centralizes_iff cochar z).mp h _ ((testSpec k).map a.op) (unitPoint S s)
  · intro h
    unfold Centralizes
    have ha : IsAffine ((gm k).X ⊗ (testSpec k).obj (op R)).left := by
      change IsAffine (pullback (gm k).X.hom ((testSpec k).obj (op R)).hom)
      have : IsAffine (gm k).X.left := inferInstanceAs
        (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters))))
      have : IsAffine ((testSpec k).obj (op R)).left := inferInstanceAs
        (IsAffine (Spec (CommRingCat.of R)))
      have : IsAffine (Spec (CommRingCat.of k)) := inferInstance
      infer_instance
    apply hom_ext_of_points ha
    intro S p
    let a := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (p ≫ snd (gm k).X ((testSpec k).obj (op R)))).unop
    let v : GroupPoints (gm k) S := p ≫ fst _ _
    have ha' : (testSpec k).map a.op = p ≫ snd _ _ :=
      (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
    obtain ⟨s, hs⟩ : ∃ s, unitPoint S s = v := ⟨unitEquiv S v, by
      rw [← unitPointHom_apply]; exact (unitEquiv S).symm_apply_apply v⟩
    have hc : ((testSpec k).map a.op ≫ z : Points G.X S) *
        (unitPoint S s ≫ cochar.hom.hom : Points G.X S) =
      (unitPoint S s ≫ cochar.hom.hom : Points G.X S) *
        ((testSpec k).map a.op ≫ z : Points G.X S) := (h S a s).eq
    rw [ha', hs] at hc
    simp only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv]
    apply mul_inv_eq_iff_eq_mul.mpr
    change (p ≫ snd (gm k).X ((testSpec k).obj (op R)) ≫ z : Points G.X S) *
        (p ≫ fst (gm k).X ((testSpec k).obj (op R)) ≫ cochar.hom.hom : Points G.X S) =
      (p ≫ fst (gm k).X ((testSpec k).obj (op R)) ≫ cochar.hom.hom : Points G.X S) *
        (p ≫ snd (gm k).X ((testSpec k).obj (op R)) ≫ z : Points G.X S)
    simpa only [v, Category.assoc] using hc

/-- Evaluation of the Laurent parameter at an invertible element. -/
private def evalLaurent {R S : TestAlgebra k} (a : R ⟶ S) (s : Sˣ) : laurentAlgebra R ⟶ S :=
  CommAlgCat.ofHom
    { LaurentPolynomial.eval₂ a.hom.toRingHom s with
      commutes' := fun c ↦ by
        change LaurentPolynomial.eval₂ a.hom.toRingHom s (LaurentPolynomial.C (algebraMap k R c)) = _
        rw [LaurentPolynomial.eval₂_C]
        exact a.hom.commutes c }

private theorem evalLaurent_constants {R S : TestAlgebra k} (a : R ⟶ S) (s : Sˣ) :
    laurentConstants R ≫ evalLaurent a s = a := by
  apply CommAlgCat.hom_ext
  ext x
  exact LaurentPolynomial.eval₂_C a.hom.toRingHom s x

private theorem evalLaurent_parameter {R S : TestAlgebra k} (a : R ⟶ S) (s : Sˣ) :
    Units.map (evalLaurent a s).hom.toMonoidHom (laurentParameter R) = s := by
  apply Units.ext
  change LaurentPolynomial.eval₂ a.hom.toRingHom s (LaurentPolynomial.T 1) = s.val
  rw [LaurentPolynomial.eval₂_T, zpow_one]

private theorem orbit_eval {R S : TestAlgebra k} (a : R ⟶ S) (s : Sˣ)
    (cochar : Cocharacter G) (g : GroupPoints G R) :
    mapPoints (evalLaurent a s) (orbit cochar g) =
      cocharacterPoint cochar S s * (show GroupPoints G S from mapPoints a g) *
        (cocharacterPoint cochar S s)⁻¹ := by
  let f := (((groupPointsFunctor k).obj G).map (evalLaurent a s)).hom
  let t := cocharacterPoint cochar (laurentAlgebra R) (laurentParameter R)
  let x : GroupPoints G (laurentAlgebra R) := mapPoints (laurentConstants R) g
  change f (t * x * t⁻¹) = _
  have ht : f t = cocharacterPoint cochar S s :=
    (mapPoints_cocharacterPoint (evalLaurent a s) cochar (laurentParameter R)).trans
      (congrArg (cocharacterPoint cochar S) (evalLaurent_parameter a s))
  have hx : f x = mapPoints a g := by
    change mapPoints (evalLaurent a s) (mapPoints (laurentConstants R) g) = _
    rw [← mapPoints_comp, evalLaurent_constants]
  rw [map_mul, map_mul, map_inv, ht, hx]

private def polynomialConstants (R : TestAlgebra k) : R ⟶ polynomialAlgebra R :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Polynomial R))

private theorem polynomialConstants_laurent (R : TestAlgebra k) :
    polynomialConstants R ≫ polynomialToLaurent R = laurentConstants R := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact Polynomial.toLaurent_C x

private theorem polynomialConstants_zero (R : TestAlgebra k) :
    polynomialConstants R ≫ polynomialEvaluate R 0 = 𝟙 R := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact Polynomial.eval₂_C (f := (AlgHom.id k R).toRingHom) (x := 0)

private theorem centralizes_hasLimit (cochar : Cocharacter G) {R : TestAlgebra k}
    {g : GroupPoints G R} (h : Centralizes cochar g) : HasLimit cochar g g := by
  have hc := (centralizes_onAlgebras cochar g).mp h (laurentAlgebra R)
    (laurentConstants R) (laurentParameter R)
  refine ⟨mapPoints (polynomialConstants R) g, ?_, ?_⟩
  · rw [← mapPoints_comp, polynomialConstants_laurent]
    exact (mul_inv_eq_iff_eq_mul.mpr hc.eq.symm).symm
  · rw [← mapPoints_comp, polynomialConstants_zero]
    simp [mapPoints]

private def scalePolynomial (R : TestAlgebra k) (s : Rˣ) :
    polynomialAlgebra R ⟶ polynomialAlgebra R :=
  CommAlgCat.ofHom
    ((Polynomial.aeval (Polynomial.C s.val * Polynomial.X)).restrictScalars k)

private def scaleLaurent (R : TestAlgebra k) (s : Rˣ) : laurentAlgebra R ⟶ laurentAlgebra R :=
  evalLaurent (laurentConstants R) (Units.map (laurentConstants R).hom.toMonoidHom s *
    laurentParameter R)

private theorem scale_polynomial_laurent (R : TestAlgebra k) (s : Rˣ) :
    scalePolynomial R s ≫ polynomialToLaurent R =
      polynomialToLaurent R ≫ scaleLaurent R s := by
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext'
  · apply AlgHom.ext
    intro r
    change Polynomial.toLaurent (Polynomial.aeval (Polynomial.C s.val * Polynomial.X)
      (Polynomial.C r)) = LaurentPolynomial.eval₂ LaurentPolynomial.C
      (Units.map (laurentConstants R).hom.toMonoidHom s * laurentParameter R)
        (Polynomial.toLaurent (Polynomial.C r))
    simp
  · change Polynomial.toLaurent (Polynomial.aeval (Polynomial.C s.val * Polynomial.X)
      Polynomial.X) = LaurentPolynomial.eval₂ LaurentPolynomial.C
      (Units.map (laurentConstants R).hom.toMonoidHom s * laurentParameter R)
        (Polynomial.toLaurent Polynomial.X)
    simp only [Polynomial.aeval_X, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      LaurentPolynomial.eval₂_T, zpow_one]
    rfl

private theorem scale_polynomial_zero (R : TestAlgebra k) (s : Rˣ) :
    scalePolynomial R s ≫ polynomialEvaluate R 0 = polynomialEvaluate R 0 := by
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext'
  · ext r
    change Polynomial.aevalTower (AlgHom.id k R) 0
        (Polynomial.aeval (Polynomial.C s.val * Polynomial.X) (Polynomial.C r)) =
      Polynomial.aevalTower (AlgHom.id k R) 0 (Polynomial.C r)
    simp
  · change Polynomial.aevalTower (AlgHom.id k R) 0
        (Polynomial.aeval (Polynomial.C s.val * Polynomial.X) Polynomial.X) =
      Polynomial.aevalTower (AlgHom.id k R) 0 Polynomial.X
    simp

/-- Replacing the parameter by s t preserves evaluation at zero. On the punctured
line this substitution conjugates the original family by the constant point λ(s). -/
private theorem limit_commutes_unit (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    {R : TestAlgebra k} {g z : GroupPoints G R} (h : HasLimit cochar g z) (s : Rˣ) :
    Commute z (cocharacterPoint cochar R s) := by
  obtain ⟨f, hf, hz⟩ := h
  let c := cocharacterPoint cochar R s
  let p : GroupPoints G (polynomialAlgebra R) := mapPoints (polynomialConstants R) c
  let l : GroupPoints G (laurentAlgebra R) := mapPoints (laurentConstants R) c
  have hp : mapPoints (polynomialToLaurent R) p = l := by
    rw [show p = mapPoints (polynomialConstants R) c from rfl, ← mapPoints_comp,
      polynomialConstants_laurent]
  have hp0 : mapPoints (polynomialEvaluate R 0) p = c := by
    rw [show p = mapPoints (polynomialConstants R) c from rfl, ← mapPoints_comp,
      polynomialConstants_zero]
    simp [mapPoints]
  have hscale : mapPoints (polynomialToLaurent R) (mapPoints (scalePolynomial R s) f) =
      mapPoints (polynomialToLaurent R) (p * f * p⁻¹) := by
    rw [← mapPoints_comp, scale_polynomial_laurent, mapPoints_comp, hf]
    change mapPoints (scaleLaurent R s) (orbit cochar g) =
      ((((groupPointsFunctor k).obj G).map (polynomialToLaurent R)).hom) (p * f * p⁻¹)
    rw [map_mul, map_mul, map_inv]
    change _ = (mapPoints (polynomialToLaurent R) p : GroupPoints G _) *
      mapPoints (polynomialToLaurent R) f * (mapPoints (polynomialToLaurent R) p : GroupPoints G _)⁻¹
    rw [hp, hf, scaleLaurent,
      orbit_eval (laurentConstants R) _ cochar g, cocharacterPoint_mul,
      ← mapPoints_cocharacterPoint (laurentConstants R) cochar s]
    let t := cocharacterPoint cochar (laurentAlgebra R) (laurentParameter R)
    let x : GroupPoints G (laurentAlgebra R) := mapPoints (laurentConstants R) g
    change (l * t) * x * (l * t)⁻¹ = l * (t * x * t⁻¹) * l⁻¹
    group
  have hpoly := polynomialFamily_injective ha R hscale
  have he := congrArg (mapPoints (X := G.X) (polynomialEvaluate R 0)) hpoly
  rw [← mapPoints_comp, scale_polynomial_zero, hz] at he
  change z = ((((groupPointsFunctor k).obj G).map (polynomialEvaluate R 0)).hom) (p * f * p⁻¹) at he
  rw [map_mul, map_mul, map_inv] at he
  change z = (mapPoints (polynomialEvaluate R 0) p : GroupPoints G _) *
    mapPoints (polynomialEvaluate R 0) f * (mapPoints (polynomialEvaluate R 0) p : GroupPoints G _)⁻¹ at he
  rw [hp0, hz] at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

private theorem limit_centralizes (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    {R : TestAlgebra k} {g z : GroupPoints G R} (h : HasLimit cochar g z) :
    Centralizes cochar z :=
  (centralizes_onAlgebras cochar z).mpr
    fun _ a s ↦ limit_commutes_unit ha cochar (h.map a) s

/-- The map on point groups induced by a group-scheme homomorphism. -/
private abbrev pointHom (f : G ⟶ H) (R : TestAlgebra k) :
    GroupPoints G R →* GroupPoints H R :=
  (((groupPointsFunctor k).map f).app R).hom

private theorem pointHom_injective (S : ClosedSubgroup G) (R : TestAlgebra k) :
    Function.Injective (pointHom S.inclusion R) := by
  let : Mono S.inclusion.hom.hom := mono_over _ S.isClosedImmersion
  intro p q h
  exact (cancel_mono S.inclusion.hom.hom).mp h

private theorem affine_subgroup (ha : IsAffine G.X.left) (S : ClosedSubgroup G) :
    IsAffine S.group.X.left := by
  let := S.isClosedImmersion
  exact isAffine_of_isAffineHom S.inclusion.hom.hom.left

private theorem liftPointGroupHom {J : GroupScheme k}
    (ha : IsAffine J.X.left) (C : ClosedSubgroup G)
    (α : (groupPointsFunctor k).obj J ⟶ (groupPointsFunctor k).obj G)
    (h : ∀ (R : TestAlgebra k) (p : GroupPoints J R), ∃ z : GroupPoints C.group R,
      pointHom C.inclusion R z = α.app R p) :
    ∃ f : J ⟶ C.group, (groupPointsFunctor k).map (f ≫ C.inclusion) = α := by
  classical
  let z (R : TestAlgebra k) (p : GroupPoints J R) := (h R p).choose
  have hz (R : TestAlgebra k) (p : GroupPoints J R) :
      pointHom C.inclusion R (z R p) = α.app R p := (h R p).choose_spec
  let β : (groupPointsFunctor k).obj J ⟶ (groupPointsFunctor k).obj C.group :=
    { app := fun R ↦ GrpCat.ofHom {
        toFun := z R
        map_one' := (pointHom_injective C R) (by rw [hz, map_one, map_one])
        map_mul' := fun p q ↦ (pointHom_injective C R) (by
          change pointHom C.inclusion R (z R ((show GroupPoints J R from p) * (show GroupPoints J R from q))) =
            pointHom C.inclusion R (z R p * z R q)
          rw [hz, (pointHom C.inclusion R).map_mul, hz, hz]
          exact (α.app R).hom.map_mul p q) }
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro p
        apply pointHom_injective C S
        change pointHom C.inclusion S (z S (mapPoints a p)) =
          (mapPoints a (z R p) : GroupPoints C.group S) ≫ C.inclusion.hom.hom
        rw [hz, mapPoints, Category.assoc]
        change α.app S (mapPoints a p) = mapPoints a (pointHom C.inclusion R (z R p))
        rw [hz]
        exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (α.naturality a)) p }
  obtain ⟨f, hf⟩ := (groupHomComparison k J C.group ha).2 β
  refine ⟨f, ?_⟩
  change (groupPointsFunctor k).map f = β at hf
  rw [Functor.map_comp, hf]
  ext R p
  exact hz R p

private theorem subgroupInclusionFactors {J : GroupScheme k} (ha : IsAffine J.X.left)
    (C : ClosedSubgroup G) (i : J ⟶ G)
    (h : ∀ (R : TestAlgebra k) (p : GroupPoints J R), ∃ z : GroupPoints C.group R,
      pointHom C.inclusion R z = pointHom i R p) :
    ∃ f : J ⟶ C.group, f ≫ C.inclusion = i := by
  obtain ⟨f, hf⟩ := liftPointGroupHom ha C ((groupPointsFunctor k).map i) h
  exact ⟨f, (groupHomComparison k J G ha).1 hf⟩

private def ambientLimit (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    (P : ClosedSubgroup G) (hP : RepresentsOnAlgebras P (fun _ g ↦ HasExtension cochar g)) :
    (groupPointsFunctor k).obj P.group ⟶ (groupPointsFunctor k).obj G := by
  classical
  let h (R : TestAlgebra k) (p : GroupPoints P.group R) :
      HasExtension cochar (pointHom P.inclusion R p) := (hP R _).2 ⟨p, rfl⟩
  let z (R : TestAlgebra k) (p : GroupPoints P.group R) := (h R p).choose
  have hz (R : TestAlgebra k) (p : GroupPoints P.group R) :
      HasLimit cochar (pointHom P.inclusion R p) (z R p) := (h R p).choose_spec
  letI := ha
  refine {
    app := fun R ↦ GrpCat.ofHom {
      toFun := z R
      map_one' := ?_
      map_mul' := ?_ }
    naturality := ?_ }
  · apply limitIsUnique cochar (hz R 1)
    simpa only [map_one] using hasLimit_one cochar R
  · intro p q
    apply limitIsUnique cochar (hz R (p * q))
    simpa only [map_mul] using (hz R p).mul (hz R q)
  · intro R S a
    apply GrpCat.ext
    intro p
    change z S (mapPoints a p) = mapPoints a (z R p)
    apply limitIsUnique cochar (hz S (mapPoints a p))
    have hh := (hz R p).map a
    change HasLimit cochar (((testSpec k).map a.op) ≫ (p ≫ P.inclusion.hom.hom)) _ at hh
    rw [← Category.assoc] at hh
    exact hh

private theorem ambientLimit_formula (ha : IsAffine G.X.left) (cochar : Cocharacter G)
    (P : ClosedSubgroup G) (hP : RepresentsOnAlgebras P (fun _ g ↦ HasExtension cochar g))
    (R : TestAlgebra k) (p : GroupPoints P.group R) :
    HasLimit cochar (pointHom P.inclusion R p) ((ambientLimit ha cochar P hP).app R p) :=
  ((hP R (pointHom P.inclusion R p)).2 ⟨p, rfl⟩).choose_spec

private theorem splitKernel_product {P C N : GroupScheme k} (s : C ⟶ P) (l : P ⟶ C)
    (n : N ⟶ P) (hs : s ≫ l = 𝟙 C)
    (hn : IsPullback n.hom.hom (toUnit _) l.hom.hom η[C.X])
    (hm : Mono n.hom.hom) : IsIso (multiplyFactors s n) := by
  let := hm
  let F := Grp.forget (SchemeOver k)
  let s' := s.hom.hom
  let l' := l.hom.hom
  let n' := n.hom.hom
  have hs' : s' ≫ l' = 𝟙 C.X := F.congr_map hs
  have hn' : n' ≫ l' = 1 := hn.w
  let q : P.X ⟶ P.X := (l' ≫ s')⁻¹ * 𝟙 P.X
  have hq : q ≫ l' = toUnit P.X ≫ η[C.X] := by
    change ((l' ≫ s')⁻¹ * 𝟙 P.X) ≫ l' = (1 : P.X ⟶ C.X)
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hs', Category.comp_id,
      Category.id_comp, inv_mul_cancel]
  let h := hn.lift q (toUnit _) hq
  have hh : h ≫ n' = q := hn.lift_fst _ _ _
  let m := multiplyFactors s n
  let inv := lift l' h
  have hi : inv ≫ m = 𝟙 P.X := by
    change lift l' h ≫ ((fst _ _ ≫ s') * (snd _ _ ≫ n')) = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hh]
    dsimp [q]
    group
  have hml : m ≫ l' = fst C.X N.X := by
    change ((fst _ _ ≫ s') * (snd _ _ ≫ n')) ≫ l' = _
    rw [MonObj.mul_comp, Category.assoc, hs', Category.comp_id, Category.assoc, hn',
      MonObj.comp_one, mul_one]
  have hj : m ≫ inv = 𝟙 (C.X ⊗ N.X) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [inv, Category.assoc, lift_fst, hml, Category.id_comp]
    · simp only [inv, Category.assoc, lift_snd, Category.id_comp]
      apply (cancel_mono n').mp
      rw [Category.assoc, hh]
      change m ≫ ((l' ≫ s')⁻¹ * 𝟙 P.X) = snd _ _ ≫ n'
      rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hml, Category.comp_id]
      change (fst _ _ ≫ s')⁻¹ * ((fst _ _ ≫ s') * (snd _ _ ≫ n')) = _
      group
  exact ⟨⟨inv, hj, hi⟩⟩

theorem existsLimitDecomposition : Specs.CocharacterDynamics.ExistsLimitDecomposition.{u} := by
  intro k _ G cochar
  obtain ⟨P, hP⟩ := parabolicSubgroupExists G cochar
  obtain ⟨C, hC⟩ := cocharacterCentralizerExists G cochar
  have ha := G.property.1
  let := ha
  let := affine_subgroup ha C
  let p := ambientLimit ha cochar P hP
  have hp := ambientLimit_formula ha cochar P hP
  obtain ⟨l, hl⟩ := liftPointGroupHom (affine_subgroup ha P) C p (fun R x ↦
    (hC _ _).mp (limit_centralizes ha cochar (hp R x)))
  have hlP (R : TestAlgebra k) (x : GroupPoints P.group R) :
      HasLimit cochar (pointHom P.inclusion R x) (pointHom (l ≫ C.inclusion) R x) := by
    change HasLimit cochar _ ((((groupPointsFunctor k).map (l ≫ C.inclusion)).app R) x)
    rw [hl]
    exact hp R x
  obtain ⟨s, hs⟩ := subgroupInclusionFactors (affine_subgroup ha C) P C.inclusion
    (fun R x ↦ (hP R _).mp ⟨_, centralizes_hasLimit cochar ((hC _ _).mpr ⟨x, rfl⟩)⟩)
  have hsl : s ≫ l = 𝟙 _ := by
    apply (groupHomComparison k C.group C.group (affine_subgroup ha C)).1
    ext R x
    change pointHom (s ≫ l) R x = x
    apply pointHom_injective C R
    change pointHom (s ≫ l ≫ C.inclusion) R x = pointHom C.inclusion R x
    have hh := hlP R (pointHom s R x)
    change HasLimit cochar (pointHom (s ≫ P.inclusion) R x)
      (pointHom (s ≫ l ≫ C.inclusion) R x) at hh
    rw [hs] at hh
    exact limitIsUnique cochar hh (centralizes_hasLimit cochar ((hC _ _).mpr ⟨x, rfl⟩))
  obtain ⟨N, hN⟩ := schemeKernel_exists l
  let := N.isClosedImmersion
  let := P.isClosedImmersion
  let U : ClosedSubgroup G.val :=
    ⟨N.group, N.inclusion ≫ P.inclusion, IsClosedImmersion.comp
      N.inclusion.hom.hom.left P.inclusion.hom.hom.left⟩
  have hU : RepresentsOnAlgebras U (fun _ g ↦ HasLimit cochar g 1) := by
    intro R g
    constructor
    · intro hg
      obtain ⟨x, hx⟩ := (hP R g).mp ⟨1, hg⟩
      have he := hlP R x
      rw [hx] at he
      have hz : pointHom (l ≫ C.inclusion) R x = 1 := limitIsUnique cochar he hg
      have hx1 : pointHom l R x = 1 := by
        apply pointHom_injective C R
        rw [map_one]
        exact hz
      obtain ⟨y, hy⟩ := (schemeKernel_sections hN x).mpr hx1
      change pointHom N.inclusion R y = x at hy
      change pointHom P.inclusion R x = g at hx
      exact ⟨y, by
        change pointHom P.inclusion R (pointHom N.inclusion R y) = g
        rw [hy, hx]⟩
    · rintro ⟨y, rfl⟩
      have hy : pointHom l R (pointHom N.inclusion R y) = 1 :=
        (schemeKernel_sections hN _).mp ⟨y, rfl⟩
      have hh := hlP R (pointHom N.inclusion R y)
      change HasLimit cochar (pointHom U.inclusion R y)
        (pointHom C.inclusion R (pointHom l R (pointHom N.inclusion R y))) at hh
      rwa [hy, map_one] at hh
  exact ⟨⟨P, U, C, hP, hU, hC, N.inclusion, rfl, s, hs, l, hlP, hsl, hN,
    splitKernel_product s l N.inclusion hsl hN (mono_over _ N.isClosedImmersion)⟩⟩

private theorem unitPoint_inv (R : TestAlgebra k) (s : Rˣ) :
    unitPoint R s⁻¹ = (unitPoint R s)⁻¹ := by
  simp only [← unitPointHom_apply, map_inv]

private theorem opposite_point (cochar : Cocharacter G) (R : TestAlgebra k) (s : Rˣ) :
    cocharacterPoint (oppositeCocharacter cochar) R s = cocharacterPoint cochar R s⁻¹ := by
  let A := DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters
  let i := specGroupMap (groupAlgebraMap k (invMonoidHom (α := IntegerCharacters.{u})))
  have hi : pointHom i R (unitPoint R s) = unitPoint R s⁻¹ := by
    apply (A.app R).groupIsoToMulEquiv.injective
    change A.hom.app R (pointHom i R (unitPoint R s)) = A.hom.app R (unitPoint R s⁻¹)
    rw [unitPoint_inv]
    apply MonoidHom.ext
    intro m
    let a (x : GroupPoints (gm k) R) : IntegerCharacters →* Rˣ := A.hom.app R x
    change a (pointHom i R (unitPoint R s)) m = a ((unitPoint R s)⁻¹) m
    have h := pointsIso_precompose (invMonoidHom (α := IntegerCharacters.{u})) R (unitPoint R s) m
    change a (pointHom i R (unitPoint R s)) m = a (unitPoint R s) (m⁻¹) at h
    have hinv : a ((unitPoint R s)⁻¹) = (a (unitPoint R s))⁻¹ :=
      (A.hom.app R).hom.map_inv (unitPoint R s)
    rw [h, hinv, map_inv]
    rfl
  change pointHom (i ≫ cochar) R (unitPoint R s) = pointHom cochar R (unitPoint R s⁻¹)
  rw [show pointHom (i ≫ cochar) R (unitPoint R s) =
    pointHom cochar R (pointHom i R (unitPoint R s)) from
      (Category.assoc (unitPoint R s) i.hom.hom cochar.hom.hom).symm, hi]

private def invertLaurent (R : TestAlgebra k) : laurentAlgebra R ⟶ laurentAlgebra R :=
  CommAlgCat.ofHom (LaurentPolynomial.invert.toAlgHom.restrictScalars k)

private theorem invertLaurent_constants (R : TestAlgebra k) :
    laurentConstants R ≫ invertLaurent R = laurentConstants R := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro r
  exact LaurentPolynomial.invert_C r

private theorem invertLaurent_parameter (R : TestAlgebra k) :
    Units.map (invertLaurent R).hom.toMonoidHom (laurentParameter R) = (laurentParameter R)⁻¹ := by
  apply Units.ext
  change LaurentPolynomial.invert (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial R) =
    LaurentPolynomial.T (-1)
  rw [LaurentPolynomial.invert_T]

private theorem invertLaurent_involutive (R : TestAlgebra k) :
    invertLaurent R ≫ invertLaurent R = 𝟙 _ := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro r
  exact LaurentPolynomial.involutive_invert r

private theorem orbit_opposite (cochar : Cocharacter G) {R : TestAlgebra k} (g : GroupPoints G R) :
    orbit (oppositeCocharacter cochar) g = mapPoints (invertLaurent R) (orbit cochar g) := by
  let f := (((groupPointsFunctor k).obj G).map (invertLaurent R)).hom
  change _ = f (_ * _ * _)
  rw [map_mul, map_mul, map_inv]
  change _ = (mapPoints (invertLaurent R) (cocharacterPoint cochar _ _) : GroupPoints G _) *
    (mapPoints (invertLaurent R) (mapPoints (laurentConstants R) g) : GroupPoints G _) *
    (mapPoints (invertLaurent R) (cocharacterPoint cochar _ _) : GroupPoints G _)⁻¹
  rw [mapPoints_cocharacterPoint, invertLaurent_parameter, ← mapPoints_comp,
    invertLaurent_constants]
  simp only [orbit, opposite_point]

private theorem polynomial_constant_of_reverse {R : Type u} [CommRing R] (p q : Polynomial R)
    (h : q.toLaurent = LaurentPolynomial.invert p.toLaurent) : p = Polynomial.C (p.coeff 0) := by
  have hp := constant_of_regular_and_inverse ⟨p, rfl⟩ ⟨q, h⟩
  apply Polynomial.toLaurent_injective
  rw [Polynomial.toLaurent_C, ← coeff_toLaurent_nat p 0]
  exact hp

/-- Regularity in both parameters forces the family to equal its constant term. -/
private theorem polynomial_family_constant_of_reverse (ha : IsAffine G.X.left)
    {R : TestAlgebra k} (f y : GroupPoints G (polynomialAlgebra R))
    (h : mapPoints (polynomialToLaurent R) y =
      mapPoints (invertLaurent R) (mapPoints (polynomialToLaurent R) f)) :
    f = mapPoints (polynomialConstants R) (mapPoints (polynomialEvaluate R 0) f) := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let p := (F.preimage (f ≫ e.inv)).unop
  let q := (F.preimage (y ≫ e.inv)).unop
  have hp : (testSpec k).map p.op = f ≫ e.inv := F.map_preimage _
  have hq : (testSpec k).map q.op = y ≫ e.inv := F.map_preimage _
  have he : q ≫ polynomialToLaurent R =
      p ≫ polynomialToLaurent R ≫ invertLaurent R := by
    apply Quiver.Hom.op_inj
    apply F.map_injective
    simp only [op_comp, Functor.map_comp, hp, hq, Category.assoc]
    simpa only [mapPoints, Category.assoc] using congrArg (· ≫ e.inv) h
  have eq : p = p ≫ polynomialEvaluate R 0 ≫ polynomialConstants R := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    have hcoeff := DFunLike.congr_fun (congrArg (fun r ↦ r.hom) he) a
    change (q.hom a).toLaurent = LaurentPolynomial.invert (p.hom a).toLaurent at hcoeff
    change p.hom a = Polynomial.C ((Polynomial.aevalTower (AlgHom.id k R) 0) (p.hom a))
    change p.hom a = Polynomial.C ((p.hom a).eval₂ (RingHom.id R) 0)
    rw [Polynomial.eval₂_at_zero, RingHom.id_apply]
    exact polynomial_constant_of_reverse _ _ hcoeff
  apply (cancel_mono e.inv).mp
  have hh := congrArg (fun a ↦ (testSpec k).map a.op) eq
  simp only [op_comp, Functor.map_comp, hp, Category.assoc] at hh
  exact hh

theorem oppositeLimit_intersection_onPoints {R : TestAlgebra k} (ha : IsAffine G.X.left)
    (cochar : Cocharacter G) (g : GroupPoints G R)
    (hp : HasExtension cochar g) (hu : HasLimit (oppositeCocharacter cochar) g 1) :
    g = 1 := by
  obtain ⟨_, f, hf, _⟩ := hp
  obtain ⟨y, hy, hy0⟩ := hu
  have he : mapPoints (polynomialToLaurent R) f =
      mapPoints (invertLaurent R) (mapPoints (polynomialToLaurent R) y) := by
    rw [hy, orbit_opposite, ← mapPoints_comp, invertLaurent_involutive, hf]
    simp [mapPoints]
  have h := polynomial_family_constant_of_reverse ha y f he
  have hy1 : y = 1 := by
    rw [h, hy0]
    exact map_one (((groupPointsFunctor k).obj G).map (polynomialConstants R)).hom
  have ho : orbit (oppositeCocharacter cochar) g = 1 := by
    rw [← hy, hy1]
    exact map_one (((groupPointsFunctor k).obj G).map (polynomialToLaurent R)).hom
  let a := evalLaurent (𝟙 R) (1 : Rˣ)
  have h := congrArg (mapPoints (X := G.X) a) ho
  rw [orbit_eval] at h
  change _ = ((((groupPointsFunctor k).obj G).map a).hom) 1 at h
  rw [map_one] at h
  have hid : mapPoints (X := G.X) (𝟙 R) g = g := by simp [mapPoints]
  rw [hid] at h
  let c := cocharacterPoint (oppositeCocharacter cochar) R (1 : Rˣ)
  have hh : c * g = c := by
    change c * g * c⁻¹ = (1 : GroupPoints G R) at h
    simpa only [one_mul] using mul_inv_eq_iff_eq_mul.mp h
  exact mul_left_cancel (hh.trans (mul_one c).symm)

private theorem oppositeIntersection_onPoints {R : TestAlgebra k}
    (ha : IsAffine G.X.left) {cochar : Cocharacter G}
    (D : LimitDecomposition cochar) (E : LimitDecomposition (oppositeCocharacter cochar))
    (x : GroupPoints E.contracting.group R) (y : GroupPoints D.parabolic.group R)
    (h : pointHom E.contracting.inclusion R x = pointHom D.parabolic.inclusion R y) :
    pointHom E.contracting.inclusion R x = 1 := by
  apply oppositeLimit_intersection_onPoints ha cochar
  · rw [h]
    exact (D.parabolic_points R _).2 ⟨y, rfl⟩
  · exact (E.contracting_points R _).2 ⟨x, rfl⟩

set_option maxHeartbeats 600000 in
theorem oppositeLimitIntersection : Specs.CocharacterDynamics.OppositeLimitIntersection.{u} := by
  intro k _ G cochar D E
  let := G.property.1
  let i := E.contracting.inclusion.hom.hom
  let j := D.parabolic.inclusion.hom.hom
  let : Mono i := mono_over _ E.contracting.isClosedImmersion
  let : Mono j := mono_over _ D.parabolic.isClosedImmersion
  have hη : IsClosedImmersion (η[G.val.X]).left := by
    have : IsAffine (𝟙_ (SchemeOver k)).left := inferInstanceAs
      (IsAffine (Spec (CommRingCat.of k)))
    apply IsClosedImmersion.of_surjective_of_isAffine
    have hw : (η[G.val.X]).left ≫ G.val.X.hom = 𝟙 _ := (η[G.val.X]).w
    have happ := congrArg Scheme.Hom.appTop hw
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at happ
    exact Function.RightInverse.surjective (fun x ↦ ConcreteCategory.congr_hom happ x)
  have hc (c : PullbackCone i j) : c.fst ≫ i = 1 := by
    obtain ⟨f, hf⟩ := (factorsThroughClosed_iff η[G.val.X] hη (c.fst ≫ i)).mpr
      fun R a ↦ ⟨toUnit _, by
        change (1 : GroupPoints G.val R) = a ≫ c.fst ≫ i
        exact (oppositeIntersection_onPoints G.property.1 D E (a ≫ c.fst) (a ≫ c.snd)
          (by
            change (a ≫ c.fst) ≫ i = (a ≫ c.snd) ≫ j
            simpa only [Category.assoc] using congrArg (a ≫ ·) c.condition)).symm⟩
    exact hf.symm.trans (congrArg (· ≫ η[G.val.X]) (toUnit_unique f (toUnit _)))
  change IsPullback _ _ i j
  have hw : η[E.contracting.group.X] ≫ i = η[D.parabolic.group.X] ≫ j :=
    (IsMonHom.one_hom i).trans (IsMonHom.one_hom j).symm
  exact ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ toUnit c.pt) (by
    intro c
    apply (cancel_mono i).mp
    change (1 : c.pt ⟶ E.contracting.group.X) ≫ i = c.fst ≫ i
    rw [MonObj.one_comp, hc]) (by
    intro c
    apply (cancel_mono j).mp
    change (1 : c.pt ⟶ D.parabolic.group.X) ≫ j = c.snd ≫ j
    rw [MonObj.one_comp, ← c.condition, hc]) (by
    intro c f _ _
    exact toUnit_unique _ _)⟩⟩

section BaseChange

variable {K : Type u} [Field K] [Algebra k K]

private abbrev restricted (R : TestAlgebra K) : TestAlgebra k :=
  (restrictTestAlgebra k K).obj R

private abbrev changedPoints (J : GroupScheme k) (R : TestAlgebra K) :=
  GroupPoints ((groupBaseChange k K).obj J) R

private abbrev bpoint (J : GroupScheme k) (R : TestAlgebra K) :
    changedPoints J R ≃* GroupPoints J (restricted (k := k) R) :=
  baseChangePointGroupEquiv K J R

private theorem bpoint_natural {J : GroupScheme k} {R S : TestAlgebra K} (a : R ⟶ S)
    (p : changedPoints J R) :
    bpoint J S (mapPoints a p) = mapPoints ((restrictTestAlgebra k K).map a) (bpoint J R p) :=
  baseChangePointsNaturality k K J.X a p

private theorem bpoint_morphism {J L : GroupScheme k} {R : TestAlgebra K} (f : J ⟶ L)
    (p : changedPoints J R) :
    bpoint L R (pointHom ((groupBaseChange k K).map f) R p) =
      pointHom f (restricted R) (bpoint J R p) :=
  baseChangePointsSchemeNaturality k K f.hom.hom R p

/-- The standard multiplicative groups over the two fields use the same unit
after identifying the base-changed test points by the projection. -/
private theorem gm_baseChange (k K : Type u) [Field k] [Field K] [Algebra k K] :
    ∃ e : gm K ≅ (groupBaseChange k K).obj (gm k),
      ∀ (R : TestAlgebra K) (s : Rˣ),
        bpoint (gm k) R (pointHom e.hom R (unitPoint R s)) = unitPoint (restricted R) s := by
  let E (R : TestAlgebra K) : GroupPoints (gm K) R ≃* changedPoints (gm k) R :=
    (unitEquiv R).trans <|
      (unitEquiv (restricted R)).symm.trans (bpoint (gm k) R).symm
  have hE (R : TestAlgebra K) (s : Rˣ) :
      bpoint (gm k) R (E R (unitPoint R s)) = unitPoint (restricted R) s := by
    change bpoint (gm k) R ((bpoint (gm k) R).symm
      ((unitEquiv (restricted R)).symm (unitEquiv R (unitPoint R s)))) = _
    rw [(bpoint (gm k) R).apply_symm_apply, unitEquiv_unitPoint]
    exact unitPointHom_apply (restricted R) s
  let N : (groupPointsFunctor K).obj (gm K) ≅
      (groupPointsFunctor K).obj ((groupBaseChange k K).obj (gm k)) :=
    NatIso.ofComponents (fun R ↦ (E R).toGrpIso) (by
      intro R S a
      apply GrpCat.ext
      intro p
      let s := unitEquiv R p
      have hp : unitPoint R s = p :=
        (unitPointHom_apply R s).symm.trans ((unitEquiv R).symm_apply_apply p)
      change E S (mapPoints a p) = mapPoints a (E R p)
      rw [← hp, mapPoints_unitPoint]
      apply (bpoint (gm k) S).injective
      rw [hE, bpoint_natural, hE, mapPoints_unitPoint]
      rfl)
  have aff (F : Type u) [Field F] : IsAffine (gm F).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra F IntegerCharacters))))
  have hb : IsAffine ((groupBaseChange k K).obj (gm k)).X.left := by
    change IsAffine (pullback (gm k).X.hom (fieldSpecMap k K))
    have : IsAffine (gm k).X.left := aff k
    have : IsAffine (Spec (CommRingCat.of k)) := inferInstance
    have : IsAffine (Spec (CommRingCat.of K)) := inferInstance
    infer_instance
  obtain ⟨f, hf⟩ := (groupHomComparison K _ _ (aff K)).2 N.hom
  obtain ⟨g, hg⟩ := (groupHomComparison K _ _ hb).2 N.inv
  change (groupPointsFunctor K).map f = N.hom at hf
  change (groupPointsFunctor K).map g = N.inv at hg
  refine ⟨⟨f, g, ?_, ?_⟩, ?_⟩
  · apply (groupHomComparison K _ _ (aff K)).1
    change (groupPointsFunctor K).map (f ≫ g) = (groupPointsFunctor K).map (𝟙 _)
    rw [Functor.map_comp, hf, hg, N.hom_inv_id]
    exact ((groupPointsFunctor K).map_id _).symm
  · apply (groupHomComparison K _ _ hb).1
    change (groupPointsFunctor K).map (g ≫ f) = (groupPointsFunctor K).map (𝟙 _)
    rw [Functor.map_comp, hf, hg, N.inv_hom_id]
    exact ((groupPointsFunctor K).map_id _).symm
  · intro R s
    have hf' : pointHom f R (unitPoint R s) = E R (unitPoint R s) :=
      DFunLike.congr_fun (congrArg (fun τ ↦ (τ.app R).hom) hf) (unitPoint R s)
    rw [hf', hE]

private def algebraIsoOfRingIso (A B : TestAlgebra k) (e : A ≃+* B)
    (h : ∀ x, e (algebraMap k A x) = algebraMap k B x) : A ≅ B := by
  let f : A ≃ₐ[k] B := AlgEquiv.ofRingEquiv h
  exact ⟨ConcreteCategory.ofHom (C := CommAlgCat k) f.toAlgHom,
    ConcreteCategory.ofHom (C := CommAlgCat k) f.symm.toAlgHom,
    CommAlgCat.hom_ext (DFunLike.ext _ _ f.symm_apply_apply),
    CommAlgCat.hom_ext (DFunLike.ext _ _ f.apply_symm_apply)⟩

private def restrictPolynomial (R : TestAlgebra K) :
    restricted (k := k) (polynomialAlgebra R) ≅ polynomialAlgebra (restricted (k := k) R) :=
  algebraIsoOfRingIso _ _ (RingEquiv.refl (Polynomial R)) fun _ ↦ rfl

private def restrictLaurent (R : TestAlgebra K) :
    restricted (k := k) (laurentAlgebra R) ≅ laurentAlgebra (restricted (k := k) R) :=
  algebraIsoOfRingIso _ _ (RingEquiv.refl (LaurentPolynomial R)) fun _ ↦ rfl

private theorem restrict_polynomial_laurent (R : TestAlgebra K) :
    (restrictPolynomial (k := k) R).hom ≫ polynomialToLaurent (restricted R) =
      (restrictTestAlgebra k K).map (polynomialToLaurent R) ≫ (restrictLaurent R).hom := by
  apply CommAlgCat.hom_ext
  exact DFunLike.ext _ _ fun _ ↦ rfl

private theorem restrict_polynomial_zero (R : TestAlgebra K) :
    (restrictPolynomial (k := k) R).hom ≫ polynomialEvaluate (restricted R) 0 =
      (restrictTestAlgebra k K).map (polynomialEvaluate R 0) := by
  apply CommAlgCat.hom_ext
  exact DFunLike.ext _ _ fun _ ↦ rfl

private theorem restrict_laurent_constants (R : TestAlgebra K) :
    (restrictTestAlgebra k K).map (laurentConstants R) ≫ (restrictLaurent R).hom =
      laurentConstants (restricted (k := k) R) := by
  apply CommAlgCat.hom_ext
  exact DFunLike.ext _ _ fun _ ↦ rfl

private theorem restrict_laurent_parameter (R : TestAlgebra K) :
    Units.map (restrictLaurent (k := k) R).hom.hom.toMonoidHom
        (laurentParameter R) =
      laurentParameter (restricted (k := k) R) := by
  apply Units.ext
  rfl

private def polynomialPointCompare (R : TestAlgebra K) :
    changedPoints G (polynomialAlgebra R) ≃*
      GroupPoints G (polynomialAlgebra (restricted (k := k) R)) :=
  (bpoint G (polynomialAlgebra R)).trans
    ((((groupPointsFunctor k).obj G).mapIso (restrictPolynomial R)).groupIsoToMulEquiv)

private def laurentPointCompare (R : TestAlgebra K) :
    changedPoints G (laurentAlgebra R) ≃*
      GroupPoints G (laurentAlgebra (restricted (k := k) R)) :=
  (bpoint G (laurentAlgebra R)).trans
    ((((groupPointsFunctor k).obj G).mapIso (restrictLaurent R)).groupIsoToMulEquiv)

private theorem polynomialPointCompare_laurent (R : TestAlgebra K)
    (f : changedPoints G (polynomialAlgebra R)) :
    laurentPointCompare R (mapPoints (polynomialToLaurent R) f) =
      mapPoints (polynomialToLaurent (restricted R)) (polynomialPointCompare R f) := by
  change mapPoints (restrictLaurent R).hom
    (bpoint G (laurentAlgebra R) (mapPoints (polynomialToLaurent R) f)) =
    mapPoints (polynomialToLaurent (restricted R))
      (mapPoints (restrictPolynomial R).hom (bpoint G (polynomialAlgebra R) f))
  rw [bpoint_natural, ← mapPoints_comp, ← mapPoints_comp, restrict_polynomial_laurent]

private theorem polynomialPointCompare_zero (R : TestAlgebra K)
    (f : changedPoints G (polynomialAlgebra R)) :
    bpoint G R (mapPoints (polynomialEvaluate R 0) f) =
      mapPoints (polynomialEvaluate (restricted R) 0) (polynomialPointCompare R f) := by
  change bpoint G R (mapPoints (polynomialEvaluate R 0) f) =
    mapPoints (polynomialEvaluate (restricted R) 0)
      (mapPoints (restrictPolynomial R).hom (bpoint G (polynomialAlgebra R) f))
  rw [bpoint_natural, ← mapPoints_comp, restrict_polynomial_zero]

private theorem laurentPointCompare_constants (R : TestAlgebra K) (g : changedPoints G R) :
    laurentPointCompare R (mapPoints (laurentConstants R) g) =
      mapPoints (laurentConstants (restricted R)) (bpoint G R g) := by
  change mapPoints (restrictLaurent R).hom (bpoint G (laurentAlgebra R)
    (mapPoints (laurentConstants R) g)) = _
  rw [bpoint_natural, ← mapPoints_comp, restrict_laurent_constants]

private theorem laurentPointCompare_cocharacter (cochar : Cocharacter G)
    (e : gm K ≅ (groupBaseChange k K).obj (gm k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      bpoint (gm k) R (pointHom e.hom R (unitPoint R s)) = unitPoint (restricted R) s)
    (R : TestAlgebra K) :
    laurentPointCompare R (cocharacterPoint (e.hom ≫ (groupBaseChange k K).map cochar)
      (laurentAlgebra R) (laurentParameter R)) =
      cocharacterPoint cochar (laurentAlgebra (restricted R)) (laurentParameter (restricted R)) := by
  let S := laurentAlgebra R
  let s := laurentParameter R
  change mapPoints (restrictLaurent R).hom
    (bpoint G S (pointHom (e.hom ≫ (groupBaseChange k K).map cochar) S (unitPoint S s))) = _
  have hcomp : pointHom (e.hom ≫ (groupBaseChange k K).map cochar) S (unitPoint S s) =
      pointHom ((groupBaseChange k K).map cochar) S (pointHom e.hom S (unitPoint S s)) := by
    exact (Category.assoc (unitPoint S s) e.hom.hom.hom
      ((groupBaseChange k K).map cochar).hom.hom).symm
  rw [hcomp, bpoint_morphism, he]
  change mapPoints (restrictLaurent R).hom (cocharacterPoint cochar (restricted S) s) = _
  rw [mapPoints_cocharacterPoint, restrict_laurent_parameter]

private theorem laurentPointCompare_orbit (cochar : Cocharacter G)
    (e : gm K ≅ (groupBaseChange k K).obj (gm k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      bpoint (gm k) R (pointHom e.hom R (unitPoint R s)) = unitPoint (restricted R) s)
    (R : TestAlgebra K) (g : changedPoints G R) :
    laurentPointCompare R (orbit (e.hom ≫ (groupBaseChange k K).map cochar) g) =
      orbit cochar (bpoint G R g) := by
  let t := cocharacterPoint (e.hom ≫ (groupBaseChange k K).map cochar)
    (laurentAlgebra R) (laurentParameter R)
  let x : changedPoints G (laurentAlgebra R) := mapPoints (laurentConstants R) g
  change laurentPointCompare R (t * x * t⁻¹) = _
  rw [map_mul, map_mul, map_inv, laurentPointCompare_cocharacter cochar e he R]
  have hx : laurentPointCompare R x = mapPoints (laurentConstants (restricted R)) (bpoint G R g) :=
    laurentPointCompare_constants R g
  rw [hx]
  rfl

/-- Projection along scalar extension identifies the polynomial extensions
and their values at zero. -/
private theorem baseChange_hasLimit_iff (cochar : Cocharacter G)
    (e : gm K ≅ (groupBaseChange k K).obj (gm k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      bpoint (gm k) R (pointHom e.hom R (unitPoint R s)) = unitPoint (restricted R) s)
    (R : TestAlgebra K) (g z : changedPoints G R) :
    HasLimit (e.hom ≫ (groupBaseChange k K).map cochar) g z ↔
      HasLimit cochar (bpoint G R g) (bpoint G R z) := by
  constructor
  · rintro ⟨f, hf, hz⟩
    refine ⟨polynomialPointCompare R f, ?_, ?_⟩
    · rw [← polynomialPointCompare_laurent, hf, laurentPointCompare_orbit cochar e he R]
    · rw [← polynomialPointCompare_zero, hz]
  · rintro ⟨f, hf, hz⟩
    obtain ⟨f', rfl⟩ := (polynomialPointCompare R).surjective f
    refine ⟨f', (laurentPointCompare R).injective ?_, (bpoint G R).injective ?_⟩
    · rw [polynomialPointCompare_laurent, hf, laurentPointCompare_orbit cochar e he R]
    · rw [polynomialPointCompare_zero, hz]

private theorem baseChange_hasExtension_iff (cochar : Cocharacter G)
    (e : gm K ≅ (groupBaseChange k K).obj (gm k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      bpoint (gm k) R (pointHom e.hom R (unitPoint R s)) = unitPoint (restricted R) s)
    (R : TestAlgebra K) (g : changedPoints G R) :
    HasExtension (e.hom ≫ (groupBaseChange k K).map cochar) g ↔
      HasExtension cochar (bpoint G R g) := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨bpoint G R z, (baseChange_hasLimit_iff cochar e he R g z).mp hz⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := (bpoint G R).surjective z
    exact ⟨w, (baseChange_hasLimit_iff cochar e he R g w).mpr hz⟩

private theorem baseChange_image_iff (S : ClosedSubgroup G)
    (R : TestAlgebra K) (g : changedPoints G R) :
    (∃ s : changedPoints S.group R, pointHom ((groupBaseChange k K).map S.inclusion) R s = g) ↔
      ∃ s : GroupPoints S.group (restricted (k := k) R),
        pointHom S.inclusion (restricted R) s = bpoint G R g := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨bpoint S.group R s, (bpoint_morphism S.inclusion s).symm⟩
  · rintro ⟨s, hs⟩
    obtain ⟨s', rfl⟩ := (bpoint S.group R).surjective s
    refine ⟨s', (bpoint G R).injective ?_⟩
    rw [bpoint_morphism, hs]

private theorem centralizes_precomposeIso {J L N : GroupScheme k}
    (e : J ≅ L) (i : L ⟶ N) {T : SchemeOver k} (p : T ⟶ N.X) :
    Centralizes (e.hom ≫ i) p ↔ Centralizes i p := by
  let F := Grp.forget (SchemeOver k)
  constructor
  · intro h
    refine (centralizes_iff i p).mpr fun U t x ↦ ?_
    have hh := (centralizes_iff (e.hom ≫ i) p).mp h U t (x ≫ e.inv.hom.hom)
    change Commute (t ≫ p) ((x ≫ F.map e.inv) ≫ (F.map e.hom ≫ F.map i)) at hh
    rw [Category.assoc, ← Category.assoc (F.map e.inv), ← Functor.map_comp,
      e.inv_hom_id, F.map_id L, Category.id_comp] at hh
    exact hh
  · intro h
    refine (centralizes_iff (e.hom ≫ i) p).mpr fun U t x ↦ ?_
    change Commute (t ≫ p) (x ≫ e.hom.hom.hom ≫ i.hom.hom)
    rw [← Category.assoc]
    exact (centralizes_iff i p).mp h U t (x ≫ e.hom.hom.hom)

theorem limitSubgroupsBaseChange : Specs.CocharacterDynamics.LimitSubgroupsBaseChange.{u} := by
  intro k K _ _ _ G cochar D
  obtain ⟨e, he⟩ := gm_baseChange k K
  refine ⟨e, he, ?_⟩
  obtain ⟨hz, hZ⟩ := centralizerSchemeBaseChange k K cochar D.centralizer D.centralizer_points
  refine ⟨baseChangeClosedSubgroup k K D.parabolic.inclusion D.parabolic.isClosedImmersion,
    baseChangeClosedSubgroup k K D.contracting.inclusion D.contracting.isClosedImmersion, hz,
    ?_, ?_, ?_, ?_⟩
  · intro R g
    exact (baseChange_hasExtension_iff cochar e he R g).trans
      ((D.parabolic_points _ _).trans (baseChange_image_iff D.parabolic R g).symm)
  · intro R g
    refine (baseChange_hasLimit_iff cochar e he R g 1).trans ?_
    rw [map_one]
    exact (D.contracting_points _ _).trans (baseChange_image_iff D.contracting R g).symm
  · intro T g
    exact (centralizes_precomposeIso e _ g).trans (hZ T g)
  · intro R p
    apply (baseChange_hasLimit_iff cochar e he R _ _).mpr
    change HasLimit cochar
      (bpoint G.val R (pointHom ((groupBaseChange k K).map D.parabolic.inclusion) R p))
      (bpoint G.val R
        (pointHom ((groupBaseChange k K).map (D.limit ≫ D.centralizer.inclusion)) R p))
    rw [bpoint_morphism, bpoint_morphism]
    exact D.limit_points _ _

end BaseChange
end
end LinearAlgebraicGroups.CocharacterDynamics
