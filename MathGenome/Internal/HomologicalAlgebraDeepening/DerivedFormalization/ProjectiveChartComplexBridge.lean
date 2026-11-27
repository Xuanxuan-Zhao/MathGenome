import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveChartComplexBridge
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveTwists
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.LaurentCechCohomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.Data.Finset.Sort
import Batteries.Tactic.OpenPrivate

set_option Elab.async false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open HomogeneousLocalization HomologicalComplex
open AdvancedHomologicalAlgebra.Cech
open DerivedFormalization.ProjectiveTwists
open DerivedFormalization.LaurentCechCohomology
open Specs.DerivedFormalization.ProjectiveCechComparison
open Specs.DerivedFormalization.OrderedCechComparison

namespace DerivedFormalization.ProjectiveChartComplexBridge

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open private basicStructureEquiv basicStructureEquiv_value
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveTwists

open private term_zero_outside
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.LaurentCechCohomology

private theorem card_tupleIndices {n p : ℕ} (t : IncreasingTuple (Index n) p) :
    (tupleIndices n t.1).card = p + 1 := by
  simp [tupleIndices, Finset.card_image_of_injective _ t.2.injective]

private abbrev tupleFace {n p : ℕ} (t : IncreasingTuple (Index n) p) : Faces n (p : ℤ) :=
  ⟨tupleIndices n t.1, by exact_mod_cast card_tupleIndices t,
    Finset.card_pos.mp (by rw [card_tupleIndices]; exact Nat.succ_pos _)⟩

private def faceTuple {n p : ℕ} (J : Faces n (p : ℤ)) : IncreasingTuple (Index n) p :=
  ⟨J.val.orderEmbOfFin (by exact_mod_cast J.property.1),
    (J.val.orderEmbOfFin _).strictMono⟩

private theorem tupleFace_faceTuple {n p : ℕ} (J : Faces n (p : ℤ)) :
    tupleFace (faceTuple J) = J := by
  apply Subtype.ext
  exact J.val.image_orderEmbOfFin_univ _

private theorem faceTuple_tupleFace {n p : ℕ} (t : IncreasingTuple (Index n) p) :
    faceTuple (tupleFace t) = t := by
  apply Subtype.ext
  symm
  exact Finset.orderEmbOfFin_unique _ (fun j ↦ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) t.2

/-- An increasing Čech index is the unique increasing enumeration of its vertex set. -/
private def tupleFaceEquiv (n p : ℕ) : IncreasingTuple (Index n) p ≃ Faces n (p : ℤ) where
  toFun := tupleFace
  invFun := faceTuple
  left_inv := faceTuple_tupleFace
  right_inv := tupleFace_faceTuple

private abbrev omitVertex {n p : ℕ} (t : IncreasingTuple (Index n) (p + 1)) (j : Fin (p + 2)) :
    IncreasingTuple (Index n) p :=
  ⟨t.1 ∘ j.succAbove, t.2.comp j.strictMono_succAbove⟩

private theorem indices_omit {n p : ℕ} (t : IncreasingTuple (Index n) (p + 1))
    (j : Fin (p + 2)) : tupleIndices n (omitVertex t j).1 = (tupleIndices n t.1).erase (t.1 j) := by
  ext a
  simp only [tupleIndices, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and,
    Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨fun h ↦ Fin.succAbove_ne _ _ (t.2.injective h), ⟨_, rfl⟩⟩
  · rintro ⟨hne, i, rfl⟩
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq (fun h : i = j ↦ hne (congrArg t.1 h))
    exact ⟨l, rfl⟩

private theorem tuple_sign (k : Type u) [Field k] {n p : ℕ}
    (t : IncreasingTuple (Index n) p) (j : Fin (p + 1)) :
    sign k (tupleIndices n t.1) (t.1 j) = (-1 : k) ^ j.val := by
  have heq : (tupleIndices n t.1).filter (· < t.1 j) = (Finset.Iio j).image t.1 := by
    ext a
    simp only [tupleIndices, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
      Finset.mem_Iio, true_and]
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, t.2.lt_iff_lt.mp hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, t.2 hi⟩
  rw [sign, heq, Finset.card_image_of_injective _ t.2.injective, Fin.card_Iio]

section Geometry

variable (k : Type u) [Field k] (n : ℕ)

private theorem tupleOpen_intersection (c : Cover (globalOpen k n) (Index n))
    (hc : c.opens = chart k n) {p : ℕ} (t : Fin (p + 1) → Index n) :
    tupleOpen c t = intersection k n (tupleIndices n t) := by
  rw [tupleOpen_eq_iInf, hc]
  apply le_antisymm
  · apply Finset.le_inf
    intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact iInf_le _ j
  · apply le_iInf
    intro j
    exact Finset.inf_le (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

private theorem indices_nonempty {p : ℕ} (t : Fin (p + 1) → Index n) :
    (tupleIndices n t).Nonempty :=
  ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_ground_scalar (f : Polynomials k n) {d : ℕ}
    (hf : f ∈ grading k n d) (hd : 0 < d) (r : k)
    (x : Proj.basicOpen (grading k n) f)
    (hP : Submonoid.powers f ≤ nonZeroDivisors (Polynomials k n)) :
    structureToFunctions k n (Proj.basicOpen (grading k n) f)
      ((R k n).obj.map (homOfLE le_top).op (groundScalarsValue k n r)) x =
        intoFraction k n (MvPolynomial.C r) := by
  let A := grading k n
  let V := Proj.basicOpen A f
  let a : CommRingCat.of k ⟶ CommRingCat.of (Away A f) :=
    CommRingCat.ofHom ((fromZeroRingHom A _).comp (constantInDegreeZero k n))
  have hScheme : V.ι ≫ Expected.structureMapValue k n =
      Proj.basicOpenToSpec A f ≫ Spec.map a := by
    apply (cancel_epi (Proj.basicOpenIsoSpec A f hf hd).inv).mp
    rw [← Category.assoc, Proj.basicOpenIsoSpec_inv_ι,
      ← Proj.basicOpenIsoSpec_hom A f hf hd, Iso.inv_hom_id_assoc]
    rw [Expected.structureMapValue, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
    rfl
  have hRestrict : (projectiveSpace k n).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op =
      V.ι.appTop ≫ V.topIso.hom := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    rfl
  have hRing :
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Expected.structureMapValue k n).appTop ≫
        (projectiveSpace k n).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op =
      a ≫ Proj.awayToSection A f := by
    rw [hRestrict, ← Category.assoc (Expected.structureMapValue k n).appTop,
      ← Scheme.Hom.comp_appTop, hScheme, Scheme.Hom.comp_appTop]
    simp only [Category.assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc,
      Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top, Iso.inv_hom_id_assoc,
      ]
    change a ≫ Proj.awayToSection A f ≫ V.topIso.inv ≫ V.topIso.hom = _
    rw [Iso.inv_hom_id, Category.comp_id]
  have hElement := ConcreteCategory.congr_hom hRing r
  change ((R k n).obj.map (homOfLE le_top).op) (groundScalarsValue k n r) =
    basicStructureEquiv k n f hf hd V rfl (a r) at hElement
  rw [hElement, basicStructureEquiv_value k n f hf hd V rfl hP]
  change homogeneousToFraction k n _ hP
    (HomogeneousLocalization.mk ⟨0, constantInDegreeZero k n r, 1, one_mem _⟩) = _
  rw [homogeneousToFraction_mk]
  simp [fraction, constantInDegreeZero]

private theorem ground_scalar_intersection (J : Finset (Index n)) (hJ : J.Nonempty)
    (r : k) (x : intersection k n J) :
    structureToFunctions k n (intersection k n J)
      ((R k n).obj.map (homOfLE le_top).op (groundScalarsValue k n r)) x =
        intoFraction k n (MvPolynomial.C r) := by
  revert x
  rw [intersectionBasicOpen]
  intro x
  exact restrict_ground_scalar k n _ (chartProduct_degree k n J) (Finset.card_pos.mpr hJ)
    r x (powers_product_le_nonZeroDivisors k n J)

private theorem chartToFraction_smul (J : Finset (Index n)) (r : k)
    (a : ChartLocalization k n J) :
    chartToFraction k n J (r • a) =
      intoFraction k n (MvPolynomial.C r) * chartToFraction k n J a := by
  rw [Algebra.smul_def, map_mul,
    IsScalarTower.algebraMap_apply k (Polynomials k n) (ChartLocalization k n J)]
  congr 1
  exact IsLocalization.lift_eq (unit_in_fraction k n _ (powers_product_le_nonZeroDivisors k n J)) _

private def chartDegreeEquiv (J : Finset (Index n)) (hJ : J.Nonempty) (m : ℤ) :
    chartPiece k n m J ≃ DegreePiece k n J m := by
  let h := (chartCoefficientComparison k n).1 J hJ m
  refine (Equiv.ofBijective (fun a : DegreePiece k n J m ↦
    (⟨a.val, (h _).2 ⟨a, rfl⟩⟩ : chartPiece k n m J)) ⟨?_, ?_⟩).symm
  · intro a b hab
    exact Subtype.ext (congrArg (fun a : chartPiece k n m J ↦ a.val) hab)
  · intro b
    obtain ⟨a, ha⟩ := (h _).1 b.property
    exact ⟨a, Subtype.ext ha⟩

private theorem chartDegreeEquiv_val (J : Finset (Index n)) (hJ : J.Nonempty) (m : ℤ)
    (a : chartPiece k n m J) : (chartDegreeEquiv k n J hJ m a).val = a.val :=
  congrArg Subtype.val ((chartDegreeEquiv k n J hJ m).symm_apply_apply a)

variable {c : Cover (globalOpen k n) (Index n)} {T : TwistFamily k n}

private abbrev groundLocal (m : ℤ) {p : ℕ} (t : Fin (p + 1) → Index n) :=
  (GroundRestriction k n).obj
    (localSections (R k n) (T m).val (globalOpen k n) (tupleOpen c t) (tupleOpen_le c t))

set_option backward.isDefEq.respectTransparency false in
private def chartCoordinateEquiv (hc : c.opens = chart k n)
    {w : SectionCoordinates k n T} (hw : TwistCoordinates k n w)
    {d : LocalizedCoordinates k n c T} (hd : LocalizedTerms k n c w d)
    (m : ℤ) (p : ℕ) (t : Fin (p + 1) → Index n) :
    chartPiece k n m (tupleIndices n t) ≃ₗ[k] groundLocal k n (c := c) (T := T) m t := by
  let J := tupleIndices n t
  let E := (chartDegreeEquiv k n J (indices_nonempty n t) m).trans (d m p t)
  have hE (a : chartPiece k n m J) (x : tupleOpen c t) :
      (w m (tupleOpen c t) (E a)).val x = chartToFraction k n J a.val := by
    exact (hd m p t _ x).trans (congrArg _ (chartDegreeEquiv_val k n J _ m a))
  refine { E with map_add' := ?_, map_smul' := ?_ }
  · intro a b
    apply (w m (tupleOpen c t)).injective
    apply Subtype.ext
    funext x
    change (w m _ (E (a + b))).val x = (w m _ (E a + E b)).val x
    rw [hw.1, hE, hE, hE]
    exact map_add _ _ _
  · intro r a
    apply (w m (tupleOpen c t)).injective
    apply Subtype.ext
    funext x
    change (w m _ (E (r • a))).val x =
      (w m _ (((R k n).obj.map (homOfLE (tupleOpen_le c t)).op
        (groundScalarsValue k n r)) • E a)).val x
    rw [hw.2.1, hE, hE]
    have hs : ∀ x : tupleOpen c t,
        structureToFunctions k n (tupleOpen c t)
          ((R k n).obj.map (homOfLE le_top).op (groundScalarsValue k n r)) x =
            intoFraction k n (MvPolynomial.C r) := by
      rw [tupleOpen_intersection k n c hc]
      exact ground_scalar_intersection k n J (indices_nonempty n t) r
    rw [hs x]
    exact chartToFraction_smul k n J r a.val

private theorem chartCoordinateEquiv_apply (hc : c.opens = chart k n)
    {w : SectionCoordinates k n T} (hw : TwistCoordinates k n w)
    {d : LocalizedCoordinates k n c T} (hd : LocalizedTerms k n c w d)
    (m : ℤ) (p : ℕ) (t : Fin (p + 1) → Index n) (a : chartPiece k n m (tupleIndices n t)) :
    ((d m p t).symm (chartCoordinateEquiv k n hc hw hd m p t a)).val = a.val := by
  change ((d m p t).symm ((d m p t) _)).val = _
  rw [Equiv.symm_apply_apply]
  exact chartDegreeEquiv_val k n _ _ _ a

private def termComparison (hc : c.opens = chart k n)
    {w : SectionCoordinates k n T} (hw : TwistCoordinates k n w)
    {d : LocalizedCoordinates k n c T} (hd : LocalizedTerms k n c w d)
    (m : ℤ) (p : ℕ) :
    LocalizedTerm k n m p ≃ₗ[k] (GroundComplex k n c (T m)).X p := by
  let e := Equiv.piCongrLeft' (fun J : Faces n p ↦ chartPiece k n m J.val)
    (tupleFaceEquiv n p).symm
  let a (t : IncreasingTuple (Index n) p) := chartCoordinateEquiv k n hc hw hd m p t.1
  let f : LocalizedTerm k n m p ≃ (GroundComplex k n c (T m)).X p :=
    e.trans (Equiv.piCongrRight fun t ↦ (a t).toEquiv)
  refine { f with map_add' := ?_, map_smul' := ?_ }
  · intro x y
    funext t
    exact map_add (a t) (x (tupleFace t)) (y (tupleFace t))
  · intro r x
    funext t
    exact map_smul (a t) r (x (tupleFace t))

private theorem termComparison_apply (hc : c.opens = chart k n)
    {w : SectionCoordinates k n T} (hw : TwistCoordinates k n w)
    {d : LocalizedCoordinates k n c T} (hd : LocalizedTerms k n c w d)
    (m : ℤ) (p : ℕ) (s : LocalizedTerm k n m p) (t : IncreasingTuple (Index n) p) :
    ((d m p t.1).symm
      ((show IncreasingCochains (R k n) c (T m).val p from
        termComparison k n hc hw hd m p s) t)).val = (s (tupleFace t)).val := by
  have h := chartCoordinateEquiv_apply k n hc hw hd m p t.1 (s (tupleFace t))
  exact h

private theorem localizedDeleteSum_fraction (m : ℤ) (p : ℕ)
    (s : LocalizedTerm k n m p) (t : IncreasingTuple (Index n) (p + 1)) :
    chartToFraction k n (tupleIndices n t.1) (localizedDeleteSum k n m p s (tupleFace t)) =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) •
        chartToFraction k n (tupleIndices n (omitVertex t j).1) (s (tupleFace (omitVertex t j))).val := by
  classical
  rw [localizedDeleteSum, map_sum]
  change (∑ i ∈ Finset.univ.image t.1, chartToFraction k n (tupleIndices n t.1) _) = _
  rw [Finset.sum_image (fun _ _ _ _ h ↦ t.2.injective h)]
  apply Finset.sum_congr rfl
  intro j _
  have h : (↑((tupleIndices n t.1).erase (t.1 j)).card : ℤ) = (p : ℤ) + 1 ∧
      ((tupleIndices n t.1).erase (t.1 j)).Nonempty := by
    rw [← indices_omit t j]
    exact (tupleFace (omitVertex t j)).property
  rw [dite_eq_left h, chartToFraction_smul, localizationRestriction_value, tuple_sign]
  have hi : (⟨(tupleIndices n t.1).erase (t.1 j), h⟩ : Faces n p) = tupleFace (omitVertex t j) :=
    Subtype.ext (indices_omit t j).symm
  rw [congrArg (fun J : Faces n p ↦ chartToFraction k n J.val (s J).val) hi]
  simp [zsmul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
private theorem termComparison_comm (hc : c.opens = chart k n)
    {w : SectionCoordinates k n T} (hw : TwistCoordinates k n w)
    {d : LocalizedCoordinates k n c T} (hd : LocalizedTerms k n c w d)
    (hD : LocalizedDifferential k n c d) (m : ℤ)
    (e : ∀ p : ℤ, Term k n m p ≃ₗ[k] LocalizedTerm k n m p)
    (he : ∀ p x (J : Faces n (p + 1)),
      (e (p + 1) (differential k n m p x) J).val = localizedDeleteSum k n m p (e p x) J)
    (p : ℕ) (x : Term k n m p) :
    (GroundComplex k n c (T m)).d p (p + 1) (termComparison k n hc hw hd m p (e p x)) =
      termComparison k n hc hw hd m (p + 1) (e (p + 1 : ℕ) (differential k n m p x)) := by
  let F := (T m).val
  change (GroundRestriction k n).map ((increasingComplex (R k n) c F).d p (p + 1)) _ = _
  rw [increasingComplex_d]
  change increasingDifferential (R k n) c F p (termComparison k n hc hw hd m p (e p x)) = _
  funext t
  apply (d m (p + 1) t.1).symm.injective
  apply Subtype.ext
  apply localizationToFraction_injective k n _ (powers_product_le_nonZeroDivisors k n _)
  change chartToFraction k n (tupleIndices n t.1)
      ((d m (p + 1) t.1).symm (increasingDifferential (R k n) c F p
        (termComparison k n hc hw hd m p (e p x)) t)).val = _
  rw [hD, termComparison_apply]
  have he' :
      (e (p + 1 : ℕ) (differential k n m p x) (tupleFace t)).val =
        localizedDeleteSum k n m p (e p x) (tupleFace t) :=
    he (p : ℤ) x (tupleFace t)
  rw [he']
  change _ = chartToFraction k n (tupleIndices n t.1) _
  rw [localizedDeleteSum_fraction]
  apply Finset.sum_congr rfl
  intro j _
  rw [termComparison_apply k n hc hw hd m p (e p x) (omitVertex t j)]

private def comparisonIso (hc : c.opens = chart k n)
    {w : SectionCoordinates k n T} (hw : TwistCoordinates k n w)
    {d : LocalizedCoordinates k n c T} (hd : LocalizedTerms k n c w d)
    (hD : LocalizedDifferential k n c d) (m : ℤ)
    (sq : ∀ p, (differential k n m (p + 1)).comp (differential k n m p) = 0)
    (e : ∀ p : ℤ, Term k n m p ≃ₗ[k] LocalizedTerm k n m p)
    (he : ∀ p x (J : Faces n (p + 1)),
      (e (p + 1) (differential k n m p x) J).val = localizedDeleteSum k n m p (e p x) J) :
    (orderedComplex k n m sq).restriction ComplexShape.embeddingUpNat ≅ GroundComplex k n c (T m) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ ((e p).trans (termComparison k n hc hw hd m p)).toModuleIso)
    (by
      intro p j hj
      obtain rfl : p + 1 = j := hj
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (GroundComplex k n c (T m)).d p (p + 1)
          (termComparison k n hc hw hd m p (e p x)) =
        termComparison k n hc hw hd m (p + 1) (e ((p : ℤ) + 1)
          ((orderedComplex k n m sq).d (p : ℤ) ((p : ℤ) + 1) x))
      simp only [orderedComplex, CochainComplex.of_d]
      exact termComparison_comm k n hc hw hd hD m e he p x)

private theorem comparisonIso_apply (hc : c.opens = chart k n)
    {w : SectionCoordinates k n T} (hw : TwistCoordinates k n w)
    {d : LocalizedCoordinates k n c T} (hd : LocalizedTerms k n c w d)
    (hD : LocalizedDifferential k n c d) (m : ℤ)
    (sq : ∀ p, (differential k n m (p + 1)).comp (differential k n m p) = 0)
    (e : ∀ p : ℤ, Term k n m p ≃ₗ[k] LocalizedTerm k n m p)
    (he : ∀ p x (J : Faces n (p + 1)),
      (e (p + 1) (differential k n m p x) J).val = localizedDeleteSum k n m p (e p x) J)
    (p : ℕ) (x : Term k n m p) :
    (comparisonIso k n hc hw hd hD m sq e he).hom.f p x =
      termComparison k n hc hw hd m p (e p x) := rfl

end Geometry

section Nonnegative

variable {k : Type u} [Field k]
variable {K : CochainComplex (ModuleCat.{u} k) ℤ} {L : CochainComplex (ModuleCat.{u} k) ℕ}

private abbrev natEmbedding := ComplexShape.embeddingUpNat

private theorem hasLift_of_nonnegative (φ : K.restriction natEmbedding ⟶ L)
    (hK : ∀ p : ℤ, p < 0 → IsZero (K.X p)) :
    natEmbedding.HasLift φ := by
  intro j hj p hp
  have hnr := hj.notMem hp
  have hneg : p < 0 := by
    by_contra! h
    exact hnr p.toNat (Int.toNat_of_nonneg h)
  exact (hK p hneg).eq_of_src _ _

private def nonnegativeIso (φ : K.restriction natEmbedding ⟶ L)
    (hK : ∀ p : ℤ, p < 0 → IsZero (K.X p)) (hφ : ∀ p, IsIso (φ.f p)) :
    K ≅ L.extend natEmbedding := by
  let lift := natEmbedding.liftExtend φ (hasLift_of_nonnegative φ hK)
  haveI (p : ℤ) : IsIso (lift.f p) := by
    by_cases h : 0 ≤ p
    · exact (natEmbedding.isIso_liftExtend_f_iff φ (hasLift_of_nonnegative φ hK)
        (Int.toNat_of_nonneg h)).mpr (hφ p.toNat)
    · have hr (j : ℕ) : natEmbedding.f j ≠ p := by
        change (j : ℤ) ≠ p
        omega
      exact (hK p (lt_of_not_ge h)).isIso (L.isZero_extend_X _ _ hr) _
  letI := HomologicalComplex.Hom.isIso_of_components lift
  exact asIso lift

private def nonnegativeHomologyIso (i : K ≅ L.extend natEmbedding) (q : ℕ) :
    K.homology (q : ℤ) ≅ L.homology q :=
  homologyMapIso i (q : ℤ) ≪≫ L.extendHomologyIso natEmbedding (rfl : natEmbedding.f q = (q : ℤ))

private def nonnegativeCyclesMap (i : K ≅ L.extend natEmbedding) (q : ℕ) :
    K.cycles (q : ℤ) ⟶ L.cycles q :=
  cyclesMap i.hom (q : ℤ) ≫ (L.extendCyclesIso natEmbedding
    (rfl : natEmbedding.f q = (q : ℤ))).hom

set_option backward.isDefEq.respectTransparency false in
private theorem nonnegativeHomologyIso_apply (i : K ≅ L.extend natEmbedding) (q : ℕ)
    (z : K.cycles (q : ℤ)) :
    (nonnegativeHomologyIso i q).hom (K.homologyπ _ z) =
      L.homologyπ q (nonnegativeCyclesMap i q z) := by
  have h : K.homologyπ _ ≫ (nonnegativeHomologyIso i q).hom =
      nonnegativeCyclesMap i q ≫ L.homologyπ q := by
    unfold nonnegativeHomologyIso nonnegativeCyclesMap
    rw [Iso.trans_hom, homologyMapIso_hom, ← Category.assoc,
      homologyπ_naturality, Category.assoc, homologyπ_extendHomologyIso_hom, Category.assoc]
  exact ConcreteCategory.congr_hom h z

set_option backward.isDefEq.respectTransparency false in
private theorem nonnegativeCyclesMap_apply (φ : K.restriction natEmbedding ⟶ L)
    (hK : ∀ p : ℤ, p < 0 → IsZero (K.X p)) (hφ : ∀ p, IsIso (φ.f p))
    (q : ℕ) (z : K.cycles (q : ℤ)) :
    L.iCycles q (nonnegativeCyclesMap (nonnegativeIso φ hK hφ) q z) =
      φ.f q (K.iCycles _ z) := by
  have h : nonnegativeCyclesMap (nonnegativeIso φ hK hφ) q ≫ L.iCycles q =
      K.iCycles _ ≫ φ.f q := by
    let hq : natEmbedding.f q = (q : ℤ) := rfl
    unfold nonnegativeCyclesMap
    rw [Category.assoc, extendCyclesIso_hom_iCycles]
    change cyclesMap (nonnegativeIso φ hK hφ).hom (natEmbedding.f q) ≫
      (L.extend natEmbedding).iCycles (natEmbedding.f q) ≫ _ = _
    rw [cyclesMap_i_assoc]
    change K.iCycles _ ≫ (natEmbedding.liftExtend φ (hasLift_of_nonnegative φ hK)).f _ ≫
        (L.extendXIso natEmbedding hq).hom = _
    rw [natEmbedding.liftExtend_f φ (hasLift_of_nonnegative φ hK) hq]
    have hi : (K.restrictionXIso natEmbedding hq).inv = 𝟙 (K.X (q : ℤ)) := rfl
    rw [hi]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Category.id_comp]
    rfl
  exact ConcreteCategory.congr_hom h z

end Nonnegative

/-- The canonical chart coordinates intertwine the two differentials and
identify the induced cycle classes in every nonnegative degree. -/
theorem comparison : Specs.DerivedFormalization.ProjectiveChartComplexBridge.comparisonType.{u} := by
  classical
  intro k _ n _ m c T w d hc hw hd hD sq e he K C
  let φ : K.restriction natEmbedding ≅ C := comparisonIso k n hc hw hd hD m sq e he
  have hK (p : ℤ) (hp : p < 0) : IsZero (K.X p) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      ⟨fun x y ↦ (term_zero_outside k (Or.inl hp) x).trans
        (term_zero_outside k (Or.inl hp) y).symm⟩
  have hφ (q : ℕ) : IsIso (φ.hom.f q) :=
    (HomologicalComplex.Hom.isoApp φ q).isIso_hom
  let i := nonnegativeIso φ.hom hK hφ
  refine ⟨φ, nonnegativeHomologyIso i, nonnegativeCyclesMap i, ?_⟩
  intro q z
  have hz : C.iCycles q (nonnegativeCyclesMap i q z) =
      φ.hom.f q (K.iCycles (q : ℤ) z) :=
    nonnegativeCyclesMap_apply φ.hom hK hφ q z
  refine ⟨nonnegativeHomologyIso_apply i q z, hz, ?_⟩
  intro t
  refine ⟨(tupleFace t).property, ?_⟩
  have hf : φ.hom.f q (K.iCycles (q : ℤ) z) =
      termComparison k n hc hw hd m q (e q (K.iCycles (q : ℤ) z)) :=
    comparisonIso_apply k n hc hw hd hD m sq e he q (K.iCycles (q : ℤ) z)
  have hval := congrArg
    (fun s : C.X q ↦ ((d m q t.val).symm
      ((show IncreasingCochains (R k n) c (T m).val q from s) t)).val) (hz.trans hf)
  exact congrArg (chartToLaurent k n (tupleIndices n t.val))
    (hval.trans (termComparison_apply k n hc hw hd m q (e q (K.iCycles (q : ℤ) z)) t))

end DerivedFormalization.ProjectiveChartComplexBridge
