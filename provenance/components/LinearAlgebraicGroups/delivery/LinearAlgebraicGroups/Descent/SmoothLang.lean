import Specs.LinearAlgebraicGroups.Descent.SmoothLang
import LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Polynomial

set_option maxHeartbeats 1000000

universe u

namespace LinearAlgebraicGroups

noncomputable section

private theorem connectedSpace_pullback_of_section {k K : Type u} [Field k] [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] {X : Scheme.{u}} [ConnectedSpace X]
    (f : X ⟶ Spec (CommRingCat.of k)) (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _) :
    ConnectedSpace ↥(pullback f (fieldSpecMap k K) : Scheme.{u}) := by
  let b := fieldSpecMap k K
  let p := pullback.fst f b
  let t : Spec (CommRingCat.of K) ⟶ pullback f b :=
    pullback.lift (b ≫ s) (𝟙 _) (by simp [hs])
  have hp : t ≫ p = b ≫ s := pullback.lift_fst _ _ _
  let x := s (IsLocalRing.closedPoint k)
  let y := t (IsLocalRing.closedPoint K)
  have hsRange : Set.range s = {x} := Set.range_eq_singleton (fun a ↦ congrArg s (Subsingleton.elim a _))
  have htRange : Set.range t = {y} := Set.range_eq_singleton (fun a ↦ congrArg t (Subsingleton.elim a _))
  have hpb : IsPullback t b p s := by
    apply IsPullback.flip
    refine IsPullback.of_bot ?_ hp.symm (IsPullback.of_hasPullback f b)
    have ht : t ≫ pullback.snd f b = 𝟙 _ := pullback.lift_snd _ _ _
    rw [ht, hs]
    exact IsPullback.of_id_snd
  have hfibre : Set.range t = p ⁻¹' {x} := by
    rw [← hsRange]
    let e := hpb.isoPullback
    have he : e.hom ≫ pullback.fst p s = t := hpb.isoPullback_hom_fst
    rw [← he, ← Scheme.Pullback.range_fst p s]
    have hs : Function.Surjective e.hom := e.hom.homeomorph.surjective
    exact hs.range_comp (pullback.fst p s)
  have : IsIntegralHom b := IsIntegralHom.SpecMap_iff.mpr
    (Algebra.isIntegral_def.mp (inferInstance : Algebra.IsIntegral k K))
  have hopen : IsOpenMap p := p.isOpenMap
  have hclosed : IsClosedMap p := p.isClosedMap
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨y⟩, ?_⟩
  intro U hU
  by_cases hEmpty : U = ∅
  · exact Or.inl hEmpty
  refine Or.inr ?_
  by_contra hTop
  have hu : p '' U = Set.univ :=
    IsClopen.eq_univ ⟨hclosed _ hU.1, hopen _ hU.2⟩
      ((Set.nonempty_iff_ne_empty.mpr hEmpty).image p)
  have hc : p '' Uᶜ = Set.univ :=
    IsClopen.eq_univ ⟨hclosed _ hU.compl.1, hopen _ hU.compl.2⟩
      ((Set.nonempty_compl.mpr hTop).image p)
  have hu' : x ∈ p '' U := hu.symm ▸ Set.mem_univ _
  have hc' : x ∈ p '' Uᶜ := hc.symm ▸ Set.mem_univ _
  obtain ⟨a, ha, hax⟩ := hu'
  obtain ⟨c, hc, hcx⟩ := hc'
  have only (v : ↥(pullback f b : Scheme.{u})) (h : p v = x) : v = y := by
    have hv : v ∈ (p ⁻¹' {x} : Set ↥(pullback f b : Scheme.{u})) := h
    rw [← hfibre, htRange] at hv
    exact hv
  exact hc (only c hcx |>.trans (only a hax).symm ▸ ha)

theorem smoothGroupGeometricConnectedness : Specs.SmoothGroupGeometricConnectedness.{u} := by
  intro k _ _ G _ _ _
  exact connectedSpace_pullback_of_section G.X.hom (groupIdentitySection G) (Over.w _)

private theorem pow_card_eq_self_iff {k K : Type u} [Field k] [Fintype k] [Field K]
    [Algebra k K] (x : K) :
    x ^ Fintype.card k = x ↔ x ∈ Set.range (algebraMap k K) := by
  classical
  let f : k[X] := Polynomial.X ^ Fintype.card k - Polynomial.X
  have hdegree : f.natDegree = Fintype.card k :=
    FiniteField.X_pow_card_sub_X_natDegree_eq k Fintype.one_lt_card
  have hcard : f.roots.card = f.natDegree := by
    rw [hdegree, FiniteField.roots_X_pow_card_sub_X]
    simp
  have hne : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
  have hm := Polynomial.roots_map_of_injective_of_card_eq_natDegree (p := f)
    (algebraMap k K).injective hcard
  constructor
  · intro hx
    have hr : x ∈ (f.map (algebraMap k K)).roots :=
      (Polynomial.mem_roots_map_of_injective (algebraMap k K).injective hne).mpr (by simp [f, hx])
    rw [← hm] at hr
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hr
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

private theorem frobeniusOnPoints_left {k : Type u} [Field k] [Fintype k]
    {X : SchemeOver k} {R : TestAlgebra k} (x : Points X R) :
    (frobeniusOnPoints R x).left =
      Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom k R).toRingHom) ≫ x.left := rfl

private theorem extendRationalPoint_left {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : SchemeOver k} (x : Points X (CommAlgCat.of k k)) :
    (extendRationalPoint (K := K) x).left = fieldSpecMap k K ≫ x.left := rfl

theorem frobeniusFixedPoints : Specs.FrobeniusFixedPoints.{u} := by
  intro k K _ _ _ _ X x
  let σ := CommRingCat.ofHom (FiniteField.frobeniusAlgHom k K).toRingHom
  constructor
  · intro h
    have hx : Spec.map σ ≫ x.left = x.left := by
      rw [← frobeniusOnPoints_left x, h]
    obtain ⟨⟨z, a⟩, ha⟩ := (Scheme.SpecToEquivOfField K X.left).symm.surjective x.left
    change Spec.map a ≫ X.left.fromSpecResidueField z = x.left at ha
    rw [← ha, ← Category.assoc, ← Spec.map_comp, cancel_mono] at hx
    have hfix : a ≫ σ = a := Spec.map_injective hx
    have ha' (r : X.left.residueField z) :
        a r ∈ Set.range (algebraMap k K) := by
      apply (pow_card_eq_self_iff (k := k) _).mp
      exact congrArg (fun f : X.left.residueField z ⟶ CommRingCat.of K ↦ f r) hfix
    let i : k ≃+* (algebraMap k K).range :=
      RingEquiv.ofLeftInverse (Function.injective_iff_hasLeftInverse.mp (algebraMap k K).injective).choose_spec
    let a₀ := CommRingCat.ofHom (i.symm.toRingHom.comp (a.hom.codRestrict _ ha'))
    have hf : a₀ ≫ CommRingCat.ofHom (algebraMap k K) = a := by
      ext r
      exact congrArg Subtype.val (i.apply_symm_apply ⟨a r, ha' r⟩)
    let x₀ := Spec.map a₀ ≫ X.left.fromSpecResidueField z
    have he : fieldSpecMap k K ≫ x₀ = x.left := by
      change fieldSpecMap k K ≫ Spec.map a₀ ≫ X.left.fromSpecResidueField z = x.left
      rw [← ha, ← Category.assoc, ← Spec.map_comp, hf]
    have hx₀ : x₀ ≫ X.hom = 𝟙 _ := by
      have hh : fieldSpecMap k K ≫ (x₀ ≫ X.hom) = fieldSpecMap k K := by
        rw [← Category.assoc, he]
        exact Over.w x
      obtain ⟨β, hβ⟩ := Spec.map_surjective (x₀ ≫ X.hom)
      rw [← hβ, ← Spec.map_comp] at hh
      have heq := Spec.map_injective hh
      rw [← hβ, ← Spec.map_id]
      congr 1
      apply CommRingCat.hom_ext
      ext r
      exact (algebraMap k K).injective (congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of K ↦ f r) heq)
    refine ⟨Over.homMk x₀ (hx₀.trans ?_), ?_⟩
    · exact (Spec.map_id _).symm
    · apply Over.OverMorphism.ext
      exact he
  · rintro ⟨a, rfl⟩
    apply Over.OverMorphism.ext
    have hσ : Spec.map σ ≫ fieldSpecMap k K = fieldSpecMap k K := by
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      ext r
      change (algebraMap k K r) ^ Fintype.card k = algebraMap k K r
      rw [← map_pow, FiniteField.pow_card]
    rw [frobeniusOnPoints_left, extendRationalPoint_left]
    change Spec.map σ ≫ fieldSpecMap k K ≫ a.left = fieldSpecMap k K ≫ a.left
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ a.left) hσ)

private def frobeniusPointHom {k : Type u} [Field k] [Fintype k] (G : Specs.GroupScheme k)
    (R : TestAlgebra k) : Points G.X R →* Points G.X R where
  toFun := frobeniusOnPoints R
  map_one' := MonObj.comp_one _
  map_mul' := MonObj.comp_mul _

theorem smoothLangFibres : Specs.SmoothLangFibres.{u} := by
  intro k _ _ G g h
  let F := frobeniusPointHom G (CommAlgCat.of k (AlgebraicClosure k))
  change F h * h⁻¹ = F g * g⁻¹ ↔ _
  constructor
  · intro he
    have hf : F (g⁻¹ * h) = g⁻¹ * h := by
      rw [map_mul, map_inv]
      have he' := congrArg (fun x ↦ (F g)⁻¹ * x * h) he
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he'
    obtain ⟨a, ha⟩ := (frobeniusFixedPoints k (AlgebraicClosure k) G.X (g⁻¹ * h)).mp hf
    exact ⟨a, by rw [ha, mul_inv_cancel_left]⟩
  · rintro ⟨a, rfl⟩
    have hf : F (extendRationalPoint (K := AlgebraicClosure k) a) = extendRationalPoint a :=
      (frobeniusFixedPoints k (AlgebraicClosure k) G.X _).mpr ⟨a, rfl⟩
    rw [map_mul, hf, mul_inv_rev, mul_assoc, mul_inv_cancel_left]

private theorem mapPoints_comp_apply {k : Type u} [Field k] {X : SchemeOver k}
    {R S T : TestAlgebra k} (a : R ⟶ S) (b : S ⟶ T) (p : Points X R) :
    mapPoints b (mapPoints a p) = mapPoints (a ≫ b) p := by
  simp only [mapPoints, ← Category.assoc, ← Functor.map_comp, ← op_comp]

private def mapPointsMonoidHom {k : Type u} [Field k] (G : Specs.GroupScheme k)
    {R S : TestAlgebra k} (a : R ⟶ S) : Points G.X R →* Points G.X S where
  toFun := mapPoints a
  map_one' := MonObj.comp_one _
  map_mul' := MonObj.comp_mul _

private theorem frobeniusOnPoints_naturality {k : Type u} [Field k] [Fintype k]
    {X : SchemeOver k} {R S : TestAlgebra k} (a : R ⟶ S) (p : Points X R) :
    mapPoints a (frobeniusOnPoints _ p) = frobeniusOnPoints _ (mapPoints a p) := by
  unfold frobeniusOnPoints
  rw [mapPoints_comp_apply, mapPoints_comp_apply]
  congr 1
  ext x
  exact map_pow a.hom x (Fintype.card k)

private theorem frobeniusOnPoints_eq_of_quotient {k K A : Type u} [Field k] [Fintype k]
    [Field K] [Algebra k K] [CommRing A] [Algebra K A]
    {X : SchemeOver k} (I : Ideal A) (hI : I ^ 2 = ⊥)
    {p q : Points X ((restrictTestAlgebra k K).obj (CommAlgCat.of K A))}
    (hpq : mapPoints ((restrictTestAlgebra k K).map
      (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I))) p =
      mapPoints ((restrictTestAlgebra k K).map
      (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I))) q) :
    frobeniusOnPoints _ p = frobeniusOnPoints _ q := by
  let R := (restrictTestAlgebra k K).obj (CommAlgCat.of K A)
  let S := (restrictTestAlgebra k K).obj (CommAlgCat.of K (A ⧸ I))
  let : Algebra k R := R.algebra
  let : Algebra k S := S.algebra
  let m : R ⟶ S := (restrictTestAlgebra k K).map
    (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I))
  let φ : R →ₐ[k] R := FiniteField.frobeniusAlgHom k R
  have hk (a : R) (ha : a ∈ I) : φ a = 0 := by
    change a ^ Fintype.card k = 0
    apply pow_eq_zero_of_le (show 2 ≤ Fintype.card k from Fintype.one_lt_card)
    have h : a * a ∈ I ^ 2 := by simpa only [pow_two] using Ideal.mul_mem_mul ha ha
    simpa [hI, pow_two] using h
  let b : S ⟶ R := CommAlgCat.ofHom (show S →ₐ[k] R from
    { toRingHom := Ideal.Quotient.lift I φ.toRingHom hk
      commutes' := fun x ↦ by
        change Ideal.Quotient.lift I φ.toRingHom hk (Ideal.Quotient.mk I (algebraMap k R x)) = _
        rw [Ideal.Quotient.lift_mk]
        exact φ.commutes x })
  have hf : m ≫ b = CommAlgCat.ofHom φ := by
    ext a
    exact Ideal.Quotient.lift_mk I φ.toRingHom hk
  change mapPoints m p = mapPoints m q at hpq
  have e := congrArg (mapPoints b) hpq
  rw [mapPoints_comp_apply, mapPoints_comp_apply, hf] at e
  exact e

section ScalarExtensionFrobenius

variable {k K : Type u} [Field k] [Fintype k] [Field K] [Algebra k K]

private def baseFrobeniusOnPoints (G : Specs.GroupScheme k) (R : TestAlgebra K) :
    Points ((groupBaseChange k K).obj G).X R →*
      Points ((groupBaseChange k K).obj G).X R :=
  let e := baseChangePointGroupEquiv K G R
  e.symm.toMonoidHom.comp ((frobeniusPointHom G _).comp e.toMonoidHom)

private theorem baseChangePoint_baseFrobeniusOnPoints (G : Specs.GroupScheme k)
    (R : TestAlgebra K) (p : Points ((groupBaseChange k K).obj G).X R) :
    baseChangePoint k K G.X R (baseFrobeniusOnPoints G R p) =
      frobeniusOnPoints _ (baseChangePoint k K G.X R p) := by
  let e := baseChangePointGroupEquiv K G R
  exact e.apply_symm_apply (frobeniusOnPoints _ (e p))

private theorem baseFrobeniusOnPoints_naturality (G : Specs.GroupScheme k)
    {R S : TestAlgebra K} (a : R ⟶ S) (p : Points ((groupBaseChange k K).obj G).X R) :
    mapPoints a (baseFrobeniusOnPoints G R p) =
      baseFrobeniusOnPoints G S (mapPoints a p) := by
  apply (baseChangePoints k K G.X S).injective
  rw [baseChangePoint_baseFrobeniusOnPoints]
  erw [baseChangePointsNaturality k K G.X a (baseFrobeniusOnPoints G R p),
    baseChangePointsNaturality k K G.X a p, baseChangePoint_baseFrobeniusOnPoints,
    frobeniusOnPoints_naturality]

private theorem baseFrobeniusOnPoints_eq_of_quotient (G : Specs.GroupScheme k)
    {A : Type u} [CommRing A] [Algebra K A] (I : Ideal A) (hI : I ^ 2 = ⊥)
    {p q : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K A)}
    (hpq : mapPoints (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I)) p =
      mapPoints (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I)) q) :
    baseFrobeniusOnPoints G _ p = baseFrobeniusOnPoints G _ q := by
  apply (baseChangePoints k K G.X (CommAlgCat.of K A)).injective
  rw [baseChangePoint_baseFrobeniusOnPoints, baseChangePoint_baseFrobeniusOnPoints]
  let a := CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I)
  let R := CommAlgCat.of K A
  let S := CommAlgCat.of K (A ⧸ I)
  apply frobeniusOnPoints_eq_of_quotient (k := k) (K := K) I hI
  exact (baseChangePointsNaturality k K G.X (R := R) (S := S) a p).symm.trans
    ((congrArg (baseChangePoint k K G.X S) hpq).trans
      (baseChangePointsNaturality k K G.X (R := R) (S := S) a q))

private def scalarHom (R : TestAlgebra K) : CommAlgCat.of K K ⟶ R :=
  CommAlgCat.ofHom (Algebra.ofId K R)

/-- The twisted orbit operation with a fixed K-point, on affine K-test schemes. -/
private def twistedOrbitPoint (G : Specs.GroupScheme k)
    (x : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K))
    {R : TestAlgebra K} (p : Points ((groupBaseChange k K).obj G).X R) :
    Points ((groupBaseChange k K).obj G).X R :=
  baseFrobeniusOnPoints G R p *
    mapPoints (scalarHom R) x * p⁻¹

private theorem twistedOrbitPoint_naturality (G : Specs.GroupScheme k)
    (x : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K))
    {R S : TestAlgebra K} (a : R ⟶ S) (p : Points ((groupBaseChange k K).obj G).X R) :
    mapPoints a (twistedOrbitPoint G x p) = twistedOrbitPoint G x (mapPoints a p) := by
  let H := (groupBaseChange k K).obj G
  let m := mapPointsMonoidHom H a
  have h : (scalarHom R) ≫ a =
      scalarHom S := by ext
  change m (twistedOrbitPoint G x p) = _
  unfold twistedOrbitPoint
  rw [map_mul, map_mul, map_inv]
  change mapPoints a (baseFrobeniusOnPoints G R p) *
    mapPoints a (mapPoints (scalarHom R) x) *
      (mapPoints a p)⁻¹ = _
  rw [baseFrobeniusOnPoints_naturality, mapPoints_comp_apply, h]

private theorem twistedOrbitPoint_lift (G : Specs.GroupScheme k)
    (x : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K))
    {A : Type u} [CommRing A] [Algebra K A] (I : Ideal A) (hI : I ^ 2 = ⊥)
    (p y : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K A))
    (hy : mapPoints (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I)) y =
      twistedOrbitPoint G x (mapPoints (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I)) p)) :
    ∃! z : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K A),
      mapPoints (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I)) z =
          mapPoints (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I)) p ∧
        twistedOrbitPoint G x z = y := by
  let H := (groupBaseChange k K).obj G
  let ca := CommAlgCat.ofHom (Algebra.ofId K A)
  let m := mapPointsMonoidHom H (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I))
  let F := baseFrobeniusOnPoints G (CommAlgCat.of K A)
  let c := mapPoints ca x
  let z := y⁻¹ * F p * c
  have he : m y = m (F p * c * p⁻¹) :=
    hy.trans (twistedOrbitPoint_naturality G x (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I)) p).symm
  have hz : m z = m p := by
    simp only [z, map_mul, map_inv, he]
    group
  have hf : F z = F p := baseFrobeniusOnPoints_eq_of_quotient G I hI hz
  refine ⟨z, ⟨hz, ?_⟩, ?_⟩
  · change F z * c * z⁻¹ = y
    rw [hf]
    dsimp only [z]
    group
  · intro w hw
    have eqF : F w = F p := baseFrobeniusOnPoints_eq_of_quotient G I hI hw.1
    have h : F w * c * w⁻¹ = y := hw.2
    rw [eqF] at h
    change w = y⁻¹ * F p * c
    rw [← h]
    group


private theorem exists_affine_point_range {X : SchemeOver K} (U : X.left.Opens)
    (hU : IsAffineOpen U) :
    ∃ (A : TestAlgebra K) (i : Points X A), IsOpenImmersion i.left ∧
      Set.range i.left = (U : Set X.left) := by
  let V : SchemeOver K := Over.mk (U.ι ≫ X.hom)
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (G := V)).mpr hU
  let i : Points X A.unop := e.hom ≫ Over.homMk U.ι rfl
  have hs : Function.Surjective e.hom.left :=
    ((Over.forget _).mapIso e).hom.homeomorph.surjective
  refine ⟨A.unop, i, ?_, ?_⟩
  · change IsOpenImmersion (e.hom.left ≫ U.ι)
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    infer_instance
  · change Set.range (U.ι ∘ e.hom.left) = _
    exact (hs.range_comp U.ι).trans Subtype.range_coe

private def factorPointThroughOpen {X : SchemeOver K} {A B : TestAlgebra K}
    (i : Points X A) [IsOpenImmersion i.left] (y : Points X B)
    (h : Set.range y.left ⊆ Set.range i.left) :
    Points ((testSpec K).obj (op A)) B :=
  Over.homMk (IsOpenImmersion.lift i.left y.left h) (by
    rw [← Over.w i, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w y])

private theorem factorPointThroughOpen_comp {X : SchemeOver K} {A B : TestAlgebra K}
    (i : Points X A) [IsOpenImmersion i.left] (y : Points X B)
    (h : Set.range y.left ⊆ Set.range i.left) :
    factorPointThroughOpen i y h ≫ i = y := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac i.left y.left h

private theorem quotientSpec_surjective {A : Type u} [CommRing A] [Algebra K A]
    (I : Ideal A) (hI : I ^ 2 = ⊥) :
    Function.Surjective (((testSpec K).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K I)).op).left) := by
  change Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.mk I))
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  apply Set.eq_univ_of_forall
  intro z
  change RingHom.ker (Ideal.Quotient.mk I) ≤ z.asIdeal
  rw [Ideal.mk_ker]
  intro a ha
  have h : a * a ∈ I ^ 2 := by simpa only [pow_two] using Ideal.mul_mem_mul ha ha
  rw [hI, Ideal.mem_bot] at h
  exact (z.isPrime.mem_or_mem (h ▸ z.asIdeal.zero_mem)).elim id id

private abbrev affinePoint {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (a : A →ₐ[K] B) :
    Points ((testSpec K).obj (op (CommAlgCat.of K A))) (CommAlgCat.of K B) :=
  (testSpec K).map (CommAlgCat.ofHom a).op

private theorem affinePoint_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C] (a : A →ₐ[K] B) (b : B →ₐ[K] C) :
    affinePoint (b.comp a) = affinePoint b ≫ affinePoint a := by
  rw [← Functor.map_comp]
  rfl

private theorem affinePoint_bijective {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] :
    Function.Bijective (affinePoint : (A →ₐ[K] B) → _) := by
  let hf : (testSpec K).FullyFaithful := algSpec.fullyFaithful
  constructor
  · intro f g h
    have e := hf.map_injective (f := (CommAlgCat.ofHom f).op) (g := (CommAlgCat.ofHom g).op) h
    exact congrArg (fun a : op (CommAlgCat.of K B) ⟶ op (CommAlgCat.of K A) ↦ a.unop.hom) e
  · intro f
    obtain ⟨a, ha⟩ := hf.map_surjective f
    exact ⟨a.unop.hom, ha⟩

private theorem mapPoints_affinePoint {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    {Y : SchemeOver K} (a : A →ₐ[K] B) (m : B →ₐ[K] C)
    (p : Points Y (CommAlgCat.of K A)) :
    mapPoints (CommAlgCat.ofHom m) (affinePoint a ≫ p) = affinePoint (m.comp a) ≫ p := by
  rw [affinePoint_comp a m]
  exact (Category.assoc _ _ _).symm

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency false in

private theorem etale_affine_twistedOrbit (G : Specs.GroupScheme k)
    (x : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K))
    {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Algebra.FormallySmooth K A] [IsNoetherianRing B]
    (i : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K A))
    (j : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K B))
    [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (β : B →ₐ[K] A) (hβ : affinePoint β ≫ j = twistedOrbitPoint G x i)
    [LocallyOfFiniteType (affinePoint β).left] :
    Etale (affinePoint β).left := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  let : Algebra B A := β.toRingHom.toAlgebra
  let : IsScalarTower K B A := IsScalarTower.of_algHom β
  change Algebra.Etale B A
  apply Algebra.Etale.iff_formallyUnramified_and_smooth.mpr
  have hformal : Algebra.FormallyEtale B A := by
    apply Algebra.FormallyEtale.iff_comp_bijective.mpr
    intro T _ _ I hI
    let : Algebra K T := ((algebraMap B T).comp (algebraMap K B)).toAlgebra
    let : IsScalarTower K B T := IsScalarTower.of_algebraMap_eq' rfl
    let m := Ideal.Quotient.mkₐ K I
    let b : B →ₐ[K] T := IsScalarTower.toAlgHom K B T
    have bcomp (a : A →ₐ[B] T) : (a.restrictScalars K).comp β = b := by
      ext z
      exact a.commutes z
    have bcomp₀ (a : A →ₐ[B] (T ⧸ I)) : (a.restrictScalars K).comp β = m.comp b := by
      ext z
      exact a.commutes z
    have chart (a : A →ₐ[K] T) :
        twistedOrbitPoint G x (affinePoint a ≫ i) = affinePoint (a.comp β) ≫ j := by
      calc
        _ = affinePoint a ≫ twistedOrbitPoint G x i :=
          (twistedOrbitPoint_naturality G x (CommAlgCat.ofHom a) i).symm
        _ = _ := by rw [← hβ, ← Category.assoc, ← affinePoint_comp β a]
    constructor
    · intro a₁ a₂ ha
      let p₁ := affinePoint (a₁.restrictScalars K) ≫ i
      let p₂ := affinePoint (a₂.restrictScalars K) ≫ i
      let y := affinePoint b ≫ j
      have he : mapPoints (CommAlgCat.ofHom m) p₁ = mapPoints (CommAlgCat.ofHom m) p₂ := by
        dsimp only [p₁, p₂]
        rw [mapPoints_affinePoint _ m i, mapPoints_affinePoint _ m i]
        have heq : m.comp (a₁.restrictScalars K) = m.comp (a₂.restrictScalars K) := by
          apply AlgHom.ext
          intro t
          exact congrArg (fun z : A →ₐ[B] (T ⧸ I) ↦ z t) ha
        rw [heq]
      have h₁ : twistedOrbitPoint G x p₁ = y := by
        change twistedOrbitPoint G x (affinePoint (a₁.restrictScalars K) ≫ i) = affinePoint b ≫ j
        rw [chart, bcomp]
      have h₂ : twistedOrbitPoint G x p₂ = y := by
        change twistedOrbitPoint G x (affinePoint (a₂.restrictScalars K) ≫ i) = affinePoint b ≫ j
        rw [chart, bcomp]
      have hy : mapPoints (CommAlgCat.ofHom m) y = twistedOrbitPoint G x (mapPoints (CommAlgCat.ofHom m) p₁) := by
        rw [← h₁, twistedOrbitPoint_naturality]
      obtain ⟨z, _, hz⟩ := twistedOrbitPoint_lift G x I hI p₁ y hy
      have h : p₁ = p₂ := (hz p₁ ⟨rfl, h₁⟩).trans (hz p₂ ⟨he.symm, h₂⟩).symm
      have hinj : Mono i := by
        let : Mono i.left := inferInstance
        exact (Over.forget _).mono_of_mono_map (f := i) ‹Mono i.left›
      have heq := (affinePoint_bijective (K := K)).injective ((cancel_mono i).mp h)
      ext r
      exact congrArg (fun a : A →ₐ[K] T ↦ a r) heq
    · intro a₀
      obtain ⟨a', ha'⟩ := Algebra.FormallySmooth.exists_lift I ⟨2, hI⟩ (a₀.restrictScalars K)
      let p := affinePoint a' ≫ i
      let y := affinePoint b ≫ j
      have hre : mapPoints (CommAlgCat.ofHom m) p = affinePoint (a₀.restrictScalars K) ≫ i := by
        dsimp only [p]
        rw [mapPoints_affinePoint a' m i, ha']
      have hy : mapPoints (CommAlgCat.ofHom m) y =
          twistedOrbitPoint G x (mapPoints (CommAlgCat.ofHom m) p) := by
        rw [hre]
        dsimp only [y]
        rw [mapPoints_affinePoint b m j]
        have hcomp : affinePoint (a₀.restrictScalars K) ≫ affinePoint β ≫ j =
            affinePoint (m.comp b) ≫ j := by rw [← Category.assoc, ← affinePoint_comp, bcomp₀]
        rw [← hcomp, hβ]
        exact twistedOrbitPoint_naturality G x (CommAlgCat.ofHom (a₀.restrictScalars K)) i
      obtain ⟨z, ⟨hz, he⟩, _⟩ := twistedOrbitPoint_lift G x I hI p y hy
      have hRange : Set.range z.left ⊆ Set.range i.left := by
        have hv := congrArg (fun a ↦ Set.range a.left) (hz.trans hre)
        change Set.range (z.left ∘ (affinePoint m).left) = _ at hv
        rw [(quotientSpec_surjective I hI).range_comp z.left] at hv
        rw [hv]
        change Set.range (i.left ∘ (affinePoint (a₀.restrictScalars K)).left) ⊆ Set.range i.left
        exact Set.range_comp_subset_range _ _
      obtain ⟨a, ha⟩ := (affinePoint_bijective (K := K)).surjective (factorPointThroughOpen i z hRange)
      have hzi : affinePoint a ≫ i = z := by rw [ha, factorPointThroughOpen_comp]
      have hji : Mono j := by
        let : Mono j.left := inferInstance
        exact (Over.forget _).mono_of_mono_map (f := j) ‹Mono j.left›
      have hβ' : a.comp β = b := by
        apply (affinePoint_bijective (K := K)).injective
        apply (cancel_mono j).mp
        rw [← chart, hzi, he]
      let AtoT : A →ₐ[B] T :=
        { toRingHom := a.toRingHom
          commutes' := fun r ↦ congrArg (fun c : B →ₐ[K] T ↦ c r) hβ' }
      refine ⟨AtoT, ?_⟩
      have hii : Mono i := by
        let : Mono i.left := inferInstance
        exact (Over.forget _).mono_of_mono_map (f := i) ‹Mono i.left›
      have ha₀ : m.comp a = a₀.restrictScalars K := by
        apply (affinePoint_bijective (K := K)).injective
        apply (cancel_mono i).mp
        rw [affinePoint_comp, Category.assoc, hzi]
        exact hz.trans hre
      ext r
      exact congrArg (fun c : A →ₐ[K] (T ⧸ I) ↦ c r) ha₀
  let : Algebra.FormallyEtale B A := hformal
  refine ⟨inferInstance, ⟨inferInstance, ?_⟩⟩
  have ht := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    (inferInstance : LocallyOfFiniteType (affinePoint β).left)
  exact Algebra.FinitePresentation.of_finiteType.mp ht

private def pointsClosedEquiv [IsAlgClosed K] (X : SchemeOver K) [LocallyOfFiniteType X.hom] :
    Points X (CommAlgCat.of K K) ≃ closedPoints X.left :=
  (show Points X (CommAlgCat.of K K) ≃
      {p : Spec (CommRingCat.of K) ⟶ X.left // p ≫ X.hom = 𝟙 _} from
    { toFun := fun p ↦ ⟨p.left, (Over.w p).trans (Spec.map_id _)⟩
      invFun := fun p ↦ Over.homMk p.1 (p.2.trans (Spec.map_id _).symm)
      left_inv := fun _ ↦ Over.OverMorphism.ext rfl
      right_inv := fun _ ↦ Subtype.ext rfl }).trans (pointEquivClosedPoint X.hom)

private theorem point_in_range_of_closed_point [IsAlgClosed K] {X Y : SchemeOver K}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (y : Points Y (CommAlgCat.of K K))
    (hy : y.left (IsLocalRing.closedPoint K) ∈ Set.range f.left) :
    ∃ z : Points X (CommAlgCat.of K K), z ≫ f = y := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let e := pointsClosedEquiv (K := K) Y
  let t : Set X.left := f.left ⁻¹' {(e y).1}
  have ht : t.Nonempty := by
    obtain ⟨a, ha⟩ := hy
    exact ⟨a, ha⟩
  have htc : IsClosed t := (e y).2.preimage f.left.continuous
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints ht htc.isLocallyClosed
  refine ⟨(pointsClosedEquiv (K := K) X).symm ⟨z, hzc⟩, e.injective (Subtype.ext ?_)⟩
  have hz' := congrArg Subtype.val ((pointsClosedEquiv (K := K) X).apply_symm_apply ⟨z, hzc⟩)
  change f.left (((pointsClosedEquiv (K := K) X).symm ⟨z, hzc⟩).left (IsLocalRing.closedPoint K)) =
    (e y).1
  exact (congrArg f.left hz').trans hz

private theorem twistedOrbitPoint_one (G : Specs.GroupScheme k)
    (x : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K)) :
    twistedOrbitPoint G x 1 = x := by
  have h : scalarHom (CommAlgCat.of K K) = 𝟙 _ := by ext
  simp [twistedOrbitPoint, h, mapPoints]

set_option maxHeartbeats 2500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_open_neighborhood_twistedOrbit [IsAlgClosed K]
    (G : Specs.GroupScheme k) [Smooth G.X.hom]
    (x : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K)) :
    ∃ U : Set ((groupBaseChange k K).obj G).X.left, IsOpen U ∧
      x.left (IsLocalRing.closedPoint K) ∈ U ∧
      ∀ y : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K),
        y.left (IsLocalRing.closedPoint K) ∈ U →
          ∃ g : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K),
            twistedOrbitPoint G x g = y := by
  let H := (groupBaseChange k K).obj G
  let e : Points H.X (CommAlgCat.of K K) := 1
  have hH : Smooth H.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom (fieldSpecMap k K)))
  obtain ⟨U, hU, heU, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := e.left (IsLocalRing.closedPoint K)) (by trivial)
  obtain ⟨A, i, hi, hiR⟩ := exists_affine_point_range U hU
  have heRange : Set.range e.left ⊆ Set.range i.left := by
    rw [hiR]
    rintro _ ⟨z, rfl⟩
    change Spec (CommRingCat.of K) at z
    exact (congrArg e.left (Subsingleton.elim z (IsLocalRing.closedPoint K))).symm ▸ heU
  let a₀ := factorPointThroughOpen i e heRange
  have ha₀ : a₀ ≫ i = e := factorPointThroughOpen_comp i e heRange
  obtain ⟨a, ha⟩ := (affinePoint_bijective (K := K)).surjective a₀
  let f := twistedOrbitPoint G x i
  have hfx : a₀ ≫ f = x := by
    rw [← ha]
    change mapPoints (CommAlgCat.ofHom a) (twistedOrbitPoint G x i) = x
    rw [twistedOrbitPoint_naturality, show mapPoints (CommAlgCat.ofHom a) i = e from
      (congrArg (· ≫ i) ha).trans ha₀, twistedOrbitPoint_one]
  let aPoint := a₀.left (IsLocalRing.closedPoint K)
  have hfPoint : f.left aPoint = x.left (IsLocalRing.closedPoint K) :=
    congrArg (fun m : Points H.X (CommAlgCat.of K K) ↦ m.left (IsLocalRing.closedPoint K)) hfx
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := x.left (IsLocalRing.closedPoint K)) (by trivial)
  have haV : aPoint ∈ f.left ⁻¹ᵁ V := by
    change f.left aPoint ∈ V
    rwa [hfPoint]
  obtain ⟨W, hW, haW, hWV⟩ := exists_isAffineOpen_mem_and_subset haV
  obtain ⟨B, j, hj, hjR⟩ := exists_affine_point_range V hV
  obtain ⟨C, w, hw, hwR⟩ := exists_affine_point_range W hW
  let i' := w ≫ i
  let f' := twistedOrbitPoint G x i'
  let hFF : (testSpec K).FullyFaithful := algSpec.fullyFaithful
  obtain ⟨b, hb⟩ := hFF.map_surjective w
  have hf' : f' = w ≫ f := by
    dsimp only [f', i', f]
    rw [← hb]
    exact (twistedOrbitPoint_naturality G x b.unop i).symm
  have hRange : Set.range f'.left ⊆ Set.range j.left := by
    rw [hf', hjR]
    rintro y ⟨s, rfl⟩
    have hs : w.left s ∈ Set.range w.left := Set.mem_range_self s
    rw [hwR] at hs
    exact hWV hs
  let r := factorPointThroughOpen j f' hRange
  obtain ⟨β, hβ⟩ := (affinePoint_bijective (K := K)).surjective r
  have hβ' : affinePoint β ≫ j = f' :=
    (congrArg (· ≫ j) hβ).trans (factorPointThroughOpen_comp j f' hRange)
  have hio : IsOpenImmersion i'.left := inferInstanceAs (IsOpenImmersion (w.left ≫ i.left))
  have hic : Smooth ((testSpec K).obj (op C)).hom := by
    rw [← Over.w i']
    infer_instance
  have hjc : LocallyOfFiniteType ((testSpec K).obj (op B)).hom := by
    rw [← Over.w j]
    infer_instance
  have hcs : Algebra.Smooth K C := RingHom.smooth_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hic
  have hbs : Algebra.FiniteType K B := RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hjc
  have hBN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  have hft : LocallyOfFiniteType (affinePoint β).left := by
    let l := (affinePoint β).left
    let t := ((testSpec K).obj (op B)).hom
    have : LocallyOfFiniteType (l ≫ t) := by
      rw [show l ≫ t = ((testSpec K).obj (op C)).hom from Over.w (affinePoint β)]
      infer_instance
    exact locallyOfFiniteType_of_comp l t
  have het : Etale (affinePoint β).left := etale_affine_twistedOrbit G x i' j β hβ'
  have hfo : IsOpenMap f'.left := by
    rw [← hβ']
    exact j.left.isOpenMap.comp (affinePoint β).left.isOpenMap
  refine ⟨Set.range f'.left, hfo.isOpen_range, ?_, ?_⟩
  · have haR : aPoint ∈ Set.range w.left := hwR.symm ▸ haW
    obtain ⟨z, hz⟩ := haR
    refine ⟨z, ?_⟩
    rw [hf']
    exact (congrArg f.left hz).trans hfPoint
  · intro y hy
    obtain ⟨z, hz⟩ := point_in_range_of_closed_point f' y hy
    refine ⟨z ≫ i', ?_⟩
    obtain ⟨c, hc⟩ := (affinePoint_bijective (K := K)).surjective z
    rw [← hc]
    exact (twistedOrbitPoint_naturality G x (CommAlgCat.ofHom c) i').symm.trans
      ((congrArg (· ≫ f') hc).trans hz)

private theorem baseLang_surjective [IsAlgClosed K] (G : Specs.GroupScheme k) [Smooth G.X.hom]
    [ConnectedSpace ((groupBaseChange k K).obj G).X.left] :
    Function.Surjective (fun g : Points ((groupBaseChange k K).obj G).X (CommAlgCat.of K K) ↦
      baseFrobeniusOnPoints G (CommAlgCat.of K K) g * g⁻¹) := by
  classical
  let H := (groupBaseChange k K).obj G
  let P := Points H.X (CommAlgCat.of K K)
  let F := baseFrobeniusOnPoints G (CommAlgCat.of K K)
  let L : P → P := fun g ↦ F g * g⁻¹
  have hH : Smooth H.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom (fieldSpecMap k K)))
  have : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  let e := pointsClosedEquiv (K := K) H.X
  choose U hUo hUm hUr using exists_open_neighborhood_twistedOrbit (K := K) G
  have hL (x g : P) : twistedOrbitPoint G x g ∈ Set.range L ↔ x ∈ Set.range L := by
    have ht : twistedOrbitPoint G x g = F g * x * g⁻¹ := by
      have h : scalarHom (CommAlgCat.of K K) = 𝟙 _ := by ext
      simp [twistedOrbitPoint, h, mapPoints, F]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨g⁻¹ * a, ?_⟩
      change F (g⁻¹ * a) * (g⁻¹ * a)⁻¹ = x
      calc
        _ = (F g)⁻¹ * (F a * a⁻¹) * g := by rw [map_mul, map_inv, mul_inv_rev]; group
        _ = x := by
          rw [show F a * a⁻¹ = twistedOrbitPoint G x g from ha, ht]
          group
    · rintro ⟨a, rfl⟩
      use g * a
      change F (g * a) * (g * a)⁻¹ = _
      rw [ht, map_mul, mul_inv_rev]
      dsimp only [L]
      group
  let A : Set H.X.left := ⋃ x : P, ⋃ (_ : x ∈ Set.range L), U x
  let B : Set H.X.left := ⋃ x : P, ⋃ (_ : x ∉ Set.range L), U x
  have hao : IsOpen A := isOpen_iUnion fun x ↦ isOpen_iUnion fun _ ↦ hUo x
  have hbo : IsOpen B := isOpen_iUnion fun x ↦ isOpen_iUnion fun _ ↦ hUo x
  have hcA (x : P) : (e x).1 ∈ A ↔ x ∈ Set.range L := by
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hyL, hyU⟩ := Set.mem_iUnion.mp hy
      obtain ⟨g, rfl⟩ := hUr y x hyU
      exact (hL y g).mpr hyL
    · intro hx
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hUm x⟩⟩
  have hcB (x : P) : (e x).1 ∈ B ↔ x ∉ Set.range L := by
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hyL, hyU⟩ := Set.mem_iUnion.mp hy
      obtain ⟨g, rfl⟩ := hUr y x hyU
      exact fun hg ↦ hyL ((hL y g).mp hg)
    · intro hx
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hUm x⟩⟩
  have hd : Disjoint A B := by
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra h
    obtain ⟨y, ⟨hyA, hyB⟩, hyC⟩ := nonempty_inter_closedPoints
      (Set.nonempty_iff_ne_empty.mpr h) (hao.inter hbo).isLocallyClosed
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hyC⟩
    exact (hcB x).mp (hx.symm ▸ hyB) ((hcA x).mp (hx.symm ▸ hyA))
  have hcover : A ∪ B = Set.univ := by
    by_contra h
    obtain ⟨y, hy, hyC⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr h)
      (hao.union hbo).isClosed_compl.isLocallyClosed
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hyC⟩
    by_cases hxL : x ∈ Set.range L
    · have hmem := (hcA x).mpr hxL
      rw [hx] at hmem
      exact hy (Or.inl hmem)
    · have hmem := (hcB x).mpr hxL
      rw [hx] at hmem
      exact hy (Or.inr hmem)
  have hbCompl : B = Aᶜ := by
    ext y
    constructor
    · intro hb ha
      exact Set.disjoint_left.mp hd ha hb
    · intro ha
      have hy : y ∈ A ∪ B := hcover.symm ▸ Set.mem_univ _
      exact hy.resolve_left ha
  have hAc : IsClosed A := by
    apply isOpen_compl_iff.mp
    rwa [← hbCompl]
  have he : (1 : P) ∈ Set.range L := ⟨1, by simp [L]⟩
  have hA : A = Set.univ := IsClopen.eq_univ ⟨hAc, hao⟩ ⟨_, (hcA 1).mpr he⟩
  exact fun x ↦ (hcA x).mp (hA.symm ▸ Set.mem_univ _)

end ScalarExtensionFrobenius

private def testAlgebraIso {k : Type u} [Field k] (A B : TestAlgebra k)
    (e : A ≃+* B) (he : ∀ a : k, e (algebraMap k A a) = algebraMap k B a) : A ≅ B :=
  CommAlgCat.isoMk { toRingEquiv := e, commutes' := he }

theorem smoothLangSurjectivity : Specs.SmoothLangSurjectivity.{u} := by
  intro k _ _ G _ _ _
  let K := AlgebraicClosure k
  let R := CommAlgCat.of K K
  let R₀ := (restrictTestAlgebra k K).obj R
  let e := baseChangePointGroupEquiv K G R
  let i := testAlgebraIso R₀ (CommAlgCat.of k K) (RingEquiv.refl K) (fun _ ↦ rfl)
  let v := mapPointsMonoidHom G i.hom
  have : ConnectedSpace ((groupBaseChange k K).obj G).X.left :=
    smoothGroupGeometricConnectedness k G
  have h := baseLang_surjective (K := K) G
  intro x
  obtain ⟨p, hp⟩ := h (e.symm (mapPoints i.inv x))
  refine ⟨v (e p), ?_⟩
  have hF : e (baseFrobeniusOnPoints G R p) = frobeniusOnPoints _ (e p) :=
    baseChangePoint_baseFrobeniusOnPoints G R p
  have hR : v (e (baseFrobeniusOnPoints G R p * p⁻¹)) = x := by
    change baseFrobeniusOnPoints G R p * p⁻¹ = _ at hp
    rw [hp, e.apply_symm_apply]
    change mapPoints i.hom (mapPoints i.inv x) = x
    rw [mapPoints_comp_apply, Iso.inv_hom_id]
    simp [mapPoints]
  rw [map_mul, map_inv, hF, map_mul, map_inv] at hR
  unfold langOnGeometricPoints
  change frobeniusOnPoints _ (mapPoints i.hom (e p)) * (v (e p))⁻¹ = _
  rw [← frobeniusOnPoints_naturality]
  exact hR


end

end LinearAlgebraicGroups
