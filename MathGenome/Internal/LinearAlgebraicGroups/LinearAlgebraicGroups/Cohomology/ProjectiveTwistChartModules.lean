import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ProjectiveTwistChartModules
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.AlgebraicGeometry.AffineScheme

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open scoped BigOperators

universe u
noncomputable section

set_option Elab.async false

namespace LinearAlgebraicGroups.ProjectiveTwistChartModules

open Specs.ProjectiveSpaces
  (coordinateProjectiveSpace coordinateOpen coordinate_mem_degree_one grading constants)
open Specs.OrderedCechComparison (groundRingHom groundRingHomOpen)
open Specs.ProjectiveTwistChartModules

attribute [local instance] MvPolynomial.gradedAlgebra

section StandardIntersections

variable (k ι : Type u) [Field k]

private theorem intersectionOpen_isAffine (s : Finset ι) (hs : s.Nonempty) :
    IsAffineOpen (chartOpen k s) :=
  Proj.isAffineOpen_basicOpen (grading k ι) (coordinateProduct k ι s)
    (coordinateProduct_degree k ι s) (Finset.card_pos.mpr hs)

private def intersectionSectionsIso (s : Finset ι) (hs : s.Nonempty) :
    CommRingCat.of (Away (grading k ι) (coordinateProduct k ι s)) ≅
      Γ((coordinateProjectiveSpace k ι).left, chartOpen k s) :=
  Proj.basicOpenIsoAway (grading k ι) _ (coordinateProduct_degree k ι s) (Finset.card_pos.mpr hs)

set_option backward.isDefEq.respectTransparency false in
private theorem intersectionOpen_insert_eq_basicOpen [DecidableEq ι] {s : Finset ι}
    (hs : s.Nonempty) (j : ι) :
    chartOpen k (insert j s) = (coordinateProjectiveSpace k ι).left.basicOpen
      ((intersectionSectionsIso k ι s hs).hom (Away.isLocalizationElem
        (coordinateProduct_degree k ι s) (coordinate_mem_degree_one k ι j))) := by
  rw [chartOpen_eq_inf k ι (insert j s), Finset.inf_insert, ← chartOpen_eq_inf k ι s]
  let B := chartOpen k s
  let hB := intersectionOpen_isAffine k ι s hs
  let e := intersectionSectionsIso k ι s hs
  let a := Proj.basicOpenIsoSpec (grading k ι) _ (coordinateProduct_degree k ι s)
    (Finset.card_pos.mpr hs)
  let f := hB.fromSpec
  let g := Proj.awayι (grading k ι) _ (coordinateProduct_degree k ι s) (Finset.card_pos.mpr hs)
  let r := Away.isLocalizationElem (coordinateProduct_degree k ι s) (coordinate_mem_degree_one k ι j)
  have hcomp : Spec.map e.hom ≫ g = f := by
    change Spec.map e.hom ≫ a.inv ≫ B.ι = hB.isoSpec.inv ≫ B.ι
    rw [← Category.assoc]
    congr 1
    apply (cancel_mono a.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change Spec.map e.hom = hB.isoSpec.inv ≫ a.hom
    change _ = hB.isoSpec.inv ≫ B.toSpecΓ ≫ Spec.map e.hom
    rw [hB.isoSpec_inv_toSpecΓ_assoc]
  have hg := Proj.awayι_preimage_basicOpen (grading k ι) (coordinateProduct_degree k ι s)
    (Finset.card_pos.mpr hs) (coordinate_mem_degree_one k ι j) Nat.one_pos
  have hpre : f ⁻¹ᵁ coordinateOpen k ι j = PrimeSpectrum.basicOpen (e.hom r) := by
    rw [← hcomp, Scheme.Hom.comp_preimage]
    change (Spec.map e.hom) ⁻¹ᵁ (g ⁻¹ᵁ coordinateOpen k ι j) = _
    rw [show g ⁻¹ᵁ coordinateOpen k ι j = PrimeSpectrum.basicOpen r from hg]
    rfl
  change coordinateOpen k ι j ⊓ B = (coordinateProjectiveSpace k ι).left.basicOpen (e.hom r)
  rw [← hB.fromSpec_image_basicOpen, ← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf,
    hB.opensRange_fromSpec, inf_comm]

end StandardIntersections
section LaurentChartAlgebra

variable {k ι : Type u} [Field k] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem polynomialExponent_injective :
    Function.Injective (polynomialExponent (ι := ι)) := by
  intro a b h
  ext i
  exact Int.ofNat_inj.mp (congrFun h i)

omit [DecidableEq ι] in
private theorem polynomialToLaurent_injective :
    Function.Injective (polynomialToLaurent (k := k) (ι := ι)) :=
  AddMonoidAlgebra.mapDomain_injective polynomialExponent_injective

omit [DecidableEq ι] in
private theorem polynomialToLaurent_monomial (a : ι →₀ ℕ) (c : k) :
    polynomialToLaurent (MvPolynomial.monomial a c) =
      AddMonoidAlgebra.single (polynomialExponent a) c := by
  exact AddMonoidAlgebra.mapDomain_single

private theorem polynomialToLaurent_coordinateProduct (s : Finset ι) :
    polynomialToLaurent (coordinateProduct k ι s) =
      AddMonoidAlgebra.single (coordinateProductExponent s) 1 := by
  induction s using Finset.induction_on with
  | empty =>
    rw [show coordinateProductExponent (∅ : Finset ι) = 0 by
      funext i; simp [coordinateProductExponent]]
    rw [show coordinateProduct k ι (∅ : Finset ι) = 1 by simp [coordinateProduct],
      map_one, AddMonoidAlgebra.one_def]
  | @insert j s hj ih =>
    rw [coordinateProduct, Finset.prod_insert hj, map_mul]
    change polynomialToLaurent (MvPolynomial.monomial (Finsupp.single j 1) 1) *
      polynomialToLaurent (coordinateProduct k ι s) = _
    rw [polynomialToLaurent_monomial, ih, AddMonoidAlgebra.single_mul_single, mul_one]
    congr 1
    funext i
    by_cases hi : j = i
    · subst i
      simp [coordinateProductExponent, polynomialExponent, hj]
    · have h := Ne.symm hi
      simp [coordinateProductExponent, polynomialExponent, Finsupp.single_apply, hi, h]

omit [DecidableEq ι] in
private theorem isUnit_laurent_monomial (a : ι → ℤ) :
    IsUnit (AddMonoidAlgebra.single (R := k) a 1) := by
  apply IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-a) 1)
  simp [AddMonoidAlgebra.one_def]

private theorem isUnit_polynomialToLaurent_coordinateProduct (s : Finset ι) :
    IsUnit (polynomialToLaurent (coordinateProduct k ι s)) := by
  rw [polynomialToLaurent_coordinateProduct]
  exact isUnit_laurent_monomial _

private def localizedPolynomialToLaurent (s : Finset ι) :
    Localization.Away (coordinateProduct k ι s) →+* LaurentRing k ι :=
  IsLocalization.Away.lift (coordinateProduct k ι s)
    (g := polynomialToLaurent.toRingHom) (isUnit_polynomialToLaurent_coordinateProduct s)

private theorem localizedPolynomialToLaurent_algebraMap (s : Finset ι) (x : MvPolynomial ι k) :
    localizedPolynomialToLaurent s (algebraMap _ _ x) = polynomialToLaurent x :=
  IsLocalization.Away.lift_eq _ _ x

private theorem localizedPolynomialToLaurent_injective (s : Finset ι) :
    Function.Injective (localizedPolynomialToLaurent (k := k) s) := by
  unfold localizedPolynomialToLaurent IsLocalization.Away.lift
  apply (IsLocalization.lift_injective_iff _).mpr
  intro x y
  constructor
  · intro h
    exact ((localizedPolynomialToLaurent_algebraMap s x).symm.trans
      (congrArg (localizedPolynomialToLaurent s) h)).trans
      (localizedPolynomialToLaurent_algebraMap s y)
  · intro h
    rw [polynomialToLaurent_injective h]

private def chartToLaurent (s : Finset ι) :
    Away (grading k ι) (coordinateProduct k ι s) →+* LaurentRing k ι :=
  (localizedPolynomialToLaurent s).comp (algebraMap _ _)

private theorem chartToLaurent_injective (s : Finset ι) :
    Function.Injective (chartToLaurent (k := k) s) :=
  (localizedPolynomialToLaurent_injective s).comp (HomogeneousLocalization.val_injective _)

private theorem chartToLaurent_mk (s : Finset ι) {d : ℕ}
    (hdeg : coordinateProduct k ι s ∈ grading k ι d) (n : ℕ) (p : MvPolynomial ι k)
    (hp : p ∈ grading k ι (n • d)) :
    chartToLaurent s (Away.mk _ hdeg n p hp) =
      polynomialToLaurent p *
        AddMonoidAlgebra.single (-(n • coordinateProductExponent s)) 1 := by
  change localizedPolynomialToLaurent s
    ((Away.mk _ hdeg n p hp).val) = _
  rw [Away.val_mk, Localization.mk_eq_mk']
  unfold localizedPolynomialToLaurent IsLocalization.Away.lift
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  change polynomialToLaurent p =
    polynomialToLaurent (coordinateProduct k ι s ^ n) *
      (polynomialToLaurent p * AddMonoidAlgebra.single (-(n • coordinateProductExponent s)) 1)
  rw [map_pow, polynomialToLaurent_coordinateProduct, AddMonoidAlgebra.single_pow]
  rw [mul_left_comm, AddMonoidAlgebra.single_mul_single]
  simp [← AddMonoidAlgebra.one_def]

variable [Fintype ι]

private theorem sum_coordinateProductExponent (s : Finset ι) :
    (∑ i, coordinateProductExponent s i) = s.card := by
  simp [coordinateProductExponent, Finset.sum_ite_mem]

omit [DecidableEq ι] in
private theorem sum_polynomialExponent (a : ι →₀ ℕ) :
    (∑ i, polynomialExponent a i) = a.degree := by
  simp [polynomialExponent, Finsupp.degree_eq_sum]

private theorem sum_nsmul_coordinateProductExponent (n : ℕ) (s : Finset ι) :
    (∑ i, (n • coordinateProductExponent s) i) = (n : ℤ) * s.card := by
  change (∑ i, n • coordinateProductExponent s i) = _
  rw [← Finset.smul_sum, sum_coordinateProductExponent, nsmul_eq_mul]

private def isChartExponent (s : Finset ι) (a : ι → ℤ) : Prop :=
  (∑ i, a i) = 0 ∧ ∀ i ∉ s, 0 ≤ a i

private theorem isChartExponent_of_polynomial_fraction (s : Finset ι)
    (n : ℕ) (a : ι →₀ ℕ) (ha : a.degree = n * s.card) :
    isChartExponent s (polynomialExponent a - n • coordinateProductExponent s) := by
  constructor
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_polynomialExponent,
      sum_nsmul_coordinateProductExponent, ha, Nat.cast_mul, sub_self]
  · intro i hi
    simp [coordinateProductExponent, polynomialExponent, hi]

private theorem chartToLaurent_support (s : Finset ι)
    (x : Away (grading k ι) (coordinateProduct k ι s))
    (a : ι → ℤ) (ha : a ∈ (chartToLaurent s x).coeff.support) :
    isChartExponent s a := by
  classical
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (coordinateProduct_degree k ι s) x
  rw [chartToLaurent_mk] at ha
  have he : polynomialToLaurent p * AddMonoidAlgebra.single (-(n • coordinateProductExponent s)) 1 =
      ∑ b ∈ p.support, AddMonoidAlgebra.single (polynomialExponent b - n • coordinateProductExponent s)
        (p.coeff b) := by
    conv_lhs => rw [p.as_sum, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [polynomialToLaurent_monomial, AddMonoidAlgebra.single_mul_single, mul_one, sub_eq_add_neg]
  rw [he, Finsupp.mem_support_iff] at ha
  by_contra hn
  apply ha
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single]
  apply Finset.sum_eq_zero
  intro b hb
  have hdeg : b.degree = n * s.card := by
    have h := hp (MvPolynomial.mem_support_iff.mp hb)
    rw [Finsupp.degree_eq_weight_one]
    rw [show (1 : ι → ℕ) = (fun _ => 1) by funext i; exact Pi.one_apply i] at h
    simpa [nsmul_eq_mul] using h
  have h := isChartExponent_of_polynomial_fraction s n b hdeg
  have hb' : polynomialExponent b - n • coordinateProductExponent s ≠ a :=
    fun eq => hn (eq ▸ h)
  exact Finsupp.single_eq_of_ne hb'.symm

private theorem single_mem_range_chartToLaurent (s : Finset ι) (a : ι → ℤ) (ha : isChartExponent s a)
    (c : k) : AddMonoidAlgebra.single a c ∈ (chartToLaurent (k := k) s).range := by
  classical
  let n := ∑ i, (a i).natAbs
  let q := a + n • coordinateProductExponent s
  have hq (i : ι) : 0 ≤ q i := by
    by_cases hi : i ∈ s
    · have hn : (a i).natAbs ≤ n :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (a j).natAbs) (Finset.mem_univ i)
      have hb : -(↑(a i).natAbs : ℤ) ≤ a i := by omega
      have hqi : q i = a i + (n : ℤ) := by
        simp [q, coordinateProductExponent, hi, nsmul_eq_mul]
      omega
    · simpa [q, coordinateProductExponent, hi] using ha.2 i hi
  let b : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (q i).toNat)
  have hb : polynomialExponent b = q := by
    funext i
    change ((b i : ℕ) : ℤ) = q i
    change ((Finsupp.equivFunOnFinite b i : ℕ) : ℤ) = q i
    rw [show Finsupp.equivFunOnFinite b = (fun j => (q j).toNat) from
      Finsupp.equivFunOnFinite.apply_symm_apply _]
    exact Int.toNat_of_nonneg (hq i)
  have hd : b.degree = n * s.card := by
    apply Int.ofNat_inj.mp
    rw [← sum_polynomialExponent, hb, Nat.cast_mul]
    simp only [q, Pi.add_apply, Finset.sum_add_distrib, sum_nsmul_coordinateProductExponent,
      ha.1, zero_add]
  have hm : MvPolynomial.monomial b c ∈ grading k ι (n • s.card) :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_monomial c hd)
  refine ⟨Away.mk _ (coordinateProduct_degree k ι s) n (MvPolynomial.monomial b c) hm, ?_⟩
  rw [chartToLaurent_mk, polynomialToLaurent_monomial, AddMonoidAlgebra.single_mul_single, mul_one,
    hb]
  simp [q]

private theorem chartToLaurent_range (s : Finset ι) (x : LaurentRing k ι) :
    x ∈ (chartToLaurent (k := k) s).range ↔ ∀ a ∈ x.coeff.support, isChartExponent s a := by
  constructor
  · rintro ⟨y, rfl⟩ a ha
    exact chartToLaurent_support s y a ha
  · intro h
    rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
    exact (chartToLaurent (k := k) s).range.sum_mem
      (fun a ha => single_mem_range_chartToLaurent s a (h a ha) (x.coeff a))

end LaurentChartAlgebra

section LaurentChartRestrictions

variable {k ι : Type u} [Field k] [DecidableEq ι]

private theorem coordinateProduct_eq_mul_of_subset {s t : Finset ι} (hst : s ⊆ t) :
    coordinateProduct k ι t = coordinateProduct k ι s * coordinateProduct k ι (t \ s) := by
  unfold coordinateProduct
  rw [mul_comm, Finset.prod_sdiff hst]

private theorem coordinateProductExponent_eq_add_of_subset {s t : Finset ι} (hst : s ⊆ t) :
    coordinateProductExponent t = coordinateProductExponent s + coordinateProductExponent (t \ s) := by
  funext i
  by_cases hi : i ∈ s
  · simp [coordinateProductExponent, hi, hst hi]
  · simp [coordinateProductExponent, hi]

/-- The restriction between degree-zero homogeneous localizations indexed by
two nested sets of inverted coordinates. -/
private def chartRestriction {s t : Finset ι} (hst : s ⊆ t) :
    Away (grading k ι) (coordinateProduct k ι s) →+*
      Away (grading k ι) (coordinateProduct k ι t) :=
  awayMap (grading k ι) (coordinateProduct_degree k ι (t \ s))
    (coordinateProduct_eq_mul_of_subset hst)

/-- In the Laurent algebra the restriction maps keep each integer exponent
vector and its coefficient. -/
private theorem chartToLaurent_chartRestriction {s t : Finset ι} (hst : s ⊆ t)
    (a : Away (grading k ι) (coordinateProduct k ι s)) :
    chartToLaurent t (chartRestriction hst a) = chartToLaurent s a := by
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (coordinateProduct_degree k ι s) a
  rw [chartRestriction, awayMap_mk, chartToLaurent_mk, chartToLaurent_mk,
    map_mul, map_pow, polynomialToLaurent_coordinateProduct, AddMonoidAlgebra.single_pow,
    mul_assoc, AddMonoidAlgebra.single_mul_single, one_pow, mul_one]
  congr 2
  rw [coordinateProductExponent_eq_add_of_subset hst, smul_add]
  abel

private theorem intersectionOpen_anti {s t : Finset ι} (h : s ⊆ t) :
    chartOpen k t ≤ chartOpen k s :=
  Proj.basicOpen_mono _ _ _ ⟨_, coordinateProduct_eq_mul_of_subset h⟩

private def sectionsToLaurent (s : Finset ι) (hs : s.Nonempty) :
    Γ((coordinateProjectiveSpace k ι).left, chartOpen k s) →+* LaurentRing k ι :=
  (chartToLaurent s).comp (intersectionSectionsIso k ι s hs).inv.hom

private theorem sectionsToLaurent_injective (s : Finset ι) (hs : s.Nonempty) :
    Function.Injective (sectionsToLaurent (k := k) s hs) :=
  (chartToLaurent_injective s).comp
    (ConcreteCategory.bijective_of_isIso (intersectionSectionsIso k ι s hs).inv).1

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsToLaurent_restriction {s t : Finset ι} (h : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (a : Γ((coordinateProjectiveSpace k ι).left, chartOpen k s)) :
    sectionsToLaurent t ht (((coordinateProjectiveSpace k ι).left.presheaf.map
      (homOfLE (intersectionOpen_anti h)).op) a) = sectionsToLaurent s hs a := by
  let e := intersectionSectionsIso k ι s hs
  let f := intersectionSectionsIso k ι t ht
  let i := (coordinateProjectiveSpace k ι).left.presheaf.map
    (homOfLE (intersectionOpen_anti (k := k) h)).op
  have hcomm : CommRingCat.ofHom (chartRestriction (k := k) h) ≫ f.hom = e.hom ≫ i := by
    exact Proj.awayMap_awayToSection (grading k ι) (coordinateProduct_degree k ι (t \ s))
      (coordinateProduct_eq_mul_of_subset h)
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 a
  have hh := ConcreteCategory.congr_hom hcomm b
  change chartToLaurent t (f.inv (i (e.hom b))) = chartToLaurent s (e.inv (e.hom b))
  rw [show i (e.hom b) = f.hom (chartRestriction h b) from hh.symm,
    Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]
  exact chartToLaurent_chartRestriction h b

end LaurentChartRestrictions

section ProjectiveRatios

variable {k ι : Type u} [Field k] [DecidableEq ι] [Fintype ι]

private theorem sectionsToLaurent_range (s : Finset ι) (hs : s.Nonempty) (l : LaurentRing k ι) :
    l ∈ (sectionsToLaurent (k := k) s hs).range ↔ ∀ a ∈ l.coeff.support, isChartExponent s a := by
  rw [← chartToLaurent_range s l]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(intersectionSectionsIso k ι s hs).inv x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (intersectionSectionsIso k ι s hs).inv).2 x
    exact ⟨y, rfl⟩

private theorem exists_section_laurentMonomial (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℤ) (ha : isChartExponent s a) :
    ∃ x, sectionsToLaurent (k := k) s hs x = AddMonoidAlgebra.single a 1 := by
  apply (sectionsToLaurent_range s hs _).mpr
  intro b hb
  have hb' : b = a := Finset.mem_singleton.mp (Finsupp.support_single_subset hb)
  rwa [hb']

private def ratioExponent (i j : ι) : ι → ℤ :=
  coordinateProductExponent {i} - coordinateProductExponent {j}

private theorem isChartExponent_ratio (s : Finset ι) (i j : ι) (hj : j ∈ s) :
    isChartExponent s (ratioExponent i j) := by
  constructor
  · simp [ratioExponent, Finset.sum_sub_distrib, sum_coordinateProductExponent]
  · intro z hz
    have hne : z ≠ j := fun e => hz (e ▸ hj)
    simp [ratioExponent, coordinateProductExponent, hne, Finset.mem_singleton]
    split <;> omega

private def ratioSection (s : Finset ι) (hs : s.Nonempty) (i j : ι) (hj : j ∈ s) :
    Γ((coordinateProjectiveSpace k ι).left, chartOpen k s) :=
  (exists_section_laurentMonomial s hs _ (isChartExponent_ratio s i j hj)).choose

@[simp] private theorem sectionsToLaurent_ratioSection (s : Finset ι) (hs : s.Nonempty)
    (i j : ι) (hj : j ∈ s) :
    sectionsToLaurent (k := k) s hs (ratioSection s hs i j hj) =
      AddMonoidAlgebra.single (ratioExponent i j) 1 :=
  (exists_section_laurentMonomial s hs _ (isChartExponent_ratio s i j hj)).choose_spec

private theorem ratioSection_self (s : Finset ι) (hs : s.Nonempty) (j : ι) (hj : j ∈ s) :
    ratioSection (k := k) s hs j j hj = 1 := by
  apply sectionsToLaurent_injective s hs
  rw [sectionsToLaurent_ratioSection, map_one, ratioExponent, sub_self, AddMonoidAlgebra.one_def]

private theorem ratioSection_mul (s : Finset ι) (hs : s.Nonempty) {i j l : ι}
    (hj : j ∈ s) (hl : l ∈ s) :
    ratioSection (k := k) s hs i j hj * ratioSection s hs j l hl = ratioSection s hs i l hl := by
  apply sectionsToLaurent_injective s hs
  simp only [map_mul, sectionsToLaurent_ratioSection, AddMonoidAlgebra.single_mul_single,
    mul_one]
  congr 1
  unfold ratioExponent
  abel

private theorem ratioSection_restriction {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty)
    (ht : t.Nonempty) (i j : ι) (hj : j ∈ s) :
    ((coordinateProjectiveSpace k ι).left.presheaf.map (homOfLE (intersectionOpen_anti h)).op)
      (ratioSection s hs i j hj) = ratioSection t ht i j (h hj) := by
  apply sectionsToLaurent_injective t ht
  rw [sectionsToLaurent_restriction h hs ht, sectionsToLaurent_ratioSection,
    sectionsToLaurent_ratioSection]

private def chartDenominator (s : Finset ι) (hs : s.Nonempty) (i : ι) :
    Γ((coordinateProjectiveSpace k ι).left, chartOpen k s) :=
  (intersectionSectionsIso k ι s hs).hom (Away.isLocalizationElem
    (coordinateProduct_degree k ι s) (coordinate_mem_degree_one k ι i))

omit [Fintype ι] in
private theorem sectionsToLaurent_chartDenominator (s : Finset ι) (hs : s.Nonempty) (i : ι) :
    sectionsToLaurent (k := k) s hs (chartDenominator s hs i) =
      AddMonoidAlgebra.single (s.card • coordinateProductExponent {i} - coordinateProductExponent s)
        1 := by
  change chartToLaurent s ((intersectionSectionsIso k ι s hs).inv
    ((intersectionSectionsIso k ι s hs).hom (Away.isLocalizationElem _ _))) = _
  rw [Iso.hom_inv_id_apply]
  unfold Away.isLocalizationElem
  have hi : polynomialToLaurent (MvPolynomial.X i : MvPolynomial ι k) =
      AddMonoidAlgebra.single (coordinateProductExponent {i}) 1 := by
    simpa [coordinateProduct] using polynomialToLaurent_coordinateProduct (k := k) ({i} : Finset ι)
  rw [chartToLaurent_mk, map_pow, hi, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single,
    one_nsmul, one_pow, mul_one, sub_eq_add_neg]

private theorem isUnit_chartDenominator (s : Finset ι) (hs : s.Nonempty) (j : ι) (hj : j ∈ s) :
    IsUnit (chartDenominator (k := k) s hs j) := by
  let a := coordinateProductExponent s - s.card • coordinateProductExponent {j}
  have ha : isChartExponent s a := by
    constructor
    · change (∑ i, (coordinateProductExponent s - s.card • coordinateProductExponent {j}) i) = 0
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_nsmul_coordinateProductExponent,
        sum_coordinateProductExponent, Finset.card_singleton, Nat.cast_one, mul_one, sub_self]
    · intro i hi
      have hne : i ≠ j := fun e => hi (e ▸ hj)
      simp [a, coordinateProductExponent, hi, hne]
  obtain ⟨x, hx⟩ := exists_section_laurentMonomial (k := k) s hs a ha
  apply IsUnit.of_mul_eq_one x
  apply sectionsToLaurent_injective s hs
  rw [map_mul, sectionsToLaurent_chartDenominator, hx, AddMonoidAlgebra.single_mul_single,
    mul_one, map_one, AddMonoidAlgebra.one_def]
  congr 1
  dsimp [a]
  abel

private theorem chartDenominator_eq_mul (s : Finset ι) (hs : s.Nonempty) (i j : ι) (hj : j ∈ s) :
    chartDenominator (k := k) s hs i = chartDenominator s hs j * ratioSection s hs i j hj ^ s.card := by
  apply sectionsToLaurent_injective s hs
  simp only [map_mul, map_pow, sectionsToLaurent_chartDenominator, sectionsToLaurent_ratioSection,
    AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single, one_pow, mul_one]
  congr 1
  unfold ratioExponent
  rw [smul_sub]
  abel

/-- Adjoining a projective coordinate is the principal open defined by its
ratio to any already inverted coordinate. -/
private theorem intersectionOpen_insert_eq_ratio {s : Finset ι} (hs : s.Nonempty)
    (i j : ι) (hj : j ∈ s) :
    chartOpen k (insert i s) =
      (coordinateProjectiveSpace k ι).left.basicOpen (ratioSection s hs i j hj) := by
  have h := intersectionOpen_insert_eq_basicOpen k ι hs i
  change chartOpen k (insert i s) =
    (coordinateProjectiveSpace k ι).left.basicOpen (chartDenominator s hs i) at h
  rw [h, chartDenominator_eq_mul s hs i j hj, Scheme.basicOpen_mul,
    Scheme.basicOpen_of_isUnit _ (isUnit_chartDenominator s hs j hj),
    Scheme.basicOpen_pow _ _ (Finset.card_pos.mpr hs)]
  exact inf_eq_right.mpr (Scheme.basicOpen_le _ _)

end ProjectiveRatios


section ChartGeometry
variable {k ι : Type u} [Field k] [DecidableEq ι] [Fintype ι]

set_option backward.isDefEq.respectTransparency false in
private theorem specMap_intersectionSectionsIso_away (S : ChartIndex ι) :
    Spec.map (intersectionSectionsIso k ι S.val S.property).hom ≫
      Proj.awayι (grading k ι) _ (coordinateProduct_degree k ι S.val)
        (Finset.card_pos.mpr S.property) =
      (intersectionOpen_isAffine k ι S.val S.property).fromSpec := by
  let B := chartOpen k S.val
  let hB := intersectionOpen_isAffine k ι S.val S.property
  let e := intersectionSectionsIso k ι S.val S.property
  let a := Proj.basicOpenIsoSpec (grading k ι) _ (coordinateProduct_degree k ι S.val)
    (Finset.card_pos.mpr S.property)
  change Spec.map e.hom ≫ a.inv ≫ B.ι = hB.isoSpec.inv ≫ B.ι
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono a.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ = hB.isoSpec.inv ≫ B.toSpecΓ ≫ Spec.map e.hom
  rw [hB.isoSpec_inv_toSpecΓ_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem chartGround_eq (S : ChartIndex ι) :
    (intersectionSectionsIso k ι S.val S.property).inv.hom.comp (chartGround k S) =
      (fromZeroRingHom (grading k ι) (Submonoid.powers (coordinateProduct k ι S.val))).comp (constants k ι) := by
  let X := coordinateProjectiveSpace k ι
  let e := intersectionSectionsIso k ι S.val S.property
  let a := Proj.awayι (grading k ι) _ (coordinateProduct_degree k ι S.val)
    (Finset.card_pos.mpr S.property)
  let hB := intersectionOpen_isAffine k ι S.val S.property
  let c := CommRingCat.ofHom (constants k ι)
  let f := CommRingCat.ofHom (fromZeroRingHom (grading k ι) (Submonoid.powers (coordinateProduct k ι S.val)))
  let b := CommRingCat.ofHom (chartGround k S)
  have hstruct : X.hom = X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (groundRingHom X)) := by
    change X.hom = X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso _).inv ≫ X.hom.appTop)
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hleft : hB.fromSpec ≫ X.hom = Spec.map b := by
    rw [hstruct, ← Category.assoc, hB.fromSpec_toSpecΓ, ← Spec.map_comp]
    rfl
  have hright : hB.fromSpec ≫ X.hom = Spec.map ((c ≫ f) ≫ e.hom) := by
    rw [← specMap_intersectionSectionsIso_away (k := k) S, Category.assoc]
    change Spec.map e.hom ≫ a ≫ (Proj.toSpecZero (grading k ι) ≫ Spec.map c) = _
    rw [← Category.assoc a, Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  have h : b = (c ≫ f) ≫ e.hom := Spec.map_injective (hleft.symm.trans hright)
  change (b ≫ e.inv).hom = (c ≫ f).hom
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
private theorem sectionsToLaurent_constants (S : ChartIndex ι) (r : k) :
    sectionsToLaurent S.val S.property (chartGround k S r) = AddMonoidAlgebra.single 0 r := by
  change chartToLaurent S.val
    (((intersectionSectionsIso k ι S.val S.property).inv.hom.comp (chartGround k S)) r) = _
  rw [chartGround_eq]
  let p : MvPolynomial ι k := MvPolynomial.C r
  have hp : p ∈ grading k ι (0 • S.val.card) := by
    rw [zero_smul]
    exact MvPolynomial.isHomogeneous_C ι r
  have hf : fromZeroRingHom (grading k ι) (Submonoid.powers (coordinateProduct k ι S.val))
      (constants k ι r) = Away.mk _ (coordinateProduct_degree k ι S.val) 0 p hp := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk]
    change Localization.mk p (1 : Submonoid.powers (coordinateProduct k ι S.val)) =
      Localization.mk p _
    exact congrArg (Localization.mk p) (Subtype.ext (pow_zero _).symm)
  change chartToLaurent S.val (fromZeroRingHom _ _ (constants k ι r)) = _
  rw [hf, chartToLaurent_mk, zero_smul, neg_zero, ← AddMonoidAlgebra.one_def, mul_one]
  exact (polynomialToLaurent (k := k) (ι := ι)).commutes r

private theorem ratioExponent_eq (i j : ι) :
    ratioExponent i j = Specs.ProjectiveTwistChartModules.ratioExponent i j := by
  ext l
  simp [ratioExponent, Specs.ProjectiveTwistChartModules.ratioExponent, coordinateExponent,
    coordinateProductExponent]

set_option backward.isDefEq.respectTransparency false in
/-- Regular sections on the actual projective intersections, with their restriction and ratio laws. -/
def chartGeometry : ChartGeometry k ι where
  affine S := intersectionOpen_isAffine k ι S.val S.property
  embed S := sectionsToLaurent S.val S.property
  injective S := sectionsToLaurent_injective S.val S.property
  range S x := sectionsToLaurent_range S.val S.property x
  fraction_coeff S n p hp := by
    let e := intersectionSectionsIso k ι S.val S.property
    change chartToLaurent S.val (e.inv (e.hom _)) = _
    rw [Iso.hom_inv_id_apply]
    exact chartToLaurent_mk S.val (coordinateProduct_degree k ι S.val) n p hp
  constants := sectionsToLaurent_constants
  restrict_embed h r := sectionsToLaurent_restriction (indexSubset h) _ _ r
  ratio S i j hj := ratioSection S.val S.property i j hj
  ratio_coeff S i j hj := by
    rw [sectionsToLaurent_ratioSection, ratioExponent_eq]
  ratio_self S := ratioSection_self S.val S.property
  ratio_mul S _ _ _ := ratioSection_mul S.val S.property
  ratio_restrict h := ratioSection_restriction (indexSubset h) _ _
  insert_open S := intersectionOpen_insert_eq_ratio S.property
  ring_localization S i j hj := by
    exact (intersectionOpen_isAffine k ι S.val S.property).isLocalization_of_eq_basicOpen
      (ratioSection S.val S.property i j hj) (homOfLE (chartOpen_anti (indexSubset (insertHom i S))))
      (intersectionOpen_insert_eq_ratio S.property i j hj)

theorem chartGeometryExists : ChartGeometryExists.{u} := by
  intro k ι _ _ _ _
  exact ⟨chartGeometry⟩

end ChartGeometry

section TwistModules

set_option backward.isDefEq.respectTransparency false

variable {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]

private theorem allowed_add {S : Set ι} {d e : ℤ} {a b : ι → ℤ}
    (ha : a ∈ allowed d S) (hb : b ∈ allowed e S) : a + b ∈ allowed (d + e) S :=
  ⟨by simp [Finset.sum_add_distrib, ha.1, hb.1],
    fun i hi => add_nonneg (ha.2 i hi) (hb.2 i hi)⟩

private theorem laurentPart_mono {S T : Set ι} (d : ℤ) (h : S ⊆ T) :
    LaurentPart k d S ≤ LaurentPart k d T :=
  AddMonoidAlgebra.supported_mono fun _ ha => ⟨ha.1, fun i hi => ha.2 i (fun h' => hi (h h'))⟩

private theorem mul_mem_laurentPart {S : Set ι} {d e : ℤ} {x y : LaurentRing k ι}
    (hx : x ∈ LaurentPart k d S) (hy : y ∈ LaurentPart k e S) :
    x * y ∈ LaurentPart k (d + e) S := by
  classical
  apply AddMonoidAlgebra.mem_supported'.mpr
  intro a ha
  rw [AddMonoidAlgebra.coeff_mul]
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro c hc
  have h : b + c ≠ a := fun he => ha (he ▸ allowed_add (hx hb) (hy hc))
  exact ite_eq_right h

private theorem single_mem_laurentPart {S : Set ι} {d : ℤ} {a : ι → ℤ}
    (ha : a ∈ allowed d S) (r : k) : AddMonoidAlgebra.single a r ∈ LaurentPart k d S := by
  apply AddMonoidAlgebra.mem_supported.mpr
  intro b hb
  have h : b = a := Finset.mem_singleton.mp (Finsupp.support_single_subset hb)
  exact h.symm ▸ ha

private theorem powerExponent_allowed {S : Set ι} (d : ℤ) {i : ι} (hi : i ∈ S) :
    powerExponent d i ∈ allowed d S := by
  refine ⟨?_, fun j hj => ?_⟩
  · simp [powerExponent, coordinateExponent, Pi.smul_apply, zsmul_eq_mul, mul_ite]
  · simp [powerExponent, coordinateExponent, Pi.smul_apply, show j ≠ i from fun h => hj (h ▸ hi)]

private abbrev powerMonomial (d : ℤ) (i : ι) : LaurentRing k ι :=
  AddMonoidAlgebra.single (powerExponent d i) 1

private theorem powerMonomial_mul_neg (d : ℤ) (i : ι) :
    powerMonomial (k := k) d i * powerMonomial (-d) i = 1 := by
  rw [AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.one_def]
  simp [powerExponent, neg_smul]

private theorem scaled_chart_mem (G : ChartGeometry k ι) (S : ChartIndex ι) (d : ℤ)
    (r : ChartRing k S) {x : LaurentRing k ι} (hx : x ∈ LaurentPart k d (S.val : Set ι)) :
    G.embed S r * x ∈ LaurentPart k d (S.val : Set ι) := by
  simpa only [zero_add] using
    mul_mem_laurentPart ((G.range S _).mp ⟨r, rfl⟩) hx

private def chartPart (G : ChartGeometry k ι) (d : ℤ) (S : ChartIndex ι) :
    @Submodule (ChartRing k S) (LaurentRing k ι) _ _ (G.embed S).toModule :=
  letI := (G.embed S).toModule
  { carrier := LaurentPart k d (S.val : Set ι)
    zero_mem' := (LaurentPart k d (S.val : Set ι)).zero_mem
    add_mem' := (LaurentPart k d (S.val : Set ι)).add_mem
    smul_mem' := scaled_chart_mem G S d }

private abbrev twistModule (G : ChartGeometry k ι) (d : ℤ) (S : ChartIndex ι) :
    ModuleCat.{u} (ChartRing k S) :=
  letI := (G.embed S).toModule
  ModuleCat.of (ChartRing k S) (chartPart G d S)

private def twistRestriction (G : ChartGeometry k ι) (d : ℤ)
    {S T : (ChartIndex ι)ᵒᵈᵒᵖ} (h : S ⟶ T) :
    twistModule G d (indexOf S) ⟶
      (ModuleCat.restrictScalars ((chartRings k ι).map h).hom).obj (twistModule G d (indexOf T)) :=
  ModuleCat.ofHom (X := twistModule G d (indexOf S))
    (Y := (ModuleCat.restrictScalars ((chartRings k ι).map h).hom).obj
      (twistModule G d (indexOf T))) {
    toFun x := ⟨x.val, laurentPart_mono d (indexSubset h) x.property⟩
    map_add' _ _ := rfl
    map_smul' r x := Subtype.ext (by
      change G.embed (indexOf S) r * x.val =
        G.embed (indexOf T) ((chartRings k ι).map h r) * x.val
      rw [G.restrict_embed h r]) }

private def twistModules (G : ChartGeometry k ι) (d : ℤ) :
    PresheafOfModules.{u} (chartRingPresheaf k ι) where
  obj S := twistModule G d (indexOf S)
  map := twistRestriction G d
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

private def twistCoefficients (G : ChartGeometry k ι) (d : ℤ) (S : ChartIndex ι) :
    twistModule G d S ≃+ LaurentPart k d (S.val : Set ι) where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def twistBasis (G : ChartGeometry k ι) (d : ℤ) (S : ChartIndex ι)
    (i : ι) (hi : i ∈ S.val) :
    ChartRing k S ≃ₗ[ChartRing k S] twistModule G d S := by
  let f : ChartRing k S →ₗ[ChartRing k S] twistModule G d S :=
    { toFun r := ⟨G.embed S r * powerMonomial d i, scaled_chart_mem G S d r
        (single_mem_laurentPart (powerExponent_allowed d hi) 1)⟩
      map_add' r s := Subtype.ext (by change G.embed S (r + s) * _ = _; rw [map_add, add_mul]; rfl)
      map_smul' r s := Subtype.ext (by
        change G.embed S (r * s) * _ = G.embed S r * (G.embed S s * _)
        rw [map_mul, mul_assoc]) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro r s h
    apply G.injective S
    have h' : G.embed S r * powerMonomial d i = G.embed S s * powerMonomial d i :=
      congrArg Subtype.val h
    simpa only [mul_assoc, powerMonomial_mul_neg, mul_one] using
      congrArg (fun x => x * powerMonomial (-d) i) h'
  · intro x
    have hm := mul_mem_laurentPart x.property
      (single_mem_laurentPart (powerExponent_allowed (-d) hi) (1 : k))
    rw [add_neg_cancel] at hm
    obtain ⟨r, hr⟩ := (G.range S _).mpr hm
    refine ⟨r, Subtype.ext ?_⟩
    change G.embed S r * powerMonomial d i = x.val
    rw [hr, mul_assoc]
    change x.val * (powerMonomial (-d) i * powerMonomial d i) = x.val
    rw [mul_comm (powerMonomial (-d) i), powerMonomial_mul_neg, mul_one]

private theorem twistBasis_val (G : ChartGeometry k ι) (d : ℤ) (S : ChartIndex ι)
    (i : ι) (hi : i ∈ S.val) (r : ChartRing k S) :
    (twistBasis G d S i hi r).val = G.embed S r * powerMonomial d i := rfl

private theorem embed_ratioUnit_zpow (G : ChartGeometry k ι) (S : ChartIndex ι)
    (i j : ι) (hi : i ∈ S.val) (hj : j ∈ S.val) (d : ℤ) :
    G.embed S ((G.ratioUnit S i j hi hj ^ d : (ChartRing k S)ˣ) : ChartRing k S) =
      AddMonoidAlgebra.single (d • Specs.ProjectiveTwistChartModules.ratioExponent i j) 1 := by
  let f := (AddMonoidAlgebra.of k (ι → ℤ)).toHomUnits
  let g := Units.map (G.embed S).toMonoidHom
  let v := Multiplicative.ofAdd (Specs.ProjectiveTwistChartModules.ratioExponent i j)
  have h : g (G.ratioUnit S i j hi hj) = f v := Units.ext (G.ratio_coeff S i j hj)
  change (g (G.ratioUnit S i j hi hj ^ d) : LaurentRing k ι) = (f (v ^ d) : LaurentRing k ι)
  rw [map_zpow, map_zpow, h]

private theorem twistBasis_transition (G : ChartGeometry k ι) (d : ℤ) (S : ChartIndex ι)
    (i j : ι) (hi : i ∈ S.val) (hj : j ∈ S.val) :
    twistBasis G d S i hi 1 =
      ((G.ratioUnit S i j hi hj ^ d : (ChartRing k S)ˣ) : ChartRing k S) • twistBasis G d S j hj 1 := by
  apply Subtype.ext
  change (twistBasis G d S i hi 1).val =
    G.embed S _ * (twistBasis G d S j hj 1).val
  rw [twistBasis_val, twistBasis_val, map_one, one_mul, one_mul, embed_ratioUnit_zpow,
    AddMonoidAlgebra.single_mul_single, mul_one]
  have he : d • Specs.ProjectiveTwistChartModules.ratioExponent i j + powerExponent d j =
      powerExponent d i := by
    simp [powerExponent, Specs.ProjectiveTwistChartModules.ratioExponent, smul_sub]
  rw [he]


private theorem twistModules_localized (G : ChartGeometry k ι) (d : ℤ)
    (S : ChartIndex ι) (i j : ι) (hj : j ∈ S.val) :
    localizesAt (twistModules G d) S i (G.ratio S i j hj) := by
  let T := insertIndex i S
  let h := insertHom i S
  let ρ : ChartRing k S →+* ChartRing k T := ((chartRings k ι).map h).hom
  letI : Algebra (ChartRing k S) (ChartRing k T) := ρ.toAlgebra
  letI : IsLocalization.Away (G.ratio S i j hj) (ChartRing k T) := G.ring_localization S i j hj
  let eS := twistBasis G d S j hj
  let eT₀ := twistBasis G d T j (Finset.mem_insert_of_mem hj)
  letI : Module (ChartRing k S) (twistModule G d T) := Module.compHom (twistModule G d T) ρ
  let eT : ChartRing k T ≃ₗ[ChartRing k S] twistModule G d T :=
    eT₀.toAddEquiv.toLinearEquiv fun r x => by
      change eT₀ (ρ r * x) = ρ r • eT₀ x
      exact eT₀.map_smul (ρ r) x
  let L : ChartRing k S →ₗ[ChartRing k S] ChartRing k T := Algebra.linearMap _ _
  let P := Submonoid.powers (G.ratio S i j hj)
  let g : twistModule G d S →ₗ[ChartRing k S] twistModule G d T :=
    ((twistModules G d).map h).hom
  have hcomm : g ∘ₗ eS.toLinearMap = eT.toLinearMap ∘ₗ L := by
    apply LinearMap.ext
    intro r
    apply Subtype.ext
    change (eS r).val = (eT₀ (ρ r)).val
    have hρ := G.restrict_embed h r
    change G.embed T (ρ r) = G.embed S r at hρ
    rw [twistBasis_val, twistBasis_val, hρ]
  haveI : IsLocalizedModule P L := by
    exact (isLocalizedModule_iff_isLocalization' P (ChartRing k T)).mpr inferInstance
  have hloc : IsLocalizedModule P (eT.toLinearMap ∘ₗ L) :=
    IsLocalizedModule.of_linearEquiv P L eT
  rw [← hcomm] at hloc
  exact (IsLocalizedModule.comp_iff_of_bijective_right P eS.toLinearMap eS.bijective).mp hloc

/-- The homogeneous Laurent modules with the multiplication action of the chart rings. -/
def twistDiagram (G : ChartGeometry k ι) (d : ℤ) : TwistDiagram G d where
  modules := twistModules G d
  coefficients := twistCoefficients G d
  smul_coeff _ _ _ := rfl
  ground_coeff S a x := by
    change G.embed S (chartGround k S a) * x.val = a • x.val
    rw [G.constants, Algebra.smul_def]
    rfl
  restrict_coeff _ _ := rfl
  basis := twistBasis G d
  basis_coeff := twistBasis_val G d
  basis_transition := twistBasis_transition G d
  localized := twistModules_localized G d

theorem twistDiagramsExist : TwistDiagramsExist.{u} := by
  intro k ι _ _ _ G d
  exact ⟨twistDiagram G d⟩

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the constructed modules to the field gives the Laurent coefficient diagram. -/
def groundDiagramIso (G : ChartGeometry k ι) (d : ℤ) (M : TwistDiagram G d) :
    groundDiagram M.modules ≅ chartSets ι ⋙ laurentPresheaf k d :=
  NatIso.ofComponents (fun S => by
    let A := (groundDiagram M.modules).obj S
    let B := (chartSets ι ⋙ laurentPresheaf k d).obj S
    let f : A ≃+ B := M.coefficients (indexOf S)
    exact LinearEquiv.toModuleIso (X₁ := A) (X₂ := B)
      (f.toLinearEquiv fun a x => Subtype.ext (M.ground_coeff (indexOf S) a x)))
    (fun h => ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (M.restrict_coeff h x)))

theorem groundComparison : GroundComparison.{u} := by
  intro k ι _ _ _ G d M
  exact ⟨groundDiagramIso G d M, fun _ _ => rfl⟩

end TwistModules


section OrderedCech

open Specs.OrderedCechComparison (cechMap orderedCochainsMap)

variable {k ι : Type u} [Field k] [Fintype ι]

private abbrev degreeEmbedding (d : ℤ) : Exponents ι d ↪ (ι → ℤ) :=
  ⟨Subtype.val, Subtype.val_injective⟩

private theorem negativeSupport_subset_iff {d : ℤ} {S : Set ι} (a : Exponents ι d) :
    (negativeSupport a : Set ι) ⊆ S ↔ ∀ i ∉ S, 0 ≤ a.val i := by
  constructor
  · intro h i hi
    exact le_of_not_gt fun hneg => hi (h (by simpa [negativeSupport] using hneg))
  · intro h i hi
    by_contra his
    exact (not_lt_of_ge (h i his)) (by simpa [negativeSupport] using hi)

private def fixedDegreeCoefficients (d : ℤ) (S : Set ι) :
    LaurentPart k d S →ₗ[k] monomials k d S where
  toFun x := ⟨Finsupp.lcomapDomain (R := k) (degreeEmbedding d) (degreeEmbedding d).injective x.val.coeff,
    (Finsupp.mem_supported k _).mpr (by
      intro a ha
      have hmem : a.val ∈ x.val.coeff.support := by
        change a ∈ (Finsupp.lcomapDomain (R := k) (degreeEmbedding d) (degreeEmbedding d).injective
          x.val.coeff).support at ha
        rw [Finsupp.mem_support_iff, Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply] at ha
        exact Finsupp.mem_support_iff.mpr ha
      exact (negativeSupport_subset_iff a).mpr (x.property hmem).2)⟩
  map_add' x y := Subtype.ext (by ext a; simp [Finsupp.comapDomain_apply])
  map_smul' r x := Subtype.ext (by ext a; simp [Finsupp.comapDomain_apply])

private theorem fixedDegreeCoefficients_apply {d : ℤ} {S : Set ι}
    (x : LaurentPart k d S) (a : Exponents ι d) :
    (fixedDegreeCoefficients d S x).val a = x.val.coeff a.val := by
  change (Finsupp.lcomapDomain (R := k) (degreeEmbedding d) (degreeEmbedding d).injective
    x.val.coeff) a = _
  rw [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]
  rfl

private def fixedDegreeEquiv (d : ℤ) (S : Set ι) :
    LaurentPart k d S ≃ₗ[k] monomials k d S := by
  refine LinearEquiv.ofBijective (fixedDegreeCoefficients d S) ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro a
    by_cases ha : (∑ j, a j) = d
    · simpa only [fixedDegreeCoefficients_apply] using
        congrArg (fun z : monomials k d S => z.val ⟨a, ha⟩) h
    · have (z : LaurentPart k d S) : z.val.coeff a = 0 :=
        Finsupp.notMem_support_iff.mp (fun hz => ha (z.property hz).1)
      rw [this x, this y]
  · intro y
    let f := Finsupp.embDomain (degreeEmbedding d) y.val
    refine ⟨⟨AddMonoidAlgebra.ofCoeff f, ?_⟩, ?_⟩
    · apply AddMonoidAlgebra.mem_supported.mpr
      intro a ha
      change a ∈ f.support at ha
      rw [Finsupp.support_embDomain] at ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
      exact ⟨b.property, (negativeSupport_subset_iff b).mp (y.property hb)⟩
    · apply Subtype.ext
      ext a
      rw [fixedDegreeCoefficients_apply]
      exact Finsupp.embDomain_apply_self _ _ _

set_option backward.isDefEq.respectTransparency false in
private def fixedDegreeNatIso (d : ℤ) :
    laurentPresheaf (ι := ι) k d ≅ monomialPresheaf (ι := ι) k d :=
  NatIso.ofComponents
    (fun S => (fixedDegreeEquiv d (OrderDual.ofDual S.unop)).toModuleIso)
    (fun {S T} h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      apply Finsupp.ext
      intro a
      change (fixedDegreeCoefficients d (OrderDual.ofDual T.unop)
        ((laurentPresheaf k d).map h x)).val a =
        (fixedDegreeCoefficients d (OrderDual.ofDual S.unop) x).val a
      rw [fixedDegreeCoefficients_apply, fixedDegreeCoefficients_apply]
      rfl)

variable [LinearOrder ι]

set_option backward.isDefEq.respectTransparency false in
private def cechTermIso (d : ℤ) (n : ℕ) :
    (laurentCech (ι := ι) k d).X n ≅ (monomialCech (ι := ι) k d).X n :=
  (LinearEquiv.piCongrRight fun e : Fin (n + 1) ↪o ι =>
    fixedDegreeEquiv (k := k) d (OrderDual.ofDual
      (Specs.OrderedCechComparison.tupleOpen singletonCoordinates e))).toModuleIso

set_option backward.isDefEq.respectTransparency false in
private theorem cechTermIso_hom (d : ℤ) (n : ℕ) :
    (cechTermIso (k := k) (ι := ι) d n).hom =
      (cechMap singletonCoordinates (fixedDegreeNatIso (k := k) d).hom).f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext e
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Coefficientwise comparison with the fixed-degree ordered Čech model. -/
def orderedLaurentComparison (d : ℤ) : OrderedLaurentComparison k ι d where
  iso := HomologicalComplex.Hom.isoOfComponents (cechTermIso d) fun i j _ => by
    rw [cechTermIso_hom, cechTermIso_hom]
    exact (cechMap singletonCoordinates (fixedDegreeNatIso (k := k) d).hom).comm i j
  coeff _ _ _ _ := fixedDegreeCoefficients_apply _ _

theorem orderedLaurentComparisonExists : OrderedLaurentComparisonExists.{u} := by
  intro k ι _ _ _ d
  exact ⟨orderedLaurentComparison d⟩

end OrderedCech

end LinearAlgebraicGroups.ProjectiveTwistChartModules
