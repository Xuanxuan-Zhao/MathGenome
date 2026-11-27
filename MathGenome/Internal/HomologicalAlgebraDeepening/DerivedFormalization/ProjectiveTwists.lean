import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveTwists
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped BigOperators
open HomogeneousLocalization

namespace DerivedFormalization.ProjectiveTwists

universe u

variable (k : Type u) [Field k] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

def proj : Scheme := projectiveSpace k n

/-- The structure map of projective space over the ground field. -/
def structureMap : projectiveSpace k n ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (grading k n) ≫ Spec.map (CommRingCat.ofHom (constantInDegreeZero k n))

theorem variables_generate :
    Algebra.adjoin (grading k n 0) (Set.range (variablePolynomial k n)) = ⊤ := by
  let B := Algebra.adjoin (grading k n 0) (Set.range (variablePolynomial k n))
  let B' : Subalgebra k (Polynomials k n) :=
    { B.toSubring with
      algebraMap_mem' := fun r ↦
        (algebraMap_mem B ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩) }
  have h : Algebra.adjoin k (Set.range (variablePolynomial k n)) ≤ B' :=
    Algebra.adjoin_le fun x hx ↦ show x ∈ B from Algebra.subset_adjoin hx
  have hx : Algebra.adjoin k (Set.range (variablePolynomial k n)) = ⊤ :=
    MvPolynomial.adjoin_range_X
  rw [hx] at h
  exact top_le_iff.mp fun x _ ↦ h (Algebra.mem_top : x ∈ (⊤ : Subalgebra k (Polynomials k n)))

theorem standardCover : ⨆ i, chart k n i = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _ (fun i ↦ ⟨1, variable_degree k n i⟩)
    (variables_generate k n)

theorem intersectionBasicOpen (J : Finset (Index n)) :
    intersection k n J = Proj.basicOpen (grading k n) (chartProduct k n J) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      rw [intersection, Finset.inf_empty, chartProduct, Finset.prod_empty, Proj.basicOpen_one]
      rfl
  | insert i J hi ih =>
      rw [chartProduct, Finset.prod_insert hi, Proj.basicOpen_mul]
      change (insert i J).inf (chart k n) = chart k n i ⊓ _
      rw [Finset.inf_insert]
      exact congrArg (chart k n i ⊓ ·) ih

def chartScheme (J : Finset (Index n)) (hJ : J.Nonempty) :
    Scheme.Opens.toScheme (X := projectiveSpace k n) (intersection k n J) ≅ Spec (CommRingCat.of (ChartRing k n J)) :=
  Scheme.isoOfEq _ (intersectionBasicOpen k n J) ≪≫
    Proj.basicOpenIsoSpec _ _ (chartProduct_degree k n J) (Finset.card_pos.mpr hJ)

theorem coordinate_mem_inverted (J : Finset (Index n)) {i : Index n} (hi : i ∈ J) :
    variablePolynomial k n i ∈ invertedCoordinates k n J :=
  Submonoid.subset_closure ⟨i, hi, rfl⟩

theorem product_mem_inverted (J : Finset (Index n)) :
    chartProduct k n J ∈ invertedCoordinates k n J :=
  (invertedCoordinates k n J).prod_mem (fun _i hi ↦ coordinate_mem_inverted k n J hi)

theorem chartLocalization (J : Finset (Index n)) :
    IsLocalization (invertedCoordinates k n J) (ChartLocalization k n J) := by
  refine IsLocalization.of_le (Submonoid.powers (chartProduct k n J)) _
    (Submonoid.powers_le.mpr (product_mem_inverted k n J)) ?_
  intro r hr
  have h : invertedCoordinates k n J ≤
      (IsUnit.submonoid (ChartLocalization k n J)).comap
        (algebraMap (Polynomials k n) (ChartLocalization k n J)) := by
    refine Submonoid.closure_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    exact IsLocalization.Away.isUnit_of_dvd (chartProduct k n J)
      (Finset.dvd_prod_of_mem _ hi)
  exact h hr

theorem localizationToFraction_injective (P : Submonoid (Polynomials k n))
    (hP : P ≤ nonZeroDivisors _) : Function.Injective (localizationToFraction k n P hP) := by
  apply (IsLocalization.lift_injective_iff (S := Localization P) (unit_in_fraction k n P hP)).2
  intro x y
  rw [(IsLocalization.injective (Localization P) hP).eq_iff, (intoFraction_injective k n).eq_iff]

@[simp] theorem localizationToFraction_mk (P : Submonoid (Polynomials k n))
    (hP : P ≤ nonZeroDivisors _) (a : Polynomials k n) (b : P) :
    localizationToFraction k n P hP (Localization.mk a b) = fraction k n a b := by
  rw [Localization.mk_eq_mk']
  change IsLocalization.lift (unit_in_fraction k n P hP) _ = _
  apply (IsLocalization.lift_mk'_spec (S := Localization P) _ _ _ _).2
  exact (mul_div_cancel₀ _ (unit_in_fraction k n P hP b).ne_zero).symm

theorem homogeneousToFraction_injective (P : Submonoid (Polynomials k n))
    (hP : P ≤ nonZeroDivisors _) : Function.Injective (homogeneousToFraction k n P hP) :=
  (localizationToFraction_injective k n P hP).comp (val_injective P)

@[simp] theorem homogeneousToFraction_mk (P : Submonoid (Polynomials k n))
    (hP : P ≤ nonZeroDivisors _) (s : NumDenSameDeg (grading k n) P) :
    homogeneousToFraction k n P hP (HomogeneousLocalization.mk s) =
      fraction k n s.num s.den := by
  exact localizationToFraction_mk k n P hP _ _

private theorem not_mem_ne_zero {x : projectiveSpace k n} {b : Polynomials k n}
    (hb : b ∉ x.asHomogeneousIdeal) : b ≠ 0 := fun h ↦ hb (h ▸ zero_mem _)

@[simp] theorem fraction_zero (b : Polynomials k n) : fraction k n 0 b = 0 := by
  simp [fraction]

private theorem fraction_add (a b c d : Polynomials k n) (hb : b ≠ 0) (hd : d ≠ 0) :
    fraction k n a b + fraction k n c d = fraction k n (a * d + c * b) (b * d) := by
  simp only [fraction, map_add, map_mul]
  simpa only [mul_comm (intoFraction k n b)] using
    div_add_div (intoFraction k n a) (intoFraction k n c)
      (intoFraction_ne_zero k n hb) (intoFraction_ne_zero k n hd)

private theorem fraction_mul (a b c d : Polynomials k n) :
    fraction k n a b * fraction k n c d = fraction k n (a * c) (b * d) := by
  simp [fraction, div_mul_div_comm]

private theorem fraction_mul_cancel (a b c : Polynomials k n) (hc : c ≠ 0) :
    fraction k n (a * c) (b * c) = fraction k n a b := by
  simp [fraction, mul_div_mul_right _ _ (intoFraction_ne_zero k n hc)]

private theorem primeCompl_mul_mem {x : projectiveSpace k n} {a b : Polynomials k n}
    (ha : a ∉ x.asHomogeneousIdeal) (hb : b ∉ x.asHomogeneousIdeal) :
    a * b ∉ x.asHomogeneousIdeal :=
  (PrimeComplement k n x).mul_mem (x := a) (y := b) ha hb

abbrev TwistProperty (m : ℤ) {U : OpensOfProj k n}
    (s : U → RationalFunctions k n) := (twistPrelocal k n m).sheafify.pred s

theorem frame_nonzero (i : Index n) (m : ℤ) : frame k n i m ≠ 0 := by
  exact zpow_ne_zero _ (intoFraction_ne_zero k n (MvPolynomial.X_ne_zero i))

theorem section_zero (m : ℤ) (U : OpensOfProj k n) :
    TwistProperty k n m (0 : U → RationalFunctions k n) := by
  intro x
  have hx : x.1 ∈ ⨆ i, chart k n i := by rw [standardCover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨U ⊓ chart k n i, ⟨x.2, hi⟩, U.infLELeft _, ?_⟩
  refine ⟨0, variablePolynomial k n i ^ (-m).toNat, m.toNat, (-m).toNat,
    zero_mem _, ?_, by omega, ?_, by simp⟩
  · simpa using SetLike.pow_mem_graded (-m).toNat (variable_degree k n i)
  · intro y h
    exact y.2.2 (y.1.isPrime.mem_of_pow_mem _ h)

theorem section_add {m : ℤ} {U : OpensOfProj k n} {s t : U → RationalFunctions k n}
    (hs : TwistProperty k n m s) (ht : TwistProperty k n m t) :
    TwistProperty k n m (s + t) := by
  apply TopCat.PrelocalPredicate.sheafify_inductionOn₂' _ _ _ (fun a b ↦ a + b) ?_ hs ht
  intro V W a b ha hb
  obtain ⟨ra, sa, da, ea, hra, hsa, hma, hda, hfa⟩ := ha
  obtain ⟨rb, sb, db, eb, hrb, hsb, hmb, hdb, hfb⟩ := hb
  have heq : db + ea = da + eb := by omega
  refine ⟨ra * sb + rb * sa, sa * sb, da + eb, ea + eb,
    add_mem (SetLike.mul_mem_graded hra hsb) (heq ▸ SetLike.mul_mem_graded hrb hsa),
    SetLike.mul_mem_graded hsa hsb, by omega, ?_, ?_⟩
  · exact fun x ↦ primeCompl_mul_mem k n (hda ⟨x, x.2.1⟩) (hdb ⟨x, x.2.2⟩)
  · intro x
    change a ⟨x, x.2.1⟩ + b ⟨x, x.2.2⟩ = _
    rw [hfa ⟨x, x.2.1⟩, hfb ⟨x, x.2.2⟩]
    exact fraction_add k n _ _ _ _ (not_mem_ne_zero k n (hda ⟨x, x.2.1⟩))
      (not_mem_ne_zero k n (hdb ⟨x, x.2.2⟩))

theorem section_neg {m : ℤ} {U : OpensOfProj k n} {s : U → RationalFunctions k n}
    (hs : TwistProperty k n m s) : TwistProperty k n m (-s) := by
  apply TopCat.PrelocalPredicate.sheafify_inductionOn' _ (fun a ↦ -a) ?_ hs
  intro V a ha
  obtain ⟨r, s, d, e, hr, hs, hm, hd, hf⟩ := ha
  exact ⟨-r, s, d, e, neg_mem hr, hs, hm, hd, fun x ↦ by simp [hf x, fraction, neg_div]⟩

theorem section_mul {m l : ℤ} {U : OpensOfProj k n} {s t : U → RationalFunctions k n}
    (hs : TwistProperty k n m s) (ht : TwistProperty k n l t) :
    TwistProperty k n (m + l) (s * t) := by
  apply TopCat.PrelocalPredicate.sheafify_inductionOn₂' _ _ _ (fun a b ↦ a * b) ?_ hs ht
  intro V W a b ha hb
  obtain ⟨ra, sa, da, ea, hra, hsa, hma, hda, hfa⟩ := ha
  obtain ⟨rb, sb, db, eb, hrb, hsb, hmb, hdb, hfb⟩ := hb
  refine ⟨ra * rb, sa * sb, da + db, ea + eb, SetLike.mul_mem_graded hra hrb,
    SetLike.mul_mem_graded hsa hsb, by omega, ?_, ?_⟩
  · exact fun x ↦ primeCompl_mul_mem k n (hda ⟨x, x.2.1⟩) (hdb ⟨x, x.2.2⟩)
  · intro x
    change a ⟨x, x.2.1⟩ * b ⟨x, x.2.2⟩ = _
    rw [hfa ⟨x, x.2.1⟩, hfb ⟨x, x.2.2⟩]
    exact fraction_mul k n _ _ _ _

def sectionAddSubgroup (m : ℤ) (U : OpensOfProj k n) :
    AddSubgroup (U → RationalFunctions k n) where
  carrier := {s | TwistProperty k n m s}
  zero_mem' := section_zero k n m U
  add_mem' := section_add k n
  neg_mem' := section_neg k n

instance (m : ℤ) (U : OpensOfProj k n) : AddCommGroup (TwistSections k n m U) :=
  (sectionAddSubgroup k n m U).toAddCommGroup

theorem structureToFunctions_injective (U : OpensOfProj k n) :
    Function.Injective (structureToFunctions k n U) := by
  intro s t h
  apply Subtype.ext
  funext x
  exact homogeneousToFraction_injective k n _
    (@Ideal.primeCompl_le_nonZeroDivisors _ _ _ x.1.asHomogeneousIdeal.toIdeal x.1.isPrime)
    (congrFun h x)

set_option backward.isDefEq.respectTransparency false in
theorem structureToFunctions_mem (U : OpensOfProj k n) (s : structureSections k n U) :
    TwistProperty k n 0 (structureToFunctions k n U s) := by
  intro x
  obtain ⟨V, hx, i, d, a, b, hb, hs⟩ := s.property x
  exact ⟨V, hx, i, a, b, d, d, a.2, b.2, by omega, hb, fun y ↦ by
    change fiberToFraction k n y.1 (s.val (i y)) = _
    exact (congrArg (fiberToFraction k n y.1) (hs y)).trans
      (homogeneousToFraction_mk k n _ _ _)⟩

private def fiberMk (x : Base k n) (d : ℕ) (a b : grading k n d)
    (hb : b.val ∉ x.asHomogeneousIdeal) : Fiber k n x :=
  HomogeneousLocalization.mk ⟨d, a, b, hb⟩

private theorem fiberMk_value (x : Base k n) (d : ℕ) (a b : grading k n d)
    (hb : b.val ∉ x.asHomogeneousIdeal) :
    fiberToFraction k n x (fiberMk k n x d a b hb) = fraction k n a b :=
  homogeneousToFraction_mk k n _ _ _

private theorem fiberToFraction_injective (x : Base k n) :
    Function.Injective (fiberToFraction k n x) :=
  homogeneousToFraction_injective k n (PrimeComplement k n x) _

private theorem exists_fiber_value (U : OpensOfProj k n)
    (s : U → RationalFunctions k n) (hs : TwistProperty k n 0 s) (x : U) :
    ∃ r : Fiber k n x.1, fiberToFraction k n x.1 r = s x := by
  obtain ⟨V, hx, i, a, b, d, e, ha, hb, hdeg, hden, he⟩ := hs x
  have hd : d = e := by omega
  subst e
  exact ⟨fiberMk k n x.1 d ⟨a, ha⟩ ⟨b, hb⟩ (hden ⟨x, hx⟩),
    (fiberMk_value k n x.1 d ⟨a, ha⟩ ⟨b, hb⟩ _).trans (he ⟨x, hx⟩).symm⟩

set_option backward.isDefEq.respectTransparency false in
theorem structureToFunctions_surjective (U : OpensOfProj k n)
    (s : U → RationalFunctions k n) (hs : TwistProperty k n 0 s) :
    ∃ r : structureSections k n U, structureToFunctions k n U r = s := by
  choose r hr using exists_fiber_value k n U s hs
  refine ⟨⟨r, ?_⟩, funext hr⟩
  intro x
  obtain ⟨V, hx, i, a, b, d, e, ha, hb, hdeg, hden, he⟩ := hs x
  have hd : d = e := by omega
  subst e
  refine ⟨V, hx, i, d, ⟨a, ha⟩, ⟨b, hb⟩, hden, fun y ↦ ?_⟩
  change r (i y) = fiberMk k n y.1 d ⟨a, ha⟩ ⟨b, hb⟩ (hden y)
  exact fiberToFraction_injective k n y.1
    ((hr (i y)).trans ((he y).trans (fiberMk_value k n y.1 d ⟨a, ha⟩ ⟨b, hb⟩ _).symm))

instance (U : OpensOfProj k n) : Module (structureSections k n U) (U → RationalFunctions k n) :=
  (structureToFunctions k n U).toModule

theorem scalar_apply (U : OpensOfProj k n) (r : structureSections k n U)
    (s : U → RationalFunctions k n) (x : U) :
    (r • s) x = structureToFunctions k n U r x * s x := rfl

def sectionSubmodule (m : ℤ) (U : OpensOfProj k n) :
    Submodule (structureSections k n U) (U → RationalFunctions k n) where
  __ := sectionAddSubgroup k n m U
  smul_mem' r s hs := by
    change TwistProperty k n m s at hs
    change TwistProperty k n m (structureToFunctions k n U r * s)
    simpa using section_mul k n (structureToFunctions_mem k n U r) hs

instance (m : ℤ) (U : OpensOfProj k n) :
    Module (structureSections k n U) (TwistSections k n m U) :=
  (sectionSubmodule k n m U).module

theorem frame_neg (i : Index n) (m : ℤ) :
    frame k n i (-m) = (frame k n i m)⁻¹ := zpow_neg _ _

theorem frame_add (i : Index n) (m l : ℤ) :
    frame k n i (m + l) = frame k n i m * frame k n i l :=
  zpow_add₀ (intoFraction_ne_zero k n (MvPolynomial.X_ne_zero i)) m l

theorem frame_isSection (i : Index n) (m : ℤ) {U : OpensOfProj k n}
    (hU : U ≤ chart k n i) :
    TwistProperty k n m (fun _ : U ↦ frame k n i m) := by
  apply TopCat.PrelocalPredicate.sheafifyOf
  rcases Int.eq_nat_or_neg m with ⟨a, rfl | rfl⟩
  · refine ⟨variablePolynomial k n i ^ a, 1, a, 0, ?_, SetLike.one_mem_graded _,
      by omega, fun y hy ↦ y.1.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy isUnit_one),
      fun _ ↦ by simp [frame, fraction]⟩
    simpa using SetLike.pow_mem_graded a (variable_degree k n i)
  · refine ⟨1, variablePolynomial k n i ^ a, 0, a, SetLike.one_mem_graded _, ?_,
      by omega, ?_, fun _ ↦ by simp [frame, fraction, zpow_neg]⟩
    · simpa using SetLike.pow_mem_graded a (variable_degree k n i)
    · exact fun y h ↦ (hU y.2) (y.1.isPrime.mem_of_pow_mem _ h)

theorem frame_mul_mem (i : Index n) (m : ℤ) {U : OpensOfProj k n}
    (hU : U ≤ chart k n i) (r : structureSections k n U) :
    TwistProperty k n m (fun x ↦ structureToFunctions k n U r x * frame k n i m) := by
  change TwistProperty k n m (structureToFunctions k n U r * fun _ ↦ frame k n i m)
  simpa only [zero_add] using section_mul k n (structureToFunctions_mem k n U r)
    (frame_isSection k n i m hU)

/-- The frame `x_i^m` gives an isomorphism with the free rank-one module on
every subopen of the chart. -/
def frameEquiv (i : Index n) (m : ℤ) {U : OpensOfProj k n}
    (hU : U ≤ chart k n i) : structureSections k n U ≃ₗ[structureSections k n U]
      TwistSections k n m U := by
  let f : structureSections k n U →ₗ[structureSections k n U] TwistSections k n m U :=
    { toFun := fun r ↦ ⟨_, frame_mul_mem k n i m hU r⟩
      map_add' := fun r s ↦ Subtype.ext (funext fun x ↦ by
        change structureToFunctions k n U (r + s) x * _ =
          structureToFunctions k n U r x * _ + structureToFunctions k n U s x * _
        rw [map_add, Pi.add_apply, add_mul])
      map_smul' := fun r s ↦ Subtype.ext (funext fun x ↦ by
        change structureToFunctions k n U (r * s) x * _ =
          structureToFunctions k n U r x * (structureToFunctions k n U s x * _)
        rw [map_mul, Pi.mul_apply, mul_assoc]) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro r s h
    apply structureToFunctions_injective
    funext x
    exact mul_right_cancel₀ (frame_nonzero k n i m)
      (congrFun (congrArg Subtype.val h) x)
  · intro s
    have ht : TwistProperty k n 0 (fun x ↦ s.val x * frame k n i (-m)) := by
      have h := section_mul k n s.property (frame_isSection k n i (-m) hU)
      rwa [add_neg_cancel] at h
    obtain ⟨r, hr⟩ := structureToFunctions_surjective k n U _ ht
    refine ⟨r, Subtype.ext (funext fun x ↦ ?_)⟩
    change structureToFunctions k n U r x * frame k n i m = s.val x
    rw [congrFun hr x, frame_neg, inv_mul_cancel_right₀ (frame_nonzero k n i m)]

@[simp] theorem frameEquiv_apply (i : Index n) (m : ℤ) {U : OpensOfProj k n}
    (hU : U ≤ chart k n i) (r : structureSections k n U) (x : U) :
    (frameEquiv k n i m hU r).val x =
      structureToFunctions k n U r x * frame k n i m := rfl

abbrev twistModule (m : ℤ) (U : (OpensOfProj k n)ᵒᵖ) :
    ModuleCat (structurePresheaf k n |>.obj U) :=
  ModuleCat.of (structureSections k n U.unop) (TwistSections k n m U.unop)

private instance twistModule_module (m : ℤ) (U : (OpensOfProj k n)ᵒᵖ) :
    Module ((structurePresheaf k n).obj U) (twistModule k n m U) :=
  (twistModule k n m U).isModule

private def twistRestrictLinear (m : ℤ) {U V : (OpensOfProj k n)ᵒᵖ} (f : U ⟶ V) :
    twistModule k n m U →ₛₗ[((structurePresheaf k n).map f).hom] twistModule k n m V where
  toFun := (twistTypes k n m).obj.map f
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
def twistPresheaf (m : ℤ) : PresheafOfModules (moduleRingSheaf k n).obj where
  obj := twistModule k n m
  map {U V} f :=
    ModuleCat.semilinearMapAddEquiv ((structurePresheaf k n).map f).hom
      (twistModule k n m U) (twistModule k n m V)
      (twistRestrictLinear k n m f)
  map_id _ := by apply ModuleCat.Hom.ext; apply DFunLike.ext; intro s; rfl
  map_comp _ _ := by apply ModuleCat.Hom.ext; apply DFunLike.ext; intro s; rfl

/-- The twisting sheaf as a sheaf of modules over the structure sheaf of projective space. -/
def twistingSheaf (m : ℤ) : SheafOfModules (moduleRingSheaf k n) where
  val := twistPresheaf k n m
  isSheaf := by
    apply (Presheaf.isSheaf_iff_isSheaf_comp _ _ (forget AddCommGrpCat.{u})).mpr
    let e : (twistPresheaf k n m).presheaf ⋙ forget AddCommGrpCat.{u} ≅
        (twistTypes k n m).obj :=
      NatIso.ofComponents (fun U ↦ Equiv.toIso (Equiv.refl (TwistSections k n m U.unop)))
        (by intros; ext s; rfl)
    exact (Presheaf.isSheaf_of_iso_iff e).mpr (twistTypes k n m).property

theorem intersection_le_chart {J : Finset (Index n)} {i : Index n} (hi : i ∈ J) :
    intersection k n J ≤ chart k n i := Finset.inf_le hi

theorem inverted_le_nonZeroDivisors (J : Finset (Index n)) :
    invertedCoordinates k n J ≤ nonZeroDivisors (Polynomials k n) := by
  refine Submonoid.closure_le.mpr ?_
  rintro _ ⟨i, _, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero i)

/-- Clear a denominator made of coordinate factors by multiplying it by a homogeneous cofactor. -/
private theorem homogeneous_cofactor (J : Finset (Index n)) {b : Polynomials k n}
    (hb : b ∈ invertedCoordinates k n J) :
    ∃ (c : Polynomials k n) (t d e : ℕ), b ∈ grading k n d ∧ c ∈ grading k n e ∧
      d + e = t * J.card ∧ b * c = chartProduct k n J ^ t := by
  classical
  induction hb using Submonoid.closure_induction with
  | mem _ hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨chartProduct k n (J.erase i), 1, 1, (J.erase i).card, variable_degree k n i,
      chartProduct_degree k n _, ?_, ?_⟩
    · have := Finset.card_erase_add_one hi
      omega
    · simpa [chartProduct] using Finset.mul_prod_erase J (variablePolynomial k n) hi
  | one =>
    exact ⟨1, 0, 0, 0, SetLike.one_mem_graded _, SetLike.one_mem_graded _, by simp, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨c, t, d, e, ha, hc, ht, heq⟩ := ha
    obtain ⟨f, v, d', e', hb, hf, hv, heq'⟩ := hb
    refine ⟨c * f, t + v, d + d', e + e', SetLike.mul_mem_graded ha hb,
      SetLike.mul_mem_graded hc hf, ?_, ?_⟩
    · rw [Nat.add_mul, ← ht, ← hv]
      omega
    · rw [mul_mul_mul_comm, heq, heq', ← pow_add]

theorem degreePiece_image (J : Finset (Index n)) (m : ℤ) (s : RationalFunctions k n) :
    (∃ w : DegreePiece k n J m, chartToFraction k n J w.val = s) ↔
      homogeneousFraction k n (invertedCoordinates k n J) m s := by
  constructor
  · rintro ⟨⟨w, a, t, d, ha, hm, rfl⟩, rfl⟩
    exact ⟨a, chartProduct k n J ^ t, d, t * J.card, ha,
      SetLike.pow_mem_graded t (chartProduct_degree k n J),
      pow_mem (product_mem_inverted k n J) _, hm, localizationToFraction_mk k n _ _ _ _⟩
  · rintro ⟨a, b, d, e, ha, hb, hP, hm, rfl⟩
    obtain ⟨c, t, e', f, hb', hc, hdeg, heq⟩ := homogeneous_cofactor k n J hP
    have hbne := nonZeroDivisors.ne_zero (inverted_le_nonZeroDivisors k n J hP)
    have he : e' = e :=
      (MvPolynomial.IsHomogeneous.totalDegree hb' hbne).symm.trans
        (MvPolynomial.IsHomogeneous.totalDegree hb hbne)
    subst e'
    have hcne : c ≠ 0 := by
      intro h
      have hz := pow_ne_zero t (chartProduct_ne_zero k n J)
      exact hz (heq.symm.trans (by simp [h]))
    refine ⟨⟨Localization.mk (a * c) (chartDenominator k n J t), a * c, t, d + f,
      SetLike.mul_mem_graded ha hc, ?_, rfl⟩, ?_⟩
    · rw [← hdeg]
      omega
    · rw [localizationToFraction_mk]
      exact (congrArg (fraction k n (a * c)) heq).symm.trans (fraction_mul_cancel k n a b c hcne)

theorem chartRing_image (J : Finset (Index n)) (s : RationalFunctions k n) :
    (∃ a : ChartRing k n J, chartRingToFraction k n J a = s) ↔
      homogeneousFraction k n (invertedCoordinates k n J) 0 s := by
  rw [← degreePiece_image]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨t, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (grading k n) (chartProduct_degree k n J) a
    exact ⟨⟨_, p, t, t * J.card, hp, by omega, rfl⟩, rfl⟩
  · rintro ⟨⟨_, p, t, d, hd, hdeg, rfl⟩, rfl⟩
    have he : d = t * J.card := by omega
    subst d
    exact ⟨HomogeneousLocalization.Away.mk _ (chartProduct_degree k n J) t p hd, rfl⟩

private theorem homogeneousFraction_mul (P : Submonoid (Polynomials k n)) {m l : ℤ}
    {s t : RationalFunctions k n}
    (hs : homogeneousFraction k n P m s) (ht : homogeneousFraction k n P l t) :
    homogeneousFraction k n P (m + l) (s * t) := by
  obtain ⟨a, b, d, e, ha, hb, hP, hm, rfl⟩ := hs
  obtain ⟨c, f, g, j, hc, hf, hP', hl, rfl⟩ := ht
  exact ⟨a * c, b * f, d + g, e + j, SetLike.mul_mem_graded ha hc, SetLike.mul_mem_graded hb hf,
    P.mul_mem hP hP', by omega, fraction_mul k n _ _ _ _⟩

private theorem frame_homogeneousFraction (P : Submonoid (Polynomials k n))
    (i : Index n) (hi : variablePolynomial k n i ∈ P) (m : ℤ) :
    homogeneousFraction k n P m (frame k n i m) := by
  rcases Int.eq_nat_or_neg m with ⟨a, rfl | rfl⟩
  · exact ⟨variablePolynomial k n i ^ a, 1, a, 0,
      by simpa using SetLike.pow_mem_graded a (variable_degree k n i),
      SetLike.one_mem_graded _, P.one_mem, by omega, by simp [frame, fraction]⟩
  · exact ⟨1, variablePolynomial k n i ^ a, 0, a, SetLike.one_mem_graded _,
      by simpa using SetLike.pow_mem_graded a (variable_degree k n i),
      P.pow_mem hi _, by omega, by simp [frame, fraction, zpow_neg]⟩

theorem degreePiece_frame {J : Finset (Index n)} {i : Index n} (hi : i ∈ J)
    (m : ℤ) (s : RationalFunctions k n) :
    (∃ w : DegreePiece k n J m, chartToFraction k n J w.val = s) ↔
      ∃ a : ChartRing k n J, s = chartRingToFraction k n J a * frame k n i m := by
  rw [degreePiece_image]
  have h (l : ℤ) := frame_homogeneousFraction k n (invertedCoordinates k n J) i
    (coordinate_mem_inverted k n J hi) l
  constructor
  · intro hs
    have h0 := homogeneousFraction_mul k n _ hs (h (-m))
    rw [add_neg_cancel] at h0
    obtain ⟨a, ha⟩ := (chartRing_image k n J _).mpr h0
    exact ⟨a, by rw [ha, frame_neg, inv_mul_cancel_right₀ (frame_nonzero k n i m)]⟩
  · rintro ⟨a, rfl⟩
    have h0 := (chartRing_image k n J _).mp ⟨a, rfl⟩
    simpa only [zero_add] using homogeneousFraction_mul k n _ h0 (h m)

private def zeroPoint : Base k n where
  asHomogeneousIdeal := ⊥
  isPrime := by rw [HomogeneousIdeal.toIdeal_bot]; infer_instance
  not_irrelevant_le h := by
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem (grading k n) (by decide : 0 < (1 : ℕ))
      (variable_degree k n (0 : Index n)))
    exact MvPolynomial.X_ne_zero (0 : Index n) (by
      change variablePolynomial k n 0 ∈ (⊥ : Ideal (Polynomials k n)) at hx
      exact Ideal.mem_bot.mp hx)

private theorem zeroPoint_mem_intersection (J : Finset (Index n)) :
    zeroPoint k n ∈ intersection k n J := by
  rw [intersectionBasicOpen]
  change chartProduct k n J ∉ (⊥ : HomogeneousIdeal (grading k n))
  change chartProduct k n J ∉ (⊥ : Ideal (Polynomials k n))
  exact fun h ↦ chartProduct_ne_zero k n J (Ideal.mem_bot.mp h)

private def basicStructureEquiv (f : Polynomials k n) {d : ℕ}
    (hf : f ∈ grading k n d) (hd : 0 < d) (U : OpensOfProj k n)
    (hU : U = Proj.basicOpen (grading k n) f) :
    Away (grading k n) f ≃+* structureSections k n U := by
  subst U
  exact Iso.commRingCatIsoToRingEquiv (Proj.basicOpenIsoAway _ _ hf hd)

private theorem basicStructureEquiv_value (f : Polynomials k n) {d : ℕ}
    (hf : f ∈ grading k n d) (hd : 0 < d) (U : OpensOfProj k n)
    (hU : U = Proj.basicOpen (grading k n) f)
    (hP : Submonoid.powers f ≤ nonZeroDivisors (Polynomials k n))
    (a : Away (grading k n) f) (x : U) :
    structureToFunctions k n U (basicStructureEquiv k n f hf hd U hU a) x =
      homogeneousToFraction k n _ hP a := by
  subst U
  obtain ⟨b, rfl⟩ := HomogeneousLocalization.mk_surjective a
  have hb := ProjectiveSpectrum.Proj.awayToSection_apply (grading k n) f
    (HomogeneousLocalization.mk b) x
  change localizationToFraction k n (PrimeComplement k n x.1)
    (@Ideal.primeCompl_le_nonZeroDivisors _ _ _ x.1.asHomogeneousIdeal.toIdeal x.1.isPrime)
    (((ProjectiveSpectrum.Proj.awayToSection (grading k n) f) (HomogeneousLocalization.mk b)).val x).val =
      _
  refine (congrArg (localizationToFraction k n (PrimeComplement k n x.1) _) hb).trans ?_
  rw [val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    ← Localization.mk_eq_mk', localizationToFraction_mk, homogeneousToFraction_mk]
  rfl

def chartStructureEquiv (J : Finset (Index n)) (hJ : J.Nonempty) :
    ChartRing k n J ≃+* structureSections k n (intersection k n J) :=
  basicStructureEquiv k n _ (chartProduct_degree k n J) (Finset.card_pos.mpr hJ) _
    (intersectionBasicOpen k n J)

theorem chartStructureEquiv_value (J : Finset (Index n)) (hJ : J.Nonempty)
    (a : ChartRing k n J) (x : intersection k n J) :
    structureToFunctions k n _ (chartStructureEquiv k n J hJ a) x =
      chartRingToFraction k n J a :=
  basicStructureEquiv_value k n _ _ _ _ _ _ _ _

private theorem exists_section_for_degreePiece {J : Finset (Index n)} (hJ : J.Nonempty)
    (m : ℤ) (p : DegreePiece k n J m) :
    ∃ s : TwistSections k n m (intersection k n J),
      ∀ x, s.val x = chartToFraction k n J p.val := by
  obtain ⟨i, hi⟩ := hJ
  obtain ⟨a, ha⟩ := (degreePiece_frame k n hi m _).mp ⟨p, rfl⟩
  refine ⟨frameEquiv k n i m (intersection_le_chart k n hi)
    (chartStructureEquiv k n J ⟨i, hi⟩ a), fun x ↦ ?_⟩
  rw [frameEquiv_apply]
  exact (congrArg (· * frame k n i m) (chartStructureEquiv_value k n J ⟨i, hi⟩ a x)).trans ha.symm

private theorem degreePiece_section_unique (J : Finset (Index n)) (m : ℤ)
    (p : DegreePiece k n J m) {s t : TwistSections k n m (intersection k n J)}
    (hs : ∀ x, s.val x = chartToFraction k n J p.val)
    (ht : ∀ x, t.val x = chartToFraction k n J p.val) : s = t :=
  Subtype.ext (funext fun x ↦ (hs x).trans (ht x).symm)

/-- The actual homogeneous components of the ordinary localization give the twist sections. -/
def degreePieceSections (J : Finset (Index n)) (hJ : J.Nonempty) (m : ℤ) :
    DegreePiece k n J m ≃ TwistSections k n m (intersection k n J) := by
  classical
  let h := exists_section_for_degreePiece k n hJ m
  let f := fun p ↦ (h p).choose
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro p q hpq
    let x : intersection k n J := ⟨zeroPoint k n, zeroPoint_mem_intersection k n J⟩
    apply Subtype.ext
    apply localizationToFraction_injective k n _ (powers_product_le_nonZeroDivisors k n J)
    exact ((h p).choose_spec x).symm.trans
      ((congrArg (fun s : TwistSections k n m (intersection k n J) ↦ s.val x) hpq).trans
        ((h q).choose_spec x))
  · intro s
    obtain ⟨i, hi⟩ := hJ
    obtain ⟨r, rfl⟩ := (frameEquiv k n i m (intersection_le_chart k n hi)).surjective s
    obtain ⟨a, rfl⟩ := (chartStructureEquiv k n J ⟨i, hi⟩).surjective r
    obtain ⟨p, hp⟩ := (degreePiece_frame k n hi m _).mpr ⟨a, rfl⟩
    refine ⟨p, degreePiece_section_unique k n J m p ((h p).choose_spec) fun x ↦ ?_⟩
    rw [frameEquiv_apply]
    exact (congrArg (· * frame k n i m) (chartStructureEquiv_value k n J ⟨i, hi⟩ a x)).trans hp.symm

@[simp] theorem degreePieceSections_value (J : Finset (Index n)) (hJ : J.Nonempty)
    (m : ℤ) (p : DegreePiece k n J m) (x : intersection k n J) :
    (degreePieceSections k n J hJ m p).val x = chartToFraction k n J p.val :=
  (exists_section_for_degreePiece k n hJ m p).choose_spec x


private theorem localizationToFraction_algebraMap (P : Submonoid (Polynomials k n))
    (hP : P ≤ nonZeroDivisors _) (a : Polynomials k n) :
    localizationToFraction k n P hP (algebraMap _ _ a) = intoFraction k n a :=
  IsLocalization.lift_eq (unit_in_fraction k n P hP) a

theorem localizationRestriction_value {J K : Finset (Index n)} (h : J ⊆ K)
    (a : ChartLocalization k n J) :
    chartToFraction k n K (localizationRestriction k n h a) = chartToFraction k n J a := by
  have hcomp : (chartToFraction k n K).comp (localizationRestriction k n h) =
      chartToFraction k n J := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (chartProduct k n J))
    apply RingHom.ext
    intro b
    change chartToFraction k n K (localizationRestriction k n h (algebraMap _ _ b)) =
      chartToFraction k n J (algebraMap _ _ b)
    rw [localizationRestriction, IsLocalization.Away.lift_eq,
      localizationToFraction_algebraMap, localizationToFraction_algebraMap]
  exact DFunLike.congr_fun hcomp a

theorem inverted_mono : Monotone (invertedCoordinates k n) :=
  fun _ _ h ↦ Submonoid.closure_mono (Set.image_mono h)

def degreeRestriction {J K : Finset (Index n)} (h : J ⊆ K) (m : ℤ)
    (a : DegreePiece k n J m) : DegreePiece k n K m := by
  refine ⟨localizationRestriction k n h a.val, ?_⟩
  have ha := (degreePiece_image k n J m _).mp ⟨a, rfl⟩
  obtain ⟨x, y, d, e, hx, hy, hyJ, he, hval⟩ := ha
  obtain ⟨b, hb⟩ := (degreePiece_image k n K m _).mpr
    ⟨x, y, d, e, hx, hy, inverted_mono k n h hyJ, he, hval⟩
  have hh : b.val = localizationRestriction k n h a.val :=
    localizationToFraction_injective k n _ (powers_product_le_nonZeroDivisors k n K)
      (hb.trans (localizationRestriction_value k n h a.val).symm)
  exact hh ▸ b.property

theorem degreeRestriction_value {J K : Finset (Index n)} (h : J ⊆ K) (m : ℤ)
    (a : DegreePiece k n J m) :
    (degreeRestriction k n h m a).val = localizationRestriction k n h a.val := rfl

theorem twistPresheaf_restrict {U V : OpensOfProj k n} (h : V ≤ U) (m : ℤ)
    (s : TwistSections k n m U) :
    (twistPresheaf k n m).map (homOfLE h).op s = restriction k n h m s := rfl

theorem degreePieceSections_restrict {J K : Finset (Index n)} (h : J ⊆ K)
    (hJ : J.Nonempty) (hK : K.Nonempty) (m : ℤ) (a : DegreePiece k n J m) :
    restriction k n (intersection_antitone k n h) m (degreePieceSections k n J hJ m a) =
      degreePieceSections k n K hK m (degreeRestriction k n h m a) := by
  apply Subtype.ext
  funext x
  change (degreePieceSections k n J hJ m a).val
    ⟨x, intersection_antitone k n h x.2⟩ = _
  rw [degreePieceSections_value, degreePieceSections_value, degreeRestriction_value,
    localizationRestriction_value]

def degreeMul (J : Finset (Index n)) (m l : ℤ)
    (a : DegreePiece k n J m) (b : DegreePiece k n J l) : DegreePiece k n J (m + l) := by
  refine ⟨a.val * b.val, ?_⟩
  obtain ⟨p, t, d, hp, hdeg, he⟩ := a.property
  obtain ⟨q, v, e, hq, hdeg', he'⟩ := b.property
  refine ⟨p * q, t + v, d + e, SetLike.mul_mem_graded hp hq, ?_, ?_⟩
  · rw [Nat.add_mul]
    omega
  · rw [he, he', Localization.mk_mul]
    congr 1
    apply Subtype.ext
    exact (pow_add ..).symm

def sectionMul (m l : ℤ) (U : OpensOfProj k n)
    (a : TwistSections k n m U) (b : TwistSections k n l U) : TwistSections k n (m + l) U :=
  ⟨a.val * b.val, section_mul k n a.property b.property⟩

theorem sectionMul_degreePieceSections (J : Finset (Index n)) (hJ : J.Nonempty) (m l : ℤ)
    (a : DegreePiece k n J m) (b : DegreePiece k n J l) :
    sectionMul k n m l _ (degreePieceSections k n J hJ m a) (degreePieceSections k n J hJ l b) =
      degreePieceSections k n J hJ (m + l) (degreeMul k n J m l a b) := by
  apply Subtype.ext
  funext x
  change (degreePieceSections k n J hJ m a).val x *
    (degreePieceSections k n J hJ l b).val x = _
  rw [degreePieceSections_value, degreePieceSections_value, degreePieceSections_value]
  exact ((chartToFraction k n J).map_mul _ _).symm

theorem frameEquiv_restrict (i : Index n) (m : ℤ) {U V : OpensOfProj k n}
    (hU : U ≤ chart k n i) (hVU : V ≤ U) (r : structureSections k n U) :
    restriction k n hVU m (frameEquiv k n i m hU r) =
      frameEquiv k n i m (hVU.trans hU) ((projectiveSpace k n).presheaf.map (homOfLE hVU).op r) :=
  rfl

def frameTransition (i j : Index n) (m : ℤ) {U : OpensOfProj k n}
    (hi : U ≤ chart k n i) (hj : U ≤ chart k n j) : structureSections k n U :=
  (frameEquiv k n i m hi).symm ⟨_, frame_isSection k n j m hj⟩

theorem frameTransition_value (i j : Index n) (m : ℤ) {U : OpensOfProj k n}
    (hi : U ≤ chart k n i) (hj : U ≤ chart k n j) (x : U) :
    structureToFunctions k n U (frameTransition k n i j m hi hj) x =
      fraction k n (variablePolynomial k n j) (variablePolynomial k n i) ^ m := by
  have h := congrArg (fun s : TwistSections k n m U ↦ s.val x)
    ((frameEquiv k n i m hi).apply_symm_apply ⟨_, frame_isSection k n j m hj⟩)
  change structureToFunctions k n U (frameTransition k n i j m hi hj) x * frame k n i m =
    frame k n j m at h
  rw [fraction, div_zpow]
  exact (eq_div_iff (frame_nonzero k n i m)).2 h


private theorem variable_powers_le_nonZeroDivisors (i : Index n) :
    Submonoid.powers (variablePolynomial k n i) ≤ nonZeroDivisors (Polynomials k n) :=
  Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero i))

private theorem coordinateRatio_value (i j : Index n) :
    homogeneousToFraction k n _ (variable_powers_le_nonZeroDivisors k n i)
      (coordinateRatio k n i j) =
    fraction k n (variablePolynomial k n j) (variablePolynomial k n i) := by
  unfold coordinateRatio homogeneousToFraction
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, localizationToFraction_mk]
  exact congrArg (fraction k n (variablePolynomial k n j)) (pow_one _)

private def dehomogenize (i : Index n) : Polynomials k n →+* CoordinatePolynomials k n i :=
  MvPolynomial.eval₂Hom MvPolynomial.C (dehomogenizedVariable k n i)

private theorem dehomogenize_self (i : Index n) :
    dehomogenize k n i (variablePolynomial k n i) = 1 := by
  simp [dehomogenize, dehomogenizedVariable]

private def dehomogenizeLocalization (i : Index n) :
    Localization.Away (variablePolynomial k n i) →+* CoordinatePolynomials k n i :=
  Localization.awayLift (dehomogenize k n i) (variablePolynomial k n i)
    (isUnit_iff_exists_inv.mpr ⟨1, by rw [mul_one, dehomogenize_self]⟩)

private theorem dehomogenizeLocalization_mk (i : Index n) (a : Polynomials k n) (t : ℕ) :
    dehomogenizeLocalization k n i
      (Localization.mk a (⟨(variablePolynomial k n i) ^ t, t, rfl⟩ :
        Submonoid.powers (variablePolynomial k n i))) = dehomogenize k n i a := by
  unfold dehomogenizeLocalization
  rw [Localization.awayLift_mk _ _ a 1 (by rw [mul_one, dehomogenize_self])]
  simp

private def dehomogenizeSingleton (i : Index n) :
    SingletonRing k n i →+* CoordinatePolynomials k n i :=
  (dehomogenizeLocalization k n i).comp (algebraMap _ _)

private theorem dehomogenizeSingleton_mk (i : Index n) (a : Polynomials k n)
    (t : ℕ) (ha : a ∈ grading k n (t • (1 : ℕ))) :
    dehomogenizeSingleton k n i (HomogeneousLocalization.Away.mk _
      (variable_degree k n i) t a ha) = dehomogenize k n i a := by
  rw [dehomogenizeSingleton, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, dehomogenizeLocalization_mk]

private theorem constantInSingleton_eq (i : Index n) (r : k) :
    constantInSingleton k n i r =
      HomogeneousLocalization.Away.mk _ (variable_degree k n i) 0 (MvPolynomial.C r)
        (by simp) := rfl

private theorem dehomogenize_comp_ratios (i : Index n) :
    (dehomogenizeSingleton k n i).comp (ratios k n i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, ratios, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
    rw [constantInSingleton_eq, dehomogenizeSingleton_mk]
    simp [dehomogenize]
  · intro j
    simp only [RingHom.comp_apply, ratios, MvPolynomial.eval₂Hom_X', RingHom.id_apply]
    rw [coordinateRatio, dehomogenizeSingleton_mk]
    simp [dehomogenize, dehomogenizedVariable, j.2]

private theorem ratio_constant_value (i : Index n) (r : k) :
    homogeneousToFraction k n _ (variable_powers_le_nonZeroDivisors k n i)
      (constantInSingleton k n i r) = intoFraction k n (MvPolynomial.C r) := by
  refine (homogeneousToFraction_mk k n _ _ _).trans ?_
  change fraction k n (MvPolynomial.C r) 1 = _
  simp [fraction]

private theorem dehomogenizedVariable_value (i j : Index n) :
    homogeneousToFraction k n _ (variable_powers_le_nonZeroDivisors k n i)
      (ratios k n i (dehomogenizedVariable k n i j)) =
    fraction k n (variablePolynomial k n j) (variablePolynomial k n i) := by
  by_cases h : j = i
  · subst j
    simp [dehomogenizedVariable, fraction, intoFraction_ne_zero k n (MvPolynomial.X_ne_zero i)]
  · simpa only [dehomogenizedVariable, dite_eq_right h, ratios, MvPolynomial.eval₂Hom_X'] using
      coordinateRatio_value k n i j

private theorem intoFraction_eval₂ :
    MvPolynomial.eval₂Hom ((intoFraction k n).comp MvPolynomial.C)
      (fun i ↦ intoFraction k n (variablePolynomial k n i)) = intoFraction k n := by
  apply MvPolynomial.ringHom_ext <;> intros <;> simp

private theorem eval₂_dehomogenize (i : Index n) :
    ((homogeneousToFraction k n _ (variable_powers_le_nonZeroDivisors k n i)).comp
      (ratios k n i)).comp (dehomogenize k n i) =
    MvPolynomial.eval₂Hom ((intoFraction k n).comp MvPolynomial.C)
      (fun j ↦ fraction k n (variablePolynomial k n j) (variablePolynomial k n i)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, dehomogenize, MvPolynomial.eval₂Hom_C,
      ratios, ratio_constant_value]
  · intro j
    simp only [RingHom.comp_apply, dehomogenize, MvPolynomial.eval₂Hom_X']
    exact dehomogenizedVariable_value k n i j

private theorem dehomogenized_homogeneous_value (i : Index n) (a : Polynomials k n)
    (d : ℕ) (ha : a ∈ grading k n d) :
    MvPolynomial.eval₂Hom ((intoFraction k n).comp MvPolynomial.C)
      (fun j ↦ fraction k n (variablePolynomial k n j) (variablePolynomial k n i)) a =
      fraction k n a (variablePolynomial k n i ^ d) := by
  let g := MvPolynomial.eval₂Hom ((intoFraction k n).comp MvPolynomial.C)
    (fun j ↦ fraction k n (variablePolynomial k n j) (variablePolynomial k n i))
  have hg (e : Index n →₀ ℕ) (he : e ∈ a.support) :
      g (MvPolynomial.monomial e (a.coeff e)) =
        fraction k n (MvPolynomial.monomial e (a.coeff e)) (variablePolynomial k n i ^ d) := by
    have hdeg : d = ∑ j ∈ e.support, e j :=
      MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support ha he
    conv_rhs => rw [fraction, ← intoFraction_eval₂ k n]
    simp only [g, MvPolynomial.eval₂Hom_monomial, fraction, Finsupp.prod, div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← hdeg,
      intoFraction_eval₂, map_pow, mul_div_assoc]
  change g a = fraction k n a _
  unfold fraction
  conv_lhs => rw [MvPolynomial.as_sum a]
  rw [map_sum]
  simp_rw [fraction] at hg
  rw [Finset.sum_congr rfl hg]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← map_sum, ← MvPolynomial.as_sum]

/-- The degree-zero ring of a single standard chart is its dehomogenized polynomial ring. -/
def singletonCoordinates (i : Index n) : SingletonRing k n i ≃+* CoordinatePolynomials k n i :=
  RingEquiv.ofRingHom (dehomogenizeSingleton k n i) (ratios k n i)
    (dehomogenize_comp_ratios k n i) (by
      apply RingHom.ext
      intro a
      obtain ⟨t, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
        _ (variable_degree k n i) a
      simp only [RingHom.comp_apply, RingHom.id_apply, dehomogenizeSingleton_mk]
      apply homogeneousToFraction_injective k n _ (variable_powers_le_nonZeroDivisors k n i)
      have h := DFunLike.congr_fun (eval₂_dehomogenize k n i) p
      rw [dehomogenized_homogeneous_value k n i p t (by simpa using hp)] at h
      refine h.trans ?_
      unfold homogeneousToFraction
      rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
        HomogeneousLocalization.Away.val_mk, localizationToFraction_mk])

theorem singletonCoordinates_ratio (i : Index n) (j : ChartVariables n i) :
    singletonCoordinates k n i (coordinateRatio k n i j.val) = MvPolynomial.X j := by
  change dehomogenizeSingleton k n i (coordinateRatio k n i j.val) = _
  rw [coordinateRatio, dehomogenizeSingleton_mk]
  simp [dehomogenize, dehomogenizedVariable, j.2]

private theorem invertedRatioProduct_value (J : Finset (Index n)) (i : Index n) :
    singletonCoordinates k n i
      (Away.isLocalizationElem (variable_degree k n i) (chartProduct_degree k n (J.erase i))) =
        ratioProduct k n J i := by
  change dehomogenizeSingleton k n i (Away.isLocalizationElem _ _) = _
  simp only [Away.isLocalizationElem, pow_one, dehomogenizeSingleton_mk]
  simp [chartProduct, ratioProduct, dehomogenize, MvPolynomial.eval₂Hom_X']

/-- After choosing a chart, its intersections invert the ratios for the other indices. -/
def intersectionCoordinates (J : Finset (Index n)) (i : Index n) (hi : i ∈ J) :
    ChartRing k n J ≃+* CoordinateLocalization k n J i := by
  let hf := variable_degree k n i
  let hg := chartProduct_degree k n (J.erase i)
  let he := chartProduct_eq_variable_mul_erase k n hi
  letI : Algebra (SingletonRing k n i) (ChartRing k n J) :=
    (HomogeneousLocalization.awayMap (grading k n) hg he).toAlgebra
  let t := Away.isLocalizationElem hf hg
  letI : IsLocalization.Away t (ChartRing k n J) :=
    Away.isLocalization_mul hf hg he (by decide)
  refine IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers t)
    (T := Submonoid.powers (ratioProduct k n J i)) _ _ (singletonCoordinates k n i) ?_
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (invertedRatioProduct_value k n J i)

@[simp] theorem twist_smul_apply (m : ℤ) (U : OpensOfProj k n)
    (r : structureSections k n U) (s : TwistSections k n m U) (x : U) :
    (r • s).val x = structureToFunctions k n U r x * s.val x := rfl

@[simp] theorem twist_add_apply (m : ℤ) (U : OpensOfProj k n)
    (r s : TwistSections k n m U) (x : U) :
    (r + s).val x = r.val x + s.val x := rfl

@[simp] theorem sectionMul_apply (m l : ℤ) (U : OpensOfProj k n)
    (a : TwistSections k n m U) (b : TwistSections k n l U) (x : U) :
    (sectionMul k n m l U a b).val x = a.val x * b.val x := rfl

open scoped TensorProduct MonoidalCategory

abbrev twistTensorPresheaf (m l : ℤ) : PresheafOfModulesOfCommRing (commStructurePresheaf k n) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (twistPresheaf k n m) (twistPresheaf k n l)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
def twistPresheafMultiplication (m l : ℤ) :
    twistTensorPresheaf k n m l ⟶ twistPresheaf k n (m + l) where
  app U := ModuleCat.MonoidalCategory.tensorLift (sectionMul k n m l U.unop)
    (fun a a' b ↦ Subtype.ext (funext fun x ↦ add_mul (a.val x) (a'.val x) (b.val x)))
    (fun r a b ↦ Subtype.ext (funext fun x ↦
      mul_assoc (structureToFunctions k n U.unop r x) (a.val x) (b.val x)))
    (fun a b b' ↦ Subtype.ext (funext fun x ↦ mul_add (a.val x) (b.val x) (b'.val x)))
    (fun r a b ↦ Subtype.ext (funext fun x ↦
      mul_left_comm (a.val x) (structureToFunctions k n U.unop r x) (b.val x)))
  naturality f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    rfl

theorem twistPresheafMultiplication_tmul (m l : ℤ) (U : OpensOfProj k n)
    (a : TwistSections k n m U) (b : TwistSections k n l U) :
    (twistPresheafMultiplication k n m l).app (op U) (a ⊗ₜ b) = sectionMul k n m l U a b :=
  rfl

/-- The tensor product sheaf, obtained by sheafifying the sectionwise tensor product. -/
def twistTensor (m l : ℤ) : SheafOfModules (moduleRingSheaf k n) :=
  (twistSheafification k n).obj (twistTensorPresheaf k n m l)

/-- Multiplication of homogeneous sections induces multiplication of the twists. -/
def twistMultiplication (m l : ℤ) :
    twistTensor k n m l ⟶ twistingSheaf k n (m + l) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (moduleRingSheaf k n).obj)
    (P := twistTensorPresheaf k n m l) (F := twistingSheaf k n (m + l))).symm
      (twistPresheafMultiplication k n m l)

set_option maxHeartbeats 600000 in
theorem twistMultiplication_presheaf (m l : ℤ) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (moduleRingSheaf k n).obj)
      (twistMultiplication k n m l) = twistPresheafMultiplication k n m l :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (moduleRingSheaf k n).obj)
    (P := twistTensorPresheaf k n m l) (F := twistingSheaf k n (m + l))).apply_symm_apply _

theorem chartRing_noetherian (J : Finset (Index n)) (hJ : J.Nonempty) :
    IsNoetherianRing (ChartRing k n J) := by
  obtain ⟨i, hi⟩ := hJ
  exact isNoetherianRing_of_ringEquiv _ (intersectionCoordinates k n J i hi).symm

private theorem is_degree_of_frame {J : Finset (Index n)} {i : Index n} (hi : i ∈ J)
    (m : ℤ) (a : ChartLocalization k n J) (r : ChartRing k n J)
    (h : chartToFraction k n J a = chartRingToFraction k n J r * frame k n i m) :
    ∃ b : DegreePiece k n J m, b.val = a := by
  obtain ⟨b, hb⟩ := (degreePiece_frame k n hi m _).mpr ⟨r, h⟩
  exact ⟨b, localizationToFraction_injective k n _ (powers_product_le_nonZeroDivisors k n J) hb⟩

/-- The homogeneous piece with its actual scalar action from the degree-zero ring. -/
def degreeSubmodule (J : Finset (Index n)) (hJ : J.Nonempty) (m : ℤ) :
    Submodule (ChartRing k n J) (ChartLocalization k n J) where
  carrier := {a | ∃ (p : Polynomials k n) (t d : ℕ),
    p ∈ grading k n d ∧ (d : ℤ) - (t * J.card : ℕ) = m ∧
    a = Localization.mk p (chartDenominator k n J t)}
  zero_mem' := by
    obtain ⟨i, hi⟩ := hJ
    obtain ⟨b, hb⟩ := is_degree_of_frame k n hi m 0 0 (by simp)
    exact hb ▸ b.property
  add_mem' {a b} ha hb := by
    obtain ⟨i, hi⟩ := hJ
    obtain ⟨r, hr⟩ := (degreePiece_frame k n hi m _).mp
      ⟨(⟨a, ha⟩ : DegreePiece k n J m), rfl⟩
    obtain ⟨s, hs⟩ := (degreePiece_frame k n hi m _).mp
      ⟨(⟨b, hb⟩ : DegreePiece k n J m), rfl⟩
    obtain ⟨p, hp⟩ := is_degree_of_frame k n hi m (a + b) (r + s) (by
      rw [map_add, map_add, hr, hs, add_mul])
    exact hp ▸ p.property
  smul_mem' r a ha := by
    obtain ⟨i, hi⟩ := hJ
    obtain ⟨s, hs⟩ := (degreePiece_frame k n hi m _).mp
      ⟨(⟨a, ha⟩ : DegreePiece k n J m), rfl⟩
    obtain ⟨p, hp⟩ := is_degree_of_frame k n hi m (r • a) (r * s) (by
      change chartToFraction k n J (algebraMap _ _ r * a) = _
      rw [map_mul, map_mul, hs]
      exact (mul_assoc _ _ _).symm)
    exact hp ▸ p.property

set_option backward.isDefEq.respectTransparency false in
/-- The comparison of actual degree pieces and sections is linear over the chart ring. -/
def chartTwistLinearEquiv (J : Finset (Index n)) (hJ : J.Nonempty) (m : ℤ) :
    letI := Module.compHom (TwistSections k n m (intersection k n J))
      (chartStructureEquiv k n J hJ).toRingHom
    degreeSubmodule k n J hJ m ≃ₗ[ChartRing k n J] TwistSections k n m (intersection k n J) := by
  letI := Module.compHom (TwistSections k n m (intersection k n J))
    (chartStructureEquiv k n J hJ).toRingHom
  exact { degreePieceSections k n J hJ m with
    map_add' := fun a b ↦ Subtype.ext (funext fun x ↦ by
      change (degreePieceSections k n J hJ m (a + b)).val x =
        (degreePieceSections k n J hJ m a).val x + (degreePieceSections k n J hJ m b).val x
      rw [degreePieceSections_value, degreePieceSections_value, degreePieceSections_value]
      exact (chartToFraction k n J).map_add _ _)
    map_smul' := fun r a ↦ Subtype.ext (funext fun x ↦ by
      change (degreePieceSections k n J hJ m (r • a)).val x =
        structureToFunctions k n _ (chartStructureEquiv k n J hJ r) x *
          (degreePieceSections k n J hJ m a).val x
      rw [degreePieceSections_value, degreePieceSections_value, chartStructureEquiv_value]
      exact (chartToFraction k n J).map_mul (algebraMap _ _ r) a.val) }


theorem chartRingRestriction_isLocalization {J K : Finset (Index n)} (h : J ⊆ K)
    (hJ : J.Nonempty) :
    letI := (chartRingRestriction k n h).toAlgebra
    IsLocalization.Away
      (Away.isLocalizationElem (chartProduct_degree k n J) (chartProduct_degree k n (K \ J)))
      (ChartRing k n K) :=
  Away.isLocalization_mul (chartProduct_degree k n J) (chartProduct_degree k n (K \ J))
    (chartProduct_eq_mul_sdiff k n h) (Finset.card_pos.mpr hJ).ne'

private theorem chartRingRestriction_val {J K : Finset (Index n)} (h : J ⊆ K)
    (a : ChartRing k n J) :
    (chartRingRestriction k n h a).val = localizationRestriction k n h a.val := by
  rw [chartRingRestriction, val_awayMap, localizationRestriction]

theorem chartRingRestriction_value {J K : Finset (Index n)} (h : J ⊆ K) (a : ChartRing k n J) :
    chartRingToFraction k n K (chartRingRestriction k n h a) = chartRingToFraction k n J a := by
  change chartToFraction k n K (chartRingRestriction k n h a).val =
    chartToFraction k n J a.val
  rw [chartRingRestriction_val, localizationRestriction_value]

theorem chartStructureEquiv_restrict {J K : Finset (Index n)} (h : J ⊆ K)
    (hJ : J.Nonempty) (hK : K.Nonempty) (a : ChartRing k n J) :
    (projectiveSpace k n).presheaf.map (homOfLE (intersection_antitone k n h)).op
      (chartStructureEquiv k n J hJ a) =
    chartStructureEquiv k n K hK (chartRingRestriction k n h a) := by
  apply structureToFunctions_injective
  funext x
  change structureToFunctions k n (intersection k n J) (chartStructureEquiv k n J hJ a)
    ⟨x, intersection_antitone k n h x.2⟩ = _
  rw [chartStructureEquiv_value, chartStructureEquiv_value, chartRingRestriction_value]

/-- Coordinates on the affine intersection, with its projective restriction map. -/
def chartCoordinateScheme (J : Finset (Index n)) (i : Index n) (hi : i ∈ J) :
    Scheme.Opens.toScheme (X := projectiveSpace k n) (intersection k n J) ≅
      Spec (CommRingCat.of (CoordinateLocalization k n J i)) :=
  chartScheme k n J ⟨i, hi⟩ ≪≫
    (Scheme.Spec.mapIso (intersectionCoordinates k n J i hi).symm.toCommRingCatIso.op)


theorem affineCharts : Expected.chartScheme.{u} := by
  intro k _ n J hJ
  exact ⟨chartScheme k n J hJ⟩

theorem affineCoordinateCharts : Expected.chartCoordinateScheme.{u} := by
  intro k _ n J i hi
  exact ⟨chartCoordinateScheme k n J i hi⟩

theorem singletonCoordinates_constant (i : Index n) (r : k) :
    singletonCoordinates k n i (constantInSingleton k n i r) = MvPolynomial.C r := by
  change dehomogenizeSingleton k n i (constantInSingleton k n i r) = _
  rw [constantInSingleton_eq, dehomogenizeSingleton_mk]
  exact MvPolynomial.eval₂Hom_C _ _ _

theorem singletonCoordinates_comparison : Expected.singletonCoordinates.{u} := by
  intro k _ n i
  exact ⟨singletonCoordinates k n i, singletonCoordinates_constant k n i,
    singletonCoordinates_ratio k n i⟩

theorem intersectionCoordinates_base (J : Finset (Index n)) (i : Index n) (hi : i ∈ J)
    (a : SingletonRing k n i) :
    intersectionCoordinates k n J i hi
        (awayMap (grading k n) (chartProduct_degree k n (J.erase i))
          (chartProduct_eq_variable_mul_erase k n hi) a) =
      algebraMap (CoordinatePolynomials k n i) (CoordinateLocalization k n J i)
        (singletonCoordinates k n i a) := by
  let : Algebra (SingletonRing k n i) (ChartRing k n J) :=
    (awayMap (grading k n) (chartProduct_degree k n (J.erase i))
      (chartProduct_eq_variable_mul_erase k n hi)).toAlgebra
  let : IsLocalization.Away
      (Away.isLocalizationElem (variable_degree k n i) (chartProduct_degree k n (J.erase i)))
      (ChartRing k n J) :=
    Away.isLocalization_mul (variable_degree k n i) (chartProduct_degree k n (J.erase i))
      (chartProduct_eq_variable_mul_erase k n hi) (by decide)
  unfold intersectionCoordinates
  exact IsLocalization.ringEquivOfRingEquiv_eq _ a

theorem intersectionCoordinates_comparison : Expected.intersectionCoordinates.{u} := by
  intro k _ n J i hi
  refine ⟨intersectionCoordinates k n J i hi, ?_, ?_⟩
  · intro r
    exact (intersectionCoordinates_base k n J i hi _).trans
      (congrArg (algebraMap _ _) (singletonCoordinates_constant k n i r))
  · intro j
    exact (intersectionCoordinates_base k n J i hi _).trans
      (congrArg (algebraMap _ _) (singletonCoordinates_ratio k n i j))

theorem chartStructure_comparison : Expected.chartStructureComparisons.{u} := by
  intro k _ n
  exact ⟨chartStructureEquiv k n, chartStructureEquiv_value k n,
    fun _ _ h ↦ chartStructureEquiv_restrict k n h⟩

theorem localizedTwist_comparison : Expected.localizedTwistSections.{u} := by
  intro k _ n
  refine ⟨degreePieceSections k n, degreePieceSections_value k n, ?_, ?_⟩
  · intro J K h hJ hK m p
    exact ⟨degreeRestriction k n h m p, rfl, degreePieceSections_restrict k n h hJ hK m p⟩
  · intro J hJ m l p q
    exact ⟨degreeMul k n J m l p q, rfl, fun x ↦
      (congrArg (fun s : TwistSections k n (m + l) (intersection k n J) ↦ s.val x)
        (sectionMul_degreePieceSections k n J hJ m l p q)).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The restriction to any subopen of a standard chart is the free rank-one sheaf.
The slice over that subopen is the site of its open subsets. -/
def twistTrivialization (i : Index n) (m : ℤ) (U : OpensOfProj k n) (hU : U ≤ chart k n i) :
    SheafOfModules.unit ((moduleRingSheaf k n).over U) ≅ (twistingSheaf k n m).over U := by
  let E (V : (Over U)ᵒᵖ) := frameEquiv k n i m (V.unop.hom.le.trans hU)
  refine
    { hom.val := {
        app := fun V ↦ (E V).toModuleIso.hom
        naturality := fun f ↦ ?_ }
      inv.val := {
        app := fun V ↦ (E V).toModuleIso.inv
        naturality := fun f ↦ ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply ModuleCat.Hom.ext
    apply DFunLike.ext
    intro r
    rfl
  · apply ModuleCat.Hom.ext
    apply DFunLike.ext
    intro s
    rename_i V W
    let h : W.unop.left ≤ V.unop.left := f.unop.left.le
    change (E W).symm (restriction k n h m s) =
      (projectiveSpace k n).presheaf.map (homOfLE h).op ((E V).symm s)
    apply (E W).injective
    rw [(E W).apply_symm_apply]
    exact (congrArg (restriction k n h m) ((E V).apply_symm_apply s).symm).trans
      (frameEquiv_restrict k n i m (V.unop.hom.le.trans hU) h ((E V).symm s))
  · apply SheafOfModules.Hom.ext
    apply PresheafOfModules.Hom.ext
    funext V
    apply ModuleCat.Hom.ext
    apply DFunLike.ext
    exact (E V).symm_apply_apply
  · apply SheafOfModules.Hom.ext
    apply PresheafOfModules.Hom.ext
    funext V
    apply ModuleCat.Hom.ext
    apply DFunLike.ext
    exact (E V).apply_symm_apply

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem twistingModules_comparison : Expected.twistingModules.{u} := by
  intro k _ n
  refine ⟨twistingSheaf k n, (fun m U ↦ Equiv.refl (TwistSections k n m U)),
    (fun i m _U h ↦ (frameEquiv k n i m h).toEquiv), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intro i j m U hi hj x
    have hframe :
        frameEquiv k n j m hj 1 = (⟨_, frame_isSection k n j m hj⟩ : TwistSections k n m U) := by
      apply Subtype.ext
      funext y
      rw [frameEquiv_apply, map_one]
      exact one_mul _
    change structureToFunctions k n U ((frameEquiv k n i m hi).symm
      (frameEquiv k n j m hj 1)) x = _
    rw [hframe]
    exact frameTransition_value k n i j m hi hj x
  · intro i m U hU
    refine ⟨twistTrivialization k n i m U hU, ?_⟩
    intro V r
    rfl
  · intro m l
    refine ⟨twistMultiplication k n m l, ?_⟩
    intro p U a b x
    change ((PresheafOfModules.sheafificationHomEquiv (𝟙 (moduleRingSheaf k n).obj)
      (twistMultiplication k n m l)).app (op U) (a ⊗ₜ b)).val x = _
    rw [twistMultiplication_presheaf]
    rfl

end DerivedFormalization.ProjectiveTwists
