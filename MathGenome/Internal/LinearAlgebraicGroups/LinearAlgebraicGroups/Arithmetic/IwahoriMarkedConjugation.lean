import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IwahoriMarkedConjugation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Gluing
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj TensorProduct WithZero

namespace LinearAlgebraicGroups.Arithmetic.IwahoriMarkedConjugation

open _root_.LinearAlgebraicGroups.Specs
open Specs.IwahoriMarkedConjugation
open Specs.ExceptionalAffineBuilding (lengthZeroNormalizer)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalIwahoriCongruence (localIntegers localIntegersInclusion integralRing
  CellValues cellValue)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (markedRootPoint markedWeylWord weylWordPerm)
open Specs.IntegralSemisimpleModel (Model Integers integerAlgebra cocharacter torusPoint)
open Specs.Pinning (BasedRootDatum)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat (sameLabel_conjugateIwahori)
open private splitIwahori_absoluteChart splitChartSigns splitCell_single splitRootChart
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

attribute [local instance] integerAlgebra

universe u

set_option Elab.async false

noncomputable section

private theorem genericPoint_dominant (K : Type u) [Field K] [ValuativeRel K] :
    IsSchemeTheoreticallyDominant (genericPoint K) := by
  let i := CommRingCat.ofHom (localIntegersInclusion K).hom.toRingHom
  let j := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  let q := Scheme.ΓSpecIso (CommRingCat.of (localIntegers K))
  have h : i ≫ j = q.inv ≫ (genericPoint K).appTop := Scheme.ΓSpecIso_inv_naturality i
  have he : (genericPoint K).appTop = q.hom ≫ i ≫ j := by
    rw [h, Iso.hom_inv_id_assoc]
  have hi : Function.Injective (genericPoint K).appTop := by
    rw [he]
    exact (ConcreteCategory.bijective_of_isIso j).injective.comp
      (Subtype.val_injective.comp (ConcreteCategory.bijective_of_isIso q.hom).injective)
  constructor
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot ((genericPoint K).appTop.hom)).mp hi

/-- The generic fibre detects equality of morphisms from a flat scheme to an affine scheme. -/
private theorem genericRestrictionInjective
    (K : Type u) [Field K] [ValuativeRel K] (X : Over (integerScheme K)) (Y : Scheme.{u})
    (hX : Flat X.hom) (hY : IsAffine Y) (f g : X.left ⟶ Y)
    (h : pullback.fst X.hom (genericPoint K) ≫ f = pullback.fst X.hom (genericPoint K) ≫ g) :
    f = g := by
  let j := pullback.fst X.hom (genericPoint K)
  let _ : IsSchemeTheoreticallyDominant (genericPoint K) := genericPoint_dominant K
  let _ : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.pullbackFst _ _
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  change f.appTop ≫ j.appTop = g.appTop ≫ j.appTop at h'
  exact CommRingCat.hom_ext (RingHom.ext fun x =>
    j.app_injective ⊤ (ConcreteCategory.congr_hom h' x))

section Gluing

variable {S Sη U X T : Scheme.{u}} (d : Sη ⟶ S)
    (x : X ⟶ S) (j : U ⟶ X)

/-- When the integral chart and the generic fibre cover a scheme, a map on
the chart that agrees with a map on the generic fibre glues uniquely. -/
theorem glueFromChartAndGeneric [IsOpenImmersion j] [IsOpenImmersion d]
    (hcover : Set.range j ∪ Set.range (pullback.fst x d) = Set.univ)
    (fU : U ⟶ T) (fη : pullback x d ⟶ T)
    (h : pullback.fst (j ≫ x) d ≫ fU =
      pullback.map (j ≫ x) d x d j (𝟙 Sη) (𝟙 S) (by simp) (by simp) ≫ fη) :
    ∃! f : X ⟶ T, j ≫ f = fU ∧ pullback.fst x d ≫ f = fη := by
  let k := pullback.fst x d
  let V : Bool → Scheme.{u} := fun i => if i then U else pullback x d
  let inc : (i : Bool) → V i ⟶ X := fun
    | true => j
    | false => k
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion)
    Bool V inc (fun z => by
      have hz : z ∈ Set.range j ∪ Set.range k := hcover.symm ▸ Set.mem_univ z
      rcases hz with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩)
    (fun i => by cases i <;> infer_instance)
  let f : (i : Bool) → V i ⟶ T := fun
    | true => fU
    | false => fη
  have mixed : pullback.fst j k ≫ fU = pullback.snd j k ≫ fη := by
    let a := pullback.fst j k
    let b := pullback.snd j k
    have hab : a ≫ j = b ≫ k := pullback.condition
    let l : pullback j k ⟶ pullback (j ≫ x) d :=
      pullback.lift a (b ≫ pullback.snd x d) (by
        simpa only [Category.assoc] using
          (congrArg (· ≫ x) hab).trans
            (Category.assoc _ _ _ |>.trans
              (congrArg (b ≫ ·) (pullback.condition (f := x) (g := d)))))
    let m := pullback.map (j ≫ x) d x d j (𝟙 Sη) (𝟙 S) (by simp) (by simp)
    have h₁ : l ≫ pullback.fst (j ≫ x) d = a := pullback.lift_fst _ _ _
    have h₂ : l ≫ m = b := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        dsimp only [m, pullback.map]
        rw [pullback.lift_fst, ← Category.assoc, h₁]
        exact hab
      · simp [m, l, pullback.map]
    calc
      a ≫ fU = l ≫ (pullback.fst (j ≫ x) d ≫ fU) := by rw [← Category.assoc, h₁]
      _ = l ≫ (m ≫ fη) := congrArg (l ≫ ·) h
      _ = b ≫ fη := by rw [← Category.assoc, h₂]
  have hf (i l : Bool) : pullback.fst (𝒰.f i) (𝒰.f l) ≫ f i =
      pullback.snd (𝒰.f i) (𝒰.f l) ≫ f l := by
    cases i <;> cases l
    · change pullback.fst k k ≫ fη = pullback.snd k k ≫ fη
      rw [(cancel_mono k).mp (pullback.condition (f := k) (g := k))]
    · change pullback.fst k j ≫ fη = pullback.snd k j ≫ fU
      simpa using congrArg ((pullbackSymmetry k j).hom ≫ ·) mixed.symm
    · exact mixed
    · change pullback.fst j j ≫ fU = pullback.snd j j ≫ fU
      rw [(cancel_mono j).mp (pullback.condition (f := j) (g := j))]
  refine ⟨𝒰.glueMorphisms f hf, ⟨𝒰.ι_glueMorphisms f hf true, 𝒰.ι_glueMorphisms f hf false⟩,
    fun g hg => 𝒰.hom_ext _ _ ?_⟩
  intro i
  cases i
  · exact hg.2.trans (𝒰.ι_glueMorphisms f hf false).symm
  · exact hg.1.trans (𝒰.ι_glueMorphisms f hf true).symm

end Gluing

section Representative

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  (Y : SplitLevel K c p p' e)

/-- Length-zero elements normalize the actual Iwahori, by the comparison for a
chosen lift and the equality of its affine label with that of the element. -/
theorem lengthZero_preservesI {r : FieldPoints M' K} (hr : r ∈ lengthZeroNormalizer Y.ad) :
    Y.ad.I.map (MulAut.conj r).toMonoidHom = Y.ad.I := by
  rcases hr with ⟨n, ⟨w, hw, hω⟩, rfl⟩
  let ω : alcoveStabilizer (ApartmentRoots.split E.datum ℚ)
      ((ApartmentRoots.split E.datum ℚ).alcove p') := ⟨w, hw⟩
  have hn : Y.ad.affine n = Y.ad.affine (Y.typeQuotient.lift ω) :=
    hω.symm.trans (Y.typeQuotient.affine_lift ω).symm
  exact (sameLabel_conjugateIwahori Y.ad hn).trans (Y.typeQuotient.preserves_I ω)

private theorem root_mem_iff (a : E.I) (z : K) :
    markedRootPoint M'.toIntegralMarking (integralRing K) a z ∈ Y.ad.I ↔
      normalizedValuation K z ≤ 1 ∧ (¬ E.base.IsPos a → normalizedValuation K z < 1) := by
  classical
  let C := Y.ad.chart
  let n := C.negative
  let p₁ := C.positive
  let R := integralRing K
  let v := normalizedValuation K
  let z₁ : CellValues E R n p₁ :=
    ((fun i => if n[i.val] = a then z else 0), 1, fun i => if p₁[i.val] = a then z else 0)
  have hs := splitChartSigns Y.ad Y.ad_points
  have hz := splitCell_single (M := M') (K := K) C.negative_enumerates C.positive_enumerates hs a z
  have hf := splitIwahori_absoluteChart Y.ad.localIwahori n p₁
    C.negative_enumerates C.positive_enumerates
    (markedRootPoint M'.toIntegralMarking R a z)
  have hz₁ : cellValue M'.toIntegralMarking R n p₁ z₁ =
      markedRootPoint M'.toIntegralMarking R a z := by
    have hz' := hz
    dsimp only [splitRootChart, Specs.ExceptionalAffineBruhat.RootSlots.coordinates] at hz'
    simp only [Units.val_one, map_one, one_mul, RingHom.id_apply, Function.update_apply] at hz'
    exact hz'
  have hi := (ExceptionalIwahoriCongruence.markedChart M'.toIntegralMarking n p₁
    C.negative_enumerates C.positive_enumerates).1 R
  rw [hf]
  constructor
  · rintro ⟨w, hw, _, hneg, hpos⟩
    obtain rfl : w = z₁ := hi (hw.trans hz₁.symm)
    by_cases ha : E.base.IsPos a
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((C.positive_enumerates.2 a).mpr ha)
      change p₁[i.val] = a at hi
      have h := hpos i
      change v (if p₁[i.val] = a then z else 0) ≤ 1 at h
      rw [ite_eq_left hi] at h
      exact ⟨h, fun h => (h ha).elim⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((C.negative_enumerates.2 a).mpr ha)
      change n[i.val] = a at hi
      have h := hneg i
      change v (if n[i.val] = a then z else 0) < 1 at h
      rw [ite_eq_left hi] at h
      exact ⟨h.le, fun _ => h⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨z₁, hz₁, fun χ => ?_, fun l => ?_, fun l => ?_⟩
    · simp [z₁]
    · change v (if n[l.val] = a then z else 0) < 1
      split_ifs with hl
      · exact h₂ ((C.negative_enumerates.2 a).mp (hl ▸ List.getElem_mem l.isLt))
      · simp [v]
    · change v (if p₁[l.val] = a then z else 0) ≤ 1
      split_ifs
      · exact h₁
      · simp [v]

open scoped Classical in
/-- The exponent used for a marked root parameter in the Iwahori chart. -/
def rootDepth (E : BasedRootDatum.{u}) (a : E.I) : ℕ :=
  if E.base.IsPos a then 0 else 1

private theorem root_mem_iff_uniformizer (π : Kˣ)
    (hπ : normalizedValuation K (π : K) = WithZero.exp (-1))
    (a : E.I) (z : K) :
    markedRootPoint M'.toIntegralMarking (integralRing K) a z ∈ Y.ad.I ↔
      normalizedValuation K z ≤ normalizedValuation K ((π : K) ^ rootDepth E a) := by
  classical
  rw [root_mem_iff Y, rootDepth]
  by_cases ha : E.base.IsPos a
  · simp [ha]
  · rw [ite_eq_right ha, pow_one, hπ]
    have hlt : ∀ x : ℤᵐ⁰, x < 1 ↔ x ≤ WithZero.exp (-1) := fun x => by
      simpa only [← WithZero.exp_add, show (-1 : ℤ) + 1 = 0 by decide, WithZero.exp_zero] using
        (WithZero.lt_mul_exp_iff_le (x := x) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_pos.ne')
    exact ⟨fun h => (hlt _).mp (h.2 ha), fun h => ⟨((hlt _).mpr h).le, fun _ => (hlt _).mpr h⟩⟩

private theorem unit_of_normalizedValue_one (x : K) (hx : normalizedValuation K x = 1) :
    ∃ v : (localIntegers K)ˣ, (localIntegersInclusion K).hom v.val = x := by
  let w := ValuativeRel.valuation K
  have hv : w x = 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
    simpa [normalizedValuation, w] using hx
  let a : localIntegers K := ⟨x, hv.le⟩
  let b : localIntegers K := ⟨x⁻¹, by change w x⁻¹ ≤ 1; simp [hv]⟩
  have hne : x ≠ 0 := fun h => by simp [h] at hx
  exact ⟨⟨a, b, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

/-- A marked root transport that normalizes the actual Iwahori becomes multiplication
by a unit in the two rescaled coordinates. The equality follows from the root
membership test and its transport in both directions. -/
theorem unit_of_iwahori_root_transport {r : FieldPoints M' K}
    (hr : r ∈ lengthZeroNormalizer Y.ad) (π : Kˣ)
    (hπ : normalizedValuation K (π : K) = WithZero.exp (-1))
    (a b : E.I) (m : Kˣ)
    (hm : ∀ z : K,
      MulAut.conj r (markedRootPoint M'.toIntegralMarking (integralRing K) a z) =
        markedRootPoint M'.toIntegralMarking (integralRing K) b ((m : K) * z)) :
    ∃ v : (localIntegers K)ˣ,
      (localIntegersInclusion K).hom v.val * (π : K) ^ rootDepth E b =
        (m : K) * (π : K) ^ rootDepth E a := by
  let s := MulAut.conj r
  have hs (g : FieldPoints M' K) : s g ∈ Y.ad.I ↔ g ∈ Y.ad.I := by
    have h := lengthZero_preservesI Y hr
    change Y.ad.I.map s.toMonoidHom = Y.ad.I at h
    calc
      s g ∈ Y.ad.I ↔ s g ∈ Y.ad.I.map s.toMonoidHom := by rw [h]
      _ ↔ g ∈ Y.ad.I := by
        rw [Subgroup.mem_map]
        exact ⟨fun ⟨x, hx, hxe⟩ => s.injective hxe ▸ hx, fun hg => ⟨g, hg, rfl⟩⟩
  let x : K := (π : K) ^ rootDepth E a
  let y : K := (π : K) ^ rootDepth E b
  let v := normalizedValuation K
  have hx : v x ≠ 0 := by simp [v, x]
  have hy : v y ≠ 0 := by simp [v, y]
  have h (z : K) : v ((m : K) * z) ≤ v y ↔ v z ≤ v x := by
    rw [← root_mem_iff_uniformizer Y π hπ a, ← root_mem_iff_uniformizer Y π hπ b,
      ← hm z]
    exact hs _
  have h₁ := (h x).mpr le_rfl
  have h₂ := (h ((m : K)⁻¹ * y)).mp (by rw [← mul_assoc, mul_inv_cancel₀ m.ne_zero, one_mul])
  have h₃ : v y ≤ v ((m : K) * x) := by
    calc
      v y = v (m : K) * v ((m : K)⁻¹ * y) := by simp [v, map_mul, m.ne_zero]
      _ ≤ v (m : K) * v x := mul_le_mul_of_nonneg_left h₂ zero_le
      _ = v ((m : K) * x) := (map_mul v _ _).symm
  have heq : v ((m : K) * x / y) = 1 := by
    rw [map_div₀, le_antisymm h₁ h₃, div_self hy]
  obtain ⟨u, hu⟩ := unit_of_normalizedValue_one ((m : K) * x / y) heq
  exact ⟨u, by rw [hu, div_mul_cancel₀ _ (pow_ne_zero _ π.ne_zero)]⟩

end Representative

section IntegralTransport

open Specs.ExceptionalIwahoriCongruence (changeRing changeRingHom integralRingMap)
open Specs.IntegralSemisimpleModel (TorusValues IntegralPoints IntegralAlgebra)
open Specs.ExceptionalMarkedRootDescent (markedWall)
open private markedWeylWord_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private torusPoint_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private scalarPoints_id from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

variable {D : BasedRootDatum.{u}} (M : Model D)

def weylWordCharacters (D : BasedRootDatum.{u}) (word : List D.I) : AddAut D.X :=
  word.foldr (fun i w => (D.datum.reflection i).toAddEquiv.trans w) (.refl _)

theorem markedWeylWord_torus
    (R : IntegralAlgebra.{u}) (word : List D.I) (t : TorusValues D R) :
    MulAut.conj (markedWeylWord M.toIntegralMarking R word)
      (torusPoint D R t ≫ M.torus.hom.hom) =
    torusPoint D R (t.comp (weylWordCharacters D word).toAddMonoidHom.toMultiplicative) ≫
      M.torus.hom.hom := by
  induction word with
  | nil =>
    simp only [markedWeylWord, List.map_nil, List.prod_nil, map_one, MulAut.one_apply]
    rfl
  | cons i word ih =>
    change MulAut.conj (markedWall M.toIntegralMarking R i 1 *
      markedWeylWord M.toIntegralMarking R word) _ = _
    rw [map_mul, MulAut.mul_apply, ih]
    let t₀ := t.comp (weylWordCharacters D word).toAddMonoidHom.toMultiplicative
    obtain ⟨he, hχ⟩ :=
      LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent.markedWallTorusReflection
        M.toIntegralMarking R i 1 t₀
    rw [MulAut.conj_apply, he]
    apply congrArg (fun v => torusPoint D R v ≫ M.torus.hom.hom)
    apply MonoidHom.ext
    intro x
    exact hχ x.toAdd

theorem markedRepresentative_baseChange
    {K : Type u} [Field K] (π : Kˣ) (y : D.Y) (word : List D.I) (R : TestAlgebra K)
    (r : FieldPoints M K)
    (hr : r = (torusPoint D (integralRing K) (cocharacter D y (integralRing K) π) ≫
        M.torus.hom.hom) * markedWeylWord M.toIntegralMarking (integralRing K) word) :
    changeRingHom M.group (integralRingMap (algebraMap K R)) r =
      (torusPoint D (integralRing R)
        (cocharacter D y (integralRing R) (Units.map (algebraMap K R).toMonoidHom π)) ≫
        M.torus.hom.hom) * markedWeylWord M.toIntegralMarking (integralRing R) word := by
  let f := integralRingMap (algebraMap K R)
  change changeRingHom M.group f r = _
  rw [hr, map_mul]
  apply congrArg₂ (· * ·)
  · let t := torusPoint D (integralRing K) (cocharacter D y (integralRing K) π)
    change IntegralSemisimpleModel.integralSpec.map f.op ≫ t ≫ M.torus.hom.hom = _
    have h := torusPoint_natural f (cocharacter D y (integralRing K) π)
    have hn : (Units.map f.hom.toRingHom).comp (cocharacter D y (integralRing K) π) =
        cocharacter D y (integralRing R) (Units.map (algebraMap K R).toMonoidHom π) := by
      apply MonoidHom.ext
      intro x
      change Units.map (algebraMap K R).toMonoidHom
          (π ^ D.datum.toLinearMap x.toAdd y) =
        Units.map (algebraMap K R).toMonoidHom π ^ D.datum.toLinearMap x.toAdd y
      exact map_zpow _ _ _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ M.torus.hom.hom) h).trans
        (congrArg (fun v => torusPoint D (integralRing R) v ≫ M.torus.hom.hom) hn))
  · exact markedWeylWord_map M.toIntegralMarking f word

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {E : BasedRootDatum.{u}} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  (Y : SplitLevel K c p p' e)

/-- A length-zero conjugation preserves the scaled root lines over every generic
test algebra. The scaling uniformizer can be chosen independently of the one
used in the representative. -/
theorem representative_transports_scaledRoots {r : FieldPoints M' K}
    (hr : IsMarkedRepresentative Y r) (π : Kˣ)
    (hπ : normalizedValuation K (π : K) = WithZero.exp (-1)) :
    ∃ w : Equiv.Perm E.I, ∃ v : E.I → (localIntegers K)ˣ,
      ∀ (R : TestAlgebra K) (a : E.I) (z : R),
        let rR := changeRingHom M'.group (integralRingMap (algebraMap K R)) r
        let d := algebraMap K R (π : K)
        let vR := algebraMap K R ((localIntegersInclusion K).hom (v a).val)
        MulAut.conj rR (markedRootPoint M'.toIntegralMarking (integralRing R)
          a (d ^ rootDepth E a * z)) =
            markedRootPoint M'.toIntegralMarking (integralRing R) (w a)
              (d ^ rootDepth E (w a) * (vR * z)) := by
  obtain ⟨hzero, ξ, y, word, _, hr⟩ := hr
  choose C hC using
    (fun a => LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent.integralWeylWordTransport M' word a)
  let w := weylWordPerm word
  let m (a : E.I) :=
    cocharacter E y (integralRing K) ξ (Multiplicative.ofAdd (E.datum.root (w a))) *
      Units.map (algebraMap Integers.{u} K).toMonoidHom (C a)
  have transport (R : TestAlgebra K) (a : E.I) (z : R) :
      MulAut.conj (changeRingHom M'.group (integralRingMap (algebraMap K R)) r)
        (markedRootPoint M'.toIntegralMarking (integralRing R) a z) =
      markedRootPoint M'.toIntegralMarking (integralRing R) (w a) (algebraMap K R (m a : K) * z) := by
    let t := cocharacter E y (integralRing R) (Units.map (algebraMap K R).toMonoidHom ξ)
    rw [markedRepresentative_baseChange M' ξ y word R r hr, map_mul, MulAut.mul_apply]
    simp only [MulAut.conj_apply]
    rw [hC a (integralRing R) z]
    refine (M'.conjugation (integralRing R) t (w a) _).trans ?_
    apply congrArg (markedRootPoint M'.toIntegralMarking (integralRing R) (w a))
    rw [← mul_assoc, Units.val_mul, map_mul]
    apply congrArg (· * z)
    apply congrArg₂ (fun (x y : R) => x * y)
    · let n := E.datum.toLinearMap (E.datum.root (w a)) y
      change ((Units.map (algebraMap K R).toMonoidHom ξ ^ n : Rˣ) : R) =
        algebraMap K R ((ξ ^ n : Kˣ) : K)
      exact congrArg (fun v : Rˣ => (v : R)) (map_zpow (Units.map (algebraMap K R).toMonoidHom) ξ n).symm
    · exact (map_intCast (algebraMap K R) (C a : Integers.{u}).down).symm
  have transportK (a : E.I) (z : K) :=
    transport (CommAlgCat.of K K) a z
  have hv (a : E.I) :=
    unit_of_iwahori_root_transport Y hzero π hπ a (w a) (m a) (by
      intro z
      have hh := transportK a z
      change MulAut.conj (scalarPoints M' (RingHom.id K) r)
        (markedRootPoint M'.toIntegralMarking (integralRing K) a z) =
        markedRootPoint M'.toIntegralMarking (integralRing K) (w a) ((m a : K) * z) at hh
      rw [scalarPoints_id] at hh
      exact hh)
  choose v hv using hv
  refine ⟨w, v, fun R a z => ?_⟩
  dsimp only
  rw [transport]
  apply congrArg (markedRootPoint M'.toIntegralMarking (integralRing R) (w a))
  have h := congrArg (algebraMap K R) (hv a)
  simp only [map_mul, map_pow] at h
  rw [← mul_assoc, ← h]
  ac_rfl

end IntegralTransport

section GenericGroupMaps

open CategoryTheory.CartesianMonoidalCategory CategoryTheory.Functor.Monoidal
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj

variable {K : Type u} [Field K] [ValuativeRel K]
local notation "Bₒ" => integerScheme K
set_option quotPrecheck false in
local notation "P" => Over.pullback (Specs.IwahoriMarkedConjugation.genericPoint K)

theorem eq_of_genericBaseChange {X Y : Over Bₒ} (hx : Flat X.hom) (hy : IsAffine Y.left)
    {f g : X ⟶ Y} (h : (P).map f = (P).map g) : f = g := by
  let i := Specs.IwahoriMarkedConjugation.genericPoint K
  apply Over.OverMorphism.ext
  apply genericRestrictionInjective K X Y.left hx hy
  have eq (m : X ⟶ Y) : ((Over.pullback i).map m).left ≫ pullback.fst Y.hom i =
      pullback.fst X.hom i ≫ m.left := by
    have hm := Over.pullback_map_left (k := m) i X
    exact (congrArg (· ≫ pullback.fst Y.hom i) hm).trans (pullback.lift_fst _ _ _)
  exact (eq f).symm.trans ((congrArg (fun (m : (Over.pullback i).obj X ⟶ (Over.pullback i).obj Y) => m.left ≫ pullback.fst Y.hom i) h).trans (eq g))

theorem tensor_flat {S : Scheme.{u}} {A B : Over S} (hA : Flat A.hom) (hB : Flat B.hom) :
    Flat (A ⊗ B).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

theorem tensor_affine {S : Scheme.{u}} {A B : Over S} (hS : IsAffine S)
    (hA : IsAffine A.left) (hB : IsAffine B.left) : IsAffine (A ⊗ B).left := by
  rw [Over.tensorObj_left]
  infer_instance

set_option synthInstance.maxHeartbeats 100000 in
theorem isMonHom_of_generic {X Y : Grp (Over Bₒ)}
    (hx : Flat X.X.hom) (hy : IsAffine Y.X.left)
    (f : X.X ⟶ Y.X)
    (g : (P).mapGrp.obj X ⟶ (P).mapGrp.obj Y)
    (hg : (P).map f = g.hom.hom) : IsMonHom f := by
  let P₁ := Over.pullback (Specs.IwahoriMarkedConjugation.genericPoint K)
  have : IsMonHom (P₁.map f) := by rw [hg]; exact g.hom.isMonHom_hom
  constructor
  · have hu : Flat ((𝟙_ (Over Bₒ))).hom := by change Flat (𝟙 Bₒ); infer_instance
    apply eq_of_genericBaseChange hu hy
    change P₁.map (η ≫ f) = P₁.map η
    simp [← Functor.obj.η_def_assoc, ← Functor.obj.η_def, ← cancel_epi (Functor.LaxMonoidal.ε P₁)]
  · apply eq_of_genericBaseChange (tensor_flat hx hx) hy
    change P₁.map (μ ≫ f) = P₁.map ((f ⊗ₘ f) ≫ μ)
    simp [← Functor.obj.μ_def_assoc, ← Functor.obj.μ_def, ← Functor.LaxMonoidal.μ_natural_assoc,
      ← cancel_epi (Functor.LaxMonoidal.μ P₁ ..)]

section CartesianGroup

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] (G : Grp C)

def conjugateBy (r : (𝟙_ C) ⟶ G.X) : G.X ⟶ G.X :=
  (toUnit G.X ≫ r) * 𝟙 G.X * (toUnit G.X ≫ r)⁻¹

@[simp] theorem conjugateBy_apply {X : C} (r : (𝟙_ C) ⟶ G.X) (x : X ⟶ G.X) :
    x ≫ conjugateBy G r = (toUnit X ≫ r) * x * (toUnit X ≫ r)⁻¹ := by
  simp only [conjugateBy, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id]
  have h : x ≫ toUnit G.X ≫ r = toUnit X ≫ r :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ r) (toUnit_unique (x ≫ toUnit G.X) (toUnit X)))
  rw [h]

theorem conjugateBy_isMonHom (r : (𝟙_ C) ⟶ G.X) : IsMonHom (conjugateBy G r) := by
  constructor
  · change (η : (𝟙_ C) ⟶ G.X) ≫ conjugateBy G r = η
    rw [conjugateBy_apply, MonObj.one_eq_one, mul_one, mul_inv_cancel]
  · let x := fst G.X G.X
    let y := snd G.X G.X
    let f := conjugateBy G r
    have h : x * y = μ[G.X] := by
      change lift x y ≫ μ[G.X] = μ[G.X]
      rw [lift_fst_snd, Category.id_comp]
    have h' : (f ⊗ₘ f) ≫ μ[G.X] = (x ≫ f) * (y ≫ f) := by
      change (f ⊗ₘ f) ≫ μ[G.X] = lift (x ≫ f) (y ≫ f) ≫ μ[G.X]
      rw [lift_fst_comp_snd_comp]
    change μ[G.X] ≫ f = (f ⊗ₘ f) ≫ μ[G.X]
    rw [h', ← h]
    change (x * y) ≫ conjugateBy G r =
      (x ≫ conjugateBy G r) * (y ≫ conjugateBy G r)
    rw [conjugateBy_apply, conjugateBy_apply, conjugateBy_apply]
    group

end CartesianGroup

end GenericGroupMaps


section GroupGluing

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj

variable {K : Type u} [Field K] [ValuativeRel K]
local notation "Bₒ" => integerScheme K
set_option quotPrecheck false in
local notation "dη" => Specs.IwahoriMarkedConjugation.genericPoint K
set_option quotPrecheck false in
local notation "P" => Over.pullback dη
set_option quotPrecheck false in
local notation "Pᵍ" => Specs.IwahoriMarkedConjugation.groupBaseChange
  (Specs.ExceptionalIwahoriCongruence.localIntegersInclusion K).hom.toRingHom

private theorem chartOverlap {U X S T Z : Scheme.{u}}
    (d : T ⟶ S) (j : U ⟶ X) (x : X ⟶ S) (u : U ⟶ S)
    (hu : j ≫ x = u) (fU : U ⟶ Z) (fT : pullback x d ⟶ Z)
    (h : pullback.fst u d ≫ fU =
      pullback.lift (pullback.fst u d ≫ j) (pullback.snd u d)
        (by rw [Category.assoc, hu, pullback.condition]) ≫ fT) :
    pullback.fst (j ≫ x) d ≫ fU =
      pullback.map (j ≫ x) d x d j (𝟙 T) (𝟙 S) (by simp) (by simp) ≫ fT := by
  subst u
  convert h using 1
  apply congrArg (· ≫ fT)
  apply pullback.hom_ext
  · rfl
  · simp [pullback.map]

/-- Extend a generic group map when its chart restriction already has an integral lift. -/
theorem extendGroupFromChart [(IsOpenImmersion dη)] {G H : Grp (Over Bₒ)}
    (hG : Flat G.X.hom) (hH : IsAffine H.X.left)
    {U : Over Bₒ} (j : U ⟶ G.X) [IsOpenImmersion j.left]
    (hcover : Set.range j.left ∪ Set.range (pullback.fst G.X.hom dη) = Set.univ)
    (fU : U ⟶ H.X) (fη : (Pᵍ).obj G ⟶ (Pᵍ).obj H)
    (hcomp : (P).map fU = (P).map j ≫ fη.hom.hom) :
    ∃ f : G ⟶ H, (Pᵍ).map f = fη := by
  let a := pullback.fst G.X.hom dη
  let b := pullback.fst H.X.hom dη
  let fη' : (P).obj G.X ⟶ (P).obj H.X := fη.hom.hom
  let au := pullback.fst U.hom dη
  have hf (V W : Over Bₒ) (f : V ⟶ W) :
      ((P).map f).left ≫ pullback.fst W.hom dη = pullback.fst V.hom dη ≫ f.left := by
    have he := Over.pullback_map_left (k := f) dη V
    exact (congrArg (· ≫ pullback.fst W.hom dη) he).trans (pullback.lift_fst _ _ _)
  obtain ⟨F, hF, _⟩ := glueFromChartAndGeneric dη G.X.hom j.left hcover fU.left (fη'.left ≫ b) (by
    have he : au ≫ fU.left = ((P).map j).left ≫ (fη'.left ≫ b) := by
      calc
        _ = ((P).map fU).left ≫ b := (hf _ _ fU).symm
        _ = _ := by
          have hh := congrArg (fun (m : (P).obj U ⟶ (P).obj H.X) => m.left ≫ b) hcomp
          exact hh.trans (Category.assoc _ _ _)
    exact chartOverlap dη j.left G.X.hom U.hom (Over.w j) fU.left (fη'.left ≫ b)
      (he.trans
        (congrArg (· ≫ (fη'.left ≫ b)) (Over.pullback_map_left (k := j) dη U))))
  have hOver : F ≫ H.X.hom = G.X.hom := by
    apply genericRestrictionInjective K G.X Bₒ hG inferInstance
    change a ≫ F ≫ H.X.hom = a ≫ G.X.hom
    have hx : fη'.left ≫ pullback.snd H.X.hom dη = pullback.snd G.X.hom dη := Over.w fη'
    rw [← Category.assoc, hF.2, Category.assoc, pullback.condition, ← Category.assoc, hx,
      ← pullback.condition]
  let f : G.X ⟶ H.X := Over.homMk F hOver
  have he : (P).map f = fη' := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (hf _ _ f).trans hF.2
    · exact (Over.w ((P).map f)).trans (Over.w fη').symm
  have hi : IsMonHom f := isMonHom_of_generic hG hH f fη he
  let g : G ⟶ H := Grp.homMk' ⟨f⟩
  exact ⟨g, Grp.hom_ext _ _ he⟩

end GroupGluing

section ChartGeometry

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj
open Specs.IntegralSemisimpleModel (AdditiveLine splitTorus)

open scoped ValuativeRel in
/-- The generic fibre of the local discrete valuation ring is open. -/
theorem genericPoint_isOpenImmersion (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : IsOpenImmersion (genericPoint K) := by
  let O := localIntegers K
  have : IsDiscreteValuationRing O := inferInstanceAs (IsDiscreteValuationRing 𝒪[K])
  let : Algebra O K := inferInstanceAs (Algebra 𝒪[K] K)
  have : IsFractionRing O K := inferInstanceAs (IsFractionRing 𝒪[K] K)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hle : Submonoid.powers π ≤ nonZeroDivisors O := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hπ.ne_zero)
  have : IsLocalization.Away π K := by
    apply (IsLocalization.iff_of_le_of_exists_dvd (S := K)
      (Submonoid.powers π) (nonZeroDivisors O) hle ?_).mpr inferInstance
    intro r hr
    obtain ⟨n, v, hv⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (mem_nonZeroDivisors_iff_ne_zero.mp hr) hπ
    refine ⟨π ^ n, ⟨n, rfl⟩, ↑v⁻¹, ?_⟩
    calc
      π ^ n = (↑v * ↑v⁻¹) * π ^ n := by simp
      _ = r * ↑v⁻¹ := by rw [hv]; ac_rfl
  exact IsOpenImmersion.of_isLocalization π

private theorem affine_markedRootProduct {D : BasedRootDatum.{u}} (L : AdditiveLine.{u})
    (l : List D.I) : IsAffine ((IntegralSemisimpleModel.product (fun _ : D.I => L.group.X) l).left) := by
  induction l with
  | nil =>
    change IsAffine (Spec (CommRingCat.of Integers.{u}))
    infer_instance
  | cons i l ih =>
    let G := IntegralSemisimpleModel.product (fun _ : D.I => L.group.X) l
    have hL : IsAffine L.group.X.left :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial Integers.{u}))))
    change IsAffine (L.group.X ⊗ G).left
    exact tensor_affine inferInstance hL ih

theorem affine_rootProductChart {D : BasedRootDatum.{u}} (M : Model D)
    (n p : List D.I) : IsAffine (rootProductChart M n p).left := by
  have hT : IsAffine (splitTorus D).X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra Integers.{u} (Multiplicative D.X)))))
  exact tensor_affine inferInstance (affine_markedRootProduct M.line n)
    (tensor_affine inferInstance hT (affine_markedRootProduct M.line p))

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {H : IwahoriModel Y} (C : ScaledRootChart H)
set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "U" => (Specs.IwahoriMarkedConjugation.changeBase (algebraMap Integers O)).obj (rootProductChart M' C.negative C.positive)

theorem scaledRootChart_affine : IsAffine (U).left := by
  let q := rootProductChart M' C.negative C.positive
  let d := Spec.map (CommRingCat.ofHom (algebraMap Integers O))
  have hq : IsAffine q.left := affine_rootProductChart M' C.negative C.positive
  change IsAffine (pullback q.hom d)
  exact isAffine_of_isAffineHom (pullback.snd q.hom d)

theorem scaledRootChart_flat : Flat (U).hom := by
  have : Smooth H.model.X.hom := H.smooth
  have : IsOpenImmersion C.chart.left := C.open_chart
  rw [← Over.w C.chart]
  infer_instance

end ChartGeometry

section BaseChangePoints

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj

variable {S T : Scheme.{u}} (d : T ⟶ S)

def forgetBasePoint (A : Over T) (G : Over S) :
    (A ⟶ (Over.pullback d).obj G) ≃ ((Over.map d).obj A ⟶ G) :=
  ((Over.mapPullbackAdj d).homEquiv A G).symm

theorem forgetBasePoint_left {A : Over T} {G : Over S}
    (x : A ⟶ (Over.pullback d).obj G) :
    (forgetBasePoint d A G x).left = x.left ≫ pullback.fst G.hom d := by
  change (((Over.mapPullbackAdj d).homEquiv A G).symm x).left = _
  rw [Adjunction.homEquiv_counit, Over.mapPullbackAdj_counit_app]
  rfl

theorem forgetBasePoint_comp {A : Over T} {G H : Over S}
    (x : A ⟶ (Over.pullback d).obj G) (f : G ⟶ H) :
    forgetBasePoint d A H (x ≫ (Over.pullback d).map f) =
      forgetBasePoint d A G x ≫ f := by
  exact (Over.mapPullbackAdj d).homEquiv_naturality_right_symm x f

set_option synthInstance.maxHeartbeats 100000 in
def forgetBaseGroupPoint (A : Over T) (G : Grp (Over S)) :
    (A ⟶ ((Over.pullback d).mapGrp.obj G).X) ≃* ((Over.map d).obj A ⟶ G.X) where
  toEquiv := forgetBasePoint d A G.X
  map_mul' x y := by
    let P := Over.pullback d
    let x' : A ⟶ P.obj G.X := x
    let y' : A ⟶ P.obj G.X := y
    let m := Functor.LaxMonoidal.μ P G.X G.X
    let t : A ⟶ P.obj (G.X ⊗ G.X) := lift x' y' ≫ m
    have he : forgetBasePoint d A (G.X ⊗ G.X) t =
        lift (forgetBasePoint d A G.X x) (forgetBasePoint d A G.X y) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [← forgetBasePoint_comp, lift_fst]
        have hi : t ≫ P.map (fst G.X G.X) = x' := by
          dsimp only [t, m]
          rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
        exact congrArg (forgetBasePoint d A G.X) hi
      · rw [← forgetBasePoint_comp, lift_snd]
        have hi : t ≫ P.map (snd G.X G.X) = y' := by
          dsimp only [t, m]
          rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
        exact congrArg (forgetBasePoint d A G.X) hi
    change forgetBasePoint d A G.X (t ≫ P.map μ[G.X]) = _
    rw [forgetBasePoint_comp, he]
    rfl

theorem forgetBasePoint_pre {A B : Over T} {G : Over S}
    (f : A ⟶ B) (x : B ⟶ (Over.pullback d).obj G) :
    forgetBasePoint d A G (f ≫ x) =
      (Over.map d).map f ≫ forgetBasePoint d B G x := by
  exact (Over.mapPullbackAdj d).homEquiv_naturality_left_symm f x

end BaseChangePoints

open Specs.IntegralSemisimpleModel (IntegralPoints)

abbrev specMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :=
  Spec.map (CommRingCat.ofHom f)

theorem specMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    specMap (g.comp f) = specMap g ≫ specMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)


section GenericPoints

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj
open Specs.IntegralSemisimpleModel (IntegralPoints integralSpec)

private def precomposePointIso {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {G : Grp C} {X Y : C} (f : X ≅ Y) : (Y ⟶ G.X) ≃* (X ⟶ G.X) where
  toFun x := f.hom ≫ x
  invFun x := f.inv ≫ x
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' x y := MonObj.comp_mul _ _ _

private def postcomposePointIso {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {G H : Grp C} (f : G ≅ H) (X : C) : (X ⟶ G.X) ≃* (X ⟶ H.X) where
  toEquiv := ((Grp.forget C).mapIso f).homToEquiv
  map_mul' x y := MonObj.mul_comp x y f.hom.hom.hom

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (H : IwahoriModel Y)

set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "dη" => Specs.IwahoriMarkedConjugation.genericPoint K
set_option quotPrecheck false in
local notation "iO" => specMap (algebraMap Integers O)
set_option quotPrecheck false in
local notation "Gη" => (Specs.IwahoriMarkedConjugation.groupBaseChange
  (localIntegersInclusion K).hom.toRingHom).obj H.model

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem genericTest_overIntegers (R : TestAlgebra K) :
    (genericTest R).hom ≫ iO = (integralSpec.obj (op (integralRing R))).hom := by
  let f := algebraMap K R
  let i : O →+* K := (localIntegersInclusion K).hom.toRingHom
  let j := algebraMap Integers O
  change (specMap f ≫ specMap i) ≫ specMap j = specMap (algebraMap Integers R)
  have h : (f.comp i).comp j = algebraMap Integers R := by
    apply RingHom.ext
    intro z
    change f (algebraMap Integers K z) = algebraMap Integers R z
    exact map_intCast f z.down
  exact ((congrArg (· ≫ specMap j) (specMap_comp i f).symm).trans (specMap_comp j (f.comp i)).symm).trans
    (congrArg (fun a : Integers →+* R => specMap a) h)

/-- The generic group comparison, as a multiplicative equivalence for every test algebra. -/
def genericFibrePoints (R : TestAlgebra K) :
    ((testSpec K).obj (op R) ⟶ (Gη).X) ≃* IntegralPoints M'.group (integralRing R) := by
  let X := (testSpec K).obj (op R)
  let A := (Specs.IwahoriMarkedConjugation.groupBaseChange (localIntegersInclusion K).hom.toRingHom)
  have : IsIso (A.map H.toIntegral) := H.genericIso
  let G := (Specs.IwahoriMarkedConjugation.groupBaseChange (algebraMap Integers O)).obj M'.group
  let I := (Over.map iO).obj (genericTest R)
  let j : integralSpec.obj (op (integralRing R)) ≅ I :=
    Over.isoMk (Iso.refl _) (by
      change (𝟙 _ ≫ (genericTest R).hom ≫ iO) = _
      rw [Category.id_comp]
      exact genericTest_overIntegers R)
  exact (postcomposePointIso (asIso (A.map H.toIntegral)) X).trans
    ((forgetBaseGroupPoint dη X G).trans
      ((forgetBaseGroupPoint iO (genericTest R) M'.group).trans (precomposePointIso j)))

set_option backward.isDefEq.respectTransparency false in
theorem genericFibrePoints_formula (R : TestAlgebra K) (x : (testSpec K).obj (op R) ⟶ (Gη).X) :
    let y := forgetBasePoint dη ((testSpec K).obj (op R)) H.model.X x
    genericFibrePoints H R x = H.genericImage (R := R) y := by
  intro y
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ (forgetBasePoint iO (genericTest R) _ (forgetBasePoint dη _ _
    (x ≫ (Over.pullback dη).map H.toIntegral.hom.hom))).left =
      y.left ≫ H.projection
  rw [Category.id_comp, forgetBasePoint_comp, forgetBasePoint_left]
  change (y.left ≫ H.toIntegral.hom.hom.left) ≫ pullback.fst M'.group.X.hom iO =
    y.left ≫ H.projection
  exact Category.assoc _ _ _

open Specs.ExceptionalIwahoriCongruence (changeRingHom integralRingMap)

private theorem genericImage_natural (R S : TestAlgebra K) (a : R ⟶ S)
    (x : genericTest R ⟶ H.model.X) :
    H.genericImage (R := S) ((Over.map dη).map ((testSpec K).map a.op) ≫ x) =
      changeRingHom M'.group (integralRingMap a.hom.toRingHom) (H.genericImage (R := R) x) := by
  apply Over.OverMorphism.ext
  change (specMap a.hom.toRingHom ≫ x.left) ≫ H.projection =
    specMap a.hom.toRingHom ≫ x.left ≫ H.projection
  exact Category.assoc _ _ _

private theorem genericFibrePoints_natural (R S : TestAlgebra K) (a : R ⟶ S)
    (x : (testSpec K).obj (op R) ⟶ (Gη).X) :
    genericFibrePoints H S ((testSpec K).map a.op ≫ x) =
      changeRingHom M'.group (integralRingMap a.hom.toRingHom) (genericFibrePoints H R x) := by
  rw [genericFibrePoints_formula, genericFibrePoints_formula]
  let x' : (testSpec K).obj (op R) ⟶ (Over.pullback dη).obj H.model.X := x
  have hn := forgetBasePoint_pre dη ((testSpec K).map a.op) x'
  exact (congrArg (fun t => H.genericImage (R := S) t) hn).trans
    (genericImage_natural H R S a (forgetBasePoint dη _ _ x'))

open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections

private def unitTestIso : (𝟙_ (SchemeOver K)) ≅
    (testSpec K).obj (op (CommAlgCat.of K K)) :=
  (groundIso (k := K)).symm

private def genericRepresentative (r : FieldPoints M' K) :
    (𝟙_ (SchemeOver K)) ⟶ (Gη).X :=
  (unitTestIso (K := K)).hom ≫ (genericFibrePoints H (CommAlgCat.of K K)).symm r

private def genericConjugation (r : FieldPoints M' K) : (Gη) ⟶ (Gη) := by
  letI := conjugateBy_isMonHom (Gη) (genericRepresentative H r)
  exact Grp.homMk' ⟨conjugateBy (Gη) (genericRepresentative H r)⟩

private theorem genericConjugation_formula (r : FieldPoints M' K) (R : TestAlgebra K)
    (x : (testSpec K).obj (op R) ⟶ (Gη).X) :
    genericFibrePoints H R (x ≫ (genericConjugation H r).hom.hom) =
      MulAut.conj (changeRingHom M'.group (integralRingMap (algebraMap K R)) r)
        (genericFibrePoints H R x) := by
  let a : CommAlgCat.of K K ⟶ R := CommAlgCat.ofHom (Algebra.ofId K R)
  let X := (testSpec K).obj (op R)
  let X₀ := (testSpec K).obj (op (CommAlgCat.of K K))
  have hterminal : IsTerminal X₀ :=
    (isTerminalTensorUnit (C := SchemeOver K)).ofIso (unitTestIso (K := K))
  have ha : toUnit X ≫ (unitTestIso (K := K)).hom = (testSpec K).map a.op :=
    hterminal.hom_ext _ _
  let q := (genericFibrePoints H (CommAlgCat.of K K)).symm r
  have hq : toUnit X ≫ genericRepresentative H r = (testSpec K).map a.op ≫ q :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) ha)
  have hR : genericFibrePoints H R (toUnit X ≫ genericRepresentative H r) =
      changeRingHom M'.group (integralRingMap (algebraMap K R)) r :=
    (congrArg (genericFibrePoints H R) hq).trans
      ((genericFibrePoints_natural H (CommAlgCat.of K K) R a q).trans
        (congrArg (changeRingHom M'.group (integralRingMap (algebraMap K R)))
          ((genericFibrePoints H (CommAlgCat.of K K)).apply_symm_apply r)))
  change genericFibrePoints H R (x ≫ conjugateBy (Gη) (genericRepresentative H r)) = _
  rw [conjugateBy_apply]
  simp only [map_mul, map_inv, MulAut.conj_apply]
  change genericFibrePoints H R (toUnit X ≫ genericRepresentative H r) * _ *
    (genericFibrePoints H R (toUnit X ≫ genericRepresentative H r))⁻¹ = _
  rw [hR]

private theorem extends_of_generic (r : FieldPoints M' K) (f : H.model ⟶ H.model)
    (h : (Specs.IwahoriMarkedConjugation.groupBaseChange (localIntegersInclusion K).hom.toRingHom).map f =
      genericConjugation H r) :
    ExtendsConjugation H r f := by
  intro R x
  let X := (testSpec K).obj (op R)
  let xη := (forgetBasePoint dη X H.model.X).symm x
  have hx : forgetBasePoint dη X H.model.X xη = x :=
    (forgetBasePoint dη X H.model.X).apply_symm_apply x
  have hf : (Over.pullback dη).map f.hom.hom = (genericConjugation H r).hom.hom :=
    congrArg (fun g => g.hom.hom) h
  have he : forgetBasePoint dη X H.model.X (xη ≫ (Over.pullback dη).map f.hom.hom) =
      x ≫ f.hom.hom :=
    (forgetBasePoint_comp dη xη f.hom.hom).trans (congrArg (· ≫ f.hom.hom) hx)
  change H.genericImage (R := R) (x ≫ f.hom.hom) =
    MulAut.conj (changeRingHom M'.group (integralRingMap (algebraMap K R)) r)
      (H.genericImage (R := R) x)
  calc
    _ = genericFibrePoints H R (xη ≫ (Over.pullback dη).map f.hom.hom) :=
      ((genericFibrePoints_formula H R _).trans
        (congrArg (fun t => H.genericImage (R := R) t) he)).symm
    _ = genericFibrePoints H R (xη ≫ (genericConjugation H r).hom.hom) :=
      congrArg (fun t => genericFibrePoints H R (xη ≫ t)) hf
    _ = _ := (genericConjugation_formula H r R xη).trans
      (congrArg _ ((genericFibrePoints_formula H R xη).trans
        (congrArg (fun t => H.genericImage (R := R) t) hx)))



end GenericPoints


section AffineTests

open Specs.ExceptionalIwahoriCongruence (residueHom changeRingHom integralRingMap)
open Specs.IntegralSemisimpleModel (integralSpec IntegralPoints fibre forgetFibrePoint)

private theorem affine_hasTest {A : Type u} [CommRing A]
    (X : Over (Spec (CommRingCat.of A))) (hX : IsAffine X.left) :
    ∃ R : CommAlgCat.{u} A, Nonempty ((algSpec (CommRingCat.of A)).obj (op R) ≅ X) := by
  obtain ⟨T, ⟨i⟩⟩ := (essImage_algSpec (R := CommRingCat.of A)).mpr hX
  exact ⟨T.unop, ⟨i⟩⟩

private theorem specMap_injective {A B : Type u} [CommRing A] [CommRing B] :
    Function.Injective (specMap : (A →+* B) → _) := by
  intro a b h
  have he : (CommRingCat.ofHom a).op = (CommRingCat.ofHom b).op :=
    Spec.fullyFaithful.map_injective h
  exact congrArg (fun f => f.unop.hom) he

private theorem affineTest_map {A B : Type u} [CommRing A] [CommRing B]
    (d : A →+* B) (R : CommAlgCat.{u} A) (S : CommAlgCat.{u} B)
    (x : (Over.map (specMap d)).obj ((algSpec (CommRingCat.of B)).obj (op S)) ⟶
      (algSpec (CommRingCat.of A)).obj (op R)) :
    ∃ a : R →+* S, x.left = specMap a ∧ a.comp (algebraMap A R) = (algebraMap B S).comp d := by
  let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) := x.left
  let a := (Spec.fullyFaithful.preimage t).unop.hom
  have ha : specMap a = x.left := Spec.fullyFaithful.map_preimage t
  refine ⟨a, ha.symm, specMap_injective ?_⟩
  rw [specMap_comp, specMap_comp, ha]
  exact Over.w x

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (H : IwahoriModel Y)

set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "iO" => specMap (algebraMap Integers O)
set_option quotPrecheck false in
local notation "Aₒ" => (Specs.IwahoriMarkedConjugation.groupBaseChange (algebraMap Integers O)).obj M'.group
set_option quotPrecheck false in
local notation "κ" => residue K
set_option quotPrecheck false in
local notation "red" => (residueHom O).hom.toRingHom
set_option quotPrecheck false in
local notation "Q" => Over.pullback (specMap red)

private def integralProjection (R : CommAlgCat.{u} O) :
    (integerTest R ⟶ (Aₒ).X) ≃* IntegralPoints M'.group (integralRing R) := by
  let j : integralSpec.obj (op (integralRing R)) ≅ (Over.map iO).obj (integerTest R) :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (specMap (algebraMap O R) ≫ iO) = specMap (algebraMap Integers R)
      rw [Category.id_comp, ← specMap_comp]
      exact congrArg specMap (RingHom.ext (fun z => map_intCast (algebraMap O R) z.down)))
  exact (forgetBaseGroupPoint iO (integerTest R) M'.group).trans (precomposePointIso j)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem integralProjection_left (R : CommAlgCat.{u} O) (g : integerTest R ⟶ (Aₒ).X) :
    (integralProjection R g).left = g.left ≫ pullback.fst M'.group.X.hom iO := by
  let g' : integerTest R ⟶ (Over.pullback iO).obj M'.group.X := g
  change 𝟙 _ ≫ (forgetBasePoint iO (integerTest R) M'.group.X g').left = _
  exact (Category.id_comp _).trans (forgetBasePoint_left iO g')

private theorem specialProjection_left (R : TestAlgebra κ)
    (x : (testSpec κ).obj (op R) ⟶ (Q).obj (Aₒ).X) :
    (forgetFibrePoint M'.group R (x ≫ H.residueIso.hom.hom.hom)).left =
      x.left ≫ pullback.fst (Aₒ).X.hom (specMap red) ≫ pullback.fst M'.group.X.hom iO := by
  change (x.left ≫ H.residueIso.hom.hom.hom.left) ≫
    pullback.fst M'.group.X.hom (specMap (algebraMap Integers κ)) = _
  exact (Category.assoc _ _ _).trans (congrArg (x.left ≫ ·) H.residueIso_overIntegral)

private theorem flatTest_lift (R : CommAlgCat.{u} O) (hR : Flat (integerTest R).hom)
    (g : integerTest R ⟶ (Aₒ).X)
    (h : ∀ (S : TestAlgebra κ) (a : R →+* S),
      a.comp (algebraMap O R) = (algebraMap κ S).comp red →
      changeRingHom M'.group (integralRingMap a) (integralProjection R g) ∈
        ExceptionalIwahoriImageComparison.markedPositiveBorel Y.ad.localIwahori.residueFibre S) :
    ∃ f : integerTest R ⟶ H.model.X, f ≫ H.toIntegral.hom.hom = g := by
  apply ExistsUnique.exists
  apply (H.universal (integerTest R) hR g).mp
  have : IsAffine (integerTest R).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have hA : IsAffine ((Q).obj (integerTest R)).left := by
    change IsAffine (pullback (integerTest R).hom (specMap red))
    exact isAffine_of_isAffineHom (pullback.snd (integerTest R).hom (specMap red))
  obtain ⟨S, ⟨j⟩⟩ := affine_hasTest ((Q).obj (integerTest R)) hA
  let x := forgetBasePoint (specMap red) ((testSpec κ).obj (op S)) (integerTest R) j.hom
  obtain ⟨a, ha, ha'⟩ := affineTest_map red R S x
  have he : j.hom.left ≫ pullback.fst (integerTest R).hom (specMap red) = specMap a :=
    (forgetBasePoint_left (specMap red) j.hom).symm.trans ha
  have hy : forgetFibrePoint M'.group S
      ((j.hom ≫ (Q).map g) ≫ H.residueIso.hom.hom.hom) =
        changeRingHom M'.group (integralRingMap a) (integralProjection R g) := by
    apply Over.OverMorphism.ext
    rw [specialProjection_left H S, Over.comp_left, Category.assoc]
    let A := (Over.pullback iO).obj M'.group.X
    let g' : integerTest R ⟶ A := g
    let pR := pullback.fst (integerTest R).hom (specMap red)
    let pA := pullback.fst A.hom (specMap red)
    let pi := pullback.fst M'.group.X.hom iO
    have hg : ((Q).map g').left ≫ pA = pR ≫ g'.left :=
      (congrArg (· ≫ pA) (Over.pullback_map_left (k := g') (specMap red) (integerTest R))).trans
        (pullback.lift_fst _ _ _)
    change j.hom.left ≫ ((Q).map g').left ≫ pA ≫ pi = specMap a ≫ (integralProjection R g).left
    calc
      _ = j.hom.left ≫ (((Q).map g').left ≫ pA) ≫ pi :=
        congrArg (j.hom.left ≫ ·) (Category.assoc _ _ _).symm
      _ = (j.hom.left ≫ pR) ≫ g'.left ≫ pi := by rw [hg, Category.assoc, Category.assoc]
      _ = _ := by rw [he, integralProjection_left] <;> rfl
  have hb := h S a ha'
  rw [← hy, ← H.borel_marked S] at hb
  obtain ⟨b, hb⟩ := hb
  refine ⟨j.inv ≫ b, ?_⟩
  have hb' := (LinearAlgebraicGroups.Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective
    M'.group S).injective hb
  have hb'' : b ≫ H.borel.inclusion.hom.hom = j.hom ≫ (Q).map g :=
    (cancel_mono H.residueIso.hom.hom.hom).mp ((Category.assoc _ _ _).trans hb')
  change (j.inv ≫ b) ≫ H.borel.inclusion.hom.hom = (Q).map g
  exact (Category.assoc _ _ _).trans
    ((congrArg (j.inv ≫ ·) hb'').trans (j.inv_hom_id_assoc ((Q).map g)))


end AffineTests

section ChartValues

open Specs.IntegralSemisimpleModel (TorusValues IntegralPoints IntegralMarking)
open Specs.ExceptionalIwahoriCongruence (changeRingHom integralRingMap markedRootFactors residueHom)
open Specs.ExceptionalIwahoriImageComparison (markedPositiveBorel)
open Specs.ExceptionalMarkedRootDescent (orderedRootPoint)
open LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison (markedPositiveBorelCoordinates)
open private cellValue_eq_mul rootWord_eq_prod torusPoint_natural torus_commutes from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private markedRootPoint_map markedRootPoint_zero fibrePointEquiv from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private markedRootPoint_single from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private normalizedValuation_lt_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {H : IwahoriModel Y} (C : ScaledRootChart H)

set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "red" => (residueHom O).hom.toRingHom
set_option quotPrecheck false in
local notation "inc" => (localIntegersInclusion K).hom.toRingHom

/-- The torus and ordered root factors are transported independently. Multiplication
uses the original order even when the permutation interchanges the signs. -/
private structure ChartTransport where
  perm : Equiv.Perm E.I
  unit : E.I → Oˣ
  chars : AddAut E.X

private def ChartTransport.identity : ChartTransport (K := K) (E := E) :=
  ⟨Equiv.refl _, fun _ => 1, AddEquiv.refl _⟩

private def ChartTransport.inverse (T : ChartTransport (K := K) (E := E)) :
    ChartTransport (K := K) (E := E) :=
  ⟨T.perm.symm, fun a => (T.unit (T.perm.symm a))⁻¹, T.chars.symm⟩

private def rootFactor {R : Type u} [CommRing R] (a : O →+* R)
    (T : ChartTransport (K := K) (E := E)) (i : E.I) (z : R) :
    IntegralPoints M'.group (integralRing R) :=
  markedRootPoint M'.toIntegralMarking (integralRing R) (T.perm i)
    (a C.uniformizer ^ rootDepth E (T.perm i) * (a (T.unit i).val * z))

private def torusFactor {R : Type u} [CommRing R] (T : ChartTransport (K := K) (E := E))
    (t : TorusValues E (integralRing R)) : IntegralPoints M'.group (integralRing R) :=
  torusPoint E (integralRing R) (t.comp T.chars.toAddMonoidHom.toMultiplicative) ≫
    M'.torus.hom.hom

private def chartValue {R : Type u} [CommRing R] (a : O →+* R) (T : ChartTransport (K := K) (E := E))
    (z : CellValues E (integralRing R) C.negative C.positive) :
    IntegralPoints M'.group (integralRing R) :=
  (List.ofFn (fun i : Fin C.negative.length => rootFactor C a T C.negative[i] (z.1 i))).prod *
    (torusFactor (M' := M') T z.2.1 *
      (List.ofFn (fun i : Fin C.positive.length => rootFactor C a T C.positive[i] (z.2.2 i))).prod)

private theorem chartValue_identity {R : Type u} [CommRing R] (a : O →+* R)
    (z : CellValues E (integralRing R) C.negative C.positive) :
    chartValue C a ChartTransport.identity z =
      cellValue M'.toIntegralMarking (integralRing R) C.negative C.positive
        ((fun i => a C.uniformizer * z.1 i), z.2.1, z.2.2) := by
  classical
  rw [cellValue_eq_mul, rootWord_eq_prod, rootWord_eq_prod]
  have hw (l : List E.I) (x : Fin l.length → R) :
      (List.ofFn (fun i : Fin l.length => rootFactor (M' := M') C a ChartTransport.identity
        l[i] (x i))).prod =
      (markedRootFactors M'.toIntegralMarking (integralRing R) l
        (fun i => a C.uniformizer ^ rootDepth E l[i] * x i)).prod := by
    unfold markedRootFactors
    congr 1
    apply congrArg List.ofFn
    funext i
    simp [rootFactor, ChartTransport.identity, map_one, markedRootPoint]
  rw [chartValue, hw, hw]
  have hn : (fun i : Fin C.negative.length => a C.uniformizer ^ rootDepth E C.negative[i] * z.1 i) =
      fun i => a C.uniformizer * z.1 i := by
    funext i
    have hi : ¬ E.base.IsPos C.negative[i.val] :=
      (C.negative_enumerates.2 _).mp (List.getElem_mem i.isLt)
    change a C.uniformizer ^ rootDepth E C.negative[i.val] * z.1 i = _
    simp only [rootDepth, ite_eq_right hi, pow_one]
  have hp : (fun i : Fin C.positive.length => a C.uniformizer ^ rootDepth E C.positive[i] * z.2.2 i) =
      z.2.2 := by
    funext i
    have hi : E.base.IsPos C.positive[i.val] :=
      (C.positive_enumerates.2 _).mp (List.getElem_mem i.isLt)
    change a C.uniformizer ^ rootDepth E C.positive[i.val] * z.2.2 i = _
    simp only [rootDepth, ite_eq_left hi, pow_zero, one_mul]
  rw [hn, hp] <;> rfl

private def mapCell {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (z : CellValues E (integralRing R) C.negative C.positive) :
    CellValues E (integralRing S) C.negative C.positive :=
  (fun i => f (z.1 i), (Units.map f.toMonoidHom).comp z.2.1, fun i => f (z.2.2 i))

private theorem chartValue_map {R S : Type u} [CommRing R] [CommRing S] (a : O →+* R)
    (f : R →+* S) (T : ChartTransport (K := K) (E := E))
    (z : CellValues E (integralRing R) C.negative C.positive) :
    changeRingHom M'.group (integralRingMap f) (chartValue C a T z) =
      chartValue C (f.comp a) T (mapCell C f z) := by
  have hr (i : E.I) (x : R) :
      changeRingHom M'.group (integralRingMap f) (rootFactor C a T i x) =
        rootFactor C (f.comp a) T i (f x) := by
    unfold rootFactor
    refine (markedRootPoint_map M'.toIntegralMarking (integralRingMap f) _ _).trans ?_
    apply congrArg (markedRootPoint M'.toIntegralMarking (integralRing S) _)
    change f (_ ^ rootDepth E (T.perm i) * (_ * x)) = _
    simp only [RingHom.comp_apply, map_mul, map_pow]
  have ht : changeRingHom M'.group (integralRingMap f) (torusFactor (M' := M') T z.2.1) =
      torusFactor T (mapCell C f z).2.1 := by
    let t := z.2.1.comp T.chars.toAddMonoidHom.toMultiplicative
    change IntegralSemisimpleModel.integralSpec.map (integralRingMap f).op ≫
      (torusPoint E (integralRing R) t ≫ M'.torus.hom.hom) = _
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ M'.torus.hom.hom) (torusPoint_natural (integralRingMap f) t))
  simp only [chartValue, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, hr, ht, mapCell]

private def pointBorel {κ : Type u} [Field κ]
    (F : ExceptionalMarkedRootDescent.MarkedFibre M' κ) (R : TestAlgebra κ) :
    Subgroup (IntegralPoints M'.group (integralRing R)) :=
  (SubgroupSections F.realization.pinned.pair.B ((testSpec κ).obj (op R))).map
    (fibrePointEquiv F R).toMonoidHom

private theorem pointBorel_coe {κ : Type u} [Field κ]
    (F : ExceptionalMarkedRootDescent.MarkedFibre M' κ) (R : TestAlgebra κ) :
    (pointBorel F R : Set _) = markedPositiveBorel F R := by
  ext g
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b ≫ F.realization.pinned.pair.B.inclusion.hom.hom, ⟨b, rfl⟩, rfl⟩

private theorem chartValue_reduction (S : TestAlgebra (residue K)) (a : O →+* S)
    (ha : a C.uniformizer = 0) (T : ChartTransport (K := K) (E := E))
    (z : CellValues E (integralRing S) C.negative C.positive) :
    chartValue C a T z ∈ markedPositiveBorel Y.ad.localIwahori.residueFibre S := by
  classical
  let F := Y.ad.localIwahori.residueFibre
  let B := pointBorel F S
  have hB : (B : Set (IntegralPoints M'.group (integralRing S))) =
      markedPositiveBorel F S := pointBorel_coe F S
  have hcoord := markedPositiveBorelCoordinates F S C.positive C.positive_enumerates
  have hr (i : E.I) (x : S) : rootFactor C a T i x ∈ B := by
    let b := T.perm i
    by_cases hb : E.base.IsPos b
    · change rootFactor C a T i x ∈ (B : Set _)
      rw [hB, hcoord]
      let y := a C.uniformizer ^ rootDepth E b * (a (T.unit i).val * x)
      refine ⟨(1, fun j => if j = b then y else 0), ?_⟩
      have hm : b ∈ C.positive := (C.positive_enumerates.2 b).mpr hb
      change ((1 : IntegralPoints (IntegralSemisimpleModel.splitTorus E) (integralRing S)) ≫
          M'.torus.hom.hom) * orderedRootPoint M'.toIntegralMarking (integralRing S)
            C.positive (fun j => if j = b then y else 0) = _
      rw [markedRootPoint_single _ _ _ C.positive_enumerates.1, ite_eq_left hm, MonObj.one_comp, one_mul] <;> rfl
    · have hz : a C.uniformizer ^ rootDepth E b * (a (T.unit i).val * x) = 0 := by
        simp [rootDepth, hb, ha]
      have he : rootFactor C a T i x = 1 := by
        unfold rootFactor
        rw [hz, markedRootPoint_zero]
      rw [he]
      exact B.one_mem
  have ht : torusFactor (M' := M') T z.2.1 ∈ B := by
    change torusFactor (M' := M') T z.2.1 ∈ (B : Set _)
    rw [hB, hcoord]
    refine ⟨(torusPoint E (integralRing S) (z.2.1.comp T.chars.toAddMonoidHom.toMultiplicative),
      fun _ => 0), ?_⟩
    simp [orderedRootPoint, markedRootPoint_zero, torusFactor]
  rw [← hB]
  have hl (l : List E.I) (x : Fin l.length → S) :
      (List.ofFn (fun i : Fin l.length => rootFactor C a T l[i] (x i))).prod ∈ B := by
    apply B.list_prod_mem
    intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hr l[i] (x i)
  exact B.mul_mem (hl C.negative z.1) (B.mul_mem ht (hl C.positive z.2.2))

private theorem uniformizer_residue_zero : red C.uniformizer = 0 := by
  apply (IsLocalRing.residue_eq_zero_iff C.uniformizer).mpr
  apply (ValuativeRel.valuation K).mem_maximalIdeal_iff.mpr
  apply (normalizedValuation_lt_one K _).mp
  rw [C.uniformizer_value]
  exact WithZero.exp_lt_one_iff.mpr (by decide)

end ChartValues

section RepresentativeOnChart

open Specs.IntegralSemisimpleModel (TorusValues)
open Specs.ExceptionalIwahoriCongruence (changeRingHom integralRingMap)
open private torus_commutes from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {H : IwahoriModel Y} (C : ScaledRootChart H)

set_option quotPrecheck false in
local notation "inc" => (localIntegersInclusion K).hom.toRingHom

private def TransportsChart (r : FieldPoints M' K) (T : ChartTransport (K := K) (E := E)) : Prop :=
  ∀ R : TestAlgebra K,
    let a := (algebraMap K R).comp inc
    let g := changeRingHom M'.group (integralRingMap (algebraMap K R)) r
    (∀ (i : E.I) (z : R),
      MulAut.conj g (rootFactor C a ChartTransport.identity i z) = rootFactor C a T i z) ∧
    (∀ t : TorusValues E (integralRing R),
      MulAut.conj g (torusFactor (K := K) (M' := M') ChartTransport.identity t) = torusFactor T t)

private theorem TransportsChart.chart (r : FieldPoints M' K)
    (T : ChartTransport (K := K) (E := E)) (h : TransportsChart C r T)
    (R : TestAlgebra K) (z : CellValues E (integralRing R) C.negative C.positive) :
    let a := (algebraMap K R).comp inc
    let g := changeRingHom M'.group (integralRingMap (algebraMap K R)) r
    MulAut.conj g (chartValue C a ChartTransport.identity z) = chartValue C a T z := by
  obtain ⟨hr, ht⟩ := h R
  simp only [chartValue, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, hr, ht]

private theorem representative_chartTransport (r : FieldPoints M' K)
    (hr : IsMarkedRepresentative Y r) :
    ∃ T : ChartTransport (K := K) (E := E), TransportsChart C r T := by
  have hπ : (C.uniformizer : K) ≠ 0 := by
    intro h
    have hs := C.uniformizer_value
    rw [h, map_zero] at hs
    exact WithZero.exp_pos.ne hs
  let π := Units.mk0 (C.uniformizer : K) hπ
  obtain ⟨w, v, hroot⟩ := representative_transports_scaledRoots M Y hr π C.uniformizer_value
  obtain ⟨_, ξ, y, word, _, hrep⟩ := hr
  refine ⟨⟨w, v, weylWordCharacters E word⟩, fun R => ⟨?_, ?_⟩⟩
  · intro i z
    have hval : (π : K) = inc C.uniformizer := rfl
    have hinc (x : localIntegers K) : (localIntegersInclusion K).hom x = inc x := rfl
    simpa only [rootFactor, ChartTransport.identity, Equiv.refl_apply, Units.val_one, map_one,
      one_mul, RingHom.comp_apply, hval, hinc] using hroot R i z
  · intro t
    let a := cocharacter E y (integralRing R) (Units.map (algebraMap K R).toMonoidHom ξ)
    change MulAut.conj (changeRingHom M'.group (integralRingMap (algebraMap K R)) r)
      (torusPoint E (integralRing R) t ≫ M'.torus.hom.hom) =
        torusPoint E (integralRing R)
          (t.comp (weylWordCharacters E word).toAddMonoidHom.toMultiplicative) ≫
          M'.torus.hom.hom
    rw [markedRepresentative_baseChange M' ξ y word R r hrep, map_mul, MulAut.mul_apply,
      markedWeylWord_torus]
    have hc := torus_commutes M'.toIntegralMarking (integralRing R) a
      (t.comp (weylWordCharacters E word).toAddMonoidHom.toMultiplicative)
    rw [MulAut.conj_apply, hc.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem TransportsChart.inv (r : FieldPoints M' K)
    (T : ChartTransport (K := K) (E := E)) (h : TransportsChart C r T) :
    TransportsChart C r⁻¹ T.inverse := by
  intro R
  let a := (algebraMap K R).comp inc
  let f := changeRingHom M'.group (integralRingMap (algebraMap K R))
  let g := MulAut.conj (f r)
  have hi (x : IntegralPoints M'.group (integralRing R)) :
      g.symm x = MulAut.conj (f r⁻¹) x := by
    simp [g, MulAut.conj_symm_apply]
  obtain ⟨hr, ht⟩ := h R
  constructor
  · intro i z
    let u := T.unit (T.perm.symm i)
    have hz := hr (T.perm.symm i) (a (u⁻¹).val * z)
    have hu : a u.val * (a (u⁻¹).val * z) = z := by
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    have he : rootFactor C a T (T.perm.symm i) (a (u⁻¹).val * z) =
        rootFactor C a ChartTransport.identity i z := by
      simp only [rootFactor, ChartTransport.identity, Equiv.apply_symm_apply, Equiv.refl_apply,
        Units.val_one, map_one, one_mul]
      exact congrArg (fun v => markedRootPoint M'.toIntegralMarking (integralRing R) i
        (a C.uniformizer ^ rootDepth E i * v)) hu
    change MulAut.conj (f r⁻¹) (rootFactor C a ChartTransport.identity i z) = _
    rw [← hi, ← he, ← hz, MulEquiv.symm_apply_apply]
    simp only [rootFactor, ChartTransport.identity, ChartTransport.inverse, Equiv.refl_apply,
      Units.val_one, map_one, one_mul, u]
    all_goals rfl
  · intro t
    let t' := t.comp T.chars.symm.toAddMonoidHom.toMultiplicative
    have hz := ht t'
    have he : torusFactor (M' := M') T t' = torusFactor (K := K) (M' := M') ChartTransport.identity t := by
      unfold torusFactor
      apply congrArg (fun y => torusPoint E (integralRing R) y ≫ M'.torus.hom.hom)
      apply MonoidHom.ext
      intro j
      change t (Multiplicative.ofAdd (T.chars.symm (T.chars (Multiplicative.toAdd j)))) = t j
      rw [AddEquiv.symm_apply_apply]
      rfl
    change MulAut.conj (f r⁻¹) (torusFactor (K := K) (M' := M') ChartTransport.identity t) = _
    rw [← hi, ← he, ← hz, MulEquiv.symm_apply_apply] <;> rfl

end RepresentativeOnChart

section Extension

open CategoryTheory.CartesianMonoidalCategory
open Specs.ExceptionalIwahoriCongruence (changeRingHom integralRingMap residueHom)
open Specs.IntegralSemisimpleModel (IntegralPoints)
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {H : IwahoriModel Y} (C : ScaledRootChart H)

set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "dη" => IwahoriMarkedConjugation.genericPoint K
set_option quotPrecheck false in
local notation "inc" => (localIntegersInclusion K).hom.toRingHom
set_option quotPrecheck false in
local notation "red" => (residueHom O).hom.toRingHom
set_option quotPrecheck false in
local notation "P" => Over.pullback dη
set_option quotPrecheck false in
local notation "Pᵍ" => Specs.IwahoriMarkedConjugation.groupBaseChange inc
set_option quotPrecheck false in
local notation "Aₒ" => (Specs.IwahoriMarkedConjugation.groupBaseChange (algebraMap Integers O)).obj M'.group
set_option quotPrecheck false in
local notation "U" => (Specs.IwahoriMarkedConjugation.changeBase (algebraMap Integers O)).obj (rootProductChart M' C.negative C.positive)

private theorem genericImage_eval {R : CommAlgCat.{u} O} {S : TestAlgebra K}
    (x : genericTest S ⟶ integerTest R) (a : R →+* S) (ha : x.left = specMap a)
    (f : integerTest R ⟶ H.model.X) :
    H.genericImage (R := S) (x ≫ f) =
      changeRingHom M'.group (integralRingMap a) (H.image (R := R) f) := by
  apply Over.OverMorphism.ext
  change (x.left ≫ f.left) ≫ H.projection = specMap a ≫ f.left ≫ H.projection
  exact (congrArg (fun v => (v ≫ f.left) ≫ H.projection) ha).trans (Category.assoc _ _ _)

private theorem image_eq_integralProjection (R : CommAlgCat.{u} O)
    (f : integerTest R ⟶ H.model.X) :
    H.image (R := R) f = integralProjection R (f ≫ H.toIntegral.hom.hom) := by
  apply Over.OverMorphism.ext
  rw [integralProjection_left]
  exact (Category.assoc _ _ _).symm

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem affineGeneric {X : Over (integerScheme K)} (hX : IsAffine X.left) :
    IsAffine ((P).obj X).left := by
  change IsAffine (pullback X.hom dη)
  exact isAffine_of_isAffineHom (pullback.snd X.hom dη)

private theorem extend_of_transport (r : FieldPoints M' K)
    (T : ChartTransport (K := K) (E := E)) (h : TransportsChart C r T) :
    ∃ f : H.model ⟶ H.model, (Pᵍ).map f = genericConjugation H r := by
  obtain ⟨R, ⟨q⟩⟩ := affine_hasTest (U) (scaledRootChart_affine C)
  obtain ⟨z, _, hz⟩ := C.scales R q.hom
  have hR : Flat (integerTest R).hom := by
    have : Flat (U).hom := scaledRootChart_flat C
    rw [← Over.w q.hom]
    infer_instance
  let g : integerTest R ⟶ (Aₒ).X :=
    (integralProjection R).symm (chartValue C (algebraMap O R) T z)
  have hg : integralProjection R g = chartValue C (algebraMap O R) T z :=
    (integralProjection R).apply_symm_apply _
  obtain ⟨f, hf⟩ := flatTest_lift H R hR g (by
    intro S a ha
    rw [hg, chartValue_map, ha]
    apply chartValue_reduction C S
    change algebraMap (residue K) S (red C.uniformizer) = 0
    rw [uniformizer_residue_zero C, map_zero])
  have hfimage : H.image (R := R) f = chartValue C (algebraMap O R) T z := by
    rw [image_eq_integralProjection R f, hf, hg]
  let fU := q.inv ≫ f
  have hcomp : (P).map fU = (P).map C.chart ≫ (genericConjugation H r).hom.hom := by
    obtain ⟨S, ⟨j⟩⟩ := affine_hasTest ((P).obj (U)) (affineGeneric (scaledRootChart_affine C))
    let A := (testSpec K).obj (op S)
    let y := forgetBasePoint dη A (U) j.hom
    let x := y ≫ q.inv
    obtain ⟨a, ha, ha'⟩ := affineTest_map inc R S x
    have htest (m : (U) ⟶ H.model.X) :
        genericFibrePoints H S (j.hom ≫ (P).map m) = H.genericImage (R := S) (y ≫ m) :=
      (genericFibrePoints_formula H S _).trans
        (congrArg (fun t => H.genericImage (R := S) t) (forgetBasePoint_comp dη j.hom m))
    have hchart : y ≫ C.chart = x ≫ (q.hom ≫ C.chart) := by simp [x]
    have hex : y ≫ fU = x ≫ f := (Category.assoc _ _ _).symm
    let b := (algebraMap K S).comp inc
    let zS := mapCell C a z
    have hval := chartValue_map C (algebraMap O R) a T z
    have hval₀ := chartValue_map C (algebraMap O R) a ChartTransport.identity z
    change a.comp (algebraMap O R) = b at ha'
    have hleft : genericFibrePoints H S (j.hom ≫ (P).map fU) = chartValue C b T zS := by
      rw [htest, hex, genericImage_eval x a ha, hfimage, hval, ha']
    have hright : genericFibrePoints H S (j.hom ≫ (P).map C.chart) =
        chartValue C b ChartTransport.identity zS := by
      rw [htest, hchart, genericImage_eval x a ha, hz, ← chartValue_identity C, hval₀, ha']
    let gη : (P).obj H.model.X ⟶ (P).obj H.model.X := (genericConjugation H r).hom.hom
    have hconj := genericConjugation_formula H r S (j.hom ≫ (P).map C.chart)
    have hrhs : genericFibrePoints H S ((j.hom ≫ (P).map C.chart) ≫ gη) = chartValue C b T zS :=
      hconj.trans ((congrArg (MulAut.conj
        (changeRingHom M'.group (integralRingMap (algebraMap K S)) r)) hright).trans
        (TransportsChart.chart C r T h S zS))
    apply (cancel_epi j.hom).mp
    exact ((genericFibrePoints H S).injective (hleft.trans hrhs.symm)).trans
      (Category.assoc j.hom ((P).map C.chart) gη)
  have := genericPoint_isOpenImmersion K
  have : IsOpenImmersion C.chart.left := C.open_chart
  have : Smooth H.model.X.hom := H.smooth
  exact extendGroupFromChart inferInstance H.affine C.chart C.covers fU
    (genericConjugation H r) hcomp

private theorem genericConjugation_mul_inv (r : FieldPoints M' K) :
    genericConjugation H r ≫ genericConjugation H r⁻¹ = 𝟙 _ := by
  let G := (Pᵍ).obj H.model
  obtain ⟨R, ⟨i⟩⟩ := affine_hasTest G.X (affineGeneric H.affine)
  apply Grp.hom_ext
  apply (cancel_epi i.hom).mp
  apply (genericFibrePoints H R).injective
  change genericFibrePoints H R (i.hom ≫
    (genericConjugation H r).hom.hom ≫ (genericConjugation H r⁻¹).hom.hom) =
      genericFibrePoints H R (i.hom ≫ 𝟙 G.X)
  rw [← Category.assoc, genericConjugation_formula, genericConjugation_formula, Category.comp_id]
  simp [MulAut.conj_apply, mul_assoc]

end Extension

/-- Marked length-zero conjugation and its inverse extend over the split Iwahori model. -/
theorem markedConjugation : MarkedConjugation.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y H C r hr
  obtain ⟨T, hT⟩ := representative_chartTransport C r hr
  obtain ⟨f, hf⟩ := extend_of_transport C r T hT
  obtain ⟨g, hg⟩ := extend_of_transport C r⁻¹ T.inverse (TransportsChart.inv C r T hT)
  let Pgroup := Specs.IwahoriMarkedConjugation.groupBaseChange (localIntegersInclusion K).hom.toRingHom
  have : Smooth H.model.X.hom := H.smooth
  have inj {f g : H.model ⟶ H.model} (h : Pgroup.map f = Pgroup.map g) : f = g := by
    apply Grp.hom_ext
    apply eq_of_genericBaseChange inferInstance H.affine
    exact congrArg (fun h => h.hom.hom) h
  have hfg : f ≫ g = 𝟙 _ := by
    apply inj
    rw [Pgroup.map_comp, hf, hg, Pgroup.map_id H.model]
    exact genericConjugation_mul_inv (H := H) r
  have hgf : g ≫ f = 𝟙 _ := by
    apply inj
    rw [Pgroup.map_comp, hf, hg, Pgroup.map_id H.model]
    simpa only [inv_inv] using genericConjugation_mul_inv (H := H) r⁻¹
  exact ⟨⟨f, g, hfg, hgf⟩, extends_of_generic H r f hf, extends_of_generic H r⁻¹ g hg⟩

end

end LinearAlgebraicGroups.Arithmetic.IwahoriMarkedConjugation
