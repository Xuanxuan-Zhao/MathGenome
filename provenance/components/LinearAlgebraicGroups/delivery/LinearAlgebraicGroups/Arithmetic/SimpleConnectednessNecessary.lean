import Specs.LinearAlgebraicGroups.Arithmetic.SimpleConnectednessNecessary
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import LinearAlgebraicGroups.Arithmetic.KummerObstructions
import LinearAlgebraicGroups.Arithmetic.TorusFibreKummerRealization
import LinearAlgebraicGroups.Arithmetic.FiniteKummerSplitting
import Batteries.Tactic.OpenPrivate

noncomputable section

universe u v

namespace LinearAlgebraicGroups.Arithmetic.SimpleConnectednessNecessary

open Specs.SimpleConnectednessNecessary
open AdelicGroups
open Specs.IntegralModels (RationalPoints)
open scoped RestrictedProduct

theorem obstructionFromLocalOpen : ObstructionFromLocalOpen.{u, v} := by
  classical
  intro K _ G D i S T w hST hw U hU ⟨y, hy⟩ hUint havoid
  let a : Outside D S := ⟨Sum.inl w, fun hs => hw (hST hs)⟩
  let V (v : Outside D S) : Set (LocalPoints D i v.1) :=
    if h : a = v then h ▸ U else
      if v.1 ∈ T then Set.univ else localSubgroup D i v.1
  let F : Finset (Outside D S) := T.preimage Subtype.val Subtype.val_injective.injOn
  have hF (v : Outside D S) : v.1 ∈ T → v ∈ F := Finset.mem_preimage.mpr
  have hVa : V a = U := by simp [V]
  have hVopen (v : Outside D S) : IsOpen (V v) := by
    by_cases h : a = v
    · subst v
      simpa only [hVa] using hU
    · by_cases hv : v.1 ∈ T
      · simp [V, h, hv]
      · simpa [V, h, hv] using localSubgroup_open D i v.1
  have hV (v : Outside D S) (hv : v ∉ insert a F) : V v = localSubgroup D i v.1 := by
    have ha : a ≠ v := fun h => hv (h ▸ Finset.mem_insert_self a F)
    have ht : v.1 ∉ T := fun h => hv (Finset.mem_insert_of_mem (hF _ h))
    simp [V, ha, ht]
  refine ⟨box D i S V, ⟨insert a F, V, hVopen, hV, rfl⟩, ?_, ?_⟩
  · let x (v : Outside D S) : LocalPoints D i v.1 :=
      if h : a = v then h ▸ y else 1
    have hx (v : Outside D S) : x v ∈ localSubgroup D i v.1 := by
      by_cases h : a = v
      · subst v
        simpa [x, a, localSubgroup] using hUint hy
      · simp [x, h]
    refine ⟨⟨x, Filter.Eventually.of_forall hx⟩, ?_⟩
    intro v
    by_cases h : a = v
    · subst v
      simpa [x, hVa] using hy
    · by_cases hv : v.1 ∈ T
      · simp [V, h, hv]
      · simpa [V, h, hv] using hx v
  · rintro g ⟨x, hx, hg⟩
    have hlocal : localPoint D i (.inl w) g ∈ U := by
      simpa only [hg a, hVa] using hx a
    apply havoid g _ hlocal
    intro j hj
    let b : Outside D S := ⟨Sum.inl j, fun hs => hj (hST hs)⟩
    have hb : localPoint D i b.1 g ∈ V b := hg b ▸ hx b
    by_cases h : a = b
    · have h' : w = j := Sum.inl.inj (congrArg Subtype.val h)
      subst j
      exact hUint hlocal
    · simpa [V, h, b, hj, localSubgroup] using hb

theorem HasObstruction.not_strongApproximation {K : Type u} [Field K]
    {G : Specs.AffineAlgebraicGroup K} {D : GlobalFieldData.{u, v} K}
    {i : Specs.IntegralModels.MatrixRealization G} {S : Finset D.Place}
    (h : HasObstruction D i S) : ¬ StrongApproximation D i S := by
  rintro hd
  obtain ⟨B, hB, hne, havoid⟩ := h
  have ho := (adelicBasis D i S).isOpen hB
  obtain ⟨x, hx, g, hg⟩ := hd.inter_open_nonempty B ho hne
  exact havoid g ⟨x, hx, hg⟩

section Matrix

open AlgebraicGeometry CategoryTheory Opposite
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Unipotent (Index)
open Specs.IntegralCentralQuotient (spectrumOfAlgHom)
open Specs.CentralCover (matrixScheme MatrixEmbedding)
open Specs.StandardGroups (universalMatrix)

open private affineGroupIsoOfPoints affineGroupIsoOfPoints_map coordinateMap coordinateMap_spec
  glPoint_eval from LinearAlgebraicGroups.Arithmetic.IntegralModels

set_option backward.isDefEq.respectTransparency false in
theorem matrixEmbeddingWithEvaluation : MatrixEmbeddingWithEvaluation.{u} := by
  intro K _ G i
  let L := StandardGroups.generalLinearGroup K (Index.{u} i.size)
  let m := StandardGroups.generalLinearGroupPointsIso K (Index.{u} i.size)
  let E : i.ambient.val ≅ L.val :=
    affineGroupIsoOfPoints i.ambient.prop.1 L.prop.1 (i.matrix ≪≫ m.symm)
  let f : G.val.X ⟶ matrixScheme K i.size :=
    i.embedding.hom.hom ≫ E.hom.hom.hom
  have hclosed : IsClosedImmersion f.left := by
    let : IsClosedImmersion i.embedding.hom.hom.left := i.closed
    let Q := Grp.forget (SchemeOver K) ⋙ Over.forget _
    let : IsIso E.hom.hom.hom.left := inferInstanceAs (IsIso (Q.map E.hom))
    change IsClosedImmersion (i.embedding.hom.hom.left ≫ E.hom.hom.hom.left)
    infer_instance
  refine ⟨⟨f, hclosed⟩, ?_⟩
  intro R _ _ g
  let A := CommAlgCat.of K R
  let p := coordinateMap (k := K) (g ≫ f)
  refine ⟨p.hom, coordinateMap_spec _, ?_⟩
  let x : Points i.ambient.val.X A := g ≫ i.embedding.hom.hom
  have hh := affineGroupIsoOfPoints_map i.ambient.prop.1 L.prop.1 (i.matrix ≪≫ m.symm)
  have hh' := congrArg (fun α => α.app A x) hh
  change x ≫ E.hom.hom.hom = (i.matrix.hom.app A ≫ m.inv.app A) x at hh'
  have hm : m.hom.app A (g ≫ f) = asMatrix i R g := by
    change m.hom.app A (g ≫ i.embedding.hom.hom ≫ E.hom.hom.hom) = _
    rw [← Category.assoc, show g ≫ i.embedding.hom.hom = x from rfl, hh', GrpCat.comp_apply]
    exact GrpCat.hom_inv_apply (m.app A) (i.matrix.hom.app A x)
  ext r s
  change p.hom (universalMatrix K (Index.{u} i.size) r s) = _
  refine (glPoint_eval p r s).symm.trans ?_
  have hspec : (testSpec K).map p.op = g ≫ f := coordinateMap_spec _
  exact congrArg (fun y : Matrix.GeneralLinearGroup (Index.{u} i.size) R => y.val r s)
    ((congrArg (m.hom.app A) hspec).trans hm)

open private glEvaluation from LinearAlgebraicGroups.Affine.StandardGroups

open private matrixPresentation continuous_glEvaluation
  from LinearAlgebraicGroups.Arithmetic.AdelicGroups

set_option backward.isDefEq.respectTransparency false in
theorem continuousAffineEvaluation : ContinuousAffineEvaluation.{u} := by
  intro K L _ _ _ _ _ G i B e b
  obtain ⟨j, hj, h⟩ := matrixPresentation B e i
  obtain ⟨a, rfl⟩ := hj b
  have hval (g : PointsIn i L) :
      evaluateAffinePoint e g (j.hom a) = glEvaluation (asMatrix i L g) a :=
    (DFunLike.congr_fun (h L g) a).symm
  simp_rw [hval]
  exact (continuous_glEvaluation a).comp continuous_induced_dom

end Matrix

section Places

open IsDedekindDomain
open scoped NumberField

open private exists_adic_of_contains from LinearAlgebraicGroups.Arithmetic.GlobalPlaces

private theorem number_globalValuationRing {K : Type u} [Field K] [NumberField K]
    (w : NumberFinitePlace K) :
    globalValuationRing (.number ‹NumberField K›) w = (w.valuation K).valuationSubring := by
  ext x
  change (algebraMap K (w.adicCompletion K) x) ∈ w.adicCompletionIntegers K ↔
    (w.valuation K) x ≤ 1
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (x : w.adicCompletion K) ≤ 1 ↔ (w.valuation K) x ≤ 1
  rw [w.valuedAdicCompletion_eq_valuation']

private theorem function_globalValuationRing {F : Type v} {K : Type u} [Field F] [Finite F]
    [Field K] [Algebra F K] (t : SeparatingParameter F K) (w : FunctionPlace K) :
    globalValuationRing (.function F t) w = w.val := by
  ext x
  exact FunctionPlace.embedding_mem_integers w x

private theorem globalValuationRing_injective {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) : Function.Injective (globalValuationRing D) := by
  cases D with
  | number h =>
    let : NumberField K := h
    intro w z he
    exact HeightOneSpectrum.valuationSubring_valuation_injective K
      ((number_globalValuationRing w).symm.trans (he.trans (number_globalValuationRing z)))
  | function F t =>
    intro w z he
    exact Subtype.ext
      ((function_globalValuationRing t w).symm.trans (he.trans (function_globalValuationRing t z)))

private theorem globalValuationRing_ne_top {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) : globalValuationRing D w ≠ ⊤ := by
  cases D with
  | number h =>
    let : NumberField K := h
    rw [number_globalValuationRing]
    intro hw
    exact ((w.valuation K).valuationSubring_eq_top_iff.mp hw) inferInstance
  | function F t =>
    rw [function_globalValuationRing t w]
    exact w.property

private theorem valuationSubring_integrallyClosed {K : Type u} [Field K] (V : ValuationSubring K) :
    IsIntegrallyClosed V := by
  rw [← V.valuationSubring_valuation]
  exact (Valuation.integer.integers V.valuation).isIntegrallyClosed

private theorem exists_globalValuationRing {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (V : ValuationSubring K) (hV : V ≠ ⊤) :
    ∃ w, globalValuationRing D w = V := by
  cases D with
  | number h =>
    let : NumberField K := h
    let : IsIntegrallyClosed V := valuationSubring_integrallyClosed V
    have hO (a : 𝓞 K) : algebraMap (𝓞 K) K a ∈ V := by
      have ha : IsIntegral ℤ (algebraMap (𝓞 K) K a) := a.property
      obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp (ha.tower_top (A := V))
      rw [← hb]
      exact b.property
    obtain ⟨w, hw⟩ := exists_adic_of_contains (⟨V, hV⟩ : FunctionPlace K) hO
    exact ⟨w, (number_globalValuationRing w).trans hw⟩
  | function F t =>
    exact ⟨⟨V, hV⟩, function_globalValuationRing t _⟩

private theorem comap_ne_top_of_finite {K E : Type u} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] (V : ValuationSubring E) (hV : V ≠ ⊤) :
    V.comap (algebraMap K E) ≠ ⊤ := by
  intro h
  apply hV
  have h' (x : K) : algebraMap K E x ∈ V := by
    change x ∈ V.comap (algebraMap K E)
    rw [h]
    exact ValuationSubring.mem_top _
  let : Algebra K V := ((algebraMap K E).codRestrict V h').toAlgebra
  let : IsScalarTower K V E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsIntegrallyClosed V := valuationSubring_integrallyClosed V
  apply top_unique
  intro x _
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := V))
  rw [← hy]
  exact y.property

theorem finitePlaceRestriction : FinitePlaceRestriction.{u, v} := by
  classical
  intro K E _ _ _ _ D D'
  have hr (w : D'.FinitePlace) : ∃ x,
      globalValuationRing D x = (globalValuationRing D' w).comap (algebraMap K E) :=
    exists_globalValuationRing D _ (comap_ne_top_of_finite _ (globalValuationRing_ne_top D' w))
  choose r hr using hr
  refine ⟨r, hr, ?_⟩
  intro T w hw e he x
  let V := (D.integers w).comap e
  have hV : V.comap (algebraMap K E) = globalValuationRing D w := by
    rw [show V = (D.integers w).comap e from rfl, ValuationSubring.comap_comap, he]
    rfl
  have hV' : V ≠ ⊤ := by
    intro h
    apply globalValuationRing_ne_top D w
    rw [← hV, h]
    ext a
    rfl
  obtain ⟨z, hz⟩ := exists_globalValuationRing D' V hV'
  have hzw : r z = w := globalValuationRing_injective D
    ((hr z).trans ((congrArg (fun U : ValuationSubring E => U.comap (algebraMap K E)) hz).trans hV))
  have hzT : z ∉ T := fun h => hw ⟨z, h, hzw⟩
  have hx := Subring.mem_iInf.mp x.property ⟨z, hzT⟩
  change (x : E) ∈ V
  rw [← hz]
  exact hx

end Places

open IsDiscreteValuationRing

private theorem one_sub_pow_unit {R : Type*} [CommRing R] [IsLocalRing R]
    {π : R} (hπ : ¬ IsUnit π) {n : ℕ} (hn : 0 < n) :
    IsUnit (1 - π ^ n) :=
  IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    (fun h => hπ ((isUnit_pow_iff hn.ne').mp h))

private theorem infiniteUnitClassesDVR (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    Infinite (Kummer.Classes R p) := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  let n (a : ℕ) := p * a + 1
  let u (a : ℕ) : Rˣ :=
    (show IsUnit (1 + π ^ n a) from by
      rw [← sub_neg_eq_add]
      apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      intro h
      apply hπ.not_isUnit
      have hn : n a ≠ 0 := Nat.succ_ne_zero _
      exact (isUnit_pow_iff hn).mp (by simpa only [neg_neg] using h.neg)).unit
  have hu (a : ℕ) : (u a : R) = 1 + π ^ n a := IsUnit.unit_spec _
  have hlt (a b : ℕ) (hab : a < b) :
      Kummer.classOf p (u a) ≠ Kummer.classOf p (u b) := by
    intro h
    obtain ⟨z, hz⟩ := QuotientGroup.eq_iff_div_mem.mp h
    have he : (u a : R) = (u b : R) * (z : R) ^ p := by
      have h' : u a = u b * z ^ p := div_eq_iff_eq_mul'.mp hz.symm
      simpa using congrArg (fun x : Rˣ => (x : R)) h'
    have hn : n a < n b := Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left hab
      (Fact.out : Nat.Prime p).pos)
    let k := n b - n a
    have hk : 0 < k := Nat.sub_pos_of_lt hn
    let t := (one_sub_pow_unit hπ.not_isUnit hk).unit
    have ht : (t : R) = 1 - π ^ k := IsUnit.unit_spec _
    have hd : (u a : R) - (u b : R) = (t : R) * π ^ n a := by
      rw [hu, hu, ht, ← Nat.add_sub_of_le hn.le, pow_add]
      ring
    have hpow : (u a : R) - (u b : R) = (u b : R) * ((z : R) - 1) ^ p := by
      rw [sub_pow_char, one_pow, mul_sub, mul_one, ← he]
    have hz1 : (z : R) - 1 ≠ 0 := by
      intro hz1
      rw [hd, hz1, zero_pow (Fact.out : Nat.Prime p).ne_zero, mul_zero] at hpow
      exact (mul_ne_zero t.ne_zero (pow_ne_zero _ hπ.ne_zero)) hpow
    obtain ⟨j, s, hs⟩ := eq_unit_mul_pow_irreducible hz1 hπ
    have hf : (t : R) * π ^ n a = (u b * s ^ p : Rˣ).val * π ^ (p * j) := by
      rw [← hd, hpow, hs, mul_pow, ← pow_mul, Nat.mul_comm j p]
      simp [mul_assoc]
    have hj := unit_mul_pow_congr_pow hπ hπ t (u b * s ^ p) _ _ hf
    change p * a + 1 = p * j at hj
    have hm := congrArg (· % p) hj
    simp [Nat.add_mod, Nat.mod_eq_of_lt (Fact.out : Nat.Prime p).one_lt] at hm
  exact Infinite.of_injective (fun a => Kummer.classOf p (u a)) fun a b h =>
    (lt_trichotomy a b).resolve_left (fun h' => hlt a b h' h) |>.resolve_right
      (fun h' => hlt b a h' h.symm)

open scoped ValuativeRel in
theorem equalCharacteristicUnitClasses : EqualCharacteristicUnitClasses.{u} := by
  intro K _ _ _ _ p _ _
  let R := 𝒪[K]
  let : CharP R p :=
    (ValuativeRel.valuation K).integer.subtype.charP Subtype.val_injective p
  have hcompact : IsCompact ((powMonoidHom (α := Rˣ) p).range : Set Rˣ) :=
    isCompact_range (continuous_pow p)
  let : IsClosed ((powMonoidHom (α := Rˣ) p).range : Set Rˣ) := hcompact.isClosed
  exact ⟨infiniteUnitClassesDVR R p, inferInstance⟩

theorem primeToResidueUnitClasses : PrimeToResidueUnitClasses.{u} := by
  classical
  intro R _ _ _ _ n hn ζ hζ hpow
  let k := IsLocalRing.ResidueField R
  let f := IsLocalRing.residue R
  let g := Units.map f.toMonoidHom
  have hζ' : g ζ ≠ 1 := by
    intro h
    have hmul := geom_sum_mul (ζ : R) n
    rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one, sub_self] at hmul
    have hne : (ζ : R) - 1 ≠ 0 := sub_ne_zero.mpr (fun h' => hζ (Units.ext h'))
    have hz := (mul_eq_zero.mp hmul).resolve_right hne
    have he : f (ζ : R) = 1 := congrArg (fun t : kˣ => (t : k)) h
    apply hn
    simpa only [map_sum, map_pow, he, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_one, map_zero] using congrArg f hz
  have hsurj : Function.Surjective g :=
    IsLocalRing.surjective_units_map_of_local_ringHom f Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk_surjective.isLocalHom f)
  have hnonsurj : ¬ Function.Surjective (powMonoidHom (α := kˣ) n) := by
    intro hs
    have hi := Finite.injective_iff_surjective.mpr hs
    apply hζ'
    apply hi
    change g ζ ^ n = (1 : kˣ) ^ n
    rw [← map_pow, hpow, map_one, one_pow]
  obtain ⟨b, hb⟩ : ∃ b : kˣ, ¬ ∃ a : kˣ, a ^ n = b := by
    change ¬ (∀ b : kˣ, ∃ a : kˣ, a ^ n = b) at hnonsurj
    exact not_forall.mp hnonsurj
  obtain ⟨a, ha⟩ := hsurj b
  refine ⟨⟨Kummer.classOf n a, 1, fun h => hb ?_⟩⟩
  obtain ⟨t, ht⟩ := (QuotientGroup.eq_one_iff _).mp h
  change t ^ n = a at ht
  exact ⟨g t, by rw [← map_pow, ht, ha]⟩

theorem integralUnitClassesInject : IntegralUnitClassesInject.{u} := by
  intro F _ V n hn a b hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ b
  let f := Units.map V.subtype.toMonoidHom
  change Kummer.classOf n (f x) = Kummer.classOf n (f y) at hab
  obtain ⟨z, hz⟩ := QuotientGroup.eq_iff_div_mem.mp hab
  change z ^ n = f x / f y at hz
  have hf (t : Vˣ) : f t ∈ V.unitGroup := by
    let h := V.unitGroupMulEquiv.symm t
    have he : h.val = f t := Units.ext (V.coe_unitGroupMulEquiv_symm_apply t)
    exact he ▸ h.property
  have hp : V.valuation (z : F) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hz]
    exact V.mem_unitGroup_iff _ |>.mp (V.unitGroup.div_mem (hf x) (hf y))
  have hz' : z ∈ V.unitGroup := (V.mem_unitGroup_iff z).mpr
    ((pow_eq_one_iff_of_nonneg zero_le hn.ne').mp hp)
  let t := V.unitGroupMulEquiv ⟨z, hz'⟩
  have ht : f t = z := Units.ext (V.coe_unitGroupMulEquiv_apply ⟨z, hz'⟩)
  apply QuotientGroup.eq_iff_div_mem.mpr
  refine ⟨t, (Units.map_injective (f := V.subtype.toMonoidHom) Subtype.val_injective) ?_⟩
  change f (t ^ n) = f (x / y)
  rw [map_pow, map_div, ht, hz]

private theorem isClosed_subgroup_of_inter_open {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {M U : Subgroup H} (hU : IsOpen (U : Set H))
    (hclosed : IsClosed ((M : Set H) ∩ U)) : IsClosed (M : Set H) := by
  apply closure_subset_iff_isClosed.mp
  intro x hx
  change x ∈ M.topologicalClosure at hx
  have ho : IsOpen ((fun y : H => x⁻¹ * y) ⁻¹' (U : Set H)) :=
    hU.preimage (continuous_const.mul continuous_id)
  have hxmem : x ∈ (fun y : H => x⁻¹ * y) ⁻¹' (U : Set H) := by
    change x⁻¹ * x ∈ U
    rw [inv_mul_cancel]
    exact U.one_mem
  obtain ⟨y, hyU, hyM⟩ := mem_closure_iff.mp hx _ ho hxmem
  change x⁻¹ * y ∈ U at hyU
  have hyxU : y⁻¹ * x ∈ U := by simpa using U.inv_mem hyU
  have h := M.topologicalClosure.mul_mem (M.topologicalClosure.inv_mem (M.le_topologicalClosure hyM)) hx
  have hyxM : y⁻¹ * x ∈ M := by
    by_contra hn
    have hz : y⁻¹ * x ∈ (U : Set H) \ ((M : Set H) ∩ U) :=
      ⟨hyxU, fun ⟨hm, _⟩ => hn hm⟩
    obtain ⟨z, ⟨hzU, hzn⟩, hzM⟩ := mem_closure_iff.mp h _ (hU.sdiff hclosed) hz
    exact hzn ⟨hzM, hzU⟩
  simpa using M.mul_mem hyM hyxM

open scoped ValuativeRel in
theorem localFieldUnitClassesHausdorff : LocalFieldUnitClassesHausdorff.{u} := by
  intro F _ _ _ _ n hn
  let v := ValuativeRel.valuation F
  let U := v.valuationSubring.unitGroup
  let P := (powMonoidHom (α := Fˣ) n).range
  let j : v.valuationSubringˣ →* Fˣ := Units.map v.valuationSubring.subtype.toMonoidHom
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have hU : IsOpen (U : Set Fˣ) := by
    have hV : IsOpen (v.valuationSubring : Set F) := Valued.isOpen_valuationSubring F
    have he : (U : Set Fˣ) =
        Units.val ⁻¹' (v.valuationSubring : Set F) ∩
          (fun y : Fˣ => ((y⁻¹ : Fˣ) : F)) ⁻¹' (v.valuationSubring : Set F) := by
      ext y
      change y ∈ v.valuationSubring.unitGroup ↔
        (y : F) ∈ v.valuationSubring ∧ ((y⁻¹ : Fˣ) : F) ∈ v.valuationSubring
      rw [Valuation.mem_unitGroup_iff, Valuation.mem_valuationSubring_iff,
        Valuation.mem_valuationSubring_iff, Units.val_inv_eq_inv_val,
        map_inv₀, inv_le_one₀ (v.pos_iff.mpr y.ne_zero), le_antisymm_iff]
    rw [he]
    exact (hV.preimage Units.continuous_val).inter (hV.preimage Units.continuous_coe_inv)
  have hj : Continuous j := continuous_subtype_val.units_map _
  have hP : IsClosed ((P : Set Fˣ) ∩ U) := by
    have he : (P : Set Fˣ) ∩ U = Set.range (fun y : v.valuationSubringˣ => j y ^ n) := by
      ext x
      constructor
      · rintro ⟨⟨z, rfl⟩, hz⟩
        have hv : v (z : F) ^ n = 1 := by
          rw [← map_pow, ← Units.val_pow_eq_pow_val]
          exact (Valuation.mem_unitGroup_iff F v (z ^ n)).mp hz
        have hz' : z ∈ U := (Valuation.mem_unitGroup_iff F v z).mpr
          ((pow_eq_one_iff_of_nonneg zero_le hn.ne').mp hv)
        exact ⟨v.valuationSubring.unitGroupMulEquiv ⟨z, hz'⟩, congrArg (· ^ n)
          (Units.ext (v.valuationSubring.coe_unitGroupMulEquiv_apply ⟨z, hz'⟩))⟩
      · rintro ⟨y, rfl⟩
        refine ⟨⟨j y, rfl⟩, U.pow_mem ?_ _⟩
        let z := v.valuationSubring.unitGroupMulEquiv.symm y
        have he : z.val = j y :=
          Units.ext (v.valuationSubring.coe_unitGroupMulEquiv_symm_apply y)
        exact he ▸ z.property
    rw [he]
    have : CompactSpace v.valuationSubringˣ := inferInstanceAs (CompactSpace 𝒪[F]ˣ)
    exact (isCompact_range (hj.pow n)).isClosed
  let : IsClosed (P : Set Fˣ) := isClosed_subgroup_of_inter_open hU hP
  exact inferInstance

section Pullback

open scoped TensorProduct
open Algebra.TensorProduct Filter Topology
open Kummer
open Specs.IntegralCentralQuotient (rightCoaction IsRightTorsor)
open Specs.CentralCoverSpreading (KernelCoordinates)

open private cover_invariants coordinateCharacter_pow fibreElement_scalar
  from LinearAlgebraicGroups.Arithmetic.KummerObstructions

private theorem continuous_unitClass {F X : Type*} [Field F] [TopologicalSpace F]
    [IsTopologicalDivisionRing F] [TopologicalSpace X] (n : ℕ)
    {f : X → F} (hf : Continuous f) (hnz : ∀ x, f x ≠ 0) :
    Continuous (fun x => classOf n (Units.mk0 (f x) (hnz x))) := by
  apply QuotientGroup.continuous_mk.comp
  refine Units.continuous_iff.mpr ⟨hf, ?_⟩
  exact hf.inv₀ hnz

set_option backward.isDefEq.respectTransparency false in
theorem continuousPullbackClass : ContinuousPullbackClass.{u} := by
  intro R B A F _ _ _ _ _ _ _ _ _ _ I n q π hq
  let : Algebra B A := q.toAlgHom.toAlgebra
  intro i hn X _ f hf c hc
  obtain ⟨hFF, hinv⟩ := cover_invariants q π hq
  let : Module.FaithfullyFlat B A := hFF
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨b, a, hb, _, hba, _⟩ := (hc x).1
  have hdegree : rightCoaction π (b ^ n i) =
      (b ^ n i) ⊗ₜ[R] (1 : KernelCoordinates R n) := by
    rw [map_pow, hb, tmul_pow, ← map_pow, coordinateCharacter_pow n i, map_one]
  obtain ⟨d, hd⟩ := (hinv _).mp hdegree
  have hpower (p : B →ₐ[R] F) :
      let : Algebra B F := p.toAlgebra
      ((1 : F) ⊗ₜ[B] b) ^ n i = algebraMap F (F ⊗[B] A) (p d) := by
    let : Algebra B F := p.toAlgebra
    change (includeRight (R := B) (A := F) b) ^ n i = _
    rw [← map_pow, ← hd]
    exact fibreElement_scalar q.toAlgHom p d
  have hdx : f x d ≠ 0 := by
    let : Algebra B F := (f x).toAlgebra
    have h : algebraMap F (F ⊗[B] A) (f x d) = algebraMap F (F ⊗[B] A) (a : F) :=
      (hpower (f x)).symm.trans hba
    exact (FaithfulSMul.algebraMap_injective F (F ⊗[B] A) h).trans_ne a.ne_zero
  let U : Set X := {y | f y d ≠ 0}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage (hf d)
  let r : U → F := fun y => f y.val d
  let C : U → Classes F (n i) := fun y => classOf (n i) (Units.mk0 (r y) y.2)
  have hC : Continuous C :=
    continuous_unitClass (n i) ((hf d).comp continuous_subtype_val) Subtype.property
  have he (y : U) : C y = c y := by
    let p := f y.val
    let : Algebra B F := p.toAlgebra
    apply (hc y).2
    refine ⟨b, Units.mk0 (r y) y.2, hb, ?_, hpower p, rfl⟩
    apply (isUnit_pow_iff hn.ne').mp
    rw [hpower p]
    exact (Units.mk0 (r y) y.2).isUnit.map (algebraMap F (F ⊗[B] A))
  have h : ContinuousWithinAt c U x := by
    rw [continuousWithinAt_iff_continuousAt_domRestrict c hdx]
    rw [show U.domRestrict c = C from (funext he).symm]
    exact hC.continuousAt
  exact h.continuousAt (hU.mem_nhds hdx)

end Pullback

section LocalSeparation

open Kummer

private def reduceExponent (R : Type*) [CommRing R] {p n : ℕ} (h : p ∣ n) :
    Classes R n →* Classes R p :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rintro _ ⟨x, rfl⟩
    obtain ⟨d, rfl⟩ := h
    exact ⟨x ^ d, by
      change (x ^ d) ^ p = x ^ (p * d)
      rw [← pow_mul, Nat.mul_comm]⟩)

private theorem map_reduceExponent {R F : Type*} [CommRing R] [CommRing F]
    (e : R →+* F) {p n : ℕ} (h : p ∣ n) (c : Classes R n) :
    map e p (reduceExponent R h c) = reduceExponent F h (map e n c) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ c
  rfl

private theorem mem_unitGroup_of_pow_eq_one {F : Type*} [Field F]
    (V : ValuationSubring F) (z : Fˣ) {p : ℕ} (hp : p ≠ 0) (hz : z ^ p = 1) :
    z ∈ V.unitGroup := by
  apply (V.mem_unitGroup_iff z).mpr
  apply (pow_eq_one_iff_of_nonneg zero_le hp).mp
  rw [← map_pow, ← Units.val_pow_eq_pow_val, hz, Units.val_one, map_one]

open scoped ValuativeRel in
private theorem exists_separatingUnit {K E : Type u} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (D : GlobalFieldData.{u, v} K)
    (S : Finset D.FinitePlace) (n : ℕ) (hn : 1 < n) (P : Set (Classes E n)) (hP : P.Finite) :
    ∃ w : D.FinitePlace, w ∉ S ∧ ∃ e : E →+* D.FiniteCompletion w,
      e.comp (algebraMap K E) = D.embedding (.inl w) ∧
      ∃ a : (D.integers w)ˣ, map (D.integers w).subtype n (classOf n a) ∉ map e n '' P := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn.ne'
  let P' := reduceExponent E hpn '' P
  have hP' : P'.Finite := hP.image _
  suffices ∃ w : D.FinitePlace, w ∉ S ∧ ∃ e : E →+* D.FiniteCompletion w,
      e.comp (algebraMap K E) = D.embedding (.inl w) ∧
      ∃ a : (D.integers w)ˣ, map (D.integers w).subtype p (classOf p a) ∉ map e p '' P' by
    obtain ⟨w, hw, e, he, a, ha⟩ := this
    refine ⟨w, hw, e, he, a, ?_⟩
    rintro ⟨c, hc, heq⟩
    apply ha
    refine ⟨reduceExponent E hpn c, ⟨c, hc, rfl⟩, ?_⟩
    rw [map_reduceExponent, heq]
    rfl
  by_cases hchar : (p : K) = 0
  · obtain ⟨w, hw, hsplit⟩ := exists_splitPlace_outside (L := E) D S
    obtain ⟨e, he⟩ := (splitsCompletelyAt_iff_embedding D w).mp hsplit
    let F := D.FiniteCompletion w
    let : IsNonarchimedeanLocalField F := D.finiteCompletion_isLocalField w
    let : Fact p.Prime := ⟨hp⟩
    let emb : K →+* F := D.embedding (.inl w)
    have hpF : (p : F) = 0 := (map_natCast emb p).symm.trans
      ((congrArg emb hchar).trans emb.map_zero)
    let : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr hpF
    have hinf : Infinite (Classes (D.integers w) p) := by
      rw [D.integers_eq_valuationSubring w]
      exact (equalCharacteristicUnitClasses F p).1
    let Q := (map (D.integers w).subtype p) ⁻¹' (map e p '' P')
    have hQ : Q.Finite :=
      (hP'.image _).preimage (integralUnitClassesInject (D.integers w) p hp.pos).injOn
    obtain ⟨b, hb⟩ := hQ.exists_notMem
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ b
    exact ⟨w, hw, e, he, a, hb⟩
  · obtain ⟨w, hw, e, he, hkill, ⟨ζ, hζ⟩, hres⟩ :=
      exists_finiteKummerSplittingPlace D S p hp.one_lt hchar P' hP'
    let V := D.integers w
    let z := (hζ.isUnit hp.ne_zero).unit
    have hzval : (z : D.FiniteCompletion w) = ζ := (hζ.isUnit hp.ne_zero).unit_spec
    have hz : z ^ p = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hzval, Units.val_one]
      exact hζ.pow_eq_one)
    let tz := V.unitGroupMulEquiv ⟨z, mem_unitGroup_of_pow_eq_one V z hp.ne_zero hz⟩
    have htz : Units.map V.subtype.toMonoidHom tz = z :=
      Units.ext (V.coe_unitGroupMulEquiv_apply _)
    have ht_ne : tz ≠ 1 := by
      intro ht
      rw [ht, map_one] at htz
      exact hζ.ne_one hp.one_lt (hzval.symm.trans (congrArg Units.val htz.symm))
    have ht_pow : tz ^ p = 1 := by
      apply Units.map_injective (f := V.subtype.toMonoidHom) Subtype.val_injective
      rw [map_pow, htz, hz, map_one]
    let : Finite (IsLocalRing.ResidueField V) := (D.integers_properties w).2.2
    let : Nontrivial (Classes V p) := primeToResidueUnitClasses V p hres tz ht_ne ht_pow
    obtain ⟨b, hb⟩ := exists_ne (1 : Classes V p)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ b
    refine ⟨w, hw, e, he, a, ?_⟩
    rintro ⟨c, hc, heq⟩
    exact hb ((integralUnitClassesInject V p hp.pos) (heq.symm.trans ((hkill c hc).trans (map_one _).symm)))

end LocalSeparation

section ModelPoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.CentralCover (matrixCoordinates matrixDeterminant matrixCoordinateMap matrixScheme
  MatrixEmbedding)
open Specs.IntegralCentralQuotient (OverBase spectrumOfAlgHom)
open Specs.Unipotent (Index)
open Specs.StandardGroups (universalMatrix)
open CentralCover (affineSpectrum scalarSpec)
open private specMap_surjective
  from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation glEvaluation_entry
  from LinearAlgebraicGroups.Affine.StandardGroups
open private continuous_glEvaluation from LinearAlgebraicGroups.Arithmetic.AdelicGroups

private abbrev matrixEntry (R : Type u) [CommRing R] {m : ℕ} (a b : Index.{u} m) :
    matrixCoordinates R m :=
  algebraMap (MvPolynomial (Index.{u} m × Index.{u} m) R) _ (MvPolynomial.X (a, b))

private theorem matrixCoordinateMap_entry {R L : Type u} [CommRing R] [CommRing L] [Algebra R L]
    {m : ℕ} (a b : Index.{u} m) :
    matrixCoordinateMap R L m (matrixEntry R a b) = matrixEntry L a b := by
  rw [matrixEntry, CentralCover.matrixCoordinateMap_algebraMap, MvPolynomial.map_X]

private theorem matrixEntry_ext {R L : Type u} [CommRing R] [CommRing L] [Algebra R L]
    {m : ℕ} {f g : matrixCoordinates R m →ₐ[R] L}
    (h : ∀ a b, f (matrixEntry R a b) = g (matrixEntry R a b)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (matrixDeterminant R m))
  apply MvPolynomial.algHom_ext
  rintro ⟨a, b⟩
  exact h a b

private def evaluateMatrix {R L : Type u} [CommRing R] [CommRing L] [Algebra R L] {m : ℕ}
    (M : Matrix.GeneralLinearGroup (Index.{u} m) L) : matrixCoordinates R m →ₐ[R] L := by
  let a : MvPolynomial (Index.{u} m × Index.{u} m) R →ₐ[R] L :=
    MvPolynomial.aeval (fun ij => M.val ij.1 ij.2)
  have ha : a (matrixDeterminant R m) = M.val.det := by
    unfold matrixDeterminant
    rw [AlgHom.map_det]
    exact congrArg Matrix.det (Matrix.ext fun i j => MvPolynomial.aeval_X _ (i, j))
  exact IsLocalization.Away.liftAlgHom (matrixDeterminant R m)
    (show IsUnit (a (matrixDeterminant R m)) from ha ▸ (Matrix.GeneralLinearGroup.det M).isUnit)

@[local simp]
private theorem evaluateMatrix_entry {R L : Type u} [CommRing R] [CommRing L] [Algebra R L] {m : ℕ}
    (M : Matrix.GeneralLinearGroup (Index.{u} m) L) (a b : Index.{u} m) :
    evaluateMatrix (R := R) M (matrixEntry R a b) = M.val a b := by
  rw [evaluateMatrix, IsLocalization.Away.liftAlgHom_apply]
  exact (IsLocalization.Away.lift_eq (matrixDeterminant R m) _ (MvPolynomial.X (a, b))).trans
    (MvPolynomial.aeval_X _ (a, b))

private def pointCoordinates {R B L : Type u} [CommRing R] [CommRing B] [CommRing L]
    [Algebra R B] [Algebra R L] (g : affineSpectrum R L ⟶ affineSpectrum R B) : B →ₐ[R] L :=
  ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage g).unop.hom

@[local simp]
private theorem spectrumOf_pointCoordinates {R B L : Type u} [CommRing R] [CommRing B]
    [CommRing L] [Algebra R B] [Algebra R L] (g : affineSpectrum R L ⟶ affineSpectrum R B) :
    spectrumOfAlgHom (pointCoordinates g) = g :=
  (algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage g

set_option backward.isDefEq.respectTransparency false in
private theorem closedMatrixCoordinates {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {Y : OverBase R} (e : affineSpectrum R B ≅ Y) {m : ℕ} (j : Y ⟶ matrixScheme R m)
    (hj : IsClosedImmersion j.left) :
    ∃ J : matrixCoordinates R m →ₐ[R] B, Function.Surjective J ∧
      spectrumOfAlgHom J = e.hom ≫ j := by
  let J := pointCoordinates (e.hom ≫ j)
  have hJ := spectrumOf_pointCoordinates (e.hom ≫ j)
  have h := congrArg Over.Hom.left hJ
  change Spec.map (CommRingCat.ofHom J.toRingHom) = e.hom.left ≫ j.left at h
  let := hj
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hc : IsClosedImmersion (e.hom.left ≫ j.left) := inferInstance
  exact ⟨J, specMap_surjective (CommRingCat.ofHom J.toRingHom) (h.symm ▸ hc), hJ⟩

set_option backward.isDefEq.respectTransparency false in
private def genericPointLift {R E L : Type u} [CommRing R] [CommRing E] [CommRing L]
    [Algebra R E] [Algebra E L] [Algebra R L] [IsScalarTower R E L]
    {Y : OverBase R} (g : affineSpectrum R L ⟶ Y) :
    affineSpectrum E L ⟶ (Over.pullback (scalarSpec R E)).obj Y :=
  Over.homMk (pullback.lift g.left (scalarSpec E L) (by
    rw [Over.w g]
    exact (CentralCover.scalarSpec_tower (R := R) (S := E) (U := L)).symm)) (by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
      simp)

@[local simp]
private theorem genericPointLift_fst {R E L : Type u} [CommRing R] [CommRing E] [CommRing L]
    [Algebra R E] [Algebra E L] [Algebra R L] [IsScalarTower R E L]
    {Y : OverBase R} (g : affineSpectrum R L ⟶ Y) :
    (genericPointLift (E := E) g).left ≫ pullback.fst Y.hom (scalarSpec R E) = g.left :=
  pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
private def genericPointRestrict {R E L : Type u} [CommRing R] [CommRing E] [CommRing L]
    [Algebra R E] [Algebra E L] [Algebra R L] [IsScalarTower R E L]
    {Y : OverBase R} (g : affineSpectrum E L ⟶ (Over.pullback (scalarSpec R E)).obj Y) :
    affineSpectrum R L ⟶ Y :=
  Over.homMk (g.left ≫ pullback.fst Y.hom (scalarSpec R E)) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hg := Over.w g
    change g.left ≫ pullback.snd Y.hom (scalarSpec R E) = scalarSpec E L at hg
    rw [hg]
    exact CentralCover.scalarSpec_tower (R := R) (S := E) (U := L))

private theorem genericPointRestrict_lift {R E L : Type u} [CommRing R] [CommRing E] [CommRing L]
    [Algebra R E] [Algebra E L] [Algebra R L] [IsScalarTower R E L]
    {Y : OverBase R} (g : affineSpectrum R L ⟶ Y) :
    genericPointRestrict (genericPointLift (E := E) g) = g :=
  Over.OverMorphism.ext (genericPointLift_fst g)

set_option backward.isDefEq.respectTransparency false in
private theorem genericPointLift_restrict {R E L : Type u} [CommRing R] [CommRing E] [CommRing L]
    [Algebra R E] [Algebra E L] [Algebra R L] [IsScalarTower R E L]
    {Y : OverBase R} (g : affineSpectrum E L ⟶ (Over.pullback (scalarSpec R E)).obj Y) :
    genericPointLift (genericPointRestrict g) = g := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact genericPointLift_fst (genericPointRestrict g)
  · exact (Over.w (genericPointLift (genericPointRestrict g))).trans (Over.w g).symm

private theorem specMap_injective_ringHom {A B : Type u} [CommRing A] [CommRing B]
    {f g : A →+* B} (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) :
    f = g :=
  CommRingCat.hom_ext_iff.mp (Spec.map_injective h)

variable {K R E L B : Type u} [Field K] [Field E] [CommRing R] [CommRing L] [CommRing B]
  [Algebra K E] [Algebra R E] [Algebra E L] [Algebra K L] [Algebra R L] [Algebra R B]
  [IsScalarTower K E L] [IsScalarTower R E L]
  {G : AffineAlgebraicGroup K} {i : Specs.IntegralModels.MatrixRealization G}
  {Y : OverBase R}

private def modelPoint (eB : affineSpectrum R B ≅ Y)
    (e : (Over.pullback (scalarSpec R E)).obj Y ≅ (baseChange K E).obj G.val.X)
    (g : PointsIn i L) : B →ₐ[R] L :=
  pointCoordinates (genericPointRestrict (genericPointLift g ≫ e.inv) ≫ eB.inv)

set_option backward.isDefEq.respectTransparency false in
private theorem modelPoint_surjective (eB : affineSpectrum R B ≅ Y)
    (e : (Over.pullback (scalarSpec R E)).obj Y ≅ (baseChange K E).obj G.val.X) :
    Function.Surjective (modelPoint (i := i) (L := L) eB e) := by
  intro p
  refine ⟨genericPointRestrict (genericPointLift (spectrumOfAlgHom p ≫ eB.hom) ≫ e.hom), ?_⟩
  unfold modelPoint
  rw [genericPointLift_restrict, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply AlgHom.toRingHom_injective
  apply specMap_injective_ringHom
  change (spectrumOfAlgHom (pointCoordinates _)).left = (spectrumOfAlgHom p).left
  rw [spectrumOf_pointCoordinates, genericPointRestrict_lift, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem modelPoint_matrix {j : Y ⟶ matrixScheme R i.size}
    {jK : MatrixEmbedding G i.size} {jE : (baseChange K E).obj G.val.X ⟶ matrixScheme E i.size}
    {eB : affineSpectrum R B ≅ Y}
    {e : (Over.pullback (scalarSpec R E)).obj Y ≅ (baseChange K E).obj G.val.X}
    (hKE : jE.left ≫ Spec.map (CommRingCat.ofHom (matrixCoordinateMap K E i.size)) =
      pullback.fst G.val.X.hom (scalarSpec K E) ≫ jK.inclusion.left)
    (hRE : e.hom.left ≫ jE.left ≫ Spec.map (CommRingCat.ofHom (matrixCoordinateMap R E i.size)) =
      pullback.fst Y.hom (scalarSpec R E) ≫ j.left)
    (J : matrixCoordinates R i.size →ₐ[R] B) (hJ : spectrumOfAlgHom J = eB.hom ≫ j)
    (g : PointsIn i L) (p : matrixCoordinates K i.size →ₐ[K] L)
    (hp : spectrumOfAlgHom p = g ≫ jK.inclusion)
    (hp' : p.mapMatrix (universalMatrix K (Index.{u} i.size)) = (asMatrix i L g).val) :
    (modelPoint eB e g).comp J = evaluateMatrix (asMatrix i L g) := by
  let gE : affineSpectrum E L ⟶ (baseChange K E).obj G.val.X := genericPointLift g
  let f : affineSpectrum R L ⟶ Y := genericPointRestrict (gE ≫ e.inv)
  let pE : matrixCoordinates E i.size →ₐ[E] L := pointCoordinates (gE ≫ jE)
  have hpE : (spectrumOfAlgHom pE).left = gE.left ≫ jE.left :=
    congrArg Over.Hom.left (spectrumOf_pointCoordinates (gE ≫ jE))
  have hK : pE.toRingHom.comp (matrixCoordinateMap K E i.size) = p.toRingHom := by
    apply specMap_injective_ringHom
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    change (spectrumOfAlgHom pE).left ≫ _ = (spectrumOfAlgHom p).left
    rw [hpE, hp, Over.comp_left, Category.assoc, hKE, ← Category.assoc, genericPointLift_fst]
  have hf : f.left ≫ j.left = (spectrumOfAlgHom pE).left ≫
      Spec.map (CommRingCat.ofHom (matrixCoordinateMap R E i.size)) := by
    rw [hpE]
    change ((gE.left ≫ e.inv.left) ≫ pullback.fst Y.hom (scalarSpec R E)) ≫ j.left = _
    have hi : e.inv.left ≫ e.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    simp only [Category.assoc, ← hRE, ← Category.assoc e.inv.left, hi, Category.id_comp]
  have hR : ((modelPoint eB e g).comp J).toRingHom =
      pE.toRingHom.comp (matrixCoordinateMap R E i.size) := by
    apply specMap_injective_ringHom
    change Spec.map (CommRingCat.ofHom ((pointCoordinates (f ≫ eB.inv)).toRingHom.comp
      J.toRingHom)) = _
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change (spectrumOfAlgHom (pointCoordinates (f ≫ eB.inv))).left ≫
      (spectrumOfAlgHom J).left = _
    rw [spectrumOf_pointCoordinates, hJ]
    change (f.left ≫ eB.inv.left) ≫ eB.hom.left ≫ j.left = _
    rw [Category.assoc, ← Category.assoc eB.inv.left, ← Over.comp_left, Iso.inv_hom_id,
      Over.id_left, Category.id_comp, hf]
    rfl
  apply matrixEntry_ext
  intro a b
  have hr := DFunLike.congr_fun hR (matrixEntry R a b)
  have hk := DFunLike.congr_fun hK (matrixEntry K a b)
  change (modelPoint eB e g).comp J (matrixEntry R a b) =
    pE (matrixCoordinateMap R E i.size (matrixEntry R a b)) at hr
  change pE (matrixCoordinateMap K E i.size (matrixEntry K a b)) = p _ at hk
  rw [matrixCoordinateMap_entry] at hr hk
  rw [hr, hk, evaluateMatrix_entry]
  exact congrArg (fun M : Matrix (Index.{u} i.size) (Index.{u} i.size) L => M a b) hp'

private theorem evaluateMatrix_map {R L L' : Type u} [CommRing R] [CommRing L] [CommRing L']
    [Algebra R L] [Algebra R L'] {m : ℕ} (f : L →ₐ[R] L')
    (M : Matrix.GeneralLinearGroup (Index.{u} m) L) :
    f.comp (evaluateMatrix M) = evaluateMatrix (Matrix.GeneralLinearGroup.map f.toRingHom M) := by
  apply matrixEntry_ext
  intro a b
  simp only [AlgHom.comp_apply, evaluateMatrix_entry, Matrix.GeneralLinearGroup.map_apply]
  rfl

private theorem continuous_evaluateMatrix {R F : Type u} [CommRing R] [Field F] [Algebra R F]
    [TopologicalSpace F] [IsTopologicalRing F] {m : ℕ} (x : matrixCoordinates R m) :
    Continuous (fun M : Matrix.GeneralLinearGroup (Index.{u} m) F => evaluateMatrix M x) := by
  have h (M : Matrix.GeneralLinearGroup (Index.{u} m) F) :
      (evaluateMatrix (R := R) M).toRingHom =
        (glEvaluation (k := F) M).toRingHom.comp (matrixCoordinateMap R F m) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (matrixDeterminant R m))
    apply MvPolynomial.ringHom_ext
    · intro r
      change evaluateMatrix M (algebraMap (MvPolynomial _ R) _ (MvPolynomial.C r)) =
        glEvaluation (k := F) M (matrixCoordinateMap R F m
          (algebraMap (MvPolynomial _ R) _ (MvPolynomial.C r)))
      rw [CentralCover.matrixCoordinateMap_algebraMap, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq,
        ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply R (MvPolynomial _ R),
        ← IsScalarTower.algebraMap_apply F (MvPolynomial _ F), AlgHom.commutes]
      exact ((glEvaluation (k := F) M).commutes (algebraMap R F r)).symm
    · rintro ⟨a, b⟩
      change evaluateMatrix M (matrixEntry R a b) =
        glEvaluation (k := F) M (matrixCoordinateMap R F m (matrixEntry R a b))
      rw [evaluateMatrix_entry, matrixCoordinateMap_entry]
      exact (glEvaluation_entry M a b).symm
  have hh (M : Matrix.GeneralLinearGroup (Index.{u} m) F) :=
    DFunLike.congr_fun (h M) x
  simp_rw [show ∀ M, evaluateMatrix (R := R) M x =
      glEvaluation (k := F) M (matrixCoordinateMap R F m x) from hh]
  exact continuous_glEvaluation (matrixCoordinateMap R F m x)

private theorem matrixRange_of_modelPoint {R B F : Type u} [CommRing R] [CommRing B]
    [Field F] [Algebra R B] [Algebra R F] {V : ValuationSubring F} [Algebra R V] {m : ℕ}
    (J : matrixCoordinates R m →ₐ[R] B) (ι : V →ₐ[R] F) (hι : ι.toRingHom = V.subtype)
    (p₀ : B →ₐ[R] V) (M : Matrix.GeneralLinearGroup (Index.{u} m) F)
    (hM : (ι.comp p₀).comp J = evaluateMatrix M) :
    M ∈ (Matrix.GeneralLinearGroup.map V.subtype).range := by
  let M₀ : Matrix (Index.{u} m) (Index.{u} m) V := Matrix.of fun a b => p₀ (J (matrixEntry R a b))
  have hdet : M₀.det = (p₀.comp J)
      (algebraMap (MvPolynomial _ R) (matrixCoordinates R m) (matrixDeterminant R m)) := by
    let f := (p₀.comp J).comp
      (Algebra.algHom R (MvPolynomial (Index.{u} m × Index.{u} m) R) (matrixCoordinates R m))
    change M₀.det = f (matrixDeterminant R m)
    rw [matrixDeterminant, AlgHom.map_det]
    rfl
  have hu : IsUnit M₀.det := hdet ▸
    (IsLocalization.Away.algebraMap_isUnit (S := matrixCoordinates R m) (matrixDeterminant R m)).map
      (p₀.comp J)
  refine ⟨Matrix.GeneralLinearGroup.mk'' M₀ hu, Matrix.GeneralLinearGroup.ext fun a b => ?_⟩
  rw [Matrix.GeneralLinearGroup.map_apply, ← hι]
  change (ι.comp p₀).comp J (matrixEntry R a b) = M.val a b
  rw [hM, evaluateMatrix_entry]

private def scalarPoint {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    {G : AffineAlgebraicGroup K} (i : Specs.IntegralModels.MatrixRealization G) :
    RationalPoints G → PointsIn i L :=
  (((groupPointsFunctor K).obj G.val).map (CommAlgCat.ofHom (Algebra.ofId K L))).hom

private theorem scalarPoint_matrix {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    {G : AffineAlgebraicGroup K} (i : Specs.IntegralModels.MatrixRealization G) (g : RationalPoints G) :
    asMatrix i L (scalarPoint i g) = Matrix.GeneralLinearGroup.map (algebraMap K L) (i.onPoints g) :=
  congrArg (fun f => f g)
    ((((groupPointsFunctor K).map i.embedding) ≫ i.matrix.hom).naturality
      (CommAlgCat.ofHom (Algebra.ofId K L)))

private theorem map_matrix_map {C D F I : Type*} [CommRing C] [CommRing D] [CommRing F]
    [Fintype I] [DecidableEq I] (f : C →+* D) (g : D →+* F) (M : Matrix.GeneralLinearGroup I C) :
    Matrix.GeneralLinearGroup.map g (Matrix.GeneralLinearGroup.map f M) =
      Matrix.GeneralLinearGroup.map (g.comp f) M :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

end ModelPoints

section Obstruction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.CentralCover (integersOutside matrixCoordinates)
open Specs.IntegralCentralQuotient (OverBase)
open Specs.Unipotent (Index)
open Kummer

open private glIntegral_iff from LinearAlgebraicGroups.Arithmetic.AdelicGroups

private theorem matrixIntegral_of_comap {K L F : Type u} [Field K] [Field L] [Field F] {m : ℕ}
    (f : K →+* L) (g : K →+* F) (V : ValuationSubring L) (W : ValuationSubring F)
    (h : V.comap f = W.comap g) (M : Matrix.GeneralLinearGroup (Index.{u} m) K)
    (hM : Matrix.GeneralLinearGroup.map f M ∈ (Matrix.GeneralLinearGroup.map V.subtype).range) :
    Matrix.GeneralLinearGroup.map g M ∈ (Matrix.GeneralLinearGroup.map W.subtype).range := by
  simp only [glIntegral_iff, ← map_inv, Matrix.GeneralLinearGroup.map_apply] at hM ⊢
  have hval (x : K) (hx : f x ∈ V) : g x ∈ W := by
    change x ∈ W.comap g
    rw [← h]
    exact hx
  exact ⟨fun a b => hval _ (hM.1 a b), fun a b => hval _ (hM.2 a b)⟩

private theorem integralModelPoint {K E B : Type u} [Field K] [Field E]
    [Algebra K E] [CommRing B] (D : GlobalFieldData.{u, v} K) (D' : GlobalFieldData.{u, v} E)
    (S : Set D'.FinitePlace) (r : D'.FinitePlace → D.FinitePlace)
    (hr : ∀ w, globalValuationRing D (r w) = (globalValuationRing D' w).comap (algebraMap K E))
    {G : AffineAlgebraicGroup K} (i : Specs.IntegralModels.MatrixRealization G)
    [Algebra (integersOutside D' S) B]
    (J : matrixCoordinates (integersOutside D' S) i.size →ₐ[integersOutside D' S] B)
    (hJ : Function.Surjective J) (g : RationalPoints G) (p : B →ₐ[integersOutside D' S] E)
    (hp : p.comp J = evaluateMatrix (Matrix.GeneralLinearGroup.map (algebraMap K E) (i.onPoints g)))
    (w : D'.FinitePlace) (hw : w ∉ S)
    (hg : localPoint D i (.inl (r w)) g ∈ integralPoints D i (r w)) :
      letI : Algebra (integersOutside D' S) (D'.integers w) :=
        (integersOutsideToLocal D' S w hw).toAlgebra
      ∃ p₀ : B →ₐ[integersOutside D' S] D'.integers w,
        (D'.integers w).subtype.comp p₀.toRingHom = (D'.embedding (.inl w)).comp p.toRingHom := by
  let R := ↥(integersOutside D' S)
  let F := D'.FiniteCompletion w
  let V := D'.integers w
  let e : E →+* F := D'.embedding (.inl w)
  let : Algebra R F := (e.comp (algebraMap R E)).toAlgebra
  let : Algebra R V := (integersOutsideToLocal D' S w hw).toAlgebra
  let ι : V →ₐ[R] F := { V.subtype with commutes' := fun _ => rfl }
  let f : E →ₐ[R] F := { e with commutes' := fun _ => rfl }
  have hmem := hg
  change asMatrix i _ (localPoint D i (.inl (r w)) g) ∈
    (Matrix.GeneralLinearGroup.map (D.integers (r w)).subtype).range at hmem
  rw [localPoint_matrix] at hmem
  have hV : (D.integers (r w)).comap (D.embedding (.inl (r w))) =
      V.comap (e.comp (algebraMap K E)) := by
    rw [← ValuationSubring.comap_comap]
    exact hr w
  obtain ⟨M₀, hM₀⟩ := matrixIntegral_of_comap _ _ _ _ hV (i.onPoints g) hmem
  have hp₀ : (f.comp p).comp J = ι.comp (evaluateMatrix M₀) := by
    rw [AlgHom.comp_assoc, hp, evaluateMatrix_map, evaluateMatrix_map]
    congr 1
    exact (map_matrix_map _ _ _).trans hM₀.symm
  obtain ⟨p₀, h⟩ := closedModelPointLift J hJ ι Subtype.val_injective (f.comp p)
    (evaluateMatrix M₀) hp₀
  exact ⟨p₀, congrArg AlgHom.toRingHom h⟩

private theorem restriction_finite_fibre {K E : Type u} [Field K] [Field E] [Algebra K E]
    (D : GlobalFieldData.{u, v} K) (D' : GlobalFieldData.{u, v} E)
    (r : D'.FinitePlace → D.FinitePlace)
    (hr : ∀ w, globalValuationRing D (r w) = (globalValuationRing D' w).comap (algebraMap K E))
    (w : D.FinitePlace) : (r ⁻¹' {w}).Finite := by
  classical
  have hex : ∃ x : K, x ∉ globalValuationRing D w := by
    by_contra! h
    exact globalValuationRing_ne_top D w (top_unique fun x _ => h x)
  obtain ⟨x, hx⟩ := hex
  refine (D'.finite_nonintegral (algebraMap K E x)).subset ?_
  intro z hz
  have heq : r z = w := hz
  change algebraMap K E x ∉ globalValuationRing D' z
  intro h
  apply hx
  rw [← heq, hr z]
  exact h

open Specs.CentralCoverSpreading (KernelCoordinates)

private theorem class_integralAt {E R B A : Type u} [Field E] [CommRing R] [CommRing B]
    [CommRing A] [Algebra R E] [Algebra R B] [HopfAlgebra R A] [Algebra B A]
    (D : GlobalFieldData.{u, v} E) (w : D.FinitePlace) [Algebra R (D.integers w)]
    {I : Type} (n : I → ℕ) (π : A →ₐc[R] KernelCoordinates R n) (k : I)
    (p : B →ₐ[R] E) (p₀ : B →ₐ[R] D.integers w)
    (hp₀ : (D.integers w).subtype.comp p₀.toRingHom = (D.embedding (.inl w)).comp p.toRingHom)
    (hclass : ∀ {L : Type u} [CommRing L] [Algebra R L] [IsLocalRing L] (f : B →ₐ[R] L),
      ∃! c, PullbackHasClass n π f k c)
    (c : Classes E (n k)) (hc : PullbackHasClass n π p k c) :
    c ∈ localUnitCondition D w (n k) := by
  let F := D.FiniteCompletion w
  let e : E →+* F := D.embedding (.inl w)
  let : Algebra R F := (e.comp (algebraMap R E)).toAlgebra
  let pF : B →ₐ[R] F := ({ e with commutes' := fun _ => rfl } : E →ₐ[R] F).comp p
  obtain ⟨d, hd⟩ := (hclass p₀).exists
  have hl := pullbackClassNaturality n π p₀ pF (D.integers w).subtype hp₀ k d hd
  have hg := pullbackClassNaturality n π p pF e rfl k c hc
  exact ⟨d, (hclass pF).unique hl hg⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem openAroundIntegralClass {K R B A : Type u} [Field K] [CommRing R] [CommRing B]
    [CommRing A] [HopfAlgebra R B] [HopfAlgebra R A] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : Specs.IntegralModels.MatrixRealization G) (w : D.FinitePlace)
    [Algebra R (D.integers w)] [Algebra R (D.FiniteCompletion w)]
    {I : Type} (n : I → ℕ) (q₀ : B →ₐc[R] A) (π : A →ₐc[R] KernelCoordinates R n)
    (hT : Specs.IntegralCentralQuotient.IsRightTorsor q₀ π) (k : I) (hk : 0 < n k)
    (J : matrixCoordinates R i.size →ₐ[R] B) (hJ : Function.Surjective J)
    (pLocal : LocalPoints D i (.inl w) → (B →ₐ[R] D.FiniteCompletion w))
    (hLocalMatrix : ∀ x, (pLocal x).comp J =
      evaluateMatrix (L := D.FiniteCompletion w) (asMatrix i (D.Completion (.inl w)) x))
    (hclass : letI : Algebra B A := q₀.toAlgHom.toAlgebra
      ∀ x, ∃! c, PullbackHasClass n π (pLocal x) k c)
    (p₀ : B →ₐ[R] D.integers w) (ι : D.integers w →ₐ[R] D.FiniteCompletion w)
    (hι : ι.toRingHom = (D.integers w).subtype)
    (x₀ : LocalPoints D i (.inl w)) (hx₀ : pLocal x₀ = ι.comp p₀)
    (a : Classes (D.integers w) (n k))
    (hAt : letI : Algebra B A := q₀.toAlgHom.toAlgebra
      PullbackHasClass n π p₀ k a)
    (C : Set (Classes (D.FiniteCompletion w) (n k))) (hC : C.Finite)
    (ha : map (D.integers w).subtype (n k) a ∉ C) :
    letI : Algebra B A := q₀.toAlgHom.toAlgebra
    ∃ U : Set (LocalPoints D i (.inl w)), IsOpen U ∧ U.Nonempty ∧
      U ⊆ integralPoints D i w ∧
      ∀ x ∈ U, ∀ c, PullbackHasClass n π (pLocal x) k c → c ∉ C := by
  let : Algebra B A := q₀.toAlgHom.toAlgebra
  let F := D.FiniteCompletion w
  let : Algebra K F := completionAlgebra D (.inl w)
  let : IsNonarchimedeanLocalField F := D.finiteCompletion_isLocalField w
  have hEvaluate (b : B) : Continuous (fun x => pLocal x b) := by
    obtain ⟨b, rfl⟩ := hJ b
    have hb (x : LocalPoints D i (.inl w)) :
        pLocal x (J b) = evaluateMatrix (asMatrix i F x) b :=
      DFunLike.congr_fun (hLocalMatrix x) b
    simp_rw [hb]
    exact (continuous_evaluateMatrix b).comp continuous_induced_dom
  let cLocal (x : LocalPoints D i (.inl w)) : Classes F (n k) := (hclass x).exists.choose
  have hcLocal (x : LocalPoints D i (.inl w)) :
      PullbackHasClass n π (pLocal x) k (cLocal x) ∧
        ∀ d, PullbackHasClass n π (pLocal x) k d → d = cLocal x :=
    ⟨(hclass x).exists.choose_spec, fun _ hd => (hclass x).unique hd (hclass x).exists.choose_spec⟩
  have hContinuous : Continuous cLocal :=
    continuousPullbackClass n q₀ π hT k hk _ pLocal hEvaluate cLocal hcLocal
  let : T2Space (Classes F (n k)) := localFieldUnitClassesHausdorff F _ hk
  let U := (integralPoints D i w : Set (LocalPoints D i (.inl w))) ∩ cLocal ⁻¹' Cᶜ
  refine ⟨U, (integralCompactOpen D i w).2.inter
    (hC.isClosed.isOpen_compl.preimage hContinuous), ?_, Set.inter_subset_left, ?_⟩
  · have hxint : x₀ ∈ integralPoints D i w :=
      matrixRange_of_modelPoint J ι hι p₀ _ (by rw [← hx₀]; exact hLocalMatrix x₀)
    have hxclass : map (D.integers w).subtype (n k) a = cLocal x₀ :=
      (hcLocal x₀).2 _ (pullbackClassNaturality n π p₀ (pLocal x₀) (D.integers w).subtype
        (by rw [← hι]; exact congrArg AlgHom.toRingHom hx₀.symm) k _ hAt)
    refine ⟨x₀, hxint, ?_⟩
    change cLocal x₀ ∉ C
    rwa [← hxclass]
  · intro x hx c hc
    rw [(hcLocal x).2 _ hc]
    exact hx.2

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- A nontrivial simply connected covering kernel prevents density in the
restricted product, including when the kernel is not smooth. -/
theorem simplyConnectednessNecessary : Specs.SimpleConnectednessNecessary.Statement.{u, v} := by
  classical
  intro K _ D G hG hsc i S _hS
  obtain ⟨jK, hjK⟩ := matrixEmbeddingWithEvaluation i
  obtain ⟨H, q, N, _, _, _, _, _, _, _, E, hE, hKE, hfinite, hgal, hN, datum, D', jE,
    _, _, _, _, hexp, hjE, hmodels⟩ := CentralCover.globalCoverWithModels D G hG jK
  obtain ⟨k, hk⟩ := hexp.mpr hsc
  let := datum.finiteIndices
  obtain ⟨S₀, hS₀, _, hFrac⟩ := CentralCover.integersOutsideFractionRing D' ∅ Set.finite_empty
  obtain ⟨S', hS', hSS', ⟨model⟩⟩ := hmodels S₀ hS₀
  let R := ↥(integersOutside D' S')
  let : IsFractionRing R E := hFrac S' hSS'
  obtain ⟨r, hr, hrLocal⟩ := finitePlaceRestriction D D'
  obtain ⟨eZ, _, htorus⟩ := TorusFibreKummerRealization.torusFibreKummerRealization model
  obtain ⟨B, A, hB, hA, hBR, hAR, eG, eH, q₀, π, hq, hπ, hT, hclass, cGlobal,
    hcGlobal, _⟩ :=
    coverPullbackFiniteness D' S' hS' datum.exponents datum.positiveExponents model.map
      model.kernelInclusion model.target.prop.1 model.source.prop.1 model.torsor eZ
  let : Algebra B A := q₀.toAlgHom.toAlgebra
  obtain ⟨s, hs, hrealize⟩ := htorus eG eH q₀ π hq hπ hT
  let eB : CentralCover.affineSpectrum R B ≅ model.target.val.X :=
    (Grp.forget (OverBase R)).mapIso eG
  let eTarget : (Over.pullback (CentralCover.scalarSpec R E)).obj model.target.val.X ≅
      (baseChange K E).obj G.val.X := (Grp.forget (OverBase E)).mapIso model.genericTarget
  obtain ⟨J, hJ, hJSpec⟩ := closedMatrixCoordinates eB model.matrixInclusion model.matrixClosed
  let pGlobal (g : RationalPoints G) : B →ₐ[R] E :=
    modelPoint eB eTarget (scalarPoint i g)
  have hGlobalMatrix (g : RationalPoints G) : (pGlobal g).comp J =
      evaluateMatrix (Matrix.GeneralLinearGroup.map (algebraMap K E) (i.onPoints g)) := by
    obtain ⟨p, hp, hp'⟩ := hjK E (scalarPoint i g)
    rw [← scalarPoint_matrix i g]
    exact modelPoint_matrix hjE model.genericMatrix J hJSpec _ p hp hp'

  let Q : Set D.FinitePlace := Sum.inl ⁻¹' (S : Set D.Place) ∪ r '' S'
  have hQ : Q.Finite :=
    (S.finite_toSet.preimage Sum.inl_injective.injOn).union (hS'.image r)
  let Qfin := hQ.toFinset
  let T : Finset D.Place := S ∪ Qfin.image Sum.inl
  -- Exclude every extension of an exceptional base place when bounding global classes.
  let S₁ : Set D'.Place := Sum.inl '' (r ⁻¹' Q)
  have hS₁ : S₁.Finite := (hQ.preimage' fun w _ => restriction_finite_fibre D D' r hr w).image _
  let : Finite (UnramifiedOutside D' S₁ (datum.exponents k)) :=
    globalFiniteness D' S₁ hS₁ _ (datum.positiveExponents k)
  let P : Set (Classes E (datum.exponents k)) := UnramifiedOutside D' S₁ (datum.exponents k)
  have hP : P.Finite := Set.toFinite _
  obtain ⟨w, hw, e, he, a, ha⟩ := exists_separatingUnit D Qfin (datum.exponents k) hk P hP
  have hwQ : w ∉ Q := by simpa only [Qfin, Set.Finite.mem_toFinset] using hw
  have hwT : Sum.inl w ∉ T := by
    intro hwT
    rcases Finset.mem_union.mp hwT with hwS | hwS
    · exact hwQ (Or.inl hwS)
    · obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hwS
      exact hw ((Sum.inl.inj hzw) ▸ hz)
  let F := D.FiniteCompletion w
  let V := D.integers w
  let : Algebra K F := completionAlgebra D (.inl w)
  let : Algebra E F := e.toAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' he.symm
  let : Algebra R F := (e.comp (algebraMap R E)).toAlgebra
  let : IsScalarTower R E F := IsScalarTower.of_algebraMap_eq' rfl
  let rv : R →+* V := (e.comp (algebraMap R E)).codRestrict V.toSubring
    (hrLocal S' w (fun hh => hwQ (Or.inr hh)) e he)
  let : Algebra R V := rv.toAlgebra
  let ι : V →ₐ[R] F := { V.subtype with commutes' := fun _ => rfl }
  let ef : E →ₐ[R] F := IsScalarTower.toAlgHom R E F
  let pLocal : LocalPoints D i (.inl w) → (B →ₐ[R] F) := modelPoint (L := F) (i := i) eB eTarget
  have hLocalMatrix (x : LocalPoints D i (.inl w)) :
      (pLocal x).comp J = evaluateMatrix (asMatrix i F x) := by
    obtain ⟨p, hp, hp'⟩ := hjK F x
    exact modelPoint_matrix (L := F) hjE model.genericMatrix J hJSpec x p hp hp'
  let aT : datum.indices → Vˣ := fun j => if j = k then a else 1
  obtain ⟨t, p₀, _, _, hAt⟩ := hrealize (V := V) aT
  obtain ⟨x₀, hx₀⟩ := modelPoint_surjective (L := F) (i := i) eB eTarget (ι.comp p₀)
  have ha' : PullbackHasClass datum.exponents π p₀ k (classOf (datum.exponents k) a) := by
    simpa [aT] using hAt k
  obtain ⟨U, hUopen, hUne, hUintegral, hUclass⟩ :=
    openAroundIntegralClass D i w datum.exponents q₀ π hT k (datum.positiveExponents k) J hJ
      pLocal hLocalMatrix (fun x => hclass (pLocal x) k) p₀ ι rfl x₀ hx₀ _
      ha' (map e (datum.exponents k) '' P) (hP.image _) ha
  refine obstructionFromLocalOpen D i S T w Finset.subset_union_left hwT U hUopen hUne hUintegral ?_
  intro g hg hUg
  have hGlobalClass : cGlobal (pGlobal g) k ∈ P := by
    change cGlobal (pGlobal g) k ∈ UnramifiedOutside D' S₁ (datum.exponents k)
    rw [UnramifiedOutside, Subgroup.mem_iInf]
    rintro ⟨z, hz⟩
    have hzQ : r z ∉ Q := fun h => hz ⟨z, h, rfl⟩
    have hz' : z ∉ S' := fun h => hzQ (Or.inr ⟨z, h, rfl⟩)
    have hg' : localPoint D i (.inl (r z)) g ∈ integralPoints D i (r z) := by
      apply hg
      intro ht
      rcases Finset.mem_union.mp ht with ht | ht
      · exact hzQ (Or.inl ht)
      · obtain ⟨z', hz', heq⟩ := Finset.mem_image.mp ht
        exact hzQ ((Sum.inl.inj heq) ▸ hQ.mem_toFinset.mp hz')
    let : Algebra R (D'.integers z) := (integersOutsideToLocal D' S' z hz').toAlgebra
    obtain ⟨p₀, hp₀⟩ := integralModelPoint D D' S' r hr i J hJ g (pGlobal g)
      (hGlobalMatrix g) z hz' hg'
    exact class_integralAt D' z datum.exponents π k (pGlobal g) p₀ hp₀
      (fun f => hclass f k) _ (hcGlobal (pGlobal g) k).1
  have hcoeff : ef.comp (pGlobal g) = pLocal (localPoint D i (.inl w) g) := by
    have hm : asMatrix i F (localPoint D i (.inl w) g) =
        Matrix.GeneralLinearGroup.map (D.embedding (.inl w)) (i.onPoints g) :=
      localPoint_matrix D i (.inl w) g
    ext b
    obtain ⟨b, rfl⟩ := hJ b
    change ((ef.comp (pGlobal g)).comp J) b = (pLocal (localPoint D i (.inl w) g)).comp J b
    rw [AlgHom.comp_assoc, hGlobalMatrix, evaluateMatrix_map, hLocalMatrix, hm, map_matrix_map]
    rw [show ef.toRingHom = e from rfl, he]
    rfl
  have hLocalClass := pullbackClassNaturality datum.exponents π (pGlobal g) (pLocal _)
    e (congrArg AlgHom.toRingHom hcoeff) k _ (hcGlobal (pGlobal g) k).1
  exact hUclass _ hUg _ hLocalClass ⟨_, hGlobalClass, rfl⟩

end Obstruction

end LinearAlgebraicGroups.Arithmetic.SimpleConnectednessNecessary
