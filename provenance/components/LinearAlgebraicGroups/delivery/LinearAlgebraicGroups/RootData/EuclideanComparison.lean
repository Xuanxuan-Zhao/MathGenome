import Specs.LinearAlgebraicGroups.RootData.EuclideanComparison
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.GroupTheory.GroupAction.Pointwise
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Flat.Domain

noncomputable section

open scoped TensorProduct Pointwise
open Set Module LieAlgebrasAndRepresentations

namespace LinearAlgebraicGroups.RootData

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
variable (P : RootDatum (ι := ι) X Y)

private theorem span_realRoot : Submodule.span ℝ (range (realRoot P)) = ⊤ := by
  apply Submodule.map_injective_of_injective (realRootSpan P).subtype_injective
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
  rfl

private theorem realReflection_root (i j : ι) :
    realReflection P i (realRoot P j) = realRoot P (P.reflectionPerm i j) := by
  apply Subtype.ext
  change (realRootSpan P).subtype (realReflection P i (realRoot P j)) = _
  rw [realReflection, Module.reflection_apply, map_sub, map_smul, realCoroot_apply_root]
  change (1 : ℝ) ⊗ₜ[ℤ] P.root j - (P.pairing j i : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] P.root i) =
    (1 : ℝ) ⊗ₜ[ℤ] P.root (P.reflectionPerm i j)
  have h := congrArg (TensorProduct.mk ℤ ℝ X 1) (P.reflectionPerm_root i j)
  rw [Int.cast_smul_eq_zsmul]
  rw [map_sub, map_zsmul] at h
  exact h

private theorem realReflection_baseChange (i : ι) (x : realRootSpan P) :
    (realRootSpan P).subtype (realReflection P i x) =
      LinearEquiv.baseChange ℤ ℝ X X (P.reflection i) ((realRootSpan P).subtype x) := by
  let s := (realRootSpan P).subtype
  let f := s.comp (realReflection P i).toLinearMap
  let g := (LinearEquiv.baseChange ℤ ℝ X X (P.reflection i)).toLinearMap.comp s
  have heq : f = g := by
    apply LinearMap.ext_on (span_realRoot P)
    rintro _ ⟨j, rfl⟩
    change s (realReflection P i (realRoot P j)) = _
    rw [realReflection_root]
    change (1 : ℝ) ⊗ₜ[ℤ] P.root (P.reflectionPerm i j) =
      LinearEquiv.baseChange ℤ ℝ X X (P.reflection i) (1 ⊗ₜ[ℤ] P.root j)
    rw [LinearEquiv.baseChange_tmul, RootPairing.reflection_apply]
    exact congrArg (TensorProduct.mk ℤ ℝ X 1) (P.reflectionPerm_root i j).symm
  exact DFunLike.congr_fun heq x

private theorem weyl_image_root (g : realWeylGroup P) :
    g.val '' range (realRoot P) = range (realRoot P) := by
  let R := range (realRoot P)
  have hle : realWeylGroup P ≤ MulAction.stabilizer (realRootSpan P ≃ₗ[ℝ] realRootSpan P) R := by
    apply (Subgroup.closure_le _).2
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    change realReflection P i '' R = R
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      rw [realReflection_root]
      exact mem_range_self _
    · rintro ⟨j, rfl⟩
      refine ⟨realRoot P ((P.reflectionPerm i).symm j), mem_range_self _, ?_⟩
      rw [realReflection_root, Equiv.apply_symm_apply]
  exact MulAction.mem_stabilizer_iff.mp (hle g.property)

private theorem weyl_roots_faithful (g h : realWeylGroup P)
    (heq : ∀ x ∈ range (realRoot P), g.val x = h.val x) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.ext_on (span_realRoot P) heq

private theorem finite_realWeylGroup [Finite ι] : Finite (realWeylGroup P) := by
  let R := range (realRoot P)
  let : Finite R := Set.finite_range (realRoot P) |>.to_subtype
  let perm (g : realWeylGroup P) : Equiv.Perm R :=
    Equiv.Perm.subtypePerm g.val.toEquiv fun x => by
      change g.val x ∈ R ↔ x ∈ R
      calc
        g.val x ∈ R ↔ g.val x ∈ g.val '' R := by rw [weyl_image_root P g]
        _ ↔ x ∈ R := g.val.injective.mem_set_image
  apply Finite.of_injective perm
  intro g h heq
  exact weyl_roots_faithful P g h fun x hx =>
    congrArg Subtype.val (congrFun (congrArg Equiv.toFun heq) ⟨x, hx⟩)

private theorem realRoot_eq_sum {B : P.Base} {j : ι} {c : ι → ℤ}
    (hc : P.root j = ∑ i ∈ B.support, c i • P.root i) :
    realRoot P j = ∑ i : B.support, (c i : ℝ) • realRoot P i := by
  classical
  apply Subtype.ext
  change _ = (realRootSpan P).subtype (∑ i : B.support, (c i : ℝ) • realRoot P i)
  have h := congrArg (TensorProduct.mk ℤ ℝ X 1) hc
  simp only [map_sum, map_zsmul, TensorProduct.mk_apply] at h
  rw [map_sum]
  simp only [map_smul, Int.cast_smul_eq_zsmul]
  exact h.trans (Finset.sum_coe_sort B.support
    (fun i => c i • ((1 : ℝ) ⊗ₜ[ℤ] P.root i))).symm

private theorem real_basis_exists (B : P.Base) :
    ∃ b : Basis B.support ℝ (realRootSpan P), ∀ i, b i = realRoot P i := by
  classical
  let r (i : B.support) := realRoot P i
  have hind : LinearIndependent ℝ r := by
    apply LinearIndependent.of_comp (realRootSpan P).subtype
    exact Module.Flat.linearIndependent_one_tmul B.linearIndepOn_root
  have hspan : Submodule.span ℝ (range r) = ⊤ := by
    rw [← span_realRoot P]
    apply le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩
      exact mem_range_self i.val
    · rintro _ ⟨j, rfl⟩
      obtain ⟨c, _, _, hc⟩ := B.exists_root_eq_sum_int j
      apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
      exact ⟨fun i => (c i : ℝ), (realRoot_eq_sum P hc).symm⟩
  exact ⟨Basis.mk hind hspan.ge, Basis.mk_apply _ _⟩

private def averagedForm {I : Type*} [Fintype I] [Fintype (realWeylGroup P)]
    (b : Basis I ℝ (realRootSpan P)) (x y : realRootSpan P) : ℝ :=
  ∑ g : realWeylGroup P, ∑ i, b.repr (g.val x) i * b.repr (g.val y) i

@[instance_reducible] private def averagedMetric {I : Type*} [Fintype I] [Fintype (realWeylGroup P)]
    (b : Basis I ℝ (realRootSpan P)) : InnerProductSpace.Core ℝ (realRootSpan P) where
  inner := averagedForm P b
  conj_inner_symm x y := by simp [averagedForm, mul_comm]
  add_left x y z := by simp [averagedForm, add_mul, Finset.sum_add_distrib]
  smul_left x y t := by simp [averagedForm, mul_assoc, Finset.mul_sum]
  re_inner_nonneg x := by
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  definite x hx := by
    have h (g : realWeylGroup P) :
        ∑ i, b.repr (g.val x) i * b.repr (g.val x) i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _) |>.mp hx) g (Finset.mem_univ _)
    apply b.repr.injective
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_self_nonneg _) |>.mp
      (h 1)) i (Finset.mem_univ _)
    simpa using hi

private theorem averagedForm_invariant {I : Type*} [Fintype I] [Fintype (realWeylGroup P)]
    (b : Basis I ℝ (realRootSpan P)) (g : realWeylGroup P) (x y : realRootSpan P) :
    averagedForm P b (g.val x) (g.val y) = averagedForm P b x y := by
  unfold averagedForm
  exact Equiv.sum_comp (Equiv.mulRight g)
    (fun h : realWeylGroup P => ∑ i, b.repr (h.val x) i * b.repr (h.val y) i)


private theorem realRoot_ne_zero (i : ι) : realRoot P i ≠ 0 := by
  intro h
  have heq := realCoroot_apply_root P i i
  rw [h, map_zero] at heq
  norm_num at heq

private theorem coroot_of_invariant_inner
    (metric : InnerProductSpace.Core ℝ (realRootSpan P))
    (hinv : letI : NormedAddCommGroup (realRootSpan P) := metric.toNormedAddCommGroup
      let : InnerProductSpace ℝ (realRootSpan P) := InnerProductSpace.ofCore metric.toCore
      ∀ (g : realWeylGroup P) (x y : realRootSpan P),
        inner ℝ (g.val x) (g.val y) = inner ℝ x y)
    (i : ι) (x : realRootSpan P) :
    let : NormedAddCommGroup (realRootSpan P) := metric.toNormedAddCommGroup
    let : InnerProductSpace ℝ (realRootSpan P) := InnerProductSpace.ofCore metric.toCore
    realCoroot P i x = 2 * inner ℝ x (realRoot P i) / inner ℝ (realRoot P i) (realRoot P i) := by
  let : NormedAddCommGroup (realRootSpan P) := metric.toNormedAddCommGroup
  let : InnerProductSpace ℝ (realRootSpan P) := InnerProductSpace.ofCore metric.toCore
  let g : realWeylGroup P := ⟨realReflection P i, Subgroup.subset_closure (mem_range_self i)⟩
  have hin := hinv g x (realRoot P i)
  change inner ℝ (realReflection P i x) (realReflection P i (realRoot P i)) = _ at hin
  have hneg : realReflection P i (realRoot P i) = -realRoot P i := by
    rw [realReflection, Module.reflection_apply, realCoroot_apply_root]
    simp [two_smul]
  rw [hneg, inner_neg_right, realReflection, Module.reflection_apply,
    inner_sub_left, real_inner_smul_left] at hin
  apply (eq_div_iff (inner_self_ne_zero.mpr (realRoot_ne_zero P i))).mpr
  linarith

private theorem latticeEmbedding_injective [Module.Free ℤ X] :
    Function.Injective (TensorProduct.mk ℤ ℝ X 1) := by
  intro x y h
  let b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  have h' := congrArg (fun a => (b.baseChange ℝ).repr a i) h
  simpa [zsmul_eq_mul] using h'

private theorem realRoot_injective [Module.Free ℤ X] : Function.Injective (realRoot P) :=
  fun _ _ h => P.root.injective (latticeEmbedding_injective (congrArg Subtype.val h))

private theorem realRoot_reduced [Module.Free ℤ X] [P.IsReduced] (i j : ι)
    (h : realRoot P j ∈ Submodule.span ℝ ({realRoot P i} : Set (realRootSpan P))) :
    realRoot P j = realRoot P i ∨ realRoot P j = -realRoot P i := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
  have hpair := congrArg (realCoroot P i) ht
  simp only [map_smul, smul_eq_mul, realCoroot_apply_root, RootPairing.pairing_same,
    Int.cast_ofNat] at hpair
  have hmul : (P.pairing j i : ℝ) • realRoot P i = (2 : ℝ) • realRoot P j := by
    rw [← hpair, ← ht, smul_smul, mul_comm]
  have hinteger : P.pairing j i • P.root i = (2 : ℤ) • P.root j := by
    apply latticeEmbedding_injective (X := X)
    rw [map_zsmul, map_zsmul]
    have heq := congrArg (realRootSpan P).subtype hmul
    rw [map_smul, map_smul] at heq
    rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ]
    exact heq
  have hdep : ¬ LinearIndependent ℤ ![P.root j, P.root i] := by
    intro hind
    rw [LinearIndependent.pair_iff] at hind
    have hz := hind (-2) (P.pairing j i) (by rw [neg_smul, hinteger, neg_add_cancel])
    norm_num at hz
  rcases RootPairing.IsReduced.eq_or_eq_neg j i hdep with h | h
  · exact Or.inl (Subtype.ext (by change (1 : ℝ) ⊗ₜ[ℤ] P.root j = (1 : ℝ) ⊗ₜ[ℤ] P.root i; rw [h]))
  · exact Or.inr (Subtype.ext (by
      change (1 : ℝ) ⊗ₜ[ℤ] P.root j = -((1 : ℝ) ⊗ₜ[ℤ] P.root i)
      rw [h, TensorProduct.tmul_neg]))


/-- The invariant Euclidean realization of an integral based root datum. -/
theorem euclideanComparison : EuclideanComparisonSpecs.comparisonType := by
  intro ι X Y _ _ _ _ _ _ _ P _ B
  classical
  let E := realRootSpan P
  let R := range (realRoot P)
  let : Finite (realWeylGroup P) := finite_realWeylGroup P
  let : Fintype (realWeylGroup P) := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := real_basis_exists P B
  let metric := averagedMetric P b
  let : NormedAddCommGroup E := metric.toNormedAddCommGroup
  let : InnerProductSpace ℝ E := InnerProductSpace.ofCore metric.toCore
  have hinv : ∀ (g : realWeylGroup P) (x y : E),
      inner ℝ (g.val x) (g.val y) = inner ℝ x y := averagedForm_invariant P b
  have hcoroot := coroot_of_invariant_inner P metric hinv
  have href (i : ι) (x : E) : realReflection P i x = rootReflection (realRoot P i) x := by
    rw [realReflection, Module.reflection_apply, rootReflection, ← hcoroot]
  have hR : IsRootSystem R := {
    finite := Set.finite_range _
    nonzero := by rintro _ ⟨i, rfl⟩; exact realRoot_ne_zero P i
    reflection_mem := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rw [← href, realReflection_root]
      exact mem_range_self _
    integral := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact ⟨P.pairing j i, (hcoroot i (realRoot P j)).symm.trans (realCoroot_apply_root P i j)⟩
    reduced := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact realRoot_reduced P i j
    span_eq_top := span_realRoot P }
  let : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let ℓ : E →ₗ[ℝ] ℝ := b.constr ℝ (fun _ => 1)
  let z : E := (InnerProductSpace.toDual ℝ E).symm (ℓ.toContinuousLinearMap)
  have hz (i : ι) : inner ℝ z (realRoot P i) = (B.height i : ℝ) := by
    rw [InnerProductSpace.toDual_symm_apply]
    change ℓ (realRoot P i) = _
    obtain ⟨c, _, _, hc⟩ := B.exists_root_eq_sum_int i
    rw [realRoot_eq_sum P hc, map_sum, B.height_eq_sum hc]
    simp only [map_smul, ← hb, ℓ, Basis.constr_basis, smul_eq_mul, mul_one, Int.cast_sum]
    exact Finset.sum_coe_sort B.support (fun i => (c i : ℝ))
  have hregular : RootRegular R z := by
    rintro _ ⟨i, rfl⟩
    simpa only [hz, Int.cast_ne_zero] using B.height_ne_zero i
  have hpos (i : ι) : realRoot P i ∈ positiveRoots R z ↔ B.IsPos i := by
    change (realRoot P i ∈ R ∧ 0 < inner ℝ z (realRoot P i)) ↔ _
    simp [R, hz, RootPairing.Base.isPos_iff]
  have hpositive : positiveRoots R z = realRoot P '' {i | B.IsPos i} := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, rfl⟩ := ha.1
      exact ⟨i, (hpos i).mp ha, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hpos i).mpr hi
  have hsimple (i : B.support) : realRoot P i ∈ simpleRoots R z := by
    refine ⟨(hpos i).mpr (B.isPos_of_mem_support i.property), ?_⟩
    intro x hx y hy heq
    obtain ⟨j, rfl⟩ := hx.1
    obtain ⟨k, rfl⟩ := hy.1
    have hj : 0 < B.height j := (hpos j).mp hx
    have hk : 0 < B.height k := (hpos k).mp hy
    have he := congrArg (inner ℝ z) heq
    rw [inner_add_right, hz, hz, hz, B.height_one_of_mem_support i.property] at he
    have hheight : (1 : ℤ) = B.height j + B.height k := by exact_mod_cast he
    omega
  have support_of_simple (i : ι) (hi : realRoot P i ∈ simpleRoots R z) : i ∈ B.support := by
    have hpi := (hpos i).mp hi.1
    have aux := hpi.induction_on_add
      (p := fun j => B.IsPos j ∧ (realRoot P j ∈ simpleRoots R z → j ∈ B.support))
      (fun j hj => ⟨B.isPos_of_mem_support hj, fun _ => hj⟩)
      (fun j k l heq hj hk => by
        refine ⟨hj.1.add (B.isPos_of_mem_support hk) heq, fun hl => ?_⟩
        exfalso
        apply hl.2 (realRoot P j) ((hpos j).mpr hj.1)
          (realRoot P k) ((hpos k).mpr (B.isPos_of_mem_support hk))
        apply Subtype.ext
        exact (congrArg (TensorProduct.mk ℤ ℝ X 1) heq).trans (map_add _ _ _))
    exact aux.2 hi
  have hbSimple : IsSimpleBasis R z b := by
    change range b = simpleRoots R z
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [hb]
      exact hsimple i
    · intro hx
      obtain ⟨i, rfl⟩ := hx.1.1
      exact ⟨⟨i, support_of_simple i hx⟩, hb _⟩
  refine ⟨realRoot_injective P, realReflection_baseChange P,
    inferInstance, weyl_image_root P, weyl_roots_faithful P, metric,
    hinv, hcoroot, href, hR, z, b, hregular, hz, hpositive, hb, hbSimple, ?_, ?_, ?_⟩
  · ext i j
    change rootCartan (b j) (b i) = (P.pairing j i : ℝ)
    rw [hb, hb, rootCartan, ← hcoroot, realCoroot_apply_root]
  · intro i j
    rw [hb, coroot, real_inner_smul_right, ← realCoroot_apply_root P i j, hcoroot]
    ring
  · exact Matrix.posDef_gram_of_linearIndependent b.linearIndependent


private theorem det_integralCartan_ne_zero [Finite ι]
    [Module.Free ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ X] [Module.Finite ℤ Y]
    [P.IsReduced] (B : P.Base) [DecidableEq B.support] :
    (integralCartan P B).det ≠ 0 := by
  obtain ⟨_, _, _, _, _, metric, _, _, _, _, _, b, _, _, _, _, _, hCartan, _, hGram⟩ :=
    euclideanComparison P B
  let E := realRootSpan P
  let : NormedAddCommGroup E := metric.toNormedAddCommGroup
  let : InnerProductSpace ℝ E := InnerProductSpace.ofCore metric.toCore
  let D := Matrix.diagonal (fun i : B.support => inner ℝ (b i) (b i))
  have hscaled : D * cartanMatrix b = (2 : ℝ) • Matrix.gram ℝ b := by
    ext i j
    simp only [D, Matrix.diagonal_mul, cartanMatrix, rootCartan, Matrix.smul_apply,
      Matrix.gram_apply, smul_eq_mul]
    rw [mul_comm, div_mul_cancel₀ _ (inner_self_ne_zero.mpr (b.ne_zero i)), real_inner_comm]
  have hdet : (cartanMatrix b).det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det hscaled
    rw [Matrix.det_mul, hz, mul_zero, Matrix.det_smul] at h
    exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hGram.det_pos.ne') h.symm
  change cartanMatrix b = (Int.castRingHom ℝ).mapMatrix (integralCartan P B) at hCartan
  intro hz
  apply hdet
  rw [hCartan, ← RingHom.map_det, hz, map_zero]

private theorem simple_evaluation_ker (B : P.Base) :
    (LinearMap.pi (fun i : B.support => extendFunctional ℚ (P.root' i))).ker =
      rationalRootAnnihilator P := by
  classical
  let V := ℚ ⊗[ℤ] Y
  let extension : (Y →ₗ[ℤ] ℤ) →ₗ[ℤ] V →ₗ[ℚ] ℚ :=
    ((TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.compRight ℤ).comp
      (LinearMap.baseChangeHom ℤ ℚ Y ℤ)
  ext y
  simp only [LinearMap.mem_ker, rationalRootAnnihilator, Submodule.mem_iInf]
  constructor
  · intro hy i
    let f : X →ₗ[ℤ] ℚ := ((LinearMap.applyₗ y).restrictScalars ℤ).comp
      (extension.comp P.toLinearMap)
    obtain ⟨c, _, _, hc⟩ := B.exists_root_eq_sum_int i
    change f (P.root i) = 0
    rw [hc, map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    have h : f (P.root j) = 0 := congrFun hy ⟨j, hj⟩
    rw [map_zsmul, h, smul_zero]
  · intro hy
    ext i
    exact hy i

/-- The rational Cartan matrix is invertible and the simple coroot span
complements the common annihilator of the roots. -/
theorem rationalComplement : EuclideanComparisonSpecs.rationalComplementType := by
  intro ι X Y _ _ _ _ _ _ _ P _ B _
  let V := ℚ ⊗[ℤ] Y
  let v (i : B.support) : V := (1 : ℚ) ⊗ₜ[ℤ] P.coroot i
  let S := rationalSimpleCorootSpan P B
  let e : V →ₗ[ℚ] (B.support → ℚ) := LinearMap.pi fun i => extendFunctional ℚ (P.root' i)
  let C := (Int.castRingHom ℚ).mapMatrix (integralCartan P B)
  have hu : IsUnit C.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [show C.det = ((integralCartan P B).det : ℚ) from
      ((Int.castRingHom ℚ).map_det _).symm, Int.cast_ne_zero]
    exact det_integralCartan_ne_zero P B
  refine ⟨hu, ?_⟩
  have hLI : LinearIndependent ℚ v :=
    Module.Flat.linearIndependent_one_tmul B.linearIndepOn_coroot
  let b : Basis B.support ℚ S := Basis.span hLI
  have hb (i : B.support) : S.subtype (b i) = v i := Basis.coe_span_apply hLI i
  let A := C.transpose
  have hA : IsUnit A.det := by simpa [A, Matrix.det_transpose] using hu
  let F := A.toLinearEquiv' (A.invertibleOfIsUnitDet hA)
  have hEval (c : B.support → ℚ) :
      e (S.subtype (b.equivFun.symm c)) = F c := by
    change _ = Matrix.toLin' A c
    funext i
    rw [b.equivFun_symm_apply, map_sum, map_sum, Finset.sum_apply, Matrix.toLin'_apply]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb]
    change c j * extendFunctional ℚ (P.root' i) (v j) = (P.pairing i j : ℚ) * c j
    rw [extendFunctional_one_tmul]
    exact mul_comm _ _
  let proj : V →ₗ[ℚ] S := b.equivFun.symm.toLinearMap.comp (F.symm.toLinearMap.comp e)
  have hProj (y : S) : proj y = y := by
    have h := hEval (b.equivFun y)
    rw [LinearEquiv.symm_apply_apply] at h
    change b.equivFun.symm (F.symm (e (S.subtype y))) = y
    rw [h, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hker : proj.ker = rationalRootAnnihilator P := by
    rw [← simple_evaluation_ker P B]
    ext y
    simp only [LinearMap.mem_ker]
    change b.equivFun.symm (F.symm (e y)) = 0 ↔ e y = 0
    constructor
    · intro h
      have h' := b.equivFun.symm.injective (h.trans (map_zero b.equivFun.symm).symm)
      exact F.symm.injective (h'.trans (map_zero F.symm).symm)
    · intro h
      rw [h, map_zero, map_zero]
  rw [← hker]
  exact LinearMap.isCompl_of_proj hProj

end LinearAlgebraicGroups.RootData
