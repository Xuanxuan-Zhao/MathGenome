import Specs.LinearAlgebraicGroups.Arithmetic.DivisionNormOneArchimedeanReduction
import LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import LinearAlgebraicGroups.Arithmetic.InnerTypeASplitRank
import LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Topology
open LinearAlgebraicGroups.Specs
open scoped TensorProduct Classical RestrictedProduct commutatorElement

universe u v

namespace LinearAlgebraicGroups.Arithmetic.DivisionNormOneArchimedeanReduction

open Specs.Arithmetic.DivisionNormOneArchimedeanReduction (ArchimedeanReduction)
open Specs.Arithmetic.ProjectiveRecurrence
  (cocharacterRadicalPoints evaluateArchimedean localPointSet)
open Specs.IntegralModels (MatrixRealization)
open Specs.OuterTypeAModels (RepresentsNormOne)
open _root_.Specs.RM03.CSA (isCentralSimple)
open AdelicGroups ArithmeticLatticeProjection CompactProductIsolation
open Specs.Unipotent (baseChangedAlgebraicGroup)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open RM03.CSA (isCentralSimple_baseChange reducedNorm genericReducedNorm
  genericReducedNorm_eval reducedNorm_basis_baseChange)
open RM03.CSA.NormOneGroup (normAt normOneFunctor changeCoefficients
  isUnit_of_normAt_eq_one)
open LocalNormOneCommutators.Spec (elementary elementaryGroup)
open InnerTypeALocalGeneration.Spec (matrixCentralSimple)
open private norm_algEquiv from LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators
open private baseChangePointIso affineGroupIso affineGroupIso_hom
  from LinearAlgebraicGroups.Descent.InnerTypeA

section NormOneModels

variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  {hA : isCentralSimple K A} {b : Module.Basis I K A} {G : AffineAlgebraicGroup K}

private def normOnePointIsoOf
    (p : ∀ R : TestAlgebra K, Points G.val.X R ≃ RM03.CSA.NormOneGroup.normOne (R := R) hA b)
    (hmul : ∀ R (x y : ((groupPointsFunctor K).obj G.val).obj R),
      (p R (x * y)).val = (p R x).val * (p R y).val)
    (hnat : ∀ {R S : TestAlgebra K} (f : R ⟶ S) (x : Points G.val.X R),
      (p S (mapPoints f x)).val = changeCoefficients f.hom (p R x).val) :
    (groupPointsFunctor K).obj G.val ≅ normOneFunctor hA b := by
  refine NatIso.ofComponents (fun R => ?_) ?_
  · letI := RM03.CSA.NormOneGroup.normOneGroup (R := R) hA b
    exact (show ((groupPointsFunctor K).obj G.val).obj R ≃*
        RM03.CSA.NormOneGroup.normOne (R := R) hA b from
      { toEquiv := p R
        map_mul' := fun x y => Subtype.ext (hmul R x y) }).toGrpIso
  · intro R S f
    ext x : 2
    exact Subtype.ext (hnat f x)

private def normOnePointIso (h : RepresentsNormOne hA b G) :
    (groupPointsFunctor K).obj G.val ≅ normOneFunctor hA b :=
  normOnePointIsoOf (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2

variable {F M : Type u} [Field F] [Algebra K F] [Ring M] [Algebra F M]

private def extendAlgebraEquiv (e : F ⊗[K] A ≃ₐ[F] M) (R : TestAlgebra F) :
    (restrictTestAlgebra K F).obj R ⊗[K] A ≃ₐ[R] R ⊗[F] M :=
  letI : Algebra K R := inferInstanceAs (Algebra K ((restrictTestAlgebra K F).obj R))
  letI : IsScalarTower K F R := IsScalarTower.of_algebraMap_eq' rfl
  (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid F R R).symm
    (AlgEquiv.refl : A ≃ₐ[K] A)).trans
    ((Algebra.TensorProduct.assoc K F R R F A).trans
      (Algebra.TensorProduct.congr (.refl : R ≃ₐ[R] R) e))

private theorem extendAlgebraEquiv_tmul (e : F ⊗[K] A ≃ₐ[F] M) (R : TestAlgebra F)
    (r : R) (a : A) :
    extendAlgebraEquiv e R (r ⊗ₜ[K] a) = r ⊗ₜ[F] e (1 ⊗ₜ[K] a) := by
  rfl

private theorem extendAlgebraEquiv_natural (e : F ⊗[K] A ≃ₐ[F] M)
    {R S : TestAlgebra F} (f : R ⟶ S) (x : (restrictTestAlgebra K F).obj R ⊗[K] A) :
    extendAlgebraEquiv e S (changeCoefficients ((restrictTestAlgebra K F).map f).hom x) =
      changeCoefficients f.hom (extendAlgebraEquiv e R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    change extendAlgebraEquiv e S (f.hom r ⊗ₜ[K] a) =
      changeCoefficients f.hom (extendAlgebraEquiv e R (r ⊗ₜ[K] a))
    rw [extendAlgebraEquiv_tmul, extendAlgebraEquiv_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem normAt_extendAlgebraEquiv [Infinite F] (hA : isCentralSimple K A)
    (b : Module.Basis I K A) (hM : isCentralSimple F M) (e : F ⊗[K] A ≃ₐ[F] M)
    (R : TestAlgebra F) (x : (restrictTestAlgebra K F).obj R ⊗[K] A) :
    normAt hM ((b.baseChange F).map e.toLinearEquiv) (extendAlgebraEquiv e R x) =
      normAt hA b x := by
  let ch := (b.baseChange F).map e.toLinearEquiv
  have hpol : genericReducedNorm hM ch = MvPolynomial.map (algebraMap K F)
      (genericReducedNorm hA b) := by
    rw [← reducedNorm_basis_baseChange hA b]
    apply MvPolynomial.funext
    intro z
    rw [genericReducedNorm_eval hM, genericReducedNorm_eval (isCentralSimple_baseChange hA),
      norm_algEquiv (isCentralSimple_baseChange hA) hM e]
    congr 1
    simp [ch]
  have hcoord : ∀ l, (ch.baseChange R).repr (extendAlgebraEquiv e R x) l =
      (b.baseChange ((restrictTestAlgebra K F).obj R)).repr x l := by
    intro l
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
    | tmul r a =>
      rw [extendAlgebraEquiv_tmul]
      rw [Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
        Module.Basis.map_repr]
      change ((b.baseChange F).repr (e.symm (e (1 ⊗ₜ[K] a))) l) • r =
        (b.repr a l) • r
      rw [AlgEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul]
      simp only [Algebra.smul_def, mul_one]
      rfl
  letI : Algebra K R := inferInstanceAs (Algebra K ((restrictTestAlgebra K F).obj R))
  change MvPolynomial.eval₂ (algebraMap F R)
    (fun l => (ch.baseChange R).repr (extendAlgebraEquiv e R x) l)
    (genericReducedNorm hM ch) = _
  simp only [hpol, hcoord, MvPolynomial.eval₂_map]
  rfl

private def extendNormOneFunctor [Infinite F] (hA : isCentralSimple K A)
    (b : Module.Basis I K A) (hM : isCentralSimple F M) (e : F ⊗[K] A ≃ₐ[F] M) :
    restrictTestAlgebra K F ⋙ normOneFunctor hA b ≅
      normOneFunctor hM ((b.baseChange F).map e.toLinearEquiv) := by
  refine NatIso.ofComponents (fun R => ?_) ?_
  · let c := (b.baseChange F).map e.toLinearEquiv
    let f := extendAlgebraEquiv e R
    letI := RM03.CSA.NormOneGroup.normOneGroup (R := (restrictTestAlgebra K F).obj R) hA b
    letI := RM03.CSA.NormOneGroup.normOneGroup (R := R) hM c
    let φ : RM03.CSA.NormOneGroup.normOne
        (R := (restrictTestAlgebra K F).obj R) hA b ≃*
        RM03.CSA.NormOneGroup.normOne (R := R) hM c :=
      { toEquiv := f.toEquiv.subtypeEquiv fun x => by
          change normAt hA b x = 1 ↔ normAt hM c (f x) = 1
          rw [normAt_extendAlgebraEquiv hA b hM e]
        map_mul' := fun x y => Subtype.ext (map_mul f x.val y.val) }
    exact φ.toGrpIso
  · intro R S f
    ext x : 2
    exact Subtype.ext (extendAlgebraEquiv_natural e f x.val)

end NormOneModels

open CocharacterDynamics (HasLimit)
open Specs.InnerTypeARelativeContraction (NormOnePoints blockEntry)
open Specs.CharacterDescent (Cocharacter)
open LocalNormOneCommutators (elementary_single_diagonal reducedNorm_diagonalSlot
  diagonalSlot diagonalSlot_commutator_mem elementaryGroup_le_commutator commutator_norm_one)

private theorem normOneElementary {F B : Type u} [Field F] [Infinite F] [DivisionRing B]
    [Algebra F B] (hB : isCentralSimple F B)
    (hcomm : ∀ x : Bˣ, reducedNorm hB (x : B) = 1 → ∃ a b : Bˣ, ⁅a, b⁆ = x)
    {m : ℕ} (hm : 2 ≤ m) (hM : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    (x : (Matrix (Fin m) (Fin m) B)ˣ) (hx : reducedNorm hM (x : Matrix _ _ B) = 1) :
    x ∈ elementaryGroup (Fin m) := by
  let i : Fin m := ⟨0, Nat.zero_lt_two.trans_le hm⟩
  let j : Fin m := ⟨1, hm⟩
  have hji : j ≠ i := by intro h; simpa [i, j] using congrArg Fin.val h
  let E := elementaryGroup (B := B) (Fin m)
  obtain ⟨L, hL, R, hR, a, he⟩ := elementary_single_diagonal i x
  have hL₁ := commutator_norm_one hM (elementaryGroup_le_commutator (F := F) hL)
  have hR₁ := commutator_norm_one hM (elementaryGroup_le_commutator (F := F) hR)
  change reducedNorm hM (L : Matrix _ _ B) = 1 at hL₁
  change reducedNorm hM (R : Matrix _ _ B) = 1 at hR₁
  have hn : reducedNorm hB (a : B) = 1 := by
    rw [← reducedNorm_diagonalSlot hB (Nat.zero_lt_two.trans_le hm) hM i a, ← he,
      Units.val_mul, Units.val_mul, RM03.CSA.reducedNorm_mul, RM03.CSA.reducedNorm_mul,
      hL₁, hx, hR₁, mul_one, mul_one]
  obtain ⟨a₁, a₂, rfl⟩ := hcomm a hn
  have ha : diagonalSlot i ⁅a₁, a₂⁆ ∈ E := diagonalSlot_commutator_mem j i hji a₁ a₂
  have he' : x = L⁻¹ * diagonalSlot i ⁅a₁, a₂⁆ * R⁻¹ := by rw [← he]; group
  rw [he']
  exact E.mul_mem (E.mul_mem (E.inv_mem hL) ha) (E.inv_mem hR)

private theorem normAt_self {F M I : Type u} [Field F] [Ring M] [Algebra F M] [Fintype I]
    (hM : isCentralSimple F M) (b : Module.Basis I F M) (x : F ⊗[F] M) :
    normAt hM b x = reducedNorm hM (Algebra.TensorProduct.lid F M x) := by
  change MvPolynomial.eval₂ (RingHom.id F) (fun i => (b.baseChange F).repr x i)
    (genericReducedNorm hM b) = _
  rw [MvPolynomial.eval₂_id, genericReducedNorm_eval]
  congr 1
  have h := congrArg (Algebra.TensorProduct.lid F M) ((b.baseChange F).sum_repr x)
  simpa only [map_sum, map_smul, Module.Basis.baseChange_apply, Algebra.TensorProduct.lid_tmul,
    one_smul] using h

private def normOneUnit {F M I : Type u} [Field F] [Ring M] [Algebra F M] [Fintype I]
    (hM : isCentralSimple F M) (b : Module.Basis I F M)
    (x : RM03.CSA.NormOneGroup.normOne (R := F) hM b) : Mˣ :=
  Units.map (Algebra.TensorProduct.lid F M).toMonoidHom
    (isUnit_of_normAt_eq_one hM b x.val x.property).unit

private theorem normOneUnit_val {F M I : Type u} [Field F] [Ring M] [Algebra F M] [Fintype I]
    (hM : isCentralSimple F M) (b : Module.Basis I F M)
    (x : RM03.CSA.NormOneGroup.normOne (R := F) hM b) :
    (normOneUnit hM b x : M) = Algebra.TensorProduct.lid F M x.val := by
  change (Algebra.TensorProduct.lid F M) _ = _
  rw [IsUnit.unit_spec]

private theorem rationalRadicalsGenerate {F B I : Type u} [Field F] [Infinite F] [DivisionRing B]
    [Algebra F B] [Fintype I] {m : ℕ} (hm : 2 ≤ m) (hB : isCentralSimple F B)
    (hcomm : ∀ x : Bˣ, reducedNorm hB (x : B) = 1 → ∃ a b : Bˣ, ⁅a, b⁆ = x)
    {hM : isCentralSimple F (Matrix (Fin m) (Fin m) B)}
    {b : Module.Basis I F (Matrix (Fin m) (Fin m) B)} {H : AffineAlgebraicGroup F}
    {P : NormOnePoints hM b H} {S : ClosedSubgroup H.val}
    {D : Specs.InnerTypeARelativeContraction.ScalarDiagonalModel P S}
    (hD : Specs.InnerTypeASplitRank.RelativeBlockDescription D) :
    Subgroup.closure (cocharacterRadicalPoints H) = ⊤ := by
  obtain ⟨α, _, _, _, hcochar, _, hlimit⟩ := hD
  let R := CommAlgCat.of F F
  let M := Matrix (Fin m) (Fin m) B
  let V := IntegralModels.RationalPoints H
  let C := Subgroup.closure (cocharacterRadicalPoints H)
  let E := Algebra.TensorProduct.lid F M
  let φ : V →* Mˣ :=
    { toFun := fun x => normOneUnit hM b (P.point R x)
      map_one' := by
        apply Units.ext
        rw [normOneUnit_val, P.one, map_one]
        rfl
      map_mul' := fun x y => by
        apply Units.ext
        simp only [Units.val_mul, normOneUnit_val, P.mul, map_mul] }
  have hφ (x : V) : (φ x : M) = E (P.point R x).val := normOneUnit_val _ _ _
  have hφi : Function.Injective φ := by
    intro x y h
    exact (P.point R).injective (Subtype.ext (E.injective (by
      rw [← hφ x, ← hφ y, h])))
  have hφnorm (x : V) : reducedNorm hM (φ x : M) = 1 := by
    rw [hφ, ← normAt_self hM b]
    exact (P.point R x).property
  have hgenerators : elementaryGroup (B := B) (Fin m) ≤ C.map φ := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, j, hij, a, rfl⟩
    let u := elementary i j hij a
    have hn : reducedNorm hM (u : M) = 1 :=
      commutator_norm_one hM (elementaryGroup_le_commutator (F := F)
        (LocalNormOneCommutators.elementary_mem_elementaryGroup i j hij a))
    let y : RM03.CSA.NormOneGroup.normOne (R := F) hM b :=
      ⟨1 ⊗ₜ[F] (u : M), by rw [normAt_self]; simpa⟩
    let x : V := (P.point R).symm y
    have hx : P.point R x = y := (P.point R).apply_symm_apply y
    have hv : (P.point R x).val = 1 + blockEntry i j (1 ⊗ₜ[F] a) := by
      rw [hx]
      change (1 : F) ⊗ₜ[F] (1 + Matrix.single i j a) = _
      rw [TensorProduct.tmul_add, ← Algebra.TensorProduct.one_def]
      rfl
    obtain ⟨c, hc⟩ := hcochar i j hij
    have hpos : 0 < Specs.CharacterPairing.pairing S.group (α i j) c := by rw [hc]; decide
    have hl := ((hlimit i j hij c hpos R x).1.mpr ⟨_, hv, ?_⟩).2
    · obtain ⟨L⟩ := CocharacterDynamics.existsLimitDecomposition H (c ≫ S.inclusion)
      obtain ⟨z, hz⟩ := (L.contracting_points R x).mp hl
      refine ⟨x, Subgroup.subset_closure ⟨c ≫ S.inclusion, L, ⟨z, hz⟩⟩, Units.ext ?_⟩
      rw [hφ, hx]
      exact one_smul F _
    · intro z hz
      have hblock : blockEntry i j z = blockEntry i j (1 ⊗ₜ[F] a) :=
        add_left_cancel (hz.symm.trans hv)
      have hmap (y : R ⊗[F] B) : Specs.InnerTypeARelativeContraction.blockProjection i j
          (blockEntry i j y) = y := by
        induction y using TensorProduct.inductionOn with
        | tmul r a => simp [Specs.InnerTypeARelativeContraction.blockProjection, blockEntry]
        | add x y hx hy => simp [hx, hy]
      exact (hmap z).symm.trans ((congrArg _ hblock).trans (hmap _))
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨y, hy, he⟩ := hgenerators (normOneElementary hB hcomm hm hM (φ x) (hφnorm x))
  exact (hφi he) ▸ hy

open private onGroupPoints onGroupPoints_mapPoints onGroupPoints_orbit
  from LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction

private theorem mapRadicalPoint {F : Type u} [Field F] {H G : AffineAlgebraicGroup F}
    (f : H.val ⟶ G.val) {x : IntegralModels.RationalPoints H}
    (hx : x ∈ cocharacterRadicalPoints H) :
    onGroupPoints f (CommAlgCat.of F F) x ∈ cocharacterRadicalPoints G := by
  let R := CommAlgCat.of F F
  obtain ⟨c, L, z, hz⟩ := hx
  have hl : HasLimit c x 1 := (L.contracting_points R x).mpr ⟨z, hz⟩
  obtain ⟨p, hp, hp₀⟩ := hl
  have hl' : HasLimit (c ≫ f) (onGroupPoints f R x) 1 := by
    refine ⟨onGroupPoints f _ p, ?_, ?_⟩
    · rw [← onGroupPoints_mapPoints, hp, onGroupPoints_orbit]
    · rw [← onGroupPoints_mapPoints, hp₀, map_one]
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition G (c ≫ f)
  exact ⟨c ≫ f, E, (E.contracting_points R _).mp hl'⟩

open private centralSimple_transport reducedNorm_transport transportedAlgebraEquiv
  transportedAlgebraEquiv_one_tmul from LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA
open private norm_field norm_quaternion from LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators
open private existsPresentation pointCoord pointCoord_isInducing normAt_eq_reducedNorm
  from LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA

private theorem realDivisionCoordinatesCompact {B I : Type u} [DivisionRing B] [Algebra ℝ B]
    [Fintype I] (hB : isCentralSimple ℝ B) (b : Module.Basis I ℝ B) :
    IsCompact ((fun x : B => fun l => b.repr x l) '' {x | reducedNorm hB x = 1}) := by
  letI := hB.2.2
  obtain ⟨n, hn, _⟩ := D07.Ch23.Frobenius.finiteDimensionalClassification B
  rcases hn with ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
  · let hR : isCentralSimple ℝ ℝ := ⟨inferInstance, inferInstance, inferInstance⟩
    have he (x : B) : reducedNorm hB x = e.symm x :=
      (norm_algEquiv hB hR e.symm x).trans (norm_field hR _)
    have hset : {x | reducedNorm hB x = 1} = ({1} : Set B) := by
      ext x
      change reducedNorm hB x = 1 ↔ x = 1
      rw [he, ← map_one e.symm, e.symm.injective.eq_iff]
    rw [hset, Set.image_singleton]
    exact isCompact_singleton
  · have hcenter : e Complex.I ∈ Subalgebra.center ℝ B := by
      apply Subalgebra.mem_center_iff.mpr
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, mul_comm]
    letI := hB.2.1
    obtain ⟨r, hr⟩ := (Algebra.IsCentral.mem_center_iff ℝ).mp hcenter
    have hc : Complex.I = algebraMap ℝ ℂ r := e.injective (hr.trans (e.commutes r).symm)
    simpa using congrArg Complex.im hc
  · let H := Quaternion ℝ
    let hH := RM03.CSA.isCentralSimple_of_isCentralDivision ℝ H RM03.Brauer.quaternion_isCentralDivision
    letI : FiniteDimensional ℝ H := hH.2.2
    have hset : e '' (Metric.sphere (0 : H) 1) = {x : B | reducedNorm hB x = 1} := by
      ext x
      obtain ⟨q, rfl⟩ := e.surjective x
      rw [e.injective.mem_set_image]
      change q ∈ Metric.sphere (0 : H) 1 ↔ reducedNorm hB (e q) = 1
      rw [← norm_algEquiv hH hB e, norm_quaternion, Quaternion.normSq_eq_norm_mul_self,
        Metric.mem_sphere, dist_zero_right]
      constructor
      · rintro h
        rw [h, one_mul]
      · intro h
        nlinarith [norm_nonneg q]
    rw [← hset, Set.image_image]
    apply (isCompact_sphere (0 : H) 1).image
    exact continuous_pi fun l => ((b.coord l).comp e.toLinearMap).continuous_of_finiteDimensional

private theorem complexDivisionCoordinatesCompact {B I : Type u} [DivisionRing B] [Algebra ℂ B]
    [Fintype I] (hB : isCentralSimple ℂ B) (b : Module.Basis I ℂ B) :
    IsCompact ((fun x : B => fun l => b.repr x l) '' {x | reducedNorm hB x = 1}) := by
  have hset : {x | reducedNorm hB x = 1} = ({1} : Set B) := by
    ext x
    change reducedNorm hB x = 1 ↔ x = 1
    constructor
    · intro hx
      have hu : IsUnit x := (RM03.CSA.reducedNorm_ne_zero_iff_isUnit hB x).mp
        (hx.symm ▸ one_ne_zero)
      obtain ⟨u, rfl⟩ := hu
      exact congrArg Units.val (LocalNormOneCommutators.complexDivision hB u hx)
    · rintro rfl
      exact RM03.CSA.reducedNorm_one hB
  rw [hset, Set.image_singleton]
  exact isCompact_singleton

private theorem divisionCoordinatesCompactOfEquiv {F B I : Type u} {L : Type*} [Field F] [Field L]
    [TopologicalSpace F] [TopologicalSpace L] [DivisionRing B] [Algebra F B] [Fintype I]
    (e : F ≃+* L) (he : Continuous e.symm) (hB : isCentralSimple F B)
    (b : Module.Basis I F B)
    (hc : letI : Algebra L B := Algebra.compHom B e.symm.toRingHom
      ∀ c : Module.Basis I L B, IsCompact ((fun x : B => fun l => c.repr x l) ''
        {x | reducedNorm (centralSimple_transport e hB) x = 1})) :
    IsCompact ((fun x : B => fun l => b.repr x l) '' {x | reducedNorm hB x = 1}) := by
  letI : Algebra F L := e.toRingHom.toAlgebra
  letI : Algebra L B := Algebra.compHom B e.symm.toRingHom
  let f : L ⊗[F] B ≃ₐ[L] B := transportedAlgebraEquiv e
  let c := (b.baseChange L).map f.toLinearEquiv
  let r (z : I → L) (l : I) := e.symm (z l)
  have hr : Continuous r := continuous_pi fun l => he.comp (continuous_apply l)
  have hnorm : {x : B | reducedNorm (centralSimple_transport e hB) x = 1} =
      {x | reducedNorm hB x = 1} := by
    ext x
    change reducedNorm (centralSimple_transport e hB) x = 1 ↔ reducedNorm hB x = 1
    rw [reducedNorm_transport, ← map_one e, e.injective.eq_iff]
  have hcoord (x : B) : r (fun l => c.repr x l) = fun l => b.repr x l := by
    have hx : f.symm x = 1 ⊗ₜ[F] x := by
      apply f.injective
      exact (f.apply_symm_apply x).trans (transportedAlgebraEquiv_one_tmul e x).symm
    funext l
    have hc' : c.repr x l = e (b.repr x l) := by
      rw [Module.Basis.map_repr]
      change (b.baseChange L).repr (f.symm x) l = _
      rw [hx, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
      rfl
    exact (congrArg e.symm hc').trans (e.symm_apply_apply _)
  have hcompact := (hc c).image hr
  rw [Set.image_image, hnorm] at hcompact
  exact (funext hcoord) ▸ hcompact

private theorem divisionCommutatorsOfEquiv {F B : Type u} {L : Type*} [Field F] [Field L]
    [DivisionRing B] [Algebra F B] (e : F ≃+* L) (hB : isCentralSimple F B)
    (hc : letI : Algebra L B := Algebra.compHom B e.symm.toRingHom
      ∀ x : Bˣ, reducedNorm (centralSimple_transport e hB) (x : B) = 1 →
        ∃ a b : Bˣ, ⁅a, b⁆ = x) :
    ∀ x : Bˣ, reducedNorm hB (x : B) = 1 → ∃ a b : Bˣ, ⁅a, b⁆ = x := by
  letI : Algebra L B := Algebra.compHom B e.symm.toRingHom
  intro x hx
  apply hc
  rw [reducedNorm_transport e hB, hx, map_one]

private theorem normOneCoordinatesInducing {K A I F : Type u} [Field K] [Field F]
    [Ring A] [Algebra K A] [Fintype I] [Algebra K F] [TopologicalSpace F]
    [IsTopologicalDivisionRing F]
    {hA : isCentralSimple K A} {b : Module.Basis I K A} {G : AffineAlgebraicGroup K}
    (h : RepresentsNormOne hA b G) (i : MatrixRealization G) :
    IsInducing (fun x : PointsIn i F =>
      fun l => (b.baseChange F).repr ((normOnePointIso h).hom.app (CommAlgCat.of K F) x).val l) := by
  obtain ⟨P⟩ := existsPresentation hA b
  let pG := normOnePointIso h
  let pH := normOnePointIsoOf P.point P.point_mul P.point_natural
  let α := pH ≪≫ pG.symm
  let e := affineGroupIso P.group.property.1 G.property.1 α
  let j : MatrixRealization P.group :=
    { size := i.size
      ambient := i.ambient
      matrix := i.matrix
      embedding := e.hom ≫ i.embedding
      closed := by
        change IsClosedImmersion (e.hom.hom.hom.left ≫ i.embedding.hom.hom.left)
        let : IsIso e.hom.hom.hom.left :=
          (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso e.hom
        let := i.closed
        infer_instance }
  let R := CommAlgCat.of K F
  let ψ : PointsIn j F ≃* PointsIn i F :=
    (((groupPointsFunctor K).mapIso e).app R).groupIsoToMulEquiv
  have hmat : asMatrix i F ∘ ψ = asMatrix j F := by
    funext x
    change (i.matrix.hom.app R) (((groupPointsFunctor K).map i.embedding).app R (ψ x)) =
      (i.matrix.hom.app R) (((groupPointsFunctor K).map (e.hom ≫ i.embedding)).app R x)
    rw [Functor.map_comp]
    rfl
  have hψ : IsInducing ψ := by
    refine ⟨?_⟩
    change TopologicalSpace.induced (asMatrix j F) inferInstance =
      TopologicalSpace.induced ψ (TopologicalSpace.induced (asMatrix i F) inferInstance)
    rw [induced_compose, hmat]
  let Ψ : PointsIn j F ≃ₜ PointsIn i F := ψ.toEquiv.toHomeomorphOfIsInducing hψ
  have hfun : (groupPointsFunctor K).map e.hom ≫ pG.hom = pH.hom := by
    rw [affineGroupIso_hom]
    simp [α]
  have hc (x : PointsIn j F) : pG.hom.app R (ψ x) = P.point R x :=
    congrArg (fun η : (groupPointsFunctor K).obj P.group.val ⟶ normOneFunctor hA b => η.app R x) hfun
  let f := fun x : PointsIn i F => fun l => (b.baseChange F).repr (pG.hom.app R x).val l
  have heq : f = pointCoord P j ∘ Ψ.symm := by
    funext x l
    change (b.baseChange F).repr (pG.hom.app R x).val l =
      (b.baseChange F).repr (P.point R (ψ.symm x)).val l
    rw [← hc, ψ.apply_symm_apply]
  change IsInducing f
  rw [heq]
  exact (pointCoord_isInducing (F := F) P j).comp Ψ.symm.isInducing

private theorem compactNormOneOfDivision {K A I F B : Type u} [Field K] [Field F]
    [Ring A] [Algebra K A] [Fintype I] [Algebra K F] [TopologicalSpace F]
    [IsTopologicalDivisionRing F] [DivisionRing B] [Algebra F B]
    {hA : isCentralSimple K A} {b : Module.Basis I K A} {G : AffineAlgebraicGroup K}
    (h : RepresentsNormOne hA b G) (i : MatrixRealization G)
    (e : F ⊗[K] A ≃ₐ[F] B) (hB : isCentralSimple F B)
    (hc : ∀ d : Module.Basis I F B,
      IsCompact ((fun x : B => fun l => d.repr x l) '' {x | reducedNorm hB x = 1})) :
    CompactSpace (PointsIn i F) := by
  let R := CommAlgCat.of K F
  let p := ((normOnePointIso h).app R).groupIsoToMulEquiv
  let f := fun x : PointsIn i F => fun l => (b.baseChange F).repr (p x).val l
  let d := (b.baseChange F).map e.toLinearEquiv
  have he (x : F ⊗[K] A) (l : I) : d.repr (e x) l = (b.baseChange F).repr x l := by
    rw [Module.Basis.map_repr]
    change (b.baseChange F).repr (e.symm (e x)) l = _
    rw [e.symm_apply_apply]
  have hn (x : F ⊗[K] A) : normAt hA b x = reducedNorm hB (e x) :=
    (normAt_eq_reducedNorm hA b x).trans (norm_algEquiv (isCentralSimple_baseChange hA) hB e x)
  refine ⟨(normOneCoordinatesInducing h i).isCompact_iff.mpr ?_⟩
  change IsCompact (f '' Set.univ)
  convert hc d using 1
  ext z
  constructor
  · rintro ⟨x, _, rfl⟩
    exact ⟨e (p x).val, (hn _).symm.trans (p x).property, funext (he _)⟩
  · rintro ⟨x, hx, rfl⟩
    let y : RM03.CSA.NormOneGroup.normOne (R := F) hA b :=
      ⟨e.symm x, by rwa [hn, e.apply_symm_apply]⟩
    refine ⟨p.symm y, Set.mem_univ _, ?_⟩
    funext l
    change (b.baseChange F).repr (p (p.symm y)).val l = d.repr x l
    rw [p.apply_symm_apply, ← he, show e y.val = x from e.apply_symm_apply x]

/-- Evaluation of a one-by-one matrix with the same finite-index instances
as the division algebra presentation. -/
private def oneByOneMatrix {F B : Type u} [Field F] [Ring B] [Algebra F B] :
    Matrix (Fin 1) (Fin 1) B ≃ₐ[F] B where
  toFun x := x 0 0
  invFun x := Matrix.of fun _ _ => x
  left_inv x := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    rfl
  right_inv _ := rfl
  map_mul' _ _ := by simp [Matrix.mul_apply]
  map_add' _ _ := rfl
  commutes' r := by simp [Matrix.algebraMap_matrix_apply]

private theorem archimedeanRadicalsGenerate {K A I : Type u} [Field K] [NumberField K]
    [DivisionRing A] [Algebra K A] [Fintype I]
    {hA : isCentralSimple K A} {b : Module.Basis I K A} {G : AffineAlgebraicGroup K}
    (h : RepresentsNormOne hA b G) (i : MatrixRealization G)
    (D : GlobalFieldData.{u,u} K) (hD : D = .number inferInstance) (w : D.InfinitePlace) :
    ¬ CompactSpace (LocalPoints D i (.inr w)) →
    Subgroup.closure (localPointSet D i (.inr w)
      (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G))) = ⊤ := by
  subst D
  let D : GlobalFieldData.{u,u} K := .number inferInstance
  let F := w.Completion
  letI : NormedField F := inferInstanceAs (NormedField w.Completion)
  letI : Algebra K F := completionAlgebra D (.inr w)
  letI : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  let C := F ⊗[K] A
  let hC : isCentralSimple F C := isCentralSimple_baseChange hA
  obtain ⟨m, B, _, _, hdivision, hm, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation F C hC
  let hB := RM03.CSA.isCentralSimple_of_isCentralDivision F B hdivision
  have harch :
      (∀ x : Bˣ, reducedNorm hB (x : B) = 1 → ∃ a b : Bˣ, ⁅a, b⁆ = x) ∧
      (∀ d : Module.Basis I F B,
        IsCompact ((fun x : B => fun l => d.repr x l) '' {x | reducedNorm hB x = 1})) := by
    rcases w.isReal_or_isComplex with hw | hw
    · obtain ⟨ε, hε⟩ := numberRealCompletion w hw
      let E : w.Completion ≃ᵢ ℝ := ⟨ε.toEquiv, hε⟩
      letI : Algebra ℝ B := Algebra.compHom B ε.symm.toRingHom
      exact ⟨divisionCommutatorsOfEquiv ε hB (LocalNormOneCommutators.realDivision _),
        fun d => divisionCoordinatesCompactOfEquiv ε E.symm.continuous hB d
          (realDivisionCoordinatesCompact _)⟩
    · obtain ⟨ε, hε⟩ := numberComplexCompletion w hw
      let E : w.Completion ≃ᵢ ℂ := ⟨ε.toEquiv, hε⟩
      letI : Algebra ℂ B := Algebra.compHom B ε.symm.toRingHom
      refine ⟨divisionCommutatorsOfEquiv ε hB ?_,
        fun d => divisionCoordinatesCompactOfEquiv ε E.symm.continuous hB d
          (complexDivisionCoordinatesCompact _)⟩
      intro x hx
      have he := LocalNormOneCommutators.complexDivision (centralSimple_transport ε hB) x hx
      exact ⟨1, 1, by simp [he]⟩
  intro hnc
  have hm₂ : 2 ≤ m := by
    by_contra hlt
    have h₁ : m = 1 := by omega
    subst m
    exact hnc (compactNormOneOfDivision (F := F) h i (e.trans oneByOneMatrix)
      hB harch.2)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let M := Matrix (Fin (n + 1)) (Fin (n + 1)) B
  let hM : isCentralSimple F M := matrixCentralSimple hB hm
  let d := (b.baseChange F).map e.toLinearEquiv
  obtain ⟨o, P, S, _, _, _, ⟨Q, hQ⟩, _⟩ := InnerTypeASplitRank.splitRank n hdivision hM d
  let H := @Specs.StandardGroups.spectrum F _
    (Descent.InnerTypeA.Specification.NormOneCoordinates hM d) _ o.hopf inferInstance
  let G₀ := baseChangedAlgebraicGroup F G
  have hg : Subgroup.closure (cocharacterRadicalPoints H) = ⊤ :=
    rationalRadicalsGenerate hm₂ hB harch.1 hQ
  let e₀ := baseChangePointIso (K := F) G.val ≪≫
    ((Functor.whiskeringLeft _ _ _).obj (restrictTestAlgebra K F)).mapIso (normOnePointIso h) ≪≫
    extendNormOneFunctor hA b hM e
  let e₁ := normOnePointIsoOf P.point P.mul P.natural
  let eH : H.val ≅ G₀.val :=
    affineGroupIso H.property.1 G₀.property.1 (e₁ ≪≫ e₀.symm)
  let R := CommAlgCat.of F F
  let E : IntegralModels.RationalPoints H ≃* PointsIn i F :=
    ((((groupPointsFunctor F).mapIso eH).app R).groupIsoToMulEquiv).trans
      (baseChangePointGroupEquiv F G.val R)
  let L := Subgroup.closure (localPointSet D i (.inr w) (cocharacterRadicalPoints G₀))
  have hmap : Subgroup.closure (cocharacterRadicalPoints H) ≤ L.comap E.toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    apply Subgroup.subset_closure
    exact ⟨onGroupPoints eH.hom R x, mapRadicalPoint eH.hom hx, rfl⟩
  change L = ⊤
  apply eq_top_iff.mpr
  intro p _
  obtain ⟨x, rfl⟩ := E.surjective p
  exact hmap (by rw [hg]; trivial)

private theorem radicalContracted {K : Type u} [Field K] [NumberField K]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G)
    (D : GlobalFieldData.{u,u} K) (hD : D = .number inferInstance) (w : D.InfinitePlace) :
    ∀ g ∈ localPointSet D i (.inr w)
      (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w)) G)),
      Contracted g := by
  subst D
  let D : GlobalFieldData.{u,u} K := .number inferInstance
  let F := w.Completion
  letI : Field F := inferInstanceAs (Field w.Completion)
  letI : TopologicalSpace F := inferInstanceAs (TopologicalSpace w.Completion)
  letI : Algebra K F := completionAlgebra D (.inr w)
  let H := baseChangedAlgebraicGroup F G
  intro g hg
  obtain ⟨p, ⟨c, E, hp⟩, hg⟩ := hg
  obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
  let e : PointsIn j F ≃* PointsIn i F :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  have hcont : Continuous e := hj.continuous
  have hgp : e p = g := (Over.OverMorphism.ext hg).symm
  obtain ⟨a, _, ha⟩ := LocalCocharacterEvaluation.archimedeanCompletionScalars w
  letI : Algebra ℝ F := a
  obtain ⟨t, ht⟩ := LocalCocharacterEvaluation.contractingScalarExists (E := ℝ)
  have hcontract := LocalCocharacterEvaluation.contractingEvaluation H j c E ha t ht p hp
  let z : PointsIn j F := CocharacterDynamics.cocharacterPoint (G := H.val) c (CommAlgCat.of F F)
    (Units.map (algebraMap ℝ F).toMonoidHom t)
  refine ⟨e z, ?_⟩
  have htend := (hcont.tendsto (1 : PointsIn j F)).comp hcontract
  simpa only [Function.comp_def, map_mul, map_pow, map_inv, map_one, hgp, z] using htend

private theorem denseProductContracted {J : Type*} [Finite J]
    {P : J → Type*} [∀ j, Group (P j)] [∀ j, TopologicalSpace (P j)]
    (h : ∀ j, Dense (Subgroup.closure {x : P j | Contracted x} : Set (P j))) :
    Dense (Subgroup.closure {x : ∀ j, P j | Contracted x} : Set (∀ j, P j)) := by
  let A (j : J) : Set (P j) := {x | Contracted x}
  have h₁ (j : J) : 1 ∈ A j :=
    ⟨1, by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : P j)) atTop (𝓝 1))⟩
  have hsub : Set.univ.pi A ⊆ {x : ∀ j, P j | Contracted x} := by
    intro x hx
    have hj : ∀ j, Contracted (x j) := fun j => hx j (Set.mem_univ _)
    choose y hy using hj
    exact ⟨y, tendsto_pi_nhds.mpr hy⟩
  have hd : Dense (Subgroup.closure (Set.univ.pi A) : Set (∀ j, P j)) := by
    rw [Subgroup.closure_pi h₁]
    exact dense_pi Set.univ fun j _ => h j
  exact hd.mono (Subgroup.closure_mono hsub)

private theorem noncompactOfSubset {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G)
    {S T : Finset D.Place} (hST : S ⊆ T) (hS : ¬ CompactSpace (FinitePoints D i S)) :
    ¬ CompactSpace (FinitePoints D i T) := by
  classical
  intro hT
  let f := forgetPlaces D i hST
  have hf : Continuous (f : FinitePoints D i T → FinitePoints D i S) := by
    apply continuous_pi
    intro w
    exact continuous_apply (⟨w.1, hST w.2⟩ : (↑T : Set D.Place))
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨fun w => if hw : w.1 ∈ S then x ⟨w.1, hw⟩ else 1, ?_⟩
    funext w
    change (if hw : w.1 ∈ S then x ⟨w.1, hw⟩ else 1) = x w
    have hw : w.1 ∈ S := w.2
    rw [dite_eq_left hw]
  exact hS ⟨hsurj.range_eq ▸ isCompact_range hf⟩

private theorem liftThroughArchimedeanProduct {K : Type u} [Field K] [NumberField K]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (D : GlobalFieldData.{u,u} K) (hD : D = .number inferInstance) :
    ∀ (S : Finset D.Place) (A : Finset D.InfinitePlace),
      let J := A.map (Function.Embedding.inr : D.InfinitePlace ↪ D.Place)
      Disjoint J S →
      CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) →
      ¬ CompactSpace (FinitePoints D i S) →
      (∀ w : D.InfinitePlace, Sum.inr w ∉ S ∪ J → CompactSpace (LocalPoints D i (.inr w))) →
      (∀ w : A, Dense (Subgroup.closure
        (localPointSet D i (.inr w.val)
          (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w.val)) G))) :
        Set (LocalPoints D i (.inr w.val)))) →
      StrongApproximation D i (S ∪ J) → StrongApproximation D i S := by
  classical
  intro S A J hd hcompact hS hc hg happrox
  by_cases hA : A.Nonempty
  · have hmem (w : A) : Sum.inr w.val ∈ J := Finset.mem_map.mpr ⟨w.val, w.property, rfl⟩
    let e : (↑A : Set D.InfinitePlace) ≃ (↑J : Set D.Place) :=
      Equiv.ofBijective (fun w => ⟨Sum.inr w.val, hmem w⟩) ⟨
        fun _ _ h => Subtype.ext (Sum.inr.inj (congrArg Subtype.val h)),
        fun w => by
          obtain ⟨a, ha, he⟩ := Finset.mem_map.mp w.property
          exact ⟨⟨a, ha⟩, Subtype.ext he⟩⟩
    let T := S ∪ J
    let U := integralOutside D i T
    obtain ⟨hUc, hUo⟩ := compactOpenOutside D i T hc
    have hAT (w : A) : Sum.inr w.val ∈ T := Finset.mem_union_right S (hmem w)
    have hAS (w : A) : Sum.inr w.val ∉ S := Finset.disjoint_left.mp hd (hmem w)
    have hp := ProjectiveRecurrence.archimedeanLatticeProjection G i D hD S T A U
      Finset.subset_union_left hA hAS hAT hcompact hS hUc hUo hG hg
    let E : (∀ w : A, LocalPoints D i (.inr w.val)) ≃ₜ FinitePoints D i J :=
      Homeomorph.piCongrLeft (Y := fun w : (↑J : Set D.Place) => LocalPoints D i w.val) e
    have heq : E '' (↑((lattice D i T U).map (evaluateArchimedean D i A hAT)) :
        Set (∀ w : A, LocalPoints D i (.inr w.val))) =
        (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
      rw [show projectedArithmetic D i S J U =
        (lattice D i T U).map (forgetPlaces D i (J := J) Finset.subset_union_right) from rfl,
        Subgroup.coe_map, Subgroup.coe_map, Set.image_image]
      congr 1
      funext x w
      obtain ⟨a, rfl⟩ := e.surjective w
      rw [show E ((evaluateArchimedean D i A hAT) x) (e a) =
        (evaluateArchimedean D i A hAT) x a from Homeomorph.piCongrLeft_apply_apply e _ a]
      rfl
    have hp' : Dense (projectedArithmetic D i S J U : Set (FinitePoints D i J)) :=
      heq ▸ E.surjective.denseRange.dense_image E.continuous hp
    have hgen : Dense (Subgroup.closure {x : FinitePoints D i J | Contracted x} :
        Set (FinitePoints D i J)) := by
      apply denseProductContracted
      intro w
      obtain ⟨a, rfl⟩ := e.surjective w
      exact (hg a).mono (Subgroup.closure_mono (radicalContracted i D hD a.val))
    have hins := (isolateAdelicFactors D i S J hd U hUc hUo).2 hp' hgen
    have hker : ((forgetOutside D i (S := S) (T := T) Finset.subset_union_left).ker :
        Set (Adeles D i S)) ⊆ diagonalClosure D i S := by
      rw [← range_insertFinite_eq_ker D i hd]
      rintro _ ⟨x, rfl⟩
      exact hins x
    exact ((enlargeOmittedSet D i S T Finset.subset_union_left).2 hker).2.2.mp happrox
  · have hJ : J = ∅ := by simp [J, Finset.not_nonempty_iff_eq_empty.mp hA]
    simpa [hJ] using happrox

private theorem reductionAtNumberData {K A I : Type u} [Field K] [NumberField K]
    [DivisionRing A] [Algebra K A] [Fintype I]
    {hA : isCentralSimple K A} {b : Module.Basis I K A} {G : AffineAlgebraicGroup K}
    (h : RepresentsNormOne hA b G) (i : MatrixRealization G)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (D : GlobalFieldData.{u,u} K) (hD : D = .number inferInstance)
    (hcompact : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (S : Finset D.Place) (hS : ¬ CompactSpace (FinitePoints D i S)) :
    ∃ T : Finset D.Place,
      (∀ w : D.Place, w ∈ T ↔ w ∈ S ∨
        ∃ a : D.InfinitePlace, w = Sum.inr a ∧
          ¬ CompactSpace (LocalPoints D i (Sum.inr a))) ∧
      (∀ a : D.InfinitePlace, Sum.inr a ∉ T →
        CompactSpace (LocalPoints D i (Sum.inr a))) ∧
      ¬ CompactSpace (FinitePoints D i T) ∧
      (StrongApproximation D i T → StrongApproximation D i S) := by
  classical
  letI : Fintype D.InfinitePlace := by rw [hD]; exact inferInstanceAs (Fintype (NumberField.InfinitePlace K))
  let B : Finset D.InfinitePlace := Finset.univ.filter fun a =>
    Sum.inr a ∉ S ∧ ¬ CompactSpace (LocalPoints D i (.inr a))
  let J : Finset D.Place := B.map Function.Embedding.inr
  let T := S ∪ J
  have hB (a : D.InfinitePlace) : a ∈ B ↔
      Sum.inr a ∉ S ∧ ¬ CompactSpace (LocalPoints D i (.inr a)) := by simp [B]
  have hJ (w : D.Place) : w ∈ J ↔ ∃ a : D.InfinitePlace,
      w = Sum.inr a ∧ Sum.inr a ∉ S ∧ ¬ CompactSpace (LocalPoints D i (.inr a)) := by
    simp only [J, Finset.mem_map, Function.Embedding.inr_apply]
    exact ⟨fun ⟨a, ha, he⟩ => ⟨a, he.symm, (hB a).mp ha⟩,
      fun ⟨a, he, ha⟩ => ⟨a, (hB a).mpr ha, he.symm⟩⟩
  have hmem (w : D.Place) : w ∈ T ↔ w ∈ S ∨ ∃ a : D.InfinitePlace,
      w = Sum.inr a ∧ ¬ CompactSpace (LocalPoints D i (.inr a)) := by
    rw [Finset.mem_union, hJ]
    constructor
    · rintro (hs | ⟨a, ha, _, hc⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨a, ha, hc⟩
    · rintro (hs | ⟨a, rfl, hc⟩)
      · exact Or.inl hs
      · by_cases hs : Sum.inr a ∈ S
        · exact Or.inl hs
        · exact Or.inr ⟨a, rfl, hs, hc⟩
  have hc (a : D.InfinitePlace) : Sum.inr a ∉ T →
      CompactSpace (LocalPoints D i (.inr a)) := by
    intro ha
    by_contra hnc
    exact ha ((hmem _).mpr (Or.inr ⟨a, rfl, hnc⟩))
  have hd : Disjoint J S := Finset.disjoint_left.mpr fun w hw => by
    obtain ⟨a, rfl, ha, _⟩ := (hJ w).mp hw
    exact ha
  refine ⟨T, hmem, hc, noncompactOfSubset D i Finset.subset_union_left hS, ?_⟩
  exact liftThroughArchimedeanProduct i hG D hD S B hd hcompact hS hc
    (fun a => by
      rw [archimedeanRadicalsGenerate h i D hD a.val ((hB a.val).mp a.property).2,
        Subgroup.coe_top]
      exact dense_univ)

/-- The point data at a place, including the rational diagonal and the topology
used for its restricted product. Bundling the data allows comparison of the
two place universes by reducing at each of the two kinds of places. -/
private structure LocalFactor (Γ : Type u) [Group Γ] where
  points : Type u
  group : Group points
  topology : TopologicalSpace points
  integral : @Subgroup points group
  rational : @MonoidHom Γ points _ group.toMulOneClass.toMulOne

attribute [local instance] LocalFactor.group LocalFactor.topology

private def localFactor {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    LocalFactor (IntegralModels.RationalPoints G) :=
  ⟨LocalPoints D i w, inferInstance, inferInstance, localSubgroup D i w, localPoint D i w⟩

private abbrev factorProduct {Γ P : Type u} [Group Γ]
    (L : P → LocalFactor Γ) (S : Finset P) :=
  ∀ w : (↑S : Set P), (L w.val).points

private abbrev factorAdeles {Γ P : Type u} [Group Γ]
    (L : P → LocalFactor Γ) (S : Finset P) :=
  Πʳ w : {w : P // w ∉ S}, [(L w.val).points, (L w.val).integral]

private def factorDiagonal {Γ P : Type u} [Group Γ] (L : P → LocalFactor Γ) :
    Subgroup (factorAdeles L ∅) where
  carrier := {x | ∃ g : Γ, ∀ w, x w = (L w.val).rational g}
  one_mem' := ⟨1, fun w => (map_one (L w.val).rational).symm⟩
  mul_mem' := by
    rintro x y ⟨g, hg⟩ ⟨h, hh⟩
    exact ⟨g * h, fun w => by change x w * y w = _; rw [hg, hh, map_mul]⟩
  inv_mem' := by
    rintro x ⟨g, hg⟩
    exact ⟨g⁻¹, fun w => by change (x w)⁻¹ = _; rw [hg, map_inv]⟩

private def factorApproximation {Γ P : Type u} [Group Γ]
    (L : P → LocalFactor Γ) (S : Finset P) : Prop :=
  Dense {x : factorAdeles L S | ∃ g : Γ, ∀ w, x w = (L w.val).rational g}

private def reductionForFactors {Γ P A : Type u} [Group Γ]
    (L : P → LocalFactor Γ) (arch : A → P) (S : Finset P) : Prop :=
  CompactSpace (factorAdeles L ∅ ⧸ factorDiagonal L) →
  ¬ CompactSpace (factorProduct L S) →
  ∃ T : Finset P,
    (∀ w : P, w ∈ T ↔ w ∈ S ∨ ∃ a : A, w = arch a ∧ ¬ CompactSpace (L (arch a)).points) ∧
    (∀ a : A, arch a ∉ T → CompactSpace (L (arch a)).points) ∧
    ¬ CompactSpace (factorProduct L T) ∧
    (factorApproximation L T → factorApproximation L S)

theorem archimedeanReduction : ArchimedeanReduction.{u,v} := by
  classical
  intro K A _ D _ _ hA I _ b G hG _ h i hcompact S hSne hS
  cases D with
  | function F t =>
      refine ⟨S, ?_, ?_, hS, id⟩
      · intro w
        exact ⟨Or.inl, fun hw => hw.elim id (fun ⟨a, _, _⟩ => a.elim)⟩
      · intro a
        exact a.elim
  | number hK =>
      letI := hK
      let D₀ : GlobalFieldData.{u,u} K := .number hK
      let D₁ : GlobalFieldData.{u,v} K := .number hK
      have hfam : localFactor D₀ i = localFactor D₁ i := by
        funext w
        cases w <;> rfl
      have hred : reductionForFactors (localFactor D₀ i) Sum.inr S :=
        fun hc hn => reductionAtNumberData h i hG D₀ rfl hc S hn
      rw [hfam] at hred
      exact hred hcompact hS

end LinearAlgebraicGroups.Arithmetic.DivisionNormOneArchimedeanReduction
