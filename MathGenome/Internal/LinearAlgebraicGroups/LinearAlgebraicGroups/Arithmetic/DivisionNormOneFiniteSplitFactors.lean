import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.DivisionNormOneFiniteSplitFactors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AlmostEverywhereSplitAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Batteries.Tactic.OpenPrivate

open CategoryTheory Filter Topology
open scoped Classical CategoryTheory.MonObj TensorProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.DivisionNormOneFiniteSplitFactors

open LinearAlgebraicGroups.Specs
open AdelicGroups (PointsIn LocalPoints asMatrix changePoints)
open ArithmeticLatticeProjection (FinitePoints)
open CompactProductIsolation (Contracted)
open Specs.IntegralModels (MatrixRealization)
open Specs.OuterTypeAModels (RepresentsNormOne)
open Specs.GeometricRadicals (IsSplitReductive)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.Unipotent (Index baseChangedAlgebraicGroup)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open RM03.CSA.NormOneGroup (normOne normOneFunctor)
open Matrix (SpecialLinearGroup)
open private baseChangePointIso splitNormOnePoints
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private def normOnePointIso {K A I : Type u} [Field K] [Ring A] [Algebra K A]
    [Fintype I] {hA : isCentralSimple K A} {b : Module.Basis I K A}
    {G : AffineAlgebraicGroup K} (h : RepresentsNormOne hA b G) :
    (groupPointsFunctor K).obj G.val ≅ normOneFunctor hA b := by
  let p := Classical.choose h
  have hp := Classical.choose_spec h
  refine NatIso.ofComponents (fun R => ?_) ?_
  · letI := RM03.CSA.NormOneGroup.normOneGroup (R := R) hA b
    exact (show ((groupPointsFunctor K).obj G.val).obj R ≃* normOne (R := R) hA b from
      { toEquiv := p R
        map_mul' := fun x y => Subtype.ext (hp.1 R x y) }).toGrpIso
  · intro R S f
    ext x : 2
    exact Subtype.ext (hp.2 f x)

private def splitMatrixPoints {K F A I : Type u} [Field K] [Field F] [Algebra K F]
    [Ring A] [Algebra K A] [Fintype I] {hA : isCentralSimple K A}
    {b : Module.Basis I K A} {G : AffineAlgebraicGroup K} (h : RepresentsNormOne hA b G)
    (e : (F ⊗[K] A) ≃ₐ[F] Matrix (Fin (degree K A)) (Fin (degree K A)) F) :
    SpecialMatrixPoints (baseChangedAlgebraicGroup F G) (degree K A) :=
  baseChangePointIso G.val ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra K F) (normOnePointIso h) ≪≫
    splitNormOnePoints hA b e

private theorem splitMatrixStructure {F : Type u} [Field F] {L : AffineAlgebraicGroup F}
    {n : ℕ} (hn : 0 < n) (s : SpecialMatrixPoints L n) :
    IsSplitReductive L ∧ GeometricallySimplyConnected L := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨T, _, _, B, _, _, _, hsc⟩ :=
    LinearAlgebraicGroups.RootData.SpecialLinearDatum.matrixPinnedDatum F r L s
  obtain ⟨hc, hm⟩ := B.maximal
  exact ⟨⟨B.reductive, T.subgroup, T.split, hc, hm⟩, hsc⟩

/-- The split matrix comparison is continuous from the matrix group into
the given closed realization of the original group. -/
private theorem continuousSplitPoints {K F : Type u} [Field K] [Field F] [Algebra K F]
    [TopologicalSpace F] [IsTopologicalRing F] {G : AffineAlgebraicGroup K}
    (i : MatrixRealization G) {n : ℕ} (hn : 0 < n)
    (s : SpecialMatrixPoints (baseChangedAlgebraicGroup F G) n) :
    ∃ e : SpecialLinearGroup (Index.{u} n) F ≃* PointsIn i F, Continuous e := by
  let L := baseChangedAlgebraicGroup F G
  obtain ⟨j, hj⟩ := LocalCocharacterEvaluation.completionPointTopology (F := F) G i
  let M := LinearAlgebraicGroups.StandardGroups.generalLinearGroup F (Index.{u} n)
  let m := LinearAlgebraicGroups.StandardGroups.generalLinearGroupPointsIso F (Index.{u} n)
  obtain ⟨f, hf, hmatrix, _, _⟩ :=
    LinearAlgebraicGroups.GeneralLinearStructure.generalLinearDerived F n hn M L m s
  let j' : MatrixRealization L := ⟨n, M, m, f, hf⟩
  let q : PointsIn j' F ≃* SpecialLinearGroup (Index.{u} n) F :=
    (s.app (CommAlgCat.of F F)).groupIsoToMulEquiv
  have hq : Continuous q.symm := by
    apply (IsInducing.induced (asMatrix j' F)).continuous_iff.mpr
    have h : asMatrix j' F ∘ q.symm =
        (SpecialLinearGroup.toGL : SpecialLinearGroup (Index.{u} n) F → _) := by
      funext x
      change asMatrix j' F (q.symm x) = _
      rw [show asMatrix j' F (q.symm x) = SpecialLinearGroup.toGL (q (q.symm x)) from
        hmatrix (CommAlgCat.of F F) (q.symm x), q.apply_symm_apply]
    rw [h]
    exact SpecialLinearGroup.continuous_toGL
  let p : PointsIn j F ≃* PointsIn i F :=
    baseChangePointGroupEquiv F G.val (CommAlgCat.of F F)
  have hp : Continuous p := hj.continuous
  exact ⟨q.symm.trans ((changePoints j' j F).trans p),
    hp.comp ((AdelicGroups.continuous_changePoints j' j F).comp hq)⟩

private def singletonLocalPoints {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (w : D.Place) :
    FinitePoints D i {w} ≃ₜ* LocalPoints D i w := by
  let w₀ : (↑({w} : Finset D.Place) : Set D.Place) := ⟨w, Finset.mem_singleton_self _⟩
  letI : Unique (↑({w} : Finset D.Place) : Set D.Place) :=
    ⟨⟨w₀⟩, fun x => Subtype.ext (Finset.mem_singleton.mp x.property)⟩
  let A := fun x : (↑({w} : Finset D.Place) : Set D.Place) => LocalPoints D i x.1
  let h := Homeomorph.piUnique A
  exact ⟨MulEquiv.piUnique A, h.continuous, h.symm.continuous⟩

private theorem subgroup_eq_top_of_transvections {F idx : Type u} [Field F] [Fintype idx]
    [DecidableEq idx] (H : Subgroup (SpecialLinearGroup idx F))
    (h : ∀ (i j : idx) (hij : i ≠ j) (a : F), SpecialLinearGroup.transvection hij a ∈ H) :
    H = ⊤ := by
  apply top_unique
  intro x _
  rcases subsingleton_or_nontrivial idx with hidx | hidx
  · letI := hidx
    rw [Subsingleton.elim x 1]
    exact H.one_mem
  letI := hidx
  refine SpecialLinearGroup.diagonal_transvection_induction' (· ∈ H) x ?_ h
    (fun _ _ => H.mul_mem)
  intro i j hij a ha
  let t := Units.mk0 a ha
  let w := Specs.SpecialLinearDatum.transvectionWord (R := F) hij
  have hw (z : Fˣ) : w z ∈ H :=
    H.mul_mem (H.mul_mem (h i j hij z) (h j i hij.symm (-↑z⁻¹))) (h i j hij z)
  have hd : SpecialLinearGroup.diag2n hij a ha = w t * (w 1)⁻¹ := by
    apply Subtype.ext
    rw [SpecialLinearGroup.diag2n_coe,
      LinearAlgebraicGroups.RootData.SpecialLinearDatum.normalizedWord F idx i j hij t]
    congr 1
    funext l
    by_cases hi : l = i
    · simp only [Specs.SpecialLinearDatum.coordinatePairUnits, ite_eq_left hi, t, Units.val_mk0]
    · by_cases hj : l = j
      · simp only [Specs.SpecialLinearDatum.coordinatePairUnits, ite_eq_right hi, ite_eq_left hj, t,
          Units.val_inv_eq_inv_val, Units.val_mk0]
      · simp only [Specs.SpecialLinearDatum.coordinatePairUnits, ite_eq_right hi, ite_eq_right hj,
          Units.val_one]
  rw [hd]
  exact H.mul_mem (hw t) (H.inv_mem (hw 1))

open ValuativeRel in
private theorem contractingUnit (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    ∃ t : Fˣ, Tendsto (fun k : ℕ => (t : F) ^ k) atTop (𝓝 0) := by
  obtain ⟨x, hx, hv⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  letI : MulArchimedean (ValueGroupWithZero F) := isRankLeOne_iff_mulArchimedean.mp inferInstance
  exact ⟨Units.mk0 x hx, Valued.tendsto_zero_pow_of_v_lt_one (Γ₀ := ValueGroupWithZero F) hv⟩

private theorem diagonal_conjugates_transvection {F idx : Type u} [Field F] [Fintype idx]
    [DecidableEq idx] {i j : idx} (hij : i ≠ j) (t : F) (ht : t ≠ 0) (a : F) :
    let d := SpecialLinearGroup.diag2n hij t ht
    d * SpecialLinearGroup.transvection hij a * d⁻¹ =
      SpecialLinearGroup.transvection hij (t ^ 2 * a) := by
  let d := SpecialLinearGroup.diag2n hij t ht
  let e := SpecialLinearGroup.diag2n hij t⁻¹ (inv_ne_zero ht)
  have hde : d * e = 1 := by
    apply Subtype.ext
    change d.val * e.val = 1
    simp only [d, e, SpecialLinearGroup.diag2n_coe, Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one using 2
    funext l
    by_cases hi : l = i <;> by_cases hj : l = j <;>
      simp [hi, hj, ht, hij.symm]
  have he : d⁻¹ = e := inv_eq_of_mul_eq_one_right hde
  change d * SpecialLinearGroup.transvection hij a * d⁻¹ = _
  rw [he]
  apply Subtype.ext
  change d.val * (1 + Matrix.single i j a) * e.val = 1 + Matrix.single i j (t ^ 2 * a)
  rw [mul_add, mul_one, add_mul, show d.val * e.val = 1 from congrArg Subtype.val hde, add_right_inj]
  simp only [d, e, SpecialLinearGroup.diag2n_coe]
  ext l m
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hl : l = i <;> by_cases hm : m = j <;>
    simp [Matrix.single, hl, hm, Ne.symm, hij.symm, pow_two, mul_comm, mul_left_comm]

private theorem transvection_contracted {F idx : Type u} [Field F] [Fintype idx] [DecidableEq idx]
    [TopologicalSpace F] [IsTopologicalRing F] (t : Fˣ)
    (ht : Tendsto (fun k : ℕ => (t : F) ^ k) atTop (𝓝 0))
    {i j : idx} (hij : i ≠ j) (a : F) :
    Contracted (SpecialLinearGroup.transvection hij a) := by
  let d := SpecialLinearGroup.diag2n hij (t : F) t.ne_zero
  refine ⟨d, ?_⟩
  have hd (m : ℕ) : d ^ m * SpecialLinearGroup.transvection hij a * (d ^ m)⁻¹ =
      SpecialLinearGroup.transvection hij (((t : F) ^ m) ^ 2 * a) := by
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        d ^ (m + 1) * SpecialLinearGroup.transvection hij a * (d ^ (m + 1))⁻¹ =
            d * (d ^ m * SpecialLinearGroup.transvection hij a * (d ^ m)⁻¹) * d⁻¹ := by
              rw [pow_succ']
              group
        _ = _ := by
          rw [ih, diagonal_conjugates_transvection hij (t : F) t.ne_zero]
          congr 1
          rw [pow_succ]
          ring
  have hcont : Continuous (SpecialLinearGroup.transvection hij : F → SpecialLinearGroup idx F) := by
    apply IsInducing.subtypeVal.continuous_iff.mpr
    apply continuous_matrix
    intro l m
    change Continuous (fun b : F => (1 : Matrix idx idx F) l m + Matrix.single i j b l m)
    apply continuous_const.add
    by_cases h : i = l ∧ j = m
    · simpa only [Matrix.single, Matrix.of_apply, ite_eq_left h] using
        (continuous_id' : Continuous (fun b : F => b))
    · simpa only [Matrix.single, Matrix.of_apply, ite_eq_right h] using
        (continuous_const : Continuous (fun _ : F => (0 : F)))
  have hlim : Tendsto (fun m : ℕ => ((t : F) ^ m) ^ 2 * a) atTop (𝓝 0) := by
    simpa using (ht.pow 2).mul (tendsto_const_nhds (x := a))
  simpa only [hd, Function.comp_def, SpecialLinearGroup.transvection_coeff_zero] using
    (hcont.tendsto 0).comp hlim

private theorem dense_of_splitPoints {F P : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Group P] [TopologicalSpace P] {n : ℕ}
    (e : SpecialLinearGroup (Index.{u} n) F ≃* P) (he : Continuous e) :
    Dense (Subgroup.closure {x : P | Contracted x} : Set P) := by
  let H : Subgroup P := Subgroup.closure {x : P | Contracted x}
  obtain ⟨t, ht⟩ := contractingUnit F
  have hH : H.comap e.toMonoidHom = ⊤ := by
    apply subgroup_eq_top_of_transvections
    intro i j hij a
    change e (SpecialLinearGroup.transvection hij a) ∈ H
    apply Subgroup.subset_closure
    obtain ⟨d, hd⟩ := transvection_contracted t ht hij a
    refine ⟨e d, ?_⟩
    simpa only [Function.comp_def, map_one, map_mul, map_inv, map_pow] using
      (he.tendsto 1).comp hd
  have heq : H = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := e.surjective x
    change y ∈ H.comap e.toMonoidHom
    rw [hH]
    trivial
  change Dense (H : Set P)
  rw [heq, Subgroup.coe_top]
  exact dense_univ

/-- Cofinite split places and contracted generation for the original norm-one group. -/
theorem finiteSplitFactors : Specs.Arithmetic.DivisionNormOneFiniteSplitFactors.Statement.{u,v} := by
  intro K A _ D _ _ hA I _ b G _ _ h
  have hfinite := AlmostEverywhereSplitAlgebras.almost_everywhere_split D hA
  refine ⟨hfinite.toFinset, ?_⟩
  intro w hw
  let F := D.Completion (.inl w)
  letI : Algebra K F := AdelicGroups.completionAlgebra D (.inl w)
  letI : ValuativeRel F := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  letI : IsNonarchimedeanLocalField F := D.finiteCompletion_isLocalField w
  let n := degree K A
  have hn : 0 < n := RM03.CSA.degree_pos hA
  have hsplit : Nonempty ((F ⊗[K] A) ≃ₐ[F] Matrix (Fin n) (Fin n) F) := by
    by_contra hnot
    exact hw (hfinite.mem_toFinset.mpr hnot)
  obtain ⟨e⟩ := hsplit
  let s := splitMatrixPoints h e
  obtain ⟨hs, hsc⟩ := splitMatrixStructure hn s
  refine ⟨hs, hsc, fun i => ?_⟩
  obtain ⟨p, hp⟩ := continuousSplitPoints i hn s
  let q := (singletonLocalPoints D i (.inl w)).symm
  exact dense_of_splitPoints (p.trans q.toMulEquiv) (q.continuous.comp hp)

end

end LinearAlgebraicGroups.Arithmetic.DivisionNormOneFiniteSplitFactors
