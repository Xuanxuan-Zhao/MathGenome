import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.ProjectiveSpaces
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.LinearAlgebra.Projection
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.FinitePresentation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped DirectSum TensorProduct BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace LinearAlgebraicGroups.ProjectiveSpaces

open Specs.ProjectiveSpaces

noncomputable section

/-- Projective space in homogeneous coordinates. -/
abbrev coordinateProjectiveSpace := Specs.ProjectiveSpaces.coordinateProjectiveSpace

/-- The projective scheme of lines in a finite-dimensional space. -/
abbrev projectiveSpace (k : Type u) [Field k] (W : Type u) [AddCommGroup W] [Module k W]
    [Module.Finite k W] : SchemeOver k :=
  Specs.ProjectiveSpaces.projectiveSpace k W

variable (k ι : Type u) [Field k]

private def constantsEquiv : k ≃+* grading k ι 0 :=
  RingEquiv.ofBijective (constants k ι) (by
    constructor
    · intro a b h
      simpa [constants] using congrArg (fun p : grading k ι 0 => (p : MvPolynomial ι k).coeff 0) h
    · intro p
      have hp := p.property
      change (p : MvPolynomial ι k) ∈ MvPolynomial.homogeneousSubmodule ι k 0 at hp
      rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at hp
      obtain ⟨a, ha⟩ := hp
      exact ⟨a, Subtype.ext ha⟩)

private theorem adjoin_variables :
    Algebra.adjoin (grading k ι 0) (Set.range (MvPolynomial.X (R := k) (σ := ι))) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  clear * - k ι p
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact Subalgebra.algebraMap_mem _ (constants k ι a)
  | add p q hp hq =>
    exact add_mem hp hq
  | mul_X p i hp =>
    exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

private theorem finiteType_polynomials [Finite ι] :
    Algebra.FiniteType (grading k ι 0) (MvPolynomial ι k) := by
  classical
  let := Fintype.ofFinite ι
  exact ⟨⟨Finset.univ.image MvPolynomial.X, by simpa using adjoin_variables k ι⟩⟩

theorem projectiveSpaceProper : ProjectiveSpaceProper.{u} := by
  intro k W _ _ _ _
  let ι := ULift.{u} (Fin (Module.finrank k W))
  let := finiteType_polynomials k ι
  have h : IsIso (CommRingCat.ofHom (constants k ι)) :=
    (constantsEquiv k ι).toCommRingCatIso.isIso_hom
  change IsProper (Proj.toSpecZero (grading k ι) ≫ Spec.map (CommRingCat.ofHom (constants k ι)))
  infer_instance

theorem coordinateOpenCover : CoordinateOpenCover.{u} := by
  intro k ι _
  exact Proj.iSup_basicOpen_eq_top' _ _ (fun i => ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
    (adjoin_variables k ι)

theorem coordinateAffineCharts : CoordinateAffineCharts.{u} := by
  intro k ι _ i
  exact ⟨Proj.instIsOpenImmersionAwayι (grading k ι) _
    (MvPolynomial.isHomogeneous_X k i) Nat.one_pos, congrArg SetLike.coe (Proj.opensRange_awayι _ _ _ _)⟩

open HomogeneousLocalization

private def chartMap (i : ι) : MvPolynomial {j : ι // j ≠ i} k →+* chartRing k ι i :=
  MvPolynomial.eval₂Hom ((fromZeroRingHom (grading k ι) _).comp (constants k ι))
    (fun j => coordinateRatio k ι i j.val)

private theorem ratio_val (i j : ι) :
    (coordinateRatio k ι i j).val =
      Localization.mk (S := Submonoid.powers (MvPolynomial.X (R := k) i)) (MvPolynomial.X j) ⟨MvPolynomial.X i, Submonoid.mem_powers _⟩ := by
  change Localization.mk (S := Submonoid.powers (MvPolynomial.X (R := k) i)) _ ⟨MvPolynomial.X i ^ 1, ⟨1, rfl⟩⟩ = _
  congr 1
  exact Subtype.ext (pow_one _)

private theorem ratio_self (i : ι) : coordinateRatio k ι i i = 1 := by
  apply val_injective
  rw [ratio_val, val_one, Localization.mk_self_mk]

private theorem evaluate_fraction {B : Type u} [CommRing B] (i : ι)
    (f : MvPolynomial ι k →+* B) (hf : f (MvPolynomial.X i) = 1)
    (p : MvPolynomial ι k) (n : ℕ) :
    (IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X i))
      (g := f) (MvPolynomial.X i) (hf ▸ isUnit_one))
      (Localization.mk p ⟨MvPolynomial.X i ^ n, ⟨n, rfl⟩⟩) = f p := by
  rw [Localization.mk_eq_mk']
  let lift : Localization.Away (MvPolynomial.X (R := k) i) →+* B :=
    IsLocalization.Away.lift
    (g := f) (MvPolynomial.X i) (hf ▸ isUnit_one)
  change lift _ = _
  have h := congrArg lift (IsLocalization.mk'_spec (M := Submonoid.powers (MvPolynomial.X i))
    (Localization.Away (MvPolynomial.X i))
    p ⟨MvPolynomial.X i ^ n, ⟨n, rfl⟩⟩)
  simpa [lift, hf] using h

private theorem chartMap_injective (i : ι) : Function.Injective (chartMap k ι i) := by
  classical
  let f : MvPolynomial ι k →+* MvPolynomial {j : ι // j ≠ i} k :=
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun j => if h : j ≠ i then MvPolynomial.X ⟨j, h⟩ else 1)
  have hf : f (MvPolynomial.X i) = 1 := by simp [f]
  let g : Localization.Away (MvPolynomial.X (R := k) i) →+*
      MvPolynomial {j : ι // j ≠ i} k :=
    IsLocalization.Away.lift (g := f) (MvPolynomial.X i) (hf ▸ isUnit_one)
  let inv := g.comp (algebraMap (chartRing k ι i) _)
  have h : inv.comp (chartMap k ι i) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change g ((chartMap k ι i (MvPolynomial.C a)).val) = MvPolynomial.C a
      rw [chartMap, MvPolynomial.eval₂Hom_C]
      change g (Localization.mk (MvPolynomial.C a)
        ⟨(MvPolynomial.X i)^0, ⟨0, rfl⟩⟩) = MvPolynomial.C a
      rw [show g (Localization.mk (MvPolynomial.C a)
        ⟨(MvPolynomial.X i)^0, ⟨0, rfl⟩⟩) = f (MvPolynomial.C a)
        from evaluate_fraction k ι i f hf _ 0]
      simp [f]
    · intro j
      change g ((chartMap k ι i (MvPolynomial.X j)).val) = MvPolynomial.X j
      rw [chartMap, MvPolynomial.eval₂Hom_X']
      change g (Localization.mk (MvPolynomial.X j.val)
        ⟨(MvPolynomial.X i)^1, ⟨1, rfl⟩⟩) = MvPolynomial.X j
      rw [show g (Localization.mk (MvPolynomial.X j.val)
        ⟨(MvPolynomial.X i)^1, ⟨1, rfl⟩⟩) = f (MvPolynomial.X j.val)
        from evaluate_fraction k ι i f hf _ 1]
      simp [f, j.property]
  exact Function.LeftInverse.injective (g := inv) (fun p => DFunLike.congr_fun h p)

private theorem product_ratios [Fintype ι] (i : ι) (a : ι → ℕ) :
    ∏ j, coordinateRatio k ι i j ^ a j =
      Away.mk (grading k ι) (MvPolynomial.isHomogeneous_X k i)
        (∑ j, a j) (∏ j, MvPolynomial.X j ^ a j) (by
          simpa using (SetLike.prod_pow_mem_graded (grading k ι) (fun _ => 1) MvPolynomial.X
            (F := Finset.univ) a (fun j _ => (show MvPolynomial.X j ∈ grading k ι 1
              from MvPolynomial.isHomogeneous_X k j)))) := by
  apply val_injective
  change (algebraMap (chartRing k ι i) _) _ =
    Localization.mk (S := Submonoid.powers (MvPolynomial.X (R := k) i)) (∏ j, MvPolynomial.X j ^ a j)
      ⟨MvPolynomial.X i ^ (∑ j, a j), pow_mem (Submonoid.mem_powers _) _⟩
  simp only [map_prod, map_pow, HomogeneousLocalization.algebraMap_apply, ratio_val]
  simp_rw [Localization.mk_pow]
  rw [Localization.mk_prod]
  congr 1
  apply Subtype.ext
  simpa using (Finset.prod_pow_eq_pow_sum Finset.univ a (MvPolynomial.X (R := k) i))

private theorem chartMap_surjective [Finite ι] (i : ι) :
    Function.Surjective (chartMap k ι i) := by
  classical
  let := Fintype.ofFinite ι
  let : Algebra (grading k ι 0) (MvPolynomial {j : ι // j ≠ i} k) :=
    (MvPolynomial.C.comp (constantsEquiv k ι).symm.toRingHom).toAlgebra
  let φ : MvPolynomial {j : ι // j ≠ i} k →ₐ[grading k ι 0] chartRing k ι i :=
    { chartMap k ι i with
      commutes' a := by
        change chartMap k ι i (MvPolynomial.C ((constantsEquiv k ι).symm a)) =
          fromZeroRingHom (grading k ι) _ a
        rw [chartMap, MvPolynomial.eval₂Hom_C]
        exact congrArg (fromZeroRingHom (grading k ι) _) ((constantsEquiv k ι).apply_symm_apply a) }
  change Function.Surjective φ
  rw [← AlgHom.range_eq_top, ← top_le_iff]
  rw [← Away.adjoin_mk_prod_pow_eq_top (MvPolynomial.isHomogeneous_X k i) ι
    MvPolynomial.X (adjoin_variables k ι) (fun _ => 1) (MvPolynomial.isHomogeneous_X k)]
  apply Algebra.adjoin_le_iff.mpr
  rintro _ ⟨n, a, ha, -, rfl⟩
  have hn : (∑ j, a j) = n := by simpa using ha
  subst n
  rw [← product_ratios k ι i a]
  exact (φ.range.prod_mem (fun j _ => φ.range.pow_mem (show coordinateRatio k ι i j ∈ φ.range by
    by_cases hj : j = i
    · subst j
      rw [ratio_self]
      exact φ.range.one_mem
    · exact ⟨MvPolynomial.X ⟨j, hj⟩, MvPolynomial.eval₂Hom_X' _ _ _⟩) (a j)))

theorem polynomialChartCoordinates : PolynomialChartCoordinates.{u} := by
  intro k ι _ _ i
  exact ⟨RingEquiv.ofBijective (chartMap k ι i)
    ⟨chartMap_injective k ι i, chartMap_surjective k ι i⟩,
    MvPolynomial.eval₂Hom_C _ _, MvPolynomial.eval₂Hom_X' _ _⟩

theorem segreChartSurjective : SegreChartSurjective.{u} := by
  intro k I _ _ J p
  classical
  let φ := segreChartMap k p
  have generator (i : I) (j : {j : J i // j ≠ p i}) :
      MvPolynomial.X (⟨i, j⟩ : Σ i, {j : J i // j ≠ p i}) ∈ φ.range := by
    let q := Function.update p i j.val
    have hq : q ≠ p := by
      intro h
      exact j.property (by simpa [q] using congrFun h i)
    refine ⟨MvPolynomial.X ⟨q, hq⟩, ?_⟩
    change (segreChartMap k p) (MvPolynomial.X ⟨q, hq⟩) = _
    rw [segreChartMap, MvPolynomial.aeval_X, Finset.prod_eq_single i]
    · simp [q, normalizedCoordinate, j.property]
    · intro a _ ha
      simp [q, Function.update_of_ne ha, normalizedCoordinate]
    · simp
  apply (AlgHom.range_eq_top _).mp
  rw [eq_top_iff]
  intro r _
  clear * - generator r
  induction r using MvPolynomial.induction_on with
  | C a => exact Subalgebra.algebraMap_mem _ a
  | add f g hf hg => exact add_mem hf hg
  | mul_X f a hf => exact mul_mem hf (generator a.1 a.2)

theorem tensorBaseChange : TensorBaseChange.{u} := by
  intro k I _ _ W _ _ _ R
  let b := fun i => Module.finBasis k (W i)
  let src := Basis.piTensorProduct (fun i => (b i).baseChange R)
  let dst := (Basis.piTensorProduct b).baseChange R
  refine ⟨src.repr.trans dst.repr.symm, ?_⟩
  intro r v
  apply dst.ext_elem
  intro a
  change (dst.repr (dst.repr.symm (src.repr _))) a = _
  simp only [LinearEquiv.apply_symm_apply, src, dst, Basis.piTensorProduct_repr_tprod_apply,
    Basis.baseChange_repr_tmul, Algebra.smul_def, map_prod, Finset.prod_mul_distrib]

private def normalizedLine {ι W : Type u} [AddCommGroup W] [Module k W] [Finite ι]
    (b : Basis ι k W) (i : ι) (R : TestAlgebra k)
    (v : {v : R ⊗[k] W // (b.baseChange R).coord i v = 1}) :
    AffinePivotLine k b i R := by
  let α := LinearMap.toSpanSingleton R (R ⊗[k] W) v.val
  let q := (b.baseChange R).coord i
  have hleft (a : R) : q (α a) = a := by
    change q (a • v.val) = a
    rw [map_smul, v.property, smul_eq_mul, mul_one]
  let e : R ≃ₗ[R] α.range := LinearEquiv.ofInjective α (Function.LeftInverse.injective hleft)
  have he (a : R) : (e a : R ⊗[k] W) = α a := rfl
  have hq (x : α.range) : q x.val = e.symm x := by
    obtain ⟨a, rfl⟩ := e.surjective x
    rw [LinearEquiv.symm_apply_apply, he, hleft]
  let retraction := e.toLinearMap.comp q
  exact ⟨{
    submodule := α.range
    split := ⟨retraction.ker, LinearMap.isCompl_of_proj (fun x => by
      change e (q x.val) = x
      rw [hq, e.apply_symm_apply])⟩
    finite := Module.Finite.equiv e
    projective := Module.Projective.of_equiv e
    rank_one := fun p => by
      let := p.nontrivial
      rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_self]
      rfl },
    by
      have hEq : q ∘ α.range.subtype = e.symm := funext hq
      exact hEq.symm ▸ e.symm.bijective⟩

private theorem normalizedLine_span {ι W : Type u} [AddCommGroup W] [Module k W] [Finite ι]
    (b : Basis ι k W) (i : ι) (R : TestAlgebra k)
    (v : {v : R ⊗[k] W // (b.baseChange R).coord i v = 1}) :
    (normalizedLine k b i R v).val.submodule =
      Submodule.span R (Set.singleton v.val) :=
  LinearMap.range_toSpanSingleton _

private theorem affineLine_ext {W : Type u} [AddCommGroup W] [Module k W]
    {R : TestAlgebra k} {L M : AffineLine k W R} (h : L.submodule = M.submodule) : L = M := by
  cases L
  cases M
  cases h
  rfl

theorem affinePivotNormalForm : AffinePivotNormalForm.{u} := by
  intro k ι W _ _ _ _ b i R
  let q := (b.baseChange R).coord i
  have hinj : Function.Injective (normalizedLine k b i R) := by
    intro v w h
    have hs := congrArg (fun L : AffinePivotLine k b i R => L.val.submodule) h
    simp only [normalizedLine_span] at hs
    have hv : v.val ∈ Submodule.span R (Set.singleton w.val) :=
      hs ▸ Submodule.mem_span_singleton_self v.val
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    have ha1 := congrArg q ha
    change q (a • w.val) = q v.val at ha1
    rw [map_smul, w.property, v.property, smul_eq_mul, mul_one] at ha1
    apply Subtype.ext
    simpa [ha1] using ha.symm
  have hsurj : Function.Surjective (normalizedLine k b i R) := by
    intro L
    let π := q.comp L.val.submodule.subtype
    let e : L.val.submodule ≃ₗ[R] R := LinearEquiv.ofBijective π L.property
    let v := e.symm 1
    have hv : q v.val = 1 := e.apply_symm_apply 1
    refine ⟨⟨v.val, hv⟩, ?_⟩
    apply Subtype.ext
    apply affineLine_ext
    rw [normalizedLine_span]
    apply le_antisymm ((Submodule.span_singleton_le_iff_mem _ _).mpr v.property)
    intro x hx
    let y : L.val.submodule := ⟨x, hx⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨e y, ?_⟩
    have h : e y • v = y := by
      apply e.injective
      rw [map_smul]
      change e y • e (e.symm 1) = e y
      rw [e.apply_symm_apply, smul_eq_mul, mul_one]
    exact congrArg Subtype.val h
  exact ⟨Equiv.ofBijective (normalizedLine k b i R) ⟨hinj, hsurj⟩,
    normalizedLine_span k b i R⟩

private theorem chartStructureIsIso (k ι : Type u) [Field k] [Unique ι] :
    IsIso (chartScheme (k := k) (default : ι)).hom := by
  let i : ι := default
  let : IsEmpty {j : ι // j ≠ i} :=
    ⟨fun j => j.property (Subsingleton.elim j.val i)⟩
  obtain ⟨e, hC, _⟩ := polynomialChartCoordinates k ι i
  let incl := algebraMap k (chartRing k ι i)
  have h (a : k) : e (MvPolynomial.C a) = incl a := hC a
  have bij : Function.Bijective incl := by
    constructor
    · intro a b hab
      exact MvPolynomial.C_injective _ _ (e.injective ((h a).trans (hab.trans (h b).symm)))
    · intro z
      obtain ⟨f, rfl⟩ := e.surjective z
      refine ⟨f.coeff 0, ?_⟩
      rw [← h, ← MvPolynomial.eq_C_of_isEmpty f]
  have iso : IsIso (CommRingCat.ofHom incl) :=
    (RingEquiv.ofBijective incl bij).toCommRingCatIso.isIso_hom
  change IsIso (Spec.map (CommRingCat.ofHom incl))
  infer_instance

private theorem chartMorphismIsIso (k ι : Type u) [Field k] [Unique ι] :
    IsIso (chartMorphism (k := k) (default : ι)).left := by
  let i : ι := default
  have htop : coordinateOpen k ι i = ⊤ := by
    calc
      coordinateOpen k ι i = ⨆ j, coordinateOpen k ι j := by
        apply le_antisymm (le_iSup _ i)
        exact iSup_le fun j => (Subsingleton.elim j i) ▸ le_rfl
      _ = ⊤ := coordinateOpenCover k ι
  change IsIso (chartInclusion k ι i)
  rw [isIso_iff_isOpenImmersion_and_surjective, surjective_iff, ← Set.range_eq_univ]
  obtain ⟨hOpen, hRange⟩ := coordinateAffineCharts k ι i
  exact ⟨hOpen, hRange.trans (by simp [htop])⟩

private theorem coordinatePoint (k ι : Type u) [Field k] [Unique ι] :
    IsIso (coordinateProjectiveSpace k ι).hom := by
  let f := chartMorphism (k := k) (default : ι)
  let := chartMorphismIsIso k ι
  have : IsIso (f.left ≫ (coordinateProjectiveSpace k ι).hom) := by
    rw [Over.w f]
    exact chartStructureIsIso k ι
  exact IsIso.of_isIso_comp_left f.left _

theorem oneDimensionalProjectiveSpace : OneDimensionalProjectiveSpace.{u} := by
  intro k W _ _ _ _ h
  refine ⟨projectiveSpaceProper k W, ?_⟩
  let ι := ULift.{u} (Fin (Module.finrank k W))
  have hu : Nonempty (Unique ι) := Fintype.card_eq_one_iff_nonempty_unique.mp (by simp [ι, h])
  obtain ⟨inst⟩ := hu
  exact coordinatePoint k ι

theorem emptySegre : EmptySegre.{u} := by
  intro k I _ _ W _ _ _
  let c : tensorSpace (k := k) W ≃ₗ[k] k := PiTensorProduct.isEmptyEquiv I
  have hr : Module.finrank k (tensorSpace (k := k) W) = 1 :=
    c.finrank_eq.trans (Module.finrank_self k)
  let P := projectiveSpace k (tensorSpace (k := k) W)
  let U := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let : IsIso P.hom := (oneDimensionalProjectiveSpace k _ hr).2
  let ep : P ≅ U := Over.isoMk (asIso P.hom) (Category.comp_id _)
  have hU : Limits.IsTerminal U :=
    Limits.IsTerminal.ofUniqueHom (fun S => Over.homMk S.hom) (fun S f => by
      apply Over.OverMorphism.ext
      exact (Category.comp_id f.left).symm.trans (Over.w f))
  have hprod : Limits.IsTerminal (projectiveProduct (k := k) W) :=
    Limits.IsTerminal.ofUniqueHom (fun _ => Limits.Pi.lift (fun i => isEmptyElim i))
      (fun _ _ => Limits.Pi.hom_ext _ _ (fun i => isEmptyElim i))
  let e := hprod.uniqueUpToIso (hU.ofIso ep.symm)
  have : IsIso e.hom.left := inferInstanceAs
    (IsIso ((Over.forget (Spec (CommRingCat.of k))).map e.hom))
  exact ⟨e, inferInstance, ⟨c⟩⟩

private theorem localizationElem_eq_ratio (i j : ι) :
    Away.isLocalizationElem (coordinate_mem_degree_one k ι i)
      (coordinate_mem_degree_one k ι j) = coordinateRatio k ι i j := by
  apply val_injective
  change Localization.mk ((MvPolynomial.X j : MvPolynomial ι k) ^ 1)
    (S := Submonoid.powers (MvPolynomial.X (R := k) i)) ⟨_, pow_mem (Submonoid.mem_powers _) 1⟩ =
      Localization.mk (MvPolynomial.X j)
        ⟨MvPolynomial.X i ^ 1, pow_mem (Submonoid.mem_powers _) 1⟩
  rw [pow_one]

theorem coordinateOverlap : CoordinateOverlap.{u} := by
  intro k ι _ i j
  rw [← localizationElem_eq_ratio k ι i j]
  exact Proj.awayι_preimage_basicOpen (grading k ι) (coordinate_mem_degree_one k ι i) Nat.one_pos
    (coordinate_mem_degree_one k ι j) Nat.one_pos

private theorem val_overlap_ratio (i j l : ι) {f : MvPolynomial ι k}
    (hf : f = MvPolynomial.X i * MvPolynomial.X j) :
    (awayMap (grading k ι) (coordinate_mem_degree_one k ι j) hf
      (coordinateRatio k ι i l)).val =
    Localization.mk (MvPolynomial.X l * MvPolynomial.X j)
      (S := Submonoid.powers f) ⟨f, Submonoid.mem_powers _⟩ := by
  have h := val_awayMap_mk (grading k ι) (coordinate_mem_degree_one k ι j) hf
    1 ⟨MvPolynomial.X l, coordinate_mem_degree_one k ι l⟩ 1
    (show MvPolynomial.X i ^ 1 ∈ grading k ι 1 by
      rw [pow_one]; exact coordinate_mem_degree_one k ι i)
  refine h.trans ?_
  refine congrArg₂ (Localization.mk (S := Submonoid.powers f))
    (show MvPolynomial.X l * MvPolynomial.X j ^ 1 = MvPolynomial.X l * MvPolynomial.X j by
      rw [pow_one]) ?_
  exact Subtype.ext (pow_one _)

theorem coordinateTransition : CoordinateTransition.{u} := by
  intro k ι _ i j l
  apply val_injective
  let f : MvPolynomial ι k := MvPolynomial.X i * MvPolynomial.X j
  change (awayMap (grading k ι) (coordinate_mem_degree_one k ι j) (x := f) rfl
    (coordinateRatio k ι i l)).val =
    (awayMap (grading k ι) (coordinate_mem_degree_one k ι i) (x := f) (mul_comm _ _)
        (coordinateRatio k ι j l) *
      awayMap (grading k ι) (coordinate_mem_degree_one k ι j) (x := f) rfl
        (coordinateRatio k ι i j)).val
  rw [val_mul, val_overlap_ratio, val_overlap_ratio, val_overlap_ratio]
  rw [Localization.mk_mul]
  have hh : ((MvPolynomial.X l * MvPolynomial.X i) * (MvPolynomial.X j * MvPolynomial.X j) :
      MvPolynomial ι k) = (MvPolynomial.X l * MvPolynomial.X j) * f := by simp [f]; ac_rfl
  rw [hh]
  simp only [Localization.mk_eq_mk']
  exact (IsLocalization.mk'_cancel (S := Localization.Away f) (M := Submonoid.powers f)
    (MvPolynomial.X l * MvPolynomial.X j) ⟨f, Submonoid.mem_powers _⟩
    ⟨f, Submonoid.mem_powers _⟩).symm

theorem affinePivotCoordinates : AffinePivotCoordinates.{u} := by
  intro k ι W _ _ _ _ b i R
  obtain ⟨e, hC, hX⟩ := polynomialChartCoordinates k ι i
  let ψ : MvPolynomial {j : ι // j ≠ i} k ≃ₐ[k] chartRing k ι i :=
    { e with commutes' := hC }
  let B := b.baseChange R
  let F (a : chartRing k ι i →ₐ[k] R) :
      {v : R ⊗[k] W // B.coord i v = 1} :=
    ⟨B.equivFun.symm (fun j => a (coordinateRatio k ι i j)), by
      rw [Basis.coord_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply,
        ratio_self, map_one]⟩
  have hFj : Function.Injective F := by
    intro a b hab
    apply DFunLike.ext
    intro z
    obtain ⟨f, rfl⟩ := ψ.surjective z
    have h : a.comp ψ.toAlgHom = b.comp ψ.toAlgHom := by
      ext j
      change a (e (MvPolynomial.X j)) = b (e (MvPolynomial.X j))
      rw [hX]
      simpa only [F, LinearEquiv.apply_symm_apply] using
        congrArg (fun v => B.equivFun v.val j.val) hab
    exact DFunLike.congr_fun h f
  have hFs : Function.Surjective F := by
    intro v
    let vj := B.equivFun v.val
    let ev : MvPolynomial {j : ι // j ≠ i} k →ₐ[k] R :=
      MvPolynomial.aeval (fun j => vj j.val)
    let a := ev.comp ψ.symm.toAlgHom
    refine ⟨a, Subtype.ext (B.equivFun.injective ?_)⟩
    change B.equivFun (B.equivFun.symm (fun j => a (coordinateRatio k ι i j))) = vj
    rw [LinearEquiv.apply_symm_apply]
    funext j
    by_cases hj : j = i
    · subst j
      rw [ratio_self, map_one]
      exact v.property.symm
    · have he : ψ (MvPolynomial.X ⟨j, hj⟩) = coordinateRatio k ι i j := hX ⟨j, hj⟩
      rw [← he]
      simp [a, ev]
  obtain ⟨normal, hn⟩ := affinePivotNormalForm k ι W b i R
  exact ⟨(Equiv.ofBijective F ⟨hFj, hFs⟩).trans normal, fun a => hn (F a)⟩

section AffineBaseChange

variable {k : Type u} [Field k]
variable {W : Type u} [AddCommGroup W] [Module k W]

private def lineOfSplitInjection {R : TestAlgebra k} {M : Type u} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M]
    (f : M →ₗ[R] R ⊗[k] W) (r : R ⊗[k] W →ₗ[R] M) (hr : r.comp f = LinearMap.id)
    (hM : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1) : AffineLine k W R := by
  let e := LinearEquiv.ofInjective f (LinearMap.injective_of_comp_eq_id f r hr)
  let q := e.toLinearMap.comp r
  have hq (x : f.range) : q x.val = x := by
    obtain ⟨y, rfl⟩ := e.surjective x
    change e (r (f y)) = e y
    exact congrArg e (DFunLike.congr_fun hr y)
  exact ⟨f.range, ⟨q.ker, LinearMap.isCompl_of_proj hq⟩, Module.Finite.equiv e,
    Module.Projective.of_equiv e, fun p => by
      rw [← Module.rankAtStalk_eq_of_equiv e]
      exact hM p⟩

private def lineRetraction {R : TestAlgebra k} (L : AffineLine k W R) :
    R ⊗[k] W →ₗ[R] L.submodule :=
  L.submodule.projectionOnto L.split.choose L.split.choose_spec

@[simp]
private theorem lineRetraction_comp_subtype {R : TestAlgebra k} (L : AffineLine k W R) :
    (lineRetraction L).comp L.submodule.subtype = LinearMap.id :=
  Submodule.projectionOnto_comp_subtype L.split.choose_spec

/-- Scalar extension of affine lines along any map of test algebras. -/
def affineLineBaseChange {R T : TestAlgebra k} (a : R ⟶ T) (L : AffineLine k W R) :
    AffineLine k W T := by
  letI : Algebra R T := a.hom.toAlgebra
  letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  letI := L.finite
  letI := L.projective
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T W
  refine lineOfSplitInjection (e.toLinearMap.comp (L.submodule.subtype.baseChange T))
    (((lineRetraction L).baseChange T).comp e.symm.toLinearMap) ?_ (fun p => ?_)
  · have hc : ((lineRetraction L).baseChange T).comp (L.submodule.subtype.baseChange T) =
        LinearMap.id := by
      rw [← LinearMap.baseChange_comp, lineRetraction_comp_subtype, LinearMap.baseChange_id]
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
      using DFunLike.congr_fun hc x
  · exact (Module.rankAtStalk_baseChange (R := (R : Type u)) (M := L.submodule) p).trans
      (L.rank_one _)

@[simp]
theorem affineLineBaseChange_submodule {R T : TestAlgebra k} (a : R ⟶ T) (L : AffineLine k W R) :
    (affineLineBaseChange a L).submodule = changeLineSubmodule k W a L.submodule :=
  LinearMap.range_comp _ _

/-- Extension of the coefficients of a vector in the constant bundle. -/
private def extendVector {R T : TestAlgebra k} (a : R ⟶ T) :
    R ⊗[k] W →ₗ[k] T ⊗[k] W :=
  TensorProduct.map a.hom.toLinearMap (LinearMap.id : W →ₗ[k] W)

private theorem extendVector_tmul {R T : TestAlgebra k} (a : R ⟶ T) (r : R) (w : W) :
    (extendVector a) (r ⊗ₜ[k] w) = a.hom r ⊗ₜ[k] w := rfl

private theorem changeLineSubmodule_eq_span {R T : TestAlgebra k} (a : R ⟶ T)
    (L : Submodule R (R ⊗[k] W)) :
    changeLineSubmodule k W a L = Submodule.span T (extendVector a '' (L : Set (R ⊗[k] W))) := by
  let : Algebra R T := a.hom.toAlgebra
  let : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T W
  have he (x : R ⊗[k] W) : e (1 ⊗ₜ[R] x) = extendVector a x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    | tmul r w =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, extendVector_tmul]
      change ((algebraMap R T r) * 1) ⊗ₜ[k] w = a.hom r ⊗ₜ[k] w
      rw [mul_one]
      rfl
  change (L.baseChange T).map e.toLinearMap = _
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_image, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (he x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, he x⟩

private theorem extendVector_smul {R T : TestAlgebra k} (a : R ⟶ T)
    (r : R) (x : R ⊗[k] W) : extendVector a (r • x) = a.hom r • extendVector a x := by
  induction x using TensorProduct.inductionOn with
  | tmul s w =>
    rw [TensorProduct.smul_tmul', extendVector_tmul, extendVector_tmul, TensorProduct.smul_tmul']
    simp only [smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem extendVector_span {R T : TestAlgebra k} (a : R ⟶ T) (E : Set (R ⊗[k] W)) :
    Submodule.span T (extendVector a '' (Submodule.span R E : Set (R ⊗[k] W))) =
      Submodule.span T (extendVector a '' E) := by
  apply le_antisymm _ (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [extendVector_smul]; exact Submodule.smul_mem _ _ hx

theorem changeLineSubmodule_span {R T : TestAlgebra k} (a : R ⟶ T) (E : Set (R ⊗[k] W)) :
    changeLineSubmodule k W a (Submodule.span R E) = Submodule.span T (extendVector a '' E) := by
  rw [changeLineSubmodule_eq_span, extendVector_span]

private theorem extendVector_comp {R T U : TestAlgebra k} (a : R ⟶ T) (b : T ⟶ U)
    (x : R ⊗[k] W) : extendVector b (extendVector a x) = extendVector (a ≫ b) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r w => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem extendVector_id {R : TestAlgebra k} (x : R ⊗[k] W) :
    extendVector (𝟙 R) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r w => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem affineLineBaseChange_id {R : TestAlgebra k} (L : AffineLine k W R) :
    affineLineBaseChange (𝟙 R) L = L := by
  apply affineLine_ext
  rw [affineLineBaseChange_submodule, changeLineSubmodule_eq_span]
  have he : (extendVector (W := W) (𝟙 R) : R ⊗[k] W → R ⊗[k] W) = id :=
    funext extendVector_id
  rw [he, Set.image_id, Submodule.span_eq]

theorem affineLineBaseChange_comp {R T U : TestAlgebra k} (a : R ⟶ T) (b : T ⟶ U)
    (L : AffineLine k W R) :
    affineLineBaseChange (a ≫ b) L = affineLineBaseChange b (affineLineBaseChange a L) := by
  apply affineLine_ext
  simp only [affineLineBaseChange_submodule]
  rw [changeLineSubmodule_eq_span b, changeLineSubmodule_eq_span a, extendVector_span,
    Set.image_image, changeLineSubmodule_eq_span]
  exact congrArg (fun g : R ⊗[k] W → U ⊗[k] W =>
    Submodule.span U (g '' (L.submodule : Set (R ⊗[k] W)))) (funext (extendVector_comp a b)).symm

/-- The affine line functor on all commutative test algebras. -/
def affineLineFunctor (k : Type u) [Field k] (W : Type u) [AddCommGroup W] [Module k W] :
    TestAlgebra k ⥤ Type u where
  obj R := AffineLine k W R
  map a := ↾affineLineBaseChange a
  map_id R := by ext L; exact affineLineBaseChange_id L
  map_comp a b := by ext L; exact affineLineBaseChange_comp a b L

private theorem extendVector_coord {ι : Type u} (b : Basis ι k W) (i : ι)
    {R T : TestAlgebra k} (a : R ⟶ T) (x : R ⊗[k] W) :
    (b.baseChange T).coord i (extendVector a x) = a.hom ((b.baseChange R).coord i x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r w =>
    rw [extendVector_tmul, Basis.coord_apply, Basis.coord_apply,
      Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
      Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]

end AffineBaseChange

section PivotLocus

variable {k : Type u} [Field k]
variable {W ι : Type u} [AddCommGroup W] [Module k W] [Finite ι]

set_option maxHeartbeats 1000000 in
omit [Finite ι] in
private theorem lineCoord_bijective_of_surjective (b : Basis ι k W) (i : ι)
    {R : TestAlgebra k} (L : AffineLine k W R)
    (h : Function.Surjective ((b.baseChange R).coord i ∘ L.submodule.subtype)) :
    Function.Bijective ((b.baseChange R).coord i ∘ L.submodule.subtype) := by
  let := L.finite
  let := L.projective
  let f : L.submodule →ₗ[R] R := ((b.baseChange R).coord i).comp L.submodule.subtype
  change Function.Bijective f
  change Function.Surjective f at h
  exact Module.bijective_of_surjective_of_rankAtStalk_eq (φ := f) h (fun m _ => by
      let p : PrimeSpectrum R := ⟨m, inferInstance⟩
      let := p.nontrivial
      change Module.rankAtStalk L.submodule p = Module.rankAtStalk (R : Type u) p
      rw [L.rank_one, Module.rankAtStalk_self]
      rfl)

omit [Finite ι] in
private theorem lineCoord_bijective_of_one (b : Basis ι k W) (i : ι)
    {R : TestAlgebra k} (L : AffineLine k W R) (v : L.submodule)
    (hv : (b.baseChange R).coord i v.val = 1) :
    Function.Bijective ((b.baseChange R).coord i ∘ L.submodule.subtype) := by
  apply lineCoord_bijective_of_surjective b i L
  intro r
  refine ⟨r • v, ?_⟩
  change (b.baseChange R).coord i (r • v.val) = r
  rw [map_smul, hv, smul_eq_mul, mul_one]

omit [Finite ι] in
private theorem pivot_of_unit_coord (b : Basis ι k W) (i : ι)
    {R : TestAlgebra k} (L : AffineLine k W R) (v : L.submodule)
    (hv : IsUnit ((b.baseChange R).coord i v.val)) :
    Function.Bijective ((b.baseChange R).coord i ∘ L.submodule.subtype) := by
  obtain ⟨r, hr⟩ := hv
  refine lineCoord_bijective_of_one b i L ((↑r⁻¹ : R) • v) ?_
  change (b.baseChange R).coord i ((↑r⁻¹ : R) • v.val) = 1
  rw [map_smul, ← hr, smul_eq_mul, Units.inv_mul]

private theorem line_span_of_pivot (b : Basis ι k W) (i : ι)
    {R : TestAlgebra k} (L : AffinePivotLine k b i R) :
    ∃ v : R ⊗[k] W, (b.baseChange R).coord i v = 1 ∧
      L.val.submodule = Submodule.span R {v} := by
  obtain ⟨normal, hnormal⟩ := affinePivotNormalForm k ι W b i R
  obtain ⟨v, rfl⟩ := normal.surjective L
  exact ⟨v.val, v.property, hnormal v⟩

private theorem normalized_pivot_iff (b : Basis ι k W) (i j : ι)
    {R : TestAlgebra k} (v : {v : R ⊗[k] W // (b.baseChange R).coord i v = 1}) :
    Function.Bijective ((b.baseChange R).coord j ∘
      (normalizedLine k b i R v).val.submodule.subtype) ↔
      IsUnit ((b.baseChange R).coord j v.val) := by
  have hmem : v.val ∈ (normalizedLine k b i R v).val.submodule := by
    rw [normalizedLine_span]
    exact Submodule.mem_span_singleton_self _
  refine ⟨fun h => ?_, fun hv => pivot_of_unit_coord b j _ ⟨v.val, hmem⟩ hv⟩
  obtain ⟨x, hx⟩ := h.2 1
  set y : R ⊗[k] W := x.val with hy
  have hxmem : y ∈ (normalizedLine k b i R v).val.submodule := x.property
  rw [normalizedLine_span] at hxmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hxmem
  apply IsUnit.of_mul_eq_one r
  change (b.baseChange R).coord j y = 1 at hx
  rw [← hr, map_smul, smul_eq_mul, mul_comm] at hx
  exact hx

omit [Finite ι] in
/-- The coordinates of all vectors of a split rank-one line generate the unit ideal. -/
theorem lineCoordinates_span_top (b : Basis ι k W)
    {R : TestAlgebra k} (L : AffineLine k W R) :
    Ideal.span (Set.range (fun s : ι × L.submodule =>
      (b.baseChange R).coord s.1 s.2.val)) = ⊤ := by
  classical
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  let T := CommAlgCat.of k (R ⧸ m)
  let a : R ⟶ T := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k m)
  let N := affineLineBaseChange a L
  have hcoords (i : ι) (v : N.submodule) : (b.baseChange T).coord i v.val = 0 := by
    set y : T ⊗[k] W := v.val
    have hv : y ∈ (affineLineBaseChange a L).submodule := v.property
    rw [affineLineBaseChange_submodule, changeLineSubmodule_eq_span] at hv
    let q := (b.baseChange T).coord i
    have hspan : Submodule.span T (extendVector a '' (L.submodule : Set (R ⊗[k] W))) ≤ q.ker :=
      Submodule.span_le.mpr (by
        rintro _ ⟨w, hw, rfl⟩
        change q (extendVector a w) = 0
        rw [show q (extendVector a w) = a.hom ((b.baseChange R).coord i w)
          from extendVector_coord b i a w]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span ⟨(i, ⟨w, hw⟩), rfl⟩)))
    exact hspan hv
  have hsub : Subsingleton N.submodule := by
    rw [subsingleton_iff_forall_eq 0]
    intro v
    apply Subtype.ext
    apply (b.baseChange T).ext_elem
    intro i
    change (b.baseChange T).coord i v.val = (b.baseChange T).coord i 0
    rw [hcoords, map_zero]
  let p : PrimeSpectrum T := ⟨⊥, inferInstance⟩
  have hzero : Module.rankAtStalk N.submodule p = 0 := by
    rw [Module.rankAtStalk_eq_zero_of_subsingleton]
    rfl
  exact Nat.zero_ne_one (hzero.symm.trans (N.rank_one p))

private abbrev awayAlgebra {R : TestAlgebra k} (r : R) : TestAlgebra k :=
  CommAlgCat.of k (Localization.Away r)

private def awayHom {R : TestAlgebra k} (r : R) : R ⟶ awayAlgebra r :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Localization.Away r))

omit [Finite ι] in
/-- Localizing at a coordinate of any vector of the line makes that coordinate a pivot. -/
theorem linePivot_away (b : Basis ι k W) (i : ι)
    {R : TestAlgebra k} (L : AffineLine k W R) (v : L.submodule) :
    let r := (b.baseChange R).coord i v.val
    let a := awayHom (k := k) r
    Function.Bijective ((b.baseChange (awayAlgebra (k := k) r)).coord i ∘
      (affineLineBaseChange a L).submodule.subtype) := by
  intro r a
  have hv : extendVector a v.val ∈ (affineLineBaseChange a L).submodule := by
    rw [affineLineBaseChange_submodule, changeLineSubmodule_eq_span]
    exact Submodule.subset_span ⟨v.val, v.property, rfl⟩
  apply pivot_of_unit_coord b i _ ⟨_, hv⟩
  change IsUnit ((b.baseChange (awayAlgebra (k := k) r)).coord i (extendVector a v.val))
  rw [extendVector_coord]
  change IsUnit (algebraMap R (Localization.Away r) r)
  exact IsLocalization.Away.algebraMap_isUnit r

end PivotLocus

section ChartPoints

variable {k ι W : Type u} [Field k] [Finite ι] [AddCommGroup W] [Module k W]

private def chartVector (b : Basis ι k W) (i : ι) {R : TestAlgebra k}
    (a : chartRing k ι i →ₐ[k] R) : R ⊗[k] W :=
  (b.baseChange R).equivFun.symm (fun j => a (coordinateRatio k ι i j))

@[simp]
private theorem chartVector_coord (b : Basis ι k W) (i j : ι) {R : TestAlgebra k}
    (a : chartRing k ι i →ₐ[k] R) :
    (b.baseChange R).coord j (chartVector b i a) = a (coordinateRatio k ι i j) := by
  change (b.baseChange R).equivFun ((b.baseChange R).equivFun.symm _) j = _
  rw [LinearEquiv.apply_symm_apply]

private def chartLine (b : Basis ι k W) (i : ι) {R : TestAlgebra k}
    (a : chartRing k ι i →ₐ[k] R) : AffineLine k W R :=
  ((affinePivotCoordinates k ι W b i R).choose a).val

private theorem chartLine_span (b : Basis ι k W) (i : ι) {R : TestAlgebra k}
    (a : chartRing k ι i →ₐ[k] R) :
    (chartLine b i a).submodule = Submodule.span R {chartVector b i a} :=
  (affinePivotCoordinates k ι W b i R).choose_spec a

private theorem chartLine_injective (b : Basis ι k W) (i : ι) {R : TestAlgebra k} :
    Function.Injective (chartLine b i (R := R)) := by
  intro a a' h
  exact (affinePivotCoordinates k ι W b i R).choose.injective (Subtype.ext h)

private theorem chartLine_baseChange (b : Basis ι k W) (i : ι) {R T : TestAlgebra k}
    (a : chartRing k ι i →ₐ[k] R) (f : R ⟶ T) :
    affineLineBaseChange f (chartLine b i a) = chartLine b i (f.hom.comp a) := by
  apply affineLine_ext
  rw [affineLineBaseChange_submodule, chartLine_span, chartLine_span, changeLineSubmodule_span,
    Set.image_singleton]
  congr 2
  apply (b.baseChange T).ext_elem
  intro j
  change (b.baseChange T).coord j (extendVector f (chartVector b i a)) =
    (b.baseChange T).coord j (chartVector b i (f.hom.comp a))
  rw [extendVector_coord, chartVector_coord, chartVector_coord]
  rfl

private def chartPoint (i : ι) {R : TestAlgebra k} (a : chartRing k ι i →ₐ[k] R) :
    Points (coordinateProjectiveSpace k ι) R :=
  (testSpec k).map (CommAlgCat.ofHom a).op ≫ chartMorphism i

omit [Finite ι] in
private theorem chartPoint_baseChange (i : ι) {R T : TestAlgebra k}
    (a : chartRing k ι i →ₐ[k] R) (f : R ⟶ T) :
    mapPoints f (chartPoint i a) = chartPoint i (f.hom.comp a) := by
  simp only [mapPoints, chartPoint]
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

private theorem chartPoint_line_eq (b : Basis ι k W) {R : TestAlgebra k} {i j : ι}
    (a : chartRing k ι i →ₐ[k] R) (c : chartRing k ι j →ₐ[k] R)
    (h : chartPoint i a = chartPoint j c) : chartLine b i a = chartLine b j c := by
  let fa := Scheme.Spec.map (CommRingCat.ofHom a.toRingHom).op
  let fc := Scheme.Spec.map (CommRingCat.ofHom c.toRingHom).op
  have hfac : fa ≫ chartInclusion k ι i = fc ≫ chartInclusion k ι j :=
    congrArg Over.Hom.left h
  let e : pullback (chartInclusion k ι i) (chartInclusion k ι j) ≅
      Spec (CommRingCat.of (overlapRing k ι i j)) :=
    Proj.pullbackAwayιIso (grading k ι) (coordinate_mem_degree_one k ι i) Nat.one_pos
      (coordinate_mem_degree_one k ι j) Nat.one_pos rfl
  let m := pullback.lift fa fc hfac ≫ e.hom
  let t : overlapRing k ι i j →+* R := (Scheme.Spec.preimage m).unop.hom
  have hm : Spec.map (CommRingCat.ofHom t) = m := Scheme.Spec.map_preimage m
  have ha : t.comp (overlapFromFirst k ι i j) = a.toRingHom := by
    have hh : m ≫ Spec.map (CommRingCat.ofHom (overlapFromFirst k ι i j)) = fa := by
      dsimp only [m, e]
      rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left, pullback.lift_fst]
    rw [← hm, ← Spec.map_comp] at hh
    exact congrArg (fun f : CommRingCat.of (chartRing k ι i) ⟶ CommRingCat.of R => f.hom)
      (Quiver.Hom.op_inj (Scheme.Spec.map_injective hh))
  have hc : t.comp (overlapFromSecond k ι i j) = c.toRingHom := by
    have hh : m ≫ Spec.map (CommRingCat.ofHom (overlapFromSecond k ι i j)) = fc := by
      dsimp only [m, e]
      rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right, pullback.lift_snd]
    rw [← hm, ← Spec.map_comp] at hh
    exact congrArg (fun f : CommRingCat.of (chartRing k ι j) ⟶ CommRingCat.of R => f.hom)
      (Quiver.Hom.op_inj (Scheme.Spec.map_injective hh))
  have hcoord (l : ι) : a (coordinateRatio k ι i l) =
      c (coordinateRatio k ι j l) * a (coordinateRatio k ι i j) := by
    have h' := congrArg t (coordinateTransition k ι i j l)
    rw [map_mul] at h'
    change (t.comp (overlapFromFirst k ι i j)) (coordinateRatio k ι i l) =
      (t.comp (overlapFromSecond k ι i j)) (coordinateRatio k ι j l) *
        (t.comp (overlapFromFirst k ι i j)) (coordinateRatio k ι i j) at h'
    rwa [ha, hc] at h'
  have hv : chartVector b i a = a (coordinateRatio k ι i j) • chartVector b j c := by
    apply (b.baseChange R).ext_elem
    intro l
    change (b.baseChange R).coord l (chartVector b i a) =
      (b.baseChange R).coord l (a (coordinateRatio k ι i j) • chartVector b j c)
    rw [map_smul, chartVector_coord, chartVector_coord, smul_eq_mul, mul_comm]
    exact hcoord l
  have hunit : IsUnit (a (coordinateRatio k ι i j)) := by
    apply IsUnit.of_mul_eq_one (c (coordinateRatio k ι j i))
    have hi := hcoord i
    rw [ratio_self, map_one, mul_comm] at hi
    exact hi.symm
  apply affineLine_ext
  rw [chartLine_span, chartLine_span, hv]
  exact Submodule.span_singleton_smul_eq hunit _

omit [Finite ι] in
private theorem chartPoint_range_of_unit {R : TestAlgebra k} {i j : ι}
    (a : chartRing k ι i →ₐ[k] R) (ha : IsUnit (a (coordinateRatio k ι i j))) :
    Set.range (chartPoint i a).left ⊆ Set.range (chartInclusion k ι j) := by
  rw [(coordinateAffineCharts k ι j).2]
  rintro _ ⟨x, rfl⟩
  let f := Spec.map (CommRingCat.ofHom a.toRingHom)
  have hx : f x ∈ (chartInclusion k ι i) ⁻¹ᵁ coordinateOpen k ι j := by
    rw [coordinateOverlap k ι i j]
    let p : PrimeSpectrum R := x
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr
      (fun h => p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h ha))
  exact (Scheme.Hom.mem_preimage _).mp hx

private theorem chartPoint_eq_iff (b : Basis ι k W) {R : TestAlgebra k} {i j : ι}
    (a : chartRing k ι i →ₐ[k] R) (c : chartRing k ι j →ₐ[k] R) :
    chartPoint i a = chartPoint j c ↔ chartLine b i a = chartLine b j c := by
  refine ⟨chartPoint_line_eq b a c, fun h => ?_⟩
  have hunit : IsUnit (a (coordinateRatio k ι i j)) := by
    let v : {v : R ⊗[k] W // (b.baseChange R).coord i v = 1} :=
      ⟨chartVector b i a, by rw [chartVector_coord, ratio_self, map_one]⟩
    have he : (normalizedLine k b i R v).val = chartLine b i a := by
      apply affineLine_ext
      rw [normalizedLine_span, chartLine_span]
      rfl
    rw [← chartVector_coord b i j a]
    apply (normalized_pivot_iff b i j v).mp
    rw [he, h]
    exact ((affinePivotCoordinates k ι W b j R).choose c).property
  let g := IsOpenImmersion.lift (chartInclusion k ι j) (chartPoint i a).left
    (chartPoint_range_of_unit a hunit)
  have hg : g ≫ chartInclusion k ι j = (chartPoint i a).left :=
    IsOpenImmersion.lift_fac _ _ _
  let G : Points (chartScheme j) R := Over.homMk g (by
    rw [← Over.w (chartMorphism (k := k) j)]
    change g ≫ (chartInclusion k ι j ≫ (coordinateProjectiveSpace k ι).hom) = _
    rw [← Category.assoc, hg, Over.w])
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let d : chartRing k ι j →ₐ[k] R := (F.preimage G).unop.hom
  have hd : chartPoint j d = chartPoint i a := by
    change (testSpec k).map (F.preimage G) ≫ chartMorphism j = _
    rw [Functor.FullyFaithful.map_preimage F]
    exact Over.OverMorphism.ext hg
  have hdc := chartLine_injective b j ((chartPoint_line_eq b d a hd).trans h)
  exact hd.symm.trans (congrArg (chartPoint j) hdc)

end ChartPoints

section AffineTesting

variable {k : Type u} [Field k]

private abbrev overAlong {S : SchemeOver k} {U : Scheme.{u}} (a : U ⟶ S.left) : SchemeOver k :=
  Over.mk (a ≫ S.hom)

private abbrev overHom {S : SchemeOver k} {U : Scheme.{u}} (a : U ⟶ S.left) :
    overAlong a ⟶ S := Over.homMk a rfl

private def affinePresentation (S : SchemeOver k) [IsAffine S.left] :
    Σ R : TestAlgebra k, (testSpec k).obj (op R) ≅ S := by
  let e := S.left.isoSpec.symm
  let f := Scheme.Spec.preimage (e.hom ≫ S.hom)
  letI : Algebra k (S.left.presheaf.obj (op ⊤)) := f.unop.hom.toAlgebra
  let R := CommAlgCat.of k (S.left.presheaf.obj (op ⊤))
  refine ⟨R, Over.isoMk e ?_⟩
  change e.hom ≫ S.hom = Scheme.Spec.map f
  exact (Scheme.Spec.map_preimage _).symm

private def coverPresentation (S : SchemeOver k) (i : S.left.affineCover.I₀) :
    Σ R : TestAlgebra k, (testSpec k).obj (op R) ≅ overAlong (S.left.affineCover.f i) := by
  letI : IsAffine (overAlong (S.left.affineCover.f i)).left := S.left.isAffine_affineCover i
  exact affinePresentation (overAlong (S.left.affineCover.f i))

private theorem overHom_ext_affine {S T : SchemeOver k} (f g : S ⟶ T)
    (h : ∀ (R : TestAlgebra k) (a : Points S R), a ≫ f = a ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply S.left.affineCover.hom_ext
  intro i
  let e := (coverPresentation S i).2
  let q := e.hom ≫ overHom (S.left.affineCover.f i)
  have he := congrArg Over.Hom.left (h _ q)
  change (e.hom.left ≫ S.left.affineCover.f i) ≫ f.left =
    (e.hom.left ≫ S.left.affineCover.f i) ≫ g.left at he
  apply (cancel_epi e.hom.left).mp
  simpa only [Category.assoc] using he

private def glueOver {S T : SchemeOver k} (𝒰 : S.left.OpenCover)
    (m : ∀ i, overAlong (𝒰.f i) ⟶ T)
    (hm : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (m i).left =
      pullback.snd _ _ ≫ (m j).left) : S ⟶ T := by
  let q := 𝒰.glueMorphisms (fun i => (m i).left) hm
  refine Over.homMk q (𝒰.hom_ext _ _ fun i => ?_)
  rw [← Category.assoc, show 𝒰.f i ≫ q = (m i).left from 𝒰.ι_glueMorphisms _ hm i]
  exact Over.w (m i)

@[reassoc]
private theorem glueOver_fac {S T : SchemeOver k} (𝒰 : S.left.OpenCover)
    (m : ∀ i, overAlong (𝒰.f i) ⟶ T)
    (hm : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (m i).left =
      pullback.snd _ _ ≫ (m j).left) (i) :
    overHom (𝒰.f i) ≫ glueOver 𝒰 m hm = m i :=
  Over.OverMorphism.ext (𝒰.ι_glueMorphisms _ hm i)

private theorem onAffineTests_congr {S T : SchemeOver k}
    (m : ∀ (R : TestAlgebra k), Points S R → Points T R)
    (hm : ∀ {R R' : TestAlgebra k} (a : R ⟶ R') (p : Points S R),
      m R' (mapPoints a p) = mapPoints a (m R p))
    {R R' : TestAlgebra k} (x : (testSpec k).obj (op R') ⟶ (testSpec k).obj (op R))
    (p : Points S R) : m R' (x ≫ p) = x ≫ m R p := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a := (F.preimage x).unop
  have he : (testSpec k).map a.op = x := F.map_preimage x
  simpa only [mapPoints, he] using hm a p

set_option backward.isDefEq.respectTransparency false in
private theorem exists_of_affineTests {S T : SchemeOver k}
    (m : ∀ (R : TestAlgebra k), Points S R → Points T R)
    (hm : ∀ {R R' : TestAlgebra k} (a : R ⟶ R') (p : Points S R),
      m R' (mapPoints a p) = mapPoints a (m R p)) :
    ∃ f : S ⟶ T, ∀ (R : TestAlgebra k) (a : Points S R), a ≫ f = m R a := by
  let 𝒰 := S.left.affineCover
  let A (i : 𝒰.I₀) := (coverPresentation S i).1
  let e (i : 𝒰.I₀) := (coverPresentation S i).2
  let q (i : 𝒰.I₀) := (e i).hom ≫ overHom (𝒰.f i)
  let n (i : 𝒰.I₀) := (e i).inv ≫ m (A i) (q i)
  have hn {R : TestAlgebra k} (i : 𝒰.I₀)
      (p : Points (overAlong (𝒰.f i)) R) :
      p ≫ n i = m R (p ≫ overHom (𝒰.f i)) := by
    change p ≫ (e i).inv ≫ m (A i) (q i) = _
    rw [← Category.assoc, ← onAffineTests_congr m hm]
    simp [q, Category.assoc]
  have hc (i j : 𝒰.I₀) : pullback.fst (𝒰.f i) (𝒰.f j) ≫ (n i).left =
      pullback.snd _ _ ≫ (n j).left := by
    let V := overAlong (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
    let a : V ⟶ overAlong (𝒰.f i) :=
      Over.homMk (pullback.fst _ _) (Category.assoc _ _ _).symm
    let b : V ⟶ overAlong (𝒰.f j) := Over.homMk (pullback.snd _ _) (by
      dsimp [V]
      rw [← Category.assoc, ← pullback.condition])
    have hab : a ≫ overHom (𝒰.f i) = b ≫ overHom (𝒰.f j) :=
      Over.OverMorphism.ext pullback.condition
    exact congrArg Over.Hom.left (overHom_ext_affine (a ≫ n i) (b ≫ n j) fun R p => by
      rw [← Category.assoc p a, ← Category.assoc p b, hn i (p ≫ a), hn j (p ≫ b),
        Category.assoc, Category.assoc, hab])
  let f := glueOver 𝒰 n hc
  refine ⟨f, fun R p => ?_⟩
  apply Over.OverMorphism.ext
  let 𝒱 : ((testSpec k).obj (op R)).left.OpenCover := 𝒰.pullback₁ p.left
  apply 𝒱.hom_ext
  intro i
  let j : 𝒰.I₀ := i
  let V := overAlong (𝒱.f i)
  let a : V ⟶ overAlong (𝒰.f j) := Over.homMk (pullback.snd _ _) (by
    change pullback.snd p.left (𝒰.f j) ≫ (𝒰.f j ≫ S.hom) =
      pullback.fst p.left (𝒰.f j) ≫ ((testSpec k).obj (op R)).hom
    rw [← pullback.condition_assoc, Over.w p])
  let b := overHom (𝒱.f i)
  have hab : a ≫ overHom (𝒰.f j) = b ≫ p :=
    Over.OverMorphism.ext pullback.condition.symm
  have hglue : a ≫ n j = b ≫ p ≫ f := by
    calc
      a ≫ n j = (a ≫ overHom (𝒰.f j)) ≫ f := by
        rw [Category.assoc, glueOver_fac]
      _ = b ≫ p ≫ f := by rw [hab, Category.assoc]
  exact congrArg Over.Hom.left (overHom_ext_affine (b ≫ p ≫ f) (b ≫ m R p) fun R' t => by
    calc
      t ≫ b ≫ p ≫ f = (t ≫ a) ≫ n j := by rw [← hglue, Category.assoc]
      _ = m R' ((t ≫ a) ≫ overHom (𝒰.f j)) := hn j _
      _ = m R' ((t ≫ b) ≫ p) := by rw [Category.assoc, hab, Category.assoc]
      _ = t ≫ b ≫ m R p := by rw [onAffineTests_congr m hm, Category.assoc])

end AffineTesting

section LocalizationDescent

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W]
variable (k W)

private def scalarExtension (A B : Type u) [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] :
    A ⊗[k] W →ₗ[A] B ⊗[k] W :=
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B W).toLinearMap.restrictScalars A).comp
    (TensorProduct.mk A B _ 1)

private theorem scalarExtension_tmul (A B : Type u) [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] (r : A) (w : W) :
    scalarExtension k W A B (r ⊗ₜ[k] w) = algebraMap A B r ⊗ₜ[k] w := by
  change (TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B W)
    (1 ⊗ₜ[A] (r ⊗ₜ[k] w)) = _
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]

private instance scalarExtension_isLocalizedModule (A B : Type u) [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (s : Submonoid A) [IsLocalization s B] :
    IsLocalizedModule s (scalarExtension k W A B) :=
  (isLocalizedModule_iff_isBaseChange s B _).mpr
    (IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange k A B B W)
      (fun _ => rfl))

variable {k W}

private abbrev awaySubmodule {R : TestAlgebra k} (r : R) (N : Submodule R (R ⊗[k] W)) :
    Submodule (Localization.Away r) (Localization.Away r ⊗[k] W) :=
  N.localized' (Localization.Away r) (Submonoid.powers r) (scalarExtension k W R _)

private theorem scalarExtension_eq_extendVector {R : TestAlgebra k} (r : R) (v : R ⊗[k] W) :
    scalarExtension k W R (Localization.Away r) v = extendVector (awayHom r) v := by
  induction v using TensorProduct.inductionOn with
  | tmul a w => rw [scalarExtension_tmul, extendVector_tmul]; rfl
  | add v w hv hw => simp only [map_add, hv, hw]

private theorem awaySubmodule_eq_changeLineSubmodule {R : TestAlgebra k} (r : R)
    (N : Submodule R (R ⊗[k] W)) :
    awaySubmodule r N = changeLineSubmodule k W (awayHom r) N := by
  simp only [awaySubmodule, Submodule.localized'_eq_span, changeLineSubmodule_eq_span]
  congr 1
  exact congrArg (fun f : R ⊗[k] W → Localization.Away r ⊗[k] W =>
    f '' (N : Set (R ⊗[k] W))) (funext (scalarExtension_eq_extendVector r))

private theorem exists_pow_smul_mem_of_mem_away {A B M N : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] (r : A)
    [IsLocalization.Away r B] (f : M →ₗ[A] N) [IsLocalizedModule.Away r f]
    (P : Submodule A M) {x : M}
    (hx : f x ∈ P.localized' B (Submonoid.powers r) f) :
    ∃ n : ℕ, r ^ n • x ∈ P := by
  obtain ⟨y, hy, s, hs⟩ := (Submodule.mem_localized' B _ f P _).mp hx
  have h : f (s • x) = f y := by
    change f ((s : A) • x) = f y
    rw [map_smul]
    change s • f x = f y
    rw [← hs, IsLocalizedModule.mk'_cancel']
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers r) h
  have hmem : (t * s) • x ∈ P := by
    rw [mul_smul, ht]
    exact P.smul_mem _ hy
  obtain ⟨n, hn⟩ := (t * s).property
  change r ^ n = ((t * s : Submonoid.powers r) : A) at hn
  exact ⟨n, hn.symm ▸ hmem⟩

private theorem awaySubmodule_injective {R : TestAlgebra k} {s : Set R}
    (hs : Ideal.span s = ⊤) {N P : Submodule R (R ⊗[k] W)}
    (h : ∀ r : s, awaySubmodule r.val N = awaySubmodule r.val P) : N = P :=
  Submodule.eq_of_isLocalized'_span s hs (fun r => Localization.Away r.val)
    (fun r => Localization.Away r.val ⊗[k] W) (fun _r => scalarExtension k W R _) h

/-- Restrict an algebra map to a principal open when the denominator becomes a unit. -/
private def liftAway {R T : TestAlgebra k} (f : R ⟶ T) (r : R) (h : IsUnit (f.hom r)) :
    awayAlgebra r ⟶ T :=
  CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom r h)

@[simp]
private theorem awayHom_liftAway {R T : TestAlgebra k} (f : R ⟶ T)
    (r : R) (h : IsUnit (f.hom r)) : awayHom r ≫ liftAway f r h = f := by
  apply CommAlgCat.hom_ext
  ext x
  change IsLocalization.Away.lift r h (algebraMap R (Localization.Away r) x) = f.hom x
  exact IsLocalization.Away.lift_eq r h x

private theorem extendVector_mem_changeLineSubmodule {R T : TestAlgebra k} (a : R ⟶ T)
    {P : Submodule R (R ⊗[k] W)} {x : R ⊗[k] W} (hx : x ∈ P) :
    extendVector a x ∈ changeLineSubmodule k W a P := by
  rw [changeLineSubmodule_eq_span]
  exact Submodule.subset_span ⟨x, hx, rfl⟩

section Gluing

variable {R : TestAlgebra k} {I : Type u} [Fintype I]
variable (r : I → R) (L : ∀ i, AffineLine k W (awayAlgebra (r i)))
variable (hL : ∀ (i j : I) (T : TestAlgebra k) (a : awayAlgebra (r i) ⟶ T)
    (b : awayAlgebra (r j) ⟶ T), awayHom (r i) ≫ a = awayHom (r j) ≫ b →
    affineLineBaseChange a (L i) = affineLineBaseChange b (L j))

private def gluedSubmodule : Submodule R (R ⊗[k] W) :=
  ⨅ i, ((L i).submodule.restrictScalars R).comap (scalarExtension k W R (Localization.Away (r i)))

omit [Fintype I] in
private theorem mem_gluedSubmodule (v : R ⊗[k] W) :
    v ∈ gluedSubmodule r L ↔ ∀ i, extendVector (awayHom (r i)) v ∈ (L i).submodule := by
  simp only [gluedSubmodule, Submodule.mem_iInf, Submodule.mem_comap,
    scalarExtension_eq_extendVector]
  rfl

include hL in
private theorem pow_smul_mem_gluedSubmodule (i : I) (v : R ⊗[k] W)
    (hv : extendVector (awayHom (r i)) v ∈ (L i).submodule) :
    ∃ n : ℕ, r i ^ n • v ∈ gluedSubmodule r L := by
  classical
  have h (j : I) : ∃ n : ℕ,
      (awayHom (r j)).hom (r i) ^ n • extendVector (awayHom (r j)) v ∈ (L j).submodule := by
    let B := awayAlgebra (r j)
    let x : B := (awayHom (r j)).hom (r i)
    let C := awayAlgebra (k := k) x
    let b : B ⟶ C := awayHom x
    have hu : IsUnit (((awayHom (r j)) ≫ b).hom (r i)) :=
      IsLocalization.Away.algebraMap_isUnit x
    let a := liftAway (awayHom (r j) ≫ b) (r i) hu
    have hab : awayHom (r i) ≫ a = awayHom (r j) ≫ b := awayHom_liftAway _ _ _
    have hv' := extendVector_mem_changeLineSubmodule a hv
    rw [← affineLineBaseChange_submodule, hL i j C a b hab, affineLineBaseChange_submodule,
      ← awaySubmodule_eq_changeLineSubmodule] at hv'
    have he : extendVector a (extendVector (awayHom (r i)) v) =
        scalarExtension k W B (Localization.Away x) (extendVector (awayHom (r j)) v) := by
      rw [scalarExtension_eq_extendVector, extendVector_comp, extendVector_comp, hab]
    rw [he] at hv'
    exact exists_pow_smul_mem_of_mem_away x _ _ hv'
  choose n hn using h
  let m := Finset.univ.sup n
  refine ⟨m, (mem_gluedSubmodule r L _).2 fun j => ?_⟩
  have hj : n j ≤ m := Finset.le_sup (Finset.mem_univ j)
  rw [extendVector_smul, map_pow, ← Nat.sub_add_cancel hj, pow_add, mul_smul]
  exact (L j).submodule.smul_mem _ (hn j)

include hL in
private theorem localized_gluedSubmodule (i : I) :
    awaySubmodule (r i) (gluedSubmodule r L) = (L i).submodule := by
  let f := scalarExtension k W R (Localization.Away (r i))
  apply le_antisymm
  · simp only [awaySubmodule, Submodule.localized'_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    rw [scalarExtension_eq_extendVector]
    exact (mem_gluedSubmodule r L v).1 hv i
  · intro x hx
    obtain ⟨⟨v, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers (r i)) f x
    have hv : extendVector (awayHom (r i)) v ∈ (L i).submodule := by
      rw [← scalarExtension_eq_extendVector, ← IsLocalizedModule.mk'_cancel' f v s]
      rw [Submonoid.smul_def, ← IsScalarTower.algebraMap_smul (R := (R : Type u))
        (Localization.Away (r i))]
      change algebraMap R (Localization.Away (r i)) s.val •
        IsLocalizedModule.mk' f v s ∈ (L i).submodule
      exact (L i).submodule.smul_mem _ hx
    obtain ⟨n, hn⟩ := pow_smul_mem_gluedSubmodule r L hL i v hv
    let t : Submonoid.powers (r i) := ⟨r i ^ n, n, rfl⟩
    refine (Submodule.mem_localized' _ _ f _ _).mpr ⟨r i ^ n • v, hn, t * s, ?_⟩
    change IsLocalizedModule.mk' f (t • v) (t * s) = IsLocalizedModule.mk' f v s
    exact IsLocalizedModule.mk'_cancel_left f v t s

end Gluing

section ConstructLine

variable {R : TestAlgebra k} [Module.Finite k W]

set_option maxHeartbeats 600000 in
private theorem projective_quotient_of_localizations (s : Set R) (hs : Ideal.span s = ⊤)
    (N : Submodule R (R ⊗[k] W)) (L : ∀ r : s, AffineLine k W (awayAlgebra r.val))
    (hL : ∀ r : s, awaySubmodule r.val N = (L r).submodule) :
    Module.Projective R ((R ⊗[k] W) ⧸ N) := by
  let B (r : s) := Localization.Away r.val
  let V (r : s) := B r ⊗[k] W
  let Q (r : s) := V r ⧸ awaySubmodule r.val N
  let loc (r : s) := scalarExtension k W R (B r)
  let f (r : s) : (R ⊗[k] W) ⧸ N →ₗ[R] Q r :=
    N.toLocalizedQuotient' (B r) (Submonoid.powers r.val) (loc r)
  have : ∀ r : s, IsLocalizedModule.Away r.val (f r) :=
    fun r => IsLocalizedModule.toLocalizedQuotient' (B r) (Submonoid.powers r.val) (loc r) N
  have (r : s) : Module.Projective (B r) (Q r) := by
    obtain ⟨P, hP⟩ := (L r).split
    have h : IsCompl (awaySubmodule r.val N) P := (hL r).symm ▸ hP
    let e := (awaySubmodule r.val N).quotientEquivOfIsCompl P h
    have : Module.Projective (B r) P := Module.Projective.of_split P.subtype
      (P.projectionOnto _ h.symm) (Submodule.projectionOnto_comp_subtype h.symm)
    exact Module.Projective.of_equiv e.symm
  have : Module.Flat R ((R ⊗[k] W) ⧸ N) :=
    Module.flat_of_isLocalized_span (R : Type u) (R ⊗[k] W ⧸ N) s hs Q f
      (fun r => Module.Flat.trans R (B r) (Q r))
  have : Module.FinitePresentation R (R ⊗[k] W ⧸ N) :=
    Module.FinitePresentation.of_localizationSpan' s hs (Rₚ := B) f fun r =>
      Module.finitePresentation_of_projective (B r) (Q r)
  exact Module.Flat.projective_of_finitePresentation

omit [Module.Finite k W] in
private theorem line_rank_of_localizations (s : Set R) (hs : Ideal.span s = ⊤)
    (N : Submodule R (R ⊗[k] W)) [Module.Finite R N] [Module.Projective R N]
    (L : ∀ r : s, AffineLine k W (awayAlgebra r.val))
    (hL : ∀ r : s, awaySubmodule r.val N = (L r).submodule) (p : PrimeSpectrum R) :
    Module.rankAtStalk N p = 1 := by
  have hp : ∃ r : s, r.val ∉ p.asIdeal := by
    by_contra! hn
    have hle : Ideal.span s ≤ p.asIdeal := Ideal.span_le.mpr fun x hx => hn ⟨x, hx⟩
    exact p.isPrime.ne_top (top_unique (hs ▸ hle))
  obtain ⟨r, hr⟩ := hp
  let B := Localization.Away r.val
  obtain ⟨p', hp'⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R B)) := by
    rw [PrimeSpectrum.localization_away_comap_range B r.val]
    exact hr
  let S := Submonoid.powers r.val
  let g := N.toLocalized' B S (scalarExtension k W R B)
  have h : Module.rankAtStalk (awaySubmodule r.val N) p' =
      Module.rankAtStalk N (PrimeSpectrum.comap (algebraMap R B) p') :=
    Module.rankAtStalk_isBaseChange (R := (R : Type u)) (M := N) (f := g)
      (IsLocalizedModule.isBaseChange S B g) p'
  rw [hp'] at h
  exact h.symm.trans ((hL r).symm ▸ (L r).rank_one p')

private theorem line_of_localizations (s : Set R) (hs : Ideal.span s = ⊤)
    (N : Submodule R (R ⊗[k] W)) (L : ∀ r : s, AffineLine k W (awayAlgebra r.val))
    (hL : ∀ r : s, awaySubmodule r.val N = (L r).submodule) :
    ∃ M : AffineLine k W R, M.submodule = N := by
  have := projective_quotient_of_localizations s hs N L hL
  obtain ⟨q, hq⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let π : R ⊗[k] W →ₗ[R] N :=
    (LinearMap.id - q.comp N.mkQ).codRestrict N fun v => by
      apply (Submodule.Quotient.mk_eq_zero N).mp
      change N.mkQ (v - q (N.mkQ v)) = 0
      rw [map_sub, show N.mkQ (q (N.mkQ v)) = N.mkQ v from DFunLike.congr_fun hq (N.mkQ v),
        sub_self]
  have hπ (v : N) : π v.val = v := by
    apply Subtype.ext
    change v.val - q (N.mkQ v.val) = v.val
    rw [N.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr v.property, map_zero, sub_zero]
  have : Module.Projective R N := Module.Projective.of_split N.subtype π (LinearMap.ext hπ)
  have : Module.Finite R N := Module.Finite.of_surjective π fun v => ⟨v.val, hπ v⟩
  exact ⟨⟨N, ⟨π.ker, LinearMap.isCompl_of_proj hπ⟩, inferInstance, inferInstance,
    line_rank_of_localizations s hs N L hL⟩, rfl⟩

end ConstructLine

end LocalizationDescent

section PrincipalCovers

variable {k : Type u} [Field k] {R : TestAlgebra k}

private theorem mapPoints_comp' {T U : TestAlgebra k} {S : SchemeOver k}
    (a : R ⟶ T) (b : T ⟶ U) (p : Points S R) :
    mapPoints b (mapPoints a p) = mapPoints (a ≫ b) p := by
  simp only [mapPoints, op_comp, Functor.map_comp, Category.assoc]

private def extendAway {T : TestAlgebra k} (a : R ⟶ T) (r : R) :
    awayAlgebra r ⟶ awayAlgebra (a.hom r) :=
  liftAway (a ≫ awayHom (a.hom r)) r
    (IsLocalization.Away.algebraMap_isUnit (a.hom r))

private theorem awayHom_extendAway {T : TestAlgebra k} (a : R ⟶ T) (r : R) :
    awayHom r ≫ extendAway a r = a ≫ awayHom (a.hom r) := awayHom_liftAway _ _ _

private theorem span_range_map_eq_top {I : Type u} {T : TestAlgebra k} (a : R ⟶ T)
    (r : I → R) (hr : Ideal.span (Set.range r) = ⊤) :
    Ideal.span (Set.range fun i => a.hom (r i)) = ⊤ := by
  rw [show (fun i => a.hom (r i)) = a.hom ∘ r from rfl, Set.range_comp]
  change Ideal.span ((a.hom : R →+* T) '' Set.range r) = ⊤
  rw [← Ideal.map_span, hr, Ideal.map_top]

private def principalOpenCover {I : Type u} (r : I → R)
    (hr : Ideal.span (Set.range r) = ⊤) : ((testSpec k).obj (op R)).left.OpenCover where
  I₀ := I
  X i := ((testSpec k).obj (op (awayAlgebra (r i)))).left
  f i := ((testSpec k).map (awayHom (r i)).op).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      have hx : ∃ i, r i ∉ x.asIdeal := by
        by_contra! h
        exact x.isPrime.ne_top (top_unique (hr ▸ Ideal.span_le.mpr (Set.range_subset_iff.mpr h)))
      obtain ⟨i, hi⟩ := hx
      refine ⟨i, ?_⟩
      change x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (r i))))
      exact (PrimeSpectrum.localization_away_comap_range (Localization.Away (r i)) (r i)).symm ▸
        (PrimeSpectrum.mem_basicOpen (r i) (x : PrimeSpectrum R)).mpr hi
    · intro i
      change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r i)))))
      infer_instance

private theorem affinePoints_ext_principal {T : SchemeOver k} {p q : Points T R}
    {I : Type u} (r : I → R) (hr : Ideal.span (Set.range r) = ⊤)
    (h : ∀ i, mapPoints (awayHom (r i)) p = mapPoints (awayHom (r i)) q) :
    p = q :=
  Over.OverMorphism.ext ((principalOpenCover r hr).hom_ext _ _
    fun i => congrArg Over.Hom.left (h i))

private theorem gluePrincipalPoints {T : SchemeOver k} {I : Type u} (r : I → R)
    (hr : Ideal.span (Set.range r) = ⊤) (p : ∀ i, Points T (awayAlgebra (r i)))
    (hp : ∀ (i j : I) (A : TestAlgebra k) (a : awayAlgebra (r i) ⟶ A)
      (b : awayAlgebra (r j) ⟶ A), awayHom (r i) ≫ a = awayHom (r j) ≫ b →
        mapPoints a (p i) = mapPoints b (p j)) :
    ∃ q : Points T R, ∀ i, mapPoints (awayHom (r i)) q = p i := by
  let 𝒰 := principalOpenCover r hr
  let a₀ (i : I) := (testSpec k).map (awayHom (r i)).op
  have hm (i j : I) : pullback.fst (𝒰.f i) (𝒰.f j) ≫ (p i).left =
      pullback.snd _ _ ≫ (p j).left := by
    let V := overAlong (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
    let u : V ⟶ (testSpec k).obj (op (awayAlgebra (r i))) := Over.homMk (pullback.fst _ _) (by
      rw [← Over.w (a₀ i)]
      exact (Category.assoc _ _ _).symm)
    let v : V ⟶ (testSpec k).obj (op (awayAlgebra (r j))) := Over.homMk (pullback.snd _ _) (by
      have h := Over.w (a₀ j)
      refine (congrArg (pullback.snd (𝒰.f i) (𝒰.f j) ≫ ·) h.symm).trans ?_
      exact (pullback.condition_assoc (f := 𝒰.f i) (g := 𝒰.f j) _).symm.trans
        (Category.assoc _ _ _).symm)
    have huv : u ≫ a₀ i = v ≫ a₀ j := Over.OverMorphism.ext pullback.condition
    apply congrArg Over.Hom.left (a₁ := u ≫ p i) (a₂ := v ≫ p j)
    apply overHom_ext_affine
    intro A t
    let F := algSpec.fullyFaithful (R := CommRingCat.of k)
    let a := (F.preimage (t ≫ u)).unop
    let b := (F.preimage (t ≫ v)).unop
    have ha : (testSpec k).map a.op = t ≫ u := F.map_preimage _
    have hb : (testSpec k).map b.op = t ≫ v := F.map_preimage _
    have hab : awayHom (r i) ≫ a = awayHom (r j) ≫ b := by
      apply Quiver.Hom.op_inj
      apply F.map_injective
      simp only [op_comp, Functor.map_comp, ha, hb, Category.assoc]
      exact congrArg (t ≫ ·) huv
    simpa only [mapPoints, ha, hb, Category.assoc] using hp i j A a b hab
  let q := 𝒰.glueMorphisms (fun i => (p i).left) hm
  have hq (i : I) : 𝒰.f i ≫ q = (p i).left := 𝒰.ι_glueMorphisms _ hm i
  have hw : q ≫ T.hom = ((testSpec k).obj (op R)).hom := by
    apply 𝒰.hom_ext
    intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ T.hom) (hq i)).trans ((Over.w (p i)).trans (Over.w (a₀ i)).symm))
  exact ⟨Over.homMk q hw, fun i => Over.OverMorphism.ext (hq i)⟩

end PrincipalCovers

section AffineRepresentation

variable {k ι W : Type u} [Field k] [Finite ι] [AddCommGroup W] [Module k W]
variable {R : TestAlgebra k}

omit [Finite ι] in
private theorem point_has_chart {i : ι} (p : Points (coordinateProjectiveSpace k ι) R)
    (hp : Set.range p.left ⊆ Set.range (chartInclusion k ι i)) :
    ∃ a : chartRing k ι i →ₐ[k] R, p = chartPoint i a := by
  let g := IsOpenImmersion.lift (chartInclusion k ι i) p.left hp
  have hg : g ≫ chartInclusion k ι i = p.left := IsOpenImmersion.lift_fac _ _ _
  let G : Points (chartScheme i) R := Over.homMk g (by
    rw [← Over.w (chartMorphism (k := k) i)]
    change g ≫ (chartInclusion k ι i ≫ (coordinateProjectiveSpace k ι).hom) = _
    rw [← Category.assoc, hg, Over.w])
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  refine ⟨(F.preimage G).unop.hom, ?_⟩
  change p = (testSpec k).map (F.preimage G) ≫ chartMorphism i
  rw [Functor.FullyFaithful.map_preimage F]
  exact Over.OverMorphism.ext hg.symm

omit [Finite ι] in
private theorem point_has_principal_chart_cover (p : Points (coordinateProjectiveSpace k ι) R) :
    ∃ (J : Type u) (_ : Fintype J) (r : J → R) (i : J → ι)
      (a : ∀ j, chartRing k ι (i j) →ₐ[k] awayAlgebra (r j)),
      Ideal.span (Set.range r) = ⊤ ∧ ∀ j, mapPoints (awayHom (r j)) p = chartPoint (i j) (a j) := by
  classical
  let s : Set R := { r | ∃ i : ι,
    (PrimeSpectrum.basicOpen r : ((testSpec k).obj (op R)).left.Opens) ≤
      p.left ⁻¹ᵁ coordinateOpen k ι i }
  have hcov (x : PrimeSpectrum R) : ∃ r ∈ s, x ∈ PrimeSpectrum.basicOpen r := by
    have hx : p.left x ∈ (⨆ i, coordinateOpen k ι i) := by
      rw [coordinateOpenCover k ι]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hx' : x ∈ p.left ⁻¹ᵁ coordinateOpen k ι i := (Scheme.Hom.mem_preimage _).mpr hi
    obtain ⟨U, ⟨r, rfl⟩, hxr, hr⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (PrimeSpectrum.isBasis_basic_opens (R := R))) hx'
    exact ⟨r, ⟨i, hr⟩, hxr⟩
  have hs : Ideal.span s = ⊤ := by
    by_contra hn
    obtain ⟨m, hm, hle⟩ := (Ideal.span s).exists_le_maximal hn
    obtain ⟨r, hr, hx⟩ := hcov ⟨m, inferInstance⟩
    exact hx (hle (Ideal.subset_span hr))
  obtain ⟨t, ht, ht'⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  let r : (↑t : Type u) → R := Subtype.val
  let i (j : (↑t : Type u)) := (ht j.property).choose
  have h (j : (↑t : Type u)) : ∃ a : chartRing k ι (i j) →ₐ[k] awayAlgebra (r j),
      mapPoints (awayHom (r j)) p = chartPoint (i j) a := by
    apply point_has_chart
    rw [(coordinateAffineCharts k ι (i j)).2]
    rintro _ ⟨x, rfl⟩
    have hx : PrimeSpectrum.comap (algebraMap R (Localization.Away (r j))) x ∈
        PrimeSpectrum.basicOpen (r j) := by
      let y : PrimeSpectrum (Localization.Away (r j)) := x
      change PrimeSpectrum.comap (algebraMap R (Localization.Away (r j))) y ∈
        (PrimeSpectrum.basicOpen (r j) : Set (PrimeSpectrum R))
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (r j)) (r j)]
      exact Set.mem_range_self y
    exact (Scheme.Hom.mem_preimage p.left).mp ((ht j.property).choose_spec hx)
  choose a ha using h
  exact ⟨↑t, inferInstance, r, i, a, by rwa [Subtype.range_val], ha⟩

/-- The line of a point is characterized by its coordinates on all affine tests
that factor through one of the standard charts. -/
private def IsLineOfPoint (b : Basis ι k W) (p : Points (coordinateProjectiveSpace k ι) R)
    (L : AffineLine k W R) : Prop :=
  ∀ (T : TestAlgebra k) (f : R ⟶ T) (j : ι) (a : chartRing k ι j →ₐ[k] T),
    mapPoints f p = chartPoint j a → affineLineBaseChange f L = chartLine b j a

omit [Finite ι] in
private theorem affineLines_ext_principal {L M : AffineLine k W R}
    {J : Type u} (r : J → R) (hr : Ideal.span (Set.range r) = ⊤)
    (h : ∀ j, affineLineBaseChange (awayHom (r j)) L = affineLineBaseChange (awayHom (r j)) M) :
    L = M := by
  apply affineLine_ext
  apply awaySubmodule_injective hr
  rintro ⟨_, ⟨j, rfl⟩⟩
  simpa only [awaySubmodule_eq_changeLineSubmodule, ← affineLineBaseChange_submodule] using
    congrArg AffineLine.submodule (h j)

private theorem isLineOfPoint_of_cover (b : Basis ι k W)
    (p : Points (coordinateProjectiveSpace k ι) R) (L : AffineLine k W R)
    {J : Type u} (r : J → R) (hr : Ideal.span (Set.range r) = ⊤)
    (i : J → ι) (a : ∀ j, chartRing k ι (i j) →ₐ[k] awayAlgebra (r j))
    (hp : ∀ j, mapPoints (awayHom (r j)) p = chartPoint (i j) (a j))
    (hL : ∀ j, affineLineBaseChange (awayHom (r j)) L = chartLine b (i j) (a j)) :
    IsLineOfPoint b p L := by
  intro T f j c hc
  apply affineLines_ext_principal (fun t => f.hom (r t)) (span_range_map_eq_top f r hr)
  intro t
  let f' := extendAway f (r t)
  let g := awayHom (f.hom (r t))
  have hfg : awayHom (r t) ≫ f' = f ≫ g := awayHom_extendAway f (r t)
  have hp' : chartPoint (i t) (f'.hom.comp (a t)) = chartPoint j (g.hom.comp c) := by
    rw [← chartPoint_baseChange, ← chartPoint_baseChange, ← hp, ← hc,
      mapPoints_comp', mapPoints_comp', hfg]
  change affineLineBaseChange g (affineLineBaseChange f L) =
    affineLineBaseChange g (chartLine b j c)
  rw [← affineLineBaseChange_comp, ← hfg, affineLineBaseChange_comp, hL,
    chartLine_baseChange, chartLine_baseChange]
  exact chartPoint_line_eq b _ _ hp'

private theorem exists_line_of_point (b : Basis ι k W) [Module.Finite k W]
    (p : Points (coordinateProjectiveSpace k ι) R) : ∃ L, IsLineOfPoint b p L := by
  obtain ⟨J, inst, r, i, a, hr, hp⟩ := point_has_principal_chart_cover p
  let L (j : J) := chartLine b (i j) (a j)
  have hL (j j' : J) (T : TestAlgebra k) (f : awayAlgebra (r j) ⟶ T)
      (g : awayAlgebra (r j') ⟶ T) (h : awayHom (r j) ≫ f = awayHom (r j') ≫ g) :
      affineLineBaseChange f (L j) = affineLineBaseChange g (L j') := by
    dsimp only [L]
    rw [chartLine_baseChange, chartLine_baseChange]
    apply chartPoint_line_eq b
    rw [← chartPoint_baseChange, ← chartPoint_baseChange, ← hp, ← hp,
      mapPoints_comp', mapPoints_comp', h]
  let N := gluedSubmodule r L
  have hloc (j : J) : awaySubmodule (r j) N = (L j).submodule :=
    localized_gluedSubmodule r L hL j
  have hex (x : Set.range r) : ∃ A : AffineLine k W (awayAlgebra x.val),
      awaySubmodule x.val N = A.submodule := by
    obtain ⟨u, ⟨j, rfl⟩⟩ := x
    exact ⟨L j, hloc j⟩
  choose K hK using hex
  obtain ⟨M, hM⟩ := line_of_localizations (Set.range r) hr N K hK
  refine ⟨M, isLineOfPoint_of_cover b p M r hr i a hp fun j => ?_⟩
  apply affineLine_ext
  simpa only [affineLineBaseChange_submodule, hM, ← awaySubmodule_eq_changeLineSubmodule]
    using hloc j

private theorem exists_point_of_line (b : Basis ι k W) (L : AffineLine k W R) :
    ∃ p, IsLineOfPoint b p L := by
  let J := ι × L.submodule
  let r (j : J) := (b.baseChange R).coord j.1 j.2.val
  have hr : Ideal.span (Set.range r) = ⊤ := lineCoordinates_span_top b L
  let i (j : J) := j.1
  let M (j : J) := affineLineBaseChange (awayHom (r j)) L
  let a (j : J) := (affinePivotCoordinates k ι W b (i j) (awayAlgebra (r j))).choose.symm
    ⟨M j, linePivot_away b j.1 L j.2⟩
  have ha (j : J) : chartLine b (i j) (a j) = M j :=
    congrArg Subtype.val ((affinePivotCoordinates k ι W b (i j) (awayAlgebra (r j))).choose.apply_symm_apply _)
  let p (j : J) := chartPoint (i j) (a j)
  obtain ⟨q, hq⟩ := gluePrincipalPoints r hr p (fun j j' T f g hf => by
    dsimp only [p]
    rw [chartPoint_baseChange, chartPoint_baseChange]
    apply (chartPoint_eq_iff b _ _).mpr
    rw [← chartLine_baseChange, ← chartLine_baseChange, ha, ha]
    change affineLineBaseChange f (affineLineBaseChange (awayHom (r j)) L) =
      affineLineBaseChange g (affineLineBaseChange (awayHom (r j')) L)
    rw [← affineLineBaseChange_comp, ← affineLineBaseChange_comp, hf])
  exact ⟨q, isLineOfPoint_of_cover b q L r hr i a hq fun j => (ha j).symm⟩

private theorem line_of_point_unique (b : Basis ι k W) {p : Points (coordinateProjectiveSpace k ι) R}
    {L M : AffineLine k W R} (hL : IsLineOfPoint b p L) (hM : IsLineOfPoint b p M) : L = M := by
  obtain ⟨J, _, r, i, a, hr, hp⟩ := point_has_principal_chart_cover p
  exact affineLines_ext_principal r hr fun j =>
    (hL _ _ _ _ (hp j)).trans (hM _ _ _ _ (hp j)).symm

private theorem point_of_line_unique (b : Basis ι k W) {p q : Points (coordinateProjectiveSpace k ι) R}
    {L : AffineLine k W R} (hp : IsLineOfPoint b p L) (hq : IsLineOfPoint b q L) : p = q := by
  obtain ⟨J, _, r, i, a, hr, ha⟩ := point_has_principal_chart_cover p
  apply affinePoints_ext_principal r hr
  intro j
  obtain ⟨K, _, s, l, c, hs, hc⟩ := point_has_principal_chart_cover (mapPoints (awayHom (r j)) q)
  apply affinePoints_ext_principal s hs
  intro t
  rw [hc, ha, chartPoint_baseChange]
  apply (chartPoint_eq_iff b _ _).mpr
  have h1 := hp _ (awayHom (r j) ≫ awayHom (s t)) (i j) ((awayHom (s t)).hom.comp (a j)) (by
    rw [← mapPoints_comp', ha, chartPoint_baseChange])
  have h2 := hq _ (awayHom (r j) ≫ awayHom (s t)) (l t) (c t) (by rw [← mapPoints_comp', hc])
  exact h1.symm.trans h2

section

variable [Module.Finite k W]

private def affinePointEquiv (b : Basis ι k W) (R : TestAlgebra k) :
    Points (coordinateProjectiveSpace k ι) R ≃ AffineLine k W R where
  toFun p := (exists_line_of_point b p).choose
  invFun L := (exists_point_of_line b L).choose
  left_inv p := point_of_line_unique b
    (exists_point_of_line b ((exists_line_of_point b p).choose)).choose_spec
    (exists_line_of_point b p).choose_spec
  right_inv L := line_of_point_unique b
    (exists_line_of_point b ((exists_point_of_line b L).choose)).choose_spec
    (exists_point_of_line b L).choose_spec

private theorem affinePointEquiv_spec (b : Basis ι k W)
    (p : Points (coordinateProjectiveSpace k ι) R) :
    IsLineOfPoint b p (affinePointEquiv b R p) :=
  (exists_line_of_point b p).choose_spec

private theorem affinePointEquiv_chartPoint (b : Basis ι k W) (i : ι)
    (a : chartRing k ι i →ₐ[k] R) :
    affinePointEquiv b R (chartPoint i a) = chartLine b i a := by
  have h : mapPoints (𝟙 R) (chartPoint i a) = chartPoint i a := by simp [mapPoints]
  simpa only [affineLineBaseChange_id] using affinePointEquiv_spec b (chartPoint i a) R (𝟙 R) i a h

private theorem affinePointEquiv_natural (b : Basis ι k W) {T : TestAlgebra k}
    (f : R ⟶ T) (p : Points (coordinateProjectiveSpace k ι) R) :
    affinePointEquiv b T (mapPoints f p) = affineLineBaseChange f (affinePointEquiv b R p) := by
  apply line_of_point_unique b (affinePointEquiv_spec b _)
  intro U g j a h
  rw [← affineLineBaseChange_comp]
  exact affinePointEquiv_spec b p U (f ≫ g) j a ((mapPoints_comp' f g p).symm ▸ h)

end

end AffineRepresentation

section LineRepresentation

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]

omit [Module.Finite k W] in
private theorem lineFamily_ext {S : SchemeOver k} {L M : LineFamily k W S}
    (h : ∀ (R : TestAlgebra k) (a : Points S R), L.line R a = M.line R a) : L = M := by
  cases L
  cases M
  congr
  exact funext (fun R => funext (h R))

private def lineFamilyOfHom {ι : Type u} [Finite ι] (b : Basis ι k W) (S : SchemeOver k)
    (f : S ⟶ coordinateProjectiveSpace k ι) : LineFamily k W S where
  line R a := affinePointEquiv b R (a ≫ f)
  compatible g a := by
    rw [show mapPoints g a ≫ f = mapPoints g (a ≫ f) from Category.assoc _ _ _,
      affinePointEquiv_natural, affineLineBaseChange_submodule]

private def lineFamilyEquiv {ι : Type u} [Finite ι] (b : Basis ι k W) (S : SchemeOver k) :
    (S ⟶ coordinateProjectiveSpace k ι) ≃ LineFamily k W S :=
  Equiv.ofBijective (lineFamilyOfHom b S) (by
    constructor
    · intro f g h
      apply overHom_ext_affine f g
      intro R a
      exact (affinePointEquiv b R).injective (congrArg (fun L : LineFamily k W S => L.line R a) h)
    · intro L
      let m (R : TestAlgebra k) (p : Points S R) := (affinePointEquiv b R).symm (L.line R p)
      have hm {R T : TestAlgebra k} (g : R ⟶ T) (p : Points S R) :
          m T (mapPoints g p) = mapPoints g (m R p) := by
        apply (affinePointEquiv b T).injective
        rw [affinePointEquiv_natural]
        simp only [m, Equiv.apply_symm_apply]
        apply affineLine_ext
        rw [L.compatible, affineLineBaseChange_submodule]
      obtain ⟨f, hf⟩ := exists_of_affineTests m hm
      refine ⟨f, lineFamily_ext fun R p => ?_⟩
      change affinePointEquiv b R (p ≫ f) = _
      rw [hf, Equiv.apply_symm_apply])

private def projectiveBasis (k W : Type u) [Field k] [AddCommGroup W] [Module k W]
    [Module.Finite k W] : Basis (ULift.{u} (Fin (Module.finrank k W))) k W :=
  (Module.finBasis k W).reindex Equiv.ulift.symm

/-- The projective space represents the cartesian functor of rank-one summands
on all affine test schemes over the base. -/
def lineRepresentation (k : Type u) [Field k] (W : Type u) [AddCommGroup W] [Module k W]
    [Module.Finite k W] : LineRepresentation k W where
  points S := lineFamilyEquiv (projectiveBasis k W) S
  naturality f p := lineFamily_ext fun R a =>
    congrArg (affinePointEquiv (projectiveBasis k W) R) (Category.assoc a f p).symm

private theorem iso_of_affineTests {S T : SchemeOver k}
    (m : ∀ R : TestAlgebra k, Points S R ≃ Points T R)
    (hm : ∀ {R R' : TestAlgebra k} (a : R ⟶ R') (p : Points S R),
      m R' (mapPoints a p) = mapPoints a (m R p)) :
    ∃ e : S ≅ T, ∀ (R : TestAlgebra k) (a : Points S R), a ≫ e.hom = m R a := by
  obtain ⟨f, hf⟩ := exists_of_affineTests (fun R => m R) hm
  have hsymm {R R' : TestAlgebra k} (a : R ⟶ R') (p : Points T R) :
      (m R').symm (mapPoints a p) = mapPoints a ((m R).symm p) := by
    apply (m R').injective
    rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := exists_of_affineTests (fun R => (m R).symm) hsymm
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply overHom_ext_affine
    intro R p
    rw [← Category.assoc, hg, hf, Equiv.symm_apply_apply, Category.comp_id]
  · apply overHom_ext_affine
    intro R p
    rw [← Category.assoc, hf, hg, Equiv.apply_symm_apply, Category.comp_id]

theorem basisPointFormula (k W : Type u) [Field k] [AddCommGroup W] [Module k W]
    [Module.Finite k W] : BasisPointFormula k W (lineRepresentation k W) := by
  intro ι _ b
  let B := projectiveBasis k W
  let m (R : TestAlgebra k) := (affinePointEquiv b R).trans (affinePointEquiv B R).symm
  have hm {R T : TestAlgebra k} (g : R ⟶ T) (p : Points (coordinateProjectiveSpace k ι) R) :
      m T (mapPoints g p) = mapPoints g (m R p) := by
    apply (affinePointEquiv B T).injective
    rw [affinePointEquiv_natural B]
    simp only [m, Equiv.trans_apply, Equiv.apply_symm_apply, affinePointEquiv_natural b]
  obtain ⟨e, he⟩ := iso_of_affineTests m hm
  refine ⟨e, fun i R a => ?_⟩
  change (affinePointEquiv B R (𝟙 _ ≫
    ((testSpec k).map (CommAlgCat.ofHom a).op ≫ chartMorphism i ≫ e.hom))).submodule = _
  rw [Category.id_comp, ← Category.assoc]
  change (affinePointEquiv B R (chartPoint i a ≫ e.hom)).submodule = _
  rw [he]
  simp only [m, Equiv.trans_apply, Equiv.apply_symm_apply, affinePointEquiv_chartPoint]
  exact chartLine_span b i a

end LineRepresentation

section LinearTransport

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W]

private def lineTransport {R : TestAlgebra k} (g : W ≃ₗ[k] W) (L : AffineLine k W R) :
    AffineLine k W R := by
  let B := g.baseChange k R W W
  let := L.finite
  let := L.projective
  refine lineOfSplitInjection (B.toLinearMap.comp L.submodule.subtype)
    ((lineRetraction L).comp B.symm.toLinearMap) ?_ L.rank_one
  apply LinearMap.ext
  intro x
  change lineRetraction L (B.symm (B x.val)) = x
  rw [B.symm_apply_apply]
  exact DFunLike.congr_fun (lineRetraction_comp_subtype L) x

@[simp]
private theorem lineTransport_submodule {R : TestAlgebra k}
    (g : W ≃ₗ[k] W) (L : AffineLine k W R) :
    (lineTransport g L).submodule = L.submodule.map (g.baseChange k R W W).toLinearMap := by
  change (((g.baseChange k R W W).toLinearMap).comp L.submodule.subtype).range = _
  rw [LinearMap.range_comp, Submodule.range_subtype]

private theorem lineTransport_id {R : TestAlgebra k} (L : AffineLine k W R) :
    lineTransport (LinearEquiv.refl k W) L = L := by
  apply affineLine_ext
  rw [lineTransport_submodule]
  have h : ((LinearEquiv.refl k W).baseChange k R W W).toLinearMap = LinearMap.id := by
    exact congrArg LinearEquiv.toLinearMap
      (LinearEquiv.baseChange_one (R := k) (A := (R : Type u)) (M := W))
  rw [h, Submodule.map_id]

private theorem lineTransport_trans {R : TestAlgebra k} (g h : W ≃ₗ[k] W)
    (L : AffineLine k W R) : lineTransport (g.trans h) L = lineTransport h (lineTransport g L) := by
  apply affineLine_ext
  simp only [lineTransport_submodule, LinearEquiv.baseChange_trans, LinearEquiv.coe_trans,
    Submodule.map_comp]

private theorem lineTransport_natural {R T : TestAlgebra k} (a : R ⟶ T)
    (g : W ≃ₗ[k] W) (L : AffineLine k W R) :
    affineLineBaseChange a (lineTransport g L) = lineTransport g (affineLineBaseChange a L) := by
  let B := g.baseChange k R W W
  let B' := g.baseChange k T W W
  have he (x : R ⊗[k] W) : extendVector a (B x) = B' (extendVector a x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r w =>
      change extendVector a ((g.baseChange k R W W) (r ⊗ₜ[k] w)) =
        (g.baseChange k T W W) (extendVector a (r ⊗ₜ[k] w))
      rw [LinearEquiv.baseChange_tmul, extendVector_tmul, extendVector_tmul, LinearEquiv.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  apply affineLine_ext
  simp only [affineLineBaseChange_submodule, lineTransport_submodule, changeLineSubmodule_eq_span,
    Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, (he v).symm⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, he v⟩

private def lineTransportEquiv (g : W ≃ₗ[k] W) (R : TestAlgebra k) :
    AffineLine k W R ≃ AffineLine k W R where
  toFun := lineTransport g
  invFun := lineTransport g.symm
  left_inv L := by rw [← lineTransport_trans, LinearEquiv.self_trans_symm, lineTransport_id]
  right_inv L := by rw [← lineTransport_trans, LinearEquiv.symm_trans_self, lineTransport_id]

variable [Module.Finite k W]

private theorem exists_projectiveTransport (g : W ≃ₗ[k] W) :
    ∃ e : projectiveSpace k W ≅ projectiveSpace k W, ∀ (R : TestAlgebra k) (p : Points _ R),
      affinePointEquiv (projectiveBasis k W) R (p ≫ e.hom) =
        lineTransport g (affinePointEquiv (projectiveBasis k W) R p) := by
  let B := projectiveBasis k W
  let m (R : TestAlgebra k) := (affinePointEquiv B R).trans
    ((lineTransportEquiv g R).trans (affinePointEquiv B R).symm)
  have hm {R T : TestAlgebra k} (a : R ⟶ T) (p : Points (projectiveSpace k W) R) :
      m T (mapPoints a p) = mapPoints a (m R p) := by
    apply (affinePointEquiv B T).injective
    rw [affinePointEquiv_natural B]
    simp only [m, Equiv.trans_apply, Equiv.apply_symm_apply, affinePointEquiv_natural B]
    exact (lineTransport_natural a g _).symm
  obtain ⟨e, he⟩ := iso_of_affineTests m hm
  exact ⟨e, fun R p => by rw [he]; exact (affinePointEquiv B R).apply_symm_apply _⟩

/-- A linear automorphism acts on the projective scheme by carrying each line to its image. -/
def projectiveTransport (k : Type u) [Field k] (W : Type u) [AddCommGroup W] [Module k W]
    [Module.Finite k W] (g : W ≃ₗ[k] W) : projectiveSpace k W ≅ projectiveSpace k W :=
  (exists_projectiveTransport g).choose

private theorem projectiveTransport_apply (g : W ≃ₗ[k] W) (R : TestAlgebra k) (p : Points _ R) :
    affinePointEquiv (projectiveBasis k W) R (p ≫ (projectiveTransport k W g).hom) =
      lineTransport g (affinePointEquiv (projectiveBasis k W) R p) :=
  (exists_projectiveTransport g).choose_spec R p

theorem automorphismPointFormula (k W : Type u) [Field k] [AddCommGroup W] [Module k W]
    [Module.Finite k W] :
    AutomorphismPointFormula k W (lineRepresentation k W) (projectiveTransport k W) := by
  refine ⟨?_, ?_, fun g S p R a => ?_⟩
  · apply Iso.ext
    apply overHom_ext_affine
    intro R a
    apply (affinePointEquiv (projectiveBasis k W) R).injective
    rw [projectiveTransport_apply, lineTransport_id, Iso.refl_hom, Category.comp_id]
  · intro g h
    apply Iso.ext
    apply overHom_ext_affine
    intro R a
    apply (affinePointEquiv (projectiveBasis k W) R).injective
    rw [Iso.trans_hom, ← Category.assoc, projectiveTransport_apply, projectiveTransport_apply,
      projectiveTransport_apply, lineTransport_trans]
  · change (affinePointEquiv (projectiveBasis k W) R
      (a ≫ p ≫ (projectiveTransport k W g).hom)).submodule = _
    rw [← Category.assoc, projectiveTransport_apply, lineTransport_submodule]
    rfl

end LinearTransport

theorem projectiveSpaceLineGeometry : ProjectiveSpaceLineGeometry.{u} := by
  intro k W _ _ _ _
  exact ⟨lineRepresentation k W, projectiveTransport k W, basisPointFormula k W,
    automorphismPointFormula k W⟩

section TensorLines

variable {k I : Type u} [Field k] [Finite I] (W : I → Type u)
variable [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)]

private def tensorBasis :
    Basis (∀ i, ULift.{u} (Fin (Module.finrank k (W i)))) k (tensorSpace (k := k) W) :=
  Basis.piTensorProduct (fun i => projectiveBasis k (W i))

private def tensorChangeEquiv (R : TestAlgebra k) :
    (⨂[R] i, R ⊗[k] W i) ≃ₗ[R] R ⊗[k] tensorSpace (k := k) W :=
  (Basis.piTensorProduct (fun i => (projectiveBasis k (W i)).baseChange R)).repr.trans
    ((tensorBasis W).baseChange R).repr.symm

private def tensorVector (R : TestAlgebra k) (v : ∀ i, R ⊗[k] W i) :
    R ⊗[k] tensorSpace (k := k) W :=
  tensorChangeEquiv W R (PiTensorProduct.tprod R v)

private theorem tensorVector_coord [Fintype I] (R : TestAlgebra k)
    (v : ∀ i, R ⊗[k] W i) (p : ∀ i, ULift.{u} (Fin (Module.finrank k (W i)))) :
    ((tensorBasis W).baseChange R).coord p (tensorVector W R v) =
      ∏ i, ((projectiveBasis k (W i)).baseChange R).coord (p i) (v i) := by
  simp only [tensorVector, tensorChangeEquiv, Basis.coord_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, Basis.piTensorProduct_repr_tprod_apply]

private theorem tensorVector_tmul [Fintype I] (R : TestAlgebra k)
    (r : I → R) (v : ∀ i, W i) :
    tensorVector W R (fun i => r i ⊗ₜ[k] v i) = (∏ i, r i) ⊗ₜ[k] PiTensorProduct.tprod k v := by
  apply ((tensorBasis W).baseChange R).ext_elem
  intro p
  change ((tensorBasis W).baseChange R).coord p (tensorVector W R _) = _
  rw [tensorVector_coord]
  simp only [Basis.coord_apply, tensorBasis, Basis.baseChange_repr_tmul, Algebra.smul_def,
    Basis.piTensorProduct_repr_tprod_apply, map_prod, Finset.prod_mul_distrib]

private theorem tensorVector_baseChange {R T : TestAlgebra k} (a : R ⟶ T) (v : ∀ i, R ⊗[k] W i) :
    extendVector a (tensorVector W R v) = tensorVector W T (fun i => extendVector a (v i)) := by
  let := Fintype.ofFinite I
  apply ((tensorBasis W).baseChange T).ext_elem
  intro p
  change ((tensorBasis W).baseChange T).coord p (extendVector a (tensorVector W R v)) =
    ((tensorBasis W).baseChange T).coord p (tensorVector W T _)
  simp only [extendVector_coord, tensorVector_coord, map_prod]

set_option maxHeartbeats 1000000 in
private theorem tensorVector_transport {R : TestAlgebra k} (g : ∀ i, W i ≃ₗ[k] W i)
    (v : ∀ i, R ⊗[k] W i) :
    ((PiTensorProduct.congr g).baseChange k R _ _) (tensorVector W R v) =
      tensorVector W R (fun i => (g i).baseChange k R _ _ (v i)) := by
  let := Fintype.ofFinite I
  let c := tensorChangeEquiv W R
  let e := (PiTensorProduct.congr g).baseChange k R _ _
  let f := PiTensorProduct.congr (fun i => (g i).baseChange k R _ _)
  have h : e.toLinearMap.comp c.toLinearMap = c.toLinearMap.comp f.toLinearMap := by
    apply (Basis.piTensorProduct (fun i => (projectiveBasis k (W i)).baseChange R)).ext
    intro p
    simp only [LinearMap.comp_apply, Basis.piTensorProduct_apply, Basis.baseChange_apply,
      LinearEquiv.coe_coe, f, PiTensorProduct.congr_tprod, LinearEquiv.baseChange_tmul]
    change e (tensorVector W R (fun i => (1 : R) ⊗ₜ[k] projectiveBasis k (W i) (p i))) =
      tensorVector W R (fun i => (1 : R) ⊗ₜ[k] g i (projectiveBasis k (W i) (p i)))
    simp only [tensorVector_tmul, Finset.prod_const_one, e, LinearEquiv.baseChange_tmul,
      PiTensorProduct.congr_tprod]
  have he := DFunLike.congr_fun h (PiTensorProduct.tprod R v)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, f, PiTensorProduct.congr_tprod,
    e, c, tensorVector] using he

private def tensorLineSubmodule (R : TestAlgebra k)
    (L : ∀ i, Submodule R (R ⊗[k] W i)) : Submodule R (R ⊗[k] tensorSpace (k := k) W) :=
  (LinearMap.range (PiTensorProduct.mapIncl L)).map (tensorChangeEquiv W R).toLinearMap

set_option maxHeartbeats 1000000 in
private theorem tensorLineSubmodule_eq_span {R : TestAlgebra k}
    (L : ∀ i, Submodule R (R ⊗[k] W i)) {J : I → Type u}
    (v : ∀ i, J i → R ⊗[k] W i) (h : ∀ i, Submodule.span R (Set.range (v i)) = L i) :
    tensorLineSubmodule W R L =
      Submodule.span R (Set.range (fun p : ∀ i, J i => tensorVector W R (fun i => v i (p i)))) := by
  let w (i : I) (a : J i) : L i :=
    ⟨v i a, by rw [← h i]; exact Submodule.subset_span (Set.mem_range_self a)⟩
  have hw (i : I) : Submodule.span R (Set.range (w i)) = ⊤ := by
    apply (Submodule.map_injective_of_injective (L i).subtype_injective)
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact h i
  let f : (⨂[R] i, L i) →ₗ[R] R ⊗[k] tensorSpace (k := k) W :=
    (tensorChangeEquiv W R).toLinearMap.comp (PiTensorProduct.mapIncl L)
  let v₀ (p : ∀ i, J i) : ⨂[R] i, L i := PiTensorProduct.tprod R (fun i => w i (p i))
  have hg : Submodule.span R (Set.range v₀) = ⊤ :=
    PiTensorProduct.submodule_span_eq_top (g := w) hw
  have hf (p : ∀ i, J i) : f (v₀ p) = tensorVector W R (fun i => v i (p i)) := by
    change (tensorChangeEquiv W R) ((PiTensorProduct.mapIncl L) (PiTensorProduct.tprod R _)) = _
    rw [PiTensorProduct.mapIncl, PiTensorProduct.map_tprod]
    rfl
  calc
    tensorLineSubmodule W R L = f.range := (LinearMap.range_comp _ _).symm
    _ = (⊤ : Submodule R (⨂[R] i, L i)).map f := (Submodule.map_top f).symm
    _ = (Submodule.span R (Set.range v₀)).map f := congrArg (Submodule.map f) hg.symm
    _ = Submodule.span R (Set.range (fun p : ∀ i, J i => tensorVector W R (fun i => v i (p i)))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      exact congrArg (fun z : (∀ i, J i) → _ => Submodule.span R (Set.range z)) (funext hf)

private theorem tensorLineSubmodule_baseChange {R T : TestAlgebra k} (a : R ⟶ T)
    (L : ∀ i, Submodule R (R ⊗[k] W i)) :
    changeLineSubmodule k (tensorSpace (k := k) W) a (tensorLineSubmodule W R L) =
      tensorLineSubmodule W T (fun i => changeLineSubmodule k (W i) a (L i)) := by
  let v (i : I) (x : L i) := x.val
  have hv (i : I) : Submodule.span R (Set.range (v i)) = L i := by
    change Submodule.span R (Set.range (Subtype.val : L i → R ⊗[k] W i)) = L i
    rw [Subtype.range_val, Submodule.span_eq]
  have he (i : I) : Submodule.span T (Set.range (fun x : L i => extendVector a (v i x))) =
      changeLineSubmodule k (W i) a (L i) := by
    rw [changeLineSubmodule_eq_span, show (fun x : L i => extendVector a (v i x)) =
      extendVector a ∘ v i from rfl, Set.range_comp]
    change Submodule.span T (extendVector a '' Set.range (Subtype.val : L i → R ⊗[k] W i)) = _
    rw [Subtype.range_val]
  rw [tensorLineSubmodule_eq_span W L v hv, changeLineSubmodule_span,
    tensorLineSubmodule_eq_span W _ (fun i x => extendVector a (v i x)) he]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext p
  exact tensorVector_baseChange W a _

private theorem tensorLineSubmodule_singleton (R : TestAlgebra k) (v : ∀ i, R ⊗[k] W i) :
    tensorLineSubmodule W R (fun i => Submodule.span R {v i}) =
      Submodule.span R {tensorVector W R v} := by
  let w (i : I) (_ : PUnit.{u + 1}) := v i
  have hconst : Set.range (fun _ : (∀ _ : I, PUnit.{u + 1}) => tensorVector W R v) =
      {tensorVector W R v} := Set.range_const
  rw [tensorLineSubmodule_eq_span W _ w (fun i => by simp [w])]
  exact congrArg (Submodule.span R) hconst

private abbrev IsPivot {ι V : Type u} [AddCommGroup V] [Module k V] (b : Basis ι k V)
    (i : ι) {R : TestAlgebra k} (L : AffineLine k V R) : Prop :=
  Function.Bijective ((b.baseChange R).coord i ∘ L.submodule.subtype)

private theorem exists_common_pivot_cover {R : TestAlgebra k}
    (L : ∀ i, AffineLine k (W i) R) :
    ∃ (J : Type u) (r : J → R) (p : ∀ _ : J, ∀ i, ULift.{u} (Fin (Module.finrank k (W i)))),
      Ideal.span (Set.range r) = ⊤ ∧
        ∀ j i, IsPivot (projectiveBasis k (W i)) (p j i) (affineLineBaseChange (awayHom (r j)) (L i)) := by
  classical
  let := Fintype.ofFinite I
  let J := ∀ i, ULift.{u} (Fin (Module.finrank k (W i))) × (L i).submodule
  let c (j : J) (i : I) := ((projectiveBasis k (W i)).baseChange R).coord (j i).1 (j i).2.val
  let r (j : J) := ∏ i, c j i
  have hr : Ideal.span (Set.range r) = ⊤ := by
    by_contra hh
    obtain ⟨m, hm, hm'⟩ := (Ideal.span (Set.range r)).exists_le_maximal hh
    have H (i : I) : ∃ v : ULift.{u} (Fin (Module.finrank k (W i))) × (L i).submodule,
        ((projectiveBasis k (W i)).baseChange R).coord v.1 v.2.val ∉ m := by
      by_contra! h
      exact hm.ne_top (top_unique ((lineCoordinates_span_top (projectiveBasis k (W i)) (L i)) ▸
        Ideal.span_le.mpr (Set.range_subset_iff.mpr h)))
    choose j hj using H
    have hmem : ∏ i, c j i ∈ m := hm' (Ideal.subset_span (Set.mem_range_self j))
    have hn (s : Finset I) : (∏ i ∈ s, c j i) ∉ m := by
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty] using hm.isPrime.one_notMem
      | insert i s hi ih =>
        rw [Finset.prod_insert hi]
        exact fun h => (hm.isPrime.mem_or_mem' h).elim (hj i) ih
    exact hn Finset.univ hmem
  refine ⟨J, r, fun j i => (j i).1, hr, fun j i => ?_⟩
  let a := awayHom (r j)
  let v := extendVector a (j i).2.val
  have hv : v ∈ (affineLineBaseChange a (L i)).submodule := by
    rw [affineLineBaseChange_submodule]
    exact extendVector_mem_changeLineSubmodule a (j i).2.property
  apply pivot_of_unit_coord _ _ _ ⟨v, hv⟩
  change IsUnit (((projectiveBasis k (W i)).baseChange (awayAlgebra (r j))).coord (j i).1
    (extendVector a (j i).2.val))
  rw [extendVector_coord]
  have hunit : IsUnit (∏ n, a.hom (c j n)) := by
    rw [← map_prod]
    exact IsLocalization.Away.algebraMap_isUnit (r j)
  exact (IsUnit.prod_univ_iff.mp hunit) i

private theorem tensorLine_exists {R : TestAlgebra k} (L : ∀ i, AffineLine k (W i) R) :
    ∃ M : AffineLine k (tensorSpace (k := k) W) R,
      M.submodule = tensorLineSubmodule W R (fun i => (L i).submodule) := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨J, r, p, hr, hP⟩ := exists_common_pivot_cover W L
  let N := tensorLineSubmodule W R (fun i => (L i).submodule)
  have h (x : Set.range r) : ∃ M : AffineLine k (tensorSpace (k := k) W) (awayAlgebra x.val),
      awaySubmodule x.val N = M.submodule := by
    obtain ⟨z, ⟨j, rfl⟩⟩ := x
    let T := awayAlgebra (r j)
    let A (i : I) : AffinePivotLine k (projectiveBasis k (W i)) (p j i) T :=
      ⟨affineLineBaseChange (awayHom (r j)) (L i), hP j i⟩
    choose v hv1 hv2 using fun i => line_span_of_pivot _ _ (A i)
    have hv : ((tensorBasis W).baseChange T).coord (p j) (tensorVector W T v) = 1 := by
      rw [tensorVector_coord]
      simp only [hv1, Finset.prod_const_one]
    let M := (normalizedLine k (tensorBasis W) (p j) T ⟨tensorVector W T v, hv⟩).val
    refine ⟨M, ?_⟩
    rw [awaySubmodule_eq_changeLineSubmodule]
    change changeLineSubmodule k _ (awayHom (r j)) (tensorLineSubmodule W R _) = _
    rw [tensorLineSubmodule_baseChange]
    simp only [← affineLineBaseChange_submodule, ← show ∀ i, (A i).val.submodule =
        (affineLineBaseChange (awayHom (r j)) (L i)).submodule from fun _ => rfl, hv2,
      M, normalizedLine_span]
    exact tensorLineSubmodule_singleton W T v
  choose M hM using h
  exact line_of_localizations (Set.range r) hr N M hM

private def tensorLine {R : TestAlgebra k} (L : ∀ i, AffineLine k (W i) R) :
    AffineLine k (tensorSpace (k := k) W) R :=
  (tensorLine_exists W L).choose

private theorem tensorLine_submodule {R : TestAlgebra k} (L : ∀ i, AffineLine k (W i) R) :
    (tensorLine W L).submodule = tensorLineSubmodule W R (fun i => (L i).submodule) :=
  (tensorLine_exists W L).choose_spec

private theorem tensorLine_baseChange {R T : TestAlgebra k} (a : R ⟶ T)
    (L : ∀ i, AffineLine k (W i) R) :
    affineLineBaseChange a (tensorLine W L) = tensorLine W (fun i => affineLineBaseChange a (L i)) := by
  apply affineLine_ext
  simp only [affineLineBaseChange_submodule, tensorLine_submodule, tensorLineSubmodule_baseChange]

private theorem tensorLine_transport {R : TestAlgebra k} (g : ∀ i, W i ≃ₗ[k] W i)
    (L : ∀ i, AffineLine k (W i) R) :
    lineTransport (PiTensorProduct.congr g) (tensorLine W L) =
      tensorLine W (fun i => lineTransport (g i) (L i)) := by
  let v (i : I) (x : (L i).submodule) := x.val
  let w (i : I) (x : (L i).submodule) := (g i).baseChange k R _ _ (v i x)
  have hv (i : I) : Submodule.span R (Set.range (v i)) = (L i).submodule := by
    change Submodule.span R (Set.range (Subtype.val : (L i).submodule → _)) = _
    rw [Subtype.range_val, Submodule.span_eq]
  have hw (i : I) : Submodule.span R (Set.range (w i)) = (lineTransport (g i) (L i)).submodule := by
    rw [lineTransport_submodule]
    conv_rhs => rw [← hv i, Submodule.map_span]
    change Submodule.span R (Set.range (⇑((g i).baseChange k R _ _) ∘ v i)) = _
    rw [Set.range_comp]
    rfl
  apply affineLine_ext
  rw [lineTransport_submodule, tensorLine_submodule, tensorLine_submodule,
    tensorLineSubmodule_eq_span W _ v hv, tensorLineSubmodule_eq_span W _ w hw,
    Submodule.map_span, ← Set.range_comp]
  exact congrArg (fun z : (∀ i, (L i).submodule) → R ⊗[k] tensorSpace (k := k) W =>
    Submodule.span R (Set.range z)) (funext fun x => tensorVector_transport W g (fun i => v i (x i)))

private theorem input_pivot_of_tensor_pivot {R : TestAlgebra k} (L : ∀ i, AffineLine k (W i) R)
    (p : ∀ i, ULift.{u} (Fin (Module.finrank k (W i))))
    (h : IsPivot (tensorBasis W) p (tensorLine W L)) (i : I) :
    IsPivot (projectiveBasis k (W i)) (p i) (L i) := by
  classical
  let := Fintype.ofFinite I
  let f := ((projectiveBasis k (W i)).baseChange R).coord (p i)
  let P := (f.comp (L i).submodule.subtype).range
  let q := ((tensorBasis W).baseChange R).coord p
  have hP : (tensorLine W L).submodule ≤ P.comap q := by
    let v (j : I) (x : (L j).submodule) := x.val
    have hv (j : I) : Submodule.span R (Set.range (v j)) = (L j).submodule := by
      change Submodule.span R (Set.range (Subtype.val : (L j).submodule → _)) = _
      rw [Subtype.range_val, Submodule.span_eq]
    rw [tensorLine_submodule, tensorLineSubmodule_eq_span W _ v hv, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    let c (j : I) := ((projectiveBasis k (W j)).baseChange R).coord (p j) (v j (w j))
    change q (tensorVector W R (fun j => v j (w j))) ∈ P
    rw [show q (tensorVector W R (fun j => v j (w j))) = ∏ j, c j from tensorVector_coord W R _ p]
    rw [← Finset.prod_erase_mul _ c (Finset.mem_univ i)]
    exact P.smul_mem _ ⟨w i, rfl⟩
  apply lineCoord_bijective_of_surjective
  intro a
  obtain ⟨x, hx⟩ := h.2 a
  have hx' : q x.val = a := hx
  have ha : q x.val ∈ P := hP x.property
  rw [hx'] at ha
  exact ha

private theorem tensorVector_update_coord [Fintype I] {R : TestAlgebra k}
    (p : ∀ i, ULift.{u} (Fin (Module.finrank k (W i)))) (v : ∀ i, R ⊗[k] W i)
    (h : ∀ i, ((projectiveBasis k (W i)).baseChange R).coord (p i) (v i) = 1)
    [DecidableEq I] (i : I) (j : ULift.{u} (Fin (Module.finrank k (W i)))) :
    ((tensorBasis W).baseChange R).coord (Function.update p i j) (tensorVector W R v) =
      ((projectiveBasis k (W i)).baseChange R).coord j (v i) := by
  rw [tensorVector_coord, Finset.prod_eq_single i]
  · rw [Function.update_self]
  · intro l _ hl
    rw [Function.update_of_ne hl, h]
  · simp

private theorem tensorLine_injective_of_pivot {R : TestAlgebra k}
    (L M : ∀ i, AffineLine k (W i) R)
    (p : ∀ i, ULift.{u} (Fin (Module.finrank k (W i))))
    (hL : ∀ i, IsPivot (projectiveBasis k (W i)) (p i) (L i))
    (h : tensorLine W L = tensorLine W M) :
    L = M := by
  classical
  let := Fintype.ofFinite I
  choose v hv1 hv2 using fun i => line_span_of_pivot (projectiveBasis k (W i)) (p i)
    (⟨L i, hL i⟩ : AffinePivotLine k (projectiveBasis k (W i)) (p i) R)
  change ∀ i, (L i).submodule = Submodule.span R {v i} at hv2
  have hspan : (tensorLine W L).submodule = Submodule.span R {tensorVector W R v} := by
    rw [tensorLine_submodule, funext hv2, tensorLineSubmodule_singleton]
  have hv : ((tensorBasis W).baseChange R).coord p (tensorVector W R v) = 1 := by
    rw [tensorVector_coord]
    simp only [hv1, Finset.prod_const_one]
  have hp : IsPivot (tensorBasis W) p (tensorLine W L) := by
    apply lineCoord_bijective_of_one _ _ _
      ⟨tensorVector W R v, hspan.symm ▸ Submodule.mem_span_singleton_self _⟩
    exact hv
  have hM := input_pivot_of_tensor_pivot W M p (h ▸ hp)
  choose w hw1 hw2 using fun i => line_span_of_pivot (projectiveBasis k (W i)) (p i)
    (⟨M i, hM i⟩ : AffinePivotLine k (projectiveBasis k (W i)) (p i) R)
  change ∀ i, (M i).submodule = Submodule.span R {w i} at hw2
  have hspan' : (tensorLine W M).submodule = Submodule.span R {tensorVector W R w} := by
    rw [tensorLine_submodule, funext hw2, tensorLineSubmodule_singleton]
  have hw : ((tensorBasis W).baseChange R).coord p (tensorVector W R w) = 1 := by
    rw [tensorVector_coord]
    simp only [hw1, Finset.prod_const_one]
  have he : tensorVector W R v = tensorVector W R w := by
    have hmem : tensorVector W R v ∈ Submodule.span R {tensorVector W R w} := by
      rw [← hspan', ← h, hspan]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := congrArg (((tensorBasis W).baseChange R).coord p) hc
    rw [map_smul, hv, hw, smul_eq_mul, mul_one] at h1
    simpa only [h1, one_smul] using hc.symm
  funext i
  apply affineLine_ext
  rw [hv2, hw2]
  congr 2
  apply ((projectiveBasis k (W i)).baseChange R).ext_elem
  intro j
  exact (tensorVector_update_coord W p v hv1 i j).symm.trans
    ((congrArg (((tensorBasis W).baseChange R).coord (Function.update p i j)) he).trans
      (tensorVector_update_coord W p w hw1 i j))

private theorem tensorLine_injective {R : TestAlgebra k} :
    Function.Injective (tensorLine W (R := R)) := by
  intro L M h
  obtain ⟨J, r, p, hr, hp⟩ := exists_common_pivot_cover W L
  funext i
  apply affineLines_ext_principal r hr
  intro j
  have hh := congrArg (affineLineBaseChange (awayHom (r j))) h
  rw [tensorLine_baseChange, tensorLine_baseChange] at hh
  exact congrFun (tensorLine_injective_of_pivot W _ _ (p j) (hp j) hh) i

end TensorLines

section ProperProducts

variable {k : Type u} [Field k]

private theorem proper_of_overIso {X Y : SchemeOver k} (e : X ≅ Y)
    (h : IsProper Y.hom) : IsProper X.hom := by
  rw [← Over.w e.hom]
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of k))).map e.hom))
  infer_instance

private theorem binaryProduct_proper (X Y : SchemeOver k) (hX : IsProper X.hom)
    (hY : IsProper Y.hom) : IsProper (X ⨯ Y).hom := by
  rw [← Over.w (prod.fst (X := X) (Y := Y)), ← Over.prodLeftIsoPullback_hom_fst, Category.assoc]
  infer_instance

private theorem product_proper {I : Type u} [Finite I] (X : I → SchemeOver k)
    (h : ∀ i, IsProper (X i).hom) : IsProper (∏ᶜ X).hom := by
  let P (J : Type u) := ∀ [Finite J], ∀ (Y : J → SchemeOver k),
    (∀ j, IsProper (Y j).hom) → IsProper (∏ᶜ Y).hom
  have hP : P I := by
    refine Finite.induction_empty_option (P := P) ?_ ?_ ?_ I
    · intro A B e ih _ Y hY
      have : Finite A := Finite.of_equiv B e.symm
      let X' (a : A) := Y (e a)
      let E : (∏ᶜ X') ≅ ∏ᶜ Y := Pi.whiskerEquiv e (fun _ => Iso.refl _)
      exact proper_of_overIso E.symm (ih X' (fun a => hY (e a)))
    · intro _ Y _
      let U := Over.mk (𝟙 (Spec (CommRingCat.of k)))
      have hU : IsTerminal U :=
        IsTerminal.ofUniqueHom (fun S => Over.homMk S.hom) (fun S f =>
          Over.OverMorphism.ext ((Category.comp_id _).symm.trans (Over.w f)))
      have hprod : IsTerminal (∏ᶜ Y) :=
        IsTerminal.ofUniqueHom (fun _ => Pi.lift (fun j => isEmptyElim j))
          (fun _ _ => Pi.hom_ext _ _ (fun j => isEmptyElim j))
      exact proper_of_overIso (hprod.uniqueUpToIso hU) (by change IsProper (𝟙 _); infer_instance)
    · intro A _ ih _ Y hY
      let Y' (a : A) := Y (some a)
      let c : BinaryFan (Y none) (∏ᶜ Y') :=
        BinaryFan.mk (P := ∏ᶜ Y) (Pi.π Y none) (Pi.lift fun a => Pi.π Y (some a))
      have hc : IsLimit c := by
        apply BinaryFan.isLimitMk (fun s => Pi.lift fun j => Option.casesOn j s.fst
          (fun a => s.snd ≫ Pi.π Y' a))
        · intro s
          simp
        · intro s
          apply Pi.hom_ext
          intro a
          simp [Category.assoc]
        · intro s m h₁ h₂
          apply Pi.hom_ext
          intro j
          cases j with
          | none => simpa [c] using h₁
          | some a =>
            have hh := congrArg (· ≫ Pi.π Y' a) h₂
            simpa [c, Category.assoc] using hh
      let E := hc.conePointUniqueUpToIso (prodIsProd (Y none) (∏ᶜ Y'))
      exact proper_of_overIso E (binaryProduct_proper _ _ (hY none) (ih Y' (fun a => hY (some a))))
  exact hP X h

end ProperProducts

section SegreMorphism

variable {k I : Type u} [Field k] [Finite I] (W : I → Type u)
variable [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)]

private theorem exists_segre (W : I → Type u)
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)] :
    ∃ σ : projectiveProduct (k := k) W ⟶ projectiveSpace k (tensorSpace (k := k) W),
      ∀ (R : TestAlgebra k) (p : Points (projectiveProduct (k := k) W) R),
        affinePointEquiv (projectiveBasis k (tensorSpace (k := k) W)) R (p ≫ σ) =
          tensorLine W (fun i => affinePointEquiv (projectiveBasis k (W i)) R (p ≫ Pi.π _ i)) := by
  let E (R : TestAlgebra k) := affinePointEquiv (projectiveBasis k (tensorSpace (k := k) W)) R
  let E' (R : TestAlgebra k) (i : I) := affinePointEquiv (projectiveBasis k (W i)) R
  let m (R : TestAlgebra k) (p : Points (projectiveProduct (k := k) W) R) :=
    (E R).symm (tensorLine W fun i => E' R i (p ≫ Pi.π _ i))
  have hm {R T : TestAlgebra k} (a : R ⟶ T) (p : Points (projectiveProduct (k := k) W) R) :
      m T (mapPoints a p) = mapPoints a (m R p) := by
    apply (E T).injective
    rw [show E T (mapPoints a (m R p)) = affineLineBaseChange a (E R (m R p)) from
      affinePointEquiv_natural _ _ _]
    simp only [m, Equiv.apply_symm_apply, tensorLine_baseChange]
    congr 1
    funext i
    rw [show mapPoints a p ≫ Pi.π _ i = mapPoints a (p ≫ Pi.π _ i) from Category.assoc _ _ _]
    exact affinePointEquiv_natural (projectiveBasis k (W i)) a _
  obtain ⟨σ, hσ⟩ := exists_of_affineTests m hm
  exact ⟨σ, fun R p => by rw [hσ]; exact (E R).apply_symm_apply _⟩

/-- The Segre map sends a family of lines to its tensor product. -/
def segreMorphism : projectiveProduct (k := k) W ⟶ projectiveSpace k (tensorSpace (k := k) W) :=
  (exists_segre (k := k) W).choose

private theorem segreMorphism_apply (R : TestAlgebra k) (p : Points (projectiveProduct (k := k) W) R) :
    affinePointEquiv (projectiveBasis k (tensorSpace (k := k) W)) R (p ≫ segreMorphism W) =
      tensorLine W (fun i => affinePointEquiv (projectiveBasis k (W i)) R (p ≫ Pi.π _ i)) :=
  (exists_segre (k := k) W).choose_spec R p

theorem segrePointFormula :
    SegrePointFormula W (fun i => lineRepresentation k (W i))
      (lineRepresentation k (tensorSpace (k := k) W)) (segreMorphism W) := by
  refine ⟨tensorChangeEquiv W, ?_, ?_⟩
  · intro R v
    let := Fintype.ofFinite I
    simpa only [Finset.prod_const_one, tensorVector] using tensorVector_tmul W R (fun _ => 1) v
  · intro S p R a
    change (affinePointEquiv (projectiveBasis k (tensorSpace (k := k) W)) R
      (a ≫ p ≫ segreMorphism W)).submodule = _
    rw [← Category.assoc, segreMorphism_apply, tensorLine_submodule]
    change tensorLineSubmodule W R _ = tensorLineSubmodule W R
      (fun i => (affinePointEquiv (projectiveBasis k (W i)) R (a ≫ p ≫ Pi.π _ i)).submodule)
    simp only [Category.assoc]

theorem segreEquivariance (g : ∀ i, W i ≃ₗ[k] W i) :
    Limits.Pi.map (fun i => (projectiveTransport k (W i) (g i)).hom) ≫ segreMorphism W =
      segreMorphism W ≫ (projectiveTransport k (tensorSpace (k := k) W)
        (PiTensorProduct.congr g)).hom := by
  apply overHom_ext_affine
  intro R p
  apply (affinePointEquiv (projectiveBasis k (tensorSpace (k := k) W)) R).injective
  simp only [← Category.assoc p, segreMorphism_apply, projectiveTransport_apply, tensorLine_transport]
  congr 1
  funext i
  rw [Category.assoc, Pi.map_π, ← Category.assoc, projectiveTransport_apply]

private theorem segreMorphism_mono : Mono (segreMorphism (k := k) W).left := by
  constructor
  intro S f g h
  let X := projectiveProduct (k := k) W
  let σ := segreMorphism (k := k) W
  have hw : g ≫ X.hom = f ≫ X.hom := by
    rw [← Over.w σ, ← Category.assoc, ← Category.assoc, h]
  let V := overAlong (S := X) f
  let f' : V ⟶ X := Over.homMk f rfl
  let g' : V ⟶ X := Over.homMk g hw
  have hm : f' ≫ σ = g' ≫ σ := Over.OverMorphism.ext h
  apply congrArg Over.Hom.left (a₁ := f') (a₂ := g')
  apply overHom_ext_affine
  intro R a
  have he : (a ≫ f') ≫ σ = (a ≫ g') ≫ σ := by rw [Category.assoc, Category.assoc, hm]
  have heq : affinePointEquiv (projectiveBasis k (tensorSpace (k := k) W)) R ((a ≫ f') ≫ σ) =
      affinePointEquiv (projectiveBasis k (tensorSpace (k := k) W)) R ((a ≫ g') ≫ σ) :=
    congrArg _ he
  rw [show σ = segreMorphism W from rfl, segreMorphism_apply, segreMorphism_apply] at heq
  have hprod := tensorLine_injective W heq
  exact Pi.hom_ext _ _ (fun i => (affinePointEquiv (projectiveBasis k (W i)) R).injective (congrFun hprod i))

theorem segreClosedImmersion : IsClosedImmersion (segreMorphism (k := k) W).left := by
  let σ := segreMorphism (k := k) W
  have hprod : IsProper (projectiveProduct (k := k) W).hom :=
    product_proper _ (fun i => projectiveSpaceProper k (W i))
  have : IsProper (σ.left ≫ (projectiveSpace k (tensorSpace (k := k) W)).hom) := Over.w σ ▸ hprod
  have : IsProper (projectiveSpace k (tensorSpace (k := k) W)).hom := projectiveSpaceProper k _
  exact (IsClosedImmersion.iff_isProper_and_mono (f := σ.left)).mpr
    ⟨IsProper.of_comp σ.left (projectiveSpace k (tensorSpace (k := k) W)).hom, segreMorphism_mono W⟩

/-- The Segre morphism for the empty family is the isomorphism between the two points. -/
theorem emptySegreMorphism [IsEmpty I] :
    IsIso (segreMorphism (k := k) W) ∧ Nonempty (tensorSpace (k := k) W ≃ₗ[k] k) := by
  obtain ⟨e, _, h⟩ := emptySegre k I W
  have hprod : IsTerminal (projectiveProduct (k := k) W) :=
    IsTerminal.ofUniqueHom (fun _ => Limits.Pi.lift (fun i => isEmptyElim i))
      (fun _ _ => Limits.Pi.hom_ext _ _ (fun i => isEmptyElim i))
  have htarget := hprod.ofIso e
  rw [htarget.hom_ext (segreMorphism W) e.hom]
  exact ⟨inferInstance, h⟩

end SegreMorphism

theorem projectiveSpaceSegreGeometry : ProjectiveSpaceSegreGeometry.{u} := by
  intro k _
  refine ⟨lineRepresentation k, projectiveTransport k, fun W _ _ _ =>
    ⟨basisPointFormula k W, automorphismPointFormula k W⟩, ?_⟩
  intro I _ W _ _ _
  exact ⟨segreMorphism W, segreClosedImmersion W, segrePointFormula W, segreEquivariance W,
    fun _ => emptySegreMorphism W⟩

section TildeBaseChange

open TopCat

private def affineSectionsPushforwardIso {A B : CommRingCat.{u}} (f : A ⟶ B) :
    Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor (R := A) ≅
      moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars f.hom := by
  let E := TopCat.Sheaf.forget (ModuleCat.{u} A) (Spec A) ⋙
    (evaluation _ _).obj (op ⊤)
  exact (Functor.associator _ _ E).symm ≪≫
    Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso f) E

/-- Pullback of the associated module sheaf on spectra is extension of scalars. -/
def tildeSpecPullback {A B : CommRingCat.{u}} (f : A ⟶ B) :
    tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor B :=
  Adjunction.leftAdjointUniq
    ((tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight
      (affineSectionsPushforwardIso f))
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp tilde.adjunction)

private def extendScalarsAlgebraIso (A B M : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] :
    (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A M) ≅
      ModuleCat.of B (B ⊗[A] M) := by
  let F (s : Algebra A B) : ModuleCat B := letI := s; ModuleCat.of B (B ⊗[A] M)
  change F (algebraMap A B).toAlgebra ≅ F inferInstance
  exact eqToIso (congrArg F toAlgebra_algebraMap)

private def tildeAlgebraMapPullback (A B M : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (tilde (ModuleCat.of A M)) ≅ tilde (ModuleCat.of B (B ⊗[A] M)) :=
  (tildeSpecPullback (CommRingCat.ofHom (algebraMap A B))).app (ModuleCat.of A M) ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso (extendScalarsAlgebraIso A B M)

variable (k W : Type u) [Field k] [AddCommGroup W] [Module k W]

/-- On an affine test the constant bundle is the sheaf associated to the scalar extension. -/
def affineConstantBundleIso (R : TestAlgebra k) :
    tilde (ModuleCat.of R (R ⊗[k] W)) ≅ constantBundle k W ((testSpec k).obj (op R)) :=
  (tildeAlgebraMapPullback k R W).symm

end TildeBaseChange

theorem affineConstantBundle : AffineConstantBundle.{u} := by
  intro k W _ _ _ R
  exact ⟨affineConstantBundleIso k W R⟩

section AffineLineSheaves

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
variable {R : TestAlgebra k}

private def tildeLineAwayUnit (L : AffineLine k W R) (r : R)
    (i : ULift.{u} (Fin (Module.finrank k W)))
    (h : IsPivot (projectiveBasis k W) i (affineLineBaseChange (awayHom r) L)) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj
      (tilde (ModuleCat.of R L.submodule)) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away r))).ringCatSheaf := by
  let B := Localization.Away r
  let N := awaySubmodule r L.submodule
  let L' := affineLineBaseChange (awayHom r) L
  have he : N = L'.submodule := by
    rw [affineLineBaseChange_submodule]
    exact awaySubmodule_eq_changeLineSubmodule r _
  let e := (IsLocalizedModule.isBaseChange (Submonoid.powers r) B
    (L.submodule.toLocalized' B (Submonoid.powers r) (scalarExtension k W R B))).equiv
  let q := ((projectiveBasis k W).baseChange B).coord i
  let d : L'.submodule ≃ₗ[B] B := LinearEquiv.ofBijective (q.comp L'.submodule.subtype) h
  let c : B ⊗[R] L.submodule ≃ₗ[B] B := e.trans ((LinearEquiv.ofEq N _ he).trans d)
  exact (tildeSpecPullback (CommRingCat.ofHom (algebraMap R B))).app (ModuleCat.of R L.submodule) ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (extendScalarsAlgebraIso R B L.submodule ≪≫ LinearEquiv.toModuleIso c) ≪≫ tildeSelf

private theorem tildeLine_locally_unit (L : AffineLine k W R) (x : PrimeSpectrum R) :
    ∃ U : (Spec (CommRingCat.of R)).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (tilde (ModuleCat.of R L.submodule)) ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  classical
  let b := projectiveBasis k W
  have hp : ∃ s : ULift.{u} (Fin (Module.finrank k W)) × L.submodule,
      (b.baseChange R).coord s.1 s.2.val ∉ x.asIdeal := by
    by_contra! h
    exact x.isPrime.ne_top (top_unique ((lineCoordinates_span_top b L) ▸
      Ideal.span_le.mpr (Set.range_subset_iff.mpr h)))
  obtain ⟨⟨i, v⟩, hv⟩ := hp
  let r := (b.baseChange R).coord i v.val
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen r
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  have : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have hU : Set.range j = Set.range U.ι :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).trans U.range_ι.symm
  let e := IsOpenImmersion.isoOfRangeEq j U.ι hU
  let M := tilde (R := CommRingCat.of R) (ModuleCat.of R L.submodule)
  have he : e.inv ≫ j = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hU
  have : IsOpenImmersion e.inv := inferInstance
  let u := tildeLineAwayUnit L r i (linePivot_away b i L v)
  refine ⟨U, hv, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackCongr he.symm).app M ≪≫
    (Scheme.Modules.pullbackComp e.inv j).symm.app M ≪≫
    (Scheme.Modules.pullback e.inv).mapIso u ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback e.inv).symm.app _ ≪≫
    Scheme.Modules.restrictUnitIso e.inv

private theorem exists_affineLineSheaf (L : AffineLine k W R) :
    let S := (testSpec k).obj (op R)
    ∃ M : LineSubbundle k W ((testSpec k).obj (op R)),
      ∃ d : tilde (ModuleCat.of R L.submodule) ≅ (M.val : S.left.Modules),
        (tilde.functor (CommRingCat.of R)).map (ModuleCat.ofHom L.submodule.subtype) ≫
          (affineConstantBundleIso k W R).hom = d.hom ≫ M.val.arrow := by
  let F := tilde.functor (CommRingCat.of R)
  let E : (Spec (CommRingCat.of R)).Modules := constantBundle k W ((testSpec k).obj (op R))
  let c : F.obj (ModuleCat.of R (R ⊗[k] W)) ≅ E := affineConstantBundleIso k W R
  let i : ModuleCat.of R L.submodule ⟶ ModuleCat.of R (R ⊗[k] W) :=
    ModuleCat.ofHom L.submodule.subtype
  let q : ModuleCat.of R (R ⊗[k] W) ⟶ ModuleCat.of R L.submodule :=
    ModuleCat.ofHom (lineRetraction L)
  let f := F.map i ≫ c.hom
  let g := c.inv ≫ F.map q
  have hgf : f ≫ g = 𝟙 _ := by
    have h : i ≫ q = 𝟙 (ModuleCat.of R L.submodule) :=
      ModuleCat.hom_ext (lineRetraction_comp_subtype L)
    calc
      f ≫ g = F.map i ≫ c.hom ≫ c.inv ≫ F.map q := Category.assoc _ _ _
      _ = F.map i ≫ F.map q := congrArg (F.map i ≫ ·) (Iso.hom_inv_id_assoc c _)
      _ = 𝟙 _ := by rw [← F.map_comp, h, F.map_id]
  have : Mono f := by
    constructor
    intro Z f₁ f₂ h
    calc
      f₁ = f₁ ≫ (f ≫ g) := by rw [hgf, Category.comp_id]
      _ = (f₁ ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = (f₂ ≫ f) ≫ g := congrArg (· ≫ g) h
      _ = f₂ ≫ (f ≫ g) := Category.assoc _ _ _
      _ = f₂ := by rw [hgf, Category.comp_id]
  let A := Subobject.mk f
  let d := (Subobject.underlyingIso f).symm
  have hd : d.hom ≫ A.arrow = f := Subobject.underlyingIso_arrow f
  let r := g ≫ d.hom
  have hr : A.arrow ≫ r = 𝟙 _ := by
    apply (cancel_epi d.hom).mp
    calc
      d.hom ≫ (A.arrow ≫ r) = (d.hom ≫ A.arrow) ≫ r := (Category.assoc _ _ _).symm
      _ = f ≫ (g ≫ d.hom) := congrArg (· ≫ r) hd
      _ = (f ≫ g) ≫ d.hom := (Category.assoc _ _ _).symm
      _ = d.hom ≫ 𝟙 _ := by rw [hgf, Category.comp_id, Category.id_comp]
  refine ⟨⟨A, ?_⟩, d, hd.symm⟩
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := tildeLine_locally_unit L x
  let P := Scheme.Modules.pullback U.ι
  refine ⟨U, hx, ⟨P.mapIso d.symm ≪≫ e⟩, P.map r, ?_⟩
  exact (P.map_comp A.arrow r).symm.trans ((congrArg (fun t => P.map t) hr).trans (P.map_id _))

end AffineLineSheaves

theorem affineLineSheafInclusion : AffineLineSheafInclusion.{u} := by
  intro k W _ _ _ _
  exact ⟨affineConstantBundleIso k W, fun _ L => exists_affineLineSheaf L⟩

private theorem extendScalarsAlgebraIso_naturality
    {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) :
    (ModuleCat.extendScalars (algebraMap A B)).map (ModuleCat.ofHom f) ≫
        (extendScalarsAlgebraIso A B N).hom =
      (extendScalarsAlgebraIso A B M).hom ≫ ModuleCat.ofHom (f.baseChange B) := by
  let F (a : Algebra A B) (V : Type u) [AddCommGroup V] [Module A V] : ModuleCat B :=
    letI := a
    ModuleCat.of B (B ⊗[A] V)
  let g (a : Algebra A B) : F a M ⟶ F a N :=
    letI := a
    ModuleCat.ofHom (f.baseChange B)
  have natural (a b : Algebra A B) (h : a = b) :
      g a ≫ eqToHom (congrArg (fun t => F t N) h) =
        eqToHom (congrArg (fun t => F t M) h) ≫ g b := by
    cases h
    simp
  exact natural _ _ toAlgebra_algebraMap


private theorem tildeAlgebraMapPullback_naturality
    {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
        ((tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f)) ≫
          (tildeAlgebraMapPullback A B N).hom =
      (tildeAlgebraMapPullback A B M).hom ≫
        (tilde.functor (CommRingCat.of B)).map (ModuleCat.ofHom (f.baseChange B)) := by
  let ψ := tildeSpecPullback (CommRingCat.ofHom (algebraMap A B))
  let F := tilde.functor (CommRingCat.of B)
  let G := tilde.functor (CommRingCat.of A) ⋙
    Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  let H := ModuleCat.extendScalars (algebraMap A B)
  let a : ModuleCat.of A M ⟶ ModuleCat.of A N := ModuleCat.ofHom f
  let b : ModuleCat.of B (B ⊗[A] M) ⟶ ModuleCat.of B (B ⊗[A] N) :=
    ModuleCat.ofHom (f.baseChange B)
  let u := (extendScalarsAlgebraIso A B M).hom
  let v := (extendScalarsAlgebraIso A B N).hom
  have huv : F.map (H.map a) ≫ F.map v = F.map u ≫ F.map b := by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg (fun t => F.map t) (extendScalarsAlgebraIso_naturality f)
  change G.map a ≫ (ψ.hom.app _ ≫ F.map v) = (ψ.hom.app _ ≫ F.map u) ≫ F.map b
  exact (NatTrans.naturality_assoc ψ.hom a _).trans
    ((congrArg (ψ.hom.app _ ≫ ·) huv).trans (Category.assoc _ _ _).symm)

private def pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let F := TopologicalSpace.Opens.map f.base
  let G := Functor.fromPUnit.{0} (⊤ : Y.Opens)
  letI : G.Final := Functor.final_fromPUnit_of_isTerminal Limits.isTerminalTop
  letI : (Functor.fromPUnit.{0} (⊤ : X.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal Limits.isTerminalTop
  letI : (G ⋙ F).Final := Functor.final_of_natIso
    (F := Functor.fromPUnit.{0} (⊤ : X.Opens)) (Discrete.natIso (fun _ => Iso.refl _))
  letI : (TopologicalSpace.Opens.map f.base).Final := Functor.final_of_final_comp G F
  let m := SheafOfModules.pullbackObjUnitToUnit.{u}
    (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom
  have hm : IsIso m := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
    (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom
  exact @asIso _ _ _ _ m hm

section LocallyTrivialSheaves

variable {X : Scheme.{u}} (M : X.Modules)

private def restrictionUnitOverIso (U : X.Opens) :
    (Scheme.Modules.overEquiv U).functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf := by
  let F := Scheme.Modules.overEquiv U
  change (SheafOfModules.overFunctor X.ringCatSheaf U ⋙ F.functor).obj
    (SheafOfModules.unit X.ringCatSheaf) ≅ _
  exact (Scheme.Modules.overFunctorEquiv U).app _ ≪≫ Scheme.Modules.restrictUnitIso U.ι

private def freeIsoLocalGenerators (U : X.Opens)
    (e : SheafOfModules.free.{u} (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) :
    (M.over U).GeneratingSections where
  I := PUnit.{u + 1}
  s := (M.over U).freeHomEquiv e.hom
  epi := by rw [Equiv.symm_apply_apply]; infer_instance

private theorem isIso_freeIsoLocalGenerators (U : X.Opens)
    (e : SheafOfModules.free.{u} (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) :
    IsIso (freeIsoLocalGenerators M U e).π := by
  change IsIso ((M.over U).freeHomEquiv.symm ((M.over U).freeHomEquiv e.hom))
  rw [Equiv.symm_apply_apply]
  infer_instance

private def freeIsoOfUnitPullback (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    SheafOfModules.free.{u} (R := X.ringCatSheaf.over U) PUnit ≅ M.over U := by
  let E := Scheme.Modules.overEquiv U
  let p : E.functor.obj (M.over U) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    (Scheme.Modules.overFunctorEquiv U).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e
  let a : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
    E.fullyFaithfulFunctor.preimageIso (p ≪≫ (restrictionUnitOverIso U).symm)
  exact coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit (X.ringCatSheaf.over U)) ≪≫ a.symm


private def coverWithFreeGenerator (U : X → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    (e : ∀ x : X, SheafOfModules.free.{u} (R := X.ringCatSheaf.over (U x)) PUnit ≅ M.over (U x)) :
    M.LocalGeneratorsData where
  I := X
  X := U
  coversTop := hU
  generators x := freeIsoLocalGenerators M (U x) (e x)

set_option backward.isDefEq.respectTransparency false in
private theorem coverWithFreeGenerator_isQuasicoherent (U : X → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (e : ∀ x : X, SheafOfModules.free.{u} (R := X.ringCatSheaf.over (U x)) PUnit ≅ M.over (U x)) :
    M.IsQuasicoherent := by
  have h : (coverWithFreeGenerator M U hU e).IsLocallyFreeData :=
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.mk (q := coverWithFreeGenerator M U hU e) (fun x => by
      let y : X := x
      change IsIso (freeIsoLocalGenerators M (U y) (e y)).π
      exact isIso_freeIsoLocalGenerators M (U y) (e y))
  exact (coverWithFreeGenerator M U hU e).quasiCoherentData.isQuasicoherent

private theorem quasicoherent_of_locally_unit
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    M.IsQuasicoherent := by
  classical
  choose U hx he using h
  have hU : (Opens.grothendieckTopology X).CoversTop U :=
    (Opens.coversTop_iff _ _).mpr (top_unique (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩))
  exact coverWithFreeGenerator_isQuasicoherent M U hU
    (fun x => freeIsoOfUnitPullback M (U x) (he x).some)

end LocallyTrivialSheaves
section AffineSheafDescent

private theorem retraction_of_commuting_isos {C : Type*} [Category C]
    {A B A' B' : C} (f : A ⟶ B) (f' : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : f ≫ b.hom = a.hom ≫ f') (r : B' ⟶ A') (hr : f' ≫ r = 𝟙 A') :
    ∃ q : B ⟶ A, f ≫ q = 𝟙 A := by
  refine ⟨b.hom ≫ r ≫ a.inv, ?_⟩
  rw [← Category.assoc f, h, Category.assoc, ← Category.assoc f', hr, Category.id_comp,
    Iso.hom_inv_id]

private theorem line_after_pullback {X Y : Scheme.{u}} {M E : X.Modules}
    (f : M ⟶ E) (U : X.Opens) (g : Y ⟶ U.toScheme)
    (t : ((Scheme.Modules.pullback U.ι).obj M) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (r : (Scheme.Modules.pullback U.ι).obj E ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (hr : (Scheme.Modules.pullback U.ι).map f ≫ r = 𝟙 _)
    (j : Y ⟶ X) (h : g ≫ U.ι = j) :
    Nonempty ((Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) ∧
    ∃ q, (Scheme.Modules.pullback j).map f ≫ q = 𝟙 _ := by
  let P := Scheme.Modules.pullback g
  let I := Scheme.Modules.pullback U.ι
  let J := Scheme.Modules.pullback j
  let e := (Scheme.Modules.pullbackComp g U.ι) ≪≫ Scheme.Modules.pullbackCongr h
  refine ⟨⟨(e.app M).symm ≪≫ P.mapIso t ≪≫ pullbackUnitIso g⟩, ?_⟩
  have hc : J.map f ≫ (e.app E).inv = (e.app M).inv ≫ P.map (I.map f) :=
    e.inv.naturality f
  have hq : P.map (I.map f) ≫ P.map r = 𝟙 _ := by
    rw [← P.map_comp, hr, P.map_id]
  exact retraction_of_commuting_isos _ _ (e.app M).symm (e.app E).symm hc _ hq

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
variable {R : TestAlgebra k}

private abbrev tildeInclusion (N : Submodule R (R ⊗[k] W)) :
    tilde (R := CommRingCat.of R) (ModuleCat.of R N) ⟶
      tilde (R := CommRingCat.of R) (ModuleCat.of R (R ⊗[k] W)) :=
  (tilde.functor (CommRingCat.of R)).map
    (ModuleCat.ofHom N.subtype : ModuleCat.of R N ⟶ ModuleCat.of R (R ⊗[k] W))

omit [Module.Finite k W] in
private theorem localizedSubmoduleLine_of_splitSheaf (N : Submodule R (R ⊗[k] W)) (r : R)
    (t : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj
      (tilde (ModuleCat.of R N)) ≅ SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away r))).ringCatSheaf)
    (q : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj
          (tilde (ModuleCat.of R (R ⊗[k] W))) ⟶
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj
          (tilde (ModuleCat.of R N)))
    (hq : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).map
          (tildeInclusion N) ≫ q = 𝟙 _) :
    ∃ L : AffineLine k W (awayAlgebra r), L.submodule = awaySubmodule r N := by
  let B := Localization.Away r
  let S := Submonoid.powers r
  let P := awaySubmodule r N
  let f := scalarExtension k W R B
  let e : B ⊗[R] N ≃ₗ[B] P := (IsLocalizedModule.isBaseChange S B
    (N.toLocalized' B S f)).equiv
  let c : B ⊗[R] (R ⊗[k] W) ≃ₗ[B] B ⊗[k] W :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange k R B B W
  have hcomm : c.toLinearMap.comp (N.subtype.baseChange B) = P.subtype.comp e.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      have hb : b ⊗ₜ[R] x = b • ((1 : B) ⊗ₜ[R] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hb, map_smul, map_smul]
      congr 1
      change c ((1 : B) ⊗ₜ[R] x.val) = (e ((1 : B) ⊗ₜ[R] x)).val
      rw [show e ((1 : B) ⊗ₜ[R] x) = N.toLocalized' B S f x from by
        exact (IsBaseChange.equiv_tmul _ 1 x).trans (one_smul _ _)]
      rfl
  let F := tilde.functor (CommRingCat.of B)
  let em : ModuleCat.of B (B ⊗[R] N) ≅ ModuleCat.of B P := e.toModuleIso
  let cm : ModuleCat.of B (B ⊗[R] (R ⊗[k] W)) ≅ ModuleCat.of B (B ⊗[k] W) := c.toModuleIso
  let E := tildeAlgebraMapPullback R B N ≪≫ F.mapIso em
  let C := tildeAlgebraMapPullback R B (R ⊗[k] W) ≪≫ F.mapIso cm
  let i : ModuleCat.of B P ⟶ ModuleCat.of B (B ⊗[k] W) := ModuleCat.ofHom P.subtype
  let J := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  have hn : J.map (tildeInclusion N) ≫ C.hom = E.hom ≫ F.map i := by
    have h₀ := tildeAlgebraMapPullback_naturality (A := (R : Type u)) (B := B)
      (M := ↥N) (N := R ⊗[k] W) N.subtype
    have h₁ : F.map (ModuleCat.ofHom (N.subtype.baseChange B)) ≫ F.map cm.hom =
        F.map em.hom ≫ F.map i := by
      rw [← F.map_comp, ← F.map_comp]
      exact congrArg (fun a => F.map a) (ModuleCat.hom_ext hcomm)
    calc
      _ = J.map (tildeInclusion N) ≫ (tildeAlgebraMapPullback R B (R ⊗[k] W)).hom ≫
          F.map cm.hom := rfl
      _ = (tildeAlgebraMapPullback R B N).hom ≫ F.map (ModuleCat.ofHom (N.subtype.baseChange B)) ≫
          F.map cm.hom :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ F.map cm.hom) h₀).trans (Category.assoc _ _ _))
      _ = (tildeAlgebraMapPullback R B N).hom ≫ F.map em.hom ≫ F.map i :=
        congrArg ((tildeAlgebraMapPullback R B N).hom ≫ ·) h₁
      _ = E.hom ≫ F.map i := (Category.assoc _ _ _).symm
  obtain ⟨g, hg⟩ :=
    retraction_of_commuting_isos (F.map i) (J.map (tildeInclusion N)) E.symm C.symm
      (by
        change F.map i ≫ C.inv = E.inv ≫ J.map (tildeInclusion N)
        apply (cancel_mono C.hom).mp
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hn,
          Iso.inv_hom_id_assoc]) q hq
  let Ff := tilde.fullyFaithfulFunctor (R := CommRingCat.of B)
  let gg : ModuleCat.of B (B ⊗[k] W) ⟶ ModuleCat.of B P := Ff.preimage g
  have hgg : i ≫ gg = 𝟙 _ := by
    apply Ff.map_injective
    rw [Functor.map_comp, Ff.map_preimage, hg]
    exact (F.map_id _).symm
  let u : ModuleCat.of B P ≅ ModuleCat.of B B := Ff.preimageIso (E.symm ≪≫ t ≪≫ tildeSelf.symm)
  let u' := u.toLinearEquiv
  refine ⟨⟨P, ⟨gg.hom.ker, LinearMap.isCompl_of_proj (fun x => DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom hgg) x)⟩, Module.Finite.equiv u'.symm,
      Module.Projective.of_equiv u'.symm, fun p => ?_⟩, rfl⟩
  let := p.nontrivial
  change Module.rankAtStalk (↑(ModuleCat.of B P)) p = 1
  rw [Module.rankAtStalk_eq_of_equiv u', Module.rankAtStalk_self]
  rfl

private theorem affineLine_of_tildeInclusion (N : Submodule R (R ⊗[k] W))
    (h : IsLocalLineInclusion (tildeInclusion N)) :
    ∃ L : AffineLine k W R, L.submodule = N := by
  classical
  let s : Set R := {r | ∃ L : AffineLine k W (awayAlgebra r), awaySubmodule r N = L.submodule}
  have hp (x : PrimeSpectrum R) : ∃ r ∈ s, r ∉ x.asIdeal := by
    obtain ⟨U, hxU, ⟨t⟩, q, hq⟩ := h x
    obtain ⟨V, ⟨r, rfl⟩, hx, hr⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (PrimeSpectrum.isBasis_basic_opens (R := R))) hxU
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
    have hs : Set.range j ⊆ Set.range U.ι := by
      have h₁ : Set.range j = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
        PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
      have h₂ : Set.range U.ι = (U : Set (Spec (CommRingCat.of R))) := U.range_ι
      exact Set.Subset.trans (le_of_eq h₁)
        (Set.Subset.trans (show (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
          (U : Set (Spec (CommRingCat.of R))) from hr) (le_of_eq h₂.symm))
    let g := IsOpenImmersion.lift U.ι j hs
    have hg := IsOpenImmersion.lift_fac U.ι j hs
    obtain ⟨⟨t'⟩, q', hq'⟩ := line_after_pullback (tildeInclusion N) U g t q hq j hg
    obtain ⟨L, hL⟩ := localizedSubmoduleLine_of_splitSheaf N r t' q' hq'
    exact ⟨r, ⟨L, hL.symm⟩, hx⟩
  have htop : Ideal.span s = ⊤ := by
    by_contra hn
    obtain ⟨m, hm, hl⟩ := (Ideal.span s).exists_le_maximal hn
    obtain ⟨r, hr, hn⟩ := hp ⟨m, inferInstance⟩
    exact hn (hl (Ideal.subset_span hr))
  have hex (r : s) : ∃ L : AffineLine k W (awayAlgebra r.val), awaySubmodule r.val N = L.submodule :=
    r.property
  choose L hL using hex
  exact line_of_localizations s htop N L hL

set_option maxHeartbeats 1000000 in
private theorem exists_line_of_affineLineSheaf
    (M : LineSubbundle k W ((testSpec k).obj (op R))) :
    let S := (testSpec k).obj (op R)
    ∃ (L : AffineLine k W R) (d : tilde (ModuleCat.of R L.submodule) ≅ (M.val : S.left.Modules)),
      tildeInclusion L.submodule ≫ (affineConstantBundleIso k W R).hom = d.hom ≫ M.val.arrow := by
  let S := (testSpec k).obj (op R)
  let M₀ : (Spec (CommRingCat.of R)).Modules := Subobject.underlying.obj M.val
  have hM : M₀.IsQuasicoherent := quasicoherent_of_locally_unit M₀ fun x => by
    obtain ⟨U, hU, e, _, _⟩ := M.property x
    exact ⟨U, hU, e⟩
  let F := tilde.functor (CommRingCat.of R)
  let E : (Spec (CommRingCat.of R)).Modules := constantBundle k W S
  let c : F.obj (ModuleCat.of R (R ⊗[k] W)) ≅ E := affineConstantBundleIso k W R
  let j : M₀ ⟶ E := M.val.arrow
  have hj : Mono j := inferInstanceAs (Mono M.val.arrow)
  let FF := tilde.fullyFaithfulFunctor (R := CommRingCat.of R)
  let A := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj M₀
  have hh : IsIso M₀.fromTildeΓ := @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _ _ hM
  let e : F.obj A ≅ M₀ := @asIso _ _ _ _ M₀.fromTildeΓ hh
  let a : A ⟶ ModuleCat.of R (R ⊗[k] W) := FF.preimage (e.hom ≫ j ≫ c.inv)
  have ha : F.map a = e.hom ≫ j ≫ c.inv := FF.map_preimage _
  have hm' : Mono (F.map a) := ha.symm ▸ (inferInstanceAs (Mono (e.hom ≫ j ≫ c.inv)))
  have hm : Mono a := by
    constructor
    intro Z f g h
    apply FF.map_injective
    apply (cancel_mono (F.map a)).mp
    rw [← F.map_comp, ← F.map_comp, h]
  let P := a.hom.range
  let b : A ≅ ModuleCat.of R P :=
    LinearEquiv.toModuleIso (LinearEquiv.ofInjective a.hom ((ModuleCat.mono_iff_injective a).mp hm))
  let i : ModuleCat.of R P ⟶ ModuleCat.of R (R ⊗[k] W) := ModuleCat.ofHom P.subtype
  have hb : b.hom ≫ i = a := rfl
  let d := (F.mapIso b).symm ≪≫ e
  have hd : tildeInclusion P ≫ c.hom = d.hom ≫ j := by
    have hd' : F.map b.hom ≫ F.map i = F.map a :=
      (F.map_comp _ _).symm.trans (congrArg (fun t => F.map t) hb)
    have he : F.map b.hom ≫ d.hom = e.hom := by
      change (F.mapIso b).hom ≫ (F.mapIso b).inv ≫ e.hom = _
      exact Iso.hom_inv_id_assoc _ _
    apply (cancel_epi (F.mapIso b).hom).mp
    calc
      _ = F.map a ≫ c.hom := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c.hom) hd')
      _ = (e.hom ≫ j ≫ c.inv) ≫ c.hom := congrArg (· ≫ c.hom) ha
      _ = e.hom ≫ j := by rw [Category.assoc, Category.assoc j, Iso.inv_hom_id, Category.comp_id]
      _ = F.map b.hom ≫ (d.hom ≫ j) :=
        (congrArg (· ≫ j) he.symm).trans (Category.assoc _ _ _)
  have hlocal : IsLocalLineInclusion (tildeInclusion P) := by
    intro x
    obtain ⟨U, hx, ⟨t⟩, r, hr⟩ := M.property x
    let G := Scheme.Modules.pullback U.ι
    refine ⟨U, hx, ⟨G.mapIso d ≪≫ t⟩, ?_⟩
    have hcomm : G.map (tildeInclusion P) ≫ (G.mapIso c).hom = (G.mapIso d).hom ≫ G.map M.val.arrow :=
      (G.map_comp _ _).symm.trans ((congrArg (fun f => G.map f) hd).trans (G.map_comp _ _))
    exact retraction_of_commuting_isos _ _ (G.mapIso d) (G.mapIso c) hcomm r hr
  obtain ⟨L, hL⟩ := affineLine_of_tildeInclusion P hlocal
  let Q (P : Submodule R (R ⊗[k] W)) : Prop :=
    ∃ e : tilde (ModuleCat.of R P) ≅ M₀, tildeInclusion P ≫ c.hom = e.hom ≫ j
  have hQ : Q P := ⟨d, hd⟩
  exact ⟨L, (congrArg Q hL).mpr hQ⟩

end AffineSheafDescent

theorem affineLineSheafReverse : AffineLineSheafReverse.{u} := by
  intro k W _ _ _ _
  exact ⟨affineConstantBundleIso k W, fun _ M => exists_line_of_affineLineSheaf M⟩

section AffineSheafCoherence

open TopCat
open scoped ChangeOfRings

private theorem homEquiv_comp_mate {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G')
    (t : F' ⟶ F) {M : C} {N : D} (h : F.obj M ⟶ N) :
    a.homEquiv _ _ h ≫ (conjugateEquiv a b t).app N =
      b.homEquiv _ _ (t.app M ≫ h) := by
  apply (b.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    conjugateEquiv_counit, t.naturality_assoc, ← Adjunction.homEquiv_counit,
    Equiv.symm_apply_apply]

/-- The transpose, evaluated on a generator of the original module. -/
private def transposeAt {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    (M : ModuleCat A) (N : X.Modules) (h : (Scheme.Modules.pullback f).obj (tilde M) ⟶ N)
    (m : M) : Γ(N, (⊤ : X.Opens)) :=
  ((tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _ h) m

private theorem transposeAt_injective {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    (M : ModuleCat A) (N : X.Modules) : Function.Injective (transposeAt f M N) := by
  intro x y h
  apply ((tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _).injective
  exact ModuleCat.hom_ext (LinearMap.ext (congrFun h))

private theorem transposeAt_congr {A : CommRingCat.{u}} {X : Scheme.{u}} {f g : X ⟶ Spec A}
    (p : f = g) (M : ModuleCat A) (N : X.Modules) (h : (Scheme.Modules.pullback g).obj (tilde M) ⟶ N)
    (m : M) :
    transposeAt f M N ((Scheme.Modules.pullbackCongr p).hom.app _ ≫ h) m =
      transposeAt g M N h m := by
  cases p
  simp [Scheme.Modules.pullbackCongr]

private theorem transposeAt_comp {A B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec B) (g : Spec B ⟶ Spec A) (M : ModuleCat A) (N : X.Modules)
    (h : (Scheme.Modules.pullback (f ≫ g)).obj (tilde M) ⟶ N) (m : M) :
    transposeAt g M ((Scheme.Modules.pushforward f).obj N)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((Scheme.Modules.pullbackComp f g).hom.app _ ≫ h)) m =
    transposeAt (f ≫ g) M N h m := by
  let a := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let b := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let c := Scheme.Modules.pullbackComp f g
  let v := Scheme.Modules.pushforwardComp f g
  have he := homEquiv_comp_mate a b c.inv (c.hom.app (tilde M) ≫ h)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Iso.inv_hom_id_app_assoc] at he
  let P := (Scheme.Modules.pushforward (f ≫ g)).obj N
  have ht := congrArg (fun j : tilde M ⟶ P =>
    ((tilde.adjunction.homEquiv M P j) m : Γ(N, (⊤ : X.Opens)))) he
  rw [Adjunction.homEquiv_naturality_right] at ht
  exact ht

set_option backward.isDefEq.respectTransparency false in
private theorem transposeAt_tildeSpecPullback {A B : CommRingCat.{u}} (f : A ⟶ B)
    (M : ModuleCat A) (N : (Spec B).Modules)
    (h : (ModuleCat.extendScalars f.hom ⋙ tilde.functor B).obj M ⟶ N) (m : M) :
    transposeAt (Spec.map f) M N ((tildeSpecPullback f).hom.app M ≫ h) m =
      (tilde.adjunction.homEquiv _ _ h) ((1 : B) ⊗ₜ[A,f.hom] m) := by
  let a := tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))
  let c := affineSectionsPushforwardIso f
  let b := (ModuleCat.extendRestrictScalarsAdj f.hom).comp tilde.adjunction
  let h' : (ModuleCat.extendScalars f.hom ⋙ tilde.functor B).obj M ⟶ N := h
  have ht := (a.ofNatIsoRight c).homEquiv_leftAdjointUniq_hom_app b M
  have he := ((a.ofNatIsoRight c).homEquiv_naturality_right
    ((tildeSpecPullback f).hom.app M) h').trans <|
      (congrArg (· ≫ _) ht).trans (b.homEquiv_unit M N h').symm
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at he
  exact congrArg (fun j => (j m : Γ(N, (⊤ : (Spec B).Opens)))) he

private theorem extendScalarsAlgebraIso_hom_one_tmul (A B M : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] (m : M) :
    (extendScalarsAlgebraIso A B M).hom ((1 : B) ⊗ₜ[A,algebraMap A B] m) =
      (1 : B) ⊗ₜ[A] m := by
  let F (s : Algebra A B) : ModuleCat B := letI := s; ModuleCat.of B (B ⊗[A] M)
  let t (s : Algebra A B) : F s := letI := s; (1 : B) ⊗ₜ[A] m
  have h (s s' : Algebra A B) (e : s = s') :
      (eqToHom (congrArg F e)) (t s) = t s' := by subst e; rfl
  exact h _ _ toAlgebra_algebraMap

set_option backward.isDefEq.respectTransparency false in
private theorem transposeAt_tildeAlgebraMapPullback (A B M : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] {N : (Spec (CommRingCat.of B)).Modules}
    (h : tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[A] M)) ⟶ N) (m : M) :
    transposeAt (Spec.map (CommRingCat.ofHom (algebraMap A B))) (ModuleCat.of A M) N
      ((tildeAlgebraMapPullback A B M).hom ≫ h) m =
      (tilde.adjunction.homEquiv _ N h) ((1 : B) ⊗ₜ[A] m) := by
  let f := CommRingCat.ofHom (algebraMap A B)
  let M₀ : ModuleCat (CommRingCat.of A) := ModuleCat.of A M
  let ψ := (tildeSpecPullback f).app M₀
  let e := (extendScalarsAlgebraIso A B M).hom
  let H := tilde.functor (CommRingCat.of B)
  have hn := (tilde.adjunction (R := CommRingCat.of B)).homEquiv_naturality_left e h
  change transposeAt (Spec.map f) M₀ N ((ψ.hom ≫ H.map e) ≫ h) m = _
  refine (congrArg (fun q => transposeAt (Spec.map f) M₀ N q m)
    (Category.assoc ψ.hom (H.map e) h)).trans ?_
  refine (transposeAt_tildeSpecPullback f M₀ N (H.map e ≫ h) m).trans ?_
  refine (congrArg (fun j => j ((1 : B) ⊗ₜ[A,algebraMap A B] m)) hn).trans ?_
  change (tilde.adjunction.homEquiv _ N h) (e ((1 : B) ⊗ₜ[A,algebraMap A B] m)) = _
  exact congrArg (fun z => (tilde.adjunction.homEquiv _ N h) z)
    (extendScalarsAlgebraIso_hom_one_tmul A B M m)

end AffineSheafCoherence

section LineSubbundlePullback

open TopCat TopologicalSpace

set_option backward.isDefEq.respectTransparency false

private theorem mono_of_localLine {X : Scheme.{u}} {M E : X.Modules} {i : M ⟶ E}
    (h : IsLocalLineInclusion i) : Mono i := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U s t he
  apply TopCat.Presheaf.section_ext (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) U.unop
  intro x hx
  obtain ⟨V, hxV, _, r, hr⟩ := h x
  let p : V.toScheme := ⟨x, hxV⟩
  let P := Scheme.Modules.restrictFunctor V.ι
  let Q := Scheme.Modules.pullback V.ι
  let e := Scheme.Modules.restrictFunctorIsoPullback V.ι
  have hc : P.map i ≫ (e.app E).hom = (e.app M).hom ≫ Q.map i := e.hom.naturality i
  obtain ⟨q, hq⟩ := retraction_of_commuting_isos _ _ (e.app M) (e.app E) hc r hr
  let G := Scheme.Modules.toPresheaf V.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ p
  have hi : Mono (G.map (P.map i)) := by
    have hh : G.map (P.map i) ≫ G.map q = 𝟙 _ := by rw [← G.map_comp, hq, G.map_id]
    exact mono_of_mono_fac hh
  let ψ := Scheme.Modules.restrictStalkNatIso V.ι p
  let T := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ x
  have hψ : G.map (P.map i) ≫ ψ.hom.app E = ψ.hom.app M ≫ T.map i :=
    ψ.hom.naturality i
  have hmono : Mono (ψ.hom.app M ≫ T.map i) := hψ ▸
    (inferInstanceAs (Mono (G.map (P.map i) ≫ ψ.hom.app E)))
  have hmono' : Mono (T.map i) := by
    have hc : (ψ.inv.app M) ≫ ψ.hom.app M ≫ T.map i = T.map i := ψ.inv_hom_id_app_assoc _ _
    exact hc ▸ (inferInstanceAs (Mono (ψ.inv.app M ≫ ψ.hom.app M ≫ T.map i)))
  have hinj := (AddCommGrpCat.mono_iff_injective (T.map i)).mp hmono'
  apply hinj
  change ((M.presheaf.germ U.unop x hx ≫
    (TopCat.Presheaf.stalkFunctor _ x).map i.mapPresheaf) s) =
    ((M.presheaf.germ U.unop x hx ≫
    (TopCat.Presheaf.stalkFunctor _ x).map i.mapPresheaf) t)
  rw [TopCat.Presheaf.stalkFunctor_map_germ]
  exact congrArg (fun a => E.presheaf.germ U.unop x hx a) he

private theorem isLocalLineInclusion_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M E E' : _} (i : M ⟶ E) (h : IsLocalLineInclusion i)
    (e : (Scheme.Modules.pullback f).obj E ≅ E') :
    IsLocalLineInclusion ((Scheme.Modules.pullback f).map i ≫ e.hom) := by
  intro x
  obtain ⟨V, hx, ⟨t⟩, r, hr⟩ := h (f x)
  let U := f ⁻¹ᵁ V
  have hs : Set.range (U.ι ≫ f) ⊆ Set.range V.ι := by
    rw [V.range_ι]
    rintro _ ⟨y, rfl⟩
    exact y.property
  let a := IsOpenImmersion.lift V.ι (U.ι ≫ f) hs
  obtain ⟨ht, ⟨q, hq⟩⟩ := line_after_pullback i V a t r hr (U.ι ≫ f)
    (IsOpenImmersion.lift_fac V.ι (U.ι ≫ f) hs)
  let C := Scheme.Modules.pullbackComp U.ι f
  let P := Scheme.Modules.pullback U.ι
  let F := Scheme.Modules.pullback f
  let J := Scheme.Modules.pullback (U.ι ≫ f)
  refine ⟨U, hx, ⟨C.app M ≪≫ ht.some⟩, ?_⟩
  have hc : ((F ⋙ P).map i) ≫ C.hom.app E = C.hom.app M ≫ J.map i := C.hom.naturality i
  obtain ⟨g, hg⟩ := retraction_of_commuting_isos _ _ (C.app M) (C.app E) hc q hq
  refine ⟨P.map e.inv ≫ g, ?_⟩
  change P.map (F.map i ≫ e.hom) ≫ P.map e.inv ≫ g = _
  calc
    _ = P.map (F.map i) ≫ P.map e.hom ≫ P.map e.inv ≫ g :=
      P.map_comp_assoc (F.map i) e.hom _
    _ = P.map (F.map i) ≫ g := by
      have he : P.map e.hom ≫ P.map e.inv ≫ g = g := by
        calc
          _ = P.map (e.hom ≫ e.inv) ≫ g := (P.map_comp_assoc _ _ _).symm
          _ = g := by rw [e.hom_inv_id, P.map_id, Category.id_comp]
      exact congrArg (P.map (F.map i) ≫ ·) he
    _ = _ := hg

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W]

/-- Pullback of a locally split line inside the pulled back constant bundle. -/
def pullbackLine {S T : SchemeOver k} (f : T ⟶ S) (L : LineSubbundle k W S) :
    LineSubbundle k W T := by
  let P := Scheme.Modules.pullback f.left
  let i := P.map L.val.arrow ≫ (pullbackAmbientIso k W f).hom
  have hi := isLocalLineInclusion_pullback f.left L.val.arrow L.property (pullbackAmbientIso k W f)
  letI : Mono i := mono_of_localLine hi
  refine ⟨Subobject.mk i, ?_⟩
  intro x
  obtain ⟨U, hx, ⟨t⟩, r, hr⟩ := hi x
  let F := Scheme.Modules.pullback U.ι
  let e := Subobject.underlyingIso i
  refine ⟨U, hx, ⟨F.mapIso e ≪≫ t⟩, ?_⟩
  have hc : F.map (Subobject.mk i).arrow ≫ (Iso.refl _).hom =
      (F.mapIso e).hom ≫ F.map i := by
    change F.map (Subobject.mk i).arrow ≫ 𝟙 _ = F.map e.hom ≫ F.map i
    exact (Category.comp_id _).trans <| (congrArg F.map
      (Subobject.underlyingIso_hom_comp_eq_mk i).symm).trans (F.map_comp _ _)
  exact retraction_of_commuting_isos _ _ (F.mapIso e) (Iso.refl _) hc r hr

theorem isPullbackLine_pullbackLine {S T : SchemeOver k} (f : T ⟶ S)
    (L : LineSubbundle k W S) :
    IsPullbackLine k W f L (pullbackLine f L) := by
  dsimp only [pullbackLine]
  let i := (Scheme.Modules.pullback f.left).map L.val.arrow ≫ (pullbackAmbientIso k W f).hom
  let : Mono i := mono_of_localLine
    (isLocalLineInclusion_pullback f.left L.val.arrow L.property (pullbackAmbientIso k W f))
  exact ⟨(Subobject.underlyingIso i).symm, (Subobject.underlyingIso_arrow i).symm⟩

theorem pullbackLine_eq_iff {S T : SchemeOver k} (f : T ⟶ S)
    (L : LineSubbundle k W S) (M : LineSubbundle k W T) :
    pullbackLine f L = M ↔ IsPullbackLine k W f L M := by
  constructor
  · rintro rfl
    exact isPullbackLine_pullbackLine f L
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := isPullbackLine_pullbackLine f L
    apply Subtype.ext
    apply Subobject.eq_of_comm (a.symm ≪≫ b)
    change a.inv ≫ b.hom ≫ M.val.arrow = _
    rw [← hb, ha, Iso.inv_hom_id_assoc]

private theorem pullbackAmbientIso_comp_hom_aux {X Y Z B : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : Z ⟶ B) (M : B.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g a).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ a)).hom.app M =
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback a).obj M) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) a).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g a)).hom.app M := by
  let P := Scheme.Modules.pullback f
  let e := (Scheme.Modules.pullbackComp f (g ≫ a)).app M
  let d := P.mapIso ((Scheme.Modules.pullbackComp g a).app M)
  let c := (Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback a).obj M)
  let b := (Scheme.Modules.pullbackComp (f ≫ g) a).app M
  let r := (Scheme.Modules.pullbackCongr (Category.assoc f g a)).app M
  have hc := congrArg (fun t => t.app M) (Scheme.Modules.pseudofunctor_associativity f g a)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.id_comp, Functor.whiskerLeft_app] at hc
  change e.inv ≫ d.inv ≫ c.hom ≫ b.hom = r.inv at hc
  change d.hom ≫ e.hom = c.hom ≫ b.hom ≫ r.hom
  calc
    d.hom ≫ e.hom = d.hom ≫ e.hom ≫ r.inv ≫ r.hom := by simp
    _ = c.hom ≫ b.hom ≫ r.hom := by rw [← hc]; simp

private theorem pullbackAmbientIso_comp_hom_of_eq {X Y Z B : Scheme.{u}}
    (x : X ⟶ Y) (y : Y ⟶ Z) (a : Z ⟶ B) (b : Y ⟶ B) (c : X ⟶ B)
    (p : y ≫ a = b) (q : x ≫ b = c) (r : (x ≫ y) ≫ a = c) (M : B.Modules) :
    (Scheme.Modules.pullback x).map ((Scheme.Modules.pullbackComp y a).hom.app M ≫
      (Scheme.Modules.pullbackCongr p).hom.app M) ≫
      (Scheme.Modules.pullbackComp x b).hom.app M ≫ (Scheme.Modules.pullbackCongr q).hom.app M =
    (Scheme.Modules.pullbackComp x y).hom.app ((Scheme.Modules.pullback a).obj M) ≫
      (Scheme.Modules.pullbackComp (x ≫ y) a).hom.app M ≫
        (Scheme.Modules.pullbackCongr r).hom.app M := by
  subst b
  subst c
  simpa only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Category.assoc] using pullbackAmbientIso_comp_hom_aux x y a M

private theorem pullbackAmbientIso_comp_hom {S T U : SchemeOver k} (f : T ⟶ S) (g : U ⟶ T) :
    (Scheme.Modules.pullback g.left).map (pullbackAmbientIso k W f).hom ≫
      (pullbackAmbientIso k W g).hom =
    (Scheme.Modules.pullbackComp g.left f.left).hom.app (constantBundle k W S) ≫
      (pullbackAmbientIso k W (g ≫ f)).hom :=
  pullbackAmbientIso_comp_hom_of_eq g.left f.left S.hom T.hom U.hom
    (Over.w f) (Over.w g) (Over.w (g ≫ f)) (tilde (ModuleCat.of k W))

theorem pullbackLine_comp {S T U : SchemeOver k} (f : T ⟶ S) (g : U ⟶ T)
    (L : LineSubbundle k W S) :
    pullbackLine (g ≫ f) L = pullbackLine g (pullbackLine f L) := by
  let P := Scheme.Modules.pullback f.left
  let Q := Scheme.Modules.pullback g.left
  let C₀ := Scheme.Modules.pullbackComp g.left f.left
  obtain ⟨a, ha⟩ := isPullbackLine_pullbackLine f L
  obtain ⟨b, hb⟩ := isPullbackLine_pullbackLine g (pullbackLine f L)
  apply (pullbackLine_eq_iff _ _ _).mpr
  refine ⟨(C₀.app _).symm ≪≫ Q.mapIso a ≪≫ b, ?_⟩
  let i := L.val.arrow
  have hc := pullbackAmbientIso_comp_hom (W := W) f g
  have h := C₀.inv.naturality_assoc i
    (Q.map (pullbackAmbientIso k W f).hom ≫ (pullbackAmbientIso k W g).hom)
  change (Scheme.Modules.pullback (g.left ≫ f.left)).map i ≫
      (pullbackAmbientIso k W (g ≫ f)).hom =
    (C₀.app _).inv ≫ (Q.map a.hom ≫ b.hom) ≫ (pullbackLine g (pullbackLine f L)).val.arrow
  simp only [Category.assoc]
  rw [← hb, ← Q.map_comp_assoc, ← ha, Q.map_comp, Category.assoc]
  symm
  refine h.symm.trans ?_
  rw [hc, Iso.inv_hom_id_app_assoc]

theorem pullbackLine_id {S : SchemeOver k} (L : LineSubbundle k W S) :
    pullbackLine (𝟙 S) L = L := by
  apply (pullbackLine_eq_iff _ _ _).mpr
  let e := Scheme.Modules.pullbackId S.left
  refine ⟨e.app _, ?_⟩
  have h₀ := congrArg (fun t => t.app (tilde (R := CommRingCat.of k) (ModuleCat.of k W)))
    (Scheme.Modules.pseudofunctor_right_unitality S.hom)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at h₀
  have he : (pullbackAmbientIso k W (𝟙 S)).hom = e.hom.app (constantBundle k W S) := by
    let M := tilde (R := CommRingCat.of k) (ModuleCat.of k W)
    change (Scheme.Modules.pullbackComp (𝟙 S.left) S.hom).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Category.id_comp S.hom)).hom.app M = _
    have h₁ : (Scheme.Modules.pullbackComp (𝟙 S.left) S.hom).inv.app M ≫
        e.hom.app (constantBundle k W S) =
        (Scheme.Modules.pullbackCongr (Category.id_comp S.hom)).hom.app M := h₀
    rw [← h₁, Iso.hom_inv_id_app_assoc]
  rw [he]
  exact e.hom.naturality L.val.arrow

end LineSubbundlePullback

section AffineLineSheafEquivalence

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W]
variable {R T : TestAlgebra k}

variable [Module.Finite k W]

private def AffineSheafMatch (L : AffineLine k W R)
    (M : LineSubbundle k W ((testSpec k).obj (op R))) : Prop :=
  ∃ d : tilde (R := CommRingCat.of R) (ModuleCat.of R L.submodule) ≅ Subobject.underlying.obj M.val,
    tildeInclusion L.submodule ≫ (affineConstantBundleIso k W R).hom = d.hom ≫ M.val.arrow

omit [Module.Finite k W] in
private theorem AffineSheafMatch.unique_sheaf {L : AffineLine k W R}
    {M N : LineSubbundle k W ((testSpec k).obj (op R))}
    (h : AffineSheafMatch L M) (h' : AffineSheafMatch L N) : M = N := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨e, he⟩ := h'
  apply Subtype.ext
  apply Subobject.eq_of_comm (d.symm ≪≫ e)
  change (d.inv ≫ e.hom) ≫ N.val.arrow = M.val.arrow
  rw [Category.assoc, ← he, hd, Iso.inv_hom_id_assoc]

omit [Module.Finite k W] in
private theorem AffineSheafMatch.unique_line {L L' : AffineLine k W R}
    {M : LineSubbundle k W ((testSpec k).obj (op R))}
    (h : AffineSheafMatch L M) (h' : AffineSheafMatch L' M) : L = L' := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨e, he⟩ := h'
  let C := affineConstantBundleIso k W R
  let F := tilde.functor (CommRingCat.of R)
  let FF := tilde.fullyFaithfulFunctor (R := CommRingCat.of R)
  let t : F.obj (ModuleCat.of R L.submodule) ≅ F.obj (ModuleCat.of R L'.submodule) := d ≪≫ e.symm
  have hcomm : t.hom ≫ tildeInclusion L'.submodule = tildeInclusion L.submodule := by
    apply (cancel_mono C.hom).mp
    change (d.hom ≫ e.inv) ≫ tildeInclusion L'.submodule ≫ C.hom =
      tildeInclusion L.submodule ≫ C.hom
    calc
      _ = d.hom ≫ e.inv ≫ (tildeInclusion L'.submodule ≫ C.hom) := Category.assoc _ _ _
      _ = d.hom ≫ e.inv ≫ e.hom ≫ M.val.arrow := congrArg (fun z => d.hom ≫ e.inv ≫ z) he
      _ = _ := (congrArg (d.hom ≫ ·) (e.inv_hom_id_assoc M.val.arrow)).trans hd.symm
  let v := FF.preimageIso t
  have hmap : v.hom ≫ ModuleCat.ofHom L'.submodule.subtype = ModuleCat.ofHom L.submodule.subtype := by
    apply FF.map_injective
    change F.map (v.hom ≫ ModuleCat.ofHom L'.submodule.subtype) = tildeInclusion L.submodule
    rw [F.map_comp]
    exact (congrArg (fun z => z ≫ tildeInclusion L'.submodule) (FF.map_preimage t.hom)).trans hcomm
  apply affineLine_ext
  have heq := congrArg (fun j : ModuleCat.of R L.submodule ⟶ ModuleCat.of R (R ⊗[k] W) =>
    j.hom.range) hmap
  simpa only [ModuleCat.hom_comp, LinearMap.range_comp, LinearMap.range_eq_top.mpr
    ((ModuleCat.epi_iff_surjective v.hom).mp inferInstance), Submodule.map_top, Submodule.range_subtype,
    ModuleCat.hom_ofHom] using heq.symm

/-- Associated sheaves identify the affine module lines with the locally split line subbundles. -/
def affineLineSheafEquiv (R : TestAlgebra k) :
    AffineLine k W R ≃ LineSubbundle k W ((testSpec k).obj (op R)) where
  toFun L := (exists_affineLineSheaf L).choose
  invFun M := (exists_line_of_affineLineSheaf M).choose
  left_inv L := AffineSheafMatch.unique_line
    (exists_line_of_affineLineSheaf ((exists_affineLineSheaf L).choose)).choose_spec
    (exists_affineLineSheaf L).choose_spec
  right_inv M := AffineSheafMatch.unique_sheaf
    (exists_affineLineSheaf ((exists_line_of_affineLineSheaf M).choose)).choose_spec
    (exists_line_of_affineLineSheaf M).choose_spec

theorem affineLineSheafEquiv_spec (L : AffineLine k W R) :
    AffineSheafMatch L (affineLineSheafEquiv R L) := (exists_affineLineSheaf L).choose_spec

end AffineLineSheafEquivalence

section TildeScalarTower

open TopCat

set_option maxRecDepth 260

variable (A B C M : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [AddCommGroup M] [Module A M]

private abbrev specAlgebraMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

private theorem specAlgebraMap_comp :
    specAlgebraMap B C ≫ specAlgebraMap A B = specAlgebraMap A C := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq A B C]

private abbrev cancelTower : C ⊗[B] (B ⊗[A] M) ≃ₗ[C] C ⊗[A] M :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M

private abbrev towerTarget : (Spec (CommRingCat.of C)).Modules :=
  tilde (R := CommRingCat.of C) (ModuleCat.of C (C ⊗[A] M))

private theorem transposeAt_tower_tmul (m : M) :
    let d := (tilde.functor (CommRingCat.of C)).map (cancelTower A B C M).toModuleIso.hom
    (tilde.adjunction.homEquiv _ (towerTarget A C M) d)
        ((1 : C) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m)) =
      (tilde.adjunction.homEquiv _ (towerTarget A C M) (𝟙 _)) ((1 : C) ⊗ₜ[A] m) := by
  let F := tilde.functor (CommRingCat.of C)
  let N := towerTarget A C M
  let e := (cancelTower A B C M).toModuleIso
  let t : C ⊗[B] (B ⊗[A] M) := (1 : C) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m)
  have ht : e.hom t = (1 : C) ⊗ₜ[A] m := by
    change (cancelTower A B C M) t = _
    rw [show t = (1 : C) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m) from rfl,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  let K := tilde.adjunction (R := CommRingCat.of C)
  change K.homEquiv _ N (F.map e.hom) t = _
  calc
    _ = K.homEquiv _ N (F.map e.hom ≫ 𝟙 N) t :=
      congrArg (fun q => K.homEquiv (ModuleCat.of C (C ⊗[B] (B ⊗[A] M))) N q t)
        (Category.comp_id (F.map e.hom)).symm
    _ = K.homEquiv _ N (𝟙 N) (e.hom t) :=
      congrArg (fun q => q t) (K.homEquiv_naturality_left e.hom (𝟙 N))
    _ = _ := congrArg (fun v => K.homEquiv _ N (𝟙 N) v) ht

private abbrev towerBaseModule := ModuleCat.of (CommRingCat.of A) M

private abbrev towerCompositeComparison : (Scheme.Modules.pullback (specAlgebraMap B C ≫ specAlgebraMap A B)).obj
    (tilde (towerBaseModule A M)) ⟶ towerTarget A C M :=
  (Scheme.Modules.pullbackCongr (specAlgebraMap_comp A B C)).hom.app _ ≫
    (tildeAlgebraMapPullback A C M).hom

private abbrev towerSource : (Spec (CommRingCat.of C)).Modules :=
  (Scheme.Modules.pullback (specAlgebraMap B C)).obj
    ((Scheme.Modules.pullback (specAlgebraMap A B)).obj (tilde (towerBaseModule A M)))

private def towerFirstIso :
    towerSource A B C M ≅
    (Scheme.Modules.pullback (specAlgebraMap B C)).obj
      (tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[A] M))) :=
  (Scheme.Modules.pullback (specAlgebraMap B C)).mapIso (tildeAlgebraMapPullback A B M)

private def towerCompositeHom :
    towerSource A B C M ⟶ (Scheme.Modules.pullback (specAlgebraMap A C)).obj
      (tilde (towerBaseModule A M)) :=
  (Scheme.Modules.pullbackComp (specAlgebraMap B C) (specAlgebraMap A B)).hom.app
      (tilde (towerBaseModule A M)) ≫
    (Scheme.Modules.pullbackCongr (specAlgebraMap_comp A B C)).hom.app (tilde (towerBaseModule A M))

private def towerLastIso :
    (Scheme.Modules.pullback (specAlgebraMap A C)).obj (tilde (towerBaseModule A M)) ≅
      towerTarget A C M :=
  tildeAlgebraMapPullback A C M

private def towerAfterFirst :
    (Scheme.Modules.pullback (specAlgebraMap B C)).obj
      (tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[A] M))) ⟶ towerTarget A C M :=
  (tildeAlgebraMapPullback B C (B ⊗[A] M)).hom ≫
    (tilde.functor (CommRingCat.of C)).map (cancelTower A B C M).toModuleIso.hom

private def iteratedTildeComparison : towerSource A B C M ⟶ towerTarget A C M :=
  (towerFirstIso A B C M).hom ≫ towerAfterFirst A B C M

private def compositeTildeComparison : towerSource A B C M ⟶ towerTarget A C M :=
  (Scheme.Modules.pullbackComp (specAlgebraMap B C) (specAlgebraMap A B)).hom.app
      (tilde (towerBaseModule A M)) ≫ towerCompositeComparison A B C M

private theorem compositeTildeComparison_assoc :
    towerCompositeHom A B C M ≫ (towerLastIso A C M).hom =
      compositeTildeComparison A B C M := by
  unfold towerCompositeHom compositeTildeComparison towerCompositeComparison
  exact Category.assoc _ _ _

private def towerTranspose (h : towerSource A B C M ⟶ towerTarget A C M) (m : M) :
    Γ(towerTarget A C M, (⊤ : (Spec (CommRingCat.of C)).Opens)) :=
  let f := specAlgebraMap B C
  let g := specAlgebraMap A B
  let N := towerTarget A C M
  transposeAt g (towerBaseModule A M) ((Scheme.Modules.pushforward f).obj N)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ N h) m

private def towerGenerator (m : M) : Γ(towerTarget A C M, (⊤ : (Spec (CommRingCat.of C)).Opens)) :=
  (tilde.adjunction.homEquiv _ (towerTarget A C M) (𝟙 _)) ((1 : C) ⊗ₜ[A] m)

set_option maxHeartbeats 200000 in
private theorem transposeAt_tower_left (m : M) :
    towerTranspose A B C M (iteratedTildeComparison A B C M) m = towerGenerator A C M m := by
  let f := specAlgebraMap B C
  let g := specAlgebraMap A B
  let J := Scheme.Modules.pullbackPushforwardAdjunction f
  let N := towerTarget A C M
  let U := (Scheme.Modules.pushforward f).obj N
  let v := (tildeAlgebraMapPullback A B M).hom
  let w := (tildeAlgebraMapPullback B C (B ⊗[A] M)).hom
  let d := (tilde.functor (CommRingCat.of C)).map (cancelTower A B C M).toModuleIso.hom
  let h := J.homEquiv _ N (w ≫ d)
  have hn := J.homEquiv_naturality_left v (w ≫ d)
  let m' : towerBaseModule A M := m
  refine (congrArg (fun x => transposeAt g (towerBaseModule A M) U x m') hn).trans ?_
  refine (transposeAt_tildeAlgebraMapPullback A B M h m).trans ?_
  refine (transposeAt_tildeAlgebraMapPullback B C (B ⊗[A] M) d ((1 : B) ⊗ₜ[A] m)).trans ?_
  exact transposeAt_tower_tmul A B C M m

private theorem transposeAt_comp_congr {A' B' : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec B') (g : Spec B' ⟶ Spec A') (j : X ⟶ Spec A') (p : f ≫ g = j)
    (M' : ModuleCat A') (N : X.Modules) (z : (Scheme.Modules.pullback j).obj (tilde M') ⟶ N) (m : M') :
    transposeAt g M' ((Scheme.Modules.pushforward f).obj N)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((Scheme.Modules.pullbackComp f g).hom.app _ ≫
          (Scheme.Modules.pullbackCongr p).hom.app _ ≫ z)) m =
    transposeAt j M' N z m :=
  (transposeAt_comp f g M' N ((Scheme.Modules.pullbackCongr p).hom.app _ ≫ z) m).trans
    (transposeAt_congr p M' N z m)

private theorem transposeAt_tildeAlgebraMapPullback_hom (A' C' M' : Type u)
    [CommRing A'] [CommRing C'] [Algebra A' C'] [AddCommGroup M'] [Module A' M'] (m : M') :
    let N := towerTarget A' C' M'
    transposeAt (specAlgebraMap A' C') (towerBaseModule A' M') N (tildeAlgebraMapPullback A' C' M').hom m =
      (tilde.adjunction.homEquiv _ N (𝟙 N)) ((1 : C') ⊗ₜ[A'] m) := by
  let N := towerTarget A' C' M'
  let z := (tildeAlgebraMapPullback A' C' M').hom
  have h := transposeAt_tildeAlgebraMapPullback A' C' M' (𝟙 N) m
  exact (congrArg (fun x => transposeAt (specAlgebraMap A' C') (towerBaseModule A' M') N x m)
    (Category.comp_id z).symm).trans h

set_option maxHeartbeats 300000 in
private theorem transposeAt_tower_right (m : M) :
    towerTranspose A B C M (compositeTildeComparison A B C M) m = towerGenerator A C M m := by
  let f := specAlgebraMap B C
  let g := specAlgebraMap A B
  let j := specAlgebraMap A C
  let p : f ≫ g = j := specAlgebraMap_comp A B C
  let M₀ := towerBaseModule A M
  let N := towerTarget A C M
  let z := (tildeAlgebraMapPullback A C M).hom
  exact (transposeAt_comp_congr f g j p M₀ N z m).trans
    (transposeAt_tildeAlgebraMapPullback_hom A C M m)


private theorem transposeAt_composite_injective {A' B' : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec B') (g : Spec B' ⟶ Spec A') (M' : ModuleCat A') (N : X.Modules) :
    Function.Injective (fun j : (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback g).obj (tilde M')) ⟶ N =>
        transposeAt g M' ((Scheme.Modules.pushforward f).obj N)
          ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ j)) :=
  (transposeAt_injective g M' ((Scheme.Modules.pushforward f).obj N)).comp
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ N).injective

private theorem tildeTowerPullback :
    iteratedTildeComparison A B C M = compositeTildeComparison A B C M := by
  have hi : Function.Injective (towerTranspose A B C M) :=
    transposeAt_composite_injective (specAlgebraMap B C) (specAlgebraMap A B)
      (towerBaseModule A M) (towerTarget A C M)
  exact hi (funext fun m => (transposeAt_tower_left A B C M m).trans
    (transposeAt_tower_right A B C M m).symm)

private theorem inv_comp_compare {C : Type*} [Category C] {A B D E : C}
    (e : A ≅ B) (q : D ≅ E) (r : B ⟶ E) (z : A ⟶ D)
    (h : e.hom ≫ r = z ≫ q.hom) : e.inv ≫ z = r ≫ q.inv := by
  apply (cancel_mono q.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, e.inv_hom_id_assoc]

private theorem tildeTowerPullback_inverse :
    (towerFirstIso A B C M).inv ≫ towerCompositeHom A B C M =
      towerAfterFirst A B C M ≫ (towerLastIso A C M).inv :=
  inv_comp_compare (towerFirstIso A B C M) (towerLastIso A C M) (towerAfterFirst A B C M)
    (towerCompositeHom A B C M)
    ((tildeTowerPullback A B C M).trans (compositeTildeComparison_assoc A B C M).symm)

end TildeScalarTower

section PullbackSections

open TopCat TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {X Y Z : Scheme.{u}}

private def pullSection (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) :
    Γ(M, U) →ₛₗ[(f.appLE U V h).hom] Γ((Scheme.Modules.pullback f).obj M, V) where
  toFun x := ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M |>.app U <| x)
  map_add' x y := by
    let P := Scheme.Modules.pullback f
    let J := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
    let e := (P.obj M).presheaf.map (homOfLE h).op
    exact (congrArg (fun z => e z) ((J.app U).hom.map_add x y)).trans (e.hom.map_add _ _)
  map_smul' r x := by
    let P := Scheme.Modules.pullback f
    let J := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
    let e := (P.obj M).presheaf.map (homOfLE h).op
    exact (congrArg (fun z => e z) (J.app_smul (U := U) r x)).trans
      ((P.obj M).map_smul (homOfLE h) (f.app U r) (J.app U x))

private theorem pullSection_naturality (f : X ⟶ Y) {M N : Y.Modules} (i : M ⟶ N)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (x : Γ(M, U)) :
    pullSection f N U V h (i.app U x) =
      ((Scheme.Modules.pullback f).map i).app V (pullSection f M U V h x) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  let P := Scheme.Modules.pullback f
  have hn := congrArg (fun t => t.app U x) (A.unit.naturality i)
  change (A.unit.app N).app U (i.app U x) = (P.map i).app (f ⁻¹ᵁ U) ((A.unit.app M).app U x) at hn
  change (P.obj N).presheaf.map (homOfLE h).op ((A.unit.app N).app U (i.app U x)) =
    (P.map i).app V ((P.obj M).presheaf.map (homOfLE h).op ((A.unit.app M).app U x))
  rw [hn]
  exact ((P.map i).mapPresheaf.naturality_apply (homOfLE h).op _).symm

private theorem pullSection_restrict_source (f : X ⟶ Y) (M : Y.Modules)
    {U U' : Y.Opens} (p : U' ≤ U) {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U') (x : Γ(M, U)) :
    pullSection f M U' V h (M.presheaf.map (homOfLE p).op x) =
      pullSection f M U V (h.trans ((Opens.map f.base).monotone p)) x := by
  let P := Scheme.Modules.pullback f
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  change (P.obj M).presheaf.map (homOfLE h).op (η.app U' (M.presheaf.map (homOfLE p).op x)) =
    (P.obj M).presheaf.map _ (η.app U x)
  have hn := η.mapPresheaf.naturality_apply (homOfLE p).op x
  change η.app U' (M.presheaf.map (homOfLE p).op x) =
    ((Scheme.Modules.pushforward f).obj (P.obj M)).presheaf.map (homOfLE p).op (η.app U x) at hn
  rw [Scheme.Modules.pushforward_obj_presheaf_map] at hn
  rw [hn]
  let t : Γ(P.obj M, f ⁻¹ᵁ U) := η.app U x
  exact congrArg (fun j => j t)
    (((P.obj M).presheaf.map_comp ((Opens.map f.base).map (homOfLE p)).op (homOfLE h).op).symm)

private theorem pullSection_restrict_target (f : X ⟶ Y) (M : Y.Modules)
    {U : Y.Opens} {V V' : X.Opens} (p : V' ≤ V) (h : V ≤ f ⁻¹ᵁ U) (x : Γ(M, U)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE p).op (pullSection f M U V h x) =
      pullSection f M U V' (p.trans h) x := by
  simp only [pullSection, LinearMap.coe_mk, AddHom.coe_mk, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

private theorem pullbackUnit_comp_app (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens)
    (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U s =
      ((Scheme.Modules.pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj M)).app (g ⁻¹ᵁ U)
            (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U s)) := by
  let A := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let B := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let e := Scheme.Modules.pullbackComp f g
  have h := homEquiv_comp_mate A B e.inv (e.hom.app M)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Iso.inv_hom_id_app] at h
  have h' : A.unit.app M ≫ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).map
      (e.hom.app M) ≫ (Scheme.Modules.pushforwardComp f g).hom.app _ = B.unit.app M := by
    have he : B.homEquiv _ _ (𝟙 ((Scheme.Modules.pullback (f ≫ g)).obj M)) =
        B.unit.app M := by
      rw [B.homEquiv_unit, (Scheme.Modules.pushforward (f ≫ g)).map_id]
      exact Category.comp_id _
    rw [he, A.homEquiv_unit, Category.assoc] at h
    exact h
  rw [Adjunction.comp_unit_app] at h'
  exact congrArg (fun t => t.app U s) h'.symm

private theorem pullSection_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    {U : Z.Opens} {V : Y.Opens} {W : X.Opens}
    (h : V ≤ g ⁻¹ᵁ U) (h' : W ≤ f ⁻¹ᵁ V) (x : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app W
        (pullSection f ((Scheme.Modules.pullback g).obj M) V W h' (pullSection g M U V h x)) =
      pullSection (f ≫ g) M U W (h'.trans ((Opens.map f.base).monotone h)) x := by
  let P := Scheme.Modules.pullback g
  let Q := Scheme.Modules.pullback f
  let e := (Scheme.Modules.pullbackComp f g).hom.app M
  let ix := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U x
  have hg : pullSection g M U V h x = (P.obj M).presheaf.map (homOfLE h).op ix := rfl
  rw [hg, pullSection_restrict_source]
  let t := h'.trans ((Opens.map f.base).monotone h)
  let u := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (P.obj M)).app (g ⁻¹ᵁ U) ix
  change e.app W ((Q.obj (P.obj M)).presheaf.map (homOfLE t).op u) = _
  exact (e.mapPresheaf.naturality_apply (homOfLE t).op u).trans
    (congrArg (fun z => ((Scheme.Modules.pullback (f ≫ g)).obj M).presheaf.map (homOfLE t).op z)
      (pullbackUnit_comp_app f g M U x).symm)

private theorem pullSection_open (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (V : X.Opens) :
    Function.Bijective (pullSection f M (f ''ᵁ V) V (f.preimage_image_eq V).ge) := by
  let A := Scheme.Modules.restrictAdjunction f
  let B := Scheme.Modules.pullbackPushforwardAdjunction f
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  have h := A.homEquiv_leftAdjointUniq_hom_app B M
  rw [A.homEquiv_unit] at h
  have h₀ := congrArg (fun t => t.app (f ''ᵁ V)) h
  change (A.unit.app M).app (f ''ᵁ V) ≫ (e.hom.app M).app (f ⁻¹ᵁ (f ''ᵁ V)) =
    (B.unit.app M).app (f ''ᵁ V) at h₀
  have hf : f ''ᵁ (f ⁻¹ᵁ (f ''ᵁ V)) = f ''ᵁ V := by rw [f.preimage_image_eq]
  have hunit : IsIso ((A.unit.app M).app (f ''ᵁ V)) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    exact inferInstanceAs (IsIso (M.presheaf.map (eqToHom hf).op))
  let r := ((Scheme.Modules.pullback f).obj M).presheaf.map
    (homOfLE (f.preimage_image_eq V).ge).op
  have : IsIso r := inferInstanceAs (IsIso (((Scheme.Modules.pullback f).obj M).presheaf.map
    (eqToHom (f.preimage_image_eq V).symm).op))
  have hbij (φ : Γ(M, f ''ᵁ V) ⟶ Γ((Scheme.Modules.pullback f).obj M, V)) [IsIso φ] :
      Function.Bijective φ :=
    ⟨(AddCommGrpCat.mono_iff_injective _).mp inferInstance,
      (AddCommGrpCat.epi_iff_surjective _).mp inferInstance⟩
  have hb := hbij (((A.unit.app M).app (f ''ᵁ V) ≫
    (e.hom.app M).app (f ⁻¹ᵁ (f ''ᵁ V))) ≫ r)
  rw [h₀] at hb
  exact hb

end PullbackSections

section SheafSections

open TopCat TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {M N E : X.Modules}

private abbrev sectionRange (i : M ⟶ E) (U : X.Opens) :
    Submodule Γ(X, U) Γ(E, U) :=
  (i.val.app (op U)).hom.range

private theorem sectionMap_injective (i : M ⟶ E) [Mono i] (U : X.Opens) :
    Function.Injective (i.app U) :=
  (ModuleCat.mono_iff_injective _).mp
    (inferInstanceAs (Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map i)))

private theorem mem_sectionRange_of_local (i : M ⟶ E) [Mono i] (U : X.Opens) (s : Γ(E, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (a : V ≤ U), x ∈ V ∧
      E.presheaf.map (homOfLE a).op s ∈ sectionRange i V) :
    s ∈ sectionRange i U := by
  let B := CategoryTheory.forget AddCommGrpCat.{u}
  let f := Functor.whiskerRight i.mapPresheaf B
  have hf : Mono f := by
    rw [NatTrans.mono_iff_mono_app]
    intro V
    change Mono ((B.map (i.app V.unop)))
    exact (CategoryTheory.mono_iff_injective _).mpr (sectionMap_injective i V.unop)
  let J := Opens.grothendieckTopology X
  let F := Subfunctor.range f
  have hM : Presieve.IsSheaf J (M.presheaf ⋙ B) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf
  have hE : Presieve.IsSheaf J (E.presheaf ⋙ B) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.HasSheafCompose.isSheaf _ E.isSheaf
  have hN : Presieve.IsSheaf J F.toFunctor := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_of_iso_iff (J := J) (asIso (Subfunctor.toRange f))).mp
      ((isSheaf_iff_isSheaf_of_type _ _).mpr hM)
  have hcov : F.sieveOfSection (U := op U) s ∈ J U := by
    intro x hx
    obtain ⟨V, a, hxV, hs⟩ := h x hx
    exact ⟨V, homOfLE a, hs, hxV⟩
  exact (Subfunctor.isSheaf_iff F hE).mp hN (op U) s hcov

private def sectionRangeFactor (i : M ⟶ E) (j : N ⟶ E) [Mono j] (U : X.Opens)
    (h : sectionRange i U ≤ sectionRange j U) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
  (LinearEquiv.ofInjective (j.val.app (op U)).hom (sectionMap_injective j U)).symm.toLinearMap.comp
    ((i.val.app (op U)).hom.codRestrict _ fun s => h ⟨s, rfl⟩)

private theorem sectionRangeFactor_fac (i : M ⟶ E) (j : N ⟶ E) [Mono j] (U : X.Opens)
    (h : sectionRange i U ≤ sectionRange j U) (s : Γ(M, U)) :
    j.app U (sectionRangeFactor i j U h s) = i.app U s := by
  let e := LinearEquiv.ofInjective (j.val.app (op U)).hom (sectionMap_injective j U)
  let t : sectionRange j U := ⟨i.app U s, h ⟨s, rfl⟩⟩
  change (e (e.symm t)).val = t.val
  exact congrArg Subtype.val (e.apply_symm_apply t)

private def factorOfSectionRangeLe (i : M ⟶ E) (j : N ⟶ E) [Mono j]
    (h : ∀ U, sectionRange i U ≤ sectionRange j U) : M ⟶ N where
  val :=
    { app := fun U => ModuleCat.ofHom (sectionRangeFactor i j U.unop (h U.unop))
      naturality := by
        intro U V f
        ext s
        let a (V : X.Opens) := sectionRangeFactor i j V (h V)
        apply sectionMap_injective j V.unop
        change j.app V.unop (a V.unop (M.presheaf.map f s)) =
          j.app V.unop (N.presheaf.map f (a U.unop s))
        calc
          _ = i.app V.unop (M.presheaf.map f s) := sectionRangeFactor_fac i j _ _ _
          _ = E.presheaf.map f (i.app U.unop s) := i.mapPresheaf.naturality_apply f s
          _ = E.presheaf.map f (j.app U.unop (a U.unop s)) :=
            congrArg (fun z => E.presheaf.map f z) (sectionRangeFactor_fac i j _ _ _).symm
          _ = _ := (j.mapPresheaf.naturality_apply f _).symm }

private theorem factorOfSectionRangeLe_fac (i : M ⟶ E) (j : N ⟶ E) [Mono j]
    (h : ∀ U, sectionRange i U ≤ sectionRange j U) :
    factorOfSectionRangeLe i j h ≫ j = i := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  exact sectionRangeFactor_fac i j U (h U) s

private theorem subobject_eq_of_sectionRanges (A B : Subobject E)
    (h : ∀ U, sectionRange A.arrow U = sectionRange B.arrow U) : A = B := by
  refine le_antisymm ?_ ?_
  · exact Subobject.le_of_comm _ (factorOfSectionRangeLe_fac A.arrow B.arrow fun U => (h U).le)
  · exact Subobject.le_of_comm _ (factorOfSectionRangeLe_fac B.arrow A.arrow fun U => (h U).ge)

private theorem sectionRange_mk {i : M ⟶ E} [Mono i] (U : X.Opens) :
    sectionRange (Subobject.mk i).arrow U = sectionRange i U := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have h := congrArg (fun f => (F.map f).hom.range) (Subobject.underlyingIso_hom_comp_eq_mk i)
  rw [F.map_comp, ModuleCat.hom_comp, LinearMap.range_comp, LinearMap.range_eq_top.mpr
    ((ModuleCat.epi_iff_surjective (F.map (Subobject.underlyingIso i).hom)).mp inferInstance),
    Submodule.map_top] at h
  exact h.symm

end SheafSections

section AffineLineSheafNaturality

open TopCat

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 120000
set_option maxRecDepth 300

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W]
variable {R T : TestAlgebra k}

private theorem towerFirstIso_inv_explicit (A B C M : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [AddCommGroup M] [Module A M] :
    (towerFirstIso A B C M).inv =
      (Scheme.Modules.pullback (specAlgebraMap B C)).map (tildeAlgebraMapPullback A B M).inv := rfl

private def towerCompositeIso (A B C M : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [AddCommGroup M] [Module A M] :
    towerSource A B C M ≅ (Scheme.Modules.pullback (specAlgebraMap A C)).obj
      (tilde (towerBaseModule A M)) :=
  ((Scheme.Modules.pullbackComp (specAlgebraMap B C) (specAlgebraMap A B)) ≪≫
    Scheme.Modules.pullbackCongr (specAlgebraMap_comp A B C)).app (tilde (towerBaseModule A M))

private theorem towerCompositeIso_hom (A B C M : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [AddCommGroup M] [Module A M] :
    (towerCompositeIso A B C M).hom = towerCompositeHom A B C M :=
  NatTrans.comp_app _ _ _

private theorem pullbackAmbientIso_tower (a : R ⟶ T) :
    let : Algebra R T := a.hom.toAlgebra
    let : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
    pullbackAmbientIso k W ((testSpec k).map a.op) =
      towerCompositeIso k (R : Type u) (T : Type u) W := rfl

private theorem towerHom_over (a : R ⟶ T) :
    let : Algebra R T := a.hom.toAlgebra
    let : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
    towerCompositeHom k (R : Type u) (T : Type u) W =
      (pullbackAmbientIso k W ((testSpec k).map a.op)).hom := by
  let : Algebra R T := a.hom.toAlgebra
  let : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  rw [pullbackAmbientIso_tower, towerCompositeIso_hom]

private theorem towerInv_over (a : R ⟶ T) :
    let : Algebra R T := a.hom.toAlgebra
    (towerFirstIso k (R : Type u) (T : Type u) W).inv =
    (Scheme.Modules.pullback ((testSpec k).map a.op).left).map (affineConstantBundleIso k W R).hom := by
  let : Algebra R T := a.hom.toAlgebra
  exact towerFirstIso_inv_explicit k (R : Type u) (T : Type u) W

private theorem towerLastInv_over (T : TestAlgebra k) :
    (towerLastIso k (T : Type u) W).inv = (affineConstantBundleIso k W T).hom := rfl

private theorem affineConstantBundleIso_pullback (a : R ⟶ T) :
    let : Algebra R T := a.hom.toAlgebra
    let : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
    (Scheme.Modules.pullback ((testSpec k).map a.op).left).map (affineConstantBundleIso k W R).hom ≫
      (pullbackAmbientIso k W ((testSpec k).map a.op)).hom =
    ((tildeAlgebraMapPullback (R : Type u) T (R ⊗[k] W)).hom ≫
      (tilde.functor (CommRingCat.of T)).map
        (TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T W).toModuleIso.hom) ≫
      (affineConstantBundleIso k W T).hom := by
  let : Algebra R T := a.hom.toAlgebra
  let : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  let U := (R : Type u)
  let V := (T : Type u)
  let i := (towerFirstIso k U V W).inv
  let c := towerCompositeHom k U V W
  let j := towerAfterFirst k U V W
  let z := (towerLastIso k V W).inv
  let G := Scheme.Modules.pullback ((testSpec k).map a.op).left
  let d := (pullbackAmbientIso k W ((testSpec k).map a.op)).hom
  have hi : G.map (affineConstantBundleIso k W R).hom = i := (towerInv_over (W := W) a).symm
  have hc : d = c := (towerHom_over (W := W) a).symm
  have hz : z = (affineConstantBundleIso k W T).hom := towerLastInv_over T
  have hp : i ≫ c = j ≫ z := tildeTowerPullback_inverse k U V W
  refine (congrArg (· ≫ d) hi).trans ?_
  refine (congrArg (i ≫ ·) hc).trans (hp.trans ?_)
  exact congrArg (j ≫ ·) hz

private theorem pullback_tildeInclusion (a : R ⟶ T) (L : AffineLine k W R) :
    let P := Scheme.Modules.pullback ((testSpec k).map a.op).left
    let L' := affineLineBaseChange a L
    ∃ e : P.obj (tilde (R := CommRingCat.of R) (ModuleCat.of R L.submodule)) ≅
        tilde (R := CommRingCat.of T) (ModuleCat.of T L'.submodule),
      P.map (tildeInclusion L.submodule ≫ (affineConstantBundleIso k W R).hom) ≫
          (pullbackAmbientIso k W ((testSpec k).map a.op)).hom =
        e.hom ≫ tildeInclusion L'.submodule ≫ (affineConstantBundleIso k W T).hom := by
  let : Algebra R T := a.hom.toAlgebra
  let : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  let P := Scheme.Modules.pullback ((testSpec k).map a.op).left
  let L' := affineLineBaseChange a L
  let C := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T W
  let i := L.submodule.subtype.baseChange T
  let j := C.toLinearMap.comp i
  have hcomp : ((lineRetraction L).baseChange T).comp i = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, lineRetraction_comp_subtype, LinearMap.baseChange_id]
  have hj : Function.Injective j := C.injective.comp
    (LinearMap.injective_of_comp_eq_id _ _ hcomp)
  let e : T ⊗[R] L.submodule ≃ₗ[T] L'.submodule := LinearEquiv.ofInjective j hj
  let H := tilde.functor (CommRingCat.of T)
  let ψ := tildeAlgebraMapPullback (R : Type u) T (↥L.submodule)
  let c := tildeAlgebraMapPullback (R : Type u) T (R ⊗[k] W)
  let r := H.map (ModuleCat.ofHom i)
  let m := H.map C.toModuleIso.hom
  let z := (affineConstantBundleIso k W T).hom
  let em : ModuleCat.of T (T ⊗[R] L.submodule) ≅ ModuleCat.of T L'.submodule := e.toModuleIso
  let n := H.map em.hom
  let d := ψ ≪≫ H.mapIso em
  have hmn : r ≫ m = n ≫ tildeInclusion L'.submodule := by
    change H.map (ModuleCat.ofHom i) ≫ H.map C.toModuleIso.hom =
      H.map em.hom ≫ H.map (ModuleCat.ofHom L'.submodule.subtype)
    rw [← H.map_comp, ← H.map_comp]
    rfl
  refine ⟨d, ?_⟩
  have h₁ := affineConstantBundleIso_pullback (W := W) a
  have h₂ := tildeAlgebraMapPullback_naturality (A := (R : Type u)) (B := (T : Type u))
    (M := ↥L.submodule) (N := R ⊗[k] W) L.submodule.subtype
  change P.map (tildeInclusion L.submodule ≫ (affineConstantBundleIso k W R).hom) ≫ _ =
    (ψ.hom ≫ n) ≫ tildeInclusion L'.submodule ≫ z
  calc
    _ = P.map (tildeInclusion L.submodule) ≫
        P.map (affineConstantBundleIso k W R).hom ≫
          (pullbackAmbientIso k W ((testSpec k).map a.op)).hom := P.map_comp_assoc _ _ _
    _ = P.map (tildeInclusion L.submodule) ≫ (c.hom ≫ m) ≫ z :=
      congrArg (P.map (tildeInclusion L.submodule) ≫ ·) h₁
    _ = P.map (tildeInclusion L.submodule) ≫ c.hom ≫ m ≫ z :=
      congrArg (P.map (tildeInclusion L.submodule) ≫ ·) (Category.assoc c.hom m z)
    _ = (ψ.hom ≫ r) ≫ m ≫ z := (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ m ≫ z) h₂)
    _ = ψ.hom ≫ (r ≫ m) ≫ z := by simp only [Category.assoc]
    _ = ψ.hom ≫ (n ≫ tildeInclusion L'.submodule) ≫ z := congrArg (fun v => ψ.hom ≫ v ≫ z) hmn
    _ = _ := by simp only [Category.assoc]

section InclusionIsomorphisms

variable {C D : Type*} [Category C] [Category D]
variable {A B E : C}

private def SameInclusion (i : A ⟶ E) (j : B ⟶ E) : Prop :=
  ∃ e : A ≅ B, i = e.hom ≫ j

private theorem SameInclusion.symm {i : A ⟶ E} {j : B ⟶ E} (h : SameInclusion i j) :
    SameInclusion j i := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [he, Iso.symm_hom, e.inv_hom_id_assoc]

private theorem SameInclusion.trans {A' : C} {i : A ⟶ E} {j : B ⟶ E} {l : A' ⟶ E}
    (h : SameInclusion i j) (h' : SameInclusion j l) : SameInclusion i l := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := h'
  exact ⟨e ≪≫ f, he.trans ((congrArg (e.hom ≫ ·) hf).trans (Category.assoc _ _ _).symm)⟩

private theorem SameInclusion.map (F : C ⥤ D) {E' : D} (u : F.obj E ⟶ E')
    {i : A ⟶ E} {j : B ⟶ E} (h : SameInclusion i j) :
    SameInclusion (F.map i ≫ u) (F.map j ≫ u) := by
  obtain ⟨e, he⟩ := h
  exact ⟨F.mapIso e, (congrArg (fun a => F.map a ≫ u) he).trans (F.map_comp_assoc _ _ _)⟩

end InclusionIsomorphisms

private theorem affineSheafMatch_inclusion (L : AffineLine k W R)
    (M : LineSubbundle k W ((testSpec k).obj (op R))) (hM : AffineSheafMatch L M) :
    SameInclusion (tildeInclusion L.submodule ≫ (affineConstantBundleIso k W R).hom) M.val.arrow := hM

private def AffineInclusionComparison (f : Points ((testSpec k).obj (op R)) T)
    (L : AffineLine k W R) (L' : AffineLine k W T) : Prop :=
    let i := tildeInclusion L.submodule ≫ (affineConstantBundleIso k W R).hom
    let j := tildeInclusion L'.submodule ≫ (affineConstantBundleIso k W T).hom
    SameInclusion ((Scheme.Modules.pullback f.left).map i ≫ (pullbackAmbientIso k W f).hom) j

private theorem pullback_affineInclusionComparison (a : R ⟶ T) (L : AffineLine k W R) :
    AffineInclusionComparison ((testSpec k).map a.op) L (affineLineBaseChange a L) :=
  pullback_tildeInclusion a L

private theorem isPullbackLine_of_sameInclusion {S T : SchemeOver k} (f : T ⟶ S)
    (M : LineSubbundle k W S) (N : LineSubbundle k W T)
    (h : SameInclusion ((Scheme.Modules.pullback f.left).map M.val.arrow ≫
      (pullbackAmbientIso k W f).hom) N.val.arrow) : IsPullbackLine k W f M N := h

set_option maxHeartbeats 130000 in
private theorem affineSheafMatch_of_comparison (f : Points ((testSpec k).obj (op R)) T)
    (L : AffineLine k W R) (L' : AffineLine k W T)
    (M : LineSubbundle k W ((testSpec k).obj (op R)))
    (N : LineSubbundle k W ((testSpec k).obj (op T)))
    (hM : AffineSheafMatch L M) (hN : AffineSheafMatch L' N)
    (hc : AffineInclusionComparison f L L') : IsPullbackLine k W f M N := by
  let P := Scheme.Modules.pullback f.left
  let c := (pullbackAmbientIso k W f).hom
  have hs := affineSheafMatch_inclusion L M hM
  have ht := affineSheafMatch_inclusion L' N hN
  have hu := hs.symm.map P c
  have hv := SameInclusion.trans hc ht
  exact isPullbackLine_of_sameInclusion f M N (hu.trans hv)

private theorem affineSheafMatch_pullback (a : R ⟶ T) (L : AffineLine k W R)
    (M : LineSubbundle k W ((testSpec k).obj (op R)))
    (N : LineSubbundle k W ((testSpec k).obj (op T)))
    (hM : AffineSheafMatch L M) (hN : AffineSheafMatch (affineLineBaseChange a L) N) :
    IsPullbackLine k W ((testSpec k).map a.op) M N :=
  affineSheafMatch_of_comparison ((testSpec k).map a.op) L (affineLineBaseChange a L) M N hM hN
    (pullback_affineInclusionComparison a L)


variable [Module.Finite k W]

/-- On spectra, pullback of the associated line is the base change of the affine module line. -/
theorem affineLineSheafEquiv_natural (a : R ⟶ T) (L : AffineLine k W R) :
    pullbackLine ((testSpec k).map a.op) (affineLineSheafEquiv R L) =
      affineLineSheafEquiv T (affineLineBaseChange a L) :=
  (pullbackLine_eq_iff _ _ _).mpr <|
    affineSheafMatch_pullback a L _ _ (affineLineSheafEquiv_spec L)
      (affineLineSheafEquiv_spec (affineLineBaseChange a L))

theorem affineLineSheafEquiv_family {S : SchemeOver k} (L : LineFamily k W S)
    (a : Points S R) (f : Points ((testSpec k).obj (op R)) T) :
    pullbackLine f (affineLineSheafEquiv R (L.line R a)) =
      affineLineSheafEquiv T (L.line T (f ≫ a)) := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let g := (F.preimage f).unop
  have hg : (testSpec k).map g.op = f := F.map_preimage f
  rw [← hg, affineLineSheafEquiv_natural]
  congr 1
  apply affineLine_ext
  rw [affineLineBaseChange_submodule]
  exact (L.compatible g a).symm

end AffineLineSheafNaturality

section BundleSections

open TopCat TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W]
variable {S T D : SchemeOver k}

private def pullBundleSectionLinearMap (f : T ⟶ S) (U : S.left.Opens) (V : T.left.Opens)
    (h : V ≤ f.left ⁻¹ᵁ U) :
    Γ(constantBundle k W S, U) →ₛₗ[(f.left.appLE U V h).hom] Γ(constantBundle k W T, V) :=
  ((pullbackAmbientIso k W f).hom.val.app (op V)).hom.comp
    (pullSection f.left (constantBundle k W S) U V h)

private def pullBundleSection (f : T ⟶ S) (U : S.left.Opens) (V : T.left.Opens)
    (h : V ≤ f.left ⁻¹ᵁ U) (s : Γ(constantBundle k W S, U)) : Γ(constantBundle k W T, V) :=
  (pullbackAmbientIso k W f).hom.app V (pullSection f.left (constantBundle k W S) U V h s)

private theorem pullBundleSection_restrict_source (f : T ⟶ S) {U U' : S.left.Opens}
    (p : U' ≤ U) {V : T.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U')
    (s : Γ(constantBundle k W S, U)) :
    pullBundleSection f U' V h ((constantBundle k W S).presheaf.map (homOfLE p).op s) =
      pullBundleSection f U V (h.trans ((Opens.map f.left.base).monotone p)) s :=
  congrArg (fun z => (pullbackAmbientIso k W f).hom.app V z)
    (pullSection_restrict_source f.left (constantBundle k W S) p h s)

private theorem pullBundleSection_comp (f : T ⟶ S) (g : D ⟶ T)
    {U : S.left.Opens} {V : T.left.Opens} {B : D.left.Opens}
    (h : V ≤ f.left ⁻¹ᵁ U) (h' : B ≤ g.left ⁻¹ᵁ V) (s : Γ(constantBundle k W S, U)) :
    pullBundleSection g V B h' (pullBundleSection f U V h s) =
      pullBundleSection (g ≫ f) U B (h'.trans ((Opens.map g.left.base).monotone h)) s := by
  let A := constantBundle k W S
  let F := Scheme.Modules.pullback f.left
  let G := Scheme.Modules.pullback g.left
  let a := (pullbackAmbientIso k W f).hom
  let b := (pullbackAmbientIso k W g).hom
  let c := (pullbackAmbientIso k W (g ≫ f)).hom
  let e := (Scheme.Modules.pullbackComp g.left f.left).hom.app A
  let t := pullSection f.left A U V h s
  let z := pullSection g.left (F.obj A) V B h' t
  change b.app B (pullSection g.left _ V B h' (a.app V t)) = _
  rw [pullSection_naturality]
  change (G.map a ≫ b).app B z = _
  rw [pullbackAmbientIso_comp_hom (W := W)]
  change c.app B (e.app B z) = _
  exact congrArg (fun x => c.app B x) (pullSection_comp g.left f.left A h h' s)

private theorem pullBundleSection_open (f : T ⟶ S) [IsOpenImmersion f.left] (V : T.left.Opens) :
    Function.Bijective (pullBundleSection (W := W) f (f.left ''ᵁ V) V (f.left.preimage_image_eq V).ge) := by
  let e := (pullbackAmbientIso k W f).hom.app V
  have he : Function.Bijective e :=
    ⟨(AddCommGrpCat.mono_iff_injective _).mp inferInstance,
      (AddCommGrpCat.epi_iff_surjective _).mp inferInstance⟩
  exact he.comp (pullSection_open f.left (constantBundle k W S) V)

private theorem pullBundleSection_mem (f : T ⟶ S)
    {M : S.left.Modules} {N : T.left.Modules}
    (i : M ⟶ constantBundle k W S) (j : N ⟶ constantBundle k W T)
    (d : (Scheme.Modules.pullback f.left).obj M ≅ N)
    (hd : (Scheme.Modules.pullback f.left).map i ≫ (pullbackAmbientIso k W f).hom = d.hom ≫ j)
    {U : S.left.Opens} {V : T.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U) (s : Γ(constantBundle k W S, U))
    (hs : s ∈ sectionRange i U) : pullBundleSection f U V h s ∈ sectionRange j V := by
  obtain ⟨t, rfl⟩ := hs
  let x := pullSection f.left M U V h t
  refine ⟨d.hom.app V x, ?_⟩
  change (d.hom ≫ j).app V x = (pullbackAmbientIso k W f).hom.app V
    (pullSection f.left _ U V h (i.app U t))
  refine (congrArg (fun z => z.app V x) hd.symm).trans ?_
  exact congrArg (fun z => (pullbackAmbientIso k W f).hom.app V z)
    (pullSection_naturality f.left i U V h t).symm

private theorem pullBundleSection_mem_iff_open (f : T ⟶ S) [IsOpenImmersion f.left]
    {M : S.left.Modules} {N : T.left.Modules}
    (i : M ⟶ constantBundle k W S) (j : N ⟶ constantBundle k W T)
    (d : (Scheme.Modules.pullback f.left).obj M ≅ N)
    (hd : (Scheme.Modules.pullback f.left).map i ≫ (pullbackAmbientIso k W f).hom = d.hom ≫ j)
    (V : T.left.Opens) (s : Γ(constantBundle k W S, f.left ''ᵁ V)) :
    pullBundleSection f (f.left ''ᵁ V) V (f.left.preimage_image_eq V).ge s ∈ sectionRange j V ↔
      s ∈ sectionRange i (f.left ''ᵁ V) := by
  let U := f.left ''ᵁ V
  let h : V ≤ f.left ⁻¹ᵁ U := (f.left.preimage_image_eq V).ge
  refine ⟨?_, pullBundleSection_mem f i j d hd h s⟩
  rintro ⟨x, hx⟩
  let y := d.inv.app V x
  obtain ⟨z, hz⟩ := (pullSection_open f.left M V).surjective y
  have hr : d.hom.app V y = x := by
    change (d.inv ≫ d.hom).app V x = _
    rw [d.inv_hom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
  refine ⟨z, (pullBundleSection_open (W := W) f V).injective ?_⟩
  calc
    pullBundleSection f U V h (i.app U z) =
        ( (Scheme.Modules.pullback f.left).map i ≫ (pullbackAmbientIso k W f).hom).app V y := by
      change (pullbackAmbientIso k W f).hom.app V (pullSection f.left _ U V h (i.app U z)) = _
      rw [pullSection_naturality, hz]
      rfl
    _ = j.app V x := by rw [hd, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hr]
    _ = _ := hx

private theorem mono_open_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M E : Y.Modules} (i : M ⟶ E) [Mono i] : Mono ((Scheme.Modules.pullback f).map i) := by
  let F := Scheme.Modules.restrictFunctor f
  let t := Scheme.Modules.restrictFunctorIsoPullback f
  have h : Mono (F.map i) := by
    apply (SheafOfModules.forget _).mono_of_mono_map
    exact PresheafOfModules.mono_of_injective fun V => sectionMap_injective i (f ''ᵁ V.unop)
  have h' : Mono (t.hom.app M ≫ (Scheme.Modules.pullback f).map i) :=
    t.hom.naturality i ▸ (inferInstanceAs (Mono (F.map i ≫ t.hom.app E)))
  have he : t.inv.app M ≫ t.hom.app M ≫ (Scheme.Modules.pullback f).map i =
    (Scheme.Modules.pullback f).map i := t.inv_hom_id_app_assoc _ _
  exact he ▸ (inferInstanceAs (Mono (t.inv.app M ≫ t.hom.app M ≫ (Scheme.Modules.pullback f).map i)))

private structure AffineOpenChart (S : SchemeOver k) where
  R : TestAlgebra k
  map : Points S R
  isOpen : IsOpenImmersion map.left

attribute [local instance] AffineOpenChart.isOpen

private abbrev AffineOpenChart.image (a : AffineOpenChart S) : S.left.Opens :=
  a.map.left ''ᵁ ⊤

private theorem exists_affineOpenChart {U : S.left.Opens} {x : S.left} (hx : x ∈ U) :
    ∃ a : AffineOpenChart S, x ∈ a.image ∧ a.image ≤ U := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  let : IsAffine (overAlong (S := S) V.ι).left := hV
  let p := affinePresentation (overAlong (S := S) V.ι)
  let f := p.2.hom ≫ overHom (S := S) V.ι
  have hf : IsOpenImmersion f.left := by
    change IsOpenImmersion (p.2.hom.left ≫ V.ι)
    infer_instance
  let a : AffineOpenChart S := ⟨p.1, f, hf⟩
  have he : a.image = V := by
    change f.left ''ᵁ ⊤ = V
    rw [Scheme.Hom.image_top_eq_opensRange]
    change (p.2.hom.left ≫ V.ι).opensRange = V
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_of_isIso, Scheme.Opens.ι_image_top]
  exact ⟨a, he.symm ▸ hxV, he.symm ▸ hVU⟩

private theorem AffineOpenChart.le_preimage (a : AffineOpenChart S) {U : S.left.Opens}
    (h : a.image ≤ U) : ⊤ ≤ a.map.left ⁻¹ᵁ U := by
  intro x _
  exact h ⟨x, trivial, rfl⟩

private def chartSection (a : AffineOpenChart S) {U : S.left.Opens} (h : a.image ≤ U) :
    Γ(constantBundle k W S, U) →
      Γ(constantBundle k W ((testSpec k).obj (op a.R)), (⊤ : ((testSpec k).obj (op a.R)).left.Opens)) :=
  pullBundleSection a.map U ⊤ (a.le_preimage h)

private theorem chartSection_restrict (a : AffineOpenChart S) {U V : S.left.Opens}
    (p : V ≤ U) (h : a.image ≤ V) (s : Γ(constantBundle k W S, U)) :
    chartSection a h ((constantBundle k W S).presheaf.map (homOfLE p).op s) =
      chartSection a (h.trans p) s :=
  pullBundleSection_restrict_source a.map p (a.le_preimage h) s

private theorem mem_sectionRange_of_charts {M : S.left.Modules}
    (i : M ⟶ constantBundle k W S) [Mono i] {U : S.left.Opens} (s : Γ(constantBundle k W S, U))
    (h : ∀ x ∈ U, ∃ (a : AffineOpenChart S) (ha : a.image ≤ U), x ∈ a.image ∧
      chartSection a ha s ∈ sectionRange
        ((Scheme.Modules.pullback a.map.left).map i ≫ (pullbackAmbientIso k W a.map).hom) ⊤) :
    s ∈ sectionRange i U := by
  apply mem_sectionRange_of_local i U s
  intro x hx
  obtain ⟨a, ha, hx', hs⟩ := h x hx
  refine ⟨a.image, ha, hx', ?_⟩
  let j := (Scheme.Modules.pullback a.map.left).map i ≫ (pullbackAmbientIso k W a.map).hom
  apply (pullBundleSection_mem_iff_open a.map i j (Iso.refl _) (Category.id_comp _).symm ⊤ _).mp
  change chartSection a le_rfl ((constantBundle k W S).presheaf.map (homOfLE ha).op s) ∈ _
  exact (chartSection_restrict a ha le_rfl s).symm ▸ hs

private theorem sectionRange_eq_of_comm {X : Scheme.{u}} {M N E : X.Modules}
    (i : M ⟶ E) (j : N ⟶ E) (e : M ≅ N) (h : i = e.hom ≫ j) (U : X.Opens) :
    sectionRange i U = sectionRange j U := by
  ext s
  change (∃ x, i.app U x = s) ↔ ∃ y, j.app U y = s
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨e.hom.app U x, (congrArg (fun f => f.app U x) h).symm.trans hx⟩
  · rintro ⟨y, hy⟩
    have hid : e.hom.app U (e.inv.app U y) = y := by
      change (e.inv ≫ e.hom).app U y = _
      rw [e.inv_hom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
    refine ⟨e.inv.app U y, ?_⟩
    rw [h, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hid, hy]

private theorem lineSubbundle_ext_of_charts (L N : LineSubbundle k W S)
    (h : ∀ x : S.left, ∃ a : AffineOpenChart S, x ∈ a.image ∧
      pullbackLine a.map L = pullbackLine a.map N) : L = N := by
  apply Subtype.ext
  apply subobject_eq_of_sectionRanges
  intro U
  suffices hle : ∀ (M₁ M₂ : LineSubbundle k W S),
    (∀ x : S.left, ∃ a : AffineOpenChart S, x ∈ a.image ∧
      pullbackLine a.map M₁ = pullbackLine a.map M₂) →
      sectionRange M₁.val.arrow U ≤ sectionRange M₂.val.arrow U from
    le_antisymm (hle L N h) (hle N L (fun x => by obtain ⟨a, ha, h'⟩ := h x; exact ⟨a, ha, h'.symm⟩))
  intro M₁ M₂ h' s hs
  apply mem_sectionRange_of_local M₂.val.arrow U s
  intro x hx
  obtain ⟨a, hxa, heq⟩ := h' x
  let V := U ⊓ a.image
  have hpre := a.map.left.image_preimage_eq_opensRange_inf V
  have he : a.map.left ''ᵁ (a.map.left ⁻¹ᵁ V) = V := by
    rw [hpre, ← a.map.left.image_top_eq_opensRange, inf_eq_right.mpr inf_le_right]
  let V' := a.map.left ⁻¹ᵁ V
  have hle₀ : a.map.left ''ᵁ V' ≤ U := he.le.trans inf_le_left
  refine ⟨a.map.left ''ᵁ V', hle₀, he.symm ▸ (show x ∈ V from ⟨hx, hxa⟩), ?_⟩
  let t := (constantBundle k W S).presheaf.map (homOfLE hle₀).op s
  have ht : t ∈ sectionRange M₁.val.arrow (a.map.left ''ᵁ V') := by
    obtain ⟨z, rfl⟩ := hs
    exact ⟨(Subobject.underlying.obj M₁.val).presheaf.map (homOfLE hle₀).op z,
      M₁.val.arrow.mapPresheaf.naturality_apply (homOfLE hle₀).op z⟩
  obtain ⟨d₁, hd₁⟩ := isPullbackLine_pullbackLine a.map M₁
  obtain ⟨d₂, hd₂⟩ := (pullbackLine_eq_iff _ _ _).mp heq.symm
  exact (pullBundleSection_mem_iff_open a.map _ _ d₂ hd₂ V' t).mp
    ((pullBundleSection_mem_iff_open a.map _ _ d₁ hd₁ V' t).mpr ht)

end BundleSections

section SheafGluing

open TopCat TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 160000

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
variable {S : SchemeOver k}

attribute [local instance] AffineOpenChart.isOpen

private abbrev localLine (L : LineFamily k W S) {R : TestAlgebra k} (a : Points S R) :=
  affineLineSheafEquiv R (L.line R a)

private theorem localLine_pull (L : LineFamily k W S) {R T : TestAlgebra k}
    (a : Points S R) (b : Points ((testSpec k).obj (op R)) T) :
    IsPullbackLine k W b (localLine L a) (localLine L (b ≫ a)) :=
  (pullbackLine_eq_iff _ _ _).mp (affineLineSheafEquiv_family L a b)

private def restrictedChart {R : TestAlgebra k} (a : Points S R) [IsOpenImmersion a.left]
    (b : AffineOpenChart ((testSpec k).obj (op R))) : AffineOpenChart S :=
  ⟨b.R, b.map ≫ a, by change IsOpenImmersion (b.map.left ≫ a.left); infer_instance⟩

private theorem restrictedChart_image {R : TestAlgebra k} (a : Points S R)
    [IsOpenImmersion a.left] (b : AffineOpenChart ((testSpec k).obj (op R))) :
    (restrictedChart a b).image = a.left ''ᵁ b.image := by
  simp only [AffineOpenChart.image, Scheme.Hom.image_top_eq_opensRange]
  exact Scheme.Hom.opensRange_comp b.map.left a.left

omit [Module.Finite k W] in
private theorem chartSection_comp {R : TestAlgebra k}
    (a : Points S R) [IsOpenImmersion a.left]
    (b : AffineOpenChart ((testSpec k).obj (op R))) {U : S.left.Opens}
    {V : ((testSpec k).obj (op R)).left.Opens} (ha : V ≤ a.left ⁻¹ᵁ U) (hb : b.image ≤ V)
    (hc : (restrictedChart a b).image ≤ U) (s : Γ(constantBundle k W S, U)) :
    chartSection b hb (pullBundleSection a U V ha s) =
      chartSection (restrictedChart a b) hc s :=
  pullBundleSection_comp a b.map ha (b.le_preimage hb) s

set_option maxHeartbeats 150000 in
private theorem mem_localLine_of_charts {R : TestAlgebra k} (L : LineFamily k W S)
    (a : Points S R) {V : ((testSpec k).obj (op R)).left.Opens}
    (s : Γ(constantBundle k W ((testSpec k).obj (op R)), V))
    (h : ∀ x ∈ V, ∃ (b : AffineOpenChart ((testSpec k).obj (op R))) (hb : b.image ≤ V),
      x ∈ b.image ∧ chartSection b hb s ∈ sectionRange (localLine L (b.map ≫ a)).val.arrow ⊤) :
    s ∈ sectionRange (localLine L a).val.arrow V := by
  let i := (localLine L a).val.arrow
  apply mem_sectionRange_of_charts (S := (testSpec k).obj (op R)) i s
  intro x hx
  obtain ⟨b, hb, hx', hs⟩ := h x hx
  obtain ⟨d, hd⟩ := localLine_pull L a b.map
  refine ⟨b, hb, hx', ?_⟩
  rw [sectionRange_eq_of_comm _ _ d hd ⊤]
  exact hs

/-- A section belongs to the glued line precisely when it belongs on each affine open test. -/
private def gluedLinePresheaf (L : LineFamily k W S) : (constantBundle k W S).val.Submodule where
  obj U := ⨅ (a : AffineOpenChart S) (h : a.image ≤ U.unop),
    (sectionRange (localLine L a.map).val.arrow ⊤).comap (pullBundleSectionLinearMap a.map U.unop ⊤ (a.le_preimage h))
  map := by
    intro U V f s hs
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hs ⊢
    intro a ha
    change chartSection a ha ((constantBundle k W S).presheaf.map f s) ∈ _
    exact (chartSection_restrict a (leOfHom f.unop) ha s).symm ▸ hs a (ha.trans (leOfHom f.unop))

private theorem mem_gluedLinePresheaf (L : LineFamily k W S) (U : S.left.Opens)
    (s : Γ(constantBundle k W S, U)) :
    s ∈ (gluedLinePresheaf L).obj (op U) ↔
      ∀ (a : AffineOpenChart S) (ha : a.image ≤ U),
        chartSection a ha s ∈ sectionRange (localLine L a.map).val.arrow ⊤ := by
  simp only [gluedLinePresheaf, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

set_option maxHeartbeats 150000 in
private theorem gluedLinePresheaf_isSheaf (L : LineFamily k W S) (U : S.left.Opens)
    (s : Γ(constantBundle k W S, U))
    (h : (gluedLinePresheaf L).toSubfunctor.sieveOfSection (U := op U) s ∈
      Opens.grothendieckTopology S.left U) :
    s ∈ (gluedLinePresheaf L).obj (op U) := by
  apply (mem_gluedLinePresheaf L U s).mpr
  intro a ha
  refine mem_localLine_of_charts L a.map
    (pullBundleSection a.map U ⊤ (a.le_preimage ha) s) ?_
  intro x _
  have hx : a.map.left x ∈ U := ha ⟨x, trivial, rfl⟩
  obtain ⟨V, p, hp, hxV⟩ := h (a.map.left x) hx
  obtain ⟨b, hxb, hb⟩ := exists_affineOpenChart (S := (testSpec k).obj (op a.R))
    (U := a.map.left ⁻¹ᵁ V) hxV
  let c := restrictedChart a.map b
  have hc : c.image ≤ V :=
    (restrictedChart_image a.map b).le.trans (Set.image_subset_iff.mpr hb)
  refine ⟨b, le_top, hxb, ?_⟩
  have hs : (constantBundle k W S).presheaf.map (homOfLE (leOfHom p)).op s ∈
      (gluedLinePresheaf L).obj (op V) := hp
  have hm := (mem_gluedLinePresheaf L V _).mp hs c hc
  let v : ⊤ ≤ b.map.left ⁻¹ᵁ (⊤ : ((testSpec k).obj (op a.R)).left.Opens) :=
    b.le_preimage le_top
  let w := a.le_preimage ha
  change pullBundleSection b.map ⊤ ⊤ v (pullBundleSection a.map U ⊤ w s) ∈ _
  rw [pullBundleSection_comp a.map b.map w v s]
  let Q := sectionRange (localLine L c.map).val.arrow (⊤ : ((testSpec k).obj (op c.R)).left.Opens)
  change chartSection c (hc.trans (leOfHom p)) s ∈ Q
  rw [← chartSection_restrict c (leOfHom p) hc s]
  exact hm

private def gluedLineSections (L : LineFamily k W S) : (constantBundle k W S).Submodule where
  toSubmodule := gluedLinePresheaf L
  isSheaf := by
    intro U s h
    exact gluedLinePresheaf_isSheaf L U.unop s h

private theorem affineTestMembership_congr (L : LineFamily k W S) {R : TestAlgebra k}
    {a b : Points S R} (e : a = b) {U : S.left.Opens} (s : Γ(constantBundle k W S, U))
    (ha : ⊤ ≤ a.left ⁻¹ᵁ U) (hb : ⊤ ≤ b.left ⁻¹ᵁ U) :
    (pullBundleSection a U ⊤ ha s ∈ sectionRange (localLine L a).val.arrow ⊤) ↔
    (pullBundleSection b U ⊤ hb s ∈ sectionRange (localLine L b).val.arrow ⊤) := by
  cases e
  rfl

private theorem mem_gluedLineSections_iff (L : LineFamily k W S) {R : TestAlgebra k}
    (a : Points S R) [IsOpenImmersion a.left] (V : ((testSpec k).obj (op R)).left.Opens)
    (s : Γ(constantBundle k W S, a.left ''ᵁ V)) :
    s ∈ (gluedLineSections L).obj (op (a.left ''ᵁ V)) ↔
      pullBundleSection a (a.left ''ᵁ V) V (a.left.preimage_image_eq V).ge s ∈
        sectionRange (localLine L a).val.arrow V := by
  change s ∈ (gluedLinePresheaf L).obj (op (a.left ''ᵁ V)) ↔ _
  rw [mem_gluedLinePresheaf]
  let h := (a.left.preimage_image_eq V).ge
  constructor
  · intro hs
    apply mem_localLine_of_charts L a
    intro x hx
    obtain ⟨b, hxb, hb⟩ := exists_affineOpenChart hx
    let c := restrictedChart a b
    have hc : c.image ≤ a.left ''ᵁ V :=
      (restrictedChart_image a b).le.trans (a.left.image_mono hb)
    refine ⟨b, hb, hxb, ?_⟩
    rw [chartSection_comp a b h hb hc s]
    exact hs c hc
  · intro hs c hc
    have hinc : Set.range c.map.left ⊆ Set.range a.left := by
      rintro x ⟨y, rfl⟩
      obtain ⟨z, _, hz⟩ := hc ⟨y, trivial, rfl⟩
      exact ⟨z, hz⟩
    let g := IsOpenImmersion.lift a.left c.map.left hinc
    let q : (testSpec k).obj (op c.R) ⟶ (testSpec k).obj (op R) := Over.homMk g (by
      rw [← Over.w a, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w c.map])
    have hq : q ≫ a = c.map := Over.OverMorphism.ext (IsOpenImmersion.lift_fac ..)
    have hle : ⊤ ≤ g ⁻¹ᵁ V := by
      intro x _
      obtain ⟨y, hy, he⟩ := hc ⟨x, trivial, rfl⟩
      have hh := congrFun (congrArg (fun f : ((testSpec k).obj (op c.R)).left ⟶ S.left =>
        (f : ((testSpec k).obj (op c.R)).left → S.left)) (IsOpenImmersion.lift_fac a.left c.map.left hinc)) x
      change a.left (g x) = c.map.left x at hh
      change g x ∈ V
      rw [a.left.isOpenEmbedding.injective (hh.trans he.symm)]
      exact hy
    obtain ⟨d, hd⟩ := localLine_pull L a q
    have hmem := pullBundleSection_mem q _ _ d hd hle _ hs
    let hcomp : ⊤ ≤ (q ≫ a).left ⁻¹ᵁ (a.left ''ᵁ V) :=
      hle.trans ((Opens.map q.left.base).monotone h)
    apply (affineTestMembership_congr L hq s hcomp (c.le_preimage hc)).mp
    rw [← pullBundleSection_comp a q h hle s]
    exact hmem

private theorem gluedLineSections_on_chart (L : LineFamily k W S) {R : TestAlgebra k}
    (a : Points S R) [IsOpenImmersion a.left] :
    let i := (gluedLineSections L).ι
    ∃ e : (Scheme.Modules.pullback a.left).obj (gluedLineSections L).toSheafOfModules ≅
      Subobject.underlying.obj (localLine L a).val,
      (Scheme.Modules.pullback a.left).map i ≫ (pullbackAmbientIso k W a).hom =
        e.hom ≫ (localLine L a).val.arrow := by
  let N := gluedLineSections L
  let i := N.ι
  let j := (Scheme.Modules.pullback a.left).map i ≫ (pullbackAmbientIso k W a).hom
  have hi : Mono i := inferInstanceAs (Mono N.ι)
  have hmono : Mono ((Scheme.Modules.pullback a.left).map i) := mono_open_pullback a.left i
  let : Mono j := inferInstanceAs (Mono ((Scheme.Modules.pullback a.left).map i ≫ _))
  have he : Subobject.mk j = (localLine L a).val := by
    apply subobject_eq_of_sectionRanges
    intro V
    rw [sectionRange_mk]
    ext t
    obtain ⟨s, rfl⟩ := (pullBundleSection_open (W := W) a V).surjective t
    rw [pullBundleSection_mem_iff_open a i j (Iso.refl _) (Category.id_comp _).symm V s]
    have hs : s ∈ sectionRange i (a.left ''ᵁ V) ↔ s ∈ N.obj (op (a.left ''ᵁ V)) := by
      change (∃ z : N.obj (op (a.left ''ᵁ V)), z.val = s) ↔ _
      exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun hz => ⟨⟨s, hz⟩, rfl⟩⟩
    exact hs.trans (mem_gluedLineSections_iff L a V s)
  let e := Subobject.isoOfMkEq j _ he
  exact ⟨e, (Subobject.ofMkLE_arrow (f := j) he.le).symm⟩

end SheafGluing

section SheafLineRepresentation

open TopCat TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 220000

private theorem isLocalLineInclusion_congr {X : Scheme.{u}} {A B A' B' : X.Modules}
    {i : A ⟶ B} {j : A' ⟶ B'} (d : A ≅ A') (e : B ≅ B')
    (h : i ≫ e.hom = d.hom ≫ j) (hj : IsLocalLineInclusion j) :
    IsLocalLineInclusion i := by
  intro x
  obtain ⟨U, hx, ⟨t⟩, r, hr⟩ := hj x
  let P := Scheme.Modules.pullback U.ι
  refine ⟨U, hx, ⟨P.mapIso d ≪≫ t⟩, ?_⟩
  have hh : P.map i ≫ (P.mapIso e).hom = (P.mapIso d).hom ≫ P.map j := by
    exact (P.map_comp _ _).symm.trans ((congrArg P.map h).trans (P.map_comp _ _))
  exact retraction_of_commuting_isos _ _ (P.mapIso d) (P.mapIso e) hh r hr

private theorem isLocalLineInclusion_of_openCover {X : Scheme.{u}} {M E : X.Modules}
    (i : M ⟶ E)
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsOpenImmersion f ∧ x ∈ Set.range f ∧ IsLocalLineInclusion ((Scheme.Modules.pullback f).map i)) :
    IsLocalLineInclusion i := by
  intro x
  obtain ⟨Y, f, hf, ⟨y, rfl⟩, hloc⟩ := h x
  obtain ⟨V, hy, ⟨t⟩, r, hr⟩ := hloc y
  let U := f ''ᵁ V
  have hu : f y ∈ U := ⟨y, hy, rfl⟩
  have he : Set.range U.ι ⊆ Set.range (V.ι ≫ f) := by
    rintro z ⟨w, rfl⟩
    obtain ⟨v, hv, h⟩ := w.property
    exact ⟨⟨v, hv⟩, h⟩
  let g := IsOpenImmersion.lift (V.ι ≫ f) U.ι he
  have hg : (g ≫ V.ι) ≫ f = U.ι :=
    (Category.assoc _ _ _).trans (IsOpenImmersion.lift_fac (V.ι ≫ f) U.ι he)
  let J := Scheme.Modules.pullback U.ι
  let e := (Scheme.Modules.pullbackComp (g ≫ V.ι) f) ≪≫ Scheme.Modules.pullbackCongr hg
  obtain ⟨⟨u⟩, q, hq⟩ :=
    line_after_pullback ((Scheme.Modules.pullback f).map i) V g t r hr (g ≫ V.ι) rfl
  refine ⟨U, hu, ⟨(e.app M).symm ≪≫ u⟩, ?_⟩
  exact retraction_of_commuting_isos _ _ (e.app M).symm (e.app E).symm (e.inv.naturality i) q hq

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
variable {S T : SchemeOver k}

attribute [local instance] AffineOpenChart.isOpen

private theorem gluedLineSections_isLocalLineInclusion (L : LineFamily k W S) :
    IsLocalLineInclusion (gluedLineSections L).ι := by
  apply isLocalLineInclusion_of_openCover
  intro x
  obtain ⟨a, hxa, _⟩ := exists_affineOpenChart (U := (⊤ : S.left.Opens)) (x := x) trivial
  obtain ⟨e, he⟩ := gluedLineSections_on_chart L a.map
  obtain ⟨y, _, hy⟩ := hxa
  have hr : x ∈ Set.range a.map.left := ⟨y, hy⟩
  exact ⟨_, a.map.left, a.isOpen, hr,
    isLocalLineInclusion_congr e (pullbackAmbientIso k W a.map) he (localLine L a.map).property⟩

private def gluedLine (L : LineFamily k W S) : LineSubbundle k W S := by
  let N := gluedLineSections L
  let i := N.ι
  letI : Mono i := inferInstanceAs (Mono N.ι)
  exact ⟨Subobject.mk i, isLocalLineInclusion_congr (Subobject.underlyingIso i) (Iso.refl _)
    ((Category.comp_id _).trans (Subobject.underlyingIso_hom_comp_eq_mk i).symm)
    (gluedLineSections_isLocalLineInclusion L)⟩

private theorem gluedLine_on_chart (L : LineFamily k W S) {R : TestAlgebra k}
    (a : Points S R) [IsOpenImmersion a.left] :
    pullbackLine a (gluedLine L) = localLine L a := by
  let N := gluedLineSections L
  let i := N.ι
  let : Mono i := inferInstanceAs (Mono N.ι)
  let e := Subobject.underlyingIso i
  let P := Scheme.Modules.pullback a.left
  obtain ⟨d, hd⟩ := gluedLineSections_on_chart L a
  apply (pullbackLine_eq_iff _ _ _).mpr
  refine ⟨P.mapIso e ≪≫ d, ?_⟩
  have hh : (gluedLine L).val.arrow = e.hom ≫ i :=
    (Subobject.underlyingIso_hom_comp_eq_mk i).symm
  rw [hh, P.map_comp, Category.assoc, hd]
  rfl

private theorem factors_through_affineOpenChart {S T : SchemeOver k} (a : AffineOpenChart S)
    (b : T ⟶ S) (h : Set.range b.left ⊆ a.image) :
    ∃ q : T ⟶ (testSpec k).obj (op a.R), q ≫ a.map = b := by
  have hi : Set.range b.left ⊆ Set.range a.map.left := by
    intro x hx
    obtain ⟨y, _, hy⟩ := h hx
    exact ⟨y, hy⟩
  let g := IsOpenImmersion.lift a.map.left b.left hi
  let q : T ⟶ (testSpec k).obj (op a.R) := Over.homMk g (by
    rw [← Over.w a.map, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w b])
  exact ⟨q, Over.OverMorphism.ext (IsOpenImmersion.lift_fac ..)⟩

private theorem gluedLine_on_affineTest (L : LineFamily k W S) {R : TestAlgebra k} (a : Points S R) :
    pullbackLine a (gluedLine L) = localLine L a := by
  apply lineSubbundle_ext_of_charts
  intro x
  obtain ⟨b, hxb, _⟩ := exists_affineOpenChart (S := S) (U := ⊤) (x := a.left x) trivial
  obtain ⟨c, hxc, hc⟩ := exists_affineOpenChart (U := a.left ⁻¹ᵁ b.image) hxb
  have h : Set.range (c.map ≫ a).left ⊆ b.image := by
    rintro z ⟨y, rfl⟩
    exact hc ⟨y, trivial, rfl⟩
  obtain ⟨q, hq⟩ := factors_through_affineOpenChart b (c.map ≫ a) h
  refine ⟨c, hxc, ?_⟩
  calc
    pullbackLine c.map (pullbackLine a (gluedLine L)) =
        pullbackLine (c.map ≫ a) (gluedLine L) := (pullbackLine_comp _ _ _).symm
    _ = pullbackLine (q ≫ b.map) (gluedLine L) := by rw [hq]
    _ = pullbackLine q (pullbackLine b.map (gluedLine L)) := pullbackLine_comp _ _ _
    _ = pullbackLine q (localLine L b.map) := by rw [gluedLine_on_chart]
    _ = localLine L (q ≫ b.map) := affineLineSheafEquiv_family L b.map q
    _ = localLine L (c.map ≫ a) := by rw [hq]
    _ = pullbackLine c.map (localLine L a) := (affineLineSheafEquiv_family L a c.map).symm

private def lineFamilyOfSubbundle (M : LineSubbundle k W S) : LineFamily k W S where
  line R a := (affineLineSheafEquiv R).symm (pullbackLine a M)
  compatible f a := by
    rw [← affineLineBaseChange_submodule]
    apply congrArg AffineLine.submodule
    apply (affineLineSheafEquiv _).injective
    rw [Equiv.apply_symm_apply, ← affineLineSheafEquiv_natural, Equiv.apply_symm_apply,
      ← pullbackLine_comp]

private theorem lineFamilyOfSubbundle_injective :
    Function.Injective (lineFamilyOfSubbundle (k := k) (W := W) (S := S)) := by
  intro M N he
  apply lineSubbundle_ext_of_charts
  intro x
  obtain ⟨a, hxa, _⟩ := exists_affineOpenChart (S := S) (U := ⊤) (x := x) trivial
  exact ⟨a, hxa, (affineLineSheafEquiv a.R).symm.injective
    (congrArg (fun L : LineFamily k W S => L.line a.R a.map) he)⟩

private theorem lineFamilyOfSubbundle_gluedLine (L : LineFamily k W S) :
    lineFamilyOfSubbundle (gluedLine L) = L := by
  apply lineFamily_ext
  intro R a
  change (affineLineSheafEquiv R).symm (pullbackLine a (gluedLine L)) = L.line R a
  rw [gluedLine_on_affineTest]
  exact (affineLineSheafEquiv R).symm_apply_apply _

/-- Cartesian families of affine lines and actual locally split line subbundles are equivalent. -/
def lineFamilySheafEquiv (S : SchemeOver k) : LineFamily k W S ≃ LineSubbundle k W S where
  toFun := gluedLine
  invFun := lineFamilyOfSubbundle
  left_inv := lineFamilyOfSubbundle_gluedLine
  right_inv M := lineFamilyOfSubbundle_injective (lineFamilyOfSubbundle_gluedLine (lineFamilyOfSubbundle M))

private theorem lineFamilyOfSubbundle_naturality (f : T ⟶ S) (L : LineSubbundle k W S) :
    lineFamilyOfSubbundle (pullbackLine f L) = (lineFamilyOfSubbundle L).pullback k W f :=
  lineFamily_ext fun R a => congrArg (affineLineSheafEquiv R).symm (pullbackLine_comp f a L).symm

theorem lineFamilySheafEquiv_naturality (f : T ⟶ S) (L : LineFamily k W S) :
    pullbackLine f (lineFamilySheafEquiv S L) = lineFamilySheafEquiv T (L.pullback k W f) := by
  apply (lineFamilySheafEquiv T).symm.injective
  rw [Equiv.symm_apply_apply]
  change lineFamilyOfSubbundle (pullbackLine f _) = _
  rw [lineFamilyOfSubbundle_naturality]
  exact congrArg (fun N : LineFamily k W S => N.pullback k W f) ((lineFamilySheafEquiv S).symm_apply_apply L)

theorem sheafPointFormula (k W : Type u) [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W] :
    SheafPointFormula k W (lineRepresentation k W) := by
  refine ⟨lineFamilySheafEquiv, affineConstantBundleIso k W, ?_, ?_⟩
  · intro S T f p
    apply (pullbackLine_eq_iff _ _ _).mp
    rw [lineFamilySheafEquiv_naturality, (lineRepresentation k W).naturality f p]
  · intro R p
    let S := (testSpec k).obj (op R)
    let L := (lineRepresentation k W).points S p
    let M := lineFamilySheafEquiv S L
    have h : (affineLineSheafEquiv R).symm M = L.line R (𝟙 S) := by
      have he := congrArg (fun N : LineFamily k W S => N.line R (𝟙 S))
        ((lineFamilySheafEquiv S).symm_apply_apply L)
      change (affineLineSheafEquiv R).symm (pullbackLine (𝟙 S) M) = _ at he
      rwa [pullbackLine_id] at he
    have he : affineLineSheafEquiv R (L.line R (𝟙 S)) = M :=
      (congrArg (affineLineSheafEquiv R) h).symm.trans ((affineLineSheafEquiv R).apply_symm_apply M)
    change AffineSheafMatch (L.line R (𝟙 S)) M
    exact he ▸ affineLineSheafEquiv_spec (L.line R (𝟙 S))

theorem projectiveSpaceGeometry : ProjectiveSpaceGeometry.{u} := by
  intro k _
  refine ⟨lineRepresentation k, projectiveTransport k, fun W _ _ _ =>
    ⟨basisPointFormula k W, sheafPointFormula k W, automorphismPointFormula k W⟩, ?_⟩
  intro I _ W _ _ _
  exact ⟨segreMorphism W, segreClosedImmersion W, segrePointFormula W, segreEquivariance W⟩

end SheafLineRepresentation

end

end LinearAlgebraicGroups.ProjectiveSpaces
