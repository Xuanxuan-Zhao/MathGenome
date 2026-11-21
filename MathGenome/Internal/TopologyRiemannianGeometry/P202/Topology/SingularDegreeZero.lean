import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularDegreeZero
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace P202.SingularDegreeZero
open P202Specs.SingularChains P202Specs.SingularDegreeZero
universe u v w w'
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

local instance : HasCoproducts.{w} (ModuleCat.{max v w} R) :=
  hasCoproducts_shrink.{w, max v w}

/-- The coproduct description and the finite-sum description of chains agree,
including when the index set is empty. The universe lift changes only the
coefficient universe. -/
def coproductFinsuppIso (I : Type w) :
    (∐ fun _ : I => coefficientModule.{u,v,w} R M) ≅ ModuleCat.of R (I →₀ M) where
  hom := Sigma.desc (fun i => ModuleCat.ofHom
    ((Finsupp.lsingle i).comp (ULift.moduleEquiv : ULift.{w} M ≃ₗ[R] M).toLinearMap))
  inv := ModuleCat.ofHom (Finsupp.lsum R (fun i =>
    (Sigma.ι (fun _ : I => coefficientModule.{u,v,w} R M) i).hom.comp
      (ULift.moduleEquiv.symm : M ≃ₗ[R] ULift.{w} M).toLinearMap))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc_assoc, Category.comp_id]
    apply ModuleCat.hom_ext
    ext m
    change (Finsupp.lsum R (fun j =>
      (Sigma.ι (fun _ : I => coefficientModule.{u,v,w} R M) j).hom.comp
        (ULift.moduleEquiv.symm : M ≃ₗ[R] ULift.{w} M).toLinearMap))
      (Finsupp.single i m.down) = _
    rw [Finsupp.lsum_single]
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro i m
    change (Sigma.desc (fun j => ModuleCat.ofHom
      ((Finsupp.lsingle j).comp (ULift.moduleEquiv : ULift.{w} M ≃ₗ[R] M).toLinearMap))).hom ((Finsupp.lsum R (fun j =>
      (Sigma.ι (fun _ : I => coefficientModule.{u,v,w} R M) j).hom.comp
        (ULift.moduleEquiv.symm : M ≃ₗ[R] ULift.{w} M).toLinearMap))
      (Finsupp.single i m)) = _
    rw [Finsupp.lsum_single]
    change ((Sigma.ι (fun _ : I => coefficientModule.{u,v,w} R M) i) ≫
      Sigma.desc (fun j => ModuleCat.ofHom
        ((Finsupp.lsingle j).comp (ULift.moduleEquiv : ULift.{w} M ≃ₗ[R] M).toLinearMap))).hom (ULift.up m) = _
    rw [Sigma.ι_comp_desc]
    rfl

@[reassoc (attr := simp)]
theorem ι_coproductFinsuppIso_hom (I : Type w) (i : I) :
    Sigma.ι (fun _ : I => coefficientModule.{u,v,w} R M) i ≫
      (coproductFinsuppIso R M I).hom = ModuleCat.ofHom
        ((Finsupp.lsingle i).comp (ULift.moduleEquiv : ULift.{w} M ≃ₗ[R] M).toLinearMap) := by
  simp [coproductFinsuppIso]

/-- The bridge is natural in the simplex index; hence it also respects all faces. -/
def coproductFinsuppNatIso :
    sigmaConst.obj (coefficientModule.{u,v,w} R M) ≅ finsuppFunctor.{u,v,w} R M :=
  NatIso.ofComponents (coproductFinsuppIso R M) (by
    intro I J f
    apply Sigma.hom_ext
    intro i
    apply ModuleCat.hom_ext
    ext m
    simp [finsuppFunctor])

/-- An isomorphism of the actual upstream complex with Mathlib's coproduct model. -/
def libraryChainIso (X : TopCat.{w}) :
    (TopCat.toSSet.obj X).chainComplex (coefficientModule.{u,v,w} R M) ≅ complex R M X :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (Functor.isoWhiskerLeft (TopCat.toSSet.obj X) (coproductFinsuppNatIso R M))

/-- Ordinary degree zero for arbitrary spaces and arbitrary module coefficients. -/
theorem degreeZero : Expected.degreeZero.{u,v,w} := by
  intro R _ M _ _ X
  exact ⟨((complex R M X).extendHomologyIso (degreeEmbedding 0) (j := 0) (by rfl) ≪≫
    (HomologicalComplex.homologyFunctor _ _ 0).mapIso (libraryChainIso R M X).symm ≪≫
    TopCat.singularHomology₀Iso X (coefficientModule.{u,v,w} R M) ≪≫
    coproductFinsuppIso R M (ZerothHomotopy X)).toLinearEquiv⟩

/-- An empty space has no singular simplices in any nonnegative degree. -/
instance simplexIsEmpty (X : TopCat.{w}) [IsEmpty X] (n : ℕ) : IsEmpty (Simplex X n) :=
  ⟨fun s => isEmptyElim (simplexEquiv X n s (Convexity.StdSimplex.single 0))⟩

lemma emptyComplexX (X : TopCat.{w}) [IsEmpty X] (n : ℕ) :
    IsZero ((complex R M X).X n) := by
  change IsZero (ModuleCat.of R (Simplex X n →₀ M))
  exact ModuleCat.isZero_of_subsingleton _

lemma emptyOrdinaryX (X : TopCat.{w}) [IsEmpty X] (n : ℤ) :
    IsZero ((ordinaryComplex R M X).X n) := by
  by_cases h : n < 0
  · exact P202.SingularChains.ordinary_negative_chains R M X n h
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
    exact (ordinaryNonnegativeIso R M X k).isZero_iff.mpr (emptyComplexX R M X k)

theorem emptyOrdinary : Expected.emptyOrdinary.{u,v,w} := by
  intro R _ M _ _ X _ n
  exact (HomologicalComplex.ExactAt.of_isZero (emptyOrdinaryX R M X n)).isZero_homology

lemma emptyReducedX (X : TopCat.{w}) [IsEmpty X] (n : ℤ) (hn : n ≠ -1) :
    IsZero ((reducedComplex R M X).X n) := by
  by_cases h : n < -1
  · exact (P202.SingularChains.reduced_below_minus_one R M X n h).1
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
    exact (reducedNonnegativeIso R M X k).isZero_iff.mpr (emptyComplexX R M X k)

theorem emptyReducedOther : Expected.emptyReducedOther.{u,v,w} := by
  intro R _ M _ _ X _ n hn
  exact (HomologicalComplex.ExactAt.of_isZero (emptyReducedX R M X n hn)).isZero_homology

theorem emptyReducedMinusOne : Expected.emptyReducedMinusOne.{u,v,w} := by
  intro R _ M _ _ X _
  let K := reducedComplex R M X
  let S := K.sc' 0 (-1) (-2)
  have hf : S.f = 0 := (emptyReducedX R M X 0 (by omega)).eq_of_src _ _
  have hg : S.g = 0 := (emptyReducedX R M X (-2) (by omega)).eq_of_tgt _ _
  exact ⟨(ShortComplex.homologyMapIso (K.isoSc' 0 (-1) (-2) (by simp) (by simp)) ≪≫
    (ShortComplex.HomologyData.ofZeros S hf hg).left.homologyIso ≪≫
    reducedAugmentationIso R M X).toLinearEquiv.trans ULift.moduleEquiv⟩

/-- Positive-degree ordinary homology vanishes for every totally disconnected
space. This gives the point and both point complexes of the zero sphere. -/
lemma totallyDisconnectedHomology (X : TopCat.{w}) [TotallyDisconnectedSpace X]
    (n : ℤ) (hn : n ≠ 0) : IsZero (homology R M X n) := by
  by_cases h : n < 0
  · exact P202.SingularChains.ordinary_negative_homology R M X n h
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
    have hk : k ≠ 0 := by omega
    apply ((complex R M X).extendHomologyIso (degreeEmbedding 0) (j := k)
      (by change (0 : ℤ) + k = k; omega)).isZero_iff.mpr
    apply ((HomologicalComplex.homologyFunctor _ _ k).mapIso (libraryChainIso R M X)).isZero_iff.mp
    exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ k
      (coefficientModule.{u,v,w} R M) X hk

theorem pointOrdinaryOther : Expected.pointOrdinaryOther.{u,v,w} := by
  intro R _ M _ _ n hn
  exact totallyDisconnectedHomology R M point n hn

theorem sphereOrdinaryOther : Expected.sphereOrdinaryOther.{u,v,w} := by
  intro R _ M _ _ n hn
  exact totallyDisconnectedHomology R M zeroSphere n hn

/-- Degree zero for a totally disconnected space is the finite direct sum on
its actual points, compatibly with the same chain model as above. -/
def totallyDisconnectedZero (X : TopCat.{w}) [TotallyDisconnectedSpace X] :
    homology R M X 0 ≃ₗ[R] (X →₀ M) :=
  ((complex R M X).extendHomologyIso (degreeEmbedding 0) (j := 0) (by rfl) ≪≫
    (HomologicalComplex.homologyFunctor _ _ 0).mapIso (libraryChainIso R M X).symm ≪≫
    AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace _
      (coefficientModule.{u,v,w} R M) X ≪≫ coproductFinsuppIso R M X).toLinearEquiv

theorem pointOrdinaryZero : Expected.pointOrdinaryZero.{u,v,w} := by
  intro R _ M _ _
  exact ⟨(totallyDisconnectedZero R M point).trans
    (Finsupp.uniqueLinearEquiv R M PUnit.unit)⟩

theorem sphereOrdinaryZero : Expected.sphereOrdinaryZero.{u,v,w} := by
  intro R _ M _ _
  exact ⟨(totallyDisconnectedZero R M zeroSphere).trans
    (((Finsupp.mapDomain.linearEquiv M R Equiv.ulift).trans
      (Finsupp.linearEquivFunOnFinite R M (Fin 2))).trans (LinearEquiv.finTwoArrow R M))⟩

/-- Change from singular-set components to topological path components. -/
def componentCoproductIso (X : TopCat.{w}) :
    (∐ fun _ : (TopCat.toSSet.obj X).π₀ => coefficientModule.{u,v,w} R M) ≅
      ModuleCat.of R (ComponentSums M X) :=
  (sigmaConst.obj (coefficientModule.{u,v,w} R M)).mapIso
    TopCat.zerothHomotopyEquiv.toIso.symm ≪≫ coproductFinsuppIso R M (ZerothHomotopy X)

/-- The canonical component projection on zero chains. -/
def componentProjection (X : TopCat.{w}) :
    (complex R M X).X 0 ⟶ ModuleCat.of R (ComponentSums M X) :=
  (libraryChainIso R M X).inv.f 0 ≫
    SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj X) (coefficientModule.{u,v,w} R M) ≫
    (componentCoproductIso R M X).hom

lemma boundary_componentProjection (X : TopCat.{w}) :
    (complex R M X).d 1 0 ≫ componentProjection R M X = 0 := by
  unfold componentProjection
  rw [← (libraryChainIso R M X).inv.comm_assoc 1 0]
  simp only [SSet.π₀.d_fromChainComplexXZero_assoc,
    CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

/-- The sum of components really is the source's augmentation. -/
lemma componentProjection_sum (X : TopCat.{w}) :
    componentProjection R M X ≫ ModuleCat.ofHom
      ((ULift.moduleEquiv.symm : M ≃ₗ[R] ULift.{w} M).toLinearMap.comp
        (componentSum R M X)) = augmentation R M X := by
  rw [← cancel_epi ((libraryChainIso R M X).hom.f 0)]
  dsimp only [componentProjection]
  have hcancel : (libraryChainIso R M X).hom.f 0 ≫ (libraryChainIso R M X).inv.f 0 = 𝟙 _ :=
    congrArg (fun f => f.f 0) (libraryChainIso R M X).hom_inv_id
  simp only [← Category.assoc, hcancel, Category.id_comp]
  apply Sigma.hom_ext
  intro s
  simp only [Category.assoc]
  change (TopCat.toSSet.obj X).ιChainComplex s ≫
    SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj X) (coefficientModule.{u,v,w} R M) ≫
      (componentCoproductIso R M X).hom ≫ _ =
    Sigma.ι _ s ≫ (coproductFinsuppIso R M (Simplex X 0)).hom ≫ augmentation R M X
  rw [SSet.π₀.comp_fromChainComplexXZero_assoc]
  simp only [componentCoproductIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  simp only [sigmaConst_obj_map, Sigma.ι_comp_map'_assoc, Category.id_comp]
  rw [ι_coproductFinsuppIso_hom_assoc, ι_coproductFinsuppIso_hom_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change ULift.up ((componentSum R M X) (Finsupp.single _ m.down)) =
    ULift.up ((sumCoefficients R M _) (Finsupp.single _ m.down))
  simp [componentSum, sumCoefficients]

/-- The projection is a cokernel of the actual upstream one-boundary. -/
def componentProjectionIsCokernel (X : TopCat.{w}) :
    IsColimit (CokernelCofork.ofπ (componentProjection R M X)
      (boundary_componentProjection R M X)) := by
  apply IsCokernel.ofIso _
    (SSet.isColimitCokernelCoforkChainComplexDOneZero (TopCat.toSSet.obj X)
      (coefficientModule.{u,v,w} R M))
    (CokernelCofork.ofπ (componentProjection R M X) (boundary_componentProjection R M X))
    ((HomologicalComplex.eval _ _ 1).mapIso (libraryChainIso R M X))
    ((HomologicalComplex.eval _ _ 0).mapIso (libraryChainIso R M X))
    (componentCoproductIso R M X)
  · exact (libraryChainIso R M X).hom.comm 1 0
  · simp [componentProjection]

/-- Right homology data for the reduced zero group, with its full kernel model. -/
def reducedZeroData (X : TopCat.{w}) :
    ((augmentedShifted R M X).sc' 2 1 0).RightHomologyData := by
  change (ShortComplex.mk ((complex R M X).d 1 0) (augmentation R M X)
    (augmentation_boundary R M X)).RightHomologyData
  let p := componentProjection R M X
  let q := ModuleCat.ofHom
    ((ULift.moduleEquiv.symm : M ≃ₗ[R] ULift.{w} M).toLinearMap.comp
      (componentSum R M X))
  let hp := componentProjectionIsCokernel R M X
  have hpq : hp.desc (CokernelCofork.ofπ (augmentation R M X)
      (augmentation_boundary R M X)) = q := by
    apply Cofork.IsColimit.hom_ext hp
    rw [Cofork.IsColimit.π_desc]
    exact (componentProjection_sum R M X).symm
  refine {
    Q := ModuleCat.of R (ComponentSums M X)
    H := ModuleCat.of R (LinearMap.ker (componentSum R M X))
    p := p
    ι := ModuleCat.ofHom (LinearMap.ker (componentSum R M X)).subtype
    wp := boundary_componentProjection R M X
    hp := hp
    wι := ?_
    hι := ?_ }
  · rw [hpq]
    ext z
    exact congrArg ULift.up z.property
  · refine KernelFork.IsLimit.ofι _ _ (fun k hk => ?_) ?_ ?_
    · refine ModuleCat.ofHom (k.hom.codRestrict _ (fun z => ?_))
      have hz := congrArg (fun f => f.hom z) hk
      change (hp.desc (CokernelCofork.ofπ (augmentation R M X)
        (augmentation_boundary R M X))).hom (k.hom z) = 0 at hz
      rw [hpq] at hz
      exact congrArg ULift.down hz
    · intro W k hk
      rfl
    · intro W k hk m hm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun f => f.hom z) hm

theorem reducedDegreeZero : Expected.reducedDegreeZero.{u,v,w} := by
  intro R _ M _ _ X
  exact ⟨((augmentedShifted R M X).extendHomologyIso (degreeEmbedding (-1))
      (j := 1) (by rfl) ≪≫
    ShortComplex.homologyMapIso ((augmentedShifted R M X).isoSc' 2 1 0 (by simp) (by simp)) ≪≫
    (reducedZeroData R M X).homologyIso).toLinearEquiv⟩

/-- Augmentation only changes homology in degrees zero and minus one. -/
def reducedPositiveIso (X : TopCat.{w}) (n : ℕ) (hn : 0 < n) :
    reducedHomology R M X n ≅ homology R M X n := by
  let K := complex R M X
  let L := augmentedShifted R M X
  have h1 : (ComplexShape.down ℕ).prev (n+1) = n+2 := by simp
  have h2 : (ComplexShape.down ℕ).next (n+1) = n := by simp
  have h3 : (ComplexShape.down ℕ).prev n = n+1 := by simp
  have h4 : (ComplexShape.down ℕ).next n = n-1 := by
    cases n <;> simp
  refine (L.extendHomologyIso (degreeEmbedding (-1)) (j := n+1) (by
    change (-1 : ℤ) + ((n+1 : ℕ) : ℤ) = n; omega)) ≪≫
    ShortComplex.homologyMapIso (L.isoSc' (n+2) (n+1) n h1 h2) ≪≫ ?_ ≪≫
    (ShortComplex.homologyMapIso (K.isoSc' (n+1) n (n-1) h3 h4)).symm ≪≫
    (K.extendHomologyIso (degreeEmbedding 0) (j := n) (by
      change (0 : ℤ) + n = n; omega)).symm
  apply ShortComplex.homologyMapIso
  cases n with
  | zero => exact False.elim (by omega)
  | succ m =>
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [K, L, augmentedShifted])
      (by simp [K, L, augmentedShifted])

lemma nonemptyReducedMinusOne (X : TopCat.{w}) [Nonempty X] :
    IsZero (reducedHomology R M X (-1)) := by
  let L := augmentedShifted R M X
  apply (L.extendHomologyIso (degreeEmbedding (-1)) (j := 0) (by rfl)).isZero_iff.mpr
  apply HomologicalComplex.ExactAt.isZero_homology
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro m hm
  let x : X := Classical.choice inferInstance
  refine ⟨Finsupp.single (TopCat.toSSetObj₀Equiv.symm x) m.down, ?_⟩
  change (augmentation R M X).hom _ = m
  exact P202.SingularChains.augmentation_single R M X _ m.down

lemma totallyDisconnectedReducedOther (X : TopCat.{w}) [TotallyDisconnectedSpace X]
    [Nonempty X] (n : ℤ) (hn : n ≠ 0) : IsZero (reducedHomology R M X n) := by
  by_cases h : n < -1
  · exact (P202.SingularChains.reduced_below_minus_one R M X n h).2
  by_cases he : n = -1
  · subst n
    exact nonemptyReducedMinusOne R M X
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  apply (reducedPositiveIso R M X k (by omega)).isZero_iff.mpr
  exact totallyDisconnectedHomology R M X k hn

theorem sphereReducedOther : Expected.sphereReducedOther.{u,v,w} := by
  intro R _ M _ _ n hn
  exact totallyDisconnectedReducedOther R M zeroSphere n hn

lemma sumCoefficients_eq_eval (I : Type w) [Subsingleton I] (c : I →₀ M) (i : I) :
    sumCoefficients R M I c = c i := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single j m =>
    have h : j = i := Subsingleton.elim _ _
    subst j
    simp [sumCoefficients]

lemma sumKernel_subsingleton (I : Type w) [Subsingleton I] :
    Subsingleton (LinearMap.ker (sumCoefficients R M I)) := by
  constructor
  intro a b
  apply Subtype.ext
  ext i
  have ha := a.property
  have hb := b.property
  change sumCoefficients R M I a.val = 0 at ha
  change sumCoefficients R M I b.val = 0 at hb
  rw [sumCoefficients_eq_eval R M I _ i] at ha hb
  exact ha.trans hb.symm

theorem pointReduced : Expected.pointReduced.{u,v,w} := by
  intro R _ M _ _ n
  by_cases hn : n = 0
  · subst n
    obtain ⟨e⟩ := reducedDegreeZero R M point.{w}
    have : Subsingleton (ZerothHomotopy point.{w}) := by
      constructor
      intro a b
      induction a using ZerothHomotopy.rec with
      | mk x =>
        induction b using ZerothHomotopy.rec with
        | mk y => exact congrArg ZerothHomotopy.mk (Subsingleton.elim x y)
    have : Subsingleton (LinearMap.ker (componentSum R M point.{w})) :=
      sumKernel_subsingleton R M (ZerothHomotopy point.{w})
    apply ModuleCat.isZero_iff_subsingleton.mpr
    constructor
    intro a b
    apply e.injective
    exact Subsingleton.elim _ _
  · exact totallyDisconnectedReducedOther R M point n hn

/-- No two distinct points of a totally disconnected space are path joined. -/
def componentsOfTotallyDisconnected (X : TopCat.{w}) [TotallyDisconnectedSpace X] :
    ZerothHomotopy X ≃ X where
  toFun := ZerothHomotopy.lift id (fun _ _ p => by
    have h := TotallyDisconnectedSpace.eq_of_continuous p p.continuous 0 1
    simpa using h)
  invFun := ZerothHomotopy.mk
  left_inv c := by induction c; rfl
  right_inv x := rfl

lemma sumCoefficients_mapDomain {I : Type w} {J : Type w'} (f : I → J) (c : I →₀ M) :
    sumCoefficients R M J (Finsupp.mapDomain f c) = sumCoefficients R M I c := by
  have h : (sumCoefficients R M J).comp (Finsupp.lmapDomain M R f) =
      sumCoefficients R M I := by
    apply Finsupp.lhom_ext
    intro i m
    simp [sumCoefficients]
  exact LinearMap.congr_fun h c

/-- Reindexing finite component sums preserves their sum-zero kernel. -/
def sumKernelReindex {I : Type w} {J : Type w'} (e : I ≃ J) :
    LinearMap.ker (sumCoefficients R M I) ≃ₗ[R]
      LinearMap.ker (sumCoefficients R M J) where
  toFun c := ⟨Finsupp.mapDomain e c.val, by
    change sumCoefficients R M J _ = 0
    rw [sumCoefficients_mapDomain]
    exact c.property⟩
  invFun c := ⟨Finsupp.mapDomain e.symm c.val, by
    change sumCoefficients R M I _ = 0
    rw [sumCoefficients_mapDomain]
    exact c.property⟩
  left_inv c := by
    apply Subtype.ext
    exact (Finsupp.mapDomain.linearEquiv M R e).symm_apply_apply c.val
  right_inv c := by
    apply Subtype.ext
    exact (Finsupp.mapDomain.linearEquiv M R e).apply_symm_apply c.val
  map_add' a b := by apply Subtype.ext; exact Finsupp.mapDomain_add
  map_smul' r a := by
    apply Subtype.ext
    exact (Finsupp.lmapDomain M R e).map_smul r a.val

/-- The kernel of the sum on two copies of `M` is `M`, by `m ↦ (m,-m)`. -/
def twoPointSumKernel : LinearMap.ker (sumCoefficients R M (Fin 2)) ≃ₗ[R] M where
  toFun c := c.val 0
  invFun m := ⟨Finsupp.single 0 m - Finsupp.single 1 m, by
    change sumCoefficients R M (Fin 2) _ = 0
    rw [map_sub]
    simp [sumCoefficients]⟩
  left_inv c := by
    apply Subtype.ext
    have hc := c.property
    change sumCoefficients R M (Fin 2) c.val = 0 at hc
    have hs : sumCoefficients R M (Fin 2) =
        Finsupp.lapply 0 + Finsupp.lapply 1 := by
      apply Finsupp.lhom_ext
      intro i m
      fin_cases i <;> simp [sumCoefficients]
    have hc' : c.val 0 + c.val 1 = 0 := (LinearMap.congr_fun hs c.val).symm.trans hc
    ext i
    fin_cases i
    · simp
    · simpa using (eq_neg_of_add_eq_zero_right hc').symm
  right_inv m := by simp
  map_add' a b := rfl
  map_smul' r a := rfl

theorem sphereReducedZero : Expected.sphereReducedZero.{u,v,w} := by
  intro R _ M _ _
  obtain ⟨e⟩ := reducedDegreeZero R M zeroSphere.{w}
  let f : ZerothHomotopy zeroSphere.{w} ≃ Fin 2 :=
    (componentsOfTotallyDisconnected zeroSphere.{w}).trans Equiv.ulift
  exact ⟨e.trans ((sumKernelReindex R M f).trans (twoPointSumKernel R M))⟩

end P202.SingularDegreeZero
