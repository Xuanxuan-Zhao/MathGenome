import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.CellularDegrees
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.Degree
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-! Cellular attaching coefficients, paper.tex 1543–1557.

The actual skeletal differential is computed in characteristic-compatible
coordinates. Independent geometric orientation charts give the integral degree
formula with arbitrary coefficients; oriented intervals give final minus initial.
The support argument uses closure finiteness and applies to infinite CW complexes.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory HomologicalComplex Topology
open scoped Simplicial
universe u v w

namespace P202.Homology.CellularDegrees
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.CellularDegrees

theorem cellCollapse : Expected.cellCollapse.{w} := by
  classical
  intro X _ _ n c b
  let P := P202Specs.SpheresDisks.diskPair n
  let Q := P202Specs.GoodPairQuotient.quotientSpace P
  let π := P202Specs.GoodPairQuotient.quotientProjection P
  let p : Q := π (boundaryInclusion n b)
  have hb (z : Sphere n) : π (boundaryInclusion n z) = p := by
    apply Quotient.sound
    apply Or.inr
    constructor
    · change ‖z.val‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using z.property
    · change ‖b.val‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using b.property
  let f : C(skeletonLT X n, Q) := ContinuousMap.const _ p
  let diskProjection : C(Disk n, Q) := ⟨fun x => π x, π.hom.continuous⟩
  let g : ∀ _d : Cell X n, C(Disk n, Q) :=
    fun d => if d = c then diskProjection else ContinuousMap.const _ p
  have hcompat (d : Cell X n) (z : Sphere n) :
      g d (boundaryInclusion n z) = f (attachingMap n d z) := by
    by_cases h : d = c
    · simpa [g, f, h, diskProjection] using hb z
    · simp [g, f, h]
  obtain ⟨q, ⟨hqold, hqcell⟩, _⟩ := P202.Topology.attachmentPushout n f g hcompat
  refine ⟨q, ?_, hqold, ?_, ?_⟩
  · have hcomp : (fun x : Disk n => q (diskToSkeleton X CWStructure.boundary_lands n c x)) = π := by
      funext x
      simpa [g, diskProjection] using hqcell c x
    apply IsQuotientMap.of_comp
      ((characteristic X n c).continuous.subtype_mk _) q.continuous
    change IsQuotientMap (fun x : Disk n => q (diskToSkeleton X CWStructure.boundary_lands n c x))
    rw [hcomp]
    exact isQuotientMap_quotient_mk'
  · intro d x
    by_cases h : d = c
    · simpa [g, diskProjection, h] using hqcell d x
    · simpa [g, h] using hqcell d x
  · intro x hx
    obtain ⟨y, hy⟩ := (CWStructure.attachment_quotient (X := X) n).surjective x
    cases y with
    | inl y =>
      change oldSkeletonInclusion X n y = x at hy
      rw [← hy]
      exact hqold y
    | inr y =>
      obtain ⟨d, z⟩ := y
      change diskToSkeleton X CWStructure.boundary_lands n d z = x at hy
      by_cases hd : d = c
      · subst d
        have hz : ‖z.val‖ = 1 := by
          have hle : ‖z.val‖ ≤ 1 := by
            simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
          apply le_antisymm hle
          by_contra h
          have hlt : ‖z.val‖ < 1 := lt_of_not_ge h
          apply hx
          rw [← hy]
          exact ⟨⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hlt⟩, rfl⟩
        have hzπ : π z = p := by
          apply Quotient.sound
          exact Or.inr ⟨hz, by
            change ‖b.val‖ = 1
            simpa only [Metric.mem_sphere, dist_zero_right] using b.property⟩
        rw [← hy]
        have hqz : q (diskToSkeleton X CWStructure.boundary_lands n c z) = π z := by
          simpa [g, diskProjection] using hqcell c z
        exact hqz.trans hzπ
      · rw [← hy]
        simpa [g, hd] using hqcell d z

theorem attachingNaturality :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (c : Cell X (n+1))
    (a : relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ)),
    differential X R M n (cellClass X R M (n+1) c a) =
      homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ)
        ((homologyFunctor R M (n : ℤ)).map (attachingBoundary X n c)
          (pairConnecting R M (referenceDiskPair.{w} (n+1)) n a)) := by
  intro X _ _ R _ M _ _ n c a
  have h := P202.Homology.pairConnecting_natural R M
    (characteristicPairMap (X := X) (n+1) c) n
  have ha := congrArg (fun f => f a) h
  dsimp only [cellClass, differential, attachingBoundary]
  simp only [Functor.map_comp, ModuleCat.comp_apply]
  simp only [ModuleCat.comp_apply] at ha
  exact congrArg (fun x =>
    homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ)
      ((homologyFunctor R M (n : ℤ)).map (lowerMap X (n+1)) x)) ha.symm

section Coordinates
variable (X : Type w) [TopologicalSpace X] [CWStructure X]
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable (n : ℕ)
variable (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))

lemma coordinates_symm_single
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : CharacteristicCoordinates X R M n g e) (c : Cell X n) (m : M) :
    e.symm (Finsupp.single c m) = cellClass X R M n c (g m) := by
  apply e.injective
  rw [e.apply_symm_apply, he]

lemma coordinates_unique
    (e f : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : CharacteristicCoordinates X R M n g e)
    (hf : CharacteristicCoordinates X R M n g f) : e = f := by
  have hi : e.symm.toLinearMap = f.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro c m
    exact (coordinates_symm_single X R M n g e he c m).trans
      (coordinates_symm_single X R M n g f hf c m).symm
  have hs : e.symm = f.symm := LinearEquiv.toLinearMap_injective hi
  simpa using congrArg LinearEquiv.symm hs

/-- The finite-support property comes from an actual characteristic-compatible
direct sum, rather than replacing homology by a freely chosen free module. -/
lemma boundary_finite_support :
    ∃ e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M),
      CharacteristicCoordinates X R M n g e ∧
      ∀ z : chainGroup X R M (n+1),
        ∃ F : Finset (Cell X n), ∀ c, c ∉ F → e (differential X R M n z) c = 0 := by
  classical
  obtain ⟨e, he⟩ := P202.Homology.cellularOrientedCoordinates X R M n g
  refine ⟨e, he, fun z => ⟨(e (differential X R M n z)).support, ?_⟩⟩
  intro c hc
  exact Finsupp.notMem_support_iff.mp hc

end Coordinates

theorem coordinatesUnique :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ)
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e f : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M)),
    CharacteristicCoordinates X R M n g e →
    CharacteristicCoordinates X R M n g f → e = f := by
  intro X _ _ R _ M _ _ n g e f he hf
  exact coordinates_unique X R M n g e f he hf

theorem boundaryFiniteSupport :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ)
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)),
    ∃ e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M),
      CharacteristicCoordinates X R M n g e ∧
      ∀ z : chainGroup X R M (n+1),
        ∃ F : Finset (Cell X n), ∀ c, c ∉ F → e (differential X R M n z) c = 0 := by
  intro X _ _ R _ M _ _ n g
  exact boundary_finite_support X R M n g

section Endpoints
open CategoryTheory.Limits Opposite
open scoped Simplicial
open P202Specs.SpheresDisks
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

lemma simplexChainZ_map {Y Z : TopCat.{w}} (f : Y ⟶ Z) (n : ℕ)
    (s : Simplex Y n) (m : M) :
    ((ordinaryFunctor R M).map f).f (n : ℤ) (simplexChainZ R M Y n s m) =
      simplexChainZ R M Z n ((TopCat.toSSet.map f).app (op ⦋n⦌) s) m := by
  have hmap : (ordinaryNonnegativeIso R M Y n).inv ≫
      ((ordinaryFunctor R M).map f).f (n : ℤ) ≫
        (ordinaryNonnegativeIso R M Z n).hom = (chainMap R M f).f n := by
    change (ordinaryNonnegativeIso R M Y n).inv ≫
      (extendMap ((chainFunctor R M).map f) (degreeEmbedding 0)).f (n : ℤ) ≫ _ = _
    rw [HomologicalComplex.extendMap_f _ _
      (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)]
    simp [ordinaryNonnegativeIso]
  have hc := congrArg (fun f => f (Finsupp.single s m)) hmap
  apply (ordinaryNonnegativeIso R M Z n).toLinearEquiv.injective
  change (ordinaryNonnegativeIso R M Z n).hom
    (((ordinaryFunctor R M).map f).f (n : ℤ)
      ((ordinaryNonnegativeIso R M Y n).inv (Finsupp.single s m))) = _
  simp only [ModuleCat.comp_apply] at hc
  exact hc.trans (by simpa [simplexChainZ] using P202.SingularChains.chainMap_single R M f n s m)

lemma pointSimplex_map {Y Z : TopCat.{w}} (f : Y ⟶ Z) (p : Y) :
    (TopCat.toSSet.map f).app (op ⦋0⦌) (pointSimplex Y p) = pointSimplex Z (f p) := by
  apply (simplexEquiv Z 0).injective
  rw [P202.SingularChains.simplexEquiv_postcomp]
  simp [pointSimplex]

lemma simplex_zero_equiv (Y : TopCat.{w}) : Function.Bijective (pointSimplex Y) := by
  constructor
  · intro p q h
    have h' := congrArg (fun s => simplexEquiv Y 0 s (Convexity.StdSimplex.single 0)) h
    simpa [pointSimplex] using h'
  · intro s
    refine ⟨simplexEquiv Y 0 s (Convexity.StdSimplex.single 0), ?_⟩
    apply (simplexEquiv Y 0).injective
    ext x
    have hx : x = Convexity.StdSimplex.single 0 := Subsingleton.elim _ _
    simp [pointSimplex, hx]

lemma disconnected_boundary_one (Y : TopCat.{w}) [TotallyDisconnectedSpace Y] :
    (ordinaryComplex R M Y).d 1 0 = 0 := by
  have he (s : Simplex Y 1) : face 0 s = face 1 s := by
    let e := TopCat.toSSetIsoConst Y
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app (op ⦋0⦌))).injective
    have h0 := congrArg (fun f => f s) (e.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op)
    have h1 := congrArg (fun f => f s) (e.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op)
    exact h0.trans h1.symm
  apply (cancel_epi (ordinaryNonnegativeIso R M Y 1).inv).mp
  apply (cancel_mono (ordinaryNonnegativeIso R M Y 0).hom).mp
  simp only [zero_comp, comp_zero]
  trans (complex R M Y).d 1 0
  · simpa only [Nat.reduceAdd, Int.ofNat_zero, Int.ofNat_one, Category.assoc] using
      P202.SingularChains.ordinary_boundary R M Y 0
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s m
  change boundary R M Y 0 (Finsupp.single s m) = 0
  rw [P202.SingularChains.boundary_single]
  simp [Fin.sum_univ_two, he]

/-- On a totally disconnected space, H₀ is the actual zero-chain module. -/
def zeroChainEquiv (Y : TopCat.{w}) [TotallyDisconnectedSpace Y] :
    homology R M Y 0 ≃ₗ[R] (Y →₀ M) := by
  let K := ordinaryComplex R M Y
  haveI : IsIso (K.iCycles 0) := K.isIso_iCycles 0 (-1) (by simp)
    (P202.SingularChains.ordinary_boundary_zero R M Y (-1))
  haveI : IsIso (K.homologyπ 0) := K.isIso_homologyπ 1 0 (by simp)
    (disconnected_boundary_one R M Y)
  exact (asIso (K.homologyπ 0)).symm.toLinearEquiv.trans
    ((asIso (K.iCycles 0)).toLinearEquiv.trans
      ((ordinaryNonnegativeIso R M Y 0).toLinearEquiv.trans
        (Finsupp.mapDomain.linearEquiv M R
          (Equiv.ofBijective (pointSimplex Y) (simplex_zero_equiv Y)).symm)))

lemma zeroChainEquiv_class (Y : TopCat.{w}) [TotallyDisconnectedSpace Y]
    (z : (ordinaryComplex R M Y).X 0)
    (hz : (ordinaryComplex R M Y).d 0 (-1) z = 0) :
    zeroChainEquiv R M Y (classOf R (ordinaryComplex R M Y) 0 z hz) =
      Finsupp.mapDomain (Equiv.ofBijective (pointSimplex Y) (simplex_zero_equiv Y)).symm
        ((ordinaryNonnegativeIso R M Y 0).hom z) := by
  haveI : IsIso ((ordinaryComplex R M Y).iCycles 0) :=
    (ordinaryComplex R M Y).isIso_iCycles 0 (-1) (by simp)
      (P202.SingularChains.ordinary_boundary_zero R M Y (-1))
  haveI : IsIso ((ordinaryComplex R M Y).homologyπ 0) :=
    (ordinaryComplex R M Y).isIso_homologyπ 1 0 (by simp) (disconnected_boundary_one R M Y)
  let K := ordinaryComplex R M Y
  have hc : (asIso (K.homologyπ 0)).inv
      (K.homologyπ 0 (K.cyclesMk z (-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hz)) =
      K.cyclesMk z (-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hz :=
    (asIso (K.homologyπ 0)).toLinearEquiv.symm_apply_apply _
  have hv : K.iCycles 0 ((asIso (K.homologyπ 0)).inv
      (K.homologyπ 0 (K.cyclesMk z (-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hz))) = z :=
    (congrArg (K.iCycles 0) hc).trans (K.i_cyclesMk _ _ _ _)
  exact congrArg (fun t => Finsupp.mapDomain
    (Equiv.ofBijective (pointSimplex Y) (simplex_zero_equiv Y)).symm
      ((ordinaryNonnegativeIso R M Y 0).hom t)) hv

/-- The boundary of a singular interval is final endpoint minus initial endpoint,
before taking relative homology. -/
lemma relativeSimplexChain_map {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ)
    (s : Simplex P.space n) (m : M) :
    (relativeMap (ordinaryFunctor R M) f).f (n : ℤ)
      (relativeSimplexChain R M P n s m) =
    relativeSimplexChain R M Q n ((TopCat.toSSet.map f.map).app (op ⦋n⦌) s) m := by
  have hp := congrArg (fun f => f.f (n : ℤ)) (projection_map (ordinaryFunctor R M) f)
  have hc := congrArg (fun f => f (simplexChainZ R M P.space n s m)) hp
  change (relativeMap (ordinaryFunctor R M) f).f (n : ℤ)
      ((projection (ordinaryFunctor R M) P).f (n : ℤ) (simplexChainZ R M P.space n s m)) =
    (projection (ordinaryFunctor R M) Q).f (n : ℤ)
      (simplexChainZ R M Q.space n ((TopCat.toSSet.map f.map).app (op ⦋n⦌) s) m)
  exact hc.trans (congrArg ((projection (ordinaryFunctor R M) Q).f (n : ℤ))
    (simplexChainZ_map R M f.map n s m))

lemma pointSimplex_pair_square {P Q : Pair.{w}} (f : P ⟶ Q) (p : P.sub) :
    (TopCat.toSSet.map f.map).app (op ⦋0⦌)
      ((TopCat.toSSet.map P.inclusion).app (op ⦋0⦌) (pointSimplex P.sub p)) =
    (TopCat.toSSet.map Q.inclusion).app (op ⦋0⦌) (pointSimplex Q.sub (f.restrict p)) := by
  simp only [pointSimplex_map]
  rfl

lemma interval_boundary_lift (P : Pair.{w}) (s : Simplex P.space 1) (a b : P.sub)
    (ha : face 0 s = (TopCat.toSSet.map P.inclusion).app (op ⦋0⦌) (pointSimplex P.sub a))
    (hb : face 1 s = (TopCat.toSSet.map P.inclusion).app (op ⦋0⦌) (pointSimplex P.sub b))
    (m : M) :
    ((ordinaryFunctor R M).map P.inclusion).f 0
      (simplexChainZ R M P.sub 0 (pointSimplex P.sub a) m -
        simplexChainZ R M P.sub 0 (pointSimplex P.sub b) m) =
      (ordinaryComplex R M P.space).d 1 0 (simplexChainZ R M P.space 1 s m) := by
  rw [map_sub]
  refine (congrArg₂ (· - ·) (simplexChainZ_map R M P.inclusion 0 (pointSimplex P.sub a) m)
    (simplexChainZ_map R M P.inclusion 0 (pointSimplex P.sub b) m)).trans ?_
  rw [← ha, ← hb]
  apply (ordinaryNonnegativeIso R M P.space 0).toLinearEquiv.injective
  have hd := congrArg (fun f => f (Finsupp.single s m))
    (P202.SingularChains.ordinary_boundary R M P.space 0)
  simp only [ModuleCat.comp_apply] at hd
  refine Eq.trans ?_ hd.symm
  simp only [simplexChainZ, map_sub, Iso.toLinearEquiv_apply, Iso.inv_hom_id_apply]
  change Finsupp.single (face 0 s) m - Finsupp.single (face 1 s) m =
    boundary R M P.space 0 (Finsupp.single s m)
  rw [P202.SingularChains.boundary_single]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

lemma relativePath_cycle (P : Pair.{w}) (s : Simplex P.space 1) (a b : P.sub)
    (ha : face 0 s = (TopCat.toSSet.map P.inclusion).app (op ⦋0⦌) (pointSimplex P.sub a))
    (hb : face 1 s = (TopCat.toSSet.map P.inclusion).app (op ⦋0⦌) (pointSimplex P.sub b))
    (m : M) :
    (ordinary R M P).d 1 0 (relativeSimplexChain R M P 1 s m) = 0 := by
  let π := projection (ordinaryFunctor R M) P
  have hc := congrArg (fun f => f (simplexChainZ R M P.space 1 s m)) (π.comm 1 0)
  change (ordinary R M P).d 1 0 (π.f 1 (simplexChainZ R M P.space 1 s m)) = 0
  change (ordinary R M P).d 1 0 (π.f 1 (simplexChainZ R M P.space 1 s m)) =
    π.f 0 ((ordinaryComplex R M P.space).d 1 0 (simplexChainZ R M P.space 1 s m)) at hc
  rw [hc, ← interval_boundary_lift R M P s a b ha hb m]
  exact congrArg (fun f => f (simplexChainZ R M P.sub 0 (pointSimplex P.sub a) m -
    simplexChainZ R M P.sub 0 (pointSimplex P.sub b) m))
      (congrArg (fun f => f.f 0) (cokernel.condition (inclusion (ordinaryFunctor R M) P)))

lemma pairConnecting_path (P : Pair.{w}) (s : Simplex P.space 1) (a b : P.sub)
    (ha : face 0 s = (TopCat.toSSet.map P.inclusion).app (op ⦋0⦌) (pointSimplex P.sub a))
    (hb : face 1 s = (TopCat.toSSet.map P.inclusion).app (op ⦋0⦌) (pointSimplex P.sub b))
    (m : M) :
    pairConnecting R M P 0
      (classOf R (ordinary R M P) 1 (relativeSimplexChain R M P 1 s m)
        (relativePath_cycle R M P s a b ha hb m)) =
    classOf R (ordinaryComplex R M P.sub) 0
      (simplexChainZ R M P.sub 0 (pointSimplex P.sub a) m -
        simplexChainZ R M P.sub 0 (pointSimplex P.sub b) m)
      (by rw [P202.SingularChains.ordinary_boundary_zero]; rfl) := by
  let h := P202.RelativeSingularChains.ordinary_short_exact R M P
  rw [pairConnecting_eq R M P 0 h]
  exact P202.ChainLES.lift_formula _ h 1 0 (by simp)
    (relativeSimplexChain R M P 1 s m) (relativePath_cycle R M P s a b ha hb m)
    (simplexChainZ R M P.space 1 s m) rfl
    (simplexChainZ R M P.sub 0 (pointSimplex P.sub a) m -
      simplexChainZ R M P.sub 0 (pointSimplex P.sub b) m)
    (interval_boundary_lift R M P s a b ha hb m)
    (by
      change (ordinaryComplex R M P.sub).d 0 ((ComplexShape.down ℤ).next 0) _ = 0
      rw [P202.SingularChains.ordinary_boundary_zero]; rfl)

variable (X : Type w) [TopologicalSpace X] [CWStructure X]

/-- Vertex coordinates with the positive point normalization. -/
def positiveVertexEquiv : chainGroup X R M 0 ≃ₗ[R] (Cell X 0 →₀ M) := by
  letI := P202.Homology.zeroSkeleton_discrete X
  letI := P202.Homology.zeroSkeleton_projection_isIso X R M
  exact (asIso (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X 0)) 0)).symm.toLinearEquiv.trans
    ((zeroChainEquiv R M (skeletalSpace X 1)).trans
      (Finsupp.mapDomain.linearEquiv M R (P202.Homology.vertexEquiv X).symm))

lemma positiveVertexEquiv_projection
    (z : (ordinaryComplex R M (skeletalSpace X 1)).X 0)
    (hz : (ordinaryComplex R M (skeletalSpace X 1)).d 0 (-1) z = 0) :
    positiveVertexEquiv R M X
      (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X 0)) 0
        (classOf R (ordinaryComplex R M (skeletalSpace X 1)) 0 z hz)) =
      Finsupp.mapDomain (P202.Homology.vertexEquiv X).symm
        (Finsupp.mapDomain (Equiv.ofBijective (pointSimplex (skeletalSpace X 1))
          (simplex_zero_equiv (skeletalSpace X 1))).symm
            ((ordinaryNonnegativeIso R M (skeletalSpace X 1) 0).hom z)) := by
  letI := P202.Homology.zeroSkeleton_discrete X
  letI := P202.Homology.zeroSkeleton_projection_isIso X R M
  let π := homologyMap (projection (ordinaryFunctor R M) (skeletalPair X 0)) 0
  have hc : (asIso π).inv (π
      (classOf R (ordinaryComplex R M (skeletalSpace X 1)) 0 z hz)) =
      classOf R (ordinaryComplex R M (skeletalSpace X 1)) 0 z hz :=
    (asIso π).toLinearEquiv.symm_apply_apply _
  change Finsupp.mapDomain _ (zeroChainEquiv R M (skeletalSpace X 1)
    ((asIso π).inv (π _))) = _
  rw [hc, zeroChainEquiv_class]
  rfl

/-- Naturality of cycle classes without a constraint on the ring universe. -/
lemma homologyMap_classOf {K L : ChainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L)
    (n : ℤ) (z : K.X n) (hz : K.d n (n-1) z = 0)
    (hfz : L.d n (n-1) (f.f n z) = 0) :
    homologyMap f n (classOf R K n z hz) = classOf R L n (f.f n z) hfz := by
  change homologyMap f n (K.homologyπ n (K.cyclesMk z (n-1) _ hz)) =
    L.homologyπ n (L.cyclesMk (f.f n z) (n-1) _ hfz)
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply]
  exact (congrArg (f.f n) (K.i_cyclesMk _ _ _ _)).trans (L.i_cyclesMk _ _ _ _).symm

/-- Signed endpoint incidence for every interval class in the skeletal pair. -/
lemma path_boundary_coordinates (s : Simplex (skeletalPair X 1).space 1)
    (a b : (skeletalPair X 1).sub)
    (ha : face 0 s = (TopCat.toSSet.map (skeletalPair X 1).inclusion).app (op ⦋0⦌)
      (pointSimplex (skeletalPair X 1).sub a))
    (hb : face 1 s = (TopCat.toSSet.map (skeletalPair X 1).inclusion).app (op ⦋0⦌)
      (pointSimplex (skeletalPair X 1).sub b)) (m : M) :
    positiveVertexEquiv R M X
      (differential X R M 0
        (classOf R (ordinary R M (skeletalPair X 1)) 1
          (relativeSimplexChain R M (skeletalPair X 1) 1 s m)
          (relativePath_cycle R M (skeletalPair X 1) s a b ha hb m))) =
    Finsupp.single ((P202.Homology.vertexEquiv X).symm (lowerHomeomorph X 1 a)) m -
      Finsupp.single ((P202.Homology.vertexEquiv X).symm (lowerHomeomorph X 1 b)) m := by
  let P := skeletalPair X 1
  let z := simplexChainZ R M P.sub 0 (pointSimplex P.sub a) m -
    simplexChainZ R M P.sub 0 (pointSimplex P.sub b) m
  have hz : (ordinaryComplex R M P.sub).d 0 (-1) z = 0 := by
    rw [P202.SingularChains.ordinary_boundary_zero]; rfl
  have hmap := homologyMap_classOf R ((ordinaryFunctor R M).map (lowerMap X 1)) 0 z hz
    (by
      change (ordinaryComplex R M (skeletalSpace X 1)).d 0 (-1) _ = 0
      rw [P202.SingularChains.ordinary_boundary_zero]; rfl)
  change positiveVertexEquiv R M X
    (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X 0)) 0
      ((homologyFunctor R M 0).map (lowerMap X 1) (pairConnecting R M P 0 _))) = _
  rw [pairConnecting_path R M P s a b ha hb m]
  change positiveVertexEquiv R M X
    (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X 0)) 0
      (homologyMap ((ordinaryFunctor R M).map (lowerMap X 1)) 0
        (classOf R (ordinaryComplex R M P.sub) 0 z hz))) = _
  refine (congrArg (fun t => positiveVertexEquiv R M X
    (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X 0)) 0 t)) hmap).trans ?_
  change positiveVertexEquiv R M X
    (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X 0)) 0
      (classOf R (ordinaryComplex R M (skeletalSpace X 1)) 0
        (((ordinaryFunctor R M).map (lowerMap X 1)).f 0 z) _)) = _
  rw [positiveVertexEquiv_projection]
  have ha' : ((ordinaryFunctor R M).map (lowerMap X 1)).f 0
      (simplexChainZ R M P.sub 0 (pointSimplex P.sub a) m) =
      simplexChainZ R M (skeletalSpace X 1) 0
        (pointSimplex (skeletalSpace X 1) (lowerHomeomorph X 1 a)) m :=
    (simplexChainZ_map R M (lowerMap X 1) 0 (pointSimplex P.sub a) m).trans
      (congrArg (fun t => simplexChainZ R M (skeletalSpace X 1) 0 t m)
        (pointSimplex_map (lowerMap X 1) a))
  have hb' : ((ordinaryFunctor R M).map (lowerMap X 1)).f 0
      (simplexChainZ R M P.sub 0 (pointSimplex P.sub b) m) =
      simplexChainZ R M (skeletalSpace X 1) 0
        (pointSimplex (skeletalSpace X 1) (lowerHomeomorph X 1 b)) m :=
    (simplexChainZ_map R M (lowerMap X 1) 0 (pointSimplex P.sub b) m).trans
      (congrArg (fun t => simplexChainZ R M (skeletalSpace X 1) 0 t m)
        (pointSimplex_map (lowerMap X 1) b))
  simp only [z, map_sub]
  rw [ha', hb']
  simp only [simplexChainZ, map_sub, Iso.inv_hom_id_apply,
    Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have he (p : skeletalSpace X 1) :
      (Equiv.ofBijective (pointSimplex (skeletalSpace X 1))
        (simplex_zero_equiv (skeletalSpace X 1))).symm
        (pointSimplex (skeletalSpace X 1) p) = p := Equiv.symm_apply_apply _ p
  change Finsupp.mapDomain (P202.Homology.vertexEquiv X).symm
    (Finsupp.mapDomain (Equiv.ofBijective (pointSimplex (skeletalSpace X 1))
      (simplex_zero_equiv (skeletalSpace X 1))).symm
      ((Finsupp.single (pointSimplex (skeletalSpace X 1) (lowerHomeomorph X 1 a)) m :
        Simplex (skeletalSpace X 1) 0 →₀ M) -
        Finsupp.single (pointSimplex (skeletalSpace X 1) (lowerHomeomorph X 1 b)) m)) = _
  simp only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, he]

/-- Applying the one-cell characteristic map preserves the signed endpoints. -/
lemma cell_path_boundary (c : Cell X 1)
    (s : Simplex (referenceDiskPair.{w} 1).space 1)
    (a b : (referenceDiskPair.{w} 1).sub)
    (ha : face 0 s = (TopCat.toSSet.map (referenceDiskPair.{w} 1).inclusion).app (op ⦋0⦌)
      (pointSimplex (referenceDiskPair.{w} 1).sub a))
    (hb : face 1 s = (TopCat.toSSet.map (referenceDiskPair.{w} 1).inclusion).app (op ⦋0⦌)
      (pointSimplex (referenceDiskPair.{w} 1).sub b)) (m : M) :
    positiveVertexEquiv R M X (differential X R M 0
      (cellClass X R M 1 c (classOf R (ordinary R M (referenceDiskPair.{w} 1)) 1
        (relativeSimplexChain R M (referenceDiskPair.{w} 1) 1 s m)
        (relativePath_cycle R M (referenceDiskPair.{w} 1) s a b ha hb m)))) =
    Finsupp.single ((P202.Homology.vertexEquiv X).symm (attachingBoundary X 0 c a)) m -
      Finsupp.single ((P202.Homology.vertexEquiv X).symm (attachingBoundary X 0 c b)) m := by
  let f := characteristicPairMap (X := X) 1 c
  let t := (TopCat.toSSet.map f.map).app (op ⦋1⦌) s
  have ha' : face 0 t = (TopCat.toSSet.map (skeletalPair X 1).inclusion).app (op ⦋0⦌)
      (pointSimplex (skeletalPair X 1).sub (f.restrict a)) := by
    have hn := congrArg (fun g => g s)
      ((TopCat.toSSet.map f.map).naturality (SimplexCategory.δ (0 : Fin 2)).op)
    exact hn.symm.trans ((congrArg ((TopCat.toSSet.map f.map).app (op ⦋0⦌)) ha).trans
      (pointSimplex_pair_square f a))
  have hb' : face 1 t = (TopCat.toSSet.map (skeletalPair X 1).inclusion).app (op ⦋0⦌)
      (pointSimplex (skeletalPair X 1).sub (f.restrict b)) := by
    have hn := congrArg (fun g => g s)
      ((TopCat.toSSet.map f.map).naturality (SimplexCategory.δ (1 : Fin 2)).op)
    exact hn.symm.trans ((congrArg ((TopCat.toSSet.map f.map).app (op ⦋0⦌)) hb).trans
      (pointSimplex_pair_square f b))
  have hm := homologyMap_classOf R (relativeMap (ordinaryFunctor R M) f) 1
    (relativeSimplexChain R M (referenceDiskPair.{w} 1) 1 s m)
    (relativePath_cycle R M (referenceDiskPair.{w} 1) s a b ha hb m)
    (by
      exact (congrArg ((ordinary R M (skeletalPair X 1)).d 1 0)
        (relativeSimplexChain_map R M f 1 s m)).trans
          (relativePath_cycle R M (skeletalPair X 1) t (f.restrict a) (f.restrict b) ha' hb' m))
  have hclass : cellClass X R M 1 c
      (classOf R (ordinary R M (referenceDiskPair.{w} 1)) 1
        (relativeSimplexChain R M (referenceDiskPair.{w} 1) 1 s m)
        (relativePath_cycle R M (referenceDiskPair.{w} 1) s a b ha hb m)) =
      classOf R (ordinary R M (skeletalPair X 1)) 1
        (relativeSimplexChain R M (skeletalPair X 1) 1 t m)
        (relativePath_cycle R M (skeletalPair X 1) t (f.restrict a) (f.restrict b) ha' hb' m) := by
    exact hm.trans (by congr 1; exact relativeSimplexChain_map R M f 1 s m)
  exact (congrArg (fun z => positiveVertexEquiv R M X (differential X R M 0 z)) hclass).trans
    (path_boundary_coordinates R M X t (f.restrict a) (f.restrict b) ha' hb' m)

lemma positiveVertexEquiv_point (p : skeletalSpace X 1) (m : M) :
    positiveVertexEquiv R M X (relativePointClass R M (skeletalPair X 0) p m) =
      Finsupp.single ((P202.Homology.vertexEquiv X).symm p) m := by
  unfold relativePointClass
  change positiveVertexEquiv R M X
    (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X 0)) 0
      (classOf R (ordinaryComplex R M (skeletalSpace X 1)) 0
        (simplexChainZ R M (skeletalSpace X 1) 0 (pointSimplex (skeletalSpace X 1) p) m) _)) = _
  rw [positiveVertexEquiv_projection]
  simp only [simplexChainZ, Iso.inv_hom_id_apply]
  change Finsupp.mapDomain (P202.Homology.vertexEquiv X).symm
    (Finsupp.mapDomain (Equiv.ofBijective (pointSimplex (skeletalSpace X 1))
      (simplex_zero_equiv (skeletalSpace X 1))).symm
      (Finsupp.single (pointSimplex (skeletalSpace X 1) p) m :
        Simplex (skeletalSpace X 1) 0 →₀ M)) = _
  simp only [Finsupp.mapDomain_single]
  have he : (Equiv.ofBijective (pointSimplex (skeletalSpace X 1))
      (simplex_zero_equiv (skeletalSpace X 1))).symm
      (pointSimplex (skeletalSpace X 1) p) = p := Equiv.symm_apply_apply _ p
  rw [he]

/-- An ordered disk interval has its indicated final and initial faces. -/
lemma interval_face (h : IntervalParametrization) (i : Fin 2) :
    face i h.simplex = (TopCat.toSSet.map (referenceDiskPair.{w} 1).inclusion).app
      (op ⦋0⦌) (pointSimplex (referenceDiskPair.{w} 1).sub (h.endpoint i)) := by
  apply (simplexEquiv _ 0).injective
  rw [P202.SingularChains.simplexEquiv_face, P202.SingularChains.simplexEquiv_postcomp]
  simp only [IntervalParametrization.simplex, pointSimplex, Equiv.apply_symm_apply]
  ext x
  have hx : x = Convexity.StdSimplex.single 0 := Subsingleton.elim _ _
  subst x
  rfl

/-- Transport across the reference disk universe preserves each weighted simplex. -/
lemma ordinaryTransport_simplexChainZ {Y : TopCat.{0}} {Z : TopCat.{w}}
    (e : Y ≃ₜ Z) (n : ℕ) (s : Simplex Y n) (m : M) :
    (P202.Homology.DiskBridge.ordinaryTransport R M e).hom.f (n : ℤ)
      (simplexChainZ R (ULift.{w} M) Y n s (ULift.up m)) =
    simplexChainZ R M Z n (P202.Homology.DiskBridge.simplexTransport e n s) m := by
  have hmap : (ordinaryNonnegativeIso R (ULift.{w} M) Y n).inv ≫
      (P202.Homology.DiskBridge.ordinaryTransport R M e).hom.f (n : ℤ) ≫
        (ordinaryNonnegativeIso R M Z n).hom =
      (P202.Homology.DiskBridge.complexTransport R M e).hom.f n := by
    change (ordinaryNonnegativeIso R (ULift.{w} M) Y n).inv ≫
      (extendMap (P202.Homology.DiskBridge.complexTransport R M e).hom
        (degreeEmbedding 0)).f (n : ℤ) ≫ _ = _
    rw [HomologicalComplex.extendMap_f _ _
      (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)]
    simp [ordinaryNonnegativeIso]
  have hc := congrArg (fun f => f (Finsupp.single s (ULift.up m))) hmap
  apply (ordinaryNonnegativeIso R M Z n).toLinearEquiv.injective
  change (ordinaryNonnegativeIso R M Z n).hom
    ((P202.Homology.DiskBridge.ordinaryTransport R M e).hom.f (n : ℤ)
      ((ordinaryNonnegativeIso R (ULift.{w} M) Y n).inv (Finsupp.single s (ULift.up m)))) = _
  simp only [ModuleCat.comp_apply] at hc
  refine hc.trans ?_
  simp only [simplexChainZ, Iso.toLinearEquiv_apply, Iso.inv_hom_id_apply]
  change P202.Homology.DiskBridge.chainsTransport R M e n
      (Finsupp.single s (ULift.up m)) = _
  exact P202.Homology.DiskBridge.chainsTransport_single R M e n s (ULift.up m)

/-- The relative interval transport includes both its boundary and coefficient universe. -/
def intervalRelativeTransport (h : IntervalParametrization) :
    ordinary R (ULift.{w} M) (simplexPair 1) ≅
      ordinary R M (referenceDiskPair.{w} 1) :=
  P202.Homology.DiskBridge.relativeTransport R M h.referenceHomeomorph
    h.boundaryHomeomorph (fun _ => rfl)

lemma intervalRelativeTransport_affine (h : IntervalParametrization) (m : M) :
    (intervalRelativeTransport R M h).hom.f 1
      (relativeAffineChain R (ULift.{w} M) 1 (ULift.up m)) =
    relativeSimplexChain R M (referenceDiskPair.{w} 1) 1 h.simplex m := by
  have hp : projection (ordinaryFunctor R (ULift.{w} M)) (simplexPair 1) ≫
      (intervalRelativeTransport R M h).hom =
    (P202.Homology.DiskBridge.ordinaryTransport R M h.referenceHomeomorph).hom ≫
      projection (ordinaryFunctor R M) (referenceDiskPair.{w} 1) :=
    cokernel.π_desc _ _ _
  have hc := congrArg (fun f => f.f (1 : ℤ)
    (affineChainZ R (ULift.{w} M) 1 (ULift.up m))) hp
  change (intervalRelativeTransport R M h).hom.f 1
      (relativeAffineChain R (ULift.{w} M) 1 (ULift.up m)) =
    (projection (ordinaryFunctor R M) (referenceDiskPair.{w} 1)).f 1
      ((P202.Homology.DiskBridge.ordinaryTransport R M h.referenceHomeomorph).hom.f 1
        (simplexChainZ R (ULift.{w} M) (simplex 1) 1 (affineSimplex 1) (ULift.up m))) at hc
  refine hc.trans (congrArg ((projection (ordinaryFunctor R M) (referenceDiskPair.{w} 1)).f 1) ?_)
  refine (ordinaryTransport_simplexChainZ R M h.referenceHomeomorph 1 (affineSimplex 1) m).trans ?_
  congr 1

/-- Each parametrized oriented interval is a genuine relative generator,
with arbitrary coefficients and the specified simplex representative. -/
lemma interval_generator (h : IntervalParametrization) :
    ∃ g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} 1) 1,
      ∀ m : M, g m = classOf R (ordinary R M (referenceDiskPair.{w} 1)) 1
        (relativeSimplexChain R M (referenceDiskPair.{w} 1) 1 h.simplex m)
        (relativePath_cycle R M (referenceDiskPair.{w} 1) h.simplex (h.endpoint 0)
          (h.endpoint 1) (interval_face h 0) (interval_face h 1) m) := by
  obtain ⟨hz, e, he⟩ := P202.SpheresDisks.simplexGenerator R (ULift.{w} M) 1
  let H := (HomologicalComplex.homologyFunctor _ _ (1 : ℤ)).mapIso
    (intervalRelativeTransport R M h)
  refine ⟨(ULift.moduleEquiv : ULift.{w} M ≃ₗ[R] M).symm.trans
    (e.symm.trans H.toLinearEquiv), ?_⟩
  intro m
  have hm : e.symm (ULift.up m) =
      classOf R (ordinary R (ULift.{w} M) (simplexPair 1)) 1
        (relativeAffineChain R (ULift.{w} M) 1 (ULift.up m)) (hz (ULift.up m)) := by
    apply e.injective
    exact (e.apply_symm_apply (ULift.up m)).trans (he (ULift.up m)).symm
  change H.hom (e.symm (ULift.up m)) = _
  rw [hm]
  exact (homologyMap_classOf R (intervalRelativeTransport R M h).hom 1
    (relativeAffineChain R (ULift.{w} M) 1 (ULift.up m)) (hz (ULift.up m))
    (by
      rw [intervalRelativeTransport_affine]
      exact relativePath_cycle R M (referenceDiskPair.{w} 1) h.simplex (h.endpoint 0)
        (h.endpoint 1) (interval_face h 0) (interval_face h 1) m)).trans
      (by congr 1; exact intervalRelativeTransport_affine R M h m)

/-- Ordered boundary-preserving interval parametrizations exist. -/
lemma intervalParametrization_nonempty : Nonempty IntervalParametrization := by
  obtain ⟨e, he⟩ := P202.Topology.diskSimplexParametrization 1
  refine ⟨⟨e.symm, fun x => ?_⟩⟩
  have hx : ‖(e.symm x).val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (e.symm x).property
  have hi := he (e.symm x)
  rw [e.apply_symm_apply] at hi
  change x ∈ (simplexPair 1).subspace ↔ _
  rw [P202.SpheresDisks.simplex_boundary_iff, hi]
  exact ⟨fun h => le_antisymm hx (not_lt.mp h), fun h => by simp [h]⟩

end Endpoints

/-- Positive vertex coordinates compute every skeletal interval boundary. -/
theorem intervalBoundary :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    ∃ e : chainGroup X R M 0 ≃ₗ[R] (Cell X 0 →₀ M),
      (∀ (c : Cell X 0) (m : M),
        e (relativePointClass R M (skeletalPair X 0)
          (diskToSkeleton X CWStructure.boundary_lands 0 c ⟨0, by simp⟩) m) =
            Finsupp.single c m) ∧
      ∀ (s : Simplex (skeletalPair X 1).space 1) (a b : (skeletalPair X 1).sub),
        face 0 s = (TopCat.toSSet.map (skeletalPair X 1).inclusion).app
          (Opposite.op ⦋0⦌) (pointSimplex (skeletalPair X 1).sub a) →
        face 1 s = (TopCat.toSSet.map (skeletalPair X 1).inclusion).app
          (Opposite.op ⦋0⦌) (pointSimplex (skeletalPair X 1).sub b) →
        ∃ (vfinal vinitial : Cell X 0),
          lowerHomeomorph X 1 a =
            diskToSkeleton X CWStructure.boundary_lands 0 vfinal ⟨0, by simp⟩ ∧
          lowerHomeomorph X 1 b =
            diskToSkeleton X CWStructure.boundary_lands 0 vinitial ⟨0, by simp⟩ ∧
          ∃ hz : ∀ m : M, (ordinary R M (skeletalPair X 1)).d 1 0
              (relativeSimplexChain R M (skeletalPair X 1) 1 s m) = 0,
            ∀ m : M,
              e (differential X R M 0
                (P202Specs.SpheresDisks.classOf R (ordinary R M (skeletalPair X 1)) 1
                  (relativeSimplexChain R M (skeletalPair X 1) 1 s m) (hz m))) =
                Finsupp.single vfinal m - Finsupp.single vinitial m
 := by
  intro X _ _ R _ M _ _
  refine ⟨positiveVertexEquiv R M X, ?_, ?_⟩
  · intro c m
    rw [positiveVertexEquiv_point]
    change Finsupp.single ((P202.Homology.vertexEquiv X).symm
      (P202.Homology.vertexEquiv X c)) m = _
    rw [Equiv.symm_apply_apply]
  · intro s a b ha hb
    refine ⟨(P202.Homology.vertexEquiv X).symm (lowerHomeomorph X 1 a),
      (P202.Homology.vertexEquiv X).symm (lowerHomeomorph X 1 b), ?_, ?_,
      relativePath_cycle R M (skeletalPair X 1) s a b ha hb, ?_⟩
    · exact ((P202.Homology.vertexEquiv X).apply_symm_apply _).symm
    · exact ((P202.Homology.vertexEquiv X).apply_symm_apply _).symm
    · intro m
      exact path_boundary_coordinates R M X s a b ha hb m

/-- Oriented characteristic intervals are genuine relative generators, and their
cellular boundaries have the signed incidences of their two endpoints. -/
theorem intervalCellBoundary :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (h : IntervalParametrization),
    ∃ (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} 1) 1)
      (e : chainGroup X R M 0 ≃ₗ[R] (Cell X 0 →₀ M))
      (hz : ∀ m : M, (ordinary R M (referenceDiskPair.{w} 1)).d 1 0
        (relativeSimplexChain R M (referenceDiskPair.{w} 1) 1 h.simplex m) = 0),
      (∀ (c : Cell X 0) (m : M),
        e (relativePointClass R M (skeletalPair X 0)
          (diskToSkeleton X CWStructure.boundary_lands 0 c ⟨0, by simp⟩) m) =
            Finsupp.single c m) ∧
      (∀ m : M, g m = P202Specs.SpheresDisks.classOf R
        (ordinary R M (referenceDiskPair.{w} 1)) 1
        (relativeSimplexChain R M (referenceDiskPair.{w} 1) 1 h.simplex m) (hz m)) ∧
      ∀ c : Cell X 1, ∃ vfinal vinitial : Cell X 0,
        attachingBoundary X 0 c (h.endpoint 0) =
          diskToSkeleton X CWStructure.boundary_lands 0 vfinal ⟨0, by simp⟩ ∧
        attachingBoundary X 0 c (h.endpoint 1) =
          diskToSkeleton X CWStructure.boundary_lands 0 vinitial ⟨0, by simp⟩ ∧
        ∀ m : M, e (differential X R M 0 (cellClass X R M 1 c (g m))) =
          Finsupp.single vfinal m - Finsupp.single vinitial m
 := by
  intro X _ _ R _ M _ _ h
  obtain ⟨g, hg⟩ := interval_generator R M h
  refine ⟨g, positiveVertexEquiv R M X,
    relativePath_cycle R M (referenceDiskPair.{w} 1) h.simplex (h.endpoint 0)
      (h.endpoint 1) (interval_face h 0) (interval_face h 1), ?_, hg, ?_⟩
  · intro c m
    rw [positiveVertexEquiv_point]
    change Finsupp.single ((P202.Homology.vertexEquiv X).symm
      (P202.Homology.vertexEquiv X c)) m = _
    rw [Equiv.symm_apply_apply]
  · intro c
    refine ⟨(P202.Homology.vertexEquiv X).symm (attachingBoundary X 0 c (h.endpoint 0)),
      (P202.Homology.vertexEquiv X).symm (attachingBoundary X 0 c (h.endpoint 1)), ?_, ?_, ?_⟩
    · exact ((P202.Homology.vertexEquiv X).apply_symm_apply _).symm
    · exact ((P202.Homology.vertexEquiv X).apply_symm_apply _).symm
    · intro m
      rw [hg]
      exact cell_path_boundary R M X c h.simplex (h.endpoint 0) (h.endpoint 1)
        (interval_face h 0) (interval_face h 1) m

end P202.Homology.CellularDegrees

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace P202.Homology.CellularDegrees.CoefficientAction

lemma single_homology_ext {C : Type u} [Category.{v} C] [Abelian C]
    (n : ℕ) (A : C)
    (f g : (single C (.down ℕ) n).obj A ⟶ (single C (.down ℕ) n).obj A)
    (h : homologyMap f n = homologyMap g n) : f = g := by
  apply from_single_hom_ext
  let S := (single C (.down ℕ) n).obj A
  haveI : IsIso (S.iCycles n) := S.isIso_iCycles n _ rfl (by simp [S])
  haveI : IsIso (S.homologyπ n) := S.isIso_homologyπ _ n rfl (by simp [S])
  apply (cancel_epi (S.iCycles n)).mp
  rw [← cyclesMap_i, ← cyclesMap_i]
  congr 1
  apply (cancel_mono (S.homologyπ n)).mp
  rw [← homologyπ_naturality, ← homologyπ_naturality, h]

lemma homotopy_of_single_equiv {C : Type u} [Category.{v} C] [Abelian C]
    (K : ChainComplex C ℕ) (n : ℕ) (A : C)
    (e : HomotopyEquiv ((single C (.down ℕ) n).obj A) K)
    (f g : K ⟶ K) (h : homologyMap f n = homologyMap g n) :
    Nonempty (Homotopy f g) := by
  have hc : e.hom ≫ f ≫ e.inv = e.hom ≫ g ≫ e.inv := by
    apply single_homology_ext n A
    simp only [homologyMap_comp, h]
  let hf := (e.homotopyInvHomId.compRightId f).symm
  refine ⟨hf.trans ?_⟩
  have hh : Homotopy ((e.inv ≫ e.hom) ≫ f)
      (e.inv ≫ (e.hom ≫ f ≫ e.inv) ≫ e.hom) := by
    simpa only [Category.assoc] using
      ((e.homotopyInvHomId.compLeftId (e.hom ≫ f)).symm.compLeft e.inv)
  refine hh.trans ?_
  rw [hc]
  have hh' : Homotopy (e.inv ≫ (e.hom ≫ g ≫ e.inv) ≫ e.hom)
      ((e.inv ≫ e.hom) ≫ g) := by
    simpa only [Category.assoc] using
      ((e.homotopyInvHomId.compLeftId (e.hom ≫ g)).compLeft e.inv)
  exact hh'.trans (e.homotopyInvHomId.compRightId g)

lemma additive_transfer_scalar_action {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type*} [Category* D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) (n : ℕ) (A : C)
    (e : HomotopyEquiv ((single C (.down ℕ) n).obj A) K)
    (f : K ⟶ K) (d : ℤ)
    (h : homologyMap f n = d • 𝟙 (K.homology n)) :
    homologyMap ((F.mapHomologicalComplex (.down ℕ)).map f) n =
      d • 𝟙 (((F.mapHomologicalComplex (.down ℕ)).obj K).homology n) := by
  have hs : homologyMap (d • 𝟙 K) n = d • 𝟙 (K.homology n) := by
    change (homologyFunctor C (.down ℕ) n).map (d • 𝟙 K) = _
    rw [(homologyFunctor C (.down ℕ) n).map_zsmul,
      (homologyFunctor C (.down ℕ) n).map_id]
    rfl
  obtain ⟨ho⟩ := homotopy_of_single_equiv K n A e f (d • 𝟙 K) (h.trans hs.symm)
  have hm := (F.mapHomotopy ho).homologyMap_eq n
  rw [(F.mapHomologicalComplex (.down ℕ)).map_zsmul,
    (F.mapHomologicalComplex (.down ℕ)).map_id] at hm
  change homologyMap _ n = (homologyFunctor D (.down ℕ) n).map (d • 𝟙 _) at hm
  simpa only [(homologyFunctor D (.down ℕ) n).map_zsmul,
    (homologyFunctor D (.down ℕ) n).map_id, homologyFunctor_obj] using hm

open P202Specs.SingularChains P202Specs.SpheresDisks
open P202.SpheresDisks P202.SpheresDisks.IntegralCoefficients

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

lemma integralTensorAugmentedIso_natural {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).map
      (augmentedShiftedMap ℤ ℤ f) ≫ (integralTensorAugmentedIso R M Y).hom =
    (integralTensorAugmentedIso R M X).hom ≫ augmentedShiftedMap R M f := by
  apply HomologicalComplex.Hom.ext
  funext k
  cases k with
  | zero => simp [integralTensorAugmentedIso, integralTensorAugmentedComponent,
      augmentedShiftedMap]
  | succ n =>
    change ((integralTensorFunctor R M).map ((chainMap ℤ ℤ f).f n)) ≫
        (integralTensorChainsEquiv R M Y n).toModuleIso.hom =
      (integralTensorChainsEquiv R M X n).toModuleIso.hom ≫ (chainMap R M f).f n
    have h := congrArg (fun g => g.f n)
      (P202.Homology.Coefficients.tensorComplexIso_natural R M f)
    exact h

lemma integral_augmented_sphere_action (n : ℕ) (f : sphere n ⟶ sphere n) :
    homologyMap (augmentedShiftedMap ℤ ℤ f) (n+1) =
      P202Specs.Degree.degree n f • 𝟙 ((augmentedShifted ℤ ℤ (sphere n)).homology (n+1)) := by
  let K := augmentedShifted ℤ ℤ (sphere n)
  let e : P202Specs.Degree.sphereGroup n ≅ K.homology (n+1) :=
    K.extendHomologyIso (degreeEmbedding (-1))
      (j := n+1) (by change (-1 : ℤ) + (n+1 : ℕ) = (n : ℤ); omega)
  have hd : P202Specs.Degree.induced n f =
      P202Specs.Degree.degree n f • 𝟙 (P202Specs.Degree.sphereGroup n) := by
    apply ModuleCat.hom_ext
    ext x
    exact P202.Degree.action n f x
  apply (cancel_epi e.hom).mp
  have hn := extendHomologyIso_hom_naturality
    (augmentedShiftedMap ℤ ℤ f) (degreeEmbedding (-1))
    (show (degreeEmbedding (-1)).f (n+1) = (n : ℤ) by
      change (-1 : ℤ) + (n+1 : ℕ) = (n : ℤ); omega)
  change P202Specs.Degree.induced n f ≫ e.hom =
    e.hom ≫ homologyMap (augmentedShiftedMap ℤ ℤ f) (n+1) at hn
  rw [← hn, hd]
  simp only [Preadditive.zsmul_comp, Category.id_comp,
    Preadditive.comp_zsmul, Category.comp_id]
  rfl

lemma tensor_augmented_sphere_action (n : ℕ) (f : sphere n ⟶ sphere n) :
    homologyMap (((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).map
      (augmentedShiftedMap ℤ ℤ f)) (n+1) =
    P202Specs.Degree.degree n f •
      𝟙 ((((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).obj
        (augmentedShifted ℤ ℤ (sphere n))).homology (n+1)) := by
  let K := augmentedShifted ℤ ℤ (sphere n)
  have : ∀ k, Projective (K.X k) := fun k => sphere_augmented_projective ℤ n k
  obtain ⟨g⟩ := (sphere_augmented_homology ℤ n (n+1)).1 rfl
  have : Projective (K.homology (n+1)) := Projective.of_iso g.toModuleIso.symm inferInstance
  let e := ConcentratedHomology.singleHomologyHomotopyEquiv K (n+1)
    (fun k hk => (sphere_augmented_homology ℤ n k).2 hk)
  exact additive_transfer_scalar_action
    (integralTensorFunctor R M) K (n+1) (K.homology (n+1)) e
    (augmentedShiftedMap ℤ ℤ f) (P202Specs.Degree.degree n f)
    (integral_augmented_sphere_action n f)

lemma augmented_sphere_action (n : ℕ) (f : sphere n ⟶ sphere n) :
    homologyMap (augmentedShiftedMap R M f) (n+1) =
      P202Specs.Degree.degree n f • 𝟙 ((augmentedShifted R M (sphere n)).homology (n+1)) := by
  let e := (homologyFunctor (ModuleCat.{v} R) (.down ℕ) (n+1)).mapIso
    (integralTensorAugmentedIso R M (sphere n))
  apply (cancel_epi e.hom).mp
  have hn := congrArg (fun g => homologyMap g (n+1))
    (integralTensorAugmentedIso_natural R M f)
  simp only [homologyMap_comp] at hn
  change _ ≫ e.hom = e.hom ≫ homologyMap (augmentedShiftedMap R M f) (n+1) at hn
  rw [← hn, tensor_augmented_sphere_action]
  simp only [Preadditive.zsmul_comp, Category.id_comp,
    Preadditive.comp_zsmul, Category.comp_id]
  rfl

theorem sphere_action (n : ℕ) (f : sphere n ⟶ sphere n)
    (x : reducedHomology R M (sphere n) (n : ℤ)) :
    (reducedHomologyFunctor R M (n : ℤ)).map f x = P202Specs.Degree.degree n f • x := by
  let K := augmentedShifted R M (sphere n)
  let e : reducedHomology R M (sphere n) (n : ℤ) ≅ K.homology (n+1) :=
    K.extendHomologyIso (degreeEmbedding (-1))
      (j := n+1) (by change (-1 : ℤ) + (n+1 : ℕ) = (n : ℤ); omega)
  apply e.toLinearEquiv.injective
  have hn := extendHomologyIso_hom_naturality
    (augmentedShiftedMap R M f) (degreeEmbedding (-1))
    (show (degreeEmbedding (-1)).f (n+1) = (n : ℤ) by
      change (-1 : ℤ) + (n+1 : ℕ) = (n : ℤ); omega)
  have hx := congrArg (fun g => g x) hn
  change e.hom ((reducedHomologyFunctor R M (n : ℤ)).map f x) =
    homologyMap (augmentedShiftedMap R M f) (n+1) (e.hom x) at hx
  rw [augmented_sphere_action] at hx
  simpa using hx

end P202.Homology.CellularDegrees.CoefficientAction

noncomputable section
open CategoryTheory Topology HomologicalComplex
open scoped OnePoint
open P202.Cellular P202Specs.SpheresDisks P202Specs.GoodPairQuotient
namespace P202.Homology.CellularDegrees.Geometry

/-- Collapse the boundary of the disk to infinity. -/
def diskToOnePoint (n : ℕ) (x : Disk n) : OnePoint (OpenDisk n) :=
  if h : ‖x.val‖ < 1 then (⟨x.val, by simpa only [Metric.mem_ball, dist_zero_right] using h⟩ : OpenDisk n) else ∞

lemma diskToOnePoint_interior (n : ℕ) (x : OpenDisk n) :
    diskToOnePoint n (interiorInclusion n x) = (x : OnePoint (OpenDisk n)) := by
  have h : ‖x.val‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using x.property
  simp [diskToOnePoint, interiorInclusion, h]

lemma diskToOnePoint_boundary (n : ℕ) (x : Sphere n) :
    diskToOnePoint n (boundaryInclusion n x) = ∞ := by
  have h : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  simp [diskToOnePoint, boundaryInclusion, h]

lemma diskToOnePoint_continuous (n : ℕ) : Continuous (diskToOnePoint n) := by
  classical
  apply continuous_def.mpr
  intro s hs
  by_cases hinf : (∞ : OnePoint (OpenDisk n)) ∈ s
  · have hk := ((OnePoint.isOpen_iff_of_mem hinf).mp hs).2
    have hc : IsClosed ((interiorInclusion n) '' (((↑) : OpenDisk n → OnePoint (OpenDisk n)) ⁻¹' s)ᶜ) :=
      (hk.image (continuous_subtype_val.subtype_mk _)).isClosed
    have he : (diskToOnePoint n ⁻¹' s) =
        ((interiorInclusion n) '' (((↑) : OpenDisk n → OnePoint (OpenDisk n)) ⁻¹' s)ᶜ)ᶜ := by
      ext x
      by_cases hx : ‖x.val‖ < 1
      · let y : OpenDisk n := ⟨x.val, by simpa only [Metric.mem_ball, dist_zero_right] using hx⟩
        have hxy : interiorInclusion n y = x := Subtype.ext rfl
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_image]
        constructor
        · intro h ⟨z, hz, hzx⟩
          have hzx' : z = y := Subtype.ext (congrArg (fun p : Disk n => p.val) hzx)
          subst z
          exact hz (by simpa [diskToOnePoint, hx, y] using h)
        · intro h
          by_contra h'
          apply h
          exact ⟨y, by simpa [diskToOnePoint, hx, y] using h', hxy⟩
      · simp only [Set.mem_preimage, diskToOnePoint, dif_neg hx, hinf, Set.mem_compl_iff,
          true_iff, Set.mem_image, not_exists, not_and]
        intro y _ hy
        have hy' : ‖x.val‖ < 1 := by
          rw [← hy]
          simpa only [interiorInclusion, Metric.mem_ball, dist_zero_right] using y.property
        exact hx hy'
    rw [he]
    exact hc.isOpen_compl
  · have ho := (OnePoint.isOpen_iff_of_notMem hinf).mp hs
    have hi : IsOpenMap (interiorInclusion n) := by
      have he : interiorInclusion n = fun x : OpenDisk n =>
          (⟨x.val, Metric.ball_subset_closedBall x.property⟩ : Disk n) := rfl
      exact (Metric.isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1)).isOpenEmbedding_subtypeVal.isOpenMap.codRestrict _
    have he : diskToOnePoint n ⁻¹' s =
        (interiorInclusion n) '' (((↑) : OpenDisk n → OnePoint (OpenDisk n)) ⁻¹' s) := by
      ext x
      constructor
      · intro hx
        have hxlt : ‖x.val‖ < 1 := by
          by_contra h
          exact hinf (by simpa [diskToOnePoint, h] using hx)
        exact ⟨⟨x.val, by simpa only [Metric.mem_ball, dist_zero_right] using hxlt⟩, by simpa [diskToOnePoint, hxlt] using hx,
          Subtype.ext rfl⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [diskToOnePoint_interior] using hy
    rw [he]
    exact hi _ ho

lemma diskToOnePoint_respects (n : ℕ) (x y : Disk n)
    (h : (collapseSetoid (diskPair n)).r x y) :
    diskToOnePoint n x = diskToOnePoint n y := by
  rcases h with rfl | ⟨hx, hy⟩
  · rfl
  · change ‖x.val‖ = 1 at hx
    change ‖y.val‖ = 1 at hy
    simp [diskToOnePoint, hx, hy]

def quotientToOnePoint (n : ℕ) : quotientSpace (diskPair n) → OnePoint (OpenDisk n) :=
  Quotient.lift (diskToOnePoint n) (diskToOnePoint_respects n)

lemma quotientToOnePoint_continuous (n : ℕ) : Continuous (quotientToOnePoint n) :=
  continuous_quot_lift _ (diskToOnePoint_continuous n)

lemma quotientToOnePoint_bijective (n : ℕ) (b : Sphere n) :
    Function.Bijective (quotientToOnePoint n) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | h x =>
      induction b using Quotient.inductionOn with | h y =>
        change diskToOnePoint n x = diskToOnePoint n y → _
        intro h
        apply Quotient.sound
        by_cases hx : ‖x.val‖ < 1
        · have hy : ‖y.val‖ < 1 := by
            by_contra hy
            simp [diskToOnePoint, hx, hy] at h
          have hxy : x.val = y.val := by
            have hh := congrArg
              (fun p : OnePoint (OpenDisk n) => Option.map Subtype.val p) h
            simp only [diskToOnePoint, dite_eq_left hx, dite_eq_left hy] at hh
            exact Option.some.inj hh
          exact Or.inl (Subtype.ext hxy)
        · have hy : ¬ ‖y.val‖ < 1 := by
            intro hy
            simp [diskToOnePoint, hx, hy] at h
          exact Or.inr ⟨le_antisymm (by simpa only [Metric.mem_closedBall, dist_zero_right]
            using x.property) (le_of_not_gt hx),
            le_antisymm (by simpa only [Metric.mem_closedBall, dist_zero_right]
            using y.property) (le_of_not_gt hy)⟩
  · intro p
    induction p using OnePoint.rec with
    | infty =>
      exact ⟨quotientProjection (diskPair n) (boundaryInclusion n b),
        diskToOnePoint_boundary n b⟩
    | coe p =>
      exact ⟨quotientProjection (diskPair n) (interiorInclusion n p),
        diskToOnePoint_interior n p⟩

def diskQuotientOnePointHomeomorph (n : ℕ) (b : Sphere n) :
    quotientSpace (diskPair n) ≃ₜ OnePoint (OpenDisk n) :=
  letI : CompactSpace (diskPair n).space := by change CompactSpace (Disk n); infer_instance
  letI : LocallyCompactSpace (OpenDisk n) := Metric.isOpen_ball.locallyCompactSpace
  letI : CompactSpace (quotientSpace (diskPair n)) :=
    (isQuotientMap_quotient_mk' (s := collapseSetoid (diskPair n))).surjective.compactSpace continuous_quotient_mk'
  let e := Equiv.ofBijective (quotientToOnePoint n) (quotientToOnePoint_bijective n b)
  have he : Continuous e := quotientToOnePoint_continuous n
  he.homeoOfEquivCompactToT2

def diskQuotientSphereHomeomorph (n : ℕ) (b : Sphere n) :
    quotientSpace (diskPair n) ≃ₜ sphere n :=
  (diskQuotientOnePointHomeomorph n b).trans
    ((Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin n))).symm.onePointCongr.trans
      (onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin n))
        (ι := Fin (n+1)) (by simp)))

open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202.Homology.CellLocalization P202.Topology.Collar

/-- The standard disk pair is a genuine good pair, with its radial outer collar. -/
def diskGoodPairData (n : ℕ) (b : Sphere n) : Data where
  pair := diskPair n
  nonempty := ⟨boundaryInclusion n b, by
    change ‖b.val‖ = 1
    simpa only [Metric.mem_sphere, dist_zero_right] using b.property⟩
  closed := isClosed_eq continuous_subtype_val.norm continuous_const
  neighborhood := {x | 1/2 < ‖x.val‖}
  open_neighborhood := isOpen_lt continuous_const continuous_subtype_val.norm
  subset_neighborhood := by
    intro x hx
    change ‖x.val‖ = 1 at hx
    change 1/2 < ‖x.val‖
    rw [hx]
    norm_num
  deformation := (outerDiskDeformation n).comp ⟨Prod.swap, continuous_swap⟩
  at_zero := outerDiskDeformation_zero n
  at_one := outerDiskDeformation_one n
  fixes := by
    intro t x hx
    exact outerDiskDeformation_fixed n x t hx


def referenceDiskQuotientHomeomorph (n : ℕ) :
    quotientSpace (referenceDiskPair.{w} n) ≃ₜ quotientSpace (diskPair n) :=
  Homeomorph.Quotient.congr (referenceDiskHomeomorph n) (by
    intro x y
    change (x = y ∨ (‖x.down.val‖ = 1 ∧ ‖y.down.val‖ = 1)) ↔
      (x.down = y.down ∨ (‖x.down.val‖ = 1 ∧ ‖y.down.val‖ = 1))
    exact or_congr (ULift.down_injective.eq_iff.symm) Iff.rfl)

def referenceDiskQuotientSphereHomeomorph (n : ℕ) (b : Sphere n) :
    quotientSpace (referenceDiskPair.{w} n) ≃ₜ ULift.{w} (sphere n) :=
  ((referenceDiskQuotientHomeomorph n).trans (diskQuotientSphereHomeomorph n b)).trans
    Homeomorph.ulift.symm

def referenceOuterDiskHomeomorph (n : ℕ) :
    {x : (referenceDiskPair.{w} n).space // 1/2 < ‖x.down.val‖} ≃ₜ OuterDisk n where
  toFun x := ⟨x.val.down, x.property⟩
  invFun x := ⟨ULift.up x.val, x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by
    change Continuous (fun x : {x : ULift.{w} (Disk n) // 1/2 < ‖x.down.val‖} =>
      (⟨x.val.down, x.property⟩ : OuterDisk n))
    exact (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    change Continuous (fun x : OuterDisk n =>
      (⟨ULift.up x.val, x.property⟩ : {x : ULift.{w} (Disk n) // 1/2 < ‖x.down.val‖}))
    exact (continuous_uliftUp.comp continuous_subtype_val).subtype_mk _

def referenceOuterDiskDeformation (n : ℕ) :
    C(unitInterval × {x : ULift.{w} (Disk n) // 1/2 < ‖x.down.val‖},
      {x : ULift.{w} (Disk n) // 1/2 < ‖x.down.val‖}) :=
  let e := referenceOuterDiskHomeomorph n
  ⟨fun p => e.symm (outerDiskDeformation n (e p.2, p.1)),
    e.symm.continuous.comp ((outerDiskDeformation n).continuous.comp
      ((e.continuous.comp continuous_snd).prodMk continuous_fst))⟩

def referenceDiskGoodPairData (n : ℕ) (b : Sphere n) : Data.{w} where
  pair := referenceDiskPair n
  nonempty := ⟨ULift.up (boundaryInclusion n b), by
    change ‖b.val‖ = 1
    simpa only [Metric.mem_sphere, dist_zero_right] using b.property⟩
  closed := isClosed_eq (continuous_subtype_val.comp continuous_uliftDown).norm continuous_const
  neighborhood := {x | 1/2 < ‖x.down.val‖}
  open_neighborhood := isOpen_lt continuous_const
    (continuous_subtype_val.comp continuous_uliftDown).norm
  subset_neighborhood := by
    intro x hx
    change ‖x.down.val‖ = 1 at hx
    change 1/2 < ‖x.down.val‖
    rw [hx]
    norm_num
  deformation := referenceOuterDiskDeformation n
  at_zero := by
    intro x
    apply (referenceOuterDiskHomeomorph n).injective
    exact outerDiskDeformation_zero n _
  at_one := by
    intro x
    exact outerDiskDeformation_one n _
  fixes := by
    intro t x hx
    apply (referenceOuterDiskHomeomorph n).injective
    exact outerDiskDeformation_fixed n _ t hx

theorem referenceDiskQuotientHomology (n : ℕ) (b : Sphere n) :
    ∃ c : reduced ℤ ℤ (referenceDiskPair.{w} n) ≅ ordinary ℤ ℤ (referenceDiskPair.{w} n),
      IsRelativeComparison ℤ (referenceDiskPair.{w} n) c ∧
      ∀ j : ℕ,
        IsIso (homologyMap (projection (reducedFunctor ℤ ℤ)
          (quotientPair (referenceDiskPair.{w} n))) (j : ℤ)) ∧
        ∃ e : relativeHomology ℤ ℤ (referenceDiskPair.{w} n) (j : ℤ) ≅
            reducedHomology ℤ ℤ (quotientSpace (referenceDiskPair.{w} n)) (j : ℤ),
          homologyMap c.hom (j : ℤ) ≫ e.hom ≫
            homologyMap (projection (reducedFunctor ℤ ℤ)
              (quotientPair (referenceDiskPair.{w} n))) (j : ℤ) =
          homologyMap (relativeMap (reducedFunctor ℤ ℤ)
            (quotientPairMap (referenceDiskPair.{w} n))) (j : ℤ) :=
  P202.GoodPairQuotient.isomorphism ℤ (referenceDiskGoodPairData n b)

end P202.Homology.CellularDegrees.Geometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Topology
namespace P202.Homology.CellularDegrees
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.CellularDegrees

/-- A map whose whole image lies in the target subspace is zero on relative chains. -/
lemma relativeMap_zero_of_range_in_subspace
    {P Q : Pair.{w}} (f : P ⟶ Q)
    (h : ∀ x : P.space, f.map x ∈ Q.subspace)
    {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} {shape : ComplexShape ι}
    (K : TopCat.{w} ⥤ HomologicalComplex C shape) :
    relativeMap K f = 0 := by
  let g : P.space ⟶ Q.sub := TopCat.ofHom
    ⟨fun x => ⟨f.map x, h x⟩, f.map.hom.continuous.subtype_mk _⟩
  have hg : g ≫ Q.inclusion = f.map := rfl
  apply (cancel_epi (projection K P)).mp
  rw [projection_map, comp_zero, ← hg, K.map_comp, Category.assoc]
  change K.map g ≫ inclusion K Q ≫ cokernel.π (inclusion K Q) = 0
  simp

variable (X : Type w) [TopologicalSpace X] [CWStructure X]

open Classical in
/-- The geometric selected-cell collapse, with the universe lift needed by
maps of genuine skeletal pairs. -/
lemma liftedCellCollapse (n : ℕ) (c : Cell X n) (b : (referenceDiskPair.{w} n).sub) :
    ∃ q : skeletalPair X n ⟶ P202Specs.GoodPairQuotient.quotientPair (referenceDiskPair.{w} n),
      IsQuotientMap q.map ∧
      ∀ (d : Cell X n) (x : (referenceDiskPair.{w} n).space),
        q.map ((characteristicPairMap n d).map x) =
          if d = c then P202Specs.GoodPairQuotient.quotientProjection (referenceDiskPair.{w} n) x
          else P202Specs.GoodPairQuotient.quotientProjection (referenceDiskPair.{w} n) b.val := by
  classical
  let P := referenceDiskPair.{w} n
  let Q := P202Specs.GoodPairQuotient.quotientSpace P
  let π := P202Specs.GoodPairQuotient.quotientProjection P
  let p : Q := π b.val
  have hb (z : Sphere n) : π ⟨boundaryInclusion n z⟩ = p := by
    apply Quotient.sound
    apply Or.inr
    constructor
    · change ‖z.val‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using z.property
    · exact b.property
  let f : C(skeletonLT X n, Q) := ContinuousMap.const _ p
  let diskProjection : C(Disk n, Q) :=
    ⟨fun x => π ⟨x⟩, π.hom.continuous.comp continuous_uliftUp⟩
  let g : ∀ _d : Cell X n, C(Disk n, Q) :=
    fun d => if d = c then diskProjection else ContinuousMap.const _ p
  have hcompat (d : Cell X n) (z : Sphere n) :
      g d (boundaryInclusion n z) = f (attachingMap n d z) := by
    by_cases h : d = c
    · simpa [g, f, h, diskProjection] using hb z
    · simp [g, f, h]
  obtain ⟨q, ⟨hqold, hqcell⟩, _⟩ := P202.Topology.attachmentPushout n f g hcompat
  let qpair : skeletalPair X n ⟶ P202Specs.GoodPairQuotient.quotientPair P :=
    ⟨TopCat.ofHom q, fun x hx => by
      refine ⟨b.val, b.property, ?_⟩
      exact (hqold ⟨x.val, hx⟩).symm⟩
  refine ⟨qpair, ?_, ?_⟩
  · have hcomp : (fun x : P.space => q ((characteristicPairMap n c).map x)) = π := by
      funext x
      change q (diskToSkeleton X CWStructure.boundary_lands n c x.down) = π x
      have hh := hqcell c x.down
      have hxx : (ULift.up x.down : P.space) = x := by cases x; rfl
      simpa only [g, ite_eq_left rfl, diskProjection, ContinuousMap.coe_mk, hxx] using hh
    apply IsQuotientMap.of_comp
      (characteristicPairMap n c).map.hom.continuous q.continuous
    change IsQuotientMap (fun x : P.space => q ((characteristicPairMap n c).map x))
    rw [hcomp]
    exact isQuotientMap_quotient_mk'
  · intro d x
    change q (diskToSkeleton X CWStructure.boundary_lands n d x.down) = _
    by_cases h : d = c
    · have hxx : (ULift.up x.down : P.space) = x := by cases x; rfl
      simpa only [qpair, g, ite_eq_left h, diskProjection, ContinuousMap.coe_mk, hxx] using hqcell d x.down
    · simpa [qpair, g, h] using hqcell d x.down

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

open Classical in
lemma collapseCoordinate (n : ℕ) (c : Cell X n)
    (b : (referenceDiskPair.{w} n).sub)
    (q : skeletalPair X n ⟶ P202Specs.GoodPairQuotient.quotientPair (referenceDiskPair.{w} n))
    (hq : ∀ (d : Cell X n) (x : (referenceDiskPair.{w} n).space),
        q.map ((characteristicPairMap n d).map x) =
          if d = c then P202Specs.GoodPairQuotient.quotientProjection (referenceDiskPair.{w} n) x
          else P202Specs.GoodPairQuotient.quotientProjection (referenceDiskPair.{w} n) b.val)
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : CharacteristicCoordinates X R M n g e)
    (z : chainGroup X R M n) :
    (relativeHomologyFunctor R M (n : ℤ)).map q z =
      (relativeHomologyFunctor R M (n : ℤ)).map
        (P202Specs.GoodPairQuotient.quotientPairMap (referenceDiskPair.{w} n)) (g (e z c)) := by
  classical
  let F := relativeHomologyFunctor R M (n : ℤ)
  have hmaps : (F.map q).hom.comp e.symm.toLinearMap =
      ((F.map (P202Specs.GoodPairQuotient.quotientPairMap (referenceDiskPair.{w} n))).hom.comp
        g.toLinearMap).comp (Finsupp.lapply c) := by
    apply Finsupp.lhom_ext
    intro d m
    have hsingle : e.symm (Finsupp.single d m) = cellClass X R M n d (g m) := by
      apply e.injective
      rw [e.apply_symm_apply, he]
    change F.map q (e.symm (Finsupp.single d m)) =
      F.map (P202Specs.GoodPairQuotient.quotientPairMap (referenceDiskPair.{w} n))
        (g ((Finsupp.single d m) c))
    rw [hsingle]
    change F.map q (F.map (characteristicPairMap n d) (g m)) = _
    rw [← ModuleCat.comp_apply, ← Functor.map_comp]
    by_cases hd : d = c
    · subst d
      have hm : characteristicPairMap n c ≫ q =
          P202Specs.GoodPairQuotient.quotientPairMap (referenceDiskPair.{w} n) := by
        apply PairMap.ext
        apply TopCat.hom_ext
        ext x
        exact (hq c x).trans (ite_eq_left rfl)
      rw [hm]
      simp
    · have hz : relativeMap (ordinaryFunctor R M) (characteristicPairMap n d ≫ q) = 0 := by
        apply relativeMap_zero_of_range_in_subspace
        intro x
        refine ⟨b.val, b.property, ?_⟩
        exact ((hq d x).trans (ite_eq_right hd)).symm
      change homologyMap (relativeMap (ordinaryFunctor R M) (characteristicPairMap n d ≫ q))
        (n : ℤ) (g m) = _
      rw [hz, homologyMap_zero]
      simp [Finsupp.single_eq_of_ne (Ne.symm hd)]
  have hh := congrArg (fun f => f (e z)) hmaps
  change F.map q (e.symm (e z)) =
      F.map (P202Specs.GoodPairQuotient.quotientPairMap (referenceDiskPair.{w} n))
        (g (e z c)) at hh
  rw [e.symm_apply_apply] at hh
  exact hh

end P202.Homology.CellularDegrees

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.Homology.CellularDegrees.CoefficientAction
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.GoodPairQuotient

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

lemma goodPairQuotient_relative_nonnegative (D : Data.{w}) :
    QuasiIso (relativeMap (chainFunctor R M) (quotientPairMap D.pair)) := by
  haveI : QuasiIso (relativeMap (chainFunctor ℤ ℤ) (quotientPairMap D.pair)) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact P202.GoodPairQuotient.relative_quotient_isIso_conditional
      P202.Excision.isomorphism P202.Excision.naturality ℤ D n
  exact P202.Homology.Coefficients.relativeMap_quasiIso_of_integral R M _

lemma goodPairQuotient_relative (D : Data.{w}) (n : ℕ) :
    IsIso (homologyMap (relativeMap (ordinaryFunctor R M) (quotientPairMap D.pair))
      (n : ℤ)) := by
  haveI := goodPairQuotient_relative_nonnegative R M D
  exact (P202.Homology.CoefficientExtension.ordinaryRelativeHomologyMap_isIso_iff
    R M (quotientPairMap D.pair) n).mpr inferInstance

end P202.Homology.CellularDegrees.CoefficientAction

namespace P202.Homology.CellularDegrees
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.CellularDegrees

theorem sphereCoefficientAction : Expected.sphereCoefficientAction.{u,v} := by
  intro R _ M _ _ n f x
  exact CoefficientAction.sphere_action R M n f x

theorem diskQuotientSphere : Expected.diskQuotientSphere := by
  intro n b
  exact ⟨Geometry.diskQuotientSphereHomeomorph n b⟩

end P202.Homology.CellularDegrees

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.Homology.CellularDegrees.ConnectingBridge
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.SpheresDisks
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

lemma ordinary_contractible_positive (Y : TopCat.{w}) [Nonempty Y]
    [ContractibleSpace Y] (n : ℕ) (hn : 0 < n) :
    IsZero (homology R M Y (n : ℤ)) :=
  (P202.SingularDegreeZero.reducedPositiveIso R M Y n hn).isZero_iff.mp
    (P202.PrismHomotopy.contractible R M Y (n : ℤ))

lemma reference_disk_contractible (n : ℕ) :
    ContractibleSpace (referenceDiskPair.{w} n).space := by
  letI := P202.SpheresDisks.disk_contractible n
  exact (referenceDiskHomeomorph.{w} n).contractibleSpace

lemma reference_disk_nonempty (n : ℕ) : Nonempty (referenceDiskPair.{w} n).space :=
  ⟨ULift.up ⟨0, by simp⟩⟩

lemma pairConnecting_isIso_of_contractible (P : Pair.{w}) [Nonempty P.space]
    [ContractibleSpace P.space] (n : ℕ) (hn : 0 < n) :
    IsIso (pairConnecting R M P n) := by
  let h := P202.RelativeSingularChains.ordinary_short_exact R M P
  rw [pairConnecting_eq R M P n h]
  exact (HomologicalComplex.shortExact_of_degreewise_shortExact _ h).isIso_δ
    ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp)
    (ordinary_contractible_positive R M P.space (n+1) (by omega))
    (ordinary_contractible_positive R M P.space n hn)

lemma reference_pairConnecting_isIso (n : ℕ) (hn : 0 < n) :
    IsIso (pairConnecting R M (referenceDiskPair.{w} (n+1)) n) := by
  letI := reference_disk_nonempty.{w} (n+1)
  letI := reference_disk_contractible.{w} (n+1)
  exact pairConnecting_isIso_of_contractible R M _ n hn

def referenceDiskConnectingIso (n : ℕ) (hn : 0 < n) :
    relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ) ≅
      homology R M (referenceDiskPair.{w} (n+1)).sub (n : ℤ) := by
  letI := reference_pairConnecting_isIso R M n hn
  exact asIso (pairConnecting R M (referenceDiskPair.{w} (n+1)) n)

@[simp] lemma referenceDiskConnectingIso_hom (n : ℕ) (hn : 0 < n) :
    (referenceDiskConnectingIso R M n hn).hom =
      pairConnecting R M (referenceDiskPair.{w} (n+1)) n := rfl

def referenceBoundarySphereHomeomorph (n : ℕ) :
    (referenceDiskPair.{w} (n+1)).sub ≃ₜ ULift.{w} (sphere n) where
  toFun x := ULift.up ⟨x.val.down.val, by
    have hx : ‖x.val.down.val‖ = 1 := x.property
    simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  invFun x := ⟨ULift.up ⟨x.down.val, Metric.sphere_subset_closedBall x.down.property⟩, by
    change ‖x.down.val‖ = 1
    simpa only [Metric.mem_sphere, dist_zero_right] using x.down.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_uliftUp.comp
    ((continuous_subtype_val.comp (continuous_uliftDown.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun := ((continuous_uliftUp.comp
    ((continuous_subtype_val.comp continuous_uliftDown).subtype_mk _)).subtype_mk _)

abbrev liftedSphere (n : ℕ) : TopCat.{w} := TopCat.of (ULift.{w} (sphere n))

def referenceBoundaryReducedIso (n : ℕ) (hn : 0 < n) :
    homology R M (referenceDiskPair.{w} (n+1)).sub (n : ℤ) ≅
      reducedHomology R M (liftedSphere.{w} n) (n : ℤ) :=
  (P202.SingularDegreeZero.reducedPositiveIso R M
    (referenceDiskPair.{w} (n+1)).sub n hn).symm ≪≫
  (reducedHomologyFunctor R M (n : ℤ)).mapIso
    (TopCat.isoOfHomeo (referenceBoundarySphereHomeomorph.{w} n))

def referenceDiskBoundaryShift (n : ℕ) (hn : 0 < n) :
    relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ) ≅
      reducedHomology R M (liftedSphere.{w} n) (n : ℤ) :=
  referenceDiskConnectingIso R M n hn ≪≫ referenceBoundaryReducedIso R M n hn

lemma referenceDiskBoundaryShift_hom (n : ℕ) (hn : 0 < n) :
    (referenceDiskBoundaryShift R M n hn).hom =
      pairConnecting R M (referenceDiskPair.{w} (n+1)) n ≫
        (referenceBoundaryReducedIso R M n hn).hom := rfl

/-- The canonical projection from augmented to ordinary chains. -/
lemma singletonSubspace_inclusion_retraction (P : Pair.{w}) [Nonempty P.sub]
    [Subsingleton P.sub] : ∃ r : P.space ⟶ P.sub, P.inclusion ≫ r = 𝟙 P.sub := by
  refine ⟨TopCat.ofHom (ContinuousMap.const _ (Classical.choice (inferInstance : Nonempty P.sub))), ?_⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact Subsingleton.elim _ _

lemma singletonSubspace_homology_inclusion_mono (P : Pair.{w}) [Nonempty P.sub]
    [Subsingleton P.sub] (i : ℤ) :
    Mono (homologyMap ((ordinaryFunctor R M).map P.inclusion) i) := by
  obtain ⟨r, hr⟩ := singletonSubspace_inclusion_retraction P
  haveI : IsSplitMono ((homologyFunctor R M i).map P.inclusion) :=
    IsSplitMono.mk' ⟨(homologyFunctor R M i).map r, by
      rw [← CategoryTheory.Functor.map_comp, hr]
      exact (homologyFunctor R M i).map_id _⟩
  change Mono ((homologyFunctor R M i).map P.inclusion)
  infer_instance

lemma singletonSubspace_connecting_zero (P : Pair.{w}) [Nonempty P.sub]
    [Subsingleton P.sub] (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    P202Specs.ChainLES.connecting
      (P202.RelativeSingularChains.ordinary_short_exact R M P) i j hij = 0 := by
  let h := P202.RelativeSingularChains.ordinary_short_exact R M P
  let hs := HomologicalComplex.shortExact_of_degreewise_shortExact _ h
  letI := singletonSubspace_homology_inclusion_mono R M P j
  apply (cancel_mono (homologyMap ((ordinaryFunctor R M).map P.inclusion) j)).mp
  rw [zero_comp]
  exact hs.δ_comp i j hij

lemma singletonSubspace_projection_epi (P : Pair.{w}) [Nonempty P.sub]
    [Subsingleton P.sub] (i : ℤ) :
    Epi (homologyMap (projection (ordinaryFunctor R M) P) i) := by
  let h := P202.RelativeSingularChains.ordinary_short_exact R M P
  let hs := HomologicalComplex.shortExact_of_degreewise_shortExact _ h
  exact (hs.homology_exact₃ i (i-1) (by simp)).epi_f
    (singletonSubspace_connecting_zero R M P i (i-1) (by simp))

lemma singletonSubspace_projection_isIso (P : Pair.{w}) [Nonempty P.sub]
    [Subsingleton P.sub] (n : ℕ) (hn : 0 < n) :
    IsIso (homologyMap (projection (ordinaryFunctor R M) P) (n : ℤ)) := by
  let h := P202.RelativeSingularChains.ordinary_short_exact R M P
  let hs := HomologicalComplex.shortExact_of_degreewise_shortExact _ h
  letI := singletonSubspace_projection_epi R M P (n : ℤ)
  have hz : IsZero (homology R M P.sub (n : ℤ)) :=
    P202.SingularDegreeZero.totallyDisconnectedHomology R M P.sub (n : ℤ) (by omega)
  haveI : Mono (homologyMap (projection (ordinaryFunctor R M) P) (n : ℤ)) :=
    (hs.homology_exact₂ (n : ℤ)).mono_g (hz.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

def singletonSubspaceProjectionIso (P : Pair.{w}) [Nonempty P.sub]
    [Subsingleton P.sub] (n : ℕ) (hn : 0 < n) :
    homology R M P.space (n : ℤ) ≅ relativeHomology R M P (n : ℤ) := by
  letI := singletonSubspace_projection_isIso R M P n hn
  exact asIso (homologyMap (projection (ordinaryFunctor R M) P) (n : ℤ))

@[simp] lemma singletonSubspaceProjectionIso_hom (P : Pair.{w}) [Nonempty P.sub]
    [Subsingleton P.sub] (n : ℕ) (hn : 0 < n) :
    (singletonSubspaceProjectionIso R M P n hn).hom =
      homologyMap (projection (ordinaryFunctor R M) P) (n : ℤ) := rfl

end P202.Homology.CellularDegrees.ConnectingBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.Homology.CellularDegrees.PositiveComparison
open P202Specs.SingularChains
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

def reducedToOrdinary (X : TopCat.{w}) : reducedComplex R M X ⟶ ordinaryComplex R M X where
  f i := match i with
    | .ofNat n => (reducedNonnegativeIso R M X n).hom ≫ (ordinaryNonnegativeIso R M X n).inv
    | .negSucc _ => 0
  comm' i j hij := by
    change j + 1 = i at hij
    cases i with
    | ofNat k =>
      cases j with
      | ofNat n =>
        simp only [Int.ofNat_eq_natCast] at hij
        have hk : k = n+1 := by omega
        subst k
        change ((reducedNonnegativeIso R M X (n+1)).hom ≫ _ ) ≫ _ =
          _ ≫ ((reducedNonnegativeIso R M X n).hom ≫ _)
        have ho := P202.SingularChains.ordinary_boundary R M X n
        have hr := P202.SingularChains.reduced_boundary R M X n
        rw [← hr] at ho
        simpa only [Int.ofNat_eq_natCast, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
          Iso.hom_inv_id, Category.comp_id] using
          congrArg (fun f => (reducedNonnegativeIso R M X (n+1)).hom ≫ f ≫
            (ordinaryNonnegativeIso R M X n).inv) ho
      | negSucc n =>
        have hz := P202.SingularChains.ordinary_negative_chains R M X (Int.negSucc n) (by omega)
        exact hz.eq_of_tgt _ _
    | negSucc k =>
      have hj : j < 0 := by omega
      have hz := P202.SingularChains.ordinary_negative_chains R M X j hj
      exact hz.eq_of_tgt _ _

@[simp] lemma reducedToOrdinary_f (X : TopCat.{w}) (n : ℕ) :
    (reducedToOrdinary R M X).f (n : ℤ) =
      (reducedNonnegativeIso R M X n).hom ≫ (ordinaryNonnegativeIso R M X n).inv := rfl

instance reducedToOrdinary_f_isIso (X : TopCat.{w}) (n : ℕ) :
    IsIso ((reducedToOrdinary R M X).f (n : ℤ)) := by
  rw [reducedToOrdinary_f]
  infer_instance

lemma ordinary_map_degree {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    ((ordinaryFunctor R M).map f).f (n : ℤ) ≫ (ordinaryNonnegativeIso R M Y n).hom =
      (ordinaryNonnegativeIso R M X n).hom ≫ (chainMap R M f).f n := by
  change (extendMap (chainMap R M f) (degreeEmbedding 0)).f (n : ℤ) ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _
    (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)]
  simp [ordinaryNonnegativeIso]

lemma reduced_map_degree {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    ((reducedFunctor R M).map f).f (n : ℤ) ≫ (reducedNonnegativeIso R M Y n).hom =
      (reducedNonnegativeIso R M X n).hom ≫ (chainMap R M f).f n := by
  change (extendMap (augmentedShiftedMap R M f) (degreeEmbedding (-1))).f (n : ℤ) ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _
    (show (degreeEmbedding (-1)).f (n+1) = (n : ℤ) by
      change (-1 : ℤ) + ((n+1 : ℕ) : ℤ) = n; omega)]
  simp [reducedNonnegativeIso, augmentedShiftedMap]

lemma reducedToOrdinary_natural {X Y : TopCat.{w}} (f : X ⟶ Y) :
    (reducedFunctor R M).map f ≫ reducedToOrdinary R M Y =
      reducedToOrdinary R M X ≫ (ordinaryFunctor R M).map f := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | ofNat n =>
    apply (cancel_mono (ordinaryNonnegativeIso R M Y n).hom).mp
    change ((reducedFunctor R M).map f).f (n : ℤ) ≫
        ((reducedNonnegativeIso R M Y n).hom ≫ (ordinaryNonnegativeIso R M Y n).inv) ≫
        (ordinaryNonnegativeIso R M Y n).hom =
      ((reducedNonnegativeIso R M X n).hom ≫ (ordinaryNonnegativeIso R M X n).inv) ≫
        ((ordinaryFunctor R M).map f).f (n : ℤ) ≫ (ordinaryNonnegativeIso R M Y n).hom
    simp only [Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rw [reduced_map_degree, ordinary_map_degree]
    simp
  | negSucc n =>
    exact (P202.SingularChains.ordinary_negative_chains R M Y (Int.negSucc n)
      (by omega)).eq_of_tgt _ _

lemma reducedToOrdinary_homology_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (j : ℤ) :
    (reducedHomologyFunctor R M j).map f ≫ homologyMap (reducedToOrdinary R M Y) j =
      homologyMap (reducedToOrdinary R M X) j ≫ (homologyFunctor R M j).map f := by
  change homologyMap ((reducedFunctor R M).map f) j ≫ _ =
    _ ≫ homologyMap ((ordinaryFunctor R M).map f) j
  simpa only [homologyMap_comp] using
    congrArg (fun g => homologyMap g j) (reducedToOrdinary_natural R M f)

lemma reducedToOrdinary_homology_isIso (X : TopCat.{w}) (n : ℕ) :
    IsIso (homologyMap (reducedToOrdinary R M X) ((n+1 : ℕ) : ℤ)) := by
  apply (quasiIsoAt_iff_isIso_homologyMap _ _).mp
  let φ := reducedToOrdinary R M X
  have hp : (ComplexShape.down ℤ).prev ((n+1 : ℕ) : ℤ) = ((n+2 : ℕ) : ℤ) := by
    exact (ComplexShape.down ℤ).prev_eq' (by
      change ((n+1 : ℕ) : ℤ) + 1 = ((n+2 : ℕ) : ℤ); omega)
  have hn : (ComplexShape.down ℤ).next ((n+1 : ℕ) : ℤ) = (n : ℤ) := by
    exact (ComplexShape.down ℤ).next_eq' (by
      change (n : ℤ) + 1 = ((n+1 : ℕ) : ℤ); omega)
  apply (quasiIsoAt_iff' φ ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ) (n : ℤ) hp hn).mpr
  let ψ := (shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℤ)
    ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ) (n : ℤ)).map φ
  haveI : IsIso ψ.τ₁ := by change IsIso (φ.f ((n+2 : ℕ) : ℤ)); infer_instance
  haveI : IsIso ψ.τ₂ := by change IsIso (φ.f ((n+1 : ℕ) : ℤ)); infer_instance
  haveI : IsIso ψ.τ₃ := by change IsIso (φ.f (n : ℤ)); infer_instance
  haveI : IsIso ψ := ShortComplex.isIso_of_isIso ψ
  exact ShortComplex.quasiIso_of_isIso ψ

end P202.Homology.CellularDegrees.PositiveComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.Homology.CellularDegrees.CoefficientAction
open P202Specs.SingularChains P202Specs.SpheresDisks
open P202.Homology.DiskBridge

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

lemma ordinary_sphere_action_via_comparison (n : ℕ) (f : sphere n ⟶ sphere n)
    (T : reducedComplex R M (sphere n) ⟶ ordinaryComplex R M (sphere n))
    [Epi (homologyMap T (n : ℤ))]
    (hn : (reducedFunctor R M).map f ≫ T = T ≫ (ordinaryFunctor R M).map f)
    (x : homology R M (sphere n) (n : ℤ)) :
    (P202Specs.SingularChains.homologyFunctor R M (n : ℤ)).map f x =
      P202Specs.Degree.degree n f • x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (homologyMap T (n : ℤ))).mp
    inferInstance x
  have he := congrArg (fun g => homologyMap g (n : ℤ)) hn
  simp only [homologyMap_comp] at he
  have hz := congrArg (fun g => g z) he
  change homologyMap T (n : ℤ)
      ((reducedHomologyFunctor R M (n : ℤ)).map f z) =
    (P202Specs.SingularChains.homologyFunctor R M (n : ℤ)).map f
      (homologyMap T (n : ℤ) z) at hz
  rw [sphere_action] at hz
  simpa using hz.symm

lemma ordinaryTransport_natural {X X' : TopCat.{0}} {Y Y' : TopCat.{w}}
    (e : X ≃ₜ Y) (e' : X' ≃ₜ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : ∀ x, e' (f x) = g (e x)) :
    (ordinaryFunctor R (ULift.{w} M)).map f ≫ (ordinaryTransport R M e').hom =
      (ordinaryTransport R M e).hom ≫ (ordinaryFunctor R M).map g := by
  let E := (degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)
  change E.map (chainMap R (ULift.{w} M) f) ≫ E.map (complexTransport R M e').hom =
    E.map (complexTransport R M e).hom ≫ E.map (chainMap R M g)
  rw [← E.map_comp, ← E.map_comp, complexTransport_natural R M e e' f g h]

def conjugateSelfMap {n : ℕ} {Y : TopCat.{w}} (h : sphere n ≃ₜ Y)
    (f : Y ⟶ Y) : sphere n ⟶ sphere n :=
  TopCat.ofHom ⟨fun x => h.symm (f (h x)),
    h.symm.continuous.comp (f.hom.continuous.comp h.continuous)⟩

lemma ordinary_sphere_action_transport {n : ℕ} {Y : TopCat.{w}}
    (h : sphere n ≃ₜ Y) (f : Y ⟶ Y)
    (hs : ∀ x : homology R (ULift.{w} M) (sphere n) (n : ℤ),
      (homologyFunctor R (ULift.{w} M) (n : ℤ)).map (conjugateSelfMap h f) x =
        P202Specs.Degree.degree n (conjugateSelfMap h f) • x)
    (x : homology R M Y (n : ℤ)) :
    (homologyFunctor R M (n : ℤ)).map f x =
      P202Specs.Degree.degree n (conjugateSelfMap h f) • x := by
  let e := (HomologicalComplex.homologyFunctor (ModuleCat.{max v w} R) (.down ℤ)
    (n : ℤ)).mapIso (ordinaryTransport R M h)
  have hn := congrArg (fun g => homologyMap g (n : ℤ))
    (ordinaryTransport_natural R M h h (conjugateSelfMap h f) f (fun x => by
      exact h.apply_symm_apply (f (h x))))
  simp only [homologyMap_comp] at hn
  change (homologyFunctor R (ULift.{w} M) (n : ℤ)).map (conjugateSelfMap h f) ≫ e.hom =
    e.hom ≫ (homologyFunctor R M (n : ℤ)).map f at hn
  have hx := congrArg (fun g => g (e.inv x)) hn
  simp only [ModuleCat.comp_apply] at hx
  rw [hs] at hx
  have he : e.hom (e.inv x) = x := e.toLinearEquiv.apply_symm_apply x
  simp only [map_zsmul] at hx
  erw [he] at hx
  exact hx.symm

theorem ordinary_sphere_action (n : ℕ) (hn : 0 < n) (f : sphere n ⟶ sphere n)
    (x : homology R M (sphere n) (n : ℤ)) :
    (P202Specs.SingularChains.homologyFunctor R M (n : ℤ)).map f x =
      P202Specs.Degree.degree n f • x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  haveI := P202.Homology.CellularDegrees.PositiveComparison.reducedToOrdinary_homology_isIso R M (sphere (k+1)) k
  exact ordinary_sphere_action_via_comparison R M (k+1) f
    (P202.Homology.CellularDegrees.PositiveComparison.reducedToOrdinary R M (sphere (k+1)))
    (P202.Homology.CellularDegrees.PositiveComparison.reducedToOrdinary_natural R M f) x

theorem homeomorphic_sphere_action (n : ℕ) (hn : 0 < n) {Y : TopCat.{w}}
    (h : sphere n ≃ₜ Y) (f : Y ⟶ Y) (x : homology R M Y (n : ℤ)) :
    (P202Specs.SingularChains.homologyFunctor R M (n : ℤ)).map f x =
      P202Specs.Degree.degree n (conjugateSelfMap h f) • x := by
  exact ordinary_sphere_action_transport R M h f
    (fun z => ordinary_sphere_action R (ULift.{w} M) n hn (conjugateSelfMap h f) z) x

end P202.Homology.CellularDegrees.CoefficientAction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Topology
namespace P202.Homology.CellularDegrees
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.CellularDegrees
open P202Specs.GoodPairQuotient

lemma absolute_projection_zero_of_range_in_subspace
    {Y : TopCat.{w}} {Q : Pair.{w}} (f : Y ⟶ Q.space)
    (h : ∀ x : Y, f x ∈ Q.subspace)
    {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} {shape : ComplexShape ι}
    (K : TopCat.{w} ⥤ HomologicalComplex C shape) :
    K.map f ≫ projection K Q = 0 := by
  let g : Y ⟶ Q.sub := TopCat.ofHom
    ⟨fun x => ⟨f x, h x⟩, f.hom.continuous.subtype_mk _⟩
  have hg : g ≫ Q.inclusion = f := rfl
  rw [← hg, K.map_comp, Category.assoc]
  change K.map g ≫ inclusion K Q ≫ cokernel.π (inclusion K Q) = 0
  simp

variable (X : Type w) [TopologicalSpace X] [CWStructure X]

open Classical in
lemma liftedCellCollapse_complement (n : ℕ) (c : Cell X n)
    (b : (referenceDiskPair.{w} n).sub)
    (q : skeletalPair X n ⟶ quotientPair (referenceDiskPair.{w} n))
    (hq : ∀ (d : Cell X n) (x : (referenceDiskPair.{w} n).space),
      q.map ((characteristicPairMap n d).map x) =
        if d = c then quotientProjection (referenceDiskPair.{w} n) x
        else quotientProjection (referenceDiskPair.{w} n) b.val)
    (x : skeletalSpace X (n+1)) (hx : x.val ∉ openCell X n c) :
    q.map x = quotientProjection (referenceDiskPair.{w} n) b.val := by
  classical
  let P := referenceDiskPair.{w} n
  let π := quotientProjection P
  obtain ⟨y, hy⟩ := (CWStructure.attachment_quotient (X := X) n).surjective x
  cases y with
  | inl y =>
    change oldSkeletonInclusion X n y = x at hy
    have hsub := q.mapsTo (show oldSkeletonInclusion X n y ∈
        (skeletalPair X n).subspace from y.property)
    obtain ⟨z, hz, hzx⟩ := hsub
    rw [← hy]
    exact hzx.symm.trans (Quotient.sound (Or.inr ⟨hz, b.property⟩))
  | inr y =>
    obtain ⟨d, z⟩ := y
    change diskToSkeleton X CWStructure.boundary_lands n d z = x at hy
    by_cases hd : d = c
    · subst d
      have hz : ‖z.val‖ = 1 := by
        have hle : ‖z.val‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
        apply le_antisymm hle
        by_contra h
        have hlt : ‖z.val‖ < 1 := lt_of_not_ge h
        apply hx
        rw [← hy]
        exact ⟨⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hlt⟩, rfl⟩
      have hqz := (hq c (ULift.up z)).trans (ite_eq_left rfl)
      rw [← hy]
      exact hqz.trans (Quotient.sound (Or.inr ⟨hz, b.property⟩))
    · rw [← hy]
      exact (hq d (ULift.up z)).trans (ite_eq_right hd)

lemma attachingBoundary_finite_cells (n : ℕ) (c : Cell X (n+1)) :
    ∃ F : Finset (Cell X n), ∀ d, d ∉ F →
      ∀ x : (referenceDiskPair.{w} (n+1)).sub,
        (attachingBoundary X n c x).val ∉ openCell X n d := by
  classical
  obtain ⟨S, hS⟩ := CWStructure.closure_finite (X := X) (n+1) c
  let F := S.preimage (Sigma.mk n) sigma_mk_injective.injOn
  refine ⟨F, ?_⟩
  intro d hd x hx
  have hclosed : (attachingBoundary X n c x).val ∈ closedCell X (n+1) c :=
    ⟨x.val.down, rfl⟩
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hS hclosed)
  obtain ⟨haS, hxa⟩ := Set.mem_iUnion.mp ha
  have heq : a = (⟨n, d⟩ : Σ m, Cell X m) := by
    by_contra hne
    exact Set.disjoint_left.mp (CWStructure.disjoint_interiors
      (Set.mem_univ a) (Set.mem_univ ⟨n,d⟩) hne) hxa hx
  subst a
  apply hd
  simpa only [F, Finset.mem_preimage] using haS

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The support set is independent of the entire relative class of the source
cell, hence in particular of its coefficient in any source orientation. -/
lemma cellBoundary_uniformFiniteSupport (n : ℕ)
    (b : (referenceDiskPair.{w} n).sub) (c : Cell X (n+1))
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : CharacteristicCoordinates X R M n g e) :
    ∃ F : Finset (Cell X n),
      ∀ (a : relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ))
        d, d ∉ F → e (differential X R M n (cellClass X R M (n+1) c a)) d = 0 := by
  classical
  obtain ⟨F, hF⟩ := attachingBoundary_finite_cells X n c
  refine ⟨F, ?_⟩
  intro a d hd
  obtain ⟨q, _, hq⟩ := liftedCellCollapse X n d b
  let P := referenceDiskPair.{w} n
  let Q := quotientPair P
  have hrange : ∀ x : (referenceDiskPair.{w} (n+1)).sub,
      (attachingBoundary X n c ≫ q.map) x ∈ Q.subspace := by
    intro x
    refine ⟨b.val, b.property, ?_⟩
    exact (liftedCellCollapse_complement X n d b q hq
      (attachingBoundary X n c x) (hF d hd x)).symm
  have hchain : (ordinaryFunctor R M).map (attachingBoundary X n c) ≫
      projection (ordinaryFunctor R M) (skeletalPair X n) ≫
        relativeMap (ordinaryFunctor R M) q = 0 := by
    rw [projection_map, ← Category.assoc, ← Functor.map_comp]
    exact absolute_projection_zero_of_range_in_subspace
      (attachingBoundary X n c ≫ q.map) hrange (ordinaryFunctor R M)
  have hH := congrArg (fun f => homologyMap f (n : ℤ)) hchain
  simp only [homologyMap_comp, homologyMap_zero] at hH
  have hzero : (relativeHomologyFunctor R M (n : ℤ)).map q
      (differential X R M n (cellClass X R M (n+1) c a)) = 0 := by
    rw [attachingNaturality]
    have hx0 := congrArg (fun f => f
      (pairConnecting R M (referenceDiskPair.{w} (n+1)) n a)) hH
    change (relativeHomologyFunctor R M (n : ℤ)).map q
      (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ)
        ((P202Specs.SingularChains.homologyFunctor R M (n : ℤ)).map
          (attachingBoundary X n c)
          (pairConnecting R M (referenceDiskPair.{w} (n+1)) n a))) = 0 at hx0
    exact hx0
  let b0 : Sphere n := ⟨b.val.down.val, by
    have hb := b.property
    change ‖b.val.down.val‖ = 1 at hb
    simpa only [Metric.mem_sphere, dist_zero_right] using hb⟩
  let D := Geometry.referenceDiskGoodPairData n b0
  let t := (relativeHomologyFunctor R M (n : ℤ)).map (quotientPairMap P)
  haveI : IsIso t := CoefficientAction.goodPairQuotient_relative R M D n
  have hcoord := collapseCoordinate X R M n d b q hq g e he
    (differential X R M n (cellClass X R M (n+1) c a))
  apply g.injective
  apply (asIso t).toLinearEquiv.injective
  change t (g (e (differential X R M n (cellClass X R M (n+1) c a)) d)) = t (g 0)
  simpa only [map_zero] using hcoord.symm.trans hzero

lemma cellBoundary_uniformFiniteSupport_positive (n : ℕ) (hn : 0 < n)
    (c : Cell X (n+1))
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : CharacteristicCoordinates X R M n g e) :
    ∃ F : Finset (Cell X n),
      ∀ (a : relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ))
        d, d ∉ F → e (differential X R M n (cellClass X R M (n+1) c a)) d = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : (referenceDiskPair.{w} n).sub :=
    ⟨ULift.up ⟨x, Metric.sphere_subset_closedBall hx⟩, by
      change ‖x‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  exact cellBoundary_uniformFiniteSupport X R M n b c g e he

end P202.Homology.CellularDegrees

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Topology
universe x y
namespace P202.Homology.CellularDegrees
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.CellularDegrees

section FinsuppFamily
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]
  {B : Type x} [AddCommGroup B] [Module R B] {I : Type y}

def finsuppFamilyLinearMap (g : ∀ i : I, A ≃ₗ[R] B) : (I →₀ A) →ₗ[R] (I →₀ B) :=
  Finsupp.lsum R fun i => (Finsupp.lsingle i).comp (g i).toLinearMap

@[simp] lemma finsuppFamilyLinearMap_single (g : ∀ i : I, A ≃ₗ[R] B) (i : I) (a : A) :
    finsuppFamilyLinearMap g (Finsupp.single i a) = Finsupp.single i (g i a) := by
  unfold finsuppFamilyLinearMap
  rw [Finsupp.lsum_single]
  rfl

def finsuppFamilyEquiv (g : ∀ i : I, A ≃ₗ[R] B) : (I →₀ A) ≃ₗ[R] (I →₀ B) :=
  LinearEquiv.ofLinearMap (finsuppFamilyLinearMap g)
    (finsuppFamilyLinearMap fun i => (g i).symm)
    (by
      apply Finsupp.lhom_ext
      intro i a
      simp only [LinearMap.comp_apply, finsuppFamilyLinearMap_single, LinearEquiv.apply_symm_apply,
        LinearMap.id_coe, id_eq])
    (by
      apply Finsupp.lhom_ext
      intro i a
      simp only [LinearMap.comp_apply, finsuppFamilyLinearMap_single, LinearEquiv.symm_apply_apply,
        LinearMap.id_coe, id_eq])

@[simp] lemma finsuppFamilyEquiv_single (g : ∀ i : I, A ≃ₗ[R] B) (i : I) (a : A) :
    finsuppFamilyEquiv g (Finsupp.single i a) = Finsupp.single i (g i a) :=
  finsuppFamilyLinearMap_single g i a

end FinsuppFamily

variable (X : Type w) [TopologicalSpace X] [CWStructure X]
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Coordinates permit a separate orientation on every cell. -/
def cellwiseOrientedCellEquiv (n : ℕ)
    (g : ∀ c : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)) :
    chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M) :=
  (P202.Homology.cellGroupSumIso X R M n n).symm.toLinearEquiv.trans
    (finsuppFamilyEquiv fun c => (g c).symm)

lemma cellwiseOrientedCellEquiv_characteristic (n : ℕ)
    (g : ∀ c : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (c : Cell X n) (m : M) :
    cellwiseOrientedCellEquiv X R M n g (cellClass X R M n c (g c m)) = Finsupp.single c m := by
  rw [cellClass, ← P202.Homology.cellGroupSumIso_single X R M n n c (g c m)]
  change finsuppFamilyEquiv (fun c => (g c).symm)
    ((P202.Homology.cellGroupSumIso X R M n n).inv
      ((P202.Homology.cellGroupSumIso X R M n n).hom (Finsupp.single c (g c m)))) = _
  rw [ModuleCat.inv_hom_apply, finsuppFamilyEquiv_single, LinearEquiv.symm_apply_apply]

theorem cellwiseOrientedCoordinates (n : ℕ)
    (g : ∀ c : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)) :
    ∃ e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M),
      ∀ c m, e (cellClass X R M n c (g c m)) = Finsupp.single c m :=
  ⟨cellwiseOrientedCellEquiv X R M n g, cellwiseOrientedCellEquiv_characteristic X R M n g⟩

lemma cellwiseCoordinates_unique (n : ℕ)
    (g : ∀ c : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e f : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : ∀ c m, e (cellClass X R M n c (g c m)) = Finsupp.single c m)
    (hf : ∀ c m, f (cellClass X R M n c (g c m)) = Finsupp.single c m) : e = f := by
  have hi : e.symm.toLinearMap = f.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro c m
    have he' : e.symm (Finsupp.single c m) = cellClass X R M n c (g c m) := by
      apply e.injective
      rw [e.apply_symm_apply, he]
    have hf' : f.symm (Finsupp.single c m) = cellClass X R M n c (g c m) := by
      apply f.injective
      rw [f.apply_symm_apply, hf]
    exact he'.trans hf'.symm
  have hs : e.symm = f.symm := LinearEquiv.toLinearMap_injective hi
  simpa using congrArg LinearEquiv.symm hs

open Classical in
lemma cellwiseCollapseCoordinate (n : ℕ) (c : Cell X n)
    (b : (referenceDiskPair.{w} n).sub)
    (q : skeletalPair X n ⟶ P202Specs.GoodPairQuotient.quotientPair (referenceDiskPair.{w} n))
    (hq : ∀ (d : Cell X n) (x : (referenceDiskPair.{w} n).space),
        q.map ((characteristicPairMap n d).map x) =
          if d = c then P202Specs.GoodPairQuotient.quotientProjection (referenceDiskPair.{w} n) x
          else P202Specs.GoodPairQuotient.quotientProjection (referenceDiskPair.{w} n) b.val)
    (g : ∀ d : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : ∀ d m, e (cellClass X R M n d (g d m)) = Finsupp.single d m)
    (z : chainGroup X R M n) :
    (relativeHomologyFunctor R M (n : ℤ)).map q z =
      (relativeHomologyFunctor R M (n : ℤ)).map
        (P202Specs.GoodPairQuotient.quotientPairMap (referenceDiskPair.{w} n)) (g c (e z c)) := by
  classical
  let F := relativeHomologyFunctor R M (n : ℤ)
  have hmaps : (F.map q).hom.comp e.symm.toLinearMap =
      ((F.map (P202Specs.GoodPairQuotient.quotientPairMap (referenceDiskPair.{w} n))).hom.comp
        (g c).toLinearMap).comp (Finsupp.lapply c) := by
    apply Finsupp.lhom_ext
    intro d m
    have hsingle : e.symm (Finsupp.single d m) = cellClass X R M n d (g d m) := by
      apply e.injective
      rw [e.apply_symm_apply, he]
    change F.map q (e.symm (Finsupp.single d m)) =
      F.map (P202Specs.GoodPairQuotient.quotientPairMap (referenceDiskPair.{w} n))
        (g c ((Finsupp.single d m) c))
    rw [hsingle]
    change F.map q (F.map (characteristicPairMap n d) (g d m)) = _
    rw [← ModuleCat.comp_apply, ← Functor.map_comp]
    by_cases hd : d = c
    · subst d
      have hm : characteristicPairMap n c ≫ q =
          P202Specs.GoodPairQuotient.quotientPairMap (referenceDiskPair.{w} n) := by
        apply PairMap.ext
        apply TopCat.hom_ext
        ext x
        exact (hq c x).trans (ite_eq_left rfl)
      rw [hm]
      simp
    · have hz : relativeMap (ordinaryFunctor R M) (characteristicPairMap n d ≫ q) = 0 := by
        apply relativeMap_zero_of_range_in_subspace
        intro x
        refine ⟨b.val, b.property, ?_⟩
        exact ((hq d x).trans (ite_eq_right hd)).symm
      change homologyMap (relativeMap (ordinaryFunctor R M) (characteristicPairMap n d ≫ q))
        (n : ℤ) (g d m) = _
      rw [hz, homologyMap_zero]
      simp [Finsupp.single_eq_of_ne (Ne.symm hd)]
  have hh := congrArg (fun f => f (e z)) hmaps
  change F.map q (e.symm (e z)) =
      F.map (P202Specs.GoodPairQuotient.quotientPairMap (referenceDiskPair.{w} n))
        (g c (e z c)) at hh
  rw [e.symm_apply_apply] at hh
  exact hh


end P202.Homology.CellularDegrees

namespace P202.Homology.CellularDegrees
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.CellularDegrees P202Specs.GoodPairQuotient
variable (X : Type w) [TopologicalSpace X] [CWStructure X]
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
lemma cellBoundary_cellwise_uniformFiniteSupport (n : ℕ)
    (b : (referenceDiskPair.{w} n).sub) (c : Cell X (n+1))
    (g : ∀ d : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : ∀ d m, e (cellClass X R M n d (g d m)) = Finsupp.single d m) :
    ∃ F : Finset (Cell X n),
      ∀ (a : relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ))
        d, d ∉ F → e (differential X R M n (cellClass X R M (n+1) c a)) d = 0 := by
  classical
  obtain ⟨F, hF⟩ := attachingBoundary_finite_cells X n c
  refine ⟨F, ?_⟩
  intro a d hd
  obtain ⟨q, _, hq⟩ := liftedCellCollapse X n d b
  let P := referenceDiskPair.{w} n
  let Q := quotientPair P
  have hrange : ∀ x : (referenceDiskPair.{w} (n+1)).sub,
      (attachingBoundary X n c ≫ q.map) x ∈ Q.subspace := by
    intro x
    refine ⟨b.val, b.property, ?_⟩
    exact (liftedCellCollapse_complement X n d b q hq
      (attachingBoundary X n c x) (hF d hd x)).symm
  have hchain : (ordinaryFunctor R M).map (attachingBoundary X n c) ≫
      projection (ordinaryFunctor R M) (skeletalPair X n) ≫
        relativeMap (ordinaryFunctor R M) q = 0 := by
    rw [projection_map, ← Category.assoc, ← Functor.map_comp]
    exact absolute_projection_zero_of_range_in_subspace
      (attachingBoundary X n c ≫ q.map) hrange (ordinaryFunctor R M)
  have hH := congrArg (fun f => homologyMap f (n : ℤ)) hchain
  simp only [homologyMap_comp, homologyMap_zero] at hH
  have hzero : (relativeHomologyFunctor R M (n : ℤ)).map q
      (differential X R M n (cellClass X R M (n+1) c a)) = 0 := by
    rw [attachingNaturality]
    have hx0 := congrArg (fun f => f
      (pairConnecting R M (referenceDiskPair.{w} (n+1)) n a)) hH
    change (relativeHomologyFunctor R M (n : ℤ)).map q
      (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ)
        ((P202Specs.SingularChains.homologyFunctor R M (n : ℤ)).map
          (attachingBoundary X n c)
          (pairConnecting R M (referenceDiskPair.{w} (n+1)) n a))) = 0 at hx0
    exact hx0
  let b0 : Sphere n := ⟨b.val.down.val, by
    have hb := b.property
    change ‖b.val.down.val‖ = 1 at hb
    simpa only [Metric.mem_sphere, dist_zero_right] using hb⟩
  let D := Geometry.referenceDiskGoodPairData n b0
  let t := (relativeHomologyFunctor R M (n : ℤ)).map (quotientPairMap P)
  haveI : IsIso t := CoefficientAction.goodPairQuotient_relative R M D n
  have hcoord := cellwiseCollapseCoordinate X R M n d b q hq g e he
    (differential X R M n (cellClass X R M (n+1) c a))
  apply (g d).injective
  apply (asIso t).toLinearEquiv.injective
  change t (g d (e (differential X R M n (cellClass X R M (n+1) c a)) d)) = t (g d 0)
  simpa only [map_zero] using hcoord.symm.trans hzero

lemma cellBoundary_cellwise_uniformFiniteSupport_positive (n : ℕ) (hn : 0 < n)
    (c : Cell X (n+1))
    (g : ∀ d : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : ∀ d m, e (cellClass X R M n d (g d m)) = Finsupp.single d m) :
    ∃ F : Finset (Cell X n),
      ∀ (a : relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ))
        d, d ∉ F → e (differential X R M n (cellClass X R M (n+1) c a)) d = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : (referenceDiskPair.{w} n).sub :=
    ⟨ULift.up ⟨x, Metric.sphere_subset_closedBall hx⟩, by
      change ‖x‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  exact cellBoundary_cellwise_uniformFiniteSupport X R M n b c g e he


end P202.Homology.CellularDegrees

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Topology
namespace P202.Homology.CellularDegrees.AttachingCalculation
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.CellularDegrees P202Specs.SpheresDisks
open P202Specs.GoodPairQuotient
open P202.Homology.CellularDegrees
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

abbrev referenceQuotient (n : ℕ) : Pair.{w} := quotientPair (referenceDiskPair.{w} n)

lemma referenceQuotient_nonempty (n : ℕ) (b : (referenceDiskPair.{w} n).sub) :
    Nonempty (referenceQuotient.{w} n).sub :=
  ⟨⟨quotientProjection _ b.val, b.val, b.property, rfl⟩⟩

lemma referenceQuotient_subsingleton (n : ℕ) : Subsingleton (referenceQuotient.{w} n).sub := by
  constructor
  rintro ⟨x, a, ha, rfl⟩ ⟨y, b, hb, rfl⟩
  apply Subtype.ext
  apply Quotient.sound
  exact Or.inr ⟨ha, hb⟩

def referenceQuotientProjectionIso (n : ℕ) (hn : 0 < n)
    (b : (referenceDiskPair.{w} n).sub) :
    homology R M (referenceQuotient.{w} n).space (n : ℤ) ≅
      relativeHomology R M (referenceQuotient.{w} n) (n : ℤ) := by
  letI := referenceQuotient_nonempty n b
  letI := referenceQuotient_subsingleton.{w} n
  exact ConnectingBridge.singletonSubspaceProjectionIso R M _ n hn

def diskQuotientRelativeIso (n : ℕ) (b : (referenceDiskPair.{w} n).sub) :
    relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ) ≅
      relativeHomology R M (referenceQuotient.{w} n) (n : ℤ) := by
  let b0 : Sphere n := ⟨b.val.down.val, by
    have hb : ‖b.val.down.val‖ = 1 := b.property
    simpa only [Metric.mem_sphere, dist_zero_right] using hb⟩
  let D := Geometry.referenceDiskGoodPairData n b0
  let t := (relativeHomologyFunctor R M (n : ℤ)).map
    (quotientPairMap (referenceDiskPair.{w} n))
  haveI : IsIso t := CoefficientAction.goodPairQuotient_relative R M D n
  exact asIso t

variable (n : ℕ) (hn : 0 < n) (b : (referenceDiskPair.{w} n).sub)
variable (hS : (referenceDiskPair.{w} (n+1)).sub ≃ₜ ULift.{w} (sphere n))
variable (hT : (referenceQuotient.{w} n).space ≃ₜ ULift.{w} (sphere n))

def quotientBoundaryHomeomorph : (referenceQuotient.{w} n).space ≃ₜ
    (referenceDiskPair.{w} (n+1)).sub := hT.trans hS.symm

def nextDiskOrientation
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)) :
    M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ) :=
  g.trans ((diskQuotientRelativeIso R M n b).toLinearEquiv.trans
    ((referenceQuotientProjectionIso R M n hn b).symm.toLinearEquiv.trans
      (((homologyFunctor R M (n : ℤ)).mapIso
        (TopCat.isoOfHomeo (quotientBoundaryHomeomorph n hS hT))).toLinearEquiv.trans
          (ConnectingBridge.referenceDiskConnectingIso R M n hn).symm.toLinearEquiv)))

lemma nextDiskOrientation_boundary
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)) (m : M) :
    pairConnecting R M (referenceDiskPair.{w} (n+1)) n
      (nextDiskOrientation R M n hn b hS hT g m) =
    (homologyFunctor R M (n : ℤ)).map (TopCat.isoOfHomeo
      (quotientBoundaryHomeomorph n hS hT)).hom
      ((referenceQuotientProjectionIso R M n hn b).inv
        ((diskQuotientRelativeIso R M n b).hom (g m))) := by
  change (ConnectingBridge.referenceDiskConnectingIso R M n hn).hom
    ((ConnectingBridge.referenceDiskConnectingIso R M n hn).inv _) = _
  exact (ConnectingBridge.referenceDiskConnectingIso R M n hn).inv_hom_id_apply _

variable (X : Type w) [TopologicalSpace X] [CWStructure X]

def attachingQuotientEndomorphism (q : skeletalPair X n ⟶ referenceQuotient.{w} n)
    (c : Cell X (n+1)) : (referenceQuotient.{w} n).space ⟶ (referenceQuotient.{w} n).space :=
  (TopCat.isoOfHomeo (quotientBoundaryHomeomorph n hS hT)).hom ≫
    attachingBoundary X n c ≫ q.map

def attachingSphereMap (q : skeletalPair X n ⟶ referenceQuotient.{w} n)
    (c : Cell X (n+1)) : sphere n ⟶ sphere n :=
  CoefficientAction.conjugateSelfMap (hT.trans Homeomorph.ulift).symm
    (attachingQuotientEndomorphism n hS hT X q c)

open Classical in
/-- Calculation for any chosen geometric sphere charts, with the adjacent
relative disk orientations specified by those charts. -/
lemma attaching_degree_normalized
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : CharacteristicCoordinates X R M n g e)
    (c : Cell X (n+1)) (d : Cell X n)
    (q : skeletalPair X n ⟶ referenceQuotient.{w} n)
    (hq : ∀ (k : Cell X n) (x : (referenceDiskPair.{w} n).space),
      q.map ((characteristicPairMap n k).map x) =
        if k = d then quotientProjection (referenceDiskPair.{w} n) x
        else quotientProjection (referenceDiskPair.{w} n) b.val) (m : M) :
    e (differential X R M n (cellClass X R M (n+1) c
      (nextDiskOrientation R M n hn b hS hT g m))) d =
      P202Specs.Degree.degree n (attachingSphereMap n hS hT X q c) • m := by
  let z := cellClass X R M (n+1) c (nextDiskOrientation R M n hn b hS hT g m)
  let A := diskQuotientRelativeIso R M n b
  let P := referenceQuotientProjectionIso R M n hn b
  let k := (TopCat.isoOfHomeo (quotientBoundaryHomeomorph n hS hT)).hom
  let F := homologyFunctor R M (n : ℤ)
  let a := attachingBoundary X n c
  have hcoord := collapseCoordinate X R M n d b q hq g e he (differential X R M n z)
  have hnat : homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ) ≫
      (relativeHomologyFunctor R M (n : ℤ)).map q =
    F.map q.map ≫ P.hom := by
    change homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ) ≫
      homologyMap (relativeMap (ordinaryFunctor R M) q) (n : ℤ) =
      homologyMap ((ordinaryFunctor R M).map q.map) (n : ℤ) ≫
        homologyMap (projection (ordinaryFunctor R M) (referenceQuotient.{w} n)) (n : ℤ)
    simpa only [homologyMap_comp] using
      congrArg (fun f => homologyMap f (n : ℤ)) (projection_map (ordinaryFunctor R M) q)
  change (relativeHomologyFunctor R M (n : ℤ)).map q (differential X R M n z) =
    A.hom (g (e (differential X R M n z) d)) at hcoord
  have hcollapse : A.hom (g (e (differential X R M n z) d)) =
      P.hom (F.map (k ≫ a ≫ q.map) (P.inv (A.hom (g m)))) := by
    rw [← hcoord]
    dsimp only [z]
    rw [attachingNaturality]
    have ht := congrArg (fun f => f
      (F.map a (pairConnecting R M (referenceDiskPair.{w} (n+1)) n
        (nextDiskOrientation R M n hn b hS hT g m)))) hnat
    simp only [ModuleCat.comp_apply] at ht
    refine ht.trans ?_
    apply congrArg P.hom
    simp only [Functor.map_comp, ModuleCat.comp_apply]
    apply congrArg (F.map q.map)
    apply congrArg (F.map a)
    exact nextDiskOrientation_boundary R M n hn b hS hT g m
  have hscalar := CoefficientAction.homeomorphic_sphere_action R M n hn
    (hT.trans Homeomorph.ulift).symm (k ≫ a ≫ q.map) (P.inv (A.hom (g m)))
  change F.map (k ≫ a ≫ q.map) (P.inv (A.hom (g m))) =
    P202Specs.Degree.degree n (attachingSphereMap n hS hT X q c) • _ at hscalar
  rw [hscalar, map_zsmul, Iso.inv_hom_id_apply] at hcollapse
  apply g.injective
  apply A.toLinearEquiv.injective
  change A.hom (g (e (differential X R M n z) d)) =
    A.hom (g (P202Specs.Degree.degree n (attachingSphereMap n hS hT X q c) • m))
  rw [map_zsmul, map_zsmul]
  exact hcollapse


variable (s : M ≃ₗ[R] homology R M (TopCat.of (ULift.{w} (sphere n))) (n : ℤ))

def sourceChartOrientation :
    M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ) :=
  s.trans (((homologyFunctor R M (n : ℤ)).mapIso (TopCat.isoOfHomeo hS)).symm.toLinearEquiv.trans
    (ConnectingBridge.referenceDiskConnectingIso R M n hn).symm.toLinearEquiv)

def targetChartOrientation :
    M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ) :=
  s.trans (((homologyFunctor R M (n : ℤ)).mapIso (TopCat.isoOfHomeo hT)).symm.toLinearEquiv.trans
    ((referenceQuotientProjectionIso R M n hn b).toLinearEquiv.trans
      (diskQuotientRelativeIso R M n b).symm.toLinearEquiv))

lemma nextDiskOrientation_chart :
    nextDiskOrientation R M n hn b hS hT (targetChartOrientation R M n hn b hT s) =
      sourceChartOrientation R M n hn hS s := by
  apply LinearEquiv.ext
  intro m
  apply (ConnectingBridge.referenceDiskConnectingIso R M n hn).toLinearEquiv.injective
  change pairConnecting R M (referenceDiskPair.{w} (n+1)) n _ = _
  rw [nextDiskOrientation_boundary]
  let F := homologyFunctor R M (n : ℤ)
  let HS : homology R M (referenceDiskPair.{w} (n+1)).sub (n : ℤ) ≅
      homology R M (TopCat.of (ULift.{w} (sphere n))) (n : ℤ) :=
    F.mapIso (TopCat.isoOfHomeo hS)
  let HT : homology R M (referenceQuotient.{w} n).space (n : ℤ) ≅
      homology R M (TopCat.of (ULift.{w} (sphere n))) (n : ℤ) :=
    F.mapIso (TopCat.isoOfHomeo hT)
  let A := diskQuotientRelativeIso R M n b
  let P := referenceQuotientProjectionIso R M n hn b
  have hk : F.map (TopCat.isoOfHomeo (quotientBoundaryHomeomorph n hS hT)).hom =
      HT.hom ≫ HS.inv := by
    change F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp]
    rfl
  change F.map (TopCat.isoOfHomeo (quotientBoundaryHomeomorph n hS hT)).hom
    (P.inv (A.hom ((targetChartOrientation R M n hn b hT s) m))) = _
  rw [hk]
  change HS.inv (HT.hom (P.inv (A.hom (A.inv (P.hom (HT.inv (s m))))))) =
    (ConnectingBridge.referenceDiskConnectingIso R M n hn).hom
      ((ConnectingBridge.referenceDiskConnectingIso R M n hn).inv (HS.inv (s m)))
  simp only [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply]

open Classical in
/-- Calculation for any chosen geometric sphere charts, with the adjacent
relative disk orientations specified by those charts. -/
lemma attaching_degree_cellwise_normalized
    (g : ∀ k : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))
    (he : ∀ k m, e (cellClass X R M n k (g k m)) = Finsupp.single k m)
    (c : Cell X (n+1)) (d : Cell X n)
    (q : skeletalPair X n ⟶ referenceQuotient.{w} n)
    (hq : ∀ (k : Cell X n) (x : (referenceDiskPair.{w} n).space),
      q.map ((characteristicPairMap n k).map x) =
        if k = d then quotientProjection (referenceDiskPair.{w} n) x
        else quotientProjection (referenceDiskPair.{w} n) b.val) (m : M) :
    e (differential X R M n (cellClass X R M (n+1) c
      (nextDiskOrientation R M n hn b hS hT (g d) m))) d =
      P202Specs.Degree.degree n (attachingSphereMap n hS hT X q c) • m := by
  let z := cellClass X R M (n+1) c (nextDiskOrientation R M n hn b hS hT (g d) m)
  let A := diskQuotientRelativeIso R M n b
  let P := referenceQuotientProjectionIso R M n hn b
  let k := (TopCat.isoOfHomeo (quotientBoundaryHomeomorph n hS hT)).hom
  let F := homologyFunctor R M (n : ℤ)
  let a := attachingBoundary X n c
  have hcoord := cellwiseCollapseCoordinate X R M n d b q hq g e he (differential X R M n z)
  have hnat : homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ) ≫
      (relativeHomologyFunctor R M (n : ℤ)).map q =
    F.map q.map ≫ P.hom := by
    change homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ) ≫
      homologyMap (relativeMap (ordinaryFunctor R M) q) (n : ℤ) =
      homologyMap ((ordinaryFunctor R M).map q.map) (n : ℤ) ≫
        homologyMap (projection (ordinaryFunctor R M) (referenceQuotient.{w} n)) (n : ℤ)
    simpa only [homologyMap_comp] using
      congrArg (fun f => homologyMap f (n : ℤ)) (projection_map (ordinaryFunctor R M) q)
  change (relativeHomologyFunctor R M (n : ℤ)).map q (differential X R M n z) =
    A.hom (g d (e (differential X R M n z) d)) at hcoord
  have hcollapse : A.hom (g d (e (differential X R M n z) d)) =
      P.hom (F.map (k ≫ a ≫ q.map) (P.inv (A.hom (g d m)))) := by
    rw [← hcoord]
    dsimp only [z]
    rw [attachingNaturality]
    have ht := congrArg (fun f => f
      (F.map a (pairConnecting R M (referenceDiskPair.{w} (n+1)) n
        (nextDiskOrientation R M n hn b hS hT (g d) m)))) hnat
    simp only [ModuleCat.comp_apply] at ht
    refine ht.trans ?_
    apply congrArg P.hom
    simp only [Functor.map_comp, ModuleCat.comp_apply]
    apply congrArg (F.map q.map)
    apply congrArg (F.map a)
    exact nextDiskOrientation_boundary R M n hn b hS hT (g d) m
  have hscalar := CoefficientAction.homeomorphic_sphere_action R M n hn
    (hT.trans Homeomorph.ulift).symm (k ≫ a ≫ q.map) (P.inv (A.hom (g d m)))
  change F.map (k ≫ a ≫ q.map) (P.inv (A.hom (g d m))) =
    P202Specs.Degree.degree n (attachingSphereMap n hS hT X q c) • _ at hscalar
  rw [hscalar, map_zsmul, Iso.inv_hom_id_apply] at hcollapse
  apply (g d).injective
  apply A.toLinearEquiv.injective
  change A.hom (g d (e (differential X R M n z) d)) =
    A.hom (g d (P202Specs.Degree.degree n (attachingSphereMap n hS hT X q c) • m))
  rw [map_zsmul, map_zsmul]
  exact hcollapse



lemma sourceChartOrientation_compatible :
    SourceChartCoordinate R M n hS s (sourceChartOrientation R M n hn hS s) := by
  intro m
  let C := ConnectingBridge.referenceDiskConnectingIso R M n hn
  let HS : homology R M (referenceDiskPair.{w} (n+1)).sub (n : ℤ) ≅
      homology R M (P202Specs.CellularDegrees.liftedSphere.{w} n) (n : ℤ) :=
    (homologyFunctor R M (n : ℤ)).mapIso (TopCat.isoOfHomeo hS)
  change HS.hom (C.hom (C.inv (HS.inv (s m)))) = s m
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

lemma targetChartOrientation_compatible :
    TargetChartCoordinate R M n hT s (targetChartOrientation R M n hn b hT s) := by
  intro m
  let A := diskQuotientRelativeIso R M n b
  let P := referenceQuotientProjectionIso R M n hn b
  let HT : homology R M (referenceQuotient.{w} n).space (n : ℤ) ≅
      homology R M (P202Specs.CellularDegrees.liftedSphere.{w} n) (n : ℤ) :=
    (homologyFunctor R M (n : ℤ)).mapIso (TopCat.isoOfHomeo hT)
  change A.hom (A.inv (P.hom (HT.inv (s m)))) = P.hom (HT.inv (s m))
  exact A.inv_hom_id_apply _

lemma attachingSphereMap_eq_chart (q : skeletalPair X n ⟶ referenceQuotient.{w} n)
    (c : Cell X (n+1)) :
    attachingSphereMap n hS hT X q c = chartAttachingMap X n hS hT q c := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (hT (q.map (attachingBoundary X n c
    (hS.symm (hT (hT.symm (ULift.up x))))))).down = _
  rw [hT.apply_symm_apply]
  rfl

end P202.Homology.CellularDegrees.AttachingCalculation

namespace P202.Homology.CellularDegrees
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.CellularDegrees P202Specs.SpheresDisks
open P202Specs.GoodPairQuotient
open AttachingCalculation

theorem geometricBoundaryFormula :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (hn : 0 < n) (b : (referenceDiskPair.{w} n).sub)
    (hS : ∀ c : Cell X (n+1), (referenceDiskPair.{w} (n+1)).sub ≃ₜ liftedSphere.{w} n)
    (hT : ∀ d : Cell X n, quotientSpace (referenceDiskPair.{w} n) ≃ₜ liftedSphere.{w} n)
    (s : M ≃ₗ[R] homology R M (liftedSphere.{w} n) (n : ℤ)),
    ∃ (gS : ∀ c : Cell X (n+1), M ≃ₗ[R]
        relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ))
      (gT : ∀ d : Cell X n, M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
      (e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M)),
      (∀ c, SourceChartCoordinate R M n (hS c) s (gS c)) ∧
      (∀ d, TargetChartCoordinate R M n (hT d) s (gT d)) ∧
      CellwiseCharacteristicCoordinates R M X n gT e ∧
      (∀ d : Cell X n, ∃ q : skeletalPair X n ⟶ quotientPair (referenceDiskPair.{w} n),
        SelectedCellCollapse X n d b q ∧
        ∀ (c : Cell X (n+1)) (m : M),
          e (differential X R M n (cellClass X R M (n+1) c (gS c m))) d =
            P202Specs.Degree.degree n (chartAttachingMap X n (hS c) (hT d) q c) • m) ∧
      ∀ c : Cell X (n+1), ∃ F : Finset (Cell X n),
        ∀ (a : relativeHomology R M (referenceDiskPair.{w} (n+1)) ((n+1 : ℕ) : ℤ))
          d, d ∉ F → e (differential X R M n (cellClass X R M (n+1) c a)) d = 0 := by
  intro X _ _ R _ M _ _ n hn b hS hT s
  let gS := fun c => sourceChartOrientation R M n hn (hS c) s
  let gT := fun d => targetChartOrientation R M n hn b (hT d) s
  obtain ⟨e, he⟩ := cellwiseOrientedCoordinates X R M n gT
  refine ⟨gS, gT, e, ?_, ?_, he, ?_, ?_⟩
  · intro c
    exact sourceChartOrientation_compatible R M n hn (hS c) s
  · intro d
    exact targetChartOrientation_compatible R M n hn b (hT d) s
  · intro d
    obtain ⟨q, hquot, hq⟩ := liftedCellCollapse X n d b
    refine ⟨q, ⟨hquot, hq, ?_⟩, ?_⟩
    · intro x hx
      exact liftedCellCollapse_complement X n d b q hq x hx
    · intro c m
      have hh := attaching_degree_cellwise_normalized R M n hn b (hS c) (hT d)
        X gT e he c d q hq m
      have hg : nextDiskOrientation R M n hn b (hS c) (hT d) (gT d) = gS c :=
        nextDiskOrientation_chart R M n hn b (hS c) (hT d) s
      rw [hg, attachingSphereMap_eq_chart] at hh
      exact hh
  · intro c
    exact cellBoundary_cellwise_uniformFiniteSupport X R M n b c gT e he

theorem chartDataExist : Expected.chartDataExist.{u,v,w} := by
  intro R _ M _ _ n hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let b0 : Sphere n := ⟨x, hx⟩
  let b : (referenceDiskPair.{w} n).sub :=
    ⟨ULift.up (boundaryInclusion n b0), by
      change ‖x‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  let ht := Geometry.referenceDiskQuotientSphereHomeomorph.{w} n b0
  let htIso : (referenceQuotient.{w} n).space ≅ P202Specs.CellularDegrees.liftedSphere.{w} n :=
    TopCat.isoOfHomeo ht
  let HS := (homologyFunctor R M (n : ℤ)).mapIso htIso
  obtain ⟨g⟩ := (P202.Homology.DiskBridge.referenceDiskHomology R M n n).1 rfl
  let sm := g.symm.trans ((diskQuotientRelativeIso R M n b).toLinearEquiv.trans
    ((referenceQuotientProjectionIso R M n hn b).symm.toLinearEquiv.trans HS.toLinearEquiv))
  exact ⟨⟨b⟩, ⟨ConnectingBridge.referenceBoundarySphereHomeomorph n⟩, ⟨ht⟩, ⟨sm⟩⟩

end P202.Homology.CellularDegrees
