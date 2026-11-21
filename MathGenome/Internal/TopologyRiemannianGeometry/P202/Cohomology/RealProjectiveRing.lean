import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.RealProjectiveRing
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.RealProjectiveHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficients
import Mathlib.Algebra.Field.ZMod
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.LocalOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.CompactOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.ThomClass
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.TransverseThomProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.RelativeCupProduct
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Models
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.RealProjectiveSpace
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.SliceStructures
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.TransversePreimage

/-! The real-projective singular cohomology ring over F₂, with its actual
hyperplane Thom-image generator, grading, truncation, and normalized local and
global fundamental-class evaluations on every standard projective subspace. -/
noncomputable section
namespace P202.Cohomology.RealProjectiveRing
open P202Specs.RealProjectiveRing
open Polynomial
open P202Specs.CupProduct P202Specs.RealProjectiveHomology
open scoped DirectSum

/-- The principal relation is valid in the literal polynomial quotient. -/
theorem quotientTruncation : Expected.quotientTruncation := by
  intro R _ m
  have ht : variableClass R m ^ (m+1) = 0 := by
    change (AdjoinRoot.mk (X ^ (m+1)) X) ^ (m+1) = 0
    rw [← map_pow]
    exact AdjoinRoot.mk_self
  exact ⟨ht, fun n hn => pow_eq_zero_of_le (by omega) ht⟩

/-- This is the algebraic endpoint, before identifying cohomology of RP⁰. -/
theorem quotientPoint : Expected.quotientPoint := by
  intro R _
  let e : AdjoinRoot (X - C (0 : R)) ≃ₐ[R] R := Polynomial.quotientSpanXSubCAlgEquiv 0
  exact ⟨(AdjoinRoot.algEquivOfEq R (X^(0+1)) (X-C (0:R)) (by simp)).trans e⟩

/-- The sign in the upstream graded-commutativity formula is trivial mod two. -/
theorem modTwoCommutative : Expected.modTwoCommutative := by
  intro X C
  let := C.gradedRing
  intro a b
  induction a using DirectSum.induction_on with
  | zero => simp
  | of p a =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of q b =>
      rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
      simp only [C.product_eq]
      apply DirectSum.of_eq_of_gradedMonoid_eq
      have hs : ((-1 : ℤ) ^ (p*q)) • C.product q p b a = C.product q p b a := by
        have hn : ((-1 : ℤ) : ZMod 2) = 1 := by decide
        rw [← Int.cast_smul_eq_zsmul (R := ZMod 2), Int.cast_pow, hn, one_pow, one_smul]
      simpa only [hs] using C.graded_commutative p q a b
    | add b c hb hc => simp only [mul_add, add_mul, hb, hc]
  | add a c ha hc => simp only [mul_add, add_mul, ha, hc]

/-- Uniqueness of a mod-two orientation generator, independently of geometry. -/
theorem modTwoGeneratorUnique : Expected.modTwoGeneratorUnique := by
  intro V _ _ a b ha hb
  obtain ⟨r, hr⟩ := ha.2 b
  have hcases : r = 0 ∨ r = 1 := by
    have hrlt := r.val_lt
    have hv : r.val = 0 ∨ r.val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl (ZMod.val_injective 2 hv)
    · exact Or.inr (ZMod.val_injective 2 hv)
  rcases hcases with rfl | rfl
  · have hb0 : b = 0 := by simpa using hr.symm
    have heq : (0 : ZMod 2) = 1 := hb.1 (by simp [hb0])
    exact False.elim (zero_ne_one heq)
  · simpa using hr


/-- A nilpotent element whose initial powers form a basis gives exactly the
truncated polynomial algebra. This proves bijectivity, not just a quotient map. -/
theorem presentationFromBasis : Expected.presentationFromBasis := by
  intro R _ _ A _ _ m x hx b hb
  let p : Polynomial R := X ^ (m+1)
  let pb := AdjoinRoot.powerBasis' (monic_X_pow (R := R) (m+1))
  have hd : p.natDegree = m+1 := by simp [p]
  have hz : p.eval₂ (Algebra.ofId R A) x = 0 := by
    simpa [p] using hx
  let f : AdjoinRoot p →ₐ[R] A := AdjoinRoot.liftAlgHom p (Algebra.ofId R A) x hz
  let e : AdjoinRoot p ≃ₗ[R] A := pb.basis.equiv b (finCongr hd)
  have hf : f.toLinearMap = e.toLinearMap := by
    apply pb.basis.ext
    intro i
    change f (pb.basis i) = (pb.basis.equiv b (finCongr hd)) (pb.basis i)
    rw [Module.Basis.equiv_apply, pb.basis_eq_pow]
    rw [hb]
    change f (AdjoinRoot.root p ^ (i : ℕ)) = x ^ (i : ℕ)
    simp only [map_pow, f, AdjoinRoot.liftAlgHom_root]
  have hbij : Function.Bijective f := by
    change Function.Bijective f.toLinearMap
    rw [hf]
    exact e.bijective
  refine ⟨AlgEquiv.ofBijective f hbij, ?_⟩
  change f (AdjoinRoot.root p) = x
  exact AdjoinRoot.liftAlgHom_root p (Algebra.ofId R A) x hz

section GradedBasis
variable (R : Type*) [CommRing R]
variable (M : ℕ → Type*) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
variable (m : ℕ) (p : ∀ n, M n)
variable (gen : ∀ n, n ≤ m → Function.Bijective (fun r : R => r • p n))
variable (above : ∀ n, m < n → ∀ a : M n, a = 0)

private def gradedCoordinate (i : Fin (m+1)) : (⨁ n, M n) →ₗ[R] R :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton R (M i.val) (p i.val))
    (gen i.val (by omega))).symm.toLinearMap.comp (DirectSum.component R ℕ M i.val)

private theorem gradedCoordinate_of (i j : Fin (m+1)) :
    gradedCoordinate R M m p gen i (DirectSum.of M j.val (p j.val)) = if i=j then 1 else 0 := by
  classical
  by_cases h : i=j
  · subst j
    change (LinearEquiv.ofBijective (LinearMap.toSpanSingleton R (M i.val) (p i.val))
      (gen i.val (by omega))).symm ((DirectSum.of M i.val (p i.val)) i.val) = _
    rw [DirectSum.of_eq_same, ite_eq_left rfl]
    apply (LinearEquiv.ofBijective (LinearMap.toSpanSingleton R (M i.val) (p i.val))
      (gen i.val (by omega))).injective
    rw [LinearEquiv.apply_symm_apply]
    change p i.val = (1 : R) • p i.val
    rw [one_smul]
  · have hval : i.val ≠ j.val := fun hv => h (Fin.ext hv)
    change (LinearEquiv.ofBijective (LinearMap.toSpanSingleton R (M i.val) (p i.val))
      (gen i.val (by omega))).symm ((DirectSum.of M j.val (p j.val)) i.val) = _
    rw [DirectSum.of_eq_of_ne _ _ _ hval, map_zero, ite_eq_right h]

include gen above in
 theorem finiteGradedBasis : ∃ b : Module.Basis (Fin (m+1)) R (⨁ n, M n),
      ∀ i, b i = DirectSum.of M i.val (p i.val) := by
  classical
  let v : Fin (m+1) → (⨁ n, M n) := fun i => DirectSum.of M i.val (p i.val)
  have hi : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro f hf i
    have h := congrArg (gradedCoordinate R M m p gen i) hf
    simpa [map_sum, map_smul, v, gradedCoordinate_of] using h
  have hs : ∀ a, a ∈ Submodule.span R (Set.range v) := by
    intro a
    induction a using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of n a =>
      by_cases hn : n ≤ m
      · obtain ⟨r, rfl⟩ := (gen n hn).2 a
        rw [DirectSum.of_smul]
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨⟨n, by omega⟩, rfl⟩
      · rw [above n (by omega) a, map_zero]
        exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
  exact ⟨Module.Basis.mk hi (fun _ _ => hs _), fun i => Module.Basis.mk_apply _ _ _⟩

end GradedBasis

/-- All algebraic assembly, including the finite basis and homogeneous powers.
The geometric construction of these powers remains a separate obligation. -/
theorem presentationFromPowers : Expected.presentationFromPowers := by
  intro m C p
  letI := C.gradedRing
  letI := C.algebra
  intro hp gen above
  letI : CommRing (HStar (ZMod 2) (projective m)) :=
    { (inferInstance : Ring (HStar (ZMod 2) (projective m))) with
      mul_comm := modTwoCommutative _ C }
  let x : HStar (ZMod 2) (projective m) := DirectSum.of _ 1 (p 1)
  have hx : x ^ (m+1) = 0 := by
    rw [hp, above (m+1) (by omega) (p (m+1)), map_zero]
  obtain ⟨b, hb⟩ := finiteGradedBasis (ZMod 2) (H (ZMod 2) (projective m)) m p gen above
  obtain ⟨e, he⟩ := presentationFromBasis
    (ZMod 2) (HStar (ZMod 2) (projective m)) m x hx b (fun i => (hb i).trans (hp i.val).symm)
  refine ⟨{ powers := p, equiv := e, homogeneous := ?_, generators := gen, above := above }⟩
  intro n
  rw [map_pow, he, hp]

open CategoryTheory CategoryTheory.Limits
open P202Specs.SingularChains P202Specs.CohomologyPairs
open P202Specs.RealProjectiveHomology

/-- All finite real projective quotients have one mod-two degree-zero class. -/
theorem cohomologyDegreeZero : Expected.cohomologyDegreeZero := by
  intro m
  let eh := (Classical.choice
    (P202.SingularDegreeZero.degreeZero (ZMod 2) (ZMod 2) (projective m))).trans
      (Finsupp.uniqueLinearEquiv (ZMod 2) (ZMod 2) (Classical.arbitrary _))
  let ev := P202Specs.UniversalCoefficients.evaluation (ZMod 2) (ZMod 2)
    (ordinaryComplex (ZMod 2) (ZMod 2) (projective m)) 0
  let e := LinearEquiv.ofBijective ev
    (P202.UniversalCoefficients.evaluation_bijective (ZMod 2)
      (ordinaryComplex (ZMod 2) (ZMod 2) (projective m)) 0)
  exact ⟨e.trans ((LinearEquiv.arrowCongr eh
    (LinearEquiv.refl (ZMod 2) (ZMod 2))).trans
      (LinearMap.ringLmapEquivSelf (ZMod 2) (ZMod 2) (ZMod 2)))⟩

private theorem pointHomologyPositive (n : ℕ) (hn : 0 < n) :
    IsZero (homology (ZMod 2) (ZMod 2) (projective 0) (n : ℤ)) := by
  let e := (homologyFunctor (ZMod 2) (ZMod 2) (n : ℤ)).mapIso
    (TopCat.isoOfHomeo (X := projective 0)
      (Y := P202Specs.SingularDegreeZero.point.{0})
      P202.Homology.RealProjectiveHomology.zeroHomeomorph)
  exact e.isZero_iff.mpr
    (P202.SingularDegreeZero.pointOrdinaryOther (ZMod 2) (ZMod 2) (n : ℤ) (by omega))

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Field UCT computes the actual singular cohomology of the point quotient,
not just the dimension-zero polynomial quotient. -/
theorem pointCohomology : Expected.pointCohomology := by
  refine ⟨cohomologyDegreeZero 0, ?_⟩
  intro n hn a
  haveI := ModuleCat.subsingleton_of_isZero (pointHomologyPositive n hn)
  apply (P202.UniversalCoefficients.evaluation_bijective (ZMod 2)
    (ordinaryComplex (ZMod 2) (ZMod 2) (projective 0)) (n : ℤ)).1
  exact Subsingleton.elim _ _

/-- When all positive summands vanish, the degree-zero inclusion is onto. -/
private theorem zeroInclusionBijective
    (M : ℕ → Type*) [∀ n, AddCommGroup (M n)]
    (h : ∀ n : ℕ, 0 < n → ∀ a : M n, a = 0) :
    Function.Bijective (DirectSum.of M 0) := by
  refine ⟨DirectSum.of_injective 0, ?_⟩
  intro a
  induction a using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n a =>
    cases n with
    | zero => exact ⟨a, rfl⟩
    | succ n => exact ⟨0, by simp [h (n+1) (by omega) a]⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a+b, map_add _ _ _⟩

private theorem modTwoCases (r : ZMod 2) : r = 0 ∨ r = 1 := by
  have hr := r.val_lt
  have hv : r.val = 0 ∨ r.val = 1 := by omega
  exact hv.imp (fun h => ZMod.val_injective 2 h) (fun h => ZMod.val_injective 2 h)

/-- The coefficient algebra of the actual point quotient. No geometric
normal-orientation data is needed in dimension zero. -/
private def pointAlgebraEquiv (C : CohomologyRing (ZMod 2) (projective 0)) :
    letI := C.gradedRing
    letI := C.algebra
    ZMod 2 ≃ₐ[ZMod 2] HStar (ZMod 2) (projective 0) := by
  letI := C.gradedRing
  letI := C.algebra
  let e0 := Classical.choice pointCohomology.1
  have habove := pointCohomology.2
  let incl : H (ZMod 2) (projective 0) 0 ≃ₗ[ZMod 2]
      HStar (ZMod 2) (projective 0) :=
    LinearEquiv.ofBijective (DirectSum.lof (ZMod 2) ℕ (H (ZMod 2) (projective 0)) 0)
      (zeroInclusionBijective _ habove)
  let e := incl.symm.trans e0
  haveI : Nontrivial (HStar (ZMod 2) (projective 0)) := e.toEquiv.nontrivial
  have he1 : e (1 : HStar (ZMod 2) (projective 0)) = 1 := by
    rcases modTwoCases (e 1) with h | h
    · have hz : (1 : HStar (ZMod 2) (projective 0)) = 0 :=
        e.injective (h.trans (map_zero e).symm)
      exact False.elim (one_ne_zero hz)
    · exact h
  let f : ZMod 2 →ₐ[ZMod 2] HStar (ZMod 2) (projective 0) := Algebra.ofId _ _
  have hf : ∀ r, e (f r) = r := by
    intro r
    change e (algebraMap _ _ r) = r
    rw [Algebra.algebraMap_eq_smul_one, map_smul, he1, smul_eq_mul, mul_one]
  apply AlgEquiv.ofBijective f
  constructor
  · intro a b hab
    calc a = e (f a) := (hf a).symm
         _ = e (f b) := congrArg e hab
         _ = b := hf b
  · intro a
    exact ⟨e a, e.injective (hf (e a))⟩

/-- The dimension-zero projective space has the full asserted graded
presentation, on the existing singular cohomology ring and its unit. -/
theorem pointPresentation : Expected.pointPresentation := by
  intro C
  letI := C.gradedRing
  letI := C.algebra
  let e := (Classical.choice (quotientPoint (ZMod 2))).trans (pointAlgebraEquiv C)
  let p : ∀ n, H (ZMod 2) (projective 0) n
    | 0 => GradedMonoid.GOne.one
    | _+1 => 0
  refine ⟨{ powers := p
            equiv := e
            homogeneous := ?_
            generators := ?_
            above := pointCohomology.2 }⟩
  · intro n
    cases n with
    | zero =>
      change e (_ ^ 0) = DirectSum.of _ 0 GradedMonoid.GOne.one
      rw [pow_zero, map_one]
      exact (DirectSum.of_zero_one _).symm
    | succ n =>
      rw [(quotientTruncation (ZMod 2) 0).2 (n+1) (by omega), map_zero]
      exact (map_zero (DirectSum.of _ (n+1))).symm
  · intro n hn
    have hn0 : n = 0 := by omega
    subst n
    have he : Function.Bijective
        (fun r : ZMod 2 => algebraMap (ZMod 2) (HStar (ZMod 2) (projective 0)) r) :=
      (pointAlgebraEquiv C).bijective
    have hfac : ∀ r : ZMod 2,
        DirectSum.of (H (ZMod 2) (projective 0)) 0 (r • p 0) =
          algebraMap (ZMod 2) (HStar (ZMod 2) (projective 0)) r := by
      intro r
      rw [DirectSum.of_smul]
      change r • (1 : HStar (ZMod 2) (projective 0)) = _
      exact (Algebra.algebraMap_eq_smul_one r).symm
    constructor
    · intro a b hab
      apply he.1
      exact (hfac a).symm.trans ((congrArg (DirectSum.of _ 0) hab).trans (hfac b))
    · intro a
      obtain ⟨r, hr⟩ := he.2 (DirectSum.of _ 0 a)
      refine ⟨r, ?_⟩
      apply DirectSum.of_injective 0
      rw [hfac r]
      exact hr


universe w

theorem cupPower_homogeneous : Expected.cupPowerHomogeneous.{w} := by
  intro X C u
  letI := C.gradedRing
  intro n
  induction n with
  | zero => exact (DirectSum.of_zero_one _).symm
  | succ n ih =>
    rw [pow_succ, ih, DirectSum.of_mul_of]
    simp only [C.product_eq]
    rfl

theorem cupPower_one {X : TopCat.{w}} (C : CohomologyRing (ZMod 2) X)
    (u : H (ZMod 2) X 1) : cupPower C u 1 = u := by
  letI := C.gradedRing
  apply DirectSum.of_injective 1
  rw [← cupPower_homogeneous, pow_one]

theorem cupPower_natural (μ : NaturalCohomologyRing.{0,w} (ZMod 2))
    {X Y : TopCat.{w}} (f : X ⟶ Y) (u : H (ZMod 2) Y 1) (n : ℕ) :
    hPullback (ZMod 2) f n (cupPower (μ.ring Y) u n) =
      cupPower (μ.ring X) (hPullback (ZMod 2) f 1 u) n := by
  letI := (μ.ring X).gradedRing
  letI := (μ.ring X).algebra
  letI := (μ.ring Y).gradedRing
  letI := (μ.ring Y).algebra
  apply DirectSum.of_injective n
  rw [← μ.pullback_homogeneous, ← cupPower_homogeneous, map_pow,
    μ.pullback_homogeneous, cupPower_homogeneous]


/-- The independent restriction map agrees with the accepted coordinate inclusion. -/
theorem standardInclusion_eq (n m : ℕ) (h : n ≤ m) :
    standardInclusion n m h = TopCat.ofHom
      (P202.Homology.RealProjectiveHomology.projectiveInclusion n m h) := by
  ext x
  induction x using Quotient.inductionOn with | _ x => rfl

open P202.Cellular P202Specs.CellularChains

lemma homologyAboveDimension (m j : ℕ) (hj : m < j)
    (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    IsZero (homology R M (projective m) (j : ℤ)) := by
  letI := P202.Homology.RealProjectiveHomology.standardCW m
  obtain ⟨labels, _⟩ := P202.Homology.RealProjectiveHomology.standardCW_standard m
  haveI : IsEmpty (Cell (Space m) j) :=
    ⟨fun c => (Nat.not_le_of_gt hj) ((labels j c).property)⟩
  let e := Classical.choice (P202.Homology.cellularCellGroups (Space m) R M j)
  have hz : IsZero (chainGroup (Space m) R M j) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact e.injective.subsingleton
  let K := cellularComplex (Space m) R M
  have hK : IsZero (K.homology j) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (K.sc j) hz
  exact (P202.Homology.CellularComparison.comparisonIso (Space m) R M j).isZero_iff.mp hK

lemma cohomologyAboveDimension (m j : ℕ) (hj : m < j)
    (K : Type*) [Field K] (a : P202Specs.CupProduct.H K (projective m) j) : a = 0 := by
  let ev := P202Specs.UniversalCoefficients.evaluation K K
    (ordinaryComplex K K (projective m)) (j : ℤ)
  apply (P202.UniversalCoefficients.evaluation_bijective K
    (ordinaryComplex K K (projective m)) (j : ℤ)).injective
  change ev a = ev 0
  haveI := ModuleCat.subsingleton_of_isZero (homologyAboveDimension m j hj K K)
  apply LinearMap.ext
  intro z
  have hz : z = 0 := Subsingleton.elim _ _
  simp [hz]


/-- Specialization of field vanishing to the requested coefficient field. -/
theorem modTwoCohomologyAboveDimension : Expected.cohomologyAboveDimension := by
  intro m n hn a
  exact cohomologyAboveDimension m n hn (ZMod 2) a


namespace ModTwoGroups
open P202.Cellular P202Specs.RealProjectiveHomology P202Specs.SpheresDisks
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains P202Specs.CellularDegrees P202Specs.GoodPairQuotient
open P202.Homology.RealProjectiveHomology
open P202.Homology.CellularDegrees.AttachingCalculation
abbrev F := ZMod 2

lemma incidence_smul_zero (j : ℕ) (a : F) : incidence j • a = 0 := by
  rcases Nat.even_or_odd j with he | ho
  · rw [incidence_even he]
    simpa [two_smul] using ZModModule.add_self a
  · rw [incidence_odd ho, zero_smul]

lemma boundary_one_zero (m : ℕ) :
    letI := standardCW m
    differential (Space m) F F 0 = 0 := by
  classical
  letI := standardCW m
  obtain ⟨labels, hchar⟩ := standardCW_standard m
  haveI := cell_subsingleton labels 1
  ext z
  change differential (Space m) F F 0 z = 0
  by_cases hm : 1 ≤ m
  · obtain ⟨h⟩ := P202.Homology.CellularDegrees.intervalParametrization_nonempty
    obtain ⟨g, e, hz, he, hg, hboundary⟩ :=
      P202.Homology.CellularDegrees.intervalCellBoundary (Space m) F F h
    obtain ⟨g1⟩ := (P202.Homology.DiskBridge.referenceDiskHomology F F 1 1).1 rfl
    let e1 := P202.Homology.orientedCellEquiv (Space m) F F 1 g1.symm
    let c := (labels 1).symm ⟨(), hm⟩
    let a := e1 z c
    have hz' : cellClass (Space m) F F 1 c (g1.symm a) = z := by
      apply e1.injective
      change P202.Homology.orientedCellEquiv (Space m) F F 1 g1.symm
        (cellClass (Space m) F F 1 c (g1.symm a)) = e1 z
      rw [cellClass, P202.Homology.orientedCellEquiv_characteristic]
      ext d
      have hd : d = c := Subsingleton.elim _ _
      subst d
      simp [a]
    rw [← hz']
    obtain ⟨vfinal, vinitial, hv, hw, hd⟩ := hboundary c
    apply e.injective
    rw [map_zero]
    haveI := cell_subsingleton labels 0
    have hsame : vfinal = vinitial := Subsingleton.elim _ _
    simpa only [LinearEquiv.apply_symm_apply, hsame, sub_self] using hd (g.symm (g1.symm a))
  · haveI : IsEmpty (Cell (Space m) 1) := ⟨fun c => hm (labels 1 c).property⟩
    obtain ⟨e⟩ := P202.Homology.cellularCellGroups (Space m) F F 1
    have hz : z = 0 := e.injective (Subsingleton.elim _ _)
    simp [hz]

lemma differential_zero (m n : ℕ) :
    letI := standardCW m
    differential (Space m) F F n = 0 := by
  classical
  letI := standardCW m
  obtain ⟨labels, hchar⟩ := standardCW_standard m
  haveI := cell_subsingleton labels (n+1)
  by_cases hn : 0 < n
  · by_cases hm : n+1 ≤ m
    · let D := standardAttachingCharts n hn
      let g := (Classical.choice
        ((P202.Homology.DiskBridge.referenceDiskHomology F F n n).1 rfl)).symm
      let e := P202.Homology.orientedCellEquiv (Space m) F F n g
      have he : CharacteristicCoordinates (Space m) F F n g e :=
        P202.Homology.orientedCellEquiv_characteristic (Space m) F F n g
      let gS := nextDiskOrientation F F n hn D.boundaryPoint D.source D.target g
      let eS := P202.Homology.orientedCellEquiv (Space m) F F (n+1) gS
      let c := (labels (n+1)).symm ⟨(), hm⟩
      ext z
      change differential (Space m) F F n z = 0
      let a := eS z c
      have hz : cellClass (Space m) F F (n+1) c (gS a) = z := by
        apply eS.injective
        change P202.Homology.orientedCellEquiv (Space m) F F (n+1) gS
          (cellClass (Space m) F F (n+1) c (gS a)) = eS z
        rw [cellClass, P202.Homology.orientedCellEquiv_characteristic]
        ext d
        have hd : d = c := Subsingleton.elim _ _
        subst d
        simp [a]
      rw [← hz]
      apply e.injective
      rw [map_zero]
      ext d
      obtain ⟨q, _, hq⟩ := P202.Homology.CellularDegrees.liftedCellCollapse
        (Space m) n d D.boundaryPoint
      have h := attaching_degree_normalized F F n hn D.boundaryPoint D.source D.target
        (Space m) g e he c d q hq a
      rw [attachingSphereMap_eq_chart] at h
      have hq' (z : (referenceDiskPair.{0} n).space) :
          q.map ((characteristicPairMap n d).map z) = quotientProjection _ z := by
        simpa using hq d z
      have hf := polynomial_chartAttachingMap m n hm (boundaryPole n hn) c d q hq'
      change chartAttachingMap (Space m) n D.source D.target q c = sphereFold n at hf
      rw [hf, sphereFold_degree] at h
      exact h.trans (incidence_smul_zero (n+1) a)
    · haveI : IsEmpty (Cell (Space m) (n+1)) := ⟨fun c => hm (labels (n+1) c).property⟩
      obtain ⟨e⟩ := P202.Homology.cellularCellGroups (Space m) F F (n+1)
      ext z
      have hz : z = 0 := e.injective (Subsingleton.elim _ _)
      simp [hz]
  · have hn0 : n = 0 := by omega
    subst n
    exact boundary_one_zero m


def zeroDifferentialHomology {R : Type} [CommRing R]
    (K : ChainComplex (ModuleCat R) ℕ) (hd : ∀ n, K.d (n+1) n = 0) (n : ℕ) :
    K.homology n ≃ₗ[R] K.X n := by
  have hf : (K.sc n).f = 0 := by
    change K.d ((ComplexShape.down ℕ).prev n) n = 0
    rw [ChainComplex.prev]
    exact hd n
  have hg : (K.sc n).g = 0 := by
    change K.d n ((ComplexShape.down ℕ).next n) = 0
    cases n with
    | zero => rw [ChainComplex.next_nat_zero]; exact K.shape 0 0 (by decide)
    | succ n => rw [ChainComplex.next_nat_succ]; exact hd n
  exact ((ShortComplex.LeftHomologyData.ofZeros (K.sc n) hf hg).homologyIso).toLinearEquiv

/-- Every actual mod-two homology group in degrees zero through m is F₂. -/
def homologyCoordinate (m n : ℕ) (hn : n ≤ m) :
    homology F F (projective m) (n : ℤ) ≃ₗ[F] F := by
  classical
  letI := standardCW m
  let labels := Classical.choose (standardCW_standard m)
  haveI := cell_subsingleton labels n
  let e := Classical.choice (P202.Homology.cellularCellGroups (Space m) F F n)
  let eC := e.trans (Finsupp.uniqueLinearEquiv F F ((labels n).symm ⟨(), hn⟩))
  let K := cellularComplex (Space m) F F
  have hd : ∀ j, K.d (j+1) j = 0 := by
    intro j
    simpa only [K, cellularComplex, ChainComplex.of, ChainComplex.of_d] using differential_zero m j
  exact (P202.Homology.CellularComparison.comparisonIso (Space m) F F n).symm.toLinearEquiv.trans
    ((zeroDifferentialHomology K hd n).trans eC)

/-- The actual singular cup-product grading has one copy of F₂ in every
indicated projective degree. -/
def cohomologyCoordinate (m n : ℕ) (hn : n ≤ m) :
    P202Specs.CupProduct.H F (projective m) n ≃ₗ[F] F := by
  let e := LinearEquiv.ofBijective
    (P202Specs.UniversalCoefficients.evaluation F F
      (ordinaryComplex F F (projective m)) (n : ℤ))
    ((P202.UniversalCoefficients.field_duality F).1 (projective m) n)
  exact e.trans ((LinearEquiv.arrowCongr (homologyCoordinate m n hn)
    (LinearEquiv.refl F F)).trans (LinearMap.ringLmapEquivSelf F F F))


/-- Evaluation one on any genuine homology class certifies a generator. -/
lemma generatorOfEvaluation (m n : ℕ) (hn : n ≤ m)
    (a : P202Specs.CupProduct.H F (projective m) n)
    (z : homology F F (projective m) (n : ℤ))
    (h : P202Specs.UniversalCoefficients.evaluation F F
      (ordinaryComplex F F (projective m)) (n : ℤ) a z = 1) :
    Function.Bijective (fun r : F => r • a) := by
  let e := cohomologyCoordinate m n hn
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, map_zero, LinearMap.zero_apply] at h
    exact zero_ne_one h
  have he : e a ≠ 0 := fun h0 => ha (e.injective (h0.trans e.map_zero.symm))
  constructor
  · intro r s hrs
    have hh := congrArg e hrs
    simp only [map_smul, smul_eq_mul] at hh
    exact mul_right_cancel₀ he hh
  · intro y
    refine ⟨e y / e a, e.injective ?_⟩
    simp only [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ (e y) he

end ModTwoGroups

/-- Every indicated graded group is a copy of the specified field. -/
theorem cohomologyGroups : Expected.cohomologyGroups := by
  intro m n hn
  exact ⟨ModTwoGroups.cohomologyCoordinate m n hn⟩


theorem generatorOfNonzero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] K) (a : V) (ha : a ≠ 0) :
    Function.Bijective (fun r : K => r • a) := by
  have hea : e a ≠ 0 := fun h => ha (e.injective (h.trans (map_zero e).symm))
  constructor
  · intro r s h
    have hh := congrArg e h
    simp only [map_smul, smul_eq_mul] at hh
    exact mul_right_cancel₀ hea hh
  · intro b
    refine ⟨e b / e a, ?_⟩
    apply e.injective
    simp only [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ _ hea

theorem presentationWithPowers (m : ℕ) (C : CohomologyRing (ZMod 2) (projective m))
    (p : ∀ n, H (ZMod 2) (projective m) n) :
    letI := C.gradedRing
    letI := C.algebra
    (∀ n, (DirectSum.of _ 1 (p 1)) ^ n = DirectSum.of _ n (p n)) →
    (∀ n, n ≤ m → Function.Bijective (fun r : ZMod 2 => r • p n)) →
    (∀ n, m < n → ∀ a : H (ZMod 2) (projective m) n, a = 0) →
    ∃ P : Presentation m C, P.powers = p := by
  letI := C.gradedRing
  letI := C.algebra
  intro hp gen above
  letI : CommRing (HStar (ZMod 2) (projective m)) :=
    { (inferInstance : Ring (HStar (ZMod 2) (projective m))) with
      mul_comm := modTwoCommutative _ C }
  let x : HStar (ZMod 2) (projective m) := DirectSum.of _ 1 (p 1)
  have hx : x ^ (m+1) = 0 := by
    rw [hp, above (m+1) (by omega) (p (m+1)), map_zero]
  obtain ⟨b, hb⟩ := finiteGradedBasis (ZMod 2) (H (ZMod 2) (projective m)) m p gen above
  obtain ⟨e, he⟩ := presentationFromBasis
    (ZMod 2) (HStar (ZMod 2) (projective m)) m x hx b (fun i => (hb i).trans (hp i.val).symm)
  refine ⟨{ powers := p, equiv := e, homogeneous := ?_, generators := gen, above := above }, rfl⟩
  intro n
  rw [map_pow, he, hp]

theorem presentationFromEvaluations (m : ℕ) (μ : NaturalCohomologyRing (ZMod 2))
    (u : H (ZMod 2) (projective m) 1)
    (heval : ∀ n (hn : n ≤ m), ∃ z : homology (ZMod 2) (ZMod 2) (projective n) (n : ℤ),
      kronecker (projective n) n
        (hPullback (ZMod 2) (standardInclusion n m hn) n (cupPower (μ.ring (projective m)) u n)) z = 1) :
    ∃ P : Presentation m (μ.ring (projective m)),
      ∀ n, P.powers n = cupPower (μ.ring (projective m)) u n := by
  let C := μ.ring (projective m)
  let p := cupPower C u
  have gen : ∀ n, n ≤ m → Function.Bijective (fun r : ZMod 2 => r • p n) := by
    intro n hn
    apply generatorOfNonzero (Classical.choice (cohomologyGroups m n hn))
    intro hz
    obtain ⟨z, h⟩ := heval n hn
    change kronecker (projective n) n (hPullback (ZMod 2)
      (standardInclusion n m hn) n (p n)) z = 1 at h
    rw [hz, map_zero, map_zero, LinearMap.zero_apply] at h
    exact zero_ne_one h
  have hp : letI := C.gradedRing
      ∀ n, (DirectSum.of _ 1 (p 1)) ^ n = DirectSum.of _ n (p n) := by
    letI := C.gradedRing
    intro n
    change (DirectSum.of _ 1 (cupPower C u 1)) ^ n = _
    rw [cupPower_one]
    exact cupPower_homogeneous _ C u n
  obtain ⟨P, hP⟩ := presentationWithPowers m C p hp gen (modTwoCohomologyAboveDimension m)
  exact ⟨P, fun n => congrFun hP n⟩


open HomologicalComplex P202Specs.RelativeSingularChains

lemma relativeEvaluation (R : Type*) [CommRing R] (P : Pair) (n : ℤ)
    (a : relativeCohomology R R P n) (z : homology R R P.space n) :
    P202Specs.UniversalCoefficients.evaluation R R (ordinaryComplex R R P.space) n
      (homologyMap (relativeToAbsolute R R P) n a) z =
    P202Specs.UniversalCoefficients.evaluation R R (ordinary R R P) n a
      (homologyMap (projection (ordinaryFunctor R R) P) n z) := by
  have h := P202.UniversalCoefficientsCohomology.evaluation_natural R R R
    (projection (ordinaryFunctor R R) P) (LinearMap.id : R →ₗ[R] R) n a z
  rw [P202.UniversalCoefficientsCohomology.dualMap_id] at h
  exact h

open P202Specs.LocalOrientation P202Specs.CompactOrientation

lemma absoluteToLocal (R : Type*) [CommRing R] {M : Type*} [TopologicalSpace M]
    (n : ℕ) (x : M) (z : homology R R (TopCat.of M) (n : ℤ)) :
    homologyMap (projection (ordinaryFunctor R R) (localPair M x)) (n : ℤ) z =
      restrictPoint R (Set.mem_univ x) n (absoluteToSupported R M n z) := by
  let p := projection (ordinaryFunctor R R) (supportedPair M Set.univ)
  let q := relativeMap (ordinaryFunctor R R) (pointMap (Set.mem_univ x))
  let r := projection (ordinaryFunctor R R) (localPair M x)
  have h : p ≫ q = r :=
    (projection_map (ordinaryFunctor R R) (pointMap (Set.mem_univ x))).trans
      ((congrArg (fun f => f ≫ r) ((ordinaryFunctor R R).map_id (TopCat.of M))).trans
        (Category.id_comp r))
  have hh : homologyMap p (n : ℤ) ≫ homologyMap q (n : ℤ) =
      homologyMap r (n : ℤ) :=
    (homologyMap_comp p q (n : ℤ)).symm.trans (congrArg (fun f => homologyMap f (n : ℤ)) h)
  exact (congrArg (fun f => f z) hh).symm

lemma localEvaluation (R : Type*) [CommRing R] {M : Type*} [TopologicalSpace M]
    (n : ℕ) (x : M) (o : LocalChoice R n M)
    (z : homology R R (TopCat.of M) (n : ℤ))
    (hz : HasLocalValues R o Set.univ (absoluteToSupported R M n z))
    (a : relativeCohomology R R (localPair M x) (n : ℤ)) :
    P202Specs.UniversalCoefficients.evaluation R R
      (ordinaryComplex R R (TopCat.of M)) (n : ℤ)
      (homologyMap (relativeToAbsolute R R (localPair M x)) (n : ℤ) a) z =
      P202Specs.UniversalCoefficients.evaluation R R (ordinary R R (localPair M x))
        (n : ℤ) a (o x) := by
  have h₁ := relativeEvaluation R (localPair M x) (n : ℤ) a z
  have h₂ := absoluteToLocal R n x z
  have h₃ := hz x (Set.mem_univ x)
  exact h₁.trans (congrArg (fun y => P202Specs.UniversalCoefficients.evaluation R R
    (ordinary R R (localPair M x)) (n : ℤ) a y) (h₂.trans h₃))

lemma localEvaluation_one (R : Type*) [CommRing R] {M : Type*} [TopologicalSpace M]
    (n : ℕ) (x : M) (o : LocalChoice R n M)
    (z : homology R R (TopCat.of M) (n : ℤ))
    (hz : HasLocalValues R o Set.univ (absoluteToSupported R M n z))
    (a : relativeCohomology R R (localPair M x) (n : ℤ))
    (ha : P202Specs.UniversalCoefficients.evaluation R R
      (ordinary R R (localPair M x)) (n : ℤ) a (o x) = 1) :
    P202Specs.UniversalCoefficients.evaluation R R
      (ordinaryComplex R R (TopCat.of M)) (n : ℤ)
      (homologyMap (relativeToAbsolute R R (localPair M x)) (n : ℤ) a) z = 1 := by
  rw [localEvaluation R n x o z hz a]
  exact ha


open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.BundleOperationsData

universe u
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}

/-- Two normal mod-two orientations agree pointwise and therefore as records. -/
theorem modTwoNormalOrientationUnique (N : NormalBundle T S i) (d : ℕ)
    (a b : P202Specs.ThomClass.Orientation (ZMod 2) N d) : a = b := by
  have hgen : a.generator = b.generator := by
    funext p
    obtain ⟨r, hr⟩ := (a.generates p).2 (b.generator p)
    have hr0 : r ≠ 0 := by
      intro heq
      have hb0 : b.generator p = 0 := by simpa [heq] using hr.symm
      exact zero_ne_one ((b.generates p).1 (by simp [hb0]))
    have hr1 : r = 1 := Fin.eq_one_of_ne_zero r hr0
    simpa [hr1] using hr
  cases a
  cases b
  cases hgen
  rfl


open P202Specs.SpheresDisks

/-- The L2 unit sphere and the coordinate sum-of-squares sphere are the same geometric sphere. -/
def smoothSphereHomeomorph (n : ℕ) : sphere n ≃ₜ SmoothManifolds.SphereTorusData.Sphere n where
  toFun x := ⟨fun j => x.val j, by
    change ∑ j, (x.val j)^2 = 1
    rw [← EuclideanSpace.real_norm_sq_eq]
    have hx : ‖x.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    rw [hx]
    norm_num⟩
  invFun x := ⟨WithLp.toLp 2 x.val, by
    simp only [Metric.mem_sphere, dist_zero_right]
    have hsq : ‖(WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin (n+1)))‖^2 = 1 := by
      simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply, SmoothManifolds.SphereTorusData.squareSum] using x.property
    nlinarith [norm_nonneg (WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin (n+1)))]⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact ((PiLp.homeomorph 2 (fun _ : Fin (n+1) => ℝ)).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact ((PiLp.homeomorph 2 (fun _ : Fin (n+1) => ℝ)).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

/-- The original antipodal quotient is homeomorphic to the P104 ratio-chart quotient. -/
def smoothProjectiveHomeomorph (n : ℕ) :
    Space n ≃ₜ SmoothManifolds.ProjectiveData.RealProjectiveSpace n :=
  Homeomorph.Quotient.congr (smoothSphereHomeomorph n) (by
    intro x y
    constructor
    · rintro (h | h)
      · apply Or.inl
        apply Subtype.ext
        funext j
        exact congrArg (fun v : EuclideanSpace ℝ (Fin (n+1)) => v j) h
      · apply Or.inr
        apply Subtype.ext
        funext j
        exact congrArg (fun v : EuclideanSpace ℝ (Fin (n+1)) => v j) h
    · rintro (h | h)
      · apply Or.inl
        ext j
        exact congrArg (fun v : SmoothManifolds.SphereTorusData.Sphere n => v.val j) h
      · apply Or.inr
        ext j
        exact congrArg (fun v : SmoothManifolds.SphereTorusData.Sphere n => v.val j) h)

lemma smoothProjectiveHomeomorph_quotient (n : ℕ) (x : sphere n) :
    smoothProjectiveHomeomorph n (quotientMap n x) =
      SmoothManifolds.ProjectiveData.projectiveProjection (smoothSphereHomeomorph n x) := rfl
/-- The ratio charts on the original projective quotient. -/
def smoothProjectiveAtlas (n : ℕ) :=
  SmoothManifolds.MapData.transportAtlas (smoothProjectiveHomeomorph n).symm
    (SmoothManifolds.ProjectiveData.projectiveAtlas n)

/-- The actual real projective quotient with its standard ratio-chart smooth structure. -/
def smoothProjectiveManifold (n : ℕ) :
    SmoothManifolds.AtlasData.SmoothManifold n .euclidean (Space n) := by
  have hA : SmoothManifolds.AtlasData.IsContDiffAtlas (⊤ : ℕ∞) (smoothProjectiveAtlas n) :=
    SmoothManifolds.transportAtlas_isContDiffAtlas _ _ _
      (SmoothManifolds.Projective.projectiveAtlas_isContDiffAtlas n)
  exact {
    topologicalManifold := {
      hausdorff := (smoothProjectiveHomeomorph n).isEmbedding.t2Space
      secondCountable := (smoothProjectiveHomeomorph n).secondCountableTopology
      atlas := smoothProjectiveAtlas n
      covers := hA.1 }
    smoothStructure := ⟨_, SmoothManifolds.maximalExtension_isMaximal hA⟩ }

lemma smoothProjectiveManifold_atlas (n : ℕ) :
    (smoothProjectiveManifold n).topologicalManifold.atlas = smoothProjectiveAtlas n := rfl



/-- The global evaluation follows from the actual relative-to-ordinary map
and the defining local values of the fundamental class. -/
def powerEvaluationOfLocal (μ : NaturalCohomologyRing (ZMod 2)) (m n : ℕ) (hn : n ≤ m)
    (u : H (ZMod 2) (projective m) 1) (F : FundamentalData n)
    (a : relativeCohomology (ZMod 2) (ZMod 2)
      (localPair (Space n) (coordinatePoint n)) (n : ℤ))
    (hgen : Function.Bijective (fun r : ZMod 2 => r • a))
    (heval : P202Specs.UniversalCoefficients.evaluation (ZMod 2) (ZMod 2)
      (ordinary (ZMod 2) (ZMod 2) (localPair (Space n) (coordinatePoint n))) (n : ℤ)
      a (F.orientation.val (coordinatePoint n)) = 1)
    (himage : P202Specs.RelativeCupProduct.forget (ZMod 2) _ n a =
      hPullback (ZMod 2) (standardInclusion n m hn) n (cupPower (μ.ring (projective m)) u n)) :
    PowerEvaluation μ m n hn u where
  fundamental := F
  localClass := a
  local_generator := hgen
  local_evaluation := heval
  ordinary_image := himage
  global_evaluation := by
    rw [← himage]
    exact localEvaluation_one (ZMod 2) n (coordinatePoint n) F.orientation.val
      F.fundamental F.local_values a heval

/-- Final assembly leaves only construction of the genuine hyperplane Thom
class and its normalized local restrictions; the additive ranks are proved here. -/
theorem geometricAssembly : Expected.geometricAssembly := by
  intro μ m G heval
  obtain ⟨P, hP⟩ := presentationFromEvaluations (m+1) μ G.ordinaryClass
    (fun n hn => ⟨(heval n hn).fundamental.fundamental, (heval n hn).global_evaluation⟩)
  exact ⟨{ geometry := G, presentation := P, powers_eq := hP, evaluations := heval }⟩


lemma perfectEvaluationOfGenerators (P : Pair) (n : ℤ)
    (a : relativeCohomology (ZMod 2) (ZMod 2) P n)
    (o : relativeHomology (ZMod 2) (ZMod 2) P n)
    (ha : Function.Bijective (fun r : ZMod 2 => r • a))
    (ho : Function.Bijective (fun r : ZMod 2 => r • o)) :
    P202Specs.UniversalCoefficients.evaluation (ZMod 2) (ZMod 2)
      (ordinary (ZMod 2) (ZMod 2) P) n a o = 1 := by
  let ev := P202Specs.UniversalCoefficients.evaluation (ZMod 2) (ZMod 2)
    (ordinary (ZMod 2) (ZMod 2) P) n
  have hne : ev a o ≠ 0 := by
    intro hz
    have hea : ev a = ev 0 := by
      apply LinearMap.ext
      intro z
      obtain ⟨r, rfl⟩ := ho.surjective z
      calc
        (ev a) (r • o) = r • (ev a) o := (ev a).map_smul r o
        _ = 0 := (congrArg (fun s : ZMod 2 => r • s) hz).trans (smul_zero r)
        _ = (ev 0) (r • o) :=
          (congrArg (fun f : relativeHomology (ZMod 2) (ZMod 2) P n →ₗ[ZMod 2] ZMod 2 =>
            f (r • o)) ev.map_zero).symm
    have ha0 : a = 0 := (P202.UniversalCoefficients.evaluation_bijective (ZMod 2)
      (ordinary (ZMod 2) (ZMod 2) P) n).injective hea
    have h01 : (0 : ZMod 2) = 1 := ha.injective (by simp [ha0])
    exact zero_ne_one h01
  have hvlt := (ev a o).val_lt
  have hvne : (ev a o).val ≠ 0 := by
    intro hz
    exact hne ((ZMod.val_eq_zero _).mp hz)
  have hv : (ev a o).val = 1 := by omega
  change ev a o = 1
  apply (ZMod.val_injective 2)
  change (ev a o).val = 1
  exact hv

lemma normalizedRelativeClass (P : Pair) (n : ℤ)
    (o : relativeHomology (ZMod 2) (ZMod 2) P n)
    (ho : Function.Bijective (fun r : ZMod 2 => r • o)) :
    ∃ a : relativeCohomology (ZMod 2) (ZMod 2) P n,
      Function.Bijective (fun r : ZMod 2 => r • a) ∧
      P202Specs.UniversalCoefficients.evaluation (ZMod 2) (ZMod 2)
        (ordinary (ZMod 2) (ZMod 2) P) n a o = 1 := by
  let hE : relativeHomology (ZMod 2) (ZMod 2) P n ≃ₗ[ZMod 2] ZMod 2 :=
    (LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton (ZMod 2) _ o) ho).symm
  let eD : (relativeHomology (ZMod 2) (ZMod 2) P n →ₗ[ZMod 2] ZMod 2) ≃ₗ[ZMod 2] ZMod 2 :=
    (LinearEquiv.arrowCongr hE (LinearEquiv.refl (ZMod 2) (ZMod 2))).trans
      (LinearMap.ringLmapEquivSelf (ZMod 2) (ZMod 2) (ZMod 2))
  let eC : relativeCohomology (ZMod 2) (ZMod 2) P n ≃ₗ[ZMod 2]
      (relativeHomology (ZMod 2) (ZMod 2) P n →ₗ[ZMod 2] ZMod 2) :=
    LinearEquiv.ofBijective
      (P202Specs.UniversalCoefficients.evaluation (ZMod 2) (ZMod 2)
        (ordinary (ZMod 2) (ZMod 2) P) n)
      (P202.UniversalCoefficients.evaluation_bijective (ZMod 2)
        (ordinary (ZMod 2) (ZMod 2) P) n)
  let E := eC.trans eD
  let a := E.symm 1
  have ha : Function.Bijective (fun r : ZMod 2 => r • a) := by
    have he : (fun r : ZMod 2 => r • a) = fun r => E.symm r := by
      funext r
      exact (E.symm.map_smul r 1).symm.trans (congrArg E.symm (mul_one r))
    rw [he]
    exact E.symm.bijective
  exact ⟨a, ha, perfectEvaluationOfGenerators P n a o ha ho⟩



lemma fundamentalData_nonempty (n : ℕ) : Nonempty (FundamentalData n) := by
  let A : Manifold n (Space n) := forgetSmooth (smoothProjectiveManifold n)
  obtain ⟨o, ho, _⟩ := (P202.LocalOrientation.modTwoOrientation n (Space n) A).2
  let O : Orientation (ZMod 2) A := ⟨o, ho⟩
  obtain ⟨z, hz, _⟩ :=
    (P202.CompactOrientation.ordinaryFundamentalClass (ZMod 2) n (Space n) A O
      isCompact_univ).2
  exact ⟨{ manifold := A, orientation := O, fundamental := z, local_values := hz }⟩



theorem degreeZeroUnitGenerator (m : ℕ) (C : CohomologyRing (ZMod 2) (projective m)) :
    letI := C.gradedRing
    Function.Bijective (fun r : ZMod 2 => r • (GradedMonoid.GOne.one : H (ZMod 2) (projective m) 0)) := by
  letI := C.gradedRing
  let e := Classical.choice (cohomologyGroups m 0 (by omega))
  haveI : Nontrivial (H (ZMod 2) (projective m) 0) := e.toEquiv.nontrivial
  haveI : Nontrivial (HStar (ZMod 2) (projective m)) :=
    (DirectSum.of_injective (β := H (ZMod 2) (projective m)) 0).nontrivial
  apply generatorOfNonzero e
  intro h
  have h1 : (1 : HStar (ZMod 2) (projective m)) = 0 := by
    rw [← DirectSum.of_zero_one _]
    change DirectSum.of _ 0 GradedMonoid.GOne.one = 0
    rw [h, map_zero]
  exact one_ne_zero h1



theorem cohomologyTruncation (m : ℕ) (C : CohomologyRing (ZMod 2) (projective m))
    (u : H (ZMod 2) (projective m) 1) :
    letI := C.gradedRing
    ∀ n : ℕ, m < n → (DirectSum.of _ 1 u) ^ n = 0 := by
  letI := C.gradedRing
  intro n hn
  have hz := modTwoCohomologyAboveDimension m n hn (cupPower C u n)
  rw [cupPower_homogeneous, hz, map_zero]


open SmoothManifolds.MapClassData SmoothManifolds.AbstractTubularData

namespace ModTwoOrientation
open P202Specs.ThomClass P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.CellularChains
attribute [local instance] normalTopology
abbrev F := ZMod 2

lemma generatorUnique (V : Type*) [AddCommGroup V] [Module F V] (a b : V)
    (ha : Function.Bijective (fun r : F => r • a))
    (hb : Function.Bijective (fun r : F => r • b)) : a = b :=
  modTwoGeneratorUnique V a b ha hb

/-- Both actual rank-zero model pairs are singletons with empty complement. -/
def modelZeroDiskIso : modelPair.{u} 0 ≅ referenceDiskPair.{u} 0 where
  hom := {
    map := TopCat.ofHom ⟨fun _ => ULift.up ⟨0, by simp⟩, continuous_const⟩
    mapsTo := by
      intro z hz
      exact (hz (Subsingleton.elim _ _)).elim }
  inv := {
    map := TopCat.ofHom ⟨fun _ => ULift.up 0, continuous_const⟩
    mapsTo := by
      intro z hz
      change ‖z.down.val‖ = 1 at hz
      have hz0 : z.down.val = 0 := Subsingleton.elim _ _
      rw [hz0, norm_zero] at hz
      norm_num at hz }
  hom_inv_id := by
    apply PairMap.ext
    apply TopCat.hom_ext
    ext z
    apply ULift.ext
    exact Subsingleton.elim _ _
  inv_hom_id := by
    apply PairMap.ext
    apply TopCat.hom_ext
    ext z
    apply ULift.ext
    apply Subtype.ext
    exact Subsingleton.elim _ _

def modelHomologyCoordinate (d : ℕ) :
    relativeHomology F F (modelPair.{u} d) (d : ℤ) ≃ₗ[F] F := by
  cases d with
  | zero =>
    let e := (relativeHomologyFunctor F F 0).mapIso modelZeroDiskIso
    exact e.toLinearEquiv.trans (Classical.choice
      ((P202.Homology.DiskBridge.referenceDiskHomology F F 0 0).1 rfl))
  | succ k =>
    exact (P202.ThomClass.modelHomologySelfIso F k).toLinearEquiv.trans ULift.moduleEquiv

def modelCohomologyCoordinate (d : ℕ) :
    relativeCohomology F F (modelPair.{u} d) (d : ℤ) ≃ₗ[F] F := by
  let e := LinearEquiv.ofBijective
    (P202Specs.UniversalCoefficients.evaluation F F
      (ordinary F F (modelPair.{u} d)) (d : ℤ))
    (P202.UniversalCoefficients.evaluation_bijective F
      (ordinary F F (modelPair.{u} d)) (d : ℤ))
  exact e.trans ((LinearEquiv.arrowCongr (modelHomologyCoordinate d)
    (LinearEquiv.refl F F)).trans (LinearMap.ringLmapEquivSelf F F F))

variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}

def chartCohomologyEquiv (N : NormalBundle T S i)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a) :
    relativeCohomology F F (modelPair.{u} (n-m)) ((n-m : ℕ) : ℤ) ≃ₗ[F]
      relativeCohomology F F (fiberPair N p) ((n-m : ℕ) : ℤ) :=
  ((relativeCohomologyFunctor F F ((n-m : ℕ) : ℤ)).mapIso
    (P202.ThomClass.fiberCoordinatesIso N a p hp).op).toLinearEquiv

/-- The unique rank generator of a real normal fiber over F₂. -/
def fiberGenerator (N : NormalBundle T S i) (p : P) :
    relativeCohomology F F (fiberPair N p) ((n-m : ℕ) : ℤ) :=
  let a := Classical.choose ((normalBundle N).covers p)
  let hp := Classical.choose_spec ((normalBundle N).covers p)
  chartCohomologyEquiv N a p hp ((modelCohomologyCoordinate (n-m)).symm 1)

lemma modelGenerator_generates (d : ℕ) :
    Function.Bijective (fun r : F => r • (modelCohomologyCoordinate.{u} d).symm 1) := by
  have hfun : (fun r : F => r • (modelCohomologyCoordinate.{u} d).symm 1) =
      (modelCohomologyCoordinate.{u} d).symm := by
    funext r
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [hfun]
  exact (modelCohomologyCoordinate.{u} d).symm.bijective

lemma chartGenerator_generates (N : NormalBundle T S i)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a) :
    Function.Bijective (fun r : F => r •
      chartCohomologyEquiv N a p hp ((modelCohomologyCoordinate (n-m)).symm 1)) := by
  have hfun : (fun r : F => r •
      chartCohomologyEquiv N a p hp ((modelCohomologyCoordinate (n-m)).symm 1)) =
      (chartCohomologyEquiv N a p hp) ∘
      (fun r : F => r • (modelCohomologyCoordinate (n-m)).symm 1) := by
    funext r
    exact (map_smul _ _ _).symm
  rw [hfun]
  exact (chartCohomologyEquiv N a p hp).bijective.comp (modelGenerator_generates (n-m))

lemma fiberGenerator_generates (N : NormalBundle T S i) (p : P) :
    Function.Bijective (fun r : F => r • fiberGenerator N p) :=
  chartGenerator_generates N _ _ _

lemma chartGenerator_eq (N : NormalBundle T S i)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a) :
    (relativeCohomologyFunctor F F ((n-m : ℕ) : ℤ)).map
      (fiberCoordinates N a p hp).op ((modelCohomologyCoordinate (n-m)).symm 1) =
        fiberGenerator N p := by
  apply generatorUnique
  · exact chartGenerator_generates N a p hp
  · exact fiberGenerator_generates N p

/-- Canonical mod-two normal orientation: every original linear chart gives
its same unique nonzero fiber generator, so all local compatibility is automatic. -/
def orientation (N : NormalBundle T S i) : Orientation F N (n-m) where
  generator := fiberGenerator N
  generates := fiberGenerator_generates N
  locally_constant := by
    intro p
    obtain ⟨a, hp⟩ := (normalBundle N).covers p
    refine ⟨a, (normalBundle N).baseSet a, ?_, hp, fun _ h => h,
      (modelCohomologyCoordinate (n-m)).symm 1, ?_⟩
    · rw [← (normalBundle N).trivialization_baseSet a]
      exact ((normalBundle N).trivialization a).open_baseSet
    · intro q hq
      exact chartGenerator_eq N a q hq


lemma orientation_unique (N : NormalBundle T S i) (d : ℕ)
    (o o' : Orientation F N d) : o = o' := by
  have hgen : o.generator = o'.generator := by
    funext p
    exact generatorUnique _ _ _ (o.generates p) (o'.generates p)
  cases o
  cases o'
  cases hgen
  rfl

/-- This form preserves the original theorem's vacuous rank condition on an
empty embedded manifold, allowing every declared orientation degree there. -/
def orientationWithRank (N : NormalBundle T S i) (d : ℕ)
    (hrank : ∀ _ : P, d = n-m) : Orientation F N d := by
  classical
  by_cases hP : Nonempty P
  · have hd := hrank (Classical.choice hP)
    subst d
    exact orientation N
  · haveI : IsEmpty P := not_nonempty_iff.mp hP
    exact {
      generator := fun p => isEmptyElim p
      generates := fun p => isEmptyElim p
      locally_constant := fun p => isEmptyElim p }

end ModTwoOrientation


open P202.Homology.RealProjectiveHomology in
lemma standardHyperplane_quotient_mem (n : ℕ) (x : sphere (n+1)) :
    quotientMap (n+1) x ∈ Set.range (standardInclusion n (n+1) (by omega)) ↔
      x.val (Fin.last (n+1)) = 0 := by
  rw [standardInclusion_eq]
  constructor
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with | _ y =>
      have hq' : quotientMap (n+1) (sphereInclusion n (n+1) (by omega) y) =
          quotientMap (n+1) x := hq
      rcases Quotient.exact hq' with heq | heq
      · have hh := congrArg (fun v : EuclideanSpace ℝ (Fin (n+2)) => v (Fin.last (n+1))) heq
        have hz := coordinateInclusion_apply_high n (n+1) (by omega) y.val
          (Fin.last (n+1)) (by simp)
        exact (hz.symm.trans hh).symm
      · have hh := congrArg (fun v : EuclideanSpace ℝ (Fin (n+2)) => v (Fin.last (n+1))) heq
        have hz := coordinateInclusion_apply_high n (n+1) (by omega) y.val
          (Fin.last (n+1)) (by simp)
        change coordinateInclusion n (n+1) _ y.val (Fin.last (n+1)) = -x.val (Fin.last (n+1)) at hh
        rw [hz] at hh
        linarith
  · intro hx
    let v : EuclideanSpace ℝ (Fin (n+1)) := WithLp.toLp 2 (fun j => x.val j.castSucc)
    have hnorm : ‖v‖ = 1 := by
      have hsq : ‖v‖ ^ 2 = 1 := by
        have heq : ‖x.val‖ ^ 2 = 1 := by
          have hxnorm : ‖x.val‖ = 1 := by
            simpa only [Metric.mem_sphere, dist_zero_right] using x.property
          rw [hxnorm]
          norm_num
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc, hx] at heq
        simpa [EuclideanSpace.real_norm_sq_eq, v] using heq
      nlinarith [norm_nonneg v]
    let y : sphere n := ⟨v, by simpa only [Metric.mem_sphere, dist_zero_right] using hnorm⟩
    refine ⟨quotientMap n y, ?_⟩
    change quotientMap (n+1) (sphereInclusion n (n+1) (by omega) y) = quotientMap (n+1) x
    congr 1
    apply Subtype.ext
    ext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · have hidx : Fin.castLE (Nat.succ_le_succ (show n ≤ n+1 by omega)) k = k.castSucc := Fin.ext rfl
      simpa only [hidx, sphereInclusion, ContinuousMap.coe_mk, y, v, PiLp.toLp_apply] using
        coordinateInclusion_apply n (n+1) (by omega) v k
    · simpa only [sphereInclusion, ContinuousMap.coe_mk, hx] using
        coordinateInclusion_apply_high n (n+1) (by omega) v (Fin.last (n+1)) (by simp)


end P202.Cohomology.RealProjectiveRing

namespace P202.Cohomology.RealProjectiveGeometry
open SmoothManifolds hiding Sphere Euclidean SmoothManifold RealProjectiveSpace
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.SphereTorusData
  SmoothManifolds.ProjectiveData SmoothManifolds.SliceData
open Set

/-- Last-coordinate hyperplane in the literal sum-of-squares antipodal quotient. -/
def hyperplaneSet (n : ℕ) : Set (RealProjectiveSpace (n+1)) :=
  projectiveProjection '' {x : Sphere (n+1) | x.val (Fin.last (n+1)) = 0}

lemma projection_mem_hyperplaneSet (n : ℕ) (x : Sphere (n+1)) :
    projectiveProjection x ∈ hyperplaneSet n ↔ x.val (Fin.last (n+1)) = 0 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (Projective.projection_fiber y x).mp hxy with rfl | h
    · exact hy
    · have hh := congrArg (fun z : Sphere (n+1) => z.val (Fin.last (n+1))) h
      change y.val (Fin.last (n+1)) = -x.val (Fin.last (n+1)) at hh
      rw [hy] at hh
      linarith
  · exact fun h => ⟨x, h, rfl⟩

lemma coordinateSlice_hyperplane (n : ℕ) (v : Euclidean (n+1)) :
    v ∈ coordinateSlice n (n+1) .euclidean ↔ v (Fin.last n) = 0 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp [sliceEmbedding]
  · intro hv
    refine ⟨fun j => v j.castSucc, Set.mem_univ _, ?_⟩
    funext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · simp [sliceEmbedding, k.is_lt]
    · simp [sliceEmbedding, hv]

lemma hyperplane_ratioChart_slice (n : ℕ) (i : Fin (n+1)) :
    IsSliceChart (hyperplaneSet n) n .euclidean (Projective.projectiveChart i.castSucc) := by
  refine ⟨by omega, by simp, ?_⟩
  ext y
  constructor
  · rintro ⟨p, ⟨hp, hpi⟩, rfl⟩
    refine ⟨Set.mem_univ _, (coordinateSlice_hyperplane n _).2 ?_⟩
    obtain ⟨x, hx, rfl⟩ := hp
    change x.val (i.castSucc.succAbove (Fin.last n)) / x.val i.castSucc = 0
    rw [Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i), hx, zero_div]
  · rintro ⟨hy, hslice⟩
    have hlast : y.val (Fin.last n) = 0 := (coordinateSlice_hyperplane n _).1 hslice
    refine ⟨projectiveInverse i.castSucc y.val, ⟨?_, Projective.inverse_mem_locus _ _⟩, ?_⟩
    · apply (projection_mem_hyperplaneSet n _).2
      change insertOne i.castSucc y.val (Fin.last (n+1)) /
        Real.sqrt (1 + squareSum y.val) = 0
      rw [← Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i)]
      simp only [insertOne, Fin.insertNth_apply_succAbove, hlast, zero_div]
    · exact Subtype.ext (Projective.ratios_inverse _ _)

lemma hyperplane_hasSliceCharts (n : ℕ) :
    HasSliceCharts (Projective.projectiveManifold (n+1)) (hyperplaneSet n) n .euclidean := by
  refine ⟨by omega, ?_⟩
  intro p hp
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨j, hj⟩ := Projective.locus_cover (projectiveProjection x)
  have hjx : x.val j ≠ 0 := (Projective.projection_mem_locus j x).1 hj
  have hjlast : j ≠ Fin.last (n+1) := by
    intro h
    exact hjx (h ▸ hx)
  obtain ⟨i, rfl⟩ := j.eq_castSucc_of_ne_last hjlast
  refine ⟨.euclidean, Or.inl rfl, Projective.projectiveChart i.castSucc, ?_, hj,
    hyperplane_ratioChart_slice n i⟩
  have hc : Projective.projectiveChart i.castSucc ∈
      (Projective.projectiveManifold (n+1)).smoothStructure.val :=
    subset_maximalExtension (Projective.projectiveAtlas_isContDiffAtlas (n+1))
      ⟨i.castSucc, Projective.projectiveChart_spec i.castSucc⟩
  intro e he p hp hpe
  exact ⟨chartContDiffAt_of_compatible
    ((Projective.projectiveManifold (n+1)).smoothStructure.property.1.2 _ hc e he) hp hpe,
    chartContDiffAt_of_compatible
    ((Projective.projectiveManifold (n+1)).smoothStructure.property.1.2 e he _ hc) hpe hp⟩

/-- An actual smooth hyperplane source with precisely the target subspace topology. -/
theorem hyperplane_embeddedSubmanifold (n : ℕ) :
    ∃ S : SmoothManifold n .euclidean (hyperplaneSet n),
      SmoothManifolds.MapClassData.IsSmoothEmbedding S
        (Projective.projectiveManifold (n+1)) Subtype.val := by
  obtain ⟨S, hS, _⟩ := SliceStructures.exists_slice_manifold
    (Projective.projectiveManifold (n+1)) (hyperplaneSet n) (hyperplane_hasSliceCharts n)
  exact ⟨S, hS⟩

end P202.Cohomology.RealProjectiveGeometry

namespace P202.Cohomology.RealProjectiveGeometry
open P202.Cohomology.RealProjectiveRing P202Specs.RealProjectiveRing P202Specs.RealProjectiveHomology P202Specs.SpheresDisks
open SmoothManifolds hiding Sphere Euclidean SmoothManifold RealProjectiveSpace Diffeomorph
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.MapClassData SmoothManifolds.TangentData SmoothManifolds.DifferentialData

lemma standardHyperplane_range_smooth (n : ℕ) :
    Set.range (fun q => smoothProjectiveHomeomorph (n+1)
      (standardInclusion n (n+1) (by omega) q)) = hyperplaneSet n := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    have hq : standardInclusion n (n+1) (by omega) q ∈
        Set.range (standardInclusion n (n+1) (by omega)) := ⟨q, rfl⟩
    change smoothProjectiveHomeomorph (n+1) (standardInclusion n (n+1) (by omega) q) ∈ hyperplaneSet n
    generalize standardInclusion n (n+1) (by omega) q = z at *
    induction z using Quotient.inductionOn with | _ x =>
      change SmoothManifolds.ProjectiveData.projectiveProjection
        (smoothSphereHomeomorph (n+1) x) ∈ hyperplaneSet n
      exact (projection_mem_hyperplaneSet n (smoothSphereHomeomorph (n+1) x)).2
        ((standardHyperplane_quotient_mem n x).1 hq)
  · rintro ⟨x, hx, rfl⟩
    let y := (smoothSphereHomeomorph (n+1)).symm x
    have hy : y.val (Fin.last (n+1)) = 0 := hx
    obtain ⟨q, hq⟩ := (standardHyperplane_quotient_mem n y).2 hy
    refine ⟨q, ?_⟩
    change smoothProjectiveHomeomorph (n+1) (standardInclusion n (n+1) (by omega) q) = _
    rw [hq]
    rfl

/-- Source projective space is homeomorphic to the actual smooth coordinate hyperplane. -/
def standardHyperplaneHomeomorph (n : ℕ) : Space n ≃ₜ hyperplaneSet n := by
  let e := smoothProjectiveHomeomorph (n+1)
  letI : T2Space (Space (n+1)) := e.isEmbedding.t2Space
  have hf := P202.Homology.RealProjectiveHomology.projectiveInclusion_closedEmbedding
    n (n+1) (by omega)
  have hf' : _root_.Topology.IsEmbedding (standardInclusion n (n+1) (by omega)) := by
    rw [standardInclusion_eq]
    exact hf.isEmbedding
  exact (e.isEmbedding.comp hf').toHomeomorph.trans
    (Homeomorph.setCongr (standardHyperplane_range_smooth n))

lemma standardHyperplaneHomeomorph_val (n : ℕ) (q : Space n) :
    (standardHyperplaneHomeomorph n q).val = smoothProjectiveHomeomorph (n+1)
      (standardInclusion n (n+1) (by omega) q) := rfl

/-- A diffeomorphism is a smooth embedding in the actual quotient tangent convention. -/
lemma diffeomorph_isSmoothEmbedding {k l : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold k .euclidean X) (T : SmoothManifold l .euclidean Y)
    (d : Diffeomorph S.smoothStructure.val T.smoothStructure.val) :
    IsSmoothEmbedding S T d.toEquiv := by
  refine ⟨d.contDiff_toFun, d.toEquiv.injective, ?_, ?_⟩
  · intro p
    obtain ⟨D, hD⟩ := differential_diffeomorph S T d p
    exact (MapClasses.smooth_tangent_invariants S T d.toEquiv d.contDiff_toFun
      p D.toLinearMap hD).2.1.mpr D.injective
  · exact ⟨d.toHomeomorph.isEmbedding.toHomeomorph, fun _ => rfl⟩

/-- Standard hyperplane inclusion on the original antipodal quotients is a smooth embedding. -/
theorem exists_standardHyperplane_smoothEmbedding (n : ℕ) :
    ∃ (S : SmoothManifold n .euclidean (Space n))
      (T : SmoothManifold (n+1) .euclidean (Space (n+1))),
      IsSmoothEmbedding S T (standardInclusion n (n+1) (by omega)) := by
  obtain ⟨A, hA⟩ := hyperplane_embeddedSubmanifold n
  let B := Projective.projectiveManifold (n+1)
  obtain ⟨S, hS, _⟩ := TransversePreimage.transport_embedded A B Subtype.val hA
    (standardHyperplaneHomeomorph n).symm
  obtain ⟨T, d, hd⟩ := TransversePreimage.exists_manifold_diffeomorph B
    (smoothProjectiveHomeomorph (n+1)).symm
  have hdembed := diffeomorph_isSmoothEmbedding B T d
  have hcomp := TransversePreimage.smoothEmbedding_comp S B T
    (Subtype.val ∘ (standardHyperplaneHomeomorph n).symm.symm) d.toEquiv hS hdembed
  have heq : d.toEquiv ∘ (Subtype.val ∘ (standardHyperplaneHomeomorph n).symm.symm) =
      standardInclusion n (n+1) (by omega) := by
    funext q
    change d.toEquiv (standardHyperplaneHomeomorph n q).val = _
    rw [hd, standardHyperplaneHomeomorph_val]
    exact (smoothProjectiveHomeomorph (n+1)).symm_apply_apply _
  exact ⟨S, T, heq ▸ hcomp⟩

end P202.Cohomology.RealProjectiveGeometry

namespace P202.Cohomology.RealProjectiveRing
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem fundamentalClasses : P202Specs.RealProjectiveRing.Expected.fundamentalClasses := by
  intro n
  exact fundamentalData_nonempty n

open P202Specs.RealProjectiveRing P202Specs.RealProjectiveHomology
open P202Specs.LocalOrientation P202Specs.CohomologyPairs P202Specs.RelativeSingularChains

lemma fundamentalLocalClass (n : ℕ) (F : FundamentalData n) (x : Space n) :
    ∃ a : relativeCohomology (ZMod 2) (ZMod 2) (localPair (Space n) x) (n : ℤ),
      Function.Bijective (fun r : ZMod 2 => r • a) ∧
      P202Specs.UniversalCoefficients.evaluation (ZMod 2) (ZMod 2)
        (ordinary (ZMod 2) (ZMod 2) (localPair (Space n) x)) (n : ℤ) a
        (F.orientation.val x) = 1 ∧
      kronecker (projective n) n
        (P202Specs.RelativeCupProduct.forget (ZMod 2) (localPair (Space n) x) n a)
        F.fundamental = 1 := by
  obtain ⟨a, ha, hev⟩ := normalizedRelativeClass (localPair (Space n) x) (n : ℤ)
    (F.orientation.val x) (F.orientation.property.1 x)
  refine ⟨a, ha, hev, ?_⟩
  exact localEvaluation_one (ZMod 2) n x F.orientation.val F.fundamental F.local_values a hev


theorem normalizedLocalClasses : P202Specs.RealProjectiveRing.Expected.normalizedLocalClasses := by
  intro n F
  exact fundamentalLocalClass n F (P202Specs.RealProjectiveRing.coordinatePoint n)

open P202Specs.RealProjectiveRing P202Specs.RealProjectiveHomology
open SmoothManifolds.AtlasData SmoothManifolds.BundleOperationsData

theorem hyperplaneGeometry : Expected.hyperplaneGeometry := by
  intro n
  obtain ⟨S, T, hemb⟩ :=
    P202.Cohomology.RealProjectiveGeometry.exists_standardHyperplane_smoothEmbedding n
  obtain ⟨N⟩ := SmoothManifolds.BundleOperations.exists_normal S T
    (standardInclusion n (n+1) (by omega)) hemb
  let hrank : ∀ _ : Space n, 1 = (n+1)-n := fun _ => by omega
  let o := ModTwoOrientation.orientationWithRank N 1 hrank
  obtain ⟨htube, c, hc, _⟩ := P202.ThomClass.exists_unique (ZMod 2) n (n+1) 1
    (Space n) (Space (n+1)) S T (standardInclusion n (n+1) (by omega)) hemb N hrank o
  exact ⟨{ source := S
           ambient := T
           embedding := hemb
           normal := N
           orientation := o
           tube := htube
           thom := c
           fiber_values := hc }⟩


open P202Specs.CohomologyPairs

theorem hyperplaneThomNonzero (n : ℕ) (G : HyperplaneGeometry n) : G.thom ≠ 0 := by
  obtain ⟨K, hK⟩ := G.tube
  let p := coordinatePoint n
  let f := (relativeCohomologyFunctor (ZMod 2) (ZMod 2) 1).map
    (P202Specs.ThomClass.sliceToFiber G.normal K p).op
  haveI : IsIso f := P202.ThomClass.sliceToFiber_isIso G.normal K p (ZMod 2) 1
  have h := G.fiber_values K hK p
  intro hc
  rw [hc, map_zero] at h
  have hz : G.orientation.generator p = 0 :=
    (ConcreteCategory.bijective_of_isIso f).injective
      (h.symm.trans (map_zero f.hom).symm)
  exact zero_ne_one ((G.orientation.generates p).injective (by simp [hz]))


namespace HyperplaneOrdinary
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.ProjectiveData SmoothManifolds.SphereTorusData
open P202Specs.RealProjectiveRing P202Specs.RealProjectiveHomology
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
open P202Specs.SingularChains P202Specs.ThomClass P202Specs.ChainLES
open P202.Cohomology.RealProjectiveRing P202.Cohomology.RealProjectiveGeometry
abbrev F := ZMod 2

lemma hyperplane_compl_eq_locus (n : ℕ) :
    (hyperplaneSet n)ᶜ = projectiveLocus (Fin.last (n+1)) := by
  ext p
  induction p using Quotient.inductionOn with | _ x =>
    change (¬ projectiveProjection x ∈ hyperplaneSet n) ↔
      projectiveProjection x ∈ projectiveLocus (Fin.last (n+1))
    rw [projection_mem_hyperplaneSet, SmoothManifolds.Projective.projection_mem_locus]

def hyperplaneComplementHomeomorph (n : ℕ) :
    (ambientPair (standardInclusion n (n+1) (by omega))).sub ≃ₜ Euclidean (n+1) := by
  let e := smoothProjectiveHomeomorph (n+1)
  let c := SmoothManifolds.Projective.projectiveChart (Fin.last (n+1))
  have hmem (x : Space (n+1)) :
      x ∉ Set.range (standardInclusion n (n+1) (by omega)) ↔
        e x ∈ projectiveLocus (Fin.last (n+1)) := by
    rw [← hyperplane_compl_eq_locus]
    change ¬ x ∈ _ ↔ ¬ e x ∈ _
    apply not_congr
    rw [← standardHyperplane_range_smooth n]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, rfl⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, e.injective hq⟩
  exact (e.subtype hmem).trans (c.toHomeomorphSourceTarget.trans
    ((Homeomorph.Set.univ _).trans (Homeomorph.Set.univ _)))

instance complement_contractible (n : ℕ) :
    ContractibleSpace (ambientPair (standardInclusion n (n+1) (by omega))).sub :=
  (hyperplaneComplementHomeomorph n).contractibleSpace

lemma restriction_surjective_of_contractible
    (R : Type*) [CommRing R] (A : Type*) [AddCommGroup A] [Module R A]
    (P : Pair) [ContractibleSpace P.sub] (q : ℤ) :
    Function.Surjective (homologyMap (restriction R A P) q) := by
  obtain ⟨p, ⟨H⟩⟩ := id_nullhomotopic P.sub
  let r : P.space ⟶ P.sub := TopCat.ofHom (ContinuousMap.const _ p)
  let F := ordinaryCohomologyFunctor R A q
  have hH : F.map (𝟙 P.sub).op = F.map (P.inclusion ≫ r).op :=
    (P202.CohomologyPairs.homotopy_invariant R A).1 H q
  have hid : F.map r.op ≫ F.map P.inclusion.op = 𝟙 (F.obj (op P.sub)) := by
    rw [← F.map_comp, ← op_comp, ← hH]
    simp
  intro b
  refine ⟨F.map r.op b, ?_⟩
  have hb := congrArg (fun f => f b) hid
  exact hb

lemma forget_one_injective_of_contractible
    (R : Type*) [CommRing R] (A : Type*) [AddCommGroup A] [Module R A]
    (P : Pair) [ContractibleSpace P.sub] :
    Function.Injective (homologyMap (relativeToAbsolute R A P) 1) := by
  let S := cochainSequence R A P
  let hS := HomologicalComplex.shortExact_of_degreewise_shortExact S
    (P202.CohomologyPairs.short_exact R A P)
  haveI : Epi (homologyMap S.g 0) := (ModuleCat.epi_iff_surjective _).mpr
    (restriction_surjective_of_contractible R A P 0)
  have hδ : hS.δ 0 1 (by simp) = 0 := by
    apply (cancel_epi (homologyMap S.g 0)).mp
    simp
  haveI : Mono (homologyMap S.f 1) := (hS.homology_exact₁ 0 1 (by simp)).mono_g hδ
  exact (ModuleCat.mono_iff_injective (homologyMap S.f 1)).mp inferInstance

lemma hyperplane_forget_injective (n : ℕ) :
    Function.Injective (P202Specs.RelativeCupProduct.forget F
      (ambientPair (standardInclusion n (n+1) (by omega))) 1) :=
  forget_one_injective_of_contractible F F _


end HyperplaneOrdinary

/-- The relative hyperplane Thom generator survives in ordinary cohomology. -/
theorem hyperplaneOrdinaryNonzero (n : ℕ) (G : HyperplaneGeometry n) : G.ordinaryClass ≠ 0 := by
  intro h
  apply hyperplaneThomNonzero n G
  apply HyperplaneOrdinary.hyperplane_forget_injective n
  change G.ordinaryClass = P202Specs.RelativeCupProduct.forget (ZMod 2)
    (P202Specs.ThomClass.ambientPair (standardInclusion n (n+1) (by omega))) 1 0
  simpa only [map_zero] using h

/-- The requested degree-one generator is the ordinary hyperplane Thom image. -/
theorem hyperplaneGenerator : Expected.hyperplaneGenerator := by
  intro n G
  exact generatorOfNonzero (Classical.choice (cohomologyGroups (n+1) 1 (by omega)))
    G.ordinaryClass (hyperplaneOrdinaryNonzero n G)


end P202.Cohomology.RealProjectiveRing

namespace P202.Cohomology.RealProjectiveRing.TransverseSlices
open CategoryTheory Opposite
open SmoothManifolds.AtlasData
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
  P202Specs.RelativeCupProduct P202Specs.TransverseThomProduct
universe u w

variable {R : Type u} [CommRing R] {n k : ℕ} {M : TopCat.{w}}
  {S : SmoothManifold n .euclidean M}
  {F : Fin k → OrientedSubmanifold R M S}
  {x : M} {p : ∀ j, (F j).source} {h : ∀ j, (F j).inclusion (p j) = x}
  {b : ModelOrientationAt R F p}

/-- Restriction from all ordered normal blocks to any normalized slice domain is excisive. -/
theorem normalizedSlice_toBlocks_isIso
    (s : NormalizedIntersectionSlice R F x p h b)
    (B : SupportedClass R (normalBlockSpace R F))
    (hB : B.support = zeroBlockSupport R F) (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map (s.toBlocks B hB).op) := by
  cases B with
  | mk support hclosed degree value =>
    dsimp only at hB
    subst support
    change IsIso ((relativeCohomologyFunctor R R q).map
      (P202.ThomClass.openPairInclusion
        (⟨normalBlockSpace R F, {z | z.down ≠ 0}⟩ : Pair)
        {z | z.down ∈ s.domain}).op)
    apply P202.ThomClass.openPairInclusion_isIso
    · exact isOpen_ne_fun continuous_uliftDown continuous_const
    · exact s.domain_open.preimage continuous_uliftDown
    · intro z hz
      change ¬ z.down ≠ 0 at hz
      change z.down ∈ s.domain
      rw [Classical.not_not.mp hz]
      exact s.domain_zero

/-- Nonzero model product has a nonzero pullback to every centered slice domain. -/
theorem normalizedSlice_blockPullback_ne_zero [Nontrivial R]
    (s : NormalizedIntersectionSlice R F x p h b)
    (B : SupportedClass R (normalBlockSpace R F))
    (hB : B.support = zeroBlockSupport R F)
    (hgen : Function.Bijective (fun r : R => r • B.value)) :
    relativePullback R (s.toBlocks B hB) B.degree B.value ≠ 0 := by
  haveI := normalizedSlice_toBlocks_isIso s B hB (B.degree : ℤ)
  have hB0 : B.value ≠ 0 := by
    intro hzero
    exact zero_ne_one (hgen.injective (by simp [hzero]))
  intro hzero
  apply hB0
  exact (ConcreteCategory.bijective_of_isIso
    ((relativeCohomologyFunctor R R (B.degree : ℤ)).map
      (s.toBlocks B hB).op)).injective (by
        change relativePullback R (s.toBlocks B hB) B.degree B.value =
          relativePullback R (s.toBlocks B hB) B.degree 0
        simpa only [map_zero] using hzero)


end P202.Cohomology.RealProjectiveRing.TransverseSlices

namespace P202.Cohomology.RealProjectiveRing
/-- Independent coordinate hyperplane tangent spaces give simultaneous normal surjectivity. -/
theorem coordinateNormalQuotients_surjective
    {K V : Type*} [Ring K] [AddCommGroup V] [Module K V] {ι : Type*}
    (e : V ≃ₗ[K] (ι → K)) (W : ι → Submodule K V)
    (hW : ∀ j v, v ∈ W j ↔ e v j = 0) :
    Function.Surjective (fun v : V => fun j => (W j).mkQ v) := by
  intro q
  let v : ι → V := fun j => Quotient.out (q j)
  let z := e.symm (fun j => e (v j) j)
  refine ⟨z, ?_⟩
  funext j
  calc
    (W j).mkQ z = (W j).mkQ (v j) := by
      apply (Submodule.Quotient.eq (W j)).2
      apply (hW j (z - v j)).2
      simp [z]
    _ = q j := Submodule.Quotient.mk_out (q j)


end P202.Cohomology.RealProjectiveRing


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory HomologicalComplex
namespace P202.Cohomology.RealProjectiveRing.StandardRestriction
open P202Specs.RealProjectiveRing P202Specs.RealProjectiveHomology
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202.Cellular P202Specs.CellularChains
open P202.Homology.RealProjectiveHomology
open P202Specs.CupProduct
abbrev F := ZMod 2

/-- The fixed standard coordinate inclusion preserves every specified skeleton. -/
def cellularInclusion (n m : ℕ) (h : n ≤ m) :
    letI := standardCW n
    letI := standardCW m
    CellularMap (Space n) (Space m) := by
  letI := standardCW n
  letI := standardCW m
  refine ⟨projectiveInclusion n m h, ?_⟩
  intro j z hz
  simp only [skeletonLT, Set.mem_iUnion] at hz ⊢
  obtain ⟨k, hk, c, x, hx⟩ := hz
  refine ⟨k, hk, (⟨(), c.property.trans h⟩ : {i : Unit // k ≤ m}), x, ?_⟩
  change standardCharacteristic m k _ (P202.Cellular.interiorInclusion k x) = _
  rw [← hx]
  exact (projectiveInclusion_characteristic n m k h c.property _).symm

lemma characteristicPair_natural (n m q : ℕ) (h : n ≤ m) (hq : q ≤ n) :
    letI := standardCW n
    letI := standardCW m
    characteristicPairMap q (show Cell (Space n) q from ⟨(), hq⟩) ≫
      (cellularInclusion n m h).onPair q =
    characteristicPairMap q (show Cell (Space m) q from ⟨(), hq.trans h⟩) := by
  letI := standardCW n
  letI := standardCW m
  apply PairMap.ext
  ext x
  apply Subtype.ext
  change projectiveInclusion n m h (standardCharacteristic n q hq x.down) =
    standardCharacteristic m q (hq.trans h) x.down
  exact projectiveInclusion_characteristic n m q h hq x.down

/-- A sole characteristic cell induces an isomorphism on its relative disk group. -/
lemma characteristicPair_isIso (n q : ℕ) (hq : q ≤ n)
    (R : Type) [CommRing R] :
    letI := standardCW n
    IsIso ((relativeHomologyFunctor R R (q : ℤ)).map
      (characteristicPairMap q (show Cell (Space n) q from ⟨(), hq⟩))) := by
  classical
  letI := standardCW n
  let c : Cell (Space n) q := ⟨(), hq⟩
  haveI : Unique (Cell (Space n) q) := ⟨⟨c⟩, fun _ => Subtype.ext (Subsingleton.elim _ _)⟩
  obtain ⟨g⟩ := (P202.Homology.DiskBridge.referenceDiskHomology R R q q).1 rfl
  let e := P202.Homology.orientedCellEquiv (Space n) R R q g.symm
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have hc (a : R) :
      e ((relativeHomologyFunctor R R (q : ℤ)).map
        (characteristicPairMap q c) (g.symm a)) = Finsupp.single c a :=
    P202.Homology.orientedCellEquiv_characteristic (Space n) R R q g.symm c a
  constructor
  · intro a b hab
    have hh := congrArg e hab
    rw [← g.symm_apply_apply a, ← g.symm_apply_apply b, hc, hc] at hh
    exact g.injective (by simpa using congrArg (fun f => f c) hh)
  · intro z
    refine ⟨g.symm (e z c), e.injective ?_⟩
    rw [hc]
    apply Finsupp.ext
    intro d
    have hd : d = c := Subsingleton.elim _ _
    subst d
    simp

lemma cellularDegree_isIso (n m q : ℕ) (h : n ≤ m) (hq : q ≤ n)
    (R : Type) [CommRing R] :
    letI := standardCW n
    letI := standardCW m
    IsIso (cellularDegreeMap R R (cellularInclusion n m h) q) := by
  letI := standardCW n
  letI := standardCW m
  let H := relativeHomologyFunctor R R (q : ℤ)
  let c : referenceDiskPair.{0} q ⟶ skeletalPair (Space n) q :=
    characteristicPairMap q ⟨(), hq⟩
  haveI : IsIso (H.map c) := characteristicPair_isIso n q hq R
  haveI : IsIso (H.map c ≫ cellularDegreeMap R R (cellularInclusion n m h) q) := by
    change IsIso (H.map c ≫ H.map ((cellularInclusion n m h).onPair q))
    rw [← H.map_comp, characteristicPair_natural]
    exact characteristicPair_isIso m q (hq.trans h) R
  exact IsIso.of_isIso_comp_left (H.map c) _

end P202.Cohomology.RealProjectiveRing.StandardRestriction

namespace P202.Cohomology.RealProjectiveRing.StandardRestriction
open P202Specs.RealProjectiveRing P202Specs.RealProjectiveHomology
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202.Cellular P202Specs.CellularChains
open P202.Homology.RealProjectiveHomology
open P202Specs.CupProduct

lemma homologyMap_isIso_of_zero_differentials
    {R : Type} [CommRing R] {K L : ChainComplex (ModuleCat R) ℕ}
    (hK : ∀ j, K.d (j+1) j = 0) (hL : ∀ j, L.d (j+1) j = 0)
    (φ : K ⟶ L) (q : ℕ) [IsIso (φ.f q)] : IsIso (homologyMap φ q) := by
  have hf {J : ChainComplex (ModuleCat R) ℕ} (hJ : ∀ j, J.d (j+1) j = 0) :
      (J.sc q).f = 0 := by
    change J.d ((ComplexShape.down ℕ).prev q) q = 0
    rw [ChainComplex.prev]
    exact hJ q
  have hg {J : ChainComplex (ModuleCat R) ℕ} (hJ : ∀ j, J.d (j+1) j = 0) :
      (J.sc q).g = 0 := by
    change J.d q ((ComplexShape.down ℕ).next q) = 0
    cases q with
    | zero => rw [ChainComplex.next_nat_zero]; exact J.shape 0 0 (by decide)
    | succ j => rw [ChainComplex.next_nat_succ]; exact hJ j
  let ψ := (shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) q).map φ
  let γ := ShortComplex.LeftHomologyMapData.ofZeros ψ (hf hK) (hg hK) (hf hL) (hg hL)
  change IsIso (ShortComplex.homologyMap ψ)
  rw [γ.homologyMap_eq]
  change IsIso (_ ≫ φ.f q ≫ _)
  infer_instance

/-- Every standard coordinate inclusion induces the actual F₂ homology
isomorphism in all degrees through its source dimension, including the top. -/
lemma homology_isIso (n m q : ℕ) (h : n ≤ m) (hq : q ≤ n) :
    IsIso ((homologyFunctor F F (q : ℤ)).map (standardInclusion n m h)) := by
  letI := standardCW n
  letI := standardCW m
  let f := cellularInclusion n m h
  let φ := P202.Homology.cellularChainMap F F f
  have hd (a j : ℕ) : letI := standardCW a;
      (cellularComplex (Space a) F F).d (j+1) j = 0 := by
    letI := standardCW a
    simpa only [cellularComplex, ChainComplex.of, ChainComplex.of_d] using
      ModTwoGroups.differential_zero a j
  haveI : IsIso (φ.f q) := cellularDegree_isIso n m q h hq F
  haveI := homologyMap_isIso_of_zero_differentials (hd n) (hd m) φ q
  have hn := P202.Homology.CellularComparison.comparisonIso_natural F F f φ
    (fun _ => rfl) q
  have hnat :
      (homologyFunctor F F (q : ℤ)).map (standardInclusion n m h) =
      (P202.Homology.CellularComparison.comparisonIso (Space n) F F q).inv ≫
      homologyMap φ q ≫
      (P202.Homology.CellularComparison.comparisonIso (Space m) F F q).hom := by
    rw [standardInclusion_eq]
    rw [hn, Iso.inv_hom_id_assoc]
    rfl
  rw [hnat]
  infer_instance

lemma evaluation_natural (n m q : ℕ) (h : n ≤ m)
    (a : H F (projective m) q)
    (z : homology F F (projective n) (q : ℤ)) :
    P202Specs.UniversalCoefficients.evaluation F F
        (ordinaryComplex F F (projective n)) (q : ℤ)
        (hPullback F (standardInclusion n m h) q a) z =
      P202Specs.UniversalCoefficients.evaluation F F
        (ordinaryComplex F F (projective m)) (q : ℤ) a
        ((homologyFunctor F F (q : ℤ)).map (standardInclusion n m h) z) := by
  have hn := P202.UniversalCoefficientsCohomology.evaluation_natural F F F
    ((ordinaryFunctor F F).map (standardInclusion n m h))
    (LinearMap.id : F →ₗ[F] F) (q : ℤ) a z
  rw [P202.UniversalCoefficientsCohomology.dualMap_id] at hn
  exact hn

lemma pullback_bijective (n m q : ℕ) (h : n ≤ m) (hq : q ≤ n) :
    Function.Bijective (hPullback F (standardInclusion n m h) q) := by
  haveI := homology_isIso n m q h hq
  let eH := (asIso ((homologyFunctor F F (q : ℤ)).map
    (standardInclusion n m h))).toLinearEquiv
  let eN := LinearEquiv.ofBijective
    (P202Specs.UniversalCoefficients.evaluation F F
      (ordinaryComplex F F (projective n)) (q : ℤ))
    ((P202.UniversalCoefficients.field_duality F).1 (projective n) q)
  let eM := LinearEquiv.ofBijective
    (P202Specs.UniversalCoefficients.evaluation F F
      (ordinaryComplex F F (projective m)) (q : ℤ))
    ((P202.UniversalCoefficients.field_duality F).1 (projective m) q)
  let e := eM.trans ((LinearEquiv.arrowCongr eH.symm (LinearEquiv.refl F F)).trans eN.symm)
  have he (a : H F (projective m) q) : hPullback F (standardInclusion n m h) q a = e a := by
    apply eN.injective
    apply LinearMap.ext
    intro z
    change P202Specs.UniversalCoefficients.evaluation F F
      (ordinaryComplex F F (projective n)) (q : ℤ)
      (hPullback F (standardInclusion n m h) q a) z = _
    rw [evaluation_natural]
    change _ = eN (eN.symm _) z
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have heq : (hPullback F (standardInclusion n m h) q : _ → _) = e := funext he
  rw [heq]
  exact e.bijective

/-- Restriction preserves every actual in-range homogeneous generator. -/
lemma pullback_generator (n m q : ℕ) (h : n ≤ m) (hq : q ≤ n)
    (a : H F (projective m) q)
    (ha : Function.Bijective (fun r : F => r • a)) :
    Function.Bijective (fun r : F => r • hPullback F (standardInclusion n m h) q a) := by
  have hb := (pullback_bijective n m q h hq).comp ha
  simpa only [Function.comp_def, map_smul] using hb

/-- The unique actual mod-two hyperplane generators restrict to each other. -/
lemma pullback_hyperplaneClass (n m : ℕ) (h : n ≤ m)
    (G : HyperplaneGeometry n) (T : HyperplaneGeometry m) :
    hPullback F (standardInclusion (n+1) (m+1) (Nat.succ_le_succ h)) 1 T.ordinaryClass =
      G.ordinaryClass := by
  apply modTwoGeneratorUnique
  · exact pullback_generator (n+1) (m+1) 1 (Nat.succ_le_succ h) (by omega)
      T.ordinaryClass (hyperplaneGenerator m T)
  · exact hyperplaneGenerator n G

lemma pullback_ne_zero (n m : ℕ) (h : n ≤ m) (hn : 1 ≤ n)
    (a : H F (projective m) 1) (ha : a ≠ 0) :
    hPullback F (standardInclusion n m h) 1 a ≠ 0 := by
  intro hz
  apply ha
  exact (pullback_bijective n m 1 h hn).injective (by simpa using hz)

end P202.Cohomology.RealProjectiveRing.StandardRestriction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open P202Specs.RealProjectiveRing P202Specs.RealProjectiveHomology
open P202Specs.CupProduct P202Specs.RelativeCupProduct P202Specs.LocalOrientation
namespace P202.Cohomology.RealProjectiveRing

/-- In each nonzero projective degree, the mod-two nonzero class is unique. -/
theorem nonzeroCohomologyClassUnique (m n : ℕ) (hn : n ≤ m)
    (a b : H (ZMod 2) (projective m) n) (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  let e := ModTwoGroups.cohomologyCoordinate m n hn
  exact modTwoGeneratorUnique _ a b (generatorOfNonzero e a ha) (generatorOfNonzero e b hb)

/-- The actual local top-class map is an isomorphism over F₂. Its nonzero
normalization follows from the fundamental class, so this also applies at RP⁰. -/
theorem localTopForget_bijective (n : ℕ) (x : Space n) :
    Function.Bijective (forget (ZMod 2) (localPair (Space n) x) n) := by
  obtain ⟨F⟩ := fundamentalClasses n
  obtain ⟨a, ha, heval, hglobal⟩ := fundamentalLocalClass n F x
  have hordinary : forget (ZMod 2) (localPair (Space n) x) n a ≠ 0 := by
    intro hz
    rw [hz, map_zero, LinearMap.zero_apply] at hglobal
    exact zero_ne_one hglobal
  have hb := generatorOfNonzero (ModTwoGroups.cohomologyCoordinate n n le_rfl)
    (forget (ZMod 2) (localPair (Space n) x) n a) hordinary
  constructor
  · intro c d hcd
    obtain ⟨r, rfl⟩ := ha.surjective c
    obtain ⟨s, rfl⟩ := ha.surjective d
    have hrs : r = s := hb.injective (by simpa only [map_smul] using hcd)
    rw [hrs]
  · intro c
    obtain ⟨r, hr⟩ := hb.surjective c
    exact ⟨r • a, (map_smul _ r a).trans hr⟩

/-- Nonvanishing of the genuine restricted cup power supplies its full local
and global fundamental-class normalization, using the already proved local
orientation groups and the actual relative-to-ordinary evaluation map. -/
theorem powerEvaluationOfNonzero (μ : NaturalCohomologyRing (ZMod 2))
    (m n : ℕ) (hn : n ≤ m) (u : H (ZMod 2) (projective m) 1)
    (h : hPullback (ZMod 2) (standardInclusion n m hn) n
      (cupPower (μ.ring (projective m)) u n) ≠ 0) :
    Nonempty (PowerEvaluation μ m n hn u) := by
  obtain ⟨F⟩ := fundamentalClasses n
  obtain ⟨a, ha, heval, hglobal⟩ := normalizedLocalClasses n F
  have hordinary : forget (ZMod 2) (localPair (Space n) (coordinatePoint n)) n a ≠ 0 := by
    intro hz
    rw [hz, map_zero, LinearMap.zero_apply] at hglobal
    exact zero_ne_one hglobal
  have himage := nonzeroCohomologyClassUnique n n le_rfl
    (forget (ZMod 2) (localPair (Space n) (coordinatePoint n)) n a)
    (hPullback (ZMod 2) (standardInclusion n m hn) n
      (cupPower (μ.ring (projective m)) u n)) hordinary h
  exact ⟨powerEvaluationOfLocal μ m n hn u F a ha heval himage⟩

lemma standardInclusion_self (m : ℕ) (h : m ≤ m) : standardInclusion m m h = 𝟙 _ := by
  rw [standardInclusion_eq]
  ext q
  induction q using Quotient.inductionOn with | _ x =>
    change P202Specs.RealProjectiveHomology.quotientMap m
      (P202.Homology.RealProjectiveHomology.sphereInclusion m m h x) =
        P202Specs.RealProjectiveHomology.quotientMap m x
    congr 1
    apply Subtype.ext
    ext j
    exact P202.Homology.RealProjectiveHomology.coordinateInclusion_apply m m h x.val j

lemma hPullback_identity {X : TopCat} (n : ℕ) (a : H (ZMod 2) X n) :
    hPullback (ZMod 2) (𝟙 X) n a = a := by
  let F := P202Specs.CohomologyPairs.ordinaryCohomologyFunctor (ZMod 2) (ZMod 2) (n : ℤ)
  exact congrArg (fun f : F.obj (Opposite.op X) ⟶ F.obj (Opposite.op X) => f a)
    (F.map_id (Opposite.op X))

/-- The nullary power is the actual unit, including restriction to RP⁰. -/
theorem powerEvaluationZero (μ : NaturalCohomologyRing (ZMod 2)) (m : ℕ)
    (u : H (ZMod 2) (projective m) 1) :
    Nonempty (PowerEvaluation μ m 0 (Nat.zero_le m) u) := by
  apply powerEvaluationOfNonzero
  rw [cupPower_natural]
  letI := (μ.ring (projective 0)).gradedRing
  change (GradedMonoid.GOne.one : H (ZMod 2) (projective 0) 0) ≠ 0
  intro hz
  exact zero_ne_one ((degreeZeroUnitGenerator 0 (μ.ring (projective 0))).injective
    (by simp only [hz, smul_zero]))

/-- The constructed hyperplane generator has the full required evaluation in
projective dimension one. -/
theorem projectiveLinePresentation (μ : NaturalCohomologyRing (ZMod 2)) :
    Nonempty (GeometricPresentation μ 0) := by
  obtain ⟨G⟩ := hyperplaneGeometry 0
  have heval : ∀ n (hn : n ≤ 1), Nonempty (PowerEvaluation μ 1 n hn G.ordinaryClass) := by
    intro n hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · exact powerEvaluationZero μ 1 G.ordinaryClass
    · apply powerEvaluationOfNonzero
      rw [cupPower_one, standardInclusion_self, hPullback_identity]
      exact hyperplaneOrdinaryNonzero 0 G
  exact geometricAssembly μ 0 G (fun n hn => Classical.choice (heval n hn))

end P202.Cohomology.RealProjectiveRing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open P202Specs.CupProduct P202Specs.ThomClass P202Specs.RelativeCupProduct
  P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
namespace P202.Cohomology.RealProjectiveRing
universe w
variable {m n : ℕ} {P M : Type w} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M} {i : P → M}

/-- The fiber normalization of a Thom class proves that class is nonzero. -/
theorem normalizedThomClass_ne_zero (N : NormalBundle T S i) (d : ℕ)
    (o : Orientation (ZMod 2) N d)
    (tube : ∃ K : TubularNeighborhood N, NormalCompatible N K)
    (c : HR (ZMod 2) (ambientPair i) d) (hc : HasFiberValues (ZMod 2) o c) (p : P) :
    c ≠ 0 := by
  obtain ⟨K, hK⟩ := tube
  let f := (relativeCohomologyFunctor (ZMod 2) (ZMod 2) (d : ℤ)).map
    (sliceToFiber N K p).op
  haveI : IsIso f := P202.ThomClass.sliceToFiber_isIso N K p (ZMod 2) (d : ℤ)
  have h := hc K hK p
  intro hz
  rw [hz, map_zero] at h
  have ho : o.generator p = 0 :=
    (ConcreteCategory.bijective_of_isIso f).injective
      (h.symm.trans (map_zero f.hom).symm)
  exact zero_ne_one ((o.generates p).injective (by simp [ho]))

/-- A codimension-one normalized Thom image survives in ordinary cohomology
when the actual complement is contractible. -/
theorem normalizedThomOrdinary_ne_zero (N : NormalBundle T S i)
    (o : Orientation (ZMod 2) N 1)
    (tube : ∃ K : TubularNeighborhood N, NormalCompatible N K)
    (c : HR (ZMod 2) (ambientPair i) 1) (hc : HasFiberValues (ZMod 2) o c) (p : P)
    [ContractibleSpace (ambientPair i).sub] :
    forget (ZMod 2) (ambientPair i) 1 c ≠ 0 := by
  let f := forget (ZMod 2) (ambientPair i) 1
  have hinj : Function.Injective f :=
    HyperplaneOrdinary.forget_one_injective_of_contractible (ZMod 2) (ZMod 2) (ambientPair i)
  intro hz
  exact normalizedThomClass_ne_zero N 1 o tube c hc p
    (hinj (hz.trans (map_zero f).symm))
end P202.Cohomology.RealProjectiveRing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open P202Specs.RealProjectiveRing P202Specs.RealProjectiveHomology
open P202Specs.CupProduct P202Specs.RelativeCupProduct P202Specs.LocalOrientation
  P202Specs.CohomologyPairs P202Specs.RelativeSingularChains P202Specs.SingularChains
  P202Specs.CompactOrientation
namespace P202.Cohomology.RealProjectiveRing

/-- Cohomology coordinates for the identical projective quotient in ratio charts. -/
def smoothCohomologyCoordinate (m n : ℕ) (hn : n ≤ m) :
    H (ZMod 2) (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace m)) n ≃ₗ[ZMod 2]
      ZMod 2 := by
  let e := (ordinaryCohomologyFunctor (ZMod 2) (ZMod 2) (n : ℤ)).mapIso
    (TopCat.isoOfHomeo (X := projective m)
      (Y := TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace m))
      (smoothProjectiveHomeomorph m)).op
  exact e.toLinearEquiv.trans (ModTwoGroups.cohomologyCoordinate m n hn)

/-- A normalized fundamental class makes the actual local top forget map
bijective whenever the global top cohomology is one-dimensional over F₂. -/
theorem localForgetOfFundamental_bijective {M : Type*} [TopologicalSpace M]
    (n : ℕ) (A : Manifold n M) (O : Orientation (ZMod 2) A)
    (z : homology (ZMod 2) (ZMod 2) (TopCat.of M) (n : ℤ))
    (hz : HasLocalValues (ZMod 2) O.val Set.univ
      (absoluteToSupported (ZMod 2) M n z))
    (e : H (ZMod 2) (TopCat.of M) n ≃ₗ[ZMod 2] ZMod 2) (x : M) :
    Function.Bijective (forget (ZMod 2) (localPair M x) n) := by
  obtain ⟨a, ha, hev⟩ := normalizedRelativeClass (localPair M x) (n : ℤ)
    (O.val x) (O.property.1 x)
  have hglobal := localEvaluation_one (ZMod 2) n x O.val z hz a hev
  have hordinary : forget (ZMod 2) (localPair M x) n a ≠ 0 := by
    intro h0
    rw [h0, map_zero, LinearMap.zero_apply] at hglobal
    exact zero_ne_one hglobal
  have hb := generatorOfNonzero e (forget (ZMod 2) (localPair M x) n a) hordinary
  constructor
  · intro c d hcd
    obtain ⟨r, rfl⟩ := ha.surjective c
    obtain ⟨s, rfl⟩ := ha.surjective d
    have hrs : r = s := hb.injective (by simpa only [map_smul] using hcd)
    rw [hrs]
  · intro c
    obtain ⟨r, hr⟩ := hb.surjective c
    exact ⟨r • a, (map_smul _ r a).trans hr⟩

/-- Local top classes on the canonical ratio-chart projective manifold survive
in ordinary singular cohomology. -/
theorem smoothLocalTopForget_bijective (n : ℕ)
    (x : SmoothManifolds.ProjectiveData.RealProjectiveSpace n) :
    Function.Bijective (forget (ZMod 2)
      (localPair (SmoothManifolds.ProjectiveData.RealProjectiveSpace n) x) n) := by
  let A := forgetSmooth (SmoothManifolds.Projective.projectiveManifold n)
  obtain ⟨o, ho, _⟩ := (P202.LocalOrientation.modTwoOrientation n _ A).2
  let O : Orientation (ZMod 2) A := ⟨o, ho⟩
  haveI : CompactSpace (SmoothManifolds.ProjectiveData.RealProjectiveSpace n) :=
    (smoothProjectiveHomeomorph n).compactSpace
  obtain ⟨z, hz, _⟩ := (P202.CompactOrientation.ordinaryFundamentalClass (ZMod 2) n _ A O
    isCompact_univ).2
  exact localForgetOfFundamental_bijective n A O z hz (smoothCohomologyCoordinate n n le_rfl) x

end P202.Cohomology.RealProjectiveRing


namespace P202.Cohomology.RealProjectiveRing
open P202Specs.RealProjectiveRing P202Specs.RealProjectiveHomology
open P202Specs.CupProduct
open CategoryTheory

/-- Transfer the remaining top-power assertion from the smooth ratio-chart
quotient back to the original geometric-sphere quotient, through the actual
homeomorphism and naturality of the singular cup product. -/
theorem topCupPowerNonzero_of_ratio
    (μ : NaturalCohomologyRing (ZMod 2))
    (htop : ∀ (n : ℕ)
      (u : H (ZMod 2) (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (n+1))) 1),
      u ≠ 0 → cupPower (μ.ring _) u (n+1) ≠ 0)
    (n : ℕ) (u : H (ZMod 2) (projective (n+1)) 1) (hu : u ≠ 0) :
    cupPower (μ.ring (projective (n+1))) u (n+1) ≠ 0 := by
  let e : projective (n+1) ≅
      TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (n+1)) :=
    TopCat.isoOfHomeo (smoothProjectiveHomeomorph (n+1))
  have hi : Function.Injective (hPullback (ZMod 2) e.inv 1) :=
    (ConcreteCategory.bijective_of_isIso
      ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor (ZMod 2) (ZMod 2)
        (1 : ℤ)).map e.inv.op)).injective
  have hv : hPullback (ZMod 2) e.inv 1 u ≠ 0 := by
    intro hv
    apply hu
    exact hi (by simpa only [map_zero] using hv)
  have hvtop := htop n (hPullback (ZMod 2) e.inv 1 u) hv
  intro hz
  apply hvtop
  rw [← cupPower_natural μ e.inv u (n+1), hz, map_zero]

/-- Once the genuine top-power nonvanishing on the smooth quotient is proved,
all restrictions, local/global evaluations, Thom-image identifications and
algebraic presentation fields follow on the fixed source objects. -/
theorem completeRingOfTopNonzero (μ : NaturalCohomologyRing (ZMod 2))
    (htop : ∀ (n : ℕ)
      (u : H (ZMod 2) (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (n+1))) 1),
      u ≠ 0 → cupPower (μ.ring _) u (n+1) ≠ 0) :
    Nonempty (Presentation 0 (μ.ring (projective 0))) ∧
      ∀ m : ℕ, Nonempty (GeometricPresentation μ m) := by
  refine ⟨pointPresentation (μ.ring (projective 0)), ?_⟩
  intro m
  obtain ⟨G⟩ := hyperplaneGeometry m
  apply geometricAssembly μ m G
  intro n hn
  cases n with
  | zero => exact Classical.choice (powerEvaluationZero μ (m+1) G.ordinaryClass)
  | succ k =>
    apply Classical.choice
    apply powerEvaluationOfNonzero
    rw [cupPower_natural]
    apply topCupPowerNonzero_of_ratio μ htop k
    exact StandardRestriction.pullback_ne_zero (k+1) (m+1) hn (by omega)
      G.ordinaryClass (hyperplaneOrdinaryNonzero m G)

/-- Universal assembly into the complete independent source-facing target. -/
theorem completeRingOfTopNonzeroAll
    (htop : ∀ (μ : NaturalCohomologyRing (ZMod 2)) (n : ℕ)
      (u : H (ZMod 2) (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (n+1))) 1),
      u ≠ 0 → cupPower (μ.ring _) u (n+1) ≠ 0) : Expected.completeRing := by
  intro μ
  exact completeRingOfTopNonzero μ (htop μ)

end P202.Cohomology.RealProjectiveRing


noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped DirectSum TensorProduct
open P202Specs.CupProduct P202Specs.RelativeCupProduct
  P202Specs.RelativeSingularChains P202Specs.TransverseThomProduct

universe u w
namespace P202.Cohomology.RealProjectiveRing
variable {R : Type u} [CommRing R] {X : TopCat.{w}}

/-- The homogeneous ordinary image of a relative supported class. -/
def supportedOrdinary (a : SupportedClass R X) : HStar R X :=
  DirectSum.of (H R X) a.degree (forget R (⟨X,a.supportᶜ⟩ : Pair) a.degree a.value)

lemma forget_heq {s t : Set X} (hst : s = t) (n : ℕ)
    (a : HR R (⟨X,s⟩ : Pair) n) (b : HR R (⟨X,t⟩ : Pair) n) (hab : HEq a b) :
    forget R (⟨X,s⟩ : Pair) n a = forget R (⟨X,t⟩ : Pair) n b := by
  subst t
  cases hab
  rfl

/-- The actual relative cup product maps to multiplication in every represented singular ring. -/
lemma supportedOrdinary_cup (μ : NaturalRelativeCupProduct.{u,w} R)
    (C : CohomologyRing R X) (a b : SupportedClass R X) :
    letI := C.gradedRing
    supportedOrdinary (supportedCup R μ a b) = supportedOrdinary a * supportedOrdinary b := by
  letI := C.gradedRing
  unfold supportedOrdinary
  rw [DirectSum.of_mul_of, C.product_eq]
  have h := μ.absolute ⟨X,a.supportᶜ,b.supportᶜ⟩
    ⟨a.closed.isOpen_compl,b.closed.isOpen_compl⟩ a.degree b.degree a.value b.value C
  have hv : HEq (supportedCup R μ a b).value
      (μ.product ⟨X,a.supportᶜ,b.supportᶜ⟩
        ⟨a.closed.isOpen_compl,b.closed.isOpen_compl⟩ a.degree b.degree (a.value ⊗ₜ[R] b.value)) := by
    unfold supportedCup
    dsimp only
    exact cast_heq _ _
  have hf := forget_heq (Set.compl_inter a.support b.support) (a.degree+b.degree)
    (supportedCup R μ a b).value
    (μ.product ⟨X,a.supportᶜ,b.supportᶜ⟩
      ⟨a.closed.isOpen_compl,b.closed.isOpen_compl⟩ a.degree b.degree (a.value ⊗ₜ[R] b.value)) hv
  exact congrArg (DirectSum.of (H R X) (a.degree+b.degree)) (hf.trans h)

/-- All factors with the same ordinary image give its corresponding actual ring power. -/
lemma supportedOrdinary_orderedCup (μ : NaturalRelativeCupProduct.{u,w} R)
    (C : CohomologyRing R X) (k : ℕ) (F : Fin (k+1) → SupportedClass R X)
    (x : HStar R X) (hx : ∀ j, supportedOrdinary (F j) = x) :
    letI := C.gradedRing
    supportedOrdinary (orderedCup R μ k F) = x^(k+1) := by
  letI := C.gradedRing
  induction k with
  | zero => simpa only [orderedCup, Nat.zero_add, pow_one] using hx 0
  | succ k ih =>
    change supportedOrdinary (supportedCup R μ (F 0)
      (orderedCup R μ k (fun j => F j.succ))) = _
    rw [supportedOrdinary_cup μ C, hx 0, ih (fun j => F j.succ) (fun j => hx j.succ)]
    exact (pow_succ' x (k+1)).symm
/-- Equality of homogeneous ordinary images gives equality in the common degree. -/
lemma forget_eq_of_supportedOrdinary (a : SupportedClass R X) (q : ℕ)
    (hq : a.degree = q) (b : H R X q)
    (hab : supportedOrdinary a = DirectSum.of (H R X) q b) :
    hq ▸ (forget R (⟨X,a.supportᶜ⟩ : Pair) a.degree a.value) = b := by
  subst q
  exact DirectSum.of_injective a.degree hab

lemma supportedOrdinary_eq_of_cast_forget (a : SupportedClass R X) (q : ℕ)
    (hq : a.degree = q) (b : H R X q)
    (hab : hq ▸ (forget R (⟨X,a.supportᶜ⟩ : Pair) a.degree a.value) = b) :
    supportedOrdinary a = DirectSum.of (H R X) q b := by
  subst q
  exact congrArg (DirectSum.of (H R X) a.degree) hab

lemma orderedCup_degree_one (ν : NaturalRelativeCupProduct.{u,w} R)
    (k : ℕ) (F : Fin (k+1) → SupportedClass R X)
    (hd : ∀ j, (F j).degree = 1) :
    (orderedCup R ν k F).degree = k+1 := by
  induction k with
  | zero => exact hd 0
  | succ k ih =>
    change (F 0).degree + (orderedCup R ν k (fun j => F j.succ)).degree = k+1+1
    rw [hd 0, ih (fun j => F j.succ) (fun j => hd j.succ)]
    omega

lemma forget_castRelativeDegree {P : Pair.{w}} {d e : ℕ}
    (h : d = e) (a : HR R P d) :
    forget R P e (castRelativeDegree R h a) = h ▸ (forget R P d a) := by
  subst e
  rfl

/-- Cast the topological relative product to the actual ordinary cup power.
The input equality only identifies the homogeneous ordinary images of factors. -/
lemma orderedCup_forget_eq_power
    {X : TopCat.{w}}
    (ν : NaturalRelativeCupProduct.{0,w} (ZMod 2))
    (C : CohomologyRing (ZMod 2) X) (k : ℕ)
    (F : Fin (k+1) → SupportedClass (ZMod 2) X)
    (u : H (ZMod 2) X 1)
    (hdegree : (orderedCup (ZMod 2) ν k F).degree = k+1)
    (hfactors : ∀ j, supportedOrdinary (F j) = DirectSum.of _ 1 u) :
    hdegree ▸ (forget (ZMod 2)
      (⟨X,(orderedCup (ZMod 2) ν k F).supportᶜ⟩ : Pair)
      (orderedCup (ZMod 2) ν k F).degree
      (orderedCup (ZMod 2) ν k F).value) =
        P202Specs.RealProjectiveRing.cupPower C u (k+1) := by
  letI := C.gradedRing
  apply forget_eq_of_supportedOrdinary _ _ hdegree
  rw [supportedOrdinary_orderedCup ν C k F _ hfactors]
  have hpow : ∀ n, (DirectSum.of _ 1 u : HStar (ZMod 2) X)^n =
      DirectSum.of _ n (P202Specs.RealProjectiveRing.cupPower C u n) := by
    intro n
    induction n with
    | zero => exact (DirectSum.of_zero_one _).symm
    | succ n ih =>
      rw [pow_succ, ih, DirectSum.of_mul_of]
      simp only [C.product_eq]
      rfl
  exact hpow (k+1)

/-- Direct value-level version when every relative factor has degree one. -/
lemma orderedCup_forget_eq_cupPower {X : TopCat.{w}}
    (ν : NaturalRelativeCupProduct.{0,w} (ZMod 2))
    (C : CohomologyRing (ZMod 2) X) (k : ℕ)
    (F : Fin (k+1) → SupportedClass (ZMod 2) X)
    (u : H (ZMod 2) X 1) (hd : ∀ j, (F j).degree = 1)
    (hfactors : ∀ j,
      hd j ▸ (forget (ZMod 2) (⟨X,(F j).supportᶜ⟩ : Pair) (F j).degree (F j).value) = u) :
    orderedCup_degree_one ν k F hd ▸
      (forget (ZMod 2) (⟨X,(orderedCup (ZMod 2) ν k F).supportᶜ⟩ : Pair)
        (orderedCup (ZMod 2) ν k F).degree (orderedCup (ZMod 2) ν k F).value) =
          P202Specs.RealProjectiveRing.cupPower C u (k+1) := by
  apply orderedCup_forget_eq_power ν C k F u
  intro j
  exact supportedOrdinary_eq_of_cast_forget (F j) 1 (hd j) u (hfactors j)

/-- A point-supported nonzero class survives if the actual local forget map is injective. -/
lemma supported_forget_cast_ne_zero {X : TopCat.{w}}
    (a : SupportedClass R X) (x : X) (q : ℕ)
    (hsupport : a.support = {x}) (hdegree : a.degree = q)
    (ha : a.value ≠ 0)
    (hforget : Function.Injective
      (forget R (P202Specs.LocalOrientation.localPair X x) q)) :
    hdegree ▸ (forget R (⟨X,a.supportᶜ⟩ : Pair) a.degree a.value) ≠ 0 := by
  cases a with
  | mk support closed degree value =>
    dsimp only at hsupport hdegree
    subst support
    subst q
    apply mt (fun hzero => hforget (hzero.trans (map_zero _).symm)) ha

/-- Nonzero actual point-supported relative product gives nonzero actual cup power. -/
lemma cupPower_nonzero_of_supportedProduct {X : TopCat.{w}}
    (ν : NaturalRelativeCupProduct.{0,w} (ZMod 2))
    (C : CohomologyRing (ZMod 2) X) (k : ℕ)
    (F : Fin (k+1) → SupportedClass (ZMod 2) X)
    (u : H (ZMod 2) X 1) (x : X)
    (hdegree : (orderedCup (ZMod 2) ν k F).degree = k+1)
    (hfactors : ∀ j, supportedOrdinary (F j) = DirectSum.of _ 1 u)
    (hsupport : (orderedCup (ZMod 2) ν k F).support = {x})
    (hnonzero : (orderedCup (ZMod 2) ν k F).value ≠ 0)
    (hforget : Function.Injective
      (forget (ZMod 2) (P202Specs.LocalOrientation.localPair X x) (k+1))) :
    P202Specs.RealProjectiveRing.cupPower C u (k+1) ≠ 0 := by
  have h := supported_forget_cast_ne_zero (orderedCup (ZMod 2) ν k F) x (k+1)
    hsupport hdegree hnonzero hforget
  rw [orderedCup_forget_eq_power ν C k F u hdegree hfactors] at h
  exact h

/-- Version with degree-one ordinary factor equalities in their actual graded groups. -/
lemma cupPower_nonzero_of_degreeOne_supportedProduct {X : TopCat.{w}}
    (ν : NaturalRelativeCupProduct.{0,w} (ZMod 2))
    (C : CohomologyRing (ZMod 2) X) (k : ℕ)
    (F : Fin (k+1) → SupportedClass (ZMod 2) X)
    (u : H (ZMod 2) X 1) (x : X)
    (hd : ∀ j, (F j).degree = 1)
    (hfactors : ∀ j,
      hd j ▸ (forget (ZMod 2) (⟨X,(F j).supportᶜ⟩ : Pair) (F j).degree (F j).value) = u)
    (hsupport : (orderedCup (ZMod 2) ν k F).support = {x})
    (hnonzero : (orderedCup (ZMod 2) ν k F).value ≠ 0)
    (hforget : Function.Injective
      (forget (ZMod 2) (P202Specs.LocalOrientation.localPair X x) (k+1))) :
    P202Specs.RealProjectiveRing.cupPower C u (k+1) ≠ 0 := by
  apply cupPower_nonzero_of_supportedProduct ν C k F u x
    (orderedCup_degree_one ν k F hd) _ hsupport hnonzero hforget
  intro j
  exact supportedOrdinary_eq_of_cast_forget (F j) 1 (hd j) u (hfactors j)

end P202.Cohomology.RealProjectiveRing

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped DirectSum TensorProduct
open P202Specs.CupProduct P202Specs.RelativeCupProduct
  P202Specs.RelativeSingularChains P202Specs.TransverseThomProduct P202Specs.ThomClass
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
namespace P202.Cohomology.RealProjectiveRing

/-- Degree transport preserves zero in the actual relative cohomology group. -/
lemma castRelativeDegree_eq_zero_iff {R : Type*} [CommRing R] {P : Pair}
    {d e : ℕ} (h : d = e) (a : HR R P d) :
    castRelativeDegree R h a = 0 ↔ a = 0 := by
  subst e
  rfl

lemma castRelativeDegree_zero {R : Type*} [CommRing R] {P : Pair}
    {d e : ℕ} (h : d = e) : castRelativeDegree R h (0 : HR R P d) = 0 := by
  subst e
  rfl

/-- Explicit degree cast keeps the ambient space fixed. -/
def castOrdinaryDegree {R : Type*} [CommRing R] {X : TopCat} {d e : ℕ}
    (h : d = e) (a : H R X d) : H R X e := h ▸ a

/-- The codimension cast is only degree transport; no new normalization is assumed. -/
lemma normalizedThomOrdinary_cast_ne_zero
    {m n : ℕ} {P M : Type w} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
    {i : P → M} (N : NormalBundle T S i) (d : ℕ) (hd : d = 1)
    (o : P202Specs.ThomClass.Orientation (ZMod 2) N d)
    (tube : ∃ K : TubularNeighborhood N, NormalCompatible N K)
    (c : HR (ZMod 2) (ambientPair i) d) (hc : HasFiberValues (ZMod 2) o c) (p : P)
    [ContractibleSpace (ambientPair i).sub] :
    hd ▸ (forget (ZMod 2) (ambientPair i) d c) ≠ 0 := by
  subst d
  exact normalizedThomOrdinary_ne_zero N o tube c hc p

/-- The accepted transverse product and actual local forget map give nonzero top powers. -/
theorem smoothProjective_topPower_ne_zero_of_transverseFamily
    (ν : NaturalRelativeCupProduct.{0,0} (ZMod 2))
    (k : ℕ)
    (F : Fin (k+1) → OrientedSubmanifold (ZMod 2)
      (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (k+1)))
      (SmoothManifolds.Projective.projectiveManifold (k+1)))
    (htransverse : IsTransverse (ZMod 2) F)
    (hd : ∀ j, (F j).codimension = 1)
    (x : SmoothManifolds.ProjectiveData.RealProjectiveSpace (k+1))
    (hsupport : intersectionSupport (ZMod 2) F = {x})
    (hcompl : ∀ j, ContractibleSpace (ambientPair (F j).inclusion).sub)
    (C : CohomologyRing (ZMod 2)
      (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (k+1))))
    (u : H (ZMod 2)
      (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (k+1))) 1)
    (hu : u ≠ 0) :
    P202Specs.RealProjectiveRing.cupPower C u (k+1) ≠ 0 := by
  classical
  obtain ⟨c,hclosed,hc,hproducts⟩ := P202.TransverseThomProduct.nonemptyTransverseProduct
    (ZMod 2) (k+1) k
      (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (k+1)))
      (SmoothManifolds.Projective.projectiveManifold (k+1)) F htransverse
  let G : Fin (k+1) → SupportedClass (ZMod 2)
      (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (k+1))) :=
    fun j => ⟨(F j).support, hclosed j, (F j).codimension, c j⟩
  let A := orderedCup (ZMod 2) ν k G
  obtain ⟨hA,hAd,hpoints⟩ := hproducts ν
  change A.support = intersectionSupport (ZMod 2) F at hA
  change A.degree = totalCodimension (ZMod 2) F at hAd
  have hx : x ∈ intersectionSupport (ZMod 2) F := by rw [hsupport]; exact Set.mem_singleton x
  have hpx : ∀ j, ∃ p : (F j).source, (F j).inclusion p = x := by
    intro j
    exact Set.mem_iInter.mp hx j
  choose p hp using hpx
  obtain ⟨⟨b⟩, hmodels⟩ := hpoints x p hp
  obtain ⟨⟨s⟩,hB,hBd,hgen,heq⟩ := hmodels b
  let B := orderedCup (ZMod 2) ν k (blockSupportedFactor (ZMod 2) F p b)
  change B.support = zeroBlockSupport (ZMod 2) F at hB
  change B.degree = totalCodimension (ZMod 2) F at hBd
  change Function.Bijective (fun r : ZMod 2 => r • B.value) at hgen
  have hnonzero : A.value ≠ 0 := by
    intro hzero
    have hright := TransverseSlices.normalizedSlice_blockPullback_ne_zero s B hB hgen
    have he := heq s
    change castRelativeDegree (ZMod 2) hAd
      (relativePullback (ZMod 2) (s.toAmbient A hA) A.degree A.value) =
      castRelativeDegree (ZMod 2) hBd
        (relativePullback (ZMod 2) (s.toBlocks B hB) B.degree B.value) at he
    rw [hzero,map_zero,castRelativeDegree_zero] at he
    exact hright ((castRelativeDegree_eq_zero_iff hBd _).mp he.symm)
  have hfactor : ∀ j,
      castOrdinaryDegree (hd j)
        (forget (ZMod 2) (⟨_,(G j).supportᶜ⟩ : Pair) (G j).degree (G j).value) = u := by
    intro j
    letI := (F j).compact
    letI := hcompl j
    have hcnonzero := normalizedThomOrdinary_cast_ne_zero (F j).normal
      (F j).codimension (hd j) (F j).orientation
      (P202.ThomClass.exists_unique (ZMod 2) (F j).dimension (k+1) (F j).codimension
        (F j).source _ (F j).atlas (SmoothManifolds.Projective.projectiveManifold (k+1))
        (F j).inclusion (F j).embedding (F j).normal (F j).rank (F j).orientation).1
      (c j) (hc j) (p j)
    exact modTwoGeneratorUnique _ _ _
      (generatorOfNonzero (smoothCohomologyCoordinate (k+1) 1 (by omega)) _ hcnonzero)
      (generatorOfNonzero (smoothCohomologyCoordinate (k+1) 1 (by omega)) u hu)
  exact cupPower_nonzero_of_degreeOne_supportedProduct ν C k G u x hd hfactor
    (hA.trans hsupport) hnonzero (smoothLocalTopForget_bijective (k+1) x).injective

end P202.Cohomology.RealProjectiveRing


noncomputable section
set_option maxHeartbeats 100000
namespace P202.Cohomology.RealProjectiveCoordinates
open SmoothManifolds hiding Sphere Euclidean ModelSpace ModelChart SmoothManifold RealProjectiveSpace TangentSpace SmoothGerm
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.ProjectiveData SmoothManifolds.SphereTorusData
  SmoothManifolds.SliceData SmoothManifolds.MapClassData
open Set
open scoped Topology

/-- The vanishing locus of one homogeneous coordinate. -/
def coordinateHyperplane (n : ℕ) (j : Fin (n+2)) : Set (RealProjectiveSpace (n+1)) :=
  projectiveProjection '' {x : Sphere (n+1) | x.val j = 0}

lemma projection_mem_coordinateHyperplane (n : ℕ) (j : Fin (n+2)) (x : Sphere (n+1)) :
    projectiveProjection x ∈ coordinateHyperplane n j ↔ x.val j = 0 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (Projective.projection_fiber y x).mp hxy with rfl | h
    · exact hy
    · have hh := congrArg (fun z : Sphere (n+1) => z.val j) h
      change y.val j = -x.val j at hh
      rw [hy] at hh
      linarith
  · exact fun h => ⟨x, h, rfl⟩

/-- Swap the chosen coordinate with the last coordinate. -/
def swapCoordinates (n : ℕ) (k : Fin (n+1)) : Euclidean (n+1) ≃ₜ Euclidean (n+1) where
  toFun z := fun j => z (Equiv.swap k (Fin.last n) j)
  invFun z := fun j => z (Equiv.swap k (Fin.last n) j)
  left_inv z := by funext j; simp
  right_inv z := by funext j; simp
  continuous_toFun := continuous_pi (fun _ => continuous_apply _)
  continuous_invFun := continuous_pi (fun _ => continuous_apply _)

lemma contDiff_swapCoordinates (n : ℕ) (k : Fin (n+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (swapCoordinates n k) :=
  contDiff_pi.mpr (fun _ => contDiff_apply ℝ (fun _ => ℝ) _)

def modelSwap (n : ℕ) (k : Fin (n+1)) :
    ModelSpace (n+1) .euclidean ≃ₜ ModelSpace (n+1) .euclidean :=
  (Homeomorph.Set.univ _).trans ((swapCoordinates n k).trans (Homeomorph.Set.univ _).symm)

def coordinateHyperplaneChart (n : ℕ) (i : Fin (n+2)) (k : Fin (n+1)) :
    ModelChart (n+1) .euclidean (RealProjectiveSpace (n+1)) :=
  (Projective.projectiveChart i).transHomeomorph (modelSwap n k)

@[simp] lemma coordinateHyperplaneChart_val (n : ℕ) (i : Fin (n+2)) (k : Fin (n+1))
    (p : RealProjectiveSpace (n+1)) :
    (coordinateHyperplaneChart n i k p).val =
      swapCoordinates n k (projectiveRatios i p) := rfl

@[simp] lemma coordinateHyperplaneChart_source (n : ℕ) (i : Fin (n+2)) (k : Fin (n+1)) :
    (coordinateHyperplaneChart n i k).source = projectiveLocus i := rfl

lemma coordinateHyperplaneChart_compatible (n : ℕ) (i : Fin (n+2)) (k : Fin (n+1)) :
    CompatibleChart (Projective.projectiveManifold (n+1)) (coordinateHyperplaneChart n i k) := by
  have he : Projective.projectiveChart i ∈
      (Projective.projectiveManifold (n+1)).smoothStructure.val :=
    subset_maximalExtension (Projective.projectiveAtlas_isContDiffAtlas (n+1))
      ⟨i, Projective.projectiveChart_spec i⟩
  apply SliceStructures.compatibleChart_of_change (Projective.projectiveManifold (n+1))
    (Projective.projectiveChart i) he (coordinateHyperplaneChart n i k)
    (swapCoordinates n k).toOpenPartialHomeomorph
  · exact (contDiff_swapCoordinates n k).contDiffOn
  · exact (contDiff_swapCoordinates n k).contDiffOn
  · exact fun _ h => h
  · intro p hp
    exact ⟨mem_univ _, rfl⟩

lemma coordinateSlice_last (n : ℕ) (v : Euclidean (n+1)) :
    v ∈ coordinateSlice n (n+1) .euclidean ↔ v (Fin.last n) = 0 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp [sliceEmbedding]
  · intro hv
    refine ⟨fun j => v j.castSucc, Set.mem_univ _, ?_⟩
    funext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · simp [sliceEmbedding, k.is_lt]
    · simp [sliceEmbedding, hv]

lemma coordinateHyperplaneChart_slice (n : ℕ) (i : Fin (n+2)) (k : Fin (n+1)) :
    IsSliceChart (coordinateHyperplane n (i.succAbove k)) n .euclidean
      (coordinateHyperplaneChart n i k) := by
  refine ⟨by omega, by simp, ?_⟩
  ext y
  constructor
  · rintro ⟨p, ⟨hp, hpi⟩, rfl⟩
    refine ⟨(coordinateHyperplaneChart n i k).map_source hpi,
      (coordinateSlice_last n _).2 ?_⟩
    obtain ⟨x, hx, rfl⟩ := hp
    change x.val (i.succAbove k) = 0 at hx
    change x.val (i.succAbove (Equiv.swap k (Fin.last n) (Fin.last n))) / x.val i = 0
    simp [hx]
  · rintro ⟨hy, hslice⟩
    let z : Euclidean (n+1) := swapCoordinates n k y.val
    have hz : z k = 0 := by
      have hlast := (coordinateSlice_last n _).1 hslice
      simpa [z, swapCoordinates] using hlast
    refine ⟨projectiveInverse i z, ⟨?_, Projective.inverse_mem_locus _ _⟩, ?_⟩
    · apply (projection_mem_coordinateHyperplane n _ _).2
      change insertOne i z (i.succAbove k) / Real.sqrt (1 + squareSum z) = 0
      simp [insertOne, hz]
    · apply Subtype.ext
      change swapCoordinates n k (projectiveRatios i (projectiveInverse i z)) = y.val
      rw [Projective.ratios_inverse]
      exact (swapCoordinates n k).apply_symm_apply y.val

/-- Every coordinate hyperplane is embedded in the same canonical smooth projective quotient. -/
lemma coordinateHyperplane_hasSliceCharts (n : ℕ) (j : Fin (n+2)) :
    HasSliceCharts (Projective.projectiveManifold (n+1)) (coordinateHyperplane n j) n .euclidean := by
  refine ⟨by omega, ?_⟩
  intro p hp
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨i, hi⟩ := Projective.locus_cover (projectiveProjection x)
  have hix : x.val i ≠ 0 := (Projective.projection_mem_locus i x).1 hi
  have hji : j ≠ i := by intro h; exact hix (h ▸ hx)
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
  exact ⟨.euclidean, Or.inl rfl, coordinateHyperplaneChart n i k,
    coordinateHyperplaneChart_compatible n i k, hi, coordinateHyperplaneChart_slice n i k⟩

 theorem coordinateHyperplane_embeddedSubmanifold (n : ℕ) (j : Fin (n+2)) :
    ∃ S : SmoothManifold n .euclidean (coordinateHyperplane n j),
      IsSmoothEmbedding S (Projective.projectiveManifold (n+1)) Subtype.val := by
  obtain ⟨S, hS, _⟩ := SliceStructures.exists_slice_manifold
    (Projective.projectiveManifold (n+1)) (coordinateHyperplane n j)
    (coordinateHyperplane_hasSliceCharts n j)
  exact ⟨S, hS⟩


open SmoothManifolds.TangentData SmoothManifolds.DifferentialData SmoothManifolds.BundleOperationsData

lemma normal_differential_coordinate_zero
    {m n : ℕ} {P M : Type} [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold m .euclidean P) (S : SmoothManifold n .euclidean M)
    (f : P → M) (N : NormalBundle T S f) (p : P)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hp : f p ∈ d.source) (k : Fin n)
    (hz : ∀ q : P, (d (f q)).val k = 0) (v : TangentSpace T p) :
    coordinateDerivationEquiv S (f p) d hd hp (N.differential p v) k = 0 := by
  change (N.differential p v).val (coordinateGerm S (f p) d hd hp k) = 0
  have hzero : Filter.Germ.ofFun ((fun y => (d y).val k) ∘ f) =
      (0 : SmoothGerm T p).val := by
    have he : ((fun y => (d y).val k) ∘ f) = (fun _ : P => (0 : ℝ)) := funext hz
    rw [he]
    rfl
  exact (N.isDifferential p v (coordinateGerm S (f p) d hd hp k) 0
    (fun y => (d y).val k) rfl hzero).trans (map_zero v.val)

lemma image_eq_coordinate_kernel
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {n : ℕ}
    (e : V ≃ₗ[K] (Fin (n+1) → K)) (f : W →ₗ[K] V)
    (hf : Function.Injective f) (hdim : Module.finrank K W = n)
    (k : Fin (n+1)) (hz : ∀ u, e (f u) k = 0) :
    ∀ v, v ∈ LinearMap.range f ↔ e v k = 0 := by
  let L : V →ₗ[K] K := (LinearMap.proj k).comp e.toLinearMap
  have : FiniteDimensional K V := e.symm.finiteDimensional
  have hsurj : Function.Surjective L := by
    intro r
    refine ⟨e.symm (Pi.single k r), ?_⟩
    simp [L]
  have hincl : LinearMap.range f ≤ LinearMap.ker L := by
    rintro v ⟨u, rfl⟩
    exact hz u
  have hdimrange : Module.finrank K (LinearMap.range f) = n := by
    rw [LinearMap.finrank_range_of_inj hf, hdim]
  have hdimL : Module.finrank K (LinearMap.range L) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have hdimker : Module.finrank K (LinearMap.ker L) = n := by
    have htotal : Module.finrank K V = n+1 := by simpa using e.finrank_eq
    have hd := LinearMap.finrank_range_add_finrank_ker (K := K) L
    rw [hdimL, htotal] at hd
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hincl (hdimrange.trans hdimker.symm)
  intro v
  rw [heq]
  rfl


lemma normal_differential_range_eq_coordinate_kernel
    {n : ℕ} {P M : Type} [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold n .euclidean P) (S : SmoothManifold (n+1) .euclidean M)
    (f : P → M) (N : NormalBundle T S f) (p : P)
    (d : ModelChart (n+1) .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hp : f p ∈ d.source) (k : Fin (n+1))
    (hz : ∀ q : P, (d (f q)).val k = 0) :
    ∀ v : TangentSpace S (f p), v ∈ LinearMap.range (N.differential p) ↔
      coordinateDerivationEquiv S (f p) d hd hp v k = 0 := by
  have := (tangent_dimension T p).1
  exact image_eq_coordinate_kernel (K := ℝ) (V := TangentSpace S (f p))
    (W := TangentSpace T p) (coordinateDerivationEquiv S (f p) d hd hp)
    (N.differential p) (N.injective p) (tangent_dimension T p).2 k
    (normal_differential_coordinate_zero T S f N p d hd hp k hz)


open P202Specs.TransverseThomProduct

lemma allCoordinateHyperplanes_mem_locus_zero (n : ℕ)
    (x : RealProjectiveSpace (n+1))
    (hx : ∀ j : Fin (n+1), x ∈ coordinateHyperplane n j.succ) :
    x ∈ projectiveLocus (0 : Fin (n+2)) := by
  induction x using Quotient.inductionOn with | _ x =>
  apply (Projective.projection_mem_locus _ x).2
  intro hz
  have hxj : ∀ j : Fin (n+1), x.val j.succ = 0 := by
    intro j
    exact (projection_mem_coordinateHyperplane n j.succ x).1 (hx j)
  have hxzero : x.val = 0 := by
    funext j
    exact Fin.cases hz hxj j
  have hs := x.property
  rw [hxzero] at hs
  simp [squareSum] at hs

/-- Coordinate hyperplanes with their original quotient normal bundles, on one fixed ambient atlas. -/
def coordinateFamily (n : ℕ)
    (T : ∀ j : Fin (n+1), SmoothManifold n .euclidean (coordinateHyperplane n j.succ))
    (hc : ∀ j : Fin (n+1), CompactSpace (coordinateHyperplane n j.succ))
    (he : ∀ j : Fin (n+1), IsSmoothEmbedding (T j) (Projective.projectiveManifold (n+1)) Subtype.val)
    (N : ∀ j : Fin (n+1), NormalBundle (T j) (Projective.projectiveManifold (n+1)) Subtype.val)
    (o : ∀ j : Fin (n+1), P202Specs.ThomClass.Orientation (ZMod 2) (N j) 1) :
    Fin (n+1) → OrientedSubmanifold (ZMod 2) (TopCat.of (RealProjectiveSpace (n+1)))
      (Projective.projectiveManifold (n+1)) :=
  fun j => {
    source := TopCat.of (coordinateHyperplane n j.succ)
    compact := hc j
    dimension := n
    atlas := T j
    inclusion := Subtype.val
    embedding := he j
    normal := N j
    codimension := 1
    rank := fun _ => by omega
    orientation := o j }


lemma coordinateFamily_transverse (n : ℕ)
    (T : ∀ j : Fin (n+1), SmoothManifold n .euclidean (coordinateHyperplane n j.succ))
    (hc : ∀ j : Fin (n+1), CompactSpace (coordinateHyperplane n j.succ))
    (he : ∀ j : Fin (n+1), IsSmoothEmbedding (T j) (Projective.projectiveManifold (n+1)) Subtype.val)
    (N : ∀ j : Fin (n+1), NormalBundle (T j) (Projective.projectiveManifold (n+1)) Subtype.val)
    (o : ∀ j : Fin (n+1), P202Specs.ThomClass.Orientation (ZMod 2) (N j) 1) :
    IsTransverse (ZMod 2) (coordinateFamily n T hc he N o) := by
  intro x p h
  have hx : ∀ j : Fin (n+1), x ∈ coordinateHyperplane n j.succ := by
    intro j
    have hj := (p j).property
    have hjEq : (p j).val = x := h j
    rw [hjEq] at hj
    exact hj
  have hp : p = fun j => (⟨x, hx j⟩ : coordinateHyperplane n j.succ) := by
    funext j
    exact Subtype.ext (h j)
  subst p
  have hh : h = fun _ => Eq.refl x := Subsingleton.elim _ _
  subst h
  let S := Projective.projectiveManifold (n+1)
  let d := Projective.projectiveChart (0 : Fin (n+2))
  have hd : d ∈ S.smoothStructure.val :=
    subset_maximalExtension (Projective.projectiveAtlas_isContDiffAtlas (n+1))
      ⟨0, Projective.projectiveChart_spec 0⟩
  have hx0 : x ∈ d.source := allCoordinateHyperplanes_mem_locus_zero n x hx
  let E := coordinateDerivationEquiv S x d hd hx0
  let W : Fin (n+1) → Submodule ℝ (TangentSpace S x) :=
    fun j => LinearMap.range ((N j).differential ⟨x,hx j⟩)
  have hW : ∀ j v, v ∈ W j ↔ E v j = 0 := by
    intro j
    apply normal_differential_range_eq_coordinate_kernel (T j) S Subtype.val (N j)
      ⟨x,hx j⟩ d hd hx0 j
    intro q
    obtain ⟨y, hy, hqy⟩ := q.property
    change projectiveRatios 0 q.val j = 0
    rw [← hqy]
    change y.val ((0 : Fin (n+2)).succAbove j) / y.val 0 = 0
    simpa using div_eq_zero_iff.mpr (Or.inl hy)
  change Function.Surjective (fun v : TangentSpace S x => fun j => (W j).mkQ v)
  apply P202.Cohomology.RealProjectiveRing.coordinateNormalQuotients_surjective (K := ℝ) (V := TangentSpace S x) E W
  exact hW

open P202Specs.ThomClass

/-- The actual complement of any coordinate hyperplane is its full affine chart. -/
def coordinateHyperplaneComplementHomeomorph (n : ℕ) (j : Fin (n+2)) :
    (ambientPair (Subtype.val : coordinateHyperplane n j → RealProjectiveSpace (n+1))).sub ≃ₜ
      Euclidean (n+1) := by
  let c := Projective.projectiveChart j
  have hmem (p : RealProjectiveSpace (n+1)) :
      p ∉ Set.range (Subtype.val : coordinateHyperplane n j → RealProjectiveSpace (n+1)) ↔
        p ∈ projectiveLocus j := by
    rw [Subtype.range_val]
    induction p using Quotient.inductionOn with | _ x =>
      change (¬ projectiveProjection x ∈ coordinateHyperplane n j) ↔
        projectiveProjection x ∈ projectiveLocus j
      rw [projection_mem_coordinateHyperplane, Projective.projection_mem_locus]
  exact ((Homeomorph.refl _).subtype hmem).trans
    (c.toHomeomorphSourceTarget.trans
      ((Homeomorph.Set.univ _).trans (Homeomorph.Set.univ _)))

instance coordinateHyperplaneComplement_contractible (n : ℕ) (j : Fin (n+2)) :
    ContractibleSpace (ambientPair
      (Subtype.val : coordinateHyperplane n j → RealProjectiveSpace (n+1))).sub :=
  (coordinateHyperplaneComplementHomeomorph n j).contractibleSpace

lemma coordinateHyperplane_compl_eq_locus (n : ℕ) (j : Fin (n+2)) :
    (coordinateHyperplane n j)ᶜ = projectiveLocus j := by
  ext p
  induction p using Quotient.inductionOn with | _ x =>
    change (¬ projectiveProjection x ∈ coordinateHyperplane n j) ↔
      projectiveProjection x ∈ projectiveLocus j
    rw [projection_mem_coordinateHyperplane, Projective.projection_mem_locus]

lemma coordinateHyperplane_isClosed (n : ℕ) (j : Fin (n+2)) :
    IsClosed (coordinateHyperplane n j) := by
  apply isOpen_compl_iff.mp
  rw [coordinateHyperplane_compl_eq_locus]
  exact Projective.isOpen_locus j

instance coordinateHyperplane_compact (n : ℕ) (j : Fin (n+2)) :
    CompactSpace (coordinateHyperplane n j) := by
  haveI : CompactSpace (RealProjectiveSpace (n+1)) :=
    (P202.Cohomology.RealProjectiveRing.smoothProjectiveHomeomorph (n+1)).compactSpace
  exact isCompact_iff_compactSpace.mp (coordinateHyperplane_isClosed n j).isCompact

def coordinateOrigin (n : ℕ) : RealProjectiveSpace (n+1) :=
  projectiveInverse (0 : Fin (n+2)) (0 : Euclidean (n+1))

lemma coordinateOrigin_mem (n : ℕ) (j : Fin (n+1)) :
    coordinateOrigin n ∈ coordinateHyperplane n j.succ := by
  apply (projection_mem_coordinateHyperplane n _ _).2
  change insertOne (0 : Fin (n+2)) (0 : Euclidean (n+1)) j.succ /
    Real.sqrt (1 + squareSum (0 : Euclidean (n+1))) = 0
  simp [insertOne, Fin.insertNth_zero]

lemma coordinateHyperplanes_intersection (n : ℕ) :
    (⋂ j : Fin (n+1), coordinateHyperplane n j.succ) = {coordinateOrigin n} := by
  ext p
  constructor
  · intro hp
    have h : ∀ j : Fin (n+1), p ∈ coordinateHyperplane n j.succ := Set.mem_iInter.mp hp
    have hsource : p ∈ projectiveLocus (0 : Fin (n+2)) := by
      induction p using Quotient.inductionOn with | _ x =>
        apply (Projective.projection_mem_locus _ x).2
        intro hx0
        have hx : x.val = 0 := by
          funext j
          refine Fin.cases hx0 ?_ j
          intro j
          exact (projection_mem_coordinateHyperplane n j.succ x).1 (h j)
        have hs := x.property
        rw [hx] at hs
        norm_num [squareSum] at hs
    have hr : projectiveRatios (0 : Fin (n+2)) p = 0 := by
      induction p using Quotient.inductionOn with | _ x =>
        funext j
        change x.val ((0 : Fin (n+2)).succAbove j) / x.val 0 = 0
        rw [Fin.succAbove_zero, (projection_mem_coordinateHyperplane n j.succ x).1 (h j), zero_div]
    change p = coordinateOrigin n
    have hi := Projective.inverse_ratios (0 : Fin (n+2)) p hsource
    simpa only [hr, coordinateOrigin] using hi.symm
  · intro hp
    have heq : p = coordinateOrigin n := hp
    subst p
    exact Set.mem_iInter.mpr (coordinateOrigin_mem n)

end P202.Cohomology.RealProjectiveCoordinates

namespace P202.Cohomology.RealProjectiveCoordinates
open SmoothManifolds hiding Sphere Euclidean ModelSpace ModelChart SmoothManifold RealProjectiveSpace
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.ProjectiveData SmoothManifolds.SphereTorusData
  SmoothManifolds.SliceData SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
open P202Specs.TransverseThomProduct P202Specs.ThomClass

/-- An actual finite transverse family of compact coordinate hyperplanes,
with its original quotient normal bundles and canonical mod-two orientations. -/
theorem coordinateFamily_exists (n : ℕ) :
    ∃ F : Fin (n+1) → OrientedSubmanifold (ZMod 2)
        (TopCat.of (RealProjectiveSpace (n+1))) (Projective.projectiveManifold (n+1)),
      IsTransverse (ZMod 2) F ∧
      (∀ j, (F j).codimension = 1) ∧
      intersectionSupport (ZMod 2) F = {coordinateOrigin n} ∧
      ∀ j, ContractibleSpace (ambientPair (F j).inclusion).sub := by
  classical
  have hemb : ∀ j : Fin (n+1), ∃ T : SmoothManifold n .euclidean (coordinateHyperplane n j.succ),
      IsSmoothEmbedding T (Projective.projectiveManifold (n+1)) Subtype.val :=
    fun j => coordinateHyperplane_embeddedSubmanifold n j.succ
  choose T he using hemb
  have hnormal : ∀ j : Fin (n+1),
      Nonempty (NormalBundle (T j) (Projective.projectiveManifold (n+1)) Subtype.val) :=
    fun j => BundleOperations.exists_normal (T j) (Projective.projectiveManifold (n+1))
      Subtype.val (he j)
  let N := fun j => Classical.choice (hnormal j)
  let o := fun j => P202.Cohomology.RealProjectiveRing.ModTwoOrientation.orientationWithRank
    (N j) 1 (fun _ => by omega)
  let hc := fun j : Fin (n+1) => coordinateHyperplane_compact n j.succ
  let F := coordinateFamily n T hc he N o
  refine ⟨F, coordinateFamily_transverse n T hc he N o, fun _ => rfl, ?_, ?_⟩
  · change (⋂ j : Fin (n+1), Set.range (Subtype.val : coordinateHyperplane n j.succ → _)) = _
    simpa only [Subtype.range_val] using coordinateHyperplanes_intersection n
  · intro j
    exact coordinateHyperplaneComplement_contractible n j.succ

end P202.Cohomology.RealProjectiveCoordinates

namespace P202.Cohomology.RealProjectiveRing
open P202Specs.RealProjectiveRing P202Specs.RealProjectiveHomology P202Specs.CupProduct

/-- The actual top cup power of every degree-one generator is nonzero. -/
theorem smoothProjective_topPower_ne_zero
    (ν : P202Specs.RelativeCupProduct.NaturalRelativeCupProduct.{0,0} (ZMod 2))
    (n : ℕ)
    (C : CohomologyRing (ZMod 2)
      (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (n+1))))
    (u : H (ZMod 2)
      (TopCat.of (SmoothManifolds.ProjectiveData.RealProjectiveSpace (n+1))) 1)
    (hu : u ≠ 0) : cupPower C u (n+1) ≠ 0 := by
  obtain ⟨F, htransverse, hd, hsupport, hcompl⟩ :=
    P202.Cohomology.RealProjectiveCoordinates.coordinateFamily_exists n
  exact smoothProjective_topPower_ne_zero_of_transverseFamily ν n F htransverse hd
    (P202.Cohomology.RealProjectiveCoordinates.coordinateOrigin n) hsupport hcompl C u hu

/-- The full real-projective cohomology ring, including its normalized
hyperplane Thom generator and every required local and global evaluation. -/
theorem completeRing : Expected.completeRing := by
  obtain ⟨ν⟩ := P202.RelativeCupProduct.product.{0,0} (ZMod 2)
  apply completeRingOfTopNonzeroAll
  intro μ n u hu
  exact smoothProjective_topPower_ne_zero ν n (μ.ring _) u hu

/-- The graded truncated-polynomial presentation in every dimension. -/
theorem ringPresentation : Expected.ringPresentation := by
  intro μ m
  cases m with
  | zero => exact (completeRing μ).1
  | succ m =>
    obtain ⟨G⟩ := (completeRing μ).2 m
    exact ⟨G.presentation⟩

end P202.Cohomology.RealProjectiveRing
