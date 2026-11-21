import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.EilenbergZilber
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.TorusRing
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficientsCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.TorusHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.CupProduct
import Mathlib.LinearAlgebra.Dual.Basis

/-! Integral cohomology ring of every finite torus. Canonical evaluation
identifies ordered coordinate monomials with the duals of the prescribed
external-product cycles. Their integral square relations and anticommutation
give the full graded exterior-algebra presentation, including the empty torus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct DirectSum
namespace P202.Cohomology.TorusRing
open P202Specs.TorusRing P202Specs.SingularChains
open P202Specs.CupProduct P202Specs.CohomologyPairs
open P202Specs.AlexanderWhitney P202Specs.EilenbergZilber
open P202Specs.TopologicalKunneth

/-- The representative condition determines the external product uniquely.
Thus a basis constructed with a Künneth sequence also works for any supplied
external product with the prescribed shuffle representatives. -/
theorem externalProduct_unique (e f : ExternalProduct ℤ) : e = f := by
  have hm : e.map = f.map := by
    funext X Y p q
    apply TensorProduct.ext'
    intro a b
    obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((complex ℤ ℤ X).homologyπ p)).mp inferInstance a
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((complex ℤ ℤ Y).homologyπ q)).mp inferInstance b
    obtain ⟨z, hz, he⟩ := e.represents X Y p q a b
    obtain ⟨w, hw, hf⟩ := f.represents X Y p q a b
    have hzw : z = w := (ModuleCat.mono_iff_injective
      ((complex ℤ ℤ (productSpace X Y)).iCycles (p+q))).mp inferInstance
        (hz.trans hw.symm)
    exact he.trans ((congrArg ((complex ℤ ℤ (productSpace X Y)).homologyπ (p+q))
      hzw).trans hf.symm)
  cases e
  cases f
  cases hm
  rfl

/-- Naturality uses the actual ordinary singular maps on both sides. -/
theorem evaluate_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : Hc Y n) (z : Hm X n) :
    evaluate X n (hPullback ℤ f n a) z = evaluate Y n a (hMap ℤ f n z) := by
  have h := P202.UniversalCoefficientsCohomology.evaluation_natural ℤ ℤ ℤ
    ((ordinaryFunctor ℤ ℤ).map f) (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (n : ℤ) a z
  rw [P202.UniversalCoefficientsCohomology.dualMap_id] at h
  exact h

/-- Evaluation on categorical cycle representatives is literal evaluation of
the cochain on the chain, with no chosen splitting of the UCT. -/
theorem evaluate_homologyπ (X : TopCat.{0}) (n : ℕ)
    (a : (ordinaryCochains ℤ ℤ X).cycles (n : ℤ))
    (z : (ordinaryComplex ℤ ℤ X).cycles (n : ℤ)) :
    evaluate X n ((ordinaryCochains ℤ ℤ X).homologyπ (n : ℤ) a)
      ((ordinaryComplex ℤ ℤ X).homologyπ (n : ℤ) z) =
      (show (ordinaryComplex ℤ ℤ X).X (n : ℤ) →ₗ[ℤ] ℤ from
        (ordinaryCochains ℤ ℤ X).iCycles (n : ℤ) a)
        ((ordinaryComplex ℤ ℤ X).iCycles (n : ℤ) z) := by
  let A := ordinaryCochains ℤ ℤ X
  let K := ordinaryComplex ℤ ℤ X
  have hclass (L : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℤ))
      (x : L.cycles (n : ℤ)) :
      P202Specs.UniversalCoefficientsCohomology.cycleClass ℤ L (n : ℤ)
        ((L.sc (n : ℤ)).moduleCatCyclesIso.hom x) = L.homologyπ (n : ℤ) x := by
    rw [P202.UniversalCoefficientsCohomology.cycleClass_eq]
    simp
  have ha : P202Specs.UniversalCoefficientsCohomology.cycleClass ℤ A (n : ℤ)
      ((A.sc (n : ℤ)).moduleCatCyclesIso.hom a) = A.homologyπ (n : ℤ) a := by
    rw [P202.UniversalCoefficientsCohomology.cycleClass_eq]
    simp
  rw [← ha, ← hclass K z]
  erw [P202.UniversalCoefficientsCohomology.evaluation_formula]
  have hiA := CategoryTheory.congr_fun (A.sc (n : ℤ)).moduleCatCyclesIso_hom_i a
  have hiK := CategoryTheory.congr_fun (K.sc (n : ℤ)).moduleCatCyclesIso_hom_i z
  change ((A.sc (n : ℤ)).moduleCatCyclesIso.hom a).val = A.iCycles (n : ℤ) a at hiA
  change ((K.sc (n : ℤ)).moduleCatCyclesIso.hom z).val = K.iCycles (n : ℤ) z at hiK
  erw [hiA, hiK]

/-- The integer/nonnegative homology adapter preserves Kronecker pairing. -/
theorem evaluate_nonnegative (X : TopCat.{0}) (n : ℕ)
    (a : (ordinaryCochains ℤ ℤ X).cycles (n : ℤ))
    (z : (complex ℤ ℤ X).cycles n) :
    evaluate X n ((ordinaryCochains ℤ ℤ X).homologyπ (n : ℤ) a)
      ((ordinaryHomologyIso ℤ X n).inv ((complex ℤ ℤ X).homologyπ n z)) =
      cocycleValue ℤ X n a ((complex ℤ ℤ X).iCycles n z) := by
  let K := complex ℤ ℤ X
  let h : (degreeEmbedding 0).f n = (n : ℤ) := by change (0 : ℤ) + n = n; omega
  have hz := CategoryTheory.congr_fun (K.homologyπ_extendHomologyIso_inv
    (degreeEmbedding 0) h) z
  change (ordinaryHomologyIso ℤ X n).inv (K.homologyπ n z) =
    (ordinaryComplex ℤ ℤ X).homologyπ (n : ℤ)
      ((K.extendCyclesIso (degreeEmbedding 0) h).inv z) at hz
  rw [hz, evaluate_homologyπ]
  have hi := CategoryTheory.congr_fun
    (K.extendCyclesIso_inv_iCycles (degreeEmbedding 0) h) z
  change (show (ordinaryComplex ℤ ℤ X).X (n : ℤ) →ₗ[ℤ] ℤ from
    (ordinaryCochains ℤ ℤ X).iCycles (n : ℤ) a) _ = _
  simp only [CategoryTheory.comp_apply] at hi
  erw [hi]
  rfl


/-- The external cochain product is evaluation of the specified AW component. -/
theorem external_cup_cochain (X Y : TopCat.{0}) (p q : ℕ)
    (a : Cochain ℤ X p) (b : Cochain ℤ Y q) (c : Chains ℤ (productSpace X Y) (p+q)) :
    cup ℤ (productSpace X Y) p q
      (pullback ℤ (firstProjection X Y) p a) (pullback ℤ (secondProjection X Y) q b) c =
      tensorPairing ℤ a b (aw ℤ X Y (p+q) c ⟨(p,q),rfl⟩) := by
  let ev : Total ℤ X Y (p+q) →ₗ[ℤ] Summand ℤ X Y p q :=
    LinearMap.proj (φ := fun i : Diagonal (p+q) => Summand ℤ X Y i.val.1 i.val.2) ⟨(p,q),rfl⟩
  have he : cup ℤ (productSpace X Y) p q
      (pullback ℤ (firstProjection X Y) p a) (pullback ℤ (secondProjection X Y) q b) =
      (tensorPairing ℤ a b).comp (ev.comp (aw ℤ X Y (p+q))) := by
    apply (Finsupp.basisSingleOne : Module.Basis _ ℤ (Chains ℤ (productSpace X Y) (p+q))).ext
    intro s
    simp only [Finsupp.coe_basisSingleOne]
    rw [P202.CupProduct.cup_single]
    change _ = tensorPairing ℤ a b (aw ℤ X Y (p+q) (Finsupp.single s 1) ⟨(p,q),rfl⟩)
    rw [P202.AlexanderWhitney.formula]
    simp only [one_smul, one_mul, awComponent, P202.CupProduct.tensorPairing_tmul]
    change a (((chainMap ℤ ℤ (firstProjection X Y)).f p).hom _) *
      b (((chainMap ℤ ℤ (secondProjection X Y)).f q).hom _) = _
    rw [P202.SingularChains.chainMap_single, P202.SingularChains.chainMap_single]
    rfl
  exact LinearMap.congr_fun he c

/-- A tensor cocycle kills every total boundary, also in degree zero. -/
theorem tensorPairing_totalBoundary (X Y : TopCat.{0}) (p q n : ℕ) (h : p+q=n)
    (a : Cochain ℤ X p) (b : Cochain ℤ Y q)
    (ha : delta ℤ X p a = 0) (hb : delta ℤ Y q b = 0)
    (z : Total ℤ X Y (n+1)) :
    tensorPairing ℤ a b (totalBoundary ℤ X Y n z ⟨(p,q),h⟩) = 0 := by
  have hl (t : Summand ℤ X Y (p+1) q) :
      tensorPairing ℤ a b (leftBoundary ℤ X Y p q t) = 0 := by
    induction t using TensorProduct.inductionOn with
    | tmul c d =>
      change a (chainBoundary ℤ X p c) * b d = 0
      have hc : a (chainBoundary ℤ X p c) = 0 := LinearMap.congr_fun ha c
      rw [hc, zero_mul]
    | add t u ht hu => simp only [map_add, ht, hu, add_zero]
  have hr (t : Summand ℤ X Y p (q+1)) :
      tensorPairing ℤ a b (rightBoundary ℤ X Y p q t) = 0 := by
    induction t using TensorProduct.inductionOn with
    | tmul c d =>
      change a c * b (chainBoundary ℤ Y q d) = 0
      have hd : b (chainBoundary ℤ Y q d) = 0 := LinearMap.congr_fun hb d
      rw [hd, mul_zero]
    | add t u ht hu => simp only [map_add, ht, hu, add_zero]
  change tensorPairing ℤ a b
    (leftBoundary ℤ X Y p q (z ⟨(p+1,q),by omega⟩) +
      (-1 : ℤ)^p • rightBoundary ℤ X Y p q (z ⟨(p,q+1),by omega⟩)) = 0
  rw [map_add, map_zsmul, hl, hr, smul_zero, add_zero]

/-- Evaluating the tensor-side homotopy with cocycles removes its boundary.
The cycle is in the literal total complex used by AW and shuffle. -/
theorem tensorPairing_aw_shuffle (X Y : TopCat.{0}) (p q n : ℕ) (h : p+q=n)
    (a : Cochain ℤ X p) (b : Cochain ℤ Y q)
    (ha : delta ℤ X p a = 0) (hb : delta ℤ Y q b = 0)
    (z : (tensorComplex ℤ X Y).cycles n) :
    tensorPairing ℤ a b
      (aw ℤ X Y n (P202Specs.ShuffleModel.shuffle ℤ X Y n
        ((tensorComplex ℤ X Y).iCycles n z)) ⟨(p,q),h⟩) =
      tensorPairing ℤ a b ((tensorComplex ℤ X Y).iCycles n z ⟨(p,q),h⟩) := by
  obtain ⟨_, k, _, _⟩ := P202.EilenbergZilber.naturalHomotopies ℤ
  let F : Total ℤ X Y n →ₗ[ℤ] ℤ :=
    (tensorPairing ℤ a b).comp (LinearMap.proj (φ := fun i : Diagonal n => Summand ℤ X Y i.val.1 i.val.2) ⟨(p,q),h⟩)
  let zz : Total ℤ X Y n := (tensorComplex ℤ X Y).iCycles n z
  have hz : F ((aw ℤ X Y n).comp (P202Specs.ShuffleModel.shuffle ℤ X Y n) zz - zz) = 0 := by
    cases n with
    | zero =>
      have hk := LinearMap.congr_fun (k.zero X Y) ((tensorComplex ℤ X Y).iCycles 0 z)
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply] at hk
      change F (aw ℤ X Y 0 (P202Specs.ShuffleModel.shuffle ℤ X Y 0 zz) - zz) = 0
      erw [hk]
      exact tensorPairing_totalBoundary X Y p q 0 h a b ha hb _
    | succ n =>
      have hk := LinearMap.congr_fun (k.succ X Y n) ((tensorComplex ℤ X Y).iCycles (n+1) z)
      have hd : totalBoundary ℤ X Y n ((tensorComplex ℤ X Y).iCycles (n+1) z) = 0 := by
        have hh := CategoryTheory.congr_fun ((tensorComplex ℤ X Y).iCycles_d (n+1) n) z
        change ((tensorComplex ℤ X Y).d (n+1) n).hom
          ((tensorComplex ℤ X Y).iCycles (n+1) z) = 0 at hh
        simpa only [tensorComplex, ChainComplex.of_d, ModuleCat.hom_ofHom] using hh
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
        LinearMap.add_apply] at hk
      rw [hd, map_zero, add_zero] at hk
      change F (aw ℤ X Y (n+1) (P202Specs.ShuffleModel.shuffle ℤ X Y (n+1) zz) - zz) = 0
      erw [hk]
      exact tensorPairing_totalBoundary X Y p q (n+1) h a b ha hb _
  change F _ = F _
  exact sub_eq_zero.mp ((map_sub F _ _).symm.trans hz)

/-- The accepted cubical computation works also for the empty product. -/
theorem homologyRanks (m n : ℕ) :
    Nonempty (Hm (space m) n ≃ₗ[ℤ] (Fin (m.choose n) → ℤ)) := by
  let C := P202.Homology.TorusHomology.cubicalCWStructure m
  have hc := P202.Homology.TorusHomology.cubicalCWStructure_isProduct m
  exact P202.Homology.TorusHomology.homology_of_cubical_geometry m C hc
    (P202.Homology.TorusHomology.product_cubical_differential_zero m C hc) n

instance torusHomologyFree (m n : ℕ) : Module.Free ℤ (Hm (space m) n) := by
  obtain ⟨e⟩ := homologyRanks m n
  exact Module.Free.of_equiv e.symm

def circleHomologyEquiv (n : ℕ) : Hm circle n ≃ₗ[ℤ] Hm (space 1) n :=
  ((homologyFunctor ℤ ℤ (n : ℤ)).mapIso (TopCat.isoOfHomeo circleTorus)).toLinearEquiv

instance circleHomologyFree (n : ℕ) : Module.Free ℤ (Hm circle n) :=
  Module.Free.of_equiv (circleHomologyEquiv n).symm

/-- An orientation is an actual integral circle generator, and exists. -/
theorem orientation : P202Specs.TorusRing.Expected.orientation := by
  obtain ⟨e⟩ := homologyRanks 1 1
  letI : Unique (Fin (Nat.choose 1 1)) := by
    change Unique (Fin 1)
    infer_instance
  exact ⟨((circleHomologyEquiv 1).trans e).trans
    (LinearEquiv.funUnique (Fin (Nat.choose 1 1)) ℤ ℤ)⟩

/-- Over ℤ, projectivity of the preceding homology kills the actual Ext term.
No cohomology splitting is treated as a canonical choice. -/
theorem evaluationBijectiveOfFree (X : TopCat)
    (hf : ∀ n : ℕ, Module.Free ℤ (Hm X n)) (n : ℕ) :
    Function.Bijective (evaluate X n) := by
  let C := ordinaryComplex ℤ ℤ X
  cases n with
  | zero =>
    exact P202.UniversalCoefficientsCohomology.degree_zero ℤ ℤ C
      (P202.UniversalCoefficientsCohomology.ordinary_zero ℤ X)
  | succ n =>
    letI := hf n
    let P := P103.Ch11.ExtTorDefinitions.resolutionFamily ℤ (C.homology (n : ℤ))
    haveI : Subsingleton
        (P202Specs.UniversalCoefficientsCohomology.actualExt ℤ ℤ C (n : ℤ)) :=
      P103.Ch11.VanishingAndFlatness.ext_projective ℤ (C.homology (n : ℤ)) ℤ
        inferInstance P.val P.property 0
    obtain ⟨α, σ, hi, hx, hs, hσ, hα⟩ :=
      P202.UniversalCoefficientsCohomology.actual_split ℤ ℤ C
        (P202.UniversalCoefficientsCohomology.ordinary_zero ℤ X)
        (P202.UniversalCoefficientsCohomology.ordinary_free ℤ X) n
    refine ⟨?_, hs⟩
    intro a b hab
    have hz : evaluate X (n+1) (a-b) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨x, hxa⟩ := (hx (a-b)).mp hz
    apply sub_eq_zero.mp
    rw [← hxa, Subsingleton.elim x 0, map_zero]

/-- All nonnegative degrees, including H⁰(T⁰;ℤ). -/
theorem evaluation : P202Specs.TorusRing.Expected.evaluation :=
  fun m n => evaluationBijectiveOfFree (space m) (torusHomologyFree m) n

theorem circleEvaluation : P202Specs.TorusRing.Expected.circleEvaluation :=
  fun n => evaluationBijectiveOfFree circle circleHomologyFree n

/-- With a zero homology group, injective evaluation kills cohomology. -/
theorem cohomologySubsingleton (X : TopCat) (n : ℕ)
    (he : Function.Injective (evaluate X n)) [Subsingleton (Hm X n)] :
    Subsingleton (Hc X n) := by
  haveI : Subsingleton (Hm X n →ₗ[ℤ] ℤ) := inferInstance
  exact he.subsingleton

theorem aboveDimension : P202Specs.TorusRing.Expected.aboveDimension := by
  intro m n hmn
  haveI : Subsingleton (Hm (space m) n) := ModuleCat.subsingleton_of_isZero
    (P202.Homology.TorusHomology.torus_homology_above_dimension m n hmn)
  exact cohomologySubsingleton (space m) n (evaluation m n).injective

theorem circleAboveOne : P202Specs.TorusRing.Expected.circleAboveOne := by
  intro n hn
  haveI : Subsingleton (Hm (space 1) n) := ModuleCat.subsingleton_of_isZero
    (P202.Homology.TorusHomology.torus_homology_above_dimension 1 n hn)
  haveI : Subsingleton (Hm circle n) := (circleHomologyEquiv n).injective.subsingleton
  exact cohomologySubsingleton circle n (circleEvaluation n).injective

/-- The normalized circle class is dual to the chosen orientation. -/
def orientedClass (o : Orientation) : Hc circle 1 :=
  (LinearEquiv.ofBijective (evaluate circle 1) (circleEvaluation 1)).symm o.toLinearMap

@[simp] theorem evaluate_orientedClass (o : Orientation) :
    evaluate circle 1 (orientedClass o) = o.toLinearMap :=
  (LinearEquiv.ofBijective (evaluate circle 1) (circleEvaluation 1)).apply_symm_apply _

@[simp] theorem orientedClass_generator (o : Orientation) :
    evaluate circle 1 (orientedClass o) (o.symm 1) = 1 := by
  rw [evaluate_orientedClass]
  exact o.apply_symm_apply 1

/-- The homogeneous graded sign implies actual anticommutation in H*. -/
theorem anticommutation : P202Specs.TorusRing.Expected.anticommutation := by
  intro C X a b
  letI := (C.ring X).gradedRing
  rw [DirectSum.of_mul_of, DirectSum.of_mul_of,
    (C.ring X).product_eq, (C.ring X).product_eq]
  have h := (C.ring X).graded_commutative 1 1 a b
  have hab : (C.ring X).product 1 1 a b = -(C.ring X).product 1 1 b a :=
    sigma_mk_injective (by simpa only [GradedMonoid, GradedMonoid.mk, Nat.one_mul, pow_one, neg_one_zsmul] using h)
  rw [hab, map_neg]

/-- The integral square relation is pulled back from the zero second group
of the circle. It does not follow merely from a sign and multiplication by 2. -/
theorem squares : P202Specs.TorusRing.Expected.squares := by
  intro C a m i
  letI := (C.ring circle).gradedRing
  letI := (C.ring circle).algebra
  letI := (C.ring (space m)).gradedRing
  letI := (C.ring (space m)).algebra
  haveI : Subsingleton (Hc circle 2) := circleAboveOne 2 (by decide)
  have hzero : (DirectSum.of (H ℤ circle) 1 a : HStar ℤ circle) *
      DirectSum.of (H ℤ circle) 1 a = 0 := by
    rw [DirectSum.of_mul_of]
    have h : GradedMonoid.GMul.mul a a = (0 : Hc circle 2) := Subsingleton.elim _ _
    rw [h, map_zero]
  have h := congrArg (C.pullback (projection m i)) hzero
  simpa only [map_mul, map_zero, C.pullback_homogeneous, generator, coordinateClass] using h

/-- Torsion-free evaluation also kills the square of every integral degree-one
class, which is the relation needed by the exterior-algebra universal property. -/
theorem degreeOneSquare (C : NaturalCohomologyRing ℤ) (m : ℕ)
    (a : Hc (space m) 1) : (C.ring (space m)).product 1 1 a a = 0 := by
  have h := (C.ring (space m)).graded_commutative 1 1 a a
  have hneg : (C.ring (space m)).product 1 1 a a =
      -(C.ring (space m)).product 1 1 a a :=
    sigma_mk_injective (by
      simpa only [GradedMonoid, GradedMonoid.mk, Nat.one_mul, pow_one, neg_one_zsmul] using h)
  apply (evaluation m 2).injective
  ext z
  have hz := congrArg (fun c => evaluate (space m) 2 c z) hneg
  simp only [map_neg, LinearMap.neg_apply] at hz
  simp only [map_zero, LinearMap.zero_apply]
  omega

def coordinateLinear (a : Hc circle 1) (m : ℕ) : (Fin m → ℤ) →ₗ[ℤ] Hc (space m) 1 :=
  let g : (Fin m → ℤ) →+ Hc (space m) 1 := {
    toFun v := ∑ i : Fin m, v i • coordinateClass a m i
    map_zero' := by simp
    map_add' v w := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib] }
  { toFun := g
    map_add' := g.map_add
    map_smul' r v := by
      simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul g ℤ ℤ r v }

@[simp] theorem coordinateLinear_single (a : Hc circle 1) (m : ℕ) (i : Fin m) :
    coordinateLinear a m (Pi.single i 1) = coordinateClass a m i := by
  classical
  simp [coordinateLinear, Pi.single_apply, ite_smul]

/-- The exterior-algebra morphism with its prescribed coordinate images.
The product-dual basis calculation below establishes its bijectivity. -/
theorem exteriorMap : P202Specs.TorusRing.Expected.exteriorMap := by
  intro C a m
  letI := (C.ring (space m)).gradedRing
  letI := (C.ring (space m)).algebra
  letI : Ring (HStar ℤ (space m)) := inferInstance
  letI : Module ℤ (HStar ℤ (space m)) := Algebra.toModule
  let g : (Fin m → ℤ) →+ HStar ℤ (space m) :=
    (DirectSum.of (H ℤ (space m)) 1).comp (coordinateLinear a m).toAddMonoidHom
  let f : (Fin m → ℤ) →ₗ[ℤ] HStar ℤ (space m) := {
    toFun := g
    map_add' := g.map_add
    map_smul' r v := by
      simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul g ℤ ℤ r v }
  have hf (v : Fin m → ℤ) : f v * f v = 0 := by
    change DirectSum.of (H ℤ (space m)) 1 (coordinateLinear a m v) *
      DirectSum.of (H ℤ (space m)) 1 (coordinateLinear a m v) = 0
    rw [DirectSum.of_mul_of, (C.ring (space m)).product_eq, degreeOneSquare, map_zero]
  refine ⟨ExteriorAlgebra.lift ℤ ⟨f, hf⟩, ?_⟩
  intro i
  rw [ExteriorAlgebra.lift_ι_apply]
  change DirectSum.of (H ℤ (space m)) 1 (coordinateLinear a m (Pi.single i 1)) = _
  rw [coordinateLinear_single]
  rfl

theorem negative : P202Specs.TorusRing.Expected.negative := by
  intro m q hq
  exact ModuleCat.subsingleton_of_isZero
    ((P202.CohomologyPairs.negative ℤ ℤ).1 (space m) q hq).2

/-- Pairing with the positive point class evaluates a degree-zero cochain. -/
theorem evaluate_pointClass (X : TopCat.{0}) (x : X)
    (a : (ordinaryCochains ℤ ℤ X).cycles 0) :
    evaluate X 0 ((ordinaryCochains ℤ ℤ X).homologyπ 0 a) (pointClass X x) =
      cocycleValue ℤ X 0 a (Finsupp.single (pointSimplex X x) 1) := by
  let K := complex ℤ ℤ X
  let z : P202Specs.UniversalCoefficientsCohomology.Algebraic.cycles K 0 := ⟨Finsupp.single (pointSimplex X x) 1, by
    change ((complex ℤ ℤ X).d 0 ((ComplexShape.down ℕ).next 0)).hom _ = 0
    rw [ChainComplex.next_nat_zero, (complex ℤ ℤ X).shape 0 0 (by decide)]
    rfl⟩
  change evaluate X 0 ((ordinaryCochains ℤ ℤ X).homologyπ 0 a)
    ((ordinaryHomologyIso ℤ X 0).inv
      (P202Specs.UniversalCoefficientsCohomology.cycleClass ℤ K 0 z)) = _
  rw [P202.UniversalCoefficientsCohomology.cycleClass_eq]
  have he := evaluate_nonnegative X 0 a ((K.sc 0).moduleCatCyclesIso.inv z)
  have hi := CategoryTheory.congr_fun (K.sc 0).moduleCatCyclesIso_inv_iCycles z
  change K.iCycles 0 ((K.sc 0).moduleCatCyclesIso.inv z) = z.val at hi
  exact he.trans (congrArg (cocycleValue ℤ X 0 a) hi)

/-- The unit is normalized to +1 on every point class. -/
theorem unit_evaluate_pointClass (C : NaturalCohomologyRing ℤ)
    (X : TopCat.{0}) (x : X) :
    letI := (C.ring X).gradedRing
    evaluate X 0 (GradedMonoid.GOne.one : Hc X 0) (pointClass X x) = 1 := by
  letI := (C.ring X).gradedRing
  obtain ⟨a, ha, hu⟩ := (C.ring X).unit_represents
  rw [hu, evaluate_pointClass, ha]
  exact P202.SingularChains.augmentationLinear_single ℤ ℤ X _ 1

/-- The canonical evaluation isomorphism on the torus. -/
def evaluationEquiv (m n : ℕ) :
    Hc (space m) n ≃ₗ[ℤ] (Hm (space m) n →ₗ[ℤ] ℤ) :=
  LinearEquiv.ofBijective (evaluate (space m) n) (evaluation m n)

/-- Transport the finite dual basis through the canonical evaluation map. -/
def cohomologyDualBasis (m n : ℕ)
    (b : Module.Basis (ActiveSet m n) ℤ (Hm (space m) n)) :
    Module.Basis (ActiveSet m n) ℤ (Hc (space m) n) :=
  b.dualBasis.map (evaluationEquiv m n).symm

@[simp] theorem evaluate_cohomologyDualBasis (m n : ℕ)
    (b : Module.Basis (ActiveSet m n) ℤ (Hm (space m) n))
    (s t : ActiveSet m n) :
    evaluate (space m) n (cohomologyDualBasis m n b s) (b t) =
      if s = t then 1 else 0 := by
  classical
  change evaluationEquiv m n ((b.dualBasis.map (evaluationEquiv m n).symm) s) (b t) = _
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.dualBasis_apply_self]
  simp only [eq_comm]

/-- Equality of pairings on a homology basis determines a cohomology class. -/
theorem cohomology_ext_basis (m n : ℕ)
    (b : Module.Basis (ActiveSet m n) ℤ (Hm (space m) n))
    {a a' : Hc (space m) n}
    (h : ∀ t, evaluate (space m) n a (b t) = evaluate (space m) n a' (b t)) :
    a = a' :=
  (evaluation m n).injective (b.ext h)


/-- A list of coordinate classes has its prescribed homogeneous degree. -/
theorem word_homogeneous (C : NaturalCohomologyRing ℤ) (a : Hc circle 1)
    (m : ℕ) (l : List (Fin m)) :
    letI := (C.ring (space m)).gradedRing
    ∃ x : Hc (space m) l.length,
      DirectSum.of (H ℤ (space m)) l.length x = (l.map (generator a m)).prod := by
  letI := (C.ring (space m)).gradedRing
  let n := l.dProdIndex (fun _ => (1 : ℕ))
  have hn : n = l.length := by
    dsimp only [n]
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.dProdIndex_cons, List.length_cons, ih]; omega
  have hz : (l.map (generator a m)).prod ∈
      Set.range (DirectSum.of (H ℤ (space m)) n) :=
    ⟨l.dProd (fun _ => (1 : ℕ)) (coordinateClass a m),
      DirectSum.ofList_dProd _ _ _ _⟩
  have hrange := congrArg (fun k : ℕ => Set.range (DirectSum.of (H ℤ (space m)) k)) hn
  exact Eq.mp (congrArg (fun S : Set (HStar ℤ (space m)) => (l.map (generator a m)).prod ∈ S) hrange) hz

/-- The ordered square-free monomial lives in degree equal to its cardinality. -/
theorem monomial_homogeneous (C : NaturalCohomologyRing ℤ) (a : Hc circle 1)
    (m n : ℕ) (s : ActiveSet m n) :
    letI := (C.ring (space m)).gradedRing
    ∃ x : Hc (space m) n,
      DirectSum.of (H ℤ (space m)) n x = monomial C a m s.val := by
  letI := (C.ring (space m)).gradedRing
  have h := word_homogeneous C a m (s.val.sort (· ≤ ·))
  have hn : (s.val.sort (· ≤ ·)).length = n :=
    (Finset.length_sort _).trans s.property
  have hrange := congrArg (fun k : ℕ => Set.range (DirectSum.of (H ℤ (space m)) k)) hn
  exact Eq.mp (congrArg (fun S : Set (HStar ℤ (space m)) => monomial C a m s.val ∈ S) hrange) h

def monomialClass (C : NaturalCohomologyRing ℤ) (a : Hc circle 1)
    (m n : ℕ) (s : ActiveSet m n) : Hc (space m) n :=
  Classical.choose (monomial_homogeneous C a m n s)

@[simp] theorem of_monomialClass (C : NaturalCohomologyRing ℤ) (a : Hc circle 1)
    (m n : ℕ) (s : ActiveSet m n) :
    letI := (C.ring (space m)).gradedRing
    DirectSum.of (H ℤ (space m)) n (monomialClass C a m n s) =
      monomial C a m s.val :=
  Classical.choose_spec (monomial_homogeneous C a m n s)


/-- Kronecker-delta pairings identify the monomials with a complete basis. -/
theorem monomial_basis_of_pairing (C : NaturalCohomologyRing ℤ) (a : Hc circle 1)
    (m n : ℕ) (b : Module.Basis (ActiveSet m n) ℤ (Hm (space m) n))
    (h : ∀ s t, evaluate (space m) n (monomialClass C a m n s) (b t) =
      if s = t then 1 else 0) :
    letI := (C.ring (space m)).gradedRing
    ∃ c : Module.Basis (ActiveSet m n) ℤ (Hc (space m) n),
      (∀ s, DirectSum.of (H ℤ (space m)) n (c s) = monomial C a m s.val) ∧
      (∀ s t, evaluate (space m) n (c s) (b t) = if s = t then 1 else 0) := by
  letI := (C.ring (space m)).gradedRing
  refine ⟨cohomologyDualBasis m n b, ?_, evaluate_cohomologyDualBasis m n b⟩
  intro s
  have hs : cohomologyDualBasis m n b s = monomialClass C a m n s :=
    cohomology_ext_basis m n b (fun t => (evaluate_cohomologyDualBasis m n b s t).trans
      (h s t).symm)
  rw [hs, of_monomialClass]

end P202.Cohomology.TorusRing


noncomputable section
open scoped BigOperators

namespace P202.Cohomology.TorusRing

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- Over a commutative ring, a square biorthogonal system is a basis. -/
def basisOfBiorthogonal (q : M ≃ₗ[R] (ι → R)) (v : ι → M)
    (φ : ι → M →ₗ[R] R) (h : ∀ i j, φ i (v j) = if i = j then 1 else 0) :
    Module.Basis ι R M := by
  classical
  let s : (ι → R) →ₗ[R] M := (Pi.basisFun R ι).constr R v
  let t : M →ₗ[R] (ι → R) := LinearMap.pi φ
  have hts : t.comp s = LinearMap.id := by
    apply (Pi.basisFun R ι).ext
    intro j
    ext i
    change φ i (s ((Pi.basisFun R ι) j)) = (Pi.basisFun R ι) j i
    rw [show s ((Pi.basisFun R ι) j) = v j from Module.Basis.constr_basis _ _ _ _]
    simpa only [Pi.basisFun_apply, Pi.single_apply] using h i j
  let a : Module.End R (ι → R) := t.comp q.symm.toLinearMap
  let b : Module.End R (ι → R) := q.toLinearMap.comp s
  have hab : a * b = 1 := by
    apply LinearMap.ext
    intro x
    funext i
    change t (q.symm (q (s x))) i = x i
    rw [q.symm_apply_apply]
    exact congrFun (LinearMap.congr_fun hts x) i
  have hba : b * a = 1 := mul_eq_one_comm.mp hab
  have hst : s.comp t = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply q.injective
    have hx := LinearMap.congr_fun hba (q x)
    change q (s (t (q.symm (q x)))) = q x at hx
    change q (s (t x)) = q x
    simpa only [q.symm_apply_apply] using hx
  let e : M ≃ₗ[R] (ι → R) := {
    toLinearMap := t
    invFun := s
    left_inv := fun x => LinearMap.congr_fun hst x
    right_inv := fun x => LinearMap.congr_fun hts x }
  exact (Pi.basisFun R ι).map e.symm

@[simp] theorem basisOfBiorthogonal_apply (q : M ≃ₗ[R] (ι → R)) (v : ι → M)
    (φ : ι → M →ₗ[R] R) (h : ∀ i j, φ i (v j) = if i = j then 1 else 0) (j : ι) :
    basisOfBiorthogonal q v φ h j = v j := by
  classical
  change (Pi.basisFun R ι).constr R v ((Pi.basisFun R ι) j) = v j
  exact Module.Basis.constr_basis _ _ _ _

end P202.Cohomology.TorusRing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped TensorProduct DirectSum
namespace P202.Cohomology.TorusRing
open P202Specs.TorusRing P202Specs.SingularChains
open P202Specs.CupProduct P202Specs.CohomologyPairs
open P202Specs.AlexanderWhitney P202Specs.EilenbergZilber
open P202Specs.TopologicalKunneth

/-- Delete the last coordinate of a finite subset. -/
def dropLast {m : ℕ} (s : Finset (Fin (m+1))) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i.castSucc ∈ s)

@[simp] theorem mem_dropLast {m : ℕ} (s : Finset (Fin (m+1))) (i : Fin m) :
    i ∈ dropLast s ↔ i.castSucc ∈ s := by
  simp [dropLast]

@[simp] theorem dropLast_map {m : ℕ} (s : Finset (Fin m)) :
    dropLast (s.map Fin.castSuccEmb) = s := by
  ext i
  simp

@[simp] theorem dropLast_insert {m : ℕ} (s : Finset (Fin (m+1))) :
    dropLast (insert (Fin.last m) s) = dropLast s := by
  ext i
  simp

@[simp] theorem last_notMem_map {m : ℕ} (s : Finset (Fin m)) :
    Fin.last m ∉ s.map Fin.castSuccEmb := by
  simp

theorem map_dropLast_of_notMem {m : ℕ} (s : Finset (Fin (m+1)))
    (h : Fin.last m ∉ s) : (dropLast s).map Fin.castSuccEmb = s := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [h]
  | cast j => simp

theorem insert_map_dropLast_of_mem {m : ℕ} (s : Finset (Fin (m+1)))
    (h : Fin.last m ∈ s) : insert (Fin.last m) ((dropLast s).map Fin.castSuccEmb) = s := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [h]
  | cast j => simp

def dropInactive {m n : ℕ} (s : ActiveSet (m+1) n) (h : Fin.last m ∉ s.val) :
    ActiveSet m n :=
  ⟨dropLast s.val, by rw [← Finset.card_map Fin.castSuccEmb, map_dropLast_of_notMem _ h]; exact s.property⟩

def dropActive {m n : ℕ} (s : ActiveSet (m+1) (n+1)) (h : Fin.last m ∈ s.val) :
    ActiveSet m n :=
  ⟨dropLast s.val, by
    have hh := congrArg Finset.card (insert_map_dropLast_of_mem s.val h)
    rw [Finset.card_insert_of_notMem (last_notMem_map _), Finset.card_map, s.property] at hh
    omega⟩

@[simp] theorem dropInactive_inactive {m n : ℕ} (s : ActiveSet m n)
    (h : Fin.last m ∉ (inactive s).val) : dropInactive (inactive s) h = s := by
  apply Subtype.ext
  exact dropLast_map _

@[simp] theorem dropActive_active {m n : ℕ} (s : ActiveSet m n)
    (h : Fin.last m ∈ (active s).val) : dropActive (active s) h = s := by
  apply Subtype.ext
  simp [dropActive, active]

@[simp] theorem inactive_dropInactive {m n : ℕ} (s : ActiveSet (m+1) n)
    (h : Fin.last m ∉ s.val) : inactive (dropInactive s h) = s := by
  apply Subtype.ext
  exact map_dropLast_of_notMem _ h

@[simp] theorem active_dropActive {m n : ℕ} (s : ActiveSet (m+1) (n+1))
    (h : Fin.last m ∈ s.val) : active (dropActive s h) = s := by
  apply Subtype.ext
  exact insert_map_dropLast_of_mem _ h

private theorem last_notMem_zero {m : ℕ} (s : ActiveSet (m+1) 0) :
    Fin.last m ∉ s.val := by
  have : s.val = ∅ := Finset.card_eq_zero.mp s.property
  simp [this]

private theorem activeSet_zero_degree (n : ℕ) (s : ActiveSet 0 n) : n = 0 := by
  have hs : s.val = ∅ := by ext i; exact Fin.elim0 i
  simpa [hs] using s.property.symm

/-- The literally prescribed ordered external-product cycles, before proving
that they form a basis. -/
def productCycle (e : ExternalProduct ℤ) (o : Orientation) :
    ∀ m n : ℕ, ActiveSet m n → Hm (space m) n
  | 0, n, s => by
      have hn := activeSet_zero_degree n s
      subst n
      exact pointClass (space 0) (fun _ => 1)
  | m+1, 0, s =>
      hMap ℤ (append m) 0
        (ordinaryExternal ℤ e (space m) circle 0 0
          (productCycle e o m 0 (dropInactive s (last_notMem_zero s)) ⊗ₜ[ℤ] pointClass circle 1))
  | m+1, n+1, s =>
      if h : Fin.last m ∈ s.val then
        hMap ℤ (append m) (n+1)
          (ordinaryExternal ℤ e (space m) circle n 1
            (productCycle e o m n (dropActive s h) ⊗ₜ[ℤ] o.symm 1))
      else
        hMap ℤ (append m) (n+1)
          (ordinaryExternal ℤ e (space m) circle (n+1) 0
            (productCycle e o m (n+1) (dropInactive s h) ⊗ₜ[ℤ] pointClass circle 1))

@[simp] theorem productCycle_zero (e : ExternalProduct ℤ) (o : Orientation) :
    productCycle e o 0 0 ⟨∅, rfl⟩ = pointClass (space 0) (fun _ => 1) := rfl

@[simp] theorem productCycle_inactive (e : ExternalProduct ℤ) (o : Orientation)
    (m n : ℕ) (s : ActiveSet m n) :
    productCycle e o (m+1) n (inactive s) =
      hMap ℤ (append m) n
        (ordinaryExternal ℤ e (space m) circle n 0
          (productCycle e o m n s ⊗ₜ[ℤ] pointClass circle 1)) := by
  cases n with
  | zero => simp only [productCycle, dropInactive_inactive]
  | succ n =>
    rw [productCycle, dite_eq_right (show Fin.last m ∉ (inactive s).val from last_notMem_map s.val), dropInactive_inactive]

@[simp] theorem productCycle_active (e : ExternalProduct ℤ) (o : Orientation)
    (m n : ℕ) (s : ActiveSet m n) :
    productCycle e o (m+1) (n+1) (active s) =
      hMap ℤ (append m) (n+1)
        (ordinaryExternal ℤ e (space m) circle n 1
          (productCycle e o m n s ⊗ₜ[ℤ] o.symm 1)) := by
  rw [productCycle, dite_eq_left (by simp [active]), dropActive_active]

end P202.Cohomology.TorusRing

namespace P202.Cohomology.TorusRing
open P202Specs.TorusRing P202Specs.EilenbergZilber

/-- Reindex the known torus rank by its square-free coordinate subsets. -/
def homologyCoordinates (m n : ℕ)
    (q : Hm (space m) n ≃ₗ[ℤ] (Fin (m.choose n) → ℤ)) :
    Hm (space m) n ≃ₗ[ℤ] (ActiveSet m n → ℤ) :=
  q.trans (LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivFinOfCardEq (by
    simpa only [Fintype.card_fin] using Fintype.card_finset_len (α := Fin m) n)))

/-- The prescribed cycles form a basis as soon as a biorthogonal system of
functionals has been established. Equal finite rank makes the system complete. -/
def productBasisOfBiorthogonal (e : ExternalProduct ℤ) (o : Orientation)
    (q : ∀ m n, Hm (space m) n ≃ₗ[ℤ] (ActiveSet m n → ℤ))
    (φ : ∀ m n, ActiveSet m n → Hm (space m) n →ₗ[ℤ] ℤ)
    (h : ∀ m n s t, φ m n s (productCycle e o m n t) = if s = t then 1 else 0) :
    ProductBasis e o where
  basis m n := basisOfBiorthogonal (q m n) (productCycle e o m n) (φ m n) (h m n)
  zero := by simp
  inactive m n s := by simp
  active m n s := by simp

@[simp] theorem productBasisOfBiorthogonal_basis (e : ExternalProduct ℤ) (o : Orientation)
    (q : ∀ m n, Hm (space m) n ≃ₗ[ℤ] (ActiveSet m n → ℤ))
    (φ : ∀ m n, ActiveSet m n → Hm (space m) n →ₗ[ℤ] ℤ)
    (h : ∀ m n s t, φ m n s (productCycle e o m n t) = if s = t then 1 else 0)
    (m n : ℕ) (s : ActiveSet m n) :
    (productBasisOfBiorthogonal e o q φ h).basis m n s = productCycle e o m n s :=
  basisOfBiorthogonal_apply (q m n) (productCycle e o m n) (φ m n) (h m n) s

end P202.Cohomology.TorusRing


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct DirectSum
namespace P202.Cohomology.TorusRing
open P202Specs.TorusRing P202Specs.SingularChains
open P202Specs.CupProduct P202Specs.CohomologyPairs
open P202Specs.AlexanderWhitney P202Specs.EilenbergZilber
open P202Specs.TopologicalKunneth

/-- A pure tensor of cycles, inserted into its single bidegree, is a total cycle. -/
theorem tensorCycle_boundary (X Y : TopCat.{0}) (p q n : ℕ) (h : p+q=n+1)
    (a : (complex ℤ ℤ X).cycles p) (b : (complex ℤ ℤ Y).cycles q) :
    totalBoundary ℤ X Y n
      (Pi.single (M := fun i : Diagonal (n+1) => Summand ℤ X Y i.val.1 i.val.2) (⟨(p,q),h⟩ : Diagonal (n+1))
        ((complex ℤ ℤ X).iCycles p a ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles q b)) = 0 := by
  classical
  funext i
  change leftBoundary ℤ X Y i.val.1 i.val.2
    (Pi.single (M := fun i : Diagonal (n+1) => Summand ℤ X Y i.val.1 i.val.2) (⟨(p,q),h⟩ : Diagonal (n+1))
      ((complex ℤ ℤ X).iCycles p a ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles q b)
      ⟨(i.val.1+1,i.val.2),by have := i.property; omega⟩) +
    (-1 : ℤ)^i.val.1 • rightBoundary ℤ X Y i.val.1 i.val.2
    (Pi.single (M := fun i : Diagonal (n+1) => Summand ℤ X Y i.val.1 i.val.2) (⟨(p,q),h⟩ : Diagonal (n+1))
      ((complex ℤ ℤ X).iCycles p a ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles q b)
      ⟨(i.val.1,i.val.2+1),by have := i.property; omega⟩) = 0
  have hl : leftBoundary ℤ X Y i.val.1 i.val.2
    (Pi.single (M := fun i : Diagonal (n+1) => Summand ℤ X Y i.val.1 i.val.2) (⟨(p,q),h⟩ : Diagonal (n+1))
      ((complex ℤ ℤ X).iCycles p a ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles q b)
      ⟨(i.val.1+1,i.val.2),by have := i.property; omega⟩) = 0 := by
    by_cases he : (⟨(i.val.1+1,i.val.2),by have := i.property; omega⟩ : Diagonal (n+1)) = ⟨(p,q),h⟩
    · have hp : p = i.val.1 + 1 := (congrArg (fun j : Diagonal (n+1) => j.val.1) he).symm
      have hq : q = i.val.2 := (congrArg (fun j : Diagonal (n+1) => j.val.2) he).symm
      subst p q
      rw [Pi.single_eq_same]
      change (boundary ℤ ℤ X i.val.1 ((complex ℤ ℤ X).iCycles (i.val.1+1) a)) ⊗ₜ[ℤ] _ = 0
      have hd := CategoryTheory.congr_fun ((complex ℤ ℤ X).iCycles_d (i.val.1+1) i.val.1) a
      change boundary ℤ ℤ X i.val.1 _ = 0 at hd
      erw [hd, TensorProduct.zero_tmul]
    · rw [Pi.single_eq_of_ne he, map_zero]
  have hr : rightBoundary ℤ X Y i.val.1 i.val.2
    (Pi.single (M := fun i : Diagonal (n+1) => Summand ℤ X Y i.val.1 i.val.2) (⟨(p,q),h⟩ : Diagonal (n+1))
      ((complex ℤ ℤ X).iCycles p a ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles q b)
      ⟨(i.val.1,i.val.2+1),by have := i.property; omega⟩) = 0 := by
    by_cases he : (⟨(i.val.1,i.val.2+1),by have := i.property; omega⟩ : Diagonal (n+1)) = ⟨(p,q),h⟩
    · have hp : p = i.val.1 := (congrArg (fun j : Diagonal (n+1) => j.val.1) he).symm
      have hq : q = i.val.2 + 1 := (congrArg (fun j : Diagonal (n+1) => j.val.2) he).symm
      subst p q
      rw [Pi.single_eq_same]
      change _ ⊗ₜ[ℤ] (boundary ℤ ℤ Y i.val.2 ((complex ℤ ℤ Y).iCycles (i.val.2+1) b)) = 0
      have hd := CategoryTheory.congr_fun ((complex ℤ ℤ Y).iCycles_d (i.val.2+1) i.val.2) b
      change boundary ℤ ℤ Y i.val.2 _ = 0 at hd
      erw [hd, TensorProduct.tmul_zero]
    · rw [Pi.single_eq_of_ne he, map_zero]
  rw [hl, hr, smul_zero, add_zero]

/-- The tensor cycle with its actual representative, at any named total degree. -/
def tensorCycleAt (X Y : TopCat.{0}) (p q n : ℕ) (h : p+q=n)
    (a : (complex ℤ ℤ X).cycles p) (b : (complex ℤ ℤ Y).cycles q) :
    (tensorComplex ℤ X Y).cycles n :=
  ((tensorComplex ℤ X Y).sc n).moduleCatCyclesIso.inv
    ⟨Pi.single (⟨(p,q),h⟩ : Diagonal n)
      ((complex ℤ ℤ X).iCycles p a ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles q b), by
      change ((tensorComplex ℤ X Y).d n ((ComplexShape.down ℕ).next n)).hom _ = 0
      cases n with
      | zero =>
        rw [ChainComplex.next_nat_zero]
        rw [(tensorComplex ℤ X Y).shape 0 0 (by decide)]
        rfl
      | succ n =>
        rw [ChainComplex.next_nat_succ]
        simpa only [tensorComplex, ChainComplex.of_d, ModuleCat.hom_ofHom] using
          tensorCycle_boundary X Y p q n h a b⟩

abbrev tensorCycle (X Y : TopCat.{0}) (p q : ℕ)
    (a : (complex ℤ ℤ X).cycles p) (b : (complex ℤ ℤ Y).cycles q) :
    (tensorComplex ℤ X Y).cycles (p+q) := tensorCycleAt X Y p q (p+q) rfl a b

@[simp] theorem tensorCycle_i (X Y : TopCat.{0}) (p q : ℕ)
    (a : (complex ℤ ℤ X).cycles p) (b : (complex ℤ ℤ Y).cycles q) :
    (tensorComplex ℤ X Y).iCycles (p+q) (tensorCycle X Y p q a b) =
      Pi.single (⟨(p,q),rfl⟩ : Diagonal (p+q))
        ((complex ℤ ℤ X).iCycles p a ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles q b) := by
  exact CategoryTheory.congr_fun
    ((tensorComplex ℤ X Y).sc (p+q)).moduleCatCyclesIso_inv_iCycles _

/-- The evaluation formula at the chain level, in the matching bidegree. -/
theorem external_cup_shuffle (X Y : TopCat.{0}) (p q : ℕ)
    (a : Cochain ℤ X p) (b : Cochain ℤ Y q)
    (ha : delta ℤ X p a = 0) (hb : delta ℤ Y q b = 0)
    (z : (complex ℤ ℤ X).cycles p) (w : (complex ℤ ℤ Y).cycles q) :
    cup ℤ (productSpace X Y) p q
      (pullback ℤ (firstProjection X Y) p a)
      (pullback ℤ (secondProjection X Y) q b)
      (P202Specs.ShuffleModel.shuffleComponent ℤ X Y p q
        ((complex ℤ ℤ X).iCycles p z ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles q w)) =
      a ((complex ℤ ℤ X).iCycles p z) * b ((complex ℤ ℤ Y).iCycles q w) := by
  classical
  have hs := tensorPairing_aw_shuffle X Y p q (p+q) rfl a b ha hb
    (tensorCycle X Y p q z w)
  rw [tensorCycle_i, P202.ShuffleBoundary.shuffle_single] at hs
  change tensorPairing ℤ a b
    (aw ℤ X Y (p+q) (P202Specs.ShuffleModel.shuffleComponent ℤ X Y p q
      ((complex ℤ ℤ X).iCycles p z ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles q w)) ⟨(p,q),rfl⟩) = _ at hs
  rw [external_cup_cochain]
  exact hs.trans (by
    rw [Pi.single_eq_same]
    exact P202.CupProduct.tensorPairing_tmul ℤ a b _ _)

/-- Different bidegrees pair to zero before passing to homology. -/
theorem external_cup_shuffle_mismatched (X Y : TopCat.{0}) (p q r s : ℕ)
    (h : p+q=r+s) (hne : p ≠ r ∨ q ≠ s)
    (a : Cochain ℤ X p) (b : Cochain ℤ Y q)
    (ha : delta ℤ X p a = 0) (hb : delta ℤ Y q b = 0)
    (z : (complex ℤ ℤ X).cycles r) (w : (complex ℤ ℤ Y).cycles s) :
    tensorPairing ℤ a b
      (aw ℤ X Y (r+s) (P202Specs.ShuffleModel.shuffleComponent ℤ X Y r s
        ((complex ℤ ℤ X).iCycles r z ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles s w))
        ⟨(p,q),h⟩) = 0 := by
  classical
  have hs := tensorPairing_aw_shuffle X Y p q (r+s) h a b ha hb
    (tensorCycle X Y r s z w)
  rw [tensorCycle_i, P202.ShuffleBoundary.shuffle_single] at hs
  change tensorPairing ℤ a b
    (aw ℤ X Y (r+s) (P202Specs.ShuffleModel.shuffleComponent ℤ X Y r s
      ((complex ℤ ℤ X).iCycles r z ⊗ₜ[ℤ] (complex ℤ ℤ Y).iCycles s w)) ⟨(p,q),h⟩) = _ at hs
  rw [hs]
  have hidx : (⟨(p,q),h⟩ : Diagonal (r+s)) ≠ ⟨(r,s),rfl⟩ := by
    intro he
    have hp := congrArg (fun j : Diagonal (r+s) => j.val.1) he
    have hq := congrArg (fun j : Diagonal (r+s) => j.val.2) he
    exact hne.elim (fun hh => hh hp) (fun hh => hh hq)
  simp only [Pi.single_eq_of_ne hidx, map_zero]

/-- The external cup formula is unchanged by a degree transport. -/
theorem cast_external_cup_cochain (X Y : TopCat.{0}) (p q n : ℕ) (h : p+q=n)
    (a : Cochain ℤ X p) (b : Cochain ℤ Y q) (c : Chains ℤ (productSpace X Y) n) :
    castCochain ℤ h (cup ℤ (productSpace X Y) p q
      (pullback ℤ (firstProjection X Y) p a)
      (pullback ℤ (secondProjection X Y) q b)) c =
    tensorPairing ℤ a b (aw ℤ X Y n c ⟨(p,q),h⟩) := by
  subst n
  exact external_cup_cochain X Y p q a b c

/-- Kronecker evaluation also respects a transport of the cohomology degree. -/
theorem evaluate_cast_nonnegative (X : TopCat.{0}) (p n : ℕ) (h : p=n)
    (a : (ordinaryCochains ℤ ℤ X).cycles (p : ℤ))
    (z : (complex ℤ ℤ X).cycles n) :
    evaluate X n (h ▸ ((ordinaryCochains ℤ ℤ X).homologyπ (p : ℤ) a))
      ((ordinaryHomologyIso ℤ X n).inv ((complex ℤ ℤ X).homologyπ n z)) =
    castCochain ℤ h (cocycleValue ℤ X p a) ((complex ℤ ℤ X).iCycles n z) := by
  subst n
  exact evaluate_nonnegative X p a z

/-- The ordinary external representative is the prescribed shuffle cycle. -/
theorem ordinaryExternal_homologyπ (e : ExternalProduct ℤ) (X Y : TopCat.{0}) (p q : ℕ)
    (z : (complex ℤ ℤ X).cycles p) (w : (complex ℤ ℤ Y).cycles q)
    (t : (complex ℤ ℤ (productSpace X Y)).cycles (p+q))
    (ht : e.map X Y p q ((complex ℤ ℤ X).homologyπ p z ⊗ₜ[ℤ]
      (complex ℤ ℤ Y).homologyπ q w) =
        (complex ℤ ℤ (productSpace X Y)).homologyπ (p+q) t) :
    ordinaryExternal ℤ e X Y p q
      ((ordinaryHomologyIso ℤ X p).inv ((complex ℤ ℤ X).homologyπ p z) ⊗ₜ[ℤ]
        (ordinaryHomologyIso ℤ Y q).inv ((complex ℤ ℤ Y).homologyπ q w)) =
      (ordinaryHomologyIso ℤ (productSpace X Y) (p+q)).inv
        ((complex ℤ ℤ (productSpace X Y)).homologyπ (p+q) t) := by
  simp only [ordinaryExternal, LinearMap.comp_apply, TensorProduct.map_tmul]
  have hx := CategoryTheory.congr_fun (ordinaryHomologyIso ℤ X p).inv_hom_id
    ((complex ℤ ℤ X).homologyπ p z)
  have hy := CategoryTheory.congr_fun (ordinaryHomologyIso ℤ Y q).inv_hom_id
    ((complex ℤ ℤ Y).homologyπ q w)
  change (ordinaryHomologyIso ℤ X p).hom
    ((ordinaryHomologyIso ℤ X p).inv ((complex ℤ ℤ X).homologyπ p z)) =
    (complex ℤ ℤ X).homologyπ p z at hx
  change (ordinaryHomologyIso ℤ Y q).hom
    ((ordinaryHomologyIso ℤ Y q).inv ((complex ℤ ℤ Y).homologyπ q w)) =
    (complex ℤ ℤ Y).homologyπ q w at hy
  erw [hx, hy, ht]

/-- Cup and shuffle external products are adjoint under canonical Kronecker
pairing, with the specified AW and shuffle conventions. -/
theorem evaluate_external_product (C : NaturalCohomologyRing ℤ) (e : ExternalProduct ℤ)
    (X Y : TopCat.{0}) (p q : ℕ) (a : Hc X p) (b : Hc Y q)
    (z : Hm X p) (w : Hm Y q) :
    evaluate (productSpace X Y) (p+q)
      ((C.ring (productSpace X Y)).product p q
        (hPullback ℤ (firstProjection X Y) p a)
        (hPullback ℤ (secondProjection X Y) q b))
      (ordinaryExternal ℤ e X Y p q (z ⊗ₜ[ℤ] w)) =
      evaluate X p a z * evaluate Y q b w := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinaryCochains ℤ ℤ X).homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinaryCochains ℤ ℤ Y).homologyπ (q : ℤ))).mp inferInstance b
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    (ordinaryHomologyIso ℤ X p).inv).mp inferInstance z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    (ordinaryHomologyIso ℤ Y q).inv).mp inferInstance w
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((complex ℤ ℤ X).homologyπ p)).mp inferInstance z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((complex ℤ ℤ Y).homologyπ q)).mp inferInstance w
  let a' := HomologicalComplex.cyclesMap
    ((ordinaryCochainFunctor ℤ ℤ).map (firstProjection X Y).op) (p : ℤ) a
  let b' := HomologicalComplex.cyclesMap
    ((ordinaryCochainFunctor ℤ ℤ).map (secondProjection X Y).op) (q : ℤ) b
  obtain ⟨c, hc, hpc⟩ := (C.ring (productSpace X Y)).represents p q a' b'
  obtain ⟨t, ht, hpt⟩ := e.represents X Y p q z w
  have hprod := ordinaryExternal_homologyπ e X Y p q z w t hpt
  rw [P202.CupProduct.hPullback_homologyπ, P202.CupProduct.hPullback_homologyπ]
  change evaluate (productSpace X Y) (p+q)
    ((C.ring (productSpace X Y)).product p q
      ((ordinaryCochains ℤ ℤ (productSpace X Y)).homologyπ (p : ℤ) a')
      ((ordinaryCochains ℤ ℤ (productSpace X Y)).homologyπ (q : ℤ) b')) _ = _
  rw [hpc, hprod, evaluate_nonnegative, hc, ht]
  dsimp only [a', b']
  rw [P202.CupProduct.cocycleValue_pullback, P202.CupProduct.cocycleValue_pullback]
  rw [external_cup_shuffle X Y p q _ _
    (P202.CupProduct.cocycleValue_delta ℤ X p a)
    (P202.CupProduct.cocycleValue_delta ℤ Y q b), evaluate_nonnegative, evaluate_nonnegative]

/-- With equal total degree, cohomological and homological external products
of different bidegrees have zero Kronecker pairing. -/
theorem evaluate_external_product_mismatched
    (C : NaturalCohomologyRing ℤ) (e : ExternalProduct ℤ)
    (X Y : TopCat.{0}) (p q r s : ℕ) (h : p+q=r+s) (hne : p ≠ r ∨ q ≠ s)
    (a : Hc X p) (b : Hc Y q) (z : Hm X r) (w : Hm Y s) :
    evaluate (productSpace X Y) (r+s)
      (h ▸ ((C.ring (productSpace X Y)).product p q
        (hPullback ℤ (firstProjection X Y) p a)
        (hPullback ℤ (secondProjection X Y) q b)))
      (ordinaryExternal ℤ e X Y r s (z ⊗ₜ[ℤ] w)) = 0 := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinaryCochains ℤ ℤ X).homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinaryCochains ℤ ℤ Y).homologyπ (q : ℤ))).mp inferInstance b
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    (ordinaryHomologyIso ℤ X r).inv).mp inferInstance z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    (ordinaryHomologyIso ℤ Y s).inv).mp inferInstance w
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((complex ℤ ℤ X).homologyπ r)).mp inferInstance z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((complex ℤ ℤ Y).homologyπ s)).mp inferInstance w
  let a' := HomologicalComplex.cyclesMap
    ((ordinaryCochainFunctor ℤ ℤ).map (firstProjection X Y).op) (p : ℤ) a
  let b' := HomologicalComplex.cyclesMap
    ((ordinaryCochainFunctor ℤ ℤ).map (secondProjection X Y).op) (q : ℤ) b
  obtain ⟨c, hc, hpc⟩ := (C.ring (productSpace X Y)).represents p q a' b'
  obtain ⟨t, ht, hpt⟩ := e.represents X Y r s z w
  have hprod := ordinaryExternal_homologyπ e X Y r s z w t hpt
  rw [P202.CupProduct.hPullback_homologyπ, P202.CupProduct.hPullback_homologyπ]
  change evaluate (productSpace X Y) (r+s)
    (h ▸ ((C.ring (productSpace X Y)).product p q
      ((ordinaryCochains ℤ ℤ (productSpace X Y)).homologyπ (p : ℤ) a')
      ((ordinaryCochains ℤ ℤ (productSpace X Y)).homologyπ (q : ℤ) b'))) _ = _
  rw [hpc, hprod, evaluate_cast_nonnegative, hc, ht]
  dsimp only [a', b']
  rw [P202.CupProduct.cocycleValue_pullback, P202.CupProduct.cocycleValue_pullback]
  rw [cast_external_cup_cochain]
  exact external_cup_shuffle_mismatched X Y p q r s h hne _ _
    (P202.CupProduct.cocycleValue_delta ℤ X p a)
    (P202.CupProduct.cocycleValue_delta ℤ Y q b) z w

end P202.Cohomology.TorusRing


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
open scoped DirectSum
namespace P202.Cohomology.TorusRing

lemma dfinsupp_basis_apply {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] {M : ι → Type*} {η : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (b : ∀ i, Module.Basis (η i) R (M i)) (i : ι) (j : η i) :
    DFinsupp.basis b ⟨i,j⟩ = DFinsupp.single i (b i j) := by
  classical
  apply (DFinsupp.basis b).repr.injective
  simp [DFinsupp.basis, DFinsupp.mapRange.linearEquiv,
    sigmaFinsuppLequivDFinsupp]

lemma map_exterior_basis {m : ℕ} {A : Type*} [Ring A] [Algebra ℤ A]
    (f : ExteriorAlgebra ℤ (Fin m → ℤ) →ₐ[ℤ] A) (g : Fin m → A)
    (hf : ∀ i, f (ExteriorAlgebra.ι ℤ (Pi.single i 1)) = g i)
    (s : Finset (Fin m)) :
    f ((Pi.basisFun ℤ (Fin m)).ExteriorAlgebra s) = ((s.sort (· ≤ ·)).map g).prod := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ (show s.card = s.card from rfl)]
  unfold ExteriorAlgebra.ιMulti_family
  rw [ExteriorAlgebra.ιMulti_apply, map_list_prod]
  simp only [List.map_ofFn, Function.comp_apply, Pi.basisFun_apply]
  congr 1
  rw [List.ofFn_eq_map]
  simp only [Function.comp_def, hf, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  change List.map (g ∘ (s.orderEmbOfFin rfl)) _ = _
  rw [← List.map_map, Finset.listMap_orderEmbOfFin_finRange]
end P202.Cohomology.TorusRing

namespace P202.Cohomology.TorusRing

def exteriorEquivOfBasis {m : ℕ} {A : Type*} [Ring A] [Algebra ℤ A]
    (f : ExteriorAlgebra ℤ (Fin m → ℤ) →ₐ[ℤ] A) (g : Fin m → A)
    (hf : ∀ i, f (ExteriorAlgebra.ι ℤ (Pi.single i 1)) = g i)
    (b : Module.Basis (Finset (Fin m)) ℤ A)
    (hb : ∀ s, b s = ((s.sort (· ≤ ·)).map g).prod) :
    ExteriorAlgebra ℤ (Fin m → ℤ) ≃ₐ[ℤ] A := by
  let bE := (Pi.basisFun ℤ (Fin m)).ExteriorAlgebra
  let e := bE.equiv b (Equiv.refl _)
  have hfe : f.toLinearMap = e.toLinearMap := by
    apply bE.ext
    intro s
    change f (bE s) = e (bE s)
    rw [Module.Basis.equiv_apply]
    exact (map_exterior_basis f g hf s).trans (hb s).symm
  have hfun : (fun x => f x) = (fun x => e x) := by
    funext x
    exact LinearMap.congr_fun hfe x
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply e.injective
    simpa only [← congrFun hfun x, ← congrFun hfun y] using hxy
  · intro y
    refine ⟨e.symm y, ?_⟩
    exact (congrFun hfun _).trans (e.apply_symm_apply y)


end P202.Cohomology.TorusRing
namespace P202.Cohomology.TorusRing
lemma exterior_homogeneous_image {m n : ℕ} {A M : Type*}
    [Ring A] [Algebra ℤ A] [AddCommGroup M] [Module ℤ M]
    (f : ExteriorAlgebra ℤ (Fin m → ℤ) →ₐ[ℤ] A)
    (l : M →ₗ[ℤ] A)
    (b : Module.Basis (Set.powersetCard (Fin m) n) ℤ M)
    (hf : ∀ s : Set.powersetCard (Fin m) n,
      f ((Pi.basisFun ℤ (Fin m)).ExteriorAlgebra s.val) = l (b s)) :
    f '' (↑(⋀[ℤ]^n (Fin m → ℤ)) : Set (ExteriorAlgebra ℤ (Fin m → ℤ))) =
      Set.range l := by
  let bE := (Pi.basisFun ℤ (Fin m)).exteriorPower n
  let e := bE.equiv b (Equiv.refl _)
  have hfe : f.toLinearMap.comp (⋀[ℤ]^n (Fin m → ℤ)).subtype =
      l.comp e.toLinearMap := by
    apply bE.ext
    intro s
    change f (bE s) = l (e (bE s))
    rw [Module.Basis.equiv_apply]
    exact (congrArg f (ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun ℤ (Fin m)) s)).symm.trans (hf s)
  have hfun (x : ⋀[ℤ]^n (Fin m → ℤ)) : f x = l (e x) :=
    LinearMap.congr_fun hfe x
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e ⟨x,hx⟩, (hfun ⟨x,hx⟩).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨e.symm z, (e.symm z).property, ?_⟩
    exact (hfun (e.symm z)).trans (congrArg l (e.apply_symm_apply z))
end P202.Cohomology.TorusRing
namespace P202.Cohomology.TorusRing

noncomputable def directSumFinsetBasis {R : Type*} [CommRing R] {m : ℕ}
    {H : ℕ → Type*} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)]
    (b : ∀ n, Module.Basis (Set.powersetCard (Fin m) n) R (H n)) :
    Module.Basis (Finset (Fin m)) R (⨁ n, H n) :=
  (DFinsupp.basis b).reindex Set.powersetCard.prodEquiv

lemma directSumFinsetBasis_apply {R : Type*} [CommRing R] {m n : ℕ}
    {H : ℕ → Type*} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)]
    (b : ∀ n, Module.Basis (Set.powersetCard (Fin m) n) R (H n))
    (s : Set.powersetCard (Fin m) n) :
    directSumFinsetBasis b s.val = DirectSum.of H n (b n s) := by
  classical
  have h := (DFinsupp.basis b).reindex_apply Set.powersetCard.prodEquiv s.val
  change directSumFinsetBasis b s.val = _ at h
  rw [h]
  have he : Set.powersetCard.prodEquiv.symm s.val = ⟨n,s⟩ := by
    apply Set.powersetCard.prodEquiv.injective
    simp
  rw [he]
  exact dfinsupp_basis_apply b n s

noncomputable def directSumFinsetAddEquiv {R : Type*} [CommRing R] {m : ℕ}
    {H : ℕ → Type*} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)]
    (b : ∀ n, Module.Basis (Set.powersetCard (Fin m) n) R (H n)) :
    (⨁ n, H n) ≃+ (Finset (Fin m) →₀ R) :=
  (directSumFinsetBasis b).repr.toAddEquiv

end P202.Cohomology.TorusRing

open P202Specs.TorusRing P202Specs.CupProduct
namespace P202.Cohomology.TorusRing

def totalMonomialBasis (C : NaturalCohomologyRing ℤ) (m : ℕ)
    (b : ∀ n, Module.Basis (ActiveSet m n) ℤ (Hc (space m) n)) :
    letI := (C.ring (space m)).gradedRing
    letI := (C.ring (space m)).algebra
    Module.Basis (Finset (Fin m)) ℤ (HStar ℤ (space m)) := by
  letI := (C.ring (space m)).gradedRing
  letI := (C.ring (space m)).algebra
  exact Module.Basis.ofRepr (directSumFinsetAddEquiv b).toIntLinearEquiv

lemma totalMonomialBasis_apply (C : NaturalCohomologyRing ℤ) (m n : ℕ)
    (b : ∀ n, Module.Basis (ActiveSet m n) ℤ (Hc (space m) n)) (s : ActiveSet m n) :
    letI := (C.ring (space m)).gradedRing
    letI := (C.ring (space m)).algebra
    totalMonomialBasis C m b s.val = DirectSum.of (H ℤ (space m)) n (b n s) := by
  letI := (C.ring (space m)).gradedRing
  letI := (C.ring (space m)).algebra
  change (Module.Basis.ofRepr (directSumFinsetAddEquiv b).toIntLinearEquiv) s.val = _
  have h : (Module.Basis.ofRepr (directSumFinsetAddEquiv b).toIntLinearEquiv) s.val =
      directSumFinsetBasis b s.val := by
    simp only [Module.Basis.coe_ofRepr]
    rfl
  exact h.trans (directSumFinsetBasis_apply b s)

end P202.Cohomology.TorusRing
namespace P202.Cohomology.TorusRing

theorem presentationOfMonomialBasis (C : NaturalCohomologyRing ℤ)
    (e : P202Specs.EilenbergZilber.ExternalProduct ℤ) (o : Orientation)
    (a : Hc circle 1) (B : ProductBasis e o) (m : ℕ)
    (f : letI := (C.ring (space m)).gradedRing
      letI := (C.ring (space m)).algebra
      ExteriorAlgebra ℤ (Fin m → ℤ) →ₐ[ℤ] HStar ℤ (space m))
    (hf : ∀ i, f (ExteriorAlgebra.ι ℤ (Pi.single i 1)) = generator a m i)
    (hsq : letI := (C.ring (space m)).gradedRing
      ∀ i, generator a m i * generator a m i = 0)
    (hanti : letI := (C.ring (space m)).gradedRing
      ∀ i j, generator a m i * generator a m j = -(generator a m j * generator a m i))
    (b : ∀ n, Module.Basis (ActiveSet m n) ℤ (Hc (space m) n))
    (hmon : ∀ n s, DirectSum.of (H ℤ (space m)) n (b n s) = monomial C a m s.val)
    (hdual : ∀ n s t, evaluate (space m) n (b n s) (B.basis m n t) = if s = t then 1 else 0) :
    Presentation C e o a B m := by
  letI := (C.ring (space m)).gradedRing
  letI := (C.ring (space m)).algebra
  let bTotal := totalMonomialBasis C m b
  have hbTotal (s : Finset (Fin m)) :
      bTotal s = ((s.sort (· ≤ ·)).map (generator a m)).prod := by
    change totalMonomialBasis C m b s = _
    rw [totalMonomialBasis_apply C m s.card b ⟨s,rfl⟩, hmon]
    rfl
  let E := exteriorEquivOfBasis f (generator a m) hf bTotal hbTotal
  refine ⟨E, hf, ?_, hsq, hanti, ?_⟩
  · intro n
    let g : Hc (space m) n →+ HStar ℤ (space m) := DirectSum.of (H ℤ (space m)) n
    let l : Hc (space m) n →ₗ[ℤ] HStar ℤ (space m) := {
      toFun := g
      map_add' := g.map_add
      map_smul' r v := by
        simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul g ℤ ℤ r v }
    have h : ∀ s : Set.powersetCard (Fin m) n,
        f ((Pi.basisFun ℤ (Fin m)).ExteriorAlgebra s.val) = l (b n s) := by
      intro s
      change f ((Pi.basisFun ℤ (Fin m)).ExteriorAlgebra s.val) = DirectSum.of _ n (b n s)
      exact (map_exterior_basis f (generator a m) hf s.val).trans (hmon n s).symm
    change f '' (↑(⋀[ℤ]^n (Fin m → ℤ)) : Set (ExteriorAlgebra ℤ (Fin m → ℤ))) = Set.range l
    exact exterior_homogeneous_image f l (b n) h
  · intro n
    exact ⟨b n, hmon n, hdual n⟩

end P202.Cohomology.TorusRing



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped TensorProduct DirectSum
namespace P202.Cohomology.TorusRing
open P202Specs.TorusRing P202Specs.SingularChains
open P202Specs.CupProduct P202Specs.CohomologyPairs
open P202Specs.AlexanderWhitney P202Specs.EilenbergZilber
open P202Specs.TopologicalKunneth

@[simp] theorem sort_map_castSucc {m : ℕ} (s : Finset (Fin m)) :
    (s.map Fin.castSuccEmb).sort (· ≤ ·) = (s.sort (· ≤ ·)).map Fin.castSucc := by
  exact (Finset.map_sort Fin.castSuccEmb s (fun i j : Fin m => i ≤ j)
    (fun i j : Fin (m+1) => i ≤ j) (fun _ _ _ _ => Iff.rfl)).symm

@[simp] theorem sort_insert_last {m : ℕ} (s : Finset (Fin m)) :
    (insert (Fin.last m) (s.map Fin.castSuccEmb)).sort (· ≤ ·) =
      (s.sort (· ≤ ·)).map Fin.castSucc ++ [Fin.last m] := by
  let l := (s.sort (· ≤ ·)).map Fin.castSucc
  have hn : (l ++ [Fin.last m]).Nodup := by
    simp only [List.nodup_append, List.nodup_singleton, true_and]
    constructor
    · exact (s.sort_nodup _).map (Fin.castSucc_injective m)
    · intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst y
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      exact Fin.castSucc_ne_last z
  have hs : (l ++ [Fin.last m]).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · exact List.Pairwise.map Fin.castSucc (fun i j hij => hij) (s.pairwise_sort (· ≤ ·))
    · intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst y
      exact Fin.le_last _
  have h := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hs
  have hset : (l ++ [Fin.last m]).toFinset = insert (Fin.last m) (s.map Fin.castSuccEmb) := by
    ext i
    simp [l, Finset.mem_map]
  rwa [hset] at h

@[simp] theorem append_projection_castSucc (m : ℕ) (i : Fin m) :
    append m ≫ projection (m+1) i.castSucc = firstProjection (space m) circle ≫ projection m i := by
  ext z
  change (Fin.snoc (α := fun _ => Circle) z.1 z.2 i.castSucc).val = (z.1 i).val
  exact congrArg Subtype.val (Fin.snoc_castSucc (α := fun _ => Circle) z.2 z.1 i)

@[simp] theorem append_projection_last (m : ℕ) :
    append m ≫ projection (m+1) (Fin.last m) = secondProjection (space m) circle := by
  ext z
  change (Fin.snoc (α := fun _ => Circle) z.1 z.2 (Fin.last m)).val = z.2.val
  exact congrArg Subtype.val (Fin.snoc_last (α := fun _ => Circle) z.2 z.1)

@[simp] theorem hPullback_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (a : Hc Z n) :
    hPullback ℤ (f ≫ g) n a = hPullback ℤ f n (hPullback ℤ g n a) := by
  simp only [hPullback, op_comp, Functor.map_comp, ModuleCat.hom_comp]
  rfl

@[simp] theorem pullback_generator_castSucc (C : NaturalCohomologyRing ℤ)
    (a : Hc circle 1) (m : ℕ) (i : Fin m) :
    C.pullback (append m) (generator a (m+1) i.castSucc) =
      C.pullback (firstProjection (space m) circle) (generator a m i) := by
  simp only [generator, coordinateClass, C.pullback_homogeneous]
  rw [← hPullback_comp, ← hPullback_comp, append_projection_castSucc]

@[simp] theorem pullback_generator_last (C : NaturalCohomologyRing ℤ)
    (a : Hc circle 1) (m : ℕ) :
    C.pullback (append m) (generator a (m+1) (Fin.last m)) =
      C.pullback (secondProjection (space m) circle) (DirectSum.of (H ℤ circle) 1 a) := by
  simp only [generator, coordinateClass, C.pullback_homogeneous]
  rw [← hPullback_comp, append_projection_last]

/-- Deleting an inactive final coordinate pulls an ordered monomial back
from the first factor, preserving its order. -/
theorem pullback_monomial_inactive (C : NaturalCohomologyRing ℤ)
    (a : Hc circle 1) (m n : ℕ) (s : ActiveSet m n) :
    C.pullback (append m) (monomial C a (m+1) (inactive s).val) =
      C.pullback (firstProjection (space m) circle) (monomial C a m s.val) := by
  letI := (C.ring (space m)).gradedRing
  letI := (C.ring (space m)).algebra
  letI := (C.ring (space (m+1))).gradedRing
  letI := (C.ring (space (m+1))).algebra
  letI := (C.ring (productSpace (space m) circle)).gradedRing
  letI := (C.ring (productSpace (space m) circle)).algebra
  simp only [monomial, inactive, sort_map_castSucc, List.map_map, map_list_prod]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact pullback_generator_castSucc C a m i

/-- The active final coordinate is appended on the right of the ordered cup
monomial, giving the positive product orientation. -/
theorem pullback_monomial_active (C : NaturalCohomologyRing ℤ)
    (a : Hc circle 1) (m n : ℕ) (s : ActiveSet m n) :
    letI := (C.ring (productSpace (space m) circle)).gradedRing
    C.pullback (append m) (monomial C a (m+1) (active s).val) =
      C.pullback (firstProjection (space m) circle) (monomial C a m s.val) *
      C.pullback (secondProjection (space m) circle) (DirectSum.of (H ℤ circle) 1 a) := by
  letI := (C.ring (space m)).gradedRing
  letI := (C.ring (space m)).algebra
  letI := (C.ring (space (m+1))).gradedRing
  letI := (C.ring (space (m+1))).algebra
  letI := (C.ring (productSpace (space m) circle)).gradedRing
  letI := (C.ring (productSpace (space m) circle)).algebra
  simp only [monomial, active, sort_insert_last, List.map_append,
    List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
    map_mul, pullback_generator_last, List.map_map, map_list_prod]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i hi
  exact pullback_generator_castSucc C a m i

end P202.Cohomology.TorusRing

namespace P202.Cohomology.TorusRing
open P202Specs.TorusRing P202Specs.SingularChains
open P202Specs.CupProduct P202Specs.CohomologyPairs
open P202Specs.AlexanderWhitney P202Specs.EilenbergZilber
open P202Specs.TopologicalKunneth

/-- The homogeneous inactive monomial pulls back from the first factor. -/
theorem pullback_monomialClass_inactive (C : NaturalCohomologyRing ℤ)
    (a : Hc circle 1) (m n : ℕ) (s : ActiveSet m n) :
    hPullback ℤ (append m) n (monomialClass C a (m+1) n (inactive s)) =
      hPullback ℤ (firstProjection (space m) circle) n (monomialClass C a m n s) := by
  letI := (C.ring (productSpace (space m) circle)).gradedRing
  apply DirectSum.of_injective (β := P202Specs.CupProduct.H ℤ (productSpace (space m) circle)) n
  rw [← C.pullback_homogeneous, ← C.pullback_homogeneous,
    of_monomialClass, of_monomialClass, pullback_monomial_inactive]

/-- The homogeneous active monomial is the external cup product in bidegree
(n,1), with the final circle factor ordered on the right. -/
theorem pullback_monomialClass_active (C : NaturalCohomologyRing ℤ)
    (a : Hc circle 1) (m n : ℕ) (s : ActiveSet m n) :
    hPullback ℤ (append m) (n+1) (monomialClass C a (m+1) (n+1) (active s)) =
      (C.ring (productSpace (space m) circle)).product n 1
        (hPullback ℤ (firstProjection (space m) circle) n (monomialClass C a m n s))
        (hPullback ℤ (secondProjection (space m) circle) 1 a) := by
  letI := (C.ring (productSpace (space m) circle)).gradedRing
  apply DirectSum.of_injective (β := P202Specs.CupProduct.H ℤ (productSpace (space m) circle)) (n+1)
  rw [← C.pullback_homogeneous, of_monomialClass, pullback_monomial_active,
    ← of_monomialClass C a m n s, C.pullback_homogeneous, C.pullback_homogeneous,
    DirectSum.of_mul_of, (C.ring (productSpace (space m) circle)).product_eq]

/-- The inactive monomial can also be expressed as an external cup product
in bidegree (n,0), so mixed bidegrees use the same pairing theorem. -/
theorem pullback_monomialClass_inactive_product (C : NaturalCohomologyRing ℤ)
    (a : Hc circle 1) (m n : ℕ) (s : ActiveSet m n) :
    letI := (C.ring circle).gradedRing
    hPullback ℤ (append m) n (monomialClass C a (m+1) n (inactive s)) =
      (C.ring (productSpace (space m) circle)).product n 0
        (hPullback ℤ (firstProjection (space m) circle) n (monomialClass C a m n s))
        (hPullback ℤ (secondProjection (space m) circle) 0 (GradedMonoid.GOne.one : Hc circle 0)) := by
  letI := (C.ring circle).gradedRing
  letI := (C.ring circle).algebra
  letI := (C.ring (space m)).gradedRing
  letI := (C.ring (space m)).algebra
  letI := (C.ring (productSpace (space m) circle)).gradedRing
  letI := (C.ring (productSpace (space m) circle)).algebra
  rw [pullback_monomialClass_inactive]
  apply DirectSum.of_injective (β := P202Specs.CupProduct.H ℤ (productSpace (space m) circle)) n
  have hof (x : Hc (productSpace (space m) circle) n) (y : Hc (productSpace (space m) circle) 0) :
      DirectSum.of (H ℤ (productSpace (space m) circle)) n
        ((C.ring (productSpace (space m) circle)).product n 0 x y) =
      DirectSum.of (H ℤ (productSpace (space m) circle)) n x *
        DirectSum.of (H ℤ (productSpace (space m) circle)) 0 y := by
    rw [DirectSum.of_mul_of, (C.ring (productSpace (space m) circle)).product_eq]
    simp only [Nat.add_zero]
  rw [hof, ← C.pullback_homogeneous (secondProjection (space m) circle) 0
    (GradedMonoid.GOne.one : Hc circle 0)]
  have hu : DirectSum.of (H ℤ circle) 0 (GradedMonoid.GOne.one : Hc circle 0) =
      (1 : HStar ℤ circle) := rfl
  rw [hu, map_one, mul_one]

end P202.Cohomology.TorusRing

namespace P202.Cohomology.TorusRing

open P202Specs.EilenbergZilber

/-- The normalized product pairings give the entire graded exterior ring,
including the point case and the prescribed duality of bases. -/
theorem ring_of_product_pairings
    (h : ∀ (C : NaturalCohomologyRing ℤ) (e : ExternalProduct ℤ)
      (o : Orientation) (m n : ℕ) (s t : ActiveSet m n),
      evaluate (space m) n (monomialClass C (orientedClass o) m n s)
        (productCycle e o m n t) = if s = t then 1 else 0) :
    P202Specs.TorusRing.Expected.ring := by
  classical
  refine ⟨orientation, ?_⟩
  intro C e o
  let a := orientedClass o
  let q := fun m n => homologyCoordinates m n (Classical.choice (homologyRanks m n))
  let φ := fun m n s => evaluate (space m) n (monomialClass C a m n s)
  let B := productBasisOfBiorthogonal e o q φ (h C e o)
  refine ⟨a, B, evaluate_orientedClass o, ?_⟩
  intro m
  have hδ (n : ℕ) (s t : ActiveSet m n) :
      evaluate (space m) n (monomialClass C a m n s) (B.basis m n t) =
        if s = t then 1 else 0 := by
    change evaluate (space m) n (monomialClass C a m n s)
      ((productBasisOfBiorthogonal e o q φ (h C e o)).basis m n t) = _
    rw [productBasisOfBiorthogonal_basis]
    exact h C e o m n s t
  have hb (n : ℕ) := monomial_basis_of_pairing C a m n (B.basis m n) (hδ n)
  choose b hmon hdual using hb
  obtain ⟨f, hf⟩ := exteriorMap C a m
  exact presentationOfMonomialBasis C e o a B m f hf (squares C a m)
    (fun i j => anticommutation C (space m) (coordinateClass a m i) (coordinateClass a m j))
    b hmon hdual

end P202.Cohomology.TorusRing

namespace P202.Cohomology.TorusRing
open P202Specs.TorusRing P202Specs.SingularChains
open P202Specs.CupProduct P202Specs.CohomologyPairs
open P202Specs.AlexanderWhitney P202Specs.EilenbergZilber
open P202Specs.TopologicalKunneth

def unitClass (C : NaturalCohomologyRing.{0,0} ℤ) (X : TopCat.{0}) : Hc X 0 :=
  letI := (C.ring X).gradedRing
  GradedMonoid.GOne.one

@[simp] theorem hPullback_unitClass (C : NaturalCohomologyRing.{0,0} ℤ)
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    hPullback ℤ f 0 (unitClass C Y) = unitClass C X := by
  letI := (C.ring X).gradedRing
  letI := (C.ring X).algebra
  letI := (C.ring Y).gradedRing
  letI := (C.ring Y).algebra
  apply DirectSum.of_injective (β := P202Specs.CupProduct.H ℤ X) 0
  calc
    DirectSum.of (P202Specs.CupProduct.H ℤ X) 0 (hPullback ℤ f 0 (unitClass C Y)) =
      C.pullback f (DirectSum.of (P202Specs.CupProduct.H ℤ Y) 0 (unitClass C Y)) :=
        (C.pullback_homogeneous f 0 (unitClass C Y)).symm
    _ = 1 := by change C.pullback f 1 = 1; exact map_one _
    _ = DirectSum.of (P202Specs.CupProduct.H ℤ X) 0 (unitClass C X) := rfl

@[simp] theorem product_unitClass (C : NaturalCohomologyRing.{0,0} ℤ)
    (X : TopCat.{0}) (n : ℕ) (d : Hc X n) :
    (C.ring X).product n 0 d (unitClass C X) = d := by
  letI := (C.ring X).gradedRing
  apply DirectSum.of_injective (β := P202Specs.CupProduct.H ℤ X) n
  have h : DirectSum.of (P202Specs.CupProduct.H ℤ X) n d * (1 : HStar ℤ X) = DirectSum.of _ n d := mul_one _
  change DirectSum.of (P202Specs.CupProduct.H ℤ X) n d * DirectSum.of (P202Specs.CupProduct.H ℤ X) 0 (unitClass C X) = _ at h
  rw [DirectSum.of_mul_of, (C.ring X).product_eq] at h
  exact h

/-- Pullback from the first factor is its external cohomology product with the unit. -/
theorem firstPullback_product_unit (C : NaturalCohomologyRing.{0,0} ℤ)
    (X Y : TopCat.{0}) (n : ℕ) (d : Hc X n) :
    (C.ring (productSpace X Y)).product n 0
      (hPullback ℤ (firstProjection X Y) n d)
      (hPullback ℤ (secondProjection X Y) 0 (unitClass C Y)) =
    hPullback ℤ (firstProjection X Y) n d := by
  rw [hPullback_unitClass, product_unitClass]

/-- Pulling back from the first factor preserves evaluation on a product with
any positive point class in the second factor. -/
theorem evaluate_firstPullback_external_point
    (C : NaturalCohomologyRing.{0,0} ℤ) (e : ExternalProduct.{0,0} ℤ)
    (X Y : TopCat.{0}) (n : ℕ) (d : Hc X n) (z : Hm X n) (y : Y) :
    evaluate (productSpace X Y) n (hPullback ℤ (firstProjection X Y) n d)
      (ordinaryExternal ℤ e X Y n 0 (z ⊗ₜ[ℤ] pointClass Y y)) =
    evaluate X n d z := by
  have h := evaluate_external_product C e X Y n 0 d (unitClass C Y) z (pointClass Y y)
  rw [firstPullback_product_unit] at h
  have hu : evaluate Y 0 (unitClass C Y) (pointClass Y y) = 1 := unit_evaluate_pointClass C Y y
  rw [hu, mul_one] at h
  exact h

/-- A class pulled back from the first factor pairs to zero when the second
homology factor has positive degree one. -/
theorem evaluate_firstPullback_external_one
    (C : NaturalCohomologyRing.{0,0} ℤ) (e : ExternalProduct.{0,0} ℤ)
    (X Y : TopCat.{0}) (n : ℕ) (d : Hc X (n+1)) (z : Hm X n) (w : Hm Y 1) :
    evaluate (productSpace X Y) (n+1) (hPullback ℤ (firstProjection X Y) (n+1) d)
      (ordinaryExternal ℤ e X Y n 1 (z ⊗ₜ[ℤ] w)) = 0 := by
  have h := evaluate_external_product_mismatched C e X Y (n+1) 0 n 1 rfl
    (Or.inr (by decide)) d (unitClass C Y) z w
  change evaluate (productSpace X Y) (n+1)
    ((C.ring (productSpace X Y)).product (n+1) 0
      (hPullback ℤ (firstProjection X Y) (n+1) d)
      (hPullback ℤ (secondProjection X Y) 0 (unitClass C Y))) _ = 0 at h
  rw [firstPullback_product_unit] at h
  exact h

end P202.Cohomology.TorusRing

-- DELTA INDUCTION
namespace P202.Cohomology.TorusRing
open P202Specs.TorusRing

@[simp] theorem inactive_inj {m n : ℕ} {s t : ActiveSet m n} :
    inactive s = inactive t ↔ s = t := by
  constructor
  · intro h
    apply Subtype.ext
    have hh := congrArg (fun u : ActiveSet (m+1) n => dropLast u.val) h
    simpa only [inactive, dropLast_map] using hh
  · exact congrArg inactive

@[simp] theorem active_inj {m n : ℕ} {s t : ActiveSet m n} :
    active s = active t ↔ s = t := by
  constructor
  · intro h
    apply Subtype.ext
    have hh := congrArg (fun u : ActiveSet (m+1) (n+1) => dropLast u.val) h
    simpa only [active, dropLast_insert, dropLast_map] using hh
  · exact congrArg active

@[simp] theorem inactive_ne_active {m n : ℕ} (s : ActiveSet m (n+1)) (t : ActiveSet m n) :
    inactive s ≠ active t := by
  intro h
  have hh := congrArg (fun u : ActiveSet (m+1) (n+1) => Fin.last m ∈ u.val) h
  simpa only [inactive, active, last_notMem_map, Finset.mem_insert_self, eq_iff_iff,
    false_iff, not_true_eq_false] using hh

@[simp] theorem active_ne_inactive {m n : ℕ} (s : ActiveSet m n) (t : ActiveSet m (n+1)) :
    active s ≠ inactive t := (inactive_ne_active t s).symm

/-- The four final-coordinate cases reduce the square-free pairing matrix to
its value on the empty product. -/
theorem delta_of_recursion
    (D : ∀ m n, ActiveSet m n → ActiveSet m n → ℤ)
    (hzero : D 0 0 ⟨∅,rfl⟩ ⟨∅,rfl⟩ = 1)
    (hii : ∀ m n (s t : ActiveSet m n),
      D (m+1) n (inactive s) (inactive t) = D m n s t)
    (haa : ∀ m n (s t : ActiveSet m n),
      D (m+1) (n+1) (active s) (active t) = D m n s t)
    (hia : ∀ m n (s : ActiveSet m (n+1)) (t : ActiveSet m n),
      D (m+1) (n+1) (inactive s) (active t) = 0)
    (hai : ∀ m n (s : ActiveSet m n) (t : ActiveSet m (n+1)),
      D (m+1) (n+1) (active s) (inactive t) = 0) :
    ∀ m n s t, D m n s t = if s = t then 1 else 0 := by
  classical
  intro m
  induction m with
  | zero =>
    intro n s t
    have hsval : s.val = ∅ := by ext i; exact Fin.elim0 i
    have hn : n = 0 := by simpa only [hsval, Finset.card_empty] using s.property.symm
    subst n
    have hs : s = ⟨∅,rfl⟩ := Subtype.ext hsval
    have ht : t = ⟨∅,rfl⟩ := by apply Subtype.ext; exact Finset.card_eq_zero.mp t.property
    subst s
    subst t
    simpa only [ite_true] using hzero
  | succ m ih =>
    intro n s t
    cases n with
    | zero =>
      have hs : Fin.last m ∉ s.val := by rw [Finset.card_eq_zero.mp s.property]; simp
      have ht : Fin.last m ∉ t.val := by rw [Finset.card_eq_zero.mp t.property]; simp
      conv_lhs => rw [← inactive_dropInactive s hs, ← inactive_dropInactive t ht]
      rw [hii, ih]
      have he : dropInactive s hs = dropInactive t ht ↔ s = t := by
        simpa only [inactive_dropInactive] using
          (inactive_inj (s := dropInactive s hs) (t := dropInactive t ht)).symm
      simp only [he]
    | succ n =>
      by_cases hs : Fin.last m ∈ s.val
      · by_cases ht : Fin.last m ∈ t.val
        · conv_lhs => rw [← active_dropActive s hs, ← active_dropActive t ht]
          rw [haa, ih]
          have he : dropActive s hs = dropActive t ht ↔ s = t := by
            simpa only [active_dropActive] using
              (active_inj (s := dropActive s hs) (t := dropActive t ht)).symm
          simp only [he]
        · conv_lhs => rw [← active_dropActive s hs, ← inactive_dropInactive t ht]
          rw [hai]
          have hst : s ≠ t := by intro he; apply ht; simpa only [← he] using hs
          simp only [hst, ite_false]
      · by_cases ht : Fin.last m ∈ t.val
        · conv_lhs => rw [← inactive_dropInactive s hs, ← active_dropActive t ht]
          rw [hia]
          have hst : s ≠ t := by intro he; apply hs; simpa only [he] using ht
          simp only [hst, ite_false]
        · conv_lhs => rw [← inactive_dropInactive s hs, ← inactive_dropInactive t ht]
          rw [hii, ih]
          have he : dropInactive s hs = dropInactive t ht ↔ s = t := by
            simpa only [inactive_dropInactive] using
              (inactive_inj (s := dropInactive s hs) (t := dropInactive t ht)).symm
          simp only [he]

end P202.Cohomology.TorusRing


namespace P202.Cohomology.TorusRing
open P202Specs.TorusRing P202Specs.SingularChains
open P202Specs.CupProduct P202Specs.CohomologyPairs
open P202Specs.AlexanderWhitney P202Specs.EilenbergZilber
open P202Specs.TopologicalKunneth

-- ACTUAL DELTA PAIRING
/-- Ordered square-free cup monomials are dual to the prescribed product cycles. -/
theorem monomial_productCycle_pairing
    (C : NaturalCohomologyRing ℤ) (e : ExternalProduct ℤ) (o : Orientation) :
    ∀ m n (s t : ActiveSet m n),
      evaluate (space m) n (monomialClass C (orientedClass o) m n s)
        (productCycle e o m n t) = if s = t then 1 else 0 := by
  classical
  let a := orientedClass o
  let D := fun m n (s t : ActiveSet m n) =>
    evaluate (space m) n (monomialClass C a m n s) (productCycle e o m n t)
  apply delta_of_recursion D
  · letI := (C.ring (space 0)).gradedRing
    have hu : monomialClass C a 0 0 ⟨∅,rfl⟩ =
        (GradedMonoid.GOne.one : Hc (space 0) 0) := by
      apply DirectSum.of_injective (β := H ℤ (space 0)) 0
      rw [of_monomialClass]
      simp only [monomial, Finset.sort_empty, List.map_nil, List.prod_nil]
      rfl
    change evaluate (space 0) 0 _ _ = 1
    rw [productCycle_zero, hu]
    exact unit_evaluate_pointClass C (space 0) (fun _ => 1)
  · intro m n s t
    change evaluate (space (m+1)) n _ _ = _
    rw [productCycle_inactive, ← evaluate_natural, pullback_monomialClass_inactive,
      evaluate_firstPullback_external_point C e]
  · intro m n s t
    change evaluate (space (m+1)) (n+1) _ _ = _
    rw [productCycle_active, ← evaluate_natural, pullback_monomialClass_active,
      evaluate_external_product C e]
    change _ * evaluate circle 1 (orientedClass o) (o.symm 1) = _
    rw [orientedClass_generator, mul_one]
  · intro m n s t
    change evaluate (space (m+1)) (n+1) _ _ = 0
    rw [productCycle_active, ← evaluate_natural, pullback_monomialClass_inactive]
    exact evaluate_firstPullback_external_one C e (space m) circle n
      (monomialClass C a m (n+1) s) (productCycle e o m n t) (o.symm 1)
  · intro m n s t
    change evaluate (space (m+1)) (n+1) _ _ = 0
    rw [productCycle_inactive, ← evaluate_natural, pullback_monomialClass_active]
    exact evaluate_external_product_mismatched C e (space m) circle n 1 (n+1) 0 rfl
      (Or.inr (by decide)) (monomialClass C a m n s) a
      (productCycle e o m (n+1) t) (pointClass circle 1)

end P202.Cohomology.TorusRing

namespace P202.Cohomology.TorusRing

/-- The integral cohomology of every finite torus is the exterior algebra on
its oriented coordinate classes, with its ordered product-dual bases. -/
theorem ring : P202Specs.TorusRing.Expected.ring :=
  ring_of_product_pairings monomial_productCycle_pairing

end P202.Cohomology.TorusRing
