import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.TransverseThomProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.EilenbergZilber
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.CupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SpheresDisks
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.ThomClass
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.TransverseNormalCoordinates
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.LocalThomProjection
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Basic.Unique

/-! Ordered relative evaluation, genuine union-relative cup representatives,
empty support, the nullary unit, orientation-dual normal-fiber cycles, finite
ordered model orientation generators, and the full smooth transverse-family
conclusion on every normalized normal slice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped TensorProduct Topology
universe u w v
namespace P202.TransverseThomProduct
open P202Specs.SingularChains P202Specs.AlexanderWhitney
  P202Specs.ShuffleModel P202Specs.CupProduct P202Specs.EilenbergZilber
  P202Specs.TransverseThomProduct
variable (R : Type u) [CommRing R]

lemma pairing_leftBoundary {X Y : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q) (ha : delta R X p a = 0)
    (z : Summand R X Y (p+1) q) :
    tensorPairing R a b (leftBoundary R X Y p q z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul c d =>
    change a (chainBoundary R X p c) * b d = 0
    have h := LinearMap.congr_fun ha c
    change a (chainBoundary R X p c) = 0 at h
    rw [h, zero_mul]
  | add z z' hz hz' => simp only [map_add, hz, hz', add_zero]

lemma pairing_rightBoundary {X Y : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q) (hb : delta R Y q b = 0)
    (z : Summand R X Y p (q+1)) :
    tensorPairing R a b (rightBoundary R X Y p q z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul c d =>
    change a c * b (chainBoundary R Y q d) = 0
    have h := LinearMap.congr_fun hb d
    change b (chainBoundary R Y q d) = 0 at h
    rw [h, mul_zero]
  | add z z' hz hz' => simp only [map_add, hz, hz', add_zero]

lemma orderedPairing_boundary {X Y : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q)
    (ha : delta R X p a = 0) (hb : delta R Y q b = 0)
    (n : ℕ) (h : p+q=n) (z : Total R X Y (n+1)) :
    orderedPairing R a b n h (totalBoundary R X Y n z) = 0 := by
  change tensorPairing R a b
    (leftBoundary R X Y p q (z ⟨(p+1,q),by omega⟩) +
      (-1 : ℤ)^p • rightBoundary R X Y p q (z ⟨(p,q+1),by omega⟩)) = 0
  rw [map_add, map_zsmul, pairing_leftBoundary R a b ha,
    pairing_rightBoundary R a b hb, smul_zero, add_zero]

lemma orderedPairing_tensorPair {X Y : TopCat.{w}} {p q : ℕ}
    (A : Set X) (B : Set Y) (a : Cochain R X p) (b : Cochain R Y q)
    (ha : VanishesOn R A a) (hb : VanishesOn R B b)
    (n : ℕ) (h : p+q=n) (z : Total R X Y n)
    (hz : z ∈ tensorPair R X Y A B n) : orderedPairing R a b n h z = 0 := by
  change z ∈ LinearMap.range (totalMap R (subspaceInclusion X A) (𝟙 Y) n) ⊔
    LinearMap.range (totalMap R (𝟙 X) (subspaceInclusion Y B) n) at hz
  rw [Submodule.mem_sup] at hz
  obtain ⟨l, ⟨l', rfl⟩, r, ⟨r', rfl⟩, rfl⟩ := hz
  rw [map_add]
  have hl : ∀ t : Summand R (TopCat.of A) Y p q,
      tensorPairing R a b
        (TensorProduct.map ((chainMap R R (subspaceInclusion X A)).f p).hom
          ((chainMap R R (𝟙 Y)).f q).hom t) = 0 := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c d => change a _ * b _ = 0; rw [ha, zero_mul]
    | add s t hs ht => simp only [map_add, hs, ht, add_zero]
  have hr : ∀ t : Summand R X (TopCat.of B) p q,
      tensorPairing R a b
        (TensorProduct.map ((chainMap R R (𝟙 X)).f p).hom
          ((chainMap R R (subspaceInclusion Y B)).f q).hom t) = 0 := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c d => change a _ * b _ = 0; rw [hb, mul_zero]
    | add s t hs ht => simp only [map_add, hs, ht, add_zero]
  change tensorPairing R a b _ + tensorPairing R a b _ = 0
  exact (congrArg₂ (· + ·) (hl _) (hr _)).trans (add_zero 0)

/-- Both relative faces are respected by the very same natural tensor homotopy. -/
lemma orderedPairing_homotopy_face {X Y : TopCat.{w}} {p q n : ℕ}
    (A : Set X) (B : Set Y) (a : Cochain R X p) (b : Cochain R Y q)
    (ha : VanishesOn R A a) (hb : VanishesOn R B b)
    (H : TensorHomotopy.{u,w} R) (h : p+q=n+1)
    (z : Total R X Y n) (hz : z ∈ tensorPair R X Y A B n) :
    orderedPairing R a b (n+1) h (H.hom X Y n z) = 0 := by
  obtain ⟨K, _, _, _⟩ := P202.EilenbergZilber.naturalHomotopies R
  have hf := (P202.EilenbergZilber.relativeCompatibility R K H X Y A B n).2.2.2
  apply orderedPairing_tensorPair R A B a b ha hb
  exact hf (Submodule.mem_map_of_mem hz)

lemma externalCochain_aw (X Y : TopCat.{w}) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R Y q) (c : Chains R (productSpace X Y) (p+q)) :
    externalCochain R X Y p q a b c =
      orderedPairing R a b (p+q) rfl (aw R X Y (p+q) c) := by
  have h : externalCochain R X Y p q a b =
      (orderedPairing R a b (p+q) rfl).comp (aw R X Y (p+q)) := by
    apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R (productSpace X Y) (p+q))).ext
    intro s
    change externalCochain R X Y p q a b (Finsupp.single s 1) = _
    simp only [externalCochain, P202.CupProduct.cup_single, pullback,
      LinearMap.lcomp_apply, LinearMap.comp_apply, one_mul]
    change a (((chainMap R R (firstProjection X Y)).f p).hom _) *
      b (((chainMap R R (secondProjection X Y)).f q).hom _) = _
    rw [P202.SingularChains.chainMap_single, P202.SingularChains.chainMap_single]
    change _ = tensorPairing R a b (aw R X Y (p+q) (Finsupp.single s 1) ⟨(p,q),rfl⟩)
    rw [P202.AlexanderWhitney.formula]
    simp only [one_smul, awComponent, P202.CupProduct.tensorPairing_tmul]
    rw [← P202.AlexanderWhitney.post_interval, ← P202.AlexanderWhitney.post_interval]
    rfl
  exact LinearMap.congr_fun h c

/-- AW/shuffle evaluation on every relative total cycle. -/
theorem relativeTensorEvaluation : P202Specs.TransverseThomProduct.evaluation_type.{u,w} := by
  intro R _ X Y A B p q a b ha hb hA hB z hz
  rw [externalCochain_aw]
  obtain ⟨_, H, _, _⟩ := P202.EilenbergZilber.naturalHomotopies R
  have eval : ∀ (n : ℕ) (hn : p+q=n) (z : Total R X Y n),
      IsRelativeTensorCycle R X Y A B n z →
      orderedPairing R a b n hn (aw R X Y n (shuffle R X Y n z)) =
        orderedPairing R a b n hn z := by
    intro n hn z hz
    cases n with
    | zero =>
      have he := congrArg (orderedPairing R a b 0 hn)
        (LinearMap.congr_fun (H.zero X Y) z)
      dsimp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply] at he
      rw [map_sub, orderedPairing_boundary R a b ha hb] at he
      exact sub_eq_zero.mp he
    | succ n =>
      have he := congrArg (orderedPairing R a b (n+1) hn)
        (LinearMap.congr_fun (H.succ X Y n) z)
      dsimp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
        LinearMap.add_apply] at he
      rw [map_sub, map_add, orderedPairing_boundary R a b ha hb, zero_add] at he
      have hf := orderedPairing_homotopy_face R A B a b hA hB H hn _ hz
      rw [hf] at he
      exact sub_eq_zero.mp he
  
  exact eval (p+q) rfl z hz


lemma single_face_left {X Y : TopCat.{w}} (A : Set X) (B : Set Y)
    (n : ℕ) (i : Diagonal n) (c : Chains R X i.val.1) (d : Chains R Y i.val.2)
    (hc : c ∈ LinearMap.range ((chainMap R R (subspaceInclusion X A)).f i.val.1).hom) :
    Pi.single i (c ⊗ₜ[R] d) ∈ tensorPair R X Y A B n := by
  classical
  obtain ⟨c', rfl⟩ := hc
  apply Submodule.mem_sup_left
  refine ⟨Pi.single i (c' ⊗ₜ[R] d), ?_⟩
  rw [P202.EZTensorHomotopy.totalMap_single]
  simp only [TensorProduct.map_tmul, P202.EZTensorHomotopy.push,
    P202.SingularChains.chainMap_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]
  rfl

lemma single_face_right {X Y : TopCat.{w}} (A : Set X) (B : Set Y)
    (n : ℕ) (i : Diagonal n) (c : Chains R X i.val.1) (d : Chains R Y i.val.2)
    (hd : d ∈ LinearMap.range ((chainMap R R (subspaceInclusion Y B)).f i.val.2).hom) :
    Pi.single i (c ⊗ₜ[R] d) ∈ tensorPair R X Y A B n := by
  classical
  obtain ⟨d', rfl⟩ := hd
  apply Submodule.mem_sup_right
  refine ⟨Pi.single i (c ⊗ₜ[R] d'), ?_⟩
  rw [P202.EZTensorHomotopy.totalMap_single]
  simp only [TensorProduct.map_tmul, P202.EZTensorHomotopy.push,
    P202.SingularChains.chainMap_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]
  rfl

/-- The boundary of the ordered tensor of relative cycles lies in the sum
of the two faces. Degree zero has no augmented boundary. -/
lemma pureTensor_relativeCycle {X Y : TopCat.{w}} (A : Set X) (B : Set Y)
    (p q : ℕ) (c : Chains R X p) (d : Chains R Y q)
    (hc : IsRelativeCycle R X A p c) (hd : IsRelativeCycle R Y B q d) :
    IsRelativeTensorCycle R X Y A B (p+q)
      (Pi.single (⟨(p,q),rfl⟩ : Diagonal (p+q)) (c ⊗ₜ[R] d)) := by
  classical
  have aux : ∀ (n : ℕ) (h : p+q=n),
      IsRelativeTensorCycle R X Y A B n
        (Pi.single (⟨(p,q),h⟩ : Diagonal n) (c ⊗ₜ[R] d)) := by
    intro n h
    cases p with
    | zero =>
      cases q with
      | zero =>
        have hn : n = 0 := by omega
        subst hn
        trivial
      | succ q =>
        have hn : n = q+1 := by omega
        subst hn
        change totalBoundary R X Y q _ ∈ tensorPair R X Y A B q
        rw [P202.ShuffleBoundary.totalBoundary_single_zero_left]
        change Pi.single (⟨(0,q),by omega⟩ : Diagonal q)
          (c ⊗ₜ[R] boundary R R Y q d) ∈ tensorPair R X Y A B q
        exact single_face_right R A B q ⟨(0,q),by omega⟩ c _ hd
    | succ p =>
      cases q with
      | zero =>
        have hn : n = p+1 := by omega
        subst hn
        change totalBoundary R X Y p _ ∈ tensorPair R X Y A B p
        rw [P202.ShuffleBoundary.totalBoundary_single_zero_right]
        change Pi.single (⟨(p,0),rfl⟩ : Diagonal p)
          (boundary R R X p c ⊗ₜ[R] d) ∈ tensorPair R X Y A B p
        exact single_face_left R A B p ⟨(p,0),rfl⟩ _ d hc
      | succ q =>
        have hn : n = (p+q+1)+1 := by omega
        subst hn
        change totalBoundary R X Y (p+q+1) _ ∈ tensorPair R X Y A B (p+q+1)
        rw [P202.ShuffleBoundary.totalBoundary_single_positive]
        exact (tensorPair R X Y A B (p+q+1)).add_mem
          (single_face_left R A B (p+q+1) ⟨(p,q+1), by omega⟩ _ d hc)
          ((tensorPair R X Y A B (p+q+1)).toAddSubgroup.zsmul_mem
            (single_face_right R A B (p+q+1) ⟨(p+1,q), by omega⟩ c _ hd) _)
  exact aux (p+q) rfl

/-- The scalar product formula before specializing evaluations to one. -/
theorem evaluation_pureTensor {X Y : TopCat.{w}}
    (A : Set X) (B : Set Y) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R Y q)
    (c : Chains R X p) (d : Chains R Y q)
    (ha : delta R X p a = 0) (hb : delta R Y q b = 0)
    (hA : VanishesOn R A a) (hB : VanishesOn R B b)
    (hc : IsRelativeCycle R X A p c) (hd : IsRelativeCycle R Y B q d) :
    externalCochain R X Y p q a b
      (shuffleComponent R X Y p q (c ⊗ₜ[R] d)) = a c * b d := by
  classical
  have he := relativeTensorEvaluation R X Y A B p q a b ha hb hA hB _
    (pureTensor_relativeCycle R A B p q c d hc hd)
  rw [P202.ShuffleBoundary.shuffle_single] at he
  simpa only [castChains, orderedPairing, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.single_eq_same, LinearMap.id_apply,
    P202.CupProduct.tensorPairing_tmul] using he


lemma chainMap_range_in_subspace {X Y : TopCat.{w}} (f : X ⟶ Y)
    (A : Set Y) (hf : ∀ x, f x ∈ A) (n : ℕ) :
    LinearMap.range ((chainMap R R f).f n).hom ≤
      LinearMap.range ((chainMap R R (subspaceInclusion Y A)).f n).hom := by
  let g : X ⟶ TopCat.of A := TopCat.ofHom
    ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have hfg : f = g ≫ subspaceInclusion Y A := rfl
  rw [hfg, P202.SingularChains.chainMap_comp]
  exact LinearMap.range_comp_le_range _ _

lemma productPair_le_union (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (n : ℕ) :
    productPair R X Y A B n ≤
      LinearMap.range
        ((chainMap R R (subspaceInclusion (productSpace X Y) (productFaces X Y A B))).f n).hom := by
  apply sup_le
  · exact chainMap_range_in_subspace R
      (productMap (subspaceInclusion X A) (𝟙 Y)) (productFaces X Y A B)
      (fun z => Or.inl z.1.property) n
  · exact chainMap_range_in_subspace R
      (productMap (𝟙 X) (subspaceInclusion Y B)) (productFaces X Y A B)
      (fun z => Or.inr z.2.property) n

lemma shuffle_relativeCycle (X Y : TopCat.{w}) (A : Set X) (B : Set Y)
    (n : ℕ) (z : Total R X Y n) (hz : IsRelativeTensorCycle R X Y A B n z) :
    IsRelativeCycle R (productSpace X Y) (productFaces X Y A B) n
      (shuffle R X Y n z) := by
  cases n with
  | zero => trivial
  | succ n =>
    change boundary R R (productSpace X Y) n _ ∈ _
    have hc := LinearMap.congr_fun (P202.ShuffleBoundary.chain_identity R X Y n) z
    change boundary R R (productSpace X Y) n (shuffle R X Y (n+1) z) =
      shuffle R X Y n (totalBoundary R X Y n z) at hc
    rw [hc]
    obtain ⟨K, H, _, _⟩ := P202.EilenbergZilber.naturalHomotopies R
    apply productPair_le_union R X Y A B n
    exact (P202.EilenbergZilber.relativeCompatibility R K H X Y A B n).2.1
      (Submodule.mem_map_of_mem hz)

lemma shuffleComponent_relativeCycle {X Y : TopCat.{w}} (A : Set X) (B : Set Y)
    (p q : ℕ) (c : Chains R X p) (d : Chains R Y q)
    (hc : IsRelativeCycle R X A p c) (hd : IsRelativeCycle R Y B q d) :
    IsRelativeCycle R (productSpace X Y) (productFaces X Y A B) (p+q)
      (shuffleComponent R X Y p q (c ⊗ₜ[R] d)) := by
  have h := shuffle_relativeCycle R X Y A B (p+q) _
    (pureTensor_relativeCycle R A B p q c d hc hd)
  rw [P202.ShuffleBoundary.shuffle_single] at h
  exact h

lemma externalCochain_vanishes_productPair {X Y : TopCat.{w}} {p q : ℕ}
    (A : Set X) (B : Set Y) (a : Cochain R X p) (b : Cochain R Y q)
    (ha : VanishesOn R A a) (hb : VanishesOn R B b)
    (c : Chains R (productSpace X Y) (p+q)) (hc : c ∈ productPair R X Y A B (p+q)) :
    externalCochain R X Y p q a b c = 0 := by
  rw [externalCochain_aw]
  obtain ⟨K, H, _, _⟩ := P202.EilenbergZilber.naturalHomotopies R
  apply orderedPairing_tensorPair R A B a b ha hb
  exact (P202.EilenbergZilber.relativeCompatibility R K H X Y A B (p+q)).1
    (Submodule.mem_map_of_mem hc)


open CategoryTheory.Limits P202Specs.RelativeSingularChains P202Specs.CohomologyPairs

/-- The full pair has zero cohomology in every integer degree. -/
lemma fullPair_cohomology (X : TopCat.{w}) (n : ℤ) :
    IsZero (relativeCohomology R R (⟨X,Set.univ⟩ : Pair) n) := by
  let P : Pair := ⟨X,Set.univ⟩
  let e : P.sub ≅ X := TopCat.isoOfHomeo (Homeomorph.Set.univ X)
  have he : P.inclusion = e.hom := rfl
  haveI : IsIso P.inclusion := he ▸ inferInstance
  haveI : IsIso (inclusion (ordinaryFunctor R R) P) :=
    inferInstanceAs (IsIso ((ordinaryFunctor R R).map P.inclusion))
  haveI : IsIso ((inclusion (ordinaryFunctor R R) P).f n) :=
    inferInstanceAs (IsIso ((HomologicalComplex.eval _ _ n).map
      (inclusion (ordinaryFunctor R R) P)))
  have hz : IsZero ((ordinary R R P).X n) :=
    (isZero_cokernel_of_epi _).of_iso (degreeQuotientIso (ordinaryFunctor R R) P n)
  have hc : IsZero ((relativeCochains R R P).X n) :=
    P202.CohomologyPairs.dual_isZero R R _ hz
  exact ((relativeCochains R R P).sc n).isZero_homology_of_isZero_X₂ hc

/-- This endpoint needs no geometric or orientation hypotheses. -/
lemma emptySupport_cohomology : P202Specs.TransverseThomProduct.emptySupport_type.{u,w} := by
  intro R _ X s hs n
  subst s
  simpa only [Set.compl_empty] using fullPair_cohomology R X n

/-- Closed auxiliary target with the original coefficient and space universes. -/
theorem evaluation : P202Specs.TransverseThomProduct.evaluation_type.{u,w} := by
  exact relativeTensorEvaluation

/-- Closed auxiliary target with the original coefficient and space universes. -/
theorem evaluationOne : P202Specs.TransverseThomProduct.evaluationOne_type.{u,w} := by
  intro R _ X Y A B p q a b c d ha hb hA hB hc hd hac hbd
  rw [evaluation_pureTensor R A B p q a b c d ha hb hA hB hc hd, hac, hbd, one_mul]

/-- Closed auxiliary target with the original coefficient and space universes. -/
theorem emptySupport : P202Specs.TransverseThomProduct.emptySupport_type.{u,w} := by
  exact emptySupport_cohomology



section RelativeCocycleRepresentatives
open P202Specs.RelativeCupProduct
lemma relativeCocycleValue_toAbsolute (P : Pair.{w}) (n : ℕ)
    (a : (relativeCochains R R P).cycles (n : ℤ)) :
    relativeCocycleValue R P n a = cocycleValue R P.space n
      (HomologicalComplex.cyclesMap (relativeToAbsolute R R P) (n : ℤ) a) := by
  have h := congrArg (fun ff => ff a)
    (HomologicalComplex.cyclesMap_i (relativeToAbsolute R R P) (n : ℤ))
  exact (congrArg (ordinaryCochainsEquiv R R P.space n) h).symm

lemma relativeCocycleValue_delta (P : Pair.{w}) (n : ℕ)
    (a : (relativeCochains R R P).cycles (n : ℤ)) :
    delta R P.space n (relativeCocycleValue R P n a) = 0 := by
  rw [relativeCocycleValue_toAbsolute]
  exact P202.CupProduct.cocycleValue_delta R P.space n _

lemma relativeCocycleValue_vanishesOn (P : Pair.{w}) (n : ℕ)
    (a : (relativeCochains R R P).cycles (n : ℤ)) :
    VanishesOn R P.subspace (relativeCocycleValue R P n a) := by
  intro c
  change ordinaryCochainsEquiv R R P.space n
    ((relativeToAbsolute R R P).f (n : ℤ)
      ((relativeCochains R R P).iCycles (n : ℤ) a))
    (((chainMap R R P.inclusion).f n).hom c) = 0
  rw [← P202.CohomologyPairs.quotient_identification R R P n]
  have hzero : (Submodule.Quotient.mk
      (((chainMap R R P.inclusion).f n).hom c) : chainQuotient R R P n) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨c, rfl⟩
  rw [hzero, map_zero]

lemma relativeCocycleValue_pullback {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ)
    (a : (relativeCochains R R Q).cycles (n : ℤ)) :
    relativeCocycleValue R P n (HomologicalComplex.cyclesMap
      ((relativeCochainFunctor R R).map f.op) (n : ℤ) a) =
        pullback R f.map n (relativeCocycleValue R Q n a) := by
  have h := congrArg (fun ff => ff a)
    (HomologicalComplex.cyclesMap_i ((relativeCochainFunctor R R).map f.op) (n : ℤ))
  change (relativeCochains R R P).iCycles (n : ℤ)
      (HomologicalComplex.cyclesMap ((relativeCochainFunctor R R).map f.op) (n : ℤ) a) =
    (((relativeCochainFunctor R R).map f.op).f (n : ℤ))
      ((relativeCochains R R Q).iCycles (n : ℤ) a) at h
  unfold relativeCocycleValue
  rw [h]
  have hs := (cochainSequenceMap R R f).comm₁₂
  have hd := congrArg (fun ff => ff.f (n : ℤ)) hs
  change ((relativeCochainFunctor R R).map f.op).f (n : ℤ) ≫
      (relativeToAbsolute R R P).f (n : ℤ) =
    (relativeToAbsolute R R Q).f (n : ℤ) ≫
      ((ordinaryCochainFunctor R R).map f.map.op).f (n : ℤ) at hd
  have he := congrArg (fun ff => ff ((relativeCochains R R Q).iCycles (n : ℤ) a)) hd
  rw [show (relativeToAbsolute R R P).f (n : ℤ)
      (((relativeCochainFunctor R R).map f.op).f (n : ℤ)
        ((relativeCochains R R Q).iCycles (n : ℤ) a)) =
      ((ordinaryCochainFunctor R R).map f.map.op).f (n : ℤ)
        ((relativeToAbsolute R R Q).f (n : ℤ)
          ((relativeCochains R R Q).iCycles (n : ℤ) a)) from he]
  exact P202.CupProduct.ordinaryCochainsEquiv_pullback R f.map n _


lemma relativePullback_homologyπ {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ)
    (a : (relativeCochains R R Q).cycles (n : ℤ)) :
    relativePullback R f n ((relativeCochains R R Q).homologyπ (n : ℤ) a) =
      (relativeCochains R R P).homologyπ (n : ℤ)
        (HomologicalComplex.cyclesMap ((relativeCochainFunctor R R).map f.op) (n : ℤ) a) := by
  exact congrArg (fun ff => ff a)
    (HomologicalComplex.homologyπ_naturality ((relativeCochainFunctor R R).map f.op) (n : ℤ))

lemma sumCocycleValue_toAbsolute (P : TwoSubspaces.{w}) (n : ℕ)
    (a : (sumCochains R P).cycles (n : ℤ)) :
    sumCocycleValue R P n a = cocycleValue R P.space n
      (HomologicalComplex.cyclesMap (sumToAbsolute R P) (n : ℤ) a) := by
  have h := congrArg (fun ff => ff a)
    (HomologicalComplex.cyclesMap_i (sumToAbsolute R P) (n : ℤ))
  exact (congrArg (ordinaryCochainsEquiv R R P.space n) h).symm

lemma sumCocycleValue_delta (P : TwoSubspaces.{w}) (n : ℕ)
    (a : (sumCochains R P).cycles (n : ℤ)) :
    delta R P.space n (sumCocycleValue R P n a) = 0 := by
  rw [sumCocycleValue_toAbsolute]
  exact P202.CupProduct.cocycleValue_delta R P.space n _

lemma unionComparison_toAbsolute (P : TwoSubspaces.{w}) :
    unionComparison R P ≫ sumToAbsolute R P = relativeToAbsolute R R P.unionPair := by
  dsimp only [unionComparison, sumToAbsolute, relativeToAbsolute]
  rw [← Functor.map_comp, ← op_comp]
  congr 1
  congr 1
  simp only [sumProjection, sumToUnion, CategoryTheory.Limits.cokernel.π_desc]

lemma sumCocycleValue_unionComparison (P : TwoSubspaces.{w}) (n : ℕ)
    (a : (relativeCochains R R P.unionPair).cycles (n : ℤ)) :
    sumCocycleValue R P n
        (HomologicalComplex.cyclesMap (unionComparison R P) (n : ℤ) a) =
      relativeCocycleValue R P.unionPair n a := by
  have h := congrArg (fun ff => ff a)
    (HomologicalComplex.cyclesMap_i (unionComparison R P) (n : ℤ))
  change (sumCochains R P).iCycles (n : ℤ)
      (HomologicalComplex.cyclesMap (unionComparison R P) (n : ℤ) a) =
    (unionComparison R P).f (n : ℤ)
      ((relativeCochains R R P.unionPair).iCycles (n : ℤ) a) at h
  unfold sumCocycleValue relativeCocycleValue
  rw [h]
  have hd := congrArg (fun ff => ff.f (n : ℤ)) (unionComparison_toAbsolute R P)
  exact congrArg (ordinaryCochainsEquiv R R P.space n)
    (congrArg (fun ff => ff ((relativeCochains R R P.unionPair).iCycles (n : ℤ) a)) hd)



lemma productPair_le_sumChains (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (n : ℕ) :
    productPair R X Y A B n ≤ sumChains R (productSubspaces X Y A B) n := by
  apply sup_le
  · apply le_sup_of_le_left
    exact chainMap_range_in_subspace R
      (productMap (subspaceInclusion X A) (𝟙 Y)) {z | z.1 ∈ A}
      (fun z => z.1.property) n
  · apply le_sup_of_le_right
    exact chainMap_range_in_subspace R
      (productMap (𝟙 X) (subspaceInclusion Y B)) {z | z.2 ∈ B}
      (fun z => z.2.property) n

lemma shuffle_sumRelativeCycle (X Y : TopCat.{w}) (A : Set X) (B : Set Y)
    (n : ℕ) (z : Total R X Y n) (hz : IsRelativeTensorCycle R X Y A B n z) :
    IsSumRelativeCycle R (productSubspaces X Y A B) n (shuffle R X Y n z) := by
  cases n with
  | zero => trivial
  | succ n =>
    change boundary R R (productSpace X Y) n _ ∈ _
    have hc := LinearMap.congr_fun (P202.ShuffleBoundary.chain_identity R X Y n) z
    change boundary R R (productSpace X Y) n (shuffle R X Y (n+1) z) =
      shuffle R X Y n (totalBoundary R X Y n z) at hc
    rw [hc]
    obtain ⟨K, H, _, _⟩ := P202.EilenbergZilber.naturalHomotopies R
    apply productPair_le_sumChains R X Y A B n
    exact (P202.EilenbergZilber.relativeCompatibility R K H X Y A B n).2.1
      (Submodule.mem_map_of_mem hz)

lemma shuffleComponent_sumRelativeCycle {X Y : TopCat.{w}} (A : Set X) (B : Set Y)
    (p q : ℕ) (c : Chains R X p) (d : Chains R Y q)
    (hc : IsRelativeCycle R X A p c) (hd : IsRelativeCycle R Y B q d) :
    IsSumRelativeCycle R (productSubspaces X Y A B) (p+q)
      (shuffleComponent R X Y p q (c ⊗ₜ[R] d)) := by
  have h := shuffle_sumRelativeCycle R X Y A B (p+q) _
    (pureTensor_relativeCycle R A B p q c d hc hd)
  rw [P202.ShuffleBoundary.shuffle_single] at h
  exact h

/-- The prescribed relative cup product, after the genuine sum/union comparison,
has a cocycle representative evaluating to one on the ordered shuffled cycle.
The two individual input chains are actual relative cycles. -/
theorem relativeExternalProduct_evaluationOne (μ : NaturalRelativeCupProduct.{u,w} R)
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B)
    (p q : ℕ)
    (a : (relativeCochains R R (⟨X,A⟩ : Pair)).cycles (p : ℤ))
    (b : (relativeCochains R R (⟨Y,B⟩ : Pair)).cycles (q : ℤ))
    (c : Chains R X p) (d : Chains R Y q)
    (hc : IsRelativeCycle R X A p c) (hd : IsRelativeCycle R Y B q d)
    (hac : relativeCocycleValue R (⟨X,A⟩ : Pair) p a c = 1)
    (hbd : relativeCocycleValue R (⟨Y,B⟩ : Pair) q b d = 1) :
    ∃ e : (sumCochains R (productSubspaces X Y A B)).cycles ((p+q : ℕ) : ℤ),
      HomologicalComplex.homologyMap (unionComparison R (productSubspaces X Y A B))
        ((p+q : ℕ) : ℤ)
        (μ.product (productSubspaces X Y A B) (productSubspaces_isOpen X Y A B hA hB) p q
          (relativePullback R (productLeftProjection X Y A B) p
            ((relativeCochains R R (⟨X,A⟩ : Pair)).homologyπ (p : ℤ) a) ⊗ₜ[R]
           relativePullback R (productRightProjection X Y A B) q
            ((relativeCochains R R (⟨Y,B⟩ : Pair)).homologyπ (q : ℤ) b))) =
          (sumCochains R (productSubspaces X Y A B)).homologyπ ((p+q : ℕ) : ℤ) e ∧
      sumCocycleValue R (productSubspaces X Y A B) (p+q) e
        (shuffleComponent R X Y p q (c ⊗ₜ[R] d)) = 1 := by
  let f := productLeftProjection X Y A B
  let g := productRightProjection X Y A B
  let a' := HomologicalComplex.cyclesMap ((relativeCochainFunctor R R).map f.op) (p : ℤ) a
  let b' := HomologicalComplex.cyclesMap ((relativeCochainFunctor R R).map g.op) (q : ℤ) b
  obtain ⟨e, he, hclass⟩ := μ.represents (productSubspaces X Y A B)
    (productSubspaces_isOpen X Y A B hA hB) p q a' b'
  refine ⟨e, ?_, ?_⟩
  · rw [relativePullback_homologyπ, relativePullback_homologyπ]
    exact hclass
  · rw [he]
    dsimp only [a', b']
    rw [relativeCocycleValue_pullback, relativeCocycleValue_pullback]
    change externalCochain R X Y p q
      (relativeCocycleValue R (⟨X,A⟩ : Pair) p a)
      (relativeCocycleValue R (⟨Y,B⟩ : Pair) q b) _ = 1
    rw [evaluation_pureTensor R A B p q _ _ c d
      (relativeCocycleValue_delta R _ p a) (relativeCocycleValue_delta R _ q b)
      (relativeCocycleValue_vanishesOn R _ p a) (relativeCocycleValue_vanishesOn R _ q b)
      hc hd, hac, hbd, one_mul]

lemma sumProjection_vanishes (P : TwoSubspaces.{w}) (n : ℕ)
    (c : Chains R P.space n) (hc : c ∈ sumChains R P n) :
    (sumProjection R P).f (n : ℤ)
      ((ordinaryNonnegativeIso R R P.space n).inv c) = 0 := by
  have hl : inclusion (ordinaryFunctor R R) P.leftPair ≫ sumProjection R P = 0 := by
    have h := congrArg
      (fun ff => (CategoryTheory.Limits.biprod.inl :
        ordinaryComplex R R P.leftPair.sub ⟶ _) ≫ ff)
      (CategoryTheory.Limits.cokernel.condition (sumInclusion R P))
    simpa only [← Category.assoc, sumInclusion, sumProjection,
      CategoryTheory.Limits.biprod.inl_desc, comp_zero] using h
  have hr : inclusion (ordinaryFunctor R R) P.rightPair ≫ sumProjection R P = 0 := by
    have h := congrArg
      (fun ff => (CategoryTheory.Limits.biprod.inr :
        ordinaryComplex R R P.rightPair.sub ⟶ _) ≫ ff)
      (CategoryTheory.Limits.cokernel.condition (sumInclusion R P))
    simpa only [← Category.assoc, sumInclusion, sumProjection,
      CategoryTheory.Limits.biprod.inr_desc, comp_zero] using h
  have hleft (x : Chains R P.leftPair.sub n) :
      (sumProjection R P).f (n : ℤ)
        ((ordinaryNonnegativeIso R R P.space n).inv
          (((chainMap R R P.leftPair.inclusion).f n).hom x)) = 0 := by
    have hsq := congrArg (fun ff => ff x)
      (P202.CupProduct.ordinary_chainMap_degree R P.leftPair.inclusion n)
    change ((ordinaryFunctor R R).map P.leftPair.inclusion).f (n : ℤ)
        ((ordinaryNonnegativeIso R R P.leftPair.sub n).inv x) =
      (ordinaryNonnegativeIso R R P.space n).inv
        (((chainMap R R P.leftPair.inclusion).f n).hom x) at hsq
    rw [← hsq]
    exact congrArg
      (fun ff => ff.f (n : ℤ) ((ordinaryNonnegativeIso R R P.leftPair.sub n).inv x)) hl
  have hright (x : Chains R P.rightPair.sub n) :
      (sumProjection R P).f (n : ℤ)
        ((ordinaryNonnegativeIso R R P.space n).inv
          (((chainMap R R P.rightPair.inclusion).f n).hom x)) = 0 := by
    have hsq := congrArg (fun ff => ff x)
      (P202.CupProduct.ordinary_chainMap_degree R P.rightPair.inclusion n)
    change ((ordinaryFunctor R R).map P.rightPair.inclusion).f (n : ℤ)
        ((ordinaryNonnegativeIso R R P.rightPair.sub n).inv x) =
      (ordinaryNonnegativeIso R R P.space n).inv
        (((chainMap R R P.rightPair.inclusion).f n).hom x) at hsq
    rw [← hsq]
    exact congrArg
      (fun ff => ff.f (n : ℤ) ((ordinaryNonnegativeIso R R P.rightPair.sub n).inv x)) hr
  obtain ⟨l, ⟨l', rfl⟩, r, ⟨r', rfl⟩, rfl⟩ := Submodule.mem_sup.mp hc
  rw [map_add, map_add, hleft, hright, add_zero]

lemma sumCochainValue_vanishes (P : TwoSubspaces.{w}) (n : ℕ)
    (a : (sumCochains R P).X (n : ℤ))
    (c : Chains R P.space n) (hc : c ∈ sumChains R P n) :
    ordinaryCochainsEquiv R R P.space n ((sumToAbsolute R P).f (n : ℤ) a) c = 0 := by
  change (sumQuotient R P).X (n : ℤ) →ₗ[R] R at a
  change a ((sumProjection R P).f (n : ℤ)
    ((ordinaryNonnegativeIso R R P.space n).inv c)) = 0
  rw [sumProjection_vanishes R P n c hc, map_zero]

lemma sumCocycleValue_eq_zero_of_homologyπ_eq_zero_succ
    (P : TwoSubspaces.{w}) (n : ℕ)
    (a : (sumCochains R P).cycles ((n+1 : ℕ) : ℤ))
    (ha : (sumCochains R P).homologyπ ((n+1 : ℕ) : ℤ) a = 0)
    (z : Chains R P.space (n+1))
    (hz : boundary R R P.space n z ∈ sumChains R P n) :
    sumCocycleValue R P (n+1) a z = 0 := by
  change ((sumCochains R P).sc ((n+1 : ℕ) : ℤ)).homologyπ a = 0 at ha
  obtain ⟨x, hx⟩ := (P202.CupProduct.shortComplex_homologyπ_eq_zero_iff R
    ((sumCochains R P).sc ((n+1 : ℕ) : ℤ)) a).mp ha
  have hp : ((ComplexShape.down ℤ).symm).prev ((n+1 : ℕ) : ℤ) = (n : ℤ) :=
    ((ComplexShape.down ℤ).symm).prev_eq' (by simp)
  change (sumCochains R P).X (((ComplexShape.down ℤ).symm).prev ((n+1 : ℕ) : ℤ)) at x
  change (sumCochains R P).d _ ((n+1 : ℕ) : ℤ) x =
    (sumCochains R P).iCycles ((n+1 : ℕ) : ℤ) a at hx
  revert x
  rw [hp]
  intro x hx
  unfold sumCocycleValue
  rw [← hx]
  have hd := congrArg (fun ff => ff x)
    ((sumToAbsolute R P).comm (n : ℤ) ((n+1 : ℕ) : ℤ))
  change (ordinaryCochains R R P.space).d (n : ℤ) ((n+1 : ℕ) : ℤ)
      ((sumToAbsolute R P).f (n : ℤ) x) =
    (sumToAbsolute R P).f ((n+1 : ℕ) : ℤ)
      ((sumCochains R P).d (n : ℤ) ((n+1 : ℕ) : ℤ) x) at hd
  rw [← hd, P202.CupProduct.ordinaryCochainsEquiv_d]
  change ordinaryCochainsEquiv R R P.space n ((sumToAbsolute R P).f (n : ℤ) x)
    (boundary R R P.space n z) = 0
  exact sumCochainValue_vanishes R P n x _ hz

lemma sumCocycleValue_eq_zero_of_homologyπ_eq_zero_zero
    (P : TwoSubspaces.{w}) (a : (sumCochains R P).cycles 0)
    (ha : (sumCochains R P).homologyπ 0 a = 0)
    (z : Chains R P.space 0) : sumCocycleValue R P 0 a z = 0 := by
  let f := sumToAbsolute R P
  have hnat := congrArg (fun ff => ff a)
    (HomologicalComplex.homologyπ_naturality f 0)
  change (HomologicalComplex.homologyMap f 0) ((sumCochains R P).homologyπ 0 a) =
    (ordinaryCochains R R P.space).homologyπ 0
      (HomologicalComplex.cyclesMap f 0 a) at hnat
  rw [ha, map_zero] at hnat
  have hzero := (P202.CupProduct.homologyπ_eq_zero_iff_zero R P.space
    (HomologicalComplex.cyclesMap f 0 a)).mp hnat.symm
  calc
    sumCocycleValue R P 0 a z = cocycleValue R P.space 0
        (HomologicalComplex.cyclesMap f 0 a) z :=
      congrArg (fun ff => ff z) (sumCocycleValue_toAbsolute R P 0 a)
    _ = cocycleValue R P.space 0 0 z :=
      congrArg (fun aa => cocycleValue R P.space 0 aa z) hzero
    _ = 0 := congrArg (fun ff : Cochain R P.space 0 => ff z)
      ((P202.CupProduct.cocycleValueLinear R P.space 0).map_zero)

lemma sumCocycleValue_sub (P : TwoSubspaces.{w}) (n : ℕ)
    (a b : (sumCochains R P).cycles (n : ℤ)) :
    sumCocycleValue R P n (a-b) = sumCocycleValue R P n a - sumCocycleValue R P n b := by
  unfold sumCocycleValue
  simp only [map_sub]

lemma sumCocycleValue_eq_of_homologyπ_eq
    (P : TwoSubspaces.{w}) (n : ℕ)
    (a b : (sumCochains R P).cycles (n : ℤ))
    (hab : (sumCochains R P).homologyπ (n : ℤ) a =
      (sumCochains R P).homologyπ (n : ℤ) b)
    (z : Chains R P.space n) (hz : IsSumRelativeCycle R P n z) :
    sumCocycleValue R P n a z = sumCocycleValue R P n b z := by
  have hzero : (sumCochains R P).homologyπ (n : ℤ) (a-b) = 0 := by
    rw [map_sub, hab, sub_self]
  have heval : sumCocycleValue R P n (a-b) z = 0 := by
    cases n with
    | zero => exact sumCocycleValue_eq_zero_of_homologyπ_eq_zero_zero R P (a-b) hzero z
    | succ n => exact sumCocycleValue_eq_zero_of_homologyπ_eq_zero_succ R P n (a-b) hzero z hz
  rw [sumCocycleValue_sub, LinearMap.sub_apply] at heval
  exact sub_eq_zero.mp heval


/-- Evaluation one for every cocycle of the genuine union-relative product. -/
theorem relativeProductEvaluation_of_representatives :
    P202Specs.TransverseThomProduct.relativeProductEvaluation_type.{u,w} := by
  intro R _ μ X Y A B hA hB p q a b c d hc hd hac hbd t ht
  obtain ⟨e, he, hev⟩ := relativeExternalProduct_evaluationOne
    R μ X Y A B hA hB p q a b c d hc hd hac hbd
  let t' := HomologicalComplex.cyclesMap
    (unionComparison R (productSubspaces X Y A B)) ((p+q : ℕ) : ℤ) t
  have hclass : (sumCochains R (productSubspaces X Y A B)).homologyπ
      ((p+q : ℕ) : ℤ) t' =
      (sumCochains R (productSubspaces X Y A B)).homologyπ ((p+q : ℕ) : ℤ) e := by
    have hn := congrArg (fun ff => ff t)
      (HomologicalComplex.homologyπ_naturality
        (unionComparison R (productSubspaces X Y A B)) ((p+q : ℕ) : ℤ))
    change HomologicalComplex.homologyMap (unionComparison R (productSubspaces X Y A B))
        ((p+q : ℕ) : ℤ)
        ((relativeCochains R R (productSubspaces X Y A B).unionPair).homologyπ
          ((p+q : ℕ) : ℤ) t) =
      (sumCochains R (productSubspaces X Y A B)).homologyπ ((p+q : ℕ) : ℤ) t' at hn
    rw [ht, he] at hn
    exact hn.symm
  have hval := sumCocycleValue_eq_of_homologyπ_eq R (productSubspaces X Y A B) (p+q)
    t' e hclass (shuffleComponent R X Y p q (c ⊗ₜ[R] d))
    (shuffleComponent_sumRelativeCycle R A B p q c d hc hd)
  dsimp only [t'] at hval
  rw [sumCocycleValue_unionComparison] at hval
  exact hval.trans hev

end RelativeCocycleRepresentatives

section GeometricSupport
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
variable {n k : ℕ} {M : TopCat.{w}} {S : SmoothManifold n .euclidean M}

lemma support_isClosed (N : OrientedSubmanifold R M S) : IsClosed N.support := by
  letI := S.topologicalManifold.hausdorff
  letI := N.compact
  obtain ⟨e, he⟩ := N.embedding.2.2.2
  have hi : Continuous N.inclusion := by
    have hf : N.inclusion = fun p => (e p).val := funext fun p => (he p).symm
    rw [hf]
    exact continuous_subtype_val.comp e.continuous
  exact (isCompact_range hi).isClosed

lemma complement_isOpen (N : OrientedSubmanifold R M S) : IsOpen N.supportᶜ :=
  (support_isClosed R N).isOpen_compl

lemma intersection_isClosed (F : Fin k → OrientedSubmanifold R M S) :
    IsClosed (intersectionSupport R F) :=
  isClosed_iInter fun j => support_isClosed R (F j)

lemma intersectionComplement_isOpen (F : Fin k → OrientedSubmanifold R M S) :
    IsOpen (intersectionSupport R F)ᶜ :=
  (intersection_isClosed R F).isOpen_compl

lemma intersectionComplement (F : Fin k → OrientedSubmanifold R M S) :
    (intersectionSupport R F)ᶜ = ⋃ j, (F j).supportᶜ := by
  simp only [intersectionSupport, Set.compl_iInter]


set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
/-- Every individual quotient normal projection is surjective. -/
lemma normalProjectionAt_surjective (N : OrientedSubmanifold R M S)
    (p : N.source) (x : M) (h : N.inclusion p = x) :
    Function.Surjective (normalProjectionAt R N p x h) := by
  cases h
  exact Submodule.Quotient.mk_surjective _

/-- For one member mutual transversality adds no assumption. -/
lemma singleton_isTransverse (F : Fin 1 → OrientedSubmanifold R M S) :
    IsTransverse R F := by
  intro x p h v
  obtain ⟨z, hz⟩ := normalProjectionAt_surjective R (F 0) (p 0) x (h 0) (v 0)
  refine ⟨z, ?_⟩
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact hz

/-- The zero-member tangent projection has the zero vector as a preimage. -/
lemma empty_isTransverse (F : Fin 0 → OrientedSubmanifold R M S) :
    IsTransverse R F := by
  intro x p h v
  exact ⟨0, funext fun j => Fin.elim0 j⟩

end GeometricSupport

section NormalProjectionGeometry
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData SmoothManifolds.TangentData
attribute [local instance] normalTopology
variable {R : Type u} [CommRing R] {n k : ℕ} {M : TopCat.{w}}
  {S : SmoothManifold n .euclidean M}

def normalProjectionLinearMap (N : OrientedSubmanifold R M S)
    (p : N.source) (x : M) (h : N.inclusion p = x) :
    TangentSpace S x →ₗ[ℝ] NormalFiber N.normal p := by
  subst x
  exact
    { toFun := Submodule.Quotient.mk
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

lemma normalProjectionLinearMap_apply (N : OrientedSubmanifold R M S)
    (p : N.source) (x : M) (h : N.inclusion p = x) (v : TangentSpace S x) :
    normalProjectionLinearMap N p x h v = normalProjectionAt R N p x h v := by
  subst x
  rfl

def combinedNormalProjection (F : Fin k → OrientedSubmanifold R M S)
    (x : M) (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x) :
    TangentSpace S x →ₗ[ℝ] (∀ j, NormalFiber (F j).normal (p j)) :=
  LinearMap.pi (fun j => normalProjectionLinearMap (F j) (p j) x (h j))

lemma combinedNormalProjection_surjective (F : Fin k → OrientedSubmanifold R M S)
    (hF : IsTransverse R F) (x : M) (p : ∀ j, (F j).source)
    (h : ∀ j, (F j).inclusion (p j) = x) :
    Function.Surjective (combinedNormalProjection F x p h) := by
  have heq : (combinedNormalProjection F x p h : TangentSpace S x → _) =
      (fun v => fun j => normalProjectionAt R (F j) (p j) x (h j) v) := by
    funext v j
    exact normalProjectionLinearMap_apply (F j) (p j) x (h j) v
  rw [heq]
  exact hF x p h

lemma normalFiber_dimension (N : OrientedSubmanifold R M S) (p : N.source) :
    FiniteDimensional ℝ (NormalFiber N.normal p) ∧
      Module.finrank ℝ (NormalFiber N.normal p) = N.codimension := by
  obtain ⟨a, ha⟩ := (normalBundle N.normal).covers p
  let e := P202Specs.ThomClass.fiberLinearCoordinates N.normal a p ha
  constructor
  · exact Module.Finite.equiv e.symm
  · rw [e.finrank_eq, N.rank p]
    simp [Euclidean]

lemma totalCodimension_le (F : Fin k → OrientedSubmanifold R M S)
    (hF : IsTransverse R F) (x : M) (p : ∀ j, (F j).source)
    (h : ∀ j, (F j).inclusion (p j) = x) :
    totalCodimension R F ≤ n := by
  cases k with
  | zero => simp [totalCodimension]
  | succ k =>
    obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 x
    let e := (F 0).normal.ambientTangent.fiberCoordinates.equiv c hc x hxc
    letI : FiniteDimensional ℝ (TangentSpace S x) := Module.Finite.equiv e.symm
    letI : ∀ j : Fin (k+1), FiniteDimensional ℝ (NormalFiber (F j).normal (p j)) :=
      fun j => (normalFiber_dimension (F j) (p j)).1
    have hdim := LinearMap.finrank_le_finrank_of_surjective
      (combinedNormalProjection_surjective F hF x p h)
    rw [Module.finrank_pi_fintype, e.finrank_eq] at hdim
    have hcodim : (∑ j : Fin (k+1), Module.finrank ℝ (NormalFiber (F j).normal (p j))) =
        totalCodimension R F := by
      unfold totalCodimension
      exact Finset.sum_congr rfl (fun j _ => (normalFiber_dimension (F j) (p j)).2)
    rw [hcodim] at hdim
    simpa [Euclidean] using hdim

lemma intersection_eq_empty_of_dimension_lt (F : Fin k → OrientedSubmanifold R M S)
    (hF : IsTransverse R F) (hdim : n < totalCodimension R F) :
    intersectionSupport R F = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hp : ∀ j, ∃ p : (F j).source, (F j).inclusion p = x := by
    intro j
    exact (Set.mem_iInter.mp hx j)
  choose p h using hp
  exact (not_le_of_gt hdim) (totalCodimension_le F hF x p h)

lemma embeddedData_projection (N : OrientedSubmanifold R M S)
    (p : N.source) (x : M) (h : N.inclusion p = x) (v : TangentSpace S x) :
    P202Specs.TransverseNormalCoordinates.normalProjection (N.embeddedData R) p x h v =
      normalProjectionAt R N p x h v := by
  subst x
  rfl

end NormalProjectionGeometry

/-- The original mutual-transversality hypothesis is exactly the hypothesis
of the proved smooth simultaneous-coordinate theorem. -/
theorem normalCoordinates :
    P202Specs.TransverseThomProduct.normalCoordinates_type.{u,w} := by
  intro R _ n k M S F hF x p h
  apply P202.TransverseNormalCoordinates.simultaneousCoordinates
    n k M S (fun j => (F j).embeddedData R) x p h
  intro z
  obtain ⟨v,hv⟩ := hF x p h z
  refine ⟨v, ?_⟩
  funext j
  change P202Specs.TransverseNormalCoordinates.normalProjection
    ((F j).embeddedData R) (p j) x (h j) v = z j
  rw [embeddedData_projection]
  exact congrFun hv j


section LocalNormalSections
open Filter Set
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Local normal slice preserves every target coordinate exactly, with no target reparametrization. -/
theorem exists_local_section (f : E → F) (L : E →L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f L a) (hL : Function.Surjective L)
    (V : Set E) (hV : IsOpen V) (haV : a ∈ V) :
    ∃ U : Set F, IsOpen U ∧ f a ∈ U ∧
      ∃ s : F → E, ContinuousOn s U ∧ s (f a) = a ∧
        (∀ y ∈ U, s y ∈ V ∧ f (s y) = y) ∧ Set.InjOn s U := by
  have hL' : L.range = ⊤ := LinearMap.range_eq_top.mpr hL
  let e := hf.implicitToOpenPartialHomeomorph f L hL'
  let j : F → F × L.ker := fun y => (y, 0)
  have hj : Continuous j := continuous_id.prodMk continuous_const
  let W := e.target ∩ e.symm ⁻¹' V
  have hW : IsOpen W := e.symm.isOpen_inter_preimage hV
  let U := j ⁻¹' W
  have hU : IsOpen U := hW.preimage hj
  have hcenter : e a = (f a, 0) := hf.implicitToOpenPartialHomeomorph_self hL'
  have ha : a ∈ e.source := hf.mem_implicitToOpenPartialHomeomorph_source hL'
  have hfa : f a ∈ U := by
    change (f a, 0) ∈ e.target ∩ e.symm ⁻¹' V
    rw [← hcenter]
    refine ⟨e.map_source ha, ?_⟩
    change e.symm (e a) ∈ V
    rwa [e.left_inv ha]
  let s : F → E := fun y => e.symm (j y)
  have hs : ContinuousOn s U := e.symm.continuousOn.comp hj.continuousOn (fun _ hy => hy.1)
  refine ⟨U, hU, hfa, s, hs, ?_, ?_, ?_⟩
  · change e.symm (f a, 0) = a
    rw [← hcenter, e.left_inv ha]
  · intro y hy
    refine ⟨hy.2, ?_⟩
    have he : e (e.symm (j y)) = j y := e.right_inv hy.1
    have hp := congrArg Prod.fst he
    exact hp
  · intro y hy z hz heq
    have he := congrArg e heq
    change e (e.symm (j y)) = e (e.symm (j z)) at he
    rw [e.right_inv hy.1, e.right_inv hz.1] at he
    exact congrArg Prod.fst he

/-- Inverting a normalized full tubular differential recovers the actual quotient normal projection. -/
theorem inverse_normal_derivative
    {B N A C Q : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [AddCommGroup Q] [Module ℝ Q]
    (coord : (B × N) ≃L[ℝ] A) (quot : C →ₗ[ℝ] Q) (fiber : Q ≃ₗ[ℝ] N)
    (J : A →L[ℝ] C) (I : C →L[ℝ] A)
    (hJI : J.comp I = ContinuousLinearMap.id ℝ C)
    (hJ : ∀ b v, quot (J (coord (b, v))) = fiber.symm v) :
    ∀ w, (coord.symm (I w)).2 = fiber (quot w) := by
  intro w
  have hh := hJ (coord.symm (I w)).1 (coord.symm (I w)).2
  rw [Prod.eta, coord.apply_symm_apply] at hh
  have hi : J (I w) = w := congrArg (fun A => A w) hJI
  rw [hi] at hh
  have hv := congrArg fiber hh
  simpa only [LinearEquiv.apply_symm_apply] using hv.symm

end LocalNormalSections

/-- Empty-intersection endpoint for every finite ordered family. -/
theorem emptyIntersection : P202Specs.TransverseThomProduct.emptyIntersection_type.{u,w} := by
  intro R _ n k M S F h q
  exact emptySupport_cohomology R M (intersectionSupport R F) h q


lemma relativeCycle_map {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ)
    (c : Chains R P.space n) (hc : IsRelativeCycle R P.space P.subspace n c) :
    IsRelativeCycle R Q.space Q.subspace n (((chainMap R R f.map).f n).hom c) := by
  cases n with
  | zero => trivial
  | succ n =>
    obtain ⟨z, hz⟩ := hc
    refine ⟨((chainMap R R f.restrict).f n).hom z, ?_⟩
    have hs := inclusion_square (chainFunctor R R) f
    have hs' := congrArg (fun g => g.f n) hs
    have hd := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (P202.SingularChains.chainMap_boundary R R f.map n)) c
    change boundary R R Q.space n (((chainMap R R f.map).f (n+1)).hom c) =
      ((chainMap R R f.map).f n).hom (boundary R R P.space n c) at hd
    rw [hd, ← hz]
    exact congrArg (fun k => k z) (congrArg ModuleCat.Hom.hom hs'.symm)


section RelativeCycleLifts
open HomologicalComplex P202Specs.RelativeCupProduct
def relativeChainProjection (P : Pair.{w}) (n : ℕ) :
    Chains R P.space n →ₗ[R] (ordinary R R P).X (n : ℤ) :=
  ((projection (ordinaryFunctor R R) P).f (n : ℤ)).hom.comp
    (ordinaryNonnegativeIso R R P.space n).inv.hom

lemma relativeChainProjection_surjective (P : Pair.{w}) (n : ℕ) :
    Function.Surjective (relativeChainProjection R P n) := by
  have h := (P202.RelativeSingularChains.ordinary_short_exact R R P (n : ℤ)).moduleCat_surjective_g
  exact h.comp (ordinaryNonnegativeIso R R P.space n).toLinearEquiv.symm.surjective

lemma relativeChainProjection_eq_zero_iff (P : Pair.{w}) (n : ℕ)
    (c : Chains R P.space n) :
    relativeChainProjection R P n c = 0 ↔
      c ∈ LinearMap.range ((chainMap R R P.inclusion).f n).hom := by
  have h := (P202.RelativeSingularChains.ordinary_short_exact R R P (n : ℤ)).exact.moduleCat_range_eq_ker
  change LinearMap.range ((inclusion (ordinaryFunctor R R) P).f (n : ℤ)).hom =
    LinearMap.ker ((projection (ordinaryFunctor R R) P).f (n : ℤ)).hom at h
  change ((ordinaryNonnegativeIso R R P.space n).inv c) ∈
    LinearMap.ker ((projection (ordinaryFunctor R R) P).f (n : ℤ)).hom ↔ _
  rw [← h]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(ordinaryNonnegativeIso R R P.sub n).hom a, ?_⟩
    have hs := congrArg (fun ff => ff a) (ordinary_inclusion_degree R R P n)
    change (ordinaryNonnegativeIso R R P.space n).hom
      ((inclusion (ordinaryFunctor R R) P).f (n : ℤ) a) =
        ((chainMap R R P.inclusion).f n).hom
          ((ordinaryNonnegativeIso R R P.sub n).hom a) at hs
    rw [ha, ModuleCat.hom_inv_apply] at hs
    exact hs.symm
  · rintro ⟨a, rfl⟩
    refine ⟨(ordinaryNonnegativeIso R R P.sub n).inv a, ?_⟩
    apply (ordinaryNonnegativeIso R R P.space n).toLinearEquiv.injective
    change (ordinaryNonnegativeIso R R P.space n).hom _ =
      (ordinaryNonnegativeIso R R P.space n).hom _
    rw [ModuleCat.hom_inv_apply]
    have hs := congrArg (fun ff => ff ((ordinaryNonnegativeIso R R P.sub n).inv a))
      (ordinary_inclusion_degree R R P n)
    change (ordinaryNonnegativeIso R R P.space n).hom
      ((inclusion (ordinaryFunctor R R) P).f (n : ℤ)
        ((ordinaryNonnegativeIso R R P.sub n).inv a)) =
      ((chainMap R R P.inclusion).f n).hom
        ((ordinaryNonnegativeIso R R P.sub n).hom
          ((ordinaryNonnegativeIso R R P.sub n).inv a)) at hs
    rw [ModuleCat.hom_inv_apply] at hs
    exact hs

lemma relativeChainProjection_boundary (P : Pair.{w}) (n : ℕ)
    (c : Chains R P.space (n+1)) :
    (ordinary R R P).d ((n+1 : ℕ) : ℤ) (n : ℤ)
      (relativeChainProjection R P (n+1) c) =
        relativeChainProjection R P n (boundary R R P.space n c) := by
  have h := congrArg (fun ff => ff ((ordinaryNonnegativeIso R R P.space (n+1)).inv c))
    ((projection (ordinaryFunctor R R) P).comm ((n+1 : ℕ) : ℤ) (n : ℤ))
  change (ordinary R R P).d _ _ (relativeChainProjection R P (n+1) c) =
    (projection (ordinaryFunctor R R) P).f (n : ℤ)
      ((ordinaryComplex R R P.space).d _ _ ((ordinaryNonnegativeIso R R P.space (n+1)).inv c)) at h
  rw [h]
  change (projection (ordinaryFunctor R R) P).f (n : ℤ) _ =
    (projection (ordinaryFunctor R R) P).f (n : ℤ) _
  apply congrArg ((projection (ordinaryFunctor R R) P).f (n : ℤ))
  apply (ordinaryNonnegativeIso R R P.space n).toLinearEquiv.injective
  change (ordinaryNonnegativeIso R R P.space n).hom _ =
    (ordinaryNonnegativeIso R R P.space n).hom _
  erw [ModuleCat.hom_inv_apply]
  have hb := congrArg (fun ff => ff c) (P202.SingularChains.ordinary_boundary R R P.space n)
  change (ordinaryNonnegativeIso R R P.space n).hom
    ((ordinaryComplex R R P.space).d _ _ ((ordinaryNonnegativeIso R R P.space (n+1)).inv c)) =
      boundary R R P.space n c at hb
  exact hb

lemma relativeCycle_lift (P : Pair.{w}) (n : ℕ)
    (z : (ordinary R R P).X (n : ℤ))
    (hz : (ordinary R R P).d (n : ℤ) ((n : ℤ)-1) z = 0) :
    ∃ c : Chains R P.space n, relativeChainProjection R P n c = z ∧
      IsRelativeCycle R P.space P.subspace n c := by
  obtain ⟨c, hc⟩ := relativeChainProjection_surjective R P n z
  refine ⟨c, hc, ?_⟩
  cases n with
  | zero => trivial
  | succ n =>
    apply (relativeChainProjection_eq_zero_iff R P n _).mp
    have hn : (((n+1 : ℕ) : ℤ)-1) = (n : ℤ) := by omega
    rw [hn] at hz
    rw [← relativeChainProjection_boundary, hc, hz]

lemma relativeCocycleValue_projection (P : Pair.{w}) (n : ℕ)
    (a : (relativeCochains R R P).cycles (n : ℤ))
    (c : Chains R P.space n) :
    relativeCocycleValue R P n a c =
      (show (ordinary R R P).X (n : ℤ) →ₗ[R] R from
        (relativeCochains R R P).iCycles (n : ℤ) a) (relativeChainProjection R P n c) := rfl


lemma relativeChainProjection_isCycle (P : Pair.{w}) (n : ℕ)
    (c : Chains R P.space n) (hc : IsRelativeCycle R P.space P.subspace n c) :
    (ordinary R R P).d (n : ℤ) ((n : ℤ)-1) (relativeChainProjection R P n c) = 0 := by
  cases n with
  | zero =>
    have hz := (P202.RelativeSingularChains.ordinary_negative R R P (-1) (by omega)).1
    have hd := hz.eq_of_tgt ((ordinary R R P).d 0 (-1)) 0
    change (ordinary R R P).d 0 (-1) _ = 0
    rw [hd]
    rfl
  | succ n =>
    have hn : (((n+1 : ℕ) : ℤ)-1) = (n : ℤ) := by omega
    rw [hn, relativeChainProjection_boundary]
    exact (relativeChainProjection_eq_zero_iff R P n _).mpr hc

/-- Evaluation on cocycles at an actual relative cycle. -/
def relativeCycleCocycleEvaluation (P : Pair.{w}) (n : ℕ)
    (c : Chains R P.space n) :
    (relativeCochains R R P).cycles (n : ℤ) →ₗ[R] R :=
  (LinearMap.applyₗ (R := R) (relativeChainProjection R P n c)).comp
    ((relativeCochains R R P).iCycles (n : ℤ)).hom

lemma relativeCycleCocycleEvaluation_boundary (P : Pair.{w}) (n : ℕ)
    (c : Chains R P.space n) (hc : IsRelativeCycle R P.space P.subspace n c) :
    ((relativeCochains R R P).sc (n : ℤ)).toCycles ≫
      ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{w} R ≃ₗ[R] R).symm.toLinearMap.comp
        (relativeCycleCocycleEvaluation R P n c)) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  have hi := congrArg (fun ff => ff x)
    (((relativeCochains R R P).sc (n : ℤ)).toCycles_i)
  change (show (ordinary R R P).X (n : ℤ) →ₗ[R] R from
    ((relativeCochains R R P).sc (n : ℤ)).iCycles
      (((relativeCochains R R P).sc (n : ℤ)).toCycles x))
        (relativeChainProjection R P n c) = 0
  change ((relativeCochains R R P).sc (n : ℤ)).iCycles
    (((relativeCochains R R P).sc (n : ℤ)).toCycles x) =
      ((relativeCochains R R P).sc (n : ℤ)).f x at hi
  refine (congrArg (fun a : (relativeCochains R R P).X (n : ℤ) =>
    (show (ordinary R R P).X (n : ℤ) →ₗ[R] R from a)
      (relativeChainProjection R P n c)) hi).trans ?_
  change (show (ordinary R R P).X ((ComplexShape.up ℤ).prev (n : ℤ)) →ₗ[R] R from x)
    ((ordinary R R P).d (n : ℤ) ((ComplexShape.up ℤ).prev (n : ℤ))
      (relativeChainProjection R P n c)) = 0
  have hp : (ComplexShape.up ℤ).prev (n : ℤ) = ((n : ℤ)-1) :=
    (ComplexShape.up ℤ).prev_eq' (by simp)
  have hz : (ordinary R R P).d (n : ℤ) ((ComplexShape.up ℤ).prev (n : ℤ))
      (relativeChainProjection R P n c) = 0 := by
    rw [hp]
    exact relativeChainProjection_isCycle R P n c hc
  rw [hz, map_zero]

/-- Actual relative cohomology evaluation at a finite relative chain cycle. -/
def relativeCycleEvaluation (P : Pair.{w}) (n : ℕ)
    (c : Chains R P.space n) (hc : IsRelativeCycle R P.space P.subspace n c) :
    HR R P n →ₗ[R] R :=
  (ULift.moduleEquiv : ULift.{w} R ≃ₗ[R] R).toLinearMap.comp
  (((relativeCochains R R P).sc (n : ℤ)).descHomology
    (ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{w} R ≃ₗ[R] R).symm.toLinearMap.comp
        (relativeCycleCocycleEvaluation R P n c)))
    (relativeCycleCocycleEvaluation_boundary R P n c hc)).hom

lemma relativeCycleEvaluation_homologyπ (P : Pair.{w}) (n : ℕ)
    (c : Chains R P.space n) (hc : IsRelativeCycle R P.space P.subspace n c)
    (a : (relativeCochains R R P).cycles (n : ℤ)) :
    relativeCycleEvaluation R P n c hc ((relativeCochains R R P).homologyπ (n : ℤ) a) =
      relativeCocycleValue R P n a c := by
  have h := congrArg (fun ff => (ff a).down)
    (((relativeCochains R R P).sc (n : ℤ)).π_descHomology
      (ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{w} R ≃ₗ[R] R).symm.toLinearMap.comp
        (relativeCycleCocycleEvaluation R P n c)))
      (relativeCycleCocycleEvaluation_boundary R P n c hc))
  exact h

end RelativeCycleLifts

section FiberOrientationCycles
set_option maxHeartbeats 500000
open HomologicalComplex
abbrev singleRank (d : ℤ) :=
  (single (ModuleCat.{max u v} R) (.down ℤ) d).obj (ModuleCat.of R (ULift.{v} R))
abbrev dualSingle (d : ℤ) :=
  (dualComplexFunctor R R (.down ℤ)).obj (op (singleRank.{u,v} R d))
lemma dualSingle_d (d i j : ℤ) : (dualSingle.{u,v} R d).d i j = 0 := by
  change ModuleCat.ofHom (LinearMap.lcomp R R ((singleRank.{u,v} R d).d j i).hom) = 0
  simp only [singleRank, single_obj_d]
  ext f x
  exact f.map_zero

def singleDualHomologyEquiv (d : ℤ) :
    (dualSingle.{u,v} R d).homology d ≃ₗ[R] R :=
  (((dualSingle R d).isoHomologyπ (d-1) d (by change (ComplexShape.up ℤ).prev d = d-1; simp) (dualSingle_d R d _ _)).symm ≪≫
    (dualSingle R d).iCyclesIso d (d+1) (by change (ComplexShape.up ℤ).next d = d+1; simp) (dualSingle_d R d _ _)).toLinearEquiv.trans
    ((LinearEquiv.arrowCongr
      ((singleObjXSelf (.down ℤ) d (ModuleCat.of R (ULift.{v} R))).toLinearEquiv.trans
        ULift.moduleEquiv)
      (LinearEquiv.refl R R)).trans (LinearMap.ringLmapEquivSelf R R R))

lemma singleDualHomologyEquiv_apply (d : ℤ) (a : (dualSingle.{u,v} R d).cycles d) :
    singleDualHomologyEquiv R d ((dualSingle R d).homologyπ d a) =
      (show (singleRank R d).X d →ₗ[R] R from (dualSingle R d).iCycles d a)
        ((singleObjXSelf (.down ℤ) d (ModuleCat.of R (ULift.{v} R))).inv (ULift.up 1)) := by
  change (LinearEquiv.arrowCongr _ (LinearEquiv.refl R R)
    ((dualSingle R d).iCycles d
      (((dualSingle R d).isoHomologyπ (d-1) d (by change (ComplexShape.up ℤ).prev d = d-1; simp) (dualSingle_d R d _ _)).inv
        ((dualSingle R d).homologyπ d a)))) 1 = _
  have h := congrArg (fun f : (dualSingle R d).cycles d ⟶ (dualSingle R d).cycles d => f a)
    ((dualSingle R d).isoHomologyπ_hom_inv_id (d-1) d
      (by change (ComplexShape.up ℤ).prev d = d-1; simp) (dualSingle_d R d _ _))
  change ((dualSingle R d).isoHomologyπ (d-1) d _ _).inv
    ((dualSingle R d).homologyπ d a) = a at h
  rw [h]
  rfl

def evaluationOnSingleEquiv
    (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (d : ℤ)
    (e : HomotopyEquiv (singleRank.{u,v} R d) K) :
    ((dualComplexFunctor R R (.down ℤ)).obj (op K)).homology d ≃ₗ[R] R := by
  let ed := P202.CohomologyExcisionMV.dualHomotopyEquiv R R e
  haveI := ed.quasiIso_hom
  haveI := (quasiIsoAt_iff_isIso_homologyMap ed.hom d).mp inferInstance
  exact (asIso (homologyMap ed.hom d)).toLinearEquiv.trans (singleDualHomologyEquiv R d)

lemma evaluationOnSingleEquiv_apply
    (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (d : ℤ)
    (e : HomotopyEquiv (singleRank.{u,v} R d) K)
    (a : ((dualComplexFunctor R R (.down ℤ)).obj (op K)).cycles d) :
    evaluationOnSingleEquiv R K d e
      (((dualComplexFunctor R R (.down ℤ)).obj (op K)).homologyπ d a) =
    (show K.X d →ₗ[R] R from
      ((dualComplexFunctor R R (.down ℤ)).obj (op K)).iCycles d a)
      (e.hom.f d ((singleObjXSelf (.down ℤ) d
        (ModuleCat.of R (ULift.{v} R))).inv (ULift.up 1))) := by
  let D := (dualComplexFunctor R R (.down ℤ)).obj (op K)
  let f := (P202.CohomologyExcisionMV.dualHomotopyEquiv R R e).hom
  have h := congrArg (fun m : D.cycles d ⟶ (dualSingle R d).homology d => m a)
    (homologyπ_naturality f d)
  change homologyMap f d (D.homologyπ d a) =
    (dualSingle R d).homologyπ d (cyclesMap f d a) at h
  change singleDualHomologyEquiv R d (homologyMap f d (D.homologyπ d a)) = _
  rw [h, singleDualHomologyEquiv_apply]
  have hc := congrArg (fun m : D.cycles d ⟶ (dualSingle R d).X d => m a)
    (cyclesMap_i f d)
  change (dualSingle R d).iCycles d (cyclesMap f d a) = f.f d (D.iCycles d a) at hc
  rw [hc]
  rfl

open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.SingularChains
def emptySubspaceOrdinaryIso (B : Pair.{v}) [IsEmpty B.sub] :
    ordinaryComplex R R B.space ≅ ordinary R R B := by
  have hin : inclusion (ordinaryFunctor R R) B = 0 := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (P202.SingularDegreeZero.emptyOrdinaryX R R B.sub n).eq_of_src _ _
  haveI : IsIso (projection (ordinaryFunctor R R) B) := by
    change IsIso (cokernel.π (inclusion (ordinaryFunctor R R) B))
    rw [hin]
    infer_instance
  exact asIso (projection (ordinaryFunctor R R) B)

def modelZeroPointHomeomorph :
    (modelPair.{v} 0).space ≃ₜ P202Specs.SingularDegreeZero.point.{v} := by
  exact {
    toFun := fun _ => PUnit.unit
    invFun := fun _ => ULift.up 0
    left_inv := fun z => by
      apply ULift.ext
      funext i
      exact Fin.elim0 i
    right_inv := fun _ => Subsingleton.elim _ _
    continuous_toFun := continuous_const
    continuous_invFun := continuous_const }

def modelZeroHomologyIso :
    (ordinary R R (modelPair.{v} 0)).homology 0 ≅ ModuleCat.of R (ULift.{v} R) := by
  haveI : IsEmpty (modelPair.{v} 0).sub := ⟨fun z => z.property (Subsingleton.elim _ _)⟩
  let e := Classical.choice (P202.SingularDegreeZero.pointOrdinaryZero.{u,u,v} R R)
  exact ((HomologicalComplex.homologyFunctor _ _ 0).mapIso (emptySubspaceOrdinaryIso R (modelPair 0))).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      ((ordinaryFunctor R R).mapIso (TopCat.isoOfHomeo modelZeroPointHomeomorph)) ≪≫
    (e.trans ULift.moduleEquiv.symm).toModuleIso

lemma modelZeroHomology_isZero (q : ℤ) (hq : q ≠ 0) :
    IsZero ((ordinary R R (modelPair.{v} 0)).homology q) := by
  haveI : IsEmpty (modelPair.{v} 0).sub := ⟨fun z => z.property (Subsingleton.elim _ _)⟩
  let e := ((HomologicalComplex.homologyFunctor _ _ q).mapIso
    (emptySubspaceOrdinaryIso R (modelPair.{v} 0))).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      ((ordinaryFunctor R R).mapIso (TopCat.isoOfHomeo modelZeroPointHomeomorph))
  exact e.isZero_iff.mpr (P202.SingularDegreeZero.pointOrdinaryOther R R q hq)


theorem modelRelativeHomotopyEquiv_all (d : ℕ) :
    Nonempty (HomotopyEquiv (singleRank.{u,v} R (d : ℤ))
      (ordinary R R (modelPair.{v} d))) := by
  cases d with
  | succ n => exact P202.ThomClass.modelRelativeHomotopyEquiv R n
  | zero =>
    haveI : ∀ q, Projective ((ordinary R R (modelPair.{v} 0)).X q) := by
      intro q
      haveI := P202.CohomologyExcisionMV.relative_ordinary_free R (modelPair.{v} 0) q
      exact ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
    haveI : Projective (ModuleCat.of R (ULift.{v} R)) :=
      ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
    exact P202.ThomClass.homotopyEquiv_single_of_homology_concentrated R
      (ordinary R R (modelPair.{v} 0))
      ⟨0, fun q hq => (P202.RelativeSingularChains.ordinary_negative R R
        (modelPair.{v} 0) q hq).1⟩
      0 (ModuleCat.of R (ULift.{v} R)) (modelZeroHomologyIso R)
      (modelZeroHomology_isZero R)


open P202Specs.RelativeCupProduct P202Specs.TransverseThomProduct
/-- The actual cycle is chosen from the given orientation class and works for
all of its actual cocycle representatives. -/
theorem exists_relativeOrientationCycle
    (B : Pair.{v}) (d : ℕ)
    (e : HomotopyEquiv (singleRank.{u,v} R (d : ℤ)) (ordinary R R B))
    (g : relativeCohomology R R B (d : ℤ))
    (hg : Function.Surjective (fun r : R => r • g)) :
    ∃ c : Chains R B.space d,
      IsRelativeCycle R B.space B.subspace d c ∧
      ∀ a : (relativeCochains R R B).cycles (d : ℤ),
        (relativeCochains R R B).homologyπ (d : ℤ) a = g →
        relativeCocycleValue R B d a c = 1 := by
  let K := ordinary R R B
  let E := evaluationOnSingleEquiv R K (d : ℤ) e
  obtain ⟨r, hr⟩ := hg (E.symm 1)
  have hrE : r • E (g) = 1 := by
    have h := congrArg E hr
    change E (r • g) = E (E.symm 1) at h
    rw [E.map_smul, E.apply_symm_apply] at h
    exact h
  let t := ((singleObjXSelf (.down ℤ) (d : ℤ)
    (ModuleCat.of R (ULift.{v} R))).inv (ULift.up 1))
  let z := r • e.hom.f d t
  have hz : K.d (d : ℤ) ((d : ℤ)-1) z = 0 := by
    have h := congrArg (fun f : (singleRank R d).X d ⟶ K.X ((d : ℤ)-1) => f t)
      (e.hom.comm d ((d : ℤ)-1))
    change K.d (d : ℤ) ((d : ℤ)-1) (e.hom.f d t) =
      e.hom.f ((d : ℤ)-1) ((singleRank R d).d (d : ℤ) ((d : ℤ)-1) t) at h
    have ht : (singleRank R d).d (d : ℤ) ((d : ℤ)-1) t = 0 := rfl
    rw [ht, map_zero] at h
    change K.d (d : ℤ) ((d : ℤ)-1) (r • e.hom.f d t) = 0
    rw [map_smul, h, smul_zero]
  obtain ⟨c, hc, hcy⟩ := P202.TransverseThomProduct.relativeCycle_lift R B d z hz
  refine ⟨c, hcy, ?_⟩
  intro a ha
  rw [P202.TransverseThomProduct.relativeCocycleValue_projection, hc]
  change (show K.X (d : ℤ) →ₗ[R] R from
    (relativeCochains R R B).iCycles (d : ℤ) a)
      (r • e.hom.f d t) = 1
  rw [map_smul]
  have he := evaluationOnSingleEquiv_apply R K (d : ℤ) e a
  change E ((relativeCochains R R B).homologyπ (d : ℤ) a) =
    (show K.X (d : ℤ) →ₗ[R] R from
      (relativeCochains R R B).iCycles (d : ℤ) a) (e.hom.f d t) at he
  rw [← he, ha]
  exact hrE


/-- Every model-fiber cohomology generator has one finite relative cycle dual
to all its actual cocycle representatives. -/
theorem exists_modelOrientationCycle (d : ℕ)
    (g : relativeCohomology R R (modelPair.{v} d) (d : ℤ))
    (hg : Function.Surjective (fun r : R => r • g)) :
    ∃ c : Chains R (modelPair.{v} d).space d,
      IsRelativeCycle R (modelPair.{v} d).space (modelPair.{v} d).subspace d c ∧
      ∀ a : (relativeCochains R R (modelPair.{v} d)).cycles (d : ℤ),
        (relativeCochains R R (modelPair.{v} d)).homologyπ (d : ℤ) a = g →
        relativeCocycleValue R (modelPair.{v} d) d a c = 1 := by
  obtain ⟨e⟩ := modelRelativeHomotopyEquiv_all R d
  exact exists_relativeOrientationCycle R (modelPair.{v} d) d e g hg


section NormalFiber
open P202Specs.RelativeCupProduct P202Specs.TransverseThomProduct
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
variable {m n : ℕ} {P M : Type v} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

theorem normalFiberRelativeHomotopyEquiv
    (N : NormalBundle T S i) (p : P) :
    Nonempty (HomotopyEquiv (singleRank.{u,v} R ((n-m : ℕ) : ℤ))
      (ordinary R R (fiberPair N p))) := by
  obtain ⟨a, hp⟩ := (normalBundle N).covers p
  obtain ⟨e⟩ := modelRelativeHomotopyEquiv_all R (n-m)
  let f := (relativeFunctor (ordinaryFunctor R R)).mapIso
    (P202.ThomClass.fiberCoordinatesIso N a p hp).symm
  exact ⟨e.trans (HomotopyEquiv.ofIso f)⟩

/-- The actual cycle is chosen from the given orientation class and works for
all of its actual cocycle representatives. -/
theorem exists_normalFiberOrientationCycle
    (N : NormalBundle T S i) (d : ℕ) (hd : d = n-m)
    (o : Orientation R N d) (p : P) :
    ∃ c : Chains R (fiberPair N p).space d,
      IsRelativeCycle R (fiberPair N p).space (fiberPair N p).subspace d c ∧
      ∀ a : (relativeCochains R R (fiberPair N p)).cycles (d : ℤ),
        (relativeCochains R R (fiberPair N p)).homologyπ (d : ℤ) a = o.generator p →
        relativeCocycleValue R (fiberPair N p) d a c = 1 := by
  subst d
  obtain ⟨e⟩ := normalFiberRelativeHomotopyEquiv R N p
  exact exists_relativeOrientationCycle R (fiberPair N p) (n-m) e (o.generator p)
    (o.generates p).surjective


end NormalFiber

end FiberOrientationCycles

theorem orientationCycle : P202Specs.TransverseThomProduct.orientationCycle_type.{u,w} := by
  intro R _ m n d P M _ _ T S i N hd o p
  exact exists_normalFiberOrientationCycle R N d hd o p

section ParametrizedDiskCycles
open P202Specs.SpheresDisks
/-- The actual ordered affine chain is a relative cycle modulo all its faces. -/
lemma affineChain_relativeCycle (n : ℕ) (r : R) :
    IsRelativeCycle R (simplex n) (simplexPair n).subspace n (affineChain R n r) := by
  cases n with
  | zero => trivial
  | succ n =>
    exact ⟨orientedBoundary R n r,
      P202.SpheresDisks.inclusion_orientedBoundary R R n r⟩

/-- The chosen disk-simplex parametrization gives an actual chain in the geometric disk.
No compatibility with a separately chosen Euclidean orientation is asserted here. -/
def parametrizedDiskChain (n : ℕ) (r : R) : Chains R (disk n) n :=
  ((chainMap R R (P202.SpheresDisks.diskSimplexPairIso n).inv.map).f n).hom
    (affineChain R n r)

lemma parametrizedDiskChain_relativeCycle (n : ℕ) (r : R) :
    IsRelativeCycle R (disk n) (diskPair n).subspace n (parametrizedDiskChain R n r) :=
  relativeCycle_map R (P202.SpheresDisks.diskSimplexPairIso n).inv n _
    (affineChain_relativeCycle R n r)
lemma parametrizedDiskChain_smul (n : ℕ) (r : R) :
    parametrizedDiskChain R n r = r • parametrizedDiskChain R n 1 := by
  let f := ((chainMap R R (P202.SpheresDisks.diskSimplexPairIso n).inv.map).f n).hom
  change f (Finsupp.single (affineSimplex n) r) =
    r • f (Finsupp.single (affineSimplex n) 1)
  have h : (Finsupp.single (affineSimplex n) r : Chains R (simplex n) n) =
      r • Finsupp.single (affineSimplex n) 1 := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  exact (congrArg f h).trans (f.map_smul r _)

/-- The generic bridge on the actual parametrized disk chains. The chosen
factor order is retained; no Euclidean orientation comparison is assumed. -/
lemma parametrizedDiskProduct_evaluation (p q : ℕ) (r s : R)
    (a : Cochain R (disk p) p) (b : Cochain R (disk q) q)
    (ha : delta R (disk p) p a = 0) (hb : delta R (disk q) q b = 0)
    (hA : VanishesOn R (diskPair p).subspace a)
    (hB : VanishesOn R (diskPair q).subspace b) :
    externalCochain R (disk p) (disk q) p q a b
      (shuffleComponent R (disk p) (disk q) p q
        (parametrizedDiskChain R p r ⊗ₜ[R] parametrizedDiskChain R q s)) =
      a (parametrizedDiskChain R p r) * b (parametrizedDiskChain R q s) :=
  evaluation_pureTensor R (diskPair p).subspace (diskPair q).subspace p q a b _ _
    ha hb hA hB (parametrizedDiskChain_relativeCycle R p r)
    (parametrizedDiskChain_relativeCycle R q s)

end ParametrizedDiskCycles

/-- Original quotient normal-fiber coordinate isomorphism. -/
abbrev fiberCoordinatesIso := @P202.ThomClass.fiberCoordinatesIso


section EvaluationNormalization
variable {R : Type u} [CommRing R]
variable {H : Type v} [AddCommGroup H] [Module R H]
variable {C : Type w} [AddCommGroup C] [Module R C]
/-- A generator of the cohomology line has a cycle evaluating to one as soon
as evaluation on a fixed cycle is known to be an isomorphism. -/
theorem normalizeEvaluation
    (pairing : H →ₗ[R] C →ₗ[R] R)
    (z : C) (e : H ≃ₗ[R] R)
    (he : ∀ h, e h = pairing h z)
    (g : H) (hg : Function.Surjective (fun r : R => r • g)) :
    ∃ r : R, pairing g (r • z) = 1 := by
  obtain ⟨r, hr⟩ := hg (e.symm 1)
  change r • g = e.symm 1 at hr
  refine ⟨r, ?_⟩
  have h : e (r • g) = 1 := by rw [hr, e.apply_symm_apply]
  rw [e.map_smul, he] at h
  simpa only [map_smul, smul_eq_mul] using h

theorem generates_of_evaluation_one (e : H ≃ₗ[R] R) (f : H →ₗ[R] R)
    (a : H) (ha : f a = 1) : Function.Bijective (fun r : R => r • a) := by
  have hexp (h : H) : h = e h • e.symm 1 := by
    apply e.injective
    simp
  have hunit : e a * f (e.symm 1) = 1 := by
    have h := ha
    rw [hexp a, map_smul] at h
    exact h
  constructor
  · intro r s hrs
    have h := congrArg f hrs
    simpa only [map_smul, ha, smul_eq_mul, mul_one] using h
  · intro h
    refine ⟨e h * f (e.symm 1), ?_⟩
    apply e.injective
    simp only [map_smul, smul_eq_mul]
    calc
      e h * f (e.symm 1) * e a = e h * (e a * f (e.symm 1)) := by ring
      _ = e h := by rw [hunit, mul_one]

end EvaluationNormalization

section OrderedProducts
open P202Specs.RelativeCupProduct
variable {X : TopCat.{w}} (μ : NaturalRelativeCupProduct.{u,w} R)

/-- The single-factor operation recovers the original relative class exactly. -/
lemma orderedCup_single (F : Fin 1 → SupportedClass R X) :
    orderedCup R μ 0 F = F 0 := rfl

/-- The support of the ordered product is the intersection of all supports. -/
lemma orderedCup_support (k : ℕ) (F : Fin (k+1) → SupportedClass R X) :
    (orderedCup R μ k F).support = ⋂ j, (F j).support := by
  induction k with
  | zero =>
    ext x
    simp only [orderedCup, Set.mem_iInter]
    exact ⟨fun h j => (show j = 0 by omega) ▸ h, fun h => h 0⟩
  | succ k ih =>
    change (F 0).support ∩ (orderedCup R μ k (fun j => F j.succ)).support = _
    rw [ih]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Fin.forall_fin_succ]

/-- The output degree is the sum in the given order, including rank-zero factors. -/
lemma orderedCup_degree (k : ℕ) (F : Fin (k+1) → SupportedClass R X) :
    (orderedCup R μ k F).degree = ∑ j, (F j).degree := by
  induction k with
  | zero => simp [orderedCup]
  | succ k ih =>
    change (F 0).degree + (orderedCup R μ k (fun j => F j.succ)).degree = _
    rw [ih]
    exact (Fin.sum_univ_succ (fun j => (F j).degree)).symm

/-- A class in a supported relative group is zero when the support is empty. -/
lemma SupportedClass.value_eq_zero (a : SupportedClass R X) (h : a.support = ∅) :
    a.value = 0 := by
  letI := ModuleCat.subsingleton_of_isZero
    (emptySupport_cohomology R X a.support h (a.degree : ℤ))
  exact Subsingleton.elim _ _

end OrderedProducts

/-- Apply the full Thom premise in its original (space, coefficient) order. -/
lemma singleMember_of_thom (hThom : P202Specs.ThomClass.exists_unique_type.{w,u}) :
    P202Specs.TransverseThomProduct.singleMember_type.{u,w} := by
  intro R _ n M S N
  letI := N.compact
  obtain ⟨hK, c, hc, huniq⟩ := hThom R N.dimension n N.codimension
    N.source M N.atlas S N.inclusion N.embedding N.normal N.rank N.orientation
  refine ⟨hK, c, ⟨hc, support_isClosed R N, ?_⟩, ?_⟩
  · intro μ
    rfl
  · intro c' hc'
    exact huniq c' hc'.1


/-- Closed auxiliary target with the original coefficient and space universes. -/
theorem singleMember : P202Specs.TransverseThomProduct.singleMember_type.{u,w} := by
  exact singleMember_of_thom P202.ThomClass.exists_unique


/-- Closed relative-product evaluation bridge on actual relative representatives. -/
theorem relativeProductEvaluation : P202Specs.TransverseThomProduct.relativeProductEvaluation_type.{u,w} := by
  exact relativeProductEvaluation_of_representatives

/-- The actual upstream Thom theorem constructs each factor; the existing
ordered product then has the exact ambient support, total degree and empty case. -/
theorem orderedThomClasses :
    P202Specs.TransverseThomProduct.orderedThomClasses_type.{u,w} := by
  intro R _ n k M S F
  classical
  have hth : ∀ j : Fin (k+1),
      ∃ c : P202Specs.RelativeCupProduct.HR R (⟨M, ((F j).support)ᶜ⟩ : Pair) (F j).codimension,
        P202Specs.ThomClass.HasFiberValues R (F j).orientation c := by
    intro j
    letI := (F j).compact
    exact (P202.ThomClass.exists_unique R (F j).dimension n (F j).codimension
      (F j).source M (F j).atlas S (F j).inclusion (F j).embedding
      (F j).normal (F j).rank (F j).orientation).2.exists
  choose c hc using hth
  let hclosed : ∀ j, IsClosed (F j).support := fun j => support_isClosed R (F j)
  refine ⟨c, hclosed, hc, ?_⟩
  intro μ
  let G : Fin (k+1) → SupportedClass R M := fun j =>
    ⟨(F j).support, hclosed j, (F j).codimension, c j⟩
  change (orderedCup R μ k G).support = intersectionSupport R F ∧
    (orderedCup R μ k G).degree = totalCodimension R F ∧
    (intersectionSupport R F = ∅ → (orderedCup R μ k G).value = 0)
  have hs : (orderedCup R μ k G).support = intersectionSupport R F := by
    simpa only [G, intersectionSupport] using orderedCup_support R μ k G
  have hd : (orderedCup R μ k G).degree = totalCodimension R F := by
    simpa only [G, totalCodimension] using orderedCup_degree R μ k G
  exact ⟨hs, hd, fun h => SupportedClass.value_eq_zero R _ (hs.trans h)⟩

section NullaryUnit
open HomologicalComplex P202Specs.RelativeCupProduct
lemma relativeCocycleValue_point (B : Pair.{w})
    (a : (relativeCochains R R B).cycles 0) (x : B.space) :
    relativeCocycleValue R B 0 a
      (Finsupp.single ((simplexEquiv B.space 0).symm (ContinuousMap.const _ x)) 1) =
      P202.ThomClass.relativeZeroValue R R B
        ((relativeCochains R R B).homologyπ 0 a) x := by
  let K := relativeCochains R R B
  have hd : K.d (-1) 0 = 0 :=
    ((P202.CohomologyPairs.negative R R).2 B (-1) (by decide)).1.eq_of_src _ _
  have hi := congrArg (fun f : K.cycles 0 ⟶ K.cycles 0 => f a)
    (K.isoHomologyπ_hom_inv_id (-1) 0 (by simp) hd)
  change (K.isoHomologyπ (-1) 0 (by simp) hd).inv (K.homologyπ 0 a) = a at hi
  have hrep : P202.ThomClass.relativeZeroCochain R R B (K.homologyπ 0 a) = K.iCycles 0 a := by
    change K.iCycles 0 ((K.isoHomologyπ (-1) 0 (by simp) hd).inv (K.homologyπ 0 a)) = _
    rw [hi]
  unfold P202.ThomClass.relativeZeroValue P202.ThomClass.relativeZeroCocycle
  rw [hrep]
  rfl

theorem nullaryUnit_on (X : TopCat.{w}) :
    ∃! c : HR R (⟨X,∅⟩ : Pair) 0,
      ∀ a : (relativeCochains R R (⟨X,∅⟩ : Pair)).cycles 0,
        (relativeCochains R R (⟨X,∅⟩ : Pair)).homologyπ 0 a = c →
        ∀ x : X, relativeCocycleValue R (⟨X,∅⟩ : Pair) 0 a
          (Finsupp.single ((simplexEquiv X 0).symm (ContinuousMap.const _ x)) 1) = 1 := by
  let B : Pair.{w} := ⟨X,∅⟩
  let f : LocallyConstant X R := LocallyConstant.const X 1
  obtain ⟨c, hc⟩ := P202.ThomClass.exists_relativeH0_of_locallyConstant R R B f
    (fun x hx => False.elim hx)
  have hp : ∀ a : (relativeCochains R R B).cycles 0,
      (relativeCochains R R B).homologyπ 0 a = c →
      ∀ x : X, relativeCocycleValue R B 0 a
        (Finsupp.single ((simplexEquiv X 0).symm (ContinuousMap.const _ x)) 1) = 1 := by
    intro a ha x
    rw [relativeCocycleValue_point, ha]
    exact hc x
  refine ⟨c, hp, ?_⟩
  intro c' hc'
  apply P202.ThomClass.relativeZeroValue_ext R R B c' c
  intro x
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective
    ((relativeCochains R R B).homologyπ 0)).mp inferInstance c'
  calc
    P202.ThomClass.relativeZeroValue R R B c' x =
      relativeCocycleValue R B 0 a
        (Finsupp.single ((simplexEquiv X 0).symm (ContinuousMap.const _ x)) 1) := by
          rw [relativeCocycleValue_point, ha]
    _ = 1 := hc' a ha x
    _ = P202.ThomClass.relativeZeroValue R R B c x := (hc x).symm


end NullaryUnit

theorem nullaryUnit : P202Specs.TransverseThomProduct.nullaryUnit_type.{u,w} := by
  intro R _ X
  exact nullaryUnit_on R X

section ModelProductGenerators
open P202Specs.ThomClass P202Specs.RelativeCupProduct
  P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open HomologicalComplex

theorem modelExternalProduct_generates (μ : NaturalRelativeCupProduct.{u,w} R)
    (p q : ℕ) (a : HR R (modelPair.{w} p) p) (b : HR R (modelPair.{w} q) q)
    (ha : Function.Surjective (fun r : R => r • a))
    (hb : Function.Surjective (fun r : R => r • b)) :
    Function.Bijective (fun r : R => r • modelExternalProduct R μ p q a b) := by
  let X := (modelPair.{w} p).space
  let Y := (modelPair.{w} q).space
  let A := (modelPair.{w} p).subspace
  let B := (modelPair.{w} q).subspace
  let Q := (productSubspaces X Y A B).unionPair
  let v := modelExternalProduct R μ p q a b
  obtain ⟨c,hc,hca⟩ := exists_modelOrientationCycle R p a ha
  obtain ⟨d,hd,hdb⟩ := exists_modelOrientationCycle R q b hb
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective
    ((relativeCochains R R (modelPair.{w} p)).homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨br,hbr⟩ := (ModuleCat.epi_iff_surjective
    ((relativeCochains R R (modelPair.{w} q)).homologyπ (q : ℤ))).mp inferInstance b
  obtain ⟨er,her⟩ := (ModuleCat.epi_iff_surjective
    ((relativeCochains R R Q).homologyπ ((p+q : ℕ) : ℤ))).mp inferInstance v
  let z := shuffleComponent R X Y p q (c ⊗ₜ[R] d)
  have hz : IsRelativeCycle R Q.space Q.subspace (p+q) z :=
    shuffleComponent_relativeCycle R A B p q c d hc hd
  have heclass : (relativeCochains R R Q).homologyπ ((p+q : ℕ) : ℤ) er =
      μ.product (productSubspaces X Y A B)
        (productSubspaces_isOpen X Y A B (modelPair_isOpen p) (modelPair_isOpen q)) p q
        (relativePullback R (productLeftProjection X Y A B) p
          ((relativeCochains R R (modelPair.{w} p)).homologyπ (p : ℤ) ar) ⊗ₜ[R]
         relativePullback R (productRightProjection X Y A B) q
          ((relativeCochains R R (modelPair.{w} q)).homologyπ (q : ℤ) br)) := by
    simpa only [har,hbr,v,modelExternalProduct] using her
  have hev : relativeCocycleValue R Q (p+q) er z = 1 :=
    relativeProductEvaluation R μ X Y A B (modelPair_isOpen p) (modelPair_isOpen q)
      p q ar br c d hc hd (hca ar har) (hdb br hbr) er heclass
  have hv : relativeCycleEvaluation R Q (p+q) z hz v = 1 := by
    rw [← her, relativeCycleEvaluation_homologyπ]
    exact hev
  obtain ⟨e⟩ := modelRelativeHomotopyEquiv_all R (p+q)
  let f := (relativeFunctor (ordinaryFunctor R R)).mapIso (orderedModelProductIso.{w} p q).symm
  let eQ := e.trans (HomotopyEquiv.ofIso f)
  let E := evaluationOnSingleEquiv R (ordinary R R Q) ((p+q : ℕ) : ℤ) eQ
  exact generates_of_evaluation_one E (relativeCycleEvaluation R Q (p+q) z hz) v hv

theorem orderedModelProductOrientation_generates (μ : NaturalRelativeCupProduct.{u,w} R)
    (p q : ℕ) (a : HR R (modelPair.{w} p) p) (b : HR R (modelPair.{w} q) q)
    (ha : Function.Surjective (fun r : R => r • a))
    (hb : Function.Surjective (fun r : R => r • b)) :
    Function.Bijective (fun r : R => r • orderedModelProductOrientation R μ p q a b) := by
  let E := ((relativeCohomologyFunctor R R ((p+q : ℕ) : ℤ)).mapIso
    (orderedModelProductIso.{w} p q).op).symm.toLinearEquiv
  have h := E.bijective.comp (modelExternalProduct_generates R μ p q a b ha hb)
  change Function.Bijective (fun r : R => E (r • modelExternalProduct R μ p q a b)) at h
  have hE : E (modelExternalProduct R μ p q a b) =
      orderedModelProductOrientation R μ p q a b := rfl
  simpa only [E.map_smul, hE] using h

lemma modelGenerator_of_surjective (d : ℕ) (a : HR R (modelPair.{w} d) d)
    (ha : Function.Surjective (fun r : R => r • a)) :
    Function.Bijective (fun r : R => r • a) := by
  obtain ⟨e⟩ := modelRelativeHomotopyEquiv_all R d
  let E := evaluationOnSingleEquiv R (ordinary R R (modelPair.{w} d)) (d : ℤ) e
  obtain ⟨r,hr⟩ := ha (E.symm 1)
  apply generates_of_evaluation_one E (r • E.toLinearMap) a
  change r • E a = 1
  simpa only [E.map_smul, E.apply_symm_apply] using congrArg E hr

lemma orderedModelCup_degree (μ : NaturalRelativeCupProduct.{u,w} R)
    (k : ℕ) (F : Fin (k+1) → ModelClass.{u,w} R) :
    (orderedModelCup R μ k F).degree = ∑ j, (F j).degree := by
  induction k with
  | zero => simp [orderedModelCup]
  | succ k ih =>
    change (F 0).degree + (orderedModelCup R μ k (fun j => F j.succ)).degree = _
    rw [ih]
    exact (Fin.sum_univ_succ (fun j => (F j).degree)).symm

theorem orderedModelCup_generates (μ : NaturalRelativeCupProduct.{u,w} R)
    (k : ℕ) (F : Fin (k+1) → ModelClass.{u,w} R)
    (hF : ∀ j, Function.Surjective (fun r : R => r • (F j).value)) :
    Function.Bijective (fun r : R => r • (orderedModelCup R μ k F).value) := by
  induction k with
  | zero => exact modelGenerator_of_surjective R (F 0).degree (F 0).value (hF 0)
  | succ k ih =>
    exact orderedModelProductOrientation_generates R μ (F 0).degree
      (orderedModelCup R μ k (fun j => F j.succ)).degree (F 0).value
      (orderedModelCup R μ k (fun j => F j.succ)).value (hF 0)
      (ih (fun j => F j.succ) (fun j => hF j.succ)).surjective

theorem modelProductGenerator :
    P202Specs.TransverseThomProduct.modelProductGenerator_type.{u,w} := by
  intro R _ μ p q a b ha hb
  exact modelExternalProduct_generates R μ p q a b ha hb

theorem orderedModelOrientation :
    P202Specs.TransverseThomProduct.orderedModelOrientation_type.{u,w} := by
  intro R _ μ k F
  exact ⟨orderedModelCup_degree R μ k F, orderedModelCup_generates R μ k F⟩

end ModelProductGenerators

section LocalThomExpressions
set_option maxHeartbeats 400000
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
open P202Specs.ThomClass P202.ThomClass
attribute [local instance] normalTopology
variable {m n : ℕ} {P M : Type v} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
variable (R : Type u) [CommRing R]

lemma normalChart_class_eq_projection (N : NormalBundle T S i) (d : ℕ)
    (hd : n-m=d) (hpos : 0 < d)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ))
    (a : P) (U : Set P) (hopen : IsOpen U) (hU : U ⊆ (normalBundle N).baseSet a)
    (cModel : relativeCohomology R R (modelPair.{v} (n-m)) (d : ℤ))
    (hg : ∀ (p : P) (hp : p ∈ U),
      (relativeCohomologyFunctor R R (d : ℤ)).map (fiberCoordinates N a p (hU hp)).op cModel = g p)
    (c : relativeCohomology R R (normalOverPair N U) (d : ℤ))
    (hc : NormalHasValues R N U d g c) :
    c = (relativeCohomologyFunctor R R (d : ℤ)).map
      ((normalChartPairIso N a U hU).hom ≫
        secondProductProjection (TopCat.of U) (modelPair.{v} (n-m))).op cModel := by
  let F := relativeCohomologyFunctor R R (d : ℤ)
  let b := F.map ((normalChartPairIso N a U hU).hom ≫
    secondProductProjection (TopCat.of U) (modelPair.{v} (n-m))).op cModel
  have hb : NormalHasValues R N U d g b := by
    intro p hp
    change (F.map ((normalChartPairIso N a U hU).hom ≫
      secondProductProjection (TopCat.of U) (modelPair.{v} (n-m))).op ≫
      F.map (fiberToNormalOver N U p hp).op) cModel = g p
    rw [← Functor.map_comp, ← op_comp, normalChart_projection_fiber]
    exact hg p hp
  obtain ⟨_, b', hb', hu⟩ :=
    normalThomOn_of_chart R N d hd hpos g a U hU cModel hg U hopen Set.Subset.rfl
  exact (hu c hc).trans (hu b hb).symm

theorem ambientThom_local_normal_expression [CompactSpace P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (d : ℕ)
    (hd : n-m=d) (hpos : 0 < d) (o : Orientation R N d)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ)) (hc : HasFiberValues R o c)
    (K : TubularNeighborhood N) (hK : NormalCompatible N K) (p : P) :
    ∃ (a : P) (U : Set P), IsOpen U ∧ p ∈ U ∧
      ∃ hU : U ⊆ (normalBundle N).baseSet a,
        ∃ g : relativeCohomology R R (modelPair.{v} (n-m)) (d : ℤ),
          (relativeCohomologyFunctor R R (d : ℤ)).map
            (normalOverMono N (show U ⊆ Set.univ from Set.subset_univ _) ≫
              (normalOverUnivIso N).hom).op
            (ambientNormalCohomologyEquiv hi N K R (d : ℤ) c) =
          (relativeCohomologyFunctor R R (d : ℤ)).map
            ((normalChartPairIso N a U hU).hom ≫
              secondProductProjection (TopCat.of U) (modelPair.{v} (n-m))).op g ∧
          ∀ (q : P) (hq : q ∈ U),
            (relativeCohomologyFunctor R R (d : ℤ)).map
              (fiberCoordinates N a q (hU hq)).op g = o.generator q := by
  obtain ⟨a, U, hopen, hp, hU, g, hg⟩ := o.locally_constant p
  refine ⟨a, U, hopen, hp, hU, g, ?_, hg⟩
  let F := relativeCohomologyFunctor R R (d : ℤ)
  let j := normalOverMono N (show U ⊆ Set.univ from Set.subset_univ _) ≫
    (normalOverUnivIso N).hom
  apply normalChart_class_eq_projection R N d hd hpos o.generator a U hopen hU g hg
  intro q hq
  change (F.map j.op ≫ F.map (fiberToNormalOver N U q hq).op)
    (ambientNormalCohomologyEquiv hi N K R (d : ℤ) c) = o.generator q
  rw [← Functor.map_comp, ← op_comp]
  have hj : fiberToNormalOver N U q hq ≫ j = fiberToNormal N q := PairMap.ext _ _ rfl
  rw [hj]
  exact (normal_fiber_values_iff_slice hi N K R d o c).mp (hc K hK) q


end LocalThomExpressions


section GeometricAssemblyAuxiliaries
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
  P202Specs.RelativeCupProduct P202Specs.ThomClass
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData SmoothManifolds.TangentData SmoothManifolds.DifferentialData

section CupNaturality
/-- Pullback of a supported homogeneous class keeps its exact inverse-image support. -/
def supportedPullback {X Y : TopCat.{w}} (f : X ⟶ Y) (a : SupportedClass R Y) :
    SupportedClass R X where
  support := f ⁻¹' a.support
  closed := a.closed.preimage f.hom.continuous
  degree := a.degree
  value := relativePullback R
    (⟨f, fun _ h => h⟩ : (⟨X, (f ⁻¹' a.support)ᶜ⟩ : Pair) ⟶
      (⟨Y, a.supportᶜ⟩ : Pair)) a.degree a.value

lemma relativePullback_comp' {A B C : Pair.{w}} (f : A ⟶ B) (g : B ⟶ C)
    (d : ℕ) (a : HR R C d) :
    relativePullback R f d (relativePullback R g d a) =
      relativePullback R (f ≫ g) d a := by
  change (((relativeCohomologyFunctor R R (d : ℤ)).map g.op) ≫
    ((relativeCohomologyFunctor R R (d : ℤ)).map f.op)) a = _
  rw [← Functor.map_comp, ← op_comp]
  rfl

lemma relativePullback_subspace_eq {X : TopCat.{w}} (A B : Set X) (h : A = B)
    (d : ℕ) (a : HR R (⟨X,B⟩ : Pair) d) :
    relativePullback R (⟨𝟙 X, h.subset⟩ : (⟨X,A⟩ : Pair) ⟶ (⟨X,B⟩ : Pair)) d a =
      cast (congrArg (fun S => ↥(HR R (⟨X,S⟩ : Pair) d)) h.symm) a := by
  subst B
  change ((relativeCohomologyFunctor R R (d : ℤ)).map (𝟙 _)) a = _
  simp

lemma supportedCup_value {X : TopCat.{w}} (μ : NaturalRelativeCupProduct R)
    (a b : SupportedClass R X) :
    (supportedCup R μ a b).value =
      relativePullback R (⟨𝟙 X, (Set.compl_inter a.support b.support).subset⟩ :
        (⟨X,(a.support ∩ b.support)ᶜ⟩ : Pair) ⟶
        (⟨X,a.supportᶜ ∪ b.supportᶜ⟩ : Pair)) (a.degree + b.degree)
        (μ.product ⟨X,a.supportᶜ,b.supportᶜ⟩
          ⟨a.closed.isOpen_compl,b.closed.isOpen_compl⟩ a.degree b.degree
          (a.value ⊗ₜ[R] b.value)) := by
  apply eq_of_heq
  let v := μ.product ⟨X,a.supportᶜ,b.supportᶜ⟩
    ⟨a.closed.isOpen_compl,b.closed.isOpen_compl⟩ a.degree b.degree
    (a.value ⊗ₜ[R] b.value)
  refine HEq.trans (b := v) ?_ ?_
  · unfold supportedCup
    dsimp only
    exact cast_heq _ _
  · symm
    rw [relativePullback_subspace_eq R _ _ (Set.compl_inter a.support b.support)]
    exact cast_heq _ _

lemma supportedClass_ext {X : TopCat.{w}} {a b : SupportedClass R X}
    (hs : a.support = b.support) (hd : a.degree = b.degree)
    (hv : HEq a.value b.value) : a = b := by
  cases a
  cases b
  cases hs
  cases hd
  cases hv
  rfl

lemma supportedCup_pullback {X Y : TopCat.{w}} (μ : NaturalRelativeCupProduct R)
    (f : X ⟶ Y) (a b : SupportedClass R Y) :
    supportedPullback R f (supportedCup R μ a b) =
      supportedCup R μ (supportedPullback R f a) (supportedPullback R f b) := by
  let P : TwoSubspaces := ⟨X, (f ⁻¹' a.support)ᶜ, (f ⁻¹' b.support)ᶜ⟩
  let Q : TwoSubspaces := ⟨Y, a.supportᶜ, b.supportᶜ⟩
  let m : P.Map Q := ⟨f, fun _ h => h, fun _ h => h⟩
  have hP : P.IsOpen :=
    ⟨(a.closed.preimage f.hom.continuous).isOpen_compl,
     (b.closed.preimage f.hom.continuous).isOpen_compl⟩
  have hQ : Q.IsOpen := ⟨a.closed.isOpen_compl, b.closed.isOpen_compl⟩
  have h := μ.naturality P Q hP hQ m a.degree b.degree a.value b.value
  apply supportedClass_ext R
  · rfl
  · rfl
  apply heq_of_eq
  change relativePullback R _ _ (supportedCup R μ a b).value = _
  rw [supportedCup_value, supportedCup_value]
  dsimp only [supportedCup, supportedPullback]
  rw [relativePullback_comp']
  dsimp only [P, Q, m, TwoSubspaces.Map.leftMap, TwoSubspaces.Map.rightMap] at h
  rw [← h, relativePullback_comp']
  congr 1

lemma orderedCup_pullback {X Y : TopCat.{w}} (μ : NaturalRelativeCupProduct R)
    (f : X ⟶ Y) (k : ℕ) (F : Fin (k+1) → SupportedClass R Y) :
    supportedPullback R f (orderedCup R μ k F) =
      orderedCup R μ k (fun j => supportedPullback R f (F j)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change supportedPullback R f (supportedCup R μ (F 0)
      (orderedCup R μ k (fun j => F j.succ))) = _
    rw [supportedCup_pullback, ih]
    rfl

lemma supportedPullback_comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : SupportedClass R Z) :
    supportedPullback R f (supportedPullback R g a) = supportedPullback R (f ≫ g) a := by
  apply supportedClass_ext R
  · rfl
  · rfl
  apply heq_of_eq
  exact relativePullback_comp' R _ _ _ _

lemma supportedPullback_id {X : TopCat.{w}} (a : SupportedClass R X) :
    supportedPullback R (𝟙 X) a = a := by
  apply supportedClass_ext R
  · rfl
  · rfl
  apply heq_of_eq
  change ((relativeCohomologyFunctor R R (a.degree : ℤ)).map (𝟙 _)) a.value = a.value
  simp

/-- A model generator regarded as a class supported exactly at its origin. -/
def modelSupported (a : ModelClass.{u,w} R) :
    SupportedClass R (modelPair.{w} a.degree).space where
  support := {z | z.down = 0}
  closed := isClosed_eq continuous_uliftDown continuous_const
  degree := a.degree
  value := a.value

/-- Equality of pair maps after changing the source relative subspace. -/
lemma relativePullback_heq {X Y : TopCat.{w}} (A A' : Set X) (B : Set Y)
    (hA : A = A') (f : (⟨X,A⟩ : Pair) ⟶ (⟨Y,B⟩ : Pair))
    (f' : (⟨X,A'⟩ : Pair) ⟶ (⟨Y,B⟩ : Pair)) (hf : f.map = f'.map)
    (d : ℕ) (a : HR R (⟨Y,B⟩ : Pair) d) :
    HEq (relativePullback R f d a) (relativePullback R f' d a) := by
  subst A'
  have hh : f = f' := PairMap.ext _ _ hf
  subst f'
  rfl

open P202Specs.CupProduct P202Specs.SingularChains P202Specs.AlexanderWhitney

/-- The first coordinate block, without a spurious pair-map condition on the other block. -/
def modelLeftBlock (p q : ℕ) :
    (modelPair.{w} (p+q)).space ⟶ (modelPair.{w} p).space :=
  (orderedModelProductIso p q).inv.map ≫ firstProjection _ _

/-- The second coordinate block, retaining the prescribed block order. -/
def modelRightBlock (p q : ℕ) :
    (modelPair.{w} (p+q)).space ⟶ (modelPair.{w} q).space :=
  (orderedModelProductIso p q).inv.map ≫ secondProjection _ _

lemma modelCup_as_supportedCup (μ : NaturalRelativeCupProduct.{u,w} R)
    (a b : ModelClass.{u,w} R) :
    supportedCup R μ
      (supportedPullback R (modelLeftBlock a.degree b.degree) (modelSupported R a))
      (supportedPullback R (modelRightBlock a.degree b.degree) (modelSupported R b)) =
      modelSupported R (modelCup R μ a b) := by
  apply supportedClass_ext R
  · ext z
    change (((orderedModelProductIso a.degree b.degree).inv.map z).1.down = 0 ∧
      ((orderedModelProductIso a.degree b.degree).inv.map z).2.down = 0) ↔ z.down = 0
    have hh := orderedModelHomeomorph_zero_iff a.degree b.degree
      ((orderedModelHomeomorph a.degree b.degree).symm z)
    change ((orderedModelHomeomorph a.degree b.degree).symm z).1.down = 0 ∧
      ((orderedModelHomeomorph a.degree b.degree).symm z).2.down = 0 ↔ z.down = 0
    simpa only [Homeomorph.apply_symm_apply] using hh.symm
  · rfl
  change HEq (supportedCup R μ _ _).value
    (relativePullback R (orderedModelProductIso a.degree b.degree).inv (a.degree+b.degree)
      (modelExternalProduct R μ a.degree b.degree a.value b.value))
  rw [supportedCup_value]
  let X := (modelPair.{w} a.degree).space
  let Y := (modelPair.{w} b.degree).space
  let P := productSubspaces X Y (modelPair.{w} a.degree).subspace
    (modelPair.{w} b.degree).subspace
  let Q : TwoSubspaces := ⟨(modelPair.{w} (a.degree+b.degree)).space,
    (modelLeftBlock a.degree b.degree) ⁻¹' (modelPair.{w} a.degree).subspace,
    (modelRightBlock a.degree b.degree) ⁻¹' (modelPair.{w} b.degree).subspace⟩
  let m : Q.Map P := ⟨(orderedModelProductIso a.degree b.degree).inv.map,
    fun _ h => h, fun _ h => h⟩
  have hQ : Q.IsOpen :=
    ⟨(modelPair_isOpen _).preimage (modelLeftBlock _ _).hom.continuous,
     (modelPair_isOpen _).preimage (modelRightBlock _ _).hom.continuous⟩
  have hP : P.IsOpen := productSubspaces_isOpen _ _ _ _ (modelPair_isOpen _) (modelPair_isOpen _)
  have h := μ.naturality Q P hQ hP m a.degree b.degree
    (relativePullback R (productLeftProjection X Y _ _) a.degree a.value)
    (relativePullback R (productRightProjection X Y _ _) b.degree b.value)
  have hl := relativePullback_comp' R m.leftMap (productLeftProjection X Y _ _) a.degree a.value
  have hr := relativePullback_comp' R m.rightMap (productRightProjection X Y _ _) b.degree b.value
  rw [hl, hr] at h
  change relativePullback R m.unionMap (a.degree+b.degree)
    (modelExternalProduct R μ a.degree b.degree a.value b.value) =
      μ.product Q hQ a.degree b.degree
        (relativePullback R
          (⟨modelLeftBlock a.degree b.degree, fun _ h => h⟩ : Q.leftPair ⟶ modelPair a.degree)
          a.degree a.value ⊗ₜ[R]
         relativePullback R
          (⟨modelRightBlock a.degree b.degree, fun _ h => h⟩ : Q.rightPair ⟶ modelPair b.degree)
          b.degree b.value) at h
  dsimp only [supportedPullback, modelSupported]
  change HEq (relativePullback R _ (a.degree+b.degree)
    (μ.product Q hQ a.degree b.degree
      (relativePullback R _ a.degree a.value ⊗ₜ[R]
       relativePullback R _ b.degree b.value))) _
  rw [← h, relativePullback_comp']
  apply relativePullback_heq R
  · ext z
    change ¬ ((((orderedModelProductIso a.degree b.degree).inv.map z).1.down = 0) ∧
      (((orderedModelProductIso a.degree b.degree).inv.map z).2.down = 0)) ↔ z.down ≠ 0
    apply not_congr
    have hh := orderedModelHomeomorph_zero_iff a.degree b.degree
      ((orderedModelHomeomorph a.degree b.degree).symm z)
    change ((orderedModelHomeomorph a.degree b.degree).symm z).1.down = 0 ∧
      ((orderedModelHomeomorph a.degree b.degree).symm z).2.down = 0 ↔ z.down = 0
    simpa only [Homeomorph.apply_symm_apply] using hh.symm
  · exact Category.id_comp _

/-- Ordered block projections from the right-associated flattened normal model. -/
def modelBlockProjection (μ : NaturalRelativeCupProduct.{u,w} R) :
    (k : ℕ) → (F : Fin (k+1) → ModelClass.{u,w} R) →
      (j : Fin (k+1)) →
        (modelPair.{w} (orderedModelCup R μ k F).degree).space ⟶ (modelPair.{w} (F j).degree).space
  | 0, F => Fin.cases (𝟙 _) (fun j => Fin.elim0 j)
  | k+1, F => Fin.cases
      (modelLeftBlock (F 0).degree (orderedModelCup R μ k (fun j => F j.succ)).degree)
      (fun j => modelRightBlock (F 0).degree
        (orderedModelCup R μ k (fun j => F j.succ)).degree ≫
          modelBlockProjection μ k (fun j => F j.succ) j)

lemma orderedModelCup_as_supportedCup (μ : NaturalRelativeCupProduct.{u,w} R)
    (k : ℕ) (F : Fin (k+1) → ModelClass.{u,w} R) :
    orderedCup R μ k (fun j => supportedPullback R (modelBlockProjection R μ k F j)
      (modelSupported R (F j))) = modelSupported R (orderedModelCup R μ k F) := by
  induction k with
  | zero =>
    change supportedPullback R (𝟙 _) (modelSupported R (F 0)) = _
    exact supportedPullback_id R _
  | succ k ih =>
    simp only [orderedCup, modelBlockProjection, Fin.cases_zero, Fin.cases_succ]
    have ht :
        orderedCup R μ k (fun j =>
          supportedPullback R
            (modelRightBlock (F 0).degree
              (orderedModelCup R μ k (fun j => F j.succ)).degree ≫
                modelBlockProjection R μ k (fun j => F j.succ) j)
            (modelSupported R (F j.succ))) =
        supportedPullback R
          (modelRightBlock (F 0).degree (orderedModelCup R μ k (fun j => F j.succ)).degree)
          (modelSupported R (orderedModelCup R μ k (fun j => F j.succ))) := by
      rw [← ih, orderedCup_pullback]
      congr 1
      funext j
      exact (supportedPullback_comp R _ _ _).symm
    rw [ht]
    exact modelCup_as_supportedCup R μ _ _

lemma orderedModelCup_local_pullback {X : TopCat.{w}}
    (μ : NaturalRelativeCupProduct.{u,w} R) (k : ℕ)
    (F : Fin (k+1) → ModelClass.{u,w} R)
    (f : X ⟶ (modelPair.{w} (orderedModelCup R μ k F).degree).space) :
    orderedCup R μ k (fun j =>
      supportedPullback R (f ≫ modelBlockProjection R μ k F j) (modelSupported R (F j))) =
      supportedPullback R f (modelSupported R (orderedModelCup R μ k F)) := by
  rw [← orderedModelCup_as_supportedCup, orderedCup_pullback]
  congr 1
  funext j
  exact (supportedPullback_comp R _ _ _).symm



open P202Specs.TransverseThomProduct P202Specs.RelativeCupProduct
  P202Specs.RelativeSingularChains P202Specs.CohomologyPairs P202Specs.ThomClass
open SmoothManifolds.ModelData
variable (R : Type u) [CommRing R]

/-- Split off the first original ordered normal block. -/
def splitFiniteBlocks (k : ℕ) (D : Fin (k+2) → ℕ) :
    (∀ j, Euclidean (D j)) ≃ₜ Euclidean (D 0) × (∀ j : Fin (k+1), Euclidean (D j.succ)) where
  toFun := fun z => (z 0, fun j => z j.succ)
  invFun := fun z => Fin.cases z.1 z.2
  left_inv := by intro z; funext j; exact Fin.cases rfl (fun _ => rfl) j
  right_inv := by intro z; rfl
  continuous_toFun := (continuous_apply 0).prodMk
    (continuous_pi (fun j => continuous_apply j.succ))
  continuous_invFun := continuous_pi (fun j => Fin.cases continuous_fst
    (fun i => (continuous_apply i).comp continuous_snd) j)

/-- Flatten the normal blocks in the given order, with no permutation. -/
def modelBlocksHomeomorph (μ : NaturalRelativeCupProduct.{u,w} R) :
    (k : ℕ) → (F : Fin (k+1) → ModelClass.{u,w} R) →
      ULift.{w} (∀ j, Euclidean (F j).degree) ≃ₜ
        (modelPair.{w} (orderedModelCup R μ k F).degree).space
  | 0, F => by
    letI : Unique (Fin (0+1)) := Fin.instUnique
    change ULift.{w} (∀ j, Euclidean (F j).degree) ≃ₜ ULift.{w} (Euclidean (F 0).degree)
    exact (Homeomorph.ulift.trans (Homeomorph.piUnique _)).trans Homeomorph.ulift.symm
  | k+1, F =>
    (Homeomorph.ulift.trans (splitFiniteBlocks k (fun j => (F j).degree))).trans
      ((Homeomorph.ulift.symm.prodCongr
        (Homeomorph.ulift.symm.trans (modelBlocksHomeomorph μ k (fun j => F j.succ)))).trans
          (orderedModelHomeomorph _ _))

lemma modelLeftBlock_ordered (p q : ℕ)
    (x : (modelPair.{w} p).space) (y : (modelPair.{w} q).space) :
    modelLeftBlock p q (orderedModelHomeomorph p q (x,y)) = x := by
  change ((orderedModelHomeomorph p q).symm (orderedModelHomeomorph p q (x,y))).1 = x
  rw [Homeomorph.symm_apply_apply]

lemma modelRightBlock_ordered (p q : ℕ)
    (x : (modelPair.{w} p).space) (y : (modelPair.{w} q).space) :
    modelRightBlock p q (orderedModelHomeomorph p q (x,y)) = y := by
  change ((orderedModelHomeomorph p q).symm (orderedModelHomeomorph p q (x,y))).2 = y
  rw [Homeomorph.symm_apply_apply]

lemma modelBlockProjection_flatten (μ : NaturalRelativeCupProduct.{u,w} R)
    (k : ℕ) (F : Fin (k+1) → ModelClass.{u,w} R)
    (j : Fin (k+1)) (z : ULift.{w} (∀ j, Euclidean (F j).degree)) :
    modelBlockProjection R μ k F j (modelBlocksHomeomorph R μ k F z) = ⟨z.down j⟩ := by
  induction k with
  | zero =>
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl
  | succ k ih =>
    induction j using Fin.cases with
    | zero =>
      change modelLeftBlock _ _ (orderedModelHomeomorph _ _
        (⟨z.down 0⟩, modelBlocksHomeomorph R μ k (fun j => F j.succ)
          ⟨fun j => z.down j.succ⟩)) = _
      exact modelLeftBlock_ordered _ _ _ _
    | succ j =>
      change modelBlockProjection R μ k (fun j => F j.succ) j
        (modelRightBlock _ _ (orderedModelHomeomorph _ _
          (⟨z.down 0⟩, modelBlocksHomeomorph R μ k (fun j => F j.succ)
            ⟨fun j => z.down j.succ⟩))) = _
      rw [modelRightBlock_ordered]
      exact ih _ j _



open P202Specs.TransverseThomProduct P202Specs.RelativeCupProduct
  P202Specs.RelativeSingularChains P202Specs.CohomologyPairs P202Specs.ThomClass
open SmoothManifolds.ModelData
variable (R : Type u) [CommRing R]

/-- The actual jth projection on the original ordered normal blocks. -/
def rawModelBlockProjection (k : ℕ) (F : Fin (k+1) → ModelClass.{u,w} R)
    (j : Fin (k+1)) :
    TopCat.of (ULift.{w} (∀ j, Euclidean (F j).degree)) ⟶ (modelPair.{w} (F j).degree).space :=
  TopCat.ofHom ⟨fun z => ⟨z.down j⟩,
    continuous_uliftUp.comp ((continuous_apply j).comp continuous_uliftDown)⟩

lemma modelBlockProjection_flatten_map (μ : NaturalRelativeCupProduct.{u,w} R)
    (k : ℕ) (F : Fin (k+1) → ModelClass.{u,w} R) (j : Fin (k+1)) :
    TopCat.ofHom ⟨modelBlocksHomeomorph R μ k F, (modelBlocksHomeomorph R μ k F).continuous⟩ ≫
      modelBlockProjection R μ k F j = rawModelBlockProjection R k F j := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  exact fun z => modelBlockProjection_flatten R μ k F j z

lemma orderedCup_rawModelBlocks (μ : NaturalRelativeCupProduct.{u,w} R)
    (k : ℕ) (F : Fin (k+1) → ModelClass.{u,w} R) :
    orderedCup R μ k (fun j => supportedPullback R
      (rawModelBlockProjection R k F j) (modelSupported R (F j))) =
    supportedPullback R
      (TopCat.ofHom ⟨modelBlocksHomeomorph R μ k F, (modelBlocksHomeomorph R μ k F).continuous⟩)
      (modelSupported R (orderedModelCup R μ k F)) := by
  have h := orderedModelCup_local_pullback R μ k F
    (TopCat.ofHom ⟨modelBlocksHomeomorph R μ k F, (modelBlocksHomeomorph R μ k F).continuous⟩)
  have hh :
      (fun j => supportedPullback R
        (TopCat.ofHom ⟨modelBlocksHomeomorph R μ k F, (modelBlocksHomeomorph R μ k F).continuous⟩ ≫
          modelBlockProjection R μ k F j) (modelSupported R (F j))) =
      (fun j => supportedPullback R (rawModelBlockProjection R k F j) (modelSupported R (F j))) := by
    funext j
    congr 1
    exact modelBlockProjection_flatten_map R μ k F j
  rw [hh] at h
  exact h

/-- A homeomorphism is an isomorphism of the precise inverse-image support pairs. -/
def supportedPairIso {X Y : TopCat.{w}} (e : X ≃ₜ Y) (a : SupportedClass R Y) :
    (⟨X, (e ⁻¹' a.support)ᶜ⟩ : Pair) ≅ (⟨Y, a.supportᶜ⟩ : Pair) where
  hom := ⟨TopCat.ofHom ⟨e, e.continuous⟩, fun _ h => h⟩
  inv := ⟨TopCat.ofHom ⟨e.symm, e.symm.continuous⟩, by
    intro z hz
    change z ∉ a.support at hz
    change e (e.symm z) ∉ a.support
    simpa only [e.apply_symm_apply] using hz⟩
  hom_inv_id := PairMap.ext _ _ (TopCat.hom_ext (ContinuousMap.ext e.symm_apply_apply))
  inv_hom_id := PairMap.ext _ _ (TopCat.hom_ext (ContinuousMap.ext e.apply_symm_apply))

lemma supportedPullback_homeomorph_generates {X Y : TopCat.{w}} (e : X ≃ₜ Y)
    (a : SupportedClass R Y) (ha : Function.Bijective (fun r : R => r • a.value)) :
    Function.Bijective (fun r : R => r •
      (supportedPullback R (TopCat.ofHom ⟨e,e.continuous⟩) a).value) := by
  let E := ((relativeCohomologyFunctor R R (a.degree : ℤ)).mapIso
    (supportedPairIso R e a).op).toLinearEquiv
  have h := E.bijective.comp ha
  change Function.Bijective (fun r : R => E (r • a.value)) at h
  change Function.Bijective (fun r : R => r • E a.value)
  simpa only [E.map_smul] using h



end CupNaturality

section CommonLocalThomModels
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
open P202Specs.ThomClass P202Specs.LocalThomProjection
attribute [local instance] normalTopology

lemma localFactorProjection (n : ℕ) (M : TopCat.{w})
    (S : SmoothManifold n .euclidean M) (N : OrientedSubmanifold R M S)
    (c : HR R (⟨M,N.supportᶜ⟩ : Pair) N.codimension)
    (hc : HasFiberValues R N.orientation c) (p : N.source) :
    ∃ (K : TubularNeighborhood N.normal) (_ : NormalCompatible N.normal K)
      (a : N.source) (U : Set N.source), IsOpen U ∧ p ∈ U ∧
      ∃ hU : U ⊆ (normalBundle N.normal).baseSet a,
      ∃ g : HR R (modelPair.{w} (n-N.dimension)) N.codimension,
        (∀ (q : N.source) (hq : q ∈ U),
          relativePullback R (fiberCoordinates N.normal a q (hU hq)) N.codimension g =
            N.orientation.generator q) ∧
        Function.Bijective (fun r : R => r • g) ∧
        IsOpen (imageRegion N.normal K U) ∧ N.inclusion p ∈ imageRegion N.normal K U ∧
        (∀ y : imageRegion N.normal K U,
          ((ambientCoordinates N.normal K a U hU).map y).down = 0 ↔ y.val ∈ N.support) ∧
        (∀ (B : Pair.{w}) (f : B ⟶ ambientRegionPair N.normal K U),
          relativePullback R (f ≫ ambientRegionInclusion N.normal K U) N.codimension c =
          relativePullback R (f ≫ ambientCoordinates N.normal K a U hU) N.codimension g) := by
  letI := N.compact
  obtain ⟨K,hK⟩ := P202.ThomClass.normalized_tubular_exists N.embedding N.normal
  obtain ⟨a,U,ho,hp,hU,g,hg,hgen,hVo,hVx,hzero,he,hf⟩ :=
    P202.LocalThomProjection.localProjection R N.dimension n N.codimension
      N.source M N.atlas S N.inclusion N.embedding N.normal N.rank
      N.orientation c hc K hK p
  exact ⟨K,hK,a,U,ho,hp,hU,g,hg,hgen,hVo,hVx,hzero,hf⟩

theorem localThomModels :
    P202Specs.TransverseThomProduct.localThomModels_type.{u,w} := by
  intro R _ n k M S F c hc x hx
  classical
  have hxj : ∀ j, ∃ p : (F j).source, (F j).inclusion p = x :=
    fun j => Set.mem_iInter.mp hx j
  choose p hp using hxj
  choose K hK a U hUo hpU hU g hg hgen hVo hVx hz hf using
    (fun j => localFactorProjection R n M S (F j) (c j) (hc j) (p j))
  let V : Set M := ⋂ j, imageRegion (F j).normal (K j) (U j)
  have hV : IsOpen V := isOpen_iInter_of_finite hVo
  have hxV : x ∈ V := Set.mem_iInter.mpr (fun j => hp j ▸ hVx j)
  let f (j : Fin k) : restrictionPair M (F j).support V ⟶
      ambientRegionPair (F j).normal (K j) (U j) := {
    map := TopCat.ofHom ⟨fun y => ⟨y.val, Set.mem_iInter.mp y.property j⟩,
      continuous_subtype_val.subtype_mk _⟩
    mapsTo := fun _ hy => hy }
  refine ⟨{
    neighborhood := V
    isOpen_neighborhood := hV
    mem_neighborhood := hxV
    generator := g
    generates := hgen
    projection := fun j => f j ≫ ambientCoordinates (F j).normal (K j) (a j) (U j) (hU j)
    zero_equations := ?_
    class_formula := ?_ }⟩
  · intro j y
    exact hz j ((f j).map y)
  · intro j
    have hj := hf j _ (f j)
    have heq : f j ≫ ambientRegionInclusion (F j).normal (K j) (U j) =
        restrictionInclusion M (F j).support V := PairMap.ext _ _ rfl
    rw [heq] at hj
    exact hj

end CommonLocalThomModels

section LinearSliceComparison
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202.ThomClass
open scoped Topology

/-- A specified linear coordinate change induces the actual map of punctured
relative pairs. The linear map is retained, including its orientation sign. -/
def linearPuncturedPairIso {E F : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) :
    puncturedVectorPair E ≅ puncturedVectorPair F :=
  P202.ThomClass.pairIsoOfHomeomorph _ _ L.toHomeomorph
    (fun z => by change z ≠ 0 ↔ L z ≠ 0; exact not_congr L.map_eq_zero_iff.symm)

/-- A smooth germ with an invertible prescribed derivative acts on local
relative cohomology by exactly that linear coordinate change. This keeps the
orientation of the derivative, rather than merely proving a generator claim. -/
theorem exists_slice_cohomology_comparison
    {E F : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {U : Set E} (L : E ≃L[ℝ] F)
    (hU : IsOpen U) (h0U : 0 ∈ U) (hfc : ContinuousOn f U) (hf0 : f 0 = 0)
    (hf : HasFDerivAt f L.toContinuousLinearMap 0) :
    ∃ (ε : ℝ) (_ : 0 < ε)
      (g : openPair (puncturedVectorPair E) {z : E | norm z < ε} ⟶
        puncturedVectorPair F),
      {z : E | norm z < ε} ⊆ U ∧ (∀ z, g.map z = f z.val) ∧
      ∀ (R : Type u) [CommRing R] (q : ℤ),
        (relativeCohomologyFunctor R R q).map g.op =
          (relativeCohomologyFunctor R R q).map
            (openPairInclusion (puncturedVectorPair E) {z : E | norm z < ε} ≫
              (linearPuncturedPairIso L).hom).op ∧
        IsIso ((relativeCohomologyFunctor R R q).map g.op) := by
  let f₀ : E → E := L.symm ∘ f
  have hc₀ : ContinuousOn f₀ U := L.symm.continuous.comp_continuousOn hfc
  have hzero : f₀ 0 = 0 := by simp [f₀, hf0]
  have hderiv : HasFDerivAt f₀ (ContinuousLinearMap.id ℝ E) 0 := by
    have hh := L.symm.hasFDerivAt.comp 0 hf
    convert hh using 1
    ext z
    exact (L.symm_apply_apply z).symm
  obtain ⟨ε,hε,g₀,hsmall,hg₀,hcoh⟩ :=
    exists_cohomology_isIsoOn_of_hasFDerivAt_id hU h0U hc₀ hzero hderiv
  let g := g₀ ≫ (linearPuncturedPairIso L).hom
  refine ⟨ε,hε,g,hsmall,?_,?_⟩
  · intro z
    change L (g₀.map z) = f z.val
    rw [hg₀]
    exact L.apply_symm_apply _
  · intro R _ q
    let H := relativeCohomologyFunctor R R q
    obtain ⟨he,hiso⟩ := hcoh R q
    haveI := hiso
    constructor
    · change H.map ((g₀ ≫ (linearPuncturedPairIso L).hom).op) = _
      simp only [op_comp, Functor.map_comp]
      rw [he]
    · change IsIso (H.map ((g₀ ≫ (linearPuncturedPairIso L).hom).op))
      simp only [op_comp, Functor.map_comp]
      infer_instance

end LinearSliceComparison

section GeometricSliceExistence
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData SmoothManifolds.DifferentialData
open P202Specs.TransverseThomProduct P202Specs.ThomClass
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs P202Specs.RelativeCupProduct
attribute [local instance] normalTopology
variable (R : Type u) [CommRing R]
variable {n k : ℕ} {M : TopCat.{w}} {S : SmoothManifold n .euclidean M}

theorem modelOrientationAt_exists (F : Fin k → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) : Nonempty (ModelOrientationAt R F p) := by
  classical
  choose a U hopen hp hU g hg using fun j => (F j).orientation.locally_constant (p j)
  exact ⟨{ chartPoint := a
           base_mem := fun j => hU j (hp j)
           value := g
           prescribed := fun j => hg j (p j) (hp j) }⟩

theorem normalizedIntersectionSlice_of_coordinates
    (F : Fin k → OrientedSubmanifold R M S)
    (x : M) (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x)
    (b : ModelOrientationAt R F p)
    (C : P202Specs.TransverseNormalCoordinates.SimultaneousCoordinates
      (fun j => (F j).embeddedData R) x p h) :
    Nonempty (NormalizedIntersectionSlice R F x p h b) := by
  classical
  let T : normalBlocks R F ≃L[ℝ] normalBlocks R F :=
    ContinuousLinearEquiv.piCongrRight (fun j =>
      ((fiberLinearCoordinates (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).symm.trans
        (fiberLinearCoordinates (F j).normal (C.chartPoint j) (p j) (C.base_mem j))).toContinuousLinearEquiv)
  let V := T ⁻¹' C.sliceDomain
  let s := C.slice ∘ T
  have h0V : (0 : normalBlocks R F) ∈ V := by
    change T 0 ∈ C.sliceDomain
    simpa using C.sliceDomain_zero
  have hs0 : s 0 = x := by simp [s, C.slice_center]
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (C.chart (s z)).val) V :=
    C.slice_smooth.comp T.contDiff.contDiffOn (fun _ hz => hz)
  have hV : IsOpen V := C.sliceDomain_open.preimage T.continuous
  have hd := (C.slice_smooth.contDiffAt
    (C.sliceDomain_open.mem_nhds C.sliceDomain_zero)).differentiableAt (by simp)
  let L := (fderiv ℝ (fun z => (C.chart (C.slice z)).val) 0).comp T.toContinuousLinearMap
  have hds : HasFDerivAt (fun z => (C.chart (s z)).val) L 0 := by
    have hdz : HasFDerivAt (fun z => (C.chart (C.slice z)).val)
        (fderiv ℝ (fun z => (C.chart (C.slice z)).val) 0) (T 0) := by
      simpa only [map_zero] using hd.hasFDerivAt
    exact hdz.comp 0 T.hasFDerivAt
  refine ⟨{
    domain := V
    domain_open := hV
    domain_zero := h0V
    slice := s
    center := hs0
    chart := C.chart
    chart_mem := C.chart_mem
    in_chart := fun z hz => C.source_in_chart (C.slice_mem _ hz)
    smooth := hsmooth
    continuous := C.slice_continuous.comp T.continuous.continuousOn (fun _ hz => hz)
    injective := fun z hz w hw he => T.injective (C.slice_injective hz hw he)
    tangentCoordinates := C.tangentCoordinates
    tangent_isCoordinates := C.tangent_isCoordinates
    derivative := L
    has_derivative := hds
    normal_derivative := ?_
    avoids := ?_ }⟩
  · intro v j
    have hh := C.slice_normal_derivative (T v) j
    rw [embeddedData_projection] at hh
    change normalProjectionAt R (F j) (p j) x (h j)
      (C.tangentCoordinates.symm
        (fderiv ℝ (fun z => (C.chart (C.slice z)).val) 0 (T v))) = _
    change normalProjectionAt R (F j) (p j) x (h j)
      (C.tangentCoordinates.symm
        (fderiv ℝ (fun z => (C.chart (C.slice z)).val) 0 (T v))) = _ at hh
    rw [hh]
    change (fiberLinearCoordinates (F j).normal (C.chartPoint j) (p j) (C.base_mem j)).symm
      ((fiberLinearCoordinates (F j).normal (C.chartPoint j) (p j) (C.base_mem j))
        ((fiberLinearCoordinates (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).symm (v j))) = _
    exact LinearEquiv.symm_apply_apply _ _
  · intro z hz hz0 hmem
    apply hz0
    apply T.injective
    rw [map_zero]
    funext j
    exact (C.slice_zero_equations (T z) hz j).mp
      (Set.mem_iInter.mp hmem j)

theorem normalizedIntersectionSlice_exists
    (F : Fin k → OrientedSubmanifold R M S) (hF : IsTransverse R F)
    (x : M) (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x)
    (b : ModelOrientationAt R F p) : Nonempty (NormalizedIntersectionSlice R F x p h b) := by
  obtain ⟨C⟩ := normalCoordinates R n k M S F hF x p h
  exact normalizedIntersectionSlice_of_coordinates R F x p h b C


end GeometricSliceExistence

section FixedProjectionGeometry
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.MapData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
open Filter Set
open scoped Topology
namespace ProjectionGeometry
open P202Specs.TransverseNormalCoordinates P202Specs.ThomClass
  P202Specs.LocalThomProjection P202.TransverseNormalCoordinates
attribute [local instance] normalTopology
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

lemma ambientCoordinates_fiber (A : EmbeddedData S) (K : TubularNeighborhood A.normal)
    (a : A.source) (U : Set A.source) (hU : U ⊆ (normalBundle A.normal).baseSet a)
    (x : imageRegion A.normal K U) :
    ((ambientCoordinates A.normal K a U hU).map x).down =
      fiberLinearCoordinates A.normal a
        (((regionHomeomorph A.normal K U).symm x).val.proj)
        (hU ((regionHomeomorph A.normal K U).symm x).property.2)
        (((regionHomeomorph A.normal K U).symm x).val.snd) := by
  rfl

/-- Local smooth representatives of a prescribed normalized tubular projection.
The chart and tubular map are fixed before the construction, so this formula
can be used with the actual local Thom projection theorem. -/
theorem fixed_normal_equation (A : EmbeddedData S) (p : A.source)
    (K : TubularNeighborhood A.normal) (hK : NormalCompatible A.normal K)
    (a : A.source) (U : Set A.source) (hUopen : IsOpen U) (hpU : p ∈ U)
    (hU : U ⊆ (normalBundle A.normal).baseSet a)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hxd : A.inclusion p ∈ d.source)
    (C : TangentSpace S (A.inclusion p) ≃ₗ[ℝ] Euclidean n)
    (hC : IsChartCoordinates S (A.inclusion p) d C) :
    ∃ (O : Set (Euclidean n)) (f : Euclidean n → Euclidean (n-A.dimension))
      (D : Euclidean n →L[ℝ] Euclidean (n-A.dimension)) (V : Set M),
      IsOpen O ∧ (d (A.inclusion p)).val ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) f O ∧
      HasFDerivAt f D (d (A.inclusion p)).val ∧
      (∀ v, D (C v) = fiberLinearCoordinates A.normal a p (hU hpU)
        (normalProjection A p (A.inclusion p) rfl v)) ∧
      IsOpen V ∧ A.inclusion p ∈ V ∧ V ⊆ d.source ∧
      ∃ hV : V ⊆ imageRegion A.normal K U,
        ∀ y (hy : y ∈ V), (d y).val ∈ O ∧
          f (d y).val =
            ((ambientCoordinates A.normal K a U hU).map ⟨y, hV hy⟩).down := by
  let N := A.normal
  let B := normalBundle N
  obtain ⟨F, G, hF, hG, heF, heG⟩ := P202.ThomClass.tubular_smoothRepresentatives N K p
  obtain ⟨c, hc, hpc⟩ := A.manifold.smoothStructure.property.1.1 p
  let b := bundleChart B.coordinates (B.trivialization a) c
  have hb : b ∈ B.totalManifold.smoothStructure.val := B.chart_mem a c hc
  have hpbase : p ∈ (B.trivialization a).baseSet :=
    (B.trivialization_baseSet a).symm ▸ hU hpU
  have hzb : normalZero N p ∈ b.source :=
    (mem_bundleChart_source _ _ _ _).mpr ⟨hpbase, hpc⟩
  have hiK : A.inclusion p ∈ K.target := K.inclusion_mem ⟨p, rfl⟩
  have hGzero : G (A.inclusion p) = normalZero N p := by
    rw [heG _ hiK]
    have he : (⟨A.inclusion p, hiK⟩ : K.target) =
        K.homeomorph ⟨normalZero N p, K.zero_mem p⟩ := Subtype.ext (K.zero_eq p).symm
    rw [he, K.homeomorph.symm_apply_apply]
  have hbG : G (A.inclusion p) ∈ b.source := hGzero.symm ▸ hzb
  obtain ⟨O, hO, haO, H, hH, heH⟩ := (hG _ hiK).2 d hd b hb hxd hbG
  let I : Euclidean n →L[ℝ] Euclidean (A.dimension+(n-A.dimension)) :=
    fderiv ℝ H (d (A.inclusion p)).val
  have hI : SmoothManifolds.FiniteRegularityData.HasCoordinateDerivative d
      (fun y => (b (G y)).val) (A.inclusion p) I :=
    ⟨H, (hH.contDiffAt (hO.mem_nhds haO)).differentiableAt (by simp) |>.hasFDerivAt, heH⟩
  obtain ⟨J, hJ, hnJ⟩ := full_derivative_in_chart A.embedding N K hK F hF heF
    p a (hU hpU) c hc hpc d hd hxd
  have hFG : ∀ᶠ y in 𝓝 (A.inclusion p), F (G y) = y := by
    filter_upwards [K.isOpen_target.mem_nhds hiK] with y hy
    rw [heG y hy, heF _ (K.homeomorph.symm ⟨y, hy⟩).property]
    exact congrArg Subtype.val (K.homeomorph.apply_symm_apply ⟨y, hy⟩)
  have hJI := P202.ThomClass.coordinate_inverse_derivative b d F G
    (normalZero N p) (A.inclusion p) hxd hGzero (hG _ hiK).1 hFG J I hJ hI
  let R : Euclidean (A.dimension+(n-A.dimension)) →L[ℝ] Euclidean (n-A.dimension) :=
    (ContinuousLinearMap.snd ℝ _ _).comp B.coordinates.linearEquiv.symm.toContinuousLinearMap
  let f := R ∘ H
  let D := R.comp I
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f O := R.contDiff.comp_contDiffOn hH
  have hD : HasFDerivAt f D (d (A.inclusion p)).val :=
    R.hasFDerivAt.comp _ ((hH.contDiffAt (hO.mem_nhds haO)).differentiableAt (by simp)).hasFDerivAt
  let E := N.ambientTangent.fiberCoordinates.equiv d hd (A.inclusion p) hxd
  have hEC : E = C := SmoothManifolds.TangentBundle.chartCoordinates_unique
    (N.ambientTangent.fiberCoordinates.isCoordinates d hd (A.inclusion p) hxd) hC
  have hnormal (v : TangentSpace S (A.inclusion p)) :
      D (C v) = fiberLinearCoordinates N a p (hU hpU)
        (normalProjection A p (A.inclusion p) rfl v) := by
    rw [← hEC]
    change R (I (E v)) = _
    apply (fiberLinearCoordinates N a p (hU hpU)).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    have hh := hnJ (B.coordinates.linearEquiv.symm (I (E v))).1
      (B.coordinates.linearEquiv.symm (I (E v))).2
    rw [Prod.eta, B.coordinates.linearEquiv.apply_symm_apply] at hh
    have hi : J (I (E v)) = E v := congrArg (fun A => A (E v)) hJI
    rw [hi, LinearEquiv.symm_apply_apply] at hh
    exact hh.symm
  have hVopen := P202.LocalThomProjection.imageRegion_isOpen N K U hUopen
  have hVp := P202.LocalThomProjection.imageRegion_contains N K U p hpU
  have hnear : ∀ᶠ y in 𝓝 (A.inclusion p),
      y ∈ imageRegion N K U ∧ G y ∈ b.source ∧ y ∈ d.source ∧ (d y).val ∈ O ∧
        H (d y).val = (b (G y)).val := by
    have hGb := (hG _ hiK).1 (b.open_source.mem_nhds hbG)
    have hdc := continuous_subtype_val.continuousAt.comp (d.continuousAt hxd)
    filter_upwards [hVopen.mem_nhds hVp, hGb, d.open_source.mem_nhds hxd,
      hdc (hO.mem_nhds haO), heH] with y hy hyb hyd hyO hyH
    exact ⟨hy, hyb, hyd, hyO, hyH⟩
  obtain ⟨V, hVsub, hVopen, hpV⟩ := mem_nhds_iff.mp hnear
  have hV : V ⊆ imageRegion N K U := fun y hy => (hVsub hy).1
  refine ⟨O, f, D, V, hO, haO, hf, hD, hnormal, hVopen, hpV,
    (fun y hy => (hVsub hy).2.2.1), hV, ?_⟩
  intro y hy
  obtain ⟨hyV, hyb, hyd, hyO, hyH⟩ := hVsub hy
  refine ⟨hyO, ?_⟩
  let z := (regionHomeomorph N K U).symm ⟨y, hV hy⟩
  have hzy : (K.homeomorph ⟨z.val, z.property.1⟩).val = y :=
    congrArg Subtype.val ((regionHomeomorph N K U).apply_symm_apply ⟨y, hV hy⟩)
  have hyK : y ∈ K.target := hzy ▸ (K.homeomorph ⟨z.val, z.property.1⟩).property
  have hGy : G y = z.val := by
    rw [heG y hyK]
    have he : (⟨y, hyK⟩ : K.target) = K.homeomorph ⟨z.val, z.property.1⟩ := Subtype.ext hzy.symm
    rw [he, K.homeomorph.symm_apply_apply]
  rw [ambientCoordinates_fiber]
  change R (H (d y).val) = fiberLinearCoordinates N a z.val.proj (hU z.property.2) z.val.snd
  rw [hyH, hGy]
  have hzbase : z.val.proj ∈ (B.trivialization a).baseSet :=
    (B.trivialization_baseSet a).symm ▸ hU z.property.2
  rw [bundleChart_val B.coordinates (B.trivialization a) c z.val hzbase]
  change (B.coordinates.linearEquiv.symm (B.coordinates.linearEquiv _)).2 = _
  rw [B.coordinates.linearEquiv.symm_apply_apply]
  rfl

def normalCoordinateChange (F : Fin k → EmbeddedData S) (p a b : ∀ j, (F j).source)
    (ha : ∀ j, p j ∈ (normalBundle (F j).normal).baseSet (a j))
    (hb : ∀ j, p j ∈ (normalBundle (F j).normal).baseSet (b j)) :
    Blocks F ≃L[ℝ] Blocks F :=
  (LinearEquiv.piCongrRight (fun j =>
    (fiberLinearCoordinates (F j).normal (b j) (p j) (hb j)).symm.trans
      (fiberLinearCoordinates (F j).normal (a j) (p j) (ha j)))).toContinuousLinearEquiv


/-- On any normalized normal slice, the prescribed tubular projections have
an invertible derivative equal to the explicit change of fiber coordinates.
No change of block order occurs. -/
theorem projections_on_normal_slice
    {k : ℕ} (F : Fin k → EmbeddedData S) (x : M)
    (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x)
    (b : ∀ j, (F j).source)
    (hb : ∀ j, p j ∈ (normalBundle (F j).normal).baseSet (b j))
    (Q : Set (Blocks F)) (hQ : IsOpen Q) (h0Q : 0 ∈ Q)
    (s : Blocks F → M) (hs0 : s 0 = x)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hsd : ∀ z ∈ Q, s z ∈ d.source)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (d (s z)).val) Q)
    (hscont : ContinuousOn s Q)
    (C : TangentSpace S x ≃ₗ[ℝ] Euclidean n)
    (hC : IsChartCoordinates S x d C)
    (ds : Blocks F →L[ℝ] Euclidean n)
    (hds : HasFDerivAt (fun z => (d (s z)).val) ds 0)
    (hnormal : ∀ v j, normalProjection (F j) (p j) x (h j)
      (C.symm (ds v)) =
        (fiberLinearCoordinates (F j).normal (b j) (p j) (hb j)).symm (v j))
    (K : ∀ j, TubularNeighborhood (F j).normal)
    (hK : ∀ j, NormalCompatible (F j).normal (K j))
    (a : ∀ j, (F j).source) (U : ∀ j, Set (F j).source)
    (hUopen : ∀ j, IsOpen (U j)) (hpU : ∀ j, p j ∈ U j)
    (hU : ∀ j, U j ⊆ (normalBundle (F j).normal).baseSet (a j)) :
    ∃ (V : Set (Blocks F)) (f : Blocks F → Blocks F),
      IsOpen V ∧ 0 ∈ V ∧ V ⊆ Q ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f V ∧ f 0 = 0 ∧
      HasFDerivAt f
        (normalCoordinateChange F p a b (fun j => hU j (hpU j)) hb).toContinuousLinearMap 0 ∧
      ∃ hsource : ∀ z ∈ V, ∀ j, s z ∈ imageRegion (F j).normal (K j) (U j),
        ∀ z (hz : z ∈ V) j, f z j =
          ((ambientCoordinates (F j).normal (K j) (a j) (U j) (hU j)).map
            ⟨s z, hsource z hz j⟩).down := by
  classical
  have hxd : x ∈ d.source := by
    rw [← hs0]
    exact hsd 0 h0Q
  have hlocal (j : Fin k) :
      ∃ (O : Set (Euclidean n)) (f : Euclidean n → Euclidean (n-(F j).dimension))
        (D : Euclidean n →L[ℝ] Euclidean (n-(F j).dimension)) (V : Set M),
        IsOpen O ∧ (d x).val ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) f O ∧
        HasFDerivAt f D (d x).val ∧
        (∀ v, D (C v) =
          fiberLinearCoordinates (F j).normal (a j) (p j) (hU j (hpU j))
            (normalProjection (F j) (p j) x (h j) v)) ∧
        IsOpen V ∧ x ∈ V ∧ V ⊆ d.source ∧
        ∃ hV : V ⊆ imageRegion (F j).normal (K j) (U j),
          ∀ y (hy : y ∈ V), (d y).val ∈ O ∧
            f (d y).val =
              ((ambientCoordinates (F j).normal (K j) (a j) (U j) (hU j)).map
                ⟨y, hV hy⟩).down := by
    have hj := h j
    clear hs0
    subst x
    exact fixed_normal_equation (F j) (p j) (K j) (hK j) (a j) (U j)
      (hUopen j) (hpU j) (hU j) d hd hxd
        C hC
  choose O f D W hO hxO hf hd hn hW hxW hWd hWr hEq using hlocal
  let χ : Euclidean n → Blocks F := fun z j => f j z
  let L : Euclidean n →L[ℝ] Blocks F := ContinuousLinearMap.pi D
  let Z : Set (Euclidean n) := ⋂ j, O j
  have hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ Z := contDiffOn_pi.mpr
    (fun j => (hf j).mono (Set.iInter_subset O j))
  have hχd : HasFDerivAt χ L (d x).val := hasFDerivAt_pi.mpr hd
  let B : Set M := ⋂ j, W j
  have hB : IsOpen B := isOpen_iInter_of_finite hW
  have hxB : x ∈ B := Set.mem_iInter.mpr hxW
  let V := Q ∩ s ⁻¹' B
  have hV : IsOpen V := hscont.isOpen_inter_preimage hQ hB
  have h0V : (0 : Blocks F) ∈ V := by
    refine ⟨h0Q, ?_⟩
    change s 0 ∈ B
    rwa [hs0]
  let f₀ : Blocks F → Blocks F := fun z => χ (d (s z)).val
  have hsV (z : Blocks F) (hz : z ∈ V) (j : Fin k) : s z ∈ W j :=
    Set.mem_iInter.mp hz.2 j
  have hχV : ∀ z ∈ V, (d (s z)).val ∈ Z := by
    intro z hz
    exact Set.mem_iInter.mpr (fun j => (hEq j (s z) (hsV z hz j)).1)
  have hf₀ : ContDiffOn ℝ (⊤ : ℕ∞) f₀ V :=
    hχ.comp (hsmooth.mono Set.inter_subset_left) hχV
  have hf₀zero : f₀ 0 = 0 := by
    funext j
    change f j (d (s 0)).val = 0
    rw [hs0, (hEq j x (hxW j)).2]
    exact (P202.LocalThomProjection.ambientCoordinates_zero_iff
      (F j).normal (K j) (a j) (U j) (hU j) ⟨x, hWr j (hxW j)⟩).mpr ⟨p j, h j⟩
  have hdχ : HasFDerivAt χ L (d (s 0)).val := by
    rwa [hs0]
  have hcomp := hdχ.comp 0 hds
  have hcompD : L.comp ds =
      (normalCoordinateChange F p a b (fun j => hU j (hpU j)) hb).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    funext j
    have hh := hn j (C.symm (ds v))
    rw [LinearEquiv.apply_symm_apply, hnormal] at hh
    exact hh
  rw [hcompD] at hcomp
  have hsource : ∀ z ∈ V, ∀ j, s z ∈ imageRegion (F j).normal (K j) (U j) :=
    fun z hz j => hWr j (hsV z hz j)
  refine ⟨V, f₀, hV, h0V, Set.inter_subset_left, hf₀, hf₀zero, hcomp, hsource, ?_⟩
  intro z hz j
  exact (hEq j (s z) (hsV z hz j)).2

end ProjectionGeometry

end FixedProjectionGeometry


section
open P202Specs.TransverseThomProduct P202Specs.ThomClass
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs P202Specs.RelativeCupProduct
attribute [local instance] normalTopology
variable (R : Type u) [CommRing R]
variable {n k : ℕ} {M : TopCat.{w}} {S : SmoothManifold n .euclidean M}

def orientationBlockTransition (F : Fin k → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b b' : ModelOrientationAt R F p) :
    normalBlocks R F ≃L[ℝ] normalBlocks R F :=
  ContinuousLinearEquiv.piCongrRight (fun j =>
    ((fiberLinearCoordinates (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).symm.trans
      (fiberLinearCoordinates (F j).normal (b'.chartPoint j) (p j) (b'.base_mem j))).toContinuousLinearEquiv)

def orientationBlockTransitionMap (F : Fin k → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b b' : ModelOrientationAt R F p) :
    normalBlockSpace R F ⟶ normalBlockSpace R F :=
  TopCat.ofHom ⟨fun z => ULift.up (orientationBlockTransition R F p b b' z.down),
    continuous_uliftUp.comp ((orientationBlockTransition R F p b b').continuous.comp
      continuous_uliftDown)⟩

def orientationTransitionPair (F : Fin k → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b b' : ModelOrientationAt R F p) (j : Fin k) :
    modelPair.{w} (n-(F j).dimension) ⟶ modelPair.{w} (n-(F j).dimension) :=
  (P202.ThomClass.fiberCoordinatesIso (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).inv ≫
    (P202.ThomClass.fiberCoordinatesIso (F j).normal (b'.chartPoint j) (p j) (b'.base_mem j)).hom

lemma orientationTransitionPair_apply (F : Fin k → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b b' : ModelOrientationAt R F p) (j : Fin k)
    (z : (modelPair.{w} (n-(F j).dimension)).space) :
    ((orientationTransitionPair R F p b b' j).map z).down =
      fiberLinearCoordinates (F j).normal (b'.chartPoint j) (p j) (b'.base_mem j)
        ((fiberLinearCoordinates (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).symm z.down) := by
  let v := (fiberLinearCoordinates (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).symm z.down
  have he : (fiberChart (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).symm z =
      (⟨⟨p j, v⟩, rfl⟩ : Fiber (F j).normal (p j)) := by
    apply (fiberChart (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).injective
    rw [Homeomorph.apply_symm_apply]
    apply ULift.ext
    change z.down = fiberLinearCoordinates (F j).normal (b.chartPoint j) (p j) (b.base_mem j) v
    exact (LinearEquiv.apply_symm_apply _ _).symm
  change (fiberChart (F j).normal (b'.chartPoint j) (p j) (b'.base_mem j)
    ((fiberChart (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).symm z)).down = _
  rw [he]
  rfl

lemma orientationTransitionPair_pullback (F : Fin k → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b b' : ModelOrientationAt R F p) (j : Fin k) :
    relativePullback R (orientationTransitionPair R F p b b' j)
      (F j).codimension (b'.value j) = b.value j := by
  let e := P202.ThomClass.fiberCoordinatesIso (F j).normal (b.chartPoint j) (p j) (b.base_mem j)
  change relativePullback R (e.inv ≫ _) (F j).codimension (b'.value j) = _
  rw [← relativePullback_comp']
  change relativePullback R e.inv (F j).codimension
    (relativePullback R (fiberCoordinates (F j).normal (b'.chartPoint j) (p j) (b'.base_mem j))
      (F j).codimension (b'.value j)) = _
  rw [b'.prescribed]
  rw [← b.prescribed j, relativePullback_comp']
  change relativePullback R (e.inv ≫ e.hom) (F j).codimension (b.value j) = _
  rw [e.inv_hom_id]
  change ((relativeCohomologyFunctor R R ((F j).codimension : ℤ)).map (𝟙 _)) (b.value j) = _
  simp

lemma blockSupportedFactor_covariance (F : Fin k → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b b' : ModelOrientationAt R F p) (j : Fin k) :
    supportedPullback R (orientationBlockTransitionMap R F p b b')
      (blockSupportedFactor R F p b' j) = blockSupportedFactor R F p b j := by
  have hs : (orientationBlockTransitionMap R F p b b') ⁻¹'
      (blockSupportedFactor R F p b' j).support =
      (blockSupportedFactor R F p b j).support := by
    ext z
    change (fiberLinearCoordinates (F j).normal (b'.chartPoint j) (p j) (b'.base_mem j))
      ((fiberLinearCoordinates (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).symm
        (z.down j)) = 0 ↔ z.down j = 0
    simp only [LinearEquiv.map_eq_zero_iff]
  apply supportedClass_ext R
  · exact hs
  · rfl
  let f : (⟨normalBlockSpace R F,
      ((orientationBlockTransitionMap R F p b b') ⁻¹' {z | z.down j = 0})ᶜ⟩ : Pair) ⟶
      (⟨normalBlockSpace R F, {z | z.down j ≠ 0}⟩ : Pair) :=
    ⟨orientationBlockTransitionMap R F p b b', fun _ hz => hz⟩
  change HEq (relativePullback R f (F j).codimension
    (relativePullback R (blockProjectionPair R F j) (F j).codimension (b'.value j)))
    (relativePullback R (blockProjectionPair R F j) (F j).codimension (b.value j))
  rw [relativePullback_comp']
  apply HEq.trans (b := relativePullback R
    (blockProjectionPair R F j ≫ orientationTransitionPair R F p b b' j)
    (F j).codimension (b'.value j))
  · apply relativePullback_heq R
    · exact congrArg Set.compl hs
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      apply ULift.ext
      exact (orientationTransitionPair_apply R F p b b' j _).symm
  · apply heq_of_eq
    rw [← relativePullback_comp', orientationTransitionPair_pullback]

lemma orderedBlockOrientation_covariance (μ : NaturalRelativeCupProduct.{u,w} R)
    (F : Fin (k+1) → OrientedSubmanifold R M S) (p : ∀ j, (F j).source)
    (b b' : ModelOrientationAt R F p) :
    supportedPullback R (orientationBlockTransitionMap R F p b b')
      (orderedCup R μ k (blockSupportedFactor R F p b')) =
      orderedCup R μ k (blockSupportedFactor R F p b) := by
  rw [orderedCup_pullback]
  congr 1
  funext j
  exact blockSupportedFactor_covariance R F p b b' j



end

section
open P202Specs.TransverseThomProduct P202Specs.RelativeCupProduct
  P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
variable (R : Type u) [CommRing R]

/-- Equality in the literal relative pair, using the identity map to identify
exactly equal supports, determines equality of supported homogeneous classes. -/
lemma supportedClass_eq_of_identityPullback {X : TopCat.{w}}
    (a b : SupportedClass R X) (hs : a.support = b.support)
    (hd : a.degree = b.degree)
    (hv : castRelativeDegree R hd a.value =
      relativePullback R
        (⟨𝟙 X, fun z hz => by
          change z ∉ b.support
          rwa [← hs]⟩ : (⟨X,a.supportᶜ⟩ : Pair) ⟶ (⟨X,b.supportᶜ⟩ : Pair))
        b.degree b.value) : a = b := by
  rcases a with ⟨sa, ha, da, va⟩
  rcases b with ⟨sb, hb, db, vb⟩
  dsimp only at hs hd
  subst sb
  subst db
  apply supportedClass_ext R
  · rfl
  · rfl
  apply heq_of_eq
  change va = relativePullback R (𝟙 (⟨X,saᶜ⟩ : Pair)) da vb at hv
  change va = ((relativeCohomologyFunctor R R (da : ℤ)).map (𝟙 _)) vb at hv
  simpa using hv

/-- An exact class formula along the given map, with the exact inverse-image
support and declared degree, is equality of the actual supported classes. -/
lemma supportedClass_eq_pullback_of_formula {X Y : TopCat.{w}}
    (f : X ⟶ Y) (a : SupportedClass R X) (b : SupportedClass R Y)
    (hs : a.support = f ⁻¹' b.support) (hd : a.degree = b.degree)
    (F : (⟨X,a.supportᶜ⟩ : Pair) ⟶ (⟨Y,b.supportᶜ⟩ : Pair))
    (hF : F.map = f)
    (hv : castRelativeDegree R hd a.value = relativePullback R F b.degree b.value) :
    a = supportedPullback R f b := by
  apply supportedClass_eq_of_identityPullback R a (supportedPullback R f b) hs hd
  change castRelativeDegree R hd a.value =
    relativePullback R _ b.degree (relativePullback R _ b.degree b.value)
  rw [relativePullback_comp']
  rw [hv]
  congr 1
  congr 1
  apply PairMap.ext
  change F.map = (𝟙 X) ≫ f
  simpa using hF

/-- A common-source relative class formula gives equality of pullbacks, even
when their inverse-image support sets have different expressions. -/
lemma supportedPullbacks_eq_of_formula {X Y Z : TopCat.{w}}
    (f : Z ⟶ X) (g : Z ⟶ Y) (a : SupportedClass R X) (b : SupportedClass R Y)
    (hs : f ⁻¹' a.support = g ⁻¹' b.support) (hd : a.degree = b.degree)
    (G : (⟨Z,(f ⁻¹' a.support)ᶜ⟩ : Pair) ⟶ (⟨Y,b.supportᶜ⟩ : Pair))
    (hG : G.map = g)
    (hv : castRelativeDegree R hd
      (relativePullback R
        (⟨f, fun _ hz => hz⟩ : (⟨Z,(f ⁻¹' a.support)ᶜ⟩ : Pair) ⟶ (⟨X,a.supportᶜ⟩ : Pair))
        a.degree a.value) = relativePullback R G b.degree b.value) :
    supportedPullback R f a = supportedPullback R g b := by
  exact supportedClass_eq_pullback_of_formula R g (supportedPullback R f a) b hs hd G hG hv

/-- Factorwise local comparisons assemble to the full finite relative cup
comparison by actual naturality, retaining the finite factor order. -/
lemma orderedCup_pullbacks_eq_of_factor_equalities {X Y Z : TopCat.{w}}
    (μ : NaturalRelativeCupProduct.{u,w} R) (f : Z ⟶ X) (g : Z ⟶ Y)
    (k : ℕ) (a : Fin (k+1) → SupportedClass R X)
    (b : Fin (k+1) → SupportedClass R Y)
    (h : ∀ j, supportedPullback R f (a j) = supportedPullback R g (b j)) :
    supportedPullback R f (orderedCup R μ k a) =
      supportedPullback R g (orderedCup R μ k b) := by
  rw [orderedCup_pullback, orderedCup_pullback]
  congr 1
  exact funext h



end

section
open P202.ThomClass
lemma supportedClass_value_heq_of_eq {X : TopCat.{w}} {a b : SupportedClass R X}
    (h : a = b) : HEq a.value b.value := by
  cases h
  rfl

/-- Equality of supported classes can be checked on any open neighborhood of
their common support, using the actual excision-inclusion map. -/
lemma supportedClass_eq_of_restriction {X : TopCat.{w}}
    (a b : SupportedClass R X) (hs : a.support = b.support) (hd : a.degree = b.degree)
    (U : Set X) (hU : IsOpen U) (hsU : a.support ⊆ U)
    (h : supportedPullback R (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ X) a =
      supportedPullback R (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ X) b) :
    a = b := by
  cases a with
  | mk s cs d av =>
    cases b with
    | mk t ct e bv =>
      dsimp only at hs hd hsU
      subst t
      subst e
      refine supportedClass_ext R (a := ⟨s,cs,d,av⟩) (b := ⟨s,ct,d,bv⟩) rfl rfl ?_
      apply heq_of_eq
      let P : Pair := ⟨X,sᶜ⟩
      let f := (relativeCohomologyFunctor R R (d : ℤ)).map (openPairInclusion P U).op
      haveI : IsIso f := openPairInclusion_isIso P cs.isOpen_compl U hU
        (by intro z hz; exact hsU (not_not.mp hz)) R (d : ℤ)
      apply (ModuleCat.mono_iff_injective f).mp inferInstance
      exact eq_of_heq (supportedClass_value_heq_of_eq R h)


end

section
open CategoryTheory Opposite
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202.ThomClass P202.TransverseThomProduct
namespace LiftedSliceComparison

/-- Punctured vector pair in the original geometry universe, using the exact
`down ≠ 0` face of normal-block pairs. -/
def liftedPuncturedPair (E : Type) [NormedAddCommGroup E] : Pair.{w} :=
  ⟨TopCat.of (ULift.{w} E), {z | z.down ≠ 0}⟩

/-- A prescribed linear coordinate change on lifted normal blocks. -/
def liftedLinearPairIso {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) : liftedPuncturedPair.{w} E ≅ liftedPuncturedPair.{w} E :=
  pairIsoOfHomeomorph _ _
    (Homeomorph.ulift.trans (L.toHomeomorph.trans Homeomorph.ulift.symm))
    (fun z => by
      change z.down ≠ 0 ↔ L z.down ≠ 0
      exact not_congr L.map_eq_zero_iff.symm)

private def liftedPairIso (E : Type) [NormedAddCommGroup E] :
    liftedPuncturedPair.{w} E ≅ puncturedVectorPair (ULift.{w} E) :=
  pairIsoOfHomeomorph _ _ (Homeomorph.refl _) (fun z => by
    change (z : ULift.{w} E).down ≠ 0 ↔ (z : ULift.{w} E) ≠ (0 : ULift.{w} E)
    constructor
    · intro hz he
      exact hz (congrArg ULift.down he)
    · intro hz he
      exact hz (ULift.ext he))

private def liftedBallPairIso (E : Type) [NormedAddCommGroup E] (ε : ℝ) :
    openPair (liftedPuncturedPair.{w} E) {z | norm z.down < ε} ≅
      openPair (puncturedVectorPair (ULift.{w} E)) {z | norm z < ε} :=
  pairIsoOfHomeomorph _ _ (Homeomorph.refl _) (fun z => by
    change (z.val : ULift.{w} E).down ≠ 0 ↔ (z.val : ULift.{w} E) ≠ (0 : ULift.{w} E)
    constructor
    · intro hz he
      exact hz (congrArg ULift.down he)
    · intro hz he
      exact hz (ULift.ext he))

/-- The local comparison is expressed on the exact lifted punctured pairs used
by an arbitrary geometric normal slice. The linear map, including its sign,
is retained in the literal pullback equality. -/
theorem exists_lifted_slice_cohomology_comparison
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {U : Set E} (L : E ≃L[ℝ] E)
    (hU : IsOpen U) (h0U : 0 ∈ U) (hfc : ContinuousOn f U) (hf0 : f 0 = 0)
    (hf : HasFDerivAt f L.toContinuousLinearMap 0) :
    ∃ (ε : ℝ) (_ : 0 < ε)
      (g : openPair (liftedPuncturedPair.{w} E) {z | norm z.down < ε} ⟶
        liftedPuncturedPair.{w} E),
      {z : E | norm z < ε} ⊆ U ∧
      (∀ z, (g.map z).down = f z.val.down) ∧
      ∀ (R : Type u) [CommRing R] (q : ℤ),
        (relativeCohomologyFunctor R R q).map g.op =
          (relativeCohomologyFunctor R R q).map
            (openPairInclusion (liftedPuncturedPair.{w} E) {z | norm z.down < ε} ≫
              (liftedLinearPairIso L).hom).op ∧
        IsIso ((relativeCohomologyFunctor R R q).map g.op) := by
  let e : ULift.{w} E ≃L[ℝ] E := ContinuousLinearEquiv.ulift
  let Lhat : ULift.{w} E ≃L[ℝ] ULift.{w} E := e.trans (L.trans e.symm)
  let fhat : ULift.{w} E → ULift.{w} E := e.symm ∘ f ∘ e
  let Uhat : Set (ULift.{w} E) := e ⁻¹' U
  have hUhat : IsOpen Uhat := hU.preimage e.continuous
  have h0Uhat : (0 : ULift.{w} E) ∈ Uhat := h0U
  have hfchat : ContinuousOn fhat Uhat :=
    e.symm.continuous.comp_continuousOn
      (hfc.comp e.continuous.continuousOn (fun _ hz => hz))
  have hf0hat : fhat 0 = 0 := by simp [fhat, hf0]
  have hfhat : HasFDerivAt fhat Lhat.toContinuousLinearMap 0 := by
    have hh := e.symm.hasFDerivAt.comp 0 (hf.comp 0 e.hasFDerivAt)
    exact hh
  obtain ⟨ε,hε,g₀,hsmall,hg₀,hcoh⟩ :=
    exists_slice_cohomology_comparison Lhat hUhat h0Uhat hfchat hf0hat hfhat
  let a := liftedBallPairIso.{w} E ε
  let b := liftedPairIso.{w} E
  let g := a.hom ≫ g₀ ≫ b.inv
  have hlinear : a.hom ≫
      openPairInclusion (puncturedVectorPair (ULift.{w} E)) {z | norm z < ε} ≫
        (linearPuncturedPairIso Lhat).hom ≫ b.inv =
      openPairInclusion (liftedPuncturedPair.{w} E) {z | norm z.down < ε} ≫
        (liftedLinearPairIso L).hom := PairMap.ext _ _ rfl
  refine ⟨ε,hε,g,?_,?_,?_⟩
  · intro z hz
    exact hsmall (show norm (ULift.up z : ULift.{w} E) < ε from hz)
  · intro z
    change (g₀.map (a.hom.map z)).down = f z.val.down
    rw [hg₀]
    rfl
  · intro R _ q
    let H := relativeCohomologyFunctor R R q
    obtain ⟨he,hiso⟩ := hcoh R q
    haveI := hiso
    constructor
    · change H.map (a.hom ≫ g₀ ≫ b.inv).op = _
      simp only [op_comp, Functor.map_comp]
      rw [he]
      simpa only [H, op_comp, Functor.map_comp, Category.assoc] using
        congrArg (fun f => H.map f.op) hlinear
    · change IsIso (H.map (a.hom ≫ g₀ ≫ b.inv).op)
      simp only [op_comp, Functor.map_comp]
      infer_instance

end LiftedSliceComparison

end


section
open P202Specs.TransverseThomProduct P202Specs.RelativeCupProduct
  P202Specs.RelativeSingularChains P202Specs.CohomologyPairs P202Specs.ThomClass
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
variable (R : Type u) [CommRing R]
variable {n k : ℕ} {M : TopCat.{w}} {S : SmoothManifold n .euclidean M}

def localModelFactor (F : Fin k → OrientedSubmanifold R M S)
    (c : ∀ j, HR R (⟨M,((F j).support)ᶜ⟩ : Pair) (F j).codimension)
    (x : M) (L : LocalThomModels R F c x) (j : Fin k) :
    SupportedClass R (normalBlockSpace R F) where
  support := {z | z.down j = 0}
  closed := isClosed_eq ((continuous_apply j).comp continuous_uliftDown) continuous_const
  degree := (F j).codimension
  value := relativePullback R (blockProjectionPair R F j) (F j).codimension (L.generator j)

def localModelCombinedMap (F : Fin k → OrientedSubmanifold R M S)
    (c : ∀ j, HR R (⟨M,((F j).support)ᶜ⟩ : Pair) (F j).codimension)
    (x : M) (L : LocalThomModels R F c x) : TopCat.of L.neighborhood ⟶ normalBlockSpace R F :=
  TopCat.ofHom ⟨fun y => ULift.up (fun j => ((L.projection j).map y).down),
    continuous_uliftUp.comp (continuous_pi (fun j =>
      continuous_uliftDown.comp (L.projection j).map.hom.continuous))⟩

lemma localModel_factor_comparison (F : Fin k → OrientedSubmanifold R M S)
    (c : ∀ j, HR R (⟨M,((F j).support)ᶜ⟩ : Pair) (F j).codimension)
    (hclosed : ∀ j, IsClosed (F j).support) (x : M) (L : LocalThomModels R F c x)
    (j : Fin k) :
    supportedPullback R (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of L.neighborhood ⟶ M)
      (⟨(F j).support, hclosed j, (F j).codimension, c j⟩ : SupportedClass R M) =
    supportedPullback R (localModelCombinedMap R F c x L) (localModelFactor R F c x L j) := by
  let f : TopCat.of L.neighborhood ⟶ M := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let g := localModelCombinedMap R F c x L
  let a : SupportedClass R M := ⟨(F j).support, hclosed j, (F j).codimension, c j⟩
  let b := localModelFactor R F c x L j
  have hs : f ⁻¹' a.support = g ⁻¹' b.support := by
    ext y
    exact (L.zero_equations j y).symm
  let G : restrictionPair M (F j).support L.neighborhood ⟶
      (⟨normalBlockSpace R F,{z | z.down j ≠ 0}⟩ : Pair) :=
    ⟨g, fun y hy => by
      change ((L.projection j).map y).down ≠ 0
      exact fun hz => hy ((L.zero_equations j y).mp hz)⟩
  apply supportedPullbacks_eq_of_formula R f g a b hs rfl G rfl
  change relativePullback R (restrictionInclusion M (F j).support L.neighborhood)
      (F j).codimension (c j) =
    relativePullback R G (F j).codimension
      (relativePullback R (blockProjectionPair R F j) (F j).codimension (L.generator j))
  rw [relativePullback_comp']
  have hmap : G ≫ blockProjectionPair R F j = L.projection j := PairMap.ext _ _ rfl
  rw [hmap]
  exact L.class_formula j

lemma localModel_orderedCup_comparison (μ : NaturalRelativeCupProduct.{u,w} R)
    (F : Fin (k+1) → OrientedSubmanifold R M S)
    (c : ∀ j, HR R (⟨M,((F j).support)ᶜ⟩ : Pair) (F j).codimension)
    (hclosed : ∀ j, IsClosed (F j).support) (x : M) (L : LocalThomModels R F c x) :
    supportedPullback R (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of L.neighborhood ⟶ M)
      (orderedCup R μ k (fun j =>
        (⟨(F j).support, hclosed j, (F j).codimension, c j⟩ : SupportedClass R M))) =
    supportedPullback R (localModelCombinedMap R F c x L)
      (orderedCup R μ k (localModelFactor R F c x L)) := by
  apply orderedCup_pullbacks_eq_of_factor_equalities
  exact localModel_factor_comparison R F c hclosed x L



end

section
open P202Specs.TransverseThomProduct P202Specs.RelativeCupProduct
  P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
variable (R : Type u) [CommRing R]

/-- Restriction of a supported class to any pair on the same underlying space. -/
def supportedValueOnPair (P : Pair.{w}) (a : SupportedClass R P.space)
    (h : P.subspace ⊆ a.supportᶜ) : HR R P a.degree :=
  relativePullback R
    (⟨𝟙 P.space, h⟩ : P ⟶ (⟨P.space,a.supportᶜ⟩ : Pair)) a.degree a.value

lemma supportedValueOnPair_congr (P : Pair.{w})
    {a b : SupportedClass R P.space} (H : a = b)
    (ha : P.subspace ⊆ a.supportᶜ) (hb : P.subspace ⊆ b.supportᶜ)
    (d : ℕ) (had : a.degree = d) (hbd : b.degree = d) :
    castRelativeDegree R had (supportedValueOnPair R P a ha) =
      castRelativeDegree R hbd (supportedValueOnPair R P b hb) := by
  cases H
  rfl

/-- Supported pullback equality implies equality on every actual source pair
for which the two given pair maps are defined. Only degree transport remains. -/
lemma relativePullbacks_eq_of_supportedPullbacks_eq
    {X Y : TopCat.{w}} (P : Pair.{w}) (a : SupportedClass R X) (b : SupportedClass R Y)
    (f : P ⟶ (⟨X,a.supportᶜ⟩ : Pair)) (g : P ⟶ (⟨Y,b.supportᶜ⟩ : Pair))
    (H : supportedPullback R f.map a = supportedPullback R g.map b)
    (d : ℕ) (had : a.degree = d) (hbd : b.degree = d) :
    castRelativeDegree R had (relativePullback R f a.degree a.value) =
      castRelativeDegree R hbd (relativePullback R g b.degree b.value) := by
  have hc := supportedValueOnPair_congr R P H f.mapsTo g.mapsTo d had hbd
  change castRelativeDegree R had
    (relativePullback R _ a.degree (relativePullback R _ a.degree a.value)) =
    castRelativeDegree R hbd
      (relativePullback R _ b.degree (relativePullback R _ b.degree b.value)) at hc
  rw [relativePullback_comp', relativePullback_comp'] at hc
  have hf : (⟨𝟙 P.space, f.mapsTo⟩ : P ⟶
      (⟨P.space,(f.map ⁻¹' a.support)ᶜ⟩ : Pair)) ≫
      (⟨f.map, fun _ hz => hz⟩ : (⟨P.space,(f.map ⁻¹' a.support)ᶜ⟩ : Pair) ⟶
        (⟨X,a.supportᶜ⟩ : Pair)) = f := PairMap.ext _ _ (Category.id_comp _)
  have hg : (⟨𝟙 P.space, g.mapsTo⟩ : P ⟶
      (⟨P.space,(g.map ⁻¹' b.support)ᶜ⟩ : Pair)) ≫
      (⟨g.map, fun _ hz => hz⟩ : (⟨P.space,(g.map ⁻¹' b.support)ᶜ⟩ : Pair) ⟶
        (⟨Y,b.supportᶜ⟩ : Pair)) = g := PairMap.ext _ _ (Category.id_comp _)
  rw [hf,hg] at hc
  exact hc

variable {n k : ℕ} {M : TopCat.{w}} {S : SmoothManifold n .euclidean M}
  {F : Fin k → OrientedSubmanifold R M S}
  {x : M} {p : ∀ j, (F j).source} {h : ∀ j, (F j).inclusion (p j) = x}
  {b : ModelOrientationAt R F p}

def sliceAmbientTopMap (s : NormalizedIntersectionSlice R F x p h b) : s.pair.space ⟶ M :=
  TopCat.ofHom ⟨fun z => s.slice z.val.down,
    s.continuous.comp_continuous (continuous_uliftDown.comp continuous_subtype_val)
      (fun z => z.property)⟩

def sliceBlockTopMap (s : NormalizedIntersectionSlice R F x p h b) :
    s.pair.space ⟶ normalBlockSpace R F :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

lemma sliceAmbient_supportedPullback_support
    (s : NormalizedIntersectionSlice R F x p h b)
    (A : SupportedClass R M) (hA : A.support = intersectionSupport R F) :
    (supportedPullback R (sliceAmbientTopMap R s) A).support = {z | z.val.down = 0} := by
  ext z
  change s.slice z.val.down ∈ A.support ↔ z.val.down = 0
  rw [hA]
  constructor
  · intro hz
    by_contra hn
    exact s.avoids z.val.down z.property hn hz
  · intro hz
    rw [hz, s.center]
    exact Set.mem_iInter.mpr (fun j => ⟨p j, h j⟩)

lemma sliceBlock_supportedPullback_support
    (s : NormalizedIntersectionSlice R F x p h b)
    (B : SupportedClass R (normalBlockSpace R F)) (hB : B.support = zeroBlockSupport R F) :
    (supportedPullback R (sliceBlockTopMap R s) B).support = {z | z.val.down = 0} := by
  ext z
  change z.val ∈ B.support ↔ z.val.down = 0
  rw [hB]
  rfl

/-- This is precisely the equality in the full nonempty transverse target. -/
lemma slice_relativeEquality_of_supportedEquality
    (s : NormalizedIntersectionSlice R F x p h b)
    (A : SupportedClass R M) (B : SupportedClass R (normalBlockSpace R F))
    (hA : A.support = intersectionSupport R F) (hB : B.support = zeroBlockSupport R F)
    (d : ℕ) (hAd : A.degree = d) (hBd : B.degree = d)
    (H : supportedPullback R (sliceAmbientTopMap R s) A =
      supportedPullback R (sliceBlockTopMap R s) B) :
    castRelativeDegree R hAd (relativePullback R (s.toAmbient A hA) A.degree A.value) =
      castRelativeDegree R hBd (relativePullback R (s.toBlocks B hB) B.degree B.value) := by
  exact relativePullbacks_eq_of_supportedPullbacks_eq R s.pair A B
    (s.toAmbient A hA) (s.toBlocks B hB) H d hAd hBd



end

namespace LiftedSliceComparison
open P202.ThomClass
/-- On a sufficiently small lifted ball, the nonlinear germ and its prescribed
linear derivative induce the same supported class for EVERY class supported at
zero. The original derivative determines the orientation sign. -/
theorem exists_lifted_supported_comparison
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {U : Set E} (L : E ≃L[ℝ] E)
    (hU : IsOpen U) (h0U : 0 ∈ U) (hfc : ContinuousOn f U) (hf0 : f 0 = 0)
    (hf : HasFDerivAt f L.toContinuousLinearMap 0) :
    ∃ (ε : ℝ) (_ : 0 < ε)
      (g : openPair (liftedPuncturedPair.{w} E) {z | norm z.down < ε} ⟶
        liftedPuncturedPair.{w} E),
      {z : E | norm z < ε} ⊆ U ∧
      (∀ z, (g.map z).down = f z.val.down) ∧
      ∀ (R : Type u) [CommRing R]
        (B : P202Specs.TransverseThomProduct.SupportedClass R (TopCat.of (ULift.{w} E))),
        B.support = {z | z.down = 0} →
          supportedPullback R g.map B =
            supportedPullback R
              ((openPairInclusion (liftedPuncturedPair.{w} E) {z | norm z.down < ε}).map ≫
                (liftedLinearPairIso L).hom.map) B := by
  obtain ⟨ε,hε,g,hsmall,hg,hcoh⟩ :=
    exists_lifted_slice_cohomology_comparison.{u,w} L hU h0U hfc hf0 hf
  let linear := openPairInclusion (liftedPuncturedPair.{w} E) {z | norm z.down < ε} ≫
    (liftedLinearPairIso L).hom
  refine ⟨ε,hε,g,hsmall,hg,?_⟩
  intro R _ B hB
  let X := (openPair (liftedPuncturedPair.{w} E) {z | norm z.down < ε}).space
  have hsG : g.map ⁻¹' B.support = {z : X | z.val.down = 0} := by
    ext z
    change g.map z ∈ B.support ↔ z.val.down = 0
    rw [hB]
    constructor
    · intro hz
      by_contra hzn
      exact g.mapsTo hzn hz
    · intro hz
      change (g.map z).down = 0
      rw [hg, hz, hf0]
  have hsL : linear.map ⁻¹' B.support = {z : X | z.val.down = 0} := by
    ext z
    change linear.map z ∈ B.support ↔ z.val.down = 0
    rw [hB]
    change L z.val.down = 0 ↔ z.val.down = 0
    exact L.map_eq_zero_iff
  have hs : g.map ⁻¹' B.support = linear.map ⁻¹' B.support := hsG.trans hsL.symm
  let C : Pair.{w} := ⟨X, (g.map ⁻¹' B.support)ᶜ⟩
  let J : C ⟶ openPair (liftedPuncturedPair.{w} E) {z | norm z.down < ε} := {
    map := 𝟙 X
    mapsTo := by
      intro z hz
      change z.val.down ≠ 0
      intro hz0
      exact hz (hsG.symm ▸ hz0) }
  let I : liftedPuncturedPair.{w} E ⟶ (⟨TopCat.of (ULift.{w} E), B.supportᶜ⟩ : Pair.{w}) := {
    map := 𝟙 _
    mapsTo := by
      intro z hz
      change z ∉ B.support
      rw [hB]
      exact hz }
  let G : C ⟶ (⟨TopCat.of (ULift.{w} E), B.supportᶜ⟩ : Pair.{w}) := J ≫ linear ≫ I
  apply supportedPullbacks_eq_of_formula R g.map linear.map B B hs rfl G rfl
  change P202Specs.RelativeCupProduct.relativePullback R _ B.degree B.value =
    P202Specs.RelativeCupProduct.relativePullback R G B.degree B.value
  have hF : (⟨g.map, fun _ hz => hz⟩ : C ⟶
      (⟨TopCat.of (ULift.{w} E), B.supportᶜ⟩ : Pair.{w})) = J ≫ g ≫ I :=
    PairMap.ext _ _ rfl
  rw [hF]
  change ((relativeCohomologyFunctor R R (B.degree : ℤ)).map (J ≫ g ≫ I).op) B.value =
    ((relativeCohomologyFunctor R R (B.degree : ℤ)).map (J ≫ linear ≫ I).op) B.value
  have heq := (hcoh R (B.degree : ℤ)).1
  simpa only [linear, op_comp, Functor.map_comp, ModuleCat.comp_apply] using
    congrArg (fun k => (relativeCohomologyFunctor R R (B.degree : ℤ)).map J.op
      (k ((relativeCohomologyFunctor R R (B.degree : ℤ)).map I.op B.value))) heq

end LiftedSliceComparison


section BlockOrientationGenerators
open P202Specs.TransverseThomProduct P202Specs.RelativeCupProduct
  P202Specs.RelativeSingularChains P202Specs.CohomologyPairs P202Specs.ThomClass
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
variable (R : Type u) [CommRing R]
attribute [local instance] normalTopology
/-- A homogeneous class supported on one actual coordinate hyperplane. -/
def rawGradedBlockFactor (k : ℕ) (D E : Fin (k+1) → ℕ)
    (a : ∀ j, HR R (modelPair.{w} (D j)) (E j)) (j : Fin (k+1)) :
    SupportedClass R (TopCat.of (ULift.{w} (∀ j, Euclidean (D j)))) where
  support := {z | z.down j = 0}
  closed := isClosed_eq ((continuous_apply j).comp continuous_uliftDown) continuous_const
  degree := E j
  value := relativePullback R
    (⟨TopCat.ofHom ⟨fun z => ULift.up (z.down j),
      continuous_uliftUp.comp ((continuous_apply j).comp continuous_uliftDown)⟩,
      fun _ hz => hz⟩ :
        (⟨TopCat.of (ULift.{w} (∀ j, Euclidean (D j))), {z | z.down j ≠ 0}⟩ : Pair) ⟶
          modelPair.{w} (D j)) (E j) (a j)

/-- The raw block generator theorem allows the original declared degree,
using its verified equality with the actual normal rank. -/
theorem rawModelBlocks_generates (μ : NaturalRelativeCupProduct.{u,w} R)
    (k : ℕ) (D E : Fin (k+1) → ℕ) (hDE : E = D)
    (a : ∀ j, HR R (modelPair.{w} (D j)) (E j))
    (ha : ∀ j, Function.Surjective (fun r : R => r • a j)) :
    Function.Bijective (fun r : R => r •
      (orderedCup R μ k (rawGradedBlockFactor R k D E a)).value) := by
  subst E
  let G : Fin (k+1) → ModelClass.{u,w} R := fun j => ⟨D j,a j⟩
  have hfactor : rawGradedBlockFactor R k D D a =
      (fun j => supportedPullback R (rawModelBlockProjection R k G j) (modelSupported R (G j))) := by
    funext j
    rfl
  rw [hfactor]
  rw [orderedCup_rawModelBlocks]
  have hg := orderedModelCup_generates R μ k G ha
  have he := supportedPullback_homeomorph_generates R
    (X := TopCat.of (ULift.{w} (∀ j, Euclidean (G j).degree)))
    (Y := (modelPair.{w} (orderedModelCup R μ k G).degree).space)
    (modelBlocksHomeomorph R μ k G)
    (modelSupported R (orderedModelCup R μ k G)) hg
  exact he

variable {n k : ℕ} {M : TopCat.{w}} {S : SmoothManifold n .euclidean M}

theorem modelOrientationAt_generates (F : Fin k → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b : ModelOrientationAt R F p) (j : Fin k) :
    Function.Bijective (fun r : R => r • b.value j) := by
  let E := ((relativeCohomologyFunctor R R ((F j).codimension : ℤ)).mapIso
    (P202.ThomClass.fiberCoordinatesIso (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).op).toLinearEquiv
  have he : E (b.value j) = (F j).orientation.generator (p j) := b.prescribed j
  constructor
  · intro r s hrs
    apply ((F j).orientation.generates (p j)).injective
    have hh := congrArg E hrs
    simpa only [E.map_smul, he] using hh
  · intro x
    obtain ⟨r, hr⟩ := ((F j).orientation.generates (p j)).surjective (E x)
    refine ⟨r, E.injective ?_⟩
    simpa only [E.map_smul, he] using hr

theorem blockSupportedFactor_generates (μ : NaturalRelativeCupProduct.{u,w} R)
    (F : Fin (k+1) → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b : ModelOrientationAt R F p) :
    Function.Bijective (fun r : R => r • (orderedCup R μ k (blockSupportedFactor R F p b)).value) := by
  have hDE : (fun j => (F j).codimension) = (fun j => n - (F j).dimension) := by
    funext j
    exact (F j).rank (p j)
  exact rawModelBlocks_generates R μ k (fun j => n - (F j).dimension)
    (fun j => (F j).codimension) hDE b.value
    (fun j => (modelOrientationAt_generates R F p b j).surjective)

theorem blockSupportedFactor_support (μ : NaturalRelativeCupProduct.{u,w} R)
    (F : Fin (k+1) → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b : ModelOrientationAt R F p) :
    (orderedCup R μ k (blockSupportedFactor R F p b)).support = zeroBlockSupport R F := by
  rw [orderedCup_support]
  ext z
  simp only [Set.mem_iInter, blockSupportedFactor, Set.mem_setOf_eq, zeroBlockSupport]
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

theorem blockSupportedFactor_degree (μ : NaturalRelativeCupProduct.{u,w} R)
    (F : Fin (k+1) → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b : ModelOrientationAt R F p) :
    (orderedCup R μ k (blockSupportedFactor R F p b)).degree = totalCodimension R F := by
  exact orderedCup_degree R μ k (blockSupportedFactor R F p b)


end BlockOrientationGenerators


section FullTransverseAssembly
set_option maxHeartbeats 800000
open P202Specs.LocalThomProjection P202.ThomClass
lemma castDegree_pullback_natural {P Q : Pair.{w}} (f : P ⟶ Q)
    {d e : ℕ} (h : d = e) (v : HR R Q d) :
    relativePullback R f e (castRelativeDegree R h v) =
      castRelativeDegree R h (relativePullback R f d v) := by
  cases h
  rfl

/-- Exact relative cup equality may be checked after any excisive source
restriction, directly on actual relative cohomology, with all degrees retained. -/
lemma relativeEquality_of_excisive_supportedEquality
    {X Y : TopCat.{w}} (P Q : Pair.{w}) (j : Q ⟶ P)
    (a : SupportedClass R X) (b : SupportedClass R Y)
    (f : P ⟶ (⟨X,a.supportᶜ⟩ : Pair)) (g : P ⟶ (⟨Y,b.supportᶜ⟩ : Pair))
    (d : ℕ) (had : a.degree = d) (hbd : b.degree = d)
    (hj : IsIso ((relativeCohomologyFunctor R R (d : ℤ)).map j.op))
    (H : supportedPullback R (j ≫ f).map a = supportedPullback R (j ≫ g).map b) :
    castRelativeDegree R had (relativePullback R f a.degree a.value) =
      castRelativeDegree R hbd (relativePullback R g b.degree b.value) := by
  haveI := hj
  apply (ConcreteCategory.bijective_of_isIso
    ((relativeCohomologyFunctor R R (d : ℤ)).map j.op)).injective
  change relativePullback R j d
      (castRelativeDegree R had (relativePullback R f a.degree a.value)) =
    relativePullback R j d
      (castRelativeDegree R hbd (relativePullback R g b.degree b.value))
  rw [castDegree_pullback_natural, castDegree_pullback_natural,
    relativePullback_comp', relativePullback_comp']
  exact relativePullbacks_eq_of_supportedPullbacks_eq R Q a b (j ≫ f) (j ≫ g) H d had hbd


namespace LiftedSliceComparison
/-- Literal inclusion of a lifted coordinate ball into an arbitrary slice domain. -/
def liftedBallToDomain {E : Type} [NormedAddCommGroup E]
    (U : Set E) (ε : ℝ) (hsmall : {z : E | norm z < ε} ⊆ U) :
    openPair (liftedPuncturedPair.{w} E) {z | norm z.down < ε} ⟶
      openPair (liftedPuncturedPair.{w} E) {z | z.down ∈ U} where
  map := TopCat.ofHom ⟨fun z => ⟨z.val, hsmall z.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  mapsTo := fun _ hz => hz

/-- Excision on a lifted punctured-vector pair. -/
theorem liftedDomainInclusion_isIso
    {E : Type} [NormedAddCommGroup E] (U : Set E) (hU : IsOpen U) (h0U : 0 ∈ U)
    (R : Type u) [CommRing R] (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map
      (openPairInclusion (liftedPuncturedPair.{w} E) {z | z.down ∈ U}).op) := by
  apply openPairInclusion_isIso
  · exact isOpen_ne_fun continuous_uliftDown continuous_const
  · exact hU.preimage continuous_uliftDown
  · intro z hz
    change ¬ z.down ≠ 0 at hz
    change z.down ∈ U
    rw [Classical.not_not.mp hz]
    exact h0U

/-- Restriction from an arbitrary normal-slice domain to any centered coordinate
ball inside it is an isomorphism, through its exact literal inclusion. -/
theorem liftedBallToDomain_isIso
    {E : Type} [NormedAddCommGroup E] (U : Set E) (hU : IsOpen U) (h0U : 0 ∈ U)
    (ε : ℝ) (hε : 0 < ε) (hsmall : {z : E | norm z < ε} ⊆ U)
    (R : Type u) [CommRing R] (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map
      (liftedBallToDomain.{w} U ε hsmall).op) := by
  let H := relativeCohomologyFunctor R R q
  let iU := openPairInclusion (liftedPuncturedPair.{w} E) {z | z.down ∈ U}
  let iB := openPairInclusion (liftedPuncturedPair.{w} E) {z | norm z.down < ε}
  let j := liftedBallToDomain.{w} U ε hsmall
  have hji : j ≫ iU = iB := PairMap.ext _ _ rfl
  haveI : IsIso (H.map iU.op) := liftedDomainInclusion_isIso U hU h0U R q
  haveI : IsIso (H.map iB.op) :=
    liftedDomainInclusion_isIso {z : E | norm z < ε}
      (isOpen_lt continuous_norm continuous_const) (by simpa using hε) R q
  haveI : IsIso (H.map iU.op ≫ H.map j.op) := by
    rw [← H.map_comp, ← op_comp, hji]
    infer_instance
  exact IsIso.of_isIso_comp_left (H.map iU.op) (H.map j.op)

end LiftedSliceComparison

variable {n k : ℕ} {M : TopCat.{w}} {S : SmoothManifold n .euclidean M}
attribute [local instance] normalTopology

theorem thomProduct_on_normalizedSlice
    (μ : NaturalRelativeCupProduct.{u,w} R)
    (F : Fin (k+1) → OrientedSubmanifold R M S)
    (c : ∀ j, HR R (⟨M,((F j).support)ᶜ⟩ : Pair) (F j).codimension)
    (hc : ∀ j, HasFiberValues R (F j).orientation (c j))
    (hclosed : ∀ j, IsClosed (F j).support)
    (x : M) (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x)
    (b : ModelOrientationAt R F p) (s : NormalizedIntersectionSlice R F x p h b) :
    let A := orderedCup R μ k (fun j =>
      (⟨(F j).support, hclosed j, (F j).codimension, c j⟩ : SupportedClass R M))
    let B := orderedCup R μ k (blockSupportedFactor R F p b)
    ∀ (hA : A.support = intersectionSupport R F)
      (hAd : A.degree = totalCodimension R F)
      (hB : B.support = zeroBlockSupport R F)
      (hBd : B.degree = totalCodimension R F),
      castRelativeDegree R hAd (relativePullback R (s.toAmbient A hA) A.degree A.value) =
        castRelativeDegree R hBd (relativePullback R (s.toBlocks B hB) B.degree B.value) := by
  classical
  intro A B hA hAd hB hBd
  choose K hK a U hUo hpU hU g hg hgen hVo hVx hz hf using
    (fun j => localFactorProjection R n M S (F j) (c j) (hc j) (p j))
  let b0 : ModelOrientationAt R F p := {
    chartPoint := a
    base_mem := fun j => hU j (hpU j)
    value := g
    prescribed := fun j => hg j (p j) (hpU j) }
  let V : Set M := ⋂ j, imageRegion (F j).normal (K j) (U j)
  have hV : IsOpen V := isOpen_iInter_of_finite hVo
  have hxV : x ∈ V := Set.mem_iInter.mpr (fun j => h j ▸ hVx j)
  let fj (j : Fin (k+1)) : restrictionPair M (F j).support V ⟶
      ambientRegionPair (F j).normal (K j) (U j) := {
    map := TopCat.ofHom ⟨fun y => ⟨y.val, Set.mem_iInter.mp y.property j⟩,
      continuous_subtype_val.subtype_mk _⟩
    mapsTo := fun _ hy => hy }
  let L : LocalThomModels R F c x := {
    neighborhood := V
    isOpen_neighborhood := hV
    mem_neighborhood := hxV
    generator := g
    generates := hgen
    projection := fun j => fj j ≫ ambientCoordinates (F j).normal (K j) (a j) (U j) (hU j)
    zero_equations := fun j y => hz j ((fj j).map y)
    class_formula := fun j => by
      have hj := hf j _ (fj j)
      have heq : fj j ≫ ambientRegionInclusion (F j).normal (K j) (U j) =
          restrictionInclusion M (F j).support V := PairMap.ext _ _ rfl
      rw [heq] at hj
      exact hj }
  let B0 := orderedCup R μ k (blockSupportedFactor R F p b0)
  have hB0 : B0.support = {z | z.down = 0} := by
    rw [orderedCup_support]
    ext z
    simp only [Set.mem_iInter, blockSupportedFactor, Set.mem_setOf_eq]
    exact ⟨fun h => funext h, fun h j => congrFun h j⟩
  have hn : ∀ v j, P202Specs.TransverseNormalCoordinates.normalProjection
      ((F j).embeddedData R) (p j) x (h j)
      (s.tangentCoordinates.symm (s.derivative v)) =
      (fiberLinearCoordinates (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).symm (v j) := by
    intro v j
    rw [embeddedData_projection]
    exact s.normal_derivative v j
  obtain ⟨Q, f, hQ, h0Q, hQdom, hfsmooth, hf0, hdf, hsource, hfeq⟩ :=
    ProjectionGeometry.projections_on_normal_slice
      (fun j => (F j).embeddedData R) x p h b.chartPoint b.base_mem
      s.domain s.domain_open s.domain_zero s.slice s.center
      s.chart s.chart_mem s.in_chart s.smooth s.continuous
      s.tangentCoordinates s.tangent_isCoordinates s.derivative s.has_derivative hn
      K hK a U hUo hpU hU
  let T := orientationBlockTransition R F p b b0
  have hT : ProjectionGeometry.normalCoordinateChange
      (fun j => (F j).embeddedData R) p a b.chartPoint
      (fun j => hU j (hpU j)) b.base_mem = T := by
    ext v j
    rfl
  rw [hT] at hdf
  obtain ⟨ε,hε,gBall,hsmall,hgBall,hcoh⟩ :=
    LiftedSliceComparison.exists_lifted_supported_comparison.{u,w}
      T hQ h0Q hfsmooth.continuousOn hf0 hdf
  let PBall := openPair (LiftedSliceComparison.liftedPuncturedPair.{w} (normalBlocks R F))
    {z | norm z.down < ε}
  have hsmallDom : {z : normalBlocks R F | norm z < ε} ⊆ s.domain :=
    fun z hz => hQdom (hsmall hz)
  let J : PBall ⟶ s.pair := LiftedSliceComparison.liftedBallToDomain s.domain ε hsmallDom
  let sLocal : PBall.space ⟶ TopCat.of L.neighborhood :=
    TopCat.ofHom ⟨fun z => ⟨s.slice z.val.down, Set.mem_iInter.mpr (hsource _ (hsmall z.property))⟩,
      (s.continuous.comp_continuous
        (continuous_uliftDown.comp continuous_subtype_val)
        (fun z => hsmallDom z.property)).subtype_mk _⟩
  have hlocal := localModel_orderedCup_comparison R μ F c hclosed x L
  have hlocalBall := congrArg (supportedPullback R sLocal) hlocal
  rw [supportedPullback_comp, supportedPullback_comp] at hlocalBall
  have hAmbient : sLocal ≫
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of L.neighborhood ⟶ M) =
      (J ≫ s.toAmbient A hA).map := TopCat.hom_ext (ContinuousMap.ext (fun _ => rfl))
  have hCombined : sLocal ≫ localModelCombinedMap R F c x L = gBall.map := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply ULift.ext
    change (fun j => ((L.projection j).map (sLocal z)).down) = (gBall.map z).down
    rw [hgBall]
    funext j
    exact (hfeq z.val.down (hsmall z.property) j).symm
  rw [hAmbient,hCombined] at hlocalBall
  have hSmall : supportedPullback R (J ≫ s.toAmbient A hA).map A =
      supportedPullback R (J ≫ s.toBlocks B hB).map B := by
    change supportedPullback R (J ≫ s.toAmbient A hA).map A =
      supportedPullback R
        (openPairInclusion (LiftedSliceComparison.liftedPuncturedPair.{w} (normalBlocks R F))
          {z | norm z.down < ε}).map B
    calc
      _ = supportedPullback R gBall.map B0 := hlocalBall
      _ = supportedPullback R
          ((openPairInclusion (LiftedSliceComparison.liftedPuncturedPair.{w} (normalBlocks R F))
            {z | norm z.down < ε}).map ≫
            (LiftedSliceComparison.liftedLinearPairIso T).hom.map) B0 := hcoh R B0 hB0
      _ = _ := by
        have hlin : (LiftedSliceComparison.liftedLinearPairIso T).hom.map =
            orientationBlockTransitionMap R F p b b0 := rfl
        rw [hlin, ← supportedPullback_comp, orderedBlockOrientation_covariance]
  apply relativeEquality_of_excisive_supportedEquality R s.pair PBall J A B
    (s.toAmbient A hA) (s.toBlocks B hB) (totalCodimension R F) hAd hBd
    (LiftedSliceComparison.liftedBallToDomain_isIso s.domain s.domain_open s.domain_zero
      ε hε hsmallDom R (totalCodimension R F : ℤ)) hSmall


/-- The prescribed ordered relative Thom product gives the product orientation
on every normalized normal slice, over every commutative coefficient ring. -/
theorem nonemptyTransverseProduct :
    P202Specs.TransverseThomProduct.nonemptyTransverseProduct_type.{u,w} := by
  intro R _ n k M S F hF
  obtain ⟨c,hclosed,hc,hproducts⟩ := orderedThomClasses R n k M S F
  refine ⟨c,hclosed,hc,?_⟩
  intro μ
  dsimp only
  obtain ⟨hA,hAd,_⟩ := hproducts μ
  refine ⟨hA,hAd,?_⟩
  intro x p h
  refine ⟨modelOrientationAt_exists R F p,?_⟩
  intro b
  refine ⟨normalizedIntersectionSlice_exists R F hF x p h b,?_⟩
  have hB := blockSupportedFactor_support R μ F p b
  have hBd := blockSupportedFactor_degree R μ F p b
  refine ⟨hB,hBd,blockSupportedFactor_generates R μ F p b,?_⟩
  intro s
  exact thomProduct_on_normalizedSlice R μ F c hc hclosed x p h b s hA hAd hB hBd

/-- All finite endpoints: nonempty transverse families and the actual nullary
relative unit. The empty-intersection and singleton endpoints are proved above. -/
theorem fullTransverseProduct :
    P202Specs.TransverseThomProduct.fullTransverseProduct_type.{u,w} :=
  ⟨nonemptyTransverseProduct, nullaryUnit⟩

end FullTransverseAssembly

end GeometricAssemblyAuxiliaries

end P202.TransverseThomProduct
