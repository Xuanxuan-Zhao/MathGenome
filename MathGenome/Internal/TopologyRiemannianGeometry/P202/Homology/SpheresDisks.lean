import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SpheresDisks
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.MayerVietoris
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Homology.Additive
import Mathlib.Topology.Order.Lattice
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Spheres

/-! Sphere, disk and oriented simplex computations for arbitrary module
coefficients. The sphere calculation uses the two-pole Mayer–Vietoris cover.
A face-adapted cover proves primitivity of the actual oriented affine simplex.
Integral chain homotopy equivalences transfer both computations to all modules. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

universe u v w
namespace P202.SpheresDisks
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks

/-- Full point and contractible-space assertion, in every integer degree. -/
theorem contractible : contractible_type.{u,v,w} := by
  intro R _ M _ _
  exact ⟨P202.SingularDegreeZero.pointReduced R M, P202.PrismHomotopy.contractible R M⟩

/-- The signs already give the final endpoint minus the initial endpoint. -/
theorem endpointDifference : endpointDifference_type.{u,v} := by
  intro R _ M _ _ m
  simp [orientedBoundary, Fin.sum_univ_two, sub_eq_add_neg]

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Every Euclidean disk is contractible, including the zero-dimensional disk. -/
lemma disk_contractible (n : ℕ) : ContractibleSpace (disk n) := by
  exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).contractibleSpace
    ⟨0, by simp⟩

/-- No coefficient restriction is needed for the disk's reduced homology. -/
lemma disk_reduced (n : ℕ) (j : ℤ) : IsZero (reducedHomology R M (disk n) j) := by
  have := disk_contractible n
  exact P202.PrismHomotopy.contractible R M (disk n) j

/-- Straight-line contraction in barycentric coordinates. -/
lemma simplex_contractible (n : ℕ) : ContractibleSpace (simplex n) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨Convexity.StdSimplex.single 0, ⟨{
    toFun := fun tx => Convexity.convexCombPair (R := ℝ)
      (unitInterval.symm tx.1) tx.1 (unitInterval.nonneg _) (unitInterval.nonneg _)
      (by simp) tx.2 (Convexity.StdSimplex.single 0)
    continuous_toFun := ?_
    map_zero_left := by intro x; simp
    map_one_left := by intro x; simp }⟩⟩
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff]
  unfold Function.comp
  apply continuous_pi
  intro i
  simp only [unitInterval.coe_symm_eq, Convexity.StdSimplex.weights_convexCombPair,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- Mapping the ordered boundary faces into the simplex gives the actual
singular boundary, with all signs fixed by the vertex order. -/
lemma inclusion_orientedBoundary (n : ℕ) (m : M) :
    ((chainMap R M (simplexPair (n+1)).inclusion).f n) (orientedBoundary M n m) =
      boundary R M (simplex (n+1)) n (affineChain M (n+1) m) := by
  rw [affineChain, P202.SingularChains.boundary_single]
  simp only [orientedBoundary, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [P202.SingularChains.chainMap_single]
  congr 1
/-- Integer indexing preserves the affine signed boundary identity. -/
lemma inclusion_orientedBoundaryZ (n : ℕ) (m : M) :
    (inclusion (ordinaryFunctor R M) (simplexPair (n+1))).f (n : ℤ)
        (orientedBoundaryZ R M n m) =
      (ordinaryComplex R M (simplex (n+1))).d ((n+1 : ℕ) : ℤ) (n : ℤ)
        (affineChainZ R M (n+1) m) := by
  apply (ordinaryNonnegativeIso R M (simplex (n+1)) n).toLinearEquiv.injective
  have h₁ := congrArg
    (fun f => (ordinaryNonnegativeIso R M (simplexPair (n+1)).sub n).inv ≫ f)
    (ordinary_inclusion_degree R M (simplexPair (n+1)) n)
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h₁
  have h₂ := congrArg (fun f => f (affineChain M (n+1) m))
    (P202.SingularChains.ordinary_boundary R M (simplex (n+1)) n)
  have h₁' : (ordinaryNonnegativeIso R M (simplex (n+1)) n).hom
      ((inclusion (ordinaryFunctor R M) (simplexPair (n+1))).f (n : ℤ)
        (orientedBoundaryZ R M n m)) =
      ((chainMap R M (simplexPair (n+1)).inclusion).f n) (orientedBoundary M n m) := by
    exact congrArg (fun f => f (orientedBoundary M n m)) h₁
  exact h₁'.trans ((inclusion_orientedBoundary R M n m).trans h₂.symm)

/-- The signed boundary is a cycle in the boundary subspace. -/
lemma orientedBoundaryZ_cycle (n : ℕ) (m : M) :
    (ordinaryComplex R M (simplexPair (n+1)).sub).d (n : ℤ) ((n : ℤ)-1)
      (orientedBoundaryZ R M n m) = 0 := by
  let f := inclusion (ordinaryFunctor R M) (simplexPair (n+1))
  apply (ModuleCat.mono_iff_injective (f.f ((n : ℤ)-1))).mp inferInstance
  rw [map_zero]
  have hc := congrArg (fun g => g (orientedBoundaryZ R M n m))
    (f.comm (n : ℤ) ((n : ℤ)-1))
  change (f.f ((n : ℤ)-1))
    ((ordinaryComplex R M (simplexPair (n+1)).sub).d (n : ℤ) ((n : ℤ)-1)
      (orientedBoundaryZ R M n m)) = 0
  change (ordinaryComplex R M (simplex (n+1))).d (n : ℤ) ((n : ℤ)-1)
      (f.f (n : ℤ) (orientedBoundaryZ R M n m)) =
    f.f ((n : ℤ)-1)
      ((ordinaryComplex R M (simplexPair (n+1)).sub).d (n : ℤ) ((n : ℤ)-1)
        (orientedBoundaryZ R M n m)) at hc
  apply hc.symm.trans
  change (ordinaryComplex R M (simplex (n+1))).d (n : ℤ) ((n : ℤ)-1)
    ((inclusion (ordinaryFunctor R M) (simplexPair (n+1))).f (n : ℤ)
      (orientedBoundaryZ R M n m)) = 0
  rw [inclusion_orientedBoundaryZ]
  exact congrArg (fun g => g (affineChainZ R M (n+1) m))
    ((ordinaryComplex R M (simplex (n+1))).d_comp_d ((n+1 : ℕ) : ℤ) (n : ℤ) ((n : ℤ)-1))

/-- Every coefficient multiple of the affine simplex is a relative cycle. -/
lemma relativeAffineChain_cycle_succ (n : ℕ) (m : M) :
    (ordinary R M (simplexPair (n+1))).d ((n+1 : ℕ) : ℤ) (n : ℤ)
      (relativeAffineChain R M (n+1) m) = 0 := by
  let p := projection (ordinaryFunctor R M) (simplexPair (n+1))
  have hc := congrArg (fun g => g (affineChainZ R M (n+1) m))
    (p.comm ((n+1 : ℕ) : ℤ) (n : ℤ))
  change (ordinary R M (simplexPair (n+1))).d ((n+1 : ℕ) : ℤ) (n : ℤ)
      (p.f ((n+1 : ℕ) : ℤ) (affineChainZ R M (n+1) m)) = 0
  change (ordinary R M (simplexPair (n+1))).d ((n+1 : ℕ) : ℤ) (n : ℤ)
      (p.f ((n+1 : ℕ) : ℤ) (affineChainZ R M (n+1) m)) =
    p.f (n : ℤ) ((ordinaryComplex R M (simplex (n+1))).d ((n+1 : ℕ) : ℤ) (n : ℤ)
      (affineChainZ R M (n+1) m)) at hc
  apply hc.trans
  rw [← inclusion_orientedBoundaryZ]
  exact congrArg (fun g => g (orientedBoundaryZ R M n m))
    (congrArg (fun g => g.f (n : ℤ)) (cokernel.condition
      (inclusion (ordinaryFunctor R M) (simplexPair (n+1)))))

/-- Every affine simplex is a relative cycle, including a vertex. -/
lemma relativeAffineChain_cycle (n : ℕ) (m : M) :
    (ordinary R M (simplexPair n)).d (n : ℤ) ((n : ℤ)-1)
      (relativeAffineChain R M n m) = 0 := by
  cases n with
  | zero =>
    have h := congrArg (fun g => g (affineChainZ R M 0 m))
      ((projection (ordinaryFunctor R M) (simplexPair 0)).comm 0 (-1))
    change (ordinary R M (simplexPair 0)).d 0 (-1)
        (relativeAffineChain R M 0 m) =
      (projection (ordinaryFunctor R M) (simplexPair 0)).f (-1)
        ((ordinaryComplex R M (simplex 0)).d 0 (-1) (affineChainZ R M 0 m)) at h
    exact h.trans (by rw [P202.SingularChains.ordinary_boundary_zero]; exact map_zero _)
  | succ n =>
    have h : ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) := by omega
    rw [h]
    exact relativeAffineChain_cycle_succ R M n m

/-- The coefficient map to the actual relative chains. -/
def relativeAffineLinear (n : ℕ) : M →ₗ[R]
    (ordinary R M (simplexPair n)).X (n : ℤ) :=
  ((projection (ordinaryFunctor R M) (simplexPair n)).f (n : ℤ)).hom.comp
    ((ordinaryNonnegativeIso R M (simplex n) n).inv.hom.comp
      (Finsupp.lsingle (affineSimplex n)))

/-- Lift the affine coefficient map to categorical cycles. -/
def affineCycleMap (n : ℕ) : ModuleCat.of R M ⟶
    (ordinary R M (simplexPair n)).cycles (n : ℤ) :=
  (ordinary R M (simplexPair n)).liftCycles
    (ModuleCat.ofHom (relativeAffineLinear R M n)) ((n : ℤ)-1)
    ((ComplexShape.down ℤ).next_eq' (by simp)) (by
      apply ModuleCat.hom_ext
      ext m
      exact relativeAffineChain_cycle R M n m)

/-- The specified affine cycle determines a linear coefficient-to-homology
map. Its bijectivity expresses the normalization in the relative generator theorem. -/
def affineClassLinear (n : ℕ) : M →ₗ[R]
    relativeHomology R M (simplexPair n) (n : ℤ) :=
  (affineCycleMap R M n ≫ (ordinary R M (simplexPair n)).homologyπ (n : ℤ)).hom

lemma affineClassLinear_apply (n : ℕ) (m : M) :
    affineClassLinear R M n m =
      classOf R (ordinary R M (simplexPair n)) (n : ℤ)
        (relativeAffineChain R M n m) (relativeAffineChain_cycle R M n m) := by
  change (ordinary R M (simplexPair n)).homologyπ (n : ℤ) (affineCycleMap R M n m) = _
  unfold classOf P202Specs.ChainLES.cycleClass
  apply congrArg ((ordinary R M (simplexPair n)).homologyπ (n : ℤ))
  apply (ModuleCat.mono_iff_injective
    ((ordinary R M (simplexPair n)).iCycles (n : ℤ))).mp inferInstance
  change (affineCycleMap R M n ≫
    (ordinary R M (simplexPair n)).iCycles (n : ℤ)) m = _
  simp only [affineCycleMap, HomologicalComplex.liftCycles_i]
  change relativeAffineChain R M n m =
    ((forget₂ (ModuleCat R) Ab).map
      ((ordinary R M (simplexPair n)).iCycles (n : ℤ))) _
  symm
  apply HomologicalComplex.i_cyclesMk

lemma simplexGenerator_of_affineClass_bijective
    (h : ∀ (R : Type u) [CommRing R] (M : Type v)
      [AddCommGroup M] [Module R M] (n : ℕ),
      Function.Bijective (affineClassLinear R M n)) :
    simplexGenerator_type.{u,v} := by
  intro R _ M _ _ n
  refine ⟨relativeAffineChain_cycle R M n,
    (LinearEquiv.ofBijective (affineClassLinear R M n) (h R M n)).symm, ?_⟩
  intro m
  rw [← affineClassLinear_apply]
  exact (LinearEquiv.ofBijective (affineClassLinear R M n) (h R M n)).symm_apply_apply m

lemma simplex_zero_boundary_empty : IsEmpty (simplexPair 0).sub := by
  refine ⟨?_⟩
  rintro ⟨x, i, hi⟩
  let : Subsingleton (Fin (0+1)) := inferInstanceAs (Subsingleton (Fin 1))
  have h : x.weights i = 1 := Convexity.StdSimplex.weights_apply_eq_one x i
  rw [h] at hi
  exact zero_ne_one hi.symm

instance simplex_zero_singular_subsingleton (k : ℕ) : Subsingleton (Simplex (simplex 0) k) :=
  (simplexEquiv (simplex 0) k).injective.subsingleton

lemma simplex_zero_ordinary_boundary :
    (ordinaryComplex R M (simplex 0)).d 1 0 = 0 := by
  apply (cancel_epi (ordinaryNonnegativeIso R M (simplex 0) 1).inv).mp
  apply (cancel_mono (ordinaryNonnegativeIso R M (simplex 0) 0).hom).mp
  simp only [zero_comp, comp_zero]
  change (ordinaryNonnegativeIso R M (simplex 0) 1).inv ≫
      (ordinaryComplex R M (simplex 0)).d 1 0 ≫
      (ordinaryNonnegativeIso R M (simplex 0) 0).hom = 0
  trans (complex R M (simplex 0)).d 1 0
  · simpa only [Nat.reduceAdd, Int.ofNat_zero, Int.ofNat_one] using
      P202.SingularChains.ordinary_boundary R M (simplex 0) 0
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s m
  change boundary R M (simplex 0) 0 (Finsupp.single s m) = 0
  rw [P202.SingularChains.boundary_single]
  simp [Fin.sum_univ_two, Subsingleton.elim (face 0 s) (face 1 s)]

lemma simplex_zero_projection_iso (k : ℤ) :
    IsIso ((projection (ordinaryFunctor R M) (simplexPair 0)).f k) := by
  have : IsEmpty (simplexPair 0).sub := simplex_zero_boundary_empty
  exact ((P202.RelativeSingularChains.ordinary_short_exact R M (simplexPair 0)) k).isIso_g_iff.mpr
    (P202.SingularDegreeZero.emptyOrdinaryX R M (simplexPair 0).sub k)

lemma simplex_zero_relative_boundary : (ordinary R M (simplexPair 0)).d 1 0 = 0 := by
  have : IsIso ((projection (ordinaryFunctor R M) (simplexPair 0)).f 1) :=
    simplex_zero_projection_iso R M 1
  apply (cancel_epi ((projection (ordinaryFunctor R M) (simplexPair 0)).f 1)).mp
  rw [HomologicalComplex.Hom.comm]
  change (ordinaryComplex R M (simplex 0)).d 1 0 ≫ _ = _
  rw [simplex_zero_ordinary_boundary]
  simp

lemma affineClassLinear_zero_bijective : Function.Bijective (affineClassLinear R M 0) := by
  let K := ordinary R M (simplexPair 0)
  have h₀ : K.d 0 (-1) = 0 :=
    (P202.RelativeSingularChains.ordinary_negative R M (simplexPair 0) (-1) (by omega)).1.eq_of_tgt _ _
  have : IsIso (K.iCycles 0) := K.isIso_iCycles 0 (-1) (by simp) h₀
  have : IsIso (K.homologyπ 0) := K.isIso_homologyπ 1 0 (by simp)
    (simplex_zero_relative_boundary R M)
  have : IsIso ((projection (ordinaryFunctor R M) (simplexPair 0)).f 0) :=
    simplex_zero_projection_iso R M 0
  have hlinear : Function.Bijective (relativeAffineLinear R M 0) := by
    change Function.Bijective ((fun x =>
      (projection (ordinaryFunctor R M) (simplexPair 0)).f 0 x) ∘
      (fun x => (ordinaryNonnegativeIso R M (simplex 0) 0).inv x) ∘
      (fun m => Finsupp.single (affineSimplex 0) m))
    apply (asIso ((projection (ordinaryFunctor R M) (simplexPair 0)).f 0)).toLinearEquiv.bijective.comp
    apply (ordinaryNonnegativeIso R M (simplex 0) 0).symm.toLinearEquiv.bijective.comp
    exact (Finsupp.uniqueLinearEquiv R M (affineSimplex 0)).symm.bijective
  have hcycle : Function.Bijective (affineCycleMap R M 0) := by
    have hcomp : (K.iCycles 0) ∘ (affineCycleMap R M 0) = relativeAffineLinear R M 0 := by
      funext m
      change ((affineCycleMap R M 0) ≫ (ordinary R M (simplexPair 0)).iCycles 0) m = _
      have h := (ordinary R M (simplexPair 0)).liftCycles_i
        (ModuleCat.ofHom (relativeAffineLinear R M 0)) ((0 : ℤ)-1)
        ((ComplexShape.down ℤ).next_eq' (by simp))
        (by apply ModuleCat.hom_ext; ext m; exact relativeAffineChain_cycle R M 0 m)
      exact congrArg (fun f : ModuleCat.of R M ⟶ (ordinary R M (simplexPair 0)).X 0 => f m) h
    rw [← hcomp] at hlinear
    exact (Function.Bijective.of_comp_iff' (asIso (K.iCycles 0)).toLinearEquiv.bijective (affineCycleMap R M 0)).mp hlinear
  exact (asIso (K.homologyπ 0)).toLinearEquiv.bijective.comp hcycle


/-- Contracting the ambient space identifies relative homology with reduced
homology of the subspace one degree below. This also covers an empty subspace. -/
def contractiblePairIso (P : Pair.{w}) [Nonempty P.space]
    [ContractibleSpace P.space] (j : ℤ) :
    relativeHomology R M P j ≅ reducedHomology R M P.sub (j-1) := by
  let e := Classical.choice (P202.RelativeSingularChains.relative_versions_iso R M P)
  let h := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.reduced_short_exact R M P)
  exact (HomologicalComplex.homologyFunctor _ _ j).mapIso e.symm ≪≫
    h.δIso j (j-1) (by simp)
      (P202.PrismHomotopy.contractible R M P.space j)
      (P202.PrismHomotopy.contractible R M P.space (j-1))

/-- Boundary-of-a-lift, using the actual signed boundary in the subspace. -/
theorem simplexConnecting : simplexConnecting_type.{u,v} := by
  intro R _ M _ _ n
  let h := P202.RelativeSingularChains.ordinary_short_exact R M (simplexPair (n+1))
  refine ⟨h, fun m => ⟨relativeAffineChain_cycle_succ R M n m,
    orientedBoundaryZ_cycle R M n m, ?_⟩⟩
  exact P202.ChainLES.lift_formula _ h ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp)
    (relativeAffineChain R M (n+1) m) (relativeAffineChain_cycle_succ R M n m)
    (affineChainZ R M (n+1) m) rfl (orientedBoundaryZ R M n m)
    (inclusion_orientedBoundaryZ R M n m) (by
      change (ordinaryComplex R M (simplexPair (n+1)).sub).d (n : ℤ)
        ((ComplexShape.down ℤ).next (n : ℤ)) (orientedBoundaryZ R M n m) = 0
      rw [(ComplexShape.down ℤ).next_eq' (show (ComplexShape.down ℤ).Rel (n : ℤ) ((n : ℤ)-1) by simp)]
      exact orientedBoundaryZ_cycle R M n m)

/-- The boundary subtype of the closed disk is its unit sphere. -/
def diskBoundaryHomeomorph (n : ℕ) :
    (diskPair n).sub ≃ₜ P202.Cellular.Sphere n where
  toFun x := ⟨x.val.val, by simpa only [diskPair, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using x.property⟩
  invFun x := ⟨⟨x.val, Metric.sphere_subset_closedBall x.property⟩, by
    simpa only [diskPair, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- A concrete disk-to-sphere shift, valid in all integer degrees. -/
def diskHomologyShift (n : ℕ) (j : ℤ) :
    relativeHomology R M (diskPair (n+1)) j ≅ reducedHomology R M (sphere n) (j-1) := by
  have : Nonempty (diskPair (n+1)).space := ⟨⟨0, by simp⟩⟩
  have : ContractibleSpace (diskPair (n+1)).space := disk_contractible (n+1)
  exact contractiblePairIso R M (diskPair (n+1)) j ≪≫
    (reducedHomologyFunctor R M (j-1)).mapIso
      (TopCat.isoOfHomeo (diskBoundaryHomeomorph (n+1)))

lemma disk_zero_boundary_empty : IsEmpty (diskPair 0).sub := by
  refine ⟨fun x => ?_⟩
  have h : ‖x.val.val‖ = 1 := x.property
  have he : x.val.val = 0 := Subsingleton.elim _ _
  simp only [he, norm_zero, zero_ne_one] at h

/-- The zero-dimensional disk pair is handled without a negative-dimensional sphere. -/
lemma disk_zero (j : ℕ) :
    (j = 0 → Nonempty (relativeHomology R M (diskPair 0) (j : ℤ) ≃ₗ[R] M)) ∧
    (j ≠ 0 → IsZero (relativeHomology R M (diskPair 0) (j : ℤ))) := by
  have : Nonempty (diskPair 0).space := ⟨⟨0, by simp⟩⟩
  have : ContractibleSpace (diskPair 0).space := disk_contractible 0
  have := disk_zero_boundary_empty
  constructor
  · rintro rfl
    obtain ⟨e⟩ := P202.SingularDegreeZero.emptyReducedMinusOne R M (diskPair 0).sub
    exact ⟨(contractiblePairIso R M (diskPair 0) 0).toLinearEquiv.trans e⟩
  · intro hj
    exact (contractiblePairIso R M (diskPair 0) (j : ℤ)).isZero_iff.mpr
      (P202.SingularDegreeZero.emptyReducedOther R M (diskPair 0).sub ((j : ℤ)-1) (by omega))

/-- The Euclidean zero-sphere is the same two-point space as the shared base case. -/
def zeroSphereMap (b : P202Specs.SingularDegreeZero.zeroSphere.{0}) : sphere 0 :=
  ⟨EuclideanSpace.single 0 (if b.down = 0 then 1 else -1), by
    simp only [Metric.mem_sphere, dist_zero_right, EuclideanSpace.single, PiLp.norm_single]
    split <;> norm_num⟩

lemma zeroSphereMap_bijective : Function.Bijective zeroSphereMap := by
  constructor
  · intro ⟨b⟩ ⟨c⟩ h
    have h' := congrArg (fun x : sphere 0 => x.val 0) h
    fin_cases b <;> fin_cases c
    all_goals try rfl
    all_goals norm_num [zeroSphereMap, EuclideanSpace.single, PiLp.single_apply] at h'
  · intro x
    have hn : ‖x.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have hs : (x.val 0)^2 = 1 := by
      have := EuclideanSpace.real_norm_sq_eq x.val
      simpa [hn] using this.symm
    rcases sq_eq_one_iff.mp hs with h | h
    · refine ⟨⟨0⟩, ?_⟩
      apply Subtype.ext
      ext i
      have hi : i = 0 := by omega
      subst i
      simpa [zeroSphereMap, PiLp.single_apply] using h.symm
    · refine ⟨⟨1⟩, ?_⟩
      apply Subtype.ext
      ext i
      have hi : i = 0 := by omega
      subst i
      simpa [zeroSphereMap, PiLp.single_apply] using h.symm

/-- The equivalence is topological, so it induces the actual singular homology isomorphism. -/
def zeroSphereHomeomorph : P202Specs.SingularDegreeZero.zeroSphere.{0} ≃ₜ sphere 0 :=
  (continuous_of_discreteTopology : Continuous zeroSphereMap).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective zeroSphereMap zeroSphereMap_bijective)

lemma sphere_zero (j : ℕ) :
    (j = 0 → Nonempty (reducedHomology R M (sphere 0) (j : ℤ) ≃ₗ[R] M)) ∧
    (j ≠ 0 → IsZero (reducedHomology R M (sphere 0) (j : ℤ))) := by
  let e := (reducedHomologyFunctor R M (j : ℤ)).mapIso (TopCat.isoOfHomeo zeroSphereHomeomorph)
  constructor
  · rintro rfl
    obtain ⟨f⟩ := P202.SingularDegreeZero.sphereReducedZero R M
    exact ⟨e.symm.toLinearEquiv.trans f⟩
  · intro hj
    exact e.isZero_iff.mp (P202.SingularDegreeZero.sphereReducedOther R M (j : ℤ) (by omega))

/-- Once the sphere induction is supplied, the entire disk computation follows,
including degree zero and dimension zero. This is an intermediate reduction,
not an original-target conditional helper. -/
lemma diskHomology_of_sphereHomology (hs : sphereHomology_type.{u,v}) :
    diskHomology_type.{u,v} := by
  intro R _ M _ _ n j
  cases n with
  | zero => exact disk_zero R M j
  | succ n =>
    cases j with
    | zero =>
      have : Nonempty (sphere n) :=
        (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).to_subtype
      refine ⟨fun h => False.elim (by omega), fun _ => ?_⟩
      exact (diskHomologyShift R M n 0).isZero_iff.mpr
        (P202.SingularDegreeZero.nonemptyReducedMinusOne R M (sphere n))
    | succ j =>
      have hj : (((j+1 : ℕ) : ℤ)-1) = (j : ℤ) := by omega
      let e : relativeHomology R M (diskPair (n+1)) ((j+1 : ℕ) : ℤ) ≅
          reducedHomology R M (sphere n) (j : ℤ) :=
        diskHomologyShift R M n ((j+1 : ℕ) : ℤ) ≪≫ eqToIso (congrArg _ hj)
      constructor
      · intro h
        obtain ⟨f⟩ := (hs R M n j).1 (by omega)
        exact ⟨e.toLinearEquiv.trans f⟩
      · intro h
        exact e.isZero_iff.mpr ((hs R M n j).2 (by omega))

/-- The algebraic step in the hemisphere induction: when the two cover members
have zero homology in consecutive degrees, the Mayer–Vietoris arrow is an isomorphism. -/
lemma mvConnecting_isIso
    (F : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ)
    (δ : P202Specs.MayerVietoris.Connecting.{u,v,w} F)
    (he : P202Specs.MayerVietoris.Exact F δ)
    (C : P202Specs.MayerVietoris.CoverPair.{v,w}) (n : ℤ)
    (hleft : ∀ k ∈ ({n, n+1} : Set ℤ), IsZero ((F.obj C.leftPair).homology k))
    (hright : ∀ k ∈ ({n, n+1} : Set ℤ), IsZero ((F.obj C.rightPair).homology k)) :
    IsIso (δ C n) := by
  let e := he.1 C n
  have hm₁ : IsZero (P202Specs.MayerVietoris.homologyMiddle F C (n+1)) :=
    (biprod_isZero_iff _ _).mpr ⟨hleft _ (by simp), hright _ (by simp)⟩
  have hm₀ : IsZero (P202Specs.MayerVietoris.homologyMiddle F C n) :=
    (biprod_isZero_iff _ _).mpr ⟨hleft _ (by simp), hright _ (by simp)⟩
  have : Mono (δ C n) :=
    ((e.sc 1).exact_iff_mono (hm₁.eq_zero_of_src _)).mp (e.exact 1)
  have : Epi (δ C n) :=
    ((e.sc 2).exact_iff_epi (hm₀.eq_zero_of_tgt _)).mp (e.exact 2)
  exact isIso_of_mono_of_epi _

/-- The supplied full Mayer–Vietoris premise gives all the shifts for any
contractible two-member cover, simultaneously in all integer degrees.
This is stated for exactly the ring-coefficient functor of the frozen premise. -/
lemma reducedMV_shifts
    (mv : P202Specs.MayerVietoris.mayerVietoris_type.{u,v,w}) :
    ∃ δ : P202Specs.MayerVietoris.Connecting.{u,v,w}
        (P202Specs.MayerVietoris.theoryFunctor R .reduced),
      ∀ (C : P202Specs.MayerVietoris.CoverPair.{v,w})
        [Nonempty C.leftPair.space] [ContractibleSpace C.leftPair.space]
        [Nonempty C.rightPair.space] [ContractibleSpace C.rightPair.space] (n : ℤ),
        IsIso (δ C n) := by
  obtain ⟨⟨δ, he, _hn, _hb⟩, _⟩ := mv R .reduced
  refine ⟨δ, ?_⟩
  intro C _ _ _ _ n
  exact mvConnecting_isIso R _ δ he C n
    (fun k _ => P202.PrismHomotopy.contractible R R C.leftPair.space k)
    (fun k _ => P202.PrismHomotopy.contractible R R C.rightPair.space k)

/-- Positive-dimensional geometric spheres are path connected in their actual
Euclidean subspace topology. -/
lemma sphere_pathConnected (n : ℕ) : PathConnectedSpace (sphere (n+1)) := by
  have hd : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin ((n+1)+1))) := by
    rw [← Module.finrank_eq_rank]
    simp only [finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < (n+1)+1 by omega)
  exact isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere hd (0 : EuclideanSpace ℝ (Fin ((n+1)+1)))
      (show (0 : ℝ) ≤ 1 by norm_num))

/-- This includes all module coefficients; no finite generation or
coefficient connectedness is used. -/
lemma sphere_reduced_zero (n : ℕ) : IsZero (reducedHomology R M (sphere (n+1)) 0) := by
  have := sphere_pathConnected n
  obtain ⟨e⟩ := P202.SingularDegreeZero.reducedDegreeZero R M (sphere (n+1))
  have : Subsingleton (LinearMap.ker
      (P202Specs.SingularDegreeZero.componentSum R M (sphere (n+1)))) :=
    P202.SingularDegreeZero.sumKernel_subsingleton R M (ZerothHomotopy (sphere (n+1)))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact e.injective.subsingleton

/-- Homotopy equivalences act by actual reduced singular homology
isomorphisms, for arbitrary module coefficients and all integer degrees. -/
def reducedHomologyIsoOfHomotopyEquiv {X Y : TopCat.{w}}
    (e : ContinuousMap.HomotopyEquiv X Y) (j : ℤ) :
    reducedHomology R M X j ≅ reducedHomology R M Y j := by
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  have hfg : TopCat.Homotopy (f ≫ g) (𝟙 X) := Classical.choice e.left_inv
  have hgf : TopCat.Homotopy (g ≫ f) (𝟙 Y) := Classical.choice e.right_inv
  have := (P202.PrismHomotopy.equivalence R M f g hfg hgf j).2
  exact asIso ((reducedHomologyFunctor R M j).map f)

/-- The library's coordinate sphere has a literal two-pole open cover.
Only its topological cover is used; its de Rham complexes play no role. -/
def spherePoleCover (n : ℕ) : P202Specs.MayerVietoris.CoverPair.{0,0} :=
  let C := SmoothManifolds.SphereCohomology.PoleTopology.cover n
  P202Specs.MayerVietoris.CoverPair.ofSets
    ⟨TopCat.of (SmoothManifolds.SphereTorusData.Sphere n), ∅⟩
    C.U C.V C.U.isOpen C.V.isOpen (by
      apply Set.eq_univ_of_forall
      intro x
      exact C.cover x)

lemma spherePoleCover_left_contractible (n : ℕ) :
    ContractibleSpace (spherePoleCover n).leftPair.space :=
  (SmoothManifolds.SphereCohomology.PoleTopology.complements_contractible n).1

lemma spherePoleCover_right_contractible (n : ℕ) :
    ContractibleSpace (spherePoleCover n).rightPair.space :=
  (SmoothManifolds.SphereCohomology.PoleTopology.complements_contractible n).2

/-- A complete geometric suspension step for the ring-coefficient interface
that the present upstream Mayer–Vietoris theorem actually supplies. -/
lemma sphere_ring_shift (n : ℕ) (j : ℤ) :
    Nonempty (reducedHomology R R (sphere (n+1)) (j+1) ≅
      reducedHomology R R (sphere n) j) := by
  let C := spherePoleCover (n+1)
  have : ContractibleSpace C.leftPair.space := spherePoleCover_left_contractible (n+1)
  have : ContractibleSpace C.rightPair.space := spherePoleCover_right_contractible (n+1)
  have : Nonempty C.leftPair.space :=
    ⟨⟨SmoothManifolds.SphereCohomology.PoleTopology.south (n+1),
      (SmoothManifolds.SphereCohomology.PoleTopology.north_ne_south (n+1)).symm⟩⟩
  have : Nonempty C.rightPair.space :=
    ⟨⟨SmoothManifolds.SphereCohomology.PoleTopology.north (n+1),
      SmoothManifolds.SphereCohomology.PoleTopology.north_ne_south (n+1)⟩⟩
  obtain ⟨δ, hδ⟩ := reducedMV_shifts R
    P202.MayerVietoris.mayerVietoris.{u,0,0}
  have := hδ C j
  let e := SmoothManifolds.SphereCohomology.PoleTopology.overlapHomotopyEquiv n
  exact ⟨(reducedHomologyFunctor R R (j+1)).mapIso
      (TopCat.isoOfHomeo
        (SmoothManifolds.SphereCohomology.metricSphereHomeomorph (n+1))).symm ≪≫
    asIso (δ C j) ≪≫
    reducedHomologyIsoOfHomotopyEquiv R R
      (X := C.intersectionPair.space)
      (Y := TopCat.of (SmoothManifolds.SphereTorusData.Sphere n)) e j ≪≫
    (reducedHomologyFunctor R R j).mapIso
      (TopCat.isoOfHomeo (SmoothManifolds.SphereCohomology.metricSphereHomeomorph n))⟩

/-- The full nonnegative sphere computation with coefficients in the ring
itself, before coefficient change by tensoring integral chain homotopy equivalences. -/
lemma sphere_ring_homology (n j : ℕ) :
    (j = n → Nonempty (reducedHomology R R (sphere n) (j : ℤ) ≃ₗ[R] R)) ∧
    (j ≠ n → IsZero (reducedHomology R R (sphere n) (j : ℤ))) := by
  induction n generalizing j with
  | zero => exact sphere_zero R R j
  | succ n ih =>
    cases j with
    | zero =>
      exact ⟨fun h => False.elim (by omega), fun _ => sphere_reduced_zero R R n⟩
    | succ j =>
      obtain ⟨e⟩ := sphere_ring_shift R n (j : ℤ)
      have hj : ((j+1 : ℕ) : ℤ) = (j : ℤ)+1 := by omega
      rw [hj]
      constructor
      · intro h
        obtain ⟨f⟩ := (ih j).1 (by omega)
        exact ⟨e.toLinearEquiv.trans f⟩
      · intro h
        exact e.isZero_iff.mpr ((ih j).2 (by omega))

/- Projectivity permits coefficient change without a flatness hypothesis. -/
namespace ConcentratedHomology
variable {C : Type u} [Category.{v} C] [Abelian C]

noncomputable def fromSingleHomology (K : ChainComplex C ℕ) (n : ℕ)
    [Projective (K.homology n)] :
    (single C (.down ℕ) n).obj (K.homology n) ⟶ K :=
  mkHomFromSingle
    (Projective.factorThru (𝟙 (K.homology n)) (K.homologyπ n) ≫ K.iCycles n)
    (by intro k hk; rw [Category.assoc, K.iCycles_d, comp_zero])

lemma fromSingleHomology_quasiIso (K : ChainComplex C ℕ) (n : ℕ)
    [Projective (K.homology n)]
    (h : ∀ i : ℕ, i ≠ n → IsZero (K.homology i)) :
    QuasiIso (fromSingleHomology K n) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : i = n
  · subst i
    have heq : homologyMap (fromSingleHomology K n) n =
        (singleObjHomologySelfIso (.down ℕ) n (K.homology n)).hom := by
      apply (cancel_epi (((single C (.down ℕ) n).obj (K.homology n)).homologyπ n)).mp
      rw [homologyπ_naturality, homologyπ_singleObjHomologySelfIso_hom]
      have heq' : cyclesMap (fromSingleHomology K n) n =
          (singleObjCyclesSelfIso (.down ℕ) n (K.homology n)).hom ≫
            Projective.factorThru (𝟙 (K.homology n)) (K.homologyπ n) := by
        apply (cancel_mono (K.iCycles n)).mp
        rw [cyclesMap_i]
        simp only [fromSingleHomology, mkHomFromSingle_f, Category.assoc,
          singleObjCyclesSelfIso_hom]
      rw [heq', Category.assoc, Projective.factorThru_comp, Category.comp_id]
    rw [heq]
    infer_instance
  · exact (isZero_single_obj_homology (.down ℕ) n (K.homology n) i hi).isIso
      (h i hi) _

noncomputable def singleHomologyHomotopyEquiv (K : ChainComplex C ℕ) (n : ℕ)
    [Projective (K.homology n)] [∀ i, Projective (K.X i)]
    (h : ∀ i : ℕ, i ≠ n → IsZero (K.homology i)) :
    HomotopyEquiv ((single C (.down ℕ) n).obj (K.homology n)) K := by
  haveI : ∀ i, Projective (((single C (.down ℕ) n).obj (K.homology n)).X i) := by
    intro i
    by_cases hi : i = n
    · subst i
      simpa only [single_obj_X_self] using (inferInstance : Projective (K.homology n))
    · exact (isZero_single_obj_X (.down ℕ) n (K.homology n) i hi).projective
  have hf := (ChainComplex.quasiIso_iff_of_projective (fromSingleHomology K n)).mp
    (fromSingleHomology_quasiIso K n h)
  exact Classical.choose hf
end ConcentratedHomology

namespace ConcentratedHomology
universe u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

noncomputable def mapSingleHomologyIso (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) (n : ℕ)
    [Projective (K.homology n)] [∀ i, Projective (K.X i)]
    (h : ∀ i : ℕ, i ≠ n → IsZero (K.homology i)) :
    ((F.mapHomologicalComplex (.down ℕ)).obj K).homology n ≅ F.obj (K.homology n) :=
  ((F.mapHomotopyEquiv (singleHomologyHomotopyEquiv K n h)).toHomologyIso n).symm ≪≫
    (homologyFunctor D (.down ℕ) n).mapIso
      ((singleMapHomologicalComplex F (.down ℕ) n).app (K.homology n)) ≪≫
    singleObjHomologySelfIso (.down ℕ) n (F.obj (K.homology n))

lemma mapSingleHomology_isZero (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) (n : ℕ)
    [Projective (K.homology n)] [∀ i, Projective (K.X i)]
    (h : ∀ i : ℕ, i ≠ n → IsZero (K.homology i))
    (i : ℕ) (hi : i ≠ n) :
    IsZero (((F.mapHomologicalComplex (.down ℕ)).obj K).homology i) := by
  let e := (F.mapHomotopyEquiv (singleHomologyHomotopyEquiv K n h)).toHomologyIso i
  let e' := (homologyFunctor D (.down ℕ) i).mapIso
    ((singleMapHomologicalComplex F (.down ℕ) n).app (K.homology n))
  exact e.isZero_iff.mp (e'.isZero_iff.mpr
    (isZero_single_obj_homology (.down ℕ) n (F.obj (K.homology n)) i hi))
end ConcentratedHomology

lemma sphere_augmented_projective (n k : ℕ) :
    Projective ((augmentedShifted R R (sphere n)).X k) := by
  cases k with
  | zero =>
    change Projective (coefficientModule R R)
    infer_instance
  | succ k =>
    change Projective (ModuleCat.of R (Chains R (sphere n) k))
    infer_instance

lemma sphere_augmented_homology (n k : ℕ) :
    (k = n+1 → Nonempty ((augmentedShifted R R (sphere n)).homology k ≃ₗ[R] R)) ∧
    (k ≠ n+1 → IsZero ((augmentedShifted R R (sphere n)).homology k)) := by
  have : Nonempty (sphere n) :=
    (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).to_subtype
  cases k with
  | zero =>
    refine ⟨fun h => False.elim (by omega), fun _ => ?_⟩
    exact ((augmentedShifted R R (sphere n)).extendHomologyIso (degreeEmbedding (-1))
      (j := 0) (by rfl)).isZero_iff.mp
      (P202.SingularDegreeZero.nonemptyReducedMinusOne R R (sphere n))
  | succ k =>
    let e : reducedHomology R R (sphere n) (k : ℤ) ≅
        (augmentedShifted R R (sphere n)).homology (k+1) :=
      (augmentedShifted R R (sphere n)).extendHomologyIso (degreeEmbedding (-1))
        (j := k+1) (by change (-1 : ℤ) + (k+1 : ℕ) = (k : ℤ); omega)
    constructor
    · intro h
      obtain ⟨f⟩ := (sphere_ring_homology R n k).1 (by omega)
      exact ⟨e.symm.toLinearEquiv.trans f⟩
    · intro h
      exact e.isZero_iff.mp ((sphere_ring_homology R n k).2 (by omega))

namespace IntegralCoefficients

/-- Tensor integral modules with the coefficient module. The scalar action
is on the first factor, so this lands directly in R-modules. -/
def integralTensorFunctor : ModuleCat.{w} ℤ ⥤ ModuleCat.{max v w} R where
  obj A := ModuleCat.of R (M ⊗[ℤ] A)
  map f := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lTensor R M f.hom)
  map_id A := by
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.lTensor_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.lTensor_comp g.hom f.hom

instance : (integralTensorFunctor.{u,v,w} R M).Additive where
  map_add := by
    intro A B f g
    apply ModuleCat.hom_ext
    exact map_add (TensorProduct.AlgebraTensorModule.lTensor R M) f.hom g.hom

/-- The augmentation coefficient object, with both universe lifts respected. -/
def integralTensorAugmentationEquiv :
    (M ⊗[ℤ] ULift.{w} ℤ) ≃ₗ[R] ULift.{w} M :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R M)
    (ULift.moduleEquiv : ULift.{w} ℤ ≃ₗ[ℤ] ℤ)).trans
      ((TensorProduct.AlgebraTensorModule.rid ℤ R M).trans ULift.moduleEquiv.symm)

@[simp] lemma integralTensorAugmentationEquiv_tmul (m : M) (a : ULift.{w} ℤ) :
    integralTensorAugmentationEquiv R M (m ⊗ₜ[ℤ] a) = ULift.up (a.down • m) := rfl

/-- Coefficients at a singular-simplex basis, retaining R-linearity. -/
def integralTensorChainsEquiv (X : TopCat.{w}) (n : ℕ) :
    (M ⊗[ℤ] Chains ℤ X n) ≃ₗ[R] Chains M X n :=
  by classical exact TensorProduct.finsuppScalarRight ℤ R M (Simplex X n)

@[simp] lemma integralTensorChainsEquiv_tmul_single (X : TopCat.{w}) (n : ℕ)
    (m : M) (s : Simplex X n) (a : ℤ) :
    integralTensorChainsEquiv R M X n (m ⊗ₜ[ℤ] Finsupp.single s a) =
      Finsupp.single s (a • m) := by
  ext i
  by_cases h : s = i
  · subst i; simp [integralTensorChainsEquiv]
  · simp [integralTensorChainsEquiv, h]

lemma integralTensorChainsEquiv_boundary (X : TopCat.{w}) (n : ℕ)
    (z : M ⊗[ℤ] Chains ℤ X (n+1)) :
    integralTensorChainsEquiv R M X n
        (TensorProduct.AlgebraTensorModule.lTensor R M (boundary ℤ ℤ X n) z) =
      boundary R M X n (integralTensorChainsEquiv R M X (n+1) z) := by
  classical
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul m p =>
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hp hq
    | single s a =>
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul,
        P202.SingularChains.boundary_single, integralTensorChainsEquiv_tmul_single,
        TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_zsmul]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : Chains M X n => (-1 : ℤ)^i.val • z)
        (integralTensorChainsEquiv_tmul_single R M X n m (face i s) a)

lemma integralTensorChainsEquiv_augmentation (X : TopCat.{w})
    (z : M ⊗[ℤ] Chains ℤ X 0) :
    integralTensorAugmentationEquiv R M
        (TensorProduct.AlgebraTensorModule.lTensor R M (augmentation ℤ ℤ X).hom z) =
      augmentation R M X (integralTensorChainsEquiv R M X 0 z) := by
  classical
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul m p =>
    induction p using Finsupp.induction_linear with
    | zero =>
      simp only [TensorProduct.tmul_zero, map_zero]
    | add p q hp hq =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hp hq
    | single s a =>
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, augmentation,
                integralTensorChainsEquiv_tmul_single, integralTensorAugmentationEquiv_tmul]
      apply ULift.ext
      change sumCoefficients ℤ ℤ _ (Finsupp.single s a) • m =
        sumCoefficients R M _ (Finsupp.single s (a • m))
      rw [show sumCoefficients ℤ ℤ _ (Finsupp.single s a) = a from
        P202.SingularChains.augmentationLinear_single ℤ ℤ X s a,
        show sumCoefficients R M _ (Finsupp.single s (a • m)) = a • m from
        P202.SingularChains.augmentationLinear_single R M X s (a • m)]

/-- Degree-by-degree coefficient comparison for the augmented complexes. -/
def integralTensorAugmentedComponent (X : TopCat.{w}) (n : ℕ) :
    (integralTensorFunctor R M).obj ((augmentedShifted ℤ ℤ X).X n) ≅
      (augmentedShifted R M X).X n := by
  cases n with
  | zero => exact (integralTensorAugmentationEquiv R M).toModuleIso
  | succ n => exact (integralTensorChainsEquiv R M X n).toModuleIso

/-- Tensoring the integral augmented singular complex gives the actual
R-module coefficient complex, including its augmentation. -/
def integralTensorAugmentedIso (X : TopCat.{w}) :
    ((integralTensorFunctor R M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (augmentedShifted ℤ ℤ X) ≅ augmentedShifted R M X :=
  HomologicalComplex.Hom.isoOfComponents
    (integralTensorAugmentedComponent R M X) (by
      intro i j hij
      have hi : j+1=i := hij
      subst i
      cases j with
      | zero =>
        apply ModuleCat.hom_ext
        ext z
        exact (integralTensorChainsEquiv_augmentation R M X z).symm
      | succ n =>
        apply ModuleCat.hom_ext
        ext z
        exact (integralTensorChainsEquiv_boundary R M X n z).symm)

/-- The tensor image of the integral unit is the specified coefficient module. -/
def integralTensorUnitIso :
    (integralTensorFunctor.{u,v,0} R M).obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of R M :=
  (TensorProduct.AlgebraTensorModule.rid ℤ R M).toModuleIso

end IntegralCoefficients

lemma sphere_homology_of_tensor_adapter
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (F : ModuleCat.{0} ℤ ⥤ ModuleCat.{v} R) [F.Additive]
    (n : ℕ)
    (e : (F.mapHomologicalComplex (.down ℕ)).obj (augmentedShifted ℤ ℤ (sphere n)) ≅
      augmentedShifted R M (sphere n))
    (eZ : F.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of R M) (j : ℕ) :
    (j = n → Nonempty (reducedHomology R M (sphere n) (j : ℤ) ≃ₗ[R] M)) ∧
    (j ≠ n → IsZero (reducedHomology R M (sphere n) (j : ℤ))) := by
  let K := augmentedShifted ℤ ℤ (sphere n)
  have : ∀ k, Projective (K.X k) := fun k => sphere_augmented_projective ℤ n k
  obtain ⟨f⟩ := (sphere_augmented_homology ℤ n (n+1)).1 rfl
  let ef : K.homology (n+1) ≅ ModuleCat.of ℤ ℤ := f.toModuleIso
  have : Projective (K.homology (n+1)) := Projective.of_iso ef.symm inferInstance
  have hvan (k : ℕ) (hk : k ≠ n+1) : IsZero (K.homology k) :=
    (sphere_augmented_homology ℤ n k).2 hk
  let er : reducedHomology R M (sphere n) (j : ℤ) ≅
      (augmentedShifted R M (sphere n)).homology (j+1) :=
    (augmentedShifted R M (sphere n)).extendHomologyIso (degreeEmbedding (-1))
      (j := j+1) (by change (-1 : ℤ) + (j+1 : ℕ) = (j : ℤ); omega)
  let ee := (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.down ℕ) (j+1)).mapIso e
  constructor
  · intro hj
    subst j
    let eh := ConcentratedHomology.mapSingleHomologyIso F K (n+1) hvan
    exact ⟨(er ≪≫ ee.symm ≪≫ eh ≪≫ F.mapIso ef ≪≫ eZ).toLinearEquiv⟩
  · intro hj
    exact er.isZero_iff.mpr (ee.isZero_iff.mp
      (ConcentratedHomology.mapSingleHomology_isZero F K (n+1) hvan (j+1) (by omega)))

/-- Integral sphere chains are free with free homology in one degree.
Tensoring their chain homotopy equivalence computes every module coefficient. -/
theorem sphereHomology : sphereHomology_type.{u,v} := by
  intro R _ M _ _ n j
  exact sphere_homology_of_tensor_adapter R M
    (IntegralCoefficients.integralTensorFunctor R M) n
    (IntegralCoefficients.integralTensorAugmentedIso R M (sphere n))
    (IntegralCoefficients.integralTensorUnitIso R M) j

/-- The relative disk calculation includes the point-empty pair. -/
theorem diskHomology : diskHomology_type.{u,v} :=
  diskHomology_of_sphereHomology sphereHomology

/-- Once the positive-degree geometric suspension isomorphisms have been
constructed, the two-point computation and connectedness supply the full
arbitrary-coefficient sphere calculation. -/
lemma sphereHomology_of_shifts
    (hs : ∀ (R : Type u) [CommRing R] (M : Type v)
      [AddCommGroup M] [Module R M] (n j : ℕ),
      Nonempty (reducedHomology R M (sphere (n+1)) ((j+1 : ℕ) : ℤ) ≃ₗ[R]
        reducedHomology R M (sphere n) (j : ℤ))) :
    sphereHomology_type.{u,v} := by
  intro R _ M _ _ n
  induction n with
  | zero => exact sphere_zero R M
  | succ n ih =>
    intro j
    cases j with
    | zero =>
      exact ⟨fun h => False.elim (by omega), fun _ => sphere_reduced_zero R M n⟩
    | succ j =>
      obtain ⟨e⟩ := hs R M n j
      constructor
      · intro h
        obtain ⟨f⟩ := (ih j).1 (by omega)
        exact ⟨e.trans f⟩
      · intro h
        apply ModuleCat.isZero_iff_subsingleton.mpr
        have := ModuleCat.isZero_iff_subsingleton.mp ((ih j).2 (by omega))
        exact e.injective.subsingleton

/-- The simplex boundary is precisely the complement of the positive
barycentric stratum. Nonnegativity of all weights is essential here. -/
lemma simplex_boundary_iff (n : ℕ) (x : simplex n) :
    x ∈ (simplexPair n).subspace ↔
      x ∉ P202.Cellular.standardSimplexInterior n := by
  classical
  change (∃ i, x.weights i = 0) ↔ ¬ (∀ i, 0 < x.weights i)
  push Not
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, hi.le⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, le_antisymm hi (x.weights_nonneg i)⟩

/-- The accepted disk parametrization preserves the whole boundary, including
the empty boundary in dimension zero. -/
def diskSimplexPairIso (n : ℕ) : diskPair n ≅ simplexPair n := by
  let e := Classical.choose (P202.Topology.diskSimplexParametrization n)
  have he := Classical.choose_spec (P202.Topology.diskSimplexParametrization n)
  have hb (x : disk n) : e x ∈ (simplexPair n).subspace ↔
      x ∈ (diskPair n).subspace := by
    rw [simplex_boundary_iff, he]
    change ¬ ‖x.val‖ < 1 ↔ ‖x.val‖ = 1
    have hx : ‖x.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    exact ⟨fun h => le_antisymm hx (not_lt.mp h), fun h => by simp [h]⟩
  exact {
    hom := ⟨TopCat.ofHom ⟨e, e.continuous⟩, fun x hx => (hb x).mpr hx⟩
    inv := ⟨TopCat.ofHom ⟨e.symm, e.symm.continuous⟩, fun x hx =>
      (hb (e.symm x)).mp (by simpa using hx)⟩
    hom_inv_id := PairMap.ext _ _ (by ext x; exact e.symm_apply_apply x)
    inv_hom_id := PairMap.ext _ _ (by ext x; exact e.apply_symm_apply x) }

/-- The disk and simplex computations use the same relative singular functor. -/
def diskSimplexHomologyIso (n : ℕ) (j : ℤ) :
    relativeHomology R M (diskPair n) j ≅
      relativeHomology R M (simplexPair n) j :=
  (relativeHomologyFunctor R M j).mapIso (diskSimplexPairIso n)

lemma simplexVanishing_of_diskHomology (hd : diskHomology_type.{u,v}) :
    simplexVanishing_type.{u,v} := by
  intro R _ M _ _ n j hj
  exact (diskSimplexHomologyIso R M n (j : ℤ)).isZero_iff.mp ((hd R M n j).2 hj)

/-- All off-top simplex groups therefore follow from the sphere computation. -/
lemma simplexVanishing_of_sphereHomology (hs : sphereHomology_type.{u,v}) :
    simplexVanishing_type.{u,v} :=
  simplexVanishing_of_diskHomology (diskHomology_of_sphereHomology hs)

/-- Disk parametrization transfers the off-top vanishing to the simplex pair. -/
theorem simplexVanishing : simplexVanishing_type.{u,v} :=
  simplexVanishing_of_diskHomology diskHomology

namespace IntegralCoefficients
open P202Specs.SingularChains P202Specs.RelativeSingularChains

def relativeCoordinates (P : Pair.{0}) (n : ℕ) :
    (nonnegative R M P).X n ≃ₗ[R] (Outside P n →₀ M) :=
  Classical.choose (P202.RelativeSingularChains.quotient_coordinates R M P n)

lemma relativeCoordinates_projection (P : Pair.{0}) (n : ℕ) (c : Chains M P.space n) :
    relativeCoordinates R M P n ((projection (chainFunctor R M) P).f n c) =
      outsideProjection R M P n c :=
  Classical.choose_spec (P202.RelativeSingularChains.quotient_coordinates R M P n) c

def integralTensorRelativeComponent (P : Pair.{0}) (n : ℕ) :
    (integralTensorFunctor R M).obj ((nonnegative ℤ ℤ P).X n) ≅
      (nonnegative R M P).X n := by
  classical
  exact (integralTensorFunctor R M).mapIso (relativeCoordinates ℤ ℤ P n).toModuleIso ≪≫
    (TensorProduct.finsuppScalarRight ℤ R M (Outside P n)).toModuleIso ≪≫
      (relativeCoordinates R M P n).symm.toModuleIso

lemma integralTensorRelativeComponent_projection (P : Pair.{0}) (n : ℕ)
    (m : M) (c : Chains ℤ P.space n) :
    (integralTensorRelativeComponent R M P n).hom
      (m ⊗ₜ[ℤ] ((projection (chainFunctor ℤ ℤ) P).f n c)) =
      (projection (chainFunctor R M) P).f n
        (integralTensorChainsEquiv R M P.space n (m ⊗ₜ[ℤ] c)) := by
  classical
  apply (relativeCoordinates R M P n).injective
  change (relativeCoordinates R M P n)
    ((relativeCoordinates R M P n).symm
      ((TensorProduct.finsuppScalarRight ℤ R M (Outside P n))
        (TensorProduct.AlgebraTensorModule.lTensor R M
          (relativeCoordinates ℤ ℤ P n).toLinearMap
            (m ⊗ₜ[ℤ] ((projection (chainFunctor ℤ ℤ) P).f n c))))) = _
  rw [LinearEquiv.apply_symm_apply, TensorProduct.AlgebraTensorModule.lTensor_tmul]
  rw [relativeCoordinates_projection R M P n]
  change (TensorProduct.finsuppScalarRight ℤ R M (Outside P n))
    (m ⊗ₜ[ℤ] (relativeCoordinates ℤ ℤ P n)
      ((projection (chainFunctor ℤ ℤ) P).f n c)) = _
  rw [relativeCoordinates_projection ℤ ℤ P n c]
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hc hd
  | single s a =>
    ext i
    rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
    change (Finsupp.single s a) i.val • m =
      (integralTensorChainsEquiv R M P.space n
        (m ⊗ₜ[ℤ] Finsupp.single s a)) i.val
    rw [integralTensorChainsEquiv_tmul_single]
    by_cases h : s = i.val
    · subst s; simp
    · simp [h]
end IntegralCoefficients

namespace IntegralCoefficients
open P202Specs.SingularChains P202Specs.RelativeSingularChains

lemma integralTensorRelativeComponent_boundary (P : Pair.{0}) (n : ℕ)
    (z : M ⊗[ℤ] (nonnegative ℤ ℤ P).X (n+1)) :
    (integralTensorRelativeComponent R M P n).hom
        (TensorProduct.AlgebraTensorModule.lTensor R M
          ((nonnegative ℤ ℤ P).d (n+1) n).hom z) =
      (nonnegative R M P).d (n+1) n
        ((integralTensorRelativeComponent R M P (n+1)).hom z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul m q =>
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((projection (chainFunctor ℤ ℤ) P).f (n+1))).mp inferInstance q
    rw [TensorProduct.AlgebraTensorModule.lTensor_tmul,
      integralTensorRelativeComponent_projection]
    have hpZ := congrArg (fun f => f c)
      ((projection (chainFunctor ℤ ℤ) P).comm (n+1) n)
    change (nonnegative ℤ ℤ P).d (n+1) n
        ((projection (chainFunctor ℤ ℤ) P).f (n+1) c) =
      (projection (chainFunctor ℤ ℤ) P).f n (boundary ℤ ℤ P.space n c) at hpZ
    rw [hpZ, integralTensorRelativeComponent_projection]
    have hpM := congrArg (fun f => f
      (integralTensorChainsEquiv R M P.space (n+1) (m ⊗ₜ[ℤ] c)))
      ((projection (chainFunctor R M) P).comm (n+1) n)
    change (nonnegative R M P).d (n+1) n
        ((projection (chainFunctor R M) P).f (n+1)
          (integralTensorChainsEquiv R M P.space (n+1) (m ⊗ₜ[ℤ] c))) =
      (projection (chainFunctor R M) P).f n
        (boundary R M P.space n
          (integralTensorChainsEquiv R M P.space (n+1) (m ⊗ₜ[ℤ] c))) at hpM
    rw [hpM]
    apply congrArg ((projection (chainFunctor R M) P).f n)
    simpa only [TensorProduct.AlgebraTensorModule.lTensor_tmul] using
      integralTensorChainsEquiv_boundary R M P.space n (m ⊗ₜ[ℤ] c)

def integralTensorRelativeIso (P : Pair.{0}) :
    ((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).obj
      (nonnegative ℤ ℤ P) ≅ nonnegative R M P :=
  HomologicalComplex.Hom.isoOfComponents (integralTensorRelativeComponent R M P)
    (by
      intro i j hij
      have hi : j+1=i := hij
      subst i
      apply ModuleCat.hom_ext
      ext z
      exact (integralTensorRelativeComponent_boundary R M P j z).symm)
end IntegralCoefficients

namespace IntegralCoefficients
open P202Specs.SingularChains P202Specs.RelativeSingularChains

theorem relativeExtensionCokernel (P : Pair.{0}) :
    ((sequence (chainFunctor R M) P).map
      ((degreeEmbedding 0).extendFunctor (ModuleCat.{v} R))).ShortExact :=
  P202.MayerVietoris.extend_shortExact (degreeEmbedding 0)
    (sequence (chainFunctor R M) P)
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (P202.RelativeSingularChains.sequence_shortExact (chainFunctor R M) P))

def ordinaryRelativeExtensionIso (P : Pair.{0}) :
    ordinary R M P ≅ (nonnegative R M P).extend (degreeEmbedding 0) :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (inclusion (ordinaryFunctor R M) P))
    (relativeExtensionCokernel R M P).gIsCokernel

lemma ordinaryRelativeExtensionIso_projection (P : Pair.{0}) :
    projection (ordinaryFunctor R M) P ≫ (ordinaryRelativeExtensionIso R M P).hom =
      HomologicalComplex.extendMap (projection (chainFunctor R M) P) (degreeEmbedding 0) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (inclusion (ordinaryFunctor R M) P))
    (relativeExtensionCokernel R M P).gIsCokernel (.one)

def ordinaryRelativeHomologyIso (P : Pair.{0}) (n : ℕ) :
    relativeHomology R M P (n : ℤ) ≅ (nonnegative R M P).homology n :=
  (HomologicalComplex.homologyFunctor _ _ (n : ℤ)).mapIso
      (ordinaryRelativeExtensionIso R M P) ≪≫
    (nonnegative R M P).extendHomologyIso (degreeEmbedding 0)
      (j := n) (by change (0 : ℤ) + (n : ℤ) = n; omega)
end IntegralCoefficients

namespace SimplexGeometry

/-- Restrict a genuine pair isomorphism to its specified subspaces. -/
def pairBoundaryHomeomorph {P Q : Pair.{w}} (e : P ≅ Q) : P.sub ≃ₜ Q.sub where
  toFun := e.hom.restrict
  invFun := e.inv.restrict
  left_inv x := Subtype.ext (by
    have h := congrArg (fun f : P ⟶ P => f.map x.val) e.hom_inv_id
    exact h)
  right_inv x := Subtype.ext (by
    have h := congrArg (fun f : Q ⟶ Q => f.map x.val) e.inv_hom_id
    exact h)
  continuous_toFun := e.hom.restrict.hom.continuous
  continuous_invFun := e.inv.restrict.hom.continuous

/-- A simplex boundary is the geometric sphere of the same dimension. -/
def simplexBoundaryHomeomorph (n : ℕ) : (simplexPair (n+1)).sub ≃ₜ sphere n :=
  (pairBoundaryHomeomorph (diskSimplexPairIso (n+1))).symm.trans
    (diskBoundaryHomeomorph (n+1))

/-- Puncturing the actual simplex boundary at any chosen point gives Euclidean space. -/
def simplexBoundaryPuncturedHomeomorph (n : ℕ) (p : (simplexPair (n+1)).sub) :
    {x : (simplexPair (n+1)).sub // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin n) := by
  let e := (simplexBoundaryHomeomorph n).trans
    (SmoothManifolds.SphereCohomology.metricSphereHomeomorph n).symm
  exact (e.subtype (fun x => (show x ≠ p ↔ e x ≠ e p from e.injective.ne_iff.symm))).trans
    (SmoothManifolds.SphereCohomology.PoleTopology.puncturedHomeomorph n (e p))

lemma simplexBoundary_punctured_contractible (n : ℕ)
    (p : (simplexPair (n+1)).sub) :
    ContractibleSpace {x : (simplexPair (n+1)).sub // x ≠ p} :=
  (simplexBoundaryPuncturedHomeomorph n p).contractibleSpace




/-- The distinguished vertex, as a point of the entire simplex boundary. -/
def simplexBoundaryVertex (n : ℕ) : (simplexPair (n+1)).sub :=
  ⟨Convexity.StdSimplex.single 0, ⟨1, by simp⟩⟩

/-- Interior barycenter of the face opposite the distinguished vertex. -/
def oppositeFaceBarycenter (n : ℕ) : (simplexPair (n+1)).sub :=
  boundaryFace 0 Convexity.StdSimplex.barycenter

lemma boundaryFace_zero_weight {n : ℕ} (i : Fin (n+2)) (x : simplex n) :
    (boundaryFace i x).val.weights i = 0 := by
  change (x.weights.mapDomain i.succAbove) i = 0
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)

lemma oppositeFaceBarycenter_weight_succ (n : ℕ) (i : Fin (n+1)) :
    (oppositeFaceBarycenter n).val.weights i.succ = (n+1 : ℝ)⁻¹ := by
  change (Convexity.StdSimplex.barycenter.weights.mapDomain
    (0 : Fin (n+2)).succAbove) i.succ = _
  rw [Fin.succAbove_zero, Finsupp.mapDomain_apply_of_injective (Fin.succ_injective (n+1))]
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    (Convexity.StdSimplex.weights_barycenter_apply (K := ℝ) i)

lemma simplexBoundaryVertex_ne_barycenter (n : ℕ) :
    simplexBoundaryVertex n ≠ oppositeFaceBarycenter n := by
  intro h
  have h0 := congrArg (fun x : (simplexPair (n+1)).sub => x.val.weights 0) h
  have hb := boundaryFace_zero_weight (0 : Fin (n+2))
    (Convexity.StdSimplex.barycenter : simplex n)
  simp only [simplexBoundaryVertex, Convexity.StdSimplex.weights_single,
    Finsupp.single_eq_same] at h0
  rw [show (oppositeFaceBarycenter n).val.weights 0 = 0 from hb] at h0
  exact one_ne_zero h0

/-- A face-adapted open cover. The opposite face belongs to the left member,
and every other boundary face belongs to the right member. -/
def simplexBoundaryFaceCover (n : ℕ) : P202Specs.MayerVietoris.CoverPair.{0,0} := by
  haveI : T2Space ((simplexPair (n+1)).sub) :=
    (simplexBoundaryHomeomorph n).symm.t2Space
  exact P202Specs.MayerVietoris.CoverPair.ofSets
    ⟨(simplexPair (n+1)).sub, ∅⟩
    {simplexBoundaryVertex n}ᶜ {oppositeFaceBarycenter n}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (by
      apply Set.eq_univ_of_forall
      intro x
      by_cases h : x = simplexBoundaryVertex n
      · exact Or.inr (by simpa [h] using simplexBoundaryVertex_ne_barycenter n)
      · exact Or.inl h)

lemma simplexBoundaryFaceCover_left_contractible (n : ℕ) :
    ContractibleSpace (simplexBoundaryFaceCover n).leftPair.space :=
  simplexBoundary_punctured_contractible n (simplexBoundaryVertex n)

lemma simplexBoundaryFaceCover_right_contractible (n : ℕ) :
    ContractibleSpace (simplexBoundaryFaceCover n).rightPair.space :=
  simplexBoundary_punctured_contractible n (oppositeFaceBarycenter n)

lemma boundaryFace_zero_mem_left (n : ℕ) (x : simplex n) :
    boundaryFace (0 : Fin (n+2)) x ∈ (simplexBoundaryFaceCover n).left := by
  change boundaryFace (0 : Fin (n+2)) x ≠ simplexBoundaryVertex n
  intro h
  have h0 := congrArg (fun y : (simplexPair (n+1)).sub => y.val.weights 0) h
  rw [boundaryFace_zero_weight] at h0
  simp only [simplexBoundaryVertex, Convexity.StdSimplex.weights_single,
    Finsupp.single_eq_same] at h0
  exact zero_ne_one h0

lemma boundaryFace_succ_mem_right (n : ℕ) (i : Fin (n+1)) (x : simplex n) :
    boundaryFace i.succ x ∈ (simplexBoundaryFaceCover n).right := by
  change boundaryFace i.succ x ≠ oppositeFaceBarycenter n
  intro h
  have hi := congrArg (fun y : (simplexPair (n+1)).sub => y.val.weights i.succ) h
  rw [boundaryFace_zero_weight, oppositeFaceBarycenter_weight_succ] at hi
  have hp : (0 : ℝ) < (n+1 : ℝ)⁻¹ := by positivity
  linarith



lemma boundaryFace_zero_weight_succ (n : ℕ) (x : simplex n) (i : Fin (n+1)) :
    (boundaryFace (0 : Fin (n+2)) x).val.weights i.succ = x.weights i := by
  change (x.weights.mapDomain (0 : Fin (n+2)).succAbove) i.succ = x.weights i
  rw [Fin.succAbove_zero, Finsupp.mapDomain_apply_of_injective (Fin.succ_injective (n+1))]

/-- Side faces of the boundary, with the distinguished vertex removed. -/
abbrev simplexBoundarySide (n : ℕ) :=
  {x : (simplexPair (n+1)).sub //
    (∃ i : Fin (n+1), x.val.weights i.succ = 0) ∧ x ≠ simplexBoundaryVertex n}

/-- The smaller boundary enters as the boundary of the opposite face. -/
def simplexBoundarySideFace (n : ℕ) :
    C((simplexPair n).sub, simplexBoundarySide n) where
  toFun y := ⟨boundaryFace 0 y.val, by
    refine ⟨?_, boundaryFace_zero_mem_left n y.val⟩
    obtain ⟨i, hi⟩ := y.property
    exact ⟨i, (boundaryFace_zero_weight_succ n y.val i).trans hi⟩⟩
  continuous_toFun := ((boundaryFace 0).continuous.comp continuous_subtype_val).subtype_mk _

/-- Side points miss both punctures and therefore enter the overlap literally. -/
def simplexBoundarySideToOverlap (n : ℕ) :
    C(simplexBoundarySide n, (simplexBoundaryFaceCover n).intersectionPair.space) where
  toFun x := ⟨x.val, x.property.2, by
    intro h
    obtain ⟨i, hi⟩ := x.property.1
    have he := congrArg (fun y : (simplexPair (n+1)).sub => y.val.weights i.succ) h
    rw [hi, oppositeFaceBarycenter_weight_succ] at he
    have hp : (0 : ℝ) < (n+1 : ℝ)⁻¹ := by positivity
    linarith⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The exact smaller-boundary map needed in the Mayer–Vietoris induction. -/
def simplexBoundaryFaceToOverlap (n : ℕ) :
    C((simplexPair n).sub, (simplexBoundaryFaceCover n).intersectionPair.space) :=
  (simplexBoundarySideToOverlap n).comp (simplexBoundarySideFace n)

end SimplexGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open CategoryTheory
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
open scoped BigOperators

namespace SimplexGeometry

/-- Minimum of the barycentric coordinates other than the distinguished one. -/
def tailMin {n : ℕ} (x : simplex (n+1)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : Fin (n+1) => x.weights i.succ)

lemma tailMin_le {n : ℕ} (x : simplex (n+1)) (i : Fin (n+1)) :
    tailMin x ≤ x.weights i.succ :=
  Finset.inf'_le _ (Finset.mem_univ i)

lemma tailMin_nonneg {n : ℕ} (x : simplex (n+1)) : 0 ≤ tailMin x := by
  exact Finset.le_inf' _ _ (fun i _ => x.weights_nonneg i.succ)

lemma tailMin_continuous (n : ℕ) : Continuous (tailMin : simplex (n+1) → ℝ) :=
  Continuous.finset_inf'_apply _ (fun i _ => Convexity.StdSimplex.continuous_weights_apply ℝ i.succ)

lemma tailMin_attained {n : ℕ} (x : simplex (n+1)) :
    ∃ i : Fin (n+1), x.weights i.succ = tailMin x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i : Fin (n+1) => x.weights i.succ)
  exact ⟨i, hi.symm⟩

lemma tailMin_zero_iff {n : ℕ} (x : simplex (n+1)) :
    tailMin x = 0 ↔ ∃ i : Fin (n+1), x.weights i.succ = 0 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := tailMin_attained x
    exact ⟨i, hi.trans h⟩
  · rintro ⟨i, hi⟩
    exact le_antisymm (hi ▸ tailMin_le x i) (tailMin_nonneg x)

lemma tail_sum {n : ℕ} (x : simplex (n+1)) :
    x.weights 0 + ∑ i : Fin (n+1), x.weights i.succ = 1 := by
  simpa only [Fin.sum_univ_succ] using x.total_of_fintype

lemma tailMin_mul_le_sum {n : ℕ} (x : simplex (n+1)) :
    (n+1 : ℝ) * tailMin x ≤ ∑ i : Fin (n+1), x.weights i.succ := by
  calc
    _ = ∑ i : Fin (n+1), tailMin x := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => tailMin_le x i)

def radialDen {n : ℕ} (x : simplex (n+1)) : ℝ := 1-(n+1 : ℝ)*tailMin x

lemma radialDen_nonneg {n : ℕ} (x : simplex (n+1)) : 0 ≤ radialDen x := by
  have h := tailMin_mul_le_sum x
  have hs := tail_sum x
  have hz := x.weights_nonneg 0
  dsimp [radialDen]
  linarith

lemma radialDen_eq_zero {n : ℕ} (x : (simplexPair (n+1)).sub)
    (h : radialDen x.val = 0) : x = oppositeFaceBarycenter n := by
  have hm := tailMin_mul_le_sum x.val
  have hs := tail_sum x.val
  have hz := x.val.weights_nonneg 0
  have hx0 : x.val.weights 0 = 0 := by dsimp [radialDen] at h; linarith
  have htail : ∑ i : Fin (n+1), (x.val.weights i.succ - tailMin x.val) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [radialDen] at h
    push_cast
    linarith
  have hcoord (i : Fin (n+1)) : x.val.weights i.succ = tailMin x.val := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sub_nonneg.mpr (tailMin_le x.val i))).mp htail i (Finset.mem_univ i)
    linarith
  have hmin : tailMin x.val = (n+1 : ℝ)⁻¹ := by
    dsimp [radialDen] at h
    rw [← one_div]
    apply (eq_div_iff (by positivity : (n+1 : ℝ) ≠ 0)).mpr
    nlinarith
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hx0.trans (boundaryFace_zero_weight _ _).symm
  · exact (hcoord j).trans (hmin.trans (oppositeFaceBarycenter_weight_succ n j).symm)

lemma radialDen_pos {n : ℕ} (x : (simplexPair (n+1)).sub)
    (hx : x ≠ oppositeFaceBarycenter n) : 0 < radialDen x.val := by
  refine lt_of_le_of_ne (radialDen_nonneg x.val) ?_
  intro h
  exact hx (radialDen_eq_zero x h.symm)



def radialSimplex {n : ℕ} (x : (simplexPair (n+1)).sub)
    (hx : x ≠ oppositeFaceBarycenter n) : simplex (n+1) where
  weights := Finsupp.equivFunOnFinite.symm
    (Fin.cases (x.val.weights 0 / radialDen x.val)
      (fun i => (x.val.weights i.succ-tailMin x.val) / radialDen x.val))
  nonneg := by
    intro i
    simp only [Finsupp.coe_equivFunOnFinite_symm, Finsupp.zero_apply]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact div_nonneg (x.val.weights_nonneg 0) (radialDen_pos x hx).le
    · exact div_nonneg (sub_nonneg.mpr (tailMin_le x.val j)) (radialDen_pos x hx).le
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← add_div]
    apply (div_eq_one_iff_eq (radialDen_pos x hx).ne').mpr
    have hs := tail_sum x.val
    dsimp [radialDen]
    push_cast
    linarith

@[simp] lemma radialSimplex_weight_zero {n : ℕ} (x : (simplexPair (n+1)).sub)
    (hx : x ≠ oppositeFaceBarycenter n) :
    (radialSimplex x hx).weights 0 = x.val.weights 0 / radialDen x.val := rfl

@[simp] lemma radialSimplex_weight_succ {n : ℕ} (x : (simplexPair (n+1)).sub)
    (hx : x ≠ oppositeFaceBarycenter n) (i : Fin (n+1)) :
    (radialSimplex x hx).weights i.succ =
      (x.val.weights i.succ-tailMin x.val) / radialDen x.val := rfl

lemma radialSimplex_tail_zero {n : ℕ} (x : (simplexPair (n+1)).sub)
    (hx : x ≠ oppositeFaceBarycenter n) :
    ∃ i : Fin (n+1), (radialSimplex x hx).weights i.succ = 0 := by
  obtain ⟨i, hi⟩ := tailMin_attained x.val
  exact ⟨i, by rw [radialSimplex_weight_succ, hi, sub_self, zero_div]⟩

lemma radialSimplex_fixed {n : ℕ} (x : (simplexPair (n+1)).sub)
    (hx : x ≠ oppositeFaceBarycenter n) (hm : tailMin x.val = 0) :
    radialSimplex x hx = x.val := by
  apply Convexity.StdSimplex.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radialDen, hm]
  · simp [radialDen, hm]

lemma radialSimplex_ne_vertex {n : ℕ} (x : (simplexPair (n+1)).sub)
    (hx : x ≠ oppositeFaceBarycenter n) (hv : x ≠ simplexBoundaryVertex n) :
    radialSimplex x hx ≠ (simplexBoundaryVertex n).val := by
  intro he
  obtain ⟨i, hi⟩ := x.property
  refine Fin.cases ?_ (fun j hj => ?_) i hi
  · intro h0
    have he0 := congrArg (fun y : simplex (n+1) => y.weights 0) he
    rw [radialSimplex_weight_zero, h0, zero_div] at he0
    simp [simplexBoundaryVertex] at he0
  · have hm : tailMin x.val = 0 := (tailMin_zero_iff x.val).mpr ⟨j, hj⟩
    rw [radialSimplex_fixed x hx hm] at he
    exact hv (Subtype.ext he)

/-- Radial projection in the opposite-face direction lands in the punctured side faces. -/
def simplexOverlapToSide (n : ℕ) :
    C((simplexBoundaryFaceCover n).intersectionPair.space, simplexBoundarySide n) where
  toFun x :=
    ⟨⟨radialSimplex x.val x.property.2, by
      obtain ⟨i, hi⟩ := radialSimplex_tail_zero x.val x.property.2
      exact ⟨i.succ, hi⟩⟩,
      radialSimplex_tail_zero x.val x.property.2, by
        intro h
        exact radialSimplex_ne_vertex x.val x.property.2 x.property.1
          (congrArg Subtype.val h)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff]
    apply continuous_pi
    intro i
    have htail : Continuous (fun x : (simplexBoundaryFaceCover n).intersectionPair.space =>
        tailMin x.val.val) :=
      (tailMin_continuous n).comp (continuous_subtype_val.comp continuous_subtype_val)
    have hw (j : Fin (n+2)) : Continuous
        (fun x : (simplexBoundaryFaceCover n).intersectionPair.space => x.val.val.weights j) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ j).comp
        (continuous_subtype_val.comp continuous_subtype_val)
    have hd : Continuous (fun x : (simplexBoundaryFaceCover n).intersectionPair.space =>
        radialDen x.val.val) := continuous_const.sub (continuous_const.mul htail)
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (hw 0).div hd (fun x => (radialDen_pos x.val x.property.2).ne')
    · exact ((hw j.succ).sub htail).div hd (fun x => (radialDen_pos x.val x.property.2).ne')

end SimplexGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
namespace SimplexGeometry


lemma simplexBoundarySide_head_lt_one (n : ℕ) (x : simplexBoundarySide n) :
    x.val.val.weights 0 < 1 := by
  have hs := x.val.val.total_of_fintype
  change (∑ i : Fin (n+2), x.val.val.weights i) = 1 at hs
  rw [Fin.sum_univ_succ] at hs
  have hnn : 0 ≤ ∑ i : Fin (n+1), x.val.val.weights i.succ :=
    Finset.sum_nonneg (fun i _ => x.val.val.weights_nonneg i.succ)
  have hle : x.val.val.weights 0 ≤ 1 := by linarith
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  exfalso
  apply x.property.2
  apply Subtype.ext
  have hz : ∀ i : Fin (n+1), x.val.val.weights i.succ = 0 := by
    have hsum : ∑ i : Fin (n+1), x.val.val.weights i.succ = 0 := by linarith
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => x.val.val.weights_nonneg i.succ)).mp hsum i (by simp)
  apply Convexity.StdSimplex.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [simplexBoundaryVertex] using h
  · simpa [simplexBoundaryVertex] using hz j

/-- Normalize all coordinates except the distinguished vertex. -/
def simplexBoundaryTail (n : ℕ) (x : simplexBoundarySide n) : simplex n where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i : Fin (n+1) => x.val.val.weights i.succ / (1 - x.val.val.weights 0))
  nonneg := by
    intro i
    exact div_nonneg (x.val.val.weights_nonneg i.succ)
      (sub_pos.mpr (simplexBoundarySide_head_lt_one n x)).le
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ i : Fin (n+1), x.val.val.weights i.succ / (1 - x.val.val.weights 0)) = 1
    rw [← Finset.sum_div]
    have hs := x.val.val.total_of_fintype
    change (∑ i : Fin (n+2), x.val.val.weights i) = 1 at hs
    rw [Fin.sum_univ_succ] at hs
    have he : (∑ i : Fin (n+1), x.val.val.weights i.succ) = 1 - x.val.val.weights 0 := by linarith
    rw [he]
    exact div_self (ne_of_gt (sub_pos.mpr (simplexBoundarySide_head_lt_one n x)))

@[simp] lemma simplexBoundaryTail_weight (n : ℕ) (x : simplexBoundarySide n) (i : Fin (n+1)) :
    (simplexBoundaryTail n x).weights i =
      x.val.val.weights i.succ / (1 - x.val.val.weights 0) := rfl

/-- Tail normalization lands in the actual lower simplex boundary. -/
def simplexBoundaryTailMap (n : ℕ) : C(simplexBoundarySide n, (simplexPair n).sub) where
  toFun x := ⟨simplexBoundaryTail n x, by
    obtain ⟨i, hi⟩ := x.property.1
    exact ⟨i, by simp [hi]⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff]
    unfold Function.comp
    apply continuous_pi
    intro i
    change Continuous (fun x : simplexBoundarySide n =>
      x.val.val.weights i.succ / (1 - x.val.val.weights 0))
    apply Continuous.div
    · exact (Convexity.StdSimplex.continuous_weights_apply ℝ i.succ).comp
        (continuous_subtype_val.comp continuous_subtype_val)
    · exact continuous_const.sub ((Convexity.StdSimplex.continuous_weights_apply ℝ 0).comp
        (continuous_subtype_val.comp continuous_subtype_val))
    · intro x
      exact ne_of_gt (sub_pos.mpr (simplexBoundarySide_head_lt_one n x))

lemma simplexBoundaryTailMap_face (n : ℕ) (y : (simplexPair n).sub) :
    simplexBoundaryTailMap n (simplexBoundarySideFace n y) = y := by
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  ext i
  change (boundaryFace (0 : Fin (n+2)) y.val).val.weights i.succ /
    (1 - (boundaryFace (0 : Fin (n+2)) y.val).val.weights 0) = y.val.weights i
  rw [boundaryFace_zero_weight, boundaryFace_zero_weight_succ]
  simp


/-- Move a side point linearly toward its normalized tail. -/
def simplexBoundarySideDeform (n : ℕ) (tx : unitInterval × simplexBoundarySide n) :
    simplexBoundarySide n := by
  let z := Convexity.convexCombPair (R := ℝ) (X := Convexity.StdSimplex ℝ (Fin (n+2)))
    (unitInterval.symm tx.1) tx.1 (unitInterval.nonneg _) (unitInterval.nonneg _)
    (by simp) tx.2.val.val
    (simplexBoundarySideFace n (simplexBoundaryTailMap n tx.2)).val.val
  have hw (i : Fin (n+2)) : z.weights i =
      (1 - (tx.1 : ℝ)) * tx.2.val.val.weights i +
      (tx.1 : ℝ) * (simplexBoundarySideFace n (simplexBoundaryTailMap n tx.2)).val.val.weights i := by
    simp [z, Convexity.StdSimplex.weights_convexCombPair, unitInterval.coe_symm_eq]
  have hz : ∃ i : Fin (n+1), z.weights i.succ = 0 := by
    obtain ⟨i, hi⟩ := tx.2.property.1
    refine ⟨i, ?_⟩
    rw [hw]
    change (1 - (tx.1 : ℝ)) * tx.2.val.val.weights i.succ +
      (tx.1 : ℝ) * (boundaryFace (0 : Fin (n+2)) (simplexBoundaryTail n tx.2)).val.weights i.succ = 0
    rw [boundaryFace_zero_weight_succ, simplexBoundaryTail_weight, hi]
    simp
  have hhead : z.weights 0 < 1 := by
    rw [hw]
    change (1 - (tx.1 : ℝ)) * tx.2.val.val.weights 0 +
      (tx.1 : ℝ) * (boundaryFace (0 : Fin (n+2)) (simplexBoundaryTail n tx.2)).val.weights 0 < 1
    rw [boundaryFace_zero_weight]
    have hlt := simplexBoundarySide_head_lt_one n tx.2
    have hpos := mul_nonneg (unitInterval.nonneg tx.1) (tx.2.val.val.weights_nonneg 0)
    nlinarith
  refine ⟨⟨z, ?_⟩, hz, ?_⟩
  · obtain ⟨i, hi⟩ := hz
    exact ⟨i.succ, hi⟩
  · intro he
    have hh := congrArg (fun y : (simplexPair (n+1)).sub => y.val.weights 0) he
    change z.weights 0 = (Convexity.StdSimplex.single (0 : Fin (n+2))).weights 0 at hh
    simp only [Convexity.StdSimplex.weights_single, Finsupp.single_eq_same] at hh
    linarith

lemma simplexBoundarySideDeform_continuous (n : ℕ) :
    Continuous (simplexBoundarySideDeform n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff]
  unfold Function.comp
  apply continuous_pi
  intro i
  change Continuous (fun tx : unitInterval × simplexBoundarySide n =>
    (Convexity.convexCombPair (R := ℝ) (X := Convexity.StdSimplex ℝ (Fin (n+2)))
      (unitInterval.symm tx.1) tx.1 (unitInterval.nonneg _) (unitInterval.nonneg _)
      (by simp) tx.2.val.val
      (simplexBoundarySideFace n (simplexBoundaryTailMap n tx.2)).val.val).weights i)
  simp only [unitInterval.coe_symm_eq, Convexity.StdSimplex.weights_convexCombPair,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hx : Continuous (fun tx : unitInterval × simplexBoundarySide n => tx.2.val.val.weights i) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  have hy : Continuous (fun tx : unitInterval × simplexBoundarySide n =>
      (simplexBoundarySideFace n (simplexBoundaryTailMap n tx.2)).val.val.weights i) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp
        ((simplexBoundarySideFace n).continuous.comp
          ((simplexBoundaryTailMap n).continuous.comp continuous_snd))))
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hx).add
    ((continuous_subtype_val.comp continuous_fst).mul hy)

/-- Normalization is a deformation retraction onto the lower simplex boundary. -/
def simplexBoundarySideHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (simplexBoundarySide n) ((simplexPair n).sub) where
  toFun := simplexBoundaryTailMap n
  invFun := simplexBoundarySideFace n
  left_inv := ⟨{
    toFun := fun tx => simplexBoundarySideDeform n (unitInterval.symm tx.1, tx.2)
    continuous_toFun := (simplexBoundarySideDeform_continuous n).comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      dsimp only [simplexBoundarySideDeform]
      change Convexity.convexCombPair (R := ℝ) (X := Convexity.StdSimplex ℝ (Fin (n+2))) _ _ _ _ _ _ _ = _
      simp
    map_one_left := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      dsimp only [simplexBoundarySideDeform]
      change Convexity.convexCombPair (R := ℝ) (X := Convexity.StdSimplex ℝ (Fin (n+2))) _ _ _ _ _ _ _ = _
      simp }⟩
  right_inv := by
    have he : (simplexBoundaryTailMap n).comp (simplexBoundarySideFace n) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact simplexBoundaryTailMap_face n x
    rw [he]



lemma simplexBoundary_head_lt_one (n : ℕ) (x : (simplexPair (n+1)).sub)
    (hx : x ≠ simplexBoundaryVertex n) : x.val.weights 0 < 1 := by
  have hs := x.val.total_of_fintype
  change (∑ i : Fin (n+2), x.val.weights i) = 1 at hs
  rw [Fin.sum_univ_succ] at hs
  have hnn : 0 ≤ ∑ i : Fin (n+1), x.val.weights i.succ :=
    Finset.sum_nonneg (fun i _ => x.val.weights_nonneg i.succ)
  have hle : x.val.weights 0 ≤ 1 := by linarith
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  exfalso
  apply hx
  apply Subtype.ext
  have hz : ∀ i : Fin (n+1), x.val.weights i.succ = 0 := by
    have hsum : ∑ i : Fin (n+1), x.val.weights i.succ = 0 := by linarith
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => x.val.weights_nonneg i.succ)).mp hsum i (by simp)
  apply Convexity.StdSimplex.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [simplexBoundaryVertex] using h
  · simpa [simplexBoundaryVertex] using hz j

lemma radialSimplex_preserves_zero {n : ℕ} (x : (simplexPair (n+1)).sub)
    (hx : x ≠ oppositeFaceBarycenter n) (i : Fin (n+2)) (hi : x.val.weights i = 0) :
    (radialSimplex x hx).weights i = 0 := by
  refine Fin.cases ?_ (fun j hj => ?_) i hi
  · intro h0
    rw [radialSimplex_weight_zero, h0, zero_div]
  · have hm : tailMin x.val = 0 := (tailMin_zero_iff x.val).mpr ⟨j, hj⟩
    rw [radialSimplex_fixed x hx hm]
    exact hj

/-- A convex interpolation between the radial projection and the original point. -/
def simplexOverlapDeform (n : ℕ)
    (tx : unitInterval × (simplexBoundaryFaceCover n).intersectionPair.space) :
    (simplexBoundaryFaceCover n).intersectionPair.space := by
  let r := simplexOverlapToSide n tx.2
  let z := Convexity.convexCombPair (R := ℝ) (X := Convexity.StdSimplex ℝ (Fin (n+2)))
    (unitInterval.symm tx.1) tx.1 (unitInterval.nonneg _) (unitInterval.nonneg _)
    (by simp) r.val.val tx.2.val.val
  have hw (i : Fin (n+2)) : z.weights i =
      (1 - (tx.1 : ℝ)) * r.val.val.weights i + (tx.1 : ℝ) * tx.2.val.val.weights i := by
    simp [z, Convexity.StdSimplex.weights_convexCombPair, unitInterval.coe_symm_eq]
  have hb : ∃ i : Fin (n+2), z.weights i = 0 := by
    obtain ⟨i, hi⟩ := tx.2.val.property
    refine ⟨i, ?_⟩
    rw [hw]
    have hr : r.val.val.weights i = 0 := radialSimplex_preserves_zero tx.2.val tx.2.property.2 i hi
    rw [hi, hr]
    simp
  have hhead : z.weights 0 < 1 := by
    rw [hw]
    have hx := simplexBoundary_head_lt_one n tx.2.val tx.2.property.1
    have hr := simplexBoundary_head_lt_one n r.val r.property.2
    have hm : max (r.val.val.weights 0) (tx.2.val.val.weights 0) < 1 := max_lt hr hx
    have h₁ := mul_nonneg (unitInterval.nonneg tx.1)
      (sub_nonneg.mpr (le_max_right (r.val.val.weights 0) (tx.2.val.val.weights 0)))
    have h₂ := mul_nonneg (sub_nonneg.mpr (unitInterval.le_one tx.1))
      (sub_nonneg.mpr (le_max_left (r.val.val.weights 0) (tx.2.val.val.weights 0)))
    nlinarith
  refine ⟨⟨z, hb⟩, ?_, ?_⟩
  · intro he
    have hh := congrArg (fun y : (simplexPair (n+1)).sub => y.val.weights 0) he
    change z.weights 0 = (Convexity.StdSimplex.single (0 : Fin (n+2))).weights 0 at hh
    simp only [Convexity.StdSimplex.weights_single, Finsupp.single_eq_same] at hh
    linarith
  · intro he
    obtain ⟨i, hi⟩ := tailMin_attained tx.2.val.val
    have hr : r.val.val.weights i.succ = 0 := by
      change (radialSimplex tx.2.val tx.2.property.2).weights i.succ = 0
      rw [radialSimplex_weight_succ, hi, sub_self, zero_div]
    have hmin : tailMin tx.2.val.val < (n+1 : ℝ)⁻¹ := by
      rw [← one_div]
      apply (lt_div_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr
      have hd := radialDen_pos tx.2.val tx.2.property.2
      dsimp [radialDen] at hd
      nlinarith
    have hmul : (tx.1 : ℝ) * tailMin tx.2.val.val ≤ tailMin tx.2.val.val := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (unitInterval.le_one tx.1)) (tailMin_nonneg tx.2.val.val)]
    have he' := congrArg (fun y : (simplexPair (n+1)).sub => y.val.weights i.succ) he
    change z.weights i.succ = (oppositeFaceBarycenter n).val.weights i.succ at he'
    rw [hw, hr, hi, oppositeFaceBarycenter_weight_succ] at he'
    linarith

lemma simplexOverlapDeform_continuous (n : ℕ) : Continuous (simplexOverlapDeform n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff]
  unfold Function.comp
  apply continuous_pi
  intro i
  change Continuous (fun tx : unitInterval × (simplexBoundaryFaceCover n).intersectionPair.space =>
    (Convexity.convexCombPair (R := ℝ) (X := Convexity.StdSimplex ℝ (Fin (n+2)))
      (unitInterval.symm tx.1) tx.1 (unitInterval.nonneg _) (unitInterval.nonneg _)
      (by simp) (simplexOverlapToSide n tx.2).val.val tx.2.val.val).weights i)
  simp only [unitInterval.coe_symm_eq, Convexity.StdSimplex.weights_convexCombPair,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hx : Continuous (fun tx : unitInterval × (simplexBoundaryFaceCover n).intersectionPair.space =>
      tx.2.val.val.weights i) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  have hr : Continuous (fun tx : unitInterval × (simplexBoundaryFaceCover n).intersectionPair.space =>
      (simplexOverlapToSide n tx.2).val.val.weights i) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp
        ((simplexOverlapToSide n).continuous.comp continuous_snd)))
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hr).add
    ((continuous_subtype_val.comp continuous_fst).mul hx)

lemma simplexOverlapToSide_inclusion (n : ℕ) (y : simplexBoundarySide n) :
    simplexOverlapToSide n (simplexBoundarySideToOverlap n y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  change radialSimplex (simplexBoundarySideToOverlap n y).val
    (simplexBoundarySideToOverlap n y).property.2 = y.val.val
  exact radialSimplex_fixed (simplexBoundarySideToOverlap n y).val
    (simplexBoundarySideToOverlap n y).property.2
    ((tailMin_zero_iff y.val.val).mpr y.property.1)

/-- The radial projection retracts the open intersection onto the punctured side faces. -/
def simplexOverlapSideHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv ((simplexBoundaryFaceCover n).intersectionPair.space)
      (simplexBoundarySide n) where
  toFun := simplexOverlapToSide n
  invFun := simplexBoundarySideToOverlap n
  left_inv := ⟨{
    toFun := simplexOverlapDeform n
    continuous_toFun := simplexOverlapDeform_continuous n
    map_zero_left := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      dsimp only [simplexOverlapDeform]
      change Convexity.convexCombPair (R := ℝ) (X := Convexity.StdSimplex ℝ (Fin (n+2))) _ _ _ _ _ _ _ = _
      simp [simplexBoundarySideToOverlap]
    map_one_left := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      dsimp only [simplexOverlapDeform]
      change Convexity.convexCombPair (R := ℝ) (X := Convexity.StdSimplex ℝ (Fin (n+2))) _ _ _ _ _ _ _ = _
      simp }⟩
  right_inv := by
    have he : (simplexOverlapToSide n).comp (simplexBoundarySideToOverlap n) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact simplexOverlapToSide_inclusion n x
    rw [he]


def simplexOverlapBoundaryHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv ((simplexBoundaryFaceCover n).intersectionPair.space)
      ((simplexPair n).sub) :=
  (simplexOverlapSideHomotopyEquiv n).trans (simplexBoundarySideHomotopyEquiv n)

lemma simplexOverlapBoundaryHomotopyEquiv_invFun (n : ℕ) :
    (simplexOverlapBoundaryHomotopyEquiv n).invFun = simplexBoundaryFaceToOverlap n := rfl

end SimplexGeometry

namespace SimplexGeometry
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
open CategoryTheory

def simplexBoundaryFaceReducedIso (n : ℕ) (j : ℤ) :
    reducedHomology R M (simplexPair n).sub j ≅
      reducedHomology R M (simplexBoundaryFaceCover n).intersectionPair.space j :=
  reducedHomologyIsoOfHomotopyEquiv R M
    (simplexOverlapBoundaryHomotopyEquiv n).symm j

lemma simplexBoundaryFaceReducedIso_hom (n : ℕ) (j : ℤ) :
    (simplexBoundaryFaceReducedIso R M n j).hom =
      (reducedHomologyFunctor R M j).map (TopCat.ofHom (simplexBoundaryFaceToOverlap n)) := rfl

instance simplexBoundaryFaceToOverlap_reduced_isIso (n : ℕ) (j : ℤ) :
    IsIso ((reducedHomologyFunctor R M j).map (TopCat.ofHom (simplexBoundaryFaceToOverlap n))) := by
  rw [← simplexBoundaryFaceReducedIso_hom]
  infer_instance

end SimplexGeometry

namespace SimplexOrientation
open P202Specs.MayerVietoris P202Specs.RelativeSingularChains

/-- The boundary formula needs only the left boundary equation when the overlap
inclusion is injective. Existence of the other equation and the cycle condition
comes from the actual Mayer–Vietoris boundary lift theorem. -/
lemma mv_formula_of_left_boundary
    {R : Type u} [CommRing R]
    (F : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ)
    (δ : Connecting.{u,v,w} F)
    (hlift : BoundaryLifts.{u,v,w} F) (hformula : BoundaryFormula F δ)
    (C : CoverPair.{v,w}) (n : ℤ) (c : (middle F C).X (n+1))
    (hc : (F.obj C.pair).d (n+1) n ((chainSum F C).f (n+1) c) = 0)
    (x : (F.obj C.intersectionPair).X n)
    (hinj : Function.Injective ((F.map C.toLeft).f n))
    (hx : (F.map C.toLeft).f n x =
      (biprod.fst : middle F C ⟶ F.obj C.leftPair).f n
        ((middle F C).d (n+1) n c)) :
    ∃ hxc : (F.obj C.intersectionPair).d n (n-1) x = 0,
      δ C n (P202Specs.MayerVietoris.classOf (F.obj C.pair) (n+1)
        ((chainSum F C).f (n+1) c) (by rw [add_sub_cancel_right]; exact hc)) =
      P202Specs.MayerVietoris.classOf (F.obj C.intersectionPair) n x hxc := by
  obtain ⟨x', ⟨hx', hxc⟩, _⟩ := hlift C n c hc
  have hfirst : chainFirst F C ≫ (biprod.fst : middle F C ⟶ F.obj C.leftPair) =
      F.map C.toLeft := by simp [chainFirst]
  have hxleft : (F.map C.toLeft).f n x' =
      (biprod.fst : middle F C ⟶ F.obj C.leftPair).f n
        ((middle F C).d (n+1) n c) := by
    calc
      _ = (biprod.fst : middle F C ⟶ F.obj C.leftPair).f n
          ((chainFirst F C).f n x') :=
        (congrArg (fun f => f.f n x') hfirst).symm
      _ = _ := congrArg (fun z =>
        (biprod.fst : middle F C ⟶ F.obj C.leftPair).f n z) hx'
  have heq : x' = x := hinj (hxleft.trans hx.symm)
  subst x'
  exact ⟨hxc, hformula C n c hc x hx' hxc⟩

/-- Split chains in the direct sum use the actual degreewise biproduct maps. -/
def splitChain {R : Type u} [CommRing R]
    (F : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ)
    (C : CoverPair.{v,w}) (n : ℤ)
    (a : (F.obj C.leftPair).X n) (b : (F.obj C.rightPair).X n) : (middle F C).X n :=
  (biprod.inl : F.obj C.leftPair ⟶ middle F C).f n a +
    (biprod.inr : F.obj C.rightPair ⟶ middle F C).f n b

lemma chainSum_splitChain {R : Type u} [CommRing R]
    (F : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ)
    (C : CoverPair.{v,w}) (n : ℤ)
    (a : (F.obj C.leftPair).X n) (b : (F.obj C.rightPair).X n) :
    (chainSum F C).f n (splitChain F C n a b) =
      (F.map C.leftInclusion).f n a + (F.map C.rightInclusion).f n b := by
  simp only [splitChain, map_add]
  congr 1
  · exact congrArg (fun f => f.f n a) (biprod.inl_desc (F.map C.leftInclusion)
      (F.map C.rightInclusion))
  · exact congrArg (fun f => f.f n b) (biprod.inr_desc (F.map C.leftInclusion)
      (F.map C.rightInclusion))

lemma splitChain_left {R : Type u} [CommRing R]
    (F : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ)
    (C : CoverPair.{v,w}) (n : ℤ)
    (a : (F.obj C.leftPair).X n) (b : (F.obj C.rightPair).X n) :
    (biprod.fst : middle F C ⟶ F.obj C.leftPair).f n (splitChain F C n a b) = a := by
  simp only [splitChain, map_add, ← ModuleCat.comp_apply,
    biprod_inl_fst_f, biprod_inr_fst_f]
  simp

lemma splitChain_left_boundary {R : Type u} [CommRing R]
    (F : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ)
    (C : CoverPair.{v,w}) (n k : ℤ)
    (a : (F.obj C.leftPair).X n) (b : (F.obj C.rightPair).X n) :
    (biprod.fst : middle F C ⟶ F.obj C.leftPair).f k
      ((middle F C).d n k (splitChain F C n a b)) =
      (F.obj C.leftPair).d n k a := by
  calc
    _ = (F.obj C.leftPair).d n k
        ((biprod.fst : middle F C ⟶ F.obj C.leftPair).f n
          (splitChain F C n a b)) := congrArg (fun f => f (splitChain F C n a b))
      ((biprod.fst : middle F C ⟶ F.obj C.leftPair).comm n k).symm
    _ = _ := congrArg ((F.obj C.leftPair).d n k) (splitChain_left F C n a b)

lemma reduced_overlap_to_left_injective (R : Type u) [CommRing R]
    (C : CoverPair.{v,w}) (n : ℤ) :
    Function.Injective (((theoryFunctor R .reduced).map C.toLeft).f n) := by
  let F := theoryFunctor R .reduced
  have hm : Mono (F.map (pieceInclusion C.pair (C.left ∩ C.right))) := by
    change Mono (inclusion (P202Specs.SingularChains.reducedFunctor R R)
      ⟨C.pair.space, C.left ∩ C.right⟩)
    infer_instance
  have hfac : F.map C.toLeft ≫ F.map C.leftInclusion =
      F.map (pieceInclusion C.pair (C.left ∩ C.right)) := by
    rw [← F.map_comp]
    rfl
  have : Mono (F.map C.toLeft) := mono_of_mono_fac hfac
  exact (ModuleCat.mono_iff_injective ((F.map C.toLeft).f n)).mp inferInstance
end SimplexOrientation

namespace SimplexOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
open P202Specs.MayerVietoris P202.SpheresDisks.SimplexGeometry

def oppositeFaceLeftMap (n : ℕ) :
    simplex n ⟶ (simplexBoundaryFaceCover n).leftPair.space :=
  TopCat.ofHom ⟨fun x => ⟨boundaryFace 0 x, boundaryFace_zero_mem_left n x⟩,
    (boundaryFace 0).continuous.subtype_mk _⟩

def sideFaceRightMap (n : ℕ) (i : Fin (n+1)) :
    simplex n ⟶ (simplexBoundaryFaceCover n).rightPair.space :=
  TopCat.ofHom ⟨fun x => ⟨boundaryFace i.succ x, boundaryFace_succ_mem_right n i x⟩,
    (boundaryFace i.succ).continuous.subtype_mk _⟩

def oppositeFaceLeftSimplex (n : ℕ) :
    Simplex (simplexBoundaryFaceCover n).leftPair.space n :=
  (simplexEquiv _ n).symm (oppositeFaceLeftMap n).hom

def sideFaceRightSimplex (n : ℕ) (i : Fin (n+1)) :
    Simplex (simplexBoundaryFaceCover n).rightPair.space n :=
  (simplexEquiv _ n).symm (sideFaceRightMap n i).hom


def oppositeFaceLeftChain (n : ℕ) (m : M) :
    Chains M (simplexBoundaryFaceCover n).leftPair.space n :=
  Finsupp.single (oppositeFaceLeftSimplex n) m

def sideFacesRightChain (n : ℕ) (m : M) :
    Chains M (simplexBoundaryFaceCover n).rightPair.space n :=
  ∑ i : Fin (n+1), (-1 : ℤ) ^ i.succ.val • Finsupp.single (sideFaceRightSimplex n i) m

lemma oppositeFaceLeftChain_image (n : ℕ) (m : M) :
    (chainMap R M (simplexBoundaryFaceCover n).leftInclusion.map).f n
      (oppositeFaceLeftChain M n m) = Finsupp.single (boundarySimplex 0) m := by
  rw [oppositeFaceLeftChain, P202.SingularChains.chainMap_single]
  congr 1

lemma sideFacesRightChain_image (n : ℕ) (m : M) :
    (chainMap R M (simplexBoundaryFaceCover n).rightInclusion.map).f n
      (sideFacesRightChain M n m) =
      ∑ i : Fin (n+1), (-1 : ℤ) ^ i.succ.val •
        Finsupp.single (boundarySimplex i.succ) m := by
  simp only [sideFacesRightChain, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [P202.SingularChains.chainMap_single]
  congr 1

lemma orientedBoundary_face_split (n : ℕ) (m : M) :
    (chainMap R M (simplexBoundaryFaceCover n).leftInclusion.map).f n
        (oppositeFaceLeftChain M n m) +
      (chainMap R M (simplexBoundaryFaceCover n).rightInclusion.map).f n
        (sideFacesRightChain M n m) = orientedBoundary M n m := by
  rw [oppositeFaceLeftChain_image, sideFacesRightChain_image]
  unfold orientedBoundary
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul]
end SimplexOrientation

namespace SimplexOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks

def reducedAffineChainZ (n : ℕ) (m : R) :
    (reducedComplex R R (simplex n)).X (n : ℤ) :=
  (reducedNonnegativeIso R R (simplex n) n).inv (affineChain R n m)

def reducedRelativeAffineChain (n : ℕ) (m : R) :
    (reduced R R (simplexPair n)).X (n : ℤ) :=
  (projection (reducedFunctor R R) (simplexPair n)).f (n : ℤ)
    (reducedAffineChainZ R n m)

lemma canonical_relative_iso_affine (n : ℕ) (m : R) :
    (P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair n)).hom.f (n : ℤ)
      (reducedRelativeAffineChain R n m) = relativeAffineChain R R n m := by
  apply (ordinaryDegreeIso R R (simplexPair n) n).toLinearEquiv.injective
  have hcomp :
      (P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair n)).hom.f (n : ℤ) ≫
        (ordinaryDegreeIso R R (simplexPair n) n).hom =
      (reducedDegreeIso R R (simplexPair n) n).hom := by
    change ((reducedDegreeIso R R (simplexPair n) n).hom ≫
      (ordinaryDegreeIso R R (simplexPair n) n).inv) ≫ _ = _
    simp
  change (ordinaryDegreeIso R R (simplexPair n) n).hom
    ((P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair n)).hom.f (n : ℤ)
      (reducedRelativeAffineChain R n m)) =
    (ordinaryDegreeIso R R (simplexPair n) n).hom (relativeAffineChain R R n m)
  rw [← ModuleCat.comp_apply, hcomp]
  unfold reducedRelativeAffineChain relativeAffineChain
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    P202.RelativeSingularChains.reduced_degree,
    P202.RelativeSingularChains.ordinary_degree]
  simp only [reducedAffineChainZ, affineChainZ]
  change (projection (chainFunctor R R) (simplexPair n)).f n
    ((reducedNonnegativeIso R R (simplex n) n).hom
      ((reducedNonnegativeIso R R (simplex n) n).inv (affineChain R n m))) =
    (projection (chainFunctor R R) (simplexPair n)).f n
      ((ordinaryNonnegativeIso R R (simplex n) n).hom
        ((ordinaryNonnegativeIso R R (simplex n) n).inv (affineChain R n m)))
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ← ModuleCat.comp_apply, Iso.inv_hom_id]

lemma reducedRelativeAffineChain_cycle (n : ℕ) (m : R) :
    (reduced R R (simplexPair n)).d (n : ℤ) ((n : ℤ)-1)
      (reducedRelativeAffineChain R n m) = 0 := by
  let e := P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair n)
  apply (ModuleCat.mono_iff_injective (e.hom.f ((n : ℤ)-1))).mp inferInstance
  rw [map_zero]
  have hcomm := congrArg (fun f => f (reducedRelativeAffineChain R n m))
    (e.hom.comm (n : ℤ) ((n : ℤ)-1))
  simp only [ModuleCat.comp_apply] at hcomm
  rw [← hcomm]
  change (ordinary R R (simplexPair n)).d (n : ℤ) ((n : ℤ)-1)
    (e.hom.f (n : ℤ) (reducedRelativeAffineChain R n m)) = 0
  rw [canonical_relative_iso_affine]
  exact relativeAffineChain_cycle R R n m

/-- The canonical reduced/ordinary comparison preserves the displayed affine
chain, so its inverse preserves its actual homology class with no unit ambiguity. -/
lemma canonical_relative_iso_affineClass (n : ℕ) (m : R) :
    homologyMap (P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair n)).inv
      (n : ℤ)
      (classOf R (ordinary R R (simplexPair n)) (n : ℤ)
        (relativeAffineChain R R n m) (relativeAffineChain_cycle R R n m)) =
    classOf R (reduced R R (simplexPair n)) (n : ℤ)
      (reducedRelativeAffineChain R n m) (reducedRelativeAffineChain_cycle R n m) := by
  let e := P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair n)
  have himage : e.inv.f (n : ℤ) (relativeAffineChain R R n m) =
      reducedRelativeAffineChain R n m := by
    apply (ModuleCat.mono_iff_injective (e.hom.f (n : ℤ))).mp inferInstance
    rw [← ModuleCat.comp_apply]
    have hid := congrArg (fun f => f.f (n : ℤ)) e.inv_hom_id
    change e.inv.f (n : ℤ) ≫ e.hom.f (n : ℤ) = 𝟙 _ at hid
    rw [hid]
    exact (canonical_relative_iso_affine R n m).symm
  have hcycle : (reduced R R (simplexPair n)).d (n : ℤ) ((n : ℤ)-1)
      (e.inv.f (n : ℤ) (relativeAffineChain R R n m)) = 0 := by
    rw [himage]
    exact reducedRelativeAffineChain_cycle R n m
  have h := P202.MayerVietoris.classOf_map e.inv (n : ℤ)
    (relativeAffineChain R R n m) (relativeAffineChain_cycle R R n m) hcycle
  change homologyMap e.inv (n : ℤ) _ = _
  change homologyMap e.inv (n : ℤ)
    (classOf R (ordinary R R (simplexPair n)) (n : ℤ)
      (relativeAffineChain R R n m) (relativeAffineChain_cycle R R n m)) =
    classOf R (reduced R R (simplexPair n)) (n : ℤ)
      (e.inv.f (n : ℤ) (relativeAffineChain R R n m)) hcycle at h
  simpa only [himage] using h

def reducedOrientedBoundaryZ (n : ℕ) (m : R) :
    (reducedComplex R R (simplexPair (n+1)).sub).X (n : ℤ) :=
  (reducedNonnegativeIso R R (simplexPair (n+1)).sub n).inv (orientedBoundary R n m)

lemma inclusion_reducedOrientedBoundaryZ (n : ℕ) (m : R) :
    (inclusion (reducedFunctor R R) (simplexPair (n+1))).f (n : ℤ)
        (reducedOrientedBoundaryZ R n m) =
      (reducedComplex R R (simplex (n+1))).d ((n+1 : ℕ) : ℤ) (n : ℤ)
        (reducedAffineChainZ R (n+1) m) := by
  apply (reducedNonnegativeIso R R (simplex (n+1)) n).toLinearEquiv.injective
  have h₁ := congrArg
    (fun f => (reducedNonnegativeIso R R (simplexPair (n+1)).sub n).inv ≫ f)
    (reduced_inclusion_degree R R (simplexPair (n+1)) n)
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h₁
  have h₂ := congrArg (fun f => f (affineChain R (n+1) m))
    (P202.SingularChains.reduced_boundary R R (simplex (n+1)) n)
  have h₁' : (reducedNonnegativeIso R R (simplex (n+1)) n).hom
      ((inclusion (reducedFunctor R R) (simplexPair (n+1))).f (n : ℤ)
        (reducedOrientedBoundaryZ R n m)) =
      ((chainMap R R (simplexPair (n+1)).inclusion).f n) (orientedBoundary R n m) := by
    exact congrArg (fun f => f (orientedBoundary R n m)) h₁
  exact h₁'.trans ((inclusion_orientedBoundary R R n m).trans h₂.symm)

/-- The signed boundary is a cycle in the boundary subspace. -/
lemma reducedOrientedBoundaryZ_cycle (n : ℕ) (m : R) :
    (reducedComplex R R (simplexPair (n+1)).sub).d (n : ℤ) ((n : ℤ)-1)
      (reducedOrientedBoundaryZ R n m) = 0 := by
  let f := inclusion (reducedFunctor R R) (simplexPair (n+1))
  apply (ModuleCat.mono_iff_injective (f.f ((n : ℤ)-1))).mp inferInstance
  rw [map_zero]
  have hc := congrArg (fun g => g (reducedOrientedBoundaryZ R n m))
    (f.comm (n : ℤ) ((n : ℤ)-1))
  change (f.f ((n : ℤ)-1))
    ((reducedComplex R R (simplexPair (n+1)).sub).d (n : ℤ) ((n : ℤ)-1)
      (reducedOrientedBoundaryZ R n m)) = 0
  change (reducedComplex R R (simplex (n+1))).d (n : ℤ) ((n : ℤ)-1)
      (f.f (n : ℤ) (reducedOrientedBoundaryZ R n m)) =
    f.f ((n : ℤ)-1)
      ((reducedComplex R R (simplexPair (n+1)).sub).d (n : ℤ) ((n : ℤ)-1)
        (reducedOrientedBoundaryZ R n m)) at hc
  apply hc.symm.trans
  change (reducedComplex R R (simplex (n+1))).d (n : ℤ) ((n : ℤ)-1)
    ((inclusion (reducedFunctor R R) (simplexPair (n+1))).f (n : ℤ)
      (reducedOrientedBoundaryZ R n m)) = 0
  rw [inclusion_reducedOrientedBoundaryZ]
  exact congrArg (fun g => g (reducedAffineChainZ R (n+1) m))
    ((reducedComplex R R (simplex (n+1))).d_comp_d ((n+1 : ℕ) : ℤ) (n : ℤ) ((n : ℤ)-1))



/-- Canonical positive-dimensional simplex pair shift, retaining the actual
chosen degree comparisons so the affine generator has its prescribed sign. -/
def canonicalSimplexShift (n : ℕ) :
    relativeHomology R R (simplexPair (n+1)) ((n+1 : ℕ) : ℤ) ≅
      reducedHomology R R (simplexPair (n+1)).sub (n : ℤ) := by
  let e := P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair (n+1))
  let h := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.reduced_short_exact R R (simplexPair (n+1)))
  haveI : ContractibleSpace (simplex (n+1)) := simplex_contractible (n+1)
  exact (HomologicalComplex.homologyFunctor _ _ ((n+1 : ℕ) : ℤ)).mapIso e.symm ≪≫
    h.δIso ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp)
      (P202.PrismHomotopy.contractible R R (simplex (n+1)) ((n+1 : ℕ) : ℤ))
      (P202.PrismHomotopy.contractible R R (simplex (n+1)) (n : ℤ))

lemma canonicalSimplexShift_affine (n : ℕ) (m : R) :
    (canonicalSimplexShift R n).hom
      (classOf R (ordinary R R (simplexPair (n+1))) ((n+1 : ℕ) : ℤ)
        (relativeAffineChain R R (n+1) m) (relativeAffineChain_cycle R R (n+1) m)) =
    classOf R (reducedComplex R R (simplexPair (n+1)).sub) (n : ℤ)
      (reducedOrientedBoundaryZ R n m) (reducedOrientedBoundaryZ_cycle R n m) := by
  let h := P202.RelativeSingularChains.reduced_short_exact R R (simplexPair (n+1))
  change P202Specs.ChainLES.connecting h ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp)
    (homologyMap (P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair (n+1))).inv
      ((n+1 : ℕ) : ℤ)
      (classOf R (ordinary R R (simplexPair (n+1))) ((n+1 : ℕ) : ℤ)
        (relativeAffineChain R R (n+1) m) (relativeAffineChain_cycle R R (n+1) m))) = _
  rw [canonical_relative_iso_affineClass]
  have hz : (reduced R R (simplexPair (n+1))).d ((n+1 : ℕ) : ℤ) (n : ℤ)
      (reducedRelativeAffineChain R (n+1) m) = 0 := by
    have hz := reducedRelativeAffineChain_cycle R (n+1) m
    have hn : (((n+1 : ℕ) : ℤ)-1) = (n : ℤ) := by omega
    rw [hn] at hz
    exact hz
  exact P202.ChainLES.lift_formula _ h ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp)
    (reducedRelativeAffineChain R (n+1) m) hz
    (reducedAffineChainZ R (n+1) m) rfl (reducedOrientedBoundaryZ R n m)
    (inclusion_reducedOrientedBoundaryZ R n m) (by
      change (reducedComplex R R (simplexPair (n+1)).sub).d (n : ℤ)
        ((ComplexShape.down ℤ).next (n : ℤ)) (reducedOrientedBoundaryZ R n m) = 0
      rw [(ComplexShape.down ℤ).next_eq' (show (ComplexShape.down ℤ).Rel (n : ℤ) ((n : ℤ)-1) by simp)]
      exact reducedOrientedBoundaryZ_cycle R n m)

lemma reduced_inclusion_augmentation (P : Pair.{0}) :
    (reducedAugmentationIso R R P.sub).inv ≫
      (inclusion (reducedFunctor R R) P).f (-1) ≫
        (reducedAugmentationIso R R P.space).hom = 𝟙 _ := by
  change (reducedAugmentationIso R R P.sub).inv ≫
    (HomologicalComplex.extendMap (augmentedShiftedMap R R P.inclusion)
      (degreeEmbedding (-1))).f (-1) ≫
      (reducedAugmentationIso R R P.space).hom = 𝟙 _
  rw [HomologicalComplex.extendMap_f _ _
    (show (degreeEmbedding (-1)).f 0 = (-1 : ℤ) from rfl)]
  simp [reducedAugmentationIso, augmentedShiftedMap]

def reducedBoundaryUnit (m : R) :
    (reducedComplex R R (simplexPair 0).sub).X (-1) :=
  (reducedAugmentationIso R R (simplexPair 0).sub).inv (ULift.up m)

lemma inclusion_reducedBoundaryUnit (m : R) :
    (inclusion (reducedFunctor R R) (simplexPair 0)).f (-1) (reducedBoundaryUnit R m) =
      (reducedComplex R R (simplex 0)).d 0 (-1) (reducedAffineChainZ R 0 m) := by
  apply (reducedAugmentationIso R R (simplex 0)).toLinearEquiv.injective
  change (reducedAugmentationIso R R (simplex 0)).hom
    ((inclusion (reducedFunctor R R) (simplexPair 0)).f (-1) (reducedBoundaryUnit R m)) =
    (reducedAugmentationIso R R (simplex 0)).hom
      ((reducedComplex R R (simplex 0)).d 0 (-1) (reducedAffineChainZ R 0 m))
  have hl := congrArg (fun f => f (ULift.up m))
    (reduced_inclusion_augmentation R (simplexPair 0))
  have hr := congrArg (fun f => f (affineChain R 0 m))
    (P202.SingularChains.reduced_augmentation R R (simplex 0))
  exact hl.trans ((P202.SingularChains.augmentation_single R R (simplex 0)
    (affineSimplex 0) m).symm.trans hr.symm)

lemma reducedBoundaryUnit_cycle (m : R) :
    (reducedComplex R R (simplexPair 0).sub).d (-1) (-2) (reducedBoundaryUnit R m) = 0 := by
  have h : IsZero ((reducedComplex R R (simplexPair 0).sub).X (-2)) :=
    (P202.SingularChains.reduced_below_minus_one R R (simplexPair 0).sub (-2) (by omega)).1
  have := ModuleCat.isZero_iff_subsingleton.mp h
  exact Subsingleton.elim _ _

def canonicalSimplexZeroShift :
    relativeHomology R R (simplexPair 0) 0 ≅
      reducedHomology R R (simplexPair 0).sub (-1) := by
  let e := P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair 0)
  let h := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.reduced_short_exact R R (simplexPair 0))
  haveI : ContractibleSpace (simplex 0) := simplex_contractible 0
  exact (HomologicalComplex.homologyFunctor _ _ 0).mapIso e.symm ≪≫
    h.δIso 0 (-1) (by simp)
      (P202.PrismHomotopy.contractible R R (simplex 0) 0)
      (P202.PrismHomotopy.contractible R R (simplex 0) (-1))

lemma canonicalSimplexZeroShift_affine (m : R) :
    (canonicalSimplexZeroShift R).hom
      (classOf R (ordinary R R (simplexPair 0)) 0
        (relativeAffineChain R R 0 m) (relativeAffineChain_cycle R R 0 m)) =
    classOf R (reducedComplex R R (simplexPair 0).sub) (-1)
      (reducedBoundaryUnit R m) (reducedBoundaryUnit_cycle R m) := by
  let h := P202.RelativeSingularChains.reduced_short_exact R R (simplexPair 0)
  change P202Specs.ChainLES.connecting h 0 (-1) (by simp)
    (homologyMap (P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair 0)).inv 0
      (classOf R (ordinary R R (simplexPair 0)) 0
        (relativeAffineChain R R 0 m) (relativeAffineChain_cycle R R 0 m))) = _
  have hcanon := canonical_relative_iso_affineClass R 0 m
  change homologyMap (P202.MayerVietoris.reducedOrdinaryRelativeIso R (simplexPair 0)).inv 0
    (classOf R (ordinary R R (simplexPair 0)) 0
      (relativeAffineChain R R 0 m) (relativeAffineChain_cycle R R 0 m)) =
    classOf R (reduced R R (simplexPair 0)) 0
      (reducedRelativeAffineChain R 0 m) (reducedRelativeAffineChain_cycle R 0 m) at hcanon
  rw [hcanon]
  have hz := reducedRelativeAffineChain_cycle R 0 m
  change (reduced R R (simplexPair 0)).d 0 (-1)
    (reducedRelativeAffineChain R 0 m) = 0 at hz
  exact P202.ChainLES.lift_formula _ h 0 (-1) (by simp)
    (reducedRelativeAffineChain R 0 m) hz
    (reducedAffineChainZ R 0 m) rfl (reducedBoundaryUnit R m)
    (inclusion_reducedBoundaryUnit R m) (by
      change (reducedComplex R R (simplexPair 0).sub).d (-1)
        ((ComplexShape.down ℤ).next (-1)) (reducedBoundaryUnit R m) = 0
      rw [(ComplexShape.down ℤ).next_eq' (show (ComplexShape.down ℤ).Rel (-1 : ℤ) (-2 : ℤ) by simp)]
      exact reducedBoundaryUnit_cycle R m)
end SimplexOrientation

namespace ConcentratedHomology
variable {C : Type u} [Category.{v} C] [Abelian C]

def fromSingleCycles (K : ChainComplex C ℕ) (n : ℕ) {A : C}
    (c : A ⟶ K.cycles n) : (single C (.down ℕ) n).obj A ⟶ K :=
  mkHomFromSingle (c ≫ K.iCycles n)
    (by intro k hk; rw [Category.assoc, K.iCycles_d, comp_zero])

lemma fromSingleCycles_homologyMap (K : ChainComplex C ℕ) (n : ℕ) {A : C}
    (c : A ⟶ K.cycles n) :
    homologyMap (fromSingleCycles K n c) n =
      (singleObjHomologySelfIso (.down ℕ) n A).hom ≫ c ≫ K.homologyπ n := by
  apply (cancel_epi (((single C (.down ℕ) n).obj A).homologyπ n)).mp
  rw [homologyπ_naturality, homologyπ_singleObjHomologySelfIso_hom_assoc]
  have heq : cyclesMap (fromSingleCycles K n c) n =
      (singleObjCyclesSelfIso (.down ℕ) n A).hom ≫ c := by
    apply (cancel_mono (K.iCycles n)).mp
    rw [cyclesMap_i]
    simp only [fromSingleCycles, mkHomFromSingle_f, Category.assoc,
      singleObjCyclesSelfIso_hom]
  rw [heq, Category.assoc]

lemma fromSingleCycles_quasiIso (K : ChainComplex C ℕ) (n : ℕ) {A : C}
    (c : A ⟶ K.cycles n) [IsIso (c ≫ K.homologyπ n)]
    (h : ∀ i : ℕ, i ≠ n → IsZero (K.homology i)) :
    QuasiIso (fromSingleCycles K n c) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : i = n
  · subst i
    rw [fromSingleCycles_homologyMap]
    infer_instance
  · exact (isZero_single_obj_homology (.down ℕ) n A i hi).isIso (h i hi) _

universe u' v'
variable {D : Type u'} [Category.{v'} D] [Abelian D]

lemma map_quasiIso_of_projective (F : C ⥤ D) [F.Additive]
    {K L : ChainComplex C ℕ} [∀ i, Projective (K.X i)]
    [∀ i, Projective (L.X i)] (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (.down ℕ)).map f) := by
  apply homotopyEquivalences_le_quasiIso
  exact F.homotopyEquivalences_mapHomologicalComplex_map f
    ((ChainComplex.quasiIso_iff_of_projective f).mp inferInstance)
end ConcentratedHomology

namespace IntegralCoefficients
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks

/-- The coefficient map into the canonical nonnegative relative chains. -/
def nonnegativeAffineLinear (n : ℕ) : M →ₗ[R] (nonnegative R M (simplexPair n)).X n :=
  ((projection (chainFunctor R M) (simplexPair n)).f n).hom.comp
    (Finsupp.lsingle (affineSimplex n))

/-- The same affine cycle in the nonnegative model, using the canonical extension isomorphism. -/
def nonnegativeAffineCycleMap (n : ℕ) : ModuleCat.of R M ⟶
    (nonnegative R M (simplexPair n)).cycles n :=
  affineCycleMap R M n ≫
    cyclesMap (ordinaryRelativeExtensionIso R M (simplexPair n)).hom (n : ℤ) ≫
      ((nonnegative R M (simplexPair n)).extendCyclesIso (degreeEmbedding 0)
        (j := n) (by change (0 : ℤ) + (n : ℤ) = n; omega)).hom

def nonnegativeAffineClassLinear (n : ℕ) : M →ₗ[R]
    (nonnegative R M (simplexPair n)).homology n :=
  (nonnegativeAffineCycleMap R M n ≫ (nonnegative R M (simplexPair n)).homologyπ n).hom

lemma nonnegativeAffineClassLinear_transport (n : ℕ) :
    (ordinaryRelativeHomologyIso R M (simplexPair n) n).hom.hom.comp
      (affineClassLinear R M n) = nonnegativeAffineClassLinear R M n := by
  change (affineCycleMap R M n ≫ (ordinary R M (simplexPair n)).homologyπ (n : ℤ) ≫
      (ordinaryRelativeHomologyIso R M (simplexPair n) n).hom).hom = _
  simp only [ordinaryRelativeHomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map, homologyπ_naturality_assoc,
    homologyπ_extendHomologyIso_hom, Category.assoc, nonnegativeAffineClassLinear,
    nonnegativeAffineCycleMap]

lemma nonnegativeAffineCycleMap_i (n : ℕ) :
    nonnegativeAffineCycleMap R M n ≫ (nonnegative R M (simplexPair n)).iCycles n =
      ModuleCat.ofHom (nonnegativeAffineLinear R M n) := by
  simp only [nonnegativeAffineCycleMap, Category.assoc,
    HomologicalComplex.extendCyclesIso_hom_iCycles]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  change affineCycleMap R M n ≫ (ordinary R M (simplexPair n)).iCycles (n : ℤ) ≫
    (ordinaryRelativeExtensionIso R M (simplexPair n)).hom.f (n : ℤ) ≫
      ((nonnegative R M (simplexPair n)).extendXIso (degreeEmbedding 0)
        (i := n) (by change (0 : ℤ) + (n : ℤ) = n; omega)).hom = _
  rw [← Category.assoc, affineCycleMap, HomologicalComplex.liftCycles_i]
  apply ModuleCat.hom_ext
  ext m
  have hp := congrArg (fun f => f.f (n : ℤ))
    (ordinaryRelativeExtensionIso_projection R M (simplexPair n))
  change (projection (ordinaryFunctor R M) (simplexPair n)).f (n : ℤ) ≫
    (ordinaryRelativeExtensionIso R M (simplexPair n)).hom.f (n : ℤ) =
      (HomologicalComplex.extendMap (projection (chainFunctor R M) (simplexPair n))
        (degreeEmbedding 0)).f (n : ℤ) at hp
  change ((nonnegative R M (simplexPair n)).extendXIso (degreeEmbedding 0)
      (i := n) (by change (0 : ℤ) + (n : ℤ) = n; omega)).hom
    (((ordinaryRelativeExtensionIso R M (simplexPair n)).hom.f (n : ℤ))
      ((projection (ordinaryFunctor R M) (simplexPair n)).f (n : ℤ)
        ((ordinaryNonnegativeIso R M (simplex n) n).inv (affineChain M n m)))) =
      (projection (chainFunctor R M) (simplexPair n)).f n (affineChain M n m)
  have hp' := congrArg (fun f : (ordinaryComplex R M (simplex n)).X (n : ℤ) ⟶
      ((nonnegative R M (simplexPair n)).extend (degreeEmbedding 0)).X (n : ℤ) =>
        f ((ordinaryNonnegativeIso R M (simplex n) n).inv (affineChain M n m))) hp
  change (ordinaryRelativeExtensionIso R M (simplexPair n)).hom.f (n : ℤ)
      ((projection (ordinaryFunctor R M) (simplexPair n)).f (n : ℤ)
        ((ordinaryNonnegativeIso R M (simplex n) n).inv (affineChain M n m))) =
    (HomologicalComplex.extendMap (projection (chainFunctor R M) (simplexPair n))
        (degreeEmbedding 0)).f (n : ℤ)
      ((ordinaryNonnegativeIso R M (simplex n) n).inv (affineChain M n m)) at hp'
  rw [hp']
  rw [HomologicalComplex.extendMap_f _ _ (show (degreeEmbedding 0).f n = (n : ℤ) by dsimp [degreeEmbedding]; omega)]
  change ((nonnegative R M (simplexPair n)).extendXIso (degreeEmbedding 0) _).hom
    (((nonnegative R M (simplexPair n)).extendXIso (degreeEmbedding 0) _).inv
      ((projection (chainFunctor R M) (simplexPair n)).f n
        ((ordinaryNonnegativeIso R M (simplex n) n).hom
          ((ordinaryNonnegativeIso R M (simplex n) n).inv (affineChain M n m))))) = _
  simp

end IntegralCoefficients

namespace IntegralCoefficients
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
open ConcentratedHomology

lemma nonnegativeAffine_quasiIso (n : ℕ)
    (hi : Function.Bijective (affineClassLinear R M n)) :
    QuasiIso (fromSingleCycles (nonnegative R M (simplexPair n)) n
      (nonnegativeAffineCycleMap R M n)) := by
  have hb : Function.Bijective (nonnegativeAffineClassLinear R M n) := by
    rw [← nonnegativeAffineClassLinear_transport]
    exact (ordinaryRelativeHomologyIso R M (simplexPair n) n).toLinearEquiv.bijective.comp hi
  have he : IsIso (nonnegativeAffineCycleMap R M n ≫
      (nonnegative R M (simplexPair n)).homologyπ n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  apply fromSingleCycles_quasiIso
  intro i hi
  exact (ordinaryRelativeHomologyIso R M (simplexPair n) i).isZero_iff.mp
    (simplexVanishing R M n i hi)

lemma affineClassLinear_bijective_of_quasiIso (n : ℕ)
    [QuasiIso (fromSingleCycles (nonnegative R M (simplexPair n)) n
      (nonnegativeAffineCycleMap R M n))] :
    Function.Bijective (affineClassLinear R M n) := by
  have he : IsIso (homologyMap
      (fromSingleCycles (nonnegative R M (simplexPair n)) n
        (nonnegativeAffineCycleMap R M n)) n) := inferInstance
  rw [fromSingleCycles_homologyMap] at he
  have he' : IsIso (nonnegativeAffineCycleMap R M n ≫
      (nonnegative R M (simplexPair n)).homologyπ n) :=
    IsIso.of_isIso_comp_left (singleObjHomologySelfIso (.down ℕ) n (ModuleCat.of R M)).hom _
  have hb : Function.Bijective (nonnegativeAffineClassLinear R M n) :=
    (ConcreteCategory.isIso_iff_bijective _).mp he'
  rw [← nonnegativeAffineClassLinear_transport] at hb
  exact (Function.Bijective.of_comp_iff'
    (ordinaryRelativeHomologyIso R M (simplexPair n) n).toLinearEquiv.bijective
    (affineClassLinear R M n)).mp hb

lemma nonnegative_integral_projective (P : Pair.{0}) (k : ℕ) :
    Projective ((nonnegative ℤ ℤ P).X k) := by
  obtain ⟨b, _⟩ := P202.RelativeSingularChains.quotient_basis ℤ P k
  exact ModuleCat.projective_of_free b

lemma single_integral_projective (n k : ℕ) :
    Projective (((single (ModuleCat.{0} ℤ) (.down ℕ) n).obj
      (ModuleCat.of ℤ ℤ)).X k) := by
  by_cases hk : k = n
  · subst k
    simpa only [single_obj_X_self] using
      (inferInstance : Projective (ModuleCat.of ℤ ℤ))
  · exact (isZero_single_obj_X (.down ℕ) n (ModuleCat.of ℤ ℤ) k hk).projective
end IntegralCoefficients

namespace SimplexOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
open P202Specs.MayerVietoris P202.SpheresDisks.SimplexGeometry

def reducedChain (X : TopCat.{0}) (n : ℕ) (c : Chains R X n) :
    (reducedComplex R R X).X (n : ℤ) :=
  (reducedNonnegativeIso R R X n).inv c

lemma reducedChain_map {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (c : Chains R X n) :
    ((reducedFunctor R R).map f).f (n : ℤ) (reducedChain R X n c) =
      reducedChain R Y n ((chainMap R R f).f n c) := by
  have he : (reducedNonnegativeIso R R X n).inv ≫ ((reducedFunctor R R).map f).f (n : ℤ) =
      (chainMap R R f).f n ≫ (reducedNonnegativeIso R R Y n).inv := by
    change (reducedNonnegativeIso R R X n).inv ≫
      (HomologicalComplex.extendMap (augmentedShiftedMap R R f) (degreeEmbedding (-1))).f (n : ℤ) = _
    rw [HomologicalComplex.extendMap_f _ _
      (show (degreeEmbedding (-1)).f (n+1) = (n : ℤ) by dsimp [degreeEmbedding]; omega)]
    simp [reducedNonnegativeIso, augmentedShiftedMap]
  exact congrArg (fun f => f c) he

def faceSplitReducedChain (n : ℕ) (m : R) :
    (middle (theoryFunctor R .reduced) (simplexBoundaryFaceCover n)).X (n : ℤ) :=
  splitChain _ _ (n : ℤ)
    (reducedChain R _ n (oppositeFaceLeftChain R n m))
    (reducedChain R _ n (sideFacesRightChain R n m))

lemma faceSplitReducedChain_sum (n : ℕ) (m : R) :
    (chainSum (theoryFunctor R .reduced) (simplexBoundaryFaceCover n)).f (n : ℤ)
      (faceSplitReducedChain R n m) = reducedOrientedBoundaryZ R n m := by
  rw [faceSplitReducedChain, chainSum_splitChain]
  change ((reducedFunctor R R).map (simplexBoundaryFaceCover n).leftInclusion.map).f (n : ℤ)
      (reducedChain R (simplexBoundaryFaceCover n).leftPair.space n (oppositeFaceLeftChain R n m)) +
    ((reducedFunctor R R).map (simplexBoundaryFaceCover n).rightInclusion.map).f (n : ℤ)
      (reducedChain R (simplexBoundaryFaceCover n).rightPair.space n (sideFacesRightChain R n m)) = _
  rw [reducedChain_map, reducedChain_map]
  change (reducedNonnegativeIso R R _ n).inv _ + (reducedNonnegativeIso R R _ n).inv _ = _
  rw [← map_add, orientedBoundary_face_split]
  rfl
end SimplexOrientation

namespace SimplexOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
open P202Specs.MayerVietoris P202.SpheresDisks.SimplexGeometry

lemma oppositeFaceLeftChain_from_affine (n : ℕ) (m : R) :
    (chainMap R R (oppositeFaceLeftMap n)).f n (affineChain R n m) =
      oppositeFaceLeftChain R n m := by
  rw [affineChain, P202.SingularChains.chainMap_single]
  congr 1

lemma oppositeFaceLeftReducedChain_from_affine (n : ℕ) (m : R) :
    ((reducedFunctor R R).map (oppositeFaceLeftMap n)).f (n : ℤ)
        (reducedAffineChainZ R n m) =
      reducedChain R _ n (oppositeFaceLeftChain R n m) := by
  change ((reducedFunctor R R).map (oppositeFaceLeftMap n)).f (n : ℤ)
      (reducedChain R _ n (affineChain R n m)) = _
  rw [reducedChain_map, oppositeFaceLeftChain_from_affine]

lemma oppositeFaceLeft_boundary_square (n : ℕ) :
    (simplexPair n).inclusion ≫ oppositeFaceLeftMap n =
      TopCat.ofHom (simplexBoundaryFaceToOverlap n) ≫ (simplexBoundaryFaceCover n).toLeft.map := by
  ext x
  rfl

/-- The positive-dimensional left face has exactly the pushed forward signed boundary. -/
lemma oppositeFaceLeftReducedChain_boundary_succ (n : ℕ) (m : R) :
    (reducedComplex R R (simplexBoundaryFaceCover (n+1)).leftPair.space).d
        ((n+1 : ℕ) : ℤ) (n : ℤ)
        (reducedChain R _ (n+1) (oppositeFaceLeftChain R (n+1) m)) =
      ((reducedFunctor R R).map (simplexBoundaryFaceCover (n+1)).toLeft.map).f (n : ℤ)
        (((reducedFunctor R R).map (TopCat.ofHom (simplexBoundaryFaceToOverlap (n+1)))).f (n : ℤ)
          (reducedOrientedBoundaryZ R n m)) := by
  rw [← oppositeFaceLeftReducedChain_from_affine]
  have hc := congrArg (fun f => f (reducedAffineChainZ R (n+1) m))
    (((reducedFunctor R R).map (oppositeFaceLeftMap (n+1))).comm ((n+1 : ℕ) : ℤ) (n : ℤ))
  change (reducedComplex R R (simplexBoundaryFaceCover (n+1)).leftPair.space).d
      ((n+1 : ℕ) : ℤ) (n : ℤ)
      (((reducedFunctor R R).map (oppositeFaceLeftMap (n+1))).f ((n+1 : ℕ) : ℤ)
        (reducedAffineChainZ R (n+1) m)) = _ at hc
  refine hc.trans ?_
  change ((reducedFunctor R R).map (oppositeFaceLeftMap (n+1))).f (n : ℤ)
    ((reducedComplex R R (simplex (n+1))).d ((n+1 : ℕ) : ℤ) (n : ℤ)
      (reducedAffineChainZ R (n+1) m)) = _
  rw [← inclusion_reducedOrientedBoundaryZ]
  have he : inclusion (reducedFunctor R R) (simplexPair (n+1)) ≫
      (reducedFunctor R R).map (oppositeFaceLeftMap (n+1)) =
      (reducedFunctor R R).map (TopCat.ofHom (simplexBoundaryFaceToOverlap (n+1))) ≫
        (reducedFunctor R R).map (simplexBoundaryFaceCover (n+1)).toLeft.map := by
    change (reducedFunctor R R).map (simplexPair (n+1)).inclusion ≫ _ = _
    rw [← Functor.map_comp, oppositeFaceLeft_boundary_square, Functor.map_comp]
  exact congrArg (fun f => f.f (n : ℤ) (reducedOrientedBoundaryZ R n m)) he

/-- In degree zero the same left-face boundary is the augmentation unit. -/
lemma oppositeFaceLeftReducedChain_boundary_zero (m : R) :
    (reducedComplex R R (simplexBoundaryFaceCover 0).leftPair.space).d 0 (-1)
        (reducedChain R _ 0 (oppositeFaceLeftChain R 0 m)) =
      ((reducedFunctor R R).map (simplexBoundaryFaceCover 0).toLeft.map).f (-1)
        (((reducedFunctor R R).map (TopCat.ofHom (simplexBoundaryFaceToOverlap 0))).f (-1)
          (reducedBoundaryUnit R m)) := by
  rw [← oppositeFaceLeftReducedChain_from_affine]
  have hc := congrArg (fun f => f (reducedAffineChainZ R 0 m))
    (((reducedFunctor R R).map (oppositeFaceLeftMap 0)).comm 0 (-1))
  change (reducedComplex R R (simplexBoundaryFaceCover 0).leftPair.space).d 0 (-1)
      (((reducedFunctor R R).map (oppositeFaceLeftMap 0)).f 0
        (reducedAffineChainZ R 0 m)) = _ at hc
  refine hc.trans ?_
  change ((reducedFunctor R R).map (oppositeFaceLeftMap 0)).f (-1)
    ((reducedComplex R R (simplex 0)).d 0 (-1)
      (reducedAffineChainZ R 0 m)) = _
  rw [← inclusion_reducedBoundaryUnit]
  have he : inclusion (reducedFunctor R R) (simplexPair 0) ≫
      (reducedFunctor R R).map (oppositeFaceLeftMap 0) =
      (reducedFunctor R R).map (TopCat.ofHom (simplexBoundaryFaceToOverlap 0)) ≫
        (reducedFunctor R R).map (simplexBoundaryFaceCover 0).toLeft.map := by
    change (reducedFunctor R R).map (simplexPair 0).inclusion ≫ _ = _
    rw [← Functor.map_comp, oppositeFaceLeft_boundary_square, Functor.map_comp]
  exact congrArg (fun f => f.f (-1) (reducedBoundaryUnit R m)) he

end SimplexOrientation

namespace IntegralCoefficients
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks

lemma integralTensorFromSingleAffine (n : ℕ) :
    ((single (ModuleCat R) (.down ℕ) n).map (integralTensorUnitIso R M).inv) ≫
      ((singleMapHomologicalComplex (integralTensorFunctor R M) (.down ℕ) n).app
        (ModuleCat.of ℤ ℤ)).inv ≫
      (((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).map
        (ConcentratedHomology.fromSingleCycles (nonnegative ℤ ℤ (simplexPair n)) n
          (nonnegativeAffineCycleMap ℤ ℤ n))) ≫
      (integralTensorRelativeIso R M (simplexPair n)).hom =
    ConcentratedHomology.fromSingleCycles (nonnegative R M (simplexPair n)) n
      (nonnegativeAffineCycleMap R M n) := by
  apply from_single_hom_ext
  apply (cancel_epi (singleObjXSelf (.down ℕ) n (ModuleCat.of R M)).inv).mp
  simp only [HomologicalComplex.comp_f, single_map_f_self, Iso.app_inv,
    singleMapHomologicalComplex_inv_app_self, Functor.mapHomologicalComplex_map_f,
    ConcentratedHomology.fromSingleCycles, mkHomFromSingle_f, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [nonnegativeAffineCycleMap_i, nonnegativeAffineCycleMap_i]
  apply ModuleCat.hom_ext
  ext m
  change (integralTensorRelativeComponent R M (simplexPair n) n).hom
      (TensorProduct.AlgebraTensorModule.lTensor R M (nonnegativeAffineLinear ℤ ℤ n)
        (m ⊗ₜ[ℤ] (1 : ℤ))) = nonnegativeAffineLinear R M n m
  rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
  change (integralTensorRelativeComponent R M (simplexPair n) n).hom
      (m ⊗ₜ[ℤ] ((projection (chainFunctor ℤ ℤ) (simplexPair n)).f n (affineChain ℤ n 1))) =
    (projection (chainFunctor R M) (simplexPair n)).f n (affineChain M n m)
  rw [integralTensorRelativeComponent_projection]
  simp only [affineChain, integralTensorChainsEquiv_tmul_single, one_zsmul]

end IntegralCoefficients

namespace IntegralCoefficients
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
open ConcentratedHomology

lemma affineClassLinear_bijective_of_integral (n : ℕ)
    (hi : Function.Bijective (affineClassLinear ℤ ℤ n)) :
    Function.Bijective (affineClassLinear R M n) := by
  let F := integralTensorFunctor R M
  let K := nonnegative ℤ ℤ (simplexPair n)
  let f := fromSingleCycles K n (nonnegativeAffineCycleMap ℤ ℤ n)
  have : ∀ k, Projective (K.X k) := fun k => nonnegative_integral_projective (simplexPair n) k
  have : ∀ k, Projective (((single (ModuleCat.{0} ℤ) (.down ℕ) n).obj
      (ModuleCat.of ℤ ℤ)).X k) := single_integral_projective n
  have : QuasiIso f := nonnegativeAffine_quasiIso ℤ ℤ n hi
  have : QuasiIso ((F.mapHomologicalComplex (.down ℕ)).map f) :=
    map_quasiIso_of_projective F f
  have hq : QuasiIso
      (((single (ModuleCat R) (.down ℕ) n).map (integralTensorUnitIso R M).inv) ≫
        ((singleMapHomologicalComplex F (.down ℕ) n).app (ModuleCat.of ℤ ℤ)).inv ≫
        ((F.mapHomologicalComplex (.down ℕ)).map f) ≫
        (integralTensorRelativeIso R M (simplexPair n)).hom) := by infer_instance
  change QuasiIso
      (((single (ModuleCat R) (.down ℕ) n).map (integralTensorUnitIso R M).inv) ≫
        ((singleMapHomologicalComplex (integralTensorFunctor R M) (.down ℕ) n).app
          (ModuleCat.of ℤ ℤ)).inv ≫
        (((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).map
          (fromSingleCycles (nonnegative ℤ ℤ (simplexPair n)) n
            (nonnegativeAffineCycleMap ℤ ℤ n))) ≫
        (integralTensorRelativeIso R M (simplexPair n)).hom) at hq
  rw [integralTensorFromSingleAffine] at hq
  exact affineClassLinear_bijective_of_quasiIso R M n
end IntegralCoefficients

namespace SimplexOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
open P202Specs.MayerVietoris P202.SpheresDisks.SimplexGeometry

/-- Reindex a connecting map by a proved successor relation. -/
def connectingAt {F : Pair.{0} ⥤ ChainComplex (ModuleCat.{u} R) ℤ}
    (δ : Connecting.{u,0,0} F) (C : CoverPair.{0,0}) (i j : ℤ) (hij : i = j+1) :
    (F.obj C.pair).homology i ⟶ (F.obj C.intersectionPair).homology j :=
  eqToHom (congrArg (fun k => (F.obj C.pair).homology k) hij) ≫ δ C j

lemma connectingAt_formula_of_left_boundary
    (F : Pair.{0} ⥤ ChainComplex (ModuleCat.{u} R) ℤ)
    (δ : Connecting.{u,0,0} F)
    (hlift : BoundaryLifts.{u,0,0} F) (hformula : BoundaryFormula F δ)
    (C : CoverPair.{0,0}) (i j : ℤ) (hij : i = j+1)
    (c : (middle F C).X i)
    (hc : (F.obj C.pair).d i j ((chainSum F C).f i c) = 0)
    (x : (F.obj C.intersectionPair).X j)
    (hinj : Function.Injective ((F.map C.toLeft).f j))
    (hx : (F.map C.toLeft).f j x =
      (biprod.fst : middle F C ⟶ F.obj C.leftPair).f j
        ((middle F C).d i j c)) :
    ∃ hxc : (F.obj C.intersectionPair).d j (j-1) x = 0,
      connectingAt R δ C i j hij
        (P202Specs.MayerVietoris.classOf (F.obj C.pair) i
          ((chainSum F C).f i c) (by
            have hh : i-1 = j := by omega
            rw [hh]; exact hc)) =
      P202Specs.MayerVietoris.classOf (F.obj C.intersectionPair) j x hxc := by
  subst i
  exact mv_formula_of_left_boundary F δ hlift hformula C j c hc x hinj hx

instance connectingAt_isIso
    {F : Pair.{0} ⥤ ChainComplex (ModuleCat.{u} R) ℤ}
    (δ : Connecting.{u,0,0} F) (C : CoverPair.{0,0}) (i j : ℤ) (hij : i = j+1)
    [IsIso (δ C j)] : IsIso (connectingAt R δ C i j hij) := by
  dsimp [connectingAt]
  infer_instance

def orientedBoundaryClass (n : ℕ) (m : R) :
    reducedHomology R R (simplexPair (n+1)).sub (n : ℤ) :=
  P202Specs.SpheresDisks.classOf R _ (n : ℤ)
    (reducedOrientedBoundaryZ R n m) (reducedOrientedBoundaryZ_cycle R n m)

lemma affineClass_bijective_of_orientedBoundaryClass
    (h : ∀ n : ℕ, Function.Bijective (orientedBoundaryClass R n)) :
    ∀ n : ℕ, Function.Bijective (affineClassLinear R R n) := by
  intro n
  cases n with
  | zero => exact affineClassLinear_zero_bijective R R
  | succ n =>
    let e := canonicalSimplexShift R n
    have hcomp : e.hom ∘ affineClassLinear R R (n+1) = orientedBoundaryClass R n := by
      funext m
      rw [Function.comp_apply, affineClassLinear_apply]
      exact canonicalSimplexShift_affine R n m
    exact (Function.Bijective.of_comp_iff'
      ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance) _).mp
        (hcomp ▸ h n)
end SimplexOrientation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SimplexOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
open P202Specs.MayerVietoris P202.SpheresDisks.SimplexGeometry

lemma classOf_congr (K : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (z z' : K.X n) (hz : K.d n (n-1) z = 0) (hz' : K.d n (n-1) z' = 0)
    (h : z = z') : P202Specs.SpheresDisks.classOf R K n z hz =
      P202Specs.SpheresDisks.classOf R K n z' hz' := by
  subst z'
  rfl

lemma faceCoverConnecting_isIso
    (δ : Connecting.{u,0,0} (theoryFunctor R .reduced))
    (he : P202Specs.MayerVietoris.Exact (theoryFunctor R .reduced) δ)
    (n : ℕ) (j : ℤ) : IsIso (δ (simplexBoundaryFaceCover n) j) := by
  let C := simplexBoundaryFaceCover n
  haveI : ContractibleSpace C.leftPair.space := simplexBoundaryFaceCover_left_contractible n
  haveI : ContractibleSpace C.rightPair.space := simplexBoundaryFaceCover_right_contractible n
  haveI : Nonempty C.leftPair.space :=
    ⟨⟨oppositeFaceBarycenter n, (simplexBoundaryVertex_ne_barycenter n).symm⟩⟩
  haveI : Nonempty C.rightPair.space :=
    ⟨⟨simplexBoundaryVertex n, simplexBoundaryVertex_ne_barycenter n⟩⟩
  exact mvConnecting_isIso R _ δ he C j
    (fun k _ => P202.PrismHomotopy.contractible R R C.leftPair.space k)
    (fun k _ => P202.PrismHomotopy.contractible R R C.rightPair.space k)

def boundaryUnitClass (m : R) : reducedHomology R R (simplexPair 0).sub (-1) :=
  P202Specs.SpheresDisks.classOf R _ (-1) (reducedBoundaryUnit R m) (reducedBoundaryUnit_cycle R m)

lemma normalizedMV_zero
    (δ : Connecting.{u,0,0} (theoryFunctor R .reduced))
    (hlift : BoundaryLifts.{u,0,0} (theoryFunctor R .reduced))
    (hformula : BoundaryFormula (theoryFunctor R .reduced) δ) (m : R) :
    connectingAt R δ (simplexBoundaryFaceCover 0) 0 (-1) (by omega)
      (orientedBoundaryClass R 0 m) =
    ((reducedHomologyFunctor R R (-1)).map (TopCat.ofHom (simplexBoundaryFaceToOverlap 0)))
      (boundaryUnitClass R m) := by
  let F := theoryFunctor R .reduced
  let C := simplexBoundaryFaceCover 0
  let c : (middle F C).X 0 := faceSplitReducedChain R 0 m
  let f := (reducedFunctor R R).map (TopCat.ofHom (simplexBoundaryFaceToOverlap 0))
  let x := f.f (-1) (reducedBoundaryUnit R m)
  have hc : (F.obj C.pair).d 0 (-1) ((chainSum F C).f 0 c) = 0 := by
    have hs := faceSplitReducedChain_sum R 0 m
    change (chainSum F C).f 0 c = reducedOrientedBoundaryZ R 0 m at hs
    rw [hs]
    exact reducedOrientedBoundaryZ_cycle R 0 m
  have hx : (F.map C.toLeft).f (-1) x =
      (biprod.fst : middle F C ⟶ F.obj C.leftPair).f (-1) ((middle F C).d 0 (-1) c) := by
    change _ = (biprod.fst : middle F C ⟶ F.obj C.leftPair).f (-1)
      ((middle F C).d 0 (-1)
        (splitChain F C 0
          (reducedChain R _ 0 (oppositeFaceLeftChain R 0 m))
          (reducedChain R _ 0 (sideFacesRightChain R 0 m))))
    rw [splitChain_left_boundary]
    exact (oppositeFaceLeftReducedChain_boundary_zero R m).symm
  obtain ⟨hxc, hδ⟩ := connectingAt_formula_of_left_boundary R F δ hlift hformula C
    0 (-1) (by omega) c hc x (reduced_overlap_to_left_injective R C (-1)) hx
  have hs := faceSplitReducedChain_sum R 0 m
  change (chainSum F C).f 0 c = reducedOrientedBoundaryZ R 0 m at hs
  have hmap := P202.MayerVietoris.classOf_map f (-1) (reducedBoundaryUnit R m)
    (reducedBoundaryUnit_cycle R m) hxc
  change connectingAt R δ C 0 (-1) _
    (P202Specs.SpheresDisks.classOf R _ 0 ((chainSum F C).f 0 c) _) =
    P202Specs.SpheresDisks.classOf R _ (-1) x hxc at hδ
  have hsclass (hz : (F.obj C.pair).d 0 (0-1) ((chainSum F C).f 0 c) = 0) :
      P202Specs.SpheresDisks.classOf R (F.obj C.pair) 0 ((chainSum F C).f 0 c) hz =
      orientedBoundaryClass R 0 m :=
    classOf_congr R _ 0 _ _ hz (reducedOrientedBoundaryZ_cycle R 0 m) hs
  rw [hsclass] at hδ
  exact hδ.trans hmap.symm

lemma normalizedMV_succ
    (δ : Connecting.{u,0,0} (theoryFunctor R .reduced))
    (hlift : BoundaryLifts.{u,0,0} (theoryFunctor R .reduced))
    (hformula : BoundaryFormula (theoryFunctor R .reduced) δ) (n : ℕ) (m : R) :
    connectingAt R δ (simplexBoundaryFaceCover (n+1)) ((n+1 : ℕ) : ℤ) (n : ℤ) (by omega)
      (orientedBoundaryClass R (n+1) m) =
    ((reducedHomologyFunctor R R (n : ℤ)).map (TopCat.ofHom (simplexBoundaryFaceToOverlap (n+1))))
      (orientedBoundaryClass R n m) := by
  let F := theoryFunctor R .reduced
  let C := simplexBoundaryFaceCover (n+1)
  let c := faceSplitReducedChain R (n+1) m
  let f := (reducedFunctor R R).map (TopCat.ofHom (simplexBoundaryFaceToOverlap (n+1)))
  let x := f.f (n : ℤ) (reducedOrientedBoundaryZ R n m)
  have hc : (F.obj C.pair).d ((n+1 : ℕ) : ℤ) (n : ℤ)
      ((chainSum F C).f ((n+1 : ℕ) : ℤ) c) = 0 := by
    have hs := faceSplitReducedChain_sum R (n+1) m
    change (chainSum F C).f ((n+1 : ℕ) : ℤ) c = reducedOrientedBoundaryZ R (n+1) m at hs
    rw [hs]
    have hcycle := reducedOrientedBoundaryZ_cycle R (n+1) m
    have hn : (((n+1 : ℕ) : ℤ)-1) = (n : ℤ) := by omega
    rw [hn] at hcycle
    exact hcycle
  have hx : (F.map C.toLeft).f (n : ℤ) x =
      (biprod.fst : middle F C ⟶ F.obj C.leftPair).f (n : ℤ)
        ((middle F C).d ((n+1 : ℕ) : ℤ) (n : ℤ) c) := by
    change _ = (biprod.fst : middle F C ⟶ F.obj C.leftPair).f (n : ℤ)
      ((middle F C).d ((n+1 : ℕ) : ℤ) (n : ℤ)
        (splitChain F C ((n+1 : ℕ) : ℤ)
          (reducedChain R _ (n+1) (oppositeFaceLeftChain R (n+1) m))
          (reducedChain R _ (n+1) (sideFacesRightChain R (n+1) m))))
    rw [splitChain_left_boundary]
    exact (oppositeFaceLeftReducedChain_boundary_succ R n m).symm
  obtain ⟨hxc, hδ⟩ := connectingAt_formula_of_left_boundary R F δ hlift hformula C
    ((n+1 : ℕ) : ℤ) (n : ℤ) (by omega) c hc x
    (reduced_overlap_to_left_injective R C (n : ℤ)) hx
  have hs := faceSplitReducedChain_sum R (n+1) m
  change (chainSum F C).f ((n+1 : ℕ) : ℤ) c = reducedOrientedBoundaryZ R (n+1) m at hs
  have hmap := P202.MayerVietoris.classOf_map f (n : ℤ) (reducedOrientedBoundaryZ R n m)
    (reducedOrientedBoundaryZ_cycle R n m) hxc
  change connectingAt R δ C ((n+1 : ℕ) : ℤ) (n : ℤ) _
    (P202Specs.SpheresDisks.classOf R _ ((n+1 : ℕ) : ℤ)
      ((chainSum F C).f ((n+1 : ℕ) : ℤ) c) _) =
    P202Specs.SpheresDisks.classOf R _ (n : ℤ) x hxc at hδ
  have hsclass (hz : (F.obj C.pair).d ((n+1 : ℕ) : ℤ) (((n+1 : ℕ) : ℤ)-1)
      ((chainSum F C).f ((n+1 : ℕ) : ℤ) c) = 0) :
      P202Specs.SpheresDisks.classOf R (F.obj C.pair) ((n+1 : ℕ) : ℤ)
        ((chainSum F C).f ((n+1 : ℕ) : ℤ) c) hz = orientedBoundaryClass R (n+1) m :=
    classOf_congr R _ ((n+1 : ℕ) : ℤ) _ _ hz (reducedOrientedBoundaryZ_cycle R (n+1) m) hs
  rw [hsclass] at hδ
  exact hδ.trans hmap.symm
end SimplexOrientation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SimplexOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks

/-- The canonical coefficient class in reduced degree minus one of the empty boundary. -/
def reducedBoundaryUnitClass (m : R) :
    reducedHomology R R (simplexPair 0).sub (-1) :=
  P202Specs.SpheresDisks.classOf R _ (-1)
    (reducedBoundaryUnit R m) (reducedBoundaryUnit_cycle R m)

lemma reducedBoundaryUnitClass_bijective : Function.Bijective (reducedBoundaryUnitClass R) := by
  let e := canonicalSimplexZeroShift R
  have hcomp : e.hom ∘ affineClassLinear R R 0 = reducedBoundaryUnitClass R := by
    funext m
    rw [Function.comp_apply, affineClassLinear_apply]
    exact canonicalSimplexZeroShift_affine R m
  have hb : Function.Bijective (e.hom ∘ affineClassLinear R R 0) :=
    ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance).comp
      (affineClassLinear_zero_bijective R R)
  rwa [hcomp] at hb

/-- Exact normalization in the base step and the recursive suspension steps
forces every signed boundary class, and hence every affine relative class,
to be primitive with the prescribed coefficient. -/
lemma affineClass_bijective_of_normalized_boundary_shifts
    (e0 : reducedHomology R R (simplexPair 1).sub 0 ≅
      reducedHomology R R (simplexPair 0).sub (-1))
    (h0 : ∀ m : R, e0.hom (orientedBoundaryClass R 0 m) = reducedBoundaryUnitClass R m)
    (es : ∀ n : ℕ, reducedHomology R R (simplexPair ((n+1)+1)).sub ((n+1 : ℕ) : ℤ) ≅
      reducedHomology R R (simplexPair (n+1)).sub (n : ℤ))
    (hs : ∀ (n : ℕ) (m : R), (es n).hom (orientedBoundaryClass R (n+1) m) =
      orientedBoundaryClass R n m) :
    ∀ n : ℕ, Function.Bijective (affineClassLinear R R n) := by
  apply affineClass_bijective_of_orientedBoundaryClass R
  intro n
  induction n with
  | zero =>
    have hcomp : e0.hom ∘ orientedBoundaryClass R 0 = reducedBoundaryUnitClass R :=
      funext h0
    exact (Function.Bijective.of_comp_iff'
      ((ConcreteCategory.isIso_iff_bijective e0.hom).mp inferInstance) _).mp
        (hcomp ▸ reducedBoundaryUnitClass_bijective R)
  | succ n ih =>
    have hcomp : (es n).hom ∘ orientedBoundaryClass R (n+1) = orientedBoundaryClass R n :=
      funext (hs n)
    exact (Function.Bijective.of_comp_iff'
      ((ConcreteCategory.isIso_iff_bijective (es n).hom).mp inferInstance) _).mp
        (hcomp ▸ ih)

end SimplexOrientation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SimplexOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.SpheresDisks
open P202Specs.MayerVietoris P202.SpheresDisks.SimplexGeometry

/-- The affine simplex is the normalized relative generator over every
commutative coefficient ring; the exact boundary signs come from the genuine
Mayer–Vietoris boundary-of-a-split-lift formula. -/
lemma affineClassLinear_ring_bijective :
    ∀ n : ℕ, Function.Bijective (affineClassLinear R R n) := by
  obtain ⟨⟨δ, he, _hn, hformula⟩, _hsmall, hlift, _⟩ :=
    P202.MayerVietoris.mayerVietoris.{u,0,0} R .reduced
  have hiso (n : ℕ) (j : ℤ) : IsIso (δ (simplexBoundaryFaceCover n) j) :=
    faceCoverConnecting_isIso R δ he n j
  let e0 : reducedHomology R R (simplexPair 1).sub 0 ≅
      reducedHomology R R (simplexPair 0).sub (-1) := by
    haveI := hiso 0 (-1)
    exact asIso (connectingAt R δ (simplexBoundaryFaceCover 0) 0 (-1) (by omega)) ≪≫
      (simplexBoundaryFaceReducedIso R R 0 (-1)).symm
  let es (n : ℕ) :
      reducedHomology R R (simplexPair ((n+1)+1)).sub ((n+1 : ℕ) : ℤ) ≅
        reducedHomology R R (simplexPair (n+1)).sub (n : ℤ) := by
    haveI := hiso (n+1) (n : ℤ)
    exact asIso (connectingAt R δ (simplexBoundaryFaceCover (n+1))
      ((n+1 : ℕ) : ℤ) (n : ℤ) (by omega)) ≪≫
      (simplexBoundaryFaceReducedIso R R (n+1) (n : ℤ)).symm
  apply affineClass_bijective_of_normalized_boundary_shifts R e0 ?_ es ?_
  · intro m
    change (simplexBoundaryFaceReducedIso R R 0 (-1)).inv
      (connectingAt R δ (simplexBoundaryFaceCover 0) 0 (-1) (by omega)
        (orientedBoundaryClass R 0 m)) = boundaryUnitClass R m
    rw [normalizedMV_zero R δ hlift hformula]
    change (simplexBoundaryFaceReducedIso R R 0 (-1)).inv
      ((simplexBoundaryFaceReducedIso R R 0 (-1)).hom (boundaryUnitClass R m)) = _
    exact congrArg (fun f => f (boundaryUnitClass R m))
      (simplexBoundaryFaceReducedIso R R 0 (-1)).hom_inv_id
  · intro n m
    change (simplexBoundaryFaceReducedIso R R (n+1) (n : ℤ)).inv
      (connectingAt R δ (simplexBoundaryFaceCover (n+1)) ((n+1 : ℕ) : ℤ) (n : ℤ) (by omega)
        (orientedBoundaryClass R (n+1) m)) = orientedBoundaryClass R n m
    rw [normalizedMV_succ R δ hlift hformula]
    change (simplexBoundaryFaceReducedIso R R (n+1) (n : ℤ)).inv
      ((simplexBoundaryFaceReducedIso R R (n+1) (n : ℤ)).hom (orientedBoundaryClass R n m)) = _
    exact congrArg (fun f => f (orientedBoundaryClass R n m))
      (simplexBoundaryFaceReducedIso R R (n+1) (n : ℤ)).hom_inv_id
end SimplexOrientation

/-- Every coefficient multiple of the oriented affine simplex is exactly
its corresponding element of the top relative homology module. -/
theorem simplexGenerator : simplexGenerator_type.{u,v} :=
  simplexGenerator_of_affineClass_bijective (fun R _ M _ _ n =>
    IntegralCoefficients.affineClassLinear_bijective_of_integral R M n
      (SimplexOrientation.affineClassLinear_ring_bijective ℤ n))

end P202.SpheresDisks
