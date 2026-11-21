import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.ShuffleTriangulation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.RelativeCupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.TransverseThomProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.CupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.TransverseThomProduct
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import Mathlib.Algebra.Ring.Int.Units
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.TransversePreimage
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FieldSimp
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.ThomClass
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleOperations
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SpheresDisks
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.LocalOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy
import Mathlib.LinearAlgebra.Projectivization.Action
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.ComplexProjectiveRing
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.ComplexProjectiveHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficientsCohomology
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-! The integral singular cup ring of every finite complex projective space.
The actual complex-normal hyperplane Thom class gives the degree-two generator.
Its powers restrict to positive local classes on all standard projective
subspaces and evaluate to one on their complex fundamental classes. This gives
the graded truncated-polynomial presentation, including the point endpoint. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
open Set Topology
namespace P202.ComplexProjective

lemma lowerSpace_closed (m k : ℕ) : IsClosed (lowerSpace m k) := by
  rw [← (quotientMap_quotient m).isClosed_preimage]
  have heq : quotientMap m ⁻¹' lowerSpace m k =
      ⋂ i : Fin (m+1), {v : NonzeroVectors m | k ≤ i.val → v.val i = 0} := by
    ext v
    simp only [Set.mem_preimage, quotientMap, lowerSpace_mk, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [heq]
  apply isClosed_iInter
  intro i
  by_cases hi : k ≤ i.val
  · simpa [hi] using isClosed_eq
      ((continuous_apply i).comp continuous_subtype_val)
      (continuous_const : Continuous (fun _ : NonzeroVectors m => (0 : ℂ)))
  · simp [hi]

lemma topStratum_eq_compl (m : ℕ) : stratum m m = (lowerSpace m m)ᶜ := by
  rw [stratum, lowerSpace_top]
  exact (Set.compl_eq_univ_sdiff _).symm

lemma affineChart_top_openEmbedding (m : ℕ) :
    IsOpenEmbedding (affineChart m m le_rfl) := by
  refine ⟨affineChart_embedding m m le_rfl, ?_⟩
  rw [affineChart_range, topStratum_eq_compl]
  exact (lowerSpace_closed m m).isOpen_compl

/-- The last-coordinate affine chart of the actual adopted quotient topology. -/
def topAffineChart (m : ℕ) : OpenPartialHomeomorph (Space m) (Fin m → ℂ) :=
  ((affineChart_top_openEmbedding m).toOpenPartialHomeomorph (affineChart m m le_rfl)).symm

lemma topAffineChart_symm (m : ℕ) (z : Fin m → ℂ) :
    (topAffineChart m).symm z = affineChart m m le_rfl z := rfl

lemma topAffineChart_source (m : ℕ) :
    (topAffineChart m).source = (lowerSpace m m)ᶜ := by
  simp only [topAffineChart, OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target]
  rw [affineChart_range, topStratum_eq_compl]

lemma topAffineChart_target (m : ℕ) :
    (topAffineChart m).target = Set.univ := rfl

end P202.ComplexProjective

namespace P202.ComplexProjective

/-- A coordinate hyperplane on the actual projective quotient. -/
def coordinateHyperplane (m : ℕ) (j : Fin (m+1)) : Set (Space m) :=
  {p | ∃ (v : Fin (m+1) → ℂ) (hv : v ≠ 0), mk v hv = p ∧ v j = 0}

lemma coordinateHyperplane_mk {m : ℕ} (j : Fin (m+1))
    (v : Fin (m+1) → ℂ) (hv : v ≠ 0) :
    mk v hv ∈ coordinateHyperplane m j ↔ v j = 0 := by
  constructor
  · rintro ⟨w, hw, he, hz⟩
    obtain ⟨a, ha⟩ := (mk_eq_mk w v hw hv).mp he
    have heq : (a : ℂ) * v j = 0 := by
      simpa [Units.smul_def] using (congrFun ha j).trans hz
    exact (mul_eq_zero.mp heq).resolve_left a.ne_zero
  · intro h
    exact ⟨v,hv,rfl,h⟩

lemma coordinateHyperplane_closed (m : ℕ) (j : Fin (m+1)) :
    IsClosed (coordinateHyperplane m j) := by
  rw [← (quotientMap_quotient m).isClosed_preimage]
  have heq : quotientMap m ⁻¹' coordinateHyperplane m j =
      {v : NonzeroVectors m | v.val j = 0} := by
    ext v
    exact coordinateHyperplane_mk j v.val v.property
  rw [heq]
  exact isClosed_eq ((continuous_apply j).comp continuous_subtype_val) continuous_const

lemma lastCoordinateHyperplane_eq (m : ℕ) :
    coordinateHyperplane m (Fin.last m) = lowerSpace m m := by
  ext p
  induction p using Projectivization.ind with | h v hv =>
  change mk v hv ∈ coordinateHyperplane m (Fin.last m) ↔ mk v hv ∈ lowerSpace m m
  rw [coordinateHyperplane_mk, lowerSpace_mk]
  constructor
  · intro h i hi
    have hei : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    simpa [hei] using h
  · exact fun h => h (Fin.last m) le_rfl

lemma coordinateHyperplane_compact (m : ℕ) (j : Fin (m+1)) :
    IsCompact (coordinateHyperplane m j) :=
  (coordinateHyperplane_closed m j).isCompact

/-- Any complex linear equivalence induces a homeomorphism of the fixed
quotient space. No replacement topology or smooth structure is chosen. -/
def projectiveLinearHomeomorph (m : ℕ)
    (e : (Fin (m+1) → ℂ) ≃ₗ[ℂ] (Fin (m+1) → ℂ)) : Space m ≃ₜ Space m where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, e.symm_apply_apply]
  right_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, e.apply_symm_apply]
  continuous_toFun := by
    apply (quotientMap_quotient m).continuous_iff.mpr
    change Continuous (quotientMap m ∘ fun v : NonzeroVectors m =>
      ⟨e v.val, fun h => v.property (e.injective (by simpa using h))⟩)
    exact (quotientMap_continuous m).comp
      ((e.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := by
    apply (quotientMap_quotient m).continuous_iff.mpr
    change Continuous (quotientMap m ∘ fun v : NonzeroVectors m =>
      ⟨e.symm v.val, fun h => v.property (e.symm.injective (by simpa using h))⟩)
    exact (quotientMap_continuous m).comp
      ((e.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _)

/-- The index permutation acts by precomposing homogeneous coordinates. -/
def coordinatePermutation (m : ℕ) (e : Equiv.Perm (Fin (m+1))) : Space m ≃ₜ Space m :=
  projectiveLinearHomeomorph m (LinearEquiv.funCongrLeft ℂ ℂ e)

lemma coordinatePermutation_hyperplane (m : ℕ) (e : Equiv.Perm (Fin (m+1)))
    (j : Fin (m+1)) (p : Space m) :
    coordinatePermutation m e p ∈ coordinateHyperplane m j ↔
      p ∈ coordinateHyperplane m (e j) := by
  induction p using Projectivization.ind with | h v hv =>
  change mk ((LinearEquiv.funCongrLeft ℂ ℂ e) v) _ ∈ _ ↔ mk v hv ∈ _
  rw [coordinateHyperplane_mk, coordinateHyperplane_mk]
  rfl

end P202.ComplexProjective

namespace P202.ComplexProjective

lemma lastCoordinateHyperplane_range (m : ℕ) :
    coordinateHyperplane (m+1) (Fin.last (m+1)) =
      Set.range (inclusion (m+1) m (Nat.le_succ m)) := by
  rw [lastCoordinateHyperplane_eq, inclusion_range]

/-- The original zero-padding inclusion moved to an arbitrary coordinate
hyperplane by a homogeneous coordinate permutation. -/
def coordinateHyperplaneInclusion (m : ℕ) (j : Fin (m+2)) : Space m → Space (m+1) :=
  coordinatePermutation (m+1) (Equiv.swap (Fin.last (m+1)) j) ∘
    inclusion (m+1) m (Nat.le_succ m)

lemma coordinateHyperplaneInclusion_range (m : ℕ) (j : Fin (m+2)) :
    Set.range (coordinateHyperplaneInclusion m j) = coordinateHyperplane (m+1) j := by
  rw [coordinateHyperplaneInclusion, Set.range_comp, ← lastCoordinateHyperplane_range]
  let e := Equiv.swap (Fin.last (m+1)) j
  change coordinatePermutation (m+1) e '' coordinateHyperplane (m+1) (Fin.last (m+1)) = _
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    apply (coordinatePermutation_hyperplane (m+1) e j q).mpr
    simpa [e] using hq
  · intro hp
    let q := (coordinatePermutation (m+1) e).symm p
    have he : coordinatePermutation (m+1) e q = p :=
      (coordinatePermutation (m+1) e).apply_symm_apply p
    have hq := (coordinatePermutation_hyperplane (m+1) e j q).mp (he ▸ hp)
    refine ⟨q, ?_,he⟩
    simpa [e] using hq

lemma coordinateHyperplaneInclusion_embedding (m : ℕ) (j : Fin (m+2)) :
    IsEmbedding (coordinateHyperplaneInclusion m j) :=
  (coordinatePermutation (m+1) (Equiv.swap (Fin.last (m+1)) j)).isEmbedding.comp
    (inclusion_embedding (m+1) m (Nat.le_succ m))

lemma coordinateHyperplane_zero (j : Fin 1) : coordinateHyperplane 0 j = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨v,hv,rfl,hj⟩ := hp
  apply hv
  ext i
  have hij : i = j := Fin.ext (by omega)
  simpa [hij] using hj

end P202.ComplexProjective

namespace P202.ComplexProjective

lemma coordinateHyperplane_topAffineChart (m : ℕ) (j : Fin m) (z : Fin m → ℂ) :
    affineChart m m le_rfl z ∈ coordinateHyperplane m j.castSucc ↔ z j = 0 := by
  rw [affineChart, coordinateHyperplane_mk]
  simp [coordinateVector, j.isLt]

lemma firstCoordinateHyperplanes_intersection (m : ℕ) :
    (⋂ j : Fin m, coordinateHyperplane m j.castSucc) =
      {affineChart m m le_rfl 0} := by
  ext p
  constructor
  · intro hp
    induction p using Projectivization.ind with | h v hv =>
    change mk v hv = affineChart m m le_rfl 0
    have hz : ∀ j : Fin m, v j.castSucc = 0 := by
      intro j
      exact (coordinateHyperplane_mk j.castSucc v hv).mp (Set.mem_iInter.mp hp j)
    have hl : v (Fin.last m) ≠ 0 := by
      intro h
      apply hv
      ext j
      refine Fin.lastCases ?_ ?_ j
      · exact h
      · exact hz
    apply (mk_eq_mk' v (coordinateVector m m 0 1) hv
      (coordinateVector_nonzero m m le_rfl 0)).mpr
    refine ⟨v (Fin.last m), ?_⟩
    ext j
    refine Fin.lastCases ?_ ?_ j
    · simp [coordinateVector]
    · intro k
      simp [coordinateVector, k.isLt, hz k]
  · intro hp
    have he : p = affineChart m m le_rfl 0 := hp
    rw [he]
    apply Set.mem_iInter.mpr
    intro j
    exact (coordinateHyperplane_topAffineChart m j 0).mpr rfl

end P202.ComplexProjective

namespace P202.ComplexProjective

instance spaceSecondCountable (m : ℕ) : SecondCountableTopology (Space m) :=
  (IsOpenQuotientMap.of_isOpenMap_isQuotientMap
    (quotientMap_open m) (quotientMap_quotient m)).secondCountableTopology

instance nonzeroVectorsPathConnected (m : ℕ) : PathConnectedSpace (NonzeroVectors m) := by
  have hdim : Module.finrank ℝ (Fin (m+1) → ℂ) = 2*(m+1) := by
    have h := Module.finrank_mul_finrank ℝ ℂ (Fin (m+1) → ℂ)
    simpa using h.symm
  have hrank : 1 < Module.rank ℝ (Fin (m+1) → ℂ) :=
    Module.one_lt_rank_of_one_lt_finrank (by rw [hdim]; omega)
  apply isPathConnected_iff_pathConnectedSpace.mp
  convert isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : Fin (m+1) → ℂ) using 1
  ext x
  change (x ≠ 0) ↔ x ≠ 0
  rfl

instance spacePathConnected (m : ℕ) : PathConnectedSpace (Space m) :=
  (quotientMap_quotient m).surjective.pathConnectedSpace (quotientMap_continuous m)

end P202.ComplexProjective

namespace P202.ComplexProjectiveRing
open P202Specs.ComplexProjectiveRing P202Specs.SingularChains P202Specs.CupProduct
  P202Specs.CohomologyPairs

lemma homology_free (m n : ℕ) :
    Module.Free ℤ (homology ℤ ℤ (projectiveSpace m) (n : ℤ)) := by
  classical
  by_cases h : ∃ r ≤ m, n = 2*r
  · obtain ⟨e⟩ := (P202.ComplexProjective.homology m n).1 h
    exact Module.Free.of_equiv e.symm
  · haveI := ModuleCat.subsingleton_of_isZero ((P202.ComplexProjective.homology m n).2 h)
    exact Module.Free.of_subsingleton _ _

lemma previousHomology_free (m n : ℕ) :
    Module.Free ℤ ((ordinaryComplex ℤ ℤ (projectiveSpace m)).homology
      (P202Specs.UniversalCoefficientsCohomology.previousDegree n)) := by
  cases n with
  | zero =>
    change Module.Free ℤ ((ordinaryComplex ℤ ℤ (projectiveSpace m)).homology (-1))
    haveI := ModuleCat.subsingleton_of_isZero
      (P202.SingularChains.ordinary_negative_homology ℤ ℤ (projectiveSpace m) (-1) (by omega))
    exact Module.Free.of_subsingleton _ _
  | succ n => exact homology_free m n

lemma evaluation_bijective (m n : ℕ) : Function.Bijective (evaluation m n) := by
  let C := ordinaryComplex ℤ ℤ (projectiveSpace m)
  let k := P202Specs.UniversalCoefficientsCohomology.previousDegree n
  haveI : Module.Free ℤ (C.homology k) := previousHomology_free m n
  haveI : Subsingleton
      (P202Specs.UniversalCoefficientsCohomology.actualExt ℤ ℤ C k) :=
    P103.Ch11.VanishingAndFlatness.ext_projective ℤ (C.homology k) ℤ Module.Projective.of_free
      (P202Specs.UniversalCoefficientsCohomology.AlgebraicExt.resolutionFamily ℤ (C.homology k)).val
      (P202Specs.UniversalCoefficientsCohomology.AlgebraicExt.resolutionFamily ℤ (C.homology k)).property 0
  obtain ⟨α, σ, hα, hexact, hsurj, hσ⟩ :=
    (P202.UniversalCoefficientsCohomology.all_degrees ℤ ℤ).1 (projectiveSpace m) n
  refine ⟨?_, hsurj⟩
  apply (injective_iff_map_eq_zero (evaluation m n)).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := (hexact x).mp hx
  have hz : z = 0 := Subsingleton.elim _ _
  rw [hz]
  exact α.toAddMonoidHom.map_zero

lemma cohomology_groups (m n : ℕ) :
    ((∃ r ≤ m, n = 2*r) → Nonempty (cohomology m n ≃ₗ[ℤ] ℤ)) ∧
    ((¬ ∃ r ≤ m, n = 2*r) → IsZero
      (ordinaryCohomology ℤ ℤ (projectiveSpace m) (n : ℤ))) := by
  let e := LinearEquiv.ofBijective (evaluation m n) (evaluation_bijective m n)
  constructor
  · intro h
    obtain ⟨f⟩ := (P202.ComplexProjective.homology m n).1 h
    exact ⟨e.trans ((LinearEquiv.arrowCongr f (LinearEquiv.refl ℤ ℤ)).trans
      (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ))⟩
  · intro h
    haveI := ModuleCat.subsingleton_of_isZero ((P202.ComplexProjective.homology m n).2 h)
    haveI : Subsingleton (cohomology m n) := e.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _

/-- A value-one integral pairing detects a primitive vector in a rank-one
module. No assumption that the tested homology class is a generator is needed. -/
lemma generates_of_pairing_one {V : Type*} [AddCommGroup V]
    (e : V ≃+ ℤ) (a : V) (χ : V →+ ℤ) (h : χ a = 1) :
    Function.Bijective (fun z : ℤ => z • a) := by
  let b : V := e.symm 1
  have hb (x : V) : x = e x • b := by
    apply e.injective
    simp [b]
  have hχ (x : V) : χ x = e x * χ b := by
    conv_lhs => rw [hb x]
    exact χ.map_zsmul _ _
  have hone : e a * χ b = 1 := (hχ a).symm.trans h
  constructor
  · intro z w hzw
    have hh := congrArg χ hzw
    simpa [h] using hh
  · intro x
    refine ⟨χ x, e.injective ?_⟩
    rw [map_zsmul, hχ]
    change (e x * χ b) * e a = e x
    calc (e x * χ b) * e a = e x * (e a * χ b) := by ring
         _ = e x := by rw [hone, mul_one]

/-- The final algebraic step in the paper's fundamental-class argument.
The evaluation is exactly the ordinary UCT arrow from the fixed chain complex. -/
lemma generator_of_evaluation_one (m n : ℕ) (hn : ∃ r ≤ m, n = 2*r)
    (a : cohomology m n)
    (z : homology ℤ ℤ (projectiveSpace m) (n : ℤ))
    (h : evaluation m n a z = 1) : Function.Bijective (fun t : ℤ => t • a) := by
  obtain ⟨e⟩ := (cohomology_groups m n).1 hn
  exact generates_of_pairing_one e.toAddEquiv a
    (((LinearMap.applyₗ (R := ℤ) z).comp (evaluation m n)).toAddMonoidHom) h

/-- Evaluation of a supported cohomology class on an absolute cycle is
evaluation of the same class on the actual quotient cycle. -/
lemma evaluation_ordinaryImage (P : P202Specs.RelativeSingularChains.Pair) (n : ℕ)
    (a : relativeCohomology ℤ ℤ P (n : ℤ))
    (z : homology ℤ ℤ P.space (n : ℤ)) :
    P202Specs.UniversalCoefficientsCohomology.evaluation ℤ ℤ
      (ordinaryComplex ℤ ℤ P.space) (n : ℤ) (ordinaryImage P n a) z =
        relativeEvaluation P n a (absoluteToRelative P n z) := by
  have h := P202.UniversalCoefficientsCohomology.evaluation_natural ℤ ℤ ℤ
    (P202Specs.RelativeSingularChains.projection (ordinaryFunctor ℤ ℤ) P)
    (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (n : ℤ) a z
  rw [P202.UniversalCoefficientsCohomology.dualMap_id] at h
  exact h

/-- Pair pullback and relative homology pushforward are adjoint under the
fixed cycle pairing. This applies in particular to every normal slice. -/
lemma relativeEvaluation_pullback
    {P Q : P202Specs.RelativeSingularChains.Pair} (f : P ⟶ Q) (n : ℕ)
    (a : relativeCohomology ℤ ℤ Q (n : ℤ))
    (z : P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ P (n : ℤ)) :
    relativeEvaluation P n
      ((relativeCohomologyFunctor ℤ ℤ (n : ℤ)).map f.op a) z =
        relativeEvaluation Q n a
          ((P202Specs.RelativeSingularChains.relativeHomologyFunctor ℤ ℤ (n : ℤ)).map f z) := by
  have h := P202.UniversalCoefficientsCohomology.evaluation_natural ℤ ℤ ℤ
    (P202Specs.RelativeSingularChains.relativeMap (ordinaryFunctor ℤ ℤ) f)
    (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (n : ℤ) a z
  rw [P202.UniversalCoefficientsCohomology.dualMap_id] at h
  exact h

/-- A local value-one calculation gives the required global value one once
the absolute fundamental cycle restricts to that local cycle. -/
lemma evaluation_one_of_localization
    (P : P202Specs.RelativeSingularChains.Pair) (n : ℕ)
    (a : relativeCohomology ℤ ℤ P (n : ℤ))
    (z : homology ℤ ℤ P.space (n : ℤ))
    (o : P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ P (n : ℤ))
    (hz : absoluteToRelative P n z = o)
    (ha : relativeEvaluation P n a o = 1) :
    P202Specs.UniversalCoefficientsCohomology.evaluation ℤ ℤ
      (ordinaryComplex ℤ ℤ P.space) (n : ℤ) (ordinaryImage P n a) z = 1 := by
  rw [evaluation_ordinaryImage, hz, ha]

lemma cohomology_above (m n : ℕ) (h : 2*m < n) : Subsingleton (cohomology m n) := by
  apply ModuleCat.subsingleton_of_isZero
  apply (cohomology_groups m n).2
  rintro ⟨r, hr, rfl⟩
  omega

lemma degreeTwo_nilpotent (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m)) :
    letI := C.gradedRing
    ∀ v : cohomology m 2,
      (DirectSum.of (H ℤ (projectiveSpace m)) 2 v) ^ (m+1) = 0 := by
  letI := C.gradedRing
  intro v
  rw [DirectSum.ofPow]
  haveI : Subsingleton (cohomology m ((m+1) • (2 : ℕ))) :=
    cohomology_above m _ (by simp only [smul_eq_mul]; omega)
  rw [Subsingleton.elim (GradedMonoid.GMonoid.gnpow (m+1) v) 0]
  exact map_zero _

/-- A quotient-ring map for every candidate degree-two generator. Surjectivity
and injectivity still require the primitive-power argument. -/
lemma polynomialMap_exists (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m)) :
    letI := C.gradedRing
    ∀ v : cohomology m 2,
      ∃ f : truncatedPolynomial m →+* totalCohomology m,
        f (polynomialClass m Polynomial.X) =
          DirectSum.of (H ℤ (projectiveSpace m)) 2 v := by
  letI := C.gradedRing
  intro v
  let a : totalCohomology m := DirectSum.of (H ℤ (projectiveSpace m)) 2 v
  let f : Polynomial ℤ →+* totalCohomology m :=
    Polynomial.eval₂RingHom' (Int.castRingHom _) a (fun z => Int.cast_commute z a)
  have hf : truncationIdeal m ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    change f (Polynomial.X ^ (m+1)) = 0
    rw [map_pow]
    simpa [f, a] using degreeTwo_nilpotent m C v
  refine ⟨Ideal.Quotient.lift _ f (fun p hp => hf hp), ?_⟩
  change Polynomial.eval₂ (Int.castRingHom _) a Polynomial.X = a
  exact Polynomial.eval₂_X _ _

/-- A rank-one additive group forces the ring unit to be primitive. -/
lemma intCast_bijective_of_addEquiv {A : Type*} [Ring A] (e : A ≃+ ℤ) :
    Function.Bijective (Int.castRingHom A) := by
  let b : A := e.symm 1
  have hb (x : A) : x = e x • b := by
    apply e.injective
    rw [map_zsmul]
    simp [b]
  have hone : (1 : ℤ) = e 1 * e (b*b) := by
    have hx : b = (e 1) • (b*b) := by
      calc b = (1 : A)*b := (one_mul b).symm
           _ = (e 1 • b)*b := by rw [← hb 1]
           _ = (e 1) • (b*b) := smul_mul_assoc _ _ _
    have hh : e b = e ((e 1) • (b*b)) := congrArg e hx
    rw [map_zsmul] at hh
    have hb1 : e b = 1 := e.apply_symm_apply 1
    rw [hb1] at hh
    exact hh
  have hz : e 1 = 1 ∨ e 1 = -1 := by
    have := Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hone.symm)
    exact this
  constructor
  · intro x y hxy
    have h : x * e 1 = y * e 1 := by
      have hh := congrArg e hxy
      change e (x : A) = e (y : A) at hh
      rw [← zsmul_one (R := A) x, ← zsmul_one (R := A) y, map_zsmul, map_zsmul] at hh
      exact hh
    rcases hz with hz | hz <;> simpa [hz] using h
  · intro x
    rcases hz with hz | hz
    · refine ⟨e x, ?_⟩
      apply e.injective
      change e (e x : A) = e x
      rw [← zsmul_one (R := A) (e x), map_zsmul, hz]
      simp
    · refine ⟨- e x, ?_⟩
      apply e.injective
      change e ((-e x : ℤ) : A) = e x
      rw [← zsmul_one (R := A) (-e x), map_zsmul, hz]
      simp

def pointDegreeZeroEquiv : totalCohomology 0 ≃+ cohomology 0 0 :=
  AddEquiv.ofBijective
    (DirectSum.component ℤ ℕ (H ℤ (projectiveSpace 0)) 0).toAddMonoidHom (by
    constructor
    · intro x y hxy
      apply DFinsupp.ext
      intro n
      cases n with
      | zero => exact hxy
      | succ n =>
        haveI : Subsingleton (cohomology 0 (n+1)) := cohomology_above 0 _ (by omega)
        exact Subsingleton.elim _ _
    · intro a
      exact ⟨DirectSum.lof ℤ ℕ (H ℤ (projectiveSpace 0)) 0 a,
        DirectSum.component.lof_self ℤ 0 a⟩)

def pointTotalEquiv : totalCohomology 0 ≃+ ℤ :=
  pointDegreeZeroEquiv.trans
    (Classical.choice ((cohomology_groups 0 0).1 ⟨0, by omega, by omega⟩)).toAddEquiv

def pointRingEquiv (C : CohomologyRing ℤ (projectiveSpace 0)) :
    letI := C.gradedRing
    ℤ ≃+* totalCohomology 0 := by
  letI := C.gradedRing
  exact RingEquiv.ofBijective (Int.castRingHom _)
    (intCast_bijective_of_addEquiv pointTotalEquiv)

def pointPolynomialEquiv : truncatedPolynomial 0 ≃+* ℤ :=
  (Ideal.quotEquivOfEq (show truncationIdeal 0 =
      Ideal.span ({Polynomial.X - Polynomial.C (0 : ℤ)} : Set (Polynomial ℤ)) by
        simp [truncationIdeal])).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (0 : ℤ)).toRingEquiv

lemma pointPolynomialEquiv_X : pointPolynomialEquiv (polynomialClass 0 Polynomial.X) = 0 := by
  change Polynomial.eval (0 : ℤ) Polynomial.X = 0
  exact Polynomial.eval_X

lemma pointPresentation_exists (C : CohomologyRing ℤ (projectiveSpace 0)) :
    letI := C.gradedRing
    ∃ e : truncatedPolynomial 0 ≃+* totalCohomology 0,
      e (polynomialClass 0 Polynomial.X) = 0 := by
  letI := C.gradedRing
  refine ⟨pointPolynomialEquiv.trans (pointRingEquiv C), ?_⟩
  change pointRingEquiv C (pointPolynomialEquiv (polynomialClass 0 Polynomial.X)) = 0
  rw [pointPolynomialEquiv_X, map_zero]

/-- Distinct homogeneous primitive powers detect every coefficient in a
truncated polynomial. The source power basis is the actual quotient by X^(m+1). -/
lemma polynomialMap_injective_of_primitivePowers
    (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2)
    (hv : PrimitivePowers m C v) :
    letI := C.gradedRing
    ∀ f : truncatedPolynomial m →+* totalCohomology m,
      f (polynomialClass m Polynomial.X) = DirectSum.of (H ℤ (projectiveSpace m)) 2 v →
      Function.Injective f := by
  classical
  letI := C.gradedRing
  intro f hf
  let P := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow (m+1) (R := ℤ))
  have hdim : P.dim = m+1 := by simp [P]
  have hb (i : Fin P.dim) :
      f (P.basis i) = (DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^i.val := by
    rw [P.basis_eq_pow, map_pow]
    change (f (polynomialClass m Polynomial.X))^i.val = _
    rw [hf]
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  have hsum : ∑ i : Fin P.dim, (P.basis.repr x i) •
      (DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^i.val = 0 := by
    have h := congrArg f (P.basis.sum_repr x)
    simpa only [map_sum, map_zsmul, hb, hx] using h
  have hcoeff : ∀ i : Fin P.dim, P.basis.repr x i = 0 := by
    intro i
    have hi : i.val ≤ m := by have := i.isLt; omega
    obtain ⟨b, hgen, hp⟩ := hv i.val hi
    have hproj := congrArg (DirectSum.component ℤ ℕ (H ℤ (projectiveSpace m)) (2*i.val)) hsum
    rw [map_sum, map_zero] at hproj
    have hs : (∑ j : Fin P.dim,
        (DirectSum.component ℤ ℕ (H ℤ (projectiveSpace m)) (2*i.val))
          ((P.basis.repr x j) • (DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^j.val)) =
        (P.basis.repr x i) • b := by
      rw [Finset.sum_eq_single i]
      · rw [map_zsmul, hp]
        exact congrArg ((P.basis.repr x i) • ·) (DirectSum.component.lof_self ℤ (2*i.val) b)
      · intro j _ hji
        have hj : j.val ≤ m := by have := j.isLt; omega
        obtain ⟨bj, _, hpj⟩ := hv j.val hj
        have hne : 2*j.val ≠ 2*i.val := by
          intro he
          apply hji
          apply Fin.ext
          omega
        rw [map_zsmul, hpj]
        change (P.basis.repr x j) •
          ((DFinsupp.single (2*j.val) bj : totalCohomology m) (2*i.val)) = 0
        rw [DFinsupp.single_eq_of_ne hne.symm]
        change (P.basis.repr x j : ℤ) • (0 : cohomology m (2*i.val)) = 0
        exact zsmul_zero (P.basis.repr x j : ℤ)
      · simp
    rw [hs] at hproj
    apply hgen.1
    simpa only [zero_smul] using hproj
  rw [← P.basis.sum_repr x]
  simp only [hcoeff, zero_smul, Finset.sum_const_zero]

/-- Primitive powers generate the entire direct sum, because the other
homogeneous groups vanish. This includes both degree zero and m=0. -/
lemma polynomialMap_surjective_of_primitivePowers
    (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2)
    (hv : PrimitivePowers m C v) :
    letI := C.gradedRing
    ∀ f : truncatedPolynomial m →+* totalCohomology m,
      f (polynomialClass m Polynomial.X) = DirectSum.of (H ℤ (projectiveSpace m)) 2 v →
      Function.Surjective f := by
  letI := C.gradedRing
  intro f hf x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · exact ⟨0, map_zero f⟩
  · intro n a
    by_cases hn : ∃ i ≤ m, n = 2*i
    · obtain ⟨i, hi, rfl⟩ := hn
      obtain ⟨b, hgen, hp⟩ := hv i hi
      obtain ⟨z, rfl⟩ := hgen.2 a
      refine ⟨z • (polynomialClass m Polynomial.X)^i, ?_⟩
      rw [map_zsmul, map_pow, hf, hp, map_zsmul]
    · haveI := ModuleCat.subsingleton_of_isZero ((cohomology_groups m n).2 hn)
      exact ⟨0, by rw [Subsingleton.elim a 0, map_zero, map_zero]⟩
  · rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a+b, map_add f a b⟩

/-- Algebraic assembly of the general presentation. Its only additional
hypothesis is the still-to-be-proved geometric primitive-powers conclusion. -/
lemma presentation_of_primitivePowers (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2)
    (hv : PrimitivePowers m C v) :
    letI := C.gradedRing
    ∃ e : truncatedPolynomial m ≃+* totalCohomology m,
      e (polynomialClass m Polynomial.X) = DirectSum.of (H ℤ (projectiveSpace m)) 2 v ∧
      ∀ i : ℕ, i ≤ m → ∃ b : cohomology m (2*i),
        Function.Bijective (fun z : ℤ => z • b) ∧
        e ((polynomialClass m Polynomial.X)^i) =
          DirectSum.of (H ℤ (projectiveSpace m)) (2*i) b := by
  letI := C.gradedRing
  obtain ⟨f, hf⟩ := polynomialMap_exists m C v
  let e := RingEquiv.ofBijective f
    ⟨polynomialMap_injective_of_primitivePowers m C v hv f hf,
      polynomialMap_surjective_of_primitivePowers m C v hv f hf⟩
  refine ⟨e, hf, ?_⟩
  intro i hi
  obtain ⟨b, hgen, hp⟩ := hv i hi
  refine ⟨b, hgen, ?_⟩
  change f ((polynomialClass m Polynomial.X)^i) = _
  rw [map_pow, hf, hp]

open P202.ComplexProjective P202.Cellular P202Specs.CellularComparison

/-- The standard coordinate CP^r is exactly the (2r+1)-skeleton; the extra
odd dimension adds no cells and permits stabilization also in degree 2r. -/
lemma standardSkeleton_eq_lowerSpace (m r : ℕ) :
    @P202.Cellular.skeletonLT (P202.ComplexProjective.Space m) _
      (P202.ComplexProjective.standardCellStructure m) (2*r+2) =
      P202.ComplexProjective.lowerSpace m (r+1) := by
  rw [lowerSpace_partition]
  ext p
  simp only [skeletonLT, Set.mem_iUnion]
  constructor
  · rintro ⟨d, hd, c, hp⟩
    have hc := c.property
    exact ⟨c.val, by change d = 2*c.val.val at hc; omega,
      (standard_openCell m d c) ▸ hp⟩
  · rintro ⟨j, hj, hp⟩
    refine ⟨2*j.val, by omega, ⟨j,rfl⟩, ?_⟩
    rw [standard_openCell]
    exact hp

/-- The literal zero-padding inclusion, bundled using the accepted topology proof. -/
def standardInclusion (m r : ℕ) (h : r ≤ m) : projectiveSpace r ⟶ projectiveSpace m :=
  TopCat.ofHom ⟨P202.ComplexProjective.inclusion m r h,
    P202.ComplexProjective.inclusion_continuous m r h⟩

/-- Restriction to a standard projective subspace is an isomorphism on integral
homology throughout its dimension, including the top degree and CP^0. -/
lemma inclusion_homology_isIso (m r : ℕ) (h : r ≤ m) (n : ℕ) (hn : n ≤ 2*r) :
    IsIso ((homologyFunctor ℤ ℤ (n : ℤ)).map (standardInclusion m r h)) := by
  obtain ⟨C, hC⟩ := standardCW m
  letI : CWStructure (Space m) := C
  have hs : Set.range (inclusion m r h) = skeletonLT (Space m) (2*r+2) := by
    change Set.range (inclusion m r h) = @skeletonLT (Space m) _ C.toCellStructure (2*r+2)
    rw [hC, standardSkeleton_eq_lowerSpace, inclusion_range]
  let e : Space r ≃ₜ skeletonLT (Space m) (2*r+2) :=
    (inclusion_embedding m r h).toHomeomorph.trans (Homeomorph.setCongr hs)
  have he : (TopCat.isoOfHomeo e).hom ≫ skeletonToSpace (Space m) (2*r+2) =
      standardInclusion m r h := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  haveI := P202.Homology.CellularComparison.skeletalStabilization
    (Space m) ℤ ℤ n (2*r+2) (by omega)
  rw [← he, Functor.map_comp]
  infer_instance

/-- Evaluation commutes with the actual induced maps on the projective quotients. -/
lemma evaluation_pullback {m r : ℕ} (f : projectiveSpace r ⟶ projectiveSpace m)
    (n : ℕ) (a : cohomology m n)
    (z : homology ℤ ℤ (projectiveSpace r) (n : ℤ)) :
    P202Specs.ComplexProjectiveRing.evaluation r n (hPullback ℤ f n a) z =
      P202Specs.ComplexProjectiveRing.evaluation m n a
        ((homologyFunctor ℤ ℤ (n : ℤ)).map f z) := by
  have h := P202.UniversalCoefficientsCohomology.evaluation_natural ℤ ℤ ℤ
    ((ordinaryFunctor ℤ ℤ).map f) (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (n : ℤ) a z
  rw [P202.UniversalCoefficientsCohomology.dualMap_id] at h
  exact h

/-- The UCT square transfers the skeletal inclusion isomorphism to the
specified ordinary cohomology pullback, rather than to an abstract group map. -/
lemma inclusion_cohomology_bijective (m r : ℕ) (h : r ≤ m) (n : ℕ) (hn : n ≤ 2*r) :
    Function.Bijective (hPullback ℤ (standardInclusion m r h) n) := by
  let f := standardInclusion m r h
  haveI := inclusion_homology_isIso m r h n hn
  let e := (asIso ((homologyFunctor ℤ ℤ (n : ℤ)).map f)).toLinearEquiv
  let er := LinearEquiv.ofBijective (P202Specs.ComplexProjectiveRing.evaluation r n)
    (evaluation_bijective r n)
  let em := LinearEquiv.ofBijective (P202Specs.ComplexProjectiveRing.evaluation m n)
    (evaluation_bijective m n)
  let k : cohomology m n ≃ₗ[ℤ] cohomology r n :=
    em.trans ((LinearEquiv.arrowCongr e.symm (LinearEquiv.refl ℤ ℤ)).trans er.symm)
  have hk : (k : cohomology m n → cohomology r n) = hPullback ℤ f n := by
    funext a
    apply er.injective
    apply LinearMap.ext
    intro z
    change er (er.symm _) z = _
    rw [LinearEquiv.apply_symm_apply]
    exact (evaluation_pullback f n a z).symm
  rw [← hk]
  exact k.bijective

/-- The value-one calculation on CP^i detects the primitive restricted power;
restriction is an isomorphism, so the original power is primitive in CP^m. -/
lemma generator_of_restriction_evaluation_one (m i : ℕ) (hi : i ≤ m)
    (a : cohomology m (2*i))
    (z : P202Specs.SingularChains.homology ℤ ℤ (projectiveSpace i) ((2*i : ℕ) : ℤ))
    (ha : P202Specs.ComplexProjectiveRing.evaluation i (2*i)
      (hPullback ℤ (standardInclusion m i hi) (2*i) a) z = 1) :
    Function.Bijective (fun t : ℤ => t • a) := by
  let f := hPullback ℤ (standardInclusion m i hi) (2*i)
  have hf := inclusion_cohomology_bijective m i hi (2*i) le_rfl
  have hgen := generator_of_evaluation_one i (2*i) ⟨i,le_rfl,rfl⟩ (f a) z ha
  apply (Function.Bijective.of_comp_iff' hf (fun t : ℤ => t • a)).mp
  have heq : (fun t : ℤ => t • f a) = f ∘ (fun t : ℤ => t • a) := by
    funext t
    exact (map_zsmul f t a).symm
  rw [← heq]
  exact hgen


open P202Specs.ComplexProjectiveRing P202Specs.SingularChains P202Specs.CupProduct
  P202Specs.CohomologyPairs

/-- The ordinary homogeneous class of a power, with no primitivity assumed. -/
def homogeneousPower (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m))
    (v : cohomology m 2) (i : ℕ) : cohomology m (2*i) :=
  letI := C.gradedRing
  DirectSum.component ℤ ℕ (H ℤ (projectiveSpace m)) (2*i)
    ((DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^i)

lemma of_homogeneousPower (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m))
    (v : cohomology m 2) (i : ℕ) :
    letI := C.gradedRing
    DirectSum.of (H ℤ (projectiveSpace m)) (2*i) (homogeneousPower m C v i) =
      (DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^i := by
  letI := C.gradedRing
  change DirectSum.of (H ℤ (projectiveSpace m)) (2*i)
    (DirectSum.component ℤ ℕ (H ℤ (projectiveSpace m)) (2*i)
      ((DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^i)) = _
  simp only [DirectSum.ofPow]
  have hi : i • (2 : ℕ) = 2*i := by simp [smul_eq_mul, Nat.mul_comm]
  rw [← hi]
  exact congrArg (DirectSum.of (H ℤ (projectiveSpace m)) (i • (2 : ℕ)))
    (DirectSum.component.lof_self ℤ (i • (2 : ℕ)) (GradedMonoid.GMonoid.gnpow i v))

lemma homogeneousPower_eq_iff (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m))
    (v : cohomology m 2) (i : ℕ) (b : cohomology m (2*i)) :
    letI := C.gradedRing
    homogeneousPower m C v i = b ↔
      (DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^i =
        DirectSum.of (H ℤ (projectiveSpace m)) (2*i) b := by
  letI := C.gradedRing
  rw [← of_homogeneousPower]
  exact (DirectSum.of_injective (β := H ℤ (projectiveSpace m)) (2*i)).eq_iff.symm

lemma homogeneousPower_pullback (N : NaturalCohomologyRing ℤ)
    {m r : ℕ} (f : projectiveSpace r ⟶ projectiveSpace m)
    (v : cohomology m 2) (i : ℕ) :
    hPullback ℤ f (2*i) (homogeneousPower m (N.ring _) v i) =
      homogeneousPower r (N.ring _) (hPullback ℤ f 2 v) i := by
  letI := (N.ring (projectiveSpace m)).gradedRing
  letI := (N.ring (projectiveSpace m)).algebra
  letI := (N.ring (projectiveSpace r)).gradedRing
  letI := (N.ring (projectiveSpace r)).algebra
  apply DirectSum.of_injective (β := H ℤ (projectiveSpace r)) (2*i)
  rw [← N.pullback_homogeneous, of_homogeneousPower, of_homogeneousPower,
    map_pow, N.pullback_homogeneous]

lemma primitivePowers_iff_homogeneousPower (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2) :
    PrimitivePowers m C v ↔ ∀ i : ℕ, i ≤ m →
      Function.Bijective (fun t : ℤ => t • homogeneousPower m C v i) := by
  letI := C.gradedRing
  constructor
  · intro h i hi
    obtain ⟨b,hb,hp⟩ := h i hi
    rwa [((homogeneousPower_eq_iff m C v i b).mpr hp)]
  · intro h i hi
    exact ⟨homogeneousPower m C v i, h i hi, (of_homogeneousPower m C v i).symm⟩

lemma primitivePowers_of_restriction_evaluation_one (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2)
    (h : ∀ i : ℕ, (hi : i ≤ m) →
      ∃ z : homology ℤ ℤ (projectiveSpace i) ((2*i : ℕ) : ℤ),
        P202Specs.ComplexProjectiveRing.evaluation i (2*i)
          (hPullback ℤ (standardInclusion m i hi) (2*i) (homogeneousPower m C v i)) z = 1) :
    PrimitivePowers m C v := by
  apply (primitivePowers_iff_homogeneousPower m C v).mpr
  intro i hi
  obtain ⟨z,hz⟩ := h i hi
  exact generator_of_restriction_evaluation_one m i hi (homogeneousPower m C v i) z hz

/-- A primitive cohomology class admits a value-one integral homology pairing.
The UCT evaluation, rather than an abstract identification with a dual, is used. -/
lemma evaluation_one_of_generator (m n : ℕ) (hn : ∃ r ≤ m, n = 2*r)
    (a : cohomology m n) (ha : Function.Bijective (fun t : ℤ => t • a)) :
    ∃ z : homology ℤ ℤ (projectiveSpace m) (n : ℤ),
      P202Specs.ComplexProjectiveRing.evaluation m n a z = 1 := by
  obtain ⟨g⟩ := (P202.ComplexProjective.homology m n).1 hn
  let e := LinearEquiv.ofBijective (P202Specs.ComplexProjectiveRing.evaluation m n)
    (evaluation_bijective m n)
  let k : cohomology m n ≃ₗ[ℤ] ℤ :=
    e.trans ((LinearEquiv.arrowCongr g (LinearEquiv.refl ℤ ℤ)).trans
      (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ))
  obtain ⟨t,ht⟩ := ha.2 (k.symm 1)
  refine ⟨t • g.symm 1, ?_⟩
  have he := congrArg k ht
  rw [LinearEquiv.apply_symm_apply, map_zsmul] at he
  change t • (P202Specs.ComplexProjectiveRing.evaluation m n a (g.symm 1)) = 1 at he
  exact (map_zsmul (P202Specs.ComplexProjectiveRing.evaluation m n a) t (g.symm 1)).trans he

lemma primitivePowers_iff_restriction_evaluation_one (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2) :
    PrimitivePowers m C v ↔
    ∀ i : ℕ, (hi : i ≤ m) →
      ∃ z : homology ℤ ℤ (projectiveSpace i) ((2*i : ℕ) : ℤ),
        P202Specs.ComplexProjectiveRing.evaluation i (2*i)
          (hPullback ℤ (standardInclusion m i hi) (2*i) (homogeneousPower m C v i)) z = 1 := by
  constructor
  · intro h i hi
    have hb := (primitivePowers_iff_homogeneousPower m C v).mp h i hi
    have hf := inclusion_cohomology_bijective m i hi (2*i) le_rfl
    apply evaluation_one_of_generator i (2*i) ⟨i,le_rfl,rfl⟩
    have heq :
        (fun t : ℤ => t • hPullback ℤ (standardInclusion m i hi) (2*i)
          (homogeneousPower m C v i)) =
        hPullback ℤ (standardInclusion m i hi) (2*i) ∘
          (fun t : ℤ => t • homogeneousPower m C v i) := by
      funext t
      exact (map_zsmul _ _ _).symm
    rw [heq]
    exact hf.comp hb
  · exact primitivePowers_of_restriction_evaluation_one m C v

lemma homogeneousPower_zero (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m))
    (v : cohomology m 2) :
    letI := C.gradedRing
    homogeneousPower m C v 0 = (1 : cohomology m 0) := by
  letI := C.gradedRing
  apply DirectSum.of_injective (β := H ℤ (projectiveSpace m)) 0
  simpa only [Nat.mul_zero, pow_zero, DirectSum.of_zero_one] using
    of_homogeneousPower m C v 0

lemma homogeneousPower_zero_primitive (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2) :
    Function.Bijective (fun t : ℤ => t • homogeneousPower m C v 0) := by
  letI := C.gradedRing
  obtain ⟨e⟩ := (cohomology_groups m 0).1 ⟨0, Nat.zero_le m, rfl⟩
  have ha := intCast_bijective_of_addEquiv e.toAddEquiv
  change Function.Bijective (fun t : ℤ => (t : cohomology m 0)) at ha
  simpa only [homogeneousPower_zero, zsmul_one] using ha

lemma point_primitivePowers (C : CohomologyRing ℤ (projectiveSpace 0))
    (v : cohomology 0 2) : PrimitivePowers 0 C v := by
  apply (primitivePowers_iff_homogeneousPower 0 C v).mpr
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  exact homogeneousPower_zero_primitive 0 C v

/-- Only the positive powers need a geometric evaluation calculation;
the nullary power is the primitive unit in degree zero. -/
lemma primitivePowers_of_positive_restriction_evaluation_one (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2)
    (h : ∀ i : ℕ, 0 < i → (hi : i ≤ m) →
      ∃ z : homology ℤ ℤ (projectiveSpace i) ((2*i : ℕ) : ℤ),
        P202Specs.ComplexProjectiveRing.evaluation i (2*i)
          (hPullback ℤ (standardInclusion m i hi) (2*i) (homogeneousPower m C v i)) z = 1) :
    PrimitivePowers m C v := by
  apply (primitivePowers_iff_homogeneousPower m C v).mpr
  intro i hi
  cases i with
  | zero => exact homogeneousPower_zero_primitive m C v
  | succ i =>
    obtain ⟨z,hz⟩ := h (i+1) (by omega) hi
    exact generator_of_restriction_evaluation_one m (i+1) hi _ z hz

lemma pointPresentation_with_powers (C : CohomologyRing ℤ (projectiveSpace 0)) :
    letI := C.gradedRing
    ∃ (v : cohomology 0 2) (e : truncatedPolynomial 0 ≃+* totalCohomology 0),
      e (polynomialClass 0 Polynomial.X) = DirectSum.of (H ℤ (projectiveSpace 0)) 2 v ∧
      ∀ i : ℕ, i ≤ 0 → ∃ b : cohomology 0 (2*i),
        Function.Bijective (fun z : ℤ => z • b) ∧
        e ((polynomialClass 0 Polynomial.X)^i) =
          DirectSum.of (H ℤ (projectiveSpace 0)) (2*i) b := by
  letI := C.gradedRing
  obtain ⟨e,he,hp⟩ := presentation_of_primitivePowers 0 C 0 (point_primitivePowers C 0)
  exact ⟨0,e,he,hp⟩


open P202Specs.RelativeSingularChains P202Specs.LocalOrientation P202Specs.CompactOrientation

/-- The ordinary fundamental class has the prescribed value in the actual local pair. -/
lemma fundamental_toLocal {i : ℕ} (d : ComplexFundamentalData i) (x : Space i) :
    absoluteToRelative (localPair (Space i) x) (2*i) d.fundamental = d.orientation.val x := by
  have hc : projection (ordinaryFunctor ℤ ℤ) (supportedPair (Space i) Set.univ) ≫
      relativeMap (ordinaryFunctor ℤ ℤ) (pointMap (Set.mem_univ x)) =
      projection (ordinaryFunctor ℤ ℤ) (localPair (Space i) x) := by
    have h := projection_map (ordinaryFunctor ℤ ℤ) (pointMap (Set.mem_univ x))
    change _ = (ordinaryFunctor ℤ ℤ).map (𝟙 (projectiveSpace i)) ≫ _ at h
    rw [(ordinaryFunctor ℤ ℤ).map_id, Category.id_comp] at h
    exact h
  change (HomologicalComplex.homologyMap
    (projection (ordinaryFunctor ℤ ℤ) (localPair (Space i) x)) ((2*i : ℕ) : ℤ)).hom
      d.fundamental = _
  rw [← hc, HomologicalComplex.homologyMap_comp]
  exact d.fundamental_values x (Set.mem_univ x)

/-- Local evaluation one, with the specified positive complex orientation,
becomes global evaluation one on its ordinary fundamental class. -/
lemma fundamental_evaluation_one {i : ℕ} (d : ComplexFundamentalData i)
    (a : relativeCohomology ℤ ℤ
      (localPair (P202.ComplexProjective.Space i) (projectiveOrigin i)) ((2*i : ℕ) : ℤ))
    (ha : relativeEvaluation _ (2*i) a (d.orientation.val (projectiveOrigin i)) = 1) :
    P202Specs.ComplexProjectiveRing.evaluation i (2*i)
      (ordinaryImage (localPair (P202.ComplexProjective.Space i) (projectiveOrigin i))
        (2*i) a) d.fundamental = 1 := by
  exact evaluation_one_of_localization
    (localPair (P202.ComplexProjective.Space i) (projectiveOrigin i)) (2*i) a
    d.fundamental (d.orientation.val (projectiveOrigin i))
    (fundamental_toLocal d (projectiveOrigin i)) ha


/-- The precise geometric conclusion supplies primitive powers through the
actual restriction maps and their value-one fundamental-class evaluations. -/
lemma primitivePowers_of_geometricGenerator (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2)
    (hv : GeometricGenerator m C v) : PrimitivePowers m C v := by
  letI := C.gradedRing
  intro i hi
  obtain ⟨ι, d, a, b, hι, _, _, hp, _, hev⟩ := hv.2.2 i hi
  have hiota : ι = standardInclusion m i hi := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact hι
  rw [hiota] at hev
  exact ⟨b, generator_of_restriction_evaluation_one m i hi b d.fundamental hev, hp⟩

/-- Algebraic assembly from the full geometric generator retains every
restriction and fundamental-class evaluation clause. -/
lemma geometricPresentation_of_geometricGenerator :
    geometricGenerator_type → geometricPresentation_type := by
  intro h m C
  letI := C.gradedRing
  obtain ⟨v, hv⟩ := h m C
  obtain ⟨e, he, hp⟩ := presentation_of_primitivePowers m C v
    (primitivePowers_of_geometricGenerator m C v hv)
  exact ⟨v, e, hv, he, hp⟩

/-- Closed additive, truncation and point endpoints on the current upstream interfaces. -/
theorem groups : groups_type := cohomology_groups
theorem evaluation : evaluation_type := evaluation_bijective
theorem truncation : truncation_type := degreeTwo_nilpotent
theorem polynomialMap : polynomialMap_type := polynomialMap_exists
theorem pointPresentation : pointPresentation_type := pointPresentation_exists

end P202.ComplexProjectiveRing


section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Topology Filter
open scoped ContDiff
namespace P202.ComplexProjective

def orderedComplexCoordinates (m : ℕ) : (Fin m → ℂ) ≃ₗ[ℝ] (Fin (2*m) → ℝ) where
  toFun z j := if j.val % 2 = 0 then (z ⟨j.val/2, by omega⟩).re
    else (z ⟨j.val/2, by omega⟩).im
  invFun x j := ⟨x ⟨2*j.val, by omega⟩, x ⟨2*j.val+1, by omega⟩⟩
  left_inv z := by
    funext j
    apply Complex.ext <;> simp [show (2*j.val+1)/2 = j.val by omega]
  right_inv x := by
    ext j
    dsimp
    split_ifs with h
    · have hi : 2*(j.val/2) = j.val := by omega
      simp only [hi]
    · have hi : 2*(j.val/2)+1 = j.val := by omega
      simp only [hi]
  map_add' z w := by
    ext j
    dsimp
    split_ifs <;> simp
  map_smul' r z := by
    ext j
    dsimp
    split_ifs <;> simp

abbrev orderedComplexCoordinatesCLM (m : ℕ) := (orderedComplexCoordinates m).toContinuousLinearEquiv

@[simp] lemma orderedComplexCoordinates_even (m : ℕ) (z : Fin m → ℂ) (j : Fin m) :
    orderedComplexCoordinates m z ⟨2*j.val, by omega⟩ = (z j).re := by
  simp [orderedComplexCoordinates]

@[simp] lemma orderedComplexCoordinates_odd (m : ℕ) (z : Fin m → ℂ) (j : Fin m) :
    orderedComplexCoordinates m z ⟨2*j.val+1, by omega⟩ = (z j).im := by
  simp [orderedComplexCoordinates, show (2*j.val+1)/2 = j.val by omega]

end P202.ComplexProjective

namespace P202.ComplexProjective

/-- Complex ratio coordinates, omitting the chosen homogeneous coordinate. -/
def coordinateRatios {m : ℕ} (i : Fin (m+1)) : Space m → Fin m → ℂ :=
  Projectivization.lift (fun v k => v.val (i.succAbove k) / v.val i) (by
    intro a b t ha
    have ht : t ≠ 0 := by
      intro ht
      apply a.property
      simpa [ht] using ha
    funext k
    simp only [ha, Pi.smul_apply, smul_eq_mul]
    exact mul_div_mul_left _ _ ht)

@[simp] lemma coordinateRatios_mk {m : ℕ} (i : Fin (m+1))
    (v : Fin (m+1) → ℂ) (hv : v ≠ 0) (k : Fin m) :
    coordinateRatios i (mk v hv) k = v (i.succAbove k) / v i := rfl

def coordinateRepresentative {m : ℕ} (i : Fin (m+1)) (z : Fin m → ℂ) : Fin (m+1) → ℂ :=
  @Fin.insertNth m (fun _ => ℂ) i 1 z

@[simp] lemma coordinateRepresentative_same {m : ℕ} (i : Fin (m+1)) (z : Fin m → ℂ) :
    coordinateRepresentative i z i = 1 := Fin.insertNth_apply_same _ _ _

@[simp] lemma coordinateRepresentative_succAbove {m : ℕ} (i : Fin (m+1))
    (z : Fin m → ℂ) (k : Fin m) :
    coordinateRepresentative i z (i.succAbove k) = z k := Fin.insertNth_apply_succAbove _ _ _ _

lemma insertOne_nonzero {m : ℕ} (i : Fin (m+1)) (z : Fin m → ℂ) :
    coordinateRepresentative i z ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

/-- Normalize the selected homogeneous coordinate to 1. -/
def coordinateInverse {m : ℕ} (i : Fin (m+1)) (z : Fin m → ℂ) : Space m :=
  mk (coordinateRepresentative i z) (insertOne_nonzero i z)

@[simp] lemma coordinateRatios_inverse {m : ℕ} (i : Fin (m+1)) (z : Fin m → ℂ) :
    coordinateRatios i (coordinateInverse i z) = z := by
  ext k
  simp [coordinateInverse]

lemma coordinateInverse_mem {m : ℕ} (i : Fin (m+1)) (z : Fin m → ℂ) :
    coordinateInverse i z ∈ (coordinateHyperplane m i)ᶜ := by
  simp [coordinateInverse, coordinateHyperplane_mk]

lemma coordinateInverse_ratios {m : ℕ} (i : Fin (m+1)) (p : Space m)
    (hp : p ∈ (coordinateHyperplane m i)ᶜ) :
    coordinateInverse i (coordinateRatios i p) = p := by
  induction p using Projectivization.ind with | h v hv =>
  change mk v hv ∉ coordinateHyperplane m i at hp
  have hi : v i ≠ 0 := fun h => hp ((coordinateHyperplane_mk i v hv).mpr h)
  apply Eq.symm
  apply (mk_eq_mk' v _ hv (insertOne_nonzero i _)).mpr
  refine ⟨v i, ?_⟩
  ext j
  obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove j
  · simp
  · simp only [Pi.smul_apply, smul_eq_mul, coordinateRepresentative_succAbove]
    change v i * (v (i.succAbove k) / v i) = v (i.succAbove k)
    field_simp [hi]

lemma coordinateRatios_continuousOn {m : ℕ} (i : Fin (m+1)) :
    ContinuousOn (coordinateRatios i) (coordinateHyperplane m i)ᶜ := by
  intro p hp
  induction p using Projectivization.ind with | h v hv =>
  change mk v hv ∉ coordinateHyperplane m i at hp
  have hi : v i ≠ 0 := fun h => hp ((coordinateHyperplane_mk i v hv).mpr h)
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (coordinateRatios i) (quotientMap m ⟨v,hv⟩)
  apply (IsOpenQuotientMap.of_isOpenMap_isQuotientMap (quotientMap_open m)
    (quotientMap_quotient m)).continuousAt_comp_iff.mp
  change ContinuousAt (fun w : NonzeroVectors m =>
    fun k : Fin m => w.val (i.succAbove k) / w.val i) ⟨v,hv⟩
  apply continuousAt_pi.mpr
  intro k
  exact (((continuous_apply _).comp continuous_subtype_val).continuousAt.div
    ((continuous_apply _).comp continuous_subtype_val).continuousAt hi)

lemma coordinateInverse_continuous {m : ℕ} (i : Fin (m+1)) :
    Continuous (coordinateInverse i) := by
  change Continuous (quotientMap m ∘ fun z : Fin m → ℂ =>
    ⟨coordinateRepresentative i z, insertOne_nonzero i z⟩)
  apply (quotientMap_continuous m).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  obtain rfl | ⟨k,rfl⟩ := i.eq_self_or_eq_succAbove j
  · simpa using (continuous_const : Continuous (fun _ : Fin m → ℂ => (1 : ℂ)))
  · simpa using (continuous_apply k : Continuous (fun z : Fin m → ℂ => z k))

/-- The affine chart at any homogeneous coordinate, on the fixed quotient topology. -/
def coordinateChart {m : ℕ} (i : Fin (m+1)) : OpenPartialHomeomorph (Space m) (Fin m → ℂ) where
  toFun := coordinateRatios i
  invFun := coordinateInverse i
  source := (coordinateHyperplane m i)ᶜ
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' z _ := coordinateInverse_mem i z
  left_inv' := coordinateInverse_ratios i
  right_inv' z _ := coordinateRatios_inverse i z
  open_source := (coordinateHyperplane_closed m i).isOpen_compl
  open_target := isOpen_univ
  continuousOn_toFun := coordinateRatios_continuousOn i
  continuousOn_invFun := (coordinateInverse_continuous i).continuousOn

lemma coordinateCharts_cover {m : ℕ} (p : Space m) :
    ∃ i : Fin (m+1), p ∈ (coordinateChart i).source := by
  induction p using Projectivization.ind with | h v hv =>
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  refine ⟨i, ?_⟩
  change mk v hv ∉ coordinateHyperplane m i
  exact fun h => hi ((coordinateHyperplane_mk i v hv).mp h)

/-- Inverse chart followed by another chart is a rational function. -/
def coordinateTransition {m : ℕ} (i j : Fin (m+1)) (z : Fin m → ℂ) : Fin m → ℂ :=
  fun k => coordinateRepresentative i z (j.succAbove k) / coordinateRepresentative i z j

def coordinateOverlap {m : ℕ} (i j : Fin (m+1)) : Set (Fin m → ℂ) :=
  {z | coordinateRepresentative i z j ≠ 0}

lemma coordinateOverlap_ratios {m : ℕ} (i j : Fin (m+1)) (p : Space m)
    (hi : p ∈ (coordinateChart i).source) (hj : p ∈ (coordinateChart j).source) :
    coordinateRatios i p ∈ coordinateOverlap i j := by
  have hh : coordinateInverse i (coordinateRatios i p) ∉ coordinateHyperplane m j := by
    rw [coordinateInverse_ratios i p hi]
    exact hj
  simpa only [coordinateOverlap, mem_ofPred_eq, coordinateInverse, coordinateHyperplane_mk] using hh

lemma coordinateTransition_ratios {m : ℕ} (i j : Fin (m+1)) (p : Space m)
    (hi : p ∈ (coordinateChart i).source) :
    coordinateTransition i j (coordinateRatios i p) = coordinateRatios j p := by
  conv_rhs => rw [← coordinateInverse_ratios i p hi]
  rfl

lemma contDiff_insertOne {m : ℕ} (i : Fin (m+1)) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateRepresentative i) := by
  apply contDiff_pi.mpr
  intro j
  obtain rfl | ⟨k,rfl⟩ := i.eq_self_or_eq_succAbove j
  · simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Fin m → ℂ => (1 : ℂ)))
  · simpa using (contDiff_apply ℝ (fun _ : Fin m => ℂ) k)

lemma coordinateOverlap_open {m : ℕ} (i j : Fin (m+1)) : IsOpen (coordinateOverlap i j) :=
  isOpen_ne_fun ((continuous_apply j).comp (contDiff_insertOne i).continuous) continuous_const

lemma coordinateTransition_contDiffOn {m : ℕ} (i j : Fin (m+1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateTransition i j) (coordinateOverlap i j) := by
  apply contDiffOn_pi.mpr
  intro k
  convert ((contDiff_apply ℝ (fun _ => ℂ) (j.succAbove k)).comp
      (contDiff_insertOne i)).contDiffOn.mul
      ((((contDiff_apply ℝ (fun _ => ℂ) j)).comp
        (contDiff_insertOne i)).contDiffOn.inv (fun _ hz => hz)) using 1
  all_goals rfl


end P202.ComplexProjective

namespace P202.ComplexProjective
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData

/-- The same affine ratio chart, in the ordered real and imaginary coordinates. -/
def realCoordinateChart {m : ℕ} (i : Fin (m+1)) : ModelChart (2*m) .euclidean (Space m) where
  toFun p := ⟨orderedComplexCoordinatesCLM m (coordinateRatios i p), Set.mem_univ _⟩
  invFun y := coordinateInverse i ((orderedComplexCoordinatesCLM m).symm y.val)
  source := (coordinateChart i).source
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' y _ := coordinateInverse_mem i _
  left_inv' p hp := by
    dsimp
    rw [LinearEquiv.symm_apply_apply, coordinateInverse_ratios i p hp]
  right_inv' y _ := by
    apply Subtype.ext
    dsimp
    rw [coordinateRatios_inverse, LinearEquiv.apply_symm_apply]
  open_source := (coordinateChart i).open_source
  open_target := isOpen_univ
  continuousOn_toFun :=
    Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      ((orderedComplexCoordinatesCLM m).continuous.comp_continuousOn
        (coordinateRatios_continuousOn i))
  continuousOn_invFun := ((coordinateInverse_continuous i).comp
    ((orderedComplexCoordinatesCLM m).symm.continuous.comp continuous_subtype_val)).continuousOn

def realCoordinateOverlap {m : ℕ} (i j : Fin (m+1)) : Set (Fin (2*m) → ℝ) :=
  (orderedComplexCoordinatesCLM m).symm ⁻¹' coordinateOverlap i j

def realCoordinateTransition {m : ℕ} (i j : Fin (m+1))
    (x : Fin (2*m) → ℝ) : Fin (2*m) → ℝ :=
  orderedComplexCoordinatesCLM m
    (coordinateTransition i j ((orderedComplexCoordinatesCLM m).symm x))

lemma realCoordinateOverlap_open {m : ℕ} (i j : Fin (m+1)) :
    IsOpen (realCoordinateOverlap i j) :=
  (coordinateOverlap_open i j).preimage (orderedComplexCoordinatesCLM m).symm.continuous

lemma realCoordinateTransition_contDiffOn {m : ℕ} (i j : Fin (m+1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (realCoordinateTransition i j) (realCoordinateOverlap i j) :=
  (orderedComplexCoordinatesCLM m).contDiff.comp_contDiffOn
    ((coordinateTransition_contDiffOn i j).comp
      (orderedComplexCoordinatesCLM m).symm.contDiff.contDiffOn (fun _ h => h))

lemma realCoordinateChart_germ {m : ℕ} (i j : Fin (m+1)) (p : Space m)
    (hi : p ∈ (realCoordinateChart i).source) (hj : p ∈ (realCoordinateChart j).source) :
    ChartContDiffAt (⊤ : ℕ∞) (realCoordinateChart i) (realCoordinateChart j) id p := by
  refine ⟨realCoordinateOverlap i j, realCoordinateOverlap_open i j, ?_,
    realCoordinateTransition i j, realCoordinateTransition_contDiffOn i j, ?_⟩
  · change (orderedComplexCoordinatesCLM m).symm
      (orderedComplexCoordinatesCLM m (coordinateRatios i p)) ∈ coordinateOverlap i j
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact coordinateOverlap_ratios i j p hi hj
  · filter_upwards [(realCoordinateChart i).open_source.mem_nhds hi] with q hq
    change orderedComplexCoordinatesCLM m
      (coordinateTransition i j ((orderedComplexCoordinatesCLM m).symm
        (orderedComplexCoordinatesCLM m (coordinateRatios i q)))) =
      orderedComplexCoordinatesCLM m (coordinateRatios j q)
    rw [ContinuousLinearEquiv.symm_apply_apply, coordinateTransition_ratios i j q hq]

/-- Standard affine charts on the adopted complex projective quotient. -/
def projectiveCoordinateAtlas (m : ℕ) : Set (ModelChart (2*m) .euclidean (Space m)) :=
  Set.range (@realCoordinateChart m)

lemma projectiveCoordinateAtlas_isContDiffAtlas (m : ℕ) :
    IsContDiffAtlas (⊤ : ℕ∞) (projectiveCoordinateAtlas m) := by
  constructor
  · intro p
    obtain ⟨i,hi⟩ := coordinateCharts_cover p
    exact ⟨realCoordinateChart i, ⟨i,rfl⟩, hi⟩
  · rintro c ⟨i,rfl⟩ d ⟨j,rfl⟩
    exact SmoothManifolds.contDiffCompatible_of_germs
      (realCoordinateChart_germ i j) (realCoordinateChart_germ j i)

/-- The standard real dimension 2m smooth structure on the actual quotient CP^m. -/
def projectiveSmoothManifold (m : ℕ) : SmoothManifold (2*m) .euclidean (Space m) :=
  ⟨⟨inferInstance, inferInstance, projectiveCoordinateAtlas m,
      (projectiveCoordinateAtlas_isContDiffAtlas m).1⟩,
    ⟨_, SmoothManifolds.maximalExtension_isMaximal (projectiveCoordinateAtlas_isContDiffAtlas m)⟩⟩

lemma realCoordinateChart_mem_smoothStructure {m : ℕ} (i : Fin (m+1)) :
    realCoordinateChart i ∈ (projectiveSmoothManifold m).smoothStructure.val :=
  SmoothManifolds.subset_maximalExtension (projectiveCoordinateAtlas_isContDiffAtlas m) ⟨i,rfl⟩

end P202.ComplexProjective

namespace P202.ComplexProjective
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData

def projectiveLinearMap {m n : ℕ}
    (f : (Fin (m+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ)) (hf : Function.Injective f)
    (p : Space m) : Space n := Projectivization.map f hf p

lemma projectiveLinearMap_continuous {m n : ℕ}
    (f : (Fin (m+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ)) (hf : Function.Injective f) :
    Continuous (projectiveLinearMap f hf) := by
  apply (quotientMap_quotient m).continuous_iff.mpr
  change Continuous (quotientMap n ∘ fun v : NonzeroVectors m =>
    ⟨f v.val, fun h => v.property (hf (by simpa using h))⟩)
  exact (quotientMap_continuous n).comp
    ((f.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _)

def linearCoordinateTransition {m n : ℕ}
    (f : (Fin (m+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ))
    (i : Fin (m+1)) (j : Fin (n+1)) (z : Fin m → ℂ) : Fin n → ℂ :=
  fun k => f (coordinateRepresentative i z) (j.succAbove k) /
    f (coordinateRepresentative i z) j

def linearCoordinateOverlap {m n : ℕ}
    (f : (Fin (m+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ))
    (i : Fin (m+1)) (j : Fin (n+1)) : Set (Fin m → ℂ) :=
  {z | f (coordinateRepresentative i z) j ≠ 0}

lemma linearCoordinateOverlap_open {m n : ℕ}
    (f : (Fin (m+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ))
    (i : Fin (m+1)) (j : Fin (n+1)) : IsOpen (linearCoordinateOverlap f i j) :=
  isOpen_ne_fun ((continuous_apply j).comp
    (f.continuous_of_finiteDimensional.comp (contDiff_insertOne i).continuous)) continuous_const

lemma linearCoordinateTransition_contDiffOn {m n : ℕ}
    (f : (Fin (m+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ))
    (i : Fin (m+1)) (j : Fin (n+1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (linearCoordinateTransition f i j) (linearCoordinateOverlap f i j) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z => f (coordinateRepresentative i z)) :=
    (f.restrictScalars ℝ).toContinuousLinearMap.contDiff.comp (contDiff_insertOne i)
  apply contDiffOn_pi.mpr
  intro k
  convert ((contDiff_apply ℝ (fun _ => ℂ) (j.succAbove k)).comp hF).contDiffOn.mul
    ((((contDiff_apply ℝ (fun _ => ℂ) j)).comp hF).contDiffOn.inv (fun _ hz => hz)) using 1
  all_goals rfl

lemma linearCoordinateTransition_ratios {m n : ℕ}
    (f : (Fin (m+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ)) (hf : Function.Injective f)
    (i : Fin (m+1)) (j : Fin (n+1)) (p : Space m)
    (hi : p ∈ (coordinateChart i).source) :
    linearCoordinateTransition f i j (coordinateRatios i p) =
      coordinateRatios j (projectiveLinearMap f hf p) := by
  conv_rhs => rw [← coordinateInverse_ratios i p hi]
  rfl

lemma linearCoordinateOverlap_ratios {m n : ℕ}
    (f : (Fin (m+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ)) (hf : Function.Injective f)
    (i : Fin (m+1)) (j : Fin (n+1)) (p : Space m)
    (hi : p ∈ (coordinateChart i).source)
    (hj : projectiveLinearMap f hf p ∈ (coordinateChart j).source) :
    coordinateRatios i p ∈ linearCoordinateOverlap f i j := by
  rw [← coordinateInverse_ratios i p hi] at hj
  change mk (f (coordinateRepresentative i (coordinateRatios i p))) _ ∉
    coordinateHyperplane n j at hj
  exact fun h => hj ((coordinateHyperplane_mk _ _ _).mpr h)

/-- Every injective complex linear map induces a smooth map of the fixed projective quotients. -/
lemma projectiveLinearMap_smooth {m n : ℕ}
    (f : (Fin (m+1) → ℂ) →ₗ[ℂ] (Fin (n+1) → ℂ)) (hf : Function.Injective f) :
    IsSmoothMap (projectiveSmoothManifold m) (projectiveSmoothManifold n)
      (projectiveLinearMap f hf) := by
  change ManifoldContDiff (⊤ : ℕ∞) (maximalExtension _ (projectiveCoordinateAtlas m))
    (maximalExtension _ (projectiveCoordinateAtlas n)) _
  apply (SmoothManifolds.manifoldContDiff_maximalExtension_iff _ _ _
    (projectiveCoordinateAtlas_isContDiffAtlas m) (projectiveCoordinateAtlas_isContDiffAtlas n) _).mpr
  intro p
  refine ⟨(projectiveLinearMap_continuous f hf).continuousAt, ?_⟩
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hi hj
  let U := (orderedComplexCoordinatesCLM m).symm ⁻¹' linearCoordinateOverlap f i j
  let F := fun x : Fin (2*m) → ℝ => orderedComplexCoordinatesCLM n
    (linearCoordinateTransition f i j ((orderedComplexCoordinatesCLM m).symm x))
  refine ⟨U, (linearCoordinateOverlap_open f i j).preimage
    (orderedComplexCoordinatesCLM m).symm.continuous, ?_, F, ?_, ?_⟩
  · change (orderedComplexCoordinatesCLM m).symm
      (orderedComplexCoordinatesCLM m (coordinateRatios i p)) ∈ linearCoordinateOverlap f i j
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact linearCoordinateOverlap_ratios f hf i j p hi hj
  · exact (orderedComplexCoordinatesCLM n).contDiff.comp_contDiffOn
      ((linearCoordinateTransition_contDiffOn f i j).comp
        (orderedComplexCoordinatesCLM m).symm.contDiff.contDiffOn (fun _ h => h))
  · filter_upwards [(realCoordinateChart i).open_source.mem_nhds hi] with q hq
    change orderedComplexCoordinatesCLM n
      (linearCoordinateTransition f i j ((orderedComplexCoordinatesCLM m).symm
        (orderedComplexCoordinatesCLM m (coordinateRatios i q)))) =
      orderedComplexCoordinatesCLM n (coordinateRatios j (projectiveLinearMap f hf q))
    rw [ContinuousLinearEquiv.symm_apply_apply, linearCoordinateTransition_ratios f hf i j q hq]

lemma inclusion_smooth (m r : ℕ) (h : r ≤ m) :
    IsSmoothMap (projectiveSmoothManifold r) (projectiveSmoothManifold m) (inclusion m r h) :=
  projectiveLinearMap_smooth (inclusionVector m r h) (inclusionVector_injective m r h)

end P202.ComplexProjective

namespace P202.ComplexProjective
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.MapClassData SmoothManifolds.FiniteRegularityData

/-- The same homogeneous coordinate index in the larger zero-padded space. -/
def includedIndex (m r : ℕ) (h : r ≤ m) (i : Fin (r+1)) : Fin (m+1) :=
  ⟨i.val, by omega⟩

@[simp] lemma inclusionVector_apply_index (m r : ℕ) (h : r ≤ m)
    (v : Fin (r+1) → ℂ) (i : Fin (r+1)) :
    inclusionVector m r h v (includedIndex m r h i) = v i := by
  simp [inclusionVector, includedIndex, show i.val ≤ r by omega]

lemma includedIndex_injective (m r : ℕ) (h : r ≤ m) :
    Function.Injective (includedIndex m r h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin (m+1) => x.val) hij)

/-- Insert a zero in one coordinate, as an actual linear map. -/
def insertZeroLinear {r : ℕ} (i : Fin (r+1)) : (Fin r → ℂ) →ₗ[ℂ] (Fin (r+1) → ℂ) where
  toFun z := @Fin.insertNth r (fun _ => ℂ) i 0 z
  map_add' z w := by
    ext j
    obtain rfl | ⟨k,rfl⟩ := i.eq_self_or_eq_succAbove j <;> simp
  map_smul' c z := by
    ext j
    obtain rfl | ⟨k,rfl⟩ := i.eq_self_or_eq_succAbove j <;> simp

@[simp] lemma insertZeroLinear_same {r : ℕ} (i : Fin (r+1)) (z : Fin r → ℂ) :
    insertZeroLinear i z i = 0 := by simp [insertZeroLinear]

@[simp] lemma insertZeroLinear_succAbove {r : ℕ} (i : Fin (r+1)) (z : Fin r → ℂ) (k : Fin r) :
    insertZeroLinear i z (i.succAbove k) = z k := by simp [insertZeroLinear]

lemma coordinateRepresentative_eq_zero_of_ne {r : ℕ} (i : Fin (r+1))
    (z : Fin r → ℂ) (j : Fin (r+1)) (hj : j ≠ i) :
    coordinateRepresentative i z j = insertZeroLinear i z j := by
  obtain rfl | ⟨k,rfl⟩ := i.eq_self_or_eq_succAbove j
  · exact (hj rfl).elim
  · simp

/-- In charts with the same selected homogeneous coordinate, zero-padding is linear. -/
def coordinateInclusionLinear (m r : ℕ) (h : r ≤ m) (i : Fin (r+1)) :
    (Fin r → ℂ) →ₗ[ℂ] (Fin m → ℂ) where
  toFun z k := inclusionVector m r h (insertZeroLinear i z) ((includedIndex m r h i).succAbove k)
  map_add' z w := by ext k; simp
  map_smul' c z := by ext k; simp

lemma coordinateInclusionLinear_injective (m r : ℕ) (h : r ≤ m) (i : Fin (r+1)) :
    Function.Injective (coordinateInclusionLinear m r h i) := by
  intro z w he
  ext k
  have hne : includedIndex m r h (i.succAbove k) ≠ includedIndex m r h i :=
    fun hh => Fin.succAbove_ne i k ((includedIndex_injective m r h) hh)
  obtain ⟨l,hl⟩ := Fin.exists_succAbove_eq hne
  have hx := congrFun he l
  change inclusionVector m r h (insertZeroLinear i z) ((includedIndex m r h i).succAbove l) =
    inclusionVector m r h (insertZeroLinear i w) ((includedIndex m r h i).succAbove l) at hx
  simpa only [hl, inclusionVector_apply_index, insertZeroLinear_succAbove] using hx

lemma inclusionVector_representative_eq (m r : ℕ) (h : r ≤ m) (i : Fin (r+1))
    (z : Fin r → ℂ) (t : Fin (m+1)) (ht : t ≠ includedIndex m r h i) :
    inclusionVector m r h (coordinateRepresentative i z) t =
      inclusionVector m r h (insertZeroLinear i z) t := by
  by_cases hr : t.val < r+1
  · have hs : (⟨t.val,hr⟩ : Fin (r+1)) ≠ i := by
      intro hs
      apply ht
      exact Fin.ext (congrArg (fun x : Fin (r+1) => x.val) hs)
    simpa only [inclusionVector, LinearMap.coe_mk, AddHom.coe_mk, hr, dite_true]
      using coordinateRepresentative_eq_zero_of_ne i z ⟨t.val,hr⟩ hs
  · simp [inclusionVector, show ¬ t.val ≤ r by omega]

lemma coordinateRatios_inclusion_inverse (m r : ℕ) (h : r ≤ m) (i : Fin (r+1))
    (z : Fin r → ℂ) :
    coordinateRatios (includedIndex m r h i) (inclusion m r h (coordinateInverse i z)) =
      coordinateInclusionLinear m r h i z := by
  ext k
  change inclusionVector m r h (coordinateRepresentative i z) ((includedIndex m r h i).succAbove k) /
    inclusionVector m r h (coordinateRepresentative i z) (includedIndex m r h i) = _
  rw [inclusionVector_apply_index, coordinateRepresentative_same, div_one]
  exact inclusionVector_representative_eq m r h i z _ (Fin.succAbove_ne _ _)

lemma coordinateRatios_inclusion (m r : ℕ) (h : r ≤ m) (i : Fin (r+1))
    (p : Space r) (hp : p ∈ (coordinateChart i).source) :
    coordinateRatios (includedIndex m r h i) (inclusion m r h p) =
      coordinateInclusionLinear m r h i (coordinateRatios i p) := by
  conv_lhs => rw [← coordinateInverse_ratios i p hp]
  exact coordinateRatios_inclusion_inverse m r h i _

lemma inclusion_mem_coordinateChart (m r : ℕ) (h : r ≤ m) (i : Fin (r+1))
    (p : Space r) (hp : p ∈ (coordinateChart i).source) :
    inclusion m r h p ∈ (coordinateChart (includedIndex m r h i)).source := by
  rw [← coordinateInverse_ratios i p hp]
  change mk (inclusionVector m r h (coordinateRepresentative i (coordinateRatios i p))) _ ∉
    coordinateHyperplane m (includedIndex m r h i)
  rw [coordinateHyperplane_mk, inclusionVector_apply_index, coordinateRepresentative_same]
  exact one_ne_zero

/-- The real linear derivative in the ordered Re/Im charts. -/
def realCoordinateInclusionLinear (m r : ℕ) (h : r ≤ m) (i : Fin (r+1)) :
    (Fin (2*r) → ℝ) →L[ℝ] (Fin (2*m) → ℝ) :=
  (orderedComplexCoordinatesCLM m).toContinuousLinearMap.comp
    (((coordinateInclusionLinear m r h i).restrictScalars ℝ).toContinuousLinearMap.comp
      (orderedComplexCoordinatesCLM r).symm.toContinuousLinearMap)

lemma realCoordinateInclusionLinear_injective (m r : ℕ) (h : r ≤ m) (i : Fin (r+1)) :
    Function.Injective (realCoordinateInclusionLinear m r h i) :=
  (orderedComplexCoordinatesCLM m).injective.comp
    ((coordinateInclusionLinear_injective m r h i).comp (orderedComplexCoordinatesCLM r).symm.injective)

lemma chartDerivative_inclusion (m r : ℕ) (h : r ≤ m) (i : Fin (r+1))
    (p : Space r) (hp : p ∈ (realCoordinateChart i).source) :
    chartDerivative (realCoordinateChart i) (realCoordinateChart (includedIndex m r h i))
      (inclusion m r h) p = realCoordinateInclusionLinear m r h i := by
  apply SmoothManifolds.FiniteRegularity.coordinateDerivative_eq _ _ p hp
  refine ⟨realCoordinateInclusionLinear m r h i, (realCoordinateInclusionLinear m r h i).hasFDerivAt, ?_⟩
  filter_upwards [(realCoordinateChart i).open_source.mem_nhds hp] with q hq
  change orderedComplexCoordinatesCLM m
    (coordinateInclusionLinear m r h i ((orderedComplexCoordinatesCLM r).symm
      (orderedComplexCoordinatesCLM r (coordinateRatios i q)))) =
    orderedComplexCoordinatesCLM m (coordinateRatios (includedIndex m r h i) (inclusion m r h q))
  rw [ContinuousLinearEquiv.symm_apply_apply, coordinateRatios_inclusion m r h i q hq]

lemma inclusion_immersion (m r : ℕ) (h : r ≤ m) :
    IsImmersion (projectiveSmoothManifold r) (projectiveSmoothManifold m) (inclusion m r h) := by
  intro p
  obtain ⟨i,hp⟩ := coordinateCharts_cover p
  have hsm : ManifoldContDiff 1 (projectiveSmoothManifold r).smoothStructure.val
      (projectiveSmoothManifold m).smoothStructure.val (inclusion m r h) :=
    SmoothManifolds.manifoldContDiff_of_le _ _ _ _ _ (by simp) (inclusion_smooth m r h)
  apply ((SmoothManifolds.MapClasses.chart_invariants _ _ _ hsm p
    (realCoordinateChart i) (realCoordinateChart (includedIndex m r h i))
    (realCoordinateChart_mem_smoothStructure i)
    (realCoordinateChart_mem_smoothStructure (includedIndex m r h i)) hp
    (inclusion_mem_coordinateChart m r h i p hp)).2.1).mpr
  rw [chartDerivative_inclusion m r h i p hp]
  exact realCoordinateInclusionLinear_injective m r h i

lemma inclusion_smoothEmbedding (m r : ℕ) (h : r ≤ m) :
    IsSmoothEmbedding (projectiveSmoothManifold r) (projectiveSmoothManifold m) (inclusion m r h) :=
  ⟨inclusion_smooth m r h, (inclusion_embedding m r h).injective,
    inclusion_immersion m r h, (inclusion_embedding m r h).toHomeomorph,
    fun _ => rfl⟩

lemma inclusion_normal_exists (m r : ℕ) (h : r ≤ m) :
    Nonempty (SmoothManifolds.BundleOperationsData.NormalBundle
      (projectiveSmoothManifold r) (projectiveSmoothManifold m) (inclusion m r h)) :=
  SmoothManifolds.BundleOperations.exists_normal _ _ _ (inclusion_smoothEmbedding m r h)

end P202.ComplexProjective

namespace P202.ComplexProjective
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData

/-- Normalized tubular existence on each actual standard projective inclusion,
for any realization of its quotient normal bundle. -/
lemma inclusion_normalizedTubular_exists (m r : ℕ) (h : r ≤ m)
    (N : NormalBundle (projectiveSmoothManifold r) (projectiveSmoothManifold m) (inclusion m r h)) :
    ∃ K : TubularNeighborhood N, P202Specs.ThomClass.NormalCompatible N K :=
  P202.ThomClass.normalized_tubular_exists (inclusion_smoothEmbedding m r h) N

lemma inclusion_normalizedNormal_exists (m r : ℕ) (h : r ≤ m) :
    ∃ N : NormalBundle (projectiveSmoothManifold r) (projectiveSmoothManifold m) (inclusion m r h),
      ∃ K : TubularNeighborhood N, P202Specs.ThomClass.NormalCompatible N K := by
  obtain ⟨N⟩ := inclusion_normal_exists m r h
  exact ⟨N, inclusion_normalizedTubular_exists m r h N⟩

end P202.ComplexProjective
end

section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Set Topology
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.RelativeSingularChains

lemma positiveSimplexCoordinates_continuous (n : ℕ) :
    Continuous (positiveSimplexCoordinates n) := by
  apply continuous_pi
  intro j
  exact (Convexity.StdSimplex.continuous_weights_apply ℝ j.succ).sub
    (Convexity.StdSimplex.continuous_weights_apply ℝ 0)

lemma complexSimplexCoordinates_continuous (i : ℕ) :
    Continuous (complexSimplexCoordinates i) := by
  apply continuous_pi
  intro j
  exact (Complex.continuous_ofReal.comp ((continuous_apply _).comp
    (positiveSimplexCoordinates_continuous (2*i)))).add
    (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_apply _).comp (positiveSimplexCoordinates_continuous (2*i)))))

lemma complexSimplexCoordinates_zero_weights (i : ℕ)
    (x : P202.Cellular.StandardSimplex (2*i))
    (h : complexSimplexCoordinates i x = 0) :
    ∀ j, x.weights j = x.weights 0 := by
  intro j
  refine Fin.cases rfl (fun k => ?_) j
  have hk : k.val / 2 < i := by omega
  have he := congrArg Complex.re (congrFun h ⟨k.val / 2, hk⟩)
  have ho := congrArg Complex.im (congrFun h ⟨k.val / 2, hk⟩)
  simp [complexSimplexCoordinates, positiveSimplexCoordinates] at he ho
  by_cases hp : k.val % 2 = 0
  · have hj : (⟨2 * (k.val / 2) + 1, by omega⟩ : Fin (2*i+1)) = k.succ := by
      apply Fin.ext
      dsimp
      omega
    rw [hj] at he
    exact sub_eq_zero.mp he
  · have hj : (⟨2 * (k.val / 2) + 1 + 1, by omega⟩ : Fin (2*i+1)) = k.succ := by
      apply Fin.ext
      dsimp
      omega
    rw [hj] at ho
    exact sub_eq_zero.mp ho

lemma complexSimplexCoordinates_ne_zero_on_boundary (i : ℕ)
    (x : P202.Cellular.StandardSimplex (2*i))
    (hx : x ∈ (P202Specs.SpheresDisks.simplexPair (2*i)).subspace) :
    complexSimplexCoordinates i x ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ := hx
  have hall := complexSimplexCoordinates_zero_weights i x hz
  have hz0 : x.weights 0 = 0 := (hall j).symm.trans hj
  have hw : x.weights = 0 := by
    ext k
    exact (hall k).trans hz0
  have ht := x.total
  simp [hw] at ht

lemma positiveProjectiveSimplex_continuous (i : ℕ) :
    Continuous (positiveProjectiveSimplex i) :=
  (affineChart_continuous i i le_rfl).comp (complexSimplexCoordinates_continuous i)

lemma positiveProjectiveSimplex_ne_origin_on_boundary (i : ℕ)
    (x : P202.Cellular.StandardSimplex (2*i))
    (hx : x ∈ (P202Specs.SpheresDisks.simplexPair (2*i)).subspace) :
    positiveProjectiveSimplex i x ≠ projectiveOrigin i := by
  intro he
  exact complexSimplexCoordinates_ne_zero_on_boundary i x hx
    (affineChart_injective i i le_rfl he)

def positiveLocalSimplex (i : ℕ) : P202Specs.SpheresDisks.simplexPair (2*i) ⟶
    P202Specs.LocalOrientation.localPair (Space i) (projectiveOrigin i) where
  map := TopCat.ofHom ⟨positiveProjectiveSimplex i, positiveProjectiveSimplex_continuous i⟩
  mapsTo := fun x hx => positiveProjectiveSimplex_ne_origin_on_boundary i x hx

lemma positiveLocalSimplex_formula (i : ℕ)
    (x : P202.Cellular.StandardSimplex (2*i)) :
    (positiveLocalSimplex i).map x = positiveProjectiveSimplex i x := rfl

lemma complexNormalSlice_continuous (m : ℕ) : Continuous (complexNormalSlice m) := by
  change Continuous (quotientMap (m+1) ∘
    (fun w : ℂ => ⟨complexNormalVector m w, complexNormalVector_nonzero m w⟩))
  apply (quotientMap_continuous (m+1)).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  dsimp [complexNormalVector]
  split
  · exact continuous_const
  · split
    · exact continuous_id
    · exact continuous_const

lemma positiveNormalSimplex_continuous (m : ℕ) : Continuous (positiveNormalSimplex m) :=
  (complexNormalSlice_continuous m).comp
    ((continuous_apply 0).comp (complexSimplexCoordinates_continuous 1))

lemma complexNormalSlice_not_mem_hyperplane (m : ℕ) {w : ℂ} (hw : w ≠ 0) :
    complexNormalSlice m w ∉ Set.range (hyperplaneInclusion m) := by
  rw [show Set.range (hyperplaneInclusion m) = lowerSpace (m+1) (m+1) from
    inclusion_range (m+1) m (by omega)]
  intro h
  have hh := (lowerSpace_mk (complexNormalVector m w)
    (complexNormalVector_nonzero m w)).mp h ⟨m+1, by omega⟩ le_rfl
  exact hw (by simpa [complexNormalVector] using hh)

lemma positiveNormalSimplex_not_mem_hyperplane_on_boundary (m : ℕ)
    (x : P202.Cellular.StandardSimplex 2)
    (hx : x ∈ (P202Specs.SpheresDisks.simplexPair 2).subspace) :
    positiveNormalSimplex m x ∉ Set.range (hyperplaneInclusion m) := by
  apply complexNormalSlice_not_mem_hyperplane m
  intro hz
  apply complexSimplexCoordinates_ne_zero_on_boundary 1 x hx
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  simpa [hj] using hz

def positiveHyperplaneSlice (m : ℕ) : P202Specs.SpheresDisks.simplexPair 2 ⟶
    P202Specs.ThomClass.ambientPair (hyperplaneInclusion m) where
  map := TopCat.ofHom ⟨positiveNormalSimplex m, positiveNormalSimplex_continuous m⟩
  mapsTo := fun x hx => positiveNormalSimplex_not_mem_hyperplane_on_boundary m x hx

lemma positiveHyperplaneSlice_formula (m : ℕ) (x : P202.Cellular.StandardSimplex 2) :
    (positiveHyperplaneSlice m).map x = positiveNormalSimplex m x := rfl

lemma positiveSimplex_cycle (n : ℕ) :
    (ordinary ℤ ℤ (P202Specs.SpheresDisks.simplexPair n)).d (n : ℤ) ((n : ℤ)-1)
      (P202Specs.SpheresDisks.relativeAffineChain ℤ ℤ n 1) = 0 :=
  P202.SpheresDisks.relativeAffineChain_cycle ℤ ℤ n 1
end P202.ComplexProjectiveRing
end

section
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation

lemma positiveSimplexCoordinates_zero_weights (n : ℕ)
    (x : P202.Cellular.StandardSimplex n) (h : positiveSimplexCoordinates n x = 0) :
    ∀ j, x.weights j = x.weights 0 := by
  intro j
  refine Fin.cases rfl (fun k => ?_) j
  exact sub_eq_zero.mp (congrFun h k)

lemma positiveSimplexCoordinates_ne_zero_on_boundary (n : ℕ)
    (x : P202.Cellular.StandardSimplex n)
    (hx : x ∈ (P202Specs.SpheresDisks.simplexPair n).subspace) :
    positiveSimplexCoordinates n x ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ := hx
  have hall := positiveSimplexCoordinates_zero_weights n x hz
  have hz0 : x.weights 0 = 0 := (hall j).symm.trans hj
  have hw : x.weights = 0 := by
    ext k
    exact (hall k).trans hz0
  have ht := x.total
  simp [hw] at ht

def positiveRealLocalSimplex (n : ℕ) : P202Specs.SpheresDisks.simplexPair n ⟶
    localPair (Fin n → ℝ) 0 where
  map := TopCat.ofHom ⟨positiveSimplexCoordinates n, positiveSimplexCoordinates_continuous n⟩
  mapsTo := fun x hx => positiveSimplexCoordinates_ne_zero_on_boundary n x hx

def rawSimplexCoordinates (n : ℕ) (u : Fin n → ℝ) : Fin (n+1) → ℝ := Fin.cases 0 u

def simplexCoordinateMinimum (n : ℕ) (u : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (rawSimplexCoordinates n u)

lemma simplexCoordinateMinimum_le (n : ℕ) (u : Fin n → ℝ) (j : Fin (n+1)) :
    simplexCoordinateMinimum n u ≤ rawSimplexCoordinates n u j :=
  Finset.inf'_le _ (Finset.mem_univ j)

lemma simplexCoordinateMinimum_attained (n : ℕ) (u : Fin n → ℝ) :
    ∃ j, rawSimplexCoordinates n u j = simplexCoordinateMinimum n u := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (rawSimplexCoordinates n u)
  exact ⟨j, hj.symm⟩

lemma rawSimplexCoordinates_continuous (n : ℕ) (j : Fin (n+1)) :
    Continuous (fun u : Fin n → ℝ => rawSimplexCoordinates n u j) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · exact continuous_const
  · exact continuous_apply k

lemma simplexCoordinateMinimum_continuous (n : ℕ) : Continuous (simplexCoordinateMinimum n) :=
  Continuous.finset_inf'_apply _ (fun j _ => rawSimplexCoordinates_continuous n j)

def simplexCoordinateDenominator (n : ℕ) (u : Fin n → ℝ) : ℝ :=
  ∑ j, (rawSimplexCoordinates n u j - simplexCoordinateMinimum n u)

lemma simplexCoordinateDenominator_continuous (n : ℕ) :
    Continuous (simplexCoordinateDenominator n) := by
  exact continuous_finsetSum _ (fun j _ => (rawSimplexCoordinates_continuous n j).sub
    (simplexCoordinateMinimum_continuous n))

lemma simplexCoordinateDenominator_pos (n : ℕ) (u : Fin n → ℝ) (hu : u ≠ 0) :
    0 < simplexCoordinateDenominator n u := by
  have hnonneg (j : Fin (n+1)) :
      0 ≤ rawSimplexCoordinates n u j - simplexCoordinateMinimum n u :=
    sub_nonneg.mpr (simplexCoordinateMinimum_le n u j)
  have hn : 0 ≤ simplexCoordinateDenominator n u :=
    Finset.sum_nonneg (fun j _ => hnonneg j)
  refine lt_of_le_of_ne hn ?_
  intro he
  have hj (j : Fin (n+1)) : rawSimplexCoordinates n u j = simplexCoordinateMinimum n u :=
    sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp he.symm
      j (Finset.mem_univ j))
  apply hu
  ext k
  have h0 := hj 0
  have hk := hj k.succ
  simpa [rawSimplexCoordinates] using hk.trans h0.symm

def radialBoundarySimplex (n : ℕ) (u : Fin n → ℝ) (hu : u ≠ 0) :
    P202.Cellular.StandardSimplex n where
  weights := Finsupp.equivFunOnFinite.symm (fun j =>
    (rawSimplexCoordinates n u j - simplexCoordinateMinimum n u) /
      simplexCoordinateDenominator n u)
  nonneg j := by
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    exact div_nonneg (sub_nonneg.mpr (simplexCoordinateMinimum_le n u j))
      (simplexCoordinateDenominator_pos n u hu).le
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    rw [← Finset.sum_div]
    exact div_self (simplexCoordinateDenominator_pos n u hu).ne'

lemma radialBoundarySimplex_mem_boundary (n : ℕ) (u : Fin n → ℝ) (hu : u ≠ 0) :
    radialBoundarySimplex n u hu ∈ (P202Specs.SpheresDisks.simplexPair n).subspace := by
  obtain ⟨j, hj⟩ := simplexCoordinateMinimum_attained n u
  refine ⟨j, ?_⟩
  simp [radialBoundarySimplex, hj]

lemma radialBoundarySimplex_continuous (n : ℕ) :
    Continuous (fun u : {u : Fin n → ℝ // u ≠ 0} => radialBoundarySimplex n u.val u.property) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff]
  apply continuous_pi
  intro j
  change Continuous (fun u : {u : Fin n → ℝ // u ≠ 0} =>
    (rawSimplexCoordinates n u.val j - simplexCoordinateMinimum n u.val) /
      simplexCoordinateDenominator n u.val)
  exact (((rawSimplexCoordinates_continuous n j).sub
    (simplexCoordinateMinimum_continuous n)).comp continuous_subtype_val).div
    ((simplexCoordinateDenominator_continuous n).comp continuous_subtype_val)
    (fun u => (simplexCoordinateDenominator_pos n u.val u.property).ne')

def radialBoundaryRetraction (n : ℕ) :
    C({u : Fin n → ℝ // u ≠ 0}, (P202Specs.SpheresDisks.simplexPair n).sub) where
  toFun u := ⟨radialBoundarySimplex n u.val u.property,
    radialBoundarySimplex_mem_boundary n u.val u.property⟩
  continuous_toFun := (radialBoundarySimplex_continuous n).subtype_mk _

lemma rawSimplexCoordinates_positive (n : ℕ) (x : P202.Cellular.StandardSimplex n)
    (j : Fin (n+1)) :
    rawSimplexCoordinates n (positiveSimplexCoordinates n x) j = x.weights j - x.weights 0 := by
  refine Fin.cases ?_ (fun k => rfl) j
  simp [rawSimplexCoordinates]

lemma simplexCoordinateMinimum_positive_boundary (n : ℕ)
    (x : (P202Specs.SpheresDisks.simplexPair n).sub) :
    simplexCoordinateMinimum n (positiveSimplexCoordinates n x.val) = -x.val.weights 0 := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := x.property
    have h := simplexCoordinateMinimum_le n (positiveSimplexCoordinates n x.val) j
    rw [rawSimplexCoordinates_positive, hj] at h
    simpa using h
  · apply Finset.le_inf'
    intro j _
    rw [rawSimplexCoordinates_positive]
    have := x.val.weights_nonneg j
    linarith

lemma simplexCoordinateDenominator_positive_boundary (n : ℕ)
    (x : (P202Specs.SpheresDisks.simplexPair n).sub) :
    simplexCoordinateDenominator n (positiveSimplexCoordinates n x.val) = 1 := by
  dsimp [simplexCoordinateDenominator]
  simp_rw [simplexCoordinateMinimum_positive_boundary n x,
    rawSimplexCoordinates_positive, sub_neg_eq_add, sub_add_cancel]
  exact x.val.total_of_fintype

lemma radialBoundaryRetraction_left_inverse (n : ℕ)
    (x : (P202Specs.SpheresDisks.simplexPair n).sub) :
    radialBoundaryRetraction n ((positiveRealLocalSimplex n).restrict x) = x := by
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  ext j
  change (rawSimplexCoordinates n (positiveSimplexCoordinates n x.val) j -
    simplexCoordinateMinimum n (positiveSimplexCoordinates n x.val)) /
    simplexCoordinateDenominator n (positiveSimplexCoordinates n x.val) = x.val.weights j
  rw [rawSimplexCoordinates_positive, simplexCoordinateMinimum_positive_boundary,
    simplexCoordinateDenominator_positive_boundary]
  ring

lemma positiveSimplexCoordinates_radialBoundarySimplex (n : ℕ) (u : Fin n → ℝ) (hu : u ≠ 0) :
    positiveSimplexCoordinates n (radialBoundarySimplex n u hu) =
      (simplexCoordinateDenominator n u)⁻¹ • u := by
  ext j
  simp [positiveSimplexCoordinates, radialBoundarySimplex, rawSimplexCoordinates,
    div_eq_mul_inv]
  ring


def radialReturnFactor (n : ℕ) (t : unitInterval) (u : {u : Fin n → ℝ // u ≠ 0}) : ℝ :=
  (1-(t : ℝ)) * (simplexCoordinateDenominator n u.val)⁻¹ + t

lemma radialReturnFactor_pos (n : ℕ) (t : unitInterval)
    (u : {u : Fin n → ℝ // u ≠ 0}) : 0 < radialReturnFactor n t u := by
  have hD := inv_pos.mpr (simplexCoordinateDenominator_pos n u.val u.property)
  have ht0 := unitInterval.nonneg t
  have ht1 := unitInterval.le_one t
  by_cases ht : (t : ℝ) < 1
  · have hh := mul_pos (sub_pos.mpr ht) hD
    dsimp [radialReturnFactor]
    linarith
  · have ht' : (t : ℝ) = 1 := le_antisymm ht1 (le_of_not_gt ht)
    simp [radialReturnFactor, ht']

lemma radialReturnFactor_continuous (n : ℕ) : Continuous
    (fun p : unitInterval × {u : Fin n → ℝ // u ≠ 0} => radialReturnFactor n p.1 p.2) := by
  dsimp [radialReturnFactor]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (((simplexCoordinateDenominator_continuous n).comp
      (continuous_subtype_val.comp continuous_snd)).inv₀
        (fun p => (simplexCoordinateDenominator_pos n p.2.val p.2.property).ne'))).add
      (continuous_subtype_val.comp continuous_fst)

def radialBoundaryRightHomotopy (n : ℕ) :
    ContinuousMap.Homotopy (((positiveRealLocalSimplex n).restrict).hom.comp
      (radialBoundaryRetraction n))
      (ContinuousMap.id {u : Fin n → ℝ // u ≠ 0}) where
  toFun p := ⟨radialReturnFactor n p.1 p.2 • p.2.val,
    smul_ne_zero (radialReturnFactor_pos n p.1 p.2).ne' p.2.property⟩
  continuous_toFun := ((radialReturnFactor_continuous n).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  map_zero_left u := by
    apply Subtype.ext
    change radialReturnFactor n 0 u • u.val =
      positiveSimplexCoordinates n (radialBoundarySimplex n u.val u.property)
    rw [positiveSimplexCoordinates_radialBoundarySimplex]
    simp [radialReturnFactor]
  map_one_left u := by
    apply Subtype.ext
    change radialReturnFactor n 1 u • u.val = u.val
    simp [radialReturnFactor]

def radialBoundaryLeftHomotopy (n : ℕ) :
    ContinuousMap.Homotopy ((radialBoundaryRetraction n).comp
      (((positiveRealLocalSimplex n).restrict).hom))
      (ContinuousMap.id (P202Specs.SpheresDisks.simplexPair n).sub) where
  toFun p := p.2
  continuous_toFun := continuous_snd
  map_zero_left x := (radialBoundaryRetraction_left_inverse n x).symm
  map_one_left x := rfl

lemma positiveRealLocalSimplex_boundary_isIso (n : ℕ) (j : ℤ) :
    IsIso ((homologyFunctor ℤ ℤ j).map (positiveRealLocalSimplex n).restrict) := by
  exact (P202.PrismHomotopy.homologyIso ℤ ℤ
    (positiveRealLocalSimplex n).restrict (TopCat.ofHom (radialBoundaryRetraction n))
    (radialBoundaryLeftHomotopy n) (radialBoundaryRightHomotopy n) j).1

lemma homotopic_of_contractible_target {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [ContractibleSpace Y] (f g : C(X, Y)) : f.Homotopic g := by
  obtain ⟨y, hy⟩ := id_nullhomotopic Y
  have hf := hy.comp (ContinuousMap.Homotopic.refl f)
  have hg := hy.comp (ContinuousMap.Homotopic.refl g)
  apply hf.trans
  simpa using hg.symm

lemma positiveRealLocalSimplex_absolute_isIso (n : ℕ) (j : ℤ) :
    IsIso ((homologyFunctor ℤ ℤ j).map (positiveRealLocalSimplex n).map) := by
  haveI := P202.SpheresDisks.simplex_contractible n
  let f : P202Specs.SpheresDisks.simplex n ⟶ TopCat.of (Fin n → ℝ) :=
    (positiveRealLocalSimplex n).map
  let g : TopCat.of (Fin n → ℝ) ⟶ P202Specs.SpheresDisks.simplex n :=
    TopCat.ofHom (ContinuousMap.const _ (Convexity.StdSimplex.single 0))
  exact (P202.PrismHomotopy.homologyIso ℤ ℤ f g
    (Classical.choice (homotopic_of_contractible_target (g.hom.comp f.hom) (ContinuousMap.id _)))
    (Classical.choice (homotopic_of_contractible_target (f.hom.comp g.hom) (ContinuousMap.id _))) j).1

lemma positiveRealLocalSimplex_isIso (n : ℕ) (j : ℤ) :
    IsIso ((relativeHomologyFunctor ℤ ℤ j).map (positiveRealLocalSimplex n)) :=
  P202.LocalOrientation.relative_isIso_of_homology_isIso ℤ ℤ (positiveRealLocalSimplex n)
    (positiveRealLocalSimplex_boundary_isIso n) (positiveRealLocalSimplex_absolute_isIso n) j

end P202.ComplexProjectiveRing

namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation

def orderedRealComplexCoordinates (i : ℕ) (u : Fin (2*i) → ℝ) : Fin i → ℂ :=
  fun j => (u ⟨2*j.val, by omega⟩ : ℂ) + Complex.I * (u ⟨2*j.val+1, by omega⟩ : ℂ)

def orderedComplexRealCoordinates (i : ℕ) (z : Fin i → ℂ) : Fin (2*i) → ℝ :=
  fun j => if j.val % 2 = 0 then (z ⟨j.val/2, by omega⟩).re
    else (z ⟨j.val/2, by omega⟩).im

lemma orderedComplexRealCoordinates_left_inverse (i : ℕ) (u : Fin (2*i) → ℝ) :
    orderedComplexRealCoordinates i (orderedRealComplexCoordinates i u) = u := by
  ext j
  dsimp [orderedComplexRealCoordinates]
  by_cases he : j.val % 2 = 0
  · rw [if_pos he]
    have hj : (⟨2 * (j.val/2), by omega⟩ : Fin (2*i)) = j := by
      apply Fin.ext
      dsimp
      omega
    simp [orderedRealComplexCoordinates, hj]
  · rw [if_neg he]
    have hj : (⟨2 * (j.val/2) + 1, by omega⟩ : Fin (2*i)) = j := by
      apply Fin.ext
      dsimp
      omega
    simp [orderedRealComplexCoordinates, hj]

lemma orderedComplexRealCoordinates_right_inverse (i : ℕ) (z : Fin i → ℂ) :
    orderedRealComplexCoordinates i (orderedComplexRealCoordinates i z) = z := by
  ext j
  dsimp [orderedRealComplexCoordinates, orderedComplexRealCoordinates]
  have he : (2*j.val) % 2 = 0 := by omega
  have ho : (2*j.val+1) % 2 ≠ 0 := by omega
  rw [if_pos he, if_neg ho]
  have hje : (⟨(2*j.val)/2, by omega⟩ : Fin i) = j := by
    apply Fin.ext
    dsimp
    omega
  have hjo : (⟨(2*j.val+1)/2, by omega⟩ : Fin i) = j := by
    apply Fin.ext
    dsimp
    omega
  rw [hje, hjo]
  simpa only [mul_comm] using Complex.re_add_im (z j)

lemma orderedRealComplexCoordinates_continuous (i : ℕ) :
    Continuous (orderedRealComplexCoordinates i) := by
  apply continuous_pi
  intro j
  exact (Complex.continuous_ofReal.comp (continuous_apply _)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply _)))

lemma orderedComplexRealCoordinates_continuous (i : ℕ) :
    Continuous (orderedComplexRealCoordinates i) := by
  apply continuous_pi
  intro j
  dsimp [orderedComplexRealCoordinates]
  split
  · exact Complex.continuous_re.comp (continuous_apply _)
  · exact Complex.continuous_im.comp (continuous_apply _)

def orderedRealComplexHomeomorph (i : ℕ) : (Fin (2*i) → ℝ) ≃ₜ (Fin i → ℂ) where
  toFun := orderedRealComplexCoordinates i
  invFun := orderedComplexRealCoordinates i
  left_inv := orderedComplexRealCoordinates_left_inverse i
  right_inv := orderedComplexRealCoordinates_right_inverse i
  continuous_toFun := orderedRealComplexCoordinates_continuous i
  continuous_invFun := orderedComplexRealCoordinates_continuous i

@[simp] lemma orderedRealComplexCoordinates_zero (i : ℕ) :
    orderedRealComplexCoordinates i 0 = 0 := by
  ext j
  simp [orderedRealComplexCoordinates]

@[simp] lemma orderedComplexRealCoordinates_zero (i : ℕ) :
    orderedComplexRealCoordinates i 0 = 0 := by
  ext j
  simp [orderedComplexRealCoordinates]

def orderedRealComplexLocalPairIso (i : ℕ) :
    localPair (Fin (2*i) → ℝ) 0 ≅ localPair (Fin i → ℂ) 0 where
  hom := {
    map := TopCat.ofHom ⟨orderedRealComplexHomeomorph i, (orderedRealComplexHomeomorph i).continuous⟩
    mapsTo := fun u hu he => hu ((orderedRealComplexHomeomorph i).injective
      (he.trans (orderedRealComplexCoordinates_zero i).symm)) }
  inv := {
    map := TopCat.ofHom ⟨(orderedRealComplexHomeomorph i).symm, (orderedRealComplexHomeomorph i).symm.continuous⟩
    mapsTo := fun z hz he => hz ((orderedRealComplexHomeomorph i).symm.injective
      (he.trans (orderedComplexRealCoordinates_zero i).symm)) }
  hom_inv_id := PairMap.ext _ _ (by
    ext u
    exact orderedComplexRealCoordinates_left_inverse i u)
  inv_hom_id := PairMap.ext _ _ (by
    ext z
    exact orderedComplexRealCoordinates_right_inverse i z)

end P202.ComplexProjectiveRing

namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation

universe uPositive

def openEmbeddingLocalMap {X Y : Type uPositive} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsOpenEmbedding f) (x : X) : localPair X x ⟶ localPair Y (f x) where
  map := TopCat.ofHom ⟨f, hf.continuous⟩
  mapsTo := fun y hy he => hy (hf.injective he)

lemma openEmbeddingLocalMap_isIso {X Y : Type uPositive} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (f : X → Y) (hf : IsOpenEmbedding f) (x : X) (j : ℕ) :
    IsIso ((relativeHomologyFunctor ℤ ℤ (j : ℤ)).map (openEmbeddingLocalMap f hf x)) := by
  let e := hf.isEmbedding.toHomeomorph
  have hh : openEmbeddingLocalMap f hf x =
      (P202.LocalOrientation.localPairIsoOfHomeomorph e x).hom ≫
        P202Specs.LocalOrientation.openLocalInclusion (Set.range f) (e x) :=
    PairMap.ext _ _ rfl
  haveI := P202.LocalOrientation.openLocalInclusion_isIso ℤ (Set.range f) hf.isOpen_range (e x) j
  rw [hh, Functor.map_comp]
  infer_instance

lemma positiveLocalSimplex_factor (i : ℕ) :
    positiveLocalSimplex i = positiveRealLocalSimplex (2*i) ≫
      (orderedRealComplexLocalPairIso i).hom ≫
      openEmbeddingLocalMap (affineChart i i le_rfl) (affineChart_top_openEmbedding i) 0 := by
  apply PairMap.ext
  ext x
  rfl

lemma positiveLocalSimplex_isIso (i j : ℕ) :
    IsIso ((relativeHomologyFunctor ℤ ℤ (j : ℤ)).map (positiveLocalSimplex i)) := by
  haveI := positiveRealLocalSimplex_isIso (2*i) (j : ℤ)
  haveI := openEmbeddingLocalMap_isIso (affineChart i i le_rfl)
    (affineChart_top_openEmbedding i) 0 j
  rw [positiveLocalSimplex_factor, Functor.map_comp, Functor.map_comp]
  infer_instance

end P202.ComplexProjectiveRing
end

section
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation

def positiveLocalClass (i : ℕ) : LocalGroup ℤ (Space i) (projectiveOrigin i) (2*i) :=
  ((relativeHomologyFunctor ℤ ℤ ((2*i : ℕ) : ℤ)).map (positiveLocalSimplex i))
    (P202.SpheresDisks.affineClassLinear ℤ ℤ (2*i) 1)

lemma positiveLocalClass_formula (i : ℕ) : positiveLocalClass i =
    ((relativeHomologyFunctor ℤ ℤ ((2*i : ℕ) : ℤ)).map (positiveLocalSimplex i))
      (P202Specs.SpheresDisks.classOf ℤ _ ((2*i : ℕ) : ℤ)
        (P202Specs.SpheresDisks.relativeAffineChain ℤ ℤ (2*i) 1) (positiveSimplex_cycle (2*i))) := by
  exact congrArg
    ((relativeHomologyFunctor ℤ ℤ ((2*i : ℕ) : ℤ)).map (positiveLocalSimplex i))
    (P202.SpheresDisks.affineClassLinear_apply ℤ ℤ (2*i) 1)

lemma positiveLocalClass_isGenerator (i : ℕ) : IsGenerator ℤ (positiveLocalClass i) := by
  haveI := positiveLocalSimplex_isIso i (2*i)
  let e := asIso ((relativeHomologyFunctor ℤ ℤ ((2*i : ℕ) : ℤ)).map (positiveLocalSimplex i))
  let s := LinearEquiv.ofBijective (P202.SpheresDisks.affineClassLinear ℤ ℤ (2*i))
    (P202.SpheresDisks.SimplexOrientation.affineClassLinear_ring_bijective ℤ (2*i))
  have hs : IsGenerator ℤ (s 1) :=
    (P202.LocalOrientation.generator_map_iff ℤ s (1 : ℤ)).mpr
      (P202.LocalOrientation.generator_one ℤ)
  exact (P202.LocalOrientation.generator_map_iff ℤ e.toLinearEquiv (s 1)).mpr hs

end P202.ComplexProjectiveRing
end

section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.LocalOrientation P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.SpheresDisks
namespace P202.ComplexProjectiveRing

def pointCoordinateHomeomorph : Space 0 ≃ₜ Coordinate 0 where
  toFun _ := coordinateOrigin 0
  invFun _ := projectiveOrigin 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

def pointManifold : Manifold 0 (Space 0) where
  hausdorff := inferInstance
  secondCountable := inferInstance
  atlas := {pointCoordinateHomeomorph.toOpenPartialHomeomorph}
  covers _ := ⟨_, Set.mem_singleton _, Set.mem_univ _⟩

def pointSimplexHomeomorph : P202.Cellular.StandardSimplex 0 ≃ₜ Space 0 where
  toFun _ := projectiveOrigin 0
  invFun _ := Convexity.StdSimplex.barycenter
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

def pointSimplexLocalIso (x : Space 0) : simplexPair 0 ≅ localPair (Space 0) x where
  hom := ⟨(TopCat.isoOfHomeo (X := simplex 0) (Y := projectiveSpace 0) pointSimplexHomeomorph).hom, fun y hy =>
    (by have := P202.SpheresDisks.simplex_zero_boundary_empty; exact isEmptyElim (⟨y,hy⟩ : (simplexPair 0).sub))⟩
  inv := ⟨(TopCat.isoOfHomeo (X := simplex 0) (Y := projectiveSpace 0) pointSimplexHomeomorph).inv, fun y hy =>
    (hy (Subsingleton.elim _ _)).elim⟩
  hom_inv_id := by apply PairMap.ext; exact (TopCat.isoOfHomeo (X := simplex 0) (Y := projectiveSpace 0) pointSimplexHomeomorph).hom_inv_id
  inv_hom_id := by apply PairMap.ext; exact (TopCat.isoOfHomeo (X := simplex 0) (Y := projectiveSpace 0) pointSimplexHomeomorph).inv_hom_id

def pointPositiveLocalClass (x : Space 0) : LocalGroup ℤ (Space 0) x 0 :=
  ((relativeHomologyFunctor ℤ ℤ 0).map (pointSimplexLocalIso x).hom)
    (classOf ℤ _ 0 (relativeAffineChain ℤ ℤ 0 1)
      (P202.SpheresDisks.relativeAffineChain_cycle ℤ ℤ 0 1))

lemma pointPositiveLocalClass_generator (x : Space 0) :
    P202Specs.LocalOrientation.IsGenerator ℤ (pointPositiveLocalClass x) := by
  obtain ⟨hz,e,he⟩ := P202.SpheresDisks.simplexGenerator ℤ ℤ 0
  let e' := ((relativeHomologyFunctor ℤ ℤ 0).mapIso (pointSimplexLocalIso x)).toLinearEquiv
  let q := e'.symm.trans e
  have hq : q (pointPositiveLocalClass x) = 1 := by
    change e (e'.symm (e' _)) = 1
    rw [e'.symm_apply_apply]
    exact he 1
  apply (P202.LocalOrientation.generator_map_iff ℤ q (pointPositiveLocalClass x)).mp
  rw [hq]
  exact P202.LocalOrientation.generator_one ℤ

lemma pointPositiveLocalClass_orientation :
    IsOrientation ℤ pointManifold pointPositiveLocalClass := by
  refine ⟨pointPositiveLocalClass_generator, ?_⟩
  intro x
  obtain ⟨B,hx,_⟩ := P202.LocalOrientation.coordinateBall_basis pointManifold x
    isOpen_univ (Set.mem_univ x)
  let e := LinearEquiv.ofBijective (restrictPoint ℤ (B.interior_subset_closed hx) 0)
    ((P202.LocalOrientation.zeroBallRestriction ℤ (Space 0) pointManifold B).2 x hx)
  let g := e.symm (pointPositiveLocalClass x)
  refine ⟨B,hx,g,?_,?_⟩
  · apply (P202.LocalOrientation.generator_map_iff ℤ e g).mp
    rw [show e g = pointPositiveLocalClass x from e.apply_symm_apply _]
    exact pointPositiveLocalClass_generator x
  · intro y hy
    have heq : y = x := Subsingleton.elim _ _
    subst y
    exact e.apply_symm_apply _

def pointOrientation : Orientation ℤ pointManifold :=
  ⟨pointPositiveLocalClass, pointPositiveLocalClass_orientation⟩

instance pointLocalPair_empty (x : Space 0) : IsEmpty (localPair (Space 0) x).sub :=
  ⟨fun y => y.property (Subsingleton.elim _ _)⟩

def pointAbsoluteLocalEquiv (x : Space 0) :
    homology ℤ ℤ (projectiveSpace 0) 0 ≃ₗ[ℤ] LocalGroup ℤ (Space 0) x 0 :=
  (P202.LocalOrientation.emptySubspaceHomologyIso ℤ (localPair (Space 0) x) 0).toLinearEquiv

def pointFundamental : homology ℤ ℤ (projectiveSpace 0) 0 :=
  (pointAbsoluteLocalEquiv (projectiveOrigin 0)).symm
    (pointPositiveLocalClass (projectiveOrigin 0))

lemma pointFundamental_values :
    P202Specs.CompactOrientation.HasLocalValues ℤ pointOrientation.val Set.univ
      (P202Specs.CompactOrientation.absoluteToSupported ℤ (Space 0) 0 pointFundamental) := by
  intro x hx
  have heq : x = projectiveOrigin 0 := Subsingleton.elim _ _
  subst x
  have hcomp := projection_map (ordinaryFunctor ℤ ℤ) (pointMap hx)
  have hp : (ordinaryFunctor ℤ ℤ).map (pointMap hx).map = 𝟙 _ := by
    change (ordinaryFunctor ℤ ℤ).map (𝟙 _) = _
    exact (ordinaryFunctor ℤ ℤ).map_id _
  rw [hp, Category.id_comp] at hcomp
  have hhom := congrArg (fun f => HomologicalComplex.homologyMap f 0) hcomp
  rw [HomologicalComplex.homologyMap_comp] at hhom
  have hv := congrArg (fun f => f pointFundamental) hhom
  change _ = pointPositiveLocalClass (projectiveOrigin 0)
  calc
    _ = pointAbsoluteLocalEquiv (projectiveOrigin 0) pointFundamental := hv
    _ = _ := (pointAbsoluteLocalEquiv (projectiveOrigin 0)).apply_symm_apply _

def pointComplexFundamentalData : ComplexFundamentalData 0 where
  manifold := pointManifold
  orientation := pointOrientation
  localSimplex := (pointSimplexLocalIso (projectiveOrigin 0)).hom
  localSimplex_formula _ := (show ∀ x y : Space 0, x = y from Subsingleton.elim) _ _
  simplex_cycle := P202.SpheresDisks.relativeAffineChain_cycle ℤ ℤ 0 1
  orientation_positive := rfl
  fundamental := pointFundamental
  fundamental_values := pointFundamental_values

lemma evaluation_homologyπ (K : ChainComplex (ModuleCat ℤ) ℤ) (n : ℤ)
    (a : (P202Specs.UniversalCoefficientsCohomology.dualChain ℤ ℤ K).cycles n)
    (z : K.cycles n) :
    P202Specs.UniversalCoefficientsCohomology.evaluation ℤ ℤ K n
      ((P202Specs.UniversalCoefficientsCohomology.dualChain ℤ ℤ K).homologyπ n a)
      (K.homologyπ n z) =
      (show K.X n →ₗ[ℤ] ℤ from
        (P202Specs.UniversalCoefficientsCohomology.dualChain ℤ ℤ K).iCycles n a)
        (K.iCycles n z) := by
  let D := P202Specs.UniversalCoefficientsCohomology.dualChain ℤ ℤ K
  let a' := (D.sc n).moduleCatCyclesIso.hom a
  let z' := (K.sc n).moduleCatCyclesIso.hom z
  have ha := P202.UniversalCoefficientsCohomology.cycleClass_eq ℤ D n a'
  have hz := P202.UniversalCoefficientsCohomology.cycleClass_eq ℤ K n z'
  simp only [a', z', Iso.hom_inv_id_apply] at ha hz
  rw [← ha, ← hz, P202.UniversalCoefficientsCohomology.evaluation_formula]
  have hvalA : a'.val = D.iCycles n a := by
    exact congrArg (fun f => f a) (D.sc n).moduleCatCyclesIso_hom_i
  have hvalZ : z'.val = K.iCycles n z := by
    exact congrArg (fun f => f z) (K.sc n).moduleCatCyclesIso_hom_i
  rw [hvalA,hvalZ]

lemma evaluation_classOf (K : ChainComplex (ModuleCat ℤ) ℤ) (n : ℤ)
    (a : (P202Specs.UniversalCoefficientsCohomology.dualChain ℤ ℤ K).cycles n)
    (z : K.X n) (hz : K.d n (n-1) z = 0) :
    P202Specs.UniversalCoefficientsCohomology.evaluation ℤ ℤ K n
      ((P202Specs.UniversalCoefficientsCohomology.dualChain ℤ ℤ K).homologyπ n a)
      (classOf ℤ K n z hz) =
      (show K.X n →ₗ[ℤ] ℤ from
        (P202Specs.UniversalCoefficientsCohomology.dualChain ℤ ℤ K).iCycles n a) z := by
  change P202Specs.UniversalCoefficientsCohomology.evaluation ℤ ℤ K n
    ((P202Specs.UniversalCoefficientsCohomology.dualChain ℤ ℤ K).homologyπ n a)
    (K.homologyπ n (K.cyclesMk z (n-1) _ hz)) = _
  rw [evaluation_homologyπ]
  congr 1
  exact K.i_cyclesMk _ _ _ _

def pointSimplexAbsoluteClass : homology ℤ ℤ (simplex 0) 0 :=
  classOf ℤ _ 0 (affineChainZ ℤ ℤ 0 1) (by
    change (ordinaryComplex ℤ ℤ (simplex 0)).d 0 (-1) _ = 0
    rw [P202.SingularChains.ordinary_boundary_zero ℤ ℤ (simplex 0) (-1)]
    rfl)

lemma pointFundamental_eq_simplex :
    pointFundamental = (homologyFunctor ℤ ℤ 0).map
      (TopCat.isoOfHomeo (X := simplex 0) (Y := projectiveSpace 0) pointSimplexHomeomorph).hom
      pointSimplexAbsoluteClass := by
  let f := (pointSimplexLocalIso (projectiveOrigin 0)).hom
  have hp := projection_map (ordinaryFunctor ℤ ℤ) f
  have hhom := congrArg (fun f => HomologicalComplex.homologyMap f 0) hp
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  have hsource : HomologicalComplex.homologyMap
      (projection (ordinaryFunctor ℤ ℤ) (simplexPair 0)) 0 pointSimplexAbsoluteClass =
      classOf ℤ _ 0 (relativeAffineChain ℤ ℤ 0 1)
        (P202.SpheresDisks.relativeAffineChain_cycle ℤ ℤ 0 1) := by
    exact P202.MayerVietoris.classOf_map _ _ _ _ _
  apply (pointAbsoluteLocalEquiv (projectiveOrigin 0)).injective
  rw [pointFundamental, LinearEquiv.apply_symm_apply]
  have hh := congrArg (fun f => f pointSimplexAbsoluteClass) hhom
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hsource] at hh
  exact hh

lemma pointUnit_evaluation (C : P202Specs.CupProduct.CohomologyRing ℤ (projectiveSpace 0)) :
    letI := C.gradedRing
    P202Specs.ComplexProjectiveRing.evaluation 0 0 (1 : cohomology 0 0) pointFundamental = 1 := by
  letI := C.gradedRing
  obtain ⟨a,ha,hu⟩ := C.unit_represents
  change P202Specs.ComplexProjectiveRing.evaluation 0 0
    (GradedMonoid.GOne.one : cohomology 0 0) pointFundamental = 1
  rw [hu, pointFundamental_eq_simplex]
  let f := (TopCat.isoOfHomeo (X := simplex 0) (Y := projectiveSpace 0) pointSimplexHomeomorph).hom
  have hmap : (homologyFunctor ℤ ℤ 0).map f pointSimplexAbsoluteClass =
      classOf ℤ _ 0
        (((ordinaryFunctor ℤ ℤ).map f).f 0 (affineChainZ ℤ ℤ 0 1))
        (by change (ordinaryComplex ℤ ℤ (projectiveSpace 0)).d 0 (-1) _ = 0; rw [P202.SingularChains.ordinary_boundary_zero ℤ ℤ (projectiveSpace 0) (-1)]; rfl) := by
    exact P202.MayerVietoris.classOf_map _ _ _ _ _
  change P202Specs.ComplexProjectiveRing.evaluation 0 0 ((P202Specs.CohomologyPairs.ordinaryCochains ℤ ℤ
    (projectiveSpace 0)).homologyπ 0 a) ((homologyFunctor ℤ ℤ 0).map f pointSimplexAbsoluteClass) = 1
  rw [hmap]
  change P202Specs.UniversalCoefficientsCohomology.evaluation ℤ ℤ
    (ordinaryComplex ℤ ℤ (projectiveSpace 0)) 0
    ((P202Specs.UniversalCoefficientsCohomology.dualChain ℤ ℤ
      (ordinaryComplex ℤ ℤ (projectiveSpace 0))).homologyπ 0 a) _ = 1
  erw [evaluation_classOf]
  let c := ((ordinaryFunctor ℤ ℤ).map f).f 0 (affineChainZ ℤ ℤ 0 1)
  have ha' : P202Specs.CohomologyPairs.ordinaryCochainsEquiv ℤ ℤ (projectiveSpace 0) 0
      ((P202Specs.CohomologyPairs.ordinaryCochains ℤ ℤ (projectiveSpace 0)).iCycles 0 a) =
      P202Specs.CupProduct.oneCochain ℤ (projectiveSpace 0) := ha
  have hc : c = (ordinaryNonnegativeIso ℤ ℤ (projectiveSpace 0) 0).inv
      (((chainMap ℤ ℤ f).f 0) (affineChain ℤ 0 1)) := by
    unfold c affineChainZ
    change (_ ≫ ((ordinaryFunctor ℤ ℤ).map f).f 0) _ =
      ((chainMap ℤ ℤ f).f 0 ≫ _) _
    congr 2
    change (ordinaryNonnegativeIso ℤ ℤ (simplex 0) 0).inv ≫
      (HomologicalComplex.extendMap (chainMap ℤ ℤ f) (degreeEmbedding 0)).f (0 : ℤ) = _
    rw [HomologicalComplex.extendMap_f _ _ (show (degreeEmbedding 0).f 0 = (0 : ℤ) by rfl)]
    simp [ordinaryNonnegativeIso]
  change (show _ →ₗ[ℤ] ℤ from
    (P202Specs.CohomologyPairs.ordinaryCochains ℤ ℤ (projectiveSpace 0)).iCycles 0 a) c = 1
  rw [hc]
  change (P202Specs.CohomologyPairs.ordinaryCochainsEquiv ℤ ℤ (projectiveSpace 0) 0
    ((P202Specs.CohomologyPairs.ordinaryCochains ℤ ℤ (projectiveSpace 0)).iCycles 0 a))
      (((chainMap ℤ ℤ f).f 0) (affineChain ℤ 0 1)) = 1
  rw [ha']
  unfold P202Specs.CupProduct.oneCochain affineChain
  rw [P202.SingularChains.chainMap_single, P202.SingularChains.augmentationLinear_single]

def pointOrdinaryImageEquiv :
    P202Specs.CohomologyPairs.relativeCohomology ℤ ℤ
      (localPair (Space 0) (projectiveOrigin 0)) 0 ≃ₗ[ℤ] cohomology 0 0 := by
  let P := localPair (Space 0) (projectiveOrigin 0)
  have hi : inclusion (ordinaryFunctor ℤ ℤ) P = 0 := by
    apply HomologicalComplex.Hom.ext
    funext k
    exact (P202.SingularDegreeZero.emptyOrdinaryX ℤ ℤ P.sub k).eq_of_src _ _
  haveI : IsIso (projection (ordinaryFunctor ℤ ℤ) P) := by
    change IsIso (cokernel.π (inclusion (ordinaryFunctor ℤ ℤ) P))
    rw [hi]
    infer_instance
  haveI : IsIso (P202Specs.CohomologyPairs.relativeToAbsolute ℤ ℤ P) := by
    infer_instance
  exact (asIso (HomologicalComplex.homologyMap
    (P202Specs.CohomologyPairs.relativeToAbsolute ℤ ℤ P) 0)).toLinearEquiv

lemma pointGeometricGenerator (C : P202Specs.CupProduct.CohomologyRing ℤ (projectiveSpace 0)) :
    GeometricGenerator 0 C (0 : cohomology 0 2) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro k hk
    omega
  · letI := C.gradedRing
    intro i hi
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    subst i
    let a := pointOrdinaryImageEquiv.symm (1 : cohomology 0 0)
    have ha : ordinaryImage (localPair (Space 0) (projectiveOrigin 0)) 0 a =
        (1 : cohomology 0 0) := pointOrdinaryImageEquiv.apply_symm_apply _
    have hb : Function.Bijective (fun z : ℤ => z • (1 : cohomology 0 0)) := by
      simpa only [homogeneousPower_zero] using homogeneousPower_zero_primitive 0 C 0
    have haB : Function.Bijective (fun z : ℤ => z • a) := by
      have hfun : (fun z : ℤ => z • a) =
          pointOrdinaryImageEquiv.symm ∘ (fun z : ℤ => z • (1 : cohomology 0 0)) := by
        funext z
        exact (map_zsmul _ _ _).symm
      rw [hfun]
      exact pointOrdinaryImageEquiv.symm.bijective.comp hb
    have he : relativeEvaluation _ 0 a (pointOrientation.val (projectiveOrigin 0)) = 1 := by
      have h := evaluation_ordinaryImage (localPair (Space 0) (projectiveOrigin 0)) 0
        a pointFundamental
      rw [ha] at h
      have hf : absoluteToRelative (localPair (Space 0) (projectiveOrigin 0)) 0
          pointFundamental = pointOrientation.val (projectiveOrigin 0) :=
        (pointAbsoluteLocalEquiv (projectiveOrigin 0)).apply_symm_apply _
      rw [hf] at h
      exact h.symm.trans (pointUnit_evaluation C)
    refine ⟨𝟙 _,pointComplexFundamentalData,a,(1 : cohomology 0 0),?_,haB,he,?_,?_,?_⟩
    · intro x
      exact Subsingleton.elim _ _
    · simp only [pow_zero, Nat.mul_zero, DirectSum.of_zero_one]
    · change P202Specs.CupProduct.hPullback ℤ (𝟙 (projectiveSpace 0)) 0 (1 : cohomology 0 0) = _
      have hid : P202Specs.CupProduct.hPullback ℤ (𝟙 (projectiveSpace 0)) 0 (1 : cohomology 0 0) =
          (1 : cohomology 0 0) := by
        change ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℤ ℤ 0).map
          (𝟙 (Opposite.op (projectiveSpace 0)))) _ = _
        exact congrArg (fun f => f (1 : cohomology 0 0))
          ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℤ ℤ 0).map_id _)
      exact hid.trans ha.symm
    · have hid : P202Specs.CupProduct.hPullback ℤ (𝟙 (projectiveSpace 0)) 0 (1 : cohomology 0 0) =
          (1 : cohomology 0 0) := by
        change ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℤ ℤ 0).map
          (𝟙 (Opposite.op (projectiveSpace 0)))) _ = _
        exact congrArg (fun f => f (1 : cohomology 0 0))
          ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℤ ℤ 0).map_id _)
      change P202Specs.ComplexProjectiveRing.evaluation 0 0
        (P202Specs.CupProduct.hPullback ℤ (𝟙 (projectiveSpace 0)) 0
          (1 : cohomology 0 0)) pointFundamental = 1
      rw [hid]
      exact pointUnit_evaluation C

end P202.ComplexProjectiveRing
end

section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open P202Specs.ComplexProjectiveRing P202Specs.LocalOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains
namespace P202.ComplexProjectiveRing

lemma absoluteToRelative_restrictPoint {M : Type*} [TopologicalSpace M]
    {K : Set M} {x : M} (hx : x ∈ K) (n : ℕ)
    (c : homology ℤ ℤ (TopCat.of M) (n : ℤ)) :
    restrictPoint ℤ hx n (absoluteToRelative (supportedPair M K) n c) =
      absoluteToRelative (localPair M x) n c := by
  have hcomp := projection_map (ordinaryFunctor ℤ ℤ) (pointMap hx)
  have hp : (ordinaryFunctor ℤ ℤ).map (pointMap hx).map = 𝟙 _ := by
    exact (ordinaryFunctor ℤ ℤ).map_id _
  rw [hp, Category.id_comp] at hcomp
  have hhom := congrArg (fun f => HomologicalComplex.homologyMap f (n : ℤ)) hcomp
  rw [HomologicalComplex.homologyMap_comp] at hhom
  exact congrArg (fun f => f c) hhom

lemma orientation_of_absoluteLocalGenerators {n : ℕ} {M : Type*} [TopologicalSpace M]
    (A : Manifold n M) (c : homology ℤ ℤ (TopCat.of M) (n : ℤ))
    (hg : ∀ x : M, P202Specs.LocalOrientation.IsGenerator ℤ
      (absoluteToRelative (localPair M x) n c)) :
    IsOrientation ℤ A (fun x => absoluteToRelative (localPair M x) n c) := by
  refine ⟨hg, ?_⟩
  intro x
  obtain ⟨B,hx,_⟩ := P202.LocalOrientation.coordinateBall_basis A x isOpen_univ (Set.mem_univ x)
  let g := absoluteToRelative (supportedPair M B.closed) n c
  let e := P202.LocalOrientation.ballPointEquiv P202.LocalOrientation.ballRestriction ℤ B hx
  have he : e g = absoluteToRelative (localPair M x) n c :=
    absoluteToRelative_restrictPoint (B.interior_subset_closed hx) n c
  refine ⟨B,hx,g,?_,?_⟩
  · apply (P202.LocalOrientation.generator_map_iff ℤ e g).mp
    rw [he]
    exact hg x
  · intro y hy
    exact absoluteToRelative_restrictPoint (B.interior_subset_closed hy) n c

lemma absoluteLocalOrientation_fundamental_values {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : homology ℤ ℤ (TopCat.of M) (n : ℤ)) :
    P202Specs.CompactOrientation.HasLocalValues ℤ
      (fun x => absoluteToRelative (localPair M x) n c) Set.univ
      (P202Specs.CompactOrientation.absoluteToSupported ℤ M n c) := by
  intro x hx
  exact absoluteToRelative_restrictPoint hx n c
end P202.ComplexProjectiveRing
end

section
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation

universe uLocal

lemma absoluteToLocal_isIso_of_homeomorph {X Y : Type uLocal}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) (j : ℤ)
    (hx : IsIso (HomologicalComplex.homologyMap
      (projection (ordinaryFunctor ℤ ℤ) (localPair X x)) j)) :
    IsIso (HomologicalComplex.homologyMap
      (projection (ordinaryFunctor ℤ ℤ) (localPair Y (e x))) j) := by
  let f := (P202.LocalOrientation.localPairIsoOfHomeomorph e x).hom
  haveI := hx
  haveI : IsIso f.map := by
    change IsIso ((TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e).hom)
    infer_instance
  have hs := congrArg (fun k => HomologicalComplex.homologyMap k j)
    (projection_map (ordinaryFunctor ℤ ℤ) f)
  simp only [HomologicalComplex.homologyMap_comp] at hs
  haveI : IsIso (HomologicalComplex.homologyMap ((ordinaryFunctor ℤ ℤ).map f.map) j) := by
    change IsIso ((homologyFunctor ℤ ℤ j).map f.map)
    infer_instance
  haveI : IsIso (HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor ℤ ℤ) f) j) := by
    change IsIso ((relativeHomologyFunctor ℤ ℤ j).map f)
    infer_instance
  haveI : IsIso (HomologicalComplex.homologyMap ((ordinaryFunctor ℤ ℤ).map f.map) j ≫
      HomologicalComplex.homologyMap
        (projection (ordinaryFunctor ℤ ℤ) (localPair Y (e x))) j) := by
    rw [← hs]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap ((ordinaryFunctor ℤ ℤ).map f.map) j) _

lemma exists_projectiveLinearHomeomorph (m : ℕ) (x y : Space m) :
    ∃ e : (Fin (m+1) → ℂ) ≃ₗ[ℂ] (Fin (m+1) → ℂ),
      projectiveLinearHomeomorph m e x = y := by
  letI : MulAction.IsPretransitive ((Fin (m+1) → ℂ) ≃ₗ[ℂ] (Fin (m+1) → ℂ))
      (Projectivization ℂ (Fin (m+1) → ℂ)) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq
    (α := Projectivization ℂ (Fin (m+1) → ℂ))
    ((Fin (m+1) → ℂ) ≃ₗ[ℂ] (Fin (m+1) → ℂ)) x y
  exact ⟨e, he⟩

lemma projective_absoluteToLocal_isIso_of_origin (m n : ℕ)
    (h0 : IsIso (HomologicalComplex.homologyMap
      (projection (ordinaryFunctor ℤ ℤ) (localPair (Space m) (projectiveOrigin m))) (n : ℤ)))
    (x : Space m) :
    IsIso (HomologicalComplex.homologyMap
      (projection (ordinaryFunctor ℤ ℤ) (localPair (Space m) x)) (n : ℤ)) := by
  obtain ⟨e, he⟩ := exists_projectiveLinearHomeomorph m (projectiveOrigin m) x
  have hh := absoluteToLocal_isIso_of_homeomorph (projectiveLinearHomeomorph m e)
    (projectiveOrigin m) (n : ℤ) h0
  rwa [he] at hh

lemma projective_absoluteToRelative_bijective_of_origin (m n : ℕ)
    (h0 : Function.Bijective (absoluteToRelative
      (localPair (Space m) (projectiveOrigin m)) n)) (x : Space m) :
    Function.Bijective (absoluteToRelative (localPair (Space m) x) n) := by
  have hh0 : IsIso (HomologicalComplex.homologyMap
      (projection (ordinaryFunctor ℤ ℤ) (localPair (Space m) (projectiveOrigin m))) (n : ℤ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h0
  haveI := projective_absoluteToLocal_isIso_of_origin m n hh0 x
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

end P202.ComplexProjectiveRing
end

section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Set Topology
namespace P202.ComplexProjective

/-- Descent of a continuous family of complex linear coordinate changes to the
actual projective quotient. -/
lemma projectiveLinearFamily_continuous {A : Type*} [TopologicalSpace A]
    (m : ℕ) (e : A → (Fin (m+1) → ℂ) ≃ₗ[ℂ] (Fin (m+1) → ℂ))
    (he : Continuous (fun p : A × (Fin (m+1) → ℂ) => e p.1 p.2)) :
    Continuous (fun p : A × Space m => projectiveLinearHomeomorph m (e p.1) p.2) := by
  let q : A × NonzeroVectors m → A × Space m := Prod.map id (quotientMap m)
  have hq : IsQuotientMap q :=
    (IsOpenQuotientMap.id.prodMap
      (IsOpenQuotientMap.of_isOpenMap_isQuotientMap
        (quotientMap_open m) (quotientMap_quotient m))).isQuotientMap
  apply hq.continuous_iff.mpr
  change Continuous (quotientMap m ∘ fun p : A × NonzeroVectors m =>
    ⟨e p.1 p.2.val, fun h => p.2.property ((e p.1).injective (by simpa using h))⟩)
  exact (quotientMap_continuous m).comp
    ((he.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _)

/-- On the two eigenspaces of a coordinate transposition, multiply respectively
by 1 and z. For z≠0 this is an invertible complex linear map. -/
def swapInterpolationLinear (m : ℕ) (j k : Fin (m+1)) (z : ℂ) :
    (Fin (m+1) → ℂ) →ₗ[ℂ] (Fin (m+1) → ℂ) :=
  ((1+z)/2) • LinearMap.id +
    ((1-z)/2) • (LinearEquiv.funCongrLeft ℂ ℂ (Equiv.swap j k)).toLinearMap

lemma swapInterpolationLinear_apply (m : ℕ) (j k : Fin (m+1)) (z : ℂ)
    (v : Fin (m+1) → ℂ) (i : Fin (m+1)) :
    swapInterpolationLinear m j k z v i =
      ((1+z)/2) * v i + ((1-z)/2) * v (Equiv.swap j k i) := rfl

lemma swapInterpolationLinear_inv (m : ℕ) (j k : Fin (m+1)) (z : ℂ) (hz : z ≠ 0)
    (v : Fin (m+1) → ℂ) :
    swapInterpolationLinear m j k z⁻¹ (swapInterpolationLinear m j k z v) = v := by
  ext i
  simp only [swapInterpolationLinear_apply, Equiv.swap_apply_self]
  field_simp [hz]
  ring

def swapInterpolation (m : ℕ) (j k : Fin (m+1)) (z : ℂ) (hz : z ≠ 0) :
    (Fin (m+1) → ℂ) ≃ₗ[ℂ] (Fin (m+1) → ℂ) :=
  { swapInterpolationLinear m j k z with
    invFun := swapInterpolationLinear m j k z⁻¹
    left_inv := swapInterpolationLinear_inv m j k z hz
    right_inv := by
      intro v
      simpa using swapInterpolationLinear_inv m j k z⁻¹ (inv_ne_zero hz) v }

lemma swapInterpolation_one (m : ℕ) (j k : Fin (m+1)) :
    swapInterpolation m j k 1 one_ne_zero = LinearEquiv.refl ℂ _ := by
  ext v i
  simp [swapInterpolation, swapInterpolationLinear_apply]

lemma swapInterpolation_neg_one (m : ℕ) (j k : Fin (m+1)) :
    swapInterpolation m j k (-1) (by norm_num) =
      LinearEquiv.funCongrLeft ℂ ℂ (Equiv.swap j k) := by
  ext v i
  simp [swapInterpolation, swapInterpolationLinear_apply]

/-- The eigenvalue on the antisymmetric complex line turns through half a
circle. The symmetric subspace stays fixed. -/
def swapPhase (t : unitInterval) : ℂ :=
  Complex.exp (((t.val : ℂ) * Real.pi) * Complex.I)

lemma swapPhase_ne_zero (t : unitInterval) : swapPhase t ≠ 0 :=
  Complex.exp_ne_zero _

lemma swapPhase_zero : swapPhase 0 = 1 := by simp [swapPhase]

lemma swapPhase_one : swapPhase 1 = -1 := by
  simp [swapPhase]

@[fun_prop] lemma swapPhase_continuous : Continuous swapPhase := by
  unfold swapPhase
  fun_prop

/-- The literal coordinate transposition is joined to the identity by complex
linear automorphisms; this also covers j=k and the zero-dimensional case. -/
def coordinateSwapHomotopy (m : ℕ) (j k : Fin (m+1)) :
    TopCat.Homotopy (𝟙 (TopCat.of (Space m)))
      (TopCat.ofHom ⟨coordinatePermutation m (Equiv.swap j k),
        (coordinatePermutation m (Equiv.swap j k)).continuous⟩) where
  toFun p := projectiveLinearHomeomorph m
    (swapInterpolation m j k (swapPhase p.1) (swapPhase_ne_zero p.1)) p.2
  continuous_toFun := by
    apply projectiveLinearFamily_continuous (A := unitInterval) m
      (fun t => swapInterpolation m j k (swapPhase t) (swapPhase_ne_zero t))
    apply continuous_pi
    intro i
    change Continuous (fun p : unitInterval × (Fin (m+1) → ℂ) =>
      ((1+swapPhase p.1)/2) * p.2 i +
        ((1-swapPhase p.1)/2) * p.2 (Equiv.swap j k i))
    fun_prop
  map_zero_left p := by
    dsimp
    simp only [swapPhase_zero, swapInterpolation_one]
    induction p using Projectivization.ind with | h v hv =>
    rfl
  map_one_left p := by
    dsimp
    simp only [swapPhase_one, swapInterpolation_neg_one]
    rfl

end P202.ComplexProjective

namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.CohomologyPairs P202Specs.CupProduct

/-- A coordinate swap acts as the identity on the actual singular cohomology,
by the explicit complex isotopy above and the accepted prism theorem. -/
lemma coordinateSwap_pullback (m : ℕ) (j k : Fin (m+1)) (n : ℕ) :
    hPullback ℤ
      (TopCat.ofHom ⟨coordinatePermutation m (Equiv.swap j k),
        (coordinatePermutation m (Equiv.swap j k)).continuous⟩) n =
      LinearMap.id := by
  have h := (P202.CohomologyPairs.homotopy_invariant ℤ ℤ).1
    (coordinateSwapHomotopy m j k) (n : ℤ)
  rw [op_id, (ordinaryCohomologyFunctor ℤ ℤ (n : ℤ)).map_id] at h
  exact congrArg ModuleCat.Hom.hom h.symm

open P202Specs.RelativeSingularChains P202Specs.ComplexProjectiveRing

/-- Forgetting relative support commutes with the actual pullback for every
map of pairs. This is the square used to compare hyperplane Thom images. -/
lemma ordinaryImage_pullback {P Q : Pair} (f : P ⟶ Q) (n : ℕ)
    (a : relativeCohomology ℤ ℤ Q (n : ℤ)) :
    hPullback ℤ f.map n (ordinaryImage Q n a) =
      ordinaryImage P n ((relativeCohomologyFunctor ℤ ℤ (n : ℤ)).map f.op a) := by
  have h := congrArg (fun (g : relativeCochains ℤ ℤ Q ⟶ ordinaryCochains ℤ ℤ P.space) =>
    HomologicalComplex.homologyMap g (n : ℤ)) (cochainSequenceMap ℤ ℤ f).comm₁₂
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun g => g.hom a) h.symm

/-- The actual projective space paired with the complement of a coordinate
hyperplane, including the empty hyperplane in CP⁰. -/
def coordinateHyperplanePair (m : ℕ) (j : Fin (m+1)) : Pair :=
  ⟨projectiveSpace m, (coordinateHyperplane m j)ᶜ⟩

/-- The swap transports the complementary hyperplane pairs themselves. -/
def coordinateSwapPair (m : ℕ) (j k : Fin (m+1)) :
    coordinateHyperplanePair m j ⟶ coordinateHyperplanePair m k where
  map := TopCat.ofHom ⟨coordinatePermutation m (Equiv.swap j k),
    (coordinatePermutation m (Equiv.swap j k)).continuous⟩
  mapsTo := by
    intro x hx hy
    apply hx
    have h := (coordinatePermutation_hyperplane m (Equiv.swap j k) k x).mp hy
    simpa using h

/-- Transported coordinate hyperplane classes have exactly equal ordinary
images; the conclusion uses the explicit complex isotopy, not a chosen action
on an abstract cyclic group. -/
lemma ordinaryImage_coordinateSwapPair (m : ℕ) (j k : Fin (m+1)) (n : ℕ)
    (a : relativeCohomology ℤ ℤ (coordinateHyperplanePair m k) (n : ℤ)) :
    ordinaryImage (coordinateHyperplanePair m j) n
      ((relativeCohomologyFunctor ℤ ℤ (n : ℤ)).map (coordinateSwapPair m j k).op a) =
      ordinaryImage (coordinateHyperplanePair m k) n a := by
  rw [← ordinaryImage_pullback]
  change hPullback ℤ
    (TopCat.ofHom ⟨coordinatePermutation m (Equiv.swap j k),
      (coordinatePermutation m (Equiv.swap j k)).continuous⟩) n _ = _
  rw [coordinateSwap_pullback]
  rfl

end P202.ComplexProjectiveRing
end

section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Set Topology
namespace P202.ComplexProjective
open P202Specs.ComplexProjectiveRing

abbrev PuncturedSpace (m : ℕ) := {p : Space (m+1) // p ≠ projectiveOrigin (m+1)}
abbrev PuncturedVectors (m : ℕ) :=
  {v : NonzeroVectors (m+1) // quotientMap (m+1) v ≠ projectiveOrigin (m+1)}

def puncturedQuotient (m : ℕ) : PuncturedVectors m → PuncturedSpace m :=
  fun v => ⟨quotientMap (m+1) v.val, v.property⟩

lemma puncturedQuotient_openQuotient (m : ℕ) : IsOpenQuotientMap (puncturedQuotient m) :=
  (IsOpenQuotientMap.of_isOpenMap_isQuotientMap
    (quotientMap_open (m+1)) (quotientMap_quotient (m+1))).restrictPreimage
      {p : Space (m+1) | p ≠ projectiveOrigin (m+1)}

def firstCoordinates (m : ℕ) : (Fin (m+2) → ℂ) →ₗ[ℂ] (Fin (m+1) → ℂ) where
  toFun v j := v j.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma firstCoordinates_nonzero (m : ℕ) (v : Fin (m+2) → ℂ) (hv : v ≠ 0)
    (hp : mk v hv ≠ projectiveOrigin (m+1)) : firstCoordinates m v ≠ 0 := by
  intro hz
  apply hp
  apply Set.mem_singleton_iff.mp
  change mk v hv ∈ {affineChart (m+1) (m+1) le_rfl 0}
  rw [← firstCoordinateHyperplanes_intersection]
  apply Set.mem_iInter.mpr
  intro j
  apply (coordinateHyperplane_mk j.castSucc v hv).mpr
  exact congrFun hz j

def puncturedRetraction (m : ℕ) (p : PuncturedSpace m) : Space m :=
  mk (firstCoordinates m p.val.rep)
    (firstCoordinates_nonzero m p.val.rep p.val.rep_nonzero (by
      simpa only [mk, Projectivization.mk_rep] using p.property))

lemma puncturedRetraction_mk (m : ℕ) (v : Fin (m+2) → ℂ) (hv : v ≠ 0)
    (hp : mk v hv ≠ projectiveOrigin (m+1)) :
    puncturedRetraction m ⟨mk v hv, hp⟩ =
      mk (firstCoordinates m v) (firstCoordinates_nonzero m v hv hp) := by
  let p : PuncturedSpace m := ⟨mk v hv, hp⟩
  obtain ⟨a, ha⟩ := (mk_eq_mk p.val.rep v p.val.rep_nonzero hv).mp
    (by simpa only [p, mk] using Projectivization.mk_rep p.val)
  apply (mk_eq_mk _ _ _ _).mpr
  exact ⟨a, congrArg (firstCoordinates m) ha⟩

lemma puncturedRetraction_continuous (m : ℕ) : Continuous (puncturedRetraction m) := by
  apply (puncturedQuotient_openQuotient m).isQuotientMap.continuous_iff.mpr
  have he : puncturedRetraction m ∘ puncturedQuotient m =
      quotientMap m ∘ fun v : PuncturedVectors m =>
        (⟨firstCoordinates m v.val.val,
          firstCoordinates_nonzero m v.val.val v.val.property v.property⟩ : NonzeroVectors m) := by
    funext v
    exact puncturedRetraction_mk m v.val.val v.val.property v.property
  rw [he]
  exact (quotientMap_continuous m).comp
    (((firstCoordinates m).continuous_of_finiteDimensional.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)

lemma mk_eq_origin_iff_firstCoordinates (m : ℕ) (v : Fin (m+2) → ℂ) (hv : v ≠ 0) :
    mk v hv = projectiveOrigin (m+1) ↔ firstCoordinates m v = 0 := by
  have h : mk v hv ∈ (⋂ j : Fin (m+1), coordinateHyperplane (m+1) j.castSucc) ↔
      firstCoordinates m v = 0 := by
    simp only [Set.mem_iInter, coordinateHyperplane_mk]
    exact ⟨fun h => funext h, fun h j => congrFun h j⟩
  simpa only [firstCoordinateHyperplanes_intersection, Set.mem_singleton_iff,
    projectiveOrigin] using h

/-- Scale only the last homogeneous coordinate. On the punctured space the
first coordinates keep the vector nonzero, even at scale zero. -/
def scaleLastVector (m : ℕ) (s : ℂ) : (Fin (m+2) → ℂ) →ₗ[ℂ] (Fin (m+2) → ℂ) where
  toFun v i := if i = Fin.last (m+1) then s * v i else v i
  map_add' v w := by ext i; dsimp; split <;> simp [mul_add]
  map_smul' a v := by
    ext i
    dsimp
    split <;> ring

lemma firstCoordinates_scaleLast (m : ℕ) (s : ℂ) (v : Fin (m+2) → ℂ) :
    firstCoordinates m (scaleLastVector m s v) = firstCoordinates m v := by
  ext j
  simp [firstCoordinates, scaleLastVector, Fin.castSucc_ne_last]

lemma scaleLastVector_one (m : ℕ) (v : Fin (m+2) → ℂ) :
    scaleLastVector m 1 v = v := by ext i; simp [scaleLastVector]

lemma scaleLastVector_zero (m : ℕ) (v : Fin (m+2) → ℂ) :
    scaleLastVector m 0 v =
      inclusionVector (m+1) m (Nat.le_succ m) (firstCoordinates m v) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [scaleLastVector, inclusionVector]
  · have hj : j.val ≤ m := by omega
    simp [scaleLastVector, firstCoordinates, inclusionVector, Fin.castSucc_ne_last, hj]

lemma scaleLastVector_nonzero (m : ℕ) (s : ℂ) (v : Fin (m+2) → ℂ) (hv : v ≠ 0)
    (hp : mk v hv ≠ projectiveOrigin (m+1)) : scaleLastVector m s v ≠ 0 := by
  intro hz
  apply firstCoordinates_nonzero m v hv hp
  simpa only [firstCoordinates_scaleLast, map_zero] using congrArg (firstCoordinates m) hz

lemma scaleLastVector_ne_origin (m : ℕ) (s : ℂ) (v : Fin (m+2) → ℂ) (hv : v ≠ 0)
    (hp : mk v hv ≠ projectiveOrigin (m+1)) :
    mk (scaleLastVector m s v) (scaleLastVector_nonzero m s v hv hp) ≠ projectiveOrigin (m+1) := by
  rw [ne_eq, mk_eq_origin_iff_firstCoordinates, firstCoordinates_scaleLast]
  exact firstCoordinates_nonzero m v hv hp

lemma scaleLastVector_continuous (m : ℕ) :
    Continuous (fun p : ℂ × (Fin (m+2) → ℂ) => scaleLastVector m p.1 p.2) := by
  apply continuous_pi
  intro i
  dsimp [scaleLastVector]
  split
  · exact continuous_fst.mul ((continuous_apply i).comp continuous_snd)
  · exact (continuous_apply i).comp continuous_snd

def puncturedScale (m : ℕ) (s : ℂ) (p : PuncturedSpace m) : PuncturedSpace m :=
  ⟨mk (scaleLastVector m s p.val.rep)
    (scaleLastVector_nonzero m s p.val.rep p.val.rep_nonzero (by
      simpa only [mk, Projectivization.mk_rep] using p.property)),
    scaleLastVector_ne_origin m s p.val.rep p.val.rep_nonzero (by
      simpa only [mk, Projectivization.mk_rep] using p.property)⟩

lemma puncturedScale_mk (m : ℕ) (s : ℂ) (v : Fin (m+2) → ℂ) (hv : v ≠ 0)
    (hp : mk v hv ≠ projectiveOrigin (m+1)) :
    puncturedScale m s ⟨mk v hv, hp⟩ =
      ⟨mk (scaleLastVector m s v) (scaleLastVector_nonzero m s v hv hp),
        scaleLastVector_ne_origin m s v hv hp⟩ := by
  let p : PuncturedSpace m := ⟨mk v hv, hp⟩
  obtain ⟨a, ha⟩ := (mk_eq_mk p.val.rep v p.val.rep_nonzero hv).mp
    (by simpa only [p, mk] using Projectivization.mk_rep p.val)
  apply Subtype.ext
  apply (mk_eq_mk _ _ _ _).mpr
  refine ⟨a, ?_⟩
  simpa only [Units.smul_def, map_smul] using congrArg (scaleLastVector m s) ha

lemma puncturedScale_continuous (m : ℕ) :
    Continuous (fun p : ℂ × PuncturedSpace m => puncturedScale m p.1 p.2) := by
  have hq := ((IsOpenQuotientMap.id : IsOpenQuotientMap (id : ℂ → ℂ)).prodMap
    (puncturedQuotient_openQuotient m)).isQuotientMap
  apply hq.continuous_iff.mpr
  have he : (fun p : ℂ × PuncturedSpace m => puncturedScale m p.1 p.2) ∘
      Prod.map id (puncturedQuotient m) =
      fun p : ℂ × PuncturedVectors m =>
        (⟨mk (scaleLastVector m p.1 p.2.val.val)
          (scaleLastVector_nonzero m p.1 p.2.val.val p.2.val.property p.2.property),
          scaleLastVector_ne_origin m p.1 p.2.val.val p.2.val.property p.2.property⟩ :
          PuncturedSpace m) := by
    funext p
    exact puncturedScale_mk m p.1 p.2.val.val p.2.val.property p.2.property
  rw [he]
  apply Continuous.subtype_mk
  change Continuous (quotientMap (m+1) ∘ fun p : ℂ × PuncturedVectors m =>
    (⟨scaleLastVector m p.1 p.2.val.val,
      scaleLastVector_nonzero m p.1 p.2.val.val p.2.val.property p.2.property⟩ : NonzeroVectors (m+1)))
  apply (quotientMap_continuous (m+1)).comp
  exact ((scaleLastVector_continuous m).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_snd)))).subtype_mk _

lemma puncturedScale_one (m : ℕ) (p : PuncturedSpace m) : puncturedScale m 1 p = p := by
  apply Subtype.ext
  change mk (scaleLastVector m 1 p.val.rep) _ = p.val
  simp only [scaleLastVector_one, mk, Projectivization.mk_rep]

lemma puncturedScale_zero_val (m : ℕ) (p : PuncturedSpace m) :
    (puncturedScale m 0 p).val = inclusion (m+1) m (Nat.le_succ m) (puncturedRetraction m p) := by
  change mk (scaleLastVector m 0 p.val.rep) _ =
    mk (inclusionVector (m+1) m (Nat.le_succ m) (firstCoordinates m p.val.rep)) _
  apply (mk_eq_mk' _ _ _ _).mpr
  exact ⟨1, by simpa only [one_smul] using (scaleLastVector_zero m p.val.rep).symm⟩

lemma firstCoordinates_inclusion (m : ℕ) (v : Fin (m+1) → ℂ) :
    firstCoordinates m (inclusionVector (m+1) m (Nat.le_succ m) v) = v := by
  ext j
  have hj : j.val ≤ m := by omega
  simp [firstCoordinates, inclusionVector, hj]

lemma inclusion_ne_origin (m : ℕ) (p : Space m) :
    inclusion (m+1) m (Nat.le_succ m) p ≠ projectiveOrigin (m+1) := by
  induction p using Projectivization.ind with | h v hv =>
  change mk (inclusionVector (m+1) m (Nat.le_succ m) v) _ ≠ _
  rw [ne_eq, mk_eq_origin_iff_firstCoordinates, firstCoordinates_inclusion]
  exact hv

def puncturedInclusion (m : ℕ) (p : Space m) : PuncturedSpace m :=
  ⟨inclusion (m+1) m (Nat.le_succ m) p, inclusion_ne_origin m p⟩

lemma puncturedInclusion_continuous (m : ℕ) : Continuous (puncturedInclusion m) :=
  (inclusion_continuous (m+1) m (Nat.le_succ m)).subtype_mk _

lemma puncturedRetraction_inclusion (m : ℕ) (p : Space m) :
    puncturedRetraction m (puncturedInclusion m p) = p := by
  induction p using Projectivization.ind with | h v hv =>
  change puncturedRetraction m ⟨mk (inclusionVector (m+1) m (Nat.le_succ m) v) _, _⟩ = mk v hv
  rw [puncturedRetraction_mk]
  simp only [firstCoordinates_inclusion]

def puncturedRetractionMap (m : ℕ) : TopCat.of (PuncturedSpace m) ⟶ TopCat.of (Space m) :=
  TopCat.ofHom ⟨puncturedRetraction m, puncturedRetraction_continuous m⟩

def puncturedInclusionMap (m : ℕ) : TopCat.of (Space m) ⟶ TopCat.of (PuncturedSpace m) :=
  TopCat.ofHom ⟨puncturedInclusion m, puncturedInclusion_continuous m⟩

/-- The complement of the affine origin deformation retracts onto the literal
last-coordinate hyperplane, by scaling the last homogeneous coordinate to zero. -/
def puncturedRetractionHomotopy (m : ℕ) :
    TopCat.Homotopy (𝟙 (TopCat.of (PuncturedSpace m)))
      (puncturedRetractionMap m ≫ puncturedInclusionMap m) where
  toFun p := puncturedScale m (1-(p.1.val : ℂ)) p.2
  continuous_toFun := (puncturedScale_continuous m).comp
    ((continuous_const.sub (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)
  map_zero_left p := by
    change puncturedScale m (1-(0:ℂ)) p = p
    simpa only [sub_zero] using puncturedScale_one m p
  map_one_left p := by
    apply Subtype.ext
    change (puncturedScale m (1-(1:ℂ)) p).val =
      inclusion (m+1) m (Nat.le_succ m) (puncturedRetraction m p)
    simpa only [sub_self] using puncturedScale_zero_val m p

lemma puncturedRetraction_homology_isIso (m : ℕ) (j : ℤ) :
    IsIso ((P202Specs.SingularChains.homologyFunctor ℤ ℤ j).map (puncturedRetractionMap m)) := by
  have he : puncturedInclusionMap m ≫ puncturedRetractionMap m = 𝟙 _ := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact puncturedRetraction_inclusion m
  have hf : TopCat.Homotopy (puncturedInclusionMap m ≫ puncturedRetractionMap m) (𝟙 _) := by
    rw [he]
    exact TopCat.Homotopy.refl _
  exact (P202.PrismHomotopy.homologyIso ℤ ℤ (puncturedRetractionMap m)
    (puncturedInclusionMap m) (puncturedRetractionHomotopy m).symm hf j).1


end P202.ComplexProjective
end

section
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation

lemma puncturedOrigin_homology_above (m n : ℕ) (hn : 2*m < n) :
    IsZero (P202Specs.SingularChains.homology ℤ ℤ (TopCat.of (PuncturedSpace m)) (n : ℤ)) := by
  haveI := puncturedRetraction_homology_isIso m (n : ℤ)
  apply (asIso ((homologyFunctor ℤ ℤ (n : ℤ)).map (puncturedRetractionMap m))).isZero_iff.mpr
  apply (P202.ComplexProjective.homology m n).2
  rintro ⟨r,hr,rfl⟩
  omega

lemma origin_absoluteToLocal_isIso (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (projection (ordinaryFunctor ℤ ℤ)
        (localPair (Space (m+1)) (projectiveOrigin (m+1)))) ((2*(m+1) : ℕ) : ℤ)) := by
  let P := localPair (Space (m+1)) (projectiveOrigin (m+1))
  let hS := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.ordinary_short_exact ℤ ℤ P)
  have hz : IsZero (P202Specs.SingularChains.homology ℤ ℤ P.sub ((2*(m+1) : ℕ) : ℤ)) :=
    puncturedOrigin_homology_above m (2*(m+1)) (by omega)
  have hz' : IsZero (P202Specs.SingularChains.homology ℤ ℤ P.sub
      (((2*(m+1) : ℕ) : ℤ)-1)) := by
    have hidx : (((2*(m+1) : ℕ) : ℤ)-1) = ((2*m+1 : ℕ) : ℤ) := by omega
    rw [hidx]
    exact puncturedOrigin_homology_above m (2*m+1) (by omega)
  haveI : Mono (HomologicalComplex.homologyMap (projection (ordinaryFunctor ℤ ℤ) P)
      ((2*(m+1) : ℕ) : ℤ)) :=
    (hS.homology_exact₂ _).mono_g (hz.eq_of_src _ _)
  haveI : Epi (HomologicalComplex.homologyMap (projection (ordinaryFunctor ℤ ℤ) P)
      ((2*(m+1) : ℕ) : ℤ)) :=
    (hS.homology_exact₃ ((2*(m+1) : ℕ) : ℤ) (((2*(m+1) : ℕ) : ℤ)-1) (by simp)).epi_f
      (hz'.eq_of_tgt _ _)
  change IsIso (HomologicalComplex.homologyMap (projection (ordinaryFunctor ℤ ℤ) P) _)
  exact isIso_of_mono_of_epi _

lemma origin_absoluteToLocal_bijective (m : ℕ) :
    Function.Bijective (absoluteToRelative (localPair (Space (m+1)) (projectiveOrigin (m+1)))
      (2*(m+1))) := by
  haveI := origin_absoluteToLocal_isIso m
  exact (asIso (HomologicalComplex.homologyMap
    (projection (ordinaryFunctor ℤ ℤ)
      (localPair (Space (m+1)) (projectiveOrigin (m+1)))) ((2*(m+1) : ℕ) : ℤ))).toLinearEquiv.bijective
end P202.ComplexProjectiveRing
end

section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation

/-- The actual absolute-to-local map is an isomorphism in top degree at every
projective point. The proof includes CP⁰, whose punctured subspace is empty. -/
lemma absoluteToLocal_top_bijective (i : ℕ) (x : Space i) :
    Function.Bijective (absoluteToRelative (localPair (Space i) x) (2*i)) := by
  cases i with
  | zero => exact (pointAbsoluteLocalEquiv x).bijective
  | succ m =>
    exact projective_absoluteToRelative_bijective_of_origin (m+1) (2*(m+1))
      (origin_absoluteToLocal_bijective m) x

def complexFundamental (i : ℕ) : homology ℤ ℤ (projectiveSpace i) ((2*i : ℕ) : ℤ) :=
  (LinearEquiv.ofBijective
    (absoluteToRelative (localPair (Space i) (projectiveOrigin i)) (2*i))
    (absoluteToLocal_top_bijective i (projectiveOrigin i))).symm (positiveLocalClass i)

lemma complexFundamental_to_origin (i : ℕ) :
    absoluteToRelative (localPair (Space i) (projectiveOrigin i)) (2*i) (complexFundamental i) =
      positiveLocalClass i :=
  (LinearEquiv.ofBijective _ (absoluteToLocal_top_bijective i (projectiveOrigin i))).apply_symm_apply _

lemma complexFundamental_generator (i : ℕ) : IsGenerator ℤ (complexFundamental i) := by
  let e := LinearEquiv.ofBijective
    (absoluteToRelative (localPair (Space i) (projectiveOrigin i)) (2*i))
    (absoluteToLocal_top_bijective i (projectiveOrigin i))
  apply (P202.LocalOrientation.generator_map_iff ℤ e (complexFundamental i)).mp
  change IsGenerator ℤ
    (absoluteToRelative (localPair (Space i) (projectiveOrigin i)) (2*i) (complexFundamental i))
  rw [complexFundamental_to_origin]
  exact positiveLocalClass_isGenerator i

lemma complexFundamental_localGenerators (i : ℕ) (x : Space i) :
    IsGenerator ℤ (absoluteToRelative (localPair (Space i) x) (2*i) (complexFundamental i)) := by
  exact (P202.LocalOrientation.generator_map_iff ℤ
    (LinearEquiv.ofBijective _ (absoluteToLocal_top_bijective i x)) (complexFundamental i)).mpr
    (complexFundamental_generator i)

/-- The compatible global orientation fixed by the positive ordered complex
simplex in the last-coordinate chart. Its local classes are the restrictions
of one genuine ordinary fundamental class. -/
def complexOrientation (i : ℕ) :
    Orientation ℤ (projectiveSmoothManifold i).topologicalManifold :=
  ⟨fun x => absoluteToRelative (localPair (Space i) x) (2*i) (complexFundamental i),
    orientation_of_absoluteLocalGenerators _ (complexFundamental i) (complexFundamental_localGenerators i)⟩

def complexFundamentalData (i : ℕ) : ComplexFundamentalData i where
  manifold := (projectiveSmoothManifold i).topologicalManifold
  orientation := complexOrientation i
  localSimplex := positiveLocalSimplex i
  localSimplex_formula := positiveLocalSimplex_formula i
  simplex_cycle := positiveSimplex_cycle (2*i)
  orientation_positive := by
    change _ = absoluteToRelative (localPair (Space i) (projectiveOrigin i)) (2*i) (complexFundamental i)
    rw [complexFundamental_to_origin]
    exact (positiveLocalClass_formula i).symm
  fundamental := complexFundamental i
  fundamental_values := absoluteLocalOrientation_fundamental_values (complexFundamental i)

/-- All dimensions, with no orientation-existence certificate as a premise. -/
theorem fundamentalClasses : ∀ i : ℕ, Nonempty (ComplexFundamentalData i) :=
  fun i => ⟨complexFundamentalData i⟩

end P202.ComplexProjectiveRing
end

section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace P202.ComplexProjective
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.MapClassData SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData

/-- Projective complex linear automorphisms preserve the explicit ratio-chart smooth structure. -/
def projectiveLinearDiffeomorph (m : ℕ)
    (e : (Fin (m+1) → ℂ) ≃ₗ[ℂ] (Fin (m+1) → ℂ)) :
    Diffeomorph (projectiveSmoothManifold m).smoothStructure.val
      (projectiveSmoothManifold m).smoothStructure.val where
  toEquiv := (projectiveLinearHomeomorph m e).toEquiv
  contDiff_toFun := projectiveLinearMap_smooth e.toLinearMap e.injective
  contDiff_invFun := projectiveLinearMap_smooth e.symm.toLinearMap e.symm.injective

lemma projectiveLinearHomeomorph_smoothEmbedding (m : ℕ)
    (e : (Fin (m+1) → ℂ) ≃ₗ[ℂ] (Fin (m+1) → ℂ)) :
    IsSmoothEmbedding (projectiveSmoothManifold m) (projectiveSmoothManifold m)
      (projectiveLinearHomeomorph m e) := by
  let d := projectiveLinearDiffeomorph m e
  have hs : IsSmoothMap (projectiveSmoothManifold m) (projectiveSmoothManifold m)
      (projectiveLinearHomeomorph m e) := d.contDiff_toFun
  refine ⟨hs, (projectiveLinearHomeomorph m e).injective, ?_,
    (projectiveLinearHomeomorph m e).isEmbedding.toHomeomorph, fun _ => rfl⟩
  intro p
  obtain ⟨L,hL⟩ := SmoothManifolds.differential_diffeomorph _ _ d p
  exact (SmoothManifolds.MapClasses.smooth_tangent_invariants _ _ _ hs p L.toLinearMap hL).2.1.mpr L.injective

lemma coordinatePermutation_smoothEmbedding (m : ℕ) (e : Equiv.Perm (Fin (m+1))) :
    IsSmoothEmbedding (projectiveSmoothManifold m) (projectiveSmoothManifold m)
      (coordinatePermutation m e) :=
  projectiveLinearHomeomorph_smoothEmbedding m (LinearEquiv.funCongrLeft ℂ ℂ e)

/-- Every actual coordinate hyperplane is smoothly embedded with the standard source atlas. -/
lemma coordinateHyperplaneInclusion_smoothEmbedding (m : ℕ) (j : Fin (m+2)) :
    IsSmoothEmbedding (projectiveSmoothManifold m) (projectiveSmoothManifold (m+1))
      (coordinateHyperplaneInclusion m j) :=
  SmoothManifolds.TransversePreimage.smoothEmbedding_comp
    (projectiveSmoothManifold m) (projectiveSmoothManifold (m+1)) (projectiveSmoothManifold (m+1))
    (inclusion (m+1) m (Nat.le_succ m))
    (coordinatePermutation (m+1) (Equiv.swap (Fin.last (m+1)) j))
    (inclusion_smoothEmbedding (m+1) m (Nat.le_succ m))
    (coordinatePermutation_smoothEmbedding (m+1) (Equiv.swap (Fin.last (m+1)) j))

lemma coordinateHyperplaneInclusion_normal_exists (m : ℕ) (j : Fin (m+2)) :
    Nonempty (NormalBundle (projectiveSmoothManifold m) (projectiveSmoothManifold (m+1))
      (coordinateHyperplaneInclusion m j)) :=
  SmoothManifolds.BundleOperations.exists_normal _ _ _
    (coordinateHyperplaneInclusion_smoothEmbedding m j)

lemma coordinateHyperplaneInclusion_normalizedTubular_exists (m : ℕ) (j : Fin (m+2))
    (N : NormalBundle (projectiveSmoothManifold m) (projectiveSmoothManifold (m+1))
      (coordinateHyperplaneInclusion m j)) :
    ∃ K : TubularNeighborhood N, P202Specs.ThomClass.NormalCompatible N K :=
  P202.ThomClass.normalized_tubular_exists (coordinateHyperplaneInclusion_smoothEmbedding m j) N

/-- The normal bundle and normalized tube are outputs for each coordinate hyperplane. -/
lemma coordinateHyperplaneInclusion_normalizedNormal_exists (m : ℕ) (j : Fin (m+2)) :
    ∃ N : NormalBundle (projectiveSmoothManifold m) (projectiveSmoothManifold (m+1))
      (coordinateHyperplaneInclusion m j),
      ∃ K : TubularNeighborhood N, P202Specs.ThomClass.NormalCompatible N K := by
  obtain ⟨N⟩ := coordinateHyperplaneInclusion_normal_exists m j
  exact ⟨N, coordinateHyperplaneInclusion_normalizedTubular_exists m j N⟩

end P202.ComplexProjective
end

section
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs

lemma positiveLocal_previousHomology_isZero (i : ℕ) :
    IsZero ((ordinary ℤ ℤ (localPair (Space i) (projectiveOrigin i))).homology
      (P202Specs.UniversalCoefficientsCohomology.previousDegree (2*i))) := by
  cases i with
  | zero =>
    exact (P202.RelativeSingularChains.ordinary_negative ℤ ℤ
      (localPair (Space 0) (projectiveOrigin 0)) (-1) (by omega)).2
  | succ i =>
    have hidx : P202Specs.UniversalCoefficientsCohomology.previousDegree (2*(i+1)) =
        ((2*i+1 : ℕ) : ℤ) := by
      rw [P202Specs.UniversalCoefficientsCohomology.previousDegree_eq]
      omega
    rw [hidx]
    exact (P202.LocalOrientation.localHomology ℤ (2*(i+1)) (Space (i+1))
      (forgetSmooth (projectiveSmoothManifold (i+1)))
      (projectiveOrigin (i+1)) (2*i+1)).2 (by omega)

lemma relativeEvaluation_bijective_of_previousHomology_free
    (P : Pair) (n : ℕ)
    (hfree : Module.Free ℤ ((ordinary ℤ ℤ P).homology
      (P202Specs.UniversalCoefficientsCohomology.previousDegree n))) :
    Function.Bijective (relativeEvaluation P n) := by
  let C := ordinary ℤ ℤ P
  let k := P202Specs.UniversalCoefficientsCohomology.previousDegree n
  haveI : Module.Free ℤ (C.homology k) := hfree
  haveI : Subsingleton
      (P202Specs.UniversalCoefficientsCohomology.actualExt ℤ ℤ C k) :=
    P103.Ch11.VanishingAndFlatness.ext_projective ℤ (C.homology k) ℤ Module.Projective.of_free
      (P202Specs.UniversalCoefficientsCohomology.AlgebraicExt.resolutionFamily ℤ (C.homology k)).val
      (P202Specs.UniversalCoefficientsCohomology.AlgebraicExt.resolutionFamily ℤ (C.homology k)).property 0
  obtain ⟨α, σ, hα, hexact, hsurj, hσ⟩ :=
    (P202.UniversalCoefficientsCohomology.all_degrees ℤ ℤ).2 P n
  refine ⟨?_, hsurj⟩
  apply (injective_iff_map_eq_zero (relativeEvaluation P n)).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := (hexact x).mp hx
  have hz : z = 0 := Subsingleton.elim _ _
  rw [hz]
  exact α.toAddMonoidHom.map_zero

lemma positiveLocal_relativeEvaluation_bijective (i : ℕ) :
    Function.Bijective (relativeEvaluation (localPair (Space i) (projectiveOrigin i)) (2*i)) := by
  apply relativeEvaluation_bijective_of_previousHomology_free
  haveI := ModuleCat.subsingleton_of_isZero (positiveLocal_previousHomology_isZero i)
  exact Module.Free.of_subsingleton _ _

def positiveLocalEvaluationEquiv (i : ℕ) :
    relativeCohomology ℤ ℤ (localPair (Space i) (projectiveOrigin i)) ((2*i : ℕ) : ℤ) ≃ₗ[ℤ]
      (LocalGroup ℤ (Space i) (projectiveOrigin i) (2*i) →ₗ[ℤ] ℤ) :=
  LinearEquiv.ofBijective
    (relativeEvaluation (localPair (Space i) (projectiveOrigin i)) (2*i))
    (positiveLocal_relativeEvaluation_bijective i)

def positiveLocalCohomologyEquiv (i : ℕ) :
    relativeCohomology ℤ ℤ (localPair (Space i) (projectiveOrigin i)) ((2*i : ℕ) : ℤ) ≃ₗ[ℤ] ℤ :=
  (positiveLocalEvaluationEquiv i).trans
    ((LinearEquiv.arrowCongr
      (P202.LocalOrientation.generatorEquiv ℤ (positiveLocalClass i)
        (positiveLocalClass_isGenerator i)).symm (LinearEquiv.refl ℤ ℤ)).trans
      (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ))

lemma positiveLocalCohomologyEquiv_apply (i : ℕ)
    (a : relativeCohomology ℤ ℤ (localPair (Space i) (projectiveOrigin i)) ((2*i : ℕ) : ℤ)) :
    positiveLocalCohomologyEquiv i a =
      relativeEvaluation (localPair (Space i) (projectiveOrigin i)) (2*i) a (positiveLocalClass i) := by
  change relativeEvaluation (localPair (Space i) (projectiveOrigin i)) (2*i) a
    (P202.LocalOrientation.generatorEquiv ℤ (positiveLocalClass i)
      (positiveLocalClass_isGenerator i) 1) = _
  rw [P202.LocalOrientation.generatorEquiv_apply, one_smul]

def positiveLocalCohomologyClass (i : ℕ) :
    relativeCohomology ℤ ℤ (localPair (Space i) (projectiveOrigin i)) ((2*i : ℕ) : ℤ) :=
  (positiveLocalCohomologyEquiv i).symm 1

lemma positiveLocalCohomologyClass_evaluation (i : ℕ) :
    relativeEvaluation (localPair (Space i) (projectiveOrigin i)) (2*i)
      (positiveLocalCohomologyClass i) (positiveLocalClass i) = 1 := by
  rw [← positiveLocalCohomologyEquiv_apply]
  exact (positiveLocalCohomologyEquiv i).apply_symm_apply 1

lemma positiveLocalCohomologyClass_isGenerator (i : ℕ) :
    IsGenerator ℤ (positiveLocalCohomologyClass i) :=
  (P202.LocalOrientation.generator_map_iff ℤ (positiveLocalCohomologyEquiv i).symm (1 : ℤ)).mpr
    (P202.LocalOrientation.generator_one ℤ)

end P202.ComplexProjectiveRing

namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs

lemma positiveLocalCohomologyClass_primitive (i : ℕ) :
    Function.Bijective (fun z : ℤ => z • positiveLocalCohomologyClass i) := by
  exact generates_of_pairing_one (positiveLocalCohomologyEquiv i).toAddEquiv
    (positiveLocalCohomologyClass i) (positiveLocalCohomologyEquiv i).toLinearMap.toAddMonoidHom
    ((positiveLocalCohomologyEquiv i).apply_symm_apply 1)

lemma exists_positiveLocalCohomologyGenerator (i : ℕ) :
    ∃ a : relativeCohomology ℤ ℤ (localPair (Space i) (projectiveOrigin i)) ((2*i : ℕ) : ℤ),
      Function.Bijective (fun z : ℤ => z • a) ∧
        relativeEvaluation (localPair (Space i) (projectiveOrigin i)) (2*i)
          a (positiveLocalClass i) = 1 :=
  ⟨positiveLocalCohomologyClass i, positiveLocalCohomologyClass_primitive i,
    positiveLocalCohomologyClass_evaluation i⟩
end P202.ComplexProjectiveRing
end

section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation

/-- The explicit positive-simplex normalization fixes the global class uniquely,
independently of the atlas or orientation witness used in the geometric data. -/
lemma complexFundamentalData_fundamental_eq {i : ℕ} (d : ComplexFundamentalData i) :
    d.fundamental = complexFundamental i := by
  apply (absoluteToLocal_top_bijective i (projectiveOrigin i)).injective
  rw [fundamental_toLocal, complexFundamental_to_origin, ← d.orientation_positive]
  have h : d.localSimplex = positiveLocalSimplex i := by
    apply PairMap.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact d.localSimplex_formula
  rw [h]
  exact (positiveLocalClass_formula i).symm

lemma complexFundamentalData_orientation_eq {i : ℕ} (d : ComplexFundamentalData i) :
    d.orientation.val = (complexOrientation i).val := by
  funext x
  rw [← fundamental_toLocal d x, complexFundamentalData_fundamental_eq]
  rfl

/-- The explicit complex coordinate-swap isotopy preserves the canonically
normalized ordinary complex fundamental class. -/
lemma coordinateSwap_fundamental (i : ℕ) (j k : Fin (i+1)) :
    ((homologyFunctor ℤ ℤ ((2*i : ℕ) : ℤ)).map
      (TopCat.ofHom ⟨coordinatePermutation i (Equiv.swap j k),
        (coordinatePermutation i (Equiv.swap j k)).continuous⟩)) (complexFundamental i) =
      complexFundamental i := by
  have h := (P202.PrismHomotopy.homology ℤ ℤ (coordinateSwapHomotopy i j k)
    ((2*i : ℕ) : ℤ)).1
  rw [(homologyFunctor ℤ ℤ ((2*i : ℕ) : ℤ)).map_id] at h
  exact congrArg (fun f => f (complexFundamental i)) h.symm

end P202.ComplexProjectiveRing
end

section
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs

/-- The canonical positive local cohomology class evaluates to one on the
prescribed local complex orientation. -/
lemma positiveLocalCohomologyClass_orientation_evaluation (i : ℕ) :
    relativeEvaluation (localPair (Space i) (projectiveOrigin i)) (2*i)
      (positiveLocalCohomologyClass i) ((complexOrientation i).val (projectiveOrigin i)) = 1 := by
  change relativeEvaluation _ (2*i) (positiveLocalCohomologyClass i)
    (absoluteToRelative (localPair (Space i) (projectiveOrigin i)) (2*i) (complexFundamental i)) = 1
  rw [complexFundamental_to_origin]
  exact positiveLocalCohomologyClass_evaluation i

/-- Its ordinary image has the source's value-one global normalization. The
remaining ring proof must identify this image with the restricted cup powers. -/
lemma positiveLocalCohomologyClass_global_evaluation (i : ℕ) :
    P202Specs.ComplexProjectiveRing.evaluation i (2*i)
      (ordinaryImage (localPair (Space i) (projectiveOrigin i)) (2*i)
        (positiveLocalCohomologyClass i)) (complexFundamental i) = 1 := by
  exact fundamental_evaluation_one (complexFundamentalData i) (positiveLocalCohomologyClass i)
    (positiveLocalCohomologyClass_orientation_evaluation i)

lemma positiveLocalCohomologyClass_ordinary_primitive (i : ℕ) :
    Function.Bijective (fun z : ℤ => z •
      ordinaryImage (localPair (Space i) (projectiveOrigin i)) (2*i) (positiveLocalCohomologyClass i)) :=
  generator_of_evaluation_one i (2*i) ⟨i,le_rfl,rfl⟩ _ (complexFundamental i)
    (positiveLocalCohomologyClass_global_evaluation i)

/-- The actual forget-support map from local top cohomology to ordinary top
cohomology is bijective, with the positive generators matched. -/
lemma ordinaryImage_local_top_bijective (i : ℕ) :
    Function.Bijective (ordinaryImage (localPair (Space i) (projectiveOrigin i)) (2*i)) := by
  let f := ordinaryImage (localPair (Space i) (projectiveOrigin i)) (2*i)
  let a := positiveLocalCohomologyClass i
  have ha := positiveLocalCohomologyClass_primitive i
  have hb := positiveLocalCohomologyClass_ordinary_primitive i
  constructor
  · intro x y h
    obtain ⟨z,rfl⟩ := ha.surjective x
    obtain ⟨w,rfl⟩ := ha.surjective y
    have hzw : z = w := hb.injective (by simpa only [map_zsmul] using h)
    rw [hzw]
  · intro y
    obtain ⟨z,hz⟩ := hb.surjective y
    exact ⟨z • a, (map_zsmul f z a).trans hz⟩

end P202.ComplexProjectiveRing
end



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.CohomologyPairs P202Specs.CupProduct

/-- The represented singular cup product determines the product independently
of the packaging of its graded ring laws. -/
lemma cohomologyProduct_eq {X : TopCat} (C D : CohomologyRing ℤ X)
    (p q : ℕ) (a : H ℤ X p) (b : H ℤ X q) :
    C.product p q a b = D.product p q a b := by
  have hs (n : ℕ) : Function.Surjective ((ordinaryCochains ℤ ℤ X).homologyπ (n : ℤ)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨a, rfl⟩ := hs p a
  obtain ⟨b, rfl⟩ := hs q b
  obtain ⟨c, hc, hC⟩ := C.represents p q a b
  obtain ⟨d, hd, hD⟩ := D.represents p q a b
  have hcd : c = d := P202.CupProduct.cocycleValue_injective ℤ X (p+q) (hc.trans hd.symm)
  rw [hC, hD, hcd]

/-- Pullback preserves the represented product for independently packaged
singular cup rings on the source and target. -/
lemma cohomologyProduct_pullback {X Y : TopCat} (f : X ⟶ Y)
    (C : CohomologyRing ℤ X) (D : CohomologyRing ℤ Y)
    (p q : ℕ) (a : H ℤ Y p) (b : H ℤ Y q) :
    hPullback ℤ f (p+q) (D.product p q a b) =
      C.product p q (hPullback ℤ f p a) (hPullback ℤ f q b) := by
  have hs (n : ℕ) : Function.Surjective ((ordinaryCochains ℤ ℤ Y).homologyπ (n : ℤ)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨a, rfl⟩ := hs p a
  obtain ⟨b, rfl⟩ := hs q b
  obtain ⟨c, hc, hD⟩ := D.represents p q a b
  let a' := HomologicalComplex.cyclesMap ((ordinaryCochainFunctor ℤ ℤ).map f.op) (p : ℤ) a
  let b' := HomologicalComplex.cyclesMap ((ordinaryCochainFunctor ℤ ℤ).map f.op) (q : ℤ) b
  obtain ⟨d, hd, hC⟩ := C.represents p q a' b'
  rw [hD]
  simp only [P202.CupProduct.hPullback_homologyπ]
  change (ordinaryCochains ℤ ℤ X).homologyπ ((p+q : ℕ) : ℤ)
    (HomologicalComplex.cyclesMap ((ordinaryCochainFunctor ℤ ℤ).map f.op) ((p+q : ℕ) : ℤ) c) =
      C.product p q ((ordinaryCochains ℤ ℤ X).homologyπ (p : ℤ) a')
        ((ordinaryCochains ℤ ℤ X).homologyπ (q : ℤ) b')
  rw [hC]
  congr 1
  apply P202.CupProduct.cocycleValue_injective ℤ X (p+q)
  rw [P202.CupProduct.cocycleValue_pullback, hc, P202.CupProduct.cup_natural, hd]
  dsimp only [a', b']
  rw [P202.CupProduct.cocycleValue_pullback, P202.CupProduct.cocycleValue_pullback]

/-- Pullback also preserves the actual constant-one singular unit. -/
lemma cohomologyUnit_pullback {X Y : TopCat} (f : X ⟶ Y)
    (C : CohomologyRing ℤ X) (D : CohomologyRing ℤ Y) :
    letI := C.gradedRing
    letI := D.gradedRing
    hPullback ℤ f 0 (GradedMonoid.GOne.one (A := H ℤ Y)) =
      (GradedMonoid.GOne.one (A := H ℤ X)) := by
  letI := C.gradedRing
  letI := D.gradedRing
  obtain ⟨a, ha, hD⟩ := D.unit_represents
  obtain ⟨b, hb, hC⟩ := C.unit_represents
  rw [hD, hC]
  have hab : HomologicalComplex.cyclesMap ((ordinaryCochainFunctor ℤ ℤ).map f.op) 0 a = b := by
    apply P202.CupProduct.cocycleValue_injective ℤ X 0
    exact (P202.CupProduct.cocycleValue_pullback ℤ f 0 a).trans
      ((congrArg (pullback ℤ f 0) ha).trans
        ((P202.CupProduct.oneCochain_pullback ℤ f).trans hb.symm))
  exact (P202.CupProduct.hPullback_homologyπ ℤ f 0 a).trans
    (congrArg ((ordinaryCochains ℤ ℤ X).homologyπ 0) hab)

/-- The ordinary pullback is an algebra map for every witness of the singular
cup ring on its endpoints. -/
def cohomologyAlgebraPullback {X Y : TopCat} (f : X ⟶ Y)
    (C : CohomologyRing ℤ X) (D : CohomologyRing ℤ Y) :
    letI := C.gradedRing
    letI := C.algebra
    letI := D.gradedRing
    letI := D.algebra
    HStar ℤ Y →ₐ[ℤ] HStar ℤ X := by
  letI := C.gradedRing
  letI := C.algebra
  letI := D.gradedRing
  letI := D.algebra
  exact P202.CupProduct.gradedAlgebraMap ℤ (H ℤ Y) (H ℤ X)
    (fun n => hPullback ℤ f n) (cohomologyUnit_pullback f C D)
    (by intro p q a b; rw [D.product_eq, C.product_eq]; exact cohomologyProduct_pullback f C D p q a b)

lemma cohomologyAlgebraPullback_of {X Y : TopCat} (f : X ⟶ Y)
    (C : CohomologyRing ℤ X) (D : CohomologyRing ℤ Y) (n : ℕ) (a : H ℤ Y n) :
    letI := C.gradedRing
    letI := C.algebra
    letI := D.gradedRing
    letI := D.algebra
    cohomologyAlgebraPullback f C D (DirectSum.of (H ℤ Y) n a) =
      DirectSum.of (H ℤ X) n (hPullback ℤ f n a) := by
  letI := C.gradedRing
  letI := C.algebra
  letI := D.gradedRing
  letI := D.algebra
  exact P202.CupProduct.gradedAlgebraMap_of ℤ _ _ _ _ _ n a

/-- Naturality of homogeneous powers needs no globally chosen family of ring
structures: all choices represent the same singular cup product. -/
lemma homogeneousPower_pullback_any {m r : ℕ} (f : projectiveSpace r ⟶ projectiveSpace m)
    (C : CohomologyRing ℤ (projectiveSpace r))
    (D : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2) (i : ℕ) :
    hPullback ℤ f (2*i) (homogeneousPower m D v i) =
      homogeneousPower r C (hPullback ℤ f 2 v) i := by
  letI := C.gradedRing
  letI := C.algebra
  letI := D.gradedRing
  letI := D.algebra
  apply DirectSum.of_injective (β := H ℤ (projectiveSpace r)) (2*i)
  rw [← cohomologyAlgebraPullback_of f C D, of_homogeneousPower,
    of_homogeneousPower, map_pow, cohomologyAlgebraPullback_of]

lemma inclusion_comp (m r s : ℕ) (hr : r ≤ m) (hs : s ≤ r) (x : Space s) :
    P202.ComplexProjective.inclusion m r hr (P202.ComplexProjective.inclusion r s hs x) =
      P202.ComplexProjective.inclusion m s (hs.trans hr) x := by
  induction x using Projectivization.ind with | h v hv =>
  simp only [P202.ComplexProjective.inclusion, Projectivization.map_mk]
  have he : inclusionVector m r hr (inclusionVector r s hs v) =
      inclusionVector m s (hs.trans hr) v := by
    ext j
    dsimp only [inclusionVector, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> first | rfl | omega
  exact (P202.ComplexProjective.mk_eq_mk _ _ _ _).mpr ⟨1, by simpa using he.symm⟩

lemma standardInclusion_comp (m r s : ℕ) (hr : r ≤ m) (hs : s ≤ r) :
    standardInclusion r s hs ≫ standardInclusion m r hr =
      standardInclusion m s (hs.trans hr) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  exact inclusion_comp m r s hr hs

lemma standardInclusion_self (m : ℕ) (h : m ≤ m) : standardInclusion m m h = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  induction x using Projectivization.ind with | h v hv =>
  simp only [standardInclusion, P202.ComplexProjective.inclusion, Projectivization.map_mk]
  have he : inclusionVector m m h v = v := by
    ext j
    simp only [inclusionVector, LinearMap.coe_mk, AddHom.coe_mk, dif_pos j.isLt]
  exact (P202.ComplexProjective.mk_eq_mk _ _ _ _).mpr ⟨1, by simpa using he.symm⟩

lemma hPullback_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (a : H ℤ Z n) :
    hPullback ℤ f n (hPullback ℤ g n a) = hPullback ℤ (f ≫ g) n a := by
  change (((ordinaryCohomologyFunctor ℤ ℤ (n : ℤ)).map g.op) ≫
    ((ordinaryCohomologyFunctor ℤ ℤ (n : ℤ)).map f.op)) a = _
  rw [← Functor.map_comp]
  rfl

/-- The positive degree-two generator is fixed by its restriction to the
standard complex projective line and its value on that line's positive
fundamental class. No multiplicative or Thom-class conclusion is assumed. -/
def positiveDegreeTwoClass (m : ℕ) : cohomology (m+1) 2 :=
  (LinearEquiv.ofBijective (hPullback ℤ (standardInclusion (m+1) 1 (by omega)) 2)
    (inclusion_cohomology_bijective (m+1) 1 (by omega) 2 (by omega))).symm
      (ordinaryImage (P202Specs.LocalOrientation.localPair (Space 1) (projectiveOrigin 1)) 2
        (positiveLocalCohomologyClass 1))

lemma positiveDegreeTwoClass_restrict_line (m : ℕ) (h : 1 ≤ m+1) :
    hPullback ℤ (standardInclusion (m+1) 1 h) 2 (positiveDegreeTwoClass m) =
      ordinaryImage (P202Specs.LocalOrientation.localPair (Space 1) (projectiveOrigin 1)) 2
        (positiveLocalCohomologyClass 1) := by
  change (LinearEquiv.ofBijective _
    (inclusion_cohomology_bijective (m+1) 1 h 2 (by omega)))
      ((LinearEquiv.ofBijective _
        (inclusion_cohomology_bijective (m+1) 1 h 2 (by omega))).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

lemma positiveDegreeTwoClass_evaluation (m : ℕ) (h : 1 ≤ m+1) :
    P202Specs.ComplexProjectiveRing.evaluation 1 2
      (hPullback ℤ (standardInclusion (m+1) 1 h) 2 (positiveDegreeTwoClass m))
      (complexFundamental 1) = 1 := by
  rw [positiveDegreeTwoClass_restrict_line]
  exact positiveLocalCohomologyClass_global_evaluation 1

lemma positiveDegreeTwoClass_primitive (m : ℕ) :
    Function.Bijective (fun z : ℤ => z • positiveDegreeTwoClass m) :=
  generator_of_restriction_evaluation_one (m+1) 1 (by omega) _ (complexFundamental 1)
    (positiveDegreeTwoClass_evaluation m (by omega))

lemma positiveDegreeTwoClass_restrict (m r : ℕ) (h : r ≤ m) :
    hPullback ℤ (standardInclusion (m+1) (r+1) (by omega)) 2 (positiveDegreeTwoClass m) =
      positiveDegreeTwoClass r := by
  apply (inclusion_cohomology_bijective (r+1) 1 (by omega) 2 (by omega)).injective
  rw [hPullback_comp, standardInclusion_comp, positiveDegreeTwoClass_restrict_line,
    positiveDegreeTwoClass_restrict_line]

lemma positiveDegreeTwoClass_line : positiveDegreeTwoClass 0 =
    ordinaryImage (P202Specs.LocalOrientation.localPair (Space 1) (projectiveOrigin 1)) 2
      (positiveLocalCohomologyClass 1) := by
  have h := positiveDegreeTwoClass_restrict_line 0 (by omega)
  rw [standardInclusion_self] at h
  change ((ordinaryCohomologyFunctor ℤ ℤ (2 : ℤ)).map (𝟙 (Opposite.op (projectiveSpace 1)))) _ = _ at h
  have hid := congrArg (fun f => f (positiveDegreeTwoClass 0))
    ((ordinaryCohomologyFunctor ℤ ℤ (2 : ℤ)).map_id (Opposite.op (projectiveSpace 1)))
  exact hid.symm.trans h

lemma homogeneousPower_one (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m))
    (v : cohomology m 2) : homogeneousPower m C v 1 = v := by
  letI := C.gradedRing
  apply DirectSum.of_injective (β := H ℤ (projectiveSpace m)) 2
  simpa only [Nat.mul_one, pow_one] using of_homogeneousPower m C v 1

/-- The projective line endpoint of the presentation is already forced by
the positive degree-two generator, the unit, and top-degree vanishing. -/
lemma line_primitivePowers (C : CohomologyRing ℤ (projectiveSpace 1)) :
    PrimitivePowers 1 C (positiveDegreeTwoClass 0) := by
  apply (primitivePowers_iff_homogeneousPower 1 C _).mpr
  intro i hi
  interval_cases i
  · exact homogeneousPower_zero_primitive 1 C _
  · simpa only [homogeneousPower_one] using positiveDegreeTwoClass_primitive 0

lemma linePresentation (C : CohomologyRing ℤ (projectiveSpace 1)) :
    letI := C.gradedRing
    ∃ e : truncatedPolynomial 1 ≃+* totalCohomology 1,
      e (polynomialClass 1 Polynomial.X) =
        DirectSum.of (H ℤ (projectiveSpace 1)) 2 (positiveDegreeTwoClass 0) ∧
      ∀ i : ℕ, i ≤ 1 → ∃ b : cohomology 1 (2*i),
        Function.Bijective (fun z : ℤ => z • b) ∧
        e ((polynomialClass 1 Polynomial.X)^i) =
          DirectSum.of (H ℤ (projectiveSpace 1)) (2*i) b :=
  presentation_of_primitivePowers 1 C _ (line_primitivePowers C)

lemma pointUnit_complexFundamental_evaluation
    (C : CohomologyRing ℤ (projectiveSpace 0)) :
    letI := C.gradedRing
    P202Specs.ComplexProjectiveRing.evaluation 0 0
      (GradedMonoid.GOne.one (A := H ℤ (projectiveSpace 0))) (complexFundamental 0) = 1 := by
  letI := C.gradedRing
  rw [← complexFundamentalData_fundamental_eq pointComplexFundamentalData]
  exact pointUnit_evaluation C

/-- The nullary power has the full local and global unit normalization on the
standard point in every projective space. -/
lemma geometricPower_zero (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m))
    (v : cohomology m 2) :
    letI := C.gradedRing
    ∃ (d : ComplexFundamentalData 0)
      (a : relativeCohomology ℤ ℤ
        (P202Specs.LocalOrientation.localPair (Space 0) (projectiveOrigin 0)) 0)
      (b : cohomology m 0),
      Function.Bijective (fun z : ℤ => z • a) ∧
      relativeEvaluation _ 0 a (d.orientation.val (projectiveOrigin 0)) = 1 ∧
      (DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^0 =
        DirectSum.of (H ℤ (projectiveSpace m)) 0 b ∧
      hPullback ℤ (standardInclusion m 0 (Nat.zero_le m)) 0 b = ordinaryImage _ 0 a ∧
      P202Specs.ComplexProjectiveRing.evaluation 0 0
        (hPullback ℤ (standardInclusion m 0 (Nat.zero_le m)) 0 b) d.fundamental = 1 := by
  let C₀ := (Classical.choice (P202.CupProduct.cohomologyRing ℤ)).ring (projectiveSpace 0)
  letI := C.gradedRing
  letI := C₀.gradedRing
  let a := pointOrdinaryImageEquiv.symm (GradedMonoid.GOne.one (A := H ℤ (projectiveSpace 0)))
  have ha : ordinaryImage _ 0 a = (GradedMonoid.GOne.one (A := H ℤ (projectiveSpace 0))) :=
    pointOrdinaryImageEquiv.apply_symm_apply _
  have hab : Function.Bijective (fun z : ℤ => z • a) := by
    have he : (fun z : ℤ => z • a) =
        pointOrdinaryImageEquiv.symm ∘ (fun z : ℤ => z • (GradedMonoid.GOne.one (A := H ℤ (projectiveSpace 0)))) := by
      funext z
      exact (map_zsmul _ _ _).symm
    rw [he]
    apply pointOrdinaryImageEquiv.symm.bijective.comp
    change Function.Bijective (fun z : ℤ => z • (1 : cohomology 0 0))
    simpa only [homogeneousPower_zero] using homogeneousPower_zero_primitive 0 C₀ 0
  have hu := cohomologyUnit_pullback (standardInclusion m 0 (Nat.zero_le m)) C₀ C
  have heval := pointUnit_complexFundamental_evaluation C₀
  have hea : relativeEvaluation _ 0 a ((complexOrientation 0).val (projectiveOrigin 0)) = 1 := by
    change relativeEvaluation _ 0 a ((complexFundamentalData 0).orientation.val (projectiveOrigin 0)) = 1
    rw [← fundamental_toLocal (complexFundamentalData 0), ← evaluation_ordinaryImage, ha]
    exact heval
  refine ⟨complexFundamentalData 0, a, (GradedMonoid.GOne.one (A := H ℤ (projectiveSpace m))), hab, hea, ?_, ?_, ?_⟩
  · rfl
  · exact hu.trans ha.symm
  · rw [hu]
    exact heval

/-- Assembly of the geometric conclusion from the positive-degree supported
power identities. The point case, orientation evaluations, primitive local
classes and ordinary fundamental evaluations are already supplied here. -/
lemma geometricGenerator_of_positivePower_identifications (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2)
    (hpoint : m = 0 → v = 0)
    (hthom : ∀ k, ∀ h : m = k+1, ∃ d : HyperplaneThomData k,
      h ▸ v = ordinaryImage _ 2 d.thom)
    (hpowers : ∀ i : ℕ, 0 < i → (hi : i ≤ m) →
      hPullback ℤ (standardInclusion m i hi) (2*i) (homogeneousPower m C v i) =
        ordinaryImage (P202Specs.LocalOrientation.localPair (Space i) (projectiveOrigin i))
          (2*i) (positiveLocalCohomologyClass i)) :
    GeometricGenerator m C v := by
  refine ⟨hpoint, ?_, ?_⟩
  · intro k hk
    subst m
    exact hthom k rfl
  letI := C.gradedRing
  intro i hi
  by_cases hz : i = 0
  · subst i
    obtain ⟨d,a,b,ha,he,hpower,hrest,hglobal⟩ := geometricPower_zero m C v
    exact ⟨standardInclusion m 0 hi,d,a,b,fun _ => rfl,ha,he,hpower,hrest,hglobal⟩
  · refine ⟨standardInclusion m i hi, complexFundamentalData i,
      positiveLocalCohomologyClass i, homogeneousPower m C v i,
      fun _ => rfl, positiveLocalCohomologyClass_primitive i,
      positiveLocalCohomologyClass_orientation_evaluation i,
      (of_homogeneousPower m C v i).symm, hpowers i (by omega) hi, ?_⟩
    rw [hpowers i (by omega) hi]
    exact positiveLocalCohomologyClass_global_evaluation i

end P202.ComplexProjectiveRing
end



noncomputable section
namespace P202.ComplexProjectiveRing

/-- A nonzero element of a free rank-one integral module selects a unique
primitive vector on its positive ray. -/
lemma existsUnique_positive_primitive {V : Type*} [AddCommGroup V] [Module ℤ V]
    (e : V ≃ₗ[ℤ] ℤ) (v : V) (hv : v ≠ 0) :
    ∃! g : V, Function.Bijective (fun z : ℤ => z • g) ∧
      ∃ n : ℤ, 0 < n ∧ v = n • g := by
  have he : e v ≠ 0 := by
    intro hz
    exact hv (e.injective (hz.trans e.map_zero.symm))
  have hpm (g : V) (hg : Function.Bijective (fun z : ℤ => z • g)) : e g = 1 ∨ e g = -1 := by
    obtain ⟨z, hz⟩ := hg.surjective (e.symm 1)
    have hz' := congrArg e hz
    simp only [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, Int.cast_id] at hz'
    exact Int.eq_one_or_neg_one_of_mul_eq_one (by simpa only [mul_comm] using hz')
  by_cases hp : 0 < e v
  · refine ⟨e.symm 1, ⟨?_, e v, hp, ?_⟩, ?_⟩
    · constructor
      · intro z w hzw
        have h := congrArg e hzw
        simpa only [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, Int.cast_id] using h
      · intro x
        refine ⟨e x, e.injective ?_⟩
        simp only [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, Int.cast_id]
    · apply e.injective
      simp only [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, Int.cast_id]
    · rintro g ⟨hg,n,hn,hv'⟩
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      have hev := congrArg e hv'
      simp only [map_zsmul, smul_eq_mul, Int.cast_id] at hev
      rcases hpm g hg with h | h
      · exact h
      · rw [h] at hev
        omega
  · have hn : e v < 0 := by omega
    refine ⟨e.symm (-1), ⟨?_, -(e v), by omega, ?_⟩, ?_⟩
    · constructor
      · intro z w hzw
        have h := congrArg e hzw
        simp only [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_neg, mul_one, Int.cast_id] at h
        exact neg_injective h
      · intro x
        refine ⟨-(e x), e.injective ?_⟩
        simp only [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_neg, mul_one,
          neg_neg, Int.cast_id]
    · apply e.injective
      simp only [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_neg, mul_one,
        neg_neg, Int.cast_id]
    · rintro g ⟨hg,n,hn',hv'⟩
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      have hev := congrArg e hv'
      simp only [map_zsmul, smul_eq_mul, Int.cast_id] at hev
      rcases hpm g hg with h | h
      · rw [h] at hev
        omega
      · exact h

end P202.ComplexProjectiveRing
end



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite Set Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
universe u v
namespace P202.ComplexProjectiveRing
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202Specs.MayerVietoris P202.ThomClass

/-- Moving the basepoint along a path fixes the normal variable and therefore
preserves the punctured normal subspace throughout. -/
def secondProductFiberPath {X : TopCat.{u}} (B : Pair.{u}) {x y : X}
    (γ : Path x y) : P202Specs.PrismHomotopy.PairHomotopy
      (secondProductFiberInclusion X B x) (secondProductFiberInclusion X B y) where
  homotopy := {
    toFun := fun tz => (γ tz.1, tz.2)
    continuous_toFun := (γ.continuous.comp continuous_fst).prodMk continuous_snd
    map_zero_left := by intro z; change (γ 0,z) = (x,z); rw [γ.source]
    map_one_left := by intro z; change (γ 1,z) = (y,z); rw [γ.target] }
  preserves := by intro t z; exact z.property

lemma secondProductFiber_pullback_eq {X : TopCat.{u}} (B : Pair.{u}) {x y : X}
    (hxy : Joined x y) (R : Type v) [CommRing R] (q : ℤ) :
    (relativeCohomologyFunctor R R q).map (secondProductFiberInclusion X B x).op =
      (relativeCohomologyFunctor R R q).map (secondProductFiberInclusion X B y).op :=
  ((P202.CohomologyPairs.homotopy_invariant R R).2
    (secondProductFiberPath B hxy.somePath) q)

variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

/-- The original inclusion over a subset of the base. -/
def normalOverInclusion (N : NormalBundle T S i) (U : Set P) :
    normalOverPair N U ⟶ normalPair N :=
  pieceInclusion (normalPair N) (Bundle.TotalSpace.proj ⁻¹' U)

lemma normalOverInclusion_fiber (N : NormalBundle T S i) (U : Set P)
    (p : P) (hp : p ∈ U) :
    fiberToNormalOver N U p hp ≫ normalOverInclusion N U = fiberToNormal N p :=
  PairMap.ext _ _ rfl

variable (R : Type v) [CommRing R]

/-- An actual global normal-bundle class is locally represented by one fixed
model-fiber class. No orientability or generator assumption enters this fact. -/
lemma normalClass_locally_constant (N : NormalBundle T S i) (d : ℕ)
    (c : relativeCohomology R R (normalPair N) (d : ℤ)) (p : P) :
    ∃ (a : P) (U : Set P),
      IsOpen U ∧ p ∈ U ∧
      ∃ hU : U ⊆ (normalBundle N).baseSet a,
        ∃ cModel : relativeCohomology R R (modelPair.{u} (n-m)) (d : ℤ),
          ∀ (q : P) (hq : q ∈ U),
            (relativeCohomologyFunctor R R (d : ℤ)).map
              (fiberCoordinates N a q (hU hq)).op cModel =
            (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N q).op c := by
  letI := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace T.topologicalManifold
  obtain ⟨a, hpa⟩ := (normalBundle N).covers p
  have ha : IsOpen ((normalBundle N).baseSet a) := by
    rw [← (normalBundle N).trivialization_baseSet a]
    exact ((normalBundle N).trivialization a).open_baseSet
  obtain ⟨U, ⟨hUo, hp, hUp⟩, hUa⟩ :=
    (isOpen_isPathConnected_basis p).mem_iff.mp (ha.mem_nhds hpa)
  let F := relativeCohomologyFunctor R R (d : ℤ)
  let cU := F.map (normalOverInclusion N U).op c
  let cProd := F.map (normalChartPairIso N a U hUa).inv.op cU
  let cModel := F.map
    (secondProductFiberInclusion (TopCat.of U) (modelPair.{u} (n-m)) ⟨p,hp⟩).op cProd
  refine ⟨a, U, hUo, hp, hUa, cModel, ?_⟩
  intro q hq
  have hjoined : Joined (⟨p,hp⟩ : U) ⟨q,hq⟩ :=
    (hUp.joinedIn p hp q hq).joined_subtype
  have he := secondProductFiber_pullback_eq (X := TopCat.of U)
    (x := ⟨p,hp⟩) (y := ⟨q,hq⟩) (modelPair.{u} (n-m)) hjoined R (d : ℤ)
  change F.map (fiberCoordinates N a q (hUa hq)).op
    (F.map (secondProductFiberInclusion (TopCat.of U) (modelPair.{u} (n-m)) ⟨p,hp⟩).op
      cProd) = _
  rw [he, normalChart_fiberRestriction]
  change (F.map (normalOverInclusion N U).op ≫
    F.map (fiberToNormalOver N U q hq).op) c = _
  rw [← F.map_comp, ← op_comp, normalOverInclusion_fiber]

/-- An existing global class with primitive fiber restrictions determines an
actual compatible normal orientation, rather than an assumed certificate. -/
def normalOrientationOfClass (N : NormalBundle T S i) (d : ℕ)
    (c : relativeCohomology R R (normalPair N) (d : ℤ))
    (hc : ∀ p : P, Function.Bijective (fun r : R => r •
      ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c))) :
    Orientation R N d where
  generator p := (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c
  generates := hc
  locally_constant := normalClass_locally_constant R N d c

/-- Primitivity of an actual normal-bundle class is constant on some
neighborhood of every base point. -/
lemma normalClass_generates_locally (N : NormalBundle T S i) (d : ℕ)
    (c : relativeCohomology R R (normalPair N) (d : ℤ)) (p : P) :
    ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U,
      Function.Bijective (fun r : R => r •
        ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N q).op c)) ↔
      Function.Bijective (fun r : R => r •
        ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c)) := by
  obtain ⟨a,U,hUo,hp,hUa,cModel,hc⟩ := normalClass_locally_constant R N d c p
  let F := relativeCohomologyFunctor R R (d : ℤ)
  have hgen (q : P) (hq : q ∈ U) :
      Function.Bijective (fun r : R => r • (F.map (fiberToNormal N q).op c)) ↔
        Function.Bijective (fun r : R => r • cModel) := by
    rw [← hc q hq]
    let e := (asIso (F.map (fiberCoordinatesIso N a q (hUa hq)).hom.op)).toLinearEquiv
    change Function.Bijective (fun r : R => r • e cModel) ↔ _
    have he : (fun r : R => r • e cModel) = e ∘ (fun r : R => r • cModel) := by
      funext r
      exact (e.map_smul r cModel).symm
    rw [he]
    exact Function.Bijective.of_comp_iff' e.bijective _
  exact ⟨U,hUo,hp,fun q hq => (hgen q hq).trans (hgen p hp).symm⟩

lemma normalClass_generates_isClopen (N : NormalBundle T S i) (d : ℕ)
    (c : relativeCohomology R R (normalPair N) (d : ℤ)) :
    IsClopen {p : P | Function.Bijective (fun r : R => r •
      ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c))} := by
  have hopen : IsOpen {p : P | Function.Bijective (fun r : R => r •
      ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c))} := by
    apply isOpen_iff_forall_mem_open.mpr
    intro p hp
    obtain ⟨U,hUo,hpU,hconst⟩ := normalClass_generates_locally R N d c p
    exact ⟨U,fun q hq => (hconst q hq).mpr hp,hUo,hpU⟩
  refine ⟨?_,hopen⟩
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro p hp
  obtain ⟨U,hUo,hpU,hconst⟩ := normalClass_generates_locally R N d c p
  exact ⟨U,fun q hq hgen => hp ((hconst q hq).mp hgen),hUo,hpU⟩

/-- On a connected base, a global normal-bundle class that generates one
fiber generates every fiber. This does not assume that the bundle is oriented. -/
lemma normalClass_generates_of_one [PreconnectedSpace P]
    (N : NormalBundle T S i) (d : ℕ)
    (c : relativeCohomology R R (normalPair N) (d : ℤ)) (p : P)
    (hp : Function.Bijective (fun r : R => r •
      ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c))) :
    ∀ q : P, Function.Bijective (fun r : R => r •
      ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N q).op c)) := by
  have he := (normalClass_generates_isClopen R N d c).eq_univ ⟨p,hp⟩
  intro q
  change q ∈ {p : P | Function.Bijective (fun r : R => r •
    ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c))}
  rw [he]
  trivial

/-- A genuine ambient class whose normal restriction is primitive constructs
both an orientation and all of its intrinsic normalized-tube fiber values. -/
lemma ambientClass_hasFiberValues [CompactSpace P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (d : ℕ)
    (K : TubularNeighborhood N) (hK : NormalCompatible N K)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ))
    (hc : ∀ p : P, Function.Bijective (fun r : R => r •
      ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op
        (ambientNormalCohomologyEquiv hi N K R (d : ℤ) c)))) :
    HasFiberValues R
      (normalOrientationOfClass R N d (ambientNormalCohomologyEquiv hi N K R (d : ℤ) c) hc) c := by
  apply hasFiberValues_of_one_normalized R hi N d _ c K hK
  intro p
  exact ambientNormalCohomologyEquiv_restrict hi N K R (d : ℤ) p c

/-- A single primitive normal restriction suffices on a connected compact base. -/
lemma ambientClass_orientation_exists_of_one [CompactSpace P] [PreconnectedSpace P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (d : ℕ)
    (K : TubularNeighborhood N) (hK : NormalCompatible N K)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ)) (p : P)
    (hc : Function.Bijective (fun r : R => r •
      ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op
        (ambientNormalCohomologyEquiv hi N K R (d : ℤ) c)))) :
    ∃ o : Orientation R N d, HasFiberValues R o c := by
  let hgen := normalClass_generates_of_one R N d
    (ambientNormalCohomologyEquiv hi N K R (d : ℤ) c) p hc
  exact ⟨normalOrientationOfClass R N d _ hgen, ambientClass_hasFiberValues R hi N d K hK c hgen⟩

/-- When the base consists of one point, its full normal bundle is its
literal fiber, with the original subspace topologies and zero sections. -/
def fiberToNormalIso [Subsingleton P] (N : NormalBundle T S i) (p : P) :
    fiberPair N p ≅ normalPair N where
  hom := fiberToNormal N p
  inv := {
    map := TopCat.ofHom ⟨fun z => ⟨z, Subsingleton.elim z.proj p⟩,
      continuous_id.subtype_mk _⟩
    mapsTo := by
      intro z hz he
      apply hz
      exact (congrArg Subtype.val he).trans
        (congrArg (normalZero N) (Subsingleton.elim p z.proj)) }
  hom_inv_id := PairMap.ext _ _ rfl
  inv_hom_id := PairMap.ext _ _ rfl

lemma linearEquiv_generator_iff {V W : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (e : V ≃ₗ[R] W) (c : V) :
    Function.Bijective (fun r : R => r • e c) ↔
      Function.Bijective (fun r : R => r • c) := by
  have he : (fun r : R => r • e c) = e ∘ (fun r : R => r • c) := by
    funext r
    exact (e.map_smul r c).symm
  rw [he]
  exact Function.Bijective.of_comp_iff' e.bijective _

/-- Over a one-point base, any primitive global ambient relative class
constructs a compatible normal orientation and every normalized fiber value. -/
lemma ambientClass_orientation_exists_subsingleton [CompactSpace P] [Subsingleton P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (d : ℕ)
    (K : TubularNeighborhood N) (hK : NormalCompatible N K)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ))
    (hc : Function.Bijective (fun r : R => r • c)) :
    ∃ o : Orientation R N d, HasFiberValues R o c := by
  let e := ambientNormalCohomologyEquiv hi N K R (d : ℤ)
  have hgen : ∀ p : P, Function.Bijective (fun r : R => r •
      ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op (e c))) := by
    intro p
    let eFiber := (asIso ((relativeCohomologyFunctor R R (d : ℤ)).map
      (fiberToNormalIso N p).hom.op)).toLinearEquiv
    exact (linearEquiv_generator_iff R eFiber (e c)).mpr
      ((linearEquiv_generator_iff R e c).mpr hc)
  exact ⟨normalOrientationOfClass R N d (e c) hgen,
    ambientClass_hasFiberValues R hi N d K hK c hgen⟩

end P202.ComplexProjectiveRing
end



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct
universe u w
namespace P202.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
  P202Specs.CupProduct P202Specs.RelativeCupProduct P202Specs.TransverseThomProduct

variable (R : Type u) [CommRing R]

lemma relativeForget_pullback {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ)
    (a : HR R Q n) :
    forget R P n (relativePullback R f n a) =
      hPullback R f.map n (forget R Q n a) := by
  have h := congrArg (fun (g : relativeCochains R R Q ⟶ ordinaryCochains R R P.space) =>
    HomologicalComplex.homologyMap g (n : ℤ)) (cochainSequenceMap R R f).comm₁₂
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun g => g.hom a) h

/-- The homogeneous ordinary image of an actual class with closed support. -/
def supportedOrdinary {X : TopCat.{w}} (a : SupportedClass R X) : HStar R X :=
  DirectSum.of (H R X) a.degree (forget R (⟨X, a.supportᶜ⟩ : Pair) a.degree a.value)

lemma relativeForget_heq_subspace {X : TopCat.{w}} {A B : Set X} (hs : A = B)
    (n : ℕ) (a : HR R (⟨X,A⟩ : Pair) n) (b : HR R (⟨X,B⟩ : Pair) n)
    (hv : HEq a b) : forget R (⟨X,A⟩ : Pair) n a = forget R (⟨X,B⟩ : Pair) n b := by
  cases hs
  exact congrArg (forget R (⟨X,A⟩ : Pair) n) (eq_of_heq hv)

lemma supportedOrdinary_cup {X : TopCat.{w}} (C : CohomologyRing R X)
    (μ : NaturalRelativeCupProduct R) (a b : SupportedClass R X) :
    letI := C.gradedRing
    supportedOrdinary R (supportedCup R μ a b) =
      supportedOrdinary R a * supportedOrdinary R b := by
  letI := C.gradedRing
  let P : TwoSubspaces := ⟨X,a.supportᶜ,b.supportᶜ⟩
  let hP : P.IsOpen := ⟨a.closed.isOpen_compl,b.closed.isOpen_compl⟩
  have hv : HEq (supportedCup R μ a b).value
      (μ.product P hP a.degree b.degree (a.value ⊗ₜ[R] b.value)) := by
    unfold supportedCup
    dsimp only
    exact cast_heq _ _
  have h := relativeForget_heq_subspace R (Set.compl_inter a.support b.support)
    (a.degree+b.degree) (supportedCup R μ a b).value
    (μ.product P hP a.degree b.degree (a.value ⊗ₜ[R] b.value)) hv
  change DirectSum.of (H R X) (a.degree+b.degree)
    (forget R (⟨X,(a.support ∩ b.support)ᶜ⟩ : Pair) (a.degree+b.degree)
      (supportedCup R μ a b).value) = _
  rw [h, μ.absolute P hP _ _ _ _ C]
  unfold supportedOrdinary
  rw [DirectSum.of_mul_of, C.product_eq]

/-- Equal ordinary images of each factor identify a nonempty ordered relative
product with the corresponding ordinary power, without any geometry assumed. -/
lemma supportedOrdinary_orderedCup_eq_pow {X : TopCat.{w}} (C : CohomologyRing R X)
    (μ : NaturalRelativeCupProduct R) (k : ℕ)
    (F : Fin (k+1) → SupportedClass R X) (v : HStar R X)
    (hF : ∀ j, supportedOrdinary R (F j) = v) :
    letI := C.gradedRing
    supportedOrdinary R (orderedCup R μ k F) = v^(k+1) := by
  letI := C.gradedRing
  induction k with
  | zero => simpa only [orderedCup, zero_add, pow_one] using hF 0
  | succ k ih =>
    change supportedOrdinary R (supportedCup R μ (F 0)
      (orderedCup R μ k (fun j => F j.succ))) = _
    rw [supportedOrdinary_cup R C, hF 0, ih (fun j => F j.succ) (fun j => hF j.succ),
      ← pow_succ']

/-- Casting the output degree of a supported product does not change its
homogeneous ordinary image in the direct sum. -/
lemma supportedOrdinary_castDegree {X : TopCat.{w}} (a : SupportedClass R X)
    {n : ℕ} (hd : a.degree = n) :
    DirectSum.of (H R X) n
      (forget R (⟨X, a.supportᶜ⟩ : Pair) n (castRelativeDegree R hd a.value)) = supportedOrdinary R a := by
  cases hd
  rfl

/-- Degree bookkeeping can be kept separate from the product calculation.
After its output is cast to a chosen degree, the ordinary class of the actual
ordered relative product is exactly the corresponding ordinary power. -/
lemma orderedCup_ordinary_power {X : TopCat.{w}} (C : CohomologyRing R X)
    (μ : NaturalRelativeCupProduct R) (k : ℕ)
    (F : Fin (k+1) → SupportedClass R X) (v : HStar R X)
    (hF : ∀ j, supportedOrdinary R (F j) = v)
    {n : ℕ} (hd : (orderedCup R μ k F).degree = n) :
    letI := C.gradedRing
    v^(k+1) = DirectSum.of (H R X) n
      (forget R (⟨X, (orderedCup R μ k F).supportᶜ⟩ : Pair) n (castRelativeDegree R hd (orderedCup R μ k F).value)) := by
  letI := C.gradedRing
  rw [supportedOrdinary_castDegree, supportedOrdinary_orderedCup_eq_pow R C μ k F v hF]

lemma orderedCup_degree_eq_mul {X : TopCat.{w}} (μ : NaturalRelativeCupProduct R)
    (k d : ℕ) (F : Fin (k+1) → SupportedClass R X)
    (hd : ∀ j, (F j).degree = d) : (orderedCup R μ k F).degree = d*(k+1) := by
  induction k with
  | zero => simpa only [orderedCup, zero_add, mul_one] using hd 0
  | succ k ih =>
    change (F 0).degree + (orderedCup R μ k (fun j => F j.succ)).degree = _
    rw [hd 0, ih (fun j => F j.succ) (fun j => hd j.succ)]
    exact (Nat.add_comm _ _).trans (Nat.mul_succ d (k+1)).symm

end P202.ComplexProjectiveRing
end



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Set Topology
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs

/-- The complement of the actual last-coordinate hyperplane is its affine chart. -/
def hyperplaneComplementHomeomorph (m : ℕ) :
    (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)).sub ≃ₜ (Fin (m+1) → ℂ) := by
  let e := topAffineChart (m+1)
  have hs : (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)).subspace = e.source := by
    rw [topAffineChart_source]
    change (Set.range (hyperplaneInclusion m))ᶜ = (lowerSpace (m+1) (m+1))ᶜ
    congr 1
    exact inclusion_range (m+1) m (by omega)
  exact (Homeomorph.setCongr hs).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (topAffineChart_target (m+1))).trans (Homeomorph.Set.univ _)))

lemma hyperplaneComplement_contractible (m : ℕ) :
    ContractibleSpace (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)).sub :=
  (hyperplaneComplementHomeomorph m).contractibleSpace

/-- Positive-degree ordinary homology vanishes on a contractible space. -/
lemma contractible_ordinaryHomology_isZero (X : TopCat) [Nonempty X] [ContractibleSpace X]
    (n : ℤ) (hn : n ≠ 0) : IsZero (homology ℤ ℤ X n) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let p : X ⟶ P202Specs.SingularDegreeZero.point :=
    TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let q : P202Specs.SingularDegreeZero.point ⟶ X :=
    TopCat.ofHom (ContinuousMap.const _ x)
  have hpq : TopCat.Homotopy (p ≫ q) (𝟙 X) :=
    Classical.choice (homotopic_of_contractible_target _ _)
  have hqp : TopCat.Homotopy (q ≫ p) (𝟙 _) := ContinuousMap.Homotopy.refl _
  haveI := (P202.PrismHomotopy.homologyIso ℤ ℤ p q hpq hqp n).1
  exact (asIso ((homologyFunctor ℤ ℤ n).map p)).isZero_iff.mpr
    (P202.SingularDegreeZero.pointOrdinaryOther ℤ ℤ n hn)

lemma hyperplaneComplement_homology_isZero (m : ℕ) (n : ℤ) (hn : n ≠ 0) :
    IsZero (homology ℤ ℤ (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)).sub n) := by
  haveI := hyperplaneComplement_contractible m
  haveI : Nonempty (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)).sub :=
    ⟨(hyperplaneComplementHomeomorph m).symm 0⟩
  exact contractible_ordinaryHomology_isZero _ n hn

lemma hyperplane_absoluteToRelative_isIso (m : ℕ) (n : ℕ) (hn : 2 ≤ n) :
    IsIso (HomologicalComplex.homologyMap
      (projection (ordinaryFunctor ℤ ℤ)
        (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m))) (n : ℤ)) := by
  let P := P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)
  let hS := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.ordinary_short_exact ℤ ℤ P)
  have hz := hyperplaneComplement_homology_isZero m (n : ℤ) (by omega)
  have hz' := hyperplaneComplement_homology_isZero m ((n : ℤ)-1) (by omega)
  haveI : Mono (HomologicalComplex.homologyMap (projection (ordinaryFunctor ℤ ℤ) P) (n : ℤ)) :=
    (hS.homology_exact₂ _).mono_g (hz.eq_of_src _ _)
  haveI : Epi (HomologicalComplex.homologyMap (projection (ordinaryFunctor ℤ ℤ) P) (n : ℤ)) :=
    (hS.homology_exact₃ (n : ℤ) ((n : ℤ)-1) (by simp)).epi_f (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

lemma contractible_ordinaryCohomology_isZero (X : TopCat.{0}) [Nonempty X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : IsZero (ordinaryCohomology ℤ ℤ X (n : ℤ)) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let p : X ⟶ projectiveSpace 0 := TopCat.ofHom (ContinuousMap.const _ (projectiveOrigin 0))
  let q : projectiveSpace 0 ⟶ X := TopCat.ofHom (ContinuousMap.const _ x)
  have hpq : TopCat.Homotopy (p ≫ q) (𝟙 X) :=
    Classical.choice (homotopic_of_contractible_target _ _)
  have hqp : TopCat.Homotopy (q ≫ p) (𝟙 _) := by
    have he : q ≫ p = 𝟙 _ := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro y
      exact Subsingleton.elim _ _
    rw [he]
    exact ContinuousMap.Homotopy.refl _
  let F := ordinaryCohomologyFunctor ℤ ℤ (n : ℤ)
  have h₁ := (P202.CohomologyPairs.homotopy_invariant ℤ ℤ).1 hpq (n : ℤ)
  have h₂ := (P202.CohomologyPairs.homotopy_invariant ℤ ℤ).1 hqp (n : ℤ)
  change F.map (p ≫ q).op = F.map (𝟙 X).op at h₁
  change F.map (q ≫ p).op = F.map (𝟙 (projectiveSpace 0)).op at h₂
  rw [op_comp, F.map_comp, op_id, F.map_id] at h₁ h₂
  haveI : IsIso (F.map p.op) := ⟨⟨F.map q.op, h₂, h₁⟩⟩
  exact (asIso (F.map p.op)).isZero_iff.mp
    ((cohomology_groups 0 n).2 (by rintro ⟨r,hr,he⟩; exact hn (by omega)))

lemma hyperplaneComplement_cohomology_isZero (m : ℕ) (n : ℕ) (hn : n ≠ 0) :
    IsZero (ordinaryCohomology ℤ ℤ
      (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)).sub (n : ℤ)) := by
  haveI := hyperplaneComplement_contractible m
  haveI : Nonempty (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)).sub :=
    ⟨(hyperplaneComplementHomeomorph m).symm 0⟩
  exact contractible_ordinaryCohomology_isZero _ n hn

lemma hyperplane_ordinaryImage_isIso (m : ℕ) (n : ℕ) (hn : 2 ≤ n) :
    IsIso (HomologicalComplex.homologyMap
      (relativeToAbsolute ℤ ℤ
        (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m))) (n : ℤ)) := by
  let P := P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)
  let hS := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.CohomologyPairs.short_exact ℤ ℤ P)
  have hz := hyperplaneComplement_cohomology_isZero m n (by omega)
  have hz' : IsZero (ordinaryCohomology ℤ ℤ P.sub ((n : ℤ)-1)) := by
    have he : ((n : ℤ)-1) = ((n-1 : ℕ) : ℤ) := by omega
    rw [he]
    exact hyperplaneComplement_cohomology_isZero m (n-1) (by omega)
  haveI : Mono (HomologicalComplex.homologyMap (relativeToAbsolute ℤ ℤ P) (n : ℤ)) :=
    (hS.homology_exact₁ ((n : ℤ)-1) (n : ℤ) (by simp)).mono_g (hz'.eq_of_src _ _)
  haveI : Epi (HomologicalComplex.homologyMap (relativeToAbsolute ℤ ℤ P) (n : ℤ)) :=
    (hS.homology_exact₂ _).epi_f (hz.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

lemma hyperplane_ordinaryImage_bijective (m : ℕ) (n : ℕ) (hn : 2 ≤ n) :
    Function.Bijective (ordinaryImage
      (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)) n) := by
  haveI := hyperplane_ordinaryImage_isIso m n hn
  exact (asIso (HomologicalComplex.homologyMap
    (relativeToAbsolute ℤ ℤ
      (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m))) (n : ℤ))).toLinearEquiv.bijective

end P202.ComplexProjectiveRing
end


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs

/-- The projective transverse line uses homogeneous coordinates [v₁:0:…:0:v₀]. -/
def normalLineLinear (m : ℕ) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin (m+2) → ℂ) where
  toFun v j := if j.val = 0 then v 1 else if j.val = m+1 then v 0 else 0
  map_add' v w := by ext j; dsimp; split_ifs <;> simp_all
  map_smul' a v := by ext j; dsimp; split_ifs <;> simp_all

lemma normalLineLinear_injective (m : ℕ) : Function.Injective (normalLineLinear m) := by
  intro v w he
  have h0 := congrFun he (0 : Fin (m+2))
  have h1 := congrFun he (Fin.last (m+1))
  simp only [normalLineLinear, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_zero,
    Fin.val_last, if_pos rfl] at h0 h1
  have hlast : ¬ m+1 = 0 := by omega
  simp only [hlast, if_false] at h1
  ext j
  fin_cases j
  · exact h1
  · exact h0

def normalProjectiveLine (m : ℕ) : projectiveSpace 1 ⟶ projectiveSpace (m+1) :=
  TopCat.ofHom ⟨projectiveLinearMap (normalLineLinear m) (normalLineLinear_injective m),
    projectiveLinearMap_continuous (normalLineLinear m) (normalLineLinear_injective m)⟩

lemma normalProjectiveLine_preimage_hyperplane (m : ℕ) (p : Space 1) :
    normalProjectiveLine m p ∈ Set.range (hyperplaneInclusion m) ↔ p = projectiveOrigin 1 := by
  induction p using Projectivization.ind with | h v hv =>
  change mk (normalLineLinear m v) _ ∈ Set.range (hyperplaneInclusion m) ↔
    mk v hv = projectiveOrigin (0+1)
  rw [show Set.range (hyperplaneInclusion m) = coordinateHyperplane (m+1) (Fin.last (m+1)) from
    (lastCoordinateHyperplane_range m).symm, coordinateHyperplane_mk,
    mk_eq_origin_iff_firstCoordinates 0 v hv]
  have he : (normalLineLinear m v) (Fin.last (m+1)) = v 0 := by
    simp [normalLineLinear, show m+1 ≠ 0 by omega]
  rw [he]
  constructor
  · intro hz
    ext j
    have hj : j = 0 := by apply Fin.ext; omega
    simpa [firstCoordinates, hj] using hz
  · intro hz
    simpa [firstCoordinates] using congrFun hz 0

def normalProjectiveLinePair (m : ℕ) : localPair (Space 1) (projectiveOrigin 1) ⟶
    P202Specs.ThomClass.ambientPair (hyperplaneInclusion m) where
  map := normalProjectiveLine m
  mapsTo := fun p hp h => hp ((normalProjectiveLine_preimage_hyperplane m p).mp h)

lemma normalProjectiveLine_positiveSimplex (m : ℕ) (x : P202.Cellular.StandardSimplex 2) :
    normalProjectiveLine m (positiveProjectiveSimplex 1 x) = positiveNormalSimplex m x := by
  change mk (normalLineLinear m (coordinateVector 1 1 (complexSimplexCoordinates 1 x) 1)) _ =
    mk (complexNormalVector m (complexSimplexCoordinates 1 x 0)) _
  congr 1

lemma positiveHyperplaneSlice_factor (m : ℕ) :
    positiveHyperplaneSlice m = positiveLocalSimplex 1 ≫ normalProjectiveLinePair m := by
  apply PairMap.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  exact fun x => (normalProjectiveLine_positiveSimplex m x).symm

lemma normalProjectiveLine_factor (m : ℕ) :
    normalProjectiveLine m =
      (TopCat.isoOfHomeo (coordinatePermutation 1 (Equiv.swap 0 1))).hom ≫
      standardInclusion (m+1) 1 (by omega) ≫
      (TopCat.isoOfHomeo (coordinatePermutation (m+1) (Equiv.swap 1 (Fin.last (m+1))))).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  induction p using Projectivization.ind with | h v hv =>
  change mk (normalLineLinear m v) _ = mk
    ((LinearEquiv.funCongrLeft ℂ ℂ (Equiv.swap 1 (Fin.last (m+1))))
      (inclusionVector (m+1) 1 (by omega)
        ((LinearEquiv.funCongrLeft ℂ ℂ (Equiv.swap (0 : Fin 2) 1)) v))) _
  congr 1
  ext j
  simp only [LinearEquiv.funCongrLeft_apply, Equiv.coe_fn_mk]
  by_cases hj0 : j = 0
  · subst j
    have h0 : (0 : Fin (m+2)) ≠ 1 := by intro h; have hh := congrArg Fin.val h; simp at hh
    have hl0 : (0 : Fin (m+2)) ≠ Fin.last (m+1) := by intro h; have := congrArg Fin.val h; simp at this
    simp [normalLineLinear, inclusionVector, Equiv.swap_apply_of_ne_of_ne h0 hl0]
  · by_cases hjl : j = Fin.last (m+1)
    · subst j
      simp [normalLineLinear, inclusionVector, show m+1 ≠ 0 by omega]
    · by_cases hj1 : j = 1
      · subst j
        have hl1 : (1 : Fin (m+2)) ≠ Fin.last (m+1) := hjl
        have hm0 : m ≠ 0 := by
          intro hm0
          subst m
          exact hjl rfl
        have hm : 1 < m+1 := by omega
        simp [normalLineLinear, inclusionVector, hm0]
      · have hv0 : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hj0
        have hvl : j.val ≠ m+1 := by simpa only [Fin.ext_iff, Fin.val_last] using hjl
        have hv1 : j.val ≠ 1 := by simpa only [Fin.ext_iff, Fin.val_one] using hj1
        simp [normalLineLinear, inclusionVector, hj0, hvl,
          Equiv.swap_apply_of_ne_of_ne hj1 hjl, show ¬ j.val ≤ 1 by omega]

lemma normalProjectiveLine_homology_isIso (m : ℕ) :
    IsIso ((homologyFunctor ℤ ℤ 2).map (normalProjectiveLine m)) := by
  haveI := inclusion_homology_isIso (m+1) 1 (by omega) 2 (by omega)
  rw [normalProjectiveLine_factor, Functor.map_comp, Functor.map_comp]
  infer_instance

lemma normalProjectiveLinePair_homology_isIso (m : ℕ) :
    IsIso ((relativeHomologyFunctor ℤ ℤ 2).map (normalProjectiveLinePair m)) := by
  let P := localPair (Space 1) (projectiveOrigin 1)
  let Q := P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)
  haveI : IsIso (HomologicalComplex.homologyMap
      (projection (ordinaryFunctor ℤ ℤ) P) 2) := origin_absoluteToLocal_isIso 0
  haveI : IsIso (HomologicalComplex.homologyMap
      (projection (ordinaryFunctor ℤ ℤ) Q) 2) :=
    hyperplane_absoluteToRelative_isIso m 2 (by omega)
  haveI : IsIso (HomologicalComplex.homologyMap
      ((ordinaryFunctor ℤ ℤ).map (normalProjectiveLinePair m).map) 2) :=
    normalProjectiveLine_homology_isIso m
  have h := congrArg (fun f => HomologicalComplex.homologyMap f 2)
    (projection_map (ordinaryFunctor ℤ ℤ) (normalProjectiveLinePair m))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  haveI : IsIso (HomologicalComplex.homologyMap
      ((ordinaryFunctor ℤ ℤ).map (normalProjectiveLinePair m).map) 2 ≫
      HomologicalComplex.homologyMap (projection (ordinaryFunctor ℤ ℤ) Q) 2) := by
    infer_instance
  exact IsIso.of_isIso_fac_left h

lemma positiveHyperplaneSlice_homology_isIso (m : ℕ) :
    IsIso ((relativeHomologyFunctor ℤ ℤ 2).map (positiveHyperplaneSlice m)) := by
  haveI := positiveLocalSimplex_isIso 1 2
  haveI := normalProjectiveLinePair_homology_isIso m
  rw [positiveHyperplaneSlice_factor, Functor.map_comp]
  infer_instance

end P202.ComplexProjectiveRing
end


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs

/-- The class of the explicitly ordered complex transverse simplex. -/
def positiveHyperplaneClass (m : ℕ) :
    relativeHomology ℤ ℤ (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)) 2 :=
  ((relativeHomologyFunctor ℤ ℤ 2).map (positiveHyperplaneSlice m))
    (P202.SpheresDisks.affineClassLinear ℤ ℤ 2 1)

lemma positiveHyperplaneClass_isGenerator (m : ℕ) :
    IsGenerator ℤ (positiveHyperplaneClass m) := by
  haveI := positiveHyperplaneSlice_homology_isIso m
  let e := (asIso ((relativeHomologyFunctor ℤ ℤ 2).map (positiveHyperplaneSlice m))).toLinearEquiv
  let s := LinearEquiv.ofBijective (P202.SpheresDisks.affineClassLinear ℤ ℤ 2)
    (P202.SpheresDisks.SimplexOrientation.affineClassLinear_ring_bijective ℤ 2)
  exact (P202.LocalOrientation.generator_map_iff ℤ e (s 1)).mpr
    ((P202.LocalOrientation.generator_map_iff ℤ s (1 : ℤ)).mpr
      (P202.LocalOrientation.generator_one ℤ))

lemma exists_normalizedHyperplaneClass (m : ℕ) :
    ∃ a : relativeCohomology ℤ ℤ (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)) 2,
      IsGenerator ℤ a ∧ relativeEvaluation _ 2 a (positiveHyperplaneClass m) = 1 := by
  let P := P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)
  let b := positiveHyperplaneClass m
  let h := P202.LocalOrientation.generatorEquiv ℤ b (positiveHyperplaneClass_isGenerator m)
  obtain ⟨α, σ, hα, hexact, hsurj, hσ⟩ :=
    (P202.UniversalCoefficientsCohomology.all_degrees ℤ ℤ).2 P 2
  obtain ⟨a, ha⟩ := hsurj h.symm.toLinearMap
  have heval : relativeEvaluation P 2 a b = 1 := by
    rw [ha]
    change h.symm b = 1
    apply h.injective
    rw [LinearEquiv.apply_symm_apply]
    simp [h, P202.LocalOrientation.generatorEquiv_apply]
  haveI := hyperplane_ordinaryImage_isIso m 2 (by omega)
  obtain ⟨eabs⟩ := (cohomology_groups (m+1) 2).1 ⟨1,by omega,by omega⟩
  let e : relativeCohomology ℤ ℤ P 2 ≃ₗ[ℤ] ℤ :=
    (asIso (HomologicalComplex.homologyMap (relativeToAbsolute ℤ ℤ P) 2)).toLinearEquiv.trans eabs
  refine ⟨a,?_,heval⟩
  have hg := generates_of_pairing_one e.toAddEquiv a
    (((LinearMap.applyₗ (R := ℤ) b).comp (relativeEvaluation P 2)).toAddMonoidHom) heval
  change Function.Bijective _
  convert hg using 1
  funext r
  exact Int.cast_smul_eq_zsmul (R := ℤ) r a

/-- A genuine relative generator normalized by evaluation on the positive
complex transverse line. Its fiberwise Thom property is a separate obligation. -/
def normalizedHyperplaneClass (m : ℕ) :
    relativeCohomology ℤ ℤ (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)) 2 :=
  Classical.choose (exists_normalizedHyperplaneClass m)

lemma normalizedHyperplaneClass_isGenerator (m : ℕ) :
    IsGenerator ℤ (normalizedHyperplaneClass m) :=
  (Classical.choose_spec (exists_normalizedHyperplaneClass m)).1

lemma normalizedHyperplaneClass_evaluation (m : ℕ) :
    relativeEvaluation _ 2 (normalizedHyperplaneClass m) (positiveHyperplaneClass m) = 1 :=
  (Classical.choose_spec (exists_normalizedHyperplaneClass m)).2

lemma normalizedHyperplaneClass_positiveSlice_evaluation (m : ℕ) :
    relativeEvaluation _ 2 (normalizedHyperplaneClass m)
      (((relativeHomologyFunctor ℤ ℤ 2).map (positiveHyperplaneSlice m))
        (P202Specs.SpheresDisks.classOf ℤ _ 2
          (P202Specs.SpheresDisks.relativeAffineChain ℤ ℤ 2 1) (positiveSimplex_cycle 2))) = 1 := by
  have he := congrArg
    (fun z : relativeHomology ℤ ℤ (P202Specs.SpheresDisks.simplexPair 2) 2 =>
      relativeEvaluation _ 2 (normalizedHyperplaneClass m)
        (((relativeHomologyFunctor ℤ ℤ 2).map (positiveHyperplaneSlice m)) z))
    (P202.SpheresDisks.affineClassLinear_apply ℤ ℤ 2 1)
  exact he.symm.trans (normalizedHyperplaneClass_evaluation m)

end P202.ComplexProjectiveRing
end



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Set Topology
namespace P202.ComplexProjectiveRing
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
  P202Specs.RelativeCupProduct P202Specs.PrismHomotopy

/-- Complex coordinate space with the complement of its jth zero hyperplane. -/
abbrev complexCoordinatePair (m : ℕ) (j : Fin m) : Pair :=
  ⟨TopCat.of (Fin m → ℂ), {z | z j ≠ 0}⟩

/-- The complex line, relative to its punctured complement. -/
abbrev complexLinePair : Pair := ⟨TopCat.of ℂ, {z | z ≠ 0}⟩

/-- Projection to the jth complex coordinate, as an actual map of pairs. -/
def complexCoordinateProjection (m : ℕ) (j : Fin m) :
    complexCoordinatePair m j ⟶ complexLinePair where
  map := TopCat.ofHom ⟨fun z => z j, continuous_apply j⟩
  mapsTo := fun _ h => h

/-- Include the complex j-axis, preserving precisely the punctured subspaces. -/
def complexCoordinateSection (m : ℕ) (j : Fin m) :
    complexLinePair ⟶ complexCoordinatePair m j where
  map := TopCat.ofHom ⟨fun w i => if i = j then w else 0,
    continuous_pi (fun i => by split_ifs <;> fun_prop)⟩
  mapsTo := by
    intro w hw
    change (if j = j then w else 0) ≠ 0
    simpa using (show w ≠ 0 from hw)

lemma complexCoordinate_section_projection (m : ℕ) (j : Fin m) :
    complexCoordinateSection m j ≫ complexCoordinateProjection m j = 𝟙 complexLinePair := by
  apply PairMap.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro w
  change (if j = j then w else 0) = w
  simp

/-- Scale all transverse chart coordinates to zero, keeping the selected
complex coordinate fixed throughout, including on its punctured subspace. -/
def complexCoordinateRetractionHomotopy (m : ℕ) (j : Fin m) :
    PairHomotopy (complexCoordinateProjection m j ≫ complexCoordinateSection m j)
      (𝟙 (complexCoordinatePair m j)) where
  homotopy := {
    toFun := fun p i => if i = j then p.2 i else (p.1.val : ℂ) * p.2 i
    continuous_toFun := continuous_pi (fun i => by split_ifs <;> fun_prop)
    map_zero_left := by
      intro z
      change (fun i : Fin m => if i = j then z i else (0 : ℂ) * z i) =
        (fun i => if i = j then z j else 0)
      funext i
      by_cases h : i = j <;> simp [h]
    map_one_left := by
      intro z
      change (fun i : Fin m => if i = j then z i else (1 : ℂ) * z i) = z
      funext i
      by_cases h : i = j <;> simp [h]
  }
  preserves := by
    intro t z
    change (if j = j then z.val j else (t.val : ℂ) * z.val j) ≠ 0
    simpa using (show z.val j ≠ 0 from z.property)

/-- Every relative chart class is the pullback of its complex-axis restriction.
This is equality in the original cohomology group, by an actual pair homotopy. -/
lemma complexCoordinate_class_projection (m : ℕ) (j : Fin m)
    (n : ℕ) (a : HR ℤ (complexCoordinatePair m j) n) :
    relativePullback ℤ (complexCoordinateProjection m j) n
      (relativePullback ℤ (complexCoordinateSection m j) n a) = a := by
  have h := (P202.CohomologyPairs.homotopy_invariant ℤ ℤ).2
    (complexCoordinateRetractionHomotopy m j) (n : ℤ)
  rw [op_comp, Functor.map_comp, op_id, CategoryTheory.Functor.map_id] at h
  exact congrArg (fun g => g.hom a) h

/-- Restriction to the complex coordinate line is a genuine cohomology
isomorphism in every degree, with inverse the actual coordinate projection. -/
lemma complexCoordinate_section_cohomology_bijective (m : ℕ) (j : Fin m) (n : ℕ) :
    Function.Bijective (relativePullback ℤ (complexCoordinateSection m j) n) := by
  constructor
  · intro a b h
    have h' := congrArg (relativePullback ℤ (complexCoordinateProjection m j) n) h
    simpa only [complexCoordinate_class_projection] using h'
  · intro a
    refine ⟨relativePullback ℤ (complexCoordinateProjection m j) n a, ?_⟩
    have h := congrArg (fun f =>
      (relativeCohomologyFunctor ℤ ℤ (n : ℤ)).map f.op)
      (complexCoordinate_section_projection m j)
    rw [op_comp, Functor.map_comp, op_id, CategoryTheory.Functor.map_id] at h
    exact congrArg (fun g => g.hom a) h


open P202.ComplexProjective P202Specs.ComplexProjectiveRing

/-- The last affine chart as a map of the exact hyperplane-complement pairs. -/
def complexAffineCoordinatePair (m : ℕ) (j : Fin m) :
    complexCoordinatePair m j ⟶ coordinateHyperplanePair m j.castSucc where
  map := TopCat.ofHom ⟨affineChart m m le_rfl, affineChart_continuous m m le_rfl⟩
  mapsTo := by
    intro z hz
    change affineChart m m le_rfl z ∉ coordinateHyperplane m j.castSucc
    intro h
    exact hz ((coordinateHyperplane_topAffineChart m j z).mp h)

/-- The complex j-axis mapped into the last projective affine chart. -/
def complexProjectiveCoordinateLine (m : ℕ) (j : Fin m) :
    complexLinePair ⟶ coordinateHyperplanePair m j.castSucc :=
  complexCoordinateSection m j ≫ complexAffineCoordinatePair m j

lemma complexProjectiveCoordinateLine_formula (m : ℕ) (j : Fin m) (w : ℂ) :
    (complexProjectiveCoordinateLine m j).map w =
      affineChart m m le_rfl (fun i => if i = j then w else 0) := rfl

/-- In affine normal coordinates, every actual hyperplane-relative class is
exactly the coordinate projection pullback of its complex transverse-line
restriction. The equality follows from the explicit pair deformation above. -/
lemma complexAffineCoordinate_class_projection (m : ℕ) (j : Fin m)
    (n : ℕ) (a : HR ℤ (coordinateHyperplanePair m j.castSucc) n) :
    relativePullback ℤ (complexAffineCoordinatePair m j) n a =
      relativePullback ℤ (complexCoordinateProjection m j) n
        (relativePullback ℤ (complexProjectiveCoordinateLine m j) n a) := by
  have h := complexCoordinate_class_projection m j n
    (relativePullback ℤ (complexAffineCoordinatePair m j) n a)
  have he : relativePullback ℤ (complexCoordinateSection m j) n
      (relativePullback ℤ (complexAffineCoordinatePair m j) n a) =
      relativePullback ℤ (complexProjectiveCoordinateLine m j) n a := by
    change ((relativeCohomologyFunctor ℤ ℤ (n : ℤ)).map
      (complexCoordinateSection m j).op).hom
        (((relativeCohomologyFunctor ℤ ℤ (n : ℤ)).map
          (complexAffineCoordinatePair m j).op).hom a) =
      ((relativeCohomologyFunctor ℤ ℤ (n : ℤ)).map
        (complexCoordinateSection m j ≫ complexAffineCoordinatePair m j).op).hom a
    rw [op_comp, Functor.map_comp]
    rfl
  rw [he] at h
  exact h.symm

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs P202Specs.CupProduct

lemma normalProjectiveLinePair_positiveLocalClass (m : ℕ) :
    ((relativeHomologyFunctor ℤ ℤ 2).map (normalProjectiveLinePair m)) (positiveLocalClass 1) =
      positiveHyperplaneClass m := by
  unfold positiveLocalClass positiveHyperplaneClass
  rw [positiveHyperplaneSlice_factor, Functor.map_comp]
  rfl

lemma normalizedHyperplaneClass_normalLine_pullback (m : ℕ) :
    ((relativeCohomologyFunctor ℤ ℤ 2).map (normalProjectiveLinePair m).op)
      (normalizedHyperplaneClass m) = positiveLocalCohomologyClass 1 := by
  apply (positiveLocalCohomologyEquiv 1).injective
  calc
    positiveLocalCohomologyEquiv 1
        (((relativeCohomologyFunctor ℤ ℤ 2).map (normalProjectiveLinePair m).op)
          (normalizedHyperplaneClass m)) =
        relativeEvaluation (localPair (Space 1) (projectiveOrigin 1)) 2
          (((relativeCohomologyFunctor ℤ ℤ 2).map (normalProjectiveLinePair m).op)
            (normalizedHyperplaneClass m)) (positiveLocalClass 1) :=
      positiveLocalCohomologyEquiv_apply 1 _
    _ = relativeEvaluation _ 2 (normalizedHyperplaneClass m)
          (((relativeHomologyFunctor ℤ ℤ 2).map (normalProjectiveLinePair m)) (positiveLocalClass 1)) :=
      relativeEvaluation_pullback (normalProjectiveLinePair m) 2 _ _
    _ = relativeEvaluation _ 2 (normalizedHyperplaneClass m) (positiveHyperplaneClass m) :=
      congrArg (relativeEvaluation _ 2 (normalizedHyperplaneClass m))
        (normalProjectiveLinePair_positiveLocalClass m)
    _ = 1 := normalizedHyperplaneClass_evaluation m
    _ = positiveLocalCohomologyEquiv 1 (positiveLocalCohomologyClass 1) :=
      ((positiveLocalCohomologyEquiv_apply 1 _).trans
        (positiveLocalCohomologyClass_evaluation 1)).symm

lemma normalProjectiveLine_zero_eq_swap :
    normalProjectiveLine 0 =
      TopCat.ofHom ⟨coordinatePermutation 1 (Equiv.swap 0 1),
        (coordinatePermutation 1 (Equiv.swap 0 1)).continuous⟩ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  induction p using Projectivization.ind with | h v hv =>
  change mk (normalLineLinear 0 v) _ =
    mk ((LinearEquiv.funCongrLeft ℂ ℂ (Equiv.swap (0 : Fin 2) 1)) v) _
  congr 1
  ext j
  fin_cases j <;> simp [normalLineLinear]

lemma normalizedHyperplaneClass_zero_ordinaryImage :
    ordinaryImage (P202Specs.ThomClass.ambientPair (hyperplaneInclusion 0)) 2
      (normalizedHyperplaneClass 0) =
    ordinaryImage (localPair (Space 1) (projectiveOrigin 1)) 2 (positiveLocalCohomologyClass 1) := by
  have h := ordinaryImage_pullback (normalProjectiveLinePair 0) 2 (normalizedHyperplaneClass 0)
  change hPullback ℤ (normalProjectiveLine 0) 2 _ = _ at h
  rw [normalProjectiveLine_zero_eq_swap, coordinateSwap_pullback] at h
  change ordinaryImage _ 2 (normalizedHyperplaneClass 0) =
    ordinaryImage (localPair (Space 1) (projectiveOrigin 1)) 2
      (((relativeCohomologyFunctor ℤ ℤ 2).map (normalProjectiveLinePair 0).op)
        (normalizedHyperplaneClass 0)) at h
  exact h.trans (congrArg (ordinaryImage (localPair (Space 1) (projectiveOrigin 1)) 2)
    (normalizedHyperplaneClass_normalLine_pullback 0))

end P202.ComplexProjectiveRing
end

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite Set Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
namespace P202.ComplexProjectiveRing
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202.ThomClass
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology
variable (R : Type v) [CommRing R]

/-- In the rank degree, actual normal fiber restrictions detect a global
normal-bundle class, before constructing an orientation. -/
lemma normalClass_fiberwise_ext [CompactSpace P]
    (N : NormalBundle T S i) (d : ℕ) (hd : n-m=d) (hpos : 0<d)
    (c e : relativeCohomology R R (normalPair N) (d : ℤ))
    (h : ∀ p : P,
      (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c =
      (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op e) : c=e := by
  let g := fun p : P => (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c
  have hloc : ∀ p : P, ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ NormalThomOn R N d g U := by
    intro p
    obtain ⟨a,U,hUo,hp,hUa,cModel,hc⟩ := normalClass_locally_constant R N d c p
    exact ⟨U,hUo,hp,normalThomOn_of_chart R N d hd hpos g a U hUa cModel hc⟩
  obtain ⟨a,ha,hu⟩ := normalClass_exists_unique_of_locally R N d g hloc
  exact (hu c (fun _ => rfl)).trans (hu e (fun p => (h p).symm)).symm

/-- The vanishing locus of a genuine normal-bundle class is clopen. -/
lemma normalClass_zero_isClopen (N : NormalBundle T S i) (d : ℕ)
    (c : relativeCohomology R R (normalPair N) (d : ℤ)) :
    IsClopen {p : P | (relativeCohomologyFunctor R R (d : ℤ)).map
      (fiberToNormal N p).op c = 0} := by
  have hloc (p : P) : ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U,
      ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N q).op c=0 ↔
       (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c=0) := by
    obtain ⟨a,U,hUo,hp,hUa,cModel,hc⟩ := normalClass_locally_constant R N d c p
    let F := relativeCohomologyFunctor R R (d : ℤ)
    have hz (q : P) (hq : q ∈ U) : F.map (fiberToNormal N q).op c = 0 ↔ cModel=0 := by
      rw [← hc q hq]
      change (asIso (F.map (fiberCoordinatesIso N a q (hUa hq)).hom.op)).toLinearEquiv cModel = 0 ↔ _
      exact (asIso (F.map (fiberCoordinatesIso N a q (hUa hq)).hom.op)).toLinearEquiv.map_eq_zero_iff
    exact ⟨U,hUo,hp,fun q hq => (hz q hq).trans (hz p hp).symm⟩
  have hopen : IsOpen {p : P | (relativeCohomologyFunctor R R (d : ℤ)).map
      (fiberToNormal N p).op c = 0} := by
    apply isOpen_iff_forall_mem_open.mpr
    intro p hp
    obtain ⟨U,hUo,hpU,hconst⟩ := hloc p
    exact ⟨U,fun q hq => (hconst q hq).mpr hp,hUo,hpU⟩
  refine ⟨?_,hopen⟩
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro p hp
  obtain ⟨U,hUo,hpU,hconst⟩ := hloc p
  exact ⟨U,fun q hq hz => hp ((hconst q hq).mp hz),hUo,hpU⟩

lemma normalClass_zero_of_one [CompactSpace P] [PreconnectedSpace P]
    (N : NormalBundle T S i) (d : ℕ) (hd : n-m=d) (hpos : 0<d)
    (c : relativeCohomology R R (normalPair N) (d : ℤ)) (p : P)
    (hp : (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c = 0) : c=0 := by
  have he := (normalClass_zero_isClopen R N d c).eq_univ ⟨p,hp⟩
  apply normalClass_fiberwise_ext R N d hd hpos
  intro q
  rw [map_zero]
  change q ∈ {p : P | (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c=0}
  rw [he]
  trivial

lemma normalClass_nonzero_fiber [CompactSpace P] [PreconnectedSpace P]
    (N : NormalBundle T S i) (d : ℕ) (hd : n-m=d) (hpos : 0<d)
    (c : relativeCohomology R R (normalPair N) (d : ℤ)) (hc : c≠0) (p : P) :
    (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c ≠ 0 := by
  intro hp
  exact hc (normalClass_zero_of_one R N d hd hpos c p hp)

lemma normalClass_oneFiber_injective [CompactSpace P] [PreconnectedSpace P]
    (N : NormalBundle T S i) (d : ℕ) (hd : n-m=d) (hpos : 0<d) (p : P) :
    Function.Injective ((relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op) := by
  intro c e he
  apply sub_eq_zero.mp
  apply normalClass_zero_of_one R N d hd hpos (c-e) p
  rw [map_sub,he,sub_self]

/-- The actual model-fiber cohomology is a free integral rank-one module. -/
def normalModelCohomologyEquiv (d : ℕ) :
    relativeCohomology ℤ ℤ (modelPair.{u} d) (d : ℤ) ≃ₗ[ℤ] ℤ := by
  let e := Classical.choice (P202.TransverseThomProduct.modelRelativeHomotopyEquiv_all ℤ d)
  exact P202.TransverseThomProduct.evaluationOnSingleEquiv ℤ
    (ordinary ℤ ℤ (modelPair.{u} d)) (d : ℤ) e

def normalFiberCohomologyEquiv (N : NormalBundle T S i) (d : ℕ)
    (hd : n-m=d) (p : P) : relativeCohomology ℤ ℤ (fiberPair N p) (d : ℤ) ≃ₗ[ℤ] ℤ := by
  let a := Classical.choose ((normalBundle N).covers p)
  have hpa := Classical.choose_spec ((normalBundle N).covers p)
  let e := ((relativeCohomologyFunctor ℤ ℤ (d : ℤ)).mapIso
    (fiberCoordinatesIso N a p hpa).op).symm.toLinearEquiv
  let f : relativeCohomology ℤ ℤ (modelPair.{u} (n-m)) (d : ℤ) ≃ₗ[ℤ] ℤ := by
    rw [hd]
    exact normalModelCohomologyEquiv.{u} d
  exact e.trans f

end P202.ComplexProjectiveRing

end

noncomputable section
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData

/-- At the point hyperplane, a primitive relative class normalized on the
specified positive transverse simplex gives the full geometric Thom data. -/
lemma pointHyperplaneThomData_of_class
    (c : relativeCohomology ℤ ℤ (P202Specs.ThomClass.ambientPair (hyperplaneInclusion 0)) 2)
    (hc : IsGenerator ℤ c)
    (he : relativeEvaluation _ 2 c
      (((relativeHomologyFunctor ℤ ℤ 2).map (positiveHyperplaneSlice 0))
        (P202.SpheresDisks.affineClassLinear ℤ ℤ 2 1)) = 1) :
    ∃ d : HyperplaneThomData 0, d.thom = c := by
  obtain ⟨N,K,hK⟩ := inclusion_normalizedNormal_exists 1 0 (by omega)
  obtain ⟨o,ho⟩ := ambientClass_orientation_exists_subsingleton ℤ
    (inclusion_smoothEmbedding 1 0 (by omega)) N 2 K hK c hc
  refine ⟨{
    sourceAtlas := projectiveSmoothManifold 0
    targetAtlas := projectiveSmoothManifold 1
    embedding := inclusion_smoothEmbedding 1 0 (by omega)
    normal := N
    orientation := o
    tubular := K
    tubular_normalized := hK
    thom := c
    thom_fiber_values := ho
    positiveSlice := positiveHyperplaneSlice 0
    positiveSlice_formula := positiveHyperplaneSlice_formula 0
    simplex_cycle := positiveSimplex_cycle 2
    complex_normal_positive := ?_ }, rfl⟩
  rw [P202.SpheresDisks.affineClassLinear_apply] at he
  convert he using 1 <;> rfl

end P202.ComplexProjectiveRing

namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
lemma pointHyperplaneThomData :
    ∃ d : HyperplaneThomData 0, d.thom = normalizedHyperplaneClass 0 :=
  pointHyperplaneThomData_of_class (normalizedHyperplaneClass 0)
    (normalizedHyperplaneClass_isGenerator 0) (normalizedHyperplaneClass_evaluation 0)
end P202.ComplexProjectiveRing

end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs P202Specs.CupProduct

/-- The two coordinate swaps in the transverse projective line act trivially
on ordinary cohomology, so this restriction is the standard one. -/
lemma normalProjectiveLine_pullback (m n : ℕ) (a : cohomology (m+1) n) :
    hPullback ℤ (normalProjectiveLine m) n a =
      hPullback ℤ (standardInclusion (m+1) 1 (by omega)) n a := by
  rw [normalProjectiveLine_factor, ← hPullback_comp, ← hPullback_comp]
  change hPullback ℤ
    (TopCat.ofHom ⟨coordinatePermutation 1 (Equiv.swap 0 1),
      (coordinatePermutation 1 (Equiv.swap 0 1)).continuous⟩) n
      (hPullback ℤ (standardInclusion (m+1) 1 (by omega)) n
        (hPullback ℤ
          (TopCat.ofHom ⟨coordinatePermutation (m+1) (Equiv.swap 1 (Fin.last (m+1))),
            (coordinatePermutation (m+1) (Equiv.swap 1 (Fin.last (m+1)))).continuous⟩) n a)) = _
  rw [coordinateSwap_pullback, coordinateSwap_pullback]
  rfl

/-- The normalized relative hyperplane generator has the same ordinary image
as the canonical positive degree-two class in every ambient dimension. -/
lemma normalizedHyperplaneClass_ordinaryImage (m : ℕ) :
    ordinaryImage (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)) 2
      (normalizedHyperplaneClass m) = positiveDegreeTwoClass m := by
  apply (inclusion_cohomology_bijective (m+1) 1 (by omega) 2 (by omega)).injective
  rw [positiveDegreeTwoClass_restrict_line]
  rw [← normalProjectiveLine_pullback]
  have h := ordinaryImage_pullback (normalProjectiveLinePair m) 2 (normalizedHyperplaneClass m)
  change hPullback ℤ (normalProjectiveLine m) 2 _ = _ at h
  exact h.trans (congrArg (ordinaryImage (localPair (Space 1) (projectiveOrigin 1)) 2)
    (normalizedHyperplaneClass_normalLine_pullback m))

end P202.ComplexProjectiveRing
end

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite Set Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
namespace P202.ComplexProjectiveRing
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202.ThomClass
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

/-- A nonzero actual normal-bundle class selects the orientation generators
on its positive rays. Their local compatibility follows from uniqueness in
every original bundle trivialization. -/
lemma normalClass_positive_orientation [CompactSpace P] [PreconnectedSpace P]
    (N : NormalBundle T S i) (d : ℕ) (hd : n-m=d) (hpos : 0<d)
    (c : relativeCohomology ℤ ℤ (normalPair N) (d : ℤ)) (hc : c≠0) :
    ∃ o : Orientation ℤ N d, ∀ p : P, ∃ r : ℤ, 0<r ∧
      (relativeCohomologyFunctor ℤ ℤ (d : ℤ)).map (fiberToNormal N p).op c =
        r • o.generator p := by
  let F := relativeCohomologyFunctor ℤ ℤ (d : ℤ)
  have hRay (p : P) := existsUnique_positive_primitive (normalFiberCohomologyEquiv N d hd p)
    (F.map (fiberToNormal N p).op c) (normalClass_nonzero_fiber ℤ N d hd hpos c hc p)
  let g := fun p : P => Classical.choose (hRay p)
  have hg (p : P) : Function.Bijective (fun z : ℤ => z • g p) ∧
      ∃ r : ℤ, 0<r ∧ F.map (fiberToNormal N p).op c = r • g p :=
    (Classical.choose_spec (hRay p)).1
  have hgu (p : P) (w : relativeCohomology ℤ ℤ (fiberPair N p) (d : ℤ))
      (hw : Function.Bijective (fun z : ℤ => z • w) ∧
        ∃ r : ℤ, 0<r ∧ F.map (fiberToNormal N p).op c = r • w) : w=g p :=
    (Classical.choose_spec (hRay p)).2 w hw
  have hgen (p : P) : Function.Bijective (fun r : ℤ => r • g p) := (hg p).1
  have hgenModule (p : P) : P202Specs.LocalOrientation.IsGenerator ℤ (g p) := by
    change Function.Bijective _
    convert hgen p using 1
    funext r
    exact Int.cast_smul_eq_zsmul (R := ℤ) r (g p)
  refine ⟨{generator := g, generates := hgenModule, locally_constant := ?_}, fun p => (hg p).2⟩
  intro p
  obtain ⟨a,U,hUo,hp,hUa,cModel,hlocal⟩ := normalClass_locally_constant ℤ N d c p
  have hcm : cModel ≠ 0 := by
    intro hz
    apply normalClass_nonzero_fiber ℤ N d hd hpos c hc p
    rw [← hlocal p hp,hz,map_zero]
  let eModel : relativeCohomology ℤ ℤ (modelPair.{u} (n-m)) (d : ℤ) ≃ₗ[ℤ] ℤ := by
    rw [hd]
    exact normalModelCohomologyEquiv.{u} d
  obtain ⟨gModel,hgm,hgmu⟩ := existsUnique_positive_primitive eModel cModel hcm
  refine ⟨a,U,hUo,hp,hUa,gModel,?_⟩
  intro q hq
  let eCoord := (asIso (F.map (fiberCoordinatesIso N a q (hUa hq)).hom.op)).toLinearEquiv
  apply hgu q (eCoord gModel)
  refine ⟨?_,?_⟩
  · have heq : (fun z : ℤ => z • eCoord gModel) = eCoord ∘ (fun z : ℤ => z • gModel) := by
      funext z
      exact (map_zsmul eCoord z gModel).symm
    rw [heq]
    exact eCoord.bijective.comp hgm.1
  · obtain ⟨r,hr,hcg⟩ := hgm.2
    refine ⟨r,hr,?_⟩
    calc
      F.map (fiberToNormal N q).op c = eCoord cModel := (hlocal q hq).symm
      _ = eCoord (r • gModel) := congrArg eCoord hcg
      _ = r • eCoord gModel := map_zsmul eCoord r gModel

/-- A primitive global normal-bundle class over a connected base is primitive
on every normal fiber. The rank and local gluing statements are proved inputs;
no orientability assumption is needed. -/
lemma normalClass_primitive_fibers [CompactSpace P] [PreconnectedSpace P]
    (N : NormalBundle T S i) (d : ℕ) (hd : n-m=d) (hpos : 0<d)
    (c : relativeCohomology ℤ ℤ (normalPair N) (d : ℤ))
    (hc : P202Specs.LocalOrientation.IsGenerator ℤ c) :
    ∀ p : P, P202Specs.LocalOrientation.IsGenerator ℤ
      ((relativeCohomologyFunctor ℤ ℤ (d : ℤ)).map (fiberToNormal N p).op c) := by
  have hnon : c≠0 := by
    intro hz
    have he : (0 : ℤ)=1 := hc.injective (by simp only [hz,smul_zero])
    omega
  obtain ⟨o,ho⟩ := normalClass_positive_orientation N d hd hpos c hnon
  obtain ⟨b,hb,hbu⟩ := normalClass_exists_unique_of_orientation ℤ N d hd hpos o
  intro p
  obtain ⟨r,hr,hcp⟩ := ho p
  have hcb : c = r • b := by
    apply normalClass_oneFiber_injective ℤ N d hd hpos p
    rw [map_zsmul,hb p]
    exact hcp
  have hcBare : Function.Bijective (fun z : ℤ => z • c) := by
    change Function.Bijective _ at hc
    convert hc using 1
    funext z
    exact (Int.cast_smul_eq_zsmul (R := ℤ) z c).symm
  obtain ⟨s,hs⟩ := hcBare.surjective b
  have hrs : r*s=1 := by
    apply hcBare.injective
    calc
      (r*s) • c = r • (s • c) := mul_smul r s c
      _ = r • b := congrArg (fun z => r • z) hs
      _ = c := hcb.symm
      _ = (1 : ℤ) • c := (one_smul ℤ c).symm
  have hru : r=1 ∨ r=-1 := Int.eq_one_or_neg_one_of_mul_eq_one hrs
  have hr1 : r=1 := hru.resolve_right (by omega)
  have heval : (relativeCohomologyFunctor ℤ ℤ (d : ℤ)).map (fiberToNormal N p).op c =
      o.generator p := by simpa only [hr1,one_smul] using hcp
  rw [heval]
  exact o.generates p

end P202.ComplexProjectiveRing

namespace P202.ComplexProjectiveRing
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202.ThomClass
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

/-- A primitive actual ambient relative class constructs its intrinsic normal
orientation over a connected compact submanifold of positive codimension. -/
lemma ambientClass_orientation_exists_primitive [CompactSpace P] [PreconnectedSpace P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (d : ℕ)
    (hd : n-m=d) (hpos : 0<d)
    (K : TubularNeighborhood N) (hK : NormalCompatible N K)
    (c : relativeCohomology ℤ ℤ (ambientPair i) (d : ℤ))
    (hc : P202Specs.LocalOrientation.IsGenerator ℤ c) :
    ∃ o : Orientation ℤ N d, HasFiberValues ℤ o c := by
  let e := ambientNormalCohomologyEquiv hi N K ℤ (d : ℤ)
  have hN : P202Specs.LocalOrientation.IsGenerator ℤ (e c) :=
    (linearEquiv_generator_iff ℤ e c).mpr hc
  have hgen := normalClass_primitive_fibers N d hd hpos (e c) hN
  exact ⟨normalOrientationOfClass ℤ N d (e c) hgen,
    ambientClass_hasFiberValues ℤ hi N d K hK c hgen⟩

open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.LocalOrientation

/-- The actual complex-normal hyperplane Thom data exist in every dimension.
The primitive relative class has the specified positive-complex-slice value,
which fixes the sign of the compatible orientation constructed from its fibers. -/
lemma hyperplaneThomData_exists (m : ℕ) :
    ∃ d : HyperplaneThomData m, d.thom = normalizedHyperplaneClass m := by
  obtain ⟨N,K,hK⟩ := inclusion_normalizedNormal_exists (m+1) m (by omega)
  obtain ⟨o,ho⟩ := ambientClass_orientation_exists_primitive
    (inclusion_smoothEmbedding (m+1) m (by omega)) N 2 (by omega) (by omega) K hK
    (normalizedHyperplaneClass m) (normalizedHyperplaneClass_isGenerator m)
  exact ⟨{
    sourceAtlas := projectiveSmoothManifold m
    targetAtlas := projectiveSmoothManifold (m+1)
    embedding := inclusion_smoothEmbedding (m+1) m (by omega)
    normal := N
    orientation := o
    tubular := K
    tubular_normalized := hK
    thom := normalizedHyperplaneClass m
    thom_fiber_values := ho
    positiveSlice := positiveHyperplaneSlice m
    positiveSlice_formula := positiveHyperplaneSlice_formula m
    simplex_cycle := positiveSimplex_cycle 2
    complex_normal_positive := normalizedHyperplaneClass_positiveSlice_evaluation m }, rfl⟩

end P202.ComplexProjectiveRing

end


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.CohomologyPairs P202Specs.CupProduct

/-- The full geometric conclusion on CP¹, with the actual complex-normal
hyperplane Thom class and both local and ordinary value-one evaluations. -/
lemma lineGeometricGenerator (C : CohomologyRing ℤ (projectiveSpace 1)) :
    GeometricGenerator 1 C (positiveDegreeTwoClass 0) := by
  refine geometricGenerator_of_positivePower_identifications 1 C (positiveDegreeTwoClass 0)
    (by intro h; omega) ?_ ?_
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    obtain ⟨d, hd⟩ := pointHyperplaneThomData
    refine ⟨d, ?_⟩
    cases hk
    rw [hd]
    exact positiveDegreeTwoClass_line.trans normalizedHyperplaneClass_zero_ordinaryImage.symm
  · intro i hi him
    have hi1 : i = 1 := by omega
    subst i
    rw [homogeneousPower_one, standardInclusion_self]
    have hid := congrArg (fun f => f (positiveDegreeTwoClass 0))
      ((ordinaryCohomologyFunctor ℤ ℤ (2 : ℤ)).map_id (Opposite.op (projectiveSpace 1)))
    exact hid.trans positiveDegreeTwoClass_line

lemma lineGeometricPresentation (C : CohomologyRing ℤ (projectiveSpace 1)) :
    letI := C.gradedRing
    ∃ e : truncatedPolynomial 1 ≃+* totalCohomology 1,
      GeometricGenerator 1 C (positiveDegreeTwoClass 0) ∧
      e (polynomialClass 1 Polynomial.X) =
        DirectSum.of (H ℤ (projectiveSpace 1)) 2 (positiveDegreeTwoClass 0) ∧
      ∀ i : ℕ, i ≤ 1 → ∃ b : cohomology 1 (2*i),
        Function.Bijective (fun z : ℤ => z • b) ∧
        e ((polynomialClass 1 Polynomial.X)^i) =
          DirectSum.of (H ℤ (projectiveSpace 1)) (2*i) b := by
  letI := C.gradedRing
  obtain ⟨e,he,hp⟩ := linePresentation C
  exact ⟨e,lineGeometricGenerator C,he,hp⟩

end P202.ComplexProjectiveRing
end


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.CohomologyPairs P202Specs.CupProduct
open P202Specs.RelativeSingularChains P202Specs.RelativeCupProduct
  P202Specs.TransverseThomProduct P202Specs.LocalOrientation

/-- In a rank-one integral module, a class whose image is primitive is
itself primitive. The target need not be known to be cyclic in advance. -/
lemma isGenerator_of_linear_image {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (e : V ≃ₗ[ℤ] ℤ) (f : V →ₗ[ℤ] W)
    (a : V) (ha : IsGenerator ℤ (f a)) : IsGenerator ℤ a := by
  let g := P202.LocalOrientation.generatorEquiv ℤ (f a) ha
  have hone : g.symm (f a) = 1 := by
    apply g.injective
    rw [LinearEquiv.apply_symm_apply]
    simp only [g, P202.LocalOrientation.generatorEquiv_apply, one_smul]
  have h := generates_of_pairing_one e.toAddEquiv a
    ((g.symm.toLinearMap.comp f).toAddMonoidHom) hone
  change Function.Bijective _
  convert h using 1
  funext z
  exact Int.cast_smul_eq_zsmul (R := ℤ) z a

/-- Primitivity of a restriction of a point-supported top class implies
primitivity of its ordinary image on the actual projective space. -/
lemma supportedTop_forget_primitive (m : ℕ)
    (A : SupportedClass ℤ (projectiveSpace m))
    (hs : A.support = {projectiveOrigin m}) (hd : A.degree = 2*m)
    {Q : Pair} (f : Q ⟶ (⟨projectiveSpace m,A.supportᶜ⟩ : Pair))
    (hgen : IsGenerator ℤ (relativePullback ℤ f A.degree A.value)) :
    Function.Bijective (fun z : ℤ => z •
      forget ℤ (⟨projectiveSpace m,A.supportᶜ⟩ : Pair) A.degree A.value) := by
  rcases A with ⟨support, closed, degree, a⟩
  dsimp only at hs hd f hgen ⊢
  subst support
  subst degree
  have hlocal : IsGenerator ℤ a := isGenerator_of_linear_image
    (positiveLocalCohomologyEquiv m) (relativePullback ℤ f (2*m)) a hgen
  have hbare : Function.Bijective (fun z : ℤ => z • a) := by
    change Function.Bijective _ at hlocal
    convert hlocal using 1
    funext z
    exact (Int.cast_smul_eq_zsmul (R := ℤ) z a).symm
  have hfun : (fun z : ℤ => z • forget ℤ
      (⟨projectiveSpace m,({projectiveOrigin m} : Set (projectiveSpace m))ᶜ⟩ : Pair) (2*m) a) =
      ordinaryImage (localPair (Space m) (projectiveOrigin m)) (2*m) ∘
        (fun z : ℤ => z • a) := by
    funext z
    exact (map_zsmul _ z a).symm
  rw [hfun]
  exact (ordinaryImage_local_top_bijective m).comp hbare

/-- A point-supported relative product whose ordinary image is a power and
whose local restriction is primitive gives a primitive homogeneous top power. -/
lemma topPower_primitive_of_supported_product (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2)
    (A : SupportedClass ℤ (projectiveSpace m))
    (hs : A.support = {projectiveOrigin m}) (hd : A.degree = 2*m)
    (hp : letI := C.gradedRing
      supportedOrdinary ℤ A = (DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^m)
    {Q : Pair} (f : Q ⟶ (⟨projectiveSpace m,A.supportᶜ⟩ : Pair))
    (hgen : IsGenerator ℤ (relativePullback ℤ f A.degree A.value)) :
    Function.Bijective (fun z : ℤ => z • homogeneousPower m C v m) := by
  letI := C.gradedRing
  have hA := supportedTop_forget_primitive m A hs hd f hgen
  rcases A with ⟨support,closed,degree,a⟩
  dsimp only at hs hd hp hA
  subst degree
  have he : homogeneousPower m C v m = forget ℤ (⟨projectiveSpace m,supportᶜ⟩ : Pair) (2*m) a := by
    apply DirectSum.of_injective (β := H ℤ (projectiveSpace m)) (2*m)
    exact (of_homogeneousPower m C v m).trans hp.symm
  rwa [he]

end P202.ComplexProjectiveRing
end


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Set Topology
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
  P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
  P202Specs.RelativeCupProduct P202Specs.PrismHomotopy
open P202Specs.ThomClass P202Specs.TransverseThomProduct
  P202.TransverseThomProduct SmoothManifolds.ModelData
open scoped TensorProduct

/-- One complex coordinate is the ordered real two-coordinate model. -/
def complexLineRealHomeomorph : ℂ ≃ₜ (Fin 2 → ℝ) :=
  (Homeomorph.piUnique (fun _ : Fin 1 => ℂ)).symm.trans
    (orderedRealComplexHomeomorph 1).symm

lemma complexLineRealHomeomorph_zero : complexLineRealHomeomorph 0 = 0 := by
  change orderedComplexRealCoordinates 1 (fun _ : Fin 1 => (0 : ℂ)) = 0
  exact orderedComplexRealCoordinates_zero 1

lemma complexLineRealHomeomorph_symm_zero : complexLineRealHomeomorph.symm 0 = 0 := by
  apply complexLineRealHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, complexLineRealHomeomorph_zero]

/-- The actual complex punctured line pair is the real rank-two model pair. -/
def complexLineModelIso : complexLinePair ≅ modelPair.{0} 2 where
  hom := {
    map := TopCat.ofHom ⟨fun z => ULift.up (complexLineRealHomeomorph z),
      continuous_uliftUp.comp complexLineRealHomeomorph.continuous⟩
    mapsTo := by
      intro z hz h
      apply hz
      exact complexLineRealHomeomorph.injective
        (h.trans complexLineRealHomeomorph_zero.symm) }
  inv := {
    map := TopCat.ofHom ⟨fun z => complexLineRealHomeomorph.symm z.down,
      complexLineRealHomeomorph.symm.continuous.comp continuous_uliftDown⟩
    mapsTo := by
      intro z hz h
      apply hz
      exact complexLineRealHomeomorph.symm.injective
        (h.trans complexLineRealHomeomorph_symm_zero.symm) }
  hom_inv_id := PairMap.ext _ _ (TopCat.hom_ext (ContinuousMap.ext fun z =>
    complexLineRealHomeomorph.symm_apply_apply z))
  inv_hom_id := PairMap.ext _ _ (TopCat.hom_ext (ContinuousMap.ext fun z => by
    apply ULift.ext
    exact complexLineRealHomeomorph.apply_symm_apply z.down))

/-- Preserve the given finite complex coordinate order when replacing each
coordinate by its ordered real pair. -/
def complexCoordinateBlocksHomeomorph (m : ℕ) :
    (Fin m → ℂ) ≃ₜ ULift.{0} (Fin m → Euclidean 2) :=
  (Homeomorph.piCongrRight (fun _ : Fin m => complexLineRealHomeomorph)).trans
    Homeomorph.ulift.symm

/-- Transfer a complex-line class to the real rank-two model through the
inverse of the actual pair isomorphism. -/
def complexLineModelClass (a : HR ℤ complexLinePair 2) :
    HR ℤ (modelPair.{0} 2) 2 :=
  relativePullback ℤ complexLineModelIso.inv 2 a

lemma complexLineModelClass_generates (a : HR ℤ complexLinePair 2)
    (ha : Function.Bijective (fun r : ℤ => r • a)) :
    Function.Bijective (fun r : ℤ => r • complexLineModelClass a) := by
  let E := ((relativeCohomologyFunctor ℤ ℤ (2 : ℤ)).mapIso
    complexLineModelIso.symm.op).toLinearEquiv
  change Function.Bijective (fun r : ℤ => r • E a)
  have h := E.bijective.comp ha
  change Function.Bijective (fun r : ℤ => E (r • a)) at h
  simpa only [map_zsmul] using h

/-- The actual degree-two factor supported on a projective coordinate hyperplane. -/
def projectiveCoordinateFactor (m : ℕ)
    (c : ∀ j : Fin m, HR ℤ (coordinateHyperplanePair m j.castSucc) 2) (j : Fin m) :
    SupportedClass ℤ (projectiveSpace m) :=
  ⟨coordinateHyperplane m j.castSucc, coordinateHyperplane_closed m j.castSucc, 2, c j⟩

def complexCoordinateModelClasses (m : ℕ)
    (c : ∀ j : Fin m, HR ℤ (coordinateHyperplanePair m j.castSucc) 2) (j : Fin m) :
    HR ℤ (modelPair.{0} 2) 2 :=
  complexLineModelClass (relativePullback ℤ (complexProjectiveCoordinateLine m j) 2 (c j))

/-- Factorwise local formulas use the original coordinate order and the
actual punctured rank-two model. -/
lemma projectiveCoordinateFactor_chart_comparison (k : ℕ)
    (c : ∀ j : Fin (k+1), HR ℤ (coordinateHyperplanePair (k+1) j.castSucc) 2)
    (j : Fin (k+1)) :
    supportedPullback ℤ
      (TopCat.ofHom ⟨affineChart (k+1) (k+1) le_rfl,
        affineChart_continuous (k+1) (k+1) le_rfl⟩)
      (projectiveCoordinateFactor (k+1) c j) =
    supportedPullback ℤ
      (TopCat.ofHom ⟨complexCoordinateBlocksHomeomorph (k+1),
        (complexCoordinateBlocksHomeomorph (k+1)).continuous⟩)
      (rawGradedBlockFactor ℤ k (fun _ => 2) (fun _ => 2)
        (complexCoordinateModelClasses (k+1) c) j) := by
  let X : TopCat := TopCat.of (Fin (k+1) → ℂ)
  let Y : TopCat := TopCat.of (ULift.{0} (Fin (k+1) → Euclidean 2))
  let f : X ⟶ projectiveSpace (k+1) :=
    TopCat.ofHom ⟨affineChart (k+1) (k+1) le_rfl,
      affineChart_continuous (k+1) (k+1) le_rfl⟩
  let g : X ⟶ Y := TopCat.ofHom ⟨complexCoordinateBlocksHomeomorph (k+1),
    (complexCoordinateBlocksHomeomorph (k+1)).continuous⟩
  let A := projectiveCoordinateFactor (k+1) c j
  let B := rawGradedBlockFactor ℤ k (fun _ => 2) (fun _ => 2)
    (complexCoordinateModelClasses (k+1) c) j
  have hs : f ⁻¹' A.support = g ⁻¹' B.support := by
    ext z
    change affineChart (k+1) (k+1) le_rfl z ∈ coordinateHyperplane (k+1) j.castSucc ↔
      complexLineRealHomeomorph (z j) = 0
    refine (coordinateHyperplane_topAffineChart (k+1) j z).trans ?_
    constructor
    · intro h
      rw [h, complexLineRealHomeomorph_zero]
    · intro h
      exact complexLineRealHomeomorph.injective (h.trans complexLineRealHomeomorph_zero.symm)
  let P : Pair := ⟨X,(f ⁻¹' A.support)ᶜ⟩
  let J : P ⟶ complexCoordinatePair (k+1) j := ⟨𝟙 X, by
    intro z hz
    change z j ≠ 0
    intro h
    exact hz ((coordinateHyperplane_topAffineChart (k+1) j z).mpr h)⟩
  let G : P ⟶ (⟨Y,B.supportᶜ⟩ : Pair) := ⟨g, by
    intro z hz hg
    exact hz ((Set.ext_iff.mp hs z).mpr hg)⟩
  let Q : (⟨Y,B.supportᶜ⟩ : Pair) ⟶ modelPair.{0} 2 := {
    map := TopCat.ofHom ⟨fun z => ULift.up (z.down j),
      continuous_uliftUp.comp ((continuous_apply j).comp continuous_uliftDown)⟩
    mapsTo := fun _ h => h }
  apply supportedPullbacks_eq_of_formula ℤ f g A B hs rfl G rfl
  change relativePullback ℤ (⟨f, fun _ hz => hz⟩ : P ⟶ coordinateHyperplanePair (k+1) j.castSucc)
      2 (c j) =
    relativePullback ℤ G 2 (relativePullback ℤ Q 2
      (complexLineModelClass (relativePullback ℤ (complexProjectiveCoordinateLine (k+1) j) 2 (c j))))
  have hF : (⟨f, fun _ hz => hz⟩ : P ⟶ coordinateHyperplanePair (k+1) j.castSucc) =
      J ≫ complexAffineCoordinatePair (k+1) j := PairMap.ext _ _ rfl
  have hG : G ≫ Q ≫ complexLineModelIso.inv = J ≫ complexCoordinateProjection (k+1) j := by
    apply PairMap.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    change complexLineRealHomeomorph.symm (complexLineRealHomeomorph (z j)) = z j
    exact complexLineRealHomeomorph.symm_apply_apply (z j)
  rw [hF]
  conv_lhs => rw [← relativePullback_comp']
  conv_rhs => simp only [complexLineModelClass, relativePullback_comp', Category.assoc]
  have hG' := congrArg (fun u => u ≫ complexProjectiveCoordinateLine (k+1) j) hG
  simp only [Category.assoc] at hG'
  rw [hG']
  conv_rhs => rw [← relativePullback_comp', ← relativePullback_comp']
  rw [complexAffineCoordinate_class_projection]

/-- Primitive transverse complex line restrictions make the actual finite
ordered hyperplane product primitive on the last affine chart. This statement
is entirely in the original relative singular cohomology. -/
lemma projectiveCoordinate_orderedCup_chart_generates
    (μ : NaturalRelativeCupProduct ℤ) (k : ℕ)
    (c : ∀ j : Fin (k+1), HR ℤ (coordinateHyperplanePair (k+1) j.castSucc) 2)
    (hc : ∀ j, Function.Bijective (fun r : ℤ => r •
      relativePullback ℤ (complexProjectiveCoordinateLine (k+1) j) 2 (c j))) :
    Function.Bijective (fun r : ℤ => r •
      (supportedPullback ℤ
        (TopCat.ofHom ⟨affineChart (k+1) (k+1) le_rfl,
          affineChart_continuous (k+1) (k+1) le_rfl⟩)
        (orderedCup ℤ μ k (projectiveCoordinateFactor (k+1) c))).value) := by
  have h := rawModelBlocks_generates ℤ μ k (fun _ => 2) (fun _ => 2) rfl
    (complexCoordinateModelClasses (k+1) c)
    (fun j => by
      have hj := (complexLineModelClass_generates _ (hc j)).surjective
      convert hj using 1
      funext r
      exact int_smul_eq_zsmul (inferInstance : Module ℤ (HR ℤ (modelPair.{0} 2) 2)) r _)
  have he := supportedPullback_homeomorph_generates ℤ
    (X := TopCat.of (Fin (k+1) → ℂ))
    (Y := TopCat.of (ULift.{0} (Fin (k+1) → Euclidean 2)))
    (complexCoordinateBlocksHomeomorph (k+1))
    (orderedCup ℤ μ k (rawGradedBlockFactor ℤ k (fun _ => 2) (fun _ => 2)
      (complexCoordinateModelClasses (k+1) c))) h
  have hcmp := orderedCup_pullbacks_eq_of_factor_equalities ℤ μ
    (TopCat.ofHom ⟨affineChart (k+1) (k+1) le_rfl,
      affineChart_continuous (k+1) (k+1) le_rfl⟩)
    (TopCat.ofHom ⟨complexCoordinateBlocksHomeomorph (k+1),
      (complexCoordinateBlocksHomeomorph (k+1)).continuous⟩)
    k (projectiveCoordinateFactor (k+1) c)
    (rawGradedBlockFactor ℤ k (fun _ => 2) (fun _ => 2)
      (complexCoordinateModelClasses (k+1) c))
    (projectiveCoordinateFactor_chart_comparison k c)
  rw [hcmp]
  convert he using 1
  funext r
  exact (int_smul_eq_zsmul (inferInstance : Module ℤ _) r _).symm

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Set Topology
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs P202Specs.CupProduct P202Specs.RelativeCupProduct

/-- A coordinate swap carries the jth complementary pair to the literal
last-coordinate ambient hyperplane pair. -/
def coordinateHyperplaneToAmbient (m : ℕ) (j : Fin (m+2)) :
    coordinateHyperplanePair (m+1) j ⟶ P202Specs.ThomClass.ambientPair (hyperplaneInclusion m) where
  map := TopCat.ofHom ⟨coordinatePermutation (m+1) (Equiv.swap j (Fin.last (m+1))),
    (coordinatePermutation (m+1) (Equiv.swap j (Fin.last (m+1)))).continuous⟩
  mapsTo := by
    intro x hx hy
    apply hx
    change coordinatePermutation (m+1) (Equiv.swap j (Fin.last (m+1))) x ∈
      Set.range (hyperplaneInclusion m) at hy
    rw [← lastCoordinateHyperplane_range] at hy
    have h := (coordinatePermutation_hyperplane (m+1)
      (Equiv.swap j (Fin.last (m+1))) (Fin.last (m+1)) x).mp hy
    simpa using h

/-- The actual normalized coordinate hyperplane relative class. -/
def coordinateHyperplaneClass (m : ℕ) (j : Fin (m+2)) :
    HR ℤ (coordinateHyperplanePair (m+1) j) 2 :=
  relativePullback ℤ (coordinateHyperplaneToAmbient m j) 2 (normalizedHyperplaneClass m)

lemma coordinateHyperplaneClass_ordinaryImage (m : ℕ) (j : Fin (m+2)) :
    ordinaryImage (coordinateHyperplanePair (m+1) j) 2 (coordinateHyperplaneClass m j) =
      positiveDegreeTwoClass m := by
  have h := ordinaryImage_pullback (coordinateHyperplaneToAmbient m j) 2 (normalizedHyperplaneClass m)
  change hPullback ℤ
    (TopCat.ofHom ⟨coordinatePermutation (m+1) (Equiv.swap j (Fin.last (m+1))),
      (coordinatePermutation (m+1) (Equiv.swap j (Fin.last (m+1)))).continuous⟩) 2 _ = _ at h
  rw [coordinateSwap_pullback] at h
  exact h.symm.trans (normalizedHyperplaneClass_ordinaryImage m)

def ambientToLastCoordinatePair (m : ℕ) :
    P202Specs.ThomClass.ambientPair (hyperplaneInclusion m) ⟶
      coordinateHyperplanePair (m+1) (Fin.last (m+1)) where
  map := 𝟙 _
  mapsTo := by
    intro x hx hy
    apply hx
    change x ∈ Set.range (hyperplaneInclusion m)
    rw [← lastCoordinateHyperplane_range]
    exact hy

/-- The full projective line through the affine origin and its j-axis. -/
def projectiveCoordinateLinePair (m : ℕ) (j : Fin (m+1)) :
    localPair (Space 1) (projectiveOrigin 1) ⟶ coordinateHyperplanePair (m+1) j.castSucc :=
  normalProjectiveLinePair m ≫ ambientToLastCoordinatePair m ≫
    coordinateSwapPair (m+1) (Fin.last (m+1)) 0 ≫
    coordinateSwapPair (m+1) 0 j.castSucc

lemma projectiveCoordinateLinePair_pullback (m : ℕ) (j : Fin (m+1)) (n : ℕ)
    (a : cohomology (m+1) n) :
    hPullback ℤ (projectiveCoordinateLinePair m j).map n a =
      hPullback ℤ (standardInclusion (m+1) 1 (by omega)) n a := by
  change hPullback ℤ
    (normalProjectiveLine m ≫ (𝟙 _) ≫
      TopCat.ofHom ⟨coordinatePermutation (m+1) (Equiv.swap (Fin.last (m+1)) 0),
        (coordinatePermutation (m+1) (Equiv.swap (Fin.last (m+1)) 0)).continuous⟩ ≫
      TopCat.ofHom ⟨coordinatePermutation (m+1) (Equiv.swap 0 j.castSucc),
        (coordinatePermutation (m+1) (Equiv.swap 0 j.castSucc)).continuous⟩) n a = _
  rw [← hPullback_comp, ← hPullback_comp, ← hPullback_comp,
    coordinateSwap_pullback, coordinateSwap_pullback]
  simp only [LinearMap.id_apply]
  have hid : hPullback ℤ (𝟙 (projectiveSpace (m+1))) n a = a := by
    change ((ordinaryCohomologyFunctor ℤ ℤ (n : ℤ)).map
      (𝟙 (Opposite.op (projectiveSpace (m+1))))) a = a
    exact congrArg (fun f => f a)
      ((ordinaryCohomologyFunctor ℤ ℤ (n : ℤ)).map_id (Opposite.op (projectiveSpace (m+1))))
  rw [hid]
  exact normalProjectiveLine_pullback m n a

lemma coordinateHyperplaneClass_projectiveLine (m : ℕ) (j : Fin (m+1)) :
    relativePullback ℤ (projectiveCoordinateLinePair m j) 2
      (coordinateHyperplaneClass m j.castSucc) = positiveLocalCohomologyClass 1 := by
  apply (ordinaryImage_local_top_bijective 1).injective
  have h := ordinaryImage_pullback (projectiveCoordinateLinePair m j) 2
    (coordinateHyperplaneClass m j.castSucc)
  calc
    ordinaryImage _ (2*1) (relativePullback ℤ (projectiveCoordinateLinePair m j) 2
        (coordinateHyperplaneClass m j.castSucc)) =
      hPullback ℤ (projectiveCoordinateLinePair m j).map 2
        (ordinaryImage _ 2 (coordinateHyperplaneClass m j.castSucc)) := h.symm
    _ = hPullback ℤ (projectiveCoordinateLinePair m j).map 2 (positiveDegreeTwoClass m) :=
      congrArg (hPullback ℤ (projectiveCoordinateLinePair m j).map 2)
        (coordinateHyperplaneClass_ordinaryImage m j.castSucc)
    _ = hPullback ℤ (standardInclusion (m+1) 1 (by omega)) 2 (positiveDegreeTwoClass m) :=
      projectiveCoordinateLinePair_pullback m j 2 _
    _ = ordinaryImage _ (2*1) (positiveLocalCohomologyClass 1) :=
      positiveDegreeTwoClass_restrict_line m (by omega)

/-- The standard affine complex line, relative to its puncture. -/
def complexAffineLinePair : complexLinePair ⟶ localPair (Space 1) (projectiveOrigin 1) where
  map := TopCat.ofHom ⟨fun w => affineChart 1 1 le_rfl (fun _ => w),
    (affineChart_continuous 1 1 le_rfl).comp (continuous_pi (fun _ => continuous_id))⟩
  mapsTo := by
    intro w hw he
    apply hw
    have h := affineChart_injective 1 1 le_rfl he
    simpa using congrFun h 0

lemma openEmbeddingLocalMap_cohomology_isIso {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] (f : X → Y) (hf : IsOpenEmbedding f) (x : X) (n : ℕ) :
    IsIso ((relativeCohomologyFunctor ℤ ℤ (n : ℤ)).map (openEmbeddingLocalMap f hf x).op) := by
  let e := hf.isEmbedding.toHomeomorph
  let U := Set.range f
  let D := P202.LocalOrientation.openLocalExcisionData U hf.isOpen_range (e x)
  have hh : openEmbeddingLocalMap f hf x =
      (P202.LocalOrientation.localPairIsoOfHomeomorph e x).hom ≫
        (P202.LocalOrientation.openLocalExcisionIso U hf.isOpen_range (e x)).hom ≫ D.inclusion :=
    PairMap.ext _ _ rfl
  haveI := P202.CohomologyExcisionMV.excision ℤ ℤ D (n : ℤ)
  rw [hh, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

lemma complexAffineLinePair_cohomology_isIso (n : ℕ) :
    IsIso ((relativeCohomologyFunctor ℤ ℤ (n : ℤ)).map complexAffineLinePair.op) := by
  let e : ℂ ≃ₜ (Fin 1 → ℂ) := (Homeomorph.funUnique (Fin 1) ℂ).symm
  let f : ℂ → Space 1 := affineChart 1 1 le_rfl ∘ e
  have hf : IsOpenEmbedding f := (affineChart_top_openEmbedding 1).comp e.isOpenEmbedding
  have hh : complexAffineLinePair = openEmbeddingLocalMap f hf 0 := PairMap.ext _ _ rfl
  rw [hh]
  exact openEmbeddingLocalMap_cohomology_isIso f hf 0 n

def positiveComplexLineCohomologyClass : HR ℤ complexLinePair 2 :=
  relativePullback ℤ complexAffineLinePair 2 (positiveLocalCohomologyClass 1)

lemma positiveComplexLineCohomologyClass_isGenerator :
    IsGenerator ℤ positiveComplexLineCohomologyClass := by
  haveI := complexAffineLinePair_cohomology_isIso 2
  let e := (asIso ((relativeCohomologyFunctor ℤ ℤ 2).map complexAffineLinePair.op)).toLinearEquiv
  exact (P202.LocalOrientation.generator_map_iff ℤ e (positiveLocalCohomologyClass 1)).mpr
    (positiveLocalCohomologyClass_isGenerator 1)

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Set Topology
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs P202Specs.CupProduct P202Specs.RelativeCupProduct

lemma complexNormalVector_swap_last_zero (m : ℕ) (w : ℂ) (i : Fin (m+2)) :
    complexNormalVector m w ((Equiv.swap (Fin.last (m+1)) 0) i) =
      if i = Fin.last (m+1) then 1 else if i = 0 then w else 0 := by
  by_cases hil : i = Fin.last (m+1)
  · subst i
    simp [complexNormalVector]
  · by_cases hi0 : i = 0
    · subst i
      simp [complexNormalVector, show m+1 ≠ 0 by omega]
    · have hiv0 : i.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hi0
      have hivl : i.val ≠ m+1 := by simpa only [Fin.ext_iff, Fin.val_last] using hil
      simp [complexNormalVector, Equiv.swap_apply_of_ne_of_ne hil hi0, hil, hi0, hiv0, hivl]

lemma complexNormalVector_coordinate_swaps (m : ℕ) (j : Fin (m+1)) (w : ℂ) :
    (fun i : Fin (m+2) => complexNormalVector m w
      ((Equiv.swap (Fin.last (m+1)) 0) ((Equiv.swap 0 j.castSucc) i))) =
      coordinateVector (m+1) (m+1) (fun k => if k = j then w else 0) 1 := by
  ext i
  rw [complexNormalVector_swap_last_zero]
  have hjl : j.castSucc ≠ Fin.last (m+1) := Fin.castSucc_ne_last j
  have h0l : (0 : Fin (m+2)) ≠ Fin.last (m+1) := by
    intro h
    have hh := congrArg Fin.val h
    simp at hh
  have hsLast : (Equiv.swap 0 j.castSucc) i = Fin.last (m+1) ↔ i = Fin.last (m+1) := by
    rw [Equiv.swap_apply_eq_iff]
    rw [Equiv.swap_apply_of_ne_of_ne h0l.symm hjl.symm]
  have hsZero : (Equiv.swap 0 j.castSucc) i = 0 ↔ i = j.castSucc := by
    rw [Equiv.swap_apply_eq_iff]
    simp
  simp only [hsLast, hsZero]
  by_cases hil : i = Fin.last (m+1)
  · subst i
    simp [coordinateVector]
  · have hi : i.val < m+1 := by
      have hilv : i.val ≠ m+1 := by simpa only [Fin.ext_iff, Fin.val_last] using hil
      omega
    by_cases hij : i = j.castSucc
    · subst i
      simp [coordinateVector, j.isLt]
    · have hij' : (⟨i.val,hi⟩ : Fin (m+1)) ≠ j := by
        intro he
        apply hij
        apply Fin.ext
        exact congrArg (fun k : Fin (m+1) => k.val) he
      simp [coordinateVector, hi, hij, hij', hil]

lemma complexProjectiveCoordinateLine_factor (m : ℕ) (j : Fin (m+1)) :
    complexProjectiveCoordinateLine (m+1) j =
      complexAffineLinePair ≫ projectiveCoordinateLinePair m j := by
  apply PairMap.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro w
  symm
  change mk
    (fun i : Fin (m+2) => complexNormalVector m w
      ((Equiv.swap (Fin.last (m+1)) 0) ((Equiv.swap 0 j.castSucc) i))) _ =
      mk (coordinateVector (m+1) (m+1) (fun k => if k = j then w else 0) 1) _
  congr 1
  exact complexNormalVector_coordinate_swaps m j w

lemma coordinateHyperplaneClass_complexLine (m : ℕ) (j : Fin (m+1)) :
    relativePullback ℤ (complexProjectiveCoordinateLine (m+1) j) 2
      (coordinateHyperplaneClass m j.castSucc) = positiveComplexLineCohomologyClass := by
  rw [complexProjectiveCoordinateLine_factor]
  change ((relativeCohomologyFunctor ℤ ℤ 2).map
      (complexAffineLinePair ≫ projectiveCoordinateLinePair m j).op)
      (coordinateHyperplaneClass m j.castSucc) = _
  rw [op_comp, CategoryTheory.Functor.map_comp]
  change relativePullback ℤ complexAffineLinePair 2
      (relativePullback ℤ (projectiveCoordinateLinePair m j) 2
        (coordinateHyperplaneClass m j.castSucc)) = _
  rw [coordinateHyperplaneClass_projectiveLine]
  rfl

lemma coordinateHyperplaneClass_complexLine_isGenerator (m : ℕ) (j : Fin (m+1)) :
    IsGenerator ℤ (relativePullback ℤ (complexProjectiveCoordinateLine (m+1) j) 2
      (coordinateHyperplaneClass m j.castSucc)) := by
  rw [coordinateHyperplaneClass_complexLine]
  exact positiveComplexLineCohomologyClass_isGenerator

end P202.ComplexProjectiveRing
end


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.CohomologyPairs P202Specs.CupProduct

/-- Standard subspace restrictions reduce primitivity of every power to the
top power in its own projective dimension. -/
lemma positiveDegreeTwo_primitivePowers_of_topPowers
    (htop : ∀ (i : ℕ) (C : CohomologyRing ℤ (projectiveSpace (i+1))),
      Function.Bijective (fun z : ℤ => z •
        homogeneousPower (i+1) C (positiveDegreeTwoClass i) (i+1)))
    (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace (m+1))) :
    PrimitivePowers (m+1) C (positiveDegreeTwoClass m) := by
  apply (primitivePowers_iff_homogeneousPower (m+1) C _).mpr
  intro i hi
  cases i with
  | zero => exact homogeneousPower_zero_primitive _ _ _
  | succ i =>
    let Cᵢ := (Classical.choice (P202.CupProduct.cohomologyRing ℤ)).ring (projectiveSpace (i+1))
    let f := hPullback ℤ (standardInclusion (m+1) (i+1) hi) (2*(i+1))
    have hf : Function.Bijective f := inclusion_cohomology_bijective _ _ hi _ le_rfl
    have hpow : f (homogeneousPower (m+1) C (positiveDegreeTwoClass m) (i+1)) =
        homogeneousPower (i+1) Cᵢ (positiveDegreeTwoClass i) (i+1) := by
      rw [homogeneousPower_pullback_any _ Cᵢ C,
        positiveDegreeTwoClass_restrict m i (by omega)]
    apply (Function.Bijective.of_comp_iff' hf _).mp
    have he : f ∘ (fun z : ℤ => z • homogeneousPower (m+1) C (positiveDegreeTwoClass m) (i+1)) =
        (fun z : ℤ => z • f (homogeneousPower (m+1) C (positiveDegreeTwoClass m) (i+1))) := by
      funext z
      exact map_zsmul f z _
    rw [he, hpow]
    exact htop i Cᵢ

lemma presentation_of_positiveDegreeTwo_topPowers
    (htop : ∀ (i : ℕ) (C : CohomologyRing ℤ (projectiveSpace (i+1))),
      Function.Bijective (fun z : ℤ => z •
        homogeneousPower (i+1) C (positiveDegreeTwoClass i) (i+1))) : presentation_type := by
  intro m C
  cases m with
  | zero => exact pointPresentation_with_powers C
  | succ m =>
    obtain ⟨e,he,hp⟩ := presentation_of_primitivePowers (m+1) C (positiveDegreeTwoClass m)
      (positiveDegreeTwo_primitivePowers_of_topPowers htop m C)
    exact ⟨positiveDegreeTwoClass m,e,he,hp⟩

/-- Once the top power is identified with the positive local image, every
restriction and both evaluations in the geometric statement follow. -/
lemma geometricGenerator_of_topPower_identifications
    (htop : ∀ (i : ℕ) (C : CohomologyRing ℤ (projectiveSpace (i+1))),
      homogeneousPower (i+1) C (positiveDegreeTwoClass i) (i+1) =
        ordinaryImage (P202Specs.LocalOrientation.localPair (Space (i+1)) (projectiveOrigin (i+1)))
          (2*(i+1)) (positiveLocalCohomologyClass (i+1))) : geometricGenerator_type := by
  intro m C
  cases m with
  | zero => exact ⟨0,pointGeometricGenerator C⟩
  | succ m =>
    refine ⟨positiveDegreeTwoClass m,
      geometricGenerator_of_positivePower_identifications (m+1) C _ (by intro h; omega) ?_ ?_⟩
    · intro k hk
      have hkm : k=m := by omega
      subst k
      obtain ⟨d,hd⟩ := hyperplaneThomData_exists m
      refine ⟨d,?_⟩
      cases hk
      rw [hd]
      exact (normalizedHyperplaneClass_ordinaryImage m).symm
    · intro i hpos hi
      cases i with
      | zero => omega
      | succ i =>
        let Cᵢ := (Classical.choice (P202.CupProduct.cohomologyRing ℤ)).ring (projectiveSpace (i+1))
        rw [homogeneousPower_pullback_any _ Cᵢ C,
          positiveDegreeTwoClass_restrict m i (by omega)]
        exact htop i Cᵢ

end P202.ComplexProjectiveRing
end


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Set Topology
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs P202Specs.CupProduct P202Specs.RelativeCupProduct

lemma coordinateHyperplaneClass_affine (m : ℕ) (j : Fin (m+1)) :
    relativePullback ℤ (complexAffineCoordinatePair (m+1) j) 2
      (coordinateHyperplaneClass m j.castSucc) =
    relativePullback ℤ (complexCoordinateProjection (m+1) j) 2
      positiveComplexLineCohomologyClass := by
  calc
    _ = relativePullback ℤ (complexCoordinateProjection (m+1) j) 2
        (relativePullback ℤ (complexProjectiveCoordinateLine (m+1) j) 2
          (coordinateHyperplaneClass m j.castSucc)) :=
      complexAffineCoordinate_class_projection (m+1) j 2 _
    _ = _ := congrArg (relativePullback ℤ (complexCoordinateProjection (m+1) j) 2)
      (coordinateHyperplaneClass_complexLine m j)

/-- The ordered positively oriented complex simplex in the punctured complex line pair. -/
def positiveComplexLineSimplex : P202Specs.SpheresDisks.simplexPair 2 ⟶ complexLinePair where
  map := TopCat.ofHom ⟨fun x => complexSimplexCoordinates 1 x 0,
    (continuous_apply 0).comp (complexSimplexCoordinates_continuous 1)⟩
  mapsTo := by
    intro x hx hz
    apply complexSimplexCoordinates_ne_zero_on_boundary 1 x hx
    ext j
    have hj : j = 0 := by apply Fin.ext; omega
    simpa [hj] using hz

lemma positiveLocalSimplex_complexLine_factor :
    positiveLocalSimplex 1 = positiveComplexLineSimplex ≫ complexAffineLinePair := by
  apply PairMap.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change affineChart 1 1 le_rfl (complexSimplexCoordinates 1 x) =
    affineChart 1 1 le_rfl (fun _ => complexSimplexCoordinates 1 x 0)
  congr 1
  ext j
  have hj : j = 0 := by apply Fin.ext; omega
  rw [hj]

lemma positiveComplexLineCohomologyClass_evaluation :
    relativeEvaluation _ 2 positiveComplexLineCohomologyClass
      (((relativeHomologyFunctor ℤ ℤ 2).map positiveComplexLineSimplex)
        (P202.SpheresDisks.affineClassLinear ℤ ℤ 2 1)) = 1 := by
  have hm : ((relativeHomologyFunctor ℤ ℤ 2).map complexAffineLinePair)
      (((relativeHomologyFunctor ℤ ℤ 2).map positiveComplexLineSimplex)
        (P202.SpheresDisks.affineClassLinear ℤ ℤ 2 1)) = positiveLocalClass 1 := by
    unfold positiveLocalClass
    rw [positiveLocalSimplex_complexLine_factor, CategoryTheory.Functor.map_comp]
    rfl
  calc
    _ = relativeEvaluation (localPair (Space 1) (projectiveOrigin 1)) 2
        (positiveLocalCohomologyClass 1)
        (((relativeHomologyFunctor ℤ ℤ 2).map complexAffineLinePair)
          (((relativeHomologyFunctor ℤ ℤ 2).map positiveComplexLineSimplex)
            (P202.SpheresDisks.affineClassLinear ℤ ℤ 2 1))) :=
      relativeEvaluation_pullback complexAffineLinePair 2 _ _
    _ = relativeEvaluation (localPair (Space 1) (projectiveOrigin 1)) 2
        (positiveLocalCohomologyClass 1) (positiveLocalClass 1) :=
      congrArg (relativeEvaluation _ 2 (positiveLocalCohomologyClass 1)) hm
    _ = 1 := positiveLocalCohomologyClass_evaluation 1

end P202.ComplexProjectiveRing
end

noncomputable section
namespace P202.ComplexProjectiveRing
open P202Specs.ComplexProjectiveRing

theorem hyperplaneThomClasses : hyperplaneThomClasses_type := by
  intro m
  obtain ⟨d, _⟩ := hyperplaneThomData_exists m
  exact ⟨d⟩

theorem lineGeometricGenerators : lineGeometricGenerators_type := by
  intro C
  exact ⟨positiveDegreeTwoClass 0, lineGeometricGenerator C⟩

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Set Topology
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
  P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
  P202Specs.RelativeCupProduct P202Specs.PrismHomotopy
  P202Specs.CupProduct P202Specs.SingularChains P202Specs.LocalOrientation
  P202Specs.TransverseThomProduct P202.TransverseThomProduct
/-- Coordinate hyperplanes with equal ordinary classes and primitive actual
transverse-line restrictions produce a primitive top cup power. -/
lemma topPower_primitive_of_coordinate_factors
    (μ : NaturalRelativeCupProduct.{0,0} ℤ) (k : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace (k+1)))
    (v : cohomology (k+1) 2)
    (c : ∀ j : Fin (k+1), HR ℤ (coordinateHyperplanePair (k+1) j.castSucc) 2)
    (hv : ∀ j : Fin (k+1), ordinaryImage (coordinateHyperplanePair (k+1) j.castSucc) 2 (c j) = v)
    (hc : ∀ j : Fin (k+1), Function.Bijective (fun r : ℤ => r •
      relativePullback ℤ (complexProjectiveCoordinateLine (k+1) j) 2 (c j))) :
    Function.Bijective (fun z : ℤ => z • homogeneousPower (k+1) C v (k+1)) := by
  letI := C.gradedRing
  let F := projectiveCoordinateFactor (k+1) c
  let A := orderedCup ℤ μ k F
  have hs : A.support = {projectiveOrigin (k+1)} := by
    change (orderedCup ℤ μ k F).support = _
    rw [orderedCup_support]
    exact firstCoordinateHyperplanes_intersection (k+1)
  have hd : A.degree = 2*(k+1) :=
    orderedCup_degree_eq_mul ℤ μ k 2 F (fun _ => rfl)
  have hp : supportedOrdinary ℤ A =
      (DirectSum.of (H ℤ (projectiveSpace (k+1))) 2 v)^(k+1) := by
    apply supportedOrdinary_orderedCup_eq_pow ℤ C μ k F
    intro j
    change DirectSum.of (H ℤ (projectiveSpace (k+1))) 2
      (ordinaryImage (coordinateHyperplanePair (k+1) j.castSucc) 2 (c j)) = _
    rw [hv j]
  let g : TopCat.of (Fin (k+1) → ℂ) ⟶ projectiveSpace (k+1) :=
    TopCat.ofHom ⟨affineChart (k+1) (k+1) le_rfl,
      affineChart_continuous (k+1) (k+1) le_rfl⟩
  let f : (⟨TopCat.of (Fin (k+1) → ℂ),(g ⁻¹' A.support)ᶜ⟩ : Pair) ⟶
      (⟨projectiveSpace (k+1),A.supportᶜ⟩ : Pair) := ⟨g, fun _ hz => hz⟩
  have hgen : IsGenerator ℤ (relativePullback ℤ f A.degree A.value) := by
    change Function.Bijective (fun z : ℤ => (inferInstance : Module ℤ _).smul z
      (supportedPullback ℤ g A).value)
    convert projectiveCoordinate_orderedCup_chart_generates μ k c hc using 1
    funext z
    exact Int.cast_smul_eq_zsmul ℤ z _
  exact topPower_primitive_of_supported_product (k+1) C v A hs hd hp f hgen

/-- The canonical positive degree-two class has primitive top power in every
positive projective dimension, for the given actual singular cup ring. -/
lemma positiveDegreeTwoClass_topPower_primitive (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace (m+1))) :
    Function.Bijective (fun z : ℤ =>
      z • homogeneousPower (m+1) C (positiveDegreeTwoClass m) (m+1)) := by
  obtain ⟨μ⟩ := P202.RelativeCupProduct.product.{0,0} ℤ
  apply topPower_primitive_of_coordinate_factors μ m C (positiveDegreeTwoClass m)
    (fun j => coordinateHyperplaneClass m j.castSucc)
    (fun j => coordinateHyperplaneClass_ordinaryImage m j.castSucc)
  intro j
  have h := coordinateHyperplaneClass_complexLine_isGenerator m j
  change Function.Bijective _ at h
  convert h using 1
  funext z
  exact (Int.cast_smul_eq_zsmul ℤ z _).symm

end P202.ComplexProjectiveRing

end

noncomputable section
namespace P202.ComplexProjectiveRing
open P202Specs.ComplexProjectiveRing

/-- The full graded ring presentation for every finite complex projective
space, including the actual singular cup multiplication and the point. -/
theorem presentation : presentation_type :=
  presentation_of_positiveDegreeTwo_topPowers positiveDegreeTwoClass_topPower_primitive

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Set Topology
namespace P202.ComplexProjectiveRing
open P202Specs.ComplexProjectiveRing P202Specs.RelativeSingularChains
  P202Specs.LocalOrientation P202Specs.PrismHomotopy P202Specs.SingularChains

/-- Positive diagonal reweighting of the barycentric coordinate differences. -/
def weightedSimplexCoordinates (n : ℕ) (wts : Fin (n+1) → ℝ)
    (x : P202.Cellular.StandardSimplex n) : Fin n → ℝ :=
  fun j => x.weights j.succ / wts j.succ - x.weights 0 / wts 0

lemma weightedSimplexCoordinates_continuous (n : ℕ) (wts : Fin (n+1) → ℝ) :
    Continuous (weightedSimplexCoordinates n wts) := by
  apply continuous_pi
  intro j
  exact ((Convexity.StdSimplex.continuous_weights_apply ℝ j.succ).div_const _).sub
    ((Convexity.StdSimplex.continuous_weights_apply ℝ 0).div_const _)

lemma weightedSimplexCoordinates_ne_zero_on_boundary (n : ℕ) (wts : Fin (n+1) → ℝ)
    (hwts : ∀ i, 0 < wts i) (x : P202.Cellular.StandardSimplex n)
    (hx : x ∈ (P202Specs.SpheresDisks.simplexPair n).subspace) :
    weightedSimplexCoordinates n wts x ≠ 0 := by
  intro hz
  have hr : ∀ i, x.weights i / wts i = x.weights 0 / wts 0 := by
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    exact sub_eq_zero.mp (congrFun hz j)
  obtain ⟨k,hk⟩ := hx
  have h0 : x.weights 0 / wts 0 = 0 := by
    rw [← hr k, hk, zero_div]
  have hw : x.weights = 0 := by
    ext i
    have hi := (div_eq_iff (ne_of_gt (hwts i))).mp ((hr i).trans h0)
    simpa using hi
  have ht := x.total
  simp [hw] at ht

def weightedPositiveRealLocalSimplex (n : ℕ) (wts : Fin (n+1) → ℝ) (hwts : ∀ i, 0 < wts i) :
    P202Specs.SpheresDisks.simplexPair n ⟶ localPair (Fin n → ℝ) 0 where
  map := TopCat.ofHom ⟨weightedSimplexCoordinates n wts, weightedSimplexCoordinates_continuous n wts⟩
  mapsTo := fun x hx => weightedSimplexCoordinates_ne_zero_on_boundary n wts hwts x hx

/-- Positive barycentric weights interpolate to the equal weights. -/
def simplexWeightInterpolation {n : ℕ} (wts : Fin (n+1) → ℝ) (t : unitInterval)
    (i : Fin (n+1)) : ℝ := (1-t.val) * wts i + t.val

lemma simplexWeightInterpolation_pos {n : ℕ} (wts : Fin (n+1) → ℝ)
    (hwts : ∀ i, 0 < wts i) (t : unitInterval) (i : Fin (n+1)) :
    0 < simplexWeightInterpolation wts t i := by
  dsimp [simplexWeightInterpolation]
  have hi := hwts i
  have ht0 := t.property.1
  have ht1 := t.property.2
  by_cases ht : t.val = 1
  · simp [ht]
  · have hp : 0 < 1-t.val := sub_pos.mpr (lt_of_le_of_ne ht1 ht)
    have hm : 0 < (1-t.val)*wts i := mul_pos hp hi
    linarith

lemma simplexWeightInterpolation_continuous {n : ℕ} (wts : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    Continuous (fun t : unitInterval => simplexWeightInterpolation wts t i) := by
  dsimp [simplexWeightInterpolation]
  fun_prop

/-- Every positive diagonal barycentric reweighting gives the same relative
orientation class, by a homotopy preserving the punctured subspace. -/
def weightedPositiveRealLocalSimplex_homotopy (n : ℕ) (wts : Fin (n+1) → ℝ)
    (hwts : ∀ i, 0 < wts i) :
    PairHomotopy (weightedPositiveRealLocalSimplex n wts hwts) (positiveRealLocalSimplex n) where
  homotopy := {
    toFun := fun p => weightedSimplexCoordinates n (simplexWeightInterpolation wts p.1) p.2
    continuous_toFun := by
      apply continuous_pi
      intro j
      exact (((Convexity.StdSimplex.continuous_weights_apply ℝ j.succ).comp continuous_snd).div
        ((simplexWeightInterpolation_continuous wts j.succ).comp continuous_fst)
        (fun p => ne_of_gt (simplexWeightInterpolation_pos wts hwts p.1 j.succ))).sub
        (((Convexity.StdSimplex.continuous_weights_apply ℝ 0).comp continuous_snd).div
          ((simplexWeightInterpolation_continuous wts 0).comp continuous_fst)
          (fun p => ne_of_gt (simplexWeightInterpolation_pos wts hwts p.1 0)))
    map_zero_left := by
      intro x
      change weightedSimplexCoordinates n (simplexWeightInterpolation wts 0) x =
        weightedSimplexCoordinates n wts x
      ext j
      simp [weightedSimplexCoordinates, simplexWeightInterpolation]
    map_one_left := by
      intro x
      change weightedSimplexCoordinates n (simplexWeightInterpolation wts 1) x =
        positiveSimplexCoordinates n x
      ext j
      simp [weightedSimplexCoordinates, simplexWeightInterpolation, positiveSimplexCoordinates]
  }
  preserves := by
    intro t x
    exact weightedSimplexCoordinates_ne_zero_on_boundary n (simplexWeightInterpolation wts t)
      (simplexWeightInterpolation_pos wts hwts t) x.val x.property

lemma weightedPositiveRealLocalSimplex_homology_eq (n : ℕ) (wts : Fin (n+1) → ℝ)
    (hwts : ∀ i, 0 < wts i) (j : ℤ) :
    (relativeHomologyFunctor ℤ ℤ j).map (weightedPositiveRealLocalSimplex n wts hwts) =
      (relativeHomologyFunctor ℤ ℤ j).map (positiveRealLocalSimplex n) :=
  (P202.PrismHomotopy.relativeHomology ℤ ℤ
    (weightedPositiveRealLocalSimplex_homotopy n wts hwts) j).1

/-- The horizontal factor on the reference shuffle cell. -/
def shuffleHorizontalWeights (q : ℕ) (i : Fin 3) : ℝ :=
  if i = 2 then (q+1 : ℕ) else 1

lemma shuffleHorizontalWeights_pos (q : ℕ) (i : Fin 3) :
    0 < shuffleHorizontalWeights q i := by
  dsimp [shuffleHorizontalWeights]
  split_ifs <;> positivity

def shuffleHorizontalSimplex (q : ℕ) :
    P202Specs.SpheresDisks.simplexPair 2 ⟶ localPair (Fin 2 → ℝ) 0 :=
  weightedPositiveRealLocalSimplex 2 (shuffleHorizontalWeights q) (shuffleHorizontalWeights_pos q)

lemma shuffleHorizontalSimplex_formula_zero (q : ℕ) (x : P202.Cellular.StandardSimplex 2) :
    (shuffleHorizontalSimplex q).map x 0 = x.weights 1 - x.weights 0 := by
  change weightedSimplexCoordinates 2 (shuffleHorizontalWeights q) x _ = _
  simp [weightedSimplexCoordinates, shuffleHorizontalWeights]

lemma shuffleHorizontalSimplex_formula_one (q : ℕ) (x : P202.Cellular.StandardSimplex 2) :
    (shuffleHorizontalSimplex q).map x 1 = x.weights 2 / (q+1 : ℕ) - x.weights 0 := by
  change weightedSimplexCoordinates 2 (shuffleHorizontalWeights q) x _ = _
  simp [weightedSimplexCoordinates, shuffleHorizontalWeights]

/-- The vertical factor on the reference shuffle cell. -/
def shuffleVerticalWeights (q : ℕ) (i : Fin (q+1)) : ℝ := if i = 0 then 3 else 1

lemma shuffleVerticalWeights_pos (q : ℕ) (i : Fin (q+1)) :
    0 < shuffleVerticalWeights q i := by
  dsimp [shuffleVerticalWeights]
  split_ifs <;> positivity

def shuffleVerticalSimplex (q : ℕ) :
    P202Specs.SpheresDisks.simplexPair q ⟶ localPair (Fin q → ℝ) 0 :=
  weightedPositiveRealLocalSimplex q (shuffleVerticalWeights q) (shuffleVerticalWeights_pos q)

lemma shuffleVerticalSimplex_formula (q : ℕ) (x : P202.Cellular.StandardSimplex q) (j : Fin q) :
    (shuffleVerticalSimplex q).map x j = x.weights j.succ - x.weights 0 / 3 := by
  change weightedSimplexCoordinates q (shuffleVerticalWeights q) x j = _
  simp [weightedSimplexCoordinates, shuffleVerticalWeights, Fin.succ_ne_zero]

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
namespace P202.ComplexProjectiveRing

lemma weightedSimplexCoordinates_injective (n : ℕ) (wts : Fin (n+1) → ℝ)
    (hwts : ∀ i, 0 < wts i) : Function.Injective (weightedSimplexCoordinates n wts) := by
  intro x y hxy
  let c := x.weights 0 / wts 0 - y.weights 0 / wts 0
  have hr : ∀ i, x.weights i / wts i - y.weights i / wts i = c := by
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    have h := congrFun hxy j
    dsimp [weightedSimplexCoordinates] at h
    dsimp [c]
    linarith
  have he : ∀ i, x.weights i - y.weights i = wts i * c := by
    intro i
    have hi : (x.weights i-y.weights i) / wts i = c := by rw [sub_div]; exact hr i
    exact ((div_eq_iff (ne_of_gt (hwts i))).mp hi).trans (mul_comm _ _)
  have hs : (∑ i, wts i) * c = 0 := by
    rw [Finset.sum_mul]
    simp_rw [← he]
    rw [Finset.sum_sub_distrib, x.total_of_fintype, y.total_of_fintype, sub_self]
  have hp : 0 < ∑ i, wts i :=
    Finset.sum_pos (fun i _ => hwts i) Finset.univ_nonempty
  have hc : c = 0 := (mul_eq_zero.mp hs).resolve_left hp.ne'
  apply Convexity.StdSimplex.ext
  ext i
  have hi := he i
  rw [hc,mul_zero] at hi
  exact sub_eq_zero.mp hi

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
open CategoryTheory Set
namespace P202.ComplexProjectiveRing
open P202Specs.ShuffleModel

/-- Interior points of the genuine affine shuffle triangulation belong to
exactly one shuffle cell. This retains the same original singular shuffles. -/
lemma shuffle_interior_unique {p q : ℕ} (s t : LatticePath p q)
    (x y : StdSimplex (p+q)) (hx : ∀ k, 0 < weights x k)
    (h : parametrization s x = parametrization t y) : s=t := by
  have hxy := P202.ShuffleTriangulation.same_barycentric_coordinates s t x y h
  subst y
  have hv (k : Fin (p+q+1)) : vertex s k = vertex t k :=
    P202.ShuffleTriangulation.positive_weight_vertex_eq s t x h k (hx k)
  apply Subtype.ext
  apply Prod.ext
  · apply DFunLike.ext
    intro k
    apply Convexity.StdSimplex.single_injective (R := ℝ)
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro j
    exact congrFun (congrArg Prod.fst (hv k)) j
  · apply DFunLike.ext
    intro k
    apply Convexity.StdSimplex.single_injective (R := ℝ)
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro j
    exact congrFun (congrArg Prod.snd (hv k)) j

lemma shuffle_barycenter_unique {p q : ℕ} (s t : LatticePath p q)
    (y : StdSimplex (p+q))
    (h : parametrization s Convexity.StdSimplex.barycenter = parametrization t y) : s=t := by
  apply shuffle_interior_unique s t _ y _ h
  intro k
  rw [weights,Convexity.StdSimplex.weights_barycenter_apply]
  positivity

/-- The reference shuffle with all horizontal edges followed by all vertical
edges, whose shuffle coefficient is positive one. -/
def horizontalThenVertical (p q : ℕ) : LatticePath p q :=
  ⟨(⟨fun k => ⟨min k.val p, by omega⟩, by
      intro k l h
      exact min_le_min_right p h⟩,
    ⟨fun k => ⟨k.val-p, by omega⟩, by
      intro k l h
      exact Nat.sub_le_sub_right h p⟩), by
    intro k
    change min k.val p + (k.val-p) = k.val
    omega⟩

lemma horizontalThenVertical_stepLabel (p q : ℕ) (k : Fin (p+q)) :
    (horizontalThenVertical p q).stepLabel k = k := by
  apply Fin.ext
  unfold LatticePath.stepLabel
  split
  · rename_i hh
    change min k.val p = k.val
    change min (k.val+1) p = min k.val p+1 at hh
    omega
  · rename_i hh
    change p+(k.val-p)=k.val
    change ¬ min (k.val+1) p = min k.val p+1 at hh
    omega

lemma horizontalThenVertical_sign (p q : ℕ) : (horizontalThenVertical p q).sign=1 := by
  have he : (horizontalThenVertical p q).permutation = Equiv.refl _ := by
    apply Equiv.ext
    intro k
    change (horizontalThenVertical p q).stepLabel k = k
    exact horizontalThenVertical_stepLabel p q k
  simp [LatticePath.sign,he]

end P202.ComplexProjectiveRing

namespace P202.ComplexProjectiveRing
open P202Specs.ShuffleModel
/-- After injective coordinate maps in the two factors, the image of the
reference cell's barycenter is missed by every other shuffle simplex. -/
lemma otherShuffle_avoids_barycenter_image {p q : ℕ} (s t : LatticePath p q)
    (hst : t≠s) {X Y : Type*} (f : StdSimplex p → X) (g : StdSimplex q → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (x : StdSimplex (p+q)) :
    (f (parametrization t x).1,g (parametrization t x).2) ≠
      (f (parametrization s Convexity.StdSimplex.barycenter).1,
       g (parametrization s Convexity.StdSimplex.barycenter).2) := by
  intro he
  have hpar : parametrization s Convexity.StdSimplex.barycenter = parametrization t x := by
    apply Prod.ext
    · exact (hf (congrArg Prod.fst he)).symm
    · exact (hg (congrArg Prod.snd he)).symm
  exact hst (shuffle_barycenter_unique s t x hpar).symm
end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
namespace P202.ComplexProjectiveRing

/-- Linear interpolation from the positive ordered coordinates to the centered
reference `(2,q)` shuffle cell. The first two coordinates form the first block. -/
def positiveShuffleInterpolation (q : ℕ) (t : ℝ) (x : Fin (2+q) → ℝ) : Fin (2+q) → ℝ :=
  Fin.append
    (fun j : Fin 2 => if j=0 then x (Fin.castAdd q 0) else
      (1-t)*x (Fin.castAdd q 1) +
        t/((q : ℝ)+1)*(x (Fin.castAdd q 1) + ∑ j : Fin q, x (Fin.natAdd 2 j)))
    (fun j : Fin q => x (Fin.natAdd 2 j) - t/3*(x (Fin.castAdd q 0)+x (Fin.castAdd q 1)))

lemma positiveShuffleInterpolation_zero (q : ℕ) (x : Fin (2+q) → ℝ) :
    positiveShuffleInterpolation q 0 x = x := by
  ext j
  refine Fin.addCases ?_ ?_ j
  · intro j
    fin_cases j <;> simp [positiveShuffleInterpolation]
  · intro j
    simp [positiveShuffleInterpolation]

/-- Every intermediate matrix is injective: its Schur coefficient is a
strictly positive scalar. This supplies an actual local-pair homotopy rather
than relying on a determinant/degree theorem that is absent from the library. -/
lemma positiveShuffleInterpolation_eq_zero (q : ℕ) (t : ℝ)
    (ht0 : 0≤t) (ht1 : t≤1) (x : Fin (2+q) → ℝ)
    (h : positiveShuffleInterpolation q t x = 0) : x=0 := by
  have h0 := congrFun h (Fin.castAdd q (0 : Fin 2))
  have h1 := congrFun h (Fin.castAdd q (1 : Fin 2))
  have hv (j : Fin q) := congrFun h (Fin.natAdd 2 j)
  simp [positiveShuffleInterpolation] at h0
  simp only [positiveShuffleInterpolation, Fin.append_left, show (1 : Fin 2)≠0 by decide,
    ite_false, Pi.zero_apply] at h1
  have hval (j : Fin q) : x (Fin.natAdd 2 j) = t/3*x (Fin.castAdd q 1) := by
    have hj := hv j
    simp only [positiveShuffleInterpolation, Fin.append_right, Pi.zero_apply, h0, zero_add] at hj
    linarith
  have hs : (∑ j : Fin q, x (Fin.natAdd 2 j)) = (q : ℝ)*(t/3*x (Fin.castAdd q 1)) := by
    simp_rw [hval]
    simp
  have hd : 0<(q : ℝ)+1 := by positivity
  have ha : 0<1-t+t/((q : ℝ)+1) := by
    rcases lt_or_eq_of_le ht1 with ht | rfl
    · exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht) (div_nonneg ht0 hd.le)
    · simp only [sub_self,zero_add]
      positivity
  have hb : 0≤t/((q : ℝ)+1)*((q : ℝ)*t/3) := by positivity
  have hp : (1-t+t/((q : ℝ)+1)+t/((q : ℝ)+1)*((q : ℝ)*t/3))*x (Fin.castAdd q 1)=0 := by
    rw [hs] at h1
    nlinarith [h1]
  have hx1 : x (Fin.castAdd q 1)=0 :=
    (mul_eq_zero.mp hp).resolve_left (add_pos_of_pos_of_nonneg ha hb).ne'
  ext j
  refine Fin.addCases ?_ ?_ j
  · intro j
    fin_cases j
    · exact h0
    · exact hx1
  · intro j
    simp only [hval,hx1,mul_zero,Pi.zero_apply]

lemma positiveShuffleInterpolation_ne_zero (q : ℕ) (t : ℝ)
    (ht0 : 0≤t) (ht1 : t≤1) (x : Fin (2+q) → ℝ) (hx : x≠0) :
    positiveShuffleInterpolation q t x ≠ 0 :=
  fun h => hx (positiveShuffleInterpolation_eq_zero q t ht0 ht1 x h)

end P202.ComplexProjectiveRing

open CategoryTheory
namespace P202.ComplexProjectiveRing
open P202Specs.RelativeSingularChains P202Specs.LocalOrientation P202Specs.ComplexProjectiveRing
lemma positiveShuffleInterpolation_continuous (q : ℕ) :
    Continuous (fun tx : ℝ × (Fin (2+q) → ℝ) => positiveShuffleInterpolation q tx.1 tx.2) := by
  apply continuous_pi
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro j
    by_cases hj : j=0
    · simp only [positiveShuffleInterpolation, Fin.append_left, hj, ite_true]
      fun_prop
    · simp only [positiveShuffleInterpolation, Fin.append_left, hj, ite_false]
      fun_prop
  · intro j
    simp only [positiveShuffleInterpolation, Fin.append_right]
    fun_prop

def centeredReferenceSimplex (q : ℕ) : P202Specs.SpheresDisks.simplexPair (2+q) ⟶
    localPair (Fin (2+q) → ℝ) 0 where
  map := TopCat.ofHom ⟨fun x => positiveShuffleInterpolation q 1 (positiveSimplexCoordinates (2+q) x),
    (positiveShuffleInterpolation_continuous q).comp
      (continuous_const.prodMk (positiveSimplexCoordinates_continuous (2+q)))⟩
  mapsTo := fun x hx => positiveShuffleInterpolation_ne_zero q 1 (by norm_num) le_rfl
    (positiveSimplexCoordinates (2+q) x) (positiveSimplexCoordinates_ne_zero_on_boundary (2+q) x hx)

/-- The centered reference shuffle simplex has exactly the same local integral
class as the explicit positive ordered simplex, by an actual boundary-preserving
homotopy through the injective linear interpolation. -/
def positiveReferenceSimplexHomotopy (q : ℕ) : P202Specs.PrismHomotopy.PairHomotopy
    (positiveRealLocalSimplex (2+q)) (centeredReferenceSimplex q) where
  homotopy := {
    toFun := fun tx => positiveShuffleInterpolation q tx.1.val (positiveSimplexCoordinates (2+q) tx.2)
    continuous_toFun := (positiveShuffleInterpolation_continuous q).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        ((positiveSimplexCoordinates_continuous (2+q)).comp continuous_snd))
    map_zero_left := by intro x; exact positiveShuffleInterpolation_zero q _
    map_one_left := by intro x; rfl }
  preserves := fun t x => positiveShuffleInterpolation_ne_zero q t.val t.property.1 t.property.2
    (positiveSimplexCoordinates (2+q) x.val)
    (positiveSimplexCoordinates_ne_zero_on_boundary (2+q) x.val x.property)

end P202.ComplexProjectiveRing

namespace P202.ComplexProjectiveRing
open P202Specs.RelativeSingularChains
lemma centeredReferenceSimplex_homology_eq (q : ℕ) (j : ℤ) :
    (relativeHomologyFunctor ℤ ℤ j).map (centeredReferenceSimplex q) =
      (relativeHomologyFunctor ℤ ℤ j).map (positiveRealLocalSimplex (2+q)) :=
  ((P202.PrismHomotopy.relativeHomology ℤ ℤ (positiveReferenceSimplexHomotopy q) j).1).symm
end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.CohomologyPairs P202Specs.CupProduct
open P202Specs.RelativeSingularChains P202Specs.LocalOrientation

/-- Every witness with the prescribed complex positive slice has the same
actual relative hyperplane Thom class, independently of auxiliary charts. -/
lemma hyperplaneThomData_thom_eq {m : ℕ} (d : HyperplaneThomData m) :
    d.thom = normalizedHyperplaneClass m := by
  have hs : d.positiveSlice = positiveHyperplaneSlice m := by
    apply PairMap.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact d.positiveSlice_formula
  have hd : relativeEvaluation _ 2 d.thom (positiveHyperplaneClass m) = 1 := by
    have he := d.complex_normal_positive
    rw [hs] at he
    unfold positiveHyperplaneClass
    rw [P202.SpheresDisks.affineClassLinear_apply]
    exact he
  obtain ⟨z,hz⟩ := (normalizedHyperplaneClass_isGenerator m).surjective d.thom
  have hz' : z • normalizedHyperplaneClass m = d.thom :=
    (Int.cast_smul_eq_zsmul ℤ z (normalizedHyperplaneClass m)).symm.trans hz
  let χ := ((LinearMap.applyₗ (R := ℤ) (positiveHyperplaneClass m)).comp
    (relativeEvaluation (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)) 2)).toAddMonoidHom
  have hχ : χ (normalizedHyperplaneClass m) = 1 := normalizedHyperplaneClass_evaluation m
  have hχd : χ d.thom = 1 := hd
  have hval := congrArg χ hz'
  rw [map_zsmul, hχ, hχd, zsmul_eq_mul, mul_one] at hval
  have hz1 : z = 1 := hval
  subst z
  simpa only [one_zsmul] using hz'.symm

lemma hyperplaneThomData_ordinaryImage {m : ℕ} (d : HyperplaneThomData m) :
    ordinaryImage (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)) 2 d.thom =
      positiveDegreeTwoClass m := by
  rw [hyperplaneThomData_thom_eq, normalizedHyperplaneClass_ordinaryImage]

/-- The full algebraic presentation can be given by the ordinary image of
every normalized complex-normal hyperplane Thom witness. -/
lemma hyperplanePresentation (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace (m+1))) (d : HyperplaneThomData m) :
    letI := C.gradedRing
    ∃ e : truncatedPolynomial (m+1) ≃+* totalCohomology (m+1),
      e (polynomialClass (m+1) Polynomial.X) =
        DirectSum.of (H ℤ (projectiveSpace (m+1))) 2
          (ordinaryImage (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)) 2 d.thom) ∧
      ∀ i : ℕ, i ≤ m+1 → ∃ b : cohomology (m+1) (2*i),
        Function.Bijective (fun z : ℤ => z • b) ∧
        e ((polynomialClass (m+1) Polynomial.X)^i) =
          DirectSum.of (H ℤ (projectiveSpace (m+1))) (2*i) b := by
  rw [hyperplaneThomData_ordinaryImage]
  exact presentation_of_primitivePowers (m+1) C (positiveDegreeTwoClass m)
    (positiveDegreeTwo_primitivePowers_of_topPowers positiveDegreeTwoClass_topPower_primitive m C)

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial
universe u w
namespace P202.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202Specs.ShuffleModel P202.TransverseThomProduct
variable (R : Type u) [CommRing R]

/-- A singular simplex entirely in the designated subspace has zero image in
the actual integer-indexed relative singular chain complex. -/
lemma relativeChainProjection_single_zero (P : Pair.{w}) (n : ℕ) (s : Simplex P.space n)
    (hs : InSubspace P n s) (r : R) :
    relativeChainProjection R P n (Finsupp.single s r) = 0 := by
  apply (relativeChainProjection_eq_zero_iff R P n _).mpr
  let ss : Simplex P.sub n := (simplexEquiv P.sub n).symm
    ⟨fun x => ⟨simplexEquiv P.space n s x,hs x⟩,
      (simplexEquiv P.space n s).continuous.subtype_mk _⟩
  refine ⟨Finsupp.single ss r,?_⟩
  rw [P202.SingularChains.chainMap_single]
  apply congrArg (fun t : Simplex P.space n => Finsupp.single t r)
  apply (simplexEquiv P.space n).injective
  rw [P202.SingularChains.simplexEquiv_postcomp]
  ext x
  rfl

/-- Only the one shuffle simplex containing the support point survives in the
actual local relative chain quotient. All other terms vanish there, so no
orientation determinant is used as an unproved homology comparison. -/
lemma relativeChainProjection_shuffle_eq {X Y : TopCat.{w}} {p q : ℕ}
    (A : Set (P202Specs.AlexanderWhitney.productSpace X Y))
    (σ : Simplex X p) (τ : Simplex Y q) (s₀ : LatticePath p q)
    (havoid : ∀ s : LatticePath p q, s≠s₀ →
      InSubspace (⟨P202Specs.AlexanderWhitney.productSpace X Y,A⟩ : Pair.{w}) (p+q)
        (shuffleSimplex s σ τ)) :
    relativeChainProjection R (⟨P202Specs.AlexanderWhitney.productSpace X Y,A⟩ : Pair.{w}) (p+q)
      (shuffleGenerator R σ τ) =
      s₀.sign • relativeChainProjection R
        (⟨P202Specs.AlexanderWhitney.productSpace X Y,A⟩ : Pair.{w}) (p+q)
        (Finsupp.single (shuffleSimplex s₀ σ τ) 1) := by
  rw [shuffleGenerator,map_sum]
  simp_rw [map_zsmul]
  apply Finset.sum_eq_single s₀
  · intro s hs hne
    rw [relativeChainProjection_single_zero R _ _ _ (havoid s hne),smul_zero]
  · intro hnone
    exact (hnone (Finset.mem_univ s₀)).elim

/-- The reference shuffle has coefficient +1; its surviving relative chain is
therefore the entire localized shuffle chain, with its sign retained. -/
lemma relativeChainProjection_shuffle_eq_of_sign_one {X Y : TopCat.{w}} {p q : ℕ}
    (A : Set (P202Specs.AlexanderWhitney.productSpace X Y))
    (σ : Simplex X p) (τ : Simplex Y q) (s₀ : LatticePath p q) (hpos : s₀.sign=1)
    (havoid : ∀ s : LatticePath p q, s≠s₀ →
      InSubspace (⟨P202Specs.AlexanderWhitney.productSpace X Y,A⟩ : Pair.{w}) (p+q)
        (shuffleSimplex s σ τ)) :
    relativeChainProjection R (⟨P202Specs.AlexanderWhitney.productSpace X Y,A⟩ : Pair.{w}) (p+q)
      (shuffleGenerator R σ τ) =
      relativeChainProjection R
        (⟨P202Specs.AlexanderWhitney.productSpace X Y,A⟩ : Pair.{w}) (p+q)
        (Finsupp.single (shuffleSimplex s₀ σ τ) 1) := by
  rw [relativeChainProjection_shuffle_eq R A σ τ s₀ havoid,hpos,one_smul]

end P202.ComplexProjectiveRing

namespace P202.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.ShuffleModel
open P202.TransverseThomProduct
variable (R : Type u) [CommRing R]

/-- Actual singular shuffles localized at the image of an interior reference
barycenter have exactly one surviving term. -/
lemma relativeChainProjection_shuffle_at_barycenter {X Y : TopCat.{w}} {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) (s₀ : LatticePath p q) (hpos : s₀.sign=1)
    (hσ : Function.Injective (simplexEquiv X p σ))
    (hτ : Function.Injective (simplexEquiv Y q τ))
    (z₀ : P202Specs.AlexanderWhitney.productSpace X Y)
    (hcenter :
      (simplexEquiv X p σ (parametrization s₀ Convexity.StdSimplex.barycenter).1,
       simplexEquiv Y q τ (parametrization s₀ Convexity.StdSimplex.barycenter).2) = z₀) :
    relativeChainProjection R
      (⟨P202Specs.AlexanderWhitney.productSpace X Y,{z | z≠z₀}⟩ : Pair.{w}) (p+q)
      (shuffleGenerator R σ τ) =
      relativeChainProjection R
        (⟨P202Specs.AlexanderWhitney.productSpace X Y,{z | z≠z₀}⟩ : Pair.{w}) (p+q)
        (Finsupp.single (shuffleSimplex s₀ σ τ) 1) := by
  apply relativeChainProjection_shuffle_eq_of_sign_one R _ σ τ s₀ hpos
  intro s hs x
  change simplexEquiv (P202Specs.AlexanderWhitney.productSpace X Y) (p+q)
    (shuffleSimplex s σ τ) x ≠ z₀
  rw [P202.ShuffleModel.simplex_formula]
  rw [← hcenter]
  exact otherShuffle_avoids_barycenter_image s₀ s hs
    (simplexEquiv X p σ) (simplexEquiv Y q τ) hσ hτ x

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
universe u w
open CategoryTheory Opposite

namespace P202.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.ShuffleModel
open P202Specs.TransverseThomProduct P202.TransverseThomProduct
variable (R : Type u) [CommRing R]

/-- The same localization directly in the external relative cup product's
original union-of-two-faces pair, without changing its support object. -/
lemma relativeChainProjection_shuffle_productFaces {X Y : TopCat.{w}} {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) (s₀ : LatticePath p q) (hpos : s₀.sign=1)
    (hσ : Function.Injective (simplexEquiv X p σ))
    (hτ : Function.Injective (simplexEquiv Y q τ)) (x₀ : X) (y₀ : Y)
    (hcenter :
      (simplexEquiv X p σ (parametrization s₀ Convexity.StdSimplex.barycenter).1,
       simplexEquiv Y q τ (parametrization s₀ Convexity.StdSimplex.barycenter).2) = (x₀,y₀)) :
    relativeChainProjection R (productSubspaces X Y {x | x≠x₀} {y | y≠y₀}).unionPair (p+q)
      (shuffleGenerator R σ τ) =
      relativeChainProjection R (productSubspaces X Y {x | x≠x₀} {y | y≠y₀}).unionPair (p+q)
        (Finsupp.single (shuffleSimplex s₀ σ τ) 1) := by
  apply relativeChainProjection_shuffle_eq_of_sign_one R _ σ τ s₀ hpos
  intro s hs x
  rw [P202.ShuffleModel.simplex_formula]
  change simplexEquiv X p σ (parametrization s x).1 ≠ x₀ ∨
    simplexEquiv Y q τ (parametrization s x).2 ≠ y₀
  by_contra hzero
  push_neg at hzero
  have he : (simplexEquiv X p σ (parametrization s x).1,
      simplexEquiv Y q τ (parametrization s x).2) = (x₀,y₀) := Prod.ext hzero.1 hzero.2
  exact otherShuffle_avoids_barycenter_image s₀ s hs
    (simplexEquiv X p σ) (simplexEquiv Y q τ) hσ hτ x (he.trans hcenter.symm)
end P202.ComplexProjectiveRing

end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Set
namespace P202.ComplexProjectiveRing
open P202Specs.ShuffleModel P202Specs.ComplexProjectiveRing

lemma horizontalThenVertical_horizontal_zero (q : ℕ) (x : StdSimplex (2+q)) :
    (parametrization (horizontalThenVertical 2 q) x).1.weights 0 = x.weights 0 := by
  change weights (x.map (horizontalThenVertical 2 q).horizontal) 0 = _
  rw [← P202.ShuffleModel.ambientMap_weights]
  unfold ambientMap
  have hh (k : Fin (2+q+1)) : (horizontalThenVertical 2 q).horizontal k = 0 ↔ k = 0 := by
    change (⟨min k.val 2, _⟩ : Fin 3) = 0 ↔ k = 0
    simp only [Fin.ext_iff, Fin.val_zero]
    omega
  simp_rw [hh]
  rw [Finset.sum_filter]
  simp [weights]

lemma horizontalThenVertical_horizontal_one (q : ℕ) (x : StdSimplex (2+q)) :
    (parametrization (horizontalThenVertical 2 q) x).1.weights 1 = x.weights 1 := by
  change weights (x.map (horizontalThenVertical 2 q).horizontal) 1 = _
  rw [← P202.ShuffleModel.ambientMap_weights]
  unfold ambientMap
  have hh (k : Fin (2+q+1)) : (horizontalThenVertical 2 q).horizontal k = 1 ↔ k = 1 := by
    change (⟨min k.val 2, _⟩ : Fin 3) = 1 ↔ k = 1
    simp only [Fin.ext_iff]
    change min k.val 2 = 1 ↔ k.val = (1 : Fin (2+q+1)).val
    rw [show (1 : Fin (2+q+1)).val = 1 by
      simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1<2+q+1)]]
    omega
  simp_rw [hh]
  rw [Finset.sum_filter]
  simp [weights]

lemma horizontalThenVertical_vertical_succ (q : ℕ) (x : StdSimplex (2+q)) (j : Fin q) :
    (parametrization (horizontalThenVertical 2 q) x).2.weights j.succ =
      x.weights ⟨j.val+3,by omega⟩ := by
  change weights (x.map (horizontalThenVertical 2 q).vertical) j.succ = _
  rw [← P202.ShuffleModel.ambientMap_weights]
  unfold ambientMap
  have hh (k : Fin (2+q+1)) : (horizontalThenVertical 2 q).vertical k = j.succ ↔
      k = ⟨j.val+3,by omega⟩ := by
    change (⟨k.val-2, _⟩ : Fin (q+1)) = j.succ ↔ _
    simp only [Fin.ext_iff, Fin.val_succ, Fin.val_mk]
    omega
  simp_rw [hh]
  rw [Finset.sum_filter]
  simp [weights]

lemma horizontalThenVertical_vertical_zero (q : ℕ) (x : StdSimplex (2+q)) :
    (parametrization (horizontalThenVertical 2 q) x).2.weights 0 =
      x.weights 0 + x.weights 1 + x.weights 2 := by
  change weights (x.map (horizontalThenVertical 2 q).vertical) 0 = _
  rw [← P202.ShuffleModel.ambientMap_weights]
  unfold ambientMap
  have hh : Finset.univ.filter (fun k : Fin (2+q+1) => (horizontalThenVertical 2 q).vertical k = 0) =
      {0,1,2} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    change k.val-2=0 ↔ _
    have hk0 : (0 : Fin (2+q+1)).val = 0 := rfl
    have hk1 : (1 : Fin (2+q+1)).val = 1 := by simp
    have hk2 : (2 : Fin (2+q+1)).val = 2 := by simp [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 2<2+q+1)]
    rw [hk0,hk1,hk2]
    omega
  rw [hh]
  have hk1 : (1 : Fin (2+q+1)).val = 1 := by
    simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1<2+q+1)]
  have hk2 : (2 : Fin (2+q+1)).val = 2 := by
    simp [Nat.mod_eq_of_lt (by omega : 2<2+q+1)]
  rw [Finset.sum_insert (by simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 1<2+q+1),
      Nat.mod_eq_of_lt (by omega : 2<2+q+1)]),
    Finset.sum_insert (by simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 1<2+q+1),
      Nat.mod_eq_of_lt (by omega : 2<2+q+1)]), Finset.sum_singleton]
  dsimp [weights]
  ring

lemma shuffleWeighted_reference_formula (q : ℕ) (x : StdSimplex (2+q)) :
    Fin.append
      ((shuffleHorizontalSimplex q).map (parametrization (horizontalThenVertical 2 q) x).1)
      ((shuffleVerticalSimplex q).map (parametrization (horizontalThenVertical 2 q) x).2) =
      positiveShuffleInterpolation q 1 (positiveSimplexCoordinates (2+q) x) := by
  let z := parametrization (horizontalThenVertical 2 q) x
  have h0 := horizontalThenVertical_horizontal_zero q x
  have h1 := horizontalThenVertical_horizontal_one q x
  have hv0 := horizontalThenVertical_vertical_zero q x
  have hv := horizontalThenVertical_vertical_succ q x
  have htot : z.1.weights 0 + z.1.weights 1 + z.1.weights 2 = 1 := by
    have ht := z.1.total_of_fintype
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_empty, add_zero] at ht
    change z.1.weights 0 + (z.1.weights 1 + z.1.weights 2) = 1 at ht
    linarith
  have htail : (∑ j : Fin q, x.weights ⟨j.val+3,by omega⟩) =
      1 - (x.weights 0 + x.weights 1 + x.weights 2) := by
    have ht := z.2.total_of_fintype
    rw [Fin.sum_univ_succ] at ht
    change z.2.weights 0 + (∑ j : Fin q, z.2.weights j.succ) = 1 at ht
    simp only [z, horizontalThenVertical_vertical_zero, horizontalThenVertical_vertical_succ] at ht
    linarith
  have he0 : (Fin.castAdd q (0 : Fin 2)).succ = (1 : Fin (2+q+1)) := by
    apply Fin.ext
    simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1<2+q+1)]
  have he1 : (Fin.castAdd q (1 : Fin 2)).succ = (2 : Fin (2+q+1)) := by
    apply Fin.ext
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 2<2+q+1)]
  have hev (j : Fin q) : (Fin.natAdd 2 j).succ = (⟨j.val+3,by omega⟩ : Fin (2+q+1)) := by
    apply Fin.ext
    simp
    omega
  have hA0 (u : Fin (2+q) → ℝ) : positiveShuffleInterpolation q 1 u (Fin.castAdd q 0) =
      u (Fin.castAdd q 0) := by simp [positiveShuffleInterpolation]
  have hA1 (u : Fin (2+q) → ℝ) : positiveShuffleInterpolation q 1 u (Fin.castAdd q 1) =
      1/((q : ℝ)+1) * (u (Fin.castAdd q 1) + ∑ j : Fin q, u (Fin.natAdd 2 j)) := by
    simp [positiveShuffleInterpolation]
  have hAv (u : Fin (2+q) → ℝ) (j : Fin q) :
      positiveShuffleInterpolation q 1 u (Fin.natAdd 2 j) =
        u (Fin.natAdd 2 j) - 1/3*(u (Fin.castAdd q 0)+u (Fin.castAdd q 1)) := by
    simp [positiveShuffleInterpolation]
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro k
    fin_cases k
    · rw [Fin.append_left]
      change (shuffleHorizontalSimplex q).map z.1 (0 : Fin 2) =
        positiveShuffleInterpolation q 1 (positiveSimplexCoordinates (2+q) x) (Fin.castAdd q 0)
      rw [shuffleHorizontalSimplex_formula_zero,hA0]
      change z.1.weights 1 - z.1.weights 0 =
        x.weights (Fin.castAdd q (0 : Fin 2)).succ - x.weights 0
      rw [he0]
      exact congrArg₂ (fun a b : ℝ => a-b) h1 h0
    · rw [Fin.append_left]
      change (shuffleHorizontalSimplex q).map z.1 (1 : Fin 2) =
        positiveShuffleInterpolation q 1 (positiveSimplexCoordinates (2+q) x) (Fin.castAdd q 1)
      rw [shuffleHorizontalSimplex_formula_one,hA1]
      simp only [positiveSimplexCoordinates,he1]
      have hsum : (∑ j : Fin q,
          (x.weights (Fin.natAdd 2 j).succ - x.weights 0)) =
          1 - (x.weights 0+x.weights 1+x.weights 2) - (q : ℝ)*x.weights 0 := by
        rw [Finset.sum_sub_distrib]
        simp_rw [hev]
        rw [htail]
        simp
      rw [hsum]
      have hd : (q : ℝ)+1 ≠ 0 := by positivity
      have h01 : z.1.weights 2 = 1-x.weights 0-x.weights 1 := by
        change z.1.weights 0 = x.weights 0 at h0
        change z.1.weights 1 = x.weights 1 at h1
        linarith
      rw [h01]
      change z.1.weights 0 = x.weights 0 at h0
      rw [h0]
      push_cast
      field_simp
      ring
  · intro j
    rw [Fin.append_right,hAv]
    change (shuffleVerticalSimplex q).map z.2 j =
      (x.weights (Fin.natAdd 2 j).succ - x.weights 0) -
        1/3*((x.weights (Fin.castAdd q (0 : Fin 2)).succ - x.weights 0)+
          (x.weights (Fin.castAdd q (1 : Fin 2)).succ - x.weights 0))
    rw [shuffleVerticalSimplex_formula, he0, he1, hev]
    have hvj : z.2.weights j.succ = x.weights ⟨j.val+3,by omega⟩ := hv j
    change z.2.weights 0 = x.weights 0+x.weights 1+x.weights 2 at hv0
    rw [hvj,hv0]
    ring

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.CohomologyPairs P202Specs.CupProduct
open P202Specs.RelativeSingularChains P202Specs.RelativeCupProduct
  P202Specs.TransverseThomProduct P202Specs.LocalOrientation

/-- The exact positive-simplex evaluation of a point-supported relative
product supplies the remaining geometric top-power identification. -/
lemma topPower_eq_positiveImage_of_supported_value (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)) (v : cohomology m 2)
    (A : SupportedClass ℤ (projectiveSpace m))
    (hs : A.support = {projectiveOrigin m}) (hd : A.degree = 2*m)
    (hp : letI := C.gradedRing
      supportedOrdinary ℤ A = (DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^m)
    (f : P202Specs.SpheresDisks.simplexPair (2*m) ⟶
      (⟨projectiveSpace m,A.supportᶜ⟩ : Pair))
    (hf : ∀ x, f.map x = positiveProjectiveSimplex m x)
    (hvalue : relativeEvaluation (⟨projectiveSpace m,A.supportᶜ⟩ : Pair) (2*m)
      (castRelativeDegree ℤ hd A.value)
      (((relativeHomologyFunctor ℤ ℤ ((2*m : ℕ) : ℤ)).map f)
        (P202.SpheresDisks.affineClassLinear ℤ ℤ (2*m) 1)) = 1) :
    homogeneousPower m C v m =
      ordinaryImage (localPair (Space m) (projectiveOrigin m)) (2*m)
        (positiveLocalCohomologyClass m) := by
  letI := C.gradedRing
  rcases A with ⟨support,closed,degree,a⟩
  dsimp only at hs hd hp f hf hvalue
  subst support
  subst degree
  have hff : f = positiveLocalSimplex m := by
    apply PairMap.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact hf
  rw [hff] at hvalue
  have ha : a = positiveLocalCohomologyClass m := by
    apply (positiveLocalCohomologyEquiv m).injective
    rw [positiveLocalCohomologyEquiv_apply,
      positiveLocalCohomologyEquiv_apply, positiveLocalCohomologyClass_evaluation]
    exact hvalue
  apply DirectSum.of_injective (β := H ℤ (projectiveSpace m)) (2*m)
  rw [of_homogeneousPower, ← hp]
  change DirectSum.of (H ℤ (projectiveSpace m)) (2*m)
    (ordinaryImage (localPair (Space m) (projectiveOrigin m)) (2*m) a) = _
  rw [ha]

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace P202.ComplexProjectiveRing
open P202Specs.ComplexProjectiveRing P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.RelativeCupProduct P202Specs.ThomClass

/-- The standard positive real simplex in the actual lifted normal model. -/
def positiveModelSimplex (n : ℕ) : P202Specs.SpheresDisks.simplexPair n ⟶ modelPair.{0} n where
  map := TopCat.ofHom ⟨fun x => ULift.up (positiveSimplexCoordinates n x),
    continuous_uliftUp.comp (positiveSimplexCoordinates_continuous n)⟩
  mapsTo := fun x hx => positiveSimplexCoordinates_ne_zero_on_boundary n x hx

lemma positiveModelSimplex_complexLine :
    positiveModelSimplex 2 ≫ complexLineModelIso.inv = positiveComplexLineSimplex := by
  apply PairMap.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change orderedRealComplexCoordinates 1 (positiveSimplexCoordinates 2 x) 0 =
    complexSimplexCoordinates 1 x 0
  rfl

lemma positiveModelComplexLine_evaluation :
    relativeEvaluation (modelPair.{0} 2) 2
      (complexLineModelClass positiveComplexLineCohomologyClass)
      (((relativeHomologyFunctor ℤ ℤ 2).map (positiveModelSimplex 2))
        (P202.SpheresDisks.affineClassLinear ℤ ℤ 2 1)) = 1 := by
  have he : ((relativeHomologyFunctor ℤ ℤ 2).map complexLineModelIso.inv)
      (((relativeHomologyFunctor ℤ ℤ 2).map (positiveModelSimplex 2))
        (P202.SpheresDisks.affineClassLinear ℤ ℤ 2 1)) =
      ((relativeHomologyFunctor ℤ ℤ 2).map positiveComplexLineSimplex)
        (P202.SpheresDisks.affineClassLinear ℤ ℤ 2 1) := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, positiveModelSimplex_complexLine]
  calc
    _ = relativeEvaluation complexLinePair 2 positiveComplexLineCohomologyClass
        (((relativeHomologyFunctor ℤ ℤ 2).map complexLineModelIso.inv)
          (((relativeHomologyFunctor ℤ ℤ 2).map (positiveModelSimplex 2))
            (P202.SpheresDisks.affineClassLinear ℤ ℤ 2 1))) :=
      relativeEvaluation_pullback complexLineModelIso.inv 2 _ _
    _ = 1 := by rw [he]; exact positiveComplexLineCohomologyClass_evaluation

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace P202.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
  P202Specs.ComplexProjectiveRing P202Specs.RelativeCupProduct
  P202Specs.TransverseThomProduct P202.TransverseThomProduct

/-- The original relative homology class of a finite nonnegative chain cycle. -/
def finiteRelativeClass (P : Pair.{0}) (n : ℕ) (c : Chains ℤ P.space n)
    (hc : IsRelativeCycle ℤ P.space P.subspace n c) : relativeHomology ℤ ℤ P (n : ℤ) :=
  P202Specs.SpheresDisks.classOf ℤ (ordinary ℤ ℤ P) (n : ℤ)
    (relativeChainProjection ℤ P n c) (relativeChainProjection_isCycle ℤ P n c hc)

/-- The accepted finite-cycle evaluation agrees with the fixed UCT evaluation
on the original quotient relative cycle, with no chosen comparison sign. -/
lemma relativeEvaluation_finiteRelativeClass (P : Pair.{0}) (n : ℕ)
    (c : Chains ℤ P.space n) (hc : IsRelativeCycle ℤ P.space P.subspace n c)
    (a : HR ℤ P n) :
    relativeEvaluation P n a (finiteRelativeClass P n c hc) =
      relativeCycleEvaluation ℤ P n c hc a := by
  obtain ⟨ar, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((relativeCochains ℤ ℤ P).homologyπ (n : ℤ))).mp inferInstance a
  rw [relativeCycleEvaluation_homologyπ]
  unfold finiteRelativeClass
  erw [evaluation_classOf]
  rfl

/-- Quotienting finite chains commutes with the original relative chain map. -/
lemma relativeChainProjection_map {P Q : Pair.{0}} (f : P ⟶ Q) (n : ℕ)
    (c : Chains ℤ P.space n) :
    (relativeMap (ordinaryFunctor ℤ ℤ) f).f (n : ℤ) (relativeChainProjection ℤ P n c) =
      relativeChainProjection ℤ Q n (((chainMap ℤ ℤ f.map).f n).hom c) := by
  have h := congrArg (fun ff => ff.f (n : ℤ)
    ((ordinaryNonnegativeIso ℤ ℤ P.space n).inv c))
    (projection_map (ordinaryFunctor ℤ ℤ) f)
  change (relativeMap (ordinaryFunctor ℤ ℤ) f).f (n : ℤ)
    (relativeChainProjection ℤ P n c) =
      (projection (ordinaryFunctor ℤ ℤ) Q).f (n : ℤ)
        (((ordinaryFunctor ℤ ℤ).map f.map).f (n : ℤ)
          ((ordinaryNonnegativeIso ℤ ℤ P.space n).inv c)) at h
  rw [h]
  have hf := congrArg (fun ff => ff c) (P202.CupProduct.ordinary_chainMap_degree ℤ f.map n)
  change ((ordinaryFunctor ℤ ℤ).map f.map).f (n : ℤ)
      ((ordinaryNonnegativeIso ℤ ℤ P.space n).inv c) =
    (ordinaryNonnegativeIso ℤ ℤ Q.space n).inv (((chainMap ℤ ℤ f.map).f n).hom c) at hf
  rw [hf]
  rfl

/-- The finite quotient-cycle class is natural for actual maps of pairs. -/
lemma finiteRelativeClass_map {P Q : Pair.{0}} (f : P ⟶ Q) (n : ℕ)
    (c : Chains ℤ P.space n) (hc : IsRelativeCycle ℤ P.space P.subspace n c) :
    (relativeHomologyFunctor ℤ ℤ (n : ℤ)).map f (finiteRelativeClass P n c hc) =
      finiteRelativeClass Q n (((chainMap ℤ ℤ f.map).f n).hom c)
        (relativeCycle_map ℤ f n c hc) := by
  unfold finiteRelativeClass
  change HomologicalComplex.homologyMap (relativeMap (ordinaryFunctor ℤ ℤ) f) (n : ℤ)
      (P202Specs.SpheresDisks.classOf ℤ (ordinary ℤ ℤ P) (n : ℤ)
        (relativeChainProjection ℤ P n c) (relativeChainProjection_isCycle ℤ P n c hc)) =
    P202Specs.SpheresDisks.classOf ℤ (ordinary ℤ ℤ Q) (n : ℤ)
      (relativeChainProjection ℤ Q n (((chainMap ℤ ℤ f.map).f n).hom c))
      (relativeChainProjection_isCycle ℤ Q n _ (relativeCycle_map ℤ f n c hc))
  have hz := relativeChainProjection_map f n c
  have h := P202.MayerVietoris.classOf_map (relativeMap (ordinaryFunctor ℤ ℤ) f) (n : ℤ)
    (relativeChainProjection ℤ P n c) (relativeChainProjection_isCycle ℤ P n c hc)
    (by rw [hz]; exact relativeChainProjection_isCycle ℤ Q n _ (relativeCycle_map ℤ f n c hc))
  simpa only [P202Specs.MayerVietoris.classOf, P202Specs.SpheresDisks.classOf, hz] using h

lemma finiteRelativeClass_affine (n : ℕ) :
    finiteRelativeClass (P202Specs.SpheresDisks.simplexPair n) n
      (P202Specs.SpheresDisks.affineChain ℤ n 1) (affineChain_relativeCycle ℤ n 1) =
      P202.SpheresDisks.affineClassLinear ℤ ℤ n 1 := by
  rw [P202.SpheresDisks.affineClassLinear_apply]
  rfl

/-- A mapped affine simplex represents its actual pair-map image of the
normalized affine relative class. -/
lemma finiteRelativeClass_affineMap {P : Pair.{0}} (n : ℕ)
    (f : P202Specs.SpheresDisks.simplexPair n ⟶ P) :
    finiteRelativeClass P n
      (((chainMap ℤ ℤ f.map).f n).hom (P202Specs.SpheresDisks.affineChain ℤ n 1))
      (relativeCycle_map ℤ f n _ (affineChain_relativeCycle ℤ n 1)) =
      (relativeHomologyFunctor ℤ ℤ (n : ℤ)).map f
        (P202.SpheresDisks.affineClassLinear ℤ ℤ n 1) := by
  have h := finiteRelativeClass_map f n (P202Specs.SpheresDisks.affineChain ℤ n 1)
    (affineChain_relativeCycle ℤ n 1)
  rw [finiteRelativeClass_affine] at h
  exact h.symm

/-- Equality in the actual relative chain quotient identifies the finite
relative homology classes, independently of the cycle proofs. -/
lemma finiteRelativeClass_eq_of_projection_eq (P : Pair.{0}) (n : ℕ)
    (c d : Chains ℤ P.space n)
    (hc : IsRelativeCycle ℤ P.space P.subspace n c)
    (hd : IsRelativeCycle ℤ P.space P.subspace n d)
    (hcd : relativeChainProjection ℤ P n c = relativeChainProjection ℤ P n d) :
    finiteRelativeClass P n c hc = finiteRelativeClass P n d hd := by
  unfold finiteRelativeClass
  simp only [hcd]

/-- Exact evaluation one for the actual external relative cup class on the
actual finite shuffled relative cycle, stated at cohomology/homology level. -/
lemma relativeExternalProduct_finiteRelativeClass_one
    (μ : NaturalRelativeCupProduct.{0,0} ℤ)
    (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B)
    (p q : ℕ) (a : HR ℤ (⟨X,A⟩ : Pair) p) (b : HR ℤ (⟨Y,B⟩ : Pair) q)
    (c : Chains ℤ X p) (d : Chains ℤ Y q)
    (hc : IsRelativeCycle ℤ X A p c) (hd : IsRelativeCycle ℤ Y B q d)
    (ha : relativeEvaluation (⟨X,A⟩ : Pair) p a
      (finiteRelativeClass (⟨X,A⟩ : Pair) p c hc) = 1)
    (hb : relativeEvaluation (⟨Y,B⟩ : Pair) q b
      (finiteRelativeClass (⟨Y,B⟩ : Pair) q d hd) = 1) :
    relativeEvaluation (productSubspaces X Y A B).unionPair (p+q)
      (μ.product (productSubspaces X Y A B) (productSubspaces_isOpen X Y A B hA hB) p q
        (relativePullback ℤ (productLeftProjection X Y A B) p a ⊗ₜ[ℤ]
          relativePullback ℤ (productRightProjection X Y A B) q b))
      (finiteRelativeClass (productSubspaces X Y A B).unionPair (p+q)
        (P202Specs.ShuffleModel.shuffleComponent ℤ X Y p q (c ⊗ₜ[ℤ] d))
        (shuffleComponent_relativeCycle ℤ A B p q c d hc hd)) = 1 := by
  obtain ⟨ar, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((relativeCochains ℤ ℤ (⟨X,A⟩ : Pair)).homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨br, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((relativeCochains ℤ ℤ (⟨Y,B⟩ : Pair)).homologyπ (q : ℤ))).mp inferInstance b
  let v := μ.product (productSubspaces X Y A B) (productSubspaces_isOpen X Y A B hA hB) p q
    (relativePullback ℤ (productLeftProjection X Y A B) p
      ((relativeCochains ℤ ℤ (⟨X,A⟩ : Pair)).homologyπ (p : ℤ) ar) ⊗ₜ[ℤ]
      relativePullback ℤ (productRightProjection X Y A B) q
        ((relativeCochains ℤ ℤ (⟨Y,B⟩ : Pair)).homologyπ (q : ℤ) br))
  obtain ⟨er, her⟩ :=
    (ModuleCat.epi_iff_surjective ((relativeCochains ℤ ℤ (productSubspaces X Y A B).unionPair).homologyπ
      ((p+q : ℕ) : ℤ))).mp inferInstance v
  rw [relativeEvaluation_finiteRelativeClass, relativeCycleEvaluation_homologyπ] at ha hb
  change relativeEvaluation _ _ v _ = 1
  rw [← her, relativeEvaluation_finiteRelativeClass, relativeCycleEvaluation_homologyπ]
  exact relativeProductEvaluation_of_representatives ℤ μ X Y A B hA hB p q
    ar br c d hc hd ha hb er her

/-- A localized shuffled cycle with one surviving oriented affine simplex
evaluates one on that simplex's actual relative homology class. -/
lemma relativeExternalProduct_survivingSimplex_one
    (μ : NaturalRelativeCupProduct.{0,0} ℤ)
    (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B)
    (p q : ℕ) (a : HR ℤ (⟨X,A⟩ : Pair) p) (b : HR ℤ (⟨Y,B⟩ : Pair) q)
    (c : Chains ℤ X p) (d : Chains ℤ Y q)
    (hc : IsRelativeCycle ℤ X A p c) (hd : IsRelativeCycle ℤ Y B q d)
    (ha : relativeEvaluation (⟨X,A⟩ : Pair) p a
      (finiteRelativeClass (⟨X,A⟩ : Pair) p c hc) = 1)
    (hb : relativeEvaluation (⟨Y,B⟩ : Pair) q b
      (finiteRelativeClass (⟨Y,B⟩ : Pair) q d hd) = 1)
    (f : P202Specs.SpheresDisks.simplexPair (p+q) ⟶ (productSubspaces X Y A B).unionPair)
    (hloc : relativeChainProjection ℤ (productSubspaces X Y A B).unionPair (p+q)
        (P202Specs.ShuffleModel.shuffleComponent ℤ X Y p q (c ⊗ₜ[ℤ] d)) =
      relativeChainProjection ℤ (productSubspaces X Y A B).unionPair (p+q)
        (((chainMap ℤ ℤ f.map).f (p+q)).hom
          (P202Specs.SpheresDisks.affineChain ℤ (p+q) 1))) :
    relativeEvaluation (productSubspaces X Y A B).unionPair (p+q)
      (μ.product (productSubspaces X Y A B) (productSubspaces_isOpen X Y A B hA hB) p q
        (relativePullback ℤ (productLeftProjection X Y A B) p a ⊗ₜ[ℤ]
          relativePullback ℤ (productRightProjection X Y A B) q b))
      ((relativeHomologyFunctor ℤ ℤ ((p+q : ℕ) : ℤ)).map f
        (P202.SpheresDisks.affineClassLinear ℤ ℤ (p+q) 1)) = 1 := by
  have h := relativeExternalProduct_finiteRelativeClass_one μ X Y A B hA hB p q a b c d hc hd ha hb
  have he := finiteRelativeClass_eq_of_projection_eq (productSubspaces X Y A B).unionPair (p+q)
    (P202Specs.ShuffleModel.shuffleComponent ℤ X Y p q (c ⊗ₜ[ℤ] d))
    (((chainMap ℤ ℤ f.map).f (p+q)).hom (P202Specs.SpheresDisks.affineChain ℤ (p+q) 1))
    (shuffleComponent_relativeCycle ℤ A B p q c d hc hd)
    (relativeCycle_map ℤ f (p+q) _ (affineChain_relativeCycle ℤ (p+q) 1)) hloc
  rw [he, finiteRelativeClass_affineMap] at h
  exact h

end P202.ComplexProjectiveRing
end
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace P202.ComplexProjectiveRing
open P202Specs.ComplexProjectiveRing P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.RelativeCupProduct P202Specs.ThomClass
open P202Specs.TransverseThomProduct

/-- Evaluation-one normalization on the explicitly ordered real simplex in
its actual lifted normal model. -/
def ModelPositive (a : ModelClass.{0,0} ℤ) : Prop :=
  relativeEvaluation (modelPair.{0} a.degree) a.degree a.value
    (((relativeHomologyFunctor ℤ ℤ (a.degree : ℤ)).map (positiveModelSimplex a.degree))
      (P202.SpheresDisks.affineClassLinear ℤ ℤ a.degree 1)) = 1

/-- The exact ordered binary normalization propagates to every number of
complex coordinate blocks, without permuting factors or changing their sign. -/
lemma orderedModelCup_positive_of_binary
    (μ : NaturalRelativeCupProduct.{0,0} ℤ)
    (g₂ : HR ℤ (modelPair.{0} 2) 2)
    (h₂ : ModelPositive ⟨2,g₂⟩)
    (hbinary : ∀ (q : ℕ) (a : HR ℤ (modelPair.{0} 2) 2)
      (b : HR ℤ (modelPair.{0} q) q),
      ModelPositive ⟨2,a⟩ → ModelPositive ⟨q,b⟩ →
        ModelPositive ⟨2+q, orderedModelProductOrientation ℤ μ 2 q a b⟩)
    (k : ℕ) :
    ModelPositive (orderedModelCup ℤ μ k (fun _ => (⟨2,g₂⟩ : ModelClass.{0,0} ℤ))) := by
  induction k with
  | zero => exact h₂
  | succ k ih =>
    change ModelPositive (modelCup ℤ μ (⟨2,g₂⟩ : ModelClass.{0,0} ℤ)
      (orderedModelCup ℤ μ k (fun _ => (⟨2,g₂⟩ : ModelClass.{0,0} ℤ))))
    exact hbinary _ g₂ _ h₂ ih

lemma orderedModelCup_two_degree
    (μ : NaturalRelativeCupProduct.{0,0} ℤ)
    (g₂ : HR ℤ (modelPair.{0} 2) 2) (k : ℕ) :
    (orderedModelCup ℤ μ k (fun _ => (⟨2,g₂⟩ : ModelClass.{0,0} ℤ))).degree = 2*(k+1) := by
  rw [P202.TransverseThomProduct.orderedModelCup_degree]
  simp
  ring

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
open CategoryTheory Set
namespace P202.ComplexProjectiveRing
open P202Specs.ShuffleModel P202Specs.ComplexProjectiveRing

lemma positiveSimplexCoordinates_barycenter (n : ℕ) :
    positiveSimplexCoordinates n (Convexity.StdSimplex.barycenter : StdSimplex n) = 0 := by
  ext j
  simp [positiveSimplexCoordinates, Convexity.StdSimplex.weights_barycenter_apply]

lemma shuffleWeighted_reference_barycenter (q : ℕ) :
    ((shuffleHorizontalSimplex q).map
        (parametrization (horizontalThenVertical 2 q) Convexity.StdSimplex.barycenter).1,
      (shuffleVerticalSimplex q).map
        (parametrization (horizontalThenVertical 2 q) Convexity.StdSimplex.barycenter).2) = ((0 : Fin 2 → ℝ),(0 : Fin q → ℝ)) := by
  have h := shuffleWeighted_reference_formula q Convexity.StdSimplex.barycenter
  rw [positiveSimplexCoordinates_barycenter] at h
  have hz : positiveShuffleInterpolation q 1 (0 : Fin (2+q) → ℝ) = 0 := by
    ext k
    refine Fin.addCases ?_ ?_ k
    · intro k
      fin_cases k <;> simp [positiveShuffleInterpolation]
    · intro k
      simp [positiveShuffleInterpolation]
  rw [hz] at h
  change Fin.append
    (weightedSimplexCoordinates 2 (shuffleHorizontalWeights q)
      (parametrization (horizontalThenVertical 2 q) Convexity.StdSimplex.barycenter).1)
    (weightedSimplexCoordinates q (shuffleVerticalWeights q)
      (parametrization (horizontalThenVertical 2 q) Convexity.StdSimplex.barycenter).2) = 0 at h
  apply Prod.ext
  · change weightedSimplexCoordinates 2 (shuffleHorizontalWeights q)
      (parametrization (horizontalThenVertical 2 q) Convexity.StdSimplex.barycenter).1 = 0
    funext j
    have hj := congrFun h (Fin.castAdd q j)
    simpa only [Fin.append_left, Pi.zero_apply] using hj
  · change weightedSimplexCoordinates q (shuffleVerticalWeights q)
      (parametrization (horizontalThenVertical 2 q) Convexity.StdSimplex.barycenter).2 = 0
    funext j
    have hj := congrFun h (Fin.natAdd 2 j)
    simpa only [Fin.append_right, Pi.zero_apply] using hj

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace P202.ComplexProjectiveRing
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
  P202Specs.ComplexProjectiveRing P202Specs.RelativeCupProduct
  P202Specs.TransverseThomProduct P202.TransverseThomProduct P202Specs.AlexanderWhitney
open P202Specs.ThomClass P202Specs.LocalOrientation P202Specs.ShuffleModel
  P202Specs.SpheresDisks

/-- The canonical inclusion into the universe-lifted real normal model. -/
def realModelLift (n : ℕ) : localPair (Fin n → ℝ) 0 ⟶ modelPair.{0} n where
  map := TopCat.ofHom ⟨ULift.up, continuous_uliftUp⟩
  mapsTo := fun _ h => h

lemma positiveModelSimplex_factor (n : ℕ) :
    positiveRealLocalSimplex n ≫ realModelLift n = positiveModelSimplex n := rfl

def shuffleHorizontalModelSimplex (q : ℕ) : simplexPair 2 ⟶ modelPair.{0} 2 :=
  shuffleHorizontalSimplex q ≫ realModelLift 2

def shuffleVerticalModelSimplex (q : ℕ) : simplexPair q ⟶ modelPair.{0} q :=
  shuffleVerticalSimplex q ≫ realModelLift q

lemma shuffleHorizontalModelSimplex_homology (q : ℕ) (j : ℤ) :
    (relativeHomologyFunctor ℤ ℤ j).map (shuffleHorizontalModelSimplex q) =
      (relativeHomologyFunctor ℤ ℤ j).map (positiveModelSimplex 2) := by
  unfold shuffleHorizontalModelSimplex shuffleHorizontalSimplex
  rw [Functor.map_comp, weightedPositiveRealLocalSimplex_homology_eq]
  rw [← positiveModelSimplex_factor, Functor.map_comp]

lemma shuffleVerticalModelSimplex_homology (q : ℕ) (j : ℤ) :
    (relativeHomologyFunctor ℤ ℤ j).map (shuffleVerticalModelSimplex q) =
      (relativeHomologyFunctor ℤ ℤ j).map (positiveModelSimplex q) := by
  unfold shuffleVerticalModelSimplex shuffleVerticalSimplex
  rw [Functor.map_comp, weightedPositiveRealLocalSimplex_homology_eq]
  rw [← positiveModelSimplex_factor, Functor.map_comp]

def referenceModelSimplex (q : ℕ) : simplexPair (2+q) ⟶
    (productSubspaces (modelPair.{0} 2).space (modelPair.{0} q).space
      (modelPair.{0} 2).subspace (modelPair.{0} q).subspace).unionPair :=
  centeredReferenceSimplex q ≫ realModelLift (2+q) ≫ (orderedModelProductIso 2 q).inv

lemma referenceModelSimplex_formula (q : ℕ) (x : StdSimplex (2+q)) :
    (referenceModelSimplex q).map x =
      ((shuffleHorizontalModelSimplex q).map ((parametrization (horizontalThenVertical 2 q)) x).1,
       (shuffleVerticalModelSimplex q).map ((parametrization (horizontalThenVertical 2 q)) x).2) := by
  apply (orderedModelHomeomorph 2 q).injective
  change orderedModelHomeomorph 2 q ((orderedModelHomeomorph 2 q).symm
      (ULift.up (positiveShuffleInterpolation q 1 (positiveSimplexCoordinates (2+q) x)))) =
    orderedModelHomeomorph 2 q
      (ULift.up ((shuffleHorizontalSimplex q).map ((parametrization (horizontalThenVertical 2 q)) x).1),
       ULift.up ((shuffleVerticalSimplex q).map ((parametrization (horizontalThenVertical 2 q)) x).2))
  rw [Homeomorph.apply_symm_apply]
  apply ULift.ext
  exact (shuffleWeighted_reference_formula q x).symm

lemma referenceModelSimplex_barycenter (q : ℕ) :
    (referenceModelSimplex q).map Convexity.StdSimplex.barycenter = (ULift.up 0, ULift.up 0) := by
  apply (orderedModelHomeomorph 2 q).injective
  change orderedModelHomeomorph 2 q ((orderedModelHomeomorph 2 q).symm
      (ULift.up (positiveShuffleInterpolation q 1
        (positiveSimplexCoordinates (2+q) Convexity.StdSimplex.barycenter)))) = _
  rw [Homeomorph.apply_symm_apply, orderedModelHomeomorph_zero]
  apply ULift.ext
  have hz : positiveSimplexCoordinates (2+q) Convexity.StdSimplex.barycenter = 0 := by
    ext j
    simp [positiveSimplexCoordinates, Convexity.StdSimplex.weights_barycenter_apply]
  rw [hz]
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro i <;> simp [positiveShuffleInterpolation]

lemma mappedAffineSimplex_formula {P : Pair.{0}} (n : ℕ) (f : simplexPair n ⟶ P)
    (x : StdSimplex n) :
    simplexEquiv P.space n (postSimplex f.map n (affineSimplex n)) x = f.map x := by
  unfold postSimplex
  erw [P202.SingularChains.simplexEquiv_postcomp]
  change f.map ((simplexEquiv (simplex n) n (affineSimplex n)) x) = f.map x
  have h : simplexEquiv (simplex n) n (affineSimplex n) = ContinuousMap.id _ :=
    Equiv.apply_symm_apply _ _
  rw [h]
  rfl

/-- The ordered binary normal-model product preserves the canonical positive
simplex orientation, with exact evaluation +1. -/
lemma orderedModelProduct_positive (μ : NaturalRelativeCupProduct.{0,0} ℤ) (q : ℕ)
    (a : HR ℤ (modelPair.{0} 2) 2) (b : HR ℤ (modelPair.{0} q) q)
    (ha : relativeEvaluation (modelPair.{0} 2) 2 a
      ((relativeHomologyFunctor ℤ ℤ (2 : ℤ)).map (positiveModelSimplex 2)
        (P202.SpheresDisks.affineClassLinear ℤ ℤ 2 1)) = 1)
    (hb : relativeEvaluation (modelPair.{0} q) q b
      ((relativeHomologyFunctor ℤ ℤ (q : ℤ)).map (positiveModelSimplex q)
        (P202.SpheresDisks.affineClassLinear ℤ ℤ q 1)) = 1) :
    relativeEvaluation (modelPair.{0} (2+q)) (2+q)
      (orderedModelProductOrientation ℤ μ 2 q a b)
      ((relativeHomologyFunctor ℤ ℤ ((2+q : ℕ) : ℤ)).map (positiveModelSimplex (2+q))
        (P202.SpheresDisks.affineClassLinear ℤ ℤ (2+q) 1)) = 1 := by
  let X := (modelPair.{0} 2).space
  let Y := (modelPair.{0} q).space
  let P := productSubspaces X Y (modelPair.{0} 2).subspace (modelPair.{0} q).subspace
  let F := shuffleHorizontalModelSimplex q
  let G := shuffleVerticalModelSimplex q
  let c := ((chainMap ℤ ℤ F.map).f 2).hom (affineChain ℤ 2 1)
  let d := ((chainMap ℤ ℤ G.map).f q).hom (affineChain ℤ q 1)
  let σ := postSimplex F.map 2 (affineSimplex 2)
  let τ := postSimplex G.map q (affineSimplex q)
  have hc := relativeCycle_map ℤ F 2 (affineChain ℤ 2 1) (affineChain_relativeCycle ℤ 2 1)
  have hd := relativeCycle_map ℤ G q (affineChain ℤ q 1) (affineChain_relativeCycle ℤ q 1)
  have hac : relativeEvaluation (modelPair.{0} 2) 2 a
      (finiteRelativeClass (modelPair.{0} 2) 2 c hc) = 1 := by
    rw [finiteRelativeClass_affineMap, shuffleHorizontalModelSimplex_homology]
    exact ha
  have hbd : relativeEvaluation (modelPair.{0} q) q b
      (finiteRelativeClass (modelPair.{0} q) q d hd) = 1 := by
    rw [finiteRelativeClass_affineMap, shuffleVerticalModelSimplex_homology]
    exact hb
  have hσ : Function.Injective (simplexEquiv X 2 σ) := by
    intro x y h
    apply weightedSimplexCoordinates_injective 2 (shuffleHorizontalWeights q) (shuffleHorizontalWeights_pos q)
    have h' : F.map x = F.map y :=
      (mappedAffineSimplex_formula 2 F x).symm.trans
        (h.trans (mappedAffineSimplex_formula 2 F y))
    exact congrArg ULift.down h'
  have hτ : Function.Injective (simplexEquiv Y q τ) := by
    intro x y h
    apply weightedSimplexCoordinates_injective q (shuffleVerticalWeights q) (shuffleVerticalWeights_pos q)
    have h' : G.map x = G.map y :=
      (mappedAffineSimplex_formula q G x).symm.trans
        (h.trans (mappedAffineSimplex_formula q G y))
    exact congrArg ULift.down h'
  have hcenter :
      (simplexEquiv X 2 σ (parametrization (horizontalThenVertical 2 q) Convexity.StdSimplex.barycenter).1,
       simplexEquiv Y q τ (parametrization (horizontalThenVertical 2 q) Convexity.StdSimplex.barycenter).2) =
        (ULift.up 0, ULift.up 0) := by
    rw [← referenceModelSimplex_barycenter q, referenceModelSimplex_formula]
    simp only [σ, τ, mappedAffineSimplex_formula]
    rfl
  have hloc₀ : relativeChainProjection ℤ P.unionPair (2+q) (shuffleGenerator ℤ σ τ) =
      relativeChainProjection ℤ P.unionPair (2+q)
        (Finsupp.single (shuffleSimplex (horizontalThenVertical 2 q) σ τ) 1) := by
    apply relativeChainProjection_shuffle_eq_of_sign_one ℤ _ σ τ (horizontalThenVertical 2 q)
      (horizontalThenVertical_sign 2 q)
    intro s hs x
    rw [P202.ShuffleModel.simplex_formula]
    change (simplexEquiv X 2 σ (parametrization s x).1).down ≠ 0 ∨
      (simplexEquiv Y q τ (parametrization s x).2).down ≠ 0
    by_contra hzero
    push_neg at hzero
    have he : (simplexEquiv X 2 σ (parametrization s x).1,
        simplexEquiv Y q τ (parametrization s x).2) = (ULift.up 0,ULift.up 0) :=
      Prod.ext (ULift.ext hzero.1) (ULift.ext hzero.2)
    exact otherShuffle_avoids_barycenter_image (horizontalThenVertical 2 q) s hs
      (simplexEquiv X 2 σ) (simplexEquiv Y q τ) hσ hτ x (he.trans hcenter.symm)
  have href : postSimplex (referenceModelSimplex q).map (2+q) (affineSimplex (2+q)) =
      shuffleSimplex (horizontalThenVertical 2 q) σ τ := by
    apply (simplexEquiv (P.space) (2+q)).injective
    apply ContinuousMap.ext
    intro x
    refine (mappedAffineSimplex_formula (2+q) (referenceModelSimplex q) x).trans ?_
    erw [P202.ShuffleModel.simplex_formula]
    exact (referenceModelSimplex_formula q x).trans
      (Prod.ext (mappedAffineSimplex_formula 2 F _).symm (mappedAffineSimplex_formula q G _).symm)
  have hloc : relativeChainProjection ℤ P.unionPair (2+q)
      (shuffleComponent ℤ X Y 2 q (c ⊗ₜ[ℤ] d)) =
    relativeChainProjection ℤ P.unionPair (2+q)
      (((chainMap ℤ ℤ (referenceModelSimplex q).map).f (2+q)).hom (affineChain ℤ (2+q) 1)) := by
    have hc_single : c = Finsupp.single σ 1 :=
      P202.SingularChains.chainMap_single ℤ ℤ F.map 2 (affineSimplex 2) 1
    have hd_single : d = Finsupp.single τ 1 :=
      P202.SingularChains.chainMap_single ℤ ℤ G.map q (affineSimplex q) 1
    have href_single : ((chainMap ℤ ℤ (referenceModelSimplex q).map).f (2+q)).hom
        (affineChain ℤ (2+q) 1) = Finsupp.single
          (postSimplex (referenceModelSimplex q).map (2+q) (affineSimplex (2+q))) 1 :=
      P202.SingularChains.chainMap_single ℤ ℤ (referenceModelSimplex q).map (2+q) (affineSimplex (2+q)) 1
    rw [hc_single, hd_single]
    erw [P202.ShuffleModel.component_basis]
    rw [href_single, href]
    exact hloc₀
  have he := relativeExternalProduct_survivingSimplex_one μ X Y
    (modelPair.{0} 2).subspace (modelPair.{0} q).subspace
    (modelPair_isOpen 2) (modelPair_isOpen q) 2 q a b c d hc hd hac hbd
    (referenceModelSimplex q) hloc
  have hrefhom : (relativeHomologyFunctor ℤ ℤ ((2+q : ℕ) : ℤ)).map (referenceModelSimplex q) =
      (relativeHomologyFunctor ℤ ℤ ((2+q : ℕ) : ℤ)).map
        (positiveModelSimplex (2+q) ≫ (orderedModelProductIso 2 q).inv) := by
    unfold referenceModelSimplex
    rw [← positiveModelSimplex_factor]
    simp only [Functor.map_comp, centeredReferenceSimplex_homology_eq, Category.assoc]
  rw [hrefhom, Functor.map_comp, ModuleCat.comp_apply] at he
  change relativeEvaluation (modelPair.{0} (2+q)) (2+q)
    (relativePullback ℤ (orderedModelProductIso 2 q).inv (2+q)
      (modelExternalProduct ℤ μ 2 q a b)) _ = 1
  erw [relativeEvaluation_pullback]
  exact he

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open SmoothManifolds.ModelData
namespace P202.ComplexProjectiveRing
open P202Specs.CohomologyPairs P202Specs.RelativeCupProduct P202Specs.ThomClass
  P202Specs.TransverseThomProduct P202.TransverseThomProduct

lemma constantTwo_modelCup_degree (μ : NaturalRelativeCupProduct ℤ) (k : ℕ)
    (g : HR ℤ (modelPair.{0} 2) 2) :
    (orderedModelCup ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass ℤ))).degree = 2*(k+1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 2+(orderedModelCup ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass ℤ))).degree = _
    rw [ih]
    omega

/-- The recursive flattening of rank-two normal blocks is the original ordered
real sequence `(Re z0,Im z0,Re z1,Im z1,...)`, with no coordinate permutation. -/
lemma modelBlocksHomeomorph_two_apply (μ : NaturalRelativeCupProduct ℤ) (k : ℕ)
    (g : HR ℤ (modelPair.{0} 2) 2)
    (z : ULift.{0} (Fin (k+1) → Euclidean 2)) (j : Fin (k+1)) (l : Fin 2) :
    (modelBlocksHomeomorph ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass ℤ)) z).down
      ⟨2*j.val+l.val, by rw [constantTwo_modelCup_degree]; omega⟩ = z.down j l := by
  induction k with
  | zero =>
    have hj : j=0 := Fin.eq_zero j
    subst j
    change z.down 0 ⟨2*0+l.val,_⟩ = z.down 0 l
    fin_cases l <;> rfl
  | succ k ih =>
    induction j using Fin.cases with
    | zero =>
      let d := (orderedModelCup ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass ℤ))).degree
      change Fin.append (z.down 0)
        (modelBlocksHomeomorph ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass ℤ))
          (⟨fun j => z.down j.succ⟩ : ULift.{0} (Fin (k+1) → Euclidean 2))).down
        (⟨2*0+l.val,_⟩ : Fin (2+d)) = _
      have hi : (⟨2*0+l.val,by have := l.isLt; omega⟩ : Fin (2+d)) = Fin.castAdd d l := Fin.ext (by simp)
      rw [hi,Fin.append_left]
    | succ j =>
      let d := (orderedModelCup ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass ℤ))).degree
      let i : Fin d := ⟨2*j.val+l.val,by dsimp [d]; rw [constantTwo_modelCup_degree]; omega⟩
      change Fin.append (z.down 0)
        (modelBlocksHomeomorph ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass ℤ))
          (⟨fun j => z.down j.succ⟩ : ULift.{0} (Fin (k+1) → Euclidean 2))).down
        (⟨2*j.succ.val+l.val,_⟩ : Fin (2+d)) = _
      have hi : (⟨2*j.succ.val+l.val,by
          dsimp [d]; rw [constantTwo_modelCup_degree]; have := j.isLt; have := l.isLt; omega⟩ : Fin (2+d)) =
          Fin.natAdd 2 i := Fin.ext (by dsimp [i]; omega)
      rw [hi,Fin.append_right]
      exact ih _ j

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open SmoothManifolds.ModelData
namespace P202.ComplexProjectiveRing
open P202Specs.ComplexProjectiveRing P202Specs.CohomologyPairs P202Specs.RelativeCupProduct
  P202Specs.ThomClass P202Specs.TransverseThomProduct P202.TransverseThomProduct

lemma complexLineRealHomeomorph_apply (z : ℂ) (l : Fin 2) :
    complexLineRealHomeomorph z l = if l.val % 2 = 0 then z.re else z.im := rfl

/-- The recursive ordered model flattening agrees pointwise with the explicit
Re/Im sequence, with the total-degree equality recorded as a finite index cast. -/
lemma complexCoordinateBlocks_flatten_apply
    (μ : NaturalRelativeCupProduct.{0,0} ℤ) (k : ℕ)
    (g : HR ℤ (modelPair.{0} 2) 2) (z : Fin (k+1) → ℂ)
    (i : Fin (orderedModelCup ℤ μ k
      (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ))).degree) :
    (modelBlocksHomeomorph ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ))
      (complexCoordinateBlocksHomeomorph (k+1) z)).down i =
      orderedComplexRealCoordinates (k+1) z
        (Fin.cast (constantTwo_modelCup_degree μ k g) i) := by
  let d := (orderedModelCup ℤ μ k
    (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ))).degree
  have hid : i.val < 2*(k+1) := by
    rw [← constantTwo_modelCup_degree μ k g]
    exact i.isLt
  let j : Fin (k+1) := ⟨i.val / 2,by omega⟩
  let l : Fin 2 := ⟨i.val % 2,Nat.mod_lt _ (by norm_num)⟩
  have hidx : (⟨2*j.val+l.val,by
      dsimp [d]; rw [constantTwo_modelCup_degree μ k g]; dsimp [j,l]; omega⟩ : Fin d) = i := by
    apply Fin.ext
    dsimp [j,l]
    omega
  have h := modelBlocksHomeomorph_two_apply μ k g
    (complexCoordinateBlocksHomeomorph (k+1) z) j l
  change (modelBlocksHomeomorph ℤ μ k
    (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ))
      (complexCoordinateBlocksHomeomorph (k+1) z)).down
        (⟨2*j.val+l.val,_⟩ : Fin d) = complexLineRealHomeomorph (z j) l at h
  rw [hidx] at h
  rw [h,complexLineRealHomeomorph_apply]
  change (if l.val % 2 = 0 then (z j).re else (z j).im) =
    if i.val % 2 = 0 then (z ⟨i.val/2,by omega⟩).re else (z ⟨i.val/2,by omega⟩).im
  have hl : l.val % 2 = i.val % 2 := by dsimp [l]; rw [Nat.mod_mod]
  rw [hl]

lemma complexCoordinateBlocks_flatten
    (μ : NaturalRelativeCupProduct.{0,0} ℤ) (k : ℕ)
    (g : HR ℤ (modelPair.{0} 2) 2) (z : Fin (k+1) → ℂ) :
    (modelBlocksHomeomorph ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ))
      (complexCoordinateBlocksHomeomorph (k+1) z)).down =
      fun i => orderedComplexRealCoordinates (k+1) z
        (Fin.cast (constantTwo_modelCup_degree μ k g) i) := by
  funext i
  exact complexCoordinateBlocks_flatten_apply μ k g z i

/-- On the explicit positive complex simplex the flattened real coordinates
are the original positive barycentric differences in the same order. -/
lemma complexCoordinateBlocks_flatten_positiveSimplex
    (μ : NaturalRelativeCupProduct.{0,0} ℤ) (k : ℕ)
    (g : HR ℤ (modelPair.{0} 2) 2)
    (x : P202.Cellular.StandardSimplex (2*(k+1))) :
    (modelBlocksHomeomorph ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ))
      (complexCoordinateBlocksHomeomorph (k+1) (complexSimplexCoordinates (k+1) x))).down =
      fun i => positiveSimplexCoordinates (2*(k+1)) x
        (Fin.cast (constantTwo_modelCup_degree μ k g) i) := by
  rw [complexCoordinateBlocks_flatten]
  have h := orderedComplexRealCoordinates_left_inverse (k+1)
    (positiveSimplexCoordinates (2*(k+1)) x)
  change orderedComplexRealCoordinates (k+1) (complexSimplexCoordinates (k+1) x) =
    positiveSimplexCoordinates (2*(k+1)) x at h
  funext i
  exact congrFun h _

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace P202.ComplexProjectiveRing
open P202Specs.RelativeCupProduct P202Specs.TransverseThomProduct

lemma orderedModelComplex_positive (μ : NaturalRelativeCupProduct.{0,0} ℤ) (k : ℕ) :
    ModelPositive (orderedModelCup ℤ μ k (fun _ =>
      (⟨2, complexLineModelClass positiveComplexLineCohomologyClass⟩ : ModelClass.{0,0} ℤ))) := by
  apply orderedModelCup_positive_of_binary μ _ positiveModelComplexLine_evaluation
  intro q a b ha hb
  exact orderedModelProduct_positive μ q a b ha hb

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.RelativeCupProduct P202Specs.ThomClass
  P202Specs.CupProduct P202Specs.LocalOrientation
open P202Specs.TransverseThomProduct P202.TransverseThomProduct

/-- Degree equality acts by the order-preserving identity finite index cast. -/
def modelDegreePairMap {d e : ℕ} (h : d=e) : modelPair.{0} e ⟶ modelPair.{0} d :=
  eqToHom (congrArg (fun n => modelPair.{0} n) h.symm)

lemma modelDegreePairMap_apply {d e : ℕ} (h : d=e) (x : (modelPair.{0} e).space) :
    (modelDegreePairMap h).map x = ULift.up (fun i => x.down (Fin.cast h i)) := by
  subst e
  rfl

/-- The same standard positive simplex with an equality of the declared rank. -/
def castPositiveModelSimplex {d e : ℕ} (h : d=e) :
    P202Specs.SpheresDisks.simplexPair e ⟶ modelPair.{0} d :=
  positiveModelSimplex e ≫ modelDegreePairMap h

lemma modelPositive_cast_evaluation {d e : ℕ} (h : d=e)
    (a : HR ℤ (modelPair.{0} d) d)
    (hp : relativeEvaluation (modelPair.{0} d) d a
      (((relativeHomologyFunctor ℤ ℤ (d:ℤ)).map (positiveModelSimplex d))
        (P202.SpheresDisks.affineClassLinear ℤ ℤ d 1)) = 1) :
    relativeEvaluation (modelPair.{0} d) e (castRelativeDegree ℤ h a)
      (((relativeHomologyFunctor ℤ ℤ (e:ℤ)).map (castPositiveModelSimplex h))
        (P202.SpheresDisks.affineClassLinear ℤ ℤ e 1)) = 1 := by
  subst e
  simpa only [castPositiveModelSimplex, modelDegreePairMap, eqToHom_refl,
    Category.comp_id, castRelativeDegree] using hp

/-- The affine chart comparison assembles all complex coordinate factors into
exactly the ordered real model product. -/
lemma projectiveCoordinate_orderedCup_chart_model
    (μ : NaturalRelativeCupProduct.{0,0} ℤ) (k : ℕ)
    (c : ∀ j : Fin (k+1), HR ℤ (coordinateHyperplanePair (k+1) j.castSucc) 2)
    (g : HR ℤ (modelPair.{0} 2) 2)
    (hg : ∀ j, complexCoordinateModelClasses (k+1) c j = g) :
    supportedPullback ℤ
      (TopCat.ofHom ⟨affineChart (k+1) (k+1) le_rfl,
        affineChart_continuous (k+1) (k+1) le_rfl⟩)
      (orderedCup ℤ μ k (projectiveCoordinateFactor (k+1) c)) =
    supportedPullback ℤ
      (TopCat.ofHom ⟨complexCoordinateBlocksHomeomorph (k+1),
        (complexCoordinateBlocksHomeomorph (k+1)).continuous⟩ ≫
       TopCat.ofHom ⟨modelBlocksHomeomorph ℤ μ k
          (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ)),
         (modelBlocksHomeomorph ℤ μ k
          (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ))).continuous⟩)
      (modelSupported ℤ (orderedModelCup ℤ μ k
        (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ)))) := by
  have hcmp := orderedCup_pullbacks_eq_of_factor_equalities ℤ μ
    (TopCat.ofHom ⟨affineChart (k+1) (k+1) le_rfl,
      affineChart_continuous (k+1) (k+1) le_rfl⟩)
    (TopCat.ofHom ⟨complexCoordinateBlocksHomeomorph (k+1),
      (complexCoordinateBlocksHomeomorph (k+1)).continuous⟩)
    k (projectiveCoordinateFactor (k+1) c)
    (rawGradedBlockFactor ℤ k (fun _ => 2) (fun _ => 2)
      (complexCoordinateModelClasses (k+1) c))
    (projectiveCoordinateFactor_chart_comparison k c)
  have hgs : complexCoordinateModelClasses (k+1) c = fun _ => g := funext hg
  rw [hgs] at hcmp
  rw [hcmp]
  change supportedPullback ℤ _
    (orderedCup ℤ μ k (fun j => supportedPullback ℤ
      (rawModelBlockProjection ℤ k (fun _ => (⟨2,g⟩ : ModelClass.{0,0} ℤ)) j)
      (modelSupported ℤ (⟨2,g⟩ : ModelClass.{0,0} ℤ)))) = _
  rw [orderedCup_rawModelBlocks, supportedPullback_comp]


/-- Exact positive model evaluation fixes the sign of the actual projective
coordinate product and hence of the ordinary top cup power. -/
lemma positiveDegreeTwoClass_topPower_eq_of_modelPositive
    (μ : NaturalRelativeCupProduct.{0,0} ℤ) (k : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace (k+1)))
    (hpos : ModelPositive (orderedModelCup ℤ μ k (fun _ : Fin (k+1) =>
      (⟨2,complexLineModelClass positiveComplexLineCohomologyClass⟩ : ModelClass.{0,0} ℤ)))) :
    homogeneousPower (k+1) C (positiveDegreeTwoClass k) (k+1) =
      ordinaryImage (localPair (Space (k+1)) (projectiveOrigin (k+1))) (2*(k+1))
        (positiveLocalCohomologyClass (k+1)) := by
  letI := C.gradedRing
  let g := complexLineModelClass positiveComplexLineCohomologyClass
  let c := fun j : Fin (k+1) => coordinateHyperplaneClass k j.castSucc
  let F := projectiveCoordinateFactor (k+1) c
  let A := orderedCup ℤ μ k F
  let B := orderedModelCup ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ))
  have hs : A.support = {projectiveOrigin (k+1)} := by
    change (orderedCup ℤ μ k F).support = _
    rw [orderedCup_support]
    exact firstCoordinateHyperplanes_intersection (k+1)
  have hd : A.degree = 2*(k+1) :=
    orderedCup_degree_eq_mul ℤ μ k 2 F (fun _ => rfl)
  have hb : B.degree = 2*(k+1) := constantTwo_modelCup_degree μ k g
  have hp : supportedOrdinary ℤ A =
      (DirectSum.of (H ℤ (projectiveSpace (k+1))) 2 (positiveDegreeTwoClass k))^(k+1) := by
    apply supportedOrdinary_orderedCup_eq_pow ℤ C μ k F
    intro j
    change DirectSum.of (H ℤ (projectiveSpace (k+1))) 2
      (ordinaryImage (coordinateHyperplanePair (k+1) j.castSucc) 2
        (coordinateHyperplaneClass k j.castSucc)) = _
    rw [coordinateHyperplaneClass_ordinaryImage]
  let f : P202Specs.SpheresDisks.simplexPair (2*(k+1)) ⟶
      (⟨projectiveSpace (k+1),A.supportᶜ⟩ : Pair) := {
    map := (positiveLocalSimplex (k+1)).map
    mapsTo := by
      intro x hx
      change positiveProjectiveSimplex (k+1) x ∉ A.support
      rw [hs]
      exact positiveProjectiveSimplex_ne_origin_on_boundary (k+1) x hx }
  let q : P202Specs.SpheresDisks.simplexPair (2*(k+1)) ⟶ modelPair.{0} B.degree :=
    castPositiveModelSimplex hb
  let t : (P202Specs.SpheresDisks.simplexPair (2*(k+1))).space ⟶
      TopCat.of (Fin (k+1) → ℂ) := TopCat.ofHom
    ⟨complexSimplexCoordinates (k+1), complexSimplexCoordinates_continuous (k+1)⟩
  have hchart := projectiveCoordinate_orderedCup_chart_model μ k c g (fun j => by
    change complexLineModelClass (relativePullback ℤ
      (complexProjectiveCoordinateLine (k+1) j) 2 (coordinateHyperplaneClass k j.castSucc)) = g
    rw [coordinateHyperplaneClass_complexLine])
  have hsimplex := congrArg (supportedPullback ℤ t) hchart
  simp only [supportedPullback_comp] at hsimplex
  have hleft : t ≫ TopCat.ofHom
      ⟨affineChart (k+1) (k+1) le_rfl,
       affineChart_continuous (k+1) (k+1) le_rfl⟩ = f.map := rfl
  have hright : t ≫ (TopCat.ofHom
      ⟨complexCoordinateBlocksHomeomorph (k+1),
       (complexCoordinateBlocksHomeomorph (k+1)).continuous⟩ ≫
      TopCat.ofHom ⟨modelBlocksHomeomorph ℤ μ k
          (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ)),
        (modelBlocksHomeomorph ℤ μ k
          (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ))).continuous⟩) = q.map := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change modelBlocksHomeomorph ℤ μ k (fun _ : Fin (k+1) => (⟨2,g⟩ : ModelClass.{0,0} ℤ))
        (complexCoordinateBlocksHomeomorph (k+1) (complexSimplexCoordinates (k+1) x)) =
      (modelDegreePairMap hb).map (ULift.up (positiveSimplexCoordinates (2*(k+1)) x))
    rw [modelDegreePairMap_apply]
    apply ULift.ext
    exact complexCoordinateBlocks_flatten_positiveSimplex μ k g x
  rw [hleft,hright] at hsimplex
  have he := relativePullbacks_eq_of_supportedPullbacks_eq ℤ
    (P202Specs.SpheresDisks.simplexPair (2*(k+1))) A (modelSupported ℤ B)
    f q hsimplex (2*(k+1)) hd hb
  have hvalue : relativeEvaluation (⟨projectiveSpace (k+1),A.supportᶜ⟩ : Pair) (2*(k+1))
      (castRelativeDegree ℤ hd A.value)
      (((relativeHomologyFunctor ℤ ℤ ((2*(k+1):ℕ):ℤ)).map f)
        (P202.SpheresDisks.affineClassLinear ℤ ℤ (2*(k+1)) 1)) = 1 := by
    rw [← relativeEvaluation_pullback f (2*(k+1))]
    change relativeEvaluation (P202Specs.SpheresDisks.simplexPair (2*(k+1))) (2*(k+1))
      (relativePullback ℤ f (2*(k+1)) (castRelativeDegree ℤ hd A.value))
      (P202.SpheresDisks.affineClassLinear ℤ ℤ (2*(k+1)) 1) = 1
    rw [castDegree_pullback_natural, he]
    change relativeEvaluation (P202Specs.SpheresDisks.simplexPair (2*(k+1))) (2*(k+1))
      (castRelativeDegree ℤ hb (relativePullback ℤ q B.degree B.value))
      (P202.SpheresDisks.affineClassLinear ℤ ℤ (2*(k+1)) 1) = 1
    have hn := castDegree_pullback_natural ℤ q hb B.value
    have hn' := congrArg (fun a : HR ℤ
        (P202Specs.SpheresDisks.simplexPair (2*(k+1))) (2*(k+1)) =>
      relativeEvaluation (P202Specs.SpheresDisks.simplexPair (2*(k+1))) (2*(k+1)) a
        (P202.SpheresDisks.affineClassLinear ℤ ℤ (2*(k+1)) 1)) hn.symm
    exact hn'.trans ((relativeEvaluation_pullback q (2*(k+1)) _ _).trans
      (modelPositive_cast_evaluation hb B.value hpos))
  exact topPower_eq_positiveImage_of_supported_value (k+1) C (positiveDegreeTwoClass k)
    A hs hd hp f (fun _ => rfl) hvalue

end P202.ComplexProjectiveRing
end

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace P202.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.ComplexProjectiveRing
open P202Specs.CupProduct P202Specs.LocalOrientation

/-- The top cup power has the exact positive complex orientation, for every
packaging of the actual singular cohomology cup ring. -/
lemma positiveDegreeTwoClass_topPower_eq (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace (m+1))) :
    homogeneousPower (m+1) C (positiveDegreeTwoClass m) (m+1) =
      ordinaryImage (localPair (Space (m+1)) (projectiveOrigin (m+1))) (2*(m+1))
        (positiveLocalCohomologyClass (m+1)) := by
  obtain ⟨μ⟩ := P202.RelativeCupProduct.product.{0,0} ℤ
  exact positiveDegreeTwoClass_topPower_eq_of_modelPositive μ m C
    (orderedModelComplex_positive μ m)

/-- The hyperplane class has all standard-subspace restrictions and positive
local and global fundamental-class evaluations, including the point. -/
theorem geometricGenerator : geometricGenerator_type :=
  geometricGenerator_of_topPower_identifications positiveDegreeTwoClass_topPower_eq

/-- The integral singular cup ring of each finite complex projective space is
the truncated polynomial ring on its complex-normal hyperplane Thom class. -/
theorem geometricPresentation : geometricPresentation_type :=
  geometricPresentation_of_geometricGenerator geometricGenerator

end P202.ComplexProjectiveRing
end
