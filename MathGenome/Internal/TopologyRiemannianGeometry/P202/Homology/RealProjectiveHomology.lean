import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.RealProjectiveHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.Degree
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.MayerVietoris
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularDegrees

/-! Work on the real projective portion of T21. All quotient-space statements
below concern the geometric antipodal quotient defined in the independent Specs.
The standard CW structure, antipodal degree, attaching coefficients and complete
integral homology table are proved for the actual quotient.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v w

namespace P202.Homology.RealProjectiveHomology
open P202Specs.RealProjectiveHomology P202Specs.SpheresDisks P202Specs.SingularChains

lemma antipodal_involutive (n : ℕ) : Function.Involutive (antipodal n) := by
  intro x
  apply Subtype.ext
  exact neg_neg x.val

lemma quotient_antipodal (m : ℕ) (x : sphere m) :
    quotientMap m (antipodal m x) = quotientMap m x := by
  apply Quotient.sound
  exact Or.inr rfl

def antipodalHomeomorph (m : ℕ) : sphere m ≃ₜ sphere m where
  toFun := antipodal m
  invFun := antipodal m
  left_inv := antipodal_involutive m
  right_inv := antipodal_involutive m
  continuous_toFun := (antipodal m).hom.continuous
  continuous_invFun := (antipodal m).hom.continuous

lemma quotientMap_saturation (m : ℕ) (U : Set (sphere m)) :
    quotientMap m ⁻¹' (quotientMap m '' U) = U ∪ antipodal m ⁻¹' U := by
  ext x
  change (∃ y ∈ U, quotientMap m y = quotientMap m x) ↔ x ∈ U ∨ antipodal m x ∈ U
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases Quotient.exact hxy with h | h
    · exact Or.inl ((Subtype.ext h : y = x) ▸ hy)
    · have heq : y = antipodal m x := Subtype.ext h
      exact Or.inr (heq ▸ hy)
  · rintro (hx | hx)
    · exact ⟨x, hx, rfl⟩
    · exact ⟨antipodal m x, hx, quotient_antipodal m x⟩

lemma quotientMap_isOpen (m : ℕ) : IsOpenMap (quotientMap m) := by
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (quotientMap m ⁻¹' (quotientMap m '' U))
  rw [quotientMap_saturation]
  exact hU.union (hU.preimage (antipodal m).hom.continuous)

instance projective_t2 (m : ℕ) : T2Space (Space m) := by
  apply (t2Space_iff_of_isOpenQuotientMap (π := quotientMap m)
    ⟨Quotient.mk_surjective, (quotientMap m).hom.continuous, quotientMap_isOpen m⟩).mpr
  have hrel : {q : sphere m × sphere m | quotientMap m q.1 = quotientMap m q.2} =
      {q : sphere m × sphere m | q.1.val = q.2.val} ∪
      {q : sphere m × sphere m | q.1.val = -q.2.val} := by
    ext q
    exact Quotient.eq
  rw [hrel]
  apply IsClosed.union
  · exact isClosed_eq (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)
  · exact isClosed_eq (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd).neg

lemma quotientMap_surjective (m : ℕ) : Function.Surjective (quotientMap m) :=
  Quotient.mk_surjective

lemma antipodal_zero_degree : P202Specs.Degree.degree 0 (antipodal 0) = -1 :=
  P202.Degree.interchangeDegree

lemma zeroSphere_quotient_eq (x : sphere 0) :
    quotientMap 0 x = quotientMap 0 (P202.Degree.pole 0) := by
  rcases P202.Degree.pole_exhaustive x with rfl | rfl
  · rfl
  · rw [← P202.Degree.interchange_pole_zero]
    exact quotient_antipodal 0 (P202.Degree.pole 0)

instance zero_subsingleton : Subsingleton (Space 0) := by
  refine ⟨?_⟩
  intro x y
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
      exact (zeroSphere_quotient_eq x).trans (zeroSphere_quotient_eq y).symm

/-- The two points in S^0 become a single point in the actual quotient. -/
def zeroHomeomorph : Space 0 ≃ₜ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := quotientMap 0 (P202.Degree.pole 0)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

instance projective_pathConnected (m : ℕ) : PathConnectedSpace (Space m) := by
  cases m with
  | zero => exact zeroHomeomorph.symm.pathConnectedSpace
  | succ m =>
    haveI := P202.SpheresDisks.sphere_pathConnected m
    exact (quotientMap_surjective (m+1)).pathConnectedSpace (quotientMap (m+1)).hom.continuous

/-- Degree-zero singular homology of every projective quotient. -/
def homologyZero (m : ℕ) : homology ℤ ℤ (projective m) 0 ≃ₗ[ℤ] ℤ := by
  let e := Classical.choice (P202.SingularDegreeZero.degreeZero ℤ ℤ (projective m))
  exact e.trans (Finsupp.uniqueLinearEquiv ℤ ℤ (Classical.arbitrary _))

lemma zero_homology_positive (j : ℕ) (hj : j ≠ 0) :
    IsZero (homology ℤ ℤ (projective 0) (j : ℤ)) := by
  let e := (homologyFunctor ℤ ℤ (j : ℤ)).mapIso (TopCat.isoOfHomeo (X := projective 0)
    (Y := P202Specs.SingularDegreeZero.point.{0}) zeroHomeomorph)
  exact e.isZero_iff.mpr (P202.SingularDegreeZero.pointOrdinaryOther ℤ ℤ (j : ℤ)
    (by exact_mod_cast hj))

lemma zero_homology_calculation : HomologyCalculation 0 := by
  intro j
  refine ⟨?_, ?_, ?_⟩
  · rintro (rfl | ⟨rfl, h⟩)
    · exact ⟨homologyZero 0⟩
    · exact ⟨homologyZero 0⟩
  · rintro ⟨h, h', _⟩
    omega
  · rintro ⟨h, _⟩
    exact zero_homology_positive j (fun hj => h (Or.inl hj))

/-- The dimension-zero case needs no cellular or attaching-degree premise. -/
theorem pointCase : Expected.pointCase :=
  ⟨⟨zeroHomeomorph⟩, zero_homology_calculation⟩

/-- The boundary coefficient vanishes in odd degrees, including degree one. -/
lemma incidence_odd {j : ℕ} (hj : Odd j) : incidence j = 0 := by
  simp [incidence, hj.neg_one_pow]

lemma incidence_even {j : ℕ} (hj : Even j) : incidence j = 2 := by
  simp [incidence, hj.neg_one_pow]

lemma incidence_one : incidence 1 = 0 := by norm_num [incidence]

lemma incidence_consecutive (j : ℕ) : incidence j * incidence (j+1) = 0 := by
  rcases Nat.even_or_odd j with h | h
  · rw [incidence_odd (j := j+1) (h.add_odd (by decide : Odd 1)), mul_zero]
  · rw [incidence_odd h, zero_mul]

section Algebra

/-- In an even positive degree, injectivity of multiplication by two kills
homology. This lemma uses the actual categorical homology object. -/
lemma homology_isZero_of_injective (S : ShortComplex (ModuleCat.{0} ℤ))
    (hg : Function.Injective S.g) : IsZero S.homology := by
  apply S.exact_iff_isZero_homology.mp
  apply S.moduleCat_exact_iff.mpr
  intro x hx
  have hx0 : x = 0 := hg (hx.trans (map_zero S.g.hom).symm)
  exact ⟨0, by simp [hx0]⟩

/-- The degree-zero and odd top-dimensional cases. -/
def homologyCoordinateOfZeroMaps (S : ShortComplex (ModuleCat.{0} ℤ))
    (e : S.X₂ ≃ₗ[ℤ] ℤ) (hf : S.f = 0) (hg : S.g = 0) :
    S.homology ≃ₗ[ℤ] ℤ :=
  ((ShortComplex.LeftHomologyData.ofZeros S hf hg).homologyIso).toLinearEquiv.trans e

/-- A two-multiple image and a zero outgoing differential give Z/2. The
hypothesis describes the entire image; it does not assume the homology. -/
def homologyCoordinateModTwo (S : ShortComplex (ModuleCat.{0} ℤ))
    (e : S.X₂ ≃ₗ[ℤ] ℤ) (hg : S.g = 0)
    (hrange : ∀ x : S.X₂, (∃ a : S.X₁, S.f a = x) ↔ ∃ a : ℤ, e x = 2 * a) :
    S.homology ≃ₗ[ℤ] ZMod 2 := by
  let q : S.X₂ →ₗ[ℤ] ZMod 2 := {
    toFun := fun x => (e x : ZMod 2)
    map_add' := by intros; simp
    map_smul' := by intros; simp }
  have hq : ∀ x, q x = 0 ↔ ∃ a : S.X₁, S.f a = x := by
    intro x
    change (e x : ZMod 2) = 0 ↔ _
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hrange]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
  have hcomp : S.f ≫ ModuleCat.ofHom q = 0 := by
    ext a
    exact (hq _).mpr ⟨a, rfl⟩
  let T := ShortComplex.mk S.f (ModuleCat.ofHom q) hcomp
  have hT : T.Exact := T.moduleCat_exact_iff.mpr (fun x hx => (hq x).mp hx)
  haveI : Epi T.g := (ModuleCat.epi_iff_surjective T.g).mpr (by
    change Function.Surjective q
    intro a
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective a
    refine ⟨e.symm b, ?_⟩
    change (e (e.symm b) : ZMod 2) = a
    simpa using hb)
  exact ((ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork S hg
    (CokernelCofork.ofπ T.g hcomp) hT.gIsCokernel).homologyIso).toLinearEquiv

/-- Algebraic computation for a finite one-generator chain complex. The
coordinates and differential equation are hypotheses here; no assertion that
projective space already has these coordinates is made by this lemma. -/
lemma positiveHomologyOfCoefficients
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (m : ℕ)
    (e : ∀ j, j ≤ m → K.X j ≃ₗ[ℤ] ℤ)
    (hupper : ∀ j, m < j → IsZero (K.X j))
    (hd : ∀ (n : ℕ) (h : n+1 ≤ m) (z : K.X (n+1)),
      e n (by omega) (K.d (n+1) n z) = incidence (n+1) * e (n+1) h z)
    (n : ℕ) :
    ((n+1 = m ∧ Odd (n+1)) → Nonempty (K.homology (n+1) ≃ₗ[ℤ] ℤ)) ∧
    ((n+1 < m ∧ Odd (n+1)) → Nonempty (K.homology (n+1) ≃ₗ[ℤ] ZMod 2)) ∧
    ((m < n+1 ∨ Even (n+1)) → IsZero (K.homology (n+1))) := by
  let S := K.sc' (n+2) (n+1) n
  let hS : K.homology (n+1) ≅ S.homology :=
    K.homologyIsoSc' (n+2) (n+1) n
      ((ComplexShape.down ℕ).prev_eq' (by rfl))
      ((ComplexShape.down ℕ).next_eq' (by rfl))
  have hgzero (h : n+1 ≤ m) (ho : Odd (n+1)) : S.g = 0 := by
    ext x
    apply (e n (by omega)).injective
    change e n _ (K.d (n+1) n x) = e n _ 0
    rw [hd n h, incidence_odd ho, zero_mul, map_zero]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨htop, ho⟩
    have h : n+1 ≤ m := by omega
    have hfzero : S.f = 0 := (hupper (n+2) (by omega)).eq_of_src _ _
    exact ⟨hS.toLinearEquiv.trans
      (homologyCoordinateOfZeroMaps S (e (n+1) h) hfzero (hgzero h ho))⟩
  · rintro ⟨hint, ho⟩
    have h : n+1 ≤ m := by omega
    have hnext : n+2 ≤ m := by omega
    have hev : Even (n+2) := ho.add_odd (by decide : Odd 1)
    have hrange : ∀ x : S.X₂, (∃ a : S.X₁, S.f a = x) ↔
        ∃ a : ℤ, e (n+1) h x = 2*a := by
      intro x
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨e (n+2) hnext a, by
          change e (n+1) h (K.d (n+2) (n+1) a) = _
          rw [hd (n+1) hnext, incidence_even hev]⟩
      · rintro ⟨a, ha⟩
        refine ⟨(e (n+2) hnext).symm a, (e (n+1) h).injective ?_⟩
        change e (n+1) h (K.d (n+2) (n+1) ((e (n+2) hnext).symm a)) = _
        rw [hd (n+1) hnext, incidence_even hev, LinearEquiv.apply_symm_apply, ha]
    exact ⟨hS.toLinearEquiv.trans
      (homologyCoordinateModTwo S (e (n+1) h) (hgzero h ho) hrange)⟩
  · intro h
    by_cases htop : m < n+1
    · exact hS.isZero_iff.mpr
        (S.exact_iff_isZero_homology.mp (S.exact_of_isZero_X₂ (hupper _ htop)))
    · have hev : Even (n+1) := h.resolve_left htop
      have hle : n+1 ≤ m := by omega
      have hg : Function.Injective S.g := by
        intro a b hab
        apply (e (n+1) hle).injective
        have hh := congrArg (e n (by omega)) hab
        change e n _ (K.d (n+1) n a) = e n _ (K.d (n+1) n b) at hh
        rw [hd n hle, hd n hle, incidence_even hev] at hh
        omega
      exact hS.isZero_iff.mpr (homology_isZero_of_injective S hg)

end Algebra

section Hemisphere
open P202.Cellular

lemma hemisphereVector_norm_sq (m j : ℕ) (hj : j ≤ m) (x : Disk j) :
    ‖hemisphereVector m j x‖ ^ 2 = ‖x.val‖ ^ 2 +
      (Real.sqrt (1 - ‖x.val‖ ^ 2)) ^ 2 := by
  induction m, hj using Nat.le_induction with
  | base =>
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
    simp [hemisphereVector, EuclideanSpace.real_norm_sq_eq]
  | succ m hm ih =>
    calc
      ‖hemisphereVector (m+1) j x‖ ^ 2 = ‖hemisphereVector m j x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc,
          EuclideanSpace.real_norm_sq_eq]
        have hnot : ¬ m+1 < j := by omega
        have hneq : m+1 ≠ j := by omega
        simp only [hemisphereVector, PiLp.toLp_apply, Fin.val_last,
          Fin.val_castSucc, hnot, hneq, dite_false, ite_false, zero_pow (by decide : 2 ≠ 0), add_zero]
      _ = _ := ih

lemma hemisphereVector_norm (m j : ℕ) (hj : j ≤ m) (x : Disk j) :
    ‖hemisphereVector m j x‖ = 1 := by
  have hx : ‖x.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  have hx' : 0 ≤ 1 - ‖x.val‖ ^ 2 := by nlinarith [norm_nonneg x.val]
  have hs := hemisphereVector_norm_sq m j hj x
  rw [Real.sq_sqrt hx'] at hs
  nlinarith [norm_nonneg (hemisphereVector m j x)]

lemma hemisphereVector_continuous (m j : ℕ) :
    Continuous (hemisphereVector m j) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  dsimp [hemisphereVector]
  split_ifs
  · exact (PiLp.continuous_apply 2 _ _).comp continuous_subtype_val
  · fun_prop
  · exact continuous_const

/-- The actual upper-hemisphere parametrization into the geometric sphere. -/
def hemisphere (m j : ℕ) (hj : j ≤ m) : C(Disk j, sphere m) where
  toFun x := ⟨hemisphereVector m j x, by simpa using hemisphereVector_norm m j hj x⟩
  continuous_toFun := (hemisphereVector_continuous m j).subtype_mk _

/-- The proposed characteristic maps into the actual quotient; proving their
CW axioms remains a separate geometric obligation. -/
def standardCharacteristic (m j : ℕ) (hj : j ≤ m) : C(Disk j, Space m) :=
  (quotientMap m).hom.comp (hemisphere m j hj)

/-- On the boundary the final coordinate is zero, so the attaching map is
the antipodal sphere quotient in the preceding coordinate subspace. -/
lemma hemisphere_boundary_coordinate (m j : ℕ) (hj : j ≤ m) (x : Sphere j) :
    (hemisphere m j hj (boundaryInclusion j x)).val ⟨j, by omega⟩ = 0 := by
  have hx : ‖x.val‖ = 1 := by simpa using x.property
  simp [hemisphere, hemisphereVector, boundaryInclusion, hx]

/-- The closed characteristic disks are now defined without a CW certificate. -/
def standardCellStructure (m : ℕ) : CellStructure (Space m) where
  Cell j := { i : Unit // j ≤ m }
  characteristic j c := standardCharacteristic m j c.property

lemma hemisphere_last_pos (m j : ℕ) (hj : j ≤ m) (x : OpenDisk j) :
    0 < (hemisphere m j hj (interiorInclusion j x)).val ⟨j, by omega⟩ := by
  have hx : ‖x.val‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using x.property
  have hs : 0 < Real.sqrt (1 - ‖x.val‖ ^ 2) := Real.sqrt_pos.mpr (by
    nlinarith [norm_nonneg x.val])
  simpa [hemisphere, hemisphereVector, interiorInclusion] using hs

/-- No two interior points of one disk are identified by the quotient. -/
lemma characteristic_interior_injective (m j : ℕ) (hj : j ≤ m) :
    Function.Injective (fun x : OpenDisk j =>
      standardCharacteristic m j hj (interiorInclusion j x)) := by
  intro x y hxy
  change quotientMap m (hemisphere m j hj (interiorInclusion j x)) =
    quotientMap m (hemisphere m j hj (interiorInclusion j y)) at hxy
  rcases Quotient.exact hxy with h | h
  · apply Subtype.ext
    ext k
    have hk := congrArg (fun v : EuclideanSpace ℝ (Fin (m+1)) => v ⟨k.val, by omega⟩) h
    simpa [hemisphere, hemisphereVector, interiorInclusion, k.is_lt] using hk
  · have hpos := hemisphere_last_pos m j hj x
    have hpos' := hemisphere_last_pos m j hj y
    have hh := congrArg (fun v : EuclideanSpace ℝ (Fin (m+1)) => v ⟨j, by omega⟩) h
    simp only [PiLp.neg_apply] at hh
    linarith

/-- Boundary points related by negation have identical attaching images. -/
lemma characteristic_boundary_antipodal (m j : ℕ) (hj : j ≤ m) (x y : Sphere j)
    (hxy : x.val = -y.val) :
    standardCharacteristic m j hj (boundaryInclusion j x) =
      standardCharacteristic m j hj (boundaryInclusion j y) := by
  apply Quotient.sound
  apply Or.inr
  have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hy : ‖y.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  ext k
  change (hemisphereVector m j (boundaryInclusion j x)) k =
    -(hemisphereVector m j (boundaryInclusion j y)) k
  simp only [hemisphereVector, boundaryInclusion, PiLp.toLp_apply]
  split_ifs with h h'
  · exact congrArg (fun v : EuclideanSpace ℝ (Fin j) => v ⟨k.val, h⟩) hxy
  · simp [hx, hy]
  · simp

/-- The two endpoint images of the one-cell coincide in every ambient RP^m. -/
lemma characteristic_endpoints_coincide (m : ℕ) (hm : 1 ≤ m) :
    standardCharacteristic m 1 hm (boundaryInclusion 1 (P202.Degree.pole 0)) =
      standardCharacteristic m 1 hm (boundaryInclusion 1 (P202.Degree.pole 1)) := by
  apply characteristic_boundary_antipodal
  exact (congrArg Subtype.val P202.Degree.interchange_pole_one).symm

lemma hemisphere_top_preimage (m : ℕ) (y : sphere m)
    (hy : 0 ≤ y.val (Fin.last m)) : ∃ x : Disk m, hemisphere m m le_rfl x = y := by
  let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun k => y.val k.castSucc)
  have hy_norm : ‖y.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  have hv : ‖v‖ ^ 2 + (y.val (Fin.last m)) ^ 2 = 1 := by
    have hh := EuclideanSpace.real_norm_sq_eq y.val
    rw [Fin.sum_univ_castSucc, hy_norm] at hh
    simpa only [EuclideanSpace.real_norm_sq_eq, v, PiLp.toLp_apply, one_pow] using hh.symm
  have hvle : ‖v‖ ≤ 1 := by nlinarith [norm_nonneg v, sq_nonneg (y.val (Fin.last m))]
  let x : Disk m := ⟨v, by simpa only [Metric.mem_closedBall, dist_zero_right] using hvle⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  ext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · change (hemisphereVector m m x) (Fin.last m) = _
    have heq : 1 - ‖v‖ ^ 2 = (y.val (Fin.last m)) ^ 2 := by linarith
    simpa [hemisphereVector, x, heq, Real.sqrt_sq hy]
  · simp [hemisphere, hemisphereVector, x, v]

/-- Every projective point has a representative in the closed top hemisphere. -/
lemma standardCharacteristic_top_surjective (m : ℕ) :
    Function.Surjective (standardCharacteristic m m le_rfl) := by
  intro z
  obtain ⟨y, rfl⟩ := quotientMap_surjective m z
  by_cases hy : 0 ≤ y.val (Fin.last m)
  · obtain ⟨x, hx⟩ := hemisphere_top_preimage m y hy
    exact ⟨x, congrArg (quotientMap m) hx⟩
  · have hy' : 0 ≤ (antipodal m y).val (Fin.last m) := by
      change 0 ≤ -(y.val (Fin.last m))
      linarith
    obtain ⟨x, hx⟩ := hemisphere_top_preimage m (antipodal m y) hy'
    exact ⟨x, (congrArg (quotientMap m) hx).trans (quotient_antipodal m y)⟩

lemma standardCharacteristic_top_quotient (m : ℕ) :
    Topology.IsQuotientMap (standardCharacteristic m m le_rfl) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (standardCharacteristic_top_surjective m) (standardCharacteristic m m le_rfl).continuous

/-- The characteristic maps already give the correct weak topology on the
actual quotient, before verifying the remaining CW axioms. -/
lemma standardCellStructure_weak_topology (m : ℕ) (A : Set (Space m)) :
    IsClosed A ↔ ∀ (j : ℕ) (c : (standardCellStructure m).Cell j),
      IsClosed ((standardCellStructure m).characteristic j c ⁻¹' A) := by
  constructor
  · intro h j c
    exact h.preimage ((standardCellStructure m).characteristic j c).continuous
  · intro h
    exact (standardCharacteristic_top_quotient m).isClosed_preimage.mp (h m ⟨(), le_rfl⟩)

end Hemisphere

section StandardCells
open P202.Cellular _root_.Topology Set

/-- On the open positive hemisphere, the antipodal quotient is an embedding. -/
lemma quotient_positive_embedding (m : ℕ) (k : Fin (m+1)) :
    IsEmbedding (fun y : {y : sphere m // 0 < y.val k} => quotientMap m y.val) := by
  apply IsOpenEmbedding.isEmbedding
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (quotientMap m).hom.continuous.comp continuous_subtype_val
  · intro x y h
    apply Subtype.ext
    rcases Quotient.exact h with h | h
    · exact Subtype.ext h
    · have hh := congrArg (fun v : EuclideanSpace ℝ (Fin (m+1)) => v k) h
      simp only [PiLp.neg_apply] at hh
      have hx := x.property
      have hy := y.property
      linarith
  · exact (quotientMap_isOpen m).domRestrict
      (isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ k).comp continuous_subtype_val))

/-- Truncating a positive hemisphere chart gives back its disk coordinates. -/
lemma characteristic_interior_embedding (m j : ℕ) (hj : j ≤ m) :
    IsEmbedding (fun x : OpenDisk j =>
      standardCharacteristic m j hj (interiorInclusion j x)) := by
  let U := {y : sphere m // 0 < y.val (⟨j, by omega⟩ : Fin (m+1))}
  let h : OpenDisk j → U := fun x =>
    ⟨hemisphere m j hj (interiorInclusion j x), hemisphere_last_pos m j hj x⟩
  have hh : Continuous h := by
    exact ((hemisphere m j hj).continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _
  let p : U → EuclideanSpace ℝ (Fin j) := fun y =>
    WithLp.toLp 2 (fun k => y.val.val ⟨k.val, by omega⟩)
  have hp : Continuous p := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro k
    exact (PiLp.continuous_apply 2 _ _).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hid : p ∘ h = (Subtype.val : OpenDisk j → EuclideanSpace ℝ (Fin j)) := by
    funext x
    ext k
    simp [p, h, hemisphere, hemisphereVector, interiorInclusion, k.is_lt]
  have he : IsEmbedding h := .of_comp hh hp (hid ▸ IsEmbedding.subtypeVal)
  exact (quotient_positive_embedding m ⟨j, by omega⟩).comp he

lemma characteristic_distinct_dimensions (m j k : ℕ) (hj : j ≤ m) (hk : k ≤ m)
    (hjk : j < k) (x : OpenDisk j) (y : OpenDisk k) :
    standardCharacteristic m j hj (interiorInclusion j x) ≠
      standardCharacteristic m k hk (interiorInclusion k y) := by
  intro h
  have hz : (hemisphere m j hj (interiorInclusion j x)).val ⟨k, by omega⟩ = 0 := by
    simp [hemisphere, hemisphereVector, show ¬ k < j by omega, show k ≠ j by omega]
  have hy := hemisphere_last_pos m k hk y
  rcases Quotient.exact h with h | h
  · have hh := congrArg (fun v : EuclideanSpace ℝ (Fin (m+1)) => v ⟨k, by omega⟩) h
    rw [hz] at hh
    linarith
  · have hh := congrArg (fun v : EuclideanSpace ℝ (Fin (m+1)) => v ⟨k, by omega⟩) h
    simp only [PiLp.neg_apply, hz] at hh
    linarith

lemma standardCellStructure_disjoint (m : ℕ) :
    letI := standardCellStructure m
    (univ : Set (Σ j, Cell (Space m) j)).PairwiseDisjoint
      (fun c => openCell (Space m) c.1 c.2) := by
  letI := standardCellStructure m
  intro a _ b _ hab
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have hne : a.1 ≠ b.1 := by
    intro h
    apply hab
    cases a with | mk j a =>
      cases b with | mk k b =>
        dsimp at h
        subst k
        congr 1
        apply Subtype.ext
        exact Subsingleton.elim _ _
  rcases lt_or_gt_of_ne hne with h | h
  · exact characteristic_distinct_dimensions m _ _ a.2.property b.2.property h x y
      (hx.trans hy.symm)
  · exact characteristic_distinct_dimensions m _ _ b.2.property a.2.property h y x
      (hy.trans hx.symm)

/-- A boundary point of the j+1 disk is represented by a point of the j disk,
using the top hemisphere parametrization in its coordinate subsphere. -/
lemma characteristic_boundary_reduction (m j : ℕ) (hj : j+1 ≤ m)
    (x : Sphere (j+1)) (z : Disk j) (hz : hemisphere j j le_rfl z = x) :
    standardCharacteristic m (j+1) hj (boundaryInclusion (j+1) x) =
      standardCharacteristic m j (by omega) z := by
  apply Quotient.sound
  apply Or.inl
  have hx : ‖x.val‖ = 1 := by simpa using x.property
  ext k
  by_cases hk : k.val < j+1
  · have hh := congrArg (fun y : sphere j => y.val ⟨k.val, hk⟩) hz
    simpa [hemisphere, hemisphereVector, boundaryInclusion, hk, show k.val ≤ j by omega, hx] using hh.symm
  · simp [hemisphere, hemisphereVector, boundaryInclusion, hk, hx, show ¬ k.val ≤ j by omega,
      show ¬ k.val < j by omega, show k.val ≠ j by omega]

lemma characteristic_boundary_lower (m j : ℕ) (hj : j+1 ≤ m)
    (x : Sphere (j+1)) :
    ∃ z : Disk j, standardCharacteristic m (j+1) hj (boundaryInclusion (j+1) x) =
      standardCharacteristic m j (by omega) z := by
  by_cases hx : 0 ≤ x.val (Fin.last j)
  · obtain ⟨z, hz⟩ := hemisphere_top_preimage j x hx
    exact ⟨z, characteristic_boundary_reduction m j hj x z hz⟩
  · have hx' : 0 ≤ (antipodal j x).val (Fin.last j) := by
      change 0 ≤ -(x.val (Fin.last j))
      linarith
    obtain ⟨z, hz⟩ := hemisphere_top_preimage j (antipodal j x) hx'
    refine ⟨z, ?_⟩
    calc
      _ = standardCharacteristic m (j+1) hj
          (boundaryInclusion (j+1) (antipodal j x)) := by
        apply characteristic_boundary_antipodal
        exact (neg_neg x.val).symm
      _ = _ := characteristic_boundary_reduction m j hj (antipodal j x) z hz

/-- Each closed disk is the union of the indicated open cell and lower cells. -/
lemma characteristic_point_in_cell (m j : ℕ) (hj : j ≤ m) (x : Disk j) :
    ∃ (k : ℕ) (hk : k ≤ j) (z : OpenDisk k),
      standardCharacteristic m j hj x =
        standardCharacteristic m k (hk.trans hj) (interiorInclusion k z) := by
  induction j with
  | zero =>
    have hx : ‖x.val‖ < 1 := by
      have hzero : x.val = 0 := Subsingleton.elim _ _
      simp [hzero]
    exact ⟨0, le_rfl, ⟨x.val, by simpa using hx⟩, rfl⟩
  | succ j ih =>
    have hx : ‖x.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    rcases lt_or_eq_of_le hx with h | h
    · exact ⟨j+1, le_rfl, ⟨x.val, by simpa using h⟩, rfl⟩
    · let y : Sphere (j+1) := ⟨x.val, by simpa using h⟩
      obtain ⟨z, hz⟩ := characteristic_boundary_lower m j hj y
      obtain ⟨k, hk, w, hw⟩ := ih (by omega) z
      exact ⟨k, by omega, w, hz.trans hw⟩

lemma standardCellStructure_cover (m : ℕ) :
    letI := standardCellStructure m
    ⋃ (j : ℕ) (c : Cell (Space m) j), openCell (Space m) j c = univ := by
  letI := standardCellStructure m
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨x, rfl⟩ := standardCharacteristic_top_surjective m y
  obtain ⟨k, hk, z, hz⟩ := characteristic_point_in_cell m m le_rfl x
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨(), hk⟩, ⟨z, hz.symm⟩⟩⟩

lemma standardCellStructure_boundary (m : ℕ) :
    letI := standardCellStructure m
    ∀ j (c : Cell (Space m) j),
      MapsTo (boundaryMap (Space m) j c) univ (skeletonLT (Space m) j) := by
  letI := standardCellStructure m
  intro j c x _
  cases j with
  | zero =>
    have hx : ‖x.val‖ = 1 := by simpa using x.property
    have hz : x.val = 0 := Subsingleton.elim _ _
    simp [hz] at hx
  | succ j =>
    obtain ⟨z, hz⟩ := characteristic_boundary_lower m j c.property x
    obtain ⟨k, hk, w, hw⟩ := characteristic_point_in_cell m j (by have := c.property; omega) z
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨by omega,
      mem_iUnion.mpr ⟨⟨(), by have := c.property; omega⟩, ⟨w, (hz.trans hw).symm⟩⟩⟩⟩

lemma standardCellStructure_finite (m : ℕ) :
    Finite (Σ j, (standardCellStructure m).Cell j) := by
  apply Finite.of_injective
    (fun c : Σ j, (standardCellStructure m).Cell j =>
      (⟨c.1, Nat.lt_succ_of_le c.2.property⟩ : Fin (m+1)))
  intro a b h
  have hab : a.1 = b.1 := congrArg Fin.val h
  cases a with | mk j a =>
    cases b with | mk k b =>
      dsimp at hab
      subst k
      congr 1
      apply Subtype.ext
      exact Subsingleton.elim _ _

lemma standardCellStructure_closure_finite (m : ℕ) :
    letI := standardCellStructure m
    ∀ j (c : Cell (Space m) j), ∃ F : Finset (Σ k, Cell (Space m) k),
      closedCell (Space m) j c ⊆ ⋃ d ∈ F, openCell (Space m) d.1 d.2 := by
  classical
  letI := standardCellStructure m
  haveI := standardCellStructure_finite m
  letI := Fintype.ofFinite (Σ k, Cell (Space m) k)
  intro j c
  refine ⟨Finset.univ, ?_⟩
  intro y _
  have hy : y ∈ ⋃ (k : ℕ) (d : Cell (Space m) k), openCell (Space m) k d := by
    rw [standardCellStructure_cover m]
    trivial
  obtain ⟨k, hy⟩ := mem_iUnion.mp hy
  obtain ⟨d, hy⟩ := mem_iUnion.mp hy
  exact mem_iUnion.mpr ⟨⟨k,d⟩, mem_iUnion.mpr ⟨Finset.mem_univ _, hy⟩⟩

/-- The standard finite CW structure on the actual antipodal quotient. -/
def standardCW (m : ℕ) : CWStructure (Space m) := by
  letI := standardCellStructure m
  exact P202.Topology.cwStructureOfWeak (X := Space m)
    (fun j c => characteristic_interior_embedding m j c.property)
    (standardCellStructure_disjoint m) (standardCellStructure_cover m)
    (standardCellStructure_boundary m) (standardCellStructure_closure_finite m)
    (standardCellStructure_weak_topology m)

lemma standardCW_standard (m : ℕ) : StandardCW m (standardCW m) := by
  refine ⟨fun _ => Equiv.refl _, ?_⟩
  intro j c x
  exact ⟨hemisphere m j c.property x, rfl, rfl⟩

/-- Existence of the standard one-cell-per-degree CW model, independently of
its still-uncomputed differential. -/
theorem standardCellModel (m : ℕ) :
    ∃ C : CWStructure (Space m), StandardCW m C :=
  ⟨standardCW m, standardCW_standard m⟩

end StandardCells

section Cellular
open P202.Cellular P202Specs.CellularChains P202Specs.CellularDegrees
open P202Specs.RelativeSingularChains
variable {m : ℕ} [C : CWStructure (Space m)]

/-- There is at most one cell in each degree for the specified label system. -/
lemma cell_subsingleton
    (labels : ∀ j, Cell (Space m) j ≃ { i : Unit // j ≤ m }) (j : ℕ) :
    Subsingleton (Cell (Space m) j) :=
  ⟨fun a b => (labels j).injective (Subsingleton.elim _ _)⟩

/-- With one vertex the signed endpoints of every characteristic interval
cancel, for every class of the relative disk group. -/
lemma cellClass_boundary_one_zero (hstd : StandardCW m C)
    (c : Cell (Space m) 1)
    (a : relativeHomology ℤ ℤ (referenceDiskPair.{0} 1) 1) :
    differential (Space m) ℤ ℤ 0 (cellClass (Space m) ℤ ℤ 1 c a) = 0 := by
  obtain ⟨labels, _⟩ := hstd
  haveI := cell_subsingleton labels 0
  obtain ⟨h⟩ := P202.Homology.CellularDegrees.intervalParametrization_nonempty
  obtain ⟨g, e, hz, he, hg, hboundary⟩ :=
    P202.Homology.CellularDegrees.intervalCellBoundary (Space m) ℤ ℤ h
  obtain ⟨vfinal, vinitial, hv, hw, hd⟩ := hboundary c
  apply e.injective
  rw [map_zero]
  have hsame : vfinal = vinitial := Subsingleton.elim _ _
  simpa only [LinearEquiv.apply_symm_apply, hsame, sub_self] using hd (g.symm a)

/-- The degree-one cellular differential really is zero, independently of
all orientation choices. This includes the coincident-endpoint case. -/
lemma differential_one_zero (hstd : StandardCW m C) :
    differential (Space m) ℤ ℤ 0 = 0 := by
  obtain ⟨labels, hchar⟩ := hstd
  haveI := cell_subsingleton labels 1
  ext z
  by_cases hm : 1 ≤ m
  · obtain ⟨g⟩ :=
      (P202.Homology.DiskBridge.referenceDiskHomology ℤ ℤ 1 1).1 rfl
    let e := P202.Homology.orientedCellEquiv (Space m) ℤ ℤ 1 g.symm
    let c := (labels 1).symm ⟨(), hm⟩
    let a := e z c
    have hz : cellClass (Space m) ℤ ℤ 1 c (g.symm a) = z := by
      apply e.injective
      change P202.Homology.orientedCellEquiv (Space m) ℤ ℤ 1 g.symm
          (cellClass (Space m) ℤ ℤ 1 c (g.symm a)) = e z
      rw [cellClass, P202.Homology.orientedCellEquiv_characteristic]
      ext d
      have hd : d = c := Subsingleton.elim _ _
      subst d
      simp [a]
    rw [← hz]
    exact cellClass_boundary_one_zero ⟨labels, hchar⟩ c (g.symm a)
  · haveI : IsEmpty (Cell (Space m) 1) := ⟨fun c => hm (labels 1 c).property⟩
    obtain ⟨e⟩ := P202.Homology.cellularCellGroups (Space m) ℤ ℤ 1
    have hz : z = 0 := e.injective (Subsingleton.elim _ _)
    simp [hz]

/-- For projective dimensions zero and one, there are no higher source cells;
the endpoint calculation therefore gives the entire cellular differential. -/
lemma cellularCalculation_low_dimension (hm : m ≤ 1) (hstd : StandardCW m C) :
    CellularCalculation m C := by
  let g (j : ℕ) : ℤ ≃ₗ[ℤ] relativeHomology ℤ ℤ (referenceDiskPair.{0} j) (j : ℤ) :=
    (Classical.choice ((P202.Homology.DiskBridge.referenceDiskHomology ℤ ℤ j j).1 rfl)).symm
  let e (j : ℕ) := P202.Homology.orientedCellEquiv (Space m) ℤ ℤ j (g j)
  refine ⟨g, e, ?_, ?_⟩
  · intro j c a
    exact P202.Homology.orientedCellEquiv_characteristic (Space m) ℤ ℤ j (g j) c a
  · intro n c d a
    cases n with
    | zero =>
      rw [differential_one_zero hstd]
      simp [incidence, e]
    | succ n =>
      obtain ⟨labels, _⟩ := hstd
      have hc := (labels (n+1+1) c).property
      omega

/-- Geometric choices used to compare adjacent relative disk orientations.
No equation about a cellular differential is included in this data. -/
structure AttachingCharts (n : ℕ) where
  boundaryPoint : (referenceDiskPair.{0} n).sub
  source : (referenceDiskPair.{0} (n+1)).sub ≃ₜ
    P202Specs.CellularDegrees.liftedSphere.{0} n
  target : P202Specs.GoodPairQuotient.quotientSpace (referenceDiskPair.{0} n) ≃ₜ
    P202Specs.CellularDegrees.liftedSphere.{0} n

lemma attachingCharts_nonempty (n : ℕ) (hn : 0 < n) : Nonempty (AttachingCharts n) := by
  obtain ⟨⟨b⟩, ⟨hS⟩, ⟨hT⟩, _⟩ :=
    P202.Homology.CellularDegrees.chartDataExist ℤ ℤ n hn
  exact ⟨⟨b, hS, hT⟩⟩

/-- An initial relative disk orientation, before imposing compatibility
with any adjacent dimension. -/
def diskOrientation (j : ℕ) :
    ℤ ≃ₗ[ℤ] relativeHomology ℤ ℤ (referenceDiskPair.{0} j) (j : ℤ) :=
  (Classical.choice ((P202.Homology.DiskBridge.referenceDiskHomology ℤ ℤ j j).1 rfl)).symm

/-- Choose the source orientation in each higher degree from the preceding
target orientation through the disk quotient and boundary charts. Degree one
is independent because its two endpoint contributions cancel. -/
def coherentDiskOrientations (D : ∀ n, 0 < n → AttachingCharts n) :
    ∀ j, ℤ ≃ₗ[ℤ] relativeHomology ℤ ℤ (referenceDiskPair.{0} j) (j : ℤ) :=
  Nat.rec (diskOrientation 0) (fun n g =>
    if hn : 0 < n then
      P202.Homology.CellularDegrees.AttachingCalculation.nextDiskOrientation ℤ ℤ n hn
        (D n hn).boundaryPoint (D n hn).source (D n hn).target g
    else diskOrientation (n+1))

lemma coherentDiskOrientations_succ (D : ∀ n, 0 < n → AttachingCharts n)
    (n : ℕ) (hn : 0 < n) :
    coherentDiskOrientations D (n+1) =
      P202.Homology.CellularDegrees.AttachingCalculation.nextDiskOrientation ℤ ℤ n hn
        (D n hn).boundaryPoint (D n hn).source (D n hn).target
        (coherentDiskOrientations D n) := by
  simp only [coherentDiskOrientations, Nat.rec_add_one, dite_eq_left hn]

open Classical in
/-- A degree calculation for the genuine attaching-collapse maps suffices
for a simultaneous cellular calculation. The recurrence proves the required
compatibility of all disk generators; it does not assume that compatibility. -/
lemma cellularCalculation_of_chartDegrees (hstd : StandardCW m C)
    (D : ∀ n, 0 < n → AttachingCharts n)
    (hdegree : ∀ (n : ℕ) (hn : 0 < n)
      (c : Cell (Space m) (n+1)) (d : Cell (Space m) n)
      (q : skeletalPair (Space m) n ⟶
        P202Specs.GoodPairQuotient.quotientPair (referenceDiskPair.{0} n)),
      (∀ (k : Cell (Space m) n) (x : (referenceDiskPair.{0} n).space),
        q.map ((characteristicPairMap n k).map x) =
          if k = d then P202Specs.GoodPairQuotient.quotientProjection _ x
          else P202Specs.GoodPairQuotient.quotientProjection _ (D n hn).boundaryPoint.val) →
      P202Specs.Degree.degree n (chartAttachingMap (Space m) n
        (D n hn).source (D n hn).target q c) = incidence (n+1)) :
    CellularCalculation m C := by
  classical
  let g := coherentDiskOrientations D
  let e (j : ℕ) := P202.Homology.orientedCellEquiv (Space m) ℤ ℤ j (g j)
  have he (j : ℕ) : CharacteristicCoordinates (Space m) ℤ ℤ j (g j) (e j) :=
    P202.Homology.orientedCellEquiv_characteristic (Space m) ℤ ℤ j (g j)
  refine ⟨g, e, he, ?_⟩
  intro n c d a
  by_cases hn : 0 < n
  · obtain ⟨q, _, hq⟩ := P202.Homology.CellularDegrees.liftedCellCollapse
      (Space m) n d (D n hn).boundaryPoint
    have h := P202.Homology.CellularDegrees.AttachingCalculation.attaching_degree_normalized
      ℤ ℤ n hn (D n hn).boundaryPoint (D n hn).source (D n hn).target
      (Space m) (g n) (e n) (he n) c d q hq a
    rw [P202.Homology.CellularDegrees.AttachingCalculation.attachingSphereMap_eq_chart,
      hdegree n hn c d q hq] at h
    rw [← coherentDiskOrientations_succ D n hn] at h
    simpa [g, zsmul_eq_mul] using h
  · have hn0 : n = 0 := by omega
    subst n
    rw [differential_one_zero hstd]
    simp [incidence]

/-- Evaluation at the sole cell, after the actual cellular coordinates. -/
def oneCellCoordinate
    (labels : ∀ j, Cell (Space m) j ≃ { i : Unit // j ≤ m })
    (e : ∀ j, chainGroup (Space m) ℤ ℤ j ≃ₗ[ℤ] (Cell (Space m) j →₀ ℤ))
    (j : ℕ) (hj : j ≤ m) : chainGroup (Space m) ℤ ℤ j ≃ₗ[ℤ] ℤ := by
  haveI := cell_subsingleton labels j
  exact (e j).trans (Finsupp.uniqueLinearEquiv ℤ ℤ ((labels j).symm ⟨(), hj⟩))

lemma oneCellCoordinate_apply
    (labels : ∀ j, Cell (Space m) j ≃ { i : Unit // j ≤ m })
    (e : ∀ j, chainGroup (Space m) ℤ ℤ j ≃ₗ[ℤ] (Cell (Space m) j →₀ ℤ))
    (j : ℕ) (hj : j ≤ m) (z : chainGroup (Space m) ℤ ℤ j) :
    oneCellCoordinate labels e j hj z = e j z ((labels j).symm ⟨(), hj⟩) := rfl

lemma chainGroup_above_dimension
    (labels : ∀ j, Cell (Space m) j ≃ { i : Unit // j ≤ m })
    (e : ∀ j, chainGroup (Space m) ℤ ℤ j ≃ₗ[ℤ] (Cell (Space m) j →₀ ℤ))
    (j : ℕ) (hj : m < j) : IsZero (chainGroup (Space m) ℤ ℤ j) := by
  haveI : IsEmpty (Cell (Space m) j) := ⟨fun c => (Nat.not_le_of_gt hj) ((labels j c).property)⟩
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact (e j).injective.subsingleton

lemma differential_oneCellCoordinate
    (labels : ∀ j, Cell (Space m) j ≃ { i : Unit // j ≤ m })
    (g : ∀ j, ℤ ≃ₗ[ℤ] relativeHomology ℤ ℤ (referenceDiskPair.{0} j) (j : ℤ))
    (e : ∀ j, chainGroup (Space m) ℤ ℤ j ≃ₗ[ℤ] (Cell (Space m) j →₀ ℤ))
    (he : ∀ j, CharacteristicCoordinates (Space m) ℤ ℤ j (g j) (e j))
    (hd : ∀ (n : ℕ) (c : Cell (Space m) (n+1)) (d : Cell (Space m) n) (a : ℤ),
      e n (differential (Space m) ℤ ℤ n
        (cellClass (Space m) ℤ ℤ (n+1) c (g (n+1) a))) d = incidence (n+1) * a)
    (n : ℕ) (hn : n+1 ≤ m) (z : chainGroup (Space m) ℤ ℤ (n+1)) :
    oneCellCoordinate labels e n (by omega) (differential (Space m) ℤ ℤ n z) =
      incidence (n+1) * oneCellCoordinate labels e (n+1) hn z := by
  haveI := cell_subsingleton labels (n+1)
  let c := (labels (n+1)).symm ⟨(), hn⟩
  let d := (labels n).symm ⟨(), by omega⟩
  let a := e (n+1) z c
  have hz : cellClass (Space m) ℤ ℤ (n+1) c (g (n+1) a) = z := by
    apply (e (n+1)).injective
    rw [he (n+1)]
    ext c'
    have : c' = c := Subsingleton.elim _ _
    subst c'
    simp [a]
  rw [oneCellCoordinate_apply, oneCellCoordinate_apply]
  change e n (differential (Space m) ℤ ℤ n z) d = incidence (n+1) * a
  rw [← hz]
  exact hd n c d a

/-- Once the geometric cellular model and its coefficient calculation are
proved, the complete integral homology table follows, including all dimensions
above the top cell. This is a bridge lemma, not an extra premise of a target. -/
lemma homologyCalculation_of_cellularModel
    (hstd : StandardCW m C) (hcalc : CellularCalculation m C) : HomologyCalculation m := by
  obtain ⟨labels, _⟩ := hstd
  obtain ⟨g, e, he, hd⟩ := hcalc
  let K := cellularComplex (Space m) ℤ ℤ
  have hcoeff : ∀ (n : ℕ) (h : n+1 ≤ m) (z : K.X (n+1)),
      oneCellCoordinate labels e n (by omega) (K.d (n+1) n z) =
        incidence (n+1) * oneCellCoordinate labels e (n+1) h z := by
    intro n h z
    simpa only [K, cellularComplex, ChainComplex.of_d] using
      differential_oneCellCoordinate labels g e he hd n h z
  let comp (j : ℕ) : K.homology j ≃ₗ[ℤ] homology ℤ ℤ (projective m) (j : ℤ) :=
    (P202.Homology.CellularComparison.comparisonIso (Space m) ℤ ℤ j).toLinearEquiv
  intro j
  cases j with
  | zero =>
    refine ⟨fun _ => ⟨homologyZero m⟩, ?_, ?_⟩
    · rintro ⟨h, _⟩
      omega
    · rintro ⟨h, _⟩
      exact False.elim (h (Or.inl rfl))
  | succ n =>
    have hpos := positiveHomologyOfCoefficients K m (oneCellCoordinate labels e)
      (chainGroup_above_dimension labels e) hcoeff n
    refine ⟨?_, ?_, ?_⟩
    · rintro (hz | ⟨htop, ho⟩)
      · omega
      · obtain ⟨a⟩ := hpos.1 ⟨htop, htop.symm ▸ ho⟩
        exact ⟨(comp (n+1)).symm.trans a⟩
    · rintro ⟨_, hint, ho⟩
      obtain ⟨a⟩ := hpos.2.1 ⟨hint, ho⟩
      exact ⟨(comp (n+1)).symm.trans a⟩
    · rintro ⟨hnottop, hnotint⟩
      have hz : m < n+1 ∨ Even (n+1) := by
        rcases Nat.even_or_odd (n+1) with h | h
        · exact Or.inr h
        · apply Or.inl
          by_contra hle
          have hnle : n+1 ≤ m := by omega
          rcases lt_or_eq_of_le hnle with hlt | heq
          · exact hnotint ⟨by omega, hlt, h⟩
          · exact hnottop (Or.inr ⟨heq, heq ▸ h⟩)
      exact (comp (n+1)).toModuleIso.isZero_iff.mp (hpos.2.2 hz)

/-- The finite CW construction already proves vanishing above the cell
 dimension, independently of the still-open attaching coefficients. -/
lemma homology_above_dimension (m j : ℕ) (hj : m < j) :
    IsZero (homology ℤ ℤ (projective m) (j : ℤ)) := by
  letI := standardCW m
  obtain ⟨labels, _⟩ := standardCW_standard m
  let e (k : ℕ) := Classical.choice (P202.Homology.cellularCellGroups (Space m) ℤ ℤ k)
  have hz := chainGroup_above_dimension labels e j hj
  let K := cellularComplex (Space m) ℤ ℤ
  have hK : IsZero (K.homology j) := by
    exact ShortComplex.isZero_homology_of_isZero_X₂ (K.sc j) hz
  exact (P202.Homology.CellularComparison.comparisonIso (Space m) ℤ ℤ j).isZero_iff.mp hK

/-- The complete quotient, cellular differential, and integral homology
calculation in the first two projective dimensions. -/
theorem lowDimensionalModel (m : ℕ) (hm : m ≤ 1) :
    ∃ C : CWStructure (Space m),
      StandardCW m C ∧ CellularCalculation m C ∧ HomologyCalculation m := by
  letI C := standardCW m
  have hstd := standardCW_standard m
  have hcalc := cellularCalculation_low_dimension hm hstd
  exact ⟨C, hstd, hcalc, homologyCalculation_of_cellularModel hstd hcalc⟩

end Cellular

section CoordinateSubspaces
open P202.Cellular P202Specs.RelativeSingularChains P202Specs.CellularChains

def coordinateInclusion (n m : ℕ) (h : n ≤ m) :
    EuclideanSpace ℝ (Fin (n+1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1)) :=
  LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (Nat.succ_le_succ h))

lemma coordinateInclusion_apply (n m : ℕ) (h : n ≤ m)
    (v : EuclideanSpace ℝ (Fin (n+1))) (k : Fin (n+1)) :
    coordinateInclusion n m h v (Fin.castLE (Nat.succ_le_succ h) k) = v k := by
  simp only [coordinateInclusion, LinearIsometry.piLpExtendByZero, Function.ExtendByZero.linearMap]
  exact (Fin.castLE_injective _).extend_apply _ _ _

lemma coordinateInclusion_apply_high (n m : ℕ) (h : n ≤ m)
    (v : EuclideanSpace ℝ (Fin (n+1))) (k : Fin (m+1)) (hk : n < k.val) :
    coordinateInclusion n m h v k = 0 := by
  apply LinearIsometry.piLpExtendByZero_apply_eq_zero
  rintro ⟨i, hi⟩
  have heq := congrArg Fin.val hi
  simp only [Fin.coe_castLEEmb, Fin.val_castLE] at heq
  omega

def sphereInclusion (n m : ℕ) (h : n ≤ m) : C(sphere n, sphere m) where
  toFun x := ⟨coordinateInclusion n m h x.val, by
    simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometry.norm_map] using x.property⟩
  continuous_toFun := ((coordinateInclusion n m h).continuous.comp continuous_subtype_val).subtype_mk _

lemma sphereInclusion_injective (n m : ℕ) (h : n ≤ m) :
    Function.Injective (sphereInclusion n m h) := by
  intro x y hxy
  exact Subtype.ext ((coordinateInclusion n m h).injective (congrArg Subtype.val hxy))

lemma sphereInclusion_antipodal (n m : ℕ) (h : n ≤ m) (x : sphere n) :
    sphereInclusion n m h (antipodal n x) = antipodal m (sphereInclusion n m h x) := by
  apply Subtype.ext
  exact map_neg (coordinateInclusion n m h) x.val

def projectiveInclusion (n m : ℕ) (h : n ≤ m) : C(Space n, Space m) where
  toFun := Quotient.lift (fun x => quotientMap m (sphereInclusion n m h x)) (by
    intro x y hxy
    apply Quotient.sound
    rcases hxy with hxy | hxy
    · exact Or.inl (congrArg (coordinateInclusion n m h) hxy)
    · apply Or.inr
      simpa only [sphereInclusion, ContinuousMap.coe_mk, map_neg] using
        congrArg (coordinateInclusion n m h) hxy)
  continuous_toFun := by
    apply continuous_quot_lift
    exact (quotientMap m).hom.continuous.comp (sphereInclusion n m h).continuous

lemma projectiveInclusion_quotient (n m : ℕ) (h : n ≤ m) (x : sphere n) :
    projectiveInclusion n m h (quotientMap n x) = quotientMap m (sphereInclusion n m h x) := rfl

lemma projectiveInclusion_injective (n m : ℕ) (h : n ≤ m) :
    Function.Injective (projectiveInclusion n m h) := by
  intro x y hxy
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
      apply Quotient.sound
      rcases Quotient.exact hxy with hxy | hxy
      · exact Or.inl ((coordinateInclusion n m h).injective hxy)
      · apply Or.inr
        apply (coordinateInclusion n m h).injective
        simpa only [sphereInclusion, ContinuousMap.coe_mk, map_neg] using hxy

lemma sphereInclusion_closedEmbedding (n m : ℕ) (h : n ≤ m) :
    _root_.Topology.IsClosedEmbedding (sphereInclusion n m h) :=
  (sphereInclusion n m h).continuous.isClosedEmbedding (sphereInclusion_injective n m h)

lemma projectiveInclusion_closedEmbedding (n m : ℕ) (h : n ≤ m) [T2Space (Space m)] :
    _root_.Topology.IsClosedEmbedding (projectiveInclusion n m h) :=
  (projectiveInclusion n m h).continuous.isClosedEmbedding (projectiveInclusion_injective n m h)

lemma coordinateInclusion_hemisphereVector (n m j : ℕ) (hnm : n ≤ m) (hjn : j ≤ n)
    (x : Disk j) :
    coordinateInclusion n m hnm (hemisphereVector n j x) = hemisphereVector m j x := by
  ext k
  by_cases hk : k.val < n+1
  · let k' : Fin (n+1) := ⟨k.val, hk⟩
    have heq : Fin.castLE (Nat.succ_le_succ hnm) k' = k := Fin.ext rfl
    rw [← heq, coordinateInclusion_apply]
    simp [hemisphereVector, k']
  · rw [coordinateInclusion_apply_high n m hnm _ k (by omega)]
    simp [hemisphereVector, show ¬ k.val < j by omega, show k.val ≠ j by omega]

lemma hemisphereVector_boundary_inclusion (n m : ℕ) (hnm : n ≤ m) (x : sphere n) :
    hemisphereVector m (n+1) (boundaryInclusion (n+1) x) = coordinateInclusion n m hnm x.val := by
  ext k
  have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  by_cases hk : k.val < n+1
  · let k' : Fin (n+1) := ⟨k.val, hk⟩
    have heq : Fin.castLE (Nat.succ_le_succ hnm) k' = k := Fin.ext rfl
    rw [← heq, coordinateInclusion_apply]
    simp [hemisphereVector, boundaryInclusion, k', show k.val ≤ n by omega]
  · rw [coordinateInclusion_apply_high n m hnm _ k (by omega)]
    simp [hemisphereVector, boundaryInclusion, hx, show ¬ k.val ≤ n by omega]

lemma sphereInclusion_hemisphere (n m j : ℕ) (hnm : n ≤ m) (hjn : j ≤ n)
    (x : Disk j) :
    sphereInclusion n m hnm (hemisphere n j hjn x) =
      hemisphere m j (hjn.trans hnm) x := by
  exact Subtype.ext (coordinateInclusion_hemisphereVector n m j hnm hjn x)

lemma projectiveInclusion_characteristic (n m j : ℕ) (hnm : n ≤ m) (hjn : j ≤ n)
    (x : Disk j) :
    projectiveInclusion n m hnm (standardCharacteristic n j hjn x) =
      standardCharacteristic m j (hjn.trans hnm) x := by
  change quotientMap m (sphereInclusion n m hnm (hemisphere n j hjn x)) = _
  rw [sphereInclusion_hemisphere]
  rfl

lemma standardCharacteristic_boundary_inclusion (n m : ℕ) (h : n+1 ≤ m) (x : sphere n) :
    standardCharacteristic m (n+1) h (boundaryInclusion (n+1) x) =
      projectiveInclusion n m (by omega) (quotientMap n x) := by
  change quotientMap m (hemisphere m (n+1) h (boundaryInclusion (n+1) x)) =
    quotientMap m (sphereInclusion n m (by omega) x)
  apply congrArg (quotientMap m)
  exact Subtype.ext (hemisphereVector_boundary_inclusion n m (by omega) x)

lemma projectiveInclusion_range_skeleton (n m : ℕ) (h : n ≤ m) :
    letI := standardCellStructure m
    Set.range (projectiveInclusion n m h) = skeletonLT (Space m) (n+1) := by
  letI := standardCellStructure m
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := standardCharacteristic_top_surjective n z
    rw [projectiveInclusion_characteristic]
    obtain ⟨k, hk, w, hw⟩ := characteristic_point_in_cell m n h x
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨by omega,
      Set.mem_iUnion.mpr ⟨⟨(), hk.trans h⟩, ⟨w, hw.symm⟩⟩⟩⟩
  · intro hy
    obtain ⟨j, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hj, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨c, x, hx⟩ := Set.mem_iUnion.mp hy
    refine ⟨standardCharacteristic n j (by omega) (interiorInclusion j x), ?_⟩
    exact (projectiveInclusion_characteristic n m j h (by omega) (interiorInclusion j x)).trans hx

def projectiveSkeletonHomeomorph (n m : ℕ) (h : n ≤ m) :
    letI := standardCellStructure m
    Space n ≃ₜ skeletonLT (Space m) (n+1) := by
  letI := standardCellStructure m
  exact (projectiveInclusion_closedEmbedding n m h).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (projectiveInclusion_range_skeleton n m h))

lemma projectiveSkeletonHomeomorph_val (n m : ℕ) (h : n ≤ m) (x : Space n) :
    (projectiveSkeletonHomeomorph n m h x).val = projectiveInclusion n m h x := rfl

lemma standardAttachingBoundary (n m : ℕ) (h : n+1 ≤ m) (x : sphere n) :
    letI := standardCW m
    (P202Specs.CellularDegrees.attachingBoundary (Space m) n (show {i : Unit // n+1 ≤ m} from ⟨(), h⟩)
      ((P202.Homology.CellularDegrees.ConnectingBridge.referenceBoundarySphereHomeomorph n).symm
        (ULift.up x))).val = projectiveInclusion n m (by omega) (quotientMap n x) := by
  letI := standardCW m
  change standardCharacteristic m (n+1) h (boundaryInclusion (n+1) x) = _
  exact standardCharacteristic_boundary_inclusion n m h x


end CoordinateSubspaces

section CoverHomology
open HomologicalComplex P202Specs.MayerVietoris P202Specs.RelativeSingularChains
open P202.MayerVietoris

open P202Specs.MayerVietoris P202Specs.RelativeSingularChains

/-- A map that interchanges the two named members of a cover. -/
structure SwappingCoverMap (C D : CoverPair.{v,w}) where
  map : C.pair ⟶ D.pair
  left : Set.MapsTo map.map C.left D.right
  right : Set.MapsTo map.map C.right D.left

def SwappingCoverMap.onLeft {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) :
    C.leftPair ⟶ D.rightPair := pieceMap f.map f.left

def SwappingCoverMap.onRight {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) :
    C.rightPair ⟶ D.leftPair := pieceMap f.map f.right

def SwappingCoverMap.onIntersection {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) :
    C.intersectionPair ⟶ D.intersectionPair :=
  pieceMap f.map (fun _ hx => ⟨f.right hx.2, f.left hx.1⟩)

lemma swapping_left_square {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) :
    C.leftInclusion ≫ f.map = f.onLeft ≫ D.rightInclusion := by apply PairMap.ext; rfl
lemma swapping_right_square {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) :
    C.rightInclusion ≫ f.map = f.onRight ≫ D.leftInclusion := by apply PairMap.ext; rfl
lemma swapping_intersection_left_square {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) :
    C.toLeft ≫ f.onLeft = f.onIntersection ≫ D.toRight := by apply PairMap.ext; rfl
lemma swapping_intersection_right_square {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) :
    C.toRight ≫ f.onRight = f.onIntersection ≫ D.toLeft := by apply PairMap.ext; rfl

variable {R : Type u} [CommRing R]
  (F : Pair.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℤ)

def swappingMiddleMap {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) :
    middle F C ⟶ middle F D :=
  biprod.lift (biprod.snd ≫ F.map f.onRight) (biprod.fst ≫ F.map f.onLeft)

lemma chainFirst_swapping {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) :
    chainFirst F C ≫ swappingMiddleMap F f =
      -(F.map f.onIntersection ≫ chainFirst F D) := by
  apply biprod.hom_ext <;>
    simp only [chainFirst, swappingMiddleMap, Category.assoc, biprod.lift_fst,
      biprod.lift_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, ← F.map_comp,
      swapping_intersection_left_square, swapping_intersection_right_square]

lemma chainSum_swapping {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) :
    chainSum F C ≫ F.map f.map = swappingMiddleMap F f ≫ chainSum F D := by
  apply biprod.hom_ext' <;>
    simp only [chainSum, swappingMiddleMap, Category.assoc, biprod.inl_desc_assoc,
      biprod.inr_desc_assoc, biprod.inl_desc, biprod.inr_desc,
      Preadditive.comp_add, ← Category.assoc, biprod.inl_fst,
      biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, zero_comp, Category.id_comp,
      biprod.lift_desc, comp_zero, zero_add, add_zero, ← F.map_comp,
      swapping_left_square, swapping_right_square]
lemma classOf_neg (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    (z : K.X n) (hz : K.d n (n-1) z = 0) :
    classOf.{u,v} K n (-z) (by simp only [map_neg, hz, neg_zero]) = -classOf.{u,v} K n z hz := by
  have h := P202.MayerVietoris.classOf_map.{u,v} (-𝟙 K) n z hz (by simpa using hz)
  simpa only [homologyMap_neg, homologyMap_id, id_f, neg_f_apply,
    ModuleCat.hom_neg, ModuleCat.hom_id, LinearMap.neg_apply, LinearMap.id_apply] using h.symm

/-- The positive boundary-of-a-lift convention is anti-natural under maps
that interchange the two cover members. -/
lemma connecting_swapping
    (δ : Connecting.{u,v,w} F) (hb : BoundaryFormula F δ)
    (hs : SmallRepresentatives.{u,v,w} F) (hl : BoundaryLifts.{u,v,w} F)
    {C D : CoverPair.{v,w}} (f : SwappingCoverMap C D) (n : ℤ) :
    homologyMap (F.map f.map) (n+1) ≫ δ D n =
      -(δ C n ≫ homologyMap (F.map f.onIntersection) n) := by
  apply ModuleCat.hom_ext
  ext y
  have hn : n+1-1 = n := by omega
  obtain ⟨z, hz, rfl⟩ := P202.MayerVietoris.classOf_surjective (F.obj C.pair) (n+1) y
  obtain ⟨c, hc, hcz⟩ := hs C (n+1) z hz
  have hc' : (F.obj C.pair).d (n+1) n ((chainSum F C).f (n+1) c) = 0 := by
    convert hc using 1 <;> rw [hn]
  rw [← hcz]
  obtain ⟨x, ⟨hx, hxc⟩, _⟩ := hl C n c hc'
  let c' := (swappingMiddleMap F f).f (n+1) c
  let x' := -((F.map f.onIntersection).f n x)
  have hsum : (chainSum F D).f (n+1) c' =
      (F.map f.map).f (n+1) ((chainSum F C).f (n+1) c) := by
    exact (congrArg (fun q => q.f (n+1) c) (chainSum_swapping F f)).symm
  have hcD : (F.obj D.pair).d (n+1) n ((chainSum F D).f (n+1) c') = 0 := by
    rw [hsum, ← ModuleCat.comp_apply, (F.map f.map).comm]
    simp [hc']
  have hxD : (chainFirst F D).f n x' = (middle F D).d (n+1) n c' := by
    have hfirst := congrArg (fun q => q.f n x) (chainFirst_swapping F f)
    simp only [comp_f, neg_f_apply, Preadditive.neg_comp, ModuleCat.hom_neg, LinearMap.neg_apply, ModuleCat.comp_apply] at hfirst
    dsimp only [x', c']
    rw [map_neg, ← hfirst, hx]
    exact (congrArg (fun q => q c) ((swappingMiddleMap F f).comm (n+1) n)).symm
  have hxcD : (F.obj D.intersectionPair).d n (n-1) x' = 0 := by
    dsimp only [x']
    rw [map_neg, ← ModuleCat.comp_apply, (F.map f.onIntersection).comm]
    simp [hxc]
  have hfcycle : (F.obj D.pair).d (n+1) ((n+1)-1)
      ((F.map f.map).f (n+1) ((chainSum F C).f (n+1) c)) = 0 := by
    rw [hn]
    rw [← hsum]
    exact hcD
  have hmap := P202.MayerVietoris.classOf_map (F.map f.map) (n+1)
    ((chainSum F C).f (n+1) c) hc hfcycle
  change δ D n (homologyMap (F.map f.map) (n+1) _) =
    -(homologyMap (F.map f.onIntersection) n (δ C n _))
  rw [hmap]
  have hclass : classOf.{u,v} (F.obj D.pair) (n+1)
      ((F.map f.map).f (n+1) ((chainSum F C).f (n+1) c)) hfcycle =
      classOf.{u,v} (F.obj D.pair) (n+1) ((chainSum F D).f (n+1) c') (by rw [hn]; exact hcD) := by
    congr 1
    exact hsum.symm
  rw [hclass, hb D n c' hcD x' hxD hxcD, hb C n c hc' x hx hxc]
  dsimp only [x']
  rw [classOf_neg]
  congr 1
  symm
  apply P202.MayerVietoris.classOf_map
  rw [← ModuleCat.comp_apply, (F.map f.onIntersection).comm]
  simp [hxc]


lemma reducedHomologySum_of_cover
    (C : CoverPair.{0,0}) {Y : TopCat.{0}} (f g h k : C.pair.space ⟶ Y)
    (hL : (C.leftInclusion.map ≫ f = C.leftInclusion.map ≫ h ∧
      C.leftInclusion.map ≫ g = C.leftInclusion.map ≫ k) ∨
      (C.leftInclusion.map ≫ f = C.leftInclusion.map ≫ k ∧
      C.leftInclusion.map ≫ g = C.leftInclusion.map ≫ h))
    (hR : (C.rightInclusion.map ≫ f = C.rightInclusion.map ≫ h ∧
      C.rightInclusion.map ≫ g = C.rightInclusion.map ≫ k) ∨
      (C.rightInclusion.map ≫ f = C.rightInclusion.map ≫ k ∧
      C.rightInclusion.map ≫ g = C.rightInclusion.map ≫ h)) (n : ℤ) :
    (reducedHomologyFunctor ℤ ℤ n).map f + (reducedHomologyFunctor ℤ ℤ n).map g =
      (reducedHomologyFunctor ℤ ℤ n).map h + (reducedHomologyFunctor ℤ ℤ n).map k := by
  let F := reducedFunctor ℤ ℤ
  have hs : chainSum (theoryFunctor ℤ .reduced) C ≫ (F.map f + F.map g) =
      chainSum (theoryFunctor ℤ .reduced) C ≫ (F.map h + F.map k) := by
    apply biprod.hom_ext'
    · simp only [chainSum, biprod.inl_desc_assoc, Preadditive.comp_add]
      change F.map C.leftInclusion.map ≫ F.map f + F.map C.leftInclusion.map ≫ F.map g =
        F.map C.leftInclusion.map ≫ F.map h + F.map C.leftInclusion.map ≫ F.map k
      simp only [← F.map_comp]
      rcases hL with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]
      · rw [h₁, h₂, add_comm]
    · simp only [chainSum, biprod.inr_desc_assoc, Preadditive.comp_add]
      change F.map C.rightInclusion.map ≫ F.map f + F.map C.rightInclusion.map ≫ F.map g =
        F.map C.rightInclusion.map ≫ F.map h + F.map C.rightInclusion.map ≫ F.map k
      simp only [← F.map_comp]
      rcases hR with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]
      · rw [h₁, h₂, add_comm]
  letI := (reducedSmall_shortExact ℤ C).epi_g
  have hi : reducedSmallInclusion ℤ C ≫ (F.map f + F.map g) =
      reducedSmallInclusion ℤ C ≫ (F.map h + F.map k) := by
    apply (cancel_epi (reducedSmallSum ℤ C)).mp
    simpa only [← Category.assoc, reducedSmallSum_inclusion] using hs
  letI := reducedSmallInclusion_quasiIso ℤ C
  have hm := congrArg (fun z => homologyMap z n) hi
  simp only [homologyMap_comp, homologyMap_add] at hm
  exact (cancel_epi (homologyMap (reducedSmallInclusion ℤ C) n)).mp hm


lemma degreeSum_of_cover
    (n : ℕ) (U V : Set (P202Specs.SpheresDisks.sphere n))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (f g h k : P202Specs.SpheresDisks.sphere n ⟶ P202Specs.SpheresDisks.sphere n)
    (hL : (∀ x ∈ U, f x = h x ∧ g x = k x) ∨
      (∀ x ∈ U, f x = k x ∧ g x = h x))
    (hR : (∀ x ∈ V, f x = h x ∧ g x = k x) ∨
      (∀ x ∈ V, f x = k x ∧ g x = h x)) :
    P202Specs.Degree.degree n f + P202Specs.Degree.degree n g =
      P202Specs.Degree.degree n h + P202Specs.Degree.degree n k := by
  let C : CoverPair.{0,0} := CoverPair.ofSets
    ⟨P202Specs.SpheresDisks.sphere n, ∅⟩ U V hU hV hcover
  have hleft : (C.leftInclusion.map ≫ f = C.leftInclusion.map ≫ h ∧
      C.leftInclusion.map ≫ g = C.leftInclusion.map ≫ k) ∨
      (C.leftInclusion.map ≫ f = C.leftInclusion.map ≫ k ∧
      C.leftInclusion.map ≫ g = C.leftInclusion.map ≫ h) := by
    rcases hL with H | H
    · left
      constructor
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact (H x.val x.property).1
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact (H x.val x.property).2
    · right
      constructor
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact (H x.val x.property).1
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact (H x.val x.property).2
  have hright : (C.rightInclusion.map ≫ f = C.rightInclusion.map ≫ h ∧
      C.rightInclusion.map ≫ g = C.rightInclusion.map ≫ k) ∨
      (C.rightInclusion.map ≫ f = C.rightInclusion.map ≫ k ∧
      C.rightInclusion.map ≫ g = C.rightInclusion.map ≫ h) := by
    rcases hR with H | H
    · left
      constructor
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact (H x.val x.property).1
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact (H x.val x.property).2
    · right
      constructor
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact (H x.val x.property).1
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact (H x.val x.property).2
  have hm := reducedHomologySum_of_cover C f g h k hleft hright (n : ℤ)
  let e := P202.Degree.sphereCoordinate n
  have hv := congrArg (fun z => e (z (e.symm 1))) hm
  simp only [ModuleCat.hom_add, LinearMap.add_apply, map_add] at hv
  change e (P202Specs.Degree.induced n f (e.symm 1)) +
      e (P202Specs.Degree.induced n g (e.symm 1)) =
    e (P202Specs.Degree.induced n h (e.symm 1)) +
      e (P202Specs.Degree.induced n k (e.symm 1)) at hv
  simpa only [P202.Degree.action, map_zsmul, LinearEquiv.apply_symm_apply,
    zsmul_eq_mul, Int.cast_id, mul_one] using hv


end CoverHomology

lemma injective_of_surjective_integer_coordinates
    {A B : Type*} [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    (eA : A ≃ₗ[ℤ] ℤ) (eB : B ≃ₗ[ℤ] ℤ) (f : A →ₗ[ℤ] B)
    (hf : Function.Surjective f) : Function.Injective f := by
  have hcoord (x : A) : eB (f x) = eA x * eB (f (eA.symm 1)) := by
    have hx : x = eA x • eA.symm 1 := by
      apply eA.injective
      simp
    conv_lhs => rw [hx]
    simp
  have hc : eB (f (eA.symm 1)) ≠ 0 := by
    intro hc
    obtain ⟨a, ha⟩ := hf (eB.symm 1)
    have h := hcoord a
    rw [ha, LinearEquiv.apply_symm_apply, hc, mul_zero] at h
    omega
  intro x y h
  apply eA.injective
  apply mul_right_cancel₀ hc
  exact (hcoord x).symm.trans ((congrArg eB h).trans (hcoord y))

lemma sphere_chord_ne_zero (n : ℕ) (x y : sphere n)
    (h : 0 ≤ inner ℝ x.val y.val) (t : ℝ) :
    (1-t) • x.val + t • y.val ≠ 0 := by
  have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hy : ‖y.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  intro heq
  have hh := congrArg (fun v => inner ℝ v (x.val + y.val)) heq
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hx, hy, one_pow, inner_zero_left,
    real_inner_comm y.val x.val] at hh
  have h' : 0 ≤ inner ℝ y.val x.val := by simpa only [real_inner_comm] using h
  nlinarith

/-- Normalizing the straight chord gives a sphere homotopy whenever the
pointwise inner products of its endpoints are nonnegative. -/
def sphereChordHomotopy (n : ℕ) (f g : sphere n ⟶ sphere n)
    (h : ∀ x, 0 ≤ inner ℝ (f x).val (g x).val) : TopCat.Homotopy f g where
  toFun tx :=
    let v := (1-(tx.1 : ℝ)) • (f tx.2).val + (tx.1 : ℝ) • (g tx.2).val
    ⟨‖v‖⁻¹ • v, by
      have hv := sphere_chord_ne_zero n (f tx.2) (g tx.2) (h tx.2) (tx.1 : ℝ)
      simpa only [Metric.mem_sphere, dist_zero_right] using
        (show ‖‖v‖⁻¹ • v‖ = 1 by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)])⟩
  continuous_toFun := by
    let v : unitInterval × sphere n → EuclideanSpace ℝ (Fin (n+1)) :=
      fun tx => (1-(tx.1 : ℝ)) • (f tx.2).val + (tx.1 : ℝ) • (g tx.2).val
    have hv : Continuous v := by
      dsimp only [v]
      fun_prop
    apply Continuous.subtype_mk
    exact (hv.norm.inv₀ (fun tx => norm_ne_zero_iff.mpr
      (sphere_chord_ne_zero n (f tx.2) (g tx.2) (h tx.2) (tx.1 : ℝ)))).smul hv
  map_zero_left := by
    intro x
    apply Subtype.ext
    have hx : ‖(f x).val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using (f x).property
    simp [hx]
  map_one_left := by
    intro x
    apply Subtype.ext
    have hx : ‖(g x).val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using (g x).property
    simp [hx]

section AntipodalSign
open HomologicalComplex P202Specs.MayerVietoris P202Specs.RelativeSingularChains

namespace AntipodalGeometry
open SmoothManifolds.SphereTorusData
open SmoothManifolds.SphereCohomology.PoleTopology
abbrev CSphere := SmoothManifolds.SphereTorusData.Sphere
abbrev overlap (n : ℕ) := (P202.SpheresDisks.spherePoleCover (n+1)).intersectionPair.space

def tailSquare (n : ℕ) (x : CSphere (n+1)) : ℝ := ∑ i : Fin (n+1), x.val i.succ ^ 2
lemma tailSquare_nonneg (n : ℕ) (x : CSphere (n+1)) : 0 ≤ tailSquare n x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma tailSquare_pos (n : ℕ) (x : overlap n) : 0 < tailSquare n x.val := by
  have hnonneg := tailSquare_nonneg n x.val
  by_contra h
  have hz : tailSquare n x.val = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hall : ∀ i : Fin (n+1), x.val.val i.succ = 0 := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x.val.val i.succ))).mp hz
    intro i
    exact sq_eq_zero_iff.mp (hs i (Finset.mem_univ i))
  have hx0 : x.val.val 0 ^ 2 = 1 := by
    have hx := x.val.property
    rw [squareSum, Fin.sum_univ_succ] at hx
    change x.val.val 0 ^ 2 + tailSquare n x.val = 1 at hx
    simpa only [hz, add_zero] using hx
  rcases sq_eq_one_iff.mp hx0 with hp | hm
  · have heq : x.val = north (n+1) := by
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [north] using hp
      · simpa [north, Fin.succ_ne_zero] using hall j
    exact x.property.1 heq
  · have heq : x.val = south (n+1) := by
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [south, SmoothManifolds.SphereCohomology.PoleTopology.antipodal, north] using hm
      · simpa [south, SmoothManifolds.SphereCohomology.PoleTopology.antipodal, north, Fin.succ_ne_zero] using hall j
    exact x.property.2 heq

def equatorProjection (n : ℕ) : overlap n ⟶ TopCat.of (CSphere n) :=
  TopCat.ofHom {
    toFun := fun x => ⟨fun i => x.val.val i.succ / Real.sqrt (tailSquare n x.val), by
      have hpos := tailSquare_pos n x
      dsimp only [squareSum]
      simp only [div_pow, ← Finset.sum_div, Real.sq_sqrt hpos.le]
      exact div_self (ne_of_gt hpos)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      apply Continuous.div
      · exact (continuous_apply i.succ).comp (continuous_subtype_val.comp continuous_subtype_val)
      · exact Real.continuous_sqrt.comp (continuous_finsetSum _ (fun i _ =>
          ((continuous_apply i.succ).comp (continuous_subtype_val.comp continuous_subtype_val)).pow 2))
      · intro x
        exact ne_of_gt (Real.sqrt_pos.mpr (tailSquare_pos n x)) }

def equatorSection (n : ℕ) : TopCat.of (CSphere n) ⟶ overlap n :=
  TopCat.ofHom {
    toFun := fun x => ⟨⟨Fin.cons 0 x.val, by
      simpa [squareSum, Fin.sum_univ_succ] using x.property⟩, by
      constructor <;> intro h
      · have hh := congrArg (fun z : CSphere (n+1) => z.val 0) h
        simp [north] at hh
      · have hh := congrArg (fun z : CSphere (n+1) => z.val 0) h
        simp [south, SmoothManifolds.SphereCohomology.PoleTopology.antipodal, north] at hh⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_const
      · exact (continuous_apply j).comp continuous_subtype_val }

lemma equatorSection_projection (n : ℕ) : equatorSection n ≫ equatorProjection n = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext i
  have hsq : tailSquare n (equatorSection n x).val = 1 := by
    change squareSum x.val = 1
    exact x.property
  change x.val i / Real.sqrt (tailSquare n (equatorSection n x).val) = x.val i
  rw [hsq, Real.sqrt_one, div_one]

def coordinateAntipodal (n : ℕ) : TopCat.of (CSphere n) ⟶ TopCat.of (CSphere n) :=
  TopCat.ofHom ⟨SmoothManifolds.SphereCohomology.PoleTopology.antipodal n, (SmoothManifolds.SphereCohomology.PoleTopology.antipodal n).continuous⟩
lemma coordinateAntipodal_involutive (n : ℕ) : Function.Involutive (coordinateAntipodal n) := by
  intro x
  apply Subtype.ext
  exact neg_neg x.val
lemma coordinateAntipodal_north (n : ℕ) : coordinateAntipodal n (north n) = south n := rfl
lemma coordinateAntipodal_south (n : ℕ) : coordinateAntipodal n (south n) = north n :=
  coordinateAntipodal_involutive n (north n)

def antipodalCoverMap (n : ℕ) : SwappingCoverMap (P202.SpheresDisks.spherePoleCover n)
    (P202.SpheresDisks.spherePoleCover n) where
  map := ⟨coordinateAntipodal n, fun _ h => h.elim⟩
  left := by
    intro x hx
    change coordinateAntipodal n x ≠ south n
    intro h
    apply hx
    exact (coordinateAntipodal_involutive n).injective (h.trans (coordinateAntipodal_north n).symm)
  right := by
    intro x hx
    change coordinateAntipodal n x ≠ north n
    intro h
    apply hx
    exact (coordinateAntipodal_involutive n).injective (h.trans (coordinateAntipodal_south n).symm)

lemma tailSquare_antipodal (n : ℕ) (x : CSphere (n+1)) :
    tailSquare n (coordinateAntipodal (n+1) x) = tailSquare n x := by
  simp [tailSquare, coordinateAntipodal, SmoothManifolds.SphereCohomology.PoleTopology.antipodal, Pi.neg_apply]

lemma equatorProjection_antipodal (n : ℕ) :
    (antipodalCoverMap (n+1)).onIntersection.map ≫ equatorProjection n =
      equatorProjection n ≫ coordinateAntipodal n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext i
  change -(x.val.val i.succ) / Real.sqrt (tailSquare n (coordinateAntipodal (n+1) x.val)) =
    -(x.val.val i.succ / Real.sqrt (tailSquare n x.val))
  rw [tailSquare_antipodal, neg_div]

open P202Specs.SingularChains

def coordinateSphereCoordinate (n : ℕ) :
    reducedHomology ℤ ℤ (TopCat.of (CSphere n)) (n : ℤ) ≃ₗ[ℤ] ℤ :=
  ((reducedHomologyFunctor ℤ ℤ (n : ℤ)).mapIso
    (TopCat.isoOfHomeo (SmoothManifolds.SphereCohomology.metricSphereHomeomorph n))).toLinearEquiv.trans
    (P202.Degree.sphereCoordinate n)

def overlapCoordinate (n : ℕ) : reducedHomology ℤ ℤ (overlap n) (n : ℤ) ≃ₗ[ℤ] ℤ :=
  (P202.SpheresDisks.reducedHomologyIsoOfHomotopyEquiv ℤ ℤ
    (X := overlap n) (Y := TopCat.of (CSphere n))
    (overlapHomotopyEquiv n) (n : ℤ)).toLinearEquiv.trans (coordinateSphereCoordinate n)

lemma equatorProjection_homology_injective (n : ℕ) :
    Function.Injective ((reducedHomologyFunctor ℤ ℤ (n : ℤ)).map (equatorProjection n)) := by
  let H := reducedHomologyFunctor ℤ ℤ (n : ℤ)
  have hsection : H.map (equatorSection n) ≫ H.map (equatorProjection n) = 𝟙 _ := by
    rw [← H.map_comp, equatorSection_projection, H.map_id]
  apply injective_of_surjective_integer_coordinates (overlapCoordinate n)
    (coordinateSphereCoordinate n) (H.map (equatorProjection n)).hom
  intro y
  exact ⟨H.map (equatorSection n) y, congrArg (fun q => q y) hsection⟩

def coordinateMetricIso (n : ℕ) : TopCat.of (CSphere n) ≅ P202Specs.SpheresDisks.sphere n :=
  TopCat.isoOfHomeo (SmoothManifolds.SphereCohomology.metricSphereHomeomorph n)

lemma coordinateAntipodal_metric (n : ℕ) :
    coordinateAntipodal n ≫ (coordinateMetricIso n).hom =
      (coordinateMetricIso n).hom ≫ P202Specs.RealProjectiveHomology.antipodal n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

lemma coordinateAntipodal_zero_action
    (x : reducedHomology ℤ ℤ (TopCat.of (CSphere 0)) 0) :
    (reducedHomologyFunctor ℤ ℤ 0).map (coordinateAntipodal 0) x = (-1 : ℤ) • x := by
  let H := reducedHomologyFunctor ℤ ℤ 0
  let e := H.mapIso (coordinateMetricIso 0)
  apply e.toLinearEquiv.injective
  change H.map (coordinateMetricIso 0).hom (H.map (coordinateAntipodal 0) x) = _
  rw [← ModuleCat.comp_apply, ← H.map_comp, coordinateAntipodal_metric, H.map_comp]
  change P202Specs.Degree.induced 0 P202Specs.Degree.interchange (e.hom x) = _
  rw [P202.Degree.interchange_induced]
  simp

lemma coordinateAntipodal_action (n : ℕ)
    (x : reducedHomology ℤ ℤ (TopCat.of (CSphere n)) (n : ℤ)) :
    (reducedHomologyFunctor ℤ ℤ (n : ℤ)).map (coordinateAntipodal n) x =
      (-1 : ℤ)^(n+1) • x := by
  revert x
  induction n with
  | zero =>
    intro x
    change _ = (-1 : ℤ) • x
    exact coordinateAntipodal_zero_action x
  | succ n ih =>
    intro x
    let C := P202.SpheresDisks.spherePoleCover (n+1)
    let F := P202Specs.MayerVietoris.theoryFunctor ℤ .reduced
    obtain ⟨⟨δ, he, _hn, hb⟩, hs, hl, _⟩ := P202.MayerVietoris.mayerVietoris.{0,0,0} ℤ .reduced
    have : ContractibleSpace C.leftPair.space := P202.SpheresDisks.spherePoleCover_left_contractible (n+1)
    have : ContractibleSpace C.rightPair.space := P202.SpheresDisks.spherePoleCover_right_contractible (n+1)
    have : Nonempty C.leftPair.space :=
      ⟨⟨south (n+1), (north_ne_south (n+1)).symm⟩⟩
    have : Nonempty C.rightPair.space :=
      ⟨⟨north (n+1), north_ne_south (n+1)⟩⟩
    have : IsIso (δ C (n : ℤ)) := P202.SpheresDisks.mvConnecting_isIso ℤ F δ he C (n : ℤ)
      (fun k _ => P202.PrismHomotopy.contractible ℤ ℤ C.leftPair.space k)
      (fun k _ => P202.PrismHomotopy.contractible ℤ ℤ C.rightPair.space k)
    have hi : Function.Injective (δ C (n : ℤ)) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    apply hi
    apply equatorProjection_homology_injective n
    have hswap := connecting_swapping F δ hb hs hl (antipodalCoverMap (n+1)) (n : ℤ)
    have hswapx := congrArg (fun q => q x) hswap
    change δ C (n : ℤ) ((reducedHomologyFunctor ℤ ℤ ((n : ℤ)+1)).map
      (coordinateAntipodal (n+1)) x) =
      -((reducedHomologyFunctor ℤ ℤ (n : ℤ)).map
        (antipodalCoverMap (n+1)).onIntersection.map (δ C (n : ℤ) x)) at hswapx
    change ((reducedHomologyFunctor ℤ ℤ (n : ℤ)).map (equatorProjection n))
      (δ C (n : ℤ) (((reducedHomologyFunctor ℤ ℤ ((n : ℤ)+1)).map
      (coordinateAntipodal (n+1))) x)) = _
    rw [hswapx, map_neg]
    let H := reducedHomologyFunctor ℤ ℤ (n : ℤ)
    change -(H.map (equatorProjection n) (H.map (antipodalCoverMap (n+1)).onIntersection.map _)) = _
    rw [← ModuleCat.comp_apply, ← H.map_comp, equatorProjection_antipodal, H.map_comp,
      ModuleCat.comp_apply]
    rw [ih]
    change -((-1 : ℤ)^(n+1) • (H.map (equatorProjection n)).hom ((δ C (n : ℤ)).hom x)) =
      (H.map (equatorProjection n)).hom ((δ C (n : ℤ)).hom ((-1 : ℤ)^(n+1+1) • x))
    rw [map_zsmul, map_zsmul]
    have hp : (-1 : ℤ)^(n+1+1) = -((-1 : ℤ)^(n+1)) := by
      rw [pow_succ, mul_neg_one]
    rw [hp]
    exact (neg_zsmul _ _).symm

lemma metricAntipodal_action (n : ℕ) (x : P202Specs.Degree.sphereGroup n) :
    P202Specs.Degree.induced n (P202Specs.RealProjectiveHomology.antipodal n) x =
      (-1 : ℤ)^(n+1) • x := by
  let H := reducedHomologyFunctor ℤ ℤ (n : ℤ)
  let e := H.mapIso (coordinateMetricIso n)
  obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective x
  change H.map (P202Specs.RealProjectiveHomology.antipodal n) (e.hom y) = _
  rw [← ModuleCat.comp_apply]
  change (H.map (coordinateMetricIso n).hom ≫ H.map
    (P202Specs.RealProjectiveHomology.antipodal n)) y = _
  rw [← H.map_comp, ← coordinateAntipodal_metric, H.map_comp, ModuleCat.comp_apply,
    coordinateAntipodal_action]
  change e.toLinearEquiv ((-1 : ℤ)^(n+1) • y) = (-1 : ℤ)^(n+1) • e.toLinearEquiv y
  exact map_zsmul e.toLinearEquiv ((-1 : ℤ)^(n+1)) y

lemma antipodal_degree_all (n : ℕ) :
    P202Specs.Degree.degree n (P202Specs.RealProjectiveHomology.antipodal n) =
      (-1 : ℤ)^(n+1) :=
  (P202.Degree.scalar_unique n (P202Specs.RealProjectiveHomology.antipodal n) _
    (metricAntipodal_action n)).symm
end AntipodalGeometry

theorem antipodalDegree : P202Specs.RealProjectiveHomology.Expected.antipodalDegree :=
  AntipodalGeometry.antipodal_degree_all

end AntipodalSign

section PolynomialChart
open P202.Cellular P202Specs.RelativeSingularChains P202Specs.GoodPairQuotient

def polynomialDiskVector (n : ℕ) (x : Disk n) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (fun k => if h : k.val < n then
    2 * Real.sqrt (1 - ‖x.val‖ ^ 2) * x.val ⟨k.val, h⟩ else 1 - 2 * ‖x.val‖ ^ 2)

lemma polynomialDiskVector_norm (n : ℕ) (x : Disk n) : ‖polynomialDiskVector n x‖ = 1 := by
  have hx : ‖x.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  have hnonneg : 0 ≤ 1 - ‖x.val‖ ^ 2 := by nlinarith [norm_nonneg x.val]
  have hs := Real.sq_sqrt hnonneg
  have hsum : (∑ i : Fin n, (polynomialDiskVector n x i.castSucc)^2) =
      (2 * Real.sqrt (1 - ‖x.val‖ ^ 2))^2 * ‖x.val‖ ^ 2 := by
    simp only [polynomialDiskVector, PiLp.toLp_apply, Fin.val_castSucc, Fin.is_lt, dite_true]
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  have hnorm : ‖polynomialDiskVector n x‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc, hsum]
    simp only [polynomialDiskVector, PiLp.toLp_apply, Fin.val_last, lt_self_iff_false, dite_false]
    nlinarith
  nlinarith [norm_nonneg (polynomialDiskVector n x)]

lemma polynomialDiskVector_continuous (n : ℕ) : Continuous (polynomialDiskVector n) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  dsimp [polynomialDiskVector]
  split_ifs
  · fun_prop
  · fun_prop

def polynomialDiskSphere (n : ℕ) : C(Disk n, sphere n) where
  toFun x := ⟨polynomialDiskVector n x, by simpa using polynomialDiskVector_norm n x⟩
  continuous_toFun := (polynomialDiskVector_continuous n).subtype_mk _

lemma polynomialDiskSphere_last (n : ℕ) (x : Disk n) :
    (polynomialDiskSphere n x).val (Fin.last n) = 1 - 2 * ‖x.val‖ ^ 2 := by
  simp [polynomialDiskSphere, polynomialDiskVector]

lemma polynomialDiskSphere_boundary (n : ℕ) (x y : Sphere n) :
    polynomialDiskSphere n (boundaryInclusion n x) =
      polynomialDiskSphere n (boundaryInclusion n y) := by
  apply Subtype.ext
  ext k
  have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hy : ‖y.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  simp [polynomialDiskSphere, polynomialDiskVector, boundaryInclusion, hx, hy]

lemma polynomialDiskSphere_respects (n : ℕ) (x y : Disk n)
    (h : (collapseSetoid (diskPair n)).r x y) :
    polynomialDiskSphere n x = polynomialDiskSphere n y := by
  rcases h with rfl | ⟨hx, hy⟩
  · rfl
  · change ‖x.val‖ = 1 at hx
    change ‖y.val‖ = 1 at hy
    exact polynomialDiskSphere_boundary n ⟨x.val, by simpa using hx⟩ ⟨y.val, by simpa using hy⟩

def polynomialDiskQuotientSphere (n : ℕ) : quotientSpace (diskPair n) → sphere n :=
  Quotient.lift (polynomialDiskSphere n) (polynomialDiskSphere_respects n)

lemma polynomialDiskQuotientSphere_continuous (n : ℕ) : Continuous (polynomialDiskQuotientSphere n) :=
  continuous_quot_lift _ (polynomialDiskSphere n).continuous

lemma polynomialDiskQuotientSphere_injective (n : ℕ) :
    Function.Injective (polynomialDiskQuotientSphere n) := by
  intro a b hab
  induction a using Quotient.inductionOn with | _ x =>
    induction b using Quotient.inductionOn with | _ y =>
      change polynomialDiskSphere n x = polynomialDiskSphere n y at hab
      have hlast := congrArg (fun z : sphere n => z.val (Fin.last n)) hab
      rw [polynomialDiskSphere_last, polynomialDiskSphere_last] at hlast
      have hnorm : ‖x.val‖^2 = ‖y.val‖^2 := by linarith
      apply Quotient.sound
      by_cases hx : ‖x.val‖ < 1
      · apply Or.inl
        apply Subtype.ext
        ext i
        have hpos : 0 < Real.sqrt (1-‖x.val‖^2) := Real.sqrt_pos.mpr (by
          nlinarith [norm_nonneg x.val])
        have hi := congrArg (fun z : sphere n => z.val i.castSucc) hab
        simp only [polynomialDiskSphere, ContinuousMap.coe_mk, polynomialDiskVector,
          PiLp.toLp_apply, Fin.val_castSucc, Fin.is_lt, dite_true, ← hnorm] at hi
        nlinarith
      · apply Or.inr
        have hxle : ‖x.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
        have hxeq : ‖x.val‖ = 1 := le_antisymm hxle (le_of_not_gt hx)
        have hyeq : ‖y.val‖ = 1 := by nlinarith [norm_nonneg y.val]
        exact ⟨hxeq, hyeq⟩

lemma polynomialDiskSphere_surjective (n : ℕ) (b : Sphere n) :
    Function.Surjective (polynomialDiskSphere n) := by
  intro y
  let t := y.val (Fin.last n)
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => y.val i.castSucc)
  have hy : ‖y.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  have hw : ‖w‖^2 + t^2 = 1 := by
    have heq := EuclideanSpace.real_norm_sq_eq y.val
    rw [Fin.sum_univ_castSucc, hy] at heq
    simpa only [EuclideanSpace.real_norm_sq_eq, w, PiLp.toLp_apply, one_pow, t] using heq.symm
  have ht : -1 ≤ t ∧ t ≤ 1 := by constructor <;> nlinarith [sq_nonneg ‖w‖]
  by_cases hts : t = -1
  · have hwzero : w = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg w]
    refine ⟨boundaryInclusion n b, ?_⟩
    apply Subtype.ext
    ext k
    have hb : ‖b.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using b.property
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simpa [polynomialDiskSphere, polynomialDiskVector, boundaryInclusion, hb, t] using (show (1:ℝ)-2 = t by linarith)
    · have hi := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) hwzero
      simpa [polynomialDiskSphere, polynomialDiskVector, boundaryInclusion, hb, w] using hi.symm
  · let s := Real.sqrt ((1+t)/2)
    have htgt : -1 < t := lt_of_le_of_ne ht.1 (Ne.symm hts)
    have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
    have hsq : s^2 = (1+t)/2 := Real.sq_sqrt (by linarith [ht.1])
    let v : EuclideanSpace ℝ (Fin n) := (1/(2*s)) • w
    have hv : ‖v‖^2 = (1-t)/2 := by
      simp only [v, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, one_pow]
      field_simp
      nlinarith
    have hvle : ‖v‖ ≤ 1 := by nlinarith [norm_nonneg v, ht.1]
    let x : Disk n := ⟨v, by simpa only [Metric.mem_closedBall, dist_zero_right] using hvle⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    ext k
    have hsx : Real.sqrt (1-‖x.val‖^2) = s := by
      rw [show 1-‖x.val‖^2 = s^2 by dsimp [x]; nlinarith]
      exact Real.sqrt_sq hspos.le
    refine Fin.lastCases ?_ (fun i => ?_) k
    · rw [polynomialDiskSphere_last]
      change 1 - 2 * ‖v‖^2 = t
      rw [hv]
      ring
    · simp only [polynomialDiskSphere, ContinuousMap.coe_mk, polynomialDiskVector,
        PiLp.toLp_apply, Fin.val_castSucc, Fin.is_lt, dite_true, hsx]
      simp only [x, v, w, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]
      field_simp

lemma polynomialDiskQuotientSphere_surjective (n : ℕ) (b : Sphere n) :
    Function.Surjective (polynomialDiskQuotientSphere n) := by
  intro y
  obtain ⟨x, hx⟩ := polynomialDiskSphere_surjective n b y
  exact ⟨quotientProjection (diskPair n) x, hx⟩

def polynomialDiskQuotientSphereHomeomorph (n : ℕ) (b : Sphere n) :
    quotientSpace (diskPair n) ≃ₜ sphere n :=
  letI : CompactSpace (diskPair n).space := by change CompactSpace (Disk n); infer_instance
  letI : CompactSpace (quotientSpace (diskPair n)) :=
    (isQuotientMap_quotient_mk' (s := collapseSetoid (diskPair n))).surjective.compactSpace continuous_quotient_mk'
  let e := Equiv.ofBijective (polynomialDiskQuotientSphere n)
    ⟨polynomialDiskQuotientSphere_injective n, polynomialDiskQuotientSphere_surjective n b⟩
  have he : Continuous e := polynomialDiskQuotientSphere_continuous n
  he.homeoOfEquivCompactToT2

lemma polynomialDiskQuotientSphereHomeomorph_projection (n : ℕ) (b : Sphere n) (x : Disk n) :
    polynomialDiskQuotientSphereHomeomorph n b (quotientProjection (diskPair n) x) =
      polynomialDiskSphere n x := rfl


def polynomialReferenceDiskQuotientSphereHomeomorph (n : ℕ) (b : Sphere n) :
    quotientSpace (P202Specs.CellularChains.referenceDiskPair.{w} n) ≃ₜ ULift.{w} (sphere n) :=
  ((P202.Homology.CellularDegrees.Geometry.referenceDiskQuotientHomeomorph n).trans
    (polynomialDiskQuotientSphereHomeomorph n b)).trans Homeomorph.ulift.symm

lemma polynomialReferenceDiskQuotientSphereHomeomorph_projection (n : ℕ) (b : Sphere n)
    (x : (P202Specs.CellularChains.referenceDiskPair.{w} n).space) :
    polynomialReferenceDiskQuotientSphereHomeomorph n b
      (quotientProjection (P202Specs.CellularChains.referenceDiskPair.{w} n) x) =
      ULift.up (polynomialDiskSphere n x.down) := rfl


end PolynomialChart

section SphereFold
open P202Specs.MayerVietoris P202Specs.RelativeSingularChains


open P202Specs.SpheresDisks P202Specs.RealProjectiveHomology

/-- Scale the transverse coordinates and replace the final coordinate. -/
def latitudeVector (n : ℕ) (a b : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (fun i => if i = Fin.last n then b else a * x i)

@[simp] lemma latitudeVector_last (n : ℕ) (a b : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    latitudeVector n a b x (Fin.last n) = b := by simp [latitudeVector]

@[simp] lemma latitudeVector_castSucc (n : ℕ) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin (n+1))) (i : Fin n) :
    latitudeVector n a b x i.castSucc = a * x i.castSucc := by
  simp [latitudeVector, Fin.castSucc_ne_last]

lemma latitudeVector_norm_sq (n : ℕ) (a b : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    ‖latitudeVector n a b x‖^2 = a^2 * (‖x‖^2 - x (Fin.last n)^2) + b^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [latitudeVector_castSucc, latitudeVector_last, mul_pow]
  rw [← Finset.mul_sum]
  ring

lemma latitudeVector_inner (n : ℕ) (a b : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    inner ℝ x (latitudeVector n a b x) =
      a * (‖x‖^2 - x (Fin.last n)^2) + b * x (Fin.last n) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_castSucc,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [latitudeVector_castSucc, latitudeVector_last, star_trivial]
  simp_rw [show ∀ i : Fin n, (a * x i.castSucc) * x i.castSucc = a * (x i.castSucc)^2 by
    intro i; ring]
  rw [← Finset.mul_sum]
  ring

lemma latitudeVector_continuous (n : ℕ) {X : Type} [TopologicalSpace X]
    (a b : X → ℝ) (x : X → EuclideanSpace ℝ (Fin (n+1)))
    (ha : Continuous a) (hb : Continuous b) (hx : Continuous x) :
    Continuous (fun y => latitudeVector n (a y) (b y) (x y)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  dsimp only [latitudeVector]
  split_ifs
  · exact hb
  · exact ha.mul ((PiLp.continuous_apply 2 _ i).comp hx)

lemma sphere_norm (n : ℕ) (x : sphere n) : ‖x.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

lemma sphere_last_bound (n : ℕ) (x : sphere n) : |x.val (Fin.last n)| ≤ 1 := by
  simpa only [sphere_norm, Real.norm_eq_abs] using PiLp.norm_apply_le x.val (Fin.last n)

/-- The polynomial hemisphere-fold map. -/
def foldVector (n : ℕ) (x : sphere n) : EuclideanSpace ℝ (Fin (n+1)) :=
  latitudeVector n (2 * x.val (Fin.last n))
    (2 * (x.val (Fin.last n))^2 - 1) x.val

lemma foldVector_norm (n : ℕ) (x : sphere n) : ‖foldVector n x‖ = 1 := by
  have h := latitudeVector_norm_sq n (2 * x.val (Fin.last n))
    (2 * (x.val (Fin.last n))^2 - 1) x.val
  rw [sphere_norm] at h
  change ‖foldVector n x‖^2 = _ at h
  have hs : ‖foldVector n x‖^2 = 1 := by nlinarith [h]
  nlinarith [norm_nonneg (foldVector n x)]

def sphereFold (n : ℕ) : sphere n ⟶ sphere n :=
  TopCat.ofHom ⟨fun x => ⟨foldVector n x, by
    simpa only [Metric.mem_sphere, dist_zero_right] using foldVector_norm n x⟩,
    (latitudeVector_continuous n _ _ _
      (continuous_const.mul ((PiLp.continuous_apply 2 _ (Fin.last n)).comp continuous_subtype_val))
      ((continuous_const.mul (((PiLp.continuous_apply 2 _ (Fin.last n)).comp continuous_subtype_val).pow 2)).sub continuous_const)
      continuous_subtype_val).subtype_mk _⟩


def northFoldVector (n : ℕ) (x : sphere n) : EuclideanSpace ℝ (Fin (n+1)) :=
  latitudeVector n (2 * max (x.val (Fin.last n)) 0)
    (2 * (max (x.val (Fin.last n)) 0)^2 - 1) x.val

lemma northFoldVector_norm (n : ℕ) (x : sphere n) : ‖northFoldVector n x‖ = 1 := by
  by_cases hx : x.val (Fin.last n) ≤ 0
  · have h := latitudeVector_norm_sq n 0 (-1) x.val
    have heq : northFoldVector n x = latitudeVector n 0 (-1) x.val := by
      simp [northFoldVector, max_eq_right hx]
    rw [heq]
    nlinarith [h, norm_nonneg (latitudeVector n 0 (-1) x.val)]
  · have heq : northFoldVector n x = foldVector n x := by
      simp [northFoldVector, foldVector, max_eq_left (le_of_not_ge hx)]
    rw [heq, foldVector_norm]

lemma northFoldVector_inner_nonneg (n : ℕ) (x : sphere n) :
    0 ≤ inner ℝ x.val (northFoldVector n x) := by
  rw [northFoldVector, latitudeVector_inner, sphere_norm]
  by_cases hx : x.val (Fin.last n) ≤ 0
  · rw [max_eq_right hx]
    nlinarith
  · rw [max_eq_left (le_of_not_ge hx)]
    nlinarith

def northFold (n : ℕ) : sphere n ⟶ sphere n :=
  TopCat.ofHom ⟨fun x => ⟨northFoldVector n x, by
    simpa only [Metric.mem_sphere, dist_zero_right] using northFoldVector_norm n x⟩,
    (latitudeVector_continuous n _ _ _
      (continuous_const.mul (((PiLp.continuous_apply 2 _ (Fin.last n)).comp continuous_subtype_val).max continuous_const))
      ((continuous_const.mul ((((PiLp.continuous_apply 2 _ (Fin.last n)).comp continuous_subtype_val).max continuous_const).pow 2)).sub continuous_const)
      continuous_subtype_val).subtype_mk _⟩

lemma latitudeVector_neg (n : ℕ) (a b : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    latitudeVector n (-a) b (-x) = latitudeVector n a b x := by
  ext i
  simp only [latitudeVector, PiLp.toLp_apply]
  split_ifs
  · rfl
  · simp

lemma foldVector_antipodal (n : ℕ) (x : sphere n) :
    foldVector n (antipodal n x) = foldVector n x := by
  simp only [foldVector, antipodal, TopCat.ofHom, TopCat.hom_ofHom, ContinuousMap.coe_mk,
    PiLp.neg_apply, neg_sq, mul_neg]
  exact latitudeVector_neg _ _ _ _

lemma northFold_of_nonneg (n : ℕ) (x : sphere n) (hx : 0 ≤ x.val (Fin.last n)) :
    northFold n x = sphereFold n x := by
  apply Subtype.ext
  change northFoldVector n x = foldVector n x
  simp [northFoldVector, foldVector, max_eq_left hx]

lemma northFold_antipodal_of_nonpos (n : ℕ) (x : sphere n)
    (hx : x.val (Fin.last n) ≤ 0) :
    northFold n (antipodal n x) = sphereFold n x := by
  have hneg : 0 ≤ (antipodal n x).val (Fin.last n) := by
    change 0 ≤ -x.val (Fin.last n)
    linarith
  rw [northFold_of_nonneg n _ hneg]
  exact Subtype.ext (foldVector_antipodal n x)

/-- Shrink an equatorial latitude band to zero. -/
def beltFunction (t : ℝ) : ℝ := max (t - 1/2) 0 + min (t + 1/2) 0

lemma beltFunction_odd (t : ℝ) : beltFunction (-t) = -beltFunction t := by
  unfold beltFunction
  by_cases h : t ≤ -(1/2)
  · have h1 : t-1/2 ≤ 0 := by linarith
    have h2 : t+1/2 ≤ 0 := by linarith
    have h3 : 0 ≤ -t-1/2 := by linarith
    have h4 : 0 ≤ -t+1/2 := by linarith
    rw [max_eq_right h1, min_eq_left h2, max_eq_left h3, min_eq_right h4]
    ring
  · by_cases h' : 1/2 ≤ t
    · have h1 : 0 ≤ t-1/2 := by linarith
      have h2 : 0 ≤ t+1/2 := by linarith
      have h3 : -t-1/2 ≤ 0 := by linarith
      have h4 : -t+1/2 ≤ 0 := by linarith
      rw [max_eq_left h1, min_eq_right h2, max_eq_right h3, min_eq_left h4]
      ring
    · have h1 : t-1/2 ≤ 0 := by linarith
      have h2 : 0 ≤ t+1/2 := by linarith
      have h3 : -t-1/2 ≤ 0 := by linarith
      have h4 : 0 ≤ -t+1/2 := by linarith
      rw [max_eq_right h1, min_eq_right h2, max_eq_right h3, min_eq_right h4]
      ring

lemma beltFunction_continuous : Continuous beltFunction := by
  exact ((continuous_id.sub continuous_const).max continuous_const).add
    ((continuous_id.add continuous_const).min continuous_const)

lemma beltFunction_nonpos {t : ℝ} (h : t ≤ 1/2) : beltFunction t ≤ 0 := by
  have h1 : t-1/2 ≤ 0 := by linarith
  simp only [beltFunction, max_eq_right h1, zero_add]
  exact min_le_right _ _

lemma beltFunction_nonneg {t : ℝ} (h : -(1/2) ≤ t) : 0 ≤ beltFunction t := by
  have h1 : 0 ≤ t+1/2 := by linarith
  simp only [beltFunction, min_eq_right h1, add_zero]
  exact le_max_right _ _

lemma beltVector_inner_positive (n : ℕ) (x : sphere n) :
    0 < inner ℝ x.val (latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val) := by
  rw [latitudeVector_inner, sphere_norm]
  obtain ⟨hl, hu⟩ := abs_le.mp (sphere_last_bound n x)
  let t := x.val (Fin.last n)
  change 0 < 1 * (1^2 - t^2) + beltFunction t * t
  by_cases h : t ≤ -(1/2)
  · have h1 : t-1/2 ≤ 0 := by linarith
    have h2 : t+1/2 ≤ 0 := by linarith
    rw [beltFunction, max_eq_right h1, min_eq_left h2]
    dsimp [t] at *
    nlinarith
  · by_cases h' : 1/2 ≤ t
    · have h1 : 0 ≤ t-1/2 := by linarith
      have h2 : 0 ≤ t+1/2 := by linarith
      rw [beltFunction, max_eq_left h1, min_eq_right h2]
      dsimp [t] at *
      nlinarith
    · have h1 : t-1/2 ≤ 0 := by linarith
      have h2 : 0 ≤ t+1/2 := by linarith
      rw [beltFunction, max_eq_right h1, min_eq_right h2]
      nlinarith

lemma beltVector_ne_zero (n : ℕ) (x : sphere n) :
    latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val ≠ 0 := by
  intro h
  have hh := beltVector_inner_positive n x
  rw [h, inner_zero_right] at hh
  exact lt_irrefl _ hh

def beltRetraction (n : ℕ) : sphere n ⟶ sphere n :=
  TopCat.ofHom ⟨fun x => ⟨NormedSpace.normalize
    (latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val), by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        NormedSpace.norm_normalize (beltVector_ne_zero n x)⟩, by
    have hc : Continuous (fun x : sphere n =>
        latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val) :=
      latitudeVector_continuous n _ _ _ continuous_const
        (beltFunction_continuous.comp ((PiLp.continuous_apply 2 _ (Fin.last n)).comp
          continuous_subtype_val)) continuous_subtype_val
    apply Continuous.subtype_mk
    exact (hc.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (beltVector_ne_zero n x))).smul hc⟩


lemma beltRetraction_nonpos (n : ℕ) (x : sphere n) (h : x.val (Fin.last n) ≤ 1/2) :
    (beltRetraction n x).val (Fin.last n) ≤ 0 := by
  change (‖latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val‖⁻¹ •
    latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val) (Fin.last n) ≤ 0
  simp only [PiLp.smul_apply, smul_eq_mul, latitudeVector_last]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
    (beltFunction_nonpos h)

lemma beltRetraction_nonneg (n : ℕ) (x : sphere n) (h : -(1/2) ≤ x.val (Fin.last n)) :
    0 ≤ (beltRetraction n x).val (Fin.last n) := by
  change 0 ≤ (‖latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val‖⁻¹ •
    latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val) (Fin.last n)
  simp only [PiLp.smul_apply, smul_eq_mul, latitudeVector_last]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (beltFunction_nonneg h)

lemma beltRetraction_antipodal (n : ℕ) (x : sphere n) :
    beltRetraction n (antipodal n x) = antipodal n (beltRetraction n x) := by
  apply Subtype.ext
  change NormedSpace.normalize
    (latitudeVector n 1 (beltFunction (-x.val (Fin.last n))) (-x.val)) =
      -NormedSpace.normalize (latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val)
  rw [beltFunction_odd]
  have heq : latitudeVector n 1 (-beltFunction (x.val (Fin.last n))) (-x.val) =
      -latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val := by
    ext i
    simp only [latitudeVector, PiLp.toLp_apply, PiLp.neg_apply]
    split_ifs <;> simp
  rw [heq, NormedSpace.normalize_neg]

lemma beltRetraction_inner_nonneg (n : ℕ) (x : sphere n) :
    0 ≤ inner ℝ x.val (beltRetraction n x).val := by
  change 0 ≤ inner ℝ x.val
    (‖latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val‖⁻¹ •
      latitudeVector n 1 (beltFunction (x.val (Fin.last n))) x.val)
  rw [real_inner_smul_right]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (le_of_lt (beltVector_inner_positive n x))

def southSpherePoint (n : ℕ) : sphere n :=
  ⟨latitudeVector n 0 (-1) 0, by
    have h := latitudeVector_norm_sq n 0 (-1) 0
    have hnorm : ‖latitudeVector n 0 (-1) 0‖ = 1 := by
      nlinarith [h, norm_nonneg (latitudeVector n 0 (-1) 0)]
    simpa only [Metric.mem_sphere, dist_zero_right] using hnorm⟩

lemma northFold_of_nonpos (n : ℕ) (x : sphere n) (hx : x.val (Fin.last n) ≤ 0) :
    northFold n x = southSpherePoint n := by
  apply Subtype.ext
  change northFoldVector n x = latitudeVector n 0 (-1) 0
  simp only [northFoldVector, max_eq_right hx, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_sub]
  ext i
  simp only [latitudeVector, PiLp.toLp_apply]
  split_ifs <;> simp

lemma northFold_degree (n : ℕ) : P202Specs.Degree.degree n (northFold n) = 1 := by
  have h := P202.Degree.homotopyInvariant n (𝟙 (sphere n)) (northFold n)
    (sphereChordHomotopy n (𝟙 (sphere n)) (northFold n)
      (northFoldVector_inner_nonneg n))
  exact h.symm.trans (P202.Degree.identity n)

lemma beltRetraction_degree (n : ℕ) : P202Specs.Degree.degree n (beltRetraction n) = 1 := by
  have h := P202.Degree.homotopyInvariant n (𝟙 (sphere n)) (beltRetraction n)
    (sphereChordHomotopy n (𝟙 (sphere n)) (beltRetraction n)
      (beltRetraction_inner_nonneg n))
  exact h.symm.trans (P202.Degree.identity n)


lemma sphereFold_degree (n : ℕ) :
    P202Specs.Degree.degree n (sphereFold n) = 1 + (-1 : ℤ)^(n+1) := by
  let U : Set (sphere n) := {x | x.val (Fin.last n) < 1/2}
  let V : Set (sphere n) := {x | -(1/2) < x.val (Fin.last n)}
  have hc : Continuous (fun x : sphere n => x.val (Fin.last n)) :=
    (PiLp.continuous_apply 2 _ (Fin.last n)).comp continuous_subtype_val
  have hU : IsOpen U := isOpen_lt hc continuous_const
  have hV : IsOpen V := isOpen_lt continuous_const hc
  have hcover : U ∪ V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x.val (Fin.last n) < 1/2
    · exact Or.inl hx
    · right
      change -(1/2) < x.val (Fin.last n)
      linarith
  have hsum := degreeSum_of_cover n U V hU hV hcover
    (beltRetraction n ≫ sphereFold n)
    (P202Specs.Degree.constantMap n (southSpherePoint n))
    (beltRetraction n ≫ northFold n)
    (antipodal n ≫ beltRetraction n ≫ northFold n)
    (Or.inr (by
      intro x hx
      have hr : (beltRetraction n x).val (Fin.last n) ≤ 0 :=
        beltRetraction_nonpos n x (le_of_lt hx)
      change sphereFold n (beltRetraction n x) =
          northFold n (beltRetraction n (antipodal n x)) ∧
        southSpherePoint n = northFold n (beltRetraction n x)
      constructor
      · rw [beltRetraction_antipodal]
        exact (northFold_antipodal_of_nonpos n _ hr).symm
      · exact (northFold_of_nonpos n _ hr).symm))
    (Or.inl (by
      intro x hx
      have hr : 0 ≤ (beltRetraction n x).val (Fin.last n) :=
        beltRetraction_nonneg n x (le_of_lt hx)
      change sphereFold n (beltRetraction n x) = northFold n (beltRetraction n x) ∧
        southSpherePoint n = northFold n (beltRetraction n (antipodal n x))
      constructor
      · exact (northFold_of_nonneg n _ hr).symm
      · rw [beltRetraction_antipodal]
        symm
        apply northFold_of_nonpos
        change -(beltRetraction n x).val (Fin.last n) ≤ 0
        linarith))
  rw [P202.Degree.composition n, P202.Degree.constant n,
    P202.Degree.composition n, P202.Degree.composition n, P202.Degree.composition n,
    antipodalDegree n] at hsum
  simpa only [northFold_degree, beltRetraction_degree,
    mul_one, one_mul, add_zero] using hsum


end SphereFold

section AttachingCalculation
open P202.Cellular P202Specs.RelativeSingularChains P202Specs.CellularChains
open P202Specs.CellularDegrees P202Specs.GoodPairQuotient

lemma polynomialDiskSphere_eq_fold_hemisphere (n : ℕ) (z : Disk n) :
    polynomialDiskSphere n z = sphereFold n (hemisphere n n le_rfl z) := by
  apply Subtype.ext
  ext k
  have hz : ‖z.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  have hs := Real.sq_sqrt (show 0 ≤ 1-‖z.val‖^2 by nlinarith [norm_nonneg z.val])
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [polynomialDiskSphere, ContinuousMap.coe_mk, polynomialDiskVector,
      PiLp.toLp_apply, Fin.val_last, lt_self_iff_false, dite_false,
      sphereFold, TopCat.ofHom, TopCat.hom_ofHom, foldVector, latitudeVector_last,
      hemisphere, hemisphereVector]
    simp only [ContinuousMap.coe_mk, PiLp.toLp_apply, Fin.val_last, lt_self_iff_false,
      dite_false, ite_true]
    nlinarith
  · simp [polynomialDiskSphere, polynomialDiskVector, sphereFold, foldVector,
      latitudeVector_castSucc, hemisphere, hemisphereVector]

lemma polynomial_chartAttachingMap (m n : ℕ) (hm : n+1 ≤ m) (b : Sphere n) :
    letI := standardCW m
    ∀ (c : Cell (Space m) (n+1)) (d : Cell (Space m) n)
      (q : P202Specs.CellularChains.skeletalPair (Space m) n ⟶
        quotientPair (P202Specs.CellularChains.referenceDiskPair n)),
      (∀ z : (P202Specs.CellularChains.referenceDiskPair n).space,
        q.map ((P202Specs.CellularChains.characteristicPairMap n d).map z) =
          quotientProjection (P202Specs.CellularChains.referenceDiskPair n) z) →
      P202Specs.CellularDegrees.chartAttachingMap (Space m) n
        (P202.Homology.CellularDegrees.ConnectingBridge.referenceBoundarySphereHomeomorph n)
        (polynomialReferenceDiskQuotientSphereHomeomorph n b) q c = sphereFold n := by
  letI := standardCW m
  intro c d q hq
  have hc : c = (show {i : Unit // n+1 ≤ m} from ⟨(), hm⟩) := by
    apply Subtype.ext
    exact Subsingleton.elim _ _
  subst c
  have hd : d = (show {i : Unit // n ≤ m} from ⟨(), by omega⟩) := by
    apply Subtype.ext
    exact Subsingleton.elim _ _
  subst d
  let hS := P202.Homology.CellularDegrees.ConnectingBridge.referenceBoundarySphereHomeomorph n
  let hT := polynomialReferenceDiskQuotientSphereHomeomorph n b
  let f := P202Specs.CellularDegrees.chartAttachingMap (Space m) n hS hT q
    (show {i : Unit // n+1 ≤ m} from ⟨(), hm⟩)
  have hfupper (x : sphere n) (hx : 0 ≤ x.val (Fin.last n)) : f x = sphereFold n x := by
    obtain ⟨z, hz⟩ := hemisphere_top_preimage n x hx
    have ha : P202Specs.CellularDegrees.attachingBoundary (Space m) n
          (show {i : Unit // n+1 ≤ m} from ⟨(), hm⟩) (hS.symm (ULift.up x)) =
        (P202Specs.CellularChains.characteristicPairMap n
          (show {i : Unit // n ≤ m} from ⟨(), by omega⟩)).map (ULift.up z) := by
      apply Subtype.ext
      change standardCharacteristic m (n+1) hm (boundaryInclusion (n+1) x) =
        standardCharacteristic m n (by omega) z
      exact characteristic_boundary_reduction m n hm x z hz
    change (hT (q.map (P202Specs.CellularDegrees.attachingBoundary (Space m) n
      (show {i : Unit // n+1 ≤ m} from ⟨(), hm⟩) (hS.symm (ULift.up x))))).down = _
    rw [ha, hq]
    change polynomialDiskSphere n z = sphereFold n x
    rw [polynomialDiskSphere_eq_fold_hemisphere, hz]
  have hfantipodal (x : sphere n) : f (antipodal n x) = f x := by
    apply congrArg (fun y => (hT (q.map y)).down)
    apply Subtype.ext
    change standardCharacteristic m (n+1) hm (boundaryInclusion (n+1) (antipodal n x)) =
      standardCharacteristic m (n+1) hm (boundaryInclusion (n+1) x)
    exact characteristic_boundary_antipodal m (n+1) hm _ _ rfl
  ext x : 1
  change f x = sphereFold n x
  by_cases hx : 0 ≤ x.val (Fin.last n)
  · exact hfupper x hx
  · have hxneg : 0 ≤ (antipodal n x).val (Fin.last n) := by
      change 0 ≤ -x.val (Fin.last n)
      linarith
    rw [← hfantipodal, hfupper _ hxneg]
    exact Subtype.ext (foldVector_antipodal n x)


def boundaryPole (n : ℕ) (hn : 0 < n) : Sphere n :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩

def standardAttachingCharts (n : ℕ) (hn : 0 < n) : AttachingCharts n where
  boundaryPoint := ⟨ULift.up (boundaryInclusion n (boundaryPole n hn)), by
    change ‖(boundaryPole n hn).val‖ = 1
    simpa only [Metric.mem_sphere, dist_zero_right] using (boundaryPole n hn).property⟩
  source := P202.Homology.CellularDegrees.ConnectingBridge.referenceBoundarySphereHomeomorph n
  target := polynomialReferenceDiskQuotientSphereHomeomorph n (boundaryPole n hn)


/-- The actual standard CW structure and its complete characteristic-compatible
cellular differential, with the coincident-endpoint convention in degree one. -/
theorem cellularModel : Expected.cellularModel := by
  intro m
  letI C := standardCW m
  have hstd : StandardCW m C := standardCW_standard m
  refine ⟨C, hstd, ?_⟩
  apply cellularCalculation_of_chartDegrees hstd standardAttachingCharts
  intro n hn c d q hq
  have hq' (z : (referenceDiskPair.{0} n).space) :
      q.map ((characteristicPairMap n d).map z) = quotientProjection _ z := by
    classical
    simpa using hq d z
  change P202Specs.Degree.degree n (chartAttachingMap (Space m) n
    (P202.Homology.CellularDegrees.ConnectingBridge.referenceBoundarySphereHomeomorph n)
    (polynomialReferenceDiskQuotientSphereHomeomorph n (boundaryPole n hn)) q c) = _
  rw [polynomial_chartAttachingMap m n c.property (boundaryPole n hn) c d q hq']
  exact sphereFold_degree n

/-- The full integral homology table for every finite-dimensional real
projective quotient, including dimension zero and all degrees above m. -/
theorem integralHomology : Expected.integralHomology := by
  intro m
  obtain ⟨C, hstd, hcalc⟩ := cellularModel m
  letI := C
  exact homologyCalculation_of_cellularModel hstd hcalc

end AttachingCalculation

end P202.Homology.RealProjectiveHomology
