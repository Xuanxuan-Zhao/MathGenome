import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.ComplexProjectiveHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularComparison
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.LocalAtTarget

noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace P202.ComplexProjective

lemma mk_eq_mk {m : ℕ} (v w : Fin (m+1) → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk v hv = mk w hw ↔ ∃ a : ℂˣ, a • w = v :=
  Projectivization.mk_eq_mk_iff ℂ v w hv hw

lemma mk_eq_mk' {m : ℕ} (v w : Fin (m+1) → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk v hv = mk w hw ↔ ∃ a : ℂ, a • w = v :=
  Projectivization.mk_eq_mk_iff' ℂ v w hv hw

lemma quotientMap_quotient (m : ℕ) : IsQuotientMap (quotientMap m) :=
  isQuotientMap_quotient_mk'

lemma quotientMap_continuous (m : ℕ) : Continuous (quotientMap m) :=
  (quotientMap_quotient m).continuous

lemma lowerSpace_mk {m k : ℕ} (v : Fin (m+1) → ℂ) (hv : v ≠ 0) :
    mk v hv ∈ lowerSpace m k ↔ ∀ i, k ≤ i.val → v i = 0 := by
  constructor
  · rintro ⟨w, hw, he, hs⟩ i hi
    obtain ⟨a, ha⟩ := (mk_eq_mk w v hw hv).mp he
    have heq : (a : ℂ) * v i = 0 := by
      simpa [Units.smul_def] using (congrFun ha i).trans (hs i hi)
    exact (mul_eq_zero.mp heq).resolve_left a.ne_zero
  · intro hs
    exact ⟨v, hv, rfl, hs⟩

lemma lowerSpace_zero (m : ℕ) : lowerSpace m 0 = ∅ := by
  ext p
  change (∃ (v : Fin (m+1) → ℂ) (hv : v ≠ 0), mk v hv = p ∧
    ∀ i, 0 ≤ i.val → v i = 0) ↔ False
  constructor
  · rintro ⟨v, hv, _, hs⟩
    exact hv (funext (fun i => hs i (Nat.zero_le _)))
  · exact False.elim

lemma lowerSpace_top (m : ℕ) : lowerSpace m (m+1) = univ := by
  apply Set.eq_univ_of_forall
  intro p
  induction p using Projectivization.ind with | h v hv =>
  exact (lowerSpace_mk v hv).mpr (fun i hi => (Nat.not_le_of_lt i.isLt hi).elim)

lemma lowerSpace_mono (m : ℕ) {k l : ℕ} (h : k ≤ l) : lowerSpace m k ⊆ lowerSpace m l := by
  rintro p ⟨v, hv, he, hs⟩
  exact ⟨v, hv, he, fun i hi => hs i (h.trans hi)⟩

lemma stratum_mk {m r : ℕ} (h : r ≤ m) (v : Fin (m+1) → ℂ) (hv : v ≠ 0) :
    mk v hv ∈ stratum m r ↔
      (∀ i, r+1 ≤ i.val → v i = 0) ∧ v ⟨r, by omega⟩ ≠ 0 := by
  rw [stratum, Set.mem_sdiff, lowerSpace_mk, lowerSpace_mk]
  constructor
  · rintro ⟨hs, hn⟩
    refine ⟨hs, fun hz => hn (fun i hi => ?_)⟩
    by_cases he : i.val = r
    · simpa [show i = (⟨r, by omega⟩ : Fin (m+1)) from Fin.ext he] using hz
    · exact hs i (by omega)
  · rintro ⟨hs, hn⟩
    exact ⟨hs, fun ha => hn (ha ⟨r, by omega⟩ (le_refl r))⟩

lemma affineChart_injective (m r : ℕ) (h : r ≤ m) :
    Function.Injective (affineChart m r h) := by
  intro z w he
  obtain ⟨a, ha⟩ := (mk_eq_mk' _ _ _ _).mp he
  have har := congrFun ha ⟨r, by omega⟩
  have ha1 : a = 1 := by simpa [coordinateVector] using har
  subst a
  ext i
  have hai := congrFun ha ⟨i.val, by omega⟩
  simpa [coordinateVector, i.isLt] using hai.symm

lemma affineChart_range (m r : ℕ) (h : r ≤ m) :
    range (affineChart m r h) = stratum m r := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    apply (stratum_mk h _ _).mpr
    constructor
    · intro i hi
      simp [coordinateVector, show ¬ i.val < r by omega, show i.val ≠ r by omega]
    · simp [coordinateVector]
  · intro hp
    induction p using Projectivization.ind with | h v hv =>
    obtain ⟨hs, hn⟩ := (stratum_mk h v hv).mp hp
    let z : Fin r → ℂ := fun i => (v ⟨r, by omega⟩)⁻¹ * v ⟨i.val, by omega⟩
    refine ⟨z, (mk_eq_mk' _ _ _ _).mpr ⟨(v ⟨r, by omega⟩)⁻¹, ?_⟩⟩
    ext i
    by_cases hi : i.val < r
    · simp [coordinateVector, hi, z]
    · by_cases he : i.val = r
      · have hei : i = (⟨r, by omega⟩ : Fin (m+1)) := Fin.ext he
        simp [coordinateVector, hi, he, hei, hn]
      · simp [coordinateVector, hi, he, hs i (by omega)]

lemma affineChart_continuous (m r : ℕ) (h : r ≤ m) :
    Continuous (affineChart m r h) := by
  change Continuous (quotientMap m ∘
    (fun z : Fin r → ℂ => ⟨coordinateVector m r z 1, coordinateVector_nonzero m r h z⟩))
  apply (quotientMap_continuous m).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  dsimp [coordinateVector]
  split
  · exact continuous_apply _
  · exact continuous_const

lemma characteristic_continuous (m r : ℕ) (h : r ≤ m) :
    Continuous (characteristic m r h) := by
  change Continuous (quotientMap m ∘
    (fun z : ComplexDisk r => ⟨diskVector m r z, diskVector_nonzero m r h z⟩))
  apply (quotientMap_continuous m).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  dsimp [diskVector, coordinateVector]
  split
  · exact (PiLp.continuous_apply 2 _ _).comp continuous_subtype_val
  · split
    · exact Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (continuous_const.sub (continuous_subtype_val.norm.pow 2)))
    · exact continuous_const

lemma characteristic_boundary (m r : ℕ) (h : r ≤ m) (z : ComplexDisk r)
    (hz : ‖z.val‖ = 1) : characteristic m r h z ∈ lowerSpace m r := by
  apply (lowerSpace_mk _ _).mpr
  intro i hi
  simp [diskVector, coordinateVector, show ¬ i.val < r by omega, hz]

instance pointSubsingleton : Subsingleton (Space 0) where
  allEq p q := by
    induction p using Projectivization.ind with | h v hv =>
    induction q using Projectivization.ind with | h w hw =>
    have hv0 : v 0 ≠ 0 := fun h => hv (by ext i; have hi : i = 0 := Fin.ext (by omega); simpa [hi] using h)
    have hw0 : w 0 ≠ 0 := fun h => hw (by ext i; have hi : i = 0 := Fin.ext (by omega); simpa [hi] using h)
    apply (mk_eq_mk' v w hv hw).mpr
    refine ⟨v 0 / w 0, ?_⟩
    ext i
    have hi : i = 0 := Fin.ext (by omega)
    simp [hi, div_mul_cancel₀ _ hw0]

instance (m : ℕ) : Nonempty (Space m) :=
  ⟨affineChart m 0 (Nat.zero_le _) (fun i => Fin.elim0 i)⟩

def pointHomeomorph : Space 0 ≃ₜ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := Classical.choice inferInstance
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

theorem pointCase : Expected.pointCase := ⟨pointHomeomorph⟩

end P202.ComplexProjective


namespace P202.ComplexProjective
open P202.Cellular P202Specs.CellularChains P202Specs.SingularChains

/- The purely cellular calculation is separate from the construction of the
    CW structure; no claim that the quotient is CW is assumed in the final Spec. -/
section EvenCells
variable (X : Type) [TopologicalSpace X] [CWStructure X] (m : ℕ)
variable (labels : ∀ n, Cell X n ≃ CellIndex m n)

lemma cellIndex_subsingleton (n : ℕ) : Subsingleton (CellIndex m n) := by
  refine ⟨fun r s => ?_⟩
  apply Subtype.ext
  apply Fin.ext
  have hr := r.property
  have hs := s.property
  omega

lemma cellIndex_isEmpty (n : ℕ) (h : ¬ ∃ r ≤ m, n = 2*r) : IsEmpty (CellIndex m n) :=
  ⟨fun r => h ⟨r.val.val, by have := r.val.isLt; omega, r.property⟩⟩

include labels

lemma chainGroup_isZero (n : ℕ) (h : ¬ ∃ r ≤ m, n = 2*r) :
    IsZero (chainGroup X ℤ ℤ n) := by
  letI := cellIndex_isEmpty m n h
  letI : IsEmpty (Cell X n) := Function.isEmpty (labels n)
  obtain ⟨e⟩ := P202.Homology.cellularCellGroups X ℤ ℤ n
  exact ModuleCat.isZero_iff_subsingleton.mpr (e.injective.subsingleton)

lemma evenCells_differential_zero (n : ℕ) : differential X ℤ ℤ n = 0 := by
  by_cases hn : n % 2 = 0
  · exact (chainGroup_isZero X m labels (n+1) (by
      rintro ⟨r, _, he⟩; omega)).eq_zero_of_src _
  · exact (chainGroup_isZero X m labels n (by
      rintro ⟨r, _, he⟩; omega)).eq_zero_of_tgt _

lemma evenCells_d_zero (i j : ℕ) : (cellularComplex X ℤ ℤ).d i j = 0 := by
  by_cases hij : i = j+1
  · subst i
    exact (ChainComplex.of_d _ _ j).trans (evenCells_differential_zero X m labels j)
  · exact ChainComplex.of_d_ne _ _ hij

/-- With no adjacent nonzero cellular groups, cycles and homology equal chains. -/
def evenCells_homologyIso (n : ℕ) :
    (cellularComplex X ℤ ℤ).homology n ≅ chainGroup X ℤ ℤ n :=
  (ShortComplex.LeftHomologyData.ofZeros ((cellularComplex X ℤ ℤ).sc n)
    (evenCells_d_zero X m labels _ _) (evenCells_d_zero X m labels _ _)).homologyIso

lemma integralHomology_of_evenCells (j : ℕ) :
    ((∃ r ≤ m, j = 2*r) →
      Nonempty (P202Specs.SingularChains.homology ℤ ℤ (TopCat.of X) (j : ℤ) ≃ₗ[ℤ] ℤ)) ∧
    ((¬ ∃ r ≤ m, j = 2*r) →
      IsZero (P202Specs.SingularChains.homology ℤ ℤ (TopCat.of X) (j : ℤ))) := by
  let e := (P202.Homology.CellularComparison.comparisonIso X ℤ ℤ j).symm ≪≫
    evenCells_homologyIso X m labels j
  constructor
  · rintro ⟨r, hr, hj⟩
    obtain ⟨g⟩ := P202.Homology.cellularCellGroups X ℤ ℤ j
    letI : Subsingleton (CellIndex m j) := cellIndex_subsingleton m j
    letI : Subsingleton (Cell X j) := (labels j).injective.subsingleton
    let c : Cell X j := (labels j).symm ⟨⟨r, by omega⟩, hj⟩
    exact ⟨e.toLinearEquiv.trans (g.trans (Finsupp.uniqueLinearEquiv ℤ ℤ c))⟩
  · intro hj
    exact e.isZero_iff.mpr (chainGroup_isZero X m labels j hj)

end EvenCells

/-- Assembly of the required integral computation once the quotient geometry
    has been constructed. This is a helper, not the submitted final theorem. -/
lemma homology_of_cellStructure (hc : Expected.cellStructure) : Expected.homology := by
  intro m j
  obtain ⟨C, labels, _⟩ := hc m
  letI : CWStructure (Space m) := C
  exact integralHomology_of_evenCells (Space m) m labels j

end P202.ComplexProjective

namespace P202.ComplexProjective

abbrev NonzeroVectors (m : ℕ) := {v : Fin (m+1) → ℂ // v ≠ 0}

def scaleHomeomorph (m : ℕ) (a : ℂˣ) : NonzeroVectors m ≃ₜ NonzeroVectors m where
  toFun v := ⟨a • v.val, by
    change (a : ℂ) • v.val ≠ 0
    exact smul_ne_zero a.ne_zero v.property⟩
  invFun v := ⟨a⁻¹ • v.val, by
    change ((a⁻¹ : ℂˣ) : ℂ) • v.val ≠ 0
    exact smul_ne_zero (a⁻¹).ne_zero v.property⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp
  continuous_toFun := (continuous_const_smul a).comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := (continuous_const_smul a⁻¹).comp continuous_subtype_val |>.subtype_mk _

lemma quotientMap_open (m : ℕ) : IsOpenMap (quotientMap m) := by
  intro U hU
  rw [← (quotientMap_quotient m).isOpen_preimage]
  have hs : quotientMap m ⁻¹' (quotientMap m '' U) =
      ⋃ a : ℂˣ, scaleHomeomorph m a '' U := by
    ext v
    constructor
    · rintro ⟨w, hw, he⟩
      obtain ⟨a, ha⟩ := (mk_eq_mk _ _ _ _).mp he.symm
      exact mem_iUnion.mpr ⟨a, w, hw, Subtype.ext ha⟩
    · intro hv
      obtain ⟨a, w, hw, he⟩ := mem_iUnion.mp hv
      refine ⟨w, hw, ?_⟩
      apply (mk_eq_mk _ _ _ _).mpr
      exact ⟨a⁻¹, by
        have hva : a • w.val = v.val := congrArg Subtype.val he
        rw [← hva]; simp⟩
  rw [hs]
  exact isOpen_iUnion (fun a => (scaleHomeomorph m a).isOpenMap U hU)

lemma mk_eq_iff_minors {m : ℕ} (v w : Fin (m+1) → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk v hv = mk w hw ↔ ∀ i j, v i * w j = v j * w i := by
  constructor
  · intro he
    obtain ⟨a, rfl⟩ := (mk_eq_mk' v w hv hw).mp he
    intro i j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro he
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra hn
      exact hw (funext (fun j => by simpa using (not_exists.mp hn j)))
    refine (mk_eq_mk' v w hv hw).mpr ⟨v j / w j, ?_⟩
    ext i
    dsimp
    apply (mul_right_cancel₀ hj)
    calc
      v j / w j * w i * w j = v j * w i := by field_simp
      _ = v i * w j := (he i j).symm

instance spaceT2 (m : ℕ) : T2Space (Space m) := by
  apply (t2Space_iff_of_isOpenQuotientMap
    (IsOpenQuotientMap.of_isOpenMap_isQuotientMap (quotientMap_open m)
      (quotientMap_quotient m))).mpr
  have hs : {p : NonzeroVectors m × NonzeroVectors m |
      quotientMap m p.1 = quotientMap m p.2} =
      ⋂ i, ⋂ j, {p | p.1.val i * p.2.val j = p.1.val j * p.2.val i} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    exact mk_eq_iff_minors _ _ _ _
  rw [hs]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_eq
    (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)))
    (((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))

end P202.ComplexProjective

namespace P202.ComplexProjective

def ratios (m r : ℕ) (h : r ≤ m) : Space m → Fin r → ℂ :=
  Projectivization.lift
    (fun v i => v.val ⟨i.val, by omega⟩ / v.val ⟨r, by omega⟩)
    (by
      intro a b t ha
      have ht : t ≠ 0 := by
        intro ht
        apply a.property
        simpa [ht] using ha
      funext i
      change a.val _ / a.val _ = b.val _ / b.val _
      simp only [ha, Pi.smul_apply, smul_eq_mul]
      exact mul_div_mul_left _ _ ht)

lemma ratios_affineChart (m r : ℕ) (h : r ≤ m) (z : Fin r → ℂ) :
    ratios m r h (affineChart m r h z) = z := by
  ext i
  simp [ratios, affineChart, mk, Projectivization.lift_mk, coordinateVector, i.isLt]

lemma ratios_continuousAt (m r : ℕ) (h : r ≤ m) (v : NonzeroVectors m)
    (hv : v.val ⟨r, by omega⟩ ≠ 0) : ContinuousAt (ratios m r h) (quotientMap m v) := by
  apply (IsOpenQuotientMap.of_isOpenMap_isQuotientMap (quotientMap_open m)
    (quotientMap_quotient m)).continuousAt_comp_iff.mp
  change ContinuousAt (fun w : NonzeroVectors m =>
    fun i : Fin r => w.val ⟨i.val, by omega⟩ / w.val ⟨r, by omega⟩) v
  apply continuousAt_pi.mpr
  intro i
  exact (((continuous_apply _).comp continuous_subtype_val).continuousAt.div
    ((continuous_apply _).comp continuous_subtype_val).continuousAt hv)

lemma affineChart_embedding (m r : ℕ) (h : r ≤ m) : IsEmbedding (affineChart m r h) := by
  let f := Set.rangeFactorization (affineChart m r h)
  let g : range (affineChart m r h) → Fin r → ℂ := fun p => ratios m r h p.val
  have hf : Continuous f := (affineChart_continuous m r h).subtype_mk _
  have hg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro p
    change ContinuousAt (ratios m r h ∘ Subtype.val) p
    apply ContinuousAt.comp _ continuous_subtype_val.continuousAt
    obtain ⟨z, hz⟩ := p.property
    rw [← hz]
    exact ratios_continuousAt m r h
      ⟨coordinateVector m r z 1, coordinateVector_nonzero m r h z⟩ (by simp [coordinateVector])
  have hgf : Function.LeftInverse g f := ratios_affineChart m r h
  exact IsEmbedding.subtypeVal.comp (hgf.isEmbedding hg hf)

theorem coordinateCells : Expected.coordinateCells :=
  fun m r h => ⟨affineChart_embedding m r h, affineChart_range m r h⟩

end P202.ComplexProjective

namespace P202.ComplexProjective

abbrev UnitVectors (m : ℕ) := Metric.sphere (0 : EuclideanSpace ℂ (Fin (m+1))) 1

lemma unitVector_nonzero (m : ℕ) (z : UnitVectors m) :
    (fun i => z.val i) ≠ (0 : Fin (m+1) → ℂ) := by
  intro hz
  have hz0 : z.val = 0 := by ext i; exact congrFun hz i
  have hs := z.property
  simp [hz0] at hs

def sphereProjection (m : ℕ) (z : UnitVectors m) : Space m :=
  mk (fun i => z.val i) (unitVector_nonzero m z)

lemma sphereProjection_continuous (m : ℕ) : Continuous (sphereProjection m) := by
  change Continuous (quotientMap m ∘
    (fun z : UnitVectors m => ⟨(fun i => z.val i), unitVector_nonzero m z⟩))
  apply (quotientMap_continuous m).comp
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)

lemma sphereProjection_surjective (m : ℕ) : Function.Surjective (sphereProjection m) := by
  intro p
  induction p using Projectivization.ind with | h v hv =>
  let x : EuclideanSpace ℂ (Fin (m+1)) := WithLp.toLp 2 v
  have hx : x ≠ 0 := by
    intro hx
    apply hv
    ext i
    exact congrArg (fun x : EuclideanSpace ℂ (Fin (m+1)) => x i) hx
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let z : UnitVectors m := ⟨‖x‖⁻¹ • x, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hn]⟩
  refine ⟨z, (mk_eq_mk' _ _ _ _).mpr ⟨((‖x‖⁻¹ : ℝ) : ℂ), ?_⟩⟩
  ext i
  simp [z, x, Complex.real_smul]

instance spaceCompact (m : ℕ) : CompactSpace (Space m) :=
  (sphereProjection_surjective m).compactSpace (sphereProjection_continuous m)

end P202.ComplexProjective

namespace P202.ComplexProjective

lemma inclusion_continuous (m r : ℕ) (h : r ≤ m) : Continuous (inclusion m r h) := by
  apply (quotientMap_quotient r).continuous_iff.mpr
  change Continuous (quotientMap m ∘ fun v : NonzeroVectors r =>
    ⟨inclusionVector m r h v.val, fun hz =>
      v.property (inclusionVector_injective m r h (by simpa using hz))⟩)
  apply (quotientMap_continuous m).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  dsimp [inclusionVector]
  split
  · exact (continuous_apply _).comp continuous_subtype_val
  · exact continuous_const

lemma inclusion_range (m r : ℕ) (h : r ≤ m) :
    range (inclusion m r h) = lowerSpace m (r+1) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Projectivization.ind with | h v hv =>
    apply (lowerSpace_mk _ _).mpr
    intro i hi
    simp [inclusionVector, show ¬ i.val ≤ r by omega]
  · intro hp
    induction p using Projectivization.ind with | h v hv =>
    have hs := (lowerSpace_mk v hv).mp hp
    let w : Fin (r+1) → ℂ := fun i => v ⟨i.val, by omega⟩
    have hw : w ≠ 0 := by
      intro hw
      apply hv
      ext i
      by_cases hi : i.val < r+1
      · exact congrFun hw ⟨i.val, hi⟩
      · exact hs i (by omega)
    refine ⟨mk w hw, ?_⟩
    apply (mk_eq_mk' _ _ _ _).mpr
    refine ⟨1, ?_⟩
    ext i
    dsimp [inclusionVector]
    split
    · simp [w]
    · simp [hs i (by omega)]

lemma inclusion_embedding (m r : ℕ) (h : r ≤ m) : IsEmbedding (inclusion m r h) :=
  ((inclusion_continuous m r h).isClosedEmbedding (Projectivization.map_injective _ _)).isEmbedding

theorem nestedSubspaces : Expected.nestedSubspaces :=
  fun m r h => ⟨inclusion_embedding m r h, inclusion_range m r h⟩

lemma strata_disjoint (m : ℕ) {r s : ℕ} (hrs : r ≠ s) :
    Disjoint (stratum m r) (stratum m s) := by
  apply Set.disjoint_left.mpr
  intro p hpr hps
  rcases lt_or_gt_of_ne hrs with h | h
  · exact hps.2 (lowerSpace_mono m (by omega) hpr.1)
  · exact hpr.2 (lowerSpace_mono m (by omega) hps.1)

lemma strata_cover (m : ℕ) : ⋃ r : Fin (m+1), stratum m r.val = univ := by
  classical
  apply Set.eq_univ_of_forall
  intro p
  have hex : ∃ k, p ∈ lowerSpace m (k+1) := ⟨m, by rw [lowerSpace_top]; trivial⟩
  let r := Nat.find hex
  have hr : p ∈ lowerSpace m (r+1) := Nat.find_spec hex
  have hrm : r ≤ m := Nat.find_min' hex (by rw [lowerSpace_top]; trivial)
  refine mem_iUnion.mpr ⟨⟨r, by omega⟩, hr, ?_⟩
  intro hp
  by_cases hr0 : r = 0
  · simpa [hr0, lowerSpace_zero] using hp
  · have hr' : r-1 < r := by omega
    have hp' : p ∈ lowerSpace m ((r-1)+1) := by simpa [Nat.sub_add_cancel (by omega : 1 ≤ r)] using hp
    exact Nat.find_min hex hr' hp'

end P202.ComplexProjective

namespace P202.ComplexProjective

lemma complexDimension (r : ℕ) : Module.finrank ℝ (EuclideanSpace ℂ (Fin r)) = 2*r := by
  have h := Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin r))
  simpa using h.symm

def realComplexIsometry (r : ℕ) :
    EuclideanSpace ℝ (Fin (2*r)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin r) := by
  rw [← complexDimension r]
  exact (stdOrthonormalBasis ℝ (EuclideanSpace ℂ (Fin r))).repr.symm

end P202.ComplexProjective

namespace P202.ComplexProjective

lemma disk_norm_le (r : ℕ) (z : ComplexDisk r) : ‖z.val‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using z.property

lemma disk_height_sq (r : ℕ) (z : ComplexDisk r) :
    (Real.sqrt (1-‖z.val‖^2))^2 = 1-‖z.val‖^2 := by
  apply Real.sq_sqrt
  have := disk_norm_le r z
  have := norm_nonneg z.val
  nlinarith

lemma characteristic_mem_stratum (m r : ℕ) (h : r ≤ m) (z : ComplexDisk r) :
    characteristic m r h z ∈ stratum m r ↔ ‖z.val‖ < 1 := by
  rw [characteristic, stratum_mk h]
  have hs : ∀ i : Fin (m+1), r+1 ≤ i.val → diskVector m r z i = 0 := by
    intro i hi
    simp [diskVector, coordinateVector, show ¬ i.val < r by omega, show i.val ≠ r by omega]
  have heval : diskVector m r z ⟨r, by omega⟩ =
      ((Real.sqrt (1-‖z.val‖^2) : ℝ) : ℂ) := by simp [diskVector, coordinateVector]
  rw [heval, Complex.ofReal_ne_zero]
  constructor
  · intro hn
    have := disk_norm_le r z
    apply lt_of_le_of_ne this
    intro he
    exact hn.2 (by simp [he])
  · intro hz
    refine ⟨hs, ?_⟩
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    have := norm_nonneg z.val
    nlinarith

lemma characteristic_injective_interior (m r : ℕ) (h : r ≤ m)
    (z w : ComplexDisk r) (hz : ‖z.val‖ < 1) (hw : ‖w.val‖ < 1)
    (he : characteristic m r h z = characteristic m r h w) : z = w := by
  obtain ⟨a, ha⟩ := (mk_eq_mk' _ _ _ _).mp he
  let t := Real.sqrt (1-‖z.val‖^2)
  let u := Real.sqrt (1-‖w.val‖^2)
  have ht : 0 < t := Real.sqrt_pos.mpr (by have := norm_nonneg z.val; nlinarith)
  have hu : 0 < u := Real.sqrt_pos.mpr (by have := norm_nonneg w.val; nlinarith)
  have haLast : a * (u : ℂ) = (t : ℂ) := by
    have hh := congrFun ha ⟨r, by omega⟩
    simpa [diskVector, coordinateVector, t, u] using hh
  have haFirst : z.val = a • w.val := by
    ext i
    have hh := congrFun ha ⟨i.val, by omega⟩
    simpa [diskVector, coordinateVector, i.isLt] using hh.symm
  have hnorm : ‖z.val‖ = ‖a‖ * ‖w.val‖ := by rw [haFirst, norm_smul]
  have hheight : ‖a‖ * u = t := by
    have hh := congrArg norm haLast
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hu] using hh
  have hnorm2 : ‖z.val‖^2 = ‖a‖^2 * ‖w.val‖^2 := by rw [hnorm, mul_pow]
  have hheight2 : ‖a‖^2 * u^2 = t^2 := by rw [← mul_pow, hheight]
  have ht2 : t^2 = 1-‖z.val‖^2 := disk_height_sq r z
  have hu2 : u^2 = 1-‖w.val‖^2 := disk_height_sq r w
  have haNorm : ‖a‖ = 1 := by
    have hsq : ‖a‖^2 = 1 := by nlinarith
    have := norm_nonneg a
    nlinarith
  have htu : t = u := by simpa [haNorm] using hheight.symm
  have ha1 : a = 1 := by
    apply mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hu.ne')
    simpa [htu] using haLast
  apply Subtype.ext
  simpa [ha1] using haFirst

/-- Explicit point of the open unit ball over any affine coordinates. -/
lemma affineChart_in_characteristic_interior (m r : ℕ) (h : r ≤ m) (v : Fin r → ℂ) :
    ∃ z : ComplexDisk r, ‖z.val‖ < 1 ∧ characteristic m r h z = affineChart m r h v := by
  let x : EuclideanSpace ℂ (Fin r) := WithLp.toLp 2 v
  let d : ℝ := Real.sqrt (1+‖x‖^2)
  have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d^2 = 1+‖x‖^2 := Real.sq_sqrt (by positivity)
  have hxd : ‖x‖ < d := by have := norm_nonneg x; nlinarith
  have hnorm : ‖d⁻¹ • x‖ = ‖x‖ / d := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hd, div_eq_mul_inv, mul_comm]
  have hzlt : ‖d⁻¹ • x‖ < 1 := by rw [hnorm]; exact (div_lt_one hd).mpr hxd
  let z : ComplexDisk r := ⟨d⁻¹ • x, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hzlt.le⟩
  have hzsq : 1-‖z.val‖^2 = (d⁻¹)^2 := by
    change 1-‖d⁻¹ • x‖^2 = (d⁻¹)^2
    rw [hnorm]
    field_simp
    nlinarith
  have hheight : Real.sqrt (1-‖z.val‖^2) = d⁻¹ := by
    rw [hzsq, Real.sqrt_sq (inv_nonneg.mpr hd.le)]
  refine ⟨z, hzlt, (mk_eq_mk' _ _ _ _).mpr ⟨((d⁻¹ : ℝ) : ℂ), ?_⟩⟩
  ext i
  dsimp [diskVector, coordinateVector]
  split
  · simp [z, x, Complex.real_smul]
  · split
    · simp [hheight]
    · simp

abbrev OpenComplexDisk (r : ℕ) := Metric.ball (0 : EuclideanSpace ℂ (Fin r)) 1

def complexInteriorInclusion (r : ℕ) : OpenComplexDisk r → ComplexDisk r :=
  fun z => ⟨z.val, Metric.ball_subset_closedBall z.property⟩

def interiorCharacteristic (m r : ℕ) (h : r ≤ m) : OpenComplexDisk r → Space m :=
  characteristic m r h ∘ complexInteriorInclusion r

lemma interiorCharacteristic_continuous (m r : ℕ) (h : r ≤ m) :
    Continuous (interiorCharacteristic m r h) :=
  (characteristic_continuous m r h).comp (continuous_subtype_val.subtype_mk _)

lemma interiorCharacteristic_range (m r : ℕ) (h : r ≤ m) :
    range (interiorCharacteristic m r h) = stratum m r := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    apply (characteristic_mem_stratum m r h _).mpr
    simpa only [complexInteriorInclusion, Metric.mem_ball, dist_zero_right] using z.property
  · intro hp
    obtain ⟨v, rfl⟩ := (affineChart_range m r h).symm ▸ hp
    obtain ⟨z, hz, he⟩ := affineChart_in_characteristic_interior m r h v
    exact ⟨⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩, he⟩

lemma interiorCharacteristic_embedding (m r : ℕ) (h : r ≤ m) :
    IsEmbedding (interiorCharacteristic m r h) := by
  let s := stratum m r
  let f := characteristic m r h
  let e : OpenComplexDisk r ≃ₜ (f ⁻¹' s) := {
    toFun := fun z => ⟨complexInteriorInclusion r z,
      (characteristic_mem_stratum m r h _).mpr (by
        simpa only [complexInteriorInclusion, Metric.mem_ball, dist_zero_right] using z.property)⟩
    invFun := fun z => ⟨z.val.val, by
      simpa only [Function.comp_apply, Metric.mem_ball, dist_zero_right] using
        (characteristic_mem_stratum m r h _).mp z.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun z => by simpa only [Function.comp_apply, Metric.mem_ball, dist_zero_right] using
        (characteristic_mem_stratum m r h _).mp z.property) }
  have hf : Continuous (s.restrictPreimage f) :=
    ((characteristic_continuous m r h).comp continuous_subtype_val).subtype_mk _
  have hclosed : IsClosedMap (s.restrictPreimage f) :=
    (characteristic_continuous m r h).isClosedMap.restrictPreimage s
  have hinj : Function.Injective (s.restrictPreimage f) := by
    intro z w he
    apply Subtype.ext
    apply characteristic_injective_interior m r h _ _
      ((characteristic_mem_stratum m r h _).mp z.property)
      ((characteristic_mem_stratum m r h _).mp w.property)
    exact congrArg Subtype.val he
  exact IsEmbedding.subtypeVal.comp
    ((IsClosedEmbedding.of_continuous_injective_isClosedMap hf hinj hclosed).isEmbedding.comp e.isEmbedding)

end P202.ComplexProjective

namespace P202.ComplexProjective
open P202.Cellular

lemma lowerSpace_partition (m k : ℕ) :
    lowerSpace m k = ⋃ r : Fin (m+1), ⋃ (_ : r.val < k), stratum m r.val := by
  ext p
  constructor
  · intro hp
    have hp' : p ∈ ⋃ r : Fin (m+1), stratum m r.val := by rw [strata_cover]; trivial
    obtain ⟨r, hr⟩ := mem_iUnion.mp hp'
    have hrk : r.val < k := by
      by_contra hn
      exact hr.2 (lowerSpace_mono m (by omega) hp)
    exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hrk, hr⟩⟩
  · intro hp
    obtain ⟨r, hp⟩ := mem_iUnion.mp hp
    obtain ⟨hr, hp⟩ := mem_iUnion.mp hp
    exact lowerSpace_mono m (by omega) hp.1

def realDiskHomeomorph (r : ℕ) : Disk (2*r) ≃ₜ ComplexDisk r where
  toFun z := ⟨realComplexIsometry r z.val, by
    simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using z.property⟩
  invFun z := ⟨(realComplexIsometry r).symm z.val, by
    simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using z.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := ((realComplexIsometry r).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((realComplexIsometry r).symm.continuous.comp continuous_subtype_val).subtype_mk _

def realOpenDiskHomeomorph (r : ℕ) : OpenDisk (2*r) ≃ₜ OpenComplexDisk r where
  toFun z := ⟨realComplexIsometry r z.val, by
    simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using z.property⟩
  invFun z := ⟨(realComplexIsometry r).symm z.val, by
    simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using z.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := ((realComplexIsometry r).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((realComplexIsometry r).symm.continuous.comp continuous_subtype_val).subtype_mk _

def diskCharacteristic (m r : ℕ) (h : r ≤ m) : C(Disk (2*r), Space m) :=
  ⟨P202.ComplexProjective.characteristic m r h ∘ realDiskHomeomorph r,
    (characteristic_continuous m r h).comp (realDiskHomeomorph r).continuous⟩

def standardCharacteristic (m n : ℕ) (c : CellIndex m n) : C(Disk n, Space m) := by
  rcases c with ⟨⟨r, hr⟩, hn⟩
  dsimp at hn
  subst n
  exact diskCharacteristic m r (by omega)

@[instance_reducible] def standardCellStructure (m : ℕ) : CellStructure (Space m) where
  Cell := CellIndex m
  characteristic := standardCharacteristic m

lemma standard_interior_embedding (m : ℕ) (n : ℕ) (c : CellIndex m n) :
    @IsEmbedding (OpenDisk n) (Space m) _ _
      (@interiorMap (Space m) _ (standardCellStructure m) n c) := by
  rcases c with ⟨⟨r, hr⟩, hn⟩
  dsimp at hn
  subst n
  change IsEmbedding (interiorCharacteristic m r (by omega) ∘ realOpenDiskHomeomorph r)
  exact (interiorCharacteristic_embedding m r (by omega)).comp
    (realOpenDiskHomeomorph r).isEmbedding

lemma standard_openCell (m : ℕ) (n : ℕ) (c : CellIndex m n) :
    @openCell (Space m) _ (standardCellStructure m) n c = stratum m c.val.val := by
  rcases c with ⟨⟨r, hr⟩, hn⟩
  dsimp at hn
  subst n
  change range (interiorCharacteristic m r (by omega) ∘ realOpenDiskHomeomorph r) = stratum m r
  rw [Set.range_comp, (realOpenDiskHomeomorph r).surjective.range_eq, Set.image_univ,
    interiorCharacteristic_range]

def totalCellEquiv (m : ℕ) : (Σ n, CellIndex m n) ≃ Fin (m+1) where
  toFun c := c.2.val
  invFun r := ⟨2*r.val, ⟨r, rfl⟩⟩
  left_inv c := by
    rcases c with ⟨n, ⟨⟨r, hr⟩, hn⟩⟩
    dsimp at hn
    subst n
    rfl
  right_inv _ := rfl

lemma standard_disjoint (m : ℕ) :
    (univ : Set (Σ n, CellIndex m n)).PairwiseDisjoint
      (fun c => @openCell (Space m) _ (standardCellStructure m) c.1 c.2) := by
  intro a _ b _ hab
  change Disjoint (@openCell (Space m) _ (standardCellStructure m) a.1 a.2)
    (@openCell (Space m) _ (standardCellStructure m) b.1 b.2)
  rw [standard_openCell, standard_openCell]
  apply strata_disjoint m
  intro he
  apply hab
  exact (totalCellEquiv m).injective (Fin.ext he)

lemma standard_cover (m : ℕ) :
    (⋃ n, ⋃ c : CellIndex m n, @openCell (Space m) _ (standardCellStructure m) n c) = univ := by
  apply Set.eq_univ_of_forall
  intro p
  have hp : p ∈ ⋃ r : Fin (m+1), stratum m r.val := by rw [strata_cover]; trivial
  obtain ⟨r, hr⟩ := mem_iUnion.mp hp
  refine mem_iUnion.mpr ⟨2*r.val, mem_iUnion.mpr ⟨⟨r, rfl⟩, ?_⟩⟩
  rwa [standard_openCell]

lemma lowerSpace_subset_skeleton (m r : ℕ) :
    lowerSpace m r ⊆ @skeletonLT (Space m) _ (standardCellStructure m) (2*r) := by
  intro p hp
  rw [lowerSpace_partition] at hp
  obtain ⟨s, hp⟩ := mem_iUnion.mp hp
  obtain ⟨hs, hp⟩ := mem_iUnion.mp hp
  refine mem_iUnion.mpr ⟨2*s.val, mem_iUnion.mpr ⟨by omega, mem_iUnion.mpr ⟨⟨s, rfl⟩, ?_⟩⟩⟩
  rwa [standard_openCell]

lemma standard_boundary (m : ℕ) (n : ℕ) (c : CellIndex m n) :
    MapsTo (@boundaryMap (Space m) _ (standardCellStructure m) n c) univ
      (@skeletonLT (Space m) _ (standardCellStructure m) n) := by
  rcases c with ⟨⟨r, hr⟩, hn⟩
  dsimp at hn
  subst n
  intro z _
  apply lowerSpace_subset_skeleton m r
  apply characteristic_boundary m r (by omega)
  change ‖realComplexIsometry r z.val‖ = 1
  rw [LinearIsometryEquiv.norm_map]
  simpa only [Metric.mem_sphere, dist_zero_right] using z.property

lemma standard_closure_finite (m : ℕ) (n : ℕ) (c : CellIndex m n) :
    ∃ F : Finset (Σ k, CellIndex m k),
    @closedCell (Space m) _ (standardCellStructure m) n c ⊆
      ⋃ d ∈ F, @openCell (Space m) _ (standardCellStructure m) d.1 d.2 := by
  classical
  letI := Fintype.ofEquiv (Fin (m+1)) (totalCellEquiv m).symm
  refine ⟨Finset.univ, ?_⟩
  intro p _
  have hp : p ∈ ⋃ n, ⋃ c : CellIndex m n,
      @openCell (Space m) _ (standardCellStructure m) n c := by rw [standard_cover]; trivial
  obtain ⟨n, hp⟩ := Set.mem_iUnion.mp hp
  obtain ⟨c, hp⟩ := Set.mem_iUnion.mp hp
  exact mem_iUnion.mpr ⟨⟨n,c⟩, mem_iUnion.mpr ⟨Finset.mem_univ _, hp⟩⟩

lemma standard_weak_topology (m : ℕ) (A : Set (Space m)) :
    IsClosed A ↔ ∀ n (c : CellIndex m n), IsClosed (standardCharacteristic m n c ⁻¹' A) := by
  classical
  constructor
  · intro hA n c
    exact hA.preimage (standardCharacteristic m n c).continuous
  · intro hA
    letI := Fintype.ofEquiv (Fin (m+1)) (totalCellEquiv m).symm
    have he : A = ⋃ c : (Σ n, CellIndex m n),
        standardCharacteristic m c.1 c.2 '' (standardCharacteristic m c.1 c.2 ⁻¹' A) := by
      ext p
      constructor
      · intro hp
        have hcov : p ∈ ⋃ n, ⋃ c : CellIndex m n,
            @openCell (Space m) _ (standardCellStructure m) n c := by rw [standard_cover]; trivial
        obtain ⟨n, hcov⟩ := mem_iUnion.mp hcov
        obtain ⟨c, z, hz⟩ := mem_iUnion.mp hcov
        refine mem_iUnion.mpr ⟨⟨n,c⟩, interiorInclusion n z, ?_, hz⟩
        change standardCharacteristic m n c (interiorInclusion n z) = p at hz
        change standardCharacteristic m n c (interiorInclusion n z) ∈ A
        rwa [hz]
      · intro hp
        obtain ⟨c, z, hz, rfl⟩ := mem_iUnion.mp hp
        exact hz
    rw [he]
    apply isClosed_iUnion_of_finite
    intro c
    exact ((hA c.1 c.2).isCompact.image (standardCharacteristic m c.1 c.2).continuous).isClosed

end P202.ComplexProjective

namespace P202.ComplexProjective
open P202.Cellular

lemma standardCW (m : ℕ) :
    ∃ C : CWStructure (Space m), C.toCellStructure = standardCellStructure m := by
  letI := standardCellStructure m
  exact P202.Topology.weakCWConstructor
    (standard_interior_embedding m) (standard_disjoint m) (standard_cover m)
    (standard_boundary m) (standard_closure_finite m) (standard_weak_topology m)

theorem cellStructure : Expected.cellStructure := by
  intro m
  obtain ⟨C, hC⟩ := standardCW m
  rcases C with @⟨S, hT, hI, hD, hCov, hB, hCF, hW, hQ⟩
  change S = standardCellStructure m at hC
  subst S
  refine ⟨@CWStructure.mk (Space m) _ (standardCellStructure m) hT hI hD hCov hB hCF hW hQ,
    (fun _ => Equiv.refl _), ?_, ?_, ?_⟩
  · exact standard_openCell m
  · intro r h
    refine ⟨realComplexIsometry r, ?_⟩
    rintro ⟨⟨s, hs⟩, hc⟩ z
    have hsr : s = r := by dsimp at hc; omega
    subst s
    rfl
  · exact characteristic_boundary m

theorem homology : Expected.homology := homology_of_cellStructure cellStructure

end P202.ComplexProjective
