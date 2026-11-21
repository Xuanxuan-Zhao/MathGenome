import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SurfaceHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.CellularDegrees
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.LocalAtTarget
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-! Integral homology of the actual standard polygon surface quotients,
paper.tex 1612–1616 and 1653–1662. The quotient CW charts, common disk
orientations and attaching degrees are constructed explicitly; cellular
comparison and the integral Smith quotient give all required homology groups.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Topology
open P202.Cellular P202Specs.CellularChains P202Specs.SingularChains
open P202Specs.SurfaceHomology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped BigOperators
universe u v w

namespace P202.Homology.SurfaceHomology

lemma exponentSum_append {n : ℕ} (v z : Word n) (e : Fin n) :
    exponentSum (v ++ z) e = exponentSum v e + exponentSum z e := by
  simp [exponentSum, List.map_append, List.sum_append]

lemma exponentSum_flatMap {α : Type*} {n : ℕ} (l : List α)
    (f : α → Word n) (e : Fin n) :
    exponentSum (l.flatMap f) e = (l.map fun a => exponentSum (f a) e).sum := by
  induction l with
  | nil => simp [exponentSum]
  | cons a l ih => simp only [List.flatMap_cons, exponentSum_append,
      ih, List.map_cons, List.sum_cons]

lemma orientedExponent (g : ℕ) (e : Fin (2*g)) :
    exponentSum (orientedWord g) e = 0 := by
  classical
  rw [orientedWord, exponentSum_flatMap]
  apply List.sum_eq_zero
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  simp only [exponentSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  split_ifs <;> norm_num at *

lemma nonorientableExponent (k : ℕ) (e : Fin k) :
    exponentSum (nonorientableWord k) e = 2 := by
  classical
  rw [nonorientableWord, exponentSum_flatMap]
  simp only [exponentSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    ite_true, add_zero]
  rw [← List.sum_toFinset _ (List.nodup_finRange _)]
  simp [Finset.sum_add_distrib]

/-- Subtract the first coordinate from every remaining coordinate, and keep
the first coordinate modulo two. This is the explicit Smith quotient map. -/
def smithProjection (k : ℕ) :
    (Fin (k+1) → ℤ) →ₗ[ℤ] ((Fin k → ℤ) × ZMod 2) :=
  ({ toFun := fun v => (fun i => v i.succ - v 0, (v 0 : ZMod 2))
     map_zero' := by
       apply Prod.ext
       · ext i; rfl
       · rfl
     map_add' := by
       intro v z
       apply Prod.ext
       · ext i
         change (v i.succ + z i.succ) - (v 0 + z 0) =
           (v i.succ - v 0) + (z i.succ - z 0)
         omega
       · simp } : (Fin (k+1) → ℤ) →+ ((Fin k → ℤ) × ZMod 2)).toIntLinearMap

@[simp] lemma smithProjection_apply (k : ℕ) (v : Fin (k+1) → ℤ) :
    smithProjection k v = (fun i => v i.succ - v 0, (v 0 : ZMod 2)) := rfl

lemma smithProjection_surjective (k : ℕ) : Function.Surjective (smithProjection k) := by
  rintro ⟨v, t⟩
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective t
  refine ⟨Fin.cons z (fun i => v i + z), ?_⟩
  apply Prod.ext
  · ext i
    simp
  · simp

lemma smithProjection_ker (k : ℕ) :
    LinearMap.ker (smithProjection k) = LinearMap.range (twiceDiagonal (k+1)) := by
  ext v
  change smithProjection k v = 0 ↔ ∃ z, twiceDiagonal (k+1) z = v
  constructor
  · intro h
    have ht : ∀ i : Fin k, v i.succ - v 0 = 0 := by
      intro i
      exact congrArg (fun x => x.1 i) h
    have hm : (v 0 : ZMod 2) = 0 := congrArg Prod.snd h
    obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (v 0) 2).mp hm
    refine ⟨z, ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hz.symm
    · change 2*z = v j.succ
      have hh := ht j
      omega
  · rintro ⟨z, rfl⟩
    apply Prod.ext
    · ext i
      simp [twiceDiagonal]
    · change ((2*z : ℤ) : ZMod 2) = 0
      simp only [Int.cast_mul, Int.cast_ofNat]
      rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

/-- The actual quotient of the integral free module by the column
2(1,...,1), including the one-edge case. -/
def nonorientableQuotientEquiv (k : ℕ) :
    ((Fin (k+1) → ℤ) ⧸ LinearMap.range (twiceDiagonal (k+1))) ≃ₗ[ℤ]
      ((Fin k → ℤ) × ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ (smithProjection_ker k).symm).trans
    ((smithProjection k).quotKerEquivOfSurjective (smithProjection_surjective k))

lemma twiceDiagonal_injective (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (twiceDiagonal k) := by
  intro a b h
  have hh := congrFun h (⟨0, by omega⟩ : Fin k)
  change 2*a = 2*b at hh
  omega

/-- A quotient map of actual topological spaces, directly from its definition. -/
lemma polygonProjection_quotient {n : ℕ} (word : Word n) :
    IsQuotientMap (polygonProjection word) := isQuotientMap_quotient_mk'

lemma polygonSides_identified {n : ℕ} (word : Word n)
    (i j : Fin word.length) (h : (word.get i).1 = (word.get j).1)
    (t : unitInterval) :
    polygonProjection word
        (sidePoint word.length i.val (if (word.get i).2 then t.val else 1-t.val)) =
      polygonProjection word
        (sidePoint word.length j.val (if (word.get j).2 then t.val else 1-t.val)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr ⟨i, j, t, h, rfl, rfl⟩))

/-- In an empty-word polygon, precisely the intended boundary identifications
are imposed; no assertion about its homology is smuggled into its definition. -/
lemma emptyWord_boundary_collapsed {n : ℕ} (x y : ClosedDisk)
    (hx : ‖x.val‖ = 1) (hy : ‖y.val‖ = 1) :
    polygonProjection ([] : Word n) x = polygonProjection ([] : Word n) y :=
  Quotient.sound (Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, hx, hy⟩))


/-- Every generating identification takes place on the boundary. -/
lemma sideRelation_boundary {n : ℕ} (word : Word n) {x y : ClosedDisk}
    (h : sideRelation word x y) : ‖x.val‖ = 1 ∧ ‖y.val‖ = 1 := by
  rcases h with ⟨_, hx, hy⟩ | ⟨i, j, t, _, rfl, rfl⟩
  · exact ⟨hx, hy⟩
  · exact ⟨Circle.norm_coe _, Circle.norm_coe _⟩

/-- Taking the equivalence closure cannot identify an interior point with
another point. This checks the actual generated relation of the model. -/
lemma polygonRelation_eq_or_boundary {n : ℕ} (word : Word n) {x y : ClosedDisk}
    (h : (polygonSetoid word).r x y) : x = y ∨ (‖x.val‖ = 1 ∧ ‖y.val‖ = 1) := by
  induction h with
  | rel x y h => exact Or.inr (sideRelation_boundary word h)
  | refl x => exact Or.inl rfl
  | symm x y h ih => exact ih.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  | trans x y z _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | ⟨hx, hy⟩
    · exact ih₂
    · rcases ih₂ with rfl | ⟨_, hz⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩

lemma polygonProjection_eq_of_interior {n : ℕ} (word : Word n) {x y : ClosedDisk}
    (hx : ‖x.val‖ < 1) (h : polygonProjection word x = polygonProjection word y) : x = y := by
  rcases polygonRelation_eq_or_boundary word (Quotient.exact h) with hxy | ⟨hh, _⟩
  · exact hxy
  · exact (ne_of_lt hx hh).elim

/-- The disk interior with its genuine subspace topology. -/
abbrev InteriorDisk := {x : ClosedDisk // ‖x.val‖ < 1}

def polygonInteriorProjection {n : ℕ} (word : Word n) : C(InteriorDisk, PolygonSurface word) :=
  (polygonProjection word).comp ⟨Subtype.val, continuous_subtype_val⟩

lemma polygonInteriorProjection_openEmbedding {n : ℕ} (word : Word n) :
    IsOpenEmbedding (polygonInteriorProjection word) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (polygonInteriorProjection word).continuous
  · intro x y h
    apply Subtype.ext
    exact polygonProjection_eq_of_interior word x.property h
  · intro U hU
    have hI : IsOpen {x : ClosedDisk | ‖x.val‖ < 1} :=
      isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
    have hV : IsOpen (Subtype.val '' U : Set ClosedDisk) :=
      hI.isOpenEmbedding_subtypeVal.isOpenMap U hU
    have heq : polygonProjection word ⁻¹' (polygonInteriorProjection word '' U) =
        (Subtype.val '' U : Set ClosedDisk) := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        exact ⟨y, hy, polygonProjection_eq_of_interior word y.property hxy⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    exact (polygonProjection_quotient word).isOpen_preimage.mp (heq ▸ hV)

instance closedDiskPathConnected : PathConnectedSpace ClosedDisk :=
  isPathConnected_iff_pathConnectedSpace.mp (Metric.isPathConnected_closedBall (by norm_num))

instance polygonPathConnected {n : ℕ} (word : Word n) :
    PathConnectedSpace (PolygonSurface word) :=
  inferInstanceAs (PathConnectedSpace (Quotient (polygonSetoid word)))

/-- This proves the actual H₀ of the quotient, independently of its CW charts. -/
def polygonDegreeZeroEquiv {n : ℕ} (word : Word n) :
    homology ℤ ℤ (TopCat.of (PolygonSurface word)) 0 ≃ₗ[ℤ] ℤ :=
  (Classical.choice (P202.SingularDegreeZero.degreeZero ℤ ℤ
    (TopCat.of (PolygonSurface word)))).trans
      (Finsupp.uniqueLinearEquiv ℤ ℤ
        (ZerothHomotopy.mk (polygonProjection word ⟨0, by norm_num⟩)))

section CellularCalculation

variable (X : Type) [TopologicalSpace X] [CWStructure X]

lemma chainGroup_isZero_of_no_cells (j : ℕ) [IsEmpty (Cell X j)] :
    IsZero (chainGroup X ℤ ℤ j) := by
  obtain ⟨e⟩ := P202.Homology.cellularCellGroups X ℤ ℤ j
  letI : Subsingleton (chainGroup X ℤ ℤ j) := e.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- Dimensional vanishing uses the actual cellular-to-singular comparison. -/
lemma singularHomology_above_two
    (hc : ∀ n, 2 < n → IsEmpty (Cell X n)) (j : ℕ) (hj : 2 < j) :
    IsZero (homology ℤ ℤ (TopCat.of X) (j : ℤ)) := by
  letI : IsEmpty (Cell X j) := hc j hj
  have hz : IsZero ((cellularComplex X ℤ ℤ).X j) :=
    chainGroup_isZero_of_no_cells X j
  have hh : IsZero ((cellularComplex X ℤ ℤ).homology j) :=
    (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology
  exact (CellularComparison.comparisonIso X ℤ ℤ j).isZero_iff.mp hh

lemma differential_zero_of_coordinates {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℤ V]
    (c : chainGroup X ℤ ℤ n ≃ₗ[ℤ] V)
    (h : ∀ z, c (differential X ℤ ℤ n z) = 0) :
    differential X ℤ ℤ n = 0 := by
  ext z
  exact c.injective ((h z).trans c.map_zero.symm)

/-- A general zero-differential calculation, keeping categorical homology. -/
def homologyIsoOfZero (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (hin : K.d (n+1) n = 0) (hout : K.d n (n-1) = 0) :
    K.homology n ≅ K.X n :=
  K.homologyIsoSc' (n+1) n (n-1) (ChainComplex.prev ℕ n)
    (by cases n <;> simp) ≪≫
      (ShortComplex.LeftHomologyData.ofZeros (K.sc' (n+1) n (n-1)) hin hout).homologyIso

/-- Once both positive differentials of a two-dimensional CW complex vanish,
its integral singular homology is its cellular chain group in degrees 0,1,2.
This is a criterion, not an assumption about the polygon quotients. -/
lemma orientedCalculation
    (hc : ∀ n, 2 < n → IsEmpty (Cell X n))
    (h₁ : differential X ℤ ℤ 0 = 0) (h₂ : differential X ℤ ℤ 1 = 0) :
    Nonempty (homology ℤ ℤ (TopCat.of X) 0 ≃ₗ[ℤ] chainGroup X ℤ ℤ 0) ∧
    Nonempty (homology ℤ ℤ (TopCat.of X) 1 ≃ₗ[ℤ] chainGroup X ℤ ℤ 1) ∧
    Nonempty (homology ℤ ℤ (TopCat.of X) 2 ≃ₗ[ℤ] chainGroup X ℤ ℤ 2) := by
  have h₃ : (cellularComplex X ℤ ℤ).d 3 2 = 0 := by
    letI : IsEmpty (Cell X 3) := hc 3 (by omega)
    exact (chainGroup_isZero_of_no_cells X 3).eq_zero_of_src _
  have hd₁ : (cellularComplex X ℤ ℤ).d 1 0 = 0 := by
    exact (ChainComplex.of_d (chainGroup X ℤ ℤ) (differential X ℤ ℤ) 0).trans h₁
  have hd₂ : (cellularComplex X ℤ ℤ).d 2 1 = 0 := by
    exact (ChainComplex.of_d (chainGroup X ℤ ℤ) (differential X ℤ ℤ) 1).trans h₂
  have hd₀ : (cellularComplex X ℤ ℤ).d 0 (0-1) = 0 :=
    (cellularComplex X ℤ ℤ).shape _ _ (by simp)
  exact ⟨⟨((CellularComparison.comparisonIso X ℤ ℤ 0).symm ≪≫
        homologyIsoOfZero (cellularComplex X ℤ ℤ) 0 hd₁ hd₀).toLinearEquiv⟩,
    ⟨((CellularComparison.comparisonIso X ℤ ℤ 1).symm ≪≫
        homologyIsoOfZero (cellularComplex X ℤ ℤ) 1 hd₂ hd₁).toLinearEquiv⟩,
    ⟨((CellularComparison.comparisonIso X ℤ ℤ 2).symm ≪≫
        homologyIsoOfZero (cellularComplex X ℤ ℤ) 2 h₃ hd₂).toLinearEquiv⟩⟩

end CellularCalculation


/-- The middle three-term complex in the nonorientable calculation. -/
def nonorientableMiddle (k : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ModuleCat.shortComplexOfCompEqZero (twiceDiagonal k)
    (0 : (Fin k → ℤ) →ₗ[ℤ] ℤ) (by simp)

/-- Categorical homology of the computed middle differential. -/
def nonorientableMiddleHomology (k : ℕ) :
    (nonorientableMiddle (k+1)).homology ≃ₗ[ℤ] ((Fin k → ℤ) × ZMod 2) :=
  (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
    (nonorientableMiddle (k+1)) rfl
    (ModuleCat.cokernelCocone (nonorientableMiddle (k+1)).f)
    (ModuleCat.cokernelIsColimit (nonorientableMiddle (k+1)).f)).homologyIso.toLinearEquiv |>.trans
      (nonorientableQuotientEquiv k)

/-- The nonorientable homology calculation for an arbitrary two-dimensional
CW complex with explicitly supplied coordinates for its actual differential. -/
lemma nonorientableCalculation (X : Type) [TopologicalSpace X] [CWStructure X]
    (k : ℕ) (hk : 1 ≤ k)
    (hc : ∀ n, 2 < n → IsEmpty (Cell X n))
    (c₀ : chainGroup X ℤ ℤ 0 ≃ₗ[ℤ] ℤ)
    (c₁ : chainGroup X ℤ ℤ 1 ≃ₗ[ℤ] (Fin k → ℤ))
    (c₂ : chainGroup X ℤ ℤ 2 ≃ₗ[ℤ] ℤ)
    (h₁ : ∀ z, c₀ (differential X ℤ ℤ 0 z) = 0)
    (h₂ : ∀ z i, c₁ (differential X ℤ ℤ 1 z) i = 2*c₂ z) :
    Nonempty (homology ℤ ℤ (TopCat.of X) 0 ≃ₗ[ℤ] ℤ) ∧
    Nonempty (homology ℤ ℤ (TopCat.of X) 1 ≃ₗ[ℤ] ((Fin (k-1) → ℤ) × ZMod 2)) ∧
    IsZero (homology ℤ ℤ (TopCat.of X) 2) := by
  let K := cellularComplex X ℤ ℤ
  have hd₁ : K.d 1 0 = 0 := by
    exact (ChainComplex.of_d (chainGroup X ℤ ℤ) (differential X ℤ ℤ) 0).trans
      (differential_zero_of_coordinates X c₀ h₁)
  have hd₀ : K.d 0 (0-1) = 0 := K.shape _ _ (by simp)
  have hH₀ : Nonempty (homology ℤ ℤ (TopCat.of X) 0 ≃ₗ[ℤ] ℤ) :=
    ⟨(((CellularComparison.comparisonIso X ℤ ℤ 0).symm ≪≫
      homologyIsoOfZero K 0 hd₁ hd₀).toLinearEquiv).trans c₀⟩
  have h₃ : K.d 3 2 = 0 := by
    letI : IsEmpty (Cell X 3) := hc 3 (by omega)
    exact (chainGroup_isZero_of_no_cells X 3).eq_zero_of_src _
  have hinj : Function.Injective (differential X ℤ ℤ 1) := by
    intro a b hab
    apply c₂.injective
    apply twiceDiagonal_injective k hk
    ext i
    exact (h₂ a i).symm.trans ((congrArg (fun v => c₁ v i) hab).trans (h₂ b i))
  have hgmono : Mono (K.sc' 3 2 1).g := by
    change Mono (K.d 2 1)
    rw [show K.d 2 1 = differential X ℤ ℤ 1 from
      ChainComplex.of_d (chainGroup X ℤ ℤ) (differential X ℤ ℤ) 1]
    exact (ModuleCat.mono_iff_injective _).mpr hinj
  have hz : IsZero (K.sc' 3 2 1).homology :=
    ((K.sc' 3 2 1).exact_iff_isZero_homology).mp
      (((K.sc' 3 2 1).exact_iff_mono h₃).mpr hgmono)
  have hH₂ : IsZero (homology ℤ ℤ (TopCat.of X) 2) :=
    ((CellularComparison.comparisonIso X ℤ ℤ 2).symm ≪≫
      K.homologyIsoSc' 3 2 1 (ChainComplex.prev ℕ 2) (ChainComplex.next_nat_succ 1)).isZero_iff.mpr hz
  refine ⟨hH₀, ?_, hH₂⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let e : K.sc' 2 1 0 ≅ nonorientableMiddle (m+1) :=
    ShortComplex.isoMk c₂.toModuleIso c₁.toModuleIso c₀.toModuleIso
      (by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change (fun _ : Fin (m+1) => 2*c₂ z) = c₁ (differential X ℤ ℤ 1 z)
        funext i
        exact (h₂ z i).symm)
      (by
        ext z
        change 0 = c₀ (differential X ℤ ℤ 0 z)
        exact (h₁ z).symm)
  exact ⟨(((CellularComparison.comparisonIso X ℤ ℤ 1).symm ≪≫
    K.homologyIsoSc' 2 1 0 (ChainComplex.prev ℕ 1) (ChainComplex.next_nat_succ 0) ≪≫
      ShortComplex.homologyMapIso e).toLinearEquiv).trans (nonorientableMiddleHomology m)⟩

/-- This implication isolates the remaining geometric obligation. It is not
a proof of `Expected.orientedHomology` without its explicit premise. -/
lemma orientedHomology_of_attachingDifferentials
    (h : Expected.attachingDifferentials) : Expected.orientedHomology := by
  intro g
  obtain ⟨C, hc, charts, c₀, c₁, c₂, g₀, g₁, g₂, _, _, _, hd₁, hd₂⟩ := h.1 g
  letI := C
  have h₂ : differential (OrientedSurface g) ℤ ℤ 1 = 0 :=
    differential_zero_of_coordinates _ c₁ (by
      intro z
      ext i
      simpa using hd₂ z i)
  obtain ⟨⟨e₀⟩, ⟨e₁⟩, ⟨e₂⟩⟩ := orientedCalculation (OrientedSurface g) hc.2.2.2
    (differential_zero_of_coordinates _ c₀ hd₁) h₂
  exact ⟨⟨e₀.trans c₀⟩, ⟨e₁.trans c₁⟩, ⟨e₂.trans c₂⟩,
    singularHomology_above_two _ hc.2.2.2⟩

lemma nonorientableHomology_of_attachingDifferentials
    (h : Expected.attachingDifferentials) : Expected.nonorientableHomology := by
  intro k hk
  obtain ⟨C, hc, charts, c₀, c₁, c₂, g₀, g₁, g₂, _, _, _, hd₁, hd₂⟩ := h.2 k hk
  letI := C
  obtain ⟨h₀, h₁, h₂⟩ := nonorientableCalculation (NonorientableSurface k) k hk
    hc.2.2.2 c₀ c₁ c₂ hd₁ hd₂
  exact ⟨h₀, h₁, h₂, singularHomology_above_two _ hc.2.2.2⟩

lemma polygonCellStructures_of_attachingDifferentials
    (h : Expected.attachingDifferentials) : Expected.polygonCellStructures := by
  constructor
  · intro g
    obtain ⟨C, hc, charts, _⟩ := h.1 g
    exact ⟨C, hc, ⟨charts⟩⟩
  · intro k hk
    obtain ⟨C, hc, charts, _⟩ := h.2 k hk
    exact ⟨C, hc, ⟨charts⟩⟩

/-- The exponent and Smith computations are closed results. -/
theorem wordCoefficients : Expected.wordCoefficients :=
  ⟨orientedExponent, nonorientableExponent⟩

theorem degreeZero : Expected.degreeZero :=
  fun _ word => ⟨polygonDegreeZeroEquiv word⟩

theorem nonorientableSmith : Expected.nonorientableSmith := by
  intro k hk
  refine ⟨twiceDiagonal_injective k hk, ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact ⟨nonorientableQuotientEquiv m⟩

/-- Coincident endpoint incidences make the first cellular differential zero.
This applies to every CW complex with at most one vertex and arbitrary
coefficient modules; it does not assume a matrix formula. -/
lemma differential_zero_of_subsingleton_vertices
    (X : Type w) [TopologicalSpace X] [CWStructure X]
    [Subsingleton (Cell X 0)]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    differential X R M 0 = 0 := by
  obtain ⟨h⟩ := CellularDegrees.intervalParametrization_nonempty
  obtain ⟨g, e₀, hz, _, _, hb⟩ := CellularDegrees.intervalCellBoundary X R M h
  obtain ⟨e₁, he₁⟩ := P202.Homology.cellularOrientedCoordinates X R M 1 g
  have hs : (differential X R M 0).hom.comp e₁.symm.toLinearMap = 0 := by
    apply Finsupp.lhom_ext
    intro c m
    change differential X R M 0 (e₁.symm (Finsupp.single c m)) = 0
    rw [CellularDegrees.coordinates_symm_single X R M 1 g e₁ he₁]
    apply e₀.injective
    obtain ⟨vf, vi, _, _, hb⟩ := hb c
    exact (hb m).trans (by rw [Subsingleton.elim vf vi, sub_self, e₀.map_zero])
  ext z
  change differential X R M 0 z = 0
  have ht := congrArg (fun f => f (e₁ z)) hs
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, LinearMap.zero_apply] using ht

/-- For a polygon with one vertex, it suffices to compute the boundary of
its oriented face generators. The endpoint differential follows from signed
incidence, and linearity supplies the formula for every two-chain. -/
lemma polygonDifferentials_of_cellColumns {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)]
    (hc : PolygonCellCounts (PolygonSurface word) e)
    (charts : PolygonCharts word) (coefficient : ℤ)
    (c₀ : chainGroup (PolygonSurface word) ℤ ℤ 0 ≃ₗ[ℤ] ℤ)
    (c₁ : chainGroup (PolygonSurface word) ℤ ℤ 1 ≃ₗ[ℤ] (Fin e → ℤ))
    (c₂ : chainGroup (PolygonSurface word) ℤ ℤ 2 ≃ₗ[ℤ] ℤ)
    (g₀ : ℤ ≃ₗ[ℤ] P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
      (referenceDiskPair.{0} 0) 0)
    (g₁ : ℤ ≃ₗ[ℤ] P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
      (referenceDiskPair.{0} 1) 1)
    (g₂ : ℤ ≃ₗ[ℤ] P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
      (referenceDiskPair.{0} 2) 2)
    (h₀ : ∀ z, c₀ (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 0
      charts.vertex (g₀ z)) = z)
    (h₁ : ∀ i z, c₁ (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 1
      (charts.edges i) (g₁ z)) = Pi.single i z)
    (h₂ : ∀ z, c₂ (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 2
      charts.face (g₂ z)) = z)
    (hb : ∀ z i, c₁ (differential (PolygonSurface word) ℤ ℤ 1
      (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 2
        charts.face (g₂ z))) i = coefficient * z) :
    PolygonDifferentials word charts coefficient := by
  letI : Subsingleton (Cell (PolygonSurface word) 0) :=
    (Classical.choice hc.1).injective.subsingleton
  refine ⟨c₀, c₁, c₂, g₀, g₁, g₂, h₀, h₁, h₂, ?_, ?_⟩
  · intro z
    rw [differential_zero_of_subsingleton_vertices]
    exact c₀.map_zero
  · intro z i
    have he : P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 2
        charts.face (g₂ (c₂ z)) = z := c₂.injective (h₂ (c₂ z))
    calc
      _ = c₁ (differential (PolygonSurface word) ℤ ℤ 1
          (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 2
            charts.face (g₂ (c₂ z)))) i := congrArg (fun a => c₁
              (differential (PolygonSurface word) ℤ ℤ 1 a) i) he.symm
      _ = coefficient * c₂ z := hb (c₂ z) i

/-- The real two-disk and the complex closed unit disk have the same
norm-preserving geometric parametrization. -/
def complexDiskHomeomorph : Disk 2 ≃ₜ ClosedDisk :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_closedBall, dist_zero_right]
    change ‖x‖ ≤ 1 ↔ ‖Complex.orthonormalBasisOneI.repr.symm x‖ ≤ 1
    rw [LinearIsometryEquiv.norm_map])

@[simp] lemma complexDiskHomeomorph_norm (x : Disk 2) :
    ‖(complexDiskHomeomorph x).val‖ = ‖x.val‖ :=
  Complex.orthonormalBasisOneI.repr.symm.norm_map x.val

/-- In the empty word, the equivalence closure is exactly boundary collapse. -/
lemma emptyWord_relation_iff {n : ℕ} (x y : ClosedDisk) :
    (polygonSetoid ([] : Word n)).r x y ↔
      x = y ∨ (‖x.val‖ = 1 ∧ ‖y.val‖ = 1) := by
  constructor
  · exact polygonRelation_eq_or_boundary []
  · rintro (rfl | ⟨hx, hy⟩)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, hx, hy⟩)

lemma complexDisk_boundaryRelation (x y : Disk 2) :
    (P202Specs.GoodPairQuotient.collapseSetoid (P202Specs.SpheresDisks.diskPair 2)).r x y ↔
      (polygonSetoid ([] : Word 0)).r (complexDiskHomeomorph x) (complexDiskHomeomorph y) := by
  rw [emptyWord_relation_iff]
  change (x = y ∨ (‖x.val‖ = 1 ∧ ‖y.val‖ = 1)) ↔
    (complexDiskHomeomorph x = complexDiskHomeomorph y ∨
      (‖(complexDiskHomeomorph x).val‖ = 1 ∧ ‖(complexDiskHomeomorph y).val‖ = 1))
  rw [complexDiskHomeomorph_norm, complexDiskHomeomorph_norm]
  exact or_congr complexDiskHomeomorph.injective.eq_iff.symm Iff.rfl

/-- The genus-zero model is the genuine disk with its boundary collapsed. -/
def emptyWordDiskQuotientHomeomorph :
    P202Specs.GoodPairQuotient.quotientSpace (P202Specs.SpheresDisks.diskPair 2) ≃ₜ
      PolygonSurface ([] : Word 0) :=
  Homeomorph.Quotient.congr complexDiskHomeomorph complexDisk_boundaryRelation

/-- This identifies the actual genus-zero polygon with the geometric sphere. -/
def genusZeroSphereHomeomorph : OrientedSurface 0 ≃ₜ P202Specs.SpheresDisks.sphere 2 := by
  haveI : Nonempty (Fin 2) := ⟨0⟩
  let b : Sphere 2 := Classical.choice
    ((NormedSpace.sphere_nonempty.mpr zero_le_one :
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty).to_subtype)
  exact emptyWordDiskQuotientHomeomorph.symm.trans
    (CellularDegrees.Geometry.diskQuotientSphereHomeomorph 2 b)

/-- Positive ordinary homology of the genus-zero quotient is reduced sphere
homology, using the canonical comparison of the two singular complexes. -/
def genusZeroPositiveHomologyIso (j : ℕ) :
    homology ℤ ℤ (TopCat.of (OrientedSurface 0)) ((j+1 : ℕ) : ℤ) ≅
      reducedHomology ℤ ℤ (P202Specs.SpheresDisks.sphere 2) ((j+1 : ℕ) : ℤ) := by
  let Y := P202Specs.SpheresDisks.sphere 2
  letI := CellularDegrees.PositiveComparison.reducedToOrdinary_homology_isIso ℤ ℤ Y j
  exact (homologyFunctor ℤ ℤ ((j+1 : ℕ) : ℤ)).mapIso
      (TopCat.isoOfHomeo genusZeroSphereHomeomorph) ≪≫
    (asIso (homologyMap (CellularDegrees.PositiveComparison.reducedToOrdinary ℤ ℤ Y)
      ((j+1 : ℕ) : ℤ))).symm

/-- Complete positive-degree vanishing for the actual genus-zero polygon. -/
lemma genusZeroHomology_vanishing (j : ℕ) (hj : 0 < j) (h₂ : j ≠ 2) :
    IsZero (homology ℤ ℤ (TopCat.of (OrientedSurface 0)) (j : ℤ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact (genusZeroPositiveHomologyIso m).isZero_iff.mpr
    ((P202.SpheresDisks.sphereHomology ℤ ℤ 2 (m+1)).2 h₂)

/-- The top integral homology of the genuine genus-zero quotient. -/
def genusZeroTopHomologyEquiv :
    homology ℤ ℤ (TopCat.of (OrientedSurface 0)) 2 ≃ₗ[ℤ] ℤ :=
  (genusZeroPositiveHomologyIso 1).toLinearEquiv.trans
    (Classical.choice ((P202.SpheresDisks.sphereHomology ℤ ℤ 2 2).1 rfl))

/-- All homology groups required for the genus-zero member, including
its empty first free module and every degree above two. -/
lemma genusZeroHomology :
    Nonempty (homology ℤ ℤ (TopCat.of (OrientedSurface 0)) 0 ≃ₗ[ℤ] ℤ) ∧
    Nonempty (homology ℤ ℤ (TopCat.of (OrientedSurface 0)) 1 ≃ₗ[ℤ] (Fin (2*0) → ℤ)) ∧
    Nonempty (homology ℤ ℤ (TopCat.of (OrientedSurface 0)) 2 ≃ₗ[ℤ] ℤ) ∧
    ∀ j : ℕ, 2 < j → IsZero (homology ℤ ℤ (TopCat.of (OrientedSurface 0)) (j : ℤ)) := by
  letI : Subsingleton (homology ℤ ℤ (TopCat.of (OrientedSurface 0)) 1) :=
    ModuleCat.subsingleton_of_isZero (genusZeroHomology_vanishing 1 (by omega) (by omega))
  letI : Subsingleton (Fin (2*0) → ℤ) :=
    ⟨fun f g => funext fun i => Fin.elim0 i⟩
  refine ⟨⟨polygonDegreeZeroEquiv (orientedWord 0)⟩,
    ⟨LinearEquiv.ofSubsingleton _ _⟩, ⟨genusZeroTopHomologyEquiv⟩, ?_⟩
  intro j hj
  exact genusZeroHomology_vanishing j (by omega) (by omega)



open Set


lemma sidePoint_continuous (m i : ℕ) : Continuous (sidePoint m i) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop))

@[simp] lemma sidePoint_one (m i : ℕ) :
    sidePoint m i 1 = sidePoint m (i+1) 0 := by
  apply Subtype.ext
  simp [sidePoint, Nat.cast_add, Nat.cast_one]

@[simp] lemma sidePoint_cycle (m : ℕ) (hm : 0 < m) :
    sidePoint m m 0 = sidePoint m 0 0 := by
  apply Subtype.ext
  simp only [sidePoint, Nat.cast_zero, add_zero, mul_zero, zero_div, Circle.exp_zero]
  rw [mul_div_cancel_right₀ _ (by exact_mod_cast (Nat.ne_of_gt hm)), Circle.exp_two_pi]

lemma sidePoint_injective_Ioo (m i : ℕ) (hm : 0 < m) :
    Set.InjOn (sidePoint m i) (Set.Ioo (0 : ℝ) 1) := by
  intro t ht s hs he
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hexp : Circle.exp (2 * Real.pi * ((i : ℝ) + t) / (m : ℝ)) =
      Circle.exp (2 * Real.pi * ((i : ℝ) + s) / (m : ℝ)) := by
    apply Circle.ext
    exact congrArg (fun x : ClosedDisk => x.val) he
  have hangle : 2 * Real.pi * ((i : ℝ) + t) / (m : ℝ) =
      2 * Real.pi * ((i : ℝ) + s) / (m : ℝ) := by
    apply Circle.exp_injOn_Ico (a := 2 * Real.pi * i / m)
      (b := 2 * Real.pi * (i+1) / m) ?_ ?_ ?_ hexp
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [← sub_div]
      apply (div_le_iff₀ hmR).2
      nlinarith
    · constructor
      · apply (div_le_div_iff_of_pos_right hmR).2
        nlinarith [ht.1]
      · apply (div_lt_div_iff_of_pos_right hmR).2
        nlinarith [ht.2]
    · constructor
      · apply (div_le_div_iff_of_pos_right hmR).2
        nlinarith [hs.1]
      · apply (div_lt_div_iff_of_pos_right hmR).2
        nlinarith [hs.2]
  have h := (div_left_inj' (ne_of_gt hmR)).mp hangle
  nlinarith

lemma sidePoint_interior_injective (m : ℕ) (hm : 0 < m)
    (i j : Fin m) {t s : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (he : sidePoint m i.val t = sidePoint m j.val s) : i = j ∧ t = s := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hi0 : (0 : ℝ) ≤ i.val := by positivity
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  have him : (i.val : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  have hjm : (j.val : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hexp : Circle.exp (2 * Real.pi * ((i.val : ℝ) + t) / (m : ℝ)) =
      Circle.exp (2 * Real.pi * ((j.val : ℝ) + s) / (m : ℝ)) := by
    apply Circle.ext
    exact congrArg (fun x : ClosedDisk => x.val) he
  have hangle : 2 * Real.pi * ((i.val : ℝ) + t) / (m : ℝ) =
      2 * Real.pi * ((j.val : ℝ) + s) / (m : ℝ) := by
    apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith) ?_ ?_ hexp
    · constructor
      · exact le_of_lt (div_pos (mul_pos hpi (by linarith [ht.1])) hmR)
      · apply (div_lt_iff₀ hmR).2
        nlinarith [ht.2]
    · constructor
      · exact le_of_lt (div_pos (mul_pos hpi (by linarith [hs.1])) hmR)
      · apply (div_lt_iff₀ hmR).2
        nlinarith [hs.2]
  have hangle' := (div_left_inj' (ne_of_gt hmR)).mp hangle
  have he' : (i.val : ℝ) + t = (j.val : ℝ) + s := by nlinarith
  have hij : i.val = j.val := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have h' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
      nlinarith [ht.2, hs.1]
    · have h' : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast h
      nlinarith [ht.1, hs.2]
  refine ⟨Fin.ext hij, ?_⟩
  simp only [hij] at he'
  linarith

/-- Every generating side-pairing relation is closed. This does not by itself
assert that its equivalence closure is closed. -/
lemma sideRelation_isClosed {n : ℕ} (word : Word n) :
    IsClosed {p : ClosedDisk × ClosedDisk | sideRelation word p.1 p.2} := by
  classical
  let f (i j : Fin word.length) (t : unitInterval) : ClosedDisk × ClosedDisk :=
    (sidePoint word.length i.val (if (word.get i).2 then t.val else 1-t.val),
      sidePoint word.length j.val (if (word.get j).2 then t.val else 1-t.val))
  have hf (i j : Fin word.length) : Continuous (f i j) := by
    apply Continuous.prodMk
    · exact (sidePoint_continuous _ _).comp (by split_ifs <;> fun_prop)
    · exact (sidePoint_continuous _ _).comp (by split_ifs <;> fun_prop)
  have hfi (i j : Fin word.length) : IsClosed (Set.range (f i j)) :=
    (isCompact_range (hf i j)).isClosed
  have he : {p : ClosedDisk × ClosedDisk | sideRelation word p.1 p.2} =
      (if word = [] then {p | ‖p.1.val‖ = 1 ∧ ‖p.2.val‖ = 1} else ∅) ∪
      ⋃ (i : Fin word.length) (j : Fin word.length),
        (if (word.get i).1 = (word.get j).1 then Set.range (f i j) else ∅) := by
    ext p
    simp only [sideRelation, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (⟨hw, hx, hy⟩ | ⟨i,j,t,hij,hx,hy⟩)
      · exact Or.inl (by simp [hw, hx, hy])
      · exact Or.inr ⟨i,j, by rw [if_pos hij]; exact ⟨t, Prod.ext hx.symm hy.symm⟩⟩
    · rintro (h | ⟨i,j,h⟩)
      · by_cases hw : word = []
        · exact Or.inl ⟨hw, by simpa [hw] using h⟩
        · simp [hw] at h
      · by_cases hij : (word.get i).1 = (word.get j).1
        · rw [if_pos hij] at h
          obtain ⟨t, ht⟩ := h
          exact Or.inr ⟨i,j,t,hij,(congrArg Prod.fst ht).symm,
            (congrArg Prod.snd ht).symm⟩
        · rw [if_neg hij] at h
          exact h.elim
  rw [he]
  apply IsClosed.union
  · split_ifs
    · exact (isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const)
    · exact isClosed_empty
  · apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    split_ifs
    · exact hfi i j
    · exact isClosed_empty



/-- The actual polygon face chart is a quotient map, since its disk chart
is a homeomorphism and the polygon projection carries the quotient topology. -/
lemma polygonFace_quotient {e : ℕ} (word : Word e)
    [CellStructure (PolygonSurface word)] (charts : PolygonCharts word) :
    IsQuotientMap (characteristic (PolygonSurface word) 2 charts.face) := by
  have he : (characteristic (PolygonSurface word) 2 charts.face : Disk 2 → PolygonSurface word) =
      polygonProjection word ∘ charts.disk := funext charts.face_chart
  rw [he]
  exact (polygonProjection_quotient word).comp charts.disk.isQuotientMap

/-- Weak topology of the proposed polygon charts follows from their actual
quotient face chart. This fact requires no prior CW structure. -/
lemma polygonWeakTopology {e : ℕ} (word : Word e)
    [CellStructure (PolygonSurface word)] (charts : PolygonCharts word)
    (A : Set (PolygonSurface word)) :
    IsClosed A ↔ ∀ n (c : Cell (PolygonSurface word) n),
      IsClosed (characteristic (PolygonSurface word) n c ⁻¹' A) := by
  constructor
  · intro h n c
    exact h.preimage (characteristic (PolygonSurface word) n c).continuous
  · intro h
    exact (polygonFace_quotient word charts).isClosed_preimage.mp (h 2 charts.face)

/-- With the prescribed finite polygon cell counts, any closed cell has
finite support once the open cells cover the actual space. -/
lemma polygonClosureFinite {e : ℕ} (word : Word e)
    [CellStructure (PolygonSurface word)]
    (hc : PolygonCellCounts (PolygonSurface word) e)
    (hcover : ⋃ (n : ℕ) (c : Cell (PolygonSurface word) n),
      openCell (PolygonSurface word) n c = univ) :
    ∀ n (c : Cell (PolygonSurface word) n),
      ∃ F : Finset (Σ m, Cell (PolygonSurface word) m),
        closedCell (PolygonSurface word) n c ⊆ ⋃ d ∈ F,
          openCell (PolygonSurface word) d.1 d.2 := by
  classical
  let l₀ := (Classical.choice hc.1).symm
  let l₁ := (Classical.choice hc.2.1).symm
  let l₂ := (Classical.choice hc.2.2.1).symm
  let F : Finset (Σ m, Cell (PolygonSurface word) m) :=
    (Finset.univ.image fun i : Fin 1 => ⟨0, l₀ i⟩) ∪
    (Finset.univ.image fun i : Fin e => ⟨1, l₁ i⟩) ∪
    (Finset.univ.image fun i : Fin 1 => ⟨2, l₂ i⟩)
  have hmem (m : ℕ) (c : Cell (PolygonSurface word) m) : (⟨m, c⟩ : Σ m, Cell (PolygonSurface word) m) ∈ F := by
    rcases m with _ | _ | _ | m
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨l₀.symm c, Finset.mem_univ _, by simp⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨l₁.symm c, Finset.mem_univ _, by simp⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨l₂.symm c, Finset.mem_univ _, by simp⟩)
    · exact (hc.2.2.2 (m+3) (by omega)).false c |>.elim
  intro n c
  refine ⟨F, ?_⟩
  intro x _
  have hx : x ∈ ⋃ (n : ℕ) (c : Cell (PolygonSurface word) n),
      openCell (PolygonSurface word) n c := hcover.symm ▸ mem_univ x
  obtain ⟨m, hx⟩ := mem_iUnion.mp hx
  obtain ⟨d, hx⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨⟨m, d⟩, mem_iUnion.mpr ⟨hmem m d, hx⟩⟩



/-- Reindex the characteristic cell coordinates by a prescribed finite
labelling. This preserves the common reference-disk orientation. -/
lemma finiteCellCoordinates (X : Type) [TopologicalSpace X] [CWStructure X]
    (n m : ℕ) (labels : Fin m ≃ Cell X n)
    (g : ℤ ≃ₗ[ℤ] P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
      (referenceDiskPair.{0} n) (n : ℤ)) :
    ∃ c : chainGroup X ℤ ℤ n ≃ₗ[ℤ] (Fin m → ℤ),
      ∀ i z, c (P202Specs.CellularDegrees.cellClass X ℤ ℤ n (labels i) (g z)) =
        Pi.single i z := by
  classical
  obtain ⟨e, he⟩ := P202.Homology.cellularOrientedCoordinates X ℤ ℤ n g
  refine ⟨(e.trans (Finsupp.domLCongr labels.symm)).trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin m)), ?_⟩
  intro i z
  change Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin m)
      ((Finsupp.domLCongr labels.symm : (Cell X n →₀ ℤ) ≃ₗ[ℤ] (Fin m →₀ ℤ))
        (e (P202Specs.CellularDegrees.cellClass X ℤ ℤ n (labels i) (g z)))) = _
  rw [show e (P202Specs.CellularDegrees.cellClass X ℤ ℤ n (labels i) (g z)) = Finsupp.single (labels i) z from he (labels i) z, Finsupp.domLCongr_single, labels.symm_apply_apply,
    Finsupp.linearEquivFunOnFinite_single]

/-- With one cell, evaluation of characteristic coordinates at that cell
is the normalized copy of the coefficient module. -/
lemma singleCellCoordinates (X : Type) [TopologicalSpace X] [CWStructure X]
    (n : ℕ) [Subsingleton (Cell X n)] (a : Cell X n)
    (g : ℤ ≃ₗ[ℤ] P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
      (referenceDiskPair.{0} n) (n : ℤ)) :
    ∃ c : chainGroup X ℤ ℤ n ≃ₗ[ℤ] ℤ,
      ∀ z, c (P202Specs.CellularDegrees.cellClass X ℤ ℤ n a (g z)) = z := by
  classical
  obtain ⟨e, he⟩ := P202.Homology.cellularOrientedCoordinates X ℤ ℤ n g
  refine ⟨e.trans (Finsupp.uniqueLinearEquiv ℤ ℤ a), ?_⟩
  intro z
  change Finsupp.uniqueLinearEquiv ℤ ℤ a
    (e (P202Specs.CellularDegrees.cellClass X ℤ ℤ n a (g z))) = z
  rw [show e (P202Specs.CellularDegrees.cellClass X ℤ ℤ n a (g z)) = Finsupp.single a z from he a z]
  simp

/-- All polygon coordinates can be chosen compatibly with any three
reference orientations, with the same orientation at every edge. -/
lemma polygonCoordinates {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)]
    (hc : PolygonCellCounts (PolygonSurface word) e)
    (charts : PolygonCharts word)
    (g₀ : ℤ ≃ₗ[ℤ] P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
      (referenceDiskPair.{0} 0) 0)
    (g₁ : ℤ ≃ₗ[ℤ] P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
      (referenceDiskPair.{0} 1) 1)
    (g₂ : ℤ ≃ₗ[ℤ] P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
      (referenceDiskPair.{0} 2) 2) :
    ∃ (c₀ : chainGroup (PolygonSurface word) ℤ ℤ 0 ≃ₗ[ℤ] ℤ)
      (c₁ : chainGroup (PolygonSurface word) ℤ ℤ 1 ≃ₗ[ℤ] (Fin e → ℤ))
      (c₂ : chainGroup (PolygonSurface word) ℤ ℤ 2 ≃ₗ[ℤ] ℤ),
      (∀ z, c₀ (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 0
        charts.vertex (g₀ z)) = z) ∧
      (∀ i z, c₁ (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 1
        (charts.edges i) (g₁ z)) = Pi.single i z) ∧
      (∀ z, c₂ (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 2
        charts.face (g₂ z)) = z) := by
  letI : Subsingleton (Cell (PolygonSurface word) 0) :=
    (Classical.choice hc.1).injective.subsingleton
  letI : Subsingleton (Cell (PolygonSurface word) 2) :=
    (Classical.choice hc.2.2.1).injective.subsingleton
  obtain ⟨c₀, h₀⟩ := singleCellCoordinates (PolygonSurface word) 0 charts.vertex g₀
  obtain ⟨c₁, h₁⟩ := finiteCellCoordinates (PolygonSurface word) 1 e charts.edges g₁
  obtain ⟨c₂, h₂⟩ := singleCellCoordinates (PolygonSurface word) 2 charts.face g₂
  exact ⟨c₀, c₁, c₂, h₀, h₁, h₂⟩

/-- The entire polygon differential is determined by the boundary of its
oriented face class at 1. The normalizations and the first differential
are consequences of cellular homology, rather than extra premises. -/
lemma polygonDifferentials_of_unitColumn {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)]
    (hc : PolygonCellCounts (PolygonSurface word) e)
    (charts : PolygonCharts word) (coefficient : ℤ)
    (g₁ : ℤ ≃ₗ[ℤ] P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
      (referenceDiskPair.{0} 1) 1)
    (g₂ : ℤ ≃ₗ[ℤ] P202Specs.RelativeSingularChains.relativeHomology ℤ ℤ
      (referenceDiskPair.{0} 2) 2)
    (c₁ : chainGroup (PolygonSurface word) ℤ ℤ 1 ≃ₗ[ℤ] (Fin e → ℤ))
    (h₁ : ∀ i z, c₁ (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 1
      (charts.edges i) (g₁ z)) = Pi.single i z)
    (hb : ∀ i, c₁ (differential (PolygonSurface word) ℤ ℤ 1
      (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 2
        charts.face (g₂ 1))) i = coefficient) :
    PolygonDifferentials word charts coefficient := by
  obtain ⟨d₀⟩ := (P202.Homology.DiskBridge.referenceDiskHomology ℤ ℤ 0 0).1 rfl
  let g₀ := d₀.symm
  letI : Subsingleton (Cell (PolygonSurface word) 0) :=
    (Classical.choice hc.1).injective.subsingleton
  letI : Subsingleton (Cell (PolygonSurface word) 2) :=
    (Classical.choice hc.2.2.1).injective.subsingleton
  obtain ⟨c₀, h₀⟩ := singleCellCoordinates (PolygonSurface word) 0 charts.vertex g₀
  obtain ⟨c₂, h₂⟩ := singleCellCoordinates (PolygonSurface word) 2 charts.face g₂
  apply polygonDifferentials_of_cellColumns word hc charts coefficient
    c₀ c₁ c₂ g₀ g₁ g₂ h₀ h₁ h₂
  intro z i
  have hg : g₂ z = z • g₂ 1 := by
    simpa only [zsmul_eq_mul, Int.cast_id, mul_one] using (map_zsmul g₂ z (1 : ℤ))
  rw [hg]
  simp only [P202Specs.CellularDegrees.cellClass, map_zsmul]
  change z * c₁ (differential (PolygonSurface word) ℤ ℤ 1
    (P202Specs.CellularDegrees.cellClass (PolygonSurface word) ℤ ℤ 2
      charts.face (g₂ 1))) i = coefficient * z
  rw [hb, mul_comm]



/-- A closed equivalence relation on a compact Hausdorff space has a Hausdorff quotient. -/
theorem quotient_t2_of_closed_relation {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (s : Setoid X)
    (hs : IsClosed {p : X × X | s.r p.1 p.2}) : T2Space (Quotient s) := by
  let q : X → Quotient s := Quotient.mk s
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  have hclosed : IsClosedMap q := by
    intro A hA
    apply hq.isClosed_preimage.mp
    have heq : q ⁻¹' (q '' A) = Prod.snd '' ({p : X × X | s.r p.1 p.2} ∩ (A ×ˢ univ)) := by
      ext y
      constructor
      · rintro ⟨x, hx, he⟩
        exact ⟨(x,y), ⟨Quotient.exact he, hx, mem_univ _⟩, rfl⟩
      · rintro ⟨⟨x,z⟩, ⟨hr, hx, _⟩, rfl⟩
        exact ⟨x, hx, Quotient.sound hr⟩
    rw [heq]
    exact ((hs.inter (hA.prod isClosed_univ)).isCompact.image continuous_snd).isClosed
  have hfib : ∀ y, IsCompact (q ⁻¹' {y}) := by
    intro y
    obtain ⟨x, rfl⟩ := hq.surjective y
    have heq : q ⁻¹' {q x} = {z | s.r x z} := by
      ext z
      change q z = q x ↔ s.r x z
      rw [eq_comm]
      exact Quotient.eq
    rw [heq]
    exact (hs.preimage (continuous_const.prodMk continuous_id)).isCompact
  have hp : IsProperMap q :=
    isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hq.continuous, hclosed, hfib⟩
  have hqq : IsQuotientMap (Prod.map q q) :=
    (hp.prodMap hp).isClosedMap.isQuotientMap (hp.prodMap hp).continuous
      (by
        intro p
        obtain ⟨a, ha⟩ := hq.surjective p.1
        obtain ⟨b, hb⟩ := hq.surjective p.2
        exact ⟨(a,b), Prod.ext ha hb⟩)
  apply t2_iff_isClosed_diagonal.mpr
  apply hqq.isClosed_preimage.mp
  convert hs using 1
  ext p
  exact Quotient.eq



section GenusZeroCW


inductive GenusZeroCell : ℕ → Type
  | vertex : GenusZeroCell 0
  | face : GenusZeroCell 2

@[instance_reducible] def genusZeroCellStructure : CellStructure (OrientedSurface 0) where
  Cell := GenusZeroCell
  characteristic _n c := match c with
    | .vertex => ContinuousMap.const _ (polygonProjection [] (sidePoint 0 0 0))
    | .face => (polygonProjection []).comp ⟨complexDiskHomeomorph, complexDiskHomeomorph.continuous⟩

local instance : CellStructure (OrientedSurface 0) := genusZeroCellStructure

lemma genusZero_vertex_openCell :
    openCell (OrientedSurface 0) 0 GenusZeroCell.vertex =
      {polygonProjection [] (sidePoint 0 0 0)} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    rfl
  · rintro rfl
    exact ⟨⟨0, by simp [Metric.mem_ball]⟩, rfl⟩

lemma genusZero_face_openCell :
    openCell (OrientedSurface 0) 2 GenusZeroCell.face =
      polygonInteriorProjection ([] : Word 0) '' Set.univ := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨⟨complexDiskHomeomorph (interiorInclusion 2 y), ?_⟩, Set.mem_univ _, rfl⟩
    rw [complexDiskHomeomorph_norm]
    change ‖y.val‖ < 1
    simpa only [Metric.mem_ball, dist_zero_right] using y.property
  · rintro ⟨y,hy,rfl⟩
    let z := complexDiskHomeomorph.symm y.val
    have hz : ‖z.val‖ < 1 := by
      rw [← complexDiskHomeomorph_norm]
      simpa [z] using y.property
    exact ⟨⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩, congrArg (polygonProjection ([] : Word 0))
      (complexDiskHomeomorph.apply_symm_apply y.val)⟩

lemma genusZero_cover :
    ⋃ (n : ℕ) (c : Cell (OrientedSurface 0) n), openCell (OrientedSurface 0) n c = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y,rfl⟩ := Quotient.mk_surjective x
  have hy : ‖y.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using y.property
  rcases lt_or_eq_of_le hy with hy | hy
  · refine Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨GenusZeroCell.face, ?_⟩⟩
    rw [genusZero_face_openCell]
    exact ⟨⟨y,hy⟩, Set.mem_univ _, rfl⟩
  · refine Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨GenusZeroCell.vertex, ?_⟩⟩
    rw [genusZero_vertex_openCell]
    exact emptyWord_boundary_collapsed y _ hy (by simp [sidePoint])

lemma genusZero_interior_embedding :
    ∀ n (c : Cell (OrientedSurface 0) n),
      IsEmbedding (interiorMap (OrientedSurface 0) n c) := by
  intro n c
  cases c with
  | vertex => exact IsEmbedding.of_subsingleton _
  | face =>
    let f : OpenDisk 2 → InteriorDisk := fun y =>
      ⟨complexDiskHomeomorph (interiorInclusion 2 y), by
        rw [complexDiskHomeomorph_norm]
        change ‖y.val‖ < 1
        simpa only [Metric.mem_ball, dist_zero_right] using y.property⟩
    have hi : IsEmbedding (interiorInclusion 2) :=
      IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal
    have hf : IsEmbedding f := IsEmbedding.subtypeVal.of_comp_iff.mp
      (complexDiskHomeomorph.isEmbedding.comp hi)
    exact (polygonInteriorProjection_openEmbedding ([] : Word 0)).isEmbedding.comp hf

lemma genusZero_disjoint :
    (univ : Set (Σ n, Cell (OrientedSurface 0) n)).PairwiseDisjoint
      (fun c => openCell (OrientedSurface 0) c.1 c.2) := by
  have hVF : Disjoint (openCell (OrientedSurface 0) 0 GenusZeroCell.vertex)
      (openCell (OrientedSurface 0) 2 GenusZeroCell.face) := by
    rw [genusZero_vertex_openCell, genusZero_face_openCell]
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain rfl := hx
    obtain ⟨z, _, hz⟩ := hy
    have he : z.val = sidePoint 0 0 0 :=
      polygonProjection_eq_of_interior [] z.property hz
    have hn := congrArg (fun a : ClosedDisk => ‖a.val‖) he
    have hnorm : ‖(sidePoint 0 0 0).val‖ = 1 := by simp [sidePoint]
    exact (ne_of_lt z.property) (hn.trans hnorm)
  intro a ha b hb hab
  obtain ⟨n,c⟩ := a
  obtain ⟨m,d⟩ := b
  cases c <;> cases d
  · exact (hab rfl).elim
  · exact hVF
  · exact hVF.symm
  · exact (hab rfl).elim

lemma genusZero_boundary_lands :
    ∀ n (c : Cell (OrientedSurface 0) n),
      MapsTo (boundaryMap (OrientedSurface 0) n c) univ (skeletonLT (OrientedSurface 0) n) := by
  intro n c
  cases c with
  | vertex =>
    intro x hx
    have hx' : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have he : x.val = 0 := Subsingleton.elim _ _
    simp [he] at hx'
  | face =>
    intro x hx
    apply Set.mem_iUnion.mpr
    refine ⟨0, Set.mem_iUnion.mpr ⟨by omega, Set.mem_iUnion.mpr ⟨GenusZeroCell.vertex, ?_⟩⟩⟩
    rw [genusZero_vertex_openCell]
    change polygonProjection [] (complexDiskHomeomorph (boundaryInclusion 2 x)) = _
    apply emptyWord_boundary_collapsed
    · rw [complexDiskHomeomorph_norm]
      simpa only [boundaryInclusion, Metric.mem_sphere, dist_zero_right] using x.property
    · simp [sidePoint]

lemma genusZero_closure_finite :
    ∀ n (c : Cell (OrientedSurface 0) n), ∃ F : Finset (Σ m, Cell (OrientedSurface 0) m),
      closedCell (OrientedSurface 0) n c ⊆ ⋃ d ∈ F, openCell (OrientedSurface 0) d.1 d.2 := by
  intro n c
  classical
  refine ⟨{⟨0,GenusZeroCell.vertex⟩,⟨2,GenusZeroCell.face⟩}, ?_⟩
  intro x hx
  have h := Set.mem_iUnion.mp ((Set.ext_iff.mp genusZero_cover x).mpr (mem_univ _))
  obtain ⟨m, hm⟩ := h
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hm
  cases d
  · exact Set.mem_iUnion.mpr ⟨⟨0,GenusZeroCell.vertex⟩,
      Set.mem_iUnion.mpr ⟨by simp, hd⟩⟩
  · exact Set.mem_iUnion.mpr ⟨⟨2,GenusZeroCell.face⟩,
      Set.mem_iUnion.mpr ⟨by simp, hd⟩⟩

lemma genusZero_weak_topology : ∀ A : Set (OrientedSurface 0), IsClosed A ↔
    ∀ n (c : Cell (OrientedSurface 0) n), IsClosed (characteristic (OrientedSurface 0) n c ⁻¹' A) := by
  intro A
  constructor
  · exact fun h n c => h.preimage (characteristic (OrientedSurface 0) n c).continuous
  · intro h
    have hq : IsQuotientMap (characteristic (OrientedSurface 0) 2 GenusZeroCell.face) :=
      (polygonProjection_quotient ([] : Word 0)).comp complexDiskHomeomorph.isQuotientMap
    exact hq.isClosed_preimage.mp (h 2 GenusZeroCell.face)

@[instance_reducible] def genusZeroCWStructure : CWStructure (OrientedSurface 0) := by
  letI : T2Space (OrientedSurface 0) := genusZeroSphereHomeomorph.isEmbedding.t2Space
  exact P202.Topology.cwStructureOfWeak genusZero_interior_embedding genusZero_disjoint
    genusZero_cover genusZero_boundary_lands genusZero_closure_finite genusZero_weak_topology

def genusZeroVertexEquiv : GenusZeroCell 0 ≃ Fin 1 where
  toFun _ := 0
  invFun _ := GenusZeroCell.vertex
  left_inv c := by cases c; rfl
  right_inv c := Subsingleton.elim _ _

def genusZeroEdgeEquiv : GenusZeroCell 1 ≃ Fin 0 where
  toFun c := by cases c
  invFun c := Fin.elim0 c
  left_inv c := by cases c
  right_inv c := Fin.elim0 c

def genusZeroFaceEquiv : GenusZeroCell 2 ≃ Fin 1 where
  toFun _ := 0
  invFun _ := GenusZeroCell.face
  left_inv c := by cases c; rfl
  right_inv c := Subsingleton.elim _ _

end GenusZeroCW

lemma genusZeroPolygonCellStructures :
    ∃ C : CWStructure (OrientedSurface 0),
      letI := C
      PolygonCellCounts (OrientedSurface 0) (2*0) ∧
        Nonempty (PolygonCharts (orientedWord 0)) := by
  letI : CWStructure (OrientedSurface 0) := genusZeroCWStructure
  refine ⟨genusZeroCWStructure, ?_⟩
  refine ⟨⟨⟨genusZeroVertexEquiv⟩, ⟨genusZeroEdgeEquiv⟩,
    ⟨genusZeroFaceEquiv⟩, ?_⟩, ?_⟩
  · intro n hn
    exact ⟨fun c => by cases c <;> omega⟩
  · exact ⟨{
      vertex := GenusZeroCell.vertex
      edges := genusZeroEdgeEquiv.symm
      face := GenusZeroCell.face
      disk := complexDiskHomeomorph
      vertex_chart := fun _ => rfl
      edge_chart := fun i _ => Fin.elim0 i
      face_chart := fun _ => rfl }⟩


/-- With no edges, the positive cellular differential has no coordinates.
The orientations and all coordinate normalizations still come from the actual
characteristic maps. -/
lemma polygonDifferentials_no_edges (word : Word 0)
    [CWStructure (PolygonSurface word)]
    (hc : PolygonCellCounts (PolygonSurface word) 0)
    (charts : PolygonCharts word) (coefficient : ℤ) :
    PolygonDifferentials word charts coefficient := by
  obtain ⟨d₁⟩ := (P202.Homology.DiskBridge.referenceDiskHomology ℤ ℤ 1 1).1 rfl
  obtain ⟨d₂⟩ := (P202.Homology.DiskBridge.referenceDiskHomology ℤ ℤ 2 2).1 rfl
  obtain ⟨c₁, h₁⟩ := finiteCellCoordinates (PolygonSurface word) 1 0 charts.edges d₁.symm
  exact polygonDifferentials_of_unitColumn word hc charts coefficient d₁.symm d₂.symm
    c₁ h₁ (fun i => Fin.elim0 i)

/-- Complete CW and attaching-differential data for the genus-zero model.
The nonempty polygon families remain separate geometric obligations. -/
lemma genusZeroAttachingDifferentials :
    ∃ C : CWStructure (OrientedSurface 0),
      letI := C
      PolygonCellCounts (OrientedSurface 0) (2*0) ∧
        ∃ charts : PolygonCharts (orientedWord 0),
          PolygonDifferentials (orientedWord 0) charts 0 := by
  obtain ⟨C, hc, ⟨charts⟩⟩ := genusZeroPolygonCellStructures
  letI := C
  exact ⟨C, hc, charts, polygonDifferentials_no_edges (orientedWord 0) hc charts 0⟩

/-! A chain-level step toward the circle-degree calculation. These lemmas
prove the square-map action on classes represented by based loops; they do
not presume that such a loop is a generator of circle homology. -/
namespace CircleChains
open Opposite
open scoped Simplicial

open P202Specs.SingularChains

abbrev Triangle := Convexity.StdSimplex ℝ (Fin 3)
abbrev Interval := Convexity.StdSimplex ℝ (Fin 2)

lemma simplex_weights_le_one {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n+1))) (i : Fin (n+1)) :
    x.weights i ≤ 1 := by
  have ht := Finset.single_le_sum (f := fun i => x.weights i)
    (fun j _ => x.nonneg j) (Finset.mem_univ i)
  simpa using ht

def intervalParameter (x : Interval) : unitInterval :=
  ⟨x.weights 1, x.nonneg 1, simplex_weights_le_one x 1⟩

def triangleParameterU (x : Triangle) : unitInterval :=
  ⟨x.weights 1 + x.weights 2, add_nonneg (x.nonneg 1) (x.nonneg 2), by
    have ht : x.weights 0 + x.weights 1 + x.weights 2 = 1 := by
      have ht := x.total
      rw [Finsupp.sum_fintype _ _ (by simp)] at ht
      simpa only [Fin.sum_univ_three] using ht
    have h₀ : 0 ≤ x.weights 0 := x.nonneg 0
    linarith⟩

def triangleParameterV (x : Triangle) : unitInterval :=
  ⟨x.weights 2, x.nonneg 2, simplex_weights_le_one x 2⟩

lemma intervalParameter_continuous : Continuous intervalParameter := by
  exact (Convexity.StdSimplex.continuous_weights_apply ℝ 1).subtype_mk _
lemma triangleParameterU_continuous : Continuous triangleParameterU := by
  exact ((Convexity.StdSimplex.continuous_weights_apply ℝ 1).add
    (Convexity.StdSimplex.continuous_weights_apply ℝ 2)).subtype_mk _
lemma triangleParameterV_continuous : Continuous triangleParameterV := by
  exact (Convexity.StdSimplex.continuous_weights_apply ℝ 2).subtype_mk _

def loopSimplex (L : C(unitInterval, Circle)) : Simplex (TopCat.of Circle) 1 :=
  (simplexEquiv _ 1).symm ⟨fun x => L (intervalParameter x),
    L.continuous.comp intervalParameter_continuous⟩

def squareMap : TopCat.of Circle ⟶ TopCat.of Circle :=
  TopCat.ofHom ⟨fun z => z*z, continuous_id.mul continuous_id⟩

def squareTriangle (L : C(unitInterval, Circle)) : Simplex (TopCat.of Circle) 2 :=
  (simplexEquiv _ 2).symm ⟨fun x => L (triangleParameterU x) * L (triangleParameterV x),
    (L.continuous.comp triangleParameterU_continuous).mul
      (L.continuous.comp triangleParameterV_continuous)⟩

lemma face_weight_succ (x : Interval) (i : Fin 3) (j : Fin 2) :
    (faceInclusion (n:=1) i x).weights (i.succAbove j) = x.weights j := by
  rw [P202.SingularChains.faceInclusion_weights]
  exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => Fin.succAbove_right_injective h) _ _

lemma face_weight_zero (x : Interval) (i : Fin 3) :
    (faceInclusion (n:=1) i x).weights i = 0 := by
  rw [P202.SingularChains.faceInclusion_weights]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)

lemma triangleParameterU_face0 (x : Interval) : triangleParameterU (faceInclusion 0 x) = 1 := by
  apply Subtype.ext
  change (faceInclusion 0 x).weights 1 + (faceInclusion 0 x).weights 2 = 1
  have h₁ := face_weight_succ x 0 0
  have h₂ := face_weight_succ x 0 1
  norm_num at h₁ h₂
  rw [h₁, h₂]
  exact x.total_fin_two

lemma triangleParameterV_face0 (x : Interval) :
    triangleParameterV (faceInclusion 0 x) = intervalParameter x := by
  apply Subtype.ext
  exact face_weight_succ x 0 1

lemma triangleParameterU_face1 (x : Interval) :
    triangleParameterU (faceInclusion 1 x) = intervalParameter x := by
  apply Subtype.ext
  change (faceInclusion 1 x).weights 1 + (faceInclusion 1 x).weights 2 = x.weights 1
  rw [face_weight_zero]
  simpa using face_weight_succ x 1 1

lemma triangleParameterV_face1 (x : Interval) :
    triangleParameterV (faceInclusion 1 x) = intervalParameter x := by
  apply Subtype.ext
  exact face_weight_succ x 1 1

lemma triangleParameterU_face2 (x : Interval) :
    triangleParameterU (faceInclusion 2 x) = intervalParameter x := by
  apply Subtype.ext
  change (faceInclusion 2 x).weights 1 + (faceInclusion 2 x).weights 2 = x.weights 1
  rw [face_weight_zero, add_zero]
  exact face_weight_succ x 2 1

lemma triangleParameterV_face2 (x : Interval) : triangleParameterV (faceInclusion 2 x) = 0 := by
  apply Subtype.ext
  exact face_weight_zero x 2

lemma squareTriangle_face0 (L : C(unitInterval, Circle)) (h₁ : L 1 = 1) :
    face 0 (squareTriangle L) = loopSimplex L := by
  apply (simplexEquiv _ 1).injective
  rw [P202.SingularChains.simplexEquiv_face]
  apply ContinuousMap.ext
  intro x
  simp only [squareTriangle, Equiv.apply_symm_apply, ContinuousMap.comp_apply, loopSimplex]
  change L (triangleParameterU (faceInclusion 0 x)) *
    L (triangleParameterV (faceInclusion 0 x)) = L (intervalParameter x)
  rw [triangleParameterU_face0, triangleParameterV_face0, h₁, one_mul]

lemma squareTriangle_face1 (L : C(unitInterval, Circle)) :
    face 1 (squareTriangle L) =
      (TopCat.toSSet.map squareMap).app (op ⦋1⦌) (loopSimplex L) := by
  apply (simplexEquiv _ 1).injective
  rw [P202.SingularChains.simplexEquiv_face, P202.SingularChains.simplexEquiv_postcomp]
  apply ContinuousMap.ext
  intro x
  simp only [squareTriangle, Equiv.apply_symm_apply, ContinuousMap.comp_apply, loopSimplex]
  change L (triangleParameterU (faceInclusion 1 x)) *
    L (triangleParameterV (faceInclusion 1 x)) = L (intervalParameter x) * L (intervalParameter x)
  rw [triangleParameterU_face1, triangleParameterV_face1]

lemma squareTriangle_face2 (L : C(unitInterval, Circle)) (h₀ : L 0 = 1) :
    face 2 (squareTriangle L) = loopSimplex L := by
  apply (simplexEquiv _ 1).injective
  rw [P202.SingularChains.simplexEquiv_face]
  apply ContinuousMap.ext
  intro x
  simp only [squareTriangle, Equiv.apply_symm_apply, ContinuousMap.comp_apply, loopSimplex]
  change L (triangleParameterU (faceInclusion 2 x)) *
    L (triangleParameterV (faceInclusion 2 x)) = L (intervalParameter x)
  rw [triangleParameterU_face2, triangleParameterV_face2, h₀, mul_one]

/-- An explicit singular triangle witnesses doubling on any based loop. -/
lemma square_loop_boundary (L : C(unitInterval, Circle)) (h₀ : L 0 = 1) (h₁ : L 1 = 1) :
    boundary ℤ ℤ (TopCat.of Circle) 1 (Finsupp.single (squareTriangle L) (1:ℤ)) =
      Finsupp.single (loopSimplex L) (1:ℤ) -
        Finsupp.single ((TopCat.toSSet.map squareMap).app (op ⦋1⦌) (loopSimplex L)) (1:ℤ) +
          Finsupp.single (loopSimplex L) (1:ℤ) := by
  rw [P202.SingularChains.boundary_single]
  change (∑ i : Fin 3, (-1:ℤ)^i.val • Finsupp.single (face i (squareTriangle L)) (1:ℤ)) = _
  simp only [Fin.sum_univ_three, Fin.val_zero, pow_zero, one_smul,
    Fin.val_one, pow_one, neg_smul, squareTriangle_face0 L h₁,
    squareTriangle_face1, squareTriangle_face2 L h₀, sub_eq_add_neg]
  norm_num

open HomologicalComplex P202Specs.SpheresDisks

lemma classOf_eq_of_boundary (K : ChainComplex (ModuleCat ℤ) ℤ) (n : ℤ)
    (z z' : K.X n) (hz : K.d n (n-1) z = 0) (hz' : K.d n (n-1) z' = 0)
    (b : K.X (n+1)) (hb : z-z' = K.d (n+1) n b) :
    classOf ℤ K n z hz = classOf ℤ K n z' hz' := by
  apply sub_eq_zero.mp
  change K.homologyπ n (K.cyclesMk z (n-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hz) -
    K.homologyπ n (K.cyclesMk z' (n-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hz') = 0
  rw [← map_sub]
  have hc : K.cyclesMk z (n-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hz - K.cyclesMk z' (n-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hz' =
      K.toCycles (n+1) n b := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    rw [map_sub]
    have hK : K.iCycles n (K.cyclesMk z (n-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hz) = z := K.i_cyclesMk _ _ _ _
    have hK' : K.iCycles n (K.cyclesMk z' (n-1) ((ComplexShape.down ℤ).next_eq' (by simp)) hz') = z' := K.i_cyclesMk _ _ _ _
    have hB : K.iCycles n (K.toCycles (n+1) n b) = K.d (n+1) n b :=
      congrArg (fun f => f b) (K.toCycles_i (n+1) n)
    exact (congrArg₂ (· - ·) hK hK').trans (hb.trans hB.symm)
  rw [hc]
  exact congrArg (fun f => f b) (K.toCycles_comp_homologyπ (n+1) n)



lemma classOf_add (K : ChainComplex (ModuleCat ℤ) ℤ) (n : ℤ)
    (z z' : K.X n) (hz : K.d n (n-1) z = 0) (hz' : K.d n (n-1) z' = 0) :
    classOf ℤ K n (z+z') (by rw [map_add, hz, hz', add_zero]) =
      classOf ℤ K n z hz + classOf ℤ K n z' hz' := by
  have hn : (ComplexShape.down ℤ).next n = n-1 := (ComplexShape.down ℤ).next_eq' (by simp)
  have hs : K.d n (n-1) (z+z') = 0 := by rw [map_add, hz, hz', add_zero]
  have hc : K.cyclesMk (z+z') (n-1) hn hs =
      K.cyclesMk z (n-1) hn hz + K.cyclesMk z' (n-1) hn hz' := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    have hK := K.i_cyclesMk (z+z') (n-1) hn hs
    have hK₁ := K.i_cyclesMk z (n-1) hn hz
    have hK₂ := K.i_cyclesMk z' (n-1) hn hz'
    exact hK.trans ((map_add (K.iCycles n).hom _ _).trans (congrArg₂ (· + ·) hK₁ hK₂)).symm
  exact (congrArg (K.homologyπ n) hc).trans (map_add (K.homologyπ n).hom _ _)

open P202Specs.CellularDegrees

def ordinarySquareMap : ordinaryComplex ℤ ℤ (TopCat.of Circle) ⟶
    ordinaryComplex ℤ ℤ (TopCat.of Circle) :=
  (ordinaryFunctor ℤ ℤ).map squareMap

def ordinaryLoopChain (L : C(unitInterval, Circle)) :
    (ordinaryComplex ℤ ℤ (TopCat.of Circle)).X 1 :=
  simplexChainZ ℤ ℤ (TopCat.of Circle) 1 (loopSimplex L) 1

def ordinaryTriangleChain (L : C(unitInterval, Circle)) :
    (ordinaryComplex ℤ ℤ (TopCat.of Circle)).X 2 :=
  simplexChainZ ℤ ℤ (TopCat.of Circle) 2 (squareTriangle L) 1

lemma ordinary_square_boundary (L : C(unitInterval, Circle))
    (h₀ : L 0 = 1) (h₁ : L 1 = 1) :
    (ordinaryComplex ℤ ℤ (TopCat.of Circle)).d 2 1 (ordinaryTriangleChain L) =
      ordinaryLoopChain L - ordinarySquareMap.f 1 (ordinaryLoopChain L) +
        ordinaryLoopChain L := by
  have hm := P202.Homology.CellularDegrees.simplexChainZ_map ℤ ℤ squareMap 1 (loopSimplex L) 1
  change ordinarySquareMap.f 1 (ordinaryLoopChain L) = _ at hm
  rw [hm]
  apply (ordinaryNonnegativeIso ℤ ℤ (TopCat.of Circle) 1).toLinearEquiv.injective
  have ht := congrArg (fun f => f (Finsupp.single (squareTriangle L) (1:ℤ)))
    (P202.SingularChains.ordinary_boundary ℤ ℤ (TopCat.of Circle) 1)
  change (ordinaryNonnegativeIso ℤ ℤ (TopCat.of Circle) 1).hom
      ((ordinaryComplex ℤ ℤ (TopCat.of Circle)).d 2 1
        ((ordinaryNonnegativeIso ℤ ℤ (TopCat.of Circle) 2).inv
          (Finsupp.single (squareTriangle L) (1:ℤ)))) = _ at ht
  change (ordinaryNonnegativeIso ℤ ℤ (TopCat.of Circle) 1).hom _ = _
  simp only [ordinaryTriangleChain, ordinaryLoopChain, simplexChainZ, map_add, map_sub,
    Iso.toLinearEquiv_apply, Iso.inv_hom_id_apply]
  exact ht.trans (square_loop_boundary L h₀ h₁)

lemma square_loop_homology_action_of_cycle (L : C(unitInterval, Circle))
    (h₀ : L 0 = 1) (h₁ : L 1 = 1)
    (hz : (ordinaryComplex ℤ ℤ (TopCat.of Circle)).d 1 0 (ordinaryLoopChain L) = 0) :
    homologyMap ordinarySquareMap 1
      (classOf ℤ (ordinaryComplex ℤ ℤ (TopCat.of Circle)) 1 (ordinaryLoopChain L) hz) =
    (2:ℤ) • classOf ℤ (ordinaryComplex ℤ ℤ (TopCat.of Circle)) 1 (ordinaryLoopChain L) hz := by
  let K := ordinaryComplex ℤ ℤ (TopCat.of Circle)
  let z := ordinaryLoopChain L
  let f : K ⟶ K := ordinarySquareMap
  have hfz : K.d 1 0 (f.f 1 z) = 0 := by
    have ht := congrArg (fun g => g z) (f.comm 1 0)
    change K.d 1 0 (f.f 1 z) = f.f 0 (K.d 1 0 z) at ht
    exact ht.trans (by rw [hz]; exact map_zero _)
  have hzz : K.d 1 0 (z+z) = 0 := by rw [map_add, hz, add_zero]
  change homologyMap f 1 (classOf ℤ K 1 z hz) = (2:ℤ) • classOf ℤ K 1 z hz
  have hm := P202.Homology.CellularDegrees.homologyMap_classOf ℤ f 1 z hz hfz
  refine hm.trans ?_
  have he := classOf_eq_of_boundary K 1 (f.f 1 z) (z+z) hfz hzz
    (-ordinaryTriangleChain L) (by
      have hb := ordinary_square_boundary L h₀ h₁
      change K.d (1+1) 1 (ordinaryTriangleChain L) = z - f.f 1 z + z at hb
      rw [map_neg, hb]
      abel)
  exact he.trans ((classOf_add K 1 z z hz hz).trans (show (2:ℤ) • classOf ℤ K 1 z hz = _ by
    rw [show (2:ℤ) = 1+1 from rfl, add_zsmul, one_zsmul]).symm)

lemma intervalParameter_face0 (x : Convexity.StdSimplex ℝ (Fin 1)) :
    intervalParameter (faceInclusion 0 x) = 1 := by
  apply Subtype.ext
  change (faceInclusion (n:=0) 0 x).weights 1 = 1
  rw [P202.SingularChains.faceInclusion_weights, Fin.succAbove_zero]
  have h : (x.weights.mapDomain Fin.succ) ((0:Fin 1).succ) = x.weights 0 :=
    Finsupp.mapDomain_apply_of_injective (Fin.succ_injective 1) _ _
  change (x.weights.mapDomain Fin.succ) ((0:Fin 1).succ) = 1
  rw [h]
  have ht := x.total
  rw [Finsupp.sum_fintype _ _ (by simp)] at ht
  simpa using ht

lemma intervalParameter_face1 (x : Convexity.StdSimplex ℝ (Fin 1)) :
    intervalParameter (faceInclusion 1 x) = 0 := by
  apply Subtype.ext
  change (faceInclusion (n:=0) 1 x).weights 1 = 0
  rw [P202.SingularChains.faceInclusion_weights]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)

lemma loopSimplex_boundary (L : C(unitInterval, Circle)) (h₀ : L 0 = 1) (h₁ : L 1 = 1) :
    boundary ℤ ℤ (TopCat.of Circle) 0 (Finsupp.single (loopSimplex L) (1:ℤ)) = 0 := by
  have hf : face 0 (loopSimplex L) = face 1 (loopSimplex L) := by
    apply (simplexEquiv _ 0).injective
    rw [P202.SingularChains.simplexEquiv_face, P202.SingularChains.simplexEquiv_face]
    apply ContinuousMap.ext
    intro x
    simp only [loopSimplex, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
    change L (intervalParameter (faceInclusion 0 x)) = L (intervalParameter (faceInclusion 1 x))
    rw [intervalParameter_face0, intervalParameter_face1, h₀, h₁]
  rw [P202.SingularChains.boundary_single]
  change (∑ i : Fin 2, (-1:ℤ)^i.val • Finsupp.single (face i (loopSimplex L)) (1:ℤ)) = _
  simp [Fin.sum_univ_two, hf]

lemma ordinaryLoopChain_cycle (L : C(unitInterval, Circle)) (h₀ : L 0 = 1) (h₁ : L 1 = 1) :
    (ordinaryComplex ℤ ℤ (TopCat.of Circle)).d 1 0 (ordinaryLoopChain L) = 0 := by
  apply (ordinaryNonnegativeIso ℤ ℤ (TopCat.of Circle) 0).toLinearEquiv.injective
  have ht := congrArg (fun f => f (Finsupp.single (loopSimplex L) (1:ℤ)))
    (P202.SingularChains.ordinary_boundary ℤ ℤ (TopCat.of Circle) 0)
  change (ordinaryNonnegativeIso ℤ ℤ (TopCat.of Circle) 0).hom
      ((ordinaryComplex ℤ ℤ (TopCat.of Circle)).d 1 0 (ordinaryLoopChain L)) = _ at ht
  simpa only [map_zero, Iso.toLinearEquiv_apply] using ht.trans (loopSimplex_boundary L h₀ h₁)

/-- Doubling on every actual integral homology class represented by a based circle loop. -/
lemma square_loop_homology_action (L : C(unitInterval, Circle)) (h₀ : L 0 = 1) (h₁ : L 1 = 1) :
    homologyMap ordinarySquareMap 1
      (classOf ℤ (ordinaryComplex ℤ ℤ (TopCat.of Circle)) 1 (ordinaryLoopChain L)
        (ordinaryLoopChain_cycle L h₀ h₁)) =
    (2:ℤ) • classOf ℤ (ordinaryComplex ℤ ℤ (TopCat.of Circle)) 1 (ordinaryLoopChain L)
      (ordinaryLoopChain_cycle L h₀ h₁) :=
  square_loop_homology_action_of_cycle L h₀ h₁ (ordinaryLoopChain_cycle L h₀ h₁)


end CircleChains


/-- The finitely many endpoints of the circular polygon sides. -/
def polygonVertices (m : ℕ) : Set ClosedDisk :=
  Set.range (fun i : Fin m => sidePoint m i.val 0)

lemma polygonVertices_isClosed (m : ℕ) : IsClosed (polygonVertices m) :=
  Set.finite_range _ |>.isClosed

lemma sidePoint_mem_vertices_zero (m : ℕ) (i : Fin m) :
    sidePoint m i.val 0 ∈ polygonVertices m := ⟨i, rfl⟩

lemma sidePoint_mem_vertices_one (m : ℕ) (hm : 0 < m) (i : Fin m) :
    sidePoint m i.val 1 ∈ polygonVertices m := by
  rw [sidePoint_one]
  by_cases hi : i.val+1 < m
  · exact ⟨⟨i.val+1, hi⟩, rfl⟩
  · have he : i.val+1 = m := by omega
    rw [he, sidePoint_cycle m hm]
    exact ⟨⟨0, hm⟩, rfl⟩

/-- A point strictly inside a side cannot be any polygon endpoint. -/
lemma sidePoint_interior_not_vertex (m : ℕ) (hm : 0 < m) (i : Fin m)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    sidePoint m i.val t ∉ polygonVertices m := by
  rintro ⟨j, hj⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hexp : Circle.exp (2 * Real.pi * ((i.val : ℝ) + t) / (m : ℝ)) =
      Circle.exp (2 * Real.pi * (j.val : ℝ) / (m : ℝ)) := by
    apply Circle.ext
    simpa [sidePoint] using congrArg (fun x : ClosedDisk => x.val) hj.symm
  have hangle : 2 * Real.pi * ((i.val : ℝ) + t) / (m : ℝ) =
      2 * Real.pi * (j.val : ℝ) / (m : ℝ) := by
    apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith) ?_ ?_ hexp
    · constructor
      · exact le_of_lt (div_pos (mul_pos hpi (by linarith [ht.1])) hmR)
      · apply (div_lt_iff₀ hmR).2
        have him : (i.val : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
        nlinarith [ht.2]
    · constructor
      · positivity
      · apply (div_lt_iff₀ hmR).2
        have hjm : (j.val : ℝ) < m := by exact_mod_cast j.isLt
        nlinarith
  have hangle' := (div_left_inj' (ne_of_gt hmR)).mp hangle
  have he : (i.val : ℝ) + t = j.val := by nlinarith
  have hij : i.val < j.val := by
    have : (i.val : ℝ) < j.val := by linarith [ht.1]
    exact_mod_cast this
  have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
  linarith [ht.2]

lemma sidePoint_vertex_iff (m : ℕ) (hm : 0 < m) (i : Fin m)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    sidePoint m i.val t ∈ polygonVertices m ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    exact sidePoint_interior_not_vertex m hm i
      ⟨lt_of_le_of_ne ht.1 (Ne.symm hn.1), lt_of_le_of_ne ht.2 hn.2⟩ h
  · rintro (rfl | rfl)
    · exact sidePoint_mem_vertices_zero m i
    · exact sidePoint_mem_vertices_one m hm i

/-- Reverse a side coordinate when its letter is negatively oriented. -/
def orientedSideParameter (b : Bool) (t : unitInterval) : unitInterval :=
  if b then t else ⟨1-t.val, by constructor <;> linarith [t.property.1,t.property.2]⟩

@[simp] lemma orientedSideParameter_val (b : Bool) (t : unitInterval) :
    (orientedSideParameter b t).val = if b then t.val else 1-t.val := by
  cases b <;> rfl

@[simp] lemma orientedSideParameter_involutive (b : Bool) (t : unitInterval) :
    orientedSideParameter b (orientedSideParameter b t) = t := by
  apply Subtype.ext
  cases b <;> simp [orientedSideParameter]

lemma orientedSideParameter_injective (b : Bool) :
    Function.Injective (orientedSideParameter b) :=
  Function.Involutive.injective (orientedSideParameter_involutive b)

lemma orientedSideParameter_endpoint (b : Bool) (t : unitInterval) :
    ((orientedSideParameter b t).val = 0 ∨ (orientedSideParameter b t).val = 1) ↔
      t.val = 0 ∨ t.val = 1 := by
  cases b <;> simp only [orientedSideParameter_val, Bool.false_eq_true, ↓reduceIte]
  · constructor <;> rintro (h | h) <;> [right; left; right; left] <;> linarith

lemma sideRelation_symm {n : ℕ} (word : Word n) {x y : ClosedDisk}
    (h : sideRelation word x y) : sideRelation word y x := by
  rcases h with ⟨hw, hx, hy⟩ | ⟨i,j,t,hij,hx,hy⟩
  · exact Or.inl ⟨hw,hy,hx⟩
  · exact Or.inr ⟨j,i,t,hij.symm,hy,hx⟩

lemma sideRelation_vertex_iff {n : ℕ} (word : Word n) (hm : 0 < word.length)
    {x y : ClosedDisk} (h : sideRelation word x y) :
    x ∈ polygonVertices word.length ↔ y ∈ polygonVertices word.length := by
  rcases h with ⟨hw,_,_⟩ | ⟨i,j,t,_,rfl,rfl⟩
  · simp [hw] at hm
  · simp only [← orientedSideParameter_val]
    rw [sidePoint_vertex_iff _ hm _ (orientedSideParameter _ t).property,
      sidePoint_vertex_iff _ hm _ (orientedSideParameter _ t).property,
      orientedSideParameter_endpoint, orientedSideParameter_endpoint]

lemma sideRelation_trans_or_vertices {n : ℕ} (word : Word n)
    (hm : 0 < word.length) {x y z : ClosedDisk}
    (hxy : sideRelation word x y) (hyz : sideRelation word y z) :
    sideRelation word x z ∨
      (x ∈ polygonVertices word.length ∧ z ∈ polygonVertices word.length) := by
  by_cases hyv : y ∈ polygonVertices word.length
  · exact Or.inr ⟨(sideRelation_vertex_iff word hm hxy).mpr hyv,
      (sideRelation_vertex_iff word hm hyz).mp hyv⟩
  · rcases hxy with ⟨hw,_,_⟩ | ⟨i,j,t,hij,hx,hy⟩
    · simp [hw] at hm
    rcases hyz with ⟨hw,_,_⟩ | ⟨k,l,s,hkl,hy',hz⟩
    · simp [hw] at hm
    simp only [← orientedSideParameter_val] at hx hy hy' hz
    have ht : (orientedSideParameter (word.get j).2 t).val ∈ Set.Ioo (0 : ℝ) 1 := by
      have hn : ¬ ((orientedSideParameter (word.get j).2 t).val = 0 ∨
          (orientedSideParameter (word.get j).2 t).val = 1) := by
        intro h
        apply hyv
        rw [hy]
        exact (sidePoint_vertex_iff _ hm j (orientedSideParameter _ t).property).mpr h
      have hb := (orientedSideParameter (word.get j).2 t).property
      have hn0 : (orientedSideParameter (word.get j).2 t).val ≠ 0 := fun h => hn (Or.inl h)
      have hn1 : (orientedSideParameter (word.get j).2 t).val ≠ 1 := fun h => hn (Or.inr h)
      exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hn0), lt_of_le_of_ne hb.2 hn1⟩
    have hs : (orientedSideParameter (word.get k).2 s).val ∈ Set.Ioo (0 : ℝ) 1 := by
      have hn : ¬ ((orientedSideParameter (word.get k).2 s).val = 0 ∨
          (orientedSideParameter (word.get k).2 s).val = 1) := by
        intro h
        apply hyv
        rw [hy']
        exact (sidePoint_vertex_iff _ hm k (orientedSideParameter _ s).property).mpr h
      have hb := (orientedSideParameter (word.get k).2 s).property
      have hn0 : (orientedSideParameter (word.get k).2 s).val ≠ 0 := fun h => hn (Or.inl h)
      have hn1 : (orientedSideParameter (word.get k).2 s).val ≠ 1 := fun h => hn (Or.inr h)
      exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hn0), lt_of_le_of_ne hb.2 hn1⟩
    have hjk := sidePoint_interior_injective word.length hm j k ht hs (hy.symm.trans hy')
    obtain ⟨rfl, hts⟩ := hjk
    have hts' : t = s := orientedSideParameter_injective (word.get j).2 (Subtype.ext hts)
    subst s
    exact Or.inl (Or.inr ⟨i,l,t,hij.trans hkl,by simpa only [orientedSideParameter_val] using hx,by simpa only [orientedSideParameter_val] using hz⟩)

/-- Normal form when all polygon endpoints belong to one vertex class. -/
def polygonNormalRelation {n : ℕ} (word : Word n) (x y : ClosedDisk) : Prop :=
  x = y ∨ sideRelation word x y ∨
    (x ∈ polygonVertices word.length ∧ y ∈ polygonVertices word.length)

lemma polygonNormalRelation_trans {n : ℕ} (word : Word n) (hm : 0 < word.length)
    {x y z : ClosedDisk} (hxy : polygonNormalRelation word x y)
    (hyz : polygonNormalRelation word y z) : polygonNormalRelation word x z := by
  rcases hxy with rfl | hxy | ⟨hx,hy⟩
  · exact hyz
  · rcases hyz with rfl | hyz | ⟨hy,hz⟩
    · exact Or.inr (Or.inl hxy)
    · exact Or.inr (sideRelation_trans_or_vertices word hm hxy hyz)
    · exact Or.inr (Or.inr ⟨(sideRelation_vertex_iff word hm hxy).mpr hy,hz⟩)
  · rcases hyz with rfl | hyz | ⟨_,hz⟩
    · exact Or.inr (Or.inr ⟨hx,hy⟩)
    · exact Or.inr (Or.inr ⟨hx,(sideRelation_vertex_iff word hm hyz).mp hy⟩)
    · exact Or.inr (Or.inr ⟨hx,hz⟩)

lemma polygonRelation_normalForm {n : ℕ} (word : Word n) (hm : 0 < word.length)
    {x y : ClosedDisk} (h : (polygonSetoid word).r x y) :
    polygonNormalRelation word x y := by
  induction h with
  | rel x y h => exact Or.inr (Or.inl h)
  | refl x => exact Or.inl rfl
  | symm x y h ih =>
    rcases ih with h | h | ⟨hx,hy⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl (sideRelation_symm word h))
    · exact Or.inr (Or.inr ⟨hy,hx⟩)
  | trans x y z _ _ ih1 ih2 => exact polygonNormalRelation_trans word hm ih1 ih2

lemma polygonRelation_iff_normalForm {n : ℕ} (word : Word n)
    (hm : 0 < word.length)
    (hvertices : ∀ (i j : Fin word.length), polygonProjection word (sidePoint word.length i.val 0) =
      polygonProjection word (sidePoint word.length j.val 0))
    (x y : ClosedDisk) : (polygonSetoid word).r x y ↔ polygonNormalRelation word x y := by
  refine ⟨polygonRelation_normalForm word hm, ?_⟩
  rintro (rfl | h | ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩)
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ h
  · exact Quotient.exact (hvertices i j)

lemma polygonSetoid_isClosed_of_vertices_identified {n : ℕ} (word : Word n)
    (hm : 0 < word.length)
    (hvertices : ∀ (i j : Fin word.length), polygonProjection word (sidePoint word.length i.val 0) =
      polygonProjection word (sidePoint word.length j.val 0)) :
    IsClosed {p : ClosedDisk × ClosedDisk | (polygonSetoid word).r p.1 p.2} := by
  have he : {p : ClosedDisk × ClosedDisk | (polygonSetoid word).r p.1 p.2} =
      {p | p.1 = p.2} ∪ {p | sideRelation word p.1 p.2} ∪
      (polygonVertices word.length ×ˢ polygonVertices word.length) := by
    ext p
    rw [mem_ofPred, polygonRelation_iff_normalForm word hm hvertices]
    simp only [polygonNormalRelation, mem_union, mem_ofPred, mem_prod]
    tauto
  rw [he]
  exact (isClosed_eq continuous_fst continuous_snd).union (sideRelation_isClosed word)
    |>.union ((polygonVertices_isClosed _).prod (polygonVertices_isClosed _))

lemma polygon_t2_of_vertices_identified {n : ℕ} (word : Word n)
    (hm : 0 < word.length)
    (hvertices : ∀ (i j : Fin word.length), polygonProjection word (sidePoint word.length i.val 0) =
      polygonProjection word (sidePoint word.length j.val 0)) : T2Space (PolygonSurface word) :=
  quotient_t2_of_closed_relation (polygonSetoid word)
    (polygonSetoid_isClosed_of_vertices_identified word hm hvertices)



lemma sidePoint_surjective_boundary (m : ℕ) (hm : 0 < m) (x : ClosedDisk)
    (hx : ‖x.val‖ = 1) : ∃ (i : Fin m) (t : unitInterval),
      x = sidePoint m i.val t.val := by
  let z : Circle := ⟨x.val, mem_sphere_zero_iff_norm.mpr hx⟩
  obtain ⟨a, ha⟩ := Circle.exp_surjective z
  obtain ⟨b, hb, hab⟩ := Circle.periodic_exp.exists_mem_Ico₀
    (by positivity : (0 : ℝ) < 2*Real.pi) a
  have hbz : Circle.exp b = z := hab.symm.trans ha
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let r : ℝ := m*b/(2*Real.pi)
  have hr0 : 0 ≤ r := div_nonneg (mul_nonneg (le_of_lt hmR) hb.1) (by positivity)
  have hrm : r < m := by
    dsimp [r]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2*Real.pi)).2
    nlinarith [hb.2]
  have hir : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr0
  have hri : r < (⌊r⌋₊ : ℝ)+1 := Nat.lt_floor_add_one r
  have him : ⌊r⌋₊ < m := by exact_mod_cast (hir.trans_lt hrm)
  refine ⟨⟨⌊r⌋₊,him⟩,⟨r-⌊r⌋₊,⟨by linarith,by linarith⟩⟩,?_⟩
  apply Subtype.ext
  change x.val = (Circle.exp (2 * Real.pi * ((⌊r⌋₊ : ℝ) + (r-⌊r⌋₊)) / (m : ℝ)) : ℂ)
  have he : 2 * Real.pi * ((⌊r⌋₊ : ℝ) + (r-⌊r⌋₊)) / (m : ℝ) = b := by
    dsimp [r]
    field_simp
    ring
  rw [he]
  exact congrArg (fun u : Circle => (u : ℂ)) hbz.symm

lemma orientedSideParameter_interior_iff (b : Bool) (t : unitInterval) :
    (orientedSideParameter b t).val ∈ Set.Ioo (0 : ℝ) 1 ↔
      t.val ∈ Set.Ioo (0 : ℝ) 1 := by
  cases b <;> simp only [orientedSideParameter_val, Bool.false_eq_true, ↓reduceIte]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

lemma sidePoint_interior_eq_closed (m : ℕ) (hm : 0 < m)
    (i j : Fin m) {t s : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (he : sidePoint m i.val t = sidePoint m j.val s) : i = j ∧ t = s := by
  have hn : ¬ (s = 0 ∨ s = 1) := by
    intro h
    exact sidePoint_interior_not_vertex m hm i ht
      (he ▸ (sidePoint_vertex_iff m hm j hs).mpr h)
  have hs' : s ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm (fun h => hn (Or.inl h))),
      lt_of_le_of_ne hs.2 (fun h => hn (Or.inr h))⟩
  exact sidePoint_interior_injective m hm i j ht hs' he

/-- A side chart with the orientation specified by the actual word. -/
def orientedSidePoint {n : ℕ} (word : Word n) (i : Fin word.length)
    (t : unitInterval) : ClosedDisk :=
  sidePoint word.length i.val (orientedSideParameter (word.get i).2 t).val

lemma orientedSidePoint_interior_not_vertex {n : ℕ} (word : Word n)
    (hm : 0 < word.length) (i : Fin word.length) (t : unitInterval)
    (ht : t.val ∈ Set.Ioo (0 : ℝ) 1) :
    orientedSidePoint word i t ∉ polygonVertices word.length :=
  sidePoint_interior_not_vertex _ hm i ((orientedSideParameter_interior_iff _ _).mpr ht)

lemma orientedSidePoint_interior_eq_closed {n : ℕ} (word : Word n)
    (hm : 0 < word.length) (i j : Fin word.length) (t s : unitInterval)
    (ht : t.val ∈ Set.Ioo (0 : ℝ) 1)
    (he : orientedSidePoint word i t = orientedSidePoint word j s) : i = j ∧ t = s := by
  obtain ⟨hij,hp⟩ := sidePoint_interior_eq_closed word.length hm i j
    ((orientedSideParameter_interior_iff _ _).mpr ht)
    (orientedSideParameter (word.get j).2 s).property he
  subst j
  exact ⟨rfl,orientedSideParameter_injective (word.get i).2 (Subtype.ext hp)⟩

lemma polygonProjection_orientedSide_eq_iff {n : ℕ} (word : Word n)
    (hm : 0 < word.length) (i j : Fin word.length) (t s : unitInterval)
    (ht : t.val ∈ Set.Ioo (0 : ℝ) 1) (hs : s.val ∈ Set.Ioo (0 : ℝ) 1) :
    polygonProjection word (orientedSidePoint word i t) =
      polygonProjection word (orientedSidePoint word j s) ↔
        (word.get i).1 = (word.get j).1 ∧ t = s := by
  constructor
  · intro h
    have hn := orientedSidePoint_interior_not_vertex word hm i t ht
    rcases polygonRelation_normalForm word hm (Quotient.exact h) with he | hr | hv
    · obtain ⟨rfl,rfl⟩ := orientedSidePoint_interior_eq_closed word hm i j t s ht he
      exact ⟨rfl,rfl⟩
    · rcases hr with ⟨hw,_,_⟩ | ⟨k,l,u,hkl,hx,hy⟩
      · simp [hw] at hm
      · have hx' : orientedSidePoint word i t = orientedSidePoint word k u := by
          simpa only [orientedSidePoint,orientedSideParameter_val] using hx
        have hy' : orientedSidePoint word j s = orientedSidePoint word l u := by
          simpa only [orientedSidePoint,orientedSideParameter_val] using hy
        obtain ⟨rfl, htu⟩ := orientedSidePoint_interior_eq_closed word hm i k t u ht hx'
        obtain ⟨rfl, hsu⟩ := orientedSidePoint_interior_eq_closed word hm j l s u hs hy'
        exact ⟨hkl,htu.trans hsu.symm⟩
    · exact (hn hv.1).elim
  · rintro ⟨hij,rfl⟩
    simpa only [orientedSidePoint, orientedSideParameter_val] using polygonSides_identified word i j hij t

lemma orientedSidePoint_continuous {n : ℕ} (word : Word n) (i : Fin word.length) :
    Continuous (orientedSidePoint word i) := by
  unfold orientedSidePoint
  apply (sidePoint_continuous _ _).comp
  simp only [orientedSideParameter_val]
  split_ifs <;> fun_prop

lemma polygonProjection_orientedSide_ne_vertex {n : ℕ} (word : Word n)
    (hm : 0 < word.length) (i j : Fin word.length) (t : unitInterval)
    (ht : t.val ∈ Set.Ioo (0 : ℝ) 1) :
    polygonProjection word (orientedSidePoint word i t) ≠
      polygonProjection word (sidePoint word.length j.val 0) := by
  intro h
  have hn := orientedSidePoint_interior_not_vertex word hm i t ht
  have hv := sidePoint_mem_vertices_zero word.length j
  rcases polygonRelation_normalForm word hm (Quotient.exact h) with he | hr | hh
  · exact hn (he ▸ hv)
  · exact hn ((sideRelation_vertex_iff word hm hr).mpr hv)
  · exact hn hh.1

/-- A compact interval loop that is injective away from its two endpoints
embeds its open interval in a Hausdorff target. -/
lemma intervalLoop_interior_isEmbedding {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : C(unitInterval,X)) (v : X) (h₀ : f 0 = v) (h₁ : f 1 = v)
    (hn : ∀ t : unitInterval, t.val ∈ Set.Ioo (0 : ℝ) 1 → f t ≠ v)
    (hi : Set.InjOn f {t : unitInterval | t.val ∈ Set.Ioo (0 : ℝ) 1}) :
    Topology.IsEmbedding (fun t : {t : unitInterval // t.val ∈ Set.Ioo (0 : ℝ) 1} => f t.val) := by
  let s : Set X := {v}ᶜ
  let g := s.restrictPreimage f
  have he : {t : unitInterval | t.val ∈ Set.Ioo (0 : ℝ) 1} = f ⁻¹' s := by
    ext t
    constructor
    · intro ht
      exact hn t ht
    · intro ht
      have ht0 : t.val ≠ 0 := by
        intro h
        have h' : t = 0 := Subtype.ext h
        exact ht (h' ▸ h₀)
      have ht1 : t.val ≠ 1 := by
        intro h
        have h' : t = 1 := Subtype.ext h
        exact ht (h' ▸ h₁)
      exact ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
        lt_of_le_of_ne t.property.2 ht1⟩
  have hg : Topology.IsClosedEmbedding g := by
    apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    · exact f.continuous.restrictPreimage
    · intro x y h
      apply Subtype.ext
      apply hi
      · exact he.symm ▸ x.property
      · exact he.symm ▸ y.property
      · exact congrArg Subtype.val h
    · exact f.continuous.isClosedMap.restrictPreimage s
  let e := Homeomorph.setCongr he
  exact Topology.IsEmbedding.subtypeVal.comp (hg.isEmbedding.comp e.isEmbedding)

lemma polygon_openSide_isEmbedding {n : ℕ} (word : Word n)
    (hm : 0 < word.length)
    (hvertices : ∀ (i j : Fin word.length), polygonProjection word (sidePoint word.length i.val 0) =
      polygonProjection word (sidePoint word.length j.val 0))
    (i : Fin word.length) :
    Topology.IsEmbedding
      (fun t : {t : unitInterval // t.val ∈ Set.Ioo (0 : ℝ) 1} =>
        polygonProjection word (orientedSidePoint word i t.val)) := by
  letI := polygon_t2_of_vertices_identified word hm hvertices
  let f : C(unitInterval,PolygonSurface word) :=
    ⟨fun t => polygonProjection word (orientedSidePoint word i t),
      (polygonProjection word).continuous.comp (orientedSidePoint_continuous word i)⟩
  let v := polygonProjection word (sidePoint word.length 0 0)
  have hv (t : unitInterval) (ht : t.val = 0 ∨ t.val = 1) : f t = v := by
    have hmem : orientedSidePoint word i t ∈ polygonVertices word.length := by
      apply (sidePoint_vertex_iff _ hm i (orientedSideParameter _ t).property).mpr
      exact (orientedSideParameter_endpoint _ _).mpr ht
    obtain ⟨j,hj⟩ := hmem
    change polygonProjection word (orientedSidePoint word i t) = v
    rw [← hj]
    exact hvertices j ⟨0,hm⟩
  apply intervalLoop_interior_isEmbedding f v (hv 0 (Or.inl rfl)) (hv 1 (Or.inr rfl))
  · intro t ht
    exact polygonProjection_orientedSide_ne_vertex word hm i ⟨0,hm⟩ t ht
  · intro t ht s hs h
    exact ((polygonProjection_orientedSide_eq_iff word hm i i t s ht hs).mp h).2



namespace CircleChains
open P202Specs.CellularDegrees P202Specs.SpheresDisks Opposite
open scoped Simplicial

/-- Convex interpolation of two interval parameters. -/
def interpolate (a b t : unitInterval) : unitInterval :=
  ⟨(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ), by
    have ha₀ := a.property.1
    have ha₁ := a.property.2
    have hb₀ := b.property.1
    have hb₁ := b.property.2
    have ht₀ := t.property.1
    have ht₁ := t.property.2
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht₁) ha₀) (mul_nonneg ht₀ hb₀)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht₁) (sub_nonneg.mpr ha₁),
        mul_nonneg ht₀ (sub_nonneg.mpr hb₁)]⟩

lemma interpolate_continuous (a b : unitInterval) : Continuous (interpolate a b) := by
  exact (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)).subtype_mk _

@[simp] lemma interpolate_zero (a b : unitInterval) : interpolate a b 0 = a := by
  apply Subtype.ext
  simp [interpolate]

@[simp] lemma interpolate_one (a b : unitInterval) : interpolate a b 1 = b := by
  apply Subtype.ext
  simp [interpolate]

def segment (L : C(unitInterval, Circle)) (a b : unitInterval) : C(unitInterval, Circle) :=
  ⟨fun t => L (interpolate a b t), L.continuous.comp (interpolate_continuous a b)⟩

@[simp] lemma segment_zero (L : C(unitInterval, Circle)) (a b : unitInterval) :
    segment L a b 0 = L a := by simp [segment]

@[simp] lemma segment_one (L : C(unitInterval, Circle)) (a b : unitInterval) :
    segment L a b 1 = L b := by simp [segment]

lemma segment_zero_one (L : C(unitInterval, Circle)) : segment L 0 1 = L := by
  apply ContinuousMap.ext
  intro t
  change L (interpolate 0 1 t) = L t
  congr 1
  apply Subtype.ext
  simp [interpolate]

/-- An affine triangle in the interval with ordered vertex parameters a,b,c. -/
def triangleParameter (a b c : unitInterval) (x : Triangle) : unitInterval :=
  ⟨x.weights 0 * (a : ℝ) + x.weights 1 * (b : ℝ) + x.weights 2 * (c : ℝ), by
    have ha₀ := a.property.1
    have ha₁ := a.property.2
    have hb₀ := b.property.1
    have hb₁ := b.property.2
    have hc₀ := c.property.1
    have hc₁ := c.property.2
    have h₀ := x.nonneg 0
    have h₁ := x.nonneg 1
    have h₂ := x.nonneg 2
    have hs : x.weights 0 + x.weights 1 + x.weights 2 = 1 := by
      have ht := x.total
      rw [Finsupp.sum_fintype _ _ (by simp)] at ht
      simpa only [Fin.sum_univ_three] using ht
    constructor
    · exact add_nonneg (add_nonneg (mul_nonneg h₀ ha₀) (mul_nonneg h₁ hb₀))
        (mul_nonneg h₂ hc₀)
    · nlinarith [mul_nonneg h₀ (sub_nonneg.mpr ha₁),
        mul_nonneg h₁ (sub_nonneg.mpr hb₁),
        mul_nonneg h₂ (sub_nonneg.mpr hc₁)]⟩

lemma triangleParameter_continuous (a b c : unitInterval) :
    Continuous (triangleParameter a b c) := by
  exact ((((Convexity.StdSimplex.continuous_weights_apply ℝ 0).mul continuous_const).add
    ((Convexity.StdSimplex.continuous_weights_apply ℝ 1).mul continuous_const)).add
    ((Convexity.StdSimplex.continuous_weights_apply ℝ 2).mul continuous_const)).subtype_mk _

lemma triangleParameter_face0 (a b c : unitInterval) (x : Interval) :
    triangleParameter a b c (faceInclusion 0 x) = interpolate b c (intervalParameter x) := by
  apply Subtype.ext
  change (faceInclusion 0 x).weights 0 * _ + (faceInclusion 0 x).weights 1 * _ +
    (faceInclusion 0 x).weights 2 * _ = _
  have h₁ := face_weight_succ x 0 0
  have h₂ := face_weight_succ x 0 1
  norm_num at h₁ h₂
  rw [face_weight_zero, h₁, h₂]
  have ht := x.total_fin_two
  dsimp [interpolate, intervalParameter]
  rw [show x.weights 0 = 1 - x.weights 1 by linarith]
  ring

lemma triangleParameter_face1 (a b c : unitInterval) (x : Interval) :
    triangleParameter a b c (faceInclusion 1 x) = interpolate a c (intervalParameter x) := by
  apply Subtype.ext
  change (faceInclusion 1 x).weights 0 * _ + (faceInclusion 1 x).weights 1 * _ +
    (faceInclusion 1 x).weights 2 * _ = _
  have h₀ := face_weight_succ x 1 0
  have h₂ := face_weight_succ x 1 1
  norm_num at h₀ h₂
  rw [face_weight_zero, h₀, h₂]
  have ht := x.total_fin_two
  dsimp [interpolate, intervalParameter]
  rw [show x.weights 0 = 1 - x.weights 1 by linarith]
  ring

lemma triangleParameter_face2 (a b c : unitInterval) (x : Interval) :
    triangleParameter a b c (faceInclusion 2 x) = interpolate a b (intervalParameter x) := by
  apply Subtype.ext
  change (faceInclusion 2 x).weights 0 * _ + (faceInclusion 2 x).weights 1 * _ +
    (faceInclusion 2 x).weights 2 * _ = _
  have h₀ := face_weight_succ x 2 0
  have h₁ := face_weight_succ x 2 1
  change (faceInclusion 2 x).weights 1 = x.weights 1 at h₁
  norm_num at h₀
  rw [face_weight_zero, h₀, h₁]
  have ht := x.total_fin_two
  dsimp [interpolate, intervalParameter]
  rw [show x.weights 0 = 1 - x.weights 1 by linarith]
  ring

def subdivisionTriangle (L : C(unitInterval, Circle)) (a b c : unitInterval) :
    Simplex (TopCat.of Circle) 2 :=
  (simplexEquiv _ 2).symm ⟨fun x => L (triangleParameter a b c x),
    L.continuous.comp (triangleParameter_continuous a b c)⟩

lemma subdivisionTriangle_face0 (L : C(unitInterval, Circle)) (a b c : unitInterval) :
    face 0 (subdivisionTriangle L a b c) = loopSimplex (segment L b c) := by
  apply (simplexEquiv _ 1).injective
  rw [P202.SingularChains.simplexEquiv_face]
  apply ContinuousMap.ext
  intro x
  simp only [subdivisionTriangle, Equiv.apply_symm_apply, ContinuousMap.comp_apply, loopSimplex]
  change L (triangleParameter a b c (faceInclusion 0 x)) =
    L (interpolate b c (intervalParameter x))
  rw [triangleParameter_face0]

lemma subdivisionTriangle_face1 (L : C(unitInterval, Circle)) (a b c : unitInterval) :
    face 1 (subdivisionTriangle L a b c) = loopSimplex (segment L a c) := by
  apply (simplexEquiv _ 1).injective
  rw [P202.SingularChains.simplexEquiv_face]
  apply ContinuousMap.ext
  intro x
  simp only [subdivisionTriangle, Equiv.apply_symm_apply, ContinuousMap.comp_apply, loopSimplex]
  change L (triangleParameter a b c (faceInclusion 1 x)) =
    L (interpolate a c (intervalParameter x))
  rw [triangleParameter_face1]

lemma subdivisionTriangle_face2 (L : C(unitInterval, Circle)) (a b c : unitInterval) :
    face 2 (subdivisionTriangle L a b c) = loopSimplex (segment L a b) := by
  apply (simplexEquiv _ 1).injective
  rw [P202.SingularChains.simplexEquiv_face]
  apply ContinuousMap.ext
  intro x
  simp only [subdivisionTriangle, Equiv.apply_symm_apply, ContinuousMap.comp_apply, loopSimplex]
  change L (triangleParameter a b c (faceInclusion 2 x)) =
    L (interpolate a b (intervalParameter x))
  rw [triangleParameter_face2]

lemma subdivision_boundary (L : C(unitInterval, Circle)) (a b c : unitInterval) :
    boundary ℤ ℤ (TopCat.of Circle) 1 (Finsupp.single (subdivisionTriangle L a b c) (1:ℤ)) =
      Finsupp.single (loopSimplex (segment L b c)) (1:ℤ) -
        Finsupp.single (loopSimplex (segment L a c)) (1:ℤ) +
          Finsupp.single (loopSimplex (segment L a b)) (1:ℤ) := by
  rw [P202.SingularChains.boundary_single]
  change (∑ i : Fin 3, (-1:ℤ)^i.val •
    Finsupp.single (face i (subdivisionTriangle L a b c)) (1:ℤ)) = _
  simp only [Fin.sum_univ_three, Fin.val_zero, pow_zero, one_smul,
    Fin.val_one, pow_one, neg_smul, subdivisionTriangle_face0,
    subdivisionTriangle_face1, subdivisionTriangle_face2, sub_eq_add_neg]
  norm_num

def ordinarySubdivisionChain (L : C(unitInterval, Circle)) (a b c : unitInterval) :
    (ordinaryComplex ℤ ℤ (TopCat.of Circle)).X 2 :=
  simplexChainZ ℤ ℤ (TopCat.of Circle) 2 (subdivisionTriangle L a b c) 1

lemma ordinary_subdivision_boundary (L : C(unitInterval, Circle)) (a b c : unitInterval) :
    (ordinaryComplex ℤ ℤ (TopCat.of Circle)).d 2 1 (ordinarySubdivisionChain L a b c) =
      ordinaryLoopChain (segment L b c) - ordinaryLoopChain (segment L a c) +
        ordinaryLoopChain (segment L a b) := by
  apply (ordinaryNonnegativeIso ℤ ℤ (TopCat.of Circle) 1).toLinearEquiv.injective
  have ht := congrArg (fun f => f (Finsupp.single (subdivisionTriangle L a b c) (1:ℤ)))
    (P202.SingularChains.ordinary_boundary ℤ ℤ (TopCat.of Circle) 1)
  change (ordinaryNonnegativeIso ℤ ℤ (TopCat.of Circle) 1).hom
      ((ordinaryComplex ℤ ℤ (TopCat.of Circle)).d 2 1
        ((ordinaryNonnegativeIso ℤ ℤ (TopCat.of Circle) 2).inv
          (Finsupp.single (subdivisionTriangle L a b c) (1:ℤ)))) = _ at ht
  change (ordinaryNonnegativeIso ℤ ℤ (TopCat.of Circle) 1).hom _ = _
  simp only [ordinarySubdivisionChain, ordinaryLoopChain, simplexChainZ, map_add, map_sub,
    Iso.toLinearEquiv_apply, Iso.inv_hom_id_apply]
  exact ht.trans (subdivision_boundary L a b c)

/-- The integral singular class of a based loop. -/
def loopClass (L : C(unitInterval, Circle)) (h₀ : L 0 = 1) (h₁ : L 1 = 1) :
    homology ℤ ℤ (TopCat.of Circle) 1 :=
  classOf ℤ (ordinaryComplex ℤ ℤ (TopCat.of Circle)) 1 (ordinaryLoopChain L)
    (ordinaryLoopChain_cycle L h₀ h₁)

/-- Three parameters at the basepoint give the path subdivision formula. -/
lemma segment_homology_add (L : C(unitInterval, Circle)) (a b c : unitInterval)
    (ha : L a = 1) (hb : L b = 1) (hc : L c = 1) :
    loopClass (segment L a c) (by simpa using ha) (by simpa using hc) =
      loopClass (segment L a b) (by simpa using ha) (by simpa using hb) +
        loopClass (segment L b c) (by simpa using hb) (by simpa using hc) := by
  let K := ordinaryComplex ℤ ℤ (TopCat.of Circle)
  have hab := ordinaryLoopChain_cycle (segment L a b) (by simpa using ha) (by simpa using hb)
  have hbc := ordinaryLoopChain_cycle (segment L b c) (by simpa using hb) (by simpa using hc)
  have hac := ordinaryLoopChain_cycle (segment L a c) (by simpa using ha) (by simpa using hc)
  have he := classOf_eq_of_boundary K 1 (ordinaryLoopChain (segment L a c))
    (ordinaryLoopChain (segment L a b) + ordinaryLoopChain (segment L b c)) hac
    (by change K.d 1 0 _ = _; change K.d 1 0 _ = _ at hab hbc
        rw [map_add, hab, hbc, add_zero]) (-ordinarySubdivisionChain L a b c) (by
      have ht := ordinary_subdivision_boundary L a b c
      change K.d (1+1) 1 (ordinarySubdivisionChain L a b c) = _ at ht
      rw [map_neg, ht]
      abel)
  exact he.trans (classOf_add K 1 _ _ hab hbc)

/-- A loop with constant parameter has zero class, by a constant 2-simplex. -/
lemma segment_self_homology (L : C(unitInterval, Circle)) (a : unitInterval)
    (ha : L a = 1) :
    loopClass (segment L a a) (by simpa using ha) (by simpa using ha) = 0 := by
  have h := segment_homology_add L a a a ha ha ha
  have he : loopClass (segment L a a) (by simpa using ha) (by simpa using ha) +
      loopClass (segment L a a) (by simpa using ha) (by simpa using ha) =
      loopClass (segment L a a) (by simpa using ha) (by simpa using ha) + 0 := by
    simpa using h.symm
  exact add_left_cancel he

/-- Reversing an oriented segment negates its homology class. -/
lemma segment_homology_reverse (L : C(unitInterval, Circle)) (a b : unitInterval)
    (ha : L a = 1) (hb : L b = 1) :
    loopClass (segment L b a) (by simpa using hb) (by simpa using ha) =
      -loopClass (segment L a b) (by simpa using ha) (by simpa using hb) := by
  have h := segment_homology_add L a b a ha hb ha
  rw [segment_self_homology L a ha] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Subdivide a circle path at any finite sequence of visits to its basepoint.
The sequence need not be increasing: orientation is retained by each segment. -/
lemma segment_homology_sum (L : C(unitInterval, Circle)) (t : ℕ → unitInterval)
    (ht : ∀ i, L (t i) = 1) (m : ℕ) :
    loopClass (segment L (t 0) (t m)) (by simpa using ht 0) (by simpa using ht m) =
      ∑ i ∈ Finset.range m,
        loopClass (segment L (t i) (t (i+1)))
          (by simpa using ht i) (by simpa using ht (i+1)) := by
  induction m with
  | zero => simp [segment_self_homology L (t 0) (ht 0)]
  | succ m ih =>
    rw [segment_homology_add L (t 0) (t m) (t (m+1)) (ht 0) (ht m) (ht (m+1)), ih,
      Finset.sum_range_succ]

/-- Recover the original loop from the first and last subdivision parameters. -/
lemma loop_homology_sum (L : C(unitInterval, Circle)) (t : ℕ → unitInterval)
    (ht : ∀ i, L (t i) = 1) (m : ℕ) (h₀ : t 0 = 0) (h₁ : t m = 1) :
    loopClass L (by simpa [h₀] using ht 0) (by simpa [h₁] using ht m) =
      ∑ i ∈ Finset.range m,
        loopClass (segment L (t i) (t (i+1)))
          (by simpa using ht i) (by simpa using ht (i+1)) := by
  have h := segment_homology_sum L t ht m
  simpa only [h₀, h₁, segment_zero_one] using h

/-- A signed traversal of a reference loop, including a collapsed traversal. -/
def signedLoop (G : C(unitInterval, Circle)) (s : ℤ) : C(unitInterval, Circle) :=
  if s = 1 then G else if s = -1 then segment G 1 0 else segment G 0 0

lemma signedLoop_zero (G : C(unitInterval, Circle)) (h₀ : G 0 = 1)
    (h₁ : G 1 = 1) (s : ℤ) : signedLoop G s 0 = 1 := by
  unfold signedLoop
  split_ifs <;> simp_all

lemma signedLoop_one (G : C(unitInterval, Circle)) (h₀ : G 0 = 1)
    (h₁ : G 1 = 1) (s : ℤ) : signedLoop G s 1 = 1 := by
  unfold signedLoop
  split_ifs <;> simp_all

lemma signedLoop_class (G : C(unitInterval, Circle)) (h₀ : G 0 = 1)
    (h₁ : G 1 = 1) (s : ℤ) (hs : s = 1 ∨ s = -1 ∨ s = 0) :
    loopClass (signedLoop G s) (signedLoop_zero G h₀ h₁ s) (signedLoop_one G h₀ h₁ s) =
      s • loopClass G h₀ h₁ := by
  rcases hs with rfl | rfl | rfl
  · simp [signedLoop]
  · have h := segment_homology_reverse G 0 1 h₀ h₁
    simpa [signedLoop, segment_zero_one] using h
  · simpa [signedLoop] using segment_self_homology G 0 h₀

/-- Finite signed arcs act on the actual reference loop class by the sum of signs. -/
lemma signed_arc_homology (G L : C(unitInterval, Circle))
    (hG₀ : G 0 = 1) (hG₁ : G 1 = 1)
    (t : ℕ → unitInterval) (ht : ∀ i, L (t i) = 1) (m : ℕ)
    (h₀ : t 0 = 0) (h₁ : t m = 1) (s : ℕ → ℤ)
    (hs : ∀ i < m, s i = 1 ∨ s i = -1 ∨ s i = 0)
    (hArc : ∀ i < m, segment L (t i) (t (i+1)) = signedLoop G (s i)) :
    loopClass L (by simpa [h₀] using ht 0) (by simpa [h₁] using ht m) =
      (∑ i ∈ Finset.range m, s i) • loopClass G hG₀ hG₁ := by
  rw [loop_homology_sum L t ht m h₀ h₁]
  calc
    _ = ∑ i ∈ Finset.range m, s i • loopClass G hG₀ hG₁ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hilt := Finset.mem_range.mp hi
      have hc := signedLoop_class G hG₀ hG₁ (s i) (hs i hilt)
      simpa only [hArc i hilt] using hc
    _ = _ := by
      clear h₁ hs hArc
      induction m with
      | zero => simp
      | succ m ih =>
        simp only [Finset.sum_range_succ, add_zsmul]
        rw [ih]

/-- Naturality identifies the class of a postcomposed based loop. -/
lemma loopClass_natural (f : TopCat.of Circle ⟶ TopCat.of Circle)
    (hf : f 1 = 1) (G : C(unitInterval, Circle)) (h₀ : G 0 = 1) (h₁ : G 1 = 1) :
    (homologyFunctor ℤ ℤ 1).map f (loopClass G h₀ h₁) =
      loopClass (f.hom.comp G) (by simp [h₀, hf]) (by simp [h₁, hf]) := by
  let F := (ordinaryFunctor ℤ ℤ).map f
  have hz := ordinaryLoopChain_cycle G h₀ h₁
  have hz' := ordinaryLoopChain_cycle (f.hom.comp G) (by simp [h₀, hf]) (by simp [h₁, hf])
  have he : F.f 1 (ordinaryLoopChain G) = ordinaryLoopChain (f.hom.comp G) := by
    have hm := P202.Homology.CellularDegrees.simplexChainZ_map ℤ ℤ f 1 (loopSimplex G) 1
    change F.f 1 (ordinaryLoopChain G) = _ at hm
    rw [hm]
    congr 1
  change homologyMap F 1 _ = _
  exact P202.Homology.CellularDegrees.homologyMap_classOf ℤ F 1 _ hz
    (by change (ordinaryComplex ℤ ℤ (TopCat.of Circle)).d 1 0 _ = _
        rw [he]; exact hz') |>.trans
    (P202.SpheresDisks.SimplexOrientation.classOf_congr ℤ _ 1 _ _ _ _ he)

open P202Specs.SurfaceHomology

/-- The signed occurrence of edge e at word position i, extended by zero. -/
def wordSign {n : ℕ} (w : Word n) (e : Fin n) (i : ℕ) : ℤ :=
  if hi : i < w.length then
    if (w.get ⟨i, hi⟩).1 = e then (if (w.get ⟨i, hi⟩).2 then 1 else -1) else 0
  else 0

lemma wordSign_cases {n : ℕ} (w : Word n) (e : Fin n) (i : ℕ) :
    wordSign w e i = 1 ∨ wordSign w e i = -1 ∨ wordSign w e i = 0 := by
  classical
  unfold wordSign
  split_ifs <;> simp_all

lemma wordSign_sum {n : ℕ} (w : Word n) (e : Fin n) :
    (∑ i ∈ Finset.range w.length, wordSign w e i) = exponentSum w e := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  have h := List.sum_ofFn (f := fun i : Fin w.length =>
    if (w.get i).1 = e then (if (w.get i).2 then (1:ℤ) else -1) else 0)
  have he : List.ofFn (fun i : Fin w.length =>
      if (w.get i).1 = e then (if (w.get i).2 then (1:ℤ) else -1) else 0) =
        w.map (fun l => if l.1 = e then (if l.2 then (1:ℤ) else -1) else 0) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map (fun l : Fin n × Bool =>
        if l.1 = e then (if l.2 then (1:ℤ) else -1) else 0)) (List.ofFn_get w)
  rw [he] at h
  simpa [wordSign, exponentSum] using h.symm

/-- The exponent sum is the actual homology action whenever the boundary map
has the specified signed traversal on every arc. -/
lemma word_arc_homology {n : ℕ} (w : Word n) (e : Fin n)
    (G L : C(unitInterval, Circle)) (hG₀ : G 0 = 1) (hG₁ : G 1 = 1)
    (t : ℕ → unitInterval) (ht : ∀ i, L (t i) = 1)
    (h₀ : t 0 = 0) (h₁ : t w.length = 1)
    (hArc : ∀ i < w.length, segment L (t i) (t (i+1)) = signedLoop G (wordSign w e i)) :
    loopClass L (by simpa [h₀] using ht 0) (by simpa [h₁] using ht w.length) =
      exponentSum w e • loopClass G hG₀ hG₁ := by
  simpa only [wordSign_sum] using signed_arc_homology G L hG₀ hG₁ t ht w.length h₀ h₁
    (wordSign w e) (fun i _ => wordSign_cases w e i) hArc

/-- The counterclockwise once-around reference loop. -/
def exponentialLoop : C(unitInterval, Circle) :=
  ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩

@[simp] lemma exponentialLoop_zero : exponentialLoop 0 = 1 := by
  simp [exponentialLoop]

@[simp] lemma exponentialLoop_one : exponentialLoop 1 = 1 := by
  simp [exponentialLoop, Circle.exp_two_pi]

/-- In any integral coordinate, a nonzero class detects its integer scalar. -/
lemma scalar_eq_of_nonzero_loop
    (e : homology ℤ ℤ (TopCat.of Circle) 1 ≃ₗ[ℤ] ℤ)
    (G : C(unitInterval, Circle)) (h₀ : G 0 = 1) (h₁ : G 1 = 1)
    (hG : loopClass G h₀ h₁ ≠ 0) (a b : ℤ)
    (hab : a • loopClass G h₀ h₁ = b • loopClass G h₀ h₁) : a = b := by
  have hx : e (loopClass G h₀ h₁) ≠ 0 := by
    intro hx
    exact hG (e.injective (hx.trans (map_zero e).symm))
  have h := congrArg e hab
  simp only [map_zsmul, zsmul_eq_mul] at h
  exact mul_right_cancel₀ hx h

/-- A nonzero reference loop converts its computed homology action to degree. -/
lemma degree_eq_of_loop_action
    (h : P202Specs.SpheresDisks.sphere 1 ≃ₜ TopCat.of Circle)
    (e : homology ℤ ℤ (TopCat.of Circle) 1 ≃ₗ[ℤ] ℤ)
    (f : TopCat.of Circle ⟶ TopCat.of Circle)
    (G : C(unitInterval, Circle)) (h₀ : G 0 = 1) (h₁ : G 1 = 1)
    (hG : loopClass G h₀ h₁ ≠ 0) (d : ℤ)
    (hd : (homologyFunctor ℤ ℤ 1).map f (loopClass G h₀ h₁) = d • loopClass G h₀ h₁) :
    P202Specs.Degree.degree 1
      (P202.Homology.CellularDegrees.CoefficientAction.conjugateSelfMap h f) = d := by
  have ha := P202.Homology.CellularDegrees.CoefficientAction.homeomorphic_sphere_action
    ℤ ℤ 1 (by decide) h f (loopClass G h₀ h₁)
  exact scalar_eq_of_nonzero_loop e G h₀ h₁ hG _ d (ha.symm.trans hd)


end CircleChains

namespace AttachingBridge
open P202Specs.RelativeSingularChains P202Specs.CellularDegrees
open P202Specs.SpheresDisks P202Specs.GoodPairQuotient
open P202.Homology.CellularDegrees.AttachingCalculation

/-- With fixed source and target charts, all target edges use one reference
orientation and the face uses the corresponding common source orientation.
Only the degrees of the actual selected-cell collapse maps remain to compute. -/
lemma polygonDifferentials_of_attachingDegrees {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)]
    (hc : PolygonCellCounts (PolygonSurface word) e)
    (charts : PolygonCharts word) (coefficient : ℤ)
    (b : (referenceDiskPair.{0} 1).sub)
    (hS : (referenceDiskPair.{0} 2).sub ≃ₜ liftedSphere.{0} 1)
    (hT : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ liftedSphere.{0} 1)
    (s : ℤ ≃ₗ[ℤ] homology ℤ ℤ (liftedSphere.{0} 1) 1)
    (hd : ∀ i : Fin e, ∃ q : skeletalPair (PolygonSurface word) 1 ⟶
      quotientPair (referenceDiskPair.{0} 1),
      SelectedCellCollapse (PolygonSurface word) 1 (charts.edges i) b q ∧
      P202Specs.Degree.degree 1
        (chartAttachingMap (PolygonSurface word) 1 hS hT q charts.face) = coefficient) :
    PolygonDifferentials word charts coefficient := by
  classical
  let g₁ := targetChartOrientation ℤ ℤ 1 (by omega) b hT s
  let g₂ := sourceChartOrientation ℤ ℤ 1 (by omega) hS s
  obtain ⟨a, ha⟩ := P202.Homology.cellularOrientedCoordinates
    (PolygonSurface word) ℤ ℤ 1 g₁
  let c₁ : chainGroup (PolygonSurface word) ℤ ℤ 1 ≃ₗ[ℤ] (Fin e → ℤ) :=
    (a.trans (Finsupp.domLCongr charts.edges.symm)).trans
      (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin e))
  have hc₁ (z : chainGroup (PolygonSurface word) ℤ ℤ 1) (i : Fin e) :
      c₁ z i = a z (charts.edges i) := by
    rfl
  apply P202.Homology.SurfaceHomology.polygonDifferentials_of_unitColumn
    word hc charts coefficient g₁ g₂ c₁
  · intro i z
    change Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin e)
      ((Finsupp.domLCongr charts.edges.symm :
        (Cell (PolygonSurface word) 1 →₀ ℤ) ≃ₗ[ℤ] (Fin e →₀ ℤ))
        (a (cellClass (PolygonSurface word) ℤ ℤ 1 (charts.edges i) (g₁ z)))) = _
    rw [show a (cellClass (PolygonSurface word) ℤ ℤ 1 (charts.edges i) (g₁ z)) =
      Finsupp.single (charts.edges i) z from ha (charts.edges i) z,
      Finsupp.domLCongr_single, charts.edges.symm_apply_apply,
      Finsupp.linearEquivFunOnFinite_single]
  · intro i
    obtain ⟨q, hq, hdq⟩ := hd i
    rw [hc₁]
    have hh := attaching_degree_normalized ℤ ℤ 1 (by omega) b hS hT
      (PolygonSurface word) g₁ a ha charts.face (charts.edges i) q hq.2.1 (1 : ℤ)
    rw [nextDiskOrientation_chart, attachingSphereMap_eq_chart] at hh
    simp only [hdq, smul_eq_mul, mul_one, Nat.reduceAdd] at hh
    convert hh using 1

/-- The selected collapse map on an actual polygon side is fixed by the
characteristic-chart equations. The source boundary point is supplied by its
actual disk coordinate, so this lemma makes no unproved boundary-preservation
claim about an arbitrary disk homeomorphism. -/
lemma selectedCollapse_on_side {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)] (charts : PolygonCharts word)
    (b : (referenceDiskPair.{0} 1).sub) (d : Fin e)
    (q : skeletalPair (PolygonSurface word) 1 ⟶ quotientPair (referenceDiskPair.{0} 1))
    (hq : SelectedCellCollapse (PolygonSurface word) 1 (charts.edges d) b q)
    (i : Fin word.length) (x : Disk 1) (z : (referenceDiskPair.{0} 2).sub)
    (hz : charts.disk z.val.down = sidePoint word.length i.val
      (if (word.get i).2 then (x.val 0 + 1)/2 else 1-(x.val 0+1)/2)) :
    q.map (attachingBoundary (PolygonSurface word) 1 charts.face z) =
      if (word.get i).1 = d then
        quotientProjection (referenceDiskPair.{0} 1) (ULift.up x)
      else quotientProjection (referenceDiskPair.{0} 1) b.val := by
  classical
  have he : attachingBoundary (PolygonSurface word) 1 charts.face z =
      (characteristicPairMap 1 (charts.edges (word.get i).1)).map (ULift.up x) := by
    apply Subtype.ext
    change characteristic (PolygonSurface word) 2 charts.face z.val.down =
      characteristic (PolygonSurface word) 1 (charts.edges (word.get i).1) x
    rw [charts.face_chart, charts.edge_chart, hz]
  rw [he, hq.2.1]
  simp only [charts.edges.injective.eq_iff]

/-- Degree data need only be proved for selected collapse maps. Their
existence and restrictions are already established for every CW structure. -/
lemma polygonDifferentials_of_all_attachingDegrees {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)]
    (hc : PolygonCellCounts (PolygonSurface word) e)
    (charts : PolygonCharts word) (coefficient : ℤ)
    (b : (referenceDiskPair.{0} 1).sub)
    (hS : (referenceDiskPair.{0} 2).sub ≃ₜ liftedSphere.{0} 1)
    (hT : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ liftedSphere.{0} 1)
    (s : ℤ ≃ₗ[ℤ] homology ℤ ℤ (liftedSphere.{0} 1) 1)
    (hd : ∀ (i : Fin e) (q : skeletalPair (PolygonSurface word) 1 ⟶
      quotientPair (referenceDiskPair.{0} 1)),
      SelectedCellCollapse (PolygonSurface word) 1 (charts.edges i) b q →
      P202Specs.Degree.degree 1
        (chartAttachingMap (PolygonSurface word) 1 hS hT q charts.face) = coefficient) :
    PolygonDifferentials word charts coefficient := by
  apply polygonDifferentials_of_attachingDegrees word hc charts coefficient b hS hT s
  intro i
  obtain ⟨q, hquot, hq⟩ := P202.Homology.CellularDegrees.liftedCellCollapse
    (PolygonSurface word) 1 (charts.edges i) b
  have hsel : SelectedCellCollapse (PolygonSurface word) 1 (charts.edges i) b q :=
    ⟨hquot, hq, P202.Homology.CellularDegrees.liftedCellCollapse_complement
      (PolygonSurface word) 1 (charts.edges i) b q hq⟩
  exact ⟨q, hsel, hd i q hsel⟩

/-- Evaluation of the actual sphere self-map on a polygon side. This is
the direct bridge from geometric side parametrizations to circle degree
lemmas: surviving sides use the target disk-quotient chart and all others
have the same basepoint value. -/
lemma chartAttachingMap_on_side {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)] (charts : PolygonCharts word)
    (b : (referenceDiskPair.{0} 1).sub) (d : Fin e)
    (hS : (referenceDiskPair.{0} 2).sub ≃ₜ liftedSphere.{0} 1)
    (hT : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ liftedSphere.{0} 1)
    (q : skeletalPair (PolygonSurface word) 1 ⟶ quotientPair (referenceDiskPair.{0} 1))
    (hq : SelectedCellCollapse (PolygonSurface word) 1 (charts.edges d) b q)
    (i : Fin word.length) (x : Disk 1) (p : sphere 1)
    (hp : charts.disk (hS.symm (ULift.up p)).val.down = sidePoint word.length i.val
      (if (word.get i).2 then (x.val 0 + 1)/2 else 1-(x.val 0+1)/2)) :
    chartAttachingMap (PolygonSurface word) 1 hS hT q charts.face p =
      if (word.get i).1 = d then
        (hT (quotientProjection (referenceDiskPair.{0} 1) (ULift.up x))).down
      else (hT (quotientProjection (referenceDiskPair.{0} 1) b.val)).down := by
  classical
  change (hT (q.map (attachingBoundary (PolygonSurface word) 1 charts.face
    (hS.symm (ULift.up p))))).down = _
  rw [selectedCollapse_on_side word charts b d q hq i x _ hp]
  split_ifs <;> rfl

/-- No chosen sphere generator is an additional geometric obligation: its
existence is an accepted sphere-homology result. -/
lemma polygonDifferentials_of_geometricDegrees {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)]
    (hc : PolygonCellCounts (PolygonSurface word) e)
    (charts : PolygonCharts word) (coefficient : ℤ)
    (b : (referenceDiskPair.{0} 1).sub)
    (hS : (referenceDiskPair.{0} 2).sub ≃ₜ liftedSphere.{0} 1)
    (hT : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ liftedSphere.{0} 1)
    (hd : ∀ (i : Fin e) (q : skeletalPair (PolygonSurface word) 1 ⟶
      quotientPair (referenceDiskPair.{0} 1)),
      SelectedCellCollapse (PolygonSurface word) 1 (charts.edges i) b q →
      P202Specs.Degree.degree 1
        (chartAttachingMap (PolygonSurface word) 1 hS hT q charts.face) = coefficient) :
    PolygonDifferentials word charts coefficient := by
  obtain ⟨_, _, _, ⟨s⟩⟩ := P202.Homology.CellularDegrees.chartDataExist ℤ ℤ 1 (by omega)
  exact polygonDifferentials_of_all_attachingDegrees word hc charts coefficient b hS hT s hd


end AttachingBridge


namespace CircleChains
open P202Specs.CellularDegrees P202Specs.SpheresDisks Opposite
open scoped Simplicial

/-- A signed exponential traversal has exactly its signed angular formula. -/
lemma signedExponentialLoop_apply (s : ℤ) (hs : s = 1 ∨ s = -1 ∨ s = 0)
    (t : unitInterval) :
    signedLoop exponentialLoop s t = Circle.exp (2 * Real.pi * (s : ℝ) * (t : ℝ)) := by
  rcases hs with rfl | rfl | rfl
  · simp [signedLoop, exponentialLoop]
  · simp only [signedLoop, show (-1:ℤ) ≠ 1 by decide, ite_false,
      ite_eq_left, segment, ContinuousMap.coe_mk, exponentialLoop, interpolate,
      Int.cast_neg, Int.cast_one]
    change Circle.exp (2 * Real.pi * ((1 - (t : ℝ)) * 1 + (t : ℝ) * 0)) = _
    rw [show 2 * Real.pi * ((1 - (t : ℝ)) * 1 + (t : ℝ) * 0) =
      -(2 * Real.pi * (t : ℝ)) + 2 * Real.pi by ring, Circle.exp_add_two_pi]
    congr 1
    ring
  · simp [signedLoop, segment, interpolate, exponentialLoop]

/-- The finite signed word formula computes the integer degree after a
nonzero reference loop has been established. -/
lemma word_arc_degree {n : ℕ} (w : Word n) (edge : Fin n)
    (h : P202Specs.SpheresDisks.sphere 1 ≃ₜ TopCat.of Circle)
    (e : homology ℤ ℤ (TopCat.of Circle) 1 ≃ₗ[ℤ] ℤ)
    (f : TopCat.of Circle ⟶ TopCat.of Circle) (hf : f 1 = 1)
    (G : C(unitInterval, Circle)) (hG₀ : G 0 = 1) (hG₁ : G 1 = 1)
    (hG : loopClass G hG₀ hG₁ ≠ 0)
    (t : ℕ → unitInterval) (ht : ∀ i, f (G (t i)) = 1)
    (h₀ : t 0 = 0) (h₁ : t w.length = 1)
    (hArc : ∀ i < w.length,
      segment (f.hom.comp G) (t i) (t (i+1)) = signedLoop G (wordSign w edge i)) :
    P202Specs.Degree.degree 1
      (P202.Homology.CellularDegrees.CoefficientAction.conjugateSelfMap h f) =
        exponentSum w edge := by
  apply degree_eq_of_loop_action h e f G hG₀ hG₁ hG
  calc
    _ = loopClass (f.hom.comp G) (by simp [hG₀, hf]) (by simp [hG₁, hf]) :=
      loopClass_natural f hf G hG₀ hG₁
    _ = _ := word_arc_homology w edge G (f.hom.comp G) hG₀ hG₁ t ht h₀ h₁ hArc

/-- Only the finitely many actual arcs are required: their endpoint formulas
supply every basepoint condition needed by the homology computation. -/
lemma word_arc_degree_of_arcs {n : ℕ} (w : Word n) (edge : Fin n)
    (h : P202Specs.SpheresDisks.sphere 1 ≃ₜ TopCat.of Circle)
    (e : homology ℤ ℤ (TopCat.of Circle) 1 ≃ₗ[ℤ] ℤ)
    (f : TopCat.of Circle ⟶ TopCat.of Circle) (hf : f 1 = 1)
    (G : C(unitInterval, Circle)) (hG₀ : G 0 = 1) (hG₁ : G 1 = 1)
    (hG : loopClass G hG₀ hG₁ ≠ 0)
    (t : ℕ → unitInterval) (h₀ : t 0 = 0) (h₁ : t w.length = 1)
    (hArc : ∀ i < w.length,
      segment (f.hom.comp G) (t i) (t (i+1)) = signedLoop G (wordSign w edge i)) :
    P202Specs.Degree.degree 1
      (P202.Homology.CellularDegrees.CoefficientAction.conjugateSelfMap h f) =
        exponentSum w edge := by
  let q : ℕ → unitInterval := fun i => t (min i w.length)
  have hq : ∀ i, f (G (q i)) = 1 := by
    intro i
    by_cases hi : i < w.length
    · have hh := congrArg (fun F : C(unitInterval, Circle) => F 0) (hArc i hi)
      rw [signedLoop_zero G hG₀ hG₁] at hh
      simpa only [segment_zero, ContinuousMap.comp_apply, q,
        Nat.min_eq_left (Nat.le_of_lt hi)] using hh
    · simp only [q, Nat.min_eq_right (by omega : w.length ≤ i), h₁, hG₁, hf]
  apply word_arc_degree w edge h e f hf G hG₀ hG₁ hG q hq
  · simpa only [q, Nat.zero_min] using h₀
  · simpa only [q, Nat.min_self] using h₁
  · intro i hi
    simpa only [q, Nat.min_eq_left (Nat.le_of_lt hi),
      Nat.min_eq_left (by omega : i+1 ≤ w.length)] using hArc i hi

/-- The angular finite-arc formula computes degree in the common
counterclockwise circle coordinate. -/
lemma word_arc_degree_of_angle_formula {n : ℕ} (w : Word n) (edge : Fin n)
    (h : P202Specs.SpheresDisks.sphere 1 ≃ₜ TopCat.of Circle)
    (e : homology ℤ ℤ (TopCat.of Circle) 1 ≃ₗ[ℤ] ℤ)
    (f : TopCat.of Circle ⟶ TopCat.of Circle) (hf : f 1 = 1)
    (hG : loopClass exponentialLoop exponentialLoop_zero exponentialLoop_one ≠ 0)
    (t : ℕ → unitInterval) (h₀ : t 0 = 0) (h₁ : t w.length = 1)
    (hArc : ∀ i < w.length, ∀ u : unitInterval,
      f (Circle.exp (2 * Real.pi * (interpolate (t i) (t (i+1)) u : ℝ))) =
        Circle.exp (2 * Real.pi * (wordSign w edge i : ℝ) * (u : ℝ))) :
    P202Specs.Degree.degree 1
      (P202.Homology.CellularDegrees.CoefficientAction.conjugateSelfMap h f) =
        exponentSum w edge := by
  apply word_arc_degree_of_arcs w edge h e f hf exponentialLoop
    exponentialLoop_zero exponentialLoop_one hG t h₀ h₁
  intro i hi
  apply ContinuousMap.ext
  intro u
  rw [signedExponentialLoop_apply _ (wordSign_cases w edge i)]
  exact hArc i hi u


end CircleChains

open P202Specs.SpheresDisks in

/-- The standard real unit one-sphere as the complex unit circle. -/
def sphereCircleHomeomorph : sphere 1 ≃ₜ Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right]
    constructor
    · intro hx
      exact mem_sphere_zero_iff_norm.mpr
        ((Complex.orthonormalBasisOneI.repr.symm.norm_map x).trans hx)
    · intro hx
      exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm.trans
        (mem_sphere_zero_iff_norm.mp hx))



set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

lemma flatMap_constant_length {α β : Type*} (l : List α) (f : α → List β)
    (d : ℕ) (hf : ∀ a, (f a).length = d) :
    (l.flatMap f).length = d * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, hf, Nat.mul_add, Nat.add_comm]

lemma getElem_flatMap_block {α β : Type*} (l : List α) (f : α → List β)
    (d : ℕ) (hf : ∀ a, (f a).length = d) (i r : ℕ)
    (hi : i < l.length) (hr : r < d) :
    (l.flatMap f)[d*i+r]'(by
      rw [flatMap_constant_length l f d hf]
      have h := Nat.mul_le_mul_left d (Nat.succ_le_iff.mpr hi)
      simp only [Nat.mul_succ] at h
      omega) =
      (f (l[i]))[r]'(by rw [hf]; exact hr) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp [List.flatMap_cons, List.getElem_append, hf, hr]
    | succ i =>
      have hil : i < l.length := by simpa using hi
      simpa [List.flatMap_cons, List.getElem_append, hf, Nat.mul_add,
        show ¬d*i+d+r < d by omega, show d*i+d+r-d=d*i+r by omega,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih i hil

lemma orientedWord_length (g : ℕ) : (orientedWord g).length = 4*g := by
  unfold orientedWord
  rw [flatMap_constant_length _ _ 4 (by intro; rfl)]
  simp

lemma nonorientableWord_length (k : ℕ) : (nonorientableWord k).length = 2*k := by
  unfold nonorientableWord
  rw [flatMap_constant_length _ _ 2 (by intro; rfl)]
  simp

lemma orientedWord_get_block (g : ℕ) (i : Fin g) (r : ℕ) (hr : r < 4) :
    (orientedWord g)[4*i.val+r]'(by rw [orientedWord_length]; omega) =
    (let a : Fin (2*g) := ⟨2*i.val, by omega⟩
     let b : Fin (2*g) := ⟨2*i.val+1, by omega⟩
     [(a,true), (b,true), (a,false), (b,false)])[r]'(by simp; omega) := by
  simpa [orientedWord] using
    getElem_flatMap_block (List.finRange g) (fun i =>
      let a : Fin (2*g) := ⟨2*i.val, by omega⟩
      let b : Fin (2*g) := ⟨2*i.val+1, by omega⟩
      [(a,true), (b,true), (a,false), (b,false)]) 4 (by intro; rfl)
      i.val r (by simpa using i.isLt) hr

lemma nonorientableWord_get_block (k : ℕ) (i : Fin k) (r : ℕ) (hr : r < 2) :
    (nonorientableWord k)[2*i.val+r]'(by rw [nonorientableWord_length]; omega) =
      (i,true) := by
  have h := getElem_flatMap_block (List.finRange k)
    (fun i => [(i,true), (i,true)]) 2 (by intro; rfl) i.val r
      (by simpa using i.isLt) hr
  interval_cases r <;> simpa [nonorientableWord] using h

/-- The actual geometric endpoint at position `j`, including the final
position equal to the word length. -/
def polygonVertex {e : ℕ} (w : Word e) (j : ℕ) : PolygonSurface w :=
  polygonProjection w (sidePoint w.length j 0)

lemma polygonVertex_occurrence_endpoints {e : ℕ} (w : Word e)
    (i j : Fin w.length) (hij : (w.get i).1 = (w.get j).1)
    (hi : (w.get i).2 = true) (hj : (w.get j).2 = true) :
    polygonVertex w i.val = polygonVertex w j.val ∧
      polygonVertex w (i.val+1) = polygonVertex w (j.val+1) := by
  simp only [List.get_eq_getElem] at hi hj
  constructor
  · simpa [polygonVertex, hi, hj] using
      polygonSides_identified w i j hij (0 : unitInterval)
  · simpa [polygonVertex, hi, hj] using
      polygonSides_identified w i j hij (1 : unitInterval)

lemma polygonVertex_opposite_endpoints {e : ℕ} (w : Word e)
    (i j : Fin w.length) (hij : (w.get i).1 = (w.get j).1)
    (hi : (w.get i).2 = true) (hj : (w.get j).2 = false) :
    polygonVertex w i.val = polygonVertex w (j.val+1) ∧
      polygonVertex w (i.val+1) = polygonVertex w j.val := by
  simp only [List.get_eq_getElem] at hi hj
  constructor
  · simpa [polygonVertex, hi, hj] using
      polygonSides_identified w i j hij (0 : unitInterval)
  · simpa [polygonVertex, hi, hj] using
      polygonSides_identified w i j hij (1 : unitInterval)

lemma nonorientableVertex_block (k : ℕ) (i : Fin k)
    (r : ℕ) (hr : r ≤ 2) :
    polygonVertex (nonorientableWord k) (2*i.val+r) =
      polygonVertex (nonorientableWord k) (2*i.val) := by
  let p : Fin (nonorientableWord k).length :=
    ⟨2*i.val, by rw [nonorientableWord_length]; omega⟩
  let q : Fin (nonorientableWord k).length :=
    ⟨2*i.val+1, by rw [nonorientableWord_length]; omega⟩
  have hp : (nonorientableWord k).get p = (i,true) := by
    simpa [p, List.get_eq_getElem] using nonorientableWord_get_block k i 0 (by omega)
  have hq : (nonorientableWord k).get q = (i,true) := by
    simpa [q, List.get_eq_getElem] using nonorientableWord_get_block k i 1 (by omega)
  have h := polygonVertex_occurrence_endpoints (nonorientableWord k) p q
    (by rw [hp, hq]) (by rw [hp]) (by rw [hq])
  dsimp [p,q] at h
  interval_cases r
  · rfl
  · exact h.1.symm
  · simpa [Nat.add_assoc] using (h.1.trans h.2).symm

lemma orientedVertex_block (g : ℕ) (i : Fin g)
    (r : ℕ) (hr : r ≤ 4) :
    polygonVertex (orientedWord g) (4*i.val+r) =
      polygonVertex (orientedWord g) (4*i.val) := by
  let p (r : ℕ) (hr : r < 4) : Fin (orientedWord g).length :=
    ⟨4*i.val+r, by rw [orientedWord_length]; omega⟩
  have hp0 : (orientedWord g).get (p 0 (by omega)) =
      (⟨2*i.val, by omega⟩,true) := by
    simpa [p, List.get_eq_getElem] using orientedWord_get_block g i 0 (by omega)
  have hp1 : (orientedWord g).get (p 1 (by omega)) =
      (⟨2*i.val+1, by omega⟩,true) := by
    simpa [p, List.get_eq_getElem] using orientedWord_get_block g i 1 (by omega)
  have hp2 : (orientedWord g).get (p 2 (by omega)) =
      (⟨2*i.val, by omega⟩,false) := by
    simpa [p, List.get_eq_getElem] using orientedWord_get_block g i 2 (by omega)
  have hp3 : (orientedWord g).get (p 3 (by omega)) =
      (⟨2*i.val+1, by omega⟩,false) := by
    simpa [p, List.get_eq_getElem] using orientedWord_get_block g i 3 (by omega)
  have ha := polygonVertex_opposite_endpoints (orientedWord g)
    (p 0 (by omega)) (p 2 (by omega))
    (by rw [hp0,hp2]) (by rw [hp0]) (by rw [hp2])
  have hb := polygonVertex_opposite_endpoints (orientedWord g)
    (p 1 (by omega)) (p 3 (by omega))
    (by rw [hp1,hp3]) (by rw [hp1]) (by rw [hp3])
  dsimp [p] at ha hb
  simp only [Nat.add_zero, Nat.add_assoc] at ha hb
  interval_cases r
  · rfl
  · exact (ha.2.trans hb.2).trans ha.1.symm
  · exact hb.2.trans ha.1.symm
  · exact ha.1.symm
  · exact hb.1.symm.trans ((ha.2.trans hb.2).trans ha.1.symm)

lemma nonorientableVertex_block_start (k i : ℕ) (hi : i ≤ k) :
    polygonVertex (nonorientableWord k) (2*i) =
      polygonVertex (nonorientableWord k) 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i < k := by omega
    have h := nonorientableVertex_block k ⟨i, hi'⟩ 2 (by omega)
    simpa [Nat.mul_succ] using h.trans (ih (by omega))

lemma orientedVertex_block_start (g i : ℕ) (hi : i ≤ g) :
    polygonVertex (orientedWord g) (4*i) =
      polygonVertex (orientedWord g) 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i < g := by omega
    have h := orientedVertex_block g ⟨i, hi'⟩ 4 (by omega)
    simpa [Nat.mul_succ] using h.trans (ih (by omega))

/-- All vertices in the actual square-word quotient lie in one class. -/
lemma nonorientableVertices_single (k j : ℕ)
    (hj : j ≤ (nonorientableWord k).length) :
    polygonVertex (nonorientableWord k) j =
      polygonVertex (nonorientableWord k) 0 := by
  rw [nonorientableWord_length] at hj
  by_cases he : j = 2*k
  · simpa [he] using nonorientableVertex_block_start k k (by omega)
  · have hi : j/2 < k := by omega
    have h := nonorientableVertex_block k ⟨j/2, hi⟩ (j%2) (by omega)
    have he : 2*(j/2)+j%2 = j := by omega
    simpa [he] using h.trans (nonorientableVertex_block_start k (j/2) (by omega))

/-- All vertices in the actual commutator-word quotient lie in one class. -/
lemma orientedVertices_single (g j : ℕ)
    (hj : j ≤ (orientedWord g).length) :
    polygonVertex (orientedWord g) j =
      polygonVertex (orientedWord g) 0 := by
  rw [orientedWord_length] at hj
  by_cases he : j = 4*g
  · simpa [he] using orientedVertex_block_start g g (by omega)
  · have hi : j/4 < g := by omega
    have h := orientedVertex_block g ⟨j/4, hi⟩ (j%4) (by omega)
    have he : 4*(j/4)+j%4 = j := by omega
    simpa [he] using h.trans (orientedVertex_block_start g (j/4) (by omega))

lemma nonorientableWord_positive_occurrence (k : ℕ) (e : Fin k) :
    ∃ i : Fin (nonorientableWord k).length, (nonorientableWord k).get i = (e,true) := by
  refine ⟨⟨2*e.val, by rw [nonorientableWord_length]; omega⟩, ?_⟩
  simpa [List.get_eq_getElem] using nonorientableWord_get_block k e 0 (by omega)

lemma orientedWord_positive_occurrence (g : ℕ) (e : Fin (2*g)) :
    ∃ i : Fin (orientedWord g).length, (orientedWord g).get i = (e,true) := by
  have hi : e.val/2 < g := by omega
  have hr : e.val%2 < 2 := Nat.mod_lt _ (by omega)
  refine ⟨⟨4*(e.val/2)+e.val%2, by rw [orientedWord_length]; omega⟩, ?_⟩
  have h := orientedWord_get_block g ⟨e.val/2,hi⟩ (e.val%2) (by omega)
  have he : 2*(e.val/2)+e.val%2 = e.val := by omega
  rcases Nat.mod_two_eq_zero_or_one e.val with hr | hr
  · simp only [hr, List.getElem_cons_zero] at h
    simpa [hr, List.get_eq_getElem, show 2*(e.val/2)=e.val by omega] using h
  · simp only [hr, List.getElem_cons_succ, List.getElem_cons_zero] at h
    simpa [hr, List.get_eq_getElem, show 2*(e.val/2)+1=e.val by omega] using h

open P202.Cellular

lemma diskOne_coord_norm (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

def diskOneParameter (x : Disk 1) : unitInterval :=
  ⟨(x.val 0+1)/2, by
    have hx : |x.val 0| ≤ 1 := by
      rw [← diskOne_coord_norm]
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    rcases abs_le.mp hx with ⟨hl,hu⟩
    constructor <;> linarith⟩

def intervalToDiskOne (t : unitInterval) : Disk 1 :=
  ⟨WithLp.toLp 2 (fun _ : Fin 1 => 2*t.val-1), by
    rw [Metric.mem_closedBall, dist_zero_right, diskOne_coord_norm]
    change |2*t.val-1| ≤ 1
    rcases t.property with ⟨hl,hu⟩
    exact abs_le.mpr (by constructor <;> linarith)⟩

def diskOneParameterHomeomorph : Disk 1 ≃ₜ unitInterval where
  toFun := diskOneParameter
  invFun := intervalToDiskOne
  left_inv x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    dsimp [intervalToDiskOne, diskOneParameter]
    ring
  right_inv t := by
    apply Subtype.ext
    dsimp [intervalToDiskOne, diskOneParameter]
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    dsimp [diskOneParameter]
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    dsimp [intervalToDiskOne]
    fun_prop

def openDiskOneParameterHomeomorph : OpenDisk 1 ≃ₜ Set.Ioo (0 : ℝ) 1 where
  toFun x := ⟨(x.val 0+1)/2, by
    have hx : |x.val 0| < 1 := by
      rw [← diskOne_coord_norm]
      simpa only [Metric.mem_ball, dist_zero_right] using x.property
    rcases abs_lt.mp hx with ⟨hl,hu⟩
    constructor <;> linarith⟩
  invFun t := ⟨WithLp.toLp 2 (fun _ : Fin 1 => 2*t.val-1), by
    rw [Metric.mem_ball, dist_zero_right, diskOne_coord_norm]
    change |2*t.val-1| < 1
    rcases t.property with ⟨hl,hu⟩
    exact abs_lt.mpr (by constructor <;> linarith)⟩
  left_inv x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    dsimp
    ring
  right_inv t := by
    apply Subtype.ext
    dsimp
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

def polygonEdgeMap {e : ℕ} (w : Word e) (i : Fin w.length) :
    C(Disk 1, PolygonSurface w) where
  toFun x := polygonProjection w (sidePoint w.length i.val
    (if (w.get i).2 then (x.val 0+1)/2 else 1-(x.val 0+1)/2))
  continuous_toFun := (polygonProjection w).continuous.comp
    ((sidePoint_continuous _ _).comp (by split_ifs <;> fun_prop))

lemma polygonEdgeMap_occurrence {e : ℕ} (w : Word e) (i j : Fin w.length)
    (hij : (w.get i).1 = (w.get j).1) : polygonEdgeMap w i = polygonEdgeMap w j := by
  ext x
  exact polygonSides_identified w i j hij (diskOneParameter x)

def polygonOpenSide {e : ℕ} (w : Word e) (i : Fin w.length) :
    C(Set.Ioo (0 : ℝ) 1, PolygonSurface w) where
  toFun t := polygonProjection w (sidePoint w.length i.val
    (if (w.get i).2 then t.val else 1-t.val))
  continuous_toFun := (polygonProjection w).continuous.comp
    ((sidePoint_continuous _ _).comp (by split_ifs <;> fun_prop))

def intervalInteriorHomeomorph : Set.Ioo (0 : ℝ) 1 ≃ₜ
    {t : unitInterval // t.val ∈ Set.Ioo (0 : ℝ) 1} where
  toFun t := ⟨⟨t.val, le_of_lt t.property.1, le_of_lt t.property.2⟩, t.property⟩
  invFun t := ⟨t.val.val, t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

lemma polygonOpenSide_isEmbedding {e : ℕ} (w : Word e) (hm : 0 < w.length)
    (hvertices : ∀ (i j : Fin w.length), polygonProjection w (sidePoint w.length i.val 0) =
      polygonProjection w (sidePoint w.length j.val 0)) (i : Fin w.length) :
    IsEmbedding (polygonOpenSide w i) := by
  convert (polygon_openSide_isEmbedding w hm hvertices i).comp
    intervalInteriorHomeomorph.isEmbedding using 1
  funext t
  simp [polygonOpenSide, orientedSidePoint, orientedSideParameter_val,
    intervalInteriorHomeomorph]

lemma polygonOpenSide_ne_vertex {e : ℕ} (w : Word e) (hm : 0 < w.length)
    (i : Fin w.length) (t : Set.Ioo (0 : ℝ) 1) :
    polygonOpenSide w i t ≠ polygonVertex w 0 := by
  simpa [polygonOpenSide, polygonVertex, orientedSidePoint, orientedSideParameter_val,
    intervalInteriorHomeomorph] using
      polygonProjection_orientedSide_ne_vertex w hm i ⟨0,hm⟩
        (intervalInteriorHomeomorph t).val t.property

lemma polygonOpenSide_eq_iff {e : ℕ} (w : Word e) (hm : 0 < w.length)
    (i j : Fin w.length) (t s : Set.Ioo (0 : ℝ) 1) :
    polygonOpenSide w i t = polygonOpenSide w j s ↔
      (w.get i).1 = (w.get j).1 ∧ t = s := by
  have h := polygonProjection_orientedSide_eq_iff w hm i j
    (intervalInteriorHomeomorph t).val (intervalInteriorHomeomorph s).val t.property s.property
  simpa [polygonOpenSide, orientedSidePoint, orientedSideParameter_val,
    intervalInteriorHomeomorph, Subtype.ext_iff] using h

lemma polygonSidePoint_endpoint {e : ℕ} (w : Word e)
    (hvertices : ∀ j, j ≤ w.length → polygonVertex w j = polygonVertex w 0)
    (i : Fin w.length) (t : ℝ) (ht : t = 0 ∨ t = 1) :
    polygonProjection w (sidePoint w.length i.val t) = polygonVertex w 0 := by
  rcases ht with rfl | rfl
  · exact hvertices i.val (by omega)
  · simpa only [polygonVertex, sidePoint_one] using hvertices (i.val+1) (by omega)

lemma polygonBoundaryPoint_decomposition {e : ℕ} (w : Word e)
    (hm : 0 < w.length) (rep : Fin e → Fin w.length)
    (hrep : ∀ j, (w.get (rep j)).1 = j)
    (hvertices : ∀ j, j ≤ w.length → polygonVertex w j = polygonVertex w 0)
    (x : ClosedDisk) (hx : ‖x.val‖ = 1) :
    polygonProjection w x = polygonVertex w 0 ∨
      ∃ (j : Fin e) (t : Set.Ioo (0 : ℝ) 1),
        polygonProjection w x = polygonOpenSide w (rep j) t := by
  obtain ⟨i,u,rfl⟩ := sidePoint_surjective_boundary w.length hm x hx
  by_cases he : u.val = 0 ∨ u.val = 1
  · exact Or.inl (polygonSidePoint_endpoint w hvertices i u.val he)
  · have hu : u.val ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · exact lt_of_le_of_ne u.property.1 (Ne.symm (fun h => he (Or.inl h)))
      · exact lt_of_le_of_ne u.property.2 (fun h => he (Or.inr h))
    let t := orientedSideParameter (w.get i).2 u
    have ht : t.val ∈ Set.Ioo (0 : ℝ) 1 :=
      (orientedSideParameter_interior_iff _ _).mpr hu
    have h := polygonSides_identified w i (rep (w.get i).1) (hrep _).symm t
    have hpoint : sidePoint w.length i.val
        (if (w.get i).2 then t.val else 1-t.val) =
        sidePoint w.length i.val u.val := by
      have hi : (if (w.get i).2 then t.val else 1-t.val) = u.val := by
        simpa only [t, orientedSideParameter_val] using
          congrArg Subtype.val (orientedSideParameter_involutive (w.get i).2 u)
      rw [hi]
    rw [hpoint] at h
    exact Or.inr ⟨(w.get i).1, ⟨t.val, ht⟩, h⟩

inductive PolygonCell (e : ℕ) : ℕ → Type
  | vertex : PolygonCell e 0
  | edge : Fin e → PolygonCell e 1
  | face : PolygonCell e 2

@[instance_reducible] def polygonCellStructure {e : ℕ} (w : Word e) (rep : Fin e → Fin w.length) :
    CellStructure (PolygonSurface w) where
  Cell := PolygonCell e
  characteristic _n c := match c with
    | .vertex => ContinuousMap.const _ (polygonVertex w 0)
    | .edge j => polygonEdgeMap w (rep j)
    | .face => (polygonProjection w).comp
        ⟨complexDiskHomeomorph, complexDiskHomeomorph.continuous⟩

def polygonVertexCellEquiv (e : ℕ) : PolygonCell e 0 ≃ Fin 1 where
  toFun _ := 0
  invFun _ := .vertex
  left_inv x := by cases x; rfl
  right_inv x := by exact Subsingleton.elim _ _

def polygonEdgeCellEquiv (e : ℕ) : Fin e ≃ PolygonCell e 1 where
  toFun := .edge
  invFun x := match x with | .edge j => j
  left_inv _ := rfl
  right_inv x := by cases x; rfl

def polygonFaceCellEquiv (e : ℕ) : PolygonCell e 2 ≃ Fin 1 where
  toFun _ := 0
  invFun _ := .face
  left_inv x := by cases x; rfl
  right_inv x := by exact Subsingleton.elim _ _

section PolygonCells

variable {e : ℕ} (w : Word e) (rep : Fin e → Fin w.length)

lemma polygon_cellCounts : letI := polygonCellStructure w rep
    PolygonCellCounts (PolygonSurface w) e := by
  letI := polygonCellStructure w rep
  refine ⟨⟨polygonVertexCellEquiv e⟩, ⟨(polygonEdgeCellEquiv e).symm⟩,
    ⟨polygonFaceCellEquiv e⟩, ?_⟩
  intro n hn
  constructor
  intro x
  cases x <;> omega

def polygonCharts (hrep : ∀ j, (w.get (rep j)).1 = j) :
    letI := polygonCellStructure w rep
    PolygonCharts w := by
  letI := polygonCellStructure w rep
  exact {
    vertex := .vertex
    edges := polygonEdgeCellEquiv e
    face := .face
    disk := complexDiskHomeomorph
    vertex_chart := fun _ => rfl
    edge_chart := fun i x =>
      congrArg (fun f : C(Disk 1, PolygonSurface w) => f x)
        (polygonEdgeMap_occurrence w (rep (w.get i).1) i (hrep _))
    face_chart := fun _ => rfl }

lemma polygon_vertex_openCell : letI := polygonCellStructure w rep
    openCell (PolygonSurface w) 0 (PolygonCell.vertex : PolygonCell e 0) =
      {polygonVertex w 0} := by
  letI := polygonCellStructure w rep
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    rfl
  · rintro rfl
    exact ⟨⟨0, by simp [Metric.mem_ball]⟩, rfl⟩

lemma polygon_face_openCell : letI := polygonCellStructure w rep
    openCell (PolygonSurface w) 2 (PolygonCell.face : PolygonCell e 2) =
      polygonInteriorProjection w '' Set.univ := by
  letI := polygonCellStructure w rep
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨⟨complexDiskHomeomorph (interiorInclusion 2 y), ?_⟩, Set.mem_univ _, rfl⟩
    rw [complexDiskHomeomorph_norm]
    change ‖y.val‖ < 1
    simpa only [Metric.mem_ball, dist_zero_right] using y.property
  · rintro ⟨y,hy,rfl⟩
    let z := complexDiskHomeomorph.symm y.val
    have hz : ‖z.val‖ < 1 := by
      rw [← complexDiskHomeomorph_norm]
      simpa [z] using y.property
    exact ⟨⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩,
      congrArg (polygonProjection w) (complexDiskHomeomorph.apply_symm_apply y.val)⟩

lemma polygon_edge_openCell (j : Fin e) : letI := polygonCellStructure w rep
    openCell (PolygonSurface w) 1 (PolygonCell.edge j) =
      Set.range (polygonOpenSide w (rep j)) := by
  letI := polygonCellStructure w rep
  have he : interiorMap (PolygonSurface w) 1 (PolygonCell.edge j) =
      polygonOpenSide w (rep j) ∘ openDiskOneParameterHomeomorph := rfl
  simp only [openCell, he, Set.range_comp,
    openDiskOneParameterHomeomorph.surjective.range_eq, Set.image_univ]

lemma polygon_edge_interior_embedding (j : Fin e)
    (hj : IsEmbedding (polygonOpenSide w (rep j))) :
    letI := polygonCellStructure w rep
    IsEmbedding (interiorMap (PolygonSurface w) 1 (PolygonCell.edge j)) := by
  letI := polygonCellStructure w rep
  change IsEmbedding (polygonOpenSide w (rep j) ∘ openDiskOneParameterHomeomorph)
  exact hj.comp openDiskOneParameterHomeomorph.isEmbedding

lemma polygon_face_interior_embedding : letI := polygonCellStructure w rep
    IsEmbedding (interiorMap (PolygonSurface w) 2 (PolygonCell.face : PolygonCell e 2)) := by
  letI := polygonCellStructure w rep
  let f : OpenDisk 2 → InteriorDisk := fun y =>
    ⟨complexDiskHomeomorph (interiorInclusion 2 y), by
      rw [complexDiskHomeomorph_norm]
      change ‖y.val‖ < 1
      simpa only [Metric.mem_ball, dist_zero_right] using y.property⟩
  have hi : IsEmbedding (interiorInclusion 2) :=
    IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.of_comp_iff.mp
    (complexDiskHomeomorph.isEmbedding.comp hi)
  exact (polygonInteriorProjection_openEmbedding w).isEmbedding.comp hf

lemma polygon_boundary_mem_skeletonLT_two (hm : 0 < w.length)
    (hrep : ∀ j, (w.get (rep j)).1 = j)
    (hvertices : ∀ j, j ≤ w.length → polygonVertex w j = polygonVertex w 0)
    (x : ClosedDisk) (hx : ‖x.val‖ = 1) : letI := polygonCellStructure w rep
    polygonProjection w x ∈ skeletonLT (PolygonSurface w) 2 := by
  letI := polygonCellStructure w rep
  rcases polygonBoundaryPoint_decomposition w hm rep hrep hvertices x hx with
    h | ⟨j,t,h⟩
  · refine Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by omega,
      Set.mem_iUnion.mpr ⟨PolygonCell.vertex, ?_⟩⟩⟩
    rw [polygon_vertex_openCell]
    exact h
  · refine Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨by omega,
      Set.mem_iUnion.mpr ⟨PolygonCell.edge j, ?_⟩⟩⟩
    rw [polygon_edge_openCell]
    exact ⟨t,h.symm⟩

lemma polygon_cover (hm : 0 < w.length)
    (hrep : ∀ j, (w.get (rep j)).1 = j)
    (hvertices : ∀ j, j ≤ w.length → polygonVertex w j = polygonVertex w 0) :
    letI := polygonCellStructure w rep
    ⋃ (n : ℕ) (c : Cell (PolygonSurface w) n), openCell (PolygonSurface w) n c = Set.univ := by
  letI := polygonCellStructure w rep
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
  have hx : ‖x.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  rcases lt_or_eq_of_le hx with hx | hx
  · refine Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨PolygonCell.face, ?_⟩⟩
    rw [polygon_face_openCell]
    exact ⟨⟨x,hx⟩,Set.mem_univ _,rfl⟩
  · have h := polygon_boundary_mem_skeletonLT_two w rep hm hrep hvertices x hx
    rcases Set.mem_iUnion.mp h with ⟨n,h⟩
    rcases Set.mem_iUnion.mp h with ⟨_,h⟩
    rcases Set.mem_iUnion.mp h with ⟨c,h⟩
    exact Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨c,h⟩⟩

lemma polygon_disjoint (hm : 0 < w.length)
    (hrep : ∀ j, (w.get (rep j)).1 = j) :
    letI := polygonCellStructure w rep
    (Set.univ : Set (Σ n, Cell (PolygonSurface w) n)).PairwiseDisjoint
      (fun c => openCell (PolygonSurface w) c.1 c.2) := by
  letI := polygonCellStructure w rep
  have hVF : Disjoint (openCell (PolygonSurface w) 0 PolygonCell.vertex)
      (openCell (PolygonSurface w) 2 PolygonCell.face) := by
    rw [polygon_vertex_openCell, polygon_face_openCell]
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain rfl := hx
    obtain ⟨z, _, hz⟩ := hy
    have he : z.val = sidePoint w.length 0 0 :=
      polygonProjection_eq_of_interior w z.property hz
    have hn := congrArg (fun a : ClosedDisk => ‖a.val‖) he
    have hnorm : ‖(sidePoint w.length 0 0).val‖ = 1 := by simp [sidePoint]
    exact (ne_of_lt z.property) (hn.trans hnorm)
  have hVE (j : Fin e) : Disjoint (openCell (PolygonSurface w) 0 PolygonCell.vertex)
      (openCell (PolygonSurface w) 1 (PolygonCell.edge j)) := by
    rw [polygon_vertex_openCell, polygon_edge_openCell]
    apply Set.disjoint_left.mpr
    rintro x rfl ⟨t,ht⟩
    exact polygonOpenSide_ne_vertex w hm (rep j) t ht
  have hEF (j : Fin e) : Disjoint (openCell (PolygonSurface w) 1 (PolygonCell.edge j))
      (openCell (PolygonSurface w) 2 PolygonCell.face) := by
    rw [polygon_edge_openCell, polygon_face_openCell]
    apply Set.disjoint_left.mpr
    rintro x ⟨t,rfl⟩ ⟨z,_,hz⟩
    have he := polygonProjection_eq_of_interior w z.property hz
    have hn := congrArg (fun a : ClosedDisk => ‖a.val‖) he
    have hnorm : ‖(sidePoint w.length (rep j).val
        (if (w.get (rep j)).2 then t.val else 1-t.val)).val‖ = 1 := Circle.norm_coe _
    exact (ne_of_lt z.property) (hn.trans hnorm)
  have hEE (j k : Fin e) (hjk : j ≠ k) :
      Disjoint (openCell (PolygonSurface w) 1 (PolygonCell.edge j))
        (openCell (PolygonSurface w) 1 (PolygonCell.edge k)) := by
    rw [polygon_edge_openCell, polygon_edge_openCell]
    apply Set.disjoint_left.mpr
    rintro x ⟨t,rfl⟩ ⟨s,hs⟩
    have he := ((polygonOpenSide_eq_iff w hm (rep k) (rep j) s t).mp hs).1
    rw [hrep,hrep] at he
    exact hjk he.symm
  intro a ha b hb hab
  obtain ⟨n,c⟩ := a
  obtain ⟨m,d⟩ := b
  cases c with
  | vertex => cases d with
    | vertex => exact (hab rfl).elim
    | edge j => exact hVE j
    | face => exact hVF
  | edge j => cases d with
    | vertex => exact (hVE j).symm
    | edge k => exact hEE j k (fun h => hab (by cases h; rfl))
    | face => exact hEF j
  | face => cases d with
    | vertex => exact hVF.symm
    | edge j => exact (hEF j).symm
    | face => exact (hab rfl).elim

lemma polygon_boundary_lands (hm : 0 < w.length)
    (hrep : ∀ j, (w.get (rep j)).1 = j)
    (hvertices : ∀ j, j ≤ w.length → polygonVertex w j = polygonVertex w 0) :
    letI := polygonCellStructure w rep
    ∀ n (c : Cell (PolygonSurface w) n),
      MapsTo (boundaryMap (PolygonSurface w) n c) Set.univ (skeletonLT (PolygonSurface w) n) := by
  letI := polygonCellStructure w rep
  intro n c
  cases c with
  | vertex =>
    intro x hx
    have hx' : ‖x.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have he : x.val = 0 := Subsingleton.elim _ _
    simp [he] at hx'
  | edge j =>
    intro x hx
    have hx' : |x.val 0| = 1 := by
      rw [← diskOne_coord_norm]
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have hp : (x.val 0+1)/2 = 0 ∨ (x.val 0+1)/2 = 1 := by
      rcases le_total (x.val 0) 0 with h | h
      · rw [abs_of_nonpos h] at hx'
        left
        linarith
      · rw [abs_of_nonneg h] at hx'
        right
        linarith
    have ht : (if (w.get (rep j)).2 then (x.val 0+1)/2 else 1-(x.val 0+1)/2) = 0 ∨
        (if (w.get (rep j)).2 then (x.val 0+1)/2 else 1-(x.val 0+1)/2) = 1 := by
      split_ifs <;> rcases hp with hp | hp <;> simp [hp]
    refine Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by omega,
      Set.mem_iUnion.mpr ⟨PolygonCell.vertex, ?_⟩⟩⟩
    rw [polygon_vertex_openCell]
    exact polygonSidePoint_endpoint w hvertices (rep j) _ ht
  | face =>
    intro x hx
    exact polygon_boundary_mem_skeletonLT_two w rep hm hrep hvertices
      (complexDiskHomeomorph (boundaryInclusion 2 x)) (by
        rw [complexDiskHomeomorph_norm]
        change ‖x.val‖ = 1
        simpa only [Metric.mem_sphere, dist_zero_right] using x.property)

lemma polygon_interior_embedding (hm : 0 < w.length)
    (hvertices : ∀ j, j ≤ w.length → polygonVertex w j = polygonVertex w 0) :
    letI := polygonCellStructure w rep
    ∀ n (c : Cell (PolygonSurface w) n), IsEmbedding (interiorMap (PolygonSurface w) n c) := by
  letI := polygonCellStructure w rep
  intro n c
  cases c with
  | vertex => exact IsEmbedding.of_subsingleton _
  | edge j =>
    exact polygon_edge_interior_embedding w rep j
      (polygonOpenSide_isEmbedding w hm
        (fun i j => (hvertices i.val (by omega)).trans (hvertices j.val (by omega)).symm) (rep j))
  | face => exact polygon_face_interior_embedding w rep

end PolygonCells

/-- The actual quotient CW structure follows from occurrence coverage and
the proved single endpoint class; no CW certificate is assumed. -/
@[instance_reducible] def polygonCWStructure {e : ℕ} (w : Word e)
    (rep : Fin e → Fin w.length) (hm : 0 < w.length)
    (hrep : ∀ j, (w.get (rep j)).1 = j)
    (hvertices : ∀ j, j ≤ w.length → polygonVertex w j = polygonVertex w 0) :
    CWStructure (PolygonSurface w) := by
  letI := polygonCellStructure w rep
  letI := polygon_t2_of_vertices_identified w hm
    (fun i j => (hvertices i.val (by omega)).trans (hvertices j.val (by omega)).symm)
  let hc := polygon_cover w rep hm hrep hvertices
  exact P202.Topology.cwStructureOfWeak
    (polygon_interior_embedding w rep hm hvertices)
    (polygon_disjoint w rep hm hrep)
    hc
    (polygon_boundary_lands w rep hm hrep hvertices)
    (polygonClosureFinite w (polygon_cellCounts w rep) hc)
    (polygonWeakTopology w (polygonCharts w rep hrep))

lemma polygonCellStructures_of_word {e : ℕ} (w : Word e) (hm : 0 < w.length)
    (hoccurs : ∀ j : Fin e, ∃ i : Fin w.length, (w.get i).1 = j)
    (hvertices : ∀ j, j ≤ w.length → polygonVertex w j = polygonVertex w 0) :
    ∃ C : CWStructure (PolygonSurface w), letI := C
      PolygonCellCounts (PolygonSurface w) e ∧ Nonempty (PolygonCharts w) := by
  choose rep hrep using hoccurs
  refine ⟨polygonCWStructure w rep hm hrep hvertices, ?_⟩
  exact ⟨polygon_cellCounts w rep, ⟨polygonCharts w rep hrep⟩⟩

theorem polygonCellStructures : Expected.polygonCellStructures := by
  constructor
  · intro g
    cases g with
    | zero => exact genusZeroPolygonCellStructures
    | succ g =>
      apply polygonCellStructures_of_word (orientedWord (g+1))
        (by rw [orientedWord_length]; omega)
      · intro e
        obtain ⟨i,hi⟩ := orientedWord_positive_occurrence (g+1) e
        exact ⟨i,congrArg Prod.fst hi⟩
      · exact orientedVertices_single (g+1)
  · intro k hk
    apply polygonCellStructures_of_word (nonorientableWord k)
      (by rw [nonorientableWord_length]; omega)
    · intro e
      obtain ⟨i,hi⟩ := nonorientableWord_positive_occurrence k e
      exact ⟨i,congrArg Prod.fst hi⟩
    · exact nonorientableVertices_single k



namespace CircleGenerator
open P202Specs.RelativeSingularChains P202Specs.CellularDegrees
open P202Specs.SpheresDisks P202Specs.GoodPairQuotient
set_option maxHeartbeats 800000
open P202.Homology.SurfaceHomology.CircleChains

def realLine : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

@[simp] lemma realLine_apply (t : ℝ) (i : Fin 1) : realLine t i = t :=
  OrthonormalBasis.singleton_repr t i

lemma realLine_symm (x : EuclideanSpace ℝ (Fin 1)) :
    realLine.symm x = x 0 := by
  have hx := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) (realLine.apply_symm_apply x)
  simpa only [realLine_apply] using hx

def intervalDisk : unitInterval ≃ₜ Disk 1 where
  toFun t := ⟨realLine (2*(t:ℝ)-1), by
    simp only [Metric.mem_closedBall, dist_zero_right, realLine.norm_map, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [t.property.1], by linarith [t.property.2]⟩⟩
  invFun x := ⟨(realLine.symm x.val + 1)/2, by
    have h : |realLine.symm x.val| ≤ 1 := by
      rw [← Real.norm_eq_abs, realLine.symm.norm_map]
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    rcases abs_le.mp h with ⟨h₀,h₁⟩
    constructor <;> linarith⟩
  left_inv t := by
    apply Subtype.ext
    simp only [LinearIsometryEquiv.symm_apply_apply]
    ring
  right_inv x := by
    apply Subtype.ext
    change realLine (2*((realLine.symm x.val+1)/2)-1) = x.val
    rw [show 2*((realLine.symm x.val+1)/2)-1 = realLine.symm x.val by ring]
    exact realLine.apply_symm_apply x.val
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact realLine.continuous.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((realLine.symm.continuous.comp continuous_subtype_val).add continuous_const).div_const 2

@[simp] lemma intervalDisk_apply (t : unitInterval) (i : Fin 1) :
    (intervalDisk t).val i = 2*(t:ℝ)-1 := by
  change realLine (2*(t:ℝ)-1) i = _
  exact realLine_apply _ i

lemma intervalDisk_norm (t : unitInterval) :
    ‖(intervalDisk t).val‖ = |2*(t:ℝ)-1| := by
  change ‖realLine _‖ = _
  rw [realLine.norm_map, Real.norm_eq_abs]

def standardInterval : IntervalParametrization where
  homeomorph := Convexity.StdSimplex.homeomorphI.trans intervalDisk
  boundary x := by
    have hs : x.weights 0 + x.weights 1 = 1 := by
      have ht := x.total
      rw [Finsupp.sum_fintype _ _ (by simp)] at ht
      simpa only [Nat.reduceAdd, Fin.sum_univ_two] using ht
    change (∃ i, x.weights i = 0) ↔
      ‖(intervalDisk (Convexity.StdSimplex.homeomorphI x)).val‖ = 1
    rw [intervalDisk_norm]
    have ht : (Convexity.StdSimplex.homeomorphI x : ℝ) = x.weights 1 :=
      Convexity.StdSimplex.homeomorphI_apply_coe x
    rw [ht]
    constructor
    · rintro ⟨i,hi⟩
      fin_cases i
      · change x.weights 0 = 0 at hi
        rw [show x.weights 1 = 1 by linarith, show 2*(1:ℝ)-1=1 by ring, abs_one]
      · change x.weights 1 = 0 at hi
        rw [hi]; norm_num
    · intro h
      rcases (abs_eq_abs.mp (show |2*x.weights 1-1| = |(1:ℝ)| by simpa using h)) with h | h
      · exact ⟨0, by linarith⟩
      · exact ⟨1, by linarith⟩

@[simp] lemma standardInterval_apply (x : StandardSimplex 1) (i : Fin 1) :
    (standardInterval.homeomorph x).val i = 2*x.weights 1-1 := by
  change (intervalDisk (Convexity.StdSimplex.homeomorphI x)).val i = _
  rw [intervalDisk_apply, Convexity.StdSimplex.homeomorphI_apply_coe]

def diskExp : C((referenceDiskPair.{0} 1).space, Circle) :=
  ⟨fun x => Circle.exp (Real.pi * (realLine.symm x.down.val + 1)),
    Circle.exp.continuous.comp (continuous_const.mul
      ((realLine.symm.continuous.comp (continuous_subtype_val.comp continuous_uliftDown)).add continuous_const))⟩

lemma diskExp_boundary (x : (referenceDiskPair.{0} 1).space)
    (hx : x ∈ (referenceDiskPair.{0} 1).subspace) : diskExp x = 1 := by
  have hh : |realLine.symm x.down.val| = 1 := by
    rw [← Real.norm_eq_abs, realLine.symm.norm_map]
    exact hx
  rcases abs_eq_abs.mp (show |realLine.symm x.down.val| = |(1:ℝ)| by simpa using hh) with h | h
  · change Circle.exp (Real.pi * (realLine.symm x.down.val + 1)) = 1
    rw [h, show Real.pi * ((1:ℝ)+1)=2*Real.pi by ring, Circle.exp_two_pi]
  · change Circle.exp (Real.pi * (realLine.symm x.down.val + 1)) = 1
    rw [h]
    norm_num

lemma diskExp_respects (x y : (referenceDiskPair.{0} 1).space)
    (h : (collapseSetoid (referenceDiskPair.{0} 1)).r x y) : diskExp x = diskExp y := by
  rcases h with rfl | ⟨hx,hy⟩
  · rfl
  · rw [diskExp_boundary x hx, diskExp_boundary y hy]

def quotientExp : quotientSpace (referenceDiskPair.{0} 1) → Circle :=
  Quotient.lift diskExp diskExp_respects

lemma quotientExp_continuous : Continuous quotientExp :=
  continuous_quot_lift _ diskExp.continuous

@[simp] lemma quotientExp_projection (x : (referenceDiskPair.{0} 1).space) :
    quotientExp (quotientProjection (referenceDiskPair.{0} 1) x) = diskExp x := rfl

lemma disk_scalar_le (x : (referenceDiskPair.{0} 1).space) :
    |realLine.symm x.down.val| ≤ 1 := by
  rw [← Real.norm_eq_abs, realLine.symm.norm_map]
  simpa only [Metric.mem_closedBall, dist_zero_right] using x.down.property

lemma quotientExp_injective : Function.Injective quotientExp := by
  intro x y
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  rename_i x y
  intro h
  apply Quotient.sound
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  have hprod : Real.pi * (realLine.symm x.down.val - realLine.symm y.down.val - 2*(m:ℝ)) = 0 := by
    linear_combination hm
  have hdiff : realLine.symm x.down.val - realLine.symm y.down.val = 2*(m:ℝ) := by
    have hz := (mul_eq_zero.mp hprod).resolve_left Real.pi_ne_zero
    linarith
  obtain ⟨hx₀,hx₁⟩ := abs_le.mp (disk_scalar_le x)
  obtain ⟨hy₀,hy₁⟩ := abs_le.mp (disk_scalar_le y)
  have hm₀ : (-1:ℝ) ≤ m := by linarith
  have hm₁ : (m:ℝ) ≤ 1 := by linarith
  have hm₀' : (-1:ℤ) ≤ m := by exact_mod_cast hm₀
  have hm₁' : m ≤ (1:ℤ) := by exact_mod_cast hm₁
  interval_cases m
  · right
    have hx : realLine.symm x.down.val = -1 := by norm_num at hdiff; linarith
    have hy : realLine.symm y.down.val = 1 := by norm_num at hdiff; linarith
    constructor
    · change ‖x.down.val‖ = 1
      rw [← realLine.symm.norm_map, hx]; norm_num
    · change ‖y.down.val‖ = 1
      rw [← realLine.symm.norm_map, hy]; norm_num
  · left
    apply ULift.ext
    apply Subtype.ext
    apply realLine.symm.injective
    norm_num at hdiff
    linarith
  · right
    have hx : realLine.symm x.down.val = 1 := by norm_num at hdiff; linarith
    have hy : realLine.symm y.down.val = -1 := by norm_num at hdiff; linarith
    constructor
    · change ‖x.down.val‖ = 1
      rw [← realLine.symm.norm_map, hx]; norm_num
    · change ‖y.down.val‖ = 1
      rw [← realLine.symm.norm_map, hy]; norm_num

lemma quotientExp_surjective : Function.Surjective quotientExp := by
  intro z
  have himage := Circle.periodic_exp.image_Icc Real.two_pi_pos 0
  simp only [zero_add] at himage
  have hz : z ∈ Circle.exp '' Set.Icc (0:ℝ) (2*Real.pi) := by
    rw [himage]
    exact ⟨_, Circle.exp_arg z⟩
  obtain ⟨θ,hθ,hz⟩ := hz
  let t : unitInterval := ⟨θ/(2*Real.pi), by
    constructor
    · exact div_nonneg hθ.1 Real.two_pi_pos.le
    · exact (div_le_one Real.two_pi_pos).mpr hθ.2⟩
  refine ⟨quotientProjection (referenceDiskPair.{0} 1) (ULift.up (intervalDisk t)), ?_⟩
  rw [quotientExp_projection]
  change Circle.exp (Real.pi * (realLine.symm (realLine (2*(t:ℝ)-1)) + 1)) = z
  rw [realLine.symm_apply_apply]
  apply Eq.trans _ hz
  congr 1
  change Real.pi * (2*(θ/(2*Real.pi))-1+1) = θ
  field_simp
  ring

def quotientDiskCircle : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ Circle := by
  letI : CompactSpace (referenceDiskPair.{0} 1).space :=
    (referenceDiskHomeomorph 1).symm.compactSpace
  letI : CompactSpace (quotientSpace (referenceDiskPair.{0} 1)) :=
    Quotient.compactSpace
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective quotientExp
    ⟨quotientExp_injective, quotientExp_surjective⟩) quotientExp_continuous

@[simp] lemma quotientDiskCircle_projection (x : (referenceDiskPair.{0} 1).space) :
    quotientDiskCircle (quotientProjection (referenceDiskPair.{0} 1) x) =
      Circle.exp (Real.pi * (x.down.val 0 + 1)) := by
  change Circle.exp (Real.pi * (realLine.symm x.down.val + 1)) = _
  rw [realLine_symm]

open scoped Simplicial

def canonicalLoop : C(unitInterval, Circle) :=
  ⟨fun t => Circle.exp (2*Real.pi*(t:ℝ)), Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)⟩

@[simp] lemma canonicalLoop_zero : canonicalLoop 0 = 1 := by simp [canonicalLoop]
@[simp] lemma canonicalLoop_one : canonicalLoop 1 = 1 := by simp [canonicalLoop]

def canonicalLoopClass : homology ℤ ℤ (TopCat.of Circle) 1 :=
  classOf ℤ (ordinaryComplex ℤ ℤ (TopCat.of Circle)) 1 (ordinaryLoopChain canonicalLoop)
    (ordinaryLoopChain_cycle canonicalLoop canonicalLoop_zero canonicalLoop_one)

lemma canonicalLoop_simplex :
    (TopCat.toSSet.map (TopCat.isoOfHomeo quotientDiskCircle).inv).app (Opposite.op ⦋1⦌)
      (loopSimplex canonicalLoop) =
    (TopCat.toSSet.map (quotientProjection (referenceDiskPair.{0} 1))).app (Opposite.op ⦋1⦌)
      standardInterval.simplex := by
  apply (simplexEquiv _ 1).injective
  simp only [P202.SingularChains.simplexEquiv_postcomp]
  apply ContinuousMap.ext
  intro x
  simp only [loopSimplex, IntervalParametrization.simplex, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  apply quotientDiskCircle.injective
  change quotientDiskCircle (quotientDiskCircle.symm (canonicalLoop (intervalParameter x))) =
    quotientDiskCircle (quotientProjection (referenceDiskPair.{0} 1)
      (ULift.up (standardInterval.homeomorph x)))
  rw [quotientDiskCircle.apply_symm_apply]
  change canonicalLoop (intervalParameter x) =
    diskExp (ULift.up (standardInterval.homeomorph x))
  change Circle.exp (2*Real.pi*x.weights 1) =
    Circle.exp (Real.pi * (realLine.symm (realLine
      (2*(Convexity.StdSimplex.homeomorphI x:ℝ)-1)) + 1))
  rw [realLine.symm_apply_apply, Convexity.StdSimplex.homeomorphI_apply_coe]
  congr 1
  ring

lemma chainMap_cycle {K L : ChainComplex (ModuleCat ℤ) ℤ} (f : K ⟶ L)
    (z : K.X 1) (hz : K.d 1 0 z = 0) : L.d 1 0 (f.f 1 z) = 0 := by
  have h := congrArg (fun t => t z) (f.comm 1 0)
  change L.d 1 0 (f.f 1 z) = f.f 0 (K.d 1 0 z) at h
  rw [h,hz,map_zero]

/-- The once-around exponential loop is a primitive class in actual integral
singular homology. Its normalization follows from the accepted interval
relative generator and quotient comparison, with explicit charts. -/
lemma canonicalLoop_generator :
    ∃ e : homology ℤ ℤ (TopCat.of Circle) 1 ≃ₗ[ℤ] ℤ,
      e canonicalLoopClass = 1 := by
  obtain ⟨g,hg⟩ := P202.Homology.CellularDegrees.interval_generator ℤ ℤ standardInterval
  let b : (referenceDiskPair.{0} 1).sub :=
    ⟨ULift.up (intervalDisk 0), by
      change ‖(intervalDisk 0).val‖ = 1
      rw [intervalDisk_norm]; norm_num⟩
  let A := P202.Homology.CellularDegrees.AttachingCalculation.diskQuotientRelativeIso ℤ ℤ 1 b
  let P := P202.Homology.CellularDegrees.AttachingCalculation.referenceQuotientProjectionIso ℤ ℤ 1 (by omega) b
  let hIso : quotientSpace (referenceDiskPair.{0} 1) ≅ TopCat.of Circle :=
    TopCat.isoOfHomeo quotientDiskCircle
  let H := (homologyFunctor ℤ ℤ (1:ℤ)).mapIso hIso
  let T := (ordinaryFunctor ℤ ℤ).map hIso.inv
  let z := ordinaryLoopChain canonicalLoop
  have hz : (ordinaryComplex ℤ ℤ (TopCat.of Circle)).d 1 0 z = 0 :=
    ordinaryLoopChain_cycle canonicalLoop canonicalLoop_zero canonicalLoop_one
  let zq := T.f 1 z
  have hzq : (ordinaryComplex ℤ ℤ (quotientSpace (referenceDiskPair.{0} 1))).d 1 0 zq = 0 :=
    chainMap_cycle T z hz
  let cq := classOf ℤ (ordinaryComplex ℤ ℤ (quotientSpace (referenceDiskPair.{0} 1))) 1 zq hzq
  have hcq : H.inv canonicalLoopClass = cq :=
    P202.Homology.CellularDegrees.homologyMap_classOf ℤ T 1 z hz hzq
  let S := (relativeMap (ordinaryFunctor ℤ ℤ) (quotientPairMap (referenceDiskPair.{0} 1)))
  let v := relativeSimplexChain ℤ ℤ (referenceDiskPair.{0} 1) 1 standardInterval.simplex 1
  have hv : (ordinary ℤ ℤ (referenceDiskPair.{0} 1)).d 1 0 v = 0 :=
    P202.Homology.CellularDegrees.relativePath_cycle ℤ ℤ (referenceDiskPair.{0} 1)
      standardInterval.simplex (standardInterval.endpoint 0) (standardInterval.endpoint 1)
      (P202.Homology.CellularDegrees.interval_face standardInterval 0)
      (P202.Homology.CellularDegrees.interval_face standardInterval 1) 1
  have hSv := chainMap_cycle S v hv
  have hPv := chainMap_cycle (projection (ordinaryFunctor ℤ ℤ) (quotientPair (referenceDiskPair.{0} 1))) zq hzq
  have hzchain : zq = simplexChainZ ℤ ℤ (quotientSpace (referenceDiskPair.{0} 1)) 1
      ((TopCat.toSSet.map (quotientProjection (referenceDiskPair.{0} 1))).app (Opposite.op ⦋1⦌)
        standardInterval.simplex) 1 := by
    have hmap := P202.Homology.CellularDegrees.simplexChainZ_map ℤ ℤ hIso.inv 1
      (loopSimplex canonicalLoop) 1
    exact hmap.trans (congrArg (fun σ => simplexChainZ ℤ ℤ
      (quotientSpace (referenceDiskPair.{0} 1)) 1 σ 1) canonicalLoop_simplex)
  have hchain : (projection (ordinaryFunctor ℤ ℤ) (quotientPair (referenceDiskPair.{0} 1))).f 1 zq = S.f 1 v := by
    calc
      _ = relativeSimplexChain ℤ ℤ (quotientPair (referenceDiskPair.{0} 1)) 1
          ((TopCat.toSSet.map (quotientProjection (referenceDiskPair.{0} 1))).app (Opposite.op ⦋1⦌)
            standardInterval.simplex) 1 :=
        congrArg ((projection (ordinaryFunctor ℤ ℤ) (quotientPair (referenceDiskPair.{0} 1))).f 1) hzchain
      _ = S.f 1 v := (P202.Homology.CellularDegrees.relativeSimplexChain_map ℤ ℤ
        (quotientPairMap (referenceDiskPair.{0} 1)) 1 standardInterval.simplex 1).symm
  have hleft : P.hom cq = classOf ℤ _ 1
      ((projection (ordinaryFunctor ℤ ℤ) (quotientPair (referenceDiskPair.{0} 1))).f 1 zq) hPv :=
    P202.Homology.CellularDegrees.homologyMap_classOf ℤ _ 1 zq hzq hPv
  have hright : A.hom (g 1) = classOf ℤ _ 1 (S.f 1 v) hSv := by
    have hh := congrArg (homologyMap S 1) (hg 1)
    exact hh.trans (P202.Homology.CellularDegrees.homologyMap_classOf ℤ S 1 v hv hSv)
  have hcclass : classOf ℤ _ 1
      ((projection (ordinaryFunctor ℤ ℤ) (quotientPair (referenceDiskPair.{0} 1))).f 1 zq) hPv =
      classOf ℤ _ 1 (S.f 1 v) hSv := by
    congr 1
  have hc : P.hom cq = A.hom (g 1) := hleft.trans (hcclass.trans hright.symm)
  let k : ℤ ≃ₗ[ℤ] homology ℤ ℤ (TopCat.of Circle) 1 :=
    g.trans (A.toLinearEquiv.trans (P.symm.toLinearEquiv.trans H.toLinearEquiv))
  have hk : k 1 = canonicalLoopClass := by
    change H.hom (P.inv (A.hom (g 1))) = canonicalLoopClass
    calc
      _ = H.hom (P.inv (P.hom cq)) := congrArg (fun t => H.hom (P.inv t)) hc.symm
      _ = H.hom cq := congrArg H.hom (P.hom_inv_id_apply cq)
      _ = H.hom (H.inv canonicalLoopClass) := congrArg H.hom hcq.symm
      _ = canonicalLoopClass := H.inv_hom_id_apply _
  refine ⟨k.symm, ?_⟩
  calc
    _ = k.symm (k 1) := congrArg k.symm hk.symm
    _ = 1 := k.symm_apply_apply _

lemma canonicalLoop_eq_exponentialLoop : canonicalLoop = exponentialLoop := by
  apply ContinuousMap.ext
  intro t
  rfl

lemma canonicalLoop_ne_zero : canonicalLoopClass ≠ 0 := by
  obtain ⟨e,he⟩ := canonicalLoop_generator
  intro h
  have hz := congrArg e h
  rw [he, e.map_zero] at hz
  exact one_ne_zero hz


end CircleGenerator



/-- Equally spaced breakpoints, extended constantly after the final one. -/
def polygonTime (m : ℕ) (hm : 0 < m) (i : ℕ) : unitInterval :=
  ⟨((min i m : ℕ) : ℝ) / (m : ℝ), by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    constructor
    · exact div_nonneg (by positivity) hmR.le
    · apply (div_le_iff₀ hmR).mpr
      simpa only [one_mul] using
        (show ((min i m : ℕ) : ℝ) ≤ (m : ℝ) by exact_mod_cast Nat.min_le_right i m)⟩

@[simp] lemma polygonTime_zero (m : ℕ) (hm : 0 < m) : polygonTime m hm 0 = 0 := by
  apply Subtype.ext
  simp [polygonTime]

@[simp] lemma polygonTime_end (m : ℕ) (hm : 0 < m) : polygonTime m hm m = 1 := by
  apply Subtype.ext
  simp [polygonTime, Nat.ne_of_gt hm]

lemma polygonTime_val_of_le (m : ℕ) (hm : 0 < m) (i : ℕ) (hi : i ≤ m) :
    (polygonTime m hm i).val = (i : ℝ) / (m : ℝ) := by
  simp [polygonTime, Nat.min_eq_left hi]

/-- Interpolation between consecutive breakpoints gives the polygon's actual
equal-arc boundary parameter. -/
lemma interpolate_polygonTime (m : ℕ) (hm : 0 < m) (i : ℕ) (hi : i < m)
    (u : unitInterval) :
    (CircleChains.interpolate (polygonTime m hm i) (polygonTime m hm (i+1)) u).val =
      ((i : ℝ) + u.val) / (m : ℝ) := by
  change (1-u.val) * (polygonTime m hm i).val +
    u.val * (polygonTime m hm (i+1)).val = _
  rw [polygonTime_val_of_le m hm i (by omega),
    polygonTime_val_of_le m hm (i+1) (by omega)]
  push_cast
  ring

lemma polygonTime_lt_succ (m : ℕ) (hm : 0 < m) (i : ℕ) (hi : i < m) :
    polygonTime m hm i < polygonTime m hm (i+1) := by
  change (polygonTime m hm i).val < (polygonTime m hm (i+1)).val
  rw [polygonTime_val_of_le m hm i (by omega),
    polygonTime_val_of_le m hm (i+1) (by omega)]
  apply (div_lt_div_iff_of_pos_right (by exact_mod_cast hm : (0 : ℝ) < m)).mpr
  exact_mod_cast Nat.lt_succ_self i



namespace AttachingBridge
open P202Specs.RelativeSingularChains P202Specs.CellularDegrees
open P202Specs.SpheresDisks P202Specs.GoodPairQuotient
open P202.Homology.CellularDegrees.ConnectingBridge
open P202.Homology.CellularDegrees.CoefficientAction

/-- The quotient of the oriented reference interval is charted first as a
circle, then as the geometric sphere, with the universe lift restored. -/
def circleTargetChart
    (hQ : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ Circle) :
    quotientSpace (referenceDiskPair.{0} 1) ≃ₜ P202Specs.CellularDegrees.liftedSphere.{0} 1 :=
  hQ.trans (sphereCircleHomeomorph.symm.trans Homeomorph.ulift.symm)

/-- The natural source boundary chart agrees with the complex disk chart. -/
lemma complexDisk_boundary_circle (z : Circle) :
    complexDiskHomeomorph
      (((referenceBoundarySphereHomeomorph.{0} 1).symm
        (ULift.up (sphereCircleHomeomorph.symm z))).val.down) =
      (⟨(z : ℂ), by simp only [Metric.mem_closedBall, dist_zero_right,
        Circle.norm_coe, le_refl]⟩ : ClosedDisk) := by
  apply Subtype.ext
  change Complex.orthonormalBasisOneI.repr.symm
    (Complex.orthonormalBasisOneI.repr (z : ℂ)) = (z : ℂ)
  exact Complex.orthonormalBasisOneI.repr.symm_apply_apply _

/-- The attaching map in the actual circular boundary coordinate. -/
def circleAttachingMap {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)] (charts : PolygonCharts word)
    (hQ : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ Circle)
    (q : skeletalPair (PolygonSurface word) 1 ⟶ quotientPair (referenceDiskPair.{0} 1)) :
    TopCat.of Circle ⟶ TopCat.of Circle :=
  TopCat.ofHom ⟨fun z => hQ (q.map (attachingBoundary (PolygonSurface word) 1 charts.face
    ((referenceBoundarySphereHomeomorph.{0} 1).symm
      (ULift.up (sphereCircleHomeomorph.symm z))))), by fun_prop⟩

lemma circleAttachingMap_conjugate {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)] (charts : PolygonCharts word)
    (hQ : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ Circle)
    (q : skeletalPair (PolygonSurface word) 1 ⟶ quotientPair (referenceDiskPair.{0} 1)) :
    conjugateSelfMap sphereCircleHomeomorph (circleAttachingMap word charts hQ q) =
      chartAttachingMap (PolygonSurface word) 1 (referenceBoundarySphereHomeomorph.{0} 1)
        (circleTargetChart hQ) q charts.face := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change sphereCircleHomeomorph.symm (hQ (q.map
    (attachingBoundary (PolygonSurface word) 1 charts.face
      ((referenceBoundarySphereHomeomorph.{0} 1).symm
        (ULift.up (sphereCircleHomeomorph.symm (sphereCircleHomeomorph p))))))) = _
  rw [sphereCircleHomeomorph.symm_apply_apply]
  rfl

/-- Side parametrizations determine the circular attaching map, with the
same interval quotient chart for every target edge. -/
lemma circleAttachingMap_on_side {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)] (charts : PolygonCharts word)
    (hdisk : charts.disk = complexDiskHomeomorph)
    (hQ : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ Circle)
    (b : (referenceDiskPair.{0} 1).sub) (d : Fin e)
    (q : skeletalPair (PolygonSurface word) 1 ⟶ quotientPair (referenceDiskPair.{0} 1))
    (hq : SelectedCellCollapse (PolygonSurface word) 1 (charts.edges d) b q)
    (i : Fin word.length) (x : Disk 1) :
    circleAttachingMap word charts hQ q
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) +
        (if (word.get i).2 then (x.val 0 + 1)/2 else 1-(x.val 0+1)/2)) /
          (word.length : ℝ))) =
      if (word.get i).1 = d then
        hQ (quotientProjection (referenceDiskPair.{0} 1) (ULift.up x))
      else hQ (quotientProjection (referenceDiskPair.{0} 1) b.val) := by
  let z := Circle.exp (2 * Real.pi * ((i.val : ℝ) +
    (if (word.get i).2 then (x.val 0 + 1)/2 else 1-(x.val 0+1)/2)) /
      (word.length : ℝ))
  have hz : charts.disk
      (((referenceBoundarySphereHomeomorph.{0} 1).symm
        (ULift.up (sphereCircleHomeomorph.symm z))).val.down) =
      sidePoint word.length i.val
        (if (word.get i).2 then (x.val 0 + 1)/2 else 1-(x.val 0+1)/2) := by
    rw [hdisk, complexDisk_boundary_circle]
    rfl
  have hh := selectedCollapse_on_side word charts b d q hq i x
    ((referenceBoundarySphereHomeomorph.{0} 1).symm
      (ULift.up (sphereCircleHomeomorph.symm z))) hz
  change hQ (q.map _) = _
  rw [hh]
  split_ifs <;> rfl

lemma quotientCircle_boundary_one
    (hQ : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ Circle)
    (hQexp : ∀ x : Disk 1,
      hQ (quotientProjection (referenceDiskPair.{0} 1) (ULift.up x)) =
        Circle.exp (Real.pi * (x.val 0 + 1)))
    (b : (referenceDiskPair.{0} 1).sub) :
    hQ (quotientProjection (referenceDiskPair.{0} 1) b.val) = 1 := by
  have hb : |b.val.down.val 0| = 1 := by
    have h := b.property
    change ‖b.val.down.val‖ = 1 at h
    simpa [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using h
  change hQ (quotientProjection (referenceDiskPair.{0} 1) (ULift.up b.val.down)) = 1
  rw [hQexp]
  rcases abs_eq_abs.mp (show |b.val.down.val 0| = |(1:ℝ)| by simpa using hb) with hb | hb
  · rw [hb, show Real.pi * ((1:ℝ)+1) = 2*Real.pi by ring, Circle.exp_two_pi]
  · simp [hb]

/-- The angular attaching map on an occurrence of an edge: its sign is fixed
by the original polygon word and the common interval quotient coordinate. -/
lemma circleAttachingMap_on_side_angle {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)] (charts : PolygonCharts word)
    (hdisk : charts.disk = complexDiskHomeomorph)
    (hQ : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ Circle)
    (hQexp : ∀ x : Disk 1,
      hQ (quotientProjection (referenceDiskPair.{0} 1) (ULift.up x)) =
        Circle.exp (Real.pi * (x.val 0 + 1)))
    (b : (referenceDiskPair.{0} 1).sub) (d : Fin e)
    (q : skeletalPair (PolygonSurface word) 1 ⟶ quotientPair (referenceDiskPair.{0} 1))
    (hq : SelectedCellCollapse (PolygonSurface word) 1 (charts.edges d) b q)
    (i : Fin word.length) (u : unitInterval) (x : Disk 1)
    (hx : x.val 0 = if (word.get i).2 then 2*(u:ℝ)-1 else 1-2*(u:ℝ)) :
    circleAttachingMap word charts hQ q
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (u:ℝ)) / (word.length : ℝ))) =
        Circle.exp (2 * Real.pi * (CircleChains.wordSign word d i.val : ℝ) * (u:ℝ)) := by
  classical
  have hp : (if (word.get i).2 then (x.val 0+1)/2 else 1-(x.val 0+1)/2) = (u:ℝ) := by
    cases hs : (word.get i).2 <;> simp only [hs, Bool.false_eq_true, ite_false,
      ite_true] at hx ⊢ <;> rw [hx] <;> ring
  have hh := circleAttachingMap_on_side word charts hdisk hQ b d q hq i x
  rw [hp] at hh
  rw [hh]
  by_cases hd : (word.get i).1 = d
  · rw [if_pos hd, hQexp, hx]
    simp only [CircleChains.wordSign, dif_pos i.isLt, hd, ite_true]
    cases hs : (word.get i).2
    · simp only [hs, Bool.false_eq_true, ite_false, Int.cast_neg, Int.cast_one]
      rw [show Real.pi * (1-2*(u:ℝ)+1) = -(2*Real.pi*(u:ℝ)) + 2*Real.pi by ring,
        Circle.exp_add_two_pi]
      congr 1
      ring
    · simp only [hs, ite_true, Int.cast_one]
      congr 1
      ring
  · rw [if_neg hd, quotientCircle_boundary_one hQ hQexp b]
    simp only [List.get_eq_getElem] at hd
    simp [CircleChains.wordSign, hd]

/-- The circular attaching map has the exact signed angle formula on each
actual equal arc of the polygon boundary. -/
lemma circleAttachingMap_angle_formula {e : ℕ} (word : Word e)
    [CWStructure (PolygonSurface word)] (charts : PolygonCharts word)
    (hdisk : charts.disk = complexDiskHomeomorph)
    (hQ : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ Circle)
    (hQexp : ∀ x : Disk 1,
      hQ (quotientProjection (referenceDiskPair.{0} 1) (ULift.up x)) =
        Circle.exp (Real.pi * (x.val 0 + 1)))
    (b : (referenceDiskPair.{0} 1).sub) (d : Fin e)
    (q : skeletalPair (PolygonSurface word) 1 ⟶ quotientPair (referenceDiskPair.{0} 1))
    (hq : SelectedCellCollapse (PolygonSurface word) 1 (charts.edges d) b q)
    (i : Fin word.length) (u : unitInterval) :
    circleAttachingMap word charts hQ q
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (u:ℝ)) / (word.length : ℝ))) =
        Circle.exp (2 * Real.pi * (CircleChains.wordSign word d i.val : ℝ) * (u:ℝ)) := by
  let v : unitInterval := if (word.get i).2 then u else unitInterval.symm u
  let x : Disk 1 := intervalToDiskOne v
  have hx : x.val 0 = if (word.get i).2 then 2*(u:ℝ)-1 else 1-2*(u:ℝ) := by
    cases hs : (word.get i).2 <;>
      simp only [x, v, hs, Bool.false_eq_true, ite_false, ite_true, intervalToDiskOne,
        WithLp.ofLp_toLp, unitInterval.coe_symm_eq] <;> ring
  exact circleAttachingMap_on_side_angle word charts hdisk hQ hQexp b d q hq i u x hx

lemma circleAttachingMap_basepoint {e : ℕ} (word : Word e) (hm : 0 < word.length)
    [CWStructure (PolygonSurface word)] (charts : PolygonCharts word)
    (hdisk : charts.disk = complexDiskHomeomorph)
    (hQ : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ Circle)
    (hQexp : ∀ x : Disk 1,
      hQ (quotientProjection (referenceDiskPair.{0} 1) (ULift.up x)) =
        Circle.exp (Real.pi * (x.val 0 + 1)))
    (b : (referenceDiskPair.{0} 1).sub) (d : Fin e)
    (q : skeletalPair (PolygonSurface word) 1 ⟶ quotientPair (referenceDiskPair.{0} 1))
    (hq : SelectedCellCollapse (PolygonSurface word) 1 (charts.edges d) b q) :
    circleAttachingMap word charts hQ q 1 = 1 := by
  have h := circleAttachingMap_angle_formula word charts hdisk hQ hQexp b d q hq
    ⟨0, hm⟩ 0
  simpa using h

/-- Compute the degree of each actual selected-cell attaching map using its
signed arcs and the explicitly proved primitive counterclockwise loop. -/
lemma polygon_attaching_degree {e : ℕ} (word : Word e) (hm : 0 < word.length)
    [CWStructure (PolygonSurface word)] (charts : PolygonCharts word)
    (hdisk : charts.disk = complexDiskHomeomorph)
    (hQ : quotientSpace (referenceDiskPair.{0} 1) ≃ₜ Circle)
    (hQexp : ∀ x : Disk 1,
      hQ (quotientProjection (referenceDiskPair.{0} 1) (ULift.up x)) =
        Circle.exp (Real.pi * (x.val 0 + 1)))
    (b : (referenceDiskPair.{0} 1).sub) (d : Fin e)
    (q : skeletalPair (PolygonSurface word) 1 ⟶ quotientPair (referenceDiskPair.{0} 1))
    (hq : SelectedCellCollapse (PolygonSurface word) 1 (charts.edges d) b q) :
    P202Specs.Degree.degree 1
      (chartAttachingMap (PolygonSurface word) 1 (referenceBoundarySphereHomeomorph.{0} 1)
        (circleTargetChart hQ) q charts.face) = exponentSum word d := by
  obtain ⟨eH, _⟩ := CircleGenerator.canonicalLoop_generator
  have hG : CircleChains.loopClass CircleChains.exponentialLoop
      CircleChains.exponentialLoop_zero CircleChains.exponentialLoop_one ≠ 0 :=
    CircleGenerator.canonicalLoop_ne_zero
  have hf := circleAttachingMap_basepoint word hm charts hdisk hQ hQexp b d q hq
  have hd := CircleChains.word_arc_degree_of_angle_formula word d sphereCircleHomeomorph eH
    (circleAttachingMap word charts hQ q) hf hG (polygonTime word.length hm)
    (polygonTime_zero word.length hm) (polygonTime_end word.length hm) (by
      intro i hi u
      rw [interpolate_polygonTime word.length hm i hi u, ← mul_div_assoc]
      exact circleAttachingMap_angle_formula word charts hdisk hQ hQexp b d q hq ⟨i,hi⟩ u)
  rwa [circleAttachingMap_conjugate] at hd

/-- The standard quotient circle chart supplies one common orientation for
all edges and makes the actual cellular column the word exponent column. -/
lemma polygonDifferentials_of_constant_exponents {e : ℕ} (word : Word e)
    (hm : 0 < word.length) [CWStructure (PolygonSurface word)]
    (hc : PolygonCellCounts (PolygonSurface word) e)
    (charts : PolygonCharts word) (hdisk : charts.disk = complexDiskHomeomorph)
    (coefficient : ℤ) (hcoeff : ∀ d : Fin e, exponentSum word d = coefficient) :
    PolygonDifferentials word charts coefficient := by
  let b : (referenceDiskPair.{0} 1).sub := CircleGenerator.standardInterval.endpoint 1
  apply polygonDifferentials_of_geometricDegrees word hc charts coefficient b
    (referenceBoundarySphereHomeomorph.{0} 1)
    (circleTargetChart CircleGenerator.quotientDiskCircle)
  intro d q hq
  calc
    _ = exponentSum word d := polygon_attaching_degree word hm charts hdisk
      CircleGenerator.quotientDiskCircle
      (fun x => CircleGenerator.quotientDiskCircle_projection (ULift.up x)) b d q hq
    _ = coefficient := hcoeff d


end AttachingBridge

/-- Combine the actual quotient CW construction and its computed attaching
maps. All hypotheses concern the finite word itself. -/
lemma polygonAttachingDifferentials_of_word {e : ℕ} (word : Word e)
    (hm : 0 < word.length)
    (hoccurs : ∀ j : Fin e, ∃ i : Fin word.length, (word.get i).1 = j)
    (hvertices : ∀ j, j ≤ word.length → polygonVertex word j = polygonVertex word 0)
    (coefficient : ℤ) (hcoefficient : ∀ i : Fin e, exponentSum word i = coefficient) :
    ∃ C : CWStructure (PolygonSurface word), letI := C
      PolygonCellCounts (PolygonSurface word) e ∧
        ∃ charts : PolygonCharts word, PolygonDifferentials word charts coefficient := by
  choose rep hrep using hoccurs
  let C := polygonCWStructure word rep hm hrep hvertices
  refine ⟨C, ?_⟩
  letI := C
  refine ⟨polygon_cellCounts word rep, polygonCharts word rep hrep, ?_⟩
  exact AttachingBridge.polygonDifferentials_of_constant_exponents word hm
    (polygon_cellCounts word rep) (polygonCharts word rep hrep) rfl coefficient hcoefficient

theorem attachingDifferentials : Expected.attachingDifferentials := by
  constructor
  · intro g
    cases g with
    | zero => exact genusZeroAttachingDifferentials
    | succ g =>
      apply polygonAttachingDifferentials_of_word (orientedWord (g+1))
        (by rw [orientedWord_length]; omega)
      · intro e
        obtain ⟨i,hi⟩ := orientedWord_positive_occurrence (g+1) e
        exact ⟨i,congrArg Prod.fst hi⟩
      · exact orientedVertices_single (g+1)
      · exact orientedExponent (g+1)
  · intro k hk
    apply polygonAttachingDifferentials_of_word (nonorientableWord k)
      (by rw [nonorientableWord_length]; omega)
    · intro e
      obtain ⟨i,hi⟩ := nonorientableWord_positive_occurrence k e
      exact ⟨i,congrArg Prod.fst hi⟩
    · exact nonorientableVertices_single k
    · exact nonorientableExponent k

theorem orientedHomology : Expected.orientedHomology :=
  orientedHomology_of_attachingDifferentials attachingDifferentials

theorem nonorientableHomology : Expected.nonorientableHomology :=
  nonorientableHomology_of_attachingDifferentials attachingDifferentials

end P202.Homology.SurfaceHomology
