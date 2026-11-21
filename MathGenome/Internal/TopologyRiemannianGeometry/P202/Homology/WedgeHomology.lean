import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.WedgeHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.MayerVietoris
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SubcomplexNeighborhoods
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Homology.Functor

/-!
Work on the finite wedge assertion of `prop:p202-homology-computations`.
The canonical inclusion maps are compared using the source's open cover,
basepoint-fixing deformations and reduced Mayer–Vietoris.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits DirectSum Topology
universe u v w
namespace P202.WedgeHomology
open P202Specs.WedgeHomology P202Specs.SingularChains

variable {ι : Type w} (X : ι → BasedSpace.{w})

@[simp] theorem inclusion_base (i : ι) : inclusion X i (X i).base = point X :=
  Quotient.sound (Or.inr ⟨rfl, trivial⟩)

/-- Maps out of the usual wedge are exactly continuous maps on the summands
with a common value at the basepoints. -/
def descend {Y : TopCat.{w}} (y : Y) (f : ∀ i, (X i).space ⟶ Y)
    (hf : ∀ i, f i (X i).base = y) : TopCat.of (Wedge X) ⟶ Y := by
  let g : Presentation X → Y := Sum.elim (fun _ => y) (fun p => f p.1 p.2)
  have hg : ∀ a, IsBase X a → g a = y := by
    intro a h
    cases a with
    | inl _ => rfl
    | inr p => rcases p with ⟨i, x⟩; change x = (X i).base at h; simpa [g, h] using hf i
  have hrel : ∀ a b, (wedgeSetoid X).r a b → g a = g b := by
    intro a b h
    rcases h with rfl | h
    · rfl
    · exact (hg a h.1).trans (hg b h.2).symm
  exact TopCat.ofHom ⟨Quotient.lift g hrel,
    (continuous_const.sumElim (continuous_sigma (fun i => (f i).hom.continuous))).quotient_lift hrel⟩

@[simp] theorem inclusion_descend {Y : TopCat.{w}} (y : Y)
    (f : ∀ i, (X i).space ⟶ Y) (hf : ∀ i, f i (X i).base = y) (i : ι) :
    inclusion X i ≫ descend X y f hf = f i := by
  ext x
  rfl

@[simp] theorem descend_point {Y : TopCat.{w}} (y : Y)
    (f : ∀ i, (X i).space ⟶ Y) (hf : ∀ i, f i (X i).base = y) :
    descend X y f hf (point X) = y := rfl

/-- For a nonempty family the presentation with an extra point is the usual
quotient of the disjoint union of the summands. -/
theorem sigma_projection_quotient [Nonempty ι] :
    IsQuotientMap (fun a : Σ i, (X i).space => inclusion X a.1 a.2) := by
  constructor
  · apply IsCoinducing.of_isOpen_preimage_iff_isOpen
    intro A
    constructor
    · intro hA
      apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
      exact isOpen_sum_iff.mpr ⟨isOpen_discrete _, hA⟩
    · intro hA
      exact hA.preimage (continuous_sigma (fun i => (inclusion X i).hom.continuous))
  · intro z
    induction z using Quotient.inductionOn with | _ z =>
      cases z with
      | inl _ =>
        obtain ⟨i⟩ := ‹Nonempty ι›
        exact ⟨⟨i, (X i).base⟩, inclusion_base X i⟩
      | inr a => exact ⟨a, rfl⟩

theorem sigma_projection_fibers (a b : Σ i, (X i).space) :
    inclusion X a.1 a.2 = inclusion X b.1 b.2 ↔
      a = b ∨ (a.2 = (X a.1).base ∧ b.2 = (X b.1).base) := by
  constructor
  · intro h
    rcases Quotient.exact h with h | h
    · exact Or.inl (Sum.inr.inj h)
    · exact Or.inr h
  · intro h
    rcases h with rfl | h
    · rfl
    · exact Quotient.sound (Or.inr h)

/-- Descend a family with an interval parameter. The ordinary product topology
is essential: continuity uses the proved product-quotient theorem. -/
def parameterValue {Y : TopCat.{w}} (y : C(unitInterval, Y))
    (H : ∀ i, C((X i).space × unitInterval, Y))
    (hb : ∀ i t, H i ((X i).base, t) = y t) (t : unitInterval) : Wedge X → Y := by
  let f : Presentation X → Y := Sum.elim (fun _ => y t) (fun a => H a.1 (a.2, t))
  have hf : ∀ a, IsBase X a → f a = y t := by
    intro a h
    cases a with
    | inl _ => rfl
    | inr a => rcases a with ⟨i, x⟩; change x = (X i).base at h; simpa [f, h] using hb i t
  exact Quotient.lift f (by
    intro a b h
    rcases h with rfl | h
    · rfl
    · exact (hf a h.1).trans (hf b h.2).symm)

def descendParameter {Y : TopCat.{w}} (y : C(unitInterval, Y))
    (H : ∀ i, C((X i).space × unitInterval, Y))
    (hb : ∀ i t, H i ((X i).base, t) = y t) : C(Wedge X × unitInterval, Y) := by
  refine ⟨fun zt => parameterValue X y H hb zt.2 zt.1, ?_⟩
  let q : Presentation X → Wedge X := Quotient.mk _
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  apply (P202.Topology.quotientProductInterval q hq).continuous_iff.mpr
  have hSigma : Continuous (fun p : Σ i, (X i).space × unitInterval => H p.1 p.2) :=
    continuous_sigma (fun i => (H i).continuous)
  have hi : Continuous (fun p : (Σ i, (X i).space) × unitInterval => H p.1.1 (p.1.2, p.2)) :=
    hSigma.comp
      (Homeomorph.sigmaProdDistrib (X := fun i => (X i).space) (Y := unitInterval)).continuous
  convert ((y.continuous.comp continuous_snd).sumElim hi).comp
    (Homeomorph.sumProdDistrib (X := PUnit.{w+1})
      (Y := Σ i, (X i).space) (Z := unitInterval)).continuous using 1
  funext ⟨a, t⟩
  cases a <;> rfl

@[simp] theorem descendParameter_inclusion {Y : TopCat.{w}} (y : C(unitInterval, Y))
    (H : ∀ i, C((X i).space × unitInterval, Y))
    (hb : ∀ i t, H i ((X i).base, t) = y t) (i : ι) (x : (X i).space) (t : unitInterval) :
    descendParameter X y H hb (inclusion X i x, t) = H i (x, t) := rfl

@[simp] theorem descendParameter_point {Y : TopCat.{w}} (y : C(unitInterval, Y))
    (H : ∀ i, C((X i).space × unitInterval, Y))
    (hb : ∀ i t, H i ((X i).base, t) = y t) (t : unitInterval) :
    descendParameter X y H hb (point X, t) = y t := rfl

/-- A basepoint-fixing family of homotopies descends with its fixed point. -/
def wedgeHomotopy
    (H : ∀ i, C((X i).space × unitInterval, (X i).space))
    (hfixed : ∀ i t, H i ((X i).base, t) = (X i).base) :
    C(Wedge X × unitInterval, Wedge X) :=
  descendParameter (Y := TopCat.of (Wedge X)) X (ContinuousMap.const _ (point X))
    (fun i => (inclusion X i).hom.comp (H i))
    (fun i t => by change inclusion X i (H i ((X i).base, t)) = point X
                   rw [hfixed, inclusion_base])

@[simp] theorem wedgeHomotopy_point
    (H : ∀ i, C((X i).space × unitInterval, (X i).space))
    (hfixed : ∀ i t, H i ((X i).base, t) = (X i).base) (t : unitInterval) :
    wedgeHomotopy X H hfixed (point X, t) = point X := rfl

@[simp] theorem wedgeHomotopy_inclusion
    (H : ∀ i, C((X i).space × unitInterval, (X i).space))
    (hfixed : ∀ i t, H i ((X i).base, t) = (X i).base)
    (i : ι) (x : (X i).space) (t : unitInterval) :
    wedgeHomotopy X H hfixed (inclusion X i x, t) = inclusion X i (H i (x, t)) := rfl

theorem wedgeHomotopy_zero
    (H : ∀ i, C((X i).space × unitInterval, (X i).space))
    (hfixed : ∀ i t, H i ((X i).base, t) = (X i).base)
    (hzero : ∀ i x, H i (x, 0) = x) (z : Wedge X) :
    wedgeHomotopy X H hfixed (z, 0) = z := by
  induction z using Quotient.inductionOn with | _ a =>
    cases a with
    | inl a => rfl
    | inr a => exact congrArg (inclusion X a.1) (hzero a.1 a.2)

theorem wedgeHomotopy_one
    (H : ∀ i, C((X i).space × unitInterval, (X i).space))
    (hfixed : ∀ i t, H i ((X i).base, t) = (X i).base)
    (hone : ∀ i x, H i (x, 1) = (X i).base) (z : Wedge X) :
    wedgeHomotopy X H hfixed (z, 1) = point X := by
  induction z using Quotient.inductionOn with | _ a =>
    cases a with
    | inl a => rfl
    | inr a =>
      change inclusion X a.1 (H a.1 (a.2, 1)) = point X
      rw [hone, inclusion_base]

/-- Based contractions on the summands give a contraction on their usual
wedge. This will apply to the neighborhoods in the open-cover intersection. -/
theorem contractible_of_contractions
    (H : ∀ i, C((X i).space × unitInterval, (X i).space))
    (hzero : ∀ i x, H i (x, 0) = x)
    (hone : ∀ i x, H i (x, 1) = (X i).base)
    (hfixed : ∀ i t, H i ((X i).base, t) = (X i).base) :
    ContractibleSpace (Wedge X) := by
  let y : C(unitInterval, Wedge X) := ContinuousMap.const _ (point X)
  let F : ∀ i, C((X i).space × unitInterval, Wedge X) :=
    fun i => (inclusion X i).hom.comp (H i)
  have hb : ∀ i t, F i ((X i).base, t) = y t := by
    intro i t
    change inclusion X i (H i ((X i).base, t)) = point X
    rw [hfixed, inclusion_base]
  let K := descendParameter (Y := TopCat.of (Wedge X)) X y F hb
  apply (contractible_iff_id_nullhomotopic (Wedge X)).mpr
  refine ⟨point X, ⟨{
    toFun := fun tx => K (tx.2, tx.1)
    continuous_toFun := K.continuous.comp (continuous_snd.prodMk continuous_fst)
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro z
    induction z using Quotient.inductionOn with | _ z =>
      cases z with
      | inl _ => rfl
      | inr a =>
        change inclusion X a.1 (H a.1 (a.2, 0)) = inclusion X a.1 a.2
        rw [hzero]
  · intro z
    induction z using Quotient.inductionOn with | _ z =>
      cases z with
      | inl _ => rfl
      | inr a =>
        change inclusion X a.1 (H a.1 (a.2, 1)) = point X
        rw [hone, inclusion_base]

/-- Collapse all but one summand to its basepoint. This construction does not
require good basepoints or finiteness. -/
def coordinateMap (i j : ι) : (X j).space ⟶ (X i).space := by
  classical
  exact if h : j = i then eqToHom (congrArg (fun k => (X k).space) h)
    else TopCat.ofHom (ContinuousMap.const _ (X i).base)

@[simp] theorem coordinateMap_self (i : ι) : coordinateMap X i i = 𝟙 _ := by
  classical
  simp [coordinateMap]

theorem coordinateMap_ne (i j : ι) (h : j ≠ i) :
    coordinateMap X i j = TopCat.ofHom (ContinuousMap.const _ (X i).base) := by
  classical
  simp [coordinateMap, h]

@[simp] theorem coordinateMap_base (i j : ι) :
    coordinateMap X i j (X j).base = (X i).base := by
  classical
  by_cases h : j = i
  · subst j; simp
  · rw [coordinateMap_ne X i j h]; rfl

def retraction (i : ι) : TopCat.of (Wedge X) ⟶ (X i).space :=
  descend X (X i).base (coordinateMap X i) (coordinateMap_base X i)

@[simp] theorem inclusion_retraction (i j : ι) :
    inclusion X j ≫ retraction X i = coordinateMap X i j := rfl

@[simp] theorem retraction_point (i : ι) : retraction X i (point X) = (X i).base := rfl

theorem inclusion_injective (i : ι) : Function.Injective (inclusion X i) := by
  intro x y h
  have hi := congrArg (retraction X i) h
  change coordinateMap X i i x = coordinateMap X i i y at hi
  rw [coordinateMap_self] at hi
  exact hi

section Coefficients
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

@[simp] theorem inclusionSum_lof [DecidableEq ι] (i : ι) (n : ℕ)
    (x : reducedHomology R M (X i).space (n : ℤ)) :
    inclusionSum X R M n
        (DirectSum.lof R ι (fun j => reducedHomology R M (X j).space (n : ℤ)) i x) =
      (reducedHomologyFunctor R M (n : ℤ)).map (inclusion X i) x := by
  classical
  exact DirectSum.toModule_lof (R := R)
    (M := fun j => reducedHomology R M (X j).space (n : ℤ))
    (φ := fun j => ((reducedHomologyFunctor R M (n : ℤ)).map (inclusion X j)).hom) i x

/-- A constant map factors through the actual point and hence induces zero on
the upstream augmented homology, including in degree zero. -/
theorem reducedHomologyMap_const {Y Z : TopCat.{w}} (z : Z) (n : ℤ) :
    (reducedHomologyFunctor R M n).map
      (TopCat.ofHom (ContinuousMap.const Y z)) = 0 := by
  let p : Y ⟶ P202Specs.SingularDegreeZero.point.{w} :=
    TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let q : P202Specs.SingularDegreeZero.point.{w} ⟶ Z :=
    TopCat.ofHom (ContinuousMap.const _ z)
  have h : (reducedHomologyFunctor R M n).map q = 0 :=
    (P202.SingularDegreeZero.pointReduced R M n).eq_of_src _ _
  change (reducedHomologyFunctor R M n).map (p ≫ q) = 0
  rw [Functor.map_comp, h, comp_zero]

theorem coordinateMap_homology_ne (i j : ι) (h : j ≠ i) (n : ℤ) :
    (reducedHomologyFunctor R M n).map (coordinateMap X i j) = 0 := by
  rw [coordinateMap_ne X i j h]
  exact reducedHomologyMap_const R M _ n

/-- The induced retraction recovers the corresponding direct-sum coordinate. -/
theorem homology_retraction_inclusionSum (i : ι) (n : ℕ) :
    ((reducedHomologyFunctor R M (n : ℤ)).map (retraction X i)).hom.comp
        (inclusionSum X R M n) =
      DirectSum.component R ι (fun j => reducedHomology R M (X j).space (n : ℤ)) i := by
  classical
  apply DirectSum.linearMap_ext
  intro j
  apply LinearMap.ext
  intro x
  change ((reducedHomologyFunctor R M (n : ℤ)).map (retraction X i)).hom
    ((inclusionSum X R M n) ((DirectSum.lof R ι (fun k => reducedHomology R M (X k).space (n : ℤ)) j) x)) =
    DirectSum.component R ι (fun k => reducedHomology R M (X k).space (n : ℤ)) i ((DirectSum.lof R ι (fun k => reducedHomology R M (X k).space (n : ℤ)) j) x)
  rw [inclusionSum, DirectSum.toModule_lof]
  change ((reducedHomologyFunctor R M (n : ℤ)).map (inclusion X j) ≫
    (reducedHomologyFunctor R M (n : ℤ)).map (retraction X i)) x = _
  rw [← Functor.map_comp, inclusion_retraction]
  by_cases h : j = i
  · subst j
    simp [DirectSum.component.lof_self]
  · rw [coordinateMap_homology_ne X R M i j h]
    simp [DirectSum.component.of, h]

/-- In particular injectivity needs neither the good-point condition nor
finiteness. Surjectivity is the part that uses the good neighborhoods. -/
theorem inclusionSum_injective (n : ℕ) : Function.Injective (inclusionSum X R M n) := by
  intro a b h
  apply DirectSum.ext_component R
  intro i
  have hi := congrArg (((reducedHomologyFunctor R M (n : ℤ)).map (retraction X i)).hom) h
  exact (LinearMap.congr_fun (homology_retraction_inclusionSum X R M i n) a).symm.trans
    (hi.trans (LinearMap.congr_fun (homology_retraction_inclusionSum X R M i n) b))

end Coefficients

/-- The empty wedge is a point, rather than the empty space. -/
instance [IsEmpty ι] : Subsingleton (Wedge X) where
  allEq a b := by
    induction a using Quotient.inductionOn with | _ a =>
      induction b using Quotient.inductionOn with | _ b =>
        cases a with
        | inl a =>
          cases b with
          | inl b => rfl
          | inr b => exact isEmptyElim b.1
        | inr a => exact isEmptyElim a.1

instance : Nonempty (Wedge X) := ⟨point X⟩

/-- There is no extra topological component from the presentation point. -/
def emptyWedge_homeomorph [IsEmpty ι] : Wedge X ≃ₜ PUnit.{w+1} := by
  letI : Unique (Wedge X) := ⟨⟨point X⟩, fun _ => Subsingleton.elim _ _⟩
  exact Homeomorph.homeomorphOfUnique _ _

theorem retraction_inclusion [Subsingleton ι] (i : ι) :
    retraction X i ≫ inclusion X i = 𝟙 _ := by
  ext z
  induction z using Quotient.inductionOn with | _ z =>
    cases z with
    | inl z => exact inclusion_base X i
    | inr z =>
      rcases z with ⟨j, x⟩
      have h : j = i := Subsingleton.elim _ _
      subst j
      change inclusion X i (coordinateMap X i i x) = inclusion X i x
      rw [coordinateMap_self]
      rfl

/-- In the one-member case the actual inclusion is an isomorphism of spaces. -/
def singleWedgeIso [Subsingleton ι] (i : ι) : (X i).space ≅ TopCat.of (Wedge X) where
  hom := inclusion X i
  inv := retraction X i
  hom_inv_id := by rw [inclusion_retraction, coordinateMap_self]
  inv_hom_id := retraction_inclusion X i

section BaseCases
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

theorem emptyWedge_reducedHomology [IsEmpty ι] (n : ℤ) :
    IsZero (reducedHomology R M (TopCat.of (Wedge X)) n) :=
  P202.PrismHomotopy.contractible R M (TopCat.of (Wedge X)) n

theorem inclusionSum_empty_bijective [IsEmpty ι] (n : ℕ) :
    Function.Bijective (inclusionSum X R M n) := by
  have := ModuleCat.subsingleton_of_isZero (emptyWedge_reducedHomology X R M n)
  exact ⟨inclusionSum_injective X R M n, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem inclusionSum_single_bijective [Subsingleton ι] (i : ι) (n : ℕ) :
    Function.Bijective (inclusionSum X R M n) := by
  classical
  refine ⟨inclusionSum_injective X R M n, ?_⟩
  intro y
  refine ⟨DirectSum.lof R ι _ i
    (((reducedHomologyFunctor R M (n : ℤ)).map (retraction X i)) y), ?_⟩
  rw [inclusionSum_lof]
  change ((reducedHomologyFunctor R M (n : ℤ)).map (retraction X i) ≫
    (reducedHomologyFunctor R M (n : ℤ)).map (inclusion X i)) y = y
  rw [← Functor.map_comp, retraction_inclusion, CategoryTheory.Functor.map_id]
  rfl

end BaseCases

section OpenCover

/-- Sets assembled from subsets of the summands containing their basepoints.
This definition descends membership itself, so it retains the quotient topology. -/
def gluedSet (Z : ∀ i, Set (X i).space) (hZ : ∀ i, (X i).base ∈ Z i) : Set (Wedge X) := by
  let p : Presentation X → Prop := Sum.elim (fun _ => True) (fun a => a.2 ∈ Z a.1)
  have hp : ∀ a, IsBase X a → p a := by
    intro a h
    cases a with
    | inl _ => trivial
    | inr a => rcases a with ⟨i, x⟩; change x = (X i).base at h; simpa [p, h] using hZ i
  exact Quotient.lift p (by
    intro a b h
    apply propext
    rcases h with rfl | h
    · rfl
    · exact iff_of_true (hp a h.1) (hp b h.2))

@[simp] theorem point_mem_gluedSet (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) : point X ∈ gluedSet X Z hZ := trivial

@[simp] theorem inclusion_mem_gluedSet (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) (i : ι) (x : (X i).space) :
    inclusion X i x ∈ gluedSet X Z hZ ↔ x ∈ Z i := Iff.rfl

theorem isOpen_gluedSet (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) (hopen : ∀ i, IsOpen (Z i)) :
    IsOpen (gluedSet X Z hZ) := by
  apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
  apply isOpen_sum_iff.mpr
  exact ⟨isOpen_univ, isOpen_sigma_iff.mpr hopen⟩

theorem isClosed_gluedSet (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) (hclosed : ∀ i, IsClosed (Z i)) :
    IsClosed (gluedSet X Z hZ) := by
  apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
  apply isClosed_sum_iff.mpr
  exact ⟨isClosed_univ, isClosed_sigma_iff.mpr hclosed⟩

theorem gluedSet_basepoints :
    gluedSet X (fun i => {(X i).base}) (fun _ => Set.mem_singleton _) = {point X} := by
  ext z
  induction z using Quotient.inductionOn with | _ z =>
    cases z with
    | inl _ => exact iff_of_true trivial rfl
    | inr a =>
      rcases a with ⟨i, x⟩
      change x = (X i).base ↔ inclusion X i x = point X
      rw [← inclusion_base X i]
      exact (inclusion_injective X i).eq_iff.symm

theorem isClosed_point (h : ∀ i, IsClosed ({(X i).base} : Set (X i).space)) :
    IsClosed ({point X} : Set (Wedge X)) := by
  rw [← gluedSet_basepoints X]
  exact isClosed_gluedSet X _ _ h

/-- Restrict each summand to a neighborhood of its basepoint. -/
def subspaceFamily (Z : ∀ i, Set (X i).space) (hZ : ∀ i, (X i).base ∈ Z i) :
    ι → BasedSpace.{w} := fun i => ⟨TopCat.of (Z i), ⟨(X i).base, hZ i⟩⟩

/-- The map on disjoint-union presentations before identifying basepoints. -/
def subspacePresentation (Z : ∀ i, Set (X i).space) (hZ : ∀ i, (X i).base ∈ Z i) :
    Presentation (subspaceFamily X Z hZ) → Presentation X :=
  Sum.map id (Sigma.map id (fun _ => Subtype.val))

theorem subspacePresentation_injective (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) : Function.Injective (subspacePresentation X Z hZ) := by
  exact Sum.map_injective.mpr ⟨Function.injective_id,
    Function.injective_id.sigma_map (fun _ => Subtype.val_injective)⟩

@[simp] theorem subspacePresentation_isBase (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) (a : Presentation (subspaceFamily X Z hZ)) :
    IsBase X (subspacePresentation X Z hZ a) ↔ IsBase (subspaceFamily X Z hZ) a := by
  cases a with
  | inl a => rfl
  | inr a =>
    change a.2.val = (X a.1).base ↔ a.2 = ⟨(X a.1).base, hZ a.1⟩
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- The induced map into the original wedge. -/
def subspaceWedgeMap (Z : ∀ i, Set (X i).space) (hZ : ∀ i, (X i).base ∈ Z i) :
    TopCat.of (Wedge (subspaceFamily X Z hZ)) ⟶ TopCat.of (Wedge X) :=
  descend (subspaceFamily X Z hZ) (point X)
    (fun i => TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ inclusion X i)
    (fun i => inclusion_base X i)

@[simp] theorem subspaceWedgeMap_mk (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) (a : Presentation (subspaceFamily X Z hZ)) :
    subspaceWedgeMap X Z hZ (Quotient.mk _ a) =
      Quotient.mk (wedgeSetoid X) (subspacePresentation X Z hZ a) := by
  cases a <;> rfl

@[simp] theorem subspaceWedgeMap_point (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) :
    subspaceWedgeMap X Z hZ (point _) = point X := rfl

@[simp] theorem subspaceWedgeMap_inclusion (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) (i : ι) (x : Z i) :
    subspaceWedgeMap X Z hZ (inclusion (subspaceFamily X Z hZ) i x) = inclusion X i x := rfl

theorem subspaceWedgeMap_mem (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) (z : Wedge (subspaceFamily X Z hZ)) :
    subspaceWedgeMap X Z hZ z ∈ gluedSet X Z hZ := by
  induction z using Quotient.inductionOn with | _ a =>
    cases a with
    | inl a => trivial
    | inr a => exact a.2.property

/-- Restrict the induced map to its actual image. -/
def gluedMap (Z : ∀ i, Set (X i).space) (hZ : ∀ i, (X i).base ∈ Z i) :
    C(Wedge (subspaceFamily X Z hZ), gluedSet X Z hZ) :=
  ⟨fun z => ⟨subspaceWedgeMap X Z hZ z, subspaceWedgeMap_mem X Z hZ z⟩,
    (subspaceWedgeMap X Z hZ).hom.continuous.subtype_mk _⟩

theorem gluedMap_injective (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) : Function.Injective (gluedMap X Z hZ) := by
  intro a b h
  have h := congrArg Subtype.val h
  induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
      change subspaceWedgeMap X Z hZ (Quotient.mk _ a) =
        subspaceWedgeMap X Z hZ (Quotient.mk _ b) at h
      rw [subspaceWedgeMap_mk, subspaceWedgeMap_mk] at h
      apply Quotient.sound
      rcases Quotient.exact h with h | h
      · exact Or.inl (subspacePresentation_injective X Z hZ h)
      · exact Or.inr ⟨(subspacePresentation_isBase X Z hZ a).mp h.1,
          (subspacePresentation_isBase X Z hZ b).mp h.2⟩

/-- The restricted presentation is a continuous open surjection. This is where
openness of the neighborhoods enters the quotient-subspace comparison. -/
theorem gluedMap_quotient (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) (hopen : ∀ i, IsOpen (Z i)) :
    IsQuotientMap (gluedMap X Z hZ) := by
  let q : Presentation X → Wedge X := Quotient.mk _
  let B := gluedSet X Z hZ
  let j : Presentation (subspaceFamily X Z hZ) → q ⁻¹' B :=
    fun a => ⟨subspacePresentation X Z hZ a, by
      cases a with
      | inl a => trivial
      | inr a => exact a.2.property⟩
  have hc : Continuous (subspacePresentation X Z hZ) :=
    continuous_id.sumMap (Continuous.sigma_map (fun _ => continuous_subtype_val))
  have ho : IsOpenMap (subspacePresentation X Z hZ) :=
    IsOpenMap.id.sumMap (isOpenMap_sigma_map.mpr (fun i => (hopen i).isOpenMap_subtype_val))
  have hj : IsQuotientMap j := by
    apply (ho.subtype_mk _).isQuotientMap (hc.subtype_mk _)
    intro ⟨a, ha⟩
    cases a with
    | inl a => exact ⟨.inl a, rfl⟩
    | inr a => exact ⟨.inr ⟨a.1, ⟨a.2, ha⟩⟩, rfl⟩
  have hq : IsQuotientMap (B.restrictPreimage q) :=
    isQuotientMap_quotient_mk'.restrictPreimage_isOpen (isOpen_gluedSet X Z hZ hopen)
  have hcomp : (B.restrictPreimage q) ∘ j =
      (gluedMap X Z hZ) ∘ (Quotient.mk (wedgeSetoid (subspaceFamily X Z hZ))) := by
    funext a
    apply Subtype.ext
    exact (subspaceWedgeMap_mk X Z hZ a).symm
  apply IsQuotientMap.of_comp
    (f := Quotient.mk (wedgeSetoid (subspaceFamily X Z hZ)))
    continuous_quotient_mk' (gluedMap X Z hZ).continuous
  rw [← hcomp]
  exact hq.comp hj

/-- Open subspaces glued at the basepoints have exactly their subspace topology
in the original wedge. -/
def gluedHomeomorph (Z : ∀ i, Set (X i).space)
    (hZ : ∀ i, (X i).base ∈ Z i) (hopen : ∀ i, IsOpen (Z i)) :
    Wedge (subspaceFamily X Z hZ) ≃ₜ gluedSet X Z hZ :=
  (isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨gluedMap_quotient X Z hZ hopen, gluedMap_injective X Z hZ⟩).homeomorph _

/-- Chosen data from the source's good-point hypothesis, without any extra
homological or connectedness assumptions. -/
structure Neighborhoods where
  sets : ∀ i, Set (X i).space
  isOpen : ∀ i, IsOpen (sets i)
  deformation : ∀ i, P202.Cellular.StrongDeformationRetracts {(X i).base} (sets i)

namespace Neighborhoods
variable {X}

theorem base_mem (N : Neighborhoods X) (i : ι) : (X i).base ∈ N.sets i :=
  (N.deformation i).1 (Set.mem_singleton _)

def ofGood (h : ∀ i, Good (X i)) : Neighborhoods X where
  sets i := Classical.choose (h i).2
  isOpen i := (Classical.choose_spec (h i).2).1
  deformation i := (Classical.choose_spec (h i).2).2

/-- The common open neighborhood of the wedge point. -/
def core (N : Neighborhoods X) : Set (Wedge X) := gluedSet X N.sets N.base_mem

theorem core_isOpen (N : Neighborhoods X) : IsOpen N.core :=
  isOpen_gluedSet X N.sets N.base_mem N.isOpen

/-- Keep the summands indexed by S and thicken them by all other basepoint
neighborhoods. This is open even though individual wedge summands need not be. -/
def expanded (N : Neighborhoods X) (S : Set ι) : Set (Wedge X) := by
  classical
  exact gluedSet X (fun i => if i ∈ S then Set.univ else N.sets i)
    (fun i => by split <;> simp_all [base_mem])

@[simp] theorem inclusion_mem_expanded (N : Neighborhoods X) (S : Set ι)
    (i : ι) (x : (X i).space) :
    inclusion X i x ∈ N.expanded S ↔ i ∈ S ∨ x ∈ N.sets i := by
  classical
  change (x ∈ (if i ∈ S then Set.univ else N.sets i)) ↔ _
  by_cases h : i ∈ S <;> simp [h]

@[simp] theorem point_mem_expanded (N : Neighborhoods X) (S : Set ι) :
    point X ∈ N.expanded S := point_mem_gluedSet _ _ _

theorem expanded_isOpen (N : Neighborhoods X) (S : Set ι) : IsOpen (N.expanded S) := by
  classical
  apply isOpen_gluedSet
  intro i
  split
  · exact isOpen_univ
  · exact N.isOpen i

theorem expanded_union_compl (N : Neighborhoods X) (S : Set ι) :
    N.expanded S ∪ N.expanded Sᶜ = Set.univ := by
  classical
  ext z
  induction z using Quotient.inductionOn with | _ z =>
    cases z with
    | inl _ => exact iff_of_true (Or.inl (N.point_mem_expanded S)) trivial
    | inr z =>
      rcases z with ⟨i, x⟩
      apply iff_of_true _ trivial
      by_cases h : i ∈ S
      · exact Or.inl ((N.inclusion_mem_expanded S i x).mpr (Or.inl h))
      · exact Or.inr ((N.inclusion_mem_expanded Sᶜ i x).mpr (Or.inl h))

theorem expanded_inter_compl (N : Neighborhoods X) (S : Set ι) :
    N.expanded S ∩ N.expanded Sᶜ = N.core := by
  classical
  ext z
  induction z using Quotient.inductionOn with | _ z =>
    cases z with
    | inl _ =>
      exact iff_of_true ⟨N.point_mem_expanded S, N.point_mem_expanded Sᶜ⟩ (point_mem_gluedSet _ _ _)
    | inr z =>
      rcases z with ⟨i, x⟩
      change (inclusion X i x ∈ N.expanded S ∧ inclusion X i x ∈ N.expanded Sᶜ) ↔ x ∈ N.sets i
      rw [N.inclusion_mem_expanded S i x, N.inclusion_mem_expanded Sᶜ i x]
      simp only [Set.mem_compl_iff]
      tauto

/-- The actual basepoint-fixing contraction supplied in each neighborhood. -/
def contraction (N : Neighborhoods X) (i : ι) :
    C(N.sets i × unitInterval, N.sets i) := Classical.choose (N.deformation i).2

@[simp] theorem contraction_zero (N : Neighborhoods X) (i : ι) (x : N.sets i) :
    N.contraction i (x, 0) = x := (Classical.choose_spec (N.deformation i).2).1 x

@[simp] theorem contraction_one (N : Neighborhoods X) (i : ι) (x : N.sets i) :
    N.contraction i (x, 1) = ⟨(X i).base, N.base_mem i⟩ :=
  Subtype.ext ((Classical.choose_spec (N.deformation i).2).2.1 x)

@[simp] theorem contraction_base (N : Neighborhoods X) (i : ι) (t : unitInterval) :
    N.contraction i (⟨(X i).base, N.base_mem i⟩, t) = ⟨(X i).base, N.base_mem i⟩ :=
  (Classical.choose_spec (N.deformation i).2).2.2 _ t rfl

/-- Transfer the wedge contraction to the open core with its subspace topology. -/
def coreHomotopy (N : Neighborhoods X) : C(N.core × unitInterval, N.core) := by
  let Y := subspaceFamily X N.sets N.base_mem
  let e := gluedHomeomorph X N.sets N.base_mem N.isOpen
  let K := wedgeHomotopy Y N.contraction N.contraction_base
  exact ⟨fun zt => e (K (e.symm zt.1, zt.2)),
    e.continuous.comp (K.continuous.comp
      ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))⟩

@[simp] theorem coreHomotopy_zero (N : Neighborhoods X) (z : N.core) :
    N.coreHomotopy (z, 0) = z := by
  change gluedHomeomorph X N.sets N.base_mem N.isOpen
    (wedgeHomotopy (subspaceFamily X N.sets N.base_mem) N.contraction N.contraction_base
      ((gluedHomeomorph X N.sets N.base_mem N.isOpen).symm z, 0)) = z
  rw [wedgeHomotopy_zero _ _ _ N.contraction_zero, Homeomorph.apply_symm_apply]

@[simp] theorem coreHomotopy_one (N : Neighborhoods X) (z : N.core) :
    N.coreHomotopy (z, 1) = ⟨point X, point_mem_gluedSet _ _ _⟩ := by
  change gluedHomeomorph X N.sets N.base_mem N.isOpen
    (wedgeHomotopy (subspaceFamily X N.sets N.base_mem) N.contraction N.contraction_base
      ((gluedHomeomorph X N.sets N.base_mem N.isOpen).symm z, 1)) = _
  rw [wedgeHomotopy_one _ _ _ N.contraction_one]
  rfl

@[simp] theorem coreHomotopy_point (N : Neighborhoods X) (t : unitInterval) :
    N.coreHomotopy (⟨point X, point_mem_gluedSet _ _ _⟩, t) =
      ⟨point X, point_mem_gluedSet _ _ _⟩ := by
  let e := gluedHomeomorph X N.sets N.base_mem N.isOpen
  have he : e (point (subspaceFamily X N.sets N.base_mem)) =
      ⟨point X, point_mem_gluedSet _ _ _⟩ := rfl
  change e (wedgeHomotopy _ N.contraction N.contraction_base (e.symm _, t)) = _
  rw [← he, e.symm_apply_apply, wedgeHomotopy_point]

/-- The core really strongly retracts onto the wedge point. -/
theorem core_deformation (N : Neighborhoods X) :
    P202.Cellular.StrongDeformationRetracts {point X} N.core := by
  refine ⟨Set.singleton_subset_iff.mpr (point_mem_gluedSet _ _ _),
    N.coreHomotopy, N.coreHomotopy_zero, ?_, ?_⟩
  · intro z
    rw [N.coreHomotopy_one]
    rfl
  · intro z t hz
    have hz : z = ⟨point X, point_mem_gluedSet _ _ _⟩ := Subtype.ext hz
    subst z
    exact N.coreHomotopy_point t

instance core_nonempty (N : Neighborhoods X) : Nonempty N.core :=
  ⟨⟨point X, point_mem_gluedSet _ _ _⟩⟩

theorem core_contractible (N : Neighborhoods X) : ContractibleSpace N.core := by
  apply (contractible_iff_id_nullhomotopic N.core).mpr
  refine ⟨⟨point X, point_mem_gluedSet _ _ _⟩, ⟨{
    toFun := fun tz => N.coreHomotopy (tz.2, tz.1)
    continuous_toFun := N.coreHomotopy.continuous.comp (continuous_snd.prodMk continuous_fst)
    map_zero_left := N.coreHomotopy_zero
    map_one_left := N.coreHomotopy_one }⟩⟩

theorem core_reducedHomology (N : Neighborhoods X)
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℤ) :
    IsZero (reducedHomology R M (TopCat.of N.core) n) := by
  letI := N.core_contractible
  exact P202.PrismHomotopy.contractible R M (TopCat.of N.core) n

/-- The wedge of a selected set of summands, with its usual quotient topology. -/
def selectedFamily (S : Set ι) : S → BasedSpace.{w} := fun i => X i.val

def subwedgeInclusion (S : Set ι) :
    TopCat.of (Wedge (selectedFamily (X := X) S)) ⟶ TopCat.of (Wedge X) :=
  descend (selectedFamily (X := X) S) (point X) (fun i => inclusion X i.val)
    (fun i => inclusion_base X i.val)

@[simp] theorem subwedgeInclusion_point (S : Set ι) :
    subwedgeInclusion (X := X) S (point _) = point X := rfl

@[simp] theorem subwedgeInclusion_inclusion (S : Set ι) (i : S) (x : (X i.val).space) :
    subwedgeInclusion (X := X) S (inclusion (selectedFamily (X := X) S) i x) =
      inclusion X i.val x := rfl

/-- The summand neighborhoods used in an expanded piece. -/
def expandedSets (N : Neighborhoods X) (S : Set ι) (i : ι) : Set (X i).space := by
  classical
  exact if i ∈ S then Set.univ else N.sets i

theorem expandedSets_base (N : Neighborhoods X) (S : Set ι) (i : ι) :
    (X i).base ∈ N.expandedSets S i := by
  classical
  unfold expandedSets
  split
  · trivial
  · exact N.base_mem i

theorem expandedSets_open (N : Neighborhoods X) (S : Set ι) (i : ι) :
    IsOpen (N.expandedSets S i) := by
  classical
  unfold expandedSets
  split
  · exact isOpen_univ
  · exact N.isOpen i

def expandedFamily (N : Neighborhoods X) (S : Set ι) : ι → BasedSpace.{w} :=
  subspaceFamily X (N.expandedSets S) (N.expandedSets_base S)

/-- Contract the unused neighborhoods and fix the selected summands. -/
def expandedHomotopy (N : Neighborhoods X) (S : Set ι) (i : ι) :
    C((N.expandedFamily S i).space × unitInterval, (N.expandedFamily S i).space) := by
  classical
  by_cases hi : i ∈ S
  · exact ⟨Prod.fst, continuous_fst⟩
  · have he : N.expandedSets S i = N.sets i := by simp [expandedSets, hi]
    let e : N.expandedSets S i ≃ₜ N.sets i := Homeomorph.setCongr he
    exact ⟨fun xt => e.symm (N.contraction i (e xt.1, xt.2)),
      e.symm.continuous.comp ((N.contraction i).continuous.comp
        ((e.continuous.comp continuous_fst).prodMk continuous_snd))⟩

@[simp] theorem expandedHomotopy_zero (N : Neighborhoods X) (S : Set ι) (i : ι)
    (x : (N.expandedFamily S i).space) : N.expandedHomotopy S i (x, 0) = x := by
  classical
  by_cases hi : i ∈ S
  · simp [expandedHomotopy, hi]
  · simp [expandedHomotopy, hi]

@[simp] theorem expandedHomotopy_base (N : Neighborhoods X) (S : Set ι) (i : ι)
    (t : unitInterval) :
    N.expandedHomotopy S i ((N.expandedFamily S i).base, t) = (N.expandedFamily S i).base := by
  classical
  by_cases hi : i ∈ S
  · simp [expandedHomotopy, hi]
  · apply Subtype.ext
    change (N.expandedHomotopy S i (⟨(X i).base, _⟩, t)).val = (X i).base
    simpa [expandedHomotopy, hi, Homeomorph.setCongr] using
      congrArg Subtype.val (N.contraction_base i t)

theorem expandedHomotopy_one_selected (N : Neighborhoods X) (S : Set ι) (i : ι)
    (hi : i ∈ S) (x : (N.expandedFamily S i).space) :
    N.expandedHomotopy S i (x, 1) = x := by
  classical
  simp [expandedHomotopy, hi]

theorem expandedHomotopy_one_unused (N : Neighborhoods X) (S : Set ι) (i : ι)
    (hi : i ∉ S) (x : (N.expandedFamily S i).space) :
    N.expandedHomotopy S i (x, 1) = (N.expandedFamily S i).base := by
  classical
  apply Subtype.ext
  simp [expandedHomotopy, hi, Homeomorph.setCongr]
  rfl

/-- Collapse the unused summands to the point of the selected subwedge. -/
def selectedMap (N : Neighborhoods X) (S : Set ι) (i : ι) :
    (N.expandedFamily S i).space ⟶ TopCat.of (Wedge (selectedFamily (X := X) S)) := by
  classical
  exact if hi : i ∈ S then
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ inclusion (selectedFamily (X := X) S) ⟨i, hi⟩
  else TopCat.ofHom (ContinuousMap.const _ (point _))

@[simp] theorem selectedMap_base (N : Neighborhoods X) (S : Set ι) (i : ι) :
    N.selectedMap S i (N.expandedFamily S i).base = point _ := by
  classical
  by_cases hi : i ∈ S
  · simp only [selectedMap, dif_pos hi]
    exact inclusion_base (selectedFamily (X := X) S) (⟨i, hi⟩ : S)
  · simp only [selectedMap, dif_neg hi]
    rfl

def expandedCollapse (N : Neighborhoods X) (S : Set ι) :
    TopCat.of (N.expanded S) ⟶ TopCat.of (Wedge (selectedFamily (X := X) S)) :=
  TopCat.ofHom ⟨(gluedHomeomorph X (N.expandedSets S) (N.expandedSets_base S)
    (N.expandedSets_open S)).symm, (gluedHomeomorph X (N.expandedSets S)
      (N.expandedSets_base S) (N.expandedSets_open S)).symm.continuous⟩ ≫
    descend (N.expandedFamily S) (point _) (N.selectedMap S) (N.selectedMap_base S)

/-- The selected subwedge lies in the expanded piece. -/
def selectedInclusion (N : Neighborhoods X) (S : Set ι) :
    TopCat.of (Wedge (selectedFamily (X := X) S)) ⟶ TopCat.of (N.expanded S) := by
  have hm : ∀ z, subwedgeInclusion (X := X) S z ∈ N.expanded S := by
    intro z
    induction z using Quotient.inductionOn with | _ a =>
      cases a with
      | inl a => exact N.point_mem_expanded S
      | inr a => exact (N.inclusion_mem_expanded S a.1.val a.2).mpr (Or.inl a.1.property)
  exact TopCat.ofHom ⟨fun z => ⟨subwedgeInclusion (X := X) S z, hm z⟩,
    (subwedgeInclusion (X := X) S).hom.continuous.subtype_mk _⟩

@[simp] theorem selectedInclusion_val (N : Neighborhoods X) (S : Set ι)
    (z : Wedge (selectedFamily (X := X) S)) :
    (N.selectedInclusion S z).val = subwedgeInclusion (X := X) S z := rfl

/-- The expanded piece has the ordinary wedge topology on its constituent open subspaces. -/
def expandedGluing (N : Neighborhoods X) (S : Set ι) :
    Wedge (N.expandedFamily S) ≃ₜ N.expanded S :=
  gluedHomeomorph X (N.expandedSets S) (N.expandedSets_base S) (N.expandedSets_open S)

@[simp] theorem expandedGluing_point (N : Neighborhoods X) (S : Set ι) :
    N.expandedGluing S (point _) = ⟨point X, N.point_mem_expanded S⟩ := rfl

@[simp] theorem expandedGluing_inclusion_val (N : Neighborhoods X) (S : Set ι)
    (i : ι) (x : (N.expandedFamily S i).space) :
    (N.expandedGluing S (inclusion (N.expandedFamily S) i x)).val = inclusion X i x.val := rfl

@[simp] theorem expandedCollapse_gluing (N : Neighborhoods X) (S : Set ι)
    (z : Wedge (N.expandedFamily S)) :
    N.expandedCollapse S (N.expandedGluing S z) =
      descend (N.expandedFamily S) (point _) (N.selectedMap S) (N.selectedMap_base S) z := by
  change descend (N.expandedFamily S) (point _) (N.selectedMap S) (N.selectedMap_base S)
    ((N.expandedGluing S).symm (N.expandedGluing S z)) = _
  rw [Homeomorph.symm_apply_apply]

@[simp] theorem expandedCollapse_point (N : Neighborhoods X) (S : Set ι) :
    N.expandedCollapse S ⟨point X, N.point_mem_expanded S⟩ = point _ := by
  rw [← N.expandedGluing_point S, N.expandedCollapse_gluing]
  rfl

@[simp] theorem selectedInclusion_point (N : Neighborhoods X) (S : Set ι) :
    N.selectedInclusion S (point _) = ⟨point X, N.point_mem_expanded S⟩ := rfl

@[simp] theorem expandedCollapse_selectedInclusion (N : Neighborhoods X) (S : Set ι)
    (z : Wedge (selectedFamily (X := X) S)) :
    N.expandedCollapse S (N.selectedInclusion S z) = z := by
  classical
  induction z using Quotient.inductionOn with | _ a =>
    cases a with
    | inl a => exact N.expandedCollapse_point S
    | inr a =>
      rcases a with ⟨i, x⟩
      let y : (N.expandedFamily S i.val).space := ⟨x, by simp [expandedSets, i.property]⟩
      have h : N.expandedGluing S (inclusion (N.expandedFamily S) i.val y) =
          N.selectedInclusion S (inclusion (selectedFamily (X := X) S) i x) := by
        apply Subtype.ext
        rfl
      change N.expandedCollapse S
        (N.selectedInclusion S (inclusion (selectedFamily (X := X) S) i x)) =
        inclusion (selectedFamily (X := X) S) i x
      rw [← h, N.expandedCollapse_gluing]
      change N.selectedMap S i.val y = inclusion (selectedFamily (X := X) S) i x
      simp only [selectedMap, dite_eq_left i.property]
      rfl

/-- The selected inclusion followed by the actual subspace inclusion is the
canonical subwedge inclusion in the ambient wedge. -/
@[simp] theorem selectedInclusion_ambient (N : Neighborhoods X) (S : Set ι) :
    N.selectedInclusion S ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ =
      subwedgeInclusion (X := X) S := by
  ext z
  rfl

/-- Restricting a summand inclusion to the selected subwedge and returning to
the ambient wedge gives precisely the original summand inclusion. -/
@[simp] theorem inclusion_subwedgeInclusion (S : Set ι) (i : S) :
    inclusion (selectedFamily (X := X) S) i ≫ subwedgeInclusion (X := X) S =
      inclusion X i.val := by
  ext x
  rfl

/-- A deformation of the expanded piece which collapses just the unused neighborhoods. -/
def expandedDeformation (N : Neighborhoods X) (S : Set ι) :
    C(N.expanded S × unitInterval, N.expanded S) :=
  let e := N.expandedGluing S
  let K := wedgeHomotopy (N.expandedFamily S) (N.expandedHomotopy S)
    (N.expandedHomotopy_base S)
  ⟨fun zt => e (K (e.symm zt.1, zt.2)),
    e.continuous.comp (K.continuous.comp
      ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))⟩

@[simp] theorem expandedDeformation_zero (N : Neighborhoods X) (S : Set ι)
    (z : N.expanded S) : N.expandedDeformation S (z, 0) = z := by
  change N.expandedGluing S
    (wedgeHomotopy (N.expandedFamily S) (N.expandedHomotopy S) (N.expandedHomotopy_base S)
      ((N.expandedGluing S).symm z, 0)) = z
  rw [wedgeHomotopy_zero _ _ _ (N.expandedHomotopy_zero S), Homeomorph.apply_symm_apply]

@[simp] theorem expandedDeformation_one (N : Neighborhoods X) (S : Set ι)
    (z : N.expanded S) :
    N.expandedDeformation S (z, 1) = N.selectedInclusion S (N.expandedCollapse S z) := by
  classical
  obtain ⟨y, rfl⟩ := (N.expandedGluing S).surjective z
  rw [N.expandedCollapse_gluing]
  change N.expandedGluing S
    (wedgeHomotopy (N.expandedFamily S) (N.expandedHomotopy S) (N.expandedHomotopy_base S)
      ((N.expandedGluing S).symm (N.expandedGluing S y), 1)) = _
  rw [Homeomorph.symm_apply_apply]
  induction y using Quotient.inductionOn with | _ a =>
    cases a with
    | inl a => rfl
    | inr a =>
      rcases a with ⟨i, x⟩
      change N.expandedGluing S
        (inclusion (N.expandedFamily S) i (N.expandedHomotopy S i (x, 1))) =
        N.selectedInclusion S (N.selectedMap S i x)
      by_cases hi : i ∈ S
      · rw [N.expandedHomotopy_one_selected S i hi]
        simp only [selectedMap, dite_eq_left hi]
        apply Subtype.ext
        rfl
      · rw [N.expandedHomotopy_one_unused S i hi, inclusion_base]
        simp only [selectedMap, dite_eq_right hi]
        rfl

/-- The chosen subwedge inclusion is a homotopy inverse to collapse. -/
def selectedInclusion_collapse_homotopy (N : Neighborhoods X) (S : Set ι) :
    TopCat.Homotopy (N.expandedCollapse S ≫ N.selectedInclusion S) (𝟙 (TopCat.of (N.expanded S))) :=
  ContinuousMap.Homotopy.symm {
    toFun := fun tz => N.expandedDeformation S (tz.2, tz.1)
    continuous_toFun := (N.expandedDeformation S).continuous.comp
      (continuous_snd.prodMk continuous_fst)
    map_zero_left := N.expandedDeformation_zero S
    map_one_left := N.expandedDeformation_one S }

/-- The selected inclusion induces isomorphisms for every allowed coefficient module. -/
theorem selectedInclusion_reducedHomology_isIso (N : Neighborhoods X) (S : Set ι)
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℤ) :
    IsIso ((reducedHomologyFunctor R M n).map (N.selectedInclusion S)) := by
  apply (P202.PrismHomotopy.equivalence R M (N.selectedInclusion S) (N.expandedCollapse S) ?_
    (N.selectedInclusion_collapse_homotopy S) n).2
  have h : N.selectedInclusion S ≫ N.expandedCollapse S = 𝟙 _ := by
    ext z
    exact N.expandedCollapse_selectedInclusion S z
  rw [h]
  exact ContinuousMap.Homotopy.refl _


/-- Every class from an expanded piece has the same ambient image as a class
from the selected subwedge, with the canonical inclusion maps. -/
theorem expanded_homology_factors (N : Neighborhoods X) (S : Set ι)
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℤ)
    (x : reducedHomology R M (TopCat.of (N.expanded S)) n) :
    ∃ y : reducedHomology R M (TopCat.of (Wedge (selectedFamily (X := X) S))) n,
      (reducedHomologyFunctor R M n).map
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) x =
        (reducedHomologyFunctor R M n).map (subwedgeInclusion (X := X) S) y := by
  let F := reducedHomologyFunctor R M n
  letI : IsIso (F.map (N.selectedInclusion S)) :=
    N.selectedInclusion_reducedHomology_isIso S R M n
  obtain ⟨y, hy⟩ := ((ConcreteCategory.isIso_iff_bijective (F.map (N.selectedInclusion S))).mp
    inferInstance).2 x
  refine ⟨y, ?_⟩
  rw [← N.selectedInclusion_ambient S, CategoryTheory.Functor.map_comp]
  change _ = (F.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩))
    (F.map (N.selectedInclusion S) y)
  rw [hy]


end Neighborhoods
end OpenCover

/-- Good basepoints are preserved by the usual wedge construction. Only the
finite case will be used for the homology assertion. -/
theorem good_wedge (h : ∀ i, Good (X i)) :
    Good ⟨TopCat.of (Wedge X), point X⟩ := by
  let N := Neighborhoods.ofGood h
  exact ⟨isClosed_point X (fun i => (h i).1), N.core, N.core_isOpen, N.core_deformation⟩

/-- Extend finitely supported families from a selected collection of summands. -/
def extendSum (S : Set ι) (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    (⨁ i : S, reducedHomology R M (X i.val).space (n : ℤ)) →ₗ[R]
      (⨁ i : ι, reducedHomology R M (X i).space (n : ℤ)) := by
  classical
  exact DirectSum.toModule R S _ (fun i => DirectSum.lof R ι (fun j => reducedHomology R M (X j).space (n : ℤ)) i.val)

theorem inclusionSum_extendSum (S : Set ι) (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    (inclusionSum X R M n).comp (extendSum X S R M n) =
      ((reducedHomologyFunctor R M (n : ℤ)).map
        (Neighborhoods.subwedgeInclusion (X := X) S)).hom.comp
      (inclusionSum (Neighborhoods.selectedFamily (X := X) S) R M n) := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  change inclusionSum X R M n ((extendSum X S R M n) (DirectSum.lof R S _ i x)) = _
  rw [extendSum, DirectSum.toModule_lof, inclusionSum_lof]
  change _ = (reducedHomologyFunctor R M (n : ℤ)).map
    (Neighborhoods.subwedgeInclusion (X := X) S)
    (inclusionSum (Neighborhoods.selectedFamily (X := X) S) R M n
      (DirectSum.lof R S _ i x))
  rw [inclusionSum_lof]
  change _ = ((reducedHomologyFunctor R M (n : ℤ)).map
    (inclusion (Neighborhoods.selectedFamily (X := X) S) i) ≫
    (reducedHomologyFunctor R M (n : ℤ)).map
      (Neighborhoods.subwedgeInclusion (X := X) S)) x
  rw [← Functor.map_comp]
  rfl


/-- Finite induction assembles two-piece surjectivity into the canonical sum map. -/
theorem inclusionSum_surjective_of_splitting
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (split : ∀ (κ : Type w) (Y : κ → BasedSpace.{w}), (∀ i, Good (Y i)) →
      ∀ (S : Set κ) (n : ℕ) (z : reducedHomology R M (TopCat.of (Wedge Y)) (n : ℤ)),
      ∃ (a : reducedHomology R M
          (TopCat.of (Wedge (Neighborhoods.selectedFamily (X := Y) S))) (n : ℤ))
        (b : reducedHomology R M
          (TopCat.of (Wedge (Neighborhoods.selectedFamily (X := Y) Sᶜ))) (n : ℤ)),
        (reducedHomologyFunctor R M (n : ℤ)).map
          (Neighborhoods.subwedgeInclusion (X := Y) S) a +
        (reducedHomologyFunctor R M (n : ℤ)).map
          (Neighborhoods.subwedgeInclusion (X := Y) Sᶜ) b = z)
    [Finite ι] (h : ∀ i, Good (X i)) (n : ℕ) :
    Function.Surjective (inclusionSum X R M n) := by
  classical
  have main : ∀ k : ℕ, ∀ (κ : Type w) [Finite κ] (Y : κ → BasedSpace.{w}),
      Nat.card κ = k → (∀ i, Good (Y i)) →
      ∀ n, Function.Surjective (inclusionSum Y R M n) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro κ _ Y hk hY n
      by_cases he : IsEmpty κ
      · letI := he
        exact (inclusionSum_empty_bijective Y R M n).2
      · haveI : Nonempty κ := not_isEmpty_iff.mp he
        obtain ⟨i⟩ := ‹Nonempty κ›
        let S : Set κ := {i}
        have hi : i ∈ S := Set.mem_singleton _
        have hcard : Nat.card ↥(Sᶜ) < k := by
          rw [← hk]
          exact Finite.card_subtype_lt (x := i) (by simpa using hi)
        have hright := ih (Nat.card ↥(Sᶜ)) hcard ↥(Sᶜ)
          (Neighborhoods.selectedFamily (X := Y) Sᶜ) rfl (fun j => hY j.val) n
        have hleft : Function.Surjective
            (inclusionSum (Neighborhoods.selectedFamily (X := Y) S) R M n) :=
          (inclusionSum_single_bijective
            (Neighborhoods.selectedFamily (X := Y) S) R M ⟨i, hi⟩ n).2
        intro z
        obtain ⟨a, b, hab⟩ := split κ Y hY S n z
        obtain ⟨a', rfl⟩ := hleft a
        obtain ⟨b', rfl⟩ := hright b
        refine ⟨extendSum Y S R M n a' + extendSum Y Sᶜ R M n b', ?_⟩
        rw [map_add]
        have ha := LinearMap.congr_fun (inclusionSum_extendSum Y S R M n) a'
        have hb := LinearMap.congr_fun (inclusionSum_extendSum Y Sᶜ R M n) b'
        exact (congrArg₂ (fun a b => a + b) ha hb).trans hab
  exact main (Nat.card ι) ι X rfl h n


section MayerVietorisAssembly
open HomologicalComplex P202Specs.MayerVietoris
variable {X}
lemma sum_epi_of_overlap_zero {R : Type u} [CommRing R]
    (F : P202Specs.RelativeSingularChains.Pair.{v} ⥤
      ChainComplex (ModuleCat.{max u v} R) ℤ)
    (δ : Connecting.{u,v,w} F) (hδ : Exact F δ)
    (C : CoverPair.{v,w}) (n : ℤ)
    (hz : IsZero ((F.obj C.intersectionPair).homology (n-1))) :
    Epi (sum F C n) := by
  have he := (hδ.1 C (n-1)).exact 1
  have hg : Epi (sum F C ((n-1)+1)) := he.epi_f (hz.eq_of_tgt _ _)
  convert hg using 1 <;> congr 1 <;> omega

lemma sum_surjective_of_overlap_zero {R : Type u} [CommRing R]
    (F : P202Specs.RelativeSingularChains.Pair.{v} ⥤
      ChainComplex (ModuleCat.{max u v} R) ℤ)
    (δ : Connecting.{u,v,w} F) (hδ : Exact F δ)
    (C : CoverPair.{v,w}) (n : ℤ)
    (hz : IsZero ((F.obj C.intersectionPair).homology (n-1))) :
    Function.Surjective (sum F C n) := by
  letI := sum_epi_of_overlap_zero F δ hδ C n hz
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance



open P202Specs.WedgeHomology

theorem expanded_homology_split_ring
    (hmv : mayerVietoris_type.{u,w,w}) (N : Neighborhoods X) (S : Set ι)
    (R : Type u) [CommRing R] (n : ℤ)
    (z : reducedHomology R R (TopCat.of (Wedge X)) n) :
    ∃ (a : reducedHomology R R (TopCat.of (N.expanded S)) n)
      (b : reducedHomology R R (TopCat.of (N.expanded Sᶜ)) n),
      ((reducedHomologyFunctor R R n).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) a +
      ((reducedHomologyFunctor R R n).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) b = z := by
  let C : CoverPair.{w,w} := CoverPair.ofSets
    ⟨TopCat.of (Wedge X), ∅⟩ (N.expanded S) (N.expanded Sᶜ)
      (N.expanded_isOpen S) (N.expanded_isOpen Sᶜ) (N.expanded_union_compl S)
  obtain ⟨δ, hδ, _, _⟩ := (hmv R .reduced).1
  have hz : IsZero (((theoryFunctor R .reduced).obj C.intersectionPair).homology (n-1)) := by
    change IsZero (reducedHomology R R
      (TopCat.of ↥(N.expanded S ∩ N.expanded Sᶜ)) (n-1))
    rw [N.expanded_inter_compl S]
    exact N.core_reducedHomology R R (n-1)
  have hs := sum_surjective_of_overlap_zero (theoryFunctor R .reduced) δ hδ C n hz
  obtain ⟨y, hy⟩ := hs z
  refine ⟨(biprod.fst : homologyMiddle (theoryFunctor R .reduced) C n ⟶ _) y,
    (biprod.snd : homologyMiddle (theoryFunctor R .reduced) C n ⟶ _) y, ?_⟩
  change (biprod.desc
    ((reducedHomologyFunctor R R n).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩))
    ((reducedHomologyFunctor R R n).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩))) y = z at hy
  simp only [biprod.desc_eq, ModuleCat.hom_add, LinearMap.add_apply,
    ModuleCat.comp_apply] at hy
  convert hy using 1 <;> rfl


theorem selected_homology_split_ring
    (hmv : mayerVietoris_type.{u,w,w}) (N : Neighborhoods X) (S : Set ι)
    (R : Type u) [CommRing R] (n : ℤ)
    (z : reducedHomology R R (TopCat.of (Wedge X)) n) :
    ∃ (a : reducedHomology R R
          (TopCat.of (Wedge (Neighborhoods.selectedFamily (X := X) S))) n)
      (b : reducedHomology R R
          (TopCat.of (Wedge (Neighborhoods.selectedFamily (X := X) Sᶜ))) n),
      (reducedHomologyFunctor R R n).map
          (Neighborhoods.subwedgeInclusion (X := X) S) a +
        (reducedHomologyFunctor R R n).map
          (Neighborhoods.subwedgeInclusion (X := X) Sᶜ) b = z := by
  obtain ⟨a, b, hab⟩ := expanded_homology_split_ring hmv N S R n z
  obtain ⟨a', ha⟩ := N.expanded_homology_factors S R R n a
  obtain ⟨b', hb⟩ := N.expanded_homology_factors Sᶜ R R n b
  exact ⟨a', b', by rw [← ha, ← hb]; exact hab⟩

theorem inclusionSum_ring_surjective
    (hmv : mayerVietoris_type.{u,w,w})
    (R : Type u) [CommRing R] [Finite ι] (h : ∀ i, Good (X i)) (n : ℕ) :
    Function.Surjective (inclusionSum X R R n) := by
  apply inclusionSum_surjective_of_splitting X R R ?_ h n
  intro κ Y hY S n z
  exact selected_homology_split_ring hmv (Neighborhoods.ofGood hY) S R n z


end MayerVietorisAssembly


/-- The finite good-pointed wedge assertion with coefficients in any commutative ring. -/
theorem goodWedgeHomology_ring
    (R : Type u) [CommRing R] [Finite ι] (h : ∀ i, Good (X i)) (n : ℕ) :
    Function.Bijective (inclusionSum X R R n) :=
  ⟨inclusionSum_injective X R R n,
    inclusionSum_ring_surjective P202.MayerVietoris.mayerVietoris R h n⟩

section Vertices
open P202.Cellular

theorem zeroCell_eq_singleton (Y : BasedSpace.{w}) [CWStructure Y.space]
    (c₀ : Cell Y.space 0) (hc₀ : Y.base ∈ openCell Y.space 0 c₀) :
    openCell Y.space 0 c₀ = {Y.base} := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨a, rfl⟩
    rcases hc₀ with ⟨b, hb⟩
    have hab : a = b := Subsingleton.elim _ _
    simpa only [hab, hb] using Set.mem_singleton Y.base
  · exact Set.singleton_subset_iff.mpr hc₀

/-- A singleton vertex is an actual subcomplex; it is not an additional
structure assumed on the based CW complex. -/
def vertexSubcomplex (Y : BasedSpace.{w}) [CWStructure Y.space] (hv : IsVertex Y) :
    Subcomplex Y.space where
  cells := fun n => {c | openCell Y.space n c ⊆ {Y.base}}
  contains_closures := by
    intro n c hc x hx
    obtain ⟨c₀, hc₀⟩ := hv
    have hsingle := zeroCell_eq_singleton Y c₀ hc₀
    have hxp : x ∈ ({Y.base} : Set Y.space) := closure_minimal hc isClosed_singleton hx
    have hx₀ : x ∈ openCell Y.space 0 c₀ := hsingle.symm ▸ hxp
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr
      ⟨⟨c₀, hsingle.le⟩, hx₀⟩⟩

theorem vertexSubcomplex_carrier (Y : BasedSpace.{w}) [CWStructure Y.space]
    (hv : IsVertex Y) : (vertexSubcomplex Y hv).carrier = {Y.base} := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨c, hx⟩
    exact c.property hx
  · intro x hx
    obtain ⟨c₀, hc₀⟩ := hv
    have hsingle := zeroCell_eq_singleton Y c₀ hc₀
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr
      ⟨⟨c₀, hsingle.le⟩, hsingle.symm ▸ hx⟩⟩

/-- The accepted CW neighborhood theorem supplies precisely the good-point
hypothesis required in the general version. -/
theorem good_of_vertex (Y : BasedSpace.{w}) [CWStructure Y.space] (hv : IsVertex Y) :
    Good Y := by
  refine ⟨isClosed_singleton, ?_⟩
  obtain ⟨W, hW, h⟩ := P202.Topology.subcomplexNeighborhood (vertexSubcomplex Y hv)
  rw [vertexSubcomplex_carrier] at h
  exact ⟨W, hW, h⟩

end Vertices

/-- The CW statement follows from the good-point statement with exactly the
vertex hypothesis in the source. -/
theorem cwWedgeHomology_of_good
    (h : P202Specs.WedgeHomology.goodWedgeHomology_type.{u,v,w}) :
    P202Specs.WedgeHomology.cwWedgeHomology_type.{u,v,w} := by
  intro R _ M _ _ ι _ X _ hv n
  exact h R M ι X (fun i => good_of_vertex (X i) (hv i)) n

end P202.WedgeHomology

open Opposite HomologicalComplex P202Specs.SingularChains
open scoped Simplicial
namespace P202.WedgeCoefficients
open P202Specs.SingularChains
variable (R : Type u) [CommRing R]
variable {M N P : Type v} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

def chainCoefficientMap (f : M →ₗ[R] N) (X : TopCat.{w}) :
    complex R M X ⟶ complex R N X :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (Finsupp.mapRange.linearMap f)) (by
    intro n
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro s m
    change boundary R N X n ((Finsupp.mapRange.linearMap f) (Finsupp.single s m)) =
      (Finsupp.mapRange.linearMap f) (boundary R M X n (Finsupp.single s m))
    have hs : (Finsupp.mapRange.linearMap f) (Finsupp.single s m) = Finsupp.single s (f m) := by simp
    rw [hs, P202.SingularChains.boundary_single, P202.SingularChains.boundary_single]
    simp only [map_sum, map_zsmul]
    simp)

lemma chainCoefficientMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) (X : TopCat.{w}) :
    chainCoefficientMap R f X ≫ chainCoefficientMap R g X =
      chainCoefficientMap R (g.comp f) X := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact (Finsupp.mapRange.linearMap_comp g f).symm

lemma chainCoefficientMap_id (X : TopCat.{w}) :
    chainCoefficientMap R (LinearMap.id : M →ₗ[R] M) X = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s m
  simp [chainCoefficientMap]
  rfl

lemma chainCoefficientMap_natural (f : M →ₗ[R] N) {X Y : TopCat.{w}} (g : X ⟶ Y) :
    chainMap R M g ≫ chainCoefficientMap R f Y =
      chainCoefficientMap R f X ≫ chainMap R N g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s m
  change (Finsupp.mapRange.linearMap f) ((chainMap R M g).f n (Finsupp.single s m)) =
    (chainMap R N g).f n ((Finsupp.mapRange.linearMap f) (Finsupp.single s m))
  simp [P202.SingularChains.chainMap_single]

def augmentedCoefficientMap (f : M →ₗ[R] N) (X : TopCat.{w}) :
    augmentedShifted R M X ⟶ augmentedShifted R N X :=
  ChainComplex.ofHom (fun n => match n with
    | 0 => ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
        (f.comp ULift.moduleEquiv.toLinearMap))
    | n+1 => (chainCoefficientMap R f X).f n) (by
      intro n
      cases n with
      | zero =>
        dsimp
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext
        intro s m
        change ULift.up ((augmentationLinear R N X) ((Finsupp.mapRange.linearMap f) (Finsupp.single s m))) =
          ULift.up (f ((augmentationLinear R M X) (Finsupp.single s m)))
        simp [augmentationLinear, sumCoefficients]
      | succ n => exact (chainCoefficientMap R f X).comm (n+1) n)

lemma augmentedCoefficientMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) (X : TopCat.{w}) :
    augmentedCoefficientMap R f X ≫ augmentedCoefficientMap R g X =
      augmentedCoefficientMap R (g.comp f) X := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    exact congrArg (fun h : complex R M X ⟶ complex R P X => h.f n)
      (chainCoefficientMap_comp R f g X)

lemma augmentedCoefficientMap_id (X : TopCat.{w}) :
    augmentedCoefficientMap R (LinearMap.id : M →ₗ[R] M) X = 𝟙 _ := by
  ext n x
  cases n with
  | zero => rfl
  | succ n => simp [augmentedCoefficientMap, chainCoefficientMap]; rfl

lemma augmentedCoefficientMap_natural (f : M →ₗ[R] N) {X Y : TopCat.{w}} (g : X ⟶ Y) :
    augmentedShiftedMap R M g ≫ augmentedCoefficientMap R f Y =
      augmentedCoefficientMap R f X ≫ augmentedShiftedMap R N g := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => simp [augmentedShiftedMap, augmentedCoefficientMap]
  | succ n =>
    exact congrArg (fun h : complex R M X ⟶ complex R N Y => h.f n)
      (chainCoefficientMap_natural R f g)

def reducedCoefficientMap (f : M →ₗ[R] N) (X : TopCat.{w}) :
    reducedComplex R M X ⟶ reducedComplex R N X :=
  extendMap (augmentedCoefficientMap R f X) (degreeEmbedding (-1))

lemma reducedCoefficientMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) (X : TopCat.{w}) :
    reducedCoefficientMap R f X ≫ reducedCoefficientMap R g X =
      reducedCoefficientMap R (g.comp f) X := by
  rw [reducedCoefficientMap, reducedCoefficientMap, ← extendMap_comp, augmentedCoefficientMap_comp]
  rfl

lemma reducedCoefficientMap_id (X : TopCat.{w}) :
    reducedCoefficientMap R (LinearMap.id : M →ₗ[R] M) X = 𝟙 _ := by
  rw [reducedCoefficientMap, augmentedCoefficientMap_id, extendMap_id]
  rfl

lemma reducedCoefficientMap_natural (f : M →ₗ[R] N) {X Y : TopCat.{w}} (g : X ⟶ Y) :
    (reducedFunctor R M).map g ≫ reducedCoefficientMap R f Y =
      reducedCoefficientMap R f X ≫ (reducedFunctor R N).map g := by
  change extendMap _ _ ≫ extendMap _ _ = extendMap _ _ ≫ extendMap _ _
  rw [← extendMap_comp, ← extendMap_comp]
  exact congrArg (fun h : augmentedShifted R M X ⟶ augmentedShifted R N Y =>
    extendMap h (degreeEmbedding (-1))) (augmentedCoefficientMap_natural R f g)


end P202.WedgeCoefficients

universe u' v'
namespace P202.WedgeCoefficients
open P202Specs.SingularChains
variable (R : Type u) [CommRing R]
variable {M N P : Type v} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A linear coefficient map induces a natural map on reduced homology. -/
def homologyCoefficientMap (f : M →ₗ[R] N) (n : ℤ) :
    reducedHomologyFunctor R M n ⟶ reducedHomologyFunctor R N n where
  app X := homologyMap (reducedCoefficientMap R f X) n
  naturality X Y g := by
    change homologyMap ((reducedFunctor R M).map g) n ≫
        homologyMap (reducedCoefficientMap R f Y) n =
      homologyMap (reducedCoefficientMap R f X) n ≫
        homologyMap ((reducedFunctor R N).map g) n
    rw [← homologyMap_comp, ← homologyMap_comp, reducedCoefficientMap_natural]

@[simp] theorem homologyCoefficientMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℤ) :
    homologyCoefficientMap R f n ≫ homologyCoefficientMap R g n =
      homologyCoefficientMap R (g.comp f) n := by
  apply NatTrans.ext
  funext X
  change homologyMap (reducedCoefficientMap R f X) n ≫
    homologyMap (reducedCoefficientMap R g X) n = _
  rw [← homologyMap_comp, reducedCoefficientMap_comp]
  rfl

@[simp] theorem homologyCoefficientMap_id (n : ℤ) :
    homologyCoefficientMap R (LinearMap.id : M →ₗ[R] M) n = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  change homologyMap (reducedCoefficientMap R (LinearMap.id : M →ₗ[R] M) X) n = 𝟙 _
  rw [reducedCoefficientMap_id, homologyMap_id]

/-- A split coefficient projection is surjective on reduced homology. -/
theorem homologyCoefficientMap_surjective (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (hfg : g.comp f = LinearMap.id) (n : ℤ) (X : TopCat.{w}) :
    Function.Surjective ((homologyCoefficientMap R g n).app X) := by
  intro y
  refine ⟨(homologyCoefficientMap R f n).app X y, ?_⟩
  have h : homologyMap (reducedCoefficientMap R f X) n ≫
      homologyMap (reducedCoefficientMap R g X) n = 𝟙 _ := by
    rw [← homologyMap_comp, reducedCoefficientMap_comp, hfg,
      reducedCoefficientMap_id, homologyMap_id]
  exact congrArg (fun k => k y) h

end P202.WedgeCoefficients

namespace P202.WedgeHomology
open P202Specs.WedgeHomology P202Specs.SingularChains
variable {ι : Type w} (X : ι → BasedSpace.{w})

/-- The canonical wedge sum is surjective whenever a natural additive projection
from a surjective coefficient theory is surjective on the ambient wedge. -/
theorem inclusionSum_surjective_of_additive_natural
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (S : Type u') [CommRing S] (N : Type v') [AddCommGroup N] [Module S N]
    (n : ℕ)
    (p : ∀ Y : TopCat.{w}, reducedHomology S N Y (n : ℤ) →+
      reducedHomology R M Y (n : ℤ))
    (hnat : ∀ {Y Z : TopCat.{w}} (f : Y ⟶ Z) (y : reducedHomology S N Y (n : ℤ)),
      p Z ((reducedHomologyFunctor S N (n : ℤ)).map f y) =
        (reducedHomologyFunctor R M (n : ℤ)).map f (p Y y))
    (hp : Function.Surjective (p (TopCat.of (Wedge X))))
    (hs : Function.Surjective (inclusionSum X S N n)) :
    Function.Surjective (inclusionSum X R M n) := by
  classical
  let t := DirectSum.map (fun i => p (X i).space)
  have ht : ∀ a, p (TopCat.of (Wedge X)) (inclusionSum X S N n a) =
      inclusionSum X R M n (t a) := by
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp [t]
    | of i a =>
      change p (TopCat.of (Wedge X))
        (inclusionSum X S N n (DirectSum.lof S ι _ i a)) = _
      rw [inclusionSum_lof]
      dsimp [t]
      rw [DirectSum.map_of]
      change _ = inclusionSum X R M n (DirectSum.lof R ι _ i (p (X i).space a))
      rw [inclusionSum_lof]
      exact hnat (inclusion X i) a
    | add a b ha hb => simp only [map_add, ha, hb]
  intro y
  obtain ⟨z, rfl⟩ := hp y
  obtain ⟨a, rfl⟩ := hs z
  exact ⟨t a, (ht a).symm⟩

/-- A split linear coefficient projection transfers surjectivity of the actual
inclusion sum, preserving arbitrary index families. -/
theorem inclusionSum_surjective_of_coefficient_retract
    (R : Type u) [CommRing R] (M N : Type v)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (hfg : g.comp f = LinearMap.id) (n : ℕ)
    (hs : Function.Surjective (inclusionSum X R N n)) :
    Function.Surjective (inclusionSum X R M n) := by
  apply inclusionSum_surjective_of_additive_natural X R M R N n
    (fun Y => ((P202.WedgeCoefficients.homologyCoefficientMap R g n).app Y).hom.toAddMonoidHom)
    ?_ (P202.WedgeCoefficients.homologyCoefficientMap_surjective R f g hfg n _) hs
  intro Y Z k y
  exact congrArg (fun h => h y)
    ((P202.WedgeCoefficients.homologyCoefficientMap R g n).naturality k)

end P202.WedgeHomology

namespace P202.WedgeCoefficients
section Restriction
variable (S : Type u) [CommRing S] (M : Type v) [AddCommGroup M] [Module S M]

abbrev restrictToInt : ModuleCat.{max v w} S ⥤ ModuleCat.{max v w} ℤ :=
  ModuleCat.restrictScalars (Int.castRingHom S)

def augmentedRestrictIso (X : TopCat.{w}) :
    ((restrictToInt.{u,v,w} S).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (augmentedShifted S M X) ≅ augmentedShifted ℤ M X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => match n with
      | 0 => (show
          (((restrictToInt.{u,v,w} S).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (augmentedShifted S M X)).X 0 ≃+
          (augmentedShifted ℤ M X).X 0 from
          { toFun := fun x => x
            invFun := fun x => x
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl }).toIntLinearEquiv.toModuleIso
      | n+1 => (show
          (((restrictToInt.{u,v,w} S).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (augmentedShifted S M X)).X (n+1) ≃+
          (augmentedShifted ℤ M X).X (n+1) from
          { toFun := fun x => x
            invFun := fun x => x
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl }).toIntLinearEquiv.toModuleIso) (by
      intro i j hij
      obtain rfl : j+1 = i := hij
      cases j with
      | zero =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro c
        rfl
      | succ n =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro c
        change boundary ℤ M X n c = boundary S M X n c
        have hh : (boundary ℤ M X n).toAddMonoidHom = (boundary S M X n).toAddMonoidHom := by
          apply Finsupp.addHom_ext
          intro s m
          change boundary ℤ M X n (Finsupp.single s m) = boundary S M X n (Finsupp.single s m)
          rw [P202.SingularChains.boundary_single, P202.SingularChains.boundary_single]
        exact congrArg (fun h => h c) hh)

lemma augmentedRestrictIso_natural {X Y : TopCat.{w}} (g : X ⟶ Y) :
    ((restrictToInt.{u,v,w} S).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (augmentedShiftedMap S M g) ≫ (augmentedRestrictIso S M Y).hom =
      (augmentedRestrictIso S M X).hom ≫ augmentedShiftedMap ℤ M g := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
  | succ n =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl

local instance restrictToIntPreservesHomology :
    (restrictToInt.{u,v,w} S).PreservesHomology where
  preservesKernels _ := inferInstance
  preservesCokernels _ := inferInstance

def augmentedRestrictHomologyIso (X : TopCat.{w}) (n : ℕ) :
    (augmentedShifted ℤ M X).homology n ≅
      (restrictToInt.{u,v,w} S).obj ((augmentedShifted S M X).homology n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (augmentedRestrictIso S M X).symm ≪≫
    ((augmentedShifted S M X).sc n).mapHomologyIso (restrictToInt.{u,v,w} S)


def augmentedRestrictNatIso :
    augmentedShiftedFunctor S M ⋙
        (restrictToInt.{u,v,w} S).mapHomologicalComplex (ComplexShape.down ℕ) ≅
      augmentedShiftedFunctor ℤ M :=
  NatIso.ofComponents (augmentedRestrictIso S M) (fun g => augmentedRestrictIso_natural S M g)

def restrictionHomologyNatIso (n : ℕ) :
    (restrictToInt.{u,v,w} S).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor _ _ n ≅
      HomologicalComplex.homologyFunctor _ _ n ⋙ restrictToInt.{u,v,w} S :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso (restrictToInt.{u,v,w} S))
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor _ _ n).map f) (restrictToInt.{u,v,w} S))

def augmentedRestrictHomologyNatIso (n : ℕ) :
    augmentedShiftedFunctor ℤ M ⋙ HomologicalComplex.homologyFunctor _ _ n ≅
      (augmentedShiftedFunctor S M ⋙ HomologicalComplex.homologyFunctor _ _ n) ⋙
        restrictToInt.{u,v,w} S :=
  Functor.isoWhiskerRight (augmentedRestrictNatIso S M).symm
      (HomologicalComplex.homologyFunctor _ _ n) ≪≫
    Functor.isoWhiskerLeft (augmentedShiftedFunctor S M) (restrictionHomologyNatIso.{u,v,w} S n)

def reducedAugmentedHomologyIso (n : ℕ) :
    reducedHomologyFunctor S M (n : ℤ) ≅
      augmentedShiftedFunctor S M ⋙ HomologicalComplex.homologyFunctor _ _ (n+1) :=
  NatIso.ofComponents
    (fun X => (augmentedShifted S M X).extendHomologyIso (degreeEmbedding (-1))
      (j := n+1) (by change (-1 : ℤ) + (n+1 : ℕ) = (n : ℤ); omega))
    (fun f => extendHomologyIso_hom_naturality (augmentedShiftedMap S M f)
      (degreeEmbedding (-1)) (j := n+1)
      (by change (-1 : ℤ) + (n+1 : ℕ) = (n : ℤ); omega))

def reducedRestrictHomologyNatIso (n : ℕ) :
    reducedHomologyFunctor ℤ M (n : ℤ) ≅
      reducedHomologyFunctor S M (n : ℤ) ⋙ restrictToInt.{u,v,w} S :=
  reducedAugmentedHomologyIso ℤ M n ≪≫
    augmentedRestrictHomologyNatIso S M (n+1) ≪≫
      Functor.isoWhiskerRight (reducedAugmentedHomologyIso S M n).symm
        (restrictToInt.{u,v,w} S)

end Restriction
end P202.WedgeCoefficients

namespace P202.WedgeHomology
open P202Specs.WedgeHomology P202Specs.SingularChains P202.WedgeCoefficients
variable {ι : Type w} (X : ι → BasedSpace.{w})

/-- Changing from integer scalars back to any given scalar ring preserves
surjectivity of the canonical inclusion sum. -/
theorem inclusionSum_surjective_from_int
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
    (hs : Function.Surjective (inclusionSum X ℤ M n)) :
    Function.Surjective (inclusionSum X R M n) := by
  let e := reducedRestrictHomologyNatIso R M n
  apply inclusionSum_surjective_of_additive_natural X R M ℤ M n
    (fun Y => (e.app Y).hom.hom.toAddMonoidHom) ?_ ?_ hs
  · intro Y Z f y
    exact congrArg (fun h => h y) (e.hom.naturality f)
  · exact (e.app _).toLinearEquiv.surjective

/-- Forgetting scalar structure preserves surjectivity of the actual inclusion
sum by the natural additive scalar comparison. -/
theorem inclusionSum_surjective_to_int
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
    (hs : Function.Surjective (inclusionSum X R M n)) :
    Function.Surjective (inclusionSum X ℤ M n) := by
  let e := reducedRestrictHomologyNatIso R M n
  apply inclusionSum_surjective_of_additive_natural X ℤ M R M n
    (fun Y => (e.app Y).inv.hom.toAddMonoidHom) ?_ ?_ hs
  · intro Y Z f y
    exact congrArg (fun h => h y) (e.inv.naturality f)
  · exact (e.app _).symm.toLinearEquiv.surjective

/-- Arbitrary module coefficients follow by realizing the coefficient group as
a natural retract of the ring coefficients of its square-zero extension. -/
theorem inclusionSum_module_surjective
    (hmv : P202Specs.MayerVietoris.mayerVietoris_type.{v,w,w})
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Finite ι] (h : ∀ i, Good (X i)) (n : ℕ) :
    Function.Surjective (inclusionSum X R M n) := by
  apply inclusionSum_surjective_from_int X R M n
  letI : Module ℤᵐᵒᵖ M :=
    Module.compHom M ((RingHom.id ℤ).fromOpposite (fun x y => Commute.all x y))
  letI : IsCentralScalar ℤ M := ⟨fun _ _ => rfl⟩
  let S := TrivSqZeroExt ℤ M
  have hs : Function.Surjective (inclusionSum X S S n) :=
    inclusionSum_ring_surjective hmv S h n
  have hsInt : Function.Surjective (inclusionSum X ℤ S n) :=
    inclusionSum_surjective_to_int X S S n hs
  apply inclusionSum_surjective_of_coefficient_retract X ℤ M S
    (TrivSqZeroExt.inrHom ℤ M) (TrivSqZeroExt.sndHom ℤ M) ?_ n hsInt
  apply LinearMap.ext
  intro m
  rfl

end P202.WedgeHomology

namespace P202.WedgeHomology

/-- The full finite good-pointed wedge theorem with arbitrary module coefficients,
including the augmented degree-zero case and the empty wedge. -/
theorem goodWedgeHomology :
    P202Specs.WedgeHomology.goodWedgeHomology_type.{u,v,w} := by
  intro R _ M _ _ ι _ X h n
  exact ⟨inclusionSum_injective X R M n,
    inclusionSum_module_surjective X P202.MayerVietoris.mayerVietoris R M h n⟩

/-- The finite CW wedge theorem at vertices, with no extra good-point premise. -/
theorem cwWedgeHomology :
    P202Specs.WedgeHomology.cwWedgeHomology_type.{u,v,w} :=
  cwWedgeHomology_of_good goodWedgeHomology

end P202.WedgeHomology
