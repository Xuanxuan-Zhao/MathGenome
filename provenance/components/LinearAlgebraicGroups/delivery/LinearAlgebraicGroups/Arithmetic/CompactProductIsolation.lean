import Specs.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import Mathlib.Topology.Maps.Proper.Basic

open Set Filter Topology
open scoped Classical RestrictedProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

universe u v

namespace LinearAlgebraicGroups.Arithmetic.CompactProductIsolation

section TopologicalGroups

variable {J U : Type*} [Group J] [Group U] [TopologicalSpace J] [TopologicalSpace U]
  [IsTopologicalGroup U]

private theorem identityFiber_closed (P : Subgroup (J × U)) (hP : IsClosed (P : Set (J × U))) :
    IsClosed (identityFiber P : Set (secondClosure P)) :=
  hP.preimage (continuous_const.prodMk continuous_subtype_val)

private theorem identityFiber_normal (P : Subgroup (J × U)) (hP : IsClosed (P : Set (J × U))) :
    (identityFiber P).Normal where
  conj_mem x hx g := by
    let f : U → J × U := fun a => (1, a * x.val * a⁻¹)
    have hf : Continuous f :=
      continuous_const.prodMk ((continuous_id.mul continuous_const).mul continuous_inv)
    have hg : g.val ∈ closure (P.map (MonoidHom.snd J U) : Set U) := g.property
    change f g.val ∈ P
    apply closure_minimal _ (hP.preimage hf) hg
    rintro _ ⟨⟨j, a⟩, hja, rfl⟩
    have hc := P.mul_mem (P.mul_mem hja hx) (P.inv_mem hja)
    change (j * 1 * j⁻¹, a * x.val * a⁻¹) ∈ P at hc
    simpa [f] using hc

private theorem contracted_eq_one [CompactSpace U] [T2Space U] {x : U}
    (hx : Contracted x) : x = 1 := by
  obtain ⟨a, ha⟩ := hx
  let conjugate : U → U := fun b => b * x * b⁻¹
  have hc : Continuous conjugate := (continuous_id.mul continuous_const).mul continuous_inv
  have hclosed := (isCompact_range hc).isClosed
  have hmem : 1 ∈ range conjugate :=
    hclosed.mem_of_tendsto ha (Eventually.of_forall fun n => ⟨a ^ n, rfl⟩)
  obtain ⟨b, hb⟩ := hmem
  have h := congrArg (fun y => b⁻¹ * y * b) hb
  simpa [conjugate, mul_assoc] using h

theorem compactProductIsolation : Specs.CompactProductIsolation.compactProductIsolation.{u, v} := by
  intro J U _ _ _ _ _ _ _ P hP honto
  have hF := identityFiber_closed P hP
  letI hN : (identityFiber P).Normal := identityFiber_normal P hP
  letI : IsClosed (identityFiber P : Set (secondClosure P)) := hF
  letI : CompactSpace (secondClosure P) :=
    isCompact_iff_compactSpace.mp ((P.map (MonoidHom.snd J U)).isClosed_topologicalClosure.isCompact)
  let first := (MonoidHom.fst J U).comp P.subtype
  let second := secondCoordinate P
  let q := QuotientGroup.mk' (identityFiber P)
  have hker : first.ker ≤ (q.comp second).ker := by
    intro p hp
    change p.val.1 = 1 at hp
    change q (second p) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    change (1, p.val.2) ∈ P
    rw [← hp]
    exact p.property
  let φ : J →* (secondClosure P ⧸ identityFiber P) :=
    first.liftOfSurjective honto ⟨q.comp second, hker⟩
  have hφ (p : P) : φ (first p) = q (second p) :=
    first.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv honto) _ p
  have hfirst : Continuous first := continuous_fst.comp continuous_subtype_val
  have hsecond : Continuous second :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hfirstQ : IsQuotientMap first :=
    (isClosedMap_fst_of_compactSpace.comp hP.isClosedMap_subtype_val).isQuotientMap hfirst honto
  have hφc : Continuous φ :=
    hfirstQ.continuous_iff.mpr (by
      have he : (φ : J → _) ∘ first = q ∘ second := funext hφ
      rw [he]
      exact hq.comp hsecond)
  let ψ : J →ₜ* (secondClosure P ⧸ identityFiber P) := ⟨φ, hφc⟩
  have hkill (x : J) (hx : Contracted x) : ψ x = 1 := by
    obtain ⟨a, ha⟩ := hx
    apply contracted_eq_one
    refine ⟨ψ a, ?_⟩
    have ht : Tendsto (fun n : ℕ => φ (a ^ n * x * (a ^ n)⁻¹)) atTop (𝓝 (φ 1)) :=
      (hφc.tendsto (1 : J)).comp ha
    change Tendsto (fun n : ℕ => φ a ^ n * φ x * (φ a ^ n)⁻¹) atTop (𝓝 1)
    simpa only [map_one, map_mul, map_pow, map_inv] using ht
  have hfiber (x : J) : ψ x = 1 ↔ (x, 1) ∈ P := by
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := honto x
      change first p = x at hp
      have hy : q (second p) = 1 := (hφ p).symm.trans (hp ▸ hx)
      have hz : second p ∈ identityFiber P := (QuotientGroup.eq_one_iff (second p)).mp hy
      change (1, p.val.2) ∈ P at hz
      have hm := P.mul_mem p.property (P.inv_mem hz)
      change (p.val.1 * 1⁻¹, p.val.2 * p.val.2⁻¹) ∈ P at hm
      change p.val.1 = x at hp
      simpa [hp] using hm
    · intro hx
      let p : P := ⟨(x, 1), hx⟩
      have he : second p = 1 := Subtype.ext rfl
      change φ (first p) = 1
      rw [hφ, he, map_one]
  refine ⟨hF, hN, ψ, ⟨hφ, hkill, hfiber, ?_⟩, ?_⟩
  · intro hd x
    have hc : (Subgroup.closure {y : J | Contracted y} : Set J) ⊆ φ.ker :=
      (Subgroup.closure_le φ.ker).mpr fun y hy => hkill y hy
    have hclosed : IsClosed (φ.ker : Set J) := isClosed_singleton.preimage hφc
    exact (hfiber x).mp (closure_minimal hc hclosed (hd x))
  · intro χ hχ
    apply ContinuousMonoidHom.ext
    intro x
    obtain ⟨p, rfl⟩ := honto x
    exact (hχ.1 p).trans (hφ p).symm

end TopologicalGroups

section Adeles

open AdelicGroups ArithmeticLatticeProjection
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization)

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
variable (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)

private instance localPointsT2 (w : D.Place) : T2Space (LocalPoints D i w) :=
  (localMatrixEmbedding D i w).isEmbedding.t2Space

@[simp]
theorem forgetOutside_apply {S T : Finset D.Place} (h : S ⊆ T) (x : Adeles D i S)
    (w : Outside D T) : forgetOutside D i h x w = x (outsideIndex D h w) :=
  rfl

theorem forgetOutside_continuous {S T : Finset D.Place} (h : S ⊆ T) :
    Continuous (forgetOutside D i h) :=
  RestrictedProduct.mapAlong_continuous _ _ (outsideIndex D h)
    (outsideIndex_injective D h).tendsto_cofinite (fun _ => id)
    (Eventually.of_forall fun _ _ hx => hx) (fun _ => continuous_id)

private def extendOutside {S T : Finset D.Place} (h : S ⊆ T) (x : Adeles D i T) :
    Adeles D i S := by
  refine ⟨fun w => if hw : w.1 ∉ T then x ⟨w.1, hw⟩ else 1, ?_⟩
  have hfin : {w : Outside D T | x w ∉ localSubgroup D i w.1}.Finite :=
    eventually_cofinite.mp x.eventually
  have he : ∀ᶠ w in cofinite, w ∉
      outsideIndex D h '' {k : Outside D T | x k ∉ localSubgroup D i k.1} :=
    eventually_cofinite.mpr ((hfin.image (outsideIndex D h)).subset
      fun _ hw => not_not.mp hw)
  refine he.mono fun w hw => ?_
  change (if ht : w.1 ∉ T then x ⟨w.1, ht⟩ else 1) ∈ localSubgroup D i w.1
  by_cases ht : w.1 ∉ T
  · rw [dite_eq_left ht]
    exact not_not.mp fun hx => hw ⟨⟨w.1, ht⟩, hx, Subtype.ext rfl⟩
  · rw [dite_eq_right ht]
    exact (localSubgroup D i w.1).one_mem

private theorem extendOutside_apply {S T : Finset D.Place} (h : S ⊆ T)
    (x : Adeles D i T) (w : Outside D S) :
    extendOutside D i h x w = if hw : w.1 ∉ T then x ⟨w.1, hw⟩ else 1 := rfl

private theorem extendOutside_continuous {S T : Finset D.Place} (h : S ⊆ T) :
    Continuous (extendOutside D i h) := by
  apply (adelicBasis D i S).continuous_iff.mpr
  rintro _ ⟨F, V, hVo, hV, rfl⟩
  by_cases h1 : ∀ w : Outside D S, w.1 ∈ T → (1 : LocalPoints D i w.1) ∈ V w
  · have he : extendOutside D i h ⁻¹' box D i S V =
        box D i T (fun w => V (outsideIndex D h w)) := by
      ext x
      constructor
      · intro hx w
        have hw := hx (outsideIndex D h w)
        simpa only [extendOutside_apply, outsideIndex, dite_eq_left w.2] using hw
      · intro hx w
        by_cases hw : w.1 ∉ T
        · rw [extendOutside_apply, dite_eq_left hw]
          exact hx ⟨w.1, hw⟩
        · rw [extendOutside_apply, dite_eq_right hw]
          exact h1 w (not_not.mp hw)
    rw [he]
    have hfin : (outsideIndex D h ⁻¹' (↑F : Set (Outside D S))).Finite :=
      F.finite_toSet.preimage (outsideIndex_injective D h).injOn
    have hb : box D i T (fun w => V (outsideIndex D h w)) ∈ basicBoxes D i T := by
      let V' (w : Outside D T) : Set (LocalPoints D i w.1) := V (outsideIndex D h w)
      have hV'o (w : Outside D T) : IsOpen (V' w) := hVo (outsideIndex D h w)
      have hV'eq (w : Outside D T) (hw : w ∉ hfin.toFinset) :
          V' w = (localSubgroup D i w.1 : Set _) :=
        hV (outsideIndex D h w) fun hm => hw (hfin.mem_toFinset.mpr hm)
      exact ⟨hfin.toFinset, V', hV'o, hV'eq, rfl⟩
    exact (adelicBasis D i T).isOpen hb
  · push Not at h1
    obtain ⟨w, hw, hn⟩ := h1
    have he : extendOutside D i h ⁻¹' box D i S V = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hn
      have hxw := hx w
      rwa [extendOutside_apply, dite_eq_right (not_not.mpr hw)] at hxw
    rw [he]
    exact isOpen_empty

private theorem forgetOutside_extendOutside {S T : Finset D.Place} (h : S ⊆ T) :
    Function.LeftInverse (forgetOutside D i h) (extendOutside D i h) := by
  intro x
  apply RestrictedProduct.ext _ _
  intro w
  simp only [forgetOutside_apply, extendOutside_apply, outsideIndex, dite_eq_left w.2]

theorem forgetOutside_openQuotient {S T : Finset D.Place} (h : S ⊆ T) :
    IsOpenQuotientMap (forgetOutside D i h) :=
  MonoidHom.isOpenQuotientMap_of_isQuotientMap <|
    IsQuotientMap.of_inverse (extendOutside_continuous D i h) (forgetOutside_continuous D i h)
      (forgetOutside_extendOutside D i h)

@[simp]
theorem projectFinite_apply {S J : Finset D.Place} (h : Disjoint J S) (x : Adeles D i S)
    (w : (↑J : Set D.Place)) :
    projectFinite D i h x w = x ⟨w.1, Finset.disjoint_left.mp h w.2⟩ := rfl

private theorem projectFinite_continuous {S J : Finset D.Place} (h : Disjoint J S) :
    Continuous (projectFinite D i h) :=
  continuous_pi fun w => RestrictedProduct.continuous_eval
    (R := fun a : Outside D S => LocalPoints D i a.1)
    (A := fun a => (localSubgroup D i a.1 : Set _)) ⟨w.1, Finset.disjoint_left.mp h w.2⟩

theorem insertFinite_apply (S J : Finset D.Place) (x : FinitePoints D i J) (w : Outside D S) :
    insertFinite D i S J x w = if hw : w.1 ∈ J then x ⟨w.1, hw⟩ else 1 := rfl

private theorem insertFinite_continuous (S J : Finset D.Place) :
    Continuous (insertFinite D i S J) := by
  let R (w : Outside D S) := LocalPoints D i w.1
  let A (w : Outside D S) : Set (R w) := localSubgroup D i w.1
  let W : Set (Outside D S) := {w | w.1 ∉ J}
  have hW : (cofinite : Filter (Outside D S)) ≤ 𝓟 W := by
    rw [le_principal_iff, mem_cofinite]
    convert J.finite_toSet.preimage (f := fun w : Outside D S => w.val)
      Subtype.val_injective.injOn using 1
    ext w
    simp [W]
  let f (x : FinitePoints D i J) : Πʳ w, [R w, A w]_[𝓟 W] :=
    ⟨fun w => insertFinite D i S J x w, mem_principal.mpr fun w hw => by
      change w.1 ∉ J at hw
      change insertFinite D i S J x w ∈ localSubgroup D i w.1
      rw [insertFinite_apply, dite_eq_right hw]
      exact (localSubgroup D i w.1).one_mem⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    intro w
    change Continuous (fun x : FinitePoints D i J => insertFinite D i S J x w)
    by_cases hw : w.1 ∈ J
    · simp only [insertFinite_apply, dite_eq_left hw]
      exact @continuous_apply (↑J : Set D.Place) (fun k => LocalPoints D i k.1) _
        ⟨w.1, hw⟩
    · simp only [insertFinite_apply, dite_eq_right hw]
      exact continuous_const
  exact (RestrictedProduct.continuous_inclusion hW).comp hf

private theorem diagonalSet_eq_range (S : Finset D.Place) :
    diagonalSet D i S = range (diagonal D i S) := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, RestrictedProduct.ext _ _ fun w => (hg w).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, diagonalCoordinates D i S g⟩

/-- The closed subgroup of outside adeles generated topologically by the rational diagonal. -/
def diagonalClosedSubgroup (S : Finset D.Place) : Subgroup (Adeles D i S) :=
  (diagonal D i S).range.topologicalClosure

theorem diagonalClosedSubgroup_coe (S : Finset D.Place) :
    (diagonalClosedSubgroup D i S : Set (Adeles D i S)) = diagonalClosure D i S := by
  rw [diagonalClosedSubgroup, Subgroup.topologicalClosure_coe, diagonalClosure,
    diagonalSet_eq_range, MonoidHom.coe_range]

@[simp]
theorem forgetOutside_diagonal {S T : Finset D.Place} (h : S ⊆ T)
    (g : Specs.IntegralModels.RationalPoints G) :
    forgetOutside D i h (diagonal D i S g) = diagonal D i T g :=
  RestrictedProduct.ext _ _ fun _ => rfl

private theorem projectFinite_diagonal {S J : Finset D.Place} (h : Disjoint J S)
    (g : Specs.IntegralModels.RationalPoints G) :
    projectFinite D i h (diagonal D i S g) = rationalProjection D i J g :=
  rfl

private def joinAdeles (S J : Finset D.Place) :
    (FinitePoints D i J × Adeles D i (S ∪ J)) →* Adeles D i S where
  toFun p := insertFinite D i S J p.1 * extendOutside D i Finset.subset_union_left p.2
  map_one' := by
    apply RestrictedProduct.ext _ _
    intro w
    simp only [RestrictedProduct.mul_apply, RestrictedProduct.one_apply, insertFinite_apply,
      extendOutside_apply, Prod.fst_one, Prod.snd_one]
    split_ifs <;> simp
  map_mul' p q := by
    apply RestrictedProduct.ext _ _
    intro w
    simp only [RestrictedProduct.mul_apply, insertFinite_apply, extendOutside_apply,
      Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
    by_cases hw : w.1 ∈ J
    · simp [hw]
    · simp only [dite_eq_right hw, one_mul]
      split_ifs <;> simp

private theorem joinAdeles_continuous (S J : Finset D.Place) :
    Continuous (joinAdeles D i S J) :=
  ((insertFinite_continuous D i S J).comp continuous_fst).mul
    ((extendOutside_continuous D i Finset.subset_union_left).comp continuous_snd)

private theorem projectFinite_joinAdeles {S J : Finset D.Place} (h : Disjoint J S)
    (p : FinitePoints D i J × Adeles D i (S ∪ J)) :
    projectFinite D i h (joinAdeles D i S J p) = p.1 := by
  funext w
  simp [joinAdeles, insertFinite_apply, extendOutside_apply]

private theorem forgetOutside_joinAdeles (S J : Finset D.Place)
    (p : FinitePoints D i J × Adeles D i (S ∪ J)) :
    forgetOutside D i Finset.subset_union_left (joinAdeles D i S J p) = p.2 := by
  apply RestrictedProduct.ext _ _
  intro w
  have hJ : w.1 ∉ J := fun h => w.2 (Finset.mem_union_right S h)
  simp [joinAdeles, insertFinite_apply, extendOutside_apply, outsideIndex, hJ, w.2]

private theorem joinAdeles_project {S J : Finset D.Place} (h : Disjoint J S)
    (x : Adeles D i S) :
    joinAdeles D i S J
      (projectFinite D i h x, forgetOutside D i Finset.subset_union_left x) = x := by
  apply RestrictedProduct.ext _ _
  intro w
  by_cases hw : w.1 ∈ J
  · simp [joinAdeles, insertFinite_apply, extendOutside_apply, hw]
  · have hn : w.1 ∉ S ∪ J := by simp [w.2, hw]
    simp [joinAdeles, insertFinite_apply, extendOutside_apply, hw, hn, outsideIndex]

private theorem joinAdeles_one (S J : Finset D.Place) (x : FinitePoints D i J) :
    joinAdeles D i S J (x, 1) = insertFinite D i S J x := by
  apply RestrictedProduct.ext _ _
  intro w
  have he : extendOutside D i Finset.subset_union_left (1 : Adeles D i (S ∪ J)) w = 1 := by
    rw [extendOutside_apply]
    split_ifs <;> simp
  change insertFinite D i S J x w * _ = _
  simp [he]

/-- The kernel after adding a disjoint finite set of places is exactly the inserted product
of those places. -/
theorem range_insertFinite_eq_ker {S J : Finset D.Place} (h : Disjoint J S) :
    range (insertFinite D i S J) =
      ((forgetOutside D i (S := S) (T := S ∪ J) Finset.subset_union_left).ker :
        Set (Adeles D i S)) := by
  ext x
  change (∃ a : FinitePoints D i J, insertFinite D i S J a = x) ↔
    forgetOutside D i Finset.subset_union_left x = 1
  constructor
  · rintro ⟨a, rfl⟩
    rw [← joinAdeles_one D i S J a, forgetOutside_joinAdeles]
  · intro hx
    refine ⟨projectFinite D i h x, ?_⟩
    have he := joinAdeles_project D i h x
    rwa [hx, joinAdeles_one] at he

/-- The kernel of the projection consists of the adeles supported in the added places. -/
theorem mem_forgetOutside_ker_iff {S T : Finset D.Place} (h : S ⊆ T) (x : Adeles D i S) :
    x ∈ (forgetOutside D i h).ker ↔ support D i x ⊆ {w : Outside D S | w.1 ∈ T} := by
  change forgetOutside D i h x = 1 ↔ _
  constructor
  · intro hx w hw
    by_contra ht
    have he := congrArg (fun y : Adeles D i T => y ⟨w.1, ht⟩) hx
    exact hw (by simpa only [forgetOutside_apply, RestrictedProduct.one_apply, outsideIndex]
      using he)
  · intro hx
    apply RestrictedProduct.ext _ _
    intro w
    rw [forgetOutside_apply, RestrictedProduct.one_apply]
    exact not_not.mp fun hn => w.2 (hx hn)

/-- Isolating the product over J isolates each single factor indexed by J. -/
theorem mulSingle_mem_range_insertFinite {S J : Finset D.Place} (h : Disjoint J S)
    (w : Outside D S) (hw : w.1 ∈ J) (a : LocalPoints D i w.1) :
    RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) w a ∈
      range (insertFinite D i S J) := by
  rw [range_insertFinite_eq_ker D i h]
  apply (mem_forgetOutside_ker_iff D i Finset.subset_union_left _).mpr
  intro k hk
  by_cases he : k = w
  · exact he ▸ Finset.mem_union_right S hw
  · have hOne := RestrictedProduct.mulSingle_eq_of_ne
      (fun j : Outside D S => localSubgroup D i j.1) (i := w) (j := k) a he
    exact (hk hOne).elim

private theorem projectedArithmetic_eq_image {S J : Finset D.Place} (h : Disjoint J S)
    (U : Subgroup (Adeles D i (S ∪ J))) :
    (projectedArithmetic D i S J U : Set (FinitePoints D i J)) =
      (projectFinite D i h) '' (diagonalSet D i S ∩
        forgetOutside D i (S := S) (T := S ∪ J) Finset.subset_union_left ⁻¹'
          (U : Set (Adeles D i (S ∪ J)))) := by
  rw [diagonalSet_eq_range]
  have hcomp : (forgetPlaces D i (J := J) Finset.subset_union_right).comp
      (rationalProjection D i (S ∪ J)) = rationalProjection D i J := rfl
  change (( (arithmeticSubgroup D i (S ∪ J) U).map (rationalProjection D i (S ∪ J))).map
    (forgetPlaces D i Finset.subset_union_right) : Set (FinitePoints D i J)) = _
  rw [Subgroup.map_map, hcomp]
  ext a
  constructor
  · rintro ⟨g, ⟨b, hb, hbg⟩, rfl⟩
    refine ⟨diagonal D i S g, ⟨⟨g, rfl⟩, ?_⟩, projectFinite_diagonal D i h g⟩
    change forgetOutside D i Finset.subset_union_left (diagonal D i S g) ∈ U
    have he : b = diagonal D i (S ∪ J) g := RestrictedProduct.ext _ _ hbg
    rw [forgetOutside_diagonal, ← he]
    exact hb
  · rintro ⟨_, ⟨⟨g, rfl⟩, hg⟩, rfl⟩
    refine ⟨g, ⟨diagonal D i (S ∪ J) g, ?_, diagonalCoordinates D i (S ∪ J) g⟩,
      (projectFinite_diagonal D i h g).symm⟩
    exact (forgetOutside_diagonal D i Finset.subset_union_left g) ▸ hg

theorem isolateAdelicFactors : Specs.CompactProductIsolation.isolateAdelicFactors.{u, v} := by
  intro K _ G D i S J h U hUc hUo
  let Jpts := FinitePoints D i J
  let join := (joinAdeles D i S J).comp ((MonoidHom.id Jpts).prodMap U.subtype)
  let Z := diagonalClosedSubgroup D i S
  let P : Subgroup (Jpts × U) := Z.comap join
  let proj := projectFinite D i h
  have hZ : (Z : Set (Adeles D i S)) = diagonalClosure D i S := diagonalClosedSubgroup_coe D i S
  have hjoin : Continuous join :=
    (joinAdeles_continuous D i S J).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hZclosed : IsClosed (Z : Set (Adeles D i S)) := hZ.symm ▸ isClosed_closure
  have hP : IsClosed (P : Set (Jpts × U)) := hZclosed.preimage hjoin
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  have hproj :
      Prod.fst '' (P : Set (Jpts × U)) = proj '' compatibleAdeles D i S J U := by
    ext a
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      refine ⟨join (a, b), ⟨?_, ?_⟩, projectFinite_joinAdeles D i h (a, b.val)⟩
      · exact hZ ▸ hab
      · change forgetOutside D i Finset.subset_union_left (joinAdeles D i S J (a, b.val)) ∈ U
        rw [forgetOutside_joinAdeles]
        exact b.property
    · rintro ⟨x, ⟨hx, hb⟩, rfl⟩
      refine ⟨(proj x, ⟨_, hb⟩), ?_, rfl⟩
      change joinAdeles D i S J (proj x, forgetOutside D i Finset.subset_union_left x) ∈ Z
      rw [joinAdeles_project]
      change x ∈ (Z : Set (Adeles D i S))
      rwa [hZ]
  have hclosed : IsClosed (proj '' compatibleAdeles D i S J U) := by
    rw [← hproj]
    exact isClosedMap_fst_of_compactSpace _ hP
  have hprojEq : proj '' compatibleAdeles D i S J U =
      closure (projectedArithmetic D i S J U : Set Jpts) := by
    rw [projectedArithmetic_eq_image D i h U]
    let V := forgetOutside D i (S := S) (T := S ∪ J) Finset.subset_union_left ⁻¹'
          (U : Set (Adeles D i (S ∪ J)))
    have hV : IsOpen V :=
      hUo.preimage (forgetOutside_continuous D i Finset.subset_union_left)
    apply Subset.antisymm
    · rintro _ ⟨x, ⟨hx, hxV⟩, rfl⟩
      have hc : x ∈ closure (diagonalSet D i S ∩ V) := by
        apply mem_closure_iff.mpr
        intro W hW hxW
        obtain ⟨y, hyW, hy⟩ := mem_closure_iff.mp hx (W ∩ V) (hW.inter hV) ⟨hxW, hxV⟩
        exact ⟨y, hyW.1, hy, hyW.2⟩
      exact image_closure_subset_closure_image (projectFinite_continuous D i h) ⟨x, hc, rfl⟩
    · exact closure_minimal (image_mono (inter_subset_inter_left V subset_closure)) hclosed
  refine ⟨hprojEq, fun hd hcontracted a => ?_⟩
  have honto : Function.Surjective ((MonoidHom.fst Jpts U).comp P.subtype) := by
    intro x
    have hx : x ∈ Prod.fst '' (P : Set (Jpts × U)) := by
      rw [hproj, hprojEq]
      exact hd x
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨⟨p, hp⟩, rfl⟩
  obtain ⟨_, hN, φ, ⟨_, _, _, hφ⟩, _⟩ := compactProductIsolation P hP honto
  have ha := hφ hcontracted a
  change joinAdeles D i S J (a, ((1 : U) : Adeles D i (S ∪ J))) ∈ Z at ha
  rw [Subgroup.coe_one, joinAdeles_one] at ha
  exact hZ ▸ ha

private def truncate {S : Finset D.Place} (x : Adeles D i S) (F : Finset (Outside D S)) :
    Adeles D i S :=
  ⟨fun w => if w ∈ F then x w else 1, by
    have hF : ∀ᶠ w in cofinite, w ∉ F := by
      rw [eventually_cofinite]
      convert F.finite_toSet using 1
      ext w
      simp
    refine hF.mono ?_
    intro w hw
    change (if w ∈ F then x w else 1) ∈ localSubgroup D i w.1
    rw [ite_eq_right hw]
    exact (localSubgroup D i w.1).one_mem⟩

private theorem truncate_apply {S : Finset D.Place} (x : Adeles D i S)
    (F : Finset (Outside D S)) (w : Outside D S) :
    truncate D i x F w = if w ∈ F then x w else 1 := rfl

theorem finiteSupportDensity : Specs.CompactProductIsolation.finiteSupportDensity.{u, v} := by
  intro K _ G D i S E
  let X := Adeles D i S
  have hclosed : IsClosed {x : X | support D i x ⊆ E} := by
    have he : {x : X | support D i x ⊆ E} =
        ⋂ w : (↑(Eᶜ) : Type u), {x : X | x w.1 = 1} := by
      ext x
      rw [Set.mem_iInter]
      constructor
      · intro hx w
        exact not_not.mp fun hw => w.2 (hx hw)
      · intro hx w hw
        by_contra h
        exact hw (hx ⟨w, h⟩)
    rw [he]
    apply isClosed_iInter
    intro w
    exact isClosed_singleton.preimage (RestrictedProduct.continuous_eval
      (R := fun k : Outside D S => LocalPoints D i k.1)
      (A := fun k => (localSubgroup D i k.1 : Set _)) w.val)
  apply Subset.antisymm (closure_minimal (fun _ hx => hx.2) hclosed)
  intro x hx
  apply mem_closure_iff.mpr
  intro O hO hxO
  obtain ⟨B, ⟨F, V, _, hV, rfl⟩, hxB, hBO⟩ :=
    (adelicBasis D i S).exists_subset_of_mem_open hxO hO
  let y := truncate D i x F
  have hyF : support D i y ⊆ ↑F := by
    intro w hw
    by_contra hf
    have hf' : w ∉ F := hf
    apply hw
    change truncate D i x F w = 1
    rw [truncate_apply, ite_eq_right hf']
  have hyE : support D i y ⊆ E := by
    intro w hw
    apply hx
    have hf : w ∈ F := hyF hw
    change truncate D i x F w ≠ 1 at hw
    rwa [truncate_apply, ite_eq_left hf] at hw
  refine ⟨y, hBO ?_, F.finite_toSet.subset hyF, hyE⟩
  intro w
  rw [show y w = if w ∈ F then x w else 1 from truncate_apply D i x F w]
  by_cases hw : w ∈ F
  · rw [ite_eq_left hw]
    exact hxB w
  · rw [ite_eq_right hw, hV w hw]
    exact (localSubgroup D i w.1).one_mem

theorem isolatedFactorsSpan : Specs.CompactProductIsolation.isolatedFactorsSpan.{u, v} := by
  intro K _ G D i S E Z hZ hsingle
  rw [← finiteSupportDensity D i S E]
  apply closure_minimal _ hZ
  intro x hx
  rcases hx with ⟨hfin, hsub⟩
  have htrunc (F : Finset (Outside D S)) (hF : (↑F : Set (Outside D S)) ⊆ E) :
      truncate D i x F ∈ Z := by
    induction F using Finset.induction_on with
    | empty =>
      have he : truncate D i x ∅ = 1 :=
        RestrictedProduct.ext _ _ fun w => by simp [truncate_apply]
      rw [he]
      exact Z.one_mem
    | @insert w F hw ih =>
      let s := RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) w (x w)
      have hs : s ∈ Z := hsingle w (hF (Finset.mem_insert_self w F)) (x w)
      have he : truncate D i x (insert w F) = s * truncate D i x F := by
        apply RestrictedProduct.ext _ _
        intro k
        rw [RestrictedProduct.mul_apply, truncate_apply, truncate_apply]
        by_cases hk : k = w
        · subst k
          simp [s, hw]
        · rw [show s k = 1 from RestrictedProduct.mulSingle_eq_of_ne _ _ hk]
          simp [hk]
      rw [he]
      exact Z.mul_mem hs (ih fun k hk => hF (Finset.mem_insert_of_mem hk))
  have hF : (↑hfin.toFinset : Set (Outside D S)) ⊆ E :=
    fun _ hw => hsub (hfin.mem_toFinset.mp hw)
  have he : truncate D i x hfin.toFinset = x := by
    apply RestrictedProduct.ext _ _
    intro w
    by_cases hw : w ∈ support D i x
    · simp [truncate_apply, hfin.mem_toFinset.mpr hw]
    · have h1 : x w = 1 := not_not.mp hw
      simp [truncate_apply, h1]
  rw [← he]
  exact htrunc _ hF

private theorem quotientClosure {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B]
    (f : A →* B) (hf : IsQuotientMap f) (s : Set A) (Z : Subgroup A)
    (hZ : (Z : Set A) = closure s) (hker : f.ker ≤ Z) :
    f '' closure s = closure (f '' s) ∧
      f ⁻¹' closure (f '' s) = closure s ∧
      (Dense (f '' s) ↔ Dense s) := by
  have hsaturated : f ⁻¹' (f '' (Z : Set A)) = Z := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hk : y⁻¹ * x ∈ f.ker := by simp [hxy]
      simpa using Z.mul_mem hy (hker hk)
    · exact fun hx => ⟨x, hx, rfl⟩
  have hZclosed : IsClosed (Z : Set A) := hZ.symm ▸ isClosed_closure
  have himageClosed : IsClosed (f '' (Z : Set A)) :=
    hf.isClosed_preimage.mp (hsaturated.symm ▸ hZclosed)
  have himage : f '' closure s = closure (f '' s) := by
    apply Subset.antisymm (image_closure_subset_closure_image hf.continuous)
    rw [← hZ]
    exact closure_minimal (image_mono (hZ.symm ▸ subset_closure)) himageClosed
  have hpreimage : f ⁻¹' closure (f '' s) = closure s := by
    rw [← himage, ← hZ]
    exact hsaturated
  refine ⟨himage, hpreimage, ?_⟩
  rw [dense_iff_closure_eq, dense_iff_closure_eq]
  constructor
  · intro h
    rw [← hpreimage, h, preimage_univ]
  · intro h
    rw [← himage, h, image_univ]
    exact hf.surjective.range_eq

theorem enlargeOmittedSet : Specs.CompactProductIsolation.enlargeOmittedSet.{u, v} := by
  intro K _ G D i S T h
  let f := forgetOutside D i h
  have hf := forgetOutside_openQuotient D i h
  refine ⟨hf, fun hker => ?_⟩
  let Z := diagonalClosedSubgroup D i S
  have hZ : (Z : Set (Adeles D i S)) = diagonalClosure D i S := diagonalClosedSubgroup_coe D i S
  have hkerZ : f.ker ≤ Z := by
    intro x hx
    change x ∈ (Z : Set (Adeles D i S))
    rw [hZ]
    exact hker hx
  have hdiag : f '' diagonalSet D i S = diagonalSet D i T := by
    rw [diagonalSet_eq_range, diagonalSet_eq_range, ← range_comp]
    rfl
  have hq := quotientClosure f hf.isQuotientMap (diagonalSet D i S) Z hZ hkerZ
  rwa [hdiag] at hq

theorem projectToRemainingPlaces :
    Specs.CompactProductIsolation.projectToRemainingPlaces.{u, v} := by
  intro K _ G D i S J h
  let f := projectFinite D i h
  have hinv : Function.LeftInverse f (insertFinite D i S J) := by
    intro a
    funext w
    rw [show f (insertFinite D i S J a) w =
      insertFinite D i S J a ⟨w.1, Finset.disjoint_left.mp h w.2⟩ from rfl,
      insertFinite_apply]
    change (if hw : w.1 ∈ J then a ⟨w.1, hw⟩ else 1) = a w
    have hw : w.1 ∈ J := w.2
    rw [dite_eq_left hw]
  have hf : IsQuotientMap f :=
    IsQuotientMap.of_inverse (insertFinite_continuous D i S J) (projectFinite_continuous D i h)
      hinv
  refine ⟨MonoidHom.isOpenQuotientMap_of_isQuotientMap hf, fun hsingle => ?_⟩
  let Z := diagonalClosedSubgroup D i S
  have hZ : (Z : Set (Adeles D i S)) = diagonalClosure D i S := diagonalClosedSubgroup_coe D i S
  have hZclosed : IsClosed (Z : Set (Adeles D i S)) := hZ.symm ▸ isClosed_closure
  let E : Set (Outside D S) := {w | w.1 ∉ J}
  have hspan := isolatedFactorsSpan D i S E Z hZclosed (by
    intro w hw a
    change RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.1) w a ∈
      (Z : Set (Adeles D i S))
    rw [hZ]
    exact hsingle w hw a)
  have hker : f.ker ≤ Z := by
    intro x hx
    apply hspan
    intro w hw hwJ
    have he := congrArg (fun a : FinitePoints D i J => a ⟨w.1, hwJ⟩)
      (MonoidHom.mem_ker.mp hx)
    exact hw he
  have hdiag : f '' diagonalSet D i S = range (rationalProjection D i J) := by
    rw [diagonalSet_eq_range, ← range_comp]
    rfl
  have hq := quotientClosure f hf (diagonalSet D i S) Z hZ hker
  rwa [hdiag] at hq

end Adeles

end LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
