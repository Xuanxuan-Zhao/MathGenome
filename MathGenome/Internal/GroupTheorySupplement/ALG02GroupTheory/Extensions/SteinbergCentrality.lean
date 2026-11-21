import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.Central
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.StableSteinberg
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.NoncommPiCoprod

/-!
Centrality of the stable Steinberg map and perfectness of its source and target.

The proof follows Weibel, *The K-book*, Chapter III, Theorem 5.2.1 and Exercise 5.2.
The elementary map distinguishes the coefficients in each fresh row and column subgroup.
The generators with smaller indices normalize these subgroups.
-/

namespace ALG02GroupTheory.Extensions.StableSteinberg

open scoped BigOperators commutatorElement

variable {R : Type*} [Ring R]

/-- The exact sequence given by the stable Steinberg map and its kernel. -/
noncomputable def steinbergExtension (R : Type*) [Ring R] :
    GroupExtension (K₂ R) (Steinberg R) (Elementary R) where
  inl := (K₂ R).subtype
  rightHom := toElementary
  inl_injective := (K₂ R).subtype_injective
  range_inl_eq_ker_rightHom := Subgroup.range_subtype _
  rightHom_surjective := toElementary_surjective

private def generatorHom (i j : ℕ) (hij : i ≠ j) : Multiplicative R →* Steinberg R where
  toFun r := generator ⟨i, j, hij, r.toAdd⟩
  map_one' := by
    have h := (steinberg_satisfiesRelations (R := R)).1 i j hij 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.trans (mul_one _).symm)
  map_mul' r s := ((steinberg_satisfiesRelations (R := R)).1 i j hij r.toAdd s.toAdd).symm

/-- The orientation of the transvections through the fresh index. -/
private inductive Axis
  | column
  | row

private def Axis.rowIndex {n : ℕ} (axis : Axis) (a : Fin n) : Fin (n + 1) :=
  match axis with
  | .column => a.castSucc
  | .row => Fin.last n

private def Axis.colIndex {n : ℕ} (axis : Axis) (a : Fin n) : Fin (n + 1) :=
  match axis with
  | .column => Fin.last n
  | .row => a.castSucc

private theorem Axis.col_ne_row {n : ℕ} (axis : Axis) (a b : Fin n) :
    axis.colIndex a ≠ axis.rowIndex b := by
  cases axis with
  | column => exact (Fin.castSucc_ne_last b).symm
  | row => exact Fin.castSucc_ne_last a

private def Axis.indexGenerator {n : ℕ} (axis : Axis) (a : Fin n) (r : R) : Generator R :=
  ⟨axis.rowIndex a, axis.colIndex a,
    fun h => axis.col_ne_row a a (Fin.ext h.symm), r⟩

private def Axis.factor {n : ℕ} (axis : Axis) (a : Fin n) :
    Multiplicative R →* Steinberg R :=
  generatorHom (axis.rowIndex a) (axis.colIndex a) (axis.indexGenerator a (0 : R)).distinct

private theorem Axis.factor_commute {n : ℕ} (axis : Axis) :
    Pairwise fun (a b : Fin n) => ∀ (r s : Multiplicative R),
      Commute (axis.factor a r) (axis.factor b s) := by
  intro a b _ r s
  exact commutatorElement_eq_one_iff_commute.mp
    ((steinberg_satisfiesRelations (R := R)).2.1 (axis.indexGenerator a r.toAdd)
      (axis.indexGenerator b s.toAdd) (fun h => axis.col_ne_row a b (Fin.ext h))
      (fun h => axis.col_ne_row b a (Fin.ext h.symm)))

private def Axis.lift {n : ℕ} (axis : Axis) :
    (Fin n → Multiplicative R) →* Steinberg R :=
  MonoidHom.noncommPiCoprod (axis.factor (R := R)) (axis.factor_commute (R := R))

private theorem Axis.lift_mulSingle {n : ℕ} (axis : Axis) (a : Fin n) (r : R) :
    axis.lift (Pi.mulSingle a (Multiplicative.ofAdd r)) =
      generator (axis.indexGenerator a r) :=
  MonoidHom.noncommPiCoprod_mulSingle (axis.factor (R := R))
    (hcomm := axis.factor_commute (R := R)) a (Multiplicative.ofAdd r)

private def Axis.subgroup {n : ℕ} (axis : Axis) : Subgroup (Steinberg R) :=
  (axis.lift (n := n)).range

private theorem Axis.generator_mem {n : ℕ} (axis : Axis) (a : Fin n) (r : R) :
    generator (axis.indexGenerator a r) ∈ axis.subgroup (n := n) :=
  ⟨Pi.mulSingle a (Multiplicative.ofAdd r), axis.lift_mulSingle a r⟩

private theorem Axis.subgroup_le {n : ℕ} (axis : Axis) {H : Subgroup (Steinberg R)}
    (h : ∀ (a : Fin n) (r : R), generator (axis.indexGenerator a r) ∈ H) :
    axis.subgroup (n := n) ≤ H := by
  change (axis.lift (n := n)).range ≤ H
  rw [Axis.lift, MonoidHom.noncommPiCoprod_range]
  exact iSup_le fun a _ ⟨r, hr⟩ => hr ▸ h a r.toAdd

private def Axis.matrixPart {n : ℕ} (axis : Axis) (f : Fin n → Multiplicative R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  ∑ a : Fin n, Matrix.single (axis.rowIndex a) (axis.colIndex a) (f a).toAdd

private theorem Axis.matrixPart_apply {n : ℕ} (axis : Axis)
    (f : Fin n → Multiplicative R) (a : Fin n) :
    axis.matrixPart f (axis.rowIndex a) (axis.colIndex a) = (f a).toAdd := by
  unfold Axis.matrixPart
  rw [Matrix.sum_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    cases axis <;> simp [Axis.rowIndex, Axis.colIndex, Matrix.single, hba]
  · simp

private theorem Axis.matrixPart_mul {n : ℕ} (axis : Axis) (f g : Fin n → Multiplicative R) :
    axis.matrixPart (f * g) = axis.matrixPart f + axis.matrixPart g := by
  simp only [Axis.matrixPart, Pi.mul_apply, toAdd_mul, Matrix.single_add,
    Finset.sum_add_distrib]

private theorem Axis.matrixPart_mul_matrixPart {n : ℕ} (axis : Axis)
    (f g : Fin n → Multiplicative R) :
    axis.matrixPart f * axis.matrixPart g = 0 := by
  simp [Axis.matrixPart, Finset.sum_mul, Finset.mul_sum, Matrix.single_mul_single_of_ne,
    axis.col_ne_row]

private def Axis.finiteMatrix {n : ℕ} (axis : Axis) :
    (Fin n → Multiplicative R) →* FiniteGL R (n + 1) where
  toFun f :=
    { val := 1 + axis.matrixPart f
      inv := 1 + axis.matrixPart f⁻¹
      val_inv := by
        simp only [Matrix.add_mul, Matrix.mul_add, one_mul, mul_one,
          axis.matrixPart_mul_matrixPart, add_zero, add_assoc, ← axis.matrixPart_mul,
          mul_inv_cancel]
        simp [Axis.matrixPart]
      inv_val := by
        simp only [Matrix.add_mul, Matrix.mul_add, one_mul, mul_one,
          axis.matrixPart_mul_matrixPart, add_zero, add_assoc, ← axis.matrixPart_mul,
          inv_mul_cancel]
        simp [Axis.matrixPart] }
  map_one' := by
    apply Units.ext
    simp [Axis.matrixPart]
  map_mul' f g := by
    apply Units.ext
    change 1 + axis.matrixPart (f * g) = (1 + axis.matrixPart f) * (1 + axis.matrixPart g)
    simp [Matrix.add_mul, Matrix.mul_add, axis.matrixPart_mul_matrixPart,
      axis.matrixPart_mul, add_assoc]

private theorem Axis.finiteMatrix_mulSingle {n : ℕ} (axis : Axis) (a : Fin n) (r : R) :
    axis.finiteMatrix (Pi.mulSingle a (Multiplicative.ofAdd r)) =
      finiteTransvection (axis.rowIndex a) (axis.colIndex a) (axis.col_ne_row a a).symm r := by
  apply Units.ext
  change 1 + axis.matrixPart (Pi.mulSingle a (Multiplicative.ofAdd r)) =
    1 + Matrix.single (axis.rowIndex a) (axis.colIndex a) r
  congr 1
  unfold Axis.matrixPart
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [Pi.mulSingle_eq_of_ne hba]
  · simp

private theorem Axis.lift_toStableGL {n : ℕ} (axis : Axis) :
    ((ElementarySubgroup R).subtype.comp toElementary).comp (axis.lift (n := n)) =
      (ofFinite (n + 1)).comp axis.finiteMatrix := by
  apply (MonoidHom.noncommPiCoprodEquiv (M := StableGL R)).symm.injective
  apply Subtype.ext
  funext a
  apply MonoidHom.ext
  intro r
  change (ElementarySubgroup R).subtype
      (toElementary (axis.lift (Pi.mulSingle a (Multiplicative.ofAdd r.toAdd)))) =
    ofFinite (n + 1) (axis.finiteMatrix (Pi.mulSingle a (Multiplicative.ofAdd r.toAdd)))
  rw [axis.lift_mulSingle, axis.finiteMatrix_mulSingle, toElementary_generator]
  exact transvection_eq_ofFinite _ (axis.rowIndex a).isLt (axis.colIndex a).isLt

private theorem Axis.toElementary_injective {n : ℕ} (axis : Axis) :
    Set.InjOn (toElementary (R := R)) (axis.subgroup (R := R) (n := n)).carrier := by
  intro x hx y hy h
  obtain ⟨f, rfl⟩ : x ∈ axis.subgroup (n := n) := hx
  obtain ⟨g, rfl⟩ : y ∈ axis.subgroup (n := n) := hy
  have hm : axis.finiteMatrix f = axis.finiteMatrix g := by
    apply ofFinite_injective (n + 1)
    have hf := DFunLike.congr_fun (axis.lift_toStableGL (R := R) (n := n)) f
    have hg := DFunLike.congr_fun (axis.lift_toStableGL (R := R) (n := n)) g
    exact hf.symm.trans ((congrArg (ElementarySubgroup R).subtype h).trans hg)
  have hfg : f = g := by
    funext a
    have ha := congrArg (fun A : FiniteGL R (n + 1) =>
      A.val (axis.rowIndex a) (axis.colIndex a)) hm
    change (1 + axis.matrixPart f) (axis.rowIndex a) (axis.colIndex a) =
      (1 + axis.matrixPart g) (axis.rowIndex a) (axis.colIndex a) at ha
    simp only [Matrix.add_apply, axis.matrixPart_apply, add_right_inj] at ha
    exact Multiplicative.toAdd.injective ha
  rw [hfg]

private def rankSubgroup (n : ℕ) : Subgroup (Steinberg R) :=
  Subgroup.closure {x | ∃ g : Generator R, g.row < n ∧ g.col < n ∧ generator g = x}

private theorem generator_mem_rankSubgroup (g : Generator R) {n : ℕ}
    (hi : g.row < n) (hj : g.col < n) : generator g ∈ rankSubgroup n :=
  Subgroup.subset_closure ⟨g, hi, hj, rfl⟩

private theorem rankSubgroup_mono : Monotone (rankSubgroup (R := R)) := by
  intro n m hnm
  apply Subgroup.closure_mono
  rintro _ ⟨g, hi, hj, rfl⟩
  exact ⟨g, hi.trans_le hnm, hj.trans_le hnm, rfl⟩

private theorem exists_mem_rankSubgroup (x : Steinberg R) : ∃ n, x ∈ rankSubgroup n := by
  apply (Subgroup.mem_iSup_of_directed (rankSubgroup_mono.directed_le)).mp
  apply PresentedGroup.generated_by (relators R)
  intro g
  let n := max g.row g.col + 1
  exact (le_iSup rankSubgroup n) (generator_mem_rankSubgroup g
    (Nat.lt_succ_of_le (le_max_left _ _)) (Nat.lt_succ_of_le (le_max_right _ _)))

private theorem Axis.generator_commutator_mem {n : ℕ} (axis : Axis) (a : Fin n) (r : R)
    (g : Generator R) (hi : g.row < n) (hj : g.col < n) :
    ⁅generator g, generator (axis.indexGenerator a r)⁆ ∈ axis.subgroup (n := n) := by
  obtain ⟨i, j, hij, s⟩ := g
  have hin : i ≠ n := Nat.ne_of_lt hi
  have hjn : j ≠ n := Nat.ne_of_lt hj
  cases axis with
  | column =>
    by_cases h : (a : ℕ) = j
    · have ha : a = ⟨j, hj⟩ := Fin.ext h
      subst a
      change ⁅generator ⟨i, j, hij, s⟩, generator ⟨j, n, hjn, r⟩⁆ ∈
        Axis.column.subgroup (n := n)
      rw [(steinberg_satisfiesRelations (R := R)).2.2 i j n hij hjn hin s r]
      exact Axis.generator_mem .column (⟨i, hi⟩ : Fin n) (s * r)
    · rw [(steinberg_satisfiesRelations (R := R)).2.1 _ _ (Ne.symm h) hin]
      exact (Axis.subgroup (n := n) .column).one_mem
  | row =>
    by_cases h : (a : ℕ) = i
    · have ha : a = ⟨i, hi⟩ := Fin.ext h
      subst a
      change ⁅generator ⟨i, j, hij, s⟩, generator ⟨n, i, hin.symm, r⟩⁆ ∈
        Axis.row.subgroup (n := n)
      rw [SatisfiesRelations.reverse_chain (steinberg_satisfiesRelations (R := R))
        hij hin.symm hjn.symm s r]
      exact Axis.generator_mem .row (⟨j, hj⟩ : Fin n) (-(r * s))
    · rw [(steinberg_satisfiesRelations (R := R)).2.1 _ _ hjn (Ne.symm h)]
      exact (Axis.subgroup (n := n) .row).one_mem

private theorem Axis.conj_mem {n : ℕ} (axis : Axis) (g : Generator R)
    (hi : g.row < n) (hj : g.col < n) {x : Steinberg R}
    (hx : x ∈ axis.subgroup (n := n)) :
    generator g * x * (generator g)⁻¹ ∈ axis.subgroup (n := n) := by
  change x ∈ (axis.subgroup (n := n)).comap (MulAut.conj (generator g)).toMonoidHom
  refine axis.subgroup_le (fun a r => ?_) hx
  change MulAut.conj (generator g) (generator (axis.indexGenerator a r)) ∈ axis.subgroup (n := n)
  rw [conj_eq_commutatorElement_mul]
  exact axis.subgroup.mul_mem (axis.generator_commutator_mem a r g hi hj)
    (axis.generator_mem a r)

private theorem rankSubgroup_le_normalizer {n : ℕ} (axis : Axis) :
    rankSubgroup (R := R) n ≤ Subgroup.normalizer (axis.subgroup (R := R) (n := n)).carrier := by
  unfold rankSubgroup
  rw [Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, r⟩, hi, hj, rfl⟩
  change generator (⟨i, j, hij, r⟩ : Generator R) ∈
    Subgroup.normalizer (axis.subgroup (n := n)).carrier
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro x
  refine ⟨axis.conj_mem _ hi hj, fun hx => ?_⟩
  have hinv : generator (⟨i, j, hij, -r⟩ : Generator R) =
      (generator ⟨i, j, hij, r⟩)⁻¹ :=
    map_inv (generatorHom i j hij) (Multiplicative.ofAdd r)
  have h := axis.conj_mem ⟨i, j, hij, -r⟩ hi hj hx
  simpa [hinv, ← mul_assoc] using h

private theorem Axis.commute_of_mem_kernel {n : ℕ} (axis : Axis) {z x : Steinberg R}
    (hz : z ∈ K₂ R) (hn : z ∈ rankSubgroup n) (hx : x ∈ axis.subgroup (n := n)) :
    Commute z x := by
  have hc : z * x * z⁻¹ ∈ axis.subgroup (n := n) :=
    (Subgroup.mem_set_normalizer_iff.mp (rankSubgroup_le_normalizer axis hn) x).mp hx
  have h := axis.toElementary_injective hc hx (by
    have hz' : toElementary z = 1 := hz
    simp [hz'])
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem generator_eq_commutator {i j n : ℕ} (hij : i ≠ j)
    (hin : i ≠ n) (hnj : n ≠ j) (r : R) :
    generator ⟨i, j, hij, r⟩ =
      ⁅generator ⟨i, n, hin, r⟩, generator ⟨n, j, hnj, 1⟩⁆ := by
  rw [(steinberg_satisfiesRelations (R := R)).2.2 i n j hin hnj hij r 1, mul_one]

/-- The kernel of the stable Steinberg map is central. -/
theorem k₂_le_center (R : Type*) [Ring R] : K₂ R ≤ Subgroup.center (Steinberg R) := by
  intro z hz
  obtain ⟨m, hm⟩ := exists_mem_rankSubgroup z
  apply Subgroup.mem_center_iff.mpr
  suffices h : ∀ g : Generator R, generator g ∈ Subgroup.centralizer {z} by
    intro y
    exact (Subgroup.mem_centralizer_iff.mp
      (PresentedGroup.generated_by (relators R) (Subgroup.centralizer {z}) h y) z
      (Set.mem_singleton z)).symm
  rintro ⟨i, j, hij, r⟩
  let n := max m (max i j + 1)
  have hn : z ∈ rankSubgroup n := rankSubgroup_mono (le_max_left _ _) hm
  have hi : i < n :=
    (Nat.lt_succ_of_le (le_max_left _ _)).trans_le (le_max_right _ _)
  have hj : j < n :=
    (Nat.lt_succ_of_le (le_max_right _ _)).trans_le (le_max_right _ _)
  have hin : i ≠ n := Nat.ne_of_lt hi
  have hnj : n ≠ j := (Nat.ne_of_lt hj).symm
  have hcol : Commute z (generator ⟨i, n, hin, r⟩) :=
    Axis.commute_of_mem_kernel .column hz hn (Axis.generator_mem .column ⟨i, hi⟩ r)
  have hrow : Commute z (generator ⟨n, j, hnj, (1 : R)⟩) :=
    Axis.commute_of_mem_kernel .row hz hn (Axis.generator_mem .row ⟨j, hj⟩ 1)
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  have hx' : x = z := Set.mem_singleton_iff.mp hx
  subst x
  change Commute z (generator ⟨i, j, hij, r⟩)
  rw [generator_eq_commutator hij hin hnj r, commutatorElement_def]
  exact ((hcol.mul_right hrow).mul_right hcol.inv_right).mul_right hrow.inv_right

theorem steinbergExtension_isCentral (R : Type*) [Ring R] :
    IsCentralExtension (steinbergExtension R) :=
  (isCentralExtension_iff_ker_le_center _).mpr (k₂_le_center R)

theorem k₂_abelian (R : Type*) [Ring R] : IsMulCommutative (K₂ R) := by
  apply (Subgroup.le_centralizer_iff_isMulCommutative).mp
  exact (k₂_le_center R).trans (Subgroup.center_le_centralizer _)

theorem steinberg_isPerfect (R : Type*) [Ring R] : IsPerfect (Steinberg R) := by
  apply Group.isPerfect_def.mpr
  apply top_unique
  intro x _
  apply PresentedGroup.generated_by (relators R) (commutator (Steinberg R))
  rintro ⟨i, j, hij, r⟩
  let n := max i j + 1
  have hin : i ≠ n := Nat.ne_of_lt (Nat.lt_succ_of_le (le_max_left _ _))
  have hnj : n ≠ j := (Nat.ne_of_lt (Nat.lt_succ_of_le (le_max_right _ _))).symm
  change generator ⟨i, j, hij, r⟩ ∈ commutator (Steinberg R)
  rw [generator_eq_commutator hij hin hnj r, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem elementary_isPerfect (R : Type*) [Ring R] : IsPerfect (Elementary R) := by
  let := steinberg_isPerfect R
  exact Group.IsPerfect.ofSurjective toElementary_surjective

end ALG02GroupTheory.Extensions.StableSteinberg
