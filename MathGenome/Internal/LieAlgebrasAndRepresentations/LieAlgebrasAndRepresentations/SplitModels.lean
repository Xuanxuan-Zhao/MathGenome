import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SplitModels
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ChevalleyBasis
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreSimplicity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.KillingCriterion
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Module.Submodule.Union
import Batteries.Tactic.OpenPrivate

noncomputable section

open Module
open scoped TensorProduct

namespace LieAlgebrasAndRepresentations.SplitModels

universe u v w

open Specs.LieAlgebrasAndRepresentations.SplitModels
open private bracket_def from Mathlib.Algebra.Lie.BaseChange

theorem integer_span_lie_closed : latticeClosedType.{u,v} := by
  classical
  intro I L _ _ b hb x hx y hy
  let Z := Submodule.span ℤ (Set.range b)
  refine Submodule.span_induction₂ (p := fun x y _ _ => ⁅x, y⁆ ∈ Z) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    choose c hc using hb i j
    let z : I →₀ ℤ := (b.repr ⁅b i, b j⁆).mapRange
      (fun a => if h : ∃ n : ℤ, a = (n : ℂ) then h.choose else 0)
      (by
        have h : ∃ n : ℤ, (0 : ℂ) = (n : ℂ) := ⟨0, by simp⟩
        simp only [dite_eq_left h]
        exact_mod_cast h.choose_spec.symm)
    have hz (k : I) : (z k : ℂ) = b.repr ⁅b i, b j⁆ k := by
      have h : ∃ n : ℤ, b.repr ⁅b i, b j⁆ k = (n : ℂ) := ⟨c k, hc k⟩
      simp only [z, Finsupp.mapRange_apply, dite_eq_left h]
      exact h.choose_spec.symm
    have he : z.sum (fun k n => n • b k) = ⁅b i, b j⁆ := by
      apply b.repr.injective
      ext k
      simp only [Finsupp.sum, map_sum, map_zsmul, Finset.sum_apply', Basis.repr_self]
      rw [Finset.sum_eq_single k]
      · simpa [Int.cast_smul_eq_zsmul] using hz k
      · intro j _ hj
        simp [Ne.symm hj]
      · intro hk
        simp [Finsupp.notMem_support_iff.mp hk]
    rw [← he]
    exact Z.sum_mem (fun k _ => Z.smul_mem _ (Submodule.subset_span (Set.mem_range_self k)))
  · intros; simp [Z]
  · intros; simp [Z]
  · intros x y z _ _ _ hx hy
    simpa only [add_lie] using Z.add_mem hx hy
  · intros x y z _ _ _ hy hz
    simpa only [lie_add] using Z.add_mem hy hz
  · intros r x y _ _ h
    simpa only [zsmul_lie] using Z.smul_mem r h
  · intros r x y _ _ h
    simpa only [lie_zsmul] using Z.smul_mem r h

private def complexificationLinear {L : Type v} [LieRing L] [LieAlgebra ℂ L]
    (Z : LieSubalgebra ℤ L) : ℂ ⊗[ℤ] Z →ₗ[ℂ] L :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c => c • Z.incl.toLinearMap
      map_add' := fun a b => add_smul a b _
      map_smul' := fun a b => smul_assoc a b _ }

@[simp] private theorem complexificationLinear_tmul {L : Type v} [LieRing L] [LieAlgebra ℂ L]
    (Z : LieSubalgebra ℤ L) (c : ℂ) (z : Z) :
    complexificationLinear Z (c ⊗ₜ[ℤ] z) = c • (z : L) := rfl

set_option backward.isDefEq.respectTransparency false in
private def complexificationHom {L : Type v} [LieRing L] [LieAlgebra ℂ L]
    (Z : LieSubalgebra ℤ L) : ℂ ⊗[ℤ] Z →ₗ⁅ℂ⁆ L :=
  { complexificationLinear Z with
    map_lie' := by
      intro x y
      change complexificationLinear Z ⁅x, y⁆ = ⁅complexificationLinear Z x, complexificationLinear Z y⁆
      induction x using TensorProduct.inductionOn with
      | add x x' hx hx' => simp only [add_lie, map_add, hx, hx']
      | tmul a x =>
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' =>
          simp only [bracket_def, map_add, lie_add] at hy hy' ⊢
          rw [hy, hy']
        | tmul b y =>
          show complexificationLinear Z _ = ⁅complexificationLinear Z _, complexificationLinear Z _⁆
          simp [LieAlgebra.ExtendScalars.bracket_tmul, smul_lie, lie_smul, smul_smul, mul_comm] }

private theorem killingForm_lieEquiv {K M L : Type*} [Field K]
    [LieRing M] [LieAlgebra K M] [LieRing L] [LieAlgebra K L]
    (e : M ≃ₗ⁅K⁆ L) (x y : M) :
    _root_.killingForm K L (e x) (e y) = _root_.killingForm K M x y := by
  rw [killingForm_apply_apply, killingForm_apply_apply, ← LinearMap.trace_conj' _ e.toLinearEquiv]
  congr 1
  ext z
  obtain ⟨t, rfl⟩ := e.surjective z
  have ht : e.toLinearEquiv.symm (e t) = t := e.symm_apply_apply t
  simp [LinearEquiv.conj_apply, ← e.map_lie, ht]

private theorem killingForm_tmul {K Z : Type*} [Field K] [LieRing Z]
    [Module.Free ℤ Z] [Module.Finite ℤ Z] (x y : Z) :
    _root_.killingForm K (K ⊗[ℤ] Z) (1 ⊗ₜ[ℤ] x) (1 ⊗ₜ[ℤ] y) =
      (_root_.killingForm ℤ Z x y : K) := by
  simp [LieModule.traceForm_baseChange]

set_option maxHeartbeats 900000 in
/-- Complexification identifies the lattice with the given complex model.
The trace and determinant commute with extension of scalars. -/
theorem scalar_extension : scalarExtensionType.{u,v,w} := by
  classical
  intro I L _ _ _ _ b hss closed
  let Z := integerLattice b closed
  let bZ : Basis I ℤ Z := Basis.span (b.linearIndependent.restrict_scalars' ℤ)
  have hbZ (i : I) : (bZ i : L) = b i := Basis.coe_span_apply _ _
  have e_eq : (complexificationHom Z).toLinearMap =
      ((bZ.baseChange ℂ).repr.trans b.repr.symm).toLinearMap := by
    apply (bZ.baseChange ℂ).ext
    intro i
    calc
      _ = b i := by simp [complexificationHom, hbZ]
      _ = _ := by
        change b i = b.repr.symm ((bZ.baseChange ℂ).repr ((bZ.baseChange ℂ) i))
        rw [Basis.repr_self, Basis.repr_symm_single, one_smul]
  let e : (ℂ ⊗[ℤ] Z) ≃ₗ⁅ℂ⁆ L :=
    LieEquiv.ofBijective (complexificationHom Z) (by
      change Function.Bijective (complexificationHom Z).toLinearMap
      rw [e_eq]
      exact LinearEquiv.bijective _)
  have he (z : Z) : e (1 ⊗ₜ[ℤ] z) = (z : L) := by
    change complexificationLinear Z (1 ⊗ₜ[ℤ] z) = _
    simp
  letI : Module.Free ℤ Z := Module.Free.of_basis bZ
  letI : Module.Finite ℤ Z := Module.Finite.of_basis bZ
  have hdet : (integralKillingMatrix bZ).det ≠ 0 := by
    have nd := (killingForm_nondegenerate_iff_radical_eq_bot ℂ L).2 hss
    have matrix_eq : (LinearMap.BilinForm.toMatrix b (_root_.killingForm ℂ L)) =
        (integralKillingMatrix bZ).map (Int.castRingHom ℂ) := by
      ext i j
      rw [LinearMap.BilinForm.toMatrix_apply, ← hbZ i, ← hbZ j, ← he (bZ i), ← he (bZ j),
        killingForm_lieEquiv, killingForm_tmul]
      rfl
    have hn := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp nd
    change (LinearMap.BilinForm.toMatrix b (_root_.killingForm ℂ L)).det ≠ 0 at hn
    rw [matrix_eq] at hn
    change ((Int.castRingHom ℂ).mapMatrix (integralKillingMatrix bZ)).det ≠ 0 at hn
    rw [← RingHom.map_det] at hn
    exact fun hz => hn (by simp [hz])
  refine ⟨bZ, e, hbZ, he, hdet, ?_⟩
  intro K _ _
  let bK := bZ.baseChange K
  have hentry (i j : I) : _root_.killingForm K (K ⊗[ℤ] Z) (bK i) (bK j) =
      (integralKillingMatrix bZ i j : K) := by
    simp only [bK, Basis.baseChange_apply, integralKillingMatrix, killingForm_tmul]
  have hm : Matrix.of (fun i j => _root_.killingForm K (K ⊗[ℤ] Z) (bK i) (bK j)) =
      (integralKillingMatrix bZ).map (Int.castRingHom K) := by ext i j; exact hentry i j
  have hd : (Matrix.of (fun i j => _root_.killingForm K (K ⊗[ℤ] Z) (bK i) (bK j))).det =
      ((integralKillingMatrix bZ).det : K) := by
    rw [hm]
    exact (RingHom.map_det (Int.castRingHom K) (integralKillingMatrix bZ)).symm
  letI : Module.Finite K (K ⊗[ℤ] Z) := Module.Finite.of_basis bK
  refine ⟨hentry, hd, (killingForm_nondegenerate_iff_radical_eq_bot K _).mp ?_⟩
  change (_root_.killingForm K (K ⊗[ℤ] Z)).Nondegenerate
  refine LinearMap.BilinForm.nondegenerate_of_det_ne_zero
    (B₃ := _root_.killingForm K (K ⊗[ℤ] Z)) bK ?_
  have eq : LinearMap.BilinForm.toMatrix bK (_root_.killingForm K (K ⊗[ℤ] Z)) =
      Matrix.of (fun i j => _root_.killingForm K (K ⊗[ℤ] Z) (bK i) (bK j)) := by
    ext i j
    exact LinearMap.BilinForm.toMatrix_apply _ _ _ _
  rw [eq]
  rw [hd]
  exact Int.cast_ne_zero.mpr hdet


private theorem bracket_eq_zero_of_mem_span {K ι M : Type*} [CommRing K]
    [LieRing M] [LieAlgebra K M] (h : ι → M) {x y : M}
    (hx : x ∈ Submodule.span K (Set.range h))
    (hy : ∀ i, ⁅h i, y⁆ = 0) : ⁅x, y⁆ = 0 := by
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hy i
  | zero => simp
  | add a b _ _ ha hb => rw [add_lie, ha, hb, zero_add]
  | smul t a _ ha => rw [smul_lie, ha, smul_zero]

private def commutingSpan {K ι M : Type*} [CommRing K] [LieRing M] [LieAlgebra K M]
    (h : ι → M) (hc : ∀ i j, ⁅h i, h j⁆ = 0) : LieSubalgebra K M where
  toSubmodule := Submodule.span K (Set.range h)
  lie_mem' hx hy := by
    rw [bracket_eq_zero_of_mem_span h hx
      (fun i => by rw [← lie_skew, bracket_eq_zero_of_mem_span h hy (fun j => hc j i), neg_zero])]
    exact Submodule.zero_mem _

private theorem commutingSpan_abelian {K ι M : Type*} [CommRing K]
    [LieRing M] [LieAlgebra K M] (h : ι → M) (hc : ∀ i j, ⁅h i, h j⁆ = 0) :
    IsLieAbelian (commutingSpan (K := K) h hc) := by
  constructor
  intro x y
  apply Subtype.ext
  exact bracket_eq_zero_of_mem_span h x.property
    (fun i => by rw [← lie_skew, bracket_eq_zero_of_mem_span h y.property (fun j => hc j i), neg_zero])

set_option maxHeartbeats 650000 in
/-- Testing each coordinate in a diagonal basis detects every joint weight.
The same test shows that the Cartan span is self-normalizing. -/
theorem diagonal_split : diagonalSplitType.{u,v,w} := by
  classical
  intro K ι κ L _ _ _ b a ha ha0 hc hr
  let h (i : ι) := b (Sum.inl i)
  let H := commutingSpan (K := K) h hc
  let d : ι ⊕ κ → ι → K := Sum.elim (fun _ => 0) a
  have he (i : ι) (j : ι ⊕ κ) : ⁅h i, b j⁆ = d j i • b j := by
    cases j with
    | inl j => simpa [d] using hc i j
    | inr j => exact hr i j
  have hcoord (i : ι) (j : ι ⊕ κ) (x : L) :
      b.repr ⁅h i, x⁆ j = d j i * b.repr x j := by
    have eq : (b.coord j).comp (LieAlgebra.ad K L (h i)) = d j i • b.coord j := by
      apply b.ext
      intro k
      change b.repr ⁅h i, b k⁆ j = d j i * b.repr (b k) j
      rw [he, map_smul]
      change d k i * b.repr (b k) j = _
      by_cases hk : k = j
      · subst k
        rfl
      · simp [hk]
    exact DFunLike.congr_fun eq x
  have hmem (χ : ι → K) (x : L) : x ∈ jointSpace h χ ↔
      ∀ j, (b.repr x j ≠ 0 → d j = χ) := by
    change (∀ i, ⁅h i, x⁆ = χ i • x) ↔ _
    constructor
    · intro hx j hj
      funext i
      have ei := congrArg (fun y => b.repr y j) (hx i)
      rw [hcoord, map_smul] at ei
      exact mul_right_cancel₀ hj ei
    · intro hx i
      apply b.repr.injective
      ext j
      rw [hcoord, map_smul]
      change d j i * b.repr x j = χ i * b.repr x j
      by_cases hj : b.repr x j = 0
      · simp [hj]
      · rw [hx j hj]
  have hspan (x : L) : x ∈ H ↔ ∀ α, b.repr x (Sum.inr α) = 0 := by
    change x ∈ Submodule.span K (Set.range (b ∘ Sum.inl)) ↔ _
    rw [Set.range_comp, b.mem_span_image]
    constructor
    · intro hx α
      by_contra hn
      have := hx (Finsupp.mem_support_iff.mpr hn)
      simp at this
    · intro hx j hj
      cases j with
      | inl i => exact Set.mem_range_self i
      | inr α => exact False.elim ((Finsupp.mem_support_iff.mp hj) (hx α))
  have hzero : jointSpace h 0 = H.toSubmodule := by
    ext x
    rw [hmem]
    change _ ↔ x ∈ H
    rw [hspan]
    constructor
    · intro hx α
      by_contra hn
      exact ha0 α (hx (.inr α) hn)
    · intro hx j hj
      cases j with
      | inl i => rfl
      | inr α => exact False.elim (hj (hx α))
  have habel : IsLieAbelian H := commutingSpan_abelian (K := K) h hc
  have hcart : H.IsCartanSubalgebra := by
    letI := habel
    refine ⟨inferInstance, le_antisymm ?_ H.le_normalizer⟩
    intro x hx
    apply (hspan x).2
    intro α
    by_contra hn
    have hall (i : ι) : d (.inr α) i = 0 := by
      have hm := (H.mem_normalizer_iff' x).mp hx (h i) (Submodule.subset_span (Set.mem_range_self i))
      have hh := (hspan _).mp hm α
      rw [hcoord] at hh
      exact (mul_eq_zero.mp hh).resolve_right hn
    exact ha0 α (funext hall)
  refine ⟨H, rfl, habel, hcart, hc, hr, ha, ha0, hzero, ?_, ?_⟩
  · intro α
    ext x
    rw [hmem, ← Set.image_singleton, b.mem_span_image]
    constructor
    · intro hx j hj
      have hn := Finsupp.mem_support_iff.mp hj
      cases j with
      | inl i => exact False.elim (ha0 α (hx (.inl i) hn).symm)
      | inr β => exact Set.mem_singleton_iff.mpr (congrArg Sum.inr (ha (hx (.inr β) hn)))
    · intro hx j hj
      have hj' := Set.mem_singleton_iff.mp (hx (Finsupp.mem_support_iff.mpr hj))
      subst j
      rfl
  · intro χ hχ
    constructor
    · intro hne
      rw [Submodule.ne_bot_iff] at hne
      obtain ⟨x, hx, hx0⟩ := hne
      have hn : b.repr x ≠ 0 := fun h => hx0 (b.repr.injective (by simpa using h))
      obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hn
      have hd := (hmem χ x).mp hx j (by simpa using hj)
      cases j with
      | inl i => exact False.elim (hχ hd.symm)
      | inr α => exact ⟨α, hd⟩
    · rintro ⟨α, rfl⟩
      exact (Submodule.ne_bot_iff _).mpr ⟨b (.inr α), fun i => hr i α, b.ne_zero _⟩


open Serre
open scoped DirectSum

private theorem exists_regular_root_vector {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (R : Set E) (hR : IsRootSystem R) :
    ∃ z, RootRegular R z := by
  letI := hR.finite.fintype
  obtain ⟨z, hz⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun a : R => innerₛₗ ℝ a.val)
    (fun a => ⟨a.val, by simpa using hR.nonzero a.val a.property⟩)
  exact ⟨z, fun a ha => by simpa [real_inner_comm] using hz ⟨a, ha⟩⟩

private theorem radical_eq_bot_of_simple_projections {ι : Type u} {V : ι → Type v}
    {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    [∀ i, LieRing (V i)] [∀ i, LieAlgebra ℂ (V i)]
    [∀ i, LieAlgebra.IsSimple ℂ (V i)]
    (e : L ≃ₗ⁅ℂ⁆ (⨁ i, V i)) :
    LieAlgebra.radical ℂ L = ⊥ := by
  classical
  let hs : LieAlgebra.HasTrivialRadical ℂ L := by
    apply (LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals ℂ L).mpr
    intro I hI
    letI := hI
    apply le_bot_iff.mp
    intro x hx
    change x = 0
    apply e.injective
    apply DirectSum.lieAlgebra_ext ℂ
    intro i
    let f := (DirectSum.lieAlgebraComponent ℂ ι V i).comp e.toLieHom
    have hf : Function.Surjective f := fun y => ⟨e.symm (DirectSum.of V i y), by
      change (DirectSum.lieAlgebraComponent ℂ ι V i) (e (e.symm (DirectSum.of V i y))) = y
      rw [e.apply_symm_apply]
      exact DirectSum.component.lof_self ℂ i y⟩
    let g : I →ₗ⁅ℂ⁆ I.map f :=
      { (f.toLinearMap.comp I.incl.toLinearMap).codRestrict (I.map f).toSubmodule
          (fun z => LieIdeal.mem_map (f := f) z.property) with
        map_lie' := by intros; apply Subtype.ext; exact f.map_lie _ _ }
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨z, hz⟩ := LieIdeal.mem_map_of_surjective hf y.property
      exact ⟨z, Subtype.ext hz⟩
    letI hgsolv : LieAlgebra.IsSolvable (I.map f) := hg.lieAlgebra_isSolvable
    have hb : I.map f = ⊥ := LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable _
    have hfx : f x = 0 := LieIdeal.map_eq_bot_iff.mp hb hx
    simpa [f] using hfx
  exact hs.radical_eq_bot

private theorem serre_cartan_isCartan {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)
    (hc : ∀ i j, ⁅h A i, h A j⁆ = 0) (hzero : weightSpace A 0 = cartan A) :
    (commutingSpan (K := ℂ) (h A) hc).IsCartanSubalgebra := by
  let H := commutingSpan (K := ℂ) (h A) hc
  letI : IsLieAbelian H := commutingSpan_abelian (K := ℂ) (h A) hc
  let N := ⨆ χ ≠ (0 : ι → ℂ), weightSpace A χ
  have dis : Disjoint H.toSubmodule N := by
    change Disjoint (cartan A) N
    rw [← hzero]
    exact weightSpace_iSupIndep A 0
  have sup : H.toSubmodule ⊔ N = ⊤ := by
    apply top_unique
    rw [← weightSpace_iSup_eq_top A]
    refine iSup_le (fun χ => ?_)
    by_cases hχ : χ = 0
    · subst χ
      rw [hzero]
      exact le_sup_left
    · exact (le_iSup₂ (f := fun χ _ => weightSpace A χ) χ hχ).trans le_sup_right
  have stable (i : ι) : N ≤ N.comap (LieAlgebra.ad ℂ (Algebra A) (h A i)) := by
    refine iSup₂_le (fun χ hχ y hy => ?_)
    change ⁅h A i, y⁆ ∈ N
    have he : ⁅h A i, y⁆ = χ i • y := hy i
    rw [he]
    exact N.smul_mem _ (le_iSup₂ (f := fun χ _ => weightSpace A χ) χ hχ hy)
  refine ⟨inferInstance, le_antisymm ?_ H.le_normalizer⟩
  intro x hx
  have hm : x ∈ H.toSubmodule ⊔ N := by rw [sup]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hm
  have hzi (i : ι) : ⁅h A i, z⁆ = 0 := by
    have he := (H.mem_normalizer_iff' (y + z)).mp hx (h A i)
      (Submodule.subset_span (Set.mem_range_self i))
    rw [lie_add, ← lie_skew (h A i) y,
      bracket_eq_zero_of_mem_span (h A) hy (fun j => hc j i), neg_zero, zero_add] at he
    exact Submodule.disjoint_def.mp dis _ he (stable i hz)
  have hzH : z ∈ H := by
    change z ∈ cartan A
    rw [← hzero]
    exact fun i => by simpa using hzi i
  exact H.add_mem hy hzH

private def euclideanWeight {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : ι → E) : E →ₗ[ℝ] ι → ℂ :=
  LinearMap.pi (fun i => Complex.ofRealCLM.toLinearMap.comp
    ((2 / inner ℝ (s i) (s i)) • innerₛₗ ℝ (s i)))

private theorem euclideanWeight_apply {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : ι → E) (a : E) :
    euclideanWeight s a = rootWeight s a := by
  ext i
  simp [euclideanWeight, rootWeight, rootCartan, real_inner_comm, div_mul_eq_mul_div]

private theorem rootSpace_eq_serreWeight {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)
    (H : LieSubalgebra ℂ (Algebra A)) (bH : Basis ι ℂ H)
    (hbH : ∀ i, (bH i : Algebra A) = h A i) (μ : Module.Dual ℂ H) :
    rootSpace H μ = weightSpace A (fun i => μ (bH i)) := by
  ext x
  rw [mem_rootSpace]
  change (∀ y : H, ⁅(y : Algebra A), x⁆ = μ y • x) ↔
    ∀ i, ⁅h A i, x⁆ = μ (bH i) • x
  constructor
  · intro hx i
    rw [← hbH i, hx]
  · intro hx
    have eq : ((LieAlgebra.ad ℂ (Algebra A)).flip x).comp H.incl.toLinearMap =
        μ.smulRight x := by
      apply bH.ext
      intro i
      change ⁅(bH i : Algebra A), x⁆ = μ (bH i) • x
      rw [hbH, hx]
    exact DFunLike.congr_fun eq


/-- The Euclidean reflection reverses the ends of the common integer string.
The two endpoint inequalities identify the prescribed Cartan integer. -/
private theorem prescribed_coroot_pairing {E L : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [LieRing L] [LieAlgebra ℂ L] [Module.Finite ℂ L]
    {R : Set E} (hR : IsRootSystem R) (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (f : E →ₗ[ℝ] Module.Dual ℂ H) (hf : Function.Injective f)
    (hroots : ∀ a, f a ∈ rootSet H ↔ a ∈ R)
    (a b : R) (m : ℤ) (hm : (m : ℝ) = rootCartan b.val a.val) :
    f b.val (killingCoroot H (f a.val)) = (m : ℂ) := by
  have ha := (hroots a.val).2 a.property
  have hb := (hroots b.val).2 b.property
  have hself : f a.val (killingCoroot H (f a.val)) = 2 := by
    rw [killingCoroot_pairing hss H hH, mul_div_cancel_right₀ _ (rootForm_self_ne_zero hss H hH _ ha)]
  by_cases hba : b.val = a.val
  · have hma : (m : ℝ) = 2 := by
      rw [hm, hba, rootCartan, mul_div_cancel_right₀ _ (inner_self_ne_zero (hR.nonzero _ a.property))]
    rw [hba, hself]
    exact_mod_cast hma.symm
  by_cases hbna : b.val = -a.val
  · have hma : (m : ℝ) = -2 := by
      rw [hm, hbna, rootCartan, inner_neg_left, mul_neg, neg_div,
        mul_div_cancel_right₀ _ (inner_self_ne_zero (hR.nonzero _ a.property))]
    rw [hbna, map_neg, LinearMap.neg_apply, hself]
    exact_mod_cast hma.symm
  obtain ⟨p, q, hpq, hinterval⟩ := RootStrings.root_string hss H hH
    (f a.val) (f b.val) ha hb (fun h => hba (hf h)) (fun h => hbna (hf (h.trans (f.map_neg _).symm)))
  have hint (k : ℤ) : b.val + k • a.val ∈ R ↔ -(p : ℤ) ≤ k ∧ k ≤ (q : ℤ) := by
    rw [← hroots, map_add, map_zsmul]
    exact hinterval k
  have href (k : ℤ) (hk : b.val + k • a.val ∈ R) :
      b.val + (-m - k) • a.val ∈ R := by
    have he := hR.reflection_mem a.val a.property _ hk
    have refl_eq : rootReflection a.val (b.val + k • a.val) =
        b.val + (-m - k) • a.val := by
      have hn := inner_self_ne_zero (hR.nonzero _ a.property)
      have cart : rootCartan (b.val + k • a.val) a.val = (m : ℝ) + 2 * (k : ℝ) := by
        change 2 * inner ℝ (b.val + k • a.val) a.val / inner ℝ a.val a.val = _
        change (m : ℝ) = 2 * inner ℝ b.val a.val / inner ℝ a.val a.val at hm
        rw [inner_add_left, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left,
          mul_add, add_div, ← hm]
        field_simp
      change b.val + k • a.val - rootCartan (b.val + k • a.val) a.val • a.val = _
      rw [cart, ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ]
      push_cast
      module
    rwa [refl_eq] at he
  have hl := (hint _).mp (href (-(p : ℤ)) ((hint _).mpr (by omega)))
  have hu := (hint _).mp (href (q : ℤ) ((hint _).mpr (by omega)))
  have hm' : m = (p : ℤ) - (q : ℤ) := by omega
  rw [hpq, hm']
  push_cast
  rfl

private theorem scalar_extend_bracket {K L : Type*} [Field K] [LieRing L] [LieAlgebra ℂ L]
    (Z : LieSubalgebra ℤ L) (x y : Z) (z : Z) (n : ℤ)
    (h : ⁅(x : L), (y : L)⁆ = (n : ℂ) • (z : L)) :
    ⁅(1 ⊗ₜ[ℤ] x : K ⊗[ℤ] Z), (1 ⊗ₜ[ℤ] y : K ⊗[ℤ] Z)⁆ =
      (n : K) • (1 ⊗ₜ[ℤ] z : K ⊗[ℤ] Z) := by
  have hh : ⁅x, y⁆ = n • z :=
    Subtype.ext (by
      change ⁅(x : L), (y : L)⁆ = n • (z : L)
      simpa only [Int.cast_smul_eq_zsmul] using h)
  rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, hh, TensorProduct.tmul_smul,
    Int.cast_smul_eq_zsmul]

private theorem scalar_extend_double_bracket {K L : Type*} [Field K] [LieRing L]
    [LieAlgebra ℂ L] (Z : LieSubalgebra ℤ L) (x y z : Z) (n : ℤ)
    (h : ⁅⁅(x : L), (y : L)⁆, (z : L)⁆ = (n : ℂ) • (z : L)) :
    ⁅⁅(1 ⊗ₜ[ℤ] x : K ⊗[ℤ] Z), (1 ⊗ₜ[ℤ] y : K ⊗[ℤ] Z)⁆,
        (1 ⊗ₜ[ℤ] z : K ⊗[ℤ] Z)⁆ = (n : K) • (1 ⊗ₜ[ℤ] z : K ⊗[ℤ] Z) := by
  rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  exact scalar_extend_bracket Z ⁅x, y⁆ z z n h


private theorem scalar_extend_commutes_with_bracket {K L : Type*} [Field K] [LieRing L]
    [LieAlgebra ℂ L] (Z : LieSubalgebra ℤ L) (x y z : Z)
    (h : ⁅(x : L), ⁅(y : L), (z : L)⁆⁆ = 0) :
    ⁅(1 ⊗ₜ[ℤ] x : K ⊗[ℤ] Z),
      ⁅(1 ⊗ₜ[ℤ] y : K ⊗[ℤ] Z), (1 ⊗ₜ[ℤ] z : K ⊗[ℤ] Z)⁆⁆ = 0 := by
  have eq : ⁅x, ⁅y, z⁆⁆ = 0 := Subtype.ext h
  simp only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, eq, TensorProduct.tmul_zero]

set_option maxHeartbeats 2200000 in
/-- The normalized Chevalley basis of the complex Serre realization gives the
split model over every characteristic-zero field by tensoring its integer span. -/
theorem split_model : splitModelType.{u,w} := by
  classical
  intro E _ _ R hR
  letI : Fintype R := hR.finite.fintype
  obtain ⟨z, hz⟩ := exists_regular_root_vector R hR
  obtain ⟨s, hs⟩ := simpleRoots_basis R hR z hz
  let ι := simpleRoots R z
  letI : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := (simpleRoots_finite hR.toRootAxioms z).fintype
  have hsimple : IsSimpleBasis R z s := by
    simpa only [IsSimpleBasis, show (⇑s : ι → E) = Subtype.val from funext hs] using
      (Subtype.range_coe (s := simpleRoots R z))
  have hsm (i : ι) : s i ∈ R := hsimple.root_mem i
  let si (i : ι) : R := ⟨s i, hsm i⟩
  choose p hp using fun (α β : R) => hR.integral α.val α.property β.val β.property
  let A : Matrix ι ι ℤ := fun i j => p (si i) (si j)
  have hA (i j : ι) : (A i j : ℝ) = cartanMatrix s i j := (hp (si i) (si j)).symm
  have hcond := cartanConditions_spec R hR z hz s hsimple A hA
  let L := Algebra A
  obtain ⟨finite, _, hsupport, _, hzero, _, _⟩ := finiteType_spec R hR z hz s hsimple A hA
  letI : Module.Finite ℂ L := finite
  let V (c : Component A) := Algebra (componentMatrix A c)
  letI (c : Component A) : LieAlgebra.IsSimple ℂ (V c) :=
    componentSimple_spec R hR z hz s hsimple A hA c
  obtain ⟨ce, _⟩ := componentSum_spec R hR z hz s hsimple A hA
  have hss : IsSemisimple ℂ L := radical_eq_bot_of_simple_projections ce.symm
  letI : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  have hc := (relations_spec A hcond.2.1).1
  let H := commutingSpan (K := ℂ) (h A) hc
  letI : IsLieAbelian H := commutingSpan_abelian (K := ℂ) (h A) hc
  letI : H.IsCartanSubalgebra := serre_cartan_isCartan A hc hzero
  have hH : IsMaximalToral H := by
    refine ⟨⟨inferInstance, fun x => ?_⟩, ?_⟩
    · exact LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra x.property
    · intro K hK hHK x hx
      have hn : x ∈ H.normalizer := (H.mem_normalizer_iff' x).mpr fun y hy => by
        letI : IsLieAbelian K := hK.1
        have he := trivial_lie_zero K K (⟨y, hHK hy⟩ : K) ⟨x, hx⟩
        have he' : ⁅y, x⁆ = 0 := congrArg Subtype.val he
        rw [he']
        exact H.zero_mem
      rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at hn
  obtain ⟨bH, hbH⟩ : ∃ bH : Basis ι ℂ H, (∀ i, (bH i : L) = h A i) :=
    (triangular_of_cartanConditions A hcond).2.1
  -- The Euclidean roots embed into the full complex dual through their joint weights.
  let f : E →ₗ[ℝ] Module.Dual ℂ H :=
    ((bH.constr ℂ).toLinearMap.restrictScalars ℝ).comp (euclideanWeight s)
  have hfw (a : E) (i : ι) : f a (bH i) = rootWeight s a i := by
    change (bH.constr ℂ (euclideanWeight s a)) (bH i) = rootWeight s a i
    rw [Basis.constr_basis, euclideanWeight_apply]
  have hf : Function.Injective f := fun a b h => rootWeight_injective s (funext fun i =>
    (hfw a i).symm.trans ((congrArg (fun g : Module.Dual ℂ H => g (bH i)) h).trans (hfw b i)))
  have hre (μ : Module.Dual ℂ H) :
      rootSpace H μ = weightSpace A (fun i => μ (bH i)) := rootSpace_eq_serreWeight A H bH hbH μ
  have hweight_nonzero (μ : Module.Dual ℂ H) (hμ : μ ≠ 0) : (fun i => μ (bH i)) ≠ 0 := by
    intro h
    apply hμ
    apply bH.ext
    intro i
    exact congrFun h i
  have hroot (μ : Module.Dual ℂ H) :
      μ ∈ rootSet H ↔ ∃ a ∈ R, f a = μ := by
    constructor
    · rintro ⟨hμ, hsp⟩
      change rootSpace H μ ≠ ⊥ at hsp
      rw [hre μ] at hsp
      obtain ⟨a, ha, he⟩ := (hsupport _ (hweight_nonzero μ hμ)).1 hsp
      refine ⟨a, ha, bH.ext (fun i => ?_)⟩
      exact (hfw a i).trans (congrFun he i).symm
    · rintro ⟨a, ha, rfl⟩
      have hn : f a ≠ 0 := fun h => hR.nonzero a ha (hf (h.trans (map_zero f).symm))
      refine ⟨hn, ?_⟩
      change rootSpace H (f a) ≠ ⊥
      rw [hre (f a)]
      exact (hsupport _ (hweight_nonzero _ hn)).2 ⟨a, ha, funext (hfw a)⟩
  have hroots (x : E) : f x ∈ rootSet H ↔ x ∈ R := by
    rw [hroot]
    constructor
    · rintro ⟨a, ha, he⟩
      simpa only [hf he] using ha
    · intro hx
      exact ⟨x, hx, rfl⟩
  let rootLabel : R ≃ rootSet H := Equiv.ofBijective
    (fun a => ⟨f a.val, (hroots a.val).2 a.property⟩)
    ⟨fun a b h => Subtype.ext (hf (congrArg Subtype.val h)), fun b => by
      obtain ⟨a, ha, he⟩ := (hroot b.val).1 b.property
      exact ⟨⟨a, ha⟩, Subtype.ext he⟩⟩
  obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  let φ := (innerₛₗ ℝ z).comp r
  have hφeval (x : E) : φ (f x) = inner ℝ z x := by
    change inner ℝ z (r (f x)) = _
    rw [show r (f x) = x from DFunLike.congr_fun hr x]
  have hφ (μ : Module.Dual ℂ H) (hμ : μ ∈ rootSet H) : φ μ ≠ 0 := by
    obtain ⟨x, hx, rfl⟩ := (hroot μ).mp hμ
    rw [hφeval]
    exact hz x hx
  open Specs.LieAlgebrasAndRepresentations.SerreRelations in
  have hpos (x : E) : f x ∈ positive H φ ↔ x ∈ positiveRoots R z := by
    change (f x ∈ rootSet H ∧ 0 < φ (f x)) ↔ (x ∈ R ∧ 0 < inner ℝ z x)
    rw [hroots, hφeval]
  open Specs.LieAlgebrasAndRepresentations.SerreRelations in
  have hsimp (x : E) : f x ∈ simple H φ ↔ x ∈ simpleRoots R z := by
    constructor
    · rintro ⟨hx, hins⟩
      refine ⟨(hpos x).1 hx, fun a ha b hb eq => ?_⟩
      exact hins (f a) ((hpos a).2 ha) (f b) ((hpos b).2 hb) (by rw [← map_add, eq])
    · rintro ⟨hx, hins⟩
      refine ⟨(hpos x).2 hx, fun a ha b hb eq => ?_⟩
      obtain ⟨a', _, rfl⟩ := (hroot a).1 ha.1
      obtain ⟨b', _, rfl⟩ := (hroot b).1 hb.1
      exact hins a' ((hpos a').1 ha) b' ((hpos b').1 hb) (hf (eq.trans (map_add f _ _).symm))
  let simpleLabel : ι ≃ Specs.LieAlgebrasAndRepresentations.SerreRelations.simple H φ :=
    Equiv.ofBijective (fun i => ⟨f i.val, (hsimp i.val).2 i.property⟩)
      ⟨fun a b h => Subtype.ext (hf (congrArg Subtype.val h)), fun a => by
        obtain ⟨x, _, he⟩ := (hroot a.val).1 a.property.1.1
        exact ⟨⟨x, (hsimp x).1 (he.symm ▸ a.property)⟩, Subtype.ext he⟩⟩
  have hlabel (i : ι) : (rootLabel (si i)).val = (simpleLabel i).val := congrArg f (hs i)
  obtain ⟨negRoot, x, N, σ, bc, hxb, hOpp, hσ₂, hσ, hSign, hConstants, hZeroBracket,
    hbcH, hbcR, hint, _, _⟩ :=
    chevalley_basis hss H hH φ hφ
  let b := bc.reindex (Equiv.sumCongr simpleLabel.symm rootLabel.symm)
  have hbC (i : ι) : b (.inl i) = (killingCoroot H (simpleLabel i).val : L) := by
    simpa [b] using hbcH (simpleLabel i)
  have hbR (α : R) : b (.inr α) = x (rootLabel α) := by simp [b, hbcR]
  have hbRoot (α : rootSet H) : b (.inr (rootLabel.symm α)) = x α := by
    rw [hbR, rootLabel.apply_symm_apply]
  have hrootmem (α : R) : b (.inr α) ∈ rootSpace H (rootLabel α).val := by
    rw [hbR]
    exact (hxb (rootLabel α)).1
  let opp (α : R) : R := ⟨-α.val, hR.toRootAxioms.neg_mem α.property⟩
  have hopp (α : R) :
      rootLabel (opp α) = ⟨-(rootLabel α).val, negRoot (rootLabel α)⟩ :=
    Subtype.ext (f.map_neg α.val)
  have hbrOpp (α : R) : ⁅b (.inr α), b (.inr (opp α))⁆ =
      (killingCoroot H (rootLabel α).val : L) := by
    rw [hbR, hbR, hopp]
    exact hOpp (rootLabel α)
  have hInt : IntegralBasis b := by
    intro i j k
    simpa [b, Basis.repr_reindex_apply] using
      hint ((Equiv.sumCongr simpleLabel rootLabel) i)
        ((Equiv.sumCongr simpleLabel rootLabel) j) ((Equiv.sumCongr simpleLabel rootLabel) k)
  have hpR (α β : R) : (p α β : ℝ) = rootCartan β.val α.val := (hp α β).symm
  have hpair (α β : R) :
      (rootLabel β).val (killingCoroot H (rootLabel α).val) = (p α β : ℂ) :=
    prescribed_coroot_pairing hR hss H hH f hf hroots α β (p α β) (hpR α β)
  let a (α : R) (i : ι) := p (si i) α
  have ha : RootCoordinates s a := fun α i => hpR (si i) α
  have closed := integer_span_lie_closed b hInt
  let Z := integerLattice b closed
  obtain ⟨bZ, e, hbZ, he, hdet, hK⟩ := scalar_extension b hss closed
  refine ⟨z, ι, inferInstance, s, hsm, A, finite, H, φ, f, simpleLabel, rootLabel, b, negRoot, N, σ,
    a, p, closed, hz, hsimple, hA, hss, hH, hφ, hf, (fun _ => rfl), hlabel, hbC, hrootmem,
    hbrOpp, hopp, hσ₂, hσ, ?_, ?_, ?_, hInt, ha, hpR, bZ, e, hbZ, he, hdet, ?_⟩
  · intro α
    simpa only [hbRoot] using hSign α
  · intro α β hab
    simpa only [hbRoot] using hConstants α β hab
  · intro α β hne hab
    simpa only [hbRoot] using hZeroBracket α β hne hab
  intro K _ _
  let bK := bZ.baseChange K
  obtain ⟨_, hdK, hssK⟩ := hK K
  have hCC (i j : ι) : ⁅b (.inl i), b (.inl j)⁆ = 0 := by
    rw [hbC, hbC, ← LieSubalgebra.coe_bracket, trivial_lie_zero]
    rfl
  have hCR (i : ι) (α : R) : ⁅b (.inl i), b (.inr α)⁆ = (a α i : ℂ) • b (.inr α) := by
    rw [hbC, ← hlabel, (mem_rootSpace _ _ _).1 (hrootmem α) _, hpair]
  have hCCK (i j : ι) : ⁅bK (.inl i), bK (.inl j)⁆ = 0 := by
    have eq : ⁅bZ (.inl i), bZ (.inl j)⁆ = 0 :=
      Subtype.ext (by simpa only [LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero, hbZ] using hCC i j)
    simp [bK, LieAlgebra.ExtendScalars.bracket_tmul, eq]
  have hCRK (i : ι) (α : R) : ⁅bK (.inl i), bK (.inr α)⁆ = (a α i : K) • bK (.inr α) := by
    simpa only [bK, Basis.baseChange_apply] using
      scalar_extend_bracket (K := K) Z (bZ (.inl i)) (bZ (.inr α)) (bZ (.inr α)) (a α i)
        (by simpa only [hbZ] using hCR i α)
  let aK (α : R) (i : ι) : K := (a α i : K)
  have haK (α β : R) (h : aK α = aK β) : α = β := by
    apply Subtype.ext
    apply rootWeight_injective s
    funext i
    have he : a α i = a β i := Int.cast_injective (congrFun h i)
    change (↑(rootCartan α.val (s i)) : ℂ) = ↑(rootCartan β.val (s i))
    rw [← ha α i, ← ha β i, he]
  have haK0 (α : R) : aK α ≠ 0 := by
    intro h
    apply hR.nonzero α.val α.property
    apply rootWeight_injective s
    rw [rootWeight_zero]
    funext i
    have he : a α i = 0 := Int.cast_eq_zero.mp (congrFun h i)
    change (↑(rootCartan α.val (s i)) : ℂ) = 0
    rw [← ha α i, he]
    simp
  have hsplit := diagonal_split bK aK haK haK0 hCCK hCRK
  have hzeroModel (hempty : IsEmpty R) : Subsingleton (K ⊗[ℤ] Z) := by
    letI := hempty
    letI : IsEmpty ι := ⟨fun i => isEmptyElim (si i)⟩
    exact bK.repr.injective.subsingleton
  refine ⟨Module.Finite.of_basis bK, hzeroModel, hssK, hdK, hsplit, ?_, ?_⟩
  · intro α
    obtain ⟨T, hT, _, _, _, _, _, _, hzeroK, _, _⟩ := hsplit
    rw [← hT, ← hzeroK]
    intro i
    have hC : ⁅b (.inl i), ⁅b (.inr α), b (.inr (opp α))⁆⁆ = 0 := by
      rw [hbC, hbrOpp, ← LieSubalgebra.coe_bracket, trivial_lie_zero]
      rfl
    change ⁅bK (.inl i), ⁅bK (.inr α), bK (.inr (opp α))⁆⁆ = 0 • _
    rw [zero_smul]
    simpa only [bK, Basis.baseChange_apply] using
      scalar_extend_commutes_with_bracket (K := K) Z (bZ (.inl i)) (bZ (.inr α)) (bZ (.inr (opp α)))
        (by simpa only [hbZ] using hC)
  · intro α β
    have heC : ⁅⁅b (.inr α), b (.inr (opp α))⁆, b (.inr β)⁆ =
        (p α β : ℂ) • b (.inr β) := by
      rw [hbrOpp, (mem_rootSpace _ _ _).1 (hrootmem β) _, hpair]
    simpa only [bK, Basis.baseChange_apply] using
      scalar_extend_double_bracket (K := K) Z (bZ (.inr α)) (bZ (.inr (opp α))) (bZ (.inr β))
        (p α β) (by simpa only [hbZ] using heC)

end LieAlgebrasAndRepresentations.SplitModels
