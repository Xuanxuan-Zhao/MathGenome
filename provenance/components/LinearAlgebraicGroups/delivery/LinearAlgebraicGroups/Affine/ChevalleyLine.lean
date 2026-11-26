import Specs.LinearAlgebraicGroups.Affine.ChevalleyLine
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import LinearAlgebraicGroups.Affine.RationalRepresentations
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.FiniteType

open AlgebraicGeometry CategoryTheory Coalgebra WithConv Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

set_option backward.isDefEq.respectTransparency false

private def exteriorMatrix {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (d : ℕ) (M : Matrix ι ι R) :
    Matrix (Set.powersetCard ι d) (Set.powersetCard ι d) R :=
  fun s t ↦ (M.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
    (Set.powersetCard.ofFinEmbEquiv.symm t)).det

private theorem exteriorMatrix_toMatrix {R ι : Type u} [CommRing R] [Fintype ι]
    [DecidableEq ι] [LinearOrder ι] (d : ℕ) (M : Matrix ι ι R) :
    exteriorMatrix d M =
      LinearMap.toMatrix ((Pi.basisFun R ι).exteriorPower d) ((Pi.basisFun R ι).exteriorPower d)
        (exteriorPower.map d (Matrix.toLin' M)) := by
  ext s t
  rw [LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, exteriorPower.basis_coord,
    exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti, ← Matrix.det_transpose]
  unfold exteriorMatrix
  apply congrArg Matrix.det
  ext i j
  simp [Matrix.toLin'_apply', Pi.basisFun_apply, Matrix.mulVec_single]

private theorem exteriorMatrix_one {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (d : ℕ) :
    exteriorMatrix d (1 : Matrix ι ι R) = 1 := by
  rw [exteriorMatrix_toMatrix, Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]

private theorem exteriorMatrix_mul {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (d : ℕ) (M N : Matrix ι ι R) :
    exteriorMatrix d (M * N) = exteriorMatrix d M * exteriorMatrix d N := by
  simp only [exteriorMatrix_toMatrix, Matrix.toLin'_mul, exteriorPower.map_comp]
  rw [← Module.End.mul_eq_comp, LinearMap.toMatrix_mul]

private theorem exteriorMatrix_map {R S ι : Type u} [CommRing R] [CommRing S]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] (d : ℕ) (M : Matrix ι ι R) (f : R →+* S) :
    exteriorMatrix d (M.map f) = (exteriorMatrix d M).map f := by
  ext s t
  exact (f.map_det _).symm

private theorem exteriorIsCoactionMatrix {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (A : HopfAlgebraCategory k) (d : ℕ) (M : Matrix ι ι A)
    (hM : RationalRepresentations.IsCoactionMatrix A M) :
    RationalRepresentations.IsCoactionMatrix A (exteriorMatrix d M) := by
  let l : A →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.includeRight
  have hc : M.map (Bialgebra.comulAlgHom k A).toRingHom = M.map l.toRingHom * M.map r.toRingHom := by
    ext i j
    change comul (R := k) (M i j) = ∑ t, (M i t ⊗ₜ[k] (1 : A)) * ((1 : A) ⊗ₜ[k] M t j)
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hM.comul i j
  have he : M.map (Bialgebra.counitAlgHom k A).toRingHom = 1 := by
    ext i j
    exact hM.counit i j
  constructor
  · intro s t
    have h := congrArg (exteriorMatrix d) hc
    rw [exteriorMatrix_map d M (Bialgebra.comulAlgHom k A).toRingHom, exteriorMatrix_mul,
      exteriorMatrix_map d M l.toRingHom, exteriorMatrix_map d M r.toRingHom] at h
    have h' := congrArg (fun N : Matrix (Set.powersetCard ι d) (Set.powersetCard ι d)
      (A ⊗[k] A) ↦ N s t) h
    change comul (R := k) (exteriorMatrix d M s t) =
      ∑ a, (exteriorMatrix d M s a ⊗ₜ[k] (1 : A)) * ((1 : A) ⊗ₜ[k] exteriorMatrix d M a t) at h'
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using h'
  · intro s t
    have h := congrArg (exteriorMatrix d) he
    rw [exteriorMatrix_map d M (Bialgebra.counitAlgHom k A).toRingHom, exteriorMatrix_one] at h
    exact congrArg (fun N ↦ N s t) h

private abbrev BlockIndex (p q : ℕ) := ULift.{u} (Fin (p + q))

private def leftIndex {p q : ℕ} (i : Fin p) : BlockIndex.{u} p q :=
  ⟨Fin.castAdd q i⟩

private def rightIndex {p q : ℕ} (j : Fin q) : BlockIndex.{u} p q :=
  ⟨Fin.natAdd p j⟩

private def blockIndexEquiv {p q : ℕ} : Fin p ⊕ Fin q ≃ BlockIndex.{u} p q :=
  finSumFinEquiv.trans Equiv.ulift.symm

@[simp] private theorem blockIndexEquiv_inl {p q : ℕ} (i : Fin p) :
    blockIndexEquiv.{u} (q := q) (.inl i) = leftIndex i := rfl

@[simp] private theorem blockIndexEquiv_inr {p q : ℕ} (j : Fin q) :
    blockIndexEquiv.{u} (p := p) (.inr j) = rightIndex j := rfl

private theorem rightIndex_ne_leftIndex {p q : ℕ} (j : Fin q) (i : Fin p) :
    rightIndex.{u} j ≠ leftIndex i := by
  intro h
  have := congrArg (fun x : BlockIndex p q ↦ x.down.val) h
  simp [rightIndex, leftIndex] at this
  omega

@[simp] private theorem leftIndex_inj {p q : ℕ} {i j : Fin p} :
    leftIndex.{u} (q := q) i = leftIndex j ↔ i = j := by
  simp [leftIndex]

private def leftOrderEmbedding (p q : ℕ) : Fin p ↪o BlockIndex.{u} p q :=
  OrderEmbedding.ofStrictMono leftIndex (Fin.strictMono_castAdd q)

private def initialSubset (p q : ℕ) : Set.powersetCard (BlockIndex.{u} p q) p :=
  Set.powersetCard.ofFinEmbEquiv (leftOrderEmbedding p q)

@[simp] private theorem initialSubset_embedding {p q : ℕ} (i : Fin p) :
    Set.powersetCard.ofFinEmbEquiv.symm (initialSubset.{u} p q) i = leftIndex i := by
  simp [initialSubset]
  rfl

private theorem wedge_annihilator {R : Type u} [CommRing R] {p q : ℕ}
    (v : BlockIndex.{u} p q → R) :
    let b := Pi.basisFun R (BlockIndex.{u} p q)
    let w := b.exteriorPower p (initialSubset p q)
    ExteriorAlgebra.ι R v * w.1 = 0 ↔ ∀ j : Fin q, v (rightIndex j) = 0 := by
  classical
  let b := Pi.basisFun R (BlockIndex.{u} p q)
  let a : Fin p → (BlockIndex.{u} p q → R) := b ∘ leftIndex (q := q)
  have hw : b.exteriorPower p (initialSubset p q) = exteriorPower.ιMulti R p a := by
    simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family, a, Function.comp_def]
  change ExteriorAlgebra.ι R v * (b.exteriorPower p (initialSubset p q)).1 = 0 ↔ _
  rw [hw]
  have happ (x : BlockIndex.{u} p q → R) :
      ExteriorAlgebra.ι R x * (exteriorPower.ιMulti R p a).1 =
        (exteriorPower.ιMulti R (p + 1) (Fin.cons x a)).1 := by
    rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_succ_apply]
    rfl
  constructor
  · intro h j
    rw [happ] at h
    have hz : exteriorPower.ιMulti R (p+1) (Fin.cons v a) = 0 := Subtype.ext h
    let f : Fin (p+1) → Module.Dual R (BlockIndex.{u} p q → R) :=
      Fin.cons (b.coord (rightIndex j)) (b.coord ∘ leftIndex (q := q))
    have hdet := congrArg (exteriorPower.alternatingMapToDual R (BlockIndex.{u} p q → R) (p+1) f) hz
    rw [map_zero, exteriorPower.alternatingMapToDual_apply_ιMulti] at hdet
    let va : Fin (p+1) → (BlockIndex.{u} p q → R) := Fin.cons v a
    let D : Matrix (Fin (p+1)) (Fin (p+1)) R := .of (fun i j ↦ f j (va i))
    have hD₀ : ∀ i : Fin p, D i.succ 0 = 0 := by
      intro i
      simp [D, f, va, a, b, Module.Basis.coord_apply, rightIndex_ne_leftIndex]
    have hD₁ : D.submatrix Fin.succ Fin.succ = 1 := by
      ext i j
      change b.coord (leftIndex j) (b (leftIndex i)) = (1 : Matrix (Fin p) (Fin p) R) i j
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
      simp
    change D.det = 0 at hdet
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ] at hdet
    simp only [hD₀, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
      Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hD₁, Matrix.det_one, mul_one] at hdet
    exact hdet
  · intro hv
    have hsum : v = ∑ i : Fin p, v (leftIndex i) • a i := by
      ext j
      obtain ⟨i, rfl⟩ := blockIndexEquiv.surjective j
      rcases i with i | j
      · simp [a, b, Pi.basisFun_apply, Pi.single_apply]
      · simp [a, b, Pi.basisFun_apply, rightIndex_ne_leftIndex, hv j]
    let F : (BlockIndex.{u} p q → R) →ₗ[R] ExteriorAlgebra R (BlockIndex.{u} p q → R) :=
      (LinearMap.mulRight R (exteriorPower.ιMulti R p a).1).comp (ExteriorAlgebra.ι R)
    change F v = 0
    rw [hsum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    have hz : F (a i) = 0 := by
      change ExteriorAlgebra.ι R (a i) * _ = 0
      rw [happ]
      have eq : exteriorPower.ιMulti R (p+1) (Fin.cons (a i) a) = 0 :=
        AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := i.succ) (by simp) (Fin.succ_ne_zero _).symm
      rw [eq]
      rfl
    rw [hz, smul_zero]

private def exteriorGL {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (d : ℕ) :
    Matrix.GeneralLinearGroup ι R →* Matrix.GeneralLinearGroup (Set.powersetCard ι d) R :=
  Units.map
    { toFun := exteriorMatrix d
      map_one' := exteriorMatrix_one d
      map_mul' := exteriorMatrix_mul d }

private theorem coordinateLine_iff_unit {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    (m : Matrix.GeneralLinearGroup ι R) (i : ι) :
    Specs.StabilizesCoordinateLine m i ↔
      ∃ a : Rˣ, ∀ j, m.val j i = if j = i then (a : R) else 0 := by
  let v : ι → R := Pi.single i 1
  let F := Matrix.toLin' m.val
  have hcol (a : R) : F v = a • v ↔ ∀ j, m.val j i = if j = i then a else 0 := by
    have hv (j) : F v j = m.val j i := by
      simp [F, v, Matrix.toLin'_apply']
    have ha (j) : (a • v) j = if j = i then a else 0 := by
      by_cases h : j = i <;> simp [v, h]
    rw [funext_iff]
    simp_rw [hv, ha]
  change (Submodule.span R {v}).map F = Submodule.span R {v} ↔ _
  rw [Submodule.map_span, Set.image_singleton]
  constructor
  · intro heq
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (heq ▸ Submodule.mem_span_singleton_self (R := R) (F v))
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
      (heq.symm ▸ Submodule.mem_span_singleton_self (R := R) v)
    have hab : b * a = 1 := by
      have h : b • (a • v) = v := by rw [ha, hb]
      simpa [v, smul_eq_mul] using congrFun h i
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv'.mpr (show ∃ b, b * a = 1 from ⟨b, hab⟩)
    exact ⟨c, (hcol _).mp (hc.symm ▸ ha.symm)⟩
  · rintro ⟨a, ha⟩
    rw [(hcol _).mpr ha]
    exact Submodule.span_singleton_smul_eq a.isUnit v

private theorem coordinateLine_iff {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    (m : Matrix.GeneralLinearGroup ι R) (i : ι) :
    Specs.StabilizesCoordinateLine m i ↔ ∀ j ≠ i, m.val j i = 0 := by
  rw [coordinateLine_iff_unit]
  constructor
  · rintro ⟨a, ha⟩ j hj
    simpa [hj] using ha j
  · intro h
    have ha : IsUnit (m.val i i) := by
      apply isUnit_iff_exists_inv'.mpr
      refine ⟨m.inv i i, ?_⟩
      have hi := congrArg (fun z : Matrix ι ι R ↦ z i i) m.inv_val
      change ∑ j, m.inv i j * m.val j i = (1 : Matrix ι ι R) i i at hi
      rwa [Finset.sum_eq_single i (fun j _ hj ↦ by rw [h j hj, mul_zero])
        (by simp), Matrix.one_apply_eq] at hi
    obtain ⟨a, ha⟩ := ha
    refine ⟨a, fun j ↦ ?_⟩
    by_cases hj : j = i
    · simpa [hj] using ha.symm
    · simpa [hj] using h j hj

private theorem exteriorGL_line_iff {R : Type u} [CommRing R] {p q : ℕ}
    (m : Matrix.GeneralLinearGroup (BlockIndex.{u} p q) R) :
    Specs.StabilizesCoordinateLine (exteriorGL p m) (initialSubset p q) ↔
      ∀ (i : Fin p) (j : Fin q), m.val (rightIndex j) (leftIndex i) = 0 := by
  classical
  let b := Pi.basisFun R (BlockIndex.{u} p q)
  let e := b.exteriorPower p
  let s := initialSubset p q
  let F := Matrix.toLin' m.val
  constructor
  · intro h i j
    obtain ⟨a, ha⟩ := (coordinateLine_iff_unit _ _).mp h
    have hmap : exteriorPower.map p F (e s) = (a : R) • e s := by
      apply e.repr.injective
      ext t
      change e.repr (exteriorPower.map p F (e s)) t = e.repr ((a : R) • e s) t
      rw [← LinearMap.toMatrix_apply, ← exteriorMatrix_toMatrix]
      change (exteriorGL p m).val t s = _
      rw [ha t, map_smul, e.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
      by_cases ht : t = s <;> simp [← show s = initialSubset p q from rfl, ht, eq_comm]
    have hzero : ExteriorAlgebra.ι R (b (leftIndex i)) * (e s).1 = 0 := by
      apply (wedge_annihilator (b (leftIndex i))).mpr
      intro l
      rw [Pi.basisFun_apply, Pi.single_eq_of_ne]
      exact rightIndex_ne_leftIndex l i
    have hz := congrArg (ExteriorAlgebra.map F) hzero
    have hf : ExteriorAlgebra.map F (e s).1 = (a : R) • (e s).1 := by
      simpa only [exteriorPower.coe_map, Submodule.coe_smul] using
        congrArg (fun v : ⋀[R]^p (BlockIndex.{u} p q → R) ↦ v.1) hmap
    rw [map_mul, ExteriorAlgebra.map_apply_ι, hf, mul_smul_comm, map_zero] at hz
    have hz' : ExteriorAlgebra.ι R (F (b (leftIndex i))) * (e s).1 = 0 := by
      have h := congrArg (fun v : ExteriorAlgebra R (BlockIndex.{u} p q → R) ↦ (↑a⁻¹ : R) • v) hz
      simpa only [smul_smul, Units.inv_mul, one_smul, smul_zero] using h
    have h := (wedge_annihilator _).mp hz' j
    simpa [F, b, Pi.basisFun_apply, Matrix.toLin'_apply', Matrix.mulVec_single_one] using h
  · intro h
    apply (coordinateLine_iff _ _).mpr
    intro t ht
    obtain ⟨x, hxt, hxs⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t s).mp ht
    obtain ⟨i, rfl⟩ := blockIndexEquiv.surjective x
    rcases i with i | j
    · exfalso
      apply hxs
      apply (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp
      exact ⟨i, by simp [s]⟩
    · obtain ⟨l, hl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t _).mpr hxt
      change exteriorMatrix p m.val t s = 0
      apply Matrix.det_eq_zero_of_row_eq_zero l
      intro i
      change m.val (Set.powersetCard.ofFinEmbEquiv.symm t l)
        (Set.powersetCard.ofFinEmbEquiv.symm s i) = 0
      rw [hl]
      change m.val (rightIndex j) (Set.powersetCard.ofFinEmbEquiv.symm (initialSubset p q) i) = 0
      rw [initialSubset_embedding]
      exact h i j

/-- A linear functional vanishing on a kernel extends to the codomain. -/
private theorem exists_factor_linear {k V B : Type u} [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup B] [Module k B]
    (f : V →ₗ[k] B) (a : V →ₗ[k] k) (h : LinearMap.ker f ≤ LinearMap.ker a) :
    ∃ c : B →ₗ[k] k, ∀ x, c (f x) = a x := by
  let a' := ((LinearMap.ker f).liftQ a h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨c, hc⟩ := a'.exists_extend
  refine ⟨c, fun x ↦ ?_⟩
  have hx := LinearMap.congr_fun hc (⟨f x, LinearMap.mem_range_self f x⟩ : LinearMap.range f)
  simpa [a'] using hx

open RationalRepresentations in
private theorem regular_block_matrix {k : Type u} [Field k] (A : HopfAlgebraCategory k)
    [Algebra.FiniteType k A] (I : Ideal A) [I.IsHopfIdeal k] :
    ∃ (p q : ℕ) (M : Matrix (BlockIndex.{u} p q) (BlockIndex.{u} p q) A), IsCoactionMatrix A M ∧
      ∀ (R : TestAlgebra k) (g : A →ₐ[k] R),
        (∀ (i : Fin p) (j : Fin q), g (M (rightIndex j) (leftIndex i)) = 0) ↔
          ∀ x ∈ I, g x = 0 := by
  classical
  -- In degree zero the exterior representation of the zero space is the trivial line.
  by_cases hI : I = ⊥
  · refine ⟨0, 0, 1, ⟨fun i _ ↦ Fin.elim0 i.down, fun i _ ↦ Fin.elim0 i.down⟩, ?_⟩
    intro R g
    constructor
    · intro _ x hx
      rw [hI] at hx
      rw [show x = 0 from hx, map_zero]
    · intro _ i
      exact Fin.elim0 i
  let := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨s, hs, hsI⟩ := Submodule.fg_def.mp (IsNoetherian.noetherian I)
  let reg := RightComodule.regular (k := k) (C := A)
  obtain ⟨V₀, hV₀⟩ := RightComodule.exists_finiteSubcomodule_containing reg
    (insert 1 s) (hs.insert 1)
  let V := V₀.val
  let : FiniteDimensional k V := V₀.property.2
  obtain ⟨ρ, hρ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction reg V).mp V₀.property.1
  let W := (I.restrictScalars k).comap V.subtype
  obtain ⟨U, hU⟩ := W.exists_isCompl
  let p := Module.finrank k W
  let q := Module.finrank k U
  let : Module.Free k W := Module.Free.of_divisionRing k W
  let : Module.Free k U := Module.Free.of_divisionRing k U
  let bW := Module.finBasis k W
  let bU := Module.finBasis k U
  let β : Fin p ⊕ Fin q ≃ BlockIndex.{u} p q := blockIndexEquiv
  let b₀ := (bW.prod bU).map (W.prodEquivOfIsCompl U hU)
  let b := b₀.reindex β
  let M := coefficients A b ρ
  have hb (i : Fin p) : b (leftIndex i) = (bW i : V) := by
    calc
      b (leftIndex i) = b (β (.inl i)) := rfl
      _ = b₀ (.inl i) := by
        change b₀.reindex β (β (.inl i)) = _
        rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
      _ = (bW i : V) := by simp [b₀]
  have hW : Submodule.span k (Set.range (fun i : Fin p ↦ b (leftIndex i))) = W := by
    simp_rw [hb]
    change Submodule.span k (Set.range (W.subtype ∘ bW)) = W
    rw [Set.range_comp W.subtype bW, ← Submodule.map_span, bW.span_eq, Submodule.map_subtype_top]
  have hcoord (j : Fin q) : W ≤ LinearMap.ker (b.coord (rightIndex j)) := by
    rw [← hW, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change b (leftIndex i) ∈ LinearMap.ker (b.coord (rightIndex j))
    rw [LinearMap.mem_ker, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne]
    exact rightIndex_ne_leftIndex j i
  have hΔ (i : BlockIndex.{u} p q) :
      comul (R := k) (b i : A) = ∑ t, (b t : A) ⊗ₜ[k] M t i := by
    have he := (LinearMap.congr_fun hρ (b i)).symm
    change comul (R := k) (b i : A) = V.subtype.rTensor A (ρ.coaction (b i)) at he
    rw [he, coaction_apply_basis A b, map_sum]
    rfl
  have hbI (i : Fin p) : (b (leftIndex i) : A) ∈ I := by
    rw [hb]
    exact (bW i).property
  refine ⟨p, q, M, coefficients_isCoactionMatrix A b ρ, fun R g ↦ ?_⟩
  constructor
  · intro hz
    have hε := ((textbookHopfIdeal k A I).mp inferInstance).2.1
    have hb0 (i : Fin p) : g (b (leftIndex i) : A) = 0 := by
      let F : A ⊗[k] A →ₗ[k] A :=
        (TensorProduct.lid k A).toLinearMap.comp ((counit (R := k) (A := A)).rTensor A)
      have h := congrArg F (hΔ (leftIndex i))
      have hF (x : A) : F (comul (R := k) x) = x := by
        change TensorProduct.lid k A (((counit (R := k) (A := A)).rTensor A) (comul x)) = x
        rw [Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]
      rw [hF, map_sum] at h
      have hg := congrArg g h
      rw [map_sum] at hg
      refine hg.trans (Finset.sum_eq_zero fun t _ ↦ ?_)
      change g (counit (R := k) (b t : A) • M t (leftIndex i)) = 0
      obtain ⟨l, rfl⟩ := blockIndexEquiv.surjective t
      rcases l with l | j
      · rw [blockIndexEquiv_inl, hε _ (hbI l), zero_smul, map_zero]
      · rw [blockIndexEquiv_inr, map_smul, hz i j, smul_zero]
    have hkill : W ≤ LinearMap.ker (g.toLinearMap.comp V.subtype) := by
      rw [← hW, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hb0 i
    have hker : I ≤ RingHom.ker g.toRingHom := by
      rw [← show Ideal.span s = I from hsI, Ideal.span_le]
      intro x hx
      have hxV : x ∈ V := hV₀ (Set.mem_insert_of_mem _ hx)
      have hxI : x ∈ I := hsI ▸ Ideal.subset_span hx
      exact hkill (show (⟨x, hxV⟩ : V) ∈ W from hxI)
    exact fun x hx ↦ hker hx
  · intro hz i j
    let B := hopfQuotient A I
    let a := (hopfQuotientMap A I).hom
    let aₗ : A →ₗ[k] B := a.toAlgHom.toLinearMap
    have hker : LinearMap.ker (aₗ.comp V.subtype) ≤ LinearMap.ker (b.coord (rightIndex j)) := by
      intro x hx
      apply hcoord j
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx
    obtain ⟨ℓ, hℓ⟩ := exists_factor_linear (aₗ.comp V.subtype) (b.coord (rightIndex j)) hker
    let g' := Ideal.Quotient.liftₐ I g hz
    let E : B ⊗[k] B →ₗ[k] R :=
      (TensorProduct.lid k R).toLinearMap.comp (TensorProduct.map ℓ g'.toLinearMap)
    have hd : TensorProduct.map aₗ aₗ (comul (R := k) (b (leftIndex i) : A)) = 0 := by
      have h := CoalgHomClass.map_comp_comul_apply a (b (leftIndex i) : A)
      change TensorProduct.map aₗ aₗ (comul (R := k) (b (leftIndex i) : A)) =
        comul (R := k) (a (b (leftIndex i) : A)) at h
      rw [h, show a (b (leftIndex i) : A) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (hbI i),
        map_zero]
    have he := congrArg E hd
    rw [hΔ, map_sum, map_sum, map_zero] at he
    have hterm (t : BlockIndex.{u} p q) :
        E (TensorProduct.map aₗ aₗ ((b t : A) ⊗ₜ[k] M t (leftIndex i))) =
          b.coord (rightIndex j) (b t) • g (M t (leftIndex i)) := by
      simp only [E, LinearMap.comp_apply, TensorProduct.map_tmul]
      rw [show ℓ (aₗ (b t : A)) = b.coord (rightIndex j) (b t) from hℓ (b t)]
      rfl
    simp_rw [hterm, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at he
    simpa [ite_smul, eq_comm] using he

/-- A quotient point factors through the closed subgroup precisely when it kills
the defining ideal. The comparison is natural on every commutative test algebra. -/
private theorem quotient_point_iff {k : Type u} [Field k] {A : HopfAlgebraCategory k}
    {G H : Specs.GroupScheme k} (i : H ⟶ G) (I : Ideal A) [I.IsHopfIdeal k]
    (e : specGroup A ≅ G) (h : H ≅ specGroup (hopfQuotient A I))
    (hi : h.hom ≫ specGroupMap (hopfQuotientMap A I) = i ≫ e.inv)
    (E : ∀ B : HopfAlgebraCategory k, convolutionPoints B ≅ (groupPointsFunctor k).obj (specGroup B))
    (hE : ∀ {B C : HopfAlgebraCategory k} (a : B ⟶ C) (R : TestAlgebra k)
      (f : WithConv (C →ₐ[k] R)),
      (E B).hom.app R (toConv (f.ofConv.comp a.hom.toAlgHom)) =
        ((groupPointsFunctor k).map (specGroupMap a)).app R ((E C).hom.app R f))
    (R : TestAlgebra k) (g : A →ₐ[k] R) :
    (∀ x ∈ I, g x = 0) ↔
      ∃ hR : Points H.X R, hR ≫ i.hom.hom =
        (E A).hom.app R (toConv g) ≫ e.hom.hom.hom := by
  let Q := hopfQuotient A I
  let q := hopfQuotientMap A I
  change h.hom ≫ specGroupMap q = i ≫ e.inv at hi
  have hi' : h.inv ≫ i = specGroupMap q ≫ e.hom := by
    calc
      h.inv ≫ i = h.inv ≫ (i ≫ e.inv) ≫ e.hom := by simp
      _ = specGroupMap q ≫ e.hom := by rw [← hi]; simp
  have hiR : ∀ f : WithConv (Q →ₐ[k] R),
      ((E Q).hom.app R f : Points (specGroup Q).X R) ≫ h.inv.hom.hom ≫ i.hom.hom =
        ((E A).hom.app R (toConv (f.ofConv.comp q.hom.toAlgHom)) : Points (specGroup A).X R) ≫
          e.hom.hom.hom := by
    intro f
    have hi'' := congrArg (fun z : specGroup Q ⟶ G ↦ z.hom.hom) hi'
    change h.inv.hom.hom ≫ i.hom.hom =
      (specGroupMap q).hom.hom ≫ e.hom.hom.hom at hi''
    rw [hi'', ← Category.assoc, hE]
    rfl
  have hA := (ConcreteCategory.bijective_of_isIso ((E A).hom.app R)).1
  have hQ := (ConcreteCategory.bijective_of_isIso ((E Q).hom.app R)).2
  constructor
  · intro hg
    let f := Ideal.Quotient.liftₐ I g hg
    have hf : f.comp q.hom.toAlgHom = g := Ideal.Quotient.liftₐ_comp I g hg
    exact ⟨(E Q).hom.app R (toConv f) ≫ h.inv.hom.hom, by
      rw [Category.assoc, hiR]
      change ((E A).hom.app R (toConv (f.comp q.hom.toAlgHom)) : Points (specGroup A).X R) ≫
        e.hom.hom.hom = _
      rw [hf]⟩
  · rintro ⟨hR, hg⟩
    obtain ⟨f, hf⟩ := hQ (hR ≫ h.hom.hom.hom)
    have hh := hiR f
    change ((E Q).hom.app R f : Points (specGroup Q).X R) = _ at hf
    rw [hf, Category.assoc, ← Category.assoc h.hom.hom.hom h.inv.hom.hom] at hh
    have hinv : h.hom.hom.hom ≫ h.inv.hom.hom = 𝟙 _ :=
      ((Grp.forget (SchemeOver k)).mapIso h).hom_inv_id
    rw [hinv, Category.id_comp, hg] at hh
    have : IsIso e.hom.hom.hom := ((Grp.forget (SchemeOver k)).mapIso e).isIso_hom
    have hfg : f.ofConv.comp q.hom.toAlgHom = g :=
      congrArg WithConv.ofConv (hA ((cancel_mono e.hom.hom.hom).mp hh.symm))
    intro x hx
    rw [← hfg]
    change f.ofConv ((Ideal.Quotient.mk I) x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- Every closed subgroup scheme of a finite-type affine group is the stabilizer
of a line in a finite-dimensional rational representation. -/
theorem chevalleyLine : Specs.ChevalleyLine.{u} := by
  classical
  intro k _ G H
  obtain ⟨A, ⟨e⟩⟩ := essImage_hopfSpec.mpr G.property.1
  let eG : specGroup A.unop ≅ G.val := e
  have : IsIso eG.hom.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map eG.hom)
    infer_instance
  have hG : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  have hAG := locallyOfFiniteType_comp eG.hom.hom.hom.left G.val.X.hom
  rw [Over.w eG.hom.hom.hom] at hAG
  let : Algebra.FiniteType k A.unop := (hopfSpec_locallyOfFiniteType_iff k A.unop).mp hAG
  let i := H.inclusion ≫ eG.inv
  have hi : IsClosedImmersion i.hom.hom.left := by
    have := H.isClosedImmersion
    have : IsIso eG.inv.hom.hom.left := by
      change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map eG.inv)
      infer_instance
    change IsClosedImmersion (H.inclusion.hom.hom.left ≫ eG.inv.hom.hom.left)
    infer_instance
  obtain ⟨I, ⟨hI, eH, heH⟩, _⟩ :=
    (closedSubgroupClassification k A.unop H.group i).mp hi
  let : I.IsHopfIdeal k := hI
  obtain ⟨p, q, M, hM, hblock⟩ := regular_block_matrix A.unop I
  let N := exteriorMatrix p M
  let hN := exteriorIsCoactionMatrix A.unop p M hM
  let ι := Set.powersetCard (BlockIndex.{u} p q) p
  let L := StandardGroups.generalLinearGroup k ι
  let l := StandardGroups.generalLinearGroupPointsIso (k := k) (ι := ι)
  obtain ⟨E, _, hE⟩ := hopfSpecPoints k
  let eA := E A.unop ≪≫ (groupPointsFunctor k).mapIso eG
  let α := eA.inv ≫ RationalRepresentations.matrixPointHom A.unop N hN
  let F := groupHomEquiv G.val L.val G.property.1
  let f := F.symm (α ≫ l.inv)
  have hf : (groupPointsFunctor k).map f ≫ l.hom = α := by
    have h := F.apply_symm_apply (α ≫ l.inv)
    change (groupPointsFunctor k).map f = α ≫ l.inv at h
    rw [h, Category.assoc, l.inv_hom_id, Category.comp_id]
  refine ⟨ι, inferInstance, inferInstance, initialSubset p q, L, l, f, fun R g ↦ ?_⟩
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (eA.hom.app R)).2 g
  have hre : l.hom.app R (((groupPointsFunctor k).map f).app R (eA.hom.app R a)) =
      (RationalRepresentations.matrixPointHom A.unop N hN).app R a := by
    have h := congrArg (fun z ↦ z.app R (eA.hom.app R a)) hf
    change _ = (RationalRepresentations.matrixPointHom A.unop N hN).app R
      (eA.inv.app R (eA.hom.app R a)) at h
    simpa using h
  rw [hre]
  have hExt : (RationalRepresentations.matrixPointHom A.unop N hN).app R a =
      exteriorGL p ((RationalRepresentations.matrixPointHom A.unop M hM).app R a) := by
    apply Units.ext
    change N.map a.ofConv.toRingHom = exteriorMatrix p (M.map a.ofConv.toRingHom)
    exact (exteriorMatrix_map p M a.ofConv.toRingHom).symm
  rw [hExt, exteriorGL_line_iff]
  change (∀ (i : Fin p) (j : Fin q), a.ofConv (M (rightIndex j) (leftIndex i)) = 0) ↔ _
  rw [hblock R a.ofConv]
  exact quotient_point_iff H.inclusion I eG eH heH E hE R a.ofConv

end

end LinearAlgebraicGroups
