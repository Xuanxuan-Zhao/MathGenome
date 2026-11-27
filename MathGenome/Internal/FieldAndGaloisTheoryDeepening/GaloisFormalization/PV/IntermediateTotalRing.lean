import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FiniteTypeConstants
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.TransitiveProductProjectionKernels
import Mathlib.GroupTheory.Perm.Cycle.Basic
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.IntermediateTotalRing

namespace GaloisFormalization.PV

open scoped BigOperators nonZeroDivisors
open Matrix.GeneralLinearGroup

universe u v w

/-- An operator-stable intermediate algebra in which all regular elements are units. -/
def IsIntermediateTotalRing {kind : OperatorKind} {k : Type u} {Q : Type v}
    [Field k] [CommRing Q] [Algebra k Q] (T : Operator kind Q) (F : Subalgebra k Q) : Prop :=
  T.IsStable (F : Set Q) ∧ ProjectionKernels.RegularElementsAreUnits (F : Type v)

/-- The algebra generated over the intermediate ring by the given solution matrix
and the inverse of its determinant, inside the total extension. -/
def relativePicardVessiotSubalgebra {k : Type u} {Q : Type v}
    [Field k] [CommRing Q] [Algebra k Q] {n : ℕ} (F : Subalgebra k Q)
    (Y : Matrix.GeneralLinearGroup (Fin n) Q) : Subalgebra (F : Type v) Q :=
  matrixGeneratedSubalgebra (F : Type v) Y

private def restrictOperator {kind : OperatorKind} {Q : Type v} [CommRing Q]
    (T : Operator kind Q) (S : Subring Q) (hS : T.IsStable (S : Set Q)) :
    Operator kind S := by
  cases kind with
  | differential =>
    let d := T.toDerivation
    exact Operator.differential {
      toFun x := ⟨d x, hS x.property⟩
      map_add' x y := Subtype.ext (d.map_add x y)
      map_smul' z x := Subtype.ext (d.map_smul z x)
      map_one_eq_zero' := Subtype.ext d.map_one_eq_zero
      leibniz' x y := Subtype.ext (d.leibniz x y) }
  | difference =>
    let σ := T.toRingEquiv
    exact Operator.difference {
      toFun x := ⟨σ x, hS.1 x.property⟩
      invFun x := ⟨σ.symm x, hS.2 x.property⟩
      left_inv x := Subtype.ext (σ.symm_apply_apply x)
      right_inv x := Subtype.ext (σ.apply_symm_apply x)
      map_mul' x y := Subtype.ext (map_mul σ (x : Q) (y : Q))
      map_add' x y := Subtype.ext (map_add σ (x : Q) (y : Q)) }

private theorem restrictOperator_commutes {kind : OperatorKind} {Q : Type v} [CommRing Q]
    (T : Operator kind Q) (S : Subring Q) (hS : T.IsStable (S : Set Q)) :
    (restrictOperator T S hS).Commutes T S.subtype := by
  cases kind <;> intro x <;> rfl

private theorem commutes_of_comp_injective {kind : OperatorKind}
    {R : Type u} {S : Type v} {Q : Type w} [CommRing R] [CommRing S] [CommRing Q]
    {E : Operator kind R} {D : Operator kind S} {T : Operator kind Q}
    {f : R → S} {g : S → Q} (hg : Function.Injective g)
    (h : E.Commutes T (g ∘ f)) (hgT : D.Commutes T g) : E.Commutes D f := by
  intro x
  apply hg
  exact (h x).trans (hgT (f x)).symm

private theorem fractionRing_of_intermediate {R : Type u} {Q : Type v}
    [CommRing R] [CommRing Q] [Algebra R Q] [IsFractionRing R Q]
    (S : Subring Q) (i : R →+* S) (hi : ∀ r, (i r : Q) = algebraMap R Q r) :
    (∀ x : S, x ∈ (S : Type v)⁰ ↔ IsUnit (x : Q)) ∧
    (∀ r : R, r ∈ R⁰ → i r ∈ (S : Type v)⁰) ∧
    IsFractionRing (S : Type v) Q := by
  have hreg (x : S) : x ∈ (S : Type v)⁰ ↔ IsUnit (x : Q) := by
    constructor
    · intro hx
      change (x : Q) ∈ IsUnit.submonoid Q
      rw [← IsFractionRing.nonZeroDivisors_eq_isUnit R Q]
      apply mem_nonZeroDivisors_iff_left.mpr
      intro y hxy
      obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj R⁰ y
      have hz : x * i r = 0 := by
        apply Subtype.val_injective
        change (x : Q) * (i r : Q) = 0
        rw [hi, ← hrs, ← mul_assoc, hxy, zero_mul]
      have hr : i r = 0 := mem_nonZeroDivisors_iff_left.mp hx _ hz
      apply (IsLocalization.map_units Q s).mul_right_cancel
      rw [zero_mul, hrs, ← hi, hr]
      rfl
    · intro hx
      exact mem_nonZeroDivisors_of_injective S.subtype_injective hx.mem_nonZeroDivisors
  have hden (r : R) (hr : r ∈ R⁰) : i r ∈ (S : Type v)⁰ :=
    (hreg (i r)).mpr (hi r ▸ IsLocalization.map_units Q ⟨r, hr⟩)
  refine ⟨hreg, hden, ?_⟩
  refine ⟨fun s => (hreg s.val).mp s.property, ?_, ?_⟩
  · intro q
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj R⁰ q
    exact ⟨⟨i r, ⟨i s, hden s s.property⟩⟩, by
      change q * (i (s : R) : Q) = (i r : Q)
      rwa [hi, hi]⟩
  · intro x y h
    exact ⟨1, by simpa using S.subtype_injective h⟩

private theorem derivation_matrix_mul {R : Type v} [CommRing R] {n : ℕ}
    (d : Derivation ℤ R R) (X Y : Matrix (Fin n) (Fin n) R) :
    (X * Y).map d = X * Y.map d + X.map d * Y := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, d.leibniz,
    smul_eq_mul, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

private theorem ratio_entries_constant {kind : OperatorKind} {k : Type u} {R : Type v}
    [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    {A : LinearSystem kind k n} {E : Operator kind R}
    {Y W : Matrix.GeneralLinearGroup (Fin n) R}
    (hY : A.IsFundamental E Y) (hW : A.IsFundamental E W) :
    ∀ i j, E.IsConstant ((Y⁻¹ * W).val i j) := by
  let Z := Y⁻¹ * W
  have hmul : Y.val * Z.val = W.val :=
    congrArg Units.val (mul_inv_cancel_left Y W)
  change W.val.map E = A.mapCoefficients R * W.val at hW
  change Y.val.map E = A.mapCoefficients R * Y.val at hY
  rw [← hmul] at hW
  cases kind with
  | differential =>
    let d := E.toDerivation
    change Y.val.map d = A.mapCoefficients R * Y.val at hY
    change (Y.val * Z.val).map d = A.mapCoefficients R * (Y.val * Z.val) at hW
    rw [derivation_matrix_mul, hY, mul_assoc] at hW
    have hz : Y.val * Z.val.map d = 0 := add_right_cancel (hW.trans (zero_add _).symm)
    have hz' : Z.val.map d = 0 := by
      have h := congrArg ((Y⁻¹).val * ·) hz
      rwa [← mul_assoc, Y.inv_mul, one_mul, mul_zero] at h
    intro i j
    exact congrFun (congrFun hz' i) j
  | difference =>
    let σ := E.toRingEquiv
    change Y.val.map σ.toRingHom = A.mapCoefficients R * Y.val at hY
    change (Y.val * Z.val).map σ.toRingHom = A.mapCoefficients R * (Y.val * Z.val) at hW
    rw [Matrix.map_mul, hY, ← mul_assoc] at hW
    rw [← hY] at hW
    have hz : Z.val.map σ.toRingHom = Z.val := by
      have hz := congrArg (fun M => ((Matrix.GeneralLinearGroup.map σ.toRingHom Y)⁻¹).val * M) hW
      change ((Matrix.GeneralLinearGroup.map σ.toRingHom Y)⁻¹).val *
        ((Matrix.GeneralLinearGroup.map σ.toRingHom Y).val * Z.val.map σ.toRingHom) =
        ((Matrix.GeneralLinearGroup.map σ.toRingHom Y)⁻¹).val *
          ((Matrix.GeneralLinearGroup.map σ.toRingHom Y).val * Z.val) at hz
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using hz
    intro i j
    exact congrFun (congrFun hz i) j

private theorem generatedByMatrix_finiteType {k : Type u} {R : Type v}
    [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (Y : Matrix.GeneralLinearGroup (Fin n) R) :
    Algebra.FiniteType k (matrixGeneratedSubalgebra k Y) :=
  Algebra.FiniteType.adjoin_of_finite ((Set.finite_range _).insert _)

private theorem finiteType_of_generatedByMatrix {k : Type u} {R : Type v}
    [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    {Y : Matrix.GeneralLinearGroup (Fin n) R} (hY : matrixGeneratedSubalgebra k Y = ⊤) :
    Algebra.FiniteType k R := by
  have h := generatedByMatrix_finiteType (k := k) Y
  rw [hY] at h
  exact h.equiv Subalgebra.topEquiv

private theorem determinantInverse_map {R : Type u} {Q : Type v} [CommRing R] [CommRing Q]
    {n : ℕ} (f : R →+* Q) (Y : Matrix.GeneralLinearGroup (Fin n) R) :
    LinearSystem.determinantInverse (Matrix.GeneralLinearGroup.map f Y) =
      f (LinearSystem.determinantInverse Y) := by
  change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f Y))⁻¹ : Qˣ).val =
    f ((Matrix.GeneralLinearGroup.det Y)⁻¹ : Rˣ).val
  rw [Matrix.GeneralLinearGroup.map_det, ← _root_.map_inv]
  rfl

private theorem determinantInverse_mul {R : Type v} [CommRing R] {n : ℕ}
    (Y Z : Matrix.GeneralLinearGroup (Fin n) R) :
    LinearSystem.determinantInverse (Y * Z) =
      LinearSystem.determinantInverse Y * LinearSystem.determinantInverse Z := by
  change ((Matrix.GeneralLinearGroup.det (Y * Z))⁻¹ : Rˣ).val = _
  rw [_root_.map_mul, mul_inv_rev, Units.val_mul, mul_comm]
  rfl

private theorem matrixGeneratedSubalgebra_eq_top {kind : OperatorKind} {k : Type u} {R : Type v}
    [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    {D : OperatorField kind k} {A : LinearSystem kind k n} {E : Operator kind R}
    (hk : D.IsBaseField) (hR : IsPicardVessiotRing D A E)
    {Y : Matrix.GeneralLinearGroup (Fin n) R} (hY : A.IsFundamental E Y) :
    matrixGeneratedSubalgebra k Y = ⊤ := by
  obtain ⟨hDE, hE, W, hW, hgen⟩ := hR
  let := finiteType_of_generatedByMatrix hgen
  have hconstants := (Operator.constants_finiteType D E hk hE hDE.1).2
  let S := matrixGeneratedSubalgebra k Y
  have const_mem {r : R} (hr : E.IsConstant r) : r ∈ S := by
    obtain ⟨c, hc⟩ := hconstants ⟨r, (Operator.mem_constantSubring E r).mpr hr⟩
    have heq : algebraMap k R (c : k) = r := congrArg Subtype.val hc
    rw [← heq]
    exact S.algebraMap_mem c
  let Z := Y⁻¹ * W
  have hYZ : Y * Z = W := mul_inv_cancel_left Y W
  have y_mem (i j) : Y.val i j ∈ S := Algebra.subset_adjoin (Or.inr ⟨(i, j), rfl⟩)
  have detY_mem : LinearSystem.determinantInverse Y ∈ S :=
    Algebra.subset_adjoin (Or.inl rfl)
  have z_mem (i j) : Z.val i j ∈ S := const_mem (ratio_entries_constant hY hW i j)
  have zinv_mem (i j) : (Z⁻¹).val i j ∈ S := by
    change ((Y⁻¹ * W)⁻¹).val i j ∈ S
    rw [mul_inv_rev, inv_inv]
    exact const_mem (ratio_entries_constant hW hY i j)
  have detZ_mem : LinearSystem.determinantInverse Z ∈ S := by
    let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨(Z⁻¹).val i j, zinv_mem i j⟩
    have hmap : (algebraMap S R).mapMatrix M = (Z⁻¹).val := rfl
    have hdet := (algebraMap S R).map_det M
    rw [hmap] at hdet
    change (Z⁻¹).val.det ∈ S
    rw [← hdet]
    exact (Matrix.det M).property
  apply top_unique
  rw [← hgen, matrixGeneratedSubalgebra, Algebra.adjoin_le_iff]
  rintro _ (h | ⟨⟨i, j⟩, rfl⟩)
  · rw [Set.mem_singleton_iff.mp h, ← hYZ, determinantInverse_mul]
    exact S.mul_mem detY_mem detZ_mem
  · rw [← hYZ]
    change (Y.val * Z.val) i j ∈ S
    rw [Matrix.mul_apply]
    exact S.sum_mem (fun l _ => S.mul_mem (y_mem i l) (z_mem l j))

private theorem generatedByMatrix_eq_adjoin_image {k : Type u} {R Q : Type v}
    [Field k] [CommRing R] [CommRing Q] [Algebra k R] [Algebra k Q] [Algebra R Q]
    [IsScalarTower k R Q] {n : ℕ} (F : Subalgebra k Q)
    (Y : Matrix.GeneralLinearGroup (Fin n) R) (hY : matrixGeneratedSubalgebra k Y = ⊤) :
    relativePicardVessiotSubalgebra F (Matrix.GeneralLinearGroup.map (algebraMap R Q) Y) =
      Algebra.adjoin (F : Type v) (Set.range (algebraMap R Q)) := by
  let B := relativePicardVessiotSubalgebra F (Matrix.GeneralLinearGroup.map (algebraMap R Q) Y)
  have hR (r : R) : algebraMap R Q r ∈ B := by
    let S := (B.restrictScalars k).comap (IsScalarTower.toAlgHom k R Q)
    have hle : matrixGeneratedSubalgebra k Y ≤ S := by
      rw [matrixGeneratedSubalgebra, Algebra.adjoin_le_iff]
      rintro _ (h | ⟨⟨i, j⟩, rfl⟩)
      · rw [Set.mem_singleton_iff.mp h]
        change algebraMap R Q (LinearSystem.determinantInverse Y) ∈ B
        rw [← determinantInverse_map]
        exact Algebra.subset_adjoin (Or.inl rfl)
      · exact Algebra.subset_adjoin (Or.inr ⟨(i, j), rfl⟩)
    rw [hY] at hle
    exact hle (show r ∈ (⊤ : Subalgebra k R) from trivial)
  apply le_antisymm
  · change Algebra.adjoin _ _ ≤ _
    apply Algebra.adjoin_le_iff.mpr
    rintro _ (h | ⟨⟨i, j⟩, rfl⟩)
    · rw [Set.mem_singleton_iff.mp h, determinantInverse_map]
      exact Algebra.subset_adjoin ⟨_, rfl⟩
    · exact Algebra.subset_adjoin ⟨Y.val i j, rfl⟩
  · exact Algebra.adjoin_le_iff.mpr (by rintro _ ⟨r, rfl⟩; exact hR r)

private theorem stable_adjoin {k : Type u} {Q : Type v} [CommRing k] [CommRing Q]
    [Algebra k Q] {kind : OperatorKind} {T : Operator kind Q} {s : Set Q}
    (hs : T.IsStable s) (hk : T.IsStable (Set.range (algebraMap k Q))) :
    T.IsStable (Algebra.adjoin k s : Set Q) := by
  cases kind with
  | differential =>
    let B := Algebra.adjoin k s
    let d := T.toDerivation
    change ∀ ⦃x⦄, x ∈ B → d x ∈ B
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (hs hx)
    | algebraMap r =>
      obtain ⟨r', hr'⟩ := hk (Set.mem_range_self r)
      exact hr' ▸ B.algebraMap_mem r'
    | add x y _ _ hx hy => exact d.map_add x y ▸ B.add_mem hx hy
    | mul x y hx hy hdx hdy =>
      rw [d.leibniz, smul_eq_mul, smul_eq_mul]
      exact B.add_mem (B.mul_mem hx hdy) (B.mul_mem hy hdx)
  | difference =>
    let B := Algebra.adjoin k s
    have stable (σ : Q →+* Q) (h₁ : Set.MapsTo σ s s)
        (h₂ : Set.MapsTo σ (Set.range (algebraMap k Q)) (Set.range (algebraMap k Q))) :
        ∀ ⦃x⦄, x ∈ B → σ x ∈ B := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx => exact Algebra.subset_adjoin (h₁ hx)
      | algebraMap r =>
        obtain ⟨r', hr'⟩ := h₂ (Set.mem_range_self r)
        exact hr' ▸ B.algebraMap_mem r'
      | add x y _ _ hx hy => exact σ.map_add x y ▸ B.add_mem hx hy
      | mul x y _ _ hx hy => exact σ.map_mul x y ▸ B.mul_mem hx hy
    exact ⟨stable T.toRingEquiv.toRingHom hs.1 hk.1,
      stable T.toRingEquiv.symm.toRingHom hs.2 hk.2⟩

private theorem intermediateDifferenceComponents {Q : Type v} [CommRing Q]
    {ι : Type v} {L : ι → Type v} [∀ j, Field (L j)] [Finite ι] [Nonempty ι]
    (τ : Q ≃+* Q) (e : Q ≃+* (∀ j, L j)) (p : Equiv.Perm ι)
    (hp : ProjectionKernels.Transitive p)
    (hτ : ∀ x j, e (τ x) (p j) = 0 ↔ e x j = 0)
    (S : Subring Q) (hS : (Operator.difference τ).IsStable (S : Set Q))
    (hu : ProjectionKernels.RegularElementsAreUnits (S : Type v)) :
    Specs.intermediateFieldStructure (kind := .difference) (restrictOperator (Operator.difference τ) S hS) := by
  let σ := e.symm.trans (τ.trans e)
  let S' : Subring (∀ j, L j) := S.map e.toRingHom
  have hS' : (Operator.difference σ).IsStable (S' : Set (∀ j, L j)) := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨τ x, hS.1 hx, ?_⟩
      change e (τ x) = e (τ (e.symm (e x)))
      rw [e.symm_apply_apply]
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨τ.symm x, hS.2 hx, ?_⟩
      change e (τ.symm x) = e (τ.symm (e.symm (e x)))
      rw [e.symm_apply_apply]
  let S'' : Operator.Subring (Operator.difference σ) := ⟨S', hS'⟩
  let j : S ≃+* S' := S.equivMapOfInjective e.toRingHom e.injective
  have hσ : ProjectionKernels.PermutesFactors σ p := by
    intro x a
    change e (τ (e.symm x)) (p a) = 0 ↔ x a = 0
    rw [hτ, e.apply_symm_apply]
  have hsu : ProjectionKernels.RegularElementsAreUnits (S' : Type v) := by
    intro y hy
    have hz : j.symm y ∈ (S : Type v)⁰ :=
      mem_nonZeroDivisors_of_injective (f := j.toRingHom) j.injective
        (by change j (j.symm y) ∈ (S' : Type v)⁰; rwa [j.apply_symm_apply])
    have hy' : IsUnit (j (j.symm y)) := (hu _ hz).map j.toRingHom
    rwa [j.apply_symm_apply] at hy'
  obtain ⟨q, g, f, hq, _, hf, _, hg⟩ :=
    ProjectionKernels.decomposition σ p hσ hp S'' hsu
  let J := ProjectionKernels.Index S'
  let fields (a : J) : Field (S' ⧸ a.val) := (hf a).toField
  have hJ : Nonempty J := Nonempty.map (ProjectionKernels.ofCoordinate S') inferInstance
  have hj (x : S) :
      j ((restrictOperator (Operator.difference τ) S hS).toRingEquiv x) =
        ProjectionKernels.restrict σ S'' (j x) := by
    apply Subtype.ext
    change e (τ x) = e (τ (e.symm (e x)))
    rw [e.symm_apply_apply]
  refine ⟨J, (fun a => S' ⧸ a.val), fields, inferInstance, hJ, j.trans g, q, f, hq, ?_⟩
  intro x a
  change g (j ((restrictOperator (Operator.difference τ) S hS).toRingEquiv x)) (q a) =
    f a (g (j x) a)
  rw [hj]
  exact hg (j x) a

private theorem isNoetherianRing_of_permutedFieldComponents {S : Type v} [CommRing S]
    {τ : S ≃+* S} (h : Specs.intermediateFieldStructure (Specs.difference τ)) : IsNoetherianRing S := by
  obtain ⟨ι, L, hL, hfinite, _, e, _, _, _, _⟩ := h
  let := hL
  let := hfinite
  exact isNoetherianRing_of_ringEquiv (∀ j, L j) e.symm

set_option linter.checkUnivs false in
private theorem intermediateSubring_structure {kind : OperatorKind} {k : Type u} {R Q : Type v}
    [Field k] [CharZero k] [CommRing R] [Algebra k R] [IsNoetherianRing R]
    [CommRing Q] [Algebra R Q] [IsFractionRing R Q] {E : Operator kind R} {T : Operator kind Q}
    (hE : E.IsSimple) (hT : E.Commutes T (algebraMap R Q))
    (S : Subring Q) (hS : T.IsStable (S : Set Q))
    (hu : ProjectionKernels.RegularElementsAreUnits (S : Type v)) :
    IsNoetherianRing S ∧ Specs.intermediateFieldStructure (kind := kind) (restrictOperator T S hS) := by
  cases kind with
  | differential =>
    let : Algebra ℚ R := ((algebraMap k R).comp (algebraMap ℚ k)).toAlgebra
    have hQ := (Operator.simpleDifferentialFractionField (K := Q) E hE).2
    let : Field Q := hQ.toField
    have hF := ProjectionKernels.subring_isField_of_regular_isUnit S hu
    let : Field S := hF.toField
    exact ⟨inferInstance, hF⟩
  | difference =>
    obtain ⟨hfin, hne, _, hQ, _, p, f, e, _, ht, _, _, _, he⟩ :=
      simpleDifferenceFractionComponents E.toRingEquiv T.toRingEquiv hE hT
    let := hfin
    let := hne
    let : ∀ i : minimalPrimes R, Field (FractionRing (R ⧸ i.val)) := fun i => (hQ i).toField
    have hp : ProjectionKernels.Transitive p := by
      intro i j
      obtain ⟨m, hm⟩ := (show Equiv.Perm.SameCycle p i j from ht i j).exists_nat_pow_eq
      exact ⟨m, by rwa [p.iterate_eq_pow]⟩
    have h := intermediateDifferenceComponents T.toRingEquiv e p hp
      (fun x j => by rw [he]; exact map_eq_zero_iff _ (Operator.fractionRingEquiv (f j)).injective)
      S hS hu
    exact ⟨isNoetherianRing_of_permutedFieldComponents h, h⟩

private theorem stable_range_of_commutes {kind : OperatorKind} {R : Type u} {Q : Type v}
    [CommRing R] [CommRing Q] {E : Operator kind R} {T : Operator kind Q}
    {f : R →+* Q} (h : E.Commutes T f) : T.IsStable (Set.range f) := by
  cases kind with
  | differential =>
    rintro _ ⟨r, rfl⟩
    exact ⟨E r, h r⟩
  | difference =>
    constructor
    · rintro _ ⟨r, rfl⟩
      exact ⟨E r, h r⟩
    · rintro _ ⟨r, rfl⟩
      exact ⟨E.toRingEquiv.symm r, h.difference_symm r⟩

private theorem intermediateTotalRing_structure_aux
    {kind : OperatorKind} {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    {n : ℕ} {D : OperatorField kind k} {A : LinearSystem kind k n} {E : Operator kind R}
    {T : Operator kind (TotalQuotientRing R)} {Y : Matrix.GeneralLinearGroup (Fin n) R}
    (hk : D.IsBaseField) (hPV : IsPicardVessiotTotalExtension D A E T) (hY : A.IsFundamental E Y)
    (F : Subalgebra k (TotalQuotientRing R)) (hF : IsIntermediateTotalRing T F) :
    let Q := TotalQuotientRing R
    let B := relativePicardVessiotSubalgebra F (Matrix.GeneralLinearGroup.map (algebraMap R Q) Y)
    ∃ (D_F : Operator kind (F : Type v)) (E_B : Operator kind (B : Type v))
      (i : R →+* (B : Type v)) (hDF : D.IsExtension D_F),
      D_F.IsExtension T ∧ D_F.IsExtension E_B ∧ E_B.IsExtension T ∧
      E.Commutes E_B i ∧ (∀ r, (i r : Q) = algebraMap R Q r) ∧
      Function.Bijective (Operator.RingHom.mapConstants (D := D) (E := D_F)
        ⟨algebraMap k F, hDF.1⟩) ∧
      Specs.intermediateFieldStructure (kind := kind) D_F ∧
      Algebra.FiniteType (F : Type v) (B : Type v) ∧ IsNoetherianRing (B : Type v) ∧
      (∀ x : B, x ∈ (B : Type v)⁰ ↔ IsUnit (x : Q)) ∧
      (∀ r : R, r ∈ R⁰ → i r ∈ (B : Type v)⁰) ∧ IsFractionRing (B : Type v) Q := by
  let Q := TotalQuotientRing R
  let YQ := Matrix.GeneralLinearGroup.map (algebraMap R Q) Y
  let B := relativePicardVessiotSubalgebra F YQ
  let : CharZero k := hk.1
  have hDE := hPV.1.1
  have hE := hPV.1.2.1
  have hT := hPV.2.1
  have hDT := hPV.isExtension
  have hgen := matrixGeneratedSubalgebra_eq_top hk hPV.1 hY
  let : Algebra.FiniteType k R := finiteType_of_generatedByMatrix hgen
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have hB : B = Algebra.adjoin (F : Type v) (Set.range (algebraMap R Q)) :=
    generatedByMatrix_eq_adjoin_image F Y hgen
  have hRmem (r : R) : algebraMap R Q r ∈ B :=
    hB ▸ Algebra.subset_adjoin (Set.mem_range_self r)
  let i : R →+* B := (algebraMap R Q).codRestrict B.toSubring hRmem
  have hi (r : R) : (i r : Q) = algebraMap R Q r := rfl
  have hstableImage : T.IsStable (Set.range (algebraMap R Q)) := stable_range_of_commutes hT
  have hstableB : T.IsStable (B : Set Q) := by
    rw [hB]
    apply stable_adjoin hstableImage
    have hRange : Set.range (algebraMap (F : Type v) Q) = (F : Set Q) := by
      ext x
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    rw [hRange]
    exact hF.1
  let D_F : Operator kind (F : Type v) := restrictOperator T F.toSubring hF.1
  let E_B : Operator kind (B : Type v) := restrictOperator T B.toSubring hstableB
  have hFT : D_F.IsExtension T :=
    ⟨restrictOperator_commutes T _ _, Subtype.val_injective⟩
  have hBT : E_B.IsExtension T :=
    ⟨restrictOperator_commutes T _ _, Subtype.val_injective⟩
  have hDF : D.IsExtension D_F := by
    constructor
    · have hcomp : D.Commutes T (algebraMap (F : Type v) Q ∘ algebraMap k F) := by
        rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq k F Q]
        exact hDT.1
      exact commutes_of_comp_injective hFT.2 hcomp hFT.1
    · intro x y hxy
      exact hDT.2 (congrArg Subtype.val hxy)
  have hFB : D_F.IsExtension E_B := by
    constructor
    · exact commutes_of_comp_injective (f := algebraMap (F : Type v) B) hBT.2 hFT.1 hBT.1
    · intro x y hxy
      exact Subtype.ext (congrArg (fun b : B => (b : Q)) hxy)
  have hEB : E.Commutes E_B i :=
    commutes_of_comp_injective hBT.2 hT hBT.1
  have hconstants :
      Function.Bijective (Operator.RingHom.mapConstants (D := D) (E := D_F)
        ⟨algebraMap k F, hDF.1⟩) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hDF.2 (congrArg Subtype.val hxy))
    · intro x
      have h := (Operator.constants_finiteType_fractionRing D E T hk hE hDE.1 hT).2
      let xQ : T.constantSubring :=
        Operator.RingHom.mapConstants ⟨algebraMap (F : Type v) Q, hFT.1⟩ x
      obtain ⟨c, hc⟩ := h xQ
      have hc' : algebraMap R Q (algebraMap k R (c : k)) = ((x : F) : Q) :=
        congrArg Subtype.val hc
      refine ⟨c, Subtype.ext (Subtype.ext ?_)⟩
      change algebraMap k Q (c : k) = ((x : F) : Q)
      rwa [IsScalarTower.algebraMap_apply k R Q]
  obtain ⟨hNoeth, hstructure⟩ := intermediateSubring_structure (k := k) hE hT F.toSubring hF.1 hF.2
  let : IsNoetherianRing (F : Type v) := hNoeth
  let hfinite : Algebra.FiniteType (F : Type v) (B : Type v) :=
    generatedByMatrix_finiteType YQ
  obtain ⟨hreg, hden, hfrac⟩ := fractionRing_of_intermediate B.toSubring i hi
  exact ⟨D_F, E_B, i, hDF, hFT, hFB, hBT, hEB, hi, hconstants, hstructure,
    hfinite, Algebra.FiniteType.isNoetherianRing (F : Type v) (B : Type v), hreg, hden, hfrac⟩

/-- The intermediate total ring and its relative Picard–Vessiot algebra inside the total extension. -/
theorem intermediateTotalRing_structure : Specs.intermediateTotalRingStructure.{u, v} := by
  intro kind k R _ _ _ n D A E T Y hk hPV hY F hF
  exact intermediateTotalRing_structure_aux
    (D := D) (A := A) (E := E) (T := T) (Y := Y) hk hPV hY F hF

end GaloisFormalization.PV
