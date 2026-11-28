import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.DimensionOrbits
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.Forms
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Integral

/-! The dimension bound for change-of-basis orbits of quiver representations. -/

open CategoryTheory Module
open scoped BigOperators

namespace RepTheorySurvey.Quiver.DimensionOrbits

universe u v w d s t

section MatrixRepresentations

variable {k : Type w} [Field k] {Q : Type u} [Quiver.{v} Q] (n : Q → ℕ)

private abbrev ArrowMatrices (R : Type*) :=
  (a : RM03.Arrow Q) → Matrix (Fin (n a.2.1)) (Fin (n a.1)) R

private abbrev BasisMatrices (R : Type*) :=
  (i : Q) → Matrix (Fin (n i)) (Fin (n i)) R

private abbrev ArrowEntry := Σ a : RM03.Arrow Q, Fin (n a.2.1) × Fin (n a.1)

private abbrev BasisEntry := Σ i : Q, Fin (n i) × Fin (n i)

private abbrev spaces (k : Type w) [Field k] (n : Q → ℕ) (i : Q) :=
  ModuleCat.of k (ULift.{d} (Fin (n i) → k))

private noncomputable def standardBasis (i : Q) : Basis (Fin (n i)) k (spaces k n i) :=
  (Pi.basisFun k _).map ULift.moduleEquiv.symm

private noncomputable def matrixRepresentation (A : ArrowMatrices n k) :
    Forms.FiniteRepresentation.{u, v, w, max w d} k Q :=
  ⟨RM03.QuiverRepresentation.ofArrows (spaces k n)
    (fun {i j} a => Matrix.toLin (standardBasis n i) (standardBasis n j) (A ⟨i, j, a⟩)),
    fun i => Module.Finite.of_basis (standardBasis n i)⟩

private theorem dimensionVector_matrixRepresentation (A : ArrowMatrices n k) :
    Forms.dimensionVector (matrixRepresentation n A) = (fun i => (n i : ℤ)) := by
  funext i
  change (Module.finrank k (spaces k n i) : ℤ) = _
  rw [Module.finrank_eq_card_basis (standardBasis n i), Fintype.card_fin]

/-- An isomorphism between standard matrix representations is precisely an invertible
change of bases intertwining their arrow matrices. -/
private theorem matrixRepresentation_iso_iff (A B : ArrowMatrices n k) :
    Nonempty ((matrixRepresentation.{u, v, w, d} n A).obj ≅ (matrixRepresentation n B).obj) ↔
      ∃ G : BasisMatrices n k, (∀ i, (G i).det ≠ 0) ∧
        ∀ a : RM03.Arrow Q, G a.2.1 * A a = B a * G a.1 := by
  classical
  let b := fun i => standardBasis.{u, w, d} (k := k) n i
  constructor
  · rintro ⟨e⟩
    let f (i : Q) : spaces.{u, w, d} k n i →ₗ[k] spaces.{u, w, d} k n i :=
      RM03.QuiverRepresentation.component e.hom i
    let g (i : Q) : spaces.{u, w, d} k n i →ₗ[k] spaces.{u, w, d} k n i :=
      RM03.QuiverRepresentation.component e.inv i
    let G (i : Q) := LinearMap.toMatrix (b i) (b i) (f i)
    refine ⟨G, fun i => ?_, fun a => ?_⟩
    · apply Matrix.det_ne_zero_of_right_inverse (B := LinearMap.toMatrix (b i) (b i) (g i))
      change LinearMap.toMatrix (b i) (b i) (f i) * LinearMap.toMatrix (b i) (b i) (g i) = 1
      rw [← LinearMap.toMatrix_comp (b i) (b i) (b i)]
      change LinearMap.toMatrix (b i) (b i)
        (RM03.QuiverRepresentation.component
          (e.inv ≫ e.hom) i) = 1
      rw [e.inv_hom_id, RM03.QuiverRepresentation.component_id]
      exact LinearMap.toMatrix_id (b i)
    · rcases a with ⟨i, j, a⟩
      have h := RM03.QuiverRepresentation.naturality e.hom a.toPath
      simp only [RM03.QuiverRepresentation.mapPath_toPath, matrixRepresentation,
        RM03.QuiverRepresentation.arrow_ofArrows] at h
      change (f j).comp ((A ⟨i, j, a⟩).toLin (b i) (b j)) =
        ((B ⟨i, j, a⟩).toLin (b i) (b j)).comp (f i) at h
      have eq := congrArg (fun f => LinearMap.toMatrix (b i) (b j) f) h
      rw [LinearMap.toMatrix_comp (b i) (b j) (b j),
        LinearMap.toMatrix_comp (b i) (b i) (b j), LinearMap.toMatrix_toLin,
        LinearMap.toMatrix_toLin] at eq
      exact eq
  · rintro ⟨G, hG, h⟩
    let e (i : Q) := Matrix.toLinearEquiv (b i) (G i) (isUnit_iff_ne_zero.mpr (hG i))
    let f : (matrixRepresentation.{u, v, w, d} n A).obj ⟶ (matrixRepresentation n B).obj :=
      RM03.QuiverRepresentation.homMk (fun i => (e i).toLinearMap) (by
        intro i j a
        change ((G j).toLin (b j) (b j)).comp
          (RM03.QuiverRepresentation.arrow (matrixRepresentation.{u, v, w, d} n A).obj a) =
          (RM03.QuiverRepresentation.arrow (matrixRepresentation.{u, v, w, d} n B).obj a).comp ((G i).toLin (b i) (b i))
        simp only [matrixRepresentation, RM03.QuiverRepresentation.arrow_ofArrows]
        change ((G j).toLin (b j) (b j)).comp ((A ⟨i, j, a⟩).toLin (b i) (b j)) =
          ((B ⟨i, j, a⟩).toLin (b i) (b j)).comp ((G i).toLin (b i) (b i))
        rw [← Matrix.toLin_mul (b i) (b j) (b j), ← Matrix.toLin_mul (b i) (b i) (b j),
          h ⟨i, j, a⟩])
    have hf (i : Paths Q) : IsIso (f.app i) := by
      change IsIso (ModuleCat.ofHom (e i).toLinearMap)
      exact (LinearEquiv.toModuleIso (e i)).isIso_hom
    have : IsIso f := (NatTrans.isIso_iff_isIso_app f).mpr hf
    exact ⟨asIso f⟩

/-- A basis change can be scaled to make one of its entries equal to one. -/
private theorem exists_normalized_basis_change {A B : ArrowMatrices n k}
    (G : BasisMatrices n k) (hG : ∀ i, (G i).det ≠ 0)
    (h : ∀ a : RM03.Arrow Q, G a.2.1 * A a = B a * G a.1)
    (i : Q) (hi : 0 < n i) :
    ∃ (p : BasisEntry n) (H : BasisMatrices n k),
      H p.1 p.2.1 p.2.2 = 1 ∧ (∀ j, (H j).det ≠ 0) ∧
        ∀ a : RM03.Arrow Q, H a.2.1 * A a = B a * H a.1 := by
  have : Nonempty (Fin (n i)) := ⟨⟨0, hi⟩⟩
  obtain ⟨r, c, hrc⟩ : ∃ r c, G i r c ≠ 0 := by
    by_contra! hzero
    have : G i = 0 := Matrix.ext hzero
    exact hG i (by rw [this, Matrix.det_zero])
  let s := (G i r c)⁻¹
  refine ⟨⟨i, r, c⟩, fun j => s • G j, ?_, ?_, ?_⟩
  · change s * G i r c = 1
    exact inv_mul_cancel₀ hrc
  · intro j
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hrc)) (hG j)
  · intro a
    rw [Matrix.smul_mul, Matrix.mul_smul, h a]

end MatrixRepresentations

section PolynomialRelations

open MvPolynomial

/-- The rational functions regular on a principal open set in affine space satisfy a
nonzero polynomial relation whenever there are more functions than coordinates. -/
private theorem exists_polynomial_relation {k : Type w} [Field k]
    {ι : Type s} {J : Type t} [Fintype ι] [Fintype J]
    {δ : MvPolynomial ι k} (hδ : δ ≠ 0) (hcard : Fintype.card ι < Fintype.card J)
    (f : J → Localization.Away δ) :
    ∃ p : MvPolynomial J k, p ≠ 0 ∧ aeval f p = 0 := by
  let P := MvPolynomial ι k
  let K := FractionRing P
  let L := Localization.Away δ
  have hunit : IsUnit (IsScalarTower.toAlgHom k P K δ) := by
    refine isUnit_iff_ne_zero.mpr (fun h => hδ (IsFractionRing.injective P K ?_))
    change algebraMap P K δ = 0 at h
    simpa only [map_zero] using h
  let e : L →ₐ[k] K := IsLocalization.Away.liftAlgHom δ hunit
  have he : Function.Injective e := by
    have hL : Function.Injective (algebraMap P L) :=
      IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors hδ)
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers δ) e.toRingHom).mpr
    intro a b
    change algebraMap P L a = algebraMap P L b ↔ e (algebraMap P L a) = e (algebraMap P L b)
    have hl (x : P) : e (algebraMap P L x) = algebraMap P K x :=
      IsLocalization.Away.lift_eq δ hunit x
    rw [hl a, hl b]
    exact ⟨fun h => congrArg _ (hL h), fun h => congrArg _ (IsFractionRing.injective P K h)⟩
  have htr : IsTranscendenceBasis k (algebraMap P K ∘ X (R := k) (σ := ι)) := by
    let : Algebra.IsAlgebraic P K :=
      (IsFractionRing.comap_isAlgebraic_iff (A := P) (K := K) (C := K)).mpr inferInstance
    exact (IsTranscendenceBasis.mvPolynomial ι k).algebraMap_comp
  by_contra! h
  have hf : AlgebraicIndependent k f :=
    algebraicIndependent_iff.mpr fun p hp => not_not.mp (fun hn => h p hn hp)
  have hK : Algebra.trdeg k K = (Fintype.card ι : Cardinal) := by
    apply Cardinal.lift_inj.{max s w, s}.mp
    simpa only [Cardinal.mk_fintype, Cardinal.lift_natCast] using
      htr.lift_cardinalMk_eq_trdeg.symm
  have hle := (hf.map' he).lift_cardinalMk_le_trdeg
  rw [hK] at hle
  exact (not_le_of_gt hcard) (by simpa only [Cardinal.mk_fintype, Cardinal.lift_natCast,
    Nat.cast_le] using hle)

end PolynomialRelations

section OrbitCharts

open MvPolynomial

variable {k : Type w} [Field k] {Q : Type u} [Quiver.{v} Q]
  [Fintype Q] [Fintype (RM03.Arrow Q)] (n : Q → ℕ)

private abbrev basisEntry (G : BasisMatrices n k) (j : BasisEntry n) :=
  G j.1 j.2.1 j.2.2

private abbrev arrowEntry {R : Type*} (A : ArrowMatrices n R) (j : ArrowEntry n) :=
  A j.1 j.2.1 j.2.2

/-- Specializing a normalized change of bases evaluates the generic orbit on the open set
where the product of its vertex determinants is invertible. -/
private theorem exists_chart_polynomial (A : ArrowMatrices n k) (pivot : BasisEntry n)
    (hcard : Fintype.card (BasisEntry n) ≤ Fintype.card (ArrowEntry n)) :
    ∃ p : MvPolynomial (ArrowEntry n) k, p ≠ 0 ∧
      ∀ (H : BasisMatrices n k), basisEntry n H pivot = 1 →
        (∀ i, (H i).det ≠ 0) →
        ∀ B : ArrowMatrices n k, (∀ a : RM03.Arrow Q, H a.2.1 * A a = B a * H a.1) →
          eval (arrowEntry n B) p = 0 := by
  classical
  let ι := {j : BasisEntry n // j ≠ pivot}
  let P := MvPolynomial ι k
  let G : BasisMatrices n P := fun i => Matrix.of fun r c =>
    if h : (⟨i, r, c⟩ : BasisEntry n) ≠ pivot then X ⟨⟨i, r, c⟩, h⟩ else 1
  let δ : P := ∏ i : Q, (G i).det
  let ev (H : BasisMatrices n k) : P →ₐ[k] k := aeval (fun j : ι => basisEntry n H j.1)
  have hG (H : BasisMatrices n k) (hp : basisEntry n H pivot = 1) (i : Q) :
      (ev H).toRingHom.mapMatrix (G i) = H i := by
    ext r c
    change ev H (if h : (⟨i, r, c⟩ : BasisEntry n) ≠ pivot then X ⟨⟨i, r, c⟩, h⟩ else 1)
      = basisEntry n H ⟨i, r, c⟩
    split
    · exact aeval_X _ _
    · rw [map_one, not_ne_iff.mp ‹¬ (⟨i, r, c⟩ : BasisEntry n) ≠ pivot›, hp]
  have hδ (H : BasisMatrices n k) (hp : basisEntry n H pivot = 1)
      (hH : ∀ i, (H i).det ≠ 0) : ev H δ ≠ 0 := by
    change ev H (∏ i : Q, (G i).det) ≠ 0
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    rw [AlgHom.map_det]
    exact (congrArg Matrix.det (hG H hp i)).trans_ne (hH i)
  by_cases hz : δ = 0
  · exact ⟨1, one_ne_zero, fun H hp hH => (hδ H hp hH (by rw [hz, map_zero])).elim⟩
  let L := Localization.Away δ
  let g (i : Q) := (algebraMap P L).mapMatrix (G i)
  have hg (i : Q) : IsUnit (g i).det := by
    change IsUnit ((algebraMap P L).mapMatrix (G i)).det
    rw [← RingHom.map_det]
    exact IsLocalization.Away.isUnit_of_dvd δ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  let A' : ArrowMatrices n L := fun a => (A a).map (algebraMap k L)
  let B' : ArrowMatrices n L := fun a => g a.2.1 * A' a * (g a.1)⁻¹
  have hB' (a : RM03.Arrow Q) : B' a * g a.1 = g a.2.1 * A' a :=
    Matrix.nonsing_inv_mul_cancel_right _ _ (hg a.1)
  have hlt : Fintype.card ι < Fintype.card (ArrowEntry n) :=
    (Fintype.card_subtype_lt (x := pivot) (not_not_intro rfl)).trans_le hcard
  obtain ⟨p, hp, hpB⟩ := exists_polynomial_relation hz hlt (arrowEntry n B')
  refine ⟨p, hp, fun H hpivot hH B hB => ?_⟩
  have hu : IsUnit (ev H δ) := isUnit_iff_ne_zero.mpr (hδ H hpivot hH)
  let e : L →ₐ[k] k := IsLocalization.Away.liftAlgHom δ hu
  have heG (i : Q) : (g i).map e = H i := by
    rw [← hG H hpivot i]
    ext r c
    exact IsLocalization.Away.lift_eq δ hu (G i r c)
  have heA (a : RM03.Arrow Q) : (A' a).map e = A a := by
    ext r c
    exact e.commutes (A a r c)
  have heB (a : RM03.Arrow Q) : (B' a).map e = B a := by
    have eq := congrArg (fun M : Matrix (Fin (n a.2.1)) (Fin (n a.1)) L => M.map e) (hB' a)
    change (B' a * g a.1).map e = (g a.2.1 * A' a).map e at eq
    rw [Matrix.map_mul (L := B' a) (M := g a.1),
      Matrix.map_mul (L := g a.2.1) (M := A' a), heG, heG, heA, hB a] at eq
    have hcancel := congrArg (· * (H a.1)⁻¹) eq
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.mpr (hH a.1))]
      using hcancel
  have heval : (fun j => e (arrowEntry n B' j)) = arrowEntry n B := by
    funext j
    exact congrFun (congrFun (heB j.1) j.2.1) j.2.2
  have eq := congrArg e hpB
  rw [MvPolynomial.comp_aeval_apply, heval, map_zero] at eq
  exact eq

end OrbitCharts

/-- If a nonzero nonnegative dimension vector has nonpositive Tits value, the
finite-dimensional representations of that dimension occupy infinitely many classes. -/
theorem infinite_fixedDimensionClasses :
    DimensionOrbitsSpec.InfiniteFixedDimensionClasses.{u, v, w, d} := by
  classical
  intro k Q _ _ _ _ _ _ x hx hx_nonneg hq
  let n (i : Q) := (x i).toNat
  have hn (i : Q) : (n i : ℤ) = x i := Int.toNat_of_nonneg (hx_nonneg i)
  obtain ⟨i, hi⟩ : ∃ i, 0 < n i := by
    by_contra! h
    apply hx
    funext j
    have hzero : n j = 0 := Nat.eq_zero_of_le_zero (h j)
    rw [← hn j, hzero]
    rfl
  have hcard : Fintype.card (BasisEntry n) ≤ Fintype.card (ArrowEntry n) := by
    simp only [BasisEntry, ArrowEntry, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
    have hq' := sub_nonpos.mp hq
    simp only [← hn] at hq'
    simp only [mul_comm] at hq' ⊢
    exact_mod_cast hq'
  let C := DimensionOrbitsSpec.FixedDimensionClass.{u, v, w, max w d} k x
  let cls (A : ArrowMatrices n k) : C :=
    ⟨Quotient.mk _ (matrixRepresentation n A), matrixRepresentation n A, rfl,
      (dimensionVector_matrixRepresentation n A).trans (funext hn)⟩
  apply not_finite_iff_infinite.mp
  intro hf
  let R := Set.range cls
  let _ : Fintype R := Fintype.ofFinite _
  let rep (c : R) : ArrowMatrices n k := c.2.choose
  have hrep (c : R) : cls (rep c) = c.1 := c.2.choose_spec
  choose p hp hp_zero using fun (c : R) (pivot : BasisEntry n) =>
    exists_chart_polynomial n (rep c) pivot hcard
  let f (j : R × BasisEntry n) := p j.1 j.2
  let P := ∏ j : R × BasisEntry n, f j
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hp j.1 j.2
  apply hP
  apply MvPolynomial.funext
  intro y
  let B : ArrowMatrices n k := fun a => Matrix.of fun r c => y ⟨a, r, c⟩
  let c : R := ⟨cls B, B, rfl⟩
  have heq : (cls (rep c)).1 = (cls B).1 := congrArg Subtype.val (hrep c)
  have hiso : Nonempty ((matrixRepresentation.{u, v, w, d} n (rep c)).obj ≅
      (matrixRepresentation n B).obj) := Quotient.exact heq
  obtain ⟨G, hG, h⟩ := (matrixRepresentation_iso_iff n (rep c) B).mp hiso
  obtain ⟨pivot, H, hpivot, hH, h⟩ := exists_normalized_basis_change n G hG h i hi
  have hzero : MvPolynomial.eval y (f (c, pivot)) = 0 := hp_zero c pivot H hpivot hH B h
  change MvPolynomial.eval y (∏ j : R × BasisEntry n, f j) = MvPolynomial.eval y 0
  rw [map_prod, map_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ (c, pivot)) hzero

end RepTheorySurvey.Quiver.DimensionOrbits
