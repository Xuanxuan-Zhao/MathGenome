import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.MatrixAlgebraForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Group

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData

open _root_.LinearAlgebraicGroups.Specs
open Specs.TypeAMatrixDescentData

set_option backward.isDefEq.respectTransparency false

private theorem chain_fix_zero {r : ℕ} (hr : 2 ≤ r) (p : ChainSymmetries r)
    (h : (p.val ⟨0, by omega⟩).val = 0) : p.val = 1 := by
  ext i
  change (p.val i).val = i.val
  obtain ⟨i, hi⟩ := i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases h0 : i = 0
    · subst i
      exact h
    by_cases h1 : i = 1
    · subst i
      have he := p.property ⟨0, by omega⟩ ⟨1, hi⟩
      have ha := he.mpr (Or.inl rfl)
      change ((p.val ⟨0, by omega⟩).val + 1 = (p.val ⟨1, hi⟩).val) ∨
        ((p.val ⟨1, hi⟩).val + 1 = (p.val ⟨0, by omega⟩).val) at ha
      change (p.val ⟨1, hi⟩).val = 1
      rw [h] at ha
      omega
    have he := (p.property ⟨i - 1, by omega⟩ ⟨i, hi⟩).mpr
      (show Adjacent (⟨i - 1, by omega⟩ : Fin r) ⟨i, hi⟩ from Or.inl (by change i - 1 + 1 = i; omega))
    have hprev : (p.val ⟨i - 1, by omega⟩).val = i - 1 := ih (i - 1) (by omega) (by omega)
    have hprev' : (p.val ⟨i - 2, by omega⟩).val = i - 2 := ih (i - 2) (by omega) (by omega)
    have hne : (p.val ⟨i, hi⟩).val ≠ i - 2 := by
      intro eq
      have e := congrArg Fin.val (p.val.injective (Fin.ext (eq.trans hprev'.symm)))
      change i = i - 2 at e
      omega
    change ((p.val ⟨i - 1, by omega⟩).val + 1 = (p.val ⟨i, hi⟩).val) ∨
      ((p.val ⟨i, hi⟩).val + 1 = (p.val ⟨i - 1, by omega⟩).val) at he
    rw [hprev] at he
    change (p.val ⟨i, hi⟩).val = i
    omega

private theorem chain_zero_endpoint {r : ℕ} (hr : 2 ≤ r) (p : ChainSymmetries r) :
    (p.val ⟨0, by omega⟩).val = 0 ∨ (p.val ⟨0, by omega⟩).val + 1 = r := by
  let z : Fin r := p.val ⟨0, by omega⟩
  change z.val = 0 ∨ z.val + 1 = r
  have hz := z.isLt
  by_contra! h
  let a : Fin r := ⟨z.val - 1, by omega⟩
  let b : Fin r := ⟨z.val + 1, by omega⟩
  have ha : Adjacent a z := Or.inl (by change z.val - 1 + 1 = z.val; omega)
  have hb : Adjacent b z := Or.inr rfl
  have preimage (i : Fin r) (hi : Adjacent i z) : p.val.symm i = ⟨1, by omega⟩ := by
    apply Fin.ext
    have hh := (p.property (p.val.symm i) ⟨0, by omega⟩).mp (by simpa [z] using hi)
    unfold Adjacent at hh
    change (_ + 1 = 0) ∨ (0 + 1 = _) at hh
    change (p.val.symm i).val = 1
    omega
  have hab := congrArg Fin.val (p.val.symm.injective ((preimage a ha).trans (preimage b hb).symm))
  change z.val - 1 = z.val + 1 at hab
  omega

private def chainReversal (r : ℕ) : ChainSymmetries r :=
  ⟨Fin.revPerm, by
    intro i j
    change Adjacent i.rev j.rev ↔ Adjacent i j
    unfold Adjacent
    simp only [Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
    omega⟩

theorem chainClassification : ChainClassification := by
  intro r hr p
  rcases chain_zero_endpoint hr p with h | h
  · exact Or.inl (chain_fix_zero hr p h)
  · right
    have hrp : (chainReversal r * p).val = 1 := by
      apply chain_fix_zero hr
      change (p.val ⟨0, by omega⟩).rev.val = 0
      rw [Fin.val_rev]
      omega
    change Fin.revPerm * p.val = 1 at hrp
    apply mul_left_cancel (a := Fin.revPerm)
    rw [hrp]
    ext i
    change i.val = (i.rev).rev.val
    rw [Fin.rev_rev]

private theorem reversal_ne_one {r : ℕ} (hr : 2 ≤ r) : chainReversal r ≠ 1 := by
  intro h
  have he := congrArg (fun p : ChainSymmetries r => (p.val ⟨0, by omega⟩).val) h
  change (⟨0, by omega⟩ : Fin r).rev.val = 0 at he
  rw [Fin.val_rev] at he
  change r - (0 + 1) = 0 at he
  omega

private theorem reversal_mul_self (r : ℕ) : chainReversal r * chainReversal r = 1 := by
  apply Subtype.ext
  ext i
  change i.rev.rev.val = i.val
  rw [Fin.rev_rev]

private theorem chain_eq_one_or_reversal {r : ℕ} (hr : 2 ≤ r) (p : ChainSymmetries r) :
    p = 1 ∨ p = chainReversal r :=
  (chainClassification hr p).imp Subtype.ext Subtype.ext

private noncomputable def chainParity {r : ℕ} (hr : 2 ≤ r) : ChainSymmetries r ≃* DiagramParity := by
  classical
  let odd : DiagramParity := Multiplicative.ofAdd 1
  have hodd : odd ≠ 1 := by decide
  have hsq : odd * odd = 1 := by decide
  let f : ChainSymmetries r →* DiagramParity :=
    { toFun := fun p => if p = 1 then 1 else odd
      map_one' := ite_eq_left rfl
      map_mul' := by
        intro p q
        by_cases hp : p = 1
        · subst p; simp
        by_cases hq : q = 1
        · subst q; simp
        have h := (chain_eq_one_or_reversal hr p).resolve_left hp
        have h' := (chain_eq_one_or_reversal hr q).resolve_left hq
        rw [ite_eq_right hp, ite_eq_right hq, hsq, h, h', reversal_mul_self, ite_eq_left rfl] }
  apply MulEquiv.ofBijective f
  constructor
  · intro p q h
    rcases chain_eq_one_or_reversal hr p with rfl | rfl <;>
      rcases chain_eq_one_or_reversal hr q with rfl | rfl <;>
      simp [f, reversal_ne_one hr, hodd, Ne.symm hodd] at h ⊢
  · intro p
    have h : ∀ q : DiagramParity, q = 1 ∨ q = odd := by decide
    rcases h p with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨chainReversal r, ite_eq_right (reversal_ne_one hr)⟩

section Based

open Pinning (BasedRootDatum AttachedDatum)
open SpecialLinearDatum
open GeneralLinearStructure (SpecialMatrixPoints)

private def simpleVertex (r : ℕ) (i : Fin r) : RootIndices (r + 1) :=
  ⟨(i.castSucc, i.succ), ne_of_lt Fin.castSucc_lt_succ⟩

private noncomputable def matrixVertices {k : Type u} [Field k] {r : ℕ}
    {G : AffineAlgebraicGroup k} {s : SpecialMatrixPoints G (r + 1)}
    {T : DiagonalTorus s} {L : LatticeIdentification T} {M : RootIdentification T L}
    (B : UpperTriangularBorel T L M) (D : AttachedDatum B.pair) : Fin r ≃ ↥D.toBased.base.support := by
  have h := RootData.SpecialLinearDatum.matrixBasedDatum_of_attachedDatum B D
  let e : Fin r → ↥D.toBased.base.support := fun i =>
    ⟨M.indices (simpleVertex r i), (h.2 _).2 ⟨i, rfl, rfl⟩⟩
  apply Equiv.ofBijective e
  constructor
  · intro i j hij
    have he := M.indices.injective (congrArg Subtype.val hij)
    exact Fin.castSucc_injective _ (congrArg (fun x => x.val.1) he)
  · rintro ⟨α, hα⟩
    obtain ⟨p, rfl⟩ := M.indices.surjective α
    obtain ⟨i, hi, hj⟩ := (h.2 p).mp hα
    exact ⟨i, Subtype.ext (congrArg M.indices (Subtype.ext (Prod.ext hi.symm hj.symm)))⟩

private theorem matrixVertex_pairing {k : Type u} [Field k] {r : ℕ}
    {G : AffineAlgebraicGroup k} {s : SpecialMatrixPoints G (r + 1)}
    {T : DiagonalTorus s} {L : LatticeIdentification T} {M : RootIdentification T L}
    (B : UpperTriangularBorel T L M) (D : AttachedDatum B.pair) (i j : Fin r) :
    D.toBased.datum.pairing (matrixVertices B D i) (matrixVertices B D j) =
      if i = j then 2 else if Adjacent i j then -1 else 0 := by
  letI := D.comm
  let α := M.indices (simpleVertex r i)
  let β := M.indices (simpleVertex r j)
  change D.datum.rootDatum.pairing α β = _
  rw [← RootPairing.root_coroot_eq_pairing, D.datum.root_eq]
  change D.datum.rootDatum.toLinearMap (Additive.ofMul α.val)
    (Additive.ofMul (Additive.toMul (D.datum.rootDatum.coroot β))) = _
  rw [D.datum.pairing_eq]
  rw [L.pairing_eq, show Additive.ofMul (Additive.toMul (D.datum.rootDatum.coroot β)) =
    D.datum.rootDatum.coroot β from rfl]
  rw [show α = M.indices (simpleVertex r i) from rfl, M.character_eq,
    show β = M.indices (simpleVertex r j) from rfl,
    RootData.SpecialLinearDatum.corootsOfMatrixDatum M D.datum]
  exact RootData.SpecialLinearDatum.simpleCartanPairings r i j

private theorem matrixVertex_basis {k : Type u} [Field k] {r : ℕ}
    {G : AffineAlgebraicGroup k} {s : SpecialMatrixPoints G (r + 1)}
    {T : DiagonalTorus s} {L : LatticeIdentification T} {M : RootIdentification T L}
    (B : UpperTriangularBorel T L M) (D : AttachedDatum B.pair) :
    ∃ b : Module.Basis (Fin r) ℤ D.toBased.Y,
      ∀ i, b i = D.toBased.datum.coroot (matrixVertices B D i) := by
  obtain ⟨b, hb⟩ := RootData.SpecialLinearDatum.simpleCorootBasis r
  letI := D.comm
  refine ⟨b.map L.cocharacters.symm, fun i => L.cocharacters.injective ?_⟩
  change L.cocharacters (L.cocharacters.symm (b i)) =
    L.cocharacters (D.datum.rootDatum.coroot (M.indices (simpleVertex r i)))
  rw [LinearEquiv.apply_symm_apply, hb, RootData.SpecialLinearDatum.corootsOfMatrixDatum M D.datum]
  rfl

private theorem basedSimple_iff {D : BasedRootDatum.{u}} (d : Aut D) (i : D.I) :
    i ∈ D.base.support ↔ d.asIso.hom.val.indexEquiv i ∈ D.base.support := by
  have h := congrArg (fun S : Set D.I => d.asIso.hom.val.indexEquiv i ∈ S) d.asIso.hom.property
  constructor
  · intro hi
    exact Eq.mp h ⟨i, hi, rfl⟩
  · intro hi
    obtain ⟨j, hj, he⟩ := Eq.mpr h hi
    exact d.asIso.hom.val.indexEquiv.injective he ▸ hj

private noncomputable def basedChainMap {D : BasedRootDatum.{u}} {r : ℕ}
    (v : Fin r ≃ ↥D.base.support)
    (h : ∀ i j, D.datum.pairing (v i) (v j) =
      if i = j then 2 else if Adjacent i j then -1 else 0) : Aut D →* ChainSymmetries r := by
  classical
  let p (d : Aut D) : Equiv.Perm (Fin r) :=
    v.trans ((d.asIso.hom.val.indexEquiv.subtypeEquiv (basedSimple_iff d)).trans v.symm)
  have hp (d : Aut D) (i : Fin r) :
      (v (p d i)).val = d.asIso.hom.val.indexEquiv (v i).val :=
    congrArg Subtype.val (v.apply_symm_apply _)
  refine { toFun := fun d => ⟨p d, ?_⟩, map_one' := ?_, map_mul' := ?_ }
  · intro i j
    have he := d.asIso.hom.val.toHom.pairing (i := (v i).val) (j := (v j).val)
    rw [← hp, ← hp, h, h] at he
    by_cases hij : i = j
    · subst j
      simp [Adjacent]
    · have hn : p d i ≠ p d j := fun eq => hij ((p d).injective eq)
      by_cases ha : Adjacent i j <;> by_cases hb : Adjacent (p d i) (p d j) <;>
        simp_all
  · apply Subtype.ext
    apply Equiv.ext
    intro i
    change p 1 i = i
    apply v.injective
    apply Subtype.ext
    rw [hp]
    rfl
  · intro a b
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change p (a * b) i = p a (p b i)
    apply v.injective
    apply Subtype.ext
    rw [hp, hp, hp]
    rfl

private theorem basedChainMap_onRoots {D : BasedRootDatum.{u}} {r : ℕ}
    (v : Fin r ≃ ↥D.base.support) (h : ∀ i j, D.datum.pairing (v i) (v j) =
      if i = j then 2 else if Adjacent i j then -1 else 0) (d : Aut D) (i : Fin r) :
    (v ((basedChainMap v h d).val i)).val = d.asIso.hom.val.indexEquiv (v i).val :=
  congrArg Subtype.val (v.apply_symm_apply _)

private theorem basedChainMap_injective {D : BasedRootDatum.{u}} {r : ℕ}
    (v : Fin r ≃ ↥D.base.support) (h : ∀ i j, D.datum.pairing (v i) (v j) =
      if i = j then 2 else if Adjacent i j then -1 else 0)
    (b : Module.Basis (Fin r) ℤ D.Y) (hb : ∀ i, b i = D.datum.coroot (v i)) :
    Function.Injective (basedChainMap v h) := by
  intro d e he
  have hco (f : Aut D) (i : Fin r) :
      f.asIso.hom.val.coweightEquiv.symm (b i) = b ((basedChainMap v h f).val i) := by
    apply f.asIso.hom.val.coweightEquiv.injective
    rw [LinearEquiv.apply_symm_apply, hb, hb, basedChainMap_onRoots]
    have hm := f.asIso.hom.val.toHom.coroot_coweightMap_apply D.datum D.datum
      (f.asIso.hom.val.indexEquiv (v i).val)
    simpa only [Equiv.symm_apply_apply, RootPairing.Equiv.coweightEquiv_apply] using hm.symm
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  apply RootPairing.Equiv.coweightHom_injective D.datum
  apply MulOpposite.unop_injective
  suffices h : d.asIso.hom.val.coweightEquiv.symm = e.asIso.hom.val.coweightEquiv.symm by
    exact congrArg LinearEquiv.symm h
  apply LinearEquiv.toLinearMap_inj.mp
  apply b.ext
  intro i
  change d.asIso.hom.val.coweightEquiv.symm (b i) = e.asIso.hom.val.coweightEquiv.symm (b i)
  rw [hco, hco, he]

end Based


theorem fppfRoot : FppfRoot.{u} := by
  intro k _ R n hn a
  rcases subsingleton_or_nontrivial R with h | h
  · refine ⟨R, 𝟙 R, 1, ?_, Subsingleton.elim _ _⟩
    rw [op_id, (testSpec k).map_id]
    change Fppf.IsFppf (𝟙 _)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let p : Polynomial R := Polynomial.X ^ n - Polynomial.C (a : R)
  let A := AdjoinRoot p
  let f : R ⟶ CommAlgCat.of k A := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R A)
  have hr : AdjoinRoot.root p ^ n = algebraMap R A (a : R) := by
    change _ = AdjoinRoot.of p (a : R)
    apply sub_eq_zero.mp
    simpa only [p, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, AdjoinRoot.algebraMap_eq] using AdjoinRoot.eval₂_root p
  have hu : IsUnit (AdjoinRoot.root p) := (isUnit_pow_iff hn.ne').mp
    (hr ▸ (Units.map (algebraMap R A).toMonoidHom a).isUnit)
  refine ⟨CommAlgCat.of k A, f, hu.unit, ?_, ?_⟩
  · have hp : p.Monic := Polynomial.monic_X_pow_sub_C _ hn.ne'
    let b := (AdjoinRoot.powerBasis' hp).basis
    have hd : (AdjoinRoot.powerBasis' hp).dim = n := by
      simp [AdjoinRoot.powerBasis', p]
    have : Nonempty (Fin (AdjoinRoot.powerBasis' hp).dim) := by
      rw [hd]
      exact ⟨⟨0, hn⟩⟩
    have hff : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_linearEquiv _ _ b.repr
    change Fppf.IsFppf (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    obtain ⟨hf, hs⟩ := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap R A))).2
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
    exact ⟨hf, hs, HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr
      (inferInstance : Algebra.FinitePresentation R A))⟩
  · apply Units.ext
    change (↑hu.unit : A) ^ n = algebraMap R A (a : R)
    rw [hu.unit_spec, hr]


section Projective

open AutomorphismSequence Fppf GeneralLinearStructure
open Descent.MatrixAlgebraForms
open Specs.Unipotent (Index)
open Matrix

variable {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}

open private matrixProjection matrixProjection_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.MatrixAlgebraForms

section
open private projection_eq_one_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.MatrixAlgebraForms

private theorem matrixProjection_eq_one_iff (R : TestAlgebra k) (P : ProjectivePresentation k n)
    (g : GL (Index.{u} n) R) :
    matrixProjection P R g = 1 ↔ ∃ c : Rˣ, g = GeneralLinearGroup.scalar _ c :=
  projection_eq_one_iff P R g
end

open private groupSectionsMap groupSectionsFullyFaithful groupSectionsMap_locallySurjective
  groupSections_isSheaf fppf_mem covering_of_affine_tests descends_iso_of_locallySurjective
  projection_eq_one_iff relativeHom_ext_affine relativeEvaluate
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
variable (s : SpecialMatrixPoints G n) (P : ProjectivePresentation k n)

private def toLinearPoints :
    StandardGroups.specialLinearPoints k (Index.{u} n) ⟶
      StandardGroups.generalLinearPoints k (Index.{u} n) where
  app R := GrpCat.ofHom SpecialLinearGroup.toGL
  naturality R S a := by
    apply GrpCat.ext
    intro x
    apply Units.ext
    rfl

private noncomputable def matrixInclusion : G.val ⟶ P.linearGroup :=
  (groupHomEquiv G.val P.linearGroup G.property.1).symm (s.hom ≫ toLinearPoints ≫ P.linearPoints.inv)

private theorem matrixInclusion_apply (R : TestAlgebra k) (x : Points G.val.X R) :
    x ≫ (matrixInclusion s P).hom.hom =
      P.linearPoints.inv.app R (SpecialLinearGroup.toGL (s.hom.app R x)) := by
  exact congrArg (fun f => f.app R x)
    ((groupHomEquiv G.val P.linearGroup G.property.1).apply_symm_apply
      (s.hom ≫ toLinearPoints ≫ P.linearPoints.inv))

private theorem matrix_centralizer (hn : 0 < n) {R : Type u} [CommRing R]
    (g : GL (Index.{u} n) R)
    (h : ∀ x : SpecialLinearGroup (Index.{u} n) R,
      Commute g (SpecialLinearGroup.toGL x)) :
    ∃ a : Rˣ, g = GeneralLinearGroup.scalar _ a := by
  have comm (i j : Index.{u} n) (hij : i ≠ j) :
      g.val * single i j (1 : R) = single i j 1 * g.val := by
    have e := congrArg Units.val (h (SpecialLinearGroup.transvection hij 1)).eq
    change g.val * (1 + single i j 1) = (1 + single i j 1) * g.val at e
    simpa only [mul_add, add_mul, mul_one, one_mul, add_right_inj] using e
  let i₀ : Index.{u} n := ⟨⟨0, hn⟩⟩
  have diag (i j : Index.{u} n) (hij : i ≠ j) : g.val i i = g.val j j := by
    simpa [mul_single_apply_same, single_mul_apply_same] using
      (congrArg (fun m : Matrix (Index.{u} n) (Index.{u} n) R => m i j) (comm i j hij))
  have off (i j : Index.{u} n) (hij : i ≠ j) : g.val i j = 0 := by
    simpa [mul_single_apply_same, single_mul_apply_of_ne _ j i i i hij] using
      (congrArg (fun m : Matrix (Index.{u} n) (Index.{u} n) R => m i i) (comm j i hij.symm))
  have hg : g.val = Matrix.scalar _ (g.val i₀ i₀) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      by_cases hi : i = i₀
      · rw [hi]
      · exact diag i i₀ hi
    · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, off i j hij]
  have hu : IsUnit (g.val i₀ i₀) := by
    have e := congrArg (fun m : Matrix (Index.{u} n) (Index.{u} n) R => m i₀ i₀) g.val_inv
    rw [hg, Matrix.scalar_apply, diagonal_mul, one_apply_eq] at e
    exact IsUnit.of_mul_eq_one _ e
  exact ⟨hu.unit, Units.ext (by simpa only [GeneralLinearGroup.coe_scalar, hu.unit_spec] using hg)⟩

private theorem matrix_central_iff (hn : 0 < n) (R : TestAlgebra k) (x : Points G.val.X R) :
    innerAut x = 1 ↔
      ∃ a : Rˣ, SpecialLinearGroup.toGL (s.hom.app R x) = GeneralLinearGroup.scalar _ a := by
  constructor
  · intro h
    apply matrix_centralizer hn
    intro y
    let z : Points G.val.X R := s.inv.app R y
    let U : Over ((testSpec k).obj (op R)) := Over.mk (𝟙 _)
    have hc := congrArg (fun e : RelativeAut G.val ((testSpec k).obj (op R)) =>
      (e.asIso.hom.app (op U)).hom z) h
    change ((𝟙 _) ≫ x) * z * ((𝟙 _) ≫ x)⁻¹ = z at hc
    rw [Category.id_comp, mul_inv_eq_iff_eq_mul] at hc
    let m := SpecialLinearGroup.toGL.comp (s.hom.app R).hom
    have hm := congrArg m hc
    change m x * SpecialLinearGroup.toGL y = SpecialLinearGroup.toGL y * m x
    have hz : m z = SpecialLinearGroup.toGL y := congrArg SpecialLinearGroup.toGL
      ((s.app R).groupIsoToMulEquiv.apply_symm_apply y)
    simpa only [map_mul, hz] using hm
  · rintro ⟨a, ha⟩
    apply Aut.ext
    apply Iso.ext
    apply relativeHom_ext_affine
    intro S f z
    let b := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage f).unop
    have hb : (testSpec k).map b.op = f := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f
    change (f ≫ x) * z * (f ≫ x)⁻¹ = z
    rw [mul_inv_eq_iff_eq_mul, ← hb]
    apply (s.app S).groupIsoToMulEquiv.injective
    change s.hom.app S ((mapPoints b x) * z) = s.hom.app S (z * (mapPoints b x))
    have hmap : s.hom.app S (mapPoints b x) =
        SpecialLinearGroup.map b.hom.toRingHom (s.hom.app R x) := by
      exact NatTrans.naturality_apply s.hom b x
    change (s.hom.app S).hom (_ * _) = (s.hom.app S).hom (_ * _)
    rw [map_mul, map_mul, hmap]
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul]
    have hgl : SpecialLinearGroup.toGL (SpecialLinearGroup.map b.hom.toRingHom (s.hom.app R x)) =
        GeneralLinearGroup.map b.hom.toRingHom (SpecialLinearGroup.toGL (s.hom.app R x)) := Units.ext rfl
    rw [hgl, ha, GeneralLinearGroup.map_scalar]
    exact GeneralLinearGroup.scalar_commute _ _

private theorem section_ext_affine {U X : SchemeOver k} (x y : U ⟶ X)
    (h : ∀ (R : TestAlgebra k) (a : (testSpec k).obj (op R) ⟶ U), a ≫ x = a ≫ y) : x = y := by
  apply Over.OverMorphism.ext
  let C := U.left.affineCover
  apply C.hom_ext
  intro i
  let W : SchemeOver k := Over.mk (C.f i ≫ U.hom)
  let b : W ⟶ U := Over.homMk (C.f i)
  obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (show IsAffine W.left from Scheme.isAffine_affineCover _ _)
  have eq := congrArg (fun p => p.left) (h R.unop (e.hom ≫ b))
  change (e.hom.left ≫ C.f i) ≫ x.left = (e.hom.left ≫ C.f i) ≫ y.left at eq
  letI : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  simpa only [Category.assoc, cancel_epi] using eq

private noncomputable abbrev slProjective := matrixInclusion s P ≫ P.projection

private theorem slProjective_lift (hn : 0 < n) (R : TestAlgebra k) (g : Points P.linearGroup.X R) :
    ∃ (S : TestAlgebra k) (b : R ⟶ S) (x : Points G.val.X S),
      IsFppf ((testSpec k).map b.op).left ∧
      x ≫ (slProjective s P).hom.hom = mapPoints b (g ≫ P.projection.hom.hom) ∧
      ∃ c : Sˣ, SpecialLinearGroup.toGL (s.hom.app S x) =
        (GeneralLinearGroup.scalar _ c)⁻¹ *
          GeneralLinearGroup.map b.hom.toRingHom (P.linearPoints.hom.app R g) := by
  let A : GL (Index.{u} n) R := P.linearPoints.hom.app R g
  obtain ⟨S, b, c, hb, hc⟩ := fppfRoot R hn (GeneralLinearGroup.det A)
  let B := GeneralLinearGroup.map b.hom.toRingHom A
  let C := GeneralLinearGroup.scalar (Index.{u} n) c
  have hC : GeneralLinearGroup.det C = GeneralLinearGroup.det B := by
    rw [GeneralLinearGroup.det_scalar, Fintype.card_ulift, Fintype.card_fin, hc]
    exact (GeneralLinearGroup.map_det b.hom.toRingHom A).symm
  let w : (GeneralLinearGroup.det : GL (Index.{u} n) S →* Sˣ).ker :=
    ⟨C⁻¹ * B, by simp [hC]⟩
  let v : SpecialLinearGroup (Index.{u} n) S := SpecialLinearGroup.toGLKerEquiv.symm w
  have hv : SpecialLinearGroup.toGL v = C⁻¹ * B :=
    congrArg Subtype.val (SpecialLinearGroup.toGLKerEquiv.apply_symm_apply w)
  refine ⟨S, b, s.inv.app S v, hb, ?_, c, ?_⟩
  · have hbmap : P.linearPoints.hom.app S (mapPoints b g) = B :=
      NatTrans.naturality_apply P.linearPoints.hom b g
    have hscalar : matrixProjection P S C = 1 :=
      (matrixProjection_eq_one_iff S P C).2 ⟨c, rfl⟩
    change ((s.inv.app S v) ≫ (matrixInclusion s P).hom.hom) ≫ P.projection.hom.hom =
      (mapPoints b g) ≫ P.projection.hom.hom
    rw [matrixInclusion_apply, show s.hom.app S (s.inv.app S v) = v from
      (s.app S).groupIsoToMulEquiv.apply_symm_apply v, hv]
    have hbinv : P.linearPoints.inv.app S B = mapPoints b g := by
      rw [← hbmap]
      exact (P.linearPoints.app S).groupIsoToMulEquiv.symm_apply_apply _
    rw [← hbinv, ← matrixProjection_apply, ← matrixProjection_apply, map_mul, map_inv,
      hscalar, inv_one, one_mul]
  · rw [show s.hom.app S (s.inv.app S v) = v from
      (s.app S).groupIsoToMulEquiv.apply_symm_apply v, hv]

private theorem slProjective_locallySurjective (hn : 0 < n) :
    Presheaf.IsLocallySurjective (schemeTopology k) (groupSectionsMap (slProjective s P)) := by
  let q := groupSectionsMap (slProjective s P)
  let p := groupSectionsMap P.projection
  have hP : IsFppf P.projection.hom.hom.left := by
    have he := congrArg (fun f => f.left) P.projectionFormula
    rw [← he]
    letI : Flat P.presentation.projection.left := P.presentation.flat
    letI : Surjective P.presentation.projection.left := P.presentation.surjective
    letI : LocallyOfFinitePresentation P.presentation.projection.left := P.presentation.finitePresentation
    letI : IsIso P.comparison.hom.left := ((Over.forget _).mapIso P.comparison).isIso_hom
    change IsFppf (P.presentation.projection.left ≫ P.comparison.hom.left)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  letI := groupSectionsMap_locallySurjective P.projection hP
  constructor
  intro U y
  let J := schemeTopology k
  let T := Presheaf.imageSieve q y
  refine J.transitive (Presheaf.imageSieve_mem J p y) T ?_
  rintro V a ⟨g, hg⟩
  apply covering_of_affine_tests
  intro R b
  obtain ⟨S, f, x, hf, hx, _⟩ := slProjective_lift s P hn R (b ≫ g.down)
  apply fppf_mem ((testSpec k).map f.op) hf
  refine ⟨⟨x⟩, ULift.ext ?_⟩
  have hg' : g.down ≫ P.projection.hom.hom = a ≫ y.down := congrArg ULift.down hg
  let z : V ⟶ P.linearGroup.X := g.down
  let w : U ⟶ P.projectiveGroup.val.X := y.down
  change z ≫ P.projection.hom.hom = a ≫ w at hg'
  change x ≫ (slProjective s P).hom.hom =
    mapPoints f ((b ≫ z) ≫ P.projection.hom.hom) at hx
  change x ≫ (slProjective s P).hom.hom =
    (((testSpec k).map f.op ≫ b) ≫ a) ≫ w
  rw [hx, Category.assoc b, hg']
  simp only [mapPoints, Category.assoc]

private theorem projectiveAdjoint_kernel (hn : 0 < n) (Q : AdjointQuotient G)
    (U : SchemeOver k) (x : U ⟶ G.val.X) :
    x ≫ Q.projection.hom.hom = 1 ↔ x ≫ (slProjective s P).hom.hom = 1 := by
  have affine (R : TestAlgebra k) (z : Points G.val.X R) :
      z ≫ Q.projection.hom.hom = 1 ↔ z ≫ (slProjective s P).hom.hom = 1 := by
    rw [projection_eq_one_iff, matrix_central_iff s hn]
    change _ ↔ (z ≫ (matrixInclusion s P).hom.hom) ≫ P.projection.hom.hom = 1
    rw [matrixInclusion_apply, ← matrixProjection_apply, matrixProjection_eq_one_iff]
  constructor
  · intro h
    apply section_ext_affine
    intro R a
    rw [MonObj.comp_one, ← Category.assoc]
    exact (affine R (a ≫ x)).1 (by rw [Category.assoc, h, MonObj.comp_one])
  · intro h
    apply section_ext_affine
    intro R a
    rw [MonObj.comp_one, ← Category.assoc]
    exact (affine R (a ≫ x)).2 (by rw [Category.assoc, h, MonObj.comp_one])

private theorem projectiveAdjoint_iso (hn : 0 < n) (Q : AdjointQuotient G) :
    ∃ e : Q.quotient.val ≅ P.projectiveGroup.val, Q.projection ≫ e.hom = slProjective s P := by
  let p := groupSectionsMap Q.projection
  let q := groupSectionsMap (slProjective s P)
  have hp := groupSectionsMap_locallySurjective Q.projection Q.fppf
  have hq := slProjective_locallySurjective s P hn
  have agrees (U : (SchemeOver k)ᵒᵖ) (x y : (groupSections G.val).obj U) :
      p.app U x = p.app U y ↔ q.app U (((Iso.refl (groupSections G.val)).hom.app U) x) =
        q.app U (((Iso.refl (groupSections G.val)).hom.app U) y) := by
    simp only [Iso.refl_hom, NatTrans.id_app, GrpCat.id_apply]
    change p.app U x = p.app U y ↔ q.app U x = q.app U y
    rw [← div_eq_one (a := p.app U x), ← div_eq_one (a := q.app U x), ← map_div, ← map_div]
    change ULift.up ((x / y).down ≫ Q.projection.hom.hom) = ULift.up 1 ↔
      ULift.up ((x / y).down ≫ (slProjective s P).hom.hom) = ULift.up 1
    simp only [ULift.up_inj, projectiveAdjoint_kernel s P hn Q]
  obtain ⟨a, ha⟩ := descends_iso_of_locallySurjective p q (Iso.refl _) hp hq
    (groupSections_isSheaf Q.quotient.val) (groupSections_isSheaf P.projectiveGroup.val) agrees
  let ff := groupSectionsFullyFaithful (k := k)
  let e : Q.quotient.val ≅ P.projectiveGroup.val := ff.preimageIso a
  refine ⟨e, ff.map_injective ?_⟩
  change groupSectionsMap (Q.projection ≫ e.hom) = q
  rw [show groupSectionsMap (Q.projection ≫ e.hom) = p ≫ groupSectionsMap e.hom from
    (yonedaGrp ⋙ (Functor.whiskeringRight _ _ _).obj Fppf.liftGroups.{u,u+1}).map_comp _ _,
    show groupSectionsMap e.hom = a.hom from ff.map_preimage _]
  simpa only [Iso.refl_hom, Category.id_comp] using ha

theorem projectiveAdjoint : ProjectiveAdjoint.{u} := by
  intro k _ n hn G s P Q
  obtain ⟨e, he⟩ := projectiveAdjoint_iso s P hn Q
  refine ⟨e, fun R x => ?_⟩
  have hx : Q.projection.hom.hom ≫ e.hom.hom.hom =
      (slProjective s P).hom.hom := congrArg (fun f => f.hom.hom) he
  rw [hx]
  change (x ≫ (matrixInclusion s P).hom.hom) ≫ P.projection.hom.hom = _
  rw [matrixInclusion_apply]

end Projective

section FieldAutomorphisms

open AutomorphismSequence Fppf GeneralLinearStructure
open Descent.MatrixAlgebraForms
open Specs.Unipotent (Index)
open Pinning (AttachedDatum PinnedGroup BasedRootDatum)
open Matrix

open private matrixProjection matrixProjection_surjective matrixProjection_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.MatrixAlgebraForms
open private relativeHom_ext_affine relativeEvaluate relativeEvaluate_naturality
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private affineGroupIso affineGroupIso_hom
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA

private noncomputable abbrev fieldTest (k : Type u) [Field k] :=
  (testSpec k).obj (op (CommAlgCat.of k k))

variable {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}
  (s : SpecialMatrixPoints G n)

private theorem restriction_evaluate {S T : SchemeOver k} (b : T ⟶ S)
    (f : RelativeAut G.val S) (x : T ⟶ G.val.X) :
    relativeEvaluate (restrictAut b f).asIso.hom (Over.mk (𝟙 T)) x =
      relativeEvaluate f.asIso.hom (Over.mk b) x := by
  let c : Over.mk ((𝟙 T) ≫ b) ⟶ Over.mk b := Over.homMk (𝟙 T) rfl
  have h := relativeEvaluate_naturality f.asIso.hom c x
  change relativeEvaluate f.asIso.hom (Over.mk ((𝟙 T) ≫ b)) ((𝟙 T) ≫ x) =
    (𝟙 T) ≫ relativeEvaluate f.asIso.hom (Over.mk b) x at h
  rw [Category.id_comp, Category.id_comp] at h
  exact h

private theorem linearPoints_field (P : ProjectivePresentation k n) (R : TestAlgebra k)
    (a : (testSpec k).obj (op R) ⟶ fieldTest k) (g : GL (Index.{u} n) k) :
    P.linearPoints.hom.app R (a ≫ P.linearPoints.inv.app (CommAlgCat.of k k) g) =
      GeneralLinearGroup.map (algebraMap k R) g := by
  let b := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage a).unop
  have hb : (testSpec k).map b.op = a := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage a
  have hmap : b.hom.toRingHom = algebraMap k R := by
    ext x
    exact b.hom.commutes x
  rw [← hb]
  change P.linearPoints.hom.app R (mapPoints b (P.linearPoints.inv.app (CommAlgCat.of k k) g)) = _
  have h := NatTrans.naturality_apply P.linearPoints.hom b
    (P.linearPoints.inv.app (CommAlgCat.of k k) g)
  change P.linearPoints.hom.app R (mapPoints b _) = GeneralLinearGroup.map b.hom.toRingHom
    (P.linearPoints.hom.app (CommAlgCat.of k k) (P.linearPoints.inv.app (CommAlgCat.of k k) g)) at h
  rwa [show P.linearPoints.hom.app (CommAlgCat.of k k) (P.linearPoints.inv.app (CommAlgCat.of k k) g) =
    g from (P.linearPoints.app (CommAlgCat.of k k)).groupIsoToMulEquiv.apply_symm_apply _, hmap] at h

private theorem scalar_cancel_conjugation {R : Type u} [CommRing R]
    (c : Rˣ) (A X : GL (Index.{u} n) R) :
    ((GeneralLinearGroup.scalar _ c)⁻¹ * A) * X * ((GeneralLinearGroup.scalar _ c)⁻¹ * A)⁻¹ =
      A * X * A⁻¹ := by
  let C := GeneralLinearGroup.scalar (Index.{u} n) c
  change (C⁻¹ * A) * X * (C⁻¹ * A)⁻¹ = _
  have h := (show Commute C (A * X * A⁻¹) from
    GeneralLinearGroup.scalar_commute c _).inv_left.eq
  rw [_root_.mul_inv_rev, inv_inv]
  calc
    _ = (C⁻¹ * (A * X * A⁻¹)) * C := by simp only [mul_assoc]
    _ = _ := by rw [h, mul_assoc, inv_mul_cancel, mul_one]

set_option maxHeartbeats 800000 in
private theorem fieldInner_matrix (hn : 0 < n) (P : ProjectivePresentation k n)
    {D : BasedRootDatum.{u}} {Q : AdjointQuotient G}
    (E : ExactSequence G Q (constantGroup (Aut D))) (e : Q.quotient.val ≅ P.projectiveGroup.val)
    (he : ∀ (R : TestAlgebra k) (x : Points G.val.X R),
      x ≫ Q.projection.hom.hom ≫ e.hom.hom.hom =
        x ≫ (slProjective s P).hom.hom)
    (q : fieldTest k ⟶ Q.quotient.val.X) (g : GL (Index.{u} n) k)
    (hq : q ≫ e.hom.hom.hom = matrixProjection P (CommAlgCat.of k k) g)
    (R : TestAlgebra k) (a : (testSpec k).obj (op R) ⟶ fieldTest k) (x : Points G.val.X R) :
    let A := GeneralLinearGroup.map (algebraMap k R) g
    let y := relativeEvaluate (E.inner.app (op (fieldTest k)) ⟨q⟩).asIso.hom (Over.mk a) x
    (s.hom.app R y).val = A.val * (s.hom.app R x).val * (A⁻¹).val := by
  let V := fieldTest k
  let p : V ⟶ P.linearGroup.X := P.linearPoints.inv.app (CommAlgCat.of k k) g
  let w := E.inner.app (op V) ⟨q⟩
  let y := relativeEvaluate w.asIso.hom (Over.mk a) x
  let A := GeneralLinearGroup.map (algebraMap k R) g
  obtain ⟨S, b, z, hb, hz, c, hc⟩ := slProjective_lift s P hn R (a ≫ p)
  let b' := (testSpec k).map b.op
  let a' := b' ≫ a
  have hq' : q ≫ e.hom.hom.hom = p ≫ P.projection.hom.hom :=
    hq.trans (matrixProjection_apply P (CommAlgCat.of k k) g)
  have hz' : z ≫ Q.projection.hom.hom = a' ≫ q := by
    haveI : IsIso e.hom.hom.hom :=
      ((CategoryTheory.Grp.forget (SchemeOver k)).mapIso e).isIso_hom
    apply (cancel_mono e.hom.hom.hom).mp
    rw [Category.assoc, he S z, hz]
    simp only [a', b', mapPoints, Category.assoc, hq']
  have hw : restrictAut a' w = innerAut z := by
    have h := NatTrans.naturality_apply E.inner a'.op (⟨q⟩ : (groupSections Q.quotient.val).obj (op V))
    change E.inner.app (op ((testSpec k).obj (op S))) ⟨a' ≫ q⟩ = restrictAut a' w at h
    rw [← h, ← hz', E.onLift]
  let m : Over.mk a' ⟶ Over.mk a := Over.homMk b' rfl
  have hy : mapPoints b y = z * mapPoints b x * z⁻¹ := by
    have h₁ := relativeEvaluate_naturality w.asIso.hom m x
    have h₂ := congrArg (fun f : RelativeAut G.val ((testSpec k).obj (op S)) =>
      relativeEvaluate f.asIso.hom (Over.mk (𝟙 _)) (mapPoints b x)) hw
    rw [restriction_evaluate] at h₂
    change relativeEvaluate w.asIso.hom (Over.mk a') (mapPoints b x) =
      ((𝟙 _) ≫ z) * mapPoints b x * ((𝟙 _) ≫ z)⁻¹ at h₂
    rw [Category.id_comp] at h₂
    exact h₁.symm.trans h₂
  have hf : Function.Injective b.hom :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom b.hom.toRingHom)).mp
      ⟨hb.1, hb.2.1⟩).injective
  have hc' : SpecialLinearGroup.toGL (s.hom.app S z) =
      (GeneralLinearGroup.scalar _ c)⁻¹ * (GeneralLinearGroup.map b.hom.toRingHom A) := by
    have hA : P.linearPoints.hom.app R (a ≫ p) = A := linearPoints_field P R a g
    rw [hA] at hc
    exact hc
  let F : GL (Index.{u} n) R →* GL (Index.{u} n) S := GeneralLinearGroup.map b.hom.toRingHom
  let mS : Points G.val.X S →* GL (Index.{u} n) S :=
    SpecialLinearGroup.toGL.comp (s.hom.app S).hom
  have hmap (v : Points G.val.X R) :
      mS (mapPoints b v) = F (SpecialLinearGroup.toGL (s.hom.app R v)) := by
    have h := NatTrans.naturality_apply s.hom b v
    change s.hom.app S (mapPoints b v) = SpecialLinearGroup.map b.hom.toRingHom (s.hom.app R v) at h
    exact (congrArg SpecialLinearGroup.toGL h).trans (Units.ext rfl)
  have hmat : F (SpecialLinearGroup.toGL (s.hom.app R y)) =
      F (A * SpecialLinearGroup.toGL (s.hom.app R x) * A⁻¹) := by
    rw [← hmap, hy, map_mul, map_mul, map_inv, hmap, map_mul F, map_mul F, map_inv F]
    change (SpecialLinearGroup.toGL (s.hom.app S z)) * _ *
      (SpecialLinearGroup.toGL (s.hom.app S z))⁻¹ = _
    rw [hc', scalar_cancel_conjugation]
  ext i j
  exact hf (congrArg (fun w' : GL (Index.{u} n) S => w'.val i j) hmat)

private theorem fieldDiagram_eq_one_iff {D : BasedRootDatum.{u}} {Q : AdjointQuotient G}
    (E : ExactSequence G Q (constantGroup (Aut D))) (f : Aut G.val) :
    fieldDiagram E f = 1 ↔ ∃ q : fieldTest k ⟶ Q.quotient.val.X,
      scalarAut f (fieldTest k) = E.inner.app (op (fieldTest k)) ⟨q⟩ := by
  let V := fieldTest k
  let a := scalarAut f V
  have h := E.exact (op V) a
  constructor
  · intro hf
    have h₀ : E.outer.app (op V) a = 1 := by
      apply ULift.ext
      apply LocallyConstant.ext
      intro z
      haveI : Subsingleton V.left := by change Subsingleton (PrimeSpectrum k); infer_instance
      change (E.outer.app (op V) a).down z = 1
      rw [Subsingleton.elim z (show V.left from IsLocalRing.closedPoint k)]
      exact hf
    obtain ⟨q, hq⟩ := h.mp h₀
    exact ⟨q.down, hq.symm⟩
  · rintro ⟨q, hq⟩
    have h₀ := h.mpr ⟨⟨q⟩, hq.symm⟩
    exact congrArg (fun z : (constantGroup (k := k) (Aut D)).obj (op V) =>
      z.down (IsLocalRing.closedPoint k)) h₀

set_option maxHeartbeats 800000 in
private theorem fieldDiagram_kernel (hn : 0 < n) (P : ProjectivePresentation k n)
    {D : BasedRootDatum.{u}} {Q : AdjointQuotient G}
    (E : ExactSequence G Q (constantGroup (Aut D))) (f : Aut G.val) :
    fieldDiagram E f = 1 ↔ ∃ g, MatrixFormula s f g 1 := by
  obtain ⟨e, he⟩ := projectiveAdjoint hn s P Q
  have he' (R : TestAlgebra k) (x : Points G.val.X R) :
      x ≫ Q.projection.hom.hom ≫ e.hom.hom.hom = x ≫ (slProjective s P).hom.hom := by
    rw [he R x]
    exact (congrArg (fun z => z ≫ P.projection.hom.hom) (matrixInclusion_apply s P R x)).symm
  rw [fieldDiagram_eq_one_iff]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨g, hg⟩ := matrixProjection_surjective P hn (q ≫ e.hom.hom.hom)
    refine ⟨g, fun R x => ?_⟩
    let a : (testSpec k).obj (op R) ⟶ fieldTest k :=
      (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k R)).op
    have H := fieldInner_matrix s hn P E e he' q g hg.symm R a x
    rw [← hq] at H
    simp only [eq_self, ite_true]
    exact H
  · rintro ⟨g, hg⟩
    let p : fieldTest k ⟶ P.projectiveGroup.val.X := matrixProjection P (CommAlgCat.of k k) g
    let q := p ≫ e.inv.hom.hom
    have hq : q ≫ e.hom.hom.hom = p := by
      let j := (CategoryTheory.Grp.forget (SchemeOver k)).mapIso e
      change (p ≫ j.inv) ≫ j.hom = p
      rw [Category.assoc, j.inv_hom_id]
      exact Category.comp_id p
    refine ⟨q, ?_⟩
    apply Aut.ext
    apply Iso.ext
    apply relativeHom_ext_affine
    intro R a x
    apply (s.app R).groupIsoToMulEquiv.injective
    apply Subtype.ext
    exact (by simpa only [eq_self, ite_true] using hg R x :
      (s.hom.app R (x ≫ f.asIso.hom.hom.hom)).val = _).trans
      (fieldInner_matrix s hn P E e he' q g hq R a x).symm

private theorem transposeInverse_scheme (hn : 3 ≤ n) :
    ∃ θ : Aut G.val,
      (∀ (R : TestAlgebra k) (x : Points G.val.X R),
        (s.hom.app R (x ≫ θ.asIso.hom.hom.hom)).val = ((s.hom.app R x)⁻¹).val.transpose) ∧
      ¬ ∃ g, MatrixFormula s θ g 1 := by
  obtain ⟨t, ht, hout⟩ := Descent.InnerTypeA.transposeInverseOuter k n hn
  let β := s ≪≫ t ≪≫ s.symm
  let θ := Aut.of (affineGroupIso G.property.1 G.property.1 β)
  have hθ (R : TestAlgebra k) (x : Points G.val.X R) :
      (s.hom.app R (x ≫ θ.asIso.hom.hom.hom)).val = ((s.hom.app R x)⁻¹).val.transpose := by
    have hh := congrArg (fun f => f.app R x) (affineGroupIso_hom G.property.1 G.property.1 β)
    change x ≫ θ.asIso.hom.hom.hom = s.inv.app R (t.hom.app R (s.hom.app R x)) at hh
    rw [hh, show s.hom.app R (s.inv.app R (t.hom.app R (s.hom.app R x))) = _ from
      (s.app R).groupIsoToMulEquiv.apply_symm_apply _]
    exact ht R _
  refine ⟨θ, hθ, ?_⟩
  rintro ⟨g, hg⟩
  let R := CommAlgCat.of k k
  obtain ⟨x, hx⟩ := hout k g
  let y := s.inv.app R x
  have hy : s.hom.app R y = x := (s.app R).groupIsoToMulEquiv.apply_symm_apply _
  have hf := hg R y
  have hmap : GeneralLinearGroup.map (algebraMap k R) g = g := Units.ext rfl
  change (s.hom.app R (y ≫ θ.asIso.hom.hom.hom)).val =
    (GeneralLinearGroup.map (algebraMap k R) g).val *
    (if (1 : DiagramParity) = 1 then (s.hom.app R y).val else ((s.hom.app R y)⁻¹).val.transpose) *
      ((GeneralLinearGroup.map (algebraMap k R) g)⁻¹).val at hf
  rw [hmap, hθ, hy] at hf
  exact hx ((ht R x).trans (by simpa only [eq_self, ite_true] using hf))

private theorem apply_mul_aut (f g : Aut G.val) (R : TestAlgebra k) (x : Points G.val.X R) :
    x ≫ (f * g).asIso.hom.hom.hom = (x ≫ g.asIso.hom.hom.hom) ≫ f.asIso.hom.hom.hom :=
  (Category.assoc _ _ _).symm

private theorem apply_aut_inv_cancel (f : Aut G.val) (R : TestAlgebra k) (x : Points G.val.X R) :
    (x ≫ (f⁻¹).asIso.hom.hom.hom) ≫ f.asIso.hom.hom.hom = x := by
  let j := (CategoryTheory.Grp.forget (SchemeOver k)).mapIso f.asIso
  change (x ≫ j.inv) ≫ j.hom = x
  rw [Category.assoc, j.inv_hom_id]
  exact Category.comp_id x

set_option maxHeartbeats 800000 in
theorem fieldMatrixAutomorphisms : FieldMatrixAutomorphisms.{u} := by
  intro k _ r hr G s
  obtain ⟨T, L, M, B, _, _, hpin, _⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum k r G s
  obtain ⟨A, U, _, _, pin, _⟩ := hpin
  let P : PinnedGroup A := ⟨B.pair, U, pin⟩
  obtain ⟨D, l, Q, E, _, _⟩ := Descent.AutomorphismSequence.automorphismSequence P
  obtain ⟨W⟩ := Descent.MatrixAlgebraForms.projectivePresentable k (n := r + 1) (by omega)
  let v := matrixVertices B D
  let p := basedChainMap v (matrixVertex_pairing B D)
  obtain ⟨b, hb⟩ := matrixVertex_basis B D
  have hp : Function.Injective p := basedChainMap_injective v (matrixVertex_pairing B D) b hb
  obtain ⟨θ, hθ, houter⟩ := transposeInverse_scheme s (by omega)
  let d := fieldDiagram E.toExactSequence
  have hk (f : Aut G.val) : d f = 1 ↔ ∃ g, MatrixFormula s f g 1 :=
    fieldDiagram_kernel s (by omega) W E.toExactSequence f
  have hd : d θ ≠ 1 := fun h => houter ((hk θ).1 h)
  have hrev : p (d θ) = chainReversal r :=
    (chain_eq_one_or_reversal hr _).resolve_left (fun h => hd (hp (h.trans (map_one p).symm)))
  have hsur : Function.Surjective p := by
    intro a
    rcases chain_eq_one_or_reversal hr a with rfl | rfl
    · exact ⟨1, map_one p⟩
    · exact ⟨d θ, hrev⟩
  let C : ChainIdentification D.toBased r :=
    { vertices := v
      cartan := matrixVertex_pairing B D
      symmetries := MulEquiv.ofBijective p ⟨hp, hsur⟩
      onRoots := fun f i => (basedChainMap_onRoots v (matrixVertex_pairing B D) f i).symm
      parity := chainParity hr
      reversal := by
        intro a ha
        have h : a = chainReversal r := Subtype.ext ha
        subst a
        exact ite_eq_right (reversal_ne_one hr) }
  let δ := C.parity.toMonoidHom.comp (C.symmetries.toMonoidHom.comp d)
  let odd : DiagramParity := Multiplicative.ofAdd 1
  have hθδ : δ θ = odd := C.reversal _ (congrArg Subtype.val hrev)
  have hone (f : Aut G.val) : δ f = 1 ↔ d f = 1 := by
    change C.parity (C.symmetries (d f)) = 1 ↔ d f = 1
    rw [← map_one C.parity, C.parity.injective.eq_iff, ← map_one C.symmetries,
      C.symmetries.injective.eq_iff]
  have hk' (f : Aut G.val) : δ f = 1 ↔ ∃ g, MatrixFormula s f g 1 := (hone f).trans (hk f)
  have hcases : ∀ z : DiagramParity, z = 1 ∨ z = odd := by decide
  refine ⟨T, L, M, B, A, U, pin, D, l, Q, E, C, fun _ => rfl, ?_, ?_⟩
  · intro f
    change ∃ g, MatrixFormula s f g (δ f)
    rcases hcases (δ f) with h | h
    · rw [h]
      exact (hk' f).1 h
    · have hkf : δ (f * θ⁻¹) = 1 := by rw [map_mul, map_inv, h, hθδ, mul_inv_cancel]
      obtain ⟨g, hg⟩ := (hk' _).1 hkf
      refine ⟨g, fun R x => ?_⟩
      have H := hg R (x ≫ θ.asIso.hom.hom.hom)
      change _ = _ * (if δ f = 1 then _ else _) * _
      simp only [h, show odd ≠ 1 by decide, ite_false]
      simp only [eq_self, ite_true, apply_mul_aut, hθ] at H
      have hcancel := apply_aut_inv_cancel θ⁻¹ R x
      rw [inv_inv] at hcancel
      rwa [hcancel] at H
  · intro f g a ha
    change δ f = a
    rcases hcases a with rfl | h
    · exact (hk' f).2 ⟨g, ha⟩
    · have heven : MatrixFormula s (f * θ⁻¹) g 1 := by
        intro R x
        have H := ha R (x ≫ (θ⁻¹).asIso.hom.hom.hom)
        have hcancel := apply_aut_inv_cancel θ R x
        have Hθ := hθ R (x ≫ (θ⁻¹).asIso.hom.hom.hom)
        rw [hcancel] at Hθ
        simp only [h, show odd ≠ 1 by decide, ite_false, ← Hθ] at H
        simpa only [eq_self, ite_true, apply_mul_aut] using H
      have hz := (hk' (f * θ⁻¹)).2 ⟨g, heven⟩
      rw [map_mul, map_inv, hθδ, mul_inv_eq_one] at hz
      exact hz.trans h.symm

end FieldAutomorphisms


section Descent

open _root_.LinearAlgebraicGroups.Descent
open AutomorphismSequence

open private exists_coordinate_model spectrumIsoEquiv descend_standard_iso extendedHom_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

theorem finiteMatrixSplitting : FiniteMatrixSplitting.{u} := by
  intro k _ n _ G _ H h
  obtain ⟨S, _, _, _, ⟨j⟩⟩ := h
  obtain ⟨A, hA, ⟨a⟩⟩ := exists_coordinate_model G
  obtain ⟨B, hB, ⟨b⟩⟩ := exists_coordinate_model H
  let comparisons (L : Type u) [Field L] [Algebra k L] :=
    (extendedGroupIso (k := k) L A ≪≫ (groupBaseChange k L).mapIso a,
      extendedGroupIso (k := k) L B ≪≫ (groupBaseChange k L).mapIso b)
  let i := (spectrumIsoEquiv _ _).symm ((comparisons S).1 ≪≫ j ≪≫ (comparisons S).2.symm)
  obtain ⟨L, v, _, _⟩ := Forms.finiteLevelIsomorphisms A B hA hB ⊥ i
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(comparisons L).1.symm ≪≫ spectrumIsoEquiv _ _ v ≪≫ (comparisons L).2⟩⟩

theorem equivariantComparisonDescends : EquivariantComparisonDescends.{u} := by
  intro k K _ _ _ _ _ P Q U i j e he
  let f := i.symm ≪≫ e.asIso ≪≫ j
  obtain ⟨b, hb⟩ := descend_standard_iso f (by
    intro σ y
    let x := i.inv.hom y
    have hx : i.hom.hom x = y := ConcreteCategory.congr_hom i.inv_hom_id y
    have hj (z : extendedHopf K U) : j.hom.hom (j.inv.hom z) = z :=
      ConcreteCategory.congr_hom j.inv_hom_id z
    have h := congrArg (fun z => j.hom.hom z) (he σ x)
    change j.hom.hom (e.asIso.hom.hom (i.inv.hom
      ((standardCoordinateAction Q).act σ (i.hom.hom x)))) =
      j.hom.hom (j.inv.hom ((standardCoordinateAction U).act σ
        (j.hom.hom (e.asIso.hom.hom x)))) at h
    rw [hx, hj] at h
    exact h)
  refine ⟨b, hb, fun b' hb' => ?_⟩
  apply Iso.ext
  apply extendedHom_injective (K := K)
  exact hb'.trans hb.symm

end Descent

section SemilinearPoints

open _root_.LinearAlgebraicGroups.Descent
open AutomorphismSequence GeneralLinearStructure
open Specs.Unipotent (Index baseChangedAlgebraicGroup)
open Matrix

open private exists_coordinate_model spectrumIsoEquiv spectrumAutEquiv act_inv_apply act_apply_inv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private extendedGroupIso extendedSpecIso_hom_fst from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private baseChangePointIso transposeInverse transposeInverse_not_conjugation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {G H : AffineAlgebraicGroup k} {n : ℕ}

private theorem trivialization_coordinates
    (i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val) :
    ∃ C : TrivializationCoordinates i, Algebra.FiniteType k C.split ∧ Algebra.FiniteType k C.form := by
  obtain ⟨P, hP, ⟨p⟩⟩ := exists_coordinate_model G
  obtain ⟨Q, hQ, ⟨q⟩⟩ := exists_coordinate_model H
  let t := extendedGroupIso (k := k) K
  let L := t P ≪≫ (groupBaseChange k K).mapIso p
  let R := t Q ≪≫ (groupBaseChange k K).mapIso q
  let e := spectrumIsoEquiv (extendedHopf K P) (extendedHopf K Q)
  let j := e.symm (L ≪≫ i ≪≫ R.symm)
  have hj : Forms.spectrumIso j = L ≪≫ i ≪≫ R.symm := e.apply_symm_apply _
  refine ⟨⟨P, Q, p, q, t, extendedSpecIso_hom_fst K, j, ?_⟩, hP, hQ⟩
  change i = L.symm ≪≫ Forms.spectrumIso j ≪≫ R
  simp [hj]

private noncomputable def extendMatrixPoints (s : SpecialMatrixPoints G n) :
    SpecialMatrixPoints (baseChangedAlgebraicGroup K G) n :=
  baseChangePointIso G.val ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k K) s ≪≫
    NatIso.ofComponents (fun R => (MulEquiv.refl (SpecialLinearGroup (Index.{u} n) R)).toGrpIso)
      (by intro R S f; apply GrpCat.ext; intro x; rfl)

private noncomputable abbrev groupIsoPoints {l : Type u} [Field l] {A B : GroupScheme l}
    (j : A ≅ B) (R : TestAlgebra l) :=
  (((groupPointsFunctor l).mapIso j).app R).groupIsoToMulEquiv

private noncomputable abbrev restrictCoordinate {P : HopfAlgebraCategory k} {R : TestAlgebra K}
    (p : extendedHopf K P →ₐ[K] R) : P →ₐ[k] (restrictTestAlgebra k K).obj R := by
  letI : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq' rfl
  exact (p.restrictScalars k).comp Algebra.TensorProduct.includeRight

private noncomputable abbrev standardTestChange {P : HopfAlgebraCategory k} {R S : TestAlgebra K}
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (p : extendedHopf K P →ₐ[K] R) : extendedHopf K P →ₐ[K] S := by
  letI : Algebra k S := ((algebraMap K S).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgHom.liftEquiv k K P S (b.hom.comp (restrictCoordinate p))

private theorem restrict_standardTestChange {P : HopfAlgebraCategory k} {R S : TestAlgebra K}
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (p : extendedHopf K P →ₐ[K] R) :
    restrictCoordinate (standardTestChange b p) = b.hom.comp (restrictCoordinate p) := by
  letI : Algebra k S := ((algebraMap K S).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  apply AlgHom.ext
  intro x
  change AlgHom.liftEquiv k K P S (b.hom.comp (restrictCoordinate p)) (1 ⊗ₜ[k] x) = _
  rw [AlgHom.liftEquiv_tmul, one_smul]

private theorem standardTestChange_eval {P : HopfAlgebraCategory k} {R S : TestAlgebra K}
    (σ : Gal(K/k)) (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (hb : IsSemilinearTestMap σ b) (p : extendedHopf K P →ₐ[K] R) (x : extendedHopf K P) :
    standardTestChange b p x = b.hom (p ((standardCoordinateAction P).act σ⁻¹ x)) := by
  letI : Algebra k S := ((algebraMap K S).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  induction x using TensorProduct.inductionOn with
  | tmul c y =>
    change (AlgHom.liftEquiv k K P S (b.hom.comp (restrictCoordinate p))) (c ⊗ₜ[k] y) =
      b.hom (p (σ⁻¹ c ⊗ₜ[k] y))
    rw [AlgHom.liftEquiv_tmul, AlgHom.comp_apply]
    change c • b.hom (p (1 ⊗ₜ[k] y)) = _
    have hp : p ((σ⁻¹ c) ⊗ₜ[k] y) = σ⁻¹ c • p (1 ⊗ₜ[k] y) := by
      have h := p.toLinearMap.map_smul (σ⁻¹ c) ((1 : K) ⊗ₜ[k] y)
      change p ((σ⁻¹ c • (1 : K)) ⊗ₜ[k] y) = σ⁻¹ c • p (1 ⊗ₜ[k] y) at h
      simpa only [smul_eq_mul, mul_one] using h
    rw [hp, Algebra.smul_def, Algebra.smul_def, map_mul, hb,
      show σ (σ⁻¹ c) = c from σ.apply_symm_apply c]
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add, map_add, map_add]

private noncomputable abbrev coordinatePoint {P : HopfAlgebraCategory k} {R : TestAlgebra K}
    (p : extendedHopf K P →ₐ[K] R) : Points (specGroup (extendedHopf K P)).X R :=
  (testSpec K).map (CommAlgCat.ofHom p).op

private theorem coordinatePoint_surjective (P : HopfAlgebraCategory k) (R : TestAlgebra K) :
    Function.Surjective (coordinatePoint (P := P) (R := R)) := by
  intro x
  let F := algSpec.fullyFaithful (R := CommRingCat.of K)
  exact ⟨(F.preimage x).unop.hom, F.map_preimage x⟩

private theorem coordinatePoint_comp {P Q : HopfAlgebraCategory k} {R : TestAlgebra K}
    (p : extendedHopf K P →ₐ[K] R) (e : extendedHopf K P ≅ extendedHopf K Q) :
    coordinatePoint (p.comp e.inv.hom.toAlgHom) = coordinatePoint p ≫ (Forms.spectrumIso e).hom.hom.hom := by
  change (testSpec K).map ((CommAlgCat.ofHom e.inv.hom.toAlgHom) ≫ CommAlgCat.ofHom p).op =
    (testSpec K).map (CommAlgCat.ofHom p).op ≫ (testSpec K).map (CommAlgCat.ofHom e.inv.hom.toAlgHom).op
  rw [op_comp, Functor.map_comp]

private noncomputable abbrev modelPoint {P : HopfAlgebraCategory k} {R : TestAlgebra K}
    {W : GroupScheme K} (u : specGroup (extendedHopf K P) ≅ W)
    (p : extendedHopf K P →ₐ[K] R) : Points W.X R :=
  groupIsoPoints u R (coordinatePoint p)

private theorem modelPoint_surjective {P : HopfAlgebraCategory k} {R : TestAlgebra K}
    {W : GroupScheme K} (u : specGroup (extendedHopf K P) ≅ W) :
    Function.Surjective (modelPoint (R := R) u) :=
  (groupIsoPoints u R).surjective.comp (coordinatePoint_surjective P R)

private theorem modelPoint_project {P : HopfAlgebraCategory k} {R : TestAlgebra K}
    {W : GroupScheme k} (p : extendedHopf K P →ₐ[K] R) (j : specGroup P ≅ W)
    (t : ∀ P : HopfAlgebraCategory k, specGroup (extendedHopf K P) ≅
      (groupBaseChange k K).obj (specGroup P)) (ht : Forms.IsScalarExtensionComparison t) :
    baseChangePoint k K W.X R (modelPoint (t P ≪≫ (groupBaseChange k K).mapIso j) p) =
      (testSpec k).map (CommAlgCat.ofHom (restrictCoordinate p)).op ≫ j.hom.hom.hom := by
  have h := baseChangePointsSchemeNaturality k K j.hom.hom.hom R
    (coordinatePoint p ≫ (t P).hom.hom.hom)
  change baseChangePoint k K W.X R ((coordinatePoint p ≫ (t P).hom.hom.hom) ≫
    ((groupBaseChange k K).map j.hom).hom.hom) = _ at h
  rw [Category.assoc] at h
  change baseChangePoint k K W.X R (coordinatePoint p ≫
    ((t P).hom.hom.hom ≫ ((groupBaseChange k K).map j.hom).hom.hom)) = _
  rw [h]
  congr 1
  apply Over.OverMorphism.ext
  change (Spec.map (CommRingCat.ofHom p.toRingHom) ≫ (t P).hom.hom.hom.left) ≫
    CategoryTheory.Limits.pullback.fst (specGroup P).X.hom (fieldSpecMap k K) = _
  rw [Category.assoc, ht P]
  exact (Spec.map_comp _ _).symm

private theorem modelPoint_standardTestChange {P : HopfAlgebraCategory k} {R S : TestAlgebra K}
    {W : GroupScheme k} (p : extendedHopf K P →ₐ[K] R) (j : specGroup P ≅ W)
    (t : ∀ P : HopfAlgebraCategory k, specGroup (extendedHopf K P) ≅
      (groupBaseChange k K).obj (specGroup P)) (ht : Forms.IsScalarExtensionComparison t)
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S) :
    let u := t P ≪≫ (groupBaseChange k K).mapIso j
    baseChangePoint k K W.X S (modelPoint u (standardTestChange b p)) =
      mapPoints b (baseChangePoint k K W.X R (modelPoint u p)) := by
  dsimp only
  rw [modelPoint_project _ _ _ ht, modelPoint_project _ _ _ ht, restrict_standardTestChange]
  change (testSpec k).map (CommAlgCat.ofHom (restrictCoordinate p) ≫ b).op ≫ j.hom.hom.hom =
    (testSpec k).map b.op ≫ (testSpec k).map (CommAlgCat.ofHom (restrictCoordinate p)).op ≫ j.hom.hom.hom
  rw [op_comp, Functor.map_comp, Category.assoc]

private theorem modelPoint_trivialization {R : TestAlgebra K}
    {i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val}
    (C : TrivializationCoordinates i) (p : extendedHopf K C.split →ₐ[K] R) :
    modelPoint C.splitComparison p ≫ i.hom.hom.hom =
      modelPoint C.formComparison (p.comp C.iso.inv.hom.toAlgHom) := by
  have h : C.splitComparison ≪≫ i = Forms.spectrumIso C.iso ≪≫ C.formComparison := by
    calc
      _ = C.splitComparison ≪≫ (C.splitComparison.symm ≪≫ Forms.spectrumIso C.iso ≪≫
          C.formComparison) := congrArg (fun j => C.splitComparison ≪≫ j) C.compatibility
      _ = _ := by simp
  change (coordinatePoint p ≫ C.splitComparison.hom.hom.hom) ≫ i.hom.hom.hom =
    coordinatePoint (p.comp C.iso.inv.hom.toAlgHom) ≫ C.formComparison.hom.hom.hom
  rw [coordinatePoint_comp, Category.assoc, Category.assoc]
  exact congrArg (fun j => coordinatePoint p ≫ j.hom.hom.hom) h

private theorem modelPoint_coefficient {R : TestAlgebra K}
    {i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val}
    (C : TrivializationCoordinates i) (p : extendedHopf K C.split →ₐ[K] R)
    (a : Aut (extendedHopf K C.split)) :
    modelPoint C.splitComparison p ≫ (C.schemeAut a).asIso.hom.hom.hom =
      modelPoint C.splitComparison (p.comp a.asIso.inv.hom.toAlgHom) := by
  have h : C.splitComparison ≪≫ (C.schemeAut a).asIso =
      Forms.spectrumIso a.asIso ≪≫ C.splitComparison := by
    simp [TrivializationCoordinates.schemeAut]
  change (coordinatePoint p ≫ C.splitComparison.hom.hom.hom) ≫ (C.schemeAut a).asIso.hom.hom.hom =
    coordinatePoint (p.comp a.asIso.inv.hom.toAlgHom) ≫ C.splitComparison.hom.hom.hom
  rw [coordinatePoint_comp, Category.assoc, Category.assoc]
  exact congrArg (fun j => coordinatePoint p ≫ j.hom.hom.hom) h

private noncomputable def standardPointChange {R S : TestAlgebra K} (W : GroupScheme k)
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (x : Points ((groupBaseChange k K).obj W).X R) :
    Points ((groupBaseChange k K).obj W).X S :=
  (baseChangePointGroupEquiv K W S).symm (mapPoints b (baseChangePoint k K W.X R x))

private theorem standardPointChange_project {R S : TestAlgebra K} (W : GroupScheme k)
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (x : Points ((groupBaseChange k K).obj W).X R) :
    baseChangePoint k K W.X S (standardPointChange W b x) =
      mapPoints b (baseChangePoint k K W.X R x) :=
  (baseChangePointGroupEquiv K W S).apply_symm_apply _

private theorem standardPointChange_modelPoint {P : HopfAlgebraCategory k} {R S : TestAlgebra K}
    {W : GroupScheme k} (p : extendedHopf K P →ₐ[K] R) (j : specGroup P ≅ W)
    (t : ∀ P : HopfAlgebraCategory k, specGroup (extendedHopf K P) ≅
      (groupBaseChange k K).obj (specGroup P)) (ht : Forms.IsScalarExtensionComparison t)
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S) :
    let u := t P ≪≫ (groupBaseChange k K).mapIso j
    standardPointChange W b (modelPoint u p) = modelPoint u (standardTestChange b p) := by
  dsimp only
  apply (baseChangePointGroupEquiv K W S).injective
  exact (standardPointChange_project W b _).trans (modelPoint_standardTestChange p j t ht b).symm

private theorem standardPointChange_matrix {R S : TestAlgebra K} (s : SpecialMatrixPoints G n)
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (x : Points ((groupBaseChange k K).obj G.val).X R) :
    baseChangeMatrix s S (standardPointChange G.val b x) =
      SpecialLinearGroup.map b.hom.toRingHom (baseChangeMatrix s R x) := by
  unfold baseChangeMatrix
  rw [standardPointChange_project]
  exact NatTrans.naturality_apply s.hom b (baseChangePoint k K G.val.X R x)

private theorem transportedPoint_unique {R S : TestAlgebra K}
    (i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val)
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (x : Points ((groupBaseChange k K).obj G.val).X R) :
    ∃! y, IsTransportedPoint i b x y := by
  let e := (groupIsoPoints i S).trans (baseChangePointGroupEquiv K H.val S)
  let z := mapPoints b (baseChangePoint k K H.val.X R (x ≫ i.hom.hom.hom))
  exact ⟨e.symm z, e.apply_symm_apply _, fun y h => e.injective (h.trans (e.apply_symm_apply _).symm)⟩

private theorem coefficient_cocycle_testChange {R S : TestAlgebra K}
    {i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val}
    (C : TrivializationCoordinates i) (σ : Gal(K/k))
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (hb : IsSemilinearTestMap σ b)
    (a : Aut (extendedHopf K C.split))
    (ha : ∀ x, a.asIso.hom.hom ((standardCoordinateAction C.split).act σ x) =
      transportedCoordinateAction C.iso σ x)
    (p : extendedHopf K C.split →ₐ[K] R) :
    (((standardTestChange b p).comp a.asIso.inv.hom.toAlgHom).comp C.iso.inv.hom.toAlgHom) =
      standardTestChange b (p.comp C.iso.inv.hom.toAlgHom) := by
  apply AlgHom.ext
  intro x
  simp only [AlgHom.comp_apply, standardTestChange_eval σ b hb]
  let w := (standardCoordinateAction C.form).act σ⁻¹ x
  have h := ha (C.iso.inv.hom w)
  have hw : C.iso.hom.hom (C.iso.inv.hom w) = w := ConcreteCategory.congr_hom C.iso.inv_hom_id w
  change a.asIso.hom.hom ((standardCoordinateAction C.split).act σ (C.iso.inv.hom w)) =
    C.iso.inv.hom ((standardCoordinateAction C.form).act σ (C.iso.hom.hom (C.iso.inv.hom w))) at h
  rw [hw, show (standardCoordinateAction C.form).act σ w = x from act_apply_inv _ σ x] at h
  have h' := congrArg (fun y => (standardCoordinateAction C.split).act σ⁻¹ (a.asIso.inv.hom y)) h
  have hcancel (y : extendedHopf K C.split) : a.asIso.inv.hom (a.asIso.hom.hom y) = y :=
    ConcreteCategory.congr_hom a.asIso.hom_inv_id y
  dsimp only at h'
  rw [hcancel] at h'
  have hInv : (standardCoordinateAction C.split).act σ⁻¹
      ((standardCoordinateAction C.split).act σ (C.iso.inv.hom w)) = C.iso.inv.hom w :=
    act_inv_apply (standardCoordinateAction C.split) σ (C.iso.inv.hom w)
  exact congrArg (fun y => b.hom (p y)) (h'.symm.trans hInv)

private theorem transportedPoint_coefficient {R S : TestAlgebra K}
    {i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val}
    (C : TrivializationCoordinates i) (σ : Gal(K/k))
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (hb : IsSemilinearTestMap σ b) (a : Aut (extendedHopf K C.split))
    (ha : ∀ z, a.asIso.hom.hom ((standardCoordinateAction C.split).act σ z) =
      transportedCoordinateAction C.iso σ z)
    (x : Points ((groupBaseChange k K).obj G.val).X R) :
    IsTransportedPoint i b x (standardPointChange G.val b x ≫ (C.schemeAut a).asIso.hom.hom.hom) := by
  obtain ⟨p, rfl⟩ := modelPoint_surjective C.splitComparison x
  unfold IsTransportedPoint
  rw [standardPointChange_modelPoint p C.splitModel C.extension C.extensionProjection,
    modelPoint_coefficient, modelPoint_trivialization, modelPoint_trivialization,
    coefficient_cocycle_testChange C σ b hb a ha]
  exact modelPoint_standardTestChange _ C.formModel C.extension C.extensionProjection b

private theorem standardPointChange_coefficient {R S : TestAlgebra K}
    {i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val}
    (C : TrivializationCoordinates i) (ρ : Gal(K/k) →* MulAut (Aut (extendedHopf K C.split)))
    (hρ : Forms.IsStandardAction ρ) (σ : Gal(K/k))
    (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
    (hb : IsSemilinearTestMap σ b) (a : Aut (extendedHopf K C.split))
    (x : Points ((groupBaseChange k K).obj G.val).X R) :
    standardPointChange G.val b (x ≫ (C.schemeAut a).asIso.hom.hom.hom) =
      standardPointChange G.val b x ≫ (C.schemeAut (ρ σ a)).asIso.hom.hom.hom := by
  obtain ⟨p, rfl⟩ := modelPoint_surjective C.splitComparison x
  rw [modelPoint_coefficient, standardPointChange_modelPoint _ C.splitModel C.extension C.extensionProjection,
    standardPointChange_modelPoint _ C.splitModel C.extension C.extensionProjection, modelPoint_coefficient]
  congr 1
  apply AlgHom.ext
  intro z
  simp only [AlgHom.comp_apply, standardTestChange_eval σ b hb]
  let D : SemilinearAction k K (extendedHopf K C.split) := standardCoordinateAction C.split
  let v : extendedHopf K C.split := D.act σ⁻¹ z
  have hv : D.act σ v = z := act_apply_inv D σ z
  have h := hρ σ a⁻¹ v
  change (ρ σ a⁻¹).asIso.hom.hom (D.act σ v) = D.act σ (a.asIso.inv.hom v) at h
  rw [hv, map_inv] at h
  have h' := congrArg (D.act σ⁻¹) h
  exact congrArg (fun y => b.hom (p y))
    (h'.trans (act_inv_apply D σ (a.asIso.inv.hom v))).symm

private theorem fieldSemilinearMap_semilinear (σ : Gal(K/k)) :
    IsSemilinearTestMap σ (fieldSemilinearMap σ) := fun _ => rfl

private noncomputable def restrictedFieldAut : Gal(K/k) →*
    Aut ((restrictTestAlgebra k K).obj (CommAlgCat.of K K)) where
  toFun σ := Aut.of
    { hom := fieldSemilinearMap σ
      inv := fieldSemilinearMap σ⁻¹
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        exact σ.symm_apply_apply x
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro x
        exact σ.apply_symm_apply x }
  map_one' := Aut.ext (Iso.ext (ConcreteCategory.hom_ext _ _ (fun _ => rfl)))
  map_mul' _ _ := Aut.ext (Iso.ext (ConcreteCategory.hom_ext _ _ (fun _ => rfl)))

private noncomputable def fieldPointAction (W : GroupScheme k) : Gal(K/k) →*
    MulAut (Points W.X ((restrictTestAlgebra k K).obj (CommAlgCat.of K K))) :=
  let F := (groupPointsFunctor k).obj W
  let V := (restrictTestAlgebra k K).obj (CommAlgCat.of K K)
  let M : Aut (F.obj V) →* MulAut (F.obj V) :=
    { toFun := fun f => f.asIso.groupIsoToMulEquiv
      map_one' := MulEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => MulEquiv.ext fun _ => rfl }
  M.comp ((F.mapAut V).comp restrictedFieldAut)

private theorem fieldPointAction_apply (W : GroupScheme k) (σ : Gal(K/k))
    (x : Points W.X ((restrictTestAlgebra k K).obj (CommAlgCat.of K K))) :
    fieldPointAction W σ x = mapPoints (fieldSemilinearMap σ) x := rfl

private theorem map_inverse_transpose {I R S : Type u} [Fintype I] [DecidableEq I]
    [CommRing R] [CommRing S] (b : R →+* S) (x : SpecialLinearGroup I R) :
    ((SpecialLinearGroup.map b x)⁻¹).val.transpose = (x⁻¹).val.transpose.map b := by
  rw [← map_inv]
  rfl

private theorem field_formula_parity {n : ℕ} (hn : 3 ≤ n)
    (A B : GL (Index.{u} n) K) (p q : DiagramParity)
    (h : ∀ x : SpecialLinearGroup (Index.{u} n) K,
      A.val * (if p = 1 then x.val else (x⁻¹).val.transpose) * A⁻¹.val =
      B.val * (if q = 1 then x.val else (x⁻¹).val.transpose) * B⁻¹.val) : p = q := by
  have hn' : 3 ≤ Fintype.card (Index.{u} n) := by simpa using hn
  have distinguish (C D : GL (Index.{u} n) K)
      (hc : ∀ x : SpecialLinearGroup (Index.{u} n) K,
        C.val * x.val * C⁻¹.val = D.val * (x⁻¹).val.transpose * D⁻¹.val) : False := by
    obtain ⟨x, hx⟩ := transposeInverse_not_conjugation hn' (D⁻¹ * C)
    let X := SpecialLinearGroup.toGL x
    let Y := SpecialLinearGroup.toGL (transposeInverse x)
    have e : C * X * C⁻¹ = D * Y * D⁻¹ := Units.ext (hc x)
    have e' : Y = (D⁻¹ * C) * X * (D⁻¹ * C)⁻¹ := calc
      Y = D⁻¹ * (D * Y * D⁻¹) * D := by group
      _ = D⁻¹ * (C * X * C⁻¹) * D := congrArg (fun w => D⁻¹ * w * D) e.symm
      _ = (D⁻¹ * C) * X * (D⁻¹ * C)⁻¹ := by group
    exact hx (congrArg Units.val e')
  let odd : DiagramParity := Multiplicative.ofAdd 1
  have hcases : ∀ a : DiagramParity, a = 1 ∨ a = odd := by decide
  have ho : odd ≠ 1 := by decide
  rcases hcases p with rfl | rfl <;> rcases hcases q with rfl | rfl
  · rfl
  · exact (distinguish A B (fun x => by simpa only [eq_self, ite_true, ho, ite_false] using h x)).elim
  · exact (distinguish B A (fun x => by simpa only [eq_self, ite_true, ho, ite_false] using (h x).symm)).elim
  · rfl

private theorem matrixFormula_field {W : AffineAlgebraicGroup K} (m : SpecialMatrixPoints W n)
    {f : Aut W.val} {A : GL (Index.{u} n) K} {p : DiagramParity} (h : MatrixFormula m f A p)
    (x : Points W.val.X (CommAlgCat.of K K)) :
    let R := CommAlgCat.of K K
    (m.hom.app R (x ≫ f.asIso.hom.hom.hom)).val =
      A.val * (if p = 1 then (m.hom.app R x).val else ((m.hom.app R x)⁻¹).val.transpose) * A⁻¹.val := by
  let R := CommAlgCat.of K K
  have hA : GeneralLinearGroup.map (algebraMap K R) A = A := Units.ext rfl
  have hh := h R x
  dsimp only at hh ⊢
  rwa [hA] at hh

set_option maxHeartbeats 800000 in
private theorem coefficient_parity_invariant (hn : 3 ≤ n)
    (s : SpecialMatrixPoints G n) (m : SpecialMatrixPoints (baseChangedAlgebraicGroup K G) n)
    (hm : ∀ R x, m.hom.app R x = baseChangeMatrix s R x)
    {i : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val}
    (C : TrivializationCoordinates i) (ρ : Gal(K/k) →* MulAut (Aut (extendedHopf K C.split)))
    (hρ : Forms.IsStandardAction ρ) (σ : Gal(K/k)) (a : Aut (extendedHopf K C.split))
    (δ : Aut ((groupBaseChange k K).obj G.val) →* DiagramParity)
    (formulas : ∀ f, ∃ A, MatrixFormula m f A (δ f)) : δ (C.schemeAut (ρ σ a)) = δ (C.schemeAut a) := by
  obtain ⟨A, hA⟩ := formulas (C.schemeAut a)
  obtain ⟨B, hB⟩ := formulas (C.schemeAut (ρ σ a))
  let R := CommAlgCat.of K K
  let b := fieldSemilinearMap σ
  let F := σ.toRingHom
  let A' := GeneralLinearGroup.map F A
  apply Eq.symm
  apply field_formula_parity hn A' B
  intro X
  let x : Points ((groupBaseChange k K).obj G.val).X R :=
    (m.app R).groupIsoToMulEquiv.symm (SpecialLinearGroup.map σ⁻¹.toRingHom X)
  let y := standardPointChange G.val b x
  have hx : m.hom.app R x = SpecialLinearGroup.map σ⁻¹.toRingHom X :=
    (m.app R).groupIsoToMulEquiv.apply_symm_apply _
  have hstd (z : Points ((groupBaseChange k K).obj G.val).X R) :
      m.hom.app R (standardPointChange G.val b z) = SpecialLinearGroup.map F (m.hom.app R z) := by
    simp only [hm]
    exact standardPointChange_matrix s b z
  have hy : m.hom.app R y = X := by
    change m.hom.app R (standardPointChange G.val b x) = _
    rw [hstd, hx]
    exact Subtype.ext (Matrix.ext fun u v => σ.apply_symm_apply (X.val u v))
  have hs := standardPointChange_coefficient C ρ hρ σ b (fieldSemilinearMap_semilinear σ) a x
  have h := congrArg (fun z : Points ((groupBaseChange k K).obj G.val).X R => (m.hom.app R z).val) hs
  change (m.hom.app R (standardPointChange G.val b (x ≫ (C.schemeAut a).asIso.hom.hom.hom))).val =
    (m.hom.app R (y ≫ (C.schemeAut (ρ σ a)).asIso.hom.hom.hom)).val at h
  rw [hstd] at h
  change (m.hom.app R (x ≫ (C.schemeAut a).asIso.hom.hom.hom)).val.map F = _ at h
  rw [matrixFormula_field m hA x, matrixFormula_field m hB y, hy, Matrix.map_mul, Matrix.map_mul] at h
  have iv : ((m.hom.app R x)⁻¹).val.transpose.map F = (X⁻¹).val.transpose := by
    rw [← map_inverse_transpose, ← hstd x]
    exact congrArg (fun z : SpecialLinearGroup (Index.{u} n) K => (z⁻¹).val.transpose) hy
  have vl : (m.hom.app R x).val.map F = X.val := by
    exact congrArg Subtype.val ((hstd x).symm.trans hy)
  have hf : (A'⁻¹).val = (A⁻¹).val.map F := by rw [← map_inv]; rfl
  change A'.val * _ * (A'⁻¹).val = _
  rw [hf]
  by_cases hp : δ (C.schemeAut a) = 1
  · rw [ite_eq_left hp] at h ⊢
    change A'.val * ((m.hom.app R x).val.map F) * (A⁻¹).val.map F = _ at h
    rwa [vl] at h
  · rw [ite_eq_right hp] at h ⊢
    change A'.val * (((m.hom.app R x)⁻¹).val.transpose.map F) * (A⁻¹).val.map F = _ at h
    rwa [iv] at h

private theorem matrix_diagram_exists {l : Type u} [Field l] {W : AffineAlgebraicGroup l}
    {n : ℕ} (hn : 3 ≤ n) (m : SpecialMatrixPoints W n) :
    ∃ δ : Aut W.val →* DiagramParity,
      (∀ f, ∃ A, MatrixFormula m f A (δ f)) ∧ (∀ f A p, MatrixFormula m f A p → δ f = p) := by
  cases n with
  | zero => omega
  | succ r =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, E, C, _, h, h'⟩ := fieldMatrixAutomorphisms (by omega) m
    exact ⟨C.parity.toMonoidHom.comp (C.symmetries.toMonoidHom.comp (fieldDiagram E.toExactSequence)), h, h'⟩

set_option maxHeartbeats 900000 in
theorem matrixDescentForTrivialization : MatrixDescentForTrivialization.{u} := by
  intro k K _ _ _ _ _ n hn G H s i
  obtain ⟨C, hP, hQ⟩ := trivialization_coordinates i
  letI : TopologicalSpace (Aut (extendedHopf K C.split)) := ⊥
  letI : TopologicalSpace (Gal(K/k)) := krullTopology k K
  obtain ⟨ρ, _, hρ, _, _, hclass, _⟩ := Forms.finiteForms (K := K) C.split hP
  let Q : Forms.Models K C.split := ⟨C.form, hQ, ⟨C.iso⟩⟩
  obtain ⟨a, ha, _⟩ := hclass Q C.iso
  let m := extendMatrixPoints (K := K) s
  have hm (R : TestAlgebra K) (x : Points ((groupBaseChange k K).obj G.val).X R) :
      m.hom.app R x = baseChangeMatrix s R x := rfl
  obtain ⟨δ, hformula, hdetect⟩ := matrix_diagram_exists hn m
  let c := (spectrumAutEquiv (extendedHopf K C.split)).trans C.splitComparison.conjAut
  have hc (d : Aut (extendedHopf K C.split)) : c d = C.schemeAut d := rfl
  have hinv (σ : Gal(K/k)) (d : Aut (extendedHopf K C.split)) :
      δ (c (ρ σ d)) = δ (c d) := by
    simp only [hc]
    exact coefficient_parity_invariant hn s m hm C ρ hρ σ d δ hformula
  let χ : Gal(K/k) →* DiagramParity :=
    { toFun := fun σ => δ (c (a σ))
      map_one' := by
        have h := a.property.2 1 1
        rw [one_mul, map_one, MulAut.one_apply] at h
        have hz : a 1 = 1 := left_eq_mul.mp h
        rw [hz, map_one, map_one]
      map_mul' := fun σ τ => by
        rw [a.property.2 σ τ, map_mul, map_mul, hinv] }
  have hχ (σ : Gal(K/k)) : χ σ = δ (C.schemeAut (a σ)) := congrArg δ (hc (a σ))
  choose g hg using fun σ : Gal(K/k) => hformula (C.schemeAut (a σ))
  have hg' (σ : Gal(K/k)) : MatrixFormula m (C.schemeAut (a σ)) (g σ) (χ σ) := hχ σ ▸ hg σ
  let R₀ := CommAlgCat.of K K
  let X := (m.app R₀).groupIsoToMulEquiv
  let Y := (groupIsoPoints i R₀).trans (baseChangePointGroupEquiv K H.val R₀)
  let M := X.symm.trans Y
  let act := Forms.relabelAction M.symm (fieldPointAction (K := K) H.val)
  have hact (σ : Gal(K/k)) (x y : Points ((groupBaseChange k K).obj G.val).X R₀)
      (h : IsTransportedPoint i (fieldSemilinearMap σ) x y) :
      act σ (baseChangeMatrix s R₀ x) = baseChangeMatrix s R₀ y := by
    change M.symm (fieldPointAction H.val σ (M (baseChangeMatrix s R₀ x))) = baseChangeMatrix s R₀ y
    rw [← hm, ← hm]
    change X (Y.symm (fieldPointAction H.val σ (Y (X.symm (X x))))) = X y
    rw [X.symm_apply_apply, fieldPointAction_apply]
    exact congrArg X (Y.symm_apply_eq.mpr h.symm)
  have hformula' (σ : Gal(K/k)) {R S : TestAlgebra K}
      (b : (restrictTestAlgebra k K).obj R ⟶ (restrictTestAlgebra k K).obj S)
      (hb : IsSemilinearTestMap σ b) (x : Points ((groupBaseChange k K).obj G.val).X R)
      (y : Points ((groupBaseChange k K).obj G.val).X S) (hy : IsTransportedPoint i b x y) :
      let A := GeneralLinearGroup.map (algebraMap K S) (g σ)
      let X := baseChangeMatrix s R x
      (baseChangeMatrix s S y).val = A.val *
        (if χ σ = 1 then X.val.map b.hom.toRingHom else (X⁻¹).val.transpose.map b.hom.toRingHom) * (A⁻¹).val := by
    let t := standardPointChange G.val b x
    have ht := transportedPoint_coefficient C σ b hb (a σ) (ha σ) x
    obtain ⟨w, _, hw⟩ := transportedPoint_unique i b x
    have hwy : y = t ≫ (C.schemeAut (a σ)).asIso.hom.hom.hom := (hw y hy).trans (hw _ ht).symm
    have h := hg' σ S t
    dsimp only at h ⊢
    rw [hwy, ← hm]
    rw [hm S t, standardPointChange_matrix s b x] at h
    let A := GeneralLinearGroup.map (algebraMap K S) (g σ)
    let Z := baseChangeMatrix s R x
    let φ := b.hom.toRingHom
    have hmiddle : (if χ σ = 1 then (SpecialLinearGroup.map φ Z).val
        else ((SpecialLinearGroup.map φ Z)⁻¹).val.transpose) =
        (if χ σ = 1 then Z.val.map φ else (Z⁻¹).val.transpose.map φ) := by
      split_ifs
      · rfl
      · exact map_inverse_transpose φ Z
    exact h.trans (congrArg (fun v => A.val * v * (A⁻¹).val) hmiddle)
  refine ⟨C, ρ, a, m, δ, χ, g, act, hρ, ha, hm, hformula, hdetect,
    fun σ => ⟨hχ σ, hg' σ⟩, fun b x => transportedPoint_unique i b x, hformula', hact, ?_⟩
  intro σ Z
  let x : Points ((groupBaseChange k K).obj G.val).X R₀ := X.symm Z
  obtain ⟨y, hy, _⟩ := transportedPoint_unique i (fieldSemilinearMap σ) x
  have hx : baseChangeMatrix s R₀ x = Z := (hm R₀ x).symm.trans (X.apply_symm_apply Z)
  have h := hformula' σ (fieldSemilinearMap σ) (fieldSemilinearMap_semilinear σ) x y hy
  have het : GeneralLinearGroup.map (algebraMap K R₀) (g σ) = g σ := Units.ext rfl
  dsimp only at h
  rw [het, hx, ← hact σ x y hy, hx] at h
  exact h

theorem finiteMatrixDescent : FiniteMatrixDescent.{u} := by
  intro k _ n hn G s H h
  obtain ⟨K, _, _, _, _, ⟨i⟩⟩ := finiteMatrixSplitting hn s H h
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, i,
    matrixDescentForTrivialization hn s i⟩

end SemilinearPoints

section SchemeComparison

open _root_.LinearAlgebraicGroups.Descent
open CategoryTheory.Limits (pullback.hom_ext)

open private extendedIso spectrumIsoEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private extendedGroupIso extendedSpecIso_hom_fst extendedSpecIso_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem scalarExtensionComparison_unique
    (t : ∀ P : HopfAlgebraCategory k, specGroup (extendedHopf K P) ≅
      (groupBaseChange k K).obj (specGroup P)) (ht : Forms.IsScalarExtensionComparison t)
    (P : HopfAlgebraCategory k) : t P = extendedGroupIso K P := by
  apply Iso.ext
  apply CategoryTheory.Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (ht P).trans (extendedSpecIso_hom_fst K P).symm
  · exact (Over.w _).trans (Over.w _).symm

private theorem baseChange_spectrumIso {Q U : HopfAlgebraCategory k} (b : Q ≅ U) :
    (groupBaseChange k K).mapIso (Forms.spectrumIso b) =
      (extendedGroupIso K Q).symm ≪≫ Forms.spectrumIso (extendedIso K b) ≪≫ extendedGroupIso K U := by
  have h : extendedGroupIso K Q ≪≫ (groupBaseChange k K).mapIso (Forms.spectrumIso b) =
      Forms.spectrumIso (extendedIso K b) ≪≫ extendedGroupIso K U := by
    apply Iso.ext
    apply CategoryTheory.Grp.hom_ext
    exact (extendedSpecIso_natural K b.inv).symm
  calc
    _ = (extendedGroupIso K Q).symm ≪≫
        (extendedGroupIso K Q ≪≫ (groupBaseChange k K).mapIso (Forms.spectrumIso b)) := by simp
    _ = _ := congrArg (fun a => (extendedGroupIso K Q).symm ≪≫ a) h

theorem equivariantSchemeComparisonDescends : EquivariantSchemeComparisonDescends.{u} := by
  intro k K _ _ _ _ _ P Q U t ht i j e h
  let f := i.symm ≪≫ e.asIso ≪≫ j
  let s := spectrumIsoEquiv Q U
  let sK := spectrumIsoEquiv (extendedHopf K Q) (extendedHopf K U)
  obtain ⟨b, hb, hu⟩ := equivariantComparisonDescends i j e h
  have hQ := scalarExtensionComparison_unique t ht Q
  have hU := scalarExtensionComparison_unique t ht U
  have he : extendedIso K b = f := Iso.ext hb
  have comm (a : Q ≅ U) : (groupBaseChange k K).mapIso (s a) =
      (t Q).symm ≪≫ sK (extendedIso K a) ≪≫ t U := by
    rw [hQ, hU]
    exact baseChange_spectrumIso a
  refine ⟨s b, ?_, ?_⟩
  · change (groupBaseChange k K).mapIso (s b) = (t Q).symm ≪≫ sK f ≪≫ t U
    rw [comm, he]
  · intro a ha
    let a' := s.symm a
    have h_a : s a' = a := s.apply_symm_apply a
    have h' : (t Q).symm ≪≫ sK (extendedIso K a') ≪≫ t U = (t Q).symm ≪≫ sK f ≪≫ t U :=
      (comm a').symm.trans ((congrArg ((groupBaseChange k K).mapIso) h_a).trans ha)
    have hex : extendedIso K a' = f := by
      apply sK.injective
      have hh := congrArg (fun d => t Q ≪≫ d ≪≫ (t U).symm) h'
      simpa using hh
    exact h_a.symm.trans (congrArg s (hu a' (congrArg Iso.hom hex)))

end SchemeComparison

end LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData
