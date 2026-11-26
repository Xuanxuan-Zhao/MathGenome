import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ComoduleFiniteness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LinearJordanFactors
import Batteries.Tactic.OpenPrivate

open scoped TensorProduct Ring
open Bialgebra CategoryTheory WithConv

universe u

namespace LinearAlgebraicGroups.SemisimpleLieCentralizer

open Specs.SemisimpleLieCentralizer
open LinearAlgebraicGroups.Specs (IdentityLieStructure)

noncomputable section

variable {k : Type u} [Field k]

private theorem intertwines_powers
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (X : Module.End k V) (Y : Module.End k W)
    (h : f.comp X = Y.comp f) (n : ℕ) : f.comp (X ^ n) = (Y ^ n).comp f := by
  induction n with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

private theorem derivation_power_leibniz {A : Type u} [CommRing A] [Algebra k A]
    (D : Derivation k A A) (p : ℕ) [Fact p.Prime] [CharP k p] (a b : A) :
    (D.toLinearMap ^ p) (a * b) =
      a * (D.toLinearMap ^ p) b + b * (D.toLinearMap ^ p) a := by
  nontriviality A
  let μ := (Algebra.TensorProduct.lmul' k (S := A)).toLinearMap
  let L := D.toLinearMap.lTensor A
  let R := D.toLinearMap.rTensor A
  have h : μ.comp (L + R) = D.toLinearMap.comp μ := by
    apply TensorProduct.ext'
    intro x y
    simp [μ, L, R, mul_comm]
  have hc : Commute L R := by
    apply TensorProduct.ext'
    intro x y
    simp [L, R, Module.End.mul_apply]
  have hμ : Function.Surjective μ := fun c => ⟨c ⊗ₜ[k] (1 : A), by simp [μ]⟩
  let := hμ.nontrivial
  let : CharP (Module.End k (A ⊗[k] A)) p :=
    charP_of_injective_algebraMap (algebraMap k (Module.End k (A ⊗[k] A))).injective p
  have hh := intertwines_powers μ (L + R) D.toLinearMap h p
  rw [add_pow_char_of_commute p hc] at hh
  have hh' := LinearMap.congr_fun hh (a ⊗ₜ[k] b)
  simpa [μ, L, R, LinearMap.lTensor_pow, LinearMap.rTensor_pow, mul_comm] using hh'.symm

/-- The characteristic-p power of a left-invariant derivation. -/
def restrictedPower (A : HopfAlgebraCategory k) (p : ℕ)
    [Fact p.Prime] [CharP k p] (D : InvariantDerivation A) : InvariantDerivation A := by
  refine ⟨⟨D.val.toLinearMap ^ p, ?_, ?_⟩, ?_⟩
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fact.out : p.Prime).ne_zero
    rw [hn, pow_succ, Module.End.mul_apply]
    simp
  · intro a b
    exact derivation_power_leibniz D.val p a b
  · change IsInvariant A (D.val.toLinearMap ^ p)
    unfold IsInvariant
    rw [← LinearMap.lTensor_pow]
    exact intertwines_powers _ _ _ D.property p

theorem restrictedDerivationPower : RestrictedDerivationPower.{u} := by
  intro k _ A p _ _ D
  exact ⟨restrictedPower A p D, rfl⟩

theorem restrictedDifferentialNaturality : RestrictedDifferentialNaturality.{u} := by
  intro k _ A B p _ _ f D Dp E Ep h hD hE
  unfold IsDifferential at h ⊢
  rw [hD, hE]
  exact (intertwines_powers _ _ _ h.symm p).symm

private def contractRight (A : HopfAlgebraCategory k) (f : A →ₗ[k] k) :
    A ⊗[k] A →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap.comp (f.lTensor A)

@[simp] private theorem contractRight_tmul (A : HopfAlgebraCategory k)
    (f : A →ₗ[k] k) (a b : A) :
    contractRight A f (a ⊗ₜ[k] b) = f b • a := rfl

private theorem invariant_eq_contract (A : HopfAlgebraCategory k)
    (T : Module.End k A) (hT : IsInvariant A T) (a : A) :
    T a = contractRight A ((Coalgebra.counit (R := k)).comp T) (Coalgebra.comul a) := by
  have h : (contractRight A (Coalgebra.counit (R := k))).comp (T.lTensor A) =
      contractRight A ((Coalgebra.counit (R := k)).comp T) := by
    apply TensorProduct.ext'
    intro x y
    rfl
  have ht := LinearMap.congr_fun hT a
  apply_fun contractRight A (Coalgebra.counit (R := k)) at ht
  change (TensorProduct.rid k A) ((Coalgebra.counit (R := k)).lTensor A (Coalgebra.comul (T a))) =
    ((contractRight A (Coalgebra.counit (R := k))).comp (T.lTensor A)) (Coalgebra.comul a) at ht
  simpa [h] using ht

private theorem contractRight_counit (A : HopfAlgebraCategory k) (a : A) :
    contractRight A (Coalgebra.counit (R := k)) (Coalgebra.comul a) = a := by
  change (TensorProduct.rid k A) ((Coalgebra.counit (R := k)).lTensor A (Coalgebra.comul a)) = a
  simp

private theorem counit_contractRight (A : HopfAlgebraCategory k)
    (f : A →ₗ[k] k) (a : A) :
    Coalgebra.counit (R := k) (contractRight A f (Coalgebra.comul a)) = f a := by
  have h : (Coalgebra.counit (R := k)).comp (contractRight A f) =
      f.comp ((TensorProduct.lid k A).toLinearMap.comp
        ((Coalgebra.counit (R := k)).rTensor A)) := by
    apply TensorProduct.ext'
    intro x y
    simp [mul_comm]
  have h' := LinearMap.congr_fun h (Coalgebra.comul (R := k) a)
  simpa using h'

private theorem invariant_contractRight (A : HopfAlgebraCategory k) (f : A →ₗ[k] k) :
    IsInvariant A ((contractRight A f).comp Coalgebra.comul) := by
  let δ : A →ₗ[k] A ⊗[k] A := Coalgebra.comul
  let μ := contractRight A f
  have h : δ.comp μ = (μ.lTensor A).comp
      ((TensorProduct.assoc k A A A).toLinearMap.comp (δ.rTensor A)) := by
    apply TensorProduct.ext'
    intro a b
    change δ (μ (a ⊗ₜ[k] b)) =
      μ.lTensor A (TensorProduct.assoc k A A A (δ a ⊗ₜ[k] b))
    rw [show μ (a ⊗ₜ[k] b) = f b • a from rfl, map_smul]
    generalize δ a = z
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [μ, TensorProduct.tmul_smul]
    | add x y hx hy => simp [TensorProduct.add_tmul, smul_add, ← hx, ← hy]
  apply LinearMap.ext
  intro a
  change δ (μ (δ a)) = ((μ.comp δ).lTensor A) (δ a)
  rw [LinearMap.lTensor_comp]
  have h' := LinearMap.congr_fun h (δ a)
  simpa [δ, Coalgebra.coassoc_apply] using h'

private def evaluateCounit (A : HopfAlgebraCategory k) (D : InvariantDerivation A) :
    letI := (counitAlgHom k A).toRingHom.toAlgebra
    Derivation k A k := by
  let ε : A →ₐ[k] k := counitAlgHom k A
  letI := ε.toRingHom.toAlgebra
  refine ⟨ε.toLinearMap.comp D.val.toLinearMap, ?_, ?_⟩
  · simp
  · intro a b
    change ε (D.val (a * b)) = ε a * ε (D.val b) + ε b * ε (D.val a)
    simp [Derivation.leibniz, smul_eq_mul]

private def extendCounitDerivation (A : HopfAlgebraCategory k) :
    letI := (counitAlgHom k A).toRingHom.toAlgebra
    Derivation k A k → InvariantDerivation A := by
  let ε : A →ₐ[k] k := counitAlgHom k A
  letI := ε.toRingHom.toAlgebra
  intro d
  let T := contractRight A d.toLinearMap
  refine ⟨⟨T.comp Coalgebra.comul, ?_, ?_⟩, invariant_contractRight A _⟩
  · change T (Bialgebra.comulAlgHom k A 1) = 0
    rw [map_one]
    change T ((1 : A) ⊗ₜ[k] (1 : A)) = 0
    simp [T]
  · let C := contractRight A (Coalgebra.counit (R := k))
    have hmul (x y : A ⊗[k] A) : T (x * y) = C x * T y + C y * T x := by
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, mul_add]; ac_rfl
      | tmul a b =>
        induction y using TensorProduct.inductionOn with
        | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, add_mul]; ac_rfl
        | tmul c e =>
          have hde : d (b * e) = ε b * d e + ε e * d b := d.leibniz b e
          simp only [Algebra.TensorProduct.tmul_mul_tmul, T, C, contractRight_tmul,
            Algebra.smul_def]
          change algebraMap k A (d (b * e)) * (a * c) =
            (algebraMap k A (ε b) * a) * (algebraMap k A (d e) * c) +
            (algebraMap k A (ε e) * c) * (algebraMap k A (d b) * a)
          rw [hde, map_add, map_mul, map_mul]
          ring
    intro a b
    change T (Bialgebra.comulAlgHom k A (a * b)) = a * T (Coalgebra.comul b) + b * T (Coalgebra.comul a)
    rw [map_mul]
    simpa [C, contractRight_counit] using hmul (Coalgebra.comul a) (Coalgebra.comul b)

theorem invariantDerivationCounit : InvariantDerivationCounit.{u} := by
  intro k _ A
  let := (counitAlgHom k A).toRingHom.toAlgebra
  refine ⟨⟨evaluateCounit A, extendCounitDerivation A, ?_, ?_⟩, fun _ _ => rfl⟩
  · intro D
    apply Subtype.ext
    apply Derivation.ext
    intro a
    exact (invariant_eq_contract A D.val.toLinearMap D.property a).symm
  · intro d
    apply Derivation.ext
    intro a
    exact counit_contractRight A d.toLinearMap a

theorem invariantDerivationLifts : InvariantDerivationLifts.{u} := by
  intro k _ A
  let := (counitAlgHom k A).toRingHom.toAlgebra
  obtain ⟨e, he⟩ := invariantDerivationCounit k A
  obtain ⟨l, hl, _⟩ := counitDerivationLifts k A
  exact ⟨e.trans l, fun D a => (hl (e D) a).trans (by rw [he]; rfl)⟩

open private dualKernelIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

theorem restrictedLieOperation : RestrictedLieOperation.{u} := by
  intro k _ G A e p _ _
  obtain ⟨lifts, hlifts⟩ := invariantDerivationLifts k A
  let t := dualKernelIso e
  let q := lifts.trans ((hopfKernelLifts A).symm.trans t.toEquiv)
  let power : Specs.Lie k G → Specs.Lie k G :=
    fun x => q (restrictedPower A p (q.symm x))
  refine ⟨q, power, ?_, ?_⟩
  · intro D a
    change (((hopfKernelLifts A) (t.symm (t ((hopfKernelLifts A).symm (lifts D))))).val a).snd = _
    rw [t.symm_apply_apply, (hopfKernelLifts A).apply_symm_apply, hlifts]
    rfl
  · intro x
    change (q.symm (q (restrictedPower A p (q.symm x)))).val.toLinearMap = _
    rw [q.symm_apply_apply]
    rfl

theorem invariantDifferentialComparison : InvariantDifferentialComparison.{u} := by
  intro k _ A B f D
  let εA : A →ₐ[k] k := counitAlgHom k A
  let εB : B →ₐ[k] k := counitAlgHom k B
  let := εB.toRingHom.toAlgebra
  let F := f.hom.toLinearMap
  let T := εA.toLinearMap.comp D.val.toLinearMap
  have hε (b : B) : εA (f.hom b) = εB b := CoalgHomClass.counit_comp_apply f.hom b
  let d : Derivation k B k :=
    ⟨T.comp F, by
      change εA (D.val (f.hom 1)) = 0
      rw [map_one, D.val.map_one_eq_zero, map_zero], fun a b => by
      change εA (D.val (f.hom (a * b))) =
        εB a * εA (D.val (f.hom b)) + εB b * εA (D.val (f.hom a))
      simp [Derivation.leibniz, smul_eq_mul, hε]⟩
  refine ⟨extendCounitDerivation B d, ?_, counit_contractRight B d.toLinearMap⟩
  have h : (contractRight A T).comp (TensorProduct.map F F) =
      F.comp (contractRight B d.toLinearMap) := by
    apply TensorProduct.ext'
    intro a b
    simp [d]
  apply LinearMap.ext
  intro b
  change D.val.toLinearMap (f.hom b) = F (contractRight B d.toLinearMap (Coalgebra.comul b))
  rw [invariant_eq_contract A D.val.toLinearMap D.property (f.hom b),
    ← CoalgHomClass.map_comp_comul_apply f.hom b]
  exact LinearMap.congr_fun h (Coalgebra.comul (R := k) b)

theorem matrixDifferentialComparison : MatrixDifferentialComparison.{u} := by
  intro k _ G A e ι _ _ L l f D g hg
  let α := e.hom ≫ (groupPointsFunctor k).map f ≫ l.hom
  let S := CommAlgCat.of k A
  let R := CommAlgCat.of k (DualNumber k)
  let a : S ⟶ R := CommAlgCat.ofHom g.val
  let z : (convolutionPoints A).obj S := toConv (AlgHom.id k A)
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (α.naturality a)) z
  change α.app R (toConv g.val) = Matrix.GeneralLinearGroup.map g.val.toRingHom (α.app S z) at h
  ext i j
  change ((α.app R (toConv g.val)).val i j).snd =
    Coalgebra.counit (R := k) (D.val ((α.app S z).val i j))
  rw [h]
  exact hg _

private theorem invariant_pow (A : HopfAlgebraCategory k)
    {T : Module.End k A} (hT : IsInvariant A T) (n : ℕ) :
    IsInvariant A (T ^ n) := by
  unfold IsInvariant
  rw [← LinearMap.lTensor_pow]
  exact intertwines_powers _ _ _ hT n

private theorem matrixAction_powers (A : HopfAlgebraCategory k)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A)
    (hM : RationalRepresentations.IsCoactionMatrix A M)
    (D : InvariantDerivation A) (n : ℕ) :
    ((fun i j => Coalgebra.counit (R := k) ((D.val.toLinearMap ^ n) (M i j))) : Matrix ι ι k) =
      matrixAction A M D ^ n := by
  let T := D.val.toLinearMap
  let ε : A →ₗ[k] k := Coalgebra.counit
  let N : ℕ → Matrix ι ι k := fun m i j => ε ((T ^ m) (M i j))
  change N n = N 1 ^ n
  have hformula (m : ℕ) (i j : ι) :
      (T ^ m) (M i j) = ∑ l, N m l j • M i l := by
    rw [invariant_eq_contract A (T ^ m) (invariant_pow A D.property m) (M i j),
      hM.comul, map_sum]
    simp [N, ε]
  induction n with
  | zero =>
    rw [pow_zero]
    ext i j
    simpa [N, ε, Module.End.one_eq_id] using hM.counit i j
  | succ n ih =>
    rw [pow_succ]
    ext i j
    change ε ((T ^ (n + 1)) (M i j)) = (N 1 ^ n * N 1) i j
    rw [pow_succ, Module.End.mul_apply]
    have h1 := hformula 1 i j
    rw [pow_one] at h1
    rw [h1]
    simp only [map_sum, map_smul, smul_eq_mul, Matrix.mul_apply, ← ih]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem restrictedMatrixAction : RestrictedMatrixAction.{u} := by
  intro k _ A p _ _ ι _ _ M hM D E hE
  change (fun i j => Coalgebra.counit (R := k) (E.val.toLinearMap (M i j))) = _
  rw [hE]
  exact matrixAction_powers A M hM D p

theorem restrictedSchemeDifferential : RestrictedSchemeDifferential.{u} := by
  intro k _ G A e p _ _ D E g h hp hg hh ι _ _ L l f
  rw [matrixDifferentialComparison k G A e ι L l f D g hg,
    matrixDifferentialComparison k G A e ι L l f E h hh]
  let b := Pi.basisFun k ι
  obtain ⟨eqv, heqv⟩ := RationalRepresentations.representationCoactionComparison A b G L e l
  refine restrictedMatrixAction k A p ι _ ?_ D E hp
  rw [← heqv f]
  exact RationalRepresentations.coefficients_isCoactionMatrix A b (eqv f)

theorem restrictedAdjointPower : RestrictedAdjointPower.{u} := by
  intro k _ G s A e p _ _ D E g h hp hg hh
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨n, b, _, L, l, Ad, _, hAd, _⟩ := adjointRepresentation k G s
  have hmatrix (x : Specs.Lie k G.val) :
      LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad k (Specs.Lie k G.val) x) =
        InfinitesimalCommutator.matrixDifferential Ad l x := by
    ext i j
    have hv := congrFun (hAd x (b j)) i
    have hb : b.equivFun (b j) = Pi.single j 1 := by
      ext t
      change b.repr (b j) t = _
      rw [b.repr_self]
      simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
    rw [hb, Matrix.mulVec_single_one] at hv
    rw [LinearMap.toMatrixAlgEquiv_apply]
    exact hv.symm
  apply (LinearMap.toMatrixAlgEquiv b).injective
  rw [map_pow, hmatrix, hmatrix]
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  exact restrictedSchemeDifferential k G' A e p D E g h hp hg hh _ L.val l Ad

theorem largePrimePowerSemisimple : LargePrimePowerSemisimple.{u} := by
  intro k V _ _ _ _ _ p r _ _ X hdim
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [Subsingleton.elim (X ^ (p ^ r)) 0]
    exact Module.End.isSemisimple_zero
  let : CharP (Module.End k V) p :=
    charP_of_injective_algebraMap (algebraMap k (Module.End k V)).injective p
  obtain ⟨N, hN, S, hS, hn, hs, hx⟩ := X.exists_isNilpotent_isSemisimple
  have hc := Algebra.commute_of_mem_adjoin_singleton_of_commute hN
    (Algebra.commute_of_mem_adjoin_self hS).symm
  have hnil : N ^ Module.finrank k V = 0 := by
    simpa [hn.charpoly_eq_X_pow_finrank] using N.aeval_self_charpoly
  have hpow : N ^ (p ^ r) = 0 := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hdim
    rw [hq, pow_add, hnil, zero_mul]
  rw [hx, add_pow_char_pow_of_commute p r hc.symm, hpow, zero_add]
  exact hs.pow _

theorem largePrimePowerGeometricallySemisimple :
    LargePrimePowerGeometricallySemisimple.{u} := by
  intro k ι _ _ _ p r _ _ X hdim
  let K := AlgebraicClosure k
  let f : Matrix ι ι k →+* Matrix ι ι K := (algebraMap k K).mapMatrix
  change Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (f (X ^ (p ^ r))))
  rw [map_pow, map_pow]
  apply largePrimePowerSemisimple K (ι → K) p r
  simpa using hdim

theorem membershipDescends : MembershipDescends.{u} := by
  intro k K V _ _ _ _ _ W x
  refine ⟨?_, W.tmul_mem_baseChange_of_mem (A := K) 1⟩
  rintro ⟨t, ht⟩
  have hzero : W.mkQ.comp W.subtype = 0 := by
    ext z
    exact (Submodule.Quotient.mk_eq_zero W).mpr z.property
  have hc : (W.mkQ.baseChange K).comp (W.subtype.baseChange K) = 0 := by
    rw [← LinearMap.baseChange_comp, hzero, LinearMap.baseChange_zero]
  have hz := LinearMap.congr_fun hc t
  change (W.mkQ.baseChange K) ((W.subtype.baseChange K) t) = 0 at hz
  rw [ht, LinearMap.baseChange_tmul] at hz
  have hinj := Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := K) (V ⧸ W)
  have hz' : W.mkQ x = 0 := hinj (by simpa only [TensorProduct.mk_apply, TensorProduct.tmul_zero] using hz)
  exact (Submodule.Quotient.mk_eq_zero W).mp hz'

private theorem semilinear_surjective_of_injective
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (φ : k ≃+* k) (f : V →ₛₗ[φ.toRingHom] V) (h : Function.Injective f) :
    Function.Surjective f := by
  let : RingHomSurjective φ.toRingHom := ⟨φ.surjective⟩
  let b := Module.finBasis k V
  have hi : LinearIndependent k (fun i => f (b i)) :=
    b.linearIndependent.map_of_surjective_injectiveₛ φ f.toAddMonoidHom φ.surjective h
      (fun c x => f.map_smulₛₗ c x)
  have hs : Submodule.span k (Set.range fun i => f (b i)) = ⊤ :=
    hi.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)
  apply LinearMap.range_eq_top.mp
  rw [eq_top_iff, ← hs]
  exact Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_range_self f (b i))

private theorem frobenius_orbit_in_tail_span {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]
    (v : ι → k) (r : ℕ) :
    v ∈ Submodule.span k (Set.range fun n : ℕ => fun i => v i ^ (p ^ (r + n))) := by
  let φ := frobeniusEquiv k p
  let F : (ι → k) →ₛₗ[φ.toRingHom] (ι → k) :=
    { toFun := fun x i => φ (x i)
      map_add' := fun x y => funext fun i => φ.map_add (x i) (y i)
      map_smul' := fun c x => funext fun i => φ.map_mul c (x i) }
  have hFinj : Function.Injective F := fun _ _ h =>
    funext fun i => φ.injective (congrFun h i)
  let a (n : ℕ) : ι → k := fun i => v i ^ (p ^ n)
  have hF (n : ℕ) : F (a n) = a (n + 1) := by
    funext i
    change (v i ^ (p ^ n)) ^ p = v i ^ (p ^ (n + 1))
    rw [pow_succ, pow_mul]
  let W (s : ℕ) := Submodule.span k (Set.range fun n => a (s + n))
  let : RingHomSurjective φ.toRingHom := ⟨φ.surjective⟩
  have hstep (s : ℕ) : (W s).map F = W (s + 1) := by
    unfold W
    rw [Submodule.map_span, ← Set.range_comp']
    apply congrArg (Submodule.span k)
    apply congrArg Set.range
    funext n
    rw [hF, Nat.add_right_comm s n 1]
  have hle : (W 0).map F ≤ W 0 := by
    rw [hstep]
    apply Submodule.span_mono
    rintro _ ⟨n, rfl⟩
    exact ⟨n + 1, by simp [Nat.add_comm]⟩
  let f : W 0 →ₛₗ[φ.toRingHom] W 0 :=
    { toFun := fun x => ⟨F x.val, hle (Submodule.mem_map_of_mem x.property)⟩
      map_add' := fun x y => Subtype.ext (F.map_add x.val y.val)
      map_smul' := fun c x => Subtype.ext (F.map_smulₛₗ c x.val) }
  have hfs : Function.Surjective f := semilinear_surjective_of_injective φ f
    (fun x y h => Subtype.ext (hFinj (congrArg Subtype.val h)))
  have hstable : (W 0).map F = W 0 := by
    apply le_antisymm hle
    intro x hx
    obtain ⟨y, hy⟩ := hfs ⟨x, hx⟩
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  have hw (s : ℕ) : W s = W 0 := by
    induction s with
    | zero => rfl
    | succ s ih => rw [← hstep, ih, hstable]
  change v ∈ W r
  rw [hw]
  exact Submodule.subset_span ⟨0, by funext i; simp [a]⟩

open private eigenbasis_of_isSemisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LinearJordanFactors

private theorem semisimple_mem_of_primePowers [IsAlgClosed k] {V : Type*}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (p : ℕ) [Fact p.Prime] [CharP k p] (W : Submodule k (Module.End k V))
    {X S N : Module.End k V} (h : IsAdditiveJordanDecomposition X S N)
    (hXm : ∀ n : ℕ, X ^ (p ^ n) ∈ W) : S ∈ W := by
  classical
  obtain ⟨b, eigenvalue, hb⟩ := eigenbasis_of_isSemisimple h.semisimple
  let d : (Fin (Module.finrank k V) → k) →ₗ[k] Module.End k V :=
    (Matrix.toLinAlgEquiv b).toLinearMap.comp (Matrix.diagonalLinearMap _ k k)
  have hd : d eigenvalue = S := by
    apply b.ext
    intro i
    rw [hb]
    change Matrix.toLinAlgEquiv b (Matrix.diagonal eigenvalue) (b i) = _
    rw [Matrix.toLinAlgEquiv_self]
    simp [Matrix.diagonal_apply]
  have hdp (n : ℕ) : d (fun i => eigenvalue i ^ n) = S ^ n := by
    rw [← hd]
    change Matrix.toLinAlgEquiv b (Matrix.diagonal (fun i => eigenvalue i ^ n)) =
      (Matrix.toLinAlgEquiv b (Matrix.diagonal eigenvalue)) ^ n
    rw [← map_pow, Matrix.diagonal_pow]
    rfl
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [Subsingleton.elim S 0]
    exact W.zero_mem
  let : CharP (Module.End k V) p :=
    charP_of_injective_algebraMap (algebraMap k (Module.End k V)).injective p
  obtain ⟨m, hm⟩ := h.nilpotent
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt m (Fact.out : p.Prime).one_lt
  rw [← hd]
  have hv := frobenius_orbit_in_tail_span p eigenvalue r
  have hle : Submodule.span k (Set.range fun n : ℕ => fun i =>
      eigenvalue i ^ (p ^ (r + n))) ≤ W.comap d := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change d (fun i => eigenvalue i ^ (p ^ (r + n))) ∈ W
    rw [hdp]
    have hge : m ≤ p ^ (r + n) :=
      hr.le.trans (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (Nat.le_add_right r n))
    have hz : N ^ (p ^ (r + n)) = 0 := by
      obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hge
      rw [hq, pow_add, hm, zero_mul]
    have hpow := hXm (r + n)
    rw [h.sum, add_pow_char_pow_of_commute p (r + n) h.commute, hz, add_zero] at hpow
    exact hpow
  exact hle hv

theorem primePowerJordanMembership : PrimePowerJordanMembership.{u} := by
  intro k V _ _ _ _ _ p _ _ W hW X hx
  obtain ⟨N, hN, S, hS, hn, hs, hsum⟩ := X.exists_isNilpotent_isSemisimple
  have hc : Commute S N := Algebra.commute_of_mem_adjoin_singleton_of_commute hN
    (Algebra.commute_of_mem_adjoin_self hS).symm
  have hXm (n : ℕ) : X ^ (p ^ n) ∈ W := by
    induction n with
    | zero => simpa
    | succ n ih =>
      rw [pow_succ, pow_mul]
      exact hW _ ih
  have hsW := semisimple_mem_of_primePowers p W
    (⟨hsum.trans (add_comm N S), hc, hs, hn⟩ : IsAdditiveJordanDecomposition X S N) hXm
  refine ⟨S, hsW, N, ?_, ⟨by simpa [add_comm] using hsum, hc, hs, hn⟩⟩
  have he : N = X - S := by rw [hsum, add_sub_cancel_right]
  exact he ▸ W.sub_mem hx hsW

theorem restrictedIteratedMatrixAction : RestrictedIteratedMatrixAction.{u} := by
  intro k _ A p r _ _ ι _ _ M hM D
  have h (s : ℕ) :
      ((restrictedPower A p)^[s] D).val.toLinearMap = D.val.toLinearMap ^ (p ^ s) := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Function.iterate_succ_apply', pow_succ, pow_mul]
      change (((restrictedPower A p)^[s] D).val.toLinearMap) ^ p = _
      rw [ih]
  refine ⟨(restrictedPower A p)^[r] D, h r, ?_⟩
  change ((fun i j => Coalgebra.counit (R := k)
    (((restrictedPower A p)^[r] D).val.toLinearMap (M i j))) : Matrix ι ι k) = _
  rw [h]
  exact matrixAction_powers A M hM D (p ^ r)

theorem smoothDiagonalizableDerivationQuotient :
    SmoothDiagonalizableDerivationQuotient.{u} := by
  classical
  intro k A _ _ _ _ D hspan
  let J : Ideal A := Ideal.span (Set.range D)
  have hformal : Algebra.FormallySmooth k (A ⧸ J) := by
    rw [Algebra.FormallySmooth.iff_comp_surjective]
    intro B _ _ I hI g
    let q := Ideal.Quotient.mkₐ k J
    let qI := Ideal.Quotient.mkₐ k I
    obtain ⟨f, hf⟩ := Algebra.FormallySmooth.comp_surjective k A I hI (g.comp q)
    let E := Module.End.eigenspace D.toLinearMap
    have hE (a : A) : a ∈ ⨆ w, E w := hspan.symm ▸ Submodule.mem_top
    let : DirectSum.Decomposition E :=
      (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
        (Module.End.eigenspaces_iSupIndep D.toLinearMap) hspan).chooseDecomposition
    let P : A →ₗ[k] A := (E 0).subtype.comp
      ((DirectSum.component k k (fun w => ↥(E w)) 0).comp (DirectSum.decomposeLinearEquiv E).toLinearMap)
    have hP0 {a : A} (ha : a ∈ E 0) : P a = a :=
      DirectSum.decompose_of_mem_same E ha
    have hPne {a : A} {w : k} (ha : a ∈ E w) (hw : w ≠ 0) : P a = 0 :=
      DirectSum.decompose_of_mem_ne E ha hw
    have h1 : (1 : A) ∈ E 0 := by
      rw [Module.End.mem_eigenspace_iff]
      change D 1 = _
      simp
    have hq (w : k) (a : A) (ha : a ∈ E w) (hw : w ≠ 0) : a ∈ J := by
      have he : D a = w • a := Module.End.mem_eigenspace_iff.mp ha
      have hD : D a ∈ J := Ideal.subset_span (Set.mem_range_self a)
      rw [he] at hD
      simpa [smul_smul, hw] using (show w⁻¹ • (w • a) ∈ J from by
        rw [Algebra.smul_def]
        exact J.mul_mem_left _ hD)
    have hfI (w : k) (a : A) (ha : a ∈ E w) (hw : w ≠ 0) : f a ∈ I := by
      have h := DFunLike.congr_fun hf a
      change qI (f a) = g (q a) at h
      have hzero : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hq w a ha hw)
      have hzeroI : qI (f a) = 0 := by rw [h, hzero, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzeroI
    have hmul (m n : k) (a b : A) (ha : a ∈ E m) (hb : b ∈ E n) :
        a * b ∈ E (m + n) := by
      have ha' : D a = m • a := Module.End.mem_eigenspace_iff.mp ha
      have hb' : D b = n • b := Module.End.mem_eigenspace_iff.mp hb
      rw [Module.End.mem_eigenspace_iff]
      change D (a * b) = _
      rw [D.leibniz, ha', hb']
      simp only [smul_eq_mul, mul_smul_comm, add_smul, mul_comm b a, add_comm]
    let F := f.toLinearMap.comp P
    have hFmul (a b : A) : F (a * b) = F a * F b := by
      refine Submodule.iSup_induction E (motive := fun a =>
        F (a * b) = F a * F b) (hE a) ?_ (by simp) ?_
      · intro m a ha
        refine Submodule.iSup_induction E (motive := fun b =>
          F (a * b) = F a * F b) (hE b) ?_ (by simp) ?_
        · intro n b hb
          change f (P (a * b)) = f (P a) * f (P b)
          by_cases hm : m = 0
          · subst m
            have hp : a * b ∈ E n := by simpa using hmul 0 n a b ha hb
            by_cases hn : n = 0
            · subst n
              rw [hP0 ha, hP0 hb, hP0 hp, map_mul]
            · rw [hP0 ha, hPne hb hn, hPne hp hn, map_zero, mul_zero]
          · rw [hPne ha hm, map_zero, zero_mul]
            by_cases hmn : m + n = 0
            · have hn : n ≠ 0 := by
                intro hn
                apply hm
                simpa [hn] using hmn
              rw [hP0 (hmn ▸ hmul m n a b ha hb), map_mul]
              have hh := Ideal.mul_mem_mul (hfI m a ha hm) (hfI n b hb hn)
              rwa [← pow_two, hI, Ideal.mem_bot] at hh
            · rw [hPne (hmul m n a b ha hb) hmn, map_zero]
        · intro b₁ b₂ h₁ h₂
          simp [mul_add, h₁, h₂]
      · intro a₁ a₂ h₁ h₂
        simp [add_mul, h₁, h₂]
    let f' : A →ₐ[k] B :=
      { toFun := F
        map_zero' := map_zero F
        map_add' := map_add F
        map_one' := by change f (P 1) = 1; rw [hP0 h1, map_one]
        map_mul' := hFmul
        commutes' := fun c => by
          change f (P (algebraMap k A c)) = _
          rw [hP0, f.commutes]
          rw [Module.End.mem_eigenspace_iff]
          change D (algebraMap k A c) = _
          simp }
    have hpd (a : A) : P (D a) = 0 := by
      refine Submodule.iSup_induction E (motive := fun a => P (D a) = 0)
        (hE a) ?_ (by simp) ?_
      · intro w a ha
        have he : D a = w • a := Module.End.mem_eigenspace_iff.mp ha
        by_cases hw : w = 0
        · simp [he, hw]
        · rw [he, map_smul, hPne ha hw, smul_zero]
      · intro a b ha hb
        simp [ha, hb]
    have hj : ∀ a : A, a ∈ J → f' a = 0 := by
      have hle : J ≤ RingHom.ker f'.toRingHom :=
        Ideal.span_le.mpr (by rintro _ ⟨a, rfl⟩; change f (P (D a)) = 0; simp [hpd])
      exact fun a ha => hle ha
    refine ⟨Ideal.Quotient.liftₐ J f' hj, ?_⟩
    apply Ideal.Quotient.algHom_ext
    rw [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp, ← hf]
    apply AlgHom.ext
    intro a
    change qI (f' a) = qI (f a)
    refine Submodule.iSup_induction E (motive := fun a =>
      qI (f' a) = qI (f a)) (hE a) ?_ (by simp) ?_
    · intro w a ha
      change qI (f (P a)) = qI (f a)
      by_cases hw : w = 0
      · subst w
        rw [hP0 ha]
      · have hz : qI (f a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hfI w a ha hw)
        rw [hPne ha hw, map_zero, map_zero, hz]
    · intro a b ha hb
      simp [ha, hb]
  exact ⟨hformal, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

section Adjoint

attribute [local instance 100] LieRing.ofAssociativeRing

theorem adjointFromFaithfulDifferential : AdjointFromFaithfulDifferential.{u} := by
  intro k L V _ _ _ _ _ _ _ f hf x
  let F := f.toLinearMap
  let S := LieAlgebra.ad k L x
  let T := LieAlgebra.ad k (Module.End k V) (f x)
  have h : F.comp S = T.comp F := by
    apply LinearMap.ext
    intro y
    exact f.map_lie x y
  constructor
  · intro hs
    let W := LinearMap.range F
    have hW : W ∈ Module.End.invtSubmodule T := by
      intro v hv
      obtain ⟨y, rfl⟩ := hv
      exact ⟨S y, LinearMap.congr_fun h y⟩
    let e := LinearEquiv.ofInjective F hf
    have he : e.toLinearMap.comp S = (T.restrict (p := W) (q := W) hW).comp e.toLinearMap := by
      apply LinearMap.ext
      intro y
      exact Subtype.ext (LinearMap.congr_fun h y)
    exact (e.isSemisimple_iff S (T.restrict (p := W) (q := W) hW) he).mpr
      ((LieAlgebra.ad_isSemisimple_of_isSemisimple hs).restrict hW)
  · intro hn
    obtain ⟨n, hn'⟩ := LieAlgebra.ad_nilpotent_of_nilpotent (R := k) hn
    use n
    apply LinearMap.ext
    intro y
    apply hf
    have h' := LinearMap.congr_fun (intertwines_powers F S T h n) y
    change F ((S ^ n) y) = (T ^ n) (F y) at h'
    rw [show T ^ n = 0 from hn', LinearMap.zero_apply] at h'
    change F ((S ^ n) y) = F 0
    rw [h', map_zero]

end Adjoint

theorem genericMatrixSpecialization : GenericMatrixSpecialization.{u} := by
  intro k ι K _ _ _ _ _ F v
  ext i j
  change (MvPolynomial.aeval v) (∑ l, MvPolynomial.C (F (Pi.single l 1) i j) * MvPolynomial.X l)
    = (∑ l, v l • (F (Pi.single l 1)).map (algebraMap k K)) i j
  simp [Matrix.sum_apply, mul_comm]

theorem characteristicPolynomialOpen : CharacteristicPolynomialOpen.{u} := by
  intro k ι _ _ _ M
  have hpoint (K : Type u) [Field K] [Algebra k K] (v : ι → K) :
      evaluationPoint K v ∈ charpolyOpen M ↔
        (M.map (MvPolynomial.aeval v : MvPolynomial ι k →ₐ[k] K)).charpoly ≠
          Polynomial.X ^ Fintype.card ι := by
    let f : MvPolynomial ι k →ₐ[k] K := MvPolynomial.aeval v
    let q := M.charpoly - Polynomial.X ^ Fintype.card ι
    have hmap : q.map f.toRingHom = (M.map f.toRingHom).charpoly -
        Polynomial.X ^ Fintype.card ι := by
      dsimp only [q]
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Matrix.charpoly_map]
    change ¬ Set.range q.coeff ⊆ (RingHom.ker f.toRingHom : Set _) ↔
      (M.map f.toRingHom).charpoly ≠ Polynomial.X ^ Fintype.card ι
    apply not_congr
    rw [← sub_eq_zero, ← hmap]
    constructor
    · intro he
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      exact he (Set.mem_range_self n)
    · intro he
      rintro _ ⟨n, rfl⟩
      change f.toRingHom (q.coeff n) = 0
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
        congrArg (fun r : Polynomial K => r.coeff n) he
  exact ⟨(PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl, hpoint,
    fun K _ _ v hv => ⟨evaluationPoint K v, (hpoint K v).mpr hv⟩⟩

theorem characteristicPolynomialOpenRationalPoint :
    CharacteristicPolynomialOpenRationalPoint.{u} := by
  classical
  intro k ι _ _ _ _ M K _ _ v hv
  by_contra! h
  apply hv
  change (Set.range fun n => (M.charpoly - Polynomial.X ^ Fintype.card ι).coeff n) ⊆
    (RingHom.ker (MvPolynomial.aeval v : MvPolynomial ι k →ₐ[k] K).toRingHom : Set _)
  rintro _ ⟨n, rfl⟩
  let m := (M.charpoly - Polynomial.X ^ Fintype.card ι).coeff n
  have hz : m = 0 := MvPolynomial.funext fun w => by
    have hw := h w
    simp only [charpolyOpen, Set.mem_compl_iff, not_not, PrimeSpectrum.mem_zeroLocus] at hw
    have hwm := hw (Set.mem_range_self n)
    change (MvPolynomial.aeval w : MvPolynomial ι k →ₐ[k] k) m = 0 at hwm
    simpa only [MvPolynomial.aeval_eq_eval, map_zero] using hwm
  change (MvPolynomial.aeval v : MvPolynomial ι k →ₐ[k] K) m = 0
  simp [hz]

private theorem centralizesMatrix_iff_ideal_le_ker (A : HopfAlgebraCategory k)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (Y : Matrix ι ι k)
    {R : Type u} [CommRing R] [Algebra k R] (g : A →ₐ[k] R) :
    CentralizesMatrix A M Y g ↔ centralizerIdeal A M Y ≤ RingHom.ker g.toRingHom := by
  let T := Y.map (algebraMap k A)
  have hT : g.mapMatrix T = Y.map (algebraMap k R) := by
    ext i j
    exact g.commutes (Y i j)
  have hmat :
      g.mapMatrix (M * T - T * M) = M.map g * Y.map (algebraMap k R) -
        Y.map (algebraMap k R) * M.map g := by
    rw [map_sub, map_mul, map_mul, hT]
    rfl
  unfold CentralizesMatrix Commute SemiconjBy
  rw [← sub_eq_zero, ← hmat]
  change g.mapMatrix (M * T - T * M) = 0 ↔
    Ideal.span (Set.range fun ij : ι × ι => (M * T - T * M) ij.1 ij.2) ≤ RingHom.ker g.toRingHom
  rw [Ideal.span_le]
  constructor
  · intro h
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact congrArg (fun N : Matrix ι ι R => N i j) h
  · intro h
    ext i j
    exact h (Set.mem_range_self (i, j))

theorem matrixCentralizerPoints : MatrixCentralizerPoints.{u} := by
  intro k _ A ι _ _ M Y R _ _
  let J := centralizerIdeal A M Y
  let q := Ideal.Quotient.mkₐ k J
  let into (g : (A ⧸ J) →ₐ[k] R) : {g : A →ₐ[k] R // CentralizesMatrix A M Y g} :=
    ⟨g.comp q, (centralizesMatrix_iff_ideal_le_ker A M Y _).mpr fun a ha => by
      change g (q a) = 0
      have h : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
      rw [h, map_zero]⟩
  let out (g : {g : A →ₐ[k] R // CentralizesMatrix A M Y g}) : (A ⧸ J) →ₐ[k] R :=
    Ideal.Quotient.liftₐ J g.val fun a ha =>
      (centralizesMatrix_iff_ideal_le_ker A M Y g.val).mp g.property ha
  have hout (g : {g : A →ₐ[k] R // CentralizesMatrix A M Y g}) : (out g).comp q = g.val :=
    Ideal.Quotient.liftₐ_comp J g.val _
  refine ⟨⟨into, out, ?_, ?_⟩, fun _ => rfl⟩
  · intro g
    apply Ideal.Quotient.algHom_ext
    exact hout (into g)
  · intro g
    exact Subtype.ext (hout g)

theorem matrixCentralizerTangent : MatrixCentralizerTangent.{u} := by
  intro k _ A ι _ _ M Y hM D g hg
  let X := matrixAction A M D
  let U := M.map g.val
  let V := Y.map (algebraMap k (DualNumber k))
  let fst := TrivSqZeroExt.fstHom k k k
  let snd := TrivSqZeroExt.sndHom (R := k) (M := k)
  have hU : fst.mapMatrix U = (1 : Matrix ι ι k) := by
    ext i j
    have h := DFunLike.congr_fun g.property (M i j)
    change (g.val (M i j)).fst = Coalgebra.counit (R := k) (M i j) at h
    exact h.trans (hM.counit i j)
  have hV : fst.mapMatrix V = Y := by
    ext i j
    exact fst.commutes (Y i j)
  have hfst : fst.mapMatrix (U * V) = fst.mapMatrix (V * U) := by
    simp [map_mul, hU, hV]
  have hUV (i j : ι) : ((U * V) i j).snd = (X * Y) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    change snd (∑ l, U i l * V l j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _
    change (g.val (M i l) * algebraMap k (DualNumber k) (Y l j)).snd = X i l * Y l j
    simp [TrivSqZeroExt.algebraMap_eq_inl, hg, X, matrixAction]
  have hVU (i j : ι) : ((V * U) i j).snd = (Y * X) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    change snd (∑ l, V i l * U l j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _
    change (algebraMap k (DualNumber k) (Y i l) * g.val (M l j)).snd = Y i l * X l j
    simp [TrivSqZeroExt.algebraMap_eq_inl, hg, X, matrixAction]
  change U * V = V * U ↔ X * Y = Y * X
  constructor
  · intro h
    ext i j
    rw [← hUV, ← hVU, h]
  · intro h
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · exact congrArg (fun N : Matrix ι ι k => N i j) hfst
    · rw [hUV, hVU, h]

section AdditiveJordan

open Module Algebra

private theorem exists_additiveJordan [PerfectField k] {V : Type*}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (X : End k V) :
    ∃ S N, IsAdditiveJordanDecomposition X S N := by
  obtain ⟨N, hN, S, hS, hn, hs, hX⟩ := X.exists_isNilpotent_isSemisimple
  exact ⟨S, N, hX.trans (add_comm N S),
    commute_of_mem_adjoin_singleton_of_commute hN (commute_of_mem_adjoin_self hS).symm,
    hs, hn⟩

open private isSemisimple_baseChange additive_intertwining_over_algClosed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LinearJordanFactors

private theorem additiveJordan_baseChange [PerfectField k] {K V : Type*}
    [Field K] [Algebra k K] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {X S N : End k V} (h : IsAdditiveJordanDecomposition X S N) :
    IsAdditiveJordanDecomposition (X.baseChange K) (S.baseChange K) (N.baseChange K) := by
  let φ := End.baseChangeHom k K V
  change IsAdditiveJordanDecomposition (φ X) (φ S) (φ N)
  exact ⟨(congrArg φ h.sum).trans (map_add φ S N), h.commute.map φ,
    isSemisimple_baseChange h.semisimple, h.nilpotent.map φ⟩

private theorem additiveJordan_intertwining [PerfectField k] {V W : Type*}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {X S N : End k V} {Y T M : End k W}
    (hX : IsAdditiveJordanDecomposition X S N) (hY : IsAdditiveJordanDecomposition Y T M)
    (f : V →ₗ[k] W) (hf : f.comp X = Y.comp f) :
    f.comp S = T.comp f ∧ f.comp N = M.comp f := by
  let K := AlgebraicClosure k
  let φ := End.baseChangeHom k K V
  let ψ := End.baseChangeHom k K W
  have hcX : Commute X S := hX.sum ▸ (Commute.refl S).add_left hX.commute.symm
  have hcY : Commute Y T := hY.sum ▸ (Commute.refl T).add_left hY.commute.symm
  have hnX : IsNilpotent (X - S) := by rw [hX.sum, add_sub_cancel_left]; exact hX.nilpotent
  have hnY : IsNilpotent (Y - T) := by rw [hY.sum, add_sub_cancel_left]; exact hY.nilpotent
  have hf' : (f.baseChange K).comp (φ X) = (ψ Y).comp (f.baseChange K) := by
    change (f.baseChange K).comp (X.baseChange K) = (Y.baseChange K).comp (f.baseChange K)
    simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange K) hf
  have hs' := additive_intertwining_over_algClosed (s := φ S) (t := ψ T) (f.baseChange K)
    (isSemisimple_baseChange hX.semisimple) (isSemisimple_baseChange hY.semisimple)
    (hcX.map φ) (hcY.map ψ) (by simpa only [map_sub] using hnX.map φ)
    (by simpa only [map_sub] using hnY.map ψ) hf'
  have hs : f.comp S = T.comp f := by
    apply LinearMap.baseChangeHom_injective k V (N := W) K
    change (f.comp S).baseChange K = (T.comp f).baseChange K
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    exact hs'
  refine ⟨hs, ?_⟩
  have hn : N = X - S := by rw [hX.sum, add_sub_cancel_left]
  have hm : M = Y - T := by rw [hY.sum, add_sub_cancel_left]
  rw [hn, hm, LinearMap.comp_sub, LinearMap.sub_comp, hf, hs]

open private isSemisimple_algHom tensor_factors_commute
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LinearJordanFactors

private theorem additiveJordan_tensorSum [PerfectField k] {V W : Type*}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {X S N : End k V} {Y T M : End k W}
    (hX : IsAdditiveJordanDecomposition X S N) (hY : IsAdditiveJordanDecomposition Y T M) :
    IsAdditiveJordanDecomposition (X.rTensor W + Y.lTensor V)
      (S.rTensor W + T.lTensor V) (N.rTensor W + M.lTensor V) := by
  let L := End.rTensorAlgHom k V W
  let R := End.lTensorAlgHom k W V
  change IsAdditiveJordanDecomposition (L X + R Y) (L S + R T) (L N + R M)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hX.sum, hY.sum, map_add, map_add]
    abel
  · exact ((hX.commute.map L).add_right (tensor_factors_commute S M)).add_left
      (((tensor_factors_commute N T).symm).add_right (hY.commute.map R))
  · exact (isSemisimple_algHom L hX.semisimple).add_of_commute
      (tensor_factors_commute S T) (isSemisimple_algHom R hY.semisimple)
  · exact (tensor_factors_commute N M).isNilpotent_add (hX.nilpotent.map L) (hY.nilpotent.map R)

private abbrev CoordinateSubcomodule (A : HopfAlgebraCategory k) :=
  (RightComodule.regular (k := k) (C := A)).FiniteSubcomodule

private theorem invariant_mem_subcomodule (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) (W : CoordinateSubcomodule A) (x : W.val) :
    D.val x.val ∈ W.val := by
  obtain ⟨t, ht⟩ := W.property.1 x
  change W.val.subtype.rTensor A t = Coalgebra.comul (R := k) x.val at ht
  change D.val.toLinearMap x.val ∈ W.val
  rw [invariant_eq_contract A D.val.toLinearMap D.property, ← ht]
  clear ht
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    change (Coalgebra.counit (R := k) (D.val b)) • a.val ∈ W.val
    exact W.val.smul_mem _ a.property
  | add a b ha hb => simpa only [map_add] using W.val.add_mem ha hb

private def restrictInvariant (A : HopfAlgebraCategory k) (D : InvariantDerivation A)
    (W : CoordinateSubcomodule A) : End k W.val :=
  D.val.toLinearMap.restrict fun x hx => invariant_mem_subcomodule A D W ⟨x, hx⟩

private def localJordan [PerfectField k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) (W : CoordinateSubcomodule A) :
    {p : End k W.val × End k W.val //
      IsAdditiveJordanDecomposition (restrictInvariant A D W) p.1 p.2} := by
  letI : FiniteDimensional k W.val := W.property.2
  exact Classical.choice (by
    obtain ⟨S, N, h⟩ := exists_additiveJordan (restrictInvariant A D W)
    exact ⟨⟨(S, N), h⟩⟩)

private theorem localJordan_mono [PerfectField k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) (W U : CoordinateSubcomodule A) (h : W.val ≤ U.val)
    (x : W.val) :
    ((localJordan A D W).val.1 x).val = ((localJordan A D U).val.1 (Submodule.inclusion h x)).val := by
  let : FiniteDimensional k W.val := W.property.2
  let : FiniteDimensional k U.val := U.property.2
  have hf : (Submodule.inclusion h).comp (restrictInvariant A D W) =
      (restrictInvariant A D U).comp (Submodule.inclusion h) := by
    exact LinearMap.ext fun x => Subtype.ext rfl
  have he := (additiveJordan_intertwining (localJordan A D W).property
    (localJordan A D U).property _ hf).1
  exact congrArg Subtype.val (LinearMap.congr_fun he x)

private def semisimpleOnCoordinates [PerfectField k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) : A → A := fun a =>
  let h := (RightComodule.regular (k := k) (C := A)).exists_finiteSubcomodule a
  ((localJordan A D h.choose).val.1 ⟨a, h.choose_spec⟩).val

private theorem semisimpleOnCoordinates_eq [PerfectField k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) (W : CoordinateSubcomodule A) (x : W.val) :
    semisimpleOnCoordinates A D x.val = ((localJordan A D W).val.1 x).val := by
  let ρ := RightComodule.regular (k := k) (C := A)
  let h := ρ.exists_finiteSubcomodule x.val
  obtain ⟨U, h₁, h₂⟩ := ρ.directed_finiteSubcomodules h.choose W
  exact (localJordan_mono A D h.choose U h₁ ⟨x.val, h.choose_spec⟩).trans
    (localJordan_mono A D W U h₂ x).symm

private def semisimpleCoordinateMap [PerfectField k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) : End k A where
  toFun := semisimpleOnCoordinates A D
  map_add' a b := by
    let ρ := RightComodule.regular (k := k) (C := A)
    obtain ⟨W, ha⟩ := ρ.exists_finiteSubcomodule a
    obtain ⟨U, hb⟩ := ρ.exists_finiteSubcomodule b
    obtain ⟨T, hW, hU⟩ := ρ.directed_finiteSubcomodules W U
    let a' : T.val := ⟨a, hW ha⟩
    let b' : T.val := ⟨b, hU hb⟩
    change semisimpleOnCoordinates A D (a' + b').val =
      semisimpleOnCoordinates A D a'.val + semisimpleOnCoordinates A D b'.val
    rw [semisimpleOnCoordinates_eq A D T (a' + b'), semisimpleOnCoordinates_eq A D T a',
      semisimpleOnCoordinates_eq A D T b', map_add]
    rfl
  map_smul' t a := by
    obtain ⟨W, ha⟩ := (RightComodule.regular (k := k) (C := A)).exists_finiteSubcomodule a
    let a' : W.val := ⟨a, ha⟩
    change semisimpleOnCoordinates A D (t • a').val = t • semisimpleOnCoordinates A D a'.val
    rw [semisimpleOnCoordinates_eq A D W (t • a'), semisimpleOnCoordinates_eq A D W a', map_smul]
    rfl

private theorem semisimpleCoordinateMap_intertwines [PerfectField k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {X S N : End k V} (hX : IsAdditiveJordanDecomposition X S N)
    (f : V →ₗ[k] A) (hf : f.comp X = D.val.toLinearMap.comp f) :
    (semisimpleCoordinateMap A D).comp f = f.comp S := by
  let b := Module.finBasis k V
  obtain ⟨W, hW⟩ := (RightComodule.regular (k := k) (C := A)).exists_finiteSubcomodule_containing_range
    (fun i => f (b i))
  have hm (v : V) : f v ∈ W.val := by
    rw [← b.sum_repr v, map_sum]
    exact W.val.sum_mem fun i _ => by rw [map_smul]; exact W.val.smul_mem _ (hW i)
  let g := f.codRestrict W.val hm
  have hg : g.comp X = (restrictInvariant A D W).comp g :=
    LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun hf x)
  let : FiniteDimensional k W.val := W.property.2
  have hs := (additiveJordan_intertwining hX (localJordan A D W).property g hg).1
  apply LinearMap.ext
  intro v
  change semisimpleOnCoordinates A D (g v).val = (g (S v)).val
  rw [semisimpleOnCoordinates_eq A D W (g v)]
  exact congrArg Subtype.val (LinearMap.congr_fun hs v).symm

private theorem semisimpleCoordinateMap_leibniz [PerfectField k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) (a b : A) :
    semisimpleCoordinateMap A D (a * b) =
      a * semisimpleCoordinateMap A D b + b * semisimpleCoordinateMap A D a := by
  let ρ := RightComodule.regular (k := k) (C := A)
  obtain ⟨W, ha⟩ := ρ.exists_finiteSubcomodule a
  obtain ⟨U, hb⟩ := ρ.exists_finiteSubcomodule b
  let : FiniteDimensional k W.val := W.property.2
  let : FiniteDimensional k U.val := U.property.2
  let f := (LinearMap.mul' k A).comp (TensorProduct.map W.val.subtype U.val.subtype)
  have he : f.comp ((restrictInvariant A D W).rTensor U.val +
      (restrictInvariant A D U).lTensor W.val) = D.val.toLinearMap.comp f := by
    apply TensorProduct.ext'
    intro x y
    change D.val x.val * y.val + x.val * D.val y.val = D.val (x.val * y.val)
    rw [D.val.leibniz, smul_eq_mul, smul_eq_mul, mul_comm y.val, add_comm]
  have hj := additiveJordan_tensorSum (localJordan A D W).property (localJordan A D U).property
  have hs := semisimpleCoordinateMap_intertwines A D hj f he
  let x : W.val := ⟨a, ha⟩
  let y : U.val := ⟨b, hb⟩
  have h := LinearMap.congr_fun hs (x ⊗ₜ[k] y)
  change semisimpleCoordinateMap A D (a * b) = f
    (((localJordan A D W).val.1.rTensor U.val + (localJordan A D U).val.1.lTensor W.val)
      (x ⊗ₜ[k] y)) at h
  rw [h, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_add]
  change ((localJordan A D W).val.1 x).val * b + a * ((localJordan A D U).val.1 y).val = _
  change _ = a * semisimpleOnCoordinates A D y.val + b * semisimpleOnCoordinates A D x.val
  rw [semisimpleOnCoordinates_eq A D W x, semisimpleOnCoordinates_eq A D U y,
    mul_comm b, add_comm]

private def coactionOperator (A : HopfAlgebraCategory k) {V : Type u}
    [AddCommGroup V] [Module k V] (D : InvariantDerivation A) (ρ : RightComodule k A V) : End k V :=
  (TensorProduct.rid k V).toLinearMap.comp
    ((((Coalgebra.counit (R := k)).comp D.val.toLinearMap).lTensor V).comp ρ.coaction)

open private coaction_contractRight map_contractRight from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ComoduleFiniteness

private theorem coactionOperator_intertwines (A : HopfAlgebraCategory k) {V : Type u}
    [AddCommGroup V] [Module k V] (D : InvariantDerivation A) (ρ : RightComodule k A V) :
    ρ.coaction.comp (coactionOperator A D ρ) = (D.val.toLinearMap.lTensor V).comp ρ.coaction := by
  let f : A →ₗ[k] k := (Coalgebra.counit (R := k)).comp D.val.toLinearMap
  have hD : D.val.toLinearMap = (contractRight A f).comp Coalgebra.comul :=
    LinearMap.ext (invariant_eq_contract A D.val.toLinearMap D.property)
  apply LinearMap.ext
  intro v
  have h := coaction_contractRight ρ f v
  change ρ.coaction (coactionOperator A D ρ v) =
    (contractRight A f).lTensor V ((Coalgebra.comul (R := k)).lTensor V (ρ.coaction v)) at h
  rw [← LinearMap.lTensor_comp_apply, ← hD] at h
  exact h

open private tensor_eq_sum_basis counit_basis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

private theorem semisimpleCoordinateMap_coaction [PerfectField k] (A : HopfAlgebraCategory k)
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : InvariantDerivation A) (ρ : RightComodule k A V) {S N : End k V}
    (h : IsAdditiveJordanDecomposition (coactionOperator A D ρ) S N) :
    ρ.coaction.comp S = ((semisimpleCoordinateMap A D).lTensor V).comp ρ.coaction := by
  let b := (Module.finBasis k V).reindex (Equiv.ulift.symm : _ ≃ ULift.{u} (Fin (finrank k V)))
  let t := RationalRepresentations.tensorCoordinate (C := A) b
  have ht (i) (F : End k A) : (t i).comp (F.lTensor V) = F.comp (t i) := by
    apply TensorProduct.ext'
    intro v a
    change b.coord i v • F a = F (b.coord i v • a)
    rw [map_smul]
  have hD := coactionOperator_intertwines A D ρ
  have hi (i) : ((t i).comp ρ.coaction).comp (coactionOperator A D ρ) =
      D.val.toLinearMap.comp ((t i).comp ρ.coaction) := by
    rw [LinearMap.comp_assoc, hD, ← LinearMap.comp_assoc, ht, LinearMap.comp_assoc]
  apply LinearMap.ext
  intro v
  change ρ.coaction (S v) = (semisimpleCoordinateMap A D).lTensor V (ρ.coaction v)
  rw [← tensor_eq_sum_basis b (ρ.coaction (S v)),
    ← tensor_eq_sum_basis b ((semisimpleCoordinateMap A D).lTensor V (ρ.coaction v))]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change t i (ρ.coaction (S v)) = ((t i).comp ((semisimpleCoordinateMap A D).lTensor V)) (ρ.coaction v)
  rw [ht]
  exact (LinearMap.congr_fun (semisimpleCoordinateMap_intertwines A D h _ (hi i)) v).symm

private theorem semisimpleCoordinateMap_invariant [PerfectField k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) : IsInvariant A (semisimpleCoordinateMap A D) := by
  let ρ := RightComodule.regular (k := k) (C := A)
  let δ : A →ₗ[k] A ⊗[k] A := Coalgebra.comul
  let F := semisimpleCoordinateMap A D
  apply LinearMap.ext
  intro a
  obtain ⟨W, ha⟩ := ρ.exists_finiteSubcomodule a
  let : FiniteDimensional k W.val := W.property.2
  obtain ⟨σ, hσ⟩ := (ρ.isSubcomodule_iff_exists_coaction W.val).mp W.property.1
  let i := W.val.subtype
  have hσ' (v : W.val) : i.rTensor A (σ.coaction v) = δ (i v) := LinearMap.congr_fun hσ v
  obtain ⟨S, N, h⟩ := exists_additiveJordan (coactionOperator A D σ)
  have hi : i.comp (coactionOperator A D σ) = D.val.toLinearMap.comp i := by
    let εD : A →ₗ[k] k := Coalgebra.counit.comp D.val.toLinearMap
    apply LinearMap.ext
    intro v
    have hv := map_contractRight εD i (σ.coaction v)
    change i (coactionOperator A D σ v) = (contractRight A εD) (i.rTensor A (σ.coaction v)) at hv
    rw [hσ', ← invariant_eq_contract A D.val.toLinearMap D.property] at hv
    exact hv
  have hF := semisimpleCoordinateMap_intertwines A D h i hi
  have hS := semisimpleCoordinateMap_coaction A D σ h
  let v : W.val := ⟨a, ha⟩
  change δ (F (i v)) = F.lTensor A (δ (i v))
  calc
    δ (F (i v)) = δ (i (S v)) := congrArg δ (LinearMap.congr_fun hF v)
    _ = i.rTensor A (σ.coaction (S v)) := (hσ' _).symm
    _ = i.rTensor A (F.lTensor W.val (σ.coaction v)) :=
      congrArg (i.rTensor A) (LinearMap.congr_fun hS v)
    _ = F.lTensor A (δ (i v)) := by
      rw [← hσ']
      exact (LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor W.val i F) _).trans
        (LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor W.val i F) _).symm

private def semisimpleDerivation [PerfectField k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) : InvariantDerivation A := by
  let S := semisimpleCoordinateMap A D
  have h := semisimpleCoordinateMap_leibniz A D
  refine ⟨⟨S, ?_, fun a b => h a b⟩, semisimpleCoordinateMap_invariant A D⟩
  have h₁ : S 1 = S 1 + S 1 := by simpa only [one_mul] using h 1 1
  exact add_left_cancel (by simpa only [add_zero] using h₁ : S 1 + 0 = S 1 + S 1) |>.symm

private def nilpotentDerivation [PerfectField k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A) : InvariantDerivation A := by
  let S := semisimpleDerivation A D
  refine ⟨D.val - S.val, ?_⟩
  have hD := D.property
  have hS := S.property
  unfold IsInvariant at hD hS ⊢
  change (Coalgebra.comul (R := k)).comp (D.val.toLinearMap - S.val.toLinearMap) =
    ((D.val.toLinearMap - S.val.toLinearMap).lTensor A).comp (Coalgebra.comul (R := k))
  rw [LinearMap.comp_sub, LinearMap.lTensor_sub, LinearMap.sub_comp, hD, hS]

private theorem coactionOperator_matrix (A : HopfAlgebraCategory k)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (D : InvariantDerivation A)
    (M : Matrix ι ι A) (hM : RationalRepresentations.IsCoactionMatrix A M) :
    coactionOperator A D (RationalRepresentations.coactionOfMatrix A (Pi.basisFun k ι) M hM) =
      Matrix.toLinAlgEquiv' (matrixAction A M D) := by
  let b := Pi.basisFun k ι
  let ρ := RationalRepresentations.coactionOfMatrix A b M hM
  apply b.ext
  intro j
  have h := RationalRepresentations.coaction_apply_basis A b ρ j
  rw [RationalRepresentations.coefficients_coactionOfMatrix] at h
  change TensorProduct.rid k (ι → k)
      (((Coalgebra.counit (R := k)).comp D.val.toLinearMap).lTensor _ (ρ.coaction (b j))) = _
  rw [h, Matrix.toLinAlgEquiv'_apply]
  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, LinearMap.comp_apply,
    b, Pi.basisFun_apply, Matrix.mulVec_single_one]
  ext i
  simp [matrixAction, Pi.single_apply, Matrix.col_apply]

theorem characteristicZeroJordan : CharacteristicZeroJordan.{u} := by
  intro k _ _ A D
  let S := semisimpleDerivation A D
  let N := nilpotentDerivation A D
  refine ⟨S, N, ?_, ?_⟩
  · change D.val = S.val + (D.val - S.val)
    abel
  · intro ι _ _ M hM
    let b := Pi.basisFun k ι
    let ρ := RationalRepresentations.coactionOfMatrix A b M hM
    rw [← coactionOperator_matrix A D M hM, ← coactionOperator_matrix A S M hM,
      ← coactionOperator_matrix A N M hM]
    obtain ⟨s, n, hj⟩ := exists_additiveJordan (coactionOperator A D ρ)
    have hs := semisimpleCoordinateMap_coaction A D ρ hj
    have hse : coactionOperator A S ρ = s := by
      let C := (TensorProduct.rid k (ι → k)).toLinearMap.comp
        ((Coalgebra.counit (R := k) (A := A)).lTensor (ι → k))
      apply LinearMap.ext
      intro v
      have h := congrArg C (LinearMap.congr_fun hs v)
      change C (ρ.coaction (s v)) = C (S.val.toLinearMap.lTensor (ι → k) (ρ.coaction v)) at h
      have hc : C (ρ.coaction (s v)) = s v := ρ.counit (s v)
      rw [hc] at h
      change (TensorProduct.rid k (ι → k))
        (((Coalgebra.counit (R := k)).comp S.val.toLinearMap).lTensor (ι → k) (ρ.coaction v)) = s v
      rw [LinearMap.lTensor_comp_apply]
      exact h.symm
    have hne : coactionOperator A N ρ = n := by
      rw [show n = coactionOperator A D ρ - s by rw [hj.sum, add_sub_cancel_left], ← hse]
      have hN : N.val.toLinearMap = D.val.toLinearMap - S.val.toLinearMap := rfl
      simp only [coactionOperator, hN, LinearMap.comp_sub, LinearMap.lTensor_sub, LinearMap.sub_comp]
    exact hse.symm ▸ hne.symm ▸ hj

private theorem perfectField_jordan_in_submodule [PerfectField k] {V : Type u}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (p : ℕ) [Fact p.Prime] [CharP k p] (W : Submodule k (End k V)) (X : End k V)
    (hp : ∀ r : ℕ, X ^ (p ^ r) ∈ W) : ∃ S ∈ W, ∃ N ∈ W, IsAdditiveJordanDecomposition X S N := by
  let K := AlgebraicClosure k
  let : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  let α := TensorProduct.mk k K V 1
  have j : IsBaseChange K α := IsBaseChange.of_equiv (LinearEquiv.refl K _) fun _ => rfl
  let e := j.end.equiv
  have he (T : End k V) : e (1 ⊗ₜ[k] T) = T.baseChange K := by
    rw [IsBaseChange.equiv_tmul, one_smul]
    apply LinearMap.ext
    intro z
    induction z using j.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | smul c x hx => simp [hx]
    | tmul v => rw [IsBaseChange.endHom_comp_apply]; rfl
  obtain ⟨S, N, hj⟩ := exists_additiveJordan X
  have hv : ∀ r : ℕ, (X.baseChange K) ^ (p ^ r) ∈ (W.baseChange K).map e.toLinearMap := by
    intro r
    have hpow : (X ^ (p ^ r)).baseChange K = X.baseChange K ^ (p ^ r) :=
      (End.baseChangeHom k K V).map_pow X _
    rw [← hpow, ← he]
    exact Submodule.mem_map_of_mem ((membershipDescends k K _ W _).mpr (hp r))
  have hs := semisimple_mem_of_primePowers p ((W.baseChange K).map e.toLinearMap)
    (additiveJordan_baseChange (K := K) hj) hv
  rw [← he] at hs
  obtain ⟨q, hq, hqe⟩ := hs
  have hS := (membershipDescends k K _ W S).mp (e.injective hqe ▸ hq)
  have hx : X ∈ W := by simpa using hp 0
  have hN : N = X - S := by rw [hj.sum, add_sub_cancel_left]
  exact ⟨S, hS, N, hN ▸ W.sub_mem hx hS, hj⟩

private def invariantSubmodule (A : HopfAlgebraCategory k) : Submodule k (Derivation k A A) where
  carrier := {D | IsInvariant A D.toLinearMap}
  zero_mem' := by simp [IsInvariant]
  add_mem' := by
    intro D E hD hE
    change IsInvariant A D.toLinearMap at hD
    change IsInvariant A E.toLinearMap at hE
    change IsInvariant A (D.toLinearMap + E.toLinearMap)
    unfold IsInvariant at hD hE ⊢
    rw [LinearMap.comp_add, LinearMap.lTensor_add, LinearMap.add_comp, hD, hE]
  smul_mem' := by
    intro c D hD
    change IsInvariant A D.toLinearMap at hD
    change IsInvariant A (c • D.toLinearMap)
    unfold IsInvariant at hD ⊢
    rw [LinearMap.comp_smul, LinearMap.lTensor_smul, LinearMap.smul_comp, hD]

private def matrixActionLinear (A : HopfAlgebraCategory k) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) :
    invariantSubmodule A →ₗ[k] End k (ι → k) :=
  let f : invariantSubmodule A →ₗ[k] Matrix ι ι k :=
    { toFun := fun D => matrixAction A M ⟨D.val, D.property⟩
      map_add' := fun D E => Matrix.ext fun i j =>
        (Coalgebra.counit (R := k) (A := A)).map_add (D.val (M i j)) (E.val (M i j))
      map_smul' := fun c D => Matrix.ext fun i j => by
        change (Coalgebra.counit (R := k)) (c • D.val (M i j)) =
          c • (Coalgebra.counit (R := k)) (D.val (M i j))
        exact (Coalgebra.counit (R := k) (A := A)).map_smul c (D.val (M i j)) }
  Matrix.toLinAlgEquiv'.toLinearMap.comp f

private theorem perfectFieldMatrixJordan [PerfectField k] (A : HopfAlgebraCategory k) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (hM : RationalRepresentations.IsCoactionMatrix A M)
    (D : InvariantDerivation A) : ∃ S N : InvariantDerivation A,
    IsAdditiveJordanDecomposition (Matrix.toLinAlgEquiv' (matrixAction A M D))
      (Matrix.toLinAlgEquiv' (matrixAction A M S)) (Matrix.toLinAlgEquiv' (matrixAction A M N)) := by
  rcases CharP.exists' k with hk | ⟨p, hp, hkp⟩
  · let := hk
    obtain ⟨S, N, _, h⟩ := characteristicZeroJordan k A D
    exact ⟨S, N, h ι M hM⟩
  · let := hp
    let := hkp
    let f := matrixActionLinear A M
    have hpow (r : ℕ) : (Matrix.toLinAlgEquiv' (matrixAction A M D)) ^ (p ^ r) ∈ LinearMap.range f := by
      obtain ⟨E, _, hE⟩ := restrictedIteratedMatrixAction k A p r ι M hM D
      refine ⟨⟨E.val, E.property⟩, ?_⟩
      change Matrix.toLinAlgEquiv' (matrixAction A M E) = _
      rw [hE, map_pow]
    obtain ⟨_, ⟨S, rfl⟩, _, ⟨N, rfl⟩, h⟩ := perfectField_jordan_in_submodule p (LinearMap.range f) _ hpow
    exact ⟨⟨S.val, S.property⟩, ⟨N.val, N.property⟩, h⟩

private def tangentComparison (A : HopfAlgebraCategory k) (G : Specs.GroupScheme k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G) : InvariantDerivation A ≃ Specs.Lie k G :=
  (invariantDerivationLifts k A).choose.trans ((hopfKernelLifts A).symm.trans (dualKernelIso e).toEquiv)

private theorem tangentComparison_matrix (A : HopfAlgebraCategory k) (G : AffineGroupCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (L : Specs.GroupScheme k)
    (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L) (D : InvariantDerivation A) :
    InfinitesimalCommutator.matrixDifferential f l (tangentComparison A G.val e D) =
      matrixAction A (RationalRepresentations.universalMatrix A G L e l f) D :=
  matrixDifferentialComparison k G A e ι L l f D _ (fun a =>
    congrArg TrivSqZeroExt.snd ((invariantDerivationLifts k A).choose_spec D a))

private theorem universalMatrix_coaction (A : HopfAlgebraCategory k) (G : AffineGroupCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (L : Specs.GroupScheme k)
    (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L) :
    RationalRepresentations.IsCoactionMatrix A (RationalRepresentations.universalMatrix A G L e l f) := by
  let b := Pi.basisFun k ι
  obtain ⟨eqv, heqv⟩ := RationalRepresentations.representationCoactionComparison A b G L e l
  rw [← heqv f]
  exact RationalRepresentations.coefficients_isCoactionMatrix A b (eqv f)

theorem perfectFieldLieJordan : PerfectFieldLieJordan.{u} := by
  intro k _ _ G A e ι _ _ L l f x
  let q := tangentComparison A G.val e
  obtain ⟨D, rfl⟩ := q.surjective x
  let M := RationalRepresentations.universalMatrix A G L e l f
  obtain ⟨S, N, h⟩ := perfectFieldMatrixJordan A M (universalMatrix_coaction A G e L l f) D
  exact ⟨q S, q N, by simpa only [q, tangentComparison_matrix] using h⟩

theorem characteristicZeroLieJordan : CharacteristicZeroLieJordan.{u} := by
  intro k _ _ G A e x
  let q := tangentComparison A G.val e
  obtain ⟨D, rfl⟩ := q.surjective x
  obtain ⟨S, N, _, h⟩ := characteristicZeroJordan k A D
  refine ⟨q S, q N, fun ι _ _ L l f => ?_⟩
  simpa only [q, tangentComparison_matrix] using
    h ι _ (universalMatrix_coaction A G e L l f)

end AdditiveJordan

section Centralizer

open Algebra HopfAlgebra

private theorem convolution_centralizes_mul (A : HopfAlgebraCategory k)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A)
    (Y : Matrix ι ι k) (hM : RationalRepresentations.IsCoactionMatrix A M)
    {R : Type u} [CommRing R] [Algebra k R] {g h : A →ₐ[k] R}
    (hg : CentralizesMatrix A M Y g) (hh : CentralizesMatrix A M Y h) :
    CentralizesMatrix A M Y ((toConv g * toConv h).ofConv) := by
  let c := (RationalRepresentations.matrixPointHom A M hM).app (CommAlgCat.of k R)
  have hc := congrArg Units.val (c.hom.map_mul (toConv g) (toConv h))
  change ((toConv g * toConv h).ofConv).mapMatrix M = g.mapMatrix M * h.mapMatrix M at hc
  change Commute (((toConv g * toConv h).ofConv).mapMatrix M) (Y.map (algebraMap k R))
  rw [hc]
  exact hg.mul_left hh

private theorem convolution_centralizes_inv (A : HopfAlgebraCategory k)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A)
    (Y : Matrix ι ι k) (hM : RationalRepresentations.IsCoactionMatrix A M)
    {R : Type u} [CommRing R] [Algebra k R] {g : A →ₐ[k] R}
    (hg : CentralizesMatrix A M Y g) : CentralizesMatrix A M Y (g.comp (antipodeAlgHom k A)) := by
  let c := (RationalRepresentations.matrixPointHom A M hM).app (CommAlgCat.of k R)
  let : Group (WithConv (A →ₐ[k] R)) := convolutionGroup A (CommAlgCat.of k R)
  have hc := congrArg Units.val (c.hom.map_inv (toConv g))
  change (g.comp (antipodeAlgHom k A)).mapMatrix M = (c (toConv g))⁻¹.val at hc
  change Commute ((g.comp (antipodeAlgHom k A)).mapMatrix M) (Y.map (algebraMap k R))
  rw [hc]
  have h : Commute (c (toConv g)).val (Y.map (algebraMap k R)) := hg
  exact h.units_inv_left

theorem matrixCentralizerHopf : MatrixCentralizerHopf.{u} := by
  intro k _ A ι _ _ M Y hM
  let J := centralizerIdeal A M Y
  let q := Ideal.Quotient.mkₐ k J
  have hε : CentralizesMatrix A M Y (counitAlgHom k A) := by
    change Commute ((counitAlgHom k A).mapMatrix M) _
    have h : (counitAlgHom k A).mapMatrix M = 1 := Matrix.ext hM.counit
    rw [h]
    exact Commute.one_left _
  have hq : CentralizesMatrix A M Y q :=
    (centralizesMatrix_iff_ideal_le_ker A M Y q).mpr
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  have hh {R : Type u} [CommRing R] [Algebra k R]
      (f : (A ⧸ J) →ₐ[k] R) : CentralizesMatrix A M Y (f.comp q) :=
    (centralizesMatrix_iff_ideal_le_ker A M Y _).mpr fun a ha => by
      change f (q a) = 0
      rw [show q a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  let B := A ⧸ J
  let l : B →ₐ[k] B ⊗[k] B := Algebra.TensorProduct.includeLeft
  let r : B →ₐ[k] B ⊗[k] B := Algebra.TensorProduct.includeRight
  have hδ := convolution_centralizes_mul A M Y hM (hh l) (hh r)
  have hprod : ((toConv (l.comp q) * toConv (r.comp q)).ofConv) =
      (Algebra.TensorProduct.map q q).comp (comulAlgHom k A) := by
    apply AlgHom.ext
    intro a
    rw [show ((toConv (l.comp q) * toConv (r.comp q)).ofConv : A →ₐ[k] B ⊗[k] B) a =
      (toConv (l.comp q) * toConv (r.comp q)) a from rfl, AlgHom.convMul_apply]
    have h : Algebra.TensorProduct.lift (l.comp q) (r.comp q) (fun _ _ => Commute.all _ _) =
        Algebra.TensorProduct.map q q := by ext a <;> simp [l, r]
    rw [h]
    rfl
  rw [hprod] at hδ
  have hS := convolution_centralizes_inv A M Y hM hq
  refine { toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_ }
  · exact (centralizesMatrix_iff_ideal_le_ker A M Y _).mp hε
  · intro a ha
    exact (centralizesMatrix_iff_ideal_le_ker A M Y _).mp hδ ha
  · intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((centralizesMatrix_iff_ideal_le_ker A M Y _).mp hS ha)

private def derivationOfIdentityLift (A : HopfAlgebraCategory k)
    (f : A →ₐ[k] DualNumber A) (hf : ∀ a, (f a).fst = a) : Derivation k A A where
  toLinearMap := ((TrivSqZeroExt.sndHom (R := A) (M := A)).restrictScalars k).comp f.toLinearMap
  map_one_eq_zero' := by
    change (f 1).snd = 0
    rw [map_one]
    rfl
  leibniz' a b := by
    change (f (a * b)).snd = a • (f b).snd + b • (f a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hf, hf]
    simp [smul_eq_mul, mul_comm, add_comm]

private def extendDualToCoordinates (A : HopfAlgebraCategory k) : DualNumber k →ₐ[k] DualNumber A where
  toRingHom := InfinitesimalCommutator.mapCoefficients (algebraMap k A)
  commutes' t := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact map_zero (algebraMap k A)

private theorem conjugation_derivation (A : HopfAlgebraCategory k)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A)
    (hM : RationalRepresentations.IsCoactionMatrix A M) (D : InvariantDerivation A) :
    ∃ C : Derivation k A A,
      (∀ i j, C (M i j) =
        ((matrixAction A M D).map (algebraMap k A) * M -
          M * (matrixAction A M D).map (algebraMap k A)) i j) ∧ C M.det = 0 := by
  obtain ⟨g, hg⟩ := invariantDerivationLifts k A
  let u := TrivSqZeroExt.inlAlgHom k A A
  let v := (extendDualToCoordinates A).comp (g D).val
  let P : A →ₐ[k] DualNumber A := (toConv v * toConv u).ofConv
  let Q : A →ₐ[k] DualNumber A := (toConv u * toConv v).ofConv
  let fst := TrivSqZeroExt.fstHom k A A
  have hu : fst.comp u = AlgHom.id k A := rfl
  have hv : fst.comp v = (1 : WithConv (A →ₐ[k] A)).ofConv := by
    ext a
    exact congrArg (fun z : k × k => algebraMap k A z.1) (hg D a)
  have hP (a : A) : (P a).fst = a := by
    change (fst.comp (toConv v * toConv u).ofConv) a = _
    rw [AlgHom.comp_convMul_distrib, hu, hv, toConv_ofConv, one_mul]
    rfl
  have hQ (a : A) : (Q a).fst = a := by
    change (fst.comp (toConv u * toConv v).ofConv) a = _
    rw [AlgHom.comp_convMul_distrib, hu, hv, toConv_ofConv, mul_one]
    rfl
  let C := derivationOfIdentityLift A P hP - derivationOfIdentityLift A Q hQ
  let θ := (RationalRepresentations.matrixPointHom A M hM).app (CommAlgCat.of k (DualNumber A))
  have hp := congrArg Units.val (θ.hom.map_mul (toConv v) (toConv u))
  have hq := congrArg Units.val (θ.hom.map_mul (toConv u) (toConv v))
  change P.mapMatrix M = v.mapMatrix M * u.mapMatrix M at hp
  change Q.mapMatrix M = u.mapMatrix M * v.mapMatrix M at hq
  have hvs (i j : ι) : (v (M i j)).snd = algebraMap k A (matrixAction A M D i j) :=
    congrArg (fun z : k × k => algebraMap k A z.2) (hg D (M i j))
  refine ⟨C, ?_, ?_⟩
  · intro i j
    change (P.mapMatrix M i j).snd - (Q.mapMatrix M i j).snd = _
    rw [hp, hq]
    have h₁ : ((v.mapMatrix M * u.mapMatrix M) i j).snd =
        ((matrixAction A M D).map (algebraMap k A) * M) i j := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      change (TrivSqZeroExt.sndHom (R := A) (M := A)) (∑ l, v (M i l) * u (M l j)) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by
        change (v (M i l) * TrivSqZeroExt.inl (M l j)).snd = _
        simp [TrivSqZeroExt.snd_mul, hvs, mul_comm]
    have h₂ : ((u.mapMatrix M * v.mapMatrix M) i j).snd =
        (M * (matrixAction A M D).map (algebraMap k A)) i j := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      change (TrivSqZeroExt.sndHom (R := A) (M := A)) (∑ l, u (M i l) * v (M l j)) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by
        change (TrivSqZeroExt.inl (M i l) * v (M l j)).snd = _
        simp [TrivSqZeroExt.snd_mul, hvs]
    exact congrArg₂ (· - ·) h₁ h₂
  · have hdet : P M.det = Q M.det := by
      rw [AlgHom.map_det, AlgHom.map_det, hp, hq, Matrix.det_mul, Matrix.det_mul, mul_comm]
    change (P M.det).snd - (Q M.det).snd = 0
    rw [hdet, sub_self]

private theorem derivation_mul_mem_eigenspace {A : Type*} [CommRing A] [Algebra k A]
    (C : Derivation k A A) {a b : A} {s t : k}
    (ha : a ∈ Module.End.eigenspace C.toLinearMap s)
    (hb : b ∈ Module.End.eigenspace C.toLinearMap t) :
    a * b ∈ Module.End.eigenspace C.toLinearMap (s + t) := by
  rw [Module.End.mem_eigenspace_iff]
  change C (a * b) = _
  rw [C.leibniz, show C a = s • a from Module.End.mem_eigenspace_iff.mp ha,
    show C b = t • b from Module.End.mem_eigenspace_iff.mp hb, add_smul,
    smul_eq_mul, smul_eq_mul, mul_smul_comm, mul_smul_comm, mul_comm b a, add_comm]

private def eigenspaceAlgebra {A : Type*} [CommRing A] [Algebra k A]
    (C : Derivation k A A) : Subalgebra k A where
  carrier := (⨆ w : k, Module.End.eigenspace C.toLinearMap w : Submodule k A)
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  mul_mem' := by
    intro a b ha hb
    let E := Module.End.eigenspace C.toLinearMap
    have hzero : (0 : A) ∈ ⨆ w, E w := Submodule.zero_mem _
    refine Submodule.iSup_induction E (motive := fun a => a * b ∈ ⨆ w, E w) ha ?_
      (by simpa only [zero_mul] using hzero) ?_
    · intro s x hx
      refine Submodule.iSup_induction E (motive := fun b => x * b ∈ ⨆ w, E w) hb ?_
        (by simpa only [mul_zero] using hzero) ?_
      · intro t y hy
        exact le_iSup E (s + t) (derivation_mul_mem_eigenspace C hx hy)
      · intro y z hy hz
        rw [mul_add]
        exact Submodule.add_mem _ hy hz
    · intro x y hx hy
      rw [add_mul]
      exact Submodule.add_mem _ hx hy
  algebraMap_mem' c := by
    apply le_iSup (Module.End.eigenspace C.toLinearMap) 0
    rw [Module.End.mem_eigenspace_iff]
    change C (algebraMap k A c) = _
    simp

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem trace_coefficients_in_eigenspaceAlgebra [IsAlgClosed k]
    (A : HopfAlgebraCategory k) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (Y : Matrix ι ι k) (hY : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' Y))
    (C : Derivation k A A)
    (hC : ∀ i j, C (M i j) = (Y.map (algebraMap k A) * M - M * Y.map (algebraMap k A)) i j) :
    ∀ i j, M i j ∈ eigenspaceAlgebra C := by
  let b : Matrix ι ι k →ₐ[k] Matrix ι ι A := (Algebra.ofId k A).mapMatrix
  let f := (Matrix.traceLinearMap (α := k) (R := A) (n := ι)).comp
    ((LinearMap.mulRight k M).comp b.toLinearMap)
  let T := -(LieAlgebra.ad k (Matrix ι ι k) Y)
  let e : Matrix ι ι k ≃ₐ[k] Module.End k (ι → k) := Matrix.toLinAlgEquiv'
  have he : e.toLinearMap.comp (LieAlgebra.ad k (Matrix ι ι k) Y) =
      (LieAlgebra.ad k (Module.End k (ι → k)) (e Y)).comp e.toLinearMap := by
    apply LinearMap.ext
    intro P
    change e (Y * P - P * Y) = e Y * e P - e P * e Y
    simp
  have hT : T.IsSemisimple := Module.End.isSemisimple_neg.mpr
    ((e.toLinearEquiv.isSemisimple_iff _ _ he).mpr (LieAlgebra.ad_isSemisimple_of_isSemisimple hY))
  have h (P : Matrix ι ι k) : C (f P) = f (T P) := by
    change C ((b P * M).trace) = (b (-(Y * P - P * Y)) * M).trace
    have hc : C ((b P * M).trace) =
        (b P * (b Y * M - M * b Y)).trace := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change C (algebraMap k A (P i j) * M j i) =
        algebraMap k A (P i j) * (b Y * M - M * b Y) j i
      calc
        C (algebraMap k A (P i j) * M j i) = algebraMap k A (P i j) * C (M j i) := by
          simp [C.leibniz, smul_eq_mul]
        _ = _ := congrArg (algebraMap k A (P i j) * ·) (hC j i)
    rw [hc, neg_sub, map_sub, map_mul, map_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.trace_sub, Matrix.trace_sub]
    congr 1
    · rw [Matrix.mul_assoc]
    · rw [Matrix.trace_mul_cycle', Matrix.mul_assoc]
  have hf (P : Matrix ι ι k) : f P ∈ eigenspaceAlgebra C := by
    have hp : P ∈ ⨆ w : k, T.eigenspace w := hT.iSup_eigenspace_eq_top.symm ▸ Submodule.mem_top
    refine Submodule.iSup_induction T.eigenspace (motive := fun P => f P ∈ eigenspaceAlgebra C) hp ?_
      (by rw [map_zero]; exact (eigenspaceAlgebra C).zero_mem) ?_
    · intro w P hp
      apply le_iSup (Module.End.eigenspace C.toLinearMap) w
      rw [Module.End.mem_eigenspace_iff]
      change C (f P) = _
      rw [h, Module.End.mem_eigenspace_iff.mp hp, map_smul]
    · intro P Q hP hQ
      rw [map_add]
      exact (eigenspaceAlgebra C).add_mem hP hQ
  intro i j
  have hsingle := hf (Matrix.single j i 1)
  change (b (Matrix.single j i 1) * M).trace ∈ eigenspaceAlgebra C at hsingle
  rwa [show b (Matrix.single j i 1) = Matrix.single j i 1 by
      change (Matrix.single j i (1 : k)).map (algebraMap k A) = _
      rw [Matrix.map_single _ _ _ (algebraMap k A), map_one], Matrix.trace_single_mul, one_smul] at hsingle

open private unitMatrix from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

private theorem derivation_inverse_det (A : HopfAlgebraCategory k) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A)
    (hM : RationalRepresentations.IsCoactionMatrix A M) (C : Derivation k A A) (hc : C M.det = 0) :
    C (M.det⁻¹ʳ) = 0 := by
  have hunit : IsUnit M.det := (Matrix.GeneralLinearGroup.det (unitMatrix A M hM)).isUnit
  have h := C.leibniz M.det (M.det⁻¹ʳ)
  rw [Ring.mul_inverse_cancel _ hunit, C.map_one_eq_zero, hc, smul_zero, add_zero, smul_eq_mul] at h
  exact hunit.mul_left_cancel (h.symm.trans (mul_zero _).symm)

private theorem centralizerIdeal_eq_span_derivation (A : HopfAlgebraCategory k) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (Y : Matrix ι ι k)
    (hgen : MatrixGeneratesCoordinates A M) (C : Derivation k A A)
    (hC : ∀ i j, C (M i j) = (Y.map (algebraMap k A) * M - M * Y.map (algebraMap k A)) i j)
    (hdet : C (M.det⁻¹ʳ) = 0) : centralizerIdeal A M Y = Ideal.span (Set.range C) := by
  let J := centralizerIdeal A M Y
  have hneg (i j : ι) : (M * Y.map (algebraMap k A) - Y.map (algebraMap k A) * M) i j = -C (M i j) := by
    rw [hC, ← Matrix.neg_apply, neg_sub]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change (M * Y.map (algebraMap k A) - Y.map (algebraMap k A) * M) i j ∈ _
    rw [hneg]
    exact (Ideal.span (Set.range C)).neg_mem (Ideal.subset_span (Set.mem_range_self _))
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have ha : a ∈ Algebra.adjoin k (Set.range (fun ij : ι × ι => M ij.1 ij.2) ∪ {M.det⁻¹ʳ}) :=
      hgen.symm ▸ (show a ∈ (⊤ : Subalgebra k A) from trivial)
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨⟨i, j⟩, rfl⟩ | hx
      · have h := (Ideal.subset_span (Set.mem_range_self (i, j)) :
            (M * Y.map (algebraMap k A) - Y.map (algebraMap k A) * M) i j ∈ J)
        rw [hneg] at h
        exact J.neg_mem_iff.mp h
      · rw [Set.mem_singleton_iff.mp hx, hdet]
        exact J.zero_mem
    | algebraMap c => simp
    | add a b _ _ ha hb => rw [map_add]; exact J.add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [C.leibniz, smul_eq_mul, smul_eq_mul]
      exact J.add_mem (J.mul_mem_left _ hb) (J.mul_mem_left _ ha)

private theorem conjugation_eigenspace_decomposition [IsAlgClosed k]
    (A : HopfAlgebraCategory k) {ι : Type u} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A)
    (hM : RationalRepresentations.IsCoactionMatrix A M) (hgen : MatrixGeneratesCoordinates A M)
    (D : InvariantDerivation A) (hY : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (matrixAction A M D))) :
    ∃ C : Derivation k A A, (⨆ w : k, Module.End.eigenspace C.toLinearMap w) = ⊤ ∧
      centralizerIdeal A M (matrixAction A M D) = Ideal.span (Set.range C) := by
  obtain ⟨C, hC, hc⟩ := conjugation_derivation A M hM D
  have hdet := derivation_inverse_det A M hM C hc
  refine ⟨C, ?_, centralizerIdeal_eq_span_derivation A M _ hgen C hC hdet⟩
  have hm := trace_coefficients_in_eigenspaceAlgebra A M _ hY C hC
  have htop : (⊤ : Subalgebra k A) ≤ eigenspaceAlgebra C := by
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro _ (⟨⟨i, j⟩, rfl⟩ | hx)
    · exact hm i j
    · rw [Set.mem_singleton_iff.mp hx]
      apply le_iSup (Module.End.eigenspace C.toLinearMap) 0
      rw [Module.End.mem_eigenspace_iff]
      exact hdet.trans (zero_smul _ _).symm
  exact congrArg Subalgebra.toSubmodule (le_antisymm le_top htop)

theorem splitMatrixCentralizerSmooth : SplitMatrixCentralizerSmooth.{u} := by
  intro k _ _ A _ ι _ _ M hM hgen D hY
  obtain ⟨C, hspan, hJ⟩ := conjugation_eigenspace_decomposition A M hM hgen D hY
  rw [hJ]
  exact smoothDiagonalizableDerivationQuotient k A C hspan

open private restrictCoordinateEquiv isCoactionMatrix_extension
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

private theorem matrixAction_extension (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) {ι : Type u} (M : Matrix ι ι A) (D : InvariantDerivation A) :
    ∃ D' : InvariantDerivation (extendHopf K A),
      matrixAction (extendHopf K A) (fun i j => (1 : K) ⊗ₜ[k] M i j) D' =
        (matrixAction A M D).map (algebraMap k K) := by
  let B := extendHopf K A
  let R := CommAlgCat.of K (DualNumber K)
  obtain ⟨g, hg⟩ := invariantDerivationLifts k A
  let R₀ := (restrictTestAlgebra k K).obj R
  let : Algebra k R₀ := R₀.algebra
  let f : A →ₐ[k] R₀ := (extendDualNumber K).hom.comp (g D).val
  let E := restrictCoordinateEquiv A K R
  let G := E.symm f
  have hG (a : A) : G ((1 : K) ⊗ₜ[k] a) = f a := by
    exact DFunLike.congr_fun (E.apply_symm_apply f) a
  have hred : (TrivSqZeroExt.fstHom K K K).comp G = counitAlgHom K B := by
    apply Algebra.TensorProduct.ext (R := k) (S := K)
    · ext
    · apply AlgHom.ext
      intro a
      change (G ((1 : K) ⊗ₜ[k] a)).fst = Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[k] a)
      rw [hG, TensorProduct.counit_tmul, Bialgebra.counit_one, Algebra.smul_def, mul_one]
      exact congrArg (fun z : DualNumber k => algebraMap k K z.fst) (hg D a)
  let H : Specs.AdvCommAlg.Differentials.Tangent.PointLifts K B K (counitAlgHom K B) := ⟨G, hred⟩
  obtain ⟨w, hw⟩ := invariantDerivationLifts K B
  obtain ⟨D', hD'⟩ := w.surjective H
  refine ⟨D', Matrix.ext fun i j => ?_⟩
  have h := congrArg TrivSqZeroExt.snd (hw D' ((1 : K) ⊗ₜ[k] M i j))
  rw [hD'] at h
  change (G ((1 : K) ⊗ₜ[k] M i j)).snd = _ at h
  rw [hG] at h
  exact h.symm.trans (congrArg (fun z : DualNumber k => algebraMap k K z.snd) (hg D (M i j)))

private theorem algHom_map_inverse {B C : Type*} [CommRing B] [CommRing C]
    [Algebra k B] [Algebra k C] (f : B →ₐ[k] C) (a : B) (ha : IsUnit a) :
    f (a⁻¹ʳ) = (f a)⁻¹ʳ := by
  apply (ha.map f).mul_left_cancel
  rw [← map_mul, Ring.mul_inverse_cancel a ha, map_one, Ring.mul_inverse_cancel _ (ha.map f)]

private theorem generatesCoordinates_extension (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (hM : RationalRepresentations.IsCoactionMatrix A M)
    (hgen : MatrixGeneratesCoordinates A M) :
    MatrixGeneratesCoordinates (extendHopf K A) (fun i j => (1 : K) ⊗ₜ[k] M i j) := by
  let B := extendHopf K A
  let j := includeCoordinates K A
  let N := j.mapMatrix M
  let C := Algebra.adjoin K (Set.range (fun ij : ι × ι => N ij.1 ij.2) ∪ {N.det⁻¹ʳ})
  have hdet : j (M.det⁻¹ʳ) = N.det⁻¹ʳ := by
    have hunit : IsUnit M.det := (Matrix.GeneralLinearGroup.det (unitMatrix A M hM)).isUnit
    rw [algHom_map_inverse j M.det hunit, AlgHom.map_det]
  have hC (a : A) : j a ∈ C := by
    have htop : (⊤ : Subalgebra k A) ≤ (C.restrictScalars k).comap j := by
      rw [← hgen]
      apply Algebra.adjoin_le
      rintro x (⟨⟨i, l⟩, rfl⟩ | h)
      · exact Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_range_self (i, l)))
      · rw [Set.mem_singleton_iff.mp h]
        change j (M.det⁻¹ʳ) ∈ C
        rw [hdet]
        exact Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))
    exact htop trivial
  change C = ⊤
  apply top_unique
  intro x htop
  clear htop
  have hx (t : K) (a : A) : (t ⊗ₜ[k] a : K ⊗[k] A) = t • j a := by
    change _ = t • ((1 : K) ⊗ₜ[k] a)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    rw [hx]
    exact C.smul_mem (hC a) t
  | add x y hx hy => exact C.add_mem hx hy

private theorem centralizerIdeal_extension (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (Y : Matrix ι ι k) :
    (centralizerIdeal A M Y).map (includeCoordinates K A) =
      centralizerIdeal (extendHopf K A) (fun i j => (1 : K) ⊗ₜ[k] M i j)
        (Y.map (algebraMap k K)) := by
  let j := includeCoordinates K A
  let T := Y.map (algebraMap k A)
  have hT : j.mapMatrix T = (Y.map (algebraMap k K)).map (algebraMap K (extendHopf K A)) := by
    ext i l
    exact (j.commutes (Y i l)).trans (IsScalarTower.algebraMap_apply k K _ _)
  unfold centralizerIdeal
  rw [Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext ij
  obtain ⟨i, l⟩ := ij
  change (j.mapMatrix (M * T - T * M)) i l = _
  rw [map_sub, map_mul, map_mul, hT]
  rfl

theorem matrixCentralizerSmooth : MatrixCentralizerSmooth.{u} := by
  intro k _ A _ ι _ _ M hM hgen D hY
  let K := AlgebraicClosure k
  let J := centralizerIdeal A M (matrixAction A M D)
  let B := extendHopf K A
  let N : Matrix ι ι B := fun i j => (1 : K) ⊗ₜ[k] M i j
  obtain ⟨D', hD'⟩ := matrixAction_extension K A M D
  have hsemi : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (matrixAction B N D')) := by
    rw [hD']
    exact hY
  have hs := splitMatrixCentralizerSmooth K B ι N (isCoactionMatrix_extension A K hM)
    (generatesCoordinates_extension K A M hM hgen) D' hsemi
  rw [hD', ← centralizerIdeal_extension K A] at hs
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := k) (S := K) A K J
  have : Algebra.Smooth K (K ⊗[k] (A ⧸ J)) := Algebra.Smooth.of_equiv e.symm
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K

open AlgebraicGeometry Opposite

open private isAffine_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

theorem geometricLieJordan : GeometricLieJordan.{u} := by
  intro k _ G K H ι _ _ L l f x
  let : IsAffine G.val.X.left := G.property.1
  let HA : AffineGroupCategory K := ⟨H, isAffine_baseChange K G.val⟩
  let : (affineHopfSpec K).IsEquivalence := affineHopfSpecEquivalence K
  obtain ⟨e, _⟩ := coordinateHopfPoints K HA
  exact perfectFieldLieJordan K HA _ e ι L l f x

private def groupIsoOfPoints (G H : Specs.GroupScheme k) [IsAffine G.X.left] [IsAffine H.X.left]
    (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) : G ≅ H := by
  let F := groupPointsFunctor k
  let a := groupHomEquiv G H inferInstance
  let b := groupHomEquiv H G inferInstance
  let f := a.symm e.hom
  let g := b.symm e.inv
  have hf : F.map f = e.hom := a.apply_symm_apply _
  have hg : F.map g = e.inv := b.apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply (groupHomEquiv G G inferInstance).injective
    change F.map (f ≫ g) = F.map (𝟙 G)
    rw [F.map_comp, hf, hg, e.hom_inv_id, F.map_id]
  · apply (groupHomEquiv H H inferInstance).injective
    change F.map (g ≫ f) = F.map (𝟙 H)
    rw [F.map_comp, hf, hg, e.inv_hom_id, F.map_id]

private theorem groupIsoOfPoints_hom (G H : Specs.GroupScheme k) [IsAffine G.X.left] [IsAffine H.X.left]
    (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) :
    (groupPointsFunctor k).map (groupIsoOfPoints G H e).hom = e.hom :=
  (groupHomEquiv G H inferInstance).apply_symm_apply _

private theorem image_GLCoordinates_generates (A : HopfAlgebraCategory k) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (a : Specs.StandardGroups.GLCoordinates k ι →ₐ[k] A)
    (ha : Function.Surjective a) :
    MatrixGeneratesCoordinates A (a.mapMatrix (Specs.StandardGroups.universalMatrix k ι)) := by
  let X := Specs.StandardGroups.universalMatrix k ι
  let M := a.mapMatrix X
  let C := Algebra.adjoin k (Set.range (fun ij : ι × ι => M ij.1 ij.2) ∪ {M.det⁻¹ʳ})
  let d := Specs.StandardGroups.genericDeterminant k ι
  let H := Specs.StandardGroups.GLCoordinates k ι
  let g : MvPolynomial (ι × ι) k →ₐ[k] A := a.comp (IsScalarTower.toAlgHom k _ H)
  have hg (p : MvPolynomial (ι × ι) k) : g p ∈ C := by
    have h : Algebra.adjoin k (Set.range (MvPolynomial.X : ι × ι → MvPolynomial (ι × ι) k)) ≤
        C.comap g := by
      apply Algebra.adjoin_le
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_range_self (i, j)))
    rw [MvPolynomial.adjoin_range_X] at h
    exact h trivial
  have hd : g d = M.det := by
    change a (algebraMap (MvPolynomial (ι × ι) k) H d) = _
    change a (algebraMap (MvPolynomial (ι × ι) k) H (Specs.StandardGroups.genericMatrix k ι).det) = _
    rw [RingHom.map_det, AlgHom.map_det]
    rfl
  have hi : IsUnit M.det := by
    rw [← hd]
    exact (IsLocalization.Away.algebraMap_isUnit (S := H) d).map a
  change C = ⊤
  apply top_unique
  intro x _
  obtain ⟨z, rfl⟩ := ha x
  obtain ⟨r, p, he⟩ := IsLocalization.Away.surj d z
  have hp := congrArg a he
  change a (z * algebraMap (MvPolynomial (ι × ι) k) H d ^ r) = g p at hp
  rw [map_mul, map_pow, show a (algebraMap (MvPolynomial (ι × ι) k) H d) = g d from rfl, hd] at hp
  have hz : a z = g p * (M.det⁻¹ʳ) ^ r := by
    apply (hi.pow r).mul_right_cancel
    rw [hp, mul_assoc, ← mul_pow, Ring.inverse_mul_cancel _ hi, one_pow, mul_one]
  rw [hz]
  exact C.mul_mem (hg p) (C.pow_mem (Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))) r)

open private generalLinearRepresentation Representation.convolutionIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

theorem faithfulMatrixGenerates : FaithfulMatrixGenerates.{u} := by
  intro k _ G L A e ι _ _ l f hf
  let : IsAffine G.val.X.left := G.property
  let : IsAffine L.val.X.left := L.property
  let : HopfAlgebra k (Specs.StandardGroups.GLCoordinates k ι) := StandardGroups.generalLinearHopf k ι
  let B := CommHopfAlgCat.of k (Specs.StandardGroups.GLCoordinates k ι)
  let F := groupPointsFunctor k
  let b : F.obj (specGroup B) ≅ Specs.StandardGroups.generalLinearPoints k ι :=
    StandardGroups.generalLinearGroupPointsIso k ι
  let : IsAffine (specGroup A).X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  let : IsAffine (specGroup B).X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
  let i := groupIsoOfPoints (specGroup A) G.val ((hopfSpecPointIso A).symm ≪≫ e)
  let j := groupIsoOfPoints L.val (specGroup B) (l ≪≫ b.symm)
  let g := i.hom ≫ f ≫ j.hom
  let a : B ⟶ A := (hopfSpec.fullyFaithful.preimage g).unop
  have hg : specGroupMap a = g := hopfSpec.fullyFaithful.map_preimage g
  have hsurj : Function.Surjective a.hom := by
    apply (hopfMapClosedImmersion k a).mp
    rw [hg]
    change IsClosedImmersion (i.hom.hom.hom.left ≫ f.hom.hom.left ≫ j.hom.hom.hom.left)
    have : IsIso i.hom.hom.hom.left :=
      inferInstanceAs (IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map i.hom))
    have : IsIso j.hom.hom.hom.left :=
      inferInstanceAs (IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map j.hom))
    infer_instance
  have hM : a.hom.toAlgHom.mapMatrix (Specs.StandardGroups.universalMatrix k ι) =
      RationalRepresentations.universalMatrix A G L.val e l f := by
    have h : (hopfSpecPointIso A).hom ≫ F.map (specGroupMap a) ≫ b.hom = e.hom ≫ F.map f ≫ l.hom := by
      have hi : F.map i.hom = (hopfSpecPointIso A).inv ≫ e.hom := groupIsoOfPoints_hom _ _ _
      have hj : F.map j.hom = l.hom ≫ b.inv := groupIsoOfPoints_hom _ _ _
      rw [hg]
      change (hopfSpecPointIso A).hom ≫ F.map (i.hom ≫ f ≫ j.hom) ≫ b.hom = _
      rw [F.map_comp, F.map_comp, hi, hj]
      simp
    have he := congrArg (fun t => (t.app (CommAlgCat.of k A) (toConv (AlgHom.id k A))).val) h
    change (b.hom.app (CommAlgCat.of k A)
      ((F.map (specGroupMap a)).app (CommAlgCat.of k A)
        ((hopfSpecPointIso A).hom.app _ (toConv (AlgHom.id k A))))).val = _ at he
    have hpoint : (F.map (specGroupMap a)).app (CommAlgCat.of k A)
        ((hopfSpecPointIso A).hom.app _ (toConv (AlgHom.id k A))) =
          (hopfSpecPointIso B).hom.app _ (toConv a.hom.toAlgHom) := by
      apply Over.OverMorphism.ext
      change Spec.map (𝟙 (CommRingCat.of A)) ≫ Spec.map (CommRingCat.ofHom a.hom.toAlgHom.toRingHom) =
        Spec.map (CommRingCat.ofHom a.hom.toAlgHom.toRingHom)
      simp
    rw [hpoint] at he
    let c := Representation.convolutionIso (generalLinearRepresentation (k := k) (ι := ι))
    have hc : hopfSpecPointIso B ≪≫ b = c := by
      change hopfSpecPointIso B ≪≫ ((hopfSpecPointIso B).symm ≪≫ c) = c
      simp
    have hm := congrArg (fun t : convolutionPoints B ≅ Specs.StandardGroups.generalLinearPoints k ι =>
      (t.hom.app (CommAlgCat.of k A) (toConv a.hom.toAlgHom)).val) hc
    exact hm.symm.trans he
  rw [← hM]
  exact image_GLCoordinates_generates A a.hom.toAlgHom hsurj

private theorem tangentComparison_lift (A : HopfAlgebraCategory k) (G : Specs.GroupScheme k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G) (D : InvariantDerivation A) :
    (hopfKernelLifts A) (mapDualKernel e.inv (tangentComparison A G e D)) =
      (invariantDerivationLifts k A).choose D := by
  let t := dualKernelIso e
  let x := (hopfKernelLifts A).symm ((invariantDerivationLifts k A).choose D)
  change (hopfKernelLifts A) (t.symm (t x)) = _
  rw [t.symm_apply_apply]
  exact (hopfKernelLifts A).apply_symm_apply _

theorem restrictedSchemeNaturality : RestrictedSchemeNaturality.{u} := by
  intro k _ p _ _ A B f eA eB hAB
  let qA := tangentComparison A (specGroup A) eA
  let qB := tangentComparison B (specGroup B) eB
  let powerA := fun x => qA (restrictedPower A p (qA.symm x))
  let powerB := fun x => qB (restrictedPower B p (qB.symm x))
  have hA (D : InvariantDerivation A) (a : A) :
      (((hopfKernelLifts A) (mapDualKernel eA.inv (qA D))).val a).snd =
        Coalgebra.counit (R := k) (D.val a) := by
    rw [tangentComparison_lift A (specGroup A) eA D]
    exact congrArg TrivSqZeroExt.snd ((invariantDerivationLifts k A).choose_spec D a)
  have hB (D : InvariantDerivation B) (b : B) :
      (((hopfKernelLifts B) (mapDualKernel eB.inv (qB D))).val b).snd =
        Coalgebra.counit (R := k) (D.val b) := by
    rw [tangentComparison_lift B (specGroup B) eB D]
    exact congrArg TrivSqZeroExt.snd ((invariantDerivationLifts k B).choose_spec D b)
  refine ⟨qA, qB, powerA, powerB, hA, hB, ?_, ?_, ?_⟩
  · intro x
    change (qA.symm (qA (restrictedPower A p (qA.symm x)))).val.toLinearMap = _
    rw [qA.symm_apply_apply]
    rfl
  · intro y
    change (qB.symm (qB (restrictedPower B p (qB.symm y)))).val.toLinearMap = _
    rw [qB.symm_apply_apply]
    rfl
  · have hmap (D : InvariantDerivation A) (E : InvariantDerivation B) (h : IsDifferential f D E) :
        mapPointKernel (specGroupMap f) (qA D) = qB E := by
      let a := (invariantDerivationLifts k A).choose D
      let b := (invariantDerivationLifts k B).choose E
      have hc : a.val.comp f.hom.toAlgHom = b.val := by
        apply AlgHom.ext
        intro z
        have h1 := (invariantDerivationLifts k A).choose_spec D (f.hom z)
        have h2 := (invariantDerivationLifts k B).choose_spec E z
        change a.val (f.hom z) = b.val z
        rw [h1, h2, CoalgHomClass.counit_comp_apply]
        have hz := LinearMap.congr_fun h z
        change D.val (f.hom z) = f.hom (E.val z) at hz
        rw [hz, CoalgHomClass.counit_comp_apply]
      apply Subtype.ext
      change ((groupPointsFunctor k).map (specGroupMap f)).app (CommAlgCat.of k (DualNumber k))
        (eA.hom.app _ (toConv a.val)) = eB.hom.app _ (toConv b.val)
      rw [hAB, hc]
    intro x
    obtain ⟨D, rfl⟩ := qA.surjective x
    obtain ⟨E, hE, _⟩ := invariantDifferentialComparison k A B f D
    have hP := restrictedDifferentialNaturality k A B p f D (restrictedPower A p D)
      E (restrictedPower B p E) hE rfl rfl
    change mapPointKernel (specGroupMap f) (qA (restrictedPower A p (qA.symm (qA D)))) =
      qB (restrictedPower B p (qB.symm (mapPointKernel (specGroupMap f) (qA D))))
    rw [qA.symm_apply_apply, hmap D E hE, qB.symm_apply_apply]
    exact hmap _ _ hP

open private matrixDifferentialLinear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

private def faithfulLieHom (G L : AffineGroupCategory k) (s : IdentityLieStructure G.val)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (l : (groupPointsFunctor k).obj L.val ≅ Specs.StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L.val) (hf : IsClosedImmersion f.hom.hom.left) :
    letI := s.lieRing
    letI := s.lieAlgebra
    Specs.Lie k G.val →ₗ⁅k⁆ Module.End k (ι → k) := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let : IsAffine G.val.X.left := G.property
  let : IsAffine L.val.X.left := L.property
  let d₀ := matrixDifferentialLinear f l
  let T : Matrix ι ι k ≃ₐ[k] Module.End k (ι → k) := Matrix.toLinAlgEquiv'
  refine {
    toFun := fun x => T (InfinitesimalCommutator.matrixDifferential f l x)
    map_add' := ?_
    map_smul' := ?_
    map_lie' := ?_ }
  · intro x y
    have h := congrArg (fun g : AddGroup (PointKernel G.val) => g.toAdd.add x y) s.group_law
    have hadd : d₀ (x + y) = d₀ x + d₀ y := d₀.map_add x y
    exact (congrArg (fun z => T (InfinitesimalCommutator.matrixDifferential f l z)) h).trans
      ((congrArg T hadd).trans (T.map_add _ _))
  · intro c x
    have h := congrFun (congrFun s.scalar_law c) x
    have hsmul : d₀ (scalePointKernel G.val c x) = c • d₀ x := d₀.map_smul c x
    exact (congrArg (fun z => T (InfinitesimalCommutator.matrixDifferential f l z)) h).trans
      ((congrArg T hsmul).trans (T.toLinearMap.map_smul c (d₀ x)))
  · intro x y
    have h := (identityLieBracketMatrix k G.val L.val ι f l hf).2 s x y
    change T (InfinitesimalCommutator.matrixDifferential f l ⁅x, y⁆) =
      T (d₀ x) * T (d₀ y) - T (d₀ y) * T (d₀ x)
    rw [h, map_sub, map_mul, map_mul]
    rfl

private theorem faithfulLieHom_injective (G L : AffineGroupCategory k) (s : IdentityLieStructure G.val)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (l : (groupPointsFunctor k).obj L.val ≅ Specs.StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L.val) (hf : IsClosedImmersion f.hom.hom.left) :
    Function.Injective (faithfulLieHom G L s l f hf) := by
  let : IsAffine G.val.X.left := G.property
  let : IsAffine L.val.X.left := L.property
  exact Matrix.toLinAlgEquiv'.injective.comp (identityLieBracketMatrix k G.val L.val ι f l hf).1

theorem centralizerLieComparison : CentralizerLieComparison.{u} := by
  intro k _ G L s A e ι _ _ l f hf
  let := s.lieRing
  let := s.lieAlgebra
  intro y x
  let : IsAffine G.val.X.left := G.property
  let : IsAffine L.val.X.left := L.property
  let M := RationalRepresentations.universalMatrix A G L.val e l f
  let d := InfinitesimalCommutator.matrixDifferential f l
  let Y := d y
  let q := tangentComparison A G.val e
  obtain ⟨D, rfl⟩ := q.surjective x
  let g := (invariantDerivationLifts k A).choose D
  change (centralizerIdeal A M Y ≤
    RingHom.ker ((hopfKernelLifts A) (mapDualKernel e.inv (q D))).val.toRingHom) ↔ _
  rw [show (hopfKernelLifts A) (mapDualKernel e.inv (q D)) = g from tangentComparison_lift A G.val e D,
    ← centralizesMatrix_iff_ideal_le_ker A M Y g.val,
    matrixCentralizerTangent k A ι M Y (universalMatrix_coaction A G e L.val l f) D g
      (fun a => congrArg TrivSqZeroExt.snd ((invariantDerivationLifts k A).choose_spec D a)),
    ← tangentComparison_matrix A G e L.val l f D]
  have hd := identityLieBracketMatrix k G.val L.val ι f l hf
  have hzero : d 0 = 0 := by
    exact (matrixDifferentialLinear f l).map_zero
  have hbr : d ⁅y, q D⁆ = d y * d (q D) - d (q D) * d y := hd.2 s y (q D)
  change Commute (d (q D)) (d y) ↔ ⁅y, q D⁆ = 0
  constructor
  · intro h
    apply hd.1
    change d ⁅y, q D⁆ = d 0
    rw [hbr, hzero, sub_eq_zero]
    exact h.symm.eq
  · intro h
    have hz : d ⁅y, q D⁆ = 0 := (congrArg d h).trans hzero
    rw [hbr, sub_eq_zero] at hz
    exact (show Commute (d y) (d (q D)) from hz).symm

private theorem ideal_le_point_sq_iff (A : HopfAlgebraCategory k) (x : A →ₐ[k] k) (J : Ideal A) :
    J ≤ RingHom.ker x.toRingHom ^ 2 ↔
      ∀ g : Specs.AdvCommAlg.Differentials.Tangent.PointLifts k A k x, J ≤ RingHom.ker g.val.toRingHom := by
  constructor
  · intro h g
    refine h.trans ?_
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    have hg (z : A) : (g.val z).fst = x z := DFunLike.congr_fun g.property z
    change g.val (a * b) = 0
    rw [map_mul]
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul, hg, (show x a = 0 from ha)]
    · simp [TrivSqZeroExt.snd_mul, hg, (show x a = 0 from ha), (show x b = 0 from hb)]
  · intro h a ha
    obtain ⟨e, he, _⟩ := pointTangentLifts k A x
    have ham : a ∈ RingHom.ker x.toRingHom := by
      have hz : (e 0).val a = 0 := h (e 0) ha
      have hx := DFunLike.congr_fun (e 0).property a
      change ((e 0).val a).fst = x a at hx
      rw [hz] at hx
      exact hx.symm
    let b : RingHom.ker x.toRingHom := ⟨a, ham⟩
    apply (Ideal.toCotangent_eq_zero _ b).mp
    let B := Module.Free.chooseBasis k (PointCotangent x)
    apply B.repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    change B.coord i (Ideal.toCotangent _ b) = 0
    rw [← he (B.coord i) b]
    have hz : (e (B.coord i)).val a = 0 := h _ ha
    exact congrArg TrivSqZeroExt.snd hz

set_option maxHeartbeats 600000 in
private theorem translation_point_sq (A : HopfAlgebraCategory k) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (Y : Matrix ι ι k)
    (hM : RationalRepresentations.IsCoactionMatrix A M)
    (h : centralizerIdeal A M Y ≤ (RingHom.ker (counitAlgHom k A).toRingHom) ^ 2)
    (x : A →ₐ[k] k) (hx : centralizerIdeal A M Y ≤ RingHom.ker x.toRingHom) :
    centralizerIdeal A M Y ≤ (RingHom.ker x.toRingHom) ^ 2 := by
  apply (ideal_le_point_sq_iff A _ _).mpr
  intro g
  let R := CommAlgCat.of k (DualNumber k)
  let c := TrivSqZeroExt.inlAlgHom k k k
  let F := convolutionPoints A
  let p : F.obj R := toConv g.val
  let z : F.obj R := toConv (c.comp x)
  let r := (F.map (dualReduction k)).hom
  have hrp : r p = toConv x := congrArg toConv g.property
  have hrz : r z = toConv x := rfl
  have hr : r (p * z⁻¹) = 1 := by rw [map_mul, map_inv, hrp, hrz, mul_inv_cancel]
  let v : DualKernel F := Additive.ofMul ⟨p * z⁻¹, hr⟩
  let g₀ := hopfKernelLifts A v
  have hg₀ : CentralizesMatrix A M Y g₀.val :=
    (centralizesMatrix_iff_ideal_le_ker A M Y _).mpr ((ideal_le_point_sq_iff A _ _).mp h g₀)
  have hz : CentralizesMatrix A M Y z.ofConv :=
    (centralizesMatrix_iff_ideal_le_ker A M Y _).mpr fun a ha => by
      change c (x a) = 0
      rw [show x a = 0 from hx ha, map_zero]
  have hg := convolution_centralizes_mul A M Y hM hg₀ hz
  have he : (p * z⁻¹) * z = p := inv_mul_cancel_right p z
  change CentralizesMatrix A M Y (((p * z⁻¹) * z).ofConv) at hg
  rw [he] at hg
  exact (centralizesMatrix_iff_ideal_le_ker A M Y _).mp hg

private theorem derivation_raises_ideal_powers {A : Type*} [CommRing A] [Algebra k A]
    (C : Derivation k A A) (m : Ideal A) (hC : ∀ a, C a ∈ m ^ 2) (n : ℕ) :
    ∀ a ∈ m ^ n, C a ∈ m ^ (n + 1) := by
  have h₁ (a : A) : C a ∈ m := by
    have h : m ^ 2 ≤ m := by rw [pow_two]; exact Ideal.mul_le_left
    exact h (hC a)
  induction n with
  | zero => simpa using (fun a (_ : a ∈ (⊤ : Ideal A)) => h₁ a)
  | succ n ih =>
    let J : Ideal A :=
      { carrier := {a | a ∈ m ^ (n + 1) ∧ C a ∈ m ^ (n + 2)}
        zero_mem' := ⟨Ideal.zero_mem _, by rw [map_zero]; exact Ideal.zero_mem _⟩
        add_mem' := fun {a b} ha hb => ⟨Ideal.add_mem _ ha.1 hb.1, by
          rw [map_add]; exact Ideal.add_mem _ ha.2 hb.2⟩
        smul_mem' := fun r a ha => by
          change r * a ∈ m ^ (n + 1) ∧ C (r * a) ∈ m ^ (n + 2)
          refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
          rw [C.leibniz, smul_eq_mul, smul_eq_mul]
          apply Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha.2)
          simpa only [← pow_succ] using Ideal.mul_mem_mul ha.1 (h₁ r) }
    have hJ : m ^ (n + 1) ≤ J := by
      rw [pow_succ, Ideal.mul_le]
      intro a ha b hb
      change a * b ∈ m ^ (n + 1) ∧ C (a * b) ∈ m ^ (n + 2)
      refine ⟨by simpa only [pow_succ] using Ideal.mul_mem_mul ha hb, ?_⟩
      rw [C.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b (C a)]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_add]
        exact Ideal.mul_mem_mul ha (hC b)
      · simpa only [← pow_succ] using Ideal.mul_mem_mul (ih a ha) hb
    intro a ha
    exact (hJ ha).2

private theorem adicIntersection_annihilator {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m J : Ideal A) (hJ : ∀ n : ℕ, J ≤ m ^ n) :
    ∃ t : A, t - 1 ∈ m ∧ t ∈ (J : Submodule A A).annihilator := by
  let N : Submodule A A := ⨅ n : ℕ, m ^ n • ⊤
  have hN (n : ℕ) : m ^ n • (⊤ : Submodule A A) ⊓ N = N :=
    inf_eq_right.mpr (iInf_le _ n)
  obtain ⟨r, hr⟩ := m.exists_pow_inf_eq_pow_smul N
  have he := hr (r + 1) (Nat.le_succ r)
  rw [hN, hN, Nat.add_sub_cancel_left, pow_one] at he
  obtain ⟨a, ha, han⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul m N (IsNoetherian.noetherian N) he.le
  refine ⟨1 - a, by simpa using m.neg_mem ha, Submodule.mem_annihilator.mpr ?_⟩
  intro b hb
  have hbN : b ∈ N := by
    rw [Submodule.mem_iInf]
    intro n
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hJ n hb
  rw [sub_smul, one_smul, han b hbN, sub_self]

private theorem splitCentralizer_idempotent [IsAlgClosed k] (A : HopfAlgebraCategory k) [Algebra.FiniteType k A]
    {ι : Type u} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A)
    (hM : RationalRepresentations.IsCoactionMatrix A M) (hgen : MatrixGeneratesCoordinates A M)
    (D : InvariantDerivation A) (hs : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (matrixAction A M D)))
    (h₂ : centralizerIdeal A M (matrixAction A M D) ≤ (RingHom.ker (counitAlgHom k A).toRingHom) ^ 2) :
    IsIdempotentElem (centralizerIdeal A M (matrixAction A M D)) := by
  let Y := matrixAction A M D
  let J := centralizerIdeal A M Y
  obtain ⟨C, hspan, heq⟩ := conjugation_eigenspace_decomposition A M hM hgen D hs
  have hC (a : A) : C a ∈ J := by
    change C a ∈ centralizerIdeal A M Y
    rw [heq]
    exact Ideal.subset_span (Set.mem_range_self a)
  have hall (x : A →ₐ[k] k) (hx : J ≤ RingHom.ker x.toRingHom) (n : ℕ) : J ≤ RingHom.ker x.toRingHom ^ n := by
    let m := RingHom.ker x.toRingHom
    have hraise := derivation_raises_ideal_powers C m (fun a => translation_point_sq A M Y hM h₂ x hx (hC a))
    have hw (w : k) (a : A) (ha : a ∈ Module.End.eigenspace C.toLinearMap w) (hw : w ≠ 0) :
        ∀ n : ℕ, a ∈ m ^ n := by
      have hwa : C a = w • a := Module.End.mem_eigenspace_iff.mp ha
      intro r
      induction r with
      | zero => simp
      | succ n ih =>
        have h := hraise n a ih
        rw [hwa] at h
        have hm := (m ^ (n + 1)).mul_mem_left (algebraMap k A w⁻¹) h
        rw [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hw, one_smul] at hm
        exact hm
    change centralizerIdeal A M Y ≤ m ^ n
    rw [heq, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    have ha : a ∈ ⨆ w : k, Module.End.eigenspace C.toLinearMap w := hspan.symm ▸ Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun a => C a ∈ m ^ n) ha ?_ (by simp) ?_
    · intro w b hb
      rw [show C b = w • b from Module.End.mem_eigenspace_iff.mp hb]
      by_cases hn : w = 0
      · simp [hn]
      · rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (hw w b hb hn n)
    · intro b c hb hc
      rw [map_add]
      exact Ideal.add_mem _ hb hc
  let I := (J : Submodule A A).annihilator
  have htop : I ⊔ J = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal (I ⊔ J) h
    let := hP
    let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
    let : Field (A ⧸ P) := Ideal.Quotient.field P
    let : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
    let e : k ≃ₐ[k] A ⧸ P :=
      AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) IsAlgClosed.algebraMap_bijective_of_isIntegral
    let x := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k P)
    have hx : RingHom.ker x.toRingHom = P := by
      ext a
      exact ⟨fun h => Ideal.Quotient.eq_zero_iff_mem.mp (e.symm.injective (h.trans (map_zero e.symm).symm)),
        fun h => by change e.symm (Ideal.Quotient.mk P a) = 0; rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]⟩
    have hJP : J ≤ RingHom.ker x.toRingHom := hx.symm ▸ le_sup_right.trans hIP
    let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
    obtain ⟨t, ht, hti⟩ := adicIntersection_annihilator _ _ (hall x hJP)
    have htP : t ∈ P := le_sup_left.trans hIP hti
    rw [hx] at ht
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P (show (1 : A) ∈ P by
      simpa using P.sub_mem htP ht) isUnit_one)
  change J * J = J
  have hh := congrArg (· * J) htop
  rw [Ideal.sup_mul, Submodule.annihilator_mul, Ideal.top_mul] at hh
  simpa using hh

private theorem coordinate_ideal_map_injective (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) : Function.Injective (Ideal.map (includeCoordinates K A).toRingHom) := by
  let j := includeCoordinates K A
  have hc (J : Ideal A) : (J.map j).comap j = J := by
    apply le_antisymm ?_ Ideal.le_comap_map
    intro a ha
    have h : Ideal.Quotient.mk (J.map j) (j a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    let e := Algebra.TensorProduct.tensorQuotientEquiv (R := k) (S := K) A K J
    have h' : e ((1 : K) ⊗ₜ[k] Ideal.Quotient.mk J a) = 0 := by
      rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
      exact h
    have hh : (1 : K) ⊗ₜ[k] Ideal.Quotient.mk J a = 0 := e.injective (h'.trans (map_zero e).symm)
    have hi := Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := K) (A ⧸ J)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hi
    simpa only [TensorProduct.mk_apply, TensorProduct.tmul_zero] using hh
  intro I J h
  exact (hc I).symm.trans ((congrArg (Ideal.comap j.toRingHom) h).trans (hc J))

private theorem idempotent_proper_ideal_eq_bot {A : Type*} [CommRing A] [IsNoetherianRing A]
    [PreconnectedSpace (PrimeSpectrum A)] (I : Ideal A) (hI : IsIdempotentElem I) (hproper : I ≠ ⊤) : I = ⊥ := by
  obtain ⟨a, ha, h⟩ := (I.isIdempotentElem_iff_of_fg (IsNoetherian.noetherian I)).mp hI
  let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := A)
  let C := E ⟨a, ha⟩
  have he' : a = 0 ∨ a = 1 := by
    rcases isClopen_iff.mp C.isClopen with h₀ | h₁
    · left
      have hc : C = ⊥ := SetLike.ext' h₀
      have hh := congrArg (fun d => (E.symm d).val) hc
      rw [show (E.symm C).val = a from congrArg Subtype.val (E.symm_apply_apply ⟨a, ha⟩)] at hh
      exact hh.trans (congrArg Subtype.val PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot)
    · right
      have hc : C = ⊤ := SetLike.ext' h₁
      have hh := congrArg (fun d => (E.symm d).val) hc
      rw [show (E.symm C).val = a from congrArg Subtype.val (E.symm_apply_apply ⟨a, ha⟩)] at hh
      exact hh.trans (congrArg Subtype.val PrimeSpectrum.isIdempotentElemEquivClopens_symm_top)
  rcases he' with rfl | rfl
  · simpa using h
  · exact (hproper (by simpa [Ideal.span_singleton_one] using h)).elim

set_option maxHeartbeats 1000000 in
theorem centralizerOfCentralSemisimple : CentralizerOfCentralSemisimple.{u} := by
  intro k _ G L s A _ _ e ι _ _ l f hf
  let := s.lieRing
  let := s.lieAlgebra
  intro y M Y hY hy
  let J := centralizerIdeal A M Y
  let m := RingHom.ker (counitAlgHom k A).toRingHom
  have h₀ : J ≤ m ^ 2 := by
    apply (ideal_le_point_sq_iff A (counitAlgHom k A) J).mpr
    intro g
    let x := mapDualKernel e.hom ((hopfKernelLifts A).symm g)
    have hx : (hopfKernelLifts A) (mapDualKernel e.inv x) = g := by
      change (hopfKernelLifts A) ((dualKernelIso e).symm ((dualKernelIso e) ((hopfKernelLifts A).symm g))) = g
      rw [(dualKernelIso e).symm_apply_apply, (hopfKernelLifts A).apply_symm_apply]
    have hh := (centralizerLieComparison k G L s A e ι l f hf y x).mpr
      (by
        rw [hy]
        change s.lieRing.toAddCommGroup.toZero.zero = (0 : PointKernel G.val)
        exact congrArg (fun g : AddGroup (PointKernel G.val) => g.toZero.zero) s.group_law)
    rwa [hx] at hh
  let K := AlgebraicClosure k
  let B := extendHopf K A
  let N : Matrix ι ι B := fun i j => (1 : K) ⊗ₜ[k] M i j
  let j := includeCoordinates K A
  let mK := RingHom.ker (counitAlgHom K B).toRingHom
  let q := tangentComparison A G.val e
  let D := q.symm y
  have hD := tangentComparison_matrix A G e L.val l f D
  change InfinitesimalCommutator.matrixDifferential f l (q (q.symm y)) = matrixAction A M D at hD
  rw [q.apply_symm_apply] at hD
  change Y = matrixAction A M D at hD
  obtain ⟨E, hE⟩ := matrixAction_extension K A M D
  have hEq : matrixAction B N E = Y.map (algebraMap k K) := (congrArg (·.map (algebraMap k K)) hD).symm ▸ hE
  have hsm : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (matrixAction B N E)) := by
    rw [hEq]
    exact hY
  have hJ : J.map j = centralizerIdeal B N (matrixAction B N E) := by
    rw [hEq]
    exact centralizerIdeal_extension K A M Y
  have hm : m.map j ≤ mK := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[k] a) = 0
    rw [TensorProduct.counit_tmul, show Coalgebra.counit (R := k) a = 0 from ha, zero_smul]
  have hmK : centralizerIdeal B N (matrixAction B N E) ≤ mK ^ 2 := by
    rw [← hJ]
    refine (Ideal.map_mono h₀).trans ?_
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hm 2
  have hM := universalMatrix_coaction A G e L.val l f
  have hg := faithfulMatrixGenerates k G L A e ι l f hf
  have hId := splitCentralizer_idempotent B N (isCoactionMatrix_extension A K hM)
    (generatesCoordinates_extension K A M hM hg) E hsm hmK
  have hIdJ : IsIdempotentElem J := by
    apply coordinate_ideal_map_injective K A
    rw [Ideal.map_mul]
    change (J.map j) * (J.map j) = J.map j
    rw [hJ]
    exact hId
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  exact idempotent_proper_ideal_eq_bot J hIdJ (fun h =>
    (RingHom.ker_ne_top (counitAlgHom k A).toRingHom) (top_unique
      (h ▸ h₀.trans (by rw [pow_two]; exact Ideal.mul_le_left))))

private theorem hopfPoint_map {A B : HopfAlgebraCategory k} (a : B ⟶ A) (R : TestAlgebra k)
    (g : WithConv (A →ₐ[k] R)) :
    ((groupPointsFunctor k).map (specGroupMap a)).app R ((hopfSpecPointIso A).hom.app R g) =
      (hopfSpecPointIso B).hom.app R (toConv (g.ofConv.comp a.hom.toAlgHom)) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp (CommRingCat.ofHom a.hom.toAlgHom.toRingHom)
    (CommRingCat.ofHom g.ofConv.toRingHom)).symm

open private pointMatrix_evaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

set_option maxHeartbeats 1600000 in
theorem schemeCentralizerOfSemisimple : SchemeCentralizerOfSemisimple.{u} := by
  intro k _ G L s hG ι _ _ l f hf
  let := s.lieRing
  let := s.lieAlgebra
  intro y Y hy
  let F := groupPointsFunctor k
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  let : (affineHopfSpec k).IsEquivalence := affineHopfSpecEquivalence k
  let A := ((affineHopfSpec k).inv.obj G').unop
  let i : specGroup A ≅ G.val :=
    (affineGroupInclusion k).mapIso ((affineHopfSpec k).asEquivalence.counitIso.app G')
  let e := hopfSpecPointIso A ≪≫ F.mapIso i
  let w : (specGroup A).X.left ≅ G.val.X.left :=
    ((Grp.forget (SchemeOver k)) ⋙ Over.forget (Spec (CommRingCat.of k))).mapIso i
  let : IsIso w.hom := inferInstanceAs (IsIso w.hom)
  have hw : w.hom ≫ G.val.X.hom = Spec.map (CommRingCat.ofHom (algebraMap k A)) :=
    Over.w ((Grp.forget (SchemeOver k)).map i.hom)
  let : Algebra.Smooth k A := by
    have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
      rw [← hw]
      let hres : MorphismProperty.Respects (@Smooth.{u}) (@IsOpenImmersion.{u}) :=
        HasRingHomProperty.respects_isOpenImmersion
          (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
            RingHom.Smooth.holdsForLocalizationAway).1
      let : MorphismProperty.RespectsLeft (@Smooth.{u}) (@IsOpenImmersion.{u}) := hres.toRespectsLeft
      exact MorphismProperty.RespectsLeft.precomp (P := @Smooth.{u}) (Q := @IsOpenImmersion.{u})
        w.hom inferInstance G.val.X.hom hG
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hs)
  let M := RationalRepresentations.universalMatrix A G' L.val e l f
  let J := centralizerIdeal A M Y
  have hM := universalMatrix_coaction A G' e L.val l f
  let : J.IsHopfIdeal k := matrixCentralizerHopf k A ι M Y hM
  let Q := hopfQuotient A J
  let q := hopfQuotientMap A J
  let c : specGroup Q ⟶ G.val := specGroupMap q ≫ i.hom
  have hc : IsClosedImmersion c.hom.hom.left := by
    let : IsClosedImmersion (specGroupMap q).hom.hom.left :=
      (hopfMapClosedImmersion k q).mpr (Ideal.Quotient.mk_surjective (I := J))
    change IsClosedImmersion ((specGroupMap q).hom.hom.left ≫ w.hom)
    exact IsClosedImmersion.comp _ _
  have hSmooth : Smooth (specGroup Q).X.hom := by
    let z := tangentComparison A G.val e
    let D := z.symm y
    have hD := tangentComparison_matrix A G' e L.val l f D
    change InfinitesimalCommutator.matrixDifferential f l (z (z.symm y)) = matrixAction A M D at hD
    rw [z.apply_symm_apply] at hD
    change Y = matrixAction A M D at hD
    have hs : Algebra.Smooth k Q := by
      change Algebra.Smooth k (A ⧸ centralizerIdeal A M Y)
      rw [hD] at hy ⊢
      exact matrixCentralizerSmooth k A ι M hM (faithfulMatrixGenerates k G' L A e ι l f hf) D hy
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k Q)))
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr hs)
  have hpc (R : TestAlgebra k) (g : WithConv (Q →ₐ[k] R)) :
      (F.map c).app R ((hopfSpecPointIso Q).hom.app R g) =
        e.hom.app R (toConv (g.ofConv.comp q.hom.toAlgHom)) := by
    change (F.map (specGroupMap q ≫ i.hom)).app R ((hopfSpecPointIso Q).hom.app R g) = _
    rw [F.map_comp]
    exact congrArg ((F.map i.hom).app R).hom (hopfPoint_map q R g)
  refine ⟨⟨specGroup Q, c, hc⟩, hSmooth, ?_, ?_, ?_⟩
  · intro R a
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app R)).2 a
    change (∃ h : (F.obj (specGroup Q)).obj R, (F.map c).app R h = e.hom.app R g) ↔ _
    rw [show (l.hom.app R ((F.map f).app R (e.hom.app R g))).val = g.ofConv.mapMatrix M from
      pointMatrix_evaluation A (e.hom ≫ F.map f ≫ l.hom) R g]
    obtain ⟨v, hv⟩ := matrixCentralizerPoints k A ι M Y R
    constructor
    · rintro ⟨h, hh⟩
      obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((hopfSpecPointIso Q).hom.app R)).2 h
      rw [hpc] at hh
      have hb := (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1 hh
      have he : (v b.ofConv).val = g.ofConv := (hv b.ofConv).trans (congrArg WithConv.ofConv hb)
      exact he ▸ (v b.ofConv).property
    · intro h
      let b := v.symm ⟨g.ofConv, h⟩
      have hb : (b : Q →ₐ[k] R).comp q.hom.toAlgHom = g.ofConv :=
        (hv b).symm.trans (congrArg Subtype.val (v.apply_symm_apply ⟨g.ofConv, h⟩))
      refine ⟨(hopfSpecPointIso Q).hom.app R (toConv b), ?_⟩
      rw [hpc, hb, toConv_ofConv]
  · intro x
    let R := CommAlgCat.of k (DualNumber k)
    let t := dualKernelIso (hopfSpecPointIso Q)
    let a := (hopfKernelLifts A) (mapDualKernel e.inv x)
    have hfun (b : Specs.AdvCommAlg.Differentials.Tangent.PointLifts k Q k (counitAlgHom k Q)) :
        ((hopfKernelLifts A) (mapDualKernel e.inv
          (mapPointKernel c (t ((hopfKernelLifts Q).symm b))))).val = b.val.comp q.hom.toAlgHom := by
      change ((e.inv.app R).hom ((F.map c).app R ((hopfSpecPointIso Q).hom.app R (toConv b.val)))).ofConv = _
      rw [hpc]
      have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.hom_inv_id_app R))
        (toConv (b.val.comp q.hom.toAlgHom))
      exact congrArg WithConv.ofConv h
    have hcrit : (J ≤ RingHom.ker a.val.toRingHom) ↔ LieAlgebra.ad k (Specs.Lie k G.val) y x = 0 :=
      centralizerLieComparison k G' L s A e ι l f hf y x
    constructor
    · rintro ⟨z, hz⟩
      apply hcrit.mp
      obtain ⟨v, rfl⟩ := t.surjective z
      obtain ⟨b, rfl⟩ := (hopfKernelLifts Q).symm.surjective v
      have h := hfun b
      rw [hz] at h
      intro u hu
      change a.val u = 0
      change a.val = b.val.comp q.hom.toAlgHom at h
      rw [h]
      change b.val (Ideal.Quotient.mk J u) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hu, map_zero]
    · intro hx
      let b := Ideal.Quotient.liftₐ J a.val (fun _ hu => hcrit.mpr hx hu)
      have hb : b.comp q.hom.toAlgHom = a.val := rfl
      have hred : (TrivSqZeroExt.fstHom k k k).comp b = counitAlgHom k Q := by
        apply Ideal.Quotient.algHom_ext
        exact ((AlgHom.comp_assoc _ _ _).trans (congrArg ((TrivSqZeroExt.fstHom k k k).comp) hb)).trans
          (a.property.trans (AlgHom.ext (fun u => (CoalgHomClass.counit_comp_apply q.hom u).symm)))
      let b' : Specs.AdvCommAlg.Differentials.Tangent.PointLifts k Q k (counitAlgHom k Q) := ⟨b, hred⟩
      refine ⟨t ((hopfKernelLifts Q).symm b'), ?_⟩
      apply (dualKernelIso e).symm.injective
      apply (hopfKernelLifts A).injective
      apply Subtype.ext
      exact (hfun b').trans hb
  · intro hconn hz
    let : PreconnectedSpace G.val.X.left := hconn
    let : PreconnectedSpace (PrimeSpectrum A) := by
      change PreconnectedSpace (specGroup A).X.left
      let j := w.inv.homeomorph
      have himg := isPreconnected_range j.continuous
      rw [Set.range_eq_univ.mpr j.surjective] at himg
      exact ⟨himg⟩
    have hj : J = ⊥ := centralizerOfCentralSemisimple k G' L s A e ι l f hf y hy hz
    have hbij : Function.Bijective q.hom := (Ideal.Quotient.mk_bijective_iff_eq_bot J).mpr hj
    let iso : A ≅ Q := CommHopfAlgCat.isoMk (BialgEquiv.ofBijective q.hom hbij)
    have hq : IsIso q := inferInstanceAs (IsIso iso.hom)
    change IsIso (specGroupMap q ≫ i.hom)
    infer_instance

end Centralizer

section NonnilpotentOpen

open AlgebraicGeometry
attribute [local instance 100] LieRing.ofAssociativeRing
open private isSemisimple_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LinearJordanFactors
open private isAffine_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

private theorem adjointMatrixFamily_basis {V ι : Type u} [LieRing V] [LieAlgebra k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) (i : ι) :
    adjointMatrixFamily b (Pi.single i 1) = LinearMap.toMatrix b b (LieAlgebra.ad k V (b i)) := by
  have hb : b.equivFun (b i) = Pi.single i 1 := by
    ext t
    change b.repr (b i) t = _
    simp [b.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [← hb]
  change LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad k V (b.equivFun.symm (b.equivFun (b i)))) = _
  rw [b.equivFun.symm_apply_apply]
  rfl

private theorem adjointMatrixFamily_specialize {V W ι K : Type u} [Field K] [Algebra k K]
    [LieRing V] [LieAlgebra k V] [LieRing W] [LieAlgebra K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (e : (K ⊗[k] V) ≃ₗ⁅K⁆ W) (y : W) :
    let B := (b.baseChange K).map e.toLinearEquiv
    (genericMatrix (adjointMatrixFamily b)).map
      (MvPolynomial.aeval (B.equivFun y) : MvPolynomial ι k →ₐ[k] K) =
      LinearMap.toMatrix B B (LieAlgebra.ad K W y) := by
  let B := (b.baseChange K).map e.toLinearEquiv
  intro B'
  change (genericMatrix (adjointMatrixFamily b)).map
      (MvPolynomial.aeval (B.equivFun y) : MvPolynomial ι k →ₐ[k] K) = _
  rw [genericMatrixSpecialization k ι K]
  let T : W →ₗ[K] Matrix ι ι K :=
    (LinearMap.toMatrix B B).toLinearMap.comp (LieAlgebra.ad K W).toLinearMap
  have hmat (l : ι) : (adjointMatrixFamily b (Pi.single l 1)).map (algebraMap k K) =
      T (B l) := by
    change _ = LinearMap.toMatrix B B (LieAlgebra.ad K W (B l))
    rw [adjointMatrixFamily_basis]
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, LinearMap.toMatrix_apply]
    change algebraMap k K (b.repr ⁅b l, b j⁆ i) = B.repr ⁅B l, B j⁆ i
    have hB (m : ι) : B m = e ((1 : K) ⊗ₜ[k] b m) := by simp [B]
    rw [hB l, hB j, ← e.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
    change _ = (b.baseChange K).repr (e.toLinearEquiv.symm (e.toLinearEquiv (1 ⊗ₜ[k] ⁅b l, b j⁆))) i
    rw [e.toLinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  simp_rw [hmat, ← map_smul T, ← map_sum]
  change T (∑ l, B.repr y l • B l) = T y
  rw [B.sum_repr y]

private theorem adjointOpen_geometric_witness {V W ι K : Type u} [Field K] [Algebra k K]
    [LieRing V] [LieAlgebra k V] [LieRing W] [LieAlgebra K W] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (e : (K ⊗[k] V) ≃ₗ⁅K⁆ W) (y : W)
    (hn : ¬ IsNilpotent (LieAlgebra.ad K W y)) :
    ∃ v : ι → K, ((genericMatrix (adjointMatrixFamily b)).map
      (MvPolynomial.aeval v : MvPolynomial ι k →ₐ[k] K)).charpoly ≠ Polynomial.X ^ Fintype.card ι := by
  let B := (b.baseChange K).map e.toLinearEquiv
  let : FiniteDimensional K W := B.finiteDimensional_of_finite
  refine ⟨B.equivFun y, ?_⟩
  rw [adjointMatrixFamily_specialize b e y, LinearMap.charpoly_toMatrix,
    ← Module.finrank_eq_card_basis B]
  exact (not_congr (LinearMap.isNilpotent_iff_charpoly (LieAlgebra.ad K W y))) |>.mp hn

set_option maxHeartbeats 1000000 in
private theorem adjointOpen_baseChange_witness (K : Type u) [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (s : IdentityLieStructure G.val)
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    let H := (groupBaseChange k K).obj G.val
    ∀ (sK : IdentityLieStructure H),
      letI := s.lieRing
      letI := s.lieAlgebra
      letI := sK.lieRing
      letI := sK.lieAlgebra
      ∀ (b : Module.Basis ι k (Specs.Lie k G.val)) (y : Specs.Lie K H),
        ¬ IsNilpotent (LieAlgebra.ad K (Specs.Lie K H) y) →
        ∃ v : ι → K, ((genericMatrix (adjointMatrixFamily b)).map
          (MvPolynomial.aeval v : MvPolynomial ι k →ₐ[k] K)).charpoly ≠ Polynomial.X ^ Fintype.card ι := by
  intro H sK
  let := s.lieRing
  let := s.lieAlgebra
  let := sK.lieRing
  let := sK.lieAlgebra
  intro b y hn
  obtain ⟨e, _⟩ := (identityLieBracketBaseChange k K G).2 s sK
  exact @adjointOpen_geometric_witness k _ (Specs.Lie k G.val) (Specs.Lie K H) ι K _ _
    s.lieRing s.lieAlgebra sK.lieRing sK.lieAlgebra _ _ b e y hn

set_option maxHeartbeats 1800000 in
theorem adjointNonnilpotentOpen : AdjointNonnilpotentOpen.{u} := by
  intro k _ G s
  let := s.lieRing
  let := s.lieAlgebra
  intro ι _ _ b
  let V := Specs.Lie k G.val
  let : AddCommGroup V := s.lieRing.toAddCommGroup
  let : Module k V := s.lieAlgebra.toModule
  let : SMul k V := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  let F := adjointMatrixFamily b
  let M := genericMatrix F
  obtain ⟨hopen, hmembers, hnonempty⟩ := characteristicPolynomialOpen k ι M
  let : FiniteDimensional k V := b.finiteDimensional_of_finite
  refine ⟨hopen, ?_, ?_⟩
  · intro x
    rw [hmembers k, genericMatrixSpecialization k ι k]
    have h : (∑ l, (b.equivFun x) l • (F (Pi.single l 1)).map (algebraMap k k)) =
        LinearMap.toMatrix b b (LieAlgebra.ad k V x) := by
      let T : V →ₗ[k] Matrix ι ι k :=
        (LinearMap.toMatrix b b).toLinearMap.comp (LieAlgebra.ad k V).toLinearMap
      have hi (l : ι) : (F (Pi.single l 1)).map (algebraMap k k) = T (b l) := by
        change (adjointMatrixFamily b (Pi.single l 1)).map (algebraMap k k) = _
        rw [adjointMatrixFamily_basis]
        rfl
      simp_rw [hi, ← map_smul T, ← map_sum]
      exact congrArg T (b.sum_repr x)
    rw [h, LinearMap.charpoly_toMatrix, ← Module.finrank_eq_card_basis b]
    exact not_congr (LinearMap.isNilpotent_iff_charpoly (LieAlgebra.ad k V x)).symm
  · intro hgeom
    let K := AlgebraicClosure k
    let H := (groupBaseChange k K).obj G.val
    obtain ⟨sK, τ, hτ, hτ', L, l, f, hf, y, hY, had⟩ := hgeom
    let := hτ
    let := hτ'
    let := sK.lieRing
    let := sK.lieAlgebra
    let W := Specs.Lie K H
    let : AddCommGroup W := sK.lieRing.toAddCommGroup
    let : Module K W := sK.lieAlgebra.toModule
    let HA : AffineGroupCategory K := ⟨H, by
      let : IsAffine G.val.X.left := G.property.1
      exact isAffine_baseChange K G.val⟩
    let d : W →ₗ⁅K⁆ Module.End K (τ → K) := faithfulLieHom HA L sK l f hf
    have hd : Function.Injective d := faithfulLieHom_injective HA L sK l f hf
    let T : Module.End K W := LieAlgebra.ad K W y
    have hs : T.IsSemisimple :=
      ((adjointFromFaithfulDifferential K W (τ → K) d hd y).1 hY)
    have hz : T ≠ 0 := had
    have hn : ¬ IsNilpotent T := fun h => hz (Module.End.eq_zero_of_isNilpotent_isSemisimple (f := T) h hs)
    obtain ⟨v, hw⟩ := adjointOpen_baseChange_witness K G s sK b y hn
    refine ⟨hnonempty K v hw, fun hInf => ?_⟩
    let := hInf
    obtain ⟨w, hw⟩ := characteristicPolynomialOpenRationalPoint k ι M K v ((hmembers K v).mpr hw)
    exact ⟨b.equivFun.symm w, by simpa only [b.equivFun.apply_symm_apply] using hw⟩

private theorem semisimple_is_geometric [PerfectField k] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Y : Matrix ι ι k) (h : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' Y)) :
    GeometricallySemisimple Y := by
  let K := AlgebraicClosure k
  let X := Matrix.toLinAlgEquiv' Y
  let b := Pi.basisFun k ι
  let B := b.baseChange K
  have hmat : LinearMap.toMatrix B B (X.baseChange K) = Y.map (algebraMap k K) := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix_apply, show B j = 1 ⊗ₜ[k] b j from Module.Basis.baseChange_apply K b j,
      LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    simp only [b, Pi.basisFun_repr, Pi.basisFun_apply, Matrix.map_apply]
    exact congrArg (algebraMap k K) (congrArg (fun M : Matrix ι ι k => M i j)
      (LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' Y))
  let e := B.equivFun
  let Z : Module.End K (ι → K) := Matrix.toLinAlgEquiv' (Y.map (algebraMap k K))
  have he : e.toLinearMap.comp (X.baseChange K) = Z.comp e.toLinearMap := by
    apply B.ext
    intro j
    have hj : e (B j) = Pi.single j 1 := by
      ext i
      change B.repr (B j) i = _
      simp [B.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]
    change e ((X.baseChange K) (B j)) = Z (e (B j))
    rw [hj, show Z (Pi.single j 1) = (Y.map (algebraMap k K)).col j by
      rw [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_single_one]]
    funext i
    have h := congrArg (fun M : Matrix ι ι K => M i j) hmat
    rw [LinearMap.toMatrix_apply] at h
    exact h
  exact (e.isSemisimple_iff _ Z he).mp (isSemisimple_baseChange (K := K) h)

private theorem adjoint_of_derivation_power (G : AffineAlgebraicGroup k) (s : IdentityLieStructure G.val)
    (A : HopfAlgebraCategory k) (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (D E : InvariantDerivation A) (m : ℕ) (h : E.val.toLinearMap = D.val.toLinearMap ^ m) :
    letI := s.lieRing
    letI := s.lieAlgebra
    let q := tangentComparison A G.val e
    LieAlgebra.ad k (Specs.Lie k G.val) (q E) = (LieAlgebra.ad k (Specs.Lie k G.val) (q D)) ^ m := by
  let := s.lieRing
  let := s.lieAlgebra
  intro q
  obtain ⟨n, b, _, L, l, Ad, _, hAd, _⟩ := adjointRepresentation k G s
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  have hmatrix (x : Specs.Lie k G.val) :
      LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad k (Specs.Lie k G.val) x) =
        InfinitesimalCommutator.matrixDifferential Ad l x := by
    ext i j
    have hv := congrFun (hAd x (b j)) i
    have hb : b.equivFun (b j) = Pi.single j 1 := by
      ext t
      change b.repr (b j) t = _
      rw [b.repr_self]
      simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
    rw [hb, Matrix.mulVec_single_one] at hv
    rw [LinearMap.toMatrixAlgEquiv_apply]
    exact hv.symm
  apply (LinearMap.toMatrixAlgEquiv b).injective
  rw [map_pow, hmatrix, hmatrix]
  change InfinitesimalCommutator.matrixDifferential Ad l (tangentComparison A G.val e E) =
    InfinitesimalCommutator.matrixDifferential Ad l (tangentComparison A G.val e D) ^ m
  rw [tangentComparison_matrix A G' e L.val l Ad E, tangentComparison_matrix A G' e L.val l Ad D]
  let M := RationalRepresentations.universalMatrix A G' L.val e l Ad
  change (fun i j => Coalgebra.counit (R := k) (E.val.toLinearMap (M i j))) = matrixAction A M D ^ m
  rw [h]
  exact matrixAction_powers A M (universalMatrix_coaction A G' e L.val l Ad) D m

theorem rationalSemisimpleWitness : RationalSemisimpleWitness.{u} := by
  intro k _ G L s A _ e ι _ _ l f hf
  let := s.lieRing
  let := s.lieAlgebra
  intro d M x hx
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  let V := Specs.Lie k G.val
  let : AddCommGroup V := s.lieRing.toAddCommGroup
  let : Module k V := s.lieAlgebra.toModule
  let zero : V := (0 : PointKernel G.val)
  let : Zero V := s.lieRing.toAddCommGroup.toZero
  have hzero : (0 : V) = zero := congrArg (fun g : AddGroup (PointKernel G.val) => g.toZero.zero) s.group_law
  let q := tangentComparison A G.val e
  let F := faithfulLieHom G' L s l f hf
  have hF := faithfulLieHom_injective G' L s l f hf
  have hFzero : F (0 : V) = 0 := F.map_zero
  have hM := universalMatrix_coaction A G' e L.val l f
  have hgen := faithfulMatrixGenerates k G' L A e ι l f hf
  have finish (y : V) (hy : GeometricallySemisimple (d y)) (hn : LieAlgebra.ad k V y ≠ 0) :
      Algebra.Smooth k (A ⧸ centralizerIdeal A M (d y)) ∧ centralizerIdeal A M (d y) ≠ ⊥ := by
    constructor
    · obtain ⟨D, rfl⟩ := q.surjective y
      have h := tangentComparison_matrix A G' e L.val l f D
      change d (q D) = matrixAction A M D at h
      rw [h] at hy ⊢
      exact matrixCentralizerSmooth k A ι M hM hgen D hy
    · intro hj
      apply hn
      apply LinearMap.ext
      intro z
      rw [LinearMap.zero_apply]
      exact ((centralizerLieComparison k G' L s A e ι l f hf y z).mp (by rw [hj]; exact bot_le)).trans hzero.symm
  have commute_lie (a b : V) (h : Commute (F a) (F b)) : ⁅a, b⁆ = zero := by
    rw [← hzero]
    apply hF
    change F ⁅a, b⁆ = F 0
    exact (F.map_lie a b).trans ((sub_eq_zero.mpr h.eq).trans F.map_zero.symm)
  rcases CharP.exists' k with hzero | ⟨p, hp, hpos⟩
  · let := hzero
    obtain ⟨y, n, h⟩ := characteristicZeroLieJordan k G' A e x
    have hj := h ι L.val l f
    have hj' : IsAdditiveJordanDecomposition (F x) (F y) (F n) := hj
    have hy := semisimple_is_geometric (d y) hj.semisimple
    have hn : LieAlgebra.ad k V y ≠ 0 := by
      intro h
      apply hx
      have hval (z : V) : ⁅y, z⁆ = (0 : V) := by
        have hv := LinearMap.congr_fun h z
        exact hv.trans (LinearMap.zero_apply _)
      have he : LieAlgebra.ad k V x = LieAlgebra.ad k V n := by
        apply LinearMap.ext
        intro z
        apply hF
        change F ⁅x, z⁆ = F ⁅n, z⁆
        have hm : F y * F z = F z * F y := by
          have hlie := F.map_lie y z
          rw [hval] at hlie
          change F (0 : V) = _ at hlie
          rw [hFzero] at hlie
          exact sub_eq_zero.mp hlie.symm
        rw [F.map_lie, F.map_lie]
        change F x * F z - F z * F x = F n * F z - F z * F n
        rw [hj'.sum, add_mul, mul_add, hm, add_sub_add_left_eq_sub]
      rw [he]
      exact ((adjointFromFaithfulDifferential k _ _ F hF n).2 hj'.nilpotent)
    have hcomm : Commute (F x) (F y) :=
      hj'.sum ▸ (Commute.refl (F y)).add_left hj'.commute.symm
    rcases finish y hy hn with ⟨hs, hjp⟩
    exact ⟨y, hy, commute_lie x y hcomm, hn, hs, hjp, Or.inl ⟨hzero, n, hj⟩⟩
  · let := hp
    let := hpos
    obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt (Fintype.card ι) hp.out.one_lt
    let D := q.symm x
    obtain ⟨E, he, hE⟩ := restrictedIteratedMatrixAction k A p r ι M hM D
    let y := q E
    have hd (U : InvariantDerivation A) : d (q U) = matrixAction A M U :=
      tangentComparison_matrix A G' e L.val l f U
    have hq : q D = x := q.apply_symm_apply x
    have hy : d y = d x ^ (p ^ r) := by
      change d (q E) = _
      rw [hd, ← hq, hd, hE]
    have hs : GeometricallySemisimple (d y) := by
      rw [hy]
      exact largePrimePowerGeometricallySemisimple k ι p r (d x) hr.le
    have hAd := adjoint_of_derivation_power G s A e D E (p ^ r) he
    change LieAlgebra.ad k V y = LieAlgebra.ad k V (q D) ^ (p ^ r) at hAd
    rw [hq] at hAd
    have hn : LieAlgebra.ad k V y ≠ 0 := fun h => hx ⟨p ^ r, hAd.symm.trans h⟩
    have hFpow : F y = (F x) ^ (p ^ r) := by
      change Matrix.toLinAlgEquiv' (d y) = _
      rw [hy, map_pow]
      rfl
    have hcomm := commute_lie x y (hFpow.symm ▸ (Commute.refl (F x)).pow_right (p ^ r))
    rcases finish y hs hn with ⟨hsm, hjp⟩
    exact ⟨y, hs, hcomm, hn, hsm, hjp, Or.inr ⟨p, r, hp.out, hpos, hr.le, hy, hAd⟩⟩

end NonnilpotentOpen

end

end LinearAlgebraicGroups.SemisimpleLieCentralizer
