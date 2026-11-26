import Specs.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Arithmetic.OddSpinModels
import LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import LinearAlgebraicGroups.Albert.SplitSpin
import LinearAlgebraicGroups.Classification.CellHomomorphism
import LinearAlgebraicGroups.Flag.FlagSchemes
import LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
import LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.LinearAlgebra.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.SimpleRing.Matrix
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SkolemNoether
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification

open Matrix
open scoped Matrix TensorProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels

open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OddSpinModels (coordinateVector evenSum)
open Specs.SymplecticDivisionForms (antiValue)
open Specs.Arithmetic

theorem corootLattice :
    Specs.Arithmetic.NontrialitarianSpinModels.CorootLattice.{u} := by
  intro ι _ _ _
  obtain ⟨hSpan, hLift⟩ := _root_.LinearAlgebraicGroups.Arithmetic.OddSpinModels.corootLattice ι
  refine ⟨?_, hLift⟩
  rw [← hSpan]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.subset_span (Or.inr hx)
  · apply Submodule.span_le.mpr
    rintro x (⟨i, hi | hi⟩ | hx)
    · obtain ⟨j, hij⟩ := exists_ne i
      have hd : coordinateVector ι i - coordinateVector ι j ∈
          Submodule.span ℤ (coroots ι) :=
        Submodule.subset_span ⟨i, j, hij.symm, Or.inl rfl⟩
      have hs : coordinateVector ι i + coordinateVector ι j ∈
          Submodule.span ℤ (coroots ι) :=
        Submodule.subset_span ⟨i, j, hij.symm, Or.inr (Or.inl rfl)⟩
      rw [hi, two_smul, ← sub_add_add_cancel]
      exact (Submodule.span ℤ (coroots ι)).add_mem hd hs
    · obtain ⟨j, hij⟩ := exists_ne i
      have hd : coordinateVector ι i - coordinateVector ι j ∈
          Submodule.span ℤ (coroots ι) :=
        Submodule.subset_span ⟨i, j, hij.symm, Or.inl rfl⟩
      have hs : coordinateVector ι i + coordinateVector ι j ∈
          Submodule.span ℤ (coroots ι) :=
        Submodule.subset_span ⟨i, j, hij.symm, Or.inr (Or.inl rfl)⟩
      rw [hi, two_smul, ← sub_add_add_cancel]
      exact (Submodule.span ℤ (coroots ι)).neg_mem
        ((Submodule.span ℤ (coroots ι)).add_mem hd hs)
    · exact Submodule.subset_span hx

theorem nonarchimedeanDivision :
    NonarchimedeanDivision.{u,v} := by
  intro F _ _ _ _ A _ _ _ hA s
  exact SymplecticInvolutionModels.nonarchimedeanPresentations hA s.anti

theorem archimedeanDivision :
    ArchimedeanDivision.{u} := by
  exact SymplecticInvolutionModels.archimedeanPresentations

theorem hyperbolicPartner :
    HyperbolicPartner.{u,v} := by
  intro F B V _ _ _ _ _ h₂ s h e he hee
  obtain ⟨p, hp⟩ := h.nondegenerate e he
  let f := MulOpposite.op (h.value e p)⁻¹ • p
  have hef : h.value e f = 1 := by
    rw [h.smul_right, mul_inv_cancel₀ hp]
  have hfe : h.value f e = -1 := by
    rw [h.skew e f, hef]
    simp [antiValue]
  let t := algebraMap F B ((2 : F)⁻¹)
  let a := t * h.value f f
  have ht : t + t = 1 := by
    rw [← map_add, ← two_mul, mul_inv_cancel₀ h₂, map_one]
  have hff : antiValue s.anti (h.value f f) = - h.value f f := by
    simpa using (congrArg Neg.neg (h.skew f f)).symm
  have ha : antiValue s.anti a = -a := by
    change MulOpposite.unop (s.anti (t * h.value f f)) = -a
    rw [map_mul, MulOpposite.unop_mul]
    change antiValue s.anti (h.value f f) * MulOpposite.unop (s.anti t) = -a
    rw [show MulOpposite.unop (s.anti t) = t by simp [t], hff,
      neg_mul, ← Algebra.commutes ((2 : F)⁻¹) (h.value f f)]
  let z := f + MulOpposite.op a • e
  have hez : h.value e z = 1 := by
    change h.value e (f + _) = 1
    rw [h.add_right, hef, h.smul_right, hee, zero_mul, add_zero]
  have hze : h.value z e = -1 := by
    rw [h.skew e z, hez]
    simp [antiValue]
  have hfz : h.value f z = h.value f f - a := by
    change h.value f (f + _) = _
    rw [h.add_right, h.smul_right f e a, hfe, neg_one_mul, sub_eq_add_neg]
  have hzf : h.value z f = h.value f f - a := by
    rw [h.skew f z, hfz]
    change -MulOpposite.unop (s.anti (h.value f f - a)) = _
    rw [map_sub, MulOpposite.unop_sub]
    change -(antiValue s.anti (h.value f f) - antiValue s.anti a) = _
    rw [ha, hff]
    abel
  refine ⟨z, hez, hze, ?_⟩
  change h.value z (f + _) = 0
  rw [h.add_right, hzf, h.smul_right z e a, hze, neg_one_mul]
  have haa : a + a = h.value f f := by
    dsimp [a]
    rw [← add_mul, ht, one_mul]
  rw [sub_eq_add_neg, add_assoc, ← neg_add, haa, add_neg_cancel]

section Clifford

open CliffordAlgebra MulOpposite

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  {q : QuadraticForm R M}

private noncomputable def evenCliffordMap (g : M ≃ₗ[R] M) (c : Rˣ)
    (hg : ∀ x, q (g x) = (c : R) * q x) : even q →ₐ[R] even q :=
  even.lift q {
    bilin := (↑c⁻¹ : R) • ((even.ι q).bilin.compl₁₂ g.toLinearMap g.toLinearMap)
    contract x := by
      change (↑c⁻¹ : R) • (even.ι q).bilin (g x) (g x) = algebraMap R (even q) (q x)
      rw [(even.ι q).contract, hg, map_mul, Algebra.smul_def, ← map_mul, ← map_mul, ← mul_assoc,
        Units.inv_mul, one_mul]
    contract_mid x y z := by
      change ((↑c⁻¹ : R) • (even.ι q).bilin (g x) (g y)) *
        ((↑c⁻¹ : R) • (even.ι q).bilin (g y) (g z)) = _
      rw [smul_mul_smul_comm, (even.ι q).contract_mid, hg, smul_smul]
      rw [mul_assoc, ← mul_assoc (↑c⁻¹ : R) (↑c : R), Units.inv_mul, one_mul]
      simp only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, smul_smul, mul_comm]
      rfl }

private theorem evenCliffordMap_pair (g : M ≃ₗ[R] M) (c : Rˣ)
    (hg : ∀ x, q (g x) = (c : R) * q x) (x y : M) :
    evenCliffordMap g c hg ((even.ι q).bilin x y) =
      (↑c⁻¹ : R) • (even.ι q).bilin (g x) (g y) := by
  rw [evenCliffordMap, even.lift_ι]
  rfl

private theorem evenCliffordMap_comp_inverse (g : M ≃ₗ[R] M) (c : Rˣ)
    (hg : ∀ x, q (g x) = (c : R) * q x)
    (hg' : ∀ x, q (g.symm x) = (↑c⁻¹ : R) * q x) :
    (evenCliffordMap g.symm c⁻¹ hg').comp (evenCliffordMap g c hg) = .id R (even q) := by
  apply even.algHom_ext
  apply EvenHom.ext
  ext x y
  simp [evenCliffordMap_pair, smul_smul]

private noncomputable def reverseEven : even q →ₐ[R] (even q)ᵐᵒᵖ where
  toFun x := op ⟨reverse x.val, (reverse_mem_evenOdd_iff (Q := q)).2 x.property⟩
  map_one' := by
    apply MulOpposite.unop_injective
    exact Subtype.ext reverse.map_one
  map_zero' := by
    apply MulOpposite.unop_injective
    exact Subtype.ext (map_zero reverse)
  map_add' x y := by
    apply MulOpposite.unop_injective
    exact Subtype.ext (map_add reverse x.val y.val)
  map_mul' x y := by
    apply MulOpposite.unop_injective
    exact Subtype.ext (reverse.map_mul x.val y.val)
  commutes' r := by
    apply MulOpposite.unop_injective
    exact Subtype.ext (reverse.commutes r)

private theorem reverseEven_pair (x y : M) :
    reverseEven ((even.ι q).bilin x y) = op ((even.ι q).bilin y x) := by
  apply MulOpposite.unop_injective
  apply Subtype.ext
  simp [reverseEven, even.ι, reverse.map_mul]

private noncomputable def evenCliffordEquiv (g : quadraticSimilitudes q) : even q ≃ₐ[R] even q :=
  AlgEquiv.ofAlgHom (evenCliffordMap g.val.1 g.val.2 g.property)
    (evenCliffordMap g.val.1.symm g.val.2⁻¹ g⁻¹.property)
    (evenCliffordMap_comp_inverse g.val.1.symm g.val.2⁻¹ g⁻¹.property
      (fun x => by simpa only [LinearEquiv.symm_symm, inv_inv] using g.property x))
    (evenCliffordMap_comp_inverse g.val.1 g.val.2 g.property g⁻¹.property)

private theorem evenCliffordEquiv_pair (g : quadraticSimilitudes q) (x y : M) :
    evenCliffordEquiv g ((even.ι q).bilin x y) =
      (↑g.val.2⁻¹ : R) • (even.ι q).bilin (g.val.1 x) (g.val.1 y) :=
  evenCliffordMap_pair g.val.1 g.val.2 g.property x y

private theorem evenCliffordEquiv_reverse (g : quadraticSimilitudes q) (a : even q) :
    (evenCliffordEquiv g (unop (reverseEven a)) : CliffordAlgebra q) =
      reverse ((evenCliffordEquiv g a : even q) : CliffordAlgebra q) := by
  let f := (evenCliffordEquiv g).toAlgHom
  have h : (AlgHom.op f).comp reverseEven = reverseEven.comp f := by
    apply even.algHom_ext
    apply EvenHom.ext
    ext x y
    change (AlgHom.op f) (reverseEven ((even.ι q).bilin x y)) =
      reverseEven (f ((even.ι q).bilin x y))
    rw [reverseEven_pair]
    change op (evenCliffordEquiv g ((even.ι q).bilin y x)) =
      reverseEven (evenCliffordEquiv g ((even.ι q).bilin x y))
    simp only [evenCliffordEquiv_pair, map_smul, reverseEven_pair]
    rfl
  exact congrArg (fun x : (even q)ᵐᵒᵖ => (unop x).val) (DFunLike.congr_fun h a)

theorem evenCliffordSimilitude :
    EvenCliffordSimilitude.{u} := by
  intro R M _ _ _ q g c hg
  let a : quadraticSimilitudes q := ⟨(g, c), hg⟩
  refine ⟨evenCliffordEquiv a, evenCliffordEquiv_pair a, ?_⟩
  intro x hx
  exact evenCliffordEquiv_reverse a x

open Polynomial in
private theorem squareRoot_tensor_inclusion
    {B : Type u} [Ring B] [Algebra R B] [Nontrivial R] (d : R) :
    Function.Injective (Algebra.TensorProduct.includeRight :
      B →ₐ[R] AdjoinRoot (X ^ 2 - C d) ⊗[R] B) := by
  let p : R[X] := X ^ 2 - C d
  let pb := AdjoinRoot.powerBasis' (monic_X_pow_sub_C d (by decide : 2 ≠ 0))
  let i : Fin pb.dim := ⟨0, by change 0 < p.natDegree; simp [p]⟩
  let l := pb.basis.coord i
  have h : pb.basis i = 1 := by rw [pb.basis_eq_pow]; exact pow_zero _
  have hl : l 1 = 1 := by
    rw [← h]
    change pb.basis.repr (pb.basis i) i = 1
    rw [Module.Basis.repr_self, Finsupp.single_eq_same]
  intro x y hxy
  change (1 : AdjoinRoot p) ⊗ₜ[R] x = 1 ⊗ₜ[R] y at hxy
  have hh := congrArg (fun z => TensorProduct.lid R B (TensorProduct.map l LinearMap.id z)) hxy
  simpa [TensorProduct.map_tmul, hl] using hh

open Polynomial in
set_option maxHeartbeats 500000 in
theorem evenCliffordVectorAction :
    EvenCliffordVectorAction.{u} := by
  intro R M _ _ _ q g c hg e he a x y hxy
  let Cq := CliffordAlgebra q
  by_cases hR : Nontrivial R
  swap
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    have : Subsingleton Cq := Module.subsingleton R Cq
    exact Subsingleton.elim _ _
  let _ := hR
  let p : R[X] := X ^ 2 - C (c : R)
  let A := AdjoinRoot p
  let B := A ⊗[R] Cq
  let j : Cq →ₐ[R] B := Algebra.TensorProduct.includeRight
  let r : A := AdjoinRoot.root p
  let τ : A := algebraMap R A (↑c⁻¹ : R) * r
  have hr : r * r = algebraMap R A (c : R) := by
    have h := AdjoinRoot.eval₂_root p
    change (X ^ 2 - C (c : R)).eval₂ (AdjoinRoot.of p) r = 0 at h
    rwa [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, pow_two, sub_eq_zero,
      ← AdjoinRoot.algebraMap_eq] at h
  have hτ : r * τ = 1 := by
    change r * (algebraMap R A (↑c⁻¹ : R) * r) = 1
    rw [← mul_assoc, mul_comm r, mul_assoc, hr, ← map_mul, Units.inv_mul, map_one]
  have hττ : τ * τ = algebraMap R A (↑c⁻¹ : R) := by
    change (algebraMap R A (↑c⁻¹ : R) * r) * τ = _
    rw [mul_assoc, hτ, mul_one]
  have hCoeff (d : R) (z : Cq) :
      algebraMap R A d • j z = j (d • z) := by
    rw [map_smul, algebraMap_smul]
  let L : M →ₗ[R] B := τ • j.toLinearMap.comp ((ι q).comp g.toLinearMap)
  have hL (z : M) : L z = τ • j (ι q (g z)) := rfl
  have hSq (z : M) : L z * L z = algebraMap R B (q z) := by
    rw [hL, smul_mul_smul_comm, hττ, ← map_mul, hCoeff, ι_sq_scalar, hg,
      Algebra.smul_def, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, j.commutes]
  let F := CliffordAlgebra.lift q ⟨L, hSq⟩
  have hF (z : M) : F (ι q z) = τ • j (ι q (g z)) := by
    change CliffordAlgebra.lift q ⟨L, hSq⟩ (ι q z) = _
    rw [lift_ι_apply, hL]
  let inc := (even q).val
  have hEven : F.comp inc = j.comp (inc.comp e) := by
    apply even.algHom_ext
    apply EvenHom.ext
    ext v w
    change F (ι q v * ι q w) = j (inc (e ((even.ι q).bilin v w)))
    rw [map_mul, hF, hF, he, smul_mul_smul_comm, hττ, ← map_mul, hCoeff]
    rfl
  have hFe (b : even q) : F (b : Cq) = j (e b : Cq) := DFunLike.congr_fun hEven b
  have hh := congrArg F hxy
  simp only [map_mul, hF, hFe, mul_smul_comm, smul_mul_assoc] at hh
  have hh' := congrArg (r • ·) hh
  simp only [smul_smul, hτ, one_smul] at hh'
  apply squareRoot_tensor_inclusion (c : R)
  simpa only [map_mul] using hh'

private noncomputable def cliffordSimilitudeHom (q : QuadraticForm R M) :
    quadraticSimilitudes q →* (even q ≃ₐ[R] even q) where
  toFun := evenCliffordEquiv
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply even.algHom_ext
    apply EvenHom.ext
    apply LinearMap.ext₂
    intro x y
    exact (evenCliffordEquiv_pair (1 : quadraticSimilitudes q) x y).trans (one_smul R _)
  map_mul' g h := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply even.algHom_ext
    apply EvenHom.ext
    apply LinearMap.ext₂
    intro x y
    change evenCliffordEquiv (g * h) ((even.ι q).bilin x y) =
      evenCliffordEquiv g (evenCliffordEquiv h ((even.ι q).bilin x y))
    rw [evenCliffordEquiv_pair, evenCliffordEquiv_pair h, map_smul, evenCliffordEquiv_pair,
      smul_smul]
    change (↑(g.val.2 * h.val.2)⁻¹ : R) • _ = (↑h.val.2⁻¹ * ↑g.val.2⁻¹ : R) • _
    rw [_root_.mul_inv_rev, Units.val_mul]
    rfl

private theorem evenCliffordEquiv_of_scalar (g h : quadraticSimilitudes q) (s : Rˣ)
    (hg : ∀ x, g.val.1 x = (s : R) • h.val.1 x) (hc : g.val.2 = s ^ 2 * h.val.2) :
    evenCliffordEquiv g = evenCliffordEquiv h := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply even.algHom_ext
  apply EvenHom.ext
  apply LinearMap.ext₂
  intro x y
  change evenCliffordEquiv g ((even.ι q).bilin x y) = evenCliffordEquiv h ((even.ι q).bilin x y)
  rw [evenCliffordEquiv_pair, evenCliffordEquiv_pair, hg x, hg y, LinearMap.map_smul₂, map_smul,
    smul_smul, smul_smul]
  have hs : g.val.2⁻¹ * (s * s) = h.val.2⁻¹ := by
    rw [hc, pow_two, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have he := congrArg Units.val hs
  rw [Units.val_mul, Units.val_mul] at he
  rw [mul_assoc, he]

private theorem evenCliffordEquiv_inner (g : quadraticSimilitudes q) (a : (even q)ˣ)
    (hc : g.val.2 = 1) (ha : ImplementsIsometry q a g.val.1) (z : even q) :
    evenCliffordEquiv g z = a.val * z * a.inv := by
  let f : even q →ₐ[R] even q :=
    { toFun := fun x => a.val * x * a.inv
      map_one' := by simp
      map_mul' := fun x y => by simp [mul_assoc]
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add, add_mul]
      commutes' := fun r => by rw [← Algebra.commutes, mul_assoc, a.val_inv, mul_one] }
  have h : (evenCliffordEquiv g).toAlgHom = f := by
    apply even.algHom_ext
    apply EvenHom.ext
    apply LinearMap.ext₂
    intro x y
    change evenCliffordEquiv g ((even.ι q).bilin x y) = a.val * (even.ι q).bilin x y * a.inv
    rw [evenCliffordEquiv_pair, hc, inv_one, Units.val_one, one_smul]
    apply Subtype.ext
    change ι q (g.val.1 x) * ι q (g.val.1 y) =
      (a.val : CliffordAlgebra q) * (ι q x * ι q y) * a.inv.val
    rw [← mul_assoc (a.val : CliffordAlgebra q), ha x, mul_assoc (ι q (g.val.1 x)),
      ha y, mul_assoc, mul_assoc, show (a.val : CliffordAlgebra q) * a.inv.val = 1 from
        congrArg Subtype.val a.val_inv, mul_one]
  exact DFunLike.congr_fun h z

theorem cliffordSimilitudeAction :
    CliffordSimilitudeAction.{u} := by
  intro R M _ _ _ q
  refine ⟨cliffordSimilitudeHom q, evenCliffordEquiv_pair, evenCliffordEquiv_of_scalar,
    evenCliffordEquiv_inner, ?_⟩
  intro g a h hn ha
  let e := evenCliffordEquiv g
  let b := Units.map e.toMonoidHom a
  change reverse (b.val : CliffordAlgebra q) * (b.val : CliffordAlgebra q) = 1 ∧
    ImplementsIsometry q b (g.val.1 * h * g.val.1⁻¹)
  constructor
  · have hN : unop (reverseEven a.val) * a.val = 1 := Subtype.ext hn
    have h' := congrArg (fun z : even q => (e z : CliffordAlgebra q)) hN
    rw [map_mul, map_one, Subalgebra.coe_mul, evenCliffordEquiv_reverse g a.val] at h'
    exact h'
  · intro x
    have hx := evenCliffordVectorAction q g.val.1
      g.val.2 g.property e.toAlgHom (evenCliffordEquiv_pair g) a.val
        (g.val.1.symm x) (h (g.val.1.symm x)) (ha (g.val.1.symm x))
    rw [LinearEquiv.apply_symm_apply] at hx
    exact hx

open _root_.LinearAlgebraicGroups.Albert
open private fromOriginal fromOriginal_ι from LinearAlgebraicGroups.Albert.CliffordModel

set_option maxHeartbeats 420000 in
theorem cliffordSimilitudeBaseChange :
    CliffordSimilitudeBaseChange.{u} := by
  intro R M _ _ _ I _ q b S _ _ Q
  let j := fromOriginal S q b
  have hJ (x : CliffordAlgebra q) (hx : x ∈ even q) : j x ∈ even Q := by
    change x ∈ evenOdd q 0 at hx
    induction x, hx using even_induction with
    | algebraMap r =>
      rw [j.commutes]
      exact ((even Q).restrictScalars R).algebraMap_mem r
    | add x y hx hy h₁ h₂ =>
      rw [map_add]
      exact (even Q).add_mem h₁ h₂
    | ι_mul_ι_mul x y z hz h₁ =>
      rw [map_mul, map_mul, show j (ι q x) = ι Q (1 ⊗ₜ[R] x) from fromOriginal_ι S q b x,
        show j (ι q y) = ι Q (1 ⊗ₜ[R] y) from fromOriginal_ι S q b y]
      exact (even Q).mul_mem (ι_mul_ι_mem_evenOdd_zero Q _ _) h₁
  let J : even q →ₐ[R] even Q := (j.comp (even q).val).codRestrict ((even Q).restrictScalars R)
    fun x => hJ x.val x.property
  have hPair (x y : M) : J ((even.ι q).bilin x y) =
      (even.ι Q).bilin (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y) := by
    apply Subtype.ext
    change j (ι q x * ι q y) = ι Q (1 ⊗ₜ[R] x) * ι Q (1 ⊗ₜ[R] y)
    exact (map_mul j _ _).trans
      (congrArg₂ (· * ·) (fromOriginal_ι S q b x) (fromOriginal_ι S q b y))
  refine ⟨J, hPair, ?_⟩
  intro g h c
  have hc : (c : S) = algebraMap R S (g.val.2 : R) := rfl
  have hcInv : (↑c⁻¹ : S) = algebraMap R S (↑g.val.2⁻¹ : R) := by
    change ((Units.map (algebraMap R S).toMonoidHom g.val.2)⁻¹ : Sˣ).val = _
    rw [← map_inv]
    rfl
  have hh (x : M) : h (1 ⊗ₜ[R] x) = (1 ⊗ₜ[R] g.val.1 x) :=
    LinearEquiv.baseChange_tmul R S M M 1 x
  have hForm : Q.comp h.toLinearMap = (c : S) • Q := by
    apply baseChange_ext
    intro x
    change Q (h (1 ⊗ₜ[R] x)) = (c : S) * Q (1 ⊗ₜ[R] x)
    rw [hh]
    change CliffordSpecification.coefficientForm S q b (1 ⊗ₜ[R] g.val.1 x) =
      (c : S) * CliffordSpecification.coefficientForm S q b (1 ⊗ₜ[R] x)
    simp only [CliffordModel.coefficientForm_tmul, one_mul, g.property x, hc, map_mul]
  refine ⟨DFunLike.congr_fun hForm, ?_⟩
  intro f F hf hF z
  have he : J.comp f = (F.restrictScalars R).comp J := by
    apply even.algHom_ext
    apply EvenHom.ext
    apply LinearMap.ext₂
    intro x y
    change J (f ((even.ι q).bilin x y)) = F (J ((even.ι q).bilin x y))
    rw [hf, map_smul, hPair, hPair, hF, hh, hh, hcInv, algebraMap_smul]
  exact DFunLike.congr_fun he z

end Clifford

section SpinSimilitudeScalarExtension

open CliffordAlgebra TensorProduct

open LinearAlgebraicGroups.Albert
open SpinSpecification (ScalarClifford evenPart)

noncomputable section
variable {k M I : Type u} [Field k] [AddCommGroup M] [Module k M] [LinearOrder I]
  (q : QuadraticForm k M) (b : Module.Basis I k M) (S : Type u) [CommRing S] [Algebra k S]

open private cliffordEquiv_even cliffordEquiv_vector from LinearAlgebraicGroups.Albert.SpinFunctor

private def evenTensorInclusion : S ⊗[k] even q →ₐ[S] ScalarClifford q S :=
  Algebra.TensorProduct.map (AlgHom.id S S) (even q).val

private theorem evenTensorInclusion_linear :
    (evenTensorInclusion q S).toLinearMap = (evenOdd q 0).subtype.baseChange S := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  rfl

private theorem evenTensorInclusion_injective :
    Function.Injective (evenTensorInclusion q S) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (evenOdd q 0).subtype Subtype.val_injective
  intro x y hxy
  apply h
  have he (z : S ⊗[k] even q) : (evenTensorInclusion q S) z = (evenOdd q 0).subtype.lTensor S z :=
    (DFunLike.congr_fun (evenTensorInclusion_linear q S) z).trans
      (congrFun (LinearMap.baseChange_eq_lTensor (A := S) (evenOdd q 0).subtype) z)
  rw [← he x, ← he y]
  exact hxy

private theorem evenTensorInclusion_range (z : ScalarClifford q S) :
    z ∈ Set.range (evenTensorInclusion q S) ↔ z ∈ evenPart q S := by
  change z ∈ LinearMap.range (evenTensorInclusion q S).toLinearMap ↔ _
  rw [evenTensorInclusion_linear]
  rfl

local notation "Q" => CliffordSpecification.coefficientForm S q b

private def evenTensorEquiv : (S ⊗[k] even q) ≃ₐ[S] even Q := by
  let E := CliffordModel.baseChangeEquiv S q b
  let i := evenTensorInclusion q S
  let f := (E.toAlgHom.comp i).codRestrict (even Q) fun x =>
    (cliffordEquiv_even q S b (i x)).mpr ((evenTensorInclusion_range q S _).mp ⟨x, rfl⟩)
  refine AlgEquiv.ofBijective f ⟨fun x y h => ?_, fun z => ?_⟩
  · exact evenTensorInclusion_injective q S (E.injective (congrArg Subtype.val h))
  · have hz : E.symm z.val ∈ evenPart q S := by
      apply (cliffordEquiv_even q S b _).mp
      change E (E.symm z.val) ∈ even Q
      rw [E.apply_symm_apply]
      exact z.property
    obtain ⟨x, hx⟩ := (evenTensorInclusion_range q S _).mpr hz
    exact ⟨x, Subtype.ext ((congrArg E hx).trans (E.apply_symm_apply z.val))⟩

private theorem evenTensorEquiv_val (x : S ⊗[k] even q) :
    (evenTensorEquiv q b S x).val = CliffordModel.baseChangeEquiv S q b (evenTensorInclusion q S x) :=
  rfl

private theorem evenTensorEquiv_pair (x y : M) :
    evenTensorEquiv q b S (1 ⊗ₜ[k] (even.ι q).bilin x y) =
      (even.ι Q).bilin (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y) := by
  apply Subtype.ext
  rw [evenTensorEquiv_val]
  change CliffordModel.baseChangeEquiv S q b (1 ⊗ₜ[k] (ι q x * ι q y)) =
    ι Q (1 ⊗ₜ[k] x) * ι Q (1 ⊗ₜ[k] y)
  rw [show (1 : S) ⊗ₜ[k] (ι q x * ι q y) = (1 ⊗ₜ[k] ι q x) * (1 ⊗ₜ[k] ι q y) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
    map_mul, CliffordModel.baseChangeEquiv_ι, CliffordModel.baseChangeEquiv_ι]

private def extendedSimilitude (g : quadraticSimilitudes q) : quadraticSimilitudes Q :=
  ⟨(LinearEquiv.baseChange k S M M g.val.1, Units.map (algebraMap k S).toMonoidHom g.val.2),
    ((cliffordSimilitudeBaseChange q b S).choose_spec.2 g).1⟩

private theorem evenTensorEquiv_similitude (g : quadraticSimilitudes q)
    (z : S ⊗[k] even q) :
    evenTensorEquiv q b S
      (Algebra.TensorProduct.map (AlgHom.id S S) (evenCliffordEquiv g).toAlgHom z) =
        evenCliffordEquiv (extendedSimilitude q b S g) (evenTensorEquiv q b S z) := by
  obtain ⟨J, hPair, hJ⟩ := cliffordSimilitudeBaseChange q b S
  let E := evenTensorEquiv q b S
  let f := evenCliffordEquiv g
  let G := extendedSimilitude q b S g
  let F := evenCliffordEquiv G
  have hJE : J = ((E.toAlgHom.restrictScalars k).comp Algebra.TensorProduct.includeRight) := by
    apply even.algHom_ext
    apply EvenHom.ext
    apply LinearMap.ext₂
    intro x y
    change J ((even.ι q).bilin x y) = E (1 ⊗ₜ[k] (even.ι q).bilin x y)
    rw [hPair, evenTensorEquiv_pair]
  have h : ∀ z : even q, J (f z) = F (J z) := (hJ g).2 f.toAlgHom F.toAlgHom
    (evenCliffordEquiv_pair g) (evenCliffordEquiv_pair G)
  induction z with
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul s z =>
    change E (s ⊗ₜ[k] f z) = F (E (s ⊗ₜ[k] z))
    have hsmul (v : even q) : (s ⊗ₜ[k] v) = s • (1 ⊗ₜ[k] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsmul, hsmul, map_smul, map_smul, map_smul]
    have hz := h z
    rw [hJE] at hz
    exact congrArg (s • ·) hz

open SpinSpecification (spinUnits IsVectorAction vectors reversion)
open private baseChangeEquiv_reverse from LinearAlgebraicGroups.Albert.CliffordModel
open private conjugate_inverse from LinearAlgebraicGroups.Albert.SpinFunctor

include b in
private theorem spin_in_evenTensor (a : (ScalarClifford q S)ˣ)
    (ha : a ∈ spinUnits q S) :
    ∃ y : (S ⊗[k] even q)ˣ, Units.map (evenTensorInclusion q S).toMonoidHom y = a := by
  have haInv : a⁻¹ ∈ spinUnits q S :=
    (SpinFunctor.spinSubgroup q S b).inv_mem ha
  obtain ⟨x, hx⟩ := (evenTensorInclusion_range q S _).mpr ha.1
  obtain ⟨z, hz⟩ := (evenTensorInclusion_range q S _).mpr haInv.1
  let j := evenTensorInclusion q S
  have hxz : x * z = 1 := evenTensorInclusion_injective q S (by
    change j (x * z) = j 1
    rw [map_mul, map_one, hx, hz]
    exact a.val_inv)
  have hzx : z * x = 1 := evenTensorInclusion_injective q S (by
    change j (z * x) = j 1
    rw [map_mul, map_one, hz, hx]
    exact a.inv_val)
  exact ⟨⟨x, z, hxz, hzx⟩, Units.ext hx⟩

set_option maxHeartbeats 470000 in
private theorem tensorCliffordSimilitude_spin (g : quadraticSimilitudes q)
    (a : (S ⊗[k] even q)ˣ) (h : (S ⊗[k] M) ≃ₗ[S] (S ⊗[k] M))
    (ha : Units.map (evenTensorInclusion q S).toMonoidHom a ∈ spinUnits q S)
    (hh : IsVectorAction q S (Units.map (evenTensorInclusion q S).toMonoidHom a) h) :
    let f := Algebra.TensorProduct.map (AlgHom.id S S) (evenCliffordEquiv g).toAlgHom
    let z' := Units.map (evenTensorInclusion q S).toMonoidHom (Units.map f.toMonoidHom a)
    z' ∈ spinUnits q S ∧ IsVectorAction q S z'
      ((extendedSimilitude q b S g).val.1 * h * (extendedSimilitude q b S g).val.1⁻¹) := by
  intro f z'
  let F := CliffordModel.baseChangeEquiv S q b
  have hF (x : S ⊗[k] M) : F (vectors q S x) = ι Q x := cliffordEquiv_vector q S b x
  let E := evenTensorEquiv q b S
  let G := extendedSimilitude q b S g
  let i := evenTensorInclusion q S
  let z := Units.map i.toMonoidHom a
  let w := Units.map E.toMonoidHom a
  let w' := Units.map (evenCliffordEquiv G).toMonoidHom w
  have hzw : F z.val = (w.val : CliffordAlgebra Q) := (evenTensorEquiv_val q b S a.val).symm
  have hzw' : F z'.val = (w'.val : CliffordAlgebra Q) := by
    change F (i (f a.val)) = (evenCliffordEquiv G (E a.val) : CliffordAlgebra Q)
    rw [← evenTensorEquiv_val q b S, evenTensorEquiv_similitude]
  have hr : reverse (w.val : CliffordAlgebra Q) * (w.val : CliffordAlgebra Q) = 1 := by
    rw [← hzw, ← baseChangeEquiv_reverse S q b, ← map_mul, ← map_one F]
    exact congrArg F ha.2.1
  have hv : ImplementsIsometry Q w h := by
    intro x
    have h₀ : vectors q S (h x) = z.val * vectors q S x * z.inv := hh x
    have hy : vectors q S (h x) * z.val = z.val * vectors q S x := by
      rw [h₀, mul_assoc (z.val * _), z.inv_val, mul_one]
    have h₁ := congrArg F hy
    rw [map_mul, map_mul, hzw] at h₁
    change F (vectors q S (h x)) * (w.val : CliffordAlgebra Q) =
      (w.val : CliffordAlgebra Q) * F (vectors q S x) at h₁
    rw [hF, hF] at h₁
    exact h₁.symm
  obtain ⟨C, hC, _, _, hA⟩ := cliffordSimilitudeAction Q
  have hCG : C G = evenCliffordEquiv G := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply even.algHom_ext
    apply EvenHom.ext
    apply LinearMap.ext₂
    intro x y
    exact (hC G x y).trans (evenCliffordEquiv_pair G x y).symm
  obtain ⟨hn, hv'⟩ := hA G w h hr hv
  rw [hCG] at hn hv'
  let h' := G.val.1 * h * G.val.1⁻¹
  have hnorm : reversion q S z'.val * z'.val = 1 := by
    apply F.injective
    rw [map_mul, map_one, baseChangeEquiv_reverse S q b, hzw']
    exact hn
  have hvec : IsVectorAction q S z' h' := by
    intro x
    have h₀ : z'.val * vectors q S x = vectors q S (h' x) * z'.val := by
      apply F.injective
      rw [map_mul, map_mul, hzw']
      change (w'.val : CliffordAlgebra Q) * F (vectors q S x) =
        F (vectors q S (h' x)) * (w'.val : CliffordAlgebra Q)
      rw [hF, hF]
      exact hv' x
    change vectors q S (h' x) = z'.val * vectors q S x * z'.inv
    rw [h₀, mul_assoc, z'.val_inv, mul_one]
  refine ⟨⟨(evenTensorInclusion_range q S _).mp ⟨f a.val, rfl⟩, hnorm, ?_, ?_⟩, hvec⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨h' x, hvec x⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨h'.symm x, ?_⟩
    have hx := hvec (h'.symm x)
    rw [LinearEquiv.apply_symm_apply] at hx
    rw [hx]
    simpa only [inv_inv] using (conjugate_inverse q S z'⁻¹ (vectors q S (h'.symm x))).symm


theorem spinSimilitudeScalarExtension : SpinSimilitudeScalarExtension.{u} := by
  intro k M I _ _ _ _ q b
  refine ⟨cliffordSimilitudeHom q, evenCliffordEquiv_pair, ?_, ?_⟩
  · intro S _ _ j
    refine ⟨evenTensorInclusion_injective q S, spin_in_evenTensor q b S, ?_⟩
    intro g a h gS aS f aS' ha hh
    exact tensorCliffordSimilitude_spin q b S g a h ha hh
  · intro S T _ _ _ _ f g z f₀
    let C := evenCliffordEquiv g
    change f₀ (Algebra.TensorProduct.map (AlgHom.id S S) C.toAlgHom z) =
      Algebra.TensorProduct.map (AlgHom.id T T) C.toAlgHom (f₀ z)
    induction z with
    | tmul r v => rfl
    | add x y hx hy => simp only [map_add, hx, hy]


end

end SpinSimilitudeScalarExtension

section QuadraticPair

variable {R I : Type u} [CommRing R] [Fintype I] [DecidableEq I]
  {J : Matrix I I R}

private theorem adjoint_mul (hJ : J * J = 1) (X Y : Matrix I I R) :
    adjoint J (X * Y) = adjoint J Y * adjoint J X := by
  simp only [adjoint, transpose_mul, mul_assoc]
  rw [← mul_assoc J J, hJ, one_mul]

private theorem adjoint_square (hJT : J.transpose = J) (hJ : J * J = 1)
    (X : Matrix I I R) : adjoint J (adjoint J X) = X := by
  simp only [adjoint, transpose_mul, transpose_transpose, hJT, mul_assoc]
  rw [← mul_assoc J J, hJ, one_mul, mul_one]

private theorem trace_adjoint (hJ : J * J = 1) (X : Matrix I I R) :
    (adjoint J X).trace = X.trace := by
  rw [adjoint, trace_mul_cycle, hJ, one_mul, trace_transpose]

private theorem alternatingMatrix_iff_exists_sub_transpose (C : Matrix I I R) :
    (∀ v, diagonalValue C v = 0) ↔ ∃ D, C = D - D.transpose := by
  constructor
  · intro h
    have hDiag (i : I) : C i i = 0 := by
      simpa [diagonalValue, mulVec_single_one] using h (Pi.single i 1)
    have hSkew (i j : I) : C i j = -C j i := by
      have he := h ((Pi.single i 1 : I → R) + Pi.single j 1)
      simp [diagonalValue, mulVec_add, dotProduct_add, add_dotProduct, hDiag] at he
      exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he)
    let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
    refine ⟨Matrix.of fun i j => if i < j then C i j else 0, ?_⟩
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, not_lt_of_gt hij]
    · simp [hDiag]
    · simp [hji, not_lt_of_gt hji, hSkew i j]
  · rintro ⟨D, rfl⟩ v
    simp [diagonalValue, sub_mulVec, dotProduct_sub, dotProduct_transpose_mulVec]

omit [DecidableEq I] in
private theorem trace_mul_eq_diagonalValue (C : Matrix I I R) (v : I → R) :
    (C * vecMulVec v v).trace = diagonalValue C v := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm, diagonalValue]

private theorem mul_gram_transpose (hJT : J.transpose = J) (hJ : J * J = 1)
    (X : selfAdjoint J) : (X.val * J).transpose = X.val * J := by
  have hX : J * X.val.transpose * J = X.val := X.property
  rw [transpose_mul, hJT]
  have h := congrArg (· * J) hX
  simpa only [mul_assoc, hJ, mul_one] using h

private theorem trace_gram_pairing (hJ : J * J = 1) (L X : Matrix I I R) :
    ((J * L) * (X * J)).trace = (L * X).trace := by
  rw [mul_assoc, trace_mul_comm J, ← mul_assoc L, mul_assoc (L * X), hJ, mul_one]

private theorem trace_pairing_iff (hJT : J.transpose = J) (hJ : J * J = 1)
    (L : Matrix I I R) :
    (∀ X : selfAdjoint J, semitrace J L X = 0) ↔ ∀ x, diagonalValue (J * L) x = 0 := by
  constructor
  · intro h v
    let Y := vecMulVec v v
    have hY : Y.transpose = Y := transpose_vecMulVec v v
    have hX : Y * J ∈ selfAdjoint J := by
      change J * (Y * J).transpose * J = Y * J
      rw [transpose_mul, hJT, hY, ← mul_assoc J J, hJ, one_mul]
    have hx := h ⟨Y * J, hX⟩
    change (L * (Y * J)).trace = 0 at hx
    rw [← trace_gram_pairing hJ L (Y * J), mul_assoc Y, hJ, mul_one] at hx
    exact (trace_mul_eq_diagonalValue (J * L) v).symm.trans hx
  · intro hq X
    obtain ⟨D, hD⟩ := (alternatingMatrix_iff_exists_sub_transpose (J * L)).mp hq
    change (L * X.val).trace = 0
    rw [← trace_gram_pairing hJ, hD, sub_mul, trace_sub, sub_eq_zero]
    rw [← trace_transpose (D.transpose * (X.val * J)), transpose_mul,
      transpose_transpose, mul_gram_transpose hJT hJ, trace_mul_comm]

theorem traceOrthogonality :
    TraceOrthogonality.{u} := by
  intro R I _ _ _ h₂ J L hJT hJ
  rw [trace_pairing_iff hJT hJ]
  refine ⟨fun hq => ⟨hq, ?_⟩, And.left⟩
  obtain ⟨D, hD⟩ := (alternatingMatrix_iff_exists_sub_transpose (J * L)).mp hq
  refine ⟨J * D, ?_⟩
  have hDj : J * (J * D).transpose * J = J * D.transpose := by
    rw [transpose_mul, hJT, mul_assoc J, mul_assoc D.transpose, hJ, mul_one]
  have hD' : J * L = D + D.transpose := by
    rw [hD, sub_eq_add_neg]
    congr 1
    ext i j
    apply neg_eq_of_add_eq_zero_left
    rw [← two_mul, h₂, zero_mul]
  rw [adjoint, hDj, ← mul_add, ← hD', ← mul_assoc, hJ, one_mul]

private theorem hyperbolicGram_transpose (I R : Type u) [Fintype I] [DecidableEq I]
    [CommRing R] : (hyperbolicGram I R).transpose = hyperbolicGram I R := by
  simp [hyperbolicGram, fromBlocks_transpose]

private theorem hyperbolicGram_square (I R : Type u) [Fintype I] [DecidableEq I]
    [CommRing R] : hyperbolicGram I R * hyperbolicGram I R = 1 := by
  simp [hyperbolicGram, fromBlocks_multiply, fromBlocks_one]

private theorem splitSemitrace_over_ring (I R : Type u)
    [Fintype I] [DecidableEq I] [CommRing R] :
    let J := hyperbolicGram I R
    let L := hyperbolicProjection I R
    let q := OddSpinModels.hyperbolicForm I R
    adjoint J L + L = 1 ∧
    (∀ x, diagonalValue (J * L) x = q x) ∧
    (∀ X : Matrix (I ⊕ I) (I ⊕ I) R,
      ∃ h : X + adjoint J X ∈ selfAdjoint J,
        semitrace J L ⟨X + adjoint J X, h⟩ = X.trace) ∧
    ∀ L' : Matrix (I ⊕ I) (I ⊕ I) R,
      (∀ x, diagonalValue (J * L') x = q x) → semitrace J L' = semitrace J L := by
  intro J L q
  have hJT := hyperbolicGram_transpose I R
  have hJ := hyperbolicGram_square I R
  change J.transpose = J at hJT
  change J * J = 1 at hJ
  have hL : adjoint J L + L = 1 := by
    simp [J, L, adjoint, hyperbolicGram, hyperbolicProjection, fromBlocks_transpose,
      fromBlocks_multiply]
    rw [fromBlocks_add]
    simp [fromBlocks_one]
  have hq (x : I ⊕ I → R) : diagonalValue (J * L) x = q x := by
    simp only [J, L, hyperbolicGram, hyperbolicProjection, fromBlocks_multiply,
      mul_zero, zero_add, add_zero, mul_one, diagonalValue, q,
      OddSpinModels.hyperbolicForm, LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
  refine ⟨hL, hq, ?_, ?_⟩
  · intro X
    have hX : X + adjoint J X ∈ selfAdjoint J := by
      change adjoint J (X + adjoint J X) = X + adjoint J X
      simp only [adjoint, transpose_add, mul_add, add_mul]
      change adjoint J X + adjoint J (adjoint J X) = X + adjoint J X
      rw [adjoint_square hJT hJ, add_comm]
    refine ⟨hX, ?_⟩
    change (L * (X + adjoint J X)).trace = X.trace
    have h : (L * adjoint J X).trace = (adjoint J L * X).trace := by
      rw [← trace_adjoint hJ (L * adjoint J X), adjoint_mul hJ,
        adjoint_square hJT hJ, trace_mul_comm]
    rw [mul_add, trace_add, h, ← trace_add, ← add_mul, add_comm L, hL, one_mul]
  · intro L' hL'
    apply LinearMap.ext
    intro X
    have hq' (x : I ⊕ I → R) : diagonalValue (J * (L' - L)) x = 0 := by
      have hEq := sub_eq_zero.mpr ((hL' x).trans (hq x).symm)
      simpa only [diagonalValue, mul_sub, sub_mulVec, dotProduct_sub] using hEq
    have hx := (trace_pairing_iff hJT hJ (L' - L)).mpr hq' X
    change ((L' - L) * X.val).trace = 0 at hx
    change (L' * X.val).trace = (L * X.val).trace
    rwa [sub_mul, trace_sub, sub_eq_zero] at hx

theorem splitSemitrace :
    SplitSemitrace.{u} := by
  intro I R _ _ _ _
  exact splitSemitrace_over_ring I R

private theorem from_central_unit [Nonempty I] {C : Matrix I I R} (hUnit : IsUnit C)
    (hC : ∀ X, C * X = X * C) :
    ∃ c : Rˣ, C = (c : R) • 1 := by
  have hc : C ∈ Subalgebra.center R (Matrix I I R) := by
    rw [Subalgebra.mem_center_iff]
    exact fun Y => (hC Y).symm
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hc)
  rw [Algebra.algebraMap_eq_smul_one] at hc
  have hdet := hUnit.map detMonoidHom
  change IsUnit C.det at hdet
  rw [← hc, det_smul, det_one, mul_one] at hdet
  obtain ⟨d, rfl⟩ := (isUnit_pow_iff Fintype.card_ne_zero).mp hdet
  exact ⟨d, hc.symm⟩

private theorem matrix_conjugate_eq_scalar_iff [Nonempty I] (g : (Matrix I I R)ˣ) :
    (∀ X, conjugate g X = X) ↔
      ∃ c : Rˣ, g.val = algebraMap R (Matrix I I R) (c : R) := by
  simp only [Algebra.algebraMap_eq_smul_one]
  constructor
  · intro h
    apply from_central_unit g.isUnit
    intro X
    have hh := congrArg (· * g.val) (h X)
    simpa [conjugate, mul_assoc] using hh
  · rintro ⟨c, hc⟩ X
    have hh : g.val * X = X * g.val := by rw [hc]; simp
    rw [conjugate, hh, mul_assoc, g.val_inv, mul_one]

private theorem adjoint_conjugate_iff [Nonempty I] (hJT : J.transpose = J)
    (hJ : J * J = 1) (g : (Matrix I I R)ˣ) :
    (∀ X, adjoint J (conjugate g X) = conjugate g (adjoint J X)) ↔
      ∃ c : Rˣ, g.val.transpose * J * g.val = (c : R) • J := by
  have hf (X Y : Matrix I I R) : adjoint J (X * Y) = adjoint J Y * adjoint J X :=
    adjoint_mul hJ X Y
  have hOne : adjoint J 1 = 1 := by simp [adjoint, hJ]
  have hInv₁ : adjoint J g.val * adjoint J g.inv = 1 := by
    rw [← hf, g.inv_val, hOne]
  have hInv₂ : adjoint J g.inv * adjoint J g.val = 1 := by
    rw [← hf, g.val_inv, hOne]
  let C := adjoint J g.val * g.val
  have hEquiv (X : Matrix I I R) :
      adjoint J (conjugate g X) = conjugate g (adjoint J X) ↔
        adjoint J X * C = C * adjoint J X := by
    simp only [conjugate, hf]
    constructor
    · intro h
      have hh := congrArg (fun Y => adjoint J g.val * Y * g.val) h
      simp only [mul_assoc] at hh
      rw [← mul_assoc (adjoint J g.val) (adjoint J g.inv), hInv₁, one_mul,
        g.inv_val, mul_one] at hh
      simpa [C, mul_assoc] using hh
    · intro h
      have hh := congrArg (fun Y => adjoint J g.inv * Y * g.inv) h
      simp only [C, mul_assoc] at hh
      rw [g.val_inv, mul_one,
        ← mul_assoc (adjoint J g.inv) (adjoint J g.val), hInv₂, one_mul] at hh
      simpa only [mul_assoc] using hh
  have hC : IsUnit C :=
    (show IsUnit (adjoint J g.val) from ⟨⟨_, _, hInv₁, hInv₂⟩, rfl⟩).mul g.isUnit
  have hJC : J * C = g.val.transpose * J * g.val := by
    simp only [C, adjoint, mul_assoc]
    rw [← mul_assoc J J, hJ, one_mul]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := from_central_unit hC (fun Y => by
      have hh := (hEquiv (adjoint J Y)).mp (h (adjoint J Y))
      simpa [adjoint_square hJT hJ] using hh.symm)
    refine ⟨c, ?_⟩
    rw [← hJC, hc, Matrix.mul_smul, mul_one]
  · rintro ⟨c, hc⟩ X
    have hc' : C = (c : R) • (1 : Matrix I I R) := by
      have hh := congrArg (J * ·) (hJC.trans hc)
      simpa only [Matrix.mul_smul, ← mul_assoc, hJ, one_mul] using hh
    rw [hEquiv, hc']
    simp

omit [DecidableEq I] in
private theorem diagonalValue_congr (Q g : Matrix I I R) (x : I → R) :
    diagonalValue (g.transpose * Q * g) x = diagonalValue Q (g *ᵥ x) := by
  simp only [diagonalValue, ← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]

/-- Polarizing the matrix quadratic identity recovers its multiplier on the
Gram matrix, over every test ring. -/
private theorem matrixQuadraticSimilitude_polar (g : (Matrix I I R)ˣ)
    (L : Matrix I I R) (hPol : J * L + (J * L).transpose = J)
    (c : Rˣ) (hc : ∀ x, diagonalValue (J * L) (g.val *ᵥ x) =
      (c : R) * diagonalValue (J * L) x) :
    g.val.transpose * J * g.val = (c : R) • J := by
  let D := g.val.transpose * (J * L) * g.val - (c : R) • (J * L)
  have hD (x : I → R) : diagonalValue D x = 0 := by
    have h := sub_eq_zero.mpr ((diagonalValue_congr (J * L) g.val x).trans (hc x))
    simpa [D, diagonalValue, sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul] using h
  obtain ⟨Y, hY⟩ := (alternatingMatrix_iff_exists_sub_transpose D).mp hD
  have hSkew : D + D.transpose = 0 := by
    rw [hY, transpose_sub, transpose_transpose, sub_add_sub_cancel, sub_self]
  rw [← hPol]
  have h := hSkew
  simp only [D, transpose_sub, transpose_mul, transpose_transpose, transpose_smul] at h
  rw [mul_add, add_mul, smul_add]
  apply sub_eq_zero.mp
  calc
    _ = (g.val.transpose * (J * L) * g.val - (c : R) • (J * L)) +
        (g.val.transpose * (L.transpose * J.transpose) * g.val -
          (c : R) • (L.transpose * J.transpose)) := by
          rw [transpose_mul]
          abel
    _ = 0 := by simpa only [mul_assoc] using h

private theorem conjugate_pair_iff [Nonempty I] (hJT : J.transpose = J)
    (hJ : J * J = 1) (L : Matrix I I R) (hPol : J * L + (J * L).transpose = J)
    (g : (Matrix I I R)ˣ) :
    PreservesQuadraticPair J L (conjugate g) ↔
      ∃ c : Rˣ, ∀ x, diagonalValue (J * L) (g.val *ᵥ x) =
        (c : R) * diagonalValue (J * L) x := by
  have hTrace (X : selfAdjoint J) :
      (L * conjugate g X.val).trace = (conjugate g⁻¹ L * X.val).trace := by
    change (L * (g.val * X.val * g.inv)).trace = (g.inv * L * g.val * X.val).trace
    rw [← mul_assoc L, ← mul_assoc L, trace_mul_comm _ g.inv]
    simp only [mul_assoc]
  have hF :
      (∀ X : selfAdjoint J, (L * conjugate g X.val).trace = semitrace J L X) ↔
      ∀ x, diagonalValue (J * conjugate g⁻¹ L) x = diagonalValue (J * L) x := by
    simp only [hTrace]
    have hT := trace_pairing_iff hJT hJ (conjugate g⁻¹ L - L)
    simpa only [semitrace, LinearMap.coe_mk, AddHom.coe_mk, sub_mul, trace_sub,
      diagonalValue, mul_sub, sub_mulVec, dotProduct_sub, sub_eq_zero] using hT
  have hQ (c : Rˣ) (hc : g.val.transpose * J * g.val = (c : R) • J) (x : I → R) :
      diagonalValue (J * conjugate g⁻¹ L) x =
        (↑c⁻¹ : R) * diagonalValue (J * L) (g.val *ᵥ x) := by
    have hMove : J * g.inv = (↑c⁻¹ : R) • (g.val.transpose * J) := by
      have hh := congrArg (fun T => (↑c⁻¹ : R) • (T * g.inv)) hc
      simp only [mul_assoc, g.val_inv, mul_one, smul_mul_assoc, smul_smul, Units.inv_mul,
        one_smul] at hh
      exact hh.symm
    change diagonalValue (J * (g.inv * L * g.val)) x = _
    rw [← mul_assoc J, ← mul_assoc J, hMove, smul_mul_assoc, smul_mul_assoc,
      mul_assoc g.val.transpose J]
    simp only [diagonalValue, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact congrArg ((↑c⁻¹ : R) * ·) (diagonalValue_congr (J * L) g.val x)
  rw [PreservesQuadraticPair, adjoint_conjugate_iff hJT hJ, hF]
  constructor
  · rintro ⟨⟨c, hc⟩, h⟩
    refine ⟨c, fun x => ?_⟩
    have hh := congrArg ((c : R) * ·) (hQ c hc x).symm
    rw [← mul_assoc, Units.mul_inv, one_mul, h x] at hh
    exact hh
  · rintro ⟨c, hc⟩
    have hPol' := matrixQuadraticSimilitude_polar g L hPol c hc
    exact ⟨⟨c, hPol'⟩, fun x => by rw [hQ c hPol', hc x, ← mul_assoc, Units.inv_mul, one_mul]⟩

private theorem hyperbolicProjection_polar (I R : Type u) [Fintype I] [DecidableEq I]
    [CommRing R] :
    let J := hyperbolicGram I R
    let L := hyperbolicProjection I R
    J * L + (J * L).transpose = J := by
  dsimp only
  simp [hyperbolicGram, hyperbolicProjection, fromBlocks_multiply, fromBlocks_transpose]
  rw [fromBlocks_add]
  simp

theorem projectiveSimilitudes :
    ProjectiveSimilitudes.{u} := by
  have hAll (I R : Type u) [Fintype I] [DecidableEq I] [Nonempty I] [CommRing R] (h₂ : (2 : R) = 0)
      (g : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ) :
      PreservesQuadraticPair (hyperbolicGram I R) (hyperbolicProjection I R) (conjugate g) ↔
        ∃ c : Rˣ, ∀ x, OddSpinModels.hyperbolicForm I R (g.val *ᵥ x) =
          (c : R) * OddSpinModels.hyperbolicForm I R x := by
    have hq := (splitSemitrace I R h₂).2.1
    simpa only [hq] using conjugate_pair_iff (hyperbolicGram_transpose I R)
      (hyperbolicGram_square I R) (hyperbolicProjection I R) (hyperbolicProjection_polar I R) g
  refine ⟨?_, ?_⟩
  · intro I R _ _ _ _ h₂ J L q g
    exact ⟨hAll I R h₂ g, matrix_conjugate_eq_scalar_iff g⟩
  · intro I K _ _ _ _ h₂ J L q f
    have hCSA : _root_.Specs.RM03.CSA.isCentralSimple K (Matrix (I ⊕ I) (I ⊕ I) K) :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    obtain ⟨g, hg⟩ := RM03.CSA.algEquiv_isInner hCSA f
    change ∀ X, f X = conjugate g X at hg
    constructor
    · intro hf
      have hp : PreservesQuadraticPair J L (conjugate g) := by
        have eqF : (f : Matrix (I ⊕ I) (I ⊕ I) K → _) = conjugate g := funext hg
        rwa [← eqF]
      obtain ⟨c, hc⟩ := (hAll I K h₂ g).mp hp
      exact ⟨g, c, hg, hc⟩
    · rintro ⟨a, c, ha, hc⟩
      have hp := (hAll I K h₂ a).mpr ⟨c, hc⟩
      have eqF : (f : Matrix (I ⊕ I) (I ⊕ I) K → _) = conjugate a := funext ha
      rwa [eqF]

theorem splitPairIsometries : SplitPairIsometries.{u} := by
  intro I R _ _ _ _ J L g
  let q := OddSpinModels.hyperbolicForm I R
  have hq (x : I ⊕ I → R) : diagonalValue (J * L) x = q x :=
    (splitSemitrace_over_ring I R).2.1 x
  have hJ : J * J = 1 := hyperbolicGram_square I R
  have hPol : J * L + (J * L).transpose = J := hyperbolicProjection_polar I R
  have hPair := conjugate_pair_iff (hyperbolicGram_transpose I R) hJ L hPol g
  have hAdj (c : Rˣ) (hc : ∀ x, diagonalValue (J * L) (g.val *ᵥ x) =
      (c : R) * diagonalValue (J * L) x) :
      adjoint J g.val * g.val = (c : R) • 1 := by
    unfold adjoint
    rw [mul_assoc J g.val.transpose J, mul_assoc J, matrixQuadraticSimilitude_polar g L hPol c hc,
      Matrix.mul_smul, hJ]
  constructor
  · intro hg
    have h (x : I ⊕ I → R) : diagonalValue (J * L) (g.val *ᵥ x) =
        ((1 : Rˣ) : R) * diagonalValue (J * L) x := by
      simpa only [hq, Units.val_one, one_mul] using hg x
    exact ⟨by simpa only [Units.val_one, one_smul] using hAdj 1 h, hPair.mpr ⟨1, h⟩⟩
  · rintro ⟨hσ, hp⟩
    obtain ⟨c, hc⟩ := hPair.mp hp
    let i : I ⊕ I := Sum.inl (Classical.choice inferInstance)
    have hscalar := congrArg (fun X : Matrix (I ⊕ I) (I ⊕ I) R => X i i)
      ((hAdj c hc).symm.trans hσ)
    have hc1 : (c : R) = 1 := by simpa [Matrix.smul_apply] using hscalar
    intro x
    refine (hq _).symm.trans ((hc x).trans ?_)
    rw [hc1, one_mul]
    exact hq x

end QuadraticPair

section SplitOrthogonalModel

noncomputable section

open AlgebraicGeometry CategoryTheory
open Specs.StandardGroups
open private Representation Representation.mk Representation.equiv Representation.hopf
  Representation.naturality Representation.operations Representation.compatible Representation.convolutionIso
  generalLinearRepresentation glEvaluation glEvaluation_entry glCoordinates_ext spectrumPointsIso
  from LinearAlgebraicGroups.Affine.StandardGroups

variable {I R S : Type u} [Fintype I] [DecidableEq I] [CommRing R] [CommRing S]

private def normDifference (M : Matrix (I ⊕ I) (I ⊕ I) R) : Matrix (I ⊕ I) (I ⊕ I) R :=
  let Q := hyperbolicGram I R * hyperbolicProjection I R
  M.transpose * Q * M - Q

private abbrev OrthogonalEquationIndex (I : Type u) := (I ⊕ I) ⊕ ((I ⊕ I) × (I ⊕ I))

private def normEquations (M : Matrix (I ⊕ I) (I ⊕ I) R) : OrthogonalEquationIndex I → R :=
  Sum.elim (fun i => normDifference M i i) (fun (i, j) => normDifference M i j + normDifference M j i)

private theorem normEquations_map (f : R →+* S) (M : Matrix (I ⊕ I) (I ⊕ I) R) (e : OrthogonalEquationIndex I) :
    normEquations (M.map f) e = f (normEquations M e) := by
  have h : normDifference (M.map f) = (normDifference M).map f := by
    simp [normDifference, Matrix.map_mul, Matrix.map_sub, Matrix.transpose_map,
      hyperbolicGram, hyperbolicProjection, Matrix.fromBlocks_map]
  cases e with
  | inl i => simp [normEquations, h, Matrix.map_apply]
  | inr ij => simp [normEquations, h, Matrix.map_apply]

private theorem normEquations_iff (M : Matrix (I ⊕ I) (I ⊕ I) R) :
    (∀ x, OddSpinModels.hyperbolicForm I R (M *ᵥ x) = OddSpinModels.hyperbolicForm I R x) ↔
      ∀ e, normEquations M e = 0 := by
  have hQ (x : I ⊕ I → R) := (splitSemitrace_over_ring I R).2.1 x
  have h (x : I ⊕ I → R) : diagonalValue (normDifference M) x =
      OddSpinModels.hyperbolicForm I R (M *ᵥ x) - OddSpinModels.hyperbolicForm I R x := by
    change diagonalValue (_ - _) _ = _
    rw [← hQ (M *ᵥ x), ← hQ x, ← diagonalValue_congr]
    simp only [diagonalValue, sub_mulVec, dotProduct_sub]
  have hAll : (∀ x, diagonalValue (normDifference M) x = 0) ↔
      ∀ x, OddSpinModels.hyperbolicForm I R (M *ᵥ x) = OddSpinModels.hyperbolicForm I R x :=
    forall_congr' fun x => by rw [h, sub_eq_zero]
  rw [← hAll, alternatingMatrix_iff_exists_sub_transpose]
  constructor
  · rintro ⟨D, hD⟩ (i | ⟨i, j⟩)
    · simp [normEquations, hD]
    · simp only [normEquations, hD, Sum.elim_inr, Matrix.sub_apply, Matrix.transpose_apply]
      abel
  · intro hn
    let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
      (Fintype.equivFin (I ⊕ I)).injective
    let D := normDifference M
    have hDiag (i : I ⊕ I) : D i i = 0 := hn (Sum.inl i)
    have hSkew (i j : I ⊕ I) : D i j = -D j i := eq_neg_of_add_eq_zero_left (hn (Sum.inr (i, j)))
    refine ⟨Matrix.of fun i j => if i < j then D i j else 0, ?_⟩
    ext i j
    change D i j = (if i < j then D i j else 0) - (if j < i then D j i else 0)
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, not_lt_of_gt hij]
    · simp [hDiag]
    · simp [hji, not_lt_of_gt hji, hSkew i j]

open private dualMatrix dualMatrix_mul dualMatrix_transpose from
  LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure

theorem splitOrthogonalTangent :
    SplitOrthogonalTangent.{u} := by
  intro k I _ _ _ X q Y
  let J := hyperbolicGram I k
  let B := J * hyperbolicProjection I k
  let W := X.transpose * B + B * X
  have hB : hyperbolicGram I (DualNumber k) * hyperbolicProjection I (DualNumber k) =
      B.map (TrivSqZeroExt.inlHom k k) := by
    simp [B, J, hyperbolicGram, hyperbolicProjection, Matrix.map_mul, Matrix.fromBlocks_map]
  have hDiff : normDifference (infinitesimalOrthogonalMatrix X) = dualMatrix 0 W := by
    change (dualMatrix 1 X).transpose * (hyperbolicGram I (DualNumber k) *
      hyperbolicProjection I (DualNumber k)) * dualMatrix 1 X - _ = _
    rw [hB]
    change (dualMatrix 1 X).transpose * dualMatrix B 0 * dualMatrix 1 X - dualMatrix B 0 = _
    rw [dualMatrix_transpose, dualMatrix_mul, dualMatrix_mul]
    simp only [transpose_one, one_mul, mul_one, mul_zero, zero_add]
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · change B i j - B i j = 0
      exact sub_self _
    · change ((B * X) i j + (X.transpose * B) i j) - 0 =
        (X.transpose * B) i j + (B * X) i j
      rw [sub_zero, add_comm]
  have hPolar : B + B.transpose = J := hyperbolicProjection_polar I k
  have hW : W = (B.transpose * X).transpose + B * X := by
    simp [W, Matrix.transpose_mul]
  have hDiag (i : I ⊕ I) : W i i = Y i i := by
    change W i i = (J * X) i i
    rw [hW, Matrix.add_apply, Matrix.transpose_apply, ← Matrix.add_apply, ← add_mul,
      add_comm B.transpose B, hPolar]
  have hSum : W + W.transpose = Y + Y.transpose := by
    change W + W.transpose = J * X + (J * X).transpose
    calc
      _ = (B * X + B.transpose * X) + (B * X + B.transpose * X).transpose := by
        rw [hW]
        simp only [Matrix.transpose_add, transpose_transpose]
        abel
      _ = _ := by rw [← add_mul, hPolar]
  change (∀ x, OddSpinModels.hyperbolicForm I (DualNumber k)
    (infinitesimalOrthogonalMatrix X *ᵥ x) = OddSpinModels.hyperbolicForm I (DualNumber k) x) ↔ _
  rw [normEquations_iff]
  have hInl (i : I ⊕ I) : normEquations (infinitesimalOrthogonalMatrix X) (Sum.inl i) =
      dualMatrix 0 W i i := by
    change normDifference (infinitesimalOrthogonalMatrix X) i i = _
    rw [hDiff]
  have hInr (i j : I ⊕ I) : normEquations (infinitesimalOrthogonalMatrix X) (Sum.inr (i, j)) =
      dualMatrix 0 W i j + dualMatrix 0 W j i := by
    change normDifference (infinitesimalOrthogonalMatrix X) i j +
      normDifference (infinitesimalOrthogonalMatrix X) j i = _
    rw [hDiff]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have h' : W i i = 0 := congrArg (fun a : DualNumber k => a.snd) ((hInl i).symm.trans (h (.inl i)))
      exact (hDiag i).symm.trans h'
    · rw [← hSum]
      apply Matrix.ext
      intro i j
      exact congrArg (fun a : DualNumber k => a.snd) ((hInr i j).symm.trans (h (.inr (i, j))))
  · rintro ⟨hDiag', hSum'⟩ (i | ⟨i, j⟩)
    · rw [hInl]
      exact TrivSqZeroExt.ext rfl ((hDiag i).trans (hDiag' i))
    · rw [hInr]
      apply TrivSqZeroExt.ext
      · change (0 : k) + 0 = 0
        exact zero_add 0
      · exact congrArg (fun Z : Matrix (I ⊕ I) (I ⊕ I) k => Z i j) (hSum.trans hSum')

private def mapOrthogonal (f : R →+* S) : orthogonalMatrices I R →* orthogonalMatrices I S :=
  ((Matrix.GeneralLinearGroup.map f).comp (orthogonalMatrices I R).subtype).codRestrict
    (orthogonalMatrices I S) fun g => by
      apply (normEquations_iff _).mpr
      intro a
      change normEquations (g.val.val.map f) a = 0
      rw [normEquations_map, (normEquations_iff g.val.val).mp g.property, map_zero]

private def orthogonalMatrixPoints (k I : Type u) [Field k] [Fintype I] [DecidableEq I] :
    TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (orthogonalMatrices I R)
  map f := GrpCat.ofHom (mapOrthogonal f.hom.toRingHom)
  map_id _ := GrpCat.ext fun _ => Subtype.ext (Units.ext rfl)
  map_comp _ _ := GrpCat.ext fun _ => Subtype.ext (Units.ext rfl)

variable {k : Type u} [Field k]

private def orthogonalIdeal (k I : Type u) [Field k] [Fintype I] [DecidableEq I] :
    Ideal (GLCoordinates k (I ⊕ I)) :=
  Ideal.span (Set.range (normEquations (universalMatrix k (I ⊕ I))))

private abbrev OrthogonalCoordinates (k I : Type u) [Field k] [Fintype I] [DecidableEq I] :=
  GLCoordinates k (I ⊕ I) ⧸ orthogonalIdeal k I

local notation "qO" => Ideal.Quotient.mkₐ k (orthogonalIdeal k I)
local notation "MGL" => universalMatrix k (I ⊕ I)

private abbrev orthoEvaluation {R : Type u} [CommRing R] [Algebra k R]
    (f : OrthogonalCoordinates k I →ₐ[k] R) : orthogonalMatrices I R :=
  let g := Representation.equiv (generalLinearRepresentation (k := k) (ι := I ⊕ I))
    (CommAlgCat.of k R) (f.comp qO)
  ⟨g, (normEquations_iff g.val).mpr fun a => by
    have h : g.val = (MGL).map (f.comp qO) := by
      have hInv := (Representation.equiv (generalLinearRepresentation (k := k) (ι := I ⊕ I))
        (CommAlgCat.of k R)).symm_apply_apply (f.comp qO)
      change glEvaluation g = f.comp qO at hInv
      ext i j
      exact (glEvaluation_entry g i j).symm.trans (DFunLike.congr_fun hInv (MGL i j))
    rw [h]
    change normEquations ((MGL).map (f.comp qO).toRingHom) a = 0
    rw [normEquations_map]
    change f (qO (normEquations MGL a)) = 0
    have hzero : qO (normEquations MGL a) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span ⟨a, rfl⟩
    rw [hzero, map_zero]⟩

private def orthoCoordinates {R : Type u} [CommRing R] [Algebra k R]
    (g : orthogonalMatrices I R) : OrthogonalCoordinates k I →ₐ[k] R := by
  let f : GLCoordinates k (I ⊕ I) →ₐ[k] R := glEvaluation g.val
  refine Ideal.Quotient.liftₐ (orthogonalIdeal k I) f ?_
  have h : (MGL).map f.toRingHom = g.val.val := Matrix.ext (glEvaluation_entry g.val)
  have hle : orthogonalIdeal k I ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change f.toRingHom (normEquations MGL a) = 0
    rw [← normEquations_map f.toRingHom, h]
    exact (normEquations_iff _).mp g.property a
  exact fun a ha => hle ha

private theorem orthoCoordinates_comp {R : Type u} [CommRing R] [Algebra k R]
    (g : orthogonalMatrices I R) : (orthoCoordinates g).comp qO = glEvaluation g.val := by
  unfold orthoCoordinates
  apply Ideal.Quotient.liftₐ_comp

private def orthogonalRepresentation :
    Representation (OrthogonalCoordinates k I) (orthogonalMatrixPoints k I) :=
  Representation.mk (fun R =>
    { toFun := orthoEvaluation
      invFun := orthoCoordinates
      left_inv := fun f => by
        apply Ideal.Quotient.algHom_ext k
        rw [orthoCoordinates_comp]
        exact (Representation.equiv (generalLinearRepresentation (k := k) (ι := I ⊕ I)) R)
          |>.symm_apply_apply (f.comp qO)
      right_inv := fun g => by
        change orthogonalMatrices I R at g
        apply Subtype.ext
        change (Representation.equiv (generalLinearRepresentation (k := k) (ι := I ⊕ I)) R)
          ((orthoCoordinates g).comp qO) = g.val
        rw [orthoCoordinates_comp]
        exact (Representation.equiv (generalLinearRepresentation (k := k) (ι := I ⊕ I)) R)
          |>.apply_symm_apply g.val })
    (fun a f => Subtype.ext (Representation.naturality (generalLinearRepresentation (k := k) (ι := I ⊕ I))
      a (f.comp qO)))

local instance : HopfAlgebra k (OrthogonalCoordinates k I) :=
  Representation.hopf (orthogonalRepresentation (k := k) (I := I))

local instance : HopfAlgebra k (GLCoordinates k (I ⊕ I)) :=
  StandardGroups.generalLinearHopf k (I ⊕ I)

private def orthogonalGroup (k I : Type u) [Field k] [Fintype I] [DecidableEq I] :
    AffineAlgebraicGroup k := spectrum k (OrthogonalCoordinates k I)

private def orthogonalInclusion : (orthogonalGroup k I).val ⟶ (StandardGroups.generalLinearGroup k (I ⊕ I)).val :=
  let h := Representation.compatible (generalLinearRepresentation (k := k) (ι := I ⊕ I))
    (orthogonalRepresentation (k := k) (I := I)) qO (fun _ => (orthogonalMatrices I _).subtype)
    (fun _ _ => rfl)
  specGroupMap (CommHopfAlgCat.ofHom (BialgHom.ofAlgHom qO h.2.1.symm h.1))

private def orthogonalPointsIso :
    (groupPointsFunctor k).obj (orthogonalGroup k I).val ≅ orthogonalMatrixPoints k I :=
  spectrumPointsIso (Representation.convolutionIso (orthogonalRepresentation (k := k) (I := I)))

private theorem orthogonalInclusion_points (R : TestAlgebra k)
    (g : ((groupPointsFunctor k).obj (orthogonalGroup k I).val).obj R) :
    (StandardGroups.generalLinearGroupPointsIso k (I ⊕ I)).hom.app R
        (((groupPointsFunctor k).map orthogonalInclusion).app R g) =
      (orthogonalPointsIso.hom.app R g).val := by
  let O := CommHopfAlgCat.of k (OrthogonalCoordinates k I)
  let L := CommHopfAlgCat.of k (GLCoordinates k (I ⊕ I))
  let eO := (hopfSpecPointIso O).app R
  let eL := (hopfSpecPointIso L).app R
  obtain ⟨f, rfl⟩ := eO.groupIsoToMulEquiv.surjective g
  let F := f.ofConv
  have h : ((groupPointsFunctor k).map orthogonalInclusion).app R (eO.hom f) =
      eL.hom (WithConv.toConv (F.comp qO)) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom F.toRingHom) ≫ Spec.map (CommRingCat.ofHom (qO).toRingHom) =
      Spec.map (CommRingCat.ofHom (F.comp qO).toRingHom)
    exact (Spec.map_comp _ _).symm
  change (StandardGroups.generalLinearGroupPointsIso k (I ⊕ I)).hom.app R
    (((groupPointsFunctor k).map orthogonalInclusion).app R (eO.hom f)) = _
  rw [h]
  change (Representation.equiv (generalLinearRepresentation (k := k) (ι := I ⊕ I)) R)
      ((eL.inv (eL.hom (WithConv.toConv (F.comp qO)))).ofConv) =
    (orthoEvaluation ((eO.inv (eO.hom f)).ofConv)).val
  have hL : eL.inv (eL.hom (WithConv.toConv (F.comp qO))) = WithConv.toConv (F.comp qO) :=
    eL.groupIsoToMulEquiv.symm_apply_apply _
  have hO : eO.inv (eO.hom f) = f := eO.groupIsoToMulEquiv.symm_apply_apply f
  exact congrArg (fun u => (Representation.equiv (generalLinearRepresentation (k := k) (ι := I ⊕ I)) R)
    u.ofConv) hL |>.trans (congrArg (fun u => (orthoEvaluation u.ofConv).val) hO).symm

theorem splitOrthogonalModel :
    SplitOrthogonalModel.{u} := by
  intro k I _ _ _
  let e := orthogonalPointsIso (k := k) (I := I)
  refine ⟨⟨orthogonalGroup k I, StandardGroups.generalLinearGroup k (I ⊕ I),
    StandardGroups.generalLinearGroupPointsIso k (I ⊕ I), orthogonalInclusion, ?_,
    fun R => (e.app R).groupIsoToMulEquiv, ?_, ?_⟩⟩
  · exact IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mkₐ k (orthogonalIdeal k I)).toRingHom)
      Ideal.Quotient.mk_surjective
  · intro R S f g
    exact congrArg (fun g : (orthogonalMatrixPoints k I).obj S => g.val.val)
      (ConcreteCategory.congr_hom (e.hom.naturality f) g)
  · intro R g
    exact orthogonalInclusion_points R g

end

end SplitOrthogonalModel

theorem splitOrthogonalTangentBlocks : SplitOrthogonalTangentBlocks.{u} := by
  intro k I _ _ _ X q
  constructor
  · refine (splitOrthogonalTangent k I X).trans ?_
    let A := X.toBlocks₁₁
    let B := X.toBlocks₁₂
    let C := X.toBlocks₂₁
    let D := X.toBlocks₂₂
    have hX : hyperbolicGram I k * X = fromBlocks C D A B := by
      rw [← fromBlocks_toBlocks X, hyperbolicGram, fromBlocks_multiply]
      simp [A, B, C, D]
    change (∀ i, (hyperbolicGram I k * X) i i = 0) ∧
        hyperbolicGram I k * X + (hyperbolicGram I k * X).transpose = 0 ↔ _
    rw [hX, fromBlocks_transpose, fromBlocks_add, ← fromBlocks_zero, fromBlocks_inj]
    constructor
    · rintro ⟨hd, hc, hda, _, hb⟩
      refine ⟨eq_neg_of_add_eq_zero_left hda, fun i => hd (Sum.inr i), ?_,
        fun i => hd (Sum.inl i), ?_⟩
      · intro i j
        exact eq_neg_of_add_eq_zero_left (congrFun₂ hb i j)
      · intro i j
        exact eq_neg_of_add_eq_zero_left (congrFun₂ hc i j)
    · rintro ⟨hd, hdB, hB, hdC, hC⟩
      change D = -A.transpose at hd
      change ∀ i j, B i j = -B j i at hB
      change ∀ i j, C i j = -C j i at hC
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rintro (i | i)
        · exact hdC i
        · exact hdB i
      · ext i j
        change C i j + C j i = 0
        rw [hC i j, neg_add_cancel]
      · rw [hd, neg_add_cancel]
      · rw [hd, transpose_neg, transpose_transpose, add_neg_cancel]
      · ext i j
        change B i j + B j i = 0
        rw [hB i j, neg_add_cancel]
  · intro R _ _ t T T' Y i j
    unfold Y T T' Specs.SymplecticMatrixStructure.hyperbolicDiagonal
    simp only [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Sum.elim_inl, Sum.elim_inr, inv_inv, Matrix.map_apply, Matrix.of_apply]
    exact ⟨by ring, by ring, by ring⟩

section SplitSpinImage

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Albert
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification (ExtendedForm IsVectorAction muTwoUnderlying)
open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup IsSchemeKernel)
open Specs.FlagSchemes (toBasePoint)
open private changeModule changeModule_coord changeModule_basis spinUnitPoints spinUnitPoints_represents
  from LinearAlgebraicGroups.Albert.SpinFunctor
open private isPullback_of_affine_fibres from LinearAlgebraicGroups.Flag.FlagSchemes
open private finite_of_finite_kernel from LinearAlgebraicGroups.Classification.CellHomomorphism
open private schemeKernel_of_comp_mono from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable {R S : Type u} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

local notation "q₀" => OddSpinModels.hyperbolicForm I k
local notation "b₀" => Pi.basisFun k (I ⊕ I)

private theorem hyperbolicForm_apply (x : I ⊕ I → R) :
    OddSpinModels.hyperbolicForm I R x = ∑ i, x (Sum.inl i) * x (Sum.inr i) := by
  simp [OddSpinModels.hyperbolicForm, Matrix.toLinearMap₂'_apply', Matrix.fromBlocks_mulVec,
    dotProduct, Fintype.sum_sum_type]

private theorem hyperbolicForm_polar_ker : LinearMap.ker (q₀).polarBilin = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  have h (y : I ⊕ I → k) : (q₀).polarBilin x y = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y
  have hpol (y : I ⊕ I → k) : (q₀).polarBilin x y =
      ∑ i, (x (Sum.inl i) * y (Sum.inr i) + y (Sum.inl i) * x (Sum.inr i)) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hyperbolicForm_apply,
      Pi.add_apply, mul_add, add_mul]
    simp only [Finset.sum_add_distrib]
    abel
  funext i
  cases i with
  | inl i =>
    simpa [hpol, Pi.single_apply, mul_ite] using h (Pi.single (Sum.inr i) 1)
  | inr i =>
    simpa [hpol, Pi.single_apply, ite_mul] using h (Pi.single (Sum.inl i) 1)

variable [LinearOrder (I ⊕ I)]

private theorem extended_hyperbolicForm (x : R ⊗[k] (I ⊕ I → k)) :
    ExtendedForm q₀ R b₀ x = OddSpinModels.hyperbolicForm I R (((b₀).baseChange R).equivFun x) := by
  let Q := (OddSpinModels.hyperbolicForm I R).comp ((b₀).baseChange R).equivFun.toLinearMap
  have h : Q = ExtendedForm q₀ R b₀ :=
    (CliffordModel.coefficient_form_unique R q₀ b₀ Q).mpr fun y => by
      have hy (i : I ⊕ I) : ((b₀).baseChange R).equivFun (1 ⊗ₜ[k] y) i = algebraMap k R (y i) := by
        simp [Module.Basis.equivFun_apply, Algebra.smul_def]
      change OddSpinModels.hyperbolicForm I R (((b₀).baseChange R).equivFun (1 ⊗ₜ[k] y)) =
        algebraMap k R (q₀ y)
      simp only [hyperbolicForm_apply, hy, map_sum, map_mul]
  exact (DFunLike.congr_fun h x).symm

private def linearEquivMatrix (b : Module.Basis (I ⊕ I) R (R ⊗[k] (I ⊕ I → k))) :
    ((R ⊗[k] (I ⊕ I → k)) ≃ₗ[R] (R ⊗[k] (I ⊕ I → k))) →*
      Matrix.GeneralLinearGroup (I ⊕ I) R :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R _).symm.toMonoidHom

omit [LinearOrder (I ⊕ I)] in
private theorem linearEquivMatrix_val (g : (R ⊗[k] (I ⊕ I → k)) ≃ₗ[R] (R ⊗[k] (I ⊕ I → k))) :
    (linearEquivMatrix ((b₀).baseChange R) g).val =
      LinearMap.toMatrix ((b₀).baseChange R) ((b₀).baseChange R) g.toLinearMap := rfl

private def spinActionOnMatrices : SpinFunctor.Spin q₀ R b₀ →* orthogonalMatrices I R :=
  ((linearEquivMatrix ((b₀).baseChange R)).comp (SpinFunctor.vectorAction q₀ R b₀)).codRestrict
    (orthogonalMatrices I R) fun a => by
      let b := (b₀).baseChange R
      intro v
      obtain ⟨x, rfl⟩ := b.equivFun.surjective v
      let g := SpinFunctor.vectorAction q₀ R b₀ a
      change OddSpinModels.hyperbolicForm I R ((linearEquivMatrix b g).val *ᵥ b.equivFun x) =
        OddSpinModels.hyperbolicForm I R (b.equivFun x)
      rw [linearEquivMatrix_val, show b.equivFun x = b.repr x from rfl,
        LinearMap.toMatrix_mulVec_repr]
      exact (extended_hyperbolicForm (g x)).symm.trans
        ((SpinFunctor.vectorAction_preserves q₀ R b₀ a x).trans (extended_hyperbolicForm x))

private theorem spinActionOnMatrices_natural (f : R →ₐ[k] S) (a : SpinFunctor.Spin q₀ R b₀) :
    spinActionOnMatrices (SpinFunctor.map q₀ b₀ f a) =
      mapOrthogonal f.toRingHom (spinActionOnMatrices a) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  let b := (b₀).baseChange R
  let c := (b₀).baseChange S
  let g := SpinFunctor.vectorAction q₀ R b₀ a
  let h := SpinFunctor.vectorAction q₀ S b₀ (SpinFunctor.map q₀ b₀ f a)
  change (LinearMap.toMatrix c c h.toLinearMap) i j = f ((LinearMap.toMatrix b b g.toLinearMap) i j)
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  change c.repr (h (c j)) i = f (b.repr (g (b j)) i)
  have he : changeModule f (b j) = c j := changeModule_basis b₀ f j
  rw [← he, ← SpinFunctor.vectorAction_naturality q₀ b₀ f a (b j)]
  exact changeModule_coord b₀ f (g (b j)) i

private def splitSpinGroup (k I : Type u) [Field k] [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)] :
    AffineAlgebraicGroup k := by
  let G := SpinFunctor.spinScheme (OddSpinModels.hyperbolicForm I k) (Pi.basisFun k (I ⊕ I))
  have : LocallyOfFinitePresentation G.X.hom := SpinFunctor.spinScheme_locallyOfFinitePresentation _ _
  have : IsAffineHom G.X.hom := SpinFunctor.spinScheme_affineMorphism _ _
  exact ⟨G, SpinFunctor.spinScheme_affine _ _, inferInstance, inferInstance⟩

private def orthogonalPresentationPointsIso (O : SplitOrthogonalPresentation k I) :
    (groupPointsFunctor k).obj O.group.val ≅ orthogonalMatrixPoints k I := by
  refine NatIso.ofComponents (fun R => (O.points R).toGrpIso) ?_
  intro R S f
  apply GrpCat.ext
  intro a
  apply Subtype.ext
  apply Units.ext
  exact O.naturality f a

private def spinVectorNat : (groupPointsFunctor k).obj (splitSpinGroup k I).val ⟶
    orthogonalMatrixPoints k I where
  app R := GrpCat.ofHom (spinActionOnMatrices.comp (SpinFunctor.schemePoints q₀ b₀ R).toMonoidHom)
  naturality := by
    intro R S f
    apply GrpCat.ext
    intro a
    change spinActionOnMatrices (SpinFunctor.schemePoints q₀ b₀ _ (mapPoints f a)) =
      mapOrthogonal f.hom.toRingHom (spinActionOnMatrices (SpinFunctor.schemePoints q₀ b₀ _ a))
    exact (congrArg spinActionOnMatrices (SpinFunctor.schemePoints_naturality q₀ b₀ f a)).trans
      (spinActionOnMatrices_natural f.hom _)

private def spinVectorMorphism (O : SplitOrthogonalPresentation k I) : (splitSpinGroup k I).val ⟶ O.group.val :=
  (AffineAlgebraicGroup.groupHomEquiv (splitSpinGroup k I) O.group).symm
    (spinVectorNat ≫ (orthogonalPresentationPointsIso O).inv)

private theorem spinVectorMorphism_points (O : SplitOrthogonalPresentation k I) (R : TestAlgebra k)
    (a : Points (splitSpinGroup k I).val.X R) :
    O.points R (((groupPointsFunctor k).map (spinVectorMorphism O)).app R a) =
      spinActionOnMatrices (SpinFunctor.schemePoints q₀ b₀ R a) := by
  let e := orthogonalPresentationPointsIso O
  have h := (AffineAlgebraicGroup.groupHomEquiv (splitSpinGroup k I) O.group).apply_symm_apply
    (spinVectorNat ≫ e.inv)
  change (groupPointsFunctor k).map (spinVectorMorphism O) = spinVectorNat ≫ e.inv at h
  exact (congrArg (fun τ => O.points R (τ.app R a)) h).trans ((O.points R).apply_symm_apply _)

private def splitScalarSubgroup : ClosedSubgroup (splitSpinGroup k I).val :=
  ⟨SpinFunctor.muTwoScheme k, SpinFunctor.scalarSchemeInclusion q₀ b₀,
    SpinFunctor.scalarSchemeInclusion_isClosedImmersion q₀ b₀⟩

private theorem spinVector_kernel (O : SplitOrthogonalPresentation k I) :
    IsSchemeKernel (spinVectorMorphism O) (splitScalarSubgroup (k := k) (I := I)) := by
  let f := (spinVectorMorphism O).hom.hom
  let N := splitScalarSubgroup (k := k) (I := I)
  let j := N.inclusion.hom.hom
  have : IsClosedImmersion j.left := N.isClosedImmersion
  have : Mono j := Over.mono_of_mono_left _
  let Z := (testSpec k).obj (op (CommAlgCat.of k k))
  let z : Z ⟶ O.group.val.X := toUnit Z ≫ η[O.group.val.X]
  have h (R : TestAlgebra k) (a : Points (splitSpinGroup k I).val.X R) :
      (∃ t : Points N.group.X R, t ≫ j = a) ↔ a ≫ f = toBasePoint _ ≫ z := by
    have hz : toBasePoint ((testSpec k).obj (op R)) ≫ z = (1 : Points O.group.val.X R) := by
      rw [show z = toUnit Z ≫ η[O.group.val.X] from rfl, ← Category.assoc]
      rw [Subsingleton.elim (toBasePoint ((testSpec k).obj (op R)) ≫ toUnit Z) (toUnit _)]
      rfl
    rw [hz]
    let s : Points (splitSpinGroup k I).val.X R ≃* SpinFunctor.Spin q₀ R b₀ :=
      SpinFunctor.schemePoints q₀ b₀ R
    have h₁ : a ≫ f = (1 : Points O.group.val.X R) ↔ SpinFunctor.vectorAction q₀ R b₀ (s a) = 1 := by
      have hg : O.points R (a ≫ f) = spinActionOnMatrices (s a) := spinVectorMorphism_points O R a
      let b := (b₀).baseChange R
      let M := linearEquivMatrix b
      have hM : Function.Injective M :=
        (Units.map_injective (LinearMap.toMatrixAlgEquiv b).injective).comp
          (LinearMap.GeneralLinearGroup.generalLinearEquiv R _).symm.injective
      have he := (O.points R).injective.eq_iff (a := a ≫ f) (b := 1)
      rw [map_one, hg] at he
      refine he.symm.trans ?_
      constructor
      · intro h
        apply hM
        rw [map_one]
        exact congrArg Subtype.val h
      · intro h
        apply Subtype.ext
        change M (SpinFunctor.vectorAction q₀ R b₀ (s a)) = 1
        rw [h, map_one]
    rw [h₁]
    let e := SpinFunctor.regularKernel q₀ R b₀ (Or.inl hyperbolicForm_polar_ker)
    let μ₂ := SpinFunctor.muTwoSchemePoints k R
    constructor
    · rintro ⟨t, rfl⟩
      exact (congrArg (SpinFunctor.vectorAction q₀ R b₀)
        (SpinFunctor.scalarSchemeInclusion_points q₀ b₀ t)).trans
        (SpinFunctor.scalarEmbedding_trivial_action q₀ R b₀ (μ₂ t))
    · intro ha
      let v : (SpinFunctor.vectorAction q₀ R b₀).ker := ⟨s a, ha⟩
      refine ⟨μ₂.symm (e.symm v), s.injective ?_⟩
      change SpinFunctor.schemePoints q₀ b₀ R
        (μ₂.symm (e.symm v) ≫ (SpinFunctor.scalarSchemeInclusion q₀ b₀).hom.hom) = s a
      exact (SpinFunctor.scalarSchemeInclusion_points q₀ b₀ _).trans
        ((congrArg (SpinFunctor.scalarEmbedding q₀ R b₀) (μ₂.apply_symm_apply (e.symm v))).trans
        (congrArg Subtype.val (e.apply_symm_apply v)))
  have hpb := isPullback_of_affine_fibres j f z h
  have hw : j ≫ f = toUnit N.group.X ≫ η[O.group.val.X] := by
    have hh := hpb.w
    change j ≫ f = toBasePoint N.group.X ≫ (toUnit Z ≫ η[O.group.val.X]) at hh
    rw [← Category.assoc] at hh
    exact hh.trans (congrArg (· ≫ η[O.group.val.X]) (Subsingleton.elim _ _))
  refine IsPullback.mk' hw (fun _ _ _ ha _ => (cancel_mono j).mp ha) ?_
  intro T a b hab
  have hc : a ≫ f = toBasePoint T ≫ z := by
    rw [hab]
    change b ≫ η[O.group.val.X] = toBasePoint T ≫ (toUnit Z ≫ η[O.group.val.X])
    rw [← Category.assoc, Subsingleton.elim b (toBasePoint T ≫ toUnit Z)]
  exact ⟨hpb.lift a (toBasePoint T) hc, hpb.lift_fst _ _ _, Subsingleton.elim _ _⟩

private theorem scalarSubgroup_finite : IsFinite (splitScalarSubgroup (k := k) (I := I)).group.X.hom := by
  change IsFinite (muTwoUnderlying k).hom
  change IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap k (SpinSpecification.muTwoCoordinateRing k))))
  rw [IsFinite.SpecMap_iff]
  change (algebraMap k (SpinSpecification.muTwoCoordinateRing k)).Finite
  rw [RingHom.finite_algebraMap]
  have hp : (SpinSpecification.muTwoPolynomial k).Monic := by
    simpa [SpinSpecification.muTwoPolynomial] using Polynomial.monic_X_pow_sub_C (1 : k)
      (by decide : 2 ≠ 0)
  exact Module.Finite.of_basis (AdjoinRoot.powerBasis' hp).basis

set_option maxHeartbeats 650000 in
theorem splitSpinImage :
    SplitSpinImage.{u} := by
  intro k I _ _ _ _
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  let q := OddSpinModels.hyperbolicForm I k
  let bₖ := Pi.basisFun k (I ⊕ I)
  obtain ⟨O⟩ := splitOrthogonalModel k I
  let G := splitSpinGroup k I
  let N := splitScalarSubgroup (k := k) (I := I)
  let f := spinVectorMorphism O
  obtain ⟨H, p, j, hF, _, _⟩ := schemeImageFactorization G O.group f
  have hKernel : IsSchemeKernel p N := by
    have h := spinVector_kernel O
    have : IsClosedImmersion j.hom.hom.left := hF.2.2.2.2.2
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    exact schemeKernel_of_comp_mono p j (hF.1.symm ▸ h)
  have : IsFinite N.group.X.hom := scalarSubgroup_finite
  have : Flat p.hom.hom.left := hF.2.1
  have : Surjective p.hom.hom.left := hF.2.2.1
  have : LocallyOfFinitePresentation p.hom.hom.left := hF.2.2.2.1
  have : IsAffineHom p.hom.hom.left := hF.2.2.2.2.1
  refine ⟨⟨O, G, spinUnitPoints q bₖ, spinUnitPoints_represents q bₖ,
    H, p, j, hF.2.2.2.2.2, finite_of_finite_kernel p hKernel, inferInstance, inferInstance,
    N, hKernel, rfl, SpinFunctor.muTwoSchemePoints k, ?_, ?_, ?_⟩⟩
  · intro R a
    exact congrArg (fun a : SpinFunctor.Spin q R bₖ => a.val.val)
      (SpinFunctor.scalarSchemeInclusion_points q bₖ a)
  · intro R a b
    let E := spinUnitPoints q bₖ R
    show (a ≫ N.inclusion.hom.hom) * b = b * (a ≫ N.inclusion.hom.hom)
    apply ((spinUnitPoints_represents q bₖ).1 R).1
    have hs := congrArg (fun a : SpinFunctor.Spin q R bₖ => a.val.val)
      (SpinFunctor.scalarSchemeInclusion_points q bₖ a)
    change (E (a ≫ N.inclusion.hom.hom)).val =
      algebraMap R _ (SpinFunctor.muTwoSchemePoints k R a).val.val at hs
    calc
      E ((a ≫ N.inclusion.hom.hom) * b) = E (a ≫ N.inclusion.hom.hom) * E b := map_mul _ _ _
      _ = E b * E (a ≫ N.inclusion.hom.hom) := Units.ext <| by
        simpa only [Units.val_mul, hs] using Algebra.commutes ((SpinFunctor.muTwoSchemePoints k R a).val.val)
          (E b).val
      _ = E (b * (a ≫ N.inclusion.hom.hom)) := (map_mul _ _ _).symm
  · intro R a
    let x := SpinFunctor.schemePoints q bₖ R a
    refine ⟨SpinFunctor.vectorAction q R bₖ x, SpinFunctor.vectorAction_characterization q R bₖ x, ?_⟩
    rw [hF.1]
    exact (congrArg (fun v : orthogonalMatrices I R => v.val.val) (spinVectorMorphism_points O R a)).symm

end

end SplitSpinImage

theorem vectorDiagramSwitch :
    VectorDiagramSwitch.{u} := by
  constructor
  · intro I R _ _ _ i
    let σ : Equiv.Perm (I ⊕ I) := Equiv.swap (Sum.inl i) (Sum.inr i)
    let s := σ.permMatrix R
    have hs : s * s = 1 := by
      rw [show s = σ.permMatrix R from rfl, ← Matrix.permMatrix_mul, Equiv.swap_mul_self,
        Matrix.permMatrix_one]
    let g : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ := ⟨s, s, hs, hs⟩
    have hVec (x : I ⊕ I → R) : s *ᵥ x = x ∘ σ := Matrix.permMatrix_mulVec σ
    refine ⟨g, Units.ext hs, hVec, ?_, ?_⟩
    · intro x
      change OddSpinModels.hyperbolicForm I R (s *ᵥ x) = _
      rw [hVec, hyperbolicForm_apply, hyperbolicForm_apply]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [σ, mul_comm]
      · simp [σ, Equiv.swap_apply_def, hj]
    · intro t
      let d := Specs.SymplecticMatrixStructure.hyperbolicDiagonal t
      change s * d * s = _
      apply Matrix.mulVec_injective
      funext x j
      rw [← mulVec_mulVec, ← mulVec_mulVec, hVec, hVec]
      rcases j with j | j <;> by_cases hj : j = i <;>
        simp [d, Specs.SymplecticMatrixStructure.hyperbolicDiagonal, Matrix.mulVec_diagonal,
          σ, Equiv.swap_apply_def, hj]
  · intro I _ i j l
    refine ⟨?_, ?_⟩
    · intro hij hil
      funext a
      by_cases ha : a = i
      · subst a
        simp [invertCoordinate, coordinateVector, hij, hil]
      · simp [invertCoordinate, ha]
    · intro hj
      constructor <;> funext a <;> by_cases ha : a = i
      · subst a
        simp [invertCoordinate, coordinateVector, hj.symm]
      · simp [invertCoordinate, coordinateVector, ha]
      · subst a
        simp [invertCoordinate, coordinateVector, hj.symm]
      · simp [invertCoordinate, coordinateVector, ha]

section SpinChartFibers

open _root_.LinearAlgebraicGroups.Albert.SplitSpinSpecification
open _root_.LinearAlgebraicGroups.Albert.SplitSpin (cliffordChart orthogonalChart)
open private action_matrix_unique factor_topLeft factor_map map_alternating chartParameters_ext
  from LinearAlgebraicGroups.Albert.SplitSpin
open Polynomial

set_option maxHeartbeats 400000 in
theorem spinChartFibers :
    SpinChartFibers.{u} := by
  intro m hm R _ _ M hM hdet
  obtain ⟨e, hAct, _, _⟩ := cliffordChart.{u} m hm
  let A := M.toBlocks₁₁
  obtain ⟨⟨P, Q⟩, ⟨hP, hQ, hFac⟩, hUnique⟩ := (orthogonalChart m R M hdet).mp hM
  let Root := {u' : Rˣ // (u' : R) ^ 2 * A.det = 1}
  let parameters (r : Root) : ChartParameters m R := ⟨P, Q, A, r.val, hP, hQ, r.property⟩
  let lift (r : Root) : SpinVectorFiber m R M :=
    ⟨(e R (parameters r)).val, (e R (parameters r)).property.1, hFac.symm ▸ hAct R (parameters r)⟩
  have hLift : Function.Bijective lift := by
    constructor
    · intro r s h
      apply Subtype.ext
      have hv := congrArg (fun a : SpinVectorFiber m R M => a.val) h
      have hw : e R (parameters r) = e R (parameters s) := Subtype.ext hv
      exact congrArg ChartParameters.u ((e R).injective hw)
    · intro a
      let a' : SpinChart m R := ⟨a.val, a.property.1, M, a.property.2, hdet⟩
      obtain ⟨w, hw⟩ := (e R).surjective a'
      have hW : lower w.P * middle w.A * upper w.Q = M :=
        action_matrix_unique ((congrArg Subtype.val hw) ▸ hAct R w) a.property.2
      have hA : w.A = A := by simpa only [factor_topLeft] using congrArg toBlocks₁₁ hW
      have hW' : M = lower w.P * middle A * upper w.Q := by
        rw [← hA]
        exact hW.symm
      have hpq : (w.P, w.Q) = (P, Q) := hUnique _ ⟨w.alternatingP, w.alternatingQ, hW'⟩
      let r : Root := ⟨w.u, hA ▸ w.normOne⟩
      refine ⟨r, Subtype.ext ?_⟩
      have hpar : parameters r = w :=
        chartParameters_ext (congrArg Prod.fst hpq).symm (congrArg Prod.snd hpq).symm hA.symm rfl
      change (e R (parameters r)).val = a.val
      rw [hpar, hw]
  refine ⟨⟨Equiv.ofBijective lift hLift⟩, ?_⟩
  by_cases hR : Nontrivial R
  swap
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, ?_⟩
    have h : M.map (algebraMap R R) = M := by ext i j; simp [Matrix.map_apply]
    rw [h]
    exact ⟨lift ⟨1, Subsingleton.elim _ _⟩⟩
  let _ := hR
  obtain ⟨d, hd⟩ := hdet
  let p : R[X] := X ^ 2 - C (↑d⁻¹ : R)
  let T := AdjoinRoot p
  let f : R →+* T := algebraMap R T
  have hp : p.Monic := monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
  let pb := (AdjoinRoot.powerBasis' hp).basis
  have : Module.Free R T := Module.Free.of_basis pb
  have : Module.Finite R T := Module.Finite.of_basis pb
  have : Nontrivial T := (AdjoinRoot.nontrivial_iff_of_monic hp).mpr (by
    change 0 < (X ^ 2 - C (↑d⁻¹ : R) : R[X]).degree
    rw [degree_X_pow_sub_C (by decide : 0 < 2)]
    decide)
  let t : T := AdjoinRoot.root p
  have ht : t ^ 2 = f (↑d⁻¹ : R) := by
    have h := AdjoinRoot.eval₂_root p
    change (X ^ 2 - C (↑d⁻¹ : R)).eval₂ (AdjoinRoot.of p) t = 0 at h
    rwa [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] at h
  have hdetMap : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  have hdA : (d : R) = A.det := hd
  have hMap : t ^ 2 * (A.map f).det = 1 := by
    rw [ht, hdetMap, ← hdA, ← map_mul, Units.inv_mul, map_one]
  have hUnit : t * (t * (A.map f).det) = 1 := by rwa [← mul_assoc, ← pow_two]
  let r : Tˣ := ⟨t, t * (A.map f).det, hUnit, (mul_comm _ _).trans hUnit⟩
  let w : ChartParameters m T :=
    ⟨P.map f, Q.map f, A.map f, r, map_alternating f P hP, map_alternating f Q hQ, hMap⟩
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, ‹Module.Free R T›,
    ‹Module.Finite R T›, inferInstance, inferInstance, ?_⟩
  refine ⟨(e T w).val, (e T w).property.1, ?_⟩
  have hMapped : M.map f = lower (P.map f) * middle (A.map f) * upper (Q.map f) :=
    (congrArg (fun N => N.map f) hFac).trans (factor_map f P Q A ⟨d, hdA⟩)
  exact hMapped.symm ▸ hAct T w

end SpinChartFibers

section SpinIntegralComparison

open CliffordAlgebra
open _root_.LinearAlgebraicGroups.Albert
open SplitSpinSpecification (integralForm hyperbolicBasis PairIndex ExtendedModule HasActionMatrix vectorMatrix)
open SpinSpecification (ScalarClifford IsVectorAction spinUnits)

noncomputable section

private theorem clifford_isometry_reverse {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {p : QuadraticForm R M} {q : QuadraticForm R N} (i : p.IsometryEquiv q)
    (a : CliffordAlgebra p) :
    CliffordAlgebra.equivOfIsometry i (reverse a) =
      reverse (CliffordAlgebra.equivOfIsometry i a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι x =>
    change CliffordAlgebra.map i.toIsometry (reverse (ι p x)) =
      reverse (CliffordAlgebra.map i.toIsometry (ι p x))
    simp
  | mul a b ha hb => simp only [reverse.map_mul, map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem clifford_isometry_even {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {p : QuadraticForm R M} {q : QuadraticForm R N} (i : p.IsometryEquiv q) {a : CliffordAlgebra p}
    (ha : a ∈ evenOdd p 0) : CliffordAlgebra.equivOfIsometry i a ∈ evenOdd q 0 := by
  induction a, ha using even_induction with
  | algebraMap r =>
    rw [AlgEquiv.commutes]
    exact (even q).algebraMap_mem r
  | add a b ha hb ha' hb' =>
    rw [map_add]
    exact (evenOdd q 0).add_mem ha' hb'
  | ι_mul_ι_mul x y a ha ha' =>
    change CliffordAlgebra.map i.toIsometry (ι p x * ι p y * a) ∈ evenOdd q 0
    simp only [map_mul, map_apply_ι]
    exact (even q).mul_mem (ι_mul_ι_mem_evenOdd_zero _ _ _) ha'

open private cliffordEquiv_even cliffordEquiv_vector from LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from LinearAlgebraicGroups.Albert.CliffordModel

section
variable (k I : Type u) [Field k] [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]
variable (m : ℕ) (d : Fin m ≃ I) (R : Type u) [CommRing R] [Algebra k R]
local notation "qZ" => integralForm m
local notation "qk" => OddSpinModels.hyperbolicForm I k
local notation "bZ" => hyperbolicBasis ℤ m
local notation "bk" => Pi.basisFun k (I ⊕ I)

private def integralVectorCoordinates :
    ExtendedModule m R ≃ₗ[R] (R ⊗[k] (I ⊕ I → k)) :=
  ((((bZ).baseChange R).equivFun.trans
    (LinearEquiv.funCongrLeft R R ((d.sumCongr d).symm.trans toLex))).trans
      ((bk).baseChange R).equivFun.symm)

omit [DecidableEq I] [LinearOrder (I ⊕ I)] in
private theorem integralVectorCoordinates_repr (x : ExtendedModule m R) (i : I ⊕ I) :
    ((bk).baseChange R).equivFun (integralVectorCoordinates k I m d R x) i =
      ((bZ).baseChange R).equivFun x (toLex ((d.sumCongr d).symm i)) := by
  change ((bk).baseChange R).equivFun
      (((bk).baseChange R).equivFun.symm
        (fun j => (Module.Basis.baseChange R (bZ)).equivFun x (toLex ((d.sumCongr d).symm j)))) i = _
  rw [LinearEquiv.apply_symm_apply]

private def integralFormIsometry :
    (CliffordSpecification.coefficientForm R qZ bZ).IsometryEquiv
      (CliffordSpecification.coefficientForm R qk bk) where
  __ := integralVectorCoordinates k I m d R
  map_app' x := by
    change CliffordSpecification.coefficientForm R qk bk (integralVectorCoordinates k I m d R x) =
      CliffordSpecification.coefficientForm R qZ bZ x
    rw [extended_hyperbolicForm, SplitSpin.vectorCoordinates m R]
    simp only [hyperbolicForm_apply, integralVectorCoordinates_repr, Equiv.sumCongr_symm,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      SplitSpinSpecification.hyperbolicNorm, dotProduct]
    exact d.symm.sum_comp (fun i => (Module.Basis.baseChange R (bZ)).equivFun x (Sum.inl i) *
      ((bZ).baseChange R).equivFun x (Sum.inr i))

private def integralCliffordCoordinates : ScalarClifford qZ R ≃ₐ[R] ScalarClifford qk R :=
  (CliffordModel.baseChangeEquiv R qZ bZ).trans
    ((CliffordAlgebra.equivOfIsometry (integralFormIsometry k I m d R)).trans
      (CliffordModel.baseChangeEquiv R qk bk).symm)

open SpinSpecification (vectors reversion evenPart)

private theorem integralCliffordCoordinates_vector (x : ExtendedModule m R) :
    integralCliffordCoordinates k I m d R (vectors qZ R x) =
      vectors qk R (integralVectorCoordinates k I m d R x) := by
  apply (CliffordModel.baseChangeEquiv R qk bk).injective
  change (CliffordModel.baseChangeEquiv R qk bk) ((CliffordModel.baseChangeEquiv R qk bk).symm
    (equivOfIsometry (integralFormIsometry k I m d R) ((CliffordModel.baseChangeEquiv R qZ bZ) _))) =
    (CliffordModel.baseChangeEquiv R qk bk) _
  rw [AlgEquiv.apply_symm_apply]
  rw [show (CliffordModel.baseChangeEquiv R qZ bZ) (vectors qZ R x) = ι _ x from
    cliffordEquiv_vector qZ R bZ x]
  rw [show (CliffordModel.baseChangeEquiv R qk bk) (vectors qk R
    (integralVectorCoordinates k I m d R x)) = ι _ (integralVectorCoordinates k I m d R x) from
    cliffordEquiv_vector qk R bk _]
  exact map_apply_ι _ _

private theorem integralCliffordCoordinates_even (x : ScalarClifford qZ R) :
    integralCliffordCoordinates k I m d R x ∈ evenPart qk R ↔ x ∈ evenPart qZ R := by
  let e := CliffordModel.baseChangeEquiv R qk bk
  let mCl := CliffordAlgebra.equivOfIsometry (integralFormIsometry k I m d R)
  let c := CliffordModel.baseChangeEquiv R qZ bZ
  rw [← cliffordEquiv_even qk R bk, ← cliffordEquiv_even qZ R bZ]
  change e (e.symm (mCl (c x))) ∈ _ ↔ c x ∈ _
  rw [e.apply_symm_apply]
  refine ⟨fun h => ?_, clifford_isometry_even _⟩
  have hh := clifford_isometry_even (integralFormIsometry k I m d R).symm h
  change equivOfIsometry (integralFormIsometry k I m d R).symm (mCl (c x)) ∈ _ at hh
  rw [← equivOfIsometry_symm, AlgEquiv.symm_apply_apply] at hh
  exact hh

private theorem integralCliffordCoordinates_reverse (x : ScalarClifford qZ R) :
    integralCliffordCoordinates k I m d R (reversion qZ R x) =
      reversion qk R (integralCliffordCoordinates k I m d R x) := by
  let e := CliffordModel.baseChangeEquiv R qk bk
  let mCl := CliffordAlgebra.equivOfIsometry (integralFormIsometry k I m d R)
  let c := CliffordModel.baseChangeEquiv R qZ bZ
  apply e.injective
  change e (e.symm (mCl (c (reversion qZ R x)))) = e (reversion qk R (e.symm (mCl (c x))))
  rw [e.apply_symm_apply]
  rw [show c (reversion qZ R x) = reverse (c x) from baseChangeEquiv_reverse R qZ bZ x]
  rw [clifford_isometry_reverse]
  rw [show e (reversion qk R (e.symm (mCl (c x)))) = reverse (e (e.symm (mCl (c x)))) from
    baseChangeEquiv_reverse R qk bk _]
  rw [e.apply_symm_apply]

local notation "eC" => (integralCliffordCoordinates k I m d R)
local notation "eV" => (integralVectorCoordinates k I m d R)

private theorem integralCliffordCoordinates_conjugate (a : (ScalarClifford qZ R)ˣ)
    (x : ScalarClifford qZ R) :
    eC (SpinSpecification.conjugate qZ R a x) =
      SpinSpecification.conjugate qk R (Units.map (eC).toMonoidHom a) (eC x) := by
  simp only [SpinSpecification.conjugate, map_mul, ← map_inv]
  rfl

private theorem integralSpinUnits (a : (ScalarClifford qZ R)ˣ) :
    Units.map (eC).toMonoidHom a ∈ spinUnits qk R ↔ a ∈ spinUnits qZ R := by
  have hn : reversion qk R (eC a.val) * eC a.val = 1 ↔ reversion qZ R a.val * a.val = 1 := by
    rw [← integralCliffordCoordinates_reverse k I m d R, ← map_mul, ← map_one eC, (eC).injective.eq_iff]
  have he : ∀ x, eC (vectors qZ R x) = vectors qk R (eV x) :=
    integralCliffordCoordinates_vector k I m d R
  have hRange (c : (ScalarClifford qZ R)ˣ) :
      Set.MapsTo (SpinSpecification.conjugate qk R (Units.map (eC).toMonoidHom c))
        (LinearMap.range (vectors qk R)) (LinearMap.range (vectors qk R)) ↔
      Set.MapsTo (SpinSpecification.conjugate qZ R c)
        (LinearMap.range (vectors qZ R)) (LinearMap.range (vectors qZ R)) := by
    constructor
    · rintro h _ ⟨x, rfl⟩
      obtain ⟨w, hw⟩ := h (LinearMap.mem_range_self _ (eV x))
      refine ⟨(eV).symm w, (eC).injective ?_⟩
      rw [he, LinearEquiv.apply_symm_apply, hw, integralCliffordCoordinates_conjugate, he]
    · rintro h _ ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (eV).surjective y
      obtain ⟨z, hz⟩ := h (LinearMap.mem_range_self _ x)
      refine ⟨eV z, ?_⟩
      rw [← he, hz, integralCliffordCoordinates_conjugate, he]
  have hv : (Units.map (eC).toMonoidHom a).val = eC a.val := rfl
  simp only [spinUnits, Set.mem_ofPred_eq, hv]
  rw [integralCliffordCoordinates_even, hn, hRange a, ← map_inv, hRange a⁻¹]

private theorem integralSpinAction (a : (ScalarClifford qZ R)ˣ)
    (g : ExtendedModule m R ≃ₗ[R] ExtendedModule m R) :
    IsVectorAction qk R (Units.map (eC).toMonoidHom a) ((eV).symm.trans (g.trans eV)) ↔
      IsVectorAction qZ R a g := by
  have he : ∀ x, eC (vectors qZ R x) = vectors qk R (eV x) :=
    integralCliffordCoordinates_vector k I m d R
  constructor
  · intro h x
    apply (eC).injective
    change eC (vectors qZ R (g x)) = eC (SpinSpecification.conjugate qZ R a (vectors qZ R x))
    rw [he, integralCliffordCoordinates_conjugate, he]
    simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using h (eV x)
  · intro h x
    obtain ⟨y, rfl⟩ := (eV).surjective x
    have h' := congrArg (fun z : ScalarClifford qZ R => eC z) (h y)
    rw [he, integralCliffordCoordinates_conjugate, he] at h'
    simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using h'

local notation "BZ" => (Module.Basis.baseChange R (bZ))
local notation "Bk" => (Module.Basis.baseChange R (bk))

omit [LinearOrder (I ⊕ I)] in
private theorem integralSpinAction_matrix
    (g : ExtendedModule m R ≃ₗ[R] ExtendedModule m R) :
    LinearMap.toMatrix Bk Bk ((eV).symm.trans (g.trans eV)).toLinearMap =
      Matrix.reindex (d.sumCongr d) (d.sumCongr d) (vectorMatrix m g) := by
  let d' := d.sumCongr d
  have hb (j : I ⊕ I) : eV (BZ (toLex (d'.symm j))) = Bk j := by
    apply ((Bk).equivFun).injective
    funext i
    rw [integralVectorCoordinates_repr, Module.Basis.equivFun_self, Module.Basis.equivFun_self]
    change (if d'.symm j = d'.symm i then (1 : R) else 0) = if j = i then 1 else 0
    simp only [d'.symm.injective.eq_iff]
  apply Matrix.ext
  intro i j
  change LinearMap.toMatrix Bk Bk ((eV).symm.trans (g.trans eV)).toLinearMap i j =
    LinearMap.toMatrix BZ BZ g.toLinearMap (toLex (d'.symm i)) (toLex (d'.symm j))
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp only [← Module.Basis.equivFun_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [← hb j, LinearEquiv.symm_apply_apply, integralVectorCoordinates_repr]

private theorem integralSpinMatrix (a : (ScalarClifford qZ R)ˣ)
    (M : Matrix (PairIndex m) (PairIndex m) R) :
    HasActionMatrix m a M ↔
    ∃ g : (R ⊗[k] (I ⊕ I → k)) ≃ₗ[R] (R ⊗[k] (I ⊕ I → k)),
      IsVectorAction qk R (Units.map (eC).toMonoidHom a) g ∧
        LinearMap.toMatrix Bk Bk g.toLinearMap = Matrix.reindex (d.sumCongr d) (d.sumCongr d) M := by
  constructor
  · rintro ⟨g, hg, hm⟩
    exact ⟨_, (integralSpinAction k I m d R a g).mpr hg,
      (integralSpinAction_matrix k I m d R g).trans (congrArg _ hm)⟩
  · rintro ⟨g, hg, hm⟩
    let h := (eV).trans (g.trans (eV).symm)
    have hh : (eV).symm.trans (h.trans eV) = g := by
      ext x
      simp [h]
    refine ⟨h, (integralSpinAction k I m d R a h).mp (hh.symm ▸ hg), ?_⟩
    apply (Matrix.reindex (d.sumCongr d) (d.sumCongr d)).injective
    rw [← integralSpinAction_matrix k I m d R h, hh, hm]


end

theorem splitSpinIntegralComparison :
    SplitSpinIntegralComparison.{u} := by
  intro k I _ _ _ _ m d R _ _ q b
  refine ⟨integralCliffordCoordinates k I m d R, fun a => ⟨integralSpinUnits k I m d R a, ?_⟩⟩
  exact integralSpinMatrix k I m d R a

open AlgebraicGeometry CategoryTheory Opposite

private theorem factorsClosed_of_injective_testMap {k : Type u} [Field k]
    {R S : TestAlgebra k} (f : R ⟶ S) (hf : Function.Injective f.hom)
    {X Y : SchemeOver k} (j : X ⟶ Y) (hj : IsClosedImmersion j.left)
    (a : Points Y R) (b : Points X S) (h : mapPoints f a = b ≫ j) :
    ∃ c : Points X R, c ≫ j = a := by
  let t := ((testSpec k).map f.op).left
  have hcomp : t ≫ a.left = b.left ≫ j.left := congrArg Over.Hom.left h
  have hApp : Function.Injective t.appTop := by
    intro x y hxy
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom).injective
    apply hf
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
      CommRingCat.ofHom f.hom.toRingHom) x =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom f.hom.toRingHom) y
    rw [← Scheme.ΓSpecIso_naturality]
    exact congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom hxy
  let _ : IsAffine ((testSpec k).obj (op R)).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  let _ : QuasiCompact t :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom f.hom.toRingHom)))
  have hz : t.ker = ⊥ := Scheme.IdealSheafData.ext_of_isAffine (by
    rw [t.ker_apply ⟨⊤, isAffineOpen_top _⟩]
    exact (RingHom.injective_iff_ker_eq_bot t.appTop.hom).mp hApp)
  have hle := b.left.le_ker_comp j.left
  rw [← hcomp, Scheme.Hom.ker_comp, hz, Scheme.IdealSheafData.map_bot] at hle
  let c := IsClosedImmersion.lift j.left a.left hle
  have hc : c ≫ j.left = a.left := IsClosedImmersion.lift_fac .. 
  refine ⟨Over.homMk c ?_, Over.OverMorphism.ext hc⟩
  rw [← Over.w j, ← Category.assoc, hc, Over.w a]

open private vectors_injective from LinearAlgebraicGroups.Albert.SpinFunctor

private theorem spinVectorImage_has_chart {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
    (hFibers : SpinChartFibers.{u}) (hRank : 4 ≤ Fintype.card I) (P : SplitSpinVectorImage k I)
    (R : TestAlgebra k) (a : Points P.orthogonal.group.val.X R)
    (hdet : IsUnit (P.orthogonal.points R a).val.val.toBlocks₁₁.det) :
    ∃ c : Points P.image.val.X R, c ≫ P.inclusion.hom.hom = a := by
  let m := Fintype.card I
  let d : Fin m ≃ I := (Fintype.equivFin I).symm
  let e := d.sumCongr d
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  let A := (P.orthogonal.points R a).val.val
  let M := A.submatrix e e
  have hMdet : IsUnit M.toBlocks₁₁.det := by
    change IsUnit ((A.toBlocks₁₁).submatrix d d).det
    rwa [Matrix.det_submatrix_equiv_self]
  have hQ (v : I ⊕ I → R) : SplitSpinSpecification.hyperbolicNorm (v ∘ e) =
      OddSpinModels.hyperbolicForm I R v := by
    simpa only [SplitSpinSpecification.hyperbolicNorm, dotProduct, hyperbolicForm_apply,
      Function.comp_apply, e, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr] using
      d.sum_comp (fun i => v (Sum.inl i) * v (Sum.inr i))
  have hM : SplitSpinSpecification.PreservesNorm M := by
    intro x
    rw [show M *ᵥ x = (A *ᵥ (x ∘ e.symm)) ∘ e from Matrix.submatrix_mulVec_equiv A x e e, hQ]
    have hx := (P.orthogonal.points R a).property (x ∘ e.symm)
    change OddSpinModels.hyperbolicForm I R (A *ᵥ (x ∘ e.symm)) =
      OddSpinModels.hyperbolicForm I R (x ∘ e.symm) at hx
    rw [hx, ← hQ]
    congr
    funext y
    simp
  have hm : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hRank
  obtain ⟨_, T, hT, hRT, hZT, hZRT, _, _, hff, _, ⟨p⟩⟩ := hFibers m hm R M hM hMdet
  let _ : CommRing T := hT
  let _ : Algebra R T := hRT
  have hInt : hZT = @Ring.toIntAlgebra T hT.toRing := Subsingleton.elim _ _
  subst hZT
  let _ : Module.FaithfullyFlat R T := hff
  let _ : Algebra k T := ((algebraMap R T).comp (algebraMap k R)).toAlgebra
  let _ : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let S : TestAlgebra k := CommAlgCat.of k T
  let f : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R T)
  let q := OddSpinModels.hyperbolicForm I k
  let bk := Pi.basisFun k (I ⊕ I)
  let z := Units.map (integralCliffordCoordinates k I m d T).toMonoidHom p.val
  have hz : z ∈ spinUnits q S :=
    (integralSpinUnits k I m d T p.val).mpr p.property.1
  rw [← (P.spinRepresents.1 S).2] at hz
  obtain ⟨a', ha'⟩ := hz
  obtain ⟨g, hg, hG⟩ := (integralSpinMatrix k I m d T p.val _).mp p.property.2
  have hg' : IsVectorAction q S (P.spinPoints S a') g := ha'.symm ▸ hg
  obtain ⟨w, hw, hW⟩ := P.vector S a'
  have hgw : g = w := by
    ext x
    apply vectors_injective q S bk
    exact (hg' x).trans (hw x).symm
  have hReindex : Matrix.reindex e e (M.map (algebraMap R T)) = A.map f.hom := by
    apply Matrix.ext
    intro i j
    change (algebraMap R T) (A (e (e.symm i)) (e (e.symm j))) = (algebraMap R T) (A i j)
    rw [e.apply_symm_apply, e.apply_symm_apply]
  refine factorsClosed_of_injective_testMap f (FaithfulSMul.algebraMap_injective R T)
    P.inclusion.hom.hom P.closed a (a' ≫ P.projection.hom.hom) ?_
  apply (P.orthogonal.points S).injective
  apply Subtype.ext
  apply Units.ext
  calc
    (P.orthogonal.points S (mapPoints f a)).val.val = A.map f.hom := P.orthogonal.naturality f a
    _ = Matrix.reindex e e (M.map (algebraMap R T)) := hReindex.symm
    _ = LinearMap.toMatrix (bk.baseChange S) (bk.baseChange S) w.toLinearMap := hgw ▸ hG.symm
    _ = _ := hW


theorem splitSpinChartInImage :
    SplitSpinChartInImage.{u} := by
  intro k I _ _ _ hRank P R a hdet
  exact spinVectorImage_has_chart (spinChartFibers)
    hRank P R a hdet


end

end SpinIntegralComparison

open LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup)

section SplitSpinOpenImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

noncomputable section

set_option linter.style.haveILetI false

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]

open private coordinateUnit coordinateUnit_isIso universalPoint universalPoint_comp from
  LinearAlgebraicGroups.Classification.CellHomomorphism

private abbrev orthogonalCoordinateObject (O : SplitOrthogonalPresentation k I) : TestAlgebra k :=
  ((algΓ (CommRingCat.of k)).obj O.group.val.X).unop

private def topLeftDeterminant (O : SplitOrthogonalPresentation k I) : orthogonalCoordinateObject O :=
  letI := O.group.property.1
  (O.points _ (universalPoint O.group.val.X)).val.val.toBlocks₁₁.det

private abbrev orthoOpenRing (O : SplitOrthogonalPresentation k I) :=
  CommAlgCat.of k (Localization.Away (topLeftDeterminant O))

private def orthoOpenInclusion (O : SplitOrthogonalPresentation k I) :
    Points O.group.val.X (orthoOpenRing O) :=
  letI := O.group.property.1
  mapPoints (CommAlgCat.ofHom (IsScalarTower.toAlgHom k (orthogonalCoordinateObject O) (orthoOpenRing O)))
    (universalPoint O.group.val.X)

private theorem orthoOpenInclusion_open (O : SplitOrthogonalPresentation k I) :
    IsOpenImmersion (orthoOpenInclusion O).left := by
  haveI := O.group.property.1
  haveI := coordinateUnit_isIso O.group.val.X
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (orthogonalCoordinateObject O) (orthoOpenRing O))) ≫
    (universalPoint O.group.val.X).left)
  haveI : IsIso (universalPoint O.group.val.X).left :=
    (Over.forget _).map_isIso (inv (coordinateUnit O.group.val.X))
  have hloc : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (orthogonalCoordinateObject O) (orthoOpenRing O)))) :=
    IsOpenImmersion.of_isLocalization (topLeftDeterminant O)
  have hopen : IsOpenImmersion (universalPoint O.group.val.X).left :=
    IsOpenImmersion.of_isIso (universalPoint O.group.val.X).left
  exact @IsOpenImmersion.comp _ _ _ _ _ hloc hopen

private theorem ortho_topLeftDet_map (O : SplitOrthogonalPresentation k I)
    {R S : TestAlgebra k} (a : R ⟶ S) (p : Points O.group.val.X R) :
    (O.points S (mapPoints a p)).val.val.toBlocks₁₁.det =
      a.hom (O.points R p).val.val.toBlocks₁₁.det := by
  have hn : (O.points S (mapPoints a p)).val.val = (O.points R p).val.val.map a.hom :=
    O.naturality a p
  rw [hn]
  exact (RingHom.map_det a.hom.toRingHom _).symm

private theorem orthoOpenInclusion_det (O : SplitOrthogonalPresentation k I) :
    IsUnit (O.points _ (orthoOpenInclusion O)).val.val.toBlocks₁₁.det := by
  unfold orthoOpenInclusion
  rw [ortho_topLeftDet_map]
  exact IsLocalization.Away.algebraMap_isUnit (topLeftDeterminant O)

set_option maxHeartbeats 650000 in
private theorem orthoOpen_factors (O : SplitOrthogonalPresentation k I)
    (R : TestAlgebra k) (a : Points O.group.val.X R)
    (ha : IsUnit (O.points _ a).val.val.toBlocks₁₁.det) :
    ∃ r : Points ((testSpec k).obj (op (orthoOpenRing O))) R, r ≫ orthoOpenInclusion O = a := by
  letI := O.group.property.1
  letI := coordinateUnit_isIso O.group.val.X
  let f := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    (a ≫ coordinateUnit O.group.val.X)
  let g := f.unop
  have hfg : mapPoints g (universalPoint O.group.val.X) = a := by
    change (testSpec k).map f ≫ _ = a
    rw [Functor.FullyFaithful.map_preimage, Category.assoc]
    simp [universalPoint]
  have hg : IsUnit (g.hom (topLeftDeterminant O)) := by
    change IsUnit (g.hom (O.points _ (universalPoint O.group.val.X)).val.val.toBlocks₁₁.det)
    rwa [← ortho_topLeftDet_map O g _, hfg]
  let s : orthoOpenRing O →ₐ[k] R := IsLocalization.Away.liftAlgHom (S := orthoOpenRing O) (topLeftDeterminant O) hg
  refine ⟨(testSpec k).map (CommAlgCat.ofHom s).op, ?_⟩
  have h : (IsScalarTower.toAlgHom k (orthogonalCoordinateObject O) (orthoOpenRing O) |> s.comp) = g.hom := by
    apply AlgHom.ext
    intro x
    change s (algebraMap (orthogonalCoordinateObject O) (orthoOpenRing O) x) = g.hom x
    simp only [s, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  change (testSpec k).map (CommAlgCat.ofHom s).op ≫
    ((testSpec k).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k (orthogonalCoordinateObject O) (orthoOpenRing O))).op ≫
      universalPoint O.group.val.X) = _
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  have hc : CommAlgCat.ofHom (IsScalarTower.toAlgHom k (orthogonalCoordinateObject O) (orthoOpenRing O)) ≫
      CommAlgCat.ofHom s = g := CommAlgCat.hom_ext h
  rw [hc]
  exact hfg

open private rightTranslateProduct isPullback_tensor_structure from LinearAlgebraicGroups.Flag.SmoothOrbit
open Specs.FlagSchemes (toBasePoint)

set_option backward.isDefEq.respectTransparency false in
private theorem open_subgroup_of_identity_neighborhood {G H : GroupScheme k}
    (i : H ⟶ G) [IsClosedImmersion i.hom.hom.left] [LocallyOfFiniteType H.X.hom]
    {U : SchemeOver k} (a : U ⟶ H.X) [IsOpenImmersion (a ≫ i.hom.hom).left]
    (e : Points U (.of k k)) (he : e ≫ a = 1) :
    IsOpenImmersion i.hom.hom.left := by
  let F : SchemeOver k ⥤ Scheme := Over.forget _
  let j := i.hom.hom
  let l := a ≫ j
  let S := U ⊗ H.X
  let f : S ⟶ H.X := lift (fst U H.X ≫ a) (snd U H.X) ≫ μ[H.X]
  let t := f ≫ j
  let p : H.X ⟶ S := lift (toBasePoint H.X ≫ e) (𝟙 H.X)
  have hp : p ≫ f = 𝟙 _ := by
    change p ≫ ((fst U H.X ≫ a) * snd U H.X) = _
    rw [MonObj.comp_mul, ← Category.assoc]
    rw [show p ≫ fst U H.X = toBasePoint H.X ≫ e from lift_fst _ _,
      show p ≫ snd U H.X = 𝟙 _ from lift_snd _ _,
      Category.assoc, he, MonObj.comp_one, one_mul]
  have hf : Function.Surjective f.left := by
    intro x
    refine ⟨p.left x, ?_⟩
    exact congrArg (fun g : H.X ⟶ H.X => g.left x) hp
  let d := rightTranslateProduct (G := G) j
  have ht : t = (l ⊗ₘ 𝟙 H.X) ≫ d.hom ≫ fst G.X H.X := by
    change ((fst U H.X ≫ a) * snd U H.X) ≫ j = _
    rw [MonObj.mul_comp]
    simp [d, rightTranslateProduct, l, Category.assoc, MonObj.comp_mul]
  have hpb : IsPullback (l ⊗ₘ 𝟙 H.X) (fst U H.X) (fst G.X H.X) l := by
    refine IsPullback.mk' (by simp) ?_ ?_
    · intro T z z' h₁ h₂
      apply CartesianMonoidalCategory.hom_ext z z' h₂
      simpa only [Category.assoc, tensorHom_snd, Category.comp_id] using
        congrArg (fun f : T ⟶ G.X ⊗ H.X => f ≫ snd G.X H.X) h₁
    · intro T z x h
      refine ⟨lift x (z ≫ snd G.X H.X), ?_, lift_fst _ _⟩
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst]
        exact h.symm
      · simp
  have : IsOpenImmersion (l ⊗ₘ 𝟙 H.X).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      ((hpb.map F).flip) (show IsOpenImmersion l.left from inferInstance)
  have : IsIso d.hom.left := F.map_isIso d.hom
  have : Flat H.X.hom := inferInstance
  have : LocallyOfFinitePresentation H.X.hom := inferInstance
  have : Flat (fst G.X H.X).left :=
    MorphismProperty.of_isPullback (P := @Flat)
      (isPullback_tensor_structure G.X H.X).flip inferInstance
  have : LocallyOfFinitePresentation (fst G.X H.X).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (isPullback_tensor_structure G.X H.X).flip inferInstance
  have : Flat t.left := by
    rw [ht, Over.comp_left, Over.comp_left]
    infer_instance
  have : LocallyOfFinitePresentation t.left := by
    rw [ht, Over.comp_left, Over.comp_left]
    infer_instance
  have hr : Set.range t.left = Set.range j.left := by
    change Set.range (j.left ∘ f.left) = Set.range j.left
    rw [Set.range_comp, Set.range_eq_univ.mpr hf, Set.image_univ]
  have hopen : IsOpen (Set.range j.left) := hr ▸ t.left.isOpenMap.isOpen_range
  have (x : H.X.left) : IsIso (j.left.stalkMap x) := by
    obtain ⟨z, rfl⟩ := hf x
    have hinj : Function.Injective (t.left.stalkMap z).hom := by
      algebraize [(t.left.stalkMap z).hom]
      have : Module.FaithfullyFlat (G.X.left.presheaf.stalk (t.left z))
          (S.left.presheaf.stalk z) :=
        @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
          (Flat.stalkMap t.left z) (t.left.toLRSHom.prop z)
      exact ‹RingHom.FaithfullyFlat _›.injective
    change Function.Injective ((f.left ≫ j.left).stalkMap z).hom at hinj
    rw [Scheme.Hom.stalkMap_comp] at hinj
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨fun x y h => hinj ?_, j.left.stalkMap_surjective _⟩
    change (f.left.stalkMap z).hom ((j.left.stalkMap (f.left z)).hom x) =
      (f.left.stalkMap z).hom ((j.left.stalkMap (f.left z)).hom y)
    exact congrArg ((f.left.stalkMap z).hom) h
  exact IsOpenImmersion.of_isIso_stalkMap _ ⟨j.left.isClosedEmbedding.isEmbedding, hopen⟩

theorem splitSpinOpenImage : SplitSpinOpenImage.{u} := by
  intro k I _ _ _ hRank P
  let O := P.orthogonal
  let a := orthoOpenInclusion O
  obtain ⟨b, hb⟩ := splitSpinChartInImage k I hRank P _ a (orthoOpenInclusion_det O)
  have : IsClosedImmersion P.inclusion.hom.hom.left := P.closed
  have : LocallyOfFiniteType P.image.val.X.hom := P.image.property.2.1
  have : IsOpenImmersion (b ≫ P.inclusion.hom.hom).left := hb.symm ▸ orthoOpenInclusion_open O
  have hi : IsUnit (O.points (.of k k) 1).val.val.toBlocks₁₁.det := by
    have h : (O.points (.of k k) 1).val.val = 1 := by rw [map_one]; rfl
    rw [h, ← Matrix.fromBlocks_one (l := I) (m := I), toBlocks_fromBlocks₁₁, det_one]
    exact isUnit_one
  obtain ⟨e, he⟩ := orthoOpen_factors O (.of k k) 1 hi
  have : Mono P.inclusion.hom.hom := Over.mono_of_mono_left _
  have hb' : e ≫ b = 1 := by
    apply (cancel_mono P.inclusion.hom.hom).mp
    rw [Category.assoc, hb, he, MonObj.one_comp]
  exact open_subgroup_of_identity_neighborhood P.inclusion b e hb'


open _root_.LinearAlgebraicGroups.Albert
open SplitSpinSpecification (PairIndex Block AlternatingIndex IsAlternating PreservesNorm lower middle upper)
open private alternatingCoordinates alternating_ofCoordinates_map lower_preserves middle_preserves
  upper_preserves factor_blocks factor_det factor_map from LinearAlgebraicGroups.Albert.SplitSpin
open private exists_field_point from LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus

private theorem hyperbolicNorm_reindex {R : Type u} [CommRing R] {m : ℕ}
    (d : Fin m ≃ I) (x : I ⊕ I → R) :
    SplitSpinSpecification.hyperbolicNorm (x ∘ d.sumCongr d) =
      OddSpinModels.hyperbolicForm I R x := by
  simpa only [SplitSpinSpecification.hyperbolicNorm, dotProduct, hyperbolicForm_apply,
    Function.comp_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr] using
    d.sum_comp (fun i => x (Sum.inl i) * x (Sum.inr i))

private theorem preservesNorm_submatrix_iff {R : Type u} [CommRing R] {m : ℕ}
    (d : Fin m ≃ I) (M : Matrix (I ⊕ I) (I ⊕ I) R) :
    PreservesNorm (M.submatrix (d.sumCongr d) (d.sumCongr d)) ↔
      ∀ x, OddSpinModels.hyperbolicForm I R (M *ᵥ x) = OddSpinModels.hyperbolicForm I R x := by
  let e := d.sumCongr d
  constructor
  · intro h x
    have hp := h (x ∘ e)
    change SplitSpinSpecification.hyperbolicNorm ((M.submatrix e e) *ᵥ (x ∘ e)) =
      SplitSpinSpecification.hyperbolicNorm (x ∘ e) at hp
    rw [Matrix.submatrix_mulVec_equiv, show (x ∘ e) ∘ e.symm = x from
      funext fun i => congrArg x (e.apply_symm_apply i)] at hp
    exact (hyperbolicNorm_reindex d _).symm.trans (hp.trans (hyperbolicNorm_reindex d _))
  · intro h x
    change SplitSpinSpecification.hyperbolicNorm ((M.submatrix e e) *ᵥ x) =
      SplitSpinSpecification.hyperbolicNorm x
    rw [Matrix.submatrix_mulVec_equiv, hyperbolicNorm_reindex, h, ← hyperbolicNorm_reindex d]
    exact congrArg SplitSpinSpecification.hyperbolicNorm (funext fun i => congrArg x (e.symm_apply_apply i))

private theorem reindex_preservesNorm {R : Type u} [CommRing R] {m : ℕ}
    (d : Fin m ≃ I) (M : Matrix (PairIndex m) (PairIndex m) R) (hM : PreservesNorm M) :
    ∀ x, OddSpinModels.hyperbolicForm I R ((reindex (d.sumCongr d) (d.sumCongr d) M) *ᵥ x) =
      OddSpinModels.hyperbolicForm I R x := by
  apply (preservesNorm_submatrix_iff d _).mp
  convert hM using 1
  apply Matrix.ext
  intro i j
  let e := d.sumCongr d
  change M (e.symm (e i)) (e.symm (e j)) = M i j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

private theorem reindex_isUnit {R : Type u} [CommRing R] {m : ℕ}
    (d : Fin m ≃ I) (M : Matrix (PairIndex m) (PairIndex m) R) (hM : IsUnit M.det) :
    IsUnit (reindex (d.sumCongr d) (d.sumCongr d) M) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rwa [Matrix.det_reindex_self]

private def pointOfNormMatrix (O : SplitOrthogonalPresentation k I) (R : TestAlgebra k) {m : ℕ}
    (d : Fin m ≃ I) (M : Matrix (PairIndex m) (PairIndex m) R)
    (hM : PreservesNorm M) (hd : IsUnit M.det) : Points O.group.val.X R :=
  (O.points R).symm ⟨(reindex_isUnit d M hd).unit, by
    change ∀ x, OddSpinModels.hyperbolicForm I R (((reindex_isUnit d M hd).unit : Matrix (I ⊕ I) (I ⊕ I) R) *ᵥ x) =
      OddSpinModels.hyperbolicForm I R x
    rw [IsUnit.unit_spec]
    exact reindex_preservesNorm d M hM⟩

private theorem pointOfNormMatrix_value (O : SplitOrthogonalPresentation k I) (R : TestAlgebra k)
    {m : ℕ} (d : Fin m ≃ I) (M : Matrix (PairIndex m) (PairIndex m) R)
    (hM : PreservesNorm M) (hd : IsUnit M.det) :
    (O.points R (pointOfNormMatrix O R d M hM hd)).val.val =
      Matrix.reindex (d.sumCongr d) (d.sumCongr d) M := by
  unfold pointOfNormMatrix
  rw [MulEquiv.apply_symm_apply]
  exact IsUnit.unit_spec _

private abbrev OrthoChartIndex (m : ℕ) := (AlternatingIndex m ⊕ AlternatingIndex m) ⊕ (Fin m × Fin m)

private def orthoGenericMiddle (k : Type u) [Field k] (m : ℕ) :
    Block m (MvPolynomial (OrthoChartIndex m) k) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inr (i, j))

private abbrev OrthoParameterRing (k : Type u) [Field k] (m : ℕ) :=
  Localization.Away (orthoGenericMiddle k m).det

private def orthoParameter (k : Type u) [Field k] {m : ℕ} (i : OrthoChartIndex m) :
    OrthoParameterRing k m :=
  algebraMap (MvPolynomial (OrthoChartIndex m) k) (OrthoParameterRing k m) (MvPolynomial.X i)

private def orthoGenericLower (k : Type u) [Field k] (m : ℕ) :
    {P : Block m (OrthoParameterRing k m) // IsAlternating P} :=
  (alternatingCoordinates m (OrthoParameterRing k m)).symm
    (fun i => orthoParameter k (Sum.inl (Sum.inl i)))

private def orthoGenericUpper (k : Type u) [Field k] (m : ℕ) :
    {Q : Block m (OrthoParameterRing k m) // IsAlternating Q} :=
  (alternatingCoordinates m (OrthoParameterRing k m)).symm
    (fun i => orthoParameter k (Sum.inl (Sum.inr i)))

private def orthoGenericFactor (k : Type u) [Field k] (m : ℕ) :
    Block m (OrthoParameterRing k m) :=
  (orthoGenericMiddle k m).map (algebraMap _ _)

private theorem orthoGenericFactor_det (k : Type u) [Field k] (m : ℕ) :
    IsUnit (orthoGenericFactor k m).det := by
  unfold orthoGenericFactor
  rw [show ((orthoGenericMiddle k m).map (algebraMap _ (OrthoParameterRing k m))).det =
      algebraMap _ _ (orthoGenericMiddle k m).det from (RingHom.map_det _ _).symm]
  exact IsLocalization.Away.algebraMap_isUnit _

private def orthoParameterValues {R : Type u} [CommRing R] {m : ℕ} (P Q A : Block m R) :
    OrthoChartIndex m → R
  | .inl (.inl i) => P i.val.1 i.val.2
  | .inl (.inr i) => Q i.val.1 i.val.2
  | .inr (i, j) => A i j

private theorem orthoGenericMiddle_eval {R : Type u} [CommRing R] [Algebra k R] {m : ℕ}
    (P Q A : Block m R) :
    (orthoGenericMiddle k m).map (MvPolynomial.aeval (R := k) (orthoParameterValues P Q A)) = A := by
  ext i j
  exact MvPolynomial.aeval_X _ _

private theorem orthoParameterRing_domain (k : Type u) [Field k] (m : ℕ) :
    IsDomain (OrthoParameterRing k m) := by
  let f := MvPolynomial.aeval (R := k) (orthoParameterValues (0 : Block m k) 0 1)
  have h : f (orthoGenericMiddle k m).det = 1 := by
    change f.toRingHom (orthoGenericMiddle k m).det = 1
    rw [RingHom.map_det]
    change ((orthoGenericMiddle k m).map f).det = 1
    rw [orthoGenericMiddle_eval, det_one]
  have hne : (orthoGenericMiddle k m).det ≠ 0 := by
    intro hz
    rw [hz, map_zero] at h
    exact zero_ne_one h
  exact IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hne)

private def orthoParameterEval {R : Type u} [CommRing R] [Algebra k R] {m : ℕ}
    (P Q A : Block m R) (hA : IsUnit A.det) : OrthoParameterRing k m →ₐ[k] R :=
  IsLocalization.Away.liftAlgHom (orthoGenericMiddle k m).det
    (f := MvPolynomial.aeval (orthoParameterValues P Q A)) (by
      let f := MvPolynomial.aeval (R := k) (orthoParameterValues P Q A)
      change IsUnit (f.toRingHom _)
      rw [RingHom.map_det]
      change IsUnit ((orthoGenericMiddle k m).map f).det
      rwa [orthoGenericMiddle_eval])

private theorem orthoParameterEval_var {R : Type u} [CommRing R] [Algebra k R] {m : ℕ}
    (P Q A : Block m R) (hA : IsUnit A.det) (i : OrthoChartIndex m) :
    orthoParameterEval (k := k) P Q A hA (orthoParameter k i) = orthoParameterValues P Q A i := by
  unfold orthoParameterEval orthoParameter
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact MvPolynomial.aeval_X _ _

private theorem orthoParameterEval_blocks {R : Type u} [CommRing R] [Algebra k R] {m : ℕ}
    (P Q A : Block m R) (hP : IsAlternating P) (hQ : IsAlternating Q) (hA : IsUnit A.det) :
    let f := orthoParameterEval (k := k) P Q A hA
    (orthoGenericLower k m).val.map f = P ∧ (orthoGenericUpper k m).val.map f = Q ∧
      (orthoGenericFactor k m).map f = A := by
  intro f
  refine ⟨?_, ?_, ?_⟩
  · change (orthoGenericLower k m).val.map f.toRingHom = P
    rw [orthoGenericLower, alternating_ofCoordinates_map f.toRingHom]
    have hf : f.toRingHom ∘ (fun i => orthoParameter k (Sum.inl (Sum.inl i))) =
        alternatingCoordinates m R ⟨P, hP⟩ :=
      funext fun i => orthoParameterEval_var P Q A hA (.inl (.inl i))
    rw [hf, Equiv.symm_apply_apply]
  · change (orthoGenericUpper k m).val.map f.toRingHom = Q
    rw [orthoGenericUpper, alternating_ofCoordinates_map f.toRingHom]
    have hf : f.toRingHom ∘ (fun i => orthoParameter k (Sum.inl (Sum.inr i))) =
        alternatingCoordinates m R ⟨Q, hQ⟩ :=
      funext fun i => orthoParameterEval_var P Q A hA (.inl (.inr i))
    rw [hf, Equiv.symm_apply_apply]
  · ext i j
    exact orthoParameterEval_var P Q A hA (.inr (i, j))

private theorem orthoOpenRing_connected (O : SplitOrthogonalPresentation k I) :
    ConnectedSpace ((testSpec k).obj (op (orthoOpenRing O))).left := by
  let m := Fintype.card I
  let d : Fin m ≃ I := (Fintype.equivFin I).symm
  let e := d.sumCongr d
  let B : TestAlgebra k := CommAlgCat.of k (OrthoParameterRing k m)
  let P := orthoGenericLower k m
  let Q := orthoGenericUpper k m
  let A := orthoGenericFactor k m
  let M := lower P.val * middle A * upper Q.val
  have hA : IsUnit A.det := orthoGenericFactor_det k m
  have hM : PreservesNorm M := fun x => by
    change SplitSpinSpecification.hyperbolicNorm
      (((lower P.val * middle A) * upper Q.val) *ᵥ x) = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, lower_preserves P.property,
      middle_preserves hA, upper_preserves Q.property]
  let g := pointOfNormMatrix O B d M hM ((factor_det _ _ _ hA).symm ▸ isUnit_one)
  have hg : (O.points B g).val.val = Matrix.reindex e e M := pointOfNormMatrix_value ..
  have hgd : IsUnit (O.points B g).val.val.toBlocks₁₁.det := by
    rw [hg, show M = _ from factor_blocks A P.val Q.val]
    change IsUnit (A.submatrix d.symm d.symm).det
    rwa [Matrix.det_submatrix_equiv_self]
  obtain ⟨f, hf⟩ := orthoOpen_factors O B g hgd
  haveI : IsDomain B := orthoParameterRing_domain k m
  have hsur : Function.Surjective f.left := by
    intro z
    obtain ⟨K, _, _, p, hp⟩ := exists_field_point ((testSpec k).obj (op (orthoOpenRing O))) z
    let R : TestAlgebra k := CommAlgCat.of k K
    let a : Points O.group.val.X R := p ≫ orthoOpenInclusion O
    let N := (O.points R a).val.val.submatrix e e
    have hAd : IsUnit N.toBlocks₁₁.det := by
      change IsUnit (((O.points R a).val.val.toBlocks₁₁).submatrix d d).det
      rw [Matrix.det_submatrix_equiv_self]
      let α := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage p
      have hα : a = mapPoints α.unop (orthoOpenInclusion O) :=
        congrArg (· ≫ orthoOpenInclusion O)
          ((algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage p).symm
      rw [hα, ortho_topLeftDet_map]
      exact (orthoOpenInclusion_det O).map α.unop.hom
    have hN : PreservesNorm N := (preservesNorm_submatrix_iff d _).mpr (O.points R a).property
    obtain ⟨⟨P', Q'⟩, ⟨hP', hQ', heq⟩, _⟩ := (SplitSpin.orthogonalChart m K N hAd).mp hN
    let α := CommAlgCat.ofHom (orthoParameterEval (k := k) P' Q' N.toBlocks₁₁ hAd)
    have hmn : M.map α.hom = N := by
      obtain ⟨hP, hQ, hA'⟩ := orthoParameterEval_blocks (k := k) P' Q' N.toBlocks₁₁ hP' hQ' hAd
      exact (factor_map α.hom.toRingHom P.val Q.val A hA).trans (by
        change lower ((orthoGenericLower k m).val.map (orthoParameterEval P' Q' _ hAd)) *
          middle ((orthoGenericFactor k m).map (orthoParameterEval P' Q' _ hAd)) *
          upper ((orthoGenericUpper k m).val.map (orthoParameterEval P' Q' _ hAd)) = N
        rw [hP, hQ, hA', ← heq])
    have hm : mapPoints α g = a := by
      apply (O.points R).injective
      apply Subtype.ext
      apply Units.ext
      have hh : (O.points R (mapPoints α g)).val.val = (O.points B g).val.val.map α.hom :=
        O.naturality α g
      rw [hh, hg]
      ext i j
      change α.hom (M (e.symm i) (e.symm j)) = (O.points R a).val.val i j
      rw [show α.hom (M (e.symm i) (e.symm j)) = N (e.symm i) (e.symm j) from congrFun₂ hmn _ _]
      change (O.points R a).val.val (e (e.symm i)) (e (e.symm j)) = _
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    haveI : IsOpenImmersion (orthoOpenInclusion O).left := orthoOpenInclusion_open O
    haveI : Mono (orthoOpenInclusion O) := Over.mono_of_mono_left _
    have hb : (testSpec k).map α.op ≫ f = p := by
      apply (cancel_mono (orthoOpenInclusion O)).mp
      rw [Category.assoc, hf]
      exact hm
    refine ⟨((testSpec k).map α.op).left (IsLocalRing.closedPoint K), ?_⟩
    exact (congrArg (fun φ : Points ((testSpec k).obj (op (orthoOpenRing O))) R =>
      φ.left (IsLocalRing.closedPoint K)) hb).trans hp
  haveI : ConnectedSpace ((testSpec k).obj (op B)).left := by
    change ConnectedSpace (PrimeSpectrum B)
    infer_instance
  exact hsur.connectedSpace f.left.continuous

open SplitSpinSpecification (EvenSwitches signedSwitch HasActionMatrix integralForm)
open SpinSpecification (spinUnits IsVectorAction)
open private vectors_injective from LinearAlgebraicGroups.Albert.SpinFunctor

private abbrev vectorImageMatrix (P : SplitSpinVectorImage k I) (R : TestAlgebra k)
    (p : Points P.image.val.X R) : Matrix (I ⊕ I) (I ⊕ I) R :=
  (P.orthogonal.points R (p ≫ P.inclusion.hom.hom)).val.val

private theorem vectorImageMatrix_mul (P : SplitSpinVectorImage k I) (R : TestAlgebra k)
    (a b : Points P.image.val.X R) :
    vectorImageMatrix P R (a * b) = vectorImageMatrix P R a * vectorImageMatrix P R b := by
  change (P.orthogonal.points R ((a * b) ≫ P.inclusion.hom.hom)).val.val = _
  rw [MonObj.mul_comp]
  change ((P.orthogonal.points R) ((a ≫ P.inclusion.hom.hom) * (b ≫ P.inclusion.hom.hom))).val.val = _
  exact congrArg (fun g : orthogonalMatrices I R => g.val.val)
    (map_mul (P.orthogonal.points R) (a ≫ P.inclusion.hom.hom) (b ≫ P.inclusion.hom.hom))

private theorem vectorImageMatrix_map (P : SplitSpinVectorImage k I) {R S : TestAlgebra k}
    (f : R ⟶ S) (p : Points P.image.val.X R) :
    vectorImageMatrix P S (mapPoints f p) = (vectorImageMatrix P R p).map f.hom := by
  change (P.orthogonal.points S (((testSpec k).map f.op ≫ p) ≫ P.inclusion.hom.hom)).val.val = _
  rw [Category.assoc]
  exact P.orthogonal.naturality f (p ≫ P.inclusion.hom.hom)

private theorem integralSpinMatrix_is_image (P : SplitSpinVectorImage k I) (R : TestAlgebra k)
    [LinearOrder (I ⊕ I)] {m : ℕ} (d : Fin m ≃ I)
    (a : (SplitSpinSpecification.ScalarClifford m R)ˣ)
    (ha : a ∈ spinUnits (integralForm m) R)
    (M : Matrix (PairIndex m) (PairIndex m) R) (hM : HasActionMatrix m a M) :
    ∃ p : Points P.image.val.X R,
      vectorImageMatrix P R p = Matrix.reindex (d.sumCongr d) (d.sumCongr d) M := by
  obtain ⟨E, he⟩ := splitSpinIntegralComparison k I m d R
  let z := Units.map E.toMonoidHom a
  have hz := (he a).1.mpr ha
  rw [← (P.spinRepresents.1 R).2] at hz
  obtain ⟨b, hb⟩ := hz
  obtain ⟨g, hg, hmat⟩ := ((he a).2 M).mp hM
  obtain ⟨g', hg', hmat'⟩ := P.vector R b
  have hgg : g = g' := by
    ext x
    apply vectors_injective (OddSpinModels.hyperbolicForm I k) R (Pi.basisFun k (I ⊕ I))
    change IsVectorAction (OddSpinModels.hyperbolicForm I k) R z g at hg
    rw [hb] at hg'
    exact (hg x).trans (hg' x).symm
  refine ⟨b ≫ P.projection.hom.hom, ?_⟩
  rw [← hmat, hgg]
  exact hmat'.symm

private theorem evenSwitchPoint (P : SplitSpinVectorImage k I)
    [LinearOrder (I ⊕ I)] {m : ℕ} (d : Fin m ≃ I) (J : EvenSwitches m) :
    ∃ p : Points P.image.val.X (.of k k),
      vectorImageMatrix P (.of k k) p = Matrix.reindex (d.sumCongr d) (d.sumCongr d)
        (signedSwitch m k J.val) := by
  obtain ⟨a, ha, hM⟩ := SplitSpin.even_switch_spin_lift (S := k) J
  exact integralSpinMatrix_is_image P (.of k k) d a ha _ hM

private theorem spinPoint_evenPivot (P : SplitSpinVectorImage k I)
    [LinearOrder (I ⊕ I)] {m : ℕ} (d : Fin m ≃ I)
    (K : Type u) [Field K] [Algebra k K] (b : Points P.spin.val.X (.of k K)) :
    ∃ J : EvenSwitches m,
      IsUnit (signedSwitch m K J.val *
        (vectorImageMatrix P (.of k K) (b ≫ P.projection.hom.hom)).submatrix
          (d.sumCongr d) (d.sumCongr d)).toBlocks₁₁.det := by
  let R : TestAlgebra k := .of k K
  obtain ⟨E, he⟩ := splitSpinIntegralComparison k I m d K
  let z := P.spinPoints R b
  let a := (Units.mapEquiv E.toMulEquiv).symm z
  have hz : Units.map E.toMonoidHom a = z := (Units.mapEquiv E.toMulEquiv).apply_symm_apply z
  have ha : a ∈ spinUnits (integralForm m) K := by
    apply (he a).1.mp
    change Units.map E.toMonoidHom a ∈ spinUnits (OddSpinModels.hyperbolicForm I k) R
    rw [hz, ← (P.spinRepresents.1 R).2]
    exact ⟨b, rfl⟩
  obtain ⟨g, hg, hmat⟩ := P.vector R b
  let M := (vectorImageMatrix P R (b ≫ P.projection.hom.hom)).submatrix (d.sumCongr d) (d.sumCongr d)
  have hM : HasActionMatrix m a M := by
    apply ((he a).2 M).mpr
    refine ⟨g, ?_, ?_⟩
    · change IsVectorAction (OddSpinModels.hyperbolicForm I k) R (Units.map E.toMonoidHom a) g
      rwa [hz]
    · refine hmat.trans ?_
      ext i j
      let e := d.sumCongr d
      change (vectorImageMatrix P R (b ≫ P.projection.hom.hom)) i j =
        (vectorImageMatrix P R (b ≫ P.projection.hom.hom)) (e (e.symm i)) (e (e.symm j))
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact SplitSpin.spin_even_switch_cover a ha hM

private theorem eq_toBasePoint {X : SchemeOver k}
    (f : X ⟶ (testSpec k).obj (op (CommAlgCat.of k k))) : f = toBasePoint X := by
  apply Over.OverMorphism.ext
  have hId : ((testSpec k).obj (op (CommAlgCat.of k k))).hom = 𝟙 (Spec (CommRingCat.of k)) :=
    Spec.map_id (CommRingCat.of k)
  have hf := Over.w f
  rw [hId] at hf
  let g : X.left ⟶ Spec (CommRingCat.of k) := f.left
  change g ≫ 𝟙 _ = X.hom at hf
  exact (Category.comp_id g).symm.trans hf

private def leftTranslate {G : GroupScheme k} (s : Points G.X (.of k k)) : G.X ≅ G.X where
  hom := (toBasePoint G.X ≫ s) * 𝟙 G.X
  inv := (toBasePoint G.X ≫ s⁻¹) * 𝟙 G.X
  hom_inv_id := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
    rw [eq_toBasePoint (((toBasePoint G.X ≫ s) * 𝟙 G.X) ≫ toBasePoint G.X),
      GrpObj.comp_inv, inv_mul_cancel_left]
  inv_hom_id := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
    rw [eq_toBasePoint (((toBasePoint G.X ≫ s⁻¹) * 𝟙 G.X) ≫ toBasePoint G.X),
      GrpObj.comp_inv, mul_inv_cancel_left]

private theorem leftTranslate_points {G : GroupScheme k} (s : Points G.X (.of k k))
    (R : TestAlgebra k) (p : Points G.X R) :
    p ≫ (leftTranslate s).hom = mapPoints (CommAlgCat.ofHom (Algebra.ofId k R)) s * p := by
  change p ≫ ((toBasePoint G.X ≫ s) * 𝟙 G.X) = _
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
  rw [eq_toBasePoint (p ≫ toBasePoint G.X)]
  congr 1

private theorem spinImage_chart_factors (P : SplitSpinVectorImage k I)
    (c : Points P.image.val.X (orthoOpenRing P.orthogonal))
    (hc : c ≫ P.inclusion.hom.hom = orthoOpenInclusion P.orthogonal)
    (R : TestAlgebra k) (p : Points P.image.val.X R)
    (hp : IsUnit (vectorImageMatrix P R p).toBlocks₁₁.det) :
    ∃ a : Points ((testSpec k).obj (op (orthoOpenRing P.orthogonal))) R, a ≫ c = p := by
  obtain ⟨b, hb⟩ := orthoOpen_factors P.orthogonal R (p ≫ P.inclusion.hom.hom) hp
  haveI : IsClosedImmersion P.inclusion.hom.hom.left := P.closed
  haveI : Mono P.inclusion.hom.hom := Over.mono_of_mono_left _
  refine ⟨b, (cancel_mono P.inclusion.hom.hom).mp ?_⟩
  rwa [Category.assoc, hc]


open private signedSwitch_map from LinearAlgebraicGroups.Albert.SplitSpin

private theorem translatedChart_factors (P : SplitSpinVectorImage k I)
    (c : Points P.image.val.X (orthoOpenRing P.orthogonal))
    (hc : c ≫ P.inclusion.hom.hom = orthoOpenInclusion P.orthogonal)
    {m : ℕ} (d : Fin m ≃ I) (J : EvenSwitches m) (s : Points P.image.val.X (.of k k))
    (hs : vectorImageMatrix P (.of k k) s = Matrix.reindex (d.sumCongr d) (d.sumCongr d)
      (signedSwitch m k J.val))
    (R : TestAlgebra k) (p : Points P.image.val.X R)
    (hp : IsUnit (signedSwitch m R J.val *
      (vectorImageMatrix P R p).submatrix (d.sumCongr d) (d.sumCongr d)).toBlocks₁₁.det) :
    ∃ a : Points ((testSpec k).obj (op (orthoOpenRing P.orthogonal))) R,
      a ≫ c ≫ (leftTranslate s).inv = p := by
  let e := d.sumCongr d
  let f : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have hsR : (vectorImageMatrix P R (mapPoints f s)).submatrix e e = signedSwitch m R J.val := by
    rw [vectorImageMatrix_map, hs, ← signedSwitch_map f.hom.toRingHom]
    ext i j
    change f.hom ((signedSwitch m k J.val) (e.symm (e i)) (e.symm (e j))) =
      f.hom ((signedSwitch m k J.val) i j)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hdet : IsUnit (vectorImageMatrix P R (mapPoints f s * p)).toBlocks₁₁.det := by
    rw [← det_submatrix_equiv_self d (vectorImageMatrix P R (mapPoints f s * p)).toBlocks₁₁]
    change IsUnit ((vectorImageMatrix P R (mapPoints f s * p)).submatrix e e).toBlocks₁₁.det
    rwa [vectorImageMatrix_mul, ← submatrix_mul_equiv _ _ e e e, hsR]
  obtain ⟨a, ha⟩ := spinImage_chart_factors P c hc R (mapPoints f s * p) hdet
  refine ⟨a, ?_⟩
  have ht : p ≫ (leftTranslate s).hom = mapPoints f s * p := leftTranslate_points s R p
  rw [← Category.assoc, ha, ← ht, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem splitSpinImage_connected (hRank : 4 ≤ Fintype.card I) (P : SplitSpinVectorImage k I) :
    ConnectedSpace P.image.val.X.left := by
  let m := Fintype.card I
  let d : Fin m ≃ I := (Fintype.equivFin I).symm
  let e := d.sumCongr d
  let O := P.orthogonal
  let R₀ := orthoOpenRing O
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  obtain ⟨c, hc⟩ := splitSpinChartInImage k I hRank P R₀ (orthoOpenInclusion O) (orthoOpenInclusion_det O)
  have hs (J : EvenSwitches m) := evenSwitchPoint P d J
  choose s hs using hs
  let C := Set.range c.left
  let U (J : EvenSwitches m) := Set.range (c ≫ (leftTranslate (s J)).inv).left
  haveI : ConnectedSpace ((testSpec k).obj (op R₀)).left := orthoOpenRing_connected O
  have hC : _root_.IsConnected C := by
    simpa only [C, Set.image_univ] using isConnected_univ.image c.left c.left.continuous.continuousOn
  have hU (J : EvenSwitches m) : _root_.IsConnected (U J) := by
    simpa only [U, Set.image_univ] using
      isConnected_univ.image (c ≫ (leftTranslate (s J)).inv).left
        (c ≫ (leftTranslate (s J)).inv).left.continuous.continuousOn
  have hCover : (⋃ J, C ∪ U J) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := P.surjective.surj x
    obtain ⟨K, _, _, b, hb⟩ := exists_field_point P.spin.val.X y
    let R : TestAlgebra k := .of k K
    let p : Points P.image.val.X R := b ≫ P.projection.hom.hom
    have hp : p.left (IsLocalRing.closedPoint K) = x := by
      change P.projection.hom.hom.left (b.left (IsLocalRing.closedPoint K)) = _
      rwa [hb]
    obtain ⟨J, hJ⟩ := spinPoint_evenPivot P d K b
    obtain ⟨a, ha⟩ := translatedChart_factors P c hc d J (s J) (hs J) R p hJ
    refine Set.mem_iUnion.mpr ⟨J, Or.inr ⟨a.left (IsLocalRing.closedPoint K), ?_⟩⟩
    exact (congrArg (fun t : Points P.image.val.X R => t.left (IsLocalRing.closedPoint K)) ha).trans hp
  have hOverlap (J : EvenSwitches m) : (C ∩ U J).Nonempty := by
    let R : TestAlgebra k := .of k k
    obtain ⟨L, hL, hJL⟩ := SplitSpin.evenSwitchOverlap m k J
    have hLd : IsUnit (lower L).det := by
      simp [lower]
    let a := pointOfNormMatrix O R d (lower L) (lower_preserves hL) hLd
    have ha : (O.points R a).val.val = Matrix.reindex e e (lower L) := pointOfNormMatrix_value ..
    have had : IsUnit (O.points R a).val.val.toBlocks₁₁.det := by
      rw [ha]
      change IsUnit ((1 : Block m k).submatrix d.symm d.symm).det
      simp
    obtain ⟨p, hp⟩ := splitSpinChartInImage k I hRank P R a had
    have hM : (vectorImageMatrix P R p).submatrix e e = lower L := by
      change ((O.points R (p ≫ P.inclusion.hom.hom)).val.val).submatrix e e = _
      rw [hp, ha]
      ext i j
      change (lower L) (e.symm (e i)) (e.symm (e j)) = _
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hJ : IsUnit (signedSwitch m R J.val *
        (vectorImageMatrix P R p).submatrix e e).toBlocks₁₁.det := by
      rw [hM]
      exact hJL
    obtain ⟨z, hz⟩ := translatedChart_factors P c hc d J (s J) (hs J) R p hJ
    have hpd : IsUnit (vectorImageMatrix P R p).toBlocks₁₁.det := by
      change IsUnit (O.points R (p ≫ P.inclusion.hom.hom)).val.val.toBlocks₁₁.det
      rwa [hp]
    obtain ⟨w, hw⟩ := spinImage_chart_factors P c hc R p hpd
    let t := IsLocalRing.closedPoint k
    refine ⟨p.left t, ⟨w.left t, ?_⟩, ⟨z.left t, ?_⟩⟩
    · exact congrArg (fun g : Points P.image.val.X R => g.left t) hw
    · exact congrArg (fun g : Points P.image.val.X R => g.left t) hz
  obtain ⟨x, hx⟩ := hC.nonempty
  have hInter : (⋂ J, C ∪ U J).Nonempty :=
    ⟨x, Set.mem_iInter.mpr fun _ => Or.inl hx⟩
  rw [connectedSpace_iff_univ, ← hCover]
  refine ⟨⟨x, Set.mem_iUnion.mpr ⟨⟨∅, by simp⟩, Or.inl hx⟩⟩, ?_⟩
  exact isPreconnected_iUnion hInter (fun J => (hC.union (hOverlap J) (hU J)).isPreconnected)

theorem splitSpinIdentityComponent : SplitSpinIdentityComponent.{u} := by
  intro k I _ _ _ hRank P
  let j := P.inclusion.hom.hom
  let e := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))
  haveI : IsOpenImmersion j.left := splitSpinOpenImage k I hRank P
  haveI : IsClosedImmersion j.left := P.closed
  haveI : ConnectedSpace P.image.val.X.left := splitSpinImage_connected hRank P
  have hC : _root_.IsConnected (Set.range j.left) := by
    simpa only [Set.image_univ] using isConnected_univ.image j.left j.left.continuous.continuousOn
  have he : η[P.orthogonal.group.val.X].left e ∈ Set.range j.left := by
    refine ⟨η[P.image.val.X].left e, ?_⟩
    exact congrArg (fun f : (𝟙_ (SchemeOver k)) ⟶ P.orthogonal.group.val.X => f.left e)
      (IsMonHom.one_hom j)
  have hopen : IsClopen (Set.range j.left) :=
    ⟨j.left.isClosedEmbedding.isClosed_range, j.left.isOpenEmbedding.isOpen_range⟩
  have hr : Set.range j.left = connectedComponent (η[P.orthogonal.group.val.X].left e) :=
    (hC.subset_connectedComponent he).antisymm
      (isPreconnected_connectedComponent.subset_isClopen hopen ⟨_, mem_connectedComponent, he⟩)
  obtain ⟨Q, H, f, i, hI, _⟩ := _root_.LinearAlgebraicGroups.identityComponentAndQuotient k P.orthogonal.group
  haveI : IsOpenImmersion i.hom.hom.left := hI.openImmersion
  have hij : Set.range j.left = Set.range i.hom.hom.left := hr.trans hI.identityComponent.symm
  let α := IsOpenImmersion.isoOfRangeEq j.left i.hom.hom.left hij
  have hf : α.hom ≫ H.X.hom = P.image.val.X.hom := by
    rw [← Over.w i.hom.hom, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Over.w j]
  refine ⟨?_, hr⟩
  have hpb : IsPullback α.hom P.image.val.X.hom H.X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hf⟩
  exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb hI.geometricallyConnected

open _root_.LinearAlgebraicGroups.Specs (coordinates)

private def hyperbolicPairIndices (m : ℕ) : Bool × Fin m ≃ PairIndex m where
  toFun p := if p.1 then Sum.inr p.2 else Sum.inl p.2
  invFun := Sum.elim (fun i => (false, i)) (fun i => (true, i))
  left_inv := by rintro ⟨_ | _, i⟩ <;> rfl
  right_inv := by rintro (i | i) <;> rfl

private theorem signedSwitch_det {R : Type*} [CommRing R]
    (m : ℕ) (J : Finset (Fin m)) : (signedSwitch m R J).det = (-1 : R) ^ J.card := by
  classical
  let e := hyperbolicPairIndices m
  let H (i : Fin m) : Matrix Bool Bool R :=
    if i ∈ J then -((Equiv.swap false true).permMatrix R) else 1
  have he : (signedSwitch m R J).submatrix e e = Matrix.blockDiagonal H := by
    ext a b
    obtain ⟨a, i⟩ := a
    obtain ⟨b, j⟩ := b
    rw [Matrix.blockDiagonal_apply]
    by_cases hij : i = j
    · subst j
      by_cases hi : i ∈ J <;>
        cases a <;> cases b <;>
          simp [e, hyperbolicPairIndices, signedSwitch, H, hi, Equiv.Perm.permMatrix]
    · cases a <;> cases b <;> simp [e, hyperbolicPairIndices, signedSwitch, hij]
  rw [← Matrix.det_submatrix_equiv_self e (signedSwitch m R J), he, Matrix.det_blockDiagonal]
  have h (i : Fin m) : (H i).det = if i ∈ J then -1 else 1 := by
    by_cases hi : i ∈ J
    · simp [H, hi, Matrix.det_neg, Matrix.det_permutation]
    · simp [H, hi]
  simp only [h, Finset.prod_ite_mem_eq, Finset.prod_const]

private theorem orthogonalDet_sq {R : Type u} [CommRing R] (g : orthogonalMatrices I R) :
    g.val.val.det ^ 2 = 1 := by
  let J := hyperbolicGram I R
  let L := hyperbolicProjection I R
  have hq (x : I ⊕ I → R) :=
    (splitSemitrace_over_ring I R).2.1 x
  have h (x : I ⊕ I → R) : diagonalValue (J * L) (g.val.val *ᵥ x) =
      ((1 : Rˣ) : R) * diagonalValue (J * L) x := by
    change diagonalValue (hyperbolicGram I R * hyperbolicProjection I R) (g.val.val *ᵥ x) =
      ((1 : Rˣ) : R) * diagonalValue (hyperbolicGram I R * hyperbolicProjection I R) x
    rw [hq, hq, Units.val_one, one_mul]
    exact g.property x
  have hpol : g.val.val.transpose * J * g.val.val = J := by
    simpa only [Units.val_one, one_smul] using
      matrixQuadraticSimilitude_polar g.val L (hyperbolicProjection_polar I R) 1 h
  have hJ : IsUnit J.det :=
    IsUnit.of_mul_eq_one _ (by rw [← det_mul, hyperbolicGram_square, det_one])
  have hd := congrArg Matrix.det hpol
  simp only [det_mul, det_transpose] at hd
  apply hJ.mul_left_cancel
  calc
    J.det * g.val.val.det ^ 2 = g.val.val.det * J.det * g.val.val.det := by ring
    _ = J.det * 1 := hd.trans (mul_one _).symm

private theorem orthogonalDet_chart {m : ℕ} {R : Type u} [CommRing R]
    (M : Matrix (PairIndex m) (PairIndex m) R) (hM : PreservesNorm M)
    (hd : IsUnit M.toBlocks₁₁.det) : M.det = 1 := by
  obtain ⟨⟨P, Q⟩, ⟨_, _, h⟩, _⟩ := (SplitSpin.orthogonalChart m R M hd).mp hM
  rw [h]
  exact factor_det P Q M.toBlocks₁₁ hd

private theorem orthogonalPoint_det_natural (O : SplitOrthogonalPresentation k I)
    {R S : TestAlgebra k} (f : R ⟶ S) (a : Points O.group.val.X R) :
    (O.points S (mapPoints f a)).val.val.det = f.hom (O.points R a).val.val.det :=
  (congrArg Matrix.det (O.naturality f a)).trans (f.hom.toRingHom.map_det _).symm

private theorem imageDet_one (hRank : 4 ≤ Fintype.card I) (h₂ : (2 : k) ≠ 0)
    (P : SplitSpinVectorImage k I) (R : TestAlgebra k) (a : Points P.image.val.X R) :
    (vectorImageMatrix P R a).det = 1 := by
  let X := P.image.val.X
  let A := coordinates X
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  haveI := P.image.property.1
  haveI : IsIso (coordinateUnit X) := coordinateUnit_isIso X
  haveI : ConnectedSpace X.left :=
    @GeometricallyConnected.connectedSpace_of_subsingleton _ _ X.hom
      (splitSpinIdentityComponent k I hRank P).1 inferInstance inferInstance
  haveI : IsIso (coordinateUnit X).left := (Over.forget _).map_isIso (coordinateUnit X)
  let fX : X.left ⟶ Spec (CommRingCat.of A) := (coordinateUnit X).left
  haveI : IsIso fX := (Over.forget _).map_isIso (coordinateUnit X)
  haveI : ConnectedSpace (PrimeSpectrum A) := fX.surjective.connectedSpace fX.continuous
  let u := universalPoint X
  let d := (vectorImageMatrix P A u).det
  have hd : d ^ 2 = 1 := orthogonalDet_sq (P.orthogonal.points A (u ≫ P.inclusion.hom.hom))
  let t := algebraMap k A ((2 : k)⁻¹)
  have ht : (2 : A) * t = 1 := by
    change _ * algebraMap k A ((2 : k)⁻¹) = _
    rw [← map_ofNat (algebraMap k A) 2, ← map_mul, mul_inv_cancel₀ h₂, map_one]
  let e := t * (d + 1)
  let f := t * (1 - d)
  have hsum : e + f = 1 := by
    calc
      e + f = 2 * t := by dsimp [e, f]; ring
      _ = 1 := ht
  have hmul : e * f = 0 := by
    calc
      e * f = t ^ 2 * (1 - d ^ 2) := by dsimp [e, f]; ring
      _ = 0 := by rw [hd, sub_self, mul_zero]
  let E := PrimeSpectrum.basicOpen e
  have hcl : IsClopen (E : Set (PrimeSpectrum A)) := PrimeSpectrum.isClopen_basicOpen_of_mul_add e f hmul hsum
  let b : Points X (.of k k) := 1
  let β := (F.preimage (b ≫ coordinateUnit X)).unop
  have hβ : mapPoints β u = b := by
    change (testSpec k).map (F.preimage (b ≫ coordinateUnit X)) ≫ u = b
    rw [F.map_preimage, Category.assoc]
    simp [u, universalPoint]
  have hb : β.hom d = 1 := by
    let p := vectorImageMatrix P (.of k k) (mapPoints β u)
    have hp : p = (vectorImageMatrix P A u).map β.hom := vectorImageMatrix_map P β u
    have hd' : p.det = β.hom d := (congrArg Matrix.det hp).trans (β.hom.toRingHom.map_det _).symm
    rw [← hd']
    change (vectorImageMatrix P (.of k k) (mapPoints β u)).det = _
    rw [hβ]
    change (P.orthogonal.points (.of k k) (b ≫ P.inclusion.hom.hom)).val.val.det = _
    rw [show b = 1 from rfl, MonObj.one_comp]
    exact (congrArg (fun g : orthogonalMatrices I k => g.val.val.det)
      (map_one (P.orthogonal.points (.of k k)))).trans det_one
  have heval : β.hom e = 1 := by
    change β.hom (algebraMap k A ((2 : k)⁻¹) * (d + 1)) = _
    rw [map_mul, AlgHom.commutes, map_add, hb, map_one]
    change (2 : k)⁻¹ * (1 + 1) = _
    rw [one_add_one_eq_two, inv_mul_cancel₀ h₂]
  let z : PrimeSpectrum k := IsLocalRing.closedPoint k
  have hz : (PrimeSpectrum.comap β.hom.toRingHom z) ∈ E := by
    change β.hom e ∉ z.asIdeal
    rw [heval]
    exact fun hm => z.2.ne_top ((Ideal.eq_top_iff_one _).mpr hm)
  have hE : E = ⊤ := TopologicalSpace.Opens.ext (hcl.eq_univ ⟨_, hz⟩)
  have hunit : IsUnit e := by
    by_contra hn
    obtain ⟨J, hJ, heJ⟩ := exists_max_ideal_of_mem_nonunits hn
    let z : PrimeSpectrum A := ⟨J, hJ.isPrime⟩
    have hz' : z ∈ E := hE.symm ▸ trivial
    exact hz' heJ
  have hz' : f = 0 := hunit.mul_left_cancel (hmul.trans (mul_zero _).symm)
  have hd' : d = 1 := by
    have ht' : IsUnit t := IsUnit.of_mul_eq_one _ (by rw [mul_comm, ht])
    have hf' : 1 - d = 0 := ht'.mul_left_cancel (hz'.trans (mul_zero _).symm)
    exact (sub_eq_zero.mp hf').symm
  let w := (F.preimage (a ≫ coordinateUnit X)).unop
  have hw : mapPoints w u = a := by
    change (testSpec k).map (F.preimage (a ≫ coordinateUnit X)) ≫ u = a
    rw [F.map_preimage, Category.assoc]
    simp [u, universalPoint]
  rw [← hw, vectorImageMatrix_map]
  change ((vectorImageMatrix P A u).map w.hom).det = _
  exact ((w.hom.toRingHom.map_det _).symm.trans (by rw [show (vectorImageMatrix P A u).det = d from rfl, hd', map_one]))

private theorem detOne_field_factors (hRank : 4 ≤ Fintype.card I) (h₂ : (2 : k) ≠ 0)
    (P : SplitSpinVectorImage k I) (K : Type u) [Field K] [Algebra k K]
    (a : Points P.orthogonal.group.val.X (.of k K))
    (ha : (P.orthogonal.points (.of k K) a).val.val.det = 1) :
    ∃ b : Points P.image.val.X (.of k K), b ≫ P.inclusion.hom.hom = a := by
  let m := Fintype.card I
  let d : Fin m ≃ I := (Fintype.equivFin I).symm
  let e := d.sumCongr d
  let O := P.orthogonal
  let R : TestAlgebra k := .of k K
  let A := (O.points R a).val.val
  let M := A.submatrix e e
  have hM : PreservesNorm M := (preservesNorm_submatrix_iff d _).mpr (O.points R a).property
  have hd : M.det = 1 := (det_submatrix_equiv_self e A).trans ha
  have hInj : Function.Injective M.mulVec := Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (hd.symm ▸ isUnit_one))
  obtain ⟨J, hJ⟩ := SplitSpin.exists_switch_invertible_block M hM hInj
  have hS := (SplitSpin.signedSwitchProperties m K J).1
  have hSM : PreservesNorm (signedSwitch m K J * M) := fun v => by
    rw [← Matrix.mulVec_mulVec, hS, hM]
  have hdet := orthogonalDet_chart _ hSM hJ
  rw [det_mul, hd, mul_one, signedSwitch_det] at hdet
  have hev : Even J.card := by
    by_contra hn
    rw [(Nat.not_even_iff_odd.mp hn).neg_one_pow] at hdet
    have h : (2 : K) = 0 := by linear_combination -hdet
    exact h₂ ((algebraMap k K).injective (by simpa only [map_ofNat, map_zero] using h))
  let J' : EvenSwitches m := ⟨J, hev⟩
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  obtain ⟨s, hs⟩ := evenSwitchPoint P d J'
  let f : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  let sR := mapPoints f s
  have hsR : (vectorImageMatrix P R sR).submatrix e e = signedSwitch m K J := by
    change (vectorImageMatrix P R (mapPoints f s)).submatrix e e = _
    rw [vectorImageMatrix_map, hs, ← signedSwitch_map f.hom.toRingHom]
    ext i j
    change f.hom ((signedSwitch m k J) (e.symm (e i)) (e.symm (e j))) =
      f.hom ((signedSwitch m k J) i j)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  let b := (sR ≫ P.inclusion.hom.hom) * a
  have hbd : IsUnit (O.points R b).val.val.toBlocks₁₁.det := by
    rw [← det_submatrix_equiv_self d (O.points R b).val.val.toBlocks₁₁]
    change IsUnit ((O.points R b).val.val.submatrix e e).toBlocks₁₁.det
    have hb : (O.points R b).val.val = (vectorImageMatrix P R sR) * A :=
      congrArg (fun g : orthogonalMatrices I R => g.val.val)
        (map_mul (O.points R) (sR ≫ P.inclusion.hom.hom) a)
    rwa [hb, ← submatrix_mul_equiv _ _ e e e, hsR]
  obtain ⟨c, hc⟩ := splitSpinChartInImage k I hRank P R b hbd
  refine ⟨sR⁻¹ * c, ?_⟩
  rw [MonObj.mul_comp, GrpObj.inv_comp, hc]
  exact inv_mul_cancel_left _ _

theorem splitSpinDeterminant : SplitSpinDeterminant.{u} := by
  intro k I _ _ _ hRank h₂ P R a
  constructor
  · intro ha
    let j := P.inclusion.hom.hom
    haveI : IsOpenImmersion j.left := splitSpinOpenImage k I hRank P
    have hRange : Set.range a.left ⊆ Set.range j.left := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨K, _, _, xK, hxK⟩ := exists_field_point ((testSpec k).obj (op R)) x
      let F := algSpec.fullyFaithful (R := CommRingCat.of k)
      let f := (F.preimage xK).unop
      have h : mapPoints f a = xK ≫ a :=
        congrArg (· ≫ a) (F.map_preimage xK)
      have hd := orthogonalPoint_det_natural P.orthogonal f a
      rw [h, ha, map_one] at hd
      obtain ⟨b, hb⟩ := detOne_field_factors hRank h₂ P K (xK ≫ a) hd
      exact ⟨b.left (IsLocalRing.closedPoint K), by
        change (b ≫ j).left (IsLocalRing.closedPoint K) = _
        rw [hb]
        change a.left (xK.left (IsLocalRing.closedPoint K)) = _
        rw [hxK]⟩
    let l := IsOpenImmersion.lift j.left a.left hRange
    have hl : l ≫ j.left = a.left := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
    rw [← Over.w j, ← Category.assoc, hl, Over.w a]
  · rintro ⟨b, rfl⟩
    exact imageDet_one hRank h₂ P R b


end

end SplitSpinOpenImage

section ProjectiveCliffordAction

open CliffordAlgebra

set_option maxHeartbeats 480000 in
theorem projectiveCliffordAction :
    ProjectiveCliffordAction.{u} := by
  intro I K _ _ _ _ q P
  let V := I ⊕ I → K
  let e : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ ≃* (V ≃ₗ[K] V) := matrixColumnEquiv
  have he (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (x : V) : e g x = g.val *ᵥ x :=
    Matrix.toLinAlgEquiv'_apply g.val x
  have hq (x : V) := (splitSemitrace_over_ring I K).2.1 x
  have hPair (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) :
      PreservesQuadraticPair (hyperbolicGram I K) (hyperbolicProjection I K) (conjugate g) ↔
        ∃ c : Kˣ, ∀ x, q (e g x) = (c : K) * q x := by
    simpa only [hq, he] using conjugate_pair_iff (hyperbolicGram_transpose I K)
      (hyperbolicGram_square I K) (hyperbolicProjection I K) (hyperbolicProjection_polar I K) g
  constructor
  · intro a
    constructor
    · rintro ⟨d, rfl⟩
      change PreservesQuadraticPair (hyperbolicGram I K) (hyperbolicProjection I K)
        (conjugate (e.symm d.val.1))
      exact (hPair _).mpr ⟨d.val.2, fun x => by rw [e.apply_symm_apply]; exact d.property x⟩
    · intro ha
      have hCSA : _root_.Specs.RM03.CSA.isCentralSimple K (Matrix (I ⊕ I) (I ⊕ I) K) :=
        ⟨inferInstance, inferInstance, inferInstance⟩
      obtain ⟨g, hg⟩ := RM03.CSA.algEquiv_isInner hCSA a
      have ha' : (a : Matrix (I ⊕ I) (I ⊕ I) K → _) = conjugate g := funext hg
      rw [ha'] at ha
      obtain ⟨c, hc⟩ := (hPair _).mp ha
      let d : quadraticSimilitudes q := ⟨(e g, c), hc⟩
      refine ⟨d, AlgEquiv.ext fun X => ?_⟩
      change conjugate (e.symm (e g)) X = a X
      rw [e.symm_apply_apply]
      exact (hg X).symm
  · let C₀ := cliffordSimilitudeHom q
    have hSame (d h : quadraticSimilitudes q) (hh : P d = P h) : C₀ d = C₀ h := by
      have hQuot : P (d * h⁻¹) = 1 := by rw [map_mul, map_inv, hh, mul_inv_cancel]
      let g := e.symm (d * h⁻¹).val.1
      have hg (X : Matrix (I ⊕ I) (I ⊕ I) K) : conjugate g X = X :=
        DFunLike.congr_fun hQuot X
      obtain ⟨s, hs⟩ := (matrix_conjugate_eq_scalar_iff g).mp hg
      have hScalar (x : V) : d.val.1 x = (s : K) • h.val.1 x := by
        have hv := he g (h.val.1 x)
        rw [hs, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec] at hv
        rw [show e g = (d * h⁻¹).val.1 from e.apply_symm_apply _] at hv
        change d.val.1 (h.val.1.symm (h.val.1 x)) = _ at hv
        rwa [h.val.1.symm_apply_apply] at hv
      obtain ⟨i⟩ := ‹Nonempty I›
      let x : V := Sum.elim (Pi.single i 1) (Pi.single i 1)
      have hx : q x = 1 := by
        change OddSpinModels.hyperbolicForm I K x = 1
        simp only [hyperbolicForm_apply, x, Sum.elim_inl, Sum.elim_inr]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Pi.single_eq_of_ne hj]
        · simp
      have hc : d.val.2 = s ^ 2 * h.val.2 := by
        apply Units.ext
        have hv := d.property x
        rw [hScalar, q.map_smul, h.property, hx, mul_one, mul_one] at hv
        simpa only [Units.val_mul, Units.val_pow_eq_pow_val, pow_two, smul_eq_mul] using hv.symm
      exact evenCliffordEquiv_of_scalar d h s hScalar hc
    let representative (a : P.range) : quadraticSimilitudes q := a.property.choose
    have hRep (a : P.range) : P (representative a) = a.val := a.property.choose_spec
    let action (a : P.range) := C₀ (representative a)
    have hAction (a : P.range) (d : quadraticSimilitudes q) (hd : P d = a.val) : action a = C₀ d :=
      hSame _ _ ((hRep a).trans hd.symm)
    let C : P.range →* (even q ≃ₐ[K] even q) :=
      { toFun := action
        map_one' := (hAction 1 1 (map_one P)).trans (map_one C₀)
        map_mul' a b := by
          change action (a * b) = C₀ (representative a) * C₀ (representative b)
          refine (hAction (a * b) (representative a * representative b) ?_).trans (map_mul C₀ _ _)
          rw [map_mul, hRep, hRep]
          rfl }
    refine ⟨C, ?_, ?_⟩
    · intro g x y
      change action (P.rangeRestrict g) ((even.ι q).bilin x y) = _
      rw [hAction _ g rfl]
      exact evenCliffordEquiv_pair g x y
    · intro a z hz
      exact evenCliffordEquiv_reverse (representative a) z

end ProjectiveCliffordAction

section SplitProjectiveSpinAction

open AlgebraicGeometry CategoryTheory Opposite CliffordAlgebra TensorProduct
open scoped CategoryTheory.MonObj

open LinearAlgebraicGroups.Albert
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open SpinSpecification (ScalarClifford spinUnits IsVectorAction coefficientMap)

noncomputable section

set_option linter.unusedSectionVars false

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]
variable (P : SplitSpinVectorImage k I)
local notation "q" => OddSpinModels.hyperbolicForm I k
local notation "b" => Pi.basisFun k (I ⊕ I)

private abbrev EvenUnits (R : TestAlgebra k) := (R ⊗[k] even q)ˣ

private abbrev evenInclusion (R : TestAlgebra k) : EvenUnits (I := I) R →* (ScalarClifford q R)ˣ :=
  Units.map (evenTensorInclusion q R).toMonoidHom

private theorem evenInclusion_injective (R : TestAlgebra k) : Function.Injective (evenInclusion (I := I) R) :=
  Units.map_injective (evenTensorInclusion_injective q R)

private def spinEvenPoint (R : TestAlgebra k) (a : Points P.spin.val.X R) : EvenUnits (I := I) R :=
  (spin_in_evenTensor q b R (P.spinPoints R a)
    (Set.range_subset_iff.mp (P.spinRepresents.1 R).2.le a)).choose

private theorem spinEvenPoint_formula (R : TestAlgebra k) (a : Points P.spin.val.X R) :
    evenInclusion R (spinEvenPoint P R a) = P.spinPoints R a :=
  (spin_in_evenTensor q b R (P.spinPoints R a)
    (Set.range_subset_iff.mp (P.spinRepresents.1 R).2.le a)).choose_spec

private theorem spinEvenPoint_eq (R : TestAlgebra k) (a : Points P.spin.val.X R)
    (z : EvenUnits (I := I) R) (hz : evenInclusion R z = P.spinPoints R a) : spinEvenPoint P R a = z :=
  evenInclusion_injective R ((spinEvenPoint_formula P R a).trans hz.symm)

private abbrev evenAction (R : TestAlgebra k) (g : quadraticSimilitudes q) : EvenUnits (I := I) R →* EvenUnits (I := I) R :=
  Units.map (Algebra.TensorProduct.map (AlgHom.id R R) (evenCliffordEquiv g).toAlgHom).toMonoidHom

private theorem spinActionPoint_exists (R : TestAlgebra k) (g : quadraticSimilitudes q)
    (a : Points P.spin.val.X R) :
    ∃ c : Points P.spin.val.X R,
      P.spinPoints R c = evenInclusion R (evenAction R g (spinEvenPoint P R a)) := by
  let z := spinEvenPoint P R a
  have hz := spinEvenPoint_formula P R a
  have hmem : evenInclusion R z ∈ spinUnits q R := by
    rw [hz, ← (P.spinRepresents.1 R).2]
    exact ⟨a, rfl⟩
  obtain ⟨h, hh, _⟩ := P.vector R a
  have hv : IsVectorAction q R (evenInclusion R z) h := hz.symm ▸ hh
  have hout : evenInclusion R (evenAction R g z) ∈ spinUnits q R :=
    (tensorCliffordSimilitude_spin q b R g z h hmem hv).1
  change evenInclusion R (evenAction R g z) ∈ Set.range (P.spinPoints R)
  rwa [(P.spinRepresents.1 R).2]

private def spinActionPoint (R : TestAlgebra k) (g : quadraticSimilitudes q) (a : Points P.spin.val.X R) :
    Points P.spin.val.X R :=
  (spinActionPoint_exists P R g a).choose

private theorem spinActionPoint_formula (R : TestAlgebra k) (g : quadraticSimilitudes q)
    (a : Points P.spin.val.X R) :
    P.spinPoints R (spinActionPoint P R g a) = evenInclusion R (evenAction R g (spinEvenPoint P R a)) :=
  (spinActionPoint_exists P R g a).choose_spec

private theorem spinActionPoint_vector (R : TestAlgebra k) (g : quadraticSimilitudes q)
    (a : Points P.spin.val.X R) {h : (R ⊗[k] (I ⊕ I → k)) ≃ₗ[R] (R ⊗[k] (I ⊕ I → k))}
    (hh : IsVectorAction q R (P.spinPoints R a) h) :
    let gR := LinearEquiv.baseChange k R _ _ g.val.1
    IsVectorAction q R (P.spinPoints R (spinActionPoint P R g a)) (gR * h * gR⁻¹) := by
  intro gR
  let z := spinEvenPoint P R a
  have hz := spinEvenPoint_formula P R a
  have hmem : evenInclusion R z ∈ spinUnits q R := by
    rw [hz, ← (P.spinRepresents.1 R).2]
    exact ⟨a, rfl⟩
  rw [spinActionPoint_formula]
  exact (tensorCliffordSimilitude_spin q b R g z h hmem (hz.symm ▸ hh)).2

private def spinActionPointHom (R : TestAlgebra k) (g : quadraticSimilitudes q) :
    Points P.spin.val.X R →* Points P.spin.val.X R where
  toFun := spinActionPoint P R g
  map_one' := (P.spinRepresents.1 R).1 (by
    rw [spinActionPoint_formula, spinEvenPoint_eq P R 1 1 (by rw [map_one, map_one]),
      map_one, map_one, map_one])
  map_mul' a c := (P.spinRepresents.1 R).1 (by
    have h : spinEvenPoint P R (a * c) = spinEvenPoint P R a * spinEvenPoint P R c := by
      apply spinEvenPoint_eq
      rw [map_mul, spinEvenPoint_formula, spinEvenPoint_formula, map_mul]
    rw [map_mul, spinActionPoint_formula, spinActionPoint_formula, spinActionPoint_formula,
      h, map_mul, map_mul])

private abbrev changeEvenUnits {R S : TestAlgebra k} (f : R ⟶ S) : EvenUnits (I := I) R →* EvenUnits (I := I) S :=
  Units.map (Algebra.TensorProduct.map f.hom (AlgHom.id k (even q))).toMonoidHom

private theorem evenInclusion_change {R S : TestAlgebra k} (f : R ⟶ S) (z : EvenUnits (I := I) R) :
    evenInclusion S (changeEvenUnits f z) =
      Units.map (coefficientMap q R f.hom).toMonoidHom (evenInclusion R z) := by
  ext
  change evenTensorInclusion q S (Algebra.TensorProduct.map f.hom (AlgHom.id k (even q)) z.val) =
    coefficientMap q R f.hom (evenTensorInclusion q R z.val)
  generalize z.val = x
  induction x with
  | tmul r v => rfl
  | add a c ha hc => simp only [map_add, ha, hc]

private theorem spinEvenPoint_natural {R S : TestAlgebra k} (f : R ⟶ S) (a : Points P.spin.val.X R) :
    spinEvenPoint P S (mapPoints f a) = changeEvenUnits f (spinEvenPoint P R a) := by
  apply spinEvenPoint_eq
  rw [evenInclusion_change, spinEvenPoint_formula]
  exact (P.spinRepresents.2 f a).symm

private theorem evenAction_change {R S : TestAlgebra k} (f : R ⟶ S)
    (g : quadraticSimilitudes q) (z : EvenUnits (I := I) R) :
    evenAction S g (changeEvenUnits f z) = changeEvenUnits f (evenAction R g z) := by
  ext
  change Algebra.TensorProduct.map (AlgHom.id S S) (evenCliffordEquiv g).toAlgHom
      (Algebra.TensorProduct.map f.hom (AlgHom.id k (even q)) z.val) =
    Algebra.TensorProduct.map f.hom (AlgHom.id k (even q))
      (Algebra.TensorProduct.map (AlgHom.id R R) (evenCliffordEquiv g).toAlgHom z.val)
  generalize z.val = x
  induction x with
  | tmul r v => rfl
  | add a c ha hc => simp only [map_add, ha, hc]

private theorem spinActionPoint_naturality {R S : TestAlgebra k} (f : R ⟶ S)
    (g : quadraticSimilitudes q) (a : Points P.spin.val.X R) :
    spinActionPoint P S g (mapPoints f a) = mapPoints f (spinActionPoint P R g a) := by
  apply (P.spinRepresents.1 S).1
  rw [spinActionPoint_formula, spinEvenPoint_natural, evenAction_change, evenInclusion_change, ← spinActionPoint_formula]
  exact (P.spinRepresents.2 f _).symm

private theorem spinActionPoint_one (R : TestAlgebra k) (a : Points P.spin.val.X R) :
    spinActionPoint P R 1 a = a := by
  apply (P.spinRepresents.1 R).1
  rw [spinActionPoint_formula]
  have h : evenCliffordEquiv (1 : quadraticSimilitudes q) = 1 := map_one (cliffordSimilitudeHom q)
  change evenInclusion R (Units.map (Algebra.TensorProduct.map (AlgHom.id R R)
    (evenCliffordEquiv (1 : quadraticSimilitudes q)).toAlgHom).toMonoidHom
      (spinEvenPoint P R a)) = _
  rw [h]
  change evenInclusion R (Units.map (Algebra.TensorProduct.map (AlgHom.id R R)
    (AlgHom.id k (even q))).toMonoidHom (spinEvenPoint P R a)) = _
  rw [Algebra.TensorProduct.map_id]
  exact spinEvenPoint_formula P R a

private theorem spinActionPoint_mul (R : TestAlgebra k) (g h : quadraticSimilitudes q)
    (a : Points P.spin.val.X R) : spinActionPoint P R (g * h) a = spinActionPoint P R g (spinActionPoint P R h a) := by
  apply (P.spinRepresents.1 R).1
  rw [spinActionPoint_formula, spinActionPoint_formula,
    spinEvenPoint_eq P R _ _ (spinActionPoint_formula P R h a).symm]
  congr 1
  apply Units.ext
  let z := (spinEvenPoint P R a).val
  change Algebra.TensorProduct.map (AlgHom.id R R) (evenCliffordEquiv (g * h)).toAlgHom z =
    Algebra.TensorProduct.map (AlgHom.id R R) (evenCliffordEquiv g).toAlgHom
      (Algebra.TensorProduct.map (AlgHom.id R R) (evenCliffordEquiv h).toAlgHom z)
  have hm : evenCliffordEquiv (g * h) = evenCliffordEquiv g * evenCliffordEquiv h :=
    map_mul (cliffordSimilitudeHom q) g h
  rw [hm]
  change Algebra.TensorProduct.map (AlgHom.id R R)
    ((evenCliffordEquiv g).toAlgHom.comp (evenCliffordEquiv h).toAlgHom) z = _
  rw [Algebra.TensorProduct.map_id_comp, AlgHom.comp_apply]

private def spinActionPointEquiv (R : TestAlgebra k) (g : quadraticSimilitudes q) :
    Points P.spin.val.X R ≃* Points P.spin.val.X R where
  __ := spinActionPointHom P R g
  invFun := spinActionPoint P R g⁻¹
  left_inv a := by
    change spinActionPoint P R g⁻¹ (spinActionPoint P R g a) = _
    rw [← spinActionPoint_mul, inv_mul_cancel, spinActionPoint_one]
  right_inv a := by
    change spinActionPoint P R g (spinActionPoint P R g⁻¹ a) = _
    rw [← spinActionPoint_mul, mul_inv_cancel, spinActionPoint_one]

private def spinActionIso (g : quadraticSimilitudes q) :
    (groupPointsFunctor k).obj P.spin.val ≅ (groupPointsFunctor k).obj P.spin.val := by
  refine NatIso.ofComponents (fun R => (spinActionPointEquiv P R g).toGrpIso) ?_
  intro R S f
  apply GrpCat.ext
  intro a
  exact spinActionPoint_naturality P f g a

private def spinSchemeAction (g : quadraticSimilitudes q) : P.spin.val ≅ P.spin.val := by
  let E := AffineAlgebraicGroup.groupHomEquiv P.spin P.spin
  let a := spinActionIso P g
  refine ⟨E.symm a.hom, E.symm a.inv, ?_, ?_⟩ <;> apply E.injective
  · change (groupPointsFunctor k).map (E.symm a.hom ≫ E.symm a.inv) = (groupPointsFunctor k).map (𝟙 _)
    rw [Functor.map_comp, (groupPointsFunctor k).map_id P.spin.val]
    change E (E.symm a.hom) ≫ E (E.symm a.inv) = _
    rw [E.apply_symm_apply, E.apply_symm_apply, Iso.hom_inv_id]
  · change (groupPointsFunctor k).map (E.symm a.inv ≫ E.symm a.hom) = (groupPointsFunctor k).map (𝟙 _)
    rw [Functor.map_comp, (groupPointsFunctor k).map_id P.spin.val]
    change E (E.symm a.inv) ≫ E (E.symm a.hom) = _
    rw [E.apply_symm_apply, E.apply_symm_apply, Iso.inv_hom_id]

private theorem spinSchemeAction_points (R : TestAlgebra k) (g : quadraticSimilitudes q)
    (a : Points P.spin.val.X R) :
    a ≫ (spinSchemeAction P g).hom.hom.hom = spinActionPoint P R g a := by
  let E := AffineAlgebraicGroup.groupHomEquiv P.spin P.spin
  have h := E.apply_symm_apply (spinActionIso P g).hom
  exact congrArg (fun τ => τ.app R a) h

private theorem evenCliffordEquiv_eq_of_projective [Nonempty I] (g h : quadraticSimilitudes q)
    (hg : projectiveMatrixAction I k g = projectiveMatrixAction I k h) :
    evenCliffordEquiv g = evenCliffordEquiv h := by
  obtain ⟨_, C, hC, _⟩ := projectiveCliffordAction I k
  have he (g : quadraticSimilitudes q) :
      evenCliffordEquiv g = C ((projectiveMatrixAction I k).rangeRestrict g) := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply even.algHom_ext
    apply EvenHom.ext
    apply LinearMap.ext₂
    intro x y
    exact (evenCliffordEquiv_pair g x y).trans (hC g x y).symm
  exact (he g).trans ((congrArg C (Subtype.ext hg)).trans (he h).symm)

theorem splitProjectiveSpinAction : SplitProjectiveSpinAction.{u} := by
  intro k I _ _ _ _ P form
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  refine ⟨cliffordSimilitudeHom form, spinSchemeAction P, ?_, ?_, evenCliffordEquiv_pair, ?_, ?_, ?_⟩
  · intro g h hg
    apply Iso.ext
    apply (AffineAlgebraicGroup.groupHomEquiv P.spin P.spin).injective
    apply NatTrans.ext
    funext R
    apply GrpCat.ext
    intro a
    let a' : Points P.spin.val.X R := a
    change a' ≫ (spinSchemeAction P g).hom.hom.hom = a' ≫ (spinSchemeAction P h).hom.hom.hom
    rw [spinSchemeAction_points, spinSchemeAction_points]
    apply (P.spinRepresents.1 R).1
    rw [spinActionPoint_formula, spinActionPoint_formula]
    exact congrArg (fun C : even form ≃ₐ[k] even form => evenInclusion R
      (Units.map (Algebra.TensorProduct.map (AlgHom.id R R) C.toAlgHom).toMonoidHom (spinEvenPoint P R a')))
      (evenCliffordEquiv_eq_of_projective g h hg)
  · intro g h
    apply (AffineAlgebraicGroup.groupHomEquiv P.spin P.spin).injective
    apply NatTrans.ext
    funext R
    apply GrpCat.ext
    intro a
    let a' : Points P.spin.val.X R := a
    change a' ≫ (spinSchemeAction P (g * h)).hom.hom.hom =
      a' ≫ (spinSchemeAction P h).hom.hom.hom ≫ (spinSchemeAction P g).hom.hom.hom
    rw [← Category.assoc, spinSchemeAction_points, spinSchemeAction_points, spinSchemeAction_points]
    exact spinActionPoint_mul P R g h a'
  · intro R g a z j f hz
    rw [spinSchemeAction_points, spinActionPoint_formula]
    congr 2
    exact spinEvenPoint_eq P R a z hz
  · intro R g a h gR hh
    rw [spinSchemeAction_points]
    exact spinActionPoint_vector P R g a hh
  · intro R g a
    let x := a ≫ P.kernel.inclusion.hom.hom
    let u' := (P.kernelPoints R a).val
    let z := Units.map (algebraMap R (R ⊗[k] even form)).toMonoidHom u'
    have hz : evenInclusion R z = P.spinPoints R x := by
      apply Units.ext
      change evenTensorInclusion form R (algebraMap R (R ⊗[k] even form) (u' : R)) = (P.spinPoints R x).val
      exact ((evenTensorInclusion form R).commutes _).trans (P.scalar R a).symm
    have hu : evenAction R g z = z := by
      apply Units.ext
      exact (Algebra.TensorProduct.map (AlgHom.id R R) (evenCliffordEquiv g).toAlgHom).commutes (u' : R)
    change x ≫ (spinSchemeAction P g).hom.hom.hom = x
    rw [spinSchemeAction_points]
    apply (P.spinRepresents.1 R).1
    rw [spinActionPoint_formula, spinEvenPoint_eq P R x z hz, hu, hz]


end

end SplitProjectiveSpinAction

section OrthogonalModel

open MulOpposite
open Specs.SymplecticDivisionForms (AntiEquiv Involution dagger extendAnti
  hermitianValue intoTensor tensorMap)

open private anti_gram transportAnti matrixAnti nonempty_presentation matrix_card_eq
  extendEquiv scalarMatrixBaseChange scalar_gram_base_change from
  LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

set_option maxHeartbeats 500000 in
private theorem symmetric_of_adjoint_equiv
    {K : Type u} {I J : Type} [Field K] [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J]
    (E : Matrix I I K ≃ₐ[K] Matrix J J K) (H : (Matrix I I K)ˣ) (G : (Matrix J J K)ˣ)
    (hG : G.val.transpose = G.val)
    (hE : ∀ X, E (gramAdjoint H X) = gramAdjoint G (E X)) :
    H.val.transpose = H.val := by
  let p := Fintype.equivOfCardEq (matrix_card_eq E.toLinearEquiv)
  let re := Matrix.reindexAlgEquiv K K p
  let G' := Units.map re.symm.toMonoidHom G
  let E' := E.trans re.symm
  have hre (X : Matrix J J K) : (re.symm X).transpose = re.symm X.transpose := rfl
  have hg' : G'.val.transpose = G'.val := by
    change (re.symm G.val).transpose = re.symm G.val
    rw [hre, hG]
  have he' (X : Matrix I I K) : E' (gramAdjoint H X) = gramAdjoint G' (E' X) := by
    change re.symm (E (gramAdjoint H X)) = _
    rw [hE, gramAdjoint, map_mul, map_mul, ← hre]
    rfl
  have hCSA : RM03.CSA.IsCentralSimple K (Matrix I I K) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨U, hU⟩ := RM03.CSA.algEquiv_isInner hCSA E'
  let C := U.val.transpose * G'.val * U.val
  have hC : C.transpose = C := by
    simp [C, transpose_mul, hg', mul_assoc]
  have hComm (Y : Matrix I I K) : (C * H.inv) * Y = Y * (C * H.inv) := by
    have h := he' Y.transpose
    simp only [hU, gramAdjoint, transpose_transpose, transpose_mul] at h
    have hUt : U.val.transpose * U.inv.transpose = 1 := by
      rw [← transpose_mul, U.inv_val, transpose_one]
    have hh := congrArg (fun X => U.val.transpose * G'.val * X * U.val * H.inv) h
    have hUinv : U.inv * U.val = 1 := U.inv_val
    have hGinv : G'.val * G'.inv = 1 := G'.val_inv
    have hHinv : H.val * H.inv = 1 := H.val_inv
    change U.val.transpose * G'.val * (U.val * (H.inv * Y * H.val) * U.inv) * U.val * H.inv =
      U.val.transpose * G'.val * (G'.inv * (U.inv.transpose * (Y * U.val.transpose)) * G'.val) *
        U.val * H.inv at hh
    simp only [mul_assoc] at hh
    rw [← mul_assoc U.inv U.val, hUinv, one_mul, hHinv, mul_one,
      ← mul_assoc G'.val G'.inv, hGinv, one_mul,
      ← mul_assoc U.val.transpose U.inv.transpose, hUt, one_mul] at hh
    simpa only [C, mul_assoc] using hh
  have hUnit : IsUnit (C * H.inv) :=
    ((((Matrix.isUnit_transpose U.val).mpr U.isUnit).mul G'.isUnit).mul U.isUnit).mul
      (H⁻¹).isUnit
  have hCenter : C * H.inv ∈ Subalgebra.center K (Matrix I I K) := by
    rw [Subalgebra.mem_center_iff]
    exact fun Y => (hComm Y).symm
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hCenter)
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    exact not_isUnit_zero (hc.symm ▸ hUnit)
  have hCH : C = c • H.val := by
    rw [Algebra.smul_def, hc, mul_assoc, H.inv_val, mul_one]
  have h := hC
  rw [hCH, transpose_smul] at h
  simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using congrArg (c⁻¹ • ·) h

theorem fieldOrthogonalModel :
    FieldOrthogonalModel.{u} := by
  intro F A _ _ _ r h₂ hA s ⟨d, eL, G, hG, hsplit⟩ e
  let : IsSimpleRing A := hA.1
  let : Nonempty (Fin r) := nonempty_presentation e
  let tr := matrixAnti (AlgEquiv.toOpposite F F) (I := Fin r)
  have hCSA : RM03.CSA.IsCentralSimple F (Matrix (Fin r) (Fin r) F) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨H, hH⟩ := anti_gram hCSA (transportAnti e s.anti) tr
  have h (x : A) : e (antiValue s.anti x) = gramAdjoint H (e x) := by
    have hx := hH (e x)
    change e (antiValue s.anti (e.symm (e x))) = gramAdjoint H (e x) at hx
    rwa [e.symm_apply_apply] at hx
  let L := AlgebraicClosure F
  let E : (L ⊗[F] A) ≃ₐ[L] Matrix (Fin r) (Fin r) L :=
    (extendEquiv e).trans (scalarMatrixBaseChange (Fin r))
  let HL := Units.map (algebraMap F L).mapMatrix.toMonoidHom H
  have he (x : L ⊗[F] A) :
      E (antiValue (extendAnti s.anti L) x) = gramAdjoint HL (E x) :=
    scalar_gram_base_change s.anti e H h x
  have hHL : HL.val.transpose = HL.val := by
    apply symmetric_of_adjoint_equiv (E.symm.trans eL) HL G hG
    intro Y
    obtain ⟨x, rfl⟩ := E.surjective Y
    change eL (E.symm (gramAdjoint HL (E x))) = gramAdjoint G (eL (E.symm (E x)))
    rw [← he, E.symm_apply_apply, E.symm_apply_apply, hsplit]
  have hSym : H.val.transpose = H.val := by
    ext i j
    exact (algebraMap F L).injective (congrArg (fun X : Matrix (Fin r) (Fin r) L => X i j) hHL)
  let B : LinearMap.BilinMap F (Fin r → F) F := Matrix.toLinearMap₂' F H.val
  let q : QuadraticForm F (Fin r → F) := ((2 : F)⁻¹) • B.toQuadraticMap
  have hB (x y : Fin r → F) : B y x = B x y := by
    simp only [B, Matrix.toLinearMap₂'_apply']
    rw [← dotProduct_transpose_mulVec (x := y) (y := x), hSym, dotProduct_comm]
  have hq : q.polarBilin = B := by
    apply LinearMap.ext₂
    intro x y
    change QuadraticMap.polar (fun z => (2 : F)⁻¹ * B z z) x y = B x y
    simp only [QuadraticMap.polar, map_add, LinearMap.add_apply]
    rw [hB x y]
    calc
      _ = ((2 : F)⁻¹ * 2) * B x y := by ring
      _ = _ := by rw [inv_mul_cancel₀ h₂, one_mul]
  refine ⟨H, q, hSym, hq, ?_, h⟩
  rw [hq]
  exact LinearMap.nondegenerate_toLinearMap₂'_of_det_ne_zero'
    (isUnit_iff_ne_zero.mp (H.isUnit.map detMonoidHom))

open private matrixBaseChange matrixCoordinates_pure matrixBaseChange_natural
  quaternion_gram_base_change quaternion_point_compare split_block_dagger
  split_quaternion_anti blockPlane blockPlane_transpose extendAnti_tmul
  hermitianValue_rev hermitianValue_nondegenerate from
  LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

open private hermitianValue_pairing from
  LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

private theorem skewHermitian_of_gram
    {F : Type u} {B : Type v} {I : Type} [Field F] [DivisionRing B] [Algebra F B]
    [Fintype I] [DecidableEq I] (b : Involution F B) (H : (Matrix I I B)ˣ)
    (hH : dagger b.anti H.val = -H.val) :
    ∃ h : SkewHermitianPairing (V := I → B) b, h.value = hermitianValue b.anti H.val := by
  refine ⟨{
    value := hermitianValue b.anti H.val
    add_right := fun x y z => by simp [hermitianValue, mulVec_add, dotProduct_add]
    smul_right := fun x y a => ?_
    skew := fun x y => ?_
    nondegenerate := hermitianValue_nondegenerate b.anti H }, rfl⟩
  · have h (i : I) : (H.val *ᵥ (fun j => y j * a)) i = (H.val *ᵥ y) i * a := by
      simp [mulVec, dotProduct, Finset.sum_mul, mul_assoc]
    change hermitianValue b.anti H.val x (fun j => y j * a) = _
    simp [hermitianValue, h, dotProduct, Finset.sum_mul, mul_assoc]
  · rw [hermitianValue_rev b.anti b.square, hH]
    simp [hermitianValue, neg_mulVec, dotProduct_neg]

set_option maxHeartbeats 500000 in
theorem quaternionSkewModel :
    QuaternionSkewModel.{u} := by
  intro F A B _ _ _ _ _ r h₂ hA s
    ⟨d, eL, G, hG, hsplit⟩ hB hd e
  let : IsSimpleRing A := hA.1
  let : Nonempty (Fin r) := nonempty_presentation e
  let : Algebra.IsCentral F B := hB.2.1
  let : FiniteDimensional F B := hB.2.2
  obtain ⟨bar, hbar, hsq, hadj, _⟩ := SymplecticInvolutionModels.quaternionConjugation.{u,u,u} hB hd
  let b : Involution F B := ⟨bar, hsq⟩
  have hCSA : RM03.CSA.IsCentralSimple F (Matrix (Fin r) (Fin r) B) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨H, hH⟩ := anti_gram hCSA (transportAnti e s.anti) (matrixAnti b.anti)
  have h (x : A) : e (antiValue s.anti x) = H.inv * dagger b.anti (e x) * H.val := by
    have hx := hH (e x)
    change e (antiValue s.anti (e.symm (e x))) = H.inv * dagger b.anti (e x) * H.val at hx
    rwa [e.symm_apply_apply] at hx
  let L := AlgebraicClosure F
  obtain ⟨eB'⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hB
  let eB : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L := hd ▸ eB'
  let E (R : Type u) [CommRing R] [Algebra F R] :
      (R ⊗[F] A) ≃ₐ[R] Matrix (Fin r) (Fin r) (R ⊗[F] B) :=
    (extendEquiv e).trans (matrixBaseChange (Fin r))
  let cflat := Matrix.compAlgEquiv (Fin r) (Fin 2) L L
  let W := eB.mapMatrix.trans cflat
  let T := (eB.restrictScalars F).toAlgHom.comp (intoTensor L B)
  let Tflat := (cflat.restrictScalars F).toAlgHom.comp T.mapMatrix
  let J := blockPlane L (Fin r)
  have hflat (X : Matrix (Fin r) (Fin r) (L ⊗[F] B)) :
      W (dagger (extendAnti b.anti L) X) = gramAdjoint J (W X) :=
    split_block_dagger _ eB (split_quaternion_anti b eB (hadj L eB)) X
  have hflat' (X : Matrix (Fin r) (Fin r) B) :
      Tflat (dagger b.anti X) = gramAdjoint J (Tflat X) := by
    have hx := hflat (X.map (intoTensor L B))
    change W (dagger (extendAnti b.anti L) (X.map (intoTensor L B))) =
      gramAdjoint J (Tflat X) at hx
    have heq : dagger (extendAnti b.anti L) (X.map (intoTensor L B)) =
        (dagger b.anti X).map (intoTensor L B) := by
      ext i j
      exact extendAnti_tmul b.anti (1 : L) (X j i)
    rw [heq] at hx
    exact hx
  let H' := J * Units.map Tflat.toMonoidHom H
  let E' := (E L).trans W
  have hE' (x : L ⊗[F] A) :
      E' (antiValue (extendAnti s.anti L) x) = gramAdjoint H' (E' x) := by
    have hx := quaternion_gram_base_change s.anti b.anti e H h x
    change E L (antiValue (extendAnti s.anti L) x) =
      H.inv.map (intoTensor L B) * dagger (extendAnti b.anti L) (E L x) *
        H.val.map (intoTensor L B) at hx
    change W (E L (antiValue (extendAnti s.anti L) x)) = _
    rw [hx, map_mul, map_mul, hflat]
    change Tflat H.inv * (J.inv * (W (E L x)).transpose * J.val) * Tflat H.val =
      (Tflat H.inv * J.inv) * (W (E L x)).transpose * (J.val * Tflat H.val)
    simp only [mul_assoc]
  have hSym : H'.val.transpose = H'.val := by
    apply symmetric_of_adjoint_equiv (E'.symm.trans eL) H' G hG
    intro X
    obtain ⟨x, rfl⟩ := E'.surjective X
    change eL (E'.symm (gramAdjoint H' (E' x))) = gramAdjoint G (eL (E'.symm (E' x)))
    rw [← hE', E'.symm_apply_apply, E'.symm_apply_apply, hsplit]
  have hSkew : dagger b.anti H.val = -H.val := by
    have hT : Function.Injective T := eB.injective.comp
      (Algebra.TensorProduct.includeRight_injective (B := B) (algebraMap F L).injective)
    have hTF : Function.Injective Tflat := by
      intro X Y hXY
      have hXY' : cflat (X.map T) = cflat (Y.map T) := hXY
      ext i j
      exact hT (congrArg (fun M : Matrix (Fin r) (Fin r) (Matrix (Fin 2) (Fin 2) L) =>
        M i j) (cflat.injective hXY'))
    apply hTF
    rw [hflat', map_neg, gramAdjoint]
    change (J.val * Tflat H.val).transpose = J.val * Tflat H.val at hSym
    rw [transpose_mul, blockPlane_transpose, mul_neg, neg_eq_iff_eq_neg] at hSym
    rw [mul_assoc, hSym, mul_neg, ← mul_assoc, J.inv_val, one_mul]
  obtain ⟨pair, hpair⟩ := skewHermitian_of_gram b H hSkew
  refine ⟨b, H, hbar, hSkew, h, ⟨pair, hpair⟩,
    ⟨E, ?_, ?_, ?_⟩, ?_⟩
  · intro R _ _ x
    exact matrixCoordinates_pure (F := F) (R := R) e x
  · intro R S _ _ _ _ f x
    exact matrixBaseChange_natural f e x
  · intro R _ _ g
    exact quaternion_point_compare (F := F) (R := R) s.anti b.anti H e h g
  · intro cochar hNontrivial
    classical
    have hiso : ∃ x : Fin r → B, x ≠ 0 ∧ hermitianValue b.anti H.val x x = 0 := by
      by_contra! hAnisotropic
      apply hNontrivial
      apply QuaternionHermitianCocharacters.cocharacter_eq_one_of_anisotropic _ _ _ cochar
      rw [← hermitianValue_pairing b.anti]
      exact fun x hx => Classical.byContradiction (fun hn => hAnisotropic x hn hx)
    obtain ⟨x, hx, hxx⟩ := hiso
    have hxx' : pair.value x x = 0 := by rwa [hpair]
    obtain ⟨y, hy⟩ := hyperbolicPartner h₂ b pair x hx hxx'
    rw [hpair] at hy
    exact ⟨x, y, hx, hxx, hy⟩

end OrthogonalModel

section QuadraticPairDescent

open RM03.Brauer.SemilinearDescent (AlgebraAction)
open SymplecticIsometryDescent (Involution)

open private simple_of_scalarExtension from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification

private theorem fixed_matrix_centralSimple
    {k K I : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Fintype I] [DecidableEq I] [Nonempty I] (ρ : AlgebraAction k K (Matrix I I K)) :
    RM03.CSA.IsCentralSimple k ρ.fixedSubalgebra := by
  let : FiniteDimensional k (Matrix I I K) := Module.Finite.trans K _
  let : IsSimpleRing (K ⊗[k] ρ.fixedSubalgebra) :=
    IsSimpleRing.of_ringEquiv ρ.descentEquiv.symm.toRingEquiv inferInstance
  refine ⟨simple_of_scalarExtension (k := k) (K := K), ⟨?_⟩,
    FiniteDimensional.of_injective ρ.fixedSubalgebra.val.toLinearMap Subtype.val_injective⟩
  intro x hx
  have hComm (y : ρ.fixedSubalgebra) : y.val * x.val = x.val * y.val :=
    congrArg Subtype.val (Subalgebra.mem_center_iff.mp hx y)
  have hCenter : x.val ∈ Subalgebra.center K (Matrix I I K) := by
    apply Subalgebra.mem_center_iff.mpr
    intro y
    obtain ⟨t, rfl⟩ := ρ.descentEquiv.surjective y
    induction t using TensorProduct.inductionOn with
    | tmul a y => rw [ρ.descentEquiv_tmul, smul_mul_assoc, mul_smul_comm, hComm]
    | add y z hy hz => rw [map_add, add_mul, mul_add, hy, hz]
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff K).mp hCenter
  have haFixed (g : Gal(K/k)) : g a = a := by
    apply (algebraMap K (Matrix I I K)).injective
    calc
      algebraMap K (Matrix I I K) (g a) = ρ.act g (algebraMap K (Matrix I I K) a) := by
        simp only [Algebra.algebraMap_eq_smul_one, ρ.map_smul, ρ.map_one]
      _ = algebraMap K (Matrix I I K) a := by rw [← ha, x.property g]
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := k) a).mpr haFixed
  refine Algebra.mem_bot.mpr ⟨b, Subtype.ext ?_⟩
  change algebraMap k (Matrix I I K) b = x.val
  rw [IsScalarTower.algebraMap_apply k K, hb, ← ha]

set_option maxHeartbeats 550000 in
theorem quadraticPairDescent :
    QuadraticPairDescent.{u} := by
  intro k K I _ _ _ _ _ _ _ _ ρ hρ
  let J := hyperbolicGram I K
  let L := hyperbolicProjection I K
  have hJT : J.transpose = J := hyperbolicGram_transpose I K
  have hJ : J * J = 1 := hyperbolicGram_square I K
  have hPair (g : Gal(K/k)) :
      ∃ t : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ,
        (∀ X, ρ.act g X = conjugate t (X.map g)) ∧
          PreservesQuadraticPair J L (conjugate t) := by
    obtain ⟨t, c, ht, hc⟩ := hρ g
    have hq (y : I ⊕ I → K) : diagonalValue (J * L) y =
        OddSpinModels.hyperbolicForm I K y := (splitSemitrace_over_ring I K).2.1 y
    refine ⟨t, ht, (conjugate_pair_iff hJT hJ L (hyperbolicProjection_polar I K) t).mpr
      ⟨c, fun x => ?_⟩⟩
    simpa only [hq] using hc x
  have hJM (g : Gal(K/k)) : J.map g = J := by
    simp [J, hyperbolicGram, Matrix.fromBlocks_map]
  have hLM (g : Gal(K/k)) : L.map g = L := by
    simp [L, hyperbolicProjection, Matrix.fromBlocks_map]
  have hAdjM (g : Gal(K/k)) (X : Matrix (I ⊕ I) (I ⊕ I) K) :
      (adjoint J X).map g = adjoint J (X.map g) := by
    simp only [adjoint, Matrix.map_mul, transpose_map, hJM]
  have hAdj (g : Gal(K/k)) (X : Matrix (I ⊕ I) (I ⊕ I) K) :
      ρ.act g (adjoint J X) = adjoint J (ρ.act g X) := by
    obtain ⟨t, ht, h⟩ := hPair g
    rw [ht, ht, hAdjM, h.1]
  let s : Involution k ρ.fixedSubalgebra :=
    { toLinearMap :=
        { toFun := fun x => ⟨adjoint J x.val, fun g => by
            rw [hAdj, x.property g]⟩
          map_add' := fun x y => Subtype.ext (by
            simp only [Subalgebra.coe_add, adjoint, transpose_add, mul_add, add_mul])
          map_smul' := fun a x => Subtype.ext (by
            simp [adjoint]) }
      map_one := Subtype.ext (by change adjoint J 1 = 1; simp [adjoint, hJ])
      map_mul := fun x y => Subtype.ext (adjoint_mul hJ x.val y.val)
      involutive := fun x => Subtype.ext (adjoint_square hJT hJ x.val) }
  have hForm (x : ρ.fixedSubalgebra) :
      (s.toLinearMap x).val = adjoint J x.val := rfl
  have hTraceFixed (x : symmetricPart s) (g : Gal(K/k)) :
      g ((L * x.val.val).trace) = (L * x.val.val).trace := by
    obtain ⟨t, ht, hp⟩ := hPair g
    have hSelf : adjoint J x.val.val = x.val.val := by
      have h := sub_eq_zero.mp (LinearMap.mem_ker.mp x.property)
      exact congrArg Subtype.val h
    have hMapped : x.val.val.map g ∈ selfAdjoint J := by
      change adjoint J (x.val.val.map g) = x.val.val.map g
      rw [← hAdjM, hSelf]
    have h := hp.2 ⟨x.val.val.map g, hMapped⟩
    change (L * conjugate t (x.val.val.map g)).trace = (L * x.val.val.map g).trace at h
    rw [← ht, x.val.property g] at h
    rw [AddMonoidHom.map_trace, Matrix.map_mul, hLM, ← h]
  have hLift (x : symmetricPart s) : ∃ t : k, algebraMap k K t = (L * x.val.val).trace :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := k) _).mpr (hTraceFixed x)
  classical
  let τ : symmetricPart s →ₗ[k] k :=
    { toFun := fun x => (hLift x).choose
      map_add' := fun x y => (algebraMap k K).injective (by
        rw [map_add, (hLift _).choose_spec, (hLift x).choose_spec, (hLift y).choose_spec]
        simp [mul_add])
      map_smul' := fun a x => (algebraMap k K).injective (by
        simp only [RingHom.id_apply, smul_eq_mul, map_mul, (hLift _).choose_spec]
        change (L * (a • x.val.val)).trace = _
        rw [Matrix.mul_smul, trace_smul, Algebra.smul_def]) }
  have hC := fixed_matrix_centralSimple ρ
  let E := ρ.descentEquiv
  let j := Matrix.reindexAlgEquiv K K (Fintype.equivFin (I ⊕ I))
  have hDeg' : RM03.CSA.degree k ρ.fixedSubalgebra = Fintype.card (I ⊕ I) :=
    RM03.CSA.degree_eq_matrix_size hC (E.trans j)
  have hDeg : RM03.CSA.degree k ρ.fixedSubalgebra = 2 * Fintype.card I := by
    rw [hDeg', Fintype.card_sum, two_mul]
  refine ⟨⟨hC, hDeg, s, τ, hForm, fun x => (hLift x).choose_spec, ?_,
    E, ρ.descentEquiv_tmul, ?_⟩⟩
  · intro x
    have hsum : x + s.toLinearMap x ∈ symmetricPart s := by
      change s.toLinearMap (x + s.toLinearMap x) - (x + s.toLinearMap x) = 0
      rw [map_add, s.involutive, add_comm, sub_self]
    refine ⟨hsum, (algebraMap k K).injective ?_⟩
    have hτ (y : symmetricPart s) : algebraMap k K (τ y) = (L * y.val.val).trace :=
      (hLift y).choose_spec
    rw [hτ]
    have hst := (splitSemitrace_over_ring I K).2.2.1 x.val
    obtain ⟨hs, he⟩ := hst
    change (L * (x.val + adjoint J x.val)).trace = x.val.trace at he
    change (L * (x + s.toLinearMap x).val).trace = _
    rw [Subalgebra.coe_add, hForm, he]
    let Ed : (K ⊗[k] ρ.fixedSubalgebra) ≃ₐ[K]
        Matrix (Fin (RM03.CSA.degree k ρ.fixedSubalgebra)) (Fin (RM03.CSA.degree k ρ.fixedSubalgebra)) K :=
      E.trans (Matrix.reindexAlgEquiv K K ((Fintype.equivFin (I ⊕ I)).trans (finCongr hDeg'.symm)))
    have ht : algebraMap k K (-(RM03.CSA.reducedCharpoly hC x).coeff
        (RM03.CSA.degree k ρ.fixedSubalgebra - 1)) = (Ed (1 ⊗ₜ[k] x)).trace := by
      let : Nonempty (Fin (RM03.CSA.degree k ρ.fixedSubalgebra)) :=
        ⟨⟨0, RM03.CSA.degree_pos hC⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin,
        ← RM03.CSA.reducedCharpoly_map hC x Ed, Polynomial.coeff_map, map_neg]
    change x.val.trace = algebraMap k K (-(RM03.CSA.reducedCharpoly hC x).coeff
      (RM03.CSA.degree k ρ.fixedSubalgebra - 1))
    rw [ht]
    change x.val.trace = (Matrix.reindexAlgEquiv K K _ (E (1 ⊗ₜ[k] x))).trace
    rw [show E (1 ⊗ₜ[k] x) = x.val by simp [E]]
    simp only [Matrix.trace, Matrix.diag, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    exact (Equiv.sum_comp
      ((Fintype.equivFin (I ⊕ I)).trans (finCongr hDeg'.symm)).symm
      (fun i => x.val i i)).symm
  · intro x
    induction x using TensorProduct.inductionOn with
    | tmul a y =>
      rw [Involution.baseChange_tmul, ρ.descentEquiv_tmul, ρ.descentEquiv_tmul, hForm]
      simp [adjoint, J]
    | add y z hy hz => simp only [map_add, hy, hz, adjoint, transpose_add, mul_add, add_mul]

end QuadraticPairDescent

section QuadraticPairScalarExtension

open RM03.Brauer.SemilinearDescent (AlgebraAction)
open SymplecticIsometryDescent (Involution)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open private extendScalarsEquiv extendScalarsEquiv_tmul from
  LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
open private extendEquiv extendEquiv_tmul scalarMatrixBaseChange scalarMatrixBaseChange_tmul
  extendAnti_tmul antiValue_add from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

variable {k K I : Type u} [Field k] [Field K] [Algebra k K]
  [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}

private noncomputable def splitPairAt (D : DescendedQuadraticPair ρ)
    (S : Type u) [CommRing S] [Algebra k S] [Algebra K S] [IsScalarTower k K S] :
    (S ⊗[k] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S :=
  (extendScalarsEquiv (k := k) (K := K) S ρ.fixedSubalgebra).trans
    ((extendEquiv D.splitting).trans (scalarMatrixBaseChange (I ⊕ I)))

private theorem splitPairAt_tmul (D : DescendedQuadraticPair ρ)
    {S : Type u} [CommRing S] [Algebra k S] [Algebra K S] [IsScalarTower k K S]
    (r : S) (x : ρ.fixedSubalgebra) :
    splitPairAt D S (r ⊗ₜ[k] x) = r • x.val.map (algebraMap K S) := by
  simp only [splitPairAt, AlgEquiv.trans_apply, extendScalarsEquiv_tmul, extendEquiv_tmul,
    D.splittingFormula, one_smul, scalarMatrixBaseChange_tmul]

private theorem splitPairAt_involution (D : DescendedQuadraticPair ρ)
    {S : Type u} [CommRing S] [Algebra k S] [Algebra K S] [IsScalarTower k K S]
    (x : S ⊗[k] ρ.fixedSubalgebra) :
    splitPairAt D S ((D.involution.baseChange S).toLinearMap x) =
      adjoint (hyperbolicGram I S) (splitPairAt D S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp [Involution.baseChange_tmul, splitPairAt_tmul, D.involutionFormula, adjoint,
      Matrix.map_mul, Matrix.transpose_map, hyperbolicGram, Matrix.fromBlocks_map]
  | add x y hx hy =>
    simp [hx, hy, adjoint, Matrix.transpose_add, mul_add, add_mul]

theorem quadraticPairScalarExtension :
    QuadraticPairScalarExtension.{u} := by
  intro k K I _ _ _ _ _ ρ D S _ _ _ _
  let A := ρ.fixedSubalgebra
  let J := hyperbolicGram I S
  let L := hyperbolicProjection I S
  let E := splitPairAt D S
  refine ⟨E, splitPairAt_tmul D, splitPairAt_involution D, ?_⟩
  let f : A →ₗ[k] A := D.involution.toLinearMap - LinearMap.id
  let P := LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S f)
  let Q := selfAdjoint J
  have hmap : TensorProduct.AlgebraTensorModule.lTensor S S f =
      (D.involution.baseChange S).toLinearMap - LinearMap.id := by
    ext r
    simp [f]
  have hP (t : S ⊗[k] A) : t ∈ P ↔ E t ∈ Q := by
    change t ∈ LinearMap.ker _ ↔ adjoint J (E t) = E t
    rw [LinearMap.mem_ker, hmap, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rw [← splitPairAt_involution D t, E.injective.eq_iff]
  let l := (symmetricPart D.involution).subtype.baseChange S
  have hRange : P = LinearMap.range l := Module.Flat.ker_lTensor_eq S S f
  let m := (E.toLinearMap.comp l).codRestrict Q fun t =>
    (hP (l t)).mp (hRange ▸ LinearMap.mem_range_self l t)
  have hm : Function.Bijective m := by
    constructor
    · have hl : Function.Injective l := Module.Flat.lTensor_preserves_injective_linearMap
        (symmetricPart D.involution).subtype (symmetricPart D.involution).injective_subtype
      exact fun _ _ he => hl (E.injective (congrArg Subtype.val he))
    · intro y
      obtain ⟨t, ht⟩ := E.surjective y.val
      have h : t ∈ P := (hP t).mpr (ht ▸ y.property)
      obtain ⟨t', ht'⟩ := hRange ▸ h
      exact ⟨t', Subtype.ext ((congrArg E ht').trans ht)⟩
  let T := LinearEquiv.ofBijective m hm
  have hT (t : S ⊗[k] symmetricPart D.involution) :
      (T t).val = E ((symmetricPart D.involution).subtype.baseChange S t) := by
    rfl
  refine ⟨T, hT, ?_⟩
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul r x =>
    change (L * (T (r ⊗ₜ[k] x)).val).trace =
      TensorProduct.AlgebraTensorModule.rid k S S (D.semitrace.baseChange S (r ⊗ₜ[k] x))
    rw [hT, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      TensorProduct.AlgebraTensorModule.rid_tmul]
    rw [Algebra.smul_def (D.semitrace x) r]
    change (L * splitPairAt D S (r ⊗ₜ[k] x.val)).trace = algebraMap k S (D.semitrace x) * r
    rw [splitPairAt_tmul, Matrix.mul_smul, Matrix.trace_smul, IsScalarTower.algebraMap_apply k K S,
      D.semitraceFormula, AddMonoidHom.map_trace, Matrix.map_mul]
    simp [hyperbolicProjection, Matrix.fromBlocks_map, smul_eq_mul, mul_comm, L]
  | add t v ht hv =>
    let τ := semitrace J L
    let ψ := TensorProduct.AlgebraTensorModule.rid k S S
    let τ₀ := D.semitrace.baseChange S
    change τ (T (t + v)) = ψ (τ₀ (t + v))
    rw [T.map_add, τ.map_add, τ₀.map_add, ψ.map_add, ← ht, ← hv]

private theorem descendedPair_isOrthogonal [FiniteDimensional k K] (D : DescendedQuadraticPair ρ) :
    IsOrthogonal (toDivisionInvolution D.involution) := by
  let S := AlgebraicClosure k
  let i : K →ₐ[k] S := IsAlgClosed.lift
  let : Algebra K S := i.toRingHom.toAlgebra
  let : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq fun x => (i.commutes x).symm
  let J := hyperbolicGram I S
  let U : (Matrix (I ⊕ I) (I ⊕ I) S)ˣ :=
    ⟨J, J, hyperbolicGram_square I S, hyperbolicGram_square I S⟩
  let re := Matrix.reindexAlgEquiv S S (Fintype.equivFin (I ⊕ I))
  let E := (splitPairAt D S).trans re
  refine ⟨Fintype.card (I ⊕ I), E, Units.map re.toMonoidHom U, ?_, ?_⟩
  · change re J.transpose = re J
    rw [hyperbolicGram_transpose]
  · intro x
    have he (x : S ⊗[k] ρ.fixedSubalgebra) :
        antiValue (Specs.SymplecticDivisionForms.extendAnti
          (toDivisionInvolution D.involution).anti S) x =
          (D.involution.baseChange S).toLinearMap x := by
      induction x using TensorProduct.inductionOn with
      | tmul r x =>
        rw [extendAnti_tmul, Involution.baseChange_tmul]
        rfl
      | add x y hx hy => simp only [antiValue_add, map_add, hx, hy]
    rw [he]
    change re (splitPairAt D S ((D.involution.baseChange S).toLinearMap x)) = _
    rw [splitPairAt_involution D x]
    simp only [adjoint, gramAdjoint, E, AlgEquiv.trans_apply, map_mul]
    rfl

theorem orthogonalInvolutionDescent : OrthogonalInvolutionDescent.{u} := by
  intro k K I _ _ _ _ _ _ _ _ _ ρ hρ
  obtain ⟨D⟩ := quadraticPairDescent k K I ρ hρ
  exact ⟨D, descendedPair_isOrthogonal D⟩

end QuadraticPairScalarExtension

section PairIsometriesAfterSplitting

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs

/-- After splitting, the isometry equations on the fixed algebra recover the
full quadratic isometry condition on every commutative test algebra. -/
theorem pairIsometryScalarExtension : PairIsometryScalarExtension.{u} := by
  intro k K I _ _ _ _ _ _ ρ D R _ _
  let J := hyperbolicGram I R
  let L := hyperbolicProjection I R
  let U := R ⊗[k] symmetricPart D.involution
  let j := (symmetricPart D.involution).subtype.baseChange R
  let τ (x : U) := TensorProduct.AlgebraTensorModule.rid k R R (D.semitrace.baseChange R x)
  obtain ⟨E, hE, hσ, e, he, hτ⟩ := quadraticPairScalarExtension D R
  refine ⟨E, hE, fun a => ?_⟩
  let z := Units.map E.toMonoidHom a
  have hU : (D.involution.baseChange R).toLinearMap a.val * a.val = 1 ↔
      adjoint J z.val * z.val = 1 := by
    have h : E ((D.involution.baseChange R).toLinearMap a.val * a.val) =
        adjoint J z.val * z.val := by
      rw [map_mul, hσ]
      rfl
    exact ⟨fun h₁ => h.symm.trans (by rw [h₁, map_one]),
      fun h₂ => E.injective (h.trans (h₂.trans E.map_one.symm))⟩
  have hComm (hz : adjoint J z.val * z.val = 1) :
      ∀ X, adjoint J (conjugate z X) = conjugate z (adjoint J X) := by
    apply (adjoint_conjugate_iff (hyperbolicGram_transpose I R) (hyperbolicGram_square I R) z).mpr
    refine ⟨1, ?_⟩
    have h := congrArg (J * ·) hz
    have hJ : J * J = 1 := hyperbolicGram_square I R
    change J * ((J * z.val.transpose * J) * z.val) = J * 1 at h
    simp only [← mul_assoc, hJ, one_mul, mul_one] at h
    simpa only [Units.val_one, one_smul] using h
  have hConj (x y : U) : j y = a.val * j x * a.inv ↔ (e y).val = conjugate z (e x).val := by
    rw [he, he, conjugate]
    change j y = a.val * j x * a.inv ↔ E (j y) = E a.val * E (j x) * E a.inv
    rw [← map_mul, ← map_mul, E.injective.eq_iff]
  have hPair (hz : adjoint J z.val * z.val = 1) :
      (∀ x : U, ∃ y : U, j y = a.val * j x * a.inv ∧ τ y = τ x) ↔
      PreservesQuadraticPair J L (conjugate z) := by
    refine ⟨fun h => ⟨hComm hz, ?_⟩, ?_⟩
    · intro X
      obtain ⟨x, rfl⟩ := e.surjective X
      obtain ⟨y, hy, hy'⟩ := h x
      change (L * conjugate z (e x).val).trace = semitrace J L (e x)
      rw [← (hConj x y).mp hy]
      exact (hτ y).trans (hy'.trans (hτ x).symm)
    · intro h x
      let Y : selfAdjoint J := ⟨conjugate z (e x).val, by
        change adjoint J (conjugate z (e x).val) = conjugate z (e x).val
        rw [h.1, show adjoint J (e x).val = (e x).val from (e x).property]⟩
      let y := e.symm Y
      have hy : e y = Y := e.apply_symm_apply _
      refine ⟨y, (hConj x y).mpr (congrArg Subtype.val hy), ?_⟩
      change TensorProduct.AlgebraTensorModule.rid k R R (D.semitrace.baseChange R y) =
        TensorProduct.AlgebraTensorModule.rid k R R (D.semitrace.baseChange R x)
      rw [← hτ y, ← hτ x, hy]
      exact h.2 (e x)
  change ((D.involution.baseChange R).toLinearMap a.val * a.val = 1 ∧ _) ↔ z ∈ orthogonalMatrices I R
  rw [hU, splitPairIsometries I R z]
  exact and_congr_right hPair

end PairIsometriesAfterSplitting

section QuaternionSpinIsotropy

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open Specs.EquivariantUnipotentSeries (onPoints)
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.SymplecticDivisionForms (antiValue extendAnti)
open LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent (Involution tensorMap isometryPoints)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open RM03.Brauer.SemilinearDescent (AlgebraAction)

open private integerPointsIso from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private monomialUnit evaluateUnit evaluateUnit_monomialUnit from
  LinearAlgebraicGroups.Arithmetic.QuaternionHermitianCocharacters
open private groupBaseChangePointIso from LinearAlgebraicGroups.Affine.RationalRepresentations
open private baseChangePoint_map from LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open private quaternionIsometryComparison isometryPointsBaseChange cancelTensorBaseChange
  cancelBaseChange_involution extendAnti_involution from
  LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

open private anti_gram transportAnti matrixAnti extendEquiv scalarMatrixBaseChange
  scalar_gram_base_change nonempty_presentation extendAnti_tmul from
  LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

noncomputable section

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup k} {D : DescendedQuadraticPair ρ}

private def diagonalTorusPoints (F : Type u) [Field F] :
    (groupPointsFunctor F).obj (specGroup (groupAlgebra F IntegerCharacters)) ≅
      StandardGroups.multiplicativePoints F :=
  LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso F IntegerCharacters ≪≫
    integerPointsIso

private def cocharacterOnUnits {F : Type u} [Field F] {H : GroupScheme F}
    (c : Cocharacter H) : StandardGroups.multiplicativePoints F ⟶ (groupPointsFunctor F).obj H :=
  (diagonalTorusPoints F).inv ≫ (groupPointsFunctor F).map c

private theorem cocharacterOnUnits_eq_one {F : Type u} [Field F] {H : GroupScheme F}
    (c : Cocharacter H)
    (h : ∀ (R : TestAlgebra F) (t : Rˣ), (cocharacterOnUnits c).app R t = 1) : c = 0 := by
  apply (groupHomComparison F _ H (by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra F IntegerCharacters)))
    infer_instance)).injective
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro p
  change (p ≫ c.hom.hom) = (p ≫ (0 : Cocharacter H).hom.hom)
  rw [show p ≫ (0 : Cocharacter H).hom.hom = 1 from MonObj.comp_one p]
  let d := diagonalTorusPoints F
  have h' := h R (d.hom.app R p)
  change (d.inv.app R (d.hom.app R p)) ≫ c.hom.hom = 1 at h'
  simpa using h'

private theorem cocharacter_vector_nontrivial (M : SpinModel G D) (F : Type u) [Field F] [Algebra k F]
    (c : Cocharacter ((groupBaseChange k F).obj G.val)) (hc : c ≠ 0) :
    ¬ ∀ (R : TestAlgebra F) (t : Rˣ),
      (cocharacterOnUnits (c ≫ (groupBaseChange k F).map M.projection)).app R t = 1 := by
  intro h
  apply hc
  apply cocharacterOnUnits_eq_one
  let A := CommAlgCat.of F (AddMonoidAlgebra F ℤ)
  let a : Aˣ := monomialUnit (F := F)
  let U := (restrictTestAlgebra k F).obj A
  let z := (cocharacterOnUnits c).app A a
  let y := baseChangePoint k F G.val.X A z
  have hp : y ≫ M.projection.hom.hom = 1 := by
    have hh := h A a
    change onPoints ((groupBaseChange k F).map M.projection) A z = 1 at hh
    change onPoints M.projection ((restrictTestAlgebra k F).obj A)
      (baseChangePoint k F G.val.X A z) = 1
    rw [← baseChangePoint_map F M.projection A z, hh]
    exact (groupBaseChangePointIso F M.neutral.val).hom.app A |>.hom.map_one
  let b : Points M.kernel.group.X U := M.isKernel.lift y (toUnit _) hp
  have hb : b ≫ M.kernel.inclusion.hom.hom = y := M.isKernel.lift_fst _ _ _
  have hMono : Mono M.kernel.inclusion.hom.hom := by
    have : IsClosedImmersion M.kernel.inclusion.hom.hom.left := M.kernel.isClosedImmersion
    exact Over.mono_of_mono_left _
  let f : A ⟶ CommAlgCat.of F F := CommAlgCat.ofHom (evaluateUnit (1 : Fˣ))
  let f₀ := (restrictTestAlgebra k F).map f
  have hf : Units.map f.hom.toMonoidHom a = 1 := evaluateUnit_monomialUnit _
  have hz : mapPoints f z = 1 := by
    have hn := ConcreteCategory.congr_hom ((cocharacterOnUnits c).naturality f) a
    change (cocharacterOnUnits c).app _ (Units.map f.hom.toMonoidHom a) = mapPoints f z at hn
    rw [hf] at hn
    exact hn.symm.trans (((cocharacterOnUnits c).app (CommAlgCat.of F F)).hom.map_one)
  have hy : mapPoints f₀ y = 1 := by
    change mapPoints f₀ ((groupBaseChangePointIso F G.val).hom.app A z) = 1
    have hn := ConcreteCategory.congr_hom ((groupBaseChangePointIso F G.val).hom.naturality f) z
    change (groupBaseChangePointIso F G.val).hom.app _ (mapPoints f z) =
      mapPoints f₀ ((groupBaseChangePointIso F G.val).hom.app A z) at hn
    rw [hz] at hn
    exact hn.symm.trans ((((groupBaseChangePointIso F G.val).hom.app (CommAlgCat.of F F)).hom.map_one))
  have hb₁ : mapPoints f₀ b = 1 := by
    apply (cancel_mono M.kernel.inclusion.hom.hom).mp
    change ((testSpec k).map f₀.op ≫ b) ≫ M.kernel.inclusion.hom.hom = _
    rw [Category.assoc, hb, MonObj.one_comp]
    exact hy
  let w : A := (M.kernelPoints U b).val.val
  have hw₂ : w ^ 2 = 1 := by
    exact congrArg Units.val (M.kernelPoints U b).property
  have hfw : f.hom w = 1 := by
    have h' := M.kernelNatural U _ f₀ b
    rw [hb₁, map_one] at h'
    exact h'.symm
  have hw : w = 1 := by
    rcases eq_or_eq_neg_of_sq_eq_sq w 1 (hw₂.trans (one_pow _).symm : w ^ 2 = (1 : A) ^ 2) with h' | h'
    · exact h'
    · have he : -(1 : F) = 1 := by simpa [h'] using hfw
      rw [h']
      simpa only [map_neg, map_one] using congrArg (algebraMap F A) he
  have hb' : b = 1 := by
    apply (M.kernelPoints U).injective
    rw [map_one]
    exact Subtype.ext (Units.ext hw)
  have hz' : z = 1 := by
    apply (ConcreteCategory.bijective_of_isIso ((groupBaseChangePointIso F G.val).hom.app A)).1
    change y = (groupBaseChangePointIso F G.val).hom.app A 1
    rw [← hb, hb', MonObj.one_comp]
    exact (((groupBaseChangePointIso F G.val).hom.app A).hom.map_one).symm
  intro R t
  let f' : A ⟶ R := CommAlgCat.ofHom (evaluateUnit t)
  have he : Units.map f'.hom.toMonoidHom a = t := evaluateUnit_monomialUnit t
  have h' := ConcreteCategory.congr_hom ((cocharacterOnUnits c).naturality f') a
  change (cocharacterOnUnits c).app R (Units.map f'.hom.toMonoidHom a) = mapPoints f' z at h'
  rw [he, hz'] at h'
  exact h'.trans (map_one (((groupPointsFunctor F).obj ((groupBaseChange k F).obj G.val)).map f').hom)

private def fullIsometryPoints (M : SpinModel G D) :
    (groupPointsFunctor k).obj M.full.val ⟶ isometryPoints D.involution where
  app R := GrpCat.ofHom
    { toFun := fun x => ⟨M.fullPoints R x, ((M.fullRange R _).mp ⟨x, rfl⟩).1⟩
      map_one' := Subtype.ext (map_one (M.fullPoints R))
      map_mul' := fun x y => Subtype.ext (map_mul (M.fullPoints R) x y) }
  naturality R S f := by
    apply GrpCat.ext
    intro x
    exact Subtype.ext (M.fullNatural R S f x)

private def localVectorIsometry (M : SpinModel G D) (F : Type u) [Field F] [Algebra k F] :
    (groupPointsFunctor F).obj ((groupBaseChange k F).obj M.neutral.val) ⟶
      isometryPoints (D.involution.baseChange F) :=
  (groupBaseChangePointIso F M.neutral.val).hom ≫
    Functor.whiskerLeft (restrictTestAlgebra k F) ((groupPointsFunctor k).map M.inclusion ≫
      fullIsometryPoints M) ≫ (isometryPointsBaseChange (F := F) D.involution).inv

private theorem localVectorIsometry_injective (M : SpinModel G D) (F : Type u) [Field F] [Algebra k F]
    (R : TestAlgebra F) : Function.Injective ((localVectorIsometry M F).app R) := by
  have hInc : Mono M.inclusion.hom.hom := by
    have := M.openImmersion
    exact Over.mono_of_mono_left _
  intro a b h
  apply (ConcreteCategory.bijective_of_isIso ((groupBaseChangePointIso F M.neutral.val).hom.app R)).1
  apply (cancel_mono M.inclusion.hom.hom).mp
  apply M.fullFaithful ((restrictTestAlgebra k F).obj R)
  exact congrArg Subtype.val ((ConcreteCategory.bijective_of_isIso
    ((isometryPointsBaseChange (F := F) D.involution).inv.app R)).1 h)

private theorem orthogonal_if_split_symmetric
    {F A L S : Type u} {J : Type} [Field F] [Ring A] [Algebra F A] [Field L] [Algebra F L]
    [Field S] [Algebra F S] [Algebra L S] [IsScalarTower F L S] [Fintype J] [DecidableEq J]
    (hA : _root_.Specs.RM03.CSA.isCentralSimple F A) (s : Involution F A)
    (eL : (L ⊗[F] A) ≃ₐ[L] Matrix (Fin (_root_.Specs.RM03.CSA.degree F A))
      (Fin (_root_.Specs.RM03.CSA.degree F A)) L)
    (eS : (S ⊗[F] A) ≃ₐ[S] Matrix J J S) (G : (Matrix J J S)ˣ)
    (hG : G.val.transpose = G.val)
    (hS : ∀ x, eS ((s.baseChange S).toLinearMap x) = gramAdjoint G (eS x)) :
    ∃ H : (Matrix (Fin (_root_.Specs.RM03.CSA.degree F A))
        (Fin (_root_.Specs.RM03.CSA.degree F A)) L)ˣ,
      H.val.transpose = H.val ∧
      ∀ x, eL (antiValue (extendAnti (toDivisionInvolution s).anti L) x) = gramAdjoint H (eL x) := by
  let n := _root_.Specs.RM03.CSA.degree F A
  let hC := RM03.CSA.isCentralSimple_baseChange (L := L) hA
  let : IsSimpleRing (L ⊗[F] A) := hC.1
  let : Nonempty (Fin n) := nonempty_presentation eL
  let b := extendAnti (toDivisionInvolution s).anti L
  let hM : RM03.CSA.IsCentralSimple L (Matrix (Fin n) (Fin n) L) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨H, hH⟩ := anti_gram hM (transportAnti eL b)
    (matrixAnti (AlgEquiv.toOpposite L L))
  have hL (x : L ⊗[F] A) : eL (antiValue b x) = gramAdjoint H (eL x) := by
    have h := hH (eL x)
    change eL (antiValue b (eL.symm (eL x))) = gramAdjoint H (eL x) at h
    rwa [eL.symm_apply_apply] at h
  refine ⟨H, ?_, hL⟩
  let U := Units.map (algebraMap L S).mapMatrix.toMonoidHom H
  let E := (extendEquiv eL).trans (scalarMatrixBaseChange (R := S) (Fin n))
  let C := cancelTensorBaseChange (k := F) (F := L) (A := A) S
  have hC' (y : S ⊗[L] (L ⊗[F] A)) :
      C (antiValue (extendAnti b S) y) = (s.baseChange S).toLinearMap (C y) := by
    rw [← cancelBaseChange_involution s S y]
    congr 1
    induction y using TensorProduct.inductionOn with
    | tmul a x =>
      rw [extendAnti_tmul, Involution.baseChange_tmul]
      exact congrArg (fun z => a ⊗ₜ[L] z) (extendAnti_involution s L x)
    | add x y hx hy =>
      change MulOpposite.unop ((extendAnti b S) (x + y)) =
        ((s.baseChange L).baseChange S).toLinearMap (x + y)
      rw [map_add, MulOpposite.unop_add, map_add]
      exact congrArg₂ (· + ·) hx hy
  have hU : U.val.transpose = U.val := by
    apply symmetric_of_adjoint_equiv (E.symm.trans (C.trans eS)) U G hG
    intro m
    obtain ⟨y, rfl⟩ := E.surjective m
    have h := scalar_gram_base_change b eL H hL y
    change E (antiValue (extendAnti b S) y) = gramAdjoint U (E y) at h
    change eS (C (E.symm (gramAdjoint U (E y)))) = gramAdjoint G (eS (C (E.symm (E y))))
    rw [← h, E.symm_apply_apply, E.symm_apply_apply, hC', hS]
  ext i j
  exact (algebraMap L S).injective (congrArg (fun X : Matrix (Fin n) (Fin n) S => X i j) hU)

private theorem localOrthogonal (D : DescendedQuadraticPair ρ) (F : Type u) [Field F] [Algebra k F] :
    IsOrthogonal (toDivisionInvolution (D.involution.baseChange F)) := by
  let L := AlgebraicClosure F
  let A := ρ.fixedSubalgebra
  let T := L ⊗[k] K
  let : Nontrivial T := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k L K
    (algebraMap k K).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  let S := T ⧸ m
  let : Field S := Ideal.Quotient.field m
  let i : K →ₐ[k] S := (Ideal.Quotient.mkₐ k m).comp Algebra.TensorProduct.includeRight
  let : Algebra K S := i.toRingHom.toAlgebra
  let : IsScalarTower k K S := IsScalarTower.of_algHom i
  let hF := RM03.CSA.isCentralSimple_baseChange (L := F) D.centralSimple
  obtain ⟨eL⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hF
  let J := hyperbolicGram I S
  let H : (Matrix (I ⊕ I) (I ⊕ I) S)ˣ := ⟨J, J, hyperbolicGram_square I S, hyperbolicGram_square I S⟩
  let re := Matrix.reindexAlgEquiv S S (Fintype.equivFin (I ⊕ I))
  let U := Units.map re.toMonoidHom H
  let E := (cancelTensorBaseChange (k := k) (F := F) (A := A) S).trans ((splitPairAt D S).trans re)
  have hU : U.val.transpose = U.val := by
    change re J.transpose = re J
    rw [hyperbolicGram_transpose]
  have hE (x : S ⊗[F] (F ⊗[k] A)) :
      E (((D.involution.baseChange F).baseChange S).toLinearMap x) = gramAdjoint U (E x) := by
    change re (splitPairAt D S (cancelTensorBaseChange S
        (((D.involution.baseChange F).baseChange S).toLinearMap x))) = _
    rw [cancelBaseChange_involution, splitPairAt_involution]
    simp only [adjoint, gramAdjoint, E, AlgEquiv.trans_apply, map_mul]
    rfl
  obtain ⟨H', hH', hsplit⟩ := orthogonal_if_split_symmetric hF (D.involution.baseChange F)
    eL E U hU hE
  exact ⟨_, eL, H', hH', hsplit⟩

private def unliftMultiplicativePoints (F : Type u) [Field F] :
    QuaternionHermitianCocharacters.multiplicativePoints.{u,u} F ⟶
      StandardGroups.multiplicativePoints F where
  app R := GrpCat.ofHom
    { toFun := ULift.down
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  naturality _ _ _ := by
    apply GrpCat.ext
    intro x
    rfl

/-- The vector morphism sends a nontrivial split cocharacter to the quaternionic
isometry group, giving an isotropic vector and a hyperbolic partner. -/
theorem quaternionSpinIsotropy : QuaternionSpinIsotropy.{u} := by
  intro k K I _ _ _ _ _ ρ G D M F _ _ h₂ B _ _ hB hd r e ⟨c, hc⟩
  let s := D.involution.baseChange F
  have hA := RM03.CSA.isCentralSimple_baseChange (L := F) D.centralSimple
  obtain ⟨b, H, hbar, hskew, hAdj, ⟨h, hh⟩, ⟨E, _, hNat, hEq⟩, hIso⟩ :=
    quaternionSkewModel r h₂ hA (toDivisionInvolution s) (localOrthogonal D F) hB hd e
  let v := cocharacterOnUnits (c ≫ (groupBaseChange k F).map M.projection)
  let q := quaternionIsometryComparison s b.anti H.val E hEq hNat
  let z := unliftMultiplicativePoints F ≫ v ≫ localVectorIsometry M F ≫ q.hom
  have hNontrivial : ¬ ∀ R t, z.app R t = 1 := by
    intro hz
    apply cocharacter_vector_nontrivial M F c hc
    intro R t
    have hq : q.hom.app R ((localVectorIsometry M F).app R (v.app R t)) = 1 := hz R ⟨t⟩
    have hq' := (ConcreteCategory.bijective_of_isIso (q.hom.app R)).1
      (hq.trans ((q.hom.app R).hom.map_one).symm)
    exact localVectorIsometry_injective M F R
      (hq'.trans (((localVectorIsometry M F).app R).hom.map_one).symm)
  obtain ⟨x, y, hx, hxx, hxy, hyx, hyy⟩ := hIso z hNontrivial
  rw [← hh] at hxx hxy hyx hyy
  exact ⟨b, H, h, x, y, hbar, hskew, hAdj, hh, hx, hxx, hxy, hyx, hyy⟩

end

end QuaternionSpinIsotropy

section SplitDiagonalTorus

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Albert.SplitSpinSpecification
open LinearAlgebraicGroups.Albert

open private IsTensorLift IsTensorLift.mul IsTensorLift.mem_spin action_matrix_unique
  tensor_ratio splitScalarUnit splitScalarUnit_injective splitScalarUnit_natural tensor_scalar_lift
  factorUnit factorUnit_lift factorUnit_natural factorUnit_congr from LinearAlgebraicGroups.Albert.SplitSpin
open private scalar_tensor_injective from LinearAlgebraicGroups.Albert.SpinFunctor
open private exponentEvaluation exponentsEquiv from LinearAlgebraicGroups.Affine.StandardGroups
open private mapLiftedTorus spinTorusParameters spinTorusParameters_natural
  orthogonalTorusModel torusPointsToUnits cocharacterCoordinates cocharacterExponents_point
  spinProjection_exponents spinProjection_cocharacter_injective spinTorusProjection_points
  from LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo

noncomputable section

variable {m : ℕ} {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T]

private def diagonalBlock (t : Fin m → Sˣ) : Block m S := diagonal (fun i => ↑(t i))

omit [Algebra ℤ S] in
private theorem diagonalBlock_det (t : Fin m → Sˣ) : (diagonalBlock t).det = ∏ i, (t i : S) :=
  det_diagonal

omit [Algebra ℤ S] in
private theorem diagonalBlock_det_unit (t : Fin m → Sˣ) : IsUnit (diagonalBlock t).det := by
  rw [diagonalBlock_det]
  exact IsUnit.prod_iff.mpr fun i _ => (t i).isUnit

private theorem diagonalBlock_map (f : S →ₐ[ℤ] T) (t : Fin m → Sˣ) :
    (diagonalBlock t).map f = diagonalBlock (fun i => Units.map f.toMonoidHom (t i)) :=
  diagonal_map (map_zero f)

omit [Algebra ℤ S] in
private theorem middle_diagonal (t : Fin m → Sˣ) :
    middle (diagonalBlock t) = diagonal (Sum.elim (fun i => (t i : S)) (fun i => (↑(t i)⁻¹ : S))) := by
  unfold middle diagonalBlock
  rw [inv_diagonal, diagonal_transpose]
  let a : (Fin m → S)ˣ :=
    ⟨fun i => (t i : S), fun i => ((t i)⁻¹ : Sˣ).val,
      funext fun i => (t i).val_inv, funext fun i => (t i).inv_val⟩
  rw [show Ring.inverse (fun i => (t i : S)) = (fun i => (↑(t i)⁻¹ : S)) from Ring.inverse_unit a]
  exact fromBlocks_diagonal _ _

omit [Algebra ℤ S] in
private theorem middle_one : middle (diagonalBlock (1 : Fin m → Sˣ)) = 1 := by
  rw [middle_diagonal]
  rw [← diagonal_one]
  congr 1
  ext i
  cases i <;> simp

omit [Algebra ℤ S] in
private theorem middle_diagonal_mul (t s : Fin m → Sˣ) :
    middle (diagonalBlock (t * s)) = middle (diagonalBlock t) * middle (diagonalBlock s) := by
  simp only [middle_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> simp [mul_comm]

omit [Algebra ℤ S] in
private theorem zero_lower : lower (0 : Block m S) = 1 := by simp [lower]
omit [Algebra ℤ S] in
private theorem zero_upper : upper (0 : Block m S) = 1 := by simp [upper]

private def diagonalMiddleLift (t : Fin m → Sˣ) : (ScalarClifford m S)ˣ :=
  factorUnit 0 0 (diagonalBlock t) (diagonalBlock_det_unit t)

private theorem diagonalMiddleLift_spec (t : Fin m → Sˣ) :
    IsTensorLift (middle (diagonalBlock t)) (diagonalMiddleLift t) (∏ i, (t i : S)) := by
  simpa only [zero_lower, zero_upper, one_mul, mul_one, diagonalBlock_det, diagonalMiddleLift] using
    factorUnit_lift (m := m) 0 0 (diagonalBlock t) (by simp [IsAlternating])
      (by simp [IsAlternating]) (diagonalBlock_det_unit t)

private theorem diagonalMiddleLift_natural (f : S →ₐ[ℤ] T) (t : Fin m → Sˣ) :
    diagonalMiddleLift (fun i => Units.map f.toMonoidHom (t i)) =
      Units.map (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom (diagonalMiddleLift t) := by
  unfold diagonalMiddleLift
  rw [← factorUnit_natural f 0 0 (diagonalBlock t) (diagonalBlock_det_unit t)
    ((diagonalBlock_map f t).symm ▸ diagonalBlock_det_unit _)]
  exact factorUnit_congr (by simp) (by simp) (diagonalBlock_map f t).symm

private theorem lift_difference {M : Matrix (PairIndex m) (PairIndex m) S}
    {a b : (ScalarClifford m S)ˣ} {r : S} (hr : IsUnit r)
    (ha : IsTensorLift M a r) (hb : IsTensorLift M b r) :
    ∃ u : rootsOfUnity 2 S, a = splitScalarUnit u.val * b := by
  obtain ⟨u, hu⟩ := tensor_ratio ha.2.2 hb.2.2
  refine ⟨⟨u, ?_⟩, hu⟩
  have hNorm := (IsTensorLift.mul (tensor_scalar_lift u) hb).2.1
  rw [← hu, ha.2.1] at hNorm
  have h := scalar_tensor_injective (integralForm m) S (hyperbolicBasis ℤ m) hNorm
  apply Units.ext
  change (u : S) ^ 2 = 1
  exact hr.mul_right_cancel (h.symm.trans (one_mul _).symm)

private def normalizedMiddleLift (t : Fin m → Sˣ) : (ScalarClifford m S)ˣ :=
  diagonalMiddleLift t * (diagonalMiddleLift 1)⁻¹

private theorem normalizedMiddleLift_one :
    normalizedMiddleLift (1 : Fin m → Sˣ) = 1 := mul_inv_cancel _

private theorem normalizedMiddleLift_spec (t : Fin m → Sˣ) :
    IsTensorLift (middle (diagonalBlock t)) (normalizedMiddleLift t) (∏ i, (t i : S)) := by
  have h₀ : IsTensorLift (1 : Matrix (PairIndex m) (PairIndex m) S)
      (diagonalMiddleLift 1) 1 := by
    simpa only [middle_one, Pi.one_apply, Units.val_one, Finset.prod_const_one] using
      diagonalMiddleLift_spec (1 : Fin m → Sˣ)
  have h₁ : IsTensorLift (1 : Matrix (PairIndex m) (PairIndex m) S) 1 1 := by
    simpa only [splitScalarUnit, map_one, Units.val_one, one_pow] using
      tensor_scalar_lift (m := m) (1 : Sˣ)
  obtain ⟨u, hu⟩ := lift_difference isUnit_one h₀ h₁
  have h := tensor_scalar_lift (m := m) u.val⁻¹
  have hpow : (↑u.val⁻¹ : S) ^ 2 = 1 := by
    change ((u.val⁻¹ ^ 2 : Sˣ) : S) = 1
    rw [inv_pow, u.property, inv_one, Units.val_one]
  have hi : IsTensorLift (1 : Matrix (PairIndex m) (PairIndex m) S) (diagonalMiddleLift 1)⁻¹ 1 := by
    rw [hu, mul_one, ← show splitScalarUnit (m := m) u.val⁻¹ =
      (splitScalarUnit u.val)⁻¹ from map_inv _ _]
    simpa only [hpow] using h
  simpa only [normalizedMiddleLift, mul_one] using (IsTensorLift.mul (diagonalMiddleLift_spec t) hi)

private theorem normalizedMiddleLift_natural (f : S →ₐ[ℤ] T) (t : Fin m → Sˣ) :
    normalizedMiddleLift (fun i => Units.map f.toMonoidHom (t i)) =
      Units.map (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom (normalizedMiddleLift t) := by
  unfold normalizedMiddleLift
  rw [diagonalMiddleLift_natural, map_mul, map_inv]
  congr 2
  rw [← diagonalMiddleLift_natural]
  congr 1
  funext i
  exact (Units.map f.toMonoidHom).map_one.symm

private def diagonalVariables (J : Type u) [DecidableEq J] :
    J → (AddMonoidAlgebra ℤ (J → ℤ))ˣ :=
  fun i => (AddMonoidAlgebra.of ℤ (J → ℤ)).toHomUnits (Multiplicative.ofAdd (Pi.single i 1))

private def evaluateDiagonals {J : Type u} [Fintype J] {R : Type u} [CommRing R] [Algebra ℤ R]
    (t : J → Rˣ) : AddMonoidAlgebra ℤ (J → ℤ) →ₐ[ℤ] R :=
  AddMonoidAlgebra.lift ℤ R _ ((Units.coeHom R).comp (exponentEvaluation t))

private theorem evaluateDiagonals_variable {J : Type u} [Fintype J] [DecidableEq J]
    {R : Type u} [CommRing R] [Algebra ℤ R] (t : J → Rˣ) (i : J) :
    Units.map (evaluateDiagonals t).toMonoidHom (diagonalVariables J i) = t i := by
  apply Units.ext
  change evaluateDiagonals t (AddMonoidAlgebra.single (Pi.single i 1) 1) = _
  rw [evaluateDiagonals, AddMonoidAlgebra.lift_single]
  simp only [Algebra.smul_def, map_one, one_mul, MonoidHom.comp_apply, Units.coeHom_apply]
  exact congrArg Units.val (congrFun ((@exponentsEquiv J _ _ R _).apply_symm_apply t) i)

set_option maxHeartbeats 800000 in
private theorem normalizedMiddleLift_mul {R : Type u} [CommRing R] [Algebra ℤ R] (t s : Fin m → Rˣ) :
    normalizedMiddleLift (t * s) = normalizedMiddleLift t * normalizedMiddleLift s := by
  let J := ULift.{u} (Fin m ⊕ Fin m)
  let A := AddMonoidAlgebra ℤ (J → ℤ)
  let x : Fin m → Aˣ := fun i => diagonalVariables J (ULift.up (.inl i))
  let y : Fin m → Aˣ := fun i => diagonalVariables J (ULift.up (.inr i))
  have h₀ := normalizedMiddleLift_spec (x * y)
  have h₁ := IsTensorLift.mul (normalizedMiddleLift_spec x) (normalizedMiddleLift_spec y)
  rw [← middle_diagonal_mul, ← Finset.prod_mul_distrib] at h₁
  obtain ⟨a, ha⟩ := lift_difference (by exact IsUnit.prod_iff.mpr fun i _ => ((x * y) i).isUnit) h₀ h₁
  have hGeneric : normalizedMiddleLift (x * y) = normalizedMiddleLift x * normalizedMiddleLift y := by
    let f : A →ₐ[ℤ] ℤ := AddMonoidAlgebra.lift ℤ ℤ _ 1
    have hfvar (i : J) : Units.map f.toMonoidHom (diagonalVariables J i) = 1 := by
      apply Units.ext
      change f (AddMonoidAlgebra.single (Pi.single i 1) 1) = 1
      unfold f
      rw [AddMonoidAlgebra.lift_single]
      simp
    have hx : (fun i => Units.map f.toMonoidHom (x i)) = 1 := funext fun i => hfvar _
    have hy : (fun i => Units.map f.toMonoidHom (y i)) = 1 := funext fun i => hfvar _
    have hxy : (fun i => Units.map f.toMonoidHom ((x * y) i)) = 1 := by
      funext i
      change Units.map f.toMonoidHom (x i * y i) = 1
      rw [map_mul, congrFun hx i, congrFun hy i, Pi.one_apply, one_mul]
    have hf := congrArg (Units.map (SpinSpecification.coefficientMap (integralForm m) A f).toMonoidHom) ha
    rw [map_mul, map_mul, splitScalarUnit_natural, ← normalizedMiddleLift_natural,
      ← normalizedMiddleLift_natural, ← normalizedMiddleLift_natural, hx, hy, hxy,
      normalizedMiddleLift_one, mul_one, mul_one] at hf
    have he := splitScalarUnit_injective (m := m) (S := ℤ)
      (hf.symm.trans ((Units.map (algebraMap ℤ (ScalarClifford m ℤ)).toMonoidHom).map_one).symm)
    have hsq : (a.val.val : A) ^ 2 = 1 := congrArg Units.val a.property
    have ha' : a.val = 1 := by
      apply Units.ext
      rcases eq_or_eq_neg_of_sq_eq_sq (a.val.val : A) 1 (hsq.trans (one_pow _).symm) with h | h
      · exact h
      · have hv := congrArg Units.val he
        change f (a.val.val : A) = 1 at hv
        rw [h, map_neg, map_one] at hv
        norm_num at hv
    simpa only [ha', splitScalarUnit, map_one, one_mul] using ha
  let values : J → Rˣ := fun i => Sum.elim t s i.down
  let f : A →ₐ[ℤ] R := evaluateDiagonals values
  have hx : (fun i => Units.map f.toMonoidHom (x i)) = t :=
    funext fun i => evaluateDiagonals_variable values (ULift.up (Sum.inl i))
  have hy : (fun i => Units.map f.toMonoidHom (y i)) = s :=
    funext fun i => evaluateDiagonals_variable values (ULift.up (Sum.inr i))
  have hxy : (fun i => Units.map f.toMonoidHom ((x * y) i)) = t * s := by
    funext i
    change Units.map f.toMonoidHom (x i * y i) = t i * s i
    rw [map_mul, congrFun hx i, congrFun hy i]
  have hf := congrArg (Units.map (SpinSpecification.coefficientMap (integralForm m) A f).toMonoidHom) hGeneric
  rwa [map_mul, ← normalizedMiddleLift_natural, ← normalizedMiddleLift_natural,
    ← normalizedMiddleLift_natural, hx, hy, hxy] at hf

open Specs.Arithmetic.OddSpinAwayFromTwo (liftTorus)

private def diagonalLiftUnit {R : Type u} [CommRing R] [Algebra ℤ R] :
    liftTorus (R := R) m →* (ScalarClifford m R)ˣ where
  toFun z := splitScalarUnit z.val.2 * normalizedMiddleLift z.val.1
  map_one' := by
    change splitScalarUnit (1 : Rˣ) * normalizedMiddleLift (1 : Fin m → Rˣ) = 1
    rw [normalizedMiddleLift_one, mul_one]
    exact map_one (Units.map (algebraMap R (ScalarClifford m R)).toMonoidHom)
  map_mul' z w := by
    let a := Units.map (algebraMap R (ScalarClifford m R)).toMonoidHom
    change a (z.val.2 * w.val.2) * normalizedMiddleLift (z.val.1 * w.val.1) =
      (a z.val.2 * normalizedMiddleLift z.val.1) * (a w.val.2 * normalizedMiddleLift w.val.1)
    have hc : Commute (a w.val.2) (normalizedMiddleLift z.val.1) := by
      apply Units.ext
      exact Algebra.commutes (w.val.2 : R) _
    rw [map_mul, normalizedMiddleLift_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (a w.val.2), hc.eq, mul_assoc]

private theorem diagonalLiftUnit_spec {R : Type u} [CommRing R] [Algebra ℤ R]
    (z : liftTorus (R := R) m) :
    IsTensorLift (middle (diagonalBlock z.val.1)) (diagonalLiftUnit z) 1 := by
  have h := IsTensorLift.mul (tensor_scalar_lift (m := m) z.val.2) (normalizedMiddleLift_spec z.val.1)
  have hz := congrArg Units.val z.property
  change ((z.val.2 ^ 2 * ∏ i, z.val.1 i : Rˣ) : R) = 1 at hz
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod] at hz
  simpa only [diagonalLiftUnit, MonoidHom.coe_mk, OneHom.coe_mk, one_mul, hz] using h

private theorem diagonalLiftUnit_injective {R : Type u} [CommRing R] [Algebra ℤ R] :
    Function.Injective (diagonalLiftUnit (R := R) (m := m)) := by
  intro z w h
  have he := action_matrix_unique (h ▸ (diagonalLiftUnit_spec z).2.2) (diagonalLiftUnit_spec w).2.2
  have ht : z.val.1 = w.val.1 := by
    funext i
    apply Units.ext
    have hv := congrArg (fun M : Matrix (PairIndex m) (PairIndex m) R => M (.inl i) (.inl i)) he
    simpa only [middle_diagonal, diagonal_apply_eq, Sum.elim_inl] using hv
  have hs : z.val.2 = w.val.2 := by
    apply splitScalarUnit_injective (m := m) (S := R)
    apply mul_right_cancel (b := normalizedMiddleLift w.val.1)
    change splitScalarUnit z.val.2 * normalizedMiddleLift z.val.1 =
      splitScalarUnit w.val.2 * normalizedMiddleLift w.val.1 at h
    rwa [ht] at h
  exact Subtype.ext (Prod.ext ht hs)

private theorem diagonalLiftUnit_of_action {R : Type u} [CommRing R] [Algebra ℤ R]
    (a : (ScalarClifford m R)ˣ) (ha : a ∈ SpinSpecification.spinUnits (integralForm m) R)
    (t : Fin m → Rˣ) (ht : HasActionMatrix m a (middle (diagonalBlock t))) :
    ∃ z : liftTorus (R := R) m, z.val.1 = t ∧ diagonalLiftUnit z = a := by
  have hd := normalizedMiddleLift_spec t
  obtain ⟨u, hu⟩ := tensor_ratio ht hd.2.2
  have hn := (IsTensorLift.mul (tensor_scalar_lift u) hd).2.1
  rw [← hu, ha.2.1] at hn
  have hVal := scalar_tensor_injective (integralForm m) R (hyperbolicBasis ℤ m)
    (hn.symm.trans (map_one _).symm)
  let z : liftTorus (R := R) m := ⟨(t, u), by
    change u ^ 2 * ∏ i, t i = 1
    apply Units.ext
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_one] using hVal⟩
  exact ⟨z, rfl, hu.symm⟩

private theorem diagonalLiftUnit_natural {k : Type u} [Field k] {R S : TestAlgebra k}
    (f : R ⟶ S) (z : liftTorus (R := R) m) :
    let f₀ : R →ₐ[ℤ] S := f.hom.restrictScalars ℤ
    diagonalLiftUnit (mapLiftedTorus m f z) =
      Units.map (SpinSpecification.coefficientMap (integralForm m) R f₀).toMonoidHom (diagonalLiftUnit z) := by
  dsimp only
  let f₀ : R →ₐ[ℤ] S := f.hom.restrictScalars ℤ
  change splitScalarUnit (Units.map f₀.toMonoidHom z.val.2) *
    normalizedMiddleLift (fun i => Units.map f₀.toMonoidHom (z.val.1 i)) =
    Units.map (SpinSpecification.coefficientMap (integralForm m) R f₀).toMonoidHom
      (splitScalarUnit z.val.2 * normalizedMiddleLift z.val.1)
  rw [map_mul, splitScalarUnit_natural, normalizedMiddleLift_natural]

open Specs.Arithmetic.NontrialitarianSpinModels (SplitSpinVectorImage)
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open SpinSpecification (spinUnits IsVectorAction)

section ChangeCoefficients

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]
variable (m : ℕ) (d : Fin m ≃ I)

local notation "qZ" => integralForm m
local notation "qk" => hyperbolicForm I k
local notation "bZ" => hyperbolicBasis ℤ m
local notation "bk" => Pi.basisFun k (I ⊕ I)

private theorem integralCliffordCoordinates_basis (R : TestAlgebra k) (i : Lex (PairIndex m)) :
    integralCliffordCoordinates k I m d R (1 ⊗ₜ[ℤ] CliffordAlgebra.ι qZ (bZ i)) =
      1 ⊗ₜ[k] CliffordAlgebra.ι qk (bk ((d.sumCongr d) (ofLex i))) := by
  let v := integralVectorCoordinates k I m d R
  have hv : v ((bZ).baseChange R i) = (bk).baseChange R ((d.sumCongr d) (ofLex i)) := by
    apply ((bk).baseChange R).equivFun.injective
    funext j
    rw [integralVectorCoordinates_repr, Module.Basis.equivFun_self, Module.Basis.equivFun_self]
    change (if i = toLex ((d.sumCongr d).symm j) then (1 : R) else 0) =
      if (d.sumCongr d) (ofLex i) = j then 1 else 0
    congr 1
    exact propext ((ofLex.trans (d.sumCongr d)).injective.eq_iff.symm.trans (by simp))
  calc
    _ = integralCliffordCoordinates k I m d R (SpinSpecification.vectors qZ R ((bZ).baseChange R i)) := by
      rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
    _ = SpinSpecification.vectors qk R (v ((bZ).baseChange R i)) :=
      integralCliffordCoordinates_vector k I m d R _
    _ = _ := by rw [hv, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]

private theorem integralCliffordCoordinates_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (a : ScalarClifford m R) :
    SpinSpecification.coefficientMap qk R f.hom (integralCliffordCoordinates k I m d R a) =
      integralCliffordCoordinates k I m d S
        (SpinSpecification.coefficientMap qZ R (f.hom.restrictScalars ℤ) a) := by
  let E := integralCliffordCoordinates k I m d R
  let E' := integralCliffordCoordinates k I m d S
  let f₀ := f.hom.restrictScalars ℤ
  let F := SpinSpecification.coefficientMap qZ R f₀
  let F' := SpinSpecification.coefficientMap qk R f.hom
  let α := (F'.restrictScalars ℤ).comp (E.toAlgHom.restrictScalars ℤ)
  let β := (E'.toAlgHom.restrictScalars ℤ).comp F
  suffices h : α = β from AlgHom.congr_fun h a
  apply Algebra.TensorProduct.ext
  · ext r
    change F' (E (algebraMap R _ r)) = E' (F (algebraMap R _ r))
    rw [E.commutes]
    have h₁ : F (algebraMap R _ r) = algebraMap S _ (f.hom r) := by
      simp [F, f₀, SpinSpecification.coefficientMap, Algebra.TensorProduct.algebraMap_apply]
    have h₂ : F' (algebraMap R _ r) = algebraMap S _ (f.hom r) := by
      simp [F', SpinSpecification.coefficientMap, Algebra.TensorProduct.algebraMap_apply]
    rw [h₁, h₂, E'.commutes]
  · apply CliffordAlgebra.hom_ext
    apply (bZ).ext
    intro i
    change F' (integralCliffordCoordinates k I m d R (1 ⊗ₜ[ℤ] CliffordAlgebra.ι qZ (bZ i))) =
      integralCliffordCoordinates k I m d S (F (1 ⊗ₜ[ℤ] CliffordAlgebra.ι qZ (bZ i)))
    rw [integralCliffordCoordinates_basis]
    simp only [F, F', SpinSpecification.coefficientMap, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, map_one, integralCliffordCoordinates_basis]

end ChangeCoefficients

open private closedImmersion_of_injective_test_points from LinearAlgebraicGroups.Classification.RationalRealization
open private vectors_injective from LinearAlgebraicGroups.Albert.SpinFunctor

section SpinDiagonalScheme

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]
variable (P : SplitSpinVectorImage k I) {m : ℕ} (d : Fin (m + 1) ≃ I)

local notation "n" => (m + 1)
local notation "qZ" => integralForm n
local notation "qk" => hyperbolicForm I k
local notation "C" R => integralCliffordCoordinates k I n d R
local notation "T₀" => orthogonalTorusModel (k := k) n

private theorem diagonalSpinPoint_exists (R : TestAlgebra k) (z : liftTorus (R := R) n) :
    ∃ a : Points P.spin.val.X R,
      P.spinPoints R a = Units.map (C R).toMonoidHom (diagonalLiftUnit z) := by
  have h := (integralSpinUnits k I n d R (diagonalLiftUnit z)).mpr
    (IsTensorLift.mem_spin (diagonalLiftUnit_spec z))
  change Units.map (C R).toMonoidHom (diagonalLiftUnit z) ∈ Set.range (P.spinPoints R)
  rwa [(P.spinRepresents.1 R).2]

private def diagonalSpinPoint (R : TestAlgebra k) (z : liftTorus (R := R) n) : Points P.spin.val.X R :=
  (diagonalSpinPoint_exists P d R z).choose

private theorem diagonalSpinPoint_unit (R : TestAlgebra k) (z : liftTorus (R := R) n) :
    P.spinPoints R (diagonalSpinPoint P d R z) = Units.map (C R).toMonoidHom (diagonalLiftUnit z) :=
  (diagonalSpinPoint_exists P d R z).choose_spec

private def diagonalSpinPointHom (R : TestAlgebra k) : liftTorus (R := R) n →* Points P.spin.val.X R where
  toFun := diagonalSpinPoint P d R
  map_one' := (P.spinRepresents.1 R).1 (by rw [diagonalSpinPoint_unit, map_one, map_one, map_one])
  map_mul' z w := (P.spinRepresents.1 R).1 (by
    simp only [diagonalSpinPoint_unit, map_mul])

private theorem diagonalSpinPoint_injective (R : TestAlgebra k) :
    Function.Injective (diagonalSpinPoint P d R) := by
  intro a b h
  apply diagonalLiftUnit_injective
  apply Units.ext
  apply (C R).injective
  have h' := congrArg (P.spinPoints R) h
  rw [diagonalSpinPoint_unit, diagonalSpinPoint_unit] at h'
  exact congrArg Units.val h'

private theorem diagonalSpinPoint_natural {R S : TestAlgebra k} (f : R ⟶ S) (z : liftTorus (R := R) n) :
    diagonalSpinPoint P d S (mapLiftedTorus n f z) = mapPoints f (diagonalSpinPoint P d R z) := by
  apply (P.spinRepresents.1 S).1
  rw [diagonalSpinPoint_unit, P.spinRepresents.2, diagonalSpinPoint_unit, diagonalLiftUnit_natural]
  apply Units.ext
  exact (integralCliffordCoordinates_natural n d f (diagonalLiftUnit z).val).symm

private theorem vectorMatchesIntegralMatrix (R : TestAlgebra k) (a : Points P.spin.val.X R)
    (b : (ScalarClifford n R)ˣ) (hb : P.spinPoints R a = Units.map (C R).toMonoidHom b)
    (M : Matrix (PairIndex n) (PairIndex n) R) :
    HasActionMatrix n b M ↔
      vectorImageMatrix P R (a ≫ P.projection.hom.hom) = Matrix.reindex (d.sumCongr d) (d.sumCongr d) M := by
  rw [integralSpinMatrix k I n d R b M, ← hb]
  obtain ⟨g, hg, hm⟩ := P.vector R a
  change LinearMap.toMatrix ((Pi.basisFun k (I ⊕ I)).baseChange R)
    ((Pi.basisFun k (I ⊕ I)).baseChange R) g.toLinearMap = vectorImageMatrix P R
      (a ≫ P.projection.hom.hom) at hm
  rw [← hm]
  constructor
  · rintro ⟨h, hh, he⟩
    suffices g = h from this.symm ▸ he
    ext x
    apply vectors_injective qk R (Pi.basisFun k (I ⊕ I))
    exact (hg x).trans (hh x).symm
  · intro h
    exact ⟨g, hg, h⟩

private theorem diagonalSpinPoint_matrix (R : TestAlgebra k) (z : liftTorus (R := R) n) :
    vectorImageMatrix P R (diagonalSpinPoint P d R z ≫ P.projection.hom.hom) =
      Matrix.reindex (d.sumCongr d) (d.sumCongr d) (middle (diagonalBlock z.val.1)) :=
  (vectorMatchesIntegralMatrix P d R _ _ (diagonalSpinPoint_unit P d R z) _).mp
    (diagonalLiftUnit_spec z).2.2

private theorem diagonalSpinPoint_of_matrix (R : TestAlgebra k) (a : Points P.spin.val.X R)
    (t : Fin n → Rˣ)
    (ha : vectorImageMatrix P R (a ≫ P.projection.hom.hom) =
      Matrix.reindex (d.sumCongr d) (d.sumCongr d) (middle (diagonalBlock t))) :
    ∃ z : liftTorus (R := R) n, z.val.1 = t ∧ diagonalSpinPoint P d R z = a := by
  let b := Units.map (C R).symm.toMonoidHom (P.spinPoints R a)
  have hb : P.spinPoints R a = Units.map (C R).toMonoidHom b := by
    apply Units.ext
    exact ((C R).apply_symm_apply _).symm
  have hs : b ∈ spinUnits qZ R := (integralSpinUnits k I n d R b).mp
    (hb ▸ ((P.spinRepresents.1 R).2 ▸ Set.mem_range_self a))
  obtain ⟨z, hcoord, hz⟩ := diagonalLiftUnit_of_action b hs t
    ((vectorMatchesIntegralMatrix P d R a b hb _).mpr ha)
  refine ⟨z, hcoord, (P.spinRepresents.1 R).1 ?_⟩
  rw [diagonalSpinPoint_unit, hz, ← hb]

private def diagonalSpinNatural : (groupPointsFunctor k).obj (T₀).val ⟶
    (groupPointsFunctor k).obj P.spin.val where
  app R := GrpCat.ofHom ((diagonalSpinPointHom P d R).comp (spinTorusParameters m R).toMonoidHom)
  naturality R S f := by
    apply GrpCat.ext
    intro a
    change Points (T₀).val.X R at a
    change diagonalSpinPoint P d S (spinTorusParameters m S (mapPoints f a)) =
      mapPoints f (diagonalSpinPoint P d R (spinTorusParameters m R a))
    rw [spinTorusParameters_natural m f a, diagonalSpinPoint_natural]

private def diagonalSpinInclusion : (T₀).val ⟶ P.spin.val :=
  (AffineAlgebraicGroup.groupHomEquiv T₀ P.spin).symm (diagonalSpinNatural P d)

private theorem diagonalSpinInclusion_point (R : TestAlgebra k) (a : Points (T₀).val.X R) :
    a ≫ (diagonalSpinInclusion P d).hom.hom = diagonalSpinPoint P d R (spinTorusParameters m R a) :=
  congrArg (fun τ => τ.app R a) ((AffineAlgebraicGroup.groupHomEquiv T₀ P.spin).apply_symm_apply
    (diagonalSpinNatural P d))

private def splitDiagonalTorus : ClosedSubgroup P.spin.val where
  group := (T₀).val
  inclusion := diagonalSpinInclusion P d
  isClosedImmersion := by
    apply closedImmersion_of_injective_test_points
    intro R a b h
    change a ≫ (diagonalSpinInclusion P d).hom.hom = b ≫ (diagonalSpinInclusion P d).hom.hom at h
    rw [diagonalSpinInclusion_point, diagonalSpinInclusion_point] at h
    exact (spinTorusParameters m R).injective (diagonalSpinPoint_injective P d R h)

private theorem splitDiagonalTorus_isSplit : GeometricRadicals.IsSplitTorus (splitDiagonalTorus P d).group :=
  ⟨n, ⟨Iso.refl _⟩⟩

set_option maxHeartbeats 700000 in
/-- The preimage of the diagonal vector isometries is the split torus with
    the scalar coordinate and the remaining hyperbolic scales. -/
private theorem splitDiagonalTorus_range (R : TestAlgebra k) (a : Points P.spin.val.X R) :
    (∃ b : Points (splitDiagonalTorus P d).group.X R,
      b ≫ (splitDiagonalTorus P d).inclusion.hom.hom = a) ↔
    (∃ t : Fin n → Rˣ, vectorImageMatrix P R (a ≫ P.projection.hom.hom) =
      Matrix.reindex (d.sumCongr d) (d.sumCongr d) (middle (diagonalBlock t))) := by
  constructor
  · rintro ⟨b, rfl⟩
    change Points (T₀).val.X R at b
    change ∃ t : Fin n → Rˣ,
      vectorImageMatrix P R ((b ≫ (diagonalSpinInclusion P d).hom.hom) ≫ P.projection.hom.hom) = _
    rw [diagonalSpinInclusion_point]
    exact ⟨_, diagonalSpinPoint_matrix P d R _⟩
  · rintro ⟨t, ht⟩
    obtain ⟨z, -, hz⟩ := diagonalSpinPoint_of_matrix P d R a t ht
    obtain ⟨b, hb⟩ := (spinTorusParameters m R).surjective z
    refine ⟨b, ?_⟩
    change b ≫ (diagonalSpinInclusion P d).hom.hom = a
    rwa [diagonalSpinInclusion_point, hb]

end SpinDiagonalScheme

open Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo (spinTorusProjection)
open private orthogonalTorusModel_comm cocharacterExponents spinTorusOrthogonalPoints_eval from
  LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo

section SplitTorusLattice

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]
variable (P : SplitSpinVectorImage k I) {m : ℕ} (d : Fin (m + 1) ≃ I)

local notation "n" => (m + 1)
local notation "T₀" => orthogonalTorusModel (k := k) n
local notation "evenSum" => Specs.Arithmetic.OddSpinModels.evenSum

private instance torusComm : IsCommMonObj (splitDiagonalTorus P d).group.X :=
  orthogonalTorusModel_comm (k := k) n

private def torusProjectionLattice (d : Fin n ≃ I) :
    Additive (Cocharacter (T₀).val) →ₗ[ℤ] (I → ℤ) :=
  (LinearEquiv.funCongrLeft ℤ ℤ d.symm).toLinearMap.comp <|
    (cocharacterCoordinates (k := k) n).toLinearMap.comp <|
      AddMonoidHom.toIntLinearMap
        { toFun := fun c => Additive.ofMul (c.toMul ≫ spinTorusProjection m)
          map_zero' := by
            apply Additive.toMul.injective
            apply Grp.hom_ext
            exact MonObj.one_comp (spinTorusProjection (k := k) m).hom.hom
          map_add' := fun a b => by
            apply Additive.toMul.injective
            apply Grp.hom_ext
            exact MonObj.mul_comp a.toMul.hom.hom b.toMul.hom.hom (spinTorusProjection (k := k) m).hom.hom }

omit [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)] in
private theorem torusProjectionLattice_formula (c : Cocharacter (T₀).val) (i : I) :
    torusProjectionLattice (k := k) d (Additive.ofMul c) i =
      cocharacterExponents n (c ≫ spinTorusProjection m) (d.symm i) := rfl

omit [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)] in
private theorem torusProjectionLattice_injective (d : Fin n ≃ I) :
    Function.Injective (torusProjectionLattice (k := k) d) := by
  intro a b h
  apply Additive.toMul.injective
  apply spinProjection_cocharacter_injective m
  apply Additive.ofMul.injective
  apply (cocharacterCoordinates (k := k) n).injective
  funext i
  have e := congrFun h (d i)
  change cocharacterExponents n (a.toMul ≫ spinTorusProjection m) (d.symm (d i)) =
    cocharacterExponents n (b.toMul ≫ spinTorusProjection m) (d.symm (d i)) at e
  change cocharacterExponents n (a.toMul ≫ spinTorusProjection m) i =
    cocharacterExponents n (b.toMul ≫ spinTorusProjection m) i
  simpa only [Equiv.symm_apply_apply] using e

omit [DecidableEq I] [LinearOrder (I ⊕ I)] in
private theorem torusProjectionLattice_range (d : Fin n ≃ I) :
    LinearMap.range (torusProjectionLattice (k := k) d) = evenSum I := by
  have h := spinProjection_exponents (k := k) m
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    let w := cocharacterExponents n (a.toMul ≫ spinTorusProjection m)
    have hw : Even (∑ i, w i) := by
      change w ∈ (Specs.Arithmetic.OddSpinAwayFromTwo.evenSum n : Set (Fin n → ℤ))
      rw [← h]
      exact ⟨a.toMul, rfl⟩
    change Even (∑ i : I, w (d.symm i))
    rwa [d.symm.sum_comp]
  · intro hv
    have h' : (fun i => v (d i)) ∈ Specs.Arithmetic.OddSpinAwayFromTwo.evenSum n := by
      change Even (∑ i, v (d i))
      rwa [d.sum_comp]
    change (fun i => v (d i)) ∈ (Specs.Arithmetic.OddSpinAwayFromTwo.evenSum n : Set (Fin n → ℤ)) at h'
    rw [← h] at h'
    obtain ⟨a, ha⟩ := h'
    refine ⟨Additive.ofMul a, ?_⟩
    funext i
    rw [torusProjectionLattice_formula d a, show cocharacterExponents n (a ≫ spinTorusProjection m)
      (d.symm i) = v (d (d.symm i)) from congrFun ha _ , Equiv.apply_symm_apply]

private def diagonalCocharacterLattice :
    Additive (Cocharacter (splitDiagonalTorus P d).group) ≃ₗ[ℤ] evenSum I :=
  (LinearEquiv.ofInjective _ (torusProjectionLattice_injective (k := k) d)).trans
    (LinearEquiv.ofEq _ _ (torusProjectionLattice_range (k := k) d))

omit [Fintype I] [LinearOrder (I ⊕ I)] in
private theorem reindex_middle_diagonal {R : Type u} [CommRing R] (t : Fin n → Rˣ) :
    Matrix.reindex (d.sumCongr d) (d.sumCongr d) (middle (diagonalBlock t)) =
      Specs.SymplecticMatrixStructure.hyperbolicDiagonal (fun i => t (d.symm i)) := by
  rw [middle_diagonal, Specs.SymplecticMatrixStructure.hyperbolicDiagonal]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal, d.symm.injective.eq_iff]

private theorem diagonalCocharacter_vector (R : TestAlgebra k) (z : Rˣ)
    (c : Cocharacter (splitDiagonalTorus P d).group) :
    let p := cocharacterPoint c R z ≫ (splitDiagonalTorus P d).inclusion.hom.hom
    vectorImageMatrix P R (p ≫ P.projection.hom.hom) =
      Specs.SymplecticMatrixStructure.hyperbolicDiagonal
        (fun i => z ^ ((diagonalCocharacterLattice P d) (Additive.ofMul c)).val i) := by
  dsimp only
  let a : Points (T₀).val.X R := cocharacterPoint c R z
  change vectorImageMatrix P R ((a ≫ (diagonalSpinInclusion P d).hom.hom) ≫ P.projection.hom.hom) = _
  rw [diagonalSpinInclusion_point, diagonalSpinPoint_matrix, reindex_middle_diagonal]
  congr 1
  funext i
  have h := cocharacterExponents_point n (c ≫ spinTorusProjection m) R z (d.symm i)
  change torusPointsToUnits n R (a ≫ (spinTorusProjection (k := k) m).hom.hom) (d.symm i) =
    z ^ (cocharacterExponents n (c ≫ spinTorusProjection m) (d.symm i)) at h
  rw [spinTorusProjection_points, spinTorusOrthogonalPoints_eval] at h
  exact h

end SplitTorusLattice

section DiagonalTorusCentralizer

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped IsMulCommutative
open Specs.SymplecticMatrixStructure (hyperbolicDiagonal IsOwnSchemeCentralizer CentralizesDiagonal)

open private middle_preserves factor_map from LinearAlgebraicGroups.Albert.SplitSpin
open private offDiagonal_eq_zero_of_centralizes from LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure


variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]
variable (P : SplitSpinVectorImage k I) {m : ℕ} (d : Fin (m + 1) ≃ I)

private abbrev spinVectorMatrix (R : TestAlgebra k) (a : Points P.spin.val.X R) :=
  vectorImageMatrix P R (a ≫ P.projection.hom.hom)

omit [LinearOrder (I ⊕ I)] in
private theorem spinVectorMatrix_mul (R : TestAlgebra k) (a b : Points P.spin.val.X R) :
    spinVectorMatrix P R (a * b) = spinVectorMatrix P R a * spinVectorMatrix P R b := by
  change vectorImageMatrix P R ((a * b) ≫ P.projection.hom.hom) = _
  rw [MonObj.mul_comp]
  exact vectorImageMatrix_mul P R _ _

omit [LinearOrder (I ⊕ I)] in
private theorem spinVectorMatrix_map {R S : TestAlgebra k} (f : R ⟶ S) (a : Points P.spin.val.X R) :
    spinVectorMatrix P S (mapPoints f a) = (spinVectorMatrix P R a).map f.hom := by
  simpa only [spinVectorMatrix, Category.assoc] using vectorImageMatrix_map P f (a ≫ P.projection.hom.hom)

omit [Fintype I] [LinearOrder (I ⊕ I)] in
private theorem hyperbolicDiagonal_map {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (t : I → Rˣ) :
    (hyperbolicDiagonal t).map f = hyperbolicDiagonal (fun i => Units.map f.toMonoidHom (t i)) := by
  rw [hyperbolicDiagonal, hyperbolicDiagonal, diagonal_map (map_zero f)]
  congr 1
  funext i
  cases i <;> rfl

private theorem diagonalTorus_lift (R : TestAlgebra k) (t : I → Rˣ) :
    ∃ (S : TestAlgebra k) (f : R ⟶ S), Function.Injective f.hom ∧
      ∃ q : Points (splitDiagonalTorus P d).group.X S,
        spinVectorMatrix P S (q ≫ (splitDiagonalTorus P d).inclusion.hom.hom) =
          (hyperbolicDiagonal t).map f.hom := by
  let v : Fin (m + 1) → Rˣ := t ∘ d
  let M := middle (diagonalBlock v)
  have hdet : IsUnit (diagonalBlock v).det := diagonalBlock_det_unit v
  obtain ⟨_, A, hA, hRA, hZA, _, _, _, hFF, _, ⟨b⟩⟩ :=
    spinChartFibers (m + 1) (Nat.succ_pos _) R M (middle_preserves hdet) hdet
  let : CommRing A := hA
  let : Algebra R A := hRA
  have hInt : hZA = @Ring.toIntAlgebra A hA.toRing := Subsingleton.elim _ _
  subst hZA
  let : Module.FaithfullyFlat R A := hFF
  let : Algebra k A := ((algebraMap R A).comp (algebraMap k R)).toAlgebra
  let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let S : TestAlgebra k := CommAlgCat.of k A
  let f : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R A)
  let C := integralCliffordCoordinates k I (m + 1) d S
  have hSpin : Units.map C.toMonoidHom b.val ∈ spinUnits (hyperbolicForm I k) S :=
    (integralSpinUnits k I (m + 1) d S b.val).mpr b.property.1
  rw [← (P.spinRepresents.1 S).2] at hSpin
  obtain ⟨a, ha⟩ := hSpin
  have hm : spinVectorMatrix P S a =
      Matrix.reindex (d.sumCongr d) (d.sumCongr d) (M.map (algebraMap R S)) :=
    (vectorMatchesIntegralMatrix P d S a b.val ha _).mp b.property.2
  let t' : Fin (m + 1) → Sˣ := fun i => Units.map f.hom.toMonoidHom (v i)
  have hM : M.map (algebraMap R S) = middle (diagonalBlock t') := by
    have h := factor_map (algebraMap R S) (0 : Block (m + 1) R) 0 (diagonalBlock v) hdet
    simp only [zero_lower, zero_upper, Matrix.map_zero _ (map_zero (algebraMap R S)),
      one_mul, mul_one] at h
    exact h.trans (congrArg middle (diagonalBlock_map (f.hom.restrictScalars ℤ) v))
  rw [hM] at hm
  obtain ⟨q, hq⟩ := (splitDiagonalTorus_range P d S a).mpr ⟨t', hm⟩
  refine ⟨S, f, FaithfulSMul.algebraMap_injective R A, q, ?_⟩
  rw [hq, hm, reindex_middle_diagonal]
  change hyperbolicDiagonal (fun i => t' (d.symm i)) = (hyperbolicDiagonal t).map f.hom.toRingHom
  rw [hyperbolicDiagonal_map f.hom.toRingHom t]
  congr 1
  funext i
  change Units.map f.hom.toMonoidHom (t (d (d.symm i))) = _
  rw [Equiv.apply_symm_apply]

omit [LinearOrder (I ⊕ I)] in
private theorem orthogonal_eq_hyperbolicDiagonal {R : Type u} [CommRing R]
    (z : orthogonalMatrices I R)
    (hz : ∀ i j, i ≠ j → z.val.val i j = 0) :
    ∃ t : I → Rˣ, z.val.val = hyperbolicDiagonal t := by
  let g := z.val
  let a : I ⊕ I → R := fun i => g.val i i
  have hg : g.val = diagonal a := by
    ext i j
    by_cases h : i = j
    · subst j
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ h]
      exact hz i j h
  let J := hyperbolicGram I R
  have hInv (i : I ⊕ I) : IsUnit (a i) := by
    have h := congrArg (fun M : Matrix (I ⊕ I) (I ⊕ I) R => M i i) g.val_inv
    rw [hg, diagonal_mul, one_apply_eq] at h
    exact ⟨⟨a i, g.inv i i, h, (mul_comm _ _).trans h⟩, rfl⟩
  let t : I → Rˣ := fun i => (hInv (.inl i)).unit
  have ht (i : I) : (t i : R) = a (.inl i) := (hInv (.inl i)).unit_spec
  have hAdj : adjoint J g.val * g.val = 1 := by
    by_cases hI : Nonempty I
    · exact ((splitPairIsometries I R g).mp z.property).1
    · have : IsEmpty I := not_nonempty_iff.mp hI
      exact Subsingleton.elim _ _
  have hPair : (diagonal a) * J * (diagonal a) = J := by
    have h := congrArg (J * ·) hAdj
    have hJ : J * J = 1 := hyperbolicGram_square I R
    rw [adjoint, hg, diagonal_transpose, ← mul_assoc J, ← mul_assoc J, ← mul_assoc J,
      hJ, one_mul, mul_one] at h
    exact h
  have hNorm (i : I) : a (.inl i) * a (.inr i) = 1 := by
    have h := congrArg (fun N : Matrix (I ⊕ I) (I ⊕ I) R => N (.inl i) (.inr i)) hPair
    simp [J, hyperbolicGram, mul_diagonal, diagonal_mul] at h
    exact h
  refine ⟨t, ?_⟩
  change g.val = _
  rw [hg, hyperbolicDiagonal]
  congr 1
  funext i
  rcases i with i | i
  · exact (ht i).symm
  · apply (t i).isUnit.mul_left_cancel
    have hi := hNorm i
    rw [← ht i] at hi
    change (t i : R) * a (.inr i) = (t i : R) * (↑(t i)⁻¹ : R)
    rw [Units.mul_inv]
    exact hi

private theorem splitDiagonal_isOwnSchemeCentralizer :
    IsOwnSchemeCentralizer (splitDiagonalTorus P d) := by
  intro R a
  change Points P.spin.val.X R at a
  constructor
  · intro h
    have hC : CentralizesDiagonal (spinVectorMatrix P R a) := by
      intro S _ f t
      let : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
      let U : TestAlgebra k := CommAlgCat.of k S
      let f₀ : R ⟶ U := CommAlgCat.ofHom { toRingHom := f, commutes' := fun _ => rfl }
      obtain ⟨V, g, hg, q, hq⟩ := diagonalTorus_lift P d U t
      have he := congrArg (spinVectorMatrix P V) (h V (f₀ ≫ g) q).eq
      change spinVectorMatrix P V ((mapPoints (f₀ ≫ g) a) *
          (q ≫ (splitDiagonalTorus P d).inclusion.hom.hom)) =
        spinVectorMatrix P V ((q ≫ (splitDiagonalTorus P d).inclusion.hom.hom) *
          mapPoints (f₀ ≫ g) a) at he
      rw [spinVectorMatrix_mul, spinVectorMatrix_mul, hq, spinVectorMatrix_map] at he
      have he' : ((spinVectorMatrix P R a).map f).map g.hom * (hyperbolicDiagonal t).map g.hom =
          (hyperbolicDiagonal t).map g.hom * ((spinVectorMatrix P R a).map f).map g.hom := he
      change (spinVectorMatrix P R a).map f * hyperbolicDiagonal t = _
      apply Matrix.map_injective hg
      dsimp only
      simpa only [Matrix.map_mul (f := g.hom)] using he'
    let p := (P.orthogonal.points R ((a ≫ P.projection.hom.hom) ≫ P.inclusion.hom.hom))
    have hz (i j : I ⊕ I) (hij : i ≠ j) : p.val.val i j = 0 :=
      offDiagonal_eq_zero_of_centralizes hC hij
    obtain ⟨t, ht⟩ := orthogonal_eq_hyperbolicDiagonal p hz
    refine (splitDiagonalTorus_range P d R a).mpr ⟨fun i => t (d i), ?_⟩
    rw [reindex_middle_diagonal]
    simpa only [spinVectorMatrix, p, Equiv.apply_symm_apply] using ht
  · rintro ⟨q, rfl⟩ S f a
    let T := splitDiagonalTorus P d
    let : IsMulCommutative (Points T.group.X S) :=
      (isCommMonObj_iff_isMulCommutative T.group.X).mp (torusComm P d) _
    change Commute (mapPoints f (q ≫ T.inclusion.hom.hom)) (a ≫ T.inclusion.hom.hom)
    have h : Commute (mapPoints f q) a := mul_comm _ _
    exact h.map (IsMonHom.monoidHom T.inclusion.hom.hom _)

open Specs.GeometricRadicals (IsSplitTorus IsMaximalTorus baseChangedSubgroup)
open Specs.EquivariantUnipotentSeries (onPoints)
open private groupBaseChangePointIso from LinearAlgebraicGroups.Affine.RationalRepresentations
open private baseChangePoint_map from LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing
open private splitTorus_baseChange from LinearAlgebraicGroups.Classification.CentralIsogenies
open private sections_factor_of_affine from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private theorem maximalTorus_of_ownCentralizer {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (hT : IsSplitTorus T.group) (hc : IsOwnSchemeCentralizer T) : IsMaximalTorus T := by
  refine ⟨isTorus_of_split hT, ?_⟩
  intro S hS hTS
  obtain ⟨j, hj⟩ := hTS
  let B := Specs.Unipotent.closedSubgroupAlgebraicGroup S
  have hcS := CentralFrobeniusDescent.torus_commutative B hS
  obtain ⟨b, hb⟩ := sections_factor_of_affine T B.property.1 S.inclusion.hom.hom (by
    intro R x
    change Points S.group.X R at x
    apply (hc R (x ≫ S.inclusion.hom.hom)).mp
    intro U f y
    change Points T.group.X U at y
    change Commute ((testSpec k).map f.op ≫ (x ≫ S.inclusion.hom.hom)) (y ≫ T.inclusion.hom.hom)
    have hh := congrArg (fun g : T.group ⟶ G.val => g.hom.hom) hj
    change j.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom at hh
    let : IsMulCommutative (Points S.group.X U) :=
      (isCommMonObj_iff_isMulCommutative S.group.X).mp hcS _
    have hc' : Commute (mapPoints f x) (y ≫ j.hom.hom) := by
      show mapPoints f x * (y ≫ j.hom.hom) = (y ≫ j.hom.hom) * mapPoints f x
      exact mul_comm _ _
    rw [← hh]
    have h := hc'.map (IsMonHom.monoidHom S.inclusion.hom.hom _)
    change Commute ((mapPoints f x) ≫ S.inclusion.hom.hom) ((y ≫ j.hom.hom) ≫ S.inclusion.hom.hom) at h
    simpa only [mapPoints, Category.assoc] using h)
  exact factor_group_through_subgroup T S.inclusion b hb

private theorem ownCentralizer_baseChange {G : GroupScheme k} (T : ClosedSubgroup G)
    (hT : IsOwnSchemeCentralizer T) (K : Type u) [Field K] [Algebra k K]
    (hK : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left)
    (hc : IsCommMonObj ((groupBaseChange k K).obj T.group).X) :
    IsOwnSchemeCentralizer (baseChangedSubgroup K T hK) := by
  let T' := baseChangedSubgroup K T hK
  let G' := (groupBaseChange k K).obj G
  let gIso := groupBaseChangePointIso K G
  let tIso := groupBaseChangePointIso K T.group
  intro R x
  change Points G'.X R at x
  constructor
  · intro hx
    let x₀ : Points G.X ((restrictTestAlgebra k K).obj R) := gIso.hom.app R x
    obtain ⟨t, ht⟩ := (hT ((restrictTestAlgebra k K).obj R) x₀).mp (by
      intro S f s
      change Points T.group.X S at s
      let : Algebra K S := (f.hom.toRingHom.comp (algebraMap K R)).toAlgebra
      let V : TestAlgebra K := CommAlgCat.of K S
      let φ : R ⟶ V := CommAlgCat.ofHom { toRingHom := f.hom.toRingHom, commutes' := fun _ => rfl }
      let W := (restrictTestAlgebra k K).obj V
      let e₁ : S ⟶ W := (CommAlgCat.homEquivCommRingCat S W).symm ⟨𝟙 _, by
        apply RingHom.ext
        intro r
        exact (f.hom.commutes r).symm⟩
      let e₂ : W ⟶ S := (CommAlgCat.homEquivCommRingCat W S).symm ⟨𝟙 _, by
        apply RingHom.ext
        intro r
        exact f.hom.commutes r⟩
      let e : S ≅ W := ⟨e₁, e₂,
        by apply (forget₂ (CommAlgCat k) CommRingCat).map_injective; rfl,
        by apply (forget₂ (CommAlgCat k) CommRingCat).map_injective; rfl⟩
      let s' : Points T'.group.X V := tIso.inv.app V (mapPoints e.hom s)
      have hts : tIso.hom.app V s' = mapPoints e.hom s :=
        ConcreteCategory.congr_hom (tIso.inv_hom_id_app V) (mapPoints e.hom s)
      have hφ : f ≫ e.hom = (restrictTestAlgebra k K).map φ := by
        apply (forget₂ (CommAlgCat k) CommRingCat).map_injective
        rfl
      have hh := (hx V φ s').map (gIso.hom.app V).hom
      change Commute (gIso.hom.app V (mapPoints φ x))
        (baseChangePoint k K G.X V (onPoints ((groupBaseChange k K).map T.inclusion) V s')) at hh
      rw [baseChangePoint_map] at hh
      have hgnat := ConcreteCategory.congr_hom (gIso.hom.naturality φ) x
      change gIso.hom.app V (mapPoints φ x) = mapPoints ((restrictTestAlgebra k K).map φ) x₀ at hgnat
      rw [hgnat, ← hφ] at hh
      change Commute (mapPoints (f ≫ e.hom) x₀)
        (onPoints T.inclusion ((restrictTestAlgebra k K).obj V) (tIso.hom.app V s')) at hh
      rw [hts] at hh
      let z := mapPoints e.hom (X := G.X)
      have h1 : mapPoints (f ≫ e.hom) x₀ = z (mapPoints f x₀) := by
        change (testSpec k).map (f ≫ e.hom).op ≫ x₀ = _
        rw [show (f ≫ e.hom).op = e.hom.op ≫ f.op from rfl, Functor.map_comp, Category.assoc]
      have h2 : onPoints T.inclusion ((restrictTestAlgebra k K).obj V) (mapPoints e.hom s) =
          z (s ≫ T.inclusion.hom.hom) := by
        change ((testSpec k).map e.hom.op ≫ s) ≫ T.inclusion.hom.hom =
          (testSpec k).map e.hom.op ≫ s ≫ T.inclusion.hom.hom
        exact Category.assoc _ _ _
      rw [h1, h2] at hh
      change Commute (mapPoints f x₀) (s ≫ T.inclusion.hom.hom)
      change (mapPoints f x₀) * (s ≫ T.inclusion.hom.hom) = _
      let : IsIso e.hom := e.isIso_hom
      let : IsIso e.hom.op := inferInstance
      apply (cancel_epi ((testSpec k).map e.hom.op)).mp
      rw [MonObj.comp_mul, MonObj.comp_mul]
      exact hh.eq)
    let t' : Points T'.group.X R := tIso.inv.app R t
    refine ⟨t', ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (gIso.hom.app R)).1
    change baseChangePoint k K G.X R (onPoints ((groupBaseChange k K).map T.inclusion) R t') = x₀
    rw [baseChangePoint_map]
    have he : tIso.hom.app R t' = t := ConcreteCategory.congr_hom (tIso.inv_hom_id_app R) t
    change onPoints T.inclusion ((restrictTestAlgebra k K).obj R) (tIso.hom.app R t') = x₀
    rwa [he]
  · rintro ⟨y, rfl⟩ S f z
    change Points T'.group.X R at y
    change Points T'.group.X S at z
    let : IsMulCommutative (Points T'.group.X S) :=
      (isCommMonObj_iff_isMulCommutative T'.group.X).mp hc _
    change Commute (mapPoints f (y ≫ T'.inclusion.hom.hom)) (z ≫ T'.inclusion.hom.hom)
    have h : Commute (mapPoints f y) z := by
      show mapPoints f y * z = z * mapPoints f y
      exact mul_comm _ _
    exact h.map (IsMonHom.monoidHom T'.inclusion.hom.hom _)

open Specs.RankOneFlag (IsGeometricallyMaximal)

private theorem splitDiagonalTorus_isGeometricallyMaximal :
    IsGeometricallyMaximal (splitDiagonalTorus P d) := by
  let T := splitDiagonalTorus P d
  let K := AlgebraicClosure k
  let G' := Specs.Unipotent.baseChangedAlgebraicGroup K P.spin
  let : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  have hK : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) (fieldSpecMap k K)
      T.inclusion.hom.hom T.isClosedImmersion
  let T' := baseChangedSubgroup K T hK
  have hT' : IsSplitTorus T'.group := splitTorus_baseChange K (splitDiagonalTorus_isSplit P d)
  have hComm := CentralFrobeniusDescent.torus_commutative
    (Specs.Unipotent.closedSubgroupAlgebraicGroup (G := G') T') (isTorus_of_split hT')
  exact ⟨hK, maximalTorus_of_ownCentralizer (G := G') hT'
    (ownCentralizer_baseChange T (splitDiagonal_isOwnSchemeCentralizer P d) K hK hComm)⟩

end DiagonalTorusCentralizer

/-- The diagonal inverse image and its cocharacters in vector coordinates. -/
theorem splitSpinDiagonalTorus : SplitSpinDiagonalTorus.{u} := by
  intro k I _ _ _ _ P
  let m := Fintype.card I - 1
  have hI : 0 < Fintype.card I := Fintype.card_pos
  let d : Fin (m + 1) ≃ I := (finCongr (by dsimp [m]; omega)).trans (Fintype.equivFin I).symm
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  let T := splitDiagonalTorus P d
  have hp : (P.projection ≫ P.inclusion).hom.hom =
      P.projection.hom.hom ≫ P.inclusion.hom.hom := rfl
  refine ⟨T, torusComm P d, splitDiagonalTorus_isSplit P d,
    splitDiagonalTorus_isGeometricallyMaximal P d, ?_, ?_⟩
  · intro R a
    refine (splitDiagonalTorus_range P d R a).trans ?_
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨fun i => t (d.symm i), ?_⟩
      rw [reindex_middle_diagonal] at ht
      simpa only [hp, vectorImageMatrix, Category.assoc] using ht
    · rintro ⟨t, ht⟩
      refine ⟨fun i => t (d i), ?_⟩
      rw [reindex_middle_diagonal]
      simpa only [hp, vectorImageMatrix, Category.assoc, Equiv.apply_symm_apply] using ht
  · refine ⟨diagonalCocharacterLattice P d, fun R s c => ?_⟩
    have h : (T.inclusion ≫ P.projection ≫ P.inclusion).hom.hom =
        T.inclusion.hom.hom ≫ P.projection.hom.hom ≫ P.inclusion.hom.hom := rfl
    let a : Points T.group.X R := cocharacterPoint c R s
    change (P.orthogonal.points R (a ≫ (T.inclusion ≫ P.projection ≫ P.inclusion).hom.hom)).val.val = _
    rw [h]
    have hc := diagonalCocharacter_vector P d R s c
    change (P.orthogonal.points R (((a ≫ T.inclusion.hom.hom) ≫ P.projection.hom.hom) ≫
      P.inclusion.hom.hom)).val.val = _ at hc
    have hassoc := (Category.assoc (a ≫ T.inclusion.hom.hom) P.projection.hom.hom
      P.inclusion.hom.hom).trans (Category.assoc a T.inclusion.hom.hom
      (P.projection.hom.hom ≫ P.inclusion.hom.hom))
    exact (congrArg (fun p : Points P.orthogonal.group.val.X R =>
      (P.orthogonal.points R p).val.val) hassoc).symm.trans hc

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open private comp_conjugateFamily from LinearAlgebraicGroups.Affine.Stabilizers
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes

/-- The scalar subgroup is central as a subgroup scheme, including in characteristic two. -/
theorem splitSpinCentralIsogeny : SplitSpinCentralIsogeny.{u} := by
  intro k I _ _ _ P
  refine ⟨P.finite, P.flat, P.surjective, P.kernel, P.isKernel, ?_⟩
  let : IsAffine P.spin.val.X.left := P.spin.property.1
  let : IsClosedImmersion P.kernel.inclusion.hom.hom.left := P.kernel.isClosedImmersion
  let : IsAffine P.kernel.group.X.left := isAffine_of_isAffineHom P.kernel.inclusion.hom.hom.left
  have hA : IsAffine (P.spin.val.X ⊗ P.kernel.group.X).left := by
    rw [Over.tensorObj_left]
    infer_instance
  change conjugateFamily (𝟙 P.spin.val) P.kernel.inclusion.hom.hom = _
  apply hom_ext_of_points hA
  intro R x
  rw [comp_conjugateFamily]
  change (x ≫ snd P.spin.val.X P.kernel.group.X ≫ P.kernel.inclusion.hom.hom) *
      (x ≫ fst P.spin.val.X P.kernel.group.X ≫ 𝟙 P.spin.val.X) *
        (x ≫ snd P.spin.val.X P.kernel.group.X ≫ P.kernel.inclusion.hom.hom)⁻¹ =
      x ≫ fst P.spin.val.X P.kernel.group.X ≫ 𝟙 P.spin.val.X
  simp only [Category.comp_id]
  rw [← Category.assoc x (snd P.spin.val.X P.kernel.group.X)]
  exact mul_inv_eq_iff_eq_mul.mpr (P.central R (x ≫ snd _ _) (x ≫ fst _ _)).eq

end

end SplitDiagonalTorus

section SplitSpinGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open Specs.GeometricRadicals (IsSplitTorus)
open private reduced_of_flat_surjective from LinearAlgebraicGroups.Flag.ProjectiveFlags
open Albert
open Albert.SpinSpecification (spinUnits IsVectorAction)
open Albert.SplitSpinSpecification (PairIndex integralForm hyperbolicBasis HasActionMatrix EvenSwitches)

open private SpinRing splitSpinScheme switchOpen switchOpen_cover switchOpen_smooth spinFromAlg
  from LinearAlgebraicGroups.Albert.SplitSpin
open private coordinateUnit coordinateUnit_isIso universalPoint
  from LinearAlgebraicGroups.Classification.CellHomomorphism

noncomputable section

private abbrev SpinCoordinates (k : Type u) [Field k] (m : ℕ) := k ⊗[ℤ] SpinRing m

private theorem integralSpin_algebraSmooth (m : ℕ) (hm : 0 < m) :
    Algebra.Smooth ℤ (SpinRing m) := by
  let n := 2 * m ^ 2 - m
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
  have hd : SmoothOfRelativeDimension n (splitSpinScheme m).X.hom :=
    IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n)
      (switchOpen m) (switchOpen_cover m) (switchOpen_smooth m hm)
  have hs := hd.smooth
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℤ (SpinRing m)))) at hs
  exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hs)

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]
variable (P : SplitSpinVectorImage k I) {m : ℕ} (d : Fin m ≃ I)

private def algMapsOfIntegral (A : Type) [CommRing A] (R : TestAlgebra k) :
    ((k ⊗[ℤ] A) →ₐ[k] R) ≃ (A →ₐ[ℤ] R) where
  toFun f := (f.restrictScalars ℤ).comp Algebra.TensorProduct.includeRight
  invFun g := Algebra.TensorProduct.lift (Algebra.ofId k R) g (fun _ _ => Commute.all _ _)
  left_inv f := by
    apply Algebra.TensorProduct.ext'
    intro a b
    rw [Algebra.TensorProduct.lift_tmul]
    change algebraMap k R a * f (1 ⊗ₜ[ℤ] b) = f (a ⊗ₜ[ℤ] b)
    rw [← f.commutes, Algebra.TensorProduct.algebraMap_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  right_inv g := by
    apply AlgHom.ext
    intro x
    change Algebra.TensorProduct.lift (Algebra.ofId k R) g (fun _ _ => Commute.all _ _)
      (1 ⊗ₜ[ℤ] x) = g x
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

private theorem algMapsOfIntegral_natural (A : Type) [CommRing A] {R S : TestAlgebra k}
    (f : R ⟶ S) (g : k ⊗[ℤ] A →ₐ[k] R) :
    algMapsOfIntegral A S (f.hom.comp g) = (f.hom.restrictScalars ℤ).comp (algMapsOfIntegral A R g) :=
  rfl

private def integralPointUnit (R : TestAlgebra k) (a : Points P.spin.val.X R) :
    (SplitSpinSpecification.ScalarClifford m R)ˣ :=
  (Units.mapEquiv (integralCliffordCoordinates k I m d R).toMulEquiv).symm (P.spinPoints R a)

private theorem integralPointUnit_formula (R : TestAlgebra k) (a : Points P.spin.val.X R) :
    Units.map (integralCliffordCoordinates k I m d R).toMonoidHom (integralPointUnit P d R a) =
      P.spinPoints R a :=
  (Units.mapEquiv (integralCliffordCoordinates k I m d R).toMulEquiv).apply_symm_apply _

private theorem integralPointUnit_mem (R : TestAlgebra k) (a : Points P.spin.val.X R) :
    integralPointUnit P d R a ∈ spinUnits (integralForm m) R := by
  apply (integralSpinUnits k I m d R _).mp
  rw [integralPointUnit_formula, ← (P.spinRepresents.1 R).2]
  exact ⟨a, rfl⟩

private theorem integralPointUnit_injective (R : TestAlgebra k) :
    Function.Injective (integralPointUnit P d R) :=
  (Units.mapEquiv (integralCliffordCoordinates k I m d R).toMulEquiv).symm.injective.comp
    (P.spinRepresents.1 R).1

private theorem integralPointUnit_surjective (R : TestAlgebra k)
    (z : SpinFunctor.Spin (integralForm m) R (hyperbolicBasis ℤ m)) :
    ∃ a : Points P.spin.val.X R, integralPointUnit P d R a = z.val := by
  have h := (integralSpinUnits k I m d R _).mpr z.property
  rw [← (P.spinRepresents.1 R).2] at h
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  apply (Units.mapEquiv (integralCliffordCoordinates k I m d R).toMulEquiv).injective
  exact (integralPointUnit_formula P d R a).trans ha

set_option maxHeartbeats 500000 in
private theorem integralPointUnit_natural {R S : TestAlgebra k} (f : R ⟶ S) (a : Points P.spin.val.X R) :
    integralPointUnit P d S (mapPoints f a) =
      Units.map (SpinSpecification.coefficientMap (integralForm m) R
        (f.hom.restrictScalars ℤ)).toMonoidHom (integralPointUnit P d R a) := by
  apply (Units.mapEquiv (integralCliffordCoordinates k I m d S).toMulEquiv).injective
  change Units.map (integralCliffordCoordinates k I m d S).toMonoidHom _ =
    Units.map (integralCliffordCoordinates k I m d S).toMonoidHom _
  rw [integralPointUnit_formula, P.spinRepresents.2 f a]
  apply Units.ext
  change SpinSpecification.coefficientMap (hyperbolicForm I k) R f.hom
    (P.spinPoints R a).val = _
  rw [← integralPointUnit_formula P d R a]
  exact integralCliffordCoordinates_natural m d f (integralPointUnit P d R a).val

private def integralPointEquiv (R : TestAlgebra k) :
    Points P.spin.val.X R ≃ SpinFunctor.Spin (integralForm m) R (hyperbolicBasis ℤ m) :=
  Equiv.ofBijective (fun a => ⟨integralPointUnit P d R a, integralPointUnit_mem P d R a⟩)
    ⟨fun a b h => integralPointUnit_injective P d R (congrArg Subtype.val h),
      fun z => by
        obtain ⟨a, ha⟩ := integralPointUnit_surjective P d R z
        exact ⟨a, Subtype.ext ha⟩⟩

private def spinCoordinatePointEquiv (R : TestAlgebra k) :
    Points P.spin.val.X R ≃ (SpinCoordinates k m →ₐ[k] R) :=
  (integralPointEquiv P d R).trans ((spinFromAlg m R).symm.trans (algMapsOfIntegral (SpinRing m) R).symm)

private theorem spinCoordinatePointEquiv_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (a : Points P.spin.val.X R) :
    spinCoordinatePointEquiv P d S (mapPoints f a) =
      f.hom.comp (spinCoordinatePointEquiv P d R a) := by
  apply (algMapsOfIntegral (SpinRing m) S).injective
  refine Eq.trans ?_ (algMapsOfIntegral_natural (SpinRing m) f (spinCoordinatePointEquiv P d R a)).symm
  have h₁ (T : TestAlgebra k) (b : Points P.spin.val.X T) :
      algMapsOfIntegral (SpinRing m) T (spinCoordinatePointEquiv P d T b) =
        (spinFromAlg m T).symm (integralPointEquiv P d T b) :=
    (algMapsOfIntegral (SpinRing m) T).apply_symm_apply _
  rw [h₁ S, h₁ R]
  apply (spinFromAlg m S).injective
  let g := (spinFromAlg m R).symm (integralPointEquiv P d R a)
  change spinFromAlg m S ((spinFromAlg m S).symm (integralPointEquiv P d S (mapPoints f a))) =
    spinFromAlg m S ((f.hom.restrictScalars ℤ).comp g)
  rw [Equiv.apply_symm_apply, SpinFunctor.pointEquiv_natural]
  apply Subtype.ext
  change integralPointUnit P d S (mapPoints f a) =
    Units.map (SpinSpecification.coefficientMap (integralForm m) R
      (f.hom.restrictScalars ℤ)).toMonoidHom (spinFromAlg m R g).val
  rw [show spinFromAlg m R g = integralPointEquiv P d R a from
    (spinFromAlg m R).apply_symm_apply _]
  exact integralPointUnit_natural P d f a

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private def affineSchemeIsoOfPoints {X : SchemeOver k} [IsAffine X.left]
    (B : TestAlgebra k)
    (e : ∀ R : TestAlgebra k, Points X R ≃ (B →ₐ[k] R))
    (hn : ∀ {R S} (f : R ⟶ S) (a : Points X R), e S (mapPoints f a) = f.hom.comp (e R a)) :
    ((testSpec k).obj (op B)) ≅ X := by
  let b : Points X B := (e B).symm (AlgHom.id k B)
  let D : TestAlgebra k := _root_.LinearAlgebraicGroups.Specs.coordinates X
  let f : B ⟶ D := ConcreteCategory.ofHom (C := CommAlgCat k) (e D (universalPoint X))
  let c : X ⟶ (testSpec k).obj (op D) := coordinateUnit X
  let a : X ⟶ (testSpec k).obj (op B) := c ≫ (testSpec k).map f.op
  have hfb : mapPoints f b = universalPoint X := by
    apply (e D).injective
    rw [hn]
    change f.hom.comp (e B ((e B).symm (AlgHom.id k B))) = _
    rw [Equiv.apply_symm_apply, AlgHom.comp_id]
    rfl
  have hab : a ≫ b = 𝟙 X := by
    have hcb : (testSpec k).map f.op ≫ b = universalPoint X := hfb
    have : IsIso c := coordinateUnit_isIso X
    calc
      a ≫ b = c ≫ ((testSpec k).map f.op ≫ b) := Category.assoc _ _ _
      _ = c ≫ universalPoint X := congrArg (c ≫ ·) hcb
      _ = 𝟙 X := IsIso.hom_inv_id c
  refine ⟨b, a, ?_, hab⟩
  let φ := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (b ≫ a)
  have hφ : (testSpec k).map φ = b ≫ a := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hbφ : mapPoints φ.unop b = b := by
    change (testSpec k).map φ ≫ b = b
    rw [hφ, Category.assoc, hab, Category.comp_id]
  have h := congrArg (e B) hbφ
  rw [hn] at h
  have hb : e B b = AlgHom.id k B := (e B).apply_symm_apply _
  rw [hb, AlgHom.comp_id] at h
  have hφ' : φ.unop = 𝟙 B := CommAlgCat.hom_ext h
  rw [← hφ, ← Quiver.Hom.op_unop φ, hφ']
  exact (testSpec k).map_id (op B)

private def integralSpinSchemeIso : ((testSpec k).obj (op (CommAlgCat.of k (SpinCoordinates k m)))) ≅
    P.spin.val.X := by
  letI := P.spin.property.1
  exact affineSchemeIsoOfPoints _ (spinCoordinatePointEquiv P d) (spinCoordinatePointEquiv_natural P d)

include d in
private theorem splitCliffordSpin_smooth (hm : 0 < m) : Smooth P.spin.val.X.hom := by
  let : Algebra.Smooth ℤ (SpinRing m) := integralSpin_algebraSmooth m hm
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (SpinCoordinates k m)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr
      (inferInstance : Algebra.Smooth k (SpinCoordinates k m)))
  let e := integralSpinSchemeIso P d
  let : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have h : IsPullback e.inv.left P.spin.val.X.hom
      ((testSpec k).obj (op (CommAlgCat.of k (SpinCoordinates k m)))).hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨e.inv.w.trans (Category.comp_id _).symm⟩
  exact MorphismProperty.of_isPullback (P := @Smooth) h hs

section SplitConnectedness

open _root_.LinearAlgebraicGroups.Specs (coordinates)

omit [LinearOrder (I ⊕ I)] in
private theorem connectedHom_toEtale_eq_one {G E : GroupScheme k}
    (hG : ConnectedSpace G.X.left) (hE : Etale E.X.hom) (f : G ⟶ E) :
    f.hom.hom = 1 := by
  let y := η[E.X].left
  let : Etale E.X.hom := hE
  have hy : y ≫ E.X.hom = 𝟙 _ := Over.w _
  obtain ⟨ho, hc⟩ := etaleRationalPointImmersions E.X.hom y hy
  let : IsOpenImmersion y := ho
  let : IsClosedImmersion y := hc
  let U := f.hom.hom.left ⁻¹' Set.range y
  have hU : IsClopen U :=
    ⟨y.isClosedEmbedding.isClosed_range.preimage f.hom.hom.left.continuous,
      y.isOpenEmbedding.isOpen_range.preimage f.hom.hom.left.continuous⟩
  let x := IsLocalRing.closedPoint k
  have hU₀ : U.Nonempty :=
    ⟨η[G.X].left x, x, (congrArg (fun g : (𝟙_ (SchemeOver k)) ⟶ E.X => g.left x)
      (IsMonHom.one_hom f.hom.hom)).symm⟩
  have hRange : Set.range f.hom.hom.left ⊆ Set.range y := by
    rintro z ⟨w, rfl⟩
    change w ∈ U
    rw [hU.eq_univ hU₀]
    trivial
  let g := IsOpenImmersion.lift y f.hom.hom.left hRange
  have hg : g ≫ y = f.hom.hom.left := IsOpenImmersion.lift_fac _ _ _
  have hf : g = G.X.hom := by rw [← Category.comp_id g, ← hy, ← Category.assoc, hg, Over.w]
  apply Over.OverMorphism.ext
  exact hg.symm.trans (congrArg (· ≫ y) hf)

omit [LinearOrder (I ⊕ I)] in
private theorem kernel_in_splitDiagonal (hRank : 4 ≤ Fintype.card I) :
    ∃ (T : Specs.ClosedSubgroup P.spin.val),
      IsSplitTorus T.group ∧ ∃ f : P.kernel.group.X ⟶ T.group.X,
        f ≫ T.inclusion.hom.hom = P.kernel.inclusion.hom.hom := by
  have : Nonempty I := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card I)
  obtain ⟨T, _, hT, _, hRange, _⟩ := splitSpinDiagonalTorus k I P
  let K := P.kernel.group.X
  have : IsAffine P.spin.val.X.left := P.spin.property.1
  let : IsClosedImmersion P.kernel.inclusion.hom.hom.left := P.kernel.isClosedImmersion
  have : IsAffine K.left := isAffine_of_isAffineHom P.kernel.inclusion.hom.hom.left
  let R : TestAlgebra k := coordinates K
  let a : Points K R := universalPoint K
  have hp : a ≫ (P.kernel.inclusion ≫ P.projection ≫ P.inclusion).hom.hom = 1 := by
    have h := P.isKernel.w
    change P.kernel.inclusion.hom.hom ≫ P.projection.hom.hom = toUnit K ≫ η[P.image.val.X] at h
    change a ≫ P.kernel.inclusion.hom.hom ≫ P.projection.hom.hom ≫ P.inclusion.hom.hom = 1
    rw [← Category.assoc P.kernel.inclusion.hom.hom, h, Category.assoc,
      IsMonHom.one_hom, ← Category.assoc, comp_toUnit]
    rfl
  obtain ⟨b, hb⟩ := (hRange R (a ≫ P.kernel.inclusion.hom.hom)).mpr ⟨fun _ => 1, by
    have hp' : (a ≫ P.kernel.inclusion.hom.hom) ≫ (P.projection ≫ P.inclusion).hom.hom = 1 := by
      rw [Category.assoc]
      exact hp
    rw [hp']
    have h₁ : P.orthogonal.points R (1 : Points P.orthogonal.group.val.X R) = 1 :=
      (P.orthogonal.points R).map_one
    rw [h₁]
    simp [Specs.SymplecticMatrixStructure.hyperbolicDiagonal]⟩
  let c : K ⟶ (testSpec k).obj (op R) := coordinateUnit K
  have : IsIso c := coordinateUnit_isIso K
  refine ⟨T, hT, c ≫ b, ?_⟩
  rw [Category.assoc, hb, ← Category.assoc]
  have hca : c ≫ a = 𝟙 K := IsIso.hom_inv_id c
  rw [hca, Category.id_comp]

open private splitTorus_connected from LinearAlgebraicGroups.RootData.BorelsAndChambers

omit [LinearOrder (I ⊕ I)] in
private theorem splitCliffordSpin_connected (hRank : 4 ≤ Fintype.card I) :
    GeometricallyConnected P.spin.val.X.hom := by
  obtain ⟨E, H, q, _, hc, _, _, _⟩ := _root_.LinearAlgebraicGroups.identityComponentAndQuotient k P.spin
  obtain ⟨T, hT, f, hf⟩ := kernel_in_splitDiagonal P hRank
  have hTc : ConnectedSpace T.group.X.left := splitTorus_connected hT
  have hqT : (T.inclusion ≫ q).hom.hom = 1 := connectedHom_toEtale_eq_one hTc hc.etale _
  have hqK : P.kernel.inclusion.hom.hom ≫ q.hom.hom = 1 := by
    rw [← hf, Category.assoc]
    change f ≫ (T.inclusion ≫ q).hom.hom = 1
    rw [hqT, MonObj.comp_one]
  let : IsAffine P.spin.val.X.left := P.spin.property.1
  let : IsAffine P.image.val.X.left := P.image.property.1
  let : Flat P.projection.hom.hom.left := P.flat
  let : Surjective P.projection.hom.hom.left := P.surjective
  obtain ⟨v, hv⟩ := CentralFrobeniusDescent.descendHomOfSchemeKernel P.projection P.isKernel q hqK
  have hq : q.hom.hom = 1 := by
    let : GeometricallyConnected P.image.val.X.hom :=
      (splitSpinIdentityComponent k I hRank P).1
    have h₁ := connectedHom_toEtale_eq_one
      (GeometricallyConnected.connectedSpace_of_subsingleton P.image.val.X.hom) hc.etale v
    rw [← hv]
    change P.projection.hom.hom ≫ v.hom.hom = 1
    rw [h₁, MonObj.comp_one]
  have hq' : q.hom.hom.left = P.spin.val.X.hom ≫ η[E.X].left :=
    congrArg Over.Hom.left hq
  let : Etale E.X.hom := hc.etale
  have hId : IsPullback (𝟙 P.spin.val.X.left) P.spin.val.X.hom q.hom.hom.left η[E.X].left := by
    rw [hq']
    have hm := (etaleRationalPointImmersions E.X.hom η[E.X].left (Over.w _)).2
    let : IsClosedImmersion η[E.X].left := hm
    exact IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  let e := hc.kernel.isoIsPullback _ _ hId
  have he' : e.hom ≫ P.spin.val.X.hom = H.X.hom :=
    hc.kernel.isoIsPullback_hom_snd _ _ hId
  have hs : IsPullback e.inv P.spin.val.X.hom H.X.hom (𝟙 _) := by
    apply IsPullback.of_horiz_isIso
    exact ⟨by rw [← he', e.inv_hom_id_assoc, Category.comp_id]⟩
  exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hs hc.geometricallyConnected

include d in
private theorem splitVectorImage_smooth (hm : 0 < m) : Smooth P.image.val.X.hom := by
  have hs := splitCliffordSpin_smooth P d hm
  have hr := ((_root_.LinearAlgebraicGroups.affineGroupSmoothnessCriteria k P.spin).1).mp hs
  apply ((_root_.LinearAlgebraicGroups.affineGroupSmoothnessCriteria k P.image).1).mpr
  constructor
  intro K _ y Y a b ha
  let p := P.projection.hom.hom.left
  let : Flat p := P.flat
  let : Surjective p := P.surjective
  have hp := IsPullback.of_hasPullback p a
  have hf := hp.paste_vert ha
  have hs' : IsPullback (pullback.fst p a) (pullback.snd p a ≫ b) P.spin.val.X.hom y := by
    rw [← P.projection.hom.hom.w]
    exact hf
  let : IsReduced (pullback p a) := hr.geometrically_isReduced y _ _ hs'
  exact reduced_of_flat_surjective (pullback.snd p a)

end SplitConnectedness


/-- The Clifford group and its vector image have the required split geometry
over every field, including fields of characteristic two. -/
theorem splitSpinGeometry : SplitSpinGeometry.{u} := by
  intro k I _ _ _ hRank P
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  let d := (Fintype.equivFin I).symm
  have h : 0 < Fintype.card I := by omega
  exact ⟨splitCliffordSpin_smooth P d h, splitCliffordSpin_connected P hRank,
    splitVectorImage_smooth P d h⟩

end

end SplitSpinGeometry

section TypeDDiagram

open Specs.Arithmetic.NontrialitarianSpinModels (coroots simpleDCoroot)
open Specs.Arithmetic.OddSpinModels (coordinateVector evenSum)
open Specs.AbsoluteDynkinTypes (PreservesCartan)

private theorem d4_stabilizer (σ : Equiv.Perm (Fin 4)) (h : σ 1 = 1) (h₀ : σ 0 = 0) :
    σ = Equiv.refl _ ∨ σ = Equiv.swap 2 3 := by
  have houter (j : Fin 4) (hj₀ : j ≠ 0) (hj₁ : j ≠ 1) : σ j = 2 ∨ σ j = 3 := by
    have hcases (a : Fin 4) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
      fin_cases a <;> decide
    rcases hcases (σ j) with he | he | he | he
    · exact (hj₀ (σ.injective (he.trans h₀.symm))).elim
    · exact (hj₁ (σ.injective (he.trans h.symm))).elim
    · exact Or.inl he
    · exact Or.inr he
  have h₂ := houter 2 (by decide) (by decide)
  have h₃ := houter 3 (by decide) (by decide)
  rcases h₂ with h₂ | h₂
  · have h₃ := h₃.resolve_left
      (fun he => (by decide : (2 : Fin 4) ≠ 3) (σ.injective (h₂.trans he.symm)))
    left
    apply Equiv.ext
    intro j
    fin_cases j
    · exact h₀
    · exact h
    · exact h₂
    · exact h₃
  · have h₃ := h₃.resolve_right
      (fun he => (by decide : (2 : Fin 4) ≠ 3) (σ.injective (h₂.trans he.symm)))
    right
    apply Equiv.ext
    intro j
    fin_cases j
    · exact h₀
    · exact h
    · exact h₂.trans (Equiv.swap_apply_left 2 3).symm
    · exact h₃.trans (Equiv.swap_apply_right 2 3).symm

/-- Put a chosen fixed vector vertex in the standard position. The two
remaining possible permutations differ by the interchange of the spin vertices. -/
theorem vectorVertexStabilizer : VectorVertexStabilizer := by
  intro n hn i hi
  by_cases hn' : n = 4
  · subst n
    let a : Equiv.Perm (Fin 4) := Equiv.swap 0 i
    have ha1 : a 1 = 1 := Equiv.swap_apply_of_ne_of_ne (by decide) (fun he => hi (by
      have := congrArg Fin.val he
      simpa using this.symm))
    have ha : PreservesCartan (CartanMatrix.D 4) (CartanMatrix.D 4) a :=
      (RootData.AbsoluteDynkinTypes.d4Permutations a).mpr ha1
    have ha0 : a 0 = i := Equiv.swap_apply_left 0 i
    refine ⟨a, ha, ha0, fun σ hσ hσi => ?_⟩
    have hσ1 : σ 1 = 1 := (RootData.AbsoluteDynkinTypes.d4Permutations σ).mp hσ
    have ha1' : a.symm 1 = 1 := a.symm_apply_eq.mpr ha1.symm
    have ha0' : a.symm i = 0 := a.symm_apply_eq.mpr ha0.symm
    have hf₁ : ((a.trans σ).trans a.symm) 1 = 1 := by
      simp only [Equiv.trans_apply, ha1, hσ1, ha1']
    have hf₀ : ((a.trans σ).trans a.symm) 0 = 0 := by
      simp only [Equiv.trans_apply, ha0, hσi, ha0']
    exact d4_stabilizer ((a.trans σ).trans a.symm) hf₁ hf₀
  · simp only [ite_eq_right hn'] at hi
    have hi' : (⟨0, by omega⟩ : Fin n) = i := Fin.ext hi.symm
    refine ⟨Equiv.refl _, fun _ _ => rfl, hi', fun σ hσ _ => ?_⟩
    simpa only [Equiv.refl_trans, Equiv.refl_symm, Equiv.trans_refl] using
      (RootData.AbsoluteDynkinTypes.typeDPermutations n (by omega) σ).mp hσ

section TypeDCoordinates

variable {n : ℕ} (hn : 4 ≤ n)

private abbrev hyperbolicCoordinate (i : Fin n) : ULift.{u} (Fin n) → ℤ :=
  coordinateVector _ (ULift.up i)

private theorem hyperbolicCoordinate_dot (i j : Fin n) :
    hyperbolicCoordinate.{u} i ⬝ᵥ hyperbolicCoordinate j = if i = j then 1 else 0 := by
  rw [dotProduct_single_one]
  simp [hyperbolicCoordinate, coordinateVector, Pi.single_apply, eq_comm]

private theorem simpleDCoroot_mem (i : Fin n) :
    simpleDCoroot.{u} n hn i ∈ coroots (ULift.{u} (Fin n)) := by
  unfold simpleDCoroot
  split
  · rename_i hi
    refine ⟨ULift.up i, ULift.up (⟨i.val + 1, hi⟩ : Fin n), ?_, Or.inl rfl⟩
    intro h
    have hv := congrArg (fun x : ULift.{u} (Fin n) => x.down.val) h
    dsimp at hv
    omega
  · refine ⟨ULift.up (⟨n - 2, by omega⟩ : Fin n), ULift.up (⟨n - 1, by omega⟩ : Fin n), ?_,
      Or.inr (Or.inl rfl)⟩
    intro h
    have hv := congrArg (fun x : ULift.{u} (Fin n) => x.down.val) h
    dsimp at hv
    omega

set_option maxHeartbeats 1100000 in
private theorem simpleDCoroot_dot (i j : Fin n) :
    simpleDCoroot.{u} n hn j ⬝ᵥ simpleDCoroot n hn i = CartanMatrix.D n i j := by
  simp only [simpleDCoroot, CartanMatrix.D, Matrix.of_apply]
  split <;> split <;>
    simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add,
      hyperbolicCoordinate_dot, Fin.ext_iff] <;>
    split_ifs <;> omega

private theorem adjacentDifference_mem_span (j : ℕ) (hj : j < n) :
    hyperbolicCoordinate.{u} (⟨0, by omega⟩ : Fin n) - hyperbolicCoordinate ⟨j, hj⟩ ∈
      Submodule.span ℤ (Set.range (simpleDCoroot n hn)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have he : simpleDCoroot.{u} n hn ⟨j, by omega⟩ =
        hyperbolicCoordinate (⟨j, by omega⟩ : Fin n) - hyperbolicCoordinate ⟨j+1, hj⟩ := by
      rw [simpleDCoroot, dite_eq_left hj]
    have hm : hyperbolicCoordinate (⟨j, by omega⟩ : Fin n) - hyperbolicCoordinate ⟨j+1, hj⟩ ∈
        Submodule.span ℤ (Set.range (simpleDCoroot.{u} n hn)) := by
      rw [← he]
      exact Submodule.subset_span ⟨_, rfl⟩
    have h := Submodule.add_mem _ (ih (by omega)) hm
    convert h using 1
    abel

/-- The standard simple coroots yield the type-D Cartan matrix and generate
the full lattice of even coordinate sum. -/
theorem simpleDCoordinates : SimpleDCoordinates.{u} := by
  intro n hn
  let S := Submodule.span ℤ (Set.range (simpleDCoroot.{u} n hn))
  have : Nontrivial (ULift.{u} (Fin n)) :=
    ⟨⟨ULift.up (⟨0, by omega⟩ : Fin n), ULift.up ⟨1, by omega⟩, fun h => by
      have he := congrArg (fun x : ULift.{u} (Fin n) => x.down.val) h
      dsimp at he
      omega⟩⟩
  rw [← (corootLattice (ULift.{u} (Fin n))).1]
  refine ⟨simpleDCoroot_dot hn, le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)⟩
  · rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (simpleDCoroot_mem hn i)
  have hdiff (i j : Fin n) : hyperbolicCoordinate.{u} i - hyperbolicCoordinate j ∈ S := by
    have hi := adjacentDifference_mem_span.{u} hn i.val i.isLt
    have hj := adjacentDifference_mem_span.{u} hn j.val j.isLt
    have h := S.sub_mem hj hi
    convert h using 1
    abel
  let a : Fin n := ⟨n - 2, by omega⟩
  let b : Fin n := ⟨n - 1, by omega⟩
  have hb : ¬ b.val + 1 < n := by dsimp [b]; omega
  have hab : hyperbolicCoordinate.{u} a + hyperbolicCoordinate b ∈ S := by
    have he : simpleDCoroot.{u} n hn b = hyperbolicCoordinate a + hyperbolicCoordinate b := by
      rw [simpleDCoroot, dite_eq_right hb]
    exact he ▸ Submodule.subset_span ⟨b, rfl⟩
  have hsum (i j : Fin n) : hyperbolicCoordinate.{u} i + hyperbolicCoordinate j ∈ S := by
    have h := S.add_mem (S.add_mem (hdiff i a) (hdiff j b)) hab
    convert h using 1
    abel
  rintro _ ⟨⟨i⟩, ⟨j⟩, _, hi | hi | hi⟩
  · exact hi.symm ▸ hdiff i j
  · exact hi.symm ▸ hsum i j
  · exact hi.symm ▸ S.neg_mem (hsum i j)

end TypeDCoordinates

end TypeDDiagram

section TypeDChamber

open Specs.Arithmetic.NontrialitarianSpinModels (coroots simpleDCoroot)
open Specs.Arithmetic.OddSpinModels (coordinateVector)

private theorem heightD_ne_zero {n : ℕ} {r : ULift.{u} (Fin n) → ℤ}
    (hr : r ∈ coroots (ULift.{u} (Fin n))) : typeDRootHeight n r ≠ 0 := by
  rintro he
  rcases hr with ⟨⟨i⟩, ⟨j⟩, h, rfl | rfl | rfl⟩
  all_goals
    have hij : i.val ≠ j.val := fun hh => h (congrArg ULift.up (Fin.ext hh))
    simp only [typeDRootHeight, dotProduct_sub, dotProduct_add, dotProduct_neg, coordinateVector,
      dotProduct_single_one] at he
    change _ at he
    omega

private theorem heightD_simple {n : ℕ} (hn : 4 ≤ n) (i : Fin n) :
    typeDRootHeight n (simpleDCoroot.{u} n hn i) = 1 := by
  unfold simpleDCoroot typeDRootHeight
  split <;>
    simp only [dotProduct_sub, dotProduct_add, coordinateVector, dotProduct_single_one] <;> omega

private theorem difference_root {n : ℕ} {i j : Fin n} (h : i.val < j.val) :
    hyperbolicCoordinate.{u} i - hyperbolicCoordinate j ∈ coroots (ULift.{u} (Fin n)) ∧ 0 < typeDRootHeight n (hyperbolicCoordinate.{u} i - hyperbolicCoordinate j) := by
  refine ⟨⟨ULift.up i, ULift.up j, ?_, Or.inl rfl⟩, ?_⟩
  · intro h'
    have he := congrArg (fun x : ULift.{u} (Fin n) => x.down.val) h'
    exact (Nat.ne_of_lt h) he
  · simp only [typeDRootHeight, dotProduct_sub, hyperbolicCoordinate, coordinateVector, dotProduct_single_one]
    omega

private theorem sum_root {n : ℕ} {i j : Fin n} (h : i.val < j.val) :
    hyperbolicCoordinate.{u} i + hyperbolicCoordinate j ∈ coroots (ULift.{u} (Fin n)) ∧ 0 < typeDRootHeight n (hyperbolicCoordinate.{u} i + hyperbolicCoordinate j) := by
  refine ⟨⟨ULift.up i, ULift.up j, ?_, Or.inr (Or.inl rfl)⟩, ?_⟩
  · intro h'
    have he := congrArg (fun x : ULift.{u} (Fin n) => x.down.val) h'
    exact (Nat.ne_of_lt h) he
  · simp only [typeDRootHeight, dotProduct_add, hyperbolicCoordinate, coordinateVector, dotProduct_single_one]
    omega

private def PositiveDecomposition {n : ℕ} (r : ULift.{u} (Fin n) → ℤ) : Prop :=
  ∃ a b, (a ∈ coroots (ULift.{u} (Fin n)) ∧ 0 < typeDRootHeight n a) ∧
    (b ∈ coroots (ULift.{u} (Fin n)) ∧ 0 < typeDRootHeight n b) ∧ a + b = r

private theorem sum_simple_or_decomposes {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) (hij : i.val < j.val) :
    (hyperbolicCoordinate.{u} i + hyperbolicCoordinate j ∈ Set.range (simpleDCoroot n hn)) ∨ PositiveDecomposition (hyperbolicCoordinate.{u} i + hyperbolicCoordinate j) := by
  by_cases h : i.val + 1 < j.val
  · let l : Fin n := ⟨i.val+1, by omega⟩
    exact Or.inr ⟨hyperbolicCoordinate i - hyperbolicCoordinate l, hyperbolicCoordinate l + hyperbolicCoordinate j,
      difference_root (i := i) (j := l) (by exact Nat.lt_succ_self _),
      sum_root (i := l) (j := j) h, by abel⟩
  by_cases hh : j.val + 1 < n
  · let l : Fin n := ⟨j.val+1, hh⟩
    have hlj : j.val < l.val := Nat.lt_succ_self _
    exact Or.inr ⟨hyperbolicCoordinate j - hyperbolicCoordinate l, hyperbolicCoordinate i + hyperbolicCoordinate l,
      difference_root hlj, sum_root (hij.trans hlj), by abel⟩
  left
  refine ⟨j, ?_⟩
  rw [simpleDCoroot, dite_eq_right hh]
  have hi : (⟨n-2, by omega⟩ : Fin n) = i := Fin.ext (by change n-2 = i.val; omega)
  have hj : (⟨n-1, by omega⟩ : Fin n) = j := Fin.ext (by change n-1 = j.val; omega)
  rw [hi, hj]

private theorem positive_simple_or_decomposes {n : ℕ} (hn : 4 ≤ n) {r : ULift.{u} (Fin n) → ℤ}
    (hr : r ∈ coroots (ULift.{u} (Fin n))) (hp : 0 < typeDRootHeight n r) :
    r ∈ Set.range (simpleDCoroot n hn) ∨ PositiveDecomposition r := by
  rcases hr with ⟨⟨i⟩, ⟨j⟩, h, rfl | rfl | rfl⟩
  · change 0 < typeDRootHeight n (hyperbolicCoordinate.{u} i - hyperbolicCoordinate j) at hp
    have hij : i.val < j.val := by
      simp only [typeDRootHeight, dotProduct_sub, hyperbolicCoordinate, coordinateVector, dotProduct_single_one] at hp
      omega
    by_cases he : i.val + 1 = j.val
    · left
      have hi : i.val + 1 < n := by omega
      have hj : (⟨i.val+1, hi⟩ : Fin n) = j := Fin.ext he
      exact ⟨i, by rw [simpleDCoroot, dite_eq_left hi, hj]⟩
    · let l : Fin n := ⟨i.val+1, by omega⟩
      exact Or.inr ⟨hyperbolicCoordinate i - hyperbolicCoordinate l, hyperbolicCoordinate l - hyperbolicCoordinate j, difference_root (by change i.val < i.val+1; omega),
        difference_root (by change i.val+1 < j.val; omega), by abel⟩
  · change hyperbolicCoordinate.{u} i + hyperbolicCoordinate j ∈ _ ∨ PositiveDecomposition (hyperbolicCoordinate.{u} i + hyperbolicCoordinate j)
    rcases lt_trichotomy i.val j.val with hij | he | hji
    · exact sum_simple_or_decomposes hn i j hij
    · exact (h (congrArg ULift.up (Fin.ext he))).elim
    · rw [add_comm]
      exact sum_simple_or_decomposes hn j i hji
  · have hij : i.val ≠ j.val := fun he => h (congrArg ULift.up (Fin.ext he))
    simp only [typeDRootHeight, dotProduct_neg, dotProduct_add, coordinateVector, dotProduct_single_one] at hp
    omega

private theorem indecomposable_positive_D {n : ℕ} (hn : 4 ≤ n) (r : ULift.{u} (Fin n) → ℤ) :
    r ∈ Set.range (simpleDCoroot n hn) ↔
      r ∈ coroots (ULift.{u} (Fin n)) ∧ 0 < typeDRootHeight n r ∧ ¬ PositiveDecomposition r := by
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨simpleDCoroot_mem hn i, by simp [heightD_simple], ?_⟩
    rintro ⟨a, b, ha, hb, he⟩
    have h := congrArg (typeDRootHeight n) he
    change typeDRootHeight n (a + b) = _ at h
    rw [heightD_simple] at h
    have h' : typeDRootHeight n a + typeDRootHeight n b = 1 := by
      simpa only [typeDRootHeight, dotProduct_add] using h
    omega
  · rintro ⟨h, hp, hnd⟩
    exact (positive_simple_or_decomposes hn h hp).resolve_right hnd


/-- The indicated coordinate height selects the standard simple roots. -/
theorem typeDPositiveRoots : TypeDPositiveRoots.{u} := by
  intro n hn
  exact ⟨fun _ => heightD_ne_zero, indecomposable_positive_D hn⟩

end TypeDChamber

section SplitVectorStructure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.SymplecticMatrixStructure (CentralizesDiagonal hyperbolicDiagonal)
open Albert.SplitSpinSpecification (PairIndex Block PreservesNorm middle lower upper EvenSwitches signedSwitch)
open private factor_det middle_preserves signedSwitch_map from LinearAlgebraicGroups.Albert.SplitSpin
open private offDiagonal_eq_zero_of_centralizes from LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable (P : SplitSpinVectorImage k I) {m : ℕ} (d : Fin (m+1) ≃ I)

private theorem vectorImage_contains_middle (hRank : 4 ≤ Fintype.card I) (R : TestAlgebra k)
    (A : Block (m+1) R) (hA : IsUnit A.det) :
    ∃ p : Points P.image.val.X R,
      vectorImageMatrix P R p = Matrix.reindex (d.sumCongr d) (d.sumCongr d) (middle A) := by
  have hd : (middle A).det = 1 := by
    have h := factor_det (0 : Block (m+1) R) 0 A hA
    simpa [lower, upper] using h
  let O := P.orthogonal
  let g := pointOfNormMatrix O R d (middle A) (middle_preserves hA) (hd ▸ isUnit_one)
  have hg := pointOfNormMatrix_value O R d (middle A) (middle_preserves hA) (hd ▸ isUnit_one)
  change (O.points R g).val.val = _ at hg
  have htop : IsUnit (O.points R g).val.val.toBlocks₁₁.det := by
    rw [hg]
    change IsUnit (A.submatrix d.symm d.symm).det
    rwa [Matrix.det_submatrix_equiv_self]
  obtain ⟨p, hp⟩ := splitSpinChartInImage k I hRank P R g htop
  refine ⟨p, ?_⟩
  change (O.points R (p ≫ P.inclusion.hom.hom)).val.val = _
  exact (congrArg (fun z => (O.points R z).val.val) hp).trans hg

include d in
private theorem vectorImage_contains_diagonal (hRank : 4 ≤ Fintype.card I) (R : TestAlgebra k)
    (t : I → Rˣ) :
    ∃ p : Points P.image.val.X R, vectorImageMatrix P R p = hyperbolicDiagonal t := by
  let s : Fin (m+1) → Rˣ := t ∘ d
  obtain ⟨p, hp⟩ := vectorImage_contains_middle P d hRank R (diagonalBlock s)
    (diagonalBlock_det_unit s)
  refine ⟨p, ?_⟩
  rw [hp, reindex_middle_diagonal d s]
  simp [s]

private theorem commute_diagonal_entry {L R : Type u} [Fintype L] [DecidableEq L]
    [CommRing R] (a : L → R) (X : Matrix L L R) {i j : L}
    (h : Commute (diagonal a) X) (hX : IsUnit (X i j)) : a i = a j := by
  have hr := congrFun₂ h.eq i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hr
  exact hX.mul_right_cancel (hr.trans (mul_comm _ _))

private theorem vectorImage_leftEntry (hRank : 4 ≤ Fintype.card I) (R : TestAlgebra k)
    (i j : Fin (m+1)) :
    ∃ p : Points P.image.val.X R, vectorImageMatrix P R p (.inl (d i)) (.inl (d j)) = 1 := by
  let σ := Equiv.swap i j
  let A := σ.permMatrix R
  have hA : IsUnit A.det := by
    change IsUnit (σ.permMatrix R).det
    rw [det_permutation]
    exact (Equiv.Perm.sign σ).isUnit.map (Int.castRingHom R)
  obtain ⟨p, hp⟩ := vectorImage_contains_middle P d hRank R A hA
  refine ⟨p, ?_⟩
  rw [hp]
  change (middle A) (.inl (d.symm (d i))) (.inl (d.symm (d j))) = 1
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change A i j = 1
  simp [A, σ, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

private theorem vectorImage_crossEntries (hRank : 4 ≤ Fintype.card I) (R : TestAlgebra k)
    (i : Fin (m+1)) :
    ∃ p : Points P.image.val.X R, vectorImageMatrix P R p (.inl (d i)) (.inr (d i)) = -1 ∧
      vectorImageMatrix P R p (.inr (d i)) (.inl (d i)) = -1 := by
  have hc : Fintype.card I = m+1 := (Fintype.card_congr d).symm.trans (Fintype.card_fin _)
  have hm : 4 ≤ m+1 := hc ▸ hRank
  let j : Fin (m+1) := if i.val = 0 then ⟨1, by omega⟩ else 0
  have hij : i ≠ j := by
    intro he
    have h := congrArg Fin.val he
    by_cases h' : i.val = 0
    · simp [j, h'] at h
    · apply h'
      simp [j, h'] at h
  let J : EvenSwitches (m+1) := ⟨{i,j}, by simp [hij]⟩
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  obtain ⟨p, hp⟩ := evenSwitchPoint P d J
  let f : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  let p' := mapPoints f p
  have hmat : vectorImageMatrix P R p' =
      Matrix.reindex (d.sumCongr d) (d.sumCongr d) (signedSwitch (m+1) R J.val) := by
    rw [vectorImageMatrix_map, hp, ← signedSwitch_map f.hom.toRingHom]
    rfl
  refine ⟨p', ?_, ?_⟩
  · rw [hmat]
    change signedSwitch (m+1) R J.val (.inl (d.symm (d i))) (.inr (d.symm (d i))) = -1
    rw [Equiv.symm_apply_apply]
    simp [signedSwitch, J]
  · rw [hmat]
    change signedSwitch (m+1) R J.val (.inr (d.symm (d i))) (.inl (d.symm (d i))) = -1
    rw [Equiv.symm_apply_apply]
    simp [signedSwitch, J]

include d in
private theorem vectorImage_centralizer_isScalar (hRank : 4 ≤ Fintype.card I)
    (R : TestAlgebra k) (X : Matrix (I ⊕ I) (I ⊕ I) R)
    (hX : ∀ (S : TestAlgebra k) (f : R ⟶ S) (p : Points P.image.val.X S),
      Commute (X.map f.hom) (vectorImageMatrix P S p)) :
    ∃ a : R, X = Matrix.diagonal (fun _ => a) := by
  have h₀ : CentralizesDiagonal X := by
    intro S _ f t
    let : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
    let S' : TestAlgebra k := CommAlgCat.of k S
    let f' : R ⟶ S' := CommAlgCat.ofHom { toRingHom := f, commutes' := fun _ => rfl }
    obtain ⟨p, hp⟩ := vectorImage_contains_diagonal P d hRank S' t
    exact hp ▸ hX S' f' p
  let a (i : I ⊕ I) : R := X i i
  have hdiag : X = diagonal a := by
    ext i j
    by_cases h : i = j
    · subst j
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ h]
      exact offDiagonal_eq_zero_of_centralizes h₀ h
  have hc (p : Points P.image.val.X R) : Commute (diagonal a) (vectorImageMatrix P R p) := by
    have he := hX R (𝟙 R) p
    change Commute (X.map id) (vectorImageMatrix P R p) at he
    rwa [Matrix.map_id, hdiag] at he
  have hleft (i j : Fin (m+1)) : a (.inl (d i)) = a (.inl (d j)) := by
    obtain ⟨p, hp⟩ := vectorImage_leftEntry P d hRank R i j
    exact commute_diagonal_entry a _ (hc p) (hp ▸ isUnit_one)
  have hpaired (i : Fin (m+1)) : a (.inl (d i)) = a (.inr (d i)) := by
    obtain ⟨p, hp, _⟩ := vectorImage_crossEntries P d hRank R i
    exact commute_diagonal_entry a _ (hc p) (hp ▸ isUnit_one.neg)
  refine ⟨a (.inl (d 0)), hdiag.trans (congrArg Matrix.diagonal ?_)⟩
  funext j
  rcases j with j | j
  · obtain ⟨i, rfl⟩ := d.surjective j
    exact hleft i 0
  · obtain ⟨i, rfl⟩ := d.surjective j
    exact (hpaired i).symm.trans (hleft i 0)

private theorem isolate_coordinate {J F : Type u} [Fintype J] [DecidableEq J] [Field F]
    (W : Submodule F (J → F)) {v : J → F} (hv : v ∈ W)
    {r : Fˣ} (hr : (r : F) ≠ 1) (hri : (r : F) ≠ ↑r⁻¹)
    (f : J → F) {j j' : J} (_hjj' : j ≠ j') (hj : f j = r) (hj' : f j' = ↑r⁻¹)
    (hf : ∀ i, i ≠ j → i ≠ j' → f i = 1)
    (hstable : ∀ x ∈ W, diagonal f *ᵥ x ∈ W) (hnz : v j ≠ 0) :
    Pi.single j 1 ∈ W := by
  let z := diagonal f *ᵥ v - v
  have hz : z ∈ W := W.sub_mem (hstable v hv) hv
  have hz' (i : J) : z i = (f i - 1) * v i := by
    simp only [z, Pi.sub_apply, mulVec_diagonal, sub_mul, one_mul]
  let w := diagonal f *ᵥ z - (↑r⁻¹ : F) • z
  have hw : w ∈ W := W.sub_mem (hstable z hz) (W.smul_mem _ hz)
  let c := ((r : F) - ↑r⁻¹) * ((r : F) - 1) * v j
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hri) (sub_ne_zero.mpr hr)) hnz
  have he (i : J) : w i = (f i - (↑r⁻¹ : F)) * z i := by
    simp only [w, Pi.sub_apply, mulVec_diagonal, Pi.smul_apply, smul_eq_mul, sub_mul]
  have hw' : w = c • Pi.single j 1 := by
    funext i
    rw [he, hz', Pi.smul_apply, smul_eq_mul]
    by_cases h : i = j
    · subst i
      rw [Pi.single_eq_same, hj, mul_one]
      exact (mul_assoc _ _ _).symm
    · rw [Pi.single_eq_of_ne h, mul_zero]
      by_cases h' : i = j'
      · rw [h', hj', sub_self, zero_mul]
      · rw [hf i h h', sub_self, zero_mul, mul_zero]
  rw [hw'] at hw
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using W.smul_mem c⁻¹ hw

private theorem exists_separating_scale (F : Type u) [Field F] [Infinite F] :
    ∃ r : Fˣ, (r : F) ≠ 1 ∧ (r : F) ≠ ↑r⁻¹ := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset F)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  let r := Units.mk0 x hx.1
  refine ⟨r, hx.2.1, ?_⟩
  intro he
  have hsq : x * x = 1 := by
    change (r : F) * (r : F) = 1
    nth_rw 2 [he]
    exact Units.mul_inv r
  have h : (x - 1) * (x + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp h with h | h
  · exact hx.2.1 (sub_eq_zero.mp h)
  · exact hx.2.2 (eq_neg_of_add_eq_zero_left h)

include d in
private theorem vectorImage_invariant_eq_top {F : Type u} [Field F] [Infinite F]
    (A : Algebra k F) (hRank : 4 ≤ Fintype.card I) (W : Submodule F (I ⊕ I → F))
    (hstable : ∀ p : Points P.image.val.X (@CommAlgCat.of k _ F _ A), ∀ v ∈ W,
      vectorImageMatrix P (@CommAlgCat.of k _ F _ A) p *ᵥ v ∈ W)
    {v : I ⊕ I → F} (hv : v ∈ W) (hnz : v ≠ 0) : W = ⊤ := by
  let R : TestAlgebra k := @CommAlgCat.of k _ F _ A
  obtain ⟨r, hr, hri⟩ := exists_separating_scale F
  have extract {x : I ⊕ I → F} (hx : x ∈ W) (j : I ⊕ I) (h : x j ≠ 0) :
      Pi.single j 1 ∈ W := by
    rcases j with i | i
    · let t : I → Fˣ := Pi.mulSingle i r
      let f : I ⊕ I → F := Sum.elim (fun a => ↑(t a)) (fun a => ↑(t a)⁻¹)
      obtain ⟨p, hp⟩ := vectorImage_contains_diagonal P d hRank R t
      have hs (y : I ⊕ I → F) (hy : y ∈ W) : diagonal f *ᵥ y ∈ W := by
        have hpy := hstable p y hy
        rwa [hp] at hpy
      apply isolate_coordinate W hx hr hri f (j' := Sum.inr i) (by simp) _ _ _ hs h
      · simp [f, t]
      · simp [f, t]
      · rintro (a | a) ha ha'
        · have hne : a ≠ i := fun he => ha (congrArg Sum.inl he)
          simp [f, t, hne]
        · have hne : a ≠ i := fun he => ha' (congrArg Sum.inr he)
          simp [f, t, hne]
    · let t : I → Fˣ := Pi.mulSingle i r⁻¹
      let f : I ⊕ I → F := Sum.elim (fun a => ↑(t a)) (fun a => ↑(t a)⁻¹)
      obtain ⟨p, hp⟩ := vectorImage_contains_diagonal P d hRank R t
      have hs (y : I ⊕ I → F) (hy : y ∈ W) : diagonal f *ᵥ y ∈ W := by
        have hpy := hstable p y hy
        rwa [hp] at hpy
      apply isolate_coordinate W hx hr hri f (j' := Sum.inl i) (by simp) _ _ _ hs h
      · simp [f, t]
      · simp [f, t]
      · rintro (a | a) ha ha'
        · have hne : a ≠ i := fun he => ha' (congrArg Sum.inl he)
          simp [f, t, hne]
        · have hne : a ≠ i := fun he => ha (congrArg Sum.inr he)
          simp [f, t, hne]
  have transport {i j : I ⊕ I} (hi : Pi.single i (1 : F) ∈ W)
      (p : Points P.image.val.X R) (hp : vectorImageMatrix P R p j i ≠ 0) :
      Pi.single j 1 ∈ W := by
    apply extract (hstable p _ hi)
    rw [mulVec_single_one]
    exact hp
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hnz (funext h)
  have h₁ : ∃ i : Fin (m+1), Pi.single (Sum.inl (d i)) (1 : F) ∈ W := by
    rcases j with a | a
    · obtain ⟨i, rfl⟩ := d.surjective a
      exact ⟨i, extract hv _ hj⟩
    · obtain ⟨i, rfl⟩ := d.surjective a
      obtain ⟨p, hp, _⟩ := vectorImage_crossEntries P d hRank R i
      exact ⟨i, transport (extract hv _ hj) p (hp.symm ▸ neg_ne_zero.mpr one_ne_zero)⟩
  obtain ⟨i, hi⟩ := h₁
  have hleft (j : Fin (m+1)) : Pi.single (Sum.inl (d j)) (1 : F) ∈ W := by
    obtain ⟨p, hp⟩ := vectorImage_leftEntry P d hRank R j i
    exact transport hi p (hp.symm ▸ one_ne_zero)
  apply top_unique
  rw [← (Pi.basisFun F (I ⊕ I)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rw [Pi.basisFun_apply]
  rcases j with j | j
  · obtain ⟨a, rfl⟩ := d.surjective j
    exact hleft a
  · obtain ⟨a, rfl⟩ := d.surjective j
    obtain ⟨p, _, hp⟩ := vectorImage_crossEntries P d hRank R a
    exact transport (hleft a) p (hp.symm ▸ neg_ne_zero.mpr one_ne_zero)

section VectorRadical

open Opposite
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup SubgroupSections)
open Specs.GeometricRadicals (GeometricGroup geometricUnipotentRadical IsReductive IsTrivialSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup IsUnipotent)
open Specs.StandardGroups (generalLinearPoints)
open _root_.LinearAlgebraicGroups.RationalRepresentations
open private groupBaseChangePointIso from LinearAlgebraicGroups.Affine.RationalRepresentations
open private affineBaseTerminal from LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private sections_normal trivial_of_subsingleton_sections
  from LinearAlgebraicGroups.Reductive.GeometricRadicals

private def vectorUnitAction :
    (groupPointsFunctor k).obj P.image.val ⟶ generalLinearPoints (k := k) (I ⊕ I) where
  app R := GrpCat.ofHom <|
    (orthogonalMatrices I R).subtype.comp
      ((P.orthogonal.points R).toMonoidHom.comp (((groupPointsFunctor k).map P.inclusion).app R).hom)
  naturality R S f := by
    apply GrpCat.ext
    intro a
    apply Units.ext
    exact vectorImageMatrix_map P f a

private def vectorUnitActionOver (F : Type u) [Field F] [Algebra k F] :
    (groupPointsFunctor F).obj ((groupBaseChange k F).obj P.image.val) ⟶
      generalLinearPoints (k := F) (I ⊕ I) :=
  (groupBaseChangePointIso F P.image.val).hom ≫
    ((Functor.whiskeringLeft _ _ _).obj (restrictTestAlgebra k F)).map (vectorUnitAction P)

private theorem vectorUnitAction_injective (R : TestAlgebra k) :
    Function.Injective ((vectorUnitAction P).app R) := by
  intro a b h
  let : IsClosedImmersion P.inclusion.hom.hom.left := P.closed
  let : Mono P.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono P.inclusion.hom.hom).mp
  apply (P.orthogonal.points R).injective
  exact Subtype.ext h

private theorem unitAction_has_fixed_vector {F J : Type u} [Field F] [Fintype J]
    [DecidableEq J] [Nonempty J] {G : AffineAlgebraicGroup F} (N : ClosedSubgroup G.val)
    (hN : IsUnipotent (closedSubgroupAlgebraicGroup N))
    (ρ : (groupPointsFunctor F).obj G.val ⟶ generalLinearPoints (k := F) J) :
    ∃ v : J → F, v ≠ 0 ∧ ∀ a : Points N.group.X (CommAlgCat.of F F),
      (ρ.app _ (a ≫ N.inclusion.hom.hom)).val *ᵥ v = v := by
  obtain ⟨A, ⟨e⟩, h⟩ := hN
  let R := CommAlgCat.of F F
  let b := Pi.basisFun F J
  let fm := hopfSpecPointIso A ≪≫ (groupPointsFunctor F).mapIso e
  let α := fm.hom ≫ (groupPointsFunctor F).map N.inclusion ≫ ρ
  let E := pointsCoactionEquiv A b
  let coact := E α
  obtain ⟨v, hv, hinv⟩ := h (J → F) coact
  refine ⟨v, hv, fun a => ?_⟩
  let g := (fm.app R).groupIsoToMulEquiv.symm a
  have hga := (fm.app R).groupIsoToMulEquiv.apply_symm_apply a
  have hval := congrArg (fun β => (β.app R g).val) (E.symm_apply_apply α)
  change g.ofConv.mapMatrix (coefficients A b coact) =
    (ρ.app R (fm.hom.app R g ≫ N.inclusion.hom.hom)).val at hval
  rw [show fm.hom.app R g = a from hga] at hval
  let r := TensorProduct.rid F (J → F)
  have he : r.toLinearMap.comp (evaluate A coact g.ofConv) =
      (g.ofConv.mapMatrix (coefficients A b coact)).mulVecLin := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, evaluate, coaction_apply_basis, map_sum,
      LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, r]
    ext i
    simp [b, Pi.basisFun_apply, Pi.single_apply, mulVec, dotProduct, mul_ite]
  have hv' := (invariantKernel A coact v).mpr hinv R g.ofConv
  have hh := LinearMap.congr_fun he v
  change r (evaluate A coact g.ofConv v) =
    (g.ofConv.mapMatrix (coefficients A b coact)) *ᵥ v at hh
  rw [hv', TensorProduct.rid_tmul, one_smul, hval] at hh
  exact hh.symm

include d in
private theorem vectorImage_reductive (hRank : 4 ≤ Fintype.card I) :
    IsReductive P.image := by
  obtain ⟨_, _, hs⟩ := splitSpinGeometry k I hRank P
  refine ⟨hs, (splitSpinIdentityComponent k I hRank P).1, ?_⟩
  let F := AlgebraicClosure k
  let G := GeometricGroup P.image
  let R := CommAlgCat.of F F
  let S := (restrictTestAlgebra k F).obj R
  let Q := geometricUnipotentRadical P.image
  let U := closedSubgroupAlgebraicGroup (G := G) Q
  let ρ := vectorUnitActionOver P F
  let M : Points G.val.X R →* Matrix.GeneralLinearGroup (I ⊕ I) F := (ρ.app R).hom
  let e := (groupBaseChangePointIso F P.image.val).app R
  have hm (a : Points G.val.X R) : (M a).val = vectorImageMatrix P S (e.hom a) := rfl
  have hM : Function.Injective M :=
    (vectorUnitAction_injective P S).comp e.groupIsoToMulEquiv.injective
  have hQ := GeometricRadicals.geometricUnipotentRadicalLargest P.image
  have hN : (SubgroupSections Q ((testSpec F).obj (op R))).Normal := sections_normal hQ.1.2.2 _
  have : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v, hv, hf⟩ := unitAction_has_fixed_vector Q hQ.2.1 ρ
  let H := SubgroupSections Q ((testSpec F).obj (op R))
  let W : Submodule F (I ⊕ I → F) :=
    { carrier := {w | ∀ y ∈ H, (M y).val *ᵥ w = w}
      zero_mem' := fun y _ => Matrix.mulVec_zero _
      add_mem' := fun {x z} hx hz y hy => by rw [Matrix.mulVec_add, hx y hy, hz y hy]
      smul_mem' := fun c x hx y hy => by rw [Matrix.mulVec_smul, hx y hy] }
  have hvW : v ∈ W := by
    rintro _ ⟨a, rfl⟩
    exact hf a
  have hstable (a : Points G.val.X R) (w : I ⊕ I → F) (hw : w ∈ W) :
      (M a).val *ᵥ w ∈ W := by
    intro y hy
    have h := hw (a⁻¹ * y * (a⁻¹)⁻¹) (hN.conj_mem y hy a⁻¹)
    rw [inv_inv, map_mul, map_mul, map_inv] at h
    change (M y).val *ᵥ ((M a).val *ᵥ w) = _
    calc
      _ = (M y * M a).val *ᵥ w := Matrix.mulVec_mulVec _ _ _
      _ = (M a * ((M a)⁻¹ * M y * M a)).val *ᵥ w := by
        have he : M y * M a = M a * ((M a)⁻¹ * M y * M a) := by group
        rw [he]
      _ = (M a).val *ᵥ w := by rw [Units.val_mul, ← Matrix.mulVec_mulVec, h]
  have hW : W = ⊤ := by
    apply vectorImage_invariant_eq_top P d (F := F) S.algebra hRank W ?_ hvW hv
    intro p w hw
    let a : Points G.val.X R := e.inv p
    have ha : e.hom a = p := e.groupIsoToMulEquiv.apply_symm_apply p
    have hmat := (hm a).trans (congrArg (vectorImageMatrix P S) ha)
    have h := hstable a w hw
    rw [hmat] at h
    exact h
  have hpoints (a : Points Q.group.X R) : a = 1 := by
    let : IsClosedImmersion Q.inclusion.hom.hom.left := Q.isClosedImmersion
    let : Mono Q.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono Q.inclusion.hom.hom).mp
    rw [MonObj.one_comp]
    apply hM
    rw [map_one]
    apply Units.ext
    ext i j
    have hb : Pi.single j (1 : F) ∈ W := by rw [hW]; trivial
    have hx := hb (a ≫ Q.inclusion.hom.hom) ⟨a, rfl⟩
    have hy := congrFun hx i
    rw [Matrix.mulVec_single_one] at hy
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using hy
  let t : (testSpec F).obj (op R) ≅ 𝟙_ (SchemeOver F) :=
    (affineBaseTerminal F).uniqueUpToIso isTerminalTensorUnit
  let : Subsingleton ((𝟙_ (SchemeOver F)) ⟶ U.val.X) := ⟨fun a b =>
    (cancel_epi t.hom).mp ((hpoints (t.hom ≫ a)).trans (hpoints (t.hom ≫ b)).symm)⟩
  exact trivial_of_subsingleton_sections U hQ.1.1

end VectorRadical

section VectorCentre

open Opposite
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (IsReductive IsSemisimple)
open Albert.SpinFunctor (muTwoScheme muTwoSchemePoints muTwoPoints_natural)
open private muTwoObject muTwoSchemePoints_onSpec from LinearAlgebraicGroups.Albert.SpinFunctor
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private closedImmersion_of_injective_test_points from LinearAlgebraicGroups.Classification.RationalRealization
open private semisimple_of_finite_cover from LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo

private theorem muTwoValue_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (x : Points (muTwoScheme k).X R) :
    (muTwoSchemePoints k S (mapPoints f x)).val.val =
      f.hom (muTwoSchemePoints k R x).val.val := by
  let F := algSpec (CommRingCat.of k)
  let a : op R ⟶ muTwoObject k := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x
  have ha : F.map a = x := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hmap : mapPoints f x = F.map (f.op ≫ a) := by
    change F.map f.op ≫ x = F.map (f.op ≫ a)
    exact (congrArg (F.map f.op ≫ ·) ha.symm).trans (F.map_comp _ _).symm
  rw [hmap, ← ha, muTwoSchemePoints_onSpec, muTwoSchemePoints_onSpec]
  exact muTwoPoints_natural f.hom a.unop.hom

include d in
private theorem centre_matrix_scalar (hRank : 4 ≤ Fintype.card I)
    (Z : ClosedSubgroup P.image.val)
    (hZ : RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 P.image.val) z))
    (R : TestAlgebra k) (x : Points Z.group.X R) :
    ∃ a : R, vectorImageMatrix P R (x ≫ Z.inclusion.hom.hom) = diagonal (fun _ => a) ∧ a ^ 2 = 1 := by
  let p := x ≫ Z.inclusion.hom.hom
  have hp := (hZ _ p).mpr ⟨x, rfl⟩
  have h (S : TestAlgebra k) (f : R ⟶ S) (q : Points P.image.val.X S) :
      Commute ((vectorImageMatrix P R p).map f.hom) (vectorImageMatrix P S q) := by
    have hc := (centralizes_iff _ _).mp hp _ ((testSpec k).map f.op) q
    have hc' : Commute (mapPoints f p) q := by
      change Commute (mapPoints f p) (q ≫ 𝟙 _) at hc
      simpa only [Category.comp_id] using hc
    have he := hc'.map ((vectorUnitAction P).app S).hom
    have he' := he.map (Units.coeHom (Matrix (I ⊕ I) (I ⊕ I) S))
    change Commute (vectorImageMatrix P S (mapPoints f p)) (vectorImageMatrix P S q) at he'
    rwa [vectorImageMatrix_map] at he'
  obtain ⟨a, ha⟩ := vectorImage_centralizer_isScalar P d hRank R _ h
  refine ⟨a, ha, ?_⟩
  let x₀ : I ⊕ I → R := Sum.elim (Pi.single (d 0) 1) (Pi.single (d 0) 1)
  have hx₀ : Specs.Arithmetic.OddSpinModels.hyperbolicForm I R x₀ = 1 := by
    rw [hyperbolicForm_apply]
    simp [x₀, Pi.single_apply, mul_ite]
  have ha₀ : diagonal (fun _ : I ⊕ I => a) *ᵥ x₀ = a • x₀ := by
    ext i
    simp [mulVec_diagonal]
  have hv := (P.orthogonal.points R (p ≫ P.inclusion.hom.hom)).property x₀
  change Specs.Arithmetic.OddSpinModels.hyperbolicForm I R ((vectorImageMatrix P R p) *ᵥ x₀) =
    Specs.Arithmetic.OddSpinModels.hyperbolicForm I R x₀ at hv
  simpa only [ha, ha₀, QuadraticMap.map_smul, hx₀, smul_eq_mul, mul_one, pow_two] using hv

include d in
private theorem vectorImage_centre_finite (hRank : 4 ≤ Fintype.card I)
    (Z : ClosedSubgroup P.image.val)
    (hZ : RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 P.image.val) z)) :
    IsFinite Z.group.X.hom := by
  let C := closedSubgroupAlgebraicGroup (G := P.image) Z
  let σ (R : TestAlgebra k) (x : Points Z.group.X R) : R :=
    vectorImageMatrix P R (x ≫ Z.inclusion.hom.hom) (.inl (d 0)) (.inl (d 0))
  have hs (R : TestAlgebra k) (x : Points Z.group.X R) :
      vectorImageMatrix P R (x ≫ Z.inclusion.hom.hom) = diagonal (fun _ => σ R x) ∧
        σ R x ^ 2 = 1 := by
    obtain ⟨a, ha, hsq⟩ := centre_matrix_scalar P d hRank Z hZ R x
    have he : σ R x = a := by simp [σ, ha]
    simpa only [he] using And.intro ha hsq
  let r (R : TestAlgebra k) : Points Z.group.X R →* rootsOfUnity 2 R :=
    { toFun := fun x => rootsOfUnity.mkOfPowEq (σ R x) (hs R x).2
      map_one' := by
        apply rootsOfUnity.coe_injective
        change σ R 1 = 1
        have h := (vectorUnitAction P).app R |>.hom.map_one
        have h₁ : vectorImageMatrix P R (1 : Points P.image.val.X R) = 1 :=
          congrArg Units.val h
        simp only [σ, MonObj.one_comp, h₁, Matrix.one_apply_eq]
      map_mul' := fun x y => by
        apply rootsOfUnity.coe_injective
        change σ R (x * y) = σ R x * σ R y
        dsimp only [σ]
        rw [MonObj.mul_comp, vectorImageMatrix_mul, (hs R x).1, (hs R y).1,
          diagonal_mul_diagonal, diagonal_apply_eq]
        simp only [diagonal_apply_eq] }
  let α : (groupPointsFunctor k).obj Z.group ⟶ (groupPointsFunctor k).obj (muTwoScheme k) :=
    { app := fun R => GrpCat.ofHom ((muTwoSchemePoints k R).symm.toMonoidHom.comp (r R))
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro x
        apply (muTwoSchemePoints k S).injective
        apply rootsOfUnity.coe_injective
        change (muTwoSchemePoints k S ((muTwoSchemePoints k S).symm (r S (mapPoints f x)))).val.val =
          (muTwoSchemePoints k S (mapPoints f ((muTwoSchemePoints k R).symm (r R x)))).val.val
        rw [MulEquiv.apply_symm_apply, muTwoValue_natural, MulEquiv.apply_symm_apply]
        change σ S (mapPoints f x) = f.hom (σ R x)
        dsimp only [σ]
        rw [show mapPoints f x ≫ Z.inclusion.hom.hom =
          mapPoints f (x ≫ Z.inclusion.hom.hom) from Category.assoc _ _ _]
        rw [vectorImageMatrix_map]
        rfl }
  let : IsAffine C.val.X.left := C.property.1
  let f := (_root_.LinearAlgebraicGroups.groupHomEquiv C.val (muTwoScheme k) C.property.1).symm α
  have hf := (_root_.LinearAlgebraicGroups.groupHomEquiv C.val (muTwoScheme k) C.property.1).apply_symm_apply α
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  let hfin : IsFinite (muTwoScheme k).X.hom := scalarSubgroup_finite (k := k) (I := I)
  let : IsFinite (muTwoScheme k).X.hom := hfin
  let M : AffineAlgebraicGroup k := ⟨muTwoScheme k, by
    change IsAffine (Spec (CommRingCat.of (Albert.SpinSpecification.muTwoCoordinateRing k)))
    infer_instance, by infer_instance, by infer_instance⟩
  have hi : IsClosedImmersion f.hom.hom.left := by
    apply closedImmersion_of_injective_test_points (G := C) (H := M) f
    intro R x y hxy
    have he := congrArg (fun t => (t.app R x, t.app R y)) hf
    have hx : x ≫ f.hom.hom = (muTwoSchemePoints k R).symm (r R x) := congrArg Prod.fst he
    have hy : y ≫ f.hom.hom = (muTwoSchemePoints k R).symm (r R y) := congrArg Prod.snd he
    change x ≫ f.hom.hom = y ≫ f.hom.hom at hxy
    rw [hx, hy] at hxy
    have hσ : σ R x = σ R y := congrArg (fun t : rootsOfUnity 2 R => t.val.val)
      ((muTwoSchemePoints k R).symm.injective hxy)
    let : IsClosedImmersion Z.inclusion.hom.hom.left := Z.isClosedImmersion
    let : Mono Z.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono Z.inclusion.hom.hom).mp
    apply vectorUnitAction_injective P R
    apply Units.ext
    change vectorImageMatrix P R (x ≫ Z.inclusion.hom.hom) =
      vectorImageMatrix P R (y ≫ Z.inclusion.hom.hom)
    exact (hs R x).1.trans ((congrArg (fun a : R => diagonal (fun _ : I ⊕ I => a)) hσ).trans
      (hs R y).1.symm)
  change IsFinite C.val.X.hom
  rw [← f.hom.hom.w]
  let : IsClosedImmersion f.hom.hom.left := hi
  infer_instance

include d in
private theorem vectorImage_semisimple (hRank : 4 ≤ Fintype.card I) :
    IsSemisimple P.image := by
  let J : ClosedSubgroup P.image.val :=
    ⟨P.image.val, 𝟙 _, by
      change IsClosedImmersion (𝟙 P.image.val.X.left)
      infer_instance⟩
  obtain ⟨Z, hZ⟩ := _root_.LinearAlgebraicGroups.centralizerScheme k P.image J
  change RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 P.image.val) z) at hZ
  exact (Reductive.CentralDerived.semisimpleIffFiniteCentre P.image (vectorImage_reductive P d hRank)
    Z hZ).mpr (vectorImage_centre_finite P d hRank Z hZ)

include d in
private theorem cliffordSpin_semisimple (hRank : 4 ≤ Fintype.card I) :
    IsSemisimple P.spin := by
  obtain ⟨hs, hc, _⟩ := splitSpinGeometry k I hRank P
  exact semisimple_of_finite_cover P.projection (splitSpinCentralIsogeny P) hs hc
    (vectorImage_semisimple P d hRank)

end VectorCentre

open Specs.Pinning (AttachedDatum SplitBorelPair)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.OddSpinModels (evenSum)
open private splitBorelPair from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies

include d in
private theorem splitSpin_has_borel (hRank : 4 ≤ Fintype.card I) :
    ∃ (B : SplitBorelPair k) (D : AttachedDatum B) (e : B.G.val ≅ P.spin.val),
      IsSemisimple B.G ∧ IsSemisimple P.image ∧
      letI := D.comm
      ∃ v : Additive (Cocharacter B.T.group) ≃ₗ[ℤ] evenSum I,
        ∀ (R : TestAlgebra k) (s : Rˣ) (c : Cocharacter B.T.group),
          let a := _root_.LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint c R s
          (P.orthogonal.points R (a ≫ (B.T.inclusion ≫ e.hom ≫ P.projection ≫ P.inclusion).hom.hom)).val.val =
            hyperbolicDiagonal (fun i => s ^ (v (Additive.ofMul c)).val i) := by
  have : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hS := cliffordSpin_semisimple P d hRank
  have hO := vectorImage_semisimple P d hRank
  obtain ⟨T, comm, hsplit, hmax, _, hcoords⟩ := splitSpinDiagonalTorus k I P
  let B := splitBorelPair P.spin (reductive_of_semisimple P.spin hS) T hsplit hmax
  let D := Classification.Pinning.attachedDatum B
  let e : B.G.val ≅ P.spin.val := Iso.refl _
  refine ⟨B, D, e, hS, hO, ?_⟩
  obtain ⟨v, hv⟩ := hcoords
  refine ⟨v, fun R s c => ?_⟩
  have he : (B.T.inclusion ≫ e.hom ≫ P.projection ≫ P.inclusion) =
      T.inclusion ≫ P.projection ≫ P.inclusion := by
    change T.inclusion ≫ 𝟙 P.spin.val ≫ P.projection ≫ P.inclusion = _
    rw [Category.id_comp]
  rw [he]
  exact hv R s c


/-- Scheme-valued commutation with the split vector image forces a scalar. -/
theorem splitVectorCentralizer : SplitVectorCentralizer.{u} := by
  intro k I _ _ _ hRank P R X hX
  let m := Fintype.card I - 1
  let d : Fin (m + 1) ≃ I := (finCongr (by dsimp [m]; omega)).trans (Fintype.equivFin I).symm
  exact vectorImage_centralizer_isScalar P d hRank R X hX

/-- The semisimple split spin group has a Borel pair containing the diagonal
torus with the specified vector cocharacters. -/
theorem splitSpinBorel : SplitSpinBorel.{u} := by
  intro k I _ _ _ hRank P
  let m := Fintype.card I - 1
  let d : Fin (m + 1) ≃ I := (finCongr (by dsimp [m]; omega)).trans (Fintype.equivFin I).symm
  exact splitSpin_has_borel P d hRank

end
end SplitVectorStructure

section VectorDiagonalTorus

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.GeometricRadicals (IsSplitTorus baseChangedSubgroup)
open Specs.CentralIsogenies (IsTorusRestriction)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SymplecticMatrixStructure (hyperbolicDiagonal IsOwnSchemeCentralizer CentralizesDiagonal)
open _root_.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo (spinTorusProjection)
open private orthogonalTorusModel orthogonalTorusModel_comm torusPointsToUnits torusPointsToUnits_natural
  spinTorusProjection_points spinTorusOrthogonalPoints_eval
  from LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
open private offDiagonal_eq_zero_of_centralizes from LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
open private closedImmersion_of_injective_test_points from LinearAlgebraicGroups.Classification.RationalRealization
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private sections_factor_of_affine from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private splitTorus_baseChange from LinearAlgebraicGroups.Classification.CentralIsogenies
open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable (P : SplitSpinVectorImage k I) {m : ℕ} (d : Fin (m+1) ≃ I) (hRank : 4 ≤ Fintype.card I)

local notation "D" => orthogonalTorusModel (k := k) (m + 1)

private theorem vectorMatrix_injective (R : TestAlgebra k) :
    Function.Injective (vectorImageMatrix P R) := fun _ _ h =>
  vectorUnitAction_injective P R (Units.ext h)

private theorem vectorMatrix_one (R : TestAlgebra k) :
    vectorImageMatrix P R 1 = 1 := by
  have h : (1 : Points P.image.val.X R) ≫ P.inclusion.hom.hom = 1 := MonObj.one_comp _
  have h' : P.orthogonal.points R 1 = 1 := (P.orthogonal.points R).map_one
  change (P.orthogonal.points R (1 ≫ P.inclusion.hom.hom)).val.val = _
  rw [h]
  exact congrArg (fun g : orthogonalMatrices I R => g.val.val) h'

omit [Fintype I] in

private theorem hyperbolicDiagonal_injective (R : TestAlgebra k) :
    Function.Injective (hyperbolicDiagonal : (I → Rˣ) → _) := by
  intro s t h
  funext i
  apply Units.ext
  have h' := congrFun₂ h (Sum.inl i) (Sum.inl i)
  simpa only [hyperbolicDiagonal, Matrix.diagonal_apply_eq, Sum.elim_inl] using h'

private theorem hyperbolicDiagonal_mul {R : TestAlgebra k} (t s : I → Rˣ) :
    hyperbolicDiagonal (t * s) = hyperbolicDiagonal t * hyperbolicDiagonal s := by
  simp only [hyperbolicDiagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  rcases i with i | i
  · rfl
  · simp [Pi.mul_apply, mul_comm]

private def vectorDiagonalPoint (R : TestAlgebra k) (t : I → Rˣ) : Points P.image.val.X R :=
  (vectorImage_contains_diagonal P d hRank R t).choose

private theorem vectorDiagonalPoint_matrix (R : TestAlgebra k) (t : I → Rˣ) :
    vectorImageMatrix P R (vectorDiagonalPoint P d hRank R t) = hyperbolicDiagonal t :=
  (vectorImage_contains_diagonal P d hRank R t).choose_spec

private def vectorDiagonalPointHom (R : TestAlgebra k) : (I → Rˣ) →* Points P.image.val.X R where
  toFun := vectorDiagonalPoint P d hRank R
  map_one' := by
    apply vectorMatrix_injective
    rw [vectorDiagonalPoint_matrix, vectorMatrix_one]
    simp [hyperbolicDiagonal]
  map_mul' s t := by
    apply vectorMatrix_injective
    rw [vectorDiagonalPoint_matrix, vectorImageMatrix_mul,
      vectorDiagonalPoint_matrix, vectorDiagonalPoint_matrix, hyperbolicDiagonal_mul]

private def vectorDiagonalNatural :
    (groupPointsFunctor k).obj (D).val ⟶ (groupPointsFunctor k).obj P.image.val where
  app R := GrpCat.ofHom ((vectorDiagonalPointHom P d hRank R).comp
    { toFun := fun a i => torusPointsToUnits (m+1) R a (d.symm i)
      map_one' := by ext i; simp
      map_mul' := by intro a b; ext i; simp })
  naturality R S f := by
    apply GrpCat.ext
    intro a
    change Points (D).val.X R at a
    apply vectorMatrix_injective
    change vectorImageMatrix P S (vectorDiagonalPoint P d hRank S
      (fun i => torusPointsToUnits (m+1) S (mapPoints f a) (d.symm i))) =
      vectorImageMatrix P S (mapPoints f (vectorDiagonalPoint P d hRank R
        (fun i => torusPointsToUnits (m+1) R a (d.symm i))))
    rw [vectorImageMatrix_map, vectorDiagonalPoint_matrix, vectorDiagonalPoint_matrix,
      torusPointsToUnits_natural]
    exact (hyperbolicDiagonal_map f.hom.toRingHom
      (fun i => torusPointsToUnits (m+1) R a (d.symm i))).symm

private def vectorDiagonalInclusion : (D).val ⟶ P.image.val :=
  (AffineAlgebraicGroup.groupHomEquiv D P.image).symm (vectorDiagonalNatural P d hRank)

private theorem vectorDiagonalInclusion_matrix (R : TestAlgebra k) (a : Points (D).val.X R) :
    vectorImageMatrix P R (a ≫ (vectorDiagonalInclusion P d hRank).hom.hom) =
      hyperbolicDiagonal (fun i => torusPointsToUnits (m+1) R a (d.symm i)) := by
  have h := congrArg (fun τ => τ.app R a)
    ((AffineAlgebraicGroup.groupHomEquiv D P.image).apply_symm_apply (vectorDiagonalNatural P d hRank))
  change a ≫ (vectorDiagonalInclusion P d hRank).hom.hom = vectorDiagonalPoint P d hRank R _ at h
  rw [h, vectorDiagonalPoint_matrix]
  rfl

private def vectorDiagonalTorus : ClosedSubgroup P.image.val :=
  ⟨(D).val, vectorDiagonalInclusion P d hRank, by
    apply closedImmersion_of_injective_test_points
    intro R a b h
    have h' := congrArg (vectorImageMatrix P R) h
    change vectorImageMatrix P R (a ≫ (vectorDiagonalInclusion P d hRank).hom.hom) =
      vectorImageMatrix P R (b ≫ (vectorDiagonalInclusion P d hRank).hom.hom) at h'
    rw [vectorDiagonalInclusion_matrix, vectorDiagonalInclusion_matrix] at h'
    have h'' := hyperbolicDiagonal_injective (k := k) (I := I) R h'
    apply (torusPointsToUnits (m+1) R).injective
    funext i
    simpa only [Equiv.symm_apply_apply] using congrFun h'' (d i)⟩

private theorem vectorDiagonalTorus_range (R : TestAlgebra k) (a : Points P.image.val.X R) :
    (∃ b : Points (vectorDiagonalTorus P d hRank).group.X R,
      b ≫ (vectorDiagonalTorus P d hRank).inclusion.hom.hom = a) ↔
      ∃ t : I → Rˣ, vectorImageMatrix P R a = hyperbolicDiagonal t := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, vectorDiagonalInclusion_matrix P d hRank R b⟩
  · rintro ⟨t, ht⟩
    obtain ⟨b, hb⟩ := (torusPointsToUnits (k := k) (m+1) R).surjective (fun i => t (d i))
    refine ⟨b, vectorMatrix_injective P R ?_⟩
    change vectorImageMatrix P R (b ≫ (vectorDiagonalInclusion P d hRank).hom.hom) =
      vectorImageMatrix P R a
    rw [vectorDiagonalInclusion_matrix, ht, hb]
    simp only [Equiv.apply_symm_apply]

private theorem vectorDiagonal_isOwnSchemeCentralizer :
    IsOwnSchemeCentralizer (vectorDiagonalTorus P d hRank) := by
  intro R a
  change Points P.image.val.X R at a
  constructor
  · intro h
    have hh : CentralizesDiagonal (vectorImageMatrix P R a) := by
      intro S _ f t
      let : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
      let U : TestAlgebra k := CommAlgCat.of k S
      let f' : R ⟶ U := CommAlgCat.ofHom { toRingHom := f, commutes' := fun _ => rfl }
      obtain ⟨q, hq⟩ := vectorImage_contains_diagonal P d hRank U t
      obtain ⟨b, hb⟩ := (vectorDiagonalTorus_range P d hRank U q).mpr ⟨t, hq⟩
      have hc := h U f' b
      change Commute (mapPoints f' a) (b ≫ (vectorDiagonalTorus P d hRank).inclusion.hom.hom) at hc
      rw [hb] at hc
      have hv := congrArg (vectorImageMatrix P U) hc.eq
      rw [vectorImageMatrix_mul, vectorImageMatrix_mul, hq, vectorImageMatrix_map] at hv
      exact hv
    exact (vectorDiagonalTorus_range P d hRank R a).mpr
      (orthogonal_eq_hyperbolicDiagonal _ (fun _ _ hij => offDiagonal_eq_zero_of_centralizes hh hij))
  · rintro ⟨b, rfl⟩ S f z
    let T := vectorDiagonalTorus P d hRank
    change Points (D).val.X R at b
    change Points (D).val.X S at z
    have h : Commute (mapPoints f b) z := by
      show mapPoints f b * z = z * mapPoints f b
      apply (torusPointsToUnits (m+1) S).injective
      rw [map_mul, map_mul, mul_comm]
    exact h.map (IsMonHom.monoidHom T.inclusion.hom.hom _)

private theorem vectorDiagonal_isGeometricallyMaximal :
    IsGeometricallyMaximal (vectorDiagonalTorus P d hRank) := by
  let T := vectorDiagonalTorus P d hRank
  let K := AlgebraicClosure k
  let G' := Specs.Unipotent.baseChangedAlgebraicGroup K P.image
  let : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  have hK : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) (fieldSpecMap k K)
      T.inclusion.hom.hom T.isClosedImmersion
  let T' := baseChangedSubgroup K T hK
  have hT : IsSplitTorus T.group := ⟨m+1, ⟨Iso.refl _⟩⟩
  have hT' : IsSplitTorus T'.group := splitTorus_baseChange K hT
  have hComm := CentralFrobeniusDescent.torus_commutative
    (Specs.Unipotent.closedSubgroupAlgebraicGroup (G := G') T') (isTorus_of_split hT')
  exact ⟨hK, maximalTorus_of_ownCentralizer (G := G') hT'
    (ownCentralizer_baseChange T (vectorDiagonal_isOwnSchemeCentralizer P d hRank) K hK hComm)⟩

variable [LinearOrder (I ⊕ I)]

private theorem vectorDiagonal_restriction_commutes :
    spinTorusProjection m ≫ (vectorDiagonalTorus P d hRank).inclusion =
      (splitDiagonalTorus P d).inclusion ≫ P.projection := by
  apply Grp.hom_ext
  apply hom_ext_of_points (D).property.1
  intro R a
  change a ≫ (spinTorusProjection m).hom.hom ≫ (vectorDiagonalInclusion P d hRank).hom.hom =
    a ≫ (splitDiagonalTorus P d).inclusion.hom.hom ≫ P.projection.hom.hom
  simp only [← Category.assoc]
  apply vectorMatrix_injective
  rw [vectorDiagonalInclusion_matrix, spinTorusProjection_points, spinTorusOrthogonalPoints_eval]
  change _ = vectorImageMatrix P R ((a ≫ (diagonalSpinInclusion P d).hom.hom) ≫ P.projection.hom.hom)
  rw [diagonalSpinInclusion_point, diagonalSpinPoint_matrix, reindex_middle_diagonal]

private theorem vectorDiagonal_restriction :
    IsTorusRestriction P.projection (T := splitDiagonalTorus P d) (S := vectorDiagonalTorus P d hRank)
      (spinTorusProjection m) := by
  let T := splitDiagonalTorus P d
  let S := vectorDiagonalTorus P d hRank
  let f : T.group.X ⟶ S.group.X := (spinTorusProjection (k := k) m).hom.hom
  let t := T.inclusion.hom.hom
  let s := S.inclusion.hom.hom
  let p := P.projection.hom.hom
  have hcomm := vectorDiagonal_restriction_commutes P d hRank
  have hw : f ≫ s = t ≫ p := congrArg (fun a => a.hom.hom) hcomm
  refine ⟨hcomm, ?_⟩
  let Q := pullback s p
  have hQ := IsPullback.of_hasPullback s p
  let u : T.group.X ⟶ Q := hQ.lift f t hw
  have hu₁ : u ≫ pullback.fst s p = f := hQ.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd s p = t := hQ.lift_snd _ _ _
  have : IsAffine S.group.X.left := (D).property.1
  have : IsAffine P.spin.val.X.left := P.spin.property.1
  have : IsAffine P.image.val.X.left := P.image.property.1
  have hQ' : IsPullback (pullback.fst s p).left (pullback.snd s p).left s.left p.left :=
    hQ.map (Over.forget (Spec (CommRingCat.of k)))
  have hA : IsAffine Q.left := IsAffine.of_isPullback hQ'
  obtain ⟨v, hv⟩ := sections_factor_of_affine T hA (pullback.snd s p) (by
    intro R q
    let b : Points S.group.X R := q ≫ pullback.fst s p
    let a : Points P.spin.val.X R := q ≫ pullback.snd s p
    have hq : b ≫ s = a ≫ p := by
      simpa only [b, a, Category.assoc] using congrArg (q ≫ ·) hQ.w
    have hb := vectorDiagonalInclusion_matrix P d hRank R b
    change vectorImageMatrix P R (b ≫ s) =
      hyperbolicDiagonal (fun i => torusPointsToUnits (m+1) R b (d.symm i)) at hb
    apply (splitDiagonalTorus_range P d R a).mpr
    refine ⟨torusPointsToUnits (m+1) R b, ?_⟩
    rw [reindex_middle_diagonal, ← hq]
    exact hb)
  change Q ⟶ T.group.X at v
  change v ≫ t = pullback.snd s p at hv
  let : IsClosedImmersion t.left := T.isClosedImmersion
  let : IsClosedImmersion s.left := S.isClosedImmersion
  let : Mono t := Over.mono_of_mono_left _
  let : Mono s := Over.mono_of_mono_left _
  have hv₁ : v ≫ f = pullback.fst s p := by
    apply (cancel_mono s).mp
    rw [Category.assoc, hw, ← Category.assoc, hv, hQ.w]
  have huv : u ≫ v = 𝟙 T.group.X := by
    apply (cancel_mono t).mp
    rw [Category.assoc, hv, hu₂, Category.id_comp]
  have hvu : v ≫ u = 𝟙 Q := by
    apply hQ.hom_ext
    · rw [Category.assoc, hu₁, hv₁, Category.id_comp]
    · rw [Category.assoc, hu₂, hv, Category.id_comp]
  have hPB := IsPullback.of_iso_pullback ⟨hw⟩ ⟨u, v, huv, hvu⟩ hu₁ hu₂
  have hL := hPB.map (Over.forget (Spec (CommRingCat.of k)))
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) hL.flip P.flat,
    MorphismProperty.of_isPullback (P := @Surjective) hL.flip P.surjective⟩


/-- The vector projection restricts to an isogeny between the two
geometrically maximal diagonal tori. -/
theorem splitSpinTorusRestriction : SplitSpinTorusRestriction.{u} := by
  intro k I _ _ _ hRank P
  let m := Fintype.card I - 1
  let d : Fin (m + 1) ≃ I := (finCongr (by dsimp [m]; omega)).trans (Fintype.equivFin I).symm
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  refine ⟨splitDiagonalTorus P d, vectorDiagonalTorus P d hRank,
    spinTorusProjection m, splitDiagonalTorus_isSplit P d,
    splitDiagonalTorus_isGeometricallyMaximal P d, ⟨m + 1, ⟨Iso.refl _⟩⟩,
    vectorDiagonal_isGeometricallyMaximal P d hRank, vectorDiagonal_restriction P d hRank,
    vectorDiagonalTorus_range P d hRank⟩

end

end VectorDiagonalTorus

section VectorTangent

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open _root_.LinearAlgebraicGroups.Specs (Lie)
open private infinitesimalMatrix det_infinitesimalMatrix from LinearAlgebraicGroups.Affine.LieLeftExact

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable (P : SplitSpinVectorImage k I)

private abbrev TangentRing (k : Type u) [Field k] : TestAlgebra k :=
  CommAlgCat.of k (DualNumber k)

private abbrev vectorTangentMatrix (v : Lie k P.image.val) : Matrix (I ⊕ I) (I ⊕ I) k :=
  (vectorImageMatrix P (TangentRing k) v.toMul.val).map TrivSqZeroExt.snd

private theorem infinitesimal_reduction (M : Matrix (I ⊕ I) (I ⊕ I) k) :
    (infinitesimalOrthogonalMatrix M).map (dualReduction k).hom = 1 := rfl

private theorem vectorTangentMatrix_value (v : Lie k P.image.val) :
    vectorImageMatrix P (TangentRing k) v.toMul.val =
      infinitesimalOrthogonalMatrix (vectorTangentMatrix P v) := by
  have h := vectorImageMatrix_map P (dualReduction k) v.toMul.val
  change vectorImageMatrix P (CommAlgCat.of k k) (reduceTangentPoints P.image.val v.toMul.val) = _ at h
  rw [v.toMul.property] at h
  change vectorImageMatrix P (CommAlgCat.of k k) (1 : Points P.image.val.X (CommAlgCat.of k k)) = _ at h
  rw [vectorMatrix_one] at h
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext
  · exact congrFun₂ h.symm i j
  · rfl

private theorem vectorTangentMatrix_injective :
    Function.Injective (vectorTangentMatrix P) := by
  intro v w h
  apply Subtype.ext
  change v.toMul.val = w.toMul.val
  apply vectorUnitAction_injective P (TangentRing k)
  apply Units.ext
  change vectorImageMatrix P (TangentRing k) v.toMul.val =
    vectorImageMatrix P (TangentRing k) w.toMul.val
  rw [vectorTangentMatrix_value, vectorTangentMatrix_value, h]

private theorem infinitesimal_det_unit {J : Type u} [Fintype J] [DecidableEq J]
    (M : Matrix J J k) : IsUnit (infinitesimalMatrix M).det := by
  rw [det_infinitesimalMatrix]
  exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr isUnit_one

private theorem infinitesimalOrthogonal_top (M : Matrix (I ⊕ I) (I ⊕ I) k) :
    (infinitesimalOrthogonalMatrix M).toBlocks₁₁ = infinitesimalMatrix M.toBlocks₁₁ := by
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext
  · change (1 : Matrix (I ⊕ I) (I ⊕ I) k) (Sum.inl i) (Sum.inl j) = (1 : Matrix I I k) i j
    simp [Matrix.one_apply]
  · rfl

private theorem vectorTangentMatrix_surjective (hRank : 4 ≤ Fintype.card I)
    (M : Matrix (I ⊕ I) (I ⊕ I) k)
    (hM : ∀ x, hyperbolicForm I (DualNumber k) (infinitesimalOrthogonalMatrix M *ᵥ x) =
      hyperbolicForm I (DualNumber k) x) :
    ∃ v : Lie k P.image.val, vectorTangentMatrix P v = M := by
  let R := TangentRing k
  have hUnit : IsUnit (infinitesimalOrthogonalMatrix M) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (infinitesimal_det_unit M)
  let g : orthogonalMatrices I R := ⟨hUnit.unit, by
    change ∀ x, hyperbolicForm I (DualNumber k) (hUnit.unit.val *ᵥ x) = _
    rw [hUnit.unit_spec]
    exact hM⟩
  let a : Points P.orthogonal.group.val.X R := (P.orthogonal.points R).symm g
  have ha : (P.orthogonal.points R a).val.val = infinitesimalOrthogonalMatrix M := by
    rw [show (P.orthogonal.points R a) = g from (P.orthogonal.points R).apply_symm_apply _]
    exact hUnit.unit_spec
  have hd : IsUnit (P.orthogonal.points R a).val.val.toBlocks₁₁.det := by
    rw [ha, infinitesimalOrthogonal_top]
    exact infinitesimal_det_unit _
  obtain ⟨b, hb⟩ := splitSpinChartInImage k I hRank P R a hd
  have hMb : vectorImageMatrix P R b = infinitesimalOrthogonalMatrix M :=
    (congrArg (fun p : Points P.orthogonal.group.val.X R => (P.orthogonal.points R p).val.val) hb).trans ha
  have ht : reduceTangentPoints P.image.val b = 1 := by
    apply vectorUnitAction_injective P _
    apply Units.ext
    change vectorImageMatrix P (CommAlgCat.of k k) (reduceTangentPoints P.image.val b) =
      vectorImageMatrix P (CommAlgCat.of k k) 1
    rw [vectorMatrix_one]
    exact (vectorImageMatrix_map P (dualReduction k) b).trans
      ((congrArg (fun X : Matrix (I ⊕ I) (I ⊕ I) (DualNumber k) => X.map (dualReduction k).hom) hMb).trans
        (infinitesimal_reduction M))
  refine ⟨⟨b, ht⟩, ?_⟩
  exact congrArg (·.map TrivSqZeroExt.snd) hMb

private theorem vectorTangentMatrix_preserves (v : Lie k P.image.val) :
    ∀ x, hyperbolicForm I (DualNumber k) (infinitesimalOrthogonalMatrix (vectorTangentMatrix P v) *ᵥ x) =
      hyperbolicForm I (DualNumber k) x := by
  have h := (P.orthogonal.points (TangentRing k) (v.toMul.val ≫ P.inclusion.hom.hom)).property
  change ∀ x, hyperbolicForm I (DualNumber k) (vectorImageMatrix P (TangentRing k) v.toMul.val *ᵥ x) = _ at h
  rwa [vectorTangentMatrix_value] at h


/-- The vector image has the full tangent space of the hyperbolic
quadratic-form equations. -/
theorem splitVectorTangent : SplitVectorTangent.{u} := by
  intro k I _ _ _ hRank P R q
  let f : Lie k P.image.val →
      {X : Matrix (I ⊕ I) (I ⊕ I) k //
        ∀ x, q (infinitesimalOrthogonalMatrix X *ᵥ x) = q x} :=
    fun v => ⟨vectorTangentMatrix P v, vectorTangentMatrix_preserves P v⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact vectorTangentMatrix_injective P (congrArg Subtype.val h)
    · intro X
      obtain ⟨v, hv⟩ := vectorTangentMatrix_surjective P hRank X.val X.property
      exact ⟨v, Subtype.ext hv⟩
  exact ⟨Equiv.ofBijective f hf, vectorTangentMatrix_value P⟩

end

end VectorTangent

section VectorRoots
open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup Lie)
open Specs.AdjointRepresentation (GroupPoints constants dualMap scale)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue pairing)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.SymplecticMatrixStructure (hyperbolicDiagonal)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.AbstractPairing (Datum Root)
open private orthogonalTorusModel torusPointsToUnits orthogonalTorusModel_comm
  characterCoordinates cocharacterCoordinates characterCoordinates_evaluation pairing_coordinates
  cocharacterExponents_point from LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable (P : SplitSpinVectorImage k I) {m : ℕ} (d : Fin (m + 1) ≃ I)
variable (hRank : 4 ≤ Fintype.card I)

local notation "S" => vectorDiagonalTorus P d hRank

private def signedScale {R : Type u} [CommRing R] (t : I → Rˣ) (i : I ⊕ I) : Rˣ :=
  i.elim t (fun j => (t j)⁻¹)

omit [Fintype I] in
private theorem hyperbolicDiagonal_eq_signedScale {R : Type u} [CommRing R] (t : I → Rˣ) :
    hyperbolicDiagonal t = diagonal (fun i : I ⊕ I => (signedScale t i : R)) := by
  unfold hyperbolicDiagonal
  congr 1
  funext i
  cases i <;> rfl

private def planeWeight (i : I ⊕ I) : I → ℤ :=
  i.elim (coordinateVector I) (fun j => -coordinateVector I j)

private def planeMonomial {R : Type u} [CommRing R] (t : I → Rˣ) (a : I → ℤ) : Rˣ :=
  ∏ i, t i ^ a i

omit [Fintype I] in
private theorem swap_planeWeight (i : I ⊕ I) : planeWeight i.swap = -planeWeight i := by
  cases i <;> simp [planeWeight]

private theorem planeMonomial_weight {R : Type u} [CommRing R] (t : I → Rˣ) (i : I ⊕ I) :
    planeMonomial t (planeWeight i) = signedScale t i := by
  classical
  cases i <;> simp [planeMonomial, planeWeight, signedScale, coordinateVector, Pi.single_apply, apply_ite]

omit [DecidableEq I] in
private theorem planeMonomial_sub {R : Type u} [CommRing R] (t : I → Rˣ) (a b : I → ℤ) :
    planeMonomial t (a - b) = planeMonomial t a * (planeMonomial t b)⁻¹ := by
  simp [planeMonomial, _root_.zpow_sub, Finset.prod_mul_distrib]

omit [Fintype I] in
private theorem planeWeight_injective : Function.Injective (planeWeight (I := I)) := by
  intro i j h
  cases i with
  | inl a =>
    cases j with
    | inl b =>
      by_contra hne
      have hab : a ≠ b := fun hab => hne (congrArg Sum.inl hab)
      have he := congrFun h a
      simp [planeWeight, coordinateVector, hab] at he
    | inr b =>
      have he := congrFun h a
      by_cases hab : a = b <;> simp [planeWeight, coordinateVector, hab] at he
  | inr a =>
    cases j with
    | inl b =>
      have he := congrFun h b
      by_cases hab : b = a <;> simp [planeWeight, coordinateVector, hab] at he
    | inr b =>
      by_contra hne
      have hab : a ≠ b := fun hab => hne (congrArg Sum.inr hab)
      have he := congrFun h a
      simp [planeWeight, coordinateVector, hab] at he

private abbrev vectorScales (R : TestAlgebra k) (t : Points (S).group.X R) (i : I) : Rˣ :=
  torusPointsToUnits (m+1) R t (d.symm i)

private theorem vectorTangentMatrix_zero : vectorTangentMatrix P 0 = 0 := by
  change (vectorImageMatrix P (TangentRing k) 1).map TrivSqZeroExt.snd = 0
  rw [vectorMatrix_one]
  ext i j
  by_cases h : i = j <;> simp [h]

private theorem diagonal_weight_iff (χ : Character (S).group) (v : Lie k P.image.val) :
    v ∈ adjointWeightVectors S χ ↔
      ∀ (R : TestAlgebra k) (t : Points (S).group.X R) (i j : I ⊕ I),
        (signedScale (vectorScales P d hRank R t) i : R) *
            algebraMap k R (vectorTangentMatrix P v i j) =
          characterValue χ R t * algebraMap k R (vectorTangentMatrix P v i j) *
            (signedScale (vectorScales P d hRank R t) j : R) := by
  classical
  let entry (R : TestAlgebra k) (t : Points (S).group.X R) (i j : I ⊕ I) :=
        (signedScale (vectorScales P d hRank R t) i : R) *
            algebraMap k R (vectorTangentMatrix P v i j) =
          characterValue χ R t * algebraMap k R (vectorTangentMatrix P v i j) *
            (signedScale (vectorScales P d hRank R t) j : R)
  have step (R : TestAlgebra k) (t : Points (S).group.X R) :
      let x := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val
      let g := mapPoints (constants R) (t ≫ (S).inclusion.hom.hom)
      let y := mapPoints (scale R (characterValue χ R t)) x
      g * x * g⁻¹ = y ↔ ∀ i j, entry R t i j := by
    dsimp only
    let A := CommAlgCat.of k (DualNumber R)
    let f : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    let x : Points P.image.val.X A := mapPoints (dualMap f) v.toMul.val
    let g : Points P.image.val.X A := mapPoints (constants R) (t ≫ (S).inclusion.hom.hom)
    let c := characterValue χ R t
    let y : Points P.image.val.X A := mapPoints (scale R c) x
    change g * x * g⁻¹ = y ↔ _
    have hmul : g * x * g⁻¹ = y ↔ g * x = y * g := by
      constructor
      · intro h
        simpa using congrArg (· * g) h
      · intro h
        rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hmul, ← (vectorMatrix_injective P A).eq_iff,
      vectorImageMatrix_mul, vectorImageMatrix_mul]
    let D (i : I ⊕ I) : DualNumber R :=
      ⟨(signedScale (vectorScales P d hRank R t) i : R), 0⟩
    have hg : vectorImageMatrix P A g = diagonal D := by
      change vectorImageMatrix P A (mapPoints (constants R) _) = _
      rw [vectorImageMatrix_map]
      have he : vectorImageMatrix P R (t ≫ (S).inclusion.hom.hom) =
          hyperbolicDiagonal (vectorScales P d hRank R t) :=
        vectorDiagonalInclusion_matrix P d hRank R t
      rw [he, hyperbolicDiagonal]
      apply Matrix.ext
      intro i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        cases i <;> rfl
      · rw [Matrix.map_apply, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, map_zero]
    have hx (i j : I ⊕ I) : vectorImageMatrix P A x i j =
        ⟨algebraMap k R ((1 : Matrix (I ⊕ I) (I ⊕ I) k) i j),
          algebraMap k R (vectorTangentMatrix P v i j)⟩ := by
      change vectorImageMatrix P A (mapPoints (dualMap f) v.toMul.val) i j = _
      have he := vectorImageMatrix_map P (dualMap f) v.toMul.val
      rw [vectorTangentMatrix_value] at he
      exact congrFun₂ he i j
    have hy (i j : I ⊕ I) : vectorImageMatrix P A y i j =
        ⟨algebraMap k R ((1 : Matrix (I ⊕ I) (I ⊕ I) k) i j),
          c * algebraMap k R (vectorTangentMatrix P v i j)⟩ := by
      change vectorImageMatrix P A (mapPoints (scale R c) x) i j = _
      have he := congrFun₂ (vectorImageMatrix_map P (scale R c) x) i j
      change _ = (scale R c).hom (vectorImageMatrix P A x i j) at he
      rw [hx] at he
      exact he
    let A₀ (i j : I ⊕ I) := algebraMap k R ((1 : Matrix (I ⊕ I) (I ⊕ I) k) i j)
    let X (i j : I ⊕ I) := algebraMap k R (vectorTangentMatrix P v i j)
    let u (i : I ⊕ I) : R := ↑(signedScale (vectorScales P d hRank R t) i)
    let U (i j : I ⊕ I) : DualNumber R := (A₀ i j, X i j)
    let V (i j : I ⊕ I) : DualNumber R := (A₀ i j, c * X i j)
    have he (i j : I ⊕ I) : D i * U i j = V i j * D j ↔ entry R t i j := by
      have hfst : u i * A₀ i j = A₀ i j * u j := by
        by_cases hij : i = j
        · subst j
          exact mul_comm _ _
        · simp [A₀, hij]
      constructor
      · intro h
        have hs := congrArg (fun z : DualNumber R => z.snd) h
        change u i * X i j + 0 * A₀ i j = A₀ i j * 0 + c * X i j * u j at hs
        simpa only [zero_mul, add_zero, mul_zero, zero_add, entry, u, X, c] using hs
      · intro h
        apply TrivSqZeroExt.ext
        · exact hfst
        · change u i * X i j + 0 * A₀ i j = A₀ i j * 0 + c * X i j * u j
          simpa only [zero_mul, add_zero, mul_zero, zero_add, entry, u, X, c] using h
    rw [hg]
    constructor
    · intro h i j
      have h' := congrFun₂ h i j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hx, hy] at h'
      exact (he i j).mp h'
    · intro h
      apply Matrix.ext
      intro i j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hx, hy]
      exact (he i j).mpr (h i j)
  exact ⟨fun h R t => (step R t).mp (h R t), fun h R t => (step R t).mpr (h R t)⟩

private theorem hyperbolicGram_entry (i j : I ⊕ I) :
    hyperbolicGram I k i j = if j = i.swap then 1 else 0 := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [hyperbolicGram, Matrix.one_apply, eq_comm]

private theorem hyperbolicGram_mul_entry (M : Matrix (I ⊕ I) (I ⊕ I) k) (i j : I ⊕ I) :
    (hyperbolicGram I k * M) i j = M i.swap j := by
  classical
  simp [Matrix.mul_apply, hyperbolicGram_entry, ite_mul]

omit [Fintype I] in
private theorem roots_iff_weight_difference (a : I → ℤ) :
    a ∈ coroots I ↔ ∃ i j : I ⊕ I, i ≠ j ∧ i ≠ j.swap ∧ a = planeWeight i - planeWeight j := by
  change (∃ i j, i ≠ j ∧
    (a = coordinateVector I i - coordinateVector I j ∨
      a = coordinateVector I i + coordinateVector I j ∨
      a = -(coordinateVector I i + coordinateVector I j))) ↔ _
  constructor
  · rintro ⟨i, j, hij, rfl | rfl | rfl⟩
    · exact ⟨.inl i, .inl j, by simpa, by simp, rfl⟩
    · exact ⟨.inl i, .inr j, by simp, by simpa, by simp [planeWeight, sub_neg_eq_add]⟩
    · exact ⟨.inr i, .inl j, by simp, by simpa, by simp [planeWeight, sub_eq_add_neg, add_comm]⟩
  · rintro ⟨i | i, j | j, h, h', rfl⟩
    · exact ⟨i, j, by simpa using h, Or.inl rfl⟩
    · exact ⟨i, j, by simpa using h', Or.inr (Or.inl (by simp [planeWeight]))⟩
    · exact ⟨i, j, by simpa using h', Or.inr (Or.inr (by simp [planeWeight, sub_eq_add_neg, add_comm]))⟩
    · exact ⟨j, i, (by simpa using Ne.symm h), Or.inl (by simp [planeWeight, sub_eq_add_neg, add_comm])⟩

private def vectorRootMatrix (i j : I ⊕ I) : Matrix (I ⊕ I) (I ⊕ I) k :=
  Matrix.single i j 1 - Matrix.single j.swap i.swap 1

private theorem vectorRootMatrix_tangent {i j : I ⊕ I} (h : i ≠ j.swap) :
    ∀ x, OddSpinModels.hyperbolicForm I (DualNumber k)
        (infinitesimalOrthogonalMatrix (vectorRootMatrix (k := k) i j) *ᵥ x) =
      OddSpinModels.hyperbolicForm I (DualNumber k) x := by
  apply (splitOrthogonalTangent k I _).mpr
  have he (a b : I ⊕ I) :
      (hyperbolicGram I k * vectorRootMatrix (k := k) i j) a b =
        (if i.swap = a ∧ j = b then 1 else 0) -
          (if j = a ∧ i.swap = b then 1 else 0) := by
    rw [hyperbolicGram_mul_entry]
    simp only [vectorRootMatrix, Matrix.sub_apply, Matrix.single_apply]
    have hs (x y : I ⊕ I) : x = y.swap ↔ x.swap = y := by
      constructor <;> intro eq <;> simpa using congrArg Sum.swap eq
    simp only [hs i a, hs j.swap a, Sum.swap_swap]
  have h' : i.swap ≠ j := by
    intro e
    apply h
    simpa using congrArg Sum.swap e
  constructor
  · intro a
    rw [he]
    simp [show ¬ (i.swap = a ∧ j = a) from fun e => h' (e.1.trans e.2.symm),
      show ¬ (j = a ∧ i.swap = a) from fun e => h' (e.2.trans e.1.symm)]
  · ext a b
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply, he,
      @and_comm (i.swap = b) (j = a), @and_comm (j = b) (i.swap = a)]
    abel

omit [Fintype I] in
private theorem vectorRootMatrix_nonzero {i j : I ⊕ I} (h : i ≠ j.swap) :
    vectorRootMatrix (k := k) i j i j ≠ 0 := by
  simp [vectorRootMatrix, Ne.symm h]

private abbrev diagonalCharacters :
    Additive (Character (S).group) ≃ₗ[ℤ] (I → ℤ) :=
  (characterCoordinates (k := k) (m + 1)).trans (LinearEquiv.funCongrLeft ℤ ℤ d.symm)

private abbrev diagonalCocharacters :
    Additive (Cocharacter (orthogonalTorusModel (k := k) (m + 1)).val) ≃ₗ[ℤ] (I → ℤ) :=
  (cocharacterCoordinates (k := k) (m + 1)).trans (LinearEquiv.funCongrLeft ℤ ℤ d.symm)

private theorem diagonalCharacters_value (R : TestAlgebra k) (t : GroupPoints (S).group R)
    (χ : Character (S).group) :
    characterValue χ R t =
      (planeMonomial (vectorScales P d hRank R t) (diagonalCharacters P d hRank (Additive.ofMul χ)) : R) := by
  refine (characterCoordinates_evaluation (m+1) χ R t).trans (congrArg Units.val ?_)
  exact (d.symm.prod_comp (fun i =>
    torusPointsToUnits (m+1) R t i ^ characterCoordinates (m+1) (Additive.ofMul χ) i)).symm

private theorem diagonal_pairing (χ : Character (S).group) (c : Cocharacter (S).group) :
    pairing (S).group χ c = ∑ i, diagonalCharacters P d hRank (Additive.ofMul χ) i *
      diagonalCocharacters (k := k) d (Additive.ofMul c) i := by
  refine (pairing_coordinates (m+1) χ c).trans ?_
  exact (d.symm.sum_comp (fun i => characterCoordinates (m+1) (Additive.ofMul χ) i *
    cocharacterCoordinates (m+1) (Additive.ofMul c) i)).symm

private theorem diagonalCharacters_eq_of_value (χ : Character (S).group) (a : I → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : GroupPoints (S).group R),
      characterValue χ R t = (planeMonomial (vectorScales P d hRank R t) a : R)) :
    diagonalCharacters P d hRank (Additive.ofMul χ) = a := by
  let X := diagonalCharacters P d hRank
  let ψ : Character (S).group := Additive.toMul (X.symm a)
  have hψ : X (Additive.ofMul ψ) = a := X.apply_symm_apply a
  have hT : IsSplitTorus (S).group := ⟨m + 1, ⟨Iso.refl _⟩⟩
  have he : χ = ψ := RootData.CharacterPairing.characterValuesDetectCharacters hT (by
    intro R t
    exact (h R t).trans ((congrArg (fun w => (planeMonomial (vectorScales P d hRank R t) w : R))
      hψ.symm).trans (diagonalCharacters_value P d hRank R t ψ).symm))
  rw [he]
  exact hψ

private theorem weight_from_nonzero_entry (χ : Character (S).group) (v : Lie k P.image.val)
    (hv : v ∈ adjointWeightVectors (S) χ) {i j : I ⊕ I}
    (hij : vectorTangentMatrix P v i j ≠ 0) :
    diagonalCharacters P d hRank (Additive.ofMul χ) = planeWeight i - planeWeight j := by
  apply diagonalCharacters_eq_of_value
  intro R t
  have hu := (isUnit_iff_ne_zero.mpr hij).map (algebraMap k R)
  have h := (diagonal_weight_iff P d hRank χ v).mp hv R t i j
  rw [mul_right_comm] at h
  have h' := hu.mul_left_inj.mp h
  rw [planeMonomial_sub, planeMonomial_weight, planeMonomial_weight, Units.val_mul]
  apply (signedScale (vectorScales P d hRank R t) j).mul_left_inj.mp
  simpa [mul_assoc] using h'.symm

private theorem rootMatrix_has_weight {i j : I ⊕ I} (χ : Character (S).group)
    (hχ : diagonalCharacters P d hRank (Additive.ofMul χ) = planeWeight i - planeWeight j)
    (v : Lie k P.image.val) (hv : vectorTangentMatrix P v = vectorRootMatrix i j) :
    v ∈ adjointWeightVectors (S) χ := by
  apply (diagonal_weight_iff P d hRank χ v).mpr
  intro R t x y
  rw [hv]
  have hval := diagonalCharacters_value P d hRank R t χ
  rw [hχ] at hval
  rw [hval]
  let s := vectorScales P d hRank R t
  let a := planeWeight i - planeWeight j
  have entry (x y : I ⊕ I) (he : planeWeight x - planeWeight y = a) (z : R) :
      (signedScale s x : R) * z = (planeMonomial s a : R) * z * (signedScale s y : R) := by
    rw [← he, planeMonomial_sub, planeMonomial_weight, planeMonomial_weight, Units.val_mul]
    let u := signedScale s x
    let w := signedScale s y
    change (u : R) * z = (u * ↑w⁻¹) * z * w
    calc
      _ = (u * z) * (↑w⁻¹ * (w : R)) := by simp
      _ = _ := by ring
  by_cases h₁ : i = x ∧ j = y
  · obtain ⟨rfl, rfl⟩ := h₁
    exact entry _ _ rfl _
  by_cases h₂ : j.swap = x ∧ i.swap = y
  · obtain ⟨rfl, rfl⟩ := h₂
    exact entry _ _ (by simp [a, swap_planeWeight, sub_eq_add_neg, add_comm]) _
  simp [vectorRootMatrix, h₁, h₂]

private theorem vector_roots_coordinates :
    (fun χ => diagonalCharacters P d hRank (Additive.ofMul χ)) '' absoluteRoots (S) = coroots I := by
  ext a
  rw [roots_iff_weight_difference]
  constructor
  · rintro ⟨χ, ⟨hχ, v, hv, hvne⟩, rfl⟩
    have hM : vectorTangentMatrix P v ≠ 0 := fun he =>
      hvne (vectorTangentMatrix_injective P (he.trans (vectorTangentMatrix_zero P).symm))
    obtain ⟨i, j, hij⟩ : ∃ i j, vectorTangentMatrix P v i j ≠ 0 := by
      by_contra! h
      exact hM (Matrix.ext h)
    have he := weight_from_nonzero_entry P d hRank χ v hv hij
    refine ⟨i, j, ?_, ?_, he⟩
    · rintro rfl
      rw [sub_self] at he
      exact hχ (congrArg Additive.toMul ((diagonalCharacters P d hRank).injective
        (he.trans (diagonalCharacters P d hRank).map_zero.symm)))
    · rintro rfl
      have hz := ((splitOrthogonalTangent k I _).mp (vectorTangentMatrix_preserves P v)).1 j
      rw [hyperbolicGram_mul_entry] at hz
      exact hij hz
  · rintro ⟨i, j, hij, hpair, rfl⟩
    let X := diagonalCharacters P d hRank
    let a := planeWeight i - planeWeight j
    let χ : Character (S).group := Additive.toMul (X.symm a)
    have he : X (Additive.ofMul χ) = a := X.apply_symm_apply a
    have hχ : χ ≠ 1 := by
      intro h
      have hz : a = 0 := he.symm.trans (by rw [h]; exact X.map_zero)
      exact hij (planeWeight_injective (sub_eq_zero.mp hz))
    obtain ⟨v, hv⟩ := vectorTangentMatrix_surjective P hRank (vectorRootMatrix i j)
      (vectorRootMatrix_tangent hpair)
    refine ⟨χ, ⟨hχ, v, rootMatrix_has_weight P d hRank χ he v hv, ?_⟩, he⟩
    intro h
    rw [h, vectorTangentMatrix_zero] at hv
    exact vectorRootMatrix_nonzero hpair (congrFun₂ hv.symm i j)

open private constantPoint comp_constantPoint pointConj comp_pointConj
  from LinearAlgebraicGroups.RootData.AbstractPairing
open private IsAxis long_coroot from LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalRootDatum

private theorem vectorNormalizer_matrix (s : (S).group ≅ (S).group)
    (g : 𝟙_ (SchemeOver k) ⟶ P.image.val.X)
    (hg : (s.hom ≫ (S).inclusion).hom.hom = pointConj g (S).inclusion.hom.hom)
    (R : TestAlgebra k) (t : GroupPoints (S).group R) :
    let t' : GroupPoints (S).group R := t ≫ s.inv.hom.hom
    let A := vectorImageMatrix P R (constantPoint g _)
    diagonal (fun i : I ⊕ I => (signedScale (vectorScales P d hRank R t) i : R)) * A =
      A * diagonal (fun i : I ⊕ I => (signedScale (vectorScales P d hRank R t') i : R)) := by
  dsimp only
  let t' : GroupPoints (S).group R := t ≫ s.inv.hom.hom
  let x : Points P.image.val.X R := t ≫ (S).inclusion.hom.hom
  let y : Points P.image.val.X R := t' ≫ (S).inclusion.hom.hom
  let gR : Points P.image.val.X R := constantPoint g _
  have h₁ : t' ≫ (s.hom ≫ (S).inclusion).hom.hom = x := by
    change t ≫ (s.inv.hom.hom ≫ s.hom.hom.hom) ≫ (S).inclusion.hom.hom = _
    rw [show s.inv.hom.hom ≫ s.hom.hom.hom = 𝟙 _ from
      congrArg (fun f => f.hom.hom) s.inv_hom_id, Category.id_comp]
  have h₂ : t' ≫ (s.hom ≫ (S).inclusion).hom.hom = gR * y * gR⁻¹ := by
    rw [hg]
    exact comp_pointConj g t' (S).inclusion.hom.hom
  have he : x * gR = gR * y :=
    (congrArg (fun p : Points P.image.val.X R => p * gR) (h₁.symm.trans h₂)).trans
      (inv_mul_cancel_right _ _)
  have hx : vectorImageMatrix P R x =
      diagonal (fun i : I ⊕ I => (signedScale (vectorScales P d hRank R t) i : R)) :=
    (vectorDiagonalInclusion_matrix P d hRank R t).trans (hyperbolicDiagonal_eq_signedScale _)
  have hy : vectorImageMatrix P R y =
      diagonal (fun i : I ⊕ I => (signedScale (vectorScales P d hRank R t') i : R)) :=
    (vectorDiagonalInclusion_matrix P d hRank R t').trans (hyperbolicDiagonal_eq_signedScale _)
  have hm := congrArg (vectorImageMatrix P R) he
  rwa [vectorImageMatrix_mul, vectorImageMatrix_mul, hx, hy] at hm

private theorem vectorNormalizer_weights (s : (S).group ≅ (S).group)
    (g : 𝟙_ (SchemeOver k) ⟶ P.image.val.X)
    (hg : (s.hom ≫ (S).inclusion).hom.hom = pointConj g (S).inclusion.hom.hom)
    (j : I ⊕ I) (χ : Character (S).group)
    (hχ : diagonalCharacters P d hRank (Additive.ofMul χ) = planeWeight j) :
    ∃ i : I ⊕ I, diagonalCharacters P d hRank (Additive.ofMul (s.inv ≫ χ)) = planeWeight i := by
  let B := CommAlgCat.of k k
  let g₀ : Points P.image.val.X B := constantPoint g _
  let A := vectorImageMatrix P B g₀
  obtain ⟨i, hi⟩ : ∃ i, A i j ≠ 0 := by
    by_contra! h
    have hI : vectorImageMatrix P B g₀⁻¹ * A = 1 := by
      rw [show A = vectorImageMatrix P B g₀ from rfl, ← vectorImageMatrix_mul,
        inv_mul_cancel, vectorMatrix_one]
    exact one_ne_zero ((Matrix.one_apply_eq j).symm.trans
      ((congrFun₂ hI j j).symm.trans (by simp [Matrix.mul_apply, h])))
  refine ⟨i, diagonalCharacters_eq_of_value P d hRank (s.inv ≫ χ) _ ?_⟩
  intro R t
  let t' : GroupPoints (S).group R := t ≫ s.inv.hom.hom
  let gR : Points P.image.val.X R := constantPoint g _
  have hgR : vectorImageMatrix P R gR = A.map (algebraMap k R) := by
    let f : B ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have h : mapPoints f g₀ = gR := comp_constantPoint g _
    exact (congrArg (vectorImageMatrix P R) h).symm.trans (vectorImageMatrix_map P f g₀)
  have hm := vectorNormalizer_matrix P d hRank s g hg R t
  change diagonal (fun i : I ⊕ I => (signedScale (vectorScales P d hRank R t) i : R)) *
      vectorImageMatrix P R gR = vectorImageMatrix P R gR *
        diagonal (fun i : I ⊕ I => (signedScale (vectorScales P d hRank R t') i : R)) at hm
  rw [hgR] at hm
  have h := congrFun₂ hm i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply] at h
  rw [mul_comm (algebraMap k R (A i j)) _] at h
  have hscale := ((isUnit_iff_ne_zero.mpr hi).map (algebraMap k R)).mul_left_inj.mp h
  have hcomp : characterValue (s.inv ≫ χ) R t = characterValue χ R t' := by
    unfold characterValue t'
    congr 2
  rw [hcomp, diagonalCharacters_value, hχ, planeMonomial_weight, planeMonomial_weight]
  exact hscale.symm

omit [Fintype I] in
private theorem signedWeight_isAxis (i : I ⊕ I) :
    IsAxis (fun a : Fin (m + 1) => planeWeight i (d a)) := by
  intro a b hab
  have hd : d a ≠ d b := fun h => hab (d.injective h)
  rcases i with i | i
  · by_cases hi : i = d a
    · right
      simp [planeWeight, coordinateVector, hi, Ne.symm hd]
    · left
      simp [planeWeight, coordinateVector, Ne.symm hi]
  · by_cases hi : i = d a
    · right
      simp [planeWeight, coordinateVector, hi, Ne.symm hd]
    · left
      simp [planeWeight, coordinateVector, Ne.symm hi]

local instance : IsCommMonObj (orthogonalTorusModel (k := k) (m + 1)).val.X :=
  orthogonalTorusModel_comm (m + 1)

private theorem vector_coroot_eq [IsCommMonObj (S).group.X] (D : Datum (S)) (α : Root (S)) :
    diagonalCocharacters (k := k) d (D.rootDatum.coroot α) =
      diagonalCharacters P d hRank (D.rootDatum.root α) := by
  classical
  let X := diagonalCharacters P d hRank
  let Y := diagonalCocharacters (k := k) d
  let a := X (Additive.ofMul α.val)
  let c := Y (D.rootDatum.coroot α)
  change c = X (D.rootDatum.root α)
  rw [D.root_eq]
  change c = a
  have ha : a ∈ coroots I :=
    vector_roots_coordinates P d hRank ▸ ⟨α.val, α.property, rfl⟩
  obtain ⟨C, cochar, hC, hcochar, D₁, E, hDE, Q, F, P₁, A, xpos, xneg, hpos, hneg,
    hscalarpos, hscalarneg, reflection, hr⟩ := D.attached α
  have hc : Additive.ofMul reflection.coroot = D.rootDatum.coroot α := congrArg Additive.ofMul hr
  have hp : ∑ i, a i * c i = 2 := by
    change ∑ i, X (Additive.ofMul α.val) i * Y (D.rootDatum.coroot α) i = _
    rw [← hc]
    exact (diagonal_pairing P d hRank α.val reflection.coroot).symm.trans reflection.root_pairing
  have hcoord (i : I) :
      coordinateVector I i ∘ d = Specs.Arithmetic.OddSpinOrthogonalRootDatum.coordinate _ (d.symm i) := by
    funext b
    have h : d b = i ↔ b = d.symm i := (d.eq_symm_apply).symm
    simp [Function.comp_apply, Specs.Arithmetic.OddSpinOrthogonalRootDatum.coordinate,
      coordinateVector, Pi.single_apply, h]
  have haxis (i : Fin (m + 1)) :
      IsAxis (Specs.Arithmetic.OddSpinOrthogonalRootDatum.coordinate _ i -
        c (d i) • (a ∘ d)) := by
    let χ : Character (S).group := Additive.toMul (X.symm (coordinateVector I (d i)))
    have hχ : X (Additive.ofMul χ) = planeWeight (.inl (d i)) := X.apply_symm_apply _
    obtain ⟨j, hj⟩ := vectorNormalizer_weights P d hRank reflection.conjugation
      reflection.representative reflection.conjugates (.inl (d i)) χ hχ
    have he := congrArg (fun ψ : Character (S).group => X (Additive.ofMul ψ))
      (reflection.reflection χ)
    change X (Additive.ofMul (reflection.conjugation.inv ≫ χ)) =
      X (Additive.ofMul χ + (-pairing (S).group χ reflection.coroot) • Additive.ofMul α.val) at he
    rw [map_add, map_smul, hχ] at he
    have hpair : pairing (S).group χ reflection.coroot = c (d i) := by
      refine (diagonal_pairing P d hRank χ reflection.coroot).trans ?_
      change ∑ a, X (Additive.ofMul χ) a * Y (Additive.ofMul reflection.coroot) a = _
      rw [hχ, show Y (Additive.ofMul reflection.coroot) = c from congrArg Y hc]
      simp [planeWeight, coordinateVector, Pi.single_apply, ite_mul]
    rw [hpair, neg_smul, ← sub_eq_add_neg] at he
    change X (Additive.ofMul (reflection.conjugation.inv ≫ χ)) =
      coordinateVector I (d i) - c (d i) • a at he
    rw [show X (Additive.ofMul (reflection.conjugation.inv ≫ χ)) = planeWeight j from hj] at he
    have htotal := congrArg (fun v : I → ℤ => v ∘ d) he
    change (planeWeight j ∘ d) = (coordinateVector I (d i) ∘ d) - c (d i) • (a ∘ d) at htotal
    rw [hcoord, Equiv.symm_apply_apply] at htotal
    rw [← htotal]
    exact signedWeight_isAxis d j
  have hsum : ∑ i : Fin (m + 1), (a ∘ d) i * (c ∘ d) i = 2 :=
    (d.sum_comp (fun i => a i * c i)).trans hp
  have heq : c ∘ d = a ∘ d := by
    obtain ⟨i, j, hij, he | he | he⟩ := ha
    · apply long_coroot (d.symm i) (d.symm j) (d.symm.injective.ne hij)
        1 (-1) (by decide) (by decide) _ hsum haxis
      have hh : a ∘ d = (coordinateVector I i ∘ d) - (coordinateVector I j ∘ d) :=
        congrArg (fun v : I → ℤ => v ∘ d) he
      simpa [hcoord, sub_eq_add_neg] using hh
    · apply long_coroot (d.symm i) (d.symm j) (d.symm.injective.ne hij)
        1 1 (by decide) (by decide) _ hsum haxis
      have hh : a ∘ d = (coordinateVector I i ∘ d) + (coordinateVector I j ∘ d) :=
        congrArg (fun v : I → ℤ => v ∘ d) he
      simpa [hcoord] using hh
    · apply long_coroot (d.symm i) (d.symm j) (d.symm.injective.ne hij)
        (-1) (-1) (by decide) (by decide) _ hsum haxis
      have hh : a ∘ d = -((coordinateVector I i ∘ d) + (coordinateVector I j ∘ d)) :=
        congrArg (fun v : I → ℤ => v ∘ d) he
      simpa [hcoord, neg_add, add_comm] using hh
  funext i
  obtain ⟨j, rfl⟩ := d.surjective i
  exact congrFun heq j

open Specs.Pinning (AttachedDatum SplitBorelPair)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.CentralIsogenies (characterPullback)
open Specs.SimplyConnectedLattice (corootLatticeOf)
open Specs.BorelsAndChambers (IsPositiveSystem subgroupRoots)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open _root_.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo (spinTorusProjection)
open private reductive_of_semisimple pairing_pushforward
  from LinearAlgebraicGroups.Classification.CentralIsogenies
variable [LinearOrder (I ⊕ I)]

local notation "T" => splitDiagonalTorus P d

include hRank in
private theorem spin_coroot_coordinates
    [IsCommMonObj (T).group.X] (D : Datum (T)) :
    let v := diagonalCocharacterLattice P d
    Set.range (fun a => (v (D.rootDatum.coroot a)).val) = coroots I ∧
      ∀ a c, D.rootDatum.toLinearMap (D.rootDatum.root a) c =
        ∑ i, (v (D.rootDatum.coroot a)).val i * (v c).val i := by
  dsimp only
  let v := diagonalCocharacterLattice P d
  let q := spinTorusProjection (k := k) m
  have hss := splitDiagonalTorus_isSplit P d
  have hsm := splitDiagonalTorus_isGeometricallyMaximal P d
  have hsv : IsSplitTorus (S).group := ⟨m + 1, ⟨Iso.refl _⟩⟩
  have hmv := vectorDiagonal_isGeometricallyMaximal P d hRank
  have hs := reductive_of_semisimple P.spin (cliffordSpin_semisimple P d hRank)
  have ho := reductive_of_semisimple P.image (vectorImage_semisimple P d hRank)
  have hq := vectorDiagonal_restriction P d hRank
  obtain ⟨_, _, hbij, hcompare⟩ :=
    Classification.CentralIsogenies.centralIsogenyComparison P.spin P.image hs ho
      (T) (S) hss hsm hsv hmv P.projection q (splitSpinCentralIsogeny P) hq.1 hq.2.2
  obtain ⟨comm, ⟨E⟩⟩ := RootData.AbstractPairing.abstractPairing P.image ho (S) hsv hmv
  let := comm
  have corr (a : Root (T)) (b : Root (S)) (he : characterPullback q b.val = a.val) :
      (v (D.rootDatum.coroot a)).val = diagonalCharacters P d hRank (E.rootDatum.root b) := by
    have hα : characterPullback q b.val ∈ absoluteRoots (T) := he ▸ a.property
    have ha : (⟨characterPullback q b.val, hα⟩ : Root (T)) = a := Subtype.ext he
    have hc := (hcompare b.val b.property hα).2
      (Additive.toMul (D.rootDatum.coroot a)) (Additive.toMul (E.rootDatum.coroot b))
      (ha.symm ▸ D.attached a) (E.attached b)
    have heq := congrArg (fun c : Cocharacter (S).group =>
      diagonalCocharacters (k := k) d (Additive.ofMul c)) hc
    exact heq.trans (vector_coroot_eq P d hRank E b)
  constructor
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨β, hβ, he⟩ := hbij.surjOn a.property
      let b : Root (S) := ⟨β, hβ⟩
      change (v (D.rootDatum.coroot a)).val ∈ coroots I
      rw [corr a b he, E.root_eq, ← vector_roots_coordinates P d hRank]
      exact ⟨b.val, b.property, rfl⟩
    · rw [← vector_roots_coordinates P d hRank]
      rintro ⟨β, hβ, rfl⟩
      let b : Root (S) := ⟨β, hβ⟩
      let a : Root (T) := ⟨characterPullback q β, hbij.mapsTo hβ⟩
      refine ⟨a, (corr a b rfl).trans ?_⟩
      rw [E.root_eq]
  · intro a c
    obtain ⟨β, hβ, he⟩ := hbij.surjOn a.property
    let b : Root (S) := ⟨β, hβ⟩
    have h : D.rootDatum.toLinearMap (D.rootDatum.root a) c = pairing (T).group a.val c.toMul := by
      rw [D.root_eq]
      exact D.pairing_eq a.val c.toMul
    rw [h, ← he]
    refine (pairing_pushforward q β c.toMul).symm.trans ?_
    have hz := diagonal_pairing P d hRank β (c.toMul ≫ q)
    change _ = ∑ i, (v (D.rootDatum.coroot a)).val i * (v c).val i
    rw [corr a b he, E.root_eq]
    exact hz

private theorem full_coroot_lattice [Nontrivial I]
    [IsCommMonObj (T).group.X] (D : Datum (T))
    (hr : Set.range (fun a => ((diagonalCocharacterLattice P d) (D.rootDatum.coroot a)).val) =
      coroots I) :
    corootLatticeOf D = ⊤ := by
  let v := diagonalCocharacterLattice P d
  let j := (evenSum I).subtype.comp v.toLinearMap
  have hj : Function.Injective j := Subtype.val_injective.comp v.injective
  apply Submodule.map_injective_of_injective hj
  change (Submodule.span ℤ (Set.range D.rootDatum.coroot)).map j = Submodule.map j ⊤
  rw [Submodule.map_span, ← Set.range_comp', show Set.range (fun a => j (D.rootDatum.coroot a)) = _
    from hr, (corootLattice I).1, Submodule.map_top]
  ext x
  constructor
  · intro hx
    exact ⟨v.symm ⟨x, hx⟩, congrArg Subtype.val (v.apply_symm_apply ⟨x, hx⟩)⟩
  · rintro ⟨a, rfl⟩
    exact (v a).property

end
end VectorRoots

section SpinChamber

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open Specs.Pinning (AttachedDatum SplitBorelPair)
open Specs.CharacterDescent (Cocharacter)
open Specs.AbstractPairing (Datum Root)
open Specs.SimplyConnectedLattice (corootLatticeOf)
open Specs.BorelsAndChambers (IsPositiveSystem subgroupRoots)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.SymplecticMatrixStructure (hyperbolicDiagonal)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private unitPointsIso unitEquiv unitEquiv_unitPoint
  from LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
private theorem sum_twice_coordinate {I : Type u} [Fintype I] [DecidableEq I]
    (i : I) (a : I → ℤ) :
    ∑ j, a j * (2 • coordinateVector I i) j = 2 * a i := by
  classical
  simp [coordinateVector, Pi.single_apply, mul_ite, mul_comm]

private theorem twice_coordinate_mem_evenSum {I : Type u} [Fintype I] [DecidableEq I]
    (i : I) : 2 • coordinateVector I i ∈ evenSum I := by
  change Even (∑ j, (2 • coordinateVector I i) j)
  simp [Pi.smul_apply, ← Finset.mul_sum]

private theorem simpleDCoroot_injective (n : ℕ) (hn : 4 ≤ n) :
    Function.Injective (simpleDCoroot.{u} n hn) := by
  intro i j h
  by_contra hne
  have he := (simpleDCoordinates.{u} n hn).1 i j
  rw [← h, (simpleDCoordinates.{u} n hn).1 i i] at he
  simp only [CartanMatrix.D, Matrix.of_apply, hne, ite_false, ite_true] at he
  split_ifs at he <;> omega

open Specs.BorelsAndChambers (IsRegular positiveRoots)
open _root_.LinearAlgebraicGroups.CocharacterDynamics
  (HasExtension RepresentsOnAlgebras existsLimitDecomposition)

private def heightCoordinates (n : ℕ) : evenSum (ULift.{u} (Fin n)) :=
  ⟨fun i => 2 * ((n : ℤ) - 1 - i.down.val), by
    change Even (∑ i : ULift.{u} (Fin n), 2 * ((n : ℤ) - 1 - i.down.val))
    rw [← Finset.mul_sum]
    exact even_two_mul _⟩

set_option linter.style.haveILetI false in
set_option maxHeartbeats 800000 in
private theorem standardTypeDBorel {k : Type u} [Field k] (n : ℕ) (hn : 4 ≤ n)
    (H : AffineAlgebraicGroup k) (hred : Specs.GeometricRadicals.IsReductive H)
    (T : ClosedSubgroup H.val) (hsplit : Specs.GeometricRadicals.IsSplitTorus T.group)
    (hmax : Specs.RankOneFlag.IsGeometricallyMaximal T)
    [comm : IsCommMonObj T.group.X] (D : Datum T)
    (v : Additive (Cocharacter T.group) ≃ₗ[ℤ] evenSum (ULift.{u} (Fin n)))
    (hr : Set.range (fun a => (v (D.rootDatum.coroot a)).val) = coroots (ULift.{u} (Fin n)))
    (hp : ∀ a c, D.rootDatum.toLinearMap (D.rootDatum.root a) c =
      ∑ i, (v (D.rootDatum.coroot a)).val i * (v c).val i) :
    ∃ (B : ClosedSubgroup H.val) (hB : Specs.GeometricBorelConjugacy.IsKBorel B)
      (hBT : Specs.SchemeDerivedGroup.IsSubgroupOf T B)
      (base : D.rootDatum.Base) (simple : Fin n ≃ ↥base.support),
      (∀ a, a ∈ base.support ↔ Specs.Pinning.IsSimple ⟨H, hred, T, hsplit, hmax, B, hB, hBT⟩ a) ∧
      (∀ i, (v (D.rootDatum.coroot (simple i).val)).val = simpleDCoroot n hn i) ∧
      RepresentsOnAlgebras B (fun _ g =>
        HasExtension ((v.symm (heightCoordinates n)).toMul ≫ T.inclusion) g) := by
  let I := ULift.{u} (Fin n)
  letI := D.finiteRoots
  letI := D.freeCharacters
  letI := D.finiteCharacters
  letI := D.reduced
  let r (a : Root T) : I → ℤ := (v (D.rootDatum.coroot a)).val
  have evalPair (a : Root T) (y : Additive (Cocharacter T.group)) :
      D.rootDatum.toLinearMap (D.rootDatum.root a) y = ∑ i, r a i * (v y).val i := hp a y
  have hmem (a : Root T) : r a ∈ coroots I := hr ▸ ⟨a, rfl⟩
  let re : Root T ≃ ↥(coroots I) := Equiv.ofBijective (fun a => ⟨r a, hmem a⟩) ⟨by
    intro a b h
    have he := congrArg Subtype.val h
    apply D.rootDatum.coroot.injective
    apply v.injective
    exact Subtype.ext he, by
    intro a
    obtain ⟨b, hb⟩ := show a.val ∈ Set.range r from hr.symm ▸ a.property
    exact ⟨b, Subtype.ext hb⟩⟩
  have root_sum (a b c : Root T) :
      D.rootDatum.root a = D.rootDatum.root b + D.rootDatum.root c ↔ r a = r b + r c := by
    constructor
    · intro h
      funext i
      let z := v.symm ⟨2 • coordinateVector I i, twice_coordinate_mem_evenSum i⟩
      have hz : (v z).val = 2 • coordinateVector I i :=
        congrArg Subtype.val (v.apply_symm_apply _)
      have h' := congrArg (fun x => D.rootDatum.toLinearMap x z) h
      rw [map_add, LinearMap.add_apply, evalPair a, evalPair b, evalPair c, hz,
        sum_twice_coordinate, sum_twice_coordinate, sum_twice_coordinate] at h'
      change r a i = r b i + r c i
      omega
    · intro h
      apply D.rootDatum.toLinearMap.toPerfPair.injective
      ext z
      change D.rootDatum.toLinearMap (D.rootDatum.root a) z =
        D.rootDatum.toLinearMap (D.rootDatum.root b + D.rootDatum.root c) z
      rw [map_add, LinearMap.add_apply, evalPair a, evalPair b, evalPair c, h]
      simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  let w := heightCoordinates.{u} n
  let z := v.symm w
  let F := D.rootDatum.toLinearMap.flip z
  have value (a : Root T) : F (D.rootDatum.root a) = 2 * typeDRootHeight n (r a) := by
    change D.rootDatum.toLinearMap (D.rootDatum.root a) z = _
    rw [evalPair a, show v z = w from v.apply_symm_apply w, typeDRootHeight, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change r a i * (2 * ((n : ℤ) - 1 - i.down.val)) = _
    ring
  have hpositive := typeDPositiveRoots.{u} n hn
  have regular (a : Root T) : F (D.rootDatum.root a) ≠ 0 := by
    rw [value]
    exact mul_ne_zero two_ne_zero (hpositive.1 (r a) (hmem a))
  have positive (a : Root T) :
      a ∈ Specs.SimpleRoots.positive D.rootDatum F ↔ 0 < typeDRootHeight n (r a) := by
    change 0 < F (D.rootDatum.root a) ↔ _
    rw [value]
    omega
  have hval (a : Root T) :
      F (D.rootDatum.root a) = Specs.CharacterPairing.pairing T.group a.val z.toMul := by
    change D.rootDatum.toLinearMap (D.rootDatum.root a) z = _
    rw [D.root_eq]
    exact D.pairing_eq a.val z.toMul
  have hregular : IsRegular T z.toMul := fun a => (hval a) ▸ regular a
  obtain ⟨E⟩ := existsLimitDecomposition H (z.toMul ≫ T.inclusion)
  obtain ⟨_, hB, hBT, hpos, _, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel H hred T hsplit hmax z.toMul hregular E
  let B := E.parabolic
  obtain ⟨base, hbase⟩ := RootData.SimpleRoots.baseFor D.rootDatum F regular
  have simple_iff (a : Root T) :
      a ∈ base.support ↔ r a ∈ Set.range (simpleDCoroot n hn) := by
    rw [hbase.simple_iff, hpositive.2, positive]
    refine ⟨?_, ?_⟩
    · rintro ⟨ha, hs⟩
      refine ⟨hmem a, ha, ?_⟩
      rintro ⟨b, c, ⟨hb, hbp⟩, ⟨hc, hcp⟩, he⟩
      let bRoot := re.symm ⟨b, hb⟩
      let cRoot := re.symm ⟨c, hc⟩
      have eb : r bRoot = b := congrArg Subtype.val (re.apply_symm_apply _)
      have ec : r cRoot = c := congrArg Subtype.val (re.apply_symm_apply _)
      apply hs bRoot ((positive bRoot).mpr (eb.symm ▸ hbp))
        cRoot ((positive cRoot).mpr (ec.symm ▸ hcp))
      exact (root_sum a bRoot cRoot).mpr (by rw [eb, ec, he])
    · rintro ⟨_, hp, hs⟩
      refine ⟨hp, fun b hb c hc he => hs ?_⟩
      exact ⟨r b, r c, ⟨hmem b, (positive b).mp hb⟩, ⟨hmem c, (positive c).mp hc⟩,
        ((root_sum a b c).mp he).symm⟩
  have simple_mem (i : Fin n) : simpleDCoroot n hn i ∈ coroots I :=
    ((hpositive.2 _).mp ⟨i, rfl⟩).1
  let s (i : Fin n) : Root T := re.symm ⟨simpleDCoroot n hn i, simple_mem i⟩
  have es (i : Fin n) : r (s i) = simpleDCoroot n hn i :=
    congrArg Subtype.val (re.apply_symm_apply _)
  let f (i : Fin n) : ↥base.support := ⟨s i, (simple_iff (s i)).mpr ⟨i, (es i).symm⟩⟩
  have hf : Function.Bijective f := ⟨by
    intro i j h
    apply simpleDCoroot_injective n hn
    have e : r (s i) = r (s j) := congrArg (fun x : ↥base.support => r x.val) h
    rwa [es i, es j] at e, by
    rintro ⟨a, ha⟩
    obtain ⟨i, hi⟩ := (simple_iff a).mp ha
    refine ⟨i, Subtype.ext (re.injective (Subtype.ext ?_))⟩
    change r (s i) = r a
    exact (es i).trans hi⟩
  let simple := Equiv.ofBijective f hf
  refine ⟨B, hB, hBT, base, simple, ?_, es, E.parabolic_points⟩
  intro a
  rw [hbase.simple_iff]
  have hpos' : subgroupRoots T B = Specs.SimpleRoots.positive D.rootDatum F := by
    change subgroupRoots T E.parabolic = _
    rw [hpos]
    ext a
    change (0 < Specs.CharacterPairing.pairing T.group a.val z.toMul) ↔ 0 < F (D.rootDatum.root a)
    rw [hval a]
  simp only [Specs.Pinning.IsSimple, hpos', D.root_eq]
  rfl

private theorem unitPointsIso_apply {k : Type u} [Field k] (R : TestAlgebra k) (z : Rˣ) :
    (unitPointsIso (k := k)).hom.app R z = unitPoint R z := by
  change (unitEquiv R).symm z = _
  apply (unitEquiv R).injective
  rw [MulEquiv.apply_symm_apply, unitEquiv_unitPoint]

set_option linter.style.haveILetI false in
set_option maxHeartbeats 650000 in
/-- In the actual Clifford spin group, the attached roots and coroots are
the signed pair sums in hyperbolic coordinates, with the standard type-D base. -/
theorem splitSpinTypeD : SplitSpinTypeD.{u} := by
  intro k _ n hn P
  cases n with
  | zero => omega
  | succ m =>
    let n := m + 1
    let I := ULift.{u} (Fin n)
    let d : Fin (m + 1) ≃ I := Equiv.ulift.symm
    have hrank : 4 ≤ Fintype.card I := by simpa [I, n] using hn
    have : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    letI : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
      (Fintype.equivFin (I ⊕ I)).injective
    let T := splitDiagonalTorus P d
    have hs : IsSemisimple P.spin := cliffordSpin_semisimple P d hrank
    have hred := reductive_of_semisimple P.spin hs
    have hsplit := splitDiagonalTorus_isSplit P d
    have hmax := splitDiagonalTorus_isGeometricallyMaximal P d
    obtain ⟨comm, ⟨D⟩⟩ := RootData.AbstractPairing.abstractPairing P.spin hred T hsplit hmax
    letI := comm
    let v := diagonalCocharacterLattice P d
    obtain ⟨hr, hp⟩ := spin_coroot_coordinates P d hrank D
    have hspan := full_coroot_lattice P d D hr
    have hsconn := (Classification.SimplyConnectedLattice.latticeCriterion
      P.spin hs T hsplit hmax D).mpr hspan
    obtain ⟨B, hB, hBT, base, simple, hbase, hsimple, _⟩ :=
      standardTypeDBorel n hn P.spin hred T hsplit hmax D v hr hp
    let Q : SplitBorelPair k := ⟨P.spin, hred, T, hsplit, hmax, B, hB, hBT⟩
    let E : AttachedDatum Q := ⟨comm, D, base, hbase⟩
    refine ⟨Q, E, Iso.refl _, hs, hsconn, hspan, simple, v, (unitPointsIso (k := k)).symm, ?_,
      hsimple, hr, hp, ?_⟩
    · intro i j
      rw [← RootPairing.root_coroot_eq_pairing]
      change D.rootDatum.toLinearMap (D.rootDatum.root (simple j).val) (D.rootDatum.coroot (simple i).val) = _
      rw [hp, hsimple j, hsimple i]
      exact (simpleDCoordinates.{u} n hn).1 i j
    · intro R t c
      change (P.orthogonal.points R (((unitPointsIso (k := k)).hom.app R t) ≫
        (c ≫ T.inclusion ≫ 𝟙 P.spin.val ≫ P.projection ≫ P.inclusion).hom.hom)).val.val = _
      rw [unitPointsIso_apply, Category.id_comp]
      exact diagonalCocharacter_vector P d R t c

end SpinChamber

section PairReducedNorm

open RM03.Brauer.SemilinearDescent (AlgebraAction)

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}

/-- Over a test algebra of the splitting field the generic reduced norm is
the determinant of the matrix supplied by the descended algebra comparison. -/
theorem pairReducedNormScalarExtension (D : DescendedQuadraticPair ρ)
    (S : Type u) [CommRing S] [Algebra k S] [Algebra K S] [IsScalarTower k K S]
    (E : (S ⊗[k] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S)
    (hE : ∀ (r : S) (x : ρ.fixedSubalgebra), E (r ⊗ₜ[k] x) = r • x.val.map (algebraMap K S))
    (d : ℕ) (b : Module.Basis (Fin d) k ρ.fixedSubalgebra) (x : S ⊗[k] ρ.fixedSubalgebra) :
    MvPolynomial.eval₂ (algebraMap k S) (fun i => (b.baseChange S).repr x i)
      (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b) = (E x).det := by
  classical
  let p : I ⊕ I ≃ Fin (_root_.Specs.RM03.CSA.degree k ρ.fixedSubalgebra) :=
    (Fintype.equivFin _).trans (finCongr (by rw [D.degree, Fintype.card_sum]; omega))
  let e := D.splitting.trans (Matrix.reindexAlgEquiv K K p)
  let y (i : Fin d) : S := (b.baseChange S).repr x i
  let F := MvPolynomial.eval₂Hom (algebraMap K S) y
  have h := congrArg F (RM03.CSA.genericReducedNorm_map D.centralSimple (⇑b) e)
  have h' : MvPolynomial.eval₂ (algebraMap k S) y
        (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b) =
      (Matrix.reindexAlgEquiv S S p (E x)).det := by
    refine Eq.trans ?_ (h.trans ?_)
    · change _ = MvPolynomial.eval₂ (algebraMap K S) y
        (MvPolynomial.map (algebraMap k K) (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b))
      rw [MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq k K S]
    · let M := _root_.Specs.RM03.CSA.genericMatrix (fun i => e (1 ⊗ₜ[k] b i))
      change F M.det = _
      refine (RingHom.map_det F M).trans (congrArg Matrix.det ?_)
      change M.map F = _
      have hx : (∑ i : Fin d, y i • ((1 : S) ⊗ₜ[k] b i)) = x := by
        simpa only [y, Module.Basis.baseChange_apply] using (b.baseChange S).sum_repr x
      conv_rhs => rw [← hx]
      rw [map_sum, map_sum]
      apply Matrix.ext
      intro i j
      simp only [M, _root_.Specs.RM03.CSA.genericMatrix, Matrix.map_apply, Matrix.sum_apply,
        map_sum, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.coe_reindexAlgEquiv,
        Matrix.reindex_apply, Matrix.submatrix_apply, e, AlgEquiv.trans_apply,
        D.splittingFormula, one_smul]
      apply Finset.sum_congr rfl
      intro a _
      rw [show y a • ((1 : S) ⊗ₜ[k] b a) = y a ⊗ₜ[k] b a by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], hE]
      simp [F]
  exact h'.trans (Matrix.det_reindex_self p (E x))

end PairReducedNorm


section DescendedPairIsometries

open Matrix AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open SymplecticIsometryDescent (Involution tensorMap tensorMap_involution)

noncomputable section

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)} (D : DescendedQuadraticPair ρ)

private abbrev pairSymmetricMap (R : TestAlgebra k) :=
  (symmetricPart D.involution).subtype.baseChange R

private abbrev pairTraceMap (R : TestAlgebra k) :=
  (TensorProduct.AlgebraTensorModule.rid k R R).toLinearMap.comp (D.semitrace.baseChange R)

private theorem pairSymmetricMap_injective (R : TestAlgebra k) :
    Function.Injective (pairSymmetricMap D R) :=
  Module.Flat.lTensor_preserves_injective_linearMap
    (symmetricPart D.involution).subtype (symmetricPart D.involution).injective_subtype

private theorem pairSymmetricMap_mem_range (R : TestAlgebra k) (x : R ⊗[k] ρ.fixedSubalgebra) :
    x ∈ LinearMap.range (pairSymmetricMap D R) ↔ (D.involution.baseChange R).toLinearMap x = x := by
  let f : ρ.fixedSubalgebra →ₗ[k] ρ.fixedSubalgebra := D.involution.toLinearMap - LinearMap.id
  have hf : TensorProduct.AlgebraTensorModule.lTensor R R f =
      (D.involution.baseChange R).toLinearMap - LinearMap.id := by
    ext
    simp [f]
  rw [← show LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor R R f) =
    LinearMap.range (pairSymmetricMap D R) from Module.Flat.ker_lTensor_eq R R f,
    LinearMap.mem_ker, hf, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

private abbrev pairSymmetricChange {R S : TestAlgebra k} (f : R ⟶ S) :
    R ⊗[k] symmetricPart D.involution →ₗ[k] S ⊗[k] symmetricPart D.involution :=
  TensorProduct.map f.hom.toLinearMap LinearMap.id

private theorem pairSymmetricMap_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (x : R ⊗[k] symmetricPart D.involution) :
    pairSymmetricMap D S (pairSymmetricChange D f x) = tensorMap f (pairSymmetricMap D R x) := by
  induction x with
  | tmul r x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem pairTraceMap_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (x : R ⊗[k] symmetricPart D.involution) :
    pairTraceMap D S (pairSymmetricChange D f x) = f.hom (pairTraceMap D R x) := by
  induction x with
  | tmul r x =>
    simp only [pairSymmetricChange, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      pairTraceMap, LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, map_mul, AlgHom.commutes]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem pairConjugate_fixed (R : TestAlgebra k)
    (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ) (hg : g ∈ (D.involution.baseChange R).isometries)
    (x : R ⊗[k] symmetricPart D.involution) :
    g.val * pairSymmetricMap D R x * g.inv ∈ LinearMap.range (pairSymmetricMap D R) := by
  let σ := D.involution.baseChange R
  have hg' : σ.toLinearMap g.val = g.inv := by
    calc
      _ = (σ.toLinearMap g.val * g.val) * g.inv := by rw [mul_assoc, g.val_inv, mul_one]
      _ = _ := by rw [show σ.toLinearMap g.val * g.val = 1 from hg, one_mul]
  have hh : σ.toLinearMap g.inv = g.val := by
    rw [← hg', σ.involutive]
  rw [pairSymmetricMap_mem_range]
  change σ.toLinearMap (g.val * pairSymmetricMap D R x * g.inv) = _
  have hx := (pairSymmetricMap_mem_range D R _).mp (LinearMap.mem_range_self _ x)
  rw [σ.map_mul, σ.map_mul, hg', hh, hx, mul_assoc]

private theorem pairIsometry_map {R S : TestAlgebra k} (f : R ⟶ S)
    (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ) (hg : IsPairIsometry D R g) :
    IsPairIsometry D S (Units.map (tensorMap f).toMonoidHom g) := by
  let u := Units.map (tensorMap f).toMonoidHom g
  refine ⟨?_, ?_⟩
  · change (D.involution.baseChange S).toLinearMap (tensorMap f g.val) * tensorMap f g.val = 1
    rw [← tensorMap_involution, ← map_mul, hg.1, map_one]
  · intro x
    change ∃ y, pairSymmetricMap D S y = u.val * pairSymmetricMap D S x * u.inv ∧
      pairTraceMap D S y = pairTraceMap D S x
    induction x with
    | tmul s a =>
      obtain ⟨b, hb, ht⟩ := hg.2 ((1 : R) ⊗ₜ[k] a)
      change pairSymmetricMap D R b = g.val * pairSymmetricMap D R ((1 : R) ⊗ₜ[k] a) * g.inv at hb
      change pairTraceMap D R b = pairTraceMap D R ((1 : R) ⊗ₜ[k] a) at ht
      have hm : pairSymmetricChange D f ((1 : R) ⊗ₜ[k] a) = (1 : S) ⊗ₜ[k] a := by
        rw [pairSymmetricChange, TensorProduct.map_tmul]
        simp
      have hs : s • ((1 : S) ⊗ₜ[k] a) = s ⊗ₜ[k] a := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      refine ⟨s • pairSymmetricChange D f b, ?_, ?_⟩
      · have hscale : pairSymmetricMap D S (s ⊗ₜ[k] a) =
            s • pairSymmetricMap D S ((1 : S) ⊗ₜ[k] a) := by
          rw [← hs, map_smul]
        rw [map_smul, pairSymmetricMap_natural, hb, map_mul, map_mul, ← pairSymmetricMap_natural, hm,
          hscale]
        change s • (u.val * pairSymmetricMap D S (1 ⊗ₜ[k] a) * u.inv) =
          u.val * (s • pairSymmetricMap D S (1 ⊗ₜ[k] a)) * u.inv
        rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      · rw [map_smul, pairTraceMap_natural, ht, ← pairTraceMap_natural, hm, ← map_smul, hs]
    | add x y hx hy =>
      obtain ⟨a, ha, hat⟩ := hx
      obtain ⟨b, hb, hbt⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb, mul_add, add_mul],
        by rw [map_add, map_add, hat, hbt]⟩

private def pairIsometrySubgroup (R : TestAlgebra k) : Subgroup (R ⊗[k] ρ.fixedSubalgebra)ˣ where
  carrier := { g | IsPairIsometry D R g }
  one_mem' := by
    refine ⟨(D.involution.baseChange R).isometries.one_mem, ?_⟩
    intro x
    exact ⟨x, by simp, rfl⟩
  mul_mem' {g h} hg hh := by
    refine ⟨(D.involution.baseChange R).isometries.mul_mem hg.1 hh.1, ?_⟩
    intro x
    obtain ⟨y, hy, hyt⟩ := hh.2 x
    obtain ⟨z, hz, hzt⟩ := hg.2 y
    refine ⟨z, ?_, hzt.trans hyt⟩
    change pairSymmetricMap D R z = (g * h).val * pairSymmetricMap D R x * (g * h).inv
    rw [hz, hy]
    change g.val * (h.val * pairSymmetricMap D R x * h.inv) * g.inv =
      (g.val * h.val) * pairSymmetricMap D R x * (h.inv * g.inv)
    simp only [mul_assoc]
  inv_mem' {g} hg := by
    have hU := (D.involution.baseChange R).isometries.inv_mem hg.1
    refine ⟨hU, ?_⟩
    intro x
    obtain ⟨y, hy⟩ := pairConjugate_fixed D R g⁻¹ hU x
    refine ⟨y, hy, ?_⟩
    obtain ⟨z, hz, hzt⟩ := hg.2 y
    have hzx : z = x := by
      apply pairSymmetricMap_injective D R
      rw [hz, hy]
      change g.val * (g.inv * pairSymmetricMap D R x * g.val) * g.inv = pairSymmetricMap D R x
      rw [← mul_assoc, ← mul_assoc g.val, g.val_inv, one_mul, mul_assoc, g.val_inv, mul_one]
    exact hzx.symm ▸ hzt.symm

private def pairIsometryPoints : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (pairIsometrySubgroup D R)
  map {R S} f := GrpCat.ofHom
    (((Units.map (tensorMap f).toMonoidHom).comp (pairIsometrySubgroup D R).subtype).codRestrict
      (pairIsometrySubgroup D S) fun a => pairIsometry_map D f a.val a.property)
  map_id R := by
    apply GrpCat.ext
    intro a
    apply Subtype.ext
    apply Units.ext
    change tensorMap (𝟙 R) a.val.val = _
    induction a.val.val with
    | tmul r x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  map_comp {R S T} f g := by
    apply GrpCat.ext
    intro a
    apply Subtype.ext
    apply Units.ext
    change tensorMap (f ≫ g) a.val.val = tensorMap g (tensorMap f a.val.val)
    induction a.val.val with
    | tmul r x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

private theorem pairIsometry_of_map {R S : TestAlgebra k} (f : R ⟶ S)
    (hf : Function.Injective f.hom) (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ)
    (hg : IsPairIsometry D S (Units.map (tensorMap f).toMonoidHom g)) :
    IsPairIsometry D R g := by
  let u := Units.map (tensorMap f).toMonoidHom g
  have hi : Function.Injective (tensorMap (A := ρ.fixedSubalgebra) f) := by
    exact Module.Flat.rTensor_preserves_injective_linearMap f.hom.toLinearMap hf
  have hU : g ∈ (D.involution.baseChange R).isometries := by
    change (D.involution.baseChange R).toLinearMap g.val * g.val = 1
    apply hi
    rw [map_mul, tensorMap_involution, map_one]
    exact hg.1
  refine ⟨hU, fun x => ?_⟩
  obtain ⟨y, hy⟩ := pairConjugate_fixed D R g hU x
  obtain ⟨z, hz, ht⟩ := hg.2 (pairSymmetricChange D f x)
  have hyz : pairSymmetricChange D f y = z := by
    apply pairSymmetricMap_injective D S
    rw [pairSymmetricMap_natural, hy, hz, pairSymmetricMap_natural, map_mul, map_mul]
    rfl
  refine ⟨y, hy, hf ?_⟩
  change f.hom (pairTraceMap D R y) = f.hom (pairTraceMap D R x)
  rw [← pairTraceMap_natural, ← pairTraceMap_natural, hyz]
  exact ht

section PairRepresentation

open private Representation Representation.mk Representation.hopf Representation.convolutionIso
  spectrumPointsIso from LinearAlgebraicGroups.Affine.StandardGroups
open Specs.StandardGroups (spectrum)

variable {d : ℕ} (b : Module.Basis (Fin d) k ρ.fixedSubalgebra)
variable (p : ρ.fixedSubalgebra →ₗ[k] symmetricPart D.involution)
variable (hp : ∀ x : symmetricPart D.involution, p x.val = x)

private abbrev pairAmbientTrace (R : TestAlgebra k) :=
  (pairTraceMap D R).comp (p.baseChange R)

include hp in
private theorem pairAmbientTrace_eq (R : TestAlgebra k) (x : R ⊗[k] symmetricPart D.involution) :
    pairAmbientTrace D p R (pairSymmetricMap D R x) = pairTraceMap D R x := by
  induction x with
  | tmul r x =>
    simp only [pairAmbientTrace, LinearMap.comp_apply, LinearMap.baseChange_tmul,
      pairSymmetricMap, Submodule.subtype_apply, hp]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem pairAmbientTrace_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (a : R ⊗[k] ρ.fixedSubalgebra) :
    pairAmbientTrace D p S (tensorMap f a) = f.hom (pairAmbientTrace D p R a) := by
  induction a with
  | tmul r a =>
    change pairTraceMap D S (f.hom r ⊗ₜ[k] p a) = f.hom (pairTraceMap D R (r ⊗ₜ[k] p a))
    simpa only [pairSymmetricChange, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
      using pairTraceMap_natural D f (r ⊗ₜ[k] p a)
  | add x y hx hy => simp only [map_add, hx, hy]

private def pairEquations (R : TestAlgebra k) (a : R ⊗[k] ρ.fixedSubalgebra) :
    (Bool × Fin d) ⊕ symmetricPart D.involution → R :=
  let σ := (D.involution.baseChange R).toLinearMap
  Sum.elim (fun (ε, i) => (b.baseChange R).repr ((if ε then σ a * a else a * σ a) - 1) i)
    (fun x => pairAmbientTrace D p R (a * (1 ⊗ₜ[k] x.val) * σ a) -
      pairTraceMap D R (1 ⊗ₜ[k] x))

private theorem pairBasis_repr_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (x : R ⊗[k] ρ.fixedSubalgebra) (i : Fin d) :
    (b.baseChange S).repr (tensorMap f x) i = f.hom ((b.baseChange R).repr x i) := by
  induction x with
  | tmul r x =>
    change (b.baseChange S).repr (f.hom r ⊗ₜ[k] x) i = _
    simp only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

private theorem pairEquations_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (a : R ⊗[k] ρ.fixedSubalgebra) (i : (Bool × Fin d) ⊕ symmetricPart D.involution) :
    pairEquations D b p S (tensorMap f a) i = f.hom (pairEquations D b p R a i) := by
  have hm (x : symmetricPart D.involution) :
      tensorMap f ((1 : R) ⊗ₜ[k] x.val) = (1 : S) ⊗ₜ[k] x.val := by
    change f.hom 1 ⊗ₜ[k] x.val = _
    rw [map_one]
  rcases i with ⟨ε, i⟩ | x
  · let u := (D.involution.baseChange R).toLinearMap a
    let v := (D.involution.baseChange S).toLinearMap (tensorMap f a)
    have hσ : tensorMap f u = v := tensorMap_involution D.involution f a
    cases ε
    · change (b.baseChange S).repr (tensorMap f a * v - 1) i =
        f.hom ((b.baseChange R).repr (a * u - 1) i)
      rw [← pairBasis_repr_natural b f]
      congr 2
      simp only [map_sub, map_mul, map_one, hσ]
    · change (b.baseChange S).repr (v * tensorMap f a - 1) i =
        f.hom ((b.baseChange R).repr (u * a - 1) i)
      rw [← pairBasis_repr_natural b f]
      congr 2
      simp only [map_sub, map_mul, map_one, hσ]
  · have hTrace :
        pairTraceMap D S ((1 : S) ⊗ₜ[k] x) = f.hom (pairTraceMap D R ((1 : R) ⊗ₜ[k] x)) := by
      simpa only [pairSymmetricChange, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one,
        LinearMap.id_apply] using pairTraceMap_natural D f ((1 : R) ⊗ₜ[k] x)
    simp only [pairEquations, Sum.elim_inr, map_sub, ← pairAmbientTrace_natural D p f,
      map_mul, tensorMap_involution, hm, hTrace]

include hp in
set_option maxHeartbeats 420000 in
private theorem pairEquations_iff_eval (R : TestAlgebra k) (a : R ⊗[k] ρ.fixedSubalgebra) :
    (∀ i, pairEquations D b p R a i = 0) ↔
      ∃ g : pairIsometrySubgroup D R, g.val.val = a := by
  let σ := (D.involution.baseChange R).toLinearMap
  have hU (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ) (h : σ g.val * g.val = 1) :
      σ g.val = g.inv := by
    calc
      σ g.val = (σ g.val * g.val) * g.inv := by rw [mul_assoc, g.val_inv, mul_one]
      _ = g.inv := by rw [h, one_mul]
  constructor
  · intro h
    have hleft : σ a * a = 1 := by
      apply sub_eq_zero.mp
      apply (b.baseChange R).repr.injective
      ext i
      exact h (.inl (true, i))
    have hright : a * σ a = 1 := by
      apply sub_eq_zero.mp
      apply (b.baseChange R).repr.injective
      ext i
      exact h (.inl (false, i))
    let g : (R ⊗[k] ρ.fixedSubalgebra)ˣ := ⟨a, σ a, hright, hleft⟩
    have hg : g ∈ (D.involution.baseChange R).isometries := hleft
    refine ⟨⟨g, ⟨hg, ?_⟩⟩, rfl⟩
    have htrace (x : R ⊗[k] symmetricPart D.involution) :
        pairAmbientTrace D p R (a * pairSymmetricMap D R x * σ a) = pairTraceMap D R x := by
      induction x with
      | tmul r x =>
        have hx := sub_eq_zero.mp (h (.inr x))
        change pairAmbientTrace D p R (a * (1 ⊗ₜ[k] x.val) * σ a) =
          pairTraceMap D R (1 ⊗ₜ[k] x) at hx
        have hr : r ⊗ₜ[k] x = r • ((1 : R) ⊗ₜ[k] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hr, map_smul, map_smul,
          Algebra.mul_smul_comm r a (pairSymmetricMap D R ((1 : R) ⊗ₜ[k] x)),
          Algebra.smul_mul_assoc r _ (σ a), map_smul]
        exact congrArg (r • ·) hx
      | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy]
    intro x
    obtain ⟨y, hy⟩ := pairConjugate_fixed D R g hg x
    refine ⟨y, hy, ?_⟩
    change pairTraceMap D R y = pairTraceMap D R x
    rw [← htrace x, ← show pairSymmetricMap D R y = a * pairSymmetricMap D R x * σ a from hy]
    exact (pairAmbientTrace_eq D p hp R y).symm
  · rintro ⟨g, rfl⟩ i
    obtain ⟨hg, htrace⟩ := g.property
    have hσ : (D.involution.baseChange R).toLinearMap g.val.val = g.val.inv := hU g.val hg
    rcases i with ⟨ε, i⟩ | x
    · cases ε <;> simp only [pairEquations, Sum.elim_inl, Bool.false_eq_true, ite_false, ite_true,
        hσ, g.val.inv_val, g.val.val_inv, sub_self, map_zero, Finsupp.zero_apply]
    · obtain ⟨y, hy, ht⟩ := htrace ((1 : R) ⊗ₜ[k] x)
      change pairAmbientTrace D p R (g.val.val * (1 ⊗ₜ[k] x.val) * σ g.val.val) -
        pairTraceMap D R (1 ⊗ₜ[k] x) = 0
      rw [hσ, ← show pairSymmetricMap D R y = g.val.val * (1 ⊗ₜ[k] x.val) * g.val.inv from hy,
        pairAmbientTrace_eq D p hp]
      exact sub_eq_zero.mpr ht

private def pairFromCoordinates (R : TestAlgebra k) (x : Fin d → R) :
    R ⊗[k] ρ.fixedSubalgebra :=
  (b.baseChange R).repr.symm (Finsupp.equivFunOnFinite.symm x)

private theorem pairFromCoordinates_repr (R : TestAlgebra k) (x : Fin d → R) (i : Fin d) :
    (b.baseChange R).repr (pairFromCoordinates b R x) i = x i := by
  simp [pairFromCoordinates]

private theorem pairFromCoordinates_natural {R S : TestAlgebra k} (f : R ⟶ S) (x : Fin d → R) :
    tensorMap f (pairFromCoordinates b R x) = pairFromCoordinates b S (f.hom ∘ x) := by
  apply (b.baseChange S).repr.injective
  ext i
  rw [pairBasis_repr_natural, pairFromCoordinates_repr, pairFromCoordinates_repr]
  rfl

private abbrev pairPolynomialTest : TestAlgebra k := CommAlgCat.of k (MvPolynomial (Fin d) k)

private def pairGenericElement : (pairPolynomialTest (k := k) (d := d)) ⊗[k] ρ.fixedSubalgebra :=
  pairFromCoordinates b pairPolynomialTest MvPolynomial.X

private def pairIdeal : Ideal (MvPolynomial (Fin d) k) :=
  Ideal.span (Set.range (pairEquations D b p pairPolynomialTest (pairGenericElement b)))

private abbrev PairCoordinates := MvPolynomial (Fin d) k ⧸ pairIdeal D b p

private abbrev pairQuotient : MvPolynomial (Fin d) k →ₐ[k] PairCoordinates D b p :=
  Ideal.Quotient.mkₐ k (pairIdeal D b p)

private theorem pairGeneric_eval (R : TestAlgebra k) (f : MvPolynomial (Fin d) k →ₐ[k] R) :
    tensorMap (CommAlgCat.ofHom f : pairPolynomialTest ⟶ R) (pairGenericElement b) =
      pairFromCoordinates b R (fun i => f (MvPolynomial.X i)) :=
  pairFromCoordinates_natural b (CommAlgCat.ofHom f) _

include hp in
set_option maxHeartbeats 450000 in
private theorem pairPoint_exists (R : TestAlgebra k) (f : PairCoordinates D b p →ₐ[k] R) :
    ∃ g : (pairIsometryPoints D).obj R,
      g.val.val = pairFromCoordinates b R (fun i => f (pairQuotient D b p (MvPolynomial.X i))) := by
  apply (pairEquations_iff_eval D b p hp R _).mp
  intro i
  change pairEquations D b p R
    (pairFromCoordinates b R (fun j => (f.comp (pairQuotient D b p)) (MvPolynomial.X j))) i = 0
  rw [← pairGeneric_eval b R (f.comp (pairQuotient D b p)), pairEquations_natural]
  change f (pairQuotient D b p (pairEquations D b p pairPolynomialTest (pairGenericElement b) i)) = 0
  rw [show pairQuotient D b p (pairEquations D b p pairPolynomialTest (pairGenericElement b) i) = 0
    from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩), map_zero]

private def pairEvaluation (R : TestAlgebra k) (f : PairCoordinates D b p →ₐ[k] R) :
    (pairIsometryPoints D).obj R := (pairPoint_exists D b p hp R f).choose

private theorem pairEvaluation_val (R : TestAlgebra k) (f : PairCoordinates D b p →ₐ[k] R) :
    (pairEvaluation D b p hp R f).val.val =
      pairFromCoordinates b R (fun i => f (pairQuotient D b p (MvPolynomial.X i))) :=
  (pairPoint_exists D b p hp R f).choose_spec

set_option maxHeartbeats 450000 in
private def pairCoordinateMap (R : TestAlgebra k) (g : (pairIsometryPoints D).obj R) :
    PairCoordinates D b p →ₐ[k] R := by
  let f : MvPolynomial (Fin d) k →ₐ[k] R := MvPolynomial.aeval (fun i => (b.baseChange R).repr g.val.val i)
  refine Ideal.Quotient.liftₐ (pairIdeal D b p) f ?_
  have hle : pairIdeal D b p ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hz : tensorMap (CommAlgCat.ofHom f : pairPolynomialTest ⟶ R) (pairGenericElement b) =
        g.val.val := by
      rw [pairGeneric_eval]
      apply (b.baseChange R).repr.injective
      ext j
      rw [pairFromCoordinates_repr]
      exact MvPolynomial.aeval_X _ _
    change (CommAlgCat.ofHom f : pairPolynomialTest ⟶ R).hom
      (pairEquations D b p pairPolynomialTest (pairGenericElement b) i) = 0
    rw [← pairEquations_natural D b p (CommAlgCat.ofHom f), hz]
    exact (pairEquations_iff_eval D b p hp R _).mpr ⟨g, rfl⟩ i
  exact fun a ha => hle ha

private theorem pairCoordinateMap_X (R : TestAlgebra k) (g : (pairIsometryPoints D).obj R) (i : Fin d) :
    pairCoordinateMap D b p hp R g (pairQuotient D b p (MvPolynomial.X i)) =
      (b.baseChange R).repr g.val.val i :=
  MvPolynomial.aeval_X _ _

private def pairRepresentation : Representation (PairCoordinates D b p) (pairIsometryPoints D) :=
  Representation.mk
    (fun R => {
      toFun := pairEvaluation D b p hp R
      invFun := pairCoordinateMap D b p hp R
      left_inv := fun f => by
        apply Ideal.Quotient.algHom_ext k
        apply MvPolynomial.algHom_ext
        intro i
        change pairCoordinateMap D b p hp R (pairEvaluation D b p hp R f)
          (pairQuotient D b p (MvPolynomial.X i)) = f (pairQuotient D b p (MvPolynomial.X i))
        rw [pairCoordinateMap_X, pairEvaluation_val, pairFromCoordinates_repr]
      right_inv := fun g => by
        apply Subtype.ext
        apply Units.ext
        rw [pairEvaluation_val]
        apply (b.baseChange R).repr.injective
        ext i
        rw [pairFromCoordinates_repr, pairCoordinateMap_X] })
    (fun f a => by
      apply Subtype.ext
      apply Units.ext
      change (pairEvaluation D b p hp _ _).val.val = tensorMap f (pairEvaluation D b p hp _ a).val.val
      rw [pairEvaluation_val, pairEvaluation_val, pairFromCoordinates_natural]
      rfl)

private theorem pairIsometry_represented :
    ∃ H : AffineAlgebraicGroup k, Nonempty ((groupPointsFunctor k).obj H.val ≅ pairIsometryPoints D) := by
  let : FiniteDimensional k ρ.fixedSubalgebra := D.centralSimple.2.2
  let b := Module.finBasis k ρ.fixedSubalgebra
  obtain ⟨C, hC⟩ := (symmetricPart D.involution).exists_isCompl
  let p := (symmetricPart D.involution).projectionOnto C hC
  have hp := Submodule.projectionOnto_apply_left hC
  let P := pairRepresentation D b p hp
  let : HopfAlgebra k (PairCoordinates D b p) := Representation.hopf P
  let : Algebra.FiniteType k (PairCoordinates D b p) :=
    Algebra.FiniteType.of_surjective (pairQuotient D b p) Ideal.Quotient.mk_surjective
  exact ⟨Specs.StandardGroups.spectrum k (PairCoordinates D b p),
    ⟨spectrumPointsIso (Representation.convolutionIso P)⟩⟩

end PairRepresentation

section PairModelComparison

open private groupBaseChangePointIso from LinearAlgebraicGroups.Affine.RationalRepresentations

variable [Nonempty I]

omit [Nonempty I] in
private theorem splitPairAt_natural {S T : TestAlgebra K} (f : S ⟶ T)
    (x : (restrictTestAlgebra k K).obj S ⊗[k] ρ.fixedSubalgebra) :
    let R := (restrictTestAlgebra k K).obj S
    let U := (restrictTestAlgebra k K).obj T
    letI : Algebra k S := R.algebra
    letI : Algebra k T := U.algebra
    letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower k K T := IsScalarTower.of_algebraMap_eq' rfl
    splitPairAt D T (tensorMap ((restrictTestAlgebra k K).map f) x) =
      (splitPairAt D S x).map f.hom := by
  intro R U
  let : Algebra k S := R.algebra
  let : Algebra k T := U.algebra
  let : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k K T := IsScalarTower.of_algebraMap_eq' rfl
  induction x with
  | tmul r x =>
    change splitPairAt D T (f.hom r ⊗ₜ[k] x) = _
    rw [splitPairAt_tmul, splitPairAt_tmul]
    apply Matrix.ext
    intro i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, f.hom.commutes]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (Matrix.map_add f.hom (map_add f.hom) _ _).symm

private theorem splitPairAt_isometry (R : TestAlgebra k) [Algebra K R] [IsScalarTower k K R]
    (a : (R ⊗[k] ρ.fixedSubalgebra)ˣ) :
    IsPairIsometry D R a ↔ Units.map (splitPairAt D R).toMonoidHom a ∈ orthogonalMatrices I R := by
  obtain ⟨E, hE, h⟩ := pairIsometryScalarExtension D R
  have he : E = splitPairAt D R := by
    apply AlgEquiv.ext
    intro x
    induction x with
    | tmul r x => exact (hE r x).trans (splitPairAt_tmul D r x).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  exact he ▸ h a

private def splitPairIsometryEquiv (S : TestAlgebra K) :
    (pairIsometryPoints D).obj ((restrictTestAlgebra k K).obj S) ≃* orthogonalMatrices I S := by
  let R := (restrictTestAlgebra k K).obj S
  letI : Algebra k S := R.algebra
  letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra K R := S.algebra
  letI : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq' (by
    change algebraMap k S = (algebraMap K S).comp (algebraMap k K)
    rfl)
  let E := Units.mapEquiv (splitPairAt D S).toMulEquiv
  refine
    { toFun := fun a => ⟨E a.val, (splitPairAt_isometry D R a.val).mp a.property⟩
      invFun := fun a => ⟨E.symm a.val, (splitPairAt_isometry D R (E.symm a.val)).mpr
        (by change E (E.symm a.val) ∈ orthogonalMatrices I S; rw [E.apply_symm_apply]; exact a.property)⟩
      left_inv := fun a => Subtype.ext (E.symm_apply_apply a.val)
      right_inv := fun a => Subtype.ext (E.apply_symm_apply a.val)
      map_mul' := fun a b => Subtype.ext (map_mul E a.val b.val) }

private def splitPairIsometryIso :
    restrictTestAlgebra k K ⋙ pairIsometryPoints D ≅ orthogonalMatrixPoints K I :=
  NatIso.ofComponents (fun S => (splitPairIsometryEquiv D S).toGrpIso) (by
    intro S T f
    apply GrpCat.ext
    intro a
    apply Subtype.ext
    apply Units.ext
    exact splitPairAt_natural D f a.val.val)

private def splitOrthogonalPointsIso (O : SplitOrthogonalPresentation K I) :
    (groupPointsFunctor K).obj O.group.val ≅ orthogonalMatrixPoints K I :=
  NatIso.ofComponents (fun R => (O.points R).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro a
    apply Subtype.ext
    apply Units.ext
    exact O.naturality f a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 420000 in
/-- Representability of the full pair-isometry functor and its scalar extension
to the full split hyperbolic isometry group. -/
theorem pairIsometryModel : PairIsometryModel.{u} := by
  intro k K I _ _ _ _ _ _ ρ D O
  obtain ⟨H, ⟨p⟩⟩ := pairIsometry_represented D
  let H' := Specs.Unipotent.baseChangedAlgebraicGroup K H
  let r := groupBaseChangePointIso K H.val
  let s : (groupPointsFunctor K).obj H'.val ≅ (groupPointsFunctor K).obj O.group.val :=
    r ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k K) p ≪≫ splitPairIsometryIso D ≪≫
    (splitOrthogonalPointsIso O).symm
  let j := AffineAlgebraicGroup.groupHomEquiv H' O.group
  let j' := AffineAlgebraicGroup.groupHomEquiv O.group H'
  let e : H'.val ≅ O.group.val := by
    refine ⟨j.symm s.hom, j'.symm s.inv, ?_, ?_⟩
    · apply (AffineAlgebraicGroup.groupHomEquiv H' H').injective
      change (groupPointsFunctor K).map (j.symm s.hom ≫ j'.symm s.inv) = (groupPointsFunctor K).map (𝟙 _)
      rw [Functor.map_comp, (groupPointsFunctor K).map_id H'.val]
      change j (j.symm s.hom) ≫ j' (j'.symm s.inv) = _
      rw [j.apply_symm_apply, j'.apply_symm_apply, Iso.hom_inv_id]
    · apply (AffineAlgebraicGroup.groupHomEquiv O.group O.group).injective
      change (groupPointsFunctor K).map (j'.symm s.inv ≫ j.symm s.hom) = (groupPointsFunctor K).map (𝟙 _)
      rw [Functor.map_comp, (groupPointsFunctor K).map_id O.group.val]
      change j' (j'.symm s.inv) ≫ j (j.symm s.hom) = _
      rw [j.apply_symm_apply, j'.apply_symm_apply, Iso.inv_hom_id]
  let m (R : TestAlgebra k) := (pairIsometrySubgroup D R).subtype.comp (p.hom.app R).hom
  refine ⟨H, m, e, ?_, ?_, ?_, ?_⟩
  · intro R S f a
    exact congrArg Subtype.val (ConcreteCategory.congr_hom (p.hom.naturality f) a)
  · intro R
    exact Subtype.val_injective.comp ((p.app R).groupIsoToMulEquiv.injective)
  · intro R g
    constructor
    · rintro ⟨a, rfl⟩
      exact (p.hom.app R a).property
    · intro hg
      obtain ⟨a, ha⟩ := (p.app R).groupIsoToMulEquiv.surjective ⟨g, hg⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  · intro S R
    let : Algebra k S := R.algebra
    let : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
    refine ⟨splitPairAt D S, splitPairAt_tmul D, fun a => ?_⟩
    have he : a ≫ e.hom.hom.hom = s.hom.app S a := congrArg (fun f => f.app S a) (j.apply_symm_apply s.hom)
    rw [he]
    let q := splitOrthogonalPointsIso O
    let w : (orthogonalMatrixPoints K I).obj S := (splitPairIsometryEquiv D S) (p.hom.app R (baseChangePoint k K H.val.X S a))
    have hw : s.hom.app S a = (q.app S).inv w := rfl
    rw [hw]
    change w.val.val = ((q.app S).groupIsoToMulEquiv ((q.app S).groupIsoToMulEquiv.symm w)).val.val
    exact congrArg (fun z : (orthogonalMatrixPoints K I).obj S => z.val.val)
      ((q.app S).groupIsoToMulEquiv.apply_symm_apply w).symm

end PairModelComparison

end

end DescendedPairIsometries


section FiniteSpinReference

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Pinning (AttachedDatum PinnedGroup PinnedIso SplitBorelPair)
open Specs.GeometricRadicals (GeometricGroup IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple PreservesCartan)
open LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso pinningsExist)
open private groupBaseChangeTower radical_transport solvable_of_iso
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private centralIsogeny_postIso from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence

noncomputable section

variable {k : Type u} [Field k]

private def geometricIsoOfSeparableIso {H G : AffineAlgebraicGroup k}
    (e : (groupBaseChange k (SeparableClosure k)).obj H.val ≅
      (groupBaseChange k (SeparableClosure k)).obj G.val) :
    (GeometricGroup H).val ≅ (GeometricGroup G).val := by
  let S := SeparableClosure k
  let K := AlgebraicClosure k
  let q := groupBaseChangeTower (k := k) (K := S) K
  exact q.app H.val ≪≫ (groupBaseChange S K).mapIso e ≪≫ (q.app G.val).symm

private theorem simplyConnectedOfSeparableIso {H G : AffineAlgebraicGroup k}
    (e : (groupBaseChange k (SeparableClosure k)).obj H.val ≅
      (groupBaseChange k (SeparableClosure k)).obj G.val)
    (hG : GeometricallySimplyConnected G) : GeometricallySimplyConnected H := by
  let f := geometricIsoOfSeparableIso e
  intro J hJ p hp
  let := hG J hJ (p ≫ f.hom) (centralIsogeny_postIso f hp)
  exact IsIso.of_isIso_comp_right p f.hom

private theorem semisimpleOfSeparableIso {H G : AffineAlgebraicGroup k}
    (hH : Specs.GeometricRadicals.IsReductive H)
    (e : (groupBaseChange k (SeparableClosure k)).obj H.val ≅
      (groupBaseChange k (SeparableClosure k)).obj G.val)
    (hG : IsSemisimple G) : IsSemisimple H := by
  let f := geometricIsoOfSeparableIso e
  let P (J : AffineAlgebraicGroup (AlgebraicClosure k)) := Specs.SchemeDerivedGroup.IsSolvable J.val
  let M := Specs.GeometricRadicals.geometricSolvableRadical G
  have hM := GeometricRadicals.geometricSolvableRadicalLargest G
  have hM' := radical_transport f.symm P
    (fun d hX hY => solvable_of_iso d hX.1 hX.2.1 hY.1 hY.2.1) M hM
  have hN := GeometricRadicals.geometricSolvableRadicalLargest H
  obtain ⟨j, _, _⟩ := GeometricRadicals.radicalUnique (GeometricGroup H) P hN hM'
  obtain ⟨r⟩ := hG.2.2
  exact ⟨hH.1, hH.2.1, ⟨j ≪≫ r⟩⟩

private theorem pinnedTypeDRelabelling
    {L : Specs.RootGroups.AdditiveLine k} (P : PinnedGroup L)
    (Q : SplitBorelPair k) (D : AttachedDatum P.pair) (E : AttachedDatum Q)
    (hD : letI := D.comm; Specs.SimplyConnectedLattice.corootLattice D = ⊤)
    (hE : letI := E.comm; Specs.SimplyConnectedLattice.corootLattice E = ⊤)
    (n : ℕ) (s : Fin n ≃ ↥D.toBased.base.support) (t : Fin n ≃ ↥E.toBased.base.support)
    (hs : ∀ i j, D.toBased.datum.pairing (s j).val (s i).val = CartanMatrix.D n i j)
    (ht : ∀ i j, E.toBased.datum.pairing (t j).val (t i).val = CartanMatrix.D n i j)
    (a : Equiv.Perm (Fin n)) (ha : PreservesCartan (CartanMatrix.D n) (CartanMatrix.D n) a) :
    ∃ (U : Specs.OrderedRootProducts.RootSubgroupFamily Q.T) (p : Specs.Pinning.Pinning L Q U)
      (j : PinnedIso (⟨Q, U, p⟩ : PinnedGroup L) P),
        ∀ i, (inducedBasedIso j E D).val.indexEquiv (t i).val = (s (a i)).val := by
  let := D.comm
  let := E.comm
  let r : ↥E.toBased.base.support ≃ ↥D.toBased.base.support := (t.symm.trans a).trans s
  have hr : PreservesCartan (RootData.integralCartan E.toBased.datum E.toBased.base)
      (RootData.integralCartan D.toBased.datum D.toBased.base) r := by
    intro i j
    obtain ⟨i, rfl⟩ := t.surjective i
    obtain ⟨j, rfl⟩ := t.surjective j
    change E.toBased.datum.pairing (t j).val (t i).val =
      D.toBased.datum.pairing (r (t j)).val (r (t i)).val
    have he (q : Fin n) : r (t q) = s (a q) := by simp [r]
    rw [he i, he j, hs, ht]
    exact ha i j
  obtain ⟨f, hf, _⟩ :=
    (RootData.AbsoluteDynkinTypes.cartanDeterminesBasedDatum E.toBased D.toBased hE hD r).mp hr
  obtain ⟨U, ⟨p⟩⟩ := pinningsExist L Q
  let Q' : PinnedGroup L := ⟨Q, U, p⟩
  obtain ⟨j, hj⟩ := pinnedLift Q' P E D f
  refine ⟨U, p, j, ?_⟩
  intro i
  change (inducedBasedIso j E D).val.indexEquiv (t i).val = _
  rw [hj, hf]
  simp [r]

open private finiteLevelSchemeIso from LinearAlgebraicGroups.Arithmetic.TypeCSplitRecognition

/-- The actual split Clifford spin cover is a finite Galois reference for a
simply connected form with a fixed vector vertex. -/
theorem finiteSpinReference : FiniteSpinReference.{u} := by
  intro k _ G n hn hG hsc hfixed P₀
  obtain ⟨L, P, D, _, _, _, e, _, s, i, _, hs, hi, _⟩ := hfixed
  have hP := semisimpleOfSeparableIso P.pair.reductive e hG.1
  have hPsc := simplyConnectedOfSeparableIso e hsc
  let := D.comm
  have hD := (Classification.SimplyConnectedLattice.latticeCriterion P.pair.G hP P.pair.T
    P.pair.split P.pair.maximal D.datum).mp hPsc
  obtain ⟨B, E, e₀, _, _, hE, t, _, _, ht, _, _, _, _⟩ := splitSpinTypeD k n hn P₀
  obtain ⟨a, ha, _, _⟩ := vectorVertexStabilizer n hn i hi
  obtain ⟨_, _, j, _⟩ := pinnedTypeDRelabelling P B D E hD hE n s t hs ht a ha
  exact finiteLevelSchemeIso P₀.spin G
    ((groupBaseChange k (SeparableClosure k)).mapIso (e₀.symm ≪≫ j.group) ≪≫ e)

end

end FiniteSpinReference


section SpinPlaneSwitch

open Matrix AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OddSpinModels (hyperbolicForm coordinateVector evenSum)
open Specs.SymplecticMatrixStructure (hyperbolicDiagonal)
open Specs.CharacterDescent (Cocharacter)
open Specs.AdjointRepresentation (GroupPoints)
open private vectors_injective from LinearAlgebraicGroups.Albert.SpinFunctor
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private sections_factor_of_affine from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]

private def matrixSimilitude {R : Type u} [CommRing R]
    (g : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ) (c : Rˣ)
    (hc : ∀ x, hyperbolicForm I R (g.val *ᵥ x) = (c : R) * hyperbolicForm I R x) :
    quadraticSimilitudes (hyperbolicForm I R) :=
  ⟨(matrixColumnEquiv g, c), fun x => hc x⟩

private theorem matrixSimilitude_matrix {R : Type u} [CommRing R]
    (g : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ) (c : Rˣ)
    (hc : ∀ x, hyperbolicForm I R (g.val *ᵥ x) = (c : R) * hyperbolicForm I R x) :
    let b := Pi.basisFun R (I ⊕ I)
    LinearMap.toMatrix b b (matrixSimilitude g c hc).val.1.toLinearMap = g.val := by
  intro b
  change LinearMap.toMatrix b b (Matrix.toLin' g.val) = g.val
  rw [← Matrix.toLin_eq_toLin', LinearMap.toMatrix_toLin]

private theorem matrixSimilitude_inverse_matrix {R : Type u} [CommRing R]
    (g : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ) (c : Rˣ)
    (hc : ∀ x, hyperbolicForm I R (g.val *ᵥ x) = (c : R) * hyperbolicForm I R x) :
    let b := Pi.basisFun R (I ⊕ I)
    LinearMap.toMatrix b b (matrixSimilitude g c hc).val.1.symm.toLinearMap = g.inv := by
  intro b
  have h : (matrixSimilitude g c hc).val.1.symm = matrixColumnEquiv g⁻¹ :=
    (map_inv matrixColumnEquiv g).symm
  rw [h]
  change LinearMap.toMatrix b b (Matrix.toLin' g.inv) = g.inv
  rw [← Matrix.toLin_eq_toLin', LinearMap.toMatrix_toLin]

variable [LinearOrder (I ⊕ I)]
variable (P : SplitSpinVectorImage k I)

set_option maxHeartbeats 760000 in
private theorem spinSchemeAction_fixesScalar (P : SplitSpinVectorImage k I)
    (g : quadraticSimilitudes (hyperbolicForm I k)) (R : TestAlgebra k)
    (a : Points P.kernel.group.X R) :
    a ≫ P.kernel.inclusion.hom.hom ≫ (spinSchemeAction P g).hom.hom.hom =
      a ≫ P.kernel.inclusion.hom.hom := by
  let x := a ≫ P.kernel.inclusion.hom.hom
  let r := (P.kernelPoints R a).val.val
  let q := hyperbolicForm I k
  let T := Algebra.TensorProduct.map (AlgHom.id R R) (evenCliffordEquiv g).toAlgHom
  have hx : (P.spinPoints R x).val = algebraMap R (Albert.SpinSpecification.ScalarClifford q R) r :=
    P.scalar R a
  apply (P.spinRepresents.1 R).1
  apply Units.ext
  rw [← Category.assoc, spinSchemeAction_points, spinActionPoint_formula]
  change evenTensorInclusion q R (T (spinEvenPoint P R x).val) = (P.spinPoints R x).val
  have hs : (spinEvenPoint P R x).val = algebraMap R _ r := by
    apply evenTensorInclusion_injective q R
    rw [(evenTensorInclusion q R).commutes]
    exact (congrArg Units.val (spinEvenPoint_formula P R x)).trans hx
  rw [hs, T.commutes, (evenTensorInclusion q R).commutes, hx]

set_option maxHeartbeats 500000 in
private theorem spinSchemeAction_matrix (g : (Matrix (I ⊕ I) (I ⊕ I) k)ˣ) (c : kˣ)
    (hc : ∀ x, hyperbolicForm I k (g.val *ᵥ x) = (c : k) * hyperbolicForm I k x)
    (R : TestAlgebra k) (a : Points P.spin.val.X R) :
    spinVectorMatrix P R (a ≫ (spinSchemeAction P (matrixSimilitude g c hc)).hom.hom.hom) =
      conjugate (Matrix.GeneralLinearGroup.map (algebraMap k R) g) (spinVectorMatrix P R a) := by
  let b := Pi.basisFun k (I ⊕ I)
  let β := b.baseChange R
  have baseMatrix (f : Module.End k (I ⊕ I → k)) :
      LinearMap.toMatrix β β (f.baseChange R) =
        (LinearMap.toMatrix b b f).map (algebraMap k R) := by
    ext i j
    simp only [β, LinearMap.toMatrix_apply, Module.Basis.baseChange_apply,
      LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul,
      Matrix.map_apply, Algebra.algebraMap_eq_smul_one]
  let s := matrixSimilitude g c hc
  let t := LinearEquiv.baseChange k R (I ⊕ I → k) (I ⊕ I → k) s.val.1
  let a' := a ≫ (spinSchemeAction P s).hom.hom.hom
  obtain ⟨u, hu, hM⟩ := P.vector R a
  obtain ⟨v, hv, hM'⟩ := P.vector R a'
  have hC := spinActionPoint_vector P R s a hu
  have hW : v = t * u * t⁻¹ := by
    ext x
    apply vectors_injective (hyperbolicForm I k) R b
    exact (hv x).trans (by
      rw [show a' = spinActionPoint P R s a from spinSchemeAction_points P R s a]
      exact (hC x).symm)
  change LinearMap.toMatrix β β u.toLinearMap = spinVectorMatrix P R a at hM
  change LinearMap.toMatrix β β v.toLinearMap = spinVectorMatrix P R a' at hM'
  change spinVectorMatrix P R a' = _
  rw [← hM', ← hM, hW]
  change LinearMap.toMatrix β β ((t.toLinearMap.comp u.toLinearMap).comp t.symm.toLinearMap) = _
  rw [LinearMap.toMatrix_comp β β β, LinearMap.toMatrix_comp β β β]
  have ht : LinearMap.toMatrix β β t.toLinearMap = g.val.map (algebraMap k R) := by
    change LinearMap.toMatrix β β (s.val.1.toLinearMap.baseChange R) = _
    rw [baseMatrix, matrixSimilitude_matrix]
  have ht' : LinearMap.toMatrix β β t.symm.toLinearMap = g.inv.map (algebraMap k R) := by
    change LinearMap.toMatrix β β (s.val.1.symm.toLinearMap.baseChange R) = _
    rw [baseMatrix, matrixSimilitude_inverse_matrix]
  rw [ht, ht']
  rfl

omit [LinearOrder (I ⊕ I)] in
private theorem hyperbolicPlaneSwitch (i : I) :
    ∃ (g : (Matrix (I ⊕ I) (I ⊕ I) k)ˣ)
      (_h : ∀ x, hyperbolicForm I k (g.val *ᵥ x) = hyperbolicForm I k x),
      g * g = 1 ∧
      ∀ (R : TestAlgebra k) (t : I → Rˣ),
        conjugate (Matrix.GeneralLinearGroup.map (algebraMap k R) g) (hyperbolicDiagonal t) =
          hyperbolicDiagonal (fun j => if j = i then (t j)⁻¹ else t j) := by
  let s : Equiv.Perm (I ⊕ I) := Equiv.swap (Sum.inl i) (Sum.inr i)
  obtain ⟨g, hg, hv, he, _⟩ := (vectorDiagramSwitch.{u}).1 I k i
  have hg' : g.val = s.permMatrix k := Matrix.mulVec_injective
    (funext fun x => (hv x).trans (Matrix.permMatrix_mulVec s (v := x)).symm)
  refine ⟨g, he, hg, fun R t => ?_⟩
  obtain ⟨h, _, hv', _, hh⟩ := (vectorDiagramSwitch.{u}).1 I R i
  have hh' : h.val = s.permMatrix R := Matrix.mulVec_injective
    (funext fun x => (hv' x).trans (Matrix.permMatrix_mulVec s (v := x)).symm)
  rw [show Matrix.GeneralLinearGroup.map (algebraMap k R) g = h from Units.ext (by
    change g.val.map (algebraMap k R) = h.val
    rw [hg', hh']
    ext a b
    by_cases e : s a = b <;> simp [Equiv.Perm.permMatrix, e])]
  exact hh t

private theorem spinSchemeAction_involution (g : (Matrix (I ⊕ I) (I ⊕ I) k)ˣ)
    (hg : g * g = 1) (h : ∀ x, hyperbolicForm I k (g.val *ᵥ x) = hyperbolicForm I k x) :
    let s := matrixSimilitude g 1 (fun x => (h x).trans (one_mul _).symm)
    (spinSchemeAction P s).hom ≫ (spinSchemeAction P s).hom = 𝟙 P.spin.val := by
  intro s
  have hs : s * s = 1 := by
    apply Subtype.ext
    apply Prod.ext
    · change matrixColumnEquiv g * matrixColumnEquiv g = 1
      rw [← map_mul, hg, map_one]
    · exact one_mul _
  apply Grp.hom_ext
  apply hom_ext_of_points P.spin.property.1
  intro R a
  change a ≫ (spinSchemeAction P s).hom.hom.hom ≫ (spinSchemeAction P s).hom.hom.hom = a ≫ 𝟙 _
  rw [← Category.assoc, spinSchemeAction_points, spinSchemeAction_points,
    ← spinActionPoint_mul, hs, spinActionPoint_one, Category.comp_id]

private theorem involution_restricts {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val)
    (f : G.val ⟶ G.val) (hf : f ≫ f = 𝟙 _)
    (hT : ∀ (R : TestAlgebra k) (a : Points T.group.X R),
      ∃ b : Points T.group.X R, b ≫ T.inclusion.hom.hom = a ≫ (T.inclusion ≫ f).hom.hom) :
    ∃ e : T.group ≅ T.group, e.hom ≫ T.inclusion = T.inclusion ≫ f := by
  let U := Specs.Unipotent.closedSubgroupAlgebraicGroup T
  obtain ⟨i, hi⟩ := sections_factor_of_affine T U.property.1 (T.inclusion ≫ f).hom.hom hT
  obtain ⟨j, hj⟩ := factor_group_through_subgroup T (T.inclusion ≫ f) i hi
  let := T.isClosedImmersion
  have hmono : Mono T.inclusion.hom.hom := Over.mono_of_mono_left T.inclusion.hom.hom
  have h := congrArg (fun g : T.group ⟶ G.val => g.hom.hom) hj
  change j.hom.hom ≫ T.inclusion.hom.hom = T.inclusion.hom.hom ≫ f.hom.hom at h
  have h' := congrArg (fun g : G.val ⟶ G.val => g.hom.hom) hf
  change f.hom.hom ≫ f.hom.hom = 𝟙 _ at h'
  have hh : j ≫ j = 𝟙 _ := by
    apply Grp.hom_ext
    apply (cancel_mono T.inclusion.hom.hom).mp
    change (j.hom.hom ≫ j.hom.hom) ≫ T.inclusion.hom.hom = (𝟙 _) ≫ _
    rw [Category.assoc, h, ← Category.assoc, h, Category.assoc, h', Category.comp_id, Category.id_comp]
  exact ⟨⟨j, j, hh, hh⟩, hj⟩

omit [LinearOrder (I ⊕ I)] in
private theorem laurentParameter_zpow_injective (R : TestAlgebra k) [Nontrivial R] :
    Function.Injective (fun n : ℤ => (CocharacterDynamics.laurentParameter R)^n) := by
  let m : Multiplicative ℤ →* (CocharacterDynamics.laurentAlgebra R)ˣ :=
    { toFun := fun n =>
        ⟨LaurentPolynomial.T n.toAdd, LaurentPolynomial.T (-n.toAdd),
          by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero],
          by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]⟩
      map_one' := Units.ext LaurentPolynomial.T_zero
      map_mul' := fun a b => Units.ext (LaurentPolynomial.T_add a.toAdd b.toAdd) }
  have hm (n : ℤ) : ((CocharacterDynamics.laurentParameter R) ^ n).val =
      (LaurentPolynomial.T n : LaurentPolynomial R) := by
    have h : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
      apply Multiplicative.toAdd.injective
      simp
    exact congrArg Units.val ((map_zpow m _ _).symm.trans (congrArg m h))
  intro a b h
  have he := congrArg Units.val h
  rw [hm a, hm b] at he
  by_contra hab
  have hc := congrArg (fun f : LaurentPolynomial R => f.coeff a) he
  simp [LaurentPolynomial.T_apply, Ne.symm hab] at hc

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private theorem planeSwitch_diagonalAction {m : ℕ} (d : Fin (m + 1) ≃ I) (i : I)
    (g : (Matrix (I ⊕ I) (I ⊕ I) k)ˣ)
    (hg : g * g = 1) (h : ∀ x, hyperbolicForm I k (g.val *ᵥ x) = hyperbolicForm I k x)
    (hv : ∀ (R : TestAlgebra k) (s : I → Rˣ),
      conjugate (Matrix.GeneralLinearGroup.map (algebraMap k R) g) (hyperbolicDiagonal s) =
        hyperbolicDiagonal (fun j => if j = i then (s j)⁻¹ else s j)) :
    let T := splitDiagonalTorus P d
    let A := spinSchemeAction P (matrixSimilitude g 1 (fun x => (h x).trans (one_mul _).symm))
    ∃ e : T.group ≅ T.group,
      e.hom ≫ T.inclusion = T.inclusion ≫ A.hom ∧
      ∀ c : Cocharacter T.group,
        (diagonalCocharacterLattice P d (Additive.ofMul (c ≫ e.hom))).val =
          invertCoordinate i (diagonalCocharacterLattice P d (Additive.ofMul c)).val := by
  intro T A
  have h₁ := spinSchemeAction_involution P g hg h
  obtain ⟨e, he⟩ := involution_restricts T A.hom h₁ (fun R a => by
    change ∃ b : Points T.group.X R, b ≫ T.inclusion.hom.hom = a ≫ T.inclusion.hom.hom ≫ A.hom.hom.hom
    let u := a ≫ T.inclusion.hom.hom
    obtain ⟨s, hs⟩ := (splitDiagonalTorus_range P d R u).mp ⟨a, rfl⟩
    apply (splitDiagonalTorus_range P d R _).mpr
    let t (j : Fin (m + 1)) := if d j = i then (s j)⁻¹ else s j
    refine ⟨t, ?_⟩
    change spinVectorMatrix P R (u ≫ A.hom.hom.hom) = _
    rw [spinSchemeAction_matrix P g 1, show spinVectorMatrix P R u = _ from hs,
      reindex_middle_diagonal, hv, reindex_middle_diagonal]
    congr 1
    funext j
    simp only [t, d.apply_symm_apply])
  refine ⟨e, he, fun c => ?_⟩
  let R := CocharacterDynamics.laurentAlgebra (CommAlgCat.of k k)
  let z := CocharacterDynamics.laurentParameter (CommAlgCat.of k k)
  let v := diagonalCocharacterLattice P d
  have hmap := congrArg (fun f : T.group ⟶ P.spin.val => f.hom.hom) he
  let w : Points T.group.X R := cocharacterPoint c R z
  have heval : (cocharacterPoint (c ≫ e.hom) R z) ≫ T.inclusion.hom.hom =
      (w ≫ T.inclusion.hom.hom) ≫ A.hom.hom.hom := by
    change ((w ≫ e.hom.hom.hom) ≫ T.inclusion.hom.hom) = _
    change e.hom.hom.hom ≫ T.inclusion.hom.hom = T.inclusion.hom.hom ≫ A.hom.hom.hom at hmap
    rw [Category.assoc, hmap, ← Category.assoc]
  have hM := congrArg (spinVectorMatrix P R) heval
  change spinVectorMatrix P R (cocharacterPoint (c ≫ e.hom) R z ≫ T.inclusion.hom.hom) =
    spinVectorMatrix P R ((w ≫ T.inclusion.hom.hom) ≫ A.hom.hom.hom) at hM
  have hc (c : Cocharacter T.group) :
      spinVectorMatrix P R (cocharacterPoint c R z ≫ T.inclusion.hom.hom) =
        hyperbolicDiagonal (fun j => z ^ (v (Additive.ofMul c)).val j) :=
    diagonalCocharacter_vector P d R z c
  rw [hc, spinSchemeAction_matrix P g 1, show w = cocharacterPoint c R z from rfl,
    hc, hv] at hM
  have heq := hyperbolicDiagonal_injective R hM
  funext j
  apply laurentParameter_zpow_injective (CommAlgCat.of k k)
  have hj := congrFun heq j
  by_cases hij : j = i
  · simpa only [invertCoordinate, hij, ite_true, _root_.zpow_neg] using hj
  · simpa only [invertCoordinate, hij, ite_false] using hj

open _root_.LinearAlgebraicGroups.CocharacterDynamics
  (HasExtension HasLimit RepresentsOnAlgebras polynomialAlgebra polynomialToLaurent polynomialEvaluate
    laurentAlgebra laurentConstants laurentParameter orbit)

set_option backward.isDefEq.respectTransparency false in
private theorem hasExtension_map {G : GroupScheme k} (f : G ⟶ G) (c : Cocharacter G)
    (hc : c ≫ f = c) {R : TestAlgebra k} {a : Points G.X R}
    (ha : HasExtension c (show GroupPoints G R from a)) :
    HasExtension c (show GroupPoints G R from a ≫ f.hom.hom) := by
  let F := groupPointsFunctor k
  let v := F.map f
  have hpoint (S : TestAlgebra k) (u : Sˣ) : v.app S (cocharacterPoint c S u) = cocharacterPoint c S u := by
    change (cocharacterPoint c S u) ≫ f.hom.hom = cocharacterPoint c S u
    change cocharacterPoint (c ≫ f) S u = cocharacterPoint c S u
    rw [hc]
  have horbit : v.app (laurentAlgebra R) (orbit c (show GroupPoints G R from a)) =
      orbit c (v.app R a) := by
    change v.app (laurentAlgebra R) ((cocharacterPoint c _ (laurentParameter R)) *
      ((F.obj G).map (laurentConstants R) a) * (cocharacterPoint c _ (laurentParameter R))⁻¹) = _
    rw [map_mul, map_mul, map_inv, hpoint]
    have he := ConcreteCategory.congr_hom (v.naturality (laurentConstants R)) a
    change v.app (laurentAlgebra R) ((F.obj G).map (laurentConstants R) a) =
      (F.obj G).map (laurentConstants R) (v.app R a) at he
    rw [he]
    rfl
  obtain ⟨b, u, hu, hzero⟩ := ha
  refine ⟨v.app R b, v.app (polynomialAlgebra R) u, ?_, ?_⟩
  · have h := ConcreteCategory.congr_hom (v.naturality (polynomialToLaurent R)) u
    change mapPoints (polynomialToLaurent R) (v.app (polynomialAlgebra R) u) =
      v.app (laurentAlgebra R) (mapPoints (polynomialToLaurent R) u) at h
    exact h.trans ((congrArg (v.app (laurentAlgebra R)) hu).trans horbit)
  · have h := ConcreteCategory.congr_hom (v.naturality (polynomialEvaluate R 0)) u
    change mapPoints (polynomialEvaluate R 0) (v.app (polynomialAlgebra R) u) =
      v.app R (mapPoints (polynomialEvaluate R 0) u) at h
    exact h.trans (congrArg (v.app R) hzero)

set_option backward.isDefEq.respectTransparency false in
private theorem invariantLimitSubgroup {G : AffineAlgebraicGroup k} (B : ClosedSubgroup G.val)
    (c : Cocharacter G.val) (hB : RepresentsOnAlgebras B (fun _ x => HasExtension c x))
    (f : G.val ⟶ G.val) (hf : f ≫ f = 𝟙 _) (hc : c ≫ f = c) :
    ∃ e : B.group ≅ B.group, e.hom ≫ B.inclusion = B.inclusion ≫ f := by
  apply involution_restricts B f hf
  intro R a
  let b : Points G.val.X R := a ≫ B.inclusion.hom.hom
  have hb : HasExtension c (show GroupPoints G.val R from b) := (hB R _).mpr ⟨a, rfl⟩
  exact (hB R (b ≫ f.hom.hom)).mp (hasExtension_map f c hc hb)

omit [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)] in
private theorem invertLastHeight (n : ℕ) (hn : 0 < n) :
    invertCoordinate (ULift.up (⟨n - 1, by omega⟩ : Fin n)) (heightCoordinates.{u} n).val =
      (heightCoordinates.{u} n).val := by
  funext i
  by_cases h : i = ULift.up (⟨n - 1, by omega⟩ : Fin n)
  · subst i
    simp only [invertCoordinate, ite_true, heightCoordinates]
    omega
  · simp [invertCoordinate, h]

omit [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)] in
private theorem invertLastSimpleCoroot (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    let l : Fin n := ⟨n - 1, by omega⟩
    let p : Fin n := ⟨n - 2, by omega⟩
    invertCoordinate (ULift.up l) (simpleDCoroot.{u} n hn i) =
      simpleDCoroot n hn ((Equiv.swap p l) i) := by
  intro l p
  have hpl : p ≠ l := by
    intro h
    have he := congrArg Fin.val h
    change n - 2 = n - 1 at he
    omega
  have hnext : p.val + 1 < n := by change n - 2 + 1 < n; omega
  have heq : (⟨p.val + 1, hnext⟩ : Fin n) = l := Fin.ext (by
    change n - 2 + 1 = n - 1
    omega)
  have hlast : ¬ l.val + 1 < n := by change ¬ n - 1 + 1 < n; omega
  have hp : ULift.up (α := Fin n) p ≠ (ULift.up l : ULift.{u} (Fin n)) := fun h =>
    hpl (congrArg ULift.down h)
  have hswap := ((vectorDiagramSwitch.{u}).2 (ULift.{u} (Fin n)) (ULift.up l) (ULift.up p) (ULift.up l)).2 hp
  by_cases hi : i = p
  · subst i
    rw [Equiv.swap_apply_left, simpleDCoroot, dite_eq_left hnext, heq, simpleDCoroot, dite_eq_right hlast]
    exact hswap.1
  · by_cases hj : i = l
    · subst i
      rw [Equiv.swap_apply_right, simpleDCoroot, dite_eq_right hlast, simpleDCoroot, dite_eq_left hnext, heq]
      exact hswap.2
    · have h : i.val + 1 < n := by
        have hn' : i.val ≠ n - 1 := fun he => hj (Fin.ext he)
        omega
      let j : Fin n := ⟨i.val + 1, h⟩
      have hj' : j ≠ l := by
        intro e
        have he := congrArg Fin.val e
        change i.val + 1 = n - 1 at he
        exact hi (Fin.ext (by change i.val = n - 2; omega))
      rw [Equiv.swap_apply_of_ne_of_ne hi hj]
      change invertCoordinate (ULift.up l) (simpleDCoroot n hn i) = _
      rw [simpleDCoroot, dite_eq_left h]
      exact ((vectorDiagramSwitch.{u}).2 (ULift.{u} (Fin n)) (ULift.up l)
        (ULift.up i) (ULift.up j)).1
        (fun he => hj (congrArg ULift.down he.symm)) (fun he => hj' (congrArg ULift.down he.symm))

end

end SpinPlaneSwitch

section MarkedSpinSwitch

open Matrix AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OddSpinModels (hyperbolicForm evenSum)
open Specs.Pinning (AttachedDatum SplitBorelPair)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes

noncomputable section

set_option maxHeartbeats 800000 in
/-- The last-plane switch extends to the actual split spin scheme,
preserves the chosen Borel pair, and exchanges the two spin coroots. -/
theorem splitSpinDiagramAction : SplitSpinDiagramAction.{u} := by
  intro k _ n hn P
  dsimp only
  cases n with
  | zero => omega
  | succ m =>
    let n := m + 1
    let I := ULift.{u} (Fin n)
    let d : Fin (m + 1) ≃ I := Equiv.ulift.symm
    have hrank : 4 ≤ Fintype.card I := by simpa [I, n] using hn
    have : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
      (Fintype.equivFin (I ⊕ I)).injective
    let T := splitDiagonalTorus P d
    have hs : IsSemisimple P.spin := cliffordSpin_semisimple P d hrank
    have hred := reductive_of_semisimple P.spin hs
    have hsplit := splitDiagonalTorus_isSplit P d
    have hmax := splitDiagonalTorus_isGeometricallyMaximal P d
    obtain ⟨comm, ⟨D⟩⟩ := RootData.AbstractPairing.abstractPairing P.spin hred T hsplit hmax
    let := comm
    let v := diagonalCocharacterLattice P d
    obtain ⟨hr, hp⟩ := spin_coroot_coordinates P d hrank D
    have hspan := full_coroot_lattice P d D hr
    obtain ⟨B, hB, hBT, base, simple, hbase, hsimple, hpar⟩ :=
      standardTypeDBorel n hn P.spin hred T hsplit hmax D v hr hp
    let i : I := ULift.up (⟨n - 1, by omega⟩ : Fin n)
    obtain ⟨g, hg, hgg, hdiag⟩ := hyperbolicPlaneSwitch (k := k) i
    let A := spinSchemeAction P (matrixSimilitude g 1 (fun x => (hg x).trans (one_mul _).symm))
    have hA := spinSchemeAction_involution P g hgg hg
    obtain ⟨t, ht, htv⟩ := planeSwitch_diagonalAction P d i g hgg hg hdiag
    let c : Cocharacter T.group := (v.symm (heightCoordinates n)).toMul
    have hc : c ≫ t.hom = c := by
      apply Additive.ofMul.injective
      apply v.injective
      apply Subtype.ext
      rw [htv]
      change invertCoordinate i (v (v.symm (heightCoordinates n))).val =
        (v (v.symm (heightCoordinates n))).val
      rw [LinearEquiv.apply_symm_apply]
      exact invertLastHeight n (by omega)
    have hc' : (c ≫ T.inclusion) ≫ A.hom = c ≫ T.inclusion := by
      rw [Category.assoc, ← ht, ← Category.assoc, hc]
    obtain ⟨f, hf⟩ := invariantLimitSubgroup B (c ≫ T.inclusion) hpar A.hom hA hc'
    let Q : SplitBorelPair k := ⟨P.spin, hred, T, hsplit, hmax, B, hB, hBT⟩
    let E : AttachedDatum Q := ⟨comm, D, base, hbase⟩
    refine ⟨Q, E, Iso.refl _, A, t, f, g, simple, hspan, ?_, hg, hA, ht, hf, ?_, ?_, ?_⟩
    · intro i j
      rw [← RootPairing.root_coroot_eq_pairing]
      change D.rootDatum.toLinearMap (D.rootDatum.root (simple j).val) (D.rootDatum.coroot (simple i).val) = _
      rw [hp, hsimple j, hsimple i]
      exact (simpleDCoordinates.{u} n hn).1 i j
    · intro R a
      change (P.orthogonal.points R (a ≫ (A.hom ≫ 𝟙 _ ≫ P.projection ≫ P.inclusion).hom.hom)).val.val =
        conjugate _ (P.orthogonal.points R (a ≫ (𝟙 _ ≫ P.projection ≫ P.inclusion).hom.hom)).val.val
      rw [Category.id_comp]
      exact spinSchemeAction_matrix P g 1 _ R a
    · change P.kernel.inclusion ≫ (𝟙 P.spin.val) ≫ A.hom ≫ (𝟙 P.spin.val) = P.kernel.inclusion
      rw [Category.id_comp, Category.comp_id]
      have hcl : IsClosedImmersion P.kernel.inclusion.hom.hom.left := P.kernel.isClosedImmersion
      have ha : IsAffine P.spin.val.X.left := P.spin.property.1
      have hN : IsAffine P.kernel.group.X.left := isAffine_of_isAffineHom P.kernel.inclusion.hom.hom.left
      apply Grp.hom_ext
      apply hom_ext_of_points hN
      intro R x
      rw [Grp.comp_hom_hom]
      exact spinSchemeAction_fixesScalar P
        (matrixSimilitude g 1 (fun x => (hg x).trans (one_mul _).symm)) R x
    · intro z
      let j := (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) z
      change (D.rootDatum.coroot (simple z).val).toMul ≫ t.hom =
        (D.rootDatum.coroot (simple j).val).toMul
      apply Additive.ofMul.injective
      apply v.injective
      apply Subtype.ext
      rw [htv]
      change invertCoordinate i (v (D.rootDatum.coroot (simple z).val)).val =
        (v (D.rootDatum.coroot (simple j).val)).val
      rw [hsimple z, hsimple j]
      exact invertLastSimpleCoroot n hn z

end

end MarkedSpinSwitch

section NeutralVectorImage

open Matrix AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.GeometricRadicals (IsSemisimple)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private baseChangeMapPullback baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private fieldSpecMap_surjective from LinearAlgebraicGroups.Affine.Stabilizers

noncomputable section

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
private theorem splitImageOfVectorMorphism (G H N : AffineAlgebraicGroup k)
    {v : G.val ⟶ H.val} {p : G.val ⟶ N.val} {j : N.val ⟶ H.val}
    (hf : IsImageFactorization v p j)
    (P : SplitSpinVectorImage K I)
    (e : (groupBaseChange k K).obj G.val ≅ P.spin.val)
    (b : (groupBaseChange k K).obj H.val ≅ P.orthogonal.group.val)
    (hv : (groupBaseChange k K).map v ≫ b.hom = e.hom ≫ P.projection ≫ P.inclusion) :
    ∃ a : (groupBaseChange k K).obj N.val ≅ P.image.val,
      (groupBaseChange k K).map p ≫ a.hom = e.hom ≫ P.projection ∧
      (groupBaseChange k K).map j ≫ b.hom = a.hom ≫ P.inclusion := by
  let F := groupBaseChange k K
  let G' := baseChangedAlgebraicGroup K G
  let H' := baseChangedAlgebraicGroup K H
  let v' := F.map v
  let p' := F.map p
  let j' := F.map j
  have hcomp : p' ≫ j' = v' := by rw [← Functor.map_comp, hf.1]
  have hcomp' : (e.hom ≫ P.projection) ≫ (P.inclusion ≫ b.inv) = v' := by
    calc
      _ = (e.hom ≫ P.projection ≫ P.inclusion) ≫ b.inv := by simp only [Category.assoc]
      _ = (F.map v ≫ b.hom) ≫ b.inv := congrArg (· ≫ b.inv) hv.symm
      _ = v' := by rw [Category.assoc, b.hom_inv_id, Category.comp_id]
  have hp := baseChangeMapPullback (K := K) p.hom.hom
  have hj := baseChangeMapPullback (K := K) j.hom.hom
  have : Flat p'.hom.hom.left := MorphismProperty.of_isPullback hp.flip hf.2.1
  have : Surjective p'.hom.hom.left := MorphismProperty.of_isPullback hp.flip hf.2.2.1
  have : IsClosedImmersion j'.hom.hom.left := MorphismProperty.of_isPullback hj.flip hf.2.2.2.2.2
  have : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso e.hom
  have : IsIso b.inv.hom.hom.left :=
    (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso b.inv
  have := P.flat
  have := P.surjective
  have := P.closed
  obtain ⟨a, ha, _⟩ := schemeImageUniqueness G' H' v' p' j'
    (e.hom ≫ P.projection) (P.inclusion ≫ b.inv) hcomp hcomp'
    inferInstance inferInstance inferInstance
    (inferInstanceAs (Flat (e.hom.hom.hom.left ≫ P.projection.hom.hom.left)))
    (inferInstanceAs (Surjective (e.hom.hom.hom.left ≫ P.projection.hom.hom.left)))
    (inferInstanceAs (IsClosedImmersion (P.inclusion.hom.hom.left ≫ b.inv.hom.hom.left)))
  refine ⟨a, ha.1, ?_⟩
  change j' ≫ b.hom = a.hom ≫ P.inclusion
  rw [← ha.2, Category.assoc, Category.assoc, b.inv_hom_id, Category.comp_id]

private theorem openImmersion_of_extension {G H : GroupScheme k} (j : G ⟶ H)
    (hj : IsOpenImmersion ((groupBaseChange k K).map j).hom.hom.left) :
    IsOpenImmersion j.hom.hom.left := by
  let : Surjective (fieldSpecMap k K) := fieldSpecMap_surjective K
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (pullback.fst H.X.hom (fieldSpecMap k K)) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (baseChangeMapPullback (K := K) j.hom.hom) hq hj

private theorem imageIsIdentityComponent (G H N : AffineAlgebraicGroup k)
    (hG : GeometricallyConnected G.val.X.hom)
    (p : G.val ⟶ N.val) (hp : Surjective p.hom.hom.left)
    (j : N.val ⟶ H.val) (hc : IsClosedImmersion j.hom.hom.left) (ho : IsOpenImmersion j.hom.hom.left) :
    GeometricallyConnected N.val.X.hom ∧
      Set.range j.hom.hom.left = connectedComponent
        (η[H.val.X].left (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))))) := by
  let f := j.hom.hom
  let e := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))
  let : GeometricallyConnected G.val.X.hom := hG
  let : ConnectedSpace G.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  let : ConnectedSpace N.val.X.left := hp.1.connectedSpace p.hom.hom.left.continuous
  let : IsOpenImmersion f.left := ho
  let : IsClosedImmersion f.left := hc
  have hC : _root_.IsConnected (Set.range f.left) := by
    simpa only [Set.image_univ] using isConnected_univ.image f.left f.left.continuous.continuousOn
  have he : η[H.val.X].left e ∈ Set.range f.left := by
    refine ⟨η[N.val.X].left e, ?_⟩
    exact congrArg (fun u : (𝟙_ (SchemeOver k)) ⟶ H.val.X => u.left e) (IsMonHom.one_hom f)
  have hopen : IsClopen (Set.range f.left) :=
    ⟨f.left.isClosedEmbedding.isClosed_range, f.left.isOpenEmbedding.isOpen_range⟩
  have hr : Set.range f.left = connectedComponent (η[H.val.X].left e) :=
    (hC.subset_connectedComponent he).antisymm
      (isPreconnected_connectedComponent.subset_isClopen hopen ⟨_, mem_connectedComponent, he⟩)
  obtain ⟨_, N', _, i, hI, _⟩ := _root_.LinearAlgebraicGroups.identityComponentAndQuotient k H
  let : IsOpenImmersion i.hom.hom.left := hI.openImmersion
  let a := IsOpenImmersion.isoOfRangeEq f.left i.hom.hom.left (hr.trans hI.identityComponent.symm)
  have ha : a.hom ≫ N'.X.hom = N.val.X.hom := by
    rw [← Over.w i.hom.hom, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Over.w f]
  refine ⟨?_, hr⟩
  have hpb : IsPullback a.hom N.val.X.hom N'.X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using ha⟩
  exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb hI.geometricallyConnected

/-- The scheme image of a descended vector morphism is the neutral subgroup.
The full image factorization compares to the actual split Clifford covering. -/
theorem descendedVectorImage : DescendedVectorImage.{u} := by
  intro k K I _ _ _ _ _ hRank G H hG v P e b hv
  obtain ⟨N, p, j, hf, _, _⟩ := schemeImageFactorization G H v
  obtain ⟨a, hp, hj⟩ := splitImageOfVectorMorphism G H N hf P e b hv
  have hIncl := congrArg (fun f => f.hom.hom.left) hj
  have : IsIso b.hom.hom.hom.left := (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso b.hom
  have : IsIso a.hom.hom.hom.left := (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso a.hom
  have hoj : IsOpenImmersion j.hom.hom.left := by
    apply openImmersion_of_extension (K := K)
    apply (MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ b.hom.hom.hom.left).mp
    change ((groupBaseChange k K).map j).hom.hom.left ≫ b.hom.hom.hom.left =
      a.hom.hom.hom.left ≫ P.inclusion.hom.hom.left at hIncl
    rw [hIncl]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion _ _).mpr
      (splitSpinOpenImage K I hRank P)
  obtain ⟨hN, hrange⟩ := imageIsIdentityComponent G H N hG p hf.2.2.1 j hf.2.2.2.2.2 hoj
  exact ⟨N, p, j, a, hf, hoj, hN, hrange, hp, hj⟩

end

end NeutralVectorImage


section AffineMorphismDescent

open Matrix AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open private extendedTest extendedBase extendMap includeTest galoisTest pointsInclusion_fixed
  includeTest_galois includeTest_natural multiplyTest multiplyTest_include
  from LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [fin : FiniteDimensional k K] [gal : IsGalois k K]

include fin gal in
set_option backward.isDefEq.respectTransparency false in
private theorem descendGroupHomOnAlgebras (G H : AffineAlgebraicGroup k)
    (τ : restrictTestAlgebra k K ⋙ (groupPointsFunctor k).obj G.val ⟶
      restrictTestAlgebra k K ⋙ (groupPointsFunctor k).obj H.val)
    (hτ : ∀ (R : TestAlgebra k) (σ : Gal(K/k)) (a : Points G.val.X (extendedBase (K := K) R)),
      τ.app (extendedTest R) (mapPoints (galoisTest R σ) a) =
        mapPoints (galoisTest R σ) (τ.app (extendedTest R) a)) :
    ∃ f : G.val ⟶ H.val,
      Functor.whiskerLeft (restrictTestAlgebra k K) ((groupPointsFunctor k).map f) = τ := by
  let F := (groupPointsFunctor k).obj G.val
  let G' := (groupPointsFunctor k).obj H.val
  let i (R : TestAlgebra k) := includeTest (K := K) R
  have lift (R : TestAlgebra k) (a : F.obj R) :
      ∃ b : G'.obj R, G'.map (i R) b = τ.app (extendedTest R) (F.map (i R) a) := by
    apply ((pointsInclusion_fixed (K := K) H R).2 _).2
    intro σ
    exact (hτ R σ _).symm.trans (congrArg (τ.app (extendedTest R))
      (((pointsInclusion_fixed (K := K) G R).2 _).1 ⟨a, rfl⟩ σ))
  let d (R : TestAlgebra k) : F.obj R →* G'.obj R :=
    { toFun := fun a => (lift R a).choose
      map_one' := (pointsInclusion_fixed (K := K) H R).1 (by
        rw [(lift R 1).choose_spec]
        simp
        exact (τ.app (extendedTest R)).hom.map_one)
      map_mul' := fun a b => (pointsInclusion_fixed (K := K) H R).1 (by
        rw [(lift R (a * b)).choose_spec, map_mul, map_mul, map_mul,
          (lift R a).choose_spec, (lift R b).choose_spec]) }
  have hd (R : TestAlgebra k) (a : F.obj R) :
      G'.map (i R) (d R a) = τ.app (extendedTest R) (F.map (i R) a) :=
    (lift R a).choose_spec
  let δ : F ⟶ G' :=
    { app := fun R => GrpCat.ofHom (d R)
      naturality := by
        intro R S u
        apply GrpCat.ext
        intro a
        apply (pointsInclusion_fixed (K := K) H S).1
        let v := (restrictTestAlgebra k K).map (extendMap (K := K) u)
        have hF (x : F.obj R) : F.map (i S) (F.map u x) = F.map v (F.map (i R) x) :=
          ConcreteCategory.congr_hom
            (((F.map_comp u _).symm.trans (congrArg F.map (includeTest_natural (K := K) u))).trans
              (F.map_comp _ _)) x
        have hH (x : G'.obj R) : G'.map (i S) (G'.map u x) = G'.map v (G'.map (i R) x) :=
          ConcreteCategory.congr_hom
            (((G'.map_comp u _).symm.trans (congrArg G'.map (includeTest_natural (K := K) u))).trans
              (G'.map_comp _ _)) x
        change G'.map (i S) (d S (F.map u a)) = G'.map (i S) (G'.map u (d R a))
        rw [hd, hF, hH, hd]
        exact ConcreteCategory.congr_hom (τ.naturality (extendMap (K := K) u)) _ }
  let E := AffineAlgebraicGroup.groupHomEquiv G H
  refine ⟨E.symm δ, ?_⟩
  change Functor.whiskerLeft (restrictTestAlgebra k K) (E (E.symm δ)) = τ
  rw [E.apply_symm_apply]
  apply NatTrans.ext
  funext S
  apply GrpCat.ext
  intro x
  let R := (restrictTestAlgebra k K).obj S
  let m := (restrictTestAlgebra k K).map (multiplyTest (k := k) (K := K) S)
  have hF (y : F.obj R) : F.map m (F.map (i R) y) = y :=
    ConcreteCategory.congr_hom ((F.map_comp _ _).symm.trans
      ((congrArg F.map (multiplyTest_include S)).trans (F.map_id R))) y
  have hH (y : G'.obj R) : G'.map m (G'.map (i R) y) = y :=
    ConcreteCategory.congr_hom ((G'.map_comp _ _).symm.trans
      ((congrArg G'.map (multiplyTest_include S)).trans (G'.map_id R))) y
  change d R x = τ.app S x
  calc
    _ = G'.map m (G'.map (i R) (d R x)) := (hH _).symm
    _ = G'.map m (τ.app (extendedTest R) (F.map (i R) x)) := congrArg (G'.map m) (hd R x)
    _ = τ.app S (F.map m (F.map (i R) x)) :=
      (ConcreteCategory.congr_hom (τ.naturality (multiplyTest (k := k) (K := K) S)) _).symm
    _ = _ := congrArg (τ.app S) (hF x)

end

end AffineMorphismDescent


section SplitPairEquivariance

open Matrix AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open SymplecticIsometryDescent (tensorMap)

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}

set_option backward.isDefEq.respectTransparency false in
private theorem splitPairAt_semilinear (D : DescendedQuadraticPair ρ)
    (σ : Gal(K/k)) (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ)
    (hρ : ∀ X, ρ.act σ X = conjugate g (X.map σ))
    {R S : TestAlgebra k} [Algebra K R] [Algebra K S] [IsScalarTower k K R] [IsScalarTower k K S]
    (f : R ⟶ S) (hf : ∀ b, f.hom (algebraMap K R b) = algebraMap K S (σ b))
    (x : R ⊗[k] ρ.fixedSubalgebra) :
    splitPairAt D S (tensorMap f x) =
      conjugate (Matrix.GeneralLinearGroup.map (algebraMap K S) g) ((splitPairAt D R x).map f.hom) := by
  let g' := Matrix.GeneralLinearGroup.map (algebraMap K S) g
  induction x with
  | tmul r x =>
    have hX : (x.val.map (algebraMap K R)).map f.hom = (x.val.map σ).map (algebraMap K S) :=
      Matrix.ext fun i j => hf (x.val i j)
    have hY : conjugate g' ((x.val.map σ).map (algebraMap K S)) = x.val.map (algebraMap K S) := by
      have h := (hρ x.val).symm.trans (x.property σ)
      change g.val * x.val.map σ * g.inv = x.val at h
      have hm := congrArg (fun Y : Matrix (I ⊕ I) (I ⊕ I) K => Y.map (algebraMap K S)) h
      simp only [Matrix.map_mul] at hm
      exact hm
    change splitPairAt D S (f.hom r ⊗ₜ[k] x) = _
    rw [splitPairAt_tmul, splitPairAt_tmul]
    have hScale : (r • x.val.map (algebraMap K R)).map f.hom =
        f.hom r • (x.val.map (algebraMap K R)).map f.hom := by
      ext i j
      simp [smul_eq_mul]
    rw [hScale, hX, conjugate, Matrix.mul_smul, Matrix.smul_mul, ← show
        conjugate g' ((x.val.map σ).map (algebraMap K S)) =
          g'.val * (x.val.map σ).map (algebraMap K S) * g'.inv from rfl, hY]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    rw [Matrix.map_add f.hom (map_add f.hom)]
    simp only [conjugate, mul_add, add_mul]

end SplitPairEquivariance


section VectorMorphismDescent

open Matrix AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Unipotent (baseChangedAlgebraicGroup)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open SymplecticIsometryDescent (tensorMap)
open private groupBaseChangePointIso from LinearAlgebraicGroups.Affine.RationalRepresentations
open private baseChangePoint_map from LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open private extendedTest extendedBase galoisTest galoisTest_semilinear
  from LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent

noncomputable section

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)}

private abbrev splitVectorValue (G : AffineAlgebraicGroup k) (P : SplitSpinVectorImage K I)
    (e : (groupBaseChange k K).obj G.val ≅ P.spin.val) (S : TestAlgebra K)
    (x : Points G.val.X ((restrictTestAlgebra k K).obj S)) :=
  (P.orthogonal.points S (((baseChangePointGroupEquiv K G.val S).symm x) ≫
    (e.hom ≫ P.projection ≫ P.inclusion).hom.hom)).val.val

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
private theorem vectorMorphism_of_equivariance [FiniteDimensional k K] [IsGalois k K]
    (D : DescendedQuadraticPair ρ)
    (G H : AffineAlgebraicGroup k) (P : SplitSpinVectorImage K I)
    (e : (groupBaseChange k K).obj G.val ≅ P.spin.val)
    (b : (groupBaseChange k K).obj H.val ≅ P.orthogonal.group.val)
    (m : ∀ R : TestAlgebra k, Points H.val.X R →* (R ⊗[k] ρ.fixedSubalgebra)ˣ)
    (hNat : ∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : Points H.val.X R),
      m S (mapPoints f a) = Units.map (tensorMap f).toMonoidHom (m R a))
    (hInj : ∀ R, Function.Injective (m R))
    (hM : ∀ (S : TestAlgebra K),
      let R := (restrictTestAlgebra k K).obj S
      ∃ E : (R ⊗[k] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S,
        (∀ (s : S) (x : ρ.fixedSubalgebra), E (s ⊗ₜ[k] x) = s • x.val.map (algebraMap K S)) ∧
        ∀ x : Points ((groupBaseChange k K).obj H.val).X S,
          E (m R (baseChangePoint k K H.val.X S x)).val =
            (P.orthogonal.points S (x ≫ b.hom.hom.hom)).val.val)
    (g : Gal(K/k) → (Matrix (I ⊕ I) (I ⊕ I) K)ˣ)
    (hg : ∀ σ X, ρ.act σ X = conjugate (g σ) (X.map σ))
    (hEq : ∀ (R : TestAlgebra k) (σ : Gal(K/k)) (x : Points G.val.X (extendedBase (K := K) R)),
      let S := extendedTest (K := K) R
      let f := galoisTest R σ
      splitVectorValue G P e S (mapPoints f x) =
        conjugate (Matrix.GeneralLinearGroup.map (algebraMap K S) (g σ))
          ((splitVectorValue G P e S x).map f.hom)) :
    ∃ v : G.val ⟶ H.val,
      (groupBaseChange k K).map v ≫ b.hom = e.hom ≫ P.projection ≫ P.inclusion := by
  let F := groupBaseChange k K
  let w := e.hom ≫ P.projection ≫ P.inclusion ≫ b.inv
  let cG := groupBaseChangePointIso K G.val
  let cH := groupBaseChangePointIso K H.val
  let t := cG.inv ≫ (groupPointsFunctor K).map w ≫ cH.hom
  have ht (S : TestAlgebra K) :
      let R := (restrictTestAlgebra k K).obj S
      letI : Algebra k S := R.algebra
      letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
      ∀ x : Points G.val.X R, splitPairAt D S (m R (t.app S x)).val = splitVectorValue G P e S x := by
    intro R x
    let : Algebra k S := R.algebra
    let : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
    obtain ⟨E, he, he'⟩ := hM S
    have hE : E = splitPairAt D S := by
      apply AlgEquiv.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul s a => exact (he s a).trans (splitPairAt_tmul D s a).symm
      | add x y hx hy => simp only [map_add, hx, hy]
    let y := (baseChangePointGroupEquiv K G.val S).symm x
    have hz := he' (y ≫ w.hom.hom)
    rw [hE] at hz
    refine hz.trans ?_
    change (P.orthogonal.points S (((y ≫ w.hom.hom) ≫ b.hom.hom.hom))).val.val = _
    have hw : w ≫ b.hom = e.hom ≫ P.projection ≫ P.inclusion := by
      simp only [w, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Category.assoc, show w.hom.hom ≫ b.hom.hom.hom =
      (e.hom ≫ P.projection ≫ P.inclusion).hom.hom from congrArg (fun z => z.hom.hom) hw]
  have equivariance (R : TestAlgebra k) (σ : Gal(K/k)) (x : Points G.val.X (extendedBase (K := K) R)) :
      t.app (extendedTest R) (mapPoints (galoisTest R σ) x) =
        mapPoints (galoisTest R σ) (t.app (extendedTest R) x) := by
    let S := extendedTest (K := K) R
    let U := extendedBase (K := K) R
    let f := galoisTest R σ
    let : Algebra K U := S.algebra
    let : IsScalarTower k K U := IsScalarTower.of_algebraMap_eq' rfl
    change t.app S (mapPoints f x) = mapPoints f (t.app S x)
    apply hInj U
    apply Units.ext
    apply (splitPairAt D U).injective
    rw [hNat U U f (t.app S x)]
    change splitPairAt D U (m U (t.app S (mapPoints f x))).val =
      splitPairAt D U (tensorMap f (m U (t.app S x)).val)
    rw [splitPairAt_semilinear D σ (g σ) (hg σ) f (galoisTest_semilinear R σ)]
    have h1 := ht S (mapPoints f x)
    have h2 := ht S x
    change splitPairAt D U (m U (t.app S (mapPoints f x))).val =
      splitVectorValue G P e S (mapPoints f x) at h1
    change splitPairAt D U (m U (t.app S x)).val = splitVectorValue G P e S x at h2
    rw [h1, h2]
    exact hEq R σ x
  obtain ⟨v, hv⟩ := descendGroupHomOnAlgebras G H t equivariance
  have hvw : F.map v = w := by
    let G' := baseChangedAlgebraicGroup K G
    let H' := baseChangedAlgebraicGroup K H
    apply (AffineAlgebraicGroup.groupHomEquiv G' H').injective
    apply NatTrans.ext
    funext S
    apply GrpCat.ext
    intro x
    apply (baseChangePointGroupEquiv K H.val S).injective
    change baseChangePoint k K H.val.X S (x ≫ (F.map v).hom.hom) =
      baseChangePoint k K H.val.X S (x ≫ w.hom.hom)
    rw [show baseChangePoint k K H.val.X S (x ≫ (F.map v).hom.hom) =
      baseChangePoint k K G.val.X S x ≫ v.hom.hom from baseChangePoint_map K v S x]
    have he := congrArg (fun d => d.app S (baseChangePoint k K G.val.X S x)) hv
    change baseChangePoint k K G.val.X S x ≫ v.hom.hom =
      baseChangePoint k K H.val.X S
        (((baseChangePointGroupEquiv K G.val S).symm (baseChangePoint k K G.val.X S x)) ≫ w.hom.hom)
      at he
    rw [show ((baseChangePointGroupEquiv K G.val S).symm (baseChangePoint k K G.val.X S x)) = x from
      (baseChangePointGroupEquiv K G.val S).symm_apply_apply x] at he
    exact he
  refine ⟨v, ?_⟩
  change F.map v ≫ b.hom = _
  rw [hvw]
  simp only [w, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A semilinear matrix comparison over the splitting field descends the
actual vector representation of the Clifford cover. -/
theorem vectorMorphismDescent : VectorMorphismDescent.{u} := by
  intro k K I _ _ _ _ _ _ _ ρ D G H P e b m hNat hInj hM g hg hEq
  apply vectorMorphism_of_equivariance D G H P e b m hNat hInj hM g hg
  intro R σ x S f
  let U := (restrictTestAlgebra k K).obj S
  let y := (baseChangePointGroupEquiv K G.val S).symm x
  let z := (baseChangePointGroupEquiv K G.val S).symm (mapPoints f x)
  have hy : baseChangePoint k K G.val.X S y = x :=
    (baseChangePointGroupEquiv K G.val S).apply_symm_apply _
  have hz : baseChangePoint k K G.val.X S z = mapPoints f x :=
    (baseChangePointGroupEquiv K G.val S).apply_symm_apply _
  exact hEq S σ f (galoisTest_semilinear R σ) y z (by rw [hy, hz]; rfl)

end

end VectorMorphismDescent


section NeutralIsometryEquations

open Matrix AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open SymplecticIsometryDescent (tensorMap tensorMap_involution)
open private extendedTest extendedBase includeTest includeTest_fixed
  from LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
open private baseChangePoint_map from LinearAlgebraicGroups.Relative.ReductiveLieCentralizers

noncomputable section

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]

private theorem unitaryHyperbolic_isometry {R : Type u} [CommRing R]
    (h₂ : IsUnit (2 : R)) (g : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ)
    (hg : adjoint (hyperbolicGram I R) g.val * g.val = 1) :
    g ∈ orthogonalMatrices I R := by
  let J := hyperbolicGram I R
  let L := hyperbolicProjection I R
  let Q := J * L
  have hJ : J * J = 1 := hyperbolicGram_square I R
  have hX := congrArg (J * ·) hg
  change J * ((J * g.val.transpose * J) * g.val) = J * 1 at hX
  simp only [← mul_assoc, hJ, one_mul, mul_one] at hX
  have hGram : g.val.transpose * J * g.val = J := hX
  have hq (x : I ⊕ I → R) : diagonalValue J x = (2 : R) * hyperbolicForm I R x := by
    have hp : Q + Q.transpose = J := hyperbolicProjection_polar I R
    rw [← hp]
    have ht : diagonalValue Q.transpose x = diagonalValue Q x := by
      unfold diagonalValue
      rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
    change (x ⬝ᵥ ((Q + Q.transpose) *ᵥ x)) = _
    rw [add_mulVec, dotProduct_add]
    change diagonalValue Q x + diagonalValue Q.transpose x = _
    rw [ht, (splitSemitrace_over_ring I R).2.1 x, two_mul]
  intro x
  apply h₂.mul_left_cancel
  rw [← hq, ← hq, ← diagonalValue_congr, hGram]

variable {ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K)} (D : DescendedQuadraticPair ρ)

private theorem pairReducedNorm_natural {R S : TestAlgebra k} (f : R ⟶ S)
    {d : ℕ} (b : Module.Basis (Fin d) k ρ.fixedSubalgebra) (x : R ⊗[k] ρ.fixedSubalgebra) :
    f.hom (MvPolynomial.eval₂ (algebraMap k R) (fun i => (b.baseChange R).repr x i)
      (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b)) =
      MvPolynomial.eval₂ (algebraMap k S) (fun i => (b.baseChange S).repr (tensorMap f x) i)
        (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b) := by
  change f.hom.toRingHom (MvPolynomial.eval₂ (algebraMap k R) (fun i => (b.baseChange R).repr x i)
    (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b)) = _
  rw [MvPolynomial.eval₂_comp_left f.hom.toRingHom]
  have he : f.hom.toRingHom.comp (algebraMap k R) = algebraMap k S :=
    RingHom.ext f.hom.commutes
  rw [he]
  congr 1
  funext i
  exact (pairBasis_repr_natural b f x i).symm

variable [Nonempty I]

omit [Nonempty I] in
private theorem pairUnitary_of_split {R : TestAlgebra k} [Algebra K R] [IsScalarTower k K R]
    (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ)
    (E : (R ⊗[k] ρ.fixedSubalgebra) ≃ₐ[R] Matrix (I ⊕ I) (I ⊕ I) R)
    (he : ∀ (r : R) (x : ρ.fixedSubalgebra), E (r ⊗ₜ[k] x) = r • x.val.map (algebraMap K R)) :
    (D.involution.baseChange R).toLinearMap g.val * g.val = 1 ↔
      adjoint (hyperbolicGram I R) (E g.val) * E g.val = 1 := by
  have hE : E = splitPairAt D R := by
    apply AlgEquiv.ext
    intro x
    induction x with
    | tmul r x =>
      rw [he, splitPairAt_tmul]
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
  rw [hE, ← (splitPairAt D R).injective.eq_iff]
  rw [map_mul, splitPairAt_involution, map_one]


private theorem unitaryAndNorm_overSplittingField (h₂ : (2 : k) ≠ 0) (S : TestAlgebra K) :
    let R := (restrictTestAlgebra k K).obj S
    ∀ (E : (R ⊗[k] ρ.fixedSubalgebra) ≃ₐ[S] Matrix (I ⊕ I) (I ⊕ I) S),
      (∀ (s : S) (x : ρ.fixedSubalgebra), E (s ⊗ₜ[k] x) = s • x.val.map (algebraMap K S)) →
      ∀ {d : ℕ} (b : Module.Basis (Fin d) k ρ.fixedSubalgebra) (z : (R ⊗[k] ρ.fixedSubalgebra)ˣ),
      ((D.involution.baseChange R).toLinearMap z.val * z.val = 1 → IsPairIsometry D R z) ∧
      MvPolynomial.eval₂ (algebraMap k R) (fun i => (b.baseChange R).repr z.val i)
        (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple b) = (E z.val).det := by
  intro R E hE d b z
  let : Algebra k S := R.algebra
  let : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra K R := S.algebra
  let : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq' (by
    change algebraMap k S = (algebraMap K S).comp (algebraMap k K)
    rfl)
  refine ⟨fun hu => ?_, pairReducedNormScalarExtension D S E hE d b z.val⟩
  have h₂S : IsUnit (2 : R) := by
    have h := (isUnit_iff_ne_zero.mpr h₂).map (algebraMap k R)
    rwa [map_ofNat] at h
  have hEz : Units.map E.toMonoidHom z ∈ orthogonalMatrices I R :=
    unitaryHyperbolic_isometry h₂S _ ((pairUnitary_of_split D z E hE).mp hu)
  have hES : E = splitPairAt D S := by
    apply AlgEquiv.ext
    intro x
    induction x with
    | tmul s x => exact (hE s x).trans (splitPairAt_tmul D s x).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  exact (splitPairAt_isometry D R z).mpr (hES ▸ hEz)

omit [Nonempty I] in
private theorem unitaryEquation_map {R S : TestAlgebra k} (f : R ⟶ S)
    (g : (R ⊗[k] ρ.fixedSubalgebra)ˣ)
    (hg : (D.involution.baseChange R).toLinearMap g.val * g.val = 1) :
    (D.involution.baseChange S).toLinearMap (tensorMap f g.val) * tensorMap f g.val = 1 := by
  rw [← tensorMap_involution, ← map_mul, hg, map_one]

section NeutralReducedNorm

variable [FiniteDimensional k K] [IsGalois k K]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Compare the ground-field neutral isometry equations with reduced norm one. -/
theorem neutralPointsReducedNorm : NeutralPointsReducedNorm.{u} := by
  intro k K I _ _ _ _ _ _ _ _ ρ D hRank h₂ H N j hj m hNat hRange P b a hIncl hM
  let : FiniteDimensional k ρ.fixedSubalgebra := D.centralSimple.2.2
  let s := Module.finBasis k ρ.fixedSubalgebra
  refine ⟨_, s, fun R g => ?_⟩
  let F := groupBaseChange k K
  let S := extendedTest (K := K) R
  let U := (restrictTestAlgebra k K).obj S
  let f : R ⟶ U := includeTest (K := K) R
  have hf := (includeTest_fixed (K := K) R).1
  have h₂K : (2 : K) ≠ 0 := by
    intro h
    apply h₂
    apply (algebraMap k K).injective
    rw [map_ofNat, map_zero]
    exact h
  obtain ⟨E, hE, hEM⟩ := hM S
  let z := Units.map (tensorMap f).toMonoidHom g
  let norm (T : TestAlgebra k) (x : T ⊗[k] ρ.fixedSubalgebra) :=
    MvPolynomial.eval₂ (algebraMap k T) (fun i => (s.baseChange T).repr x i)
      (_root_.Specs.RM03.CSA.genericReducedNorm D.centralSimple s)
  have hs := unitaryAndNorm_overSplittingField D h₂ S E hE s z
  have hNorm : f.hom (norm R g.val) = (E z.val).det :=
    (pairReducedNorm_natural D f s g.val).trans hs.2
  have hc {X Y : GroupScheme k} (p : X ⟶ Y) (x : Points (F.obj X).X S) :
      baseChangePoint k K Y.X S (x ≫ (F.map p).hom.hom) =
        baseChangePoint k K X.X S x ≫ p.hom.hom := baseChangePoint_map K p S x
  have hji : (F.map j).hom.hom ≫ b.hom.hom.hom = a.hom.hom.hom ≫ P.inclusion.hom.hom :=
    congrArg (fun u => u.hom.hom) hIncl
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨((hRange R g).mp ⟨x ≫ j.hom.hom, hx⟩).1, ?_⟩
    let y := (baseChangePointGroupEquiv K N.val S).symm (mapPoints f x)
    have hy : baseChangePoint k K N.val.X S y = mapPoints f x :=
      (baseChangePointGroupEquiv K N.val S).apply_symm_apply _
    have hmul : m U (baseChangePoint k K H.val.X S (y ≫ (F.map j).hom.hom)) = z := by
      rw [hc, hy]
      exact (hNat R U f (x ≫ j.hom.hom)).trans (by rw [hx])
    have hm : E z.val = (P.orthogonal.points S (((y ≫ (F.map j).hom.hom) ≫ b.hom.hom.hom))).val.val :=
      (congrArg (fun u => E u.val) hmul).symm.trans (hEM _)
    have hdet : (E z.val).det = 1 := by
      rw [hm, Category.assoc, hji]
      exact (splitSpinDeterminant K I hRank h₂K P S _).mpr
        ⟨y ≫ a.hom.hom.hom, Category.assoc _ _ _⟩
    exact hf (hNorm.trans (hdet.trans (map_one f.hom).symm))
  · rintro ⟨hu, hnorm⟩
    have huz := unitaryEquation_map D f g hu
    have hG : IsPairIsometry D R g := pairIsometry_of_map D f hf g (hs.1 huz)
    obtain ⟨x, hx⟩ := (hRange R g).mpr hG
    let y := (baseChangePointGroupEquiv K H.val S).symm (mapPoints f x)
    have hy : baseChangePoint k K H.val.X S y = mapPoints f x :=
      (baseChangePointGroupEquiv K H.val S).apply_symm_apply _
    have hmul : m U (baseChangePoint k K H.val.X S y) = z := by
      rw [hy, hNat, hx]
    have hm : E z.val = (P.orthogonal.points S (y ≫ b.hom.hom.hom)).val.val :=
      (congrArg (fun u => E u.val) hmul).symm.trans (hEM y)
    have hdet : (P.orthogonal.points S (y ≫ b.hom.hom.hom)).val.val.det = 1 := by
      rw [← hm, ← hNorm]
      exact (congrArg f.hom hnorm).trans (map_one f.hom)
    obtain ⟨v, hv⟩ := (splitSpinDeterminant K I hRank h₂K P S _).mp hdet
    let y' : Points (F.obj N.val).X S := v ≫ a.inv.hom.hom
    let x' := baseChangePoint k K N.val.X S y'
    have hxy : mapPoints f x = x' ≫ j.hom.hom := by
      rw [← hy, ← hc]
      congr 1
      have hB : Mono b.hom.hom.hom := inferInstanceAs (Mono ((Grp.forget (SchemeOver K)).map b.hom))
      apply (cancel_mono b.hom.hom.hom).mp
      change y ≫ b.hom.hom.hom = (y' ≫ (F.map j).hom.hom) ≫ b.hom.hom.hom
      rw [Category.assoc, hji, show y' = v ≫ a.inv.hom.hom from rfl, Category.assoc,
        ← Category.assoc a.inv.hom.hom, show a.inv.hom.hom ≫ a.hom.hom.hom = 𝟙 _ from
          congrArg (Grp.forget (SchemeOver K)).map a.inv_hom_id, Category.id_comp]
      exact hv.symm
    obtain ⟨w, hw⟩ := factorsClosed_of_injective_testMap f hf j.hom.hom hj x x' hxy
    exact ⟨w, (congrArg (m R) hw).trans hx⟩

end NeutralReducedNorm

end

end NeutralIsometryEquations



section VectorVertexFactorization

open Matrix AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Pinning (AttachedDatum PinnedGroup)
open Specs.AutomorphismSequence (Aligned AdjointQuotient SplitSequence RelativeAut relativePoints
  scalarAut constantGroup restrictAut)
open Specs.RootGroups (AdditiveLine)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.RelativeFormComparison (fieldTest)
open Specs.QuasiSplitInnerForms (outerHom constantEvaluation)
open private restrict_ground from LinearAlgebraicGroups.Descent.RelativeFormComparison

noncomputable section

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

set_option backward.isDefEq.respectTransparency false in
private theorem outerAction_on_coroots {L : AdditiveLine k} {P : PinnedGroup L}
    (D : AttachedDatum P.pair) {l : Aut D.toBased ≃* Aut P}
    {Q : AdjointQuotient P.pair.G} (E : SplitSequence P D l Q)
    (a : P.pair.G.val ≅ P.pair.G.val) (t : P.pair.T.group ≅ P.pair.T.group)
    (b : P.pair.B.group ≅ P.pair.B.group)
    (ht : t.hom ≫ P.pair.T.inclusion = P.pair.T.inclusion ≫ a.hom)
    (hb : b.hom ≫ P.pair.B.inclusion = P.pair.B.inclusion ≫ a.hom) :
    letI := D.comm
    let d := outerHom (S := S) E (scalarAut (Aut.of a) (fieldTest k S))
    ∀ α : D.toBased.I, (D.toBased.datum.coroot α).toMul ≫ t.hom =
      (D.toBased.datum.coroot (d.asIso.hom.val.indexEquiv α)).toMul := by
  let := D.comm
  let U : SchemeOver k := 𝟙_ (SchemeOver k)
  let f := scalarAut (Aut.of a) U
  let p : Aligned P f :=
    { torus := scalarAut (Aut.of t) U
      borel := scalarAut (Aut.of b) U
      torus_comm := by
        ext V x
        change (x ≫ P.pair.T.inclusion.hom.hom) ≫ a.hom.hom.hom =
          (x ≫ t.hom.hom.hom) ≫ P.pair.T.inclusion.hom.hom
        simp only [Category.assoc]
        exact congrArg (x ≫ ·) (congrArg (fun u => u.hom.hom) ht.symm)
      borel_comm := by
        ext V x
        change (x ≫ P.pair.B.inclusion.hom.hom) ≫ a.hom.hom.hom =
          (x ≫ b.hom.hom.hom) ≫ P.pair.B.inclusion.hom.hom
        simp only [Category.assoc]
        exact congrArg (x ≫ ·) (congrArg (fun u => u.hom.hom) hb.symm) }
  let z := E.toExactSequence.outer.app (op U) f
  let d : Aut D.toBased := z.down (IsLocalRing.closedPoint k)
  have hz : z = ⟨LocallyConstant.const _ d⟩ := by
    apply ULift.ext
    apply LocallyConstant.ext
    intro x
    change z.down x = d
    change PrimeSpectrum k at x
    exact congrArg z.down (Subsingleton.elim x (IsLocalRing.closedPoint k))
  have hlat := E.latticeAction U f p d hz
  have hc (c : Cocharacter P.pair.T.group) :
      c ≫ t.inv = (d.asIso.hom.val.coweightEquiv (Additive.ofMul c)).toMul := by
    let M := (specGroup (groupAlgebra k IntegerCharacters)).X
    let V : Over U := Over.mk (toUnit M)
    have h := hlat.2 c V (𝟙 M)
    apply Grp.hom_ext
    change c.hom.hom ≫ t.inv.hom.hom = _
    change (𝟙 M ≫ c.hom.hom) ≫ t.inv.hom.hom =
      𝟙 M ≫ (d.asIso.hom.val.coweightEquiv (Additive.ofMul c)).toMul.hom.hom at h
    simpa only [Category.id_comp] using h
  have hd (α : D.toBased.I) :
      (D.toBased.datum.coroot α).toMul ≫ t.hom =
        (D.toBased.datum.coroot (d.asIso.hom.val.indexEquiv α)).toMul := by
    let β := d.asIso.hom.val.indexEquiv α
    have hr := d.asIso.hom.val.toHom.coroot_coweightMap_apply D.toBased.datum D.toBased.datum β
    change d.asIso.hom.val.coweightEquiv (D.toBased.datum.coroot β) =
      D.toBased.datum.coroot (d.asIso.hom.val.indexEquiv.symm β) at hr
    rw [Equiv.symm_apply_apply] at hr
    have h := hc (D.toBased.datum.coroot β).toMul
    rw [show Additive.ofMul (D.toBased.datum.coroot β).toMul = D.toBased.datum.coroot β from rfl, hr] at h
    rw [← h, Category.assoc, t.inv_hom_id, Category.comp_id]
  let r : fieldTest k S ⟶ U := toUnit _
  have hn := ConcreteCategory.congr_hom (E.toExactSequence.outer.naturality r.op) f
  change E.toExactSequence.outer.app (op (fieldTest k S)) (restrictAut r f) =
    (constantGroup (k := k) (Aut D.toBased)).map r.op z at hn
  have hres : restrictAut r f = scalarAut (Aut.of a) (fieldTest k S) := by
    apply Aut.ext
    apply Iso.ext
    ext X x
    rfl
  rw [hres, hz] at hn
  have hOut : outerHom (S := S) E (scalarAut (Aut.of a) (fieldTest k S)) = d :=
    congrArg (constantEvaluation k S (Aut D.toBased)) hn
  dsimp only
  intro α
  rw [hOut]
  exact hd α

end

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Pinning (AttachedDatum PinnedGroup PinnedIso BasedIso)
open Specs.AbsoluteDynkinTypes (PreservesCartan)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence RelativeAut groupSections scalarAut)
open Specs.RootGroups (AdditiveLine)
open Specs.CharacterDescent (Cocharacter)
open Specs.RelativeFormComparison (fieldTest)
open Specs.QuasiSplitInnerForms (outerHom)
open _root_.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms (splitKernel)
open _root_.LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open private simple_vertices based_iso_preserves_cartan from LinearAlgebraicGroups.Arithmetic.OddSpinModels
open private coroot_transport coweightEquiv rootEquiv from LinearAlgebraicGroups.Classification.Pinning

noncomputable section

private theorem basedAut_eq_of_simple {D : Specs.Pinning.BasedRootDatum.{u}}
    (hD : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) (f g : Aut D)
    (h : simple_vertices f.asIso.hom = simple_vertices g.asIso.hom) : f = g := by
  let s := simple_vertices f.asIso.hom
  have hs : PreservesCartan (RootData.integralCartan D.datum D.base)
      (RootData.integralCartan D.datum D.base) s := based_iso_preserves_cartan f.asIso.hom
  obtain ⟨_, _, hu⟩ := (RootData.AbsoluteDynkinTypes.cartanDeterminesBasedDatum D D hD hD s).mp hs
  have hf := hu f.asIso.hom (fun _ => rfl)
  have hg := hu g.asIso.hom (fun i => congrArg (fun e => (e i).val) h.symm)
  exact Aut.ext (Iso.ext (hf.trans hg.symm))

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

private def vertexPerm {D : Specs.Pinning.BasedRootDatum.{u}} {n : ℕ}
    (s : Fin n ≃ ↥D.base.support) (f : Aut D) : Equiv.Perm (Fin n) :=
  (s.trans (simple_vertices f.asIso.hom)).trans s.symm

private theorem vertexPerm_index {D : Specs.Pinning.BasedRootDatum.{u}} {n : ℕ}
    (s : Fin n ≃ ↥D.base.support) (f : Aut D) (i : Fin n) :
    (s (vertexPerm s f i)).val = f.asIso.hom.val.indexEquiv (s i).val := by
  simp only [vertexPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

private theorem vertexPerm_preservesCartan {D : Specs.Pinning.BasedRootDatum.{u}} {n : ℕ}
    (s : Fin n ≃ ↥D.base.support)
    (h : ∀ i j, D.datum.pairing (s j).val (s i).val = CartanMatrix.D n i j) (f : Aut D) :
    PreservesCartan (CartanMatrix.D n) (CartanMatrix.D n) (vertexPerm s f) := by
  intro i j
  rw [← h, ← h, vertexPerm_index, vertexPerm_index]
  exact f.asIso.hom.val.toHom.pairing.symm

private theorem vertexPerm_injective {D : Specs.Pinning.BasedRootDatum.{u}} {n : ℕ}
    (s : Fin n ≃ ↥D.base.support)
    (hD : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    Function.Injective (vertexPerm s) := by
  intro f g h
  apply basedAut_eq_of_simple hD f g
  ext i
  obtain ⟨i, rfl⟩ := s.surjective i
  change f.asIso.hom.val.indexEquiv (s i).val = g.asIso.hom.val.indexEquiv (s i).val
  rw [← vertexPerm_index, ← vertexPerm_index, h]

private theorem vertexPerm_one {D : Specs.Pinning.BasedRootDatum.{u}} {n : ℕ}
    (s : Fin n ≃ ↥D.base.support) : vertexPerm s 1 = Equiv.refl _ := by
  apply Equiv.ext
  intro i
  apply s.injective
  apply Subtype.ext
  exact vertexPerm_index s 1 i

private theorem pinned_corootTransport {L : AdditiveLine k} {P Q : PinnedGroup L}
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair) (j : PinnedIso P Q) (i : D.toBased.I) :
    letI := D.comm
    letI := E.comm
    (D.toBased.datum.coroot i).toMul ≫ j.torus.hom =
      (E.toBased.datum.coroot ((inducedBasedIso j D E).val.indexEquiv i)).toMul := by
  let := D.comm
  let := E.comm
  have h := coroot_transport j D E i
  have hp := congrArg Additive.toMul h
  change (E.toBased.datum.coroot ((inducedBasedIso j D E).val.indexEquiv i)).toMul ≫ j.torus.inv =
    (D.toBased.datum.coroot i).toMul at hp
  let c : Cocharacter Q.pair.T.group := (E.toBased.datum.coroot
    ((inducedBasedIso j D E).val.indexEquiv i)).toMul
  change c ≫ j.torus.inv = _ at hp
  change _ ≫ j.torus.hom = c
  exact (congrArg (fun f : Cocharacter P.pair.T.group => f ≫ j.torus.hom) hp).symm.trans
    (by simp only [Category.assoc, j.torus.inv_hom_id, Category.comp_id])

private theorem conjugatedSubgroupInsertion {G H G' H' : GroupScheme k}
    {f : G ⟶ H} {g : G' ⟶ H'}
    (a : G ≅ G') (b : H ≅ H') (c : G ≅ G) (d : H ≅ H)
    (h : f ≫ b.hom = a.hom ≫ g) (hc : c.hom ≫ f = f ≫ d.hom) :
    (a.symm ≪≫ c ≪≫ a).hom ≫ g = g ≫ (b.symm ≪≫ d ≪≫ b).hom := by
  have h' : a.inv ≫ f = g ≫ b.inv := by
    have hp := congrArg (fun z => a.inv ≫ z ≫ b.inv) h
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id] using hp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← h, ← Category.assoc c.hom, hc, Category.assoc, ← Category.assoc a.inv, h', Category.assoc]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
private theorem fixedVertex_outerFactorization {L : AdditiveLine k} (P : PinnedGroup L)
    (D : AttachedDatum P.pair) {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) (n : ℕ) (hn : 4 ≤ n)
    (hD : letI := D.comm; Specs.SimplyConnectedLattice.corootLattice D = ⊤)
    (s : Fin n ≃ ↥D.toBased.base.support)
    (hs : ∀ i j, D.toBased.datum.pairing (s j).val (s i).val = CartanMatrix.D n i j)
    (i : Fin n) (hi : if n = 4 then i.val ≠ 1 else i.val = 0)
    (C : SplitSpinVectorImage k (ULift.{u} (Fin n))) :
    let I := ULift.{u} (Fin n)
    ∃ (e : C.spin.val ≅ P.pair.G.val) (A : P.pair.G.val ≅ P.pair.G.val)
      (g : (Matrix (I ⊕ I) (I ⊕ I) k)ˣ),
      (∀ x, Specs.Arithmetic.OddSpinModels.hyperbolicForm I k (g.val *ᵥ x) =
        Specs.Arithmetic.OddSpinModels.hyperbolicForm I k x) ∧
      (∀ (R : TestAlgebra k) (x : Points P.pair.G.val.X R),
        let p := e.inv ≫ C.projection ≫ C.inclusion
        (C.orthogonal.points R (x ≫ (A.hom ≫ p).hom.hom)).val.val =
          conjugate (Matrix.GeneralLinearGroup.map (algebraMap k R) g)
            (C.orthogonal.points R (x ≫ p.hom.hom)).val.val) ∧
      C.kernel.inclusion ≫ e.hom ≫ A.hom = C.kernel.inclusion ≫ e.hom ∧
      ∀ f : RelativeAut P.pair.G.val (fieldTest k S),
        ((outerHom (S := S) E) f).asIso.hom.val.indexEquiv (s i).val = (s i).val →
        ∃ q : (groupSections Q.quotient.val).obj (op (fieldTest k S)),
          f = E.inner.app (op (fieldTest k S)) q ∨
          f = (show RelativeAut P.pair.G.val (fieldTest k S) from E.inner.app (op (fieldTest k S)) q) *
            scalarAut (Aut.of A) (fieldTest k S) := by
  dsimp only
  let := D.comm
  obtain ⟨B, D₀, j₀, A₀, t₀, b₀, g, s₀, hD₀, hs₀, hg, _, ht₀, hb₀, hm, hscalar, hcoroot₀⟩ :=
    splitSpinDiagramAction k n hn C
  let := D₀.comm
  obtain ⟨a, ha, hai, hstab⟩ := vectorVertexStabilizer n hn i hi
  obtain ⟨U, p, j, hj⟩ := pinnedTypeDRelabelling P B D D₀ hD hD₀ n s s₀ hs hs₀ a ha
  let e := j₀.symm ≪≫ j.group
  let A := j.group.symm ≪≫ A₀ ≪≫ j.group
  let t := j.torus.symm ≪≫ t₀ ≪≫ j.torus
  let b := j.borel.symm ≪≫ b₀ ≪≫ j.borel
  have ht : t.hom ≫ P.pair.T.inclusion = P.pair.T.inclusion ≫ A.hom :=
    conjugatedSubgroupInsertion j.torus j.group t₀ A₀ j.torus_comm ht₀
  have hb : b.hom ≫ P.pair.B.inclusion = P.pair.B.inclusion ≫ A.hom :=
    conjugatedSubgroupInsertion j.borel j.group b₀ A₀ j.borel_comm hb₀
  refine ⟨e, A, g, hg, ?_, ?_, ?_⟩
  · intro R x
    dsimp only [A, e, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact hm R (x ≫ j.group.inv.hom.hom)
  · have h : C.kernel.inclusion ≫ j₀.inv ≫ A₀.hom = C.kernel.inclusion ≫ j₀.inv := by
      apply (cancel_mono j₀.hom).mp
      simpa only [Category.assoc, j₀.inv_hom_id, Category.comp_id] using hscalar
    dsimp only [e, A, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (· ≫ j.group.hom) h |>.trans (by simp only [Category.assoc])
  let M := scalarAut (Aut.of A) (fieldTest k S)
  let d := outerHom (S := S) E M
  let π : Equiv.Perm (Fin n) := Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩
  have hd := outerAction_on_coroots (S := S) D E A t b ht hb
  have hjC (z : Fin n) :
      (D₀.toBased.datum.coroot (s₀ z).val).toMul ≫ j.torus.hom =
        (D.toBased.datum.coroot (s (a z)).val).toMul := by
    have h := pinned_corootTransport D₀ D j (s₀ z).val
    exact h.trans (congrArg (fun i : D.toBased.I => (D.toBased.datum.coroot i).toMul) (hj z))
  have hdc (z : Fin n) : vertexPerm s d (a z) = a (π z) := by
    apply s.injective
    apply Subtype.ext
    rw [vertexPerm_index]
    apply D.toBased.datum.coroot.injective
    apply Additive.toMul.injective
    rw [← hd (s (a z)).val, ← hjC, ← hjC]
    change (_ ≫ j.torus.hom) ≫ (j.torus.inv ≫ t₀.hom ≫ j.torus.hom) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have h₀ : (D₀.toBased.datum.coroot (s₀ z).val).toMul ≫ t₀.hom =
        (D₀.toBased.datum.coroot (s₀ (π z)).val).toMul := hcoroot₀ z
    rw [← Category.assoc, h₀]
  have hdπ : (a.trans (vertexPerm s d)).trans a.symm = π := by
    ext z
    simp only [Equiv.trans_apply, hdc, Equiv.symm_apply_apply]
  intro f hf
  let d' := outerHom (S := S) E f
  have hfix : vertexPerm s d' i = i := by
    apply s.injective
    apply Subtype.ext
    exact (vertexPerm_index s d' i).trans hf
  rcases hstab (vertexPerm s d') (vertexPerm_preservesCartan s hs d') hfix with hh | hh
  · have h₁ : vertexPerm s d' = vertexPerm s 1 := by
      rw [vertexPerm_one]
      apply Equiv.ext
      intro x
      obtain ⟨z, rfl⟩ := a.surjective x
      have he := congrFun (congrArg Equiv.toFun hh) z
      change a.symm (vertexPerm s d' (a z)) = z at he
      exact (a.symm_apply_eq).mp he
    have hf' : outerHom (S := S) E f = 1 := vertexPerm_injective s hD h₁
    obtain ⟨q, hq⟩ := (splitKernel E f).mp hf'
    exact ⟨q, Or.inl hq.symm⟩
  · have h₁ : vertexPerm s d' = vertexPerm s d := by
      rw [← show (a.trans (vertexPerm s d')).trans a.symm = π from hh] at hdπ
      apply Equiv.ext
      intro x
      obtain ⟨z, rfl⟩ := a.surjective x
      have he := congrFun (congrArg Equiv.toFun hdπ) z
      exact (a.symm.injective he).symm
    have hEq : outerHom (S := S) E f = outerHom (S := S) E M :=
      vertexPerm_injective s hD h₁
    have hker : outerHom (S := S) E (f * M⁻¹) = 1 := by
      rw [map_mul, map_inv, hEq, mul_inv_cancel]
    obtain ⟨q, hq⟩ := (splitKernel E (f * M⁻¹)).mp hker
    refine ⟨q, Or.inr ?_⟩
    rw [hq, inv_mul_cancel_right]

/-- Realize the stabilizer of the marked vector vertex using the split cover. -/
theorem fixedVertexOuterFactorization : FixedVertexOuterFactorization.{u} := by
  intro k S _ _ _ L P D l Q E n hn hD s hs i hi C
  exact fixedVertex_outerFactorization (S := S) P D E n hn hD s hs i hi C

end

end VectorVertexFactorization



section FiniteVertexComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Pinning (AttachedDatum PinnedGroup)
open Specs.RootGroups (AdditiveLine)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence RelativeAut relativePoints
  restrictIso restrictAut constantGroup)
open Specs.RelativeFormComparison (fieldTest fieldMap transportedAut IsInduced)
open Specs.QuasiSplitInnerForms (outerHom constantEvaluation)
open LinearAlgebraicGroups.Descent.Forms (raiseIso scalarTowerIso finiteLevelIsomorphisms)
open LinearAlgebraicGroups.Descent.NonabelianCohomology (restriction)
open private inLevel inLevel_tmul raiseIso_inLevel raiseIso_symm applyIso exists_coordinate_model
  from LinearAlgebraicGroups.Descent.Forms
open private extendedGroupIso extendedSpecIso_hom_fst from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private schemeIsoEquiv_apply induced_iff hopfIsoEquiv hopfIsoEquiv_apply hopfIsoEquiv_ground
  groundIso hopfSchemeIso coordinatePoint coordinatePoint_projection coordinatePoint_field
  coordinatePoint_ext projection hopfIsoEquiv_evaluate
  from LinearAlgebraicGroups.Descent.RelativeFormComparison

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

private theorem extendedGroupIso_comparison :
    LinearAlgebraicGroups.Descent.Forms.IsScalarExtensionComparison (extendedGroupIso (k := k) S) := by
  intro C
  exact extendedSpecIso_hom_fst S C

variable (L : FiniteGaloisIntermediateField k S)

private def finiteFieldInclusion : fieldTest k S ⟶ fieldTest k L :=
  (testSpec k).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L S)).op

private def finiteHopfInclusion (A : HopfAlgebraCategory k) : extendedHopf L A →+* extendedHopf S A :=
  (scalarTowerIso A).hom.hom.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : extendedHopf L A →ₐ[L] S ⊗[L] extendedHopf L A).toRingHom

private theorem finiteHopfInclusion_tmul (A : HopfAlgebraCategory k) (a : L) (x : A) :
    finiteHopfInclusion L A (a ⊗ₜ[k] x) = algebraMap L S a ⊗ₜ[k] x :=
  inLevel_tmul L a x

private theorem finiteHopfInclusion_projection (A : HopfAlgebraCategory k) :
    Spec.map (CommRingCat.ofHom (finiteHopfInclusion L A)) ≫ projection (S := L) A =
      projection (S := S) A := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change A at x
  change finiteHopfInclusion L A ((1 : L) ⊗ₜ[k] x) = (1 : S) ⊗ₜ[k] x
  rw [finiteHopfInclusion_tmul, map_one]

private theorem finiteHopfInclusion_field (A : HopfAlgebraCategory k) :
    Spec.map (CommRingCat.ofHom (finiteHopfInclusion L A)) ≫ (specGroup (extendedHopf L A)).X.hom =
      (specGroup (extendedHopf S A)).X.hom ≫ (finiteFieldInclusion L).left := by
  change Spec.map (CommRingCat.ofHom (finiteHopfInclusion L A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L (extendedHopf L A))) =
    Spec.map (CommRingCat.ofHom (algebraMap S (extendedHopf S A))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L S))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact finiteHopfInclusion_tmul L A x 1

private theorem coordinatePoint_finiteRestriction {A : HopfAlgebraCategory k}
    (U : Over (fieldTest k S)) (x : U.left ⟶ (specGroup A).X) :
    coordinatePoint (extendedGroupIso L) ((Over.map (finiteFieldInclusion L)).obj U) x =
      coordinatePoint (extendedGroupIso S) U x ≫
        Spec.map (CommRingCat.ofHom (finiteHopfInclusion L A)) := by
  apply coordinatePoint_ext (extendedGroupIso L) (extendedGroupIso_comparison (k := k) (S := L))
  · rw [coordinatePoint_projection _ extendedGroupIso_comparison, Category.assoc,
      finiteHopfInclusion_projection, coordinatePoint_projection _ extendedGroupIso_comparison]
  · rw [coordinatePoint_field, Category.assoc, finiteHopfInclusion_field, ← Category.assoc,
      coordinatePoint_field]
    rfl

private theorem finiteHopfInclusion_raisedIso {A B : HopfAlgebraCategory k}
    (j : extendedHopf L A ≅ extendedHopf L B) :
    Spec.map (CommRingCat.ofHom (finiteHopfInclusion L A)) ≫
        Spec.map (CommRingCat.ofHom j.inv.hom.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom (raiseIso (S := S) j).inv.hom.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (finiteHopfInclusion L B)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change inLevel L A (applyIso j.symm x) = applyIso (raiseIso (S := S) j).symm (inLevel L B x)
  rw [← raiseIso_symm L, raiseIso_inLevel]

set_option maxHeartbeats 950000 in
private theorem restrictHopfIso_finite {A B : HopfAlgebraCategory k} {G H : GroupScheme k}
    (g : specGroup A ≅ G) (h : specGroup B ≅ H) (j : extendedHopf L A ≅ extendedHopf L B) :
    restrictIso (finiteFieldInclusion L) (hopfIsoEquiv (extendedGroupIso L) g h j) =
      hopfIsoEquiv (extendedGroupIso S) g h (raiseIso (S := S) j) := by
  rw [hopfIsoEquiv_ground (extendedGroupIso L) g h j,
    hopfIsoEquiv_ground (extendedGroupIso S) g h (raiseIso (S := S) j)]
  have he :
      restrictIso (finiteFieldInclusion L)
        (hopfIsoEquiv (extendedGroupIso L) (Iso.refl (specGroup A)) (Iso.refl (specGroup B)) j) =
      hopfIsoEquiv (extendedGroupIso S) (Iso.refl (specGroup A)) (Iso.refl (specGroup B))
        (raiseIso (S := S) j) := by
    apply Iso.ext
    apply NatTrans.ext
    funext U
    apply GrpCat.ext
    intro x
    change U.unop.left ⟶ (specGroup A).X at x
    apply Over.OverMorphism.ext
    let V := (Over.map (finiteFieldInclusion L)).obj U.unop
    change (((hopfIsoEquiv (extendedGroupIso L) (Iso.refl (specGroup A))
      (Iso.refl (specGroup B)) j).hom.app (op V)).hom x).left = _
    rw [hopfIsoEquiv_evaluate _ extendedGroupIso_comparison j V x,
      hopfIsoEquiv_evaluate _ extendedGroupIso_comparison (raiseIso (S := S) j) U.unop x,
      coordinatePoint_finiteRestriction, Category.assoc, ← Category.assoc
        (Spec.map (CommRingCat.ofHom (finiteHopfInclusion L A))), finiteHopfInclusion_raisedIso]
    simp only [Category.assoc, finiteHopfInclusion_projection]
  have hcomp {G H J : GroupScheme k}
      (a : relativePoints G (fieldTest k L) ≅ relativePoints H (fieldTest k L))
      (b : relativePoints H (fieldTest k L) ≅ relativePoints J (fieldTest k L)) :
      restrictIso (finiteFieldInclusion L) (a ≪≫ b) =
        restrictIso (finiteFieldInclusion L) a ≪≫ restrictIso (finiteFieldInclusion L) b := by
    apply Iso.ext
    rfl
  have hground {G H : GroupScheme k} (a : G ≅ H) :
      restrictIso (finiteFieldInclusion L) (groundIso (S := L) a) = groundIso (S := S) a := by
    apply Iso.ext
    rfl
  rw [hcomp, hcomp, hground, hground, he]

private theorem finiteFieldInclusion_comm (σ : Gal(S/k)) :
    fieldMap k S σ ≫ finiteFieldInclusion L =
      finiteFieldInclusion L ≫ fieldMap k L (restriction L σ) := by
  change (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
      (testSpec k).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L S)).op =
      (testSpec k).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L S)).op ≫
        (testSpec k).map (CommAlgCat.ofHom (restriction L σ).toAlgHom).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  apply congrArg (fun a : CommAlgCat.of k L ⟶ CommAlgCat.of k S => (testSpec k).map a.op)
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  change σ (algebraMap L S a) = algebraMap L S (restriction L σ a)
  exact (σ.restrictNormal_commutes L a).symm

private theorem transportedAut_finite_restrict {G H : GroupScheme k}
    (r : relativePoints G (fieldTest k L) ≅ relativePoints H (fieldTest k L))
    (σ : Gal(S/k)) :
    transportedAut k S (restrictIso (finiteFieldInclusion L) r) σ =
      restrictAut (finiteFieldInclusion L) (transportedAut k L r (restriction L σ)) := by
  have hcomp {T₀ T₁ T₂ : SchemeOver k} (a : T₁ ⟶ T₀) (b : T₂ ⟶ T₁)
      (i : relativePoints G T₀ ≅ relativePoints H T₀) :
      restrictIso b (restrictIso a i) = restrictIso (b ≫ a) i := by
    apply Iso.ext
    ext U x
    rfl
  apply Aut.ext
  change restrictIso (fieldMap k S σ) (restrictIso (finiteFieldInclusion L) r) ≪≫
      (restrictIso (finiteFieldInclusion L) r).symm =
    restrictIso (finiteFieldInclusion L)
      (restrictIso (fieldMap k L (restriction L σ)) r ≪≫ r.symm)
  rw [hcomp, finiteFieldInclusion_comm, ← hcomp]
  apply Iso.ext
  rfl

private theorem outerHom_finite_restrict {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) (f : RelativeAut P.pair.G.val (fieldTest k L)) :
    outerHom (S := S) E (restrictAut (finiteFieldInclusion L) f) = outerHom (S := L) E f := by
  have he := ConcreteCategory.congr_hom (E.outer.naturality (finiteFieldInclusion L).op) f
  change E.outer.app (op (fieldTest k S)) (restrictAut (finiteFieldInclusion L) f) =
    (constantGroup (k := k) (Aut D.toBased)).map (finiteFieldInclusion L).op
      (E.outer.app (op (fieldTest k L)) f) at he
  change constantEvaluation k S _ (E.outer.app (op (fieldTest k S))
    (restrictAut (finiteFieldInclusion L) f)) =
      constantEvaluation k L _ (E.outer.app (op (fieldTest k L)) f)
  rw [he]
  let z := E.outer.app (op (fieldTest k L)) f
  change z.down _ = z.down _
  let : Subsingleton (fieldTest k L).left := inferInstanceAs (Subsingleton (PrimeSpectrum L))
  exact congrArg z.down (Subsingleton.elim _ _)

variable [IsSepClosure k S]

set_option maxHeartbeats 1100000 in
private theorem fixedVertex_finiteLevel {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) (G : AffineAlgebraicGroup k) (v : D.toBased.I)
    (e : (groupBaseChange k S).obj P.pair.G.val ≅ (groupBaseChange k S).obj G.val)
    (r : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (_hr : IsInduced k S e r)
    (h : ∀ σ : Gal(S/k), ((outerHom (S := S) E) (transportedAut k S r σ)).asIso.hom.val.indexEquiv v = v) :
    ∃ (L : FiniteGaloisIntermediateField k S)
      (j : (groupBaseChange k L).obj P.pair.G.val ≅ (groupBaseChange k L).obj G.val)
      (t : relativePoints P.pair.G.val (fieldTest k L) ≅ relativePoints G.val (fieldTest k L)),
      IsInduced k L j t ∧ r = restrictIso (finiteFieldInclusion L) t ∧
      ∀ δ : Gal(L/k), ((outerHom (S := L) E) (transportedAut k L t δ)).asIso.hom.val.indexEquiv v = v := by
  obtain ⟨B, hB, ⟨g⟩⟩ := exists_coordinate_model P.pair.G
  obtain ⟨C, hC, ⟨f⟩⟩ := exists_coordinate_model G
  let w := (hopfIsoEquiv (extendedGroupIso S) g f).symm r
  obtain ⟨L, j, _, hL⟩ := finiteLevelIsomorphisms B C hB hC ⊥ w
  let t := hopfIsoEquiv (extendedGroupIso L) g f j
  have ht : r = restrictIso (finiteFieldInclusion L) t := by
    dsimp only [t]
    rw [restrictHopfIso_finite, hL]
    exact ((hopfIsoEquiv (extendedGroupIso S) g f).apply_symm_apply r).symm
  refine ⟨L, hopfSchemeIso (extendedGroupIso L) g f j, t,
    (induced_iff _ _).mpr (hopfIsoEquiv_apply _ _ _ _).symm, ht, ?_⟩
  intro δ
  obtain ⟨σ, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective S (F := k) (K₁ := L)) δ
  have hv := h σ
  rw [ht, transportedAut_finite_restrict, outerHom_finite_restrict] at hv
  exact hv

/-- Restrict the original comparison and its fixed vertex to a finite Galois splitting field. -/
theorem fixedVertexFiniteLevel : FixedVertexFiniteLevel.{u} := by
  intro k S _ _ _ _ A P D l Q E G v e r hr h
  exact fixedVertex_finiteLevel E G v e r hr h

end

end FiniteVertexComparison

section MatrixConjugationDescent

open Matrix AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open private liftOverTestAlgebra from LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]

private theorem matrixInner_mul (R : Type u) [CommRing R] {J : Type u} [Fintype J] [DecidableEq J]
    (g h : (Matrix J J R)ˣ) : matrixInner (g * h) = matrixInner g * matrixInner h := by
  apply AlgEquiv.ext
  intro X
  change (g.val * h.val) * X * (h.inv * g.inv) = g.val * (h.val * X * h.inv) * g.inv
  simp only [mul_assoc]

private theorem conjugation_difference_commutes {R : Type u} [CommRing R]
    {J : Type u} [Fintype J] [DecidableEq J]
    (g h : (Matrix J J R)ˣ) (X : Matrix J J R) (e : conjugate g X = conjugate h X) :
    Commute (h⁻¹ * g).val X := by
  have he := congrArg (fun Y => h.inv * Y * g.val) e
  change h.inv * (g.val * X * g.inv) * g.val = h.inv * (h.val * X * h.inv) * g.val at he
  change (h.inv * g.val) * X = X * (h.inv * g.val)
  calc
    _ = h.inv * (g.val * X) := mul_assoc _ _ _
    _ = h.inv * ((g.val * X) * (g.inv * g.val)) := by rw [g.inv_val, mul_one]
    _ = h.inv * (g.val * X * g.inv) * g.val := by simp only [mul_assoc]
    _ = h.inv * (h.val * X * h.inv) * g.val := he
    _ = (h.inv * h.val) * (X * (h.inv * g.val)) := by simp only [mul_assoc]
    _ = _ := by rw [h.inv_val, one_mul]

private theorem matrixInner_eq_of_scalar {R J : Type u} [CommRing R] [Fintype J] [DecidableEq J]
    (g h : (Matrix J J R)ˣ) (c : R) (hc : (h⁻¹ * g).val = Matrix.scalar J c) :
    matrixInner g = matrixInner h := by
  let x := h⁻¹ * g
  have hId : matrixInner x = 1 := by
    apply AlgEquiv.ext
    intro X
    have hscalar : x.val = algebraMap R (Matrix J J R) c := hc
    change x.val * X * x.inv = X
    rw [show x.val * X = X * x.val from hscalar.symm ▸ Algebra.commutes c X,
      mul_assoc, x.val_inv, mul_one]
  have hxg : h * x = g := mul_inv_cancel_left h g
  have H := matrixInner_mul R h x
  rw [hId, mul_one, hxg] at H
  exact H

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private theorem vectorMatrixConjugation_unique (hRank : 4 ≤ Fintype.card I)
    (P : SplitSpinVectorImage k I) (R : TestAlgebra k)
    (g h : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ)
    (hc : ∀ (S : TestAlgebra k) (f : R ⟶ S) (a : Points P.spin.val.X S),
      conjugate (Matrix.GeneralLinearGroup.map f.hom g) (spinVectorMatrix P S a) =
        conjugate (Matrix.GeneralLinearGroup.map f.hom h) (spinVectorMatrix P S a)) :
    matrixInner g = matrixInner h := by
  let x := h⁻¹ * g
  have : Flat P.projection.hom.hom.left := P.flat
  have : Surjective P.projection.hom.hom.left := P.surjective
  have : IsFinite P.projection.hom.hom.left := P.finite
  have : LocallyOfFiniteType P.image.val.X.hom := P.image.property.2.1
  have : IsLocallyNoetherian P.image.val.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian P.image.val.X.hom
  have scalar : ∃ c : R, x.val = Matrix.diagonal (fun _ => c) := by
    apply splitVectorCentralizer k I hRank P R x.val
    intro S f y
    obtain ⟨W, u, a, hu, _, ha⟩ := liftOverTestAlgebra P.projection S y
    have hM : (vectorImageMatrix P S y).map u.hom = spinVectorMatrix P W a := by
      change (vectorImageMatrix P S y).map u.hom =
        vectorImageMatrix P W (a ≫ P.projection.hom.hom)
      rw [← vectorImageMatrix_map, show a ≫ P.projection.hom.hom = mapPoints u y from ha]
    have hx : (x.val.map f.hom).map u.hom =
        ((Matrix.GeneralLinearGroup.map (f ≫ u).hom h)⁻¹ *
          (Matrix.GeneralLinearGroup.map (f ≫ u).hom g)).val := by
      rw [← map_inv, ← map_mul]
      ext i j
      rfl
    apply Matrix.ext
    intro i j
    apply hu.injective
    have he := conjugation_difference_commutes _ _ _ (hc W (f ≫ u) a)
    have h := congrArg (fun M : Matrix (I ⊕ I) (I ⊕ I) W => M i j) he.eq
    rw [← hx, ← hM, ← Matrix.map_mul, ← Matrix.map_mul] at h
    exact h
  obtain ⟨c, hc'⟩ := scalar
  exact matrixInner_eq_of_scalar g h c hc'

private theorem tensor_equalizer_range (S : Type u) [CommRing S] [Algebra k S] [Nontrivial S]
    {s : S} (h : s ⊗ₜ[k] (1 : S) = (1 : S) ⊗ₜ[k] s) : ∃ a : k, algebraMap k S a = s := by
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : S) ≠ 0)
  refine ⟨ℓ s, ?_⟩
  have H := congrArg (TensorProduct.lid k S ∘ TensorProduct.map ℓ (LinearMap.id (R := k) (M := S))) h
  change ℓ s • (1 : S) = ℓ 1 • s at H
  simpa only [hℓ, one_smul, Algebra.smul_def, map_one, one_mul, mul_one] using H

private theorem matrix_map_injective {R S J : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (fun X : Matrix J J R => X.map f) := by
  intro X Y h
  ext i j
  exact hf (congrArg (fun Z : Matrix J J S => Z i j) h)

private theorem conjugate_map {R S J : Type u} [CommRing R] [CommRing S]
    [Fintype J] [DecidableEq J] (f : R →+* S) (g : (Matrix J J R)ˣ) (X : Matrix J J R) :
    (conjugate g X).map f = conjugate (Matrix.GeneralLinearGroup.map f g) (X.map f) := by
  unfold conjugate
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

private theorem matrixInner_ext_ground {R S J : Type u} [CommRing R] [CommRing S]
    [Fintype J] [DecidableEq J] (f : R →+* S) (g h : (Matrix J J S)ˣ)
    (hc : ∀ X : Matrix J J R, conjugate g (X.map f) = conjugate h (X.map f)) :
    matrixInner g = matrixInner h := by
  classical
  obtain ⟨c, hc'⟩ := (Matrix.mem_range_scalar_iff_commute_single' (M := (h⁻¹ * g).val)).mpr (by
    intro i j
    have H := conjugation_difference_commutes g h _ (hc (Matrix.single i j 1))
    have eq : (Matrix.single i j (1 : R)).map f = Matrix.single i j (1 : S) := by
      ext a b
      by_cases h₁ : i = a <;> by_cases h₂ : j = b <;> simp [h₁, h₂]
    rw [eq] at H
    exact H.symm)
  exact matrixInner_eq_of_scalar g h c hc'.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem projectiveMatrix_descent (S J : Type u) [CommRing S] [Algebra k S] [Nontrivial S]
    [Fintype J] [DecidableEq J] [Nonempty J] (g : (Matrix J J S)ˣ)
    (h : let l : S →ₐ[k] S ⊗[k] S := Algebra.TensorProduct.includeLeft
         let r : S →ₐ[k] S ⊗[k] S := Algebra.TensorProduct.includeRight
         matrixInner (Matrix.GeneralLinearGroup.map l.toRingHom g) =
           matrixInner (Matrix.GeneralLinearGroup.map r.toRingHom g)) :
    ∃ a : (Matrix J J k)ˣ,
      matrixInner (Matrix.GeneralLinearGroup.map (algebraMap k S) a) = matrixInner g := by
  classical
  let i := algebraMap k S
  let l : S →ₐ[k] S ⊗[k] S := Algebra.TensorProduct.includeLeft
  let r : S →ₐ[k] S ⊗[k] S := Algebra.TensorProduct.includeRight
  let F := matrixInner g
  have hrow (X : Matrix J J k) (a b : J) :
      ∃ x : k, i x = F (X.map i) a b := by
    have hX : (X.map i).map l.toRingHom = (X.map i).map r.toRingHom := by
      ext a b
      exact (l.commutes (X a b)).trans (r.commutes (X a b)).symm
    have hG : (F (X.map i)).map l = (F (X.map i)).map r := by
      change (conjugate g (X.map i)).map l.toRingHom = (conjugate g (X.map i)).map r.toRingHom
      rw [conjugate_map, conjugate_map, hX]
      exact DFunLike.congr_fun h _
    exact tensor_equalizer_range S (congrArg (fun M : Matrix J J (S ⊗[k] S) => M a b) hG)
  let A : Matrix J J k → Matrix J J k := fun X =>
    Matrix.of (fun a b => (hrow X a b).choose)
  have hA (X : Matrix J J k) : (A X).map i = F (X.map i) := by
    ext a b
    exact (hrow X a b).choose_spec
  have hi := matrix_map_injective (J := J) i i.injective
  let E : Matrix J J k →ₐ[k] Matrix J J k :=
    { toFun := A
      map_one' := hi (by dsimp only; rw [hA, Matrix.map_one _ (map_zero _) (map_one _)]; exact map_one F)
      map_zero' := hi (by dsimp only; rw [hA, Matrix.map_zero _ (map_zero _)]; exact map_zero F)
      map_add' X Y := hi (by dsimp only; rw [hA, Matrix.map_add _ (map_add i), Matrix.map_add _ (map_add i), hA, hA]; exact map_add F _ _)
      map_mul' X Y := hi (by dsimp only; rw [hA, Matrix.map_mul, Matrix.map_mul, hA, hA]; exact map_mul F _ _)
      commutes' a := hi (by
        dsimp only
        rw [hA]
        have h : (algebraMap k (Matrix J J k) a).map i = algebraMap S (Matrix J J S) (i a) := by
          change (Matrix.scalar J a).map i = Matrix.scalar J (i a)
          simp [Matrix.scalar_apply, Matrix.diagonal_map]
        rw [h, F.commutes]) }
  have hE : Function.Injective E := by
    intro X Y eq
    apply hi
    apply F.injective
    rw [← hA, ← hA]
    exact congrArg (fun M : Matrix J J k => M.map i) eq
  let e := AlgEquiv.ofBijective E ⟨hE, E.toLinearMap.injective_iff_surjective.mp hE⟩
  have hCSA : _root_.Specs.RM03.CSA.isCentralSimple k (Matrix J J k) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨a, ha⟩ := RM03.CSA.algEquiv_isInner hCSA e
  refine ⟨a, matrixInner_ext_ground i _ _ fun X => ?_⟩
  have he : e X = conjugate a X := ha X
  rw [← conjugate_map, ← he]
  exact hA X

end

end MatrixConjugationDescent



section RelativeInnerConjugation

open Matrix AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonObj TensorProduct

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.AutomorphismSequence (ExactSequence AdjointQuotient RelativeAut groupSections restrictAut innerAut)
open Specs.RelativeFormComparison (fieldTest)
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open private liftOverTestAlgebra from LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]

private abbrev fieldObject {R : TestAlgebra k} (a : CommAlgCat.of k K ⟶ R) :
    Over (fieldTest k K) := Over.mk ((testSpec k).map a.op)

private abbrev relativeApply {G : GroupScheme k} (u : RelativeAut G (fieldTest k K))
    {R : TestAlgebra k} (a : CommAlgCat.of k K ⟶ R) (x : Points G.X R) : Points G.X R :=
  (u.asIso.hom.app (op (fieldObject a))).hom x

private def fieldObject_map {R S : TestAlgebra k}
    (a : CommAlgCat.of k K ⟶ R) (b : R ⟶ S) :
    fieldObject (a ≫ b) ⟶ fieldObject a :=
  Over.homMk ((testSpec k).map b.op) (by
    change (testSpec k).map b.op ≫ (testSpec k).map a.op = (testSpec k).map (a ≫ b).op
    rw [op_comp, Functor.map_comp])

private theorem relativeApply_map {G : GroupScheme k} (u : RelativeAut G (fieldTest k K))
    {R S : TestAlgebra k} (a : CommAlgCat.of k K ⟶ R) (b : R ⟶ S) (x : Points G.X R) :
    mapPoints b (relativeApply u a x) = relativeApply u (a ≫ b) (mapPoints b x) := by
  have h := ConcreteCategory.congr_hom (u.asIso.hom.naturality (fieldObject_map a b).op) x
  change relativeApply u (a ≫ b) (mapPoints b x) = mapPoints b (relativeApply u a x) at h
  exact h.symm

private theorem relativeInnerApply {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G} {O}
    (E : ExactSequence G Q O) (q : (groupSections Q.quotient.val).obj (op (fieldTest k K)))
    {R : TestAlgebra k} (a : CommAlgCat.of k K ⟶ R) (y : Points G.val.X R)
    (hy : y ≫ Q.projection.hom.hom = mapPoints a q.down)
    (x : Points G.val.X R) :
    relativeApply (show RelativeAut G.val (fieldTest k K) from E.inner.app (op (fieldTest k K)) q)
      a x = y * x * y⁻¹ := by
  let S := (testSpec k).obj (op R)
  let f := (testSpec k).map a.op
  let v : RelativeAut G.val (fieldTest k K) := E.inner.app (op (fieldTest k K)) q
  have h := ConcreteCategory.congr_hom (E.inner.naturality f.op) q
  change E.inner.app (op S) ⟨mapPoints a q.down⟩ = restrictAut f v at h
  rw [← hy, E.onLift S y] at h
  have he := congrArg (fun u : RelativeAut G.val S =>
    (u.asIso.hom.app (op (Over.mk (𝟙 S) : Over S))).hom x) h
  change ((𝟙 S ≫ y) * x * (𝟙 S ≫ y)⁻¹) = relativeApply v a x at he
  simpa only [Category.id_comp] using he.symm

private def spinVectorUnit (C : SplitSpinVectorImage k I) (R : TestAlgebra k) :
    Points C.spin.val.X R →* (Matrix (I ⊕ I) (I ⊕ I) R)ˣ :=
  (orthogonalMatrices I R).subtype.comp ((C.orthogonal.points R).toMonoidHom.comp
    (((groupPointsFunctor k).map (C.projection ≫ C.inclusion)).app R).hom)

private theorem spinVectorUnit_map (C : SplitSpinVectorImage k I) {R S : TestAlgebra k}
    (f : R ⟶ S) (x : Points C.spin.val.X R) :
    spinVectorUnit C S (mapPoints f x) =
      Matrix.GeneralLinearGroup.map f.hom (spinVectorUnit C R x) := by
  apply Units.ext
  exact spinVectorMatrix_map C f x

private def referenceVectorUnit (C : SplitSpinVectorImage k I) {G : AffineAlgebraicGroup k}
    (e : C.spin.val ≅ G.val) (R : TestAlgebra k) :
    Points G.val.X R →* (Matrix (I ⊕ I) (I ⊕ I) R)ˣ :=
  (spinVectorUnit C R).comp (((groupPointsFunctor k).map e.inv).app R).hom

private theorem referenceVectorUnit_map (C : SplitSpinVectorImage k I) {G : AffineAlgebraicGroup k}
    (e : C.spin.val ≅ G.val) {R S : TestAlgebra k} (f : R ⟶ S) (x : Points G.val.X R) :
    referenceVectorUnit C e S (mapPoints f x) =
      Matrix.GeneralLinearGroup.map f.hom (referenceVectorUnit C e R x) :=
  spinVectorUnit_map C f (x ≫ e.inv.hom.hom)

private theorem referenceVectorUnit_compare (C : SplitSpinVectorImage k I) {G : AffineAlgebraicGroup k}
    (e : C.spin.val ≅ G.val) (R : TestAlgebra k) (x : Points C.spin.val.X R) :
    (referenceVectorUnit C e R (x ≫ e.hom.hom.hom)).val = spinVectorMatrix C R x := by
  change spinVectorMatrix C R ((x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) = _
  congr 1
  have h := congrArg (Grp.forget (SchemeOver k)).map e.hom_inv_id
  change e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ at h
  rw [Category.assoc, h, Category.comp_id]

private theorem referenceVectorUnit_isometry (C : SplitSpinVectorImage k I)
    {G : AffineAlgebraicGroup k} (e : C.spin.val ≅ G.val)
    (R : TestAlgebra k) (x : Points G.val.X R) (v : I ⊕ I → R) :
    hyperbolicForm I R ((referenceVectorUnit C e R x).val *ᵥ v) = hyperbolicForm I R v :=
  (C.orthogonal.points R ((x ≫ e.inv.hom.hom) ≫ (C.projection ≫ C.inclusion).hom.hom)).property v

private theorem relativeInner_vectorLocal {G : AffineAlgebraicGroup k}
    {Q : AdjointQuotient G} {O} (E : ExactSequence G Q O)
    (q : (groupSections Q.quotient.val).obj (op (fieldTest k K)))
    (C : SplitSpinVectorImage k I) (e : C.spin.val ≅ G.val) :
    ∃ (R : TestAlgebra k) (a : CommAlgCat.of k K ⟶ R) (g : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ),
      Function.Injective a.hom ∧
      (∀ x, hyperbolicForm I R (g.val *ᵥ x) = hyperbolicForm I R x) ∧
      ∀ (T : TestAlgebra k) (b : R ⟶ T) (x : Points G.val.X T),
        (referenceVectorUnit C e T (relativeApply
          (show RelativeAut G.val (fieldTest k K) from E.inner.app (op (fieldTest k K)) q)
          (a ≫ b) x)).val =
          conjugate (Matrix.GeneralLinearGroup.map b.hom g) (referenceVectorUnit C e T x).val := by
  have : IsAffine G.val.X.left := G.property.1
  have : IsAffine Q.quotient.val.X.left := Q.quotient.property.1
  have : Flat Q.projection.hom.hom.left := Q.fppf.1
  have : Surjective Q.projection.hom.hom.left := Q.fppf.2.1
  have : LocallyOfFinitePresentation Q.projection.hom.hom.left := Q.fppf.2.2
  obtain ⟨R, a, y, ha, _, hy⟩ := liftOverTestAlgebra Q.projection (CommAlgCat.of k K) q.down
  change y ≫ Q.projection.hom.hom = (testSpec k).map a.op ≫ q.down at hy
  let g := referenceVectorUnit C e R y
  refine ⟨R, a, g, ha.injective, referenceVectorUnit_isometry C e R y, ?_⟩
  intro T b x
  have hmap : mapPoints b y ≫ Q.projection.hom.hom = mapPoints (a ≫ b) q.down := by
    change ((testSpec k).map b.op ≫ y) ≫ Q.projection.hom.hom =
      (testSpec k).map (a ≫ b).op ≫ q.down
    rw [Category.assoc, hy, op_comp, Functor.map_comp, Category.assoc]
  rw [relativeInnerApply E q (a ≫ b) (mapPoints b y) hmap x, map_mul, map_mul, map_inv,
    referenceVectorUnit_map C e]
  rfl

end

end RelativeInnerConjugation



section RelativeInnerSimilitude

open Matrix AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.AutomorphismSequence (ExactSequence AdjointQuotient RelativeAut groupSections restrictAut innerAut)
open Specs.RelativeFormComparison (fieldTest)
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]

private theorem hyperbolicForm_map {F R : Type u} [CommRing F] [CommRing R]
    (a : F →+* R) (x : I ⊕ I → F) :
    a (hyperbolicForm I F x) = hyperbolicForm I R (a ∘ x) := by
  simp only [hyperbolicForm_apply, Function.comp_apply, map_sum, map_mul]

private theorem similitude_of_projective_isometry {F R : Type u} [Field F] [CommRing R] [Nonempty I]
    (a : F →+* R) (ha : Function.Injective a) (g : (Matrix (I ⊕ I) (I ⊕ I) F)ˣ)
    (h : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ)
    (hh : ∀ x, hyperbolicForm I R (h.val *ᵥ x) = hyperbolicForm I R x)
    (he : matrixInner (Matrix.GeneralLinearGroup.map a g) = matrixInner h) :
    ∃ c : Fˣ, ∀ x, hyperbolicForm I F (g.val *ᵥ x) = (c : F) * hyperbolicForm I F x := by
  let gR := Matrix.GeneralLinearGroup.map a g
  obtain ⟨b, hb⟩ := (Matrix.mem_range_scalar_iff_commute_single' (M := (h⁻¹ * gR).val)).mpr (by
    intro i j
    exact (conjugation_difference_commutes gR h _
      (DFunLike.congr_fun he (Matrix.single i j 1))).symm)
  have hsc : gR.val = b • h.val := by
    have H := congrArg (fun M : Matrix (I ⊕ I) (I ⊕ I) R => h.val * M) hb
    change h.val * algebraMap R (Matrix (I ⊕ I) (I ⊕ I) R) b =
      h.val * (h.inv * gR.val) at H
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, ← mul_assoc, h.val_inv, one_mul] at H
    exact H.symm
  have hscale (x : I ⊕ I → R) : hyperbolicForm I R (gR.val *ᵥ x) =
      (b * b) * hyperbolicForm I R x := by
    rw [hsc, Matrix.smul_mulVec, QuadraticMap.map_smul, hh]
    rfl
  let i : I := Classical.choice inferInstance
  let v : I ⊕ I → F := Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1
  have hv : hyperbolicForm I F v = 1 := by
    simp [v, hyperbolicForm_apply, Pi.single_apply]
  let c := hyperbolicForm I F (g.val *ᵥ v)
  have hg (x : I ⊕ I → F) : a (hyperbolicForm I F (g.val *ᵥ x)) =
      (b * b) * a (hyperbolicForm I F x) := by
    rw [hyperbolicForm_map, hyperbolicForm_map, ← hscale]
    congr 1
    ext j
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rfl
  have hc : a c = b * b := by
    change a (hyperbolicForm I F (g.val *ᵥ v)) = _
    rw [hg, hv, map_one, mul_one]
  have hq (x : I ⊕ I → F) : hyperbolicForm I F (g.val *ᵥ x) = c * hyperbolicForm I F x := by
    apply ha
    rw [hg, map_mul, hc]
  have hc0 : c ≠ 0 := by
    intro ec
    have H := hq (g.inv *ᵥ v)
    rw [Matrix.mulVec_mulVec, g.val_inv, Matrix.one_mulVec, hv, ec, zero_mul] at H
    exact one_ne_zero H
  exact ⟨Units.mk0 c hc0, hq⟩

open scoped Algebra.TensorProduct

set_option maxHeartbeats 950000 in
private theorem relativeInner_projectiveMatrix {G : AffineAlgebraicGroup k}
    {Q : AdjointQuotient G} {O} (E : ExactSequence G Q O)
    (q : (groupSections Q.quotient.val).obj (op (fieldTest k K)))
    (C : SplitSpinVectorImage k I) (e : C.spin.val ≅ G.val)
    (hRank : 4 ≤ Fintype.card I) [Nonempty I] :
    ∃ (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ),
      (∀ x, hyperbolicForm I K (g.val *ᵥ x) = (c : K) * hyperbolicForm I K x) ∧
      ∀ (T : TestAlgebra k) (a : CommAlgCat.of k K ⟶ T) (x : Points G.val.X T),
        (referenceVectorUnit C e T (relativeApply
          (show RelativeAut G.val (fieldTest k K) from E.inner.app (op (fieldTest k K)) q)
          a x)).val =
          conjugate (Matrix.GeneralLinearGroup.map a.hom g) (referenceVectorUnit C e T x).val := by
  let u : RelativeAut G.val (fieldTest k K) := E.inner.app (op (fieldTest k K)) q
  obtain ⟨R, a, gR, ha, hq, hLocal⟩ := relativeInner_vectorLocal E q C e
  let : Algebra K R := a.hom.toRingHom.toAlgebra
  let : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq' a.hom.comp_algebraMap.symm
  have : Nontrivial R := ha.nontrivial
  let L : R →ₐ[K] R ⊗[K] R := Algebra.TensorProduct.includeLeft
  let H : R →ₐ[K] R ⊗[K] R := Algebra.TensorProduct.includeRight
  let W := CommAlgCat.of k (R ⊗[K] R)
  let l : R ⟶ W := CommAlgCat.ofHom (L.restrictScalars k)
  let r : R ⟶ W := CommAlgCat.ofHom (H.restrictScalars k)
  have hlr : a ≫ l = a ≫ r := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact (L.commutes x).trans (H.commutes x).symm
  have hov : matrixInner (Matrix.GeneralLinearGroup.map L.toRingHom gR) =
      matrixInner (Matrix.GeneralLinearGroup.map H.toRingHom gR) := by
    apply vectorMatrixConjugation_unique hRank C W
    intro T b x
    let y := x ≫ e.hom.hom.hom
    have hyes := referenceVectorUnit_compare C e T x
    have h₁ := hLocal T (l ≫ b) y
    have h₂ := hLocal T (r ≫ b) y
    change (referenceVectorUnit C e T (relativeApply u (a ≫ l ≫ b) y)).val =
      conjugate (Matrix.GeneralLinearGroup.map (l ≫ b).hom gR) _ at h₁
    change (referenceVectorUnit C e T (relativeApply u (a ≫ r ≫ b) y)).val =
      conjugate (Matrix.GeneralLinearGroup.map (r ≫ b).hom gR) _ at h₂
    rw [← Category.assoc a l b, hlr, Category.assoc] at h₁
    rw [hyes] at h₁ h₂
    exact h₁.symm.trans h₂
  obtain ⟨g, hg⟩ := projectiveMatrix_descent (k := K) R (I ⊕ I) gR hov
  obtain ⟨c, hc⟩ := similitude_of_projective_isometry a.hom.toRingHom ha g gR hq hg
  refine ⟨g, c, hc, ?_⟩
  intro T b x
  let : Algebra K T := b.hom.toRingHom.toAlgebra
  let : IsScalarTower k K T := IsScalarTower.of_algebraMap_eq' b.hom.comp_algebraMap.symm
  let U := CommAlgCat.of k (R ⊗[K] T)
  let i : R →ₐ[K] U := Algebra.TensorProduct.includeLeft
  let j : T →ₐ[K] U := Algebra.TensorProduct.includeRight
  let i' : R ⟶ U := CommAlgCat.ofHom (i.restrictScalars k)
  let j' : T ⟶ U := CommAlgCat.ofHom (j.restrictScalars k)
  have hij : b ≫ j' = a ≫ i' := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact (j.commutes x).trans (i.commutes x).symm
  have hj : Function.Injective j'.hom :=
    Algebra.TensorProduct.includeRight_injective (B := T) ha
  apply matrix_map_injective j'.hom.toRingHom hj
  have hl (y : Points G.val.X T) :
      ((referenceVectorUnit C e T y).val.map j'.hom.toRingHom) =
        (referenceVectorUnit C e U (mapPoints j' y)).val :=
    (congrArg Units.val (referenceVectorUnit_map C e j' y)).symm
  change (referenceVectorUnit C e T (relativeApply u b x)).val.map j'.hom.toRingHom =
    (conjugate (Matrix.GeneralLinearGroup.map b.hom g) (referenceVectorUnit C e T x).val).map
      j'.hom.toRingHom
  have hsub := hLocal U i' (mapPoints j' x)
  change (referenceVectorUnit C e U (relativeApply u (a ≫ i') (mapPoints j' x))).val =
    conjugate (Matrix.GeneralLinearGroup.map i'.hom gR)
      (referenceVectorUnit C e U (mapPoints j' x)).val at hsub
  rw [hl, relativeApply_map, hij, hsub, conjugate_map, hl]
  have hUp : matrixInner (Matrix.GeneralLinearGroup.map i'.hom.toRingHom gR) =
      matrixInner (Matrix.GeneralLinearGroup.map j'.hom.toRingHom (Matrix.GeneralLinearGroup.map b.hom.toRingHom g)) := by
    apply matrixInner_ext_ground i'.hom.toRingHom
    intro X
    change conjugate (Matrix.GeneralLinearGroup.map i'.hom.toRingHom gR) (X.map i'.hom.toRingHom) =
      conjugate (Matrix.GeneralLinearGroup.map j'.hom.toRingHom (Matrix.GeneralLinearGroup.map b.hom.toRingHom g)) (X.map i'.hom.toRingHom)
    have hcon := congrArg (fun M : Matrix (I ⊕ I) (I ⊕ I) R => M.map i'.hom.toRingHom)
      (DFunLike.congr_fun hg.symm X)
    change (conjugate gR X).map i'.hom.toRingHom =
      (conjugate (Matrix.GeneralLinearGroup.map a.hom.toRingHom g) X).map i'.hom.toRingHom at hcon
    rw [conjugate_map, conjugate_map] at hcon
    have hcomp :
        Matrix.GeneralLinearGroup.map i'.hom.toRingHom (Matrix.GeneralLinearGroup.map a.hom.toRingHom g) =
          Matrix.GeneralLinearGroup.map j'.hom.toRingHom (Matrix.GeneralLinearGroup.map b.hom.toRingHom g) := by
      have h := congrArg (fun f : CommAlgCat.of k K ⟶ U =>
        Matrix.GeneralLinearGroup.map f.hom.toRingHom g) hij.symm
      exact h
    rw [hcomp] at hcon
    exact hcon
  exact DFunLike.congr_fun hUp _

end

end RelativeInnerSimilitude



section VectorMatrixCocycle

open AlgebraicGeometry Matrix CategoryTheory Opposite
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.AutomorphismSequence (RelativeAut relativePoints restrictIso restrictAut)
open Specs.RelativeFormComparison (fieldTest fieldMap transportedAut IsInduced)
open RM03.Brauer.SemilinearDescent (AlgebraAction)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]

private abbrev galoisAlgebraMap (σ : Gal(K/k)) : CommAlgCat.of k K ⟶ CommAlgCat.of k K :=
  CommAlgCat.ofHom σ.toAlgHom

private theorem transportedAut_one {G H : GroupScheme k}
    (r : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K)) :
    transportedAut k K r 1 = 1 := by
  apply Aut.ext
  apply Iso.ext
  change (restrictIso (fieldMap k K 1) r).hom ≫ r.inv = 𝟙 _
  rw [Specs.RelativeFormComparison.fieldMap_one]
  have h : (restrictIso (𝟙 (fieldTest k K)) r).hom = r.hom := by
    ext U x
    rfl
  rw [h, r.hom_inv_id]

private theorem transportedAut_mul {G H : GroupScheme k}
    (r : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K)) (σ τ : Gal(K/k)) :
    transportedAut k K r (σ * τ) =
      transportedAut k K r σ * restrictAut (fieldMap k K σ) (transportedAut k K r τ) := by
  let f := fieldMap k K σ
  let g := fieldMap k K τ
  apply Aut.ext
  apply Iso.ext
  change (restrictIso (fieldMap k K (σ * τ)) r).hom ≫ r.inv =
    ((restrictIso f (restrictIso g r)).hom ≫ (restrictIso f r).inv) ≫
      (restrictIso f r).hom ≫ r.inv
  have h : (restrictIso (fieldMap k K (σ * τ)) r).hom =
      (restrictIso f (restrictIso g r)).hom := by
    rw [Specs.RelativeFormComparison.fieldMap_mul]
    ext U x
    rfl
  rw [h, Category.assoc, Iso.inv_hom_id_assoc]

private theorem relativeApply_restrictGalois {G : GroupScheme k}
    (u : RelativeAut G (fieldTest k K)) (σ : Gal(K/k))
    (T : TestAlgebra k) (a : CommAlgCat.of k K ⟶ T) (x : Points G.X T) :
    relativeApply (restrictAut (fieldMap k K σ) u) a x =
      relativeApply u (galoisAlgebraMap σ ≫ a) x := by
  have he : (fieldObject a).hom ≫ fieldMap k K σ = (fieldObject (galoisAlgebraMap σ ≫ a)).hom := by
    change (testSpec k).map a.op ≫ (testSpec k).map (galoisAlgebraMap σ).op =
      (testSpec k).map (galoisAlgebraMap σ ≫ a).op
    rw [op_comp, Functor.map_comp]
  let ev (b : (testSpec k).obj (op T) ⟶ fieldTest k K) : Points G.X T → Points G.X T :=
    fun z => (u.asIso.hom.app (op (Over.mk b))).hom z
  exact congrFun (congrArg ev he) x

private theorem relativeApply_mul {G : GroupScheme k} (u v : RelativeAut G (fieldTest k K))
    (T : TestAlgebra k) (a : CommAlgCat.of k K ⟶ T) (x : Points G.X T) :
    relativeApply (u * v) a x = relativeApply u a (relativeApply v a x) := rfl

private theorem matrix_action_of_projectiveCocycle
    (g : Gal(K/k) → (Matrix (I ⊕ I) (I ⊕ I) K)ˣ)
    (h₁ : matrixInner (g 1) = 1)
    (hμ : ∀ σ τ, matrixInner (g (σ * τ)) =
      matrixInner (g σ * Matrix.GeneralLinearGroup.map σ.toRingHom (g τ))) :
    ∃ ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K),
      ∀ σ X, ρ.act σ X = conjugate (g σ) (X.map σ) := by
  let m (σ : Gal(K/k)) : Matrix (I ⊕ I) (I ⊕ I) K ≃+ Matrix (I ⊕ I) (I ⊕ I) K :=
    { toFun := fun X => X.map σ
      invFun := fun X => X.map σ.symm
      left_inv X := by ext i j; exact σ.symm_apply_apply (X i j)
      right_inv X := by ext i j; exact σ.apply_symm_apply (X i j)
      map_add' X Y := by ext i j; exact map_add σ (X i j) (Y i j) }
  let t (σ : Gal(K/k)) := (m σ).trans (matrixInner (g σ)).toRingEquiv.toAddEquiv
  refine ⟨{ act := t
            one_act := ?_
            mul_act := ?_
            map_smul := ?_
            map_one := ?_
            map_mul := ?_ }, fun _ _ => rfl⟩
  · intro X
    change matrixInner (g 1) (m 1 X) = X
    rw [h₁]
    rfl
  · intro σ τ X
    change matrixInner (g (σ * τ)) (X.map (σ * τ).toRingHom) =
      conjugate (g σ) ((conjugate (g τ) (X.map τ.toRingHom)).map σ.toRingHom)
    rw [hμ, matrixInner_mul, conjugate_map]
    rfl
  · intro σ a X
    change conjugate (g σ) ((a • X).map σ.toRingHom) =
      σ a • conjugate (g σ) (X.map σ.toRingHom)
    rw [show (a • X).map σ.toRingHom = σ a • X.map σ.toRingHom from by
      ext i j; exact map_mul σ a (X i j)]
    exact (matrixInner (g σ)).toLinearMap.map_smul (σ a) _
  · intro σ
    change matrixInner (g σ) ((1 : Matrix (I ⊕ I) (I ⊕ I) K).map σ.toRingHom) = 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), map_one]
  · intro σ X Y
    change matrixInner (g σ) ((X * Y).map σ.toRingHom) =
      matrixInner (g σ) (X.map σ.toRingHom) * matrixInner (g σ) (Y.map σ.toRingHom)
    rw [Matrix.map_mul, map_mul]

set_option maxHeartbeats 900000 in
private theorem vectorAction_projectiveCocycle {G H : AffineAlgebraicGroup k}
    (C : SplitSpinVectorImage k I) (e : C.spin.val ≅ G.val)
    (r : relativePoints G.val (fieldTest k K) ≅ relativePoints H.val (fieldTest k K))
    (hRank : 4 ≤ Fintype.card I)
    (g : Gal(K/k) → (Matrix (I ⊕ I) (I ⊕ I) K)ˣ)
    (h : ∀ σ (T : TestAlgebra k) (a : CommAlgCat.of k K ⟶ T) (x : Points G.val.X T),
      (referenceVectorUnit C e T (relativeApply (transportedAut k K r σ) a x)).val =
        conjugate (Matrix.GeneralLinearGroup.map a.hom (g σ)) (referenceVectorUnit C e T x).val) :
    ∃ ρ : AlgebraAction k K (Matrix (I ⊕ I) (I ⊕ I) K),
      ∀ σ X, ρ.act σ X = conjugate (g σ) (X.map σ) := by
  apply matrix_action_of_projectiveCocycle g
  · have hOne : matrixInner (1 : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) = 1 := by
      apply AlgEquiv.ext
      intro X
      change conjugate 1 X = X
      simp [conjugate]
    rw [← hOne]
    apply vectorMatrixConjugation_unique hRank C (CommAlgCat.of k K)
    intro T a x
    have hx := h 1 T a (x ≫ e.hom.hom.hom)
    rw [transportedAut_one] at hx
    change (referenceVectorUnit C e T (x ≫ e.hom.hom.hom)).val =
      conjugate (Matrix.GeneralLinearGroup.map a.hom (g 1)) _ at hx
    rw [referenceVectorUnit_compare] at hx
    rw [map_one]
    simpa [conjugate] using hx.symm
  · intro σ τ
    apply vectorMatrixConjugation_unique hRank C (CommAlgCat.of k K)
    intro T a x
    let y := x ≫ e.hom.hom.hom
    have he := h (σ * τ) T a y
    rw [transportedAut_mul, relativeApply_mul, relativeApply_restrictGalois,
      h σ, h τ, referenceVectorUnit_compare] at he
    rw [map_mul]
    have hm : Matrix.GeneralLinearGroup.map (galoisAlgebraMap σ ≫ a).hom.toRingHom (g τ) =
      Matrix.GeneralLinearGroup.map a.hom.toRingHom (Matrix.GeneralLinearGroup.map σ.toRingHom (g τ)) := rfl
    change conjugate (Matrix.GeneralLinearGroup.map a.hom.toRingHom (g σ))
      (conjugate (Matrix.GeneralLinearGroup.map (galoisAlgebraMap σ ≫ a).hom.toRingHom (g τ)) _) =
        conjugate (Matrix.GeneralLinearGroup.map a.hom.toRingHom (g (σ * τ))) _ at he
    rw [hm] at he
    exact he.symm.trans (DFunLike.congr_fun (matrixInner_mul T _ _).symm _)

end

end VectorMatrixCocycle



section SplitSpinFieldExtension

open AlgebraicGeometry CategoryTheory Matrix
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open _root_.LinearAlgebraicGroups.Albert
open _root_.LinearAlgebraicGroups.Albert.SplitSpinSpecification (integralForm hyperbolicBasis PairIndex)
open private groupBaseChangePointIso from LinearAlgebraicGroups.Affine.RationalRepresentations

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K I : Type u} [Field k] [Field K] [Algebra k K]
variable [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]

private def affineGroupIsoOfPointIso {F : Type u} [Field F] (X Y : AffineAlgebraicGroup F)
    (r : (groupPointsFunctor F).obj X.val ≅ (groupPointsFunctor F).obj Y.val) : X.val ≅ Y.val := by
  let j := AffineAlgebraicGroup.groupHomEquiv X Y
  let j' := AffineAlgebraicGroup.groupHomEquiv Y X
  refine ⟨j.symm r.hom, j'.symm r.inv, ?_, ?_⟩
  · apply (AffineAlgebraicGroup.groupHomEquiv X X).injective
    change (groupPointsFunctor F).map (j.symm r.hom ≫ j'.symm r.inv) = (groupPointsFunctor F).map (𝟙 _)
    rw [Functor.map_comp, (groupPointsFunctor F).map_id X.val]
    change j (j.symm r.hom) ≫ j' (j'.symm r.inv) = _
    rw [j.apply_symm_apply, j'.apply_symm_apply, Iso.hom_inv_id]
  · apply (AffineAlgebraicGroup.groupHomEquiv Y Y).injective
    change (groupPointsFunctor F).map (j'.symm r.inv ≫ j.symm r.hom) = (groupPointsFunctor F).map (𝟙 _)
    rw [Functor.map_comp, (groupPointsFunctor F).map_id Y.val]
    change j' (j'.symm r.inv) ≫ j (j.symm r.hom) = _
    rw [j.apply_symm_apply, j'.apply_symm_apply, Iso.inv_hom_id]

private theorem affineGroupIsoOfPointIso_apply {F : Type u} [Field F] (X Y : AffineAlgebraicGroup F)
    (r : (groupPointsFunctor F).obj X.val ≅ (groupPointsFunctor F).obj Y.val)
    (R : TestAlgebra F) (a : Points X.val.X R) :
    a ≫ (affineGroupIsoOfPointIso X Y r).hom.hom.hom = r.hom.app R a := by
  have h := (AffineAlgebraicGroup.groupHomEquiv X Y).apply_symm_apply r.hom
  change (groupPointsFunctor F).map (affineGroupIsoOfPointIso X Y r).hom = r.hom at h
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h R) a

private def integralSpinPointMulEquiv {m : ℕ} (P : SplitSpinVectorImage k I)
    (d : Fin m ≃ I) (R : TestAlgebra k) :
    Points P.spin.val.X R ≃* SpinFunctor.Spin (integralForm m) R (hyperbolicBasis ℤ m) where
  toEquiv := integralPointEquiv P d R
  map_mul' x y := by
    apply Subtype.ext
    change integralPointUnit P d R (x * y) = integralPointUnit P d R x * integralPointUnit P d R y
    unfold integralPointUnit
    rw [map_mul, map_mul]

private def splitSpinScalarPointEquiv {m : ℕ} (P : SplitSpinVectorImage k I)
    (Q : SplitSpinVectorImage K I) (d : Fin m ≃ I) (S : TestAlgebra K) :
    Points ((groupBaseChange k K).obj P.spin.val).X S ≃* Points Q.spin.val.X S :=
  (baseChangePointGroupEquiv K P.spin.val S).trans
    ((integralSpinPointMulEquiv P d ((restrictTestAlgebra k K).obj S)).trans
      (integralSpinPointMulEquiv Q d S).symm)

private theorem splitSpinScalarPointUnit {m : ℕ} (P : SplitSpinVectorImage k I)
    (Q : SplitSpinVectorImage K I) (d : Fin m ≃ I) (U : TestAlgebra K)
    (x : Points ((groupBaseChange k K).obj P.spin.val).X U) :
    integralPointUnit Q d U (splitSpinScalarPointEquiv P Q d U x) =
      integralPointUnit P d ((restrictTestAlgebra k K).obj U)
        (baseChangePoint k K P.spin.val.X U x) := by
  exact congrArg Subtype.val ((integralSpinPointMulEquiv Q d U).apply_symm_apply _)

set_option maxHeartbeats 800000 in
private def splitSpinScalarPointIso {m : ℕ} (P : SplitSpinVectorImage k I)
    (Q : SplitSpinVectorImage K I) (d : Fin m ≃ I) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj P.spin.val) ≅
      (groupPointsFunctor K).obj Q.spin.val :=
  NatIso.ofComponents (fun S => (splitSpinScalarPointEquiv P Q d S).toGrpIso) (by
    intro S T f
    apply GrpCat.ext
    intro a
    apply (integralSpinPointMulEquiv Q d T).injective
    apply Subtype.ext
    change integralPointUnit Q d T (splitSpinScalarPointEquiv P Q d T (mapPoints f a)) =
      integralPointUnit Q d T (mapPoints f (splitSpinScalarPointEquiv P Q d S a))
    rw [splitSpinScalarPointUnit, integralPointUnit_natural, splitSpinScalarPointUnit,
      baseChangePointsNaturality k K P.spin.val.X f a]
    all_goals exact integralPointUnit_natural P d ((restrictTestAlgebra k K).map f) _)

set_option maxRecDepth 2000 in
set_option maxHeartbeats 950000 in
private theorem splitSpinScalarComparison {m : ℕ} (P : SplitSpinVectorImage k I)
    (Q : SplitSpinVectorImage K I) (d : Fin (m + 1) ≃ I) :
    ∃ e : (groupBaseChange k K).obj P.spin.val ≅ Q.spin.val,
      ∀ (S : TestAlgebra K) (x : Points ((groupBaseChange k K).obj P.spin.val).X S),
        let R := (restrictTestAlgebra k K).obj S
        integralPointUnit Q d S (x ≫ e.hom.hom.hom) =
          integralPointUnit P d R (baseChangePoint k K P.spin.val.X S x) ∧
        spinVectorMatrix Q S (x ≫ e.hom.hom.hom) =
          spinVectorMatrix P R (baseChangePoint k K P.spin.val.X S x) := by
  let X := Specs.Unipotent.baseChangedAlgebraicGroup K P.spin
  let e := affineGroupIsoOfPointIso X Q.spin (splitSpinScalarPointIso P Q d)
  refine ⟨e, ?_⟩
  intro S x
  let R := (restrictTestAlgebra k K).obj S
  let y : Points P.spin.val.X R := baseChangePoint k K P.spin.val.X S x
  let z : Points Q.spin.val.X S := x ≫ e.hom.hom.hom
  have he : z = splitSpinScalarPointEquiv P Q d S x :=
    affineGroupIsoOfPointIso_apply X Q.spin _ S x
  have hu : integralPointUnit Q d S z = integralPointUnit P d R y := by
    rw [he]
    exact splitSpinScalarPointUnit P Q d S x
  refine ⟨hu, ?_⟩
  let a := integralPointUnit P d R y
  let D : Matrix (PairIndex (m + 1)) (PairIndex (m + 1)) R ≃ Matrix (I ⊕ I) (I ⊕ I) R :=
    Matrix.reindex (d.sumCongr d) (d.sumCongr d)
  let M := D.symm (spinVectorMatrix P R y)
  have hM : SplitSpinSpecification.HasActionMatrix (m + 1) a M := by
    apply (vectorMatchesIntegralMatrix P d R y a (integralPointUnit_formula P d R y).symm M).mpr
    exact (D.apply_symm_apply _).symm
  have hN := (vectorMatchesIntegralMatrix Q d S z (integralPointUnit Q d S z)
    (integralPointUnit_formula Q d S z).symm M).mp (hu.symm ▸ hM)
  exact hN.trans (D.apply_symm_apply _)

end

end SplitSpinFieldExtension



section SplitScalarPoints

open AlgebraicGeometry Matrix CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open _root_.LinearAlgebraicGroups.Albert
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification (ScalarClifford coefficientMap)
open _root_.LinearAlgebraicGroups.Albert.SplitSpinSpecification (integralForm)
open private scalar_tensor_injective from LinearAlgebraicGroups.Albert.SpinFunctor

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]

private theorem splitKernelPoint_natural (P : SplitSpinVectorImage k I)
    {R S : TestAlgebra k} (f : R ⟶ S) (a : Points P.kernel.group.X R) :
    (P.kernelPoints S (mapPoints f a)).val.val = f.hom (P.kernelPoints R a).val.val := by
  let q := hyperbolicForm I k
  apply scalar_tensor_injective q S (Pi.basisFun k (I ⊕ I))
  rw [← P.scalar, show mapPoints f a ≫ P.kernel.inclusion.hom.hom =
      mapPoints f (a ≫ P.kernel.inclusion.hom.hom) from Category.assoc _ _ _,
    P.spinRepresents.2]
  change coefficientMap q R f.hom ((P.spinPoints R (a ≫ P.kernel.inclusion.hom.hom)).val) = _
  rw [P.scalar]
  rfl

private theorem integralPointUnit_scalar {m : ℕ} (P : SplitSpinVectorImage k I) (d : Fin m ≃ I)
    (R : TestAlgebra k) (a : Points P.kernel.group.X R) :
    (integralPointUnit P d R (a ≫ P.kernel.inclusion.hom.hom)).val =
      algebraMap R (SplitSpinSpecification.ScalarClifford m R) (P.kernelPoints R a).val.val := by
  apply (integralCliffordCoordinates k I m d R).injective
  rw [(integralCliffordCoordinates k I m d R).commutes, ← P.scalar]
  exact congrArg Units.val (integralPointUnit_formula P d R _)

end

end SplitScalarPoints



section RelativeSimilitudes

open Matrix AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open Specs.AutomorphismSequence (ExactSequence AdjointQuotient RelativeAut groupSections scalarAut relativePoints)
open Specs.RelativeFormComparison (fieldTest transportedAut)
open Specs.Pinning (PinnedGroup AttachedDatum)
open Specs.QuasiSplitInnerForms (outerHom)
open RM03.Brauer.SemilinearDescent (AlgebraAction)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]

private theorem quadraticSimilarity_mul [Nonempty I]
    (g h : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c d : Kˣ)
    (hg : ∀ x, hyperbolicForm I K (g.val *ᵥ x) = (c : K) * hyperbolicForm I K x)
    (hh : ∀ x, hyperbolicForm I K (h.val *ᵥ x) = (d : K) * hyperbolicForm I K x) :
    ∀ x, hyperbolicForm I K ((g * h).val *ᵥ x) = ((c * d : Kˣ) : K) * hyperbolicForm I K x := by
  intro x
  change hyperbolicForm I K ((g.val * h.val) *ᵥ x) = ((c : K) * d) * hyperbolicForm I K x
  rw [← Matrix.mulVec_mulVec, hg, hh, mul_assoc]

private theorem referenceIsometry_baseChange (C : SplitSpinVectorImage k I)
    (g : (Matrix (I ⊕ I) (I ⊕ I) k)ˣ)
    (hg : ∀ v, hyperbolicForm I k (g.val *ᵥ v) = hyperbolicForm I k v) :
    ∀ v, hyperbolicForm I K ((Matrix.GeneralLinearGroup.map (algebraMap k K) g).val *ᵥ v) =
      hyperbolicForm I K v := by
  let k₀ := CommAlgCat.of k k
  let K₀ := CommAlgCat.of k K
  let f : k₀ ⟶ K₀ := CommAlgCat.ofHom (Algebra.ofId k K)
  let t : orthogonalMatrices I k := ⟨g, hg⟩
  let x := (C.orthogonal.points k₀).symm t
  have h : (C.orthogonal.points K₀ (mapPoints f x)).val.val =
      (Matrix.GeneralLinearGroup.map (algebraMap k K) g).val := by
    have hm := C.orthogonal.naturality f x
    change (C.orthogonal.points K₀ (mapPoints f x)).val.val =
      (C.orthogonal.points k₀ x).val.val.map f.hom at hm
    rw [hm]
    change ((C.orthogonal.points k₀) ((C.orthogonal.points k₀).symm t)).val.val.map f.hom = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [← h]
  exact (C.orthogonal.points K₀ (mapPoints f x)).property

private theorem relativeFactorMatrix {G : AffineAlgebraicGroup k}
    {Q : AdjointQuotient G} {O} (E : ExactSequence G Q O)
    (C : SplitSpinVectorImage k I) (e : C.spin.val ≅ G.val)
    (hRank : 4 ≤ Fintype.card I) [Nonempty I]
    (A : G.val ≅ G.val)
    (u : RelativeAut G.val (fieldTest k K))
    (a₀ : (Matrix (I ⊕ I) (I ⊕ I) k)ˣ)
    (h₀ : ∀ x, hyperbolicForm I k (a₀.val *ᵥ x) = hyperbolicForm I k x)
    (hA : ∀ (R : TestAlgebra k) (x : Points G.val.X R),
      (referenceVectorUnit C e R (x ≫ A.hom.hom.hom)).val =
        conjugate (Matrix.GeneralLinearGroup.map (algebraMap k R) a₀) (referenceVectorUnit C e R x).val)
    (hu : ∃ q : (groupSections Q.quotient.val).obj (op (fieldTest k K)),
      u = E.inner.app (op (fieldTest k K)) q ∨
      u = (show RelativeAut G.val (fieldTest k K) from E.inner.app (op (fieldTest k K)) q) *
        scalarAut (Aut.of A) (fieldTest k K)) :
    ∃ (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ),
      (∀ x, hyperbolicForm I K (g.val *ᵥ x) = (c : K) * hyperbolicForm I K x) ∧
      ∀ (R : TestAlgebra k) (a : CommAlgCat.of k K ⟶ R) (x : Points G.val.X R),
        (referenceVectorUnit C e R (relativeApply u a x)).val =
          conjugate (Matrix.GeneralLinearGroup.map a.hom g) (referenceVectorUnit C e R x).val := by
  obtain ⟨q, huv⟩ := hu
  obtain ⟨h, c, hc, hh⟩ := relativeInner_projectiveMatrix E q C e hRank
  rcases huv with rfl | rfl
  · exact ⟨h, c, hc, hh⟩
  let b := Matrix.GeneralLinearGroup.map (algebraMap k K) a₀
  refine ⟨h * b, c, ?_, ?_⟩
  · simpa only [mul_one] using
      quadraticSimilarity_mul h b c 1 hc
        (fun x => (referenceIsometry_baseChange (K := K) C a₀ h₀ x).trans (one_mul _).symm)
  intro R a x
  let v : RelativeAut G.val (fieldTest k K) := E.inner.app (op (fieldTest k K)) q
  change (referenceVectorUnit C e R (relativeApply (v * scalarAut (Aut.of A) (fieldTest k K)) a x)).val =
    conjugate (Matrix.GeneralLinearGroup.map a.hom (h * b)) _
  rw [relativeApply_mul]
  have hsc : relativeApply (scalarAut (Aut.of A) (fieldTest k K)) a x = x ≫ A.hom.hom.hom := rfl
  rw [hsc, hh R a, hA R x, map_mul]
  have hb : Matrix.GeneralLinearGroup.map a.hom.toRingHom b =
      Matrix.GeneralLinearGroup.map (algebraMap k R) a₀ := by
    apply Units.ext
    ext i j
    change a.hom (algebraMap k K (a₀.val i j)) = algebraMap k R (a₀.val i j)
    exact a.hom.commutes _
  change conjugate (Matrix.GeneralLinearGroup.map a.hom.toRingHom h)
    (conjugate (Matrix.GeneralLinearGroup.map (algebraMap k R) a₀) _) =
      conjugate (Matrix.GeneralLinearGroup.map a.hom.toRingHom h * Matrix.GeneralLinearGroup.map a.hom.toRingHom b) _
  rw [hb]
  exact DFunLike.congr_fun (matrixInner_mul R _ _).symm _

end

end RelativeSimilitudes



section SemilinearComparisonOnPoints

open Matrix AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.AutomorphismSequence (relativePoints restrictIso RelativeAut)
open Specs.RelativeFormComparison (fieldTest fieldMap transportedAut IsInduced)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private def structureAlgebraMap (S : TestAlgebra K) :
    CommAlgCat.of k K ⟶ (restrictTestAlgebra k K).obj S := by
  letI : Algebra k S := ((algebraMap K S).comp (algebraMap k K)).toAlgebra
  let f : K →ₐ[k] S := { toRingHom := algebraMap K S, commutes' := fun _ => rfl }
  exact CommAlgCat.ofHom f

private abbrev relativeComparisonApply {G H : GroupScheme k}
    (r : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    {R : TestAlgebra k} (a : CommAlgCat.of k K ⟶ R) :
    Points G.X R ≃* Points H.X R := (r.app (op (fieldObject a))).groupIsoToMulEquiv

private theorem relativeComparison_natural {G H : GroupScheme k}
    (r : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    {R T : TestAlgebra k} (a : CommAlgCat.of k K ⟶ R) (b : R ⟶ T) (x : Points G.X R) :
    mapPoints b (relativeComparisonApply r a x) =
      relativeComparisonApply r (a ≫ b) (mapPoints b x) := by
  have h := ConcreteCategory.congr_hom (r.hom.naturality (fieldObject_map a b).op) x
  change relativeComparisonApply r (a ≫ b) (mapPoints b x) =
    mapPoints b (relativeComparisonApply r a x) at h
  exact h.symm

private theorem relativeComparison_semilinear {G H : GroupScheme k}
    (r : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    {R : TestAlgebra k} (a : CommAlgCat.of k K ⟶ R)
    (f : R ⟶ R) (σ : Gal(K/k)) (hf : a ≫ f = galoisAlgebraMap σ ≫ a)
    (x : Points G.X R) :
    relativeComparisonApply r a (relativeApply (transportedAut k K r σ) a (mapPoints f x)) =
      mapPoints f (relativeComparisonApply r a x) := by
  rw [relativeComparison_natural r a f x, hf]
  have he : (fieldObject a).hom ≫ fieldMap k K σ =
      (fieldObject (galoisAlgebraMap σ ≫ a)).hom := by
    change (testSpec k).map a.op ≫ (testSpec k).map (galoisAlgebraMap σ).op =
      (testSpec k).map (galoisAlgebraMap σ ≫ a).op
    rw [op_comp, Functor.map_comp]
  let ev (b : (testSpec k).obj (op R) ⟶ fieldTest k K) :
      Points G.X R → Points H.X R :=
    fun z => (r.hom.app (op (Over.mk b))).hom z
  have h : (relativeComparisonApply r a).symm
      (ev ((fieldObject a).hom ≫ fieldMap k K σ) (mapPoints f x)) =
      relativeApply (transportedAut k K r σ) a (mapPoints f x) := rfl
  rw [← h, MulEquiv.apply_symm_apply]
  exact congrFun (congrArg ev he) _

private theorem relativeComparison_baseChange {G H : GroupScheme k}
    (e : (groupBaseChange k K).obj G ≅ (groupBaseChange k K).obj H)
    (r : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    (hr : IsInduced k K e r)
    (S : TestAlgebra K) (x : Points ((groupBaseChange k K).obj G).X S) :
    relativeComparisonApply r (structureAlgebraMap S) (baseChangePoint k K G.X S x) =
      baseChangePoint k K H.X S (x ≫ e.hom.hom.hom) := by
  let a := structureAlgebraMap (k := k) S
  let U := fieldObject a
  let z := baseChangePoint k K G.X S x
  have h := hr U z
  apply Over.OverMorphism.ext
  change (relativeComparisonApply r a z).left =
    (x.left ≫ e.hom.hom.hom.left) ≫ pullback.fst H.X.hom (fieldSpecMap k K)
  rw [show (relativeComparisonApply r a z).left = _ from h]
  have he (h : z.left ≫ G.X.hom = U.hom.left ≫ (fieldTest k K).hom) :
      pullback.lift z.left U.hom.left h = x.left := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      rfl
    · rw [pullback.lift_snd]
      change ((testSpec K).obj (op S)).hom = x.left ≫ ((groupBaseChange k K).obj G).X.hom
      exact (Over.w x).symm
  rw [he, Category.assoc]

private theorem transportedAut_semilinear_points {G H : GroupScheme k}
    (e : (groupBaseChange k K).obj G ≅ (groupBaseChange k K).obj H)
    (r : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    (hr : IsInduced k K e r)
    (S : TestAlgebra K) (σ : Gal(K/k)) :
    let R := (restrictTestAlgebra k K).obj S
    ∀ (f : R ⟶ R), (∀ b, f.hom (algebraMap K S b) = algebraMap K S (σ b)) →
    ∀ (x y : Points ((groupBaseChange k K).obj H).X S),
      baseChangePoint k K H.X S y = mapPoints f (baseChangePoint k K H.X S x) →
      baseChangePoint k K G.X S (y ≫ e.inv.hom.hom) =
        relativeApply (transportedAut k K r σ) (structureAlgebraMap S)
          (mapPoints f (baseChangePoint k K G.X S (x ≫ e.inv.hom.hom))) := by
  intro R f hf x y hxy
  let a := structureAlgebraMap (k := k) S
  have ha : a ≫ f = galoisAlgebraMap σ ≫ a := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro b
    change f.hom (algebraMap K S b) = algebraMap K S (σ b)
    exact hf b
  have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
    congrArg (Grp.forget (SchemeOver K)).map e.inv_hom_id
  apply (relativeComparisonApply r a).injective
  rw [relativeComparison_baseChange e r hr, relativeComparison_semilinear r a f σ ha,
    relativeComparison_baseChange e r hr]
  simpa only [Category.assoc, he, Category.comp_id] using hxy

end

end SemilinearComparisonOnPoints



section RelativeScalarInvariance

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite Matrix
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.AutomorphismSequence (ExactSequence AdjointQuotient RelativeAut groupSections scalarAut)
open Specs.RelativeFormComparison (fieldTest)
open private liftOverTestAlgebra from LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]

private theorem pointsMap_injectiveOfAlgHom {X : SchemeOver k} (hX : IsAffine X.left)
    {R S : TestAlgebra k} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (mapPoints (X := X) f) := by
  let F := testSpec k
  let FF := algSpec.fullyFaithful (R := CommRingCat.of k)
  obtain ⟨B, ⟨b⟩⟩ := essImage_algSpec.mpr hX
  intro x y h
  let Fₓ := FF.preimage (x ≫ b.inv)
  let Fᵧ := FF.preimage (y ≫ b.inv)
  have hx : F.map Fₓ = x ≫ b.inv := FF.map_preimage _
  have hy : F.map Fᵧ = y ≫ b.inv := FF.map_preimage _
  have e : f.op ≫ Fₓ = f.op ≫ Fᵧ := by
    apply FF.map_injective
    change F.map (f.op ≫ Fₓ) = F.map (f.op ≫ Fᵧ)
    rw [Functor.map_comp, Functor.map_comp, hx, hy, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun z : Points X S => z ≫ b.inv) h
  have e' : Fₓ.unop = Fᵧ.unop := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro t
    apply hf
    have he := congrArg (fun a : B.unop ⟶ S => a.hom t) (congrArg Quiver.Hom.unop e)
    exact he
  apply (cancel_mono b.inv).mp
  rw [← hx, ← hy]
  exact congrArg (fun z : B.unop ⟶ R => F.map z.op) e'

private theorem referenceScalar_central (C : SplitSpinVectorImage k I)
    {G : AffineAlgebraicGroup k} (e : C.spin.val ≅ G.val)
    (R : TestAlgebra k) (x : Points C.kernel.group.X R) (y : Points G.val.X R) :
    Commute (x ≫ (C.kernel.inclusion ≫ e.hom).hom.hom) y := by
  let f := (((groupPointsFunctor k).map e.hom).app R).hom
  have he := (C.central R x (y ≫ e.inv.hom.hom)).map f
  have hi : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
    congrArg (Grp.forget (SchemeOver k)).map e.inv_hom_id
  change Commute ((x ≫ C.kernel.inclusion.hom.hom) ≫ e.hom.hom.hom)
    ((y ≫ e.inv.hom.hom) ≫ e.hom.hom.hom) at he
  simpa only [Grp.comp_hom_hom, Category.assoc, hi, Category.comp_id] using he

set_option maxHeartbeats 850000 in
private theorem relativeInner_fixesScalar {G : AffineAlgebraicGroup k}
    {Q : AdjointQuotient G} {O} (E : ExactSequence G Q O)
    (q : (groupSections Q.quotient.val).obj (op (fieldTest k K)))
    (C : SplitSpinVectorImage k I) (e : C.spin.val ≅ G.val)
    (R : TestAlgebra k) (a : CommAlgCat.of k K ⟶ R) (x : Points C.kernel.group.X R) :
    relativeApply (show RelativeAut G.val (fieldTest k K) from E.inner.app (op (fieldTest k K)) q) a
      (x ≫ (C.kernel.inclusion ≫ e.hom).hom.hom) = x ≫ (C.kernel.inclusion ≫ e.hom).hom.hom := by
  have : IsAffine G.val.X.left := G.property.1
  have : IsAffine Q.quotient.val.X.left := Q.quotient.property.1
  have : Flat Q.projection.hom.hom.left := Q.fppf.1
  have : Surjective Q.projection.hom.hom.left := Q.fppf.2.1
  have : LocallyOfFinitePresentation Q.projection.hom.hom.left := Q.fppf.2.2
  let y := x ≫ (C.kernel.inclusion ≫ e.hom).hom.hom
  obtain ⟨S, b, z, hb, _, hz⟩ := liftOverTestAlgebra Q.projection R (mapPoints a q.down)
  let u : RelativeAut G.val (fieldTest k K) := E.inner.app (op (fieldTest k K)) q
  have hh : z ≫ Q.projection.hom.hom = mapPoints (a ≫ b) q.down := by
    change z ≫ Q.projection.hom.hom = (testSpec k).map b.op ≫ (testSpec k).map a.op ≫ q.down at hz
    change z ≫ Q.projection.hom.hom = (testSpec k).map (a ≫ b).op ≫ q.down
    rw [op_comp, Functor.map_comp, Category.assoc]
    exact hz
  change relativeApply u a y = y
  apply pointsMap_injectiveOfAlgHom G.property.1 b hb.injective
  rw [relativeApply_map, relativeInnerApply E q (a ≫ b) z hh]
  have hc : Commute (mapPoints b y) z := referenceScalar_central C e S (mapPoints b x) z
  exact mul_inv_eq_iff_eq_mul.mpr hc.symm.eq

private theorem relativeFactor_fixesScalar {G : AffineAlgebraicGroup k}
    {Q : AdjointQuotient G} {O} (E : ExactSequence G Q O)
    (C : SplitSpinVectorImage k I) (e : C.spin.val ≅ G.val)
    (A : G.val ≅ G.val) (u : RelativeAut G.val (fieldTest k K))
    (hA : C.kernel.inclusion ≫ e.hom ≫ A.hom = C.kernel.inclusion ≫ e.hom)
    (hu : ∃ q : (groupSections Q.quotient.val).obj (op (fieldTest k K)),
      u = E.inner.app (op (fieldTest k K)) q ∨
      u = (show RelativeAut G.val (fieldTest k K) from E.inner.app (op (fieldTest k K)) q) *
        scalarAut (Aut.of A) (fieldTest k K)) :
    ∀ (R : TestAlgebra k) (a : CommAlgCat.of k K ⟶ R) (x : Points C.kernel.group.X R),
      relativeApply u a (x ≫ (C.kernel.inclusion ≫ e.hom).hom.hom) =
        x ≫ (C.kernel.inclusion ≫ e.hom).hom.hom := by
  intro R a x
  obtain ⟨q, rfl | rfl⟩ := hu
  · exact relativeInner_fixesScalar E q C e R a x
  rw [relativeApply_mul]
  have hh : relativeApply (scalarAut (Aut.of A) (fieldTest k K)) a
      (x ≫ (C.kernel.inclusion ≫ e.hom).hom.hom) = x ≫ (C.kernel.inclusion ≫ e.hom).hom.hom := by
    change (x ≫ (C.kernel.inclusion ≫ e.hom).hom.hom) ≫ A.hom.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, Category.assoc, hA]
  rw [hh]
  exact relativeInner_fixesScalar E q C e R a x

end

end RelativeScalarInvariance



section SplitKernelFieldExtension

open AlgebraicGeometry CategoryTheory Matrix
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Albert
open _root_.LinearAlgebraicGroups.Albert.SplitSpinSpecification (integralForm)
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K I : Type u} [Field k] [Field K] [Algebra k K]
variable [Fintype I] [DecidableEq I] [LinearOrder (I ⊕ I)]

private def splitScalarPointEquiv (P : SplitSpinVectorImage k I) (Q : SplitSpinVectorImage K I)
    (S : TestAlgebra K) :
    Points ((groupBaseChange k K).obj P.kernel.group).X S ≃* Points Q.kernel.group.X S :=
  (baseChangePointGroupEquiv K P.kernel.group S).trans
    ((P.kernelPoints ((restrictTestAlgebra k K).obj S)).trans (Q.kernelPoints S).symm)

omit [LinearOrder (I ⊕ I)] in
private theorem splitScalarPointEquiv_value (P : SplitSpinVectorImage k I) (Q : SplitSpinVectorImage K I)
    (S : TestAlgebra K) (x : Points ((groupBaseChange k K).obj P.kernel.group).X S) :
    (Q.kernelPoints S (splitScalarPointEquiv P Q S x)).val.val =
      (P.kernelPoints ((restrictTestAlgebra k K).obj S) (baseChangePoint k K P.kernel.group.X S x)).val.val :=
  congrArg (fun u : rootsOfUnity 2 S => u.val.val)
    ((Q.kernelPoints S).apply_symm_apply _)

private def splitScalarPointIso (P : SplitSpinVectorImage k I) (Q : SplitSpinVectorImage K I) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj P.kernel.group) ≅
      (groupPointsFunctor K).obj Q.kernel.group :=
  NatIso.ofComponents (fun S => (splitScalarPointEquiv P Q S).toGrpIso) (by
    intro S T f
    apply GrpCat.ext
    intro a
    apply (Q.kernelPoints T).injective
    apply rootsOfUnity.coe_injective
    change (Q.kernelPoints T (splitScalarPointEquiv P Q T (mapPoints f a))).val.val =
      (Q.kernelPoints T (mapPoints f (splitScalarPointEquiv P Q S a))).val.val
    rw [splitScalarPointEquiv_value, splitKernelPoint_natural, splitScalarPointEquiv_value,
      baseChangePointsNaturality k K P.kernel.group.X f a, splitKernelPoint_natural]
    rfl)

set_option maxHeartbeats 1200000 in
private theorem splitKernelFieldComparison {m : ℕ} (P : SplitSpinVectorImage k I)
    (Q : SplitSpinVectorImage K I) (d : Fin m ≃ I) (e : (groupBaseChange k K).obj P.spin.val ≅ Q.spin.val)
    (he : ∀ (S : TestAlgebra K) (x : Points ((groupBaseChange k K).obj P.spin.val).X S),
      integralPointUnit Q d S (x ≫ e.hom.hom.hom) =
        integralPointUnit P d ((restrictTestAlgebra k K).obj S) (baseChangePoint k K P.spin.val.X S x)) :
    ∃ c : (groupBaseChange k K).obj P.kernel.group ≅ Q.kernel.group,
      (groupBaseChange k K).map P.kernel.inclusion ≫ e.hom = c.hom ≫ Q.kernel.inclusion ∧
      ∀ (S : TestAlgebra K) (a : Points ((groupBaseChange k K).obj P.kernel.group).X S),
        (P.kernelPoints ((restrictTestAlgebra k K).obj S) (baseChangePoint k K P.kernel.group.X S a)).val.val =
          (Q.kernelPoints S (a ≫ c.hom.hom.hom)).val.val := by
  let X := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup (G := P.spin) P.kernel)
  let Y := closedSubgroupAlgebraicGroup (G := Q.spin) Q.kernel
  let c := affineGroupIsoOfPointIso X Y (splitScalarPointIso P Q)
  have hc (S : TestAlgebra K) (a : Points ((groupBaseChange k K).obj P.kernel.group).X S) :
      (Q.kernelPoints S (a ≫ c.hom.hom.hom)).val.val =
        (P.kernelPoints ((restrictTestAlgebra k K).obj S) (baseChangePoint k K P.kernel.group.X S a)).val.val := by
    rw [affineGroupIsoOfPointIso_apply X Y]
    exact splitScalarPointEquiv_value P Q S a
  refine ⟨c, ?_, fun S a => (hc S a).symm⟩
  apply Grp.hom_ext
  apply hom_ext_of_points X.property.1
  intro S a
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  apply integralPointUnit_injective Q d S
  apply Units.ext
  rw [he]
  have h := baseChangePointsSchemeNaturality k K P.kernel.inclusion.hom.hom S a
  change baseChangePoint k K P.spin.val.X S (a ≫ ((groupBaseChange k K).map P.kernel.inclusion).hom.hom) =
    baseChangePoint k K P.kernel.group.X S a ≫ P.kernel.inclusion.hom.hom at h
  rw [h, integralPointUnit_scalar, integralPointUnit_scalar, hc]

end

end SplitKernelFieldExtension



section InvariantSubgroupMapDescent

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.AutomorphismSequence (relativePoints)
open Specs.RelativeFormComparison (fieldTest transportedAut IsInduced)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private extendedTest extendedBase galoisTest galoisTest_semilinear
  from LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

set_option maxHeartbeats 1200000 in
private theorem descendInvariantSubgroupMap (P G W : AffineAlgebraicGroup k)
    (w : W.val ⟶ P.val)
    (j : (groupBaseChange k K).obj P.val ≅ (groupBaseChange k K).obj G.val)
    (r : relativePoints P.val (fieldTest k K) ≅ relativePoints G.val (fieldTest k K))
    (hr : IsInduced k K j r)
    (hfix : ∀ (σ : Gal(K/k)) (R : TestAlgebra k) (a : CommAlgCat.of k K ⟶ R) (x : Points W.val.X R),
      relativeApply (transportedAut k K r σ) a (x ≫ w.hom.hom) = x ≫ w.hom.hom) :
    ∃ d : W.val ⟶ G.val, (groupBaseChange k K).map d = (groupBaseChange k K).map w ≫ j.hom := by
  let U := restrictTestAlgebra k K
  let τ : U ⋙ (groupPointsFunctor k).obj W.val ⟶ U ⋙ (groupPointsFunctor k).obj G.val :=
    { app := fun S => GrpCat.ofHom <|
        (relativeComparisonApply r (structureAlgebraMap S)).toMonoidHom.comp
          (((groupPointsFunctor k).map w).app (U.obj S)).hom
      naturality := by
        intro S T f
        apply GrpCat.ext
        intro x
        have h : structureAlgebraMap (k := k) S ≫ U.map f = structureAlgebraMap T := by
          apply CommAlgCat.hom_ext
          apply AlgHom.ext
          intro b
          exact f.hom.commutes b
        change relativeComparisonApply r (structureAlgebraMap T) ((mapPoints (U.map f) x) ≫ w.hom.hom) =
          mapPoints (U.map f) (relativeComparisonApply r (structureAlgebraMap S) (x ≫ w.hom.hom))
        rw [relativeComparison_natural, h]
        rfl }
  have hτ (R : TestAlgebra k) (σ : Gal(K/k)) (x : Points W.val.X (extendedBase (K := K) R)) :
      τ.app (extendedTest R) (mapPoints (galoisTest R σ) x) =
        mapPoints (galoisTest R σ) (τ.app (extendedTest R) x) := by
    let a := structureAlgebraMap (k := k) (extendedTest (K := K) R)
    let f := galoisTest R σ
    have hf : a ≫ f = galoisAlgebraMap σ ≫ a := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro b
      exact galoisTest_semilinear R σ b
    change relativeComparisonApply r a ((mapPoints f x) ≫ w.hom.hom) =
      mapPoints f (relativeComparisonApply r a (x ≫ w.hom.hom))
    rw [← relativeComparison_semilinear r a f σ hf (x ≫ w.hom.hom)]
    have h : mapPoints f (x ≫ w.hom.hom) = (mapPoints f x) ≫ w.hom.hom := (Category.assoc ..).symm
    rw [h, hfix]
  obtain ⟨d, hd⟩ := descendGroupHomOnAlgebras W G τ hτ
  refine ⟨d, ?_⟩
  apply Grp.hom_ext
  apply hom_ext_of_points (baseChangedAlgebraicGroup K W).property.1
  intro S x
  apply (baseChangePointGroupEquiv K G.val S).injective
  let F := groupBaseChange k K
  let a := baseChangePoint k K W.val.X S x
  let y := x ≫ (F.map w).hom.hom
  have h₁ := baseChangePointsSchemeNaturality k K d.hom.hom S x
  have h₂ := baseChangePointsSchemeNaturality k K w.hom.hom S x
  have h₃ := relativeComparison_baseChange j r hr S y
  change baseChangePoint k K G.val.X S (x ≫ (F.map d).hom.hom) = a ≫ d.hom.hom at h₁
  change baseChangePoint k K P.val.X S y = a ≫ w.hom.hom at h₂
  change baseChangePoint k K G.val.X S (x ≫ (F.map d).hom.hom) =
    baseChangePoint k K G.val.X S (y ≫ j.hom.hom.hom)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app hd S) a
  change a ≫ d.hom.hom = relativeComparisonApply r (structureAlgebraMap S) (a ≫ w.hom.hom) at h
  rw [h₁, ← h₃, h₂, h]

end

end InvariantSubgroupMapDescent



section CentralKernelDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.CentralIsogenies (IsCentralIsogeny)
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private baseChangeMapPullback baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private fieldSpecMap_surjective comp_conjugateFamily from LinearAlgebraicGroups.Affine.Stabilizers
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private schemeKernel_exists from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private finite_of_finite_kernel from LinearAlgebraicGroups.Classification.CellHomomorphism
open private extendedTest extendedBase includeTest from LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]

private theorem scalarChange_reflectsSchemeIso {X Y : SchemeOver k} (f : X ⟶ Y)
    (hf : IsIso ((baseChange k K).map f).left) : IsIso f.left := by
  let : Surjective (fieldSpecMap k K) := fieldSpecMap_surjective K
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (pullback.fst Y.hom (fieldSpecMap k K)) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme) (baseChangeMapPullback (K := K) f) hq hf

private theorem scalarChange_faithful : (baseChange k K).Faithful := by
  let e := fieldSpecMap k K
  let : Surjective e := fieldSpecMap_surjective K
  let : Flat e := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    rw [Flat.SpecMap_iff]
    let : Algebra k K := (CommRingCat.ofHom (algebraMap k K)).hom.toAlgebra
    exact Module.Flat.of_free (R := k) (M := K)
  let : QuasiCompact e := inferInstanceAs (QuasiCompact (Spec.map _))
  exact inferInstanceAs ((Over.pullback e).Faithful)

private theorem scalarChange_one {X Y : GroupScheme k} :
    (baseChange k K).map (1 : X.X ⟶ Y.X) = (1 :
      ((groupBaseChange k K).obj X).X ⟶ ((groupBaseChange k K).obj Y).X) := by
  let F := baseChange k K
  let e := Functor.Monoidal.εIso F
  change F.map (toUnit X.X ≫ η[Y.X]) = toUnit (F.obj X.X) ≫ e.hom ≫ F.map η[Y.X]
  rw [Functor.map_comp, ← Category.assoc]
  congr 1
  apply (cancel_mono e.inv).mp
  rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  exact toUnit_unique _ _

private theorem splitKernelSquare_of_comparison {G H W : GroupScheme k}
    (p : G ⟶ H) (d : W ⟶ G) (P : SplitSpinVectorImage K I)
    (e : (groupBaseChange k K).obj G ≅ P.spin.val)
    (a : (groupBaseChange k K).obj H ≅ P.image.val)
    (c : (groupBaseChange k K).obj W ≅ P.kernel.group)
    (hp : (groupBaseChange k K).map p ≫ a.hom = e.hom ≫ P.projection)
    (hd : (groupBaseChange k K).map d ≫ e.hom = c.hom ≫ P.kernel.inclusion) :
    IsPullback ((groupBaseChange k K).map d).hom.hom (toUnit ((groupBaseChange k K).obj W).X)
      ((groupBaseChange k K).map p).hom.hom η[((groupBaseChange k K).obj H).X] := by
  let U := Grp.forget (SchemeOver K)
  have hk := P.isKernel
  refine hk.of_iso' (U.mapIso c) (U.mapIso e) (Iso.refl _) (U.mapIso a) ?_ ?_ ?_ ?_
  · exact (congrArg U.map hd).symm
  · simp only [Iso.refl_hom, Category.comp_id, comp_toUnit]
  · exact (congrArg U.map hp).symm
  · simp only [Iso.refl_hom, Category.id_comp]
    exact (IsMonHom.one_hom a.hom.hom.hom).symm

set_option maxHeartbeats 1000000 in
private theorem kernel_of_split_comparison {G H : AffineAlgebraicGroup k} {W : GroupScheme k}
    (p : G.val ⟶ H.val) (d : W ⟶ G.val)
    (hk : IsPullback ((groupBaseChange k K).map d).hom.hom (toUnit ((groupBaseChange k K).obj W).X)
      ((groupBaseChange k K).map p).hom.hom η[((groupBaseChange k K).obj H.val).X]) :
    ∃ h : IsClosedImmersion d.hom.hom.left, IsSchemeKernel p (⟨W, d, h⟩ : ClosedSubgroup G.val) := by
  let : IsAffine H.val.X.left := H.property.1
  obtain ⟨Z, hZ⟩ := schemeKernel_exists p
  let F := groupBaseChange k K
  let B := baseChange k K
  let : B.Faithful := scalarChange_faithful
  have hd : d.hom.hom ≫ p.hom.hom = (1 : W.X ⟶ H.val.X) := by
    apply B.map_injective
    rw [Functor.map_comp, scalarChange_one (K := K)]
    exact hk.w
  obtain ⟨t, ht⟩ := factor_group_through_subgroup Z d
    (hZ.lift d.hom.hom (toUnit W.X) hd) (hZ.lift_fst _ _ _)
  have hZK := baseChangeKernelSquare (K := K) p Z.inclusion hZ
  let e := hk.isoIsPullback _ _ hZK
  have htK : (F.map t).hom.hom ≫ (F.map Z.inclusion).hom.hom = (F.map d).hom.hom := by
    change (Grp.forget (SchemeOver K)).map (F.map t ≫ F.map Z.inclusion) = _
    rw [← F.map_comp, ht]
    rfl
  have hmono : Mono (F.map Z.inclusion).hom.hom := by
    have hz : IsClosedImmersion (F.map Z.inclusion).hom.hom.left :=
      MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) Z.inclusion.hom.hom).flip Z.isClosedImmersion
    exact Over.mono_of_mono_left _
  have he : (F.map t).hom.hom = e.hom := by
    apply (cancel_mono (F.map Z.inclusion).hom.hom).mp
    rw [htK]
    exact (hk.isoIsPullback_hom_fst _ _ hZK).symm
  have hf : IsIso ((F.map t).hom.hom.left) := by
    rw [he]
    infer_instance
  let : IsIso ((Over.forget (Spec (CommRingCat.of k))).map t.hom.hom) :=
    scalarChange_reflectsSchemeIso (K := K) t.hom.hom hf
  let : IsIso t.hom.hom := isIso_of_reflects_iso t.hom.hom (Over.forget _)
  let a := asIso t.hom.hom
  have hcl : IsClosedImmersion d.hom.hom.left := by
    have h : t.hom.hom.left ≫ Z.inclusion.hom.hom.left = d.hom.hom.left := by
      exact congrArg (fun f : W ⟶ G.val => f.hom.hom.left) ht
    rw [← h]
    exact MorphismProperty.comp_mem @IsClosedImmersion _ _ inferInstance Z.isClosedImmersion
  refine ⟨hcl, ?_⟩
  change IsPullback d.hom.hom (toUnit W.X) p.hom.hom η[H.val.X]
  apply hZ.of_iso' a (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    exact congrArg (fun w : W ⟶ G.val => w.hom.hom) ht
  · simp only [Iso.refl_hom, Category.comp_id, comp_toUnit]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

set_option maxHeartbeats 1200000 in
private theorem scalarCentral_of_split_comparison {G W : AffineAlgebraicGroup k}
    (d : W.val ⟶ G.val) (P : SplitSpinVectorImage K I)
    (e : (groupBaseChange k K).obj G.val ≅ P.spin.val)
    (c : (groupBaseChange k K).obj W.val ≅ P.kernel.group)
    (hd : (groupBaseChange k K).map d ≫ e.hom = c.hom ≫ P.kernel.inclusion) :
    Centralizes (𝟙 G.val) d.hom.hom := by
  let : IsAffine G.val.X.left := G.property.1
  let : IsAffine W.val.X.left := W.property.1
  have hA : IsAffine (G.val.X ⊗ W.val.X).left := by
    rw [Over.tensorObj_left]
    infer_instance
  change conjugateFamily (𝟙 G.val) d.hom.hom = _
  apply hom_ext_of_points hA
  intro R x
  rw [comp_conjugateFamily]
  simp only
  let u : Points W.val.X R := x ≫ snd _ _
  let v : Points G.val.X R := x ≫ fst _ _
  change (u ≫ d.hom.hom) * v * (u ≫ d.hom.hom)⁻¹ = v
  apply mul_inv_eq_iff_eq_mul.mpr
  let S := extendedTest (K := K) R
  let f := includeTest (K := K) R
  have hf : Function.Injective f.hom :=
    Algebra.TensorProduct.includeRight_injective (B := R) (algebraMap k K).injective
  apply pointsMap_injectiveOfAlgHom G.property.1 f hf
  let z := (baseChangePointGroupEquiv K W.val S).symm (mapPoints f u)
  let y := (baseChangePointGroupEquiv K G.val S).symm (mapPoints f v)
  let F := groupBaseChange k K
  have hZ : baseChangePoint k K W.val.X S z = mapPoints f u :=
    (baseChangePointGroupEquiv K W.val S).apply_symm_apply _
  have hY : baseChangePoint k K G.val.X S y = mapPoints f v :=
    (baseChangePointGroupEquiv K G.val S).apply_symm_apply _
  have h := P.central S (z ≫ c.hom.hom.hom) (y ≫ e.hom.hom.hom)
  have hD : z ≫ (F.map d).hom.hom ≫ e.hom.hom.hom =
      (z ≫ c.hom.hom.hom) ≫ P.kernel.inclusion.hom.hom := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun a : F.obj W.val ⟶ P.spin.val => z ≫ a.hom.hom) hd
  have h' : Commute (z ≫ (F.map d).hom.hom) y := by
    let a := (((groupPointsFunctor K).map e.hom).app S).hom
    have haa : Function.Injective a := ((groupPointsFunctor K).mapIso e).app S |>.groupIsoToMulEquiv.injective
    apply haa
    rw [map_mul, map_mul]
    change ((z ≫ (F.map d).hom.hom) ≫ e.hom.hom.hom) * (y ≫ e.hom.hom.hom) =
      (y ≫ e.hom.hom.hom) * ((z ≫ (F.map d).hom.hom) ≫ e.hom.hom.hom)
    rw [Category.assoc, hD]
    exact h.eq
  have ht := h'.map (baseChangePointGroupEquiv K G.val S).toMonoidHom
  have hm := baseChangePointsSchemeNaturality k K d.hom.hom S z
  change baseChangePoint k K G.val.X S (z ≫ (F.map d).hom.hom) =
    baseChangePoint k K W.val.X S z ≫ d.hom.hom at hm
  change Commute (baseChangePoint k K G.val.X S (z ≫ (F.map d).hom.hom))
    (baseChangePoint k K G.val.X S y) at ht
  rw [hm, hY, hZ] at ht
  change ((groupPointsFunctor k).obj G.val).map f ((u ≫ d.hom.hom) * v) =
    ((groupPointsFunctor k).obj G.val).map f (v * (u ≫ d.hom.hom))
  rw [map_mul, map_mul]
  exact ht.eq

set_option maxHeartbeats 650000 in
private theorem descendedCentralKernel {G H W : AffineAlgebraicGroup k}
    (p : G.val ⟶ H.val) (d : W.val ⟶ G.val)
    [IsFinite W.val.X.hom] [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [LocallyOfFiniteType p.hom.hom.left] [IsAffineHom p.hom.hom.left]
    (P : SplitSpinVectorImage K I)
    (e : (groupBaseChange k K).obj G.val ≅ P.spin.val)
    (a : (groupBaseChange k K).obj H.val ≅ P.image.val)
    (c : (groupBaseChange k K).obj W.val ≅ P.kernel.group)
    (hp : (groupBaseChange k K).map p ≫ a.hom = e.hom ≫ P.projection)
    (hd : (groupBaseChange k K).map d ≫ e.hom = c.hom ≫ P.kernel.inclusion) :
    ∃ h : IsClosedImmersion d.hom.hom.left,
      IsSchemeKernel p (⟨W.val, d, h⟩ : ClosedSubgroup G.val) ∧ IsCentralIsogeny p := by
  obtain ⟨hh, hk⟩ := kernel_of_split_comparison p d (splitKernelSquare_of_comparison p d P e a c hp hd)
  exact ⟨hh, hk, finite_of_finite_kernel p hk, inferInstance, inferInstance, ⟨W.val, d, hh⟩, hk,
    scalarCentral_of_split_comparison d P e c hd⟩

end

end CentralKernelDescent



section EquivariantSpinReference

open AlgebraicGeometry CategoryTheory Matrix Opposite
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.RelativeFormComparison (fieldTest transportedAut)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

noncomputable section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000 in
theorem finiteEquivariantSpinReference : FiniteEquivariantSpinReference.{u} := by
  intro k _ G n hn hG hsc hf
  classical
  let I := ULift.{u} (Fin n)
  have hI : 4 ≤ Fintype.card I := by simpa [I] using hn
  let : Nonempty I := ⟨ULift.up ⟨0, by omega⟩⟩
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  obtain ⟨L, P, D, l, Q, E, eSep, rSep, s, i, hrSep, hs, hi, hfixed⟩ := hf
  have hP := semisimpleOfSeparableIso P.pair.reductive eSep hG.1
  have hPsc := simplyConnectedOfSeparableIso eSep hsc
  let := D.comm
  have hD := (Classification.SimplyConnectedLattice.latticeCriterion P.pair.G hP P.pair.T
    P.pair.split P.pair.maximal D.datum).mp hPsc
  obtain ⟨K, j, r, hr, _, hfix⟩ := fixedVertex_finiteLevel E G (s i).val eSep rSep hrSep hfixed
  obtain ⟨C₀⟩ := splitSpinImage k I hI
  obtain ⟨w, A, a, ha, hA, hscalar, hfac⟩ := fixedVertex_outerFactorization (S := K) P D E n hn hD s hs i hi C₀
  have hsim (σ : Gal(K/k)) := relativeFactorMatrix E.toExactSequence C₀ w hI A
      (transportedAut k K r σ) a ha
      (fun R x => by
        change spinVectorMatrix C₀ R ((x ≫ A.hom.hom.hom) ≫ w.inv.hom.hom) =
          conjugate (Matrix.GeneralLinearGroup.map (algebraMap k R) a)
            (spinVectorMatrix C₀ R (x ≫ w.inv.hom.hom))
        simpa only [spinVectorMatrix, vectorImageMatrix, Grp.comp_hom_hom, Category.assoc] using hA R x)
      (hfac _ (hfix σ))
  choose g c hq hg using hsim
  obtain ⟨ρ, hρ⟩ := vectorAction_projectiveCocycle C₀ w r hI g hg
  obtain ⟨C⟩ := splitSpinImage K I hI
  let d : Fin ((n - 1) + 1) ≃ I := (finCongr (by omega)).trans Equiv.ulift.symm
  obtain ⟨v, hv⟩ := splitSpinScalarComparison C₀ C d
  let F := groupBaseChange k K
  let e := j.symm ≪≫ (F.mapIso w).symm ≪≫ v
  obtain ⟨b, hb, hVal⟩ := splitKernelFieldComparison C₀ C d v (fun S x => (hv S x).1)
  let W := closedSubgroupAlgebraicGroup (G := C₀.spin) C₀.kernel
  have hStable (σ : Gal(K/k)) := relativeFactor_fixesScalar E.toExactSequence C₀ w A
    (transportedAut k K r σ) hscalar (hfac _ (hfix σ))
  obtain ⟨t, ht⟩ := descendInvariantSubgroupMap P.pair.G G W (C₀.kernel.inclusion ≫ w.hom)
    j r hr hStable
  have hTogether : F.map t ≫ e.hom = b.hom ≫ C.kernel.inclusion := by
    rw [ht, F.map_comp]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    change F.map C₀.kernel.inclusion ≫ (F.mapIso w).hom ≫ j.hom ≫ j.inv ≫
      (F.mapIso w).inv ≫ v.hom = _
    simpa only [Iso.hom_inv_id_assoc] using hb
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨⟨C₀, C, e, g, c, ρ, hρ, hq, ?_, t, b, hTogether, hVal⟩⟩⟩
  intro S σ R f hf x y hxy
  let aS := structureAlgebraMap (k := k) S
  let X (z : Points (F.obj G.val).X S) := baseChangePoint k K P.pair.G.val.X S (z ≫ j.inv.hom.hom)
  have hV (z : Points (F.obj G.val).X S) :
      spinVectorMatrix C S (z ≫ e.hom.hom.hom) = (referenceVectorUnit C₀ w R (X z)).val := by
    let b := (z ≫ j.inv.hom.hom) ≫ (F.map w.inv).hom.hom
    change spinVectorMatrix C S (b ≫ v.hom.hom.hom) = _
    rw [(hv S b).2]
    have h := baseChangePointsSchemeNaturality k K w.inv.hom.hom S (z ≫ j.inv.hom.hom)
    change baseChangePoint k K C₀.spin.val.X S b = X z ≫ w.inv.hom.hom at h
    rw [h]
    rfl
  have hxy' : X y = relativeApply (transportedAut k K r σ) aS (mapPoints f (X x)) :=
    transportedAut_semilinear_points j r hr S σ f hf x y hxy
  change spinVectorMatrix C S (y ≫ e.hom.hom.hom) =
    conjugate (Matrix.GeneralLinearGroup.map (algebraMap K S) (g σ))
      ((spinVectorMatrix C S (x ≫ e.hom.hom.hom)).map f.hom)
  rw [hV, hV, hxy', hg σ, referenceVectorUnit_map]
  rfl

end

end EquivariantSpinReference



section Assembly

open AlgebraicGeometry CategoryTheory Matrix
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.NontrialitarianSpinModels
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification (muTwoUnderlying)

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  [Fintype I] [DecidableEq I] [Nonempty I]

set_option maxHeartbeats 1150000 in
private theorem spinModel_of_trivialization (G : AffineAlgebraicGroup k)
    (hG : GeometricallyConnected G.val.X.hom) (hRank : 4 ≤ Fintype.card I)
    (T : EquivariantSpinTrivialization (K := K) (I := I) G)
    (D : DescendedQuadraticPair T.action) :
    Nonempty (SpinModel G D) := by
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  obtain ⟨H, m, b, hNat, hInj, hRange, hM⟩ := pairIsometryModel D T.split.orthogonal
  obtain ⟨v, hv⟩ := vectorMorphismDescent D G H T.split T.comparison b m hNat hInj hM
    T.g T.actionFormula T.equivariance
  obtain ⟨N, p, j, a, hF, ho, hc, hn, hp, hj⟩ :=
    descendedVectorImage hRank G H hG v T.split T.comparison b hv
  let W := closedSubgroupAlgebraicGroup (G := T.reference.spin) T.reference.kernel
  have : IsFinite W.val.X.hom := by
    change IsFinite T.reference.kernel.group.X.hom
    rw [T.reference.kernelScheme]
    exact scalarSubgroup_finite (k := k) (I := I)
  have : Flat p.hom.hom.left := hF.2.1
  have : Surjective p.hom.hom.left := hF.2.2.1
  have : LocallyOfFinitePresentation p.hom.hom.left := hF.2.2.2.1
  have : IsAffineHom p.hom.hom.left := hF.2.2.2.2.1
  obtain ⟨hd, hk, hCentral⟩ := descendedCentralKernel (W := W) p T.scalar T.split T.comparison a
    T.splitScalar hp T.scalarInclusion
  let Z : ClosedSubgroup G.val := ⟨W.val, T.scalar, hd⟩
  refine ⟨{ full := H
            neutral := N
            inclusion := j
            projection := p
            fullPoints := m
            fullNatural := hNat
            fullFaithful := hInj
            fullRange := hRange
            openImmersion := ho
            closedImmersion := hF.2.2.2.2.2
            connected := hc
            identityComponent := hn
            centralIsogeny := hCentral
            kernel := Z
            isKernel := hk
            kernelScheme := eqToIso T.reference.kernelScheme
            kernelPoints := T.reference.kernelPoints
            kernelNatural := fun R S f x => splitKernelPoint_natural T.reference f x
            splitCover := T.split
            splitSource := T.comparison
            splitNeutral := a
            splitFull := b
            splitKernel := T.splitScalar
            projectionComparison := hp
            inclusionComparison := hj
            kernelComparison := T.scalarInclusion
            scalarComparison := T.scalarValue
            matrixComparison := hM
            reducedNormOne := fun h₂ =>
              neutralPointsReducedNorm D hRank h₂ H N j hF.2.2.2.2.2 m hNat hRange
                T.split b a hj hM }⟩

/-- A simply connected form of type D with a fixed vector vertex has the
descended quadratic-pair model and its scalar Clifford double cover. -/
theorem nontrialitarianSpinModel : NontrialitarianSpinModel.{u} := by
  intro k _ G n hn hG hsc hf
  obtain ⟨K, hK, hAlg, hFin, hGal, ⟨T⟩⟩ := finiteEquivariantSpinReference k G n hn hG hsc hf
  let := hK
  let := hAlg
  let := hFin
  let := hGal
  let I := ULift.{u} (Fin n)
  let : Nonempty I := ⟨ULift.up ⟨0, by omega⟩⟩
  have hRank : 4 ≤ Fintype.card I := by simpa [I] using hn
  have hρ (σ : Gal(K/k)) :
      ∃ (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ),
        (∀ X, T.action.act σ X = conjugate g (X.map σ)) ∧
        ∀ x, Specs.Arithmetic.OddSpinModels.hyperbolicForm I K (g.val *ᵥ x) =
          (c : K) * Specs.Arithmetic.OddSpinModels.hyperbolicForm I K x :=
    ⟨T.g σ, T.multiplier σ, T.actionFormula σ, T.similarity σ⟩
  obtain ⟨D⟩ := quadraticPairDescent k K I T.action hρ
  exact ⟨K, hK, hAlg, hFin, hGal, T.action, D, hρ,
    fun _ => descendedPair_isOrthogonal D, spinModel_of_trivialization G hG.1.2.1 hRank T D⟩

end


end Assembly

end LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
