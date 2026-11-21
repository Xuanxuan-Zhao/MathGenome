import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FlatnessTests
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.P103.Ch01.HomTensorExactness
import Mathlib.Algebra.Module.CharacterModule

noncomputable section

set_option linter.style.haveILetI false

universe u v w

namespace P103.Ch02.FlatnessTests

open P103.BalancedTensor P103.Specs.Ch02.FlatnessTests
open scoped DirectSum

/-- The injectivity definition and exactness agree by balanced right exactness. -/
theorem flat_iff_exact : flat_iff_exactType.{u,v,w} := by
  intro R _ M _ _
  constructor
  · intro h A B C _ _ _ _ _ _ i p hi he hp F G hF hG
    exact ⟨h A B i hi F hF,
      P103.HomTensorExactness.tensor_first_rightExact i p he hp F hF G hG⟩
  · intro h A B _ _ _ _ f hf F hF
    let p := (LinearMap.range f).mkQ
    have he : Function.Exact f p := by
      rw [LinearMap.exact_iff, Submodule.ker_mkQ]
    exact (h A B (B ⧸ LinearMap.range f) f p hf he
      (Submodule.mkQ_surjective _) F (map p LinearMap.id) hF (by intros; rfl)).1


section TensorHelpers
variable {R : Type*} [Ring R]
variable {A B M N : Type*} [AddCommGroup A] [AddCommGroup B]
variable [AddCommGroup M] [AddCommGroup N]
variable [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] [Module R M] [Module R N]

/-- A split inclusion remains injective after tensoring. -/
theorem tensor_retract_injective (i : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : r.comp i = LinearMap.id) :
    Function.Injective (map (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i) := by
  apply Function.LeftInverse.injective (g := map LinearMap.id r)
  intro z
  have hh : (map (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) r).comp (map LinearMap.id i) =
      AddMonoidHom.id _ := by
    rw [← map_comp, h]
    simp
  exact DFunLike.congr_fun hh z

/-- The two variables of the balanced tensor commute functorially. -/
theorem tensor_rectangle (f : A →ₗ[Rᵐᵒᵖ] B) (g : M →ₗ[R] N)
    (z : Tensor R A M) :
    map LinearMap.id g (map f LinearMap.id z) =
      map f LinearMap.id (map LinearMap.id g z) := by
  induction z using induction_on with
  | h0 => simp
  | ht a m => rfl
  | ha x y hx hy => simp [hx, hy]

/-- Tensoring with a free module preserves injections, at arbitrary rank. -/
theorem tensor_free_injective (X : Type*) (f : A →ₗ[Rᵐᵒᵖ] B)
    (hf : Function.Injective f) :
    Function.Injective (map f (LinearMap.id : (X →₀ R) →ₗ[R] (X →₀ R))) := by
  classical
  let e : (X →₀ R) ≃ₗ[R] (⨁ _ : X, R) := finsuppLequivDFinsupp R
  have hj := tensor_retract_injective (A := A) e.toLinearMap e.symm.toLinearMap
    e.symm_comp
  have hu : Function.Injective (map f (LinearMap.id : R →ₗ[R] R)) := by
    intro z z' hz
    apply (rightUnit (R := R)).injective
    apply hf
    simpa only [← rightUnit_natural f] using congrArg (rightUnit (R := R)) hz
  let D : (⨁ _ : X, Tensor R A R) →+ (⨁ _ : X, Tensor R B R) :=
    DirectSum.map (fun _ => map f LinearMap.id)
  have hD : Function.Injective D :=
    (DirectSum.map_injective _).mpr (fun _ => hu)
  have hn (z : Tensor R A (⨁ _ : X, R)) :
      directSumRight (map f LinearMap.id z) = D (directSumRight z) := by
    induction z using induction_on with
    | h0 => simp
    | ht a m =>
      induction m using DirectSum.induction_on with
      | zero => simp
      | of x r => simp [D]
      | add x y hx hy => simp only [tmul_add, map_add] at *; rw [hx, hy]
    | ha x y hx hy => simp only [map_add] at *; rw [hx, hy]
  intro z z' hz
  apply hj
  apply (directSumRight (R := R)).injective
  apply hD
  rw [← hn, ← hn, ← tensor_rectangle, ← tensor_rectangle, hz]

end TensorHelpers

/-- All projectives are flat, with no restriction on free rank. -/
theorem projective_flat : projective_flatType.{u,v,w} := by
  intro R _ M _ _ h
  letI := h
  obtain ⟨s, hs⟩ := Module.projective_def'.mp h
  intro A B _ _ _ _ f hf F hF
  have hF' : F = map f LinearMap.id := hom_ext hF
  rw [hF']
  let q : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have hj := tensor_retract_injective (A := A) s q hs
  intro z z' hz
  apply hj
  apply tensor_free_injective M f hf
  rw [← tensor_rectangle, ← tensor_rectangle, hz]

/-- The free module may have any basis type, including the empty type. -/
theorem free_flat : free_flatType.{u,v,w} := by
  intro R _ X
  exact projective_flat R (X →₀ R) inferInstance


/-- The balanced tensor definition specializes to Mathlib flatness. -/
theorem commutative_flat_iff : commutative_flat_iffType.{u,v,w} := by
  intro R _ M _ _
  constructor
  · intro h
    apply (Module.Flat.iff_rTensor_preserves_injective_linearMap'.{max u v w,u,v}
      (R := R) (M := M)).mpr
    intro A B _ _ _ _ f hf
    letI := commRightModule R A
    letI := commRightModule R B
    letI : IsCentralScalar R A := ⟨fun _ _ => rfl⟩
    letI : IsCentralScalar R B := ⟨fun _ _ => rfl⟩
    let fop : A →ₗ[Rᵐᵒᵖ] B :=
      { f.toAddMonoidHom with map_smul' := fun r a => f.map_smul r.unop a }
    have hinj := h A B fop hf (map fop LinearMap.id) (by intros; rfl)
    intro z z' hz
    apply (commAddEquiv (K := R) (A := A) (B := M)).symm.injective
    apply hinj
    apply (commAddEquiv (K := R) (A := B) (B := M)).injective
    rw [commAddEquiv_natural fop LinearMap.id f (by intros; rfl),
      commAddEquiv_natural fop LinearMap.id f (by intros; rfl)]
    simpa only [LinearMap.rTensor, AddEquiv.apply_symm_apply] using hz
  · intro h A B _ _ _ _ f hf F hF
    letI := h
    letI : Module R A := Module.compHom A
      ((RingHom.id R).toOpposite (fun _ _ => Commute.all _ _))
    letI : Module R B := Module.compHom B
      ((RingHom.id R).toOpposite (fun _ _ => Commute.all _ _))
    letI : IsCentralScalar R A := ⟨fun _ _ => rfl⟩
    letI : IsCentralScalar R B := ⟨fun _ _ => rfl⟩
    let fR : A →ₗ[R] B :=
      { f.toAddMonoidHom with map_smul' := fun r a => f.map_smul (MulOpposite.op r) a }
    have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := M) fR hf
    have hF' : F = map f LinearMap.id := hom_ext hF
    rw [hF']
    intro z z' hz
    apply (commAddEquiv (K := R)).injective
    apply hinj
    change TensorProduct.map fR LinearMap.id (commAddEquiv z) =
      TensorProduct.map fR LinearMap.id (commAddEquiv z')
    rw [← commAddEquiv_natural f LinearMap.id fR (by intros; rfl),
      ← commAddEquiv_natural f LinearMap.id fR (by intros; rfl)]
    exact congrArg (commAddEquiv (K := R)) hz


/-- A finite presentation and simultaneous relation factorization give a section
of a finite free cover. This implication does not require commutativity. -/
theorem finiteRelations_projective (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] (hp : Module.FinitePresentation R M)
    (hr : FiniteRelations R M) : Module.Projective R M := by
  classical
  letI := hp
  obtain ⟨n, k, f, g, hf, he⟩ := Module.FinitePresentation.exists_fin' R M
  let b := Pi.basisFun R (Fin n)
  let c := Pi.basisFun R (Fin k)
  let x : Fin n → M := fun i => f (b i)
  let r : Fin k → Fin n → R := fun j i => g (c j) i
  have hrx (j : Fin k) : ∑ i, r j i • x i = 0 := by
    calc
      _ = f (∑ i, r j i • b i) := by simp [x]
      _ = f (g (c j)) := by
        congr 1
        simpa [r, b, Pi.basisFun_repr] using b.sum_repr (g (c j))
      _ = 0 := he.apply_apply_eq_zero (c j)
  obtain ⟨l, y, s, hxy, hrs⟩ := hr n k x r hrx
  choose z hz using fun a : Fin l => hf (y a)
  let t : (Fin n → R) →ₗ[R] (Fin n → R) :=
    b.constr ℕ (fun i => ∑ a, s i a • z a)
  have ht (i : Fin n) : t (b i) = ∑ a, s i a • z a := b.constr_basis ℕ _ i
  have hft : f.comp t = f := by
    apply b.ext
    intro i
    simpa only [LinearMap.comp_apply, ht, map_sum, map_smul, hz] using (hxy i).symm
  have htg : t.comp g = 0 := by
    apply c.ext
    intro j
    change t (g (c j)) = 0
    rw [← b.sum_repr (g (c j))]
    simp only [map_sum, map_smul, ht]
    change ∑ i, r j i • (∑ a, s i a • z a) = 0
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hrs, zero_smul, Finset.sum_const_zero]
  have hk : LinearMap.ker f ≤ LinearMap.ker t := by
    intro a ha
    obtain ⟨d, rfl⟩ := (he a).mp ha
    exact LinearMap.congr_fun htg d
  let q : M →ₗ[R] (Fin n → R) := f.liftOfSurjective hf ⟨t, hk⟩
  have hq (a : Fin n → R) : q (f a) = t a :=
    LinearMap.equivOfSurjective_apply hf hk
  have hfq : f.comp q = LinearMap.id := by
    ext m
    obtain ⟨a, rfl⟩ := hf m
    exact (congrArg f (hq a)).trans (LinearMap.congr_fun hft a)
  exact Module.Projective.of_split q f hfq


/-- Restrict the enlarged-universe tests to right modules in the ring universe.
The proof transports along explicit ULift equivalences. -/
theorem flat_small_map_injective {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (h : Flat.{u,v,w} R M)
    {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] (f : A →ₗ[Rᵐᵒᵖ] B)
    (hf : Function.Injective f) : Function.Injective (map f (LinearMap.id : M →ₗ[R] M)) := by
  let eA : ULift.{max v w} A ≃ₗ[Rᵐᵒᵖ] A := ULift.moduleEquiv
  let eB : ULift.{max v w} B ≃ₗ[Rᵐᵒᵖ] B := ULift.moduleEquiv
  let f' := eB.symm.toLinearMap.comp (f.comp eA.toLinearMap)
  have hinj := h _ _ f' (eB.symm.injective.comp (hf.comp eA.injective))
    (map f' LinearMap.id) (by intros; rfl)
  have hrect (z : Tensor R A M) :
      map f' LinearMap.id (map eA.symm.toLinearMap LinearMap.id z) =
        map eB.symm.toLinearMap LinearMap.id (map f LinearMap.id z) := by
    induction z using induction_on with
    | h0 => simp
    | ht a m => simp [f']
    | ha z z' hz hz' => simp [hz, hz']
  have hback (z : Tensor R A M) :
      map eA.toLinearMap LinearMap.id (map eA.symm.toLinearMap LinearMap.id z) = z := by
    induction z using induction_on with
    | h0 => simp
    | ht a m => simp
    | ha z z' hz hz' => simp [hz, hz']
  intro z z' hz
  have hz' : map eA.symm.toLinearMap LinearMap.id z =
      map eA.symm.toLinearMap LinearMap.id z' := by
    apply hinj
    rw [hrect, hrect, hz]
  simpa only [hback] using congrArg (map eA.toLinearMap (LinearMap.id : M →ₗ[R] M)) hz'

/-- Flatness gives the finitely generated right-ideal test. -/
theorem flat_idealTest (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] (h : Flat.{u,v,w} R M) : IdealTest R M := by
  intro I _ F hF
  have hF' : F = map I.subtype LinearMap.id := hom_ext hF
  rw [hF']
  exact flat_small_map_injective h I.subtype Subtype.val_injective

/-- Opposite-ring relation factorization gives exactly the reversed product
order in the right-module formulas. -/
theorem right_finiteRelations_iff (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    FiniteRelations Rᵐᵒᵖ M ↔ RightFiniteRelations R M := by
  constructor
  · intro h n k x r hr
    obtain ⟨l, y, s, hx, hs⟩ := h n k x (fun j i => MulOpposite.op (r j i)) hr
    refine ⟨l, y, fun i a => (s i a).unop, ?_, ?_⟩
    · simpa using hx
    · intro j a
      simpa only [Finset.unop_sum, MulOpposite.unop_mul, MulOpposite.unop_op,
        MulOpposite.unop_zero] using congrArg MulOpposite.unop (hs j a)
  · intro h n k x r hr
    obtain ⟨l, y, s, hx, hs⟩ := h n k x (fun j i => (r j i).unop) (by simpa using hr)
    refine ⟨l, y, fun i a => MulOpposite.op (s i a), hx, ?_⟩
    intro j a
    apply MulOpposite.unop_injective
    simpa only [Finset.unop_sum, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_zero] using hs j a


/-- Every balanced tensor is a finite sum of elementary tensors. -/
theorem tensor_exists_fin_sum {R A M : Type*} [Ring R] [AddCommGroup A]
    [AddCommGroup M] [Module Rᵐᵒᵖ A] [Module R M] (z : Tensor R A M) :
    ∃ (n : ℕ) (a : Fin n → A) (m : Fin n → M), z = ∑ i, tmul R (a i) (m i) := by
  induction z using induction_on with
  | h0 => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | ht a m => exact ⟨1, fun _ => a, fun _ => m, by simp⟩
  | ha z z' hz hz' =>
    obtain ⟨n, a, m, rfl⟩ := hz
    obtain ⟨n', a', m', rfl⟩ := hz'
    refine ⟨n+n', Fin.addCases a a', Fin.addCases m m', ?_⟩
    rw [Fin.sum_univ_add]
    simp

/-- The finite ideal test already gives injectivity for every right ideal.
Only the finite support of the tensor is used in the reduction. -/
theorem idealTest_all_ideals {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (h : IdealTest R M)
    (I : Submodule Rᵐᵒᵖ R) :
    Function.Injective (map I.subtype (LinearMap.id : M →ₗ[R] M)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨n, a, m, rfl⟩ := tensor_exists_fin_sum z
  let J : Submodule Rᵐᵒᵖ R := Submodule.span Rᵐᵒᵖ (Set.range fun i => (a i : R))
  have hJ : J.FG := Submodule.fg_span (Set.finite_range _)
  have hJI : J ≤ I := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (a i).property)
  let a' : Fin n → J := fun i => ⟨a i, Submodule.subset_span ⟨i, rfl⟩⟩
  let z' := ∑ i, tmul R (a' i) (m i)
  have hz' : map J.subtype (LinearMap.id : M →ₗ[R] M) z' = 0 := by
    simpa [z', a', map_sum] using hz
  have hzero : z' = 0 :=
    (h J hJ (map J.subtype LinearMap.id) (by intros; rfl)).eq_iff.mp
      (hz'.trans (map_zero _).symm)
  have hm := congrArg (map (Submodule.inclusion hJI) (LinearMap.id : M →ₗ[R] M)) hzero
  have ha (i : Fin n) : Submodule.inclusion hJI (a' i) = a i := rfl
  simpa [z', map_sum, ha] using hm

/-- Finite relation factorization annihilates every tensor in the kernel of
an ideal inclusion, without a finite-generation assumption on the ideal. -/
theorem finiteRelations_all_ideals {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (h : FiniteRelations R M)
    (I : Submodule Rᵐᵒᵖ R) :
    Function.Injective (map I.subtype (LinearMap.id : M →ₗ[R] M)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨n, a, m, rfl⟩ := tensor_exists_fin_sum z
  have hr : ∑ i, (a i : R) • m i = 0 := by
    simpa using congrArg (leftUnit (R := R) (B := M)) hz
  obtain ⟨l, y, s, hm, hs⟩ := h n 1 m (fun _ i => (a i : R)) (fun _ => hr)
  have hcoeff (j : Fin l) : ∑ i, MulOpposite.op (s i j) • a i = (0 : I) := by
    apply Subtype.ext
    simpa using hs 0 j
  calc
    ∑ i, tmul R (a i) (m i) =
        ∑ i, ∑ j, tmul R (MulOpposite.op (s i j) • a i) (y j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hm i]
      change pairing.toBiadditive (a i) (∑ j, s i j • y j) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (balance (s i j) (a i) (y j)).symm
    _ = ∑ j, ∑ i, tmul R (MulOpposite.op (s i j) • a i) (y j) :=
      Finset.sum_comm
    _ = ∑ j, tmul R (∑ i, MulOpposite.op (s i j) • a i) (y j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (map_sum ((pairing (R := R) (A := I) (B := M)).toBiadditive.flip (y j)) _ _).symm
    _ = 0 := by simp [hcoeff]


section Characters

private abbrev Character (M : Type*) [AddCommGroup M] :=
  M →ₗ[ℤ] AddCircle (1 : ℚ)

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Precomposition gives the character group its right R-action. -/
@[instance_reducible] private def characterModule : Module Rᵐᵒᵖ (Character M) :=
  P103.HomTensorExactness.homSourceModule ℤ R M (AddCircle (1 : ℚ))

attribute [local instance] characterModule

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B]

private def characterCurry (χ : Tensor R A M →+ AddCircle (1 : ℚ)) :
    A →ₗ[Rᵐᵒᵖ] Character M where
  toFun a := (χ.comp (pairing.toBiadditive a)).toIntLinearMap
  map_add' a b := by ext m; simp
  map_smul' r a := by
    ext m
    exact congrArg χ (balance r.unop a m)

private def characterUncurry (g : A →ₗ[Rᵐᵒᵖ] Character M) :
    Tensor R A M →+ AddCircle (1 : ℚ) :=
  lift <| Pairing.ofFun (fun a m => g a m)
    (by intros; simp) (by intros; simp)
    (fun r a m => LinearMap.congr_fun (g.map_smul (MulOpposite.op r) a) m)

@[simp] private theorem characterUncurry_tmul (g : A →ₗ[Rᵐᵒᵖ] Character M) (a : A) (m : M) :
    characterUncurry g (tmul R a m) = g a m := rfl

@[simp] private theorem characterCurry_apply (χ : Tensor R A M →+ AddCircle (1 : ℚ))
    (a : A) (m : M) : characterCurry χ a m = χ (tmul R a m) := rfl

/-- The character-module argument uses only the additive injective cogenerator
Q/Z and Baer's criterion over the possibly noncommutative opposite ring. -/
private theorem character_baer
    (h : ∀ I : Submodule Rᵐᵒᵖ R,
      Function.Injective (map I.subtype (LinearMap.id : M →ₗ[R] M))) :
    Module.Baer Rᵐᵒᵖ (Character M) := by
  intro I g
  let e : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R :=
    { MulOpposite.opAddEquiv.symm with map_smul' := fun _ _ => rfl }
  let J : Submodule Rᵐᵒᵖ R := Submodule.map e.toLinearMap (I : Submodule Rᵐᵒᵖ Rᵐᵒᵖ)
  let eI : I ≃ₗ[Rᵐᵒᵖ] J := Submodule.equivMapOfInjective e.toLinearMap e.injective (I : Submodule Rᵐᵒᵖ Rᵐᵒᵖ)
  have heI (z : Tensor R I M) :
      map eI.symm.toLinearMap LinearMap.id (map eI.toLinearMap LinearMap.id z) = z := by
    induction z using induction_on with
    | h0 => simp
    | ht a m => simp
    | ha z z' hz hz' => simp [hz, hz']
  have hj : Function.Injective (map eI.toLinearMap (LinearMap.id : M →ₗ[R] M)) :=
    Function.LeftInverse.injective heI
  have hrect (z : Tensor R I M) :
      map J.subtype LinearMap.id (map eI.toLinearMap LinearMap.id z) =
        map e.toLinearMap LinearMap.id (map I.subtype LinearMap.id z) := by
    induction z using induction_on with
    | h0 => simp
    | ht a m => rfl
    | ha z z' hz hz' => simp [hz, hz']
  have hinj : Function.Injective (map I.subtype (LinearMap.id : M →ₗ[R] M)) := by
    intro z z' hz
    apply hj
    apply h J
    rw [hrect, hrect, hz]
  obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℚ))).extension_property_addMonoidHom
    (map I.subtype LinearMap.id) hinj (characterUncurry g)
  refine ⟨characterCurry ψ, ?_⟩
  intro r hr
  ext m
  exact DFunLike.congr_fun hψ (tmul R (⟨r, hr⟩ : I) m)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All right ideal tests imply preservation of arbitrary injections. -/
theorem all_ideals_flat
    (h : ∀ I : Submodule Rᵐᵒᵖ R,
      Function.Injective (map I.subtype (LinearMap.id : M →ₗ[R] M))) :
    Flat R M := by
  have hb := character_baer h
  intro A B _ _ _ _ f hf F hF
  have hF' : F = map f LinearMap.id := hom_ext hF
  rw [hF']
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply CharacterModule.eq_zero_of_character_apply
  intro χ
  obtain ⟨g, hg⟩ := hb.extension_property f hf (characterCurry χ)
  have he : (characterUncurry g).comp (map f LinearMap.id) = χ := by
    apply hom_ext
    intro a m
    exact LinearMap.congr_fun (LinearMap.congr_fun hg a) m
  have hzχ := DFunLike.congr_fun he z
  change (χ : Tensor R A M →+ AddCircle (1 : ℚ)) z = 0
  simpa only [AddMonoidHom.comp_apply, hz, map_zero] using hzχ.symm

end Characters

/-- The noncommutative finitely generated ideal criterion. -/
theorem flat_iff_idealTest : flat_iff_idealTestType.{u,v,w} := by
  intro R _ M _ _
  exact ⟨flat_idealTest R M, fun h => all_ideals_flat (idealTest_all_ideals h)⟩


/-- The ideal criterion factors one relation by lifting its tensor to the
kernel of the right-linear coefficient row. -/
theorem idealTest_oneRelation {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (h : IdealTest R M)
    (n : ℕ) (x : Fin n → M) (r : Fin n → R) (hr : ∑ i, r i • x i = 0) :
    ∃ (l : ℕ) (y : Fin l → M) (s : Fin n → Fin l → R),
      (∀ i, x i = ∑ a, s i a • y a) ∧ (∀ a, ∑ i, r i * s i a = 0) := by
  classical
  let q : (Fin n → R) →ₗ[Rᵐᵒᵖ] R :=
    { toFun := fun a => ∑ i, r i * a i
      map_add' := by intro a b; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro a b; simp [Finset.sum_mul, mul_assoc] }
  have hq (i : Fin n) : q (Pi.single i 1) = r i := by
    simp [q, Pi.single_apply, mul_ite]
  let p := q.rangeRestrict
  let z := ∑ i, tmul R (Pi.single i (1 : R)) (x i)
  have hz : map p LinearMap.id z = 0 := by
    apply (idealTest_all_ideals h (LinearMap.range q))
    apply (leftUnit (R := R) (B := M)).injective
    simpa [z, p, map_sum, hq] using hr
  obtain ⟨zK, hzK⟩ :=
    ((P103.HomTensorExactness.tensor_first_rightExact
      (LinearMap.ker p).subtype p (LinearMap.exact_subtype_ker_map p)
      (LinearMap.surjective_rangeRestrict q)
      (map (LinearMap.ker p).subtype LinearMap.id) (by intros; rfl)
      (map p LinearMap.id) (by intros; rfl)).1 z).mp hz
  obtain ⟨l, a, y, ha⟩ := tensor_exists_fin_sum zK
  refine ⟨l, y, fun i j => (a j).val i, ?_, ?_⟩
  · intro i
    have ht := congrArg
      (fun z => leftUnit (R := R) (B := M)
        (map (LinearMap.proj i : (Fin n → R) →ₗ[Rᵐᵒᵖ] R) LinearMap.id z)) hzK
    rw [ha] at ht
    simpa [z, map_sum, Pi.single_apply, ite_smul] using ht.symm
  · intro j
    exact congrArg Subtype.val (show p (a j).val = 0 from (a j).property)


/-- Iterating the one-row factorization handles simultaneous relations.
Previously killed rows stay zero under further right matrix multiplication. -/
theorem idealTest_finiteRelations {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (h : IdealTest R M) : FiniteRelations R M := by
  classical
  have hmul {n l : ℕ} (r : Fin n → R) (s : Fin n → Fin l → R) (t : Fin l → R) :
      ∑ i, r i * (∑ a, s i a * t a) = ∑ a, (∑ i, r i * s i a) * t a := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
  intro n k
  induction k with
  | zero =>
    intro x r _
    refine ⟨n, x, fun i a => if i = a then 1 else 0, ?_, ?_⟩
    · intro i; simp
    · intro j; exact Fin.elim0 j
  | succ k ih =>
    intro x r hr
    obtain ⟨l, y, s, hx, hs⟩ := ih x (fun j => r j.castSucc) (fun j => hr j.castSucc)
    let t : Fin l → R := fun a => ∑ i, r (Fin.last k) i * s i a
    have hty : ∑ a, t a • y a = 0 := by
      calc
        _ = ∑ i, r (Fin.last k) i • (∑ a, s i a • y a) := by
          simp only [t, Finset.sum_smul, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
        _ = 0 := by simp only [← hx]; exact hr (Fin.last k)
    obtain ⟨l', z, s', hy, hs'⟩ := idealTest_oneRelation h l y t hty
    refine ⟨l', z, fun i b => ∑ a, s i a * s' a b, ?_, ?_⟩
    · intro i
      calc
        x i = ∑ a, s i a • y a := hx i
        _ = ∑ a, ∑ b, (s i a * s' a b) • z b := by
          simp only [hy, Finset.smul_sum, smul_smul]
        _ = ∑ b, (∑ a, s i a * s' a b) • z b := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul]
    · intro j b
      rw [hmul]
      refine Fin.lastCases ?_ (fun j => ?_) j
      · exact hs' b
      · simp only [hs, zero_mul, Finset.sum_const_zero]

/-- Flatness is equivalent to the full simultaneous finite-relation test. -/
theorem flat_iff_finiteRelations : flat_iff_finiteRelationsType.{u,v,w} := by
  intro R _ M _ _
  exact ⟨fun h => idealTest_finiteRelations (flat_idealTest R M h),
    fun h => all_ideals_flat (finiteRelations_all_ideals h)⟩

/-- A finitely presented flat module is projective. -/
theorem finitelyPresented_flat_projective : finitelyPresented_flat_projectiveType.{u,v,w} := by
  intro R _ M _ _ hp h
  exact finiteRelations_projective R M hp ((flat_iff_finiteRelations R M).mp h)

/-- The right-module characterizations, with coefficients in the reversed order. -/
theorem right_characterizations : right_characterizationsType.{u,v,w} := by
  intro R _ M _ _
  exact ⟨flat_iff_exact Rᵐᵒᵖ M, flat_iff_idealTest Rᵐᵒᵖ M,
    (flat_iff_finiteRelations Rᵐᵒᵖ M).trans (right_finiteRelations_iff R M)⟩

/-- Projectivity consequences for right modules over the same original ring. -/
theorem right_projectivity : right_projectivityType.{u,v,w} := by
  intro R _ M _ _
  exact ⟨projective_flat Rᵐᵒᵖ M, finitelyPresented_flat_projective Rᵐᵒᵖ M⟩


section OppositeTensor
variable {R A B : Type*} [Ring R] [AddCommGroup A] [AddCommGroup B]
variable [Module Rᵐᵒᵖ A] [Module R B]

/-- Exchange the factors while reversing the base ring. -/
private def oppositeFlip :
    letI := doubleOppositeModule R B
    Tensor R A B ≃+ Tensor Rᵐᵒᵖ B A := by
  letI := doubleOppositeModule R B
  let f : Tensor R A B →+ Tensor Rᵐᵒᵖ B A :=
    lift <| Pairing.ofFun (fun a b => tmul Rᵐᵒᵖ b a)
      (by intros; exact tmul_add _ _ _)
      (by intros; exact add_tmul _ _ _)
      (fun r a b => (balance (R := Rᵐᵒᵖ) (MulOpposite.op r) b a).symm)
  let g : Tensor Rᵐᵒᵖ B A →+ Tensor R A B :=
    lift <| Pairing.ofFun (fun b a => tmul R a b)
      (by intros; exact tmul_add _ _ _)
      (by intros; exact add_tmul _ _ _)
      (fun r b a => (balance r.unop a b).symm)
  exact
    { f with
      invFun := g
      left_inv := fun z => by
        change g (f z) = z
        induction z using induction_on with
        | h0 => simp
        | ht a b => rfl
        | ha z z' hz hz' => simp [hz, hz']
      right_inv := fun z => by
        change f (g z) = z
        induction z using induction_on with
        | h0 => simp
        | ht b a => rfl
        | ha z z' hz hz' => simp [hz, hz'] }

@[simp] private theorem oppositeFlip_tmul (a : A) (b : B) :
    letI := doubleOppositeModule R B
    oppositeFlip (tmul R a b) = tmul Rᵐᵒᵖ b a := rfl

end OppositeTensor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The right-module version really preserves M⊗_R− in the original ring,
using the explicit balanced flip to tensors over its opposite. -/
theorem rightFlat_iff_opposite : rightFlat_iff_oppositeType.{u,v,w} := by
  intro R _ M _ _
  constructor
  · intro h A B _ _ _ _ f hf F hF
    letI : Module R A := Module.compHom A (RingEquiv.opOp R).toRingHom
    letI : Module R B := Module.compHom B (RingEquiv.opOp R).toRingHom
    let fR : A →ₗ[R] B :=
      { f.toAddMonoidHom with map_smul' := fun r a => f.map_smul (MulOpposite.op (MulOpposite.op r)) a }
    let eA := oppositeFlip (R := R) (A := M) (B := A)
    let eB := oppositeFlip (R := R) (A := M) (B := B)
    have hcomm (z : Tensor R M A) : eB (map LinearMap.id fR z) = F (eA z) := by
      induction z using induction_on with
      | h0 => simp
      | ht m a => exact (hF a m).symm
      | ha z z' hz hz' => simp [hz, hz']
    have hinj := h A B fR hf (map LinearMap.id fR) (by intros; rfl)
    intro z z' hz
    apply eA.symm.injective
    apply hinj
    apply eB.injective
    rw [hcomm, hcomm]
    simpa only [AddEquiv.apply_symm_apply] using hz
  · intro h A B _ _ _ _ f hf F hF
    letI := doubleOppositeModule R A
    letI := doubleOppositeModule R B
    let fop : A →ₗ[Rᵐᵒᵖᵐᵒᵖ] B :=
      { f.toAddMonoidHom with map_smul' := fun r a => f.map_smul r.unop.unop a }
    let eA := oppositeFlip (R := R) (A := M) (B := A)
    let eB := oppositeFlip (R := R) (A := M) (B := B)
    have hcomm (z : Tensor R M A) : eB (F z) = map fop LinearMap.id (eA z) := by
      induction z using induction_on with
      | h0 => simp
      | ht m a => rw [hF]; rfl
      | ha z z' hz hz' => simp [hz, hz']
    have hinj := h A B fop hf (map fop LinearMap.id) (by intros; rfl)
    intro z z' hz
    apply eA.injective
    apply hinj
    rw [← hcomm, ← hcomm, hz]


/-- Flat tensor preserves exactness even when the original sequence has
neither an injective first map nor a surjective second map. -/
theorem flat_preserves_exact : flat_preserves_exactType.{u,v,w} := by
  intro R _ M _ _ h A B C _ _ _ _ _ _ i p he F G hF hG
  have hF' : F = map i LinearMap.id := hom_ext hF
  have hG' : G = map p LinearMap.id := hom_ext hG
  rw [hF', hG']
  let p' := p.rangeRestrict
  let j := (LinearMap.range p).subtype
  have he' : Function.Exact i p' := by
    apply LinearMap.exact_iff.mpr
    simpa only [p', LinearMap.ker_rangeRestrict] using LinearMap.exact_iff.mp he
  have hex := (P103.HomTensorExactness.tensor_first_rightExact (B := M) i p' he'
    (LinearMap.surjective_rangeRestrict p) (map i LinearMap.id) (by intros; rfl)
    (map p' LinearMap.id) (by intros; rfl)).1
  have hj := h (LinearMap.range p) C j Subtype.val_injective
    (map j LinearMap.id) (by intros; rfl)
  have hc : (map j (LinearMap.id : M →ₗ[R] M)).comp (map p' LinearMap.id) =
      map p LinearMap.id := hom_ext (by intros; rfl)
  intro z
  constructor
  · intro hz
    apply (hex z).mp
    apply hj
    exact (DFunLike.congr_fun hc z).trans hz |>.trans (map_zero _).symm
  · intro hz
    have hpz := (hex z).mpr hz
    rw [← DFunLike.congr_fun hc z]
    change map j LinearMap.id (map p' LinearMap.id z) = 0
    rw [hpz, map_zero]


/-- Combine the opposite-ring theorems with the balanced tensor flip. -/
theorem right_tensor_characterizations : right_tensor_characterizationsType.{u,v,w} := by
  intro R _ M _ _
  obtain ⟨he, hi, hr⟩ := right_characterizations R M
  have hb := rightFlat_iff_opposite R M
  exact ⟨hb.trans he, hb.trans hi, hb.trans hr,
    fun hp => hb.mpr (projective_flat Rᵐᵒᵖ M hp),
    fun hp hf => finitelyPresented_flat_projective Rᵐᵒᵖ M hp (hb.mp hf)⟩

end P103.Ch02.FlatnessTests
