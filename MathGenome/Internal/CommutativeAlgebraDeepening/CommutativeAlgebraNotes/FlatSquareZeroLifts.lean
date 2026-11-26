import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FlatSquareZeroLifts
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Quotient

noncomputable section

-- Local instances specify the scalar actions used by the tensor products.
set_option linter.style.haveILetI false

open scoped TensorProduct
open TensorProduct LinearMap Module
open CommutativeAlgebraNotes.SquareZeroLift

namespace CommutativeAlgebraNotes.FlatSquareZeroLifts

section Modules

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

private def idealAction (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    I ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp (I.subtype.rTensor M)

@[simp] private theorem idealAction_tmul (I : Ideal R) (i : I) (x : M) :
    idealAction I M (i ⊗ₜ[R] x) = (i : R) • x := rfl

private theorem idealAction_range (I : Ideal R) :
    LinearMap.range (idealAction I M) = I • ⊤ :=
  I.subtype_rTensor_range M

private theorem idealAction_injective (I : Ideal R) [Module.Flat R M] :
    Function.Injective (idealAction I M) :=
  (TensorProduct.lid R M).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap I.subtype I.subtype_injective)

private theorem eq_bot_of_le_ideal_smul (I : Ideal R) (hI : IsNilpotent I)
    (P : Submodule R M) (h : P ≤ I • P) : P = ⊥ := by
  have aux (n : ℕ) : P ≤ I ^ n • P := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Submodule.mul_smul]
        exact h.trans (smul_mono_right I ih)
  obtain ⟨n, hn⟩ := hI
  apply le_antisymm _ bot_le
  simpa [hn] using aux n

/-- Right exactness lifts a relation whose image under ideal multiplication vanishes. -/
private theorem kernel_le_ideal_smul {F : Type*} [AddCommGroup F] [Module R F]
    (I : Ideal R) (p : F →ₗ[R] M) (hp : Function.Surjective p)
    (hact : Function.Injective (idealAction I M))
    (hk : p.ker ≤ I • (⊤ : Submodule R F)) : p.ker ≤ I • p.ker := by
  intro y hy
  have hy' : y ∈ LinearMap.range (idealAction I F) := by
    rw [idealAction_range]
    exact hk hy
  obtain ⟨t, rfl⟩ := hy'
  have hcomm : (idealAction I M).comp (p.lTensor I) = p.comp (idealAction I F) := by
    apply TensorProduct.ext'
    intro i a
    simp
  have ht : p.lTensor I t = 0 := by
    apply hact
    rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, map_zero]
    exact hy
  have hex : Function.Exact (p.ker.subtype.lTensor I) (p.lTensor I) :=
    lTensor_exact I (f := p.ker.subtype) (g := p) p.exact_subtype_ker_map hp
  obtain ⟨s, rfl⟩ := (hex t).mp ht
  have ham :
      (idealAction I F).comp (p.ker.subtype.lTensor I) =
        p.ker.subtype.comp (idealAction I p.ker) := by
    apply TensorProduct.ext'
    intro i a
    simp
  rw [← LinearMap.comp_apply, ham, LinearMap.comp_apply]
  exact (Submodule.mem_smul_top_iff I p.ker _).mp
    ((idealAction_range (M := p.ker) I) ▸ (idealAction I p.ker).mem_range_self s)

variable {S : Type*} [CommRing S] [Algebra R S]

private theorem baseChange_unit_ker (hS : Function.Surjective (algebraMap R S)) :
    LinearMap.ker (TensorProduct.mk R S M 1) = RingHom.ker (algebraMap R S) • ⊤ := by
  let q := Algebra.linearMap R S
  have hc : (TensorProduct.mk R S M 1).comp (TensorProduct.lid R M).toLinearMap =
      q.rTensor M := by
    apply TensorProduct.ext'
    intro r x
    change (1 : S) ⊗ₜ[R] (r • x) = algebraMap R S r ⊗ₜ[R] x
    rw [← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  have he := rTensor_exact M q.exact_subtype_ker_map hS
  have hker : LinearMap.ker q = RingHom.ker (algebraMap R S) := rfl
  rw [← idealAction_range, idealAction, LinearMap.range_comp]
  apply Submodule.comap_injective_of_surjective (TensorProduct.lid R M).surjective
  rw [← LinearMap.ker_comp, hc, Submodule.comap_map_eq_of_injective
    (TensorProduct.lid R M).injective]
  exact he.linearMap_ker_eq

/-- A free reduction modulo a nilpotent ideal lifts to a free module when ideal
multiplication on its tensor product is injective. -/
private theorem free_of_nilpotent_reduction (hS : Function.Surjective (algebraMap R S))
    (hI : IsNilpotent (RingHom.ker (algebraMap R S)))
    [Module.Free S (S ⊗[R] M)]
    (hact : Function.Injective (idealAction (RingHom.ker (algebraMap R S)) M)) :
    Module.Free R M := by
  classical
  let I := RingHom.ker (algebraMap R S)
  let b := Module.Free.chooseBasis S (S ⊗[R] M)
  let ι := Module.Free.ChooseBasisIndex S (S ⊗[R] M)
  let F := ι →₀ R
  let jM := TensorProduct.mk R S M 1
  let jF := TensorProduct.mk R S F 1
  have hM : Function.Surjective jM := TensorProduct.mk_surjective R M S hS
  choose x hx using fun i : ι => hM (b i)
  let p : F →ₗ[R] M := Finsupp.linearCombination R x
  let bp := Algebra.TensorProduct.basis S (Finsupp.basisSingleOne : Basis ι R F)
  have hchange : p.baseChange S = (bp.equiv b (Equiv.refl ι)).toLinearMap := by
    apply bp.ext
    intro i
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    change p.baseChange S (Algebra.TensorProduct.basis S Finsupp.basisSingleOne i) = b i
    rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul]
    change (1 : S) ⊗ₜ[R] (Finsupp.linearCombination R x (Finsupp.single i 1)) = b i
    rw [Finsupp.linearCombination_single, one_smul]
    exact hx i
  have hcomm (y : F) : p.baseChange S (jF y) = jM (p y) := rfl
  have hpSurj : Function.Surjective p := by
    have hSup : p.range ⊔ (I • (⊤ : Submodule R M)) = ⊤ := by
      apply top_unique
      intro m _
      have hbc : Function.Surjective (p.baseChange S) := by
        rw [hchange]
        exact (bp.equiv b (Equiv.refl ι)).surjective
      obtain ⟨t, ht⟩ := hbc (jM m)
      obtain ⟨y, rfl⟩ := TensorProduct.mk_surjective R F S hS t
      have hz : m - p y ∈ I • (⊤ : Submodule R M) := by
        rw [← baseChange_unit_ker hS, LinearMap.mem_ker, map_sub, ← hcomm, ht, sub_self]
      exact Submodule.mem_sup.mpr ⟨p y, ⟨y, rfl⟩, m - p y, hz, by abel⟩
    have hc : (⊤ : Submodule R (M ⧸ p.range)) ≤ I • ⊤ := by
      have hm := congrArg (Submodule.map p.range.mkQ) hSup
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq,
        Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hm
      exact hm.ge
    have hzero := eq_bot_of_le_ideal_smul I hI ⊤ hc
    rw [← LinearMap.range_eq_top]
    exact Submodule.Quotient.subsingleton_iff.mp
      ⟨fun a b => sub_eq_zero.mp ((Submodule.mem_bot (R := R)).mp
        (hzero ▸ (Submodule.mem_top (x := a - b))))⟩
  have hk : p.ker ≤ I • (⊤ : Submodule R F) := by
    intro y hy
    rw [← baseChange_unit_ker hS, LinearMap.mem_ker]
    have hpInj : Function.Injective (p.baseChange S) := by
      rw [hchange]
      exact (bp.equiv b (Equiv.refl ι)).injective
    apply hpInj
    rw [hcomm, LinearMap.mem_ker.mp hy, map_zero, map_zero]
  have hks : p.ker ≤ I • p.ker :=
    kernel_le_ideal_smul I p hpSurj hact hk
  have hker := eq_bot_of_le_ideal_smul I hI p.ker hks
  exact Module.Free.of_equiv (LinearEquiv.ofBijective p
    ⟨LinearMap.ker_eq_bot.mp hker, hpSurj⟩)

end Modules

/-- Every flat module over a local Artin ring is free, with no finiteness hypothesis. -/
theorem flatIsFree : Specs.CommutativeAlgebraNotes.FlatSquareZeroLifts.FlatIsFree := by
  intro R _ _ _ M _ _ _
  let S := IsLocalRing.ResidueField R
  have hs : Function.Surjective (algebraMap R S) := Ideal.Quotient.mk_surjective
  apply free_of_nilpotent_reduction (R := R) (S := S) hs
  · have h := (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp (inferInstance : IsArtinianRing R)
    change IsNilpotent (RingHom.ker (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))
    simpa only [Ideal.mk_ker] using h
  · exact idealAction_injective _

section Lifts

variable {R A B D : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra A B]
  [CommRing D] [Algebra R D]
variable (e : BaseExtension R A) (g : D →+* B)
  (over : ∀ a, g (algebraMap R D a) = algebraMap A B (e.hom a))

private def reductionHom : letI := e.baseAlgebra; A ⊗[R] D →ₐ[A] B :=
  letI := e.baseAlgebra
  letI := e.targetAlgebra B
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  Algebra.TensorProduct.lift (Algebra.ofId A B)
    ({ __ := g, commutes' := over } : D →ₐ[R] B) (fun _ _ => Commute.all _ _)

@[simp] private theorem reductionHom_unit (d : D) :
    letI := e.baseAlgebra
    reductionHom e g over ((1 : A) ⊗ₜ[R] d) = g d := by
  letI := e.baseAlgebra
  change algebraMap A B 1 * g d = g d
  rw [map_one, one_mul]

private theorem reductionHom_surjective (hg : Function.Surjective g) :
    Function.Surjective (reductionHom e g over) := by
  intro b
  obtain ⟨d, rfl⟩ := hg b
  letI := e.baseAlgebra
  exact ⟨(1 : A) ⊗ₜ[R] d, reductionHom_unit e g over d⟩

private theorem unit_surjective :
    letI := e.baseAlgebra
    Function.Surjective (TensorProduct.mk R A D 1) := by
  letI := e.baseAlgebra
  exact TensorProduct.mk_surjective R D A e.surjective

private theorem unit_eq_zero_iff (d : D) :
    letI := e.baseAlgebra
    (1 : A) ⊗ₜ[R] d = 0 ↔ d ∈ LinearMap.range (idealAction e.I D) := by
  letI := e.baseAlgebra
  change d ∈ LinearMap.ker (TensorProduct.mk R A D 1) ↔ _
  rw [baseChange_unit_ker e.surjective, idealAction_range]
  rfl

include over in
private theorem reduction_of_ker_range (hg : Function.Surjective g)
    (hker : ∀ d, g d = 0 ↔ d ∈ LinearMap.range (idealAction e.I D)) : ReducesTo e g := by
  letI := e.baseAlgebra
  have hInj : Function.Injective (reductionHom e g over) := by
    apply (RingHom.injective_iff_ker_eq_bot (reductionHom e g over).toRingHom).mpr
    apply le_antisymm _ bot_le
    intro t ht
    obtain ⟨d, rfl⟩ := unit_surjective (D := D) e t
    change reductionHom e g over ((1 : A) ⊗ₜ[R] d) = 0 at ht
    rw [reductionHom_unit] at ht
    exact Ideal.mem_bot.mpr ((unit_eq_zero_iff e d).mpr ((hker d).mp ht))
  exact ⟨AlgEquiv.ofBijective (reductionHom e g over) ⟨hInj, reductionHom_surjective e g over hg⟩,
    reductionHom_unit e g over⟩

private def reduceCoefficients :
    letI := e.baseAlgebra
    e.I ⊗[R] D →+ Coefficients e B :=
  letI := e.baseAlgebra
  letI := e.kernelTower
  ((TensorProduct.comm A e.I B).toLinearMap.comp
    (((reductionHom e g over).toLinearMap.lTensor e.I).comp
      (AlgebraTensorModule.cancelBaseChange R A A e.I D).symm.toLinearMap)).toAddMonoidHom

@[simp] private theorem reduceCoefficients_tmul (i : e.I) (d : D) :
    reduceCoefficients e g over (i ⊗ₜ[R] d) = coefficientTensor e (g d) i := by
  letI := e.baseAlgebra
  letI := e.kernelTower
  simp [reduceCoefficients]

private theorem reduceCoefficients_surjective (hg : Function.Surjective g) :
    Function.Surjective (reduceCoefficients e g over) := by
  letI := e.baseAlgebra
  letI := e.kernelTower
  exact (TensorProduct.comm A e.I B).surjective.comp
    ((LinearMap.lTensor_surjective _ (reductionHom_surjective e g over hg)).comp
      (AlgebraTensorModule.cancelBaseChange R A A e.I D).symm.surjective)

private theorem reduceCoefficients_injective (h : ReducesTo e g) :
    Function.Injective (reduceCoefficients e g over) := by
  letI := e.baseAlgebra
  letI := e.kernelTower
  obtain ⟨E, hE⟩ := h
  have heq : reductionHom e g over = E.toAlgHom := by
    apply AlgHom.ext
    intro t
    obtain ⟨d, rfl⟩ := unit_surjective (D := D) e t
    exact (reductionHom_unit e g over d).trans (hE d).symm
  unfold reduceCoefficients
  simp only [heq]
  exact (TensorProduct.comm A e.I B).injective.comp
    ((TensorProduct.congr (LinearEquiv.refl A e.I) E.toLinearEquiv).injective.comp
      (AlgebraTensorModule.cancelBaseChange R A A e.I D).symm.injective)

private theorem scalar_coefficientTensor (b : B) (b' : B) (i : e.I) :
    b • coefficientTensor e b' i = coefficientTensor e (b * b') i := by
  change b • (b' ⊗ₜ[A] i) = (b * b') ⊗ₜ[A] i
  rw [TensorProduct.smul_tmul', smul_eq_mul]

private theorem flat_kernel_marking [Module.Flat R D] (h : ReducesTo e g) :
    ∃ (hg : Function.Surjective g) (hz : RingHom.ker g ^ 2 = ⊥),
      letI := kernelModule g hg hz
      ∃ m : RingHom.ker g ≃ₗ[B] Coefficients e B,
        ∀ (i : e.I) (d : D),
          m (d • coefficientInKernel e g over i) = coefficientTensor e (g d) i := by
  letI := e.baseAlgebra
  obtain ⟨E, hE⟩ := h
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨t, rfl⟩ := E.surjective b
    obtain ⟨d, rfl⟩ := unit_surjective (D := D) e t
    exact ⟨d, (hE d).symm⟩
  have hker (d : D) : g d = 0 ↔ d ∈ LinearMap.range (idealAction e.I D) := by
    rw [← unit_eq_zero_iff, ← hE, ← map_zero E]
    exact E.injective.eq_iff
  have hIdeal : RingHom.ker g = e.I.map (algebraMap R D) := by
    ext d
    rw [RingHom.mem_ker, hker, idealAction_range, Ideal.smul_top_eq_map]
    rfl
  have hz : RingHom.ker g ^ 2 = ⊥ := by
    rw [hIdeal, ← Ideal.map_pow, e.squareZero, Ideal.map_bot]
  letI := kernelModule g hg hz
  let μ : e.I ⊗[R] D →+ RingHom.ker g :=
    { toFun := fun t => ⟨idealAction e.I D t, (hker _).mpr ((idealAction e.I D).mem_range_self t)⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun t s => Subtype.ext (map_add _ t s) }
  have hμ : Function.Bijective μ := by
    constructor
    · intro x y hxy
      exact idealAction_injective e.I (congrArg Subtype.val hxy)
    · intro x
      obtain ⟨t, ht⟩ := (hker _).mp x.property
      exact ⟨t, Subtype.ext ht⟩
  let m := (AddEquiv.ofBijective μ hμ).symm.trans
    (AddEquiv.ofBijective (reduceCoefficients e g over)
      ⟨reduceCoefficients_injective e g over ⟨E, hE⟩, reduceCoefficients_surjective e g over hg⟩)
  have hμ_tmul (i : e.I) (d : D) :
      μ (i ⊗ₜ[R] d) = d • coefficientInKernel e g over i := by
    apply Subtype.ext
    change (i : R) • d = d * algebraMap R D i
    rw [Algebra.smul_def, mul_comm]
  have hm (i : e.I) (d : D) :
      m (d • coefficientInKernel e g over i) = coefficientTensor e (g d) i := by
    rw [← hμ_tmul]
    change reduceCoefficients e g over ((AddEquiv.ofBijective μ hμ).symm
      (AddEquiv.ofBijective μ hμ (i ⊗ₜ[R] d))) = _
    rw [AddEquiv.symm_apply_apply, reduceCoefficients_tmul]
  refine ⟨hg, hz, { __ := m, map_smul' := ?_ }, hm⟩
  intro b x
  obtain ⟨d, rfl⟩ := hg b
  change m (g d • x) = g d • m x
  rw [kernelModule_smul g hg hz d x]
  obtain ⟨t, rfl⟩ := hμ.surjective x
  refine TensorProduct.inductionOn t ?_ ?_
  · intro i y
    rw [hμ_tmul, ← mul_smul, hm, hm, map_mul, scalar_coefficientTensor]
  · intro t s ht hs
    rw [map_add μ, smul_add, map_add m, ht, hs, map_add m, smul_add]

private theorem flat_of_marked_lift [Module.Free A B] (L : Lift e (coefficientMap (B := B) e)) :
    Module.Flat R L.Ring ∧ ReducesTo e L.map := by
  letI := e.baseAlgebra
  let g := L.map
  have hformula (i : e.I) (d : L.Ring) :
      L.marking (d • coefficientInKernel e L.map L.over i) =
        coefficientTensor e (g d) i := by
    rw [← L.map_smul d, map_smul]
    change g d • L.marking (coefficientInKernel e L.map L.over i) = _
    have hi : L.marking (coefficientInKernel e L.map L.over i) =
        coefficientMap (B := B) e i := L.induces i
    rw [hi]
    change g d • coefficientTensor e 1 i = _
    rw [scalar_coefficientTensor, mul_one]
  have hcomp (t : e.I ⊗[R] L.Ring) :
      idealAction e.I L.Ring t = (L.marking.symm (reduceCoefficients e g L.over t) : L.ker) := by
    refine TensorProduct.inductionOn t ?_ ?_
    · intro i d
      rw [idealAction_tmul, reduceCoefficients_tmul, ← hformula, LinearEquiv.symm_apply_apply]
      change (i : R) • d = d * algebraMap R L.Ring i
      rw [Algebra.smul_def, mul_comm]
    · intro t s ht hs
      rw [map_add, map_add, map_add]
      exact congrArg₂ (· + ·) ht hs
  have hker (d : L.Ring) : g d = 0 ↔ d ∈ LinearMap.range (idealAction e.I L.Ring) := by
    constructor
    · intro hd
      let x : L.ker := ⟨d, hd⟩
      obtain ⟨t, ht⟩ := reduceCoefficients_surjective e g L.over L.surjective (L.marking x)
      exact ⟨t, by rw [hcomp, ht, LinearEquiv.symm_apply_apply]⟩
    · rintro ⟨t, rfl⟩
      rw [hcomp]
      exact (L.marking.symm (reduceCoefficients e g L.over t)).property
  have hred := reduction_of_ker_range e g L.over L.surjective hker
  refine ⟨?_, hred⟩
  obtain ⟨E, hE⟩ := hred
  letI : Module.Free A (A ⊗[R] L.Ring) := Module.Free.of_equiv E.symm.toLinearEquiv
  letI : Module.Free R L.Ring := by
    apply free_of_nilpotent_reduction (S := A) e.surjective
    · exact ⟨2, e.squareZero⟩
    · intro x y hxy
      apply reduceCoefficients_injective e g L.over ⟨E, hE⟩
      apply L.marking.symm.injective
      apply Subtype.ext
      rw [← hcomp x, ← hcomp y]
      exact hxy
  infer_instance

end Lifts

/-- A flat lift has the canonical square-zero kernel marking. -/
theorem flatToSquareZero :
    Specs.CommutativeAlgebraNotes.FlatSquareZeroLifts.FlatToSquareZero := by
  intro k _ R A f hf hs B _ _ _ D _ _ _ g e h
  have over (a : R) : g (algebraMap R D a) = algebraMap A B (e.hom a) := by
    letI := e.baseAlgebra
    obtain ⟨E, hE⟩ := h
    rw [← hE]
    have ht : (1 : A) ⊗ₜ[R] algebraMap R D a =
        algebraMap A (A ⊗[R] D) (e.hom a) := by
      change (1 : A) ⊗ₜ[R] algebraMap R D a = e.hom a ⊗ₜ[R] (1 : D)
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
      rfl
    rw [ht, E.commutes]
  obtain ⟨hg, hz, marking, hmark⟩ := flat_kernel_marking e g over h
  let L : Lift e (coefficientMap (B := B) e) :=
    { Ring := D
      map := g
      over := over
      surjective := hg
      squareZero := hz
      marking := marking
      induces := fun i => by
        have hi := hmark i 1
        rw [one_smul, map_one] at hi
        exact hi }
  exact ⟨L, AlgEquiv.refl, fun _ => rfl, hmark⟩

/-- A square-zero lift with the prescribed coefficient map is flat and has
the prescribed base change. -/
theorem squareZeroToFlat :
    Specs.CommutativeAlgebraNotes.FlatSquareZeroLifts.SquareZeroToFlat := by
  intro k _ R A f hf hs B _ _ _ e L
  letI : Module.Free A B := flatIsFree A B
  exact flat_of_marked_lift e L

end CommutativeAlgebraNotes.FlatSquareZeroLifts
