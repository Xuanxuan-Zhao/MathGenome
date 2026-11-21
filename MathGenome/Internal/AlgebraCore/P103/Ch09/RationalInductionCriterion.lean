import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.RationalInductionCriterion
import MathGenome.Internal.AlgebraCore.P103.Ch09.VirtualCharacterRing
import MathGenome.Internal.AlgebraCore.P103.Ch09.InducedCharacter
import MathGenome.Internal.AlgebraCore.P103.Ch08.CharacterTableOrthogonality
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

noncomputable section
open scoped BigOperators TensorProduct Classical
universe u
namespace P103.Ch09.RationalInductionCriterion
open RationalInductionSpecs VirtualCharacterSpecs

variable {G : Type u} [Group G] [Fintype G]
local instance (ℋ : Set (Subgroup G)) : Fintype ℋ := Fintype.ofFinite ℋ

/-- The canonical induction on the accepted integral character lattices has
exactly the finite conjugacy formula, including on virtual differences. -/
theorem integral_induction_formula (H : Subgroup G) (χ : VirtualCharacterSpecs.Ring H) :
    (VirtualCharacterRing.Induction.map H χ).1 =
      InducedCharacterSpecs.inductionValue H χ.1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := (VirtualCharacterRing.difference χ.1).mp χ.2
  let A : VirtualCharacterSpecs.Ring H := ⟨a, Subring.subset_closure ha⟩
  let B : VirtualCharacterSpecs.Ring H := ⟨b, Subring.subset_closure hb⟩
  have he : χ = A - B := Subtype.ext hab
  have ordinary_formula (x : VirtualCharacterSpecs.Ring H) (hx : Ordinary H x.1) :
      (VirtualCharacterRing.Induction.map H x).1 =
        InducedCharacterSpecs.inductionValue H x.1 := by
    obtain ⟨n, ρ, hρ⟩ := hx
    have hm := VirtualCharacterRing.Induction.map_actual H ρ x hρ.symm
    obtain ⟨D, E, _⟩ := induced_character_realization H ρ
    have hc := induced_character H ρ D E
    have hd := VirtualCharacterRing.Induction.anyData H ρ D
    rw [hm, hd.2, ← hρ]
    exact funext hc.2.1
  rw [he, map_sub]
  change (VirtualCharacterRing.Induction.map H A).1 -
      (VirtualCharacterRing.Induction.map H B).1 =
        InducedCharacterSpecs.inductionValue H (A.1 - B.1)
  rw [map_sub, ordinary_formula A ha, ordinary_formula B hb]

theorem integral_induction : RationalInductionSpecs.Expected.integralInductionType.{u} := by
  intro G _ _ ℋ
  exact ⟨fun H => VirtualCharacterRing.Induction.map H.1,
    fun H χ => integral_induction_formula H.1 χ⟩

/-- A class indicator, regarded as a function on the group. -/
def classIndicator (g : G) : G → ℂ :=
  fun y => if ConjClasses.mk y = ConjClasses.mk g then 1 else 0

theorem classIndicator_invariant (g : G) :
    classIndicator g ∈ InducedCharacterSpecs.classFunctions G := by
  intro a y
  have he : ConjClasses.mk (a * y * a⁻¹) = ConjClasses.mk y :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨a, rfl⟩).symm
  simp only [classIndicator, he]

/-- An omitted class is killed by every induction in the family. -/
theorem induction_vanishes (H : Subgroup G) (g : G)
    (hg : ∀ x : G, x⁻¹ * g * x ∉ H) (ψ : H → ℂ) :
    InducedCharacterSpecs.inductionValue H ψ g = 0 := by
  simp [InducedCharacterSpecs.inductionValue, hg]

/-- Projection formula for a class function, directly from the conjugacy sum. -/
theorem induction_projection (H : Subgroup G) (f : InducedCharacterSpecs.classFunctions G)
    (ψ : H → ℂ) (g : G) :
    InducedCharacterSpecs.inductionValue H (fun h => f.1 h * ψ h) g =
      f.1 g * InducedCharacterSpecs.inductionValue H ψ g := by
  have hf (x : G) : f.1 (x⁻¹ * g * x) = f.1 g := by
    simpa only [inv_inv] using f.2 x⁻¹ g
  change (Nat.card H : ℂ)⁻¹ * _ = _ * ((Nat.card H : ℂ)⁻¹ * _)
  simp_rw [hf]
  have hs : (∑ x : G, if h : x⁻¹ * g * x ∈ H then
      f.1 g * ψ ⟨x⁻¹ * g * x, h⟩ else 0) =
      f.1 g * ∑ x : G, if h : x⁻¹ * g * x ∈ H then ψ ⟨x⁻¹ * g * x, h⟩ else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  rw [hs]
  ring

/-- The induction of 1 is a positive rational counting function wherever a
conjugate meets H; no positivity assumption on arbitrary characters is used. -/
theorem induction_one_ne_zero (H : Subgroup G) (g : G)
    (hg : ∃ x : G, x⁻¹ * g * x ∈ H) :
    InducedCharacterSpecs.inductionValue H (fun _ => 1) g ≠ 0 := by
  classical
  let s := Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ H)
  have hs : 0 < s.card := by
    obtain ⟨x, hx⟩ := hg
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have he : InducedCharacterSpecs.inductionValue H (fun _ => 1) g =
      (Nat.card H : ℂ)⁻¹ * (s.card : ℂ) := by
    simp [InducedCharacterSpecs.inductionValue, s, Finset.sum_boole]
  rw [he]
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast Nat.card_pos.ne'))
    (by exact_mod_cast hs.ne')

/-- Class indicators in a conjugate of H are scalar multiples of inductions
of their restrictions. This is an explicit preimage construction. -/
theorem indicator_induced (H : Subgroup G) (g : G)
    (hg : ∃ x : G, x⁻¹ * g * x ∈ H) :
    ∃ ψ : InducedCharacterSpecs.classFunctions H,
      InducedCharacterSpecs.inductionValue H ψ.1 = classIndicator g := by
  let c := InducedCharacterSpecs.inductionValue H (fun _ => 1) g
  have hc : c ≠ 0 := induction_one_ne_zero H g hg
  let ψ : InducedCharacterSpecs.classFunctions H :=
    ⟨fun h => c⁻¹ * classIndicator g h, by
      intro a h
      have hi := classIndicator_invariant g (a : G) (h : G)
      simpa using congrArg (c⁻¹ * ·) hi⟩
  refine ⟨ψ, ?_⟩
  funext y
  have hp := induction_projection H
    ⟨classIndicator g, classIndicator_invariant g⟩ (fun _ => 1) y
  have hl : InducedCharacterSpecs.inductionValue H ψ.1 y =
      c⁻¹ * (classIndicator g y * InducedCharacterSpecs.inductionValue H (fun _ => 1) y) := by
    have he : ψ.1 = c⁻¹ • (fun h : H => classIndicator g h * (1 : ℂ)) := by
      funext h; simp [ψ]
    rw [he, map_smul]
    exact congrArg (c⁻¹ * ·) hp
  rw [hl]
  by_cases hy : ConjClasses.mk y = ConjClasses.mk g
  · have he : InducedCharacterSpecs.inductionValue H (fun _ => 1) y = c := by
      have hconj := ConjClasses.mk_eq_mk_iff_isConj.mp hy
      obtain ⟨a, ha⟩ := isConj_iff.mp hconj
      dsimp [c]
      rw [← ha]
      exact (induceFunction_conjugate H (fun _ => 1) a y).symm
    simp [classIndicator, hy, he, hc]
  · simp [classIndicator, hy]


/-- Linear induction on all complex class functions. -/
def complexInduction (H : Subgroup G) :
    InducedCharacterSpecs.classFunctions H →ₗ[ℂ] InducedCharacterSpecs.classFunctions G :=
  ((InducedCharacterSpecs.inductionValue H).comp
    (InducedCharacterSpecs.classFunctions H).subtype).codRestrict
      (InducedCharacterSpecs.classFunctions G) (fun ψ => induced_class_function H ψ)

@[simp] theorem complexInduction_apply (H : Subgroup G)
    (ψ : InducedCharacterSpecs.classFunctions H) :
    (complexInduction H ψ).1 = InducedCharacterSpecs.inductionValue H ψ.1 := rfl

/-- The finite family product is the direct sum in the source. -/
def complexTotal (ℋ : Set (Subgroup G)) :
    (∀ H : ℋ, InducedCharacterSpecs.classFunctions H.1) →ₗ[ℂ]
      InducedCharacterSpecs.classFunctions G :=
  ∑ H : ℋ, (complexInduction H.1).comp (LinearMap.proj H)

@[simp] theorem complexTotal_apply (ℋ : Set (Subgroup G))
    (ψ : ∀ H : ℋ, InducedCharacterSpecs.classFunctions H.1) :
    complexTotal ℋ ψ = ∑ H : ℋ, complexInduction H.1 (ψ H) := by
  simp [complexTotal]

@[simp] theorem complexTotal_single (ℋ : Set (Subgroup G)) (H : ℋ)
    (ψ : InducedCharacterSpecs.classFunctions H.1) :
    complexTotal ℋ (Pi.single H ψ) = complexInduction H.1 ψ := by
  rw [complexTotal_apply, Finset.sum_eq_single H]
  · simp
  · intro K _ hK
    rw [Pi.single_eq_of_ne hK, map_zero]
  · simp

/-- Quotient functions and invariant functions are linearly identical. -/
def classPullback : Ch08.CharacterTableSpecs.ClassFunction G →ₗ[ℂ]
    InducedCharacterSpecs.classFunctions G where
  toFun F := ⟨fun g => F (ConjClasses.mk g), by
    intro a g
    exact congrArg F (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨a, rfl⟩).symm)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem classPullback_bijective : Function.Bijective (classPullback (G := G)) := by
  constructor
  · intro F K h
    funext D
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep D
    exact congrArg (fun f : InducedCharacterSpecs.classFunctions G => f.1 g) h
  · intro f
    obtain ⟨F, hF, _⟩ := (Ch08.CharacterTableOrthogonality.pullback f.1).mp
      (fun g a => f.2 a g)
    exact ⟨F, Subtype.ext (funext hF)⟩

/-- The covering criterion over ℂ, with explicit class-indicator preimages. -/
theorem complex_criterion (ℋ : Set (Subgroup G)) :
    Function.Surjective (complexTotal ℋ) ↔ Covers ℋ := by
  constructor
  · intro hs g
    by_contra hg
    have hz : ∀ (H : ℋ) (x : G), x⁻¹ * g * x ∉ H.1 := by
      simpa only [Covers, not_exists] using hg
    obtain ⟨ψ, hψ⟩ := hs ⟨classIndicator g, classIndicator_invariant g⟩
    have he := congrArg (fun f : InducedCharacterSpecs.classFunctions G => f.1 g) hψ
    simp only [complexTotal_apply, Submodule.coe_sum, Finset.sum_apply,
      complexInduction_apply] at he
    simp only [induction_vanishes _ _ (hz _) _, Finset.sum_const_zero,
      classIndicator, ite_true] at he
    exact zero_ne_one he
  · intro hcov
    apply LinearMap.range_eq_top.mp
    apply top_unique
    intro f _
    let pb := classPullback (G := G)
    obtain ⟨F, rfl⟩ := classPullback_bijective.2 f
    have hi (D : ConjClasses G) :
        classPullback (Pi.single D 1) ∈ LinearMap.range (complexTotal ℋ) := by
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep D
      obtain ⟨H, x, hx⟩ := hcov g
      obtain ⟨ψ, hψ⟩ := indicator_induced H.1 g ⟨x, hx⟩
      refine ⟨Pi.single H ψ, ?_⟩
      rw [complexTotal_single]
      apply Subtype.ext
      rw [complexInduction_apply, hψ]
      funext y
      simp [classPullback, classIndicator, Pi.single_apply]
    have hf : (∑ D : ConjClasses G, F D • classPullback (Pi.single D 1)) =
        classPullback F := by
      simp_rw [← map_smul]
      rw [← map_sum]
      congr 1
      funext D
      simp [Pi.single_apply]
    rw [← hf]
    exact Submodule.sum_mem _ (fun D _ => Submodule.smul_mem _ _ (hi D))

/-- The inclusion of the integral lattice into complex class functions. -/
def integralEvaluation : VirtualCharacterSpecs.Ring G →ₗ[ℤ]
    InducedCharacterSpecs.classFunctions G :=
  { toFun := fun χ => ⟨χ.1, fun a g => VirtualCharacterRing.classFunctions χ.2 g a⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Complexification uses the actual values of virtual characters. -/
def complexEvaluation : (ℂ ⊗[ℤ] VirtualCharacterSpecs.Ring G) →ₗ[ℂ]
    InducedCharacterSpecs.classFunctions G := integralEvaluation.liftBaseChange ℂ

@[simp] theorem complexEvaluation_tmul (c : ℂ) (χ : VirtualCharacterSpecs.Ring G) :
    (complexEvaluation (c ⊗ₜ[ℤ] χ)).1 = c • χ.1 := rfl

/-- The integral irreducible basis becomes exactly the ordinary complex
character basis. This proves the required complexification identification. -/
theorem complexEvaluation_bijective : Function.Bijective (complexEvaluation (G := G)) := by
  obtain ⟨C, hC, hEx, b, hb⟩ := VirtualCharacterRing.free_abelian (G := G)
  let D : Ch08.FourierSpecs.Family.{u,u} G :=
    { n := C.n
      space := fun i => C.space i
      add := fun i => inferInstance
      module := fun i => inferInstance
      representation := fun i => Ch08.RegularMultiplicitySpecs.idealRepresentation (C.space i) }
  have hD : Ch08.FourierSpecs.Valid D := by
    refine ⟨fun i => by
      letI := hC.1 i
      exact Ch08.RegularMultiplicity.ideal_irreducible (C.space i), ?_⟩
    intro i j hij
    apply hC.2 i j
    obtain ⟨e⟩ := hij
    exact ⟨(Ch08.RegularMultiplicity.idealModuleEquiv (C.space i)).symm.trans
      ((Ch08.RegularMultiplicity.moduleEquivOfEquiv e).trans
        (Ch08.RegularMultiplicity.idealModuleEquiv (C.space j)))⟩
  have hDex : Ch08.FourierSpecs.Complete D := by
    intro V _ _ ρ hρ
    exact hEx ρ hρ
  obtain ⟨c, hc⟩ := Ch08.CharacterTableOrthogonality.basis D hD hDex
  let c' := c.map (LinearEquiv.ofBijective classPullback classPullback_bijective)
  let e := (b.baseChange ℂ).equiv c' (Equiv.refl _)
  have he : complexEvaluation (G := G) = e.toLinearMap := by
    apply (b.baseChange ℂ).ext
    intro i
    change complexEvaluation ((b.baseChange ℂ) i) = e ((b.baseChange ℂ) i)
    rw [Module.Basis.equiv_apply]
    apply Subtype.ext
    simp only [Module.Basis.baseChange_apply, complexEvaluation_tmul, one_smul,
      Equiv.refl_apply, c', Module.Basis.map_apply, LinearEquiv.ofBijective_apply, hc]
    exact hb i
  rw [he]
  exact e.bijective


/-- Tensoring a finite product and evaluating its factors gives all tuples
of complex class functions. -/
def complexDomainEquiv (ℋ : Set (Subgroup G)) :
    (ℂ ⊗[ℤ] (∀ H : ℋ, VirtualCharacterSpecs.Ring H.1)) ≃ₗ[ℂ]
      (∀ H : ℋ, InducedCharacterSpecs.classFunctions H.1) :=
  (TensorProduct.piRight ℤ ℂ ℂ (fun H : ℋ => VirtualCharacterSpecs.Ring H.1)).trans
    (LinearEquiv.piCongrRight fun _ =>
      LinearEquiv.ofBijective complexEvaluation complexEvaluation_bijective)

@[simp] theorem complexDomainEquiv_tmul (ℋ : Set (Subgroup G)) (c : ℂ)
    (χ : ∀ H : ℋ, VirtualCharacterSpecs.Ring H.1) (H : ℋ) :
    ((complexDomainEquiv ℋ (c ⊗ₜ[ℤ] χ)) H).1 = c • (χ H).1 := rfl

/-- The complex map is the base change of the actual integral induction sum,
not an unrelated map with the same dimensions. -/
theorem complex_induction_commutes (ℋ : Set (Subgroup G))
    (ind : ∀ H : ℋ, VirtualCharacterSpecs.Ring H.1 →+ VirtualCharacterSpecs.Ring G)
    (hind : IsInduction ℋ ind) :
    (complexEvaluation (G := G)).comp ((integralTotal ℋ ind).baseChange ℂ) =
      (complexTotal ℋ).comp (complexDomainEquiv ℋ).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c χ
  apply Subtype.ext
  change c • (integralTotal ℋ ind χ).1 = _
  have hv : (integralTotal ℋ ind χ).1 = ∑ H : ℋ, (ind H (χ H)).1 := by
    change (virtualSubring G).subtype (integralTotal ℋ ind χ) = _
    simp [integralTotal]
  rw [hv, Finset.smul_sum]
  simp only [LinearMap.comp_apply, complexTotal_apply, Submodule.coe_sum,
    complexInduction_apply]
  apply Finset.sum_congr rfl
  intro H _
  change c • (ind H (χ H)).1 =
    InducedCharacterSpecs.inductionValue H.1 (c • (χ H).1)
  rw [map_smul, hind]

/-- Complex surjectivity reflects precisely the base change of the integral
sum, using the established character-basis identifications. -/
theorem complex_baseChange_criterion (ℋ : Set (Subgroup G))
    (ind : ∀ H : ℋ, VirtualCharacterSpecs.Ring H.1 →+ VirtualCharacterSpecs.Ring G)
    (hind : IsInduction ℋ ind) :
    Function.Surjective ((integralTotal ℋ ind).baseChange ℂ) ↔ Covers ℋ := by
  rw [← complex_criterion]
  have hcomm := LinearMap.congr_fun (complex_induction_commutes ℋ ind hind)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcomm
  constructor
  · intro hs f
    obtain ⟨z, hz⟩ := complexEvaluation_bijective.2 f
    obtain ⟨x, hx⟩ := hs z
    refine ⟨complexDomainEquiv ℋ x, ?_⟩
    exact (hcomm x).symm.trans (by rw [hx, hz])
  · intro hs z
    obtain ⟨f, hf⟩ := hs (complexEvaluation z)
    refine ⟨(complexDomainEquiv ℋ).symm f, ?_⟩
    apply complexEvaluation_bijective.1
    rw [hcomm]
    simpa using hf

/-- Faithful flatness of ℂ over ℚ supplies rank descent. It applies to the
base change of the integral map, so no rational conclusion is assumed from
complex spanning. -/
theorem rational_complex_surjective_iff {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (f : M →ₗ[ℤ] N) :
    Function.Surjective (f.baseChange ℚ) ↔ Function.Surjective (f.baseChange ℂ) := by
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ N
  have ht : Function.Surjective ((f.baseChange ℚ).baseChange ℂ) ↔
      Function.Surjective (f.baseChange ℚ) :=
    Module.FaithfullyFlat.lTensor_surjective_iff_surjective ℚ ℂ (f.baseChange ℚ)
  rw [← ht, LinearMap.baseChange_baseChange]
  change Function.Surjective (eN.symm.toLinearMap.comp ((f.baseChange ℂ).comp eM.toLinearMap)) ↔ _
  constructor
  · intro hs n
    obtain ⟨m, hm⟩ := hs (eN.symm n)
    exact ⟨eM m, eN.symm.injective hm⟩
  · intro hs n
    obtain ⟨m, hm⟩ := hs (eN n)
    exact ⟨eM.symm m, by simp [hm]⟩

/-- The complete rational induction criterion for the tensor-product spaces
and the prescribed induction maps. -/
theorem rational_criterion : RationalInductionSpecs.Expected.criterionType.{u} := by
  intro G _ _ ℋ ind hind
  let hpi := TensorProduct.piRight ℤ ℚ ℚ (fun H : ℋ => VirtualCharacterSpecs.Ring H.1)
  have hsurj : Function.Surjective (rationalSum ℋ ind) ↔
      Function.Surjective ((integralTotal ℋ ind).baseChange ℚ) := by
    constructor
    · intro hs y
      obtain ⟨x, hx⟩ := hs y
      exact ⟨hpi.symm x, by simpa [rationalSum, hpi] using hx⟩
    · intro hs y
      obtain ⟨x, hx⟩ := hs y
      refine ⟨hpi x, ?_⟩
      change ((integralTotal ℋ ind).baseChange ℚ) (hpi.symm (hpi x)) = y
      rw [hpi.symm_apply_apply]
      exact hx
  exact hsurj.trans ((rational_complex_surjective_iff _).trans
    (complex_baseChange_criterion ℋ ind hind))


/-- Every element belongs to the cyclic subgroup it generates, also for
identity elements and the trivial group. -/
theorem cyclic_cover : Covers (cyclicFamily G) := by
  intro g
  refine ⟨⟨Subgroup.zpowers g, by change IsCyclic _; infer_instance⟩, 1, ?_⟩
  simp

/-- Clearing denominators in an actual tensor product, for any integral
module. The resulting denominator is a strictly positive natural number. -/
theorem tensor_clear_denominators {M : Type*} [AddCommGroup M]
    (z : ℚ ⊗[ℤ] M) : ∃ (N : ℕ) (m : M), 0 < N ∧ N • z = 1 ⊗ₜ[ℤ] m := by
  induction z using TensorProduct.inductionOn with
  | tmul q m =>
      refine ⟨q.den, q.num • m, q.den_pos, ?_⟩
      calc
        q.den • (q ⊗ₜ[ℤ] m) = (q.den • q) ⊗ₜ[ℤ] m :=
          TensorProduct.smul_tmul' _ _ _
        _ = (q.num : ℚ) ⊗ₜ[ℤ] m := by rw [nsmul_eq_mul, Rat.den_mul_eq_num]
        _ = 1 ⊗ₜ[ℤ] (q.num • m) := by
          simpa only [zsmul_eq_mul, mul_one] using
            (TensorProduct.smul_tmul (R := ℤ) q.num (1 : ℚ) m)
  | add x y hx hy =>
      obtain ⟨N, a, hN, hx⟩ := hx
      obtain ⟨M, b, hM, hy⟩ := hy
      refine ⟨N * M, M • a + N • b, Nat.mul_pos hN hM, ?_⟩
      calc
        (N * M) • (x + y) = M • (N • x) + N • (M • y) := by
          simp [smul_add, smul_smul, Nat.mul_comm]
        _ = 1 ⊗ₜ[ℤ] (M • a + N • b) := by
          rw [hx, hy, TensorProduct.tmul_add]
          simp only [TensorProduct.tmul_smul]

/-- Evaluation of the rational tensor space, still with values in ℂ. -/
def rationalEvaluation : (ℚ ⊗[ℤ] VirtualCharacterSpecs.Ring G) →ₗ[ℚ]
    InducedCharacterSpecs.classFunctions G := integralEvaluation.liftBaseChange ℚ

@[simp] theorem rationalEvaluation_one_tmul (χ : VirtualCharacterSpecs.Ring G) :
    rationalEvaluation (1 ⊗ₜ[ℤ] χ) = integralEvaluation χ := by
  simp [rationalEvaluation]

/-- The cyclic rational criterion, followed by tensor denominator clearing,
places a positive multiple of every virtual character in the integral image. -/
theorem cyclic_positive_multiple (χ : VirtualCharacterSpecs.Ring G) :
    ∃ (N : ℕ) (ψ : ∀ H : cyclicFamily G, VirtualCharacterSpecs.Ring H.1),
      0 < N ∧ N • χ =
        integralTotal (cyclicFamily G) (fun H => VirtualCharacterRing.Induction.map H.1) ψ := by
  let ℋ := cyclicFamily G
  let ind : ∀ H : ℋ, VirtualCharacterSpecs.Ring H.1 →+ VirtualCharacterSpecs.Ring G :=
    fun H => VirtualCharacterRing.Induction.map H.1
  have hind : IsInduction ℋ ind := fun H χ => integral_induction_formula H.1 χ
  have hs := (rational_criterion ℋ ind hind).mpr cyclic_cover
  obtain ⟨x, hx⟩ := hs (1 ⊗ₜ[ℤ] χ)
  let z := (TensorProduct.piRight ℤ ℚ ℚ
    (fun H : ℋ => VirtualCharacterSpecs.Ring H.1)).symm x
  have hz : ((integralTotal ℋ ind).baseChange ℚ) z = 1 ⊗ₜ[ℤ] χ := hx
  obtain ⟨N, ψ, hN, hψ⟩ := tensor_clear_denominators z
  have he := congrArg ((integralTotal ℋ ind).baseChange ℚ) hψ
  rw [map_nsmul, hz, LinearMap.baseChange_tmul] at he
  have hv := congrArg (rationalEvaluation (G := G)) he
  simp only [map_nsmul, rationalEvaluation_one_tmul] at hv
  refine ⟨N, ψ, hN, ?_⟩
  apply Subtype.ext
  exact congrArg (fun f : InducedCharacterSpecs.classFunctions G => f.1) hv

/-- Integral-multiple Artin induction, with a finite list of cyclic subgroups
and arbitrary virtual input. -/
theorem integral_multiple : RationalInductionSpecs.Expected.integralMultipleType.{u} := by
  intro G _ _ χ
  obtain ⟨N, ψ, hN, hψ⟩ := cyclic_positive_multiple χ
  let ℋ := cyclicFamily G
  let e := (Fintype.equivFin ℋ).symm
  refine ⟨N, Fintype.card ℋ, (fun i => (e i).1), (fun i => ψ (e i)), hN,
    (fun i => (e i).2), ?_⟩
  have hv : (integralTotal ℋ (fun H => VirtualCharacterRing.Induction.map H.1) ψ).1 =
      ∑ H : ℋ, InducedCharacterSpecs.inductionValue H.1 (ψ H).1 := by
    change (virtualSubring G).subtype
      (integralTotal ℋ (fun H => VirtualCharacterRing.Induction.map H.1) ψ) = _
    simp [integralTotal, integral_induction_formula]
  have he := congrArg (fun χ : VirtualCharacterSpecs.Ring G => χ.1) hψ
  change N • χ.1 = _ at he
  rw [hv] at he
  exact he.trans (e.sum_comp _).symm

/-- Dividing the positive integral multiple gives rational coefficients for
all virtual characters; ordinary characters are included in the same ring. -/
theorem artin : RationalInductionSpecs.Expected.artinType.{u} := by
  intro G _ _ χ
  obtain ⟨N, n, H, ψ, hN, hH, he⟩ := integral_multiple χ
  refine ⟨n, H, ψ, (fun _ => (N : ℚ)⁻¹), hH, ?_⟩
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (N : ℂ) • χ.1 = ∑ i, InducedCharacterSpecs.inductionValue (H i) (ψ i).1 := by
    simpa only [Nat.cast_smul_eq_nsmul] using he
  rw [← Finset.smul_sum, Rat.cast_inv, Rat.cast_natCast, ← hm, smul_smul,
    inv_mul_cancel₀ hNc, one_smul]

end P103.Ch09.RationalInductionCriterion
