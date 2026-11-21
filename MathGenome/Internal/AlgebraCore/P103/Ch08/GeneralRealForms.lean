import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.GeneralRealForms
import MathGenome.Internal.AlgebraCore.P103.Ch08.IrreducibleRealForms
import MathGenome.Internal.AlgebraCore.P103.Ch08.RegularMultiplicity
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Lagrange

noncomputable section
universe u v w
namespace P103.Ch08.GeneralRealForms
open RegularMultiplicitySpecs RealFormSpecs FrobeniusSchurSpecs GeneralRealFormSpecs
open IrreducibleRealForms
open scoped Matrix

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- A finite-dimensional irreducible has an irreducible contragredient.
The coannihilator argument uses the original invariant subspaces. -/
theorem dual_irreducible [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Irreducible ℂ G V ρ) :
    Irreducible ℂ G (Module.Dual ℂ V) ρ.dual := by
  have : Nontrivial V := hρ.1
  constructor
  · infer_instance
  · intro U
    let W : Subrepresentation ρ :=
      { toSubmodule := U.toSubmodule.dualCoannihilator
        apply_mem_toSubmodule := by
          intro g x hx
          rw [Submodule.mem_dualCoannihilator] at hx ⊢
          intro f hf
          simpa [Representation.dual_apply, Module.Dual.transpose_apply] using
            hx (ρ.dual g⁻¹ f) (U.apply_mem_toSubmodule g⁻¹ hf) }
    have hd : U.toSubmodule.dualCoannihilator.dualAnnihilator = U.toSubmodule :=
      Subspace.dualCoannihilator_dualAnnihilator_eq
    rcases hρ.2 W with hW | hW
    · right
      apply Subrepresentation.toSubmodule_injective
      have hw : U.toSubmodule.dualCoannihilator = ⊥ := congrArg Subrepresentation.toSubmodule hW
      rw [← hd, hw, Submodule.dualAnnihilator_bot]
      rfl
    · left
      apply Subrepresentation.toSubmodule_injective
      have hw : U.toSubmodule.dualCoannihilator = ⊤ := congrArg Subrepresentation.toSubmodule hW
      rw [← hd, hw, Submodule.dualAnnihilator_top]
      rfl

/-- Equality with the contragredient is exactly real-valuedness of the character. -/
theorem realCharacter_iff_selfDual [Fintype G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : RealCharacter ρ ↔ SelfDual ρ := by
  rw [SelfDual, RegularMultiplicity.character_classification]
  constructor
  · intro h
    funext g
    change CharacterSpecs.characterValue ρ g = ρ.dual.character g
    rw [Representation.char_dual]
    exact (h g).symm.trans (character_inverse_conjugate ρ g).symm
  · intro h g
    have hg := congrFun h g
    change CharacterSpecs.characterValue ρ g = ρ.dual.character g at hg
    rw [Representation.char_dual] at hg
    change CharacterSpecs.characterValue ρ g = CharacterSpecs.characterValue ρ g⁻¹ at hg
    rw [character_inverse_conjugate] at hg
    exact hg.symm

/-- An involution gives a nonsingular symmetric form even on a reducible or
zero space: positivity proves that the symmetrized form has zero radical. -/
theorem perfectSymmetricForm_of_conjugateStructure [Fintype G]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hreal : HasConjugateStructure ρ 1) : HasPerfectSymmetricForm ρ := by
  obtain ⟨J, hJ, hJJ⟩ := hreal
  have hJJ' : ∀ x, J (J x) = x := by simpa using hJJ
  obtain ⟨h, hh⟩ := existsInvariantHermitian ρ
  let B := conjugateForm h J
  have hB : Invariant ρ B := conjugateForm_invariant ρ h hh J hJ
  have hs : (B + B.flip).IsSymm := ⟨fun x y => add_comm _ _⟩
  have hl : (B + B.flip).SeparatingLeft := by
    intro x hx
    by_contra hn
    have hz := congrArg Complex.re (hx (J x))
    change (h.toFun x (J (J x)) + h.toFun (J x) (J x)).re = 0 at hz
    rw [hJJ', Complex.add_re] at hz
    have hp := h.positive x hn
    have hq := h.nonneg (J x)
    linarith
  refine ⟨B + B.flip, (invariantForms ρ).add_mem hB
    (FrobeniusSchurIndicator.invariant_flip hB), hs, hl, ?_⟩
  intro x hx
  exact hl x (fun y => (hs.eq x y).trans (hx y))

theorem realForm_symmetric_necessity : realFormSymmetricNecessityType.{u,v} := by
  intro G _ _ V _ _ _ ρ h
  exact perfectSymmetricForm_of_conjugateStructure ρ (conjugateStructure_of_realForm ρ h)

/-- Descent from the zero involution includes all presentations of the zero space. -/
theorem zero_realForm : zeroRealFormType.{u,v} := by
  intro G _ V _ _ _ ρ
  apply realForm_of_conjugateStructure ρ
  exact ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩


/-- Duality moves from one argument of the character pairing to the other. -/
lemma pairing_dual [Fintype G] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue ρ.dual)
        (CharacterSpecs.characterValue σ) =
      UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue ρ)
        (CharacterSpecs.characterValue σ.dual) := by
  unfold UnitaritySpecs.functionPairingValue
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by
    change ρ.dual.character g * star (σ.character g) =
      ρ.character g⁻¹ * star (σ.dual.character g⁻¹)
    rw [Representation.char_dual, Representation.char_dual, inv_inv])

/-- The natural multiplicity in a dual is the multiplicity of the dual type. -/
lemma multiplicity_dual_pair [Fintype G] [FiniteDimensional ℂ V]
    (C : Family G) (ρ : Representation ℂ G V) (i j : Fin C.n)
    (hij : DualPair C i j) : multiplicity C ρ.dual i = multiplicity C ρ j := by
  apply Nat.cast_injective (R := ℂ)
  rw [← RegularMultiplicity.pairing_multiplicity,
    ← RegularMultiplicity.pairing_multiplicity, pairing_dual,
    RegularMultiplicity.character_of_equiv hij.some]

/-- Actual decompositions make equality of all multiplicities an isomorphism. -/
lemma equiv_of_multiplicity_eq [Fintype G] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (C : Family G) (hC : Valid C) (hEx : Exhaustive.{u,u} C)
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hm : multiplicity C ρ = multiplicity C σ) : Nonempty (ρ.Equiv σ) := by
  have eρ := (RegularMultiplicity.multiplicity_decomposition C hC
    (RegularMultiplicity.exhaustive_from_regular C hEx) ρ).1
  have eσ := (RegularMultiplicity.multiplicity_decomposition C hC
    (RegularMultiplicity.exhaustive_from_regular C hEx) σ).1
  rw [hm] at eρ
  exact ⟨RegularMultiplicity.representationEquivOfModuleEquiv (eρ.some.trans eσ.some.symm)⟩

lemma multiplicity_eq_of_equiv [Fintype G] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (C : Family G) {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) : multiplicity C ρ = multiplicity C σ := by
  funext i
  apply Nat.cast_injective (R := ℂ)
  rw [← RegularMultiplicity.pairing_multiplicity,
    ← RegularMultiplicity.pairing_multiplicity, RegularMultiplicity.character_of_equiv e]

/-- Every representative has a representative of its dual type. -/
lemma exists_dual_type [Fintype G] (C : Family G) (hC : Valid C)
    (hEx : Exhaustive.{u,u} C) (i : Fin C.n) : ∃ j, DualPair C i j := by
  have := hC.1 i
  obtain ⟨j, ⟨e⟩⟩ := hEx (idealRepresentation (C.space i)).dual
    (dual_irreducible _ (RegularMultiplicity.ideal_irreducible (C.space i)))
  exact ⟨j, ⟨e.symm⟩⟩

/-- The precise general real-character criterion; distinct dual types must
occur equally often, with no condition on self-dual types. -/
theorem real_character_criterion : realCharacterCriterionType.{u,v} := by
  intro G _ _ C hC hEx V _ _ _ ρ
  constructor
  · intro hr i j _ hij
    obtain ⟨e⟩ := (realCharacter_iff_selfDual ρ).mp hr
    exact (congrFun (multiplicity_eq_of_equiv C e) i).trans
      (multiplicity_dual_pair C ρ i j hij)
  · intro hm
    apply (realCharacter_iff_selfDual ρ).mpr
    apply equiv_of_multiplicity_eq C hC hEx
    funext i
    obtain ⟨j, hij⟩ := exists_dual_type C hC hEx i
    rw [multiplicity_dual_pair C ρ i j hij]
    by_cases heq : i = j
    · rw [heq]
    · exact hm i j heq hij


/-- Nondegeneracy makes the invariant form itself an equivariant duality;
no irreducibility is needed. -/
theorem selfDual_of_perfectSymmetricForm [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (h : HasPerfectSymmetricForm ρ) : SelfDual ρ := by
  obtain ⟨B, hB, _, hnd⟩ := h
  exact ⟨(FrobeniusSchurIndicator.formMap ρ B hB).ofBijective (B.toDual hnd).bijective⟩

theorem symmetricForm_balanced_necessity : symmetricFormBalancedNecessityType.{u,v} := by
  intro G _ _ C hC hEx V _ _ _ ρ h
  exact (real_character_criterion C hC hEx ρ).mp
    ((realCharacter_iff_selfDual ρ).mpr (selfDual_of_perfectSymmetricForm ρ h))

theorem realForm_real_character : realFormRealCharacterType.{u,v} := by
  intro G _ _ V _ _ _ ρ h
  exact (realCharacter_iff_selfDual ρ).mpr
    (selfDual_of_perfectSymmetricForm ρ (realForm_symmetric_necessity ρ h))

/-- A quaternionic conjugate-linear structure forces even complex dimension.
This determinant argument also covers the zero space. -/
theorem even_finrank_of_quaternionic [FiniteDimensional ℂ V]
    (J : V →ₗ⋆[ℂ] V) (hJJ : ∀ x, J (J x) = -x) :
    Even (Module.finrank ℂ V) := by
  classical
  let b := Module.finBasis ℂ V
  let M : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun i j => b.repr (J (b j)) i
  have hM : M * M.map (starRingEnd ℂ) = -1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply]
    have he := congrArg (fun x => b.repr (J x) i) (b.sum_repr (J (b j)))
    simp only [map_sum, map_smulₛₗ, hJJ, map_neg] at he
    simpa [M, Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply,
      b.repr_self, Finsupp.single_apply, eq_comm, mul_comm] using he
  have hd := congrArg Matrix.det hM
  rw [Matrix.det_mul] at hd
  change M.det * ((starRingEnd ℂ).mapMatrix M).det = (- (1 : Matrix (Fin (Module.finrank ℂ V)) _ ℂ)).det at hd
  rw [← RingHom.map_det] at hd
  have hd' : M.det * star M.det = (-1 : ℂ) ^ Module.finrank ℂ V := by
    simpa only [Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin, starRingEnd_apply] using hd
  by_contra hn
  rw [(Nat.not_even_iff_odd.mp hn).neg_one_pow] at hd'
  have hre := congrArg Complex.re hd'
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.neg_re, Complex.one_re] at hre
  nlinarith [sq_nonneg M.det.re, sq_nonneg M.det.im]

/-- Composing on both sides with equivariant conjugate-linear maps gives
conjugation on the genuine space of intertwiners. -/
def intertwinerConjugation {W : Type w} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (J : V →ₗ⋆[ℂ] V) (K : W →ₗ⋆[ℂ] W)
    (hJ : ∀ g x, J (ρ g x) = ρ g (J x))
    (hK : ∀ g x, K (σ g x) = σ g (K x)) :
    σ.IntertwiningMap ρ →ₗ⋆[ℂ] σ.IntertwiningMap ρ where
  toFun f :=
    { toLinearMap := J.comp (f.toLinearMap.comp K)
      isIntertwining' g := by
        ext x
        change J (f (K (σ g x))) = ρ g (J (f (K x)))
        rw [hK, f.isIntertwining, hJ] }
  map_add' f t := by
    ext x
    change J ((f + t) (K x)) = J (f (K x)) + J (t (K x))
    exact J.map_add _ _
  map_smul' c f := by
    ext x
    change J (c • f (K x)) = star c • J (f (K x))
    exact J.map_smulₛₗ c _

/-- A real structure on the target and a quaternionic structure on a simple
source force the intertwiner multiplicity to be even. -/
theorem even_intertwiner_of_structures [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : HasConjugateStructure ρ 1) (hσ : HasConjugateStructure σ (-1)) :
    Even (Module.finrank ℂ (σ.IntertwiningMap ρ)) := by
  obtain ⟨J, hJ, hJJ⟩ := hρ
  obtain ⟨K, hK, hKK⟩ := hσ
  apply even_finrank_of_quaternionic (intertwinerConjugation ρ σ J K hJ hK)
  intro f
  ext x
  change J (J (f (K (K x)))) = -f x
  simp only [hKK, neg_one_smul, map_neg, hJJ, one_smul]

/-- Necessity of the quaternionic parity condition for an actual real form.
No complete-family assumption is needed in this direction. -/
theorem realForm_even_multiplicity [Fintype G] [FiniteDimensional ℂ V]
    (C : Family G) (hC : Valid C) (ρ : Representation ℂ G V)
    (hreal : HasRealForm ρ) : EvenQuaternionicMultiplicity C ρ := by
  intro i hi
  have := hC.1 i
  exact even_intertwiner_of_structures ρ (idealRepresentation (C.space i))
    (conjugateStructure_of_realForm ρ hreal)
    ((normalized_structures _ (RegularMultiplicity.ideal_irreducible (C.space i))).2 hi)

/-- Real polynomial functions of an operator commute with any additive map
that commutes with the operator and with real scalar multiplication. -/
lemma real_aeval_commute (A : Module.End ℂ V) (f : V →+ V)
    (hr : ∀ (r : ℝ) x, f ((r : ℂ) • x) = (r : ℂ) • f x)
    (hA : ∀ x, f (A x) = A (f x)) (p : Polynomial ℝ) :
    ∀ x, f ((Polynomial.aeval A p) x) = (Polynomial.aeval A p) (f x) := by
  induction p using Polynomial.induction_on with
  | C a =>
    intro x
    rw [Polynomial.aeval_C]
    exact hr a x
  | add p q hp hq =>
    intro x
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a hn =>
    intro x
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    change f ((Polynomial.aeval A _) (A x)) = (Polynomial.aeval A _) (A (f x))
    rw [hn, hA]

lemma real_aeval_on_eigenvector (A : Module.End ℂ V) (p : Polynomial ℝ)
    (x : V) (r : ℝ) (hx : A x = (r : ℂ) • x) :
    (Polynomial.aeval A p) x = Complex.ofReal (p.eval r) • x := by
  induction p using Polynomial.induction_on with
  | C a => simp [Polynomial.aeval_C]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    change (Polynomial.aeval A _) (A x) = _
    rw [hx, map_smul, h]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Complex.ofReal_mul, Complex.ofReal_pow, smul_smul]
    congr 1
    ring

/-- Normalize the conjugate-linear map associated to a perfect symmetric form
using a real polynomial in its positive self-adjoint square. -/
theorem conjugateStructure_of_perfectSymmetricForm [Fintype G]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hform : HasPerfectSymmetricForm ρ) : HasConjugateStructure ρ 1 := by
  classical
  obtain ⟨B, hB, hs, hnd⟩ := hform
  obtain ⟨h, hh⟩ := existsInvariantHermitian ρ
  let J := bilinearConjugate h B
  have hJ := bilinearConjugate_equivariant h ρ hh B hB
  have hi : Function.Injective J := bilinearConjugate_injective h B hnd
  let A : Module.End ℂ V := J.comp J
  have hpair (x y : V) : h.toFun x (A y) = h.toFun (J y) (J x) := by
    change h.toFun x (bilinearConjugate h B (J y)) = _
    rw [bilinearConjugate_pairing, hs.eq]
    exact (bilinearConjugate_pairing h B _ _).symm
  letI : InnerProductSpace.Core ℂ V := h.core
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ V)
  have hA : A.IsSymmetric := by
    intro x y
    change h.toFun y (A x) = h.toFun (A y) x
    rw [hpair, ← h.conj_symm (A y) x, hpair, h.conj_symm]
  let b := (hA.eigenvectorBasis rfl).toBasis
  let μ := hA.eigenvalues rfl
  have hb (i) : A (b i) = (μ i : ℂ) • b i := hA.apply_eigenvectorBasis rfl i
  have hpos (i) : 0 < μ i := by
    have hv : b i ≠ 0 := b.ne_zero i
    have hJv : J (b i) ≠ 0 := fun hz => hv (hi (hz.trans J.map_zero.symm))
    have hp := h.positive (J (b i)) hJv
    have hq := h.positive (b i) hv
    have he := congrArg Complex.re (hpair (b i) (b i))
    rw [hb, h.smul_right] at he
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
    exact (mul_pos_iff_of_pos_right hq).mp (he.symm ▸ hp)
  obtain ⟨p, hp⟩ := (Polynomial.exists_eval_eq_iff μ (fun i => (Real.sqrt (μ i))⁻¹)).mpr
    (fun i j hij => by rw [hij])
  let T : Module.End ℂ V := Polynomial.aeval A p
  have hJT (x) : J (T x) = T (J x) :=
    real_aeval_commute A J.toAddMonoidHom
      (fun r x => by simpa using J.map_smulₛₗ (r : ℂ) x) (fun _ => rfl) p x
  have hTρ (g) (x) : T (ρ g x) = ρ g (T x) := by
    symm
    apply real_aeval_commute A (ρ g).toAddMonoidHom
      (fun r x => (ρ g).map_smul (r : ℂ) x) _ p x
    intro x
    change ρ g (J (J x)) = J (J (ρ g x))
    rw [hJ, hJ]
  have hTA : (T.comp T).comp A = LinearMap.id := by
    apply b.ext
    intro i
    change T (T (A (b i))) = b i
    rw [hb, map_smul, map_smul, real_aeval_on_eigenvector A p _ _ (hb i), map_smul,
      real_aeval_on_eigenvector A p _ _ (hb i), hp]
    rw [smul_smul, smul_smul]
    have hc : (μ i : ℂ) * ↑(Real.sqrt (μ i))⁻¹ * ↑(Real.sqrt (μ i))⁻¹ = 1 := by
      have he : (Real.sqrt (μ i) : ℂ) ^ 2 = (μ i : ℂ) := by
        exact_mod_cast Real.sq_sqrt (hpos i).le
      have hn : (Real.sqrt (μ i) : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (hpos i))
      rw [← he]
      push_cast
      field_simp
    rw [hc, one_smul]
  refine ⟨T.comp J, ?_, ?_⟩
  · intro g x
    change T (J (ρ g x)) = ρ g (T (J x))
    rw [hJ, hTρ]
  · intro x
    change T (J (T (J x))) = (1 : ℂ) • x
    rw [hJT, one_smul]
    exact congrArg (fun f : Module.End ℂ V => f x) hTA

/-- The full equivalence for arbitrary finite-dimensional representations,
including the zero representation. -/
theorem symmetric_form_criterion : symmetricFormCriterionType.{u,v} := by
  intro G _ _ V _ _ _ ρ
  exact ⟨realForm_symmetric_necessity ρ, fun h =>
    realForm_of_conjugateStructure ρ (conjugateStructure_of_perfectSymmetricForm ρ h)⟩

theorem symmetricForm_parity_necessity : symmetricFormParityNecessityType.{u,v} := by
  intro G _ _ C hC _ V _ _ _ ρ h
  exact realForm_even_multiplicity C hC ρ ((symmetric_form_criterion ρ).mpr h)

/-- Both numerical obstructions are necessary for a real form. -/
theorem realForm_multiplicity_necessity [Fintype G] [FiniteDimensional ℂ V]
    (C : Family G) (hC : Valid C) (hEx : Exhaustive.{u,u} C)
    (ρ : Representation ℂ G V) (h : HasRealForm ρ) :
    BalancedMultiplicity C ρ ∧ EvenQuaternionicMultiplicity C ρ :=
  ⟨(real_character_criterion C hC hEx ρ).mp (realForm_real_character ρ h),
    realForm_even_multiplicity C hC ρ h⟩

/-- Transport an actual conjugate-linear structure across an equivariant
complex-linear isomorphism. -/
theorem conjugateStructure_transport {W : Type w} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) {ε : ℂ} (h : HasConjugateStructure ρ ε) :
    HasConjugateStructure σ ε := by
  obtain ⟨J, hJ, hJJ⟩ := h
  let K := e.toLinearMap.comp (J.comp e.symm.toLinearMap)
  refine ⟨K, ?_, ?_⟩
  · intro g x
    change e (J (e.symm (σ g x))) = σ g (e (J (e.symm x)))
    have h₁ : e.symm (σ g x) = ρ g (e.symm x) :=
      congrArg (fun f : W →ₗ[ℂ] V => f x) (e.symm.isIntertwining' g)
    rw [h₁, hJ]
    exact congrArg (fun f : V →ₗ[ℂ] W => f (J (e.symm x))) (e.isIntertwining' g)
  · intro x
    change e (J (e.symm (e (J (e.symm x))))) = ε • x
    rw [e.symm_apply_apply, hJJ, map_smul, e.apply_symm_apply]

/-- On a conjugate pair, swap the two summands using a conjugate-linear
isomorphism and its inverse. -/
theorem conjugate_pair_structure {W : Type w} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : V ≃ₗ⋆[ℂ] W) (he : ∀ g x, e (ρ g x) = σ g (e x)) :
    HasConjugateStructure (ρ.prod σ) 1 := by
  have hinv (g) (y) : e.symm (σ g y) = ρ g (e.symm y) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  let K : V × W →ₗ⋆[ℂ] V × W :=
    { toFun := fun x => (e.symm x.2, e x.1)
      map_add' := fun x y => Prod.ext (e.symm.map_add _ _) (e.map_add _ _)
      map_smul' := fun c x => Prod.ext (e.symm.map_smulₛₗ c _) (e.map_smulₛₗ c _) }
  refine ⟨K, ?_, ?_⟩
  · intro g x
    exact Prod.ext (hinv g x.2) (he g x.1)
  · intro x
    change (e.symm (e x.1), e (e.symm x.2)) = (1 : ℂ) • x
    simp only [e.symm_apply_apply, e.apply_symm_apply, one_smul]

/-- Two quaternionic copies have a real structure, with the necessary sign
in the second component. -/
theorem quaternionic_pair_structure (ρ : Representation ℂ G V)
    (h : HasConjugateStructure ρ (-1)) : HasConjugateStructure (ρ.prod ρ) 1 := by
  obtain ⟨J, hJ, hJJ⟩ := h
  let K : V × V →ₗ⋆[ℂ] V × V :=
    { toFun := fun x => (J x.2, -J x.1)
      map_add' := fun x y => Prod.ext (J.map_add _ _) (by simp [map_add, add_comm])
      map_smul' := fun c x => Prod.ext (J.map_smulₛₗ c _) (by simp [map_smulₛₗ]) }
  refine ⟨K, ?_, ?_⟩
  · intro g x
    apply Prod.ext
    · exact hJ g x.2
    · change -J (ρ g x.1) = ρ g (-J x.1)
      rw [hJ, map_neg]
  · intro x
    apply Prod.ext
    · change J (-J x.1) = (1 : ℂ) • x.1
      simp [map_neg, hJJ]
    · change -J (J x.2) = (1 : ℂ) • x.2
      simp [hJJ]

/-- Hermitian duality identifies any finite-dimensional representation's
dual with its complex conjugate, equivariantly. -/
theorem dual_pair_structure [Fintype G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : HasConjugateStructure (ρ.prod ρ.dual) 1 := by
  obtain ⟨h, hh⟩ := existsInvariantHermitian ρ
  apply conjugate_pair_structure ρ ρ.dual (Hermitian.dualEquiv h)
  intro g x
  ext y
  change h.toFun y (ρ g x) = h.toFun (ρ g⁻¹ y) x
  simpa only [Representation.self_inv_apply] using hh g (ρ g⁻¹ y) x

/-- The componentwise representation on an arbitrary product of spaces. -/
def productRepresentation {ι : Type*} {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ G (X i)) : Representation ℂ G (∀ i, X i) where
  toFun g :=
    { toFun := fun x i => ρ i g (x i)
      map_add' := fun x y => funext fun i => (ρ i g).map_add (x i) (y i)
      map_smul' := fun c x => funext fun i => (ρ i g).map_smul c (x i) }
  map_one' := by ext x i; exact congrArg (fun f : Module.End ℂ (X i) => f (x i)) (ρ i).map_one
  map_mul' g h := by
    ext x i
    exact congrArg (fun f : Module.End ℂ (X i) => f (x i)) ((ρ i).map_mul g h)

/-- Structures on factors assemble without any nonzero-dimension assumption. -/
theorem product_structure {ι : Type*} {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ G (X i)) (ε : ℂ)
    (h : ∀ i, HasConjugateStructure (ρ i) ε) :
    HasConjugateStructure (productRepresentation ρ) ε := by
  choose J hJ hJJ using h
  let K : (∀ i, X i) →ₗ⋆[ℂ] (∀ i, X i) :=
    { toFun := fun x i => J i (x i)
      map_add' := fun x y => funext fun i => (J i).map_add (x i) (y i)
      map_smul' := fun c x => funext fun i => (J i).map_smulₛₗ c (x i) }
  refine ⟨K, ?_, ?_⟩
  · intro g x
    exact funext fun i => hJ i g (x i)
  · intro x
    exact funext fun i => hJJ i (x i)

/-- Every even number of quaternionic copies has an actual real structure. -/
theorem even_quaternionic_copies (ρ : Representation ℂ G V)
    (hρ : HasConjugateStructure ρ (-1)) (n : ℕ) (hn : Even n) :
    HasConjugateStructure (productRepresentation (fun _ : Fin n => ρ)) 1 := by
  obtain ⟨k, rfl⟩ := hn
  let τ := productRepresentation (fun _ : Fin k => ρ)
  have hτ : HasConjugateStructure τ (-1) := product_structure _ _ (fun _ => hρ)
  let e : (Fin (k + k) → V) ≃ₗ[ℂ] (Fin k → V) × (Fin k → V) :=
    (LinearEquiv.funCongrLeft ℂ V finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ V)
  have he : (productRepresentation (fun _ : Fin (k + k) => ρ)).Equiv (τ.prod τ) :=
    Representation.Equiv.mk e (fun g => by ext x <;> rfl)
  exact conjugateStructure_transport he.symm (quaternionic_pair_structure τ hτ)

/-- The canonical multiplicity decomposition, expressed as a product with
its actual componentwise group action. -/
theorem multiplicity_product_equiv [Fintype G] [FiniteDimensional ℂ V]
    (C : Family G) (hC : Valid C) (hEx : Exhaustive.{u,u} C)
    (ρ : Representation ℂ G V) :
    Nonempty (ρ.Equiv (productRepresentation (fun i : Fin C.n =>
      productRepresentation (fun _ : Fin (multiplicity C ρ i) =>
        idealRepresentation (C.space i))))) := by
  obtain ⟨e₀⟩ := (RegularMultiplicity.multiplicity_decomposition C hC
    (RegularMultiplicity.exhaustive_from_regular C hEx) ρ).1
  let e := e₀.trans (DFinsupp.linearEquivFunOnFintype (R := MonoidAlgebra ℂ G))
  refine ⟨Representation.Equiv.mk
    (ρ.asModuleEquiv.symm.trans (e.restrictScalars ℂ)) ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  funext i j
  change e (ρ.asModuleEquiv.symm (ρ g x)) i j =
    idealRepresentation (C.space i) g (e (ρ.asModuleEquiv.symm x) i j)
  rw [ρ.asModuleEquiv_symm_map_rho, e.map_smul]
  rfl

/-- The realization construction is complete when every irreducible type is
self-dual: positive copies descend separately and negative copies in pairs. -/
theorem selfDual_family_construction [Fintype G] [FiniteDimensional ℂ V]
    (C : Family G) (hC : Valid C) (hEx : Exhaustive.{u,u} C)
    (ρ : Representation ℂ G V)
    (hself : ∀ i, SelfDual (idealRepresentation (C.space i)))
    (heven : EvenQuaternionicMultiplicity C ρ) : HasConjugateStructure ρ 1 := by
  obtain ⟨e⟩ := multiplicity_product_equiv C hC hEx ρ
  apply conjugateStructure_transport e.symm
  apply product_structure _ 1
  intro i
  have := hC.1 i
  let σ := idealRepresentation (C.space i)
  have hirr := RegularMultiplicity.ideal_irreducible (C.space i)
  obtain hzero | hpos | hneg := (FrobeniusSchurIndicator.classification σ hirr).1
  · exact ((FrobeniusSchurIndicator.classification σ hirr).2.1.mp hzero (hself i)).elim
  · exact product_structure _ 1 (fun _ => (normalized_structures σ hirr).1 hpos)
  · exact even_quaternionic_copies σ ((normalized_structures σ hirr).2 hneg) _ (heven i hneg)

/-- A self-dual simple type descends in any allowed number of copies:
positive types impose no parity condition. -/
theorem selfDual_copies_structure [Fintype G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Irreducible ℂ G V ρ)
    (hself : SelfDual ρ) (n : ℕ)
    (heven : indicatorValue ρ = -1 → Even n) :
    HasConjugateStructure (productRepresentation (fun _ : Fin n => ρ)) 1 := by
  obtain hzero | hpos | hneg := (FrobeniusSchurIndicator.classification ρ hρ).1
  · exact ((FrobeniusSchurIndicator.classification ρ hρ).2.1.mp hzero hself).elim
  · exact product_structure _ 1 (fun _ => (normalized_structures ρ hρ).1 hpos)
  · exact even_quaternionic_copies ρ ((normalized_structures ρ hρ).2 hneg) n (heven hneg)

section DualIndices

variable [Fintype G]

/-- Dual type is unique in a family without repetitions. -/
lemma dualPair_unique (C : Family G) (hC : Valid C) {i j k : Fin C.n}
    (hj : DualPair C i j) (hk : DualPair C i k) : j = k := by
  obtain ⟨e⟩ := hj
  obtain ⟨f⟩ := hk
  exact hC.2 j k ⟨(RegularMultiplicity.idealModuleEquiv _).symm.trans
    ((RegularMultiplicity.moduleEquivOfEquiv (e.symm.trans f)).trans
      (RegularMultiplicity.idealModuleEquiv _))⟩

lemma dualPair_symm (C : Family G) {i j : Fin C.n}
    (hij : DualPair C i j) : DualPair C j i := by
  obtain ⟨e⟩ := hij
  apply (RegularMultiplicity.character_classification _ _).mpr
  funext g
  change ((idealRepresentation (C.space j)).dual).character g =
    (idealRepresentation (C.space i)).character g
  rw [Representation.char_dual]
  have he := congrFun (Representation.char_iso e) g⁻¹
  rw [Representation.char_dual, inv_inv] at he
  exact he.symm

/-- The canonical duality involution on the actual representative indices. -/
def dualIndex (C : Family G) (hC : Valid C) (hEx : Exhaustive.{u,u} C) : Fin C.n → Fin C.n :=
  fun i => Classical.choose (exists_dual_type C hC hEx i)

lemma dualPair_dualIndex (C : Family G) (hC : Valid C) (hEx : Exhaustive.{u,u} C)
    (i : Fin C.n) : DualPair C i (dualIndex C hC hEx i) :=
  Classical.choose_spec (exists_dual_type C hC hEx i)

lemma dualIndex_involutive (C : Family G) (hC : Valid C) (hEx : Exhaustive.{u,u} C) :
    Function.Involutive (dualIndex C hC hEx) := by
  intro i
  apply dualPair_unique C hC (dualPair_dualIndex C hC hEx (dualIndex C hC hEx i))
  exact dualPair_symm C (dualPair_dualIndex C hC hEx i)

lemma dualIndex_fixed_iff_selfDual (C : Family G) (hC : Valid C)
    (hEx : Exhaustive.{u,u} C) (i : Fin C.n) :
    dualIndex C hC hEx i = i ↔ SelfDual (idealRepresentation (C.space i)) := by
  constructor
  · intro hi
    have hd := dualPair_dualIndex C hC hEx i
    rw [hi] at hd
    exact ⟨hd.some.symm⟩
  · intro hi
    exact dualPair_unique C hC (dualPair_dualIndex C hC hEx i) ⟨hi.some.symm⟩

/-- Contragredient blocks are equivariantly conjugate-isomorphic. -/
lemma dualPair_conjugateEquiv (C : Family G) {i j : Fin C.n}
    (hij : DualPair C i j) :
    ∃ e : C.space i ≃ₗ⋆[ℂ] C.space j,
      ∀ g x, e (idealRepresentation (C.space i) g x) =
        idealRepresentation (C.space j) g (e x) := by
  obtain ⟨h, hh⟩ := existsInvariantHermitian (idealRepresentation (C.space i))
  obtain ⟨f⟩ := hij
  refine ⟨(Hermitian.dualEquiv h).trans f.toLinearEquiv, ?_⟩
  intro g x
  change f (Hermitian.dualEquiv h (idealRepresentation (C.space i) g x)) = _
  have he : Hermitian.dualEquiv h (idealRepresentation (C.space i) g x) =
      (idealRepresentation (C.space i)).dual g (Hermitian.dualEquiv h x) := by
    ext y
    change h.toFun y (idealRepresentation (C.space i) g x) =
      h.toFun (idealRepresentation (C.space i) g⁻¹ y) x
    simpa only [Representation.self_inv_apply] using
      hh g (idealRepresentation (C.space i) g⁻¹ y) x
  rw [he]
  exact congrArg (fun t : Module.Dual ℂ (C.space i) →ₗ[ℂ] C.space j =>
    t (Hermitian.dualEquiv h x)) (f.isIntertwining' g)

/-- Equal multiplicities promote conjugate duality to the actual product blocks. -/
lemma dualPair_block_conjugateEquiv (C : Family G)
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hbal : BalancedMultiplicity C ρ)
    {i j : Fin C.n} (hne : i ≠ j) (hij : DualPair C i j) :
    ∃ e : (Fin (multiplicity C ρ i) → C.space i) ≃ₗ⋆[ℂ]
        (Fin (multiplicity C ρ j) → C.space j),
      ∀ g x, e (productRepresentation (fun _ : Fin (multiplicity C ρ i) =>
          idealRepresentation (C.space i)) g x) =
        productRepresentation (fun _ : Fin (multiplicity C ρ j) =>
          idealRepresentation (C.space j)) g (e x) := by
  obtain ⟨e, he⟩ := dualPair_conjugateEquiv C hij
  have hm : multiplicity C ρ i = multiplicity C ρ j := hbal i j hne hij
  let f : (Fin (multiplicity C ρ i) → C.space i) ≃ₗ⋆[ℂ]
      (Fin (multiplicity C ρ i) → C.space j) :=
    { toFun := fun x k => e (x k)
      invFun := fun x k => e.symm (x k)
      left_inv := fun x => funext fun k => e.symm_apply_apply (x k)
      right_inv := fun x => funext fun k => e.apply_symm_apply (x k)
      map_add' := fun x y => funext fun k => e.map_add (x k) (y k)
      map_smul' := fun c x => funext fun k => e.map_smulₛₗ c (x k) }
  let r : (Fin (multiplicity C ρ i) → C.space j) ≃ₗ[ℂ]
      (Fin (multiplicity C ρ j) → C.space j) :=
    LinearEquiv.funCongrLeft ℂ (C.space j) (finCongr hm.symm)
  refine ⟨f.trans r, ?_⟩
  intro g x
  apply funext
  intro k
  exact he g (x (finCongr hm.symm k))

end DualIndices

namespace PairAssembly

variable {ι : Type*} {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]

def castEquiv {i j : ι} (h : i = j) : X i ≃ₗ[ℂ] X j := by
  subst j
  exact LinearEquiv.refl ℂ (X i)


theorem castEquiv_apply {i j : ι} (h : i = j) (x : X i) :
    castEquiv (X := X) h x = h ▸ x := by subst j; rfl

@[simp] theorem castEquiv_refl (i : ι) :
    castEquiv (X := X) (rfl : i = i) = LinearEquiv.refl ℂ (X i) := rfl

def swapMap [LinearOrder ι] (d : ι → ι) (hd : Function.Involutive d)
    (e : ∀ i, X i ≃ₗ⋆[ℂ] X (d i))
    (J : ∀ i, X i →ₗ⋆[ℂ] X i) (i : ι) : X (d i) →ₗ⋆[ℂ] X i :=
  if hi : d i = i then
    (J i).comp (castEquiv (X := X) hi).toLinearMap
  else if i < d i then
    (e i).symm.toLinearMap
  else
    (castEquiv (X := X) (hd i)).toLinearMap.comp (e (d i)).toLinearMap


theorem castEquiv_pi {i j : ι} (h : i = j) (x : ∀ i, X i) :
    castEquiv (X := X) h (x i) = x j := by subst j; rfl

theorem castEquiv_J {i j : ι} (h : i = j) (J : ∀ i, X i →ₗ⋆[ℂ] X i) (x : X i) :
    castEquiv (X := X) h (J i x) = J j (castEquiv (X := X) h x) := by subst j; rfl

theorem castEquiv_e (d : ι → ι) (e : ∀ i, X i ≃ₗ⋆[ℂ] X (d i))
    (x : ∀ i, X i) {i j : ι} (h : i = j) :
    castEquiv (X := X) (congrArg d h) (e i (x i)) = e j (x j) := by subst j; rfl

theorem swapMap_square [LinearOrder ι] (d : ι → ι) (hd : Function.Involutive d)
    (e : ∀ i, X i ≃ₗ⋆[ℂ] X (d i))
    (J : ∀ i, X i →ₗ⋆[ℂ] X i) (hJ : ∀ i, d i = i → ∀ x, J i (J i x) = x)
    (x : ∀ i, X i) (i : ι) :
    swapMap d hd e J i (swapMap d hd e J (d i) (x (d (d i)))) = x i := by
  by_cases hi : d i = i
  · have hdi : d (d i) = d i := congrArg d hi
    simp only [swapMap, dite_eq_left hi, dite_eq_left hdi, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    rw [castEquiv_J hi, castEquiv_pi, castEquiv_pi]
    exact hJ i hi _
  · have hdi : d (d i) ≠ d i := by intro h; exact hi (hd.injective h)
    by_cases hlt : i < d i
    · have hnlt : ¬d i < d (d i) := by simpa only [hd i] using not_lt.mpr hlt.le
      simp only [swapMap, dite_eq_right hi, dite_eq_right hdi, ite_eq_left hlt, ite_eq_right hnlt,
        LinearMap.comp_apply, LinearEquiv.coe_coe]
      change (e i).symm (castEquiv (X := X) (congrArg d (hd i))
        (e (d (d i)) (x (d (d i))))) = x i
      rw [castEquiv_e d e x (hd i)]
      exact (e i).symm_apply_apply _
    · have hlt' : d i < i := lt_of_le_of_ne (le_of_not_gt hlt) hi
      have hlt'' : d i < d (d i) := by simpa only [hd i] using hlt'
      simp only [swapMap, dite_eq_right hi, dite_eq_right hdi, ite_eq_right hlt, ite_eq_left hlt'',
        LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact castEquiv_pi (hd i) x

lemma castEquiv_rho (ρ : ∀ i, Representation ℂ G (X i))
    {i j : ι} (h : i = j) (g : G) (x : X i) :
    castEquiv (X := X) h (ρ i g x) = ρ j g (castEquiv (X := X) h x) := by
  subst j
  rfl

/-- Choose pointwise anti-linear equivalences and fixed-block involutions.
No compatibility is required away from fixed indices: orientation supplies it. -/
theorem choose_pair_data
    (ρ : ∀ i, Representation ℂ G (X i)) (d : ι → ι)
    (hfix : ∀ i, d i = i → HasConjugateStructure (ρ i) 1)
    (hpair : ∀ i, d i ≠ i → ∃ e : X i ≃ₗ⋆[ℂ] X (d i),
      ∀ g x, e (ρ i g x) = ρ (d i) g (e x)) :
    ∃ (J : ∀ i, X i →ₗ⋆[ℂ] X i) (e : ∀ i, X i ≃ₗ⋆[ℂ] X (d i)),
      (∀ i g x, J i (ρ i g x) = ρ i g (J i x)) ∧
      (∀ i, d i = i → ∀ x, J i (J i x) = x) ∧
      (∀ i g x, e i (ρ i g x) = ρ (d i) g (e i x)) := by
  classical
  have hex : ∀ i, ∃ J : X i →ₗ⋆[ℂ] X i,
      (∀ g x, J (ρ i g x) = ρ i g (J x)) ∧
      (d i = i → ∀ x, J (J x) = x) := by
    intro i
    by_cases hi : d i = i
    · obtain ⟨J, hJ, hJJ⟩ := hfix i hi
      exact ⟨J, hJ, fun _ x => by simpa only [one_smul] using hJJ x⟩
    · refine ⟨0, ?_, fun h => (hi h).elim⟩
      intro g x
      simp only [LinearMap.zero_apply, map_zero]
  choose J hJ hJJ using hex
  have he : ∀ i, ∃ e : X i ≃ₗ⋆[ℂ] X (d i),
      ∀ g x, e (ρ i g x) = ρ (d i) g (e x) := by
    intro i
    by_cases hi : d i = i
    · let a : X i ≃ₗ⋆[ℂ] X i := LinearEquiv.ofInvolutive (J i) (hJJ i hi)
      let b : X i ≃ₗ[ℂ] X (d i) := castEquiv (X := X) hi.symm
      refine ⟨a.trans b, ?_⟩
      intro g x
      change b (J i (ρ i g x)) = ρ (d i) g (b (J i x))
      rw [hJ]
      exact castEquiv_rho ρ hi.symm g (J i x)
    · exact hpair i hi
  choose e he using he
  exact ⟨J, e, hJ, hJJ, he⟩

lemma swapMap_equivariant [LinearOrder ι] (d : ι → ι) (hd : Function.Involutive d)
    (ρ : ∀ i, Representation ℂ G (X i))
    (e : ∀ i, X i ≃ₗ⋆[ℂ] X (d i))
    (he : ∀ i g x, e i (ρ i g x) = ρ (d i) g (e i x))
    (J : ∀ i, X i →ₗ⋆[ℂ] X i)
    (hJ : ∀ i, d i = i → ∀ g x, J i (ρ i g x) = ρ i g (J i x))
    (i : ι) (g : G) (x : X (d i)) :
    swapMap d hd e J i (ρ (d i) g x) = ρ i g (swapMap d hd e J i x) := by
  by_cases hi : d i = i
  · simp only [swapMap, dite_eq_left hi, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [castEquiv_rho, hJ i hi]
  · by_cases hlt : i < d i
    · simp only [swapMap, dite_eq_right hi, ite_eq_left hlt, LinearEquiv.coe_coe]
      apply (e i).injective
      rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
    · simp only [swapMap, dite_eq_right hi, ite_eq_right hlt, LinearMap.comp_apply,
        LinearEquiv.coe_coe]
      rw [he, castEquiv_rho]

theorem product_swap_structure [LinearOrder ι] (d : ι → ι)
    (hd : Function.Involutive d) (ρ : ∀ i, Representation ℂ G (X i))
    (e : ∀ i, X i ≃ₗ⋆[ℂ] X (d i))
    (he : ∀ i g x, e i (ρ i g x) = ρ (d i) g (e i x))
    (J : ∀ i, X i →ₗ⋆[ℂ] X i)
    (hJ : ∀ i, d i = i → ∀ g x, J i (ρ i g x) = ρ i g (J i x))
    (hJJ : ∀ i, d i = i → ∀ x, J i (J i x) = x) :
    HasConjugateStructure (productRepresentation ρ) 1 := by
  let K : (∀ i, X i) →ₗ⋆[ℂ] (∀ i, X i) :=
    { toFun := fun x i => swapMap d hd e J i (x (d i))
      map_add' := fun x y => funext fun i => (swapMap d hd e J i).map_add _ _
      map_smul' := fun c x => funext fun i => (swapMap d hd e J i).map_smulₛₗ c _ }
  refine ⟨K, ?_, ?_⟩
  · intro g x
    exact funext fun i => swapMap_equivariant d hd ρ e he J hJ i g _
  · intro x
    apply funext
    intro i
    exact (swapMap_square d hd e J hJJ x i).trans (one_smul ℂ (x i)).symm

/-- An involution on the factors assembles fixed-factor real structures and
conjugate pair equivalences into a real structure on the full product. -/
theorem involutive_product_structure [LinearOrder ι] (d : ι → ι)
    (hd : Function.Involutive d) (ρ : ∀ i, Representation ℂ G (X i))
    (hfix : ∀ i, d i = i → HasConjugateStructure (ρ i) 1)
    (hpair : ∀ i, d i ≠ i → ∃ e : X i ≃ₗ⋆[ℂ] X (d i),
      ∀ g x, e (ρ i g x) = ρ (d i) g (e x)) :
    HasConjugateStructure (productRepresentation ρ) 1 := by
  obtain ⟨J, e, hJ, hJJ, he⟩ := choose_pair_data ρ d hfix hpair
  exact product_swap_structure d hd ρ e he J (fun i _ => hJ i) hJJ

end PairAssembly

/-- The numerical conditions construct an actual equivariant conjugation.
Self-dual summands use their normalized structures; non-self-dual summands
are exchanged in pairs through Hermitian duality. -/
theorem real_structure_construction : realStructureConstructionType.{u,v} := by
  intro G _ _ C hC hEx V _ _ _ ρ hbal heven
  obtain ⟨e⟩ := multiplicity_product_equiv C hC hEx ρ
  apply conjugateStructure_transport e.symm
  let d := dualIndex C hC hEx
  let σ := fun i : Fin C.n => productRepresentation
    (fun _ : Fin (multiplicity C ρ i) => idealRepresentation (C.space i))
  change HasConjugateStructure (productRepresentation σ) 1
  apply PairAssembly.involutive_product_structure d (dualIndex_involutive C hC hEx) σ
  · intro i hi
    have := hC.1 i
    exact selfDual_copies_structure (idealRepresentation (C.space i))
      (RegularMultiplicity.ideal_irreducible (C.space i))
      ((dualIndex_fixed_iff_selfDual C hC hEx i).mp hi)
      (multiplicity C ρ i) (heven i)
  · intro i hi
    exact dualPair_block_conjugateEquiv C ρ hbal (Ne.symm hi)
      (dualPair_dualIndex C hC hEx i)

/-- Equal multiplicities on non-self-dual pairs and even multiplicities on
quaternionic types are exactly the conditions for a real realization. -/
theorem real_form_criterion : realFormCriterionType.{u,v} := by
  intro G _ _ C hC hEx V _ _ _ ρ
  exact ⟨realForm_multiplicity_necessity C hC hEx ρ, fun h =>
    realForm_of_conjugateStructure ρ
      (real_structure_construction C hC hEx ρ h.1 h.2)⟩

end P103.Ch08.GeneralRealForms
