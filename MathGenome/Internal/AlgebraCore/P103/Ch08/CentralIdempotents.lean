import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.CentralIdempotents
import MathGenome.Internal.AlgebraCore.P103.Ch08.FourierTransform
import Mathlib.LinearAlgebra.Projection

noncomputable section
universe u v w x
namespace P103.Ch08.CentralIdempotents
open scoped MonoidAlgebra
open FourierSpecs CentralIdempotentSpecs

/-- Fourier inversion of a single identity block is the character sum in the source. -/
theorem inverse_block {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (i : Fin C.n) :
    ∀ g, inverseCoefficient C (block C i) g = (idempotent C i).coeff g := by
  classical
  intro g
  simp [inverseCoefficient, block, idempotent, CharacterSpecs.characterValue,
    MonoidAlgebra.coeff_sum, div_eq_mul_inv, mul_comm,
    apply_ite, Finsupp.single_apply, mul_assoc]

/-- The specified character sum acts as identity on its own type and zero on the others. -/
theorem block_action : blockActionType.{u,v} := by
  intro G _ _ C hC hEx i
  obtain ⟨E, hE, _, hInv, _⟩ := FourierTransform.fourier C hC hEx
  have h : E.symm (block C i) = idempotent C i := by
    ext g
    exact (hInv _ g).trans (inverse_block C i g)
  rw [← h]
  have ha (a : ℂ[G]) : action C a = E a :=
    funext fun j => (hE a j).symm
  rw [ha]
  exact E.apply_symm_apply _

/-- The identity/zero tuples commute with all tuples of endomorphisms. -/
theorem central : centralType.{u,v} := by
  intro G _ _ C hC hEx i
  apply Subalgebra.mem_center_iff.mpr
  intro a
  apply FourierTransform.action_injective C hC hEx
  rw [map_mul, map_mul, block_action C hC hEx]
  ext j
  by_cases h : j = i <;> simp [block, h]

theorem idempotent_mul : idempotentType.{u,v} := by
  intro G _ _ C hC hEx i
  apply FourierTransform.action_injective C hC hEx
  rw [map_mul, block_action C hC hEx]
  ext j
  by_cases h : j = i <;> simp [block, h]

theorem orthogonal : orthogonalType.{u,v} := by
  intro G _ _ C hC hEx i j hij
  apply FourierTransform.action_injective C hC hEx
  rw [map_mul, map_zero, block_action C hC hEx, block_action C hC hEx]
  ext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [block]

theorem sum_eq_one : sumType.{u,v} := by
  intro G _ _ C hC hEx
  classical
  apply FourierTransform.action_injective C hC hEx
  rw [map_sum, map_one]
  simp_rw [block_action C hC hEx]
  ext j
  simp [block]


/-- Central elements act by scalars on each irreducible, with no extra
finite-dimensionality hypothesis: it follows from finiteness of the group. -/
theorem central_scalar {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (a : ℂ[G])
    (ha : a ∈ Subalgebra.center ℂ ℂ[G]) (i : Fin C.n) :
    ∃ c : ℂ, action C a i = c • (1 : Module.End ℂ (C.space i)) := by
  have := RegularMultiplicity.finite_dimensional (C.representation i) (hC.1 i)
  let f := Representation.IntertwiningMap.centralAlgebraMul (C.representation i) ha
  obtain ⟨c, hc, _⟩ := Schur.uniqueScalar (C.representation i) (hC.1 i) f
  exact ⟨c, congrArg Representation.IntertwiningMap.toLinearMap hc⟩

/-- A central idempotent has only zero and identity blocks. -/
theorem central_idempotent_blocks {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (a : ℂ[G])
    (ha : a ∈ Subalgebra.center ℂ ℂ[G]) (haa : a * a = a) (i : Fin C.n) :
    action C a i = 0 ∨ action C a i = 1 := by
  have : Nontrivial (C.space i) := (hC.1 i).1
  obtain ⟨c, hc⟩ := central_scalar C hC a ha i
  have hm : (c • (1 : Module.End ℂ (C.space i))) * (c • 1) = c • 1 := by
    rw [← hc]
    change (action C a * action C a) i = action C a i
    rw [← map_mul, haa]
  have hc2 : c * c = c := by
    apply smul_left_injective ℂ (show (1 : Module.End ℂ (C.space i)) ≠ 0 from one_ne_zero)
    simpa [smul_smul, smul_mul_smul_comm] using hm
  rcases (IsIdempotentElem.iff_eq_zero_or_one.mp hc2) with h | h
  · left; simpa [h] using hc
  · right; simpa [h] using hc

/-- Nonzeroness is guaranteed by the nonzero irreducible in the selected block. -/
theorem idempotent_ne_zero {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C) (i : Fin C.n) :
    idempotent C i ≠ 0 := by
  have : Nontrivial (C.space i) := (hC.1 i).1
  intro h
  have he := congrFun (block_action C hC hEx i) i
  rw [h, map_zero] at he
  simp [block] at he

/-- Exactly the displayed character sums are primitive central idempotents. -/
theorem primitive : primitiveType.{u,v} := by
  intro G _ _ C hC hEx e
  classical
  have inj := FourierTransform.action_injective C hC hEx
  constructor
  · rintro ⟨he, hee, hne, hp⟩
    obtain ⟨i, hi⟩ : ∃ i, action C e i ≠ 0 := by
      by_contra! h
      apply hne
      apply inj
      funext i
      simpa using h i
    have hi1 := (central_idempotent_blocks C hC e he hee i).resolve_left (hi)
    have hle : idempotent C i * e = idempotent C i := by
      apply inj
      rw [map_mul, block_action C hC hEx]
      funext j
      by_cases hji : j = i
      · subst j; simp [block, hi1]
      · simp [block, hji]
    rcases hp (idempotent C i) (central C hC hEx i)
      (idempotent_mul C hC hEx i) hle with h | h
    · exact False.elim (idempotent_ne_zero C hC hEx i h)
    · exact ⟨i, h.symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨central C hC hEx i, idempotent_mul C hC hEx i,
      idempotent_ne_zero C hC hEx i, ?_⟩
    intro f hf hff hfi
    have hblocks := congrArg (action C) hfi
    rw [map_mul, block_action C hC hEx] at hblocks
    have hoff (j) (hji : j ≠ i) : action C f j = 0 := by
      have h := congrFun hblocks j
      simpa [block, hji] using h.symm
    rcases central_idempotent_blocks C hC f hf hff i with h | h
    · left
      apply inj
      funext j
      by_cases hji : j = i
      · subst j; simpa using h
      · simpa using hoff j hji
    · right
      apply inj
      rw [block_action C hC hEx]
      funext j
      by_cases hji : j = i
      · subst j; simpa [block] using h
      · simpa [block, hji] using hoff j hji


/-- Centrality can be checked directly on conjugate coefficients, without
any choice of a family of irreducibles. -/
theorem center_coefficients : centerCoefficientsType.{u} := by
  intro G _ a
  constructor
  · intro ha g h
    have he := congrArg (fun b : ℂ[G] => b.coeff (h * g))
      (Subalgebra.mem_center_iff.mp ha (MonoidAlgebra.single h 1))
    simpa [mul_assoc] using he.symm
  · intro ha
    apply Subalgebra.mem_center_iff.mpr
    intro b
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b c hb hc => simp [add_mul, mul_add, hb, hc]
    | single g c =>
      ext h
      have he := ha (g⁻¹ * h) g
      simp only [← mul_assoc, mul_inv_cancel, one_mul] at he
      simp [he, mul_comm]

/-- Coefficients of a central element descend to the conjugacy quotient. -/
theorem center_coeff_eq_of_class_eq {G : Type u} [Group G] (a : ℂ[G])
    (ha : a ∈ Subalgebra.center ℂ ℂ[G]) {g h : G}
    (hgh : ConjClasses.mk g = ConjClasses.mk h) : a.coeff g = a.coeff h := by
  obtain ⟨s, hs⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hgh)
  rw [← hs]
  exact (center_coefficients a |>.mp ha g s).symm

/-- Turn a function on conjugacy classes into the element with those coefficients. -/
def classFunctionElement {G : Type u} [Group G] [Fintype G]
    (f : ConjClasses G → ℂ) : ℂ[G] :=
  ∑ g : G, MonoidAlgebra.single g (f (ConjClasses.mk g))

theorem classFunctionElement_coeff {G : Type u} [Group G] [Fintype G]
    (f : ConjClasses G → ℂ) (g : G) :
    (classFunctionElement f).coeff g = f (ConjClasses.mk g) := by
  classical
  simp [classFunctionElement, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem classFunctionElement_central {G : Type u} [Group G] [Fintype G]
    (f : ConjClasses G → ℂ) :
    classFunctionElement f ∈ Subalgebra.center ℂ ℂ[G] := by
  apply (center_coefficients _).mpr
  intro g h
  simp only [classFunctionElement_coeff]
  congr 1
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact (isConj_iff.mpr ⟨h, rfl⟩).symm

/-- The coefficientwise identification of the center with functions on classes. -/
def centerClassEquiv {G : Type u} [Group G] [Fintype G] :
    Subalgebra.center ℂ ℂ[G] ≃ₗ[ℂ] (ConjClasses G → ℂ) where
  toFun a D := a.val.coeff (Classical.choose (ConjClasses.exists_rep D))
  invFun f := ⟨classFunctionElement f, classFunctionElement_central f⟩
  left_inv a := by
    apply Subtype.ext
    ext g
    rw [classFunctionElement_coeff]
    apply center_coeff_eq_of_class_eq _ a.property
    exact Classical.choose_spec (ConjClasses.exists_rep (ConjClasses.mk g))
  right_inv f := by
    funext D
    change (classFunctionElement f).coeff
      (Classical.choose (ConjClasses.exists_rep D)) = f D
    rw [classFunctionElement_coeff, Classical.choose_spec (ConjClasses.exists_rep D)]
  map_add' a b := by ext D; rfl
  map_smul' c a := by ext D; rfl

/-- The usual class sums are a complex basis of the actual algebra center. -/
theorem class_sum_basis : classSumBasisType.{u} := by
  intro G _ _
  classical
  let E := centerClassEquiv (G := G)
  refine ⟨Module.Basis.ofEquivFun E, ?_⟩
  intro D
  rw [Module.Basis.coe_ofEquivFun]
  change classFunctionElement (Pi.single D 1) = classSum D
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : ConjClasses.mk g = D
  · simp [hg]
  · simp [hg]


/-- Transfer a block action through an actual equivariant equivalence. -/
theorem action_on_equivalent {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C)
    {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (i j : Fin C.n) (e : (C.representation j).Equiv ρ) :
    ρ.asAlgebraHom (idempotent C i) = if j = i then 1 else 0 := by
  have h : (C.representation j).asAlgebraHom (idempotent C i) =
      if j = i then 1 else 0 := congrFun (block_action C hC hEx i) j
  rw [← FourierTransform.equiv_conj_action e, h]
  by_cases hj : j = i
  · simp only [ite_eq_left hj]
    ext x
    change e.toLinearEquiv (e.toLinearEquiv.symm x) = x
    exact e.toLinearEquiv.apply_symm_apply x
  · simp [hj]

/-- The projection is identity or zero on every irreducible, including
irreducibles presented in a different universe from the chosen family. -/
theorem simple_action : simpleActionType.{u,v,w} := by
  intro G _ _ C hC hEx X _ _ ρ hρ i
  constructor
  · rintro ⟨e⟩
    simpa using action_on_equivalent C hC hEx ρ i i e
  · intro h
    obtain ⟨j, ⟨e⟩⟩ := FourierTransform.complete_exhaustive C hEx ρ hρ
    have hji : j ≠ i := by rintro rfl; exact h ⟨e⟩
    simpa [hji] using action_on_equivalent C hC hEx ρ i j e

/-- The algebra module on a restricted representation is the inherited
submodule, through the identity on vectors. -/
def subrepresentationModuleEquiv {G : Type u} [Group G]
    {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (U : Subrepresentation ρ) :
    U.toRepresentation.asModule ≃ₗ[ℂ[G]] U.asSubmodule where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    exact restriction_compatibility ρ U a x

/-- A simple algebra submodule restricts to a nonzero irreducible
subrepresentation of the original action. -/
theorem irreducible_submodule {G : Type u} [Group G]
    {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S] :
    Irreducible ℂ G (Subrepresentation.ofSubmodule' S).toSubmodule
      (Subrepresentation.ofSubmodule' S).toRepresentation := by
  let U := Subrepresentation.ofSubmodule' S
  have : IsSimpleModule ℂ[G] U.asSubmodule := by
    change IsSimpleModule ℂ[G] S
    infer_instance
  have : IsSimpleModule ℂ[G] U.toRepresentation.asModule :=
    IsSimpleModule.congr (subrepresentationModuleEquiv ρ U)
  have : Representation.IsIrreducible U.toRepresentation :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr inferInstance
  exact ⟨IsSimpleModule.nontrivial ℂ[G] U.toRepresentation.asModule,
    fun V => eq_bot_or_eq_top V⟩

/-- Arbitrary-dimensional Maschke semisimplicity supplies a spanning family
of irreducible subrepresentations. No finiteness is imposed on this family. -/
theorem irreducibles_span {G : Type u} [Group G] [Fintype G]
    {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) :
    (⨆ (U : Subrepresentation ρ)
      (_ : Irreducible ℂ G U.toSubmodule U.toRepresentation), U.toSubmodule) = ⊤ := by
  have := Maschke.semisimple ρ (by exact_mod_cast Nat.card_pos.ne')
  have h := IsSemisimpleModule.sSup_simples_eq_top ℂ[G] ρ.asModule
  rw [sSup_eq_iSup'] at h
  have ht : (⨆ S : {S : Submodule ℂ[G] ρ.asModule | IsSimpleModule ℂ[G] S},
      (Subrepresentation.ofSubmodule' S.val).toSubmodule) = ⊤ := by
    simpa only [Submodule.restrictScalars_iSup, Submodule.restrictScalars_top] using!
      congrArg (Submodule.restrictScalars ℂ) h
  apply top_unique
  rw [← ht]
  apply iSup_le
  intro S
  have : IsSimpleModule ℂ[G] S.val := S.property
  exact le_iSup_of_le (Subrepresentation.ofSubmodule' S.val)
    (le_iSup_of_le (irreducible_submodule ρ S.val) le_rfl)


/-- The algebra extension of the restricted action is the restriction of
the algebra extension, on every vector. -/
theorem restriction_action {G : Type u} [Group G]
    {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (U : Subrepresentation ρ) (a : ℂ[G]) (x : U.toSubmodule) :
    (U.toRepresentation.asAlgebraHom a x : X) = ρ.asAlgebraHom a x :=
  restriction_compatibility ρ U a x

/-- Every copy of the selected type is fixed pointwise, hence lies in the range. -/
theorem isotypic_le_range {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C)
    {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (i : Fin C.n) :
    isotypic C ρ i ≤ LinearMap.range (ρ.asAlgebraHom (idempotent C i)) := by
  apply iSup_le
  intro U
  apply iSup_le
  rintro ⟨e⟩ x hx
  have ha : U.toRepresentation.asAlgebraHom (idempotent C i) = 1 := by
    simpa using action_on_equivalent C hC hEx U.toRepresentation i i e
  have hfix := restriction_action ρ U (idempotent C i) ⟨x, hx⟩
  rw [ha] at hfix
  exact ⟨x, hfix.symm⟩

/-- For any spanning family of irreducible subrepresentations, the image of
an idempotent lies in the sum of just the summands of the corresponding type.
The family and the ambient representation may both be infinite-dimensional. -/
theorem range_le_type_sum {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C)
    {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    {J : Type x} (U : J → Subrepresentation ρ)
    (hU : ∀ j, Irreducible ℂ G (U j).toSubmodule (U j).toRepresentation)
    (htop : (⨆ j, (U j).toSubmodule) = ⊤) (i : Fin C.n) :
    LinearMap.range (ρ.asAlgebraHom (idempotent C i)) ≤
      ⨆ (j : J) (_ : Nonempty ((C.representation i).Equiv (U j).toRepresentation)),
        (U j).toSubmodule := by
  classical
  rw [← Submodule.map_top, ← htop, Submodule.map_iSup]
  apply iSup_le
  intro j x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hact := restriction_action ρ (U j) (idempotent C i) ⟨y, hy⟩
  by_cases hj : Nonempty ((C.representation i).Equiv (U j).toRepresentation)
  · have ha := (simple_action C hC hEx (U j).toRepresentation (hU j) i).1 hj
    rw [ha] at hact
    rw [← hact]
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj hy)
  · have ha := (simple_action C hC hEx (U j).toRepresentation (hU j) i).2 hj
    rw [ha] at hact
    rw [← hact]
    exact Submodule.zero_mem _

/-- The image is exactly the sum of all copies of the selected type,
using arbitrary-dimensional Maschke semisimplicity for the reverse inclusion. -/
theorem range_eq_isotypic {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C)
    {X : Type w} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (i : Fin C.n) :
    LinearMap.range (ρ.asAlgebraHom (idempotent C i)) = isotypic C ρ i := by
  apply le_antisymm ?_ (isotypic_le_range C hC hEx ρ i)
  let J := {U : Subrepresentation ρ | Irreducible ℂ G U.toSubmodule U.toRepresentation}
  have htop : (⨆ j : J, j.val.toSubmodule) = ⊤ := by
    rw [iSup_subtype]
    exact irreducibles_span ρ
  apply (range_le_type_sum C hC hEx ρ (fun j : J => j.val)
    (fun j => j.property) htop i).trans
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  exact le_iSup_of_le j.val (le_iSup_of_le hj le_rfl)

/-- The action is the projection onto the intrinsic isotypic component,
along its kernel. -/
theorem isotypic_projection : isotypicProjectionType.{u,v,w} := by
  intro G _ _ C hC hEx X _ _ ρ i
  let p := ρ.asAlgebraHom (idempotent C i)
  have hp : IsIdempotentElem p := by
    change p * p = p
    dsimp [p]
    rw [← map_mul, idempotent_mul C hC hEx]
  have hr := range_eq_isotypic C hC hEx ρ i
  refine ⟨hr, hp, ?_, ?_⟩
  · intro x hx
    exact (LinearMap.IsIdempotentElem.mem_range_iff hp).mp (hr.symm ▸ hx)
  · rw [← hr]
    exact LinearMap.IsIdempotentElem.isCompl hp

/-- In every internal direct-sum decomposition, the sum of the summands of
the chosen type is the same intrinsic component. -/
theorem decomposition : decompositionType.{u,v,w,x} := by
  intro G _ _ C hC hEx X _ _ ρ J U hU _ htop i
  apply le_antisymm
  · rw [← range_eq_isotypic C hC hEx ρ i]
    exact range_le_type_sum C hC hEx ρ U hU htop i
  · apply iSup_le
    intro j
    apply iSup_le
    intro hj
    exact le_iSup_of_le (U j) (le_iSup_of_le hj le_rfl)


/-- The primitive idempotents give the scalar-coordinate basis of the center. -/
theorem idempotent_basis : idempotentBasisType.{u,v} := by
  intro G _ _ C hC hEx
  classical
  let b : Fin C.n → Subalgebra.center ℂ ℂ[G] :=
    fun i => ⟨idempotent C i, central C hC hEx i⟩
  let L := Fintype.linearCombination ℂ b
  have hL (f : Fin C.n → ℂ) (j : Fin C.n) :
      action C (L f).val j = f j • (1 : Module.End ℂ (C.space j)) := by
    have hv : (L f).val = ∑ i, f i • idempotent C i := by
      simp [L, b, Fintype.linearCombination_apply]
    rw [hv, map_sum]
    simp_rw [map_smul, block_action C hC hEx]
    simp [block, Finset.sum_apply, smul_ite]
  have hbij : Function.Bijective L := by
    constructor
    · intro f g hfg
      funext j
      have : Nontrivial (C.space j) := (hC.1 j).1
      have he := congrArg (fun a : Subalgebra.center ℂ ℂ[G] => action C a.val j) hfg
      rw [hL, hL] at he
      exact smul_left_injective ℂ (show (1 : Module.End ℂ (C.space j)) ≠ 0 from one_ne_zero) he
    · intro a
      choose c hc using fun j => central_scalar C hC a.val a.property j
      refine ⟨c, Subtype.ext ?_⟩
      apply FourierTransform.action_injective C hC hEx
      funext j
      exact (hL c j).trans (hc j).symm
  refine ⟨(Pi.basisFun ℂ (Fin C.n)).map (LinearEquiv.ofBijective L hbij), ?_⟩
  intro i
  simp [L, b, Module.Basis.map_apply]

end P103.Ch08.CentralIdempotents
