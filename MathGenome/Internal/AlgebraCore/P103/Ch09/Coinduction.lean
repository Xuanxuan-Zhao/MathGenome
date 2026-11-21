import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.Coinduction
import MathGenome.Internal.AlgebraCore.P103.Ch09.InductionModels

noncomputable section
universe u v w x y
namespace P103.Ch09.Coinduction
open scoped MonoidAlgebra
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k H V)

@[simp] theorem action_apply (g : G) (f : Functions H ρ) (x : G) :
    (action H ρ g f).1 x = f.1 (x * g) := rfl

/-- The algebra action on the domain is precisely left multiplication. -/
theorem regular_smul (b : k[H]) (a : k[G]) :
    (regular H).asModuleEquiv (b • (regular H).asModuleEquiv.symm a) =
      subgroupAlgebra H b * a := by
  rw [Representation.asModuleEquiv_map_smul]
  simp only [LinearEquiv.apply_symm_apply]
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp [hb, hc, add_mul]
  | single h c =>
    simpa [regular, restrict] using
      (Representation.asAlgebraHom_ofMulAction_smul_eq_mul
        (MonoidAlgebra.single (h : G) c) a)

/-- Extend a covariant function linearly over the group basis. -/
def functionToIntertwiner (f : Functions H ρ) : (regular H).IntertwiningMap ρ where
  toLinearMap := Finsupp.linearCombination k f.1 ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  isIntertwining' h := by
    ext x
    simpa [regular, restrict, Representation.ofMulAction_single] using f.2 h x

/-- Restriction to the group basis is inverse to linear extension. -/
def intertwinerFunctions : (regular H).IntertwiningMap ρ ≃ₗ[k] Functions H ρ where
  toFun F := ⟨fun x => F (MonoidAlgebra.single x 1), by
    intro h x
    have hh := Representation.IntertwiningMap.isIntertwining _ _ F h (MonoidAlgebra.single x 1)
    simpa [regular, restrict, Representation.ofMulAction_single] using hh⟩
  invFun := functionToIntertwiner H ρ
  left_inv F := by ext x; simp [functionToIntertwiner]
  right_inv f := by ext x; simp [functionToIntertwiner]
  map_add' F F' := by ext x; rfl
  map_smul' c F := by ext x; rfl

/-- The established intertwiner/algebra-linear-map correspondence makes this
an equivalence with the actual Hom over the subgroup algebra. -/
def functionEquivalence : Hom H ρ ≃ₗ[k] Functions H ρ :=
  (Representation.IntertwiningMap.equivLinearMapAsModule (regular H) ρ).symm ≪≫ₗ
    intertwinerFunctions H ρ

@[simp] theorem functionEquivalence_apply (F : Hom H ρ) (x : G) :
    (functionEquivalence H ρ F).1 x = eval H ρ F (MonoidAlgebra.single x 1) := rfl

/-- Right translation transported to the algebra-linear Hom model. -/
def representation : Representation k G (Hom H ρ) where
  toFun g := (functionEquivalence H ρ).symm.toLinearMap ∘ₗ
    action H ρ g ∘ₗ (functionEquivalence H ρ).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro F
    change (functionEquivalence H ρ).symm (action H ρ 1 (functionEquivalence H ρ F)) = F
    rw [map_one]
    exact (functionEquivalence H ρ).symm_apply_apply F
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    change (functionEquivalence H ρ).symm (action H ρ (g * h) (functionEquivalence H ρ F)) =
      (functionEquivalence H ρ).symm (action H ρ g
        (functionEquivalence H ρ ((functionEquivalence H ρ).symm
          (action H ρ h (functionEquivalence H ρ F)))))
    rw [LinearEquiv.apply_symm_apply, map_mul, Module.End.mul_apply]

@[simp] theorem functionEquivalence_action (g : G) (F : Hom H ρ) :
    functionEquivalence H ρ (representation H ρ g F) =
      action H ρ g (functionEquivalence H ρ F) := by
  exact (functionEquivalence H ρ).apply_symm_apply _

/-- Evaluation at any algebra element is coefficient-field linear. -/
def evalLinear (F : Hom H ρ) : k[G] →ₗ[k] V :=
  ρ.asModuleEquiv.toLinearMap ∘ₗ F.restrictScalars k ∘ₗ
    (regular H).asModuleEquiv.symm.toLinearMap

theorem evalLinear_apply (F : Hom H ρ) (a : k[G]) :
    evalLinear H ρ F a = eval H ρ F a := rfl

/-- The group action is right multiplication on every algebra input. -/
theorem representation_eval (g : G) (F : Hom H ρ) (a : k[G]) :
    eval H ρ (representation H ρ g F) a =
      eval H ρ F (a * MonoidAlgebra.single g 1) := by
  change evalLinear H ρ (representation H ρ g F) a =
    evalLinear H ρ F (a * MonoidAlgebra.single g 1)
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_mul, ha, hb]
  | single x c =>
    have hc : MonoidAlgebra.single x c = c • MonoidAlgebra.single x 1 := by simp
    rw [hc, smul_mul_assoc, map_smul, map_smul]
    congr 1
    have h := congrArg (fun f : Functions H ρ => f.1 x)
      (functionEquivalence_action H ρ g F)
    change eval H ρ (representation H ρ g F) (MonoidAlgebra.single x 1) =
      eval H ρ F (MonoidAlgebra.single x 1 * MonoidAlgebra.single g 1)
    change eval H ρ (representation H ρ g F) (MonoidAlgebra.single x 1) =
      (functionEquivalence H ρ F).1 (x * g) at h
    simpa only [functionEquivalence_apply, MonoidAlgebra.single_mul_single, one_mul] using h

def data : Data H ρ where
  representation := representation H ρ
  equivalence := functionEquivalence H ρ
  evaluation := functionEquivalence_apply H ρ
  action_eval := representation_eval H ρ
  equivariant := functionEquivalence_action H ρ

theorem coinduction_construction : Specs.constructionType.{u,v,w} := by
  intro k G _ _ H V _ _ ρ
  exact ⟨⟨data H ρ⟩, regular_smul H⟩

section Adjunction
variable (C : Data H ρ)
variable {W : Type x} [AddCommGroup W] [Module k W]
variable (τ : Representation k G W)

/-- Change from the Hom model to the function model on intertwiner spaces. -/
def functionIntertwiners :
    τ.IntertwiningMap C.representation ≃ₗ[k] τ.IntertwiningMap (action H ρ) where
  toFun Φ :=
    { toLinearMap := C.equivalence.toLinearMap ∘ₗ Φ.toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro z
        exact (congrArg C.equivalence (Representation.IntertwiningMap.isIntertwining _ _ Φ g z)).trans
          (C.equivariant g (Φ z)) }
  invFun Φ :=
    { toLinearMap := C.equivalence.symm.toLinearMap ∘ₗ Φ.toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro z
        apply C.equivalence.injective
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearEquiv.apply_symm_apply, C.equivariant]
        exact Representation.IntertwiningMap.isIntertwining _ _ Φ g z }
  left_inv Φ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    exact C.equivalence.symm_apply_apply _
  right_inv Φ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    exact C.equivalence.apply_symm_apply _
  map_add' Φ Ψ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    exact C.equivalence.map_add _ _
  map_smul' c Φ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    exact C.equivalence.map_smul c _

/-- The inverse to evaluation, in function coordinates. -/
def functionLift (ψ : (restrict H τ).IntertwiningMap ρ) :
    τ.IntertwiningMap (action H ρ) where
  toLinearMap :=
    { toFun z := ⟨fun x => ψ (τ x z), by
        intro h x
        change ψ (τ ((h : G) * x) z) = _
        rw [map_mul, Module.End.mul_apply]
        exact Representation.IntertwiningMap.isIntertwining _ _ ψ h (τ x z)⟩
      map_add' z z' := by ext x; simp
      map_smul' c z := by ext x; simp }
  isIntertwining' g := by
    ext z x
    change ψ (τ x (τ g z)) = ψ (τ (x * g) z)
    rw [map_mul, Module.End.mul_apply]

/-- Evaluation at the identity gives the right adjunction, with no finiteness. -/
def functionAdjunction :
    τ.IntertwiningMap (action H ρ) ≃ₗ[k] (restrict H τ).IntertwiningMap ρ where
  toFun Φ :=
    { toLinearMap := (LinearMap.proj 1).comp ((Functions H ρ).subtype.comp Φ.toLinearMap)
      isIntertwining' h := by
        ext z
        change (Φ (τ h z)).1 1 = ρ h ((Φ z).1 1)
        rw [Φ.isIntertwining]
        simpa only [action_apply, one_mul, mul_one, Subgroup.subtype_apply] using (Φ z).2 h 1 }
  invFun := functionLift H ρ τ
  left_inv Φ := by
    ext z x
    change (Φ (τ x z)).1 1 = (Φ z).1 x
    rw [Representation.IntertwiningMap.isIntertwining _ _ Φ]
    simp only [action_apply, one_mul]
  right_inv ψ := by ext z; change ψ (τ 1 z) = ψ z; simp
  map_add' Φ Ψ := by ext z; rfl
  map_smul' c Φ := by ext z; rfl

/-- The right adjunction on the actual algebra-linear Hom object. -/
def adjunction :
    τ.IntertwiningMap C.representation ≃ₗ[k] (restrict H τ).IntertwiningMap ρ :=
  functionIntertwiners H ρ C τ ≪≫ₗ functionAdjunction H ρ τ

@[simp] theorem adjunction_apply (Φ : τ.IntertwiningMap C.representation) (z : W) :
    adjunction H ρ C τ Φ z = eval H ρ (Φ z) 1 := by
  change (C.equivalence (Φ z)).1 1 = _
  rw [C.evaluation]
  congr 1

@[simp] theorem adjunction_symm_basis (ψ : (restrict H τ).IntertwiningMap ρ)
    (z : W) (x : G) :
    eval H ρ ((adjunction H ρ C τ).symm ψ z) (MonoidAlgebra.single x 1) =
      ψ (τ x z) := by
  rw [← C.evaluation]
  exact congrArg (fun f : Functions H ρ => f.1 x) (C.equivalence.apply_symm_apply _)

/-- Linear maps on the group algebra expand in its finite-support basis. -/
theorem eval_sum (F : Hom H ρ) (a : k[G]) :
    eval H ρ F a = a.coeff.sum (fun x c => c • eval H ρ F (MonoidAlgebra.single x 1)) := by
  change evalLinear H ρ F a = _
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single a]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro x _
  have hc : MonoidAlgebra.single x (a.coeff x) = a.coeff x • MonoidAlgebra.single x 1 := by simp
  rw [hc, map_smul]
  rfl

theorem adjunction_symm_eval (ψ : (restrict H τ).IntertwiningMap ρ) (z : W) (a : k[G]) :
    eval H ρ ((adjunction H ρ C τ).symm ψ z) a =
      a.coeff.sum (fun x c => c • ψ (τ x z)) := by
  rw [eval_sum]
  simp only [adjunction_symm_basis]

end Adjunction

theorem right_adjunction : Specs.adjunctionType.{u,v,w,x} := by
  intro k G _ _ H V _ _ ρ C W _ _ τ
  exact ⟨adjunction H ρ C τ, adjunction_apply H ρ C τ, adjunction_symm_eval H ρ C τ⟩

section Naturality
variable {V' : Type y} [AddCommGroup V'] [Module k V']
variable {ρ' : Representation k H V'}
variable (C : Data H ρ) (C' : Data H ρ') (f : ρ.IntertwiningMap ρ')

/-- Coinduction sends an intertwiner to postcomposition, in Hom coordinates. -/
def postcompose : C.representation.IntertwiningMap C'.representation where
  toLinearMap := C'.equivalence.symm.toLinearMap ∘ₗ
    (Representation.coindMap H.subtype f).toLinearMap ∘ₗ C.equivalence.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro F
    apply C'.equivalence.injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply, C.equivariant, C'.equivariant]
    exact Representation.IntertwiningMap.isIntertwining _ _
      (Representation.coindMap H.subtype f) g _

theorem postcompose_eval (F : Hom H ρ) (a : k[G]) :
    eval H ρ' (postcompose H ρ C C' f F) a = f (eval H ρ F a) := by
  change evalLinear H ρ' (postcompose H ρ C C' f F) a = f (evalLinear H ρ F a)
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single x c =>
    have hc : MonoidAlgebra.single x c = c • MonoidAlgebra.single x 1 := by simp
    rw [hc, map_smul, map_smul, map_smul]
    congr 1
    change eval H ρ' (postcompose H ρ C C' f F) (MonoidAlgebra.single x 1) =
      f (eval H ρ F (MonoidAlgebra.single x 1))
    rw [← C'.evaluation, ← C.evaluation]
    change (C'.equivalence (C'.equivalence.symm
      (Representation.coindMap H.subtype f (C.equivalence F)))).1 x = _
    rw [LinearEquiv.apply_symm_apply]
    rfl

end Naturality

theorem right_adjunction_naturality : Specs.adjunctionNaturalityType.{u,v,w,x,y} := by
  intro k G _ _ H V _ _ ρ V' _ _ ρ' C C' f
  refine ⟨postcompose H ρ C C' f, postcompose_eval H ρ C C' f, ?_⟩
  intro W _ _ τ
  refine ⟨adjunction H ρ C τ, adjunction H ρ' C' τ,
    adjunction_apply H ρ C τ, adjunction_apply H ρ' C' τ, ?_, ?_⟩
  · intro Φ
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change adjunction H ρ' C' τ ((postcompose H ρ C C' f).comp Φ) z =
      f (adjunction H ρ C τ Φ z)
    rw [adjunction_apply, Representation.IntertwiningMap.comp_apply,
      postcompose_eval, adjunction_apply]
  · intro W' _ _ τ' p
    refine ⟨adjunction H ρ C τ', adjunction_apply H ρ C τ', ?_⟩
    intro Φ
    apply LinearMap.ext
    intro z
    simp only [Representation.IntertwiningMap.toLinearMap_apply, LinearMap.coe_comp,
      Function.comp_apply, adjunction_apply, Representation.IntertwiningMap.comp_apply]

/-- Inversion takes finite left-coset support to finite right-coset support. -/
theorem finite_right_of_left (f : G → V)
    (hf : (QuotientGroup.mk '' Function.support f : Set (G ⧸ H)).Finite) :
    (rightCoset H '' Function.support (fun x => f x⁻¹)).Finite := by
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  apply (hf.image e.symm).subset
  rintro q ⟨x, hx, rfl⟩
  refine ⟨QuotientGroup.mk x⁻¹, ⟨x⁻¹, hx, rfl⟩, ?_⟩
  change rightCoset H ((x⁻¹)⁻¹) = rightCoset H x
  rw [inv_inv]

/-- Inversion in the opposite direction exchanges the support conditions too. -/
theorem finite_left_of_right (f : G → V)
    (hf : (rightCoset H '' Function.support f).Finite) :
    (QuotientGroup.mk '' Function.support (fun x => f x⁻¹) : Set (G ⧸ H)).Finite := by
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  apply (hf.image e).subset
  rintro q ⟨x, hx, rfl⟩
  refine ⟨rightCoset H x⁻¹, ⟨x⁻¹, hx, rfl⟩, ?_⟩
  change QuotientGroup.mk ((x⁻¹)⁻¹) = (QuotientGroup.mk x : G ⧸ H)
  rw [inv_inv]

/-- The representative-free inverse-coordinate transform. -/
def invertFunctions : functions H ρ ≃ₗ[k] finiteFunctions H ρ where
  toFun f := ⟨⟨fun x => f.1 x⁻¹, by
    intro h x
    simpa using f.2.1 x⁻¹ h⁻¹⟩, finite_right_of_left H f.1 f.2.2⟩
  invFun F := ⟨fun x => F.1.1 x⁻¹, by
    refine ⟨?_, finite_left_of_right H F.1.1 F.2⟩
    intro x h
    simpa using F.1.2 h⁻¹ x⁻¹⟩
  left_inv f := by ext x; exact congrArg f.1 (inv_inv x)
  right_inv F := by ext x; exact congrArg F.1.1 (inv_inv x)
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

@[simp] theorem invertFunctions_apply (f : functions H ρ) (x : G) :
    (invertFunctions H ρ f).1.1 x = f.1 x⁻¹ := rfl

@[simp] theorem invertFunctions_symm_apply (F : finiteFunctions H ρ) (x : G) :
    ((invertFunctions H ρ).symm F).1 x = F.1.1 x⁻¹ := rfl

/-- The transform intertwines left translation with right translation. -/
theorem inversion_equivariant (g : G) (f : functions H ρ) :
    (invertFunctions H ρ (functionAction H ρ g f)).1 =
      action H ρ g (invertFunctions H ρ f).1 := by
  apply Subtype.ext
  funext x
  change f.1 (g⁻¹ * x⁻¹) = f.1 ((x * g)⁻¹)
  rw [mul_inv_rev]

/-- Finite right-coset support is stable under the coinduced action. -/
theorem finiteSupport_action (g : G) (F : Functions H ρ)
    (hF : FiniteSupport H ρ F) : FiniteSupport H ρ (action H ρ g F) := by
  let z : finiteFunctions H ρ := ⟨F, hF⟩
  have hh := (invertFunctions H ρ (functionAction H ρ g ((invertFunctions H ρ).symm z))).2
  rw [inversion_equivariant, LinearEquiv.apply_symm_apply] at hh
  exact hh

/-- Thus the finite support subspace is an actual subrepresentation. -/
def finiteSubrepresentation : Subrepresentation (action H ρ) where
  toSubmodule := finiteFunctions H ρ
  apply_mem_toSubmodule g := finiteSupport_action H ρ g

/-- Finite index alone makes every coinduced function finitely supported modulo H. -/
theorem finiteSupport_of_finiteIndex [H.FiniteIndex] (F : Functions H ρ) :
    FiniteSupport H ρ F := by
  letI : Finite (RightCosets H) :=
    Finite.of_equiv (G ⧸ H) (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  exact Set.toFinite _

section Comparison
variable (C : Data H ρ) (D : InductionData H ρ) (E : FunctionModelData H ρ D)

/-- The tensor/function equivalence followed by inversion. -/
def finiteComparison : letI := D.module; Induced H ρ ≃ₗ[k] finiteFunctions H ρ :=
  E.equivalence ≪≫ₗ invertFunctions H ρ

/-- Inclusion of induction into the actual algebra-linear coinduction. -/
def embeddingLinear : letI := D.module; Induced H ρ →ₗ[k] Hom H ρ := by
  letI := D.module
  exact C.equivalence.symm.toLinearMap ∘ₗ (finiteFunctions H ρ).subtype ∘ₗ
    (finiteComparison H ρ D E).toLinearMap

@[simp] theorem embeddingLinear_formula (z : Induced H ρ) (x : G) :
    letI := D.module;
    (C.equivalence (embeddingLinear H ρ C D E z)).1 x = (E.equivalence z).1 x⁻¹ :=
  congrArg (fun f : Functions H ρ => f.1 x) (C.equivalence.apply_symm_apply _)

/-- Left tensor multiplication becomes right translation after inversion. -/
def embedding : letI := D.module; D.representation.IntertwiningMap C.representation := by
  letI := D.module
  refine { toLinearMap := embeddingLinear H ρ C D E, isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro z
  apply C.equivalence.injective
  apply Subtype.ext
  funext x
  change (C.equivalence (embeddingLinear H ρ C D E (D.representation g z))).1 x =
    (C.equivalence (C.representation g (embeddingLinear H ρ C D E z))).1 x
  rw [C.equivariant, action_apply, embeddingLinear_formula, embeddingLinear_formula]
  rw [E.equivariant, mul_inv_rev]

@[simp] theorem embedding_formula (z : Induced H ρ) (x : G) :
    letI := D.module;
    (C.equivalence (embedding H ρ C D E z)).1 x = (E.equivalence z).1 x⁻¹ :=
  embeddingLinear_formula H ρ C D E z x

theorem embedding_injective : letI := D.module; Function.Injective (embedding H ρ C D E) := by
  letI := D.module
  intro z z' h
  apply (finiteComparison H ρ D E).injective
  apply Subtype.ext
  exact C.equivalence.symm.injective h

/-- The image consists of exactly the finite-right-coset-support functions. -/
theorem embedding_range (F : Hom H ρ) :
    letI := D.module;
    (∃ z, embedding H ρ C D E z = F) ↔ FiniteSupport H ρ (C.equivalence F) := by
  letI := D.module
  constructor
  · rintro ⟨z, rfl⟩
    have hh := (finiteComparison H ρ D E z).2
    change FiniteSupport H ρ
      (C.equivalence (C.equivalence.symm (finiteComparison H ρ D E z).1))
    rwa [LinearEquiv.apply_symm_apply]
  · intro hF
    refine ⟨(finiteComparison H ρ D E).symm ⟨C.equivalence F, hF⟩, ?_⟩
    change C.equivalence.symm
      ((finiteComparison H ρ D E)
        ((finiteComparison H ρ D E).symm ⟨C.equivalence F, hF⟩)).1 = F
    rw [LinearEquiv.apply_symm_apply]
    exact C.equivalence.symm_apply_apply F

theorem embedding_surjective [H.FiniteIndex] :
    letI := D.module; Function.Surjective (embedding H ρ C D E) := by
  letI := D.module
  intro F
  exact (embedding_range H ρ C D E F).2 (finiteSupport_of_finiteIndex H ρ _)

/-- At finite index this same natural inclusion is an isomorphism. -/
def finiteIndexEquivalence [H.FiniteIndex] :
    letI := D.module; Induced H ρ ≃ₗ[k] Hom H ρ := by
  letI := D.module
  exact LinearEquiv.ofBijective (embedding H ρ C D E).toLinearMap
    ⟨embedding_injective H ρ C D E, embedding_surjective H ρ C D E⟩

end Comparison

theorem induction_coinduction_comparison : Specs.comparisonType.{u,v,w} := by
  intro k G _ _ H V _ _ ρ C D E
  letI := D.module
  refine ⟨embedding H ρ C D E, embedding_injective H ρ C D E,
    embedding_formula H ρ C D E, embedding_range H ρ C D E, ?_, ?_⟩
  · intro g F hF
    rw [C.equivariant]
    exact finiteSupport_action H ρ g _ hF
  · intro _
    exact ⟨embedding_surjective H ρ C D E,
      finiteIndexEquivalence H ρ C D E, fun _ => rfl⟩

theorem induction_coinduction_naturality : Specs.comparisonNaturalityType.{u,v,w,x} := by
  intro k G _ _ H V _ _ ρ W _ _ σ f C C' D D' E E'
  letI := D.module
  letI := D'.module
  intro F hF J J' Q hJ hJ' hQ z
  apply C'.equivalence.injective
  apply Subtype.ext
  funext x
  calc
    (C'.equivalence (J' (F z))).1 x = (E'.equivalence (F z)).1 x⁻¹ := hJ' _ _
    _ = f ((E.equivalence z).1 x⁻¹) :=
      P103.Ch09.model_naturality H ρ σ D D' E E' f F hF z x⁻¹
    _ = f ((C.equivalence (J z)).1 x) := congrArg f (hJ z x).symm
    _ = (C'.equivalence (Q (J z))).1 x := by
      rw [C'.evaluation, hQ, C.evaluation]

end P103.Ch09.Coinduction
