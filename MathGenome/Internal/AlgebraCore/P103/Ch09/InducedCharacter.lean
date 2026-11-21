import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InducedCharacter
import MathGenome.Internal.AlgebraCore.P103.Ch09.InductionModels
import MathGenome.Internal.AlgebraCore.P103.Ch08.CharacterConstructions

noncomputable section
open scoped BigOperators
open scoped Classical
universe u v w
namespace P103.Ch09
namespace InducedCharacterProof

/-- Trace on a finite product is the sum of its diagonal block traces. -/
theorem trace_pi {K : Type*} [Field K] {I : Type*} [Fintype I]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (L : (I → W) →ₗ[K] (I → W)) :
    LinearMap.trace K (I → W) L =
      ∑ i, LinearMap.trace K W
        ((LinearMap.proj i).comp (L.comp (LinearMap.single K (fun _ : I => W) i))) := by
  classical
  have hL : L = ∑ i, (LinearMap.single K (fun _ : I => W) i).comp
      ((LinearMap.proj i).comp L) := by
    ext f j
    simp
  conv_lhs => rw [hL, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearMap.trace_comp_comm']
  rfl

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ H V)

/-- The Reynolds average imposing f(xh)=h⁻¹f(x). -/
def average : (G → V) →ₗ[ℂ] (G → V) where
  toFun f x := (Nat.card H : ℂ)⁻¹ • ∑ h : H, ρ h (f (x * h))
  map_add' f f' := by
    ext x
    simp [map_add, Finset.sum_add_distrib, smul_add]
  map_smul' c f := by
    ext x
    simp [← Finset.smul_sum, smul_comm c]

theorem average_covariant (f : G → V) (x : G) (a : H) :
    average H ρ f (x * a) = ρ a⁻¹ (average H ρ f x) := by
  change (Nat.card H : ℂ)⁻¹ • (∑ h : H, ρ h (f (x * a * h))) = _
  simp only [average, LinearMap.coe_mk, AddHom.coe_mk, map_smul, map_sum]
  congr 1
  calc
    ∑ h : H, ρ h (f (x * a * h)) =
        ∑ h : H, ρ a⁻¹ (ρ (a * h) (f (x * (a * h)))) := by
      apply Finset.sum_congr rfl; intro h hh
      simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
    _ = ∑ h : H, ρ a⁻¹ (ρ h (f (x * h))) :=
      Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)

/-- The finite support condition is automatic because G is finite. -/
def projection : (G → V) →ₗ[ℂ] functions H ρ :=
  (average H ρ).codRestrict (functions H ρ) (by
    intro f
    exact ⟨average_covariant H ρ f, Set.toFinite _⟩)

theorem projection_inclusion (f : functions H ρ) :
    projection H ρ f.1 = f := by
  apply Subtype.ext
  funext x
  change (Nat.card H : ℂ)⁻¹ • (∑ h : H, ρ h (f.1 (x * h))) = f.1 x
  have hn : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  simp only [f.2.1, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, ← mul_smul, inv_mul_cancel₀ hn, one_smul]

variable [FiniteDimensional ℂ V]

/-- The trace of the induced function action can be computed in all functions,
using the split inclusion and the averaging projection. -/
theorem trace_functionAction (g : G) :
    Ch08.CharacterSpecs.characterValue (functionAction H ρ) g =
      InducedCharacterSpecs.inductionValue H (Ch08.CharacterSpecs.characterValue ρ) g := by
  let i := (functions H ρ).subtype
  let p := projection H ρ
  have hsplit : p.comp i = LinearMap.id := by
    apply LinearMap.ext; intro f; exact projection_inclusion H ρ f
  have ht : LinearMap.trace ℂ _ (functionAction H ρ g) =
      LinearMap.trace ℂ (G → V) (i.comp ((functionAction H ρ g).comp p)) := by
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, hsplit, LinearMap.comp_id]
  change LinearMap.trace ℂ _ _ = _
  rw [ht, trace_pi]
  change (∑ x : G, LinearMap.trace ℂ V
      ((LinearMap.proj x).comp ((i.comp ((functionAction H ρ g).comp p)).comp
        (LinearMap.single ℂ (fun _ : G => V) x)))) = _
  unfold InducedCharacterSpecs.inductionValue
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have heq (h : H) : g⁻¹ * x * (h : G) = x ↔ (h : G) = x⁻¹ * g * x := by
    constructor <;> intro he
    · calc
        (h : G) = (g⁻¹ * x)⁻¹ * x := (eq_inv_mul_iff_mul_eq).mpr he
        _ = x⁻¹ * g * x := by simp [mul_inv_rev]
    · rw [he]; group
  have hd : (LinearMap.proj x).comp
      ((i.comp ((functionAction H ρ g).comp p)).comp
        (LinearMap.single ℂ (fun _ : G => V) x)) =
      (Nat.card H : ℂ)⁻¹ • ∑ h : H, if (h : G) = x⁻¹ * g * x then ρ h else 0 := by
    ext z
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
      LinearMap.smul_apply, LinearMap.sum_apply]
    change (Nat.card H : ℂ)⁻¹ • (∑ h : H, ρ h ((Pi.single x z : G → V) (g⁻¹ * x * h))) = _
    congr 1
    apply Finset.sum_congr rfl
    intro h hh
    by_cases hhx : (h : G) = x⁻¹ * g * x
    · rw [ite_eq_left hhx, (heq h).mpr hhx]
      simp
    · have hhx' := mt (heq h).mp hhx
      simp [hhx, Pi.single_eq_of_ne hhx']
  rw [hd, map_smul, map_sum]
  simp only [smul_eq_mul]
  congr 1
  by_cases hm : x⁻¹ * g * x ∈ H
  · let h : H := ⟨x⁻¹ * g * x, hm⟩
    rw [dite_eq_left hm]
    have hs : (∑ h' : H, LinearMap.trace ℂ V
        (if (h' : G) = x⁻¹ * g * x then ρ h' else 0)) =
        LinearMap.trace ℂ V (ρ h) := by
      rw [Finset.sum_eq_single h]
      · simp [h]
      · intro b hb hbh
        have hb' : (b : G) ≠ x⁻¹ * g * x := by
          intro he; exact hbh (Subtype.ext he)
        simp [hb']
      · simp
    simpa [h, Ch08.CharacterSpecs.characterValue] using hs
  · rw [dite_eq_right hm]
    apply Finset.sum_eq_zero
    intro h hh
    have hh' : (h : G) ≠ x⁻¹ * g * x := by
      intro he; exact hm (he ▸ h.2)
    simp [hh']

end InducedCharacterProof

/-- Induction of functions by the finite conjugacy sum. -/
def induceClassFunction : InducedCharacterSpecs.inductionType :=
  @InducedCharacterSpecs.inductionValue

/-- Reindexing x by ax proves conjugacy invariance of the induced sum. -/
theorem induceFunction_conjugate {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (ψ : H → ℂ) (a g : G) :
    InducedCharacterSpecs.inductionValue H ψ (a * g * a⁻¹) =
      InducedCharacterSpecs.inductionValue H ψ g := by
  classical
  change (Nat.card H : ℂ)⁻¹ * _ = (Nat.card H : ℂ)⁻¹ * _
  congr 1
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft a) _ _
  intro x
  have he : (a * x)⁻¹ * (a * g * a⁻¹) * (a * x) = x⁻¹ * g * x := by group
  change (if h : x⁻¹ * g * x ∈ H then ψ ⟨x⁻¹ * g * x, h⟩ else 0) =
    (if h : (a * x)⁻¹ * (a * g * a⁻¹) * (a * x) ∈ H then
      ψ ⟨(a * x)⁻¹ * (a * g * a⁻¹) * (a * x), h⟩ else 0)
  rw [he]

theorem induced_class_function : InducedCharacterSpecs.classFunctionType := by
  intro G _ _ H ψ a g
  exact induceFunction_conjugate H ψ a g

/-- The full formula, dimension at one and vanishing, for every tensor action
with the prescribed function-model comparison. -/
theorem induced_character : InducedCharacterSpecs.characterFormulaType := by
  intro G _ _ H V _ _ _ ρ D E
  have hdimF : Module.finrank ℂ (functions H ρ) = H.index * Module.finrank ℂ V := by
    letI := inducedScalarModule H ρ
    rw [← (functionEquiv H ρ).finrank_eq]
    exact TensorCoordinates.induced_finrank H ρ
  letI := D.module
  letI : FiniteDimensional ℂ (Induced H ρ) :=
    FiniteDimensional.of_injective E.equivalence.toLinearMap E.equivalence.injective
  have hchar (g : G) : Ch08.CharacterSpecs.characterValue D.representation g =
      Ch08.CharacterSpecs.characterValue (functionAction H ρ) g := by
    have he : E.equivalence.conj (D.representation g) = functionAction H ρ g := by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext x
      change (E.equivalence (D.representation g (E.equivalence.symm f))).1 x = _
      rw [E.equivariant]
      simp [functionAction_apply]
    unfold Ch08.CharacterSpecs.characterValue
    rw [← he, LinearMap.trace_conj']
  have hformula (g : G) : Ch08.CharacterSpecs.characterValue D.representation g =
      InducedCharacterSpecs.inductionValue H (Ch08.CharacterSpecs.characterValue ρ) g := by
    rw [hchar]
    exact InducedCharacterProof.trace_functionAction H ρ g
  refine ⟨inferInstance, hformula, ?_, ?_⟩
  · unfold Ch08.CharacterSpecs.characterValue
    rw [map_one, LinearMap.trace_one, E.equivalence.finrank_eq, hdimF, Nat.cast_mul]
  · intro g hg
    rw [hformula]
    change (Nat.card H : ℂ)⁻¹ * _ = 0
    simp [hg]

/-- Upstream induction supplies the tensor action and its actual function
comparison, so the hypotheses of `induced_character` are inhabited. -/
theorem induced_character_realization : InducedCharacterSpecs.realizationType := by
  intro G _ _ H V _ _ _ ρ
  refine ⟨inductionData H ρ, functionModelData H ρ, ?_⟩
  exact TensorCoordinates.induced_finiteDimensional H ρ

/-- The same operator is the linear extension of representation induction. -/
theorem induced_character_linear_extension :
  ∀ {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    {ι : Type w} [Fintype ι] (V : ι → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ H (V i))
    (D : ∀ i, InductionData H (ρ i)) (E : ∀ i, FunctionModelData H (ρ i) (D i))
    (c : ι → ℂ),
    InducedCharacterSpecs.inductionValue H (∑ i, c i • Ch08.CharacterSpecs.characterValue (ρ i)) =
      ∑ i, c i • (letI := (D i).module; Ch08.CharacterSpecs.characterValue (D i).representation) := by
  intro G _ _ H ι _ V _ _ _ ρ D E c
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  congr 1
  funext g
  exact ((induced_character H (ρ i) (D i) (E i)).2.1 g).symm

end P103.Ch09
