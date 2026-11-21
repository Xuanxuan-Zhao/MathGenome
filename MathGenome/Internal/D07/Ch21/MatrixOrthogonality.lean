import MathGenome.Internal.D07.Ch21.HomPairing
import MathGenome.Internal.D07.Ch17.SchurScalar
import MathGenome.Internal.D07.Appendix.AlgebraicFta
import MathGenome.Internal.Specs.D07.Ch21.MatrixOrthogonality

namespace D07.Ch21.MatrixOrthogonality

universe u v w t s r
noncomputable section
open Specs.D07.Ch21.MatrixOrthogonality
open Specs.D07.Ch21.HomPairing

variable {G : Type u} {V : Type v} {W : Type w}
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

lemma average_intertwines (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (T : V →ₗ[ℂ] W) : ρ.IsIntertwiningMap σ (homAverageValue G V W ρ σ T) :=
  (HomPairing.invariants_intertwiners G V W ρ σ _).mp
    ((HomPairing.average_projection G V W ρ σ).1 T)

theorem average_inequivalent : AverageInequivalent.{u,v,w} := by
  intro G V W _ _ _ _ _ _ ρ σ hρ hσ hne T
  by_contra h
  obtain ⟨e, _⟩ := D07.Ch17.SchurNonscalar.nonzero_intertwiner_equivalence ℂ G V W
    ρ σ _ hρ hσ (average_intertwines ρ σ T) h
  exact hne ⟨e⟩

lemma trace_average_self [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (T : Module.End ℂ V) :
    LinearMap.trace ℂ V (homAverageValue G V V ρ ρ T) = LinearMap.trace ℂ V T := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have ht (g : G) : LinearMap.trace ℂ V ((ρ g).comp (T.comp (ρ g⁻¹))) =
      LinearMap.trace ℂ V T := by
    have hi : (ρ g⁻¹).comp (ρ g) = 1 := by
      rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rw [LinearMap.trace_comp_cycle, hi]
    rfl
  simp only [homAverageValue, map_smul, map_sum, LinearMap.sum_apply,
    LinearMap.smul_apply, homActionValue, Representation.linHom_apply, ht, smul_eq_mul]
  simp [hc]

theorem average_self : AverageSelf.{u,v} := by
  intro G V _ _ _ _ _ ρ hρ
  have : Nontrivial V := D07.Ch17.IrreducibleDefinition.irreducible_nontrivial hρ
  have hd : 0 < Module.finrank ℂ V := Module.finrank_pos
  refine ⟨hd, fun T => ?_⟩
  let S : Specs.D07.Ch17.SchurNonscalar.endomorphismAlgebraValue ℂ G V ρ :=
    ⟨homAverageValue G V V ρ ρ T,
      (D07.Ch17.SchurNonscalar.endomorphism_algebra_characterization ℂ G V ρ _).mpr
        (average_intertwines ρ ρ T)⟩
  obtain ⟨z, hz, _⟩ := D07.Ch17.SchurScalar.unique_scalar ℂ G V ρ hρ S
  change homAverageValue G V V ρ ρ T = z • (1 : Module.End ℂ V) at hz
  have htrace := trace_average_self ρ T
  rw [hz, map_smul, smul_eq_mul, LinearMap.trace_one] at htrace
  have hdim : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  have hz' : z = LinearMap.trace ℂ V T / (Module.finrank ℂ V : ℂ) :=
    (eq_div_iff hdim).mpr htrace
  rw [hz, hz']


omit [Fintype G] in
/-- A unitary action matrix has the inverse prescribed by the representation. -/
lemma matrix_inverse {ι : Type t} [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V)
    (hu : ∀ g, LinearMap.toMatrix b b (ρ g) ∈ Matrix.unitaryGroup ι ℂ) (g : G) :
    LinearMap.toMatrix b b (ρ g⁻¹) = (LinearMap.toMatrix b b (ρ g)).conjTranspose := by
  have hNM : LinearMap.toMatrix b b (ρ g⁻¹) * LinearMap.toMatrix b b (ρ g) = 1 := by
    rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one,
      LinearMap.toMatrix_one]
  exact left_inv_eq_right_inv hNM (Matrix.mem_unitaryGroup_iff.mp (hu g))

/-- The (a,e) entry of the average of E_{d,f} is the coefficient pairing.
Only the source matrix's inverse is converted to a conjugate transpose. -/
lemma average_matrix_unit {ι : Type t} {κ : Type s}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℂ W)
    (hu : ∀ g, LinearMap.toMatrix c c (σ g) ∈ Matrix.unitaryGroup κ ℂ)
    (a d : ι) (e f : κ) :
    LinearMap.toMatrix c b
        (homAverageValue G W V σ ρ ((LinearMap.toMatrix c b).symm (Matrix.single d f 1)))
        a e = pairingValue G (coefficient ρ b a d) (coefficient σ c e f) := by
  simp only [homAverageValue, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
    map_sum, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, pairingValue, coefficient]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  change LinearMap.toMatrix c b
    ((ρ g).comp (((LinearMap.toMatrix c b).symm (Matrix.single d f 1)).comp (σ g⁻¹))) a e = _
  rw [LinearMap.toMatrix_comp c b b, LinearMap.toMatrix_comp c c b,
    LinearEquiv.apply_symm_apply, matrix_inverse σ c hu g]
  simp [Matrix.mul_apply, Matrix.single, ite_and, Matrix.conjTranspose_apply]

theorem coefficient_self : CoefficientSelf.{u,v,t} := by
  intro G V ι _ _ _ _ _ _ _ ρ b hρ hu a d c e
  let T : Module.End ℂ V := (LinearMap.toMatrix b b).symm (Matrix.single d e 1)
  have hT : LinearMap.trace ℂ V T = if d = e then 1 else 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
    change Matrix.trace ((LinearMap.toMatrix b b) ((LinearMap.toMatrix b b).symm _)) = _
    rw [LinearEquiv.apply_symm_apply]
    by_cases h : d = e
    · subst e; simp
    · simp [h]
  rw [← average_matrix_unit ρ ρ b b hu a d c e]
  change LinearMap.toMatrix b b (homAverageValue G V V ρ ρ T) a c = _
  rw [(average_self G V ρ hρ).2 T, hT, map_smul, LinearMap.toMatrix_one]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  ring

theorem coefficient_inequivalent : CoefficientInequivalent.{u,v,w,t,s} := by
  intro G V W ι κ _ _ _ _ _ _ _ _ _ _ _ _ ρ σ b c hρ hσ hne _hu hv a d e f
  rw [← average_matrix_unit ρ σ b c hv a d e f]
  have hne' : ¬ Nonempty (σ.Equiv ρ) := fun ⟨e⟩ => hne ⟨e.symm⟩
  rw [average_inequivalent G W V σ ρ hσ hρ hne']
  simp

theorem character_orthogonality : CharacterOrthogonality.{u,v,w} := by
  intro G V W _ _ _ _ _ _ _ _ ρ σ hρ hσ
  classical
  have : Representation.IsIrreducible ρ := hρ
  have : Representation.IsIrreducible σ := hσ
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero
    (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  have h := Representation.char_orthonormal ρ σ
  have he : Nonempty (σ.Equiv ρ) ↔ Nonempty (ρ.Equiv σ) :=
    ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩
  rw [he] at h
  change (Fintype.card G : ℂ)⁻¹ * ∑ g, _ = _
  simp_rw [← D07.Ch21.UnitaryAveraging.character_inverse G W σ]
  simpa only [Nat.card_eq_fintype_card, Representation.character,
    Specs.D07.Ch17.Characters.characterValue] using h

theorem coefficient_nonzero : CoefficientNonzero.{u,v,t} := by
  intro G V ι _ _ _ _ _ _ _ ρ b hρ hu a d hz
  have h := coefficient_self G V ι ρ b hρ hu a d a d
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (average_self G V ρ hρ).1)
  simp [hz, pairingValue] at h
  exact hd h.symm

open scoped Classical in
theorem family_orthogonality :
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) (V : I → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (n : I → ℕ)
    (ρ : ∀ i, Representation ℂ G (V i))
    (b : ∀ i, Module.Basis (Fin (n i)) ℂ (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) →
    (∀ i g, LinearMap.toMatrix (b i) (b i) (ρ i g) ∈
      Matrix.unitaryGroup (Fin (n i)) ℂ) →
    let f : (Σ i, Fin (n i) × Fin (n i)) → G → ℂ :=
      fun p => coefficient (ρ p.1) (b p.1) p.2.1 p.2.2
    (∀ p, f p ≠ 0) ∧
    ∀ p q, Specs.D07.Ch21.HomPairing.pairingValue G (f p) (f q) =
      if p = q then (Module.finrank ℂ (V p.1) : ℂ)⁻¹ else 0 := by
  intro G _ _ I V _ _ _ n ρ b hi hne hu
  classical
  dsimp only
  refine ⟨fun ⟨i, a, d⟩ => coefficient_nonzero G (V i) (Fin (n i))
    (ρ i) (b i) (hi i) (hu i) a d, ?_⟩
  rintro ⟨i, a, d⟩ ⟨j, c, e⟩
  by_cases hij : i = j
  · subst j
    rw [coefficient_self G (V i) (Fin (n i)) (ρ i) (b i) (hi i) (hu i)]
    by_cases hac : a = c <;> by_cases hde : d = e
    · subst c; subst e; simp
    · simp [hac, hde]
    · simp [hac, hde]
    · simp [hac, hde]
  · rw [coefficient_inequivalent G (V i) (V j) (Fin (n i)) (Fin (n j))
      (ρ i) (ρ j) (b i) (b j) (hi i) (hi j) (hne i j hij) (hu i) (hu j)]
    have hpq : (⟨i, (a, d)⟩ : Σ i, Fin (n i) × Fin (n i)) ≠ ⟨j, (c, e)⟩ :=
      fun h => hij (congrArg Sigma.fst h)
    simp [hpq]

end
end D07.Ch21.MatrixOrthogonality
