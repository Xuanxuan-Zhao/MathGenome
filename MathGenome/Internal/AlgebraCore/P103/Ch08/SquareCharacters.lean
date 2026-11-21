import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.SquareCharacters
import MathGenome.Internal.AlgebraCore.P103.Ch08.CharacterConstructions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel

noncomputable section
universe u v w
namespace P103.Ch08.SquareCharacters
open SquareSpecs
variable {k : Type u} {V : Type w} [Field k] [AddCommGroup V] [Module k V]

@[simp] theorem flip_tmul (v w : V) :
    flip k V (TensorProduct.tmul k v w) = TensorProduct.tmul k w v := rfl

@[simp] theorem flip_flip (z : TensorSquare k V) : flip k V (flip k V z) = z :=
  (TensorProduct.comm k V V).symm_apply_apply z

@[simp] theorem mem_plus (z : TensorSquare k V) :
    z ∈ plusSpace k V ↔ flip k V z = z := by
  simp [plusSpace, LinearMap.mem_ker, sub_eq_zero]

@[simp] theorem mem_minus (z : TensorSquare k V) :
    z ∈ minusSpace k V ↔ flip k V z = -z := by
  simp [minusSpace, LinearMap.mem_ker, eq_neg_iff_add_eq_zero]

@[simp] theorem plusProjection_apply (z : TensorSquare k V) :
    plusProjection k V z = (2 : k)⁻¹ • (z + flip k V z) := rfl

@[simp] theorem minusProjection_apply (z : TensorSquare k V) :
    minusProjection k V z = (2 : k)⁻¹ • (z - flip k V z) := rfl

lemma half_two (h2 : (2 : k) ≠ 0) (z : TensorSquare k V) :
    (2 : k)⁻¹ • (z + z) = z := by
  rw [← two_smul k z, smul_smul, inv_mul_cancel₀ h2, one_smul]

lemma plusProjection_mem (z : TensorSquare k V) :
    plusProjection k V z ∈ plusSpace k V := by
  simp only [mem_plus, plusProjection_apply, map_smul, map_add, flip_flip]
  congr 1
  exact add_comm _ _

lemma minusProjection_mem (z : TensorSquare k V) :
    minusProjection k V z ∈ minusSpace k V := by
  simp only [mem_minus, minusProjection_apply, map_smul, map_sub, flip_flip,
    ← smul_neg, neg_sub]

lemma plusProjection_fixed (h2 : (2 : k) ≠ 0) (z : plusSpace k V) :
    plusProjection k V z = (z : TensorSquare k V) := by
  rw [plusProjection_apply, (mem_plus _).mp z.property, half_two h2]

lemma minusProjection_fixed (h2 : (2 : k) ≠ 0) (z : minusSpace k V) :
    minusProjection k V z = (z : TensorSquare k V) := by
  rw [minusProjection_apply, (mem_minus _).mp z.property, sub_neg_eq_add, half_two h2]

lemma sub_flip_mem (z : TensorSquare k V) : z - flip k V z ∈ symmetricRelations k V := by
  induction z using TensorProduct.inductionOn with
  | tmul v w => exact Submodule.subset_span ⟨v, w, rfl⟩
  | add x y hx hy =>
    simpa only [map_add, add_sub_add_comm] using (symmetricRelations k V).add_mem hx hy

lemma cross_mem (v w : V) :
    TensorProduct.tmul k v w + TensorProduct.tmul k w v ∈ exteriorRelations k V := by
  have h (a : V) : TensorProduct.tmul k a a ∈ exteriorRelations k V :=
    Submodule.subset_span ⟨a, rfl⟩
  have := (exteriorRelations k V).sub_mem
    ((exteriorRelations k V).sub_mem (h (v + w)) (h v)) (h w)
  simpa only [TensorProduct.add_tmul, TensorProduct.tmul_add] using
    (show (TensorProduct.tmul k v w + TensorProduct.tmul k w v) =
      (TensorProduct.tmul k (v+w) (v+w) - TensorProduct.tmul k v v) -
        TensorProduct.tmul k w w by
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]; abel) ▸ this

lemma add_flip_mem (z : TensorSquare k V) : z + flip k V z ∈ exteriorRelations k V := by
  induction z using TensorProduct.inductionOn with
  | tmul v w => exact cross_mem v w
  | add x y hx hy =>
    simpa only [map_add, add_add_add_comm] using (exteriorRelations k V).add_mem hx hy

lemma symmetric_le_ker : symmetricRelations k V ≤ LinearMap.ker (plusProjection k V) := by
  apply Submodule.span_le.mpr
  rintro z ⟨v,w,rfl⟩
  change plusProjection k V (TensorProduct.tmul k v w - TensorProduct.tmul k w v) = 0
  simp only [plusProjection_apply, map_sub, flip_tmul]
  simp only [add_comm (TensorProduct.tmul k w v), sub_self]

lemma exterior_le_ker : exteriorRelations k V ≤ LinearMap.ker (minusProjection k V) := by
  apply Submodule.span_le.mpr
  rintro z ⟨v,rfl⟩
  simp [LinearMap.mem_ker]

lemma ker_plusProjection (h2 : (2 : k) ≠ 0) :
    LinearMap.ker (plusProjection k V) = symmetricRelations k V := by
  apply le_antisymm _ symmetric_le_ker
  intro z hz
  have hz' : z + flip k V z = 0 :=
    (smul_eq_zero.mp (show (2 : k)⁻¹ • (z + flip k V z) = 0 from hz)).resolve_left
      (inv_ne_zero h2)
  have hf : flip k V z = -z := (eq_neg_iff_add_eq_zero).mpr (by rw [add_comm]; exact hz')
  have := (symmetricRelations k V).smul_mem (2 : k)⁻¹ (sub_flip_mem z)
  rwa [hf, sub_neg_eq_add, half_two h2] at this

lemma ker_minusProjection (h2 : (2 : k) ≠ 0) :
    LinearMap.ker (minusProjection k V) = exteriorRelations k V := by
  apply le_antisymm _ exterior_le_ker
  intro z hz
  have hz' : z - flip k V z = 0 :=
    (smul_eq_zero.mp (show (2 : k)⁻¹ • (z - flip k V z) = 0 from hz)).resolve_left
      (inv_ne_zero h2)
  have hf : flip k V z = z := (sub_eq_zero.mp hz').symm
  have := (exteriorRelations k V).smul_mem (2 : k)⁻¹ (add_flip_mem z)
  rwa [hf, half_two h2] at this

/-- A projection with kernel `N` induces the quotient-to-image equivalence. -/
def projectionEquiv {M : Type*} [AddCommGroup M] [Module k M]
    (N E : Submodule k M) (p : Module.End k M)
    (hp : ∀ z, p z ∈ E) (hfix : ∀ z : E, p z = (z : M))
    (hker : LinearMap.ker p = N) : (M ⧸ N) ≃ₗ[k] E :=
  let f := p.codRestrict E hp
  (Submodule.quotEquivOfEq N (LinearMap.ker f) (by simpa [f] using hker.symm)).trans
    (f.quotKerEquivOfSurjective (fun z => ⟨z, Subtype.ext (hfix z)⟩))

@[simp] lemma projectionEquiv_mk {M : Type*} [AddCommGroup M] [Module k M]
    (N E : Submodule k M) (p : Module.End k M)
    (hp : ∀ z, p z ∈ E) (hfix : ∀ z : E, p z = (z : M))
    (hker : LinearMap.ker p = N) (z : M) :
    (projectionEquiv N E p hp hfix hker (N.mkQ z) : M) = p z := by
  rfl

def symmetricEquiv (h2 : (2 : k) ≠ 0) : SymmetricSquare k V ≃ₗ[k] plusSpace k V :=
  projectionEquiv _ _ _ plusProjection_mem (plusProjection_fixed h2) (ker_plusProjection h2)

def exteriorEquiv (h2 : (2 : k) ≠ 0) : ExteriorSquare k V ≃ₗ[k] minusSpace k V :=
  projectionEquiv _ _ _ minusProjection_mem (minusProjection_fixed h2) (ker_minusProjection h2)

variable {G : Type v} [Group G] (ρ : Representation k G V)

lemma flip_diagonal (g : G) (z : TensorSquare k V) :
    flip k V (CharacterSpecs.tensorValue ρ ρ g z) =
      CharacterSpecs.tensorValue ρ ρ g (flip k V z) :=
  (TensorProduct.map_comm (ρ g) (ρ g) z).symm

lemma plusProjection_diagonal (g : G) (z : TensorSquare k V) :
    plusProjection k V (CharacterSpecs.tensorValue ρ ρ g z) =
      CharacterSpecs.tensorValue ρ ρ g (plusProjection k V z) := by
  simp [flip_diagonal]

lemma minusProjection_diagonal (g : G) (z : TensorSquare k V) :
    minusProjection k V (CharacterSpecs.tensorValue ρ ρ g z) =
      CharacterSpecs.tensorValue ρ ρ g (minusProjection k V z) := by
  simp [flip_diagonal]

/-- The +1 eigenspace is stable under the diagonal action. -/
def plusSubrepresentation : Subrepresentation (CharacterSpecs.tensorValue ρ ρ) where
  toSubmodule := plusSpace k V
  apply_mem_toSubmodule g z hz := by
    rw [mem_plus] at hz ⊢
    rw [flip_diagonal, hz]

/-- The −1 eigenspace is stable under the diagonal action. -/
def minusSubrepresentation : Subrepresentation (CharacterSpecs.tensorValue ρ ρ) where
  toSubmodule := minusSpace k V
  apply_mem_toSubmodule g z hz := by
    rw [mem_minus] at hz ⊢
    rw [flip_diagonal, hz, map_neg]

/-- Stability of the actual symmetric quotient relations. -/
def symmetricSubrepresentation : Subrepresentation (CharacterSpecs.tensorValue ρ ρ) where
  toSubmodule := symmetricRelations k V
  apply_mem_toSubmodule g z hz := by
    have hle : symmetricRelations k V ≤
        (symmetricRelations k V).comap (CharacterSpecs.tensorValue ρ ρ g) := by
      apply Submodule.span_le.mpr
      rintro z ⟨v,w,rfl⟩
      change CharacterSpecs.tensorValue ρ ρ g
        (TensorProduct.tmul k v w - TensorProduct.tmul k w v) ∈ symmetricRelations k V
      change TensorProduct.map (ρ g) (ρ g)
        (TensorProduct.tmul k v w - TensorProduct.tmul k w v) ∈ symmetricRelations k V
      rw [map_sub, TensorProduct.map_tmul, TensorProduct.map_tmul]
      exact Submodule.subset_span ⟨ρ g v, ρ g w, rfl⟩
    exact hle hz

/-- Stability of the actual exterior quotient relations. -/
def exteriorSubrepresentation : Subrepresentation (CharacterSpecs.tensorValue ρ ρ) where
  toSubmodule := exteriorRelations k V
  apply_mem_toSubmodule g z hz := by
    have hle : exteriorRelations k V ≤
        (exteriorRelations k V).comap (CharacterSpecs.tensorValue ρ ρ g) := by
      apply Submodule.span_le.mpr
      rintro z ⟨v,rfl⟩
      change CharacterSpecs.tensorValue ρ ρ g (TensorProduct.tmul k v v) ∈ exteriorRelations k V
      exact Submodule.subset_span ⟨ρ g v, rfl⟩
    exact hle hz

def squareActions (h2 : (2 : k) ≠ 0) : SquareActions ρ where
  symmetric := (symmetricSubrepresentation ρ).quotient
  exterior := (exteriorSubrepresentation ρ).quotient
  plus := (plusSubrepresentation ρ).toRepresentation
  minus := (minusSubrepresentation ρ).toRepresentation
  symmetricEquiv := symmetricEquiv h2
  exteriorEquiv := exteriorEquiv h2
  symmetric_action _ _ := rfl
  exterior_action _ _ := rfl
  plus_action _ _ := rfl
  minus_action _ _ := rfl
  symmetric_projection _ := projectionEquiv_mk ..
  exterior_projection _ := projectionEquiv_mk ..
  symmetric_equivariant g z := by
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      apply Subtype.ext
      change (symmetricEquiv h2 ((symmetricRelations k V).mkQ
        (CharacterSpecs.tensorValue ρ ρ g z)) : TensorSquare k V) =
          CharacterSpecs.tensorValue ρ ρ g
            (symmetricEquiv h2 ((symmetricRelations k V).mkQ z))
      simp only [symmetricEquiv, projectionEquiv_mk, plusProjection_diagonal]
  exterior_equivariant g z := by
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      apply Subtype.ext
      change (exteriorEquiv h2 ((exteriorRelations k V).mkQ
        (CharacterSpecs.tensorValue ρ ρ g z)) : TensorSquare k V) =
          CharacterSpecs.tensorValue ρ ρ g
            (exteriorEquiv h2 ((exteriorRelations k V).mkQ z))
      simp only [exteriorEquiv, projectionEquiv_mk, minusProjection_diagonal]

theorem quotient_models : SquareSpecs.constructionType := by
  intro k G V _ _ _ _ _ h2 ρ
  exact ⟨squareActions ρ h2⟩

/-- The tensor-basis calculation, valid over any field without eigenvalues. -/
lemma trace_flip_map [FiniteDimensional k V] (A B : Module.End k V) :
    LinearMap.trace k (TensorSquare k V) ((flip k V).comp (TensorProduct.map A B)) =
      LinearMap.trace k V (B.comp A) := by
  classical
  let b := Module.finBasis k V
  rw [LinearMap.trace_eq_matrix_trace k (b.tensorProduct b),
    LinearMap.trace_eq_matrix_trace k b, LinearMap.toMatrix_comp b b b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, LinearMap.comp_apply,
    Module.Basis.tensorProduct_apply', TensorProduct.map_tmul, flip_tmul,
    Fintype.sum_prod_type, Module.Basis.tensorProduct_repr_tmul_apply,
    smul_eq_mul, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Trace on a projected subspace is the ambient trace after projection.
The proof uses cyclicity between the ambient space and the subspace. -/
lemma trace_restriction {M : Type*} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] (E : Submodule k M) (p A : Module.End k M)
    (r : Module.End k E) (hp : ∀ z, p z ∈ E)
    (hfix : ∀ z : E, p z = (z : M)) (hact : ∀ z : E, (r z : M) = A z) :
    LinearMap.trace k E r = LinearMap.trace k M (p.comp A) := by
  let f := p.codRestrict E hp
  have hr : (f.comp A).comp E.subtype = r := by
    ext z
    change p (A z) = (r z : M)
    rw [← hact, hfix]
  have h := LinearMap.trace_comp_comm' (f.comp A) E.subtype
  rw [hr] at h
  exact h.symm

lemma trace_intertwined {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (e : M ≃ₗ[k] N)
    (A : Module.End k M) (B : Module.End k N) (h : ∀ z, e (A z) = B (e z)) :
    LinearMap.trace k M A = LinearMap.trace k N B := by
  have heq : e.conj A = B := by
    ext z
    change e (A (e.symm z)) = B z
    rw [h, e.apply_symm_apply]
  rw [← heq, LinearMap.trace_conj']

lemma trace_diagonal [FiniteDimensional k V] (g : G) :
    LinearMap.trace k (TensorSquare k V) (CharacterSpecs.tensorValue ρ ρ g) =
      CharacterSpecs.characterValue ρ g ^ 2 := by
  change LinearMap.trace k _ (TensorProduct.map (ρ g) (ρ g)) = _
  rw [LinearMap.trace_tensorProduct', pow_two]
  rfl

lemma trace_flip_diagonal [FiniteDimensional k V] (g : G) :
    LinearMap.trace k (TensorSquare k V)
        ((flip k V).comp (CharacterSpecs.tensorValue ρ ρ g)) =
      CharacterSpecs.characterValue ρ (g ^ 2) := by
  change LinearMap.trace k _ ((flip k V).comp (TensorProduct.map (ρ g) (ρ g))) =
    LinearMap.trace k V (ρ (g ^ 2))
  rw [trace_flip_map, pow_two, map_mul]
  rfl

/-- Characters of the actual symmetric-square and exterior-square quotients. -/
theorem square_characters : SquareSpecs.charactersType := by
  intro k G V _ _ _ _ _ h2 ρ S g
  have hs : CharacterSpecs.characterValue S.symmetric g =
      LinearMap.trace k (TensorSquare k V)
        ((plusProjection k V).comp (CharacterSpecs.tensorValue ρ ρ g)) := by
    calc
      _ = LinearMap.trace k (plusSpace k V) (S.plus g) :=
        trace_intertwined S.symmetricEquiv (S.symmetric g) (S.plus g)
          (S.symmetric_equivariant g)
      _ = _ := trace_restriction _ _ _ _ plusProjection_mem
        (plusProjection_fixed h2) (S.plus_action g)
  have ha : CharacterSpecs.characterValue S.exterior g =
      LinearMap.trace k (TensorSquare k V)
        ((minusProjection k V).comp (CharacterSpecs.tensorValue ρ ρ g)) := by
    calc
      _ = LinearMap.trace k (minusSpace k V) (S.minus g) :=
        trace_intertwined S.exteriorEquiv (S.exterior g) (S.minus g)
          (S.exterior_equivariant g)
      _ = _ := trace_restriction _ _ _ _ minusProjection_mem
        (minusProjection_fixed h2) (S.minus_action g)
  constructor
  · rw [hs, plusProjection, LinearMap.smul_comp, LinearMap.add_comp, LinearMap.id_comp,
      map_smul, map_add, trace_diagonal, trace_flip_diagonal]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  · rw [ha, minusProjection, LinearMap.smul_comp, LinearMap.sub_comp, LinearMap.id_comp,
      map_smul, map_sub, trace_diagonal, trace_flip_diagonal]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

end P103.Ch08.SquareCharacters
