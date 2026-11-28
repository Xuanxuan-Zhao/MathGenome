import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.NormalizedObstruction
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.AdjointCohomology
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace LieNotes.Heisenberg.NormalizedObstruction

open Specs.LieNotes.Heisenberg (ModelValue xValue yValue zValue centerLineValue)
open Specs.LieNotes.Heisenberg.NormalizedObstruction
open Specs.LieNotes.Heisenberg.AdjointCohomology (HeisenbergBasis)
open AdvancedHomologicalAlgebra.CE
open LieAlgebrasAndRepresentations.AbelianExtensions
open LieAlgebrasAndRepresentations.DeformationObstructions
open LieModule.Cohomology
open scoped TensorProduct Polynomial PowerSeries

universe u v

variable {k : Type u} [Field k]

private theorem model_table : HeisenbergBasis (basis k) := by
  obtain ⟨hx, hy, hz⟩ := basis_vectors k
  unfold HeisenbergBasis
  rw [hx, hy, hz]
  exact ⟨lie_xy k, lie_z_right k _, lie_z_right k _⟩

@[simp]
private theorem normalized_apply (a b c d e : k) (p q : ModelValue k) :
    normalized a b c d e p q = phi k a b c d e ![p,q] :=
  phiExterior_apply k a b c d e p q

@[simp]
private theorem cochainExterior_normalized (a b c d e : k) :
    cochainExterior (normalized a b c d e) = phiExterior k a b c d e :=
  (twoCochainExteriorEquiv (k := k) (g := Model k) (M := Model k)).apply_symm_apply _

private theorem normalized_cocycle [CharZero k] (a b c d e : k) :
    d₂₃ k (Model k) (Model k) (normalized a b c d e) = 0 := by
  apply (exterior_cycle_iff _ AdjointCohomology.d_formula _).mp
  rw [cochainExterior_normalized]
  obtain ⟨_, h⟩ := AdjointCohomology.model_normal_form k
  obtain ⟨f, hf, _⟩ := h ![a,b,c,d,e]
  change f.val = phiExterior k a b c d e at hf
  rw [← hf]
  exact f.property

private theorem degree_zero (p q r : Model k) :
    insertion (originalBracket (k := k)) originalBracket p q r = 0 := by
  simp only [insertion, originalBracket_apply]
  rw [← lie_skew ⁅p,q⁆ r, ← lie_skew ⁅q,r⁆ p, ← lie_skew ⁅r,p⁆ q]
  have h : -(⁅p, ⁅q,r⁆⁆ + ⁅q, ⁅r,p⁆⁆ + ⁅r, ⁅p,q⁆⁆) = 0 := by
    rw [lie_jacobi, neg_zero]
  calc
    _ = -(⁅p, ⁅q,r⁆⁆ + ⁅q, ⁅r,p⁆⁆ + ⁅r, ⁅p,q⁆⁆) := by abel
    _ = 0 := h

private theorem degree_one [CharZero k] (a b c d e : k) (p q r : Model k) :
    insertion originalBracket (normalized a b c d e) p q r +
      insertion (normalized a b c d e) originalBracket p q r = 0 := by
  rw [linearJacobi, normalized_cocycle]
  simp

theorem first_order : FirstOrderType := by
  intro k _ _ a b c d e
  refine ⟨⟨coefficients a b c d e, rfl, ?_, ?_⟩, rfl⟩
  · intro n hn
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm]
    rfl
  · intro n hn p q r
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simpa [jacobiCoefficient, coefficients] using degree_zero p q r
    · have h : Finset.antidiagonal 1 = {(0,1), (1,0)} := by decide
      simpa [jacobiCoefficient, h, coefficients] using degree_one a b c d e p q r

private theorem obstruction_eq_insertion (a b c d e : k) (p q r : Model k) :
    obstruction (coefficients a b c d e) 2 p q r =
      insertion (normalized a b c d e) (normalized a b c d e) p q r := by
  have h : (Finset.antidiagonal 2).filter (fun p : ℕ × ℕ => 0 < p.1 ∧ 0 < p.2) =
      {(1,1)} := by decide
  simp [obstruction, h, coefficients]

theorem obstruction_xyz : ObstructionType := by
  intro k _ _ a b c d e
  rw [obstruction_eq_insertion]
  change insertion (normalized a b c d e) (normalized a b c d e) (x k) (y k) (z k) = _
  simp only [insertion]
  rw [← twoCochain_skew (normalized a b c d e) (x k) (z k)]
  simp only [normalized_apply, phi_xy, phi_xz, phi_yz]
  apply ModelValue.ext
  funext i
  fin_cases i <;>
    simp [phi_apply, x, y, z, xValue, yValue, zValue,
      show ∀ p q : Model k, (p - q).coords = p.coords - q.coords from fun _ _ => rfl,
      show ∀ p : Model k, (-p).coords = -p.coords from fun _ => rfl] <;> ring

private theorem differential_center [CharZero k] (ψ : Cochain k) :
    Specs.LieNotes.Heisenberg.AdjointCohomology.d k (Model k) 2 (cochainExterior ψ)
      (wedge k (Model k) 3 ![x k,y k,z k]) ∈ centerLineValue k := by
  obtain ⟨hx, hy, hz⟩ := basis_vectors k
  have h := AdjointCohomology.differential_two_image k (Model k) (basis k) model_table
  rw [hx, hy, hz] at h
  exact (h _).mp ⟨cochainExterior ψ, rfl⟩

theorem order_two : OrderTwoType := by
  intro k _ _ a b c d e ψ
  obtain ⟨D, hD⟩ := first_order k a b c d e
  refine ⟨?_, differential_center ψ⟩
  simp only [← hD, jacobiCoefficient_update_top (by decide : 0 < 2)]
  rw [ce_two_formula _ AdjointCohomology.d_formula]

open private three_ext from MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.AdjointCohomology in
private theorem insertion_zero_of_equations [CharZero k] (a b c d e : k)
    (he : Equations a b c d e) (p q r : Model k) :
    insertion (normalized a b c d e) (normalized a b c d e) p q r = 0 := by
  let f := obstructionExterior (coefficients a b c d e) 2
  have h : f = 0 := by
    apply three_ext (basis k)
    obtain ⟨hx, hy, hz⟩ := basis_vectors k
    change f (wedge k (Model k) 3 ![basis k 0, basis k 1, basis k 2]) = 0
    rw [hx, hy, hz, show f = _ from rfl, obstructionExterior_wedge]
    change obstruction (coefficients a b c d e) 2 (xValue k) (yValue k) (zValue k) = 0
    rw [obstruction_xyz k a b c d e, he.1, he.2, zero_smul, zero_smul, sub_zero]
  rw [← obstruction_eq_insertion]
  have hh := LinearMap.congr_fun h (wedge k (Model k) 3 ![p,q,r])
  simp only [f, obstructionExterior_wedge, LinearMap.zero_apply] at hh
  exact hh

section ScalarExtension

variable {A : Type v} [CommRing A] [Algebra k A]

private theorem extend_tmul (f : Cochain k) (s t : A) (p q : Model k) :
    extendCochain A f (s ⊗ₜ[k] p) (t ⊗ₜ[k] q) = (s * t) ⊗ₜ[k] f p q := by
  simp [extendCochain, LinearMap.smul_apply, Module.End.baseChangeHom,
    LinearMap.baseChangeHom, TensorProduct.smul_tmul']

theorem extend_cochain : ExtendCochainType := by
  intro k _ A _ _ f s t p q
  exact extend_tmul f s t p q

private theorem extend_skew (f : Cochain k) (p q : A ⊗[k] Model k) :
    extendCochain A f q p = -extendCochain A f p q := by
  have h : (extendCochain A f).flip + extendCochain A f = 0 := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s p
    apply TensorProduct.AlgebraTensorModule.ext
    intro t q
    simp only [LinearMap.add_apply, LinearMap.flip_apply, LinearMap.zero_apply, extend_tmul]
    rw [← twoCochain_skew f p q, mul_comm t s, TensorProduct.tmul_neg, neg_add_cancel]
  rw [eq_neg_iff_add_eq_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) q

private theorem extend_alt (f : Cochain k) (p : A ⊗[k] Model k) :
    extendCochain A f p p = 0 := by
  induction p using TensorProduct.inductionOn with
  | tmul s p => simp [extend_tmul]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq, extend_skew f p q]
    abel

private theorem bracket_alt (t : A) (a b c d e : k) (ψ : Cochain k) (p : A ⊗[k] Model k) :
    bracket t a b c d e ψ p p = 0 := by
  simp [bracket, extend_alt]

private def jacobiMultilinear {V : Type*} [AddCommGroup V] [Module A V]
    (B : V →ₗ[A] V →ₗ[A] V) : MultilinearMap A (fun _ : Fin 3 => V) V where
  toFun v := cyclicJacobiator B (v 0) (v 1) (v 2)
  map_update_add' := by
    intro hd
    have he : hd = instDecidableEqFin 3 := Subsingleton.elim _ _
    subst hd
    intro x i y z
    fin_cases i <;> simp [cyclicJacobiator, Function.update, map_add, LinearMap.add_apply] <;> abel
  map_update_smul' := by
    intro hd
    have he : hd = instDecidableEqFin 3 := Subsingleton.elim _ _
    subst hd
    intro x i r y
    fin_cases i <;> simp [cyclicJacobiator, Function.update, map_smul, smul_add]

private theorem jacobi_of_pure
    (B : (A ⊗[k] Model k) →ₗ[A] (A ⊗[k] Model k) →ₗ[A] (A ⊗[k] Model k))
    (h : ∀ p q r : Model k, cyclicJacobiator B (1 ⊗ₜ[k] p) (1 ⊗ₜ[k] q) (1 ⊗ₜ[k] r) = 0)
    (p q r : A ⊗[k] Model k) : cyclicJacobiator B p q r = 0 := by
  have he : jacobiMultilinear B = 0 := by
    apply Module.Basis.ext_multilinear (fun _ => (basis k).baseChange A)
    intro i
    simpa [jacobiMultilinear] using h (basis k (i 0)) (basis k (i 1)) (basis k (i 2))
  exact DFunLike.congr_fun he ![p,q,r]

private def mixedJacobi {V : Type*} [AddCommGroup V] [Module A V]
    (F G : V →ₗ[A] V →ₗ[A] V) (p q r : V) : V :=
  F (G p q) r + F (G q r) p + F (G r p) q

section MixedJacobi

variable {V : Type*} [AddCommGroup V] [Module A V]
variable (F G H : V →ₗ[A] V →ₗ[A] V) (p q r : V) (s : A)

private theorem mixed_add_left :
    mixedJacobi (F + G) H p q r = mixedJacobi F H p q r + mixedJacobi G H p q r := by
  simp only [mixedJacobi, LinearMap.add_apply]
  abel

private theorem mixed_add_right :
    mixedJacobi F (G + H) p q r = mixedJacobi F G p q r + mixedJacobi F H p q r := by
  simp only [mixedJacobi, LinearMap.add_apply, map_add]
  abel

private theorem mixed_smul_left :
    mixedJacobi (s • F) G p q r = s • mixedJacobi F G p q r := by
  simp only [mixedJacobi, LinearMap.smul_apply, smul_add]

private theorem mixed_smul_right :
    mixedJacobi F (s • G) p q r = s • mixedJacobi F G p q r := by
  simp only [mixedJacobi, LinearMap.smul_apply, map_smul, smul_add]

end MixedJacobi

private theorem mixed_pure (f g : Cochain k) (p q r : Model k) :
    mixedJacobi (extendCochain A f) (extendCochain A g)
      (1 ⊗ₜ[k] p) (1 ⊗ₜ[k] q) (1 ⊗ₜ[k] r) = 1 ⊗ₜ[k] insertion f g p q r := by
  simp only [mixedJacobi, extend_tmul, one_mul, insertion, TensorProduct.tmul_add]

/-- Expansion in the scalar parameter on generators of the tensor product. -/
private theorem jacobi_expansion (t : A) (a b c d e : k) (ψ : Cochain k) (p q r : Model k) :
    let μ : Cochain k := originalBracket
    let φ := normalized a b c d e
    cyclicJacobiator (bracket t a b c d e ψ)
        (1 ⊗ₜ[k] p) (1 ⊗ₜ[k] q) (1 ⊗ₜ[k] r) =
      (1 ⊗ₜ[k] insertion μ μ p q r) +
      t • (1 ⊗ₜ[k] (insertion μ φ p q r + insertion φ μ p q r)) +
      t ^ 2 • (1 ⊗ₜ[k] (insertion μ ψ p q r + insertion ψ μ p q r + insertion φ φ p q r)) +
      t ^ 3 • (1 ⊗ₜ[k] (insertion φ ψ p q r + insertion ψ φ p q r)) +
      t ^ 4 • (1 ⊗ₜ[k] insertion ψ ψ p q r) := by
  dsimp only
  change mixedJacobi (bracket t a b c d e ψ) (bracket t a b c d e ψ) _ _ _ = _
  simp only [bracket, mixed_add_left, mixed_add_right, mixed_smul_left, mixed_smul_right,
    mixed_pure, TensorProduct.tmul_add, smul_add, smul_smul,
    show t * t = t ^ 2 by ring,
    show t * t ^ 2 = t ^ 3 by ring,
    show t ^ 2 * t = t ^ 3 by ring,
    show t ^ 2 * t ^ 2 = t ^ 4 by ring]
  abel

theorem linear_bracket : LinearBracketType := by
  intro k _ _ A _ _ t a b c d e he
  refine ⟨bracket_alt t a b c d e 0, jacobi_of_pure _ ?_⟩
  intro p q r
  rw [jacobi_expansion]
  simp [degree_zero, degree_one, insertion_zero_of_equations a b c d e he]

end ScalarExtension

private theorem truncated_cube : (truncatedParameter k) ^ 3 = 0 := by
  unfold truncatedParameter
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

private theorem truncated_square_tmul {p : Model k}
    (h : ((truncatedParameter k) ^ 2) ⊗ₜ[k] p = 0) : p = 0 := by
  have hcoord (i : Fin 3) : (basis k).repr p i = 0 := by
    have hi := congrArg (fun v => ((basis k).baseChange (TruncatedBase k)).repr v i) h
    simp only [Module.Basis.baseChange_repr_tmul, map_zero, Finsupp.zero_apply] at hi
    let P : k[X] := Polynomial.C ((basis k).repr p i) * Polynomial.X ^ 2
    have hm : Ideal.Quotient.mk (truncationIdeal k) P = 0 := by
      rw [Algebra.smul_def, ← (Ideal.Quotient.mkₐ k (truncationIdeal k)).commutes] at hi
      simpa [P, Polynomial.algebraMap_eq, truncatedParameter] using hi
    have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hm)
    have h2 := Polynomial.X_pow_dvd_iff.mp hd 2 (by decide)
    simpa [P, Polynomial.coeff_C_mul_X_pow] using h2
  apply (basis k).repr.injective
  ext i
  simpa using hcoord i

theorem quotient_comparison : QuotientComparisonType := by
  intro k _ _ a b c d e D hD ψ
  rw [extensionEquation_spec 2 (by decide) D ψ]
  simp only [hD, obstruction_eq_insertion]
  let t := truncatedParameter k
  have h3 : t ^ 3 = 0 := truncated_cube
  have h4 : t ^ 4 = 0 := by rw [pow_succ, h3, zero_mul]
  have heval (p q r : Model k) :
      cyclicJacobiator (bracket t a b c d e ψ) (1 ⊗ₜ[k] p) (1 ⊗ₜ[k] q) (1 ⊗ₜ[k] r) =
        (t ^ 2) ⊗ₜ[k] (insertion (normalized a b c d e) (normalized a b c d e) p q r -
          d₂₃ k (Model k) (Model k) ψ p q r) := by
    rw [jacobi_expansion, degree_zero, degree_one, linearJacobi, h3, h4]
    simp only [TensorProduct.tmul_zero, TensorProduct.zero_tmul, smul_zero, add_zero, zero_add,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, sub_eq_add_neg]
    congr 1
    abel
  constructor
  · intro h p q r
    have hj := h.2 (1 ⊗ₜ[k] p) (1 ⊗ₜ[k] q) (1 ⊗ₜ[k] r)
    rw [heval] at hj
    exact (sub_eq_zero.mp (truncated_square_tmul hj)).symm
  · intro h
    refine ⟨bracket_alt t a b c d e ψ, jacobi_of_pure _ ?_⟩
    intro p q r
    rw [heval, h, sub_self, TensorProduct.tmul_zero]

theorem extension_iff : ExtensionType := by
  intro k _ _ a b c d e
  constructor
  · rintro ⟨ψ, hψ⟩
    obtain ⟨D, hD⟩ := first_order k a b c d e
    have h := (extensionEquation_spec 2 (by decide) D ψ).mp
      ((quotient_comparison k a b c d e D hD ψ).mp hψ) (x k) (y k) (z k)
    rw [← ce_two_formula _ AdjointCohomology.d_formula, hD] at h
    have hobs : obstruction (coefficients a b c d e) 2 (x k) (y k) (z k) =
        (c * d - e * a) • x k - (e * b + c * a) • y k := obstruction_xyz k a b c d e
    rw [hobs] at h
    have hm := differential_center ψ
    rw [h, centerLineValue, Submodule.mem_span_singleton] at hm
    obtain ⟨s, hs⟩ := hm
    have h0 := congrArg (fun v : Model k => v.coords 0) hs
    have h1 := congrArg (fun v : Model k => v.coords 1) hs
    constructor
    · simpa [x, y, z, xValue, yValue, zValue,
        show ∀ p q : Model k, (p - q).coords = p.coords - q.coords from fun _ _ => rfl]
        using h0.symm
    · have hx : -(c * a) + -(e * b) = 0 := by
        simpa [x, y, z, xValue, yValue, zValue,
          show ∀ p q : Model k, (p - q).coords = p.coords - q.coords from fun _ _ => rfl]
          using h1.symm
      linear_combination -hx
  · intro h
    exact ⟨0, linear_bracket k _ (truncatedParameter k) a b c d e h⟩

theorem polynomial_formal : PolynomialFormalType := by
  intro k _ _ a b c d e h
  exact ⟨linear_bracket k _ Polynomial.X a b c d e h,
    linear_bracket k _ PowerSeries.X a b c d e h⟩

section LieAlgebra

variable {A V : Type*} [CommRing A] [AddCommGroup V] [Module A V]
variable {B : V →ₗ[A] V →ₗ[A] V}

/-- Install an alternating bilinear operation satisfying cyclic Jacobi as a Lie ring. -/
@[instance_reducible]
def lieRingOfBracket (h : IsLieBracket B) : LieRing V where
  bracket p q := B p q
  add_lie p q r := LinearMap.congr_fun (map_add B p q) r
  lie_add p q r := map_add (B p) q r
  lie_self := h.1
  leibniz_lie p q r := by
    change B p (B q r) = B (B p q) r + B q (B p r)
    have skew (x y : V) : B x y = -B y x := by
      rw [eq_neg_iff_add_eq_zero]
      simpa only [map_add, LinearMap.add_apply, h.1, zero_add, add_zero] using h.1 (y + x)
    have hj := h.2 p q r
    unfold cyclicJacobiator at hj
    rw [skew (B q r) p, skew r p, map_neg, LinearMap.neg_apply, skew (B p r) q, neg_neg] at hj
    calc
      B p (B q r) = B (B p q) r + B q (B p r) -
          (B (B p q) r + -B p (B q r) + B q (B p r)) := by abel
      _ = _ := by rw [hj, sub_zero]

/-- The Lie algebra uses the given module action on the same carrier. -/
@[instance_reducible]
def lieAlgebraOfBracket (h : IsLieBracket B) : @LieAlgebra A V _ (lieRingOfBracket h) := by
  letI : LieRing V := lieRingOfBracket h
  exact { toModule := inferInstance, lie_smul := fun t p q => map_smul (B p) t q }

end LieAlgebra

end LieNotes.Heisenberg.NormalizedObstruction
