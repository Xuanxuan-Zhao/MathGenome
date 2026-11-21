import MathGenome.Internal.Specs.D05.M11.SymplecticBlocks
import MathGenome.Internal.D05.M11.Radicals
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace D05.M11.SymplecticBlocks
open Module
open Specs.D05.M11.SymplecticBlocks
open scoped BigOperators

universe u v
variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- The simultaneous orthogonal complement of a normalized pair. -/
def pairComplement (B : LinearMap.BilinForm K V) (u v : V) : Submodule K V :=
  LinearMap.ker (B u) ⊓ LinearMap.ker (B v)

/-- Removing the two components of a vector leaves a vector in the complement. -/
lemma remainder_mem (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u v : V) (huv : B u v = 1) (x : V) :
    x - B x v • u + B x u • v ∈ pairComplement B u v := by
  have hvu : B v u = -1 := by rw [← hB.neg_eq, huv]
  constructor <;> change _ = 0
  · simp only [map_add, map_sub, map_smul, smul_eq_mul, hB.self_eq_zero,
      huv, mul_zero, mul_one, sub_zero]
    rw [← hB.neg_eq x u]
    ring
  · simp only [map_add, map_sub, map_smul, smul_eq_mul, hB.self_eq_zero,
      hvu, mul_zero, add_zero]
    rw [← hB.neg_eq x v]
    ring

/-- Addition is an isomorphism from the hyperbolic plane and its complement. -/
noncomputable def splitPair (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u v : V) (huv : B u v = 1) :
    ((K × K) × pairComplement B u v) ≃ₗ[K] V := by
  let f : (K × K) × pairComplement B u v →ₗ[K] V :=
    { toFun := fun p => p.1.1 • u + p.1.2 • v + p.2
      map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add,
        Submodule.coe_add, add_smul]; abel
      map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd,
        Submodule.coe_smul_of_tower, smul_add, smul_smul, smul_eq_mul, RingHom.id_apply] }
  have hvu : B v u = -1 := by rw [← hB.neg_eq, huv]
  apply LinearEquiv.ofBijective f
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    have hu := congrArg (fun x => B u x) hp
    have hv := congrArg (fun x => B v x) hp
    have hw₁ : B u (p.2 : V) = 0 := p.2.property.1
    have hw₂ : B v (p.2 : V) = 0 := p.2.property.2
    change B u (p.1.1 • u + p.1.2 • v + (p.2 : V)) = B u 0 at hu
    change B v (p.1.1 • u + p.1.2 • v + (p.2 : V)) = B v 0 at hv
    simp only [map_add, map_smul, smul_eq_mul, hB.self_eq_zero, huv,
      mul_zero, mul_one, zero_add, hw₁, add_zero, map_zero] at hu
    simp only [map_add, map_smul, smul_eq_mul, hB.self_eq_zero, hvu,
      mul_zero, hw₂, add_zero, map_zero, mul_neg, mul_one, neg_eq_zero] at hv
    have hw : (p.2 : V) = 0 := by simpa [f, hu, hv] using hp
    exact Prod.ext (Prod.ext hv hu) (Subtype.ext hw)
  · intro x
    refine ⟨((B x v, -B x u), ⟨_, remainder_mem B hB u v huv x⟩), ?_⟩
    change B x v • u + (-B x u) • v + (x - B x v • u + B x u • v) = x
    rw [neg_smul]
    abel

lemma splitPair_apply (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u v : V) (huv : B u v = 1) (p : (K × K) × pairComplement B u v) :
    splitPair B hB u v huv p = p.1.1 • u + p.1.2 • v + p.2 := rfl

lemma splitPair_value (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u v : V) (huv : B u v = 1) (p q : (K × K) × pairComplement B u v) :
    B (splitPair B hB u v huv p) (splitPair B hB u v huv q) =
      p.1.1 * q.1.2 - p.1.2 * q.1.1 + B p.2 q.2 := by
  have hvu : B v u = -1 := by rw [← hB.neg_eq, huv]
  have hp₁ : B u (p.2 : V) = 0 := p.2.property.1
  have hp₂ : B v (p.2 : V) = 0 := p.2.property.2
  have hq₁ : B u (q.2 : V) = 0 := q.2.property.1
  have hq₂ : B v (q.2 : V) = 0 := q.2.property.2
  have hp₃ : B (p.2 : V) u = 0 := (hB.eq_iff).mp hp₁
  have hp₄ : B (p.2 : V) v = 0 := (hB.eq_iff).mp hp₂
  simp only [splitPair_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hB.self_eq_zero, huv, hvu,
    hp₃, hp₄, hq₁, hq₂]
  ring

/-- Prepend one hyperbolic coordinate pair. -/
def prependPair (r s : ℕ) :
    ((K × K) × Coordinates K r s) ≃ₗ[K] Coordinates K (r + 1) s where
  toFun p := (Fin.cons p.1 p.2.1, p.2.2)
  invFun p := (p.1 0, (fun i => p.1 i.succ, p.2))
  left_inv p := by simp
  right_inv p := by
    apply Prod.ext
    · funext i; exact Fin.cases rfl (fun _ => rfl) i
    · rfl
  map_add' p q := by
    apply Prod.ext
    · funext i; exact Fin.cases rfl (fun _ => rfl) i
    · rfl
  map_smul' a p := by
    apply Prod.ext
    · funext i; exact Fin.cases rfl (fun _ => rfl) i
    · rfl

lemma prependPair_value {r s : ℕ} (p q : (K × K) × Coordinates K r s) :
    blockValue (prependPair r s p) (prependPair r s q) =
      p.1.1 * q.1.2 - p.1.2 * q.1.1 + blockValue p.2 q.2 := by
  simp [blockValue, prependPair, Fin.sum_univ_succ]
  ring

/-- Adding an empty list of planes changes no vector coordinates. -/
def emptyPairs (s : ℕ) : (Fin s → K) ≃ₗ[K] Coordinates K 0 s where
  toFun x := (fun i => Fin.elim0 i, x)
  invFun x := x.2
  left_inv _ := rfl
  right_inv _ := Prod.ext (funext (fun i => Fin.elim0 i)) rfl
  map_add' _ _ := Prod.ext (funext (fun i => Fin.elim0 i)) rfl
  map_smul' _ _ := Prod.ext (funext (fun i => Fin.elim0 i)) rfl

private theorem coordinates_induction (n : ℕ) :
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    Module.finrank K V ≤ n → ∀ B : LinearMap.BilinForm K V, B.IsAlt →
      ∃ r s : ℕ, ∃ e : V ≃ₗ[K] Coordinates K r s,
        ∀ x y, B x y = blockValue (e x) (e y) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ hn B hB
    by_cases hz : B = 0
    · refine ⟨0, Module.finrank K V,
        (Module.finBasis K V).equivFun.trans (emptyPairs _), ?_⟩
      intro x y
      simp [hz, blockValue]
    · have hp : ∃ u v : V, B u v ≠ 0 := by
        by_contra h
        push Not at h
        exact hz (by ext u v; exact h u v)
      obtain ⟨u, v₀, huv₀⟩ := hp
      let v := (B u v₀)⁻¹ • v₀
      have huv : B u v = 1 := by
        simp [v, huv₀]
      let W := pairComplement B u v
      let f := splitPair B hB u v huv
      have hdim : Module.finrank K V = 2 + Module.finrank K W := by
        rw [← f.finrank_eq, Module.finrank_prod, Module.finrank_prod]
        simp [W]
      have hlt : Module.finrank K W < n := by omega
      have hW : (B.restrict W).IsAlt := fun x => hB x
      obtain ⟨r, s, e, he⟩ := ih _ hlt W le_rfl (B.restrict W) hW
      let g := f.symm.trans ((LinearEquiv.refl K (K × K)).prodCongr e)
      refine ⟨r + 1, s, g.trans (prependPair r s), ?_⟩
      intro x y
      change B x y = blockValue (prependPair r s (g x)) (prependPair r s (g y))
      rw [prependPair_value]
      have h := splitPair_value B hB u v huv (f.symm x) (f.symm y)
      change B (f (f.symm x)) (f (f.symm y)) = _ at h
      simp only [LinearEquiv.apply_symm_apply] at h
      change B x y = (f.symm x).1.1 * (f.symm y).1.2 -
        (f.symm x).1.2 * (f.symm y).1.1 +
        blockValue (e (f.symm x).2) (e (f.symm y).2)
      rw [← he]
      exact h

theorem normal_coordinates : Specs.D05.M11.SymplecticBlocks.normal_coordinates := by
  intro K V _ _ _ _ B hB
  exact coordinates_induction (Module.finrank K V) V le_rfl B hB

theorem radical_coordinates : Specs.D05.M11.SymplecticBlocks.radical_coordinates := by
  intro K V _ _ _ r s B e he x
  rw [D05.M11.Radicals.mem_leftRadical]
  constructor
  · intro hx
    have ht (p : Coordinates K r s) : blockValue (e x) p = 0 := by
      rw [← e.apply_symm_apply p, ← he]
      exact hx _
    funext i
    apply Prod.ext
    · have h := ht (Pi.single i (0, 1), 0)
      simpa [blockValue, Pi.single_apply, apply_ite, mul_ite, ite_mul] using h
    · have h := ht (Pi.single i (1, 0), 0)
      simpa [blockValue, Pi.single_apply, apply_ite, mul_ite, ite_mul] using h
  · intro hx y
    rw [he]
    simp [blockValue, hx]

/-- Rank and dimension of any coordinates satisfying the evaluation identity. -/
lemma coordinate_dimensions [FiniteDimensional K V] {r s : ℕ}
    (B : LinearMap.BilinForm K V) (e : V ≃ₗ[K] Coordinates K r s)
    (he : ∀ x y, B x y = blockValue (e x) (e y)) :
    Module.finrank K V = 2 * r + s ∧ Module.finrank K (LinearMap.range B) = 2 * r := by
  have hd : Module.finrank K V = 2 * r + s := by
    rw [e.finrank_eq]
    simp [Coordinates, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]
  let p : V →ₗ[K] (Fin r → K × K) :=
    (LinearMap.fst K (Fin r → K × K) (Fin s → K)).comp e.toLinearMap
  have hp : Function.Surjective p := by
    intro z
    exact ⟨e.symm (z, 0), by simp [p]⟩
  have hk : LinearMap.ker B = LinearMap.ker p := by
    ext x
    exact radical_coordinates B e he x
  have hr : Module.finrank K (LinearMap.range p) = 2 * r := by
    rw [LinearMap.range_eq_top.mpr hp, finrank_top]
    simp [Module.finrank_pi_fintype, Module.finrank_prod, Nat.mul_comm]
  have h₁ := B.finrank_range_add_finrank_ker
  have h₂ := p.finrank_range_add_finrank_ker
  rw [← hk, hr] at h₂
  exact ⟨hd, by omega⟩

theorem even_rank : Specs.D05.M11.SymplecticBlocks.even_rank := by
  intro K V _ _ _ _ B hB
  obtain ⟨r, s, e, he⟩ := normal_coordinates B hB
  rw [(coordinate_dimensions B e he).2]
  exact ⟨r, by omega⟩

theorem even_dimension : Specs.D05.M11.SymplecticBlocks.even_dimension := by
  intro K V _ _ _ _ B hB hN
  have hk : LinearMap.ker B = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    exact hN.1 x (fun y => by simpa using congrArg (fun f : V →ₗ[K] K => f y) hx)
  have h := B.finrank_range_add_finrank_ker
  rw [hk, finrank_bot, add_zero] at h
  rw [← h]
  exact even_rank B hB

/-- Flatten paired coordinates, retaining the order within each plane. -/
def flattenCoordinates (r s : ℕ) : Coordinates K r s ≃ₗ[K] (BlockIndex r s → K) where
  toFun p := Sum.elim (fun ij => if ij.2 = 0 then (p.1 ij.1).1 else (p.1 ij.1).2) p.2
  invFun f := (fun i => (f (.inl (i, 0)), f (.inl (i, 1))), fun z => f (.inr z))
  left_inv p := by
    apply Prod.ext
    · funext i; apply Prod.ext <;> simp
    · rfl
  right_inv f := by
    funext z
    rcases z with ⟨i, j⟩ | z
    · fin_cases j <;> simp
    · rfl
  map_add' p q := by
    funext z
    rcases z with ⟨i, j⟩ | z
    · fin_cases j <;> simp
    · rfl
  map_smul' a p := by
    funext z
    rcases z with ⟨i, j⟩ | z
    · fin_cases j <;> simp
    · rfl

lemma flatten_single_plane {r s : ℕ} (i : Fin r) (j : Fin 2) :
    (flattenCoordinates r s (K := K)).symm (Pi.single (.inl (i, j)) 1) =
      (Pi.single i (Basis.finTwoProd K j), 0) := by
  apply Prod.ext
  · funext k
    apply Prod.ext <;> fin_cases j <;>
      simp [flattenCoordinates, Pi.single_apply, apply_ite, eq_comm]
  · funext k
    simp [flattenCoordinates, Pi.single_apply]

lemma flatten_single_radical {r s : ℕ} (z : Fin s) :
    (flattenCoordinates r s (K := K)).symm (Pi.single (.inr z) 1) =
      (0, Pi.single z 1) := by
  apply Prod.ext
  · funext k; apply Prod.ext <;> simp [flattenCoordinates, Pi.single_apply]
  · funext k; simp [flattenCoordinates, Pi.single_apply]

lemma blockValue_single_plane {r s : ℕ} (i k : Fin r) (j l : Fin 2) :
    blockValue (K := K) (s := s) (Pi.single i (Basis.finTwoProd K j), 0)
      (Pi.single k (Basis.finTwoProd K l), 0) =
      if i = k then J K j l else 0 := by
  fin_cases j <;> fin_cases l <;>
    simp [blockValue, Pi.single_apply, apply_ite, J, eq_comm]

/-- The zero block is the span of exactly its own basis vectors. -/
lemma radical_span_of_coordinates {r s : ℕ} (B : LinearMap.BilinForm K V)
    (e : V ≃ₗ[K] Coordinates K r s)
    (he : ∀ x y, B x y = blockValue (e x) (e y)) :
    let b := Basis.ofEquivFun (e.trans (flattenCoordinates r s))
    Specs.D05.M11.Radicals.leftRadical_value B =
      Submodule.span K (Set.range (fun z : Fin s => b (.inr z))) := by
  classical
  intro b
  let f := e.trans (flattenCoordinates r s)
  have hb (z : Fin s) : e (b (.inr z)) = (0, Pi.single z 1) := by
    change e (Basis.ofEquivFun f (.inr z)) = _
    rw [Basis.coe_ofEquivFun]
    change e (e.symm ((flattenCoordinates r s).symm _)) = _
    rw [e.apply_symm_apply, flatten_single_radical]
  apply le_antisymm
  · intro x hx
    have hx' := (radical_coordinates B e he x).mp hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨(e x).2, ?_⟩
    apply e.injective
    rw [map_sum]
    simp_rw [map_smul, hb, Prod.smul_mk, smul_zero]
    apply Prod.ext
    · simpa only [Prod.fst_sum, Finset.sum_const_zero] using hx'.symm
    · simp only [Prod.snd_sum]
      change (∑ i, (e x).2 i • Pi.single i 1) = (e x).2
      simpa using (Pi.basisFun K (Fin s)).sum_repr (e x).2
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    change b (.inr z) ∈ Specs.D05.M11.Radicals.leftRadical_value B
    exact (radical_coordinates B e he _).mpr (by rw [hb])

theorem normal_basis : Specs.D05.M11.SymplecticBlocks.normal_basis := by
  intro K V _ _ _ _ B hB
  classical
  obtain ⟨r, s, e, he⟩ := normal_coordinates B hB
  let f := e.trans (flattenCoordinates r s)
  let b := Basis.ofEquivFun f
  have hb (a : BlockIndex r s) : e (b a) =
      (flattenCoordinates r s).symm (Pi.single a 1) := by
    rw [Basis.coe_ofEquivFun]
    change e (e.symm _) = _
    exact e.apply_symm_apply _
  refine ⟨r, s, b, ?_, (coordinate_dimensions B e he).1,
    (coordinate_dimensions B e he).2, radical_span_of_coordinates B e he⟩
  intro a c
  rw [he, hb, hb]
  rcases a with ⟨i, j⟩ | z <;> rcases c with ⟨k, l⟩ | w
  · rw [flatten_single_plane, flatten_single_plane, blockValue_single_plane]
    rfl
  · rw [flatten_single_plane, flatten_single_radical]
    simp [blockValue, blockMatrix]
  · rw [flatten_single_radical, flatten_single_plane]
    simp [blockValue, blockMatrix]
  · rw [flatten_single_radical, flatten_single_radical]
    simp [blockValue, blockMatrix]

end D05.M11.SymplecticBlocks
