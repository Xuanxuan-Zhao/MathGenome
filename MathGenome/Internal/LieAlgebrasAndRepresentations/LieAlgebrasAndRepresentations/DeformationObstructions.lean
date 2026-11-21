import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DeformationObstructions
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InfinitesimalDeformations
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace LieAlgebrasAndRepresentations.DeformationObstructions
open LieModule.Cohomology AdvancedHomologicalAlgebra.CE
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]

/-- The binary/ternary NR commutator, evaluated on four arguments. -/
def insertionCommutator (a : twoCochain k g g) (T : g → g → g → g)
    (x y z w : g) : g :=
  a (T x y z) w - a (T x y w) z + a (T x z w) y - a (T y z w) x -
  T (a x y) z w + T (a x z) y w - T (a x w) y z -
  T (a y z) x w + T (a y w) x z - T (a z w) x y

/-- The binary case of graded Jacobi: the Bianchi identity for the Jacobiator.
This uses only alternation and bilinearity, not the Jacobi identity for `a`. -/
theorem bianchi (a : twoCochain k g g) (x y z w : g) :
    insertionCommutator a (insertion a a) x y z w = 0 := by
  simp only [insertionCommutator, insertion, map_add, LinearMap.add_apply]
  rw [← twoCochain_skew a (a x y) w, ← twoCochain_skew a (a x z) w,
    ← twoCochain_skew a (a x w) z, ← twoCochain_skew a (a y z) w,
    ← twoCochain_skew a (a y w) z, ← twoCochain_skew a (a z w) y,
    ← twoCochain_skew a x z, ← twoCochain_skew a x w,
    ← twoCochain_skew a y w]
  simp only [map_neg, LinearMap.neg_apply]
  rw [← twoCochain_skew a (a x y) (a z w),
    ← twoCochain_skew a (a x z) (a y w),
    ← twoCochain_skew a (a x w) (a y z)]
  abel


/-- A cubic expression used only to polarize the proved Bianchi identity. -/
def cubic (a b c : twoCochain k g g) (x y z w : g) : g :=
  insertionCommutator a (insertion b c) x y z w

private theorem cubic_add_left (a b c d : twoCochain k g g) (x y z w : g) :
    cubic (a+b) c d x y z w = cubic a c d x y z w + cubic b c d x y z w := by
  simp [cubic, insertionCommutator, insertion, add_apply_apply, map_add,
    LinearMap.add_apply]
  abel

private theorem cubic_add_middle (a b c d : twoCochain k g g) (x y z w : g) :
    cubic a (b+c) d x y z w = cubic a b d x y z w + cubic a c d x y z w := by
  simp [cubic, insertionCommutator, insertion, add_apply_apply, map_add,
    LinearMap.add_apply]
  abel

private theorem cubic_add_right (a b c d : twoCochain k g g) (x y z w : g) :
    cubic a b (c+d) x y z w = cubic a b c x y z w + cubic a b d x y z w := by
  simp [cubic, insertionCommutator, insertion, add_apply_apply, map_add,
    LinearMap.add_apply]
  abel

/-- Full polarization of the binary Bianchi identity. -/
theorem polarized_bianchi (a b c : twoCochain k g g) (x y z w : g) :
    cubic a b c x y z w + cubic a c b x y z w +
    cubic b a c x y z w + cubic b c a x y z w +
    cubic c a b x y z w + cubic c b a x y z w = 0 := by
  calc
    _ = cubic (a+b+c) (a+b+c) (a+b+c) x y z w -
        cubic (a+b) (a+b) (a+b) x y z w -
        cubic (a+c) (a+c) (a+c) x y z w -
        cubic (b+c) (b+c) (b+c) x y z w +
        cubic a a a x y z w + cubic b b b x y z w + cubic c c c x y z w := by
      simp only [cubic_add_left, cubic_add_middle, cubic_add_right]
      abel
    _ = 0 := by simp only [cubic, bianchi]; abel

/-- A symmetric finite sum over all ordered triples with total degree n. -/
def tripleSum (n : ℕ) (f : ℕ → ℕ → ℕ → g) : g :=
  ∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1),
    ∑ l ∈ Finset.range (n+1), if i+j+l=n then f i j l else 0

private theorem tripleSum_add (n : ℕ) (f h : ℕ → ℕ → ℕ → g) :
    tripleSum n (fun i j l => f i j l + h i j l) = tripleSum n f + tripleSum n h := by
  simp only [tripleSum, ite_add_zero, Finset.sum_add_distrib]

private theorem tripleSum_swap12 (n : ℕ) (f : ℕ → ℕ → ℕ → g) :
    tripleSum n (fun i j l => f j i l) = tripleSum n f := by
  unfold tripleSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.add_comm j i]

private theorem tripleSum_swap23 (n : ℕ) (f : ℕ → ℕ → ℕ → g) :
    tripleSum n (fun i j l => f i l j) = tripleSum n f := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp only [Nat.add_right_comm]

/-- Coefficient extraction in graded Jacobi, with no closure hypothesis. -/
theorem coefficient_bianchi [CharZero k] (c : ℕ → twoCochain k g g)
    (n : ℕ) (x y z w : g) :
    tripleSum n (fun i j l => cubic (c i) (c j) (c l) x y z w) = 0 := by
  let f := fun i j l => cubic (c i) (c j) (c l) x y z w
  have h₁ := tripleSum_swap12 n f
  have h₂ := tripleSum_swap23 n f
  have h₃ : tripleSum n (fun i j l => f j l i) = tripleSum n f := by
    rw [← h₂]
    exact tripleSum_swap12 n (fun i j l => f i l j)
  have h₄ : tripleSum n (fun i j l => f l i j) = tripleSum n f := by
    rw [← h₁]
    exact tripleSum_swap23 n (fun i j l => f j i l)
  have h₅ : tripleSum n (fun i j l => f l j i) = tripleSum n f := by
    rw [← h₃]
    exact tripleSum_swap23 n (fun i j l => f j l i)
  have h : tripleSum n (fun i j l => f i j l + f i l j + f j i l +
      f j l i + f l i j + f l j i) = 0 := by
    have hp : (fun i j l => f i j l + f i l j + f j i l +
        f j l i + f l i j + f l j i) = (fun _ _ _ => (0 : g)) := by
      funext i j l
      exact polarized_bianchi (c i) (c j) (c l) x y z w
    rw [hp]
    simp [tripleSum]
  simp only [tripleSum_add, h₁, h₂, h₃, h₄, h₅] at h
  have hh : (6 : k) • tripleSum n f = 0 := by
    simpa only [show (6 : k) = 1+1+1+1+1+1 by norm_num, add_smul, one_smul] using h
  exact (smul_eq_zero.mp hh).resolve_left (by norm_num)


private theorem tripleSum_group (n : ℕ) (f : ℕ → ℕ → ℕ → g) :
    tripleSum n f = ∑ i ∈ Finset.range (n+1),
      ∑ p ∈ Finset.antidiagonal (n-i), f i p.1 p.2 := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_product', ← Finset.sum_filter]
  have he : ((Finset.range (n+1) ×ˢ Finset.range (n+1)).filter
      (fun p : ℕ × ℕ => i+p.1+p.2=n)) = Finset.antidiagonal (n-i) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_antidiagonal] at *
    omega
  rw [he]

private theorem commutator_jacobi_sum (c : ℕ → twoCochain k g g)
    (a : twoCochain k g g) (n : ℕ) (x y z w : g) :
    (∑ p ∈ Finset.antidiagonal n, cubic a (c p.1) (c p.2) x y z w) =
      insertionCommutator a (jacobiCoefficient c n) x y z w := by
  simp only [cubic, insertionCommutator, jacobiCoefficient,
    map_sum, LinearMap.sum_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]

@[simp] theorem twoCochain_zero_apply (x y : g) :
    (0 : twoCochain k g g) x y = 0 := rfl

@[simp] theorem insertion_zero_left (b : twoCochain k g g) (x y z : g) :
    insertion 0 b x y z = 0 := by simp [insertion, twoCochain_zero_apply]
@[simp] theorem insertion_zero_right (b : twoCochain k g g) (x y z : g) :
    insertion b 0 x y z = 0 := by simp [insertion, twoCochain_zero_apply]

/-- Zero extension removes precisely the two endpoint terms. -/
theorem jacobiCoefficient_eq_obstruction {N : ℕ}
    (c : TruncatedDeformation (k := k) (g := g) N) (x y z : g) :
    jacobiCoefficient c.coeff N x y z = obstruction c.coeff N x y z := by
  classical
  unfold jacobiCoefficient obstruction
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : 0 < p.1 ∧ 0 < p.2
  · simp [h]
  · have hs := Finset.mem_antidiagonal.mp hp
    have hz : p.1 = 0 ∨ p.2 = 0 := by omega
    rcases hz with hz | hz
    · have he : p.2 = N := by omega
      simp [he, c.cutoff N le_rfl]
    · have he : p.1 = N := by omega
      simp [he, c.cutoff N le_rfl]

@[simp] theorem originalBracket_apply (x y : g) :
    originalBracket (k := k) x y = ⁅x,y⁆ := rfl

private theorem commutator_original (T : g → g → g → g) (x y z w : g) :
    insertionCommutator (originalBracket (k := k)) T x y z w = dThree T x y z w := by
  simp only [insertionCommutator, originalBracket_apply, dThree]
  rw [← lie_skew w (T x y z), ← lie_skew z (T x y w),
    ← lie_skew y (T x z w), ← lie_skew x (T y z w)]
  abel

/-- Closure of the obstruction follows from the actual degree-N Bianchi identity. -/
theorem closure_spec [CharZero k] :
    Specs.LieAlgebrasAndRepresentations.DeformationObstructions.closureStatement k g := by
  intro N hN c x y z w
  have h := coefficient_bianchi c.coeff N x y z w
  rw [tripleSum_group] at h
  simp_rw [commutator_jacobi_sum] at h
  have he : (∑ i ∈ Finset.range (N+1),
      insertionCommutator (c.coeff i) (jacobiCoefficient c.coeff (N-i)) x y z w) =
      insertionCommutator (c.coeff 0) (jacobiCoefficient c.coeff N) x y z w := by
    apply Finset.sum_eq_single 0
    · intro i hi hi0
      have hiN : N-i < N := by omega
      have hj : jacobiCoefficient c.coeff (N-i) = fun _ _ _ => 0 := by
        funext a b d
        exact c.jacobi _ hiN a b d
      simp [hj, insertionCommutator]
    · simp
  rw [he, c.base, commutator_original] at h
  have hj : jacobiCoefficient c.coeff N = obstruction c.coeff N := by
    funext a b d
    exact jacobiCoefficient_eq_obstruction c a b d
  rw [hj] at h
  exact h


/-- Updating degree N leaves all Jacobi coefficients below N unchanged. -/
theorem jacobiCoefficient_update_lt (c : ℕ → twoCochain k g g)
    (b : twoCochain k g g) {n N : ℕ} (hn : n < N) (x y z : g) :
    jacobiCoefficient (Function.update c N b) n x y z = jacobiCoefficient c n x y z := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  have hs := Finset.mem_antidiagonal.mp hp
  have h₁ : p.1 ≠ N := by omega
  have h₂ : p.2 ≠ N := by omega
  simp [Function.update_of_ne, h₁, h₂]

private theorem jacobiCoefficient_split (c : ℕ → twoCochain k g g)
    {N : ℕ} (hN : 0 < N) (x y z : g) :
    jacobiCoefficient c N x y z =
      insertion (c 0) (c N) x y z + insertion (c N) (c 0) x y z +
        obstruction c N x y z := by
  classical
  have he : ((Finset.antidiagonal N).filter
      (fun p : ℕ × ℕ => ¬ (0 < p.1 ∧ 0 < p.2))) = {(0,N),(N,0)} := by
    ext ⟨i,j⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    omega
  have hne : (0,N) ≠ (N,0) := by intro h; have := congrArg Prod.fst h; omega
  unfold jacobiCoefficient
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : ℕ × ℕ => 0 < p.1 ∧ 0 < p.2), he]
  simp only [Finset.sum_pair hne]
  change obstruction c N x y z + _ = _
  abel

private theorem obstruction_update (c : ℕ → twoCochain k g g)
    (b : twoCochain k g g) {N : ℕ} (x y z : g) :
    obstruction (Function.update c N b) N x y z = obstruction c N x y z := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp,hi,hj⟩ := Finset.mem_filter.mp hp
  have hs := Finset.mem_antidiagonal.mp hp
  have h₁ : p.1 ≠ N := by omega
  have h₂ : p.2 ≠ N := by omega
  simp [Function.update_of_ne, h₁, h₂]

/-- The linear part of the left-nested Jacobiator has the source sign −d. -/
theorem linearJacobi (b : twoCochain k g g) (x y z : g) :
    insertion originalBracket b x y z + insertion b originalBracket x y z =
      -(d₂₃ k g g b x y z) := by
  have h := LieAlgebrasAndRepresentations.InfinitesimalDeformations.linearJacobi_spec
    (k := k) (g := g) b x y z
  simp only [insertion, originalBracket_apply]
  rw [← h]
  abel

/-- The coefficient at the new order is exactly Oᴺ−dcᴺ. -/
theorem jacobiCoefficient_update_top {N : ℕ} (hN : 0 < N)
    (c : TruncatedDeformation (k := k) (g := g) N)
    (b : twoCochain k g g) (x y z : g) :
    jacobiCoefficient (Function.update c.coeff N b) N x y z =
      obstruction c.coeff N x y z - d₂₃ k g g b x y z := by
  classical
  rw [jacobiCoefficient_split _ hN, Function.update_self,
    Function.update_of_ne (by omega : 0 ≠ N), c.base,
    obstruction_update, linearJacobi]
  abel

/-- Extension is equivalent to the precise coboundary equation in the source. -/
theorem extensionEquation_spec [CharZero k] :
    Specs.LieAlgebrasAndRepresentations.DeformationObstructions.extensionEquationStatement k g := by
  intro N hN c b
  constructor
  · intro h x y z
    have hh := h N (by omega) x y z
    rw [jacobiCoefficient_update_top (by omega)] at hh
    exact (sub_eq_zero.mp hh).symm
  · intro h n hn x y z
    by_cases he : n = N
    · subst n
      rw [jacobiCoefficient_update_top (by omega), h, sub_self]
    · rw [jacobiCoefficient_update_lt _ _ (by omega)]
      exact c.jacobi n (by omega) x y z


private theorem insertion_repeat₁ (a b : twoCochain k g g) (x y : g) :
    insertion a b x x y = 0 := by
  simp only [insertion, twoCochain_alt, map_zero, LinearMap.zero_apply,
    ← twoCochain_skew b x y, map_neg, LinearMap.neg_apply]
  abel

private theorem insertion_repeat₂ (a b : twoCochain k g g) (x y : g) :
    insertion a b x y x = 0 := by
  simp only [insertion, twoCochain_alt, map_zero, LinearMap.zero_apply,
    ← twoCochain_skew b x y, map_neg, LinearMap.neg_apply]
  abel

private theorem insertion_repeat₃ (a b : twoCochain k g g) (x y : g) :
    insertion a b y x x = 0 := by
  simp only [insertion, twoCochain_alt, map_zero, LinearMap.zero_apply,
    ← twoCochain_skew b x y, map_neg, LinearMap.neg_apply]
  abel

/-- The insertion is genuinely alternating, not merely a function on triples. -/
def insertionAlternating (a b : twoCochain k g g) : g [⋀^Fin 3]→ₗ[k] g where
  toFun x := insertion a b (x 0) (x 1) (x 2)
  map_update_add' := by
    intro hd
    have he : hd = instDecidableEqFin 3 := Subsingleton.elim _ _
    subst hd
    intro x i y z
    fin_cases i <;> simp [insertion, Function.update, map_add, LinearMap.add_apply] <;> abel
  map_update_smul' := by
    intro hd
    have he : hd = instDecidableEqFin 3 := Subsingleton.elim _ _
    subst hd
    intro x i r y
    fin_cases i <;> simp [insertion, Function.update, map_smul, smul_add]
  map_eq_zero_of_eq' := by
    intro x i j h hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change insertion a b (x 0) (x 1) (x 2) = 0
      change x 0 = x 1 at h
      rw [h]
      exact insertion_repeat₁ _ _ _ _
    · change insertion a b (x 0) (x 1) (x 2) = 0
      change x 0 = x 2 at h
      rw [h]
      exact insertion_repeat₂ _ _ _ _
    · change insertion a b (x 0) (x 1) (x 2) = 0
      change x 1 = x 0 at h
      rw [h]
      exact insertion_repeat₁ _ _ _ _
    · exact (hne rfl).elim
    · change insertion a b (x 0) (x 1) (x 2) = 0
      change x 1 = x 2 at h
      rw [h]
      exact insertion_repeat₃ _ _ _ _
    · change insertion a b (x 0) (x 1) (x 2) = 0
      change x 2 = x 0 at h
      rw [h]
      exact insertion_repeat₂ _ _ _ _
    · change insertion a b (x 0) (x 1) (x 2) = 0
      change x 2 = x 1 at h
      rw [h]
      exact insertion_repeat₃ _ _ _ _
    · exact (hne rfl).elim

def obstructionAlternating (c : ℕ → twoCochain k g g) (N : ℕ) : g [⋀^Fin 3]→ₗ[k] g :=
  ∑ p ∈ (Finset.antidiagonal N).filter (fun p => 0 < p.1 ∧ 0 < p.2),
    insertionAlternating (c p.1) (c p.2)

@[simp] theorem obstructionAlternating_apply (c : ℕ → twoCochain k g g)
    (N : ℕ) (x : Fin 3 → g) :
    obstructionAlternating c N x = obstruction c N (x 0) (x 1) (x 2) := by
  simp [obstructionAlternating, obstruction, insertionAlternating]

def obstructionExterior (c : ℕ → twoCochain k g g) (N : ℕ) : W k g 3 →ₗ[k] g :=
  exteriorPower.alternatingMapLinearEquiv (obstructionAlternating c N)

@[simp] theorem obstructionExterior_wedge (c : ℕ → twoCochain k g g)
    (N : ℕ) (x : Fin 3 → g) :
    obstructionExterior c N (wedge k g 3 x) = obstruction c N (x 0) (x 1) (x 2) := by
  rw [obstructionExterior, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    obstructionAlternating_apply]

open LieAlgebrasAndRepresentations.AbelianExtensions

omit [LieRing g] in
@[simp] private theorem remove_vec3_1 (x y z : g) :
    (1 : Fin 3).removeNth ![x,y,z] = ![x,z] := by
  ext i
  fin_cases i <;> rfl

omit [LieRing g] in
@[simp] private theorem remove_vec3_2 (x y z : g) :
    (2 : Fin 3).removeNth ![x,y,z] = ![x,y] := by
  ext i
  fin_cases i <;> rfl

omit [LieRing g] in
@[simp] private theorem remove_vec4_1 (x y z w : g) :
    (1 : Fin 4).removeNth ![x,y,z,w] = ![x,z,w] := by
  ext i
  fin_cases i <;> rfl

omit [LieRing g] in
@[simp] private theorem remove_vec4_2 (x y z w : g) :
    (2 : Fin 4).removeNth ![x,y,z,w] = ![x,y,w] := by
  ext i
  fin_cases i <;> rfl

omit [LieRing g] in
@[simp] private theorem remove_vec4_3 (x y z w : g) :
    (3 : Fin 4).removeNth ![x,y,z,w] = ![x,y,z] := by
  ext i
  fin_cases i <;> rfl

/-- Degree-three differential with precisely the accepted exterior CE convention. -/
theorem ce_three_formula
    (δ : ∀ n, (W k g n →ₗ[k] g) →ₗ[k] (W k g (n+1) →ₗ[k] g))
    (hδ : HasLieCEFormula δ) (f : W k g 3 →ₗ[k] g) (x y z w : g) :
    δ 3 f (wedge k g 4 ![x,y,z,w]) =
      dThree (fun a b c => f (wedge k g 3 ![a,b,c])) x y z w := by
  rw [hδ]
  have hi₁ : Finset.Ici (1 : Fin 3) = {1,2} := by decide
  have hi₂ : Finset.Ici (2 : Fin 3) = {2} := by decide
  simp [cochainBracketSum, Fin.sum_univ_succ, hi₁, hi₂,
    remove_vec3_1, remove_vec3_2, remove_vec4_1, remove_vec4_2, remove_vec4_3, dThree]
  rw [← lie_skew y (f (wedge k g 3 ![x,z,w])),
    ← lie_skew w (f (wedge k g 3 ![x,y,z]))]
  abel

/-- The displayed obstruction gives a cycle in the ordinary exterior complex. -/
theorem obstructionExterior_cycle [CharZero k]
    (δ : ∀ n, (W k g n →ₗ[k] g) →ₗ[k] (W k g (n+1) →ₗ[k] g))
    (hδ : HasLieCEFormula δ) {N : ℕ} (hN : 1 ≤ N)
    (c : TruncatedDeformation (k := k) (g := g) N) :
    δ 3 (obstructionExterior c.coeff N) = 0 := by
  apply wedge_ext
  intro x
  have hx : x = ![x 0,x 1,x 2,x 3] := by ext i; fin_cases i <;> rfl
  rw [hx, ce_three_formula δ hδ]
  have he : (fun a b d => obstructionExterior c.coeff N (wedge k g 3 ![a,b,d])) =
      obstruction c.coeff N := by
    funext a b d
    simp
  rw [he]
  exact closure_spec N hN c _ _ _ _


/-- The obstruction class in ordinary H³ vanishes exactly when the truncation extends. -/
theorem cohomology_spec [CharZero k] :
    Specs.LieAlgebrasAndRepresentations.DeformationObstructions.cohomologyStatement k g := by
  intro δ hs hδ N hN c
  let O : LinearMap.ker (δ 3) :=
    ⟨obstructionExterior c.coeff N, obstructionExterior_cycle δ hδ hN c⟩
  refine ⟨O, ?_, ?_⟩
  · intro x y z
    exact obstructionExterior_wedge c.coeff N ![x,y,z]
  · rw [Submodule.Quotient.mk_eq_zero]
    change O.1 ∈ LinearMap.range (δ 2) ↔ _
    constructor
    · rintro ⟨f,hf⟩
      let b : twoCochain k g g := exteriorCochain f
      have hb : cochainExterior b = f :=
        (twoCochainExteriorEquiv (k := k) (g := g) (M := g)).apply_symm_apply f
      refine ⟨b, (extensionEquation_spec N hN c b).mpr ?_⟩
      intro x y z
      rw [← ce_two_formula δ hδ, hb, hf]
      exact obstructionExterior_wedge c.coeff N ![x,y,z]
    · rintro ⟨b,hb⟩
      refine ⟨cochainExterior b, ?_⟩
      apply wedge_ext
      intro x
      have hx : x = ![x 0,x 1,x 2] := by ext i; fin_cases i <;> rfl
      change δ 2 (cochainExterior b) (wedge k g 3 x) =
        obstructionExterior c.coeff N (wedge k g 3 x)
      rw [hx, ce_two_formula δ hδ, (extensionEquation_spec N hN c b).mp hb]
      symm
      exact obstructionExterior_wedge c.coeff N ![x 0,x 1,x 2]

end LieAlgebrasAndRepresentations.DeformationObstructions
