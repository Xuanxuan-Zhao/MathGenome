import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.DegreeDividesCenterIndex
import MathGenome.Internal.AlgebraCore.P103.Ch08.DegreeDividesOrder
import MathGenome.Internal.AlgebraCore.P103.Ch08.ProductIrreducibles
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith

/-! The central-index conclusion of paper.tex 1685–1689, 1729–1737.

We realize the source's tensor powers by repeated central products. For a
model carrying the original central scalars, the anti-diagonal copy of Z(G)
in G × H acts trivially on the external tensor product. Quotienting preserves
irreducibility, multiplies degree by d, and multiplies group order by the
index of Z(G). Order divisibility for these quotients, followed by the
prime-exponent argument, gives the conclusion. -/

noncomputable section
universe u v
namespace P103.Ch08
namespace DegreeDividesCenterIndex

/-- A fixed nonzero factor cannot compensate for a larger prime exponent in
all powers. -/
theorem dvd_of_powers_dvd (d q c : ℕ) (hd : d ≠ 0) (hq : q ≠ 0)
    (hc : c ≠ 0) (h : ∀ m : ℕ, 0 < m → d ^ m ∣ c * q ^ m) : d ∣ q := by
  apply (Nat.factorization_le_iff_dvd hd hq).mp
  intro p
  by_contra hh
  have hp : q.factorization p + 1 ≤ d.factorization p := by omega
  let m := c.factorization p + 1
  have hm : 0 < m := by omega
  have he := (Nat.factorization_le_iff_dvd (pow_ne_zero m hd)
    (mul_ne_zero hc (pow_ne_zero m hq))).mpr (h m hm) p
  simp only [Nat.factorization_mul hc (pow_ne_zero m hq),
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at he
  dsimp [m] at he
  nlinarith

variable {G : Type u} {V : Type v} [Group G]
  [AddCommGroup V] [Module ℂ V]

/-- Central elements are scalar, with no faithfulness assumption. -/
theorem center_scalars [Finite G] (ρ : Representation ℂ G V) (hρ : Irreducible ℂ G V ρ) :
    ∃ a : Subgroup.center G → ℂ,
      ∀ z : Subgroup.center G, ρ z = a z • LinearMap.id := by
  let := Fintype.ofFinite G
  have := ClassSumIntegrality.finiteDimensional_of_irreducible ρ hρ
  have hs (z : Subgroup.center G) : ∃ c : ℂ, ρ z = c • LinearMap.id := by
    let f : ρ.IntertwiningMap ρ :=
      { toLinearMap := ρ z
        isIntertwining' := fun g => by
          change ρ z * ρ g = ρ g * ρ z
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 g] }
    obtain ⟨c, hc, _⟩ := Schur.uniqueScalar ρ hρ f
    exact ⟨c, congrArg Representation.IntertwiningMap.toLinearMap hc⟩
  exact ⟨fun z => (hs z).choose, fun z => (hs z).choose_spec⟩

/-- A finite group representation carrying the original central scalars.
The central map need not be injective. -/
structure CentralModel (G : Type u) [Group G] (a : Subgroup.center G → ℂ) where
  H : Type u
  [groupH : Group H]
  [finiteH : Finite H]
  W : Type v
  [addW : AddCommGroup W]
  [moduleW : Module ℂ W]
  [finiteW : FiniteDimensional ℂ W]
  rep : Representation ℂ H W
  centralMap : Subgroup.center G →* H
  central : ∀ z, centralMap z ∈ Subgroup.center H
  scalar : ∀ z, rep (centralMap z) = a z • LinearMap.id
  irreducible : Irreducible ℂ H W rep

attribute [instance] CentralModel.groupH CentralModel.finiteH
  CentralModel.addW CentralModel.moduleW CentralModel.finiteW

namespace CentralModel
variable {a : Subgroup.center G → ℂ} (M : CentralModel.{u,v} G a)

/-- The subgroup identified when taking a central product. Its first
coordinate makes this map injective even if `centralMap` is not. -/
def antiDiagonal : Subgroup.center G →* G × M.H where
  toFun z := (z, M.centralMap z⁻¹)
  map_one' := by simp
  map_mul' z t := by
    apply Prod.ext
    · rfl
    · change M.centralMap ((z * t)⁻¹) = M.centralMap z⁻¹ * M.centralMap t⁻¹
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      exact mul_inv_rev (z : G) (t : G) |>.trans
        (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ z.2) (t : G)⁻¹)

theorem antiDiagonal_injective : Function.Injective M.antiDiagonal := by
  intro z t h
  exact Subtype.ext (congrArg Prod.fst h)

instance antiDiagonal_normal : M.antiDiagonal.range.Normal :=
  Subgroup.normal_of_le_center (by
    rintro _ ⟨z, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Prod.ext
    · exact Subgroup.mem_center_iff.mp z.2 x.1
    · exact Subgroup.mem_center_iff.mp (M.central z⁻¹) x.2)

theorem card_antiDiagonal : Nat.card M.antiDiagonal.range = Nat.card (Subgroup.center G) := by
  exact Nat.card_congr (Equiv.ofInjective M.antiDiagonal M.antiDiagonal_injective).symm

end CentralModel

/-- Irreducibility of a pullback implies irreducibility of the original
representation: every invariant subspace pulls back on the same space. -/
theorem irreducible_of_comp {K : Type*} {H : Type*} [Group K] [Group H]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ K W) (f : H →* K)
    (h : Irreducible ℂ H W (σ.comp f)) : Irreducible ℂ K W σ := by
  refine ⟨h.1, fun U => ?_⟩
  let U' : Subrepresentation (σ.comp f) :=
    ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
  rcases h.2 U' with he | he
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation (σ.comp f) => S.toSubmodule) he
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation (σ.comp f) => S.toSubmodule) he

theorem scalar_mul_inverse (ρ : Representation ℂ G V)
    (hρ : Irreducible ℂ G V ρ) (a : Subgroup.center G → ℂ)
    (ha : ∀ z : Subgroup.center G, ρ z = a z • LinearMap.id) (z : Subgroup.center G) :
    a z * a z⁻¹ = 1 := by
  have : Nontrivial V := hρ.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply smul_left_injective ℂ hv
  calc
    (a z * a z⁻¹) • v = ρ z (ρ (z⁻¹ : Subgroup.center G) v) := by
      rw [ha z, ha z⁻¹]
      simp [smul_smul, mul_comm]
    _ = (1 : ℂ) • v := by
      change (ρ (z : G) * ρ ((z : G)⁻¹)) v = _
      rw [← map_mul]
      simp

variable [Finite G]

/-- One tensor step, followed by quotienting by the central anti-diagonal. -/
def centralProduct (ρ : Representation ℂ G V) (hρ : Irreducible ℂ G V ρ)
    (a : Subgroup.center G → ℂ) (ha : ∀ z : Subgroup.center G, ρ z = a z • LinearMap.id)
    (M : CentralModel.{u,v} G a) : CentralModel.{u,v} G a := by
  let := Fintype.ofFinite G
  have := ClassSumIntegrality.finiteDimensional_of_irreducible ρ hρ
  let N := M.antiDiagonal.range
  let τ := ProductSpecs.externalValue ρ M.rep
  letI : Representation.IsTrivial (τ.comp N.subtype) := by
    constructor
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := hx
    ext v w
    change τ ((z : G), M.centralMap z⁻¹) (TensorProduct.tmul ℂ v w) =
      TensorProduct.tmul ℂ v w
    rw [ProductIrreducibles.external_apply, ha z, M.scalar z⁻¹]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
      mul_comm (a z⁻¹) (a z), scalar_mul_inverse ρ hρ a ha z]
  let j : Subgroup.center G →* (G × M.H) ⧸ N :=
    { toFun := fun z => QuotientGroup.mk' N (z, 1)
      map_one' := by
        change QuotientGroup.mk' N (1 : G × M.H) = 1
        exact map_one _
      map_mul' := by
        intro z t
        change QuotientGroup.mk' N ((z : G) * (t : G), 1) =
          QuotientGroup.mk' N (z, 1) * QuotientGroup.mk' N (t, 1)
        rw [← map_mul]
        congr 1
        simp }
  exact
    { H := (G × M.H) ⧸ N
      W := TensorProduct ℂ V M.W
      rep := τ.ofQuotient N
      centralMap := j
      central := fun z => by
        apply Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
        refine ⟨((z : G), 1), ?_, rfl⟩
        apply Subgroup.mem_center_iff.mpr
        intro x
        apply Prod.ext
        · exact Subgroup.mem_center_iff.mp z.2 x.1
        · simp
      scalar := fun z => by
        ext v w
        change τ ((z : G), 1) (TensorProduct.tmul ℂ v w) =
          a z • TensorProduct.tmul ℂ v w
        rw [ProductIrreducibles.external_apply, ha z, map_one]
        simp [TensorProduct.smul_tmul']
      irreducible := by
        apply irreducible_of_comp (τ.ofQuotient N) (QuotientGroup.mk' N)
        exact ProductIrreducibles.external_irreducible ρ M.rep hρ M.irreducible }

theorem centralProduct_degree (ρ : Representation ℂ G V) (hρ : Irreducible ℂ G V ρ)
    (a : Subgroup.center G → ℂ) (ha : ∀ z : Subgroup.center G, ρ z = a z • LinearMap.id)
    (M : CentralModel.{u,v} G a) :
    Module.finrank ℂ (centralProduct ρ hρ a ha M).W =
      Module.finrank ℂ V * Module.finrank ℂ M.W := by
  let := Fintype.ofFinite G
  have := ClassSumIntegrality.finiteDimensional_of_irreducible ρ hρ
  exact Module.finrank_tensorProduct

theorem centralProduct_order (ρ : Representation ℂ G V) (hρ : Irreducible ℂ G V ρ)
    (a : Subgroup.center G → ℂ) (ha : ∀ z : Subgroup.center G, ρ z = a z • LinearMap.id)
    (M : CentralModel.{u,v} G a) :
    Nat.card (centralProduct ρ hρ a ha M).H =
      (Subgroup.center G).index * Nat.card M.H := by
  change Nat.card ((G × M.H) ⧸ M.antiDiagonal.range) = _
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Subgroup.center G))
  calc
    Nat.card (Subgroup.center G) * Nat.card ((G × M.H) ⧸ M.antiDiagonal.range) =
        Nat.card (G × M.H) := by
      rw [← M.card_antiDiagonal]
      exact M.antiDiagonal.range.card_mul_index
    _ = Nat.card (Subgroup.center G) * ((Subgroup.center G).index * Nat.card M.H) := by
      rw [Nat.card_prod, ← (Subgroup.center G).card_mul_index]
      ac_rfl

/-- Iterated central products realize every positive tensor degree. -/
theorem central_models (ρ : Representation ℂ G V) (hρ : Irreducible ℂ G V ρ)
    (a : Subgroup.center G → ℂ)
    (ha : ∀ z : Subgroup.center G, ρ z = a z • LinearMap.id) (n : ℕ) :
    ∃ M : CentralModel.{u,v} G a,
      Module.finrank ℂ M.W = Module.finrank ℂ V ^ (n + 1) ∧
      Nat.card M.H = Nat.card (Subgroup.center G) * (Subgroup.center G).index ^ (n + 1) := by
  let := Fintype.ofFinite G
  have := ClassSumIntegrality.finiteDimensional_of_irreducible ρ hρ
  induction n with
  | zero =>
    let M : CentralModel.{u,v} G a :=
      { H := G
        W := V
        rep := ρ
        centralMap := (Subgroup.center G).subtype
        central := fun z => z.2
        scalar := ha
        irreducible := hρ }
    refine ⟨M, ?_, ?_⟩
    · simp [M]
    · simp [M]
  | succ n ih =>
    obtain ⟨M, hd, hc⟩ := ih
    refine ⟨centralProduct ρ hρ a ha M, ?_, ?_⟩
    · rw [centralProduct_degree, hd, pow_succ' _ (n + 1)]
    · rw [centralProduct_order, hc, pow_succ' _ (n + 1)]
      ac_rfl

end DegreeDividesCenterIndex

/-- The degree of any nonzero irreducible complex representation divides
the index of the full center. -/
theorem degree_divides_center_index :
    DegreeDividesCenterIndexSpecs.degree_divides_center_indexType := by
  intro G V _ _ _ _ ρ hρ
  let := Fintype.ofFinite G
  have := ClassSumIntegrality.finiteDimensional_of_irreducible ρ hρ
  have : Nontrivial V := hρ.1
  obtain ⟨a, ha⟩ := DegreeDividesCenterIndex.center_scalars ρ hρ
  apply DegreeDividesCenterIndex.dvd_of_powers_dvd (Module.finrank ℂ V)
    (Subgroup.center G).index (Nat.card (Subgroup.center G))
  · exact (Module.finrank_pos (R := ℂ) (M := V)).ne'
  · exact Subgroup.index_ne_zero_of_finite
  · exact Nat.card_pos.ne'
  · intro m hm
    cases m with
    | zero => omega
    | succ n =>
      obtain ⟨M, hd, hc⟩ := DegreeDividesCenterIndex.central_models ρ hρ a ha n
      rw [← hd, ← hc]
      exact degree_divides_order M.rep M.irreducible

/-- Both divisibility assertions in the source theorem. -/
theorem degree_divisibility : DegreeDividesCenterIndexSpecs.degree_divisibilityType := by
  intro G V _ _ _ _ ρ hρ
  exact ⟨degree_divides_order ρ hρ, degree_divides_center_index ρ hρ⟩

end P103.Ch08
