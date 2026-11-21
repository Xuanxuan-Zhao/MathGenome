import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Module.ULift

open CategoryTheory Finsupp

universe u v

namespace ALG02GroupTheory.IntegralBar

noncomputable section

variable (G : Type u) [Group G]

/-- A copy of the integers in the universe of the group. -/
abbrev Integers := ULift.{u} ℤ

/-- The discrete group acts trivially on the integral coefficient module. -/
abbrev coefficients : Rep Integers.{u} G := Rep.trivial Integers.{u} G Integers.{u}

/-- The standard (unnormalized) integral bar chains. -/
abbrev chains : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ :=
  groupHomology.inhomogeneousChains (coefficients G)

/-- Integral homology of a discrete group. -/
abbrev homology (n : ℕ) : ModuleCat.{u} Integers.{u} :=
  groupHomology (coefficients G) n

variable {G} {H : Type u} [Group H]

/-- The identity on integral coefficients viewed as an intertwining map. -/
abbrev coefficientMap (f : G →* H) :
    coefficients G ⟶ Rep.res f (coefficients H) :=
  𝟙 (coefficients G)

/-- The integral bar chain map induced by the given group homomorphism. -/
abbrev chainsMap (f : G →* H) : chains G ⟶ chains H :=
  groupHomology.chainsMap f (coefficientMap f)

/-- The map on integral homology induced by the given group homomorphism. -/
abbrev homologyMap (f : G →* H) (n : ℕ) : homology G n ⟶ homology H n :=
  groupHomology.map f (coefficientMap f) n

/-- The restriction of the ambient relative commutator subgroup to the kernel. -/
abbrev relativeCommutator (N : Subgroup G) : Subgroup N :=
  (⁅(⊤ : Subgroup G), N⁆ : Subgroup G).subgroupOf N

/-- The relative commutator subgroup pulled back via the given kernel inclusion. -/
abbrev pulledBackCommutator {K : Type v} [Group K] (i : K →* G) : Subgroup K :=
  (⁅(⊤ : Subgroup G), i.range⁆ : Subgroup G).comap i

instance (N : Subgroup G) [N.Normal] : (relativeCommutator N).Normal :=
  (Subgroup.commutator_normal ⊤ N).comap N.subtype

instance {K : Type v} [Group K] (i : K →* G) [i.range.Normal] :
    (pulledBackCommutator i).Normal :=
  (Subgroup.commutator_normal ⊤ i.range).comap i

/-- The homology class represented by the degree-one generator with coefficient one. -/
abbrev generatorClass (g : G) : homology G 1 :=
  groupHomology.H1π (coefficients G)
    ((groupHomology.cycles₁IsoOfIsTrivial (coefficients G)).inv (single g 1))

/-- The basis element of the standard bar complex with coefficient one. -/
abbrev bar (n : ℕ) (g : Fin n → G) : (chains G).X n :=
  single g 1

/-- The submodule spanned by the tuples with at least one identity entry. -/
def degenerate (G : Type u) [Group G] (n : ℕ) :
    Submodule Integers.{u} ((chains G).X n) :=
  Submodule.span _ {z | ∃ g : Fin n → G, (∃ j, g j = 1) ∧ z = bar n g}

abbrev NormalizedModule (G : Type u) [Group G] (n : ℕ) :=
  (chains G).X n ⧸ degenerate G n

/-- The quotient class of a bar tuple. -/
abbrev normalizedBar (n : ℕ) (g : Fin n → G) : NormalizedModule G n :=
  (degenerate G n).mkQ (bar n g)

theorem bar_mem_degenerate {n : ℕ} {g : Fin n → G} (h : ∃ j, g j = 1) :
    bar n g ∈ degenerate G n :=
  Submodule.subset_span ⟨g, h, rfl⟩

private theorem normalizedBar_of_identity {n : ℕ} {g : Fin n → G} (h : ∃ j, g j = 1) :
    normalizedBar n g = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (bar_mem_degenerate h)

private theorem contract_first {n : ℕ} (g : Fin (n + 1) → G) (h : g 0 = 1) :
    Fin.contractNth 0 (· * ·) g = fun k => g k.succ := by
  funext k
  by_cases hk : k.val = 0
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ hk]
    have he : k.castSucc = 0 := Fin.ext hk
    simp [he, h]
  · exact Fin.contractNth_apply_of_gt _ _ _ _ (show 0 < k.val by omega)

private theorem contract_adjacent {n : ℕ} (g : Fin (n + 1) → G) (i : Fin n)
    (h : g i.succ = 1) :
    Fin.contractNth i.castSucc (· * ·) g = Fin.contractNth i.succ (· * ·) g := by
  funext k
  rcases lt_trichotomy k.val i.val with hlt | heq | hgt
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hlt,
      Fin.contractNth_apply_of_lt _ _ _ _ (show k.val < i.succ.val by simpa using Nat.lt_succ_of_lt hlt)]
  · have he : k = i := Fin.ext heq
    subst k
    rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl,
      Fin.contractNth_apply_of_lt _ _ _ _ (Nat.lt_succ_self _), h, mul_one]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ hgt]
    by_cases he : k.val = i.succ.val
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ he]
      have hk : k.castSucc = i.succ := Fin.ext he
      rw [hk, h, one_mul]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp at he ⊢; omega)]

private theorem normalization_annihilates_d {n : ℕ} (g : Fin (n + 1) → G)
    (h : ∃ j, g j = 1) :
    (degenerate G n).mkQ ((chains G).d (n + 1) n (bar (n + 1) g)) = 0 := by
  classical
  rw [groupHomology.inhomogeneousChains.d_def]
  unfold bar
  rw [groupHomology.inhomogeneousChains.d_single (A := coefficients G)]
  change (degenerate G n).mkQ (single (fun k => g k.succ) 1 + _) = 0
  simp only [map_add, map_sum, map_smul]
  change normalizedBar n (fun k => g k.succ) +
    ∑ j : Fin (n + 1), (-1 : Integers.{u}) ^ (j.val + 1) •
      normalizedBar n (Fin.contractNth j (· * ·) g) = 0
  obtain ⟨i, hi⟩ := h
  induction i using Fin.cases with
  | zero =>
    rw [Finset.sum_eq_single 0]
    · rw [contract_first g hi]
      simp
    · intro j _ hj
      let k : Fin n := ⟨0, by
        have := j.isLt
        have hpos : 0 < j.val := Nat.pos_of_ne_zero (fun hz => hj (Fin.ext hz))
        omega⟩
      have hlt : k.val < j.val := Nat.pos_of_ne_zero (fun hz => hj (Fin.ext hz))
      rw [normalizedBar_of_identity ⟨k, by
        rw [Fin.contractNth_apply_of_lt _ _ _ _ hlt]
        exact hi⟩, smul_zero]
    · simp
  | succ i =>
    rw [normalizedBar_of_identity ⟨i, hi⟩, zero_add]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i.succ)]
    rw [Finset.sum_eq_single i.castSucc]
    · rw [contract_adjacent g i hi]
      simp [pow_succ, mul_neg, neg_smul]
    · intro j hj hcast
      have hsucc : j ≠ i.succ := (Finset.mem_erase.mp hj).1
      have hdeg : ∃ k, Fin.contractNth j (· * ·) g k = 1 := by
        by_cases hlt : j.val < i.val
        · exact ⟨i, (Fin.contractNth_apply_of_gt _ _ _ _ hlt).trans hi⟩
        · have hcast' : j.val ≠ i.val := fun he => hcast (Fin.ext he)
          have hsucc' : j.val ≠ i.val + 1 := fun he => hsucc (Fin.ext he)
          let k : Fin n := ⟨i.val + 1, by have := j.isLt; omega⟩
          exact ⟨k, (Fin.contractNth_apply_of_lt _ _ _ _ (show k.val < j.val by
            change i.val + 1 < j.val
            omega)).trans hi⟩
      rw [normalizedBar_of_identity hdeg, smul_zero]
    · have hne : i.castSucc ≠ i.succ := fun e => by
        have he := congrArg Fin.val e
        simp at he
      simp [hne]


theorem d_mem_degenerate (n : ℕ) {x : (chains G).X (n + 1)}
    (hx : x ∈ degenerate G (n + 1)) : (chains G).d (n + 1) n x ∈ degenerate G n := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have hle : degenerate G (n + 1) ≤
      ((degenerate G n).mkQ.comp ((chains G).d (n + 1) n).hom).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    exact normalization_annihilates_d g hg
  exact hle hx

private def normalizedDifferential (G : Type u) [Group G] (n : ℕ) :
    NormalizedModule G (n + 1) →ₗ[Integers.{u}] NormalizedModule G n :=
  (degenerate G (n + 1)).liftQ ((degenerate G n).mkQ.comp ((chains G).d (n + 1) n).hom)
    (fun _ hx => (Submodule.Quotient.mk_eq_zero _).mpr (d_mem_degenerate n hx))

/-- The bar complex with identity-containing tuples set to zero. -/
def normalizedChains (G : Type u) [Group G] : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of _ (NormalizedModule G n))
    (fun n => ModuleCat.ofHom (normalizedDifferential G n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := (degenerate G (n + 2)).mkQ_surjective x
      change (degenerate G n).mkQ ((chains G).d (n + 1) n
        ((chains G).d (n + 2) (n + 1) y)) = 0
      rw [show (chains G).d (n + 1) n ((chains G).d (n + 2) (n + 1) y) = 0 from
        DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
          ((chains G).d_comp_d (n + 2) (n + 1) n)) y, map_zero])

@[simp]
theorem normalizedChains_d_mk (n : ℕ) (x : (chains G).X (n + 1)) :
    (normalizedChains G).d (n + 1) n ((degenerate G (n + 1)).mkQ x) =
      (degenerate G n).mkQ ((chains G).d (n + 1) n x) := by
  have hd : (normalizedChains G).d (n + 1) n =
      ModuleCat.ofHom (normalizedDifferential G n) :=
    by
      unfold normalizedChains
      change ChainComplex.of.d (fun i => ModuleCat.of Integers.{u} (NormalizedModule G i))
        (fun i => ModuleCat.ofHom (normalizedDifferential G i)) (n + 1) n = _
      exact ChainComplex.of_d _ _ n
  rw [hd]
  rfl

/-- The canonical projection to normalized chains. -/
def normalization (G : Type u) [Group G] : chains G ⟶ normalizedChains G :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (degenerate G n).mkQ) (fun n => by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => normalizedChains_d_mk n x)

@[simp]
theorem normalization_f_apply (n : ℕ) (x : (chains G).X n) :
    (normalization G).f n x = (degenerate G n).mkQ x :=
  rfl

@[simp]
private theorem chainsMap_single_one (f : G →* H) (n : ℕ) (x : Fin n → G) :
    (chainsMap f).f n (bar n x) = bar n (f ∘ x) :=
  groupHomology.chainsMap_f_single f (coefficientMap f) n x 1

private theorem chainsMap_mem_degenerate (f : G →* H) (n : ℕ) {x : (chains G).X n}
    (hx : x ∈ degenerate G n) : (chainsMap f).f n x ∈ degenerate H n := by
  have hle : degenerate G n ≤ (degenerate H n).comap ((chainsMap f).f n).hom := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, ⟨j, hj⟩, rfl⟩
    change (chainsMap f).f n (bar n g) ∈ degenerate H n
    rw [chainsMap_single_one]
    exact bar_mem_degenerate ⟨j, by simp [hj]⟩
  exact hle hx

private def normalizedMapComponent (f : G →* H) (n : ℕ) :
    NormalizedModule G n →ₗ[Integers.{u}] NormalizedModule H n :=
  (degenerate G n).liftQ ((degenerate H n).mkQ.comp ((chainsMap f).f n).hom)
    (fun _ hx => (Submodule.Quotient.mk_eq_zero _).mpr (chainsMap_mem_degenerate f n hx))

/-- The normalized chain map acts on bar tuples by application in each entry. -/
def normalizedChainsMap (f : G →* H) : normalizedChains G ⟶ normalizedChains H :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (normalizedMapComponent f n)) (fun n => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (degenerate G (n + 1)).mkQ_surjective x
    change (normalizedChains H).d (n + 1) n
        ((degenerate H (n + 1)).mkQ ((chainsMap f).f (n + 1) y)) =
      normalizedMapComponent f n ((normalizedChains G).d (n + 1) n
        ((degenerate G (n + 1)).mkQ y))
    rw [normalizedChains_d_mk, normalizedChains_d_mk]
    apply congrArg (degenerate H n).mkQ
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      ((chainsMap f).comm (n + 1) n)) y)

end
end ALG02GroupTheory.IntegralBar

namespace ALG02GroupTheory.IntegralBar.Spec

noncomputable section

def commutatorGenerated : Prop :=
  ∀ {G : Type u} [Group G] (U V : Subgroup G),
    ⁅U, V⁆ = Subgroup.closure {x | ∃ u ∈ U, ∃ v ∈ V, u * v * u⁻¹ * v⁻¹ = x}

def ambientCommutatorNormal : Prop :=
  ∀ {G : Type u} [Group G] (N : Subgroup G) [N.Normal],
    (⁅(⊤ : Subgroup G), N⁆ : Subgroup G).Normal

def ambientCommutatorLe : Prop :=
  ∀ {G : Type u} [Group G] (N : Subgroup G) [N.Normal], ⁅(⊤ : Subgroup G), N⁆ ≤ N

def relativeQuotientCommutative : Prop :=
  ∀ {G : Type u} [Group G] (N : Subgroup G) [N.Normal],
    IsMulCommutative (N ⧸ relativeCommutator N)

def mapPulledBackCommutator : Prop :=
  ∀ {G : Type u} [Group G] {K : Type v} [Group K] (i : K →* G)
    (hi : Function.Injective i),
    (pulledBackCommutator i).map (MonoidHom.ofInjective hi).toMonoidHom =
      relativeCommutator i.range

set_option linter.checkUnivs false in
def kernelQuotientEquivType :=
  ∀ {G : Type u} [Group G] {K : Type v} [Group K] (i : K →* G)
    (_ : Function.Injective i) [i.range.Normal],
    (K ⧸ pulledBackCommutator i) ≃* (i.range ⧸ relativeCommutator i.range)

def kernelQuotientEquivValue : kernelQuotientEquivType.{u, v} :=
  fun i hi =>
    QuotientGroup.congr _ _ (MonoidHom.ofInjective hi) (by
      exact Subgroup.map_comap_eq_self_of_surjective
        (f := (MonoidHom.ofInjective hi).toMonoidHom) (MonoidHom.ofInjective hi).surjective
        (relativeCommutator i.range))

def kernelQuotientEquivMk : Prop :=
  ∀ {G : Type u} [Group G] {K : Type v} [Group K] (i : K →* G)
    (hi : Function.Injective i) [i.range.Normal] (k : K),
    kernelQuotientEquivValue i hi (QuotientGroup.mk k) =
      QuotientGroup.mk (MonoidHom.ofInjective hi k)

def kernelQuotientCommutative : Prop :=
  ∀ {G : Type u} [Group G] {K : Type v} [Group K] (i : K →* G)
    (_ : Function.Injective i) [i.range.Normal],
    IsMulCommutative (K ⧸ pulledBackCommutator i)

def h1EquivType :=
  ∀ (G : Type u) [Group G], homology G 1 ≃+ Additive (Abelianization G)

def h1EquivValue : h1EquivType.{u} :=
  fun G =>
    (groupHomology.H1AddEquivOfIsTrivial (coefficients G)).trans <|
      (TensorProduct.congr (LinearEquiv.refl ℤ _) ULift.moduleEquiv).toAddEquiv.trans
        (TensorProduct.rid ℤ _).toAddEquiv

def h1EquivGeneratorClass : Prop :=
  ∀ {G : Type u} [Group G] (g : G),
    h1EquivValue G (generatorClass g) = Additive.ofMul (Abelianization.of g)

def homologyMapGeneratorClass : Prop :=
  ∀ {G H : Type u} [Group G] [Group H] (f : G →* H) (g : G),
    homologyMap f 1 (generatorClass g) = generatorClass (f g)

def h1EquivNatural : Prop :=
  ∀ {G H : Type u} [Group G] [Group H] (f : G →* H) (x : homology G 1),
    h1EquivValue H (homologyMap f 1 x) =
      MonoidHom.toAdditive (Abelianization.map f) (h1EquivValue G x)

def chainsMapId : Prop :=
  ∀ {G : Type u} [Group G], chainsMap (MonoidHom.id G) = 𝟙 (chains G)

def chainsMapComp : Prop :=
  ∀ {G H L : Type u} [Group G] [Group H] [Group L] (f : G →* H) (g : H →* L),
    chainsMap (g.comp f) = chainsMap f ≫ chainsMap g

def homologyMapId : Prop :=
  ∀ {G : Type u} [Group G] (n : ℕ), homologyMap (MonoidHom.id G) n = 𝟙 (homology G n)

def homologyMapComp : Prop :=
  ∀ {G H L : Type u} [Group G] [Group H] [Group L] (f : G →* H) (g : H →* L) (n : ℕ),
    homologyMap (g.comp f) n = homologyMap f n ≫ homologyMap g n

def chainsMapBar : Prop :=
  ∀ {G H : Type u} [Group G] [Group H] (f : G →* H) (n : ℕ) (x : Fin n → G),
    (chainsMap f).f n (bar n x) = bar n (f ∘ x)

def normalizedChainsMapBar : Prop :=
  ∀ {G H : Type u} [Group G] [Group H] (f : G →* H) (n : ℕ) (x : Fin n → G),
    (normalizedChainsMap f).f n (normalizedBar n x) = normalizedBar n (f ∘ x)

def normalizedChainsMapId : Prop :=
  ∀ {G : Type u} [Group G], normalizedChainsMap (MonoidHom.id G) = 𝟙 (normalizedChains G)

def normalizedChainsMapComp : Prop :=
  ∀ {G H L : Type u} [Group G] [Group H] [Group L] (f : G →* H) (g : H →* L),
    normalizedChainsMap (g.comp f) = normalizedChainsMap f ≫ normalizedChainsMap g

def normalizationNatural : Prop :=
  ∀ {G H : Type u} [Group G] [Group H] (f : G →* H),
    normalization G ≫ normalizedChainsMap f = chainsMap f ≫ normalization H

def normalizationSurjective : Prop :=
  ∀ {G : Type u} [Group G] (n : ℕ), Function.Surjective ((normalization G).f n)

def normalizedChainsMapSurjective : Prop :=
  ∀ {G H : Type u} [Group G] [Group H] (f : G →* H) (_ : Function.Surjective f) (n : ℕ),
    Function.Surjective ((normalizedChainsMap f).f n)

def normalizedBarEqZero : Prop :=
  ∀ {G : Type u} [Group G] {n : ℕ} {g : Fin n → G} (_ : ∃ j, g j = 1),
    normalizedBar n g = 0

def dOneEqZero : Prop :=
  ∀ {G : Type u} [Group G], (chains G).d 1 0 = 0

def normalizedDOneEqZero : Prop :=
  ∀ {G : Type u} [Group G], (normalizedChains G).d 1 0 = 0

def barDOne : Prop :=
  ∀ {G : Type u} [Group G] (a : G), (chains G).d 1 0 (bar 1 ![a]) = 0

def barDTwo : Prop :=
  ∀ {G : Type u} [Group G] (a b : G),
    (chains G).d 2 1 (bar 2 ![a, b]) = bar 1 ![b] - bar 1 ![a * b] + bar 1 ![a]

def barDThree : Prop :=
  ∀ {G : Type u} [Group G] (a b c : G),
    (chains G).d 3 2 (bar 3 ![a, b, c]) =
      bar 2 ![b, c] - bar 2 ![a * b, c] + bar 2 ![a, b * c] - bar 2 ![a, b]

def normalizedBarDOne : Prop :=
  ∀ {G : Type u} [Group G] (a : G), (normalizedChains G).d 1 0 (normalizedBar 1 ![a]) = 0

def normalizedBarDTwo : Prop :=
  ∀ {G : Type u} [Group G] (a b : G),
    (normalizedChains G).d 2 1 (normalizedBar 2 ![a, b]) =
      normalizedBar 1 ![b] - normalizedBar 1 ![a * b] + normalizedBar 1 ![a]

def normalizedBarDThree : Prop :=
  ∀ {G : Type u} [Group G] (a b c : G),
    (normalizedChains G).d 3 2 (normalizedBar 3 ![a, b, c]) =
      normalizedBar 2 ![b, c] - normalizedBar 2 ![a * b, c] +
        normalizedBar 2 ![a, b * c] - normalizedBar 2 ![a, b]

def normalizationHomologyIsIso : Prop :=
  ∀ {G : Type u} [Group G] (n : ℕ) (_ : n ≤ 2),
    IsIso (HomologicalComplex.homologyMap (normalization G) n)

def normalizationHomologyNatural : Prop :=
  ∀ {G H : Type u} [Group G] [Group H] (f : G →* H) (n : ℕ),
    HomologicalComplex.homologyMap (normalization G) n ≫
        HomologicalComplex.homologyMap (normalizedChainsMap f) n =
      homologyMap f n ≫ HomologicalComplex.homologyMap (normalization H) n

end

end ALG02GroupTheory.IntegralBar.Spec
