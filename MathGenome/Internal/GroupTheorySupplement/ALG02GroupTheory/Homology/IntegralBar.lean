import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.IntegralBar
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence

open CategoryTheory Category Finsupp

universe u v

namespace ALG02GroupTheory.IntegralBar

noncomputable section

variable {G H L : Type u} [Group G] [Group H] [Group L]

theorem commutator_generated (U V : Subgroup G) :
    ⁅U, V⁆ = Subgroup.closure {x | ∃ u ∈ U, ∃ v ∈ V, u * v * u⁻¹ * v⁻¹ = x} :=
  Subgroup.commutator_def U V

theorem ambientCommutator_normal (N : Subgroup G) [N.Normal] :
    (⁅(⊤ : Subgroup G), N⁆ : Subgroup G).Normal :=
  inferInstance

theorem ambientCommutator_le (N : Subgroup G) [N.Normal] :
    ⁅(⊤ : Subgroup G), N⁆ ≤ N :=
  Subgroup.commutator_le_right _ _

theorem relativeQuotient_commutative (N : Subgroup G) [N.Normal] :
    IsMulCommutative (N ⧸ relativeCommutator N) := by
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  apply Subgroup.commutator_le.mpr
  intro a _ b _
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a.1) b.2

theorem map_pulledBackCommutator {K : Type v} [Group K]
    (i : K →* G) (hi : Function.Injective i) :
    (pulledBackCommutator i).map (MonoidHom.ofInjective hi).toMonoidHom =
      relativeCommutator i.range :=
  Subgroup.map_comap_eq_self_of_surjective
    (f := (MonoidHom.ofInjective hi).toMonoidHom) (MonoidHom.ofInjective hi).surjective
    (relativeCommutator i.range)

/-- Transport of the kernel quotient along the isomorphism onto the kernel image. -/
def kernelQuotientEquiv {K : Type v} [Group K] (i : K →* G)
    (hi : Function.Injective i) [i.range.Normal] :
    (K ⧸ pulledBackCommutator i) ≃* (i.range ⧸ relativeCommutator i.range) :=
  QuotientGroup.congr _ _ (MonoidHom.ofInjective hi) (map_pulledBackCommutator i hi)

@[simp]
theorem kernelQuotientEquiv_mk {K : Type v} [Group K] (i : K →* G)
    (hi : Function.Injective i) [i.range.Normal] (k : K) :
    kernelQuotientEquiv i hi (QuotientGroup.mk k) =
      QuotientGroup.mk (MonoidHom.ofInjective hi k) :=
  QuotientGroup.congr_mk _ _ _ _ _

theorem kernelQuotient_commutative {K : Type v} [Group K] (i : K →* G)
    (hi : Function.Injective i) [i.range.Normal] :
    IsMulCommutative (K ⧸ pulledBackCommutator i) := by
  let _ := relativeQuotient_commutative i.range
  refine ⟨⟨fun a b => (kernelQuotientEquiv i hi).injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact mul_comm' _ _

/-- Abelianization identifies integral first homology with the abelian quotient. -/
def h1Equiv (G : Type u) [Group G] : homology G 1 ≃+ Additive (Abelianization G) :=
  (groupHomology.H1AddEquivOfIsTrivial (coefficients G)).trans <|
    (TensorProduct.congr (LinearEquiv.refl ℤ _) ULift.moduleEquiv).toAddEquiv.trans
      (TensorProduct.rid ℤ _).toAddEquiv

@[simp]
theorem h1Equiv_generatorClass (g : G) :
    h1Equiv G (generatorClass g) = Additive.ofMul (Abelianization.of g) := by
  unfold h1Equiv generatorClass
  rw [AddEquiv.trans_apply, groupHomology.H1AddEquivOfIsTrivial_single]
  change (1 : ℤ) • Additive.ofMul (Abelianization.of g) = _
  exact one_smul ℤ _

@[simp]
theorem homologyMap_generatorClass (f : G →* H) (g : G) :
    homologyMap f 1 (generatorClass g) = generatorClass (f g) := by
  unfold generatorClass
  rw [groupHomology.H1π_comp_map_apply]
  refine congrArg (groupHomology.H1π (coefficients H)) (Subtype.ext ?_)
  change groupHomology.chainsMap₁ f (coefficientMap f) (single g 1) = single (f g) 1
  simp [groupHomology.chainsMap₁]
  rfl

theorem h1Equiv_natural (f : G →* H) (x : homology G 1) :
    h1Equiv H (homologyMap f 1 x) =
      MonoidHom.toAdditive (Abelianization.map f) (h1Equiv G x) := by
  obtain ⟨y, rfl⟩ := (h1Equiv G).symm.surjective x
  refine QuotientGroup.induction_on (α := G) y ?_
  intro g
  have eq : (h1Equiv G).symm (Additive.ofMul (Abelianization.of g)) = generatorClass g :=
    (AddEquiv.symm_apply_eq _).mpr (h1Equiv_generatorClass g).symm
  change h1Equiv H (homologyMap f 1
    ((h1Equiv G).symm (Additive.ofMul (Abelianization.of g)))) =
    MonoidHom.toAdditive (Abelianization.map f)
      (h1Equiv G ((h1Equiv G).symm (Additive.ofMul (Abelianization.of g))))
  rw [eq, homologyMap_generatorClass, h1Equiv_generatorClass, h1Equiv_generatorClass]
  rfl

theorem chainsMap_id : chainsMap (MonoidHom.id G) = 𝟙 (chains G) :=
  groupHomology.chainsMap_id

theorem chainsMap_comp (f : G →* H) (g : H →* L) :
    chainsMap (g.comp f) = chainsMap f ≫ chainsMap g := by
  rw [← groupHomology.chainsMap_comp]
  rfl

theorem homologyMap_id (n : ℕ) : homologyMap (MonoidHom.id G) n = 𝟙 (homology G n) :=
  groupHomology.map_id n

theorem homologyMap_comp (f : G →* H) (g : H →* L) (n : ℕ) :
    homologyMap (g.comp f) n = homologyMap f n ≫ homologyMap g n := by
  rw [← groupHomology.map_comp]
  rfl

@[simp]
theorem chainsMap_bar (f : G →* H) (n : ℕ) (x : Fin n → G) :
    (chainsMap f).f n (bar n x) = bar n (f ∘ x) :=
  groupHomology.chainsMap_f_single f (coefficientMap f) n x 1

@[simp]
theorem normalizedChainsMap_bar (f : G →* H) (n : ℕ) (x : Fin n → G) :
    (normalizedChainsMap f).f n (normalizedBar n x) = normalizedBar n (f ∘ x) := by
  change (degenerate H n).mkQ ((chainsMap f).f n (bar n x)) = _
  rw [chainsMap_bar]

theorem normalization_natural (f : G →* H) :
    normalization G ≫ normalizedChainsMap f = chainsMap f ≫ normalization H := by
  ext n : 1
  rfl

theorem normalizedBar_eq_zero {n : ℕ} {g : Fin n → G} (h : ∃ j, g j = 1) :
    normalizedBar n g = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (bar_mem_degenerate h)

theorem normalization_f_surjective (n : ℕ) :
    Function.Surjective ((normalization G).f n) :=
  (degenerate G n).mkQ_surjective

theorem normalizedChainsMap_f_surjective (f : G →* H) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective ((normalizedChainsMap f).f n) := by
  have : Epi (coefficientMap f) := inferInstanceAs (Epi (𝟙 (coefficients G)))
  have hs : Function.Surjective ((chainsMap f).f n) :=
    (ModuleCat.epi_iff_surjective _).mp
      (groupHomology.chainsMap_f_map_epi f (coefficientMap f) hf n)
  intro x
  obtain ⟨y, rfl⟩ := normalization_f_surjective (G := H) n x
  obtain ⟨z, rfl⟩ := hs y
  exact ⟨(normalization G).f n z, rfl⟩

theorem normalizedChainsMap_id :
    normalizedChainsMap (MonoidHom.id G) = 𝟙 (normalizedChains G) := by
  have : Epi (normalization G) := HomologicalComplex.epi_of_epi_f _ (fun n =>
    (ModuleCat.epi_iff_surjective _).mpr (normalization_f_surjective n))
  apply (cancel_epi (normalization G)).mp
  rw [normalization_natural, chainsMap_id, Category.id_comp, Category.comp_id]

theorem normalizedChainsMap_comp (f : G →* H) (g : H →* L) :
    normalizedChainsMap (g.comp f) = normalizedChainsMap f ≫ normalizedChainsMap g := by
  have : Epi (normalization G) := HomologicalComplex.epi_of_epi_f _ (fun n =>
    (ModuleCat.epi_iff_surjective _).mpr (normalization_f_surjective n))
  apply (cancel_epi (normalization G)).mp
  rw [normalization_natural, chainsMap_comp, Category.assoc, ← Category.assoc (normalization G),
    normalization_natural, Category.assoc, normalization_natural]

theorem d_one_eq_zero : (chains G).d 1 0 = 0 := by
  apply (cancel_epi (groupHomology.chainsIso₁ (coefficients G)).inv).mp
  rw [groupHomology.eq_d₁₀_comp_inv, groupHomology.d₁₀_eq_zero_of_isTrivial]
  simp

theorem normalized_d_one_eq_zero : (normalizedChains G).d 1 0 = 0 := by
  have : Epi ((normalization G).f 1) :=
    (ModuleCat.epi_iff_surjective _).mpr (normalization_f_surjective 1)
  apply (cancel_epi ((normalization G).f 1)).mp
  rw [(normalization G).comm, d_one_eq_zero]
  simp

theorem bar_d_one (a : G) : (chains G).d 1 0 (bar 1 ![a]) = 0 := by
  rw [d_one_eq_zero]
  rfl

theorem bar_d_two (a b : G) :
    (chains G).d 2 1 (bar 2 ![a, b]) =
      bar 1 ![b] - bar 1 ![a * b] + bar 1 ![a] := by
  rw [show (chains G).d 2 1 =
    groupHomology.inhomogeneousChains.d (coefficients G) 1 from
    groupHomology.inhomogeneousChains.d_def _ _]
  unfold bar
  rw [groupHomology.inhomogeneousChains.d_single (A := coefficients G)]
  have h₀ : (fun i : Fin 1 => ![a, b] i.succ) = ![b] := by
    funext i
    fin_cases i
    rfl
  have h₁ : Fin.contractNth (0 : Fin 2) (· * ·) ![a, b] = ![a * b] := by
    funext i
    fin_cases i
    rfl
  have h₂ : Fin.contractNth (1 : Fin 2) (· * ·) ![a, b] = ![a] := by
    funext i
    fin_cases i
    rfl
  change single (fun i : Fin 1 => ![a, b] i.succ) 1 + _ = _
  rw [h₀]
  simp [Fin.sum_univ_two, h₁, h₂, sub_eq_add_neg, add_assoc]

theorem bar_d_three (a b c : G) :
    (chains G).d 3 2 (bar 3 ![a, b, c]) =
      bar 2 ![b, c] - bar 2 ![a * b, c] + bar 2 ![a, b * c] - bar 2 ![a, b] := by
  rw [show (chains G).d 3 2 =
    groupHomology.inhomogeneousChains.d (coefficients G) 2 from
    groupHomology.inhomogeneousChains.d_def _ _]
  unfold bar
  rw [groupHomology.inhomogeneousChains.d_single (A := coefficients G)]
  have h₀ : (fun i : Fin 2 => ![a, b, c] i.succ) = ![b, c] := by
    funext i
    fin_cases i <;> rfl
  have h₁ : Fin.contractNth (0 : Fin 3) (· * ·) ![a, b, c] = ![a * b, c] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : Fin.contractNth (1 : Fin 3) (· * ·) ![a, b, c] = ![a, b * c] := by
    funext i
    fin_cases i <;> rfl
  have h₃ : Fin.contractNth (2 : Fin 3) (· * ·) ![a, b, c] = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  change single (fun i : Fin 2 => ![a, b, c] i.succ) 1 + _ = _
  rw [h₀]
  simp [Fin.sum_univ_three, h₁, h₂, h₃, sub_eq_add_neg, add_assoc, pow_succ]
  abel

theorem normalizedBar_d_one (a : G) :
    (normalizedChains G).d 1 0 (normalizedBar 1 ![a]) = 0 := by
  rw [normalized_d_one_eq_zero]
  rfl

theorem normalizedBar_d_two (a b : G) :
    (normalizedChains G).d 2 1 (normalizedBar 2 ![a, b]) =
      normalizedBar 1 ![b] - normalizedBar 1 ![a * b] + normalizedBar 1 ![a] := by
  rw [normalizedChains_d_mk (n := 1), bar_d_two, map_add, map_sub]

theorem normalizedBar_d_three (a b c : G) :
    (normalizedChains G).d 3 2 (normalizedBar 3 ![a, b, c]) =
      normalizedBar 2 ![b, c] - normalizedBar 2 ![a * b, c] +
        normalizedBar 2 ![a, b * c] - normalizedBar 2 ![a, b] := by
  rw [normalizedChains_d_mk (n := 2), bar_d_three, map_sub, map_add, map_sub]


private def degenerateDifferential (G : Type u) [Group G] (n : ℕ) :
    degenerate G (n + 1) →ₗ[Integers.{u}] degenerate G n :=
  ((chains G).d (n + 1) n).hom.restrict (fun _ hx => d_mem_degenerate n hx)

private def degenerateChains (G : Type u) [Group G] : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of _ (degenerate G n))
    (fun n => ModuleCat.ofHom (degenerateDifferential G n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        ((chains G).d_comp_d (n + 2) (n + 1) n)) x.val)

private theorem degenerateChains_d (n : ℕ) :
    (degenerateChains G).d (n + 1) n = ModuleCat.ofHom (degenerateDifferential G n) := by
  unfold degenerateChains
  change ChainComplex.of.d (fun i => ModuleCat.of Integers.{u} (degenerate G i))
    (fun i => ModuleCat.ofHom (degenerateDifferential G i)) (n + 1) n = _
  exact ChainComplex.of_d _ _ n

private def degenerateInclusion (G : Type u) [Group G] : degenerateChains G ⟶ chains G :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (degenerate G n).subtype) (fun n => by
    rw [degenerateChains_d]
    rfl)

private def normalizationSequence (G : Type u) [Group G] :
    ShortComplex (ChainComplex (ModuleCat.{u} Integers.{u}) ℕ) :=
  ShortComplex.mk (degenerateInclusion G) (normalization G) (by
    ext n : 1
    exact ModuleCat.hom_ext (LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).mpr x.2))

private theorem normalizationSequence_shortExact : (normalizationSequence G).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · change ∀ x : (chains G).X n, (degenerate G n).mkQ x = 0 ↔
        x ∈ Set.range (degenerate G n).subtype
    intro x
    refine (Submodule.Quotient.mk_eq_zero _).trans ?_
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
  · exact Subtype.val_injective
  · exact (degenerate G n).mkQ_surjective

private theorem degenerate_zero : degenerate G 0 = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨g, ⟨j, _⟩, _⟩
  exact Fin.elim0 j

private def degenerateBoundaries (G : Type u) [Group G] (n : ℕ) :
    Submodule Integers.{u} ((chains G).X n) :=
  LinearMap.range (((chains G).d (n + 1) n).hom.comp (degenerate G (n + 1)).subtype)

private theorem degenerate_one_le_boundaries : degenerate G 1 ≤ degenerateBoundaries G 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, ⟨i, hi⟩, rfl⟩
  have hg : g = ![(1 : G)] := by
    funext j
    have hj : j = i := Subsingleton.elim _ _
    subst j
    simpa using hi
  rw [hg]
  refine ⟨⟨bar 2 ![(1 : G), 1], bar_mem_degenerate ⟨0, rfl⟩⟩, ?_⟩
  change (chains G).d 2 1 (bar 2 ![(1 : G), 1]) = _
  rw [bar_d_two, one_mul, sub_self, zero_add]

/-- Subtract the identity-pair multiple detected by the identity coefficient of the boundary. -/
private def correctedBarChain (G : Type u) [Group G] :
    (chains G).X 2 →ₗ[Integers.{u}] (chains G).X 2 :=
  LinearMap.id - (LinearMap.toSpanSingleton Integers.{u} _ (bar 2 ![(1 : G), 1])).comp
    ((Finsupp.lapply (R := Integers.{u}) ![(1 : G)]).comp ((chains G).d 2 1).hom)

private theorem correctedBarChain_apply (x : (chains G).X 2) :
    correctedBarChain G x =
      x - ((chains G).d 2 1 x) ![(1 : G)] • bar 2 ![(1 : G), 1] :=
  rfl

private theorem correctedBarChain_mem_boundaries {x : (chains G).X 2}
    (hx : x ∈ degenerate G 2) : correctedBarChain G x ∈ degenerateBoundaries G 2 := by
  have h : degenerate G 2 ≤ (degenerateBoundaries G 2).comap (correctedBarChain G) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, ⟨i, hi⟩, rfl⟩
    have hg : g = ![g 0, g 1] := by
      funext j
      fin_cases j <;> rfl
    change correctedBarChain G (bar 2 g) ∈ degenerateBoundaries G 2
    rw [hg, correctedBarChain_apply, bar_d_two]
    fin_cases i
    · have ho : g 0 = 1 := hi
      rw [ho, one_mul, sub_self, zero_add]
      have hc : (bar 1 ![(1 : G)]) ![(1 : G)] = 1 := single_eq_same
      rw [hc, one_smul]
      refine ⟨⟨bar 3 ![(1 : G), 1, g 1], bar_mem_degenerate ⟨0, rfl⟩⟩, ?_⟩
      change (chains G).d 3 2 (bar 3 ![(1 : G), 1, g 1]) = _
      rw [bar_d_three, one_mul, sub_self, zero_add, one_mul]
    · have ho : g 1 = 1 := hi
      rw [ho, mul_one, sub_add_cancel]
      have hc : (bar 1 ![(1 : G)]) ![(1 : G)] = 1 := single_eq_same
      rw [hc, one_smul]
      refine ⟨⟨-bar 3 ![g 0, (1 : G), 1],
        Submodule.neg_mem _ (bar_mem_degenerate ⟨1, rfl⟩)⟩, ?_⟩
      change (chains G).d 3 2 (-bar 3 ![g 0, (1 : G), 1]) = _
      rw [map_neg, bar_d_three, mul_one, one_mul, sub_add_cancel, neg_sub]
  exact h hx

private theorem degenerate_two_mem_boundaries {x : (chains G).X 2}
    (hx : x ∈ degenerate G 2) (hcycle : (chains G).d 2 1 x = 0) :
    x ∈ degenerateBoundaries G 2 := by
  have h := correctedBarChain_mem_boundaries hx
  rwa [correctedBarChain_apply, hcycle, Finsupp.zero_apply, zero_smul, sub_zero] at h


private theorem degenerate_exact_at_zero : (degenerateChains G).ExactAt 0 := by
  apply ShortComplex.exact_of_isZero_X₂
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (degenerate G 0)
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [degenerate_zero] at hx hy
  exact Subtype.ext (hx.trans hy.symm)

private theorem degenerate_exact_at_succ (n : ℕ)
    (h : ∀ x ∈ degenerate G (n + 1), (chains G).d (n + 1) n x = 0 →
      x ∈ degenerateBoundaries G (n + 1)) :
    (degenerateChains G).ExactAt (n + 1) := by
  apply ShortComplex.exact_of_iso
    ((degenerateChains G).isoSc' (n + 2) (n + 1) n
      (ChainComplex.prev ℕ _) (ChainComplex.next_nat_succ _)).symm
  apply ModuleCat.shortComplex_exact
  change ∀ x : degenerate G (n + 1), (degenerateChains G).d (n + 1) n x = 0 ↔
    x ∈ Set.range ((degenerateChains G).d (n + 2) (n + 1))
  rw [degenerateChains_d, degenerateChains_d]
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := h x.val x.property (congrArg Subtype.val hx)
    exact ⟨y, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      ((chains G).d_comp_d (n + 2) (n + 1) n)) y.val

private theorem degenerate_homology_isZero (n : ℕ) (hn : n ≤ 2) :
    Limits.IsZero ((degenerateChains G).homology n) := by
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
  interval_cases n
  · exact degenerate_exact_at_zero
  · exact degenerate_exact_at_succ 0 (fun _ hx _ => degenerate_one_le_boundaries hx)
  · exact degenerate_exact_at_succ 1 (fun _ hx hz => degenerate_two_mem_boundaries hx hz)

/-- The quotient to normalized bar chains induces an isomorphism in degrees zero to two. -/
theorem normalization_homology_isIso (n : ℕ) (hn : n ≤ 2) :
    IsIso (HomologicalComplex.homologyMap (normalization G) n) := by
  have hS := normalizationSequence_shortExact (G := G)
  have hzero := degenerate_homology_isZero (G := G) n hn
  have hm : Mono (HomologicalComplex.homologyMap (normalization G) n) :=
    (hS.homology_exact₂ n).mono_g (hzero.eq_of_src _ _)
  have he : Epi (HomologicalComplex.homologyMap (normalization G) n) := by
    cases n with
    | zero =>
      have : Epi ((normalization G).f 0) :=
        (ModuleCat.epi_iff_surjective _).mpr (degenerate G 0).mkQ_surjective
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)
    | succ n =>
      have hh : (ComplexShape.down ℕ).Rel (n + 1) n := by simp
      exact (hS.homology_exact₃ (n + 1) n hh).epi_f
        ((degenerate_homology_isZero (G := G) n (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The canonical normalization isomorphism on integral homology in low degrees. -/
def normalizationHomologyIso (G : Type u) [Group G] (n : ℕ) (hn : n ≤ 2) :
    homology G n ≅ (normalizedChains G).homology n :=
  @asIso _ _ _ _ _ (normalization_homology_isIso (G := G) n hn)

theorem normalization_homology_natural (f : G →* H) (n : ℕ) :
    HomologicalComplex.homologyMap (normalization G) n ≫
        HomologicalComplex.homologyMap (normalizedChainsMap f) n =
      homologyMap f n ≫ HomologicalComplex.homologyMap (normalization H) n := by
  rw [← HomologicalComplex.homologyMap_comp]
  change HomologicalComplex.homologyMap (normalization G ≫ normalizedChainsMap f) n =
    HomologicalComplex.homologyMap (chainsMap f) n ≫ _
  rw [normalization_natural, HomologicalComplex.homologyMap_comp]

end
end ALG02GroupTheory.IntegralBar
