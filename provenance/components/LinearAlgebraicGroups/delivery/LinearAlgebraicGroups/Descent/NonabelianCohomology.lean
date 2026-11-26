import Specs.LinearAlgebraicGroups.Descent.NonabelianCohomology
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.MulAction

open CategoryTheory Opposite AlgebraicGeometry
open scoped Topology CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Descent.NonabelianCohomology

universe u v w

/-- The continuous crossed homomorphisms for the coefficient action. -/
abbrev Z1 : Specification.CocyclesType := @Cocycle

/-- Two cocycles are equivalent if one is obtained from the other by a change of witness. -/
abbrev CocycleEquiv : Specification.EquivalenceType := @Cohomologous

/-- Continuous nonabelian first cohomology. -/
abbrev H1Continuous : Specification.CocyclesType := @H1

/-- The identity class in continuous nonabelian first cohomology. -/
abbrev neutralClass : Specification.BasepointType := @basepoint

/-- Galois cohomology of a group scheme with its natural action on discrete points
over the chosen separable closure. -/
noncomputable abbrev H1OfGroupScheme : Specification.GroupH1Type := @groupH1

/-- The identity class of the group scheme's Galois cohomology. -/
noncomputable abbrev neutralGroupClass : Specification.GroupBasepointType := @groupBasepoint

section Cohomology

variable {Γ : Type u} {M : Type v} [Group Γ] [TopologicalSpace Γ]
  [Group M] [TopologicalSpace M] {ρ : Γ →* MulAut M}

@[simp] theorem Cocycle.map_one (a : Cocycle ρ) : a 1 = 1 := by
  have h := a.property.2 1 1
  simpa using h

theorem classOf_eq_iff {a a' : Cocycle ρ} :
    classOf a = classOf a' ↔ Cohomologous a a' :=
  ⟨Quotient.exact, @Quotient.sound _ (cocycleSetoid ρ) _ _⟩

variable {Δ : Type w} [Group Δ] [TopologicalSpace Δ] [DiscreteTopology Δ]
  {q : Γ →* Δ}

omit [TopologicalSpace Δ] [DiscreteTopology Δ] in
private theorem same_restriction (a : Cocycle ρ) (h : ∀ n ∈ q.ker, a n = 1)
    {σ τ : Γ} (he : q σ = q τ) : a σ = a τ := by
  have hk : σ⁻¹ * τ ∈ q.ker := by simp [he]
  have ha := a.property.2 σ (σ⁻¹ * τ)
  simpa [h _ hk] using ha.symm

omit [TopologicalSpace Δ] [DiscreteTopology Δ] in
private theorem fixed_of_trivial_on_kernel (a : Cocycle ρ)
    (h : ∀ n ∈ q.ker, a n = 1) (σ : Γ) : a σ ∈ Fixed ρ q.ker := by
  intro n hn
  have he : q (n * σ) = q σ := by simp [MonoidHom.mem_ker.mp hn]
  simpa [h n hn] using (a.property.2 n σ).symm.trans (same_restriction a h he)

private theorem descend_of_trivial_on_kernel (hq : Function.Surjective q) (a : Cocycle ρ)
    (h : ∀ n ∈ q.ker, a n = 1) :
    ∃ c : Cocycle (quotientAction ρ q hq), ∀ σ, (c (q σ)).val = a σ := by
  obtain ⟨pick, hpick⟩ := hq.hasRightInverse
  let f (δ : Δ) : Fixed ρ q.ker :=
    ⟨a (pick δ), fixed_of_trivial_on_kernel a h (pick δ)⟩
  have hf (σ : Γ) : (f (q σ)).val = a σ :=
    same_restriction a h (hpick (q σ))
  refine ⟨⟨f, continuous_of_discreteTopology, ?_⟩, hf⟩
  intro δ ε
  obtain ⟨σ, rfl⟩ := hq δ
  obtain ⟨τ, rfl⟩ := hq ε
  apply Subtype.ext
  change (f (q σ * q τ)).val = (f (q σ)).val *
    (quotientAction ρ q hq (q σ) (f (q τ))).val
  rw [← map_mul q, hf, quotientAction_apply, hf, hf]
  exact a.property.2 σ τ

end Cohomology

section Galois

variable {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
  {M : Type v} [Group M] [TopologicalSpace M] [DiscreteTopology M]
  {ρ : Gal(S/k) →* MulAut M}

omit [IsGalois k S] in
private theorem restriction_ker (L : FiniteGaloisIntermediateField k S) :
    (restriction L).ker = L.fixingSubgroup :=
  L.toIntermediateField.restrictNormalHom_ker

omit [IsGalois k S] in
private theorem eventually_trivial (a : Cocycle ρ) :
    {σ | a σ = 1} ∈ 𝓝 (1 : Gal(S/k)) :=
  ((isOpen_discrete ({1} : Set M)).preimage a.property.1).mem_nhds (by simp)

private theorem finiteLevel_subgroup_above (L₀ : FiniteGaloisIntermediateField k S)
    {U : Set Gal(S/k)} (hU : U ∈ 𝓝 (1 : Gal(S/k))) :
    ∃ L : FiniteGaloisIntermediateField k S, L₀ ≤ L ∧
      ((restriction L).ker : Set Gal(S/k)) ⊆ U := by
  obtain ⟨L, hL⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois _).mp hU
  refine ⟨L₀ ⊔ L, le_sup_left, ?_⟩
  rw [restriction_ker]
  intro σ hσ
  have hle : L.toIntermediateField ≤ (L₀ ⊔ L).toIntermediateField :=
    (FiniteGaloisIntermediateField.le_iff _ _).mp le_sup_right
  exact hL (IntermediateField.fixingSubgroup_le hle hσ)

/-- A continuous cocycle is inflated from a finite Galois group acting on the
coefficient subgroup fixed by its restriction kernel. -/
theorem finiteLevel (L₀ : FiniteGaloisIntermediateField k S) (a : Cocycle ρ) :
    ∃ (L : FiniteGaloisIntermediateField k S) (c : Cocycle (levelAction ρ L)),
      L₀ ≤ L ∧ DescendsAt ρ a L c := by
  obtain ⟨L, hle, hL⟩ := finiteLevel_subgroup_above L₀ (eventually_trivial a)
  obtain ⟨c, hc⟩ := descend_of_trivial_on_kernel (AlgEquiv.restrictNormalHom_surjective S)
    a (fun n hn => hL hn)
  exact ⟨L, c, hle, hc⟩

/-- Equivalent continuous cocycles and their specified witness descend together. -/
theorem finiteLevelChangesBy (L₀ : FiniteGaloisIntermediateField k S)
    (a a' : Cocycle ρ) (b : M) (hb : ChangesBy a a' b) :
    ∃ (L : FiniteGaloisIntermediateField k S) (c c' : Cocycle (levelAction ρ L))
      (d : LevelCoefficients ρ L), L₀ ≤ L ∧ DescendsAt ρ a L c ∧ DescendsAt ρ a' L c' ∧
        d.val = b ∧ ChangesBy c c' d := by
  obtain ⟨L, hle, hL⟩ := finiteLevel_subgroup_above L₀
    (Filter.inter_mem (eventually_trivial a) (eventually_trivial a'))
  have h (n : Gal(S/k)) (hn : n ∈ (restriction L).ker) : a n = 1 ∧ a' n = 1 := hL hn
  have hq : Function.Surjective (restriction L) := AlgEquiv.restrictNormalHom_surjective S
  obtain ⟨c, hc⟩ := descend_of_trivial_on_kernel hq a (fun n hn => (h n hn).1)
  obtain ⟨c', hc'⟩ := descend_of_trivial_on_kernel hq a' (fun n hn => (h n hn).2)
  have hd : b ∈ LevelCoefficients ρ L := by
    intro n hn
    have he := hb n
    rw [(h n hn).1, (h n hn).2, mul_one] at he
    have he' := congrArg (b * ·) he
    simpa [mul_assoc] using he'.symm
  refine ⟨L, c, c', ⟨b, hd⟩, hle, hc, hc', rfl, ?_⟩
  intro δ
  obtain ⟨σ, rfl⟩ := hq δ
  apply Subtype.ext
  change (c' (restriction L σ)).val =
    b⁻¹ * (c (restriction L σ)).val * (levelAction ρ L (restriction L σ) ⟨b, hd⟩).val
  rw [hc', hc, quotientAction_apply]
  exact hb σ

/-- Equality of classes can be checked at a common finite Galois level. -/
theorem finiteLevelClassEq (L₀ : FiniteGaloisIntermediateField k S) (a a' : Cocycle ρ) :
    classOf a = classOf a' ↔
      ∃ (L : FiniteGaloisIntermediateField k S) (c c' : Cocycle (levelAction ρ L)),
        L₀ ≤ L ∧ DescendsAt ρ a L c ∧ DescendsAt ρ a' L c' ∧ classOf c = classOf c' := by
  constructor
  · intro he
    obtain ⟨b, hb⟩ := classOf_eq_iff.mp he
    obtain ⟨L, c, c', d, hle, hc, hc', _, hd⟩ := finiteLevelChangesBy L₀ a a' b hb
    exact ⟨L, c, c', hle, hc, hc', classOf_eq_iff.mpr ⟨d, hd⟩⟩
  · rintro ⟨L, c, c', _, hc, hc', he⟩
    obtain ⟨d, hd⟩ := classOf_eq_iff.mp he
    apply classOf_eq_iff.mpr
    refine ⟨d.val, fun σ => ?_⟩
    rw [← hc' σ, ← hc σ]
    have hh := congrArg Subtype.val (hd (restriction L σ))
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, quotientAction_apply] using hh

/-- Inflate a finite-level cocycle using restriction and the coefficient inclusion. -/
noncomputable def inflate (L : FiniteGaloisIntermediateField k S)
    (c : Cocycle (levelAction ρ L)) : Cocycle ρ :=
  ⟨fun σ => (c (restriction L σ)).val,
    continuous_subtype_val.comp
      (c.property.1.comp (InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField)),
    fun σ τ => by
      change (c (restriction L (σ * τ))).val =
        (c (restriction L σ)).val * ρ σ (c (restriction L τ)).val
      rw [map_mul]
      have h := congrArg Subtype.val (c.property.2 (restriction L σ) (restriction L τ))
      simpa only [Subgroup.coe_mul, quotientAction_apply] using h⟩

omit [DiscreteTopology M] in
theorem descendsAt_iff_inflate_eq (a : Cocycle ρ) (L : FiniteGaloisIntermediateField k S)
    (c : Cocycle (levelAction ρ L)) : DescendsAt ρ a L c ↔ inflate L c = a :=
  ⟨fun h => Subtype.ext (funext h), fun h σ => congrArg (fun a : Cocycle ρ => a σ) h⟩

/-- A Galois action on a discrete group is continuous exactly when every coefficient
is fixed by the kernel of some finite-level restriction. -/
theorem continuousAction_iff_finiteLevel :
    Continuous (fun p : Gal(S/k) × M => ρ p.1 p.2) ↔
      ∀ m : M, ∃ L : FiniteGaloisIntermediateField k S, m ∈ LevelCoefficients ρ L := by
  let actionHom : Gal(S/k) →* Function.End M :=
    { toFun := fun σ m => ρ σ m
      map_one' := by rw [map_one]; rfl
      map_mul' := fun σ τ => by rw [map_mul]; rfl }
  let : MulAction Gal(S/k) M := MulAction.ofEndHom actionHom
  change Continuous (fun p : Gal(S/k) × M => p.1 • p.2) ↔ _
  rw [show Continuous (fun p : Gal(S/k) × M => p.1 • p.2) ↔
      ContinuousSMul Gal(S/k) M from ⟨fun h => ⟨h⟩, fun h => h.continuous_smul⟩,
    continuousSMul_iff_stabilizer_isOpen]
  constructor
  · intro h m
    obtain ⟨L, -, hL⟩ := finiteLevel_subgroup_above (⊥ : FiniteGaloisIntermediateField k S)
      ((h m).mem_nhds (Subgroup.one_mem _))
    exact ⟨L, fun n hn => hL hn⟩
  · intro h m
    obtain ⟨L, hL⟩ := h m
    apply Subgroup.isOpen_mono (H₁ := (restriction L).ker)
    · exact hL
    · rw [restriction_ker]
      exact L.toIntermediateField.fixingSubgroup_isOpen

end Galois

section SchemePoints

set_option backward.isDefEq.respectTransparency false

variable {k S : Type u} [Field k] [Field S] [Algebra k S]
  {H : Over (Spec (CommRingCat.of k))} [GrpObj H]

@[simp] private theorem pointMap_left {L : Type u} [Field L] [Algebra k L]
    (f : L →ₐ[k] S) (p : Points k L H) :
    (pointMap k L H f p).left = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ p.left :=
  rfl

@[simp] private theorem pointAction_left (σ : Gal(S/k)) (p : Points k S H) :
    (pointAction k S H σ p).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p.left :=
  rfl

private theorem spec_precomp_injective {L : Type u} [Field L] (f : L →+* S)
    {X : Scheme.{u}} :
    Function.Injective (fun p : Spec (CommRingCat.of L) ⟶ X =>
      Spec.map (CommRingCat.ofHom f) ≫ p) := by
  intro p q hpq
  obtain ⟨⟨x, φ⟩, rfl⟩ := (X.SpecToEquivOfField L).symm.surjective p
  obtain ⟨⟨y, ψ⟩, rfl⟩ := (X.SpecToEquivOfField L).symm.surjective q
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hpq ⊢
  let z : ↑(Spec (CommRingCat.of S)) := IsLocalRing.closedPoint S
  have he := congrArg (fun t : Spec (CommRingCat.of S) ⟶ X => t z) hpq
  have hxy : x = y :=
    (Scheme.fromSpecResidueField_apply x _).symm.trans
      (he.trans (Scheme.fromSpecResidueField_apply y _))
  subst y
  simp only [← Category.assoc, ← Spec.map_comp, cancel_mono, Spec.map_inj] at hpq
  have hφψ : φ = ψ := by
    ext z
    exact f.injective (congrArg (fun t : X.residueField x ⟶ CommRingCat.of S => t z) hpq)
  rw [hφψ]

omit [GrpObj H] in
private theorem points_have_affine_factorization (p : Points k S H) :
    ∃ (A : CommRingCat.{u}) (i : Spec A ⟶ H.left), IsOpenImmersion i ∧
      ∃ (f : A ⟶ CommRingCat.of S), p.left = Spec.map f ≫ i := by
  obtain ⟨A, i, hi, hmem, _⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset
      (x := p.left (IsLocalRing.closedPoint S)) (U := ⊤) (by simp)
  let p' : Spec (CommRingCat.of S) ⟶ H.left := p.left
  have hsubset : Set.range p' ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y (IsLocalRing.closedPoint S)]
  let lift := IsOpenImmersion.lift i p' hsubset
  refine ⟨A, i, hi, Spec.preimage lift, ?_⟩
  change p' = Spec.map (Spec.preimage lift) ≫ i
  rw [Spec.map_preimage]
  exact (IsOpenImmersion.lift_fac i p' hsubset).symm

variable [IsGalois k S]

/-- The points defined over an intermediate finite Galois field are exactly
the points fixed by the kernel of restriction. -/
theorem finitePoints_iff_fixed (L : FiniteGaloisIntermediateField k S) (p : Points k S H) :
    p ∈ Set.range (pointMap k L H L.toIntermediateField.val) ↔
      p ∈ Fixed (pointAction k S H) (restriction L).ker := by
  constructor
  · rintro ⟨q, rfl⟩ σ hσ
    rw [restriction_ker] at hσ
    apply Over.OverMorphism.ext
    rw [pointAction_left, pointMap_left]
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom L.toIntermediateField.val.toRingHom) ≫ q.left =
      Spec.map (CommRingCat.ofHom L.toIntermediateField.val.toRingHom) ≫ q.left
    have he : CommRingCat.ofHom L.toIntermediateField.val.toRingHom ≫
        CommRingCat.ofHom σ.toRingHom =
        CommRingCat.ofHom L.toIntermediateField.val.toRingHom := by
      ext x
      exact (IntermediateField.mem_fixingSubgroup_iff L.toIntermediateField σ).mp hσ x x.2
    rw [← Category.assoc, ← Spec.map_comp, he]
  · intro hp
    obtain ⟨A, i, hi, φ, hφ⟩ := points_have_affine_factorization p
    have hrange (x : A) : φ x ∈ L.toIntermediateField := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L.toIntermediateField,
        IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hh := congrArg Over.Hom.left (hp σ (by rwa [restriction_ker]))
      rw [pointAction_left, hφ] at hh
      change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map φ ≫ i =
        Spec.map φ ≫ i at hh
      rw [← Category.assoc, ← Spec.map_comp, cancel_mono, Spec.map_inj] at hh
      exact congrArg (fun t : A ⟶ CommRingCat.of S => t x) hh
    let ψ : A →+* L := φ.hom.codRestrict L.toIntermediateField.toSubring hrange
    let q : Spec (CommRingCat.of L) ⟶ H.left := Spec.map (CommRingCat.ofHom ψ) ≫ i
    have he : Spec.map (CommRingCat.ofHom L.toIntermediateField.val.toRingHom) ≫ q = p.left := by
      change Spec.map (CommRingCat.ofHom L.toIntermediateField.val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ) ≫ i = (p.left : Spec (CommRingCat.of S) ⟶ H.left)
      exact (by
        rw [← Category.assoc, ← Spec.map_comp]
        exact hφ.symm)
    have hw : q ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
      apply spec_precomp_injective L.toIntermediateField.val.toRingHom
      dsimp only
      rw [← Category.assoc, he]
      have hpw : (p.left : Spec (CommRingCat.of S) ⟶ H.left) ≫ H.hom =
          Spec.map (CommRingCat.ofHom (algebraMap k S)) := Over.w p
      rw [hpw, ← Spec.map_comp]
      rfl
    let q' : Points k L H := Over.homMk q hw
    refine ⟨q', Over.OverMorphism.ext ?_⟩
    rw [pointMap_left]
    exact he

/-- Every point of a locally finite-type group over an algebraic Galois extension
is defined over a finite Galois intermediate field. -/
theorem point_defined_at_finite_level [LocallyOfFiniteType H.hom] (p : Points k S H) :
    ∃ L : FiniteGaloisIntermediateField k S,
      p ∈ Set.range (pointMap k L H L.toIntermediateField.val) := by
  classical
  obtain ⟨A, i, hi, φ, hφ⟩ := points_have_affine_factorization p
  let f : CommRingCat.of k ⟶ A := Spec.preimage (i ≫ H.hom)
  have hf : Spec.map f = i ≫ H.hom := Spec.map_preimage _
  let : Algebra k A := f.hom.toAlgebra
  have hfin : Algebra.FiniteType k A := by
    apply RingHom.finiteType_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := f)).mp
    rw [hf]
    infer_instance
  have hcomp : f ≫ φ = CommRingCat.ofHom (algebraMap k S) := by
    apply Spec.map_inj.mp
    rw [Spec.map_comp, hf, ← Category.assoc, ← hφ]
    exact Over.w p
  let g : A →ₐ[k] S :=
    { __ := φ.hom
      commutes' := fun x => congrArg (fun t : CommRingCat.of k ⟶ CommRingCat.of S => t x) hcomp }
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  have : Finite (↑(s.image g) : Set S) := (s.image g).finite_toSet.to_subtype
  let L := FiniteGaloisIntermediateField.adjoin k (↑(s.image g) : Set S)
  have hle : Algebra.adjoin k (s : Set A) ≤ L.toIntermediateField.toSubalgebra.comap g := by
    apply Algebra.adjoin_le
    intro x hx
    change g x ∈ L.toIntermediateField
    apply FiniteGaloisIntermediateField.subset_adjoin
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hmem (x : A) : g x ∈ L.toIntermediateField := by
    apply hle
    rw [hs]
    trivial
  refine ⟨L, (finitePoints_iff_fixed L p).mpr ?_⟩
  intro σ hσ
  rw [restriction_ker] at hσ
  apply Over.OverMorphism.ext
  rw [pointAction_left, hφ]
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map φ ≫ i = Spec.map φ ≫ i
  rw [← Category.assoc, ← Spec.map_comp, cancel_mono, Spec.map_inj]
  ext x
  exact (IntermediateField.mem_fixingSubgroup_iff L.toIntermediateField σ).mp hσ _ (hmem x)

/-- The finite-stage group of points is the kernel-fixed subgroup, compatibly
with the action of the finite Galois group. -/
theorem finitePointsIdentification (L : FiniteGaloisIntermediateField k S) :
    ∃ e : Points k L H ≃* LevelCoefficients (pointAction k S H) L,
      (∀ p, (e p).val = pointMap k L H L.toIntermediateField.val p) ∧
      (∀ δ p, e (pointAction k L H δ p) = levelAction (pointAction k S H) L δ (e p)) := by
  let f := pointMap k L H L.toIntermediateField.val
  let f' : Points k L H →* LevelCoefficients (pointAction k S H) L :=
    f.codRestrict _ (fun p => (finitePoints_iff_fixed L (f p)).mp ⟨p, rfl⟩)
  have hinj : Function.Injective f' := by
    intro p q h
    have he : f p = f q := congrArg Subtype.val h
    apply Over.OverMorphism.ext
    apply spec_precomp_injective L.toIntermediateField.val.toRingHom
    simpa only [f, pointMap_left] using congrArg Over.Hom.left he
  have hsurj : Function.Surjective f' := by
    intro m
    obtain ⟨p, hp⟩ := (finitePoints_iff_fixed L m.val).mpr m.property
    exact ⟨p, Subtype.ext hp⟩
  let e := MulEquiv.ofBijective f' ⟨hinj, hsurj⟩
  refine ⟨e, fun _ => rfl, ?_⟩
  intro δ p
  obtain ⟨σ, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective S :
    Function.Surjective (restriction L)) δ
  apply Subtype.ext
  change f (pointAction k L H (restriction L σ) p) =
    (levelAction (pointAction k S H) L (restriction L σ) (e p)).val
  rw [quotientAction_apply]
  change f (pointAction k L H (restriction L σ) p) = pointAction k S H σ (f p)
  apply Over.OverMorphism.ext
  simp only [f, pointAction_left, pointMap_left, ← Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom (restriction L σ).toRingHom ≫
        CommRingCat.ofHom L.toIntermediateField.val.toRingHom =
      CommRingCat.ofHom L.toIntermediateField.val.toRingHom ≫ CommRingCat.ofHom σ.toRingHom := by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ L x
  rw [he]

omit [IsGalois k S] in
/-- For a smooth group over k, the natural action on its discrete separable-closure
points is continuous. -/
theorem continuousPointAction [IsSepClosure k S] [Smooth H.hom] :
    letI : TopologicalSpace (Points k S H) := ⊥
    Continuous (fun p : Gal(S/k) × Points k S H => pointAction k S H p.1 p.2) := by
  let : TopologicalSpace (Points k S H) := ⊥
  let : DiscreteTopology (Points k S H) := ⟨rfl⟩
  apply (continuousAction_iff_finiteLevel (ρ := pointAction k S H)).mpr
  intro p
  obtain ⟨L, hL⟩ := point_defined_at_finite_level p
  exact ⟨L, (finitePoints_iff_fixed L p).mp hL⟩

end SchemePoints

end LinearAlgebraicGroups.Descent.NonabelianCohomology
