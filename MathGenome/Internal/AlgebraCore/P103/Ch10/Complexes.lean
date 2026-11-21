import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Complexes

/-! Explicit quotient homology of arbitrary module complexes. See the independent
Specs for the shared definitions and the left/right module convention. -/
namespace P103.Ch10.Complexes
open CategoryTheory
noncomputable section
universe u v w w'

abbrev Chain := @P103.Specs.Ch10.Complexes.Chain.{u,v}
abbrev Cochain := @P103.Specs.Ch10.Complexes.Cochain.{u,v}
abbrev cycles := @P103.Specs.Ch10.Complexes.cycles.{u,v,w}
abbrev boundaries := @P103.Specs.Ch10.Complexes.boundaries.{u,v,w}
abbrev cycleBoundaries := @P103.Specs.Ch10.Complexes.cycleBoundaries.{u,v,w}
abbrev Homology := @P103.Specs.Ch10.Complexes.Homology.{u,v,w}
abbrev homologyClass := @P103.Specs.Ch10.Complexes.homologyClass.{u,v,w}
abbrev cyclesMap := @P103.Specs.Ch10.Complexes.cyclesMap.{u,v,w}
abbrev homologyMap := @P103.Specs.Ch10.Complexes.homologyMap.{u,v,w}
abbrev Acyclic := @P103.Specs.Ch10.Complexes.Acyclic.{u,v,w}
abbrev QuasiIsomorphism := @P103.Specs.Ch10.Complexes.QuasiIsomorphism.{u,v,w}
abbrev SupportedIn := @P103.Specs.Ch10.Complexes.SupportedIn.{u,v,w}
abbrev extendByZero := @P103.Specs.Ch10.Complexes.extendByZero.{u,v,w,w'}
abbrev extendByZeroTermEquiv := @P103.Specs.Ch10.Complexes.extendByZeroTermEquiv.{u,v,w,w'}
abbrev nonnegativeChainEmbedding := P103.Specs.Ch10.Complexes.nonnegativeChainEmbedding
abbrev extendNonnegativeChain := @P103.Specs.Ch10.Complexes.extendNonnegativeChain.{u,v}
abbrev extendNonnegativeCochain := @P103.Specs.Ch10.Complexes.extendNonnegativeCochain.{u,v}

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
variable {C D E : HomologicalComplex (ModuleCat.{v} R) c}

theorem differential_squared (C : HomologicalComplex (ModuleCat.{v} R) c) (i j k : ι) :
    (C.d j k).hom.comp (C.d i j).hom = 0 := by
  exact congrArg ModuleCat.Hom.hom (C.d_comp_d i j k)

theorem boundaries_le_cycles (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    boundaries C n ≤ cycles C n := P103.Specs.Ch10.Complexes.boundaryInclusion C n

theorem cycleBoundaries_image (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    (cycleBoundaries C n).map (cycles C n).subtype = boundaries C n := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hx
    exact ⟨⟨x, boundaries_le_cycles C n hx⟩, hx, rfl⟩

theorem map_cycles (f : C ⟶ D) (n : ι) {z : C.X n} (hz : z ∈ cycles C n) :
    (f.f n).hom z ∈ cycles D n := (cyclesMap f n ⟨z, hz⟩).property

theorem map_boundaries (f : C ⟶ D) (n : ι) {z : C.X n} (hz : z ∈ boundaries C n) :
    (f.f n).hom z ∈ boundaries D n := by
  exact P103.Specs.Ch10.Complexes.mapBoundary f n (show (⟨z, boundaries_le_cycles C n hz⟩ : cycles C n) ∈
    cycleBoundaries C n from hz)

@[simp] theorem cyclesMap_apply (f : C ⟶ D) (n : ι) (z : cycles C n) :
    (cyclesMap f n z : D.X n) = (f.f n).hom z.val := rfl

@[simp] theorem homologyMap_apply (f : C ⟶ D) (n : ι) (z : cycles C n) :
    homologyMap f n (homologyClass C n z) = homologyClass D n (cyclesMap f n z) := rfl

theorem homologyClass_eq_iff (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι)
    (z z' : cycles C n) :
    homologyClass C n z = homologyClass C n z' ↔ z.val - z'.val ∈ boundaries C n := by
  exact Submodule.Quotient.eq (cycleBoundaries C n)

theorem homologyMap_wellDefined (f : C ⟶ D) (n : ι) (z z' : cycles C n)
    (h : z.val - z'.val ∈ boundaries C n) :
    homologyClass D n (cyclesMap f n z) = homologyClass D n (cyclesMap f n z') := by
  exact congrArg (homologyMap f n) ((homologyClass_eq_iff C n z z').mpr h)

@[simp] theorem homologyMap_id (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    homologyMap (𝟙 C) n = LinearMap.id := by
  apply (cycleBoundaries C n).quot_hom_ext
  intro z
  rfl

@[simp] theorem homologyMap_comp (f : C ⟶ D) (g : D ⟶ E) (n : ι) :
    homologyMap (f ≫ g) n = (homologyMap g n).comp (homologyMap f n) := by
  apply (cycleBoundaries C n).quot_hom_ext
  intro z
  rfl

@[simp] theorem homologyMap_add (f g : C ⟶ D) (n : ι) :
    homologyMap (f + g) n = homologyMap f n + homologyMap g n := by
  apply (cycleBoundaries C n).quot_hom_ext
  intro z
  change homologyClass D n (cyclesMap (f + g) n z) =
    homologyClass D n (cyclesMap f n z) + homologyClass D n (cyclesMap g n z)
  rw [← map_add]
  congr 1

@[simp] theorem homologyMap_zero (C D : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    homologyMap (0 : C ⟶ D) n = 0 := by
  apply (cycleBoundaries C n).quot_hom_ext
  intro z
  change homologyClass D n 0 = 0
  exact map_zero _

theorem acyclic_iff (C : HomologicalComplex (ModuleCat.{v} R) c) :
    Acyclic C ↔ ∀ n, boundaries C n = cycles C n := by
  constructor
  · intro h n
    apply le_antisymm (boundaries_le_cycles C n)
    intro x hx
    have hz : homologyClass C n ⟨x, hx⟩ = 0 := (h n).elim _ _
    exact (Submodule.Quotient.mk_eq_zero (cycleBoundaries C n)).mp hz
  · intro h n
    apply (Submodule.Quotient.subsingleton_iff).mpr
    apply top_unique
    intro z _
    change z.val ∈ boundaries C n
    rw [h n]
    exact z.property

theorem quasiIsomorphism_iff (f : C ⟶ D) :
    QuasiIsomorphism f ↔ ∀ n, ∃ e : Homology C n ≃ₗ[R] Homology D n,
      e.toLinearMap = homologyMap f n := by
  constructor
  · intro h n
    exact ⟨LinearEquiv.ofBijective (homologyMap f n) (h n), rfl⟩
  · intro h n
    obtain ⟨e, he⟩ := h n
    change Function.Bijective (homologyMap f n)
    rw [← he]
    exact e.bijective

/-- Specialization checks: outgoing/incoming degrees are the source's n-1/n+1. -/
theorem cycles_chain (C : Chain.{u,v} R) (n : ℤ) :
    cycles C n = LinearMap.ker (C.d n (n - 1)).hom := by
  dsimp only [cycles, P103.Specs.Ch10.Complexes.cycles]
  rw [ChainComplex.next]

theorem boundaries_chain (C : Chain.{u,v} R) (n : ℤ) :
    boundaries C n = LinearMap.range (C.d (n + 1) n).hom := by
  dsimp only [boundaries, P103.Specs.Ch10.Complexes.boundaries]
  rw [ChainComplex.prev]

theorem cycles_cochain (C : Cochain.{u,v} R) (n : ℤ) :
    cycles C n = LinearMap.ker (C.d n (n + 1)).hom := by
  dsimp only [cycles, P103.Specs.Ch10.Complexes.cycles]
  rw [CochainComplex.next]

theorem boundaries_cochain (C : Cochain.{u,v} R) (n : ℤ) :
    boundaries C n = LinearMap.range (C.d (n - 1) n).hom := by
  dsimp only [boundaries, P103.Specs.Ch10.Complexes.boundaries]
  rw [CochainComplex.prev]

theorem homology_chain (C : Chain.{u,v} R) (n : ℤ) :
    Homology C n = (LinearMap.ker (C.d n (n - 1)).hom ⧸
      (LinearMap.range (C.d (n + 1) n).hom).comap
        (LinearMap.ker (C.d n (n - 1)).hom).subtype) := by
  let F (out inc : ℤ) := (LinearMap.ker (C.d n out).hom ⧸
    (LinearMap.range (C.d inc n).hom).comap (LinearMap.ker (C.d n out).hom).subtype)
  change F _ _ = F _ _
  rw [ChainComplex.next, ChainComplex.prev]

theorem homology_cochain (C : Cochain.{u,v} R) (n : ℤ) :
    Homology C n = (LinearMap.ker (C.d n (n + 1)).hom ⧸
      (LinearMap.range (C.d (n - 1) n).hom).comap
        (LinearMap.ker (C.d n (n + 1)).hom).subtype) := by
  let F (out inc : ℤ) := (LinearMap.ker (C.d n out).hom ⧸
    (LinearMap.range (C.d inc n).hom).comap (LinearMap.ker (C.d n out).hom).subtype)
  change F _ _ = F _ _
  rw [CochainComplex.next, CochainComplex.prev]

variable {ι' : Type w'} {c' : ComplexShape ι'}

theorem supported_d_from (C : HomologicalComplex (ModuleCat.{v} R) c) (s : Set ι)
    (h : SupportedIn C s) (i j : ι) (hi : i ∉ s) : C.d i j = 0 := by
  let := h i hi
  apply ModuleCat.hom_ext
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

theorem supported_d_to (C : HomologicalComplex (ModuleCat.{v} R) c) (s : Set ι)
    (h : SupportedIn C s) (i j : ι) (hj : j ∉ s) : C.d i j = 0 := by
  let := h j hj
  apply ModuleCat.hom_ext
  ext x
  exact Subsingleton.elim _ _

theorem extendByZero_supported (C : HomologicalComplex (ModuleCat.{v} R) c)
    (e : c.Embedding c') : SupportedIn (extendByZero C e) (Set.range e.f) := by
  intro n hn
  apply ModuleCat.subsingleton_of_isZero
  exact C.isZero_extend_X e n (fun i hi => hn ⟨i, hi⟩)

/-- The extended differential agrees with the original after the canonical
identification of terms in the image of the embedding. -/
theorem extendByZero_d (C : HomologicalComplex (ModuleCat.{v} R) c)
    (e : c.Embedding c') (i j : ι) :
    (extendByZero C e).d (e.f i) (e.f j) =
      (C.extendXIso e rfl).hom ≫ C.d i j ≫ (C.extendXIso e rfl).inv := by
  exact C.extend_d_eq e rfl rfl

theorem extendNonnegativeChain_supported (C : ChainComplex (ModuleCat.{v} R) ℕ) :
    SupportedIn (extendNonnegativeChain C) (Set.Ici (0 : ℤ)) := by
  intro n hn
  apply extendByZero_supported C nonnegativeChainEmbedding n
  rintro ⟨i, rfl⟩
  exact hn (Int.natCast_nonneg i)

theorem extendNonnegativeCochain_supported (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    SupportedIn (extendNonnegativeCochain C) (Set.Ici (0 : ℤ)) := by
  intro n hn
  apply extendByZero_supported C ComplexShape.embeddingUpNat n
  rintro ⟨i, rfl⟩
  exact hn (Int.natCast_nonneg i)

end
end P103.Ch10.Complexes
