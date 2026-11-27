import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Cofibrations
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.Projective
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.CellCokernelsKFlat

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex

universe u v

namespace DerivedFormalization.Model.Complexes

variable {A : Type u} [Ring A]

private noncomputable def cokernelRetract {X Y U V : Cochains A} {f : X ⟶ Y} {g : U ⟶ V}
    (r : RetractArrow f g) : Retract (cokernel f) (cokernel g) where
  i := cokernel.map f g r.i.left r.i.right r.i_w.symm
  r := cokernel.map g f r.r.left r.r.right r.r_w.symm
  retract := by
    apply (cancel_epi (cokernel.π f)).mp
    simp

private theorem splitMonoOfRetract {X Y U V : ModuleCat.{u} A} {f : X ⟶ Y} {g : U ⟶ V}
    (r : RetractArrow f g) (hg : IsSplitMono g) : IsSplitMono f := by
  obtain ⟨⟨s⟩⟩ := hg
  exact ⟨⟨⟨r.i.right ≫ s.retraction ≫ r.r.left, by
    rw [← r.i_w_assoc, s.id_assoc, r.retract_left]⟩⟩⟩

private theorem kProjectiveOfRetract {P Q : Cochains A} (r : Retract P Q)
    (hQ : Q.IsKProjective) : P.IsKProjective := by
  constructor
  intro E g hE
  obtain ⟨H⟩ := hQ.nonempty_homotopy_zero (r.r ≫ g) hE
  exact ⟨by simpa using H.compLeft r.i⟩

private theorem descCokernelComponent {X Y : Cochains A} (f : X ⟶ Y) (n : ℤ)
    {M : ModuleCat.{u} A} (g : Y.X n ⟶ M) (hg : f.f n ≫ g = 0) :
    ∃ d : (cokernel f).X n ⟶ M, (cokernel.π f).f n ≫ d = g := by
  let F := eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n
  let d := CokernelCofork.IsColimit.desc' (isColimitOfHasCokernelOfPreservesColimit F f) g hg
  exact ⟨d.val, d.property⟩

private theorem liftKernelComponent {X Y : Cochains A} (q : X ⟶ Y) (n : ℤ)
    {M : ModuleCat.{u} A} (g : M ⟶ X.X n) (hg : g ≫ q.f n = 0) :
    ∃ l : M ⟶ (kernel q).X n, l ≫ (kernel.ι q).f n = g := by
  let F := eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n
  let l := KernelFork.IsLimit.lift' (isLimitOfHasKernelOfPreservesLimit F q) g hg
  exact ⟨l.val, l.property⟩

private theorem gradedLiftComponent {S T X Y : Cochains A}
    {f : S ⟶ T} {q : X ⟶ Y} {a : S ⟶ X} {b : T ⟶ Y}
    (sq : CommSq a f q b) (n : ℤ) (hs : IsSplitMono (f.f n))
    (hp : Projective ((cokernel f).X n)) (hq : Epi (q.f n)) :
    ∃ w : T.X n ⟶ X.X n, f.f n ≫ w = a.f n ∧ w ≫ q.f n = b.f n := by
  obtain ⟨⟨r⟩⟩ := hs
  have hw := congrArg (fun k : S ⟶ Y ↦ k.f n) sq.w
  change a.f n ≫ q.f n = f.f n ≫ b.f n at hw
  obtain ⟨b', hb'⟩ := descCokernelComponent f n (b.f n - r.retraction ≫ a.f n ≫ q.f n) (by
    rw [Preadditive.comp_sub, r.id_assoc, ← hw, sub_self])
  obtain ⟨l, hl⟩ := hp.factors b' (q.f n)
  have hπ : f.f n ≫ (cokernel.π f).f n = 0 := by
    simpa only [comp_f, zero_f] using congrArg (fun k : S ⟶ cokernel f ↦ k.f n)
      (cokernel.condition f)
  refine ⟨r.retraction ≫ a.f n + (cokernel.π f).f n ≫ l, ?_, ?_⟩
  · rw [Preadditive.comp_add, r.id_assoc, ← Category.assoc (f.f n), hπ, zero_comp, add_zero]
  · rw [Preadditive.add_comp, Category.assoc, Category.assoc, hl, hb', add_sub_cancel]

private theorem factorCochain {S T X Y : Cochains A}
    (f : S ⟶ T) (q : X ⟶ Y) {m : ℤ} (w : Cochain T X m)
    (hf : (Cochain.ofHom f).comp w (zero_add m) = 0)
    (hq : w.comp (Cochain.ofHom q) (add_zero m) = 0) :
    ∃ z : Cochain (cokernel f) (kernel q) m,
      ((Cochain.ofHom (cokernel.π f)).comp z (zero_add m)).comp
        (Cochain.ofHom (kernel.ι q)) (add_zero m) = w := by
  have h (i j : ℤ) (hij : i + m = j) :
      ∃ z : (cokernel f).X i ⟶ (kernel q).X j,
        (cokernel.π f).f i ≫ z ≫ (kernel.ι q).f j = w.v i j hij := by
    obtain ⟨d, hd⟩ := descCokernelComponent f i (w.v i j hij) (by
      simpa using Cochain.congr_v hf i j hij)
    obtain ⟨l, hl⟩ := liftKernelComponent q j d (by
      apply (cancel_epi ((cokernel.π f).f i)).mp
      rw [← Category.assoc, hd, comp_zero]
      simpa using Cochain.congr_v hq i j hij)
    exact ⟨l, by rw [hl, hd]⟩
  choose z hz using h
  refine ⟨Cochain.mk z, ?_⟩
  apply Cochain.ext
  intro i j hij
  simpa only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.mk_v, Category.assoc] using hz i j hij

private theorem boundaryOfExact {P K : Cochains A} (h : (CochainComplex.HomComplex P K).ExactAt 1)
    (z : Cochain P K 1) (hz : δ 1 2 z = 0) :
    ∃ t : Cochain P K 0, δ 0 1 t = z := by
  have h' := (exactAt_iff' (K := CochainComplex.HomComplex P K)
    (i := 0) (j := 1) (k := 2)
    ((ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk 0 1 rfl))
    ((ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk 1 2 rfl))).mp h
  exact ((ShortComplex.ab_exact_iff _).mp h') z hz

private theorem liftingOfCokernel {S T X Y : Cochains A} (f : S ⟶ T) (q : X ⟶ Y)
    (hs : ∀ n : ℤ, IsSplitMono (f.f n)) (hp : ∀ n : ℤ, Projective ((cokernel f).X n))
    (hq : degreewiseSurjective A q)
    (h : (CochainComplex.HomComplex (cokernel f) (kernel q)).ExactAt 1) :
    HasLiftingProperty f q := by
  constructor
  intro a b sq
  have lifts (n : ℤ) : ∃ w : T.X n ⟶ X.X n, f.f n ≫ w = a.f n ∧ w ≫ q.f n = b.f n :=
    gradedLiftComponent sq n (hs n) (hp n) ((ModuleCat.epi_iff_surjective _).2 (hq n))
  choose w hw using lifts
  let u : Cochain T X 0 := Cochain.ofHoms w
  have hu (n : ℤ) : u.v n n (add_zero n) = w n := Cochain.ofHoms_v w n
  have hu₁ : (Cochain.ofHom f).comp u (zero_add 0) = Cochain.ofHom a := by
    apply Cochain.ext₀
    intro i
    simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, hu] using (hw i).1
  have hu₂ : u.comp (Cochain.ofHom q) (add_zero 0) = Cochain.ofHom b := by
    apply Cochain.ext₀
    intro i
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, hu] using (hw i).2
  -- The differential of the graded lift vanishes on the source and lands in the kernel.
  obtain ⟨z, hz⟩ := factorCochain f q (δ 0 1 u)
    (by rw [← δ_ofHom_comp, hu₁, δ_ofHom])
    (by rw [← δ_comp_ofHom, hu₂, δ_ofHom])
  have hz' : δ 1 2 z = 0 := by
    have he := congrArg (δ 1 2) hz
    simp only [δ_comp_ofHom, δ_ofHom_comp, δ_δ] at he
    apply Cochain.ext
    intro i j hij
    have he' := Cochain.congr_v he i j hij
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      Cochain.zero_v, Category.assoc] at he' ⊢
    apply (cancel_mono ((kernel.ι q).f j)).mp
    apply (cancel_epi ((cokernel.π f).f i)).mp
    simpa only [Category.assoc, zero_comp, comp_zero] using he'
  obtain ⟨t, ht⟩ := boundaryOfExact h z hz'
  let c := ((Cochain.ofHom (cokernel.π f)).comp t (zero_add 0)).comp
    (Cochain.ofHom (kernel.ι q)) (add_zero 0)
  have hc : δ 0 1 c = δ 0 1 u := by
    simpa only [c, δ_comp_ofHom, δ_ofHom_comp, ht] using hz
  let l := (Cocycle.mk (u - c) 1 (zero_add 1) (by rw [δ_sub, hc, sub_self])).homOf
  refine ⟨⟨⟨l, ?_, ?_⟩⟩⟩
  · ext1 n
    change f.f n ≫ (u - c).v n n (add_zero n) = a.f n
    simp only [c, Cochain.sub_v, hu, Preadditive.comp_sub, Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, (hw n).1]
    have hπ : f.f n ≫ (cokernel.π f).f n = 0 := by
      simpa only [comp_f, zero_f] using congrArg (fun k : S ⟶ cokernel f ↦ k.f n)
        (cokernel.condition f)
    simp [← Category.assoc, hπ]
  · ext1 n
    change (u - c).v n n (add_zero n) ≫ q.f n = b.f n
    have hι : (kernel.ι q).f n ≫ q.f n = 0 := by
      simpa only [comp_f, zero_f] using congrArg (fun k : kernel q ⟶ Y ↦ k.f n)
        (kernel.condition q)
    simp [c, Cochain.sub_v, hu, Preadditive.sub_comp, Category.assoc, hι, (hw n).2]

/-- The projective cofibrations are the degreewise split monomorphisms whose cokernels
are termwise projective and have acyclic signed Hom into every acyclic complex. -/
theorem projectiveCofibrations_iff (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y) :
    projectiveCofibrations A f ↔
      (∀ n : ℤ, IsSplitMono (f.f n)) ∧
      (∀ n : ℤ, Projective ((cokernel f).X n)) ∧
      (∀ E : Cochains A, E.Acyclic → (CochainComplex.HomComplex (cokernel f) E).Acyclic) := by
  constructor
  · rw [← iCellRetracts_eq_projectiveCofibrations A]
    rintro ⟨U, V, g, r, hg⟩
    let s := cokernelRetract r
    refine ⟨fun n ↦ ?_, fun n ↦ ?_, ?_⟩
    · exact splitMonoOfRetract (r.map (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n))
        (iCell_degreewiseSplitMono A g hg n)
    · let F := eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n
      exact (s.map F).projective (p := iCellCokernel_degreewiseProjective A g hg n)
    · exact (isKProjective_iff_homComplex_acyclic A _).1
        (kProjectiveOfRetract s (iCellCokernel_isKProjective A g hg))
  · rintro ⟨hs, hp, h⟩ U V q hq
    have hK := (kernel_acyclic_iff_quasiIso q hq.1).2 hq.2
    exact liftingOfCokernel f q hs hp hq.1 (h (kernel q) hK 1)

/-- A projective cofibration has K-flat cokernel over the arbitrary coefficient ring. -/
theorem projectiveCofibrationCokernel_isKFlat (A : Type u) [Ring A]
    {X Y : Cochains A} (f : X ⟶ Y) (hf : projectiveCofibrations A f) :
    IsKFlat.{u,v} A (cokernel f) := by
  rw [← iCellRetracts_eq_projectiveCofibrations A] at hf
  obtain ⟨U, V, g, r, hg⟩ := hf
  exact isKFlat_of_retract A (cokernelRetract r) (iCellCokernel_isKFlat A g hg)

end DerivedFormalization.Model.Complexes
