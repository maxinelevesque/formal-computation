import FormalComputation.Observation

/-!
# Three classes of observers (`notes/12-observation.md` §12.2)

Observers are covariant families `B : A ⥤ Type v` over a category `A` of descriptions and
runs. Observing `t` with `B` means evaluating, `B t`. Two descriptions are **the same under a
class `𝒪` of observers** when there are bijections `B t ≃ B u`, one for each `B ∈ 𝒪`, natural
in `B` (`Sameness`, `ObsEq`). Unfolded, this is a natural isomorphism between evaluation at
`t` and evaluation at `u`, restricted to the full subcategory on `𝒪`.

Larger classes give finer sameness (`ObsEq.mono`), and sameness under a class of predicates
gives agreement on every verdict of the family pairing (`ObsEq.same`).

The essay's three equalities are three classes of observers. Proved here:
1. **All families see text** (`obsEq_univ_iff`): `t` and `u` are the same under all families
   exactly when `t ≅ u` in `A`. The proof is Yoneda: the corepresentable `Hom(t, -)` is an
   observer.
2. **Behaviours see running** (`obsEq_beh_iff`): for a localization `L : A ⥤ C` at the steps,
   `t` and `u` are the same under all behaviours exactly when `L t ≅ L u`. The direction
   "isomorphic in the localization ⇒ same under behaviours" (`obsEq_beh_of_iso`) holds for any
   localization functor. The converse (`iso_of_obsEq_beh`) needs the localization's hom-sets in
   the universe `v` of the families, so that its corepresentables are behaviours; the
   canonical construction `𝒜.steps.Localization` is not known to satisfy this in general, so
   it is a hypothesis.
3. **Invariant observers cannot tell a fibre apart** (`obsEq_of_zigzag`): if every observer
   in `𝒪` is a behaviour, terms joined by a zigzag of steps are the same under `𝒪`.
-/

universe v u u' v'

namespace FormalComputation.Obs

open CategoryTheory Opposite

variable {A : Type u} [Category.{v} A]

/-- **Sameness of `t` and `u` under a class `𝒪` of observers**: a bijection `B t ≃ B u` for
each observer `B ∈ 𝒪`, natural in the observer. -/
structure Sameness (𝒪 : Set (A ⥤ Type v)) (t u : A) where
  /-- The bijection for each observer. -/
  e : ∀ B ∈ 𝒪, B.obj t ≃ B.obj u
  /-- Naturality in the observer. -/
  nat : ∀ (B : A ⥤ Type v) (hB : B ∈ 𝒪) (B' : A ⥤ Type v) (hB' : B' ∈ 𝒪) (α : B ⟶ B')
    (x : B.obj t), α.app u (e B hB x) = e B' hB' (α.app t x)

/-- `t` and `u` are **the same under `𝒪`**. -/
def ObsEq (𝒪 : Set (A ⥤ Type v)) (t u : A) : Prop := Nonempty (Sameness 𝒪 t u)

namespace Sameness

variable {𝒪 : Set (A ⥤ Type v)} {t u r : A}

/-- Sameness is reflexive. -/
def refl (𝒪 : Set (A ⥤ Type v)) (t : A) : Sameness 𝒪 t t :=
  ⟨fun _ _ => Equiv.refl _, fun _ _ _ _ _ _ => rfl⟩

/-- Sameness is symmetric. -/
def symm (S : Sameness 𝒪 t u) : Sameness 𝒪 u t where
  e B hB := (S.e B hB).symm
  nat B hB B' hB' α y := by
    show α.app t ((S.e B hB).symm y) = (S.e B' hB').symm (α.app u y)
    apply (S.e B' hB').injective
    rw [Equiv.apply_symm_apply, ← S.nat B hB B' hB' α, Equiv.apply_symm_apply]

/-- Sameness is transitive. -/
def trans (S : Sameness 𝒪 t u) (S' : Sameness 𝒪 u r) : Sameness 𝒪 t r where
  e B hB := (S.e B hB).trans (S'.e B hB)
  nat B hB B' hB' α x := by
    show α.app r (S'.e B hB (S.e B hB x)) = S'.e B' hB' (S.e B' hB' (α.app t x))
    rw [S'.nat B hB B' hB' α, S.nat B hB B' hB' α]

/-- Fewer observers, coarser sameness. -/
def mono (S : Sameness 𝒪 t u) {𝒪' : Set (A ⥤ Type v)} (h : 𝒪' ⊆ 𝒪) : Sameness 𝒪' t u :=
  ⟨fun B hB => S.e B (h hB), fun B hB B' hB' α x => S.nat B (h hB) B' (h hB') α x⟩

/-- Isomorphic descriptions are the same under every class of observers. -/
def ofIso (𝒪 : Set (A ⥤ Type v)) (i : t ≅ u) : Sameness 𝒪 t u where
  e B _ := (B.mapIso i).toEquiv
  nat B _ B' _ α x := NatTrans.naturality_apply α i.hom x

/-- The Yoneda step. If the observer `Q ⋙ Hom(Q t, -)` is in `𝒪`, the bijection of every
observer of the form `Q ⋙ H` is the action of one map `Q t ⟶ Q u`. -/
theorem app_eq (S : Sameness 𝒪 t u) {C : Type u'} [Category.{v} C] (Q : A ⥤ C)
    (hF : Q ⋙ coyoneda.obj (op (Q.obj t)) ∈ 𝒪) (H : C ⥤ Type v) (hH : Q ⋙ H ∈ 𝒪)
    (h : H.obj (Q.obj t)) :
    S.e (Q ⋙ H) hH h = H.map (S.e _ hF (𝟙 (Q.obj t)) : Q.obj t ⟶ Q.obj u) h := by
  have h₁ := S.nat _ hF _ hH (Functor.whiskerLeft Q (coyonedaEquiv.symm h)) (𝟙 (Q.obj t))
  change H.map (S.e _ hF (𝟙 (Q.obj t)) : Q.obj t ⟶ Q.obj u) h =
    S.e (Q ⋙ H) hH (H.map (𝟙 (Q.obj t)) h) at h₁
  have h₂ : H.map (𝟙 (Q.obj t)) h = h := by simp
  rw [h₂] at h₁
  exact h₁.symm

/-- **Yoneda for observers.** If the corepresentables `Q ⋙ Hom(Q t, -)` and `Q ⋙ Hom(Q u, -)`
are observers, sameness under `𝒪` gives an isomorphism `Q t ≅ Q u`. -/
def iso (S : Sameness 𝒪 t u) {C : Type u'} [Category.{v} C] (Q : A ⥤ C)
    (ht : Q ⋙ coyoneda.obj (op (Q.obj t)) ∈ 𝒪) (hu : Q ⋙ coyoneda.obj (op (Q.obj u)) ∈ 𝒪) :
    Q.obj t ≅ Q.obj u where
  hom := S.e _ ht (𝟙 (Q.obj t))
  inv := S.symm.e _ hu (𝟙 (Q.obj u))
  hom_inv_id := by
    have h₁ := S.symm.app_eq Q hu (coyoneda.obj (op (Q.obj t))) ht (S.e _ ht (𝟙 (Q.obj t)))
    change (S.e _ ht).symm (S.e _ ht (𝟙 (Q.obj t))) =
      (S.e _ ht (𝟙 (Q.obj t)) : Q.obj t ⟶ Q.obj u) ≫
        (S.symm.e _ hu (𝟙 (Q.obj u)) : Q.obj u ⟶ Q.obj t) at h₁
    rw [Equiv.symm_apply_apply] at h₁
    exact h₁.symm
  inv_hom_id := by
    have h₁ := S.app_eq Q ht (coyoneda.obj (op (Q.obj u))) hu (S.symm.e _ hu (𝟙 (Q.obj u)))
    change S.e _ hu ((S.e _ hu).symm (𝟙 (Q.obj u))) =
      (S.symm.e _ hu (𝟙 (Q.obj u)) : Q.obj u ⟶ Q.obj t) ≫
        (S.e _ ht (𝟙 (Q.obj t)) : Q.obj t ⟶ Q.obj u) at h₁
    rw [Equiv.apply_symm_apply] at h₁
    exact h₁.symm

end Sameness

namespace ObsEq

variable {𝒪 : Set (A ⥤ Type v)} {t u r : A}

theorem refl (𝒪 : Set (A ⥤ Type v)) (t : A) : ObsEq 𝒪 t t := ⟨Sameness.refl 𝒪 t⟩

theorem symm (h : ObsEq 𝒪 t u) : ObsEq 𝒪 u t := let ⟨S⟩ := h; ⟨S.symm⟩

theorem trans (h : ObsEq 𝒪 t u) (h' : ObsEq 𝒪 u r) : ObsEq 𝒪 t r :=
  let ⟨S⟩ := h; let ⟨S'⟩ := h'; ⟨S.trans S'⟩

/-- **More observers, finer sameness.** -/
theorem mono (h : ObsEq 𝒪 t u) {𝒪' : Set (A ⥤ Type v)} (h' : 𝒪' ⊆ 𝒪) : ObsEq 𝒪' t u :=
  let ⟨S⟩ := h; ⟨S.mono h'⟩

/-- Sameness under `𝒪` implies agreement on every verdict of the family pairing (`B` accepts
`t` when `B t` is inhabited). -/
theorem same (h : ObsEq 𝒪 t u) : (familyPairing 𝒪).Same t u := by
  obtain ⟨S⟩ := h
  rintro ⟨B, hB⟩
  show Nonempty (B.obj t) ↔ Nonempty (B.obj u)
  exact ⟨Nonempty.map (S.e B hB), Nonempty.map (S.e B hB).symm⟩

end ObsEq

/-! ### 1. All families: sameness of text -/

/-- **All families see text.** `t` and `u` are the same under all families exactly when they
are isomorphic in `A`. -/
theorem obsEq_univ_iff {t u : A} :
    ObsEq (Set.univ : Set (A ⥤ Type v)) t u ↔ Nonempty (t ≅ u) :=
  ⟨fun ⟨S⟩ => ⟨S.iso (𝟭 A) (Set.mem_univ _) (Set.mem_univ _)⟩,
    fun ⟨i⟩ => ⟨Sameness.ofIso _ i⟩⟩

/-- The same for any class of observers that contains the corepresentables `Hom(t, -)`. -/
theorem obsEq_iff_of_corep {𝒪 : Set (A ⥤ Type v)} (h𝒪 : ∀ X : A, coyoneda.obj (op X) ∈ 𝒪)
    {t u : A} : ObsEq 𝒪 t u ↔ Nonempty (t ≅ u) := by
  constructor
  · rintro ⟨S⟩
    refine ⟨S.iso (𝟭 A) ?_ ?_⟩ <;>
      first
        | exact h𝒪 _
        | (rw [Functor.id_comp]; exact h𝒪 _)
  · rintro ⟨i⟩
    exact ⟨Sameness.ofIso _ i⟩

/-! ### 2. Behaviours: sameness after running -/

/-- The behaviours of the covariant presentation, as a class of observers. -/
def behSet (𝒜 : DynPresentation A) : Set (A ⥤ Type v) := {B | 𝒜.toCopresentation.Beh B}

theorem mem_behSet_iff {𝒜 : DynPresentation A} {B : A ⥤ Type v} :
    B ∈ behSet 𝒜 ↔ 𝒜.steps.IsInvertedBy B :=
  Iff.of_eq (congrFun (beh_eq_isInvertedBy_co 𝒜) B)

/-- Read through a localization at the steps, every corepresentable is a behaviour. -/
theorem corep_mem_behSet (𝒜 : DynPresentation A) {C : Type u'} [Category.{v} C] (L : A ⥤ C)
    [L.IsLocalization 𝒜.steps] (X : C) : L ⋙ coyoneda.obj (op X) ∈ behSet 𝒜 := by
  rw [mem_behSet_iff]
  intro a b s hs
  haveI : IsIso (L.map s) := Localization.inverts L 𝒜.steps s hs
  exact Functor.map_isIso (coyoneda.obj (op X)) (L.map s)

/-- **Same under behaviours ⇒ isomorphic in the localization**, for a localization whose
hom-sets lie in the universe of the families. -/
theorem iso_of_obsEq_beh (𝒜 : DynPresentation A) {C : Type u'} [Category.{v} C] (L : A ⥤ C)
    [L.IsLocalization 𝒜.steps] {t u : A} (h : ObsEq (behSet 𝒜) t u) :
    Nonempty (L.obj t ≅ L.obj u) :=
  let ⟨S⟩ := h
  ⟨S.iso L (corep_mem_behSet 𝒜 L _) (corep_mem_behSet 𝒜 L _)⟩

section Lift

variable (𝒜 : DynPresentation A) {D : Type u'} [Category.{v'} D] (L : A ⥤ D)
  [L.IsLocalization 𝒜.steps] {t u : A}

/-- The bijection `B t ≃ B u` that a behaviour `B` gives to an isomorphism `L t ≅ L u` in the
localization: lift `B` through `L` and apply the lift to the isomorphism. -/
noncomputable def liftedEquiv (B : A ⥤ Type v) (hB : 𝒜.steps.IsInvertedBy B)
    (φ : L.obj t ≅ L.obj u) : B.obj t ≃ B.obj u :=
  (((Localization.fac B hB L).app t).symm ≪≫ (Localization.lift B hB L).mapIso φ ≪≫
    (Localization.fac B hB L).app u).toEquiv

theorem liftedEquiv_apply (B : A ⥤ Type v) (hB : 𝒜.steps.IsInvertedBy B)
    (φ : L.obj t ≅ L.obj u) (x : B.obj t) :
    liftedEquiv 𝒜 L B hB φ x = (Localization.fac B hB L).hom.app u
      ((Localization.lift B hB L).map φ.hom ((Localization.fac B hB L).inv.app t x)) :=
  rfl

/-- The lifted bijections are natural in the behaviour. -/
theorem liftedEquiv_nat (B B' : A ⥤ Type v) (hB : 𝒜.steps.IsInvertedBy B)
    (hB' : 𝒜.steps.IsInvertedBy B') (α : B ⟶ B') (φ : L.obj t ≅ L.obj u) (x : B.obj t) :
    α.app u (liftedEquiv 𝒜 L B hB φ x) = liftedEquiv 𝒜 L B' hB' φ (α.app t x) := by
  obtain ⟨ᾱ, hα⟩ : ∃ ᾱ : Localization.lift B hB L ⟶ Localization.lift B' hB' L,
      ∀ (X : A) (z : (Localization.lift B hB L).obj (L.obj X)),
        ᾱ.app (L.obj X) z = (Localization.fac B' hB' L).inv.app X
          (α.app X ((Localization.fac B hB L).hom.app X z)) :=
    ⟨Localization.liftNatTrans L 𝒜.steps B B' _ _ α, fun X z =>
      types_congr_hom (Localization.liftNatTrans_app L 𝒜.steps B B' _ _ α X) z⟩
  have e₁ : (Localization.fac B' hB' L).inv.app t (α.app t x) =
      ᾱ.app (L.obj t) ((Localization.fac B hB L).inv.app t x) := by
    first
      | rw [hα, Iso.inv_hom_id_app_apply]
      | (rw [hα]; simp)
  have e₂ : ∀ w, α.app u ((Localization.fac B hB L).hom.app u w) =
      (Localization.fac B' hB' L).hom.app u (ᾱ.app (L.obj u) w) := by
    intro w
    first
      | rw [hα, Iso.inv_hom_id_app_apply]
      | (rw [hα]; simp)
  rw [liftedEquiv_apply, liftedEquiv_apply, e₁, ← NatTrans.naturality_apply ᾱ φ.hom, e₂]

/-- **Isomorphic in the localization ⇒ same under behaviours**, for any localization functor
at the steps. -/
theorem obsEq_beh_of_iso (φ : L.obj t ≅ L.obj u) : ObsEq (behSet 𝒜) t u :=
  ⟨{ e := fun B hB => liftedEquiv 𝒜 L B (mem_behSet_iff.1 hB) φ
     nat := fun B hB B' hB' α x =>
       liftedEquiv_nat 𝒜 L B B' (mem_behSet_iff.1 hB) (mem_behSet_iff.1 hB') α φ x }⟩

end Lift

/-- **Behaviours see running.** For a localization `L : A ⥤ C` at the steps whose hom-sets lie
in the universe of the families, `t` and `u` are the same under all behaviours exactly when
`L t ≅ L u`. -/
theorem obsEq_beh_iff (𝒜 : DynPresentation A) {C : Type u'} [Category.{v} C] (L : A ⥤ C)
    [L.IsLocalization 𝒜.steps] {t u : A} :
    ObsEq (behSet 𝒜) t u ↔ Nonempty (L.obj t ≅ L.obj u) :=
  ⟨iso_of_obsEq_beh 𝒜 L, fun ⟨φ⟩ => obsEq_beh_of_iso 𝒜 L φ⟩

/-- For the canonical localization `𝒜.steps.Localization`, the direction that holds without
a size hypothesis. -/
theorem obsEq_beh_of_iso_Q (𝒜 : DynPresentation A) {t u : A}
    (φ : 𝒜.steps.Q.obj t ≅ 𝒜.steps.Q.obj u) : ObsEq (behSet 𝒜) t u :=
  obsEq_beh_of_iso 𝒜 𝒜.steps.Q φ

/-! ### 3. Invariant observers: a fibre looks the same -/

/-- A step gives sameness under any class of behaviours. -/
noncomputable def Sameness.ofStep (𝒜 : DynPresentation A) {𝒪 : Set (A ⥤ Type v)}
    (hbeh : ∀ B ∈ 𝒪, 𝒜.toCopresentation.Beh B) {t t' : A} (s : t ⟶ t') (hs : 𝒜.steps s) :
    Sameness 𝒪 t t' where
  e B hB := Equiv.ofBijective (B.map s) ((beh_iff_map_bijective_co 𝒜 B).1 (hbeh B hB) s hs)
  nat _ _ _ _ α x := NatTrans.naturality_apply α s x

/-- **If every observer is a behaviour, terms joined by a zigzag of steps are the same under
the observers.** -/
theorem obsEq_of_zigzag (𝒜 : DynPresentation A) {𝒪 : Set (A ⥤ Type v)}
    (hbeh : ∀ B ∈ 𝒪, 𝒜.toCopresentation.Beh B) {t u : A}
    (h : Relation.EqvGen (fun a b => ∃ s : a ⟶ b, 𝒜.steps s) t u) : ObsEq 𝒪 t u := by
  induction h with
  | rel a b hs =>
    obtain ⟨s, hs⟩ := hs
    exact ⟨Sameness.ofStep 𝒜 hbeh s hs⟩
  | refl a => exact ObsEq.refl 𝒪 a
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end FormalComputation.Obs
