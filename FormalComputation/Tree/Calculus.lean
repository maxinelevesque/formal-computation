import FormalComputation.Calculus

/-!
# Tree calculus as a calculus with probes

Tree calculus in the five-rule triage presentation (treecalcul.us, as in the `tree-semantics`
repository):

    △ △ y z             →  y              (K)
    △ (△ x) y z         →  x z (y z)      (S)
    △ (△ w x) y △       →  w              (triage: leaf)
    △ (△ w x) y (△ u)   →  x u            (triage: stem)
    △ (△ w x) y (△ u v) →  y u v          (triage: fork)

Terms carry variables, as in the essay's SKI, so that probes can supply them and read them
back. The syntax, parallel reduction and its diamond property are ported from
`tree-semantics` (`TreeCalculus/Algebra.lean`, `Tm.Par`, `Tm.cd`, `Tm.par_cd`,
`Tm.par_diamond`), unchanged except for names and namespace.

Proved here:
- tree calculus with probes is a `Calculus`, and it is confluent (`calculus_confluent`), so every
  general result of `FormalComputation.Calculus` applies;
- **probes read code** (`probes_read_code`): `S K △` and `S K K` agree on every argument and lie
  in different fibres, but a probe tells them apart, by triage on their code. In SKI the
  corresponding terms agree under every probe (`SKI.probeEq_SK`).
-/

namespace FormalComputation.Tree

open Relation

universe u

/-- Terms of tree calculus, with variables. -/
inductive Tm (α : Type u) where
  | L : Tm α
  | V : α → Tm α
  | A : Tm α → Tm α → Tm α
  deriving DecidableEq

namespace Tm
scoped infixl:70 " ∙ " => Tm.A

variable {α : Type u}

/-- Parallel reduction: contract any set of redexes at once, including redexes
nested inside the retained arguments of a contracted redex. -/
inductive Par : Tm α → Tm α → Prop where
  | leaf : Par L L
  | var (n) : Par (V n) (V n)
  | app {f f' a a'} : Par f f' → Par a a' → Par (f ∙ a) (f' ∙ a')
  | k {y y'} (z) : Par y y' → Par (L ∙ L ∙ y ∙ z) y'
  | s {x x' y y' z z'} : Par x x' → Par y y' → Par z z' →
      Par (L ∙ (L ∙ x) ∙ y ∙ z) (x' ∙ z' ∙ (y' ∙ z'))
  | tl {w w'} (x y) : Par w w' → Par (L ∙ (L ∙ w ∙ x) ∙ y ∙ L) w'
  | ts {x x' u u'} (w y) : Par x x' → Par u u' →
      Par (L ∙ (L ∙ w ∙ x) ∙ y ∙ (L ∙ u)) (x' ∙ u')
  | tf {y y' u u' v v'} (w x) : Par y y' → Par u u' → Par v v' →
      Par (L ∙ (L ∙ w ∙ x) ∙ y ∙ (L ∙ u ∙ v)) (y' ∙ u' ∙ v')

theorem Par.refl : ∀ t : Tm α, Par t t
  | L => .leaf
  | V n => .var n
  | f ∙ a => .app (Par.refl f) (Par.refl a)

/-- Complete development: contract every redex present in the term. -/
def cd : Tm α → Tm α
  | L => L
  | V n => V n
  | L ∙ L ∙ y ∙ _ => cd y
  | L ∙ (L ∙ x) ∙ y ∙ z => cd x ∙ cd z ∙ (cd y ∙ cd z)
  | L ∙ (L ∙ w ∙ _) ∙ _ ∙ L => cd w
  | L ∙ (L ∙ _ ∙ x) ∙ _ ∙ (L ∙ u) => cd x ∙ cd u
  | L ∙ (L ∙ _ ∙ _) ∙ y ∙ (L ∙ u ∙ v) => cd y ∙ cd u ∙ cd v
  | f ∙ a => cd f ∙ cd a


/-! ### Inversion for the stuck shapes -/

theorem par_L {t : Tm α} (h : Par L t) : t = L := by cases h; rfl

theorem par_V {n : α} {t : Tm α} (h : Par (V n) t) : t = V n := by cases h; rfl

theorem par_L1 {a t : Tm α} (h : Par (L ∙ a) t) : ∃ a', t = L ∙ a' ∧ Par a a' := by
  cases h with
  | app hf ha => cases hf; exact ⟨_, rfl, ha⟩

theorem par_L2 {a b t : Tm α} (h : Par (L ∙ a ∙ b) t) :
    ∃ a' b', t = L ∙ a' ∙ b' ∧ Par a a' ∧ Par b b' := by
  cases h with
  | app hf hb =>
    obtain ⟨a', rfl, ha⟩ := par_L1 hf
    exact ⟨_, _, rfl, ha, hb⟩

/-- **Triangle property.** Every parallel reduct of `t` reduces in one
parallel step to the complete development `cd t`. -/
theorem par_cd : ∀ (t t' : Tm α), Par t t' → Par t' (cd t) := by
  intro t
  induction t using cd.induct with
  | case1 => intro t' h; cases h; exact Par.leaf
  | case2 n => intro t' h; cases h; exact Par.var n
  | case3 y a ih =>
    intro t' h
    rw [cd.eq_3]
    cases h with
    | app hf ha =>
      obtain ⟨p, y', rfl, hp, hy⟩ := par_L2 hf
      cases par_L hp
      exact Par.k _ (ih _ hy)
    | k _ hy => exact ih _ hy
  | case4 x y z ihx ihz ihy =>
    intro t' h
    rw [cd.eq_4]
    cases h with
    | app hf ha =>
      obtain ⟨p, y', rfl, hp, hy⟩ := par_L2 hf
      obtain ⟨x', rfl, hx⟩ := par_L1 hp
      exact Par.s (ihx _ hx) (ihy _ hy) (ihz _ ha)
    | s hx hy hz =>
      exact Par.app (Par.app (ihx _ hx) (ihz _ hz)) (Par.app (ihy _ hy) (ihz _ hz))
  | case5 w a a1 ihw =>
    intro t' h
    rw [cd.eq_5]
    cases h with
    | app hf ha =>
      cases par_L ha
      obtain ⟨p, y', rfl, hp, hy⟩ := par_L2 hf
      obtain ⟨w', x', rfl, hw, hx⟩ := par_L2 hp
      exact Par.tl _ _ (ihw _ hw)
    | tl _ _ hw => exact ihw _ hw
  | case6 a x a1 u ihx ihu =>
    intro t' h
    rw [cd.eq_6]
    cases h with
    | app hf ha =>
      obtain ⟨u', rfl, hu⟩ := par_L1 ha
      obtain ⟨p, y', rfl, hp, hy⟩ := par_L2 hf
      obtain ⟨w', x', rfl, hw, hx⟩ := par_L2 hp
      exact Par.ts _ _ (ihx _ hx) (ihu _ hu)
    | ts _ _ hx hu => exact Par.app (ihx _ hx) (ihu _ hu)
  | case7 a a1 y u v ihy ihu ihv =>
    intro t' h
    rw [cd.eq_7]
    cases h with
    | app hf ha =>
      obtain ⟨u', v', rfl, hu, hv⟩ := par_L2 ha
      obtain ⟨p, y', rfl, hp, hy⟩ := par_L2 hf
      obtain ⟨w', x', rfl, hw, hx⟩ := par_L2 hp
      exact Par.tf _ _ (ihy _ hy) (ihu _ hu) (ihv _ hv)
    | tf _ _ hy hu hv => exact Par.app (Par.app (ihy _ hy) (ihu _ hu)) (ihv _ hv)
  | case8 f a h1 h2 h3 h4 h5 ihf iha =>
    intro t' h
    rw [cd.eq_8 f a h1 h2 h3 h4 h5]
    cases h with
    | app hf ha => exact Par.app (ihf _ hf) (iha _ ha)
    | k _ _ => exact (h1 _ rfl).elim
    | s _ _ _ => exact (h2 _ _ rfl).elim
    | tl _ _ _ => exact (h3 _ _ _ rfl rfl).elim
    | ts _ _ _ _ => exact (h4 _ _ _ _ rfl rfl).elim
    | tf _ _ _ _ _ => exact (h5 _ _ _ _ _ rfl rfl).elim

/-- **Diamond property** of parallel reduction. -/
theorem par_diamond {t a b : Tm α} (ha : Par t a) (hb : Par t b) :
    ∃ c, Par a c ∧ Par b c :=
  ⟨cd t, par_cd t a ha, par_cd t b hb⟩


/-! ### One step, runs, confluence -/

/-- One step of running: a rule applied anywhere in the term. -/
inductive Step : Tm α → Tm α → Prop where
  | k (y z : Tm α) : Step (L ∙ L ∙ y ∙ z) y
  | s (x y z : Tm α) : Step (L ∙ (L ∙ x) ∙ y ∙ z) (x ∙ z ∙ (y ∙ z))
  | tl (w x y : Tm α) : Step (L ∙ (L ∙ w ∙ x) ∙ y ∙ L) w
  | ts (w x y u : Tm α) : Step (L ∙ (L ∙ w ∙ x) ∙ y ∙ (L ∙ u)) (x ∙ u)
  | tf (w x y u v : Tm α) : Step (L ∙ (L ∙ w ∙ x) ∙ y ∙ (L ∙ u ∙ v)) (y ∙ u ∙ v)
  | appL {f f' : Tm α} (a : Tm α) : Step f f' → Step (f ∙ a) (f' ∙ a)
  | appR (f : Tm α) {a a' : Tm α} : Step a a' → Step (f ∙ a) (f ∙ a')

/-- Running: any number of steps. -/
abbrev Reds : Tm α → Tm α → Prop := ReflTransGen Step

theorem reds_appL (a : Tm α) {f f' : Tm α} (h : Reds f f') : Reds (f ∙ a) (f' ∙ a) := by
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (.appL a s)

theorem reds_appR (f : Tm α) {a a' : Tm α} (h : Reds a a') : Reds (f ∙ a) (f ∙ a') := by
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (.appR f s)

theorem reds_app {f f' a a' : Tm α} (h₁ : Reds f f') (h₂ : Reds a a') :
    Reds (f ∙ a) (f' ∙ a') :=
  (reds_appL a h₁).trans (reds_appR f' h₂)

theorem par_of_step {t u : Tm α} (s : Step t u) : Par t u := by
  induction s with
  | k y z => exact .k z (Par.refl y)
  | s x y z => exact .s (Par.refl x) (Par.refl y) (Par.refl z)
  | tl w x y => exact .tl x y (Par.refl w)
  | ts w x y u => exact .ts w y (Par.refl x) (Par.refl u)
  | tf w x y u v => exact .tf w x (Par.refl y) (Par.refl u) (Par.refl v)
  | appL a _ ih => exact .app ih (Par.refl a)
  | appR f _ ih => exact .app (Par.refl f) ih

theorem reds_of_par {t u : Tm α} (h : Par t u) : Reds t u := by
  induction h with
  | leaf => exact .refl
  | var n => exact .refl
  | app _ _ ih₁ ih₂ => exact reds_app ih₁ ih₂
  | k z _ ih => exact (reds_appL z (reds_appR (L ∙ L) ih)).tail (Step.k _ z)
  | s _ _ _ ihx ihy ihz =>
    exact (reds_app (reds_app (reds_appR L (reds_appR L ihx)) ihy) ihz).tail (Step.s _ _ _)
  | tl x y _ ih =>
    exact (reds_appL L (reds_appL y (reds_appR L (reds_appL x (reds_appR L ih))))).tail
      (Step.tl _ _ _)
  | ts w y _ _ ihx ihu =>
    exact (reds_app (reds_appL y (reds_appR L (reds_appR (L ∙ w) ihx))) (reds_appR L ihu)).tail
      (Step.ts _ _ _ _)
  | tf w x _ _ _ ihy ihu ihv =>
    exact (reds_app (reds_app .refl ihy) (reds_app (reds_appR L ihu) ihv)).tail
      (Step.tf _ _ _ _ _)

theorem reds_of_parStar {t u : Tm α} (h : ReflTransGen Par t u) : Reds t u := by
  induction h with
  | refl => exact .refl
  | tail _ hp ih => exact ih.trans (reds_of_par hp)

/-- **Confluence.** Two runs from one term can be continued until they meet. -/
theorem confluent {a b c : Tm α} (hb : Reds a b) (hc : Reds a c) :
    ∃ d, Reds b d ∧ Reds c d := by
  have star : ∀ {x y : Tm α}, Reds x y → ReflTransGen Par x y := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (par_of_step hs)
  obtain ⟨d, h₁, h₂⟩ := church_rosser (fun a b c hab hac => by
    obtain ⟨d, e, f⟩ := par_diamond hab hac
    exact ⟨d, ReflGen.single e, ReflTransGen.single f⟩) (star hb) (star hc)
  exact ⟨d, reds_of_parStar h₁, reds_of_parStar h₂⟩

/-! ### Normal forms -/

/-- Whether the root of a term is a redex. -/
def isRedex : Tm α → Bool
  | L ∙ L ∙ _ ∙ _ => true
  | L ∙ (L ∙ _) ∙ _ ∙ _ => true
  | L ∙ (L ∙ _ ∙ _) ∙ _ ∙ L => true
  | L ∙ (L ∙ _ ∙ _) ∙ _ ∙ (L ∙ _) => true
  | L ∙ (L ∙ _ ∙ _) ∙ _ ∙ (L ∙ _ ∙ _) => true
  | _ => false

/-- Whether a term contains a redex. -/
def hasRedex : Tm α → Bool
  | f ∙ a => isRedex (f ∙ a) || hasRedex f || hasRedex a
  | _ => false

theorem hasRedex_of_step {t u : Tm α} (s : Step t u) : hasRedex t = true := by
  induction s with
  | k y z => simp [hasRedex, isRedex]
  | s x y z => simp [hasRedex, isRedex]
  | tl w x y => simp [hasRedex, isRedex]
  | ts w x y u => simp [hasRedex, isRedex]
  | tf w x y u v => simp [hasRedex, isRedex]
  | appL a _ ih => simp [hasRedex, ih]
  | appR f _ ih => simp [hasRedex, ih]

/-! ### Probes -/

/-- Terms written in variables alone: the outcomes a probe may read. -/
inductive InVars : Tm α → Prop
  | var (n : α) : InVars (V n)
  | app {t u : Tm α} : InVars t → InVars u → InVars (t ∙ u)

theorem InVars.left {f a : Tm α} (h : InVars (f ∙ a)) : InVars f := by
  cases h with
  | app h₁ _ => exact h₁

theorem InVars.right {f a : Tm α} (h : InVars (f ∙ a)) : InVars a := by
  cases h with
  | app _ h₂ => exact h₂

theorem not_inVars_L : ¬ InVars (L : Tm α) := fun h => by cases h

theorem not_inVars_of_step {t u : Tm α} (s : Step t u) : ¬ InVars t := by
  induction s with
  | k y z => exact fun h => not_inVars_L h.left.left.left
  | s x y z => exact fun h => not_inVars_L h.left.left.left
  | tl w x y => exact fun h => not_inVars_L h.left.left.left
  | ts w x y u => exact fun h => not_inVars_L h.left.left.left
  | tf w x y u v => exact fun h => not_inVars_L h.left.left.left
  | appL a _ ih => exact fun h => ih h.left
  | appR f _ ih => exact fun h => ih h.right

end Tm

open Tm

/-- A **probe**: a context with any number of holes. -/
inductive Probe (α : Type u) where
  | hole
  | lit (t : Tm α)
  | app (C D : Probe α)

variable {α : Type u}

/-- Put the term under test in every hole. -/
def Probe.plug : Probe α → Tm α → Tm α
  | .hole, t => t
  | .lit u, _ => u
  | .app C D, t => C.plug t ∙ D.plug t

/-- Put the probe `D` in every hole of `C`. -/
def Probe.subst : Probe α → Probe α → Probe α
  | .hole, D => D
  | .lit u, _ => .lit u
  | .app C₁ C₂, D => .app (C₁.subst D) (C₂.subst D)

theorem Probe.plug_subst (C D : Probe α) (t : Tm α) :
    (C.subst D).plug t = C.plug (D.plug t) := by
  induction C with
  | hole => rfl
  | lit u => rfl
  | app C₁ C₂ ih₁ ih₂ => simp only [Probe.subst, Probe.plug, ih₁, ih₂]

theorem reds_plug (C : Probe α) {t u : Tm α} (s : Step t u) : Reds (C.plug t) (C.plug u) := by
  induction C with
  | hole => exact .single s
  | lit v => exact .refl
  | app C D ih₁ ih₂ => exact reds_app ih₁ ih₂

/-- **Tree calculus with probes, as a calculus.** -/
def calculus : Calculus where
  Tm := Tm ℕ
  Step := Step
  Ctx := Probe ℕ
  hole := .hole
  plug := Probe.plug
  subst := Probe.subst
  plug_hole _ := rfl
  plug_subst := Probe.plug_subst
  reds_plug C _ _ s := reds_plug C s
  Out := InVars
  out_normal hr s := not_inVars_of_step s hr

/-- Tree calculus is confluent, as a calculus. -/
theorem calculus_confluent : calculus.Confluent := fun _ _ _ hb hc => confluent hb hc

theorem isNormal_of_hasRedex {t : Tm ℕ} (h : hasRedex t = false) : calculus.IsNormal t :=
  fun _ s => by simp [hasRedex_of_step s] at h

/-! ### Running concrete terms -/

/-- One step at the root, if the root is a redex. -/
def rootStep : (t : Tm α) → Option {u // Step t u}
  | L ∙ L ∙ y ∙ z => some ⟨y, .k y z⟩
  | L ∙ (L ∙ x) ∙ y ∙ z => some ⟨_, .s x y z⟩
  | L ∙ (L ∙ w ∙ x) ∙ y ∙ L => some ⟨w, .tl w x y⟩
  | L ∙ (L ∙ w ∙ x) ∙ y ∙ (L ∙ u) => some ⟨_, .ts w x y u⟩
  | L ∙ (L ∙ w ∙ x) ∙ y ∙ (L ∙ u ∙ v) => some ⟨_, .tf w x y u v⟩
  | _ => none

/-- One step, leftmost-outermost, with its proof. -/
def step : (t : Tm α) → Option {u // Step t u}
  | L => none
  | V _ => none
  | f ∙ a =>
    match rootStep (f ∙ a) with
    | some p => some p
    | none =>
      match step f with
      | some ⟨f', h⟩ => some ⟨f' ∙ a, .appL a h⟩
      | none =>
        match step a with
        | some ⟨a', h⟩ => some ⟨f ∙ a', .appR f h⟩
        | none => none

/-- At most `n` steps, with the run as proof. -/
def run : ℕ → (t : Tm α) → {u // Reds t u}
  | 0, t => ⟨t, .refl⟩
  | n + 1, t =>
    match step t with
    | some ⟨u, h⟩ => ⟨(run n u).1, ReflTransGen.head h (run n u).2⟩
    | none => ⟨t, .refl⟩

/-! ### Probes read code -/

/-- `K = △ △`. -/
def K : Tm ℕ := L ∙ L
/-- `S K △`: an identity. -/
def idT : Tm ℕ := L ∙ (L ∙ K) ∙ L
/-- `S K K`: another identity, with different code. -/
def idT' : Tm ℕ := L ∙ (L ∙ K) ∙ K
/-- `triage a b c` sends a leaf to `a`, a stem `△ u` to `b u`, and a fork `△ u v` to `c u v`. -/
def triage (a b c : Tm ℕ) : Tm ℕ := L ∙ (L ∙ a ∙ b) ∙ c

/-- The separating probe: take the right child of the code under test (`triage △ △ (K I)`),
then triage it, reading `x` from a leaf and `y` from a stem. -/
def sep : Probe ℕ :=
  .app (.lit (triage (V 0) (K ∙ V 1) L)) (.app (.lit (triage L L (K ∙ idT))) .hole)

theorem idT_apply (z : Tm ℕ) : Reds (idT ∙ z) z :=
  ReflTransGen.head (Step.s K L z) (ReflTransGen.single (Step.k z (L ∙ z)))

theorem idT'_apply (z : Tm ℕ) : Reds (idT' ∙ z) z :=
  ReflTransGen.head (Step.s K K z) (ReflTransGen.single (Step.k z (K ∙ z)))

theorem sep_idT : calculus.Reads (sep.plug idT) (V 0) := by
  have h := (run 10 (sep.plug idT)).2
  have e : (run 10 (sep.plug idT)).1 = V 0 := by decide
  exact ⟨e ▸ h, .var 0⟩

theorem sep_idT' : calculus.Reads (sep.plug idT') (V 1) := by
  have h := (run 10 (sep.plug idT')).2
  have e : (run 10 (sep.plug idT')).1 = V 1 := by decide
  exact ⟨e ▸ h, .var 1⟩

theorem isNormal_idT : calculus.IsNormal idT := isNormal_of_hasRedex rfl
theorem isNormal_idT' : calculus.IsNormal idT' := isNormal_of_hasRedex rfl

/-- **In tree calculus, probes read code.** `S K △` and `S K K` agree on every argument, and
they lie in different fibres. A probe tells them apart, by triage on their code. (In SKI, `S K y`
and `I` agree under every probe: `SKI.probeEq_SK`.) -/
theorem probes_read_code :
    (∀ z, calculus.Conv (idT ∙ z) (idT' ∙ z)) ∧ ¬ calculus.Conv idT idT' ∧
      ¬ calculus.ProbeEq idT idT' := by
  refine ⟨fun z => ?_, fun h => ?_, fun h => ?_⟩
  · exact EqvGen.trans _ _ _ (Calculus.reds_conv (L := calculus) (idT_apply z))
      (EqvGen.symm _ _ (Calculus.reds_conv (L := calculus) (idT'_apply z)))
  · exact absurd (Calculus.conv_normal_eq calculus_confluent h isNormal_idT isNormal_idT')
      (by decide)
  · have h' := (h sep (V 0)).1 sep_idT
    exact absurd (Calculus.reads_unique calculus_confluent h' sep_idT') (by decide)

end FormalComputation.Tree
