import Mathlib.Logic.Relation
import Mathlib.Tactic.Common

/-!
# A one-step diamond makes cost a property of the term

In interaction nets two different interactions never overlap, so they commute in one step
each (Lafont, *Interaction nets*, POPL 1990). In `tree-semantics` this is
`Ix.strong_confluence`, and its consequence `Steps.equal_lengths` says every run to a normal
form has the same length. This file proves that consequence for any one-step relation.

**Hypothesis** (`OneStepDiamond`): if a term steps to two *different* terms, each of them
steps, in exactly one step, to a common term. (Two steps to the same term are allowed, and
need nothing.)

Proved here:
- **Equal lengths** (`equal_lengths`): two runs from one term to normal forms have the same
  length, and end at the same normal form.
- **Each step costs exactly one** (`step_cost`): if `a` has a run of length `m` to a normal
  form, then every one-step reduct of `a` has a run of length `m - 1` to the same normal form.
- **No longer runs** (`length_le`): every run from `a`, normalizing or not, has length at most
  `m`, and can be finished to the normal form in exactly the remaining number of steps.

So the length of a run to the normal form depends on the term alone: cost belongs to the term.
-/

namespace FormalComputation.Diamond

variable {α : Type*} (Step : α → α → Prop)

/-- `RedN Step n a b`: a run of exactly `n` steps from `a` to `b`. -/
inductive RedN : ℕ → α → α → Prop
  | refl (a : α) : RedN 0 a a
  | head (n : ℕ) (a b c : α) : Step a b → RedN n b c → RedN (n + 1) a c

/-- A term that takes no step. -/
def Normal (a : α) : Prop := ∀ b, ¬ Step a b

/-- **The one-step diamond**: two different one-step reducts of a term each step, in exactly
one step, to a common term. -/
def OneStepDiamond : Prop :=
  ∀ ⦃a b c : α⦄, Step a b → Step a c → b ≠ c → ∃ d, Step b d ∧ Step c d

variable {Step}

/-- The induction behind all three results: for a term with a run of length `m` to a normal
form `n`, every one-step reduct has a run of length `m - 1` to `n`, and every run to a normal
form has length `m` and ends at `n`. -/
theorem diamond_key (hd : OneStepDiamond Step) (n : α) (hn : Normal Step n) :
    ∀ (m : ℕ) (a : α), RedN Step m a n →
      (∀ b, Step a b → ∃ m', m = m' + 1 ∧ RedN Step m' b n) ∧
      (∀ k n', RedN Step k a n' → Normal Step n' → k = m ∧ n' = n) := by
  intro m
  induction m with
  | zero =>
    intro a h
    have ha : a = n := by
      cases h
      rfl
    subst ha
    refine ⟨fun b hb => absurd hb (hn b), fun k n' h' _ => ?_⟩
    cases h' with
    | refl => exact ⟨rfl, rfl⟩
    | head k₀ a₀ b c₀ s _ => exact absurd s (hn b)
  | succ m ih =>
    intro a h
    obtain ⟨b₀, s₀, h₀⟩ : ∃ b₀, Step a b₀ ∧ RedN Step m b₀ n := by
      cases h with
      | head _ _ b₀ _ s₀ h₀ => exact ⟨b₀, s₀, h₀⟩
    have part₁ : ∀ b, Step a b → ∃ m', m + 1 = m' + 1 ∧ RedN Step m' b n := by
      intro b hb
      by_cases hbb : b₀ = b
      · subst hbb
        exact ⟨m, rfl, h₀⟩
      · obtain ⟨d, hd₀, hdb⟩ := hd s₀ hb hbb
        obtain ⟨m', hm', hdn⟩ := (ih b₀ h₀).1 d hd₀
        exact ⟨m' + 1, by omega, RedN.head _ _ _ _ hdb hdn⟩
    refine ⟨part₁, fun k n' h' hn' => ?_⟩
    cases h' with
    | refl => exact absurd s₀ (hn' b₀)
    | head k' _ c _ sc hc =>
      obtain ⟨m', hm, hcn⟩ := part₁ c sc
      have hm' : m' = m := by omega
      subst hm'
      obtain ⟨hk, he⟩ := (ih c hcn).2 k' n' hc hn'
      exact ⟨by omega, he⟩

/-- **Equal lengths.** Under the one-step diamond, any two runs from a term to normal forms
have the same length and end at the same normal form. -/
theorem equal_lengths (hd : OneStepDiamond Step) {a n n' : α} {m k : ℕ}
    (h : RedN Step m a n) (hn : Normal Step n) (h' : RedN Step k a n') (hn' : Normal Step n') :
    m = k ∧ n = n' := by
  obtain ⟨hk, he⟩ := (diamond_key hd n hn m a h).2 k n' h' hn'
  exact ⟨hk.symm, he.symm⟩

/-- **Each step costs exactly one.** Under the one-step diamond, if `a` runs to the normal form
`n` in `m` steps, every one-step reduct of `a` runs to `n` in `m - 1` steps. -/
theorem step_cost (hd : OneStepDiamond Step) {a b n : α} {m : ℕ} (h : RedN Step m a n)
    (hn : Normal Step n) (s : Step a b) : ∃ m', m = m' + 1 ∧ RedN Step m' b n :=
  (diamond_key hd n hn m a h).1 b s

/-- **No run is longer.** Under the one-step diamond, if `a` runs to the normal form `n` in `m`
steps, every run from `a` has at most `m` steps and can be finished to `n` in exactly the
remaining number of steps. In particular `a` has no infinite run. -/
theorem length_le (hd : OneStepDiamond Step) {n : α} (hn : Normal Step n) {k : ℕ} {a b : α}
    (h' : RedN Step k a b) : ∀ m, RedN Step m a n → k ≤ m ∧ RedN Step (m - k) b n := by
  induction h' with
  | refl a =>
    intro m h
    refine ⟨Nat.zero_le _, ?_⟩
    rw [Nat.sub_zero]
    exact h
  | head k a c b s _ ih =>
    intro m h
    obtain ⟨m', hm, hcn⟩ := step_cost hd h hn s
    obtain ⟨hle, hrest⟩ := ih m' hcn
    refine ⟨by omega, ?_⟩
    have e : m - (k + 1) = m' - k := by omega
    rw [e]
    exact hrest

end FormalComputation.Diamond
