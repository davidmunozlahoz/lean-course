import Mathlib.Tactic

/- 1.2.1 Basic tactics -/

/-
In 1.1 we wrote proofs as terms: to prove p ∧ q → q ∧ p we wrote
the function fun h => ⟨h.2, h.1⟩ directly. This is fine for short
proofs, but it quickly becomes unreadable, and it is not how we
think about proofs. On paper, we say "assume p ∧ q; then we have p
and q; we have to prove q ∧ p, so it is enough to prove q and p..."
That is, we work backwards from what we have to prove, step by step.

Tactics allow us to do precisely this. A tactic is an instruction
that tells Lean how to make progress in the proof: "assume", "split
into two cases", "apply this theorem", and so on. Behind the scenes,
each tactic builds a piece of the proof term for us. We enter tactic
mode with the keyword by (don't worry about the meaning of the tactics
in the next example; we'll go through them one by one below):
-/

section

variable (p q r : Prop)

example : p ∧ q → q ∧ p := by
  intro h
  constructor
  · exact h.2
  · exact h.1

/-
Now the infoview becomes really important. Put your cursor at the end
of each line of the proof above and look at it. Before intro h you
will see

    p q r : Prop
    ⊢ p ∧ q → q ∧ p

This is the goal (or proof state). Above the turnstile ⊢ (typed \|-)
there is the context: the variables and hypotheses we have at our
disposal. Below it there is the target: what we have to prove. After
intro h, the goal becomes

    p q r : Prop
    h : p ∧ q
    ⊢ q ∧ p

and after constructor there are two goals, ⊢ q and ⊢ p, each with
its own context. When everything has been proven, the infoview
says "No goals", and the proof is done.
-/

/-
We are about to overview all the basic tactics of Lean. There is no
need to memorize all of them at once, since in practice most of our
proof terms will be written by AI. However, if one wants to become a
serious Leaner, and contribute to high quality projects like mathlib,
then it should be cristal clear that tactics are the "moves" in this "game
of math" that Lean creates, and that one has to know them by heart.
-/

/-
Let us start with implication. To prove
p → q, on paper we say "assume p", and in Lean we write intro hp: the
target becomes q, and the hypothesis hp : p appears in the context.
To introduce several hypotheses at once, write intro h₁ h₂ h₃.

When the target is exactly one of our hypotheses, or any term we can
build, exact closes the goal: exact hp works if hp : p and the target
is p. Finally, if h : p → q and the target is q, then apply h reduces
the target to p: "to prove q, it is enough to prove p".
-/

example : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

/-
Look at the infoview after each line. Note that the last two lines
could have been replaced by exact hpq hp: exact accepts any term,
exactly as in 1.1.

Remember that ¬p is p → False. So intro hp also works when the
target is ¬p (the new target is False), and if hnp : ¬p and the
target is False, then apply hnp reduces it to p.
-/

example : p → p := by
  intro hp
  exact hp

example : (p → q → r) → (q → p → r) := by
  intro hpqr hq hp
  exact hpqr hp hq

example : (p → p → q) → p → q := by
  sorry

example : (p → q) → ¬q → ¬p := by
  sorry

example : p → ¬¬p := by
  intro hp hnp
  exact hnp hp

/-
To prove p ∧ q, the tactic constructor
splits the goal into two: one with target p, and one with target q.
It works in the same way for p ↔ q, which is split into p → q and
q → p.

Now we have more than one goal, and the infoview shows all of them.
The tactics always act on the first one. The dot · (typed \.) focuses
on the first goal: the indented tactics after it must close that goal
completely, or Lean complains. This keeps proofs organized, so use it
whenever there is more than one goal.

To use h : p ∧ q, write obtain ⟨hp, hq⟩ := h: this replaces h by
hp : p and hq : q in the context. We can also use h.1 : p and h.2 : q.
The same works for h : p ↔ q, which gives us the two implications.
-/

example : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨hp, hq⟩ := h
  constructor
  · exact hq
  · exact hp

example : (p → q → r) → p ∧ q → r := by
  intro h hpq
  obtain ⟨hp, hq⟩ := hpq
  apply h
  · exact hp
  · exact hq

/-
Note, in the last example, that apply h produced two goals, since h
has two hypotheses before its conclusion r.
-/

example : p ∧ (q ∧ r) → (p ∧ q) ∧ r := by
  sorry

example : (p → q) → p ∧ r → q ∧ r := by
  sorry

example : (p → q → r) ↔ (p ∧ q → r) := by
  sorry

example : (p ↔ q) → (q ↔ r) → (p ↔ r) := by
  sorry

/-
To prove p ∨ q, we have to choose which one
we prove: left changes the target to p, and right changes it to q.
To use h : p ∨ q, we argue by cases: rcases h with hp | hq produces
two goals, one with hp : p in the context, and one with hq : q.
-/

example : p ∨ q → q ∨ p := by
  intro h
  rcases h with hp | hq
  · right
    exact hp
  · left
    exact hq

/-
The patterns of obtain and rcases can be combined and nested: ⟨_, _⟩
splits an ∧ (or an ↔), and _ | _ splits an ∨. For instance,
rcases h with ⟨hp, hq | hr⟩ takes apart h : p ∧ (q ∨ r) into two
cases, and rcases h with hp | hq | hr takes apart h : p ∨ (q ∨ r)
into three. In fact, obtain and rcases are the same tactic, written
in two different ways.
-/

example : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  rcases h with ⟨hp, hq | hr⟩
  · left
    constructor
    · exact hp
    · exact hq
  · right
    exact ⟨hp, hr⟩

/-
In the last line we used the anonymous constructor of 1.1, instead
of constructor. Feel free to mix the terms we learned before and
tactics in this way.
-/

example : (p → r) → (q → r) → p ∨ q → r := by
  sorry

example : p ∨ (q ∨ r) → (p ∨ q) ∨ r := by
  sorry

example : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := by
  sorry

example : (p ∨ q → r) ↔ (p → r) ∧ (q → r) := by
  sorry

/-
rintro. Very often we introduce a hypothesis and immediately take it
apart. rintro does both things at once: it is intro followed by
rcases, and it accepts the same patterns. For instance, the example
above can be shortened to:
-/

example : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  rintro ⟨hp, hq | hr⟩
  · left
    exact ⟨hp, hq⟩
  · right
    exact ⟨hp, hr⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  sorry

example : (p ∨ q) ∧ r → (p ∧ r) ∨ (q ∧ r) := by
  sorry

example : (p → q) ∧ (p → r) → p → q ∧ r := by
  sorry

/-
exfalso and contradiction. If the target is not False, but our
hypotheses are contradictory, exfalso changes the target to False
(this is the principle of explosion, False.elim, of 1.1). And when
the contradiction is obvious, for instance when we have hp : p and
hnp : ¬p, or h : False, in the context, contradiction closes the goal
directly.
-/

example : p → ¬p → q := by
  intro hp hnp
  exfalso
  exact hnp hp

example : p → ¬p → q := by
  intro hp hnp
  contradiction

example : False → p := by
  sorry

example : ¬(p ∧ ¬p) := by
  sorry

example : p ∨ q → ¬p → q := by
  sorry

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  sorry

/-
have. On paper, we often prove an intermediate fact before going on:
"we first show that q". In Lean, have hq : q := proof adds hq : q to
the context. The proof can be a term, or a tactic proof starting with
by, indented below.
-/

example : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  have hq : q := hpq hp
  have hr : r := by
    apply hqr
    exact hq
  exact hr

/-
We can also omit the name: have : q := proof adds the hypothesis to
the context with the name this, which we can use as any other name.
And if the statement can be deduced from the proof, we can omit it
too, and write simply have := proof.
-/

example : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  have : q := hpq hp
  exact hqr this

/-
There is only one this at a time: after a second nameless have, the
name this refers to the new hypothesis. The old one stays in the
context, but it appears as this✝ in the infoview, and we cannot refer
to it by that name. So this is fine for a fact that we use right
away, as above, but anything that we need later deserves a name.
-/

/-
use (and the quantifiers). Recall that ∀ is a (dependent) function,
so it works exactly like →: we prove ∀ x, P x with intro x, and use
h : ∀ x, P x with apply h, or exact h a. For the existential, we only
need one new tactic: to prove ∃ x, P x, use a provides the witness a,
and leaves us with the target P a. To use h : ∃ x, P x, we take it
apart with obtain ⟨x, hx⟩ := h (or rcases, or rintro), which gives us
the witness x and hx : P x.
-/

variable (α : Type) (P Q : α → Prop)

example (h : ∀ x, P x ∧ Q x) : ∀ x, P x := by
  intro x
  obtain ⟨hpx, hqx⟩ := h x
  exact hpx

example : (∃ x, P x ∧ Q x) → ∃ x, Q x := by
  rintro ⟨w, hpw, hqw⟩
  use w

/-
Note that the pattern ⟨w, hpw, hqw⟩ is short for ⟨w, ⟨hpw, hqw⟩⟩.
Also, use w tried to close the goal Q w by itself, and it succeeded,
since hqw is in the context.
-/

example : (∀ x, P x → Q x) → (∀ x, P x) → ∀ x, Q x := by
  intro hPQ hP x
  exact (hPQ x) (hP x)

example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).1
    · intro x
      exact (h x).2
  · intro h
    exact (fun x => ⟨h.1 x, h.2 x⟩)

/- Or, using more direct terms: -/
example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h
    exact ⟨fun x => (h x).1, fun x => (h x).2⟩
  · intro h
    exact (fun x => ⟨h.1 x, h.2 x⟩)

example : ∃ n : ℕ, n * n = 16 := by
  sorry

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

example : (¬∃ x, P x) ↔ ∀ x, ¬P x := by
  sorry

/-
by_contra and by_cases. Classical logic has its own tactics:
by_contra h assumes h : ¬p, where p is the target, and changes the
target to False. And by_cases h : p splits the proof into two cases:
one with h : p, and one with h : ¬p.
-/

example (h : ¬¬p) : p := by
  by_contra hnp
  exact h hnp

example : (p → q) → ¬p ∨ q := by
  intro h
  by_cases hp : p
  · right
    exact h hp
  · left
    exact hp

example : (¬q → ¬p) → (p → q) := by
  sorry

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  sorry

example : (¬∀ x, P x) → ∃ x, ¬P x := by
  sorry

/-
rfl and rw. Finally, equality. rfl proves a = a (up to computation,
as in 1.1). If h : a = b, then rw [h] rewrites the target, replacing
every a by b. To replace b by a instead, write rw [← h] (← is typed
\l). We can also rewrite a hypothesis h' with rw [h] at h'. After
rewriting, rw tries rfl, so it often closes the goal by itself if the
expression has been simplified sufficiently.
-/

example (a b c : α) (h₁ : a = b) (h₂ : c = b) : a = c := by
  rw [h₁, h₂]

example (a b : α) (h : a = b) (ha : P a) : P b := by
  rw [← h]
  exact ha

example (a b c : α) (h₁ : a = b) (h₂ : b = c) (ha : P a) : P c := by
  sorry

example (f : α → α) (hf : ∀ x, f x = x) (a b : α) (h : a = b) :
    f a = b := by
  sorry

example (f : α → α) (hf : ∀ x, f x = x) (a : α) (ha : P a) :
    P (f a) := by
  sorry

end
