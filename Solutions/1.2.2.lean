import Mathlib

/- 1.2.2 Mathematics and mathlib -/

/-
Up to now we have only done logic. It is time for some mathematics.
We are getting ahead of ourselves a bit: we will use the real numbers
ℝ (typed \R) and their properties as a black box, and we will only
understand how they are built in Lean (and how Lean knows that ℝ is
a field, an ordered set, and so on) on Day 2. Please accept this for
the moment.

All of this comes from mathlib, the mathematical library of Lean
[MIL, Chapter 1]. It is a huge library (more than 250000 theorems)
written by hundreds of mathematicians, and it covers most of the
undergraduate curriculum and quite a lot of research-level
mathematics. Everything is checked by Lean, and everything is unified
in a single library, so the definitions and theorems of different
areas work together.

The first thing you can do with mathlib is calculating by rewriting
using available theorems. Look at the following theorems in mathlib,
and also notices how binary operations associate in Lean:
-/

#check mul_comm    -- mul_comm (a b : G) : a * b = b * a
#check mul_assoc   -- mul_assoc (a b c : G) : a * b * c = a * (b * c)

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b, mul_assoc]

/-
Look at the infoview after each rewrite. In the second example we
did not specify the arguments of mul_assoc: rw rewrites the first
match it finds. Be careful, though: rw [mul_comm] could rewrite a
product that you did not intend to.
-/

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_assoc c b a, mul_comm c (b * a), mul_assoc]

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
    c = 2 * a * d := by
  rw [hyp, mul_comm d a, hyp', two_mul, add_mul]

/-
Proving these identities by hand is instructive, but quickly becomes
tedious. Luckily, mathlib has tactics that do it for us:
    - ring proves identities in commutative rings, such as ℝ, ℤ, or ℚ
      (and also in ℕ, which is a commutative semiring),
    - linarith proves linear (in)equalities that follow from the
      hypotheses in the context,
    - norm_num proves numerical facts, such as 2 + 2 = 4 or
      (17 : ℝ) / 3 < 6,
    - positivity proves goals of the form 0 < x or 0 ≤ x, where x
      is obviously positive (squares, exponentials, ...),
    - simp simplifies the target using a huge collection of lemmas
      tagged with @[simp]. It is very powerful, but you never know
      exactly what it did, so use it with care.
-/

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  ring

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

example (a b c : ℝ) (h₁ : a < b) (h₂ : b ≤ c) : a + 1 < c + 2 := by
  linarith

example : (2 : ℝ) ^ 10 = 1024 := by
  norm_num

/-
  Note the (2 : ℝ): without it, Lean would think that 2 ^ 10 = 1024 is
  a statement about natural numbers.

  In Lean, a natural number is not a real number: they are terms of
  different types. So, if n : ℕ and x : ℝ, then x + n should not even
  make sense. But on paper we write this kind of thing all the time,
  and Lean lets us do it too: it knows how to convert n into a real
  number, and it tries to do it automatically. This conversion is
  called a coercion, and it appears in the infoview as an arrow, ↑n.
  We can also ask for it explicitly, by writing (n : ℝ). Look at the
  infoview here:
-/

example (n : ℕ) (x : ℝ) : x + n = n + x := by
  ring

/-
  Most of the time you can ignore these arrows. But if a goal looks
  obvious and a tactic refuses to prove it, check whether there is an
  arrow in the way. We will explain coercions in detail in 2.1.4.
-/

/-
  Very often, these tactics need a little help. linarith only uses the
  hypotheses in the context, and it knows nothing about squares,
  absolute values, and so on. But we can give it additional facts in
  square brackets, as with rw: linarith [h₁, h₂] works as if h₁ and h₂
  were in the context. These facts can be any terms, e.g., theorems
  applied to some arguments, like sq_nonneg (a - b) : 0 ≤ (a - b) ^ 2:
-/

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  linarith [sq_nonneg (a - b)]

/-
This works in the same way for several other tactics. For instance,
simp [h₁, h₂] and norm_num [h₁, h₂] use h₁ and h₂ as additional
rewriting rules (they can be hypotheses, theorems, or even
definitions, which are then unfolded). Moreover:
    - simp only [h₁, h₂] uses only h₁ and h₂ (and some very basic
      facts), instead of the whole collection of @[simp] lemmas. This
      is more predictable, so it is preferred in mathlib.
    - simp at h simplifies the hypothesis h instead of the target,
      and simp at * simplifies everything. This also works for
      norm_num.
-/

example (a b : ℝ) (h : a = 2) (h' : b = a + 1) : b * 1 + 0 = 3 := by
  norm_num [h', h]

example (a : ℝ) (h : a * 1 + 0 = 5) : a = 5 := by
  simp at h
  exact h

example (a b : ℝ) : a ≤ a + b ^ 2 := by
  simp [sq_nonneg b]

example (a b c : ℝ) (h₁ : a = b + 1) (h₂ : b = 2 * c) (h₃ : c = 1) :
    a * 1 = 3 := by
  rw [h₂] at h₁
  rw [h₃] at h₁
  rw [h₁]
  norm_num

example (f : ℕ → ℕ) (hf : ∀ n, f n = n + 1) (k : ℕ) (h : f 2 = k) :
    k = 3 := by
  rw [hf 2] at h
  rw [← h]

/-
There is one more tactic that you should know about: grind. The
tactics above each do one specific kind of job, but grind combines
many of them. It assumes the negation of the target, and then it
derives consequences from everything in the context, splitting into
cases, using equalities and ∀ hypotheses, and doing algebra and linear
arithmetic, until it reaches a contradiction:
-/

example (f : ℝ → ℝ) (a b : ℝ) (h : a = b + 1) : f (a - 1) = f b := by
  grind

example (a b : ℝ) (h : a * b = 1) (h' : a = 2) : b = 1 / 2 := by
  grind

/-
Like linarith, it sometimes needs a little help, and we can give it
additional facts in square brackets. Without the hint, this one fails:
-/

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  grind [sq_nonneg (a - b)]

/-
grind is so powerful that it solves most of the exercises of this course. So
use it with care! If you close every exercise with grind, you will
learn nothing from them. Try
to solve the exercises with the other tactics first, and keep grind
for the routine goals, the ones you already know how to solve.
Remember that if a short, elegant, and legible proof is available, it
is always better and more efficient than a powerful black box like
grind.
-/

/-
Next, inequalities. a ≤ b is typed using \le.
Here are some theorems about them:
-/

#check le_refl         -- le_refl (a : α) : a ≤ a
#check le_trans        -- le_trans : a ≤ b → b ≤ c → a ≤ c
#check lt_of_le_of_lt  -- lt_of_le_of_lt : a ≤ b → b < c → a < c
#check add_le_add      -- add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d
#check Real.exp_le_exp -- Real.exp_le_exp : Real.exp x ≤ Real.exp y ↔ x ≤ y

example (a b c : ℝ) (h₀ : a ≤ b) (h₁ : b ≤ c) : a ≤ c := by
  apply le_trans h₀
  exact h₁

example (a b c : ℝ) (h₀ : a ≤ b) (h₁ : b ≤ c) : a ≤ c :=
  le_trans h₀ h₁

example (a b : ℝ) (h : a ≤ b) : Real.exp a ≤ Real.exp b := by
  rw [Real.exp_le_exp]
  exact h

/-
Note how we rewrote with an ↔: rw works with equivalences as well as
with equalities.

Mathlib names follow strict conventions, and once you know them you
can often guess the name of the theorem you need. Roughly, the name
describes the statement: mul_comm is about the commutativity of
multiplication, le_trans about the transitivity of ≤, and
lt_of_le_of_lt deduces a < from a ≤ and a <. The usual
abbreviations are add, mul, sub, neg, inv, div, le, lt, pos (0 < x),
nonneg (0 ≤ x), abs, sq (squares), and so on.

How do you find the theorems you need? There are several ways:
    - Use the tactics exact? and apply?, which search mathlib for a
      theorem that closes the goal, or that can be applied to it.
      They tell you in the infoview what they found (and you can
      click on the suggestion to insert it in the file).
    - Use the search engines: LeanSearch (https://leansearch.net) and
      Moogle (https://www.moogle.ai) understand natural language,
      while Loogle (https://loogle.lean-lang.org) searches by the
      shape of the statement, e.g., Real.exp, _ ≤ _.
    - Browse the documentation of mathlib,
      https://leanprover-community.github.io/mathlib4_docs/, or use
      Ctrl+click on a name to jump to its definition in the source.
    - Ask an AI.
-/

example (a b : ℝ) (h : a ≤ b) : a + 1 ≤ b + 1 := by
  exact?
