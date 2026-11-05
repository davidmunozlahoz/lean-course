import Mathlib

/- 1.2.3 A first glimpse of real math -/

/-
We are now ready to do some actual, albeit basic, math. We are going
to work with limits of sequences. This example is from [MIL, 3.6]. A
sequence of real numbers is a function s : ℕ → ℝ, and we say that s
converges to a if
    for every ε > 0 there is some N such that, for every n ≥ N,
    |s n - a| < ε.
In Lean, this is literally the same:
-/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

#check ConvergesTo

/-
Here ∀ ε > 0, ... is short for ∀ ε, ε > 0 → ..., and the same holds
for ∀ n ≥ N. The absolute value |·| is typed \|. Since ConvergesTo
is just a definition, Lean unfolds it whenever needed, so we can
directly use intro, use, and so on. Let us prove that a constant
sequence converges:
-/

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ => a) a := by
  -- remember: ∀ ε > 0, ... is short for ∀ ε, ε > 0 → ...
  -- so we have to introduce two things: the ε and the fact that ε > 0
  intro ε εpos 
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  exact εpos

/-
Note that each line of this proof is a line of the proof that you
would write on paper: "let ε > 0; take N = 0; let n ≥ 0; then
|a - a| = |0| = 0 < ε." The difference is that Lean does not let us
skip any of them.

Now, the sum of two convergent sequences s and t with limits a and b. On paper: let
ε > 0. Since s converges to a, there is Ns such that
|s n - a| < ε / 2 for n ≥ Ns, and similarly there is Nt for t and b.
Take N = max Ns Nt. Then, for n ≥ N,
    |s n + t n - (a + b)| ≤ |s n - a| + |t n - b| < ε / 2 + ε / 2 = ε.
The Lean proof follows exactly the same lines:
-/

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
    (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n => s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- definitional simp; not needed, but it makes the goal more readable
  have ε2pos : 0 < ε / 2 := by linarith
  obtain ⟨Ns, hs⟩ := cs (ε / 2) ε2pos
  obtain ⟨Nt, ht⟩ := ct (ε / 2) ε2pos
  use max Ns Nt
  intro n hn
  have ngeNs : n ≥ Ns := le_of_max_le_left hn
  have ngeNt : n ≥ Nt := le_of_max_le_right hn
  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs n ngeNs) (ht n ngeNt)
    _ = ε := by ring

/-
Three new things here:
    - The arguments {s t} {a b} in curly braces are implicit when we use convergesTo_add, Lean figures them out
      from cs and ct.
    - calc allows us to write a chain of equalities and inequalities,
      exactly as on paper. Each step is _ rel term := proof, where _
      stands for the right-hand side of the previous step. Lean
      deduces the relation between the first and the last term.
    - Notice abs_add_le _ _: the underscore indicates Lean to infer
      what to use in _. It has to be used with care: it can be cleaner
      sometimes, but a lot of times it can also make the code more
      difficult to follow. Of course, it will also work if what goes
      in _ is clear and unambiguous.

Now some exercises for you to do:
-/

theorem convergesTo_neg {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ConvergesTo (fun n => -s n) (-a) := by
  sorry   -- Hint: abs_neg has type |-x| = |x|.

theorem convergesTo_sub {s t : ℕ → ℝ} {a b : ℝ}
    (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n => s n - t n) (a - b) := by
  sorry   -- Hint: use sub_eq_add_neg.

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
    (cs : ConvergesTo s a) : ConvergesTo (fun n => c * s n) (c * a) := by
  by_cases h : c = 0
  · sorry
  · have acpos : 0 < |c| := abs_pos.mpr h
    sorry -- Hint: field_simp may be useful

/-
And a harder one, the uniqueness of limits: if s converges
to a and to b, then a = b.
-/

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : ConvergesTo s a) (sb : ConvergesTo s b) : a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    sorry
  obtain ⟨Na, hNa⟩ := sa ε εpos
  obtain ⟨Nb, hNb⟩ := sb ε εpos
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    sorry
  have absb : |s N - b| < ε := by
    sorry
  have : |a - b| < |a - b| := by
    sorry
  exact lt_irrefl _ this

/-
    (*) Of course, mathlib already knows about limits, in a much more
    general form: Filter.Tendsto, which works for sequences,
    functions, limits at infinity, one-sided limits, and so on, in
    any topological space. We will meet it on Day 2. Our ConvergesTo
    s a is equivalent to Filter.Tendsto s Filter.atTop (nhds a), see
    Metric.tendsto_atTop.
-/
