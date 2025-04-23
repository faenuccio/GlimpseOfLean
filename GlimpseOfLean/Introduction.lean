import GlimpseOfLean.Library.Basic

namespace Introduction

/-
# Introduction to this tutorial

Your version contains more comments: I will discuss them rather than reading them...

Any text between `/-` and `-/` or after a `--` is a comment for you
that is ignored by Lean. -/


/-- A sequence `u` of real numbers converges to `l` if `∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| ≤ ε`.
This condition will be spelled `seq_limit u l`. -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/- ## Some differences
* `u n`
* `l : ℝ` instead of `l ∈ ℝ`.
* `f x` _(below)_
* `→` instead of `=>` _(below)_
-/

/-- A function `f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε`. -/
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

/-- Now we claim that if `f` is continuous at `x₀` then it is sequentially continuous
at `x₀`: for any sequence `u` converging to `x₀`, the sequence `f ∘ u` converges
to `f x₀`.  -/
theorem seq_limit_comp_continuous (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀)
 (hf : continuous_at f x₀) : seq_limit (f ∘ u) (f x₀) := by
  -- What do we want to prove?
  unfold seq_limit
  -- What do we know, actually?
  unfold continuous_at at hf
  -- Let's fix a positive `ε`
  intro ε hε
  -- Apply `hf` to it
  obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε
  -- Apply `hu` to this (positive) `δ`
  obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos
  -- That's the right `N`!
  use N
  -- OK, let's fix `n` larger than `N`.
  intro n hn
  -- Thanks to `Hf`, it will suffice to prove that `|u_n - x₀| ≤ δ`.
  apply Hf
  -- This follows from property `Hu` and our assumption on `n`.
  apply Hu n hn
  -- This finishes the proof!


/-
Now that this proof is over, you can choose between the short track or the longer one.
If you want to do the short track on the lean4web server you should go to
https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2FShorter.lean.

If you follow the longer track using a local installation or GitPod or Codespaces,
you should use the file explorer to the left of this panel to open the file
`Exercises > 01Rewriting.lean`.
-/
