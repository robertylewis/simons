import analysis.special_functions.trigonometric.arctan
import ring_theory.witt_vector.compare

noncomputable theory
local notation `ℤ/3ℤ` := zmod 3
open real
open_locale real

/-!

# Machine-Checked proofs in Lean

## Introduction 

I'm Rob Lewis. Just joined the Brown CS department this fall. 

My goal with this talk:
* Introduce you to the idea of proof assistants
* Show you (quickly!) what it's like to use a proof assistant
* Explain the structure and goals of Lean's library mathlib

## Following along

* Install Lean and its supporting tools:
  <https://leanprover-community.github.io/get_started.html>
* `leanproject get robertylewis/simons`
* Open the `simons` *directory* in VSCode (File -> Open Folder...)

## What is a proof assistant?

A proof assistant provides a language (or languages) to:
* define kinds of objects
* define particular objects
* state properties of those objects
* prove that these properties hold

It also provides a tool to mechanically check these proofs, 
down to logical axioms.
Ideally, we want all of this to be human-readable.
-/

#check ℕ
#check 0
#check ∀ n : ℕ, 0 ≤ n

lemma my_first_lemma : ∀ n : ℕ, 0 ≤ n :=
begin
  intro n,
  apply nat.zero_le,
end

/-!

Historically these tools have been applied with "objects" = "programs".
But nothing inherently computational about them.
Depending on our choice of languages, 
we can talk about totally abstract things.
-/

#check category_theory.category
#check differentiable
#check fderiv

/-!

### Why formalize mathematics?

* Verified proofs are very very likely to be correct
* Full specifications, no ambiguity
* Age of data: machine-readable proofs are machine-processable
* Applications in AI
* Applications in education
* It's incredibly addictive

Big leaf node projects may be exciting, 
but all of this requires *libraries*.


## A demo: complex numbers
-/

namespace demo

structure complex :=
(re : ℝ)
(im : ℝ)

def i : complex :=
{ re := 0, 
  im := 1 }

def add (c1 c2 : complex) : complex :=
{ re := c1.re + c2.re, 
  im := c1.im + c2.im }

def neg (c : complex) : complex :=
{ re := -c.re, 
  im := -c.im }

@[simp]
def mul (c1 c2 : complex) : complex :=
{ re := c1.re * c2.re - c1.im * c2.im, 
  im := c1.re * c2.im + c1.im * c2.re }

def inv (c : complex) : complex :=
let norm := (c.re^2 + c.im^2) in
{ re := c.re / norm, 
  im := - c.im / norm }

instance : field complex :=
{ add := add,
  mul := mul,
  zero := {re := 0, im := 0},
  one := {re := 1, im := 0},
  neg := neg,
  inv := inv,
  add_comm := sorry,
  add_assoc := sorry,
  zero_add := sorry,
  add_zero := sorry,
  add_left_neg := sorry,
  mul_assoc := sorry,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  mul_comm := sorry,
  exists_pair_ne := sorry,
  mul_inv_cancel := sorry,
  inv_zero := sorry }


/--
`to_polar c` returns a pair of real numbers `(angle, radius)`.
-/
def to_polar (c : complex) : ℝ × ℝ :=
(arctan (c.im / c.re), sqrt (c.re^2 + c.im^2))

def from_polar (angle radius : ℝ) : complex :=
{ re := radius * cos angle, 
  im := radius * sin angle }

example (angle radius : ℝ) :
  to_polar (from_polar angle radius) = (angle, radius) :=
begin 
  sorry
end 

end demo

/-!

## Lean and mathlib

The Lean proof asssistant is relatively new, 
relatively ergonomic,
and has a relatively large community of users interested in mathematics.

*mathlib* is the de facto standard library for Lean.

* <https://leanprover-community.github.io/> 
* <https://github.com/leanprover-community/mathlib>
* <https://leanprover.zulipchat.com/>
* 700k lines of code, nearly 200 contributors
* Collaborative open-source project
* Lots of effort to make mathlib developments coherent, reusable

Overview of the library:
<https://leanprover-community.github.io/mathlib-overview.html>

Undergraduate math in mathlib:
<https://leanprover-community.github.io/undergrad.html>

People involved at all levels of mathematical maturity!
Formalization is a great way to get undergraduates involved. 

### Noteworthy projects

A number of projects, some ongoing, have added to or built on the library.

#### Liquid tensor experiment

Peter Scholze, Dec 5, 2020:
    I want to propose a challenge: 
    Formalize the proof of the following theorem.
    
    **Theorem 1.1** (Clausen-Scholze).
    Let 0 < p' < p ≤ 1 be real numbers, 
    let S be a profinite set, 
    and let V be a p-Banach space.
    Let ℳₚ'(S) be the space of p'-measures on S. 
    
    Then Extⁱ_Cond(Ab)(ℳₚ'(S), V) = 0 for i ≥ 1.
    ...
    I think this may be my most important theorem to date.... 
    Better be sure it’s correct.

Peter Scholze, June 5, 2021:
    Exactly half a year ago I wrote the Liquid Tensor 
    Experiment blog post...
    I am excited to announce that the Experiment has verified 
    the entire part of the argument that I was unsure about. 
    I find it absolutely insane that interactive proof assistants 
    are now at the level that 
    within a very reasonable time span 
    they can formally verify difficult original research.

A collaborative effort led by Johan Commelin.
-/


/-! 
#### Formalizing perfectoid spaces 

A challenge in formalizing a very complex *definition*.  

Kevin Buzzard, Johan Commelin, Patrick Massot (2020). 


#### Formalizing the solution to the cap set problem 

A *cap set* is a subset of ℤ₃ⁿ containing no arithmetic progression. 

Theorem (Ellenberg and Gijswijt, 2017): 
The largest possible size of a cap set is O(2.756^n).

Sander Dahmen, Johannes Hölzl, Robert Y. Lewis (2019): 
-/
theorem cap_set_problem : ∃ B : ℝ,
  ∀ {n : ℕ} {A : finset (fin n → ℤ/3ℤ)},
    (∀ x y z : fin n → ℤ/3ℤ, 
      x ∈ A → y ∈ A → z ∈ A → x + y + z = 0 → x = y ∧ x = z) →
    ↑A.card ≤ 
      B * ((((3 : ℝ) / 8)^3 * (207 + 33*real.sqrt 33))^(1/3 : ℝ))^n :=
sorry

/-! 
#### Formalizing the ring of Witt vectors 

Johan Commelin and Robert Y. Lewis (2021). 

Abstract strategies for verifying Witt vector identities 
are very hard to formalize. 
With the right abstractions and some metaprogramming, 
formal arguments can follow the same path as informal arguments.
-/

#check witt_vector 
#check witt_vector.equiv 


/-!

### Current status 

Plenty of ongoing projects:
* LTE 
* Sphere eversion 
* Transition from Lean 3 to Lean 4
* 8- and 24-dim sphere packings? 

CMU recently received a $20m donation to found 
the Hoskinson Center for Formal Mathematics. 

Various events planned in the medium-term future:
* Lorentz Center in Leiden, March 2022 (ask me for details!)
* ICERM, summer 2022
* Lean Together 2022, ???


## Resources and references

Learning: <https://leanprover-community.github.io/learn.html> 
* Tutorials project: <https://github.com/leanprover-community/tutorials> 
* Lean for the Curious Mathematician: <https://leanprover-community.github.io/lftcm2020/>
* Theorem Proving in Lean: <https://leanprover.github.io/theorem_proving_in_lean/> 

Papers: <https://leanprover-community.github.io/papers.html>

* de Moura, Kong, Avigad, van Doorn, von Raumer (2015). 
  *The Lean Theorem Prover (System Description)*. 
  <https://doi.org/10.1007/978-3-319-21401-6_26> 

* The mathlib Community (2020). *The Lean mathematical library*.
  <https://doi.org/10.1145/3372885.3373824> 

* Lewis (2019). *A formal proof of Hensel's Lemma over the p-adic integers*. 
  <https://doi.org/10.1145/3293880.3294089> 

* Dahmen, Hölzl, Lewis (2019). *Formalizing the solution to the cap set problem*. 
  <https://doi.org/10.4230/LIPIcs.ITP.2019.15>

* Buzzard, Commelin, Massot (2020). *Formalising perfectoid spaces*.
  <https://doi.org/10.1145/3372885.3373830> 

* Commelin, Lewis (2021). *Formalizing the ring of Witt vectors*. 
  <https://doi.org/10.1145/3437992.3439919> 


-/