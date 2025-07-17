/-
Copyright (c) 2025. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
-/

-- Import classical logic for Rasiowa's reasoning in proposition (6)
open Classical

/-!
# Chapter I: The Algebra of Sets
## Section 1. The concept of set

This file formalizes the basic concepts from Chapter I, Section 1 of Rasiowa's textbook.

### Structure:
1. **Basic Definitions** - Sets as predicates, membership, empty set, singleton
2. **Fundamental Relations** - Equations (5)-(7) from textbook
   - 2.1 Subset Relation - Equation (5)
   - 2.2 Negated Subset Relation - Equation (6)
   - 2.3 Set Equality - Proposition (7)
3. **Concrete Examples** - Demonstrations with specific sets
4. **Basic Properties** - Propositions 1.1 (8)-(12) from textbook
   - 4.1 Empty Set Property - Proposition 1.1 (8)
   - 4.2 Reflexivity Property - Proposition 1.1 (9)
   - 4.3 Transitivity Property - Proposition 1.1 (10)
   - 4.4 Mutual Subset Equality - Proposition 1.1 (11)
   - 4.5 Inequality Disjunction - Proposition 1.1 (12)

This formalization uses only pure Lean 4 without external dependencies for educational purposes.

## References
* Helena Rasiowa, "Introduction to Modern Mathematics", Chapter I, Section 1
-/

-- Universe declaration: declares u as a universe level variable
-- Universe levels avoid Russell's paradox by creating a hierarchy of types
-- Type u lives in universe level u, Type (u+1) contains Type u, etc.
universe u

-- Variable declaration: α is an implicit parameter of type Type u
-- {α : Type u} means α is implicit - Lean infers it from context
-- Type u is the type of all types at universe level u
variable {α : Type u}

-- Namespace declaration: groups related definitions under "Rasiowa"
-- Everything defined here can be accessed as Rasiowa.definition_name
-- Inside the namespace, you can use short names directly
namespace Rasiowa

/-! ## 1. Basic Definitions

This section introduces the fundamental concept of sets as predicates and basic operations.
-/

-- When working through Rasiowa's textbook, something unexpected emerged: Lean
-- isn't built on the same set-theoretic foundations that she teaches. Instead,
-- it uses dependent type theory where sets are encoded as predicates (functions
-- that return propositions).
--
-- But Rasiowa herself connects sets to properties in Section 5: "the concept of
-- subset is often identified with that of the property which is an attribute of
-- every element of that subset." This provides the bridge between classical
-- set theory and our predicate encoding.
--
-- In Lean's encoding: Set α := α → Prop
-- - A set becomes a function from elements to propositions
-- - For element x and set A, "x ∈ A" becomes "A x" (x has property A)
-- - The empty set becomes the property that's never satisfied
-- - Membership becomes function application
--
-- Syntax: def name (parameters) : return_type := definition
-- We declare our own RasiowaSet type (though Lean has a built-in Set)
-- so we can build on top of it and make the encoding explicit
def RasiowaSet (α : Type u) : Type u := α → Prop

-- Rasiowa's formula (1): "The statement that an element a belongs to a set A
-- is written: a ∈ A"
--
-- In our predicate encoding, membership becomes function application:
-- When we write a ∈ A, it unfolds to A a - the proposition that
-- "a has property A" or "a satisfies the condition A"
--
-- BREAKDOWN OF mem FUNCTION IMPLEMENTATION:
-- def mem (a : α) (A : RasiowaSet α) : Prop := A a
-- |   |    |   |   |           |       |     |  |
-- |   |    |   |   |           |       |     |  └─ Function body: apply A to a
-- |   |    |   |   |           |       |     └─ Assignment operator
-- |   |    |   |   |           |       └─ Return type: Prop (true/false)
-- |   |    |   |   |           └─ Type annotation
-- |   |    |   |   └─ Parameter: A is a set (predicate α → Prop)
-- |   |    |   └─ Parameter type: α (element type)
-- |   |    └─ Parameter: a is an element we're testing
-- |   └─ Function name
-- └─ Definition keyword
--
-- One insight: A a means "apply predicate A to element a"
-- Since A : α → Prop, and a : α, then A a : Prop
-- So mem returns a proposition type (not a computed boolean)
-- The proposition may or may not have inhabitants (proofs)
--
-- STEP-BY-STEP UNFOLDING OF mem (TYPE SYSTEM, NOT RUNTIME):
-- This shows how definitions unfold in this type system:
--
-- Example: Consider mem 2 setA where setA = {1, 2}
-- Step 1: Substitute definition of mem
--   mem 2 setA : Prop
--   = setA 2 : Prop  [by definition of mem]
--
-- Step 2: Substitute definition of setA
--   setA 2 : Prop
--   = (fun x => x = 1 ∨ x = 2) 2 : Prop  [setA is a predicate]
--
-- Step 3: Beta reduction (substitute x with 2)
--   (fun x => x = 1 ∨ x = 2) 2 : Prop
--   = (2 = 1 ∨ 2 = 2) : Prop  [parameter substitution]
--
-- Result: mem 2 setA = (2 = 1 ∨ 2 = 2) : Prop
-- This creates a proposition type that can be proven true.
-- A proof might be: by right; rfl (proving the right disjunct 2 = 2)
--
-- Walking through how this works step by step (matching the blog explanation):
-- 
-- For setA = fun x => x = 1 ∨ x = 2 (representing {1,2}):
-- Step 1: 2 ∈ setA becomes mem 2 setA
-- Step 2: By definition of mem: setA 2  
-- Step 3: By definition of setA: (fun x => x = 1 ∨ x = 2) 2
-- Step 4: Beta reduction: 2 = 1 ∨ 2 = 2
-- Step 5: This is provable using the right disjunct: 2 = 2
--
-- This demonstrates how Rasiowa's sets and Lean's predicate functions
-- represent the same mathematical concept through different foundations
def mem (a : α) (A : RasiowaSet α) : Prop := A a

-- Notation for membership - creates custom infix operator
-- infixr:50 means right-associative with precedence 50
-- Precedence 50: higher numbers bind tighter (like * vs +)
-- Standard precedences: → is 25, ∨ is 30, ∧ is 35, = is 50
--
-- Notation vs Implementation distinction:
--
-- NOTATION (syntactic sugar):
-- - infixr creates a syntactic rule: "∈" becomes infix operator
-- - This relates to parsing: how to read the symbols
-- - It tells Lean: "when you see a ∈ A, treat ∈ as infix operator"
-- - Pure syntactic sugar - makes code look like mathematics
--
-- IMPLEMENTATION (what the sugar expands to):
-- - "=> mem" gives computational meaning to the notation
-- - This provides the computational meaning behind the notation
-- - When you write a ∈ A, this translates to mem a A behind the scenes
-- - The syntactic sugar dissolves to reveal the real function call
-- - Similar to how 2 + 3 gets translated to Add.add 2 3 in programming
--
-- Together: infixr:50 " ∈ " => mem means:
-- 1. Parse "∈" as right-associative infix with precedence 50 (syntactic sugar)
-- 2. Expand the sugar to call mem function (implementation)
--
-- Corresponds to equation (1): a ∈ A
infixr:50 " ∈ " => mem

-- Examples from the textbook:
-- "the set of all books in a given library"
-- "the set of all letters of the Greek alphabet"
-- "the set of all integers"

-- Rasiowa: "It is convenient to introduce the concept of empty set, i.e.,
-- the set which has no elements."
--
-- In our predicate encoding: the empty set is the condition that's never
-- satisfied. For any element a, a ∈ ∅ becomes False.
def empty : RasiowaSet α := fun _ => False

-- Notation for empty set:
-- Different from infix notation - this is nullary (zero arguments)
-- NOTATION (syntactic sugar): "∅" becomes a standalone symbol (not infix)
-- IMPLEMENTATION (what the sugar expands to): calls empty function
-- When you write ∅, this translates to empty behind the scenes
-- No arguments needed: ∅ → empty (contrast with a ∈ A → mem a A)
notation "∅" => empty

-- Set membership example
-- "element a belongs to a set A" written as a ∈ A
-- example declares a statement without proof (for illustration)
--
-- SYNTAX BREAKDOWN OF example DECLARATION:
-- example (A : RasiowaSet α) (a : α) : Prop := a ∈ A
-- |        |   |           |   | |     |    |  | | |
-- |        |   |           |   | |     |    |  | | └─ Body: actual proposition
-- |        |   |           |   | |     |    |  | └─ Set membership operator
-- |        |   |           |   | |     |    |  └─ Element a
-- |        |   |           |   | |     |    └─ Assignment operator
-- |        |   |           |   | |     └─ Return type: Prop
-- |        |   |           |   | └─ Type of parameter a
-- |        |   |           |   └─ Parameter a
-- |        |   |           └─ Set type α
-- |        |   └─ Parameter A (a set)
-- |        └─ Parameter list
-- └─ example keyword
--
-- What this means:
-- - "For any set A and any element a, the statement 'a ∈ A' is a proposition"
-- - We're not proving it's true or false, just showing it's a valid statement
-- - Like saying "x > 5" is a proposition - could be true or false depending on x
-- - The := shows what the proposition actually is (not a proof, just the statement)
--
-- Mathematical meaning:
-- "For any set A and element a, the statement 'a ∈ A' is a proposition"
example (A : RasiowaSet α) (a : α) : Prop := a ∈ A

-- Negation of membership: a ∉ A
-- "if a does not belong to a set A"
-- ¬ is logical negation (not)
-- Corresponds to equation (2) in textbook: a ∉ A lub ∼(a ∈ A)
def not_mem (a : α) (A : RasiowaSet α) : Prop := ¬(a ∈ A)

-- Notation for non-membership - same precedence as ∈ for consistency
--
-- Implementation relationship:
-- - not_mem is the definition (the actual logical operation)
-- - ∉ is the implementation (the mathematical notation we want to use)
--
-- Layered expansion:
-- a ∉ A                    ← Mathematical notation (what you write)
--   ↓
-- not_mem a A             ← Definition layer
--   ↓
-- ¬(mem a A)              ← Expanded definition
--   ↓
-- ¬(A a)                  ← Core logic (what computer executes)
--
-- Corresponds to equation (2): a ∉ A
infixr:50 " ∉ " => not_mem

-- Rasiowa's formula (4): "A set whose only element is a will be denoted by {a}"
--
-- In predicate encoding: singleton a is the property "equals a"
def singleton (a : α) : RasiowaSet α := fun x => x = a

/-! ## 2. Fundamental Relations

This section formalizes equations (5)-(7) from Rasiowa's textbook, establishing the
core relationships between sets: subset, negated subset, and equality.
-/

/-! ### 2.1 Subset Relation - Equation (5) -/

-- Basic subset relation ⊆
-- Rasiowa defines "A is a subset of B" as A ⊆ B
-- This corresponds to: ∀ x, x ∈ A → x ∈ B
-- ∀ means "for all", → means "implies"
def subset (A B : RasiowaSet α) : Prop := ∀ x, x ∈ A → x ∈ B

-- Notation for subset - precedence 50 same as equality and membership
-- This means a ∈ A ⊆ B is parsed as a ∈ (A ⊆ B), which gives type error as intended
infixr:50 " ⊆ " => subset
-- Superset notation: A ⊇ B means B ⊆ A (following Rasiowa's notation)
infixr:50 " ⊇ " => fun A B => B ⊆ A

-- Proper subset: A ⊂ B means A ⊆ B and A ≠ B
-- Rasiowa mentions in footnote: "it is said that A is a proper subset of B"
-- when A ⊆ B but A and B are not identical
def proper_subset (A B : RasiowaSet α) : Prop := A ⊆ B ∧ A ≠ B
infixr:50 " ⊂ " => proper_subset

-- Equivalence: (A ⊆ B) ⟺ (for all x: x ∈ A ⇒ x ∈ B)
-- theorem proves a mathematical statement
-- ↔ means "if and only if" (biconditional)
--
-- THEOREM SYNTAX BREAKDOWN:
-- theorem subset_def (A B : RasiowaSet α) : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by rfl
-- |       |          |     |             |   |     |  |     |     |      | |  |
-- |       |          |     |             |   |     |  |     |     |      | |  └─ Proof term (reflexivity)
-- |       |          |     |             |   |     |  |     |     |      | └─ Proof keyword
-- |       |          |     |             |   |     |  |     |     |      └─ Assignment
-- |       |          |     |             |   |     |  |     |     └─ Right side implication
-- |       |          |     |             |   |     |  |     └─ Membership predicate
-- |       |          |     |             |   |     |  └─ Variable x
-- |       |          |     |             |   |     └─ Universal quantifier
-- |       |          |     |             |   └─ Biconditional operator
-- |       |          |     |             └─ Type annotation separator
-- |       |          |     └─ Shared type: RasiowaSet α (both A and B have this type)
-- |       |          └─ Parameters A and B
-- |       └─ Theorem name
-- └─ Theorem declaration keyword
--
-- LOGICAL STRUCTURE EXPLANATION:
-- • theorem: declares a mathematical statement that we will prove
-- • subset_def: name of the theorem (defines what subset means)
-- • (A B : RasiowaSet α): parameters - any two sets A and B
-- • : separates parameters from the statement to prove
-- • A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B: the biconditional statement
--   - Left side: A ⊆ B (subset relation)
--   - ↔: "if and only if" (equivalence)
--   - Right side: ∀ x, x ∈ A → x ∈ B (universal quantification)
-- • := by rfl: proof that this equivalence holds by reflexivity
--   - The definition of subset IS exactly the universal quantification
--   - So both sides are definitionally equal (rfl proves this)
--
-- HOW rfl WORKS HERE:
-- We defined subset as: def subset (A B : RasiowaSet α) : Prop := ∀ x, x ∈ A → x ∈ B
-- We created infix notation: infixr:50 " ⊆ " => subset
-- So A ⊆ B is syntactic sugar that expands to: subset A B
-- Which by definition equals: ∀ x, x ∈ A → x ∈ B
-- Therefore A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B is true by reflexivity of equality
--
-- NOTATION EXPANSION CHAIN:
-- A ⊆ B                    ← What we write (infix notation)
--   ↓ (infixr:50 " ⊆ " => subset)
-- subset A B               ← Function call (notation expands)
--   ↓ (def subset ... := ∀ x, x ∈ A → x ∈ B)
-- ∀ x, x ∈ A → x ∈ B      ← Definition unfolds
theorem subset_def (A B : RasiowaSet α) :
  A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B :=
by rfl

/-! ### 2.2 Negated Subset Relation - Equation (6) -/

-- Rasiowa's formula (6): "A ⊄ B if and only if not every element of the
-- set A is an element of set B, that is, there exists in the set A an element
-- which is not an element of B"
--
-- She provides this example: "The set of all integers divisible by 3 is not
-- contained in the set of all integers divisible by 6, since there exists an
-- integer divisible by 3 which is not divisible by 6, e.g., the number 9."
--
-- LOGICAL STRUCTURE:
-- ¬(A ⊆ B) means ¬(∀ x, x ∈ A → x ∈ B)
-- Which is equivalent to: ∃ x, ¬(x ∈ A → x ∈ B)
-- Which simplifies to: ∃ x, (x ∈ A ∧ ¬(x ∈ B))
-- Using our notation: ∃ x, (x ∈ A ∧ x ∉ B)
--
-- Rasiowa's symbolic formulation (equation 6):
-- ∼(A ⊆ B) ⟺ (there is an x such that: x ∈ A and ∼(x ∈ B))
--
-- RASIOWA'S PROOF (formalized):
-- "From the definition of subset it follows..."
theorem not_subset_iff (A B : RasiowaSet α) :
  ¬(A ⊆ B) ↔ ∃ x, (x ∈ A ∧ x ∉ B) := by
  constructor
  · -- Forward: ¬(A ⊆ B) → ∃ x, (x ∈ A ∧ x ∉ B)
    intro h
    -- Step 1: Unfold the definition of subset
    rw [subset_def] at h
    -- h : ¬(∀ x, x ∈ A → x ∈ B)

    -- Step 2: Apply Rasiowa's reasoning using classical logic
    -- "not every element of set A is an element of set B"
    -- Use classical: ¬(∀ x, P x) → ∃ x, ¬P x
    rw [not_forall] at h
    -- h : ∃ x, ¬(x ∈ A → x ∈ B)

    -- Step 3: Extract the witness and simplify negated implication
    cases h with
    | intro x hx =>
      -- hx : ¬(x ∈ A → x ∈ B)
      -- Apply: ¬(P → Q) ↔ (P ∧ ¬Q)
      rw [not_imp] at hx
      -- hx : x ∈ A ∧ x ∉ B
      exact ⟨x, hx⟩

  · -- Reverse: ∃ x, (x ∈ A ∧ x ∉ B) → ¬(A ⊆ B)
    intro h
    cases h with
    | intro x hx =>
      -- hx : x ∈ A ∧ x ∉ B
      cases hx with
      | intro hx_in_A hx_not_in_B =>
        intro h_subset
        -- If A ⊆ B, then x ∈ A → x ∈ B
        have hx_in_B : x ∈ B := h_subset x hx_in_A
        -- Contradiction with x ∉ B
        exact hx_not_in_B hx_in_B

-- NOTE ON RASIOWA'S PROOF METHOD:
-- This illustrates classical logical reasoning:
-- 1. Start with definition (A ⊆ B := ∀ x, x ∈ A → x ∈ B)
-- 2. Apply negation (¬(A ⊆ B) means ¬(∀ x, x ∈ A → x ∈ B))
-- 3. Use logical equivalence (¬∀ ↔ ∃¬, and ¬(P → Q) ↔ (P ∧ ¬Q))
-- 4. Arrive at conclusion (∃ x, (x ∈ A ∧ x ∉ B))
--
-- This represents a step-by-step logical derivation rather than just an assertion.

/-! ### 2.3 Set Equality - Proposition (7) -/

-- Set equality A = B
-- Two sets are equal if and only if every element belongs to A iff it belongs to B
-- Formally: A = B ↔ ∀ x, (x ∈ A ↔ x ∈ B)
--
-- NOTE ON SET EQUALITY:
-- This expresses the extensionality principle - sets are determined by their elements
-- A = B means: for any x, x is in A exactly when x is in B
-- This appears stronger than mutual subset - it's bidirectional membership equivalence
--
-- Here, function equality is extensional, so A = B as functions means ∀ x, A x = B x
-- Since sets are predicates (α → Prop), this becomes ∀ x, (A x ↔ B x)
-- Which translates to: ∀ x, (x ∈ A ↔ x ∈ B)
theorem set_extensionality (A B : RasiowaSet α) :
  A = B ↔ ∀ x, (x ∈ A ↔ x ∈ B) := by
  constructor
  · -- Forward direction: if A = B, then same membership
    intro h x
    rw [h]
  · -- Reverse direction: if same membership, then A = B
    intro h
    funext x  -- Function extensionality
    exact propext (h x)  -- Propositional extensionality

/-! ## 3. Concrete Examples and Demonstrations

This section provides concrete examples using natural numbers to illustrate
the abstract concepts and test our definitions.
-/

-- Concrete example using natural numbers (available in pure Lean)
-- Let's define some specific sets to illustrate the concepts

-- Example sets from textbook context: A = {1, 2}, B = {1, 2, 3}
-- Using explicit disjunctive predicates to show the logical structure clearly
def setA : RasiowaSet Nat := fun x => x = 1 ∨ x = 2
def setB : RasiowaSet Nat := fun x => x = 1 ∨ x = 2 ∨ x = 3

-- Working through a concrete example (matching the blog's pedagogical approach):
-- Define setA = {1,2} and setB = {1,2,3}, then prove setA ⊆ setB
-- Proof: if x ∈ A, then x = 1 ∨ x = 2, which implies x ∈ B
--
-- WHY WE DON'T USE subset_def HERE:
-- The subset_def theorem just tells us what ⊆ means: A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B
-- It proves this by reflexivity (rfl) because it's a definitional equality.
-- But that doesn't help us prove the actual logical content of ∀ x, x ∈ setA → x ∈ setB
-- We still need to do case analysis on x ∈ setA and prove x ∈ setB
--
-- Think of it this way:
-- • subset_def: "Here's what 'subset' means" (definitional)
-- • This proof: "Here's why setA ⊆ setB is actually true" (logical work)
--
-- PROOF EXPLANATION:
-- This proof introduces several basic proof tactics
--
-- PROOF STRUCTURE BREAKDOWN:
-- theorem example_subset : setA ⊆ setB := by
-- |                         |      |      |  |
-- |                         |      |      |  └─ Tactic mode (step-by-step proof)
-- |                         |      |      └─ Assignment to proof
-- |                         |      └─ Proposition to prove
-- |                         └─ Type signature
-- └─ Example declaration (anonymous proof for demonstration)
example : setA ⊆ setB := by
  -- STEP 1: INTRO TACTIC
  -- Goal: setA ⊆ setB
  -- Since subset is defined as: ∀ x, x ∈ A → x ∈ B
  -- The intro tactic introduces the universal quantifier and implication
  -- intro x h means: "assume x is arbitrary and h : x ∈ setA"
  intro x h
  -- After intro: Goal becomes x ∈ setB, with assumptions x : Nat, h : x ∈ setA

  -- STEP 2: CASES TACTIC
  -- h : x ∈ setA means h : x = 1 ∨ x = 2 (by definition of setA)
  -- The cases tactic does case analysis on disjunction (∨)
  --
  -- HOW CASES WORKS HERE:
  -- Disjunction (∨) is an inductive type with two constructors:
  -- • Or.inl : A → A ∨ B  (left side - "in left")
  -- • Or.inr : B → A ∨ B  (right side - "in right")
  --
  -- Since h : x = 1 ∨ x = 2, it was constructed using either:
  -- • Or.inl (proof of x = 1), or
  -- • Or.inr (proof of x = 2)
  --
  -- The cases tactic deconstructs h to see which constructor was used:
  -- cases h with
  -- | inl h1 => ...  -- Case where h = Or.inl h1, so h1 : x = 1
  -- | inr h2 => ...  -- Case where h = Or.inr h2, so h2 : x = 2
  --
  -- This covers all cases: every disjunction is either left or right
  cases h with
  -- CASE 1: LEFT SIDE OF DISJUNCTION (inl = "in left")
  | inl h1 =>
    -- h1 : x = 1 (the left side of x = 1 ∨ x = 2)
    -- Goal: x ∈ setB, which means x = 1 ∨ x = 2 ∨ x = 3
    -- Since we know x = 1, we choose the left side of the target disjunction
    left;     -- Choose left side of (x = 1 ∨ x = 2 ∨ x = 3)
    exact h1  -- Provide proof: h1 : x = 1 exactly matches what we need

  -- CASE 2: RIGHT SIDE OF DISJUNCTION (inr = "in right")
  | inr h2 =>
    -- h2 : x = 2 (the right side of x = 1 ∨ x = 2)
    -- Goal: x ∈ setB, which means x = 1 ∨ x = 2 ∨ x = 3
    -- Since we know x = 2, we need the middle part: x = 2 ∨ x = 3
    right;      -- Choose right side: (x = 2 ∨ x = 3) instead of x = 1
    left;       -- Choose left side of (x = 2 ∨ x = 3), giving us x = 2
    exact h2    -- Provide proof: h2 : x = 2 exactly matches what we need

-- TACTIC GLOSSARY:
-- • by: enters tactic mode for step-by-step proof construction
-- • intro: introduces assumptions (∀ and → become assumptions)
-- • cases: case analysis on inductive types (here disjunction ∨)
-- • inl/inr: constructors for disjunction (left/right sides)
-- • left: choose left side of disjunction in goal
-- • right: choose right side of disjunction in goal
-- • exact: provide exact proof term that matches the goal
-- • semicolon (;): sequence tactics (run second after first succeeds)
--
-- LOGICAL FLOW:
-- 1. Start with ∀ x, x ∈ A → x ∈ B (definition of subset)
-- 2. Assume x and x ∈ A (intro tactic)
-- 3. Since x ∈ A means x = 1 ∨ x = 2, consider both cases (cases tactic)
-- 4. If x = 1, then x ∈ B because 1 is in {1,2,3} (left; exact)
-- 5. If x = 2, then x ∈ B because 2 is in {1,2,3} (right; left; exact)
--
-- This proof illustrates the constructive nature of these proofs:
-- We need to explicitly construct evidence for each logical step.

-- We can also check membership for specific elements
example : 1 ∈ setA := by left; rfl   -- 1 ∈ {1, 2} because 1 = 1
example : 2 ∈ setA := by right; rfl  -- 2 ∈ {1, 2} because 2 = 2
example : 1 ∈ setB := by left; rfl   -- 1 ∈ {1, 2, 3} because 1 = 1
example : 2 ∈ setB := by right; left; rfl  -- 2 ∈ {1, 2, 3} because 2 = 2

/-! ## 4. Basic Properties of Subset Relation

This section proves the fundamental properties of the subset relation:
Propositions 1.1 (8), (9), and (10) from Rasiowa's textbook.

These theorems establish that ⊆ is:
- **Empty-closed**: ∅ ⊆ A for any A (Prop. 1.1.8)
- **Reflexive**: A ⊆ A for any A (Prop. 1.1.9)
- **Transitive**: A ⊆ B ∧ B ⊆ C → A ⊆ C (Prop. 1.1.10)
-/

/-! ### 4.1 Empty Set Property - Proposition 1.1 (8) -/

-- Empty set is subset of any set
-- Rasiowa's Proposition 1.1 (8): "∅ ⊆ A for any set A"
-- A classic example from every set theory textbook
--
-- PROOF EXPLANATION: Why is ∅ ⊆ A for any set A?
-- We need to prove: ∀ x, x ∈ ∅ → x ∈ A
-- But x ∈ ∅ is impossible (empty set has no elements)
-- Since the premise is false, the implication is vacuously true
--
-- VERBOSE TACTIC PROOF:
theorem empty_subset (A : RasiowaSet α) : ∅ ⊆ A := by
  -- Goal: ∅ ⊆ A, which means ∀ x, x ∈ ∅ → x ∈ A
  intro x h
  -- After intro: x : α, h : x ∈ ∅, Goal: x ∈ A
  -- But h : x ∈ ∅ means h : False (by definition of empty set ∅)
  -- From False, we can prove anything using False.elim
  exact False.elim h
  -- False.elim : False → P means "from falsehood, anything follows"
  -- This follows the principle of explosion (ex falso quodlibet)

/-! ### 4.2 Reflexivity Property - Proposition 1.1 (9) -/

-- ALTERNATIVE: CONCISE LAMBDA PROOF
-- The same proof can be written directly as a lambda term:
-- theorem empty_subset (A : RasiowaSet α) : ∅ ⊆ A := fun _ h => False.elim h
--
-- COMPARISON:
-- • Tactic mode: Step-by-step, educational, shows reasoning process
-- • Term mode: Direct lambda, concise, functional programming style
-- • Both prove the same mathematical fact using the same logical principle
--
-- HOW THE LAMBDA VERSION WORKS:
-- fun _ h => False.elim h
-- |   | |    |         |
-- |   | |    |         └─ Apply False.elim to h
-- |   | |    └─ False.elim proves anything from False
-- |   | └─ h : x ∈ ∅, which is h : False
-- |   └─ Ignored element (we don't need to know what x is)
-- └─ Lambda creating function ∀ x, x ∈ ∅ → x ∈ A

-- Every set is subset of itself (reflexivity)
-- Rasiowa's Proposition 1.1 (9): "A ⊆ A for any set A" (reflexivity)
-- Another foundational property that seems obvious but requires proof
--
-- PROOF EXPLANATION: Why is A ⊆ A for any set A?
-- We need to prove: ∀ x, x ∈ A → x ∈ A
-- This appears trivially true - if x is in A, then x is in A!
-- The proof essentially uses the identity function on the assumption
--
-- VERBOSE TACTIC PROOF:
theorem subset_refl (A : RasiowaSet α) : A ⊆ A := by
  -- Goal: A ⊆ A, which means ∀ x, x ∈ A → x ∈ A
  intro x h
  -- After intro: x : α, h : x ∈ A, Goal: x ∈ A
  -- We already have exactly what we need: h : x ∈ A
  exact h
  -- The proof is just returning the assumption unchanged
  -- This shows that ∀ x, x ∈ A → x ∈ A works as the identity function

-- ALTERNATIVE: CONCISE LAMBDA PROOF
-- The same proof can be written directly as a lambda term:
-- theorem subset_refl (A : RasiowaSet α) : A ⊆ A := fun _ h => h
--
-- COMPARISON:
-- • Tactic mode: Shows that we're just returning the assumption
-- • Term mode: Directly expresses the identity function λ _ h. h
-- • Both express the same idea: A ⊆ A appears trivially true
--
-- HOW THE LAMBDA VERSION WORKS:
-- fun _ h => h
-- |   | |    |
-- |   | |    └─ Return h unchanged (h : x ∈ A proves x ∈ A)
-- |   | └─ h : x ∈ A (assumption that x is in A)
-- |   └─ Ignored element (we don't need to examine x itself)
-- └─ Lambda creating function ∀ x, x ∈ A → x ∈ A (identity on membership proofs)
--
-- OBSERVATION:
-- Reflexivity of ⊆ seems to correspond to the identity function in logic
-- Logical implications of the form P → P can be proved by the identity function

/-! ### 4.3 Transitivity Property - Proposition 1.1 (10) -/

-- Subset relation is transitive: A ⊆ B ∧ B ⊆ C → A ⊆ C
-- Rasiowa's Proposition 1.1 (10): transitivity of the subset relation
-- If A ⊆ B and B ⊆ C, then A ⊆ C
--
-- PROOF EXPLANATION: Why does A ⊆ B → B ⊆ C → A ⊆ C?
-- If every element of A is in B, and every element of B is in C,
-- then every element of A must be in C (by chaining the implications)
-- This resembles function composition applied to membership proofs
--
-- VERBOSE TACTIC PROOF:
theorem subset_trans (A B C : RasiowaSet α) : A ⊆ B → B ⊆ C → A ⊆ C := by
  -- Goal: A ⊆ B → B ⊆ C → A ⊆ C
  intro h₁ h₂
  -- After intro: h₁ : A ⊆ B, h₂ : B ⊆ C, Goal: A ⊆ C
  -- Now we need to prove A ⊆ C, which means ∀ x, x ∈ A → x ∈ C
  intro x h
  -- After intro: x : α, h : x ∈ A, Goal: x ∈ C
  -- We have h : x ∈ A and h₁ : A ⊆ B, so we can get x ∈ B
  have h_B : x ∈ B := h₁ x h
  -- Now we have h_B : x ∈ B and h₂ : B ⊆ C, so we can get x ∈ C
  exact h₂ x h_B
  -- This chains: x ∈ A → x ∈ B → x ∈ C

-- ALTERNATIVE: CONCISE LAMBDA PROOF
-- The same proof can be written directly as a lambda term:
-- theorem subset_trans (A B C : RasiowaSet α) : A ⊆ B → B ⊆ C → A ⊆ C :=
-- fun h₁ h₂ x h => h₂ x (h₁ x h)
--
-- COMPARISON:
-- • Tactic mode: Shows the step-by-step chaining with intermediate `have`
-- • Term mode: Direct function composition h₂ ∘ h₁ applied to membership
-- • Both demonstrate the same compositional structure
--
-- HOW THE LAMBDA VERSION WORKS:
-- fun h₁ h₂ x h => h₂ x (h₁ x h)
-- |   |  |  | |    |  | |  |  |
-- |   |  |  | |    |  | |  |  └─ h : x ∈ A (starting assumption)
-- |   |  |  | |    |  | |  └─ Apply h₁ to x and h
-- |   |  |  | |    |  | └─ This gives h₁ x h : x ∈ B
-- |   |  |  | |    |  └─ Apply h₂ to x
-- |   |  |  | |    └─ Apply result to (h₁ x h)
-- |   |  |  | └─ h : x ∈ A (element membership assumption)
-- |   |  |  └─ x : α (arbitrary element)
-- |   |  └─ h₂ : B ⊆ C (second subset assumption)
-- |   └─ h₁ : A ⊆ B (first subset assumption)
-- └─ Lambda creating function A ⊆ B → B ⊆ C → A ⊆ C
--
-- OBSERVATION:
-- Transitivity appears to correspond to function composition in logic
-- The proof structure resembles: (g ∘ f)(x) = g(f(x))
-- Here: (h₂ ∘ h₁) proves A ⊆ C from A ⊆ B and B ⊆ C
--
-- COMPUTATIONAL PATTERNS IN SUBSET THEOREMS:
-- These three theorems (Propositions 1.1 (8), (9), (10)) illustrate fundamental patterns:
--
-- 1. empty_subset (False elimination):
--    Lean: fun _ h => False.elim h
--    Pattern: Handle impossible/contradictory inputs
--
-- 2. subset_refl (Identity):
--    Lean: fun _ h => h  
--    Pattern: Identity function - return input unchanged
--
-- 3. subset_trans (Composition):
--    Lean: fun h₁ h₂ x h => h₂ x (h₁ x h)
--    Pattern: Function composition - chain two functions
--
-- OBSERVATION:
-- These patterns seem to correspond to basic logical principles:
-- • Exception handling (impossible cases)
-- • Identity transformation (trivial cases)  
-- • Pipeline composition (chaining operations)
--
-- The Curry-Howard correspondence shows that proofs ARE programs!
-- Every logical principle corresponds to a computational pattern.

/-! ### 4.4 Mutual Subset Equality - Proposition 1.1 (11) -/

-- Two sets are equal if and only if they are mutually subsets
-- This expresses the antisymmetry property of the subset relation
--
-- PROOF EXPLANATION: Why does A ⊆ B ∧ B ⊆ A → A = B?
-- If every element of A is in B, and every element of B is in A,
-- then A and B have exactly the same elements, so they are equal.
-- This uses the extensionality principle: sets are determined by their elements.
--

theorem subset_antisymm (A B : RasiowaSet α) : A ⊆ B → B ⊆ A → A = B := by
  -- Goal: A ⊆ B → B ⊆ A → A = B
  intro h₁ h₂
  -- After intro: h₁ : A ⊆ B, h₂ : B ⊆ A, Goal: A = B
  -- Use set extensionality: two sets are equal iff they have same membership
  rw [set_extensionality]
  -- Goal: ∀ x, (x ∈ A ↔ x ∈ B)
  intro x
  -- Goal: x ∈ A ↔ x ∈ B
  constructor
  · -- Forward: x ∈ A → x ∈ B
    exact h₁ x
  · -- Reverse: x ∈ B → x ∈ A
    exact h₂ x

-- ALTERNATIVE: CONCISE PROOF USING SET EXTENSIONALITY
-- The same proof can be written more directly:
-- theorem subset_antisymm (A B : RasiowaSet α) : A ⊆ B → B ⊆ A → A = B :=
-- fun h₁ h₂ => set_extensionality.mpr (fun x => ⟨h₁ x, h₂ x⟩)
--
-- OBSERVATION:
-- This theorem shows that the subset relation is antisymmetric
-- Combined with reflexivity and transitivity, this suggests ⊆ forms a partial order
-- The proof structure: bidirectional membership equivalence from mutual inclusion

/-! ### 4.5 Inequality Disjunction - Proposition 1.1 (12) -/

-- If two sets are not equal, then one is not a subset of the other
-- This follows from the contrapositive of the antisymmetry property
--
-- PROOF EXPLANATION: Why does A ≠ B → A ⊄ B ∨ B ⊄ A?
-- This appears logically equivalent to the contrapositive of proposition (11):
-- If A ⊆ B and B ⊆ A, then A = B
-- Contrapositive: If A ≠ B, then ¬(A ⊆ B ∧ B ⊆ A)
-- Which is equivalent to: A ≠ B → (A ⊄ B ∨ B ⊄ A) by De Morgan's law
--

theorem inequality_disjunction (A B : RasiowaSet α) : A ≠ B → ¬(A ⊆ B) ∨ ¬(B ⊆ A) := by
  -- Goal: A ≠ B → ¬(A ⊆ B) ∨ ¬(B ⊆ A)
  intro h
  -- After intro: h : A ≠ B, Goal: ¬(A ⊆ B) ∨ ¬(B ⊆ A)
  -- Use classical reasoning: either A ⊆ B or A ⊄ B
  by_cases h₁ : A ⊆ B
  · -- Case: A ⊆ B
    right  -- Choose right side of disjunction: ¬(B ⊆ A)
    intro h₂  -- Assume B ⊆ A
    -- h₂ : B ⊆ A, h₁ : A ⊆ B
    -- By antisymmetry: A = B
    have h_eq : A = B := subset_antisymm A B h₁ h₂
    -- Contradiction with h : A ≠ B
    exact h h_eq
  · -- Case: A ⊄ B (¬(A ⊆ B))
    left   -- Choose left side of disjunction: ¬(A ⊆ B)
    exact h₁

-- ALTERNATIVE: DIRECT CONTRAPOSITIVE PROOF
-- We could also prove this as the contrapositive of subset_antisymm:
-- theorem inequality_disjunction (A B : RasiowaSet α) : A ≠ B → ¬(A ⊆ B) ∨ ¬(B ⊆ A) :=
-- fun h => by_contra (fun h_contra => h (subset_antisymm A B
--   (Classical.not_or.mp h_contra).1 (Classical.not_or.mp h_contra).2))
--
-- LOGICAL STRUCTURE:
-- This illustrates the logical relationship:
-- • Antisymmetry: (A ⊆ B ∧ B ⊆ A) → A = B
-- • Contrapositive: A ≠ B → ¬(A ⊆ B ∧ B ⊆ A)
-- • De Morgan: A ≠ B → (¬(A ⊆ B) ∨ ¬(B ⊆ A))
--
-- OBSERVATION:
-- This helps complete our characterization of set equality in terms of subset relations
-- Together with propositions (8)-(11), this gives us the basic theory of
-- the subset relation as a partial order with specific properties

end Rasiowa
