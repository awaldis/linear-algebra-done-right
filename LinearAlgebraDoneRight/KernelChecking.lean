/-!
# Understanding Lean 4 Kernel Type Checking

This file demonstrates how the Lean kernel validates proofs.
The kernel is the small, trusted core that type-checks fully elaborated terms.

## Kernel Type-Checking Rules

The kernel validates proofs using these primitive rules:

1. **Variables** - If x has type T in context, kernel accepts it
2. **Application** - If f : A → B and a : A, then f a : B
3. **Lambda** - If body has type B under assumption x : A, then (fun x => body) : A → B
4. **Definitional Equality** - Terms that reduce to same normal form are equal
5. **Constructors** - Built-in rules for Prop, Type, inductives

Let's see these in action:
-/

-- Show the fully elaborated proof terms
set_option pp.explicit true
set_option pp.proofs true
set_option pp.all true

/-! ## Example 1: True.intro (Constructor Rule) -/

theorem true_is_true : True :=
  True.intro

-- Let's examine what the kernel checks:
#check @True.intro
-- True.intro : True
-- Kernel rule: This is a primitive constructor for the True type.
-- The kernel knows: True is an inductive with one constructor `intro : True`
-- Type checking: intro has type True ✓

#print True
-- Kernel sees: inductive True : Prop where | intro : True
-- To validate our proof, kernel checks: True.intro has type True ✓


/-! ## Example 2: rfl (Definitional Equality) -/

theorem refl_example (α : Sort _) (x : α) : x = x := 
  rfl

theorem refl_example2 (α : Sort _) (x : α) : x = x :=
  Eq.refl x

--variable (α : Type) (z : α)
variable (z : Nat)

-- This creates a "variable" named 'p' which is a proof that z = z
def p : z = z := Eq.refl z

#check p

#check @rfl
-- @rfl.{u} : ∀ {α : Sort u} {x : α}, @Eq.{u} α x x
-- This is the reflexivity axiom built into the kernel

#reduce refl_example Nat 5
-- Kernel reduces this to: @rfl.{1} Nat 5
-- Kernel rule: rfl proves x = x by definitional equality

/-! Let's see the kernel's step-by-step validation of `rfl`: -/

-- Elaborated term: @rfl.{u_1} α x
-- Kernel checks:
--   1. rfl has type: ∀ {α : Sort u} {x : α}, Eq α x x
--   2. Apply rfl to implicit argument α (type Sort u_1):
--      Result type: ∀ {x : α}, Eq α x x
--   3. Apply to implicit argument x (type α):
--      Result type: Eq α x x
--   4. Goal requires: Eq α x x
--   5. Types match ✓


/-! ## Example 3: Function Application -/

theorem id_preserves (P : Prop) : P → P :=
  fun h => h

#check @id_preserves
-- Shows: ∀ (P : Prop), P → P

-- Let's manually check how kernel validates this:
-- Elaborated: fun (P : Prop) (h : P) => h
-- Kernel checking steps:
--   1. We have: P : Prop in context
--   2. We assume: h : P in context
--   3. Body is: h
--   4. Type of h is: P (from context) ✓
--   5. Lambda rule: (fun h : P => h) has type P → P ✓
--   6. Lambda rule: (fun P : Prop => fun h : P => h) has type ∀ P : Prop, P → P ✓


/-! ## Example 4: Projection (Accessing structure fields) -/

theorem and_right {P Q : Prop} : P ∧ Q → Q :=
  fun h => h.right

-- Elaborated to: fun {P Q : Prop} (h : And P Q) => @And.right P Q h

#check @And.right
-- @And.right : ∀ {a b : Prop}, And a b → b
-- This is a primitive projection - the kernel knows And is a structure with `.right`

#print And
-- inductive And (a b : Prop) : Prop where
--   | intro : a → b → And a b
-- And.left and And.right are primitive projections

-- Kernel validation:
--   1. h has type: And P Q
--   2. And.right is a projection with type: ∀ {a b}, And a b → b
--   3. Apply And.right to {P} {Q} h
--   4. Result type: Q ✓


/-! ## Example 5: Definitional Equality with Computation -/

theorem zero_eq_zero : (0 : Nat) = 0 :=
  rfl

-- The elaborated term shows numeral handling:
#check (0 : Nat)
-- This becomes: @OfNat.ofNat Nat 0 (instOfNatNat 0)

#reduce (0 : Nat)
-- Reduces to: Nat.zero

-- Kernel validation for rfl:
--   1. Left side: @OfNat.ofNat Nat 0 (instOfNatNat 0)
--   2. Reduce: Nat.zero
--   3. Right side: @OfNat.ofNat Nat 0 (instOfNatNat 0)
--   4. Reduce: Nat.zero
--   5. Both sides reduce to Nat.zero (definitionally equal) ✓
--   6. rfl is valid ✓


/-! ## Example 6: Beta Reduction -/

theorem apply_id {α : Sort _} (x : α) : (fun y => y) x = x :=
  rfl

#reduce (fun (y : Nat) => y) 42
-- Reduces to: 42

-- Kernel validation:
--   1. Left side: (fun y => y) x
--   2. Beta-reduce: Substitute x for y in body => x
--   3. Right side: x
--   4. Both sides are definitionally equal to x ✓
--   5. rfl is valid ✓


/-! ## Summary: How the Kernel Works

When you submit a proof term to the kernel:

1. **Parsing is done** - You send fully elaborated terms (elaboration already happened)

2. **Kernel type-checks recursively**:
   - For each subterm, compute its type
   - Check types match using definitional equality
   - Definitional equality uses reduction rules (beta, delta, iota, etc.)

3. **Reduction rules**:
   - **Beta**: (fun x => body) a  ~~>  body[x := a]
   - **Delta**: Unfold definitions
   - **Iota**: Constructor/match reduction
   - **Eta**: (fun x => f x) ~~> f

4. **Type checking succeeds** if:
   - All variables are in scope
   - All applications type-check
   - All definitional equalities hold

The kernel is ~5000 lines of trusted code. Everything else (tactics, elaboration, etc.)
just produces terms that the kernel validates.
-/
