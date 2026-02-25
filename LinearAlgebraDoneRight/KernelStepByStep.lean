/-!
# Step-by-Step Kernel Validation Trace

This file shows exactly what the Lean kernel does when validating a proof,
step by step, as if you were the kernel type-checker.
-/

set_option pp.explicit true
set_option pp.proofs true

/-!
## Example: Validating `rfl` for `5 = 5`

Let's trace through exactly what happens when the kernel validates:
  `theorem five_eq_five : 5 = 5 := rfl`
-/

theorem five_eq_five : (5 : Nat) = 5 := rfl

/-!
### Kernel Validation Trace:

**Step 1: Receive elaborated proof term**
```
@rfl.{1} Nat 5
```

**Step 2: Look up type of `rfl` in environment**
```
rfl : ∀ {α : Sort u} {a : α}, Eq α a a
```

**Step 3: Type-check the application `@rfl.{1} Nat 5`**

Sub-step 3a: Instantiate universe variable u with 1
```
rfl : ∀ {α : Sort 1} {a : α}, Eq α a a
```

Sub-step 3b: Apply rfl to first implicit arg `Nat`
- Check: Nat : Sort 1?
- Compute: `#check Nat` gives `Nat : Type`
- Compute: `Type = Sort 1` (by definition)
- ✓ Match!
- Result type: `∀ {a : Nat}, Eq Nat a a`

Sub-step 3c: Apply to second implicit arg `5`
- Check: 5 : Nat?
- Compute type of 5...
  - 5 is sugar for `@OfNat.ofNat Nat 5 (instOfNatNat 5)`
  - Type of OfNat.ofNat: `∀ {α} (n : Nat) [inst : OfNat α n], α`
  - Instantiate with α := Nat, n := 5, inst := instOfNatNat 5
  - Result type: Nat
- ✓ Match!
- Result type: `Eq Nat 5 5`

**Step 4: Compare result type with goal**
- Result: `Eq Nat 5 5`
- Goal: `Eq Nat 5 5`
- Are they definitionally equal?
  - Both reduce to same normal form ✓
- ✓ Proof accepted!
-/

#check @five_eq_five
#print five_eq_five


/-!
## Example 2: Function Application

Let's validate: `theorem use_id : (fun (x : Nat) => x) 7 = 7 := rfl`
-/

theorem use_id : (fun (x : Nat) => x) 7 = 7 := rfl

/-!
### Kernel Validation Trace:

**Step 1: Receive proof term**
```
@rfl.{1} Nat ((fun (x : Nat) => x) 7)
```

**Step 2: Type-check `@rfl.{1} Nat ((fun (x : Nat) => x) 7)`**

Sub-step: Check the term `(fun (x : Nat) => x) 7`
- It's an application, so check both parts:

  Check function: `(fun (x : Nat) => x)`
  - It's a lambda: `fun (x : Nat) => x`
  - Variable x : Nat is in local context
  - Body is: x
  - Type of body: Nat (from context)
  - Lambda rule: `fun (x : Nat) => x` has type `Nat → Nat` ✓

  Check argument: `7`
  - Type of 7: Nat ✓

  Application rule: `(Nat → Nat) 7` has type `Nat` ✓

**Step 3: Apply rfl**
- rfl gets arguments: Nat and `(fun x => x) 7`
- Result type: `Eq Nat ((fun x => x) 7) ((fun x => x) 7)`

**Step 4: Check definitional equality with goal**
- Goal: `Eq Nat ((fun x => x) 7) 7`
- Result: `Eq Nat ((fun x => x) 7) ((fun x => x) 7)`
- Need to check: `((fun x => x) 7) ≡ 7` (definitional equality)

**Step 5: Reduce both sides**
- Left side: `(fun (x : Nat) => x) 7`
  - **Beta-reduce**: substitute 7 for x in body `x`
  - Result: `7`
- Right side: `7`
- Both reduce to `7` ✓
- Definitionally equal ✓

**Conclusion: Proof accepted!**
-/

-- Let's verify the reduction:
#reduce (fun (x : Nat) => x) 7   -- Output: 7


/-!
## Example 3: Validating a proof that uses And.right

`theorem get_right (P Q : Prop) (h : P ∧ Q) : Q := h.right`
-/

theorem get_right (P Q : Prop) (h : P ∧ Q) : Q := h.right

/-!
### Kernel Validation Trace:

**Step 1: Receive elaborated proof term**
```
fun (P Q : Prop) (h : And P Q) => @And.right P Q h
```

**Step 2: Type-check the lambda abstraction**

Context starts empty: `[]`

Sub-step 2a: Add P : Prop to context
- Context: `[P : Prop]`

Sub-step 2b: Add Q : Prop to context
- Context: `[P : Prop, Q : Prop]`

Sub-step 2c: Add h : And P Q to context
- Context: `[P : Prop, Q : Prop, h : And P Q]`

Sub-step 2d: Type-check body `@And.right P Q h`
- Look up And.right in environment
  ```
  And.right : ∀ {a b : Prop} (self : And a b), b
  ```
- Apply to P (implicit arg for `a`):
  - Check: P : Prop? ✓ (from context)
  - Result type: `∀ {b : Prop} (self : And P b), b`

- Apply to Q (implicit arg for `b`):
  - Check: Q : Prop? ✓ (from context)
  - Result type: `∀ (self : And P Q), Q`

- Apply to h (explicit arg for `self`):
  - Check: h : And P Q? ✓ (from context)
  - Result type: `Q`

Sub-step 2e: Lambda rules to build up the type:
- Body has type Q in context [P : Prop, Q : Prop, h : And P Q]
- So `fun (h : And P Q) => @And.right P Q h` has type `And P Q → Q`
- So `fun (Q : Prop) => fun (h : And P Q) => ...` has type `∀ (Q : Prop), And P Q → Q`
- So `fun (P : Prop) (Q : Prop) (h : And P Q) => ...` has type `∀ (P Q : Prop), And P Q → Q`

**Step 3: Compare with goal**
- Result: `∀ (P Q : Prop), And P Q → Q`
- Goal: `∀ (P Q : Prop), And P Q → Q`
- ✓ Match!

**Conclusion: Proof accepted!**
-/

#check @get_right


/-!
## How the Kernel Actually Works (Pseudocode)

```
function typeCheck(term, context, environment):
  match term:
    case Variable(name):
      return lookupInContext(name, context)

    case Application(f, a):
      typeF = typeCheck(f, context, environment)
      typeA = typeCheck(a, context, environment)

      // typeF should be a Pi type (Π x : A, B)
      match reduce(typeF):
        case Pi(x, A, B):
          check defEq(typeA, A)  // Definitional equality check
          return substitute(B, x, a)
        case _:
          error "Not a function type"

    case Lambda(x, A, body):
      typeA = typeCheck(A, context, environment)
      checkUniverse(typeA)  // A must be a type

      newContext = context.add(x, A)
      typeBody = typeCheck(body, newContext, environment)

      return Pi(x, A, typeBody)

    case Constructor/Constant(name):
      return lookupInEnvironment(name, environment)

function defEq(term1, term2):
  // Check if two terms are definitionally equal
  normal1 = reduce(term1)
  normal2 = reduce(term2)
  return alphaEq(normal1, normal2)

function reduce(term):
  match term:
    case Application((Lambda(x, _, body)), arg):
      // Beta reduction
      return reduce(substitute(body, x, arg))

    case Definition(name):
      // Delta reduction (unfold definitions)
      return reduce(lookupDefinition(name))

    case Match(Constructor(...), ...):
      // Iota reduction (match/constructor reduction)
      return reduce(matchBranch(...))

    case _:
      return term  // Already in normal form
```

This is the essence of the Lean kernel!
-/
