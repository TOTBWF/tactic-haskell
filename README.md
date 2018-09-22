# tactic-haskell
Tactic Metaprogramming as a library! This project aims to bring the proof automation
capabilities of Coq and others to Haskell.

Here's some examples:

```
p = $(tactic [t| forall a b. a -> b -> (a,b)|] $ do
  intro
  x <- intro
  y <- intro
  intro <..> [use x, use y])
```

```
f = $(tactic [t| forall a b. a -> (a -> b) -> b|] $ do
  intro
  x <- intro
  f <- intro
  elim f
  assumption)
```

## Notes
As of now, I'v directly using the Haskell type system/expression language as the term language.
However, this presents a couple of problems.
1. Template Haskell gets run in the renamer. As a result, there is no access to the haskell typechecker.
This makes doing even the most basic of things extremely difficult. For example `use '[]` won't unify
with the goal type `[Int]` because `'[]` _actually_ has type `forall (a :: *) [a]`.

I think the solution is to actually define another language that we can embed haskell inside.
This would allow richer types, simpler code, and an actual typechecker, but presents other hurdles. 

The basic implementation would use a custom quasiquoter.

## Future Plans
- Tactics that work on `Rep`, allowing for tactics that can work on any data structure.
- (True) Dependent Types
- More exotic types (Quotient types, Intersection Types, etc)

## Disclaimer
This is very much a work in progress! `tactic-haskell` makes
no promises about anything at this stage. It could work perfectly, or it could decide to burn down your house.
