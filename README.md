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

## Future Plans
- Tactics that work on `Rep`, allowing for tactics that can work on any data structure.
- (True) Dependent Types
- More exotic types (Quotient types, Intersection Types, etc)

## Disclaimer
This is very much a work in progress! `tactic-haskell` makes
no promises about anything at this stage. It could work perfectly, or it could decide to burn down your house.
