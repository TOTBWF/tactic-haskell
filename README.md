# tactic-haskell
Tactic Metaprogramming as a library! This project aims to bring the proof automation
capabilities of Coq and others to Haskell.

Here's some examples:

```
tactic "pair" [t| forall a b. a -> b -> (a,b)|] $ do
  intro
  intro "x"
  intro "y"
  split <..> [exact "x", exact "y"]
```

```
tactic "fapply" [t| forall a b. a -> (a -> b) -> b|] $ do
  forall
  intro "x"
  intro "f"
  apply "f"
  exact "x"
```

## Future Plans
- (True) Dependent Types
- More exotic types (Quotient types, Intersection Types, etc)

## Disclaimer
This is very much a work in progress! `tactic-haskell` makes
no promises about anything at this stage. It could work perfectly, or it could decide to burn down your house.
