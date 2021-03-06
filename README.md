# tactic-haskell
Tactic Metaprogramming as a library! This project aims to bring the proof automation
capabilities of Coq and others to Haskell.

Here's some examples:

```haskell
tactic "pair" [t| forall a b. a -> b -> (a,b)|] $ do
  forall
  intros_
  split
  assumption
```

```haskell
tactic "&" [t| forall a b. a -> (a -> b) -> b |] $ do
  forall
  intro "x"
  intro "f"
  apply "f"
  exact "x"
```

```haskell
tactic "foo" [t| forall a b c. a -> (a -> b) -> (b -> c) -> (a,c)|] $ do
  auto 5
```

``` haskell
tactic "either" [t| forall a b c. (a -> c) -> (b -> c) -> Either a b -> c |] $ auto 5
```

``` haskell
tactic "myFold" [t| forall a b. (a -> b -> b) -> b -> [a] -> b |] $ auto 5
```

```haskell
data Nat = Z | S Nat deriving (Show)

tactic "plus" [t| Nat -> Nat -> Nat |] $ do
  intros ["n", "m"]
  induction "n" <@>
    [ exact "m"
    , do
       apply 'S
       exact "ind"
    ]
```


For more examples, see the `samples/` directory.

## TODOs 
- Add support for type classes.
- Allow `auto` to use at top-level bindings/imported functions.
- Tidy up the output of `induction`
- Create a GHCI wrapper that allows usage from the command line/as an editor tool

## Disclaimer
This is very much a work in progress! `tactic-haskell` makes
no promises about anything at this stage. It could work perfectly, or it could decide to burn down your house.
Also, even though `auto` is good at it's job, it isn't perfect, make sure to check the output by
using `debugTactic`. 
