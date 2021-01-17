---
title: Probabilistic programming in OCaml
header-includes: |
  <link rel="stylesheet" type="text/css" href="css/main.css" />
  <script type="text/javascript" async
    src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.7/MathJax.js?config=TeX-MML-AM_CHTML">
  </script>
  <script type="text/x-mathjax-config">
    MathJax.Hub.Config({
      tex2jax: {
        inlineMath: [ ['$','$'], ["\\(","\\)"] ],
        processEscapes: true
      }
    });
  </script>
---

Here's a classic kind of word problem you might have seen before:

> There's a 1% chance of catching a deadly illness and you test positive.
> The test is correct 99% of the time. Should you be worried?

At some point I learned how to solve problems like these by
translating the problem from English into probability theory
and then performing the proper calculations.
But I haven't studied probability in a while, and
calculations are easy to get wrong.
Meanwhile, I write programs all the time and computers
are great at calculating.
So why not have a program find the answer for me?
The following OCaml code does just that:

```ocaml
(* Let the random variable X be true iff I'm sick.
   d will be the distribution of X given that I tested positive. *)
let d : bool -> float =
  pdf OBool.compare (
    (* Flip a coin with 1% chance of heads. If heads, I'm infected. *)
    let* infected : bool = coin 0.01 in
    let accuracy = 0.99 in
    (* Get tested. *)
    let* test_result =
      if infected
      then coin accuracy
      else coin (1.0 -. accuracy)
    in
    (* Assume the test came back positive. *)
    guard test_result (
    pure infected))
in 
(* What's the probability that I'm sick? *)
d true
(* ==> 0.5 *)
```

Indeed, the probability that I'm sick given that I tested positive is 50%, by Bayes' rule.

This is called 
[probabilistic programming](https://en.wikipedia.org/wiki/Probabilistic_programming).
In regular programming, you write a program and then run it to get a result.
The program you write could use (pseudo)randomness in it (e.g. simulated dice rolls),
but at the end of the run you still only get a single value.
In probabilistic programming, you write a program and then run an _inferencer_
that computes a distribution over output values.
In the above example, the inferencer is `pdf OBool.compare`.
It's argument is a program that simulates the process of getting tested and 
receiving a positive result:

- `guard test_result` is like `assert test_result`;
  it only allows the program to continue past that point if `test_result` is `true`.
- The program returns whether the simulated person is actually sick.

A normal execution of this program would either (1) fail because `test_result` was false
or (2) succeed and return whether or not the simulated person was infected.
The inferencer instead computes a distribution over the output values the program
can succeed with (`true` and `false` in this case);
the probability of succeeding with `true`
corresponds to the probability I'm actually sick given a positive test result.

You can find a lot of papers online about writing efficient inferencers. 
Rather than reading them, I decided to roll my own inferencers and try them out on some 
simple problems. 
This post describes how it works.

## Modelling random computations

Before we implement an inferencer, we need to be able to represent 
probabilistic programs. We can do this with the following signature:

```ocaml
module type RAND = sig
  type 'a t
  val pure : 'a -> 'a t
  val fail : 'a t
  val coin : float -> bool t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
end
```

- A value of type `'a t` represents a probabilistic program that
  produces a value of type `'a` if successful.
- The program `pure x` always succeeds with value `x`.
- The program `fail` always fails.
- The program `coin p` always succeeds; it yields `true` with probability \$p\$ and `false` with
    probability \$1-p\$.
- The program `(let*) e1 (fun x -> e2)` is a "probabilistic let binding."
  It first runs `e1` and binds the result to `x`; then, it runs `e2` with `x` in scope.
  OCaml's [binding operators](https://caml.inria.fr/pub/docs/manual-ocaml/bindingops.html) 
  let us write `(let*) e1 (fun x -> e2)` as `let* x = e1 in e2`.

A module that implements this signature corresponds to an interpretation of probabilistic 
programs. For example, the standard way to interpret probabilistic programs is to run them,
using the builtin `Random` module for random number generation:

```ocaml
module Execute : RAND = sig
  type 'a t = unit -> 'a
  let pure x = fun _ -> x
  exception Fail
  let fail = fun _ -> raise Fail
  let coin p = fun _ -> Random.float 1.0 <= p
  let ( let* ) x k = fun _ -> k (x ()) ()
end
```

We can implement an inferencer by giving an alternative interpretation to
probabilistic programs: rather than trying to compute a single result value, the inferencer tries to
compute an entire distribution.

To support inference, we need to add one more declaration to the `RAND` signature:

```ocaml
module Dist' : functor (A : Map.OrderedType) -> sig val f : A.t t -> float Map.Make(A).t end
```

The verbosity is due to a lack of typeclasses; in Haskell, this would be written
```hs
dist' :: Ord a => t a -> Map a Float
```

Given a probabilistic program of type `'a`, this function computes a discrete probability
distribution over its output values. 
The functor is there because the distribution is represented by a finite map, 
which requires that `'a` be comparable.

Given any implementation of this core signature, we can
implement the following extended signature:

```ocaml
module type RAND_EXT = sig
  include RAND
  val pdf : ('a -> 'a -> int) -> 'a t -> ('a -> float)
  val dist : ('a -> 'a -> int) -> 'a t -> ('a * float) list
  val guard : bool -> 'a t -> 'a t
end
```

- Given a probabilistic program of type `'a t`,
  `pdf` returns a probability density function `'a -> float`
  for easy log-time lookup. 
  The comparison function `'a -> 'a -> int` is needed to instantiate `Dist'` properly.
- Similarly, `dist` returns the distribution as a list of value-probability pairs,
    for easy iteration.
- `guard p m` is a probabilistic program which checks that `p` holds before continuing with `m`.
   It's easy to define:
    ```ocaml
    guard p m = if p then m else fail
    ```

The extension from `RAND` to `RAND_EXT` can be done once and for all, with a functor:

```ocaml
module RandExt (R : RAND) : RAND_EXT = struct .. end
```

Thanks to this, we never have to work directly with `Dist'`.
Now all we have to do is implement `RAND` in a way that performs inference.

## Monte Carlo simulation

The most basic inferencer just runs the given probabilistic program a bunch of 
times and uses the results of successful runs to estimate the distribution of output values:

```ocaml
module MonteCarlo (S : sig val samples : int end) : RAND = struct .. end
```

Just like in `Execute`,
we'll represent programs as thunks `unit -> 'a`:

```ocaml
type 'a t = unit -> 'a
```

The definitions for `pure`, `fail`, `coin`, and `let*` are identical 
to their standard interpretations:

```ocaml
let pure x = fun _ -> x
exception Fail
let fail = fun _ -> raise Fail
let coin p = fun _ -> Random.float 1.0 <= p
let ( let* ) x k = fun _ -> k (x ()) ()
```

The implementation of `Dist'` is a bit trickier. We have to write a function
`f` that takes in a probabilistic program `(m : A.t t)` and returns
a finite map from `A.t`s to `float`s:

```ocaml
module Dist' (A : Map.OrderedType) = struct
  module M = Map.Make(A)
  let f (m : A.t t) : float M.t = ..
end
```

The program `m` is represented by a thunk `unit -> A.t`.
When called, it will either yield a value of type `A.t` or raise
`Fail`.
We can write a function that repeatedly runs `m` until it succeeds with
a value of type `A.t`:

```ocaml
let rec sample m = try m () with Fail -> sample m in
```

Now we can run `sample m` repeatedly to collect `S.samples` samples
into a finite map `samples` which associates each `A.t` with the number of times
it was returned by `m ()`.
Then, normalizing each of the counts in `samples`
by the total number of samples yields
a finite map that associates each `A.t` to the frequency with which it 
occurred:

```ocaml
let rec go n samples =
  if n = 0 then samples else
  let inc = function
    | None -> Some 1
    | Some k -> Some (k + 1)
  in
  go (n - 1) (M.update (sample m) inc samples)
in
let samples = go S.samples M.empty in
M.map (fun p -> float_of_int p /. S.samples) samples
```

This inferencer isn't great: even for simple probabilistic programs,
it takes a large number of samples to converge on the true
distribution of output values.
For example, running the inferencer with 10000 samples
on the example program in the introduction yields the following distribution:
```ocaml
- : (bool * float) list = [(true, 0.492); (false, 0.508)]
```
It also has a major weakness: because the sampling function has to
keep retrying `m ()` until it successfully produces a result value,
it takes forever to collect a sufficiently large number of samples
if `m` doesn't succeed very often.

Here's an example: the following program
flips three fair coins and computes the number of heads:
```ocaml
let flip3 =
  let ind p = if p then 1 else 0 in
  let* c1 = coin 0.5 in
  let* c2 = coin 0.5 in
  let* c3 = coin 0.5 in
  pure (ind c1 + ind c2 + ind c3)
```
Running the inferencer on `flip3` with 10000 samples
yields a reasonable-looking distribution:
```ocaml
val - : (int * float) list = 
  [(0, 0.1311); (1, 0.3765); (2, 0.3704); (3, 0.122)]
```
(For reference, the true probabilities are 1/8, 3/8, 3/8, and 1/8 respectively.)

Now, here's a program that fails 99.99% of the time,
but behaves just like `flip3` when it succeeds:
```ocaml
let flip3' =
  let* b = coin 0.0001 in
  guard b flip3
```
This program should have the exact same distribution of output values as `flip3`.
However, it'll take 10000 times as long for our inferencer to figure that out, because
only one out of every 10000 runs is successful!

## Enumerating all possibilities

Instead of randomly sampling, we could run through every code path
of the program to analyze.

```ocaml
module NaiveEnum (S : sig val samples : int end) : RAND = struct .. end
```

This method works by interpreting a probabilistic program as
its distribution of output values, represented as a list of 
value-weight pairs:

```ocaml
type 'a t = ('a * float) list
```

The program `pure x` produces the value `x` with weight `1`:

```ocaml
let pure x = [(x, 1.0)]
```

The program `fail` never produces any values:

```ocaml
let fail = []
```

The program `coin p` produces `true` with weight `p` and `false` with weight
`1.0 -. p`:

```ocaml
let coin p = [(true, p); (false, 1.0 -. p)]
```

To interpret a let-binding `(let*) m k`:

- `m` is a list `[(x, p); ..]`.
- Apply `k` to each `x` in this list; this yields a nested structure of the form
  `[([(y, q); ..], p); ..]`.
- Multiply each nested `q` by its corresponding `p` to get
  `[[(y, q *. p); ..]; ..]`.
- Finally, flatten the nested lists to get `[(y, q *. p); ..]`.

In OCaml:
```ocaml
let ( let* ) xps k = 
  let ( let* ) x k = List.concat_map k x in
  let* (x, p) = xps in
  List.map (fun (y, q) -> (y, p *. q)) (k x)
```

To convert a list of weighted values into a distribution represented
as a finite map, simply fold over the list and add up weights.
Then, dividing by the sum of all the weights yields a proper probability 
distribution:

```ocaml
module Dist' (A : Map.OrderedType) = struct
  module M = Map.Make(A)
  let f (m : A.t t) : float M.t =
    let inc p = function
      | None -> Some p
      | Some q -> Some (p +. q)
    in
    let (total, samples) = 
      List.fold_left 
        (fun (total, samples) (x, p) -> 
          (total +. p, M.update x (inc p) samples))
        (0.0, M.empty) m 
    in
    M.map (fun p -> p /. total) samples
end
```

`NaiveEnum` produces much more accurate distributions than `MonteCarlo`.
In fact, it would produce exact
probabilities if we used exact arithmetic. Running it on the
example program in the introduction yields:
```ocaml
- : (bool * float) list =
  [(false, 0.500000000000000222); (true, 0.499999999999999722)]
```
Unlike random sampling, `NaiveEnum` works just as well
when the success probability is very low. For example,
it infers the following distribution for `flip3'` near-instantly:
```ocaml
- : (int * float) list =
  [(0, 0.124999999999999986); (1, 0.374999999999999944);
   (2, 0.374999999999999944); (3, 0.124999999999999986)]
```
This is because `NaiveEnum` considers every code path of the program
it analyzes, not just the paths that happen to be randomly sampled. 
So it doesn't matter how unlikely `flip3'` is to run `flip3`.

But `NaiveEnum` has lots of problems of its own.
Exhaustive analysis can easily lead to exponential blowups.
For example, `bin p n` is a binomial random variable
\$n\$ trials and success probability \$p\$:
```ocaml
let bin p n =
  let rec go n acc =
    if n = 0 then pure acc else
    let* b = coin p in
    go (n - 1) (if b then acc + 1 else acc)
  in go n 0
```

We can use `MonteCarlo` to estimate `bin 0.5 20` just fine, albeit very roughly:

```ocaml
- : (int * float) list =
  [(1, 3e-05); (2, 0.00019); (3, 0.00096); (4, 0.00477); (5, 0.01543);
   (6, 0.03737); (7, 0.07254); (8, 0.12179); (9, 0.16057); (10, 0.17396);
   (11, 0.15959); (12, 0.1207); (13, 0.07392); (14, 0.03716); (15, 0.01518);
   (16, 0.00432); (17, 0.00126); (18, 0.00023); (19, 2e-05); (20, 1e-05)]
```

But using `NaiveEnum` to estimate `bin 0.5 20` will just produce a stack overflow.
This is because `bin 0.5 20` performs \$20\$ coin flips, and so has
\$2^{20}\$ code paths; `NaiveEnum` tries to construct an enormous list
with one entry for each such path, and overflows the stack while doing so.

`NaiveEnum` also can't handle unbounded random variables.
For example, `geo p` is a geometric random variable with success probability `p`:
```ocaml
let geo p =
  let rec go n =
    let* b = coin p in
    if b then pure n else go (n + 1)
  in go 0
```

Once again, `MonteCarlo` can estimate `geo 0.5` just fine:

```ocaml
- : (int * float) list =
  [(0, 0.5034); (1, 0.2524); (2, 0.1258); (3, 0.0561); (4, 0.0309);
   (5, 0.0158); (6, 0.0077); (7, 0.0033); (8, 0.0024); (9, 0.0011);
   (10, 0.0005); (11, 0.0004); (14, 0.0002)]
```

`NaiveEnum` overflows the stack because `geo 0.5` has an unbounded number of 
code paths.

Finally, `NaiveEnum` produces many intermediate lists; these can take up
an enormous amount of space if the branching tree of possibilities is large.

## Removing intermediate lists


