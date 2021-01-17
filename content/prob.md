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
Rather than reading them, I decided to roll my own inferencer and try it out on some 
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
  type 'a t = 'a
  let pure x = x
  exception Fail
  let fail = raise Fail
  let coin p = Random.float 1.0 <= p
  let ( let* ) x k = k x
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

Thanks to this, we never have to work directly with `Dist'`.
The extension from `RAND` to `RAND_EXT` can be done once and for all, with a functor:

```ocaml
module RandExt (R : RAND) : RAND_EXT = struct .. end
```

Now all we have to do is implement `RAND` in a way that performs inference.

## Monte Carlo simulation

The most basic inferencer just runs the given probabilistic program a bunch of 
times and uses the results of successful runs to estimate the distribution of output values:

```ocaml
module MonteCarlo (S : sig val samples : int end) : RAND = struct .. end
```

Since this method needs to run the same program many times over,
we'll represent such programs as thunks `unit -> 'a`:

```ocaml
type 'a t = unit -> 'a
```

The definitions for `pure`, `fail`, `coin`, and `let*` are almost identical 
to their standard interpretations, just with some extra lambdas and `()`s in certain places:

```ocaml
let pure x = fun _ -> x
let ( let* ) m k = fun _ -> k (m ()) ()
exception Fail
let fail = fun _ -> raise Fail
let coin p = fun _ -> Random.float 1.0 <= p
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
it was returned by `m ()`:

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

Finally, normalizing each of the counts in `samples`
by the total number of samples yields
a finite map that associates each `A.t` to the frequency with which it 
occurred.

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


