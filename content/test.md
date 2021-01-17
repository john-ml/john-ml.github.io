---
header-includes: |
  <link rel="stylesheet" type="text/css" href="css/main.css" />
  <script type="text/javascript" async
    src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.7/MathJax.js?config=TeX-MML-AM_CHTML">
  </script>
---

# Test

some text

```hs
f x = let y = x + x in do y
```

*a* _*_ **a**

a `bc` d

[test link](link.html)

Inline math (MathJax not required): $a + b = c/d$. Aligned math (MathJax required):
$$
\newcommand{\testcommand}{1+2}
\begin{align*}
  (x+1)^2 
    &= (x+1)(x+1) \\
    &= x(x+1) + 1(x+1) \\
    &= (x^2+x)+(x+1) \\
    &= x^2 + 2x + 1
\end{align*}\\
\testcommand
$$

```coq
Definition x := let y := x + x in match y with y*y end.
```
and
```ocaml
Definition x := let y := x + x in match y with y*y end.
```
and
```hs
Definition x := let y := x + x in match y with y*y end.
```
and
```agda
Definition x := let y := x + x in match y with y*y end.
```
and
```ocaml
Definition x := let y := x + x in match y with y*y end.
```

```ocaml
let rec count n =
  match n with
  | 0 -> []
  | 1 -> [n]
  | n -> n :: count (n - 1) asldfjk asldfj asldfj asldf jaslkdf jlasdfj alskd fjalsdf jalsdfj alsdfj aklsdj falks dfjalk jdfalsk fdjalksdf jakld fjlaksdf jalkfdj alksd f
```

