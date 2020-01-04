---
layout: post
---

### Basic syntax / terms

| APL                                                         | Haskell                               |
|-------------------------------------------------------------|---------------------------------------| 
| monadic                                                     | unary                                 |
| dyadic                                                      | binary                                |
| niladic                                                     | nullary                               |
| function                                                    | first-order function                  |
| operator                                                    | higher-order function                 |
| `f x ..` where `f` monadic function                         | `f [x, ..]`                           |
| `x .. f y ..` where `f` dyadic function                     | `f [x, ..] [y, ..]`                   |
| `g f` where `f` monadic operator                            | `f g`                                 |
| `g f h` where `f` dyadic operator                           | `f g h`                               |
| `(g f h) x` where `f` dyadic function                       | `f (g x) (h x)` aka `liftA2 f g h x`  |
| `(f g) x` where `f`, `g` monadic functions                  | `f (g x)` aka `(f . g) x`             |
| `x (f g) y` where `f` monadic function, `g` dyadic function<br>Unlike `∘`, this is completely unambiguous.<br>There's no overload for `f` dyadic, `g` monadic. | `f (g x y)` aka `((f .) . g) x y`     |

### Lambdas, function composition, and HOFs

| APL                                                       | Haskell                               |
|-----------------------------------------------------------|---------------------------------------| 
| `{C[⍵]} x`[^1]                                            | `C[x]`                                |
| `x {C[⍺,⍵]} y`                                            | `C[x,y]`                              |
| `f{C[⍺⍺,⍵]} x`                                            | `C[f,x]`                              |
| `x f{C[⍺⍺,⍺,⍵]} y`                                        | `C[f,x,y]`                            |
| `f{C[⍺⍺,⍵⍵,⍵]}g x`                                        | `C[f,g,x]`                            |
| `x f{C[⍺⍺,⍵⍵,⍺,⍵]}g y`                                    | `C[f,g,x,y]`                          |
| `{x←M ⋄ N}`                                               | `\ .. -> let x = M in N`              |
| `{M:N ⋄ .. ⋄ P}`                                          | `\ .. -> if M then N else .. else P`  |
| `{C[∇]}`                                                  | `fix \ go .. -> C[go]`                |
| `f∘g` where `f`, `g` monadic functions                    | `f . g`                               |
| `f∘g` where `f` monadic, `g` dyadic functions  | `\ x y -> f (g x y)` aka `(f .) . g`  |
| `f∘g` where `f` dyadic, `g` monadic functions<br>When faced with ambiguity with previous (e.g. `÷∘-`), defaults to this one.<br>Probably because `f g` can be used to explicitly specify the other one if needed. | `\ x y -> f x (g y)` aka `(. g) . f`  |
| `x∘f` where `f` dyadic function and `x` value             | ``(x `f`)``                           |
| `f∘x` where `f` dyadic function and `x` value             | ``(`f` x)``                           |
| `f⍨ x`                                                    | `f x x` aka `join f x`                |
| `x f⍨ y`                                                  | `f y x`                               |
| `(f⍣n) x` where `f` monadic function and `n` natural number | `iterate f x !! n`                    |
| `(f⍣¯n) x` where `f` monadic function with inverse `g`[^2] and `n` natural number | `iterate g x !! n` |
| `(f⍣g) x` aka "apply `f` until `g`"                       | `snd $ until (uncurry g) (\ (_, y) -> (y, f y)) (y, f y)` |
| `x (f⍣z) y` = `((x∘f)⍣z) y`                               |                                       |

### Array operations

| APL                                                       | Haskell                               |
|-----------------------------------------------------------|---------------------------------------| 
| `⍬`                                                       | `[]`                                  |
| `⍳n` where `n` natural number                             | `[1..n]`                              |
| `⍴A` where `A` matrix                                     | `shape A`                             |
| `v⍴A` where `v` nat vector, `A` matrix                    | `reshape v (cycle (flatten A))`       |
| `⌽A` where `A` matrix                                     | `reverseRows A`                       |
| `⊖A` where `A` matrix                                     | `reverseCols A`                       |
| `⍉A` where `A` matrix                                     | `transpose A`                         |
| `f/`                                                      | `foldr1 f`                            |
| `f\`                                                      | `map (foldr1 f) . tail . inits`       |
| `f¨`                                                      | `map f`                               |

[^1]: `C[x,y,..]` denotes an expression containing the subexpressions `x`, `y`, etc.
[^2]: A function is invertible if it's an invertible primitive
        (`+`, `-`, `×`, `/`, etc. given the proper domain restrictions)
        or an expression built out of invertible functions using operators
        `∘`, `¯`, `∘.`, `⍨`, `\`, `[n]`, and `⍣`. User-defined functions aren't invertible.
