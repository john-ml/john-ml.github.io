---
layout: post
---

### Basic syntax / terms

| APL                                                       | Haskell                               |
|-----------------------------------------------------------|---------------------------------------| 
| monadic                                                   | unary                                 |
| dyadic                                                    | binary                                |
| niladic                                                   | nullary                               |
| function                                                  | first-order function                  |
| operator                                                  | higher-order function                 |
| `f x ..` where `f` is a unary function                    | `f [x, ..]`                           |
| `x .. f y ..` where `f` is a binary function              | ``[x, ..] `f` [y, ..]``               |
| `g f` where `f` is a monadic operator                     | `f g`                                 |
| `g f h` where `f` is dyadic operator                      | `f g h`                               |

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
| `{M:N ⋄ .. ⋄ P}`                                          | `\ .. -> if M then N else .. else -> P` |
| `{C[∇]}`                                                  | `fix \ go .. -> C[go]`                |
| `f∘g` where `f`, `g` monadic                              | `f . g`                               |
| `f∘g` where `f` monadic and `g` dyadic                    | `\ x y -> f (g x y)` aka `(f .) . g`  |
| `f∘g` where `f` dyadic and `g` monadic                    | `\ x y -> f x (g y)` aka `(. g) . f`  |
| `x∘f` where `f` dyadic and `x` value                      | ``(x `f`)``                           |
| `f∘x` where `f` dyadic and `x` value                      | ``(`f` x)``                           |
| `f⍨ x`                                                    | `\ x -> f x x` aka `join f x`         |
| `x f⍨ y`                                                  | `f y x`                               |
| `(f⍣n) x` where `f` monadic and `n` is a natural number   | `iterate f x !! n`                    |
| `(f⍣¯n) x` where `f` monadic with inverse `g`[^2] and `n` is a natural number | `iterate g x !! n` |
| `(f⍣g) x` aka "apply `f` until `g`"                       | `snd $ until (uncurry g) (\ (_, y) -> (y, f y)) (y, f y)` |
| In general, `x (f⍣z) y` = `((x∘f)⍣z) y`.                  |                                       |

### Array operations

| APL                                                       | Haskell                               |
|-----------------------------------------------------------|---------------------------------------| 
| `⍬`                                                       | `[]`                                  |
| `f/`                                                      | `foldr1 f`                            |
| `f\`                                                      | `map (foldr1 f) . tail . inits`       |
| `f¨`                                                      | `map f`                               |

[^1]: `C[x,y,..]` denotes an expression containing the subexpressions `x`, `y`, etc.
[^2]: A function is invertible if it's an invertible primitive
        (`+`, `-`, `×`, `/`, etc. given the proper domain restrictions)
        or an expression built out of invertible functions using operators
        `∘`, `¯`, `∘.`, `⍨`, `\`, `[n]`, and `⍣`. User-defined functions aren't invertible.
