# Test link page

```coq
Definition comp {A B C} (f : B -> C) (g : A -> B) : A -> C :=
  fun x => f (g x).
```

