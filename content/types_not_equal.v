(** printing forall %\forall% #∀# *)
(** printing exists %\exists% #∃# *)
(** printing fun %\lambda% #λ# *)
(** printing True %\top% #⊤# *)
(** printing False %\bot% #⊥# *)

(** * When are Coq types provably unequal? *)

(** When I first started learning Coq, I expected it
    to be strictly more expressive than
    languages with "dependent types at home" (e.g. GADTs, type families, ..). 
    But it's actually pretty difficult to translate code using things
    like GADTs into Coq, and it seems to be because other languages
    bake a number of extra rules about type inequality into the type checker.

    For example, OCaml accepts the following code without complaining about non-exhaustive 
    pattern matching:

      #<pre>
  type 'a t
    = C1 : int t
    | C2 : bool t
  let f (x : int t) : unit =
    match x with
    | C1 -> ()</pre>#

    To do so, it has to reason that the [C2] case is impossible because [int] is not equal
    to [bool].
    (Since #<a href="https://www.math.nagoya-u.ac.jp/~garrigue/papers/gadtspm.pdf">exhaustiveness 
    checking is undecidable for GADTs</a>#, it's possible that the OCaml compiler just gave up
    on trying to analyze the match expression. But that's unlikely, because it does 
    complain about exhaustivity if I add an extra constructor [C3 : int t].)

    The seemingly obvious fact that [nat] is not the same as [bool] is not obvious to Coq:
*)

Inductive T : Set -> Type :=
| C1 : T nat
| C2 : T bool.

(* begin show *)
Fail Definition failure (x : T nat) : unit :=
  match x with
  | C1 => tt
  end.
(* end show *)

(** ⟹ #<pre>
  The command has indeed failed with message: 
  Non exhaustive pattern-matching: no clause found for pattern C2</pre># 

  If we could prove [bool <>  nat], some dependent pattern matching can prove that [C2] is impossible:
*)

Definition success (H : bool <> nat) (x : T nat) : unit :=
  match x in T A return A = nat -> unit with
  | C1 => fun _ => tt
  | C2 => fun Heq : bool = nat => match H Heq with end
  end eq_refl.

(** But how to prove two types unequal?
    The usual tactics for proving things unequal
    ([discriminate], [inversion], etc.) don't work because
    [nat] and [bool] aren't constructors.

    Some metatheory handwaving suggests that proving two types unequal will be
    impossible for most practical situations.
    If we could prove [A <> B] for isomorphic [A] and [B],
    then univalence wouldn't be independent of CiC.
    So we should expect to be able to prove [A <> B]
    only when [A] and [B] aren't isomorphic.
    This is pretty bad: most data types in functional
    programming are trees of some kind or other, which are all
    isomorphic to each other (they all have a countable number of
    inhabitants).

    But, let's try to prove whatever we can anyway.
    We'll say a type [A] is less than or equal to [B] if
    there exists an injection [f : A -> B]: *)

Definition injective {A B} (f : A -> B) := forall x y, f x = f y -> x = y.

Definition leq A B := exists f : A -> B, injective f.
Infix "⊑" := leq (at level 70, no associativity).

Lemma leq_refl {A} : A ⊑ A. Proof. exists (fun x =>  x); firstorder. Qed.

(** [A] is strictly smaller than [B] if there's no injection [f : B -> A]: *)

Definition lt A B := ~ B ⊑ A.
Infix "⋤" := lt (at level 70, no associativity).

(** Two types are isomorphic if they're less than or equal to each other: *)

Definition iso A B := A ⊑ B /\ B ⊑ A.
Infix "≅" := iso (at level 70, no associativity).
Notation "a '≇' b" := (~ (a ≅ b)) (at level 70, no associativity).

Lemma iso_refl {A} : A ≅ A. Proof. split; apply leq_refl. Qed.

(* begin show *)
Polymorphic Lemma iso_ne {A B} : A ≇ B -> A <> B.
(* end show *)
Proof. intros Hnot Heq; subst; apply Hnot, iso_refl. Qed.

(* begin show *)
(** This is already enough to prove [nat <> bool]:
    [nat] and [bool] can't be isomorphic because [bool] has two inhabitants
    while [nat] has countably many. *)

Lemma nat_ne_bool : nat <> bool.
Proof.
  apply iso_ne; intros [[f Hfg] [g Hgf]].
  (** #<pre>
  f : nat -> bool
  Hfg : injective f
  g : bool -> nat
  Hgf : injective g
  ============================
  False</pre># 

  Since [f] returns [bool], [[f 0, f 1, f 2]] must contain a duplicate. *)
  pose proof Hfg 0 1 as H0.
  pose proof Hfg 1 2 as H1.
  pose proof Hfg 0 2 as H2.
  destruct (f 0), (f 1), (f 2); firstorder congruence.
Qed.
(* end show *)

(** It'd be nice to automate this kind of reasoning for more complicated types.
    First, some lemmas to make [(⊑)] and [(≅)] easier to work with: *)

Require Coq.Logic.ChoiceFacts Coq.Logic.ClassicalFacts.
Axiom FChoice : Coq.Logic.ChoiceFacts.FunctionalChoice.
Axiom LEM : Coq.Logic.ClassicalFacts.excluded_middle.
Require Import Coq.Logic.FunctionalExtensionality.

Definition surjective {A B} (f : A -> B) := forall y, exists x, f x = y.

Definition inhabited A := exists x : A, True.

Definition comp {A B C} (f : B -> C) (g : A -> B) := fun x => f (g x).
(* begin hide *)

Definition sur_inj {A B} (f : A -> B) :
  surjective f ->
  exists g : B -> A, injective g /\ forall x, f (g x) = x.
Proof.
  intros Hsur.
  destruct (FChoice B A _ Hsur) as [g Hg]; exists g; split; auto.
  intros x y Heq.
  rewrite <- (Hg x), <- (Hg y).
  now f_equal.
Qed.

Definition inj_sur {A B} (f : A -> B) :
  injective f -> inhabited A ->
  exists g : B -> A, surjective g.
Proof.
  intros Hinj [arbitrary_A _].
  enough (exists g, forall x, g (f x) = x) by firstorder.
  enough (exists g, forall y, forall x, y = f x -> g y = x) by firstorder.
  apply (FChoice B A (fun y gy => forall x : A, y = f x -> gy = x)).
  intros y.
  destruct (LEM (exists x, f x = y)) as [[x Hxy]|Hnx].
  2:{ exists arbitrary_A; assert (forall x, f x <> y) by firstorder. congruence. }
  exists x; intros x' Hx'y; apply Hinj; congruence.
Qed.

Lemma inj_comp {A B C} (f : B -> C) (g : A -> B) :
  injective f -> injective g -> injective (comp f g).
Proof. firstorder. Qed.

Lemma sur_ump {A B C} (f : A -> B) :
  surjective f ->
  forall g h : B -> C, comp g f = comp h f -> g = h.
Proof.
  intros Hsur g h Heq.
  apply functional_extensionality; intros x.
  destruct (Hsur x) as [y Hxy]; subst x.
  change (?f (?g y)) with (comp f g y); congruence.
Qed.

Lemma inj_ump {A B C} (f : B -> C) :
  injective f ->
  injective (@comp A B C f).
Proof.
  intros Hinj g h Heq.
  apply functional_extensionality; intros x.
  assert (Hcomp : comp f g x = comp f h x) by congruence.
  now apply Hinj.
Qed.

(* end hide *)
Require Import Morphisms Setoid.

Lemma leq_asym {A B} : A ⊑ B -> B ⊑ A -> A ≅ B. Proof. firstorder. Qed.
Lemma leq_trans {A B C} : A ⊑ B -> B ⊑ C -> A ⊑ C.
Proof. intros [f Hf] [g Hg]; exists (comp g f); now apply inj_comp. Qed.
Lemma leq_False {A} : False ⊑ A. Proof. unshelve eexists; [intros []|]; intros []. Qed.
Lemma leq_sum1 {A B C} : A ⊑ B -> A + C ⊑ B + C.
Proof.
  intros [f Hf]; exists (fun xy => match xy with inl x => inl (f x) | inr y => inr y end).
  intros [x|y] [x'|y']; try congruence.
  intros; assert (Hfx_eq : f x = f x') by congruence.
  apply Hf in Hfx_eq; congruence.
Qed.
Lemma leq_sum2 {A B C} : B ⊑ C -> A + B ⊑ A + C.
Proof.
  intros [f Hf]; exists (fun xy => match xy with inl x => inl x | inr y => inr (f y) end).
  intros [x|y] [x'|y']; try congruence.
  intros; assert (Hfx_eq : f y = f y') by congruence.
  apply Hf in Hfx_eq; congruence.
Qed.
Lemma leq_prod1 {A B C} : A ⊑ B -> A * C ⊑ B * C.
Proof.
  intros [f Hf]; exists (fun '(x, y) => (f x, y)).
  intros [x y] [x' y']; try congruence.
  intros; assert (Hfx_eq : f x = f x') by congruence.
  apply Hf in Hfx_eq; congruence.
Qed.
Lemma leq_prod2 {A B C} : B ⊑ C -> A * B ⊑ A * C.
Proof.
  intros [f Hf]; exists (fun '(x, y) => (x, f y)).
  intros [x y] [x' y']; try congruence.
  intros; assert (Hfx_eq : f y = f y') by congruence.
  apply Hf in Hfx_eq; congruence.
Qed.
Lemma leq_fn1 {A B C} : inhabited A -> A ⊑ B -> (A -> C) ⊑ (B -> C).
Proof.
  intros HA [f Hf].
  destruct (inj_sur f Hf HA) as [f' Hf'].
  exists (fun h => comp h f').
  intros h1 h2 Heq; eapply sur_ump; eauto.
Qed.
Lemma leq_fn2 {A B C} : B ⊑ C -> (A -> B) ⊑ (A -> C).
Proof. intros [f Hf]; exists (comp f); intros h1 h2 Heq; eapply inj_ump; eauto. Qed.

Lemma iso_sym {A B} : A ≅ B -> B ≅ A. Proof. firstorder. Qed.
Lemma iso_trans {A B C} : A ≅ B -> B ≅ C -> A ≅ C.
Proof.
  intros [[f1 Hf1] [g1 Hg1]] [[f2 Hf2] [g2 Hg2]].
  split; [exists (comp f2 f1)|exists (comp g1 g2)]; firstorder.
Qed.

Add Parametric Relation : Type iso
  reflexivity proved by @iso_refl
  symmetry proved by @iso_sym
  transitivity proved by @iso_trans
  as iso_rel.

Lemma iso_fn1 {A B C} : inhabited A -> A ≅ B -> (A -> C) ≅ (B -> C).
Proof.
  intros HA [[f Hf] [g Hg]].
  assert (HB : inhabited B) by (destruct HA as [arbA _]; now exists (f arbA)).
  destruct (inj_sur f Hf HA) as [f' Hf'].
  destruct (inj_sur g Hg HB) as [g' Hg'].
  split; [exists (fun h => comp h f')|exists (fun h => comp h g')];
  intros h1 h2 Heq; eapply sur_ump; eauto.
Qed.

Add Parametric Morphism : (fun A B => A -> B) with
  signature eq ==> iso ==> iso as iso_fn2.
Proof.
  intros x y y' [[f Hf] [g Hg]].
  split; [exists (comp f)|exists (comp g)]; intros h1 h2 Heq; eapply inj_ump; eauto.
Qed.

Add Parametric Morphism : @sum with
  signature iso ==> iso ==> iso as iso_sum.
Proof.
  intros A A' [[fA HfA] [gA HgA]] B B' [[fB HfB] [gB HgB]].
  split;
    [exists (fun x => match x with inl x => inl (fA x) | inr y => inr (fB y) end)
    |exists (fun x => match x with inl x => inl (gA x) | inr y => inr (gB y) end)];
  intros [x1|y1] [x2|y2] Heq; inversion Heq; subst; f_equal;
  try now (apply HfA + apply HfB + apply HgA + apply HgB).
Qed.

Add Parametric Morphism : @prod with
  signature iso ==> iso ==> iso as iso_prod.
Proof.
  intros A A' [[fA HfA] [gA HgA]] B B' [[fB HfB] [gB HgB]].
  split; [exists (fun '(x, y) => (fA x, fB y))|exists (fun '(x, y) => (gA x, gB y))];
  intros [x1 y1] [x2 y2] Heq; inversion Heq; subst; f_equal;
  try now (apply HfA + apply HfB + apply HgA + apply HgB).
Qed.

(** Next, a bunch of standard isomorphisms: *)

Lemma unit_True : unit ≅ True.
Proof. split; [exists (fun _ => I)|exists (fun _ => tt)]; now intros [] []. Qed.
Lemma sum_False {A} : False + A ≅ A.
Proof.
  split; [unshelve eexists; [intros [[]|x]; exact x|]|exists inr].
  - intros [[]|x] [[]|y]; congruence.
  - congruence.
Qed.
Lemma sum_comm {A B} : A + B ≅ B + A.
Proof.
  split;
    [exists (fun x => match x with inl x => inr x | inr x => inl x end)
    |exists (fun x => match x with inl x => inr x | inr x => inl x end)];
  intros [x|y] [z|w]; congruence.
Qed.
Lemma sum_assoc {A B C} : (A + B) + C ≅ A + (B + C).
Proof.
  split;
    [exists (fun x =>
       match x with
       | inl (inl x) => inl x
       | inl (inr x) => inr (inl x)
       | inr x => inr (inr x)
       end)
    |exists (fun x =>
          match x with
          | inl x => inl (inl x)
          | inr (inl x) => inl (inr x)
          | inr (inr x) => inr x
          end)];
  [intros [[?|?]|?] [[?|?]|?]|intros [?|[?|?]] [?|[?|?]]]; congruence.
Qed.
Lemma prod_False {A} : False * A ≅ False.
Proof.
  split; [unshelve eexists; [intros [[] _]|]|unshelve eexists; [intros []|]];
  [intros [[] _]|intros []].
Qed.
Lemma prod_True {A} : True * A ≅ A.
Proof.
  split; [exists snd|exists (fun x => (I, x))]; [intros [[] x] [[] y]|]; cbn; congruence.
Qed.
Lemma prod_comm {A B} : A * B ≅ B * A.
Proof.
  split; [exists (fun '(x, y) => (y, x))|exists (fun '(x, y) => (y, x))]; intros [x y] [z w]; congruence.
Qed.
Lemma prod_assoc {A B C} : (A * B) * C ≅ A * (B * C).
Proof.
  split;
    [exists (fun '((x, y), z) => (x, (y, z)))
    |exists (fun '(x, (y, z)) => ((x, y), z))];
  [intros [[??]?] [[??]?]|intros [?[??]] [?[??]]]; congruence.
Qed.
Lemma prod_sum_distr {A B C} : A * (B + C) ≅ A * B + A * C.
Proof.
  split;
    [exists (fun '(x, yz) => match yz with inl y => inl (x, y) | inr z => inr (x, z) end)
    |exists (fun xyxz => match xyxz with inl (x, y) => (x, inl y) | inr (x, z) => (x, inr z) end)];
  [intros [?[?|?]] [?[?|?]]|intros [[??]|[??]] [[??]|[??]]]; congruence.
Qed.
Lemma fun_False {A} : (False -> A) ≅ True.
Proof.
  split; [exists (fun _ => I)|exists (fun _ HF => False_rect _ HF)]; [intros f g _|intros [] []; auto].
  apply functional_extensionality; intros [].
Qed.
Lemma fun_True {A} : (True -> A) ≅ A.
Proof.
  split; [exists (fun f => f I)|exists (fun x _ => x)]; [intros f g Heq|intros x y Heq].
  - apply functional_extensionality; now intros [].
  - change (x = y) with ((fun _ => x) I = (fun _ => y) I); now rewrite Heq.
Qed.
Lemma fun_uncurry {A B C} : (A -> B -> C) ≅ (A * B -> C).
Proof.
  split; [exists (fun f '(x, y) => f x y)|exists (fun f x y => f (x, y))];
  intros f g Heq; apply functional_extensionality.
  - intros x; apply functional_extensionality; intros y.
    change (?f x y) with ((fun '(x, y) => f x y) (x, y)).
    now rewrite Heq.
  - intros [x y]; change (?f (x, y)) with ((fun x y => f (x, y)) x y).
    now rewrite Heq.
Qed.
Lemma fun_sum_distr {A B C} : (A + B -> C) ≅ (A -> C) * (B -> C).
Proof.
  split;
    [exists (fun f => (comp f inl, comp f inr))
    |exists (fun '(f, g) => fun xy => match xy with inl x => f x | inr y => g y end)].
  - intros f g Heq; inversion Heq.
    apply functional_extensionality; intros [x|y];
    change (?f (?g ?x) = ?h (?k ?y)) with (comp f g x = comp h k y); congruence.
  - intros [f1 g1] [f2 g2] Heq; f_equal; apply functional_extensionality; intros x.
    + match type of Heq with
      | ?f = ?g =>
        change (f1 x) with (f (inl x));
        change (f2 x) with (g (inl x))
      end; now rewrite Heq.
    + match type of Heq with
      | ?f = ?g =>
        change (g1 x) with (f (inr x));
        change (g2 x) with (g (inr x))
      end; now rewrite Heq.
Qed.

(** A type is finite if it has exactly [n] inhabitants for some [n : nat]. *)

Definition fin n : Type := Nat.iter n (sum True) False.
Definition finite A := exists n, A ≅ fin n.

Lemma fin_False : False ≅ fin 0. Proof. apply iso_refl. Qed.
Lemma fin_True : True ≅ fin 1. Proof. cbn; now rewrite sum_comm, sum_False. Qed.
Lemma fin_bool : bool ≅ fin 2.
Proof.
  split;
    [exists (fun b : bool => if b then inl I else inr (inl I))
    |exists (fun x =>
          match x with
          | inl _ => true
          | inr (inl _) => false
          | inr (inr x) => False_rect _ x
          end)].
  - intros [] []; congruence.
  - intros [[]|[[]|[]]] [[]|[[]|[]]]; congruence.
Qed.
Lemma fin_sum {m n} : fin m + fin n ≅ fin (m + n).
Proof.
  induction m as [|m IHm]; cbn; [now rewrite sum_False|].
  rewrite sum_assoc; apply iso_sum; now auto.
Qed.
Lemma fin_prod {m n} : fin m * fin n ≅ fin (m * n).
Proof.
  induction m as [|m IHm]; cbn; [apply prod_False|].
  rewrite prod_comm, prod_sum_distr.
  eapply iso_trans; [|apply fin_sum].
  apply iso_sum; [|rewrite prod_comm; auto].
  now rewrite prod_comm, prod_True.
Qed.
Lemma fin_fun {m n} : (fin m -> fin n) ≅ fin (Nat.pow n m).
Proof.
  induction m as [|m IHm]; cbn.
  - rewrite sum_comm, sum_False; apply fun_False.
  - rewrite fun_sum_distr, <- fin_prod.
    apply iso_prod; [|easy].
    apply fun_True.
Qed.

Require Import Lia.
Lemma nat_fin_sum {n} : fin n + nat ≅ nat.
Proof.
  induction n; cbn; [now rewrite sum_False|].
  rewrite sum_assoc.
  eapply iso_trans; [apply iso_sum; [reflexivity|apply IHn]|]; clear.
  split; [exists (fun xn => match xn with inl _ => 0 | inr n => S n end)|exists inr];
  [intros [[]|m] [[]|n]|intros m n]; congruence.
Qed.
(* begin hide *)
Fixpoint halve n :=
  match n with
  | 0 | 1 => 0
  | S (S n) => S (halve n)
  end.
Lemma halve_spec : 
  forall m, if Nat.even m then exists n, m = 2*halve n else exists n, m = 2*halve n+1.
Proof.
  fix go 1; intros [|[|m]]; [exists 0; auto..|].
  specialize (go m); cbn; destruct (Nat.even m);
  destruct go as [n Hn]; exists (S (S n)); cbn; lia.
Qed.
Lemma halve_cancel n : halve (2*n) = n.
Proof.
  induction n; [easy|].
  replace (2 * S n) with (S (S (2 * n))) by lia.
  cbn; replace (n + (n + 0)) with (2 * n) by lia.
  lia.
Qed.
Lemma halve_cancel1 n : halve (2*n + 1) = n.
Proof.
  induction n; [easy|].
  replace (2 * S n) with (S (S (2 * n))) by lia.
  cbn; replace (n + (n + 0)) with (2 * n) by lia.
  lia.
Qed.
(* end hide *)
Lemma nat_fin_prod {n} : fin (S n) * nat ≅ nat.
Proof.
  Fail induction n; cbn; [rewrite sum_comm|]. (* TODO: why setoid failures? *)
  induction n; cbn.
  - eapply iso_trans; [apply iso_prod; [rewrite sum_comm, sum_False|]; apply iso_refl|].
    now rewrite prod_True.
  - change (True + fin n)%type with (fin (S n)).
    rewrite prod_comm, prod_sum_distr.
    eapply iso_trans; [apply iso_sum; [rewrite prod_comm, prod_True; apply iso_refl|apply prod_comm]|].
    eapply iso_trans; [apply iso_sum; [apply iso_refl|apply IHn]|].
    clear.
    split;
      [exists (fun mn => match mn with inl m => 2*m | inr m => 2*m + 1 end)
      |exists (fun m => if Nat.even m then inl (halve m) else inr (halve m))];
      [intros [?|?] [?|?] Heq; try congruence; try lia; f_equal; lia|].
    intros m n.
    pose proof halve_spec m as Hevenbm.
    pose proof halve_spec n as Hevenbn.
    destruct (Nat.even m); destruct Hevenbm as [km Hkm];
    destruct (Nat.even n); destruct Hevenbn as [kn Hkn]; try congruence.
    + subst; rewrite !halve_cancel; congruence.
    + subst; rewrite !halve_cancel1; congruence.
Qed.
(* begin hide *)
Lemma pow3div2 n : ~ PeanoNat.Nat.divide 2 (Nat.pow 3 n).
Proof.
  induction n.
  - cbn; intros [k Hk]; lia.
  - replace (Nat.pow 3 (S n)) with (3 * Nat.pow 3 n) by (cbn; lia).
    intros Hdiv; apply PeanoNat.Nat.gauss in Hdiv; auto.
Qed.
Lemma halving_iter m n p :
  m <= n -> Nat.iter m halve (Nat.pow 2 n * p) = Nat.pow 2 (n - m) * p.
Proof.
  induction m as [|m IHm]; intros Hle.
  - replace (n - 0) with n by lia. auto.
  - simpl; rewrite IHm by lia.
    destruct n as [|n]; [lia|].
    replace (S n - m) with (S (n - m)) by lia.
    replace (Nat.pow 2 (S (n - m))) with (2 * Nat.pow 2 (n - m)) by (cbn; lia).
    now rewrite <- PeanoNat.Nat.mul_assoc, halve_cancel.
Qed.
Lemma halving_unequal_lt m n p q :
  m < n ->
  Nat.iter m halve (Nat.pow 2 m * Nat.pow 3 p) <> Nat.iter m halve (Nat.pow 2 n * Nat.pow 3 q).
Proof.
  intros Hlt Heq.
  rewrite !halving_iter in Heq by lia.
  replace (m - m) with 0 in Heq by lia.
  apply (pow3div2 p).
  replace (Nat.pow 3 p) with (Nat.pow 2 (n - m) * Nat.pow 3 q) by (cbn in *; lia).
  assert (n - m > 0) by lia.
  destruct (n - m) as [|k]; [lia|].
  replace (Nat.pow 2 (S k)) with (2 * Nat.pow 2 k) by (cbn; lia).
  apply PeanoNat.Nat.divide_mul_l, PeanoNat.Nat.divide_factor_l.
Qed.
Lemma halving_eq1 m n p q :
  Nat.iter (min m n) halve (Nat.pow 2 m * Nat.pow 3 p)
  = Nat.iter (min m n) halve (Nat.pow 2 n * Nat.pow 3 q) ->
  m = n.
Proof.
  intros Heq; destruct (PeanoNat.Nat.eq_dec m n) as [Hmn_eq|Hmn_ne]; auto.
  assert (Hlt : m < n \/ n < m) by lia.
  destruct Hlt as [Hlt|Hlt].
  - exfalso. apply (halving_unequal_lt m n p q); eauto.
    now replace (Nat.min m n) with m in * by lia.
  - exfalso. symmetry in Heq. apply (halving_unequal_lt n m q p); eauto.
    now replace (Nat.min m n) with n in * by lia.
Qed.
Lemma halving_eq2 m n : Nat.pow 3 m = Nat.pow 3 n -> m = n.
Proof.
  revert n; induction m; destruct n; auto; try solve [simpl in *; lia].
  intros Heq; f_equal; apply (IHm n).
  replace (Nat.pow 3 (S m)) with (3 * Nat.pow 3 m) in Heq by (cbn; lia).
  replace (Nat.pow 3 (S n)) with (3 * Nat.pow 3 n) in Heq by (cbn; lia).
  rewrite !(PeanoNat.Nat.mul_comm 3) in Heq.
  apply f_equal with (f := fun n => Nat.div n 3) in Heq.
  now rewrite !PeanoNat.Nat.div_mul in * by auto.
Qed.
(* end hide *)
Lemma nat_fin_fun {n} : (fin (S n) -> nat) ≅ nat.
Proof.
  induction n; cbn.
  - eapply iso_trans; [eapply iso_fn1; [now exists (inl I)|rewrite sum_comm; apply sum_False]|].
    now rewrite fun_True.
  - change (True + fin n)%type with (fin (S n)).
    rewrite fun_sum_distr.
    eapply iso_trans; [apply iso_prod; [apply fun_True|apply IHn]|].
    clear.
    split; [exists (fun '(m, n) => Nat.pow 2 m * Nat.pow 3 n)|exists (fun n => (n, 0))];
    [|intros m n Heq; congruence].
    intros [m1 n1] [m2 n2] Heq.
    assert (Hmeq : m1 = m2).
    { apply f_equal with (f := Nat.iter (min m1 m2) halve) in Heq.
      eapply halving_eq1; eauto. }
    assert (Hneq : n1 = n2).
    { subst m2; apply f_equal with (f := Nat.iter m1 halve) in Heq.
      rewrite !halving_iter in Heq by lia.
      replace (m1 - m1) with 0 in Heq by lia.
      cbn in Heq.
      replace (Nat.pow 3 n1 + 0) with (Nat.pow 3 n1) in Heq by lia.
      replace (Nat.pow 3 n2 + 0) with (Nat.pow 3 n2) in Heq by lia.
      now apply halving_eq2. }
    congruence.
Qed.
(* begin hide *)
Lemma fin_fun_has_max {n} (f : fin n -> nat) : exists n, forall x, f x <= n.
Proof.
  induction n.
  - exists 0; intros [].
  - specialize (IHn (comp f inr)); unfold comp in IHn.
    destruct IHn as [max_n Hmax_n].
    exists (max (f (inl I)) max_n).
    intros [[]|x].
    + apply Max.le_max_l.
    + assert (Nat.max (f (inl I)) max_n >= max_n) by apply Max.le_max_r.
      specialize (Hmax_n x).
      eapply PeanoNat.Nat.le_trans; eauto.
Qed.
(* end hide *)
Lemma fin_lt_nat {n} : fin n ⋤ nat.
Proof.
  assert (Hno_surjection : forall f : fin n -> nat, exists y, forall x, f x <> y).
  { intros f. destruct (fin_fun_has_max f) as [max Hmax].
    exists (S max); intros x Heq; specialize (Hmax x); lia. }
  intros [f Hf].
  apply (inj_sur f) in Hf; [|now exists 0].
  destruct Hf as [g Hg].
  specialize (Hno_surjection g).
  destruct Hno_surjection as [y Hy].
  specialize (Hg y).
  destruct Hg as [x Hx]; now specialize (Hy x).
Qed.

(** [A] is always strictly smaller than [A -> fin 2], by diagonalization: *)

Lemma A_lt_PA {A} : A ⋤ (A -> fin 2).
Proof.
  assert (Hno_surjection : forall f : A -> A -> fin 2, exists g, forall n, f n <> g).
  { pose (negate := fun b : fin 2 =>
                      match b with 
                      | inl _ => inr (inl I)
                      | inr (inl _) => inl I
                      | inr (inr x) => match x with end
                      end : fin 2).
    intros f; exists (fun n => negate (f n n)).
    intros n Heq.
    apply f_equal with (f := fun f => f n) in Heq.
    destruct (f n n) as [[]|[[]|[]]]; cbn in Heq; congruence. }
  intros [f Hf].
  apply (inj_sur f) in Hf; [|now exists (fun _ => inl I)].
  destruct Hf as [g Hg].
  specialize (Hno_surjection g).
  destruct Hno_surjection as [y Hy].
  specialize (Hg y).
  destruct Hg as [x Hx]; now specialize (Hy x).
Qed.

(** But, changing the codomain from [fin 2] to [fin (2 + n)]
    doesn't make the cardinality any bigger: *)
(* begin hide *)
Fixpoint fin_inj {m n} : fin m -> fin (n + m) :=
  match n with
  | 0 => fun k => k
  | S n => fun k => inr (fin_inj k)
  end.
Lemma fin_inj_ok {m n} : injective (fin_inj : fin m -> fin (n + m)).
Proof.
  induction n; [firstorder|].
  cbn; intros k1 k2 Heq.
  inversion Heq as [Heq'].
  now apply IHn.
Qed.

Lemma pow2n_ge_n n : n <= Nat.pow 2 n.
Proof.
  induction n; [cbn; lia|].
  replace (Nat.pow 2 (S n)) with (2 * Nat.pow 2 n) by (cbn; lia).
  transitivity (S (Nat.pow 2 n)); [lia|].
  remember (Nat.pow 2 n) as m.
  assert (m > 0 -> S m <= 2 * m) by lia.
  assert (Hpow_gt : forall n, Nat.pow 2 n > 0).
  { clear; induction n as [|n IHn]; auto; cbn in *; lia. }
  assert (m > 0) by (specialize (Hpow_gt n); now subst).
  lia.
Qed.

Lemma n_le_pow_2m_n m n : n <= Nat.pow (2 + m) n.
Proof.
  assert (Nat.pow (2 + m) n >= Nat.pow 2 n).
  { apply PeanoNat.Nat.pow_le_mono_l; lia. }
  assert (Nat.pow 2 n >= n) by apply pow2n_ge_n.
  lia.
Qed.
(* end hide *)

Lemma PA2n_eq_PA {A n} :
  inhabited A ->
  (forall k, fin k * A ≅ A) ->
  (A -> fin (2 + n)) ≅ (A -> fin 2).
Proof.
  intros Hinh Hdup.
  assert (inject : forall m n, m <= n -> (A -> fin m) ⊑ (A -> fin n)).
  { clear - Hdup; intros m n Hle.
    assert (Hk : exists k, n = k + m) by (exists (n - m); lia).
    destruct Hk as [k Hk].
    rewrite Hk.
    exists (comp fin_inj).
    apply inj_ump, fin_inj_ok. }
  split.
  - assert (Hmult : A ≅ A * fin (2 + n)) by (symmetry; rewrite prod_comm; apply Hdup).
    eapply leq_trans; [|eapply leq_fn1; [|apply (proj2 Hmult)]].
    2:{ destruct Hinh as [arb _]; now exists (arb, inl I). }
    eapply leq_trans; [|eapply (proj1 fun_uncurry)].
    eapply leq_trans; [|eapply leq_fn2, (proj2 fin_fun)].
    apply inject, n_le_pow_2m_n.
  - assert (Hmult : A ≅ A * fin 2) by (symmetry; rewrite prod_comm; apply Hdup).
    eapply leq_trans; [|eapply leq_fn1; [|apply (proj2 Hmult)]].
    2:{ destruct Hinh as [arb _]; now exists (arb, inl I). }
    eapply leq_trans; [|eapply (proj1 fun_uncurry)].
    eapply leq_trans; [|eapply leq_fn2, (proj2 fin_fun)].
    apply inject, n_le_pow_2m_n.
Qed.

(** In fact, even going from [fin (2 + n)] to [nat] doesn't change the cardinality
    if the domain is large enough: *)

Lemma PAnat_eq_PA {A} :
  inhabited A ->
  A * nat ⊑ A ->
  (A -> nat) ≅ (A -> fin 2).
Proof.
  intros Hinh Hinf.
  split.
  - eapply leq_trans; [|eapply leq_fn1; [|apply Hinf]].
    2: destruct Hinh as [arb _]; now exists (arb, 0).
    eapply leq_trans; [|apply (proj1 fun_uncurry)].
    exists (fun f x y => if Nat.eqb (f x) y then inl I else inr (inl I)).
    intros f g Heq; apply functional_extensionality; intros x.
    apply f_equal with (f := fun f => f x (g x)) in Heq.
    rewrite PeanoNat.Nat.eqb_refl in Heq.
    destruct (Nat.eqb (f x) (g x)) eqn:Heqb; [|congruence].
    now apply PeanoNat.Nat.eqb_eq.
  - pose (inj_fin2 := fun (x : fin 2) =>
      match x with
      | inl _ => 0
      | inr (inl _) => 1
      | inr (inr x) => match x with end
      end : nat).
    assert (inj_fin2_ok : injective inj_fin2).
    { intros [[]|[[]|[]]] [[]|[[]|[]]]; cbn in *; congruence. }
    exists (comp inj_fin2); now apply inj_ump.
Qed.

Inductive card :=
| A0
| Zero | One
| Add (c1 c2 : card)
| Mul (c1 c2 : card)
| Exp (c1 c2 : card).
Infix "|^|" := Exp (at level 60, right associativity).
Infix "|*|" := Mul (at level 62, right associativity).
Infix "|+|" := Add (at level 63, right associativity).

(** We can write a function [cardD : card -> Type] that maps each [c] to a 
    type with cardinality [c]: *)

Fixpoint cardD c : Type :=
  match c with
  | A0 => nat
  | Zero => False
  | One => True
  | c1 |+| c2 => cardD c1 + cardD c2
  | c1 |*| c2 => cardD c1 * cardD c2
  | c1 |^| c2 => cardD c2 -> cardD c1
  end.

(** We can also write a function [simpl : card -> card] to simplify
    a cardinality expression: *)

(* Fixpoint simpl c := *)
(*   match c with *)
(*   | A0 | Zero | One => c *)
(*   | Zero |+| c | c |+| Zero => c *)
(*   | c1 |+| c2 => *)
(*     match simpl c1, simpl c2 with *)
(*     | Zero, c | c, Zero => c *)
(*     | c1, c2 => c1 |+| c2 *)
(*     end *)
(*   | Zero |*| _ | _ |*| Zero => Zero *)
(*   | One |*| c | c |*| One => c *)
(*   | c1 |*| c2 => *)
(*     match simpl c1, simpl c2 with *)
(*     | Zero, _ | _, Zero => Zero *)
(*     | One, c | c, One => c *)
(*     | c1, c2 => c1 |*| c2 *)
(*     end *)
(*   | Zero |^| Zero => One *)
(*   | Zero |^| _ => Zero *)
(*   | One |^| _ => One *)
(*   | _ |^| Zero => c *)
(*   | c |^| One => c *)
(*   | c1 |^| c2 => *)

(** In general [A <> B] can be proved this way if [A] and [B] are both finite with differing numbers
    of inhabitants, or if one of types is finite and the other not. 

    What if [A] and [B] are infinite? Diagonalization says that [nat] and [nat -> bool] can't be
    isomorphic.
*)

(*
Definition disambiguable A := exists f : A -> A, forall x, f x <> x.

(* If B is disambiguable, [f : A -> A -> B] can never be surjective *)
Lemma diag {A B} :
  disambiguable B -> forall f : A -> A -> B,
  exists g : A -> B, forall n, f n <> g.
Proof.
  intros [dis Hdis] f; exists (fun x => dis (f x x)).
  intros x Heq.
  apply f_equal with (f := fun f => f x) in Heq.
  specialize (Hdis (f x x)); congruence.
Qed.

Lemma cantor {A} : disambiguable A -> not (iso nat (nat -> A)).
Proof.
  intros Hdis [ab [ba [Hab Hba]]].
  destruct (diag Hdis ab) as [g Hg].
  specialize (Hab g).
  now specialize (Hg (ba g)).
Qed.

Lemma nat_ne_nat2bool : nat <> (nat -> bool).
Proof.
  apply iso_ne, cantor.
  exists negb; now intros [|].
Qed.

Definition countable A := A ≅ nat.

Lemma card_ne {A B C} :
  countable A ->
  countable B ->
  disambiguable C ->
  A <> (B -> C).
Proof.
  intros HA HB Hdis; apply iso_ne.
  intros Hiso; apply (@cantor C Hdis).
  eapply iso_trans; [|eapply iso_fn1, HB].
  eapply iso_trans; [apply iso_sym, HA|].
  apply Hiso.
Qed.

Lemma countable_disambiguable {A} : countable A -> disambiguable A.
Proof.
  intros [to_nat [of_nat [Hfg Hgf]]].
  exists (fun x => of_nat (S (to_nat x))).
  intros x Heq.
  rewrite <- Hgf in Heq.
  apply f_equal with (f := to_nat) in Heq; rewrite !Hfg in Heq.
  remember (to_nat x) as n; clear - Heq; induction n; congruence.
Qed.

Polymorphic Lemma equal_types_iso A B : 
  A = B ->
  exists (f : A -> B) (g : B -> A), (forall x, f (g x) = x) /\ (forall x, g (f x) = x).
Proof. intros; subst; exists (fun x => x), (fun x => x); auto. Qed.

(*

Polymorphic Lemma L A B (P : Type -> Type) : A = B -> P A -> P B.
Proof. congruence. Qed.

Polymorphic Lemma L' A B :
  (forall P : Type -> Type, P A -> P B) ->
  A = B.
Proof. intros H; apply (H (fun B => A = B) eq_refl). Qed.

Polymorphic Inductive T : Type -> Type :=
| Tnat : T nat
| Tnats : False -> T (list nat).


Require Import Coq.Program.Equality.
Definition tn : T nat := Tnat.
Definition ntns : T (list nat) -> False.
  intros H.
  remember (list nat) as n.
  destruct H eqn:Hh.
  dependent inversion H.
  destruct H; auto.
  admit.

Lemma nat_ne_nats : nat <> list nat.
Proof.
  intros H.
  pose (x := L nat (list nat) T H (Tnat I)).
Lemma L A B : A = B -> forall P : Type -> Type, P A -> P B.
Proof. congruence. Qed.

Module BasicIso.

Polymorphic Lemma equal_types_iso A B : 
  A = B ->
  exists (f : A -> B) (g : B -> A), (forall x, f (g x) = x) /\ (forall x, g (f x) = x).
Proof. intros; subst; exists (fun x => x), (fun x => x); auto. Qed.

Lemma nat_ne_bool : nat <> bool.
Proof.
  intros H; apply equal_types_iso in H.
  destruct H as [f [g [Hfg Hgf]]].
  assert (H0 : g (f 0) = 0) by auto.
  assert (H1 : g (f 1) = 1) by auto.
  assert (H2 : g (f 2) = 2) by auto.
  destruct (f 0), (f 1), (f 2); congruence.
Qed.

End BasicIso.

Polymorphic Lemma equal_types_size A B : 
  A = B ->
  forall (sizeA : A -> nat), exists (f : A -> B),
  (forall n x, sizeA x <= n -> sizeB (f x) <= n).
Proof. intros; subst; exists sizeA, (fun x => x); auto. Qed.

Inductive test : Type -> bool -> Type :=
| test0 : test nat true
| test1 : test bool false.

Definition f {T} (x : test T true) : bool :=
  match x with
  | test0 => true
  end.
Print f.

Definition f {b} (x : test nat b) : bool :=
  match x with
  | test0 => true
  | test1 => _
  end.

Inductive index : Type -> Type -> Type :=
| zero {Γ T} : index (T * Γ) T
| succ {Γ S T} : index Γ T -> index (S * Γ) T.

Inductive exp : Type -> Type -> Type :=
| lit {Γ T} (x : T) : exp Γ T
| var {Γ T} (n : index Γ T) : exp Γ T
| app {Γ S T} (e1 : exp Γ (S -> T)) (e2 : exp Γ S) : exp Γ T
| lam {Γ S T} (e : exp (S * Γ) T) : exp Γ (S -> T).

Fixpoint indexD {Γ T} (n : index Γ T) : Γ -> T :=
  match n with
  | zero => fun '(v, _) => v
  | succ n => fun '(_, ρ) => indexD n ρ
  end.

Fixpoint expD {Γ T} (e : exp Γ T) : Γ -> T :=
  match e with
  | lit x => fun _ => x
  | var n => indexD n
  | app e1 e2 => fun ρ => expD e1 ρ (expD e2 ρ)
  | lam e => fun ρ v => expD e (v, ρ)
  end.

Require Import Coq.Lists.List.
Import ListNotations.

Module Original.

Fixpoint contextD Γ : Type :=
  match Γ with
  | [] => unit
  | t :: Γ => t * contextD Γ
  end.

Inductive index : Type -> Type -> Type :=
| Zero : forall {t Γ}, index (t * Γ) t
| Succ : forall {s t Γ}, index Γ t -> index (s * Γ) t.

Inductive exp : Type -> Type -> Type :=
| Var {Γ t} (n : index Γ t) : exp Γ t
| Lam {Γ s t} (e : exp (s * Γ) t) : exp Γ (s -> t)
| App {Γ s t} (e1 : exp Γ (s -> t)) (e2 : exp Γ s) : exp Γ t
| Bool {Γ} (b : bool) : exp Γ bool
| BoolElim {Γ t} (e1 : exp Γ bool) (e2 e3 : exp Γ t) : exp Γ t
| Nat {Γ} (n : nat) : exp Γ nat
| NatElim {Γ t} (e1 : exp Γ nat) (e2 : exp Γ (t -> t)) (e3 : exp Γ t) : exp Γ t.

Fixpoint indexD {Γ t} (n : index Γ t) : Γ -> t :=
  match n with
  | Zero => fun '(v, _) => v
  | Succ n => fun '(_, ρ) => indexD n ρ
  end.

Fixpoint expD {Γ t} (e : exp Γ t) : Γ -> t :=
  match e with
  | Var n => indexD n
  | Lam e => fun ρ => fun v => expD e (v, ρ)
  | App e1 e2 => fun ρ => expD e1 ρ (expD e2 ρ)
  | Bool b => fun _ => b
  | BoolElim e1 e2 e3 => fun ρ => if expD e1 ρ then expD e2 ρ else expD e3 ρ
  | Nat n => fun _ => n
  | NatElim e1 e2 e3 => fun ρ => Nat.iter (expD e1 ρ) (expD e2 ρ) (expD e3 ρ)
  end.

Recursive Extraction expD.

Definition well_erased {A} (f : (A -> Type) -> Type) :=
  exists x, (fun k => k x) = f.

Inductive erased A : Type :=
  mk_erased :
    { f : (A -> Type) -> Type
    | well_erased f
    } -> erased A.

Notation "'(' x ';' prf ')'" := (mk_erased _ (exist _ x prf)).
Notation "'(' x ';;' prf ')'" := (ex_intro _ x prf).

Definition ret {A} (x : A) : erased A := (fun k => k x; (_;; eq_refl)).

Definition map {A B} (f : A -> B) (x : erased A) : erased B :=
  let '(x_cps; Hx) := x in
  (fun k => x_cps (fun x => k (f x));
   let '(x;; Hx_cps) := Hx in
   let 'eq_refl := Hx_cps in
   (_;; eq_refl)).

Definition ap {A B} (f : erased (A -> B)) (x : erased A) : erased B :=
  let '(f_cps; Hf) := f in
  let '(x_cps; Hx) := x in
  (fun k => f_cps (fun f => x_cps (fun x => k (f x)));
   let '(f;; Hf_cps) := Hf in
   let '(x;; Hx_cps) := Hx in
   let 'eq_refl := Hf_cps in
   let 'eq_refl := Hx_cps in
   (_;; eq_refl)).

Definition use {A} (x : erased A) : (A -> Type) -> Type :=
  let '(x; _) := x in x.

Ltac mk_cast x :=
  match goal with
  | |- ?expected =>
    let got := type of x in
    replace expected with got; [exact x|];
    clear x;
    repeat multimatch goal with
    | H : ?T |- _ =>
      progress(
      let T' := eval hnf in T in
      lazymatch T' with
      | erased _ =>
        let cps := fresh "cps" in
        let Hcps := fresh "Hcps" in
        destruct H as [[cps Hcps]]
      end)
    end;
    cbn;
    repeat progress match goal with H : well_erased _ |- _ => destruct H end;
    (* subst; exact eq_refl *)
    idtac
  end.

Notation "'![' e ']'" := (let x := e in ltac:(mk_cast x)).

Inductive vec {A} : erased nat -> Type :=
| vnil : vec (ret 0)
| vcons {n} : A -> vec n -> vec (map S n).
Arguments vec : clear implicits.

Goal nat = bool -> False.
  intros H.
  pose (x := 3).
  rewrite H in x.
  pose (y := if x then 0 else 1).
  Show Proof.

  Show Proof.


Definition app {A m n} (xs : vec A m) (ys : vec A n) : vec A (ap (map Nat.add m) n).
  refine(
  match xs with
  | vnil => ![ys]
  | vcons x xs => _
  end
  ).
    repeat multimatch goal with
    | H : ?T |- _ =>
      progress(
      let T' := eval hnf in T in
      lazymatch T' with
      | erased _ =>
        idtac T T';
        let cps := fresh "cps" in
        let Hcps := fresh "Hcps" in
        idtac H cps Hcps
        (* destruct H as [[cps Hcps]] *)
      end)
    end.
    destruct m.
    revert xs ys.
    destruct n as [[cps Hcps]].
  remember (map S n) as m.
  destruct xs eqn:Hxs.
  match xs with
  | vnil => _
  | vcons x _ => x
  end.

Inductive type := TBool | TNat | TFun (s t : type).

Require Import Coq.Lists.List.
Import ListNotations.

Module Original.

Definition context := list type.

Fixpoint typeD t : Type :=
  match t with
  | TBool => bool
  | TNat => nat
  | TFun s t => typeD s -> typeD t
  end.

Fixpoint contextD Γ : Type :=
  match Γ with
  | [] => unit
  | t :: Γ => typeD t * contextD Γ
  end.

Inductive index : context -> type -> Type :=
| Zero : forall {t Γ}, index (t :: Γ) t
| Succ : forall {s t Γ}, index Γ t -> index (s :: Γ) t.

Inductive exp : context -> type -> Type :=
| Var {Γ t} (n : index Γ t) : exp Γ t
| Lam {Γ s t} (e : exp (s :: Γ) t) : exp Γ (TFun s t)
| App {Γ s t} (e1 : exp Γ (TFun s t)) (e2 : exp Γ s) : exp Γ t
| Bool {Γ} (b : bool) : exp Γ TBool
| BoolElim {Γ t} (e1 : exp Γ TBool) (e2 e3 : exp Γ t) : exp Γ t
| Nat {Γ} (n : nat) : exp Γ TNat
| NatElim {Γ t} (e1 : exp Γ TNat) (e2 : exp Γ (TFun t t)) (e3 : exp Γ t) : exp Γ t.

Fixpoint indexD {Γ t} (n : index Γ t) : contextD Γ -> typeD t :=
  match n with
  | Zero => fun '(v, _) => v
  | Succ n => fun '(_, ρ) => indexD n ρ
  end.

Fixpoint expD {Γ t} (e : exp Γ t) : contextD Γ -> typeD t :=
  match e with
  | Var n => indexD n
  | Lam e => fun ρ => fun v => expD e (v, ρ)
  | App e1 e2 => fun ρ => expD e1 ρ (expD e2 ρ)
  | Bool b => fun _ => b
  | BoolElim e1 e2 e3 => fun ρ => if expD e1 ρ then expD e2 ρ else expD e3 ρ
  | Nat n => fun _ => n
  | NatElim e1 e2 e3 => fun ρ => Nat.iter (expD e1 ρ) (expD e2 ρ) (expD e3 ρ)
  end.

End Original.

(** %\begin{verbatim}
\end{verbatim}%

#<pre>
let rec expD _ _ = function
  | Var (_UU0393_0, t, n) -> indexD _UU0393_0 t n
  | Lam (_UU0393_0, s, t, e) -> fun _UU03c1_ v -> expD (Cons (s, _UU0393_0)) t e (Pair (v, _UU03c1_))
  | App (_UU0393_0, s, t, e1, e2) ->
    fun _UU03c1_ -> expD _UU0393_0 (TFun (s, t)) e1 _UU03c1_ (expD _UU0393_0 s e2 _UU03c1_)
  | Bool (_, b) -> fun _ -> b
  | BoolElim (_UU0393_0, t, e1, e2, e3) -> fun _UU03c1_ -> (
    match expD _UU0393_0 TBool e1 _UU03c1_ with
    | True -> expD _UU0393_0 t e2 _UU03c1_
    | False -> expD _UU0393_0 t e3 _UU03c1_)
  | Nat (_, n) -> fun _ -> n
  | NatElim (_UU0393_0, t, e1, e2, e3) -> fun _UU03c1_ ->
    iter (expD _UU0393_0 TNat e1 _UU03c1_) (expD _UU0393_0 (TFun (t, t)) e2 _UU03c1_)
      (expD _UU0393_0 t e3 _UU03c1_)
</pre># *)

Definition well_erased {A} (f : (A -> Type) -> Type) :=
  exists x, (fun k => k x) = f.

Inductive erased A : Type :=
  mk_erased :
    { f : (A -> Type) -> Type
    | well_erased f
    } -> erased A.

Notation "'(' x ';' prf ')'" := (mk_erased _ (exist _ x prf)).
Notation "'(' x ';;' prf ')'" := (ex_intro _ x prf).

Definition ret {A} (x : A) : erased A := (fun k => k x; (_;; eq_refl)).

Definition map {A B} (f : A -> B) (x : erased A) : erased B :=
  let '(x_cps; Hx) := x in
  (fun k => x_cps (fun x => k (f x));
   let '(x;; Hx_cps) := Hx in
   let 'eq_refl := Hx_cps in
   (_;; eq_refl)).

Definition ap {A B} (f : erased (A -> B)) (x : erased A) : erased B :=
  let '(f_cps; Hf) := f in
  let '(x_cps; Hx) := x in
  (fun k => f_cps (fun f => x_cps (fun x => k (f x)));
   let '(f;; Hf_cps) := Hf in
   let '(x;; Hx_cps) := Hx in
   let 'eq_refl := Hf_cps in
   let 'eq_refl := Hx_cps in
   (_;; eq_refl)).

Definition use {A} (x : erased A) : (A -> Type) -> Type :=
  let '(x; _) := x in x.

Definition context := erased (list type).

Fixpoint typeD t : Type :=
  match t with
  | TBool => bool
  | TNat => nat
  | TFun s t => typeD s -> typeD t
  end.

Fixpoint contextD (Γ : list type) : Type :=
  match Γ with
  | [] => unit
  | t :: Γ => typeD t * contextD Γ
  end.

Inductive index : context -> erased type -> Type :=
| Zero : forall {t Γ}, index (ap (map cons t) Γ) t
| Succ : forall {s t Γ}, index Γ t -> index (ap (map cons s) Γ) t.

Inductive exp : context -> erased type -> Type :=
| Var {Γ t} (n : index Γ t) : exp Γ t
| Lam {Γ s t} (e : exp (ap (map cons s) Γ) t) : exp Γ (ap (map TFun s) t)
| App {Γ s t} (e1 : exp Γ (ap (map TFun s) t)) (e2 : exp Γ s) : exp Γ t
| Bool {Γ} (b : bool) : exp Γ (ret TBool)
| BoolElim {Γ t} (e1 : exp Γ (ret TBool)) (e2 e3 : exp Γ t) : exp Γ t
| Nat {Γ} (n : nat) : exp Γ (ret TNat)
| NatElim {Γ t} (e1 : exp Γ (ret TNat)) (e2 : exp Γ (ap (map TFun t) t)) (e3 : exp Γ t) : exp Γ t.

Fixpoint indexD {Γ t} (n : index Γ t) : use Γ contextD -> use t typeD :=
  match n with
  | @Zero t Γ => ![(fun '(v, _) => v) : use t typeD * use Γ contextD -> _]
  | @Succ s t Γ n => ![(fun '(_, ρ) => indexD n ρ) : use s typeD * _ -> _]
  end.

Fixpoint expD {Γ t} (e : exp Γ t) : use Γ contextD -> use t typeD :=
  match e with
  | Var n => indexD n
  | @Lam Γ s t e => fun ρ => ![(fun v => expD e ![(v, ρ) : use s typeD * use Γ contextD])]
  | @App Γ s t e1 e2 => fun ρ => (![expD e1 ρ] : use s typeD -> use t typeD) (expD e2 ρ)
  | Bool b => fun _ => b
  | BoolElim e1 e2 e3 =>
    fun ρ =>
      if expD e1 ρ
      then expD e2 ρ
      else expD e3 ρ
  | Nat n => fun _ => n
  | @NatElim _ t e1 e2 e3 =>
    fun ρ =>
      @Nat.iter
        (expD e1 ρ)
        (use t typeD)
        ![expD e2 ρ]
        (expD e3 ρ)
  end.

Extraction Inline ret map ap.
Recursive Extraction expD.

Inductive index : context -> erased type -> Type :=
| Zero : forall {t Γ}, index (t :: Γ) (ret t)
| Succ : forall {s t Γ}, index Γ t -> index (s :: Γ) t.

Inductive exp : context -> erased type -> Type :=
| Var {Γ t} (n : index Γ t) : exp Γ t
| Lam {Γ s t} (e : exp (s :: Γ) (ret t)) : exp Γ (ret (TFun s t))
| App {Γ s t} (e1 : exp Γ (ret (TFun s t))) (e2 : exp Γ (ret s)) : exp Γ (ret t)
| Bool {Γ} (b : bool) : exp Γ (ret TBool)
| BoolElim {Γ t} (e1 : exp Γ (ret TBool)) (e2 e3 : exp Γ t) : exp Γ t
| Nat {Γ} (n : nat) : exp Γ (ret TNat)
| NatElim {Γ t} (e1 : exp Γ (ret TNat)) (e2 : exp Γ (ret (TFun t t))) (e3 : exp Γ (ret t)) : exp Γ (ret t).

Fixpoint indexD {Γ t} (n : index Γ t) : contextD Γ -> proj1_sig t (fun t => typeD t) :=
  match n with
  | Zero => fun '(v, _) => v
  | Succ n => fun '(_, ρ) => indexD n ρ
  end.

Fixpoint expD {Γ t} (e : exp Γ t) : contextD Γ -> proj1_sig t (fun t => typeD t) :=
  match e with
  | Var n => indexD n
  | Lam e => fun ρ => fun v => expD e (v, ρ)
  | App e1 e2 => fun ρ => expD e1 ρ (expD e2 ρ)
  | Bool b => fun _ => b
  | BoolElim e1 e2 e3 => fun ρ => if expD e1 ρ then expD e2 ρ else expD e3 ρ
  | Nat n => fun _ => n
  | NatElim e1 e2 e3 => fun ρ => Nat.iter (expD e1 ρ) (expD e2 ρ) (expD e3 ρ)
  end.

Recursive Extraction expD.

(* Module Extrinsically. *)

(* Definition index := nat. *)

(* Inductive exp := *)
(* | Var (n : index) *)
(* | Lam (e : exp) *)
(* | App (e1 e2 : exp) *)
(* | Bool (b : bool) *)
(* | BoolElim (e1 e2 e3 : exp) *)
(* | Nat (n : nat) *)
(* | NatElim (e1 e2 e3 : exp). *)

(* Notation "Γ ',,' x" := (x :: Γ) (at level 71, left associativity). *)
(* Reserved Notation "x '∷' t '∈' Γ" (at level 80, no associativity). *)
(* Inductive index_ok : index -> context -> type -> Prop := *)
(* | Zero : forall {t Γ}, *)
(*     0 ∷ t ∈ Γ ,, t *)
(* | Succ : forall {n s t Γ}, *)
(*     n ∷ t ∈ Γ -> *)
(*     S n ∷ t ∈ Γ ,, s *)
(* where "x '∷' t '∈' Γ" := (index_ok x Γ t). *)

(* Reserved Notation "Γ '⊢' e '∷' t" (at level 80, no associativity, e at level 79). *)
(* Inductive exp_ok : exp -> context -> type -> Prop := *)
(* | OVar {Γ n t} : *)
(*     n ∷ t ∈ Γ -> *)
(*     Γ ⊢ Var n ∷ t *)
(* | OLam {Γ e s t} : *)
(*     s :: Γ ⊢ e ∷ t -> *)
(*     Γ ⊢ Lam e ∷ TFun s t *)
(* | OApp {Γ e1 s t e2} : *)
(*     Γ ⊢ e1 ∷ TFun s t -> *)
(*     Γ ⊢ e2 ∷ s -> *)
(*     Γ ⊢ App e1 e2 ∷ t *)
(* | OBool {Γ b} : *)
(*     Γ ⊢ Bool b ∷ TBool *)
(* | OBoolElim {Γ e1 e2 e3 t} : *)
(*     Γ ⊢ e1 ∷ TBool -> *)
(*     Γ ⊢ e2 ∷ t -> *)
(*     Γ ⊢ e3 ∷ t -> *)
(*     Γ ⊢ BoolElim e1 e2 e3 ∷ t *)
(* | ONat {Γ n} : *)
(*     Γ ⊢ Nat n ∷ TNat *)
(* | ONatElim {Γ t e1 e2 e3} : *)
(*     Γ ⊢ e1 ∷ TNat -> *)
(*     Γ ⊢ e2 ∷ TFun t t -> *)
(*     Γ ⊢ e3 ∷ t -> *)
(*     Γ ⊢ NatElim e1 e2 e3 ∷ t *)
(* where "Γ '⊢' e '∷' t" := (exp_ok e Γ t). *)

(* Fixpoint indexD {Γ t} n : n ∷ t ∈ Γ -> contextD Γ -> typeD t. *)
(*   destruct n. *)
(*   refine( *)
(*   match n with *)
(*   | 0 => fun Hn => _ *)
(*   | S n => fun Hn => _ *)
(*   end). *)
(*   inversion Hn. *)

(* Fixpoint expD {Γ t} (e : exp Γ t) : contextD Γ -> typeD t := *)
(*   match e with *)
(*   | Var n => indexD n *)
(*   | Lam e => fun ρ => fun v => expD e (v, ρ) *)
(*   | App e1 e2 => fun ρ => expD e1 ρ (expD e2 ρ) *)
(*   | Bool b => fun _ => b *)
(*   | BoolElim e1 e2 e3 => fun ρ => if expD e1 ρ then expD e2 ρ else expD e3 ρ *)
(*   | Nat n => fun _ => n *)
(*   | NatElim e1 e2 e3 => fun ρ => Nat.iter (expD e1 ρ) (expD e2 ρ) (expD e3 ρ) *)
(*   end. *)

(* End Extrinsically. *)

(* Definition erased A : Type := *)
(*   { f : (A -> Prop) -> Prop *)
(*   | exists x, (fun k => k x) = f *)
(*   }. *)

(* Definition ret {A} (x : A) : erased A. *)
(* Proof. exists (fun k => k x); eauto. Defined. *)

(* Notation "'(' x ';' prf ')'" := (exist _ x prf). *)
(* Notation "'(' x ';;' prf ')'" := (ex_intro _ x prf). *)

(* Definition map {A B} (f : A -> B) (x : erased A) : erased B := *)
(*   let '(g; Hg) := x in *)
(*   (fun k => g (fun x => k (f x)); *)
(*    let '(x;; Hg_eq) := Hg in *)
(*    let 'eq_refl := Hg_eq in *)
(*    (_;; eq_refl)). *)

(* Definition ret_map {A B} (f : A -> B) x : map f (ret x) = ret (f x) := eq_refl. *)

(* (* *)
(* Definition bind {A B} (f : A -> erased B) (x : erased A) : erased B. *)
(* Proof. *)
(*   refine ( *)
(*     let '(g; Hg) := x in *)
(*     _ *)
(*   ). *)
(*   destruct x as [g Hg]. *)
(*   exists (fun k => g (fun x => proj1_sig (f x) k)). *)
(*   destruct Hg as [x Hg]; subst. *)
(*   destruct (f x) as [h [fx Hfx]]; subst h; cbn; eauto. *)
(* Defined. *)

(* Definition ret_map {A B} (f : A -> B) x : map f (ret x) = ret (f x) := eq_refl. *)

(* Definition ret_bind {A B} (f : A -> erased B) x : bind f (ret x) = f x. *)
(* Proof. *)
(*   destruct (f x) as [g [fx Hfx]] eqn:Hfx_eq; subst g. *)


(* (* Lemma recover {A} (e : erased A) : exists x, e = erase x. *) *)
(* (* Proof. destruct e as [f [x Hf]]. exists x; subst; eauto. Qed. *) *)
(* *) *)
(* Inductive vec {A} : erased nat -> Type := *)
(* | vnil : vec (ret 0) *)
(* | vcons : forall n, A -> vec n -> vec (map S n). *)
(* Arguments vec : clear implicits. *)

(* Require Import Coq.Logic.Eqdep. *)

(* Lemma vec_nat_inj : forall n m : nat, ret n = ret m -> n = m. *)
(* Proof. *)
(*   unfold ret. *)
(*   intros. *)
(*   match type of H with *)
(*   | ?u = ?v => pose (test := @proj2_sig_eq _ _ u v H); clearbody test *)
(*   end. *)
(*   simpl in test. *)
(*   unfold eq_rect in test. *)
(*   inversion H. *)
(*   destruct H1. *)
(*   rewrite H1 in test. *)
(*   assert (proj1_sig_eq H = let 'eq_refl := proj1_sig_eq H in eq_refl). *)
(*   apply UIP. *)
(*   rewrite H0 in test. *)
(*   simpl in test. *)
(*   rewrite UIP. *)
(*   rewrite UIP in test. *)


(* Definition hd {A n} (v : vec A (ret (S n))) : A. *)
(* Proof. *)
(*   remember (ret (S n)) as q. *)
(*   destruct v eqn:Hv. *)
(*   admit. *)
(*   exact a. *)
(*   destruct n; simpl in *. *)
(*   assert (Heq : exists n', x (fun n => vec A (S n)) = vec A (S n')). *)
(*   destruct e; subst; eauto. *)

(*   vec A (bind (fun m => map (fun n => m + n) n) m). *)

(* Definition vapp {A m n} (v : vec A m) (w : vec A n) : *)
(*   vec A (bind (fun m => map (fun n => m + n) n) m). *)
(* Proof. *)
(*   destruct v as [|n' x v']. *)
(*   -  *)

(* (** This is a test *) *)

(* Definition x := 4. *)




*)
*)
