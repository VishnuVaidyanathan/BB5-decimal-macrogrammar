(* Claimed BB(7) champion  1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB
   (found by Jeff Ketchersid, October 2026; the claimed bound is listed on the
   BusyBeaverWiki as not independently verified).

   This file proves, with exact step counts, the one move that the run is
   made of, and the halt.  It does not prove the whole run.

   Tape shape ("clean shape"):   1 0 [G reads 0]  T        written  clean T.
   Move:   clean (1^P 0^(2j) 1^(z+2) R)
           reaches   clean ((1100)^(j-1) 1^(3P+8-2j) 00 1^z R)
           in exactly  wlen P j  steps.
   Halt:   clean (1^P 0^(2j) 1), with P even, halts.

   Vishnu Vaidyanathan.  Coq 8.18, no axioms. *)

Require Import List Lia Arith.
Set Warnings "-abstract-large-number".
Import ListNotations.

(* ---------- 1. The machine ---------- *)

Inductive St := A | B | C | D | E | F | G | Hlt.

(* state, cells to the LEFT (nearest first), cell under the head,
   cells to the RIGHT (nearest first).  [] means blank from here on. *)
Definition conf : Type := (St * list bool * bool * list bool)%type.

Definition act (w goR : bool) (s' : St) (l r : list bool) : conf :=
  if goR then
    match r with
    | []      => (s', w :: l, false, [])
    | x :: r' => (s', w :: l, x, r')
    end
  else
    match l with
    | []      => (s', [], false, w :: r)
    | x :: l' => (s', l', x, w :: r)
    end.

Definition step (c : conf) : conf :=
  let '(s, l, h, r) := c in
  match s, h with
  | A, false => act true  true  B l r     (* A0 -> 1RB *)
  | A, true  => act false true  G l r     (* A1 -> 0RG *)
  | B, false => act true  true  C l r     (* B0 -> 1RC *)
  | B, true  => act true  true  B l r     (* B1 -> 1RB *)
  | C, false => act false true  D l r     (* C0 -> 0RD *)
  | C, true  => act true  true  Hlt l r   (* C1 -> 1RZ (halt) *)
  | D, false => act false false E l r     (* D0 -> 0LE *)
  | D, true  => act false false D l r     (* D1 -> 0LD *)
  | E, false => act false false F l r     (* E0 -> 0LF *)
  | E, true  => act true  false E l r     (* E1 -> 1LE *)
  | F, false => act true  true  A l r     (* F0 -> 1RA *)
  | F, true  => act true  false F l r     (* F1 -> 1LF *)
  | G, false => act true  false C l r     (* G0 -> 1LC *)
  | G, true  => act false true  B l r     (* G1 -> 0RB *)
  | Hlt, _   => c
  end.

Fixpoint steps (n : nat) (c : conf) : conf :=
  match n with
  | 0   => c
  | S k => steps k (step c)
  end.

Lemma steps_add : forall a b c, steps (a + b) c = steps b (steps a c).
Proof. induction a as [| a IH]; intros b c; simpl; [reflexivity | apply IH]. Qed.

Lemma run : forall p q c c' c'',
  steps p c = c' -> steps q c' = c'' -> steps (p + q) c = c''.
Proof. intros. rewrite steps_add. congruence. Qed.

Ltac comp := eapply run; [ cbn [steps step act app repeat]; reflexivity | ].
Ltac by_lemma L := eapply run; [ apply L | ].
Ltac shape c' := match goal with |- steps _ ?c = _ => replace c with c' end.

(* ---------- 2. Blocks ---------- *)

Notation ones := (repeat true).
Notation zeros := (repeat false).

Lemma ones_snoc : forall k (l : list bool), ones k ++ true :: l = true :: ones k ++ l.
Proof. induction k; intros l; simpl; [reflexivity | rewrite IHk; reflexivity]. Qed.

Lemma ones_add : forall a b (l : list bool), ones (a + b) ++ l = ones a ++ ones b ++ l.
Proof. intros. rewrite repeat_app, <- app_assoc. reflexivity. Qed.

(* (0 1)^n nearest first: on the tape, read left to right, this is (1 0)^n. *)
Fixpoint zo (n : nat) : list bool :=
  match n with 0 => [] | S k => false :: true :: zo k end.

Lemma zo_snoc : forall n l, zo n ++ false :: true :: l = false :: true :: zo n ++ l.
Proof. induction n; intros l; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(* (1 1 0 0)^n *)
Fixpoint units (n : nat) : list bool :=
  match n with 0 => [] | S k => true :: true :: false :: false :: units k end.

Lemma units_snoc : forall n l,
  units n ++ true :: true :: false :: false :: l = true :: true :: false :: false :: units n ++ l.
Proof. induction n; intros l; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(* head on the first cell of r *)
Definition at_ (s : St) (l r : list bool) : conf :=
  match r with
  | h :: t => (s, l, h, t)
  | []     => (s, l, false, [])
  end.

(* ---------- 3. The coils ---------- *)

(* B walks right over ones (digit 3). *)
Lemma sweepB : forall k l r,
  steps k (at_ B l (ones k ++ false :: r)) = (B, ones k ++ l, false, r).
Proof.
  induction k as [| k IH]; intros l r.
  - reflexivity.
  - change (steps (S k) (at_ B l (ones (S k) ++ false :: r)))
      with (steps k (step (B, l, true, ones k ++ false :: r))).
    replace (step (B, l, true, ones k ++ false :: r))
      with (at_ B (true :: l) (ones k ++ false :: r)).
    + rewrite IH. rewrite ones_snoc. reflexivity.
    + cbn [step act]. destruct (ones k ++ false :: r); reflexivity.
Qed.

(* E walks left over ones (digit 9), and stops on the cell x. *)
Lemma sweepE : forall k x l r,
  steps (S k) (E, ones k ++ x :: l, true, r) = (E, l, x, ones (S k) ++ r).
Proof.
  induction k as [| k IH]; intros x l r.
  - reflexivity.
  - change (steps (S (S k)) (E, ones (S k) ++ x :: l, true, r))
      with (steps (S k) (E, ones k ++ x :: l, true, true :: r)).
    rewrite IH. rewrite ones_snoc. reflexivity.
Qed.

Lemma sweepE_blank : forall k r,
  steps (S k) (E, ones k, true, r) = (E, [], false, ones (S k) ++ r).
Proof.
  induction k as [| k IH]; intros r.
  - reflexivity.
  - change (steps (S (S k)) (E, ones (S k), true, r))
      with (steps (S k) (E, ones k, true, true :: r)).
    rewrite IH. rewrite ones_snoc. reflexivity.
Qed.

(* F walks left over ones (digit b). *)
Lemma sweepF : forall k x l r,
  steps (S k) (F, ones k ++ x :: l, true, r) = (F, l, x, ones (S k) ++ r).
Proof.
  induction k as [| k IH]; intros x l r.
  - reflexivity.
  - change (steps (S (S k)) (F, ones (S k) ++ x :: l, true, r))
      with (steps (S k) (F, ones k ++ x :: l, true, true :: r)).
    rewrite IH. rewrite ones_snoc. reflexivity.
Qed.

Lemma sweepF_blank : forall k r,
  steps (S k) (F, ones k, true, r) = (F, [], false, ones (S k) ++ r).
Proof.
  induction k as [| k IH]; intros r.
  - reflexivity.
  - change (steps (S (S k)) (F, ones (S k), true, r))
      with (steps (S k) (F, ones k, true, true :: r)).
    rewrite IH. rewrite ones_snoc. reflexivity.
Qed.

(* ---------- 4. One build round:  2476 9^(a+1) 8a0 3^(a+1) ---------- *)

(* The block of ones grows by 2 on the left and 1 on the right, and one 1
   further right is erased. *)
Lemma round_blank : forall a T,
  steps (2 * a + 9) (B, ones a, false, false :: true :: T)
  = (B, ones (a + 3), false, false :: T).
Proof.
  intros a T.
  replace (2 * a + 9) with (4 + (S a + (3 + S a))) by lia.
  comp.                                    (* 2476 *)
  by_lemma sweepE_blank.                   (* 9^(a+1) *)
  comp.                                    (* 8a0 *)
  shape (at_ B [true; true] (ones (S a) ++ false :: false :: T)).
  2: { reflexivity. }
  rewrite sweepB.                          (* 3^(a+1) *)
  replace (a + 3) with (S a + 2) by lia. rewrite repeat_app. reflexivity.
Qed.

Lemma round_gen : forall a L T,
  steps (2 * a + 9) (B, ones a ++ false :: false :: L, false, false :: true :: T)
  = (B, ones (a + 3) ++ L, false, false :: T).
Proof.
  intros a L T.
  replace (2 * a + 9) with (4 + (S a + (3 + S a))) by lia.
  comp.
  by_lemma sweepE.
  comp.
  shape (at_ B (true :: true :: L) (ones (S a) ++ false :: false :: T)).
  2: { reflexivity. }
  rewrite sweepB.
  replace (a + 3) with (S a + 2) by lia. rewrite (ones_add (S a) 2). reflexivity.
Qed.

(* P rounds in a row *)
Fixpoint bcost (P a : nat) : nat :=
  match P with 0 => 0 | S p => (2 * a + 9) + bcost p (a + 3) end.

Lemma build : forall P a T,
  steps (bcost P a) (B, ones a, false, false :: ones P ++ T)
  = (B, ones (a + 3 * P), false, false :: T).
Proof.
  induction P as [| P IH]; intros a T.
  - replace (a + 3 * 0) with a by lia. reflexivity.
  - cbn [bcost].
    eapply run. { apply (round_blank a (ones P ++ T)). }
    rewrite IH. replace (a + 3 + 3 * P) with (a + 3 * S P) by lia. reflexivity.
Qed.

Lemma bcost_closed : forall P a, bcost P a + 3 * P = P * (2 * a + 9) + 3 * P * P.
Proof.
  induction P as [| P IH]; intros a; cbn [bcost]; [lia |].
  pose proof (IH (a + 3)). nia.
Qed.

(* ---------- 5. Close and countdown ---------- *)

(* 2468 b^(a+1): the head goes back to the left end of the block. *)
Lemma close_blank : forall a T,
  steps (a + 5) (B, ones a, false, false :: false :: T)
  = (F, [], false, ones (S a) ++ false :: false :: T).
Proof.
  intros a T. replace (a + 5) with (4 + S a) by lia.
  comp. apply sweepF_blank.
Qed.

(* One countdown line  a1d 3^k 2468 b^(k+1): the block moves 2 cells to the
   right and loses a 1; "1 0" is left behind. *)
Lemma count : forall k L T,
  steps (2 * k + 8) (F, L, false, ones (k + 2) ++ false :: false :: false :: T)
  = (F, false :: true :: L, false, ones (k + 1) ++ false :: false :: T).
Proof.
  intros k L T.
  replace (2 * k + 8) with (3 + (k + (4 + S k))) by lia.
  replace (k + 2) with (S (S k)) by lia. replace (k + 1) with (S k) by lia.
  eapply run.
  { instantiate (1 := at_ B (false :: false :: true :: L)
                          (ones k ++ false :: false :: false :: T)).
    cbn [steps step act app repeat]. destruct (ones k ++ false :: false :: false :: T); reflexivity. }
  by_lemma sweepB.
  comp.
  apply sweepF.
Qed.

Lemma count_blank : forall k L,
  steps (2 * k + 8) (F, L, false, ones (k + 2) ++ [false; false])
  = (F, false :: true :: L, false, ones (k + 1) ++ [false; false]).
Proof.
  intros k L.
  replace (2 * k + 8) with (3 + (k + (4 + S k))) by lia.
  replace (k + 2) with (S (S k)) by lia. replace (k + 1) with (S k) by lia.
  eapply run.
  { instantiate (1 := at_ B (false :: false :: true :: L) (ones k ++ [false; false])).
    cbn [steps step act app repeat]. destruct (ones k ++ [false; false]); reflexivity. }
  by_lemma sweepB.
  comp.
  apply sweepF.
Qed.

(* c countdown lines: the block goes from b+1+c ones down to b+1. *)
Fixpoint ccost (c b : nat) : nat :=
  match c with 0 => 0 | S c' => (2 * (b + c') + 8) + ccost c' b end.

Lemma counts : forall c b L T,
  steps (ccost c b) (F, L, false, ones (S b + c) ++ zeros (c + 2) ++ T)
  = (F, zo c ++ L, false, ones (S b) ++ false :: false :: T).
Proof.
  induction c as [| c IH]; intros b L T.
  - replace (S b + 0) with (S b) by lia. reflexivity.
  - cbn [ccost].
    eapply run.
    { replace (S b + S c) with ((b + c) + 2) by lia.
      replace (S c + 2) with (S (S (S c))) by lia.
      cbn [repeat app]. apply count. }
    replace (b + c + 1) with (S b + c) by lia.
    replace (false :: false :: zeros c ++ T) with (zeros (c + 2) ++ T).
    2: { replace (c + 2) with (S (S c)) by lia. reflexivity. }
    rewrite IH. rewrite zo_snoc. reflexivity.
Qed.

Lemma counts_blank : forall c b L,
  steps (ccost c b) (F, L, false, ones (S b + c) ++ [false; false])
  = (F, zo c ++ L, false, ones (S b) ++ [false; false]).
Proof.
  induction c as [| c IH]; intros b L.
  - replace (S b + 0) with (S b) by lia. reflexivity.
  - cbn [ccost].
    eapply run.
    { replace (S b + S c) with ((b + c) + 2) by lia. apply count_blank. }
    replace (b + c + 1) with (S b + c) by lia.
    rewrite IH. rewrite zo_snoc. reflexivity.
Qed.

Lemma ccost_closed : forall c b, ccost c b + c = c * (2 * b + 8) + c * c.
Proof. induction c as [| c IH]; intros b; cbn [ccost]; [lia |]. pose proof (IH b). nia. Qed.

(* ---------- 6. The waiting lines  c 4769^2 8b a1 ---------- *)

(* Each waiting line uses up "1 0 1 0" on the left and leaves a unit 1100
   on the right. *)
Lemma wait_step : forall X T,
  steps 10 (G, false :: true :: true :: false :: true :: false :: X, false, T)
  = (G, false :: true :: X, false, true :: true :: false :: false :: T).
Proof. reflexivity. Qed.

Lemma wait_last : forall T,
  steps 10 (G, [false; true; true; false; true], false, T)
  = (G, [false; true], false, true :: true :: false :: false :: T).
Proof. reflexivity. Qed.

Lemma waits : forall t T,
  steps (10 * S t) (G, false :: true :: true :: zo (2 * t + 1), false, T)
  = (G, [false; true], false, units (S t) ++ T).
Proof.
  induction t as [| t IH]; intros T.
  - apply wait_last.
  - replace (10 * S (S t)) with (10 + 10 * S t) by lia.
    replace (2 * S t + 1) with (S (S (2 * t + 1))) by lia. cbn [zo].
    eapply run. { apply wait_step. }
    rewrite IH. rewrite units_snoc. reflexivity.
Qed.

(* ---------- 7. The move ---------- *)

Definition clean (T : list bool) : conf := (G, [false; true], false, T).

(* Steps of one move.  j = S j' is half the gap, and 3P + 3 = m + 2j. *)
Definition wcost (P j' m : nat) : nat :=
  9 + (bcost P 3 + ((3 * P + 3 + 5) + (ccost (2 * j' + 1) (S m)
     + (3 + (m + ((2 * m + 9) + (4 + (S (m + 4) + (4 + 10 * j'))))))))).

Theorem move : forall P j' m z R,
  3 * P + 3 = m + 2 * S j' -> 1 <= m ->
  steps (wcost P j' m)
    (clean (ones P ++ zeros (2 * S j') ++ ones (z + 2) ++ R))
  = clean (units j' ++ ones (m + 5) ++ false :: false :: ones z ++ R).
Proof.
  intros P j' m z R Hm Hm1. unfold wcost, clean.
  (* Open: c47698a03 *)
  eapply run.
  { instantiate (1 := (B, ones 3, false,
       false :: ones P ++ zeros (2 * S j') ++ ones (z + 2) ++ R)). reflexivity. }
  (* Build *)
  by_lemma build.
  (* Close *)
  replace (2 * S j') with (S (S (2 * j'))) by lia. cbn [repeat app].
  replace (3 + 3 * P) with (3 * P + 3) by lia.
  by_lemma close_blank.
  (* Countdown: 2j - 1 lines *)
  shape (F, @nil bool, false,
         ones (S (S m) + (2 * j' + 1)) ++ zeros ((2 * j' + 1) + 2) ++ ones (z + 2) ++ R).
  2: { f_equal. replace (S (S m) + (2 * j' + 1)) with (S (3 * P + 3)) by lia.
       f_equal. replace (2 * j' + 1 + 2) with (S (S (S (2 * j')))) by lia. reflexivity. }
  by_lemma counts. rewrite app_nil_r.
  (* a1d, then 3^m *)
  replace (z + 2) with (S (S z)) by lia.
  eapply run.
  { instantiate (1 := at_ B (false :: false :: true :: zo (2 * j' + 1))
                          (ones m ++ false :: false :: ones (S (S z)) ++ R)).
    cbn [steps step act app repeat].
    destruct (ones m ++ false :: false :: true :: true :: ones z ++ R); reflexivity. }
  by_lemma sweepB.
  (* one more round, using a 1 of the next block *)
  cbn [repeat app].
  by_lemma (round_gen m (true :: zo (2 * j' + 1)) (true :: ones z ++ R)).
  (* 2476 9^(m+5) *)
  comp.
  shape (E, ones (m + 4) ++ false :: true :: zo (2 * j'), true,
         false :: false :: ones z ++ R).
  2: { f_equal. f_equal. f_equal.
       replace (2 * j' + 1) with (S (2 * j')) by lia. cbn [zo].
       replace (m + 4) with ((m + 3) + 1) by lia. rewrite (ones_add (m + 3) 1). reflexivity. }
  by_lemma sweepE.
  (* 8b a1, and the waiting lines *)
  replace (S (m + 4)) with (m + 5) by lia.
  destruct j' as [| t].
  - cbn [zo units app Nat.mul]. reflexivity.
  - replace (2 * S t) with (S (2 * t + 1)) by lia. cbn [zo].
    eapply run.
    { instantiate (1 := (G, false :: true :: true :: zo (2 * t + 1), false,
         ones (m + 5) ++ false :: false :: ones z ++ R)). reflexivity. }
    apply waits.
Qed.

(* Closed form of the step count:
   3P^2 + 27P + 44 + 2j + (2j-1)(2m + 2j + 8),  with j = j' + 1. *)
Theorem wcost_closed : forall P j' m, 3 * P + 3 = m + 2 * S j' ->
  wcost P j' m
  = 3 * P * P + 27 * P + 44 + 2 * S j' + (2 * j' + 1) * (2 * m + 2 * S j' + 8).
Proof.
  intros P j' m H. unfold wcost.
  pose proof (bcost_closed P 3). pose proof (ccost_closed (2 * j' + 1) (S m)). nia.
Qed.

(* The case j = 1: the tripling.  P becomes 3P + 6 in 3P^2 + 33P + 58 steps. *)
Corollary triple : forall P z R, 1 <= P ->
  steps (3 * P * P + 33 * P + 58) (clean (ones P ++ false :: false :: ones (z + 2) ++ R))
  = clean (ones (3 * P + 6) ++ false :: false :: ones z ++ R).
Proof.
  intros P z R HP.
  pose proof (move P 0 (3 * P + 1) z R ltac:(lia) ltac:(lia)) as H.
  rewrite (wcost_closed P 0 (3 * P + 1) ltac:(lia)) in H.
  change (zeros (2 * 1)) with [false; false] in H. cbn [units app] in H.
  replace (3 * P + 1 + 5) with (3 * P + 6) in H by lia.
  rewrite <- H. f_equal. nia.
Qed.

(* Many triplings in a row: the block after the gap is used up 2 at a time. *)
Fixpoint tri (n P : nat) : nat :=
  match n with 0 => P | S k => tri k (3 * P + 6) end.

Fixpoint chcost (n P : nat) : nat :=
  match n with 0 => 0 | S k => (3 * P * P + 33 * P + 58) + chcost k (3 * P + 6) end.

Theorem chain : forall n P R, 1 <= P ->
  steps (chcost n P) (clean (ones P ++ false :: false :: ones (2 * n) ++ R))
  = clean (ones (tri n P) ++ false :: false :: R).
Proof.
  induction n as [| n IH]; intros P R HP.
  - reflexivity.
  - cbn [chcost tri].
    eapply run.
    { replace (2 * S n) with (2 * n + 2) by lia. apply triple. exact HP. }
    apply IH. lia.
Qed.

Lemma tri_closed : forall n P, tri n P + 3 = (P + 3) * 3 ^ n.
Proof.
  induction n as [| n IH]; intros P; cbn [tri Nat.pow]; [lia |].
  rewrite IH. lia.
Qed.

(* ---------- 8. The halt ---------- *)

(* The gate.  When the block after the gap is a single 1 (and it is the last
   thing on the tape), there is nothing to take 2 from.  If P is even, which
   is the case m odd below, the machine halts. *)

Lemma hw_first : forall x L T,
  steps 9 (F, false :: true :: x :: L, false, true :: false :: T)
  = (F, L, x, true :: false :: true :: false :: false :: T).
Proof. reflexivity. Qed.

Lemma hw_step : forall x L T,
  steps 10 (F, true :: false :: true :: x :: L, false, true :: false :: T)
  = (F, L, x, true :: false :: true :: true :: false :: false :: T).
Proof. reflexivity. Qed.

Lemma hw_loop : forall t Y T,
  steps (10 * t) (F, true :: zo (2 * t) ++ Y, false, true :: false :: T)
  = (F, true :: Y, false, true :: false :: units t ++ T).
Proof.
  induction t as [| t IH]; intros Y T.
  - reflexivity.
  - replace (10 * S t) with (10 + 10 * t) by lia.
    replace (2 * S t) with (S (S (2 * t))) by lia. cbn [zo app].
    eapply run. { apply hw_step. }
    rewrite IH. rewrite units_snoc. reflexivity.
Qed.

Lemma final5 : forall l T, (l = [] \/ exists l', l = false :: l') ->
  exists l2 r2, steps 5 (F, l, true, true :: false :: true :: T) = (C, l2, true, r2).
Proof.
  intros l T [-> | [l' ->]]; eexists; eexists; reflexivity.
Qed.

(* Steps before the last one; m = 2s + 1. *)
Definition hcost (P j' s : nat) : nat :=
  9 + (bcost P 3 + ((3 * P + 3 + 5) + (ccost (2 * j' + 1) (S (2 * s + 1))
     + (3 + ((2 * s + 1) + ((2 * (2 * s + 1) + 9) + (4 + (S (2 * s + 1 + 4)
     + (ccost (2 * s + 1 + 4) 0 + (9 + (10 * S s + 10))))))))))).

Lemma halt_pre : forall P j' s,
  3 * P + 3 = (2 * s + 1) + 2 * S j' ->
  steps (hcost P j' s) (clean (ones P ++ zeros (2 * S j') ++ [true]))
  = (F, zo (2 * j'), true,
     true :: false :: true :: true :: false :: false :: units (S s) ++ [true; false; false; false]).
Proof.
  intros P j' s Hm. unfold hcost, clean. set (m := 2 * s + 1) in *.
  eapply run.
  { instantiate (1 := (B, ones 3, false, false :: ones P ++ zeros (2 * S j') ++ [true])).
    reflexivity. }
  by_lemma build.
  replace (2 * S j') with (S (S (2 * j'))) by lia. cbn [repeat app].
  replace (3 + 3 * P) with (3 * P + 3) by lia.
  by_lemma close_blank.
  shape (F, @nil bool, false,
         ones (S (S m) + (2 * j' + 1)) ++ zeros ((2 * j' + 1) + 2) ++ [true]).
  2: { f_equal. replace (S (S m) + (2 * j' + 1)) with (S (3 * P + 3)) by lia.
       f_equal. replace (2 * j' + 1 + 2) with (S (S (S (2 * j')))) by lia. reflexivity. }
  by_lemma counts. rewrite app_nil_r.
  eapply run.
  { instantiate (1 := at_ B (false :: false :: true :: zo (2 * j' + 1))
                          (ones m ++ [false; false; true])).
    cbn [steps step act app repeat].
    destruct (ones m ++ [false; false; true]); reflexivity. }
  by_lemma sweepB.
  by_lemma (round_gen m (true :: zo (2 * j' + 1)) (@nil bool)).
  (* 2468, then b^(m+5): back to the left end of the block *)
  comp.
  shape (F, ones (m + 4) ++ false :: true :: zo (2 * j'), true, [false; false]).
  2: { f_equal. f_equal. f_equal.
       replace (2 * j' + 1) with (S (2 * j')) by lia. cbn [zo].
       replace (m + 4) with ((m + 3) + 1) by lia. rewrite (ones_add (m + 3) 1). reflexivity. }
  by_lemma sweepF.
  (* countdown all the way to a single 1 *)
  shape (F, true :: zo (2 * j'), false, ones (1 + (m + 4)) ++ [false; false]).
  2: { reflexivity. }
  by_lemma counts_blank.
  (* a1c47698b, then the lines a1c476998b *)
  eapply run.
  { replace (m + 4) with (S (S (2 * S s + 1))) by lia. cbn [zo app repeat].
    apply hw_first. }
  eapply run.
  { replace (zo (2 * S s + 1) ++ true :: zo (2 * j'))
      with (zo (2 * S s) ++ false :: true :: true :: zo (2 * j')).
    - apply hw_loop.
    - rewrite zo_snoc. replace (2 * S s + 1) with (S (2 * S s)) by lia. reflexivity. }
  apply hw_step.
Qed.

Theorem halt_move : forall P j' s,
  3 * P + 3 = (2 * s + 1) + 2 * S j' ->
  exists l r,
    steps (hcost P j' s + 5) (clean (ones P ++ zeros (2 * S j') ++ [true])) = (C, l, true, r).
Proof.
  intros P j' s Hm.
  destruct (final5 (zo (2 * j'))
              (true :: false :: false :: units (S s) ++ [true; false; false; false])) as [l [r H]].
  { destruct j' as [| t]; [left; reflexivity |].
    right. replace (2 * S t) with (S (S (2 * t))) by lia. eexists. reflexivity. }
  exists l, r. rewrite steps_add, (halt_pre P j' s Hm). exact H.
Qed.

(* C reading 1 is the only halting pair: the next step halts. *)
Definition state (c : conf) : St := let '(s, _, _, _) := c in s.

Corollary halts : forall P j' s,
  3 * P + 3 = (2 * s + 1) + 2 * S j' ->
  state (steps (S (hcost P j' s + 5)) (clean (ones P ++ zeros (2 * S j') ++ [true]))) = Hlt.
Proof.
  intros P j' s Hm. destruct (halt_move P j' s Hm) as [l [r H]].
  replace (S (hcost P j' s + 5)) with ((hcost P j' s + 5) + 1) by lia.
  rewrite steps_add, H. destruct r; reflexivity.
Qed.

(* Zeros written at the far ends of the tape are the same as blank cells, so
   the halt also holds when the last 1 is followed by written zeros. *)
Definition eqz (a b : list bool) : Prop := forall n, nth n a false = nth n b false.

Definition ceq (c c' : conf) : Prop :=
  let '(s, l, h, r) := c in let '(s', l', h', r') := c' in
  s = s' /\ h = h' /\ eqz l l' /\ eqz r r'.

Lemma eqz_cons : forall x a b, eqz a b -> eqz (x :: a) (x :: b).
Proof. intros x a b H [| n]; simpl; [reflexivity | apply H]. Qed.

Lemma eqz_hd : forall a b, eqz a b -> hd false a = hd false b.
Proof. intros a b H. specialize (H 0). destruct a, b; exact H. Qed.

Lemma eqz_tl : forall a b, eqz a b -> eqz (tl a) (tl b).
Proof.
  intros a b H n. specialize (H (S n)).
  destruct a, b; simpl in *; try exact H; destruct n; auto.
Qed.

Lemma act_alt : forall w goR s l r,
  act w goR s l r = if goR then (s, w :: l, hd false r, tl r) else (s, tl l, hd false l, w :: r).
Proof. intros w [|] s l r; simpl; [destruct r | destruct l]; reflexivity. Qed.

Lemma act_ceq : forall w goR s l l' r r', eqz l l' -> eqz r r' ->
  ceq (act w goR s l r) (act w goR s l' r').
Proof.
  intros w goR s l l' r r' Hl Hr. rewrite !act_alt. destruct goR; simpl.
  - repeat split; [apply eqz_hd, Hr | apply eqz_cons, Hl | apply eqz_tl, Hr].
  - repeat split; [apply eqz_hd, Hl | apply eqz_tl, Hl | apply eqz_cons, Hr].
Qed.

Lemma step_ceq : forall c c', ceq c c' -> ceq (step c) (step c').
Proof.
  intros [[[s l] h] r] [[[s' l'] h'] r'] (Hs & Hh & Hl & Hr). subst s' h'.
  destruct s, h; cbn [step]; try (apply act_ceq; assumption); repeat split; assumption.
Qed.

Lemma steps_ceq : forall n c c', ceq c c' -> ceq (steps n c) (steps n c').
Proof. induction n; intros c c' H; simpl; [exact H | apply IHn, step_ceq, H]. Qed.

Lemma eqz_app : forall x a b, eqz a b -> eqz (x ++ a) (x ++ b).
Proof. induction x; intros a' b H; simpl; [exact H | apply eqz_cons, IHx, H]. Qed.

Lemma eqz_zeros : forall k, eqz [] (zeros k).
Proof.
  intros k n. revert n. induction k; intros n; simpl; [reflexivity |].
  destruct n; simpl; [reflexivity |]. rewrite <- IHk. destruct n; reflexivity.
Qed.

Theorem halts_gen : forall P j' s k,
  3 * P + 3 = (2 * s + 1) + 2 * S j' ->
  state (steps (S (hcost P j' s + 5))
           (clean (ones P ++ zeros (2 * S j') ++ true :: zeros k))) = Hlt.
Proof.
  intros P j' s k Hm. pose proof (halts P j' s Hm) as H.
  assert (Hc : ceq (clean (ones P ++ zeros (2 * S j') ++ [true]))
                   (clean (ones P ++ zeros (2 * S j') ++ true :: zeros k))).
  { unfold clean. repeat split; try (intros n; reflexivity).
    apply eqz_app, eqz_app, eqz_cons, eqz_zeros. }
  apply (steps_ceq (S (hcost P j' s + 5))) in Hc.
  destruct (steps (S (hcost P j' s + 5)) (clean (ones P ++ zeros (2 * S j') ++ [true])))
    as [[[s1 l1] h1] r1].
  destruct (steps (S (hcost P j' s + 5)) (clean (ones P ++ zeros (2 * S j') ++ true :: zeros k)))
    as [[[s2 l2] h2] r2].
  destruct Hc as (Hs & _). cbn [state] in *. congruence.
Qed.

(* ---------- 9. The real run ---------- *)

Definition c0 : conf := (A, [], false, []).

(* After 3,954 steps the tape is clean: P = 16, a gap of 4, nineteen units
   1100 and a last single 1.  (Checked by running the machine inside Coq.) *)
Definition tail : list bool := [true; false; false; false].   (* the last 1, then cells already visited *)

Lemma start : steps 3954 c0 = clean (ones 16 ++ zeros 4 ++ units 19 ++ tail).
Proof. vm_compute. reflexivity. Qed.

(* Two moves later (step 5,656) the tripling begins with P = 12 and a
   counter of 50. *)
Theorem at_5656 :
  steps 5656 c0 = clean (ones 12 ++ false :: false :: ones 50 ++ zeros 4 ++ units 18 ++ tail).
Proof.
  replace 5656 with (3954 + (wcost 16 1 47 + wcost 2 0 7)).
  2: { rewrite (wcost_closed 16 1 47), (wcost_closed 2 0 7) by reflexivity. reflexivity. }
  eapply run. { apply start. }
  eapply run.
  { change (clean (ones 16 ++ zeros 4 ++ units 19 ++ tail))
      with (clean (ones 16 ++ zeros (2 * 2) ++ ones (0 + 2)
                   ++ (false :: false :: units 18 ++ tail))).
    apply (move 16 1 47 0); [reflexivity | lia]. }
  change (clean (units 1 ++ ones (47 + 5) ++ false :: false :: ones 0
                 ++ false :: false :: units 18 ++ tail))
    with (clean (ones 2 ++ zeros (2 * 1) ++ ones (50 + 2) ++ (zeros 4 ++ units 18 ++ tail))).
  rewrite (move 2 0 7 50); [reflexivity | reflexivity | lia].
Qed.

(* The 25 triplings that follow.  P ends as 15 * 3^25 - 3, the counter is
   used up, and the gap in front of the 18 units is now 6. *)
Theorem tripling_chain :
  steps (5656 + chcost 25 12) c0
  = clean (ones (tri 25 12) ++ zeros 6 ++ units 18 ++ tail).
Proof.
  eapply run. { apply at_5656. }
  change 50 with (2 * 25).
  rewrite chain by lia. reflexivity.
Qed.

Lemma tri_25 : tri 25 12 + 3 = 15 * 3 ^ 25.
Proof. apply tri_closed. Qed.

Print Assumptions move.
Print Assumptions halts_gen.
Print Assumptions tripling_chain.
