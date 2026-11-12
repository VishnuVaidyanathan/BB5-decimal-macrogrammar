(* ====================================================================== *)
(*  BB7Halts.v                                                            *)
(*                                                                        *)
(*  The claimed BB(7) champion                                            *)
(*      1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB                  *)
(*  halts when started on a blank tape.                                   *)
(*                                                                        *)
(*  This file builds on BB7Moves.v, which proves                          *)
(*    start     : after 3954 steps the tape is clean, with 19 units       *)
(*    move      : one macro move, for every gap width                     *)
(*    halts_gen : the gate halts the machine at the last 1                *)
(*  What is added here is the induction that joins them: the run uses     *)
(*  only moves until the gate.  The paper version of the argument is      *)
(*  bb7_halting_induction.pdf.                                            *)
(*                                                                        *)
(*  Numbers are written by their halves, so that "even" needs no side     *)
(*  condition: the working block is 2*q ones, a counter is 2*h+2 ones.    *)
(*                                                                        *)
(*  Coq 8.18, standard library only, no axioms.                           *)
(* ====================================================================== *)

Require Import List Lia Arith.
Import ListNotations.
Require Import BB7Moves.

(* ---------- reaching one configuration from another ---------- *)

Definition reaches (c c' : conf) : Prop := exists n, steps n c = c'.

Lemma reaches_refl : forall c, reaches c c.
Proof. intros c. exists 0. reflexivity. Qed.

Lemma reaches_trans : forall a b c, reaches a b -> reaches b c -> reaches a c.
Proof. intros a b c [n H] [m H']. exists (n + m). rewrite steps_add, H. exact H'. Qed.

Lemma zeros_add : forall a b (l : list bool), zeros (a + b) ++ l = zeros a ++ zeros b ++ l.
Proof. intros. rewrite repeat_app, <- app_assoc. reflexivity. Qed.

(* ---------- the move, restated with halves ---------- *)

(* gap of width 1: the block triples, the counter loses 2 *)
Lemma move1 : forall q z R,
  steps (wcost (2 * q) 0 (6 * q + 1))
    (clean (ones (2 * q) ++ zeros 2 ++ ones (z + 2) ++ R))
  = clean (ones (2 * (3 * q + 3)) ++ zeros 2 ++ ones z ++ R).
Proof.
  intros q z R. etransitivity; [ apply move; lia | ].
  replace (6 * q + 1 + 5) with (2 * (3 * q + 3)) by lia. reflexivity.
Qed.

(* gap of width S j': the tripled block becomes a counter, j' units are planted *)
Lemma moveJ : forall q j' h R, 2 * S j' <= 6 * q + 2 ->
  steps (wcost (2 * q) j' (6 * q + 3 - 2 * S j'))
    (clean (ones (2 * q) ++ zeros (2 * S j') ++ ones (2 * h + 2) ++ R))
  = clean (units j' ++ ones (2 * (3 * q + 3 - S j') + 2) ++ zeros 2 ++ ones (2 * h) ++ R).
Proof.
  intros q j' h R Hr. etransitivity; [ apply move; lia | ].
  replace (6 * q + 3 - 2 * S j' + 5) with (2 * (3 * q + 3 - S j') + 2) by lia. reflexivity.
Qed.

(* ---------- consume, width 1 ---------- *)

(* A counter behind a single gap is used up by triplings.
   The next gap grows by 2. *)
Lemma consume1 : forall h q g R, 1 <= q ->
  exists q',
    reaches (clean (ones (2 * q) ++ zeros 2 ++ ones (2 * h + 2) ++ zeros g ++ R))
            (clean (ones (2 * q') ++ zeros (g + 2) ++ R))
    /\ 3 * q + 3 <= q'
    /\ (1 <= h -> 9 * q + 12 <= q')
    /\ (2 <= h -> 27 * q + 39 <= q').
Proof.
  induction h as [|h IH]; intros q g R Hq.
  - exists (3 * q + 3). split; [ | lia ].
    exists (wcost (2 * q) 0 (6 * q + 1)).
    etransitivity; [ apply (move1 q 0 (zeros g ++ R)) | ].
    replace (g + 2) with (2 + g) by lia. reflexivity.
  - destruct (IH (3 * q + 3) g R ltac:(lia)) as [q' [Hre [H1 [H2 H3]]]].
    exists q'. split; [ | lia ].
    eapply reaches_trans; [ | exact Hre ].
    exists (wcost (2 * q) 0 (6 * q + 1)).
    replace (2 * S h + 2) with (2 * h + 2 + 2) by lia.
    apply move1.
Qed.

(* ---------- consume, any width ---------- *)

(* The statement for a gap of width j. *)
Definition consume_stmt (j : nat) : Prop :=
  forall h q g R, 1 <= q -> 2 * j <= 6 * q + 2 ->
  exists q',
    reaches (clean (ones (2 * q) ++ zeros (2 * j) ++ ones (2 * h + 2) ++ zeros g ++ R))
            (clean (ones (2 * q') ++ zeros (g + 2 * j) ++ R))
    /\ 6 <= q'
    /\ ((2 <= j \/ 2 <= h) -> 66 <= q').

Lemma consume_width1 : consume_stmt 1.
Proof.
  intros h q g R Hq _.
  destruct (consume1 h q g R Hq) as [q' [Hre [H1 [H2 H3]]]].
  exists q'. split; [ exact Hre | lia ].
Qed.

(* Planted units.  If consume holds for all widths up to J, then a row of
   t units "11 00" behind a gap of width a+1 is used up one after another,
   at widths a+1, a+2, ..., a+t. *)
Lemma planted : forall J,
  (forall j, 1 <= j -> j <= J -> consume_stmt j) -> J <= 199 ->
  forall t a q Rest, a + t <= J -> 1 <= q -> (1 <= a -> 6 <= q) -> (2 <= a -> 66 <= q) ->
  exists q',
    reaches (clean (ones (2 * q) ++ zeros (2 * (a + 1)) ++ units t ++ Rest))
            (clean (ones (2 * q') ++ zeros (2 * (a + t + 1)) ++ Rest))
    /\ 1 <= q'
    /\ (1 <= a + t -> 6 <= q')
    /\ (2 <= a + t -> 66 <= q').
Proof.
  intros J C HJ. induction t as [|t IH]; intros a q Rest Hat Hq H6 H66.
  - exists q. split; [ | lia ].
    replace (a + 0 + 1) with (a + 1) by lia. apply reaches_refl.
  - destruct (C (a + 1) ltac:(lia) ltac:(lia) 0 q 2 (units t ++ Rest) Hq ltac:(lia))
      as [q1 [Hre1 [Hq1 Hq1']]].
    destruct (IH (a + 1) q1 Rest ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as [q' [Hre2 [Hb1 [Hb2 Hb3]]]].
    exists q'. split; [ | lia ].
    eapply reaches_trans; [ exact Hre1 | ].
    replace (2 + 2 * (a + 1)) with (2 * (a + 1 + 1)) by lia.
    replace (a + S t + 1) with (a + 1 + t + 1) by lia.
    exact Hre2.
Qed.

(* One round at width j = S (S n): the first move, then the planted units,
   then the big counter (at width j - 1).  The counter of the round loses 2. *)
Lemma round : forall n,
  (forall j, 1 <= j -> j <= S n -> consume_stmt j) -> S (S n) <= 199 ->
  forall h q g R, 1 <= q -> 2 * S (S n) <= 6 * q + 2 ->
  exists q2,
    reaches (clean (ones (2 * q) ++ zeros (2 * S (S n)) ++ ones (2 * h + 2) ++ zeros g ++ R))
            (clean (ones (2 * q2) ++ zeros (2 * S (S n)) ++ ones (2 * h) ++ zeros g ++ R))
    /\ 66 <= q2.
Proof.
  intros n C Hn h q g R Hq Hr.
  (* the planted units, met by the fresh block of 2 = 2*1 *)
  destruct (planted (S n) C ltac:(lia) n 0 1
              (ones (2 * (3 * q + 3 - S (S n)) + 2) ++ zeros 2 ++ ones (2 * h) ++ zeros g ++ R)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as [q1 [Hre1 [Hq1 [Hq1a Hq1b]]]].
  (* the big counter N = 2*(3q+3-j)+2, at width S n *)
  destruct (C (S n) ltac:(lia) ltac:(lia) (3 * q + 3 - S (S n)) q1 2
              (ones (2 * h) ++ zeros g ++ R) Hq1 ltac:(lia))
    as [q2 [Hre2 [Hq2 Hq2']]].
  exists q2. split; [ | lia ].
  eapply reaches_trans.
  { exists (wcost (2 * q) (S n) (6 * q + 3 - 2 * S (S n))).
    apply (moveJ q (S n) h (zeros g ++ R) Hr). }
  eapply reaches_trans; [ exact Hre1 | ].
  replace (2 * (0 + n + 1)) with (2 * S n) by lia.
  replace (2 * S (S n)) with (2 + 2 * S n) by lia.
  exact Hre2.
Qed.

(* Consume for every width up to 199, by induction on the width. *)
Lemma consume_all : forall n j, 1 <= j -> j <= n -> n <= 199 -> consume_stmt j.
Proof.
  induction n as [|n IHn]; intros j Hj Hjn Hn; [ lia | ].
  destruct (Nat.eq_dec j (S n)) as [-> | Hne]; [ | apply IHn; lia ].
  destruct n as [|n]; [ exact consume_width1 | ].
  assert (C : forall j, 1 <= j -> j <= S n -> consume_stmt j)
    by (intros j' H1 H2; apply IHn; lia).
  intros h. induction h as [|h IHh]; intros q g R Hq Hr.
  - destruct (round n C Hn 0 q g R Hq Hr) as [q2 [Hre Hq2]].
    exists q2. split; [ | lia ].
    eapply reaches_trans; [ exact Hre | ].
    replace (g + 2 * S (S n)) with (2 * S (S n) + g) by lia.
    rewrite zeros_add. apply reaches_refl.
  - destruct (round n C Hn (S h) q g R Hq Hr) as [q2 [Hre Hq2]].
    destruct (IHh q2 g R ltac:(lia) ltac:(lia)) as [q' [Hre' [H6 H66]]].
    exists q'. split; [ | split; [ exact H6 | intros _; apply H66; lia ] ].
    eapply reaches_trans; [ exact Hre | ].
    replace (2 * S h) with (2 * h + 2) by lia. exact Hre'.
Qed.

Theorem consume : forall j, 1 <= j -> j <= 199 -> consume_stmt j.
Proof. intros j H1 H2. exact (consume_all 199 j H1 H2 (le_n _)). Qed.

(* ---------- the theorem ---------- *)

(* A clean tape with an even block of at least 12, a double gap, u >= 1 units and
   the last 1 leads to the gate: one block, a gap of width u+2, the last 1. *)
Theorem units_to_gate : forall u q k, 1 <= u -> u <= 197 -> 6 <= q ->
  exists q',
    reaches (clean (ones (2 * q) ++ zeros 4 ++ units u ++ true :: zeros k))
            (clean (ones (2 * q') ++ zeros (2 * (u + 2)) ++ true :: zeros k))
    /\ 66 <= q'.
Proof.
  intros u q k Hu1 Hu Hq.
  destruct (planted 199 consume (le_n _) u 1 q (true :: zeros k)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as [q' [Hre [H1 [H6 H66]]]].
  exists q'. split; [ | lia ].
  replace (2 * (u + 2)) with (2 * (1 + u + 1)) by lia. exact Hre.
Qed.

(* ... and from there the machine halts. *)
Theorem units_halt : forall u q k, 1 <= u -> u <= 197 -> 6 <= q ->
  exists n, state (steps n (clean (ones (2 * q) ++ zeros 4 ++ units u ++ true :: zeros k))) = Hlt.
Proof.
  intros u q k Hu1 Hu Hq.
  destruct (units_to_gate u q k Hu1 Hu Hq) as [q' [[n Hn] Hq']].
  exists (n + S (hcost (2 * q') (S u) (3 * q' - u - 1) + 5)).
  rewrite steps_add, Hn.
  replace (2 * (u + 2)) with (2 * S (S u)) by lia.
  apply halts_gen. lia.
Qed.

(* The claimed BB(7) champion halts from a blank tape. *)
Theorem champion_halts : exists n, state (steps n c0) = Hlt.
Proof.
  destruct (units_halt 19 8 3 ltac:(lia) ltac:(lia) ltac:(lia)) as [n Hn].
  exists (3954 + n). rewrite steps_add, start. exact Hn.
Qed.

(* The same, with the shape of the last tape: one block of 2*q' ones,
   a gap of 42 cells (width 21), and the last 1. *)
Theorem champion_gate : exists n q',
  steps n c0 = clean (ones (2 * q') ++ zeros 42 ++ tail) /\ 66 <= q'.
Proof.
  destruct (units_to_gate 19 8 3 ltac:(lia) ltac:(lia) ltac:(lia)) as [q' [[n Hn] Hq']].
  exists (3954 + n), q'. split; [ | exact Hq' ].
  rewrite steps_add, start. exact Hn.
Qed.

Print Assumptions champion_halts.
