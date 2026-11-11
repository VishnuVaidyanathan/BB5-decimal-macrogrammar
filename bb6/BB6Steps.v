(* BB(6) champion  1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE
   Exact step counts for its moves.

   The tape shapes and the rules "which shape reaches which shape" are due to
   mxdys (busycoq, verify/SOBCv5.v).  The same transition table appears there,
   with renamed states, as the modules TM62 and TM63, started in this
   machine's states D and B.  The run from state A proved here joins the run
   of TM63 after 15 and 9 steps (busycoq Eqv_v2.TM872); TM62 is a different
   run under the same rules.  That proof has no step counts.  This file
   proves the same moves again in a small self-contained model and adds the
   exact number of steps of each move.

   Vishnu Vaidyanathan.  Coq 8.18, no axioms. *)

Require Import List Lia Arith.
Set Warnings "-abstract-large-number".
Import ListNotations.

(* ---------- 1. The machine ---------- *)

Inductive St := A | B | C | D | E | F | Z.

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
  | A, false => act true  true  B l r   (* A0 -> 1RB *)
  | A, true  => act true  true  A l r   (* A1 -> 1RA *)
  | B, false => act true  true  C l r   (* B0 -> 1RC *)
  | B, true  => act true  true  Z l r   (* B1 -> 1RZ (halt) *)
  | C, false => act true  false D l r   (* C0 -> 1LD *)
  | C, true  => act false true  F l r   (* C1 -> 0RF *)
  | D, false => act true  true  A l r   (* D0 -> 1RA *)
  | D, true  => act false false E l r   (* D1 -> 0LE *)
  | E, false => act false false D l r   (* E0 -> 0LD *)
  | E, true  => act true  true  C l r   (* E1 -> 1RC *)
  | F, false => act true  true  A l r   (* F0 -> 1RA *)
  | F, true  => act false true  E l r   (* F1 -> 0RE *)
  | Z, _     => c
  end.

Fixpoint steps (n : nat) (c : conf) : conf :=
  match n with
  | 0   => c
  | S k => steps k (step c)
  end.

Lemma steps_add : forall a b c, steps (a + b) c = steps b (steps a c).
Proof. induction a as [| a IH]; intros b c; simpl; [reflexivity | apply IH]. Qed.

(* run p steps, then continue *)
Lemma run : forall p q c c' c'',
  steps p c = c' -> steps q c' = c'' -> steps (p + q) c = c''.
Proof. intros. rewrite steps_add. congruence. Qed.

(* ---------- 2. Blocks ---------- *)

Notation ones := (repeat true).

Lemma ones_snoc : forall k (l : list bool), ones k ++ true :: l = true :: ones k ++ l.
Proof. induction k; intros l; simpl; [reflexivity | rewrite IHk; reflexivity]. Qed.

Lemma ones_add : forall a b (l : list bool), ones (a + b) ++ l = ones a ++ ones b ++ l.
Proof. intros. rewrite repeat_app, <- app_assoc. reflexivity. Qed.

(* (1 0 0)^n, nearest first *)
Fixpoint u100 (n : nat) : list bool :=
  match n with 0 => [] | S k => true :: false :: false :: u100 k end.

(* (0 0 1)^n, nearest first *)
Fixpoint u001 (n : nat) : list bool :=
  match n with 0 => [] | S k => false :: false :: true :: u001 k end.

Lemma u100_snoc : forall n l,
  u100 n ++ true :: false :: false :: l = true :: false :: false :: u100 n ++ l.
Proof. induction n; intros l; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma u100_u001 : forall n l, u100 n ++ true :: l = true :: u001 n ++ l.
Proof. induction n; intros l; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(* ---------- 3. Three basic moves ---------- *)

(* A walks right over ones (digit 1 of the transcript). *)
Lemma sweepA : forall k l x r,
  steps (S k) (A, l, true, ones k ++ x :: r) = (A, ones (S k) ++ l, x, r).
Proof.
  induction k as [| k IH]; intros l x r.
  - reflexivity.
  - change (steps (S (S k)) (A, l, true, ones (S k) ++ x :: r))
      with (steps (S k) (A, true :: l, true, ones k ++ x :: r)).
    rewrite IH. rewrite ones_snoc. reflexivity.
Qed.

Lemma sweepA_end : forall k l,
  steps (S k) (A, l, true, ones k) = (A, ones (S k) ++ l, false, []).
Proof.
  induction k as [| k IH]; intros l.
  - reflexivity.
  - change (steps (S (S k)) (A, l, true, ones (S k)))
      with (steps (S k) (A, true :: l, true, ones k)).
    rewrite IH. rewrite ones_snoc. reflexivity.
Qed.

(* The word 479 (C0 D1 E1): a 0 under the head moves one cell left. *)
Lemma hole : forall k l r,
  steps (3 * k) (C, ones k ++ true :: l, false, r) = (C, true :: l, false, ones k ++ r).
Proof.
  induction k as [| k IH]; intros l r.
  - reflexivity.
  - replace (3 * S k) with (3 + 3 * k) by lia. rewrite steps_add.
    change (ones (S k) ++ true :: l) with (true :: ones k ++ true :: l).
    rewrite ones_snoc.
    change (steps 3 (C, true :: true :: ones k ++ l, false, r))
      with (C, true :: ones k ++ l, false, true :: r).
    rewrite <- ones_snoc. rewrite IH. rewrite ones_snoc. reflexivity.
Qed.

(* The word 5b9 (C1 F1 E1): 1 1 1 becomes 0 0 1, head moves three cells right. *)
Lemma flip : forall k l x r,
  steps (3 * S k) (C, l, true, ones (3 * k + 2) ++ x :: r) = (C, u100 (S k) ++ l, x, r).
Proof.
  induction k as [| k IH]; intros l x r.
  - reflexivity.
  - replace (3 * S (S k)) with (3 + 3 * S k) by lia. rewrite steps_add.
    replace (3 * S k + 2) with (S (S (S (3 * k + 2)))) by lia.
    change (steps 3 (C, l, true, ones (S (S (S (3 * k + 2)))) ++ x :: r))
      with (C, true :: false :: false :: l, true, ones (3 * k + 2) ++ x :: r).
    rewrite IH. change (u100 (S (S k)) ++ l) with (true :: false :: false :: u100 (S k) ++ l).
    rewrite <- u100_snoc. reflexivity.
Qed.

(* ---------- 4. The tick ---------- *)

(* run a fixed number of steps by computation *)
Ltac comp := eapply run; [ cbn [steps step act app repeat u100]; reflexivity | ].
(* use a lemma for the next stretch *)
Ltac by_lemma L := eapply run; [ apply L | ].
(* rewrite the current configuration into an equal one *)
Ltac shape c' := match goal with |- steps _ ?c = _ => replace c with c' end.
Ltac fin := cbn [steps step act app repeat u100]; rewrite ?app_nil_r; reflexivity.

(* Right side of the head in the shape S0: 0 11100 (111)^(1+b). *)
Definition R0 (b : nat) : list bool :=
  false :: true :: true :: true :: false :: false :: ones (3 * b + 3).

(* Common second half of every tick.  J is the borrow length. *)
Lemma tick_tail : forall J b X,
  steps (12 * b + 3 * J + 36)
    (C, ones 4 ++ X, true, ones (3 * J + 2) ++ false :: false :: ones (3 * b + 3))
  = (C, true :: true :: u100 J ++ ones 4 ++ X, false,
     false :: false :: true :: ones (3 * b + 5)).
Proof.
  intros J b X.
  replace (12 * b + 3 * J + 36)
    with (3 * S J + (8 + (S (3 * b + 2) + (2 + (3 * (3 * b + 5) + 5))))) by lia.
  replace (3 * b + 3) with (S (3 * b + 2)) by lia.
  by_lemma flip.          (* (5b9)^(J+1) *)
  comp.                   (* 4786025a *)
  by_lemma sweepA_end.    (* 1^(3b+3) *)
  comp.                   (* 02 *)
  shape (C, ones (3 * b + 5) ++ true :: false :: true :: true :: true :: u100 J ++ ones 4 ++ X,
         false, @nil bool).
  2: { replace (3 * b + 5) with (S (S (S (3 * b + 2)))) by lia. reflexivity. }
  by_lemma hole.          (* (479)^(3b+5) *)
  fin.                    (* 47879 *)
Qed.

(* Tick with no borrow: the last counter digit is 100. *)
Lemma tick0 : forall b X,
  steps (12 * b + 48) (E, false :: true :: X, false, R0 b)
  = (E, true :: true :: X, true, R0 (S b)).
Proof.
  intros b X. unfold R0.
  replace (12 * b + 48) with (4 + ((12 * b + 3 * 0 + 36) + (3 * 2 + 2))) by lia.
  replace (3 * S b + 3) with (S (3 * b + 5)) by lia.
  comp.                                 (* 8602 *)
  by_lemma (tick_tail 0 b X).
  by_lemma (hole 2 (ones 3 ++ X)).      (* (479)^2 *)
  fin.                                  (* 47 *)
Qed.

(* Tick with borrow j+1: the counter ends in 100 (111)^(j+1). *)
Lemma tickS : forall j b X,
  steps (12 * b + 12 * S j + 48)
    (E, ones (3 * j + 2) ++ false :: false :: true :: X, true, R0 b)
  = (E, false :: u100 j ++ ones 4 ++ X, false, R0 (S b)).
Proof.
  intros j b X. unfold R0.
  replace (12 * b + 12 * S j + 48)
    with (1 + (3 * (3 * j + 2) + (6 + ((12 * b + 3 * S j + 36) + (3 * 2 + 2))))) by lia.
  replace (3 * S b + 3) with (S (3 * b + 5)) by lia.
  comp.                                 (* 9 *)
  shape (C, ones (3 * j + 2) ++ true :: false :: false :: true :: X, false,
         true :: true :: true :: false :: false :: ones (3 * b + 3)).
  2: { rewrite ones_snoc. reflexivity. }
  by_lemma hole.                        (* (479)^(3j+2) *)
  comp.                                 (* 478602 *)
  shape (C, ones 4 ++ X, true, ones (3 * S j + 2) ++ false :: false :: ones (3 * b + 3)).
  2: { replace (3 * S j + 2) with ((3 * j + 2) + 3) by lia. rewrite ones_add. reflexivity. }
  by_lemma (tick_tail (S j) b X).
  by_lemma (hole 2 (false :: false :: u100 j ++ ones 4 ++ X)).   (* (479)^2 *)
  fin.                                  (* 47 *)
Qed.

(* ---------- 5. The binary counter ---------- *)

(* A counter is a list of bits, lowest bit first.  On the tape, bit 1 is the
   digit 100 and bit 0 is the digit 111 (read left to right); [enc] gives the
   cells nearest first, so 100 becomes 0 0 1. *)
Fixpoint enc (bs : list bool) : list bool :=
  match bs with
  | [] => []
  | true  :: t => false :: false :: true :: enc t
  | false :: t => true :: true :: true :: enc t
  end.

Lemma enc_app : forall x y, enc (x ++ y) = enc x ++ enc y.
Proof. induction x as [| [|] x IH]; intros y; simpl; [reflexivity | rewrite IH .. ]; reflexivity. Qed.

Lemma enc_falses : forall j, enc (repeat false j) = ones (3 * j).
Proof.
  induction j; [reflexivity |].
  replace (3 * S j) with (S (S (S (3 * j)))) by lia. simpl. rewrite IHj. reflexivity.
Qed.

Lemma enc_trues : forall j, enc (repeat true j) = u001 j.
Proof. induction j; simpl; [reflexivity | rewrite IHj; reflexivity]. Qed.

Lemma rep_snoc : forall (x : bool) k l, repeat x (S k) ++ l = repeat x k ++ x :: l.
Proof. induction k; intros l; [reflexivity |]. simpl in *. rewrite IHk. reflexivity. Qed.

(* Head in state E on the first cell of W; the rest of W is to its left. *)
Definition cfgE (W r : list bool) : conf :=
  match W with
  | h :: l => (E, l, h, r)
  | []     => (E, [], false, r)
  end.

(* One tick: the counter goes down by one (borrow length J), the right block
   grows by one 111.  Exactly 12b + 12J + 48 steps.  (mxdys: Inc0) *)
Theorem tick : forall J hi X b,
  steps (12 * b + 12 * J + 48)
    (cfgE (enc (repeat false J ++ true :: hi) ++ X) (R0 b))
  = cfgE (enc (repeat true J ++ false :: hi) ++ X) (R0 (S b)).
Proof.
  intros [| j] hi X b.
  - replace (12 * b + 12 * 0 + 48) with (12 * b + 48) by lia. apply tick0.
  - replace (enc (repeat false (S j) ++ true :: hi) ++ X)
      with (true :: ones (3 * j + 2) ++ false :: false :: true :: (enc hi ++ X)).
    2: { rewrite enc_app, enc_falses, <- app_assoc.
         replace (3 * S j) with (S (3 * j + 2)) by lia. reflexivity. }
    replace (enc (repeat true (S j) ++ false :: hi) ++ X)
      with (false :: false :: u100 j ++ ones 4 ++ (enc hi ++ X)).
    2: { rewrite enc_app, enc_trues, <- app_assoc. simpl.
         rewrite u100_u001. reflexivity. }
    apply tickS.
Qed.

(* N k = 2^k - 1 *)
Fixpoint Nk (k : nat) : nat :=
  match k with 0 => 0 | S k' => 2 * Nk k' + 1 end.

Lemma Nk_pow : forall k, Nk k + 1 = 2 ^ k.
Proof. induction k; simpl in *; lia. Qed.

(* Steps to count a k-bit counter down from all ones to zero,
   starting with right block b. *)
Fixpoint T (k b : nat) : nat :=
  match k with
  | 0 => 0
  | S k' => T k' b + ((12 * (b + Nk k') + 12 * k' + 48) + T k' (S (b + Nk k')))
  end.

Theorem full_ticks : forall k hi X b,
  steps (T k b) (cfgE (enc (repeat true k ++ hi) ++ X) (R0 b))
  = cfgE (enc (repeat false k ++ hi) ++ X) (R0 (b + Nk k)).
Proof.
  induction k as [| k IH]; intros hi X b.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - cbn [T]. rewrite rep_snoc.
    eapply run. { apply IH. }
    eapply run. { apply tick. }
    rewrite IH. rewrite <- rep_snoc.
    cbn [Nk]. replace (S (b + Nk k) + Nk k) with (b + (2 * Nk k + 1)) by lia.
    reflexivity.
Qed.

(* Closed form: with N = 2^k - 1,  T k b = 6N^2 + 54N + 12bN - 12k. *)
Theorem T_closed : forall k b,
  T k b + 12 * k = 6 * Nk k * Nk k + 54 * Nk k + 12 * b * Nk k.
Proof.
  induction k as [| k IH]; intros b.
  - cbn [T Nk]. lia.
  - cbn [T Nk]. pose proof (IH b) as H1. pose proof (IH (S (b + Nk k))) as H2. nia.
Qed.

Corollary full_ticks0 : forall k X b,
  steps (T k b) (cfgE (enc (repeat true k) ++ X) (R0 b))
  = cfgE (ones (3 * k) ++ X) (R0 (b + Nk k)).
Proof.
  intros k X b. pose proof (full_ticks k [] X b) as H.
  rewrite !app_nil_r in H. rewrite enc_falses in H. exact H.
Qed.

(* ---------- 6. Pieces shared by the big moves ---------- *)

Lemma flip_end : forall k l,
  steps (3 * S k) (C, l, true, ones (3 * k + 2)) = (C, u100 (S k) ++ l, false, []).
Proof.
  induction k as [| k IH]; intros l.
  - reflexivity.
  - replace (3 * S (S k)) with (3 + 3 * S k) by lia. rewrite steps_add.
    replace (3 * S k + 2) with (S (S (S (3 * k + 2)))) by lia.
    change (steps 3 (C, l, true, ones (S (S (S (3 * k + 2))))))
      with (C, true :: false :: false :: l, true, ones (3 * k + 2)).
    rewrite IH. change (u100 (S (S k)) ++ l) with (true :: false :: false :: u100 (S k) ++ l).
    rewrite <- u100_snoc. reflexivity.
Qed.

(* The marker 10, then q ones, head on the last cell.  The head walks left
   through the ones, turns the digit 100 before the marker into 111 and stops. *)
Lemma prefix : forall q Y b,
  steps (3 * q + 6)
    (cfgE (ones q ++ false :: true :: false :: false :: true :: Y) (R0 b))
  = (C, ones 4 ++ Y, false,
     false :: ones (q + 3) ++ false :: false :: ones (3 * b + 3)).
Proof.
  intros [| q] Y b; unfold R0.
  - reflexivity.
  - replace (3 * S q + 6) with (1 + (3 * q + 8)) by lia.
    replace (S q + 3) with (S (q + 3)) by lia.
    cbn [cfgE app repeat]. rewrite (ones_add q 3).
    comp.
    shape (C, ones q ++ true :: false :: true :: false :: false :: true :: Y, false,
           true :: true :: true :: false :: false :: ones (3 * b + 3)).
    2: { rewrite ones_snoc. reflexivity. }
    by_lemma hole.
    fin.
Qed.

(* After the right block has been turned into (001)^(b+1): close the move. *)
Lemma finish : forall b L',
  steps 29 (C, u100 (S b) ++ true :: L', false, [])
  = cfgE (enc (repeat true b) ++ L') (R0 0).
Proof.
  intros b L'.
  change 29 with (10 + (3 * 2 + (5 + (3 * 2 + 2)))).
  comp.
  by_lemma (hole 2 (false :: true :: true :: true :: u100 b ++ true :: L')).
  comp.
  destruct b as [| b].
  - by_lemma (hole 2 L'). destruct L'; reflexivity.
  - by_lemma (hole 2 (false :: false :: u100 b ++ true :: L')).
    cbn [steps step act app repeat u100 enc cfgE].
    rewrite u100_u001, enc_trues. reflexivity.
Qed.

(* ---------- 7. The epoch ---------- *)

(* Epoch load: the outer counter goes down by one (borrow j0), and the right
   block (111)^(1+b) is loaded into the inner counter as the value 2^b - 1.
   q is the number of ones after the marker 10.  (First half of mxdys' Rst.) *)
Theorem load : forall q j0 hi0 H b,
  steps (4 * q + 12 * j0 + 3 * b + 63)
    (cfgE (ones q ++ false :: true :: false :: false :: true ::
           enc (repeat false j0 ++ true :: hi0) ++ H) (R0 b))
  = cfgE (enc (repeat true b) ++ ones (q + 5) ++ false :: true :: false :: false :: true ::
          enc (repeat true j0 ++ false :: hi0) ++ H) (R0 0).
Proof.
  intros q j0 hi0 H b.
  replace (4 * q + 12 * j0 + 3 * b + 63)
    with ((3 * q + 6) + (3 * (3 * j0 + 3) + (6 + (3 * S j0 + (2 + (S (q + 2) +
          (2 + (3 * S b + 29)))))))) by lia.
  by_lemma prefix.
  replace (q + 3) with (S (q + 2)) by lia.
  replace (3 * b + 3) with (S (3 * b + 2)) by lia.
  rewrite !enc_app, enc_falses, enc_trues, <- !app_assoc.
  set (X := enc hi0 ++ H).
  shape (C, ones (3 * j0 + 3) ++ true :: false :: false :: true :: X, false,
         false :: ones (S (q + 2)) ++ false :: false :: ones (S (3 * b + 2))).
  2: { rewrite ones_snoc. replace (3 * j0 + 3) with (3 + 3 * j0) by lia.
       rewrite ones_add. reflexivity. }
  by_lemma hole.
  comp.
  shape (C, ones 4 ++ X, true,
         ones (3 * j0 + 2) ++ true :: false :: ones (S (q + 2)) ++ false :: false :: ones (S (3 * b + 2))).
  2: { rewrite ones_snoc. replace (3 * j0 + 3) with (S (3 * j0 + 2)) by lia. reflexivity. }
  by_lemma flip.
  comp.
  by_lemma sweepA.
  comp.
  by_lemma flip_end.
  rewrite finish. rewrite !enc_trues. subst X.
  f_equal. f_equal.
  replace (q + 5) with (S (S (S (q + 2)))) by lia.
  cbn [app repeat u100 enc]. rewrite ones_snoc. rewrite u100_u001. reflexivity.
Qed.

(* The left end of the tape, nearest first: 1110 11 read left to right. *)
Definition hdr : list bool := [true; true; false; true; true; true].

(* The shape S1 at the start of an epoch (mxdys: S1 len0 a0 m a 0 b).
   bits0 is the outer counter, q = m + 3a is the number of ones after the
   marker 10, and the right block is (111)^(1+b). *)
Definition S1c (bits0 : list bool) (q b : nat) : conf :=
  cfgE (ones q ++ false :: true :: false :: false :: true :: enc bits0 ++ hdr) (R0 b).

(* One epoch = load + 2^b - 1 ticks.  (mxdys: Rst2, Rst1, Rst0.)
   q becomes q + 3b + 5 and b becomes 2^b - 1. *)
Definition ecost (q b j0 : nat) : nat := 4 * q + 12 * j0 + 3 * b + 63 + T b 0.

Theorem epoch : forall q j0 hi0 b,
  steps (ecost q b j0) (S1c (repeat false j0 ++ true :: hi0) q b)
  = S1c (repeat true j0 ++ false :: hi0) (q + 3 * b + 5) (Nk b).
Proof.
  intros q j0 hi0 b. unfold ecost, S1c.
  eapply run. { apply load. }
  rewrite full_ticks0. cbn [Nat.add].
  replace (q + 3 * b + 5) with (3 * b + (q + 5)) by lia.
  rewrite (ones_add (3 * b) (q + 5)). reflexivity.
Qed.

(* ---------- 8. Restart and halt ---------- *)

(* When the outer counter is zero the head runs to the left end of the tape,
   rebuilds it, and comes back. *)
Lemma turn : forall L q b,
  steps (3 * q + 12 * L + 53) (S1c (repeat false L) q b)
  = (C, true :: true :: true :: u100 (S L) ++ [true; true; true; false; true; true; true],
     true, ones (q + 3) ++ false :: false :: ones (3 * b + 3)).
Proof.
  intros L q b. unfold S1c.
  replace (3 * q + 12 * L + 53)
    with ((3 * q + 6) + (3 * (3 * L + 5) + (5 + (3 * 1 + (12 + (3 * S (S L) + 6)))))) by lia.
  by_lemma prefix.
  rewrite enc_falses.
  shape (C, ones (3 * L + 5) ++ true :: [false; true; true; true], false,
         false :: ones (q + 3) ++ false :: false :: ones (3 * b + 3)).
  2: { assert (Hl : forall l, ones (3 * L + 5) ++ true :: l
                              = ones 4 ++ ones (3 * L) ++ true :: true :: l).
       { intros l. rewrite ones_snoc.
         change (true :: ones (3 * L + 5) ++ l) with (ones (S (3 * L + 5)) ++ l).
         replace (S (3 * L + 5)) with (4 + (3 * L + 2)) by lia.
         rewrite (ones_add 4), (ones_add (3 * L) 2). reflexivity. }
       rewrite Hl. reflexivity. }
  by_lemma hole.
  comp.
  by_lemma (hole 1 []).
  comp.
  shape (C, [true; true; true; false; true; true; true], true,
         ones (3 * S L + 2) ++ false :: ones (q + 3) ++ false :: false :: ones (3 * b + 3)).
  2: { replace (3 * S L + 2) with (3 * L + 5) by lia. reflexivity. }
  by_lemma flip.
  fin.
Qed.

(* Restart (mxdys: Rst1'): outer counter zero and q = 3a + 1. *)
Theorem restart : forall L a b,
  steps (12 * L + 12 * a + 3 * b + 97 + T b 0) (S1c (repeat false L) (3 * a + 1) b)
  = S1c (repeat true a ++ false :: repeat true (S L)) (3 * b + 2) (Nk b).
Proof.
  intros L a b.
  replace (12 * L + 12 * a + 3 * b + 97 + T b 0)
    with ((3 * (3 * a + 1) + 12 * L + 53) + (3 * S a + (6 + (3 * S b + (29 + T b 0))))) by lia.
  by_lemma turn.
  replace (3 * b + 3) with (S (3 * b + 2)) by lia.
  shape (C, true :: true :: true :: u100 (S L) ++ [true; true; true; false; true; true; true], true,
         ones (3 * a + 2) ++ true :: true :: false :: false :: ones (S (3 * b + 2))).
  2: { replace (3 * a + 1 + 3) with ((3 * a + 2) + 2) by lia.
       rewrite (ones_add (3 * a + 2) 2). reflexivity. }
  by_lemma flip.
  comp.
  by_lemma flip_end.
  by_lemma finish.
  rewrite full_ticks0. cbn [Nat.add]. unfold S1c.
  f_equal.
  rewrite (ones_add (3 * b) 2). rewrite enc_app, enc_trues.
  cbn [enc app repeat u001]. rewrite enc_trues. unfold hdr.
  rewrite <- !app_assoc. cbn [app]. rewrite !u100_u001. reflexivity.
Qed.

(* Halt (mxdys: Rst0'): outer counter zero and q = 3a.  After the stated
   number of steps the machine is in state B reading 1, which is its only
   halting pair; the next step halts. *)
Theorem last_move : forall L a b, exists l r,
  steps (12 * L + 12 * a + 59) (S1c (repeat false L) (3 * a) b) = (B, l, true, r).
Proof.
  intros L a b. eexists. eexists.
  replace (12 * L + 12 * a + 59)
    with ((3 * (3 * a) + 12 * L + 53) + (3 * S a + 3)) by lia.
  by_lemma turn.
  replace (3 * b + 3) with (S (3 * b + 2)) by lia.
  shape (C, true :: true :: true :: u100 (S L) ++ [true; true; true; false; true; true; true], true,
         ones (3 * a + 2) ++ true :: false :: false :: ones (S (3 * b + 2))).
  2: { replace (3 * a + 3) with ((3 * a + 2) + 1) by lia.
       rewrite (ones_add (3 * a + 2) 1). reflexivity. }
  by_lemma flip.
  cbn [steps step act app repeat u100]. reflexivity.
Qed.

(* The same, with the tape written out. *)
Lemma last_move_cfg : forall L a b,
  steps (12 * L + 12 * a + 59) (S1c (repeat false L) (3 * a) b)
  = (B, true :: true :: false :: u100 (S a) ++ true :: true :: true :: u100 (S L)
        ++ [true; true; true; false; true; true; true],
     true, ones (3 * b + 2)).
Proof.
  intros L a b.
  replace (12 * L + 12 * a + 59)
    with ((3 * (3 * a) + 12 * L + 53) + (3 * S a + 3)) by lia.
  by_lemma turn.
  replace (3 * b + 3) with (S (3 * b + 2)) by lia.
  shape (C, true :: true :: true :: u100 (S L) ++ [true; true; true; false; true; true; true], true,
         ones (3 * a + 2) ++ true :: false :: false :: ones (S (3 * b + 2))).
  2: { replace (3 * a + 3) with ((3 * a + 2) + 1) by lia.
       rewrite (ones_add (3 * a + 2) 1). reflexivity. }
  by_lemma flip.
  cbn [steps step act app repeat u100]. reflexivity.
Qed.

(* Number of ones on the tape. *)
Fixpoint cnt (l : list bool) : nat :=
  match l with
  | [] => 0
  | true :: t => S (cnt t)
  | false :: t => cnt t
  end.

Definition tape_ones (c : conf) : nat :=
  let '(_, l, h, r) := c in cnt l + (if h then 1 else 0) + cnt r.

Definition state (c : conf) : St := let '(s, _, _, _) := c in s.

Lemma cnt_app : forall x y, cnt (x ++ y) = cnt x + cnt y.
Proof. induction x as [| [|] x IH]; intros y; simpl; rewrite ?IH; reflexivity. Qed.

Lemma cnt_ones : forall n, cnt (ones n) = n.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma cnt_u100 : forall n, cnt (u100 n) = n.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(* One step later the machine has halted, with len0 + a + 3b + 16 ones. *)
Theorem halt_ones : forall L a b,
  state (steps (12 * L + 12 * a + 60) (S1c (repeat false L) (3 * a) b)) = Z /\
  tape_ones (steps (12 * L + 12 * a + 60) (S1c (repeat false L) (3 * a) b))
  = L + a + 3 * b + 16.
Proof.
  intros L a b.
  replace (12 * L + 12 * a + 60) with ((12 * L + 12 * a + 59) + 1) by lia.
  rewrite steps_add, last_move_cfg.
  replace (3 * b + 2) with (S (3 * b + 1)) by lia.
  cbn [steps step act repeat state tape_ones]. split; [reflexivity |].
  cbn [cnt u100 app]. rewrite !cnt_app, !cnt_u100, cnt_ones. cbn [cnt].
  rewrite cnt_app, cnt_u100. cbn [cnt]. lia.
Qed.

(* ---------- 9. From the blank tape ---------- *)

Definition c0 : conf := (A, [], false, []).

Lemma init821 :
  steps 821 c0
  = cfgE (enc (repeat true 6) ++ ones 2 ++ false :: true :: false :: false :: true ::
          enc (repeat true 3) ++ hdr) (R0 0).
Proof. vm_compute. reflexivity. Qed.

(* The blank tape reaches S1(3, 7, 2, 6, 63) after exactly 27,965 steps. *)
Theorem init : steps (821 + T 6 0) c0 = S1c (repeat true 3) 20 63.
Proof.
  eapply run. { apply init821. }
  rewrite full_ticks0. reflexivity.
Qed.

Lemma init_steps : 821 + T 6 0 = 27965.
Proof. reflexivity. Qed.

(* The first epoch.  It ends at step 27965 + 332 + T 63 0, and by T_closed
   T 63 0 = 6N^2 + 54N - 756 with N = 2^63 - 1.  As a number this is
   510423550381407695582443536695552928613. *)
Theorem first_epoch :
  steps ((821 + T 6 0) + ecost 20 63 0) c0
  = S1c [false; true; true] (20 + 3 * 63 + 5) (Nk 63).
Proof.
  eapply run. { apply init. }
  exact (epoch 20 0 [true; true] 63).
Qed.

(* ---------- 10. Many epochs ---------- *)

(* runF k q b: the low k bits of the outer counter go from all ones to all
   zeros (2^k - 1 epochs).  Returns (steps used, new q, new b). *)
Fixpoint runF (k q b : nat) : nat * nat * nat :=
  match k with
  | 0 => (0, q, b)
  | S k' =>
      let '(c1, q1, b1) := runF k' q b in
      let '(c3, q3, b3) := runF k' (q1 + 3 * b1 + 5) (Nk b1) in
      (c1 + (ecost q1 b1 k' + c3), q3, b3)
  end.

Theorem runF_ok : forall k q b hi c q' b',
  runF k q b = (c, q', b') ->
  steps c (S1c (repeat true k ++ hi) q b) = S1c (repeat false k ++ hi) q' b'.
Proof.
  induction k as [| k IH]; intros q b hi c q' b' H.
  - cbn [runF] in H. inversion H. reflexivity.
  - cbn [runF] in H.
    destruct (runF k q b) as [[c1 q1] b1] eqn:E1.
    destruct (runF k (q1 + 3 * b1 + 5) (Nk b1)) as [[c3 q3] b3] eqn:E3.
    inversion H; subst. rewrite rep_snoc.
    eapply run. { apply (IH _ _ (true :: hi) _ _ _ E1). }
    eapply run. { apply epoch. }
    rewrite (IH _ _ (false :: hi) _ _ _ E3). rewrite <- rep_snoc. reflexivity.
Qed.

(* runTop n z q b: the counter is z zeros (low) then n ones; all of it goes
   to zero. *)
Fixpoint runTop (n z q b : nat) : nat * nat * nat :=
  match n with
  | 0 => (0, q, b)
  | S n' =>
      let '(c2, q2, b2) := runF z (q + 3 * b + 5) (Nk b) in
      let '(c3, q3, b3) := runTop n' (S z) q2 b2 in
      (ecost q b z + (c2 + c3), q3, b3)
  end.

Theorem runTop_ok : forall n z q b hi c q' b',
  runTop n z q b = (c, q', b') ->
  steps c (S1c (repeat false z ++ repeat true n ++ hi) q b)
  = S1c (repeat false (z + n) ++ hi) q' b'.
Proof.
  induction n as [| n IH]; intros z q b hi c q' b' H.
  - cbn [runTop] in H. inversion H. rewrite Nat.add_0_r. reflexivity.
  - cbn [runTop] in H.
    destruct (runF z (q + 3 * b + 5) (Nk b)) as [[c2 q2] b2] eqn:E2.
    destruct (runTop n (S z) q2 b2) as [[c3 q3] b3] eqn:E3.
    inversion H; subst.
    eapply run. { apply (epoch q z (repeat true n ++ hi) b). }
    eapply run. { apply (runF_ok _ _ _ (false :: repeat true n ++ hi) _ _ _ E2). }
    rewrite <- rep_snoc.
    rewrite (IH _ _ _ hi _ _ _ E3).
    replace (S z + n) with (z + S n) by lia. reflexivity.
Qed.

Corollary runTop_ok0 : forall n z q b c q' b',
  runTop n z q b = (c, q', b') ->
  steps c (S1c (repeat false z ++ repeat true n) q b) = S1c (repeat false (z + n)) q' b'.
Proof.
  intros n z q b c q' b' H. pose proof (runTop_ok n z q b [] c q' b' H) as H'.
  rewrite !app_nil_r in H'. exact H'.
Qed.

(* ---------- 11. Remainders ---------- *)

Lemma Nk_Sodd : forall u, Nk (2 * u + 1) = 2 * Nk (2 * u) + 1.
Proof. intros u. replace (2 * u + 1) with (S (2 * u)) by lia. reflexivity. Qed.

Lemma Nk_even : forall t, exists s, Nk (2 * t) = 3 * s.
Proof.
  induction t as [| t [s Hs]].
  - exists 0. reflexivity.
  - replace (2 * S t) with (S (S (2 * t))) by lia. cbn [Nk]. rewrite Hs.
    exists (4 * s + 1). lia.
Qed.

Lemma Nk_odd : forall t, exists s, Nk (2 * t + 1) = 3 * s + 1.
Proof.
  intros t. destruct (Nk_even t) as [s Hs]. rewrite Nk_Sodd, Hs. exists (2 * s). lia.
Qed.

(* If b is odd it stays odd, and each epoch adds 2 to q modulo 6. *)
Lemma runF_inv : forall k q b u c q' b',
  b = 2 * u + 1 -> runF k q b = (c, q', b') ->
  (exists u', b' = 2 * u' + 1) /\ (exists t, q' = q + 2 * Nk k + 6 * t).
Proof.
  induction k as [| k IH]; intros q b u c q' b' Hb H.
  - cbn [runF] in H. inversion H; subst. split; [exists u | exists 0]; cbn [Nk]; lia.
  - cbn [runF] in H.
    destruct (runF k q b) as [[c1 q1] b1] eqn:E1.
    destruct (runF k (q1 + 3 * b1 + 5) (Nk b1)) as [[c3 q3] b3] eqn:E3.
    inversion H; subst.
    destruct (IH _ _ _ _ _ _ eq_refl E1) as [[u1 Hb1] [t1 Hq1]].
    subst b1. rewrite Nk_Sodd in E3.
    destruct (IH _ _ _ _ _ _ eq_refl E3) as [[u3 Hb3] [t3 Hq3]].
    split; [exists u3; exact Hb3 |].
    exists (t1 + t3 + u1 + 1). cbn [Nk]. lia.
Qed.

Lemma runTop_inv : forall n z q b u c q' b',
  b = 2 * u + 1 -> runTop n z q b = (c, q', b') ->
  (exists u', b' = 2 * u' + 1) /\ (exists t, q' = q + 2 * (Nk n * (Nk z + 1)) + 6 * t).
Proof.
  induction n as [| n IH]; intros z q b u c q' b' Hb H.
  - cbn [runTop] in H. inversion H; subst. split; [exists u | exists 0]; cbn [Nk]; lia.
  - cbn [runTop] in H.
    destruct (runF z (q + 3 * b + 5) (Nk b)) as [[c2 q2] b2] eqn:E2.
    destruct (runTop n (S z) q2 b2) as [[c3 q3] b3] eqn:E3.
    inversion H; subst. rewrite Nk_Sodd in E2.
    destruct (runF_inv _ _ _ _ _ _ _ eq_refl E2) as [[u2 Hb2] [t2 Hq2]].
    destruct (IH _ _ _ _ _ _ _ Hb2 E3) as [[u3 Hb3] [t3 Hq3]].
    split; [exists u3; exact Hb3 |].
    exists (t2 + t3 + u + 1). cbn [Nk] in *. nia.
Qed.

Lemma div3 : forall k r, r < 3 -> (3 * k + r) / 3 = k.
Proof. intros k r H. symmetry. apply (Nat.div_unique _ 3 k r); lia. Qed.

Lemma prod_mod : forall x y s3 s4, x = 3 * s3 + 1 -> y = 3 * s4 + 1 ->
  exists m, 2 * (x * (y + 1)) = 6 * m + 4.
Proof. intros; subst. exists (3 * s3 * s4 + 2 * s3 + s4). nia. Qed.

(* ---------- 12. The whole run ---------- *)

Lemma restart' : forall L a b q, q = 3 * a + 1 ->
  steps (12 * L + 12 * a + 3 * b + 97 + T b 0) (S1c (repeat false L) q b)
  = S1c (repeat true a ++ false :: repeat true (S L)) (3 * b + 2) (Nk b).
Proof. intros; subst; apply restart. Qed.

Lemma last_move' : forall L a b q, q = 3 * a -> exists l r,
  steps (12 * L + 12 * a + 59) (S1c (repeat false L) q b) = (B, l, true, r).
Proof. intros; subst; apply last_move. Qed.

(* The run up to the last tidy shape.  It follows mxdys' proof: 7 epochs,
   restart, a second pass, restart, a third pass.  Returns the number of
   steps used and the numbers (len0, a, b) of that last shape. *)
Definition final_params : nat * nat * nat * nat :=
  let '(c1, q1, b1) := runF 3 20 63 in
  let a1 := q1 / 3 in
  let r1 := 12 * 3 + 12 * a1 + 3 * b1 + 97 + T b1 0 in
  let '(c2, q2, b2) := runF a1 (3 * b1 + 2) (Nk b1) in
  let '(d2, p2, e2) := runTop 4 (S a1) q2 b2 in
  let a2 := p2 / 3 in
  let L2 := S a1 + 4 in
  let r2 := 12 * L2 + 12 * a2 + 3 * e2 + 97 + T e2 0 in
  let '(c3, q3, b3) := runF a2 (3 * e2 + 2) (Nk e2) in
  let '(d3, p3, e3) := runTop (S L2) (S a2) q3 b3 in
  ((821 + T 6 0) + (c1 + (r1 + (c2 + (d2 + (r2 + (c3 + d3)))))),
   S a2 + S L2, p3 / 3, e3).

(* Steps before the last one, the halting time, and the final ones. *)
Definition f_steps : nat := fst (fst (fst final_params)).
Definition f_len0  : nat := snd (fst (fst final_params)).
Definition f_a     : nat := snd (fst final_params).
Definition f_b     : nat := snd final_params.

Definition pre_halt : nat := f_steps + (12 * f_len0 + 12 * f_a + 59).

Definition halting_time : nat := S pre_halt.

Definition final_ones : nat := f_len0 + f_a + 3 * f_b + 16.

Theorem bb6_reach : exists t0 L a e,
  final_params = (t0, L, a, e) /\
  steps t0 c0 = S1c (repeat false L) (3 * a) e.
Proof.
  unfold final_params.
  (* pass 1 *)
  destruct (runF 3 20 63) as [[c1 q1] b1] eqn:E1.
  destruct (runF_inv 3 20 63 31 _ _ _ eq_refl E1) as [[u1 Hb1] [t1 Hq1]].
  cbn [Nk] in Hq1.
  remember (q1 / 3) as a1 eqn:Ha1.
  assert (Ha1' : a1 = 2 * (t1 + 5) + 1).
  { assert (Hq : q1 = 3 * (2 * (t1 + 5) + 1) + 1) by lia.
    subst a1. rewrite Hq. apply div3. lia. }
  assert (Hq1' : q1 = 3 * a1 + 1) by lia.
  destruct (runF a1 (3 * b1 + 2) (Nk b1)) as [[c2 q2] b2] eqn:E2.
  destruct (runTop 4 (S a1) q2 b2) as [[d2 p2] e2] eqn:F2.
  (* pass 2 remainders *)
  assert (Hnb1 : Nk b1 = 2 * Nk (2 * u1) + 1) by (subst b1; apply Nk_Sodd).
  destruct (runF_inv _ _ _ _ _ _ _ Hnb1 E2) as [[u2 Hb2] [t2 Hq2]].
  destruct (runTop_inv _ _ _ _ _ _ _ _ Hb2 F2) as [[v2 He2] [w2 Hp2]].
  assert (Hs1 : exists s, Nk a1 = 3 * s + 1) by (rewrite Ha1'; apply Nk_odd).
  destruct Hs1 as [s1 Hs1].
  remember (p2 / 3) as a2 eqn:Ha2.
  assert (Hx : exists x, p2 = 6 * x + 7).
  { change (Nk 4) with 15 in Hp2.
    exists (u1 + s1 + t2 + 5 * (Nk (S a1) + 1) + w2). lia. }
  destruct Hx as [x2 Hx2].
  assert (Ha2' : a2 = 2 * (x2 + 1)).
  { assert (Hq : p2 = 3 * (2 * (x2 + 1)) + 1) by lia.
    subst a2. rewrite Hq. apply div3. lia. }
  assert (Hp2' : p2 = 3 * a2 + 1) by lia.
  destruct (runF a2 (3 * e2 + 2) (Nk e2)) as [[c3 q3] b3] eqn:E3.
  destruct (runTop (S (S a1 + 4)) (S a2) q3 b3) as [[d3 p3] e3] eqn:F3.
  (* pass 3 remainders *)
  assert (Hne2 : Nk e2 = 2 * Nk (2 * v2) + 1) by (subst e2; apply Nk_Sodd).
  destruct (runF_inv _ _ _ _ _ _ _ Hne2 E3) as [[u3 Hb3] [t3 Hq3]].
  destruct (runTop_inv _ _ _ _ _ _ _ _ Hb3 F3) as [[v3 He3] [w3 Hp3]].
  assert (Hs2 : exists s, Nk a2 = 3 * s) by (rewrite Ha2'; apply Nk_even).
  destruct Hs2 as [s2 Hs2].
  assert (Hs3 : exists s, Nk (S (S a1 + 4)) = 3 * s + 1).
  { replace (S (S a1 + 4)) with (2 * (t1 + 8) + 1) by lia. apply Nk_odd. }
  destruct Hs3 as [s3 Hs3].
  assert (Hs4 : exists s, Nk (S a2) = 3 * s + 1).
  { replace (S a2) with (2 * (x2 + 1) + 1) by lia. apply Nk_odd. }
  destruct Hs4 as [s4 Hs4].
  destruct (prod_mod _ _ _ _ Hs3 Hs4) as [m Hm].
  remember (p3 / 3) as a3 eqn:Ha3.
  assert (Hy : exists y, p3 = 6 * y + 9).
  { exists (v2 + s2 + t3 + m + w3). lia. }
  destruct Hy as [y3 Hy3].
  assert (Ha3' : a3 = 2 * y3 + 3).
  { assert (Hq : p3 = 3 * (2 * y3 + 3) + 0) by lia.
    subst a3. rewrite Hq. apply div3. lia. }
  assert (Hp3' : p3 = 3 * a3) by lia.
  (* now walk through the run *)
  eexists. exists (S a2 + S (S a1 + 4)), a3, e3. split; [reflexivity |].
  rewrite <- Hp3'.
  eapply run. { apply init. }
  eapply run. { apply (runF_ok 3 20 63 [] _ _ _ E1). }
  eapply run. { apply (restart' 3 a1 b1 q1 Hq1'). }
  eapply run. { apply (runF_ok _ _ _ (false :: repeat true 4) _ _ _ E2). }
  rewrite <- rep_snoc.
  eapply run. { apply (runTop_ok0 4 (S a1) q2 b2 _ _ _ F2). }
  eapply run. { apply (restart' _ a2 e2 p2 Hp2'). }
  eapply run. { apply (runF_ok _ _ _ (false :: repeat true (S (S a1 + 4))) _ _ _ E3). }
  rewrite <- rep_snoc.
  exact (runTop_ok0 (S (S a1 + 4)) (S a2) q3 b3 _ _ _ F3).
Qed.

Theorem bb6_last_step : exists l r, steps pre_halt c0 = (B, l, true, r).
Proof.
  destruct bb6_reach as (t0 & L & a & e & Hf & Hs).
  unfold pre_halt, f_steps, f_len0, f_a. rewrite Hf. cbn [fst snd].
  destruct (last_move L a e) as [l [r H]]. exists l, r.
  eapply run; [exact Hs | exact H].
Qed.

(* ---------- 13. It is the exact halting time ---------- *)

Lemma Z_stays : forall n c, state c = Z -> state (steps n c) = Z.
Proof.
  induction n as [| n IH]; intros c H; [exact H |].
  cbn [steps]. apply IH. destruct c as [[[s l] h] r]. cbn in H. subst s. reflexivity.
Qed.

Lemma exact_from_last : forall n c l r,
  steps n c = (B, l, true, r) ->
  state (steps (S n) c) = Z /\ forall m, m < S n -> state (steps m c) <> Z.
Proof.
  intros n c l r H. split.
  - replace (S n) with (n + 1) by lia. rewrite steps_add, H. destruct r; reflexivity.
  - intros m Hm Hz.
    assert (Hk : n = m + (n - m)) by lia.
    rewrite Hk, steps_add in H.
    pose proof (Z_stays (n - m) _ Hz) as Hz'. rewrite H in Hz'. discriminate.
Qed.

(* Main theorem.  The champion, started on the blank tape, halts after exactly
   [halting_time] steps: it is halted then, and at no earlier step. *)
Theorem bb6_halts_exactly :
  state (steps halting_time c0) = Z /\
  forall m, m < halting_time -> state (steps m c0) <> Z.
Proof.
  destruct bb6_last_step as [l [r H]].
  exact (exact_from_last pre_halt c0 l r H).
Qed.

(* The number of ones on the final tape. *)
Theorem bb6_final_ones : tape_ones (steps halting_time c0) = final_ones.
Proof.
  destruct bb6_reach as (t0 & L & a & e & Hf & Hs).
  unfold halting_time, pre_halt, final_ones, f_steps, f_len0, f_a, f_b.
  rewrite Hf. cbn [fst snd].
  replace (S (t0 + (12 * L + 12 * a + 59))) with (t0 + (12 * L + 12 * a + 60)) by lia.
  rewrite steps_add, Hs. apply halt_ones.
Qed.

(* All of the above is closed under the global context (no axioms). *)
Print Assumptions bb6_final_ones.
Print Assumptions bb6_halts_exactly.
Print Assumptions first_epoch.
Print Assumptions T_closed.
