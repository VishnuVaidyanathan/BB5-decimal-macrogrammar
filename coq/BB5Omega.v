(* BB5 champion: 1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA
   Lemmas about the oscillator word  Ω = 159  =  A1 -> C1 -> E1.
   Vishnu Vaidyanathan, EDGI Research Lab — first Rocq/Coq proofs. *)

Require Import List Lia.
Import ListNotations.
Require Import Arith.
Local Infix "mod" := Nat.modulo (at level 40, no associativity) : nat_scope.
Local Infix "/" := Nat.div : nat_scope.

(* ---------- 1. The machine ---------- *)

Inductive St := A | B | C | D | E | Z.

(* A configuration: state, cells to the LEFT (nearest first),
   the cell under the head, cells to the RIGHT (nearest first).
   An empty list means "all zeros from here on". *)
Definition conf : Type := (St * list bool * bool * list bool)%type.

(* Write w, move (right if goR = true, else left), go to state s'. *)
Definition act (w goR : bool) (s' : St) (l : list bool) (r : list bool) : conf :=
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
  | A, true  => act true  false C l r   (* A1 -> 1LC *)
  | B, false => act true  true  C l r   (* B0 -> 1RC *)
  | B, true  => act true  true  B l r   (* B1 -> 1RB *)
  | C, false => act true  true  D l r   (* C0 -> 1RD *)
  | C, true  => act false false E l r   (* C1 -> 0LE *)
  | D, false => act true  false A l r   (* D0 -> 1LA *)
  | D, true  => act true  false D l r   (* D1 -> 1LD *)
  | E, false => act true  true  Z l r   (* E0 -> 1RZ (halt) *)
  | E, true  => act false false A l r   (* E1 -> 0LA *)
  | Z, _     => c                       (* halted: stay *)
  end.

Fixpoint steps (n : nat) (c : conf) : conf :=
  match n with
  | 0   => c
  | S k => steps k (step c)
  end.

Lemma steps_add : forall a b c, steps (a + b) c = steps b (steps a c).
Proof.
  induction a as [| a IH]; intros b c; simpl.
  - reflexivity.
  - apply IH.
Qed.

(* ---------- 2. One Ω ---------- *)

(* One Ω (A1, C1, E1) turns  1 1 [1]  into  [x] 0 0 1 :
   the head moves 3 cells left and two 1s are erased. *)
Theorem omega_once : forall x L R,
  steps 3 (A, true :: true :: x :: L, true, R)
  = (A, L, x, false :: false :: true :: R).
Proof.
  intros x L R. reflexivity.
Qed.

(* ---------- 3. A block of Ω's ---------- *)

(* units n = the pattern  0 0 1  repeated n times *)
Fixpoint units (n : nat) : list bool :=
  match n with
  | 0   => []
  | S k => false :: false :: true :: units k
  end.

Lemma units_snoc : forall n R,
  units n ++ (false :: false :: true :: R)
  = false :: false :: true :: (units n ++ R).
Proof.
  induction n as [| n IH]; intros R; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* M+1 Ω's in a row turn a solid block of 3(M+1) ones
   (the head cell plus 2 + 3M cells to its left)
   into M+1 copies of "0 0 1". *)
Theorem omega_block : forall M x L R,
  steps (3 * S M) (A, repeat true (2 + 3 * M) ++ x :: L, true, R)
  = (A, L, x, units (S M) ++ R).
Proof.
  induction M as [| M IH]; intros x L R.
  - (* one Ω *) reflexivity.
  - (* peel off the first Ω, then use the hypothesis *)
    replace (3 * S (S M)) with (3 + 3 * S M) by lia.
    rewrite steps_add.
    replace (2 + 3 * S M) with (S (S (S (2 + 3 * M)))) by lia.
    change (repeat true (S (S (S (2 + 3 * M)))) ++ x :: L)
      with (true :: true :: true :: (repeat true (2 + 3 * M) ++ x :: L)).
    rewrite omega_once.
    rewrite IH.
    simpl. rewrite units_snoc. reflexivity.
Qed.

(* ---------- 4. The ones count ---------- *)

Fixpoint ones (l : list bool) : nat :=
  match l with
  | []          => 0
  | true :: t   => S (ones t)
  | false :: t  => ones t
  end.

Lemma ones_units : forall n, ones (units n) = n.
Proof.
  induction n as [| n IH]; simpl; lia.
Qed.

(* Inside the block, 3M ones become M ones:
   each Ω erases exactly two 1s. This is the core of the ones law. *)
Corollary omega_block_ones : forall M,
  ones (true :: repeat true (2 + 3 * M)) = 3 * S M
  /\ ones (units (S M)) = S M.
Proof.
  intros M. split.
  - assert (H : forall k, ones (repeat true k) = k).
    { induction k as [| k IHk]; simpl; lia. }
    simpl. rewrite H. lia.
  - apply ones_units.
Qed.

(* =============================================================
   ---------- 5. The ladder rung ----------
   At the start of a rung the head (state C) is on a 0, with a
   solid block of n ones to its left (and only zeros beyond), and
   the pattern  1 0 0  to its right. In the decimal trace a rung is
       4 . 7^(n+2) . 6 . 0 . 3^(n+3) . 2
   so A = n+2 and B = n+3 = A+1  (the filler coupling law).
   ============================================================= *)

Lemma repeat_snoc : forall k (r : list bool),
  repeat true k ++ true :: r = true :: (repeat true k ++ r).
Proof.
  induction k as [| k IH]; intros r; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* D sweeps LEFT over a block of 1s, then sits on the blank beyond. *)
Lemma d_sweep : forall k r,
  steps (S k) (D, repeat true k, true, r)
  = (D, [], false, repeat true (S k) ++ r).
Proof.
  induction k as [| k IH]; intros r.
  - reflexivity.
  - change (steps (S (S k)) (D, repeat true (S k), true, r))
      with (steps (S k) (D, repeat true k, true, true :: r)).
    rewrite IH. rewrite repeat_snoc. reflexivity.
Qed.

(* B sweeps RIGHT over a block of 1s, then sits on the first 0. *)
Lemma b_sweep : forall k l x R,
  steps (S k) (B, l, true, repeat true k ++ x :: R)
  = (B, repeat true (S k) ++ l, x, R).
Proof.
  induction k as [| k IH]; intros l x R.
  - reflexivity.
  - change (steps (S (S k)) (B, l, true, repeat true (S k) ++ x :: R))
      with (steps (S k) (B, true :: l, true, repeat true k ++ x :: R)).
    rewrite IH. rewrite repeat_snoc. reflexivity.
Qed.

Lemma s_C0 : forall n R,
  steps 1 (C, repeat true n, false, true :: false :: false :: R)
  = (D, repeat true (S n), true, false :: false :: R).
Proof. reflexivity. Qed.

Lemma s_D0 : forall r, steps 1 (D, [], false, r) = (A, [], false, true :: r).
Proof. reflexivity. Qed.

Lemma s_A0 : forall x r, steps 1 (A, [], false, x :: r) = (B, [true], x, r).
Proof. reflexivity. Qed.

Lemma s_B0 : forall l x r, steps 1 (B, l, false, x :: r) = (C, true :: l, x, r).
Proof. reflexivity. Qed.

(* One rung: the block grows from n to n+5 and one "1 0 0" unit
   is swallowed. It takes exactly 2n + 9 steps. *)
Theorem rung : forall n R,
  steps (2 * n + 9) (C, repeat true n, false, true :: false :: false :: R)
  = (C, repeat true (n + 5), false, R).
Proof.
  intros n R.
  replace (2 * n + 9)
    with (1 + (S (S n) + (1 + (1 + (S (S (S n)) + 1))))) by lia.
  rewrite !steps_add.
  rewrite s_C0, d_sweep, s_D0, s_A0, b_sweep, s_B0.
  rewrite repeat_snoc, app_nil_r.
  replace (n + 5) with (S (S (S (S (S n))))) by lia.
  reflexivity.
Qed.

(* ---------- 6. A whole ladder ---------- *)

(* u100 r = the pattern  1 0 0  repeated r times *)
Fixpoint u100 (r : nat) : list bool :=
  match r with
  | 0    => []
  | S r' => true :: false :: false :: u100 r'
  end.

(* steps used by r rungs starting from a block of n *)
Fixpoint lsteps (r n : nat) : nat :=
  match r with
  | 0    => 0
  | S r' => (2 * n + 9) + lsteps r' (n + 5)
  end.

(* r rungs in a row: the block grows by exactly 5 per rung. *)
Theorem ladder : forall r n R,
  steps (lsteps r n) (C, repeat true n, false, u100 r ++ R)
  = (C, repeat true (n + 5 * r), false, R).
Proof.
  induction r as [| r IH]; intros n R.
  - simpl. replace (n + 0) with n by lia. reflexivity.
  - change (lsteps (S r) n) with (2 * n + 9 + lsteps r (n + 5)).
    change (u100 (S r) ++ R) with (true :: false :: false :: (u100 r ++ R)).
    rewrite steps_add, rung, IH.
    replace (n + 5 + 5 * r) with (n + 5 * S r) by lia.
    reflexivity.
Qed.

(* =============================================================
   ---------- 7. Edge versions (the blank end of the tape) ----------
   ============================================================= *)

(* Ω block that runs right up to the blank left end (Gate 1 case). *)
Theorem omega_block_edge : forall M R,
  steps (3 * S M) (A, repeat true (2 + 3 * M), true, R)
  = (A, [], false, units (S M) ++ R).
Proof.
  induction M as [| M IH]; intros R.
  - reflexivity.
  - replace (3 * S (S M)) with (3 + 3 * S M) by lia.
    rewrite steps_add.
    replace (2 + 3 * S M) with (S (S (S (2 + 3 * M)))) by lia.
    change (repeat true (S (S (S (2 + 3 * M)))))
      with (true :: true :: true :: repeat true (2 + 3 * M)).
    change (steps 3 (A, true :: true :: true :: repeat true (2 + 3 * M), true, R))
      with (A, repeat true (2 + 3 * M), true, false :: false :: true :: R).
    rewrite IH. simpl. rewrite units_snoc. reflexivity.
Qed.

(* B sweeps right over 1s into the blank right end. *)
Lemma b_sweep_edge : forall k l,
  steps (S k) (B, l, true, repeat true k)
  = (B, repeat true (S k) ++ l, false, []).
Proof.
  induction k as [| k IH]; intros l.
  - reflexivity.
  - change (steps (S (S k)) (B, l, true, repeat true (S k)))
      with (steps (S k) (B, true :: l, true, repeat true k)).
    rewrite IH. rewrite repeat_snoc. reflexivity.
Qed.

Lemma repeat_snoc1 : forall k, repeat true k ++ [true] = repeat true (S k).
Proof. intros k. rewrite repeat_snoc, app_nil_r. reflexivity. Qed.

Lemma units_shift : forall k r,
  true :: (units k ++ r) = u100 k ++ true :: r.
Proof.
  induction k as [| k IH]; intros r; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* =============================================================
   ---------- 8. The terminal rung  (B = A + 2) ----------
   Right side is just "1 1" then blank. In digits:
       4 . 7^(n+2) . 6 . 0 . 3^(n+4) . 2      so  B = A + 2.
   ============================================================= *)

Lemma s_B0_edge : forall l, steps 1 (B, l, false, []) = (C, true :: l, false, []).
Proof. reflexivity. Qed.

Definition tsteps (n : nat) : nat := 2 * n + 10.

Theorem terminal_rung : forall n,
  steps (tsteps n) (C, repeat true n, false, [true; true])
  = (C, repeat true (n + 6), false, []).
Proof.
  intros n. unfold tsteps.
  replace (2 * n + 10)
    with (1 + (S (S n) + (1 + (1 + (S (S (S (S n))) + 1))))) by lia.
  rewrite !steps_add.
  change (steps 1 (C, repeat true n, false, [true; true]))
    with (D, repeat true (S n), true, [true]).
  rewrite d_sweep, s_D0.
  change (steps 1 (A, [], false, true :: (repeat true (S (S n)) ++ [true])))
    with (B, [true], true, repeat true (S (S n)) ++ [true]).
  rewrite repeat_snoc1, b_sweep_edge, s_B0_edge.
  rewrite repeat_snoc1.
  replace (n + 6) with (S (S (S (S (S (S n)))))) by lia.
  reflexivity.
Qed.

(* "46": the bridge from the end of a layer to the next Ω block. *)
Lemma bridge_46 : forall l,
  steps 2 (C, l, false, []) = (A, l, true, [true]).
Proof. reflexivity. Qed.

(* =============================================================
   ---------- 9. Whole layers ----------
   A layer starts at  (A, 1^a, [1], 1).  Write  a + 1 = 3M + r.
     r = 0 : Gate 1,  ends at a' = 5M + 3
     r = 1 : Gate 2,  ends at a' = 5M + 6
     r = 2 : halt.
   ============================================================= *)

Definition layer_start (a : nat) : conf := (A, repeat true a, true, [true]).

(* Gate 1:  a = 2 + 3M',  M = M' + 1 Ω's.  Opens "0 2", first rung n = 2. *)
Theorem layer_gate1 : forall M',
  steps (3 * S M' + 2 + lsteps M' 2 + tsteps (2 + 5 * M') + 2)
        (layer_start (2 + 3 * M'))
  = layer_start (2 + 5 * M' + 6).
Proof.
  intros M'. unfold layer_start.
  rewrite !steps_add.
  rewrite omega_block_edge.
  change (steps 2 (A, [], false, units (S M') ++ [true]))
    with (C, [true; true], false, true :: (units M' ++ [true])).
  rewrite units_shift.
  change [true; true] with (repeat true 2).
  rewrite ladder.
  rewrite terminal_rung, bridge_46.
  reflexivity.
Qed.

(* Gate 2:  a = 3M,  M = M' + 1 Ω's.  Opens "1", first rung n = 0. *)
Theorem layer_gate2 : forall M',
  steps (3 * S M' + 1 + lsteps (S M') 0 + tsteps (5 * S M') + 2)
        (layer_start (3 * S M'))
  = layer_start (5 * S M' + 6).
Proof.
  intros M'. unfold layer_start.
  replace (3 * S M') with (S (2 + 3 * M')) at 2 by lia.
  rewrite <- (repeat_snoc1 (2 + 3 * M')).
  rewrite !steps_add.
  rewrite omega_block.
  change (steps 1 (A, [], true, units (S M') ++ [true]))
    with (C, @nil bool, false, true :: (units (S M') ++ [true])).
  rewrite units_shift.
  change (@nil bool) with (repeat true 0).
  rewrite ladder.
  replace (0 + 5 * S M') with (5 * S M') by lia.
  rewrite terminal_rung, bridge_46.
  reflexivity.
Qed.

Definition state (c : conf) : St := let '(s, _, _, _) := c in s.

(* Halt:  a = 3M + 1.  M Ω's, then  1 5 8  (A1, C1, E0) and stop. *)
Theorem layer_halt : forall M,
  state (steps (3 * M + 3) (layer_start (3 * M + 1))) = Z.
Proof.
  intros [| M']; unfold layer_start.
  - reflexivity.
  - replace (3 * S M' + 3) with (3 * S M' + 3) by lia.
    rewrite steps_add.
    replace (3 * S M' + 1) with (2 + 3 * M' + 2) by lia.
    replace (repeat true (2 + 3 * M' + 2))
      with (repeat true (2 + 3 * M') ++ [true; true]).
    + rewrite omega_block. reflexivity.
    + rewrite (repeat_app true (2 + 3 * M') 2). reflexivity.
Qed.

(* The very start: blank tape, "0 2 4 6", gives layer_start 2. *)
Lemma start_0246 : steps 4 (A, [], false, []) = layer_start 2.
Proof. reflexivity. Qed.

(* =============================================================
   ---------- 10. The layer map and the gate law ----------
   ============================================================= *)

(* The whole machine, one layer at a time:  Some a'  or  None (halt). *)
Definition next_layer (a : nat) : option nat :=
  match (a + 1) mod 3 with
  | 0 => Some (5 * ((a + 1) / 3) + 3)
  | 1 => Some (5 * ((a + 1) / 3) + 6)
  | _ => None
  end.

(* Every layer with a >= 1 behaves as next_layer says. *)
Theorem layer_correct : forall a, 1 <= a ->
  match next_layer a with
  | Some a' => exists n, steps n (layer_start a) = layer_start a'
  | None    => exists n, state (steps n (layer_start a)) = Z
  end.
Proof.
  intros a Ha. unfold next_layer.
  destruct ((a + 1) mod 3) as [| [| r]] eqn:Hr.
  - (* Gate 1 *)
    destruct ((a + 1) / 3) as [| M'] eqn:Hq.
    + exfalso. pose proof (Nat.div_mod (a + 1) 3). lia.
    + assert (Ha' : a = 2 + 3 * M').
      { pose proof (Nat.div_mod (a + 1) 3). lia. }
      subst a. eexists.
      replace (5 * S M' + 3) with (2 + 5 * M' + 6) by lia.
      apply layer_gate1.
  - (* Gate 2 *)
    destruct ((a + 1) / 3) as [| M'] eqn:Hq.
    + exfalso. pose proof (Nat.div_mod (a + 1) 3). lia.
    + assert (Ha' : a = 3 * S M').
      { pose proof (Nat.div_mod (a + 1) 3). lia. }
      subst a. eexists. apply layer_gate2.
  - (* halt *)
    assert (Hr2 : (a + 1) mod 3 = 2).
    { pose proof (Nat.mod_upper_bound (a + 1) 3). lia. }
    assert (Ha' : a = 3 * ((a + 1) / 3) + 1).
    { pose proof (Nat.div_mod (a + 1) 3). lia. }
    rewrite Ha'. eexists. apply layer_halt.
Qed.

(* Gate law in the paper's terms. The terminal rung has A = K, and the
   next layer starts at a' = K + 4. So the next gate is decided by
   (a' + 1) mod 3 = (K + 5) mod 3 = (K + 2) mod 3:
     0 -> Gate 1,   1 -> Gate 2,   2 -> halt.                         *)
Lemma gate_law : forall K, (K + 4 + 1) mod 3 = (K + 2) mod 3.
Proof.
  intros K. replace (K + 4 + 1) with ((K + 2) + 1 * 3) by lia.
  apply Nat.Div0.mod_add.
Qed.

(* =============================================================
   ---------- 11. The BB5 champion halts after 15 layers ----------
   ============================================================= *)

Fixpoint layers_to_halt (fuel a : nat) : option nat :=
  match fuel with
  | 0 => None
  | S f =>
      match next_layer a with
      | None    => Some 1
      | Some a' => option_map S (layers_to_halt f a')
      end
  end.

Theorem halts_from : forall fuel a k, 1 <= a ->
  layers_to_halt fuel a = Some k ->
  exists n, state (steps n (layer_start a)) = Z.
Proof.
  induction fuel as [| f IH]; intros a k Ha H; simpl in H.
  - discriminate.
  - pose proof (layer_correct a Ha) as Hl.
    destruct (next_layer a) as [a' |] eqn:Hn.
    + destruct Hl as [n1 Hn1].
      destruct (layers_to_halt f a') as [k' |] eqn:Hk; [| discriminate].
      assert (Ha' : 1 <= a').
      { unfold next_layer in Hn.
        destruct ((a + 1) mod 3) as [| [| ?]]; inversion Hn; lia. }
      destruct (IH a' k' Ha' Hk) as [n2 Hn2].
      exists (n1 + n2). rewrite steps_add, Hn1. exact Hn2.
    + exact Hl.
Qed.

(* Pure arithmetic: starting at a = 2, the map halts at layer 15. *)
Lemma fifteen_layers : layers_to_halt 20 2 = Some 15.
Proof. vm_compute. reflexivity. Qed.

Theorem bb5_champion_halts :
  exists n, state (steps n (A, [], false, [])) = Z.
Proof.
  destruct (halts_from 20 2 15 ltac:(lia) fifteen_layers) as [n Hn].
  exists (4 + n). rewrite steps_add, start_0246. exact Hn.
Qed.

(* #############################################################
   PART II — THE DECIMAL TRACE (the "decimal lens")
   Every step writes one digit:  digit = 2 * state_index + symbol.
   A0=0 A1=1 B0=2 B1=3 C0=4 C1=5 D0=6 D1=7 E0=8 E1=9.
   Below, every pattern of the paper is proved as an exact digit string.
   ############################################################# *)

Definition sidx (s : St) : nat :=
  match s with A => 0 | B => 1 | C => 2 | D => 3 | E => 4 | Z => 5 end.

Definition digit (c : conf) : nat :=
  let '(s, _, h, _) := c in 2 * sidx s + (if h then 1 else 0).

(* The digits written during n steps starting from c. *)
Fixpoint trace (n : nat) (c : conf) : list nat :=
  match n with
  | 0   => []
  | S k => digit c :: trace k (step c)
  end.

Lemma trace_add : forall a b c,
  trace (a + b) c = trace a c ++ trace b (steps a c).
Proof.
  induction a as [| a IH]; intros b c; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma trace1 : forall c, trace 1 c = [digit c].
Proof. reflexivity. Qed.

(* ---------- Ω blocks:  (159)^M ---------- *)

Fixpoint om (k : nat) : list nat :=
  match k with
  | 0    => []
  | S k' => 1 :: 5 :: 9 :: om k'
  end.

Theorem omega_block_tr : forall M x L R,
  trace (3 * S M) (A, repeat true (2 + 3 * M) ++ x :: L, true, R) = om (S M).
Proof.
  induction M as [| M IH]; intros x L R.
  - reflexivity.
  - replace (3 * S (S M)) with (3 + 3 * S M) by lia.
    rewrite trace_add.
    replace (2 + 3 * S M) with (S (S (S (2 + 3 * M)))) by lia.
    change (repeat true (S (S (S (2 + 3 * M)))) ++ x :: L)
      with (true :: true :: true :: (repeat true (2 + 3 * M) ++ x :: L)).
    rewrite omega_once, IH. reflexivity.
Qed.

Theorem omega_block_edge_tr : forall M R,
  trace (3 * S M) (A, repeat true (2 + 3 * M), true, R) = om (S M).
Proof.
  induction M as [| M IH]; intros R.
  - reflexivity.
  - replace (3 * S (S M)) with (3 + 3 * S M) by lia.
    rewrite trace_add.
    replace (2 + 3 * S M) with (S (S (S (2 + 3 * M)))) by lia.
    change (repeat true (S (S (S (2 + 3 * M)))))
      with (true :: true :: true :: repeat true (2 + 3 * M)).
    change (steps 3 (A, true :: true :: true :: repeat true (2 + 3 * M), true, R))
      with (A, repeat true (2 + 3 * M), true, false :: false :: true :: R).
    rewrite IH. reflexivity.
Qed.

(* ---------- sweeps:  7^k  and  3^k ---------- *)

Lemma d_sweep_tr : forall k r,
  trace (S k) (D, repeat true k, true, r) = repeat 7 (S k).
Proof.
  induction k as [| k IH]; intros r.
  - reflexivity.
  - change (trace (S (S k)) (D, repeat true (S k), true, r))
      with (7 :: trace (S k) (D, repeat true k, true, true :: r)).
    rewrite IH. reflexivity.
Qed.

Lemma b_sweep_tr : forall k l x R,
  trace (S k) (B, l, true, repeat true k ++ x :: R) = repeat 3 (S k).
Proof.
  induction k as [| k IH]; intros l x R.
  - reflexivity.
  - change (trace (S (S k)) (B, l, true, repeat true (S k) ++ x :: R))
      with (3 :: trace (S k) (B, true :: l, true, repeat true k ++ x :: R)).
    rewrite IH. reflexivity.
Qed.

Lemma b_sweep_edge_tr : forall k l,
  trace (S k) (B, l, true, repeat true k) = repeat 3 (S k).
Proof.
  induction k as [| k IH]; intros l.
  - reflexivity.
  - change (trace (S (S k)) (B, l, true, repeat true (S k)))
      with (3 :: trace (S k) (B, true :: l, true, repeat true k)).
    rewrite IH. reflexivity.
Qed.

(* ---------- rungs ---------- *)

(* internal rung:  4 . 7^(n+2) . 6 0 . 3^(n+3) . 2 *)
Definition rung_digits (n : nat) : list nat :=
  [4] ++ repeat 7 (n + 2) ++ [6; 0] ++ repeat 3 (n + 3) ++ [2].

(* terminal rung:  4 . 7^(n+2) . 6 0 . 3^(n+4) . 2 *)
Definition term_digits (n : nat) : list nat :=
  [4] ++ repeat 7 (n + 2) ++ [6; 0] ++ repeat 3 (n + 4) ++ [2].

Theorem rung_tr : forall n R,
  trace (2 * n + 9) (C, repeat true n, false, true :: false :: false :: R)
  = rung_digits n.
Proof.
  intros n R. unfold rung_digits.
  replace (2 * n + 9)
    with (1 + (S (S n) + (1 + (1 + (S (S (S n)) + 1))))) by lia.
  rewrite !trace_add; try rewrite !steps_add.
  rewrite s_C0, d_sweep, s_D0, s_A0, b_sweep.
  rewrite !trace1, d_sweep_tr, b_sweep_tr.
  replace (n + 2) with (S (S n)) by lia.
  replace (n + 3) with (S (S (S n))) by lia.
  reflexivity.
Qed.

Theorem terminal_rung_tr : forall n,
  trace (tsteps n) (C, repeat true n, false, [true; true]) = term_digits n.
Proof.
  intros n. unfold tsteps, term_digits.
  replace (2 * n + 10)
    with (1 + (S (S n) + (1 + (1 + (S (S (S (S n))) + 1))))) by lia.
  rewrite !trace_add; try rewrite !steps_add.
  change (steps 1 (C, repeat true n, false, [true; true]))
    with (D, repeat true (S n), true, [true]).
  rewrite d_sweep, s_D0.
  change (steps 1 (A, [], false, true :: (repeat true (S (S n)) ++ [true])))
    with (B, [true], true, repeat true (S (S n)) ++ [true]).
  rewrite repeat_snoc1, b_sweep_edge.
  rewrite !trace1, d_sweep_tr, b_sweep_edge_tr.
  replace (n + 2) with (S (S n)) by lia.
  replace (n + 4) with (S (S (S (S n)))) by lia.
  reflexivity.
Qed.

(* the ladder: r internal rungs, sizes n, n+5, n+10, ... *)
Fixpoint ltrace (r n : nat) : list nat :=
  match r with
  | 0    => []
  | S r' => rung_digits n ++ ltrace r' (n + 5)
  end.

Theorem ladder_tr : forall r n R,
  trace (lsteps r n) (C, repeat true n, false, u100 r ++ R) = ltrace r n.
Proof.
  induction r as [| r IH]; intros n R.
  - reflexivity.
  - change (lsteps (S r) n) with (2 * n + 9 + lsteps r (n + 5)).
    change (u100 (S r) ++ R) with (true :: false :: false :: (u100 r ++ R)).
    rewrite trace_add, rung, rung_tr, IH. reflexivity.
Qed.

(* ---------- whole layers as digit strings ---------- *)

(* Gate 1 layer:  (159)^M  02  ladder  terminal  46 *)
Theorem layer_gate1_tr : forall M',
  trace (3 * S M' + 2 + lsteps M' 2 + tsteps (2 + 5 * M') + 2)
        (layer_start (2 + 3 * M'))
  = om (S M') ++ [0; 2] ++ ltrace M' 2 ++ term_digits (2 + 5 * M') ++ [4; 6].
Proof.
  intros M'. unfold layer_start.
  rewrite !trace_add; try rewrite !steps_add.
  rewrite omega_block_edge, omega_block_edge_tr.
  change (steps 2 (A, [], false, units (S M') ++ [true]))
    with (C, [true; true], false, true :: (units M' ++ [true])).
  change (trace 2 (A, [], false, units (S M') ++ [true])) with [0; 2].
  rewrite units_shift.
  change [true; true] with (repeat true 2).
  rewrite ladder, ladder_tr, terminal_rung, terminal_rung_tr.
  change (trace 2 (C, repeat true (2 + 5 * M' + 6), false, [])) with [4; 6].
  rewrite !app_assoc. reflexivity.
Qed.

(* Gate 2 layer:  (159)^M  1  ladder  terminal  46 *)
Theorem layer_gate2_tr : forall M',
  trace (3 * S M' + 1 + lsteps (S M') 0 + tsteps (5 * S M') + 2)
        (layer_start (3 * S M'))
  = om (S M') ++ [1] ++ ltrace (S M') 0 ++ term_digits (5 * S M') ++ [4; 6].
Proof.
  intros M'. unfold layer_start.
  replace (3 * S M') with (S (2 + 3 * M')) at 2 by lia.
  rewrite <- (repeat_snoc1 (2 + 3 * M')).
  rewrite !trace_add; try rewrite !steps_add.
  rewrite omega_block, omega_block_tr.
  change (steps 1 (A, [], true, units (S M') ++ [true]))
    with (C, @nil bool, false, true :: (units (S M') ++ [true])).
  change (trace 1 (A, [], true, units (S M') ++ [true])) with [1].
  rewrite units_shift.
  change (@nil bool) with (repeat true 0).
  rewrite ladder, ladder_tr.
  replace (0 + 5 * S M') with (5 * S M') by lia.
  rewrite terminal_rung, terminal_rung_tr.
  change (trace 2 (C, repeat true (5 * S M' + 6), false, [])) with [4; 6].
  rewrite !app_assoc. reflexivity.
Qed.

(* Halting layer:  (159)^M  158 *)
Theorem layer_halt_tr : forall M,
  trace (3 * M + 3) (layer_start (3 * M + 1)) = om M ++ [1; 5; 8].
Proof.
  intros [| M']; unfold layer_start.
  - reflexivity.
  - rewrite trace_add.
    replace (3 * S M' + 1) with (2 + 3 * M' + 2) by lia.
    replace (repeat true (2 + 3 * M' + 2))
      with (repeat true (2 + 3 * M') ++ [true; true])
      by (rewrite (repeat_app true (2 + 3 * M') 2); reflexivity).
    rewrite omega_block, omega_block_tr. reflexivity.
Qed.

Lemma start_tr : trace 4 (A, [], false, []) = [0; 2; 4; 6].
Proof. reflexivity. Qed.

(* ---------- the whole trace is the grammar ---------- *)

Definition layer_digits (a : nat) : list nat :=
  let M := (a + 1) / 3 in
  match (a + 1) mod 3 with
  | 0 => om M ++ [0; 2] ++ ltrace (M - 1) 2 ++ term_digits (2 + 5 * (M - 1)) ++ [4; 6]
  | 1 => om M ++ [1] ++ ltrace M 0 ++ term_digits (5 * M) ++ [4; 6]
  | _ => om M ++ [1; 5; 8]
  end.

Theorem layer_correct_tr : forall a, 1 <= a ->
  match next_layer a with
  | Some a' => exists n, steps n (layer_start a) = layer_start a'
                         /\ trace n (layer_start a) = layer_digits a
  | None    => exists n, state (steps n (layer_start a)) = Z
                         /\ trace n (layer_start a) = layer_digits a
  end.
Proof.
  intros a Ha. unfold next_layer, layer_digits.
  destruct ((a + 1) mod 3) as [| [| r]] eqn:Hr.
  - destruct ((a + 1) / 3) as [| M'] eqn:Hq.
    + exfalso. pose proof (Nat.div_mod (a + 1) 3). lia.
    + assert (Ha' : a = 2 + 3 * M').
      { pose proof (Nat.div_mod (a + 1) 3). lia. }
      subst a. eexists. split.
      * replace (5 * S M' + 3) with (2 + 5 * M' + 6) by lia.
        apply layer_gate1.
      * replace (S M' - 1) with M' by lia. apply layer_gate1_tr.
  - destruct ((a + 1) / 3) as [| M'] eqn:Hq.
    + exfalso. pose proof (Nat.div_mod (a + 1) 3). lia.
    + assert (Ha' : a = 3 * S M').
      { pose proof (Nat.div_mod (a + 1) 3). lia. }
      subst a. eexists. split.
      * apply layer_gate2.
      * apply layer_gate2_tr.
  - pose proof (Nat.div_mod (a + 1) 3 ltac:(lia)) as H1.
    pose proof (Nat.mod_upper_bound (a + 1) 3 ltac:(lia)) as H2.
    set (M := (a + 1) / 3) in *.
    assert (Ha' : a = 3 * M + 1) by lia.
    clearbody M. subst a. eexists. split.
    + apply layer_halt.
    + apply layer_halt_tr.
Qed.

(* The full grammar: layer after layer until the halt. *)
Fixpoint grammar (fuel a : nat) : list nat :=
  match fuel with
  | 0 => []
  | S f => layer_digits a ++
           match next_layer a with
           | Some a' => grammar f a'
           | None    => []
           end
  end.

Theorem halts_with_trace : forall fuel a k, 1 <= a ->
  layers_to_halt fuel a = Some k ->
  exists n, state (steps n (layer_start a)) = Z
            /\ trace n (layer_start a) = grammar fuel a.
Proof.
  induction fuel as [| f IH]; intros a k Ha H; simpl in H.
  - discriminate.
  - pose proof (layer_correct_tr a Ha) as Hl. simpl grammar.
    destruct (next_layer a) as [a' |] eqn:Hn.
    + destruct Hl as [n1 [Hs1 Ht1]].
      destruct (layers_to_halt f a') as [k' |] eqn:Hk; [| discriminate].
      assert (Ha' : 1 <= a').
      { unfold next_layer in Hn.
        destruct ((a + 1) mod 3) as [| [| ?]]; inversion Hn; lia. }
      destruct (IH a' k' Ha' Hk) as [n2 [Hs2 Ht2]].
      exists (n1 + n2). split.
      * rewrite steps_add, Hs1. exact Hs2.
      * rewrite trace_add, Ht1, Hs1, Ht2. reflexivity.
    + destruct Hl as [n [Hs Ht]]. exists n. split; [exact Hs |].
      rewrite Ht, app_nil_r. reflexivity.
Qed.

(* MAIN THEOREM.  The decimal trace of the BB5 champion, from a blank
   tape to the halt, is exactly  0246  followed by the layer grammar. *)
Theorem bb5_decimal_trace :
  exists n, state (steps n (A, [], false, [])) = Z
            /\ trace n (A, [], false, []) = [0; 2; 4; 6] ++ grammar 20 2.
Proof.
  destruct (halts_with_trace 20 2 15 ltac:(lia) fifteen_layers) as [n [Hs Ht]].
  exists (4 + n). split.
  - rewrite steps_add, start_0246. exact Hs.
  - rewrite trace_add, start_tr, start_0246, Ht. reflexivity.
Qed.

(* ---------- Theorem 8.1 and the M sequence ---------- *)

(* The next layer starts at a' = K + 4 (both gates), so
   M_next = (a' + 1) / 3 = (K + 5) / 3 = (K + 2) / 3 + 1.            *)
Lemma recurrence_8_1 : forall K, (K + 4 + 1) / 3 = (K + 2) / 3 + 1.
Proof.
  intros K. replace (K + 4 + 1) with ((K + 2) + 1 * 3) by lia.
  apply Nat.div_add. lia.
Qed.

Fixpoint M_list (fuel a : nat) : list nat :=
  match fuel with
  | 0 => []
  | S f => (a + 1) / 3 ::
           match next_layer a with Some a' => M_list f a' | None => [] end
  end.

Lemma M_sequence :
  M_list 20 2 = [1; 3; 6; 12; 22; 39; 66; 112; 189; 316; 529; 883; 1473; 2456; 4095].
Proof. vm_compute. reflexivity. Qed.
