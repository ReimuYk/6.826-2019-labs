Require Import POCS.
Require Import LogAPI.
Require Import Common.OneDiskAPI.
Import ListNotations.

(** * Implementation of the atomic append-only log. *)

(** Your job is to implement the atomic append-only log API,
    as defined in [LogAPI.v], on top of a single disk, as
    defined in [OneDiskAPI.v].  The underlying disk is the
    same abstraction that you implemented in lab 2.

    To achieve crash-safety, you can rely on the fact that
    the underlying disk provides atomic block writes: that
    is, writing to a single disk block is atomic with respect
    to crash-safety.  If the system crashes in the middle of
    a write to a disk block, then after the crash, that block
    has either the old value or the new value, but not some
    other corrupted value.

    The disk provided by [OneDiskAPI.v] is synchronous, in
    the sense that disk writes that have fully completed (where
    [write] returned) are durable: if the computer crashes after
    a [write] finished, that [write] will still be there after
    the computer reboots. *)

(** To implement the log API, we assume that we have a procedure
    [addr_to_block] that encodes a number as a block, and a way
    to read the number back from the block (the function
    [block_to_addr]). This gives your implementation a way to
    serialize data onto disk. *)

Axiom addr_to_block : addr -> proc block.
Axiom block_to_addr : block -> addr.

Definition addr_to_block_spec State a : Specification unit block unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' => state' = state /\ block_to_addr r = a;
    recovered := fun _ state' => state' = state
  |}.
Axiom addr_to_block_ok : forall State a recover abstr,
  proc_spec (@addr_to_block_spec State a) (addr_to_block a) recover abstr.
Hint Resolve addr_to_block_ok : core.


(** For this lab, we provide a notation for diskUpd. Not only can you use this
    to write [diskUpd d a b] as [d [a |-> b]] but you will also see this notation
    in goals. This should especially make it easier to read goals with many
    updates of the same disk.

    Remember that the code still uses diskUpd underneath, so the same theorems
    apply. We recommend using [autorewrite with upd] or [autorewrite with upd
    in *] in this lab to simplify diskGet/diskUpd expressions, rather than
    using the theorems manually. *)
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 8, left associativity).
Notation "d [ a |=> bs ]" := (diskUpds d a bs) (at level 8, left associativity).

Opaque diskGet.


(** In this lab, you will likely be doing reasoning about
    the contents of various disk blocks.  The following
    theorem will help you do so. *)
Theorem diskGet_eq_values : forall d a b b',
    diskGet d a =?= b ->
    diskGet d a =?= b' ->
    a < diskSize d ->
    b = b'.
Proof.
  (* Fill in your proof here. *)
  intros.
  destruct (diskGet d a) eqn:Heq.
  {
    simpl in *.
    subst; auto.
  }
  {
    apply disk_inbounds_not_none in H1; auto.
  }
  Qed.

(** We use the above theorem to implement the [eq_values]
    tactic.  [eq_values] can be used when you have hypotheses
    like:

        H1: diskGet d a =?= eq b
        H2: diskGet d a =?= eq b'

    In this context, the tactic proves b = b'.
 *)
Ltac eq_values :=
  match goal with
  | [ H:  diskGet ?d ?a =?= ?b,
      H': diskGet ?d ?a =?= ?b' |- _ ] =>
    assert (b = b') by (apply (@diskGet_eq_values d a b b'); try lia; auto);
    subst
  end.


Module Log (d : OneDiskAPI) <: LogAPI.

  (** Fill in your implementation and proof here, replacing
      the placeholder statements below with your own definitions
      and theorems as appropriate.  Feel free to introduce helper
      procedures and helper theorems to structure your implementation
      and proof. *)

  Set Nested Proofs Allowed.

  (** helper tactics *)
  Ltac unfold_diskGet :=
    match goal with
    | [ |- context[diskGet ?l ?n] ] =>
      replace (diskGet l n) with (nth_error l n) by auto; simpl
    end.

  Ltac fold_diskGet :=
    match goal with
    | [ |- context[nth_error ?l ?n] ] =>
      replace (nth_error l n) with (diskGet l n) by auto; simpl
    end.

  Ltac unfold_diskSize :=
    match goal with
    | [ |- context[diskSize ?d] ] =>
      replace (diskSize d) with (length d) by auto; simpl
    end.

  Ltac fold_diskSize :=
    match goal with
    | [ |- context[length ?d] ] =>
      replace (length d) with (diskSize d) by auto; simpl
    end.

  (** helper definitions *)
  Definition diskGetLogLength (d : disk) : nat :=
    match diskGet d (diskSize d - 1) with
    | Some v => block_to_addr v
    | None => 0
    end.

  (** helper lemmas *)
  Lemma diskGet_none_size:
    forall d a,
      diskGet d a = None -> ~(a < diskSize d).
  Proof.
    unfold not.
    intros.
    eapply disk_inbounds_not_none; eauto.
  Qed.

  Lemma diskGets_eq:
    forall len d1 d2 a1 a2,
      skipn a1 d1 = skipn a2 d2 ->
      diskGets d1 a1 len = diskGets d2 a2 len.
  Proof.
    induction len.
    1: auto.
    intros.
    pose H as H0.
    eapply IHlen in H0.
    replace (S len) with (len + 1) by lia.
    do 2 rewrite diskGets_last.
    assert (diskGet d1 (a1 + len) = diskGet d2 (a2 + len)).
    {
      do 2 unfold_diskGet.
      Lemma nth_error_skipn:
        forall (l: list block) a b,
          nth_error l (a + b) = nth_error (skipn a l) b.
      Proof.
        induction l.
        {
          induction a.
          1: auto.
          intros.
          simpl.
          destruct b; auto.
        }
        {
          intros.
          simpl.
          destruct a0.
          1: auto.
          simpl.
          eapply IHl.
        }
      Qed.
      do 2 rewrite nth_error_skipn.
      rewrite H; auto.
    }
    rewrite H1.
    rewrite H0.
    reflexivity.
  Qed.

  (** abstraction relation *)
  Inductive log_abstraction (disk_state : OneDiskAPI.State) (log_state : LogAPI.State) : Prop :=
    | LogAbstraction :
      let nonsense := 0 in
      forall
        (* maximum log length is (disk size - 1) *)
        (Hlength_inbounds : ((not(diskSize disk_state = 0) -> length log_state < diskSize disk_state)) /\ (diskSize disk_state = 0 -> length log_state = 0))
        (* last entry on disk is the same as log length (or log length is 0) *)
        (Hlength_on_disk : length log_state = diskGetLogLength disk_state)
        (* for all nats i below log length, the block at i on the disk corresponds to the block at i in the log. we use diskGets log_state here even though log_state isn't a disk to ease later
         proofs. *)
        (Hentries : diskGets log_state 0 (length log_state) = diskGets disk_state 0 (length log_state))
      ,
      log_abstraction disk_state log_state.
  Definition abstr : Abstraction State :=
    abstraction_compose d.abstr {| abstraction := log_abstraction |}.

  (** recover function *)
  Definition recover : proc unit := d.recover.
  
  Theorem recover_wipe : rec_wipe recover abstr no_wipe.
  Proof.
    unfold rec_wipe.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; eauto.
  Qed.

  (** init function *)
  Definition init' : proc InitResult :=
    sz <- d.size;
    n_ <- addr_to_block 0;
    _ <- d.write (sz - 1) n_;
    Ret Initialized.
  Definition init := then_init d.init init'.

  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eapply then_init_compose; eauto.
    step_proc.
    step_proc.
    step_proc.
    step_proc.
    exists nil.
    intuition.
    constructor.
    {
      split.
      {
        intros.
        simpl.
        destruct state.
        {
          simpl in H0.
          exfalso.
          apply H0.
          auto.
        }
        {
          simpl.
          destruct (diskSize state - 0); simpl; lia.
        }
      }
      {
        intros.
        simpl.
        auto.
      }
    }
    {
      simpl.
      unfold diskGetLogLength.
      destruct state.
      {
        simpl.
        assert (diskGet nil 0 = None) by auto.
        rewrite H0.
        reflexivity.
      }
      {
        simpl.
        destruct (diskSize state - 0) eqn:Heq.
        {
          simpl.
          rewrite Heq.
          assert (diskGet (r :: state) 0 = Some r) by auto.
          rewrite H0.
          auto.
        }
        {
          simpl.
          rewrite diskUpd_size.
          rewrite Heq.
          unfold_diskGet.
          fold_diskGet.
          destruct (diskGet state n) eqn:Heq2.
          {
            SearchAbout (diskGet (diskUpd _ _ _) _).
            eapply diskUpd_eq_some in Heq2.
            instantiate (1:= r) in Heq2.
            rewrite Heq2.
            auto.
          }
          {
            eapply diskGet_none_size in Heq2.
            SearchAbout (diskGet (diskUpd _ _ _) _).
            eapply diskUpd_oob_eq in Heq2.
            instantiate (1:= r) in Heq2.
            rewrite Heq2.
            auto.
          }
        }
      }
    }
    auto.
  Qed.

  (** get_log_length function (helper) *)
  Definition get_log_length : proc nat :=
    sz <- d.size;
    if gt_dec sz 0 then
      len <- d.read (sz - 1);
      Ret (block_to_addr len)
    else
      Ret 0.

  Definition get_log_length_spec : Specification unit nat unit OneDiskAPI.State :=
    fun (_ : unit) state => {|
        pre := True;
        post := fun r state' =>
                 state' = state /\
                 r = diskGetLogLength state;
        recovered := fun _ state' =>
                      state' = state
      |}.

  Theorem get_log_length_ok : proc_spec get_log_length_spec get_log_length recover d.abstr.
  Proof.
    unfold get_log_length; intros.
    step_proc.
    destruct (gt_dec r 0).
    {
      step_proc.
      step_proc.
      unfold diskGetLogLength.
      destruct state.
      {
        simpl in g.
        lia.
      }
      {
        SearchAbout (diskGet _ _ = Some _).
        assert (exists r0, diskGet (b :: state) (diskSize (b :: state) - 1) = Some r0).
        {
          eapply disk_inbounds_exists.
          lia.
        }
        destruct H0.
        rewrite H0 in H1.
        simpl in H1.
        subst.
        rewrite H0.
        auto.
      }
    }
    step_proc.
    destruct state.
    {
      unfold diskGetLogLength.
      unfold_diskGet.
      auto.
    }
    {
      exfalso.
      apply n.
      simpl.
      lia.
    }
  Qed.

  Hint Resolve get_log_length_ok : core.

  (** get function *)
  Fixpoint get_rec (len : nat) (remaining : nat) : proc (list block) :=
    match remaining with
    | 0 =>
      Ret nil
    | S remaining' =>
      b <- d.read (len - (S remaining'));
        rest <- get_rec len remaining';
        Ret (b :: rest)
    end.

  Theorem get_rec_ok : forall (len:nat) (remaining:nat),
      proc_spec (fun (_ : unit) disk_state => {|
        pre := len <= diskSize disk_state /\ remaining <= len;
        post := fun blocks disk_state' =>
                 disk_state' = disk_state /\
                 (* diskGets returns a list of options >:( *)
                 map Some blocks = diskGets disk_state (len-remaining) (remaining)
                 ;
        recovered := fun _ disk_state' =>
                      disk_state' = disk_state
      |}) (get_rec len remaining) recover d.abstr.
  Proof.
    intros.
    induction remaining.
    {
      simpl.
      step_proc.
    }
    {
      simpl.
      step_proc.
      step_proc.
      1 : lia.
      step_proc.
      rewrite H3.
      replace (len - S remaining + 1) with (len - remaining) by lia.
      assert (Some r = diskGet state (len - S remaining)).
      {
        destruct (diskGet state (len - S remaining)) eqn:Heq.
        {
          simpl in H2.
          subst; auto.
        }
        {
          apply diskGet_none_size in Heq.
          lia.
        }
      }
      rewrite H1.
      reflexivity.
    }
  Qed.

  Hint Resolve get_rec_ok : core.

  Definition get : proc (list block) :=
    len <- get_log_length;
    r <- get_rec len len;
    Ret r.
  
  Theorem get_ok : proc_spec get_spec get recover abstr.
  Proof.
    unfold get.
    apply spec_abstraction_compose; simpl.

    step_proc.
    {
      exists state2.
      intuition.
    }
    step_proc.
    {
      inversion H0.
      destruct Hlength_inbounds.
      rewrite <- Hlength_on_disk.
      destruct (diskSize state) eqn:Heq.
      {
        intuition.
        rewrite H2.
        lia.
      }
      {
        intuition.
        lia.
      }
    }
    {
      exists state2.
      intuition.
    }
    step_proc.
    {
      exists state2.
      intuition.
      inversion H0.
      rewrite <- Hlength_on_disk in H2.
      replace (length state2 - length state2) with 0 in H2 by lia.
      rewrite <- H2 in Hentries.
      clear - Hentries.
      generalize dependent state2.
      induction r; intros.
      {
        destruct state2.
        1: auto.
        simpl in *.
        inversion Hentries.
      }
      {
        destruct state2.
        {
          simpl in *.
          inversion Hentries.
        }
        {
          simpl in *.
          inversion Hentries.
          replace (diskGet (b :: state2) 0) with (Some b) in H0 by auto.
          assert (diskGets (b :: state2) 1 (length state2) = diskGets state2 0 (length state2)).
          {
            eapply diskGets_eq.
            auto.
          }
          intuition.
          assert (r = state2).
          {
            eapply IHr.
            rewrite <- H1.
            auto.
          }
          subst; auto.
        }
      }
    }
    exists state2.
    intuition.
  Qed.
  
  (** append function *)
  Fixpoint append_rec (bs : list block) (end' : nat) : proc unit :=
    match bs with
    | nil =>
      Ret tt
    | cons b bs' =>
      _ <- d.write (end' - length bs) b;
      _ <- append_rec bs' (end');
      Ret tt
    end.

  Theorem append_rec_ok : forall (bs : list block) (end_ : nat) ,
      proc_spec (fun (_ : unit) disk_state =>
                   let len := diskGetLogLength disk_state in
                   let addr := (end_ - length bs) in {|
                     pre := end_ < (diskSize disk_state)
                           /\ end_ > 0
                           /\ length bs <= end_ - len;
                     post := fun _ disk_state' =>
                              disk_state' = diskUpds disk_state addr bs /\
                              diskGetLogLength disk_state' = diskGetLogLength disk_state /\
                              diskSize disk_state' = diskSize disk_state;
                     recovered := fun _ disk_state' =>
                                   disk_state' = disk_state \/
                                   diskGets disk_state' 0 addr = diskGets disk_state 0 addr /\
                                   diskGetLogLength disk_state = diskGetLogLength disk_state' /\

                                   diskSize disk_state' = diskSize disk_state
                                   ;
      |}) (append_rec bs end_) recover d.abstr.
  Proof.
    induction bs.
    {
      simpl.
      step_proc.
      left; auto.
    }
    {
      simpl.
      step_proc.
      {
        destruct H2.
        1: left; auto.
        right.
        split; intuition.
        {
          Lemma diskGets_upd_eq:
            forall len d a b begin,
              a >= begin + len ->
              diskGets (diskUpd d a b) begin len = diskGets d begin len.
          Proof.
            induction len.
            {
              intros; simpl.
              auto.
            }
            {
              intros.
              simpl.
              specialize (IHlen d a b (begin + 1)).
              assert (a >= begin + 1 + len) by lia.
              intuition.
              rewrite IHlen.
              assert (diskGet d [a |-> b] begin = diskGet d begin).
              {
                eapply diskUpd_neq.
                lia.
              }
              rewrite H1.
              reflexivity.
            }
          Qed.
          eapply diskGets_upd_eq.
          lia.
        }
        {
          unfold diskGetLogLength.
          rewrite diskUpd_size.
          assert (diskGet state (diskSize state - 1) = diskGet state [end_ - S (length bs) |-> a] (diskSize state - 1)).
          {
            symmetry.
            eapply diskUpd_neq.
            lia.
          }
          rewrite H2.
          auto.
        }
        {
          rewrite diskUpd_size.
          auto.
        }
      }
      step_proc.
      {
        rewrite diskUpd_size.
        lia.
      }
      {
        unfold diskGetLogLength.
        rewrite diskUpd_size.
        rewrite diskUpd_neq.
        2: lia.
        unfold diskGetLogLength in H1.
        lia.
      }
      {
        destruct H2.
        {
          right.
          split.
          {
            subst.
            apply diskGets_upd_eq.
            lia.
          }
          split.
          {
            subst.
            unfold diskGetLogLength.
            rewrite diskUpd_size.
            rewrite diskUpd_neq.
            2: lia.
            auto.
          }
          {
            subst.
            rewrite diskUpd_size.
            auto.
          }
        }
        {
          destruct H2.
          destruct H3.
          right.
          split.
          {
            Lemma diskGets_short:
              forall len2 len1 d1 d2 a1 a2,
                len1 <= len2 ->
                diskGets d1 a1 len2 = diskGets d2 a2 len2 ->
                diskGets d1 a1 len1 = diskGets d2 a2 len1.
            Proof.
              induction len2.
              {
                intros.
                replace (len1) with 0 by lia.
                auto.
              }
              {
                intros.
                simpl in H0.
                inversion H0.
                destruct len1.
                1: auto.
                simpl.
                rewrite H2.
                apply (IHlen2 len1) in H3.
                2: lia.
                rewrite H3.
                auto.
              }
            Qed.
            eapply diskGets_short in H2.
            2: instantiate (1:= (end_ - S (length bs))); lia.
            rewrite H2.
            eapply diskGets_upd_eq.
            lia.
          }
          split.
          {
            unfold diskGetLogLength in *.
            rewrite diskUpd_size in H3.
            rewrite diskUpd_neq in H3.
            2: lia.
            auto.
          }
          {
            rewrite diskUpd_size in H4.
            auto.
          }
        }
      }
      step_proc.
      {
        replace (end_ - S (length bs) + 1) with (end_ - length bs) by lia.
        Lemma diskUpd_upds_comm:
          forall bs a_sin a_list d b,
            a_sin < a_list ->
            d [a_sin |-> b] [a_list |=> bs] = d [a_list |=> bs] [a_sin |-> b].
        Proof.
          induction bs.
          {
            intros.
            simpl.
            auto.
          }
          {
            intros.
            destruct a_list.
            1: lia.
            simpl.
            rewrite IHbs.
            2: lia.
            rewrite diskUpd_comm.
            2: lia.
            auto.
          }
        Qed.
        rewrite diskUpd_upds_comm.
        2: lia.
        auto.
      }
      {
        rewrite H3.
        unfold diskGetLogLength.
        rewrite diskUpd_size.
        rewrite diskUpd_neq.
        2: lia.
        reflexivity.
      }
      {
        rewrite H4.
        rewrite diskUpd_size.
        reflexivity.
      }
      right.
      split.
      {
        rewrite diskUpd_upds_comm.
        2: lia.
        rewrite diskGets_upd_eq.
        2: lia.
        Lemma diskGets_upds_eq:
          forall bs len d a begin,
            a >= begin + len ->
            diskGets (diskUpds d a bs) begin len = diskGets d begin len.
        Proof.
          induction bs.
          1: auto.
          intros.
          destruct a0.
          {
            simpl.
            replace len with 0 by lia.
            auto.
          }
          {
            simpl.
            rewrite diskGets_upd_eq.
            2: assumption.
            eapply IHbs.
            lia.
          }
        Qed.
        rewrite diskGets_upds_eq.
        2: lia.
        auto.
      }
      split.
      {
        rewrite H3.
        unfold diskGetLogLength.
        rewrite diskUpd_size.
        rewrite diskUpd_neq.
        2: lia.
        auto.
      }
      {
        rewrite H4.
        rewrite diskUpd_size.
        auto.
      }
    }
  Qed.

  Hint Resolve append_rec_ok : core.

  Definition append (bs : list block) : proc bool :=
    size <- d.size;
      len <- get_log_length;
      if length bs == 0 then
        Ret true
      else if lt_dec (len + length bs) (size-1) then
             _ <- append_rec bs (len + length bs);
               new_len <- addr_to_block (len + length bs);
               _ <- d.write (size - 1) new_len;
               Ret true
           else
             Ret false.

  Theorem append_ok : forall bs, proc_spec (append_spec bs) (append bs) recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    step_proc.
    {
      exists state2.
      intuition.
    }
    step_proc.
    {
      exists state2.
      intuition.
    }
    destruct (equal_dec (length bs) 0).
    {
      step_proc.
      {
        exists (state2 ++ bs).
        split.
        1: left; auto.
        destruct bs.
        {
          replace (state2 ++ []) with state2.
          1: assumption.
          SearchAbout (_ = _ ++ []).
          apply app_nil_end.
        }
        {
          simpl in *.
          lia.
        }
      }
      exists state2.
      intuition.
    }
    {
      destruct (lt_dec (r + length bs) (diskSize state - 1)).
      {
        step_proc; try lia.
        {
          destruct H1.
          {
            exists state2.
            intuition.
          }
          {
            destruct H1.
            destruct H2.
            inversion H0.
            exists state2.
            split.
            1: intuition.
            constructor.
            1: split; intros; lia.
            1: rewrite Hlength_on_disk; auto.
            rewrite Hentries.
            replace (diskGetLogLength state + length bs - length bs) with (diskGetLogLength state) in H1 by lia.
            rewrite Hlength_on_disk.
            auto.
          }
        }
        assert (Hmodify: log_abstraction state [diskGetLogLength state |=> bs] state2).
        {
          inversion H0.
          constructor.
          {
            split; intros.
            1: rewrite diskUpds_size; lia.
            intuition.
            apply H3.
            rewrite diskUpds_size in H1.
            auto.
          }
          {
            rewrite Hlength_on_disk.
            Lemma diskGetLogLength_no_upds:
              forall bs disk start,
                start + length bs <= diskSize disk - 1 ->
                diskGetLogLength (diskUpds disk start bs) = diskGetLogLength disk.
            Proof.
              induction bs.
              1: auto.
              intros.
              destruct start.
              {
                simpl.
                unfold diskGetLogLength in *.
                rewrite diskUpd_size.
                destruct disk.
                1: simpl in H; lia.
                destruct disk.
                1: simpl in H; lia.
                rewrite diskUpd_neq.
                {
                  rewrite IHbs.
                  1: auto.
                  simpl in *.
                  auto.
                }
                rewrite diskUpds_size.
                simpl.
                auto.
              }
              {
                simpl.
                unfold diskGetLogLength in *.
                rewrite diskUpd_size.
                rewrite diskUpd_neq.
                {
                  rewrite IHbs.
                  1: auto.
                  simpl in *.
                  lia.
                }
                simpl in *.
                rewrite diskUpds_size.
                lia.
              }
            Qed.
            rewrite diskGetLogLength_no_upds.
            1: auto.
            lia.
          }
          rewrite diskGets_upds_eq.
          1: auto.
          lia.
        }
        assert (Hmodify2: forall r0,
                   block_to_addr r0 = diskGetLogLength state + length bs ->
                   log_abstraction state [diskGetLogLength state |=> bs] [diskSize state - 1 |-> r0] (state2 ++ bs)).
        {
          intros.
          inversion H0.
          constructor.
          {
            split; intros;
              try rewrite diskUpd_size in *;
              try rewrite diskUpds_size in *.
            {
              rewrite app_length.
              lia.
            }
            intuition.
            lia.
          }
          {
            unfold diskGetLogLength.
            rewrite diskUpd_size.
            rewrite diskUpds_size.
            rewrite diskUpd_eq.
            {
              rewrite app_length.
              rewrite H1.
              lia.
            }
            rewrite diskUpds_size.
            destruct state; lia.
          }
          {
            rewrite app_length.
            rewrite diskUpd_diskGets_neq.
            2: lia.
            rewrite <- Hlength_on_disk in *.
            repeat rewrite diskGets_app.
            assert (diskGets (state2 ++ bs) 0 (length state2) = diskGets state [length state2 |=> bs] 0 (length state2)).
            {
              rewrite diskGets_upds_eq by lia.
              rewrite <- Hentries.
              destruct (length state2) eqn:Heq2.
              1: auto.
              rewrite <- Heq2 in *.
              rewrite diskGets_app_disk.
              2: lia.
              {
                replace (length state2 - 0) with (length state2) by lia.
                replace (length state2 - length state2) with 0 by lia.
                simpl.
                apply app_nil_r.
              }
              lia.
            }
            rewrite H2.
            simpl.
            assert (diskGets state [length state2 |=> bs] (length state2) (length bs) = map Some bs).
            {
              eapply diskUpds_diskGets_eq.
              lia.
            }
            rewrite H3.
            Lemma diskGets_app_right:
              forall b a,
                diskGets (a ++ b) (length a) (length b) = map Some b.
            Proof.
              induction b.
              1: auto.
              simpl.
              assert (forall l, diskGet (l ++ a :: b) (length l) = Some a).
              {
                induction l.
                1: auto.
                simpl.
                unfold_diskGet.
                auto.
              }
              intros.
              rewrite H.
              specialize (IHb (a0 ++ [a])).
              rewrite app_length in IHb.
              simpl in IHb.
              assert ((a0 ++ [a]) ++ b = a0 ++ a :: b).
              {
                SearchAbout ((_ ++ _) ++ _).
                rewrite <- app_assoc.
                simpl.
                auto.
              }
              rewrite <- H0.
              rewrite IHb.
              auto.
            Qed.
            rewrite diskGets_app_right.
            auto.
          }
        }
        step_proc.
        {
          exists state2.
          intuition.
          replace (diskGetLogLength state + length bs - length bs) with (diskGetLogLength state) by lia.
          auto.
        }
        step_proc.
        {
          destruct H1.
          {
            exists state2.
            intuition.
            replace (diskGetLogLength state + length bs - length bs) with (diskGetLogLength state) by lia.
            auto.
          }
          {
            exists (state2 ++ bs).
            intuition.
            try replace (diskGetLogLength state + length bs - length bs) with (diskGetLogLength state) in * by lia.
            intuition.
          }
        }
        step_proc.
        {
          exists (state2 ++ bs).
          intuition.
          replace (diskGetLogLength state + length bs - length bs) with (diskGetLogLength state) by lia.
          intuition.
        }
        exists (state2 ++ bs).
        replace (diskGetLogLength state + length bs - length bs) with (diskGetLogLength state) by lia.
        intuition.
      }
      step_proc.
      {
        exists state2.
        intuition.
      }
      exists state2.
      intuition.
    }
  Qed.

  (** reset function *)
  Definition reset : proc unit :=
    sz <- d.size;
      n_ <- addr_to_block 0;
      _ <- d.write (sz - 1) n_;
      Ret tt.
  
  Theorem reset_ok : proc_spec reset_spec reset recover abstr.
  Proof.
    unfold reset.
    apply spec_abstraction_compose; simpl.
    step_proc.
    {
      exists state2.
      intuition.
    }
    step_proc.
    {
      exists state2.
      intuition.
    }
    step_proc.
    {
      destruct H1.
      {
        exists state2.
        intuition.
      }
      {
        exists [].
        intuition.
        inversion H0.
        constructor.
        {
          split; intros.
          2: auto.
          destruct (diskSize state [diskSize state - 1 |-> r]).
          1: exfalso; apply H; auto.
          simpl; lia.
        }
        {
          simpl in *.
          unfold diskGetLogLength in *.
          rewrite diskUpd_size.
          destruct state eqn:Heq.
          {
            simpl.
            unfold_diskGet.
            auto.
          }
          {
            rewrite diskUpd_eq.
            1: auto.
            simpl.
            lia.
          }
        }
        {
          simpl.
          auto.
        }
      }
    }
    step_proc.
    {
      exists [].
      intuition.
      inversion H0.
      constructor.
      {
        split; intros.
        2: auto.
        simpl; lia.
      }
      {
        simpl.
        unfold diskGetLogLength in *.
        rewrite diskUpd_size.
        destruct state eqn:Heq.
        {
          simpl.
          unfold_diskGet.
          auto.
        }
        {
          rewrite diskUpd_eq.
          1: auto.
          simpl; lia.
        }
      }
      {
        auto.
      }
    }
    exists [].
    intuition.
    inversion H0.
    constructor.
    {
      split; intros.
      2: auto.
      simpl; lia.
    }
    {
      simpl.
      unfold diskGetLogLength in *.
      rewrite diskUpd_size.
      destruct state eqn:Heq.
      {
        simpl.
        unfold_diskGet.
        auto.
      }
      {
        rewrite diskUpd_eq.
        1: auto.
        simpl; lia.
      }
    }
    {
      auto.
    }
  Qed.

  Hint Resolve reset_ok : core.

End Log.


(** It's possible to layer the log from this lab on top
    of the bad-block remapper from the previous lab.
    The statements below do that, just as a sanity check.
  *)

Require Import Lab2.BadBlockImpl.
Require Import Lab2.RemappedDiskImpl.
Module bad_disk := BadBlockDisk.
Module remapped_disk := RemappedDisk bad_disk.
Module log := Log remapped_disk.
Print Assumptions log.append_ok.
