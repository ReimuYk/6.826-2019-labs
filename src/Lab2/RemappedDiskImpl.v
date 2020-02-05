Require Import POCS.
Require Import OneDiskAPI.
Require Import BadBlockAPI.


Module RemappedDisk (bd : BadBlockAPI) <: OneDiskAPI.

  Import ListNotations.

  Definition read (a : addr) : proc block :=
    bs <- bd.getBadBlock;
    if a == bs then
      len <- bd.size;
      r <- bd.read (len-1);
      Ret r
    else
      r <- bd.read a;
    Ret r.

  Definition write (a : addr) (b : block) : proc unit :=
    bs <- bd.getBadBlock;
    len <- bd.size;
    if a == bs then
      _ <- bd.write (len-1) b;
      Ret tt
    else
      if a == (len-1) then
        Ret tt
      else
        _ <- bd.write a b;
        Ret tt.

  Definition size : proc nat :=
    len <- bd.size;
    Ret (len - 1).

  Definition init' : proc InitResult :=
    len <- bd.size;
    if len == 0 then
      Ret InitFailed
    else
      bs <- bd.getBadBlock;
      if (lt_dec bs len) then
        Ret Initialized
      else
        Ret InitFailed.

  Definition init := then_init bd.init init'.

  Definition recover: proc unit :=
    bd.recover.

  Inductive remapped_abstraction (bs_state : BadBlockAPI.State) (rd_disk : OneDiskAPI.State) : Prop :=
    | RemappedAbstraction :
      let bs_disk := stateDisk bs_state in
      let bs_addr := stateBadBlock bs_state in
      forall
        (* Fill in the rest of your abstraction here. *)
        (* To refer to the contents of disk [d] at address [a], you can write [diskGet a] *)
        (* To refer to the size of disk [d], you can write [diskSize d] *)
        (* You can try to prove [read_ok] to discover what you need from this abstraction *)

        (* Hint 1: What should be true about the non-bad blocks?   Replace [True] with what needs to be true *)
        (Hgoodblocks :
           forall a,
             (a < diskSize rd_disk /\ ~(a = bs_addr)) ->
             nth_error bs_disk a = nth_error rd_disk a
        )
        (* Hint 2: What should be true about the bad block? *)
        (Hbadblock :
           (bs_addr < diskSize rd_disk) ->
           diskGet rd_disk bs_addr = diskGet bs_disk (diskSize bs_disk - 1)
        )

        (* when writing the above,  *)
        (* Hint 3: What if the bad block address is the last address? *)
        (Hsize : diskSize bs_disk = diskSize rd_disk + 1),
      remapped_abstraction bs_state rd_disk.

  Print remapped_abstraction.
  Hint Constructors remapped_abstraction : core.

  Definition abstr : Abstraction OneDiskAPI.State :=
    abstraction_compose bd.abstr {| abstraction := remapped_abstraction |}.

  (* Note that these examples aren't trivial to prove, even if you have the
     right abstraction relation. They should help you think about whether your
     abstraction relation makes sense (although you may need to modify it to
     actually prove the implementation correct). *)

  Example abst_1_ok : forall Hinbounds,
    remapped_abstraction (BadBlockAPI.mkState [block1;block0;block0] 0 Hinbounds) [block0;block0].
  Proof.
    constructor; auto.
    simpl; intros.
    assert (a = 1) by lia.
    rewrite H0.
    auto.
  Qed.

  Example abst_2_ok : forall Hinbounds,
    remapped_abstraction (BadBlockAPI.mkState [block1;block0] 0 Hinbounds) [block0].
  Proof.
    constructor; auto.
    simpl; intros.
    lia.
  Qed.

  Example abst_3_ok : forall Hinbounds,
    remapped_abstraction (BadBlockAPI.mkState [block0;block0] 1 Hinbounds) [block0].
  Proof.
    constructor; auto.
    {
      simpl; intros.
      assert (a = 0) by lia.
      rewrite H0; auto.
    }
    {
      simpl; intros.
      lia.
    }
  Qed.

  Example abst_4_nok : forall Hinbounds,
    ~ remapped_abstraction (BadBlockAPI.mkState [block0;block0] 1 Hinbounds) [block1].
  Proof.
    intros.
    intro.
    inversion H; simpl in *.
    specialize (Hgoodblocks 0).
    simpl in *.
    unfold bs_addr in Hgoodblocks.
    intuition.
    inversion Hgoodblocks.
    Print bytes_differ.
    apply bytes_differ in H1.
    -
      auto.
    -
      unfold blockbytes.
      lia.
  Qed.

  Example abst_5_nok : forall Hinbounds,
    ~ remapped_abstraction (BadBlockAPI.mkState [block1;block1] 0 Hinbounds) [block0].
  Proof.
    intros.
    intro.
    inversion H; simpl in *.
    unfold bs_addr in Hbadblock.
    intuition.
    inversion Hbadblock.
    apply bytes_differ in H1.
    -
      auto.
    -
      unfold blockbytes.
      lia.
  Qed.

  (* Due to how remapped_abstraction is defined (as an inductive), it cannot be
  unfolded. This tactic identifies abstraction relations in the hypotheses and
  breaks them apart with [inversion], and also does some cleanup. *)
  Ltac invert_abstraction :=
    match goal with
    | H : remapped_abstraction _ _ |- _ => inversion H; clear H; subst; subst_var
    end.

  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eapply then_init_compose; eauto.
    step_proc.
    destruct r as [|n].
    {
      simpl.
      step_proc.
    }
    {
      simpl.
      step_proc.
      destruct (lt_dec r (S n)).
      {
        step_proc.
        exists (let bs_disk := stateDisk state in
                let bs_addr := stateBadBlock state in
                let shrunk := diskShrink bs_disk in
                let replaced := match diskGet bs_disk n with
                                | None => block0
                                | Some a => a
                                end in
                diskUpd shrunk bs_addr replaced
               ).
        simpl.
        intuition.
        constructor.
        {
          simpl; intros.
          destruct H0.
          assert (a0 < diskSize (stateDisk state) - 1).
          {
            rewrite diskUpd_size in H0.
            rewrite diskShrink_size in H0.
            -
              assumption.
            -
              rewrite <- H1.
              lia.
          }
          rewrite <- diskShrink_preserves.
          {
            rewrite diskUpd_neq; auto.
          }
          rewrite diskShrink_size.
          -
            rewrite <- H1.
            lia.
          -
            rewrite <- H1.
            lia.
        }
        {
          simpl; intros.
          rewrite diskUpd_size in H0.
          rewrite diskShrink_size in H0.
          2 : rewrite <- H1; lia.
          rewrite diskUpd_eq.
          2 : rewrite diskShrink_size; auto; lia.
          assert (n = diskSize (stateDisk state) - 1).
          {
            rewrite <- H1.
            lia.
          }
          rewrite H2.
          assert (forall disk, ~(disk = nil) ->
                               exists v, diskGet disk (diskSize disk - 1) = Some v).
          {
            intros.
            destruct disk.
            {
              exfalso.
              apply H3.
              auto.
            }
            clear H3.
            simpl.
            replace (diskSize disk - 0) with (diskSize disk) by lia.
            induction disk.
            {
              simpl.
              exists b.
              auto.
            }
            {
              destruct IHdisk.
              simpl.
              destruct (diskSize disk).
              {
                simpl.
                exists a0.
                auto.
              }
              {
                simpl in *.
                exists x.
                assumption.
              }
            }
          }
          specialize (H3 (stateDisk state)).
          assert (stateDisk state <> []).
          {
            destruct (stateDisk state).
            {
              inversion H1.
            }
            {
              unfold not.
              intros.
              inversion H4.
            }
          }
          apply H3 in H4.
          destruct H4.
          rewrite H4.
          reflexivity.
        }
        assert (n = diskSize (stateDisk state) - 1).
        {
          rewrite <- H1.
          simpl.
          lia.
        }
        rewrite diskUpd_size.
        rewrite diskShrink_size.
        {
          lia.
        }
        rewrite <- H1.
        intuition.
      }
      step_proc.
    }    
  Qed.

  Theorem bad_block_inbounds :
    forall state,
      stateBadBlock state < diskSize (stateDisk state).
  Proof.
    intros.
    destruct state.
    simpl.
    exact stateBadBlockInBounds.
  Qed.

  Theorem read_ok : forall a, proc_spec (OneDiskAPI.read_spec a) (read a) recover abstr.
  Proof.
    unfold read.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; eauto.

    destruct (a == r) eqn:Heq.
    {
      step_proc.
      {
        exists state2.
        split; auto.
      }
      step_proc.
      {
        exists state2.
        split; auto.
      }
      step_proc.
      {
        exists state2.
        split; auto.
        split; auto.
        invert_abstraction.
        destruct (diskSize (stateDisk state) - 1 == stateBadBlock state).
        {
          assert (diskGet state2 (stateBadBlock state) = None).
          {
            rewrite <- e.
            rewrite -> Hsize.

            rewrite -> disk_oob_eq.
            2: lia.
            trivial.
          }
          unfold maybe_eq.
          apply holds_in_none_eq.
          assumption.
        }
        {
          rewrite <- Hbadblock in H2.
          {
            apply H2 in n.
            assumption.
          }

          assert (stateBadBlock state < diskSize (stateDisk state)).
          {
            apply bad_block_inbounds.
          }
          lia.
        }
      }
      exists state2.
      split; auto.
    }
    {
      step_proc.
      {
        exists state2.
        split; auto.
      }
      step_proc.
      {
        exists state2.
        split; auto.
        split; auto.
        invert_abstraction.
        case (lt_dec a (diskSize state2)); intros.
        {
          rewrite <- Hgoodblocks.
          2: intuition.
          intuition.
        }
        {
          assert (diskGet state2 a = None).
          {
            apply disk_oob_eq.
            assumption.
          }
          unfold maybe_eq.
          apply holds_in_none_eq.
          assumption.
        }
      }
      exists state2.
      split; auto.
    }
  Qed.

  Theorem remapped_abstraction_diskUpd_remap : forall state state' s v,
    remapped_abstraction state s ->
    stateBadBlock state' = stateBadBlock state ->
    stateDisk state' = diskUpd (stateDisk state) (diskSize (stateDisk state) - 1) v ->
    remapped_abstraction state' (diskUpd s (stateBadBlock state) v).
  Proof.
    (* Hint: you may find it useful to use the [pose proof (bad_block_inbounds state)]
       if you need [lia] to make use of the fact that the bad block is in-bounds. *)
    intros.
    constructor.
    {
      (* proving Hgoodblocks. *)
      intros. intuition.
      invert_abstraction.
      rewrite -> H0 in H3.
      rewrite -> diskUpd_size in H2.
      rewrite -> H1.
      repeat rewrite -> diskUpd_neq by lia.
      apply Hgoodblocks.
      intuition.
    }
    {
      (* proving Hbadblock. *)
      intros.
      rewrite -> H0.
      rewrite -> H0 in H2.
      rewrite -> diskUpd_size in H2.
      rewrite -> H1.
      rewrite -> diskUpd_size.
      invert_abstraction.
      repeat rewrite -> diskUpd_eq by lia.
      trivial.
    }
    {
      (* proving Hsize. *)
      rewrite -> H1.
      rewrite diskUpd_size.
      rewrite diskUpd_size.
      invert_abstraction.
      assumption.
    }
  Qed.

  Theorem remapped_abstraction_diskUpd_noremap : forall state state' s a v,
    remapped_abstraction state s ->
    a <> diskSize (stateDisk state) - 1 ->
    a <> stateBadBlock state ->
    stateBadBlock state' = stateBadBlock state ->
    stateDisk state' = diskUpd (stateDisk state) a v ->
    remapped_abstraction state' (diskUpd s a v).
  Proof.
    intros.
    constructor.
    {
      (* Proving Hgoodblocks. *)
      intros.
      intuition.
      rewrite -> H2 in H5.
      rewrite -> diskUpd_size in H4.
      rewrite -> H3.
      invert_abstraction.
      case (equal_dec a a0).
      {
        intros.
        rewrite <- e.
        repeat rewrite diskUpd_eq by lia.
        trivial.
      }
      {
        intros.
        repeat rewrite diskUpd_neq by lia.
        apply Hgoodblocks.
        lia.
      }
    }
    {
      (* Proving Hbadblock. *)
      intros.
      rewrite -> H2 in H4.
      rewrite -> H2.
      rewrite -> H3.
      invert_abstraction.
      rewrite -> diskUpd_size.
      repeat rewrite diskUpd_neq by lia.
      apply Hbadblock.
      rewrite diskUpd_size in H4.
      assumption.
    }
    {
      (* Hsize. *)
      rewrite -> H3.
      rewrite diskUpd_size.
      rewrite diskUpd_size.
      invert_abstraction.
      assumption.
    }
  Qed.

  Hint Resolve remapped_abstraction_diskUpd_remap : core.
  Hint Resolve remapped_abstraction_diskUpd_noremap : core.

  Theorem write_ok : forall a v, proc_spec (OneDiskAPI.write_spec a v) (write a v) recover abstr.
  Proof.
    unfold write.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc.
    {
      exists state2.
      split; auto.
    }
    step_proc.
    {
      exists state2.
      split; auto.
    }
    case (equal_dec a (stateBadBlock state)).
    {
      intros.
      step_proc.
      {
        destruct H1.
        {
          exists state2.
          split; auto.
          subst; auto.
        }
        {
          exists (diskUpd state2 (stateBadBlock state) v).
          split; auto.
          destruct H1.
          intuition.
        }
      }
      step_proc.
      {
        exists (diskUpd state2 (stateBadBlock state) v).
        split; auto.
      }
      exists (diskUpd state2 (stateBadBlock state) v).
      intuition.
    }
    {
      intros.
      case (equal_dec a (r-1)).
      {
        intros.
        step_proc.
        {
          exists state2.
          intuition.
          invert_abstraction.
          rewrite Hsize.
          rewrite diskUpd_none.
          1: auto.
          replace (diskSize state2 + 1 - 1) with (diskSize state2) by lia.
          clear.
          induction state2; auto.
        }
        exists state2.
        intuition.
      }
      {
        intros.
        step_proc.
        {
          destruct H1.
          {
            exists state2.
            intuition.
          }
          {
            exists (diskUpd state2 a v).
            intuition.
            eauto.
          }
        }
        step_proc.
        {
          exists (diskUpd state2 a v).
          intuition.
          eauto.
        }
        exists (diskUpd state2 a v).
        intuition.
        eauto.
      }
    }
  Qed.

  Theorem size_ok : proc_spec OneDiskAPI.size_spec size recover abstr.
  Proof.
    unfold diskSize.
    intros.

    apply spec_abstraction_compose; simpl.

    step_proc; eauto.
    step_proc.
    {
      exists state2.
      intuition.
      invert_abstraction.
      rewrite Hsize.
      lia.
    }
    exists state2.
    intuition.
  Qed.

  (* This proof proves that recovery corresponds to no_wipe. *)
  Theorem recover_wipe : rec_wipe recover abstr no_wipe.
  Proof.
    unfold rec_wipe.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; eauto.
  Qed.

End RemappedDisk.


Require Import BadBlockImpl.
Module x := RemappedDisk BadBlockDisk.
Print Assumptions x.write_ok.
