(** Theorems about correctness of 
  Automated Market Maker Contract Implementation **)

From Coq Require Import ZArith_base.
Require Import Coq.QArith.QArith.
From Coq Require Import List. Import ListNotations.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import PTUtils.
From ConCert.Utils Require Import Extras.

(* Automation Tactics *)
From Coq Require Import Lia.
From Hammer Require Import Tactics.
From ConCert.Examples.dexAMM Require Import dexAMM.

(* From ConCert.Examples.EIP20 Require EIP20Token. *)

Section Theories.
  Open Scope N_scope.
  Open Scope bool.


  (** ** Init correct *)
  Lemma init_state_eq : forall chain ctx setup state,
    init chain ctx setup = Ok state ->
      state = {|  getPool := FMap.empty;
          Pools := FMap.empty;
          PIDs := 0;
          Fees := FMap.empty;
          PoolShares := AddressMap.empty;
          dividendPayingERC20 := setup.(dividendPayingERC20_);
          AmplificationFactor := 0;
          admin := ctx.(ctx_from)
      |}.
  Proof.
    intros * init_some.
    unfold init in *.
    try easy.
  Qed.

  Lemma init_correct : forall chain ctx setup state,
    init chain ctx setup = Ok state ->
      getPool state = FMap.empty /\
      Pools state = FMap.empty /\
      PIDs state = 0 /\
      Fees state = FMap.empty /\
      PoolShares state = AddressMap.empty /\
      dividendPayingERC20 state = setup.(dividendPayingERC20_) /\
      AmplificationFactor state = 0 /\
      admin state = ctx.(ctx_from).
  Proof.
    intros * init_some.
    apply init_state_eq in init_some.
    now subst.
  Qed.

  (** Initialization should always succeed *)
  Lemma init_is_some : forall chain ctx setup,
    exists state, init chain ctx setup = state.
  Proof.
    eauto.
  Qed.

  (* Tactic to simplify proof steps *)
  Ltac dexAMM_simpl :=
    match goal with
    | H : receive _ _ _ (Some _) = Ok (_, _) |- _ => cbn in H
    | |- receive _ _ _ (Some _) = Ok (_, _) => cbn
    | H : context[try_createPair] |- _ => unfold try_createPair in H
    | H : context[try_deposit] |- _ => unfold try_deposit in H
    | H : context[try_withdrawFees] |- _ => unfold try_withdrawFees in H
    | H : context[try_withdraw] |- _ => unfold try_withdraw in H
    | H : context[try_swap] |- _ => unfold try_swap in H
    | H : context[error] |- _ => unfold error in H
    | |- context[try_createPair] => unfold try_createPair
    | |- context[try_deposit] => unfold try_deposit
    | |- context[try_withdrawFees] => unfold try_withdrawFees
    | |- context[try_withdraw] => unfold try_withdraw
    | |- context[try_swap] => unfold try_swap
    | |- context[error] => unfold error
    end.

  Ltac address_map_convert :=
    match goal with
    | H : context [ AddressMap.find _ _ ] |- _ => rewrite AddressMap_find_convertible in H
    | H : context [ AddressMap.add _ _ _ ] |- _ => rewrite AddressMap_add_convertible in H
    | |- context [ AddressMap.find _ _ ] => rewrite AddressMap_find_convertible
    | |- context [ AddressMap.add _ _ _ ] => rewrite AddressMap_add_convertible
    end.

  Tactic Notation "contract_simpl" :=
    repeat (
      try dexAMM_simpl;
      try address_map_convert;
      try contract_simpl_step @receive @init).

  Ltac FMap_simpl_step :=
    match goal with
      | |- context [ FMap.find ?x (FMap.add ?x _ _) ] => setoid_rewrite FMap.find_add
      | H : FMap.find ?t ?m = Some _ |- FMap.find ?t ?m = Some _ => cbn; rewrite H; f_equal
      | H : ?x <> ?y |- context [ FMap.find ?x (FMap.add ?y _ _) ] => setoid_rewrite FMap.find_add_ne; eauto
      | H : ?y <> ?x |- context [ FMap.find ?x (FMap.add ?y _ _) ] => setoid_rewrite FMap.find_add_ne; eauto
      | H : FMap.find ?x _ = Some _ |- context [ FMap.elements (FMap.add ?x _ _) ] => setoid_rewrite FMap.elements_add_existing; eauto
      | |- context [ FMap.add ?x _ (FMap.add ?x _ _) ] => setoid_rewrite FMap.add_add
      | H : FMap.find ?x _ = None |- context [ FMap.elements (FMap.add ?x _ _) ] => setoid_rewrite FMap.elements_add; eauto
      | |- context [ FMap.remove ?x (FMap.add ?x _ _) ] => rewrite fin_maps.delete_insert_delete
      | |- context [ FMap.find ?x (FMap.partial_alter _ ?x _) ] => setoid_rewrite FMap.find_partial_alter
      | H : ?x' <> ?x |- context [ FMap.find ?x' (FMap.partial_alter _ ?x _) ] => setoid_rewrite FMap.find_partial_alter_ne; auto
      | H : ?x <> ?x' |- context [ FMap.find ?x' (FMap.partial_alter _ ?x _) ] => setoid_rewrite FMap.find_partial_alter_ne
      | H : context [ AddressMap.find _ _ ] |- _ => rewrite AddressMap_find_convertible in H
      | H : context [ AddressMap.add _ _ _ ] |- _ => rewrite AddressMap_add_convertible in H
      | |- context [ AddressMap.find _ _ ] => rewrite AddressMap_find_convertible
      | |- context [ AddressMap.add _ _ _ ] => rewrite AddressMap_add_convertible
    end.

  Tactic Notation "FMap_simpl" := repeat (FMap_simpl_step; cbn).

(*  Lemma isSome_true : forall (A : Type) (t : A),
    forall (p : option A), p = Some t -> isSome p = true.
  Proof.
    intros A t p H.
    rewrite H. reflexivity.
  Qed.

  Lemma isSome_false : forall (A : Type),
    isSome (None : option A) = true -> False.
  Proof.
    intros A H.
    discriminate H.
  Qed. *)

(** ** Expected behaviour of sberAMM functions *)

(** [try_createPair] can't rewrite pool if it's already exists in state **)
Lemma createPair_not_rewritePair : forall (prev_state new_state :State) 
                                          (chain : Chain) 
                                          (ctx: ContractCallContext) 
                                          (token0 token1 : Address) 
                                          (_fee : N) 
                                          (_isStable : bool),
  (FMap.find (token0, token1) prev_state.(getPool) <> None \/
   FMap.find (token1, token0) prev_state.(getPool) <> None) ->
  receive chain ctx prev_state (Some (createPair token0 token1 _fee _isStable)) = error.
  Proof.
    intros.
    contract_simpl.
    FMap_simpl.
    cbn.
    repeat (destruct_address_eq).
    all: auto.
    simpl.
    destruct (FMap.find (token0, token1) (getPool prev_state)) eqn:find_neq1.
    auto.
    destruct (FMap.find (token1, token0) (getPool prev_state)) eqn:find_neq2.
    auto.
    destruct H as [H1|H2].
    all: contradiction.
  Qed.

Definition createPair_update_correct (old_state new_state : State) 
                                     (token00 token11 : Address) 
                                     (_fee : N)
                                     (_isStable : bool) :=
   let PID_before := old_state.(PIDs) in
   let PID_after := new_state.(PIDs) in
   let map_getPool := FMap.find (token00, token11) new_state.(getPool) in
   match FMap.find PID_after new_state.(Pools) with
    | None => false
    | Some P => (P.(token0) =? token00)%address && (P.(token1) =? token11)%address &&
                (P.(feeRate) =? _fee) && (eqb P.(isStable) _isStable) &&
                (isSome map_getPool)
  end.

(** [try_createPair] correctrly creates pool [(token0, token1)] with id [PIDs + 1], 
    [_fee] and [_isStable] parameters **)
Lemma createPair_correct : forall prev_state new_state chain ctx token0 token1 _fee _isStable,
  receive chain ctx prev_state (Some (createPair token0 token1 _fee _isStable)) = Ok (new_state, []) ->
  createPair_update_correct prev_state new_state token0 token1 _fee _isStable = true.
  Proof.
    intros * receive_some.
    unfold createPair_update_correct.
    contract_simpl.
    cbn in *.
    FMap_simpl.
    destruct_address_eq; auto.
    rewrite N.eqb_refl.
    rewrite Bool.eqb_reflx.
    auto.
  Qed.

Definition deposit_update_correct (old_state new_state : State)
                                  (PID amount_token00 amount_token11 : N)  :=
  match (FMap.find PID old_state.(Pools), FMap.find PID new_state.(Pools)) with
  | (None, None) => true
  | (Some pool_before, Some pool_after) => 
    (pool_before.(amount0) + amount_token00 =? pool_after.(amount0)) && 
    (pool_before.(amount1) + amount_token11 =? pool_after.(amount1)) && 
    (pool_before.(totalShares) + N.sqrt (amount_token00 * amount_token11) =? pool_after.(totalShares))
  | (_, _) => false
  end.

(** [try_deposit] correctrly deposits to [PID] [amount_token0] of token0 and [amount_token1] of token1 **)
Lemma deposit_correct : forall prev_state new_state new_acts chain ctx PID amount_token00 amount_token11,
  receive chain ctx prev_state (Some (deposit PID amount_token00 amount_token11)) = Ok (new_state, new_acts) ->
  deposit_update_correct prev_state new_state PID amount_token00 amount_token11 = true.
  Proof.
    intros * receive_some.
    unfold deposit_update_correct.
    contract_simpl.
    rewrite result_of_option_eq_some in H.
    destruct (FMap.find PID (Pools prev_state)) eqn:find_neq.
    - cbn in *.
      FMap_simpl.
      inversion H.
      repeat (rewrite N.eqb_refl).
      auto.
    - cbn in *.
      FMap_simpl.
      discriminate.
  Qed.

(** Deposit function invokes 2 calls:
    IERC20(token0).safeTransferFrom(msg.sender, address(this), amount_token0);
    IERC20(token1).safeTransferFrom(msg.sender, address(this), amount_token1) **)
Lemma deposit_new_acts_correct : forall prev_state new_state new_acts chain ctx PID amount_token00 amount_token11,
  receive chain ctx prev_state (Some (deposit PID amount_token00 amount_token11)) = Ok (new_state, new_acts) ->
  exists pool, FMap.find PID prev_state.(Pools) = Some pool /\
    new_acts =
      [
        (act_call pool.(token0) 0%Z
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer_from ctx.(ctx_from) ctx.(ctx_contract_address) amount_token00)));
        (act_call pool.(token1) 0%Z
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer_from ctx.(ctx_from) ctx.(ctx_contract_address) amount_token11)))
      ].
  Proof.
    intros * receive_some.
    contract_simpl.
    rewrite result_of_option_eq_some in H.
    destruct (FMap.find PID (Pools prev_state)) eqn:find_neq.
    - cbn in *.
      FMap_simpl.
      inversion H.
      repeat (rewrite N.eqb_refl).
      exists t.
      split.
        + reflexivity.
        + reflexivity.
    - cbn in *.
      FMap_simpl.
      discriminate.
  Qed.

(** If the requirements are met then receive on deposit msg must succeed and
    if receive on deposit msg succeeds then requirements must hold *)
Lemma deposit_is_some : forall prev_state chain ctx PID amount_token00 amount_token11,
    (isSome (FMap.find PID prev_state.(Pools)) = true)
    <->
    exists new_state new_acts, 
      receive chain ctx prev_state (Some (deposit PID amount_token00 amount_token11)) = Ok (new_state, new_acts).
Proof.
  split.
  - intros.
    contract_simpl.
    rewrite result_of_option_eq_some in H0.
    destruct (FMap.find PID (Pools prev_state)) eqn:find_neq.
    + qsimpl.
    + qsimpl.
    + destruct (FMap.find PID (Pools prev_state)).
      discriminate.
      apply PTUtils.isSome_false in H; contradiction.
   - intros.
     contract_simpl.
     destruct (result_of_option (FMap.find PID (Pools prev_state)) default_error) eqn:S.
     * rewrite result_of_option_eq_some in S.
       apply PTUtils.isSome_true in S. auto.
     * intros. destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
Qed.

Definition default_pool := build_pool zero_address zero_address 0 0 0 false 0 0 0.

Definition withdrawFees_update_correct (old_state new_state : State)
                                       (caller : Address)
                                       (PID : N)  :=
  let pool_before := with_default default_pool (FMap.find PID old_state.(Pools)) in
  let shares_map := with_default FMap.empty (AddressMap.find caller old_state.(PoolShares)) in
  let share := with_default 0 (FMap.find PID shares_map) in
  let fees_map_before := with_default FMap.empty (FMap.find PID old_state.(Fees)) in
  let userFees_before := with_default (build_fee 0 0) (FMap.find caller fees_map_before) in 
  let feeToWithdraw0 := pool_before.(fee0) * share / pool_before.(totalShares) - userFees_before.(fee00) in
  let feeToWithdraw1 := pool_before.(fee1) * share / pool_before.(totalShares) - userFees_before.(fee11) in
  let pool_after := with_default default_pool (FMap.find PID new_state.(Pools)) in
  if (0 <? feeToWithdraw0) || (0 <? feeToWithdraw1) then
  let fees_map_after := with_default FMap.empty (FMap.find PID new_state.(Fees)) in
  let userFees_after := with_default (build_fee 0 0) (FMap.find caller fees_map_after) in 
  (pool_before.(amount0) - feeToWithdraw0 =? pool_after.(amount0)) && 
  (pool_before.(amount1) - feeToWithdraw1 =? pool_after.(amount1)) &&
  (userFees_before.(fee00) + feeToWithdraw0 =? userFees_after.(fee00)) &&
  (userFees_before.(fee11) + feeToWithdraw1 =? userFees_after.(fee11))
  else (pool_before.(amount0) - feeToWithdraw0 =? pool_after.(amount0)) && 
     (pool_before.(amount1) - feeToWithdraw1 =? pool_after.(amount1)).

(** [try_withdrawFees] correctly withdraw earned fees from [PID] **)
Lemma withdrawFees_correct : forall prev_state new_state new_acts chain ctx PID,
  receive chain ctx prev_state (Some (withdrawFees PID)) = Ok (new_state, new_acts) ->
  withdrawFees_update_correct prev_state new_state ctx.(ctx_from) PID = true.
  Proof.
    intros * receive_some.
    unfold withdrawFees_update_correct.
    unfold with_default.
    contract_simpl.
    rewrite result_of_option_eq_some in H.
    rewrite result_of_option_eq_some in H0.
    rewrite result_of_option_eq_some in H1.
    rewrite result_of_option_eq_some in H3.
    rewrite result_of_option_eq_some in H4.
    rewrite H. rewrite H0. rewrite H3. rewrite H4. rewrite H1.
    simpl.
    destruct
      ((0 <? fee0 t * t1 / totalShares t - fee00 t3)
      || (0 <? fee1 t * t1 / totalShares t - fee11 t3)).
    - cbn in *.
      contract_simpl. simpl. FMap_simpl.
      repeat (rewrite N.eqb_refl).
      auto.
    - cbn in *.
      contract_simpl. simpl. FMap_simpl.
      repeat (rewrite N.eqb_refl).
      auto.
  Qed.

(** withdrawFees function invokes 2 calls:
   IERC20(pool.token0).safeTransfer(msg.sender, feeToWithdraw0);
   IERC20(pool.token1).safeTransfer(msg.sender, feeToWithdraw1)
**)
Lemma withdrawFees_new_acts_correct : forall prev_state new_state new_acts chain ctx PID,
  receive chain ctx prev_state (Some (withdrawFees PID)) = Ok (new_state, new_acts) ->
  exists pool shares_map share fees_map userFees,
  FMap.find PID prev_state.(Pools) = Some pool /\
  AddressMap.find ctx.(ctx_from) prev_state.(PoolShares) = Some shares_map /\
  FMap.find PID shares_map = Some share /\
  share <> 0 /\
  FMap.find PID prev_state.(Fees) = Some fees_map /\
  FMap.find ctx.(ctx_from) fees_map = Some userFees /\
    new_acts =
      [
        (act_call pool.(token0) 0%Z
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer ctx.(ctx_from) (pool.(fee0) * share / pool.(totalShares) - userFees.(fee00)))));
        (act_call pool.(token1) 0%Z
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer ctx.(ctx_from) (pool.(fee1) * share / pool.(totalShares) - userFees.(fee11)))))
      ].
  Proof.
    intros * receive_some.
    contract_simpl.
    rewrite result_of_option_eq_some in H.
    rewrite result_of_option_eq_some in H0.
    rewrite result_of_option_eq_some in H1.
    rewrite result_of_option_eq_some in H3.
    rewrite result_of_option_eq_some in H4.
    rewrite H. rewrite H0. rewrite H3.
    exists t. exists t0.
    rewrite H1. exists t1. exists t2.
    rewrite H4. exists t3.
    destruct
      ((0 <? fee0 t * t1 / totalShares t - fee00 t3)
      || (0 <? fee1 t * t1 / totalShares t - fee11 t3)).
    - cbn in *.
      contract_simpl. simpl. FMap_simpl.
      ssimpl.
    - cbn in *.
      contract_simpl. simpl. FMap_simpl.
      ssimpl.
  Qed.

(** If the requirements are met then receive on withdrawFees msg must succeed and
    if receive on withdrawFees msg succeeds then requirements must hold *)
Lemma withdrawFees_is_some : forall prev_state chain ctx PID,
  let shares_map := with_default FMap.empty (AddressMap.find ctx.(ctx_from) prev_state.(PoolShares)) in
  let share := with_default 0 (FMap.find PID shares_map) in
  let fees_map := with_default FMap.empty (FMap.find PID prev_state.(Fees)) in
  (isSome (FMap.find PID prev_state.(Pools)) = true) /\
  share <> 0 /\
  (isSome (FMap.find ctx.(ctx_from) fees_map) = true)
  <->
  exists new_state new_acts, 
    receive chain ctx prev_state (Some (withdrawFees PID)) = Ok (new_state, new_acts).
Proof.
  split.
  - intros.
    unfold with_default in H.
    unfold isSome in H.
    contract_simpl.
  + rewrite result_of_option_eq_some in H0.
    rewrite result_of_option_eq_some in H1.
    rewrite result_of_option_eq_some in H2.
    rewrite H1 in H. rewrite H0 in H. rewrite H2 in H.
    destruct (FMap.find PID (Fees prev_state)) eqn:fees_neq.
    unfold result_of_option.
  * destruct (FMap.find (ctx_from ctx) g).
  ** destruct H as [H_left [H_neq H_right]].
  *** destruct (t1 =? 0) eqn:Heq.
      apply N.eqb_eq in Heq. contradiction H_neq.
      destruct (result_of_option (Some g) default_error) eqn:g_neq.
  **** destruct ((0 <? fee0 t * t1 / totalShares t - fee00 f)
                 || (0 <? fee1 t * t1 / totalShares t - fee11 f)).
  ****** qsimpl.
  ****** qsimpl.
  **** apply result_of_option_eq_none in g_neq. discriminate.
  ** destruct H as [H_left [H_neq H_right]]. discriminate. 
  * rewrite FMap.find_empty in H.
    destruct H as [H_left [H_neq H_right]]. discriminate.
  + rewrite result_of_option_eq_some in H0.
    rewrite result_of_option_eq_some in H1.
    apply result_of_option_eq_none in H2.
    rewrite H1 in H. rewrite H2 in H.
    destruct H as [H_left [H_neq H_right]].
    contradiction.
  + rewrite result_of_option_eq_some in H0.
    apply result_of_option_eq_none in H1.
    rewrite H1 in H.
    rewrite FMap.find_empty in H.
    destruct H as [H_left [H_neq H_right]].
    contradiction.
  + apply result_of_option_eq_none in H0.
    rewrite H0 in H.
    destruct H as [H_left [H_neq H_right]].
    discriminate.
  - intros.
    unfold with_default.
    contract_simpl.
    destruct (result_of_option (FMap.find PID (Pools prev_state)) default_error) eqn:P.
  * rewrite result_of_option_eq_some in P.
       apply PTUtils.isSome_true in P.
       rewrite P.
       destruct (result_of_option (FMap.find (ctx_from ctx) (PoolShares prev_state))) eqn:PS.
  ** rewrite result_of_option_eq_some in PS.
     rewrite PS.
     destruct (result_of_option (FMap.find PID t0) default_error) eqn:t0_neq.
     rewrite result_of_option_eq_some in t0_neq.
     rewrite t0_neq.
  *** destruct (t1 =? 0) eqn:Heq.
    ++ destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
    ++ rewrite <- N.eqb_neq.
       rewrite Heq.
       destruct (result_of_option (FMap.find PID (Fees prev_state)) default_error) eqn:f_neq.
    +++ rewrite result_of_option_eq_some in f_neq.
        rewrite f_neq.
        destruct (result_of_option (FMap.find (ctx_from ctx) t2) default_error) eqn:t2_neq.
    ++++ rewrite result_of_option_eq_some in t2_neq.
         rewrite t2_neq.
         unfold isSome.
         auto.
    ++++ destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
    +++ destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
  *** destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
  ** destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
  * destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
Qed.

Definition withdraw_update_correct (old_state new_state : State)
                                   (caller : Address)
                                   (PID : N)  :=
  let pool_before := with_default default_pool (FMap.find PID old_state.(Pools)) in
  let pool_after := with_default default_pool (FMap.find PID new_state.(Pools)) in
  let shares_map_before := with_default FMap.empty (AddressMap.find caller old_state.(PoolShares)) in
  let shares_map_after := with_default FMap.empty (AddressMap.find caller new_state.(PoolShares)) in  
  let share_before := with_default 0 (FMap.find PID shares_map_before) in
  let share_after := with_default 0 (FMap.find PID shares_map_after) in
  let fees_map_before := with_default FMap.empty (FMap.find PID old_state.(Fees)) in
  let fees_map_after := with_default FMap.empty (FMap.find PID new_state.(Fees)) in
  let userFees_before := with_default (build_fee 0 0) (FMap.find caller fees_map_before) in
  let userFees_after := with_default (build_fee 0 0) (FMap.find caller fees_map_after) in
  let feeToWithdraw0 := pool_before.(fee0) * share_before / pool_before.(totalShares) - userFees_before.(fee00) in
  let feeToWithdraw1 := pool_before.(fee1) * share_before / pool_before.(totalShares) - userFees_before.(fee11) in
  let amount_token00 := share_before * (pool_before.(amount0) - feeToWithdraw0) / pool_before.(totalShares) in
  let amount_token11 := share_before * (pool_before.(amount1) - feeToWithdraw1) / pool_before.(totalShares) in
  let a := (0 <? feeToWithdraw0) || (0 <? feeToWithdraw1) in
  let b := (pool_before.(amount0) - feeToWithdraw0 - amount_token00 =? pool_after.(amount0)) && 
  (pool_before.(amount1) - feeToWithdraw1 - amount_token11 =? pool_after.(amount1)) && 
  (pool_before.(totalShares) - share_before =? pool_after.(totalShares)) &&
  (share_after =? 0) in
  (a && b && (userFees_before.(fee00) + feeToWithdraw0 =? userFees_after.(fee00)) &&
   (userFees_before.(fee11) + feeToWithdraw1 =? userFees_after.(fee11))) || 
   (negb a && b).

(** [try_withdraw] correctly withdraw from [PID] and 
      destroy liquidity position **)
Lemma withdraw_correct : forall prev_state new_state new_acts chain ctx PID,
  receive chain ctx prev_state (Some (withdraw PID)) = Ok (new_state, new_acts) ->
  withdraw_update_correct prev_state new_state ctx.(ctx_from) PID = true.
  Proof.
    intros * receive_some.
    unfold withdraw_update_correct.
    unfold withdrawFees_update_correct.
    unfold with_default.
    contract_simpl.
    rename H into H', H1 into H.
    rewrite result_of_option_eq_some in H'.
    rewrite result_of_option_eq_some in H0.
    rewrite result_of_option_eq_some in H3.
    rewrite result_of_option_eq_some in H4.
    rewrite result_of_option_eq_some in H5.
    rewrite result_of_option_eq_some in H6.
    rewrite H'. rewrite H0. rewrite H4. rewrite H5. rewrite H6.
    simpl.
    destruct ((0 <? fee0 t2 * t0 / totalShares t2 - fee00 t4)
      || (0 <? fee1 t2 * t0 / totalShares t2 - fee11 t4)).
    - cbn in *.
      contract_simpl. simpl. FMap_simpl.
      unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools in H3.
      sintuition. rewrite FMap.find_add in H3. inversion H3.
      qsimpl.
      repeat (rewrite N.eqb_refl).
      auto.
    - cbn in *.
      contract_simpl. simpl. FMap_simpl.
      unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools in H3.
      sintuition. rewrite FMap.find_add in H3. inversion H3.
      qsimpl.
      repeat (rewrite N.eqb_refl).
      auto.
  Qed.

(** withdraw function invokes calls from [withdrawFees]:
   IERC20(pool.token0).safeTransfer(msg.sender, feeToWithdraw0);
   IERC20(pool.token1).safeTransfer(msg.sender, feeToWithdraw1)

   Also, it invokes transfers the tokens back to the user:
   IERC20(Pools[PID].token0).safeTransfer(msg.sender, amount_token0);
   IERC20(Pools[PID].token1).safeTransfer(msg.sender, amount_token1)

   And transfers the protocol fee:
   IERC20(Pools[PID].token0).safeTransfer(dividendPayingERC20, protocol_fee_token0);
   IERC20(Pools[PID].token1).safeTransfer(dividendPayingERC20, protocol_fee_token1);
**)
Lemma withdraw_new_acts_correct : forall prev_state new_state new_acts chain ctx PID,
  receive chain ctx prev_state (Some (withdraw PID)) = Ok (new_state, new_acts) ->
  exists pool shares_map share fees_map userFees,
  FMap.find PID prev_state.(Pools) = Some pool /\
  AddressMap.find ctx.(ctx_from) prev_state.(PoolShares) = Some shares_map /\
  FMap.find PID shares_map = Some share /\
  share <> 0 /\
  FMap.find PID prev_state.(Fees) = Some fees_map /\
  FMap.find ctx.(ctx_from) fees_map = Some userFees /\
  let feeToWithdraw0 := pool.(fee0) * share / pool.(totalShares) - userFees.(fee00) in
  let feeToWithdraw1 := pool.(fee1) * share / pool.(totalShares) - userFees.(fee11) in
  let amount_token0 := share * (pool.(amount0) - feeToWithdraw0) / pool.(totalShares) in
  let amount_token1 := share * (pool.(amount1) - feeToWithdraw1) / pool.(totalShares) in
  let protocol_fee_token0 := amount_token0 / 100 in
  let protocol_fee_token1 := amount_token1 / 100 in
  let amount_token0 := amount_token0 - protocol_fee_token0 in
  let amount_token1 := amount_token1 - protocol_fee_token1 in
    new_acts =
      [
        act_call pool.(token0) 0%Z
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer ctx.(ctx_from) feeToWithdraw0));
        act_call pool.(token1) 0%Z
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer ctx.(ctx_from) feeToWithdraw1));
        act_call pool.(token0) 0%Z 
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer ctx.(ctx_from) amount_token0));
        act_call pool.(token1) 0%Z 
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer ctx.(ctx_from) amount_token1));
        act_call pool.(token0) 0%Z 
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer prev_state.(dividendPayingERC20) protocol_fee_token0));
        act_call pool.(token1) 0%Z 
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer prev_state.(dividendPayingERC20) protocol_fee_token1))
      ].
Proof.
    intros * receive_some.
    contract_simpl.
    rewrite result_of_option_eq_some in H.
    rewrite result_of_option_eq_some in H0.
    rewrite result_of_option_eq_some in H3.
    rewrite result_of_option_eq_some in H4.
    rewrite result_of_option_eq_some in H5.
    rewrite result_of_option_eq_some in H6.
    rewrite H. rewrite H4.
    exists t2. exists t. exists t0. exists t3. exists t4.
    destruct ((0 <? fee0 t2 * t0 / totalShares t2 - fee00 t4)
       || (0 <? fee1 t2 * t0 / totalShares t2 - fee11 t4)).
    - unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
      set_State_Pools in H3.
      sintuition.
      rewrite FMap.find_add in H3. inversion H3.
      cbn in *.
      contract_simpl. simpl. FMap_simpl.
      ssimpl.
    - unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
      set_State_Pools in H3.
      sintuition.
      rewrite FMap.find_add in H3. inversion H3.
      qsimpl.
  Qed.

(** If the requirements are met then receive on withdraw msg must succeed and
    if receive on withdraw msg succeeds then requirements must hold *)
Lemma withdraw_is_some : forall prev_state chain ctx PID,
  let shares_map := with_default FMap.empty (AddressMap.find ctx.(ctx_from) prev_state.(PoolShares)) in
  let share := with_default 0 (FMap.find PID shares_map) in
  let pool := with_default default_pool (FMap.find PID prev_state.(Pools)) in
  let fees_map := with_default FMap.empty (FMap.find PID prev_state.(Fees)) in
  let userFees:= with_default (build_fee 0 0) (FMap.find ctx.(ctx_from) fees_map) in
  let feeToWithdraw0 := pool.(fee0) * share / pool.(totalShares) - userFees.(fee00) in
  let feeToWithdraw1 := pool.(fee1) * share / pool.(totalShares) - userFees.(fee11) in
  let amount_token0 := share * (pool.(amount0) - feeToWithdraw0) / pool.(totalShares) in
  let amount_token1 := share * (pool.(amount1) - feeToWithdraw1) / pool.(totalShares) in
  share <> 0 /\
  (isSome (FMap.find PID prev_state.(Pools)) = true) /\
  (isSome (FMap.find ctx.(ctx_from) fees_map) = true) /\
  ((pool.(amount0) - feeToWithdraw0) <? amount_token0) || ((pool.(amount1) - feeToWithdraw1) <? amount_token1) = false
  <->
  exists new_state new_acts, 
    receive chain ctx prev_state (Some (withdraw PID)) = Ok (new_state, new_acts).
Proof.
  split.
  - intros.
    unfold with_default in H.
    unfold isSome in H.
    contract_simpl.
  + rewrite result_of_option_eq_some in H0.
    rewrite result_of_option_eq_some in H1.
    rewrite H0 in H. rewrite H1 in H.
    destruct (FMap.find PID (Fees prev_state)) eqn:fees_neq.
  ++ destruct (FMap.find PID (Pools prev_state)) eqn:pools_neq.
  +++ destruct (FMap.find (ctx_from ctx) g) eqn: g_neq.
      unfold result_of_option.
      rewrite g_neq.
      destruct H as [H_1 [H_2 [H_3 H_4]]].
  *** destruct (t0 =? 0) eqn:Heq.
      apply N.eqb_eq in Heq. contradiction H_1.
      destruct ((0 <? fee0 p * t0 / totalShares p - fee00 f)
      || (0 <? fee1 p * t0 / totalShares p - fee11 f)).
  **** cbn in *.
       FMap_simpl.
       destruct ((amount0 p - (fee0 p * t0 / totalShares p - fee00 f) <?
                 t0 * (amount0 p - (fee0 p * t0 / totalShares p - fee00 f)) /
                  totalShares p)
                || (amount1 p - (fee1 p * t0 / totalShares p - fee11 f) <?
                   t0 * (amount1 p - (fee1 p * t0 / totalShares p - fee11 f)) /
                    totalShares p)).
      discriminate.
      unfold setter_from_getter_State_PoolShares,
            setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools, set_State_PoolShares, set_State_Fees.
      sintuition.
    **** cbn in *.
         FMap_simpl.
         destruct ((amount0 p - (fee0 p * t0 / totalShares p - fee00 f) <?
                   t0 * (amount0 p - (fee0 p * t0 / totalShares p - fee00 f)) /
                    totalShares p)
                  || (amount1 p - (fee1 p * t0 / totalShares p - fee11 f) <?
                     t0 * (amount1 p - (fee1 p * t0 / totalShares p - fee11 f)) /
                      totalShares p)).
         discriminate.
         unfold setter_from_getter_State_PoolShares,
            setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools, set_State_PoolShares, set_State_Fees.
        sintuition.
  *** destruct H as [H_1 [H_2 [H_3 H_4]]].
      discriminate.
  +++ destruct H as [H_1 [H_2 [H_3 H_4]]].
      discriminate.
  ++ rewrite FMap.find_empty in H.
     sintuition.
  + rewrite result_of_option_eq_some in H0.
    apply result_of_option_eq_none in H1.
    rewrite H0 in H. rewrite H1 in H.
    destruct H as [neq H_1].
    contradiction.
  + apply result_of_option_eq_none in H0.
    rewrite H0 in H.
    rewrite FMap.find_empty in H.
    destruct H as [neq H_1].
    contradiction.
  - intros.
    unfold with_default.
    unfold isSome.
    contract_simpl.
    destruct (result_of_option (FMap.find PID (Pools prev_state))) eqn: P.
  * rewrite result_of_option_eq_some in P.
    rewrite P.
    apply PTUtils.isSome_true in P.
    destruct (result_of_option (FMap.find (ctx_from ctx) (PoolShares prev_state))) eqn:PS.
  ** rewrite result_of_option_eq_some in PS.
     rewrite PS.
     destruct (result_of_option (FMap.find PID t0) default_error) eqn:t0_neq.
     rewrite result_of_option_eq_some in t0_neq.
     rewrite t0_neq.
  *** destruct (t1 =? 0) eqn:Heq.
    ++ destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
    ++ rewrite <- N.eqb_neq.
       rewrite Heq.
       destruct (result_of_option (FMap.find PID (Fees prev_state)) default_error) eqn:f_neq.
    +++ rewrite result_of_option_eq_some in f_neq.
        rewrite f_neq.
        destruct (result_of_option (FMap.find (ctx_from ctx) t2) default_error) eqn:t2_neq.
    ++++ rewrite result_of_option_eq_some in t2_neq.
         rewrite t2_neq.
         unfold isSome.
         destruct ((0 <? fee0 t * t1 / totalShares t - fee00 t3)
          || (0 <? fee1 t * t1 / totalShares t - fee11 t3)) eqn:fee_neq.
    +++++ sintuition. 
          rewrite FMap.find_add in H0.
          unfold result_of_option in H0.
          sintuition.
    destruct ((amount0 t - (fee0 t * t1 / totalShares t - fee00 t3) <?
        t1 * (amount0 t - (fee0 t * t1 / totalShares t - fee00 t3)) /
        totalShares t)
       || (amount1 t - (fee1 t * t1 / totalShares t - fee11 t3) <?
           t1 * (amount1 t - (fee1 t * t1 / totalShares t - fee11 t3)) /
           totalShares t)) eqn:am_neq.
      ssimpl. auto.
    +++++ sintuition. 
          rewrite FMap.find_add in H0.
          unfold result_of_option in H0.
          sintuition.
    destruct ((amount0 t - (fee0 t * t1 / totalShares t - fee00 t3) <?
        t1 * (amount0 t - (fee0 t * t1 / totalShares t - fee00 t3)) /
        totalShares t)
       || (amount1 t - (fee1 t * t1 / totalShares t - fee11 t3) <?
           t1 * (amount1 t - (fee1 t * t1 / totalShares t - fee11 t3)) /
           totalShares t)) eqn:am_neq.
      ssimpl. auto.
    ++++ destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
+++ all: destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
*** destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
**  destruct H as [new_state [new_acts H_eq]]. discriminate H_eq.
* qsimpl.
Qed.

Definition swap_update_correct (old_state new_state : State)
                               (caller : Address)
                               (PID : N)
                               (tokenIn : Address)
                               (amount : N)  :=
  let pool_before := with_default default_pool (FMap.find PID old_state.(Pools)) in
  let pool_after := with_default default_pool (FMap.find PID new_state.(Pools)) in
  let fee := pool_before.(feeRate) * amount in
  let amountMinusFee := amount - fee in
  if (pool_before.(isStable)) then
  if (address_eqb pool_before.(token0) tokenIn) then
  let amountOut := Z.to_N (_swapQuoteFunc pool_before.(amount0) pool_before.(amount1) amountMinusFee (Z.of_N (old_state.(AmplificationFactor))#100)) in
  (pool_before.(amount0) + amount =? pool_after.(amount0)) &&
  (pool_before.(amount1) - amountOut =? pool_after.(amount1)) &&
  (pool_before.(fee0) + fee =? pool_after.(fee0))
  else
  let amountOut := Z.to_N (_swapQuoteFunc pool_before.(amount1) pool_before.(amount0) amountMinusFee (Z.of_N (old_state.(AmplificationFactor))#100)) in
  (pool_before.(amount1) + amount =? pool_after.(amount1)) &&
  (pool_before.(amount0) - amountOut =? pool_after.(amount0)) &&
  (pool_before.(fee1) + fee =? pool_after.(fee1)) 
  else if (address_eqb pool_before.(token0) tokenIn) then
  let amountOut := amountMinusFee * pool_before.(amount1) / (amountMinusFee + pool_before.(amount0)) in
  (pool_before.(amount0) + amount =? pool_after.(amount0)) &&
  (pool_before.(amount1) - amountOut =? pool_after.(amount1)) &&
  (pool_before.(fee0) + fee =? pool_after.(fee0))
  else
  let amountOut := amountMinusFee * pool_before.(amount0) / (amountMinusFee + pool_before.(amount1)) in
  (pool_before.(amount1) + amount =? pool_after.(amount1)) &&
  (pool_before.(amount0) - amountOut =? pool_after.(amount0)) &&
  (pool_before.(fee1) + fee =? pool_after.(fee1)).

(** [try_swap] correctly swaps **)
Lemma swap_correct : forall prev_state new_state new_acts chain ctx PID tokenIn,
  receive chain ctx prev_state (Some (swap PID tokenIn)) = Ok (new_state, new_acts) ->
  swap_update_correct prev_state new_state ctx.(ctx_from) PID tokenIn (Z.to_N ctx.(ctx_amount)) = true.
  Proof.
    intros * receive_some.
    unfold swap_update_correct.
    unfold with_default.
    contract_simpl.
    rewrite result_of_option_eq_some in H.
    simpl.
    destruct ((token0 t =? tokenIn)%address) eqn:A0.
    - cbn in *.
      contract_simpl. simpl. FMap_simpl.
      destruct (isStable t) eqn:stable_cond.
      + cbn in *.
        contract_simpl. simpl. FMap_simpl.
        unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools in H2.
        rewrite result_of_option_eq_some in H3.
        unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools in H3.
        sintuition.
        rewrite FMap.find_add in H3. inversion H3.
        qsimpl.
        rewrite FMap.find_add in Heqo0. inversion Heqo0.
        qsimpl.
        repeat (rewrite N.eqb_refl).
        rewrite <- PTUtils.add_assoc1.
        rewrite N.eqb_refl.
        auto.
        apply N.leb_le.
        rewrite H0. auto.
        rewrite FMap.find_add in Heqo0. discriminate.
      + cbn in *.
        contract_simpl. simpl. FMap_simpl.
        unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools in H2.
        rewrite result_of_option_eq_some in H3.
        unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools in H3.
        sintuition.
        rewrite FMap.find_add in H3. inversion H3.
        qsimpl.
        rewrite FMap.find_add in Heqo0. inversion Heqo0.
        qsimpl.
        repeat (rewrite N.eqb_refl).
        rewrite <- PTUtils.add_assoc1.
        rewrite N.eqb_refl.
        auto.
        apply N.leb_le.
        rewrite H0. auto.
        rewrite FMap.find_add in Heqo0. discriminate.
    - cbn in *.
      contract_simpl. simpl. FMap_simpl.
      destruct (isStable t) eqn:stable_cond.
      + cbn in *.
        contract_simpl. simpl. FMap_simpl.
        unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools in H3.
        rewrite result_of_option_eq_some in H4.
        unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools in H4.
        sintuition.
        rewrite FMap.find_add in H4. inversion H4.
        qsimpl.
        rewrite FMap.find_add in Heqo0. inversion Heqo0.
        qsimpl.
        repeat (rewrite N.eqb_refl).
        rewrite <- PTUtils.add_assoc1.
        rewrite N.eqb_refl.
        auto.
        apply N.leb_le.
        rewrite H0. auto.
        rewrite FMap.find_add in Heqo0. discriminate.
      + cbn in *.
        contract_simpl. simpl. FMap_simpl.
        unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools in H3.
        rewrite result_of_option_eq_some in H4.
        unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
            set_State_Pools in H4.
        sintuition.
        rewrite FMap.find_add in H4. inversion H4.
        qsimpl.
        rewrite FMap.find_add in Heqo0. inversion Heqo0.
        qsimpl.
        repeat (rewrite N.eqb_refl).
        rewrite <- PTUtils.add_assoc1.
        rewrite N.eqb_refl.
        auto.
        apply N.leb_le.
        rewrite H0. auto.
        rewrite FMap.find_add in Heqo0. discriminate.
  Qed.

(** Swap function invokes 2 calls:
     IERC20(tokenIn).transferFrom(msg.sender, address(this), amount);
     IERC20(tokenOut).safeTransfer(msg.sender, uint(amountOut)) **)
Lemma swap_new_acts_correct : forall prev_state new_state new_acts chain ctx PID tokenIn,
  receive chain ctx prev_state (Some (swap PID tokenIn)) = Ok (new_state, new_acts) ->
  exists pool,
  FMap.find PID prev_state.(Pools) = Some pool /\
  let amountIn := Z.to_N (ctx.(ctx_amount)) in
  let fee := pool.(feeRate) * amountIn in
  let amountMinusFee := amountIn - fee in
  if (pool.(isStable)) then
  if (address_eqb pool.(token0) tokenIn) then
  let amountOut := Z.to_N (_swapQuoteFunc pool.(amount0) pool.(amount1) amountMinusFee (Z.of_N (prev_state.(AmplificationFactor))#100)) in
    new_acts =
      [
        act_call pool.(token0) 0%Z
          (@serialize EIP20Token.Msg _
            (EIP20Token.transfer_from ctx.(ctx_from) ctx.(ctx_contract_address) amountIn));
        act_call pool.(token1) 0%Z 
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer ctx.(ctx_from) amountOut))
      ]
  else let amountOut := Z.to_N (_swapQuoteFunc pool.(amount1) pool.(amount0) amountMinusFee (Z.of_N (prev_state.(AmplificationFactor))#100)) in
    new_acts =
      [
        act_call pool.(token1) 0%Z
          (@serialize EIP20Token.Msg _
            (EIP20Token.transfer_from ctx.(ctx_from) ctx.(ctx_contract_address) amountIn));
        act_call pool.(token0) 0%Z 
          (@serialize EIP20Token.Msg _
            (EIP20Token.transfer ctx.(ctx_from) amountOut))
      ]
  else
  if (address_eqb pool.(token0) tokenIn) then
  let amountOut := amountMinusFee * pool.(amount1) / (amountMinusFee + pool.(amount0)) in
    new_acts =
      [
        act_call pool.(token0) 0%Z
          (@serialize EIP20Token.Msg _
            (EIP20Token.transfer_from ctx.(ctx_from) ctx.(ctx_contract_address) amountIn));
        act_call pool.(token1) 0%Z 
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer ctx.(ctx_from) amountOut))
      ]
  else let amountOut := amountMinusFee * pool.(amount0) / (amountMinusFee + pool.(amount1)) in
    new_acts =
      [
        act_call pool.(token1) 0%Z
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer_from ctx.(ctx_from) ctx.(ctx_contract_address) amountIn));
        act_call pool.(token0) 0%Z 
          (@serialize EIP20Token.Msg _ 
            (EIP20Token.transfer ctx.(ctx_from) amountOut))
      ].
Proof.
    intros * receive_some.
    contract_simpl.
    rewrite result_of_option_eq_some in H.
    rewrite H.
    exists t.
    destruct (isStable t).
    - unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
      set_State_Pools in receive_some.
      destruct ((token0 t =? tokenIn)%address) eqn:addr0.
      + rewrite PTUtils.address_eq in addr0.
        rewrite addr0.
        sintuition.
        qsimpl.
      + destruct ((token1 t =? tokenIn)%address) eqn:addr1.
        rewrite PTUtils.address_eq in addr1.
        rewrite addr1.
        sintuition.
        all: qsimpl.
    - unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
      set_State_Pools in receive_some.
      destruct ((token0 t =? tokenIn)%address) eqn:addr0.
      + rewrite PTUtils.address_eq in addr0.
        rewrite addr0.
        sintuition.
        qsimpl.
      + destruct ((token1 t =? tokenIn)%address) eqn:addr1.
        rewrite PTUtils.address_eq in addr1.
        rewrite addr1.
        sintuition.
        all: qsimpl.
  Qed.

(* Lemma swap_is_some : forall prev_state chain ctx PID tokenIn,
  let pool := the default_pool (FMap.find PID prev_state.(Pools)) in
  let fee := pool.(feeRate) * Z.to_N (ctx.(ctx_amount)) in
  let amountMinusFee := Z.to_N (ctx.(ctx_amount)) - fee in
  N.leb fee (Z.to_N (ctx.(ctx_amount))) = true /\
  (address_eqb pool.(token0) tokenIn || address_eqb pool.(token1) tokenIn) = true
  <->
  exists new_state new_acts, 
    receive chain ctx prev_state (Some (swap PID tokenIn)) = Ok (new_state, new_acts).
Proof.
  split.
  - intros.
    unfold the in H.
    unfold isSome in H.
    contract_simpl.
  + rewrite result_of_option_eq_some in H0.
    rewrite H0 in H.
    destruct (feeRate t * Z.to_N (ctx_amount ctx) <=? Z.to_N (ctx_amount ctx)) eqn:f.
    * destruct ((token0 t =? tokenIn)%address) eqn:a0.
      ** destruct (isStable t).
*** unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
      set_State_Pools.
qsimpl.
  apply result_of_option_eq_none in Heqr.
  rewrite FMap.find_add in Heqr.
  discriminate.
*** unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
      set_State_Pools.
qsimpl.
  apply result_of_option_eq_none in Heqr.
  rewrite FMap.find_add in Heqr.
discriminate.
      ** destruct ((token1 t =? tokenIn)%address) eqn:a1.
         *** destruct (isStable t).
**** unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
      set_State_Pools.
qsimpl.
  apply result_of_option_eq_none in Heqr.
  rewrite FMap.find_add in Heqr.
  discriminate.
**** unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
      set_State_Pools.
qsimpl.
  apply result_of_option_eq_none in Heqr.
  rewrite FMap.find_add in Heqr.
discriminate.

         *** destruct (isStable t).
**** unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
      set_State_Pools.
qsimpl.
**** unfold setter_from_getter_State_Fees, setter_from_getter_State_Pools, 
      set_State_Pools.
qsimpl.

* destruct H as [H_left H_right]. discriminate.
+ apply result_of_option_eq_none in H0.
    rewrite H0 in H.
    unfold default_pool in H.
    sintuition.
*)

End Theories.