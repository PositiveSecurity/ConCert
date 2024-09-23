(** * Automated Market Maker Contract Implementation *)
(**
  This file contains an implementation of the AMM 
(https://github.com/partylikeits1983/sberAMM/blob/main/contracts/AMM.sol).

*)
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.
From Coq Require Import QArith.QArith.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import BoundedN.
From ConCert.Execution Require Import PTUtils.
Import BoundedN.Stdpp.
From ConCert.Utils Require Import Extras.
From ConCert.Examples.EIP20 Require EIP20Token.

(** * Contract types *)
Section dexAMM.
  Global Definition AddrSize : N := (2^8)%N.
  Definition ContractAddrBase : N := AddrSize / 2.
  Global Instance LocalChainBase : ChainBase :=
    {| Address := BoundedN AddrSize;
      address_eqb := BoundedN.eqb;
      address_eqb_spec := BoundedN.eqb_spec;
      address_is_contract a := (ContractAddrBase <=? BoundedN.to_N a)%N
    |}.
  Set Nonrecursive Elimination Schemes.

  Definition addr_of_Z (x : Z) := BoundedN.of_Z_const AddrSize x.
  Definition addr_of_N (x : N) := BoundedN.of_Z_const AddrSize (Z.of_N x).

  Definition zero_address : Address := addr_of_Z 0.

  Open Scope N_scope.
  Open Scope bool.

  Record Pool :=
    build_pool {
      token0 : Address;
      token1 : Address;
      amount0 : N;
      amount1 : N;
      totalShares : N;
      isStable : bool;
      fee0 : N;
      fee1 : N;
      feeRate : N;
    }.

  Global Instance Pool_serializable : Serializable Pool :=
    Derive Serializable Pool_rect <build_pool>. 

  Record Position :=
    build_position {
      amount00 : N;
      amount11 : N;
    }.

  Global Instance Position_serializable : Serializable Position :=
    Derive Serializable Position_rect <build_position>.

  Record Fee :=
    build_fee {
      fee00 : N;
      fee11 : N;
    }.

  Global Instance Fee_serializable : Serializable Fee :=
    Derive Serializable Fee_rect <build_fee>.

  Inductive Msg :=
  | modifyAmplificationFactor : N -> Msg
  | createPair : Address -> Address -> N -> bool -> Msg
  | deposit : N -> N -> N -> Msg
  | withdrawFees : N -> Msg 
  | withdraw : N -> Msg
  | swap : N -> Address -> Msg.

  Record State :=
    build_state {
      getPool : FMap (Address * Address) (FMap N (FMap bool N));
      Pools : FMap N Pool;
      PIDs : N;
      Fees : FMap N (AddressMap.AddrMap Fee);
      PoolShares : AddressMap.AddrMap (FMap N N);
      dividendPayingERC20 : Address;
      AmplificationFactor : N;
      admin : Address
    }.

  Record Setup :=
    build_setup {
      dividendPayingERC20_ : Address
    }.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  (* begin hide *)
  MetaCoq Run (make_setters State).
  MetaCoq Run (make_setters Setup).
  (* end hide *)

  Section Serialization.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.

    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <modifyAmplificationFactor, createPair, deposit, withdrawFees, withdraw,  swap>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

  End Serialization.

  Definition error {T : Type} : result T Error :=
    Err default_error.

  (** Contract functions **)
  (** Initialize contract storage *)
  Definition init (chain : Chain)
                  (ctx : ContractCallContext)
                  (setup : Setup)
                  : result State Error :=
    Ok {| getPool := FMap.empty;
          Pools := FMap.empty;
          PIDs := 0;
          Fees := FMap.empty;
          PoolShares := AddressMap.empty;
          dividendPayingERC20 := setup.(dividendPayingERC20_);
          AmplificationFactor := 0;
          admin := ctx.(ctx_from)
      |}.

(** Function modifyAmplificationFactor from Admin contract *)
  Definition try_modifyAmplificationFactor (ctx : ContractCallContext)
                                           (_ampFactor : N)
                                           (state : State)
                                           : result State Error :=
    if (ctx.(ctx_from) =? state.(admin))%address 
    then Ok (state <| AmplificationFactor := _ampFactor |>)
    else error.

    (**
     * @notice Create Token Pair function
     * @dev PID is incremented and starts from 1 not 0
     * @param token0 address token0
     * @param token1 address token1
     * @param _fee fee amount base 1e18
     * @param _isStable uses stable formula or standard formula
     * @return PID the newly created Pool ID
     *)
  Definition try_createPair (token0 : Address)
                            (token1 : Address)
                            (_fee : N)
                            (_isStable : bool)
                            (state : State)
                            : result State Error :=
    if (address_eqb token0 zero_address) || (address_eqb token1 zero_address) then error
    else if (address_eqb token0 token1) then error
    else match FMap.find (token0, token1) state.(getPool), FMap.find (token1, token0) state.(getPool) with
    | None, None => 
        let pool := (build_pool token0 token1 0 0 0 _isStable 0 0 _fee) in 
        let new_pools := FMap.add (state.(PIDs) + 1) pool state.(Pools) in
        Ok (state<|Pools := new_pools|><|PIDs := state.(PIDs) + 1|>
                 <|getPool ::= FMap.add (token0, token1) 
                                (FMap.add _fee 
                                  (FMap.add _isStable (state.(PIDs) + 1) FMap.empty)
                                 FMap.empty)|>)
    | _, _ => error end.

     (**
     * @notice Deposit function
     * @dev deposit to specific PID
     * @param PID Pool ID
     * @param amount_token0 address token1
     * @param amount_token1 fee amount base 1e18
     **)
  Definition try_deposit (caller : Address) (AMM_caddr : Address)
                         (PID : N)
                         (amount_token0 : N)
                         (amount_token1 : N)
                         (state : State)
                         : result (State * (list ActionBody)) Error :=
    do pool <- result_of_option (FMap.find PID state.(Pools)) default_error;
    let token0 := pool.(token0) in
    let token1 := pool.(token1) in
    let tr0 := EIP20Token.transfer_from caller AMM_caddr amount_token0 in
    let transfer_msg0 := act_call token0 0%Z (@serialize EIP20Token.Msg _ (tr0)) in
    let tr1 := EIP20Token.transfer_from caller AMM_caddr amount_token1 in
    let transfer_msg1 := act_call token1 0%Z (@serialize EIP20Token.Msg _ (tr1)) in
    let totalLiquidity := N.sqrt (amount_token0 * amount_token1) in (* Square root!!! *)
    let shares_map := with_default (FMap.empty) (AddressMap.find caller state.(PoolShares)) in
    let share := with_default 0 (FMap.find PID shares_map) in
    let new_poolShares := AddressMap.add caller (FMap.add PID (share + totalLiquidity) shares_map) state.(PoolShares) in
    let upd_pool := {| token0 := token0;
        token1 := token1;
        amount0 := pool.(amount0) + amount_token0;
        amount1 := pool.(amount1) + amount_token1;
        totalShares := pool.(totalShares) + totalLiquidity;
        isStable := pool.(isStable);
        fee0 := pool.(fee0);
        fee1 := pool.(fee1);
        feeRate := pool.(feeRate); |} in 
    let upd_pools := (FMap.add PID upd_pool state.(Pools))
    in Ok(state<|PoolShares := new_poolShares|> <|Pools := upd_pools|>, 
          [transfer_msg0; transfer_msg1]).

     (**
     * @notice Withdraw Fees function
     * @dev withdraw earned fees from pool
     * @param PID Pool ID
     *)
  Definition try_withdrawFees (caller : Address)
                              (PID : N)
                              (state : State)
                              : result (State * (list ActionBody)) Error :=
    do pool <- result_of_option (FMap.find PID state.(Pools)) default_error;
    do shares_map <- result_of_option (AddressMap.find caller state.(PoolShares)) default_error;
    do share <- result_of_option (FMap.find PID shares_map) default_error;
    if (share =? 0) then error
    else do fees_map <- result_of_option (FMap.find PID state.(Fees)) default_error;
    do userFees <- result_of_option (FMap.find caller fees_map) default_error;
    let feeToWithdraw0 := pool.(fee0) * share / pool.(totalShares) - userFees.(fee00) in
    let feeToWithdraw1 := pool.(fee1) * share / pool.(totalShares) - userFees.(fee11) in
    if (0 <? feeToWithdraw0) || (0 <? feeToWithdraw1)
    then let upd_fee := {| fee00 := userFees.(fee00) + feeToWithdraw0;
                           fee11 := userFees.(fee11) + feeToWithdraw1|} in
    let upd_fees := FMap.add PID (AddressMap.add caller upd_fee fees_map) state.(Fees) in
    let upd_pool := {| token0 := pool.(token0);
        token1 := pool.(token1);
        amount0 := pool.(amount0) - feeToWithdraw0;
        amount1 := pool.(amount1) - feeToWithdraw1;
        totalShares := pool.(totalShares);
        isStable := pool.(isStable);
        fee0 := pool.(fee0);
        fee1 := pool.(fee1);
        feeRate := pool.(feeRate); |} in 
    let upd_pools := (FMap.add PID upd_pool state.(Pools)) in
    let tr0 := EIP20Token.transfer caller feeToWithdraw0 in
    let transfer_msg0 := act_call pool.(token0) 0%Z (@serialize EIP20Token.Msg _ (tr0)) in
    let tr1 := EIP20Token.transfer caller feeToWithdraw1 in
    let transfer_msg1 := act_call pool.(token1) 0%Z (@serialize EIP20Token.Msg _ (tr1)) in
      Ok (state<|Pools := upd_pools|><|Fees := upd_fees|>, [transfer_msg0; transfer_msg1]) 
    else let upd_pool := {| token0 := pool.(token0);
        token1 := pool.(token1);
        amount0 := pool.(amount0) - feeToWithdraw0;
        amount1 := pool.(amount1) - feeToWithdraw1;
        totalShares := pool.(totalShares);
        isStable := pool.(isStable);
        fee0 := pool.(fee0);
        fee1 := pool.(fee1);
        feeRate := pool.(feeRate); |} in 
    let upd_pools := (FMap.add PID upd_pool state.(Pools)) in
    let tr0 := EIP20Token.transfer caller feeToWithdraw0 in
    let transfer_msg0 := act_call pool.(token0) 0%Z (@serialize EIP20Token.Msg _ (tr0)) in
    let tr1 := EIP20Token.transfer caller feeToWithdraw1 in
    let transfer_msg1 := act_call pool.(token1) 0%Z (@serialize EIP20Token.Msg _ (tr1)) in
      Ok (state<|Pools := upd_pools|>, [transfer_msg0; transfer_msg1]).

     (**
     * @notice Withdraw function
     * @dev withdraw tokens from pool and destroy liquidity position
     * @param PID Pool ID
     * @return amount_token0 address token1
     * @return amount_token1 fee amount base 1e18
     *)
  Definition try_withdraw (caller : Address)
                          (PID : N)
                          (state : State)
                          : result (State * (list ActionBody)) Error := 
    do shares_map <- result_of_option (AddressMap.find caller state.(PoolShares)) default_error;
    do share <- result_of_option (FMap.find PID shares_map) default_error;
    if (share =? 0) then error
    else do withdraw_fees <- try_withdrawFees caller PID state;
    let state := fst withdraw_fees in
    let acts := snd withdraw_fees in
    do pool <- result_of_option (FMap.find PID state.(Pools)) default_error;
    let amount_token0 := share * pool.(amount0) / pool.(totalShares) in
    let amount_token1 := share * pool.(amount1) / pool.(totalShares) in
    if (pool.(amount0) <? amount_token0) || (pool.(amount1) <? amount_token1) 
    then error
    else let upd_pool := {| token0 := pool.(token0);
        token1 := pool.(token1);
        amount0 := pool.(amount0) - amount_token0;
        amount1 := pool.(amount1) - amount_token1;
        totalShares := pool.(totalShares) - share;
        isStable := pool.(isStable);
        fee0 := pool.(fee0);
        fee1 := pool.(fee1);
        feeRate := pool.(feeRate); |} in
    let upd_pools := (FMap.add PID upd_pool state.(Pools)) in
    let protocol_fee_token0 := amount_token0 / 100 in
    let protocol_fee_token1 := amount_token1 / 100 in
    let amount_token0 := amount_token0 - protocol_fee_token0 in
    let amount_token1 := amount_token1 - protocol_fee_token1 in
    let upd_poolShares := AddressMap.add caller (FMap.add PID 0 shares_map) state.(PoolShares) in
    let tr1 := EIP20Token.transfer caller amount_token0 in
    let transfer_msg1 := act_call pool.(token0) 0%Z (@serialize EIP20Token.Msg _ (tr1)) in
    let tr2 := EIP20Token.transfer caller amount_token1 in
    let transfer_msg2 := act_call pool.(token1) 0%Z (@serialize EIP20Token.Msg _ (tr2)) in
    let tr3 := EIP20Token.transfer state.(dividendPayingERC20) protocol_fee_token0 in
    let transfer_msg3 := act_call pool.(token0) 0%Z (@serialize EIP20Token.Msg _ (tr3)) in
    let tr4 := EIP20Token.transfer state.(dividendPayingERC20) protocol_fee_token1 in
    let transfer_msg4 := act_call pool.(token1) 0%Z (@serialize EIP20Token.Msg _ (tr4)) in
    Ok (state<|Pools := upd_pools|><|PoolShares := upd_poolShares|>,
        acts ++ [transfer_msg1; transfer_msg2; transfer_msg3; transfer_msg4]).

(** @dev separate function to handle fees **)
  Definition handleFees (PID : N)
                        (tokenIn : Address)
                        (fee : N)
                        (state : State)
                        : result State Error :=
    do pool <- result_of_option (FMap.find PID state.(Pools)) default_error;
    if (address_eqb pool.(token0) tokenIn)
    then let upd_pool := {| token0 := pool.(token0);
        token1 := pool.(token1);
        amount0 := pool.(amount0) + fee;
        amount1 := pool.(amount1);
        totalShares := pool.(totalShares);
        isStable := pool.(isStable);
        fee0 := pool.(fee0) + fee;
        fee1 := pool.(fee1);
        feeRate := pool.(feeRate); |} in
    let upd_pools := (FMap.add PID upd_pool state.(Pools)) in
    Ok (state<|Pools := upd_pools|>) 
    else let upd_pool := {| token0 := pool.(token0);
        token1 := pool.(token1);
        amount0 := pool.(amount0);
        amount1 := pool.(amount1) + fee;
        totalShares := pool.(totalShares);
        isStable := pool.(isStable);
        fee0 := pool.(fee0);
        fee1 := pool.(fee1) + fee;
        feeRate := pool.(feeRate); |} in
    let upd_pools := (FMap.add PID upd_pool state.(Pools)) in
    Ok (state<|Pools := upd_pools|>).

  Open Scope Q_scope.

  Definition solve_quad (b : Q) (c : Q) := 
  (PTUtils.Q_sqrt (b*b - 4*c) - b) / 2.

     (**
     * @notice stableswap equation
     * @param Ax asset of token x
     * @param Ay asset of token y
     * @param Dx delta x, i.e. token x amount inputted
     * @return quote The quote for amount of token y swapped for token x amount inputted
     **)
  Definition _swapQuoteFunc (Ax : N) (Ay : N) (Dx : N) (A: Q) :=
    let Ax := inject_Z (Z.of_N Ax) in
    let Ay := inject_Z (Z.of_N Ay) in
    let Dx := inject_Z (Z.of_N Dx) in
    let D := Qred (Ax + Ay - A * (Ax + Ay)) in
    let rx := Qred ((Ax + Dx) / Ax) in
    let b := Qred ((Ax * (rx - A / rx)) / Ay - D / Ay) in
    let ry := Qred (solve_quad b A) in
    let Dy := Qred (Ay * ry - Ay) in
    Z.abs (PTUtils.Qfloor Dy).

  Close Scope Q_scope.

  (* @dev prevents stack too deep errors *)
  Definition calculateAmounts (AMM_caddr : Address) (PID : N)
                              (tokenIn : Address)
                              (amountMinusFee : N)
                              (state : State)
                              : result (State * N) Error :=
    do pool <- result_of_option (FMap.find PID state.(Pools)) default_error;
    if (pool.(isStable)) then
    if (address_eqb pool.(token0) tokenIn) then
    let amountOut := Z.to_N (_swapQuoteFunc pool.(amount0) pool.(amount1) amountMinusFee (Z.of_N (state.(AmplificationFactor))#100)) in
    let upd_pool := {| token0 := pool.(token0);
        token1 := pool.(token1);
        amount0 := pool.(amount0) + amountMinusFee;
        amount1 := pool.(amount1) - amountOut;
        totalShares := pool.(totalShares);
        isStable := pool.(isStable);
        fee0 := pool.(fee0);
        fee1 := pool.(fee1);
        feeRate := pool.(feeRate); |} in
    let upd_pools := (FMap.add PID upd_pool state.(Pools)) in
    Ok (state<|Pools := upd_pools|>, amountOut)
    else let amountOut := Z.to_N ( _swapQuoteFunc pool.(amount1) pool.(amount0) amountMinusFee (Z.of_N (state.(AmplificationFactor))#100)) in
    let upd_pool := {| token0 := pool.(token0);
        token1 := pool.(token1);
        amount0 := pool.(amount0) - amountOut;
        amount1 := pool.(amount1) + amountMinusFee;
        totalShares := pool.(totalShares);
        isStable := pool.(isStable);
        fee0 := pool.(fee0);
        fee1 := pool.(fee1);
        feeRate := pool.(feeRate); |} in
    let upd_pools := (FMap.add PID upd_pool state.(Pools)) in
    Ok (state<|Pools := upd_pools|>, amountOut)
    else if (address_eqb pool.(token0) tokenIn) then
    let amountOut := amountMinusFee * pool.(amount1) / (amountMinusFee + pool.(amount0)) in
    let upd_pool := {| token0 := pool.(token0);
        token1 := pool.(token1);
        amount0 := pool.(amount0) + amountMinusFee;
        amount1 := pool.(amount1) - amountOut;
        totalShares := pool.(totalShares);
        isStable := pool.(isStable);
        fee0 := pool.(fee0);
        fee1 := pool.(fee1);
        feeRate := pool.(feeRate); |} in
    let upd_pools := (FMap.add PID upd_pool state.(Pools)) in
    Ok (state<|Pools := upd_pools|>, amountOut)
    else let amountOut := amountMinusFee * pool.(amount0) / (amountMinusFee + pool.(amount1)) in
    let upd_pool := {| token0 := pool.(token0);
        token1 := pool.(token1);
        amount0 := pool.(amount0) - amountOut;
        amount1 := pool.(amount1) + amountMinusFee ;
        totalShares := pool.(totalShares);
        isStable := pool.(isStable);
        fee0 := pool.(fee0);
        fee1 := pool.(fee1);
        feeRate := pool.(feeRate); |} in
    let upd_pools := (FMap.add PID upd_pool state.(Pools)) in
    Ok (state<|Pools := upd_pools|>, amountOut).

  Definition try_swap (caller : Address) (AMM_caddr : Address)
                      (PID : N)
                      (tokenIn : Address)
                      (amount : N)
                      (state : State)
                      : result (State * (list ActionBody)) Error :=
    do pool <- result_of_option (FMap.find PID state.(Pools)) default_error;
    let tr0 := EIP20Token.transfer_from caller AMM_caddr amount in
    let transfer_msg0 := act_call tokenIn 0%Z (@serialize EIP20Token.Msg _ (tr0)) in
    let fee := pool.(feeRate) * amount in
    let amountMinusFee := amount - fee in
    if N.leb fee amount then (* Here was the bug *)
    if (address_eqb pool.(token0) tokenIn) then
    let tokenOut := pool.(token1) in
    do z <- calculateAmounts AMM_caddr PID tokenIn amountMinusFee state;
    do s <- handleFees PID tokenIn fee (fst z);
    let tr1 := EIP20Token.transfer caller (snd z) in
    let transfer_msg1 := act_call tokenOut 0%Z (@serialize EIP20Token.Msg _ (tr1)) in
    Ok (s, [transfer_msg0; transfer_msg1])
    else if (address_eqb pool.(token1) tokenIn) then
    let tokenOut := pool.(token0) in 
    do z <- calculateAmounts AMM_caddr PID tokenIn amountMinusFee state;
    do s <- handleFees PID tokenIn fee (fst z);
    let tr1 := EIP20Token.transfer caller (snd z) in
    let transfer_msg1 := act_call tokenOut 0%Z (@serialize EIP20Token.Msg _ (tr1)) in
    Ok (s, [transfer_msg0; transfer_msg1]) else error else error.

  Open Scope Z_scope.
  
  (** ** receive *)
  (** Contract entrypoint function *)
  Definition receive (chain : Chain)
                     (ctx : ContractCallContext)
                     (state : State)
                     (maybe_msg : option Msg)
                     : result (State * list ActionBody) Error :=
    let sender := ctx.(ctx_from) in
    let caddr := ctx.(ctx_contract_address) in
    match maybe_msg with
    | Some (modifyAmplificationFactor _ampFactor) =>
            without_actions (try_modifyAmplificationFactor ctx _ampFactor state)
    | Some (createPair token0 token1 _fee _isStable) =>
          without_actions (try_createPair token0 token1 _fee _isStable state)
    | Some (deposit PID amount_token0 amount_token1) =>
          try_deposit sender caddr PID amount_token0 amount_token1 state
    | Some (withdrawFees PID) =>
          try_withdrawFees sender PID state
    | Some (withdraw PID) =>
          try_withdraw sender PID state
    | Some (swap PID tokenIn) =>
          try_swap sender caddr PID tokenIn (Z.to_N ctx.(ctx_amount)) state
    | None => error
    end.
  Close Scope Z_scope.

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End dexAMM.
