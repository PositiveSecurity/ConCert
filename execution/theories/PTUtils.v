From Coq Require Import ZArith_base.
From Coq Require Import Strings.String.
From Coq Require Import List. Import ListNotations.
From Coq Require Import QArith.QArith.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Extras.

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import Containers.

Module PTUtils.

(** * BOOL *)
Open Scope bool_scope.

Theorem or_false_implies_and_false : forall A B : bool,
  A || B = false -> A = false /\ B = false.
Proof.
  intros A B H.
  split.
  - destruct A.
    + simpl in H. discriminate H.
    + reflexivity.
  - destruct B.
    + destruct A; simpl in H; discriminate H.
    + reflexivity.
Qed.

(** * OPTIONS *)
Lemma isSome_true : forall (A : Type) (t : A),
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
Qed.

(** * N Type *)
Open Scope N_scope.

Theorem lt_to_le : forall amount : N,
  (0 <? amount) = false -> (amount <=? 0) = true.
Proof.
  intros amount H.
  apply N.ltb_nlt in H.
  apply N.leb_le.
  unfold not in H.
  apply N.nlt_ge in H.
  exact H.
Qed.

Lemma add_assoc1: forall a b c : N,
  c <= b -> a + b = a + (b - c) + c.
Proof.
  intros a b c H.
  rewrite <- N.add_assoc.
  rewrite N.sub_add.
  reflexivity.
  assumption.
Qed.


(** * LISTS *)

(* General function for checking lists eqiuivalence *)
Fixpoint lists_equal {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: l1', x2 :: l2' => if eqb x1 x2 then lists_equal eqb l1' l2' else false
  | _, _ => false
  end.

(** * ADDRESSES *)

(* Find and remove addresses equal to given from list*)
Fixpoint remove_eqbAddresses `{ChainBase} (x : Address) (lst : list Address) 
                              : list Address :=
  match lst with
  | [] => []
  | y :: ys => if address_eqb x y then remove_eqbAddresses x ys else y :: remove_eqbAddresses x ys
  end.

Lemma address_eq `{ChainBase} x y :
  address_eqb x y = true <->
  x = y.
Proof.
  now destruct (address_eqb_spec x y).
Qed.

(** BALANCES *)
(** Helpers for balance incrementing **)
Definition increment_balance `{ChainBase} 
                              (m : AddressMap.AddrMap N)
                              (addr : Address)
                              (inc : N)
                              : AddressMap.AddrMap N :=
  match AddressMap.find addr m with
  | Some old => AddressMap.add addr (old + inc) m
  | None => AddressMap.add addr inc m
  end.

Definition increment_cur_balance `{ChainBase}
                                  (m : FMap string (AddressMap.AddrMap N))
                                  (currency : string)
                                  (addr : Address)
                                  (inc : N)
                                  : FMap string (AddressMap.AddrMap N) :=
  match FMap.find currency m with
  | Some old => FMap.add currency (increment_balance old addr inc) m
  | None => FMap.add currency (increment_balance AddressMap.empty addr inc) m
  end.

(* Try this lemma in your context. It guarantees increment_balance safety *)
(*  Lemma increment_balanace_is_partial_alter_plus : forall (addr : Address) amount (m : FMap Address N),
    increment_balance m addr amount =
    FMap.partial_alter (fun balance : option N => Some (with_default 0 balance + amount)) addr m.
  Proof.
    intros.
    unfold increment_balance, AddressMap.add, AddressMap.find.
    rewrite add_is_partial_alter_plus by auto.
    destruct_match eqn:addr_in_map;
      now setoid_rewrite addr_in_map.
  Qed. *)

(** * RATIONAL NUMBERS *)
  Open Scope Q_scope.

(* Square root *)
  Fixpoint sqrt_iter (q : Q) (guess : Q) (steps : nat) : Q :=
    match steps with
    | O => guess
    | S steps' => sqrt_iter q ((guess + q / guess) / (2#1)) steps'
    end.

  Definition Q_sqrt (q : Q) : Q :=
    sqrt_iter q q 4.

  Definition Qfloor (x:Q) := let (n,d) := x in Z.div n (Zpos d).

Close Scope Q_scope.
End PTUtils.