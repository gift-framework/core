(** GIFT - E8 Lie algebra formalization *)

Require Import Coq.Arith.Arith.

(** Dimension of E8 *)
Definition dim_E8 : nat := 248.

(** Rank of E8 *)
Definition rank_E8 : nat := 8.

(** Dimension of E8 x E8 *)
Definition dim_E8xE8 : nat := 2 * dim_E8.

Theorem E8xE8_dim_certified : dim_E8xE8 = 496.
Proof. reflexivity. Qed.
