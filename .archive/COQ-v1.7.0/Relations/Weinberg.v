(** GIFT - Weinberg angle and related relations *)

Require Import Coq.Arith.Arith.
Require Import GIFT.Algebra.G2.
Require Import GIFT.Topology.Betti.

(** Weinberg angle: sin^2(theta_W) = b2/(b3 + dim_G2) = 21/91 = 3/13 *)
Theorem weinberg_angle_certified : b2 * 13 = 3 * (b3 + dim_G2).
Proof. reflexivity. Qed.

(** Koide parameter: Q = dim_G2/b2 = 14/21 = 2/3 *)
Theorem koide_certified : dim_G2 * 3 = b2 * 2.
Proof. reflexivity. Qed.
