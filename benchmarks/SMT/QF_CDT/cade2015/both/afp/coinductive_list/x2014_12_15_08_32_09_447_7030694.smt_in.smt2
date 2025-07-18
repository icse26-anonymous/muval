; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 186
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort Nat$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort A_a_bool_fun_fun$ 0)
(declare-sort A_b_bool_fun_fun$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort B_a_bool_fun_fun$ 0)
(declare-sort B_b_bool_fun_fun$ 0)
(declare-sort B_llist_bool_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-sort B_llist_b_llist_fun$ 0)
(declare-sort A_a_llist_bool_fun_fun$ 0)
(declare-sort A_b_llist_bool_fun_fun$ 0)
(declare-sort A_llist_a_bool_fun_fun$ 0)
(declare-sort A_llist_b_bool_fun_fun$ 0)
(declare-sort A_llist_llist_bool_fun$ 0)
(declare-sort B_a_llist_bool_fun_fun$ 0)
(declare-sort B_b_llist_bool_fun_fun$ 0)
(declare-sort B_llist_a_bool_fun_fun$ 0)
(declare-sort B_llist_b_bool_fun_fun$ 0)
(declare-sort B_llist_llist_bool_fun$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun$ 0)
(declare-sort A_llist_b_llist_bool_fun_fun$ 0)
(declare-sort B_llist_a_llist_bool_fun_fun$ 0)
(declare-sort B_llist_b_llist_bool_fun_fun$ 0)
(declare-sort A_llist_llist_a_llist_llist_fun$ 0)
(declare-sort B_llist_llist_b_llist_llist_fun$ 0)
(declare-sort A_llist_llist_a_llist_bool_fun_fun$ 0)
(declare-sort A_llist_llist_b_llist_bool_fun_fun$ 0)
(declare-sort B_llist_llist_a_llist_bool_fun_fun$ 0)
(declare-sort B_llist_llist_b_llist_bool_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))
  (B_llist$ (lNil$a) (lCons$a (lhd$a B$) (ltl$a B_llist$)))
  (A_llist_llist$ (lNil$b) (lCons$b (lhd$b A_llist$) (ltl$b A_llist_llist$)))
  (B_llist_llist$ (lNil$c) (lCons$c (lhd$c B_llist$) (ltl$c B_llist_llist$)))))
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-fun a$ () A_b_bool_fun_fun$)
(declare-fun uu$ () B_b_bool_fun_fun$)
(declare-fun uua$ () B_llist_b_llist_bool_fun_fun$)
(declare-fun uub$ () A_a_bool_fun_fun$)
(declare-fun uuc$ () A_llist_a_llist_bool_fun_fun$)
(declare-fun xss$ () A_llist_llist$)
(declare-fun yss$ () B_llist_llist$)
(declare-fun ldrop$ (Enat$) A_llist_a_llist_fun$)
(declare-fun ldrop$a (Enat$) B_llist_b_llist_fun$)
(declare-fun ldrop$b (Enat$) A_llist_llist_a_llist_llist_fun$)
(declare-fun ldrop$c (Enat$) B_llist_llist_b_llist_llist_fun$)
(declare-fun ldropn$ (Nat$) A_llist_a_llist_fun$)
(declare-fun fun_app$ (B_llist_bool_fun$ B_llist$) Bool)
(declare-fun lconcat$ (A_llist_llist$) A_llist$)
(declare-fun ldropn$a (Nat$) B_llist_b_llist_fun$)
(declare-fun ldropn$b (Nat$) A_llist_llist_a_llist_llist_fun$)
(declare-fun ldropn$c (Nat$) B_llist_llist_b_llist_llist_fun$)
(declare-fun fun_app$a (B_llist_b_llist_bool_fun_fun$ B_llist$) B_llist_bool_fun$)
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun fun_app$c (A_llist_a_llist_bool_fun_fun$ A_llist$) A_llist_bool_fun$)
(declare-fun fun_app$d (B_bool_fun$ B$) Bool)
(declare-fun fun_app$e (B_b_bool_fun_fun$ B$) B_bool_fun$)
(declare-fun fun_app$f (A_bool_fun$ A$) Bool)
(declare-fun fun_app$g (A_a_bool_fun_fun$ A$) A_bool_fun$)
(declare-fun fun_app$h (A_llist_b_llist_bool_fun_fun$ A_llist$) B_llist_bool_fun$)
(declare-fun fun_app$i (B_llist_llist_bool_fun$ B_llist_llist$) Bool)
(declare-fun fun_app$j (A_b_bool_fun_fun$ A$) B_bool_fun$)
(declare-fun fun_app$k (B_llist_a_llist_bool_fun_fun$ B_llist$) A_llist_bool_fun$)
(declare-fun fun_app$l (A_llist_llist_bool_fun$ A_llist_llist$) Bool)
(declare-fun fun_app$m (B_llist_llist_b_llist_bool_fun_fun$ B_llist_llist$) B_llist_bool_fun$)
(declare-fun fun_app$n (B_llist_llist_a_llist_bool_fun_fun$ B_llist_llist$) A_llist_bool_fun$)
(declare-fun fun_app$o (A_llist_llist_b_llist_bool_fun_fun$ A_llist_llist$) B_llist_bool_fun$)
(declare-fun fun_app$p (A_llist_llist_a_llist_bool_fun_fun$ A_llist_llist$) A_llist_bool_fun$)
(declare-fun fun_app$q (B_a_bool_fun_fun$ B$) A_bool_fun$)
(declare-fun fun_app$r (A_llist_a_bool_fun_fun$ A_llist$) A_bool_fun$)
(declare-fun fun_app$s (A_llist_b_bool_fun_fun$ A_llist$) B_bool_fun$)
(declare-fun fun_app$t (B_llist_a_bool_fun_fun$ B_llist$) A_bool_fun$)
(declare-fun fun_app$u (B_llist_b_bool_fun_fun$ B_llist$) B_bool_fun$)
(declare-fun fun_app$v (A_a_llist_bool_fun_fun$ A$) A_llist_bool_fun$)
(declare-fun fun_app$w (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun fun_app$x (B_llist_b_llist_fun$ B_llist$) B_llist$)
(declare-fun fun_app$y (A_llist_llist_a_llist_llist_fun$ A_llist_llist$) A_llist_llist$)
(declare-fun fun_app$z (B_llist_llist_b_llist_llist_fun$ B_llist_llist$) B_llist_llist$)
(declare-fun lconcat$a (B_llist_llist$) B_llist$)
(declare-fun fun_app$aa (B_a_llist_bool_fun_fun$ B$) A_llist_bool_fun$)
(declare-fun fun_app$ab (A_b_llist_bool_fun_fun$ A$) B_llist_bool_fun$)
(declare-fun fun_app$ac (B_b_llist_bool_fun_fun$ B$) B_llist_bool_fun$)
(declare-fun ldropWhile$ (A_bool_fun$ A_llist$) A_llist$)
(declare-fun llist_all2$ (A_b_bool_fun_fun$) A_llist_b_llist_bool_fun_fun$)
(declare-fun ldropWhile$a (B_bool_fun$ B_llist$) B_llist$)
(declare-fun ldropWhile$b (A_llist_bool_fun$ A_llist_llist$) A_llist_llist$)
(declare-fun ldropWhile$c (B_llist_bool_fun$ B_llist_llist$) B_llist_llist$)
(declare-fun llist_all2$a (A_llist_b_llist_bool_fun_fun$ A_llist_llist$) B_llist_llist_bool_fun$)
(declare-fun llist_all2$b (B_b_bool_fun_fun$) B_llist_b_llist_bool_fun_fun$)
(declare-fun llist_all2$c (A_a_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun llist_all2$d (B_a_bool_fun_fun$) B_llist_a_llist_bool_fun_fun$)
(declare-fun llist_all2$e (B_b_llist_bool_fun_fun$ B_llist$) B_llist_llist_bool_fun$)
(declare-fun llist_all2$f (A_b_llist_bool_fun_fun$ A_llist$) B_llist_llist_bool_fun$)
(declare-fun llist_all2$g (B_a_llist_bool_fun_fun$ B_llist$) A_llist_llist_bool_fun$)
(declare-fun llist_all2$h (A_a_llist_bool_fun_fun$ A_llist$) A_llist_llist_bool_fun$)
(declare-fun llist_all2$i (B_llist_b_bool_fun_fun$) B_llist_llist_b_llist_bool_fun_fun$)
(declare-fun llist_all2$j (B_llist_a_bool_fun_fun$) B_llist_llist_a_llist_bool_fun_fun$)
(declare-fun llist_all2$k (A_llist_b_bool_fun_fun$) A_llist_llist_b_llist_bool_fun_fun$)
(declare-fun llist_all2$l (A_llist_a_bool_fun_fun$) A_llist_llist_a_llist_bool_fun_fun$)
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a uua$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$ (fun_app$a uua$ ?v0) ?v1)))) :named a0))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$c uuc$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$b (fun_app$c uuc$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 B$) (?v1 B$)) (! (= (fun_app$d (fun_app$e uu$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$d (fun_app$e uu$ ?v0) ?v1)))) :named a2))
(assert (! (forall ((?v0 A$) (?v1 A$)) (! (= (fun_app$f (fun_app$g uub$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$f (fun_app$g uub$ ?v0) ?v1)))) :named a3))
(assert (! (not (fun_app$ (fun_app$h (llist_all2$ a$) (lconcat$ xss$)) (lconcat$a yss$))) :named a4))
(assert (! (fun_app$i (llist_all2$a (llist_all2$ a$) xss$) yss$) :named a5))
(assert (! (= (llist_all2$b uu$) uua$) :named a6))
(assert (! (= (llist_all2$c uub$) uuc$) :named a7))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_a_bool_fun_fun$)) (=> (and (fun_app$b (fun_app$c (llist_all2$c ?v0) ?v1) ?v2) (forall ((?v4 A$) (?v5 A$)) (=> (fun_app$f (fun_app$g ?v0 ?v4) ?v5) (fun_app$f (fun_app$g ?v3 ?v4) ?v5)))) (fun_app$b (fun_app$c (llist_all2$c ?v3) ?v1) ?v2))) :named a8))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 A_b_bool_fun_fun$)) (=> (and (fun_app$ (fun_app$h (llist_all2$ ?v0) ?v1) ?v2) (forall ((?v4 A$) (?v5 B$)) (=> (fun_app$d (fun_app$j ?v0 ?v4) ?v5) (fun_app$d (fun_app$j ?v3 ?v4) ?v5)))) (fun_app$ (fun_app$h (llist_all2$ ?v3) ?v1) ?v2))) :named a9))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 B_llist_llist$) (?v3 A_llist_b_llist_bool_fun_fun$)) (=> (and (fun_app$i (llist_all2$a ?v0 ?v1) ?v2) (forall ((?v4 A_llist$) (?v5 B_llist$)) (=> (fun_app$ (fun_app$h ?v0 ?v4) ?v5) (fun_app$ (fun_app$h ?v3 ?v4) ?v5)))) (fun_app$i (llist_all2$a ?v3 ?v1) ?v2))) :named a10))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$ (fun_app$h (llist_all2$ ?v0) ?v1) lNil$a) (= ?v1 lNil$)) :pattern ((fun_app$h (llist_all2$ ?v0) ?v1)))) :named a11))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist_llist$)) (! (= (fun_app$i (llist_all2$a ?v0 ?v1) lNil$c) (= ?v1 lNil$b)) :pattern ((llist_all2$a ?v0 ?v1)))) :named a12))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v1) lNil$a) (= ?v1 lNil$a)) :pattern ((fun_app$a (llist_all2$b ?v0) ?v1)))) :named a13))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$b (fun_app$k (llist_all2$d ?v0) ?v1) lNil$) (= ?v1 lNil$a)) :pattern ((fun_app$k (llist_all2$d ?v0) ?v1)))) :named a14))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$c (llist_all2$c ?v0) ?v1) lNil$) (= ?v1 lNil$)) :pattern ((fun_app$c (llist_all2$c ?v0) ?v1)))) :named a15))
(assert (! (forall ((?v0 B_b_llist_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$i (llist_all2$e ?v0 ?v1) lNil$c) (= ?v1 lNil$a)) :pattern ((llist_all2$e ?v0 ?v1)))) :named a16))
(assert (! (forall ((?v0 A_b_llist_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$i (llist_all2$f ?v0 ?v1) lNil$c) (= ?v1 lNil$)) :pattern ((llist_all2$f ?v0 ?v1)))) :named a17))
(assert (! (forall ((?v0 B_a_llist_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$l (llist_all2$g ?v0 ?v1) lNil$b) (= ?v1 lNil$a)) :pattern ((llist_all2$g ?v0 ?v1)))) :named a18))
(assert (! (forall ((?v0 A_a_llist_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$l (llist_all2$h ?v0 ?v1) lNil$b) (= ?v1 lNil$)) :pattern ((llist_all2$h ?v0 ?v1)))) :named a19))
(assert (! (forall ((?v0 B_llist_b_bool_fun_fun$) (?v1 B_llist_llist$)) (! (= (fun_app$ (fun_app$m (llist_all2$i ?v0) ?v1) lNil$a) (= ?v1 lNil$c)) :pattern ((fun_app$m (llist_all2$i ?v0) ?v1)))) :named a20))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$h (llist_all2$ ?v0) lNil$) ?v1) (= ?v1 lNil$a)) :pattern ((fun_app$ (fun_app$h (llist_all2$ ?v0) lNil$) ?v1)))) :named a21))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 B_llist_llist$)) (! (= (fun_app$i (llist_all2$a ?v0 lNil$b) ?v1) (= ?v1 lNil$c)) :pattern ((fun_app$i (llist_all2$a ?v0 lNil$b) ?v1)))) :named a22))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a (llist_all2$b ?v0) lNil$a) ?v1) (= ?v1 lNil$a)) :pattern ((fun_app$ (fun_app$a (llist_all2$b ?v0) lNil$a) ?v1)))) :named a23))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$k (llist_all2$d ?v0) lNil$a) ?v1) (= ?v1 lNil$)) :pattern ((fun_app$b (fun_app$k (llist_all2$d ?v0) lNil$a) ?v1)))) :named a24))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$c (llist_all2$c ?v0) lNil$) ?v1) (= ?v1 lNil$)) :pattern ((fun_app$b (fun_app$c (llist_all2$c ?v0) lNil$) ?v1)))) :named a25))
(assert (! (forall ((?v0 B_llist_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$m (llist_all2$i ?v0) lNil$c) ?v1) (= ?v1 lNil$a)) :pattern ((fun_app$ (fun_app$m (llist_all2$i ?v0) lNil$c) ?v1)))) :named a26))
(assert (! (forall ((?v0 B_llist_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$n (llist_all2$j ?v0) lNil$c) ?v1) (= ?v1 lNil$)) :pattern ((fun_app$b (fun_app$n (llist_all2$j ?v0) lNil$c) ?v1)))) :named a27))
(assert (! (forall ((?v0 A_llist_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$o (llist_all2$k ?v0) lNil$b) ?v1) (= ?v1 lNil$a)) :pattern ((fun_app$ (fun_app$o (llist_all2$k ?v0) lNil$b) ?v1)))) :named a28))
(assert (! (forall ((?v0 A_llist_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$p (llist_all2$l ?v0) lNil$b) ?v1) (= ?v1 lNil$)) :pattern ((fun_app$b (fun_app$p (llist_all2$l ?v0) lNil$b) ?v1)))) :named a29))
(assert (! (forall ((?v0 B_b_llist_bool_fun_fun$) (?v1 B_llist_llist$)) (! (= (fun_app$i (llist_all2$e ?v0 lNil$a) ?v1) (= ?v1 lNil$c)) :pattern ((fun_app$i (llist_all2$e ?v0 lNil$a) ?v1)))) :named a30))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 B$) (?v4 B_llist$)) (! (= (fun_app$ (fun_app$h (llist_all2$ ?v0) (lCons$ ?v1 ?v2)) (lCons$a ?v3 ?v4)) (and (fun_app$d (fun_app$j ?v0 ?v1) ?v3) (fun_app$ (fun_app$h (llist_all2$ ?v0) ?v2) ?v4))) :pattern ((fun_app$ (fun_app$h (llist_all2$ ?v0) (lCons$ ?v1 ?v2)) (lCons$a ?v3 ?v4))))) :named a31))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist_llist$) (?v3 B_llist$) (?v4 B_llist_llist$)) (! (= (fun_app$i (llist_all2$a ?v0 (lCons$b ?v1 ?v2)) (lCons$c ?v3 ?v4)) (and (fun_app$ (fun_app$h ?v0 ?v1) ?v3) (fun_app$i (llist_all2$a ?v0 ?v2) ?v4))) :pattern ((fun_app$i (llist_all2$a ?v0 (lCons$b ?v1 ?v2)) (lCons$c ?v3 ?v4))))) :named a32))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$b (fun_app$c (llist_all2$c ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v3 ?v4)) (and (fun_app$f (fun_app$g ?v0 ?v1) ?v3) (fun_app$b (fun_app$c (llist_all2$c ?v0) ?v2) ?v4))) :pattern ((fun_app$b (fun_app$c (llist_all2$c ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a33))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B$) (?v2 B_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$b (fun_app$k (llist_all2$d ?v0) (lCons$a ?v1 ?v2)) (lCons$ ?v3 ?v4)) (and (fun_app$f (fun_app$q ?v0 ?v1) ?v3) (fun_app$b (fun_app$k (llist_all2$d ?v0) ?v2) ?v4))) :pattern ((fun_app$b (fun_app$k (llist_all2$d ?v0) (lCons$a ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a34))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B$) (?v2 B_llist$) (?v3 B$) (?v4 B_llist$)) (! (= (fun_app$ (fun_app$a (llist_all2$b ?v0) (lCons$a ?v1 ?v2)) (lCons$a ?v3 ?v4)) (and (fun_app$d (fun_app$e ?v0 ?v1) ?v3) (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v2) ?v4))) :pattern ((fun_app$ (fun_app$a (llist_all2$b ?v0) (lCons$a ?v1 ?v2)) (lCons$a ?v3 ?v4))))) :named a35))
(assert (! (forall ((?v0 A_llist_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$b (fun_app$p (llist_all2$l ?v0) (lCons$b ?v1 ?v2)) (lCons$ ?v3 ?v4)) (and (fun_app$f (fun_app$r ?v0 ?v1) ?v3) (fun_app$b (fun_app$p (llist_all2$l ?v0) ?v2) ?v4))) :pattern ((fun_app$b (fun_app$p (llist_all2$l ?v0) (lCons$b ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a36))
(assert (! (forall ((?v0 A_llist_b_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist_llist$) (?v3 B$) (?v4 B_llist$)) (! (= (fun_app$ (fun_app$o (llist_all2$k ?v0) (lCons$b ?v1 ?v2)) (lCons$a ?v3 ?v4)) (and (fun_app$d (fun_app$s ?v0 ?v1) ?v3) (fun_app$ (fun_app$o (llist_all2$k ?v0) ?v2) ?v4))) :pattern ((fun_app$ (fun_app$o (llist_all2$k ?v0) (lCons$b ?v1 ?v2)) (lCons$a ?v3 ?v4))))) :named a37))
(assert (! (forall ((?v0 B_llist_a_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$b (fun_app$n (llist_all2$j ?v0) (lCons$c ?v1 ?v2)) (lCons$ ?v3 ?v4)) (and (fun_app$f (fun_app$t ?v0 ?v1) ?v3) (fun_app$b (fun_app$n (llist_all2$j ?v0) ?v2) ?v4))) :pattern ((fun_app$b (fun_app$n (llist_all2$j ?v0) (lCons$c ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a38))
(assert (! (forall ((?v0 B_llist_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist_llist$) (?v3 B$) (?v4 B_llist$)) (! (= (fun_app$ (fun_app$m (llist_all2$i ?v0) (lCons$c ?v1 ?v2)) (lCons$a ?v3 ?v4)) (and (fun_app$d (fun_app$u ?v0 ?v1) ?v3) (fun_app$ (fun_app$m (llist_all2$i ?v0) ?v2) ?v4))) :pattern ((fun_app$ (fun_app$m (llist_all2$i ?v0) (lCons$c ?v1 ?v2)) (lCons$a ?v3 ?v4))))) :named a39))
(assert (! (forall ((?v0 A_a_llist_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 A_llist$) (?v4 A_llist_llist$)) (! (= (fun_app$l (llist_all2$h ?v0 (lCons$ ?v1 ?v2)) (lCons$b ?v3 ?v4)) (and (fun_app$b (fun_app$v ?v0 ?v1) ?v3) (fun_app$l (llist_all2$h ?v0 ?v2) ?v4))) :pattern ((fun_app$l (llist_all2$h ?v0 (lCons$ ?v1 ?v2)) (lCons$b ?v3 ?v4))))) :named a40))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 A_bool_fun$) (?v4 B_bool_fun$)) (=> (and (fun_app$ (fun_app$h (llist_all2$ ?v0) ?v1) ?v2) (forall ((?v5 A$) (?v6 B$)) (=> (fun_app$d (fun_app$j ?v0 ?v5) ?v6) (= (fun_app$f ?v3 ?v5) (fun_app$d ?v4 ?v6))))) (fun_app$ (fun_app$h (llist_all2$ ?v0) (ldropWhile$ ?v3 ?v1)) (ldropWhile$a ?v4 ?v2)))) :named a41))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 B_llist_llist$) (?v3 A_llist_bool_fun$) (?v4 B_llist_bool_fun$)) (=> (and (fun_app$i (llist_all2$a ?v0 ?v1) ?v2) (forall ((?v5 A_llist$) (?v6 B_llist$)) (=> (fun_app$ (fun_app$h ?v0 ?v5) ?v6) (= (fun_app$b ?v3 ?v5) (fun_app$ ?v4 ?v6))))) (fun_app$i (llist_all2$a ?v0 (ldropWhile$b ?v3 ?v1)) (ldropWhile$c ?v4 ?v2)))) :named a42))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_bool_fun$) (?v4 A_bool_fun$)) (=> (and (fun_app$b (fun_app$c (llist_all2$c ?v0) ?v1) ?v2) (forall ((?v5 A$) (?v6 A$)) (=> (fun_app$f (fun_app$g ?v0 ?v5) ?v6) (= (fun_app$f ?v3 ?v5) (fun_app$f ?v4 ?v6))))) (fun_app$b (fun_app$c (llist_all2$c ?v0) (ldropWhile$ ?v3 ?v1)) (ldropWhile$ ?v4 ?v2)))) :named a43))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A_llist$) (?v3 B_bool_fun$) (?v4 A_bool_fun$)) (=> (and (fun_app$b (fun_app$k (llist_all2$d ?v0) ?v1) ?v2) (forall ((?v5 B$) (?v6 A$)) (=> (fun_app$f (fun_app$q ?v0 ?v5) ?v6) (= (fun_app$d ?v3 ?v5) (fun_app$f ?v4 ?v6))))) (fun_app$b (fun_app$k (llist_all2$d ?v0) (ldropWhile$a ?v3 ?v1)) (ldropWhile$ ?v4 ?v2)))) :named a44))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$) (?v3 B_bool_fun$) (?v4 B_bool_fun$)) (=> (and (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v1) ?v2) (forall ((?v5 B$) (?v6 B$)) (=> (fun_app$d (fun_app$e ?v0 ?v5) ?v6) (= (fun_app$d ?v3 ?v5) (fun_app$d ?v4 ?v6))))) (fun_app$ (fun_app$a (llist_all2$b ?v0) (ldropWhile$a ?v3 ?v1)) (ldropWhile$a ?v4 ?v2)))) :named a45))
(assert (! (forall ((?v0 A_llist_a_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 A_llist_bool_fun$) (?v4 A_bool_fun$)) (=> (and (fun_app$b (fun_app$p (llist_all2$l ?v0) ?v1) ?v2) (forall ((?v5 A_llist$) (?v6 A$)) (=> (fun_app$f (fun_app$r ?v0 ?v5) ?v6) (= (fun_app$b ?v3 ?v5) (fun_app$f ?v4 ?v6))))) (fun_app$b (fun_app$p (llist_all2$l ?v0) (ldropWhile$b ?v3 ?v1)) (ldropWhile$ ?v4 ?v2)))) :named a46))
(assert (! (forall ((?v0 A_llist_b_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 B_llist$) (?v3 A_llist_bool_fun$) (?v4 B_bool_fun$)) (=> (and (fun_app$ (fun_app$o (llist_all2$k ?v0) ?v1) ?v2) (forall ((?v5 A_llist$) (?v6 B$)) (=> (fun_app$d (fun_app$s ?v0 ?v5) ?v6) (= (fun_app$b ?v3 ?v5) (fun_app$d ?v4 ?v6))))) (fun_app$ (fun_app$o (llist_all2$k ?v0) (ldropWhile$b ?v3 ?v1)) (ldropWhile$a ?v4 ?v2)))) :named a47))
(assert (! (forall ((?v0 B_llist_a_bool_fun_fun$) (?v1 B_llist_llist$) (?v2 A_llist$) (?v3 B_llist_bool_fun$) (?v4 A_bool_fun$)) (=> (and (fun_app$b (fun_app$n (llist_all2$j ?v0) ?v1) ?v2) (forall ((?v5 B_llist$) (?v6 A$)) (=> (fun_app$f (fun_app$t ?v0 ?v5) ?v6) (= (fun_app$ ?v3 ?v5) (fun_app$f ?v4 ?v6))))) (fun_app$b (fun_app$n (llist_all2$j ?v0) (ldropWhile$c ?v3 ?v1)) (ldropWhile$ ?v4 ?v2)))) :named a48))
(assert (! (forall ((?v0 B_llist_b_bool_fun_fun$) (?v1 B_llist_llist$) (?v2 B_llist$) (?v3 B_llist_bool_fun$) (?v4 B_bool_fun$)) (=> (and (fun_app$ (fun_app$m (llist_all2$i ?v0) ?v1) ?v2) (forall ((?v5 B_llist$) (?v6 B$)) (=> (fun_app$d (fun_app$u ?v0 ?v5) ?v6) (= (fun_app$ ?v3 ?v5) (fun_app$d ?v4 ?v6))))) (fun_app$ (fun_app$m (llist_all2$i ?v0) (ldropWhile$c ?v3 ?v1)) (ldropWhile$a ?v4 ?v2)))) :named a49))
(assert (! (forall ((?v0 A_a_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist_llist$) (?v3 A_bool_fun$) (?v4 A_llist_bool_fun$)) (=> (and (fun_app$l (llist_all2$h ?v0 ?v1) ?v2) (forall ((?v5 A$) (?v6 A_llist$)) (=> (fun_app$b (fun_app$v ?v0 ?v5) ?v6) (= (fun_app$f ?v3 ?v5) (fun_app$b ?v4 ?v6))))) (fun_app$l (llist_all2$h ?v0 (ldropWhile$ ?v3 ?v1)) (ldropWhile$b ?v4 ?v2)))) :named a50))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 Nat$)) (=> (fun_app$ (fun_app$h (llist_all2$ ?v0) ?v1) ?v2) (fun_app$ (fun_app$h (llist_all2$ ?v0) (fun_app$w (ldropn$ ?v3) ?v1)) (fun_app$x (ldropn$a ?v3) ?v2)))) :named a51))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 B_llist_llist$) (?v3 Nat$)) (=> (fun_app$i (llist_all2$a ?v0 ?v1) ?v2) (fun_app$i (llist_all2$a ?v0 (fun_app$y (ldropn$b ?v3) ?v1)) (fun_app$z (ldropn$c ?v3) ?v2)))) :named a52))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 Nat$)) (=> (fun_app$b (fun_app$c (llist_all2$c ?v0) ?v1) ?v2) (fun_app$b (fun_app$c (llist_all2$c ?v0) (fun_app$w (ldropn$ ?v3) ?v1)) (fun_app$w (ldropn$ ?v3) ?v2)))) :named a53))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A_llist$) (?v3 Nat$)) (=> (fun_app$b (fun_app$k (llist_all2$d ?v0) ?v1) ?v2) (fun_app$b (fun_app$k (llist_all2$d ?v0) (fun_app$x (ldropn$a ?v3) ?v1)) (fun_app$w (ldropn$ ?v3) ?v2)))) :named a54))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$) (?v3 Nat$)) (=> (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v1) ?v2) (fun_app$ (fun_app$a (llist_all2$b ?v0) (fun_app$x (ldropn$a ?v3) ?v1)) (fun_app$x (ldropn$a ?v3) ?v2)))) :named a55))
(assert (! (forall ((?v0 A_llist_a_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 Nat$)) (=> (fun_app$b (fun_app$p (llist_all2$l ?v0) ?v1) ?v2) (fun_app$b (fun_app$p (llist_all2$l ?v0) (fun_app$y (ldropn$b ?v3) ?v1)) (fun_app$w (ldropn$ ?v3) ?v2)))) :named a56))
(assert (! (forall ((?v0 A_llist_b_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 B_llist$) (?v3 Nat$)) (=> (fun_app$ (fun_app$o (llist_all2$k ?v0) ?v1) ?v2) (fun_app$ (fun_app$o (llist_all2$k ?v0) (fun_app$y (ldropn$b ?v3) ?v1)) (fun_app$x (ldropn$a ?v3) ?v2)))) :named a57))
(assert (! (forall ((?v0 B_llist_a_bool_fun_fun$) (?v1 B_llist_llist$) (?v2 A_llist$) (?v3 Nat$)) (=> (fun_app$b (fun_app$n (llist_all2$j ?v0) ?v1) ?v2) (fun_app$b (fun_app$n (llist_all2$j ?v0) (fun_app$z (ldropn$c ?v3) ?v1)) (fun_app$w (ldropn$ ?v3) ?v2)))) :named a58))
(assert (! (forall ((?v0 B_llist_b_bool_fun_fun$) (?v1 B_llist_llist$) (?v2 B_llist$) (?v3 Nat$)) (=> (fun_app$ (fun_app$m (llist_all2$i ?v0) ?v1) ?v2) (fun_app$ (fun_app$m (llist_all2$i ?v0) (fun_app$z (ldropn$c ?v3) ?v1)) (fun_app$x (ldropn$a ?v3) ?v2)))) :named a59))
(assert (! (forall ((?v0 A_a_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist_llist$) (?v3 Nat$)) (=> (fun_app$l (llist_all2$h ?v0 ?v1) ?v2) (fun_app$l (llist_all2$h ?v0 (fun_app$w (ldropn$ ?v3) ?v1)) (fun_app$y (ldropn$b ?v3) ?v2)))) :named a60))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 Enat$)) (=> (fun_app$ (fun_app$h (llist_all2$ ?v0) ?v1) ?v2) (fun_app$ (fun_app$h (llist_all2$ ?v0) (fun_app$w (ldrop$ ?v3) ?v1)) (fun_app$x (ldrop$a ?v3) ?v2)))) :named a61))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 B_llist_llist$) (?v3 Enat$)) (=> (fun_app$i (llist_all2$a ?v0 ?v1) ?v2) (fun_app$i (llist_all2$a ?v0 (fun_app$y (ldrop$b ?v3) ?v1)) (fun_app$z (ldrop$c ?v3) ?v2)))) :named a62))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 Enat$)) (=> (fun_app$b (fun_app$c (llist_all2$c ?v0) ?v1) ?v2) (fun_app$b (fun_app$c (llist_all2$c ?v0) (fun_app$w (ldrop$ ?v3) ?v1)) (fun_app$w (ldrop$ ?v3) ?v2)))) :named a63))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A_llist$) (?v3 Enat$)) (=> (fun_app$b (fun_app$k (llist_all2$d ?v0) ?v1) ?v2) (fun_app$b (fun_app$k (llist_all2$d ?v0) (fun_app$x (ldrop$a ?v3) ?v1)) (fun_app$w (ldrop$ ?v3) ?v2)))) :named a64))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$) (?v3 Enat$)) (=> (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v1) ?v2) (fun_app$ (fun_app$a (llist_all2$b ?v0) (fun_app$x (ldrop$a ?v3) ?v1)) (fun_app$x (ldrop$a ?v3) ?v2)))) :named a65))
(assert (! (forall ((?v0 A_llist_a_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 Enat$)) (=> (fun_app$b (fun_app$p (llist_all2$l ?v0) ?v1) ?v2) (fun_app$b (fun_app$p (llist_all2$l ?v0) (fun_app$y (ldrop$b ?v3) ?v1)) (fun_app$w (ldrop$ ?v3) ?v2)))) :named a66))
(assert (! (forall ((?v0 A_llist_b_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 B_llist$) (?v3 Enat$)) (=> (fun_app$ (fun_app$o (llist_all2$k ?v0) ?v1) ?v2) (fun_app$ (fun_app$o (llist_all2$k ?v0) (fun_app$y (ldrop$b ?v3) ?v1)) (fun_app$x (ldrop$a ?v3) ?v2)))) :named a67))
(assert (! (forall ((?v0 B_llist_a_bool_fun_fun$) (?v1 B_llist_llist$) (?v2 A_llist$) (?v3 Enat$)) (=> (fun_app$b (fun_app$n (llist_all2$j ?v0) ?v1) ?v2) (fun_app$b (fun_app$n (llist_all2$j ?v0) (fun_app$z (ldrop$c ?v3) ?v1)) (fun_app$w (ldrop$ ?v3) ?v2)))) :named a68))
(assert (! (forall ((?v0 B_llist_b_bool_fun_fun$) (?v1 B_llist_llist$) (?v2 B_llist$) (?v3 Enat$)) (=> (fun_app$ (fun_app$m (llist_all2$i ?v0) ?v1) ?v2) (fun_app$ (fun_app$m (llist_all2$i ?v0) (fun_app$z (ldrop$c ?v3) ?v1)) (fun_app$x (ldrop$a ?v3) ?v2)))) :named a69))
(assert (! (forall ((?v0 A_a_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist_llist$) (?v3 Enat$)) (=> (fun_app$l (llist_all2$h ?v0 ?v1) ?v2) (fun_app$l (llist_all2$h ?v0 (fun_app$w (ldrop$ ?v3) ?v1)) (fun_app$y (ldrop$b ?v3) ?v2)))) :named a70))
(assert (! (forall ((?v0 A_b_bool_fun_fun$)) (fun_app$ (fun_app$h (llist_all2$ ?v0) lNil$) lNil$a)) :named a71))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$)) (fun_app$i (llist_all2$a ?v0 lNil$b) lNil$c)) :named a72))
(assert (! (forall ((?v0 B_b_bool_fun_fun$)) (fun_app$ (fun_app$a (llist_all2$b ?v0) lNil$a) lNil$a)) :named a73))
(assert (! (forall ((?v0 B_a_bool_fun_fun$)) (fun_app$b (fun_app$k (llist_all2$d ?v0) lNil$a) lNil$)) :named a74))
(assert (! (forall ((?v0 A_a_bool_fun_fun$)) (fun_app$b (fun_app$c (llist_all2$c ?v0) lNil$) lNil$)) :named a75))
(assert (! (forall ((?v0 B_llist_b_bool_fun_fun$)) (fun_app$ (fun_app$m (llist_all2$i ?v0) lNil$c) lNil$a)) :named a76))
(assert (! (forall ((?v0 B_llist_a_bool_fun_fun$)) (fun_app$b (fun_app$n (llist_all2$j ?v0) lNil$c) lNil$)) :named a77))
(assert (! (forall ((?v0 A_llist_b_bool_fun_fun$)) (fun_app$ (fun_app$o (llist_all2$k ?v0) lNil$b) lNil$a)) :named a78))
(assert (! (forall ((?v0 A_llist_a_bool_fun_fun$)) (fun_app$b (fun_app$p (llist_all2$l ?v0) lNil$b) lNil$)) :named a79))
(assert (! (forall ((?v0 B_b_llist_bool_fun_fun$)) (fun_app$i (llist_all2$e ?v0 lNil$a) lNil$c)) :named a80))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 B_llist$)) (= (fun_app$ (fun_app$h (llist_all2$ ?v0) (lCons$ ?v1 ?v2)) ?v3) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v3 (lCons$a ?v4 ?v5)) (and (fun_app$d (fun_app$j ?v0 ?v1) ?v4) (fun_app$ (fun_app$h (llist_all2$ ?v0) ?v2) ?v5)))))) :named a81))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist_llist$) (?v3 B_llist_llist$)) (= (fun_app$i (llist_all2$a ?v0 (lCons$b ?v1 ?v2)) ?v3) (exists ((?v4 B_llist$) (?v5 B_llist_llist$)) (and (= ?v3 (lCons$c ?v4 ?v5)) (and (fun_app$ (fun_app$h ?v0 ?v1) ?v4) (fun_app$i (llist_all2$a ?v0 ?v2) ?v5)))))) :named a82))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 A_llist$)) (= (fun_app$b (fun_app$c (llist_all2$c ?v0) (lCons$ ?v1 ?v2)) ?v3) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v3 (lCons$ ?v4 ?v5)) (and (fun_app$f (fun_app$g ?v0 ?v1) ?v4) (fun_app$b (fun_app$c (llist_all2$c ?v0) ?v2) ?v5)))))) :named a83))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B$) (?v2 B_llist$) (?v3 A_llist$)) (= (fun_app$b (fun_app$k (llist_all2$d ?v0) (lCons$a ?v1 ?v2)) ?v3) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v3 (lCons$ ?v4 ?v5)) (and (fun_app$f (fun_app$q ?v0 ?v1) ?v4) (fun_app$b (fun_app$k (llist_all2$d ?v0) ?v2) ?v5)))))) :named a84))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B$) (?v2 B_llist$) (?v3 B_llist$)) (= (fun_app$ (fun_app$a (llist_all2$b ?v0) (lCons$a ?v1 ?v2)) ?v3) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v3 (lCons$a ?v4 ?v5)) (and (fun_app$d (fun_app$e ?v0 ?v1) ?v4) (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v2) ?v5)))))) :named a85))
(assert (! (forall ((?v0 A_llist_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist_llist$) (?v3 A_llist$)) (= (fun_app$b (fun_app$p (llist_all2$l ?v0) (lCons$b ?v1 ?v2)) ?v3) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v3 (lCons$ ?v4 ?v5)) (and (fun_app$f (fun_app$r ?v0 ?v1) ?v4) (fun_app$b (fun_app$p (llist_all2$l ?v0) ?v2) ?v5)))))) :named a86))
(assert (! (forall ((?v0 A_llist_b_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist_llist$) (?v3 B_llist$)) (= (fun_app$ (fun_app$o (llist_all2$k ?v0) (lCons$b ?v1 ?v2)) ?v3) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v3 (lCons$a ?v4 ?v5)) (and (fun_app$d (fun_app$s ?v0 ?v1) ?v4) (fun_app$ (fun_app$o (llist_all2$k ?v0) ?v2) ?v5)))))) :named a87))
(assert (! (forall ((?v0 B_llist_a_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist_llist$) (?v3 A_llist$)) (= (fun_app$b (fun_app$n (llist_all2$j ?v0) (lCons$c ?v1 ?v2)) ?v3) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v3 (lCons$ ?v4 ?v5)) (and (fun_app$f (fun_app$t ?v0 ?v1) ?v4) (fun_app$b (fun_app$n (llist_all2$j ?v0) ?v2) ?v5)))))) :named a88))
(assert (! (forall ((?v0 B_llist_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist_llist$) (?v3 B_llist$)) (= (fun_app$ (fun_app$m (llist_all2$i ?v0) (lCons$c ?v1 ?v2)) ?v3) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v3 (lCons$a ?v4 ?v5)) (and (fun_app$d (fun_app$u ?v0 ?v1) ?v4) (fun_app$ (fun_app$m (llist_all2$i ?v0) ?v2) ?v5)))))) :named a89))
(assert (! (forall ((?v0 A_a_llist_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 A_llist_llist$)) (= (fun_app$l (llist_all2$h ?v0 (lCons$ ?v1 ?v2)) ?v3) (exists ((?v4 A_llist$) (?v5 A_llist_llist$)) (and (= ?v3 (lCons$b ?v4 ?v5)) (and (fun_app$b (fun_app$v ?v0 ?v1) ?v4) (fun_app$l (llist_all2$h ?v0 ?v2) ?v5)))))) :named a90))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B$) (?v3 B_llist$)) (= (fun_app$ (fun_app$h (llist_all2$ ?v0) ?v1) (lCons$a ?v2 ?v3)) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v1 (lCons$ ?v4 ?v5)) (and (fun_app$d (fun_app$j ?v0 ?v4) ?v2) (fun_app$ (fun_app$h (llist_all2$ ?v0) ?v5) ?v3)))))) :named a91))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 B_llist$) (?v3 B_llist_llist$)) (= (fun_app$i (llist_all2$a ?v0 ?v1) (lCons$c ?v2 ?v3)) (exists ((?v4 A_llist$) (?v5 A_llist_llist$)) (and (= ?v1 (lCons$b ?v4 ?v5)) (and (fun_app$ (fun_app$h ?v0 ?v4) ?v2) (fun_app$i (llist_all2$a ?v0 ?v5) ?v3)))))) :named a92))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (fun_app$b (fun_app$c (llist_all2$c ?v0) ?v1) (lCons$ ?v2 ?v3)) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v1 (lCons$ ?v4 ?v5)) (and (fun_app$f (fun_app$g ?v0 ?v4) ?v2) (fun_app$b (fun_app$c (llist_all2$c ?v0) ?v5) ?v3)))))) :named a93))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A$) (?v3 A_llist$)) (= (fun_app$b (fun_app$k (llist_all2$d ?v0) ?v1) (lCons$ ?v2 ?v3)) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v1 (lCons$a ?v4 ?v5)) (and (fun_app$f (fun_app$q ?v0 ?v4) ?v2) (fun_app$b (fun_app$k (llist_all2$d ?v0) ?v5) ?v3)))))) :named a94))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B$) (?v3 B_llist$)) (= (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v1) (lCons$a ?v2 ?v3)) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v1 (lCons$a ?v4 ?v5)) (and (fun_app$d (fun_app$e ?v0 ?v4) ?v2) (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v5) ?v3)))))) :named a95))
(assert (! (forall ((?v0 A_a_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (= (fun_app$l (llist_all2$h ?v0 ?v1) (lCons$b ?v2 ?v3)) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v1 (lCons$ ?v4 ?v5)) (and (fun_app$b (fun_app$v ?v0 ?v4) ?v2) (fun_app$l (llist_all2$h ?v0 ?v5) ?v3)))))) :named a96))
(assert (! (forall ((?v0 B_a_llist_bool_fun_fun$) (?v1 B_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (= (fun_app$l (llist_all2$g ?v0 ?v1) (lCons$b ?v2 ?v3)) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v1 (lCons$a ?v4 ?v5)) (and (fun_app$b (fun_app$aa ?v0 ?v4) ?v2) (fun_app$l (llist_all2$g ?v0 ?v5) ?v3)))))) :named a97))
(assert (! (forall ((?v0 A_b_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 B_llist_llist$)) (= (fun_app$i (llist_all2$f ?v0 ?v1) (lCons$c ?v2 ?v3)) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v1 (lCons$ ?v4 ?v5)) (and (fun_app$ (fun_app$ab ?v0 ?v4) ?v2) (fun_app$i (llist_all2$f ?v0 ?v5) ?v3)))))) :named a98))
(assert (! (forall ((?v0 B_b_llist_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$) (?v3 B_llist_llist$)) (= (fun_app$i (llist_all2$e ?v0 ?v1) (lCons$c ?v2 ?v3)) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v1 (lCons$a ?v4 ?v5)) (and (fun_app$ (fun_app$ac ?v0 ?v4) ?v2) (fun_app$i (llist_all2$e ?v0 ?v5) ?v3)))))) :named a99))
(assert (! (forall ((?v0 A_llist_a_bool_fun_fun$) (?v1 A_llist_llist$) (?v2 A$) (?v3 A_llist$)) (= (fun_app$b (fun_app$p (llist_all2$l ?v0) ?v1) (lCons$ ?v2 ?v3)) (exists ((?v4 A_llist$) (?v5 A_llist_llist$)) (and (= ?v1 (lCons$b ?v4 ?v5)) (and (fun_app$f (fun_app$r ?v0 ?v4) ?v2) (fun_app$b (fun_app$p (llist_all2$l ?v0) ?v5) ?v3)))))) :named a100))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A$) (?v2 B$) (?v3 A_llist$) (?v4 B_llist$)) (=> (and (fun_app$d (fun_app$j ?v0 ?v1) ?v2) (fun_app$ (fun_app$h (llist_all2$ ?v0) ?v3) ?v4)) (fun_app$ (fun_app$h (llist_all2$ ?v0) (lCons$ ?v1 ?v3)) (lCons$a ?v2 ?v4)))) :named a101))
(assert (! (forall ((?v0 A_llist_b_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 A_llist_llist$) (?v4 B_llist_llist$)) (=> (and (fun_app$ (fun_app$h ?v0 ?v1) ?v2) (fun_app$i (llist_all2$a ?v0 ?v3) ?v4)) (fun_app$i (llist_all2$a ?v0 (lCons$b ?v1 ?v3)) (lCons$c ?v2 ?v4)))) :named a102))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A$) (?v2 A$) (?v3 A_llist$) (?v4 A_llist$)) (=> (and (fun_app$f (fun_app$g ?v0 ?v1) ?v2) (fun_app$b (fun_app$c (llist_all2$c ?v0) ?v3) ?v4)) (fun_app$b (fun_app$c (llist_all2$c ?v0) (lCons$ ?v1 ?v3)) (lCons$ ?v2 ?v4)))) :named a103))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B$) (?v2 A$) (?v3 B_llist$) (?v4 A_llist$)) (=> (and (fun_app$f (fun_app$q ?v0 ?v1) ?v2) (fun_app$b (fun_app$k (llist_all2$d ?v0) ?v3) ?v4)) (fun_app$b (fun_app$k (llist_all2$d ?v0) (lCons$a ?v1 ?v3)) (lCons$ ?v2 ?v4)))) :named a104))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B$) (?v2 B$) (?v3 B_llist$) (?v4 B_llist$)) (=> (and (fun_app$d (fun_app$e ?v0 ?v1) ?v2) (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v3) ?v4)) (fun_app$ (fun_app$a (llist_all2$b ?v0) (lCons$a ?v1 ?v3)) (lCons$a ?v2 ?v4)))) :named a105))
(assert (! (forall ((?v0 A_llist_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist_llist$) (?v4 A_llist$)) (=> (and (fun_app$f (fun_app$r ?v0 ?v1) ?v2) (fun_app$b (fun_app$p (llist_all2$l ?v0) ?v3) ?v4)) (fun_app$b (fun_app$p (llist_all2$l ?v0) (lCons$b ?v1 ?v3)) (lCons$ ?v2 ?v4)))) :named a106))
(assert (! (forall ((?v0 A_llist_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B$) (?v3 A_llist_llist$) (?v4 B_llist$)) (=> (and (fun_app$d (fun_app$s ?v0 ?v1) ?v2) (fun_app$ (fun_app$o (llist_all2$k ?v0) ?v3) ?v4)) (fun_app$ (fun_app$o (llist_all2$k ?v0) (lCons$b ?v1 ?v3)) (lCons$a ?v2 ?v4)))) :named a107))
(assert (! (forall ((?v0 B_llist_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A$) (?v3 B_llist_llist$) (?v4 A_llist$)) (=> (and (fun_app$f (fun_app$t ?v0 ?v1) ?v2) (fun_app$b (fun_app$n (llist_all2$j ?v0) ?v3) ?v4)) (fun_app$b (fun_app$n (llist_all2$j ?v0) (lCons$c ?v1 ?v3)) (lCons$ ?v2 ?v4)))) :named a108))
(assert (! (forall ((?v0 B_llist_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B$) (?v3 B_llist_llist$) (?v4 B_llist$)) (=> (and (fun_app$d (fun_app$u ?v0 ?v1) ?v2) (fun_app$ (fun_app$m (llist_all2$i ?v0) ?v3) ?v4)) (fun_app$ (fun_app$m (llist_all2$i ?v0) (lCons$c ?v1 ?v3)) (lCons$a ?v2 ?v4)))) :named a109))
(assert (! (forall ((?v0 A_a_llist_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 A_llist$) (?v4 A_llist_llist$)) (=> (and (fun_app$b (fun_app$v ?v0 ?v1) ?v2) (fun_app$l (llist_all2$h ?v0 ?v3) ?v4)) (fun_app$l (llist_all2$h ?v0 (lCons$ ?v1 ?v3)) (lCons$b ?v2 ?v4)))) :named a110))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (= (= (lCons$b ?v0 ?v1) (lCons$b ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a111))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist_llist$) (?v2 B_llist$) (?v3 B_llist_llist$)) (= (= (lCons$c ?v0 ?v1) (lCons$c ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a112))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a113))
(assert (! (forall ((?v0 B$) (?v1 B_llist$) (?v2 B$) (?v3 B_llist$)) (= (= (lCons$a ?v0 ?v1) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a114))
(assert (! (forall ((?v0 Enat$)) (! (= (fun_app$z (ldrop$c ?v0) lNil$c) lNil$c) :pattern ((ldrop$c ?v0)))) :named a115))
(assert (! (forall ((?v0 Enat$)) (! (= (fun_app$y (ldrop$b ?v0) lNil$b) lNil$b) :pattern ((ldrop$b ?v0)))) :named a116))
(assert (! (forall ((?v0 Enat$)) (! (= (fun_app$x (ldrop$a ?v0) lNil$a) lNil$a) :pattern ((ldrop$a ?v0)))) :named a117))
(assert (! (forall ((?v0 Enat$)) (! (= (fun_app$w (ldrop$ ?v0) lNil$) lNil$) :pattern ((ldrop$ ?v0)))) :named a118))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$z (ldropn$c ?v0) lNil$c) lNil$c) :pattern ((ldropn$c ?v0)))) :named a119))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$y (ldropn$b ?v0) lNil$b) lNil$b) :pattern ((ldropn$b ?v0)))) :named a120))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$x (ldropn$a ?v0) lNil$a) lNil$a) :pattern ((ldropn$a ?v0)))) :named a121))
(assert (! (forall ((?v0 Nat$)) (! (= (fun_app$w (ldropn$ ?v0) lNil$) lNil$) :pattern ((ldropn$ ?v0)))) :named a122))
(check-sat)
;(get-unsat-core)
