; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 566
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort Nat$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_b_fun$ 0)
(declare-sort B_a_fun$ 0)
(declare-sort B_b_fun$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort A_a_bool_fun_fun$ 0)
(declare-sort A_b_bool_fun_fun$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort B_a_bool_fun_fun$ 0)
(declare-sort B_b_bool_fun_fun$ 0)
(declare-sort B_llist_bool_fun$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun$ 0)
(declare-sort B_llist_b_llist_bool_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))
  (B_llist$ (lNil$a) (lCons$a (lhd$a B$) (ltl$a B_llist$)))))
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-fun p$ () A_b_bool_fun_fun$)
(declare-fun uu$ () A_a_bool_fun_fun$)
(declare-fun xs$ () A_llist$)
(declare-fun ys$ () B_llist$)
(declare-fun uua$ () A_llist_a_llist_bool_fun_fun$)
(declare-fun uub$ () B_b_bool_fun_fun$)
(declare-fun uuc$ () B_llist_b_llist_bool_fun_fun$)
(declare-fun lmap$ (A_a_fun$ A_llist$) A_llist$)
(declare-fun ldrop$ (Enat$ A_llist$) A_llist$)
(declare-fun lmap$a (B_a_fun$ B_llist$) A_llist$)
(declare-fun lmap$b (A_b_fun$ A_llist$) B_llist$)
(declare-fun lmap$c (B_b_fun$ B_llist$) B_llist$)
(declare-fun ldrop$a (Enat$ B_llist$) B_llist$)
(declare-fun ldropn$ (Nat$ A_llist$) A_llist$)
(declare-fun fun_app$ (B_llist_bool_fun$ B_llist$) Bool)
(declare-fun ldropn$a (Nat$ B_llist$) B_llist$)
(declare-fun lfinite$ (A_llist$) Bool)
(declare-fun fun_app$a (B_llist_b_llist_bool_fun_fun$ B_llist$) B_llist_bool_fun$)
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun fun_app$c (A_llist_a_llist_bool_fun_fun$ A_llist$) A_llist_bool_fun$)
(declare-fun fun_app$d (B_bool_fun$ B$) Bool)
(declare-fun fun_app$e (B_b_bool_fun_fun$ B$) B_bool_fun$)
(declare-fun fun_app$f (A_bool_fun$ A$) Bool)
(declare-fun fun_app$g (A_a_bool_fun_fun$ A$) A_bool_fun$)
(declare-fun fun_app$h (B_a_bool_fun_fun$ B$) A_bool_fun$)
(declare-fun fun_app$i (A_b_bool_fun_fun$ A$) B_bool_fun$)
(declare-fun fun_app$j (A_a_fun$ A$) A$)
(declare-fun fun_app$k (B_b_fun$ B$) B$)
(declare-fun iterates$ (A_a_fun$ A$) A_llist$)
(declare-fun lfinite$a (B_llist$) Bool)
(declare-fun iterates$a (B_b_fun$ B$) B_llist$)
(declare-fun llist_all2$ (A_b_bool_fun_fun$ A_llist$) B_llist_bool_fun$)
(declare-fun llist_all2$a (A_a_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun llist_all2$b (B_b_bool_fun_fun$) B_llist_b_llist_bool_fun_fun$)
(declare-fun llist_all2$c (B_a_bool_fun_fun$ B_llist$) A_llist_bool_fun$)
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a uuc$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$ (fun_app$a uuc$ ?v0) ?v1)))) :named a0))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$c uua$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$b (fun_app$c uua$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 B$) (?v1 B$)) (! (= (fun_app$d (fun_app$e uub$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$d (fun_app$e uub$ ?v0) ?v1)))) :named a2))
(assert (! (forall ((?v0 A$) (?v1 A$)) (! (= (fun_app$f (fun_app$g uu$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$f (fun_app$g uu$ ?v0) ?v1)))) :named a3))
(assert (! (not (fun_app$ (llist_all2$ p$ (ltl$ xs$)) (ltl$a ys$))) :named a4))
(assert (! (fun_app$ (llist_all2$ p$ xs$) ys$) :named a5))
(assert (! (= (llist_all2$a uu$) uua$) :named a6))
(assert (! (= (llist_all2$b uub$) uuc$) :named a7))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_a_bool_fun_fun$)) (=> (and (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v1) ?v2) (forall ((?v4 A$) (?v5 A$)) (=> (fun_app$f (fun_app$g ?v0 ?v4) ?v5) (fun_app$f (fun_app$g ?v3 ?v4) ?v5)))) (fun_app$b (fun_app$c (llist_all2$a ?v3) ?v1) ?v2))) :named a8))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A_llist$) (?v3 B_a_bool_fun_fun$)) (=> (and (fun_app$b (llist_all2$c ?v0 ?v1) ?v2) (forall ((?v4 B$) (?v5 A$)) (=> (fun_app$f (fun_app$h ?v0 ?v4) ?v5) (fun_app$f (fun_app$h ?v3 ?v4) ?v5)))) (fun_app$b (llist_all2$c ?v3 ?v1) ?v2))) :named a9))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$) (?v3 B_b_bool_fun_fun$)) (=> (and (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v1) ?v2) (forall ((?v4 B$) (?v5 B$)) (=> (fun_app$d (fun_app$e ?v0 ?v4) ?v5) (fun_app$d (fun_app$e ?v3 ?v4) ?v5)))) (fun_app$ (fun_app$a (llist_all2$b ?v3) ?v1) ?v2))) :named a10))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 A_b_bool_fun_fun$)) (=> (and (fun_app$ (llist_all2$ ?v0 ?v1) ?v2) (forall ((?v4 A$) (?v5 B$)) (=> (fun_app$d (fun_app$i ?v0 ?v4) ?v5) (fun_app$d (fun_app$i ?v3 ?v4) ?v5)))) (fun_app$ (llist_all2$ ?v3 ?v1) ?v2))) :named a11))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v1) lNil$a) (= ?v1 lNil$a)) :pattern ((fun_app$a (llist_all2$b ?v0) ?v1)))) :named a12))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$b (llist_all2$c ?v0 ?v1) lNil$) (= ?v1 lNil$a)) :pattern ((llist_all2$c ?v0 ?v1)))) :named a13))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v1) lNil$) (= ?v1 lNil$)) :pattern ((fun_app$c (llist_all2$a ?v0) ?v1)))) :named a14))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$ (llist_all2$ ?v0 ?v1) lNil$a) (= ?v1 lNil$)) :pattern ((llist_all2$ ?v0 ?v1)))) :named a15))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a (llist_all2$b ?v0) lNil$a) ?v1) (= ?v1 lNil$a)) :pattern ((fun_app$ (fun_app$a (llist_all2$b ?v0) lNil$a) ?v1)))) :named a16))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (llist_all2$c ?v0 lNil$a) ?v1) (= ?v1 lNil$)) :pattern ((fun_app$b (llist_all2$c ?v0 lNil$a) ?v1)))) :named a17))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$c (llist_all2$a ?v0) lNil$) ?v1) (= ?v1 lNil$)) :pattern ((fun_app$b (fun_app$c (llist_all2$a ?v0) lNil$) ?v1)))) :named a18))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 B_llist$)) (! (= (fun_app$ (llist_all2$ ?v0 lNil$) ?v1) (= ?v1 lNil$a)) :pattern ((fun_app$ (llist_all2$ ?v0 lNil$) ?v1)))) :named a19))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$)) (= (ltl$ (iterates$ ?v0 ?v1)) (iterates$ ?v0 (fun_app$j ?v0 ?v1)))) :named a20))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B$)) (= (ltl$a (iterates$a ?v0 ?v1)) (iterates$a ?v0 (fun_app$k ?v0 ?v1)))) :named a21))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$b (fun_app$c (llist_all2$a ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v3 ?v4)) (and (fun_app$f (fun_app$g ?v0 ?v1) ?v3) (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v2) ?v4))) :pattern ((fun_app$b (fun_app$c (llist_all2$a ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a22))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B$) (?v2 B_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$b (llist_all2$c ?v0 (lCons$a ?v1 ?v2)) (lCons$ ?v3 ?v4)) (and (fun_app$f (fun_app$h ?v0 ?v1) ?v3) (fun_app$b (llist_all2$c ?v0 ?v2) ?v4))) :pattern ((fun_app$b (llist_all2$c ?v0 (lCons$a ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a23))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B$) (?v2 B_llist$) (?v3 B$) (?v4 B_llist$)) (! (= (fun_app$ (fun_app$a (llist_all2$b ?v0) (lCons$a ?v1 ?v2)) (lCons$a ?v3 ?v4)) (and (fun_app$d (fun_app$e ?v0 ?v1) ?v3) (fun_app$ (fun_app$a (llist_all2$b ?v0) ?v2) ?v4))) :pattern ((fun_app$ (fun_app$a (llist_all2$b ?v0) (lCons$a ?v1 ?v2)) (lCons$a ?v3 ?v4))))) :named a24))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 B$) (?v4 B_llist$)) (! (= (fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v2)) (lCons$a ?v3 ?v4)) (and (fun_app$d (fun_app$i ?v0 ?v1) ?v3) (fun_app$ (llist_all2$ ?v0 ?v2) ?v4))) :pattern ((fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v2)) (lCons$a ?v3 ?v4))))) :named a25))
(assert (! (forall ((?v0 A_llist$)) (= (lfinite$ (ltl$ ?v0)) (lfinite$ ?v0))) :named a26))
(assert (! (forall ((?v0 B_llist$)) (= (lfinite$a (ltl$a ?v0)) (lfinite$a ?v0))) :named a27))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (ltl$ (lmap$ ?v0 ?v1)) (lmap$ ?v0 (ltl$ ?v1)))) :named a28))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_llist$)) (= (ltl$ (lmap$a ?v0 ?v1)) (lmap$a ?v0 (ltl$a ?v1)))) :named a29))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_llist$)) (= (ltl$a (lmap$b ?v0 ?v1)) (lmap$b ?v0 (ltl$ ?v1)))) :named a30))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_llist$)) (= (ltl$a (lmap$c ?v0 ?v1)) (lmap$c ?v0 (ltl$a ?v1)))) :named a31))
(assert (! (forall ((?v0 Nat$) (?v1 A_llist$)) (= (ltl$ (ldropn$ ?v0 ?v1)) (ldropn$ ?v0 (ltl$ ?v1)))) :named a32))
(assert (! (forall ((?v0 Nat$) (?v1 B_llist$)) (= (ltl$a (ldropn$a ?v0 ?v1)) (ldropn$a ?v0 (ltl$a ?v1)))) :named a33))
(assert (! (forall ((?v0 Enat$) (?v1 A_llist$)) (= (ltl$ (ldrop$ ?v0 ?v1)) (ldrop$ ?v0 (ltl$ ?v1)))) :named a34))
(assert (! (forall ((?v0 Enat$) (?v1 B_llist$)) (= (ltl$a (ldrop$a ?v0 ?v1)) (ldrop$a ?v0 (ltl$a ?v1)))) :named a35))
(assert (! (forall ((?v0 B_b_bool_fun_fun$)) (fun_app$ (fun_app$a (llist_all2$b ?v0) lNil$a) lNil$a)) :named a36))
(assert (! (forall ((?v0 B_a_bool_fun_fun$)) (fun_app$b (llist_all2$c ?v0 lNil$a) lNil$)) :named a37))
(assert (! (forall ((?v0 A_a_bool_fun_fun$)) (fun_app$b (fun_app$c (llist_all2$a ?v0) lNil$) lNil$)) :named a38))
(assert (! (forall ((?v0 A_b_bool_fun_fun$)) (fun_app$ (llist_all2$ ?v0 lNil$) lNil$a)) :named a39))
(assert (! (= (ltl$ lNil$) lNil$) :named a40))
(assert (! (= (ltl$a lNil$a) lNil$a) :named a41))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a42))
(assert (! (forall ((?v0 B$) (?v1 B_llist$) (?v2 B$) (?v3 B_llist$)) (= (= (lCons$a ?v0 ?v1) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a43))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a44))
(assert (! (forall ((?v0 B$) (?v1 B_llist$)) (! (= (lfinite$a (lCons$a ?v0 ?v1)) (lfinite$a ?v1)) :pattern ((lCons$a ?v0 ?v1)))) :named a45))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a46))
(assert (! (forall ((?v0 B$) (?v1 B_llist$)) (! (= (lfinite$a (lCons$a ?v0 ?v1)) (lfinite$a ?v1)) :pattern ((lCons$a ?v0 ?v1)))) :named a47))
(check-sat)
;(get-unsat-core)
