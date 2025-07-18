; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 539
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort Bool_bool_fun$ 0)
(declare-sort A_a_bool_fun_fun$ 0)
(declare-sort A_b_bool_fun_fun$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort B_a_bool_fun_fun$ 0)
(declare-sort B_b_bool_fun_fun$ 0)
(declare-sort B_llist_bool_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-sort B_llist_b_llist_fun$ 0)
(declare-sort Bool_bool_bool_fun_fun$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun$ 0)
(declare-sort A_llist_b_llist_bool_fun_fun$ 0)
(declare-sort B_llist_a_llist_bool_fun_fun$ 0)
(declare-sort B_llist_b_llist_bool_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))
  (B_llist$ (lNil$a) (lCons$a (lhd$a B$) (ltl$a B_llist$)))))
(declare-fun p$ () A_b_bool_fun_fun$)
(declare-fun uu$ () B_b_bool_fun_fun$)
(declare-fun xs$ () A_llist$)
(declare-fun acc$ () A_llist$)
(declare-fun uua$ () B_llist_b_llist_bool_fun_fun$)
(declare-fun uub$ () A_a_bool_fun_fun$)
(declare-fun uuc$ () A_llist_a_llist_bool_fun_fun$)
(declare-fun uud$ () Bool_bool_bool_fun_fun$)
(declare-fun xs$a () B_llist$)
(declare-fun acc$a () B_llist$)
(declare-fun lnull$ (A_llist$) Bool)
(declare-fun lnull$a (B_llist$) Bool)
(declare-fun fun_app$ (B_llist_bool_fun$ B_llist$) Bool)
(declare-fun lappend$ (B_llist$ B_llist$) B_llist$)
(declare-fun lfinite$ () A_llist_bool_fun$)
(declare-fun rel_fun$ (B_llist_b_llist_bool_fun_fun$ Bool_bool_bool_fun_fun$ B_llist_bool_fun$ B_llist_bool_fun$) Bool)
(declare-fun fun_app$a (B_llist_b_llist_bool_fun_fun$ B_llist$) B_llist_bool_fun$)
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun fun_app$c (A_llist_a_llist_bool_fun_fun$ A_llist$) A_llist_bool_fun$)
(declare-fun fun_app$d (Bool_bool_fun$ Bool) Bool)
(declare-fun fun_app$e (Bool_bool_bool_fun_fun$ Bool) Bool_bool_fun$)
(declare-fun fun_app$f (B_bool_fun$ B$) Bool)
(declare-fun fun_app$g (B_b_bool_fun_fun$ B$) B_bool_fun$)
(declare-fun fun_app$h (A_bool_fun$ A$) Bool)
(declare-fun fun_app$i (A_a_bool_fun_fun$ A$) A_bool_fun$)
(declare-fun fun_app$j (A_llist_b_llist_bool_fun_fun$ A_llist$) B_llist_bool_fun$)
(declare-fun fun_app$k (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun fun_app$l (B_llist_b_llist_fun$ B_llist$) B_llist$)
(declare-fun fun_app$m (B_llist_a_llist_bool_fun_fun$ B_llist$) A_llist_bool_fun$)
(declare-fun fun_app$n (B_a_bool_fun_fun$ B$) A_bool_fun$)
(declare-fun fun_app$o (A_b_bool_fun_fun$ A$) B_bool_fun$)
(declare-fun lappend$a (A_llist$ A_llist$) A_llist$)
(declare-fun lfinite$a () B_llist_bool_fun$)
(declare-fun rel_fun$a (B_llist_a_llist_bool_fun_fun$ Bool_bool_bool_fun_fun$ B_llist_bool_fun$ A_llist_bool_fun$) Bool)
(declare-fun rel_fun$b (A_llist_a_llist_bool_fun_fun$ Bool_bool_bool_fun_fun$ A_llist_bool_fun$ A_llist_bool_fun$) Bool)
(declare-fun rel_fun$c (A_llist_b_llist_bool_fun_fun$ Bool_bool_bool_fun_fun$ A_llist_bool_fun$ B_llist_bool_fun$) Bool)
(declare-fun llist_all2$ (A_b_bool_fun_fun$) A_llist_b_llist_bool_fun_fun$)
(declare-fun llist_all2$a (A_a_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun llist_all2$b (B_a_bool_fun_fun$) B_llist_a_llist_bool_fun_fun$)
(declare-fun llist_all2$c (B_b_bool_fun_fun$) B_llist_b_llist_bool_fun_fun$)
(declare-fun lmirror_aux$ (A_llist$) A_llist_a_llist_fun$)
(declare-fun lmirror_aux$a (B_llist$) B_llist_b_llist_fun$)
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (! (= (fun_app$ (fun_app$a uua$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$ (fun_app$a uua$ ?v0) ?v1)))) :named a0))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (= (fun_app$b (fun_app$c uuc$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$b (fun_app$c uuc$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 Bool) (?v1 Bool)) (! (= (fun_app$d (fun_app$e uud$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$d (fun_app$e uud$ ?v0) ?v1)))) :named a2))
(assert (! (forall ((?v0 B$) (?v1 B$)) (! (= (fun_app$f (fun_app$g uu$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$f (fun_app$g uu$ ?v0) ?v1)))) :named a3))
(assert (! (forall ((?v0 A$) (?v1 A$)) (! (= (fun_app$h (fun_app$i uub$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$h (fun_app$i uub$ ?v0) ?v1)))) :named a4))
(assert (! (not (fun_app$ (fun_app$j (llist_all2$ p$) xs$) xs$a)) :named a5))
(assert (! (fun_app$ (fun_app$j (llist_all2$ p$) (fun_app$k (lmirror_aux$ acc$) xs$)) (fun_app$l (lmirror_aux$a acc$a) xs$a)) :named a6))
(assert (! (fun_app$ (fun_app$j (llist_all2$ p$) acc$) acc$a) :named a7))
(assert (! (fun_app$b lfinite$ acc$) :named a8))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (fun_app$b lfinite$ (fun_app$k (lmirror_aux$ ?v0) ?v1)) (and (fun_app$b lfinite$ ?v1) (fun_app$b lfinite$ ?v0)))) :named a9))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (= (fun_app$ lfinite$a (fun_app$l (lmirror_aux$a ?v0) ?v1)) (and (fun_app$ lfinite$a ?v1) (fun_app$ lfinite$a ?v0)))) :named a10))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_llist$) (?v4 A_llist$)) (=> (and (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v1) ?v2) (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v3) ?v4)) (fun_app$b (fun_app$c (llist_all2$a ?v0) (fun_app$k (lmirror_aux$ ?v1) ?v3)) (fun_app$k (lmirror_aux$ ?v2) ?v4)))) :named a11))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 A_llist$) (?v4 B_llist$)) (=> (and (fun_app$ (fun_app$j (llist_all2$ ?v0) ?v1) ?v2) (fun_app$ (fun_app$j (llist_all2$ ?v0) ?v3) ?v4)) (fun_app$ (fun_app$j (llist_all2$ ?v0) (fun_app$k (lmirror_aux$ ?v1) ?v3)) (fun_app$l (lmirror_aux$a ?v2) ?v4)))) :named a12))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A_llist$) (?v3 B_llist$) (?v4 A_llist$)) (=> (and (fun_app$b (fun_app$m (llist_all2$b ?v0) ?v1) ?v2) (fun_app$b (fun_app$m (llist_all2$b ?v0) ?v3) ?v4)) (fun_app$b (fun_app$m (llist_all2$b ?v0) (fun_app$l (lmirror_aux$a ?v1) ?v3)) (fun_app$k (lmirror_aux$ ?v2) ?v4)))) :named a13))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$) (?v3 B_llist$) (?v4 B_llist$)) (=> (and (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v1) ?v2) (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v3) ?v4)) (fun_app$ (fun_app$a (llist_all2$c ?v0) (fun_app$l (lmirror_aux$a ?v1) ?v3)) (fun_app$l (lmirror_aux$a ?v2) ?v4)))) :named a14))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (=> (not (fun_app$b lfinite$ ?v0)) (= (fun_app$k (lmirror_aux$ ?v1) ?v0) ?v0)) :pattern ((fun_app$k (lmirror_aux$ ?v1) ?v0)))) :named a15))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (! (=> (not (fun_app$ lfinite$a ?v0)) (= (fun_app$l (lmirror_aux$a ?v1) ?v0) ?v0)) :pattern ((fun_app$l (lmirror_aux$a ?v1) ?v0)))) :named a16))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$)) (=> (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v1) ?v2) (= (fun_app$ lfinite$a ?v1) (fun_app$ lfinite$a ?v2)))) :named a17))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A_llist$)) (=> (fun_app$b (fun_app$m (llist_all2$b ?v0) ?v1) ?v2) (= (fun_app$ lfinite$a ?v1) (fun_app$b lfinite$ ?v2)))) :named a18))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$)) (=> (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v1) ?v2) (= (fun_app$b lfinite$ ?v1) (fun_app$b lfinite$ ?v2)))) :named a19))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$)) (=> (fun_app$ (fun_app$j (llist_all2$ ?v0) ?v1) ?v2) (= (fun_app$b lfinite$ ?v1) (fun_app$ lfinite$a ?v2)))) :named a20))
(assert (! (= (llist_all2$c uu$) uua$) :named a21))
(assert (! (= (llist_all2$a uub$) uuc$) :named a22))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$) (?v3 B_b_bool_fun_fun$)) (=> (and (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v1) ?v2) (forall ((?v4 B$) (?v5 B$)) (=> (fun_app$f (fun_app$g ?v0 ?v4) ?v5) (fun_app$f (fun_app$g ?v3 ?v4) ?v5)))) (fun_app$ (fun_app$a (llist_all2$c ?v3) ?v1) ?v2))) :named a23))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A_llist$) (?v3 B_a_bool_fun_fun$)) (=> (and (fun_app$b (fun_app$m (llist_all2$b ?v0) ?v1) ?v2) (forall ((?v4 B$) (?v5 A$)) (=> (fun_app$h (fun_app$n ?v0 ?v4) ?v5) (fun_app$h (fun_app$n ?v3 ?v4) ?v5)))) (fun_app$b (fun_app$m (llist_all2$b ?v3) ?v1) ?v2))) :named a24))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_a_bool_fun_fun$)) (=> (and (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v1) ?v2) (forall ((?v4 A$) (?v5 A$)) (=> (fun_app$h (fun_app$i ?v0 ?v4) ?v5) (fun_app$h (fun_app$i ?v3 ?v4) ?v5)))) (fun_app$b (fun_app$c (llist_all2$a ?v3) ?v1) ?v2))) :named a25))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 A_b_bool_fun_fun$)) (=> (and (fun_app$ (fun_app$j (llist_all2$ ?v0) ?v1) ?v2) (forall ((?v4 A$) (?v5 B$)) (=> (fun_app$f (fun_app$o ?v0 ?v4) ?v5) (fun_app$f (fun_app$o ?v3 ?v4) ?v5)))) (fun_app$ (fun_app$j (llist_all2$ ?v3) ?v1) ?v2))) :named a26))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_b_bool_fun_fun$) (?v2 B_b_bool_fun_fun$) (?v3 B_llist$) (?v4 B_llist$) (?v5 B_llist$) (?v6 B_llist$)) (=> (and (forall ((?v7 B$) (?v8 B$)) (=> (fun_app$f (fun_app$g ?v0 ?v7) ?v8) (forall ((?v9 B$) (?v10 B$)) (=> (fun_app$f (fun_app$g ?v0 ?v9) ?v10) (= (fun_app$f (fun_app$g ?v1 ?v7) ?v9) (fun_app$f (fun_app$g ?v2 ?v8) ?v10)))))) (and (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v3) ?v4) (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v5) ?v6))) (= (fun_app$ (fun_app$a (llist_all2$c ?v1) ?v3) ?v5) (fun_app$ (fun_app$a (llist_all2$c ?v2) ?v4) ?v6)))) :named a27))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_b_bool_fun_fun$) (?v2 A_a_bool_fun_fun$) (?v3 B_llist$) (?v4 A_llist$) (?v5 B_llist$) (?v6 A_llist$)) (=> (and (forall ((?v7 B$) (?v8 A$)) (=> (fun_app$h (fun_app$n ?v0 ?v7) ?v8) (forall ((?v9 B$) (?v10 A$)) (=> (fun_app$h (fun_app$n ?v0 ?v9) ?v10) (= (fun_app$f (fun_app$g ?v1 ?v7) ?v9) (fun_app$h (fun_app$i ?v2 ?v8) ?v10)))))) (and (fun_app$b (fun_app$m (llist_all2$b ?v0) ?v3) ?v4) (fun_app$b (fun_app$m (llist_all2$b ?v0) ?v5) ?v6))) (= (fun_app$ (fun_app$a (llist_all2$c ?v1) ?v3) ?v5) (fun_app$b (fun_app$c (llist_all2$a ?v2) ?v4) ?v6)))) :named a28))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_a_bool_fun_fun$) (?v2 A_a_bool_fun_fun$) (?v3 A_llist$) (?v4 A_llist$) (?v5 A_llist$) (?v6 A_llist$)) (=> (and (forall ((?v7 A$) (?v8 A$)) (=> (fun_app$h (fun_app$i ?v0 ?v7) ?v8) (forall ((?v9 A$) (?v10 A$)) (=> (fun_app$h (fun_app$i ?v0 ?v9) ?v10) (= (fun_app$h (fun_app$i ?v1 ?v7) ?v9) (fun_app$h (fun_app$i ?v2 ?v8) ?v10)))))) (and (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v3) ?v4) (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v5) ?v6))) (= (fun_app$b (fun_app$c (llist_all2$a ?v1) ?v3) ?v5) (fun_app$b (fun_app$c (llist_all2$a ?v2) ?v4) ?v6)))) :named a29))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_a_bool_fun_fun$) (?v2 B_b_bool_fun_fun$) (?v3 A_llist$) (?v4 B_llist$) (?v5 A_llist$) (?v6 B_llist$)) (=> (and (forall ((?v7 A$) (?v8 B$)) (=> (fun_app$f (fun_app$o ?v0 ?v7) ?v8) (forall ((?v9 A$) (?v10 B$)) (=> (fun_app$f (fun_app$o ?v0 ?v9) ?v10) (= (fun_app$h (fun_app$i ?v1 ?v7) ?v9) (fun_app$f (fun_app$g ?v2 ?v8) ?v10)))))) (and (fun_app$ (fun_app$j (llist_all2$ ?v0) ?v3) ?v4) (fun_app$ (fun_app$j (llist_all2$ ?v0) ?v5) ?v6))) (= (fun_app$b (fun_app$c (llist_all2$a ?v1) ?v3) ?v5) (fun_app$ (fun_app$a (llist_all2$c ?v2) ?v4) ?v6)))) :named a30))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$k (lmirror_aux$ ?v0) lNil$) ?v0) :pattern ((lmirror_aux$ ?v0)))) :named a31))
(assert (! (forall ((?v0 B_llist$)) (! (= (fun_app$l (lmirror_aux$a ?v0) lNil$a) ?v0) :pattern ((lmirror_aux$a ?v0)))) :named a32))
(assert (! (forall ((?v0 A_llist$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$k (lmirror_aux$ ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v1 (fun_app$k (lmirror_aux$ (lCons$ ?v1 ?v0)) ?v2))) :pattern ((fun_app$k (lmirror_aux$ ?v0) (lCons$ ?v1 ?v2))))) :named a33))
(assert (! (forall ((?v0 B_llist$) (?v1 B$) (?v2 B_llist$)) (! (= (fun_app$l (lmirror_aux$a ?v0) (lCons$a ?v1 ?v2)) (lCons$a ?v1 (fun_app$l (lmirror_aux$a (lCons$a ?v1 ?v0)) ?v2))) :pattern ((fun_app$l (lmirror_aux$a ?v0) (lCons$a ?v1 ?v2))))) :named a34))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (not (lnull$ (fun_app$k (lmirror_aux$ ?v0) ?v1))) (or (not (lnull$ ?v1)) (not (lnull$ ?v0))))) :named a35))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (= (not (lnull$a (fun_app$l (lmirror_aux$a ?v0) ?v1))) (or (not (lnull$a ?v1)) (not (lnull$a ?v0))))) :named a36))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (lnull$ (fun_app$k (lmirror_aux$ ?v0) ?v1)) (and (lnull$ ?v1) (lnull$ ?v0)))) :named a37))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (= (lnull$a (fun_app$l (lmirror_aux$a ?v0) ?v1)) (and (lnull$a ?v1) (lnull$a ?v0)))) :named a38))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B_llist$) (?v2 B_llist$) (?v3 B_llist$) (?v4 B_llist$)) (=> (and (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v1) ?v2) (=> (and (fun_app$ lfinite$a ?v1) (fun_app$ lfinite$a ?v2)) (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v3) ?v4))) (fun_app$ (fun_app$a (llist_all2$c ?v0) (lappend$ ?v1 ?v3)) (lappend$ ?v2 ?v4)))) :named a39))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B_llist$) (?v2 A_llist$) (?v3 B_llist$) (?v4 A_llist$)) (=> (and (fun_app$b (fun_app$m (llist_all2$b ?v0) ?v1) ?v2) (=> (and (fun_app$ lfinite$a ?v1) (fun_app$b lfinite$ ?v2)) (fun_app$b (fun_app$m (llist_all2$b ?v0) ?v3) ?v4))) (fun_app$b (fun_app$m (llist_all2$b ?v0) (lappend$ ?v1 ?v3)) (lappend$a ?v2 ?v4)))) :named a40))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_llist$) (?v4 A_llist$)) (=> (and (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v1) ?v2) (=> (and (fun_app$b lfinite$ ?v1) (fun_app$b lfinite$ ?v2)) (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v3) ?v4))) (fun_app$b (fun_app$c (llist_all2$a ?v0) (lappend$a ?v1 ?v3)) (lappend$a ?v2 ?v4)))) :named a41))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A_llist$) (?v2 B_llist$) (?v3 A_llist$) (?v4 B_llist$)) (=> (and (fun_app$ (fun_app$j (llist_all2$ ?v0) ?v1) ?v2) (=> (and (fun_app$b lfinite$ ?v1) (fun_app$ lfinite$a ?v2)) (fun_app$ (fun_app$j (llist_all2$ ?v0) ?v3) ?v4))) (fun_app$ (fun_app$j (llist_all2$ ?v0) (lappend$a ?v1 ?v3)) (lappend$ ?v2 ?v4)))) :named a42))
(assert (! (forall ((?v0 B_b_bool_fun_fun$)) (rel_fun$ (llist_all2$c ?v0) uud$ lfinite$a lfinite$a)) :named a43))
(assert (! (forall ((?v0 B_a_bool_fun_fun$)) (rel_fun$a (llist_all2$b ?v0) uud$ lfinite$a lfinite$)) :named a44))
(assert (! (forall ((?v0 A_a_bool_fun_fun$)) (rel_fun$b (llist_all2$a ?v0) uud$ lfinite$ lfinite$)) :named a45))
(assert (! (forall ((?v0 A_b_bool_fun_fun$)) (rel_fun$c (llist_all2$ ?v0) uud$ lfinite$ lfinite$a)) :named a46))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (or (not (lnull$ ?v0)) (not (lnull$ ?v1))) (not (lnull$ (fun_app$k (lmirror_aux$ ?v1) ?v0))))) :named a47))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (=> (or (not (lnull$a ?v0)) (not (lnull$a ?v1))) (not (lnull$a (fun_app$l (lmirror_aux$a ?v1) ?v0))))) :named a48))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (lnull$ ?v0) (lnull$ ?v1)) (lnull$ (fun_app$k (lmirror_aux$ ?v1) ?v0)))) :named a49))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (=> (and (lnull$a ?v0) (lnull$a ?v1)) (lnull$a (fun_app$l (lmirror_aux$a ?v1) ?v0)))) :named a50))
(assert (! (forall ((?v0 B$) (?v1 B_llist$) (?v2 B$) (?v3 B_llist$)) (= (= (lCons$a ?v0 ?v1) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a51))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a52))
(assert (! (forall ((?v0 B_b_bool_fun_fun$) (?v1 B$) (?v2 B_llist$) (?v3 B$) (?v4 B_llist$)) (! (= (fun_app$ (fun_app$a (llist_all2$c ?v0) (lCons$a ?v1 ?v2)) (lCons$a ?v3 ?v4)) (and (fun_app$f (fun_app$g ?v0 ?v1) ?v3) (fun_app$ (fun_app$a (llist_all2$c ?v0) ?v2) ?v4))) :pattern ((fun_app$ (fun_app$a (llist_all2$c ?v0) (lCons$a ?v1 ?v2)) (lCons$a ?v3 ?v4))))) :named a53))
(assert (! (forall ((?v0 B_a_bool_fun_fun$) (?v1 B$) (?v2 B_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$b (fun_app$m (llist_all2$b ?v0) (lCons$a ?v1 ?v2)) (lCons$ ?v3 ?v4)) (and (fun_app$h (fun_app$n ?v0 ?v1) ?v3) (fun_app$b (fun_app$m (llist_all2$b ?v0) ?v2) ?v4))) :pattern ((fun_app$b (fun_app$m (llist_all2$b ?v0) (lCons$a ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a54))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$b (fun_app$c (llist_all2$a ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v3 ?v4)) (and (fun_app$h (fun_app$i ?v0 ?v1) ?v3) (fun_app$b (fun_app$c (llist_all2$a ?v0) ?v2) ?v4))) :pattern ((fun_app$b (fun_app$c (llist_all2$a ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a55))
(assert (! (forall ((?v0 A_b_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 B$) (?v4 B_llist$)) (! (= (fun_app$ (fun_app$j (llist_all2$ ?v0) (lCons$ ?v1 ?v2)) (lCons$a ?v3 ?v4)) (and (fun_app$f (fun_app$o ?v0 ?v1) ?v3) (fun_app$ (fun_app$j (llist_all2$ ?v0) ?v2) ?v4))) :pattern ((fun_app$ (fun_app$j (llist_all2$ ?v0) (lCons$ ?v1 ?v2)) (lCons$a ?v3 ?v4))))) :named a56))
(check-sat)
;(get-unsat-core)
