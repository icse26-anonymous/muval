; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 92
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_set$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort A_llist_set$ 0)
(declare-sort A_set_a_fun$ 0)
(declare-sort A_a_llist_fun$ 0)
(declare-sort A_llist_a_fun$ 0)
(declare-sort A_a_bool_fun_fun$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-sort A_llist_llist_bool_fun$ 0)
(declare-sort A_llist_set_a_llist_fun$ 0)
(declare-sort A_set_a_fun_a_set_a_fun_fun$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun$ 0)
(declare-sort A_llist_llist_a_llist_llist_fun$ 0)
(declare-sort A_llist_llist_set_a_llist_llist_fun$ 0)
(declare-sort A_a_bool_fun_fun_a_a_bool_fun_fun_fun$ 0)
(declare-sort A_a_fun_a_set_a_fun_a_set_a_fun_fun_fun$ 0)
(declare-sort A_llist_set_a_llist_fun_a_set_a_fun_fun$ 0)
(declare-sort A_set_a_fun_a_llist_set_a_llist_fun_fun$ 0)
(declare-sort A_llist_llist_a_llist_llist_bool_fun_fun$ 0)
(declare-sort A_a_bool_fun_fun_a_llist_a_llist_bool_fun_fun_fun$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun_a_a_bool_fun_fun_fun$ 0)
(declare-sort A_llist_set_a_llist_fun_a_llist_set_a_llist_fun_fun$ 0)
(declare-sort A_a_llist_fun_a_set_a_fun_a_llist_set_a_llist_fun_fun_fun$ 0)
(declare-sort A_llist_a_fun_a_llist_set_a_llist_fun_a_set_a_fun_fun_fun$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun_a_llist_a_llist_bool_fun_fun_fun$ 0)
(declare-sort A_llist_a_llist_fun_a_llist_set_a_llist_fun_a_llist_set_a_llist_fun_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))
  (A_llist_llist$ (lNil$a) (lCons$a (lhd$a A_llist$) (ltl$a A_llist_llist$)))))
(declare-fun uu$ () A_llist_a_llist_fun$)
(declare-fun xs$ () A_llist$)
(declare-fun uua$ (A_llist$) A_llist_llist_a_llist_llist_fun$)
(declare-fun uub$ (A$) A_llist_a_llist_fun$)
(declare-fun uuc$ (A_llist_set$) A_llist_bool_fun$)
(declare-fun uud$ (A_set$) A_bool_fun$)
(declare-fun cont$ (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_fun$) Bool)
(declare-fun lSup$ () A_llist_set_a_llist_fun$)
(declare-fun lmap$ (A_a_fun$) A_llist_a_llist_fun$)
(declare-fun lset$ (A_llist_llist$) A_llist_set$)
(declare-fun chain$ (A_llist_a_llist_bool_fun_fun$ A_llist_set$) Bool)
(declare-fun lSup$a () A_llist_llist_set_a_llist_llist_fun$)
(declare-fun lmap$a (A_llist_a_fun$ A_llist_llist$) A_llist$)
(declare-fun lmap$b (A_a_llist_fun$ A_llist$) A_llist_llist$)
(declare-fun lmap$c (A_llist_a_llist_fun$ A_llist_llist$) A_llist_llist$)
(declare-fun lnull$ (A_llist_llist$) Bool)
(declare-fun lset$a (A_llist$) A_set$)
(declare-fun mcont$ (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_fun$) Bool)
(declare-fun chain$a (A_a_bool_fun_fun$ A_set$) Bool)
(declare-fun lnull$a (A_llist$) Bool)
(declare-fun mcont$a (A_llist_llist_set_a_llist_llist_fun$ A_llist_llist_a_llist_llist_bool_fun_fun$ A_llist_llist_set_a_llist_llist_fun$ A_llist_llist_a_llist_llist_bool_fun_fun$ A_llist_llist_a_llist_llist_fun$) Bool)
(declare-fun member$ (A_llist$ A_llist_set$) Bool)
(declare-fun collect$ (A_bool_fun$) A_set$)
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun img_lub$ (A_a_llist_fun$) A_llist_a_fun_a_llist_set_a_llist_fun_a_set_a_fun_fun_fun$)
(declare-fun img_ord$ (A_a_llist_fun$) A_llist_a_llist_bool_fun_fun_a_a_bool_fun_fun_fun$)
(declare-fun lappend$ (A_llist$) A_llist_a_llist_fun$)
(declare-fun lfinite$ (A_llist$) Bool)
(declare-fun lmember$ (A_llist$) A_llist_llist_bool_fun$)
(declare-fun lprefix$ () A_llist_a_llist_bool_fun_fun$)
(declare-fun member$a (A$ A_set$) Bool)
(declare-fun collect$a (A_llist_bool_fun$) A_llist_set$)
(declare-fun fun_app$a (A_llist_llist_a_llist_llist_fun$ A_llist_llist$) A_llist_llist$)
(declare-fun fun_app$b (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun fun_app$c (A_bool_fun$ A$) Bool)
(declare-fun fun_app$d (A_llist_a_llist_bool_fun_fun$ A_llist$) A_llist_bool_fun$)
(declare-fun fun_app$e (A_llist_llist_bool_fun$ A_llist_llist$) Bool)
(declare-fun fun_app$f (A_llist_llist_a_llist_llist_bool_fun_fun$ A_llist_llist$) A_llist_llist_bool_fun$)
(declare-fun fun_app$g (A_llist_set_a_llist_fun$ A_llist_set$) A_llist$)
(declare-fun fun_app$h (A_a_llist_fun$ A$) A_llist$)
(declare-fun fun_app$i (A_llist_a_fun$ A_llist$) A$)
(declare-fun fun_app$j (A_a_fun$ A$) A$)
(declare-fun fun_app$k (A_a_bool_fun_fun$ A$) A_bool_fun$)
(declare-fun fun_app$l (A_set_a_fun$ A_set$) A$)
(declare-fun fun_app$m (A_llist_a_llist_bool_fun_fun_a_a_bool_fun_fun_fun$ A_llist_a_llist_bool_fun_fun$) A_a_bool_fun_fun$)
(declare-fun fun_app$n (A_llist_set_a_llist_fun_a_set_a_fun_fun$ A_llist_set_a_llist_fun$) A_set_a_fun$)
(declare-fun fun_app$o (A_llist_a_fun_a_llist_set_a_llist_fun_a_set_a_fun_fun_fun$ A_llist_a_fun$) A_llist_set_a_llist_fun_a_set_a_fun_fun$)
(declare-fun fun_app$p (A_a_bool_fun_fun_a_llist_a_llist_bool_fun_fun_fun$ A_a_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun fun_app$q (A_set_a_fun_a_llist_set_a_llist_fun_fun$ A_set_a_fun$) A_llist_set_a_llist_fun$)
(declare-fun fun_app$r (A_a_llist_fun_a_set_a_fun_a_llist_set_a_llist_fun_fun_fun$ A_a_llist_fun$) A_set_a_fun_a_llist_set_a_llist_fun_fun$)
(declare-fun fun_app$s (A_a_bool_fun_fun_a_a_bool_fun_fun_fun$ A_a_bool_fun_fun$) A_a_bool_fun_fun$)
(declare-fun fun_app$t (A_set_a_fun_a_set_a_fun_fun$ A_set_a_fun$) A_set_a_fun$)
(declare-fun fun_app$u (A_a_fun_a_set_a_fun_a_set_a_fun_fun_fun$ A_a_fun$) A_set_a_fun_a_set_a_fun_fun$)
(declare-fun fun_app$v (A_llist_a_llist_bool_fun_fun_a_llist_a_llist_bool_fun_fun_fun$ A_llist_a_llist_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun fun_app$w (A_llist_set_a_llist_fun_a_llist_set_a_llist_fun_fun$ A_llist_set_a_llist_fun$) A_llist_set_a_llist_fun$)
(declare-fun fun_app$x (A_llist_a_llist_fun_a_llist_set_a_llist_fun_a_llist_set_a_llist_fun_fun_fun$ A_llist_a_llist_fun$) A_llist_set_a_llist_fun_a_llist_set_a_llist_fun_fun$)
(declare-fun img_lub$a (A_llist_a_fun$) A_a_llist_fun_a_set_a_fun_a_llist_set_a_llist_fun_fun_fun$)
(declare-fun img_lub$b (A_a_fun$) A_a_fun_a_set_a_fun_a_set_a_fun_fun_fun$)
(declare-fun img_lub$c (A_llist_a_llist_fun$) A_llist_a_llist_fun_a_llist_set_a_llist_fun_a_llist_set_a_llist_fun_fun_fun$)
(declare-fun img_ord$a (A_llist_a_fun$) A_a_bool_fun_fun_a_llist_a_llist_bool_fun_fun_fun$)
(declare-fun img_ord$b (A_a_fun$) A_a_bool_fun_fun_a_a_bool_fun_fun_fun$)
(declare-fun img_ord$c (A_llist_a_llist_fun$) A_llist_a_llist_bool_fun_fun_a_llist_a_llist_bool_fun_fun_fun$)
(declare-fun lappend$a (A_llist_llist$) A_llist_llist_a_llist_llist_fun$)
(declare-fun lfinite$a (A_llist_llist$) Bool)
(declare-fun lmember$a (A$) A_llist_bool_fun$)
(declare-fun lprefix$a () A_llist_llist_a_llist_llist_bool_fun_fun$)
(declare-fun admissible$ (A_llist_llist_set_a_llist_llist_fun$ A_llist_llist_a_llist_llist_bool_fun_fun$ A_llist_llist_bool_fun$) Bool)
(declare-fun pred_llist$ (A_llist_bool_fun$) A_llist_llist_bool_fun$)
(declare-fun admissible$a (A_llist_set_a_llist_fun$ A_llist_a_llist_bool_fun_fun$ A_llist_bool_fun$) Bool)
(declare-fun pred_llist$a (A_bool_fun$) A_llist_bool_fun$)
(declare-fun partial_function_definitions$ (A_llist_a_llist_bool_fun_fun$ A_llist_set_a_llist_fun$) Bool)
(declare-fun partial_function_definitions$a (A_a_bool_fun_fun$ A_set_a_fun$) Bool)
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ uu$ ?v0) (ltl$ ?v0)) :pattern ((fun_app$ uu$ ?v0)))) :named a0))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (! (= (fun_app$a (uua$ ?v0) ?v1) (lCons$a ?v0 ?v1)) :pattern ((fun_app$a (uua$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (fun_app$ (uub$ ?v0) ?v1) (lCons$ ?v0 ?v1)) :pattern ((fun_app$ (uub$ ?v0) ?v1)))) :named a2))
(assert (! (forall ((?v0 A_llist_set$) (?v1 A_llist$)) (! (= (fun_app$b (uuc$ ?v0) ?v1) (member$ ?v1 ?v0)) :pattern ((fun_app$b (uuc$ ?v0) ?v1)))) :named a3))
(assert (! (forall ((?v0 A_set$) (?v1 A$)) (! (= (fun_app$c (uud$ ?v0) ?v1) (member$a ?v1 ?v0)) :pattern ((fun_app$c (uud$ ?v0) ?v1)))) :named a4))
(assert (! (not (mcont$ lSup$ lprefix$ lSup$ lprefix$ (lappend$ xs$))) :named a5))
(assert (! (lfinite$ xs$) :named a6))
(assert (! (forall ((?v0 A_llist$)) (fun_app$b (fun_app$d lprefix$ ?v0) ?v0)) :named a7))
(assert (! (forall ((?v0 A_llist$)) (fun_app$b (fun_app$d lprefix$ ?v0) ?v0)) :named a8))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$) (?v2 A_llist_llist$)) (= (fun_app$a (lappend$a (fun_app$a (lappend$a ?v0) ?v1)) ?v2) (fun_app$a (lappend$a ?v0) (fun_app$a (lappend$a ?v1) ?v2)))) :named a9))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (= (fun_app$ (lappend$ (fun_app$ (lappend$ ?v0) ?v1)) ?v2) (fun_app$ (lappend$ ?v0) (fun_app$ (lappend$ ?v1) ?v2)))) :named a10))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (fun_app$b (fun_app$d lprefix$ ?v0) ?v1) (fun_app$b (fun_app$d lprefix$ ?v1) ?v0)) (= ?v0 ?v1))) :named a11))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (fun_app$b (fun_app$d lprefix$ ?v0) ?v1) (fun_app$b (fun_app$d lprefix$ ?v1) ?v0)) (= ?v0 ?v1))) :named a12))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (=> (and (fun_app$b (fun_app$d lprefix$ ?v0) ?v1) (fun_app$b (fun_app$d lprefix$ ?v2) ?v1)) (or (fun_app$b (fun_app$d lprefix$ ?v0) ?v2) (fun_app$b (fun_app$d lprefix$ ?v2) ?v0)))) :named a13))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (=> (and (fun_app$b (fun_app$d lprefix$ ?v0) ?v1) (fun_app$b (fun_app$d lprefix$ ?v1) ?v2)) (fun_app$b (fun_app$d lprefix$ ?v0) ?v2))) :named a14))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (=> (and (fun_app$b (fun_app$d lprefix$ ?v0) ?v1) (fun_app$b (fun_app$d lprefix$ ?v1) ?v2)) (fun_app$b (fun_app$d lprefix$ ?v0) ?v2))) :named a15))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$) (?v2 A_llist_llist$)) (=> (fun_app$e (fun_app$f lprefix$a ?v0) ?v1) (fun_app$e (fun_app$f lprefix$a (fun_app$a (lappend$a ?v2) ?v0)) (fun_app$a (lappend$a ?v2) ?v1)))) :named a16))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (=> (fun_app$b (fun_app$d lprefix$ ?v0) ?v1) (fun_app$b (fun_app$d lprefix$ (fun_app$ (lappend$ ?v2) ?v0)) (fun_app$ (lappend$ ?v2) ?v1)))) :named a17))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$)) (fun_app$e (fun_app$f lprefix$a ?v0) (fun_app$a (lappend$a ?v0) ?v1))) :named a18))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (fun_app$b (fun_app$d lprefix$ ?v0) (fun_app$ (lappend$ ?v0) ?v1))) :named a19))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$) (?v2 A_llist_llist$)) (= (fun_app$e (fun_app$f lprefix$a (fun_app$a (lappend$a ?v0) ?v1)) (fun_app$a (lappend$a ?v0) ?v2)) (=> (lfinite$a ?v0) (fun_app$e (fun_app$f lprefix$a ?v1) ?v2)))) :named a20))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist$)) (= (fun_app$b (fun_app$d lprefix$ (fun_app$ (lappend$ ?v0) ?v1)) (fun_app$ (lappend$ ?v0) ?v2)) (=> (lfinite$ ?v0) (fun_app$b (fun_app$d lprefix$ ?v1) ?v2)))) :named a21))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$)) (= (lfinite$a (fun_app$a (lappend$a ?v0) ?v1)) (and (lfinite$a ?v0) (lfinite$a ?v1)))) :named a22))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (lfinite$ (fun_app$ (lappend$ ?v0) ?v1)) (and (lfinite$ ?v0) (lfinite$ ?v1)))) :named a23))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$)) (! (=> (not (lfinite$a ?v0)) (= (fun_app$a (lappend$a ?v0) ?v1) ?v0)) :pattern ((fun_app$a (lappend$a ?v0) ?v1)))) :named a24))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (=> (not (lfinite$ ?v0)) (= (fun_app$ (lappend$ ?v0) ?v1) ?v0)) :pattern ((fun_app$ (lappend$ ?v0) ?v1)))) :named a25))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$)) (! (=> (not (lfinite$a ?v0)) (= (fun_app$e (fun_app$f lprefix$a ?v0) ?v1) (= ?v0 ?v1))) :pattern ((fun_app$e (fun_app$f lprefix$a ?v0) ?v1)))) :named a26))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (=> (not (lfinite$ ?v0)) (= (fun_app$b (fun_app$d lprefix$ ?v0) ?v1) (= ?v0 ?v1))) :pattern ((fun_app$b (fun_app$d lprefix$ ?v0) ?v1)))) :named a27))
(assert (! (forall ((?v0 A_a_fun$)) (mcont$ lSup$ lprefix$ lSup$ lprefix$ (lmap$ ?v0))) :named a28))
(assert (! (mcont$ lSup$ lprefix$ lSup$ lprefix$ uu$) :named a29))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist_set_a_llist_fun$) (?v3 A_llist_a_llist_bool_fun_fun$) (?v4 A_llist_a_llist_fun$) (?v5 A_llist$) (?v6 A_llist$)) (=> (and (mcont$ ?v0 ?v1 ?v2 ?v3 ?v4) (fun_app$b (fun_app$d ?v1 ?v5) ?v6)) (fun_app$b (fun_app$d ?v3 (fun_app$ ?v4 ?v5)) (fun_app$ ?v4 ?v6)))) :named a30))
(assert (! (forall ((?v0 A_llist$)) (mcont$a lSup$a lprefix$a lSup$a lprefix$a (uua$ ?v0))) :named a31))
(assert (! (forall ((?v0 A$)) (mcont$ lSup$ lprefix$ lSup$ lprefix$ (uub$ ?v0))) :named a32))
(assert (! (partial_function_definitions$ lprefix$ lSup$) :named a33))
(assert (! (forall ((?v0 A_llist_set$) (?v1 A_llist$)) (=> (and (chain$ lprefix$ ?v0) (forall ((?v2 A_llist$)) (=> (member$ ?v2 ?v0) (fun_app$b (fun_app$d lprefix$ ?v2) ?v1)))) (fun_app$b (fun_app$d lprefix$ (fun_app$g lSup$ ?v0)) ?v1))) :named a34))
(assert (! (forall ((?v0 A_llist_set$) (?v1 A_llist$)) (=> (and (chain$ lprefix$ ?v0) (forall ((?v2 A_llist$)) (=> (member$ ?v2 ?v0) (fun_app$b (fun_app$d lprefix$ ?v2) ?v1)))) (fun_app$b (fun_app$d lprefix$ (fun_app$g lSup$ ?v0)) ?v1))) :named a35))
(assert (! (forall ((?v0 A_llist_set$) (?v1 A_llist$)) (=> (and (chain$ lprefix$ ?v0) (member$ ?v1 ?v0)) (fun_app$b (fun_app$d lprefix$ ?v1) (fun_app$g lSup$ ?v0)))) :named a36))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (= (= (lCons$a ?v0 ?v1) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a37))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a38))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (! (= (fun_app$e (fun_app$f lprefix$a (lCons$a ?v0 ?v1)) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (fun_app$e (fun_app$f lprefix$a ?v1) ?v3))) :pattern ((fun_app$e (fun_app$f lprefix$a (lCons$a ?v0 ?v1)) (lCons$a ?v2 ?v3))))) :named a39))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (! (= (fun_app$b (fun_app$d lprefix$ (lCons$ ?v0 ?v1)) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (fun_app$b (fun_app$d lprefix$ ?v1) ?v3))) :pattern ((fun_app$b (fun_app$d lprefix$ (lCons$ ?v0 ?v1)) (lCons$ ?v2 ?v3))))) :named a40))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist_llist$)) (! (= (fun_app$a (lappend$a (lCons$a ?v0 ?v1)) ?v2) (lCons$a ?v0 (fun_app$a (lappend$a ?v1) ?v2))) :pattern ((fun_app$a (lappend$a (lCons$a ?v0 ?v1)) ?v2)))) :named a41))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A_llist$)) (! (= (fun_app$ (lappend$ (lCons$ ?v0 ?v1)) ?v2) (lCons$ ?v0 (fun_app$ (lappend$ ?v1) ?v2))) :pattern ((fun_app$ (lappend$ (lCons$ ?v0 ?v1)) ?v2)))) :named a42))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (! (= (lfinite$a (lCons$a ?v0 ?v1)) (lfinite$a ?v1)) :pattern ((lCons$a ?v0 ?v1)))) :named a43))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a44))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (! (= (lfinite$a (lCons$a ?v0 ?v1)) (lfinite$a ?v1)) :pattern ((lCons$a ?v0 ?v1)))) :named a45))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a46))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (ltl$ (fun_app$ (lmap$ ?v0) ?v1)) (fun_app$ (lmap$ ?v0) (ltl$ ?v1)))) :named a47))
(assert (! (forall ((?v0 A_llist_llist$)) (= (lfinite$a (ltl$a ?v0)) (lfinite$a ?v0))) :named a48))
(assert (! (forall ((?v0 A_llist$)) (= (lfinite$ (ltl$ ?v0)) (lfinite$ ?v0))) :named a49))
(assert (! (forall ((?v0 A_llist_a_fun$) (?v1 A_llist_llist$)) (= (lfinite$ (lmap$a ?v0 ?v1)) (lfinite$a ?v1))) :named a50))
(assert (! (forall ((?v0 A_a_llist_fun$) (?v1 A_llist$)) (= (lfinite$a (lmap$b ?v0 ?v1)) (lfinite$ ?v1))) :named a51))
(assert (! (forall ((?v0 A_llist_a_llist_fun$) (?v1 A_llist_llist$)) (= (lfinite$a (lmap$c ?v0 ?v1)) (lfinite$a ?v1))) :named a52))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (lfinite$ (fun_app$ (lmap$ ?v0) ?v1)) (lfinite$ ?v1))) :named a53))
(assert (! (forall ((?v0 A_a_llist_fun$) (?v1 A$) (?v2 A_llist$)) (! (= (lmap$b ?v0 (lCons$ ?v1 ?v2)) (lCons$a (fun_app$h ?v0 ?v1) (lmap$b ?v0 ?v2))) :pattern ((lmap$b ?v0 (lCons$ ?v1 ?v2))))) :named a54))
(assert (! (forall ((?v0 A_llist_a_fun$) (?v1 A_llist$) (?v2 A_llist_llist$)) (! (= (lmap$a ?v0 (lCons$a ?v1 ?v2)) (lCons$ (fun_app$i ?v0 ?v1) (lmap$a ?v0 ?v2))) :pattern ((lmap$a ?v0 (lCons$a ?v1 ?v2))))) :named a55))
(assert (! (forall ((?v0 A_llist_a_llist_fun$) (?v1 A_llist$) (?v2 A_llist_llist$)) (! (= (lmap$c ?v0 (lCons$a ?v1 ?v2)) (lCons$a (fun_app$ ?v0 ?v1) (lmap$c ?v0 ?v2))) :pattern ((lmap$c ?v0 (lCons$a ?v1 ?v2))))) :named a56))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$ (lmap$ ?v0) (lCons$ ?v1 ?v2)) (lCons$ (fun_app$j ?v0 ?v1) (fun_app$ (lmap$ ?v0) ?v2))) :pattern ((fun_app$ (lmap$ ?v0) (lCons$ ?v1 ?v2))))) :named a57))
(assert (! (forall ((?v0 A_llist_a_fun$) (?v1 A_llist_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lmap$a ?v0 ?v1) (lCons$ ?v2 ?v3)) (exists ((?v4 A_llist$) (?v5 A_llist_llist$)) (and (= ?v1 (lCons$a ?v4 ?v5)) (and (= ?v2 (fun_app$i ?v0 ?v4)) (= ?v3 (lmap$a ?v0 ?v5))))))) :named a58))
(assert (! (forall ((?v0 A_a_llist_fun$) (?v1 A_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (= (= (lmap$b ?v0 ?v1) (lCons$a ?v2 ?v3)) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v1 (lCons$ ?v4 ?v5)) (and (= ?v2 (fun_app$h ?v0 ?v4)) (= ?v3 (lmap$b ?v0 ?v5))))))) :named a59))
(assert (! (forall ((?v0 A_llist_a_llist_fun$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (= (= (lmap$c ?v0 ?v1) (lCons$a ?v2 ?v3)) (exists ((?v4 A_llist$) (?v5 A_llist_llist$)) (and (= ?v1 (lCons$a ?v4 ?v5)) (and (= ?v2 (fun_app$ ?v0 ?v4)) (= ?v3 (lmap$c ?v0 ?v5))))))) :named a60))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (fun_app$ (lmap$ ?v0) ?v1) (lCons$ ?v2 ?v3)) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v1 (lCons$ ?v4 ?v5)) (and (= ?v2 (fun_app$j ?v0 ?v4)) (= ?v3 (fun_app$ (lmap$ ?v0) ?v5))))))) :named a61))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (! (= (ltl$a (lCons$a ?v0 ?v1)) ?v1) :pattern ((lCons$a ?v0 ?v1)))) :named a62))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (ltl$ (lCons$ ?v0 ?v1)) ?v1) :pattern ((lCons$ ?v0 ?v1)))) :named a63))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist$)) (=> (lfinite$a ?v0) (lfinite$a (lCons$a ?v1 ?v0)))) :named a64))
(assert (! (forall ((?v0 A_llist$) (?v1 A$)) (=> (lfinite$ ?v0) (lfinite$ (lCons$ ?v1 ?v0)))) :named a65))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$) (?v2 A_llist$)) (=> (fun_app$e (fun_app$f lprefix$a ?v0) ?v1) (fun_app$e (fun_app$f lprefix$a (lCons$a ?v2 ?v0)) (lCons$a ?v2 ?v1)))) :named a66))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A$)) (=> (fun_app$b (fun_app$d lprefix$ ?v0) ?v1) (fun_app$b (fun_app$d lprefix$ (lCons$ ?v2 ?v0)) (lCons$ ?v2 ?v1)))) :named a67))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist_llist$)) (= (fun_app$e (fun_app$f lprefix$a (lCons$a ?v0 ?v1)) ?v2) (exists ((?v3 A_llist_llist$)) (and (= ?v2 (lCons$a ?v0 ?v3)) (fun_app$e (fun_app$f lprefix$a ?v1) ?v3))))) :named a68))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A_llist$)) (= (fun_app$b (fun_app$d lprefix$ (lCons$ ?v0 ?v1)) ?v2) (exists ((?v3 A_llist$)) (and (= ?v2 (lCons$ ?v0 ?v3)) (fun_app$b (fun_app$d lprefix$ ?v1) ?v3))))) :named a69))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (fun_app$b (fun_app$d lprefix$ ?v0) ?v1) (fun_app$b (fun_app$d lprefix$ (ltl$ ?v0)) (ltl$ ?v1)))) :named a70))
(assert (! (forall ((?v0 A_a_llist_fun$) (?v1 A_llist$) (?v2 A_llist$)) (= (lmap$b ?v0 (fun_app$ (lappend$ ?v1) ?v2)) (fun_app$a (lappend$a (lmap$b ?v0 ?v1)) (lmap$b ?v0 ?v2)))) :named a71))
(assert (! (forall ((?v0 A_llist_a_fun$) (?v1 A_llist_llist$) (?v2 A_llist_llist$)) (= (lmap$a ?v0 (fun_app$a (lappend$a ?v1) ?v2)) (fun_app$ (lappend$ (lmap$a ?v0 ?v1)) (lmap$a ?v0 ?v2)))) :named a72))
(assert (! (forall ((?v0 A_llist_a_llist_fun$) (?v1 A_llist_llist$) (?v2 A_llist_llist$)) (= (lmap$c ?v0 (fun_app$a (lappend$a ?v1) ?v2)) (fun_app$a (lappend$a (lmap$c ?v0 ?v1)) (lmap$c ?v0 ?v2)))) :named a73))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$) (?v2 A_llist$)) (= (fun_app$ (lmap$ ?v0) (fun_app$ (lappend$ ?v1) ?v2)) (fun_app$ (lappend$ (fun_app$ (lmap$ ?v0) ?v1)) (fun_app$ (lmap$ ?v0) ?v2)))) :named a74))
(assert (! (forall ((?v0 A_llist_set$) (?v1 A_llist$)) (=> (and (chain$ lprefix$ ?v0) (member$ ?v1 ?v0)) (fun_app$b (fun_app$d lprefix$ ?v1) (fun_app$g lSup$ ?v0)))) :named a75))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_set_a_fun$) (?v2 A_set$) (?v3 A$)) (=> (and (partial_function_definitions$a ?v0 ?v1) (and (chain$a ?v0 ?v2) (forall ((?v4 A$)) (=> (member$a ?v4 ?v2) (fun_app$c (fun_app$k ?v0 ?v4) ?v3))))) (fun_app$c (fun_app$k ?v0 (fun_app$l ?v1 ?v2)) ?v3))) :named a76))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_set_a_llist_fun$) (?v2 A_llist_set$) (?v3 A_llist$)) (=> (and (partial_function_definitions$ ?v0 ?v1) (and (chain$ ?v0 ?v2) (forall ((?v4 A_llist$)) (=> (member$ ?v4 ?v2) (fun_app$b (fun_app$d ?v0 ?v4) ?v3))))) (fun_app$b (fun_app$d ?v0 (fun_app$g ?v1 ?v2)) ?v3))) :named a77))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_set_a_fun$) (?v2 A_set$) (?v3 A$)) (=> (and (partial_function_definitions$a ?v0 ?v1) (and (chain$a ?v0 ?v2) (member$a ?v3 ?v2))) (fun_app$c (fun_app$k ?v0 ?v3) (fun_app$l ?v1 ?v2)))) :named a78))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_set_a_llist_fun$) (?v2 A_llist_set$) (?v3 A_llist$)) (=> (and (partial_function_definitions$ ?v0 ?v1) (and (chain$ ?v0 ?v2) (member$ ?v3 ?v2))) (fun_app$b (fun_app$d ?v0 ?v3) (fun_app$g ?v1 ?v2)))) :named a79))
(assert (! (forall ((?v0 A_llist_bool_fun$) (?v1 A_llist$) (?v2 A_llist_llist$)) (! (= (fun_app$e (pred_llist$ ?v0) (lCons$a ?v1 ?v2)) (and (fun_app$b ?v0 ?v1) (fun_app$e (pred_llist$ ?v0) ?v2))) :pattern ((fun_app$e (pred_llist$ ?v0) (lCons$a ?v1 ?v2))))) :named a80))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$b (pred_llist$a ?v0) (lCons$ ?v1 ?v2)) (and (fun_app$c ?v0 ?v1) (fun_app$b (pred_llist$a ?v0) ?v2))) :pattern ((fun_app$b (pred_llist$a ?v0) (lCons$ ?v1 ?v2))))) :named a81))
(assert (! (cont$ lSup$ lprefix$ lSup$ lprefix$ uu$) :named a82))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_set_a_fun$) (?v2 A$) (?v3 A$)) (=> (and (partial_function_definitions$a ?v0 ?v1) (and (fun_app$c (fun_app$k ?v0 ?v2) ?v3) (fun_app$c (fun_app$k ?v0 ?v3) ?v2))) (= ?v2 ?v3))) :named a83))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_set_a_llist_fun$) (?v2 A_llist$) (?v3 A_llist$)) (=> (and (partial_function_definitions$ ?v0 ?v1) (and (fun_app$b (fun_app$d ?v0 ?v2) ?v3) (fun_app$b (fun_app$d ?v0 ?v3) ?v2))) (= ?v2 ?v3))) :named a84))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_bool_fun$)) (=> (forall ((?v2 A$)) (= (fun_app$c ?v0 ?v2) (fun_app$c ?v1 ?v2))) (= (collect$ ?v0) (collect$ ?v1)))) :named a85))
(assert (! (forall ((?v0 A_llist_bool_fun$) (?v1 A_llist_bool_fun$)) (=> (forall ((?v2 A_llist$)) (= (fun_app$b ?v0 ?v2) (fun_app$b ?v1 ?v2))) (= (collect$a ?v0) (collect$a ?v1)))) :named a86))
(assert (! (forall ((?v0 A_llist_set$)) (= (collect$a (uuc$ ?v0)) ?v0)) :named a87))
(assert (! (forall ((?v0 A_set$)) (= (collect$ (uud$ ?v0)) ?v0)) :named a88))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_bool_fun$)) (= (member$ ?v0 (collect$a ?v1)) (fun_app$b ?v1 ?v0))) :named a89))
(assert (! (forall ((?v0 A$) (?v1 A_bool_fun$)) (= (member$a ?v0 (collect$ ?v1)) (fun_app$c ?v1 ?v0))) :named a90))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_set_a_fun$) (?v2 A$) (?v3 A$) (?v4 A$)) (=> (and (partial_function_definitions$a ?v0 ?v1) (and (fun_app$c (fun_app$k ?v0 ?v2) ?v3) (fun_app$c (fun_app$k ?v0 ?v3) ?v4))) (fun_app$c (fun_app$k ?v0 ?v2) ?v4))) :named a91))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_set_a_llist_fun$) (?v2 A_llist$) (?v3 A_llist$) (?v4 A_llist$)) (=> (and (partial_function_definitions$ ?v0 ?v1) (and (fun_app$b (fun_app$d ?v0 ?v2) ?v3) (fun_app$b (fun_app$d ?v0 ?v3) ?v4))) (fun_app$b (fun_app$d ?v0 ?v2) ?v4))) :named a92))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_set_a_fun$) (?v2 A$)) (=> (partial_function_definitions$a ?v0 ?v1) (fun_app$c (fun_app$k ?v0 ?v2) ?v2))) :named a93))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_set_a_llist_fun$) (?v2 A_llist$)) (=> (partial_function_definitions$ ?v0 ?v1) (fun_app$b (fun_app$d ?v0 ?v2) ?v2))) :named a94))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_set$)) (= (chain$a ?v0 ?v1) (forall ((?v2 A$)) (=> (member$a ?v2 ?v1) (forall ((?v3 A$)) (=> (member$a ?v3 ?v1) (or (fun_app$c (fun_app$k ?v0 ?v2) ?v3) (fun_app$c (fun_app$k ?v0 ?v3) ?v2)))))))) :named a95))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_set$)) (= (chain$ ?v0 ?v1) (forall ((?v2 A_llist$)) (=> (member$ ?v2 ?v1) (forall ((?v3 A_llist$)) (=> (member$ ?v3 ?v1) (or (fun_app$b (fun_app$d ?v0 ?v2) ?v3) (fun_app$b (fun_app$d ?v0 ?v3) ?v2)))))))) :named a96))
(assert (! (forall ((?v0 A_set$) (?v1 A_a_bool_fun_fun$)) (=> (forall ((?v2 A$) (?v3 A$)) (=> (and (member$a ?v2 ?v0) (member$a ?v3 ?v0)) (or (fun_app$c (fun_app$k ?v1 ?v2) ?v3) (fun_app$c (fun_app$k ?v1 ?v3) ?v2)))) (chain$a ?v1 ?v0))) :named a97))
(assert (! (forall ((?v0 A_llist_set$) (?v1 A_llist_a_llist_bool_fun_fun$)) (=> (forall ((?v2 A_llist$) (?v3 A_llist$)) (=> (and (member$ ?v2 ?v0) (member$ ?v3 ?v0)) (or (fun_app$b (fun_app$d ?v1 ?v2) ?v3) (fun_app$b (fun_app$d ?v1 ?v3) ?v2)))) (chain$ ?v1 ?v0))) :named a98))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_set$) (?v2 A$) (?v3 A$)) (=> (and (chain$a ?v0 ?v1) (and (member$a ?v2 ?v1) (and (member$a ?v3 ?v1) (and (=> (fun_app$c (fun_app$k ?v0 ?v2) ?v3) false) (=> (fun_app$c (fun_app$k ?v0 ?v3) ?v2) false))))) false)) :named a99))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_set$) (?v2 A_llist$) (?v3 A_llist$)) (=> (and (chain$ ?v0 ?v1) (and (member$ ?v2 ?v1) (and (member$ ?v3 ?v1) (and (=> (fun_app$b (fun_app$d ?v0 ?v2) ?v3) false) (=> (fun_app$b (fun_app$d ?v0 ?v3) ?v2) false))))) false)) :named a100))
(assert (! (forall ((?v0 A_llist_set_a_llist_fun$) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist_set_a_llist_fun$) (?v3 A_llist_a_llist_bool_fun_fun$) (?v4 A_llist_a_llist_fun$)) (=> (mcont$ ?v0 ?v1 ?v2 ?v3 ?v4) (cont$ ?v0 ?v1 ?v2 ?v3 ?v4))) :named a101))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_set$) (?v2 A$) (?v3 A$)) (=> (and (chain$a ?v0 ?v1) (and (member$a ?v2 ?v1) (member$a ?v3 ?v1))) (or (fun_app$c (fun_app$k ?v0 ?v2) ?v3) (fun_app$c (fun_app$k ?v0 ?v3) ?v2)))) :named a102))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_set$) (?v2 A_llist$) (?v3 A_llist$)) (=> (and (chain$ ?v0 ?v1) (and (member$ ?v2 ?v1) (member$ ?v3 ?v1))) (or (fun_app$b (fun_app$d ?v0 ?v2) ?v3) (fun_app$b (fun_app$d ?v0 ?v3) ?v2)))) :named a103))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist_llist$)) (! (= (fun_app$e (lmember$ ?v0) (lCons$a ?v1 ?v2)) (or (= ?v0 ?v1) (fun_app$e (lmember$ ?v0) ?v2))) :pattern ((fun_app$e (lmember$ ?v0) (lCons$a ?v1 ?v2))))) :named a104))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$b (lmember$a ?v0) (lCons$ ?v1 ?v2)) (or (= ?v0 ?v1) (fun_app$b (lmember$a ?v0) ?v2))) :pattern ((fun_app$b (lmember$a ?v0) (lCons$ ?v1 ?v2))))) :named a105))
(assert (! (forall ((?v0 A_llist_llist_bool_fun$) (?v1 A_llist_llist$)) (=> (and (admissible$ lSup$a lprefix$a ?v0) (exists ((?v2 A_llist_llist$)) (and (fun_app$e (fun_app$f lprefix$a ?v2) ?v1) (and (lfinite$a ?v2) (forall ((?v3 A_llist_llist$)) (=> (and (fun_app$e (fun_app$f lprefix$a ?v2) ?v3) (and (fun_app$e (fun_app$f lprefix$a ?v3) ?v1) (lfinite$a ?v3))) (fun_app$e ?v0 ?v3))))))) (fun_app$e ?v0 ?v1))) :named a106))
(assert (! (forall ((?v0 A_llist_bool_fun$) (?v1 A_llist$)) (=> (and (admissible$a lSup$ lprefix$ ?v0) (exists ((?v2 A_llist$)) (and (fun_app$b (fun_app$d lprefix$ ?v2) ?v1) (and (lfinite$ ?v2) (forall ((?v3 A_llist$)) (=> (and (fun_app$b (fun_app$d lprefix$ ?v2) ?v3) (and (fun_app$b (fun_app$d lprefix$ ?v3) ?v1) (lfinite$ ?v3))) (fun_app$b ?v0 ?v3))))))) (fun_app$b ?v0 ?v1))) :named a107))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (=> (member$ ?v0 (lset$ ?v1)) (exists ((?v2 A_llist_llist$) (?v3 A_llist_llist$)) (and (= ?v1 (fun_app$a (lappend$a ?v2) (lCons$a ?v0 ?v3))) (and (lfinite$a ?v2) (not (member$ ?v0 (lset$ ?v2)))))))) :named a108))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (=> (member$a ?v0 (lset$a ?v1)) (exists ((?v2 A_llist$) (?v3 A_llist$)) (and (= ?v1 (fun_app$ (lappend$ ?v2) (lCons$ ?v0 ?v3))) (and (lfinite$ ?v2) (not (member$a ?v0 (lset$a ?v2)))))))) :named a109))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (=> (member$ ?v0 (lset$ ?v1)) (exists ((?v2 A_llist_llist$) (?v3 A_llist_llist$)) (and (= ?v1 (fun_app$a (lappend$a ?v2) (lCons$a ?v0 ?v3))) (lfinite$a ?v2))))) :named a110))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (=> (member$a ?v0 (lset$a ?v1)) (exists ((?v2 A_llist$) (?v3 A_llist$)) (and (= ?v1 (fun_app$ (lappend$ ?v2) (lCons$ ?v0 ?v3))) (lfinite$ ?v2))))) :named a111))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$)) (= (ltl$a (fun_app$a (lappend$a ?v0) ?v1)) (ite (lnull$ ?v0) (ltl$a ?v1) (fun_app$a (lappend$a (ltl$a ?v0)) ?v1)))) :named a112))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (ltl$ (fun_app$ (lappend$ ?v0) ?v1)) (ite (lnull$a ?v0) (ltl$ ?v1) (fun_app$ (lappend$ (ltl$ ?v0)) ?v1)))) :named a113))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_set_a_llist_fun$) (?v2 A_a_llist_fun$) (?v3 A_llist_a_fun$)) (=> (and (partial_function_definitions$ ?v0 ?v1) (and (forall ((?v4 A$) (?v5 A$)) (=> (= (fun_app$h ?v2 ?v4) (fun_app$h ?v2 ?v5)) (= ?v4 ?v5))) (forall ((?v4 A_llist$)) (= (fun_app$h ?v2 (fun_app$i ?v3 ?v4)) ?v4)))) (partial_function_definitions$a (fun_app$m (img_ord$ ?v2) ?v0) (fun_app$n (fun_app$o (img_lub$ ?v2) ?v3) ?v1)))) :named a114))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_set_a_fun$) (?v2 A_llist_a_fun$) (?v3 A_a_llist_fun$)) (=> (and (partial_function_definitions$a ?v0 ?v1) (and (forall ((?v4 A_llist$) (?v5 A_llist$)) (=> (= (fun_app$i ?v2 ?v4) (fun_app$i ?v2 ?v5)) (= ?v4 ?v5))) (forall ((?v4 A$)) (= (fun_app$i ?v2 (fun_app$h ?v3 ?v4)) ?v4)))) (partial_function_definitions$ (fun_app$p (img_ord$a ?v2) ?v0) (fun_app$q (fun_app$r (img_lub$a ?v2) ?v3) ?v1)))) :named a115))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_set_a_fun$) (?v2 A_a_fun$) (?v3 A_a_fun$)) (=> (and (partial_function_definitions$a ?v0 ?v1) (and (forall ((?v4 A$) (?v5 A$)) (=> (= (fun_app$j ?v2 ?v4) (fun_app$j ?v2 ?v5)) (= ?v4 ?v5))) (forall ((?v4 A$)) (= (fun_app$j ?v2 (fun_app$j ?v3 ?v4)) ?v4)))) (partial_function_definitions$a (fun_app$s (img_ord$b ?v2) ?v0) (fun_app$t (fun_app$u (img_lub$b ?v2) ?v3) ?v1)))) :named a116))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_set_a_llist_fun$) (?v2 A_llist_a_llist_fun$) (?v3 A_llist_a_llist_fun$)) (=> (and (partial_function_definitions$ ?v0 ?v1) (and (forall ((?v4 A_llist$) (?v5 A_llist$)) (=> (= (fun_app$ ?v2 ?v4) (fun_app$ ?v2 ?v5)) (= ?v4 ?v5))) (forall ((?v4 A_llist$)) (= (fun_app$ ?v2 (fun_app$ ?v3 ?v4)) ?v4)))) (partial_function_definitions$ (fun_app$v (img_ord$c ?v2) ?v0) (fun_app$w (fun_app$x (img_lub$c ?v2) ?v3) ?v1)))) :named a117))
(assert (! (forall ((?v0 A_llist_llist$)) (=> (and (lfinite$a ?v0) (and (=> (= ?v0 lNil$a) false) (forall ((?v1 A_llist_llist$) (?v2 A_llist$)) (=> (and (= ?v0 (lCons$a ?v2 ?v1)) (lfinite$a ?v1)) false)))) false)) :named a118))
(assert (! (forall ((?v0 A_llist$)) (=> (and (lfinite$ ?v0) (and (=> (= ?v0 lNil$) false) (forall ((?v1 A_llist$) (?v2 A$)) (=> (and (= ?v0 (lCons$ ?v2 ?v1)) (lfinite$ ?v1)) false)))) false)) :named a119))
(assert (! (forall ((?v0 A_llist_llist$)) (= (lfinite$a ?v0) (or (= ?v0 lNil$a) (exists ((?v1 A_llist_llist$) (?v2 A_llist$)) (and (= ?v0 (lCons$a ?v2 ?v1)) (lfinite$a ?v1)))))) :named a120))
(assert (! (forall ((?v0 A_llist$)) (= (lfinite$ ?v0) (or (= ?v0 lNil$) (exists ((?v1 A_llist$) (?v2 A$)) (and (= ?v0 (lCons$ ?v2 ?v1)) (lfinite$ ?v1)))))) :named a121))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$b (fun_app$d lprefix$ lNil$) ?v0) true) :pattern ((fun_app$b (fun_app$d lprefix$ lNil$) ?v0)))) :named a122))
(assert (! (forall ((?v0 A_llist_set$)) (= (lnull$a (fun_app$g lSup$ ?v0)) (forall ((?v1 A_llist$)) (=> (member$ ?v1 ?v0) (lnull$a ?v1))))) :named a123))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (lnull$a (fun_app$ (lmap$ ?v0) ?v1)) (lnull$a ?v1))) :named a124))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$)) (= (lnull$ (fun_app$a (lappend$a ?v0) ?v1)) (and (lnull$ ?v0) (lnull$ ?v1)))) :named a125))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (lnull$a (fun_app$ (lappend$ ?v0) ?v1)) (and (lnull$a ?v0) (lnull$a ?v1)))) :named a126))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$)) (= (not (lnull$ (fun_app$a (lappend$a ?v0) ?v1))) (or (not (lnull$ ?v0)) (not (lnull$ ?v1))))) :named a127))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (not (lnull$a (fun_app$ (lappend$ ?v0) ?v1))) (or (not (lnull$a ?v0)) (not (lnull$a ?v1))))) :named a128))
(assert (! (forall ((?v0 A_llist_llist$)) (! (= (fun_app$a (lappend$a lNil$a) ?v0) ?v0) :pattern ((fun_app$a (lappend$a lNil$a) ?v0)))) :named a129))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ (lappend$ lNil$) ?v0) ?v0) :pattern ((fun_app$ (lappend$ lNil$) ?v0)))) :named a130))
(assert (! (forall ((?v0 A_llist_llist$)) (! (= (fun_app$a (lappend$a ?v0) lNil$a) ?v0) :pattern ((lappend$a ?v0)))) :named a131))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$ (lappend$ ?v0) lNil$) ?v0) :pattern ((lappend$ ?v0)))) :named a132))
(assert (! (= (lfinite$a lNil$a) true) :named a133))
(assert (! (= (lfinite$ lNil$) true) :named a134))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$b (fun_app$d lprefix$ ?v0) lNil$) (lnull$a ?v0)) :pattern ((fun_app$d lprefix$ ?v0)))) :named a135))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$)) (! (=> (and (lnull$ ?v0) (lnull$ ?v1)) (= (fun_app$a (lappend$a ?v0) ?v1) lNil$a)) :pattern ((fun_app$a (lappend$a ?v0) ?v1)))) :named a136))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (! (=> (and (lnull$a ?v0) (lnull$a ?v1)) (= (fun_app$ (lappend$ ?v0) ?v1) lNil$)) :pattern ((fun_app$ (lappend$ ?v0) ?v1)))) :named a137))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (= (member$ ?v0 (lset$ ?v1)) (fun_app$e (lmember$ ?v0) ?v1))) :named a138))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (= (member$a ?v0 (lset$a ?v1)) (fun_app$b (lmember$a ?v0) ?v1))) :named a139))
(assert (! (forall ((?v0 A_llist$)) (! (= (lnull$a ?v0) (= ?v0 lNil$)) :pattern ((lnull$a ?v0)))) :named a140))
(assert (! (forall ((?v0 A_llist$)) (! (= (fun_app$e (lmember$ ?v0) lNil$a) false) :pattern ((lmember$ ?v0)))) :named a141))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$b (lmember$a ?v0) lNil$) false) :pattern ((lmember$a ?v0)))) :named a142))
(check-sat)
;(get-unsat-core)
