; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 553
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort A_a_prod_set$ 0)
(declare-sort Bool_bool_fun$ 0)
(declare-sort A_a_a_prod_fun$ 0)
(declare-sort A_a_bool_fun_fun$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort A_a_prod_bool_fun$ 0)
(declare-sort Bool_a_a_prod_fun$ 0)
(declare-sort A_a_a_a_prod_fun_fun$ 0)
(declare-sort A_llist_a_a_prod_fun$ 0)
(declare-sort A_a_prod_a_a_prod_fun$ 0)
(declare-sort A_llist_a_llist_prod_set$ 0)
(declare-sort A_a_llist_a_llist_prod_fun$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun$ 0)
(declare-sort A_llist_a_llist_prod_bool_fun$ 0)
(declare-sort Bool_a_llist_a_llist_prod_fun$ 0)
(declare-sort A_a_a_llist_a_llist_prod_fun_fun$ 0)
(declare-sort A_llist_a_llist_a_a_prod_fun_fun$ 0)
(declare-sort A_llist_a_llist_a_llist_prod_fun$ 0)
(declare-sort A_a_prod_a_llist_a_llist_prod_fun$ 0)
(declare-sort A_llist_a_llist_prod_a_a_prod_fun$ 0)
(declare-sort A_a_bool_fun_fun_a_a_prod_bool_fun_fun$ 0)
(declare-sort A_llist_a_llist_a_llist_a_llist_prod_fun_fun$ 0)
(declare-sort A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ 0)
(declare-sort A_a_a_a_prod_fun_fun_a_a_prod_a_a_prod_fun_fun$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun_a_llist_a_llist_prod_bool_fun_fun$ 0)
(declare-sort A_a_a_llist_a_llist_prod_fun_fun_a_a_prod_a_llist_a_llist_prod_fun_fun$ 0)
(declare-sort A_llist_a_llist_a_a_prod_fun_fun_a_llist_a_llist_prod_a_a_prod_fun_fun$ 0)
(declare-sort A_llist_a_llist_a_llist_a_llist_prod_fun_fun_a_llist_a_llist_prod_a_llist_a_llist_prod_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-datatypes () ((A_llist_a_llist_prod$ (pair$ (fst$ A_llist$) (snd$ A_llist$)))
  (A_a_prod$ (pair$a (fst$a A$) (snd$a A$)))))
(declare-fun r$ () A_a_bool_fun_fun$)
(declare-fun uu$ (Bool A_llist_a_llist_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun uua$ (Bool A_a_bool_fun_fun$) A_a_bool_fun_fun$)
(declare-fun uub$ (A_a_bool_fun_fun$ A_a_a_a_prod_fun_fun$) A_a_bool_fun_fun$)
(declare-fun uuc$ (A_llist_a_llist_bool_fun_fun$ A_a_a_llist_a_llist_prod_fun_fun$) A_a_bool_fun_fun$)
(declare-fun uud$ (A_a_bool_fun_fun$ A_llist_a_llist_a_a_prod_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun uue$ (A_llist_a_llist_bool_fun_fun$ A_llist_a_llist_a_llist_a_llist_prod_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun uuf$ (A_a_a_a_prod_fun_fun$ A_a_a_a_prod_fun_fun$) A_a_a_a_prod_fun_fun$)
(declare-fun uug$ (A_a_a_a_prod_fun_fun$ A_llist_a_llist_a_a_prod_fun_fun$) A_llist_a_llist_a_a_prod_fun_fun$)
(declare-fun uuh$ (A_llist_a_llist_a_a_prod_fun_fun$ A_a_a_llist_a_llist_prod_fun_fun$) A_a_a_a_prod_fun_fun$)
(declare-fun uui$ (A_a_a_llist_a_llist_prod_fun_fun$ A_a_a_a_prod_fun_fun$) A_a_a_llist_a_llist_prod_fun_fun$)
(declare-fun uuj$ (A_llist_a_llist_a_a_prod_fun_fun$ A_llist_a_llist_a_llist_a_llist_prod_fun_fun$) A_llist_a_llist_a_a_prod_fun_fun$)
(declare-fun uuk$ (A_a_a_llist_a_llist_prod_fun_fun$ A_llist_a_llist_a_a_prod_fun_fun$) A_llist_a_llist_a_llist_a_llist_prod_fun_fun$)
(declare-fun uul$ (Bool_bool_fun$ A_a_bool_fun_fun$) A_a_bool_fun_fun$)
(declare-fun uum$ (Bool_bool_fun$ A_llist_a_llist_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun uun$ (Bool_a_a_prod_fun$ A_a_bool_fun_fun$) A_a_a_a_prod_fun_fun$)
(declare-fun uuo$ (A_a_prod_bool_fun$ A_a_a_a_prod_fun_fun$) A_a_bool_fun_fun$)
(declare-fun uup$ (Bool_a_a_prod_fun$ A_llist_a_llist_bool_fun_fun$) A_llist_a_llist_a_a_prod_fun_fun$)
(declare-fun uuq$ (Bool_a_llist_a_llist_prod_fun$ A_a_bool_fun_fun$) A_a_a_llist_a_llist_prod_fun_fun$)
(declare-fun uur$ (A_a_prod_a_a_prod_fun$ A_a_a_a_prod_fun_fun$) A_a_a_a_prod_fun_fun$)
(declare-fun uus$ (A_a_prod_bool_fun$ A_llist_a_llist_a_a_prod_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun uut$ (A_llist_a_llist_prod_bool_fun$ A_a_a_llist_a_llist_prod_fun_fun$) A_a_bool_fun_fun$)
(declare-fun uuu$ (Bool_a_llist_a_llist_prod_fun$ A_llist_a_llist_bool_fun_fun$) A_llist_a_llist_a_llist_a_llist_prod_fun_fun$)
(declare-fun uuv$ () A_a_bool_fun_fun$)
(declare-fun uuw$ (A_a_a_a_prod_fun_fun$) A_a_a_a_prod_fun_fun$)
(declare-fun uux$ (A_llist_a_llist_a_a_prod_fun_fun$) A_llist_a_llist_a_a_prod_fun_fun$)
(declare-fun uuy$ (A_a_a_llist_a_llist_prod_fun_fun$) A_a_a_llist_a_llist_prod_fun_fun$)
(declare-fun uuz$ (A_llist_a_llist_a_llist_a_llist_prod_fun_fun$) A_llist_a_llist_a_llist_a_llist_prod_fun_fun$)
(declare-fun uva$ (A_llist_a_llist_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun uvb$ (A_a_bool_fun_fun$) A_a_bool_fun_fun$)
(declare-fun swap$ (A_a_prod$) A_a_prod$)
(declare-fun lnull$ (A_llist$) Bool)
(declare-fun swap$a (A_llist_a_llist_prod$) A_llist_a_llist_prod$)
(declare-fun antisym$ (A_llist_a_llist_prod_set$) Bool)
(declare-fun collect$ (A_llist_a_llist_prod_bool_fun$) A_llist_a_llist_prod_set$)
(declare-fun fun_app$ (A_llist_a_llist_a_llist_prod_fun$ A_llist$) A_llist_a_llist_prod$)
(declare-fun llexord$ (A_a_bool_fun_fun$) A_llist_a_llist_bool_fun_fun$)
(declare-fun lprefix$ (A_llist$ A_llist$) Bool)
(declare-fun antisym$a (A_a_prod_set$) Bool)
(declare-fun collect$a (A_a_prod_bool_fun$) A_a_prod_set$)
(declare-fun fun_app$a (A_llist_a_llist_a_llist_a_llist_prod_fun_fun$ A_llist$) A_llist_a_llist_a_llist_prod_fun$)
(declare-fun fun_app$b (A_llist_a_a_prod_fun$ A_llist$) A_a_prod$)
(declare-fun fun_app$c (A_llist_a_llist_a_a_prod_fun_fun$ A_llist$) A_llist_a_a_prod_fun$)
(declare-fun fun_app$d (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun fun_app$e (A_llist_a_llist_bool_fun_fun$ A_llist$) A_llist_bool_fun$)
(declare-fun fun_app$f (A_a_llist_a_llist_prod_fun$ A$) A_llist_a_llist_prod$)
(declare-fun fun_app$g (A_a_a_llist_a_llist_prod_fun_fun$ A$) A_a_llist_a_llist_prod_fun$)
(declare-fun fun_app$h (A_a_a_prod_fun$ A$) A_a_prod$)
(declare-fun fun_app$i (A_a_a_a_prod_fun_fun$ A$) A_a_a_prod_fun$)
(declare-fun fun_app$j (A_bool_fun$ A$) Bool)
(declare-fun fun_app$k (A_a_bool_fun_fun$ A$) A_bool_fun$)
(declare-fun fun_app$l (A_llist_a_llist_prod_a_a_prod_fun$ A_llist_a_llist_prod$) A_a_prod$)
(declare-fun fun_app$m (A_llist_a_llist_a_a_prod_fun_fun_a_llist_a_llist_prod_a_a_prod_fun_fun$ A_llist_a_llist_a_a_prod_fun_fun$) A_llist_a_llist_prod_a_a_prod_fun$)
(declare-fun fun_app$n (A_llist_a_llist_prod_bool_fun$ A_llist_a_llist_prod$) Bool)
(declare-fun fun_app$o (A_llist_a_llist_bool_fun_fun_a_llist_a_llist_prod_bool_fun_fun$ A_llist_a_llist_bool_fun_fun$) A_llist_a_llist_prod_bool_fun$)
(declare-fun fun_app$p (A_a_prod_a_llist_a_llist_prod_fun$ A_a_prod$) A_llist_a_llist_prod$)
(declare-fun fun_app$q (A_a_a_llist_a_llist_prod_fun_fun_a_a_prod_a_llist_a_llist_prod_fun_fun$ A_a_a_llist_a_llist_prod_fun_fun$) A_a_prod_a_llist_a_llist_prod_fun$)
(declare-fun fun_app$r (A_a_prod_a_a_prod_fun$ A_a_prod$) A_a_prod$)
(declare-fun fun_app$s (A_a_a_a_prod_fun_fun_a_a_prod_a_a_prod_fun_fun$ A_a_a_a_prod_fun_fun$) A_a_prod_a_a_prod_fun$)
(declare-fun fun_app$t (A_a_prod_bool_fun$ A_a_prod$) Bool)
(declare-fun fun_app$u (A_a_bool_fun_fun_a_a_prod_bool_fun_fun$ A_a_bool_fun_fun$) A_a_prod_bool_fun$)
(declare-fun fun_app$v (Bool_a_llist_a_llist_prod_fun$ Bool) A_llist_a_llist_prod$)
(declare-fun fun_app$w (Bool_a_a_prod_fun$ Bool) A_a_prod$)
(declare-fun fun_app$x (Bool_bool_fun$ Bool) Bool)
(declare-fun fun_app$y (A_llist_a_llist_prod_a_llist_a_llist_prod_fun$ A_llist_a_llist_prod$) A_llist_a_llist_prod$)
(declare-fun fun_app$z (A_llist_a_llist_a_llist_a_llist_prod_fun_fun_a_llist_a_llist_prod_a_llist_a_llist_prod_fun_fun$ A_llist_a_llist_a_llist_a_llist_prod_fun_fun$) A_llist_a_llist_prod_a_llist_a_llist_prod_fun$)
(declare-fun case_prod$ () A_llist_a_llist_a_a_prod_fun_fun_a_llist_a_llist_prod_a_a_prod_fun_fun$)
(declare-fun case_prod$a () A_llist_a_llist_bool_fun_fun_a_llist_a_llist_prod_bool_fun_fun$)
(declare-fun case_prod$b () A_a_a_llist_a_llist_prod_fun_fun_a_a_prod_a_llist_a_llist_prod_fun_fun$)
(declare-fun case_prod$c () A_a_a_a_prod_fun_fun_a_a_prod_a_a_prod_fun_fun$)
(declare-fun case_prod$d () A_a_bool_fun_fun_a_a_prod_bool_fun_fun$)
(declare-fun case_prod$e () A_llist_a_llist_a_llist_a_llist_prod_fun_fun_a_llist_a_llist_prod_a_llist_a_llist_prod_fun_fun$)
(declare-fun internal_split$ () A_a_a_a_prod_fun_fun_a_a_prod_a_a_prod_fun_fun$)
(declare-fun internal_split$a () A_llist_a_llist_a_a_prod_fun_fun_a_llist_a_llist_prod_a_a_prod_fun_fun$)
(declare-fun internal_split$b () A_a_a_llist_a_llist_prod_fun_fun_a_a_prod_a_llist_a_llist_prod_fun_fun$)
(declare-fun internal_split$c () A_llist_a_llist_a_llist_a_llist_prod_fun_fun_a_llist_a_llist_prod_a_llist_a_llist_prod_fun_fun$)
(declare-fun internal_split$d () A_llist_a_llist_bool_fun_fun_a_llist_a_llist_prod_bool_fun_fun$)
(declare-fun internal_split$e () A_a_bool_fun_fun_a_a_prod_bool_fun_fun$)
(assert (! (forall ((?v0 A_llist_a_llist_a_llist_a_llist_prod_fun_fun$) (?v1 A_llist$) (?v2 A_llist$)) (! (= (fun_app$ (fun_app$a (uuz$ ?v0) ?v1) ?v2) (fun_app$ (fun_app$a ?v0 ?v2) ?v1)) :pattern ((fun_app$ (fun_app$a (uuz$ ?v0) ?v1) ?v2)))) :named a0))
(assert (! (forall ((?v0 A_llist_a_llist_a_a_prod_fun_fun$) (?v1 A_llist$) (?v2 A_llist$)) (! (= (fun_app$b (fun_app$c (uux$ ?v0) ?v1) ?v2) (fun_app$b (fun_app$c ?v0 ?v2) ?v1)) :pattern ((fun_app$b (fun_app$c (uux$ ?v0) ?v1) ?v2)))) :named a1))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$)) (! (= (fun_app$d (fun_app$e (uva$ ?v0) ?v1) ?v2) (fun_app$d (fun_app$e ?v0 ?v2) ?v1)) :pattern ((fun_app$d (fun_app$e (uva$ ?v0) ?v1) ?v2)))) :named a2))
(assert (! (forall ((?v0 A_a_a_llist_a_llist_prod_fun_fun$) (?v1 A$) (?v2 A$)) (! (= (fun_app$f (fun_app$g (uuy$ ?v0) ?v1) ?v2) (fun_app$f (fun_app$g ?v0 ?v2) ?v1)) :pattern ((fun_app$f (fun_app$g (uuy$ ?v0) ?v1) ?v2)))) :named a3))
(assert (! (forall ((?v0 A_a_a_a_prod_fun_fun$) (?v1 A$) (?v2 A$)) (! (= (fun_app$h (fun_app$i (uuw$ ?v0) ?v1) ?v2) (fun_app$h (fun_app$i ?v0 ?v2) ?v1)) :pattern ((fun_app$h (fun_app$i (uuw$ ?v0) ?v1) ?v2)))) :named a4))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A$) (?v2 A$)) (! (= (fun_app$j (fun_app$k (uvb$ ?v0) ?v1) ?v2) (fun_app$j (fun_app$k ?v0 ?v2) ?v1)) :pattern ((fun_app$j (fun_app$k (uvb$ ?v0) ?v1) ?v2)))) :named a5))
(assert (! (forall ((?v0 A_llist_a_llist_a_a_prod_fun_fun$) (?v1 A_llist_a_llist_a_llist_a_llist_prod_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$b (fun_app$c (uuj$ ?v0 ?v1) ?v2) ?v3) (fun_app$l (fun_app$m case_prod$ ?v0) (fun_app$ (fun_app$a ?v1 ?v2) ?v3))) :pattern ((fun_app$b (fun_app$c (uuj$ ?v0 ?v1) ?v2) ?v3)))) :named a6))
(assert (! (forall ((?v0 A_llist_a_llist_a_a_prod_fun_fun$) (?v1 A_a_a_llist_a_llist_prod_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$h (fun_app$i (uuh$ ?v0 ?v1) ?v2) ?v3) (fun_app$l (fun_app$m case_prod$ ?v0) (fun_app$f (fun_app$g ?v1 ?v2) ?v3))) :pattern ((fun_app$h (fun_app$i (uuh$ ?v0 ?v1) ?v2) ?v3)))) :named a7))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_a_llist_a_llist_a_llist_prod_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$d (fun_app$e (uue$ ?v0 ?v1) ?v2) ?v3) (fun_app$n (fun_app$o case_prod$a ?v0) (fun_app$ (fun_app$a ?v1 ?v2) ?v3))) :pattern ((fun_app$d (fun_app$e (uue$ ?v0 ?v1) ?v2) ?v3)))) :named a8))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_a_a_llist_a_llist_prod_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$j (fun_app$k (uuc$ ?v0 ?v1) ?v2) ?v3) (fun_app$n (fun_app$o case_prod$a ?v0) (fun_app$f (fun_app$g ?v1 ?v2) ?v3))) :pattern ((fun_app$j (fun_app$k (uuc$ ?v0 ?v1) ?v2) ?v3)))) :named a9))
(assert (! (forall ((?v0 A_a_a_llist_a_llist_prod_fun_fun$) (?v1 A_llist_a_llist_a_a_prod_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$ (fun_app$a (uuk$ ?v0 ?v1) ?v2) ?v3) (fun_app$p (fun_app$q case_prod$b ?v0) (fun_app$b (fun_app$c ?v1 ?v2) ?v3))) :pattern ((fun_app$ (fun_app$a (uuk$ ?v0 ?v1) ?v2) ?v3)))) :named a10))
(assert (! (forall ((?v0 A_a_a_llist_a_llist_prod_fun_fun$) (?v1 A_a_a_a_prod_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$f (fun_app$g (uui$ ?v0 ?v1) ?v2) ?v3) (fun_app$p (fun_app$q case_prod$b ?v0) (fun_app$h (fun_app$i ?v1 ?v2) ?v3))) :pattern ((fun_app$f (fun_app$g (uui$ ?v0 ?v1) ?v2) ?v3)))) :named a11))
(assert (! (forall ((?v0 A_a_a_a_prod_fun_fun$) (?v1 A_llist_a_llist_a_a_prod_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$b (fun_app$c (uug$ ?v0 ?v1) ?v2) ?v3) (fun_app$r (fun_app$s case_prod$c ?v0) (fun_app$b (fun_app$c ?v1 ?v2) ?v3))) :pattern ((fun_app$b (fun_app$c (uug$ ?v0 ?v1) ?v2) ?v3)))) :named a12))
(assert (! (forall ((?v0 A_a_a_a_prod_fun_fun$) (?v1 A_a_a_a_prod_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$h (fun_app$i (uuf$ ?v0 ?v1) ?v2) ?v3) (fun_app$r (fun_app$s case_prod$c ?v0) (fun_app$h (fun_app$i ?v1 ?v2) ?v3))) :pattern ((fun_app$h (fun_app$i (uuf$ ?v0 ?v1) ?v2) ?v3)))) :named a13))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist_a_llist_a_a_prod_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$d (fun_app$e (uud$ ?v0 ?v1) ?v2) ?v3) (fun_app$t (fun_app$u case_prod$d ?v0) (fun_app$b (fun_app$c ?v1 ?v2) ?v3))) :pattern ((fun_app$d (fun_app$e (uud$ ?v0 ?v1) ?v2) ?v3)))) :named a14))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_a_a_a_prod_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$j (fun_app$k (uub$ ?v0 ?v1) ?v2) ?v3) (fun_app$t (fun_app$u case_prod$d ?v0) (fun_app$h (fun_app$i ?v1 ?v2) ?v3))) :pattern ((fun_app$j (fun_app$k (uub$ ?v0 ?v1) ?v2) ?v3)))) :named a15))
(assert (! (forall ((?v0 Bool) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$d (fun_app$e (uu$ ?v0 ?v1) ?v2) ?v3) (and ?v0 (fun_app$d (fun_app$e ?v1 ?v2) ?v3))) :pattern ((fun_app$d (fun_app$e (uu$ ?v0 ?v1) ?v2) ?v3)))) :named a16))
(assert (! (forall ((?v0 Bool) (?v1 A_a_bool_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$j (fun_app$k (uua$ ?v0 ?v1) ?v2) ?v3) (and ?v0 (fun_app$j (fun_app$k ?v1 ?v2) ?v3))) :pattern ((fun_app$j (fun_app$k (uua$ ?v0 ?v1) ?v2) ?v3)))) :named a17))
(assert (! (forall ((?v0 A_llist_a_llist_prod_bool_fun$) (?v1 A_a_a_llist_a_llist_prod_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$j (fun_app$k (uut$ ?v0 ?v1) ?v2) ?v3) (fun_app$n ?v0 (fun_app$f (fun_app$g ?v1 ?v2) ?v3))) :pattern ((fun_app$j (fun_app$k (uut$ ?v0 ?v1) ?v2) ?v3)))) :named a18))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$) (?v1 A_a_a_a_prod_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$h (fun_app$i (uur$ ?v0 ?v1) ?v2) ?v3) (fun_app$r ?v0 (fun_app$h (fun_app$i ?v1 ?v2) ?v3))) :pattern ((fun_app$h (fun_app$i (uur$ ?v0 ?v1) ?v2) ?v3)))) :named a19))
(assert (! (forall ((?v0 A_a_prod_bool_fun$) (?v1 A_llist_a_llist_a_a_prod_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$d (fun_app$e (uus$ ?v0 ?v1) ?v2) ?v3) (fun_app$t ?v0 (fun_app$b (fun_app$c ?v1 ?v2) ?v3))) :pattern ((fun_app$d (fun_app$e (uus$ ?v0 ?v1) ?v2) ?v3)))) :named a20))
(assert (! (forall ((?v0 A_a_prod_bool_fun$) (?v1 A_a_a_a_prod_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$j (fun_app$k (uuo$ ?v0 ?v1) ?v2) ?v3) (fun_app$t ?v0 (fun_app$h (fun_app$i ?v1 ?v2) ?v3))) :pattern ((fun_app$j (fun_app$k (uuo$ ?v0 ?v1) ?v2) ?v3)))) :named a21))
(assert (! (forall ((?v0 Bool_a_llist_a_llist_prod_fun$) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$ (fun_app$a (uuu$ ?v0 ?v1) ?v2) ?v3) (fun_app$v ?v0 (fun_app$d (fun_app$e ?v1 ?v2) ?v3))) :pattern ((fun_app$ (fun_app$a (uuu$ ?v0 ?v1) ?v2) ?v3)))) :named a22))
(assert (! (forall ((?v0 Bool_a_llist_a_llist_prod_fun$) (?v1 A_a_bool_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$f (fun_app$g (uuq$ ?v0 ?v1) ?v2) ?v3) (fun_app$v ?v0 (fun_app$j (fun_app$k ?v1 ?v2) ?v3))) :pattern ((fun_app$f (fun_app$g (uuq$ ?v0 ?v1) ?v2) ?v3)))) :named a23))
(assert (! (forall ((?v0 Bool_a_a_prod_fun$) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$b (fun_app$c (uup$ ?v0 ?v1) ?v2) ?v3) (fun_app$w ?v0 (fun_app$d (fun_app$e ?v1 ?v2) ?v3))) :pattern ((fun_app$b (fun_app$c (uup$ ?v0 ?v1) ?v2) ?v3)))) :named a24))
(assert (! (forall ((?v0 Bool_a_a_prod_fun$) (?v1 A_a_bool_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$h (fun_app$i (uun$ ?v0 ?v1) ?v2) ?v3) (fun_app$w ?v0 (fun_app$j (fun_app$k ?v1 ?v2) ?v3))) :pattern ((fun_app$h (fun_app$i (uun$ ?v0 ?v1) ?v2) ?v3)))) :named a25))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist$) (?v3 A_llist$)) (! (= (fun_app$d (fun_app$e (uum$ ?v0 ?v1) ?v2) ?v3) (fun_app$x ?v0 (fun_app$d (fun_app$e ?v1 ?v2) ?v3))) :pattern ((fun_app$d (fun_app$e (uum$ ?v0 ?v1) ?v2) ?v3)))) :named a26))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_a_bool_fun_fun$) (?v2 A$) (?v3 A$)) (! (= (fun_app$j (fun_app$k (uul$ ?v0 ?v1) ?v2) ?v3) (fun_app$x ?v0 (fun_app$j (fun_app$k ?v1 ?v2) ?v3))) :pattern ((fun_app$j (fun_app$k (uul$ ?v0 ?v1) ?v2) ?v3)))) :named a27))
(assert (! (forall ((?v0 A$) (?v1 A$)) (! (= (fun_app$j (fun_app$k uuv$ ?v0) ?v1) false) :pattern ((fun_app$j (fun_app$k uuv$ ?v0) ?v1)))) :named a28))
(assert (! (not (antisym$ (collect$ (fun_app$o case_prod$a (llexord$ r$))))) :named a29))
(assert (! (forall ((?v0 A$)) (not (fun_app$j (fun_app$k r$ ?v0) ?v0))) :named a30))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$)) (fun_app$d (fun_app$e (llexord$ ?v0) ?v1) ?v1)) :named a31))
(assert (! (forall ((?v0 Bool) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$n (fun_app$o case_prod$a (uu$ ?v0 ?v1)) ?v2) (and ?v0 (fun_app$n (fun_app$o case_prod$a ?v1) ?v2)))) :named a32))
(assert (! (forall ((?v0 Bool) (?v1 A_a_bool_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$t (fun_app$u case_prod$d (uua$ ?v0 ?v1)) ?v2) (and ?v0 (fun_app$t (fun_app$u case_prod$d ?v1) ?v2)))) :named a33))
(assert (! (antisym$a (collect$a (fun_app$u case_prod$d r$))) :named a34))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_a_a_a_prod_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$t (fun_app$u case_prod$d ?v0) (fun_app$r (fun_app$s case_prod$c ?v1) ?v2)) (fun_app$t (fun_app$u case_prod$d (uub$ ?v0 ?v1)) ?v2))) :named a35))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_a_a_llist_a_llist_prod_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$n (fun_app$o case_prod$a ?v0) (fun_app$p (fun_app$q case_prod$b ?v1) ?v2)) (fun_app$t (fun_app$u case_prod$d (uuc$ ?v0 ?v1)) ?v2))) :named a36))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist_a_llist_a_a_prod_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$t (fun_app$u case_prod$d ?v0) (fun_app$l (fun_app$m case_prod$ ?v1) ?v2)) (fun_app$n (fun_app$o case_prod$a (uud$ ?v0 ?v1)) ?v2))) :named a37))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_a_llist_a_llist_a_llist_prod_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$n (fun_app$o case_prod$a ?v0) (fun_app$y (fun_app$z case_prod$e ?v1) ?v2)) (fun_app$n (fun_app$o case_prod$a (uue$ ?v0 ?v1)) ?v2))) :named a38))
(assert (! (forall ((?v0 A_a_a_a_prod_fun_fun$) (?v1 A_a_a_a_prod_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$r (fun_app$s case_prod$c ?v0) (fun_app$r (fun_app$s case_prod$c ?v1) ?v2)) (fun_app$r (fun_app$s case_prod$c (uuf$ ?v0 ?v1)) ?v2))) :named a39))
(assert (! (forall ((?v0 A_a_a_a_prod_fun_fun$) (?v1 A_llist_a_llist_a_a_prod_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$r (fun_app$s case_prod$c ?v0) (fun_app$l (fun_app$m case_prod$ ?v1) ?v2)) (fun_app$l (fun_app$m case_prod$ (uug$ ?v0 ?v1)) ?v2))) :named a40))
(assert (! (forall ((?v0 A_llist_a_llist_a_a_prod_fun_fun$) (?v1 A_a_a_llist_a_llist_prod_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$l (fun_app$m case_prod$ ?v0) (fun_app$p (fun_app$q case_prod$b ?v1) ?v2)) (fun_app$r (fun_app$s case_prod$c (uuh$ ?v0 ?v1)) ?v2))) :named a41))
(assert (! (forall ((?v0 A_a_a_llist_a_llist_prod_fun_fun$) (?v1 A_a_a_a_prod_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$p (fun_app$q case_prod$b ?v0) (fun_app$r (fun_app$s case_prod$c ?v1) ?v2)) (fun_app$p (fun_app$q case_prod$b (uui$ ?v0 ?v1)) ?v2))) :named a42))
(assert (! (forall ((?v0 A_llist_a_llist_a_a_prod_fun_fun$) (?v1 A_llist_a_llist_a_llist_a_llist_prod_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$l (fun_app$m case_prod$ ?v0) (fun_app$y (fun_app$z case_prod$e ?v1) ?v2)) (fun_app$l (fun_app$m case_prod$ (uuj$ ?v0 ?v1)) ?v2))) :named a43))
(assert (! (forall ((?v0 A_a_a_llist_a_llist_prod_fun_fun$) (?v1 A_llist_a_llist_a_a_prod_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$p (fun_app$q case_prod$b ?v0) (fun_app$l (fun_app$m case_prod$ ?v1) ?v2)) (fun_app$y (fun_app$z case_prod$e (uuk$ ?v0 ?v1)) ?v2))) :named a44))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_a_bool_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$x ?v0 (fun_app$t (fun_app$u case_prod$d ?v1) ?v2)) (fun_app$t (fun_app$u case_prod$d (uul$ ?v0 ?v1)) ?v2))) :named a45))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$x ?v0 (fun_app$n (fun_app$o case_prod$a ?v1) ?v2)) (fun_app$n (fun_app$o case_prod$a (uum$ ?v0 ?v1)) ?v2))) :named a46))
(assert (! (forall ((?v0 Bool_a_a_prod_fun$) (?v1 A_a_bool_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$w ?v0 (fun_app$t (fun_app$u case_prod$d ?v1) ?v2)) (fun_app$r (fun_app$s case_prod$c (uun$ ?v0 ?v1)) ?v2))) :named a47))
(assert (! (forall ((?v0 A_a_prod_bool_fun$) (?v1 A_a_a_a_prod_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$t ?v0 (fun_app$r (fun_app$s case_prod$c ?v1) ?v2)) (fun_app$t (fun_app$u case_prod$d (uuo$ ?v0 ?v1)) ?v2))) :named a48))
(assert (! (forall ((?v0 Bool_a_a_prod_fun$) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$w ?v0 (fun_app$n (fun_app$o case_prod$a ?v1) ?v2)) (fun_app$l (fun_app$m case_prod$ (uup$ ?v0 ?v1)) ?v2))) :named a49))
(assert (! (forall ((?v0 Bool_a_llist_a_llist_prod_fun$) (?v1 A_a_bool_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$v ?v0 (fun_app$t (fun_app$u case_prod$d ?v1) ?v2)) (fun_app$p (fun_app$q case_prod$b (uuq$ ?v0 ?v1)) ?v2))) :named a50))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$) (?v1 A_a_a_a_prod_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$r ?v0 (fun_app$r (fun_app$s case_prod$c ?v1) ?v2)) (fun_app$r (fun_app$s case_prod$c (uur$ ?v0 ?v1)) ?v2))) :named a51))
(assert (! (forall ((?v0 A_a_prod_bool_fun$) (?v1 A_llist_a_llist_a_a_prod_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$t ?v0 (fun_app$l (fun_app$m case_prod$ ?v1) ?v2)) (fun_app$n (fun_app$o case_prod$a (uus$ ?v0 ?v1)) ?v2))) :named a52))
(assert (! (forall ((?v0 A_llist_a_llist_prod_bool_fun$) (?v1 A_a_a_llist_a_llist_prod_fun_fun$) (?v2 A_a_prod$)) (= (fun_app$n ?v0 (fun_app$p (fun_app$q case_prod$b ?v1) ?v2)) (fun_app$t (fun_app$u case_prod$d (uut$ ?v0 ?v1)) ?v2))) :named a53))
(assert (! (forall ((?v0 Bool_a_llist_a_llist_prod_fun$) (?v1 A_llist_a_llist_bool_fun_fun$) (?v2 A_llist_a_llist_prod$)) (= (fun_app$v ?v0 (fun_app$n (fun_app$o case_prod$a ?v1) ?v2)) (fun_app$y (fun_app$z case_prod$e (uuu$ ?v0 ?v1)) ?v2))) :named a54))
(assert (! (forall ((?v0 A_a_prod$) (?v1 A_a_prod$) (?v2 A_a_a_a_prod_fun_fun$)) (=> (= ?v0 ?v1) (= (fun_app$r (fun_app$s case_prod$c ?v2) ?v0) (fun_app$r (fun_app$s case_prod$c ?v2) ?v1)))) :named a55))
(assert (! (forall ((?v0 A_llist_a_llist_prod$) (?v1 A_llist_a_llist_prod$) (?v2 A_llist_a_llist_a_a_prod_fun_fun$)) (=> (= ?v0 ?v1) (= (fun_app$l (fun_app$m case_prod$ ?v2) ?v0) (fun_app$l (fun_app$m case_prod$ ?v2) ?v1)))) :named a56))
(assert (! (forall ((?v0 A_a_prod$) (?v1 A_a_prod$) (?v2 A_a_a_llist_a_llist_prod_fun_fun$)) (=> (= ?v0 ?v1) (= (fun_app$p (fun_app$q case_prod$b ?v2) ?v0) (fun_app$p (fun_app$q case_prod$b ?v2) ?v1)))) :named a57))
(assert (! (forall ((?v0 A_llist_a_llist_prod$) (?v1 A_llist_a_llist_prod$) (?v2 A_llist_a_llist_a_llist_a_llist_prod_fun_fun$)) (=> (= ?v0 ?v1) (= (fun_app$y (fun_app$z case_prod$e ?v2) ?v0) (fun_app$y (fun_app$z case_prod$e ?v2) ?v1)))) :named a58))
(assert (! (forall ((?v0 A_llist_a_llist_prod$) (?v1 A_llist_a_llist_prod$) (?v2 A_llist_a_llist_bool_fun_fun$)) (=> (= ?v0 ?v1) (= (fun_app$n (fun_app$o case_prod$a ?v2) ?v0) (fun_app$n (fun_app$o case_prod$a ?v2) ?v1)))) :named a59))
(assert (! (forall ((?v0 A_a_prod$) (?v1 A_a_prod$) (?v2 A_a_bool_fun_fun$)) (=> (= ?v0 ?v1) (= (fun_app$t (fun_app$u case_prod$d ?v2) ?v0) (fun_app$t (fun_app$u case_prod$d ?v2) ?v1)))) :named a60))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (fun_app$d (fun_app$e (llexord$ uuv$) ?v0) ?v1) (lprefix$ ?v0 ?v1))) :named a61))
(assert (! (forall ((?v0 A_a_a_a_prod_fun_fun$) (?v1 A_a_prod$)) (= (fun_app$r (fun_app$s case_prod$c (uuw$ ?v0)) (swap$ ?v1)) (fun_app$r (fun_app$s case_prod$c ?v0) ?v1))) :named a62))
(assert (! (forall ((?v0 A_llist_a_llist_a_a_prod_fun_fun$) (?v1 A_llist_a_llist_prod$)) (= (fun_app$l (fun_app$m case_prod$ (uux$ ?v0)) (swap$a ?v1)) (fun_app$l (fun_app$m case_prod$ ?v0) ?v1))) :named a63))
(assert (! (forall ((?v0 A_a_a_llist_a_llist_prod_fun_fun$) (?v1 A_a_prod$)) (= (fun_app$p (fun_app$q case_prod$b (uuy$ ?v0)) (swap$ ?v1)) (fun_app$p (fun_app$q case_prod$b ?v0) ?v1))) :named a64))
(assert (! (forall ((?v0 A_llist_a_llist_a_llist_a_llist_prod_fun_fun$) (?v1 A_llist_a_llist_prod$)) (= (fun_app$y (fun_app$z case_prod$e (uuz$ ?v0)) (swap$a ?v1)) (fun_app$y (fun_app$z case_prod$e ?v0) ?v1))) :named a65))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist_a_llist_prod$)) (= (fun_app$n (fun_app$o case_prod$a (uva$ ?v0)) (swap$a ?v1)) (fun_app$n (fun_app$o case_prod$a ?v0) ?v1))) :named a66))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_a_prod$)) (= (fun_app$t (fun_app$u case_prod$d (uvb$ ?v0)) (swap$ ?v1)) (fun_app$t (fun_app$u case_prod$d ?v0) ?v1))) :named a67))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A$) (?v2 A_llist$) (?v3 A$) (?v4 A_llist$)) (! (= (fun_app$d (fun_app$e (llexord$ ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v3 ?v4)) (or (and (= ?v1 ?v3) (fun_app$d (fun_app$e (llexord$ ?v0) ?v2) ?v4)) (fun_app$j (fun_app$k ?v0 ?v1) ?v3))) :pattern ((fun_app$d (fun_app$e (llexord$ ?v0) (lCons$ ?v1 ?v2)) (lCons$ ?v3 ?v4))))) :named a68))
(assert (! (forall ((?v0 A_llist$) (?v1 A_a_bool_fun_fun$) (?v2 A_llist$)) (! (=> (lnull$ ?v0) (= (fun_app$d (fun_app$e (llexord$ ?v1) ?v2) ?v0) (lnull$ ?v2))) :pattern ((fun_app$d (fun_app$e (llexord$ ?v1) ?v2) ?v0)))) :named a69))
(assert (! (= internal_split$ case_prod$c) :named a70))
(assert (! (= internal_split$a case_prod$) :named a71))
(assert (! (= internal_split$b case_prod$b) :named a72))
(assert (! (= internal_split$c case_prod$e) :named a73))
(assert (! (= internal_split$d case_prod$a) :named a74))
(assert (! (= internal_split$e case_prod$d) :named a75))
(assert (! (forall ((?v0 A_a_bool_fun_fun$) (?v1 A_llist$)) (fun_app$d (fun_app$e (llexord$ ?v0) lNil$) ?v1)) :named a76))
(assert (! (forall ((?v0 A_llist$)) (lprefix$ ?v0 ?v0)) :named a77))
(assert (! (forall ((?v0 A_llist$)) (lprefix$ ?v0 ?v0)) :named a78))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a79))
(check-sat)
;(get-unsat-core)
