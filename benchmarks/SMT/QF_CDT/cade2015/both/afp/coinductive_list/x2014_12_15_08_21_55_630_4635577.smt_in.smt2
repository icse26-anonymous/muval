; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 460
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_set$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort A_a_prod_set$ 0)
(declare-sort A_a_a_prod_fun$ 0)
(declare-sort A_a_prod_a_fun$ 0)
(declare-sort A_a_bool_fun_fun$ 0)
(declare-sort A_a_prod_bool_fun$ 0)
(declare-sort A_a_fun_a_a_fun_fun$ 0)
(declare-sort A_a_prod_a_a_prod_fun$ 0)
(declare-sort A_bool_fun_a_bool_fun_fun$ 0)
(declare-sort A_a_a_prod_fun_a_a_fun_fun$ 0)
(declare-sort A_a_fun_a_a_a_prod_fun_fun$ 0)
(declare-sort A_a_prod_bool_fun_a_bool_fun_fun$ 0)
(declare-sort A_bool_fun_a_a_prod_bool_fun_fun$ 0)
(declare-sort A_a_a_prod_fun_a_a_a_prod_fun_fun$ 0)
(declare-sort A_a_prod_a_fun_a_a_prod_a_fun_fun$ 0)
(declare-sort A_set_a_bool_fun_a_bool_fun_fun_fun$ 0)
(declare-sort A_a_prod_bool_fun_a_a_prod_bool_fun_fun$ 0)
(declare-sort A_a_prod_a_a_prod_fun_a_a_prod_a_fun_fun$ 0)
(declare-sort A_a_prod_a_fun_a_a_prod_a_a_prod_fun_fun$ 0)
(declare-sort A_a_prod_set_a_bool_fun_a_bool_fun_fun_fun$ 0)
(declare-sort A_set_a_a_prod_bool_fun_a_bool_fun_fun_fun$ 0)
(declare-sort A_a_prod_a_a_prod_fun_a_a_prod_a_a_prod_fun_fun$ 0)
(declare-sort A_a_prod_set_a_bool_fun_a_a_prod_bool_fun_fun_fun$ 0)
(declare-sort A_set_a_a_prod_bool_fun_a_a_prod_bool_fun_fun_fun$ 0)
(declare-sort A_a_prod_set_a_a_prod_bool_fun_a_a_prod_bool_fun_fun_fun$ 0)
(declare-datatypes () ((A_a_prod$ (pair$ (fst$ A$) (snd$ A$)))))
(declare-codatatypes () ((A_a_prod_llist$ (lNil$) (lCons$ (lhd$ A_a_prod$) (ltl$ A_a_prod_llist$)))
  (A_llist$ (lNil$a) (lCons$a (lhd$a A$) (ltl$a A_llist$)))))
(declare-fun uu$ () A_a_a_prod_fun$)
(declare-fun xs$ () A_llist$)
(declare-fun uua$ () A_a_fun$)
(declare-fun uub$ () A_a_prod_a_a_prod_fun$)
(declare-fun uuc$ (A_a_fun$) A_a_prod_a_fun_a_a_prod_a_fun_fun$)
(declare-fun uud$ (A_a_prod_a_fun$) A_a_prod_a_a_prod_fun_a_a_prod_a_fun_fun$)
(declare-fun uue$ (A_a_prod_a_fun$) A_a_a_prod_fun_a_a_fun_fun$)
(declare-fun uuf$ (A_a_a_prod_fun$) A_a_prod_a_fun_a_a_prod_a_a_prod_fun_fun$)
(declare-fun uug$ (A_a_fun$) A_a_fun_a_a_fun_fun$)
(declare-fun uuh$ (A_a_prod_a_a_prod_fun$) A_a_prod_a_a_prod_fun_a_a_prod_a_a_prod_fun_fun$)
(declare-fun uui$ (A_a_prod_a_a_prod_fun$) A_a_a_prod_fun_a_a_a_prod_fun_fun$)
(declare-fun uuj$ (A_a_a_prod_fun$) A_a_fun_a_a_a_prod_fun_fun$)
(declare-fun uuk$ (A_a_prod_a_a_prod_fun$) A_a_prod_set_a_a_prod_bool_fun_a_a_prod_bool_fun_fun_fun$)
(declare-fun uul$ (A_a_prod_a_a_prod_fun$) A_a_prod_set_a_a_prod_bool_fun_a_a_prod_bool_fun_fun_fun$)
(declare-fun uum$ (A_a_prod_a_fun$) A_a_prod_set_a_bool_fun_a_bool_fun_fun_fun$)
(declare-fun uun$ (A_a_prod_a_fun$) A_a_prod_set_a_bool_fun_a_a_prod_bool_fun_fun_fun$)
(declare-fun uuo$ (A_a_fun$) A_set_a_bool_fun_a_bool_fun_fun_fun$)
(declare-fun uup$ (A_a_fun$) A_set_a_bool_fun_a_bool_fun_fun_fun$)
(declare-fun uuq$ (A_a_a_prod_fun$) A_set_a_a_prod_bool_fun_a_a_prod_bool_fun_fun_fun$)
(declare-fun uur$ (A_a_a_prod_fun$) A_set_a_a_prod_bool_fun_a_bool_fun_fun_fun$)
(declare-fun uus$ (A_a_prod_set$) A_a_bool_fun_fun$)
(declare-fun lset$ (A_a_prod_llist$) A_a_prod_set$)
(declare-fun lzip$ (A_llist$ A_llist$) A_a_prod_llist$)
(declare-fun image$ (A_a_prod_a_a_prod_fun$ A_a_prod_set$) A_a_prod_set$)
(declare-fun lset$a (A_llist$) A_set$)
(declare-fun image$a (A_a_prod_a_fun$ A_a_prod_set$) A_set$)
(declare-fun image$b (A_a_a_prod_fun$ A_set$) A_a_prod_set$)
(declare-fun image$c (A_a_fun$ A_set$) A_set$)
(declare-fun member$ (A_a_prod$ A_a_prod_set$) Bool)
(declare-fun collect$ (A_a_prod_bool_fun$) A_a_prod_set$)
(declare-fun fun_app$ (A_a_a_prod_fun$ A$) A_a_prod$)
(declare-fun lmember$ (A_a_prod$ A_a_prod_llist$) Bool)
(declare-fun member$a (A$ A_set$) Bool)
(declare-fun collect$a (A_bool_fun$) A_set$)
(declare-fun fun_app$a (A_bool_fun$ A$) Bool)
(declare-fun fun_app$b (A_a_bool_fun_fun$ A$) A_bool_fun$)
(declare-fun fun_app$c (A_a_prod_a_a_prod_fun$ A_a_prod$) A_a_prod$)
(declare-fun fun_app$d (A_a_prod_a_a_prod_fun_a_a_prod_a_a_prod_fun_fun$ A_a_prod_a_a_prod_fun$) A_a_prod_a_a_prod_fun$)
(declare-fun fun_app$e (A_a_a_prod_fun_a_a_a_prod_fun_fun$ A_a_a_prod_fun$) A_a_a_prod_fun$)
(declare-fun fun_app$f (A_a_prod_a_fun$ A_a_prod$) A$)
(declare-fun fun_app$g (A_a_prod_a_a_prod_fun_a_a_prod_a_fun_fun$ A_a_prod_a_a_prod_fun$) A_a_prod_a_fun$)
(declare-fun fun_app$h (A_a_fun$ A$) A$)
(declare-fun fun_app$i (A_a_a_prod_fun_a_a_fun_fun$ A_a_a_prod_fun$) A_a_fun$)
(declare-fun fun_app$j (A_a_prod_a_fun_a_a_prod_a_a_prod_fun_fun$ A_a_prod_a_fun$) A_a_prod_a_a_prod_fun$)
(declare-fun fun_app$k (A_a_fun_a_a_a_prod_fun_fun$ A_a_fun$) A_a_a_prod_fun$)
(declare-fun fun_app$l (A_a_prod_a_fun_a_a_prod_a_fun_fun$ A_a_prod_a_fun$) A_a_prod_a_fun$)
(declare-fun fun_app$m (A_a_fun_a_a_fun_fun$ A_a_fun$) A_a_fun$)
(declare-fun fun_app$n (A_a_prod_bool_fun$ A_a_prod$) Bool)
(declare-fun fun_app$o (A_a_prod_bool_fun_a_a_prod_bool_fun_fun$ A_a_prod_bool_fun$) A_a_prod_bool_fun$)
(declare-fun fun_app$p (A_a_prod_set_a_a_prod_bool_fun_a_a_prod_bool_fun_fun_fun$ A_a_prod_set$) A_a_prod_bool_fun_a_a_prod_bool_fun_fun$)
(declare-fun fun_app$q (A_bool_fun_a_bool_fun_fun$ A_bool_fun$) A_bool_fun$)
(declare-fun fun_app$r (A_a_prod_set_a_bool_fun_a_bool_fun_fun_fun$ A_a_prod_set$) A_bool_fun_a_bool_fun_fun$)
(declare-fun fun_app$s (A_set_a_a_prod_bool_fun_a_a_prod_bool_fun_fun_fun$ A_set$) A_a_prod_bool_fun_a_a_prod_bool_fun_fun$)
(declare-fun fun_app$t (A_set_a_bool_fun_a_bool_fun_fun_fun$ A_set$) A_bool_fun_a_bool_fun_fun$)
(declare-fun fun_app$u (A_bool_fun_a_a_prod_bool_fun_fun$ A_bool_fun$) A_a_prod_bool_fun$)
(declare-fun fun_app$v (A_a_prod_set_a_bool_fun_a_a_prod_bool_fun_fun_fun$ A_a_prod_set$) A_bool_fun_a_a_prod_bool_fun_fun$)
(declare-fun fun_app$w (A_a_prod_bool_fun_a_bool_fun_fun$ A_a_prod_bool_fun$) A_bool_fun$)
(declare-fun fun_app$x (A_set_a_a_prod_bool_fun_a_bool_fun_fun_fun$ A_set$) A_a_prod_bool_fun_a_bool_fun_fun$)
(declare-fun lmember$a (A$ A_llist$) Bool)
(assert (! (forall ((?v0 A$)) (! (= (fun_app$ uu$ ?v0) (pair$ ?v0 ?v0)) :pattern ((fun_app$ uu$ ?v0)))) :named a0))
(assert (! (forall ((?v0 A_a_prod_set$) (?v1 A$) (?v2 A$)) (! (= (fun_app$a (fun_app$b (uus$ ?v0) ?v1) ?v2) (member$ (pair$ ?v1 ?v2) ?v0)) :pattern ((fun_app$a (fun_app$b (uus$ ?v0) ?v1) ?v2)))) :named a1))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$) (?v1 A_a_prod_a_a_prod_fun$) (?v2 A_a_prod$)) (! (= (fun_app$c (fun_app$d (uuh$ ?v0) ?v1) ?v2) (fun_app$c ?v0 (fun_app$c ?v1 ?v2))) :pattern ((fun_app$c (fun_app$d (uuh$ ?v0) ?v1) ?v2)))) :named a2))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$) (?v1 A_a_a_prod_fun$) (?v2 A$)) (! (= (fun_app$ (fun_app$e (uui$ ?v0) ?v1) ?v2) (fun_app$c ?v0 (fun_app$ ?v1 ?v2))) :pattern ((fun_app$ (fun_app$e (uui$ ?v0) ?v1) ?v2)))) :named a3))
(assert (! (forall ((?v0 A_a_prod_a_fun$) (?v1 A_a_prod_a_a_prod_fun$) (?v2 A_a_prod$)) (! (= (fun_app$f (fun_app$g (uud$ ?v0) ?v1) ?v2) (fun_app$f ?v0 (fun_app$c ?v1 ?v2))) :pattern ((fun_app$f (fun_app$g (uud$ ?v0) ?v1) ?v2)))) :named a4))
(assert (! (forall ((?v0 A_a_prod_a_fun$) (?v1 A_a_a_prod_fun$) (?v2 A$)) (! (= (fun_app$h (fun_app$i (uue$ ?v0) ?v1) ?v2) (fun_app$f ?v0 (fun_app$ ?v1 ?v2))) :pattern ((fun_app$h (fun_app$i (uue$ ?v0) ?v1) ?v2)))) :named a5))
(assert (! (forall ((?v0 A_a_a_prod_fun$) (?v1 A_a_prod_a_fun$) (?v2 A_a_prod$)) (! (= (fun_app$c (fun_app$j (uuf$ ?v0) ?v1) ?v2) (fun_app$ ?v0 (fun_app$f ?v1 ?v2))) :pattern ((fun_app$c (fun_app$j (uuf$ ?v0) ?v1) ?v2)))) :named a6))
(assert (! (forall ((?v0 A_a_a_prod_fun$) (?v1 A_a_fun$) (?v2 A$)) (! (= (fun_app$ (fun_app$k (uuj$ ?v0) ?v1) ?v2) (fun_app$ ?v0 (fun_app$h ?v1 ?v2))) :pattern ((fun_app$ (fun_app$k (uuj$ ?v0) ?v1) ?v2)))) :named a7))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_prod_a_fun$) (?v2 A_a_prod$)) (! (= (fun_app$f (fun_app$l (uuc$ ?v0) ?v1) ?v2) (fun_app$h ?v0 (fun_app$f ?v1 ?v2))) :pattern ((fun_app$f (fun_app$l (uuc$ ?v0) ?v1) ?v2)))) :named a8))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A$)) (! (= (fun_app$h (fun_app$m (uug$ ?v0) ?v1) ?v2) (fun_app$h ?v0 (fun_app$h ?v1 ?v2))) :pattern ((fun_app$h (fun_app$m (uug$ ?v0) ?v1) ?v2)))) :named a9))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$) (?v1 A_a_prod_set$) (?v2 A_a_prod_bool_fun$) (?v3 A_a_prod$)) (! (= (fun_app$n (fun_app$o (fun_app$p (uuk$ ?v0) ?v1) ?v2) ?v3) (and (member$ ?v3 (image$ ?v0 ?v1)) (fun_app$n ?v2 ?v3))) :pattern ((fun_app$n (fun_app$o (fun_app$p (uuk$ ?v0) ?v1) ?v2) ?v3)))) :named a10))
(assert (! (forall ((?v0 A_a_prod_a_fun$) (?v1 A_a_prod_set$) (?v2 A_bool_fun$) (?v3 A$)) (! (= (fun_app$a (fun_app$q (fun_app$r (uum$ ?v0) ?v1) ?v2) ?v3) (and (member$a ?v3 (image$a ?v0 ?v1)) (fun_app$a ?v2 ?v3))) :pattern ((fun_app$a (fun_app$q (fun_app$r (uum$ ?v0) ?v1) ?v2) ?v3)))) :named a11))
(assert (! (forall ((?v0 A_a_a_prod_fun$) (?v1 A_set$) (?v2 A_a_prod_bool_fun$) (?v3 A_a_prod$)) (! (= (fun_app$n (fun_app$o (fun_app$s (uuq$ ?v0) ?v1) ?v2) ?v3) (and (member$ ?v3 (image$b ?v0 ?v1)) (fun_app$n ?v2 ?v3))) :pattern ((fun_app$n (fun_app$o (fun_app$s (uuq$ ?v0) ?v1) ?v2) ?v3)))) :named a12))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_set$) (?v2 A_bool_fun$) (?v3 A$)) (! (= (fun_app$a (fun_app$q (fun_app$t (uuo$ ?v0) ?v1) ?v2) ?v3) (and (member$a ?v3 (image$c ?v0 ?v1)) (fun_app$a ?v2 ?v3))) :pattern ((fun_app$a (fun_app$q (fun_app$t (uuo$ ?v0) ?v1) ?v2) ?v3)))) :named a13))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$) (?v1 A_a_prod_set$) (?v2 A_a_prod_bool_fun$) (?v3 A_a_prod$)) (! (= (fun_app$n (fun_app$o (fun_app$p (uul$ ?v0) ?v1) ?v2) ?v3) (and (member$ ?v3 ?v1) (fun_app$n ?v2 (fun_app$c ?v0 ?v3)))) :pattern ((fun_app$n (fun_app$o (fun_app$p (uul$ ?v0) ?v1) ?v2) ?v3)))) :named a14))
(assert (! (forall ((?v0 A_a_prod_a_fun$) (?v1 A_a_prod_set$) (?v2 A_bool_fun$) (?v3 A_a_prod$)) (! (= (fun_app$n (fun_app$u (fun_app$v (uun$ ?v0) ?v1) ?v2) ?v3) (and (member$ ?v3 ?v1) (fun_app$a ?v2 (fun_app$f ?v0 ?v3)))) :pattern ((fun_app$n (fun_app$u (fun_app$v (uun$ ?v0) ?v1) ?v2) ?v3)))) :named a15))
(assert (! (forall ((?v0 A_a_a_prod_fun$) (?v1 A_set$) (?v2 A_a_prod_bool_fun$) (?v3 A$)) (! (= (fun_app$a (fun_app$w (fun_app$x (uur$ ?v0) ?v1) ?v2) ?v3) (and (member$a ?v3 ?v1) (fun_app$n ?v2 (fun_app$ ?v0 ?v3)))) :pattern ((fun_app$a (fun_app$w (fun_app$x (uur$ ?v0) ?v1) ?v2) ?v3)))) :named a16))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_set$) (?v2 A_bool_fun$) (?v3 A$)) (! (= (fun_app$a (fun_app$q (fun_app$t (uup$ ?v0) ?v1) ?v2) ?v3) (and (member$a ?v3 ?v1) (fun_app$a ?v2 (fun_app$h ?v0 ?v3)))) :pattern ((fun_app$a (fun_app$q (fun_app$t (uup$ ?v0) ?v1) ?v2) ?v3)))) :named a17))
(assert (! (forall ((?v0 A_a_prod$)) (! (= (fun_app$c uub$ ?v0) ?v0) :pattern ((fun_app$c uub$ ?v0)))) :named a18))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$h uua$ ?v0) ?v0) :pattern ((fun_app$h uua$ ?v0)))) :named a19))
(assert (! (not (= (lset$ (lzip$ xs$ xs$)) (image$b uu$ (lset$a xs$)))) :named a20))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A_llist$) (?v3 A_llist$)) (=> (member$ (pair$ ?v0 ?v1) (lset$ (lzip$ ?v2 ?v3))) (member$a ?v1 (lset$a ?v3)))) :named a21))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A_llist$) (?v3 A_llist$)) (=> (member$ (pair$ ?v0 ?v1) (lset$ (lzip$ ?v2 ?v3))) (member$a ?v0 (lset$a ?v2)))) :named a22))
(assert (! (forall ((?v0 A_set$)) (= (image$c uua$ ?v0) ?v0)) :named a23))
(assert (! (forall ((?v0 A_a_prod_set$)) (= (image$ uub$ ?v0) ?v0)) :named a24))
(assert (! (forall ((?v0 A_a_prod$) (?v1 A_a_prod_a_a_prod_fun$) (?v2 A_a_prod$) (?v3 A_a_prod_set$)) (=> (and (= ?v0 (fun_app$c ?v1 ?v2)) (member$ ?v2 ?v3)) (member$ ?v0 (image$ ?v1 ?v3)))) :named a25))
(assert (! (forall ((?v0 A$) (?v1 A_a_prod_a_fun$) (?v2 A_a_prod$) (?v3 A_a_prod_set$)) (=> (and (= ?v0 (fun_app$f ?v1 ?v2)) (member$ ?v2 ?v3)) (member$a ?v0 (image$a ?v1 ?v3)))) :named a26))
(assert (! (forall ((?v0 A$) (?v1 A_a_fun$) (?v2 A$) (?v3 A_set$)) (=> (and (= ?v0 (fun_app$h ?v1 ?v2)) (member$a ?v2 ?v3)) (member$a ?v0 (image$c ?v1 ?v3)))) :named a27))
(assert (! (forall ((?v0 A_a_prod$) (?v1 A_a_a_prod_fun$) (?v2 A$) (?v3 A_set$)) (=> (and (= ?v0 (fun_app$ ?v1 ?v2)) (member$a ?v2 ?v3)) (member$ ?v0 (image$b ?v1 ?v3)))) :named a28))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A$) (?v3 A$)) (= (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a29))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A$) (?v3 A$)) (= (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a30))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_prod_a_fun$) (?v2 A_a_prod_set$)) (= (image$c ?v0 (image$a ?v1 ?v2)) (image$a (fun_app$l (uuc$ ?v0) ?v1) ?v2))) :named a31))
(assert (! (forall ((?v0 A_a_prod_a_fun$) (?v1 A_a_prod_a_a_prod_fun$) (?v2 A_a_prod_set$)) (= (image$a ?v0 (image$ ?v1 ?v2)) (image$a (fun_app$g (uud$ ?v0) ?v1) ?v2))) :named a32))
(assert (! (forall ((?v0 A_a_prod_a_fun$) (?v1 A_a_a_prod_fun$) (?v2 A_set$)) (= (image$a ?v0 (image$b ?v1 ?v2)) (image$c (fun_app$i (uue$ ?v0) ?v1) ?v2))) :named a33))
(assert (! (forall ((?v0 A_a_a_prod_fun$) (?v1 A_a_prod_a_fun$) (?v2 A_a_prod_set$)) (= (image$b ?v0 (image$a ?v1 ?v2)) (image$ (fun_app$j (uuf$ ?v0) ?v1) ?v2))) :named a34))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_set$)) (= (image$c ?v0 (image$c ?v1 ?v2)) (image$c (fun_app$m (uug$ ?v0) ?v1) ?v2))) :named a35))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$) (?v1 A_a_prod_a_a_prod_fun$) (?v2 A_a_prod_set$)) (= (image$ ?v0 (image$ ?v1 ?v2)) (image$ (fun_app$d (uuh$ ?v0) ?v1) ?v2))) :named a36))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$) (?v1 A_a_a_prod_fun$) (?v2 A_set$)) (= (image$ ?v0 (image$b ?v1 ?v2)) (image$b (fun_app$e (uui$ ?v0) ?v1) ?v2))) :named a37))
(assert (! (forall ((?v0 A_a_a_prod_fun$) (?v1 A_a_fun$) (?v2 A_set$)) (= (image$b ?v0 (image$c ?v1 ?v2)) (image$b (fun_app$k (uuj$ ?v0) ?v1) ?v2))) :named a38))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$) (?v1 A_a_prod_set$) (?v2 A_a_prod_bool_fun$)) (= (collect$ (fun_app$o (fun_app$p (uuk$ ?v0) ?v1) ?v2)) (image$ ?v0 (collect$ (fun_app$o (fun_app$p (uul$ ?v0) ?v1) ?v2))))) :named a39))
(assert (! (forall ((?v0 A_a_prod_a_fun$) (?v1 A_a_prod_set$) (?v2 A_bool_fun$)) (= (collect$a (fun_app$q (fun_app$r (uum$ ?v0) ?v1) ?v2)) (image$a ?v0 (collect$ (fun_app$u (fun_app$v (uun$ ?v0) ?v1) ?v2))))) :named a40))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_set$) (?v2 A_bool_fun$)) (= (collect$a (fun_app$q (fun_app$t (uuo$ ?v0) ?v1) ?v2)) (image$c ?v0 (collect$a (fun_app$q (fun_app$t (uup$ ?v0) ?v1) ?v2))))) :named a41))
(assert (! (forall ((?v0 A_a_a_prod_fun$) (?v1 A_set$) (?v2 A_a_prod_bool_fun$)) (= (collect$ (fun_app$o (fun_app$s (uuq$ ?v0) ?v1) ?v2)) (image$b ?v0 (collect$a (fun_app$w (fun_app$x (uur$ ?v0) ?v1) ?v2))))) :named a42))
(assert (! (forall ((?v0 A_a_prod$) (?v1 A_a_prod_a_a_prod_fun$) (?v2 A_a_prod_set$)) (=> (and (member$ ?v0 (image$ ?v1 ?v2)) (forall ((?v3 A_a_prod$)) (=> (and (= ?v0 (fun_app$c ?v1 ?v3)) (member$ ?v3 ?v2)) false))) false)) :named a43))
(assert (! (forall ((?v0 A$) (?v1 A_a_prod_a_fun$) (?v2 A_a_prod_set$)) (=> (and (member$a ?v0 (image$a ?v1 ?v2)) (forall ((?v3 A_a_prod$)) (=> (and (= ?v0 (fun_app$f ?v1 ?v3)) (member$ ?v3 ?v2)) false))) false)) :named a44))
(assert (! (forall ((?v0 A$) (?v1 A_a_fun$) (?v2 A_set$)) (=> (and (member$a ?v0 (image$c ?v1 ?v2)) (forall ((?v3 A$)) (=> (and (= ?v0 (fun_app$h ?v1 ?v3)) (member$a ?v3 ?v2)) false))) false)) :named a45))
(assert (! (forall ((?v0 A_a_prod$) (?v1 A_a_a_prod_fun$) (?v2 A_set$)) (=> (and (member$ ?v0 (image$b ?v1 ?v2)) (forall ((?v3 A$)) (=> (and (= ?v0 (fun_app$ ?v1 ?v3)) (member$a ?v3 ?v2)) false))) false)) :named a46))
(assert (! (forall ((?v0 A_a_prod_set$) (?v1 A_a_prod_set$)) (= (= (uus$ ?v0) (uus$ ?v1)) (= ?v0 ?v1))) :named a47))
(assert (! (forall ((?v0 A_a_prod$) (?v1 A_a_prod_llist$)) (= (member$ ?v0 (lset$ ?v1)) (lmember$ ?v0 ?v1))) :named a48))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (= (member$a ?v0 (lset$a ?v1)) (lmember$a ?v0 ?v1))) :named a49))
(assert (! (forall ((?v0 A_a_prod$) (?v1 A_a_prod_a_a_prod_fun$) (?v2 A_a_prod_set$)) (= (member$ ?v0 (image$ ?v1 ?v2)) (exists ((?v3 A_a_prod$)) (and (member$ ?v3 ?v2) (= ?v0 (fun_app$c ?v1 ?v3)))))) :named a50))
(assert (! (forall ((?v0 A$) (?v1 A_a_prod_a_fun$) (?v2 A_a_prod_set$)) (= (member$a ?v0 (image$a ?v1 ?v2)) (exists ((?v3 A_a_prod$)) (and (member$ ?v3 ?v2) (= ?v0 (fun_app$f ?v1 ?v3)))))) :named a51))
(assert (! (forall ((?v0 A$) (?v1 A_a_fun$) (?v2 A_set$)) (= (member$a ?v0 (image$c ?v1 ?v2)) (exists ((?v3 A$)) (and (member$a ?v3 ?v2) (= ?v0 (fun_app$h ?v1 ?v3)))))) :named a52))
(assert (! (forall ((?v0 A_a_prod$) (?v1 A_a_a_prod_fun$) (?v2 A_set$)) (= (member$ ?v0 (image$b ?v1 ?v2)) (exists ((?v3 A$)) (and (member$a ?v3 ?v2) (= ?v0 (fun_app$ ?v1 ?v3)))))) :named a53))
(assert (! (forall ((?v0 A_a_prod_set$) (?v1 A_a_prod_set$) (?v2 A_a_prod_a_fun$) (?v3 A_a_prod_a_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 A_a_prod$)) (=> (member$ ?v4 ?v1) (= (fun_app$f ?v2 ?v4) (fun_app$f ?v3 ?v4))))) (= (image$a ?v2 ?v0) (image$a ?v3 ?v1)))) :named a54))
(assert (! (forall ((?v0 A_a_prod_set$) (?v1 A_a_prod_set$) (?v2 A_a_prod_a_a_prod_fun$) (?v3 A_a_prod_a_a_prod_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 A_a_prod$)) (=> (member$ ?v4 ?v1) (= (fun_app$c ?v2 ?v4) (fun_app$c ?v3 ?v4))))) (= (image$ ?v2 ?v0) (image$ ?v3 ?v1)))) :named a55))
(assert (! (forall ((?v0 A_set$) (?v1 A_set$) (?v2 A_a_fun$) (?v3 A_a_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 A$)) (=> (member$a ?v4 ?v1) (= (fun_app$h ?v2 ?v4) (fun_app$h ?v3 ?v4))))) (= (image$c ?v2 ?v0) (image$c ?v3 ?v1)))) :named a56))
(assert (! (forall ((?v0 A_set$) (?v1 A_set$) (?v2 A_a_a_prod_fun$) (?v3 A_a_a_prod_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 A$)) (=> (member$a ?v4 ?v1) (= (fun_app$ ?v2 ?v4) (fun_app$ ?v3 ?v4))))) (= (image$b ?v2 ?v0) (image$b ?v3 ?v1)))) :named a57))
(assert (! (forall ((?v0 A_a_prod_a_a_prod_fun$) (?v1 A_a_prod_set$) (?v2 A_a_prod_bool_fun$)) (=> (exists ((?v3 A_a_prod$)) (and (member$ ?v3 (image$ ?v0 ?v1)) (fun_app$n ?v2 ?v3))) (exists ((?v3 A_a_prod$)) (and (member$ ?v3 ?v1) (fun_app$n ?v2 (fun_app$c ?v0 ?v3)))))) :named a58))
(assert (! (forall ((?v0 A_a_prod_a_fun$) (?v1 A_a_prod_set$) (?v2 A_bool_fun$)) (=> (exists ((?v3 A$)) (and (member$a ?v3 (image$a ?v0 ?v1)) (fun_app$a ?v2 ?v3))) (exists ((?v3 A_a_prod$)) (and (member$ ?v3 ?v1) (fun_app$a ?v2 (fun_app$f ?v0 ?v3)))))) :named a59))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_set$) (?v2 A_bool_fun$)) (=> (exists ((?v3 A$)) (and (member$a ?v3 (image$c ?v0 ?v1)) (fun_app$a ?v2 ?v3))) (exists ((?v3 A$)) (and (member$a ?v3 ?v1) (fun_app$a ?v2 (fun_app$h ?v0 ?v3)))))) :named a60))
(assert (! (forall ((?v0 A_a_a_prod_fun$) (?v1 A_set$) (?v2 A_a_prod_bool_fun$)) (=> (exists ((?v3 A_a_prod$)) (and (member$ ?v3 (image$b ?v0 ?v1)) (fun_app$n ?v2 ?v3))) (exists ((?v3 A$)) (and (member$a ?v3 ?v1) (fun_app$n ?v2 (fun_app$ ?v0 ?v3)))))) :named a61))
(assert (! (forall ((?v0 A_a_prod$)) (exists ((?v1 A$) (?v2 A$)) (= ?v0 (pair$ ?v1 ?v2)))) :named a62))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A$) (?v3 A$)) (=> (and (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (=> (and (= ?v0 ?v2) (= ?v1 ?v3)) false)) false)) :named a63))
(assert (! (forall ((?v0 A_a_prod$)) (=> (forall ((?v1 A$) (?v2 A$)) (=> (= ?v0 (pair$ ?v1 ?v2)) false)) false)) :named a64))
(check-sat)
;(get-unsat-core)
