; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 297
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort A_llist_a_llist_prod_set$ 0)
(declare-sort A_llist_a_llist_bool_fun_fun$ 0)
(declare-sort A_llist_a_llist_prod_bool_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-datatypes () ((A_llist_a_llist_prod$ (pair$ (fst$ A_llist$) (snd$ A_llist$)))))
(declare-fun p$ () A_llist_a_llist_bool_fun_fun$)
(declare-fun xs$ () A_llist$)
(declare-fun ys$ () A_llist$)
(declare-fun lnull$ (A_llist$) Bool)
(declare-fun member$ (A_llist_a_llist_prod$ A_llist_a_llist_prod_set$) Bool)
(declare-fun collect$ (A_llist_a_llist_prod_bool_fun$) A_llist_a_llist_prod_set$)
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun lprefix$ (A_llist$ A_llist$) Bool)
(declare-fun fun_app$a (A_llist_a_llist_bool_fun_fun$ A_llist$) A_llist_bool_fun$)
(declare-fun case_prod$ (A_llist_a_llist_bool_fun_fun$) A_llist_a_llist_prod_bool_fun$)
(assert (! (not (lprefix$ xs$ ys$)) :named a0))
(assert (! (fun_app$ (fun_app$a p$ xs$) ys$) :named a1))
(assert (! (member$ (pair$ xs$ ys$) (collect$ (case_prod$ p$))) :named a2))
(assert (! (forall ((?v0 A_llist$)) (lprefix$ lNil$ ?v0)) :named a3))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A$)) (=> (lprefix$ ?v0 ?v1) (lprefix$ (lCons$ ?v2 ?v0) (lCons$ ?v2 ?v1)))) :named a4))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (fun_app$ (fun_app$a p$ ?v0) ?v1) (and (=> (lnull$ ?v1) (lnull$ ?v0)) (=> (and (not (lnull$ ?v0)) (not (lnull$ ?v1))) (and (= (lhd$ ?v0) (lhd$ ?v1)) (or (fun_app$ (fun_app$a p$ (ltl$ ?v0)) (ltl$ ?v1)) (lprefix$ (ltl$ ?v0) (ltl$ ?v1)))))))) :named a5))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (lprefix$ ?v0 ?v1) (or (exists ((?v2 A_llist$)) (and (= ?v0 lNil$) (= ?v1 ?v2))) (exists ((?v2 A_llist$) (?v3 A_llist$) (?v4 A$)) (and (= ?v0 (lCons$ ?v4 ?v2)) (and (= ?v1 (lCons$ ?v4 ?v3)) (lprefix$ ?v2 ?v3))))))) :named a6))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (=> (and (lprefix$ ?v0 ?v1) (and (forall ((?v2 A_llist$)) (=> (and (= ?v0 lNil$) (= ?v1 ?v2)) false)) (forall ((?v2 A_llist$) (?v3 A_llist$) (?v4 A$)) (=> (and (= ?v0 (lCons$ ?v4 ?v2)) (and (= ?v1 (lCons$ ?v4 ?v3)) (lprefix$ ?v2 ?v3))) false)))) false)) :named a7))
(assert (! (forall ((?v0 A_llist_a_llist_bool_fun_fun$) (?v1 A_llist$) (?v2 A_llist$)) (=> (and (fun_app$ (fun_app$a ?v0 ?v1) ?v2) (forall ((?v3 A_llist$) (?v4 A_llist$)) (=> (fun_app$ (fun_app$a ?v0 ?v3) ?v4) (or (exists ((?v5 A_llist$)) (and (= ?v3 lNil$) (= ?v4 ?v5))) (exists ((?v5 A_llist$) (?v6 A_llist$) (?v7 A$)) (and (= ?v3 (lCons$ ?v7 ?v5)) (and (= ?v4 (lCons$ ?v7 ?v6)) (or (fun_app$ (fun_app$a ?v0 ?v5) ?v6) (lprefix$ ?v5 ?v6))))))))) (lprefix$ ?v1 ?v2))) :named a8))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist_a_llist_prod_set$)) (=> (and (member$ (pair$ ?v0 ?v1) ?v2) (forall ((?v3 A_llist$) (?v4 A_llist$)) (=> (member$ (pair$ ?v3 ?v4) ?v2) (or (lnull$ ?v3) (exists ((?v5 A$) (?v6 A_llist$) (?v7 A_llist$)) (and (= ?v3 (lCons$ ?v5 ?v6)) (and (= ?v4 (lCons$ ?v5 ?v7)) (or (member$ (pair$ ?v6 ?v7) ?v2) (lprefix$ ?v6 ?v7))))))))) (lprefix$ ?v0 ?v1))) :named a9))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a10))
(assert (! (forall ((?v0 A_llist$)) (=> (not (lnull$ ?v0)) (= (lCons$ (lhd$ ?v0) (ltl$ ?v0)) ?v0))) :named a11))
(assert (! (forall ((?v0 A_llist$)) (= (not (= ?v0 lNil$)) (exists ((?v1 A$) (?v2 A_llist$)) (= ?v0 (lCons$ ?v1 ?v2))))) :named a12))
(assert (! (forall ((?v0 A_llist$)) (= (not (lnull$ ?v0)) (exists ((?v1 A$) (?v2 A_llist$)) (= ?v0 (lCons$ ?v1 ?v2))))) :named a13))
(assert (! (forall ((?v0 A_llist$)) (! (= (lnull$ ?v0) (= ?v0 lNil$)) :pattern ((lnull$ ?v0)))) :named a14))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lhd$ (lCons$ ?v0 ?v1)) ?v0) :pattern ((lCons$ ?v0 ?v1)))) :named a15))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (ltl$ (lCons$ ?v0 ?v1)) ?v1) :pattern ((lCons$ ?v0 ?v1)))) :named a16))
(assert (! (= (ltl$ lNil$) lNil$) :named a17))
(check-sat)
;(get-unsat-core)
