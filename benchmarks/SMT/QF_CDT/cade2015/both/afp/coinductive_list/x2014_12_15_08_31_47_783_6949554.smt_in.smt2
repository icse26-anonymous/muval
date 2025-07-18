; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 602
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort A_llist_set$ 0)
(declare-sort A_llist_bool_fun$ 0)
(declare-sort A_llist_llist_bool_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))
  (A_llist_llist$ (lNil$a) (lCons$a (lhd$a A_llist$) (ltl$a A_llist_llist$)))))
(declare-datatypes () ((A_llist_list$ (nil$) (cons$ (hd$ A_llist$) (tl$ A_llist_list$)))))
(declare-codatatypes () ((A_llist_llist_llist$ (lNil$b) (lCons$b (lhd$b A_llist_llist$) (ltl$b A_llist_llist_llist$)))
  (A_llist_llist_llist_llist$ (lNil$c) (lCons$c (lhd$c A_llist_llist_llist$) (ltl$c A_llist_llist_llist_llist$)))))
(declare-fun x$ () A$)
(declare-fun xs$ () A_llist$)
(declare-fun set$ (A_llist_list$) A_llist_set$)
(declare-fun xs$a () A_llist$)
(declare-fun xss$ () A_llist_llist$)
(declare-fun xss$a () A_llist_list$)
(declare-fun xss$b () A_llist_llist$)
(declare-fun lnull$ () A_llist_bool_fun$)
(declare-fun lsetp$ (A_llist_llist_llist$) A_llist_llist_bool_fun$)
(declare-fun lnull$a (A_llist_llist_llist$) Bool)
(declare-fun lnull$b (A_llist_llist$) Bool)
(declare-fun lsetp$a (A_llist$) A_bool_fun$)
(declare-fun lsetp$b (A_llist_llist$) A_llist_bool_fun$)
(declare-fun collect$ (A_llist_bool_fun$) A_llist_set$)
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$) Bool)
(declare-fun lappend$ (A_llist$ A_llist$) A_llist$)
(declare-fun lconcat$ (A_llist_llist$) A_llist$)
(declare-fun less_eq$ (A_llist_set$ A_llist_set$) Bool)
(declare-fun lmember$ (A_llist_llist$ A_llist_llist_llist$) Bool)
(declare-fun fun_app$a (A_llist_llist_bool_fun$ A_llist_llist$) Bool)
(declare-fun fun_app$b (A_bool_fun$ A$) Bool)
(declare-fun lappend$a (A_llist_llist$ A_llist_llist$) A_llist_llist$)
(declare-fun lappend$b (A_llist_llist_llist$ A_llist_llist_llist$) A_llist_llist_llist$)
(declare-fun lconcat$a (A_llist_llist_llist_llist$) A_llist_llist_llist$)
(declare-fun lconcat$b (A_llist_llist_llist$) A_llist_llist$)
(declare-fun llist_of$ (A_llist_list$) A_llist_llist$)
(declare-fun lmember$a (A$) A_llist_bool_fun$)
(declare-fun lmember$b (A_llist$) A_llist_llist_bool_fun$)
(declare-fun pred_llist$ (A_llist_llist_bool_fun$ A_llist_llist_llist$) Bool)
(declare-fun pred_llist$a (A_bool_fun$) A_llist_bool_fun$)
(declare-fun pred_llist$b (A_llist_bool_fun$) A_llist_llist_bool_fun$)
(declare-fun lstrict_prefix$ (A_llist_llist_llist$ A_llist_llist_llist$) Bool)
(declare-fun lstrict_prefix$a (A_llist$) A_llist_bool_fun$)
(declare-fun lstrict_prefix$b (A_llist_llist$) A_llist_llist_bool_fun$)
(assert (! (not (= (lconcat$ xss$) (lCons$ x$ xs$))) :named a0))
(assert (! (fun_app$ lnull$ (lconcat$ (llist_of$ xss$a))) :named a1))
(assert (! (= xs$ (lappend$ xs$a (lconcat$ xss$b))) :named a2))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist_llist$) (?v2 A_llist_llist$) (?v3 A_llist_llist_llist$)) (= (= (lCons$b ?v0 ?v1) (lCons$b ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a3))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a4))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (= (= (lCons$a ?v0 ?v1) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a5))
(assert (! (= xss$ (lappend$a (llist_of$ xss$a) (lCons$a (lCons$ x$ xs$a) xss$b))) :named a6))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist_llist$) (?v2 A_llist_llist_llist$)) (! (= (lappend$b (lCons$b ?v0 ?v1) ?v2) (lCons$b ?v0 (lappend$b ?v1 ?v2))) :pattern ((lappend$b (lCons$b ?v0 ?v1) ?v2)))) :named a7))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A_llist$)) (! (= (lappend$ (lCons$ ?v0 ?v1) ?v2) (lCons$ ?v0 (lappend$ ?v1 ?v2))) :pattern ((lappend$ (lCons$ ?v0 ?v1) ?v2)))) :named a8))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist_llist$)) (! (= (lappend$a (lCons$a ?v0 ?v1) ?v2) (lCons$a ?v0 (lappend$a ?v1 ?v2))) :pattern ((lappend$a (lCons$a ?v0 ?v1) ?v2)))) :named a9))
(assert (! (forall ((?v0 A_llist_llist_llist$)) (= (not (lnull$a ?v0)) (exists ((?v1 A_llist_llist$) (?v2 A_llist_llist_llist$)) (= ?v0 (lCons$b ?v1 ?v2))))) :named a10))
(assert (! (forall ((?v0 A_llist_llist$)) (= (not (lnull$b ?v0)) (exists ((?v1 A_llist$) (?v2 A_llist_llist$)) (= ?v0 (lCons$a ?v1 ?v2))))) :named a11))
(assert (! (forall ((?v0 A_llist$)) (= (not (fun_app$ lnull$ ?v0)) (exists ((?v1 A$) (?v2 A_llist$)) (= ?v0 (lCons$ ?v1 ?v2))))) :named a12))
(assert (! (forall ((?v0 A_llist_llist_llist$) (?v1 A_llist_llist$) (?v2 A_llist_llist_llist$)) (=> (= ?v0 (lCons$b ?v1 ?v2)) (not (lnull$a ?v0)))) :named a13))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist$) (?v2 A_llist_llist$)) (=> (= ?v0 (lCons$a ?v1 ?v2)) (not (lnull$b ?v0)))) :named a14))
(assert (! (forall ((?v0 A_llist$) (?v1 A$) (?v2 A_llist$)) (=> (= ?v0 (lCons$ ?v1 ?v2)) (not (fun_app$ lnull$ ?v0)))) :named a15))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist_llist$)) (not (lnull$a (lCons$b ?v0 ?v1)))) :named a16))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (not (lnull$b (lCons$a ?v0 ?v1)))) :named a17))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (not (fun_app$ lnull$ (lCons$ ?v0 ?v1)))) :named a18))
(assert (! (forall ((?v0 A_llist_list$) (?v1 A_llist_list$)) (= (= (llist_of$ ?v0) (llist_of$ ?v1)) (= ?v0 ?v1))) :named a19))
(assert (! (forall ((?v0 A_llist_llist_llist$) (?v1 A_llist_llist_llist_llist$)) (! (= (lconcat$a (lCons$c ?v0 ?v1)) (lappend$b ?v0 (lconcat$a ?v1))) :pattern ((lCons$c ?v0 ?v1)))) :named a20))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist_llist$)) (! (= (lconcat$b (lCons$b ?v0 ?v1)) (lappend$a ?v0 (lconcat$b ?v1))) :pattern ((lCons$b ?v0 ?v1)))) :named a21))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$)) (! (= (lconcat$ (lCons$a ?v0 ?v1)) (lappend$ ?v0 (lconcat$ ?v1))) :pattern ((lCons$a ?v0 ?v1)))) :named a22))
(assert (! (forall ((?v0 A_llist_llist_bool_fun$) (?v1 A_llist_llist$) (?v2 A_llist_llist_llist$)) (! (= (pred_llist$ ?v0 (lCons$b ?v1 ?v2)) (and (fun_app$a ?v0 ?v1) (pred_llist$ ?v0 ?v2))) :pattern ((pred_llist$ ?v0 (lCons$b ?v1 ?v2))))) :named a23))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$ (pred_llist$a ?v0) (lCons$ ?v1 ?v2)) (and (fun_app$b ?v0 ?v1) (fun_app$ (pred_llist$a ?v0) ?v2))) :pattern ((fun_app$ (pred_llist$a ?v0) (lCons$ ?v1 ?v2))))) :named a24))
(assert (! (forall ((?v0 A_llist_bool_fun$) (?v1 A_llist$) (?v2 A_llist_llist$)) (! (= (fun_app$a (pred_llist$b ?v0) (lCons$a ?v1 ?v2)) (and (fun_app$ ?v0 ?v1) (fun_app$a (pred_llist$b ?v0) ?v2))) :pattern ((fun_app$a (pred_llist$b ?v0) (lCons$a ?v1 ?v2))))) :named a25))
(assert (! (exists ((?v0 A_llist$) (?v1 A_llist_list$) (?v2 A_llist_llist$)) (and (= xss$ (lappend$a (llist_of$ ?v1) (lCons$a (lCons$ x$ ?v0) ?v2))) (and (= xs$ (lappend$ ?v0 (lconcat$ ?v2))) (less_eq$ (set$ ?v1) (collect$ lnull$))))) :named a26))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist$) (?v2 A_llist_llist_llist$)) (! (= (lmember$ ?v0 (lCons$b ?v1 ?v2)) (or (= ?v0 ?v1) (lmember$ ?v0 ?v2))) :pattern ((lmember$ ?v0 (lCons$b ?v1 ?v2))))) :named a27))
(assert (! (forall ((?v0 A$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$ (lmember$a ?v0) (lCons$ ?v1 ?v2)) (or (= ?v0 ?v1) (fun_app$ (lmember$a ?v0) ?v2))) :pattern ((fun_app$ (lmember$a ?v0) (lCons$ ?v1 ?v2))))) :named a28))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_llist_llist$)) (! (= (fun_app$a (lmember$b ?v0) (lCons$a ?v1 ?v2)) (or (= ?v0 ?v1) (fun_app$a (lmember$b ?v0) ?v2))) :pattern ((fun_app$a (lmember$b ?v0) (lCons$a ?v1 ?v2))))) :named a29))
(assert (! (=> (forall ((?v0 A_llist$) (?v1 A_llist_list$) (?v2 A_llist_llist$)) (=> (and (= xss$ (lappend$a (llist_of$ ?v1) (lCons$a (lCons$ x$ ?v0) ?v2))) (and (= xs$ (lappend$ ?v0 (lconcat$ ?v2))) (less_eq$ (set$ ?v1) (collect$ lnull$)))) false)) false) :named a30))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist_llist_llist$) (?v2 A_llist_llist$) (?v3 A_llist_llist_llist$)) (! (= (lstrict_prefix$ (lCons$b ?v0 ?v1) (lCons$b ?v2 ?v3)) (and (= ?v0 ?v2) (lstrict_prefix$ ?v1 ?v3))) :pattern ((lstrict_prefix$ (lCons$b ?v0 ?v1) (lCons$b ?v2 ?v3))))) :named a31))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (! (= (fun_app$ (lstrict_prefix$a (lCons$ ?v0 ?v1)) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (fun_app$ (lstrict_prefix$a ?v1) ?v3))) :pattern ((fun_app$ (lstrict_prefix$a (lCons$ ?v0 ?v1)) (lCons$ ?v2 ?v3))))) :named a32))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist_llist$) (?v2 A_llist$) (?v3 A_llist_llist$)) (! (= (fun_app$a (lstrict_prefix$b (lCons$a ?v0 ?v1)) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (fun_app$a (lstrict_prefix$b ?v1) ?v3))) :pattern ((fun_app$a (lstrict_prefix$b (lCons$a ?v0 ?v1)) (lCons$a ?v2 ?v3))))) :named a33))
(assert (! (forall ((?v0 A_llist_llist_llist$) (?v1 A_llist_llist$)) (= (fun_app$a (lsetp$ ?v0) ?v1) (or (exists ((?v2 A_llist_llist$) (?v3 A_llist_llist_llist$)) (and (= ?v0 (lCons$b ?v2 ?v3)) (= ?v1 ?v2))) (exists ((?v2 A_llist_llist_llist$) (?v3 A_llist_llist$) (?v4 A_llist_llist$)) (and (= ?v0 (lCons$b ?v4 ?v2)) (and (= ?v1 ?v3) (fun_app$a (lsetp$ ?v2) ?v3))))))) :named a34))
(assert (! (forall ((?v0 A_llist$) (?v1 A$)) (= (fun_app$b (lsetp$a ?v0) ?v1) (or (exists ((?v2 A$) (?v3 A_llist$)) (and (= ?v0 (lCons$ ?v2 ?v3)) (= ?v1 ?v2))) (exists ((?v2 A_llist$) (?v3 A$) (?v4 A$)) (and (= ?v0 (lCons$ ?v4 ?v2)) (and (= ?v1 ?v3) (fun_app$b (lsetp$a ?v2) ?v3))))))) :named a35))
(assert (! (forall ((?v0 A_llist_llist$) (?v1 A_llist$)) (= (fun_app$ (lsetp$b ?v0) ?v1) (or (exists ((?v2 A_llist$) (?v3 A_llist_llist$)) (and (= ?v0 (lCons$a ?v2 ?v3)) (= ?v1 ?v2))) (exists ((?v2 A_llist_llist$) (?v3 A_llist$) (?v4 A_llist$)) (and (= ?v0 (lCons$a ?v4 ?v2)) (and (= ?v1 ?v3) (fun_app$ (lsetp$b ?v2) ?v3))))))) :named a36))
(assert (! (less_eq$ (set$ xss$a) (collect$ lnull$)) :named a37))
(check-sat)
;(get-unsat-core)
