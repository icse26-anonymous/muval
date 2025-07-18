; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 195
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort N$ 0)
(declare-sort Dtree$ 0)
(declare-sort N_set$ 0)
(declare-sort N_bool_fun$ 0)
(declare-sort N_dtree_fun$ 0)
(declare-sort N_bool_fun_N_bool_fun_fun$ 0)
(declare-datatypes () ((N_list$ (nil$) (cons$ (hd$ N$) (tl$ N_list$)))))
(declare-fun f$ () N_dtree_fun$)
(declare-fun nl$ () N_list$)
(declare-fun tr$ () Dtree$)
(declare-fun uu$ (N_bool_fun$) N_bool_fun_N_bool_fun_fun$)
(declare-fun nsa$ () N_set$)
(declare-fun reg$ (N_dtree_fun$ Dtree$) Bool)
(declare-fun set$ (N_list$) N_set$)
(declare-fun tr2$ () Dtree$)
(declare-fun tra$ () Dtree$)
(declare-fun last$ (N_list$) N$)
(declare-fun path$ (N_dtree_fun$ N_list$) Bool)
(declare-fun root$ (Dtree$) N$)
(declare-fun tr1a$ () Dtree$)
(declare-fun subtr$ (N_set$ Dtree$ Dtree$) Bool)
(declare-fun member$ (N$ N_set$) Bool)
(declare-fun collect$ (N_bool_fun$) N_set$)
(declare-fun fun_app$ (N_bool_fun$ N$) Bool)
(declare-fun less_eq$ (N_set$ N_set$) Bool)
(declare-fun distinct$ (N_list$) Bool)
(declare-fun fun_app$a (N_bool_fun_N_bool_fun_fun$ N_bool_fun$) N_bool_fun$)
(declare-fun fun_app$b (N_dtree_fun$ N$) Dtree$)
(assert (! (forall ((?v0 N_bool_fun$) (?v1 N_bool_fun$) (?v2 N$)) (! (= (fun_app$ (fun_app$a (uu$ ?v0) ?v1) ?v2) (and (fun_app$ ?v0 ?v2) (fun_app$ ?v1 ?v2))) :pattern ((fun_app$ (fun_app$a (uu$ ?v0) ?v1) ?v2)))) :named a0))
(assert (! (not (exists ((?v0 N_list$)) (and (path$ f$ ?v0) (and (= (fun_app$b f$ (hd$ ?v0)) tra$) (and (= (fun_app$b f$ (last$ ?v0)) tr2$) (less_eq$ (set$ ?v0) nsa$)))))) :named a1))
(assert (! (path$ f$ nl$) :named a2))
(assert (! (less_eq$ (set$ nl$) nsa$) :named a3))
(assert (! (reg$ f$ tra$) :named a4))
(assert (! (= (fun_app$b f$ (last$ nl$)) tr2$) :named a5))
(assert (! (reg$ f$ tr$) :named a6))
(assert (! (member$ (root$ tra$) nsa$) :named a7))
(assert (! (=> (forall ((?v0 N_list$)) (=> (and (path$ f$ ?v0) (and (= (fun_app$b f$ (hd$ ?v0)) tr1a$) (and (= (fun_app$b f$ (last$ ?v0)) tr2$) (less_eq$ (set$ ?v0) nsa$)))) false)) false) :named a8))
(assert (! (=> (reg$ f$ tr1a$) (exists ((?v0 N_list$)) (and (path$ f$ ?v0) (and (= (fun_app$b f$ (hd$ ?v0)) tr1a$) (and (= (fun_app$b f$ (last$ ?v0)) tr2$) (less_eq$ (set$ ?v0) nsa$)))))) :named a9))
(assert (! (reg$ f$ tra$) :named a10))
(assert (! (= (fun_app$b f$ (hd$ nl$)) tr1a$) :named a11))
(assert (! (subtr$ nsa$ tr2$ tr1a$) :named a12))
(assert (! (forall ((?v0 N_set$) (?v1 N_set$)) (=> (forall ((?v2 N$)) (=> (member$ ?v2 ?v0) (member$ ?v2 ?v1))) (less_eq$ ?v0 ?v1))) :named a13))
(assert (! (forall ((?v0 N_set$) (?v1 N_set$)) (=> (and (less_eq$ ?v0 ?v1) (less_eq$ ?v1 ?v0)) (= ?v0 ?v1))) :named a14))
(assert (! (forall ((?v0 N_set$)) (less_eq$ ?v0 ?v0)) :named a15))
(assert (! (forall ((?v0 N_list$) (?v1 N_set$)) (= (less_eq$ (set$ ?v0) ?v1) (forall ((?v2 N$)) (=> (member$ ?v2 (set$ ?v0)) (member$ ?v2 ?v1))))) :named a16))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 N_list$)) (=> (path$ ?v0 ?v1) (exists ((?v2 N_list$)) (and (path$ ?v0 ?v2) (and (= (hd$ ?v2) (hd$ ?v1)) (and (= (last$ ?v2) (last$ ?v1)) (and (less_eq$ (set$ ?v2) (set$ ?v1)) (distinct$ ?v2)))))))) :named a17))
(assert (! (forall ((?v0 N_set$) (?v1 N_bool_fun$) (?v2 N_bool_fun$)) (= (less_eq$ ?v0 (collect$ (fun_app$a (uu$ ?v1) ?v2))) (and (less_eq$ ?v0 (collect$ ?v1)) (less_eq$ ?v0 (collect$ ?v2))))) :named a18))
(check-sat)
;(get-unsat-core)
