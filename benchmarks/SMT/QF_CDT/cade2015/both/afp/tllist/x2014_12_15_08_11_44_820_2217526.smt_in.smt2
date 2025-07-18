; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 283
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort C$ 0)
(declare-sort D$ 0)
(declare-sort B_set$ 0)
(declare-sort D_set$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort B_b_set_fun$ 0)
(declare-sort D_set_bool_fun$ 0)
(declare-sort A_c_bool_fun_fun$ 0)
(declare-sort B_d_bool_fun_fun$ 0)
(declare-sort C_d_tllist_bool_fun$ 0)
(declare-sort C_d_tllist_d_set_fun$ 0)
(declare-sort A_llist_b_b_set_fun_fun$ 0)
(declare-sort A_llist_b_prod_b_set_fun$ 0)
(declare-sort B_set_d_set_bool_fun_fun$ 0)
(declare-sort A_llist_b_prod_c_d_tllist_bool_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-datatypes () ((A_llist_b_prod$ (pair$ (fst$ A_llist$) (snd$ B$)))))
(declare-codatatypes () ((C_d_tllist$ (tNil$ (terminal$ D$)) (tCons$ (thd$ C$) (ttl$ C_d_tllist$)))))
(declare-fun a$ () A_c_bool_fun_fun$)
(declare-fun b$ () B_d_bool_fun_fun$)
(declare-fun uu$ () A_llist_b_b_set_fun_fun$)
(declare-fun bot$ () B_set$)
(declare-fun uua$ (B$) B_bool_fun$)
(declare-fun uub$ (B$) B_bool_fun$)
(declare-fun bot$a () B_bool_fun$)
(declare-fun bot$b () Bool)
(declare-fun insert$ (B$ B_set$) B_set$)
(declare-fun member$ (B$ B_set$) Bool)
(declare-fun collect$ (B_bool_fun$) B_set$)
(declare-fun fun_app$ (B_b_set_fun$ B$) B_set$)
(declare-fun lfinite$ (A_llist$) Bool)
(declare-fun rel_fun$ (A_llist_b_prod_c_d_tllist_bool_fun_fun$ B_set_d_set_bool_fun_fun$ A_llist_b_prod_b_set_fun$ C_d_tllist_d_set_fun$) Bool)
(declare-fun rel_set$ (B_d_bool_fun_fun$) B_set_d_set_bool_fun_fun$)
(declare-fun fun_app$a (A_llist_b_b_set_fun_fun$ A_llist$) B_b_set_fun$)
(declare-fun fun_app$b (B_bool_fun$ B$) Bool)
(declare-fun fun_app$c (C_d_tllist_bool_fun$ C_d_tllist$) Bool)
(declare-fun fun_app$d (A_llist_b_prod_c_d_tllist_bool_fun_fun$ A_llist_b_prod$) C_d_tllist_bool_fun$)
(declare-fun fun_app$e (D_set_bool_fun$ D_set$) Bool)
(declare-fun fun_app$f (B_set_d_set_bool_fun_fun$ B_set$) D_set_bool_fun$)
(declare-fun fun_app$g (A_llist_b_prod_b_set_fun$ A_llist_b_prod$) B_set$)
(declare-fun fun_app$h (C_d_tllist_d_set_fun$ C_d_tllist$) D_set$)
(declare-fun case_prod$ (A_llist_b_b_set_fun_fun$) A_llist_b_prod_b_set_fun$)
(declare-fun pcr_tllist$ (A_c_bool_fun_fun$ B_d_bool_fun_fun$) A_llist_b_prod_c_d_tllist_bool_fun_fun$)
(declare-fun set2_tllist$ () C_d_tllist_d_set_fun$)
(assert (! (forall ((?v0 A_llist$) (?v1 B$)) (! (= (fun_app$ (fun_app$a uu$ ?v0) ?v1) (ite (lfinite$ ?v0) (insert$ ?v1 bot$) bot$)) :pattern ((fun_app$ (fun_app$a uu$ ?v0) ?v1)))) :named a0))
(assert (! (forall ((?v0 B$) (?v1 B$)) (! (= (fun_app$b (uua$ ?v0) ?v1) (= ?v0 ?v1)) :pattern ((fun_app$b (uua$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 B$) (?v1 B$)) (! (= (fun_app$b (uub$ ?v0) ?v1) (= ?v1 ?v0)) :pattern ((fun_app$b (uub$ ?v0) ?v1)))) :named a2))
(assert (! (not (rel_fun$ (pcr_tllist$ a$ b$) (rel_set$ b$) (case_prod$ uu$) set2_tllist$)) :named a3))
(assert (! (forall ((?v0 B$)) (= (collect$ (uua$ ?v0)) (insert$ ?v0 bot$))) :named a4))
(assert (! (forall ((?v0 B$)) (= (collect$ (uub$ ?v0)) (insert$ ?v0 bot$))) :named a5))
(assert (! (forall ((?v0 B$)) (member$ ?v0 (insert$ ?v0 bot$))) :named a6))
(assert (! (forall ((?v0 B$) (?v1 B_set$)) (= (insert$ ?v0 (insert$ ?v0 ?v1)) (insert$ ?v0 ?v1))) :named a7))
(assert (! (forall ((?v0 B$) (?v1 B$) (?v2 B_set$)) (= (member$ ?v0 (insert$ ?v1 ?v2)) (or (= ?v0 ?v1) (member$ ?v0 ?v2)))) :named a8))
(assert (! (forall ((?v0 B$) (?v1 B_set$) (?v2 B$)) (=> (=> (not (member$ ?v0 ?v1)) (= ?v0 ?v2)) (member$ ?v0 (insert$ ?v2 ?v1)))) :named a9))
(assert (! (forall ((?v0 A_llist_b_prod_c_d_tllist_bool_fun_fun$) (?v1 B_set_d_set_bool_fun_fun$) (?v2 A_llist_b_prod_b_set_fun$) (?v3 C_d_tllist_d_set_fun$)) (=> (forall ((?v4 A_llist_b_prod$) (?v5 C_d_tllist$)) (=> (fun_app$c (fun_app$d ?v0 ?v4) ?v5) (fun_app$e (fun_app$f ?v1 (fun_app$g ?v2 ?v4)) (fun_app$h ?v3 ?v5)))) (rel_fun$ ?v0 ?v1 ?v2 ?v3))) :named a10))
(assert (! (forall ((?v0 B_bool_fun$)) (= (= (collect$ ?v0) bot$) (forall ((?v1 B$)) (not (fun_app$b ?v0 ?v1))))) :named a11))
(assert (! (forall ((?v0 B_set$)) (= (forall ((?v1 B$)) (not (member$ ?v1 ?v0))) (= ?v0 bot$))) :named a12))
(assert (! (forall ((?v0 B_bool_fun$)) (= (= bot$ (collect$ ?v0)) (forall ((?v1 B$)) (not (fun_app$b ?v0 ?v1))))) :named a13))
(assert (! (forall ((?v0 B$)) (= (member$ ?v0 bot$) false)) :named a14))
(assert (! (forall ((?v0 B$)) (! (= (fun_app$b bot$a ?v0) bot$b) :pattern ((fun_app$b bot$a ?v0)))) :named a15))
(assert (! (= bot$ (collect$ bot$a)) :named a16))
(assert (! (forall ((?v0 B$)) (! (= (fun_app$b bot$a ?v0) bot$b) :pattern ((fun_app$b bot$a ?v0)))) :named a17))
(assert (! (forall ((?v0 B$)) (=> (member$ ?v0 bot$) false)) :named a18))
(assert (! (forall ((?v0 B_set$) (?v1 B$)) (=> (= ?v0 bot$) (not (member$ ?v1 ?v0)))) :named a19))
(assert (! (forall ((?v0 B_set$)) (=> (forall ((?v1 B$)) (=> (member$ ?v1 ?v0) false)) (= ?v0 bot$))) :named a20))
(check-sat)
;(get-unsat-core)
