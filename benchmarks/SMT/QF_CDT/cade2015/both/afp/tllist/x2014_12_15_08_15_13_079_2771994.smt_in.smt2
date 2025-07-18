; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 592
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort C$ 0)
(declare-sort D$ 0)
(declare-sort Nat$ 0)
(declare-sort Unit$ 0)
(declare-sort D_set$ 0)
(declare-sort C_bool_fun$ 0)
(declare-sort D_bool_fun$ 0)
(declare-sort Unit_d_fun$ 0)
(declare-sort D_c_d_tllist_fun$ 0)
(declare-sort C_d_tllist_c_d_tllist_fun$ 0)
(declare-sort C_bool_fun_c_d_tllist_c_d_tllist_fun_fun$ 0)
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-codatatypes () ((C_d_tllist$ (tNil$ (terminal$ D$)) (tCons$ (thd$ C$) (ttl$ C_d_tllist$)))))
(declare-fun x$ () C$)
(declare-fun xs$ () C_d_tllist$)
(declare-fun eSuc$ (Enat$) Enat$)
(declare-fun unity$ () Unit$)
(declare-fun member$ (D$ D_set$) Bool)
(declare-fun fun_app$ (C_bool_fun$ C$) Bool)
(declare-fun tappend$ (C_d_tllist$ D_c_d_tllist_fun$) C_d_tllist$)
(declare-fun tfilter$ (Unit_d_fun$) C_bool_fun_c_d_tllist_c_d_tllist_fun_fun$)
(declare-fun tlength$ (C_d_tllist$) Enat$)
(declare-fun fun_app$a (C_d_tllist_c_d_tllist_fun$ C_d_tllist$) C_d_tllist$)
(declare-fun fun_app$b (C_bool_fun_c_d_tllist_c_d_tllist_fun_fun$ C_bool_fun$) C_d_tllist_c_d_tllist_fun$)
(declare-fun fun_app$c (Unit_d_fun$ Unit$) D$)
(declare-fun tfilter$a (D$) C_bool_fun_c_d_tllist_c_d_tllist_fun_fun$)
(declare-fun pred_tllist$ (C_bool_fun$ D_bool_fun$ C_d_tllist$) Bool)
(declare-fun set2_tllist$ (C_d_tllist$) D_set$)
(assert (! (not (= (tlength$ (tCons$ x$ xs$)) (eSuc$ (tlength$ xs$)))) :named a0))
(assert (! (forall ((?v0 C$) (?v1 C_d_tllist$) (?v2 C$) (?v3 C_d_tllist$)) (= (= (tCons$ ?v0 ?v1) (tCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a1))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (= (= (eSuc$ ?v0) (eSuc$ ?v1)) (= ?v0 ?v1))) :named a2))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (= (= (eSuc$ ?v0) (eSuc$ ?v1)) (= ?v0 ?v1))) :named a3))
(assert (! (forall ((?v0 C_bool_fun$) (?v1 D_bool_fun$) (?v2 C$) (?v3 C_d_tllist$)) (! (= (pred_tllist$ ?v0 ?v1 (tCons$ ?v2 ?v3)) (and (fun_app$ ?v0 ?v2) (pred_tllist$ ?v0 ?v1 ?v3))) :pattern ((pred_tllist$ ?v0 ?v1 (tCons$ ?v2 ?v3))))) :named a4))
(assert (! (forall ((?v0 Unit_d_fun$) (?v1 C_bool_fun$) (?v2 C$) (?v3 C_d_tllist$)) (! (= (fun_app$a (fun_app$b (tfilter$ ?v0) ?v1) (tCons$ ?v2 ?v3)) (ite (fun_app$ ?v1 ?v2) (tCons$ ?v2 (fun_app$a (fun_app$b (tfilter$ ?v0) ?v1) ?v3)) (fun_app$a (fun_app$b (tfilter$ ?v0) ?v1) ?v3))) :pattern ((fun_app$a (fun_app$b (tfilter$ ?v0) ?v1) (tCons$ ?v2 ?v3))))) :named a5))
(assert (! (forall ((?v0 D$) (?v1 C_bool_fun$) (?v2 C$) (?v3 C_d_tllist$)) (! (= (fun_app$a (fun_app$b (tfilter$a ?v0) ?v1) (tCons$ ?v2 ?v3)) (ite (fun_app$ ?v1 ?v2) (tCons$ ?v2 (fun_app$a (fun_app$b (tfilter$a ?v0) ?v1) ?v3)) (fun_app$a (fun_app$b (tfilter$a ?v0) ?v1) ?v3))) :pattern ((fun_app$a (fun_app$b (tfilter$a ?v0) ?v1) (tCons$ ?v2 ?v3))))) :named a6))
(assert (! (forall ((?v0 C$) (?v1 C_d_tllist$) (?v2 D_c_d_tllist_fun$)) (! (= (tappend$ (tCons$ ?v0 ?v1) ?v2) (tCons$ ?v0 (tappend$ ?v1 ?v2))) :pattern ((tappend$ (tCons$ ?v0 ?v1) ?v2)))) :named a7))
(assert (! (forall ((?v0 C$) (?v1 C_d_tllist$)) (! (= (set2_tllist$ (tCons$ ?v0 ?v1)) (set2_tllist$ ?v1)) :pattern ((tCons$ ?v0 ?v1)))) :named a8))
(assert (! (forall ((?v0 D$) (?v1 C_d_tllist$) (?v2 C$)) (=> (member$ ?v0 (set2_tllist$ ?v1)) (member$ ?v0 (set2_tllist$ (tCons$ ?v2 ?v1))))) :named a9))
(assert (! (forall ((?v0 C$) (?v1 C_d_tllist$)) (! (= (thd$ (tCons$ ?v0 ?v1)) ?v0) :pattern ((tCons$ ?v0 ?v1)))) :named a10))
(assert (! (forall ((?v0 Unit_d_fun$)) (! (= (tfilter$ ?v0) (tfilter$a (fun_app$c ?v0 unity$))) :pattern ((tfilter$ ?v0)))) :named a11))
(check-sat)
;(get-unsat-core)
