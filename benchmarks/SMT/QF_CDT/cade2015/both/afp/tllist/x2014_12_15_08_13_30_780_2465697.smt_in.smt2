; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 324
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort Unit$ 0)
(declare-sort B_set$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort B_b_fun$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort Unit_a_fun$ 0)
(declare-sort B_a_tllist_b_a_tllist_fun$ 0)
(declare-sort B_bool_fun_b_a_tllist_b_a_tllist_fun_fun$ 0)
(declare-sort A_b_bool_fun_b_a_tllist_b_a_tllist_fun_fun_fun$ 0)
(declare-codatatypes () ((B_a_tllist$ (tNil$ (terminal$ A$)) (tCons$ (thd$ B$) (ttl$ B_a_tllist$)))))
(declare-fun uu$ (A$) Unit_a_fun$)
(declare-fun uua$ () A_b_bool_fun_b_a_tllist_b_a_tllist_fun_fun_fun$)
(declare-fun uub$ () B_b_fun$)
(declare-fun uuc$ () A_a_fun$)
(declare-fun tmap$ (B_b_fun$ A_a_fun$ B_a_tllist$) B_a_tllist$)
(declare-fun tset$ (B_a_tllist$) B_set$)
(declare-fun unity$ () Unit$)
(declare-fun member$ (B$ B_set$) Bool)
(declare-fun fun_app$ (A_b_bool_fun_b_a_tllist_b_a_tllist_fun_fun_fun$ A$) B_bool_fun_b_a_tllist_b_a_tllist_fun_fun$)
(declare-fun is_TNil$ (B_a_tllist$) Bool)
(declare-fun tfilter$ (Unit_a_fun$) B_bool_fun_b_a_tllist_b_a_tllist_fun_fun$)
(declare-fun fun_app$a (Unit_a_fun$ Unit$) A$)
(declare-fun fun_app$b (B_b_fun$ B$) B$)
(declare-fun fun_app$c (A_a_fun$ A$) A$)
(declare-fun fun_app$d (B_a_tllist_b_a_tllist_fun$ B_a_tllist$) B_a_tllist$)
(declare-fun fun_app$e (B_bool_fun_b_a_tllist_b_a_tllist_fun_fun$ B_bool_fun$) B_a_tllist_b_a_tllist_fun$)
(declare-fun fun_app$f (B_bool_fun$ B$) Bool)
(declare-fun tfilter$a () A_b_bool_fun_b_a_tllist_b_a_tllist_fun_fun_fun$)
(assert (! (forall ((?v0 A$)) (! (= (fun_app$ uua$ ?v0) (tfilter$ (uu$ ?v0))) :pattern ((fun_app$ uua$ ?v0)))) :named a0))
(assert (! (forall ((?v0 A$) (?v1 Unit$)) (! (= (fun_app$a (uu$ ?v0) ?v1) ?v0) :pattern ((fun_app$a (uu$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 B$)) (! (= (fun_app$b uub$ ?v0) ?v0) :pattern ((fun_app$b uub$ ?v0)))) :named a2))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$c uuc$ ?v0) ?v0) :pattern ((fun_app$c uuc$ ?v0)))) :named a3))
(assert (! (not (= tfilter$a uua$)) :named a4))
(assert (! (forall ((?v0 Unit_a_fun$)) (! (= (tfilter$ ?v0) (fun_app$ tfilter$a (fun_app$a ?v0 unity$))) :pattern ((tfilter$ ?v0)))) :named a5))
(assert (! (forall ((?v0 A$) (?v1 B_bool_fun$) (?v2 B$) (?v3 B_a_tllist$)) (! (= (fun_app$d (fun_app$e (fun_app$ tfilter$a ?v0) ?v1) (tCons$ ?v2 ?v3)) (ite (fun_app$f ?v1 ?v2) (tCons$ ?v2 (fun_app$d (fun_app$e (fun_app$ tfilter$a ?v0) ?v1) ?v3)) (fun_app$d (fun_app$e (fun_app$ tfilter$a ?v0) ?v1) ?v3))) :pattern ((fun_app$d (fun_app$e (fun_app$ tfilter$a ?v0) ?v1) (tCons$ ?v2 ?v3))))) :named a6))
(assert (! (forall ((?v0 A$) (?v1 B_bool_fun$) (?v2 A$)) (! (= (fun_app$d (fun_app$e (fun_app$ tfilter$a ?v0) ?v1) (tNil$ ?v2)) (tNil$ ?v2)) :pattern ((fun_app$d (fun_app$e (fun_app$ tfilter$a ?v0) ?v1) (tNil$ ?v2))))) :named a7))
(assert (! (forall ((?v0 A$) (?v1 B_bool_fun$) (?v2 B_a_tllist$)) (= (is_TNil$ (fun_app$d (fun_app$e (fun_app$ tfilter$a ?v0) ?v1) ?v2)) (forall ((?v3 B$)) (=> (member$ ?v3 (tset$ ?v2)) (not (fun_app$f ?v1 ?v3)))))) :named a8))
(assert (! (forall ((?v0 B_a_tllist$)) (= (tmap$ uub$ uuc$ ?v0) ?v0)) :named a9))
(assert (! (forall ((?v0 B$) (?v1 B_a_tllist$) (?v2 B$) (?v3 B_a_tllist$)) (= (= (tCons$ ?v0 ?v1) (tCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a10))
(assert (! (forall ((?v0 A$) (?v1 A$)) (= (= (tNil$ ?v0) (tNil$ ?v1)) (= ?v0 ?v1))) :named a11))
(assert (! (forall ((?v0 B_b_fun$) (?v1 A_a_fun$) (?v2 B_a_tllist$)) (= (is_TNil$ (tmap$ ?v0 ?v1 ?v2)) (is_TNil$ ?v2))) :named a12))
(check-sat)
;(get-unsat-core)
