; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 46
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort B_set$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort B_b_fun$ 0)
(declare-sort B_bool_fun$ 0)
(declare-sort A_b_tllist_b_fun$ 0)
(declare-sort B_a_b_tllist_fun$ 0)
(declare-sort A_b_tllist_bool_fun$ 0)
(declare-sort A_a_b_tllist_b_fun_fun$ 0)
(declare-sort A_b_tllist_a_b_tllist_fun$ 0)
(declare-sort A_a_b_tllist_a_b_tllist_fun_fun$ 0)
(declare-sort A_b_tllist_a_b_tllist_bool_fun_fun$ 0)
(declare-codatatypes () ((A_b_tllist$ (tNil$ (terminal$ B$)) (tCons$ (thd$ A$) (ttl$ A_b_tllist$)))))
(declare-fun uu$ () A_b_tllist_b_fun$)
(declare-fun uua$ () B_b_fun$)
(declare-fun uub$ () A_a_b_tllist_b_fun_fun$)
(declare-fun uuc$ () B_a_b_tllist_fun$)
(declare-fun uud$ () A_a_b_tllist_a_b_tllist_fun_fun$)
(declare-fun tmap$ (A_a_fun$ B_b_fun$ A_b_tllist$) A_b_tllist$)
(declare-fun member$ (B$ B_set$) Bool)
(declare-fun fun_app$ (A_b_tllist_b_fun$ A_b_tllist$) B$)
(declare-fun is_TNil$ (A_b_tllist$) Bool)
(declare-fun fun_app$a (B_a_b_tllist_fun$ B$) A_b_tllist$)
(declare-fun fun_app$b (A_b_tllist_a_b_tllist_fun$ A_b_tllist$) A_b_tllist$)
(declare-fun fun_app$c (A_a_b_tllist_a_b_tllist_fun_fun$ A$) A_b_tllist_a_b_tllist_fun$)
(declare-fun fun_app$d (B_b_fun$ B$) B$)
(declare-fun fun_app$e (A_a_b_tllist_b_fun_fun$ A$) A_b_tllist_b_fun$)
(declare-fun fun_app$f (A_b_tllist_bool_fun$ A_b_tllist$) Bool)
(declare-fun fun_app$g (A_b_tllist_a_b_tllist_bool_fun_fun$ A_b_tllist$) A_b_tllist_bool_fun$)
(declare-fun fun_app$h (A_a_fun$ A$) A$)
(declare-fun fun_app$i (B_bool_fun$ B$) Bool)
(declare-fun terminal0$ () A_b_tllist_b_fun$)
(declare-fun case_tllist$ (B_b_fun$ A_a_b_tllist_b_fun_fun$ A_b_tllist$) B$)
(declare-fun set2_tllist$ (A_b_tllist$) B_set$)
(declare-fun case_tllist$a (B_a_b_tllist_fun$ A_a_b_tllist_a_b_tllist_fun_fun$ A_b_tllist$) A_b_tllist$)
(assert (! (forall ((?v0 A_b_tllist$)) (! (= (fun_app$ uu$ ?v0) (terminal$ ?v0)) :pattern ((fun_app$ uu$ ?v0)))) :named a0))
(assert (! (forall ((?v0 B$)) (! (= (fun_app$a uuc$ ?v0) (tNil$ ?v0)) :pattern ((fun_app$a uuc$ ?v0)))) :named a1))
(assert (! (forall ((?v0 A$) (?v1 A_b_tllist$)) (! (= (fun_app$b (fun_app$c uud$ ?v0) ?v1) ?v1) :pattern ((fun_app$b (fun_app$c uud$ ?v0) ?v1)))) :named a2))
(assert (! (forall ((?v0 B$)) (! (= (fun_app$d uua$ ?v0) ?v0) :pattern ((fun_app$d uua$ ?v0)))) :named a3))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$e uub$ ?v0) terminal0$) :pattern ((fun_app$e uub$ ?v0)))) :named a4))
(assert (! (not (= terminal0$ uu$)) :named a5))
(assert (! (forall ((?v0 A$) (?v1 A_b_tllist$)) (! (= (terminal$ (tCons$ ?v0 ?v1)) (fun_app$ terminal0$ ?v1)) :pattern ((tCons$ ?v0 ?v1)))) :named a6))
(assert (! (forall ((?v0 B$)) (! (= (terminal$ (tNil$ ?v0)) ?v0) :pattern ((tNil$ ?v0)))) :named a7))
(assert (! (forall ((?v0 A_b_tllist$)) (= (terminal$ ?v0) (case_tllist$ uua$ uub$ ?v0))) :named a8))
(assert (! (forall ((?v0 A_b_tllist$)) (=> (is_TNil$ ?v0) (= (tNil$ (terminal$ ?v0)) ?v0))) :named a9))
(assert (! (forall ((?v0 A_b_tllist$)) (=> (is_TNil$ ?v0) (member$ (terminal$ ?v0) (set2_tllist$ ?v0)))) :named a10))
(assert (! (forall ((?v0 A_b_tllist$) (?v1 A_a_fun$) (?v2 B_b_fun$)) (=> (is_TNil$ ?v0) (= (terminal$ (tmap$ ?v1 ?v2 ?v0)) (fun_app$d ?v2 (terminal$ ?v0))))) :named a11))
(assert (! (forall ((?v0 A_b_tllist$) (?v1 A_b_tllist$)) (=> (and (= (is_TNil$ ?v0) (is_TNil$ ?v1)) (and (=> (and (is_TNil$ ?v0) (is_TNil$ ?v1)) (= (terminal$ ?v0) (terminal$ ?v1))) (=> (and (not (is_TNil$ ?v0)) (not (is_TNil$ ?v1))) (and (= (thd$ ?v0) (thd$ ?v1)) (= (ttl$ ?v0) (ttl$ ?v1)))))) (= ?v0 ?v1))) :named a12))
(assert (! (forall ((?v0 A_b_tllist_a_b_tllist_bool_fun_fun$) (?v1 A_b_tllist$) (?v2 A_b_tllist$)) (=> (and (fun_app$f (fun_app$g ?v0 ?v1) ?v2) (forall ((?v3 A_b_tllist$) (?v4 A_b_tllist$)) (=> (fun_app$f (fun_app$g ?v0 ?v3) ?v4) (and (= (is_TNil$ ?v3) (is_TNil$ ?v4)) (and (=> (and (is_TNil$ ?v3) (is_TNil$ ?v4)) (= (terminal$ ?v3) (terminal$ ?v4))) (=> (and (not (is_TNil$ ?v3)) (not (is_TNil$ ?v4))) (and (= (thd$ ?v3) (thd$ ?v4)) (or (fun_app$f (fun_app$g ?v0 (ttl$ ?v3)) (ttl$ ?v4)) (= (ttl$ ?v3) (ttl$ ?v4)))))))))) (= ?v1 ?v2))) :named a13))
(assert (! (forall ((?v0 A_b_tllist_a_b_tllist_bool_fun_fun$) (?v1 A_b_tllist$) (?v2 A_b_tllist$)) (=> (and (fun_app$f (fun_app$g ?v0 ?v1) ?v2) (forall ((?v3 A_b_tllist$) (?v4 A_b_tllist$)) (=> (fun_app$f (fun_app$g ?v0 ?v3) ?v4) (and (= (is_TNil$ ?v3) (is_TNil$ ?v4)) (and (=> (and (is_TNil$ ?v3) (is_TNil$ ?v4)) (= (terminal$ ?v3) (terminal$ ?v4))) (=> (and (not (is_TNil$ ?v3)) (not (is_TNil$ ?v4))) (and (= (thd$ ?v3) (thd$ ?v4)) (fun_app$f (fun_app$g ?v0 (ttl$ ?v3)) (ttl$ ?v4))))))))) (= ?v1 ?v2))) :named a14))
(assert (! (forall ((?v0 A$) (?v1 A_b_tllist$) (?v2 A$) (?v3 A_b_tllist$)) (= (= (tCons$ ?v0 ?v1) (tCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a15))
(assert (! (forall ((?v0 B$) (?v1 B$)) (= (= (tNil$ ?v0) (tNil$ ?v1)) (= ?v0 ?v1))) :named a16))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_b_fun$) (?v2 A_b_tllist$)) (= (is_TNil$ (tmap$ ?v0 ?v1 ?v2)) (is_TNil$ ?v2))) :named a17))
(assert (! (forall ((?v0 A_b_tllist$)) (=> (not (is_TNil$ ?v0)) (= (tCons$ (thd$ ?v0) (ttl$ ?v0)) ?v0))) :named a18))
(assert (! (forall ((?v0 B_a_b_tllist_fun$) (?v1 A_a_b_tllist_a_b_tllist_fun_fun$) (?v2 A_b_tllist$)) (! (= (case_tllist$a ?v0 ?v1 ?v2) (ite (is_TNil$ ?v2) (fun_app$a ?v0 (terminal$ ?v2)) (fun_app$b (fun_app$c ?v1 (thd$ ?v2)) (ttl$ ?v2)))) :pattern ((case_tllist$a ?v0 ?v1 ?v2)))) :named a19))
(assert (! (forall ((?v0 B_b_fun$) (?v1 A_a_b_tllist_b_fun_fun$) (?v2 A_b_tllist$)) (! (= (case_tllist$ ?v0 ?v1 ?v2) (ite (is_TNil$ ?v2) (fun_app$d ?v0 (terminal$ ?v2)) (fun_app$ (fun_app$e ?v1 (thd$ ?v2)) (ttl$ ?v2)))) :pattern ((case_tllist$ ?v0 ?v1 ?v2)))) :named a20))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_b_fun$) (?v2 A$) (?v3 A_b_tllist$)) (! (= (tmap$ ?v0 ?v1 (tCons$ ?v2 ?v3)) (tCons$ (fun_app$h ?v0 ?v2) (tmap$ ?v0 ?v1 ?v3))) :pattern ((tmap$ ?v0 ?v1 (tCons$ ?v2 ?v3))))) :named a21))
(assert (! (forall ((?v0 A_b_tllist_bool_fun$) (?v1 B_a_b_tllist_fun$) (?v2 A_a_b_tllist_a_b_tllist_fun_fun$) (?v3 A_b_tllist$)) (= (fun_app$f ?v0 (case_tllist$a ?v1 ?v2 ?v3)) (not (or (and (= ?v3 (tNil$ (terminal$ ?v3))) (not (fun_app$f ?v0 (fun_app$a ?v1 (terminal$ ?v3))))) (and (= ?v3 (tCons$ (thd$ ?v3) (ttl$ ?v3))) (not (fun_app$f ?v0 (fun_app$b (fun_app$c ?v2 (thd$ ?v3)) (ttl$ ?v3))))))))) :named a22))
(assert (! (forall ((?v0 B_bool_fun$) (?v1 B_b_fun$) (?v2 A_a_b_tllist_b_fun_fun$) (?v3 A_b_tllist$)) (= (fun_app$i ?v0 (case_tllist$ ?v1 ?v2 ?v3)) (not (or (and (= ?v3 (tNil$ (terminal$ ?v3))) (not (fun_app$i ?v0 (fun_app$d ?v1 (terminal$ ?v3))))) (and (= ?v3 (tCons$ (thd$ ?v3) (ttl$ ?v3))) (not (fun_app$i ?v0 (fun_app$ (fun_app$e ?v2 (thd$ ?v3)) (ttl$ ?v3))))))))) :named a23))
(assert (! (forall ((?v0 A_b_tllist$)) (= (ttl$ ?v0) (case_tllist$a uuc$ uud$ ?v0))) :named a24))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_b_fun$) (?v2 B$)) (! (= (tmap$ ?v0 ?v1 (tNil$ ?v2)) (tNil$ (fun_app$d ?v1 ?v2))) :pattern ((tmap$ ?v0 ?v1 (tNil$ ?v2))))) :named a25))
(assert (! (forall ((?v0 B$)) (! (= (ttl$ (tNil$ ?v0)) (tNil$ ?v0)) :pattern ((tNil$ ?v0)))) :named a26))
(assert (! (forall ((?v0 A_b_tllist$)) (= (is_TNil$ ?v0) (exists ((?v1 B$)) (= ?v0 (tNil$ ?v1))))) :named a27))
(check-sat)
;(get-unsat-core)
