; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 628
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort B$ 0)
(declare-sort Nat$ 0)
(declare-sort Enat_bool_fun$ 0)
(declare-sort B_llist_bool_fun$ 0)
(declare-sort B_llist_enat_fun$ 0)
(declare-sort Enat_enat_prod_set$ 0)
(declare-sort Enat_enat_bool_fun_fun$ 0)
(declare-sort Enat_enat_prod_bool_fun$ 0)
(declare-sort B_llist_b_llist_prod_set$ 0)
(declare-sort B_llist_b_llist_bool_fun_fun$ 0)
(declare-sort B_llist_b_llist_prod_bool_fun$ 0)
(declare-codatatypes () ((B_llist$ (lNil$) (lCons$ (lhd$ B$) (ltl$ B_llist$)))))
(declare-datatypes () ((B_llist_b_llist_prod$ (pair$ (fst$ B_llist$) (snd$ B_llist$)))
  (Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))
  (Enat_enat_prod$ (pair$a (fst$a Enat$) (snd$a Enat$)))))
(declare-fun uu$ (Bool B_llist_b_llist_bool_fun_fun$) B_llist_b_llist_bool_fun_fun$)
(declare-fun wf$ (B_llist_b_llist_prod_set$) Bool)
(declare-fun uua$ (Bool Enat_enat_bool_fun_fun$) Enat_enat_bool_fun_fun$)
(declare-fun wf$a (Enat_enat_prod_set$) Bool)
(declare-fun less$ () Enat_enat_bool_fun_fun$)
(declare-fun less$a (B_llist_b_llist_prod_set$ B_llist_b_llist_prod_set$) Bool)
(declare-fun member$ (B_llist_b_llist_prod$ B_llist_b_llist_prod_set$) Bool)
(declare-fun collect$ (B_llist_b_llist_prod_bool_fun$) B_llist_b_llist_prod_set$)
(declare-fun fun_app$ (B_llist_bool_fun$ B_llist$) Bool)
(declare-fun less_eq$ (B_llist_b_llist_prod_set$ B_llist_b_llist_prod_set$) Bool)
(declare-fun llength$ () B_llist_enat_fun$)
(declare-fun collect$a (Enat_enat_prod_bool_fun$) Enat_enat_prod_set$)
(declare-fun fun_app$a (B_llist_b_llist_bool_fun_fun$ B_llist$) B_llist_bool_fun$)
(declare-fun fun_app$b (Enat_bool_fun$ Enat$) Bool)
(declare-fun fun_app$c (Enat_enat_bool_fun_fun$ Enat$) Enat_bool_fun$)
(declare-fun fun_app$d (B_llist_enat_fun$ B_llist$) Enat$)
(declare-fun fun_app$e (B_llist_b_llist_prod_bool_fun$ B_llist_b_llist_prod$) Bool)
(declare-fun fun_app$f (Enat_enat_prod_bool_fun$ Enat_enat_prod$) Bool)
(declare-fun less_eq$a (Enat$ Enat$) Bool)
(declare-fun case_prod$ (B_llist_b_llist_bool_fun_fun$) B_llist_b_llist_prod_bool_fun$)
(declare-fun inv_image$ (Enat_enat_prod_set$ B_llist_enat_fun$) B_llist_b_llist_prod_set$)
(declare-fun case_prod$a (Enat_enat_bool_fun_fun$) Enat_enat_prod_bool_fun$)
(declare-fun lstrict_prefix$ () B_llist_b_llist_bool_fun_fun$)
(assert (! (forall ((?v0 Bool) (?v1 B_llist_b_llist_bool_fun_fun$) (?v2 B_llist$) (?v3 B_llist$)) (! (= (fun_app$ (fun_app$a (uu$ ?v0 ?v1) ?v2) ?v3) (and ?v0 (fun_app$ (fun_app$a ?v1 ?v2) ?v3))) :pattern ((fun_app$ (fun_app$a (uu$ ?v0 ?v1) ?v2) ?v3)))) :named a0))
(assert (! (forall ((?v0 Bool) (?v1 Enat_enat_bool_fun_fun$) (?v2 Enat$) (?v3 Enat$)) (! (= (fun_app$b (fun_app$c (uua$ ?v0 ?v1) ?v2) ?v3) (and ?v0 (fun_app$b (fun_app$c ?v1 ?v2) ?v3))) :pattern ((fun_app$b (fun_app$c (uua$ ?v0 ?v1) ?v2) ?v3)))) :named a1))
(assert (! (not (less_eq$ (collect$ (case_prod$ lstrict_prefix$)) (inv_image$ (collect$a (case_prod$a less$)) llength$))) :named a2))
(assert (! (forall ((?v0 Enat_enat_bool_fun_fun$) (?v1 Enat$) (?v2 Enat$)) (=> (and (forall ((?v3 Enat$) (?v4 Enat$)) (=> (less_eq$a ?v3 ?v4) (fun_app$b (fun_app$c ?v0 ?v3) ?v4))) (=> (fun_app$b (fun_app$c ?v0 ?v1) ?v2) (fun_app$b (fun_app$c ?v0 ?v2) ?v1))) (fun_app$b (fun_app$c ?v0 ?v2) ?v1))) :named a3))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (=> (fun_app$ (fun_app$a lstrict_prefix$ ?v0) ?v1) (fun_app$b (fun_app$c less$ (fun_app$d llength$ ?v0)) (fun_app$d llength$ ?v1)))) :named a4))
(assert (! (wf$ (inv_image$ (collect$a (case_prod$a less$)) llength$)) :named a5))
(assert (! (forall ((?v0 Bool) (?v1 B_llist_b_llist_bool_fun_fun$) (?v2 B_llist_b_llist_prod$)) (= (fun_app$e (case_prod$ (uu$ ?v0 ?v1)) ?v2) (and ?v0 (fun_app$e (case_prod$ ?v1) ?v2)))) :named a6))
(assert (! (forall ((?v0 Bool) (?v1 Enat_enat_bool_fun_fun$) (?v2 Enat_enat_prod$)) (= (fun_app$f (case_prod$a (uua$ ?v0 ?v1)) ?v2) (and ?v0 (fun_app$f (case_prod$a ?v1) ?v2)))) :named a7))
(assert (! (forall ((?v0 B_llist_b_llist_prod_set$) (?v1 B_llist_b_llist_prod_set$)) (=> (forall ((?v2 B_llist_b_llist_prod$)) (=> (member$ ?v2 ?v0) (member$ ?v2 ?v1))) (less_eq$ ?v0 ?v1))) :named a8))
(assert (! (forall ((?v0 B_llist_b_llist_prod_set$) (?v1 B_llist_b_llist_prod_set$)) (=> (and (less_eq$ ?v0 ?v1) (less_eq$ ?v1 ?v0)) (= ?v0 ?v1))) :named a9))
(assert (! (forall ((?v0 Enat$)) (less_eq$a ?v0 ?v0)) :named a10))
(assert (! (forall ((?v0 B_llist_b_llist_prod_set$)) (less_eq$ ?v0 ?v0)) :named a11))
(assert (! (wf$a (collect$a (case_prod$a less$))) :named a12))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (! (= (fun_app$b (fun_app$c less$ ?v0) ?v1) (and (less_eq$a ?v0 ?v1) (not (= ?v1 ?v0)))) :pattern ((fun_app$b (fun_app$c less$ ?v0) ?v1)))) :named a13))
(assert (! (forall ((?v0 B_llist_b_llist_prod_set$) (?v1 B_llist_b_llist_prod_set$)) (! (= (less$a ?v0 ?v1) (and (less_eq$ ?v0 ?v1) (not (= ?v1 ?v0)))) :pattern ((less$a ?v0 ?v1)))) :named a14))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (! (= (fun_app$b (fun_app$c less$ ?v0) ?v1) (and (less_eq$a ?v0 ?v1) (not (= ?v0 ?v1)))) :pattern ((fun_app$b (fun_app$c less$ ?v0) ?v1)))) :named a15))
(assert (! (forall ((?v0 B_llist_b_llist_prod_set$) (?v1 B_llist_b_llist_prod_set$)) (! (= (less$a ?v0 ?v1) (and (less_eq$ ?v0 ?v1) (not (= ?v0 ?v1)))) :pattern ((less$a ?v0 ?v1)))) :named a16))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (! (= (fun_app$b (fun_app$c less$ ?v0) ?v1) (and (less_eq$a ?v0 ?v1) (not (= ?v0 ?v1)))) :pattern ((fun_app$b (fun_app$c less$ ?v0) ?v1)))) :named a17))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (! (= (fun_app$b (fun_app$c less$ ?v0) ?v1) (and (less_eq$a ?v0 ?v1) (not (= ?v1 ?v0)))) :pattern ((fun_app$b (fun_app$c less$ ?v0) ?v1)))) :named a18))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (! (= (fun_app$b (fun_app$c less$ ?v0) ?v1) (and (less_eq$a ?v0 ?v1) (not (= ?v1 ?v0)))) :pattern ((fun_app$b (fun_app$c less$ ?v0) ?v1)))) :named a19))
(assert (! (forall ((?v0 B_llist_b_llist_prod_set$) (?v1 B_llist_b_llist_prod_set$)) (! (= (less$a ?v0 ?v1) (and (less_eq$ ?v0 ?v1) (not (= ?v1 ?v0)))) :pattern ((less$a ?v0 ?v1)))) :named a20))
(assert (! (forall ((?v0 Enat$) (?v1 Enat$)) (! (= (fun_app$b (fun_app$c less$ ?v0) ?v1) (and (less_eq$a ?v0 ?v1) (not (= ?v0 ?v1)))) :pattern ((fun_app$b (fun_app$c less$ ?v0) ?v1)))) :named a21))
(assert (! (forall ((?v0 B_llist_b_llist_prod_set$) (?v1 B_llist_b_llist_prod_set$)) (! (= (less$a ?v0 ?v1) (and (less_eq$ ?v0 ?v1) (not (= ?v0 ?v1)))) :pattern ((less$a ?v0 ?v1)))) :named a22))
(assert (! (forall ((?v0 B_llist_b_llist_prod_set$) (?v1 B_llist_b_llist_prod_set$)) (=> (and (less_eq$ ?v0 ?v1) (not (= ?v0 ?v1))) (less$a ?v0 ?v1))) :named a23))
(assert (! (forall ((?v0 B_llist_b_llist_prod_set$) (?v1 B_llist_b_llist_prod_set$) (?v2 B_llist_b_llist_prod_set$)) (=> (and (less_eq$ ?v0 ?v1) (less$a ?v1 ?v2)) (less$a ?v0 ?v2))) :named a24))
(assert (! (forall ((?v0 B_llist_b_llist_prod_set$) (?v1 B_llist_b_llist_prod_set$)) (=> (less$a ?v0 ?v1) (less_eq$ ?v0 ?v1))) :named a25))
(check-sat)
;(get-unsat-core)
