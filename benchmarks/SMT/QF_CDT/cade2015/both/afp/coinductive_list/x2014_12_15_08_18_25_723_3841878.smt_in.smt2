; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 572
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort Nat$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_b_fun$ 0)
(declare-sort B_a_fun$ 0)
(declare-sort B_b_fun$ 0)
(declare-sort Nat_a_fun$ 0)
(declare-sort Nat_b_fun$ 0)
(declare-codatatypes () ((B_llist$ (lNil$) (lCons$ (lhd$ B$) (ltl$ B_llist$)))
  (A_llist$ (lNil$a) (lCons$a (lhd$a A$) (ltl$a A_llist$)))))
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-fun f$ () A_b_fun$)
(declare-fun x$ () A$)
(declare-fun na$ () Nat$)
(declare-fun uu$ () B_b_fun$)
(declare-fun xs$ () A_llist$)
(declare-fun suc$ (Nat$) Nat$)
(declare-fun uua$ () A_a_fun$)
(declare-fun xsa$ () A_llist$)
(declare-fun enat$ (Nat$) Enat$)
(declare-fun less$ (Enat$ Enat$) Bool)
(declare-fun lmap$ (A_b_fun$ A_llist$) B_llist$)
(declare-fun lnth$ (B_llist$) Nat_b_fun$)
(declare-fun lmap$a (B_b_fun$ B_llist$) B_llist$)
(declare-fun lmap$b (A_a_fun$ A_llist$) A_llist$)
(declare-fun lmap$c (B_a_fun$ B_llist$) A_llist$)
(declare-fun lnth$a (A_llist$) Nat_a_fun$)
(declare-fun fun_app$ (B_b_fun$ B$) B$)
(declare-fun llength$ (A_llist$) Enat$)
(declare-fun case_nat$ (B$ Nat_b_fun$ Nat$) B$)
(declare-fun fun_app$a (A_a_fun$ A$) A$)
(declare-fun fun_app$b (Nat_b_fun$ Nat$) B$)
(declare-fun fun_app$c (A_b_fun$ A$) B$)
(declare-fun fun_app$d (Nat_a_fun$ Nat$) A$)
(declare-fun fun_app$e (B_a_fun$ B$) A$)
(declare-fun llength$a (B_llist$) Enat$)
(declare-fun case_nat$a (A$ Nat_a_fun$ Nat$) A$)
(assert (! (forall ((?v0 B$)) (! (= (fun_app$ uu$ ?v0) ?v0) :pattern ((fun_app$ uu$ ?v0)))) :named a0))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$a uua$ ?v0) ?v0) :pattern ((fun_app$a uua$ ?v0)))) :named a1))
(assert (! (not (= (fun_app$b (lnth$ (lmap$ f$ xsa$)) (suc$ na$)) (fun_app$c f$ (fun_app$d (lnth$a xsa$) (suc$ na$))))) :named a2))
(assert (! (= xsa$ (lCons$a x$ xs$)) :named a3))
(assert (! (= (fun_app$b (lnth$ (lmap$ f$ xs$)) na$) (fun_app$c f$ (fun_app$d (lnth$a xs$) na$))) :named a4))
(assert (! (forall ((?v0 B_llist$)) (= (lmap$a uu$ ?v0) ?v0)) :named a5))
(assert (! (forall ((?v0 A_llist$)) (= (lmap$b uua$ ?v0) ?v0)) :named a6))
(assert (! (forall ((?v0 B$) (?v1 B_llist$) (?v2 Nat$)) (! (= (fun_app$b (lnth$ (lCons$ ?v0 ?v1)) (suc$ ?v2)) (fun_app$b (lnth$ ?v1) ?v2)) :pattern ((fun_app$b (lnth$ (lCons$ ?v0 ?v1)) (suc$ ?v2))))) :named a7))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 Nat$)) (! (= (fun_app$d (lnth$a (lCons$a ?v0 ?v1)) (suc$ ?v2)) (fun_app$d (lnth$a ?v1) ?v2)) :pattern ((fun_app$d (lnth$a (lCons$a ?v0 ?v1)) (suc$ ?v2))))) :named a8))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (suc$ ?v0) (suc$ ?v1)) (= ?v0 ?v1))) :named a9))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (= (= (suc$ ?v0) (suc$ ?v1)) (= ?v0 ?v1))) :named a10))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B$) (?v2 B_llist$)) (! (= (lmap$c ?v0 (lCons$ ?v1 ?v2)) (lCons$a (fun_app$e ?v0 ?v1) (lmap$c ?v0 ?v2))) :pattern ((lmap$c ?v0 (lCons$ ?v1 ?v2))))) :named a11))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B$) (?v2 B_llist$)) (! (= (lmap$a ?v0 (lCons$ ?v1 ?v2)) (lCons$ (fun_app$ ?v0 ?v1) (lmap$a ?v0 ?v2))) :pattern ((lmap$a ?v0 (lCons$ ?v1 ?v2))))) :named a12))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A$) (?v2 A_llist$)) (! (= (lmap$ ?v0 (lCons$a ?v1 ?v2)) (lCons$ (fun_app$c ?v0 ?v1) (lmap$ ?v0 ?v2))) :pattern ((lmap$ ?v0 (lCons$a ?v1 ?v2))))) :named a13))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$) (?v2 A_llist$)) (! (= (lmap$b ?v0 (lCons$a ?v1 ?v2)) (lCons$a (fun_app$a ?v0 ?v1) (lmap$b ?v0 ?v2))) :pattern ((lmap$b ?v0 (lCons$a ?v1 ?v2))))) :named a14))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lmap$c ?v0 ?v1) (lCons$a ?v2 ?v3)) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v1 (lCons$ ?v4 ?v5)) (and (= ?v2 (fun_app$e ?v0 ?v4)) (= ?v3 (lmap$c ?v0 ?v5))))))) :named a15))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_llist$) (?v2 B$) (?v3 B_llist$)) (= (= (lmap$a ?v0 ?v1) (lCons$ ?v2 ?v3)) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v1 (lCons$ ?v4 ?v5)) (and (= ?v2 (fun_app$ ?v0 ?v4)) (= ?v3 (lmap$a ?v0 ?v5))))))) :named a16))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_llist$) (?v2 B$) (?v3 B_llist$)) (= (= (lmap$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v1 (lCons$a ?v4 ?v5)) (and (= ?v2 (fun_app$c ?v0 ?v4)) (= ?v3 (lmap$ ?v0 ?v5))))))) :named a17))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lmap$b ?v0 ?v1) (lCons$a ?v2 ?v3)) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v1 (lCons$a ?v4 ?v5)) (and (= ?v2 (fun_app$a ?v0 ?v4)) (= ?v3 (lmap$b ?v0 ?v5))))))) :named a18))
(assert (! (forall ((?v0 A_llist$)) (=> (less$ (enat$ na$) (llength$ ?v0)) (= (fun_app$b (lnth$ (lmap$ f$ ?v0)) na$) (fun_app$c f$ (fun_app$d (lnth$a ?v0) na$))))) :named a19))
(assert (! (forall ((?v0 B$) (?v1 B_llist$) (?v2 B$) (?v3 B_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a20))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$a ?v0 ?v1) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a21))
(assert (! (forall ((?v0 Nat$) (?v1 Nat$)) (=> (= (suc$ ?v0) (suc$ ?v1)) (= ?v0 ?v1))) :named a22))
(assert (! (forall ((?v0 Nat$)) (not (= ?v0 (suc$ ?v0)))) :named a23))
(assert (! (less$ (enat$ (suc$ na$)) (llength$ xsa$)) :named a24))
(assert (! (forall ((?v0 B$) (?v1 B_llist$) (?v2 Nat$)) (! (= (fun_app$b (lnth$ (lCons$ ?v0 ?v1)) ?v2) (case_nat$ ?v0 (lnth$ ?v1) ?v2)) :pattern ((fun_app$b (lnth$ (lCons$ ?v0 ?v1)) ?v2)))) :named a25))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 Nat$)) (! (= (fun_app$d (lnth$a (lCons$a ?v0 ?v1)) ?v2) (case_nat$a ?v0 (lnth$a ?v1) ?v2)) :pattern ((fun_app$d (lnth$a (lCons$a ?v0 ?v1)) ?v2)))) :named a26))
(assert (! (less$ (enat$ na$) (llength$ xs$)) :named a27))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_llist$)) (= (llength$ (lmap$c ?v0 ?v1)) (llength$a ?v1))) :named a28))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_llist$)) (= (llength$a (lmap$a ?v0 ?v1)) (llength$a ?v1))) :named a29))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (llength$ (lmap$b ?v0 ?v1)) (llength$ ?v1))) :named a30))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_llist$)) (= (llength$a (lmap$ ?v0 ?v1)) (llength$ ?v1))) :named a31))
(check-sat)
;(get-unsat-core)
