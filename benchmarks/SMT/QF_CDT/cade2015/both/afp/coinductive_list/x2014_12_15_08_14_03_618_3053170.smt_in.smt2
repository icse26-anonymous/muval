; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 404
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort B_set$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_b_fun$ 0)
(declare-sort B_a_fun$ 0)
(declare-sort B_b_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-sort A_llist_b_llist_fun$ 0)
(declare-sort B_llist_a_llist_fun$ 0)
(declare-sort B_llist_b_llist_fun$ 0)
(declare-datatypes () ((Nat_option$ (none$) (some$ (the$ Nat$)))
  (Enat$ (abs_enat$ (rep_enat$ Nat_option$)))))
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))
  (B_llist$ (lNil$a) (lCons$a (lhd$a B$) (ltl$a B_llist$)))))
(declare-fun f$ () B_a_fun$)
(declare-fun xs$ () B_llist$)
(declare-fun lmap$ (B_a_fun$) B_llist_a_llist_fun$)
(declare-fun lset$ (A_llist$) A_set$)
(declare-fun lmap$a (A_a_fun$) A_llist_a_llist_fun$)
(declare-fun lmap$b (A_b_fun$) A_llist_b_llist_fun$)
(declare-fun lmap$c (B_b_fun$) B_llist_b_llist_fun$)
(declare-fun lnull$ (A_llist$) Bool)
(declare-fun lset$a (B_llist$) B_set$)
(declare-fun lnull$a (B_llist$) Bool)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun fun_app$ (B_llist_a_llist_fun$ B_llist$) A_llist$)
(declare-fun lappend$ (B_llist$ B_llist$) B_llist$)
(declare-fun lfinite$ (A_llist$) Bool)
(declare-fun llength$ (A_llist$) Enat$)
(declare-fun member$a (B$ B_set$) Bool)
(declare-fun fun_app$a (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun fun_app$b (A_llist_b_llist_fun$ A_llist$) B_llist$)
(declare-fun fun_app$c (B_llist_b_llist_fun$ B_llist$) B_llist$)
(declare-fun fun_app$d (A_b_fun$ A$) B$)
(declare-fun fun_app$e (A_a_fun$ A$) A$)
(declare-fun fun_app$f (B_b_fun$ B$) B$)
(declare-fun fun_app$g (B_a_fun$ B$) A$)
(declare-fun lappend$a (A_llist$ A_llist$) A_llist$)
(declare-fun lfinite$a (B_llist$) Bool)
(declare-fun llength$a (B_llist$) Enat$)
(assert (! (not (= (llength$ (fun_app$ (lmap$ f$) xs$)) (llength$a xs$))) :named a0))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (lfinite$ (fun_app$a (lmap$a ?v0) ?v1)) (lfinite$ ?v1))) :named a1))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_llist$)) (= (lfinite$a (fun_app$b (lmap$b ?v0) ?v1)) (lfinite$ ?v1))) :named a2))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_llist$)) (= (lfinite$a (fun_app$c (lmap$c ?v0) ?v1)) (lfinite$a ?v1))) :named a3))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_llist$)) (= (lfinite$ (fun_app$ (lmap$ ?v0) ?v1)) (lfinite$a ?v1))) :named a4))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (lnull$ (fun_app$a (lmap$a ?v0) ?v1)) (lnull$ ?v1))) :named a5))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_llist$)) (= (lnull$a (fun_app$b (lmap$b ?v0) ?v1)) (lnull$ ?v1))) :named a6))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_llist$)) (= (lnull$a (fun_app$c (lmap$c ?v0) ?v1)) (lnull$a ?v1))) :named a7))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_llist$)) (= (lnull$ (fun_app$ (lmap$ ?v0) ?v1)) (lnull$a ?v1))) :named a8))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (ltl$ (fun_app$a (lmap$a ?v0) ?v1)) (fun_app$a (lmap$a ?v0) (ltl$ ?v1)))) :named a9))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_llist$)) (= (ltl$a (fun_app$b (lmap$b ?v0) ?v1)) (fun_app$b (lmap$b ?v0) (ltl$ ?v1)))) :named a10))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_llist$)) (= (ltl$a (fun_app$c (lmap$c ?v0) ?v1)) (fun_app$c (lmap$c ?v0) (ltl$a ?v1)))) :named a11))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_llist$)) (= (ltl$ (fun_app$ (lmap$ ?v0) ?v1)) (fun_app$ (lmap$ ?v0) (ltl$a ?v1)))) :named a12))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_llist$) (?v2 B_llist$)) (= (fun_app$c (lmap$c ?v0) (lappend$ ?v1 ?v2)) (lappend$ (fun_app$c (lmap$c ?v0) ?v1) (fun_app$c (lmap$c ?v0) ?v2)))) :named a13))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_llist$) (?v2 A_llist$)) (= (fun_app$b (lmap$b ?v0) (lappend$a ?v1 ?v2)) (lappend$ (fun_app$b (lmap$b ?v0) ?v1) (fun_app$b (lmap$b ?v0) ?v2)))) :named a14))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$) (?v2 A_llist$)) (= (fun_app$a (lmap$a ?v0) (lappend$a ?v1 ?v2)) (lappend$a (fun_app$a (lmap$a ?v0) ?v1) (fun_app$a (lmap$a ?v0) ?v2)))) :named a15))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_llist$) (?v2 B_llist$)) (= (fun_app$ (lmap$ ?v0) (lappend$ ?v1 ?v2)) (lappend$a (fun_app$ (lmap$ ?v0) ?v1) (fun_app$ (lmap$ ?v0) ?v2)))) :named a16))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (= (fun_app$a (lmap$a ?v0) ?v1) lNil$) (= ?v1 lNil$))) :named a17))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_llist$)) (= (= (fun_app$b (lmap$b ?v0) ?v1) lNil$a) (= ?v1 lNil$))) :named a18))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_llist$)) (= (= (fun_app$c (lmap$c ?v0) ?v1) lNil$a) (= ?v1 lNil$a))) :named a19))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_llist$)) (= (= (fun_app$ (lmap$ ?v0) ?v1) lNil$) (= ?v1 lNil$a))) :named a20))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$)) (= (= lNil$ (fun_app$a (lmap$a ?v0) ?v1)) (= ?v1 lNil$))) :named a21))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_llist$)) (= (= lNil$a (fun_app$b (lmap$b ?v0) ?v1)) (= ?v1 lNil$))) :named a22))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_llist$)) (= (= lNil$a (fun_app$c (lmap$c ?v0) ?v1)) (= ?v1 lNil$a))) :named a23))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_llist$)) (= (= lNil$ (fun_app$ (lmap$ ?v0) ?v1)) (= ?v1 lNil$a))) :named a24))
(assert (! (forall ((?v0 A_a_fun$)) (! (= (fun_app$a (lmap$a ?v0) lNil$) lNil$) :pattern ((lmap$a ?v0)))) :named a25))
(assert (! (forall ((?v0 A_b_fun$)) (! (= (fun_app$b (lmap$b ?v0) lNil$) lNil$a) :pattern ((lmap$b ?v0)))) :named a26))
(assert (! (forall ((?v0 B_b_fun$)) (! (= (fun_app$c (lmap$c ?v0) lNil$a) lNil$a) :pattern ((lmap$c ?v0)))) :named a27))
(assert (! (forall ((?v0 B_a_fun$)) (! (= (fun_app$ (lmap$ ?v0) lNil$a) lNil$) :pattern ((lmap$ ?v0)))) :named a28))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_b_fun$) (?v3 A_b_fun$)) (=> (and (forall ((?v4 A$) (?v5 A$)) (=> (and (member$ ?v4 (lset$ ?v0)) (and (member$ ?v5 (lset$ ?v1)) (= (fun_app$d ?v2 ?v4) (fun_app$d ?v3 ?v5)))) (= ?v4 ?v5))) (= (fun_app$b (lmap$b ?v2) ?v0) (fun_app$b (lmap$b ?v3) ?v1))) (= ?v0 ?v1))) :named a29))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_a_fun$) (?v3 A_a_fun$)) (=> (and (forall ((?v4 A$) (?v5 A$)) (=> (and (member$ ?v4 (lset$ ?v0)) (and (member$ ?v5 (lset$ ?v1)) (= (fun_app$e ?v2 ?v4) (fun_app$e ?v3 ?v5)))) (= ?v4 ?v5))) (= (fun_app$a (lmap$a ?v2) ?v0) (fun_app$a (lmap$a ?v3) ?v1))) (= ?v0 ?v1))) :named a30))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$) (?v2 B_b_fun$) (?v3 B_b_fun$)) (=> (and (forall ((?v4 B$) (?v5 B$)) (=> (and (member$a ?v4 (lset$a ?v0)) (and (member$a ?v5 (lset$a ?v1)) (= (fun_app$f ?v2 ?v4) (fun_app$f ?v3 ?v5)))) (= ?v4 ?v5))) (= (fun_app$c (lmap$c ?v2) ?v0) (fun_app$c (lmap$c ?v3) ?v1))) (= ?v0 ?v1))) :named a31))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$) (?v2 B_a_fun$) (?v3 B_a_fun$)) (=> (and (forall ((?v4 B$) (?v5 B$)) (=> (and (member$a ?v4 (lset$a ?v0)) (and (member$a ?v5 (lset$a ?v1)) (= (fun_app$g ?v2 ?v4) (fun_app$g ?v3 ?v5)))) (= ?v4 ?v5))) (= (fun_app$ (lmap$ ?v2) ?v0) (fun_app$ (lmap$ ?v3) ?v1))) (= ?v0 ?v1))) :named a32))
(assert (! (forall ((?v0 A_llist$) (?v1 A_b_fun$) (?v2 A_b_fun$)) (=> (forall ((?v3 A$)) (=> (member$ ?v3 (lset$ ?v0)) (= (fun_app$d ?v1 ?v3) (fun_app$d ?v2 ?v3)))) (= (fun_app$b (lmap$b ?v1) ?v0) (fun_app$b (lmap$b ?v2) ?v0)))) :named a33))
(assert (! (forall ((?v0 A_llist$) (?v1 A_a_fun$) (?v2 A_a_fun$)) (=> (forall ((?v3 A$)) (=> (member$ ?v3 (lset$ ?v0)) (= (fun_app$e ?v1 ?v3) (fun_app$e ?v2 ?v3)))) (= (fun_app$a (lmap$a ?v1) ?v0) (fun_app$a (lmap$a ?v2) ?v0)))) :named a34))
(assert (! (forall ((?v0 B_llist$) (?v1 B_b_fun$) (?v2 B_b_fun$)) (=> (forall ((?v3 B$)) (=> (member$a ?v3 (lset$a ?v0)) (= (fun_app$f ?v1 ?v3) (fun_app$f ?v2 ?v3)))) (= (fun_app$c (lmap$c ?v1) ?v0) (fun_app$c (lmap$c ?v2) ?v0)))) :named a35))
(assert (! (forall ((?v0 B_llist$) (?v1 B_a_fun$) (?v2 B_a_fun$)) (=> (forall ((?v3 B$)) (=> (member$a ?v3 (lset$a ?v0)) (= (fun_app$g ?v1 ?v3) (fun_app$g ?v2 ?v3)))) (= (fun_app$ (lmap$ ?v1) ?v0) (fun_app$ (lmap$ ?v2) ?v0)))) :named a36))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_b_fun$) (?v3 A_b_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 A$)) (=> (member$ ?v4 (lset$ ?v1)) (= (fun_app$d ?v2 ?v4) (fun_app$d ?v3 ?v4))))) (= (fun_app$b (lmap$b ?v2) ?v0) (fun_app$b (lmap$b ?v3) ?v1)))) :named a37))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$) (?v2 A_a_fun$) (?v3 A_a_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 A$)) (=> (member$ ?v4 (lset$ ?v1)) (= (fun_app$e ?v2 ?v4) (fun_app$e ?v3 ?v4))))) (= (fun_app$a (lmap$a ?v2) ?v0) (fun_app$a (lmap$a ?v3) ?v1)))) :named a38))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$) (?v2 B_b_fun$) (?v3 B_b_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 B$)) (=> (member$a ?v4 (lset$a ?v1)) (= (fun_app$f ?v2 ?v4) (fun_app$f ?v3 ?v4))))) (= (fun_app$c (lmap$c ?v2) ?v0) (fun_app$c (lmap$c ?v3) ?v1)))) :named a39))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$) (?v2 B_a_fun$) (?v3 B_a_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 B$)) (=> (member$a ?v4 (lset$a ?v1)) (= (fun_app$g ?v2 ?v4) (fun_app$g ?v3 ?v4))))) (= (fun_app$ (lmap$ ?v2) ?v0) (fun_app$ (lmap$ ?v3) ?v1)))) :named a40))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B$) (?v2 B_llist$)) (! (= (fun_app$c (lmap$c ?v0) (lCons$a ?v1 ?v2)) (lCons$a (fun_app$f ?v0 ?v1) (fun_app$c (lmap$c ?v0) ?v2))) :pattern ((fun_app$c (lmap$c ?v0) (lCons$a ?v1 ?v2))))) :named a41))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$b (lmap$b ?v0) (lCons$ ?v1 ?v2)) (lCons$a (fun_app$d ?v0 ?v1) (fun_app$b (lmap$b ?v0) ?v2))) :pattern ((fun_app$b (lmap$b ?v0) (lCons$ ?v1 ?v2))))) :named a42))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$a (lmap$a ?v0) (lCons$ ?v1 ?v2)) (lCons$ (fun_app$e ?v0 ?v1) (fun_app$a (lmap$a ?v0) ?v2))) :pattern ((fun_app$a (lmap$a ?v0) (lCons$ ?v1 ?v2))))) :named a43))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B$) (?v2 B_llist$)) (! (= (fun_app$ (lmap$ ?v0) (lCons$a ?v1 ?v2)) (lCons$ (fun_app$g ?v0 ?v1) (fun_app$ (lmap$ ?v0) ?v2))) :pattern ((fun_app$ (lmap$ ?v0) (lCons$a ?v1 ?v2))))) :named a44))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_llist$) (?v2 B$) (?v3 B_llist$)) (= (= (fun_app$c (lmap$c ?v0) ?v1) (lCons$a ?v2 ?v3)) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v1 (lCons$a ?v4 ?v5)) (and (= ?v2 (fun_app$f ?v0 ?v4)) (= ?v3 (fun_app$c (lmap$c ?v0) ?v5))))))) :named a45))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A_llist$) (?v2 B$) (?v3 B_llist$)) (= (= (fun_app$b (lmap$b ?v0) ?v1) (lCons$a ?v2 ?v3)) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v1 (lCons$ ?v4 ?v5)) (and (= ?v2 (fun_app$d ?v0 ?v4)) (= ?v3 (fun_app$b (lmap$b ?v0) ?v5))))))) :named a46))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (fun_app$a (lmap$a ?v0) ?v1) (lCons$ ?v2 ?v3)) (exists ((?v4 A$) (?v5 A_llist$)) (and (= ?v1 (lCons$ ?v4 ?v5)) (and (= ?v2 (fun_app$e ?v0 ?v4)) (= ?v3 (fun_app$a (lmap$a ?v0) ?v5))))))) :named a47))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (fun_app$ (lmap$ ?v0) ?v1) (lCons$ ?v2 ?v3)) (exists ((?v4 B$) (?v5 B_llist$)) (and (= ?v1 (lCons$a ?v4 ?v5)) (and (= ?v2 (fun_app$g ?v0 ?v4)) (= ?v3 (fun_app$ (lmap$ ?v0) ?v5))))))) :named a48))
(assert (! (forall ((?v0 B$) (?v1 B_llist$) (?v2 B$) (?v3 B_llist$)) (= (= (lCons$a ?v0 ?v1) (lCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a49))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a50))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (not (lnull$ (lappend$a ?v0 ?v1))) (or (not (lnull$ ?v0)) (not (lnull$ ?v1))))) :named a51))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (= (not (lnull$a (lappend$ ?v0 ?v1))) (or (not (lnull$a ?v0)) (not (lnull$a ?v1))))) :named a52))
(assert (! (forall ((?v0 A_llist$) (?v1 A_llist$)) (= (lnull$ (lappend$a ?v0 ?v1)) (and (lnull$ ?v0) (lnull$ ?v1)))) :named a53))
(assert (! (forall ((?v0 B_llist$) (?v1 B_llist$)) (= (lnull$a (lappend$ ?v0 ?v1)) (and (lnull$a ?v0) (lnull$a ?v1)))) :named a54))
(assert (! (forall ((?v0 B$) (?v1 B_llist$) (?v2 B_llist$)) (! (= (lappend$ (lCons$a ?v0 ?v1) ?v2) (lCons$a ?v0 (lappend$ ?v1 ?v2))) :pattern ((lappend$ (lCons$a ?v0 ?v1) ?v2)))) :named a55))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A_llist$)) (! (= (lappend$a (lCons$ ?v0 ?v1) ?v2) (lCons$ ?v0 (lappend$a ?v1 ?v2))) :pattern ((lappend$a (lCons$ ?v0 ?v1) ?v2)))) :named a56))
(assert (! (forall ((?v0 B$) (?v1 B_llist$)) (! (= (lfinite$a (lCons$a ?v0 ?v1)) (lfinite$a ?v1)) :pattern ((lCons$a ?v0 ?v1)))) :named a57))
(assert (! (forall ((?v0 A$) (?v1 A_llist$)) (! (= (lfinite$ (lCons$ ?v0 ?v1)) (lfinite$ ?v1)) :pattern ((lCons$ ?v0 ?v1)))) :named a58))
(check-sat)
;(get-unsat-core)
