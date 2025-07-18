; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 498
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort A_set$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort Bool_a_fun$ 0)
(declare-sort Bool_llist$ 0)
(declare-sort Bool_bool_fun$ 0)
(declare-sort A_a_fun_a_a_fun_fun$ 0)
(declare-sort A_llist_a_llist_fun$ 0)
(declare-sort A_a_fun_a_bool_fun_fun$ 0)
(declare-sort A_bool_fun_a_a_fun_fun$ 0)
(declare-sort A_bool_fun_a_bool_fun_fun$ 0)
(declare-sort Bool_a_fun_bool_a_fun_fun$ 0)
(declare-sort Bool_llist_bool_llist_fun$ 0)
(declare-sort Bool_a_fun_bool_bool_fun_fun$ 0)
(declare-sort Bool_bool_fun_bool_a_fun_fun$ 0)
(declare-sort Bool_bool_fun_bool_bool_fun_fun$ 0)
(declare-codatatypes () ((A_llist$ (lNil$) (lCons$ (lhd$ A$) (ltl$ A_llist$)))))
(declare-fun p$ () A_bool_fun$)
(declare-fun x$ () A$)
(declare-fun uu$ () Bool_bool_fun$)
(declare-fun xs$ () A_llist$)
(declare-fun ys$ () A_llist$)
(declare-fun comp$ (Bool_bool_fun$) A_bool_fun_a_bool_fun_fun$)
(declare-fun lhd$a (Bool_llist$) Bool)
(declare-fun lset$ (A_llist$) A_set$)
(declare-fun ltl$a (Bool_llist$) Bool_llist$)
(declare-fun comp$a (Bool_bool_fun$) Bool_bool_fun_bool_bool_fun_fun$)
(declare-fun comp$b (A_a_fun$) A_a_fun_a_a_fun_fun$)
(declare-fun comp$c (Bool_a_fun$) A_bool_fun_a_a_fun_fun$)
(declare-fun comp$d (A_bool_fun$) Bool_a_fun_bool_bool_fun_fun$)
(declare-fun comp$e (A_bool_fun$) A_a_fun_a_bool_fun_fun$)
(declare-fun comp$f (Bool_a_fun$) Bool_bool_fun_bool_a_fun_fun$)
(declare-fun comp$g (A_a_fun$) Bool_a_fun_bool_a_fun_fun$)
(declare-fun lNil$a () Bool_llist$)
(declare-fun lnull$ (A_llist$) Bool)
(declare-fun lCons$a (Bool Bool_llist$) Bool_llist$)
(declare-fun member$ (A$ A_set$) Bool)
(declare-fun fun_app$ (Bool_bool_fun$ Bool) Bool)
(declare-fun lfilter$ (A_bool_fun$) A_llist_a_llist_fun$)
(declare-fun fun_app$a (A_llist_a_llist_fun$ A_llist$) A_llist$)
(declare-fun fun_app$b (A_bool_fun_a_bool_fun_fun$ A_bool_fun$) A_bool_fun$)
(declare-fun fun_app$c (Bool_llist_bool_llist_fun$ Bool_llist$) Bool_llist$)
(declare-fun fun_app$d (Bool_bool_fun_bool_bool_fun_fun$ Bool_bool_fun$) Bool_bool_fun$)
(declare-fun fun_app$e (A_bool_fun$ A$) Bool)
(declare-fun fun_app$f (A_a_fun$ A$) A$)
(declare-fun fun_app$g (A_a_fun_a_a_fun_fun$ A_a_fun$) A_a_fun$)
(declare-fun fun_app$h (A_bool_fun_a_a_fun_fun$ A_bool_fun$) A_a_fun$)
(declare-fun fun_app$i (Bool_a_fun$ Bool) A$)
(declare-fun fun_app$j (Bool_a_fun_bool_bool_fun_fun$ Bool_a_fun$) Bool_bool_fun$)
(declare-fun fun_app$k (A_a_fun_a_bool_fun_fun$ A_a_fun$) A_bool_fun$)
(declare-fun fun_app$l (Bool_bool_fun_bool_a_fun_fun$ Bool_bool_fun$) Bool_a_fun$)
(declare-fun fun_app$m (Bool_a_fun_bool_a_fun_fun$ Bool_a_fun$) Bool_a_fun$)
(declare-fun lfilter$a (Bool_bool_fun$) Bool_llist_bool_llist_fun$)
(declare-fun ldropWhile$ (A_bool_fun$) A_llist_a_llist_fun$)
(declare-fun ldropWhile$a (Bool_bool_fun$) Bool_llist_bool_llist_fun$)
(assert (! (forall ((?v0 Bool)) (! (= (fun_app$ uu$ ?v0) (not ?v0)) :pattern ((fun_app$ uu$ ?v0)))) :named a0))
(assert (! (not (= x$ (lhd$ (fun_app$a (ldropWhile$ (fun_app$b (comp$ uu$) p$)) ys$)))) :named a1))
(assert (! (and (not (= (fun_app$a (lfilter$ p$) ys$) lNil$)) (and (= (lhd$ (fun_app$a (lfilter$ p$) ys$)) x$) (= (ltl$ (fun_app$a (lfilter$ p$) ys$)) xs$))) :named a2))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_llist$)) (= (lhd$a (fun_app$c (lfilter$a ?v0) ?v1)) (lhd$a (fun_app$c (ldropWhile$a (fun_app$d (comp$a uu$) ?v0)) ?v1)))) :named a3))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_llist$)) (= (lhd$ (fun_app$a (lfilter$ ?v0) ?v1)) (lhd$ (fun_app$a (ldropWhile$ (fun_app$b (comp$ uu$) ?v0)) ?v1)))) :named a4))
(assert (! (= (fun_app$a (lfilter$ p$) ys$) (lCons$ x$ xs$)) :named a5))
(assert (! (forall ((?v0 Bool_bool_fun$)) (! (= (fun_app$c (ldropWhile$a ?v0) lNil$a) lNil$a) :pattern ((ldropWhile$a ?v0)))) :named a6))
(assert (! (forall ((?v0 A_bool_fun$)) (! (= (fun_app$a (ldropWhile$ ?v0) lNil$) lNil$) :pattern ((ldropWhile$ ?v0)))) :named a7))
(assert (! (exists ((?v0 A$)) (and (member$ ?v0 (lset$ ys$)) (fun_app$e p$ ?v0))) :named a8))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A$)) (! (= (fun_app$f (fun_app$g (comp$b ?v0) ?v1) ?v2) (fun_app$f ?v0 (fun_app$f ?v1 ?v2))) :pattern ((fun_app$f (fun_app$g (comp$b ?v0) ?v1) ?v2)))) :named a9))
(assert (! (forall ((?v0 Bool_a_fun$) (?v1 A_bool_fun$) (?v2 A$)) (! (= (fun_app$f (fun_app$h (comp$c ?v0) ?v1) ?v2) (fun_app$i ?v0 (fun_app$e ?v1 ?v2))) :pattern ((fun_app$f (fun_app$h (comp$c ?v0) ?v1) ?v2)))) :named a10))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 Bool_a_fun$) (?v2 Bool)) (! (= (fun_app$ (fun_app$j (comp$d ?v0) ?v1) ?v2) (fun_app$e ?v0 (fun_app$i ?v1 ?v2))) :pattern ((fun_app$ (fun_app$j (comp$d ?v0) ?v1) ?v2)))) :named a11))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_bool_fun$) (?v2 Bool)) (! (= (fun_app$ (fun_app$d (comp$a ?v0) ?v1) ?v2) (fun_app$ ?v0 (fun_app$ ?v1 ?v2))) :pattern ((fun_app$ (fun_app$d (comp$a ?v0) ?v1) ?v2)))) :named a12))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_a_fun$) (?v2 A$)) (! (= (fun_app$e (fun_app$k (comp$e ?v0) ?v1) ?v2) (fun_app$e ?v0 (fun_app$f ?v1 ?v2))) :pattern ((fun_app$e (fun_app$k (comp$e ?v0) ?v1) ?v2)))) :named a13))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_bool_fun$) (?v2 A$)) (! (= (fun_app$e (fun_app$b (comp$ ?v0) ?v1) ?v2) (fun_app$ ?v0 (fun_app$e ?v1 ?v2))) :pattern ((fun_app$e (fun_app$b (comp$ ?v0) ?v1) ?v2)))) :named a14))
(assert (! (not (lnull$ (fun_app$a (lfilter$ p$) ys$))) :named a15))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_llist$)) (= (ltl$a (fun_app$c (lfilter$a ?v0) ?v1)) (fun_app$c (lfilter$a ?v0) (ltl$a (fun_app$c (ldropWhile$a (fun_app$d (comp$a uu$) ?v0)) ?v1))))) :named a16))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_llist$)) (= (ltl$ (fun_app$a (lfilter$ ?v0) ?v1)) (fun_app$a (lfilter$ ?v0) (ltl$ (fun_app$a (ldropWhile$ (fun_app$b (comp$ uu$) ?v0)) ?v1))))) :named a17))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_llist$)) (= (fun_app$c (lfilter$a ?v0) (fun_app$c (lfilter$a ?v0) ?v1)) (fun_app$c (lfilter$a ?v0) ?v1))) :named a18))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_llist$)) (= (fun_app$a (lfilter$ ?v0) (fun_app$a (lfilter$ ?v0) ?v1)) (fun_app$a (lfilter$ ?v0) ?v1))) :named a19))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_bool_fun$) (?v2 A_a_fun$)) (= (fun_app$b (comp$ ?v0) (fun_app$k (comp$e ?v1) ?v2)) (fun_app$k (comp$e (fun_app$b (comp$ ?v0) ?v1)) ?v2))) :named a20))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_bool_fun$) (?v2 A_bool_fun$)) (= (fun_app$b (comp$ ?v0) (fun_app$b (comp$ ?v1) ?v2)) (fun_app$b (comp$ (fun_app$d (comp$a ?v0) ?v1)) ?v2))) :named a21))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_bool_fun$) (?v2 Bool_a_fun$)) (= (fun_app$d (comp$a ?v0) (fun_app$j (comp$d ?v1) ?v2)) (fun_app$j (comp$d (fun_app$b (comp$ ?v0) ?v1)) ?v2))) :named a22))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_bool_fun$) (?v2 Bool_bool_fun$)) (= (fun_app$d (comp$a ?v0) (fun_app$d (comp$a ?v1) ?v2)) (fun_app$d (comp$a (fun_app$d (comp$a ?v0) ?v1)) ?v2))) :named a23))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 Bool_a_fun$) (?v2 A_bool_fun$)) (= (fun_app$k (comp$e ?v0) (fun_app$h (comp$c ?v1) ?v2)) (fun_app$b (comp$ (fun_app$j (comp$d ?v0) ?v1)) ?v2))) :named a24))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_a_fun$) (?v2 A_a_fun$)) (= (fun_app$k (comp$e ?v0) (fun_app$g (comp$b ?v1) ?v2)) (fun_app$k (comp$e (fun_app$k (comp$e ?v0) ?v1)) ?v2))) :named a25))
(assert (! (forall ((?v0 Bool_a_fun$) (?v1 A_bool_fun$) (?v2 Bool_a_fun$)) (= (fun_app$l (comp$f ?v0) (fun_app$j (comp$d ?v1) ?v2)) (fun_app$m (comp$g (fun_app$h (comp$c ?v0) ?v1)) ?v2))) :named a26))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_a_fun$)) (= (fun_app$g (comp$b ?v0) (fun_app$g (comp$b ?v1) ?v2)) (fun_app$g (comp$b (fun_app$g (comp$b ?v0) ?v1)) ?v2))) :named a27))
(assert (! (forall ((?v0 A_a_fun$) (?v1 Bool_a_fun$) (?v2 A_bool_fun$)) (= (fun_app$g (comp$b ?v0) (fun_app$h (comp$c ?v1) ?v2)) (fun_app$h (comp$c (fun_app$m (comp$g ?v0) ?v1)) ?v2))) :named a28))
(assert (! (forall ((?v0 Bool_a_fun$) (?v1 Bool_bool_fun$) (?v2 A_bool_fun$)) (= (fun_app$h (comp$c ?v0) (fun_app$b (comp$ ?v1) ?v2)) (fun_app$h (comp$c (fun_app$l (comp$f ?v0) ?v1)) ?v2))) :named a29))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_bool_fun$) (?v2 A_a_fun$)) (= (fun_app$k (comp$e (fun_app$b (comp$ ?v0) ?v1)) ?v2) (fun_app$b (comp$ ?v0) (fun_app$k (comp$e ?v1) ?v2)))) :named a30))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_bool_fun$) (?v2 A_bool_fun$)) (= (fun_app$b (comp$ (fun_app$d (comp$a ?v0) ?v1)) ?v2) (fun_app$b (comp$ ?v0) (fun_app$b (comp$ ?v1) ?v2)))) :named a31))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_bool_fun$) (?v2 Bool_a_fun$)) (= (fun_app$j (comp$d (fun_app$b (comp$ ?v0) ?v1)) ?v2) (fun_app$d (comp$a ?v0) (fun_app$j (comp$d ?v1) ?v2)))) :named a32))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 Bool_a_fun$) (?v2 A_bool_fun$)) (= (fun_app$b (comp$ (fun_app$j (comp$d ?v0) ?v1)) ?v2) (fun_app$k (comp$e ?v0) (fun_app$h (comp$c ?v1) ?v2)))) :named a33))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_bool_fun$) (?v2 Bool_bool_fun$)) (= (fun_app$d (comp$a (fun_app$d (comp$a ?v0) ?v1)) ?v2) (fun_app$d (comp$a ?v0) (fun_app$d (comp$a ?v1) ?v2)))) :named a34))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_a_fun$) (?v2 A_a_fun$)) (= (fun_app$k (comp$e (fun_app$k (comp$e ?v0) ?v1)) ?v2) (fun_app$k (comp$e ?v0) (fun_app$g (comp$b ?v1) ?v2)))) :named a35))
(assert (! (forall ((?v0 Bool_a_fun$) (?v1 A_bool_fun$) (?v2 Bool_a_fun$)) (= (fun_app$m (comp$g (fun_app$h (comp$c ?v0) ?v1)) ?v2) (fun_app$l (comp$f ?v0) (fun_app$j (comp$d ?v1) ?v2)))) :named a36))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 Bool_a_fun$) (?v2 Bool_bool_fun$)) (= (fun_app$d (comp$a (fun_app$j (comp$d ?v0) ?v1)) ?v2) (fun_app$j (comp$d ?v0) (fun_app$l (comp$f ?v1) ?v2)))) :named a37))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_a_fun$)) (= (fun_app$g (comp$b (fun_app$g (comp$b ?v0) ?v1)) ?v2) (fun_app$g (comp$b ?v0) (fun_app$g (comp$b ?v1) ?v2)))) :named a38))
(assert (! (forall ((?v0 Bool_a_fun$) (?v1 A_bool_fun$) (?v2 A_a_fun$)) (= (fun_app$g (comp$b (fun_app$h (comp$c ?v0) ?v1)) ?v2) (fun_app$h (comp$c ?v0) (fun_app$k (comp$e ?v1) ?v2)))) :named a39))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A$)) (! (= (fun_app$f (fun_app$g (comp$b ?v0) ?v1) ?v2) (fun_app$f ?v0 (fun_app$f ?v1 ?v2))) :pattern ((fun_app$f (fun_app$g (comp$b ?v0) ?v1) ?v2)))) :named a40))
(assert (! (forall ((?v0 Bool_a_fun$) (?v1 A_bool_fun$) (?v2 A$)) (! (= (fun_app$f (fun_app$h (comp$c ?v0) ?v1) ?v2) (fun_app$i ?v0 (fun_app$e ?v1 ?v2))) :pattern ((fun_app$f (fun_app$h (comp$c ?v0) ?v1) ?v2)))) :named a41))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 Bool_a_fun$) (?v2 Bool)) (! (= (fun_app$ (fun_app$j (comp$d ?v0) ?v1) ?v2) (fun_app$e ?v0 (fun_app$i ?v1 ?v2))) :pattern ((fun_app$ (fun_app$j (comp$d ?v0) ?v1) ?v2)))) :named a42))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_bool_fun$) (?v2 Bool)) (! (= (fun_app$ (fun_app$d (comp$a ?v0) ?v1) ?v2) (fun_app$ ?v0 (fun_app$ ?v1 ?v2))) :pattern ((fun_app$ (fun_app$d (comp$a ?v0) ?v1) ?v2)))) :named a43))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_a_fun$) (?v2 A$)) (! (= (fun_app$e (fun_app$k (comp$e ?v0) ?v1) ?v2) (fun_app$e ?v0 (fun_app$f ?v1 ?v2))) :pattern ((fun_app$e (fun_app$k (comp$e ?v0) ?v1) ?v2)))) :named a44))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_bool_fun$) (?v2 A$)) (! (= (fun_app$e (fun_app$b (comp$ ?v0) ?v1) ?v2) (fun_app$ ?v0 (fun_app$e ?v1 ?v2))) :pattern ((fun_app$e (fun_app$b (comp$ ?v0) ?v1) ?v2)))) :named a45))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_bool_fun$) (?v2 Bool_bool_fun$) (?v3 A_bool_fun$)) (=> (and (= (fun_app$b (comp$ ?v0) ?v1) (fun_app$b (comp$ ?v2) ?v3)) (=> (forall ((?v4 A$)) (= (fun_app$ ?v0 (fun_app$e ?v1 ?v4)) (fun_app$ ?v2 (fun_app$e ?v3 ?v4)))) false)) false)) :named a46))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 A_bool_fun$) (?v2 A_bool_fun$) (?v3 A_a_fun$)) (=> (and (= (fun_app$b (comp$ ?v0) ?v1) (fun_app$k (comp$e ?v2) ?v3)) (=> (forall ((?v4 A$)) (= (fun_app$ ?v0 (fun_app$e ?v1 ?v4)) (fun_app$e ?v2 (fun_app$f ?v3 ?v4)))) false)) false)) :named a47))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_bool_fun$) (?v2 Bool_bool_fun$) (?v3 Bool_bool_fun$)) (=> (and (= (fun_app$d (comp$a ?v0) ?v1) (fun_app$d (comp$a ?v2) ?v3)) (=> (forall ((?v4 Bool)) (= (fun_app$ ?v0 (fun_app$ ?v1 ?v4)) (fun_app$ ?v2 (fun_app$ ?v3 ?v4)))) false)) false)) :named a48))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_a_fun$) (?v2 Bool_bool_fun$) (?v3 A_bool_fun$)) (=> (and (= (fun_app$k (comp$e ?v0) ?v1) (fun_app$b (comp$ ?v2) ?v3)) (=> (forall ((?v4 A$)) (= (fun_app$e ?v0 (fun_app$f ?v1 ?v4)) (fun_app$ ?v2 (fun_app$e ?v3 ?v4)))) false)) false)) :named a49))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A_a_fun$) (?v2 A_bool_fun$) (?v3 A_a_fun$)) (=> (and (= (fun_app$k (comp$e ?v0) ?v1) (fun_app$k (comp$e ?v2) ?v3)) (=> (forall ((?v4 A$)) (= (fun_app$e ?v0 (fun_app$f ?v1 ?v4)) (fun_app$e ?v2 (fun_app$f ?v3 ?v4)))) false)) false)) :named a50))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool_bool_fun$) (?v2 A_bool_fun$) (?v3 Bool_a_fun$)) (=> (and (= (fun_app$d (comp$a ?v0) ?v1) (fun_app$j (comp$d ?v2) ?v3)) (=> (forall ((?v4 Bool)) (= (fun_app$ ?v0 (fun_app$ ?v1 ?v4)) (fun_app$e ?v2 (fun_app$i ?v3 ?v4)))) false)) false)) :named a51))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 A_a_fun$) (?v3 A_a_fun$)) (=> (and (= (fun_app$g (comp$b ?v0) ?v1) (fun_app$g (comp$b ?v2) ?v3)) (=> (forall ((?v4 A$)) (= (fun_app$f ?v0 (fun_app$f ?v1 ?v4)) (fun_app$f ?v2 (fun_app$f ?v3 ?v4)))) false)) false)) :named a52))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_a_fun$) (?v2 Bool_a_fun$) (?v3 A_bool_fun$)) (=> (and (= (fun_app$g (comp$b ?v0) ?v1) (fun_app$h (comp$c ?v2) ?v3)) (=> (forall ((?v4 A$)) (= (fun_app$f ?v0 (fun_app$f ?v1 ?v4)) (fun_app$i ?v2 (fun_app$e ?v3 ?v4)))) false)) false)) :named a53))
(assert (! (forall ((?v0 Bool_a_fun$) (?v1 A_bool_fun$) (?v2 A_a_fun$) (?v3 A_a_fun$)) (=> (and (= (fun_app$h (comp$c ?v0) ?v1) (fun_app$g (comp$b ?v2) ?v3)) (=> (forall ((?v4 A$)) (= (fun_app$i ?v0 (fun_app$e ?v1 ?v4)) (fun_app$f ?v2 (fun_app$f ?v3 ?v4)))) false)) false)) :named a54))
(assert (! (forall ((?v0 Bool_a_fun$) (?v1 A_bool_fun$) (?v2 Bool_a_fun$) (?v3 A_bool_fun$)) (=> (and (= (fun_app$h (comp$c ?v0) ?v1) (fun_app$h (comp$c ?v2) ?v3)) (=> (forall ((?v4 A$)) (= (fun_app$i ?v0 (fun_app$e ?v1 ?v4)) (fun_app$i ?v2 (fun_app$e ?v3 ?v4)))) false)) false)) :named a55))
(assert (! (forall ((?v0 A$) (?v1 A_llist$) (?v2 A$) (?v3 A_llist$)) (= (= (lCons$ ?v0 ?v1) (lCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a56))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool) (?v2 Bool_llist$)) (! (= (fun_app$c (lfilter$a ?v0) (lCons$a ?v1 ?v2)) (ite (fun_app$ ?v0 ?v1) (lCons$a ?v1 (fun_app$c (lfilter$a ?v0) ?v2)) (fun_app$c (lfilter$a ?v0) ?v2))) :pattern ((fun_app$c (lfilter$a ?v0) (lCons$a ?v1 ?v2))))) :named a57))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$a (lfilter$ ?v0) (lCons$ ?v1 ?v2)) (ite (fun_app$e ?v0 ?v1) (lCons$ ?v1 (fun_app$a (lfilter$ ?v0) ?v2)) (fun_app$a (lfilter$ ?v0) ?v2))) :pattern ((fun_app$a (lfilter$ ?v0) (lCons$ ?v1 ?v2))))) :named a58))
(assert (! (forall ((?v0 Bool_bool_fun$)) (! (= (fun_app$c (lfilter$a ?v0) lNil$a) lNil$a) :pattern ((lfilter$a ?v0)))) :named a59))
(assert (! (forall ((?v0 A_bool_fun$)) (! (= (fun_app$a (lfilter$ ?v0) lNil$) lNil$) :pattern ((lfilter$ ?v0)))) :named a60))
(assert (! (forall ((?v0 Bool_bool_fun$) (?v1 Bool) (?v2 Bool_llist$)) (! (= (fun_app$c (ldropWhile$a ?v0) (lCons$a ?v1 ?v2)) (ite (fun_app$ ?v0 ?v1) (fun_app$c (ldropWhile$a ?v0) ?v2) (lCons$a ?v1 ?v2))) :pattern ((fun_app$c (ldropWhile$a ?v0) (lCons$a ?v1 ?v2))))) :named a61))
(assert (! (forall ((?v0 A_bool_fun$) (?v1 A$) (?v2 A_llist$)) (! (= (fun_app$a (ldropWhile$ ?v0) (lCons$ ?v1 ?v2)) (ite (fun_app$e ?v0 ?v1) (fun_app$a (ldropWhile$ ?v0) ?v2) (lCons$ ?v1 ?v2))) :pattern ((fun_app$a (ldropWhile$ ?v0) (lCons$ ?v1 ?v2))))) :named a62))
(check-sat)
;(get-unsat-core)
