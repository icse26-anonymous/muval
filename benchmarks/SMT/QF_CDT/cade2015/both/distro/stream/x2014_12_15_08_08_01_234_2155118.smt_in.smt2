; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 212
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort Nat$ 0)
(declare-sort A_set$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_stream_set$ 0)
(declare-sort A_a_stream_fun$ 0)
(declare-sort A_stream_a_fun$ 0)
(declare-sort A_stream_stream_set$ 0)
(declare-sort A_a_stream_stream_fun$ 0)
(declare-sort A_stream_a_stream_fun$ 0)
(declare-sort A_stream_stream_a_fun$ 0)
(declare-sort A_stream_stream_stream_set$ 0)
(declare-sort A_stream_a_stream_stream_fun$ 0)
(declare-sort A_stream_stream_a_stream_fun$ 0)
(declare-sort A_stream_stream_stream_a_fun$ 0)
(declare-sort A_stream_stream_stream_stream_set$ 0)
(declare-sort A_stream_stream_a_stream_stream_fun$ 0)
(declare-codatatypes () ((A_stream$ (sCons$ (shd$ A$) (stl$ A_stream$)))
  (A_stream_stream$ (sCons$a (shd$a A_stream$) (stl$a A_stream_stream$)))
  (A_stream_stream_stream$ (sCons$b (shd$b A_stream_stream$) (stl$b A_stream_stream_stream$)))
  (A_stream_stream_stream_stream$ (sCons$c (shd$c A_stream_stream_stream$) (stl$c A_stream_stream_stream_stream$)))))
(declare-fun a$ () A_set$)
(declare-fun x$ () A$)
(declare-fun id$ () A_a_fun$)
(declare-fun id$a () A_stream_a_stream_fun$)
(declare-fun id$b () A_stream_stream_a_stream_stream_fun$)
(declare-fun smap$ (A_stream_a_stream_stream_fun$ A_stream_stream$) A_stream_stream_stream$)
(declare-fun snth$ (A_stream_stream_stream_stream$ Nat$) A_stream_stream_stream$)
(declare-fun smap$a (A_a_stream_stream_fun$ A_stream$) A_stream_stream_stream$)
(declare-fun smap$b (A_stream_stream_a_stream_fun$ A_stream_stream_stream$) A_stream_stream$)
(declare-fun smap$c (A_stream_stream_a_fun$ A_stream_stream_stream$) A_stream$)
(declare-fun smap$d (A_stream_stream_a_stream_stream_fun$ A_stream_stream_stream$) A_stream_stream_stream$)
(declare-fun smap$e (A_a_stream_fun$) A_stream_a_stream_stream_fun$)
(declare-fun smap$f (A_stream_a_fun$) A_stream_stream_a_stream_fun$)
(declare-fun smap$g (A_stream_a_stream_fun$) A_stream_stream_a_stream_stream_fun$)
(declare-fun smap$h (A_a_fun$) A_stream_a_stream_fun$)
(declare-fun smap$i (A_stream_stream_stream_a_fun$ A_stream_stream_stream_stream$) A_stream$)
(declare-fun snth$a (A_stream_stream_stream$ Nat$) A_stream_stream$)
(declare-fun snth$b (A_stream_stream$ Nat$) A_stream$)
(declare-fun snth$c (A_stream$ Nat$) A$)
(declare-fun member$ (A_stream$ A_stream_set$) Bool)
(declare-fun fun_app$ (A_a_stream_fun$ A$) A_stream$)
(declare-fun member$a (A$ A_set$) Bool)
(declare-fun member$b (A_stream_stream_stream_stream$ A_stream_stream_stream_stream_set$) Bool)
(declare-fun member$c (A_stream_stream_stream$ A_stream_stream_stream_set$) Bool)
(declare-fun member$d (A_stream_stream$ A_stream_stream_set$) Bool)
(declare-fun streams$ (A_set$) A_stream_set$)
(declare-fun fun_app$a (A_stream_a_stream_fun$ A_stream$) A_stream$)
(declare-fun fun_app$b (A_a_fun$ A$) A$)
(declare-fun fun_app$c (A_stream_a_stream_stream_fun$ A_stream$) A_stream_stream$)
(declare-fun fun_app$d (A_a_stream_stream_fun$ A$) A_stream_stream$)
(declare-fun fun_app$e (A_stream_stream_a_stream_fun$ A_stream_stream$) A_stream$)
(declare-fun fun_app$f (A_stream_stream_a_fun$ A_stream_stream$) A$)
(declare-fun fun_app$g (A_stream_stream_a_stream_stream_fun$ A_stream_stream$) A_stream_stream$)
(declare-fun fun_app$h (A_stream_a_fun$ A_stream$) A$)
(declare-fun fun_app$i (A_stream_stream_stream_a_fun$ A_stream_stream_stream$) A$)
(declare-fun siterate$ (A_a_fun$) A_a_stream_fun$)
(declare-fun streams$a (A_stream_stream_stream_set$) A_stream_stream_stream_stream_set$)
(declare-fun streams$b (A_stream_stream_set$) A_stream_stream_stream_set$)
(declare-fun streams$c (A_stream_set$) A_stream_stream_set$)
(declare-fun siterate$a (A_stream_a_stream_fun$) A_stream_a_stream_stream_fun$)
(declare-fun siterate$b (A_stream_stream_a_stream_stream_fun$ A_stream_stream$) A_stream_stream_stream$)
(assert (! (not (member$ (fun_app$ (siterate$ id$) x$) (streams$ a$))) :named a0))
(assert (! (member$a x$ a$) :named a1))
(assert (! (forall ((?v0 A_stream$)) (! (= (fun_app$a id$a ?v0) ?v0) :pattern ((fun_app$a id$a ?v0)))) :named a2))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$b id$ ?v0) ?v0) :pattern ((fun_app$b id$ ?v0)))) :named a3))
(assert (! (forall ((?v0 A_stream$)) (! (= (fun_app$a id$a ?v0) ?v0) :pattern ((fun_app$a id$a ?v0)))) :named a4))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$b id$ ?v0) ?v0) :pattern ((fun_app$b id$ ?v0)))) :named a5))
(assert (! (forall ((?v0 A_stream_a_stream_stream_fun$) (?v1 A_stream$)) (= (smap$ ?v0 (fun_app$c (siterate$a id$a) ?v1)) (siterate$b id$b (fun_app$c ?v0 ?v1)))) :named a6))
(assert (! (forall ((?v0 A_a_stream_stream_fun$) (?v1 A$)) (= (smap$a ?v0 (fun_app$ (siterate$ id$) ?v1)) (siterate$b id$b (fun_app$d ?v0 ?v1)))) :named a7))
(assert (! (forall ((?v0 A_stream_stream_a_stream_fun$) (?v1 A_stream_stream$)) (= (smap$b ?v0 (siterate$b id$b ?v1)) (fun_app$c (siterate$a id$a) (fun_app$e ?v0 ?v1)))) :named a8))
(assert (! (forall ((?v0 A_stream_stream_a_fun$) (?v1 A_stream_stream$)) (= (smap$c ?v0 (siterate$b id$b ?v1)) (fun_app$ (siterate$ id$) (fun_app$f ?v0 ?v1)))) :named a9))
(assert (! (forall ((?v0 A_stream_stream_a_stream_stream_fun$) (?v1 A_stream_stream$)) (= (smap$d ?v0 (siterate$b id$b ?v1)) (siterate$b id$b (fun_app$g ?v0 ?v1)))) :named a10))
(assert (! (forall ((?v0 A_a_stream_fun$) (?v1 A$)) (= (fun_app$c (smap$e ?v0) (fun_app$ (siterate$ id$) ?v1)) (fun_app$c (siterate$a id$a) (fun_app$ ?v0 ?v1)))) :named a11))
(assert (! (forall ((?v0 A_stream_a_fun$) (?v1 A_stream$)) (= (fun_app$e (smap$f ?v0) (fun_app$c (siterate$a id$a) ?v1)) (fun_app$ (siterate$ id$) (fun_app$h ?v0 ?v1)))) :named a12))
(assert (! (forall ((?v0 A_stream_a_stream_fun$) (?v1 A_stream$)) (= (fun_app$g (smap$g ?v0) (fun_app$c (siterate$a id$a) ?v1)) (fun_app$c (siterate$a id$a) (fun_app$a ?v0 ?v1)))) :named a13))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$)) (= (fun_app$a (smap$h ?v0) (fun_app$ (siterate$ id$) ?v1)) (fun_app$ (siterate$ id$) (fun_app$b ?v0 ?v1)))) :named a14))
(assert (! (forall ((?v0 A_stream_stream_stream_stream$) (?v1 A_stream_stream_stream_set$)) (= (member$b ?v0 (streams$a ?v1)) (forall ((?v2 Nat$)) (member$c (snth$ ?v0 ?v2) ?v1)))) :named a15))
(assert (! (forall ((?v0 A_stream_stream_stream$) (?v1 A_stream_stream_set$)) (= (member$c ?v0 (streams$b ?v1)) (forall ((?v2 Nat$)) (member$d (snth$a ?v0 ?v2) ?v1)))) :named a16))
(assert (! (forall ((?v0 A_stream_stream$) (?v1 A_stream_set$)) (= (member$d ?v0 (streams$c ?v1)) (forall ((?v2 Nat$)) (member$ (snth$b ?v0 ?v2) ?v1)))) :named a17))
(assert (! (forall ((?v0 A_stream$) (?v1 A_set$)) (= (member$ ?v0 (streams$ ?v1)) (forall ((?v2 Nat$)) (member$a (snth$c ?v0 ?v2) ?v1)))) :named a18))
(assert (! (forall ((?v0 A_stream_stream_stream_stream$) (?v1 A_stream_stream_stream_set$) (?v2 Nat$)) (=> (member$b ?v0 (streams$a ?v1)) (member$c (snth$ ?v0 ?v2) ?v1))) :named a19))
(assert (! (forall ((?v0 A_stream_stream_stream$) (?v1 A_stream_stream_set$) (?v2 Nat$)) (=> (member$c ?v0 (streams$b ?v1)) (member$d (snth$a ?v0 ?v2) ?v1))) :named a20))
(assert (! (forall ((?v0 A_stream_stream$) (?v1 A_stream_set$) (?v2 Nat$)) (=> (member$d ?v0 (streams$c ?v1)) (member$ (snth$b ?v0 ?v2) ?v1))) :named a21))
(assert (! (forall ((?v0 A_stream$) (?v1 A_set$) (?v2 Nat$)) (=> (member$ ?v0 (streams$ ?v1)) (member$a (snth$c ?v0 ?v2) ?v1))) :named a22))
(assert (! (forall ((?v0 A_stream_stream_a_stream_stream_fun$) (?v1 A_stream_stream$)) (= (shd$b (siterate$b ?v0 ?v1)) ?v1)) :named a23))
(assert (! (forall ((?v0 A_stream_a_stream_fun$) (?v1 A_stream$)) (= (shd$a (fun_app$c (siterate$a ?v0) ?v1)) ?v1)) :named a24))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$)) (= (shd$ (fun_app$ (siterate$ ?v0) ?v1)) ?v1)) :named a25))
(assert (! (forall ((?v0 A_stream_stream_a_stream_stream_fun$) (?v1 A_stream_stream$)) (= (smap$d ?v0 (siterate$b ?v0 ?v1)) (siterate$b ?v0 (fun_app$g ?v0 ?v1)))) :named a26))
(assert (! (forall ((?v0 A_stream_a_stream_fun$) (?v1 A_stream$)) (= (fun_app$g (smap$g ?v0) (fun_app$c (siterate$a ?v0) ?v1)) (fun_app$c (siterate$a ?v0) (fun_app$a ?v0 ?v1)))) :named a27))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$)) (= (fun_app$a (smap$h ?v0) (fun_app$ (siterate$ ?v0) ?v1)) (fun_app$ (siterate$ ?v0) (fun_app$b ?v0 ?v1)))) :named a28))
(assert (! (forall ((?v0 A_stream_a_stream_fun$) (?v1 A_stream$)) (= (stl$a (fun_app$c (siterate$a ?v0) ?v1)) (fun_app$c (siterate$a ?v0) (fun_app$a ?v0 ?v1)))) :named a29))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$)) (= (stl$ (fun_app$ (siterate$ ?v0) ?v1)) (fun_app$ (siterate$ ?v0) (fun_app$b ?v0 ?v1)))) :named a30))
(assert (! (forall ((?v0 A_stream_a_stream_fun$) (?v1 A_stream$)) (= (fun_app$c (siterate$a ?v0) ?v1) (sCons$a ?v1 (fun_app$c (siterate$a ?v0) (fun_app$a ?v0 ?v1))))) :named a31))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$)) (= (fun_app$ (siterate$ ?v0) ?v1) (sCons$ ?v1 (fun_app$ (siterate$ ?v0) (fun_app$b ?v0 ?v1))))) :named a32))
(assert (! (forall ((?v0 A_stream_stream_stream_stream$) (?v1 A_stream_stream_stream_set$)) (=> (member$b ?v0 (streams$a ?v1)) (member$c (shd$c ?v0) ?v1))) :named a33))
(assert (! (forall ((?v0 A_stream_stream_stream$) (?v1 A_stream_stream_set$)) (=> (member$c ?v0 (streams$b ?v1)) (member$d (shd$b ?v0) ?v1))) :named a34))
(assert (! (forall ((?v0 A_stream_stream$) (?v1 A_stream_set$)) (=> (member$d ?v0 (streams$c ?v1)) (member$ (shd$a ?v0) ?v1))) :named a35))
(assert (! (forall ((?v0 A_stream$) (?v1 A_set$)) (=> (member$ ?v0 (streams$ ?v1)) (member$a (shd$ ?v0) ?v1))) :named a36))
(assert (! (forall ((?v0 A_stream$) (?v1 A_set$) (?v2 A_a_fun$) (?v3 A_set$)) (=> (and (member$ ?v0 (streams$ ?v1)) (forall ((?v4 A$)) (=> (member$a ?v4 ?v1) (member$a (fun_app$b ?v2 ?v4) ?v3)))) (member$ (fun_app$a (smap$h ?v2) ?v0) (streams$ ?v3)))) :named a37))
(assert (! (forall ((?v0 A_stream_stream$) (?v1 A_stream_set$) (?v2 A_stream_a_fun$) (?v3 A_set$)) (=> (and (member$d ?v0 (streams$c ?v1)) (forall ((?v4 A_stream$)) (=> (member$ ?v4 ?v1) (member$a (fun_app$h ?v2 ?v4) ?v3)))) (member$ (fun_app$e (smap$f ?v2) ?v0) (streams$ ?v3)))) :named a38))
(assert (! (forall ((?v0 A_stream$) (?v1 A_set$) (?v2 A_a_stream_fun$) (?v3 A_stream_set$)) (=> (and (member$ ?v0 (streams$ ?v1)) (forall ((?v4 A$)) (=> (member$a ?v4 ?v1) (member$ (fun_app$ ?v2 ?v4) ?v3)))) (member$d (fun_app$c (smap$e ?v2) ?v0) (streams$c ?v3)))) :named a39))
(assert (! (forall ((?v0 A_stream_stream$) (?v1 A_stream_set$) (?v2 A_stream_a_stream_fun$) (?v3 A_stream_set$)) (=> (and (member$d ?v0 (streams$c ?v1)) (forall ((?v4 A_stream$)) (=> (member$ ?v4 ?v1) (member$ (fun_app$a ?v2 ?v4) ?v3)))) (member$d (fun_app$g (smap$g ?v2) ?v0) (streams$c ?v3)))) :named a40))
(assert (! (forall ((?v0 A_stream_stream_stream$) (?v1 A_stream_stream_set$) (?v2 A_stream_stream_a_fun$) (?v3 A_set$)) (=> (and (member$c ?v0 (streams$b ?v1)) (forall ((?v4 A_stream_stream$)) (=> (member$d ?v4 ?v1) (member$a (fun_app$f ?v2 ?v4) ?v3)))) (member$ (smap$c ?v2 ?v0) (streams$ ?v3)))) :named a41))
(assert (! (forall ((?v0 A_stream$) (?v1 A_set$) (?v2 A_a_stream_stream_fun$) (?v3 A_stream_stream_set$)) (=> (and (member$ ?v0 (streams$ ?v1)) (forall ((?v4 A$)) (=> (member$a ?v4 ?v1) (member$d (fun_app$d ?v2 ?v4) ?v3)))) (member$c (smap$a ?v2 ?v0) (streams$b ?v3)))) :named a42))
(assert (! (forall ((?v0 A_stream_stream_stream$) (?v1 A_stream_stream_set$) (?v2 A_stream_stream_a_stream_fun$) (?v3 A_stream_set$)) (=> (and (member$c ?v0 (streams$b ?v1)) (forall ((?v4 A_stream_stream$)) (=> (member$d ?v4 ?v1) (member$ (fun_app$e ?v2 ?v4) ?v3)))) (member$d (smap$b ?v2 ?v0) (streams$c ?v3)))) :named a43))
(assert (! (forall ((?v0 A_stream_stream$) (?v1 A_stream_set$) (?v2 A_stream_a_stream_stream_fun$) (?v3 A_stream_stream_set$)) (=> (and (member$d ?v0 (streams$c ?v1)) (forall ((?v4 A_stream$)) (=> (member$ ?v4 ?v1) (member$d (fun_app$c ?v2 ?v4) ?v3)))) (member$c (smap$ ?v2 ?v0) (streams$b ?v3)))) :named a44))
(assert (! (forall ((?v0 A_stream_stream_stream$) (?v1 A_stream_stream_set$) (?v2 A_stream_stream_a_stream_stream_fun$) (?v3 A_stream_stream_set$)) (=> (and (member$c ?v0 (streams$b ?v1)) (forall ((?v4 A_stream_stream$)) (=> (member$d ?v4 ?v1) (member$d (fun_app$g ?v2 ?v4) ?v3)))) (member$c (smap$d ?v2 ?v0) (streams$b ?v3)))) :named a45))
(assert (! (forall ((?v0 A_stream_stream_stream_stream$) (?v1 A_stream_stream_stream_set$) (?v2 A_stream_stream_stream_a_fun$) (?v3 A_set$)) (=> (and (member$b ?v0 (streams$a ?v1)) (forall ((?v4 A_stream_stream_stream$)) (=> (member$c ?v4 ?v1) (member$a (fun_app$i ?v2 ?v4) ?v3)))) (member$ (smap$i ?v2 ?v0) (streams$ ?v3)))) :named a46))
(assert (! (forall ((?v0 A_stream_stream_stream$) (?v1 A_stream_stream_set$)) (=> (member$c ?v0 (streams$b ?v1)) (member$c (stl$b ?v0) (streams$b ?v1)))) :named a47))
(assert (! (forall ((?v0 A_stream_stream$) (?v1 A_stream_set$)) (=> (member$d ?v0 (streams$c ?v1)) (member$d (stl$a ?v0) (streams$c ?v1)))) :named a48))
(assert (! (forall ((?v0 A_stream$) (?v1 A_set$)) (=> (member$ ?v0 (streams$ ?v1)) (member$ (stl$ ?v0) (streams$ ?v1)))) :named a49))
(assert (! (forall ((?v0 A_stream$) (?v1 A_stream_stream$) (?v2 A_stream$) (?v3 A_stream_stream$)) (= (= (sCons$a ?v0 ?v1) (sCons$a ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a50))
(assert (! (forall ((?v0 A$) (?v1 A_stream$) (?v2 A$) (?v3 A_stream$)) (= (= (sCons$ ?v0 ?v1) (sCons$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a51))
(assert (! (forall ((?v0 A_stream_a_stream_stream_fun$) (?v1 A_stream_stream$)) (= (stl$b (smap$ ?v0 ?v1)) (smap$ ?v0 (stl$a ?v1)))) :named a52))
(assert (! (forall ((?v0 A_a_stream_stream_fun$) (?v1 A_stream$)) (= (stl$b (smap$a ?v0 ?v1)) (smap$a ?v0 (stl$ ?v1)))) :named a53))
(assert (! (forall ((?v0 A_stream_stream_a_stream_fun$) (?v1 A_stream_stream_stream$)) (= (stl$a (smap$b ?v0 ?v1)) (smap$b ?v0 (stl$b ?v1)))) :named a54))
(assert (! (forall ((?v0 A_stream_stream_a_fun$) (?v1 A_stream_stream_stream$)) (= (stl$ (smap$c ?v0 ?v1)) (smap$c ?v0 (stl$b ?v1)))) :named a55))
(assert (! (forall ((?v0 A_stream_stream_a_stream_stream_fun$) (?v1 A_stream_stream_stream$)) (= (stl$b (smap$d ?v0 ?v1)) (smap$d ?v0 (stl$b ?v1)))) :named a56))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_stream$)) (= (stl$ (fun_app$a (smap$h ?v0) ?v1)) (fun_app$a (smap$h ?v0) (stl$ ?v1)))) :named a57))
(assert (! (forall ((?v0 A_a_stream_fun$) (?v1 A_stream$)) (= (stl$a (fun_app$c (smap$e ?v0) ?v1)) (fun_app$c (smap$e ?v0) (stl$ ?v1)))) :named a58))
(assert (! (forall ((?v0 A_stream_a_fun$) (?v1 A_stream_stream$)) (= (stl$ (fun_app$e (smap$f ?v0) ?v1)) (fun_app$e (smap$f ?v0) (stl$a ?v1)))) :named a59))
(assert (! (forall ((?v0 A_stream_a_stream_fun$) (?v1 A_stream_stream$)) (= (stl$a (fun_app$g (smap$g ?v0) ?v1)) (fun_app$g (smap$g ?v0) (stl$a ?v1)))) :named a60))
(assert (! (forall ((?v0 A_stream_a_stream_stream_fun$) (?v1 A_stream_stream$)) (= (shd$b (smap$ ?v0 ?v1)) (fun_app$c ?v0 (shd$a ?v1)))) :named a61))
(assert (! (forall ((?v0 A_a_stream_stream_fun$) (?v1 A_stream$)) (= (shd$b (smap$a ?v0 ?v1)) (fun_app$d ?v0 (shd$ ?v1)))) :named a62))
(assert (! (forall ((?v0 A_stream_stream_a_stream_fun$) (?v1 A_stream_stream_stream$)) (= (shd$a (smap$b ?v0 ?v1)) (fun_app$e ?v0 (shd$b ?v1)))) :named a63))
(assert (! (forall ((?v0 A_stream_stream_a_fun$) (?v1 A_stream_stream_stream$)) (= (shd$ (smap$c ?v0 ?v1)) (fun_app$f ?v0 (shd$b ?v1)))) :named a64))
(assert (! (forall ((?v0 A_stream_stream_a_stream_stream_fun$) (?v1 A_stream_stream_stream$)) (= (shd$b (smap$d ?v0 ?v1)) (fun_app$g ?v0 (shd$b ?v1)))) :named a65))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_stream$)) (= (shd$ (fun_app$a (smap$h ?v0) ?v1)) (fun_app$b ?v0 (shd$ ?v1)))) :named a66))
(assert (! (forall ((?v0 A_a_stream_fun$) (?v1 A_stream$)) (= (shd$a (fun_app$c (smap$e ?v0) ?v1)) (fun_app$ ?v0 (shd$ ?v1)))) :named a67))
(assert (! (forall ((?v0 A_stream_a_fun$) (?v1 A_stream_stream$)) (= (shd$ (fun_app$e (smap$f ?v0) ?v1)) (fun_app$h ?v0 (shd$a ?v1)))) :named a68))
(assert (! (forall ((?v0 A_stream_a_stream_fun$) (?v1 A_stream_stream$)) (= (shd$a (fun_app$g (smap$g ?v0) ?v1)) (fun_app$a ?v0 (shd$a ?v1)))) :named a69))
(assert (! (forall ((?v0 A_stream_a_stream_stream_fun$) (?v1 A_stream_stream$) (?v2 Nat$)) (= (snth$a (smap$ ?v0 ?v1) ?v2) (fun_app$c ?v0 (snth$b ?v1 ?v2)))) :named a70))
(assert (! (forall ((?v0 A_a_stream_stream_fun$) (?v1 A_stream$) (?v2 Nat$)) (= (snth$a (smap$a ?v0 ?v1) ?v2) (fun_app$d ?v0 (snth$c ?v1 ?v2)))) :named a71))
(assert (! (forall ((?v0 A_stream_stream_a_stream_fun$) (?v1 A_stream_stream_stream$) (?v2 Nat$)) (= (snth$b (smap$b ?v0 ?v1) ?v2) (fun_app$e ?v0 (snth$a ?v1 ?v2)))) :named a72))
(assert (! (forall ((?v0 A_stream_stream_a_fun$) (?v1 A_stream_stream_stream$) (?v2 Nat$)) (= (snth$c (smap$c ?v0 ?v1) ?v2) (fun_app$f ?v0 (snth$a ?v1 ?v2)))) :named a73))
(assert (! (forall ((?v0 A_stream_stream_a_stream_stream_fun$) (?v1 A_stream_stream_stream$) (?v2 Nat$)) (= (snth$a (smap$d ?v0 ?v1) ?v2) (fun_app$g ?v0 (snth$a ?v1 ?v2)))) :named a74))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_stream$) (?v2 Nat$)) (= (snth$c (fun_app$a (smap$h ?v0) ?v1) ?v2) (fun_app$b ?v0 (snth$c ?v1 ?v2)))) :named a75))
(assert (! (forall ((?v0 A_a_stream_fun$) (?v1 A_stream$) (?v2 Nat$)) (= (snth$b (fun_app$c (smap$e ?v0) ?v1) ?v2) (fun_app$ ?v0 (snth$c ?v1 ?v2)))) :named a76))
(assert (! (forall ((?v0 A_stream_a_fun$) (?v1 A_stream_stream$) (?v2 Nat$)) (= (snth$c (fun_app$e (smap$f ?v0) ?v1) ?v2) (fun_app$h ?v0 (snth$b ?v1 ?v2)))) :named a77))
(assert (! (forall ((?v0 A_stream_a_stream_fun$) (?v1 A_stream_stream$) (?v2 Nat$)) (= (snth$b (fun_app$g (smap$g ?v0) ?v1) ?v2) (fun_app$a ?v0 (snth$b ?v1 ?v2)))) :named a78))
(assert (! (forall ((?v0 A_stream_stream_stream$)) (= (sCons$b (shd$b ?v0) (stl$b ?v0)) ?v0)) :named a79))
(assert (! (forall ((?v0 A_stream_stream$)) (= (sCons$a (shd$a ?v0) (stl$a ?v0)) ?v0)) :named a80))
(assert (! (forall ((?v0 A_stream$)) (= (sCons$ (shd$ ?v0) (stl$ ?v0)) ?v0)) :named a81))
(check-sat)
;(get-unsat-core)
