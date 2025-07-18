; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 135
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort N$ 0)
(declare-sort T$ 0)
(declare-sort Dtree$ 0)
(declare-sort N_set$ 0)
(declare-sort T_set$ 0)
(declare-sort N_N_fun$ 0)
(declare-sort N_T_fun$ 0)
(declare-sort T_N_fun$ 0)
(declare-sort T_T_fun$ 0)
(declare-sort T_set_set$ 0)
(declare-sort Dtree_N_fun$ 0)
(declare-sort N_dtree_fun$ 0)
(declare-sort T_N_sum_set$ 0)
(declare-sort N_T_N_sum_fun$ 0)
(declare-sort T_N_sum_N_fun$ 0)
(declare-sort T_T_N_sum_fun$ 0)
(declare-sort Dtree_dtree_fun$ 0)
(declare-sort N_set_N_set_fun$ 0)
(declare-sort T_dtree_sum_set$ 0)
(declare-sort T_set_T_set_fun$ 0)
(declare-sort N_T_dtree_sum_fun$ 0)
(declare-sort T_T_dtree_sum_fun$ 0)
(declare-sort T_dtree_sum_N_fun$ 0)
(declare-sort T_dtree_sum_T_fun$ 0)
(declare-sort T_N_sum_T_N_sum_fun$ 0)
(declare-sort N_set_set_N_set_set_fun$ 0)
(declare-sort T_N_sum_T_dtree_sum_fun$ 0)
(declare-sort T_dtree_sum_T_N_sum_fun$ 0)
(declare-sort T_set_set_T_set_set_fun$ 0)
(declare-sort T_N_sum_set_T_N_sum_set_fun$ 0)
(declare-sort T_dtree_sum_T_dtree_sum_fun$ 0)
(declare-sort T_set_set_set_T_set_set_set_fun$ 0)
(declare-sort T_N_sum_set_set_T_N_sum_set_set_fun$ 0)
(declare-sort T_dtree_sum_set_T_dtree_sum_set_fun$ 0)
(declare-sort Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$ 0)
(declare-sort N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$ 0)
(declare-sort T_dtree_sum_set_set_T_dtree_sum_set_set_fun$ 0)
(declare-datatypes () ((T_N_sum$ (inl$ (projl$ T$)) (inr$ (projr$ N$)))
  (T_dtree_sum$ (inl$a (projl$a T$)) (inr$a (projr$a Dtree$)))))
(declare-fun n$ () N$)
(declare-fun id$ () T_T_fun$)
(declare-fun ns$ () N_set$)
(declare-fun tr$ () Dtree$)
(declare-fun uu$ () T_T_N_sum_fun$)
(declare-fun ftr$ () N_dtree_fun$)
(declare-fun id$a () T_dtree_sum_T_dtree_sum_fun$)
(declare-fun id$b () T_dtree_sum_set_T_dtree_sum_set_fun$)
(declare-fun id$c () T_N_sum_T_N_sum_fun$)
(declare-fun id$d () T_N_sum_set_T_N_sum_set_fun$)
(declare-fun id$e () T_dtree_sum_set_set_T_dtree_sum_set_set_fun$)
(declare-fun id$f () T_N_sum_set_set_T_N_sum_set_set_fun$)
(declare-fun id$g () T_set_set_T_set_set_fun$)
(declare-fun id$h () T_set_set_set_T_set_set_set_fun$)
(declare-fun id$i () N_set_N_set_fun$)
(declare-fun id$j () N_set_set_N_set_set_fun$)
(declare-fun id$k () T_set_T_set_fun$)
(declare-fun id$l () N_N_fun$)
(declare-fun tns$ () T_N_sum_set$)
(declare-fun tr$a () Dtree$)
(declare-fun uua$ () T_T_dtree_sum_fun$)
(declare-fun cont$ (Dtree$) T_dtree_sum_set$)
(declare-fun node$ (N$ T_dtree_sum_set$) Dtree$)
(declare-fun root$ () Dtree_N_fun$)
(declare-fun image$ (T_dtree_sum_T_N_sum_fun$ T_dtree_sum_set$) T_N_sum_set$)
(declare-fun hsubst$ (Dtree$) Dtree_dtree_fun$)
(declare-fun image$a (T_N_sum_T_dtree_sum_fun$ T_N_sum_set$) T_dtree_sum_set$)
(declare-fun image$b (T_N_sum_T_N_sum_fun$) T_N_sum_set_T_N_sum_set_fun$)
(declare-fun image$c (T_dtree_sum_T_dtree_sum_fun$) T_dtree_sum_set_T_dtree_sum_set_fun$)
(declare-fun image$d (T_dtree_sum_set_T_dtree_sum_set_fun$) T_dtree_sum_set_set_T_dtree_sum_set_set_fun$)
(declare-fun image$e (T_N_sum_set_T_N_sum_set_fun$) T_N_sum_set_set_T_N_sum_set_set_fun$)
(declare-fun image$f (T_set_set_T_set_set_fun$) T_set_set_set_T_set_set_set_fun$)
(declare-fun image$g (N_set_N_set_fun$) N_set_set_N_set_set_fun$)
(declare-fun image$h (T_set_T_set_fun$) T_set_set_T_set_set_fun$)
(declare-fun image$i (N_N_fun$) N_set_N_set_fun$)
(declare-fun image$j (T_T_fun$) T_set_T_set_fun$)
(declare-fun image$k (N_T_fun$ N_set$) T_set$)
(declare-fun image$l (T_N_fun$ T_set$) N_set$)
(declare-fun image$m (N_T_dtree_sum_fun$ N_set$) T_dtree_sum_set$)
(declare-fun image$n (N_T_N_sum_fun$ N_set$) T_N_sum_set$)
(declare-fun image$o (T_dtree_sum_N_fun$ T_dtree_sum_set$) N_set$)
(declare-fun image$p (T_dtree_sum_T_fun$ T_dtree_sum_set$) T_set$)
(declare-fun member$ (T_N_sum$ T_N_sum_set$) Bool)
(declare-fun vimage$ (T_T_N_sum_fun$ T_N_sum_set$) T_set$)
(declare-fun fun_app$ (T_T_dtree_sum_fun$ T$) T_dtree_sum$)
(declare-fun map_sum$ (T_T_fun$) Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$)
(declare-fun member$a (T_dtree_sum$ T_dtree_sum_set$) Bool)
(declare-fun member$b (N$ N_set$) Bool)
(declare-fun member$c (T$ T_set$) Bool)
(declare-fun vimage$a (T_T_dtree_sum_fun$ T_dtree_sum_set$) T_set$)
(declare-fun vimage$b (T_dtree_sum_T_dtree_sum_fun$) T_dtree_sum_set_T_dtree_sum_set_fun$)
(declare-fun vimage$c (T_N_sum_T_N_sum_fun$) T_N_sum_set_T_N_sum_set_fun$)
(declare-fun vimage$d (T_dtree_sum_set_T_dtree_sum_set_fun$) T_dtree_sum_set_set_T_dtree_sum_set_set_fun$)
(declare-fun vimage$e (T_N_sum_set_T_N_sum_set_fun$) T_N_sum_set_set_T_N_sum_set_set_fun$)
(declare-fun vimage$f (T_set_set_T_set_set_fun$) T_set_set_set_T_set_set_set_fun$)
(declare-fun vimage$g (N_set_N_set_fun$) N_set_set_N_set_set_fun$)
(declare-fun vimage$h (T_set_T_set_fun$) T_set_set_T_set_set_fun$)
(declare-fun vimage$i (N_N_fun$) N_set_N_set_fun$)
(declare-fun vimage$j (T_T_fun$) T_set_T_set_fun$)
(declare-fun vimage$k (N_T_fun$ T_set$) N_set$)
(declare-fun vimage$l (T_N_fun$ N_set$) T_set$)
(declare-fun vimage$m (N_T_dtree_sum_fun$ T_dtree_sum_set$) N_set$)
(declare-fun vimage$n (N_T_N_sum_fun$ T_N_sum_set$) N_set$)
(declare-fun vimage$o (T_dtree_sum_N_fun$ N_set$) T_dtree_sum_set$)
(declare-fun vimage$p (T_dtree_sum_T_fun$ T_set$) T_dtree_sum_set$)
(declare-fun vimage$q (T_N_sum_N_fun$ N_set$) T_N_sum_set$)
(declare-fun fun_app$a (T_T_N_sum_fun$ T$) T_N_sum$)
(declare-fun fun_app$b (Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$ Dtree_N_fun$) T_dtree_sum_T_N_sum_fun$)
(declare-fun fun_app$c (N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$ N_dtree_fun$) T_N_sum_T_dtree_sum_fun$)
(declare-fun fun_app$d (T_N_sum_set_T_N_sum_set_fun$ T_N_sum_set$) T_N_sum_set$)
(declare-fun fun_app$e (T_dtree_sum_set_T_dtree_sum_set_fun$ T_dtree_sum_set$) T_dtree_sum_set$)
(declare-fun fun_app$f (N_set_N_set_fun$ N_set$) N_set$)
(declare-fun fun_app$g (N_N_fun$ N$) N$)
(declare-fun fun_app$h (N_T_fun$ N$) T$)
(declare-fun fun_app$i (T_N_fun$ T$) N$)
(declare-fun fun_app$j (T_set_T_set_fun$ T_set$) T_set$)
(declare-fun fun_app$k (T_T_fun$ T$) T$)
(declare-fun fun_app$l (N_T_dtree_sum_fun$ N$) T_dtree_sum$)
(declare-fun fun_app$m (N_T_N_sum_fun$ N$) T_N_sum$)
(declare-fun fun_app$n (T_dtree_sum_N_fun$ T_dtree_sum$) N$)
(declare-fun fun_app$o (T_dtree_sum_T_fun$ T_dtree_sum$) T$)
(declare-fun fun_app$p (T_N_sum_N_fun$ T_N_sum$) N$)
(declare-fun fun_app$q (T_set_set_T_set_set_fun$ T_set_set$) T_set_set$)
(declare-fun fun_app$r (T_dtree_sum_T_N_sum_fun$ T_dtree_sum$) T_N_sum$)
(declare-fun fun_app$s (T_N_sum_T_dtree_sum_fun$ T_N_sum$) T_dtree_sum$)
(declare-fun fun_app$t (Dtree_N_fun$ Dtree$) N$)
(declare-fun fun_app$u (Dtree_dtree_fun$ Dtree$) Dtree$)
(declare-fun map_sum$a (T_T_fun$) N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$)
(declare-fun map_sum$b (T_T_fun$ N_N_fun$) T_N_sum_T_N_sum_fun$)
(declare-fun map_sum$c (T_T_fun$ Dtree_dtree_fun$) T_dtree_sum_T_dtree_sum_fun$)
(assert (! (forall ((?v0 T$)) (! (= (fun_app$ uua$ ?v0) (inl$a ?v0)) :pattern ((fun_app$ uua$ ?v0)))) :named a0))
(assert (! (forall ((?v0 T$)) (! (= (fun_app$a uu$ ?v0) (inl$ ?v0)) :pattern ((fun_app$a uu$ ?v0)))) :named a1))
(assert (! (not (= (vimage$ uu$ (image$ (fun_app$b (map_sum$ id$) root$) (image$a (fun_app$c (map_sum$a id$) ftr$) tns$))) (vimage$ uu$ tns$))) :named a2))
(assert (! (forall ((?v0 N_N_fun$) (?v1 T_N_sum_set$)) (= (vimage$ uu$ (fun_app$d (image$b (map_sum$b id$ ?v0)) ?v1)) (vimage$ uu$ ?v1))) :named a3))
(assert (! (forall ((?v0 Dtree_dtree_fun$) (?v1 T_dtree_sum_set$)) (= (vimage$a uua$ (fun_app$e (image$c (map_sum$c id$ ?v0)) ?v1)) (vimage$a uua$ ?v1))) :named a4))
(assert (! (forall ((?v0 Dtree_N_fun$) (?v1 T_dtree_sum_set$)) (= (vimage$ uu$ (image$ (fun_app$b (map_sum$ id$) ?v0) ?v1)) (vimage$a uua$ ?v1))) :named a5))
(assert (! (forall ((?v0 N_dtree_fun$) (?v1 T_N_sum_set$)) (= (vimage$a uua$ (image$a (fun_app$c (map_sum$a id$) ?v0) ?v1)) (vimage$ uu$ ?v1))) :named a6))
(assert (! (forall ((?v0 T$) (?v1 N_N_fun$) (?v2 T_N_sum_set$)) (= (member$ (inl$ ?v0) (fun_app$d (image$b (map_sum$b id$ ?v1)) ?v2)) (member$ (inl$ ?v0) ?v2))) :named a7))
(assert (! (forall ((?v0 T$) (?v1 Dtree_dtree_fun$) (?v2 T_dtree_sum_set$)) (= (member$a (inl$a ?v0) (fun_app$e (image$c (map_sum$c id$ ?v1)) ?v2)) (member$a (inl$a ?v0) ?v2))) :named a8))
(assert (! (forall ((?v0 T$) (?v1 Dtree_N_fun$) (?v2 T_dtree_sum_set$)) (= (member$ (inl$ ?v0) (image$ (fun_app$b (map_sum$ id$) ?v1) ?v2)) (member$a (inl$a ?v0) ?v2))) :named a9))
(assert (! (forall ((?v0 T$) (?v1 N_dtree_fun$) (?v2 T_N_sum_set$)) (= (member$a (inl$a ?v0) (image$a (fun_app$c (map_sum$a id$) ?v1) ?v2)) (member$ (inl$ ?v0) ?v2))) :named a10))
(assert (! (= (vimage$b id$a) id$b) :named a11))
(assert (! (= (vimage$c id$c) id$d) :named a12))
(assert (! (= (vimage$d id$b) id$e) :named a13))
(assert (! (= (vimage$e id$d) id$f) :named a14))
(assert (! (= (vimage$f id$g) id$h) :named a15))
(assert (! (= (vimage$g id$i) id$j) :named a16))
(assert (! (= (vimage$h id$k) id$g) :named a17))
(assert (! (= (vimage$i id$l) id$i) :named a18))
(assert (! (= (vimage$j id$) id$k) :named a19))
(assert (! (= (image$d id$b) id$e) :named a20))
(assert (! (= (image$e id$d) id$f) :named a21))
(assert (! (= (image$f id$g) id$h) :named a22))
(assert (! (= (image$g id$i) id$j) :named a23))
(assert (! (= (image$h id$k) id$g) :named a24))
(assert (! (= (image$c id$a) id$b) :named a25))
(assert (! (= (image$b id$c) id$d) :named a26))
(assert (! (= (image$i id$l) id$i) :named a27))
(assert (! (= (image$j id$) id$k) :named a28))
(assert (! (forall ((?v0 T$) (?v1 N_N_fun$) (?v2 T_N_sum_set$)) (=> (member$ (inl$ ?v0) (fun_app$d (image$b (map_sum$b id$ ?v1)) ?v2)) (member$ (inl$ ?v0) ?v2))) :named a29))
(assert (! (forall ((?v0 T$) (?v1 Dtree_dtree_fun$) (?v2 T_dtree_sum_set$)) (=> (member$a (inl$a ?v0) (fun_app$e (image$c (map_sum$c id$ ?v1)) ?v2)) (member$a (inl$a ?v0) ?v2))) :named a30))
(assert (! (forall ((?v0 T$) (?v1 Dtree_N_fun$) (?v2 T_dtree_sum_set$)) (=> (member$ (inl$ ?v0) (image$ (fun_app$b (map_sum$ id$) ?v1) ?v2)) (member$a (inl$a ?v0) ?v2))) :named a31))
(assert (! (forall ((?v0 T$) (?v1 N_dtree_fun$) (?v2 T_N_sum_set$)) (=> (member$a (inl$a ?v0) (image$a (fun_app$c (map_sum$a id$) ?v1) ?v2)) (member$ (inl$ ?v0) ?v2))) :named a32))
(assert (! (= tr$ (node$ n$ (image$a (fun_app$c (map_sum$a id$) ftr$) tns$))) :named a33))
(assert (! (forall ((?v0 T$) (?v1 T$)) (= (= (inl$ ?v0) (inl$ ?v1)) (= ?v0 ?v1))) :named a34))
(assert (! (forall ((?v0 T$) (?v1 T$)) (= (= (inl$a ?v0) (inl$a ?v1)) (= ?v0 ?v1))) :named a35))
(assert (! (forall ((?v0 T$) (?v1 T$)) (= (= (inl$ ?v0) (inl$ ?v1)) (= ?v0 ?v1))) :named a36))
(assert (! (forall ((?v0 T$) (?v1 T$)) (= (= (inl$a ?v0) (inl$a ?v1)) (= ?v0 ?v1))) :named a37))
(assert (! (forall ((?v0 N$) (?v1 N_N_fun$) (?v2 N_set$)) (= (member$b ?v0 (fun_app$f (vimage$i ?v1) ?v2)) (member$b (fun_app$g ?v1 ?v0) ?v2))) :named a38))
(assert (! (forall ((?v0 T$) (?v1 T_T_N_sum_fun$) (?v2 T_N_sum_set$)) (= (member$c ?v0 (vimage$ ?v1 ?v2)) (member$ (fun_app$a ?v1 ?v0) ?v2))) :named a39))
(assert (! (forall ((?v0 T$) (?v1 T_T_dtree_sum_fun$) (?v2 T_dtree_sum_set$)) (= (member$c ?v0 (vimage$a ?v1 ?v2)) (member$a (fun_app$ ?v1 ?v0) ?v2))) :named a40))
(assert (! (forall ((?v0 N$) (?v1 N_T_fun$) (?v2 T_set$)) (= (member$b ?v0 (vimage$k ?v1 ?v2)) (member$c (fun_app$h ?v1 ?v0) ?v2))) :named a41))
(assert (! (forall ((?v0 T$) (?v1 T_N_fun$) (?v2 N_set$)) (= (member$c ?v0 (vimage$l ?v1 ?v2)) (member$b (fun_app$i ?v1 ?v0) ?v2))) :named a42))
(assert (! (forall ((?v0 T$) (?v1 T_T_fun$) (?v2 T_set$)) (= (member$c ?v0 (fun_app$j (vimage$j ?v1) ?v2)) (member$c (fun_app$k ?v1 ?v0) ?v2))) :named a43))
(assert (! (forall ((?v0 N$) (?v1 N_T_dtree_sum_fun$) (?v2 T_dtree_sum_set$)) (= (member$b ?v0 (vimage$m ?v1 ?v2)) (member$a (fun_app$l ?v1 ?v0) ?v2))) :named a44))
(assert (! (forall ((?v0 N$) (?v1 N_T_N_sum_fun$) (?v2 T_N_sum_set$)) (= (member$b ?v0 (vimage$n ?v1 ?v2)) (member$ (fun_app$m ?v1 ?v0) ?v2))) :named a45))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_N_fun$) (?v2 N_set$)) (= (member$a ?v0 (vimage$o ?v1 ?v2)) (member$b (fun_app$n ?v1 ?v0) ?v2))) :named a46))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_T_fun$) (?v2 T_set$)) (= (member$a ?v0 (vimage$p ?v1 ?v2)) (member$c (fun_app$o ?v1 ?v0) ?v2))) :named a47))
(assert (! (forall ((?v0 N_N_fun$) (?v1 N$) (?v2 N$) (?v3 N_set$)) (=> (and (= (fun_app$g ?v0 ?v1) ?v2) (member$b ?v2 ?v3)) (member$b ?v1 (fun_app$f (vimage$i ?v0) ?v3)))) :named a48))
(assert (! (forall ((?v0 T_T_N_sum_fun$) (?v1 T$) (?v2 T_N_sum$) (?v3 T_N_sum_set$)) (=> (and (= (fun_app$a ?v0 ?v1) ?v2) (member$ ?v2 ?v3)) (member$c ?v1 (vimage$ ?v0 ?v3)))) :named a49))
(assert (! (forall ((?v0 T_T_dtree_sum_fun$) (?v1 T$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= (fun_app$ ?v0 ?v1) ?v2) (member$a ?v2 ?v3)) (member$c ?v1 (vimage$a ?v0 ?v3)))) :named a50))
(assert (! (forall ((?v0 T_N_fun$) (?v1 T$) (?v2 N$) (?v3 N_set$)) (=> (and (= (fun_app$i ?v0 ?v1) ?v2) (member$b ?v2 ?v3)) (member$c ?v1 (vimage$l ?v0 ?v3)))) :named a51))
(assert (! (forall ((?v0 N_T_fun$) (?v1 N$) (?v2 T$) (?v3 T_set$)) (=> (and (= (fun_app$h ?v0 ?v1) ?v2) (member$c ?v2 ?v3)) (member$b ?v1 (vimage$k ?v0 ?v3)))) :named a52))
(assert (! (forall ((?v0 T_T_fun$) (?v1 T$) (?v2 T$) (?v3 T_set$)) (=> (and (= (fun_app$k ?v0 ?v1) ?v2) (member$c ?v2 ?v3)) (member$c ?v1 (fun_app$j (vimage$j ?v0) ?v3)))) :named a53))
(assert (! (forall ((?v0 T_dtree_sum_N_fun$) (?v1 T_dtree_sum$) (?v2 N$) (?v3 N_set$)) (=> (and (= (fun_app$n ?v0 ?v1) ?v2) (member$b ?v2 ?v3)) (member$a ?v1 (vimage$o ?v0 ?v3)))) :named a54))
(assert (! (forall ((?v0 T_N_sum_N_fun$) (?v1 T_N_sum$) (?v2 N$) (?v3 N_set$)) (=> (and (= (fun_app$p ?v0 ?v1) ?v2) (member$b ?v2 ?v3)) (member$ ?v1 (vimage$q ?v0 ?v3)))) :named a55))
(assert (! (forall ((?v0 N_T_dtree_sum_fun$) (?v1 N$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= (fun_app$l ?v0 ?v1) ?v2) (member$a ?v2 ?v3)) (member$b ?v1 (vimage$m ?v0 ?v3)))) :named a56))
(assert (! (forall ((?v0 N_T_N_sum_fun$) (?v1 N$) (?v2 T_N_sum$) (?v3 T_N_sum_set$)) (=> (and (= (fun_app$m ?v0 ?v1) ?v2) (member$ ?v2 ?v3)) (member$b ?v1 (vimage$n ?v0 ?v3)))) :named a57))
(assert (! (forall ((?v0 T_dtree_sum_set$)) (! (= (fun_app$e id$b ?v0) ?v0) :pattern ((fun_app$e id$b ?v0)))) :named a58))
(assert (! (forall ((?v0 T_N_sum_set$)) (! (= (fun_app$d id$d ?v0) ?v0) :pattern ((fun_app$d id$d ?v0)))) :named a59))
(assert (! (forall ((?v0 T_set_set$)) (! (= (fun_app$q id$g ?v0) ?v0) :pattern ((fun_app$q id$g ?v0)))) :named a60))
(assert (! (forall ((?v0 N_set$)) (! (= (fun_app$f id$i ?v0) ?v0) :pattern ((fun_app$f id$i ?v0)))) :named a61))
(assert (! (forall ((?v0 N$)) (! (= (fun_app$g id$l ?v0) ?v0) :pattern ((fun_app$g id$l ?v0)))) :named a62))
(assert (! (forall ((?v0 T_set$)) (! (= (fun_app$j id$k ?v0) ?v0) :pattern ((fun_app$j id$k ?v0)))) :named a63))
(assert (! (forall ((?v0 T$)) (! (= (fun_app$k id$ ?v0) ?v0) :pattern ((fun_app$k id$ ?v0)))) :named a64))
(assert (! (= (cont$ tr$) (image$a (fun_app$c (map_sum$a id$) ftr$) tns$)) :named a65))
(assert (! (member$b n$ ns$) :named a66))
(assert (! (forall ((?v0 N$) (?v1 N_N_fun$) (?v2 N$) (?v3 N_set$)) (=> (and (= ?v0 (fun_app$g ?v1 ?v2)) (member$b ?v2 ?v3)) (member$b ?v0 (fun_app$f (image$i ?v1) ?v3)))) :named a67))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_dtree_sum_T_N_sum_fun$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= ?v0 (fun_app$r ?v1 ?v2)) (member$a ?v2 ?v3)) (member$ ?v0 (image$ ?v1 ?v3)))) :named a68))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_N_sum_T_dtree_sum_fun$) (?v2 T_N_sum$) (?v3 T_N_sum_set$)) (=> (and (= ?v0 (fun_app$s ?v1 ?v2)) (member$ ?v2 ?v3)) (member$a ?v0 (image$a ?v1 ?v3)))) :named a69))
(assert (! (forall ((?v0 T$) (?v1 N_T_fun$) (?v2 N$) (?v3 N_set$)) (=> (and (= ?v0 (fun_app$h ?v1 ?v2)) (member$b ?v2 ?v3)) (member$c ?v0 (image$k ?v1 ?v3)))) :named a70))
(assert (! (forall ((?v0 N$) (?v1 T_N_fun$) (?v2 T$) (?v3 T_set$)) (=> (and (= ?v0 (fun_app$i ?v1 ?v2)) (member$c ?v2 ?v3)) (member$b ?v0 (image$l ?v1 ?v3)))) :named a71))
(assert (! (forall ((?v0 T$) (?v1 T_T_fun$) (?v2 T$) (?v3 T_set$)) (=> (and (= ?v0 (fun_app$k ?v1 ?v2)) (member$c ?v2 ?v3)) (member$c ?v0 (fun_app$j (image$j ?v1) ?v3)))) :named a72))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 N_T_dtree_sum_fun$) (?v2 N$) (?v3 N_set$)) (=> (and (= ?v0 (fun_app$l ?v1 ?v2)) (member$b ?v2 ?v3)) (member$a ?v0 (image$m ?v1 ?v3)))) :named a73))
(assert (! (forall ((?v0 T_N_sum$) (?v1 N_T_N_sum_fun$) (?v2 N$) (?v3 N_set$)) (=> (and (= ?v0 (fun_app$m ?v1 ?v2)) (member$b ?v2 ?v3)) (member$ ?v0 (image$n ?v1 ?v3)))) :named a74))
(assert (! (forall ((?v0 N$) (?v1 T_dtree_sum_N_fun$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= ?v0 (fun_app$n ?v1 ?v2)) (member$a ?v2 ?v3)) (member$b ?v0 (image$o ?v1 ?v3)))) :named a75))
(assert (! (forall ((?v0 T$) (?v1 T_dtree_sum_T_fun$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= ?v0 (fun_app$o ?v1 ?v2)) (member$a ?v2 ?v3)) (member$c ?v0 (image$p ?v1 ?v3)))) :named a76))
(assert (! (= (fun_app$t root$ tr$) n$) :named a77))
(assert (! (= tr$a (fun_app$u (hsubst$ tr$) tr$)) :named a78))
(assert (! (forall ((?v0 Dtree$)) (= (vimage$ uu$ (image$ (fun_app$b (map_sum$ id$) root$) (cont$ ?v0))) (vimage$a uua$ (cont$ ?v0)))) :named a79))
(check-sat)
;(get-unsat-core)
