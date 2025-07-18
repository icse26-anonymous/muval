; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 59
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort N$ 0)
(declare-sort T$ 0)
(declare-sort Dtree$ 0)
(declare-sort N_set$ 0)
(declare-sort T_set$ 0)
(declare-sort N_N_fun$ 0)
(declare-sort T_T_fun$ 0)
(declare-sort N_bool_fun$ 0)
(declare-sort Dtree_N_fun$ 0)
(declare-sort N_dtree_fun$ 0)
(declare-sort T_N_sum_set$ 0)
(declare-sort T_T_sum_set$ 0)
(declare-sort N_T_N_sum_fun$ 0)
(declare-sort T_N_sum_N_fun$ 0)
(declare-sort Dtree_dtree_fun$ 0)
(declare-sort N_set_N_set_fun$ 0)
(declare-sort T_dtree_sum_set$ 0)
(declare-sort T_set_T_set_fun$ 0)
(declare-sort T_N_sum_bool_fun$ 0)
(declare-sort N_T_dtree_sum_fun$ 0)
(declare-sort T_dtree_sum_N_fun$ 0)
(declare-sort T_N_sum_T_N_sum_fun$ 0)
(declare-sort T_T_sum_T_T_sum_fun$ 0)
(declare-sort T_dtree_sum_bool_fun$ 0)
(declare-sort N_T_N_sum_set_prod_set$ 0)
(declare-sort T_N_sum_T_dtree_sum_fun$ 0)
(declare-sort T_dtree_sum_T_N_sum_fun$ 0)
(declare-sort T_set_set_T_set_set_fun$ 0)
(declare-sort N_N_T_N_sum_set_prod_fun$ 0)
(declare-sort N_T_N_sum_set_prod_N_fun$ 0)
(declare-sort N_T_N_sum_set_prod_bool_fun$ 0)
(declare-sort T_T_set_sum_T_T_set_sum_fun$ 0)
(declare-sort T_T_sum_set_T_T_sum_set_fun$ 0)
(declare-sort T_dtree_sum_T_dtree_sum_fun$ 0)
(declare-sort T_set_T_sum_T_set_T_sum_fun$ 0)
(declare-sort N_N_fun_T_N_sum_T_N_sum_fun_fun$ 0)
(declare-sort T_T_T_sum_sum_T_T_T_sum_sum_fun$ 0)
(declare-sort T_T_sum_T_sum_T_T_sum_T_sum_fun$ 0)
(declare-sort T_set_T_set_sum_T_set_T_set_sum_fun$ 0)
(declare-sort Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$ 0)
(declare-sort N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$ 0)
(declare-sort T_T_sum_T_set_sum_T_T_sum_T_set_sum_fun$ 0)
(declare-sort T_set_T_T_sum_sum_T_set_T_T_sum_sum_fun$ 0)
(declare-sort Dtree_dtree_fun_T_dtree_sum_T_dtree_sum_fun_fun$ 0)
(declare-datatypes () ((N_T_N_sum_set_prod$ (pair$ (fst$ N$) (snd$ T_N_sum_set$)))
  (T_N_sum$ (inl$ (projl$ T$)) (inr$ (projr$ N$)))
  (T_dtree_sum$ (inl$a (projl$a T$)) (inr$a (projr$a Dtree$)))
  (T_T_sum$ (inl$b (projl$b T$)) (inr$b (projr$b T$)))
  (T_T_set_sum$ (inl$c (projl$c T$)) (inr$c (projr$c T_set$)))
  (T_set_T_sum$ (inl$d (projl$d T_set$)) (inr$d (projr$d T$)))
  (T_T_T_sum_sum$ (inl$e (projl$e T$)) (inr$e (projr$e T_T_sum$)))
  (T_set_T_set_sum$ (inl$f (projl$f T_set$)) (inr$f (projr$f T_set$)))
  (T_T_sum_T_sum$ (inl$g (projl$g T_T_sum$)) (inr$g (projr$g T$)))
  (T_set_T_T_sum_sum$ (inl$h (projl$h T_set$)) (inr$h (projr$h T_T_sum$)))
  (T_T_sum_T_set_sum$ (inl$i (projl$i T_T_sum$)) (inr$i (projr$i T_set$)))))
(declare-fun p$ () N_T_N_sum_set_prod_set$)
(declare-fun id$ () T_T_fun$)
(declare-fun ns$ () N_set$)
(declare-fun tr$ () Dtree$)
(declare-fun uu$ (N_T_N_sum_set_prod_set$) N_T_N_sum_set_prod_bool_fun$)
(declare-fun wf$ (Dtree$) Bool)
(declare-fun id$a () T_set_T_set_fun$)
(declare-fun id$b () T_set_set_T_set_set_fun$)
(declare-fun id$c () T_T_sum_T_T_sum_fun$)
(declare-fun id$d () T_T_sum_set_T_T_sum_set_fun$)
(declare-fun id$e () N_N_fun$)
(declare-fun id$f () N_set_N_set_fun$)
(declare-fun id$g () Dtree_dtree_fun$)
(declare-fun id$h () T_dtree_sum_T_dtree_sum_fun$)
(declare-fun id$i () T_N_sum_T_N_sum_fun$)
(declare-fun id$j () T_T_set_sum_T_T_set_sum_fun$)
(declare-fun id$k () T_set_T_sum_T_set_T_sum_fun$)
(declare-fun id$l () T_T_T_sum_sum_T_T_T_sum_sum_fun$)
(declare-fun id$m () T_set_T_set_sum_T_set_T_set_sum_fun$)
(declare-fun id$n () T_T_sum_T_sum_T_T_sum_T_sum_fun$)
(declare-fun id$o () T_set_T_T_sum_sum_T_set_T_T_sum_sum_fun$)
(declare-fun id$p () T_T_sum_T_set_sum_T_T_sum_T_set_sum_fun$)
(declare-fun nsa$ () N_set$)
(declare-fun tr1$ () Dtree$)
(declare-fun tra$ () Dtree$)
(declare-fun uua$ (N_set$) N_bool_fun$)
(declare-fun uub$ (T_N_sum_set$) T_N_sum_bool_fun$)
(declare-fun uuc$ (T_dtree_sum_set$) T_dtree_sum_bool_fun$)
(declare-fun cont$ (Dtree$) T_dtree_sum_set$)
(declare-fun root$ () Dtree_N_fun$)
(declare-fun image$ (T_dtree_sum_T_N_sum_fun$ T_dtree_sum_set$) T_N_sum_set$)
(declare-fun subtr$ (N_set$ Dtree$ Dtree$) Bool)
(declare-fun image$a (T_set_T_set_fun$) T_set_set_T_set_set_fun$)
(declare-fun image$b (T_T_sum_T_T_sum_fun$) T_T_sum_set_T_T_sum_set_fun$)
(declare-fun image$c (N_N_fun$) N_set_N_set_fun$)
(declare-fun image$d (T_T_fun$) T_set_T_set_fun$)
(declare-fun image$e (N_T_N_sum_fun$ N_set$) T_N_sum_set$)
(declare-fun image$f (N_T_dtree_sum_fun$ N_set$) T_dtree_sum_set$)
(declare-fun image$g (T_N_sum_N_fun$ T_N_sum_set$) N_set$)
(declare-fun image$h (T_dtree_sum_N_fun$ T_dtree_sum_set$) N_set$)
(declare-fun image$i (T_N_sum_T_N_sum_fun$ T_N_sum_set$) T_N_sum_set$)
(declare-fun image$j (T_N_sum_T_dtree_sum_fun$ T_N_sum_set$) T_dtree_sum_set$)
(declare-fun image$k (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum_set$) T_dtree_sum_set$)
(declare-fun image$l (N_T_N_sum_set_prod_N_fun$ N_T_N_sum_set_prod_set$) N_set$)
(declare-fun image$m (N_N_T_N_sum_set_prod_fun$ N_set$) N_T_N_sum_set_prod_set$)
(declare-fun member$ (N_T_N_sum_set_prod$ N_T_N_sum_set_prod_set$) Bool)
(declare-fun collect$ (T_N_sum_bool_fun$) T_N_sum_set$)
(declare-fun fun_app$ (N_T_N_sum_set_prod_bool_fun$ N_T_N_sum_set_prod$) Bool)
(declare-fun map_sum$ (T_T_fun$) Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$)
(declare-fun member$a (T_dtree_sum$ T_dtree_sum_set$) Bool)
(declare-fun member$b (T_N_sum$ T_N_sum_set$) Bool)
(declare-fun member$c (N$ N_set$) Bool)
(declare-fun member$d (T$ T_set$) Bool)
(declare-fun member$e (T_T_sum$ T_T_sum_set$) Bool)
(declare-fun subtrOf$ (Dtree$) N_dtree_fun$)
(declare-fun collect$a (N_bool_fun$) N_set$)
(declare-fun collect$b (N_T_N_sum_set_prod_bool_fun$) N_T_N_sum_set_prod_set$)
(declare-fun collect$c (T_dtree_sum_bool_fun$) T_dtree_sum_set$)
(declare-fun fun_app$a (T_dtree_sum_bool_fun$ T_dtree_sum$) Bool)
(declare-fun fun_app$b (T_N_sum_bool_fun$ T_N_sum$) Bool)
(declare-fun fun_app$c (N_bool_fun$ N$) Bool)
(declare-fun fun_app$d (Dtree_N_fun$ Dtree$) N$)
(declare-fun fun_app$e (Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$ Dtree_N_fun$) T_dtree_sum_T_N_sum_fun$)
(declare-fun fun_app$f (T_set_T_set_fun$ T_set$) T_set$)
(declare-fun fun_app$g (T_T_sum_T_T_sum_fun$ T_T_sum$) T_T_sum$)
(declare-fun fun_app$h (T_T_fun$ T$) T$)
(declare-fun fun_app$i (N_N_fun$ N$) N$)
(declare-fun fun_app$j (N_set_N_set_fun$ N_set$) N_set$)
(declare-fun fun_app$k (N_T_N_sum_fun$ N$) T_N_sum$)
(declare-fun fun_app$l (N_T_dtree_sum_fun$ N$) T_dtree_sum$)
(declare-fun fun_app$m (T_N_sum_N_fun$ T_N_sum$) N$)
(declare-fun fun_app$n (T_dtree_sum_N_fun$ T_dtree_sum$) N$)
(declare-fun fun_app$o (T_N_sum_T_N_sum_fun$ T_N_sum$) T_N_sum$)
(declare-fun fun_app$p (T_N_sum_T_dtree_sum_fun$ T_N_sum$) T_dtree_sum$)
(declare-fun fun_app$q (T_dtree_sum_T_N_sum_fun$ T_dtree_sum$) T_N_sum$)
(declare-fun fun_app$r (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum$) T_dtree_sum$)
(declare-fun fun_app$s (N_T_N_sum_set_prod_N_fun$ N_T_N_sum_set_prod$) N$)
(declare-fun fun_app$t (Dtree_dtree_fun_T_dtree_sum_T_dtree_sum_fun_fun$ Dtree_dtree_fun$) T_dtree_sum_T_dtree_sum_fun$)
(declare-fun fun_app$u (N_N_fun_T_N_sum_T_N_sum_fun_fun$ N_N_fun$) T_N_sum_T_N_sum_fun$)
(declare-fun fun_app$v (T_T_set_sum_T_T_set_sum_fun$ T_T_set_sum$) T_T_set_sum$)
(declare-fun fun_app$w (T_set_T_sum_T_set_T_sum_fun$ T_set_T_sum$) T_set_T_sum$)
(declare-fun fun_app$x (T_T_T_sum_sum_T_T_T_sum_sum_fun$ T_T_T_sum_sum$) T_T_T_sum_sum$)
(declare-fun fun_app$y (T_set_T_set_sum_T_set_T_set_sum_fun$ T_set_T_set_sum$) T_set_T_set_sum$)
(declare-fun fun_app$z (T_T_sum_T_sum_T_T_sum_T_sum_fun$ T_T_sum_T_sum$) T_T_sum_T_sum$)
(declare-fun map_sum$a (T_T_fun$ T_T_fun$) T_T_sum_T_T_sum_fun$)
(declare-fun map_sum$b (T_T_fun$) Dtree_dtree_fun_T_dtree_sum_T_dtree_sum_fun_fun$)
(declare-fun map_sum$c (T_T_fun$) N_N_fun_T_N_sum_T_N_sum_fun_fun$)
(declare-fun map_sum$d (T_T_fun$ T_set_T_set_fun$) T_T_set_sum_T_T_set_sum_fun$)
(declare-fun map_sum$e (T_set_T_set_fun$ T_T_fun$) T_set_T_sum_T_set_T_sum_fun$)
(declare-fun map_sum$f (T_T_fun$ T_T_sum_T_T_sum_fun$) T_T_T_sum_sum_T_T_T_sum_sum_fun$)
(declare-fun map_sum$g (T_set_T_set_fun$ T_set_T_set_fun$) T_set_T_set_sum_T_set_T_set_sum_fun$)
(declare-fun map_sum$h (T_T_sum_T_T_sum_fun$ T_T_fun$) T_T_sum_T_sum_T_T_sum_T_sum_fun$)
(declare-fun map_sum$i (T_set_T_set_fun$ T_T_sum_T_T_sum_fun$) T_set_T_T_sum_sum_T_set_T_T_sum_sum_fun$)
(declare-fun map_sum$j (T_T_sum_T_T_sum_fun$ T_set_T_set_fun$) T_T_sum_T_set_sum_T_T_sum_T_set_sum_fun$)
(declare-fun map_sum$k (T_T_fun$) N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$)
(declare-fun fun_app$aa (T_set_T_T_sum_sum_T_set_T_T_sum_sum_fun$ T_set_T_T_sum_sum$) T_set_T_T_sum_sum$)
(declare-fun fun_app$ab (T_T_sum_T_set_sum_T_T_sum_T_set_sum_fun$ T_T_sum_T_set_sum$) T_T_sum_T_set_sum$)
(declare-fun fun_app$ac (N_dtree_fun$ N$) Dtree$)
(declare-fun fun_app$ad (N_N_T_N_sum_set_prod_fun$ N$) N_T_N_sum_set_prod$)
(declare-fun fun_app$ae (T_T_sum_set_T_T_sum_set_fun$ T_T_sum_set$) T_T_sum_set$)
(declare-fun fun_app$af (N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$ N_dtree_fun$) T_N_sum_T_dtree_sum_fun$)
(declare-fun fun_app$ag (Dtree_dtree_fun$ Dtree$) Dtree$)
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set$) (?v1 N_T_N_sum_set_prod$)) (! (= (fun_app$ (uu$ ?v0) ?v1) (member$ ?v1 ?v0)) :pattern ((fun_app$ (uu$ ?v0) ?v1)))) :named a0))
(assert (! (forall ((?v0 T_dtree_sum_set$) (?v1 T_dtree_sum$)) (! (= (fun_app$a (uuc$ ?v0) ?v1) (member$a ?v1 ?v0)) :pattern ((fun_app$a (uuc$ ?v0) ?v1)))) :named a1))
(assert (! (forall ((?v0 T_N_sum_set$) (?v1 T_N_sum$)) (! (= (fun_app$b (uub$ ?v0) ?v1) (member$b ?v1 ?v0)) :pattern ((fun_app$b (uub$ ?v0) ?v1)))) :named a2))
(assert (! (forall ((?v0 N_set$) (?v1 N$)) (! (= (fun_app$c (uua$ ?v0) ?v1) (member$c ?v1 ?v0)) :pattern ((fun_app$c (uua$ ?v0) ?v1)))) :named a3))
(assert (! (not (member$ (pair$ (fun_app$d root$ tra$) (image$ (fun_app$e (map_sum$ id$) root$) (cont$ tra$))) p$)) :named a4))
(assert (! (member$c (fun_app$d root$ tra$) nsa$) :named a5))
(assert (! (wf$ tra$) :named a6))
(assert (! (wf$ tr1$) :named a7))
(assert (! (forall ((?v0 Dtree$)) (=> (wf$ ?v0) (member$ (pair$ (fun_app$d root$ ?v0) (image$ (fun_app$e (map_sum$ id$) root$) (cont$ ?v0))) p$))) :named a8))
(assert (! (forall ((?v0 N$)) (exists ((?v1 T_N_sum_set$)) (member$ (pair$ ?v0 ?v1) p$))) :named a9))
(assert (! (= (image$a id$a) id$b) :named a10))
(assert (! (= (image$b id$c) id$d) :named a11))
(assert (! (= (image$c id$e) id$f) :named a12))
(assert (! (= (image$d id$) id$a) :named a13))
(assert (! (forall ((?v0 T_set$)) (! (= (fun_app$f id$a ?v0) ?v0) :pattern ((fun_app$f id$a ?v0)))) :named a14))
(assert (! (forall ((?v0 T_T_sum$)) (! (= (fun_app$g id$c ?v0) ?v0) :pattern ((fun_app$g id$c ?v0)))) :named a15))
(assert (! (forall ((?v0 T$)) (! (= (fun_app$h id$ ?v0) ?v0) :pattern ((fun_app$h id$ ?v0)))) :named a16))
(assert (! (forall ((?v0 N$) (?v1 N_N_fun$) (?v2 N$) (?v3 N_set$)) (=> (and (= ?v0 (fun_app$i ?v1 ?v2)) (member$c ?v2 ?v3)) (member$c ?v0 (fun_app$j (image$c ?v1) ?v3)))) :named a17))
(assert (! (forall ((?v0 T_N_sum$) (?v1 N_T_N_sum_fun$) (?v2 N$) (?v3 N_set$)) (=> (and (= ?v0 (fun_app$k ?v1 ?v2)) (member$c ?v2 ?v3)) (member$b ?v0 (image$e ?v1 ?v3)))) :named a18))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 N_T_dtree_sum_fun$) (?v2 N$) (?v3 N_set$)) (=> (and (= ?v0 (fun_app$l ?v1 ?v2)) (member$c ?v2 ?v3)) (member$a ?v0 (image$f ?v1 ?v3)))) :named a19))
(assert (! (forall ((?v0 N$) (?v1 T_N_sum_N_fun$) (?v2 T_N_sum$) (?v3 T_N_sum_set$)) (=> (and (= ?v0 (fun_app$m ?v1 ?v2)) (member$b ?v2 ?v3)) (member$c ?v0 (image$g ?v1 ?v3)))) :named a20))
(assert (! (forall ((?v0 N$) (?v1 T_dtree_sum_N_fun$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= ?v0 (fun_app$n ?v1 ?v2)) (member$a ?v2 ?v3)) (member$c ?v0 (image$h ?v1 ?v3)))) :named a21))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_T_N_sum_fun$) (?v2 T_N_sum$) (?v3 T_N_sum_set$)) (=> (and (= ?v0 (fun_app$o ?v1 ?v2)) (member$b ?v2 ?v3)) (member$b ?v0 (image$i ?v1 ?v3)))) :named a22))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_N_sum_T_dtree_sum_fun$) (?v2 T_N_sum$) (?v3 T_N_sum_set$)) (=> (and (= ?v0 (fun_app$p ?v1 ?v2)) (member$b ?v2 ?v3)) (member$a ?v0 (image$j ?v1 ?v3)))) :named a23))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_dtree_sum_T_N_sum_fun$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= ?v0 (fun_app$q ?v1 ?v2)) (member$a ?v2 ?v3)) (member$b ?v0 (image$ ?v1 ?v3)))) :named a24))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_T_dtree_sum_fun$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= ?v0 (fun_app$r ?v1 ?v2)) (member$a ?v2 ?v3)) (member$a ?v0 (image$k ?v1 ?v3)))) :named a25))
(assert (! (forall ((?v0 N$) (?v1 N_T_N_sum_set_prod_N_fun$) (?v2 N_T_N_sum_set_prod$) (?v3 N_T_N_sum_set_prod_set$)) (=> (and (= ?v0 (fun_app$s ?v1 ?v2)) (member$ ?v2 ?v3)) (member$c ?v0 (image$l ?v1 ?v3)))) :named a26))
(assert (! (forall ((?v0 N$) (?v1 T_N_sum_set$) (?v2 N$) (?v3 T_N_sum_set$)) (= (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a27))
(assert (! (forall ((?v0 N$) (?v1 T_N_sum_set$) (?v2 N$) (?v3 T_N_sum_set$)) (= (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))) :named a28))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (=> (and (= (fun_app$d root$ ?v0) (fun_app$d root$ ?v1)) (= (cont$ ?v0) (cont$ ?v1))) (= ?v0 ?v1))) :named a29))
(assert (! (forall ((?v0 T_T_sum$)) (= (fun_app$g (map_sum$a id$ id$) ?v0) ?v0)) :named a30))
(assert (! (forall ((?v0 T_dtree_sum$)) (= (fun_app$r (fun_app$t (map_sum$b id$) id$g) ?v0) ?v0)) :named a31))
(assert (! (forall ((?v0 T_N_sum$)) (= (fun_app$o (fun_app$u (map_sum$c id$) id$e) ?v0) ?v0)) :named a32))
(assert (! (forall ((?v0 T_T_set_sum$)) (= (fun_app$v (map_sum$d id$ id$a) ?v0) ?v0)) :named a33))
(assert (! (forall ((?v0 T_set_T_sum$)) (= (fun_app$w (map_sum$e id$a id$) ?v0) ?v0)) :named a34))
(assert (! (forall ((?v0 T_T_T_sum_sum$)) (= (fun_app$x (map_sum$f id$ id$c) ?v0) ?v0)) :named a35))
(assert (! (forall ((?v0 T_set_T_set_sum$)) (= (fun_app$y (map_sum$g id$a id$a) ?v0) ?v0)) :named a36))
(assert (! (forall ((?v0 T_T_sum_T_sum$)) (= (fun_app$z (map_sum$h id$c id$) ?v0) ?v0)) :named a37))
(assert (! (forall ((?v0 T_set_T_T_sum_sum$)) (= (fun_app$aa (map_sum$i id$a id$c) ?v0) ?v0)) :named a38))
(assert (! (forall ((?v0 T_T_sum_T_set_sum$)) (= (fun_app$ab (map_sum$j id$c id$a) ?v0) ?v0)) :named a39))
(assert (! (= (map_sum$a id$ id$) id$c) :named a40))
(assert (! (= (fun_app$t (map_sum$b id$) id$g) id$h) :named a41))
(assert (! (= (fun_app$u (map_sum$c id$) id$e) id$i) :named a42))
(assert (! (= (map_sum$d id$ id$a) id$j) :named a43))
(assert (! (= (map_sum$e id$a id$) id$k) :named a44))
(assert (! (= (map_sum$f id$ id$c) id$l) :named a45))
(assert (! (= (map_sum$g id$a id$a) id$m) :named a46))
(assert (! (= (map_sum$h id$c id$) id$n) :named a47))
(assert (! (= (map_sum$i id$a id$c) id$o) :named a48))
(assert (! (= (map_sum$j id$c id$a) id$p) :named a49))
(assert (! (forall ((?v0 N$) (?v1 Dtree$)) (=> (member$b (inr$ ?v0) (image$ (fun_app$e (map_sum$ id$) root$) (cont$ ?v1))) (= (fun_app$d root$ (fun_app$ac (subtrOf$ ?v1) ?v0)) ?v0))) :named a50))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$) (?v2 Dtree$)) (=> (and (wf$ ?v0) (and (member$a (inr$a ?v1) (cont$ ?v0)) (member$a (inr$a ?v2) (cont$ ?v0)))) (= (= (fun_app$d root$ ?v1) (fun_app$d root$ ?v2)) (= ?v1 ?v2)))) :named a51))
(assert (! (forall ((?v0 T_set$)) (! (= (fun_app$f id$a ?v0) ?v0) :pattern ((fun_app$f id$a ?v0)))) :named a52))
(assert (! (forall ((?v0 T_T_sum$)) (! (= (fun_app$g id$c ?v0) ?v0) :pattern ((fun_app$g id$c ?v0)))) :named a53))
(assert (! (forall ((?v0 T$)) (! (= (fun_app$h id$ ?v0) ?v0) :pattern ((fun_app$h id$ ?v0)))) :named a54))
(assert (! (forall ((?v0 N$) (?v1 N_N_fun$) (?v2 N_set$)) (= (member$c ?v0 (fun_app$j (image$c ?v1) ?v2)) (exists ((?v3 N$)) (and (member$c ?v3 ?v2) (= ?v0 (fun_app$i ?v1 ?v3)))))) :named a55))
(assert (! (forall ((?v0 N$) (?v1 T_N_sum_N_fun$) (?v2 T_N_sum_set$)) (= (member$c ?v0 (image$g ?v1 ?v2)) (exists ((?v3 T_N_sum$)) (and (member$b ?v3 ?v2) (= ?v0 (fun_app$m ?v1 ?v3)))))) :named a56))
(assert (! (forall ((?v0 N$) (?v1 T_dtree_sum_N_fun$) (?v2 T_dtree_sum_set$)) (= (member$c ?v0 (image$h ?v1 ?v2)) (exists ((?v3 T_dtree_sum$)) (and (member$a ?v3 ?v2) (= ?v0 (fun_app$n ?v1 ?v3)))))) :named a57))
(assert (! (forall ((?v0 T_N_sum$) (?v1 N_T_N_sum_fun$) (?v2 N_set$)) (= (member$b ?v0 (image$e ?v1 ?v2)) (exists ((?v3 N$)) (and (member$c ?v3 ?v2) (= ?v0 (fun_app$k ?v1 ?v3)))))) :named a58))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 N_T_dtree_sum_fun$) (?v2 N_set$)) (= (member$a ?v0 (image$f ?v1 ?v2)) (exists ((?v3 N$)) (and (member$c ?v3 ?v2) (= ?v0 (fun_app$l ?v1 ?v3)))))) :named a59))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_T_N_sum_fun$) (?v2 T_N_sum_set$)) (= (member$b ?v0 (image$i ?v1 ?v2)) (exists ((?v3 T_N_sum$)) (and (member$b ?v3 ?v2) (= ?v0 (fun_app$o ?v1 ?v3)))))) :named a60))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_dtree_sum_T_N_sum_fun$) (?v2 T_dtree_sum_set$)) (= (member$b ?v0 (image$ ?v1 ?v2)) (exists ((?v3 T_dtree_sum$)) (and (member$a ?v3 ?v2) (= ?v0 (fun_app$q ?v1 ?v3)))))) :named a61))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_N_sum_T_dtree_sum_fun$) (?v2 T_N_sum_set$)) (= (member$a ?v0 (image$j ?v1 ?v2)) (exists ((?v3 T_N_sum$)) (and (member$b ?v3 ?v2) (= ?v0 (fun_app$p ?v1 ?v3)))))) :named a62))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_T_dtree_sum_fun$) (?v2 T_dtree_sum_set$)) (= (member$a ?v0 (image$k ?v1 ?v2)) (exists ((?v3 T_dtree_sum$)) (and (member$a ?v3 ?v2) (= ?v0 (fun_app$r ?v1 ?v3)))))) :named a63))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$) (?v1 N_N_T_N_sum_set_prod_fun$) (?v2 N_set$)) (= (member$ ?v0 (image$m ?v1 ?v2)) (exists ((?v3 N$)) (and (member$c ?v3 ?v2) (= ?v0 (fun_app$ad ?v1 ?v3)))))) :named a64))
(assert (! (forall ((?v0 N$) (?v1 Dtree$)) (=> (member$b (inr$ ?v0) (image$ (fun_app$e (map_sum$ id$) root$) (cont$ ?v1))) (member$a (inr$a (fun_app$ac (subtrOf$ ?v1) ?v0)) (cont$ ?v1)))) :named a65))
(assert (! (forall ((?v0 N$) (?v1 Dtree$)) (=> (member$b (inr$ ?v0) (image$ (fun_app$e (map_sum$ id$) root$) (cont$ ?v1))) (and (member$a (inr$a (fun_app$ac (subtrOf$ ?v1) ?v0)) (cont$ ?v1)) (= (fun_app$d root$ (fun_app$ac (subtrOf$ ?v1) ?v0)) ?v0)))) :named a66))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (=> (and (wf$ ?v0) (member$a (inr$a ?v1) (cont$ ?v0))) (wf$ ?v1))) :named a67))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (=> (member$a (inr$a ?v0) (cont$ ?v1)) (member$b (inr$ (fun_app$d root$ ?v0)) (image$ (fun_app$e (map_sum$ id$) root$) (cont$ ?v1))))) :named a68))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$)) (exists ((?v1 N$) (?v2 T_N_sum_set$)) (= ?v0 (pair$ ?v1 ?v2)))) :named a69))
(assert (! (forall ((?v0 N$) (?v1 T_N_sum_set$) (?v2 N$) (?v3 T_N_sum_set$)) (=> (and (= (pair$ ?v0 ?v1) (pair$ ?v2 ?v3)) (=> (and (= ?v0 ?v2) (= ?v1 ?v3)) false)) false)) :named a70))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$)) (=> (forall ((?v1 N$) (?v2 T_N_sum_set$)) (=> (= ?v0 (pair$ ?v1 ?v2)) false)) false)) :named a71))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_bool_fun$) (?v1 N_T_N_sum_set_prod$)) (=> (forall ((?v2 N$) (?v3 T_N_sum_set$)) (fun_app$ ?v0 (pair$ ?v2 ?v3))) (fun_app$ ?v0 ?v1))) :named a72))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$)) (=> (forall ((?v1 N$) (?v2 T_N_sum_set$)) (=> (= ?v0 (pair$ ?v1 ?v2)) false)) false)) :named a73))
(assert (! (forall ((?v0 N$) (?v1 N_set$) (?v2 N_N_fun$)) (=> (member$c ?v0 ?v1) (member$c (fun_app$i ?v2 ?v0) (fun_app$j (image$c ?v2) ?v1)))) :named a74))
(assert (! (forall ((?v0 N$) (?v1 N_set$) (?v2 N_T_N_sum_fun$)) (=> (member$c ?v0 ?v1) (member$b (fun_app$k ?v2 ?v0) (image$e ?v2 ?v1)))) :named a75))
(assert (! (forall ((?v0 N$) (?v1 N_set$) (?v2 N_T_dtree_sum_fun$)) (=> (member$c ?v0 ?v1) (member$a (fun_app$l ?v2 ?v0) (image$f ?v2 ?v1)))) :named a76))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 T_N_sum_N_fun$)) (=> (member$b ?v0 ?v1) (member$c (fun_app$m ?v2 ?v0) (image$g ?v2 ?v1)))) :named a77))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_N_fun$)) (=> (member$a ?v0 ?v1) (member$c (fun_app$n ?v2 ?v0) (image$h ?v2 ?v1)))) :named a78))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 T_N_sum_T_N_sum_fun$)) (=> (member$b ?v0 ?v1) (member$b (fun_app$o ?v2 ?v0) (image$i ?v2 ?v1)))) :named a79))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 T_N_sum_T_dtree_sum_fun$)) (=> (member$b ?v0 ?v1) (member$a (fun_app$p ?v2 ?v0) (image$j ?v2 ?v1)))) :named a80))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_T_N_sum_fun$)) (=> (member$a ?v0 ?v1) (member$b (fun_app$q ?v2 ?v0) (image$ ?v2 ?v1)))) :named a81))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_T_dtree_sum_fun$)) (=> (member$a ?v0 ?v1) (member$a (fun_app$r ?v2 ?v0) (image$k ?v2 ?v1)))) :named a82))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$) (?v1 N_T_N_sum_set_prod_set$) (?v2 N_T_N_sum_set_prod_N_fun$)) (=> (member$ ?v0 ?v1) (member$c (fun_app$s ?v2 ?v0) (image$l ?v2 ?v1)))) :named a83))
(assert (! (forall ((?v0 N$) (?v1 N_set$) (?v2 N$) (?v3 N_N_fun$)) (=> (and (member$c ?v0 ?v1) (= ?v2 (fun_app$i ?v3 ?v0))) (member$c ?v2 (fun_app$j (image$c ?v3) ?v1)))) :named a84))
(assert (! (forall ((?v0 N$) (?v1 N_set$) (?v2 T_N_sum$) (?v3 N_T_N_sum_fun$)) (=> (and (member$c ?v0 ?v1) (= ?v2 (fun_app$k ?v3 ?v0))) (member$b ?v2 (image$e ?v3 ?v1)))) :named a85))
(assert (! (forall ((?v0 N$) (?v1 N_set$) (?v2 T_dtree_sum$) (?v3 N_T_dtree_sum_fun$)) (=> (and (member$c ?v0 ?v1) (= ?v2 (fun_app$l ?v3 ?v0))) (member$a ?v2 (image$f ?v3 ?v1)))) :named a86))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 N$) (?v3 T_N_sum_N_fun$)) (=> (and (member$b ?v0 ?v1) (= ?v2 (fun_app$m ?v3 ?v0))) (member$c ?v2 (image$g ?v3 ?v1)))) :named a87))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 N$) (?v3 T_dtree_sum_N_fun$)) (=> (and (member$a ?v0 ?v1) (= ?v2 (fun_app$n ?v3 ?v0))) (member$c ?v2 (image$h ?v3 ?v1)))) :named a88))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 T_N_sum$) (?v3 T_N_sum_T_N_sum_fun$)) (=> (and (member$b ?v0 ?v1) (= ?v2 (fun_app$o ?v3 ?v0))) (member$b ?v2 (image$i ?v3 ?v1)))) :named a89))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 T_dtree_sum$) (?v3 T_N_sum_T_dtree_sum_fun$)) (=> (and (member$b ?v0 ?v1) (= ?v2 (fun_app$p ?v3 ?v0))) (member$a ?v2 (image$j ?v3 ?v1)))) :named a90))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_N_sum$) (?v3 T_dtree_sum_T_N_sum_fun$)) (=> (and (member$a ?v0 ?v1) (= ?v2 (fun_app$q ?v3 ?v0))) (member$b ?v2 (image$ ?v3 ?v1)))) :named a91))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_T_dtree_sum_fun$)) (=> (and (member$a ?v0 ?v1) (= ?v2 (fun_app$r ?v3 ?v0))) (member$a ?v2 (image$k ?v3 ?v1)))) :named a92))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$) (?v1 N_T_N_sum_set_prod_set$) (?v2 N$) (?v3 N_T_N_sum_set_prod_N_fun$)) (=> (and (member$ ?v0 ?v1) (= ?v2 (fun_app$s ?v3 ?v0))) (member$c ?v2 (image$l ?v3 ?v1)))) :named a93))
(assert (! (forall ((?v0 N_N_fun$) (?v1 N_set$) (?v2 N_bool_fun$)) (=> (forall ((?v3 N$)) (=> (member$c ?v3 (fun_app$j (image$c ?v0) ?v1)) (fun_app$c ?v2 ?v3))) (forall ((?v3 N$)) (=> (member$c ?v3 ?v1) (fun_app$c ?v2 (fun_app$i ?v0 ?v3)))))) :named a94))
(assert (! (forall ((?v0 T_N_sum_N_fun$) (?v1 T_N_sum_set$) (?v2 N_bool_fun$)) (=> (forall ((?v3 N$)) (=> (member$c ?v3 (image$g ?v0 ?v1)) (fun_app$c ?v2 ?v3))) (forall ((?v3 T_N_sum$)) (=> (member$b ?v3 ?v1) (fun_app$c ?v2 (fun_app$m ?v0 ?v3)))))) :named a95))
(assert (! (forall ((?v0 T_dtree_sum_N_fun$) (?v1 T_dtree_sum_set$) (?v2 N_bool_fun$)) (=> (forall ((?v3 N$)) (=> (member$c ?v3 (image$h ?v0 ?v1)) (fun_app$c ?v2 ?v3))) (forall ((?v3 T_dtree_sum$)) (=> (member$a ?v3 ?v1) (fun_app$c ?v2 (fun_app$n ?v0 ?v3)))))) :named a96))
(assert (! (forall ((?v0 N_T_N_sum_fun$) (?v1 N_set$) (?v2 T_N_sum_bool_fun$)) (=> (forall ((?v3 T_N_sum$)) (=> (member$b ?v3 (image$e ?v0 ?v1)) (fun_app$b ?v2 ?v3))) (forall ((?v3 N$)) (=> (member$c ?v3 ?v1) (fun_app$b ?v2 (fun_app$k ?v0 ?v3)))))) :named a97))
(assert (! (forall ((?v0 N_T_dtree_sum_fun$) (?v1 N_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (forall ((?v3 T_dtree_sum$)) (=> (member$a ?v3 (image$f ?v0 ?v1)) (fun_app$a ?v2 ?v3))) (forall ((?v3 N$)) (=> (member$c ?v3 ?v1) (fun_app$a ?v2 (fun_app$l ?v0 ?v3)))))) :named a98))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$) (?v1 T_N_sum_set$) (?v2 T_N_sum_bool_fun$)) (=> (forall ((?v3 T_N_sum$)) (=> (member$b ?v3 (image$i ?v0 ?v1)) (fun_app$b ?v2 ?v3))) (forall ((?v3 T_N_sum$)) (=> (member$b ?v3 ?v1) (fun_app$b ?v2 (fun_app$o ?v0 ?v3)))))) :named a99))
(assert (! (forall ((?v0 T_dtree_sum_T_N_sum_fun$) (?v1 T_dtree_sum_set$) (?v2 T_N_sum_bool_fun$)) (=> (forall ((?v3 T_N_sum$)) (=> (member$b ?v3 (image$ ?v0 ?v1)) (fun_app$b ?v2 ?v3))) (forall ((?v3 T_dtree_sum$)) (=> (member$a ?v3 ?v1) (fun_app$b ?v2 (fun_app$q ?v0 ?v3)))))) :named a100))
(assert (! (forall ((?v0 T_N_sum_T_dtree_sum_fun$) (?v1 T_N_sum_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (forall ((?v3 T_dtree_sum$)) (=> (member$a ?v3 (image$j ?v0 ?v1)) (fun_app$a ?v2 ?v3))) (forall ((?v3 T_N_sum$)) (=> (member$b ?v3 ?v1) (fun_app$a ?v2 (fun_app$p ?v0 ?v3)))))) :named a101))
(assert (! (forall ((?v0 T_dtree_sum_T_dtree_sum_fun$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (forall ((?v3 T_dtree_sum$)) (=> (member$a ?v3 (image$k ?v0 ?v1)) (fun_app$a ?v2 ?v3))) (forall ((?v3 T_dtree_sum$)) (=> (member$a ?v3 ?v1) (fun_app$a ?v2 (fun_app$r ?v0 ?v3)))))) :named a102))
(assert (! (forall ((?v0 N_N_T_N_sum_set_prod_fun$) (?v1 N_set$) (?v2 N_T_N_sum_set_prod_bool_fun$)) (=> (forall ((?v3 N_T_N_sum_set_prod$)) (=> (member$ ?v3 (image$m ?v0 ?v1)) (fun_app$ ?v2 ?v3))) (forall ((?v3 N$)) (=> (member$c ?v3 ?v1) (fun_app$ ?v2 (fun_app$ad ?v0 ?v3)))))) :named a103))
(assert (! (forall ((?v0 N_N_fun$) (?v1 N_set$) (?v2 N_bool_fun$)) (=> (exists ((?v3 N$)) (and (member$c ?v3 (fun_app$j (image$c ?v0) ?v1)) (fun_app$c ?v2 ?v3))) (exists ((?v3 N$)) (and (member$c ?v3 ?v1) (fun_app$c ?v2 (fun_app$i ?v0 ?v3)))))) :named a104))
(assert (! (forall ((?v0 T_N_sum_N_fun$) (?v1 T_N_sum_set$) (?v2 N_bool_fun$)) (=> (exists ((?v3 N$)) (and (member$c ?v3 (image$g ?v0 ?v1)) (fun_app$c ?v2 ?v3))) (exists ((?v3 T_N_sum$)) (and (member$b ?v3 ?v1) (fun_app$c ?v2 (fun_app$m ?v0 ?v3)))))) :named a105))
(assert (! (forall ((?v0 T_dtree_sum_N_fun$) (?v1 T_dtree_sum_set$) (?v2 N_bool_fun$)) (=> (exists ((?v3 N$)) (and (member$c ?v3 (image$h ?v0 ?v1)) (fun_app$c ?v2 ?v3))) (exists ((?v3 T_dtree_sum$)) (and (member$a ?v3 ?v1) (fun_app$c ?v2 (fun_app$n ?v0 ?v3)))))) :named a106))
(assert (! (forall ((?v0 N_T_N_sum_fun$) (?v1 N_set$) (?v2 T_N_sum_bool_fun$)) (=> (exists ((?v3 T_N_sum$)) (and (member$b ?v3 (image$e ?v0 ?v1)) (fun_app$b ?v2 ?v3))) (exists ((?v3 N$)) (and (member$c ?v3 ?v1) (fun_app$b ?v2 (fun_app$k ?v0 ?v3)))))) :named a107))
(assert (! (forall ((?v0 N_T_dtree_sum_fun$) (?v1 N_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (exists ((?v3 T_dtree_sum$)) (and (member$a ?v3 (image$f ?v0 ?v1)) (fun_app$a ?v2 ?v3))) (exists ((?v3 N$)) (and (member$c ?v3 ?v1) (fun_app$a ?v2 (fun_app$l ?v0 ?v3)))))) :named a108))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$) (?v1 T_N_sum_set$) (?v2 T_N_sum_bool_fun$)) (=> (exists ((?v3 T_N_sum$)) (and (member$b ?v3 (image$i ?v0 ?v1)) (fun_app$b ?v2 ?v3))) (exists ((?v3 T_N_sum$)) (and (member$b ?v3 ?v1) (fun_app$b ?v2 (fun_app$o ?v0 ?v3)))))) :named a109))
(assert (! (forall ((?v0 T_dtree_sum_T_N_sum_fun$) (?v1 T_dtree_sum_set$) (?v2 T_N_sum_bool_fun$)) (=> (exists ((?v3 T_N_sum$)) (and (member$b ?v3 (image$ ?v0 ?v1)) (fun_app$b ?v2 ?v3))) (exists ((?v3 T_dtree_sum$)) (and (member$a ?v3 ?v1) (fun_app$b ?v2 (fun_app$q ?v0 ?v3)))))) :named a110))
(assert (! (forall ((?v0 T_N_sum_T_dtree_sum_fun$) (?v1 T_N_sum_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (exists ((?v3 T_dtree_sum$)) (and (member$a ?v3 (image$j ?v0 ?v1)) (fun_app$a ?v2 ?v3))) (exists ((?v3 T_N_sum$)) (and (member$b ?v3 ?v1) (fun_app$a ?v2 (fun_app$p ?v0 ?v3)))))) :named a111))
(assert (! (forall ((?v0 T_dtree_sum_T_dtree_sum_fun$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (exists ((?v3 T_dtree_sum$)) (and (member$a ?v3 (image$k ?v0 ?v1)) (fun_app$a ?v2 ?v3))) (exists ((?v3 T_dtree_sum$)) (and (member$a ?v3 ?v1) (fun_app$a ?v2 (fun_app$r ?v0 ?v3)))))) :named a112))
(assert (! (forall ((?v0 N_N_T_N_sum_set_prod_fun$) (?v1 N_set$) (?v2 N_T_N_sum_set_prod_bool_fun$)) (=> (exists ((?v3 N_T_N_sum_set_prod$)) (and (member$ ?v3 (image$m ?v0 ?v1)) (fun_app$ ?v2 ?v3))) (exists ((?v3 N$)) (and (member$c ?v3 ?v1) (fun_app$ ?v2 (fun_app$ad ?v0 ?v3)))))) :named a113))
(assert (! (forall ((?v0 T_set$) (?v1 T_set$) (?v2 T_T_fun$) (?v3 T_T_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 T$)) (=> (member$d ?v4 ?v1) (= (fun_app$h ?v2 ?v4) (fun_app$h ?v3 ?v4))))) (= (fun_app$f (image$d ?v2) ?v0) (fun_app$f (image$d ?v3) ?v1)))) :named a114))
(assert (! (forall ((?v0 N_set$) (?v1 N_set$) (?v2 N_N_T_N_sum_set_prod_fun$) (?v3 N_N_T_N_sum_set_prod_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 N$)) (=> (member$c ?v4 ?v1) (= (fun_app$ad ?v2 ?v4) (fun_app$ad ?v3 ?v4))))) (= (image$m ?v2 ?v0) (image$m ?v3 ?v1)))) :named a115))
(assert (! (forall ((?v0 N_set$) (?v1 N_set$) (?v2 N_T_dtree_sum_fun$) (?v3 N_T_dtree_sum_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 N$)) (=> (member$c ?v4 ?v1) (= (fun_app$l ?v2 ?v4) (fun_app$l ?v3 ?v4))))) (= (image$f ?v2 ?v0) (image$f ?v3 ?v1)))) :named a116))
(assert (! (forall ((?v0 N_set$) (?v1 N_set$) (?v2 N_T_N_sum_fun$) (?v3 N_T_N_sum_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 N$)) (=> (member$c ?v4 ?v1) (= (fun_app$k ?v2 ?v4) (fun_app$k ?v3 ?v4))))) (= (image$e ?v2 ?v0) (image$e ?v3 ?v1)))) :named a117))
(assert (! (forall ((?v0 N_set$) (?v1 N_set$) (?v2 N_N_fun$) (?v3 N_N_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 N$)) (=> (member$c ?v4 ?v1) (= (fun_app$i ?v2 ?v4) (fun_app$i ?v3 ?v4))))) (= (fun_app$j (image$c ?v2) ?v0) (fun_app$j (image$c ?v3) ?v1)))) :named a118))
(assert (! (forall ((?v0 T_dtree_sum_set$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_T_N_sum_fun$) (?v3 T_dtree_sum_T_N_sum_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 T_dtree_sum$)) (=> (member$a ?v4 ?v1) (= (fun_app$q ?v2 ?v4) (fun_app$q ?v3 ?v4))))) (= (image$ ?v2 ?v0) (image$ ?v3 ?v1)))) :named a119))
(assert (! (forall ((?v0 T$) (?v1 T_T_fun$) (?v2 T_T_sum_set$)) (= (member$e (inr$b ?v0) (fun_app$ae (image$b (map_sum$a id$ ?v1)) ?v2)) (exists ((?v3 T$)) (and (member$e (inr$b ?v3) ?v2) (= (fun_app$h ?v1 ?v3) ?v0))))) :named a120))
(assert (! (forall ((?v0 N$) (?v1 N_N_fun$) (?v2 T_N_sum_set$)) (= (member$b (inr$ ?v0) (image$i (fun_app$u (map_sum$c id$) ?v1) ?v2)) (exists ((?v3 N$)) (and (member$b (inr$ ?v3) ?v2) (= (fun_app$i ?v1 ?v3) ?v0))))) :named a121))
(assert (! (forall ((?v0 Dtree$) (?v1 N_dtree_fun$) (?v2 T_N_sum_set$)) (= (member$a (inr$a ?v0) (image$j (fun_app$af (map_sum$k id$) ?v1) ?v2)) (exists ((?v3 N$)) (and (member$b (inr$ ?v3) ?v2) (= (fun_app$ac ?v1 ?v3) ?v0))))) :named a122))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree_dtree_fun$) (?v2 T_dtree_sum_set$)) (= (member$a (inr$a ?v0) (image$k (fun_app$t (map_sum$b id$) ?v1) ?v2)) (exists ((?v3 Dtree$)) (and (member$a (inr$a ?v3) ?v2) (= (fun_app$ag ?v1 ?v3) ?v0))))) :named a123))
(assert (! (forall ((?v0 N$) (?v1 Dtree_N_fun$) (?v2 T_dtree_sum_set$)) (= (member$b (inr$ ?v0) (image$ (fun_app$e (map_sum$ id$) ?v1) ?v2)) (exists ((?v3 Dtree$)) (and (member$a (inr$a ?v3) ?v2) (= (fun_app$d ?v1 ?v3) ?v0))))) :named a124))
(assert (! (subtr$ ns$ tr$ tr1$) :named a125))
(assert (! (forall ((?v0 T$) (?v1 T_T_fun$) (?v2 T_T_sum_set$)) (=> (member$e (inr$b ?v0) (fun_app$ae (image$b (map_sum$a id$ ?v1)) ?v2)) (exists ((?v3 T$)) (and (member$e (inr$b ?v3) ?v2) (= (fun_app$h ?v1 ?v3) ?v0))))) :named a126))
(assert (! (forall ((?v0 N$) (?v1 N_N_fun$) (?v2 T_N_sum_set$)) (=> (member$b (inr$ ?v0) (image$i (fun_app$u (map_sum$c id$) ?v1) ?v2)) (exists ((?v3 N$)) (and (member$b (inr$ ?v3) ?v2) (= (fun_app$i ?v1 ?v3) ?v0))))) :named a127))
(assert (! (forall ((?v0 Dtree$) (?v1 N_dtree_fun$) (?v2 T_N_sum_set$)) (=> (member$a (inr$a ?v0) (image$j (fun_app$af (map_sum$k id$) ?v1) ?v2)) (exists ((?v3 N$)) (and (member$b (inr$ ?v3) ?v2) (= (fun_app$ac ?v1 ?v3) ?v0))))) :named a128))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree_dtree_fun$) (?v2 T_dtree_sum_set$)) (=> (member$a (inr$a ?v0) (image$k (fun_app$t (map_sum$b id$) ?v1) ?v2)) (exists ((?v3 Dtree$)) (and (member$a (inr$a ?v3) ?v2) (= (fun_app$ag ?v1 ?v3) ?v0))))) :named a129))
(assert (! (forall ((?v0 N$) (?v1 Dtree_N_fun$) (?v2 T_dtree_sum_set$)) (=> (member$b (inr$ ?v0) (image$ (fun_app$e (map_sum$ id$) ?v1) ?v2)) (exists ((?v3 Dtree$)) (and (member$a (inr$a ?v3) ?v2) (= (fun_app$d ?v1 ?v3) ?v0))))) :named a130))
(assert (! (forall ((?v0 N$) (?v1 N$)) (= (= (inr$ ?v0) (inr$ ?v1)) (= ?v0 ?v1))) :named a131))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (= (= (inr$a ?v0) (inr$a ?v1)) (= ?v0 ?v1))) :named a132))
(assert (! (forall ((?v0 N$) (?v1 N$)) (= (= (inr$ ?v0) (inr$ ?v1)) (= ?v0 ?v1))) :named a133))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (= (= (inr$a ?v0) (inr$a ?v1)) (= ?v0 ?v1))) :named a134))
(assert (! (forall ((?v0 T_N_sum_bool_fun$) (?v1 T_N_sum_bool_fun$)) (=> (forall ((?v2 T_N_sum$)) (= (fun_app$b ?v0 ?v2) (fun_app$b ?v1 ?v2))) (= (collect$ ?v0) (collect$ ?v1)))) :named a135))
(assert (! (forall ((?v0 N_bool_fun$) (?v1 N_bool_fun$)) (=> (forall ((?v2 N$)) (= (fun_app$c ?v0 ?v2) (fun_app$c ?v1 ?v2))) (= (collect$a ?v0) (collect$a ?v1)))) :named a136))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_bool_fun$) (?v1 N_T_N_sum_set_prod_bool_fun$)) (=> (forall ((?v2 N_T_N_sum_set_prod$)) (= (fun_app$ ?v0 ?v2) (fun_app$ ?v1 ?v2))) (= (collect$b ?v0) (collect$b ?v1)))) :named a137))
(assert (! (forall ((?v0 N_T_N_sum_set_prod_set$)) (= (collect$b (uu$ ?v0)) ?v0)) :named a138))
(assert (! (forall ((?v0 N_set$)) (= (collect$a (uua$ ?v0)) ?v0)) :named a139))
(assert (! (forall ((?v0 T_N_sum_set$)) (= (collect$ (uub$ ?v0)) ?v0)) :named a140))
(assert (! (forall ((?v0 T_dtree_sum_set$)) (= (collect$c (uuc$ ?v0)) ?v0)) :named a141))
(assert (! (forall ((?v0 N_T_N_sum_set_prod$) (?v1 N_T_N_sum_set_prod_bool_fun$)) (= (member$ ?v0 (collect$b ?v1)) (fun_app$ ?v1 ?v0))) :named a142))
(assert (! (forall ((?v0 N$) (?v1 N_bool_fun$)) (= (member$c ?v0 (collect$a ?v1)) (fun_app$c ?v1 ?v0))) :named a143))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_bool_fun$)) (= (member$b ?v0 (collect$ ?v1)) (fun_app$b ?v1 ?v0))) :named a144))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_bool_fun$)) (= (member$a ?v0 (collect$c ?v1)) (fun_app$a ?v1 ?v0))) :named a145))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_N_fun$) (?v2 T_N_sum$) (?v3 N$)) (=> (= (fun_app$o (fun_app$u (map_sum$c ?v0) ?v1) ?v2) (inr$ ?v3)) (exists ((?v4 N$)) (and (= ?v2 (inr$ ?v4)) (= (fun_app$i ?v1 ?v4) ?v3))))) :named a146))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_dtree_fun$) (?v2 T_N_sum$) (?v3 Dtree$)) (=> (= (fun_app$p (fun_app$af (map_sum$k ?v0) ?v1) ?v2) (inr$a ?v3)) (exists ((?v4 N$)) (and (= ?v2 (inr$ ?v4)) (= (fun_app$ac ?v1 ?v4) ?v3))))) :named a147))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_dtree_fun$) (?v2 T_dtree_sum$) (?v3 Dtree$)) (=> (= (fun_app$r (fun_app$t (map_sum$b ?v0) ?v1) ?v2) (inr$a ?v3)) (exists ((?v4 Dtree$)) (and (= ?v2 (inr$a ?v4)) (= (fun_app$ag ?v1 ?v4) ?v3))))) :named a148))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_N_fun$) (?v2 T_dtree_sum$) (?v3 N$)) (=> (= (fun_app$q (fun_app$e (map_sum$ ?v0) ?v1) ?v2) (inr$ ?v3)) (exists ((?v4 Dtree$)) (and (= ?v2 (inr$a ?v4)) (= (fun_app$d ?v1 ?v4) ?v3))))) :named a149))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_N_fun$) (?v2 N$)) (! (= (fun_app$o (fun_app$u (map_sum$c ?v0) ?v1) (inr$ ?v2)) (inr$ (fun_app$i ?v1 ?v2))) :pattern ((fun_app$o (fun_app$u (map_sum$c ?v0) ?v1) (inr$ ?v2))))) :named a150))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_dtree_fun$) (?v2 N$)) (! (= (fun_app$p (fun_app$af (map_sum$k ?v0) ?v1) (inr$ ?v2)) (inr$a (fun_app$ac ?v1 ?v2))) :pattern ((fun_app$p (fun_app$af (map_sum$k ?v0) ?v1) (inr$ ?v2))))) :named a151))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_dtree_fun$) (?v2 Dtree$)) (! (= (fun_app$r (fun_app$t (map_sum$b ?v0) ?v1) (inr$a ?v2)) (inr$a (fun_app$ag ?v1 ?v2))) :pattern ((fun_app$r (fun_app$t (map_sum$b ?v0) ?v1) (inr$a ?v2))))) :named a152))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_N_fun$) (?v2 Dtree$)) (! (= (fun_app$q (fun_app$e (map_sum$ ?v0) ?v1) (inr$a ?v2)) (inr$ (fun_app$d ?v1 ?v2))) :pattern ((fun_app$q (fun_app$e (map_sum$ ?v0) ?v1) (inr$a ?v2))))) :named a153))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_N_fun$) (?v2 Bool) (?v3 T_N_sum$) (?v4 N$)) (= (fun_app$o (fun_app$u (map_sum$c ?v0) ?v1) (ite ?v2 ?v3 (inr$ ?v4))) (ite ?v2 (fun_app$o (fun_app$u (map_sum$c ?v0) ?v1) ?v3) (inr$ (fun_app$i ?v1 ?v4))))) :named a154))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_dtree_fun$) (?v2 Bool) (?v3 T_N_sum$) (?v4 N$)) (= (fun_app$p (fun_app$af (map_sum$k ?v0) ?v1) (ite ?v2 ?v3 (inr$ ?v4))) (ite ?v2 (fun_app$p (fun_app$af (map_sum$k ?v0) ?v1) ?v3) (inr$a (fun_app$ac ?v1 ?v4))))) :named a155))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_dtree_fun$) (?v2 Bool) (?v3 T_dtree_sum$) (?v4 Dtree$)) (= (fun_app$r (fun_app$t (map_sum$b ?v0) ?v1) (ite ?v2 ?v3 (inr$a ?v4))) (ite ?v2 (fun_app$r (fun_app$t (map_sum$b ?v0) ?v1) ?v3) (inr$a (fun_app$ag ?v1 ?v4))))) :named a156))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_N_fun$) (?v2 Bool) (?v3 T_dtree_sum$) (?v4 Dtree$)) (= (fun_app$q (fun_app$e (map_sum$ ?v0) ?v1) (ite ?v2 ?v3 (inr$a ?v4))) (ite ?v2 (fun_app$q (fun_app$e (map_sum$ ?v0) ?v1) ?v3) (inr$ (fun_app$d ?v1 ?v4))))) :named a157))
(check-sat)
;(get-unsat-core)
