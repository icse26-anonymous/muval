; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 70
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort N$ 0)
(declare-sort T$ 0)
(declare-sort A_set$ 0)
(declare-sort Dtree$ 0)
(declare-sort T_set$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort N_N_fun$ 0)
(declare-sort T_T_fun$ 0)
(declare-sort A_bool_fun$ 0)
(declare-sort T_bool_fun$ 0)
(declare-sort Dtree_N_fun$ 0)
(declare-sort N_dtree_fun$ 0)
(declare-sort T_N_sum_set$ 0)
(declare-sort T_T_sum_set$ 0)
(declare-sort A_T_N_sum_fun$ 0)
(declare-sort T_N_sum_a_fun$ 0)
(declare-sort A_set_a_set_fun$ 0)
(declare-sort Dtree_dtree_fun$ 0)
(declare-sort T_dtree_sum_set$ 0)
(declare-sort T_set_T_set_fun$ 0)
(declare-sort T_N_sum_bool_fun$ 0)
(declare-sort A_T_dtree_sum_fun$ 0)
(declare-sort T_dtree_sum_a_fun$ 0)
(declare-sort T_N_sum_T_N_sum_fun$ 0)
(declare-sort T_T_sum_T_T_sum_fun$ 0)
(declare-sort T_dtree_sum_bool_fun$ 0)
(declare-sort T_N_sum_T_dtree_sum_fun$ 0)
(declare-sort T_dtree_sum_T_N_sum_fun$ 0)
(declare-sort T_set_set_T_set_set_fun$ 0)
(declare-sort T_T_sum_set_T_T_sum_set_fun$ 0)
(declare-sort T_dtree_sum_T_dtree_sum_fun$ 0)
(declare-sort T_set_T_sum_T_set_T_sum_fun$ 0)
(declare-sort N_N_fun_T_N_sum_T_N_sum_fun_fun$ 0)
(declare-sort T_T_sum_T_sum_T_T_sum_T_sum_fun$ 0)
(declare-sort T_set_T_set_sum_T_set_T_set_sum_fun$ 0)
(declare-sort Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$ 0)
(declare-sort N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$ 0)
(declare-sort T_T_sum_T_set_sum_T_T_sum_T_set_sum_fun$ 0)
(declare-sort T_set_T_T_sum_sum_T_set_T_T_sum_sum_fun$ 0)
(declare-sort T_T_sum_T_T_sum_sum_T_T_sum_T_T_sum_sum_fun$ 0)
(declare-sort Dtree_dtree_fun_T_dtree_sum_T_dtree_sum_fun_fun$ 0)
(declare-datatypes () ((T_N_sum$ (inl$ (projl$ T$)) (inr$ (projr$ N$)))
  (T_dtree_sum$ (inl$a (projl$a T$)) (inr$a (projr$a Dtree$)))
  (T_T_sum$ (inl$b (projl$b T$)) (inr$b (projr$b T$)))
  (T_set_T_sum$ (inl$c (projl$c T_set$)) (inr$c (projr$c T$)))
  (T_set_T_set_sum$ (inl$d (projl$d T_set$)) (inr$d (projr$d T_set$)))
  (T_set_T_T_sum_sum$ (inl$e (projl$e T_set$)) (inr$e (projr$e T_T_sum$)))
  (T_T_sum_T_sum$ (inl$f (projl$f T_T_sum$)) (inr$f (projr$f T$)))
  (T_T_sum_T_set_sum$ (inl$g (projl$g T_T_sum$)) (inr$g (projr$g T_set$)))
  (T_T_sum_T_T_sum_sum$ (inl$h (projl$h T_T_sum$)) (inr$h (projr$h T_T_sum$)))))
(declare-fun k$ (Dtree$) A_set$)
(declare-fun x$ () A$)
(declare-fun id$ () T_T_fun$)
(declare-fun tr$ () Dtree$)
(declare-fun wf$ (Dtree$) Bool)
(declare-fun id$a () T_set_T_set_fun$)
(declare-fun id$b () T_set_set_T_set_set_fun$)
(declare-fun id$c () T_T_sum_T_T_sum_fun$)
(declare-fun id$d () T_T_sum_set_T_T_sum_set_fun$)
(declare-fun id$e () A_a_fun$)
(declare-fun id$f () A_set_a_set_fun$)
(declare-fun id$g () T_set_T_sum_T_set_T_sum_fun$)
(declare-fun id$h () T_set_T_set_sum_T_set_T_set_sum_fun$)
(declare-fun id$i () T_set_T_T_sum_sum_T_set_T_T_sum_sum_fun$)
(declare-fun id$j () T_T_sum_T_sum_T_T_sum_T_sum_fun$)
(declare-fun id$k () T_T_sum_T_set_sum_T_T_sum_T_set_sum_fun$)
(declare-fun id$l () T_T_sum_T_T_sum_sum_T_T_sum_T_T_sum_sum_fun$)
(declare-fun id$m () Dtree_dtree_fun$)
(declare-fun id$n () T_dtree_sum_T_dtree_sum_fun$)
(declare-fun id$o () N_N_fun$)
(declare-fun id$p () T_N_sum_T_N_sum_fun$)
(declare-fun tr$a () Dtree$)
(declare-fun cont$ (Dtree$) T_dtree_sum_set$)
(declare-fun root$ () Dtree_N_fun$)
(declare-fun image$ (T_dtree_sum_T_N_sum_fun$ T_dtree_sum_set$) T_N_sum_set$)
(declare-fun image$a (T_T_sum_T_T_sum_fun$) T_T_sum_set_T_T_sum_set_fun$)
(declare-fun image$b (T_N_sum_T_N_sum_fun$ T_N_sum_set$) T_N_sum_set$)
(declare-fun image$c (T_N_sum_T_dtree_sum_fun$ T_N_sum_set$) T_dtree_sum_set$)
(declare-fun image$d (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum_set$) T_dtree_sum_set$)
(declare-fun image$e (T_set_T_set_fun$) T_set_set_T_set_set_fun$)
(declare-fun image$f (A_a_fun$) A_set_a_set_fun$)
(declare-fun image$g (T_T_fun$) T_set_T_set_fun$)
(declare-fun image$h (T_N_sum_a_fun$ T_N_sum_set$) A_set$)
(declare-fun image$i (A_T_N_sum_fun$ A_set$) T_N_sum_set$)
(declare-fun image$j (A_T_dtree_sum_fun$ A_set$) T_dtree_sum_set$)
(declare-fun image$k (T_dtree_sum_a_fun$ T_dtree_sum_set$) A_set$)
(declare-fun member$ (T_N_sum$ T_N_sum_set$) Bool)
(declare-fun fun_app$ (N_dtree_fun$ N$) Dtree$)
(declare-fun map_sum$ (T_T_fun$) Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$)
(declare-fun member$a (A$ A_set$) Bool)
(declare-fun member$b (T_dtree_sum$ T_dtree_sum_set$) Bool)
(declare-fun member$c (T_T_sum$ T_T_sum_set$) Bool)
(declare-fun member$d (T$ T_set$) Bool)
(declare-fun subtrOf$ (Dtree$) N_dtree_fun$)
(declare-fun fun_app$a (Dtree_N_fun$ Dtree$) N$)
(declare-fun fun_app$b (Dtree_N_fun_T_dtree_sum_T_N_sum_fun_fun$ Dtree_N_fun$) T_dtree_sum_T_N_sum_fun$)
(declare-fun fun_app$c (T_T_sum_set_T_T_sum_set_fun$ T_T_sum_set$) T_T_sum_set$)
(declare-fun fun_app$d (T_T_fun$ T$) T$)
(declare-fun fun_app$e (N_N_fun_T_N_sum_T_N_sum_fun_fun$ N_N_fun$) T_N_sum_T_N_sum_fun$)
(declare-fun fun_app$f (N_N_fun$ N$) N$)
(declare-fun fun_app$g (N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$ N_dtree_fun$) T_N_sum_T_dtree_sum_fun$)
(declare-fun fun_app$h (Dtree_dtree_fun_T_dtree_sum_T_dtree_sum_fun_fun$ Dtree_dtree_fun$) T_dtree_sum_T_dtree_sum_fun$)
(declare-fun fun_app$i (Dtree_dtree_fun$ Dtree$) Dtree$)
(declare-fun fun_app$j (T_set_T_set_fun$ T_set$) T_set$)
(declare-fun fun_app$k (T_T_sum_T_T_sum_fun$ T_T_sum$) T_T_sum$)
(declare-fun fun_app$l (T_N_sum_T_N_sum_fun$ T_N_sum$) T_N_sum$)
(declare-fun fun_app$m (T_N_sum_a_fun$ T_N_sum$) A$)
(declare-fun fun_app$n (T_N_sum_T_dtree_sum_fun$ T_N_sum$) T_dtree_sum$)
(declare-fun fun_app$o (A_T_N_sum_fun$ A$) T_N_sum$)
(declare-fun fun_app$p (A_a_fun$ A$) A$)
(declare-fun fun_app$q (A_set_a_set_fun$ A_set$) A_set$)
(declare-fun fun_app$r (A_T_dtree_sum_fun$ A$) T_dtree_sum$)
(declare-fun fun_app$s (T_dtree_sum_T_N_sum_fun$ T_dtree_sum$) T_N_sum$)
(declare-fun fun_app$t (T_dtree_sum_a_fun$ T_dtree_sum$) A$)
(declare-fun fun_app$u (T_dtree_sum_T_dtree_sum_fun$ T_dtree_sum$) T_dtree_sum$)
(declare-fun fun_app$v (T_bool_fun$ T$) Bool)
(declare-fun fun_app$w (T_N_sum_bool_fun$ T_N_sum$) Bool)
(declare-fun fun_app$x (A_bool_fun$ A$) Bool)
(declare-fun fun_app$y (T_dtree_sum_bool_fun$ T_dtree_sum$) Bool)
(declare-fun hsubst_c$ (Dtree$ Dtree$) T_dtree_sum_set$)
(declare-fun map_sum$a (T_T_fun$ T_T_fun$) T_T_sum_T_T_sum_fun$)
(declare-fun map_sum$b (T_T_fun$) N_N_fun_T_N_sum_T_N_sum_fun_fun$)
(declare-fun map_sum$c (T_T_fun$) N_dtree_fun_T_N_sum_T_dtree_sum_fun_fun$)
(declare-fun map_sum$d (T_T_fun$) Dtree_dtree_fun_T_dtree_sum_T_dtree_sum_fun_fun$)
(declare-fun map_sum$e (T_set_T_set_fun$ T_T_fun$) T_set_T_sum_T_set_T_sum_fun$)
(declare-fun map_sum$f (T_set_T_set_fun$ T_set_T_set_fun$) T_set_T_set_sum_T_set_T_set_sum_fun$)
(declare-fun map_sum$g (T_set_T_set_fun$ T_T_sum_T_T_sum_fun$) T_set_T_T_sum_sum_T_set_T_T_sum_sum_fun$)
(declare-fun map_sum$h (T_T_sum_T_T_sum_fun$ T_T_fun$) T_T_sum_T_sum_T_T_sum_T_sum_fun$)
(declare-fun map_sum$i (T_T_sum_T_T_sum_fun$ T_set_T_set_fun$) T_T_sum_T_set_sum_T_T_sum_T_set_sum_fun$)
(declare-fun map_sum$j (T_T_sum_T_T_sum_fun$ T_T_sum_T_T_sum_fun$) T_T_sum_T_T_sum_sum_T_T_sum_T_T_sum_sum_fun$)
(assert (! (not (and (exists ((?v0 N$)) (and (= (k$ (fun_app$ (subtrOf$ tr$) (fun_app$a root$ tr$a))) (k$ (fun_app$ (subtrOf$ tr$) ?v0))) (member$ (inr$ ?v0) (image$ (fun_app$b (map_sum$ id$) root$) (cont$ tr$))))) (member$a x$ (k$ (fun_app$ (subtrOf$ tr$) (fun_app$a root$ tr$a)))))) :named a0))
(assert (! (wf$ tr$) :named a1))
(assert (! (member$a x$ (k$ tr$a)) :named a2))
(assert (! (forall ((?v0 N$) (?v1 Dtree$)) (=> (member$ (inr$ ?v0) (image$ (fun_app$b (map_sum$ id$) root$) (cont$ ?v1))) (= (fun_app$a root$ (fun_app$ (subtrOf$ ?v1) ?v0)) ?v0))) :named a3))
(assert (! (member$b (inr$a tr$a) (cont$ tr$)) :named a4))
(assert (! (forall ((?v0 T$) (?v1 T_T_fun$) (?v2 T_T_sum_set$)) (= (member$c (inr$b ?v0) (fun_app$c (image$a (map_sum$a id$ ?v1)) ?v2)) (exists ((?v3 T$)) (and (member$c (inr$b ?v3) ?v2) (= (fun_app$d ?v1 ?v3) ?v0))))) :named a5))
(assert (! (forall ((?v0 N$) (?v1 N_N_fun$) (?v2 T_N_sum_set$)) (= (member$ (inr$ ?v0) (image$b (fun_app$e (map_sum$b id$) ?v1) ?v2)) (exists ((?v3 N$)) (and (member$ (inr$ ?v3) ?v2) (= (fun_app$f ?v1 ?v3) ?v0))))) :named a6))
(assert (! (forall ((?v0 Dtree$) (?v1 N_dtree_fun$) (?v2 T_N_sum_set$)) (= (member$b (inr$a ?v0) (image$c (fun_app$g (map_sum$c id$) ?v1) ?v2)) (exists ((?v3 N$)) (and (member$ (inr$ ?v3) ?v2) (= (fun_app$ ?v1 ?v3) ?v0))))) :named a7))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree_dtree_fun$) (?v2 T_dtree_sum_set$)) (= (member$b (inr$a ?v0) (image$d (fun_app$h (map_sum$d id$) ?v1) ?v2)) (exists ((?v3 Dtree$)) (and (member$b (inr$a ?v3) ?v2) (= (fun_app$i ?v1 ?v3) ?v0))))) :named a8))
(assert (! (forall ((?v0 N$) (?v1 Dtree_N_fun$) (?v2 T_dtree_sum_set$)) (= (member$ (inr$ ?v0) (image$ (fun_app$b (map_sum$ id$) ?v1) ?v2)) (exists ((?v3 Dtree$)) (and (member$b (inr$a ?v3) ?v2) (= (fun_app$a ?v1 ?v3) ?v0))))) :named a9))
(assert (! (= (image$e id$a) id$b) :named a10))
(assert (! (= (image$a id$c) id$d) :named a11))
(assert (! (= (image$f id$e) id$f) :named a12))
(assert (! (= (image$g id$) id$a) :named a13))
(assert (! (forall ((?v0 T$) (?v1 T_T_fun$) (?v2 T_T_sum_set$)) (=> (member$c (inr$b ?v0) (fun_app$c (image$a (map_sum$a id$ ?v1)) ?v2)) (exists ((?v3 T$)) (and (member$c (inr$b ?v3) ?v2) (= (fun_app$d ?v1 ?v3) ?v0))))) :named a14))
(assert (! (forall ((?v0 N$) (?v1 N_N_fun$) (?v2 T_N_sum_set$)) (=> (member$ (inr$ ?v0) (image$b (fun_app$e (map_sum$b id$) ?v1) ?v2)) (exists ((?v3 N$)) (and (member$ (inr$ ?v3) ?v2) (= (fun_app$f ?v1 ?v3) ?v0))))) :named a15))
(assert (! (forall ((?v0 Dtree$) (?v1 N_dtree_fun$) (?v2 T_N_sum_set$)) (=> (member$b (inr$a ?v0) (image$c (fun_app$g (map_sum$c id$) ?v1) ?v2)) (exists ((?v3 N$)) (and (member$ (inr$ ?v3) ?v2) (= (fun_app$ ?v1 ?v3) ?v0))))) :named a16))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree_dtree_fun$) (?v2 T_dtree_sum_set$)) (=> (member$b (inr$a ?v0) (image$d (fun_app$h (map_sum$d id$) ?v1) ?v2)) (exists ((?v3 Dtree$)) (and (member$b (inr$a ?v3) ?v2) (= (fun_app$i ?v1 ?v3) ?v0))))) :named a17))
(assert (! (forall ((?v0 N$) (?v1 Dtree_N_fun$) (?v2 T_dtree_sum_set$)) (=> (member$ (inr$ ?v0) (image$ (fun_app$b (map_sum$ id$) ?v1) ?v2)) (exists ((?v3 Dtree$)) (and (member$b (inr$a ?v3) ?v2) (= (fun_app$a ?v1 ?v3) ?v0))))) :named a18))
(assert (! (forall ((?v0 N$) (?v1 N$)) (= (= (inr$ ?v0) (inr$ ?v1)) (= ?v0 ?v1))) :named a19))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (= (= (inr$a ?v0) (inr$a ?v1)) (= ?v0 ?v1))) :named a20))
(assert (! (forall ((?v0 N$) (?v1 N$)) (= (= (inr$ ?v0) (inr$ ?v1)) (= ?v0 ?v1))) :named a21))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (= (= (inr$a ?v0) (inr$a ?v1)) (= ?v0 ?v1))) :named a22))
(assert (! (forall ((?v0 T_set$)) (! (= (fun_app$j id$a ?v0) ?v0) :pattern ((fun_app$j id$a ?v0)))) :named a23))
(assert (! (forall ((?v0 T_T_sum$)) (! (= (fun_app$k id$c ?v0) ?v0) :pattern ((fun_app$k id$c ?v0)))) :named a24))
(assert (! (forall ((?v0 T$)) (! (= (fun_app$d id$ ?v0) ?v0) :pattern ((fun_app$d id$ ?v0)))) :named a25))
(assert (! (forall ((?v0 T$) (?v1 T_T_fun$) (?v2 T$) (?v3 T_set$)) (=> (and (= ?v0 (fun_app$d ?v1 ?v2)) (member$d ?v2 ?v3)) (member$d ?v0 (fun_app$j (image$g ?v1) ?v3)))) :named a26))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_T_N_sum_fun$) (?v2 T_N_sum$) (?v3 T_N_sum_set$)) (=> (and (= ?v0 (fun_app$l ?v1 ?v2)) (member$ ?v2 ?v3)) (member$ ?v0 (image$b ?v1 ?v3)))) :named a27))
(assert (! (forall ((?v0 A$) (?v1 T_N_sum_a_fun$) (?v2 T_N_sum$) (?v3 T_N_sum_set$)) (=> (and (= ?v0 (fun_app$m ?v1 ?v2)) (member$ ?v2 ?v3)) (member$a ?v0 (image$h ?v1 ?v3)))) :named a28))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_N_sum_T_dtree_sum_fun$) (?v2 T_N_sum$) (?v3 T_N_sum_set$)) (=> (and (= ?v0 (fun_app$n ?v1 ?v2)) (member$ ?v2 ?v3)) (member$b ?v0 (image$c ?v1 ?v3)))) :named a29))
(assert (! (forall ((?v0 T_N_sum$) (?v1 A_T_N_sum_fun$) (?v2 A$) (?v3 A_set$)) (=> (and (= ?v0 (fun_app$o ?v1 ?v2)) (member$a ?v2 ?v3)) (member$ ?v0 (image$i ?v1 ?v3)))) :named a30))
(assert (! (forall ((?v0 A$) (?v1 A_a_fun$) (?v2 A$) (?v3 A_set$)) (=> (and (= ?v0 (fun_app$p ?v1 ?v2)) (member$a ?v2 ?v3)) (member$a ?v0 (fun_app$q (image$f ?v1) ?v3)))) :named a31))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 A_T_dtree_sum_fun$) (?v2 A$) (?v3 A_set$)) (=> (and (= ?v0 (fun_app$r ?v1 ?v2)) (member$a ?v2 ?v3)) (member$b ?v0 (image$j ?v1 ?v3)))) :named a32))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_dtree_sum_T_N_sum_fun$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= ?v0 (fun_app$s ?v1 ?v2)) (member$b ?v2 ?v3)) (member$ ?v0 (image$ ?v1 ?v3)))) :named a33))
(assert (! (forall ((?v0 A$) (?v1 T_dtree_sum_a_fun$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= ?v0 (fun_app$t ?v1 ?v2)) (member$b ?v2 ?v3)) (member$a ?v0 (image$k ?v1 ?v3)))) :named a34))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_T_dtree_sum_fun$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_set$)) (=> (and (= ?v0 (fun_app$u ?v1 ?v2)) (member$b ?v2 ?v3)) (member$b ?v0 (image$d ?v1 ?v3)))) :named a35))
(assert (! (forall ((?v0 N$) (?v1 Dtree$)) (=> (member$ (inr$ ?v0) (image$ (fun_app$b (map_sum$ id$) root$) (cont$ ?v1))) (and (member$b (inr$a (fun_app$ (subtrOf$ ?v1) ?v0)) (cont$ ?v1)) (= (fun_app$a root$ (fun_app$ (subtrOf$ ?v1) ?v0)) ?v0)))) :named a36))
(assert (! (forall ((?v0 N$) (?v1 Dtree$)) (=> (member$ (inr$ ?v0) (image$ (fun_app$b (map_sum$ id$) root$) (cont$ ?v1))) (member$b (inr$a (fun_app$ (subtrOf$ ?v1) ?v0)) (cont$ ?v1)))) :named a37))
(assert (! (forall ((?v0 T_T_fun$) (?v1 T_T_fun$) (?v2 Bool) (?v3 T$) (?v4 T_T_sum$)) (= (fun_app$k (map_sum$a ?v0 ?v1) (ite ?v2 (inr$b ?v3) ?v4)) (ite ?v2 (inr$b (fun_app$d ?v1 ?v3)) (fun_app$k (map_sum$a ?v0 ?v1) ?v4)))) :named a38))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_N_fun$) (?v2 Bool) (?v3 N$) (?v4 T_N_sum$)) (= (fun_app$l (fun_app$e (map_sum$b ?v0) ?v1) (ite ?v2 (inr$ ?v3) ?v4)) (ite ?v2 (inr$ (fun_app$f ?v1 ?v3)) (fun_app$l (fun_app$e (map_sum$b ?v0) ?v1) ?v4)))) :named a39))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_dtree_fun$) (?v2 Bool) (?v3 N$) (?v4 T_N_sum$)) (= (fun_app$n (fun_app$g (map_sum$c ?v0) ?v1) (ite ?v2 (inr$ ?v3) ?v4)) (ite ?v2 (inr$a (fun_app$ ?v1 ?v3)) (fun_app$n (fun_app$g (map_sum$c ?v0) ?v1) ?v4)))) :named a40))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_dtree_fun$) (?v2 Bool) (?v3 Dtree$) (?v4 T_dtree_sum$)) (= (fun_app$u (fun_app$h (map_sum$d ?v0) ?v1) (ite ?v2 (inr$a ?v3) ?v4)) (ite ?v2 (inr$a (fun_app$i ?v1 ?v3)) (fun_app$u (fun_app$h (map_sum$d ?v0) ?v1) ?v4)))) :named a41))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_N_fun$) (?v2 Bool) (?v3 Dtree$) (?v4 T_dtree_sum$)) (= (fun_app$s (fun_app$b (map_sum$ ?v0) ?v1) (ite ?v2 (inr$a ?v3) ?v4)) (ite ?v2 (inr$ (fun_app$a ?v1 ?v3)) (fun_app$s (fun_app$b (map_sum$ ?v0) ?v1) ?v4)))) :named a42))
(assert (! (forall ((?v0 T_T_fun$) (?v1 T_T_fun$) (?v2 Bool) (?v3 T_T_sum$) (?v4 T$)) (= (fun_app$k (map_sum$a ?v0 ?v1) (ite ?v2 ?v3 (inr$b ?v4))) (ite ?v2 (fun_app$k (map_sum$a ?v0 ?v1) ?v3) (inr$b (fun_app$d ?v1 ?v4))))) :named a43))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_N_fun$) (?v2 Bool) (?v3 T_N_sum$) (?v4 N$)) (= (fun_app$l (fun_app$e (map_sum$b ?v0) ?v1) (ite ?v2 ?v3 (inr$ ?v4))) (ite ?v2 (fun_app$l (fun_app$e (map_sum$b ?v0) ?v1) ?v3) (inr$ (fun_app$f ?v1 ?v4))))) :named a44))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_dtree_fun$) (?v2 Bool) (?v3 T_N_sum$) (?v4 N$)) (= (fun_app$n (fun_app$g (map_sum$c ?v0) ?v1) (ite ?v2 ?v3 (inr$ ?v4))) (ite ?v2 (fun_app$n (fun_app$g (map_sum$c ?v0) ?v1) ?v3) (inr$a (fun_app$ ?v1 ?v4))))) :named a45))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_dtree_fun$) (?v2 Bool) (?v3 T_dtree_sum$) (?v4 Dtree$)) (= (fun_app$u (fun_app$h (map_sum$d ?v0) ?v1) (ite ?v2 ?v3 (inr$a ?v4))) (ite ?v2 (fun_app$u (fun_app$h (map_sum$d ?v0) ?v1) ?v3) (inr$a (fun_app$i ?v1 ?v4))))) :named a46))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_N_fun$) (?v2 Bool) (?v3 T_dtree_sum$) (?v4 Dtree$)) (= (fun_app$s (fun_app$b (map_sum$ ?v0) ?v1) (ite ?v2 ?v3 (inr$a ?v4))) (ite ?v2 (fun_app$s (fun_app$b (map_sum$ ?v0) ?v1) ?v3) (inr$ (fun_app$a ?v1 ?v4))))) :named a47))
(assert (! (forall ((?v0 T_T_fun$) (?v1 T_T_fun$) (?v2 T$)) (! (= (fun_app$k (map_sum$a ?v0 ?v1) (inr$b ?v2)) (inr$b (fun_app$d ?v1 ?v2))) :pattern ((fun_app$k (map_sum$a ?v0 ?v1) (inr$b ?v2))))) :named a48))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_N_fun$) (?v2 N$)) (! (= (fun_app$l (fun_app$e (map_sum$b ?v0) ?v1) (inr$ ?v2)) (inr$ (fun_app$f ?v1 ?v2))) :pattern ((fun_app$l (fun_app$e (map_sum$b ?v0) ?v1) (inr$ ?v2))))) :named a49))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_dtree_fun$) (?v2 N$)) (! (= (fun_app$n (fun_app$g (map_sum$c ?v0) ?v1) (inr$ ?v2)) (inr$a (fun_app$ ?v1 ?v2))) :pattern ((fun_app$n (fun_app$g (map_sum$c ?v0) ?v1) (inr$ ?v2))))) :named a50))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_dtree_fun$) (?v2 Dtree$)) (! (= (fun_app$u (fun_app$h (map_sum$d ?v0) ?v1) (inr$a ?v2)) (inr$a (fun_app$i ?v1 ?v2))) :pattern ((fun_app$u (fun_app$h (map_sum$d ?v0) ?v1) (inr$a ?v2))))) :named a51))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_N_fun$) (?v2 Dtree$)) (! (= (fun_app$s (fun_app$b (map_sum$ ?v0) ?v1) (inr$a ?v2)) (inr$ (fun_app$a ?v1 ?v2))) :pattern ((fun_app$s (fun_app$b (map_sum$ ?v0) ?v1) (inr$a ?v2))))) :named a52))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$) (?v2 Dtree$)) (=> (and (wf$ ?v0) (and (member$b (inr$a ?v1) (cont$ ?v0)) (member$b (inr$a ?v2) (cont$ ?v0)))) (= (= (fun_app$a root$ ?v1) (fun_app$a root$ ?v2)) (= ?v1 ?v2)))) :named a53))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (=> (and (wf$ ?v0) (member$b (inr$a ?v1) (cont$ ?v0))) (= (fun_app$ (subtrOf$ ?v0) (fun_app$a root$ ?v1)) ?v1))) :named a54))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (=> (and (wf$ ?v0) (member$b (inr$a ?v1) (cont$ ?v0))) (wf$ ?v1))) :named a55))
(assert (! (forall ((?v0 T$) (?v1 T_set$) (?v2 T_T_fun$)) (=> (member$d ?v0 ?v1) (member$d (fun_app$d ?v2 ?v0) (fun_app$j (image$g ?v2) ?v1)))) :named a56))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 T_N_sum_T_N_sum_fun$)) (=> (member$ ?v0 ?v1) (member$ (fun_app$l ?v2 ?v0) (image$b ?v2 ?v1)))) :named a57))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 T_N_sum_a_fun$)) (=> (member$ ?v0 ?v1) (member$a (fun_app$m ?v2 ?v0) (image$h ?v2 ?v1)))) :named a58))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 T_N_sum_T_dtree_sum_fun$)) (=> (member$ ?v0 ?v1) (member$b (fun_app$n ?v2 ?v0) (image$c ?v2 ?v1)))) :named a59))
(assert (! (forall ((?v0 A$) (?v1 A_set$) (?v2 A_T_N_sum_fun$)) (=> (member$a ?v0 ?v1) (member$ (fun_app$o ?v2 ?v0) (image$i ?v2 ?v1)))) :named a60))
(assert (! (forall ((?v0 A$) (?v1 A_set$) (?v2 A_a_fun$)) (=> (member$a ?v0 ?v1) (member$a (fun_app$p ?v2 ?v0) (fun_app$q (image$f ?v2) ?v1)))) :named a61))
(assert (! (forall ((?v0 A$) (?v1 A_set$) (?v2 A_T_dtree_sum_fun$)) (=> (member$a ?v0 ?v1) (member$b (fun_app$r ?v2 ?v0) (image$j ?v2 ?v1)))) :named a62))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_T_N_sum_fun$)) (=> (member$b ?v0 ?v1) (member$ (fun_app$s ?v2 ?v0) (image$ ?v2 ?v1)))) :named a63))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_a_fun$)) (=> (member$b ?v0 ?v1) (member$a (fun_app$t ?v2 ?v0) (image$k ?v2 ?v1)))) :named a64))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_T_dtree_sum_fun$)) (=> (member$b ?v0 ?v1) (member$b (fun_app$u ?v2 ?v0) (image$d ?v2 ?v1)))) :named a65))
(assert (! (forall ((?v0 T$) (?v1 T_set$) (?v2 T$) (?v3 T_T_fun$)) (=> (and (member$d ?v0 ?v1) (= ?v2 (fun_app$d ?v3 ?v0))) (member$d ?v2 (fun_app$j (image$g ?v3) ?v1)))) :named a66))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 T_N_sum$) (?v3 T_N_sum_T_N_sum_fun$)) (=> (and (member$ ?v0 ?v1) (= ?v2 (fun_app$l ?v3 ?v0))) (member$ ?v2 (image$b ?v3 ?v1)))) :named a67))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 A$) (?v3 T_N_sum_a_fun$)) (=> (and (member$ ?v0 ?v1) (= ?v2 (fun_app$m ?v3 ?v0))) (member$a ?v2 (image$h ?v3 ?v1)))) :named a68))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_set$) (?v2 T_dtree_sum$) (?v3 T_N_sum_T_dtree_sum_fun$)) (=> (and (member$ ?v0 ?v1) (= ?v2 (fun_app$n ?v3 ?v0))) (member$b ?v2 (image$c ?v3 ?v1)))) :named a69))
(assert (! (forall ((?v0 A$) (?v1 A_set$) (?v2 T_N_sum$) (?v3 A_T_N_sum_fun$)) (=> (and (member$a ?v0 ?v1) (= ?v2 (fun_app$o ?v3 ?v0))) (member$ ?v2 (image$i ?v3 ?v1)))) :named a70))
(assert (! (forall ((?v0 A$) (?v1 A_set$) (?v2 A$) (?v3 A_a_fun$)) (=> (and (member$a ?v0 ?v1) (= ?v2 (fun_app$p ?v3 ?v0))) (member$a ?v2 (fun_app$q (image$f ?v3) ?v1)))) :named a71))
(assert (! (forall ((?v0 A$) (?v1 A_set$) (?v2 T_dtree_sum$) (?v3 A_T_dtree_sum_fun$)) (=> (and (member$a ?v0 ?v1) (= ?v2 (fun_app$r ?v3 ?v0))) (member$b ?v2 (image$j ?v3 ?v1)))) :named a72))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_N_sum$) (?v3 T_dtree_sum_T_N_sum_fun$)) (=> (and (member$b ?v0 ?v1) (= ?v2 (fun_app$s ?v3 ?v0))) (member$ ?v2 (image$ ?v3 ?v1)))) :named a73))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 A$) (?v3 T_dtree_sum_a_fun$)) (=> (and (member$b ?v0 ?v1) (= ?v2 (fun_app$t ?v3 ?v0))) (member$a ?v2 (image$k ?v3 ?v1)))) :named a74))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum$) (?v3 T_dtree_sum_T_dtree_sum_fun$)) (=> (and (member$b ?v0 ?v1) (= ?v2 (fun_app$u ?v3 ?v0))) (member$b ?v2 (image$d ?v3 ?v1)))) :named a75))
(assert (! (forall ((?v0 T_T_fun$) (?v1 T_set$) (?v2 T_bool_fun$)) (=> (forall ((?v3 T$)) (=> (member$d ?v3 (fun_app$j (image$g ?v0) ?v1)) (fun_app$v ?v2 ?v3))) (forall ((?v3 T$)) (=> (member$d ?v3 ?v1) (fun_app$v ?v2 (fun_app$d ?v0 ?v3)))))) :named a76))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$) (?v1 T_N_sum_set$) (?v2 T_N_sum_bool_fun$)) (=> (forall ((?v3 T_N_sum$)) (=> (member$ ?v3 (image$b ?v0 ?v1)) (fun_app$w ?v2 ?v3))) (forall ((?v3 T_N_sum$)) (=> (member$ ?v3 ?v1) (fun_app$w ?v2 (fun_app$l ?v0 ?v3)))))) :named a77))
(assert (! (forall ((?v0 A_T_N_sum_fun$) (?v1 A_set$) (?v2 T_N_sum_bool_fun$)) (=> (forall ((?v3 T_N_sum$)) (=> (member$ ?v3 (image$i ?v0 ?v1)) (fun_app$w ?v2 ?v3))) (forall ((?v3 A$)) (=> (member$a ?v3 ?v1) (fun_app$w ?v2 (fun_app$o ?v0 ?v3)))))) :named a78))
(assert (! (forall ((?v0 T_dtree_sum_T_N_sum_fun$) (?v1 T_dtree_sum_set$) (?v2 T_N_sum_bool_fun$)) (=> (forall ((?v3 T_N_sum$)) (=> (member$ ?v3 (image$ ?v0 ?v1)) (fun_app$w ?v2 ?v3))) (forall ((?v3 T_dtree_sum$)) (=> (member$b ?v3 ?v1) (fun_app$w ?v2 (fun_app$s ?v0 ?v3)))))) :named a79))
(assert (! (forall ((?v0 T_N_sum_a_fun$) (?v1 T_N_sum_set$) (?v2 A_bool_fun$)) (=> (forall ((?v3 A$)) (=> (member$a ?v3 (image$h ?v0 ?v1)) (fun_app$x ?v2 ?v3))) (forall ((?v3 T_N_sum$)) (=> (member$ ?v3 ?v1) (fun_app$x ?v2 (fun_app$m ?v0 ?v3)))))) :named a80))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_set$) (?v2 A_bool_fun$)) (=> (forall ((?v3 A$)) (=> (member$a ?v3 (fun_app$q (image$f ?v0) ?v1)) (fun_app$x ?v2 ?v3))) (forall ((?v3 A$)) (=> (member$a ?v3 ?v1) (fun_app$x ?v2 (fun_app$p ?v0 ?v3)))))) :named a81))
(assert (! (forall ((?v0 T_dtree_sum_a_fun$) (?v1 T_dtree_sum_set$) (?v2 A_bool_fun$)) (=> (forall ((?v3 A$)) (=> (member$a ?v3 (image$k ?v0 ?v1)) (fun_app$x ?v2 ?v3))) (forall ((?v3 T_dtree_sum$)) (=> (member$b ?v3 ?v1) (fun_app$x ?v2 (fun_app$t ?v0 ?v3)))))) :named a82))
(assert (! (forall ((?v0 T_N_sum_T_dtree_sum_fun$) (?v1 T_N_sum_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (forall ((?v3 T_dtree_sum$)) (=> (member$b ?v3 (image$c ?v0 ?v1)) (fun_app$y ?v2 ?v3))) (forall ((?v3 T_N_sum$)) (=> (member$ ?v3 ?v1) (fun_app$y ?v2 (fun_app$n ?v0 ?v3)))))) :named a83))
(assert (! (forall ((?v0 A_T_dtree_sum_fun$) (?v1 A_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (forall ((?v3 T_dtree_sum$)) (=> (member$b ?v3 (image$j ?v0 ?v1)) (fun_app$y ?v2 ?v3))) (forall ((?v3 A$)) (=> (member$a ?v3 ?v1) (fun_app$y ?v2 (fun_app$r ?v0 ?v3)))))) :named a84))
(assert (! (forall ((?v0 T_dtree_sum_T_dtree_sum_fun$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (forall ((?v3 T_dtree_sum$)) (=> (member$b ?v3 (image$d ?v0 ?v1)) (fun_app$y ?v2 ?v3))) (forall ((?v3 T_dtree_sum$)) (=> (member$b ?v3 ?v1) (fun_app$y ?v2 (fun_app$u ?v0 ?v3)))))) :named a85))
(assert (! (forall ((?v0 T_T_fun$) (?v1 T_set$) (?v2 T_bool_fun$)) (=> (exists ((?v3 T$)) (and (member$d ?v3 (fun_app$j (image$g ?v0) ?v1)) (fun_app$v ?v2 ?v3))) (exists ((?v3 T$)) (and (member$d ?v3 ?v1) (fun_app$v ?v2 (fun_app$d ?v0 ?v3)))))) :named a86))
(assert (! (forall ((?v0 T_N_sum_T_N_sum_fun$) (?v1 T_N_sum_set$) (?v2 T_N_sum_bool_fun$)) (=> (exists ((?v3 T_N_sum$)) (and (member$ ?v3 (image$b ?v0 ?v1)) (fun_app$w ?v2 ?v3))) (exists ((?v3 T_N_sum$)) (and (member$ ?v3 ?v1) (fun_app$w ?v2 (fun_app$l ?v0 ?v3)))))) :named a87))
(assert (! (forall ((?v0 A_T_N_sum_fun$) (?v1 A_set$) (?v2 T_N_sum_bool_fun$)) (=> (exists ((?v3 T_N_sum$)) (and (member$ ?v3 (image$i ?v0 ?v1)) (fun_app$w ?v2 ?v3))) (exists ((?v3 A$)) (and (member$a ?v3 ?v1) (fun_app$w ?v2 (fun_app$o ?v0 ?v3)))))) :named a88))
(assert (! (forall ((?v0 T_dtree_sum_T_N_sum_fun$) (?v1 T_dtree_sum_set$) (?v2 T_N_sum_bool_fun$)) (=> (exists ((?v3 T_N_sum$)) (and (member$ ?v3 (image$ ?v0 ?v1)) (fun_app$w ?v2 ?v3))) (exists ((?v3 T_dtree_sum$)) (and (member$b ?v3 ?v1) (fun_app$w ?v2 (fun_app$s ?v0 ?v3)))))) :named a89))
(assert (! (forall ((?v0 T_N_sum_a_fun$) (?v1 T_N_sum_set$) (?v2 A_bool_fun$)) (=> (exists ((?v3 A$)) (and (member$a ?v3 (image$h ?v0 ?v1)) (fun_app$x ?v2 ?v3))) (exists ((?v3 T_N_sum$)) (and (member$ ?v3 ?v1) (fun_app$x ?v2 (fun_app$m ?v0 ?v3)))))) :named a90))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A_set$) (?v2 A_bool_fun$)) (=> (exists ((?v3 A$)) (and (member$a ?v3 (fun_app$q (image$f ?v0) ?v1)) (fun_app$x ?v2 ?v3))) (exists ((?v3 A$)) (and (member$a ?v3 ?v1) (fun_app$x ?v2 (fun_app$p ?v0 ?v3)))))) :named a91))
(assert (! (forall ((?v0 T_dtree_sum_a_fun$) (?v1 T_dtree_sum_set$) (?v2 A_bool_fun$)) (=> (exists ((?v3 A$)) (and (member$a ?v3 (image$k ?v0 ?v1)) (fun_app$x ?v2 ?v3))) (exists ((?v3 T_dtree_sum$)) (and (member$b ?v3 ?v1) (fun_app$x ?v2 (fun_app$t ?v0 ?v3)))))) :named a92))
(assert (! (forall ((?v0 T_N_sum_T_dtree_sum_fun$) (?v1 T_N_sum_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (exists ((?v3 T_dtree_sum$)) (and (member$b ?v3 (image$c ?v0 ?v1)) (fun_app$y ?v2 ?v3))) (exists ((?v3 T_N_sum$)) (and (member$ ?v3 ?v1) (fun_app$y ?v2 (fun_app$n ?v0 ?v3)))))) :named a93))
(assert (! (forall ((?v0 A_T_dtree_sum_fun$) (?v1 A_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (exists ((?v3 T_dtree_sum$)) (and (member$b ?v3 (image$j ?v0 ?v1)) (fun_app$y ?v2 ?v3))) (exists ((?v3 A$)) (and (member$a ?v3 ?v1) (fun_app$y ?v2 (fun_app$r ?v0 ?v3)))))) :named a94))
(assert (! (forall ((?v0 T_dtree_sum_T_dtree_sum_fun$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_bool_fun$)) (=> (exists ((?v3 T_dtree_sum$)) (and (member$b ?v3 (image$d ?v0 ?v1)) (fun_app$y ?v2 ?v3))) (exists ((?v3 T_dtree_sum$)) (and (member$b ?v3 ?v1) (fun_app$y ?v2 (fun_app$u ?v0 ?v3)))))) :named a95))
(assert (! (forall ((?v0 T_set$) (?v1 T_set$) (?v2 T_T_fun$) (?v3 T_T_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 T$)) (=> (member$d ?v4 ?v1) (= (fun_app$d ?v2 ?v4) (fun_app$d ?v3 ?v4))))) (= (fun_app$j (image$g ?v2) ?v0) (fun_app$j (image$g ?v3) ?v1)))) :named a96))
(assert (! (forall ((?v0 T_N_sum_set$) (?v1 T_N_sum_set$) (?v2 T_N_sum_a_fun$) (?v3 T_N_sum_a_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 T_N_sum$)) (=> (member$ ?v4 ?v1) (= (fun_app$m ?v2 ?v4) (fun_app$m ?v3 ?v4))))) (= (image$h ?v2 ?v0) (image$h ?v3 ?v1)))) :named a97))
(assert (! (forall ((?v0 A_set$) (?v1 A_set$) (?v2 A_T_dtree_sum_fun$) (?v3 A_T_dtree_sum_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 A$)) (=> (member$a ?v4 ?v1) (= (fun_app$r ?v2 ?v4) (fun_app$r ?v3 ?v4))))) (= (image$j ?v2 ?v0) (image$j ?v3 ?v1)))) :named a98))
(assert (! (forall ((?v0 A_set$) (?v1 A_set$) (?v2 A_T_N_sum_fun$) (?v3 A_T_N_sum_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 A$)) (=> (member$a ?v4 ?v1) (= (fun_app$o ?v2 ?v4) (fun_app$o ?v3 ?v4))))) (= (image$i ?v2 ?v0) (image$i ?v3 ?v1)))) :named a99))
(assert (! (forall ((?v0 A_set$) (?v1 A_set$) (?v2 A_a_fun$) (?v3 A_a_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 A$)) (=> (member$a ?v4 ?v1) (= (fun_app$p ?v2 ?v4) (fun_app$p ?v3 ?v4))))) (= (fun_app$q (image$f ?v2) ?v0) (fun_app$q (image$f ?v3) ?v1)))) :named a100))
(assert (! (forall ((?v0 T_dtree_sum_set$) (?v1 T_dtree_sum_set$) (?v2 T_dtree_sum_T_N_sum_fun$) (?v3 T_dtree_sum_T_N_sum_fun$)) (=> (and (= ?v0 ?v1) (forall ((?v4 T_dtree_sum$)) (=> (member$b ?v4 ?v1) (= (fun_app$s ?v2 ?v4) (fun_app$s ?v3 ?v4))))) (= (image$ ?v2 ?v0) (image$ ?v3 ?v1)))) :named a101))
(assert (! (forall ((?v0 T$) (?v1 T_T_fun$) (?v2 T_set$)) (= (member$d ?v0 (fun_app$j (image$g ?v1) ?v2)) (exists ((?v3 T$)) (and (member$d ?v3 ?v2) (= ?v0 (fun_app$d ?v1 ?v3)))))) :named a102))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_N_sum_T_N_sum_fun$) (?v2 T_N_sum_set$)) (= (member$ ?v0 (image$b ?v1 ?v2)) (exists ((?v3 T_N_sum$)) (and (member$ ?v3 ?v2) (= ?v0 (fun_app$l ?v1 ?v3)))))) :named a103))
(assert (! (forall ((?v0 T_N_sum$) (?v1 A_T_N_sum_fun$) (?v2 A_set$)) (= (member$ ?v0 (image$i ?v1 ?v2)) (exists ((?v3 A$)) (and (member$a ?v3 ?v2) (= ?v0 (fun_app$o ?v1 ?v3)))))) :named a104))
(assert (! (forall ((?v0 T_N_sum$) (?v1 T_dtree_sum_T_N_sum_fun$) (?v2 T_dtree_sum_set$)) (= (member$ ?v0 (image$ ?v1 ?v2)) (exists ((?v3 T_dtree_sum$)) (and (member$b ?v3 ?v2) (= ?v0 (fun_app$s ?v1 ?v3)))))) :named a105))
(assert (! (forall ((?v0 A$) (?v1 T_N_sum_a_fun$) (?v2 T_N_sum_set$)) (= (member$a ?v0 (image$h ?v1 ?v2)) (exists ((?v3 T_N_sum$)) (and (member$ ?v3 ?v2) (= ?v0 (fun_app$m ?v1 ?v3)))))) :named a106))
(assert (! (forall ((?v0 A$) (?v1 A_a_fun$) (?v2 A_set$)) (= (member$a ?v0 (fun_app$q (image$f ?v1) ?v2)) (exists ((?v3 A$)) (and (member$a ?v3 ?v2) (= ?v0 (fun_app$p ?v1 ?v3)))))) :named a107))
(assert (! (forall ((?v0 A$) (?v1 T_dtree_sum_a_fun$) (?v2 T_dtree_sum_set$)) (= (member$a ?v0 (image$k ?v1 ?v2)) (exists ((?v3 T_dtree_sum$)) (and (member$b ?v3 ?v2) (= ?v0 (fun_app$t ?v1 ?v3)))))) :named a108))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_N_sum_T_dtree_sum_fun$) (?v2 T_N_sum_set$)) (= (member$b ?v0 (image$c ?v1 ?v2)) (exists ((?v3 T_N_sum$)) (and (member$ ?v3 ?v2) (= ?v0 (fun_app$n ?v1 ?v3)))))) :named a109))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 A_T_dtree_sum_fun$) (?v2 A_set$)) (= (member$b ?v0 (image$j ?v1 ?v2)) (exists ((?v3 A$)) (and (member$a ?v3 ?v2) (= ?v0 (fun_app$r ?v1 ?v3)))))) :named a110))
(assert (! (forall ((?v0 T_dtree_sum$) (?v1 T_dtree_sum_T_dtree_sum_fun$) (?v2 T_dtree_sum_set$)) (= (member$b ?v0 (image$d ?v1 ?v2)) (exists ((?v3 T_dtree_sum$)) (and (member$b ?v3 ?v2) (= ?v0 (fun_app$u ?v1 ?v3)))))) :named a111))
(assert (! (forall ((?v0 T_set$)) (! (= (fun_app$j id$a ?v0) ?v0) :pattern ((fun_app$j id$a ?v0)))) :named a112))
(assert (! (forall ((?v0 T_T_sum$)) (! (= (fun_app$k id$c ?v0) ?v0) :pattern ((fun_app$k id$c ?v0)))) :named a113))
(assert (! (forall ((?v0 T$)) (! (= (fun_app$d id$ ?v0) ?v0) :pattern ((fun_app$d id$ ?v0)))) :named a114))
(assert (! (forall ((?v0 N$) (?v1 N$)) (=> (= (inr$ ?v0) (inr$ ?v1)) (= ?v0 ?v1))) :named a115))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (=> (= (inr$a ?v0) (inr$a ?v1)) (= ?v0 ?v1))) :named a116))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (=> (and (wf$ ?v0) (member$b (inr$a ?v1) (cont$ ?v0))) (exists ((?v2 N$)) (and (member$ (inr$ ?v2) (image$ (fun_app$b (map_sum$ id$) root$) (cont$ ?v0))) (= (fun_app$ (subtrOf$ ?v0) ?v2) ?v1))))) :named a117))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (=> (member$b (inr$a ?v0) (cont$ ?v1)) (member$ (inr$ (fun_app$a root$ ?v0)) (image$ (fun_app$b (map_sum$ id$) root$) (cont$ ?v1))))) :named a118))
(assert (! (forall ((?v0 T_T_fun$) (?v1 T_T_fun$) (?v2 T_T_sum$) (?v3 T$)) (=> (= (fun_app$k (map_sum$a ?v0 ?v1) ?v2) (inr$b ?v3)) (exists ((?v4 T$)) (and (= ?v2 (inr$b ?v4)) (= (fun_app$d ?v1 ?v4) ?v3))))) :named a119))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_N_fun$) (?v2 T_N_sum$) (?v3 N$)) (=> (= (fun_app$l (fun_app$e (map_sum$b ?v0) ?v1) ?v2) (inr$ ?v3)) (exists ((?v4 N$)) (and (= ?v2 (inr$ ?v4)) (= (fun_app$f ?v1 ?v4) ?v3))))) :named a120))
(assert (! (forall ((?v0 T_T_fun$) (?v1 N_dtree_fun$) (?v2 T_N_sum$) (?v3 Dtree$)) (=> (= (fun_app$n (fun_app$g (map_sum$c ?v0) ?v1) ?v2) (inr$a ?v3)) (exists ((?v4 N$)) (and (= ?v2 (inr$ ?v4)) (= (fun_app$ ?v1 ?v4) ?v3))))) :named a121))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_dtree_fun$) (?v2 T_dtree_sum$) (?v3 Dtree$)) (=> (= (fun_app$u (fun_app$h (map_sum$d ?v0) ?v1) ?v2) (inr$a ?v3)) (exists ((?v4 Dtree$)) (and (= ?v2 (inr$a ?v4)) (= (fun_app$i ?v1 ?v4) ?v3))))) :named a122))
(assert (! (forall ((?v0 T_T_fun$) (?v1 Dtree_N_fun$) (?v2 T_dtree_sum$) (?v3 N$)) (=> (= (fun_app$s (fun_app$b (map_sum$ ?v0) ?v1) ?v2) (inr$ ?v3)) (exists ((?v4 Dtree$)) (and (= ?v2 (inr$a ?v4)) (= (fun_app$a ?v1 ?v4) ?v3))))) :named a123))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (=> (and (= (fun_app$a root$ ?v0) (fun_app$a root$ ?v1)) (= (cont$ ?v0) (cont$ ?v1))) (= ?v0 ?v1))) :named a124))
(assert (! (= (map_sum$e id$a id$) id$g) :named a125))
(assert (! (= (map_sum$f id$a id$a) id$h) :named a126))
(assert (! (= (map_sum$g id$a id$c) id$i) :named a127))
(assert (! (= (map_sum$h id$c id$) id$j) :named a128))
(assert (! (= (map_sum$i id$c id$a) id$k) :named a129))
(assert (! (= (map_sum$j id$c id$c) id$l) :named a130))
(assert (! (= (fun_app$h (map_sum$d id$) id$m) id$n) :named a131))
(assert (! (= (fun_app$e (map_sum$b id$) id$o) id$p) :named a132))
(assert (! (= (map_sum$a id$ id$) id$c) :named a133))
(assert (! (forall ((?v0 T_T_sum$)) (= (fun_app$k (map_sum$a id$ id$) ?v0) ?v0)) :named a134))
(assert (! (forall ((?v0 Dtree$) (?v1 Dtree$)) (! (= (hsubst_c$ ?v0 ?v1) (ite (= (fun_app$a root$ ?v1) (fun_app$a root$ ?v0)) (cont$ ?v0) (cont$ ?v1))) :pattern ((hsubst_c$ ?v0 ?v1)))) :named a135))
(check-sat)
;(get-unsat-core)
