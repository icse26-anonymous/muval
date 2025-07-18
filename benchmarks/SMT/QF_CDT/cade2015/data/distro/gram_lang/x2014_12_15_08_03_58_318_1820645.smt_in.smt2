;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort N$ 0 )
(declare-sort T$ 0 )
(declare-sort Dtree$ 0 )
(declare-sort N_set$ 0 )
(declare-sort T_dtree_sum_set$ 0 )
(declare-datatypes ()((T_dtree_sum$ (inl$ (projl$ T$ ))(inr$ (projr$ Dtree$ )))))
(declare-fun t$ ()T$ )
(declare-fun ns$ ()N_set$ )
(declare-fun tr$ ()Dtree$ )
(declare-fun tr1$ ()Dtree$ )
(declare-fun cont$ (Dtree$ )T_dtree_sum_set$ )
(declare-fun inFr$ (N_set$ Dtree$ T$ )Bool )
(declare-fun node$ (N$ T_dtree_sum_set$ )Dtree$ )
(declare-fun root$ (Dtree$ )N$ )
(declare-fun inFr2$ (N_set$ Dtree$ T$ )Bool )
(declare-fun insert$ (N$ N_set$ )N_set$ )
(declare-fun member$ (N$ N_set$ )Bool )
(declare-fun member$a (T_dtree_sum$ T_dtree_sum_set$ )Bool )
(assert (! (not (inFr2$ ns$ tr$ t$ )):named a0 ))
(assert (! (member$ (root$ tr$ )ns$ ):named a1 ))
(assert (! (member$a (inr$ tr1$ )(cont$ tr$ )):named a2 ))
(assert (! (inFr$ ns$ tr1$ t$ ):named a3 ))
(assert (! (inFr2$ ns$ tr1$ t$ ):named a4 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(=> (inFr$ ?v0 ?v1 ?v2 )(member$ (root$ ?v1 )?v0 ))):named a5 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ )(?v3 Dtree$ ))(=> (and (inFr2$ ?v0 ?v1 ?v2 )(and (member$ (root$ ?v3 )?v0 )(member$a (inr$ ?v1 )(cont$ ?v3 ))))(inFr2$ ?v0 ?v3 ?v2 ))):named a6 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(=> (inFr2$ ?v0 ?v1 ?v2 )(member$ (root$ ?v1 )?v0 ))):named a7 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 Dtree$ )(?v3 T$ ))(=> (and (member$ (root$ ?v0 )?v1 )(and (member$a (inr$ ?v2 )(cont$ ?v0 ))(inFr$ ?v1 ?v2 ?v3 )))(inFr$ ?v1 ?v0 ?v3 ))):named a8 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(= (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a10 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (and (= (root$ ?v0 )(root$ ?v1 ))(= (cont$ ?v0 )(cont$ ?v1 )))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ )(?v2 N_set$ )(?v3 T$ ))(=> (and (member$a (inr$ ?v0 )(cont$ ?v1 ))(inFr2$ ?v2 ?v0 ?v3 ))(inFr2$ (insert$ (root$ ?v1 )?v2 )?v1 ?v3 ))):named a12 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ )(?v3 Dtree$ ))(=> (and (inFr$ ?v0 ?v1 ?v2 )(member$a (inr$ ?v1 )(cont$ ?v3 )))(inFr$ (insert$ (root$ ?v3 )?v0 )?v3 ?v2 ))):named a13 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(= (inFr$ ?v0 ?v1 ?v2 )(or (exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 T$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v5 )(and (member$ (root$ ?v3 )?v4 )(member$a (inl$ ?v5 )(cont$ ?v3 )))))))(exists ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 T$ ))(and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$ (root$ ?v3 )?v4 )(and (member$a (inr$ ?v5 )(cont$ ?v3 ))(inFr$ ?v4 ?v5 ?v6 )))))))))):named a14 ))
(assert (! (forall ((?v0 N_set$ )(?v1 Dtree$ )(?v2 T$ ))(=> (and (inFr$ ?v0 ?v1 ?v2 )(and (forall ((?v3 Dtree$ )(?v4 N_set$ )(?v5 T$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v5 )(and (member$ (root$ ?v3 )?v4 )(member$a (inl$ ?v5 )(cont$ ?v3 ))))))false ))(forall ((?v3 Dtree$ )(?v4 N_set$ )(?v5 Dtree$ )(?v6 T$ ))(=> (and (= ?v0 ?v4 )(and (= ?v1 ?v3 )(and (= ?v2 ?v6 )(and (member$ (root$ ?v3 )?v4 )(and (member$a (inr$ ?v5 )(cont$ ?v3 ))(inFr$ ?v4 ?v5 ?v6 ))))))false ))))false )):named a15 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (= (inr$ ?v0 )(inr$ ?v1 ))(= ?v0 ?v1 ))):named a16 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 Dtree$ ))(=> (not (= ?v0 ?v1 ))(not (= (inr$ ?v0 )(inr$ ?v1 ))))):named a17 ))
(assert (! (forall ((?v0 Dtree$ ))(= (node$ (root$ ?v0 )(cont$ ?v0 ))?v0 )):named a18 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 T$ ))(=> (and (member$ (root$ ?v0 )?v1 )(member$a (inl$ ?v2 )(cont$ ?v0 )))(inFr2$ ?v1 ?v0 ?v2 ))):named a19 ))
(assert (! (forall ((?v0 Dtree$ )(?v1 N_set$ )(?v2 T$ ))(=> (and (member$ (root$ ?v0 )?v1 )(member$a (inl$ ?v2 )(cont$ ?v0 )))(inFr$ ?v1 ?v0 ?v2 ))):named a20 ))
(assert (! (forall ((?v0 T$ )(?v1 T$ ))(= (= (inl$ ?v0 )(inl$ ?v1 ))(= ?v0 ?v1 ))):named a21 ))
(check-sat )
;(get-unsat-core )
