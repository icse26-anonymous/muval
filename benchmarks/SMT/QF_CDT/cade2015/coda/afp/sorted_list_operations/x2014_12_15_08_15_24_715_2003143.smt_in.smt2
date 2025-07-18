;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-fun x1$ ()A$ )
(declare-fun x2$ ()A$ )
(declare-fun l1a$ ()A_list$ )
(declare-fun l2b$ ()A_list$ )
(declare-fun set$ (A_list$ )A_set$ )
(declare-fun less$ (A$ A$ )Bool )
(declare-fun insert$ (A$ A_set$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun sorted$ (A_list$ )Bool )
(declare-fun less_eq$ (A$ A$ )Bool )
(declare-fun distinct$ (A_list$ )Bool )
(declare-fun less_eq$a (A_set$ A_set$ )Bool )
(declare-fun subset_sorted$ (A_list$ A_list$ )Bool )
(assert (! (not false ):named a0 ))
(assert (! (less$ x1$ x2$ ):named a1 ))
(assert (! (not (member$ x1$ (set$ l1a$ ))):named a2 ))
(assert (! (forall ((?v0 A$ ))(=> (member$ ?v0 (set$ l1a$ ))(less_eq$ x1$ ?v0 ))):named a3 ))
(assert (! (forall ((?v0 A$ ))(=> (member$ ?v0 (set$ l2b$ ))(less_eq$ x2$ ?v0 ))):named a4 ))
(assert (! (subset_sorted$ l1a$ (cons$ x2$ l2b$ )):named a5 ))
(assert (! (less_eq$a (set$ l1a$ )(insert$ x2$ (set$ l2b$ ))):named a6 ))
(assert (! (member$ x1$ (set$ l2b$ )):named a7 ))
(assert (! (less$ x1$ x2$ ):named a8 ))
(assert (! (not (member$ x1$ (set$ l1a$ ))):named a9 ))
(assert (! (not (member$ x2$ (set$ l2b$ ))):named a10 ))
(assert (! (forall ((?v0 A$ ))(=> (member$ ?v0 (set$ l1a$ ))(less_eq$ x1$ ?v0 ))):named a11 ))
(assert (! (forall ((?v0 A$ ))(=> (member$ ?v0 (set$ l2b$ ))(less_eq$ x2$ ?v0 ))):named a12 ))
(assert (! (= (subset_sorted$ (cons$ x1$ l1a$ )l2b$ )(less_eq$a (set$ (cons$ x1$ l1a$ ))(set$ l2b$ ))):named a13 ))
(assert (! (= (subset_sorted$ l1a$ (cons$ x2$ l2b$ ))(less_eq$a (set$ l1a$ )(set$ (cons$ x2$ l2b$ )))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ )(?v2 A$ )(?v3 A_list$ ))(! (= (subset_sorted$ (cons$ ?v0 ?v1 )(cons$ ?v2 ?v3 ))(ite (less$ ?v0 ?v2 )false (ite (= ?v0 ?v2 )(subset_sorted$ ?v1 ?v3 )(subset_sorted$ (cons$ ?v0 ?v1 )?v3 )))):pattern ((subset_sorted$ (cons$ ?v0 ?v1 )(cons$ ?v2 ?v3 ))))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ ))(! (= (set$ (cons$ ?v0 ?v1 ))(insert$ ?v0 (set$ ?v1 ))):pattern ((cons$ ?v0 ?v1 )))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ )(?v2 A_set$ ))(= (less_eq$a (insert$ ?v0 ?v1 )?v2 )(and (member$ ?v0 ?v2 )(less_eq$a ?v1 ?v2 )))):named a17 ))
(assert (! (=> (and (distinct$ l2b$ )(sorted$ l2b$ ))(= (subset_sorted$ (cons$ x1$ l1a$ )l2b$ )(less_eq$a (set$ (cons$ x1$ l1a$ ))(set$ l2b$ )))):named a18 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A$ ))(less_eq$a (set$ ?v0 )(set$ (cons$ ?v1 ?v0 )))):named a19 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ ))(= (insert$ ?v0 (insert$ ?v0 ?v1 ))(insert$ ?v0 ?v1 ))):named a20 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_set$ ))(= (member$ ?v0 (insert$ ?v1 ?v2 ))(or (= ?v0 ?v1 )(member$ ?v0 ?v2 )))):named a21 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ )(?v2 A$ ))(=> (=> (not (member$ ?v0 ?v1 ))(= ?v0 ?v2 ))(member$ ?v0 (insert$ ?v2 ?v1 )))):named a22 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (forall ((?v2 A$ ))(=> (member$ ?v2 ?v0 )(member$ ?v2 ?v1 )))(less_eq$a ?v0 ?v1 ))):named a23 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (and (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 ))(= ?v0 ?v1 ))):named a24 ))
(check-sat )
;(get-unsat-core )
