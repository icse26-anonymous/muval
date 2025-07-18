;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-datatypes ()((A_tree$ (leaf$ )(node$ (left$ A_tree$ )(val$ A$ )(right$ A_tree$ )))))
(declare-fun b$ ()A$ )
(declare-fun c$ ()A$ )
(declare-fun l$ ()A_tree$ )
(declare-fun r$ ()A_tree$ )
(declare-fun u$ ()A$ )
(declare-fun aa$ ()A$ )
(declare-fun r$a ()A_tree$ )
(declare-fun rl$ ()A_tree$ )
(declare-fun rr$ ()A_tree$ )
(declare-fun splay$ (A$ A_tree$ )A_tree$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun set_tree$ (A_tree$ )A_set$ )
(declare-fun pred_tree$ (A_bool_fun$ A_tree$ )Bool )
(declare-fun splay_max$ (A_tree$ )A_tree$ )
(assert (! (not (not (= rr$ leaf$ ))):named a0 ))
(assert (! (member$ aa$ (set_tree$ rr$ )):named a1 ))
(assert (! (not (= aa$ b$ )):named a2 ))
(assert (! (forall ((?v0 A_tree$ ))(=> (and (=> (= ?v0 leaf$ )false )(=> (not (= ?v0 leaf$ ))false ))false )):named a3 ))
(assert (! (not (= aa$ c$ )):named a4 ))
(assert (! (=> (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A_tree$ ))(=> (= (splay$ aa$ rr$ )(node$ ?v0 ?v1 ?v2 ))false ))false ):named a5 ))
(assert (! (= (splay$ aa$ rr$ )(node$ l$ u$ r$ )):named a6 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(pred_tree$ ?v0 leaf$ )):named a7 ))
(assert (! (forall ((?v0 A_tree$ ))(= (= (splay_max$ ?v0 )leaf$ )(= ?v0 leaf$ ))):named a8 ))
(assert (! (= r$a (node$ rl$ b$ rr$ )):named a9 ))
(assert (! (= (left$ leaf$ )leaf$ ):named a10 ))
(assert (! (= (right$ leaf$ )leaf$ ):named a11 ))
(assert (! (= (splay_max$ leaf$ )leaf$ ):named a12 ))
(assert (! (=> (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A_tree$ ))(=> (= r$a (node$ ?v0 ?v1 ?v2 ))false ))false ):named a13 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ )(?v4 A$ )(?v5 A_tree$ ))(= (= (node$ ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (splay$ ?v0 (node$ ?v1 ?v0 ?v2 ))(node$ ?v1 ?v0 ?v2 )):pattern ((node$ ?v1 ?v0 ?v2 )))):named a15 ))
(check-sat )
;(get-unsat-core )
