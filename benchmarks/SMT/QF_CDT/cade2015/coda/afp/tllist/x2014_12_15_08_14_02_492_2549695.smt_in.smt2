;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort C$ 0 )
(declare-sort D$ 0 )
(declare-codatatypes ()((A_b_tllist$ (tNil$ (terminal$ B$ ))(tCons$ (thd$ A$ )(ttl$ A_b_tllist$ )))(C_d_tllist$ (tNil$a (terminal$a D$ ))(tCons$a (thd$a C$ )(ttl$a C_d_tllist$ )))(A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort A_llist_b_prod$ 0)
(declare-fun fst$ (A_llist_b_prod$)A_llist$)
(declare-fun snd$ (A_llist_b_prod$)B$)
(declare-fun pair$ (A_llist$ B$ )A_llist_b_prod$)
(declare-codatatypes ()((C_llist$ (lNil$a )(lCons$a (lhd$a C$ )(ltl$a C_llist$ )))))
(declare-sort C_llist_d_prod$ 0)
(declare-fun fst$a (C_llist_d_prod$)C_llist$)
(declare-fun snd$a (C_llist_d_prod$)D$)
(declare-fun pair$a (C_llist$ D$ )C_llist_d_prod$)
(declare-fun b$ ()B$ )
(declare-fun c$ ()D$ )
(declare-fun r$ (B$ D$ )Bool )
(declare-fun x$ (A_b_tllist$ C_d_tllist$ )Bool )
(declare-fun xa$ (A_llist_b_prod$ C_llist_d_prod$ )Bool )
(declare-fun xs$ ()A_b_tllist$ )
(declare-fun ys$ ()C_d_tllist$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun ysa$ ()C_llist$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(assert (! (not (r$ b$ c$ )):named a0 ))
(assert (! (x$ xs$ ys$ ):named a1 ))
(assert (! (xa$ (pair$ xsa$ b$ )(pair$a ysa$ c$ )):named a2 ))
(assert (! (lfinite$ xsa$ ):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ )(?v2 A_llist$ )(?v3 B$ ))(= (= (pair$ ?v0 ?v1 )(pair$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a4 ))
(assert (! (forall ((?v0 C_llist$ )(?v1 D$ )(?v2 C_llist$ )(?v3 D$ ))(= (= (pair$a ?v0 ?v1 )(pair$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ )(?v2 A_llist$ )(?v3 B$ ))(= (= (pair$ ?v0 ?v1 )(pair$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a6 ))
(assert (! (forall ((?v0 C_llist$ )(?v1 D$ )(?v2 C_llist$ )(?v3 D$ ))(= (= (pair$a ?v0 ?v1 )(pair$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a7 ))
(assert (! (forall ((?v0 A_llist_b_prod$ ))(=> (forall ((?v1 A_llist$ )(?v2 B$ ))(=> (= ?v0 (pair$ ?v1 ?v2 ))false ))false )):named a8 ))
(assert (! (forall ((?v0 C_llist_d_prod$ ))(=> (forall ((?v1 C_llist$ )(?v2 D$ ))(=> (= ?v0 (pair$a ?v1 ?v2 ))false ))false )):named a9 ))
(assert (! (forall ((?v0 A_llist_b_prod$ ))(exists ((?v1 A_llist$ )(?v2 B$ ))(= ?v0 (pair$ ?v1 ?v2 )))):named a10 ))
(assert (! (forall ((?v0 C_llist_d_prod$ ))(exists ((?v1 C_llist$ )(?v2 D$ ))(= ?v0 (pair$a ?v1 ?v2 )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 B$ )(?v2 A_llist$ )(?v3 B$ ))(=> (and (= (pair$ ?v0 ?v1 )(pair$ ?v2 ?v3 ))(=> (and (= ?v0 ?v2 )(= ?v1 ?v3 ))false ))false )):named a12 ))
(assert (! (forall ((?v0 C_llist$ )(?v1 D$ )(?v2 C_llist$ )(?v3 D$ ))(=> (and (= (pair$a ?v0 ?v1 )(pair$a ?v2 ?v3 ))(=> (and (= ?v0 ?v2 )(= ?v1 ?v3 ))false ))false )):named a13 ))
(check-sat )
;(get-unsat-core )
