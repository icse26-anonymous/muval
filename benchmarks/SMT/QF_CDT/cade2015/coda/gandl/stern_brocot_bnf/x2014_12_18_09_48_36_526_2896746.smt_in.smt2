;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_b_fun$ 0 )
(declare-codatatypes ()((B_tree$ (node$ (root$ B$ )(left$ B_tree$ )(right$ B_tree$ )))(A_tree$ (node$a (root$a A$ )(left$a A_tree$ )(right$a A_tree$ )))))
(declare-fun f$ ()A_b_fun$ )
(declare-fun t$ ()A_tree$ )
(declare-fun t$a ()A_tree$ )
(declare-fun plus$ (A_tree$ A_tree$ )A_tree$ )
(declare-fun plus$a (B_tree$ B_tree$ )B_tree$ )
(declare-fun plus$b (A$ A$ )A$ )
(declare-fun plus$c (B$ B$ )B$ )
(declare-fun fun_app$ (A_b_fun$ A$ )B$ )
(declare-fun map_tree$ (A_b_fun$ A_tree$ )B_tree$ )
(assert (! (not (= (map_tree$ f$ (plus$ t$ t$a ))(plus$a (map_tree$ f$ t$ )(map_tree$ f$ t$a )))):named a0 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (fun_app$ f$ (plus$b ?v0 ?v1 ))(plus$c (fun_app$ f$ ?v0 )(fun_app$ f$ ?v1 )))):named a1 ))
(check-sat )
;(get-unsat-core )
