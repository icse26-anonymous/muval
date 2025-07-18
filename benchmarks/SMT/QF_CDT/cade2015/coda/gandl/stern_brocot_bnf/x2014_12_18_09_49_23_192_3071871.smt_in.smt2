;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-codatatypes ()((Nat_tree$ (node$ (root$ Nat$ )(left$ Nat_tree$ )(right$ Nat_tree$ )))))
(declare-sort Num$ 0)
(declare-fun one$ ()Num$)
(declare-fun select$ (Num$)Num$)
(declare-fun bit0$ (Num$ )Num$)
(declare-fun selecta$ (Num$)Num$)
(declare-fun bit1$ (Num$ )Num$)
(declare-fun den$ ()Nat_tree$ )
(declare-fun mod$ (Nat_tree$ Nat_tree$ )Nat_tree$ )
(declare-fun num$ ()Nat_tree$ )
(declare-fun plus$ (Nat_tree$ Nat_tree$ )Nat_tree$ )
(declare-fun minus$ (Nat_tree$ Nat_tree$ )Nat_tree$ )
(declare-fun plus$a (Num$ Num$ )Num$ )
(declare-fun times$ (Nat_tree$ Nat_tree$ )Nat_tree$ )
(declare-fun times$a (Num$ Num$ )Num$ )
(declare-fun numeral$ (Num$ )Nat_tree$ )
(declare-fun tree_chop$ (Nat_tree$ )Nat_tree$ )
(assert (! (not (= (tree_chop$ den$ )(minus$ (plus$ num$ den$ )(times$ (numeral$ (bit0$ one$ ))(mod$ num$ den$ ))))):named a0 ))
(assert (! (forall ((?v0 Nat_tree$ )(?v1 Nat_tree$ ))(= (mod$ (plus$ ?v0 ?v1 )?v1 )(mod$ ?v0 ?v1 ))):named a1 ))
(assert (! (forall ((?v0 Nat_tree$ )(?v1 Nat_tree$ ))(= (tree_chop$ (plus$ ?v0 ?v1 ))(plus$ (tree_chop$ ?v0 )(tree_chop$ ?v1 )))):named a2 ))
(assert (! (= den$ (tree_chop$ num$ )):named a3 ))
(assert (! (forall ((?v0 Nat_tree$ )(?v1 Nat_tree$ )(?v2 Num$ ))(= (times$ (plus$ ?v0 ?v1 )(numeral$ ?v2 ))(plus$ (times$ ?v0 (numeral$ ?v2 ))(times$ ?v1 (numeral$ ?v2 ))))):named a4 ))
(assert (! (forall ((?v0 Num$ )(?v1 Nat_tree$ )(?v2 Nat_tree$ ))(= (times$ (numeral$ ?v0 )(plus$ ?v1 ?v2 ))(plus$ (times$ (numeral$ ?v0 )?v1 )(times$ (numeral$ ?v0 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 Num$ ))(= (= (bit0$ ?v0 )one$ )false )):named a6 ))
(assert (! (forall ((?v0 Num$ ))(= (= one$ (bit0$ ?v0 ))false )):named a7 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (plus$a (bit0$ ?v0 )(bit0$ ?v1 ))(bit0$ (plus$a ?v0 ?v1 ))):pattern ((plus$a (bit0$ ?v0 )(bit0$ ?v1 ))))):named a8 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (times$a (bit0$ ?v0 )(bit0$ ?v1 ))(bit0$ (bit0$ (times$a ?v0 ?v1 )))):pattern ((times$a (bit0$ ?v0 )(bit0$ ?v1 ))))):named a9 ))
(check-sat )
;(get-unsat-core )
