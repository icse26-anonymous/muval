//#Safe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

//@ ltl invariant positive: <>[]AP( Stored == 0 );

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume();
extern int __VERIFIER_nondet_int();

int Stored;
void init() { Stored = 0; }
void callback() {}
void IoQueueWorkItem() {}
void main() {
    while(__VERIFIER_nondet_int()) {
           if (__VERIFIER_nondet_int()) {
               //
               // We are safely at PASSIVE_LEVEL, call callback directly
               // to perform
               // this operation immediately.
               //
               callback ();
           } else {
	       IoQueueWorkItem ();
               Stored = 1;
               break;
           }
    }
    // Lower Irql and process
    if (Stored==1) {
        callback ();
        Stored = 0;
    }
}